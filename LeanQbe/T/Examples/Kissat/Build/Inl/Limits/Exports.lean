module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Limits.Exports

open LeanQbe.T

@[expose] def flat0 : TFlatFn := {
  name := "full_isqrt",
  as := [i64],
  rs := [i64],
  body :=
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.var 1, ())) <|
    TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 62), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.shl i64, (.imm (BitVec.ofNat 64 1), .var 0, ())⟩ <|
    TFlat.group (sig := [[i64]])
      (TBlocks.cons (ts := [i64])
        (TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl, (.var 0, .var 4, ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 2), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.lshr i64, (.var 2, .var 0, ())⟩ <|
          TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
        TFlat.group (sig := [[i64, i64, i64]])
          (TBlocks.cons (ts := [i64, i64, i64])
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.group (sig := [[i64, i64]])
            (TBlocks.cons (ts := [i64, i64])
            (TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 2), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.lshr i64, (.var 4, .var 0, ())⟩ <|
            TFlat.jump (ts := [i64, i64, i64]) 1 (.var 3, .var 2, .var 0, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .var 1, ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 4, .var 0, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .var 3, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 6, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.lshr i64, (.var 7, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .var 7, ())⟩ <|
            TFlat.jump (ts := [i64, i64]) 0 (.var 3, .var 0, ())) <|
            TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.lshr i64, (.var 5, .var 0, ())⟩ <|
            TFlat.jump (ts := [i64, i64]) 0 (.var 7, .var 0, ())) <|
            TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.ret (.var 0, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 2, .imm (BitVec.ofNat 64 0), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 1), ())) <|
            TFlat.jump (ts := [i64]) 0 (.var 3, ())) <|
          TBlocks.nil) <|
        TFlat.jump (ts := [i64, i64, i64]) 0 (.var 5, .imm (BitVec.ofNat 64 0), .var 1, ())) <|
      TBlocks.nil) <|
    TFlat.jump (ts := [i64]) 0 (.var 0, ()) }

@[expose] def flat1 : TFlatFn := {
  name := "full_ilog10",
  as := [i64],
  rs := [i64],
  body :=
    TFlat.group (sig := [[i64, i64]])
      (TBlocks.cons (ts := [i64, i64])
        (TFlat.let_ (ts := [i64]) ⟨.udiv 64, (.var 2, .imm (BitVec.ofNat 64 10), ())⟩ <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 0, .var 1, ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl,
            (.var 3, .imm (BitVec.ofNat 64 19), ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 4, .imm (BitVec.ofNat 64 10), ())⟩ <|
            TFlat.jump (ts := [i64, i64]) 0 (.var 1, .var 0, ())) <|
          TFlat.ret (.var 4, ())) <|
        TFlat.ret (.var 3, ())) <|
      TBlocks.nil) <|
    TFlat.jump (ts := [i64, i64]) 0 (.imm (BitVec.ofNat 64 1), .imm (BitVec.ofNat 64 10), ()) }

@[expose] def flat2 : TFlatFn := {
  name := "full_tick_rel",
  as := [i64],
  rs := [],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 552), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 3, .imm (BitVec.ofNat 64 288), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 6, .imm (BitVec.ofNat 64 328), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 9, .imm (BitVec.ofNat 64 304), ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl,
          (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.ret ()) <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 12, .imm (BitVec.ofNat 64 312), ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 14, .imm (BitVec.ofNat 64 320), ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.group (sig := [[i64, i64]])
          (TBlocks.cons (ts := [i64, i64])
            (TFlat.group (sig := [[i64, i64]])
            (TBlocks.cons (ts := [i64, i64])
            (TFlat.group (sig := [[i64, i64]])
            (TBlocks.cons (ts := [i64, i64])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 22, .imm (BitVec.ofNat 64 288), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 2, .var 0, ())⟩ <|
            TFlat.group (sig := [[i64, i64, i64]])
            (TBlocks.cons (ts := [i64, i64, i64])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 28, .imm (BitVec.ofNat 64 328), ())⟩ <|
            TFlat.store (t := i64) (.imm (BitVec.ofNat 64 1)) (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 29, .imm (BitVec.ofNat 64 304), ())⟩ <|
            TFlat.store (t := i64) (.var 2) (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 30, .imm (BitVec.ofNat 64 312), ())⟩ <|
            TFlat.store (t := i64) (.var 5) (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 31, .imm (BitVec.ofNat 64 320), ())⟩ <|
            TFlat.store (t := i64) (.var 5) (.var 0) <|
            TFlat.ret ()) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 25, .imm (BitVec.ofNat 64 296), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 28, .imm (BitVec.ofNat 64 296), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl, (.var 5, .var 0, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 31, .imm (BitVec.ofNat 64 288), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.jump (ts := [i64, i64, i64]) 0
            (.imm (BitVec.ofNat 64 1), .imm (BitVec.ofNat 64 1), .var 0, ())) <|
            TFlat.jump (ts := [i64, i64, i64]) 0 (.var 10, .var 9, .var 6, ())) <|
            TFlat.jump (ts := [i64, i64, i64]) 0 (.var 7, .var 6, .var 3, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i64, i64]) 0
            (.imm (BitVec.ofNat 64 1), .imm (BitVec.ofNat 64 1), ())) <|
            TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 30), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.shl i64, (.imm (BitVec.ofNat 64 1), .var 0, ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl, (.var 3, .var 0, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i64, i64]) 0
            (.imm (BitVec.ofNat 64 1), .imm (BitVec.ofNat 64 1), ())) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 24, .imm (BitVec.ofNat 64 288), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 30), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.shl i64, (.imm (BitVec.ofNat 64 1), .var 0, ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i64, i64]) 0
            (.imm (BitVec.ofNat 64 1), .imm (BitVec.ofNat 64 1), ())) <|
            TFlat.jump (ts := [i64, i64]) 0 (.var 10, .var 9, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [i64]) ⟨.sub i64, (.imm (BitVec.ofNat 64 0), .var 1, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.and i64, (.var 2, .var 0, ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl, (.var 0, .var 2, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jump (ts := [i64, i64]) 0 (.var 0, .imm (BitVec.ofNat 64 1), ())) <|
            TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 3, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jump (ts := [i64, i64]) 0 (.var 5, .var 0, ())) <|
          TBlocks.nil) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
          (.var 2, .imm (BitVec.ofNat 64 0), ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.jump (ts := [i64, i64]) 0
            (.imm (BitVec.ofNat 64 1), .imm (BitVec.ofNat 64 1), ())) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
          (.var 1, .imm (BitVec.ofNat 64 0), ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.jump (ts := [i64, i64]) 0
            (.imm (BitVec.ofNat 64 1), .imm (BitVec.ofNat 64 1), ())) <|
        TFlat.jump (ts := [i64, i64]) 0 (.var 4, .var 2, ())) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 9, .imm (BitVec.ofNat 64 304), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 12, .imm (BitVec.ofNat 64 304), ())⟩ <|
      TFlat.load i64 (.var 0) <|
      TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
      TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 15, .imm (BitVec.ofNat 64 304), ())⟩ <|
      TFlat.store (t := i64) (.var 1) (.var 0) <|
      TFlat.jump (ts := []) 0 ()) <|
    TFlat.jump (ts := []) 0 () }

@[expose] def flat3 : TFlatFn := {
  name := "full_fill_u64_m7",
  as := [i64, i64, i64],
  rs := [],
  body :=
    TFlat.group (sig := [[i64]])
      (TBlocks.cons (ts := [i64])
        (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl, (.var 0, .var 3, ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 2, .imm (BitVec.ofNat 64 8), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 6, .var 0, ())⟩ <|
          TFlat.store (t := i64) (.var 5) (.var 0) <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .imm (BitVec.ofNat 64 1), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 9, .var 0, ())⟩ <|
          TFlat.store (t := i64) (.var 8) (.var 0) <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .imm (BitVec.ofNat 64 2), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 12, .var 0, ())⟩ <|
          TFlat.store (t := i64) (.var 11) (.var 0) <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 10, .imm (BitVec.ofNat 64 3), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 15, .var 0, ())⟩ <|
          TFlat.store (t := i64) (.var 14) (.var 0) <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 13, .imm (BitVec.ofNat 64 4), ())⟩ <|
          TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
        TFlat.group (sig := [[i64]])
          (TBlocks.cons (ts := [i64])
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 0, .var 5, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 1, .imm (BitVec.ofNat 64 8), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 8, .var 0, ())⟩ <|
            TFlat.store (t := i64) (.var 7) (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 3, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
            TFlat.ret ()) <|
          TBlocks.nil) <|
        TFlat.jump (ts := [i64]) 0 (.var 2, ())) <|
      TBlocks.nil) <|
    TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 0), ()) }

@[expose] def flat4 : TFlatFn := {
  name := "full_sort_u32",
  as := [i64, i32],
  rs := [],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
      (.var 1, .imm (BitVec.ofNat 64 2), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 0), ())⟩ <|
      TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
      TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 6, .var 0, ())⟩ <|
      TFlat.load i32 (.var 0) <|
      TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
      TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
      TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 10, .var 0, ())⟩ <|
      TFlat.load i32 (.var 0) <|
      TFlat.group (sig := [[]])
        (TBlocks.cons (ts := [])
          (TFlat.ret ()) <|
        TBlocks.nil) <|
      TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i32 .bool rfl, (.var 4, .var 0, ())⟩ <|
      TFlat.jnz (.var 0)
        (TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 0), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 15, .var 0, ())⟩ <|
        TFlat.store (t := i32) (.var 4) (.var 0) <|
        TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 18, .var 0, ())⟩ <|
        TFlat.store (t := i32) (.var 11) (.var 0) <|
        TFlat.jump (ts := []) 0 ()) <|
      TFlat.jump (ts := []) 0 ()) <|
    TFlat.group (sig := [[i64]])
      (TBlocks.cons (ts := [i64])
        (TFlat.group (sig := [[i64]])
          (TBlocks.cons (ts := [i64])
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 0, .var 6, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 1, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 10, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.group (sig := [[i64, .bool]])
            (TBlocks.cons (ts := [i64, .bool])
            (TFlat.jnz (.var 0)
            (TFlat.group (sig := [[i64, .bool]])
            (TBlocks.cons (ts := [i64, .bool])
            (TFlat.jump (ts := [i64, .bool]) 1 (.var 1, .var 0, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 1, .var 8, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i64, .bool]) 0 (.var 2, .imm false, ())) <|
            TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 2, .var 9, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 17, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.group (sig := [[i64, .bool]])
            (TBlocks.cons (ts := [i64, .bool])
            (TFlat.jump (ts := [i64, .bool]) 1 (.var 1, .var 0, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i32 .bool rfl, (.var 0, .var 7, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i64, .bool]) 0 (.var 7, .imm false, ())) <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 7, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 21, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 3) (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 9, .var 16, ())⟩ <|
            TFlat.jump (ts := [i64, .bool]) 0 (.var 0, .var 9, ())) <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 1, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 15, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 4) (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 8, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jump (ts := [i64]) 1 (.var 0, ())) <|
            TBlocks.nil) <|
            TFlat.jump (ts := [i64, .bool]) 0 (.var 4, .imm true, ())) <|
            TFlat.let_ (ts := [i64]) ⟨.udiv 64, (.var 3, .imm (BitVec.ofNat 64 3), ())⟩ <|
            TFlat.jump (ts := [i64]) 1 (.var 0, ())) <|
            TBlocks.nil) <|
            TFlat.jump (ts := [i64]) 0 (.var 1, ())) <|
            TFlat.ret ()) <|
          TBlocks.nil) <|
        TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl,
      (.var 2, .imm (BitVec.ofNat 64 16), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.let_ (ts := [i64]) ⟨.udiv 64, (.var 3, .imm (BitVec.ofNat 64 3), ())⟩ <|
      TFlat.group (sig := [[i64]])
        (TBlocks.cons (ts := [i64])
          (TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 0, .var 1, ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 1, .imm (BitVec.ofNat 64 3), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
          TFlat.jump (ts := [i64]) 1 (.var 1, ())) <|
        TBlocks.nil) <|
      TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 1), ())) <|
    TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 1), ()) }

@[expose] def flat5 : TFlatFn := {
  name := "full_elim_dticks",
  as := [i64, .bool],
  rs := [i64],
  body :=
    TFlat.group (sig := [[i64]])
      (TBlocks.cons (ts := [i64])
        (TFlat.group (sig := [[i64]])
          (TBlocks.cons (ts := [i64])
            (TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.ret (.var 0, ())) <|
            TBlocks.nil) <|
            TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.jump (ts := [i64]) 1 (.var 0, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 10000000), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i64]) 0 (.var 1, ())) <|
            TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 10000000), ())) <|
          TBlocks.nil) <|
        TFlat.jnz (.var 1)
          (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .imm (BitVec.ofNat 64 776), ())⟩ <|
          TFlat.load i64 (.var 0) <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .imm (BitVec.ofNat 64 488), ())⟩ <|
          TFlat.load i64 (.var 0) <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .var 0, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .imm (BitVec.ofNat 64 504), ())⟩ <|
          TFlat.load i64 (.var 0) <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .var 0, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 12), ())⟩ <|
          TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
        TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .imm (BitVec.ofNat 64 600), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 3, .imm (BitVec.ofNat 64 1128), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 6, .imm (BitVec.ofNat 64 600), ())⟩ <|
      TFlat.load i64 (.var 0) <|
      TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 8, .imm (BitVec.ofNat 64 1128), ())⟩ <|
      TFlat.load i64 (.var 0) <|
      TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 2, .var 0, ())⟩ <|
      TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
    TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 0), ()) }

@[expose] def flat6 : TFlatFn := {
  name := "full_lcg_next_m7",
  as := [i64],
  rs := [i64],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 944), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64,
      (.var 0, .imm (BitVec.ofNat 64 6364136223846793005), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64,
      (.var 0, .imm (BitVec.ofNat 64 1442695040888963407), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .imm (BitVec.ofNat 64 944), ())⟩ <|
    TFlat.store (t := i64) (.var 1) (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 32), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.lshr i64, (.var 2, .var 0, ())⟩ <|
    TFlat.ret (.var 0, ()) }

@[expose] def flat7 : TFlatFn := {
  name := "full_m7_get64",
  as := [i64, i64],
  rs := [i64],
  body :=
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 63), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm (BitVec.ofNat 64 0), ())) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .imm (BitVec.ofNat 64 432), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 3, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .var 0, ())⟩ <|
    TFlat.load i32 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .imm (BitVec.ofNat 64 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 6, .var 0, ())⟩ <|
    TFlat.load i32 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 32), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 1, .var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.or i64, (.var 7, .var 0, ())⟩ <|
    TFlat.ret (.var 0, ()) }

@[expose] def flat8 : TFlatFn := {
  name := "full_m7_set64",
  as := [i64, i64, i64],
  rs := [],
  body :=
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl,
      (.var 1, .imm (BitVec.ofNat 64 63), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 3, .imm (BitVec.ofNat 64 432), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 4, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .var 0, ())⟩ <|
    TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 5, ())⟩ <|
    TFlat.store (t := i32) (.var 0) (.var 1) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .imm (BitVec.ofNat 64 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 32), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.lshr i64, (.var 10, .var 0, ())⟩ <|
    TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 0, ())⟩ <|
    TFlat.store (t := i32) (.var 0) (.var 3) <|
    TFlat.ret () }

@[expose] def fns : List Fn := [flat0.toFn, flat1.toFn, flat2.toFn, flat3.toFn, flat4.toFn,
    flat5.toFn, flat6.toFn, flat7.toFn, flat8.toFn]

end LeanQbe.T.Examples.Kissat.Build.Inl.Limits.Exports
