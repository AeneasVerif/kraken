module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Collect.Exports

open LeanQbe.T

@[expose] def flat0 : TFlatFn := {
  name := "full_lit_rank_m6",
  as := [i64, i64, i32],
  rs := [i64],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 3, .var 0, ())⟩ <|
    TFlat.load i8 (.var 0) <|
    TFlat.let_ (ts := [i8]) ⟨.trunc 32 8, (.imm (BitVec.ofNat 32 0), ())⟩ <|
    TFlat.let_ (ts := [i32]) ⟨.sext 8 32, (.var 1, ())⟩ <|
    TFlat.let_ (ts := [i32]) ⟨.sext 8 32, (.var 1, ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .sgt i32 .bool rfl, (.var 1, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.let_ (ts := [i32]) ⟨.lshr i32, (.var 7, .imm (BitVec.ofNat 32 1), ())⟩ <|
      TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
      TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
      TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 11, .var 0, ())⟩ <|
      TFlat.load i32 (.var 0) <|
      TFlat.let_ (ts := [i32]) ⟨.not i32, (.var 0, ())⟩ <|
      TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
      TFlat.let_ (ts := [i64]) ⟨.or i64, (.imm (BitVec.ofNat 64 8589934592), .var 0, ())⟩ <|
      TFlat.ret (.var 0, ())) <|
    TFlat.let_ (ts := [i8]) ⟨.trunc 32 8, (.imm (BitVec.ofNat 32 0), ())⟩ <|
    TFlat.let_ (ts := [i32]) ⟨.sext 8 32, (.var 5, ())⟩ <|
    TFlat.let_ (ts := [i32]) ⟨.sext 8 32, (.var 1, ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i32 .bool rfl, (.var 1, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm (BitVec.ofNat 64 4294967296), ())) <|
    TFlat.let_ (ts := [i32]) ⟨.lshr i32, (.var 11, .imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 15, .var 0, ())⟩ <|
    TFlat.load i32 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
    TFlat.ret (.var 0, ()) }

@[expose] def flat1 : TFlatFn := {
  name := "full_sweep_bins",
  as := [i64],
  rs := [],
  body :=
    TFlat.call "full_sweep_bins_m6cf" (as := [i64]) [] (.var 0, ()) <|
    TFlat.ret () }

@[expose] def flat2 : TFlatFn := {
  name := "full_rewatch_arena",
  as := [i64, i64],
  rs := [.bool],
  body :=
    TFlat.group (sig := [[.bool]])
      (TBlocks.cons (ts := [.bool])
        (TFlat.ret (.var 0, ())) <|
      TBlocks.nil) <|
    TFlat.call "full_rewatch_range_m6" (as := [i64, i64, i64]) [.bool]
      (.var 1, .imm (BitVec.ofNat 64 0), .var 0, ()) <|
    TFlat.jump (ts := [.bool]) 0 (.var 0, ()) }

@[expose] def flat3 : TFlatFn := {
  name := "full_arena_sweep",
  as := [i64],
  rs := [i64],
  body :=
    TFlat.call "full_arena_sweep_m6" (as := [i64]) [i64] (.var 0, ()) <|
    TFlat.ret (.var 0, ()) }

@[expose] def flat4 : TFlatFn := {
  name := "full_mark_reasons",
  as := [i64, .bool],
  rs := [],
  body :=
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.ret ()) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .imm (BitVec.ofNat 64 160), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.jump (ts := []) 0 ()) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .imm (BitVec.ofNat 64 96), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 6, .imm (BitVec.ofNat 64 80), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 8, .imm (BitVec.ofNat 64 88), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 10, .imm (BitVec.ofNat 64 112), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 12, .imm (BitVec.ofNat 64 832), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 14, .imm (BitVec.ofNat 64 776), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 16, .imm (BitVec.ofNat 64 48), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 6, .var 0, ())⟩ <|
    TFlat.load i32 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
    TFlat.group (sig := [[i64]])
      (TBlocks.cons (ts := [i64])
        (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 24, .imm (BitVec.ofNat 64 144), ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 3, .imm (BitVec.ofNat 64 4), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 22, .var 0, ())⟩ <|
          TFlat.load i32 (.var 0) <|
          TFlat.let_ (ts := [i32]) ⟨.lshr i32, (.var 0, .imm (BitVec.ofNat 32 1), ())⟩ <|
          TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jump (ts := [i64]) 1 (.var 0, ())) <|
            TBlocks.nil) <|
          TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 0, .var 16, ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 2, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 27, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i32 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 32 0), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 7, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 30, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.jump (ts := []) 1 ()) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i32 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 32 2147483648), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 1, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 3), ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl, (.var 0, .var 27, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.jump (ts := []) 1 ()) <|
            TBlocks.nil) <|
            TFlat.jnz (.var 45)
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 4, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 36, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 7, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 39, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [i32]) ⟨.or i32, (.var 0, .imm (BitVec.ofNat 32 2097152), ())⟩ <|
            TFlat.store (t := i32) (.var 0) (.var 5) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 4, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 36, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 7, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 39, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [i32]) ⟨.not i32, (.imm (BitVec.ofNat 32 2097152), ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.and i32, (.var 1, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 0) (.var 6) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.jump (ts := []) 0 ()) <|
          TFlat.jump (ts := []) 0 ()) <|
        TFlat.jump (ts := []) 1 ()) <|
      TBlocks.nil) <|
    TFlat.jump (ts := [i64]) 0 (.var 0, ()) }

@[expose] def fns : List Fn := [flat0.toFn, flat1.toFn, flat2.toFn, flat3.toFn, flat4.toFn]

end LeanQbe.T.Examples.Kissat.Build.Inl.Collect.Exports
