module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Dimacs.Exports

open LeanQbe.T

@[expose] def flat0 : TFlatFn := {
  name := "kissat_skip_ws_comments",
  as := [i64, i64],
  rs := [i64],
  body :=
    TFlat.group (sig := [[i64]])
      (TBlocks.cons (ts := [i64])
        (TFlat.ret (.var 0, ())) <|
      TBlocks.nil) <|
    TFlat.group (sig := [[i64]])
      (TBlocks.cons (ts := [i64])
        (TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 0, .var 1, ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.load i8 (.var 1) <|
          TFlat.let_ (ts := [i64]) ⟨.zext 8 64, (.var 0, ())⟩ <|
          TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.jump (ts := [i64]) 1 (.var 0, ())) <|
            TBlocks.nil) <|
          TFlat.group (sig := [[.bool]])
            (TBlocks.cons (ts := [.bool])
            (TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jump (ts := [i64]) 1 (.var 0, ())) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 1, .imm (BitVec.ofNat 64 99), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.jump (ts := [i64]) 2 (.var 0, ())) <|
            TBlocks.nil) <|
            TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 0, .var 8, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.load i8 (.var 1) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 8 64, (.var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 3, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 1, .imm (BitVec.ofNat 64 10), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i64]) 1 (.var 1, ())) <|
            TFlat.jump (ts := [i64]) 0 (.var 1, ())) <|
            TFlat.jump (ts := [i64]) 1 (.var 1, ())) <|
            TBlocks.nil) <|
            TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
            TFlat.jump (ts := [i64]) 3 (.var 5, ())) <|
            TBlocks.nil) <|
          TFlat.group (sig := [[.bool]])
            (TBlocks.cons (ts := [.bool])
            (TFlat.jump (ts := [.bool]) 1 (.var 0, ())) <|
            TBlocks.nil) <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 32), ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.jump (ts := [.bool]) 0 (.imm true, ())) <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl,
            (.var 1, .imm (BitVec.ofNat 64 9), ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl,
            (.var 2, .imm (BitVec.ofNat 64 13), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [.bool]) 0 (.imm true, ())) <|
            TFlat.jump (ts := [.bool]) 0 (.imm false, ())) <|
          TFlat.jump (ts := [.bool]) 0 (.imm false, ())) <|
        TFlat.jump (ts := [i64]) 1 (.var 1, ())) <|
      TBlocks.nil) <|
    TFlat.jump (ts := [i64]) 0 (.var 1, ()) }

@[expose] def flat1 : TFlatFn := {
  name := "kissat_next_lit",
  as := [i64, i64],
  rs := [i64],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 16), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.group (sig := [[i64]])
      (TBlocks.cons (ts := [i64])
        (TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 0, .var 4, ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.ret (.imm (BitVec.ofNat 64 0), ())) <|
        TFlat.load i8 (.var 1) <|
        TFlat.let_ (ts := [i64]) ⟨.zext 8 64, (.var 0, ())⟩ <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
          (.var 0, .imm (BitVec.ofNat 64 45), ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .imm (BitVec.ofNat 64 1), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 8, .imm (BitVec.ofNat 64 16), ())⟩ <|
          TFlat.store (t := i64) (.var 1) (.var 0) <|
          TFlat.group (sig := [[.bool]])
            (TBlocks.cons (ts := [.bool])
            (TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 10, .imm (BitVec.ofNat 64 24), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.ret (.imm (BitVec.ofNat 64 0), ())) <|
            TFlat.load i64 (.var 13) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.ret (.imm (BitVec.ofNat 64 0), ())) <|
            TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 3, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 1, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.or i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 19, .imm (BitVec.ofNat 64 24), ())⟩ <|
            TFlat.store (t := i64) (.var 1) (.var 0) <|
            TFlat.ret (.imm (BitVec.ofNat 64 2), ())) <|
            TFlat.ret (.imm (BitVec.ofNat 64 0), ())) <|
            TBlocks.nil) <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 9, .imm (BitVec.ofNat 64 16), ())⟩ <|
          TFlat.load i64 (.var 0) <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 0, .var 12, ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.jump (ts := [.bool]) 0 (.imm false, ())) <|
          TFlat.load i8 (.var 1) <|
          TFlat.let_ (ts := [i64]) ⟨.zext 8 64, (.var 0, ())⟩ <|
          TFlat.group (sig := [[.bool]])
            (TBlocks.cons (ts := [.bool])
            (TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 1, .imm (BitVec.ofNat 64 48), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.group (sig := [[i64, i64]])
            (TBlocks.cons (ts := [i64, i64])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 19, .imm (BitVec.ofNat 64 16), ())⟩ <|
            TFlat.store (t := i64) (.var 2) (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 20, .imm (BitVec.ofNat 64 24), ())⟩ <|
            TFlat.store (t := i64) (.var 2) (.var 0) <|
            TFlat.jump (ts := [.bool]) 2 (.imm true, ())) <|
            TBlocks.nil) <|
            TFlat.group (sig := [[i64, i64]])
            (TBlocks.cons (ts := [i64, i64])
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 1, .var 20, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.load i8 (.var 2) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 8 64, (.var 0, ())⟩ <|
            TFlat.group (sig := [[.bool]])
            (TBlocks.cons (ts := [.bool])
            (TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 4, .imm (BitVec.ofNat 64 10), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 2, .imm (BitVec.ofNat 64 48), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .var 0, ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 268435456), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [.bool]) 4 (.imm false, ())) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 9, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jump (ts := [i64, i64]) 1 (.var 0, .var 2, ())) <|
            TFlat.group (sig := [[.bool]])
            (TBlocks.cons (ts := [.bool])
            (TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i64, i64]) 3 (.var 6, .var 5, ())) <|
            TFlat.jump (ts := [.bool]) 5 (.imm false, ())) <|
            TBlocks.nil) <|
            TFlat.group (sig := [[.bool]])
            (TBlocks.cons (ts := [.bool])
            (TFlat.jump (ts := [.bool]) 1 (.var 0, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 1, .imm (BitVec.ofNat 64 32), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [.bool]) 0 (.imm true, ())) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl,
            (.var 2, .imm (BitVec.ofNat 64 9), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl,
            (.var 3, .imm (BitVec.ofNat 64 13), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [.bool]) 0 (.imm true, ())) <|
            TFlat.jump (ts := [.bool]) 0 (.imm false, ())) <|
            TFlat.jump (ts := [.bool]) 0 (.imm false, ())) <|
            TBlocks.nil) <|
            TFlat.group (sig := [[.bool]])
            (TBlocks.cons (ts := [.bool])
            (TFlat.jump (ts := [.bool]) 1 (.var 0, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 48), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl,
            (.var 1, .imm (BitVec.ofNat 64 57), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [.bool]) 0 (.imm true, ())) <|
            TFlat.jump (ts := [.bool]) 0 (.imm false, ())) <|
            TFlat.jump (ts := [.bool]) 0 (.imm false, ())) <|
            TFlat.jump (ts := [i64, i64]) 1 (.var 2, .var 1, ())) <|
            TBlocks.nil) <|
            TFlat.jump (ts := [i64, i64]) 0 (.var 0, .var 1, ())) <|
            TFlat.jump (ts := [.bool]) 1 (.imm false, ())) <|
            TBlocks.nil) <|
          TFlat.group (sig := [[.bool]])
            (TBlocks.cons (ts := [.bool])
            (TFlat.jump (ts := [.bool]) 1 (.var 0, ())) <|
            TBlocks.nil) <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 48), ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl,
            (.var 1, .imm (BitVec.ofNat 64 57), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [.bool]) 0 (.imm true, ())) <|
            TFlat.jump (ts := [.bool]) 0 (.imm false, ())) <|
          TFlat.jump (ts := [.bool]) 0 (.imm false, ())) <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .imm (BitVec.ofNat 64 16), ())⟩ <|
        TFlat.store (t := i64) (.var 5) (.var 0) <|
        TFlat.group (sig := [[.bool]])
          (TBlocks.cons (ts := [.bool])
            (TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 9, .imm (BitVec.ofNat 64 24), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.ret (.imm (BitVec.ofNat 64 1), ())) <|
            TFlat.load i64 (.var 12) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.ret (.imm (BitVec.ofNat 64 0), ())) <|
            TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 3, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 1, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 17, .imm (BitVec.ofNat 64 24), ())⟩ <|
            TFlat.store (t := i64) (.var 1) (.var 0) <|
            TFlat.ret (.imm (BitVec.ofNat 64 2), ())) <|
            TFlat.ret (.imm (BitVec.ofNat 64 0), ())) <|
          TBlocks.nil) <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 8, .imm (BitVec.ofNat 64 16), ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 0, .var 11, ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.jump (ts := [.bool]) 0 (.imm false, ())) <|
        TFlat.load i8 (.var 1) <|
        TFlat.let_ (ts := [i64]) ⟨.zext 8 64, (.var 0, ())⟩ <|
        TFlat.group (sig := [[.bool]])
          (TBlocks.cons (ts := [.bool])
            (TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 1, .imm (BitVec.ofNat 64 48), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.group (sig := [[i64, i64]])
            (TBlocks.cons (ts := [i64, i64])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 18, .imm (BitVec.ofNat 64 16), ())⟩ <|
            TFlat.store (t := i64) (.var 2) (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 19, .imm (BitVec.ofNat 64 24), ())⟩ <|
            TFlat.store (t := i64) (.var 2) (.var 0) <|
            TFlat.jump (ts := [.bool]) 2 (.imm true, ())) <|
            TBlocks.nil) <|
            TFlat.group (sig := [[i64, i64]])
            (TBlocks.cons (ts := [i64, i64])
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 1, .var 19, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.load i8 (.var 2) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 8 64, (.var 0, ())⟩ <|
            TFlat.group (sig := [[.bool]])
            (TBlocks.cons (ts := [.bool])
            (TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 4, .imm (BitVec.ofNat 64 10), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 2, .imm (BitVec.ofNat 64 48), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .var 0, ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 268435456), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [.bool]) 4 (.imm false, ())) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 9, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jump (ts := [i64, i64]) 1 (.var 0, .var 2, ())) <|
            TFlat.group (sig := [[.bool]])
            (TBlocks.cons (ts := [.bool])
            (TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i64, i64]) 3 (.var 6, .var 5, ())) <|
            TFlat.jump (ts := [.bool]) 5 (.imm false, ())) <|
            TBlocks.nil) <|
            TFlat.group (sig := [[.bool]])
            (TBlocks.cons (ts := [.bool])
            (TFlat.jump (ts := [.bool]) 1 (.var 0, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 1, .imm (BitVec.ofNat 64 32), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [.bool]) 0 (.imm true, ())) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl,
            (.var 2, .imm (BitVec.ofNat 64 9), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl,
            (.var 3, .imm (BitVec.ofNat 64 13), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [.bool]) 0 (.imm true, ())) <|
            TFlat.jump (ts := [.bool]) 0 (.imm false, ())) <|
            TFlat.jump (ts := [.bool]) 0 (.imm false, ())) <|
            TBlocks.nil) <|
            TFlat.group (sig := [[.bool]])
            (TBlocks.cons (ts := [.bool])
            (TFlat.jump (ts := [.bool]) 1 (.var 0, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 48), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl,
            (.var 1, .imm (BitVec.ofNat 64 57), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [.bool]) 0 (.imm true, ())) <|
            TFlat.jump (ts := [.bool]) 0 (.imm false, ())) <|
            TFlat.jump (ts := [.bool]) 0 (.imm false, ())) <|
            TFlat.jump (ts := [i64, i64]) 1 (.var 2, .var 1, ())) <|
            TBlocks.nil) <|
            TFlat.jump (ts := [i64, i64]) 0 (.var 0, .var 1, ())) <|
            TFlat.jump (ts := [.bool]) 1 (.imm false, ())) <|
          TBlocks.nil) <|
        TFlat.group (sig := [[.bool]])
          (TBlocks.cons (ts := [.bool])
            (TFlat.jump (ts := [.bool]) 1 (.var 0, ())) <|
          TBlocks.nil) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl,
          (.var 0, .imm (BitVec.ofNat 64 48), ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl,
            (.var 1, .imm (BitVec.ofNat 64 57), ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.jump (ts := [.bool]) 0 (.imm true, ())) <|
          TFlat.jump (ts := [.bool]) 0 (.imm false, ())) <|
        TFlat.jump (ts := [.bool]) 0 (.imm false, ())) <|
      TBlocks.nil) <|
    TFlat.group (sig := [[i64]])
      (TBlocks.cons (ts := [i64])
        (TFlat.jump (ts := [i64]) 1 (.var 0, ())) <|
      TBlocks.nil) <|
    TFlat.group (sig := [[i64]])
      (TBlocks.cons (ts := [i64])
        (TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 0, .var 4, ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.load i8 (.var 1) <|
          TFlat.let_ (ts := [i64]) ⟨.zext 8 64, (.var 0, ())⟩ <|
          TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.jump (ts := [i64]) 1 (.var 0, ())) <|
            TBlocks.nil) <|
          TFlat.group (sig := [[.bool]])
            (TBlocks.cons (ts := [.bool])
            (TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jump (ts := [i64]) 1 (.var 0, ())) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 1, .imm (BitVec.ofNat 64 99), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.jump (ts := [i64]) 2 (.var 0, ())) <|
            TBlocks.nil) <|
            TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 0, .var 11, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.load i8 (.var 1) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 8 64, (.var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 3, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 1, .imm (BitVec.ofNat 64 10), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i64]) 1 (.var 1, ())) <|
            TFlat.jump (ts := [i64]) 0 (.var 1, ())) <|
            TFlat.jump (ts := [i64]) 1 (.var 1, ())) <|
            TBlocks.nil) <|
            TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
            TFlat.jump (ts := [i64]) 3 (.var 5, ())) <|
            TBlocks.nil) <|
          TFlat.group (sig := [[.bool]])
            (TBlocks.cons (ts := [.bool])
            (TFlat.jump (ts := [.bool]) 1 (.var 0, ())) <|
            TBlocks.nil) <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 32), ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.jump (ts := [.bool]) 0 (.imm true, ())) <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl,
            (.var 1, .imm (BitVec.ofNat 64 9), ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl,
            (.var 2, .imm (BitVec.ofNat 64 13), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [.bool]) 0 (.imm true, ())) <|
            TFlat.jump (ts := [.bool]) 0 (.imm false, ())) <|
          TFlat.jump (ts := [.bool]) 0 (.imm false, ())) <|
        TFlat.jump (ts := [i64]) 1 (.var 1, ())) <|
      TBlocks.nil) <|
    TFlat.jump (ts := [i64]) 0 (.var 0, ()) }

@[expose] def fns : List Fn := [flat0.toFn, flat1.toFn]

end LeanQbe.T.Examples.Kissat.Build.Inl.Dimacs.Exports
