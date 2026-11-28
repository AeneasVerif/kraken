module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports

open LeanQbe.T

@[expose] def flat0 : TFlatFn := {
  name := "full_watch_push_m6",
  as := [i64, i32, i32, i32, i32],
  rs := [.bool],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 3, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .imm (BitVec.ofNat 64 776), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 1, .var 0, ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 4, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm false, ())) <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 6, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 11, .imm (BitVec.ofNat 64 56), ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 13, .imm (BitVec.ofNat 64 40), ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.group (sig := [[]])
          (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 4, ())⟩ <|
            TFlat.call "full_watch_push_slow_m6" (as := [i64, i32, i32, i32, i32]) [.bool]
            (.var 16, .var 15, .var 14, .var 13, .var 0, ()) <|
            TFlat.ret (.var 0, ())) <|
          TBlocks.nil) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
          (.var 2, .imm (BitVec.ofNat 64 0), ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 15, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 1, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 19, .imm (BitVec.ofNat 64 104), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 21, .imm (BitVec.ofNat 64 120), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 4, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 3, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 8, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 8, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .var 0, ())⟩ <|
            TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.jump (ts := []) 2 ()) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl, (.var 1, .var 21, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 20, .var 22, ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl, (.var 25, .var 0, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 4, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 15, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 37) (.var 0) <|
            TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 20, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 20, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 10, ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 32, ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.add i32, (.var 1, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 0) (.var 3) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 12, .var 34, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 46, .imm (BitVec.ofNat 64 56), ())⟩ <|
            TFlat.store (t := i64) (.var 1) (.var 0) <|
            TFlat.ret (.imm true, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 28, .imm (BitVec.ofNat 64 2), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 19, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 40) (.var 0) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.jump (ts := []) 1 ()) <|
            TFlat.jump (ts := []) 1 ()) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .var 23, ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl, (.var 0, .var 22, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 3, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 14, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i32 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 32 4294967295), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 7, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 18, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 40) (.var 0) <|
            TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 23, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 23, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 13, ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 35, ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.add i32, (.var 1, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 0) (.var 3) <|
            TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.ret (.imm true, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 48, .imm (BitVec.ofNat 64 464), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 0, .var 39, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 51, .imm (BitVec.ofNat 64 464), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 0, .var 42, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 54, .imm (BitVec.ofNat 64 464), ())⟩ <|
            TFlat.store (t := i64) (.var 1) (.var 0) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.jump (ts := []) 0 ()) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 31, .imm (BitVec.ofNat 64 2), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 10, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 22, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 43) (.var 0) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.jump (ts := []) 0 ()) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 29, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := []) 0 ()) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 8, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 20, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i32 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 32 4294967295), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := []) 0 ()) <|
            TFlat.jump (ts := []) 1 ()) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 19, .var 21, ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl, (.var 24, .var 0, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 23, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 14, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 36) (.var 0) <|
            TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 19, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 18, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 27, ())⟩ <|
            TFlat.store (t := i32) (.var 0) (.var 1) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 22, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 22, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 33, ())⟩ <|
            TFlat.store (t := i32) (.var 0) (.var 1) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 32, .var 34, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 46, .imm (BitVec.ofNat 64 56), ())⟩ <|
            TFlat.store (t := i64) (.var 1) (.var 0) <|
            TFlat.ret (.imm true, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 27, .imm (BitVec.ofNat 64 2), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 26, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 18, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 39) (.var 0) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.jump (ts := []) 0 ()) <|
            TBlocks.nil) <|
          TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 16, .imm (BitVec.ofNat 64 464), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 6, .imm (BitVec.ofNat 64 3), ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 1, .var 0, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := []) 1 ()) <|
            TFlat.jump (ts := []) 2 ()) <|
            TBlocks.nil) <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl,
            (.var 3, .imm (BitVec.ofNat 64 262144), ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 4, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 3, .imm (BitVec.ofNat 64 3), ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 1, .var 0, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := []) 1 ()) <|
            TFlat.jump (ts := []) 0 ()) <|
          TFlat.jump (ts := []) 0 ()) <|
        TFlat.jump (ts := []) 0 ()) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl,
      (.var 6, .imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl,
        (.var 7, .imm (BitVec.ofNat 32 2), ())⟩ <|
      TFlat.jnz (.var 0)
        (TFlat.ret (.imm false, ())) <|
      TFlat.jump (ts := []) 0 ()) <|
    TFlat.jump (ts := []) 0 () }

@[expose] def flat1 : TFlatFn := {
  name := "full_wstack_defrag",
  as := [i64],
  rs := [],
  body :=
    TFlat.call "full_wstack_defrag_m6" (as := [i64]) [] (.var 0, ()) <|
    TFlat.ret () }

@[expose] def flat2 : TFlatFn := {
  name := "full_watch_push",
  as := [i64, i32, i32, i32, i32],
  rs := [.bool],
  body :=
    TFlat.group (sig := [[.bool]])
      (TBlocks.cons (ts := [.bool])
        (TFlat.ret (.var 0, ())) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 3, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .imm (BitVec.ofNat 64 776), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 1, .var 0, ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 4, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.jump (ts := [.bool]) 0 (.imm false, ())) <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 6, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 11, .imm (BitVec.ofNat 64 56), ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 13, .imm (BitVec.ofNat 64 40), ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.group (sig := [[]])
          (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 4, ())⟩ <|
            TFlat.call "full_watch_push_slow_m6" (as := [i64, i32, i32, i32, i32]) [.bool]
            (.var 16, .var 15, .var 14, .var 13, .var 0, ()) <|
            TFlat.jump (ts := [.bool]) 2 (.var 0, ())) <|
          TBlocks.nil) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
          (.var 2, .imm (BitVec.ofNat 64 0), ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 15, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 1, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 19, .imm (BitVec.ofNat 64 104), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 21, .imm (BitVec.ofNat 64 120), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 4, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 3, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 8, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 8, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .var 0, ())⟩ <|
            TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.jump (ts := []) 2 ()) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl, (.var 1, .var 21, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 20, .var 22, ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl, (.var 25, .var 0, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 4, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 15, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 37) (.var 0) <|
            TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 20, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 20, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 10, ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 32, ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.add i32, (.var 1, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 0) (.var 3) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 12, .var 34, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 46, .imm (BitVec.ofNat 64 56), ())⟩ <|
            TFlat.store (t := i64) (.var 1) (.var 0) <|
            TFlat.jump (ts := [.bool]) 6 (.imm true, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 28, .imm (BitVec.ofNat 64 2), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 19, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 40) (.var 0) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.jump (ts := []) 1 ()) <|
            TFlat.jump (ts := []) 1 ()) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .var 23, ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl, (.var 0, .var 22, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 3, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 14, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i32 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 32 4294967295), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 7, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 18, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 40) (.var 0) <|
            TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 23, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 23, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 13, ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 35, ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.add i32, (.var 1, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 0) (.var 3) <|
            TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.jump (ts := [.bool]) 8 (.imm true, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 48, .imm (BitVec.ofNat 64 464), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 0, .var 39, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 51, .imm (BitVec.ofNat 64 464), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 0, .var 42, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 54, .imm (BitVec.ofNat 64 464), ())⟩ <|
            TFlat.store (t := i64) (.var 1) (.var 0) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.jump (ts := []) 0 ()) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 31, .imm (BitVec.ofNat 64 2), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 10, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 22, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 43) (.var 0) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.jump (ts := []) 0 ()) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 29, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := []) 0 ()) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 8, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 20, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i32 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 32 4294967295), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := []) 0 ()) <|
            TFlat.jump (ts := []) 1 ()) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 19, .var 21, ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl, (.var 24, .var 0, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 23, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 14, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 36) (.var 0) <|
            TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 19, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 18, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 27, ())⟩ <|
            TFlat.store (t := i32) (.var 0) (.var 1) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 22, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 22, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 33, ())⟩ <|
            TFlat.store (t := i32) (.var 0) (.var 1) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 32, .var 34, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 46, .imm (BitVec.ofNat 64 56), ())⟩ <|
            TFlat.store (t := i64) (.var 1) (.var 0) <|
            TFlat.jump (ts := [.bool]) 5 (.imm true, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 27, .imm (BitVec.ofNat 64 2), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 26, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 18, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 39) (.var 0) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.jump (ts := []) 0 ()) <|
            TBlocks.nil) <|
          TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 16, .imm (BitVec.ofNat 64 464), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 6, .imm (BitVec.ofNat 64 3), ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 1, .var 0, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := []) 1 ()) <|
            TFlat.jump (ts := []) 2 ()) <|
            TBlocks.nil) <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl,
            (.var 3, .imm (BitVec.ofNat 64 262144), ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 4, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 3, .imm (BitVec.ofNat 64 3), ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 1, .var 0, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := []) 1 ()) <|
            TFlat.jump (ts := []) 0 ()) <|
          TFlat.jump (ts := []) 0 ()) <|
        TFlat.jump (ts := []) 0 ()) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl,
      (.var 6, .imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl,
        (.var 7, .imm (BitVec.ofNat 32 2), ())⟩ <|
      TFlat.jnz (.var 0)
        (TFlat.jump (ts := [.bool]) 1 (.imm false, ())) <|
      TFlat.jump (ts := []) 0 ()) <|
    TFlat.jump (ts := []) 0 () }

@[expose] def flat3 : TFlatFn := {
  name := "full_watch_pop_c0",
  as := [i64, i32, i32],
  rs := [],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 1, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 3, .imm (BitVec.ofNat 64 776), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 1, .var 0, ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 4, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 8, .imm (BitVec.ofNat 64 104), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 10, .imm (BitVec.ofNat 64 120), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 11, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 1, .var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 6, .var 0, ())⟩ <|
    TFlat.load i32 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 18, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 1, .var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 14, .var 0, ())⟩ <|
    TFlat.load i32 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 25, ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 2, .var 1, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 11, .var 3, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 31, .imm (BitVec.ofNat 64 56), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 7, .var 6, ())⟩ <|
    TFlat.group (sig := [[i64]])
      (TBlocks.cons (ts := [i64])
        (TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 0, .var 9, ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 18, .var 1, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 27, .var 0, ())⟩ <|
          TFlat.store (t := i32) (.imm (BitVec.ofNat 32 4294967295)) (.var 0) <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .imm (BitVec.ofNat 64 1), ())⟩ <|
          TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
        TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 36, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 1, .var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 32, .var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 16, .var 15, ())⟩ <|
        TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 0, ())⟩ <|
        TFlat.store (t := i32) (.var 0) (.var 2) <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 45, .imm (BitVec.ofNat 64 464), ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .var 19, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 48, .imm (BitVec.ofNat 64 464), ())⟩ <|
        TFlat.store (t := i64) (.var 1) (.var 0) <|
        TFlat.ret ()) <|
      TBlocks.nil) <|
    TFlat.jump (ts := [i64]) 0 (.var 0, ()) }

@[expose] def flat4 : TFlatFn := {
  name := "full_has_bin",
  as := [i64, i32, i32],
  rs := [.bool],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .imm (BitVec.ofNat 64 776), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 1, .var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 5, ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 0, .var 1, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm false, ())) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 6, ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 0, .var 3, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm false, ())) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i32 .bool rfl, (.var 9, .var 8, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm false, ())) <|
    TFlat.let_ (ts := [i32]) ⟨.xor i32, (.var 9, .imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i32 .bool rfl, (.var 11, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm false, ())) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 13, .imm (BitVec.ofNat 64 104), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 15, .imm (BitVec.ofNat 64 120), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 16, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 1, .var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .var 0, ())⟩ <|
    TFlat.load i32 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 23, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 1, .var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 15, .var 0, ())⟩ <|
    TFlat.load i32 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
    TFlat.group (sig := [[i32]])
      (TBlocks.cons (ts := [i32])
        (TFlat.group (sig := [[i32]])
          (TBlocks.cons (ts := [i32])
            (TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 1, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 1, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 24, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 8, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 1, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 32, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 8, .var 0, ())⟩ <|
            TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 0, .var 1, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 1, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 37, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.jump (ts := [i64]) 1 (.var 0, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [i32]) ⟨.and i32,
            (.var 0, .imm (BitVec.ofNat 32 2147483648), ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 32 0), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i32]) ⟨.and i32,
            (.var 2, .imm (BitVec.ofNat 32 2147483647), ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i32 .bool rfl, (.var 0, .var 24, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.ret (.imm true, ())) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 8, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 6, .imm (BitVec.ofNat 64 2), ())⟩ <|
            TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
            TFlat.ret (.imm false, ())) <|
            TBlocks.nil) <|
            TFlat.jump (ts := [i64]) 0 (.var 9, ())) <|
          TBlocks.nil) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl, (.var 9, .var 1, ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.jump (ts := [i32]) 0 (.var 33, ())) <|
        TFlat.jump (ts := [i32]) 0 (.var 34, ())) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl, (.var 8, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.jump (ts := [i32]) 0 (.var 33, ())) <|
    TFlat.jump (ts := [i32]) 0 (.var 32, ()) }

@[expose] def flat5 : TFlatFn := {
  name := "full_delete_bin_side",
  as := [i64, i32, i32],
  rs := [],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 1, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 3, .imm (BitVec.ofNat 64 776), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 1, .var 0, ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 4, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 8, .imm (BitVec.ofNat 64 104), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 10, .imm (BitVec.ofNat 64 120), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 11, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 1, .var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 6, .var 0, ())⟩ <|
    TFlat.load i32 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 18, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 1, .var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 14, .var 0, ())⟩ <|
    TFlat.load i32 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 9, .var 1, ())⟩ <|
    TFlat.group (sig := [[i64, .bool]])
      (TBlocks.cons (ts := [i64, .bool])
        (TFlat.jnz (.var 0)
          (TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 0, .var 3, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 1, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 23, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 4, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 25, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.store (t := i32) (.var 0) (.var 3) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
            TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 4, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 23, .var 0, ())⟩ <|
            TFlat.store (t := i32) (.imm (BitVec.ofNat 32 4294967295)) (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 35, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 1, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 31, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 15, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i32]) ⟨.trunc 64 32, (.var 0, ())⟩ <|
            TFlat.store (t := i32) (.var 0) (.var 2) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 44, .imm (BitVec.ofNat 64 464), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 47, .imm (BitVec.ofNat 64 464), ())⟩ <|
            TFlat.store (t := i64) (.var 1) (.var 0) <|
            TFlat.ret ()) <|
            TBlocks.nil) <|
          TFlat.jump (ts := [i64]) 0 (.var 1, ())) <|
        TFlat.ret ()) <|
      TBlocks.nil) <|
    TFlat.group (sig := [[i64]])
      (TBlocks.cons (ts := [i64])
        (TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 0, .var 1, ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 1, .imm (BitVec.ofNat 64 4), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 20, .var 0, ())⟩ <|
          TFlat.load i32 (.var 0) <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .imm (BitVec.ofNat 64 1), ())⟩ <|
          TFlat.group (sig := [[i64, .bool]])
            (TBlocks.cons (ts := [i64, .bool])
            (TFlat.jump (ts := [i64]) 1 (.var 1, ())) <|
            TBlocks.nil) <|
          TFlat.let_ (ts := [i32]) ⟨.and i32,
            (.var 1, .imm (BitVec.ofNat 32 2147483648), ())⟩ <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 32 0), ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i32]) ⟨.and i32,
            (.var 3, .imm (BitVec.ofNat 32 2147483647), ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i32 .bool rfl, (.var 0, .var 36, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i64, .bool]) 2 (.var 4, .imm true, ())) <|
            TFlat.jump (ts := [i64, .bool]) 0 (.var 4, .imm false, ())) <|
          TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.jump (ts := [i64, .bool]) 1 (.var 0, .imm false, ())) <|
            TBlocks.nil) <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 2, .var 8, ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 3, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
          TFlat.jump (ts := [i64]) 0 (.var 3, ())) <|
        TFlat.jump (ts := [i64, .bool]) 1 (.var 1, .imm false, ())) <|
      TBlocks.nil) <|
    TFlat.jump (ts := [i64]) 0 (.var 10, ()) }

@[expose] def flat6 : TFlatFn := {
  name := "full_sort_bin_watches_fid",
  as := [i64],
  rs := [],
  body :=
    TFlat.ret () }

@[expose] def fns : List Fn := [flat0.toFn, flat1.toFn, flat2.toFn, flat3.toFn, flat4.toFn,
    flat5.toFn, flat6.toFn]

end LeanQbe.T.Examples.Kissat.Build.Inl.Watch.Exports
