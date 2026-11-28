module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Restart.Exports

open LeanQbe.T

@[expose] def flat0 : TFlatFn := {
  name := "full_restart_due",
  as := [i64],
  rs := [i64],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 160), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm (BitVec.ofNat 64 0), ())) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 3, .imm (BitVec.ofNat 64 336), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .imm (BitVec.ofNat 64 720), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm (BitVec.ofNat 64 0), ())) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 8, .imm (BitVec.ofNat 64 552), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 11, .imm (BitVec.ofNat 64 328), ())⟩ <|
      TFlat.load i64 (.var 0) <|
      TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
        (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
      TFlat.jnz (.var 0)
        (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 14, .imm (BitVec.ofNat 64 328), ())⟩ <|
        TFlat.store (t := i64) (.imm (BitVec.ofNat 64 0)) (.var 0) <|
        TFlat.ret (.imm (BitVec.ofNat 64 1), ())) <|
      TFlat.ret (.imm (BitVec.ofNat 64 0), ())) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 11, .imm (BitVec.ofNat 64 736), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 13, .imm (BitVec.ofNat 64 752), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 15, .imm (BitVec.ofNat 64 728), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 17, .imm (BitVec.ofNat 64 744), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.group (sig := [[.bool]])
      (TBlocks.cons (ts := [.bool])
        (TFlat.jnz (.var 0)
          (TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 9), ())⟩ <|
            TFlat.call "f64u_log10_u64" (as := [i64]) [i64] (.var 0, ()) <|
            TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 25, .imm (BitVec.ofNat 64 336), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .var 2, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 28, .imm (BitVec.ofNat 64 720), ())⟩ <|
            TFlat.store (t := i64) (.var 1) (.var 0) <|
            TFlat.ret (.imm (BitVec.ofNat 64 1), ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 1), ())) <|
            TFlat.jump (ts := [i64]) 0 (.var 1, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 52), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.lshr i64, (.var 1, .var 0, ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 1023), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 0), ())) <|
            TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 1, .imm (BitVec.ofNat 64 1023), ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 64), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 18446744073709551615), ())) <|
            TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 52), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.shl i64, (.imm (BitVec.ofNat 64 1), .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 52), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.shl i64, (.imm (BitVec.ofNat 64 1), .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.and i64, (.var 10, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.or i64, (.var 4, .var 0, ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl,
            (.var 8, .imm (BitVec.ofNat 64 52), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 9, .imm (BitVec.ofNat 64 52), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 2, .var 0, ())⟩ <|
            TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
            TFlat.let_ (ts := [i64]) ⟨.sub i64, (.imm (BitVec.ofNat 64 52), .var 9, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.lshr i64, (.var 2, .var 0, ())⟩ <|
            TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
            TBlocks.nil) <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 20, .imm (BitVec.ofNat 64 712), ())⟩ <|
          TFlat.load i64 (.var 0) <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 1000000000000), ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 23, .imm (BitVec.ofNat 64 712), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
          TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 1000000000000), ())) <|
        TFlat.ret (.imm (BitVec.ofNat 64 0), ())) <|
      TBlocks.nil) <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.group (sig := [[i64]])
          (TBlocks.cons (ts := [i64])
            (TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 1, .imm (BitVec.ofNat 64 0), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.ret (.imm (BitVec.ofNat 64 0), ())) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 1, .imm (BitVec.ofNat 64 0), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.ret (.imm (BitVec.ofNat 64 0), ())) <|
            TFlat.call "f64u_mul" (as := [i64, i64]) [i64]
            (.imm (BitVec.ofNat 64 4607632778762754458), .var 4, ()) <|
            TFlat.call "f64u_mul" (as := [i64, i64]) [i64] (.var 0, .var 4, ()) <|
            TFlat.call "f64u_mul" (as := [i64, i64]) [i64] (.var 8, .var 4, ()) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl, (.var 1, .var 0, ())⟩ <|
            TFlat.jump (ts := [.bool]) 3 (.var 0, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 5, .imm (BitVec.ofNat 64 0), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 4607182418800017408), ())) <|
            TFlat.call "f64u_sub" (as := [i64, i64]) [i64]
            (.imm (BitVec.ofNat 64 4607182418800017408), .var 6, ()) <|
            TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
          TBlocks.nil) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
          (.var 6, .imm (BitVec.ofNat 64 0), ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 4607182418800017408), ())) <|
        TFlat.call "f64u_sub" (as := [i64, i64]) [i64]
          (.imm (BitVec.ofNat 64 4607182418800017408), .var 7, ()) <|
        TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
      (.var 6, .imm (BitVec.ofNat 64 0), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
        (.var 5, .imm (BitVec.ofNat 64 0), ())⟩ <|
      TFlat.jnz (.var 0)
        (TFlat.call "f64u_mul" (as := [i64, i64]) [i64]
          (.imm (BitVec.ofNat 64 4607632778762754458), .var 2, ()) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl, (.var 0, .var 5, ())⟩ <|
        TFlat.jump (ts := [.bool]) 1 (.var 0, ())) <|
      TFlat.jump (ts := []) 0 ()) <|
    TFlat.jump (ts := []) 0 () }

@[expose] def fns : List Fn := [flat0.toFn]

end LeanQbe.T.Examples.Kissat.Build.Inl.Restart.Exports
