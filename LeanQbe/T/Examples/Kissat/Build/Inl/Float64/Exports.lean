module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports

open LeanQbe.T

@[expose] def flat0 : TFlatFn := {
  name := "f64u_from_u64",
  as := [i64],
  rs := [i64],
  body :=
    TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm (BitVec.ofNat 64 0), ())) <|
    TFlat.group (sig := [[i64]])
      (TBlocks.cons (ts := [i64])
        (TFlat.let_ (ts := [i64]) ⟨.add i64, (.imm (BitVec.ofNat 64 1023), .var 0, ())⟩ <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl,
          (.var 1, .imm (BitVec.ofNat 64 52), ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.let_ (ts := [i64]) ⟨.sub i64, (.imm (BitVec.ofNat 64 52), .var 2, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 5, .var 0, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 52), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 4, .var 0, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 52), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.shl i64, (.imm (BitVec.ofNat 64 1), .var 0, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.and i64, (.var 5, .var 0, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.or i64, (.var 4, .var 0, ())⟩ <|
          TFlat.ret (.var 0, ())) <|
        TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 2, .imm (BitVec.ofNat 64 52), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.lshr i64, (.var 5, .var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.shl i64, (.imm (BitVec.ofNat 64 1), .var 1, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.and i64, (.var 8, .var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 4, .imm (BitVec.ofNat 64 1), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.shl i64, (.imm (BitVec.ofNat 64 1), .var 0, ())⟩ <|
        TFlat.group (sig := [[i64, i64]])
          (TBlocks.cons (ts := [i64, i64])
            (TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 52), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 2, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 52), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.shl i64, (.imm (BitVec.ofNat 64 1), .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.and i64, (.var 5, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.or i64, (.var 4, .var 0, ())⟩ <|
            TFlat.ret (.var 0, ())) <|
          TBlocks.nil) <|
        TFlat.group (sig := [[]])
          (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.group (sig := [[i64, i64]])
            (TBlocks.cons (ts := [i64, i64])
            (TFlat.jump (ts := [i64, i64]) 2 (.var 1, .var 0, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 53), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.shl i64, (.imm (BitVec.ofNat 64 1), .var 0, ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.lshr i64, (.var 4, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 14, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jump (ts := [i64, i64]) 0 (.var 0, .var 1, ())) <|
            TFlat.jump (ts := [i64, i64]) 0 (.var 12, .var 3, ())) <|
          TBlocks.nil) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.jump (ts := []) 0 ()) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl, (.var 3, .var 1, ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.let_ (ts := [i64]) ⟨.and i64, (.var 7, .imm (BitVec.ofNat 64 1), ())⟩ <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.jump (ts := []) 0 ()) <|
          TFlat.jump (ts := [i64, i64]) 1 (.var 12, .var 9, ())) <|
        TFlat.jump (ts := [i64, i64]) 1 (.var 10, .var 7, ())) <|
      TBlocks.nil) <|
    TFlat.group (sig := [[i64, i64]])
      (TBlocks.cons (ts := [i64, i64])
        (TFlat.group (sig := [[i64, i64]])
          (TBlocks.cons (ts := [i64, i64])
            (TFlat.group (sig := [[i64, i64]])
            (TBlocks.cons (ts := [i64, i64])
            (TFlat.group (sig := [[i64, i64]])
            (TBlocks.cons (ts := [i64, i64])
            (TFlat.group (sig := [[i64, i64]])
            (TBlocks.cons (ts := [i64, i64])
            (TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.jump (ts := [i64]) 6 (.var 0, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl,
            (.var 1, .imm (BitVec.ofNat 64 2), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
            TFlat.jump (ts := [i64]) 0 (.var 1, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 2), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.shl i64, (.imm (BitVec.ofNat 64 1), .var 0, ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 3, .var 0, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 2), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.lshr i64, (.var 5, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .imm (BitVec.ofNat 64 2), ())⟩ <|
            TFlat.jump (ts := [i64, i64]) 0 (.var 1, .var 0, ())) <|
            TFlat.jump (ts := [i64, i64]) 0 (.var 4, .var 3, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.shl i64, (.imm (BitVec.ofNat 64 1), .var 0, ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 3, .var 0, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.lshr i64, (.var 5, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.jump (ts := [i64, i64]) 0 (.var 1, .var 0, ())) <|
            TFlat.jump (ts := [i64, i64]) 0 (.var 4, .var 3, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 8), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.shl i64, (.imm (BitVec.ofNat 64 1), .var 0, ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 3, .var 0, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 8), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.lshr i64, (.var 5, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .imm (BitVec.ofNat 64 8), ())⟩ <|
            TFlat.jump (ts := [i64, i64]) 0 (.var 1, .var 0, ())) <|
            TFlat.jump (ts := [i64, i64]) 0 (.var 4, .var 3, ())) <|
          TBlocks.nil) <|
        TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 16), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.shl i64, (.imm (BitVec.ofNat 64 1), .var 0, ())⟩ <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 3, .var 0, ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 16), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.lshr i64, (.var 5, .var 0, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .imm (BitVec.ofNat 64 16), ())⟩ <|
          TFlat.jump (ts := [i64, i64]) 0 (.var 1, .var 0, ())) <|
        TFlat.jump (ts := [i64, i64]) 0 (.var 4, .var 3, ())) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 32), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.shl i64, (.imm (BitVec.ofNat 64 1), .var 0, ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 3, .var 0, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 32), ())⟩ <|
      TFlat.let_ (ts := [i64]) ⟨.lshr i64, (.var 5, .var 0, ())⟩ <|
      TFlat.let_ (ts := [i64]) ⟨.add i64,
        (.imm (BitVec.ofNat 64 0), .imm (BitVec.ofNat 64 32), ())⟩ <|
      TFlat.jump (ts := [i64, i64]) 0 (.var 1, .var 0, ())) <|
    TFlat.jump (ts := [i64, i64]) 0 (.var 4, .imm (BitVec.ofNat 64 0), ()) }

@[expose] def flat1 : TFlatFn := {
  name := "f64u_to_u64",
  as := [i64],
  rs := [i64],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 52), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.lshr i64, (.var 1, .var 0, ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 1023), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm (BitVec.ofNat 64 0), ())) <|
    TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 1, .imm (BitVec.ofNat 64 1023), ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 64), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm (BitVec.ofNat 64 18446744073709551615), ())) <|
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
      TFlat.ret (.var 0, ())) <|
    TFlat.let_ (ts := [i64]) ⟨.sub i64, (.imm (BitVec.ofNat 64 52), .var 9, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.lshr i64, (.var 2, .var 0, ())⟩ <|
    TFlat.ret (.var 0, ()) }

@[expose] def flat2 : TFlatFn := {
  name := "m6_wm4_get",
  as := [i64],
  rs := [i64],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 0, .imm (BitVec.ofNat 64 2304), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 0), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .var 0, ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 5563713847938078769), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm (BitVec.ofNat 64 0), ())) <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64,
      (.imm (BitVec.ofNat 64 28), .imm (BitVec.ofNat 64 8), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 6, .var 0, ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.ret (.var 0, ()) }

@[expose] def flat3 : TFlatFn := {
  name := "m6_wm4_set",
  as := [i64, i64],
  rs := [],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 1, .imm (BitVec.ofNat 64 2304), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 0), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .var 0, ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 5563713847938078769), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64,
      (.imm (BitVec.ofNat 64 28), .imm (BitVec.ofNat 64 8), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 6, .var 0, ())⟩ <|
    TFlat.store (t := i64) (.var 8) (.var 0) <|
    TFlat.ret () }

@[expose] def fns : List Fn := [flat0.toFn, flat1.toFn, flat2.toFn, flat3.toFn]

end LeanQbe.T.Examples.Kissat.Build.Inl.Float64.Exports
