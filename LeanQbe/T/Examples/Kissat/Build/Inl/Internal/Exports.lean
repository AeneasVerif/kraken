module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Internal.Exports

open LeanQbe.T

@[expose] def flat0 : TFlatFn := {
  name := "full_update_classify_fid",
  as := [i64],
  rs := [],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 504), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .imm (BitVec.ofNat 64 488), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .var 0, ())⟩ <|
    TFlat.group (sig := [[.bool]])
      (TBlocks.cons (ts := [.bool])
        (TFlat.group (sig := [[i64]])
          (TBlocks.cons (ts := [i64])
            (TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.ret ()) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 8, .imm (BitVec.ofNat 64 2304), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 0), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .var 0, ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 5563713847938078769), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := []) 0 ()) <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64,
            (.imm (BitVec.ofNat 64 28), .imm (BitVec.ofNat 64 8), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 6, .var 0, ())⟩ <|
            TFlat.store (t := i64) (.var 8) (.var 0) <|
            TFlat.jump (ts := []) 0 ()) <|
            TBlocks.nil) <|
            TFlat.jnz (.var 1)
            (TFlat.let_ (ts := [i64]) ⟨.or i64, (.var 0, .imm (BitVec.ofNat 64 2), ())⟩ <|
            TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
            TFlat.let_ (ts := [i64]) ⟨.not i64, (.imm (BitVec.ofNat 64 2), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.and i64, (.var 1, .var 0, ())⟩ <|
            TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
          TBlocks.nil) <|
        TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 6, .imm (BitVec.ofNat 64 2304), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 0), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .var 0, ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
          (.var 0, .imm (BitVec.ofNat 64 5563713847938078769), ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 0), ())) <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64,
          (.imm (BitVec.ofNat 64 28), .imm (BitVec.ofNat 64 8), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 6, .var 0, ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 100000), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 6, .imm (BitVec.ofNat 64 504), ())⟩ <|
      TFlat.load i64 (.var 0) <|
      TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 100000), ())⟩ <|
      TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 4, .imm (BitVec.ofNat 64 990), ())⟩ <|
      TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl, (.var 1, .var 0, ())⟩ <|
      TFlat.jnz (.var 0)
        (TFlat.jump (ts := [.bool]) 0 (.imm true, ())) <|
      TFlat.jump (ts := [.bool]) 0 (.imm false, ())) <|
    TFlat.jump (ts := [.bool]) 0 (.imm false, ()) }

@[expose] def fns : List Fn := [flat0.toFn]

end LeanQbe.T.Examples.Kissat.Build.Inl.Internal.Exports
