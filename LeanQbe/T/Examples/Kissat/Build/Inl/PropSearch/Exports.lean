module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports

open LeanQbe.T

@[expose] def flat0 : TFlatFn := {
  name := "full_propagate",
  as := [i64],
  rs := [i64],
  body :=
    TFlat.call "full_propagate_ignore_hot" (as := [i64, i64]) [i64]
      (.var 0, .imm (BitVec.ofNat 64 4294967295), ()) <|
    TFlat.ret (.var 0, ()) }

@[expose] def flat1 : TFlatFn := {
  name := "full_flush_trail",
  as := [i64],
  rs := [i64],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 1024), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm (BitVec.ofNat 64 20), ())) <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 3, .imm (BitVec.ofNat 64 760), ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
          (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.ret (.imm (BitVec.ofNat 64 0), ())) <|
        TFlat.group (sig := [[]])
          (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 6, .imm (BitVec.ofNat 64 512), ())⟩ <|
            TFlat.store (t := i64) (.imm (BitVec.ofNat 64 0)) (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .imm (BitVec.ofNat 64 176), ())⟩ <|
            TFlat.store (t := i64) (.imm (BitVec.ofNat 64 4294967295)) (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 8, .imm (BitVec.ofNat 64 528), ())⟩ <|
            TFlat.store (t := i64) (.imm (BitVec.ofNat 64 0)) (.var 0) <|
            TFlat.ret (.imm (BitVec.ofNat 64 1), ())) <|
          TBlocks.nil) <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 6, .imm (BitVec.ofNat 64 152), ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 8, .imm (BitVec.ofNat 64 144), ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 13, .imm (BitVec.ofNat 64 1024), ())⟩ <|
            TFlat.store (t := i64) (.imm (BitVec.ofNat 64 1)) (.var 0) <|
            TFlat.ret (.imm (BitVec.ofNat 64 20), ())) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
            (.var 1, .imm (BitVec.ofNat 64 0), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.ret (.imm (BitVec.ofNat 64 0), ())) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 14, .imm (BitVec.ofNat 64 760), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.ret (.imm (BitVec.ofNat 64 0), ())) <|
            TFlat.jump (ts := []) 1 ()) <|
            TBlocks.nil) <|
          TFlat.call "full_propagate_ignore_hot" (as := [i64, i64]) [i64]
            (.var 11, .imm (BitVec.ofNat 64 4294967295), ()) <|
          TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
        TFlat.jump (ts := []) 0 ()) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 3, .imm (BitVec.ofNat 64 160), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.call "full_backtrack" (as := [i64, i64]) []
        (.var 6, .imm (BitVec.ofNat 64 0), ()) <|
      TFlat.jump (ts := []) 0 ()) <|
    TFlat.jump (ts := []) 0 () }

@[expose] def fns : List Fn := [flat0.toFn, flat1.toFn]

end LeanQbe.T.Examples.Kissat.Build.Inl.PropSearch.Exports
