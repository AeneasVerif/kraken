module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Dense.Exports

open LeanQbe.T

@[expose] def flat0 : TFlatFn := {
  name := "full_dense_occ_cnt_fid",
  as := [i64, i32, i64],
  rs := [i64],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .imm (BitVec.ofNat 64 104), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 3, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 1, .var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .var 0, ())⟩ <|
    TFlat.load i32 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 10, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 1, .var 0, ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 12, .var 0, ())⟩ <|
    TFlat.load i32 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.zext 32 64, (.var 0, ())⟩ <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl, (.var 0, .var 17, ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.var 1, ())) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 20, .imm (BitVec.ofNat 64 120), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 11, .var 3, ())⟩ <|
    TFlat.group (sig := [[i64, i64]])
      (TBlocks.cons (ts := [i64, i64])
        (TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 1, .var 2, ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 2, .imm (BitVec.ofNat 64 4), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .var 0, ())⟩ <|
          TFlat.load i32 (.var 0) <|
          TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl, (.var 0, .var 29, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.ret (.var 1, ())) <|
            TFlat.jump (ts := [i64, i64]) 1 (.var 2, .var 1, ())) <|
            TBlocks.nil) <|
          TFlat.let_ (ts := [i32]) ⟨.and i32,
            (.var 0, .imm (BitVec.ofNat 32 2147483648), ())⟩ <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i32 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 32 0), ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .imm (BitVec.ofNat 64 2), ())⟩ <|
          TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
        TFlat.ret (.var 1, ())) <|
      TBlocks.nil) <|
    TFlat.jump (ts := [i64, i64]) 0 (.var 12, .imm (BitVec.ofNat 64 0), ()) }

@[expose] def flat1 : TFlatFn := {
  name := "full_enter_dense",
  as := [i64],
  rs := [.bool],
  body :=
    TFlat.call "full_enter_dense_ex_fid" (as := [i64, .bool]) [.bool] (.var 0, .imm true, ()) <|
    TFlat.ret (.var 0, ()) }

@[expose] def flat2 : TFlatFn := {
  name := "full_rebuild_watches",
  as := [i64],
  rs := [i64],
  body :=
    TFlat.call "full_rebuild_watches_nosort_fid" (as := [i64]) [i64] (.var 0, ()) <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.ret (.var 0, ())) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.group (sig := [[]])
        (TBlocks.cons (ts := [])
          (TFlat.jump (ts := []) 1 ()) <|
        TBlocks.nil) <|
      TFlat.jump (ts := []) 0 ()) <|
    TFlat.jump (ts := []) 0 () }

@[expose] def flat3 : TFlatFn := {
  name := "full_m6_dense_prop",
  as := [i64],
  rs := [.bool],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 96), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.group (sig := [[]])
          (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .imm (BitVec.ofNat 64 1024), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
            TFlat.ret (.var 0, ())) <|
          TBlocks.nil) <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .imm (BitVec.ofNat 64 152), ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .imm (BitVec.ofNat 64 144), ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .imm (BitVec.ofNat 64 1024), ())⟩ <|
          TFlat.load i64 (.var 0) <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 10, .imm (BitVec.ofNat 64 152), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 11, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 15, .imm (BitVec.ofNat 64 152), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 18, .imm (BitVec.ofNat 64 152), ())⟩ <|
            TFlat.store (t := i64) (.var 1) (.var 0) <|
            TFlat.call "full_m6_dense_prop_lit" (as := [i64, i32]) [.bool]
            (.var 19, .var 4, ()) <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := []) 1 ()) <|
            TFlat.ret (.imm false, ())) <|
          TFlat.jump (ts := []) 0 ()) <|
        TFlat.jump (ts := []) 0 ()) <|
      TBlocks.nil) <|
    TFlat.jump (ts := []) 0 () }

@[expose] def flat4 : TFlatFn := {
  name := "full_dense_flush_units_m7",
  as := [i64],
  rs := [.bool],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 96), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .imm (BitVec.ofNat 64 152), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.group (sig := [[i64]])
      (TBlocks.cons (ts := [i64])
        (TFlat.group (sig := [[]])
          (TBlocks.cons (ts := [])
            (TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 6, .imm (BitVec.ofNat 64 152), ())⟩ <|
            TFlat.store (t := i64) (.var 1) (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .imm (BitVec.ofNat 64 1024), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
            TFlat.ret (.var 0, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .imm (BitVec.ofNat 64 144), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ule i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i64]) 0 (.var 3, ())) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 8, .imm (BitVec.ofNat 64 144), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
          TBlocks.nil) <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .imm (BitVec.ofNat 64 144), ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 2, .var 0, ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 8, .imm (BitVec.ofNat 64 1024), ())⟩ <|
          TFlat.load i64 (.var 0) <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 6, .imm (BitVec.ofNat 64 4), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 10, .var 0, ())⟩ <|
            TFlat.load i32 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 9, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.call "full_dense_prop_unit_m7" (as := [i64, i32]) [.bool]
            (.var 15, .var 1, ()) <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i64]) 1 (.var 1, ())) <|
            TFlat.ret (.imm false, ())) <|
          TFlat.jump (ts := []) 0 ()) <|
        TFlat.jump (ts := []) 0 ()) <|
      TBlocks.nil) <|
    TFlat.jump (ts := [i64]) 0 (.var 0, ()) }

@[expose] def fns : List Fn := [flat0.toFn, flat1.toFn, flat2.toFn, flat3.toFn, flat4.toFn]

end LeanQbe.T.Examples.Kissat.Build.Inl.Dense.Exports
