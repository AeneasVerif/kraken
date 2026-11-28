module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Tiers.Exports

open LeanQbe.T

@[expose] def flat0 : TFlatFn := {
  name := "m6_hdr_sync_legacy_tiers",
  as := [i64],
  rs := [],
  body :=
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 0, .imm (BitVec.ofNat 64 2304), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64,
          (.imm (BitVec.ofNat 64 8), .imm (BitVec.ofNat 64 8), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .var 0, ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [i64]) ⟨.add i64,
          (.imm (BitVec.ofNat 64 10), .imm (BitVec.ofNat 64 1), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .var 0, ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.group (sig := [[i64]])
          (TBlocks.cons (ts := [i64])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 9, .imm (BitVec.ofNat 64 696), ())⟩ <|
            TFlat.store (t := i64) (.var 6) (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 10, .imm (BitVec.ofNat 64 704), ())⟩ <|
            TFlat.store (t := i64) (.var 2) (.var 0) <|
            TFlat.ret ()) <|
          TBlocks.nil) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl, (.var 0, .var 4, ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.jump (ts := [i64]) 0 (.var 5, ())) <|
        TFlat.jump (ts := [i64]) 0 (.var 1, ())) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 0, .imm (BitVec.ofNat 64 2304), ())⟩ <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.jump (ts := []) 1 ()) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64,
      (.imm (BitVec.ofNat 64 0), .imm (BitVec.ofNat 64 8), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .var 0, ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 5563713847938078769), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.call "m6_hdr_init" (as := [i64]) [] (.var 5, ()) <|
      TFlat.jump (ts := []) 0 ()) <|
    TFlat.jump (ts := []) 0 () }

@[expose] def flat1 : TFlatFn := {
  name := "m6_hdr_recompute_tiers",
  as := [i64],
  rs := [],
  body :=
    TFlat.group (sig := [[i64]])
      (TBlocks.cons (ts := [i64])
        (TFlat.call "m6_hdr_recompute_tiers_mode" (as := [i64, i64]) [] (.var 1, .var 0, ()) <|
        TFlat.ret ()) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 552), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 1), ())) <|
    TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 0), ()) }

@[expose] def flat2 : TFlatFn := {
  name := "m6_hdr_update_tier_limits",
  as := [i64],
  rs := [],
  body :=
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 0, .imm (BitVec.ofNat 64 2304), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64,
          (.imm (BitVec.ofNat 64 12), .imm (BitVec.ofNat 64 8), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .var 0, ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.group (sig := [[]])
          (TBlocks.cons (ts := [])
            (TFlat.ret ()) <|
          TBlocks.nil) <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .imm (BitVec.ofNat 64 336), ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl, (.var 0, .var 2, ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.mul i64,
            (.imm (BitVec.ofNat 64 13), .imm (BitVec.ofNat 64 8), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .var 0, ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.let_ (ts := [i64]) ⟨.mul i64,
            (.imm (BitVec.ofNat 64 13), .imm (BitVec.ofNat 64 8), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 11, .var 0, ())⟩ <|
            TFlat.store (t := i64) (.var 2) (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64,
            (.imm (BitVec.ofNat 64 12), .imm (BitVec.ofNat 64 8), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 13, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 15, .imm (BitVec.ofNat 64 336), ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .var 6, ())⟩ <|
            TFlat.store (t := i64) (.var 0) (.var 3) <|
            TFlat.jump (ts := []) 2 ()) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 2), ())) <|
            TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.jump (ts := [i64]) 1 (.var 0, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl,
            (.var 1, .imm (BitVec.ofNat 64 65536), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 3, .var 0, ())⟩ <|
            TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
            TFlat.jump (ts := [i64]) 0 (.var 2, ())) <|
            TBlocks.nil) <|
          TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.call "m6_hdr_recompute_tiers_mode" (as := [i64, i64]) []
            (.var 8, .var 0, ()) <|
            TFlat.jump (ts := []) 1 ()) <|
            TBlocks.nil) <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .imm (BitVec.ofNat 64 552), ())⟩ <|
          TFlat.load i64 (.var 0) <|
          TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
          TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 1), ())) <|
          TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 0), ())) <|
        TFlat.jump (ts := []) 0 ()) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 0, .imm (BitVec.ofNat 64 2304), ())⟩ <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.jump (ts := []) 1 ()) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64,
      (.imm (BitVec.ofNat 64 0), .imm (BitVec.ofNat 64 8), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .var 0, ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 5563713847938078769), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.call "m6_hdr_init" (as := [i64]) [] (.var 5, ()) <|
      TFlat.jump (ts := []) 0 ()) <|
    TFlat.jump (ts := []) 0 () }

@[expose] def flat3 : TFlatFn := {
  name := "m6_hdr_record_used",
  as := [i64, i64],
  rs := [],
  body :=
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 1, .imm (BitVec.ofNat 64 2304), ())⟩ <|
        TFlat.group (sig := [[i64]])
          (TBlocks.cons (ts := [i64])
            (TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .var 1, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .var 0, ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.imm (BitVec.ofNat 64 14), .var 6, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 9, .var 0, ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.group (sig := [[]])
            (TBlocks.cons (ts := [])
            (TFlat.ret ()) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 18446744073709551615), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.imm (BitVec.ofNat 64 14), .var 11, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 14, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.store (t := i64) (.var 0) (.var 1) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.jump (ts := []) 0 ()) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 18446744073709551615), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 5, .var 6, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 10, .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 4, .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.store (t := i64) (.var 0) (.var 1) <|
            TFlat.jump (ts := []) 0 ()) <|
            TFlat.jump (ts := []) 0 ()) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 1, .imm (BitVec.ofNat 64 0), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 32), ())) <|
            TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 160), ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl,
            (.var 2, .imm (BitVec.ofNat 64 128), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.let_ (ts := [i64]) ⟨.sub i64,
            (.imm (BitVec.ofNat 64 128), .imm (BitVec.ofNat 64 1), ())⟩ <|
            TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
            TFlat.jump (ts := [i64]) 0 (.var 3, ())) <|
          TBlocks.nil) <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .imm (BitVec.ofNat 64 552), ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
          (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 1), ())) <|
        TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 0), ())) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 1, .imm (BitVec.ofNat 64 2304), ())⟩ <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.jump (ts := []) 1 ()) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64,
      (.imm (BitVec.ofNat 64 0), .imm (BitVec.ofNat 64 8), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .var 0, ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 5563713847938078769), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.call "m6_hdr_init" (as := [i64]) [] (.var 6, ()) <|
      TFlat.jump (ts := []) 0 ()) <|
    TFlat.jump (ts := []) 0 () }

@[expose] def flat4 : TFlatFn := {
  name := "m6_hdr_delaying",
  as := [i64, i64],
  rs := [.bool],
  body :=
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm false, ())) <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 2, .imm (BitVec.ofNat 64 2304), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.imm (BitVec.ofNat 64 16), .var 2, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .var 0, ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .ugt i64 .bool rfl,
          (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.let_ (ts := [i64]) ⟨.add i64, (.imm (BitVec.ofNat 64 16), .var 7, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .var 0, ())⟩ <|
          TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 4, .imm (BitVec.ofNat 64 1), ())⟩ <|
          TFlat.store (t := i64) (.var 0) (.var 1) <|
          TFlat.ret (.imm true, ())) <|
        TFlat.ret (.imm false, ())) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 2, .imm (BitVec.ofNat 64 2304), ())⟩ <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.jump (ts := []) 1 ()) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64,
      (.imm (BitVec.ofNat 64 0), .imm (BitVec.ofNat 64 8), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .var 0, ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 5563713847938078769), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.call "m6_hdr_init" (as := [i64]) [] (.var 7, ()) <|
      TFlat.jump (ts := []) 0 ()) <|
    TFlat.jump (ts := []) 0 () }

@[expose] def flat5 : TFlatFn := {
  name := "m6_hdr_bump_delay",
  as := [i64, i64],
  rs := [],
  body :=
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 2, .imm (BitVec.ofNat 64 2304), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.imm (BitVec.ofNat 64 20), .var 2, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .var 0, ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.group (sig := [[i64]])
          (TBlocks.cons (ts := [i64])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.imm (BitVec.ofNat 64 20), .var 7, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .var 0, ())⟩ <|
            TFlat.store (t := i64) (.var 3) (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.imm (BitVec.ofNat 64 16), .var 10, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 10, .var 0, ())⟩ <|
            TFlat.store (t := i64) (.var 6) (.var 0) <|
            TFlat.ret ()) <|
          TBlocks.nil) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl,
          (.var 0, .imm (BitVec.ofNat 64 4294967295), ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .imm (BitVec.ofNat 64 1), ())⟩ <|
          TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
        TFlat.jump (ts := [i64]) 0 (.var 1, ())) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 2, .imm (BitVec.ofNat 64 2304), ())⟩ <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.jump (ts := []) 1 ()) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64,
      (.imm (BitVec.ofNat 64 0), .imm (BitVec.ofNat 64 8), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .var 0, ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 5563713847938078769), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.call "m6_hdr_init" (as := [i64]) [] (.var 7, ()) <|
      TFlat.jump (ts := []) 0 ()) <|
    TFlat.jump (ts := []) 0 () }

@[expose] def flat6 : TFlatFn := {
  name := "m6_hdr_reduce_delay",
  as := [i64, i64],
  rs := [],
  body :=
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 4), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 2, .imm (BitVec.ofNat 64 2304), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.imm (BitVec.ofNat 64 20), .var 2, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .var 0, ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 1), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.lshr i64, (.var 1, .var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.imm (BitVec.ofNat 64 20), .var 8, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 8, .var 0, ())⟩ <|
        TFlat.store (t := i64) (.var 3) (.var 0) <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.imm (BitVec.ofNat 64 16), .var 11, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 11, .var 0, ())⟩ <|
        TFlat.store (t := i64) (.var 6) (.var 0) <|
        TFlat.ret ()) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 2, .imm (BitVec.ofNat 64 2304), ())⟩ <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.jump (ts := []) 1 ()) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64,
      (.imm (BitVec.ofNat 64 0), .imm (BitVec.ofNat 64 8), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .var 0, ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 5563713847938078769), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.call "m6_hdr_init" (as := [i64]) [] (.var 7, ()) <|
      TFlat.jump (ts := []) 0 ()) <|
    TFlat.jump (ts := []) 0 () }

@[expose] def flat7 : TFlatFn := {
  name := "m6_hdr_get_watermark",
  as := [i64, i64],
  rs := [i64],
  body :=
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm (BitVec.ofNat 64 0), ())) <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 2, .imm (BitVec.ofNat 64 2304), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.imm (BitVec.ofNat 64 24), .var 2, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .var 0, ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.ret (.var 0, ())) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 2, .imm (BitVec.ofNat 64 2304), ())⟩ <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.jump (ts := []) 1 ()) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64,
      (.imm (BitVec.ofNat 64 0), .imm (BitVec.ofNat 64 8), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .var 0, ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 5563713847938078769), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.call "m6_hdr_init" (as := [i64]) [] (.var 7, ()) <|
      TFlat.jump (ts := []) 0 ()) <|
    TFlat.jump (ts := []) 0 () }

@[expose] def flat8 : TFlatFn := {
  name := "m6_hdr_set_watermark",
  as := [i64, i64, i64],
  rs := [],
  body :=
    TFlat.let_ (ts := [.bool]) ⟨.cmp .uge i64 .bool rfl,
      (.var 1, .imm (BitVec.ofNat 64 8), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret ()) <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 3, .imm (BitVec.ofNat 64 2304), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.imm (BitVec.ofNat 64 24), .var 3, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 2, .var 0, ())⟩ <|
        TFlat.store (t := i64) (.var 5) (.var 0) <|
        TFlat.ret ()) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 3, .imm (BitVec.ofNat 64 2304), ())⟩ <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.jump (ts := []) 1 ()) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64,
      (.imm (BitVec.ofNat 64 0), .imm (BitVec.ofNat 64 8), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .var 0, ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 5563713847938078769), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.call "m6_hdr_init" (as := [i64]) [] (.var 8, ()) <|
      TFlat.jump (ts := []) 0 ()) <|
    TFlat.jump (ts := []) 0 () }

@[expose] def flat9 : TFlatFn := {
  name := "m6_hdr_dr_init",
  as := [i64],
  rs := [],
  body :=
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 0, .imm (BitVec.ofNat 64 2304), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64,
          (.imm (BitVec.ofNat 64 1), .imm (BitVec.ofNat 64 8), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .var 0, ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 63), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.lshr i64, (.var 1, .var 0, ())⟩ <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
          (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.ret ()) <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .imm (BitVec.ofNat 64 560), ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [i64]) ⟨.and i64, (.var 0, .imm (BitVec.ofNat 64 127), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64,
          (.imm (BitVec.ofNat 64 1), .imm (BitVec.ofNat 64 8), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 10, .var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 63), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.shl i64, (.imm (BitVec.ofNat 64 1), .var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 56), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.shl i64, (.var 5, .var 0, ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.or i64, (.var 2, .var 0, ())⟩ <|
        TFlat.store (t := i64) (.var 0) (.var 5) <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64,
          (.imm (BitVec.ofNat 64 2), .imm (BitVec.ofNat 64 8), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 17, .var 0, ())⟩ <|
        TFlat.store (t := i64) (.imm (BitVec.ofNat 64 0)) (.var 0) <|
        TFlat.let_ (ts := [i64]) ⟨.add i64,
          (.imm (BitVec.ofNat 64 2), .imm (BitVec.ofNat 64 1), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 20, .var 0, ())⟩ <|
        TFlat.store (t := i64) (.imm (BitVec.ofNat 64 0)) (.var 0) <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64,
          (.imm (BitVec.ofNat 64 4), .imm (BitVec.ofNat 64 8), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 22, .var 0, ())⟩ <|
        TFlat.store (t := i64) (.imm (BitVec.ofNat 64 0)) (.var 0) <|
        TFlat.let_ (ts := [i64]) ⟨.add i64,
          (.imm (BitVec.ofNat 64 4), .imm (BitVec.ofNat 64 1), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 25, .var 0, ())⟩ <|
        TFlat.store (t := i64) (.imm (BitVec.ofNat 64 0)) (.var 0) <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64,
          (.imm (BitVec.ofNat 64 6), .imm (BitVec.ofNat 64 8), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 27, .var 0, ())⟩ <|
        TFlat.store (t := i64) (.imm (BitVec.ofNat 64 4607182418800017408)) (.var 0) <|
        TFlat.let_ (ts := [i64]) ⟨.add i64,
          (.imm (BitVec.ofNat 64 6), .imm (BitVec.ofNat 64 1), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 30, .var 0, ())⟩ <|
        TFlat.store (t := i64) (.imm (BitVec.ofNat 64 4607182418800017408)) (.var 0) <|
        TFlat.ret ()) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 0, .imm (BitVec.ofNat 64 2304), ())⟩ <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.jump (ts := []) 1 ()) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64,
      (.imm (BitVec.ofNat 64 0), .imm (BitVec.ofNat 64 8), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .var 0, ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 5563713847938078769), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.call "m6_hdr_init" (as := [i64]) [] (.var 5, ()) <|
      TFlat.jump (ts := []) 0 ()) <|
    TFlat.jump (ts := []) 0 () }

@[expose] def flat10 : TFlatFn := {
  name := "m6_hdr_dr_allow",
  as := [i64],
  rs := [.bool],
  body :=
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 0, .imm (BitVec.ofNat 64 2304), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.mul i64,
          (.imm (BitVec.ofNat 64 1), .imm (BitVec.ofNat 64 8), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .var 0, ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [i64]) ⟨.sext 32 64, (.imm (BitVec.ofNat 32 63), ())⟩ <|
        TFlat.let_ (ts := [i64]) ⟨.lshr i64, (.var 1, .var 0, ())⟩ <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
          (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.ret (.imm true, ())) <|
        TFlat.group (sig := [[i64]])
          (TBlocks.cons (ts := [i64])
            (TFlat.let_ (ts := [i64]) ⟨.add i64, (.imm (BitVec.ofNat 64 4), .var 0, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 9, .var 0, ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.imm (BitVec.ofNat 64 6), .var 4, ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.mul i64, (.var 0, .imm (BitVec.ofNat 64 8), ())⟩ <|
            TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 13, .var 0, ())⟩ <|
            TFlat.load i64 (.var 0) <|
            TFlat.group (sig := [[i64]])
            (TBlocks.cons (ts := [i64])
            (TFlat.let_ (ts := [.bool]) ⟨.cmp .ult i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 4621819117588971520), ())⟩ <|
            TFlat.ret (.var 0, ())) <|
            TBlocks.nil) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.call "f64u_sub" (as := [i64, i64]) [i64]
            (.imm (BitVec.ofNat 64 4607182418800017408), .var 1, ()) <|
            TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
            (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
            TFlat.jnz (.var 0)
            (TFlat.ret (.imm true, ())) <|
            TFlat.call "f64u_div" (as := [i64, i64]) [i64] (.var 7, .var 1, ()) <|
            TFlat.jump (ts := [i64]) 0 (.var 0, ())) <|
            TFlat.jump (ts := [i64]) 0 (.var 5, ())) <|
          TBlocks.nil) <|
        TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 7, .imm (BitVec.ofNat 64 552), ())⟩ <|
        TFlat.load i64 (.var 0) <|
        TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
          (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
        TFlat.jnz (.var 0)
          (TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 1), ())) <|
        TFlat.jump (ts := [i64]) 0 (.imm (BitVec.ofNat 64 0), ())) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.sub i64, (.var 0, .imm (BitVec.ofNat 64 2304), ())⟩ <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.jump (ts := []) 1 ()) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.mul i64,
      (.imm (BitVec.ofNat 64 0), .imm (BitVec.ofNat 64 8), ())⟩ <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 1, .var 0, ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .ne i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 5563713847938078769), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.call "m6_hdr_init" (as := [i64]) [] (.var 5, ()) <|
      TFlat.jump (ts := []) 0 ()) <|
    TFlat.jump (ts := []) 0 () }

@[expose] def fns : List Fn := [flat0.toFn, flat1.toFn, flat2.toFn, flat3.toFn, flat4.toFn,
    flat5.toFn, flat6.toFn, flat7.toFn, flat8.toFn, flat9.toFn, flat10.toFn]

end LeanQbe.T.Examples.Kissat.Build.Inl.Tiers.Exports
