module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Inl.Analyze.Exports

open LeanQbe.T

@[expose] def flat0 : TFlatFn := {
  name := "full_analyze_m6_hdr",
  as := [i64],
  rs := [i64],
  body :=
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 0, .imm (BitVec.ofNat 64 160), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.ret (.imm (BitVec.ofNat 64 20), ())) <|
    TFlat.group (sig := [[]])
      (TBlocks.cons (ts := [])
        (TFlat.call "full_analyze_core_m6" (as := [i64]) [i64] (.var 3, ()) <|
        TFlat.ret (.var 0, ())) <|
      TBlocks.nil) <|
    TFlat.let_ (ts := [i64]) ⟨.add i64, (.var 3, .imm (BitVec.ofNat 64 520), ())⟩ <|
    TFlat.load i64 (.var 0) <|
    TFlat.let_ (ts := [.bool]) ⟨.cmp .eq i64 .bool rfl,
      (.var 0, .imm (BitVec.ofNat 64 0), ())⟩ <|
    TFlat.jnz (.var 0)
      (TFlat.call "m6_hdr_dr_update" (as := [i64]) [] (.var 6, ()) <|
      TFlat.jump (ts := []) 0 ()) <|
    TFlat.jump (ts := []) 0 () }

@[expose] def fns : List Fn := [flat0.toFn]

end LeanQbe.T.Examples.Kissat.Build.Inl.Analyze.Exports
