module

public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Arm64.IselLemmas4
public import LeanQbe.T.Arm64.LratBytes
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.Examples.Kissat.FullM4Bcp
public import LeanQbe.T.Spill
meta import LeanQbe.T.Arm64.Isel
meta import LeanQbe.T.Arm64.TargLemmas
meta import LeanQbe.T.Arm64.LratBytes
meta import LeanQbe.T.Examples.LratBytes
meta import LeanQbe.T.Examples.Kissat.FullM4Bcp
meta import LeanQbe.T.Spill

/-!
# AArch64 `A1` + `A4` Codegen & `zeroExtLoad` Regression Tests

Verifies levers `A1` and `A4` through `armTarget` and `Rega.lowerFn`:
1. `A4` constant materialization: 1-insn `MOVN` for `-1`, 1-insn `ORR` bitmask (`0xFFFFFFFF`,
   etc.), literal-pool `LDR` preserved for non-bitmask 4-chunk constants, negative `ADD`/`SUB`
   immediate sign flip, and `CMN` (`ADDS_e`) for negative compare immediates.
2. `A1` sub-word comparisons, zero-extension elision, and `0 - x` (`NEG`):
   - `armCmpOpIns` `.imm` handling at `n ∈ {8, 16}` without `mov x17` or dual `sxtb`/`uxtb`;
   - `armGpr.zeroExtLoad = true` eliminating `ubfm #0, #7` / `#15` after `ldrb` / `ldrh`;
   - `0 - x` emitting `sub w/x, wzr/xzr, w/x` without `mov #0`.
3. End-to-end checks on `FullM4Bcp` (`m4Bcp_fns`), `Arm64.LratBytes.lratCert.code`, and `std3`
   `#print axioms`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.Arm64IselB5Test

open LeanQbe.T LeanQbe.T.Arm64

/-! ## Helpers -/

meta def hintsOf (fs : List Fn) : List armTarget.toIsa.Hints :=
  fs.map (Fn.computeHints armTarget.toIsa armLegalTarget)

meta def chk (fs : List Fn) (exs : List (SigEntry × Nat) := []) : Bool :=
  checkCompile armTarget armLayout armLegalTarget exs [] 0 fs (hintsOf fs) 2048

meta def codeOf (fs : List Fn) (exs : List (SigEntry × Nat) := []) : List Directive :=
  extractCode (compileModule armTarget.toIsa armLegalTarget armTarget.frame.raBytes exs [] 0 fs
    (hintsOf fs))

meta def countDirs (p : Directive → Bool) (ds : List Directive) : Nat :=
  (ds.filter p).length

meta def isMovnDir : Directive → Bool
  | .instr { operation := .MOVN .., .. } => true
  | _ => false

meta def isMovz0Dir : Directive → Bool
  | .instr { operation := .MOVZ _ (.int64 0) _, .. } => true
  | _ => false

meta def isMovzDir : Directive → Bool
  | .instr { operation := .MOVZ .., .. } => true
  | _ => false

meta def isMovkDir : Directive → Bool
  | .instr { operation := .MOVK .., .. } => true
  | _ => false

meta def isLdrPoolDir : Directive → Bool
  | .instr { operation := .LDR _ (.lit (.pool _)), .. } => true
  | _ => false

meta def isOrrImmDir : Directive → Bool
  | .instr { operation := .ORR_i .., .. } => true
  | _ => false

meta def isSubZrDir : Directive → Bool
  | .instr { operation := .SUB_s _ (.low .XZR _) _, .. } => true
  | _ => false

meta def isAddImmDir : Directive → Bool
  | .instr { operation := .ADD_e .., .. } => true
  | _ => false

meta def isSubImmDir : Directive → Bool
  | .instr { operation := .SUB_e .., .. } => true
  | _ => false

meta def isAddsImmDir : Directive → Bool
  | .instr { operation := .ADDS_e .., .. } => true
  | _ => false

meta def isSubsImmDir : Directive → Bool
  | .instr { operation := .SUBS_e .., .. } => true
  | _ => false

meta def isUbfmZext8Dir : Directive → Bool
  | .instr { operation := .UBFM _ _ 0 7, .. } => true
  | _ => false

meta def isUbfmZext16Dir : Directive → Bool
  | .instr { operation := .UBFM _ _ 0 15, .. } => true
  | _ => false

meta def isExt32Dir : Directive → Bool
  | .instr { operation := .UBFM _ _ 0 7, .. }
  | .instr { operation := .SBFM _ _ 0 7, .. }
  | .instr { operation := .UBFM _ _ 0 15, .. }
  | .instr { operation := .SBFM _ _ 0 15, .. } => true
  | _ => false

/-! ## 1. `A4` constant materialization, `ADD`/`SUB` flip, and `CMN` -/

theorem armGpr_zeroExtLoad_rfl : armGpr.zeroExtLoad = true := rfl

theorem armMovImm_neg1_rfl :
    armMovImmI .X0 (~~~0#64) = [armMovnI .X0 0 .LSL0] := rfl

theorem armMovImm_u32max_rfl :
    armMovImmI .X0 0x0000_0000_FFFF_FFFF#64 =
      [armIselInsI
        (.ORR_i (.low (.reg .X0) .W64) (xzr .W64) (.int64 (Int64.ofBitVec 0xFFFFFFFF#64)))] :=
  rfl

#guard (armMovImmI .X0 0xFFFF_FFFF_0000_0000#64).all fun i => isOrrImmDir (.instr i)
#guard (armMovImmI .X0 0x0F0F_0F0F_0F0F_0F0F#64).all fun i => isOrrImmDir (.instr i)
#guard (armMovImmI .X0 0x5555_5555_5555_5555#64).all fun i => isOrrImmDir (.instr i)
#guard (armMovImmI .X0 0x0000_0000_FFFF_FFFF#64).length == 1
#guard (armMovImmI .X0 0xFFFF_FFFF_0000_0000#64).length == 1
#guard (armMovImmI .X0 0x0F0F_0F0F_0F0F_0F0F#64).length == 1
#guard (armMovImmI .X0 0x5555_5555_5555_5555#64).length == 1
#guard (armMovImmI .X0 0x1234_5678_9ABC_DEF0#64).all fun i => isLdrPoolDir (.instr i)

#guard match armGpr.op (.add i64) (.gpr (.reg .X1), .imm (-42#64), ())
    (.gpr (.reg .X0), ()) .default with
  | some ([d], _) => isSubImmDir d
  | _ => false

#guard match armGpr.op (.sub i32) (.gpr (.reg .X1), .imm (-42#32), ())
    (.gpr (.reg .X0), ()) .default with
  | some ([d], _) => isAddImmDir d
  | _ => false

#guard match armGpr.op (.cmp .eq i64) (.gpr (.reg .X1), .imm (-1#64), ())
    (.flag .eq, ()) .default with
  | some ([d], _) => isAddsImmDir d
  | _ => false

#guard match armGpr.op (.cmp .slt i32) (.gpr (.reg .X1), .imm (-5#32), ())
    (.flag .lt, ()) .default with
  | some ([d], _) => isAddsImmDir d
  | _ => false

/-! ## 2. `A1` `armCmpOpIns` sub-word immediates and `0 - x` -/

#guard match armGpr.op (.cmp .eq i8) (.gpr (.reg .X1), .imm 32#8, ())
    (.flag .eq, ()) .default with
  | some ([d1, d2], _) => isExt32Dir d1 && isSubsImmDir d2
  | _ => false

#guard match armGpr.op (.cmp .slt i8) (.gpr (.reg .X1), .imm (-1#8), ())
    (.flag .lt, ()) .default with
  | some ([d1, d2], _) => isExt32Dir d1 && isAddsImmDir d2
  | _ => false

#guard match armGpr.op (.cmp .sgt i16) (.imm 10#16, .gpr (.reg .X1), ())
    (.flag .lt, ()) .default with
  | some ([d1, d2], _) => isExt32Dir d1 && isSubsImmDir d2
  | _ => false

#guard match armGpr.op (.sub i64) (.imm 0#64, .gpr (.reg .X1), ())
    (.gpr (.reg .X0), ()) .default with
  | some ([d], _) => isSubZrDir d
  | _ => false

#guard match armGpr.op (.sub i32) (.imm 0#32, .gpr (.reg .X1), ())
    (.gpr (.reg .X0), ()) .default with
  | some ([d], _) => isSubZrDir d
  | _ => false

/-! ## 3. End-to-end verified lowering regressions -/

/-- `full_prop_lit_raw.L5`-style byte load and signed compare `< 1` (`0` dual exts/movz). -/
meta def byteCmpSltFn : Fn :=
  ⟨"byteCmpSlt", [i64, i64, i64], [i64], fun _ _ (p, a, b, ()) =>
    .load i8 (.var p) fun v =>
    .let_ (op2 (.cmp .slt i8) (.var v) (.imm 1)) fun (c, ()) =>
    .jnz (.var c) (.ret (.var a, ())) (.ret (.var b, ()))⟩

/-- `LratBytes`-style `load i8` + `zext 8 64` + range check (`0` `ubfm #0, #7` when coalesced). -/
meta def lratByteWsFn : Fn :=
  ⟨"lratByteWs", [i64, i64, i64], [i64], fun _ _ (p, a, b, ()) =>
    .load i8 (.var p) fun v =>
    .let_ (op1 (.zext 8 64) (.var v)) fun (w, ()) =>
    .let_ (op2 (.sub i64) (.var w) (.imm 9)) fun (t, ()) =>
    .let_ (op2 (.cmp .ult i64) (.var t) (.imm 5)) fun (c, ()) =>
    .jnz (.var c) (.ret (.var a, ())) (.ret (.var b, ()))⟩

/-- Byte load + `cmp .eq i8 32` uses 1 ext + `subs #32` without `movz`. -/
meta def byteCmpEqFn : Fn :=
  ⟨"byteCmpEq", [i64, i64, i64], [i64], fun _ _ (p, a, b, ()) =>
    .load i8 (.var p) fun v =>
    .let_ (op2 (.cmp .eq i8) (.var v) (.imm 32)) fun (c, ()) =>
    .jnz (.var c) (.ret (.var a, ())) (.ret (.var b, ()))⟩

/-- `load i8` + `zext 8 64` emits zero `ubfm #0, #7`. -/
meta def zextLoad8Fn : Fn :=
  ⟨"zextLoad8", [i64], [i64], fun _ _ (p, ()) =>
    .load i8 (.var p) fun v =>
    .let_ (op1 (.zext 8 64) (.var v)) fun (y, ()) => .ret (.var y, ())⟩

/-- `load i16` + `zext 16 64` emits zero `ubfm #0, #15`. -/
meta def zextLoad16Fn : Fn :=
  ⟨"zextLoad16", [i64], [i64], fun _ _ (p, ()) =>
    .load i16 (.var p) fun v =>
    .let_ (op1 (.zext 16 64) (.var v)) fun (y, ()) => .ret (.var y, ())⟩

/-- Signed negative `i16` comparison (`< -5`) uses `sbfm #0,#15` + `adds wzr, w16, #5`. -/
meta def cmpNegImm16Fn : Fn :=
  ⟨"cmpNegImm16", [i64, i64, i64], [i64], fun _ _ (p, a, b, ()) =>
    .load i16 (.var p) fun v =>
    .let_ (op2 (.cmp .slt i16) (.var v) (.imm (-5))) fun (c, ()) =>
    .jnz (.var c) (.ret (.var a, ())) (.ret (.var b, ()))⟩

/-- `0 - x` emits `sub w/x, wzr/xzr` (`NEG`) without `movz #0`. -/
meta def negSub0Fn : Fn :=
  ⟨"negSub0", [i32, i64], [i32, i64], fun _ _ (a, b, ()) =>
    .let_ (op2 (.sub i32) (.imm 0) (.var a)) fun (na, ()) =>
    .let_ (op2 (.sub i64) (.imm 0) (.var b)) fun (nb, ()) =>
    .ret (.var na, .var nb, ())⟩

/-- Storing `-1#64` and `0xFFFFFFFF#64` uses `MOVN` + 1-insn `ORR`, zero `MOVK` / pool `LDR`. -/
meta def storeConstsFn : Fn :=
  ⟨"storeConsts", [i64], [i64], fun _ _ (p, ()) =>
    .store (t := i64) (.imm (-1)) (.var p) <|
    .let_ (op2 (.add i64) (.var p) (.imm 8)) fun (q, ()) =>
    .store (t := i64) (.imm 0xFFFFFFFF) (.var q) <|
    .ret (.imm 0, ())⟩

#guard chk [byteCmpSltFn]
#guard countDirs isMovzDir (codeOf [byteCmpSltFn]) == 0
#guard countDirs isExt32Dir (codeOf [byteCmpSltFn]) == 1

#guard chk [lratByteWsFn]
#guard countDirs isUbfmZext8Dir (codeOf [lratByteWsFn]) == 0
#guard countDirs isMovzDir (codeOf [lratByteWsFn]) == 0

#guard chk [byteCmpEqFn]
#guard countDirs isUbfmZext8Dir (codeOf [byteCmpEqFn]) == 1
#guard countDirs isMovzDir (codeOf [byteCmpEqFn]) == 0

#guard chk [zextLoad8Fn]
#guard countDirs isUbfmZext8Dir (codeOf [zextLoad8Fn]) == 0

#guard chk [zextLoad16Fn]
#guard countDirs isUbfmZext16Dir (codeOf [zextLoad16Fn]) == 0

#guard chk [cmpNegImm16Fn]
#guard countDirs isExt32Dir (codeOf [cmpNegImm16Fn]) == 1
#guard countDirs isAddsImmDir (codeOf [cmpNegImm16Fn]) == 1

#guard chk [negSub0Fn]
#guard countDirs isMovz0Dir (codeOf [negSub0Fn]) == 0
#guard countDirs isSubZrDir (codeOf [negSub0Fn]) == 2

#guard chk [storeConstsFn]
#guard countDirs isMovnDir (codeOf [storeConstsFn]) == 1
#guard countDirs isOrrImmDir (codeOf [storeConstsFn]) == 1
#guard countDirs isMovkDir (codeOf [storeConstsFn]) == 0
#guard countDirs isLdrPoolDir (codeOf [storeConstsFn]) == 0

/-! ## 4. `FullM4Bcp` (`m4Bcp_fns`) and `Arm64.LratBytes` codegen -/

meta def m4BcpEx : List (SigEntry × Nat) :=
  Examples.Kissat.FullM4Bcp.m4BcpExterns.map fun e => (⟨e.name, e.as, e.rs⟩, 0)

#guard chk Examples.Kissat.FullM4Bcp.m4Bcp_fns m4BcpEx
#guard countDirs isOrrImmDir (codeOf Examples.Kissat.FullM4Bcp.m4Bcp_fns m4BcpEx) ≥ 1
#guard countDirs isLdrPoolDir (codeOf Examples.Kissat.FullM4Bcp.m4Bcp_fns m4BcpEx) == 0

#guard chk Examples.LratBytes.lratBytesFns
#guard countDirs isOrrImmDir (codeOf Examples.LratBytes.lratBytesFns) ≥ 1
#guard countDirs isLdrPoolDir (codeOf Examples.LratBytes.lratBytesFns) == 0

theorem lratBytes_compiled_check :
    checkCompile armTarget armLayout armLegalTarget [] [] 0
      Examples.LratBytes.lratBytesFns Arm64.LratBytes.lratBytesHints 2048 = true :=
  Arm64.LratBytes.compiled_check

/-! ## 5. Axiom audit -/

#print axioms LeanQbe.T.Arm64.armGprSpec
#print axioms LeanQbe.T.Arm64.armLoad_zext
#print axioms LeanQbe.T.Arm64.armLoad_spec
#print axioms LeanQbe.T.Arm64.armMovImm_wp
#print axioms LeanQbe.T.Arm64.armOp_spec
#print axioms LeanQbe.T.Arm64.LratBytes.compiled_check
#print axioms LeanQbe.T.Arm64.LratBytes.lrat_check_bytes_arm64_correct

/-! ## 6. Flag-to-slot jump argument lowering (`jumpSlotMoves` `.flag cc` -> `.slot s`) -/

meta def adds {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (a : V i64) :
    Nat → (List (V i64) → Expr V L rs) → Expr V L rs
  | 0, body => body []
  | n + 1, body =>
    .let_ (op2 (.add i64) (.var a) (.imm (BitVec.ofNat 64 (n + 1)))) fun (x, ()) =>
      adds a n fun xs => body (x :: xs)

meta def mix {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    List (V i64) → V i64 → (V i64 → Expr V L rs) → Expr V L rs
  | [], acc, k => k acc
  | x :: xs, acc, k =>
    .let_ (op2 (.xor i64) (.var acc) (.var x)) fun (y, ()) =>
    .let_ (op2 (.add i64) (.var y) (.var x)) fun (z, ()) =>
    .let_ (op2 (.xor i64) (.var z) (.var x)) fun (w, ()) => mix xs w k

meta def heavyMix {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (xs : List (V i64)) (acc : V i64) : Nat → (V i64 → Expr V L rs) → Expr V L rs
  | 0, k => k acc
  | n + 1, k => mix xs acc fun acc' => heavyMix xs acc' n k

/-- A flag-homed boolean condition (`.flag cc`) passed as a `.jump` argument to a block whose
parameter `ploc` is `.slot s .w64`. -/
meta def flagJumpSlotArm64Fn : Fn :=
  ⟨"flagJumpSlotArm64B5", [i64, i64, i64], [i64], fun _ _ (a, b, q, ()) =>
    .group (sig := [[.bool]])
      (fun (_, ()) => .cons (fun (p, ()) =>
        adds b 14 fun hs => heavyMix hs b 2 fun z =>
        .call (as := [i64]) (bs := [i64]) "extFn" (.var z, ()) fun (u, ()) =>
        .jnz (.var p) (.ret (.var u, ())) (.ret (.imm 0, ()))) .nil)
      (fun (j, ()) =>
        .let_ (op2 (.cmp .eq i64) (.var a) (.imm 0)) fun (c0, ()) =>
        .jnz (.var c0)
          (.let_ (op2 (.cmp .ult i64) (.var b) (.var q)) fun (c, ()) =>
           .jump j (.var c, ()))
          (.store (t := i64) (.var a) (.var q)
            (.jump j (.imm false, ()))))⟩

#guard (compile armTarget.toIsa armLegalTarget [flagJumpSlotArm64Fn]
  [Fn.computeHints armTarget.toIsa armLegalTarget flagJumpSlotArm64Fn]).isOk = true

end LeanQbeTest.T.Arm64IselB5Test
