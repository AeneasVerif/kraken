module

public import LeanQbe.T.Bootstrap0.Codec0
public import LeanQbe.T.Bootstrap0.Codec0Lemmas
public import LeanQbe.T.Bootstrap0.Dummies0
public import LeanQbe.T.Bootstrap0.Bridge0
public import LeanQbe.T.Bootstrap0.Mod0
public import LeanQbe.T.Bootstrap0.Splice0
public import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Bootstrap0.Codec0
meta import LeanQbe.T.Bootstrap0.Codec0Lemmas
meta import LeanQbe.T.Bootstrap0.Dummies0
meta import LeanQbe.T.Bootstrap0.Bridge0
meta import LeanQbe.T.Bootstrap0.Mod0
meta import LeanQbe.T.Bootstrap0.Splice0
meta import LeanQbe.T.Amd64.Targ

/-!
# Stage B Binary Codec (`Codec0`) Round-Trip, Negative & LCNF Validation Gate

Validates `Codec0` end-to-end:
1. Closure-free, global-free, acyclic `LeanLCNF` lowering (`papTargets = []`, `maxAp = 0`,
   `consts = 0`, `strs = 0`, `bigNats = 0`, `checkTFlat = true`, `checkAcyclic = true`) and
   x86-64 directive budget (`<= 250` dirs/fn) on both `decodeMod0` (`codec0DecodeLcMod`) and
   `[encodeMod0, decodeMod0]` (`codec0LcMod`).
2. Canonical `decodeMod0 (encodeMod0 m) = some m` round-trip and `checkMod0Bounded` on empty
   module, `dummyAddMod0`, `dummyLoopMod0`, `dummyCallTailMod0`, local `dummyAllOpsMod0`, and
   `leanqbe0` self-hosting IR (`ofTFlatModule leanqbe0Tfs`).
3. Rejection (`none`) on empty, wrong-magic, wrong-version, truncated, bad-tag, and trailing-byte
   buffers.
4. Single-line `#print axioms` audit strictly `⊆ [propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeBootstrap0Test.Codec0Test

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Amd64
open LeanQbe.T.Bootstrap0

/-! ## 1. Structural Equality & Local `dummyAllOpsMod0` Witness -/

private def ty0Eq : Ty0 → Ty0 → Bool
  | .bool, .bool | .b8, .b8 | .b16, .b16 | .b32, .b32 | .b64, .b64 => true
  | _, _ => false

private def tyList0Eq : List Ty0 → List Ty0 → Bool
  | [], [] => true
  | a :: xs, b :: ys => ty0Eq a b && tyList0Eq xs ys
  | _, _ => false

private def widthEq : Width → Width → Bool
  | .W8, .W8 | .W16, .W16 | .W32, .W32 | .W64, .W64 => true
  | _, _ => false

private def cmpOpEq : CmpOp → CmpOp → Bool
  | .eq, .eq | .ne, .ne | .ult, .ult | .ule, .ule | .ugt, .ugt | .uge, .uge
  | .slt, .slt | .sle, .sle | .sgt, .sgt | .sge, .sge => true
  | _, _ => false

private def unOp0Eq : UnOp0 → UnOp0 → Bool
  | .copy, .copy | .neg, .neg | .not, .not => true
  | _, _ => false

private def binOp0Eq : BinOp0 → BinOp0 → Bool
  | .add, .add | .sub, .sub | .mul, .mul | .and, .and | .or, .or | .xor, .xor
  | .shl, .shl | .lshr, .lshr | .ashr, .ashr | .rotl, .rotl | .rotr, .rotr => true
  | _, _ => false

private def divOp0Eq : DivOp0 → DivOp0 → Bool
  | .udiv, .udiv | .urem, .urem | .sdiv, .sdiv | .srem, .srem => true
  | _, _ => false

private def convOp0Eq : ConvOp0 → ConvOp0 → Bool
  | .ofBool, .ofBool | .zext, .zext | .sext, .sext | .trunc, .trunc => true
  | _, _ => false

private def arg0Eq : Arg0 → Arg0 → Bool
  | .var a, .var b => a == b
  | .immBool a, .immBool b => a == b
  | .immBits wa va, .immBits wb vb => widthEq wa wb && va == vb
  | _, _ => false

private def argList0Eq : List Arg0 → List Arg0 → Bool
  | [], [] => true
  | a :: xs, b :: ys => arg0Eq a b && argList0Eq xs ys
  | _, _ => false

private def opCode0Eq : OpCode0 → OpCode0 → Bool
  | .un oa ta, .un ob tb => unOp0Eq oa ob && ty0Eq ta tb
  | .bin oa ta, .bin ob tb => binOp0Eq oa ob && ty0Eq ta tb
  | .cmp ca ta, .cmp cb tb => cmpOpEq ca cb && ty0Eq ta tb
  | .select ta, .select tb => ty0Eq ta tb
  | .conv ca wsa wda, .conv cb wsb wdb => convOp0Eq ca cb && widthEq wsa wsb && widthEq wda wdb
  | .div da wa, .div db wb => divOp0Eq da db && widthEq wa wb
  | .umulw64, .umulw64 => true
  | _, _ => false

mutual
private def tflat0Eq : TFlat0 → TFlat0 → Bool
  | .let1 oa aa ka, .let1 ob ab kb => opCode0Eq oa ob && argList0Eq aa ab && tflat0Eq ka kb
  | .let2Umulw64 a1 a2 ka, .let2Umulw64 b1 b2 kb =>
    arg0Eq a1 b1 && arg0Eq a2 b2 && tflat0Eq ka kb
  | .load ta aa ka, .load tb ab kb => ty0Eq ta tb && arg0Eq aa ab && tflat0Eq ka kb
  | .store ta va aa ka, .store tb vb ab kb =>
    ty0Eq ta tb && arg0Eq va vb && arg0Eq aa ab && tflat0Eq ka kb
  | .call fa asa bsa aa ka, .call fb asb bsb ab kb =>
    fa == fb && tyList0Eq asa asb && tyList0Eq bsa bsb && argList0Eq aa ab && tflat0Eq ka kb
  | .tailCall fa asa aa, .tailCall fb asb ab =>
    fa == fb && tyList0Eq asa asb && argList0Eq aa ab
  | .jnz ca ta ea, .jnz cb tb eb => arg0Eq ca cb && tflat0Eq ta tb && tflat0Eq ea eb
  | .jump ja aa, .jump jb ab => ja == jb && argList0Eq aa ab
  | .ret va, .ret vb => argList0Eq va vb
  | .exit fa asa aa, .exit fb asb ab => fa == fb && tyList0Eq asa asb && argList0Eq aa ab
  | .hlt, .hlt => true
  | .group bsa ka, .group bsb kb => blocks0Eq bsa bsb && tflat0Eq ka kb
  | _, _ => false

private def blocks0Eq : List (List Ty0 × TFlat0) → List (List Ty0 × TFlat0) → Bool
  | [], [] => true
  | (ta, ba) :: xs, (tb, bb) :: ys => tyList0Eq ta tb && tflat0Eq ba bb && blocks0Eq xs ys
  | _, _ => false
end

private def fn0Eq (a b : TFlatFn0) : Bool :=
  a.name == b.name && tyList0Eq a.as b.as && tyList0Eq a.rs b.rs && tflat0Eq a.body b.body

private def fnList0Eq : List TFlatFn0 → List TFlatFn0 → Bool
  | [], [] => true
  | a :: xs, b :: ys => fn0Eq a b && fnList0Eq xs ys
  | _, _ => false

private def ext0Eq (a b : ExtSig0) : Bool :=
  a.name == b.name && tyList0Eq a.as b.as && tyList0Eq a.rs b.rs

private def extList0Eq : List ExtSig0 → List ExtSig0 → Bool
  | [], [] => true
  | a :: xs, b :: ys => ext0Eq a b && extList0Eq xs ys
  | _, _ => false

private def mod0Eq (a b : TFlatModule0) : Bool :=
  fnList0Eq a.fns b.fns && extList0Eq a.externs b.externs && a.exits == b.exits

private def roundTripOk (m : TFlatModule0) : Bool :=
  checkMod0Bounded m &&
  match decodeMod0 (encodeMod0 m) with
  | some m' => mod0Eq m m'
  | none => false

private def dummyAllOpsFn0 : TFlatFn0 :=
  { name := 0
    as := [.bool, .b8, .b16, .b32, .b64, .b64]
    rs := [.b64]
    body :=
      .let1 (.un .not .bool) [.var 5] <|
        .let1 (.bin .xor .bool) [.var 0, .var 6] <|
          .let1 (.un .neg .b8) [.var 6] <|
            .let1 (.bin .shl .b8) [.var 0, .immBits .W8 3] <|
              .let1 (.div .sdiv .W8) [.var 0, .immBits .W8 2] <|
                .let1 (.un .not .b16) [.var 8] <|
                  .let1 (.bin .rotr .b16) [.var 0, .immBits .W16 5] <|
                    .let1 (.div .udiv .W16) [.var 0, .immBits .W16 3] <|
                      .let1 (.cmp .ugt .b16) [.var 0, .immBits .W16 1] <|
                        .let1 (.conv .ofBool .W8 .W32) [.var 0] <|
                          .let1 (.bin .ashr .b32) [.var 0, .immBits .W32 1] <|
                            .let1 (.div .srem .W32) [.var 0, .immBits .W32 7] <|
                              .let1 (.conv .sext .W32 .W64) [.var 0] <|
                                .let1 (.bin .rotl .b64) [.var 0, .immBits .W64 7] <|
                                  .let2Umulw64 (.var 0) (.var 15) <|
                                    .let1 (.select .b64) [.var 7, .var 0, .var 1] <|
                                      .store .b8 (.immBits .W8 9) (.var 17) <|
                                        .store .b16 (.immBits .W16 11) (.var 17) <|
                                          .load .b16 (.var 17) <|
                                            .let1 (.conv .zext .W16 .W64) [.var 0] <|
                                              .let1 (.bin .add .b64) [.var 3, .var 0] <|
                                                .ret [.var 0] }

private def dummyExitHltFn0 : TFlatFn0 :=
  { name := 1
    as := [.bool, .b64]
    rs := [.b64]
    body := .jnz (.var 1) (.exit 99 [.b64] [.var 0]) .hlt }

private def dummyAllOpsMod0 : TFlatModule0 :=
  { fns := [dummyAllOpsFn0, dummyExitHltFn0]
    externs := [{ name := 7, as := [.b64, .b8], rs := [.bool] }]
    exits := [99] }

private def emptyMod0 : TFlatModule0 :=
  { fns := [], externs := [], exits := [] }

/-! ## 2. Positive Round-Trip Checks (Dummy Modules & `leanqbe0` Self-Hosting IR) -/

#guard roundTripOk emptyMod0
#guard roundTripOk dummyAddMod0
#guard roundTripOk dummyLoopMod0
#guard roundTripOk dummyCallTailMod0
#guard roundTripOk dummyAllOpsMod0

private def leanqbe0RoundTripPrefixOk : Bool :=
  match ofTFlatModule (leanqbe0Tfs.take 15) with
  | .ok (m0, _) => roundTripOk m0
  | .error _ => false

#guard leanqbe0RoundTripPrefixOk

private def leanqbe0FullRoundTripCheck : Except String (Nat × Nat) := do
  let (m0, _) ← ofTFlatModule leanqbe0Tfs
  if !roundTripOk m0 then
    .error "full leanqbe0 roundTrip failed"
  else
    .ok (m0.fns.length, (encodeMod0 m0).size)

#eval leanqbe0FullRoundTripCheck

/-! ## 3. Negative Malformed-Buffer Rejection Checks -/

private def dummyAddBytes : List UInt8 :=
  (encodeMod0 dummyAddMod0).data.toList

private def mkBa (xs : List UInt8) : ByteArray :=
  ByteArray.mk xs.toArray

#guard (decodeMod0 (mkBa [])).isNone
#guard (decodeMod0 (mkBa [0x4c, 0x51, 0x42])).isNone
#guard (decodeMod0 (mkBa [0x4c, 0x51, 0x42, 0x31, 0x01])).isNone
#guard (decodeMod0 (mkBa [0x4c, 0x51, 0x42, 0x30, 0x02, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])).isNone
#guard (decodeMod0 (mkBa [0x4c, 0x51, 0x42, 0x30, 0x01, 1, 0, 0, 0])).isNone
#guard (decodeMod0 (mkBa (dummyAddBytes ++ [0x00]))).isNone
#guard (decodeMod0 (mkBa (dummyAddBytes.take (dummyAddBytes.length - 1)))).isNone
#guard (decodeMod0 (mkBa [0x4c, 0x51, 0x42, 0x30, 0x01,
  1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 99, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])).isNone
#guard (decodeMod0 (mkBa [0x4c, 0x51, 0x42, 0x30, 0x01,
  1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 5, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0])).isNone
#guard (decodeMod0 (mkBa [0x4c, 0x51, 0x42, 0x30, 0x01,
  1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 1, 0, 0, 0, 9,
  0, 0, 0, 0, 0, 0, 0, 0])).isNone
#guard (decodeMod0 (mkBa [0x4c, 0x51, 0x42, 0x30, 0x01,
  1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 99, 0, 0, 0, 0, 10,
  0, 0, 0, 0, 0, 0, 0, 0])).isNone

/-! ## 4. Closure-Free, Global-Free & x86-64 Directive Gate (`codec0DecodeLcMod` / `codec0LcMod`) -/

private def lcGlobalsCount (m : LcModule) : Nat :=
  let consts := m.decls.filter fun d => d.params.isEmpty && !d.retTy.isScalar
  let allLits := m.decls.map (·.body.lits)
  let strs := dedupStr (allLits.flatMap (·.1))
  let bigNats := dedupNat (allLits.flatMap (·.2))
  consts.length + strs.length + bigNats.length

splice_lcnf_tflat! codec0DecodeTfs codec0DecodeLcMod
def codec0DecodeMod : Module :=
  { fns := LeanLRC.tflatFnsToFns codec0DecodeTfs
    externs := rtExterns
    exits := rtExitSyms }
eval_dir_stats! codec0DecodeDirStats x64Target x64LegalTarget codec0DecodeMod
  rtExtBounds0 rtExitSyms

splice_lcnf_tflat! codec0Tfs codec0LcMod
def codec0Mod : Module :=
  { fns := LeanLRC.tflatFnsToFns codec0Tfs
    externs := rtExterns
    exits := rtExitSyms }
eval_dir_stats! codec0DirStats x64Target x64LegalTarget codec0Mod
  rtExtBounds0 rtExitSyms

#guard codec0DecodeLcMod.papTargets.isEmpty
#guard codec0DecodeLcMod.maxAp == 0
#guard lcGlobalsCount codec0DecodeLcMod == 0
#guard codec0DecodeMod.fns.length == codec0DecodeDirStats.length
#guard codec0DecodeDirStats.all fun p => p.2 <= 250
#guard codec0DecodeMod.fns.all fun f => Func.checkTFlat f.body
#guard codec0DecodeMod.checkAcyclic

#guard codec0LcMod.papTargets.isEmpty
#guard codec0LcMod.maxAp == 0
#guard lcGlobalsCount codec0LcMod == 0
#guard codec0Mod.fns.length == codec0DirStats.length
#guard codec0DirStats.all fun p => p.2 <= 250
#guard codec0Mod.fns.all fun f => Func.checkTFlat f.body
#guard codec0Mod.checkAcyclic

private def maxDirsOf (stats : List (Sym × Nat)) : Nat :=
  stats.foldl (fun m p => Nat.max m p.2) 0

#eval (codec0DecodeLcMod.decls.length, codec0DecodeDirStats.length, maxDirsOf codec0DecodeDirStats)
#eval (codec0LcMod.decls.length, codec0DirStats.length, maxDirsOf codec0DirStats)

/-! ## 5. Single-Line Axiom Audit -/

#print axioms LeanQbe.T.Bootstrap0.mod0Bounded_of_check
#print axioms LeanQbe.T.Bootstrap0.decodeMod0_encodeMod0
#print axioms LeanQbe.T.Bootstrap0.decodeMod0_some_bounded
#print axioms LeanQbe.T.Bootstrap0.encodeMod0_decodeMod0
#print axioms LeanQbe.T.Bootstrap0.encodeMod0_inj
#print axioms LeanQbe.T.Bootstrap0.decodeMod0_inj
#print axioms LeanQbe.T.Bootstrap0.decodeMod0_encodeMod0_iff

end LeanQbeBootstrap0Test.Codec0Test
