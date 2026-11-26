module

public import LeanQbe.T.Bootstrap0.Codec0
public import LeanQbe.T.Bootstrap0.Codec0Lemmas
public import LeanQbe.T.Bootstrap0.Dummies0
public import LeanQbe.T.Bootstrap0.Bridge0
public import LeanQbe.T.Bootstrap0.Mod0
public import LeanQbe.T.Bootstrap0.Splice0
public import LeanQbe.T.Amd64.Targ
public import LeanQbeBootstrap0Test.Bootstrap0CleanTest
meta import LeanQbe.T.Bootstrap0.Codec0
meta import LeanQbe.T.Bootstrap0.Codec0Lemmas
meta import LeanQbe.T.Bootstrap0.Dummies0
meta import LeanQbe.T.Bootstrap0.Bridge0
meta import LeanQbe.T.Bootstrap0.Mod0
meta import LeanQbe.T.Bootstrap0.Splice0
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbeBootstrap0Test.Bootstrap0CleanTest

/-!
# Stage B Binary Codec (`Codec0`) Round-Trip, Negative & LCNF Validation Gate

Validates `Codec0` end-to-end:
1. Closure-free, global-free, acyclic `LeanLCNF` lowering and x86-64 directive budget (`<= 250`
   dirs/fn) on `decodeMod0` (`codec0DecodeLcMod`) and `[encodeMod0, decodeMod0]` (`codec0LcMod`).
2. Canonical `decodeMod0 (encodeMod0 m) = some m` round-trip and `checkMod0Bounded` on dummy
   modules, `dummyAllOpsMod0`, and `leanqbe0` self-hosting IR (`ofTFlatModule leanqbe0Tfs`).
3. Rejection (`none`) on empty, wrong-magic, wrong-version, truncated, bad-tag, trailing buffers.
4. Single-line `#print axioms` audit strictly `⊆ [propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeBootstrap0Test.Codec0Test

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Amd64
open LeanQbe.T.Bootstrap0
open LeanQbe.T.Bootstrap0.Codec0
open LeanQbeBootstrap0Test.Bootstrap0CleanTest

/-! ## 1. Structural Equality & Round-Trip Harness -/

private def eqTyList (xs ys : List Ty0) : Bool := xs.isEqv ys (ty0Tag · == ty0Tag ·)

private def arg0Eq : Arg0 → Arg0 → Bool
  | .var a, .var b => a == b
  | .immBool a, .immBool b => a == b
  | .immBits wa va, .immBits wb vb => widthTag wa == widthTag wb && va == vb
  | _, _ => false

private def opCode0Eq : OpCode0 → OpCode0 → Bool
  | .un oa ta, .un ob tb => unOp0Tag oa == unOp0Tag ob && ty0Tag ta == ty0Tag tb
  | .bin oa ta, .bin ob tb => binOp0Tag oa == binOp0Tag ob && ty0Tag ta == ty0Tag tb
  | .cmp ca ta, .cmp cb tb =>
    Codec0.cmpOpTag ca == Codec0.cmpOpTag cb && ty0Tag ta == ty0Tag tb
  | .select ta, .select tb => ty0Tag ta == ty0Tag tb
  | .conv ca wsa wda, .conv cb wsb wdb =>
    convOp0Tag ca == convOp0Tag cb && widthTag wsa == widthTag wsb && widthTag wda == widthTag wdb
  | .div da wa, .div db wb => divOp0Tag da == divOp0Tag db && widthTag wa == widthTag wb
  | .umulw64, .umulw64 => true
  | _, _ => false

mutual
private def tflat0Eq : TFlat0 → TFlat0 → Bool
  | .let1 oa aa ka, .let1 ob ab kb => opCode0Eq oa ob && aa.isEqv ab arg0Eq && tflat0Eq ka kb
  | .let2Umulw64 a1 a2 ka, .let2Umulw64 b1 b2 kb => arg0Eq a1 b1 && arg0Eq a2 b2 && tflat0Eq ka kb
  | .load ta aa ka, .load tb ab kb => ty0Tag ta == ty0Tag tb && arg0Eq aa ab && tflat0Eq ka kb
  | .store ta va aa ka, .store tb vb ab kb =>
    ty0Tag ta == ty0Tag tb && arg0Eq va vb && arg0Eq aa ab && tflat0Eq ka kb
  | .call fa asa bsa aa ka, .call fb asb bsb ab kb =>
    fa == fb && eqTyList asa asb && eqTyList bsa bsb && aa.isEqv ab arg0Eq && tflat0Eq ka kb
  | .tailCall fa asa aa, .tailCall fb asb ab =>
    fa == fb && eqTyList asa asb && aa.isEqv ab arg0Eq
  | .jnz ca ta ea, .jnz cb tb eb => arg0Eq ca cb && tflat0Eq ta tb && tflat0Eq ea eb
  | .jump ja aa, .jump jb ab => ja == jb && aa.isEqv ab arg0Eq
  | .ret va, .ret vb => va.isEqv vb arg0Eq
  | .exit fa asa aa, .exit fb asb ab => fa == fb && eqTyList asa asb && aa.isEqv ab arg0Eq
  | .hlt, .hlt => true
  | .group bsa ka, .group bsb kb => blocks0Eq bsa bsb && tflat0Eq ka kb
  | _, _ => false

private def blocks0Eq : List (List Ty0 × TFlat0) → List (List Ty0 × TFlat0) → Bool
  | [], [] => true
  | (ta, ba) :: xs, (tb, bb) :: ys => eqTyList ta tb && tflat0Eq ba bb && blocks0Eq xs ys
  | _, _ => false
end

private def mod0Eq (a b : TFlatModule0) : Bool :=
  (a.fns.isEqv b.fns fun x y =>
    x.name == y.name && eqTyList x.as y.as && eqTyList x.rs y.rs && tflat0Eq x.body y.body) &&
  (a.externs.isEqv b.externs fun x y =>
    x.name == y.name && eqTyList x.as y.as && eqTyList x.rs y.rs) &&
  a.exits == b.exits

private def roundTripOk (m : TFlatModule0) : Bool :=
  checkMod0Bounded m &&
  match decodeMod0 (encodeMod0 m) with
  | some m' => mod0Eq m m'
  | none => false

private def dummyAllOpsExtMod0 : TFlatModule0 :=
  { dummyAllOpsMod0 with externs := [{ name := 7, as := [.b64, .b8], rs := [.bool] }] }

private def emptyMod0 : TFlatModule0 := { fns := [], externs := [], exits := [] }

/-! ## 2. Positive Round-Trip Checks (Dummy Modules & `leanqbe0` Self-Hosting IR) -/

#guard [emptyMod0, dummyAddMod0, dummyLoopMod0, dummyCallTailMod0, dummyAllOpsExtMod0].all
  roundTripOk
#guard match ofTFlatModule (leanqbe0Tfs.take 15) with
  | .ok (m0, _) => roundTripOk m0
  | .error _ => false

private def leanqbe0FullRoundTripCheck : Except String (Nat × Nat) := do
  let (m0, _) ← ofTFlatModule leanqbe0Tfs
  if !roundTripOk m0 then .error "full leanqbe0 roundTrip failed"
  else .ok (m0.fns.length, (encodeMod0 m0).size)

#eval leanqbe0FullRoundTripCheck

/-! ## 3. Negative Malformed-Buffer Rejection Checks -/

private def dummyAddBytes : List UInt8 := (encodeMod0 dummyAddMod0).data.toList

private def badModBuffers : List (List UInt8) :=
  [ [], [0x4c, 0x51, 0x42], [0x4c, 0x51, 0x42, 0x31, 0x01],
    [0x4c, 0x51, 0x42, 0x30, 0x02, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0x4c, 0x51, 0x42, 0x30, 0x01, 1, 0, 0, 0],
    dummyAddBytes ++ [0x00], dummyAddBytes.take (dummyAddBytes.length - 1),
    [0x4c, 0x51, 0x42, 0x30, 0x01, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 99,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0x4c, 0x51, 0x42, 0x30, 0x01, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 5, 0, 0, 0, 0, 10,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0x4c, 0x51, 0x42, 0x30, 0x01, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 1,
      0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0],
    [0x4c, 0x51, 0x42, 0x30, 0x01, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 99,
      0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0] ]

#guard badModBuffers.all fun bs => (decodeMod0 (ByteArray.mk bs.toArray)).isNone

/-! ## 4. Closure-Free, Global-Free & x86-64 Directive Gate (`codec0DecodeLcMod` / `codec0LcMod`) -/

splice_lcnf_tflat! codec0DecodeTfs codec0DecodeLcMod
def codec0DecodeMod : Module :=
  { fns := LeanLRC.tflatFnsToFns codec0DecodeTfs, externs := rtExterns, exits := rtExitSyms }
eval_dir_stats! codec0DecodeDirStats x64Target x64LegalTarget codec0DecodeMod
  rtExtBounds0 rtExitSyms

splice_lcnf_tflat! codec0Tfs codec0LcMod
def codec0Mod : Module :=
  { fns := LeanLRC.tflatFnsToFns codec0Tfs, externs := rtExterns, exits := rtExitSyms }
eval_dir_stats! codec0DirStats x64Target x64LegalTarget codec0Mod
  rtExtBounds0 rtExitSyms

private def lcGateOk (lc : LcModule) (mod : Module) (stats : List (Sym × Nat)) : Bool :=
  lc.papTargets.isEmpty && lc.maxAp == 0 && lcGlobalsCount lc == 0 &&
    mod.fns.length == stats.length && (stats.all fun p => p.2 <= 250) &&
    (mod.fns.all fun f => Func.checkTFlat f.body) && mod.checkAcyclic

#guard lcGateOk codec0DecodeLcMod codec0DecodeMod codec0DecodeDirStats &&
  lcGateOk codec0LcMod codec0Mod codec0DirStats

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
