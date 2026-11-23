module

public import LeanQbe.T.LeanLCNF.Basic

/-!
# Coverage Lean 4 Programs (`LeanQbe.T.LeanLCNF.Coverage`)

Real Lean 4 functions compiled through impure `LCNF` → `LeanQbe.T` covering:
1. String literals (ASCII, 8-byte boundaries, empty, UTF-8 multibyte) & string building
   (`String.push`, `String.append`, `toString : Nat → String`, `String.toList`/`ofList`,
   `String.Pos.Raw` traversal, `==`/`<`/`compare`).
2. Big `Nat` literals (`≥ 2^63`, `≥ 2^64`, `> 2^128`) & arbitrary-precision `Nat` arithmetic
   (`+`, `-`, `*`, `/`, `%`, `<`, `<=`, `==`, `<<<`, `>>>`, `&&&`, `|||`, `^^^`, `pow`, `gcd`,
   `log2`, `pred`, `UInt64.toNat`/`ofNat`).
3. `Array` primitives (`mkEmpty`, `mk`, `push` past 512 bytes, `get!`, `set!`, `size`, `pop`,
   `swap`, `swapIfInBounds`, `toList`, `replicate`) + linear FBIP mutation vs shared copying.
4. `ByteArray` primitives (`empty`, `emptyWithCapacity`, `mk`, `data`, `push`, `get!`, `set!`,
   `size`, `==`, `<`).
5. `Float` (`bits 64` + runtime externs: `+`, `-`, `*`, `/`, `neg`, `abs`, `sqrt`, comparisons,
   `ofScientific`, `toBits`/`ofBits`, `toUInt64`/`UInt64.toFloat`, boxed `Float` in ctors/closures).

The text between `BEGIN`/`END LCNF COVERAGE` is extracted verbatim by `test/lcnf/run.sh` into the
native `lean -c` oracle so all backends execute the exact same source.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LeanLCNF.Coverage

-- BEGIN LCNF COVERAGE
def covModP : Nat := 1000000007

/-! ### 1. Strings & String Building -/

def strChecksum (s : String) : Nat :=
  let rec go (pos : String.Pos.Raw) (fuel : Nat) (acc : Nat) : Nat :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      if pos.atEnd s then acc
      else
        let c := pos.get s
        go (pos.next s) fuel ((acc * 131 + c.toNat) % covModP)
  go 0 (s.utf8ByteSize + 1) 0

def strLitTest (n : Nat) : Nat :=
  let s0 := ""
  let s1 := "abcdefgh"
  let s2 := "hello, LeanQbe!"
  let s3 := "αβγ🚀"
  let s4 := s1 ++ "-" ++ s2 ++ "-" ++ s3 ++ "-" ++ toString n
  let eq0 := if s0 == "" then 1 else 0
  let eq1 := if s1 == "abcdefgh" then 2 else 0
  let lt1 := if s1 < s2 then 4 else 0
  let cmp1 := match compare s2 s1 with | .gt => 8 | _ => 0
  let roundTrip := String.ofList s3.toList
  let eqRt := if roundTrip == s3 then 16 else 0
  let sub := String.Pos.Raw.extract s2 ⟨7⟩ ⟨15⟩
  let eqSub := if sub == "LeanQbe!" then 32 else 0
  ((strChecksum s4 * 64 + s4.length * 17 + s4.utf8ByteSize) % covModP) * 64 +
    eq0 + eq1 + lt1 + cmp1 + eqRt + eqSub

def strBuildBench (n : Nat) : Nat :=
  let rec build : Nat → String → String
    | 0, s => s
    | i + 1, s => build i (s.push (Char.ofNat (65 + i % 26)))
  let s := build n "start:"
  let s := s ++ ":" ++ toString n
  (strChecksum s * 1009 + s.length * 31 + s.utf8ByteSize) % covModP

/-! ### 2. Big `Nat` Literals & Bignum Arithmetic -/

def bigNatBench (n : Nat) : Nat :=
  let b63 : Nat := 9223372036854775808
  let b64 : Nat := 18446744073709551616
  let huge : Nat := 340282366920938463463374607431768211457
  let x := (huge + b64 * n + b63) * (n + 3)
  let y := x / (b63 + 17)
  let r := x % (b63 + 17)
  let z := ((y <<< 7) ||| (r &&& 0xffff)) ^^^ (b64 >>> 3)
  let diff := if x >= huge then x - huge else 0
  let p := Nat.pow (n % 7 + 3) 45
  let g := Nat.gcd (p + b64) (x + b63)
  let l2 := diff.log2 + p.log2
  let u64 := UInt64.ofNat (huge + n)
  let back := u64.toNat + Nat.pred (b63 + 1)
  let combined := (diff + z + p + g + back) % covModP
  let strLen := (toString (huge + b64 * (n + 1))).length
  let ltChk := if b63 < b64 && b64 < huge && (b64 == b63 * 2) then 1 else 0
  (combined * 1024 + l2 * 16 + strLen) * 2 + ltChk

/-! ### 3. `Array` Primitives & Linear FBIP Mutation -/

def sumNatList : List Nat → Nat → Nat
  | [], acc => acc
  | x :: xs, acc => sumNatList xs ((acc + x) % covModP)

def arrPushLoop : Nat → Array Nat → Array Nat
  | 0, a => a
  | i + 1, a => arrPushLoop i (a.push ((i * 37 + 11) % covModP))

def arrBench (n : Nat) : Nat :=
  let a0 := arrPushLoop n (Array.mkEmpty 2)
  let a1 := a0.set! 0 999
  let a2 := a1.swapIfInBounds 0 (n / 2)
  let a3 := if a2.size > 2 then a2.pop else a2
  let fromLst := Array.mk [10, 20, 30, 40]
  let rep := Array.replicate 5 77
  let headVal := a3[0]!
  let lstSum := sumNatList a3.toList 0
  let extra := sumNatList fromLst.toList 0 + sumNatList rep.toList 0
  ((lstSum + headVal * 13 + a3.size * 7 + extra) % covModP)

def arrMutLoop : Nat → Nat → Array Nat → Array Nat
  | 0, _, a => a
  | k + 1, n, a =>
    let idx := (k * 7) % n
    let v := a[idx]!
    let a' := a.set! idx ((v + k + 1) % covModP)
    arrMutLoop k n a'

def arrLinear (n reps : Nat) : Nat :=
  let a := arrPushLoop n (Array.mkEmpty n)
  let a' := arrMutLoop reps n a
  sumNatList a'.toList 0

def arrSharedIter : Nat → Nat → Array Nat → Nat → Nat
  | 0, _, a, acc => (acc + sumNatList a.toList 0) % covModP
  | r + 1, n, a, acc =>
    let a' := a.set! (r % n) (r + 123)
    arrSharedIter r n a' ((acc * 3 + sumNatList a.toList 0) % covModP)

def arrShared (n reps : Nat) : Nat :=
  arrSharedIter reps n (arrPushLoop n (Array.mkEmpty n)) 0

/-! ### 4. `ByteArray` Primitives -/

def baPushLoop : Nat → ByteArray → ByteArray
  | 0, ba => ba
  | i + 1, ba => baPushLoop i (ba.push (UInt8.ofNat ((i * 53 + 7) % 256)))

def sumU8List : List UInt8 → Nat → Nat
  | [], acc => acc
  | x :: xs, acc => sumU8List xs ((acc + x.toNat) % covModP)

def byteArrBench (n : Nat) : Nat :=
  let ba0 := ByteArray.empty
  let ba1 := baPushLoop n (ByteArray.emptyWithCapacity 4)
  let ba2 := ba1.set! 0 42
  let ba3 := ByteArray.mk (Array.mk [1, 2, 3, 4])
  let arr := ba3.data
  let eq := if ba0 == ByteArray.empty then 1 else 0
  let lt := if ba0 < ba2 then 2 else 0
  let mutSum := sumU8List arr.toList 0
  let v0 := (ba2.get! 0).toNat
  let vn := (ba2.get! (n / 2)).toNat
  ((ba2.size * 1009 + v0 * 31 + vn * 17 + mutSum) % covModP) * 4 + eq + lt

/-! ### 5. `Float` (`bits 64` + Runtime Externs) -/

structure FloatPair where
  tag : Nat
  x : Float
  y : Float

def applyFloat (f : Float → Float) (a : Float) : Float := f a

def floatBench (n : Nat) : UInt64 :=
  let f0 := UInt64.toFloat (UInt64.ofNat n)
  let fp : FloatPair := { tag := n, x := f0 + 1.5, y := 2.25 }
  let g := applyFloat (fun z => (z * fp.y - 0.5).sqrt) fp.x
  let c1 := if g < fp.x && fp.y <= fp.x then 1 else 0
  let c2 := if fp.x == (f0 + 1.5) then 2 else 0
  let bits := g.toBits
  let rt := Float.ofBits bits
  let neg := (-rt).abs
  neg.toBits ^^^ UInt64.ofNat (c1 + c2) + neg.toUInt64

/-! ### 6. `Int` (tagged small ints + sign-magnitude bignums) -/

/-- Decimal rendering through `cases` on `Int` (`Int.decLt` + `Int.natAbs` after `toMono`). -/
def intStr (x : Int) : String :=
  match x with
  | .ofNat m => toString m
  | .negSucc m => "-" ++ toString (m + 1)

def intMix (acc : Nat) (x : Int) : Nat := (acc * 1000003 + strChecksum (intStr x)) % covModP

def intMixList : List Int → Nat → Nat
  | [], acc => acc
  | x :: xs, acc => intMixList xs (intMix acc x)

/-- Small, tagged-boundary (`±2^62`, `±2^63`), `> 2^64`, and `> 2^128` samples. -/
def intSamples (n : Nat) : List Int :=
  let m : Int := Int.ofNat n
  let b62 : Int := 4611686018427387904
  let b64 : Int := 18446744073709551616
  let b128 : Int := 340282366920938463463374607431768211456
  [0, 1, -1, 7, -7, m + 2, -m - 3, b62 - 1, b62, -b62, -b62 - 1, b62 * 2 - 1, -(b62 * 2),
    b64 + m, -b64 - m, b128 * (m + 1) + 12345, m - b128 * b128, Int.negSucc (n * n)]

/-- Every binary `Int` operation on one pair (`ediv`/`emod`/`tdiv`/`tmod` on all four sign
combinations and by zero, comparisons, `neg`, `natAbs`). -/
def intPairMix (acc : Nat) (a b : Int) : Nat :=
  let c : Int := (if a == b then 1 else 0) + (if a < b then 2 else 0) + (if a ≤ b then 4 else 0)
  intMixList [a + b, a - b, a * b, a / b, a % b, a.tdiv b, a.tmod b, -a, Int.ofNat a.natAbs, c]
    acc

def intPairsWith (a : Int) : List Int → Nat → Nat
  | [], acc => acc
  | b :: bs, acc => intPairsWith a bs (intPairMix acc a b)

def intPairsAll (ys : List Int) : List Int → Nat → Nat
  | [], acc => acc
  | a :: as, acc => intPairsAll ys as (intPairsWith a ys acc)

/-- Euclidean laws `a = b * (a / b) + a % b` and `0 ≤ a % b < |b|` (`b ≠ 0`). -/
def intLawsWith (a : Int) : List Int → Nat → Nat
  | [], acc => acc
  | b :: bs, acc =>
    let ok := b == 0 || (a == b * (a / b) + a % b && 0 ≤ a % b && a % b < Int.ofNat b.natAbs)
    intLawsWith a bs (if ok then acc + 1 else acc)

def intLawsAll (ys : List Int) : List Int → Nat → Nat
  | [], acc => acc
  | a :: as, acc => intLawsAll ys as (intLawsWith a ys acc)

def intBench (n : Nat) : Nat :=
  let xs := intSamples n
  intPairsAll xs xs (n % 1000) * 1024 + intLawsAll xs xs 0

/-- `BitVec.toInt` at width `w` of the `BitVec` value `x` (written out locally, as are `bvOfInt`
and `intToNat`: imported Lean-defined callees are not extracted by `lcnf_of_lean!`). -/
def bvToInt (w x : Nat) : Int :=
  if 2 * x < 2 ^ w then Int.ofNat x else Int.ofNat x - Int.ofNat (2 ^ w)

def intToNat : Int → Nat
  | .ofNat n => n
  | .negSucc _ => 0

def bvOfInt (w : Nat) (i : Int) : Nat := intToNat (i % Int.ofNat (2 ^ w))

/-- Arbitrary-width `BitVec.toInt`/`ofInt` round trips and `DivConst`-style `2^128` magic. -/
def bitVecIntBench (n : Nat) : Nat :=
  let w := 60 + n % 90
  let x := (2 ^ (w - 1) + n * 977) % 2 ^ w
  let i := bvToInt w x
  let d : Int := Int.ofNat n + 7
  let magic : Int := (340282366920938463463374607431768211456 : Int) / d + 1
  let back := bvToInt 130 (bvOfInt 130 (-magic * Int.ofNat (n + 1)))
  intMixList [i, bvToInt w (bvOfInt w (-i - 1)), magic, back, (magic * d) / 3 - magic % d,
    Int.ofNat (bvOfInt 200 (-(magic * magic)))] 0

/-! ### 7. `Int64`, `UIntN.{ofBitVec,toBitVec}`, `getObjTagNat`, `USize`, non-ASCII names -/

def int64Bench (n : Nat) : Nat :=
  let a := Int64.ofNat n
  let b := Int64.ofNat (18446744073709551616 - 5 - n)
  let c := Int64.ofNat (9223372036854775808 + n)
  let eqs := (if a = Int64.ofNat n then 1 else 0) + (if a = b then 2 else 0) +
    (if b = Int64.ofNat (18446744073709551611 - n) then 4 else 0)
  intMixList [a.toInt, b.toInt, c.toInt, (Int64.ofNat (4611686018427387904 + n)).toInt] eqs

def u64OfBv (x : Nat) : UInt64 :=
  UInt64.ofBitVec (BitVec.ofFin ⟨x % 2 ^ 64, Nat.mod_lt _ (by decide)⟩)

def uintBvBench (n : Nat) : Nat :=
  let big := 340282366920938463463374607431768211457 * (n + 1) + n
  let u := u64OfBv big
  let v := u64OfBv (n * 31)
  let w := UInt32.ofBitVec (BitVec.ofFin ⟨(big + n) % 2 ^ 32, Nat.mod_lt _ (by decide)⟩)
  (u.toBitVec.toFin.val + (u * v + 12345).toBitVec.toFin.val + w.toBitVec.toFin.val * 3 +
    (u ^^^ 0xffffffffffffffff).toBitVec.toFin.val) % covModP

inductive Shape where
  | circle (r : Nat)
  | rect (w h : Nat)
  | dot
  | tri (a b c : Nat)
  deriving DecidableEq

def shapeOf (k : Nat) : Shape :=
  match k % 4 with
  | 0 => .circle k
  | 1 => .rect k (k + 1)
  | 2 => .dot
  | _ => .tri k 1 2

def shapeLoop : Nat → Nat → Nat
  | 0, acc => acc
  | k + 1, acc =>
    let s := shapeOf k
    let t := shapeOf (k / 2 * 2 + k % 2 * 4)
    shapeLoop k ((acc * 7 + s.ctorIdx + (if s = t then 100 else 0)) % covModP)

def shapeBench (n : Nat) : Nat := shapeLoop n 0

/-- `System.Platform.numBits` (local copy, so `getNumBits` is reached from this module). -/
def platformBits : Nat := (System.Platform.getNumBits ()).val

def usizeRepr (n : Nat) : String :=
  if h : n < 2 ^ platformBits then (USize.ofNatLT n h).repr else "big"

def usizeBench (n : Nat) : Nat :=
  strChecksum (usizeRepr n ++ "/" ++ usizeRepr (n * 1000003 + 18446744073709551615))

namespace Sha
def σ₀ (x : UInt32) : UInt32 := (x >>> 7 ||| x <<< 25) ^^^ (x >>> 18 ||| x <<< 14) ^^^ (x >>> 3)
def σ₁ (x : UInt32) : UInt32 := (x >>> 17 ||| x <<< 15) ^^^ (x >>> 19 ||| x <<< 13) ^^^ (x >>> 10)
def «Σ₀» (x : UInt32) : UInt32 :=
  (x >>> 2 ||| x <<< 30) ^^^ (x >>> 13 ||| x <<< 19) ^^^ (x >>> 22 ||| x <<< 10)
def «Σ₁» (x : UInt32) : UInt32 :=
  (x >>> 6 ||| x <<< 26) ^^^ (x >>> 11 ||| x <<< 21) ^^^ (x >>> 25 ||| x <<< 7)
end Sha

/-- Closures over the non-ASCII-named functions (so each stays its own symbol, `pap` target). -/
def shaFns : List (UInt32 → UInt32) := [Sha.σ₀, Sha.σ₁, Sha.«Σ₀», Sha.«Σ₁»]

def shaApply : List (UInt32 → UInt32) → UInt32 → Nat → Nat
  | [], _, acc => acc
  | f :: fs, x, acc => shaApply fs x ((acc * 31 + (f x).toNat) % covModP)

def shaMix (n : Nat) : Nat := shaApply shaFns (UInt32.ofNat (n * 2654435761 + 1)) 0
-- END LCNF COVERAGE

lcnf_of_lean! covMod
  [strLitTest, strBuildBench, bigNatBench, arrBench, arrLinear, arrShared, byteArrBench, floatBench,
   intBench, bitVecIntBench, int64Bench, uintBvBench, shapeBench, usizeBench, shaMix]

def covProgram : LcModule := covMod

end LeanQbe.T.LeanLCNF.Coverage
