module

public import LeanQbe.T.LeanLCNF.Basic

/-!
# P5 Coverage Lean 4 Programs (`LeanQbe.T.LeanLCNF.Coverage`)

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
-- END LCNF COVERAGE

lcnf_of_lean! covMod
  [strLitTest, strBuildBench, bigNatBench, arrBench, arrLinear, arrShared, byteArrBench, floatBench]

def covProgram : LcModule := covMod

end LeanQbe.T.LeanLCNF.Coverage
