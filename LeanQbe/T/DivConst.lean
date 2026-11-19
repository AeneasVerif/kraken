module

public import LeanQbe.T.OptUtil

/-!
# Verified Constant Division & Remainder Optimization Pass (`O-M1`)

Style-B PHOAS optimization pass replacing `.udiv n`, `.urem n`, `.sdiv n`, `.srem n`
(`n ∈ {32, 64}`) with constant divisor `.imm d` by shifts, bitwise masks, or Granlund-Montgomery
widening multiplications guarded by total computable boolean certificates:

* **UB preservation**: `d = 0` is left untouched for all four ops, signed `d = -1#n`
  (`BitVec.allOnes n`, where `INT_MIN / -1` is UB) is left untouched, `n ∉ {32, 64}` is left
  untouched, and any uncertified case falls back to the original instruction unchanged.
* **Unsigned division (`udiv n x d`)**:
  - `d = 1#n` forwards `x` directly without emitting an instruction;
  - `d = 2^m` (`1 ≤ m < n`) lowers to `lshr`;
  - general `d` uses untrusted Granlund-Montgomery `(M, s, addShift)` checked by
    `uNoAddCert` (`umulw + lshr`) or `uAddShiftCert` (`umulw + sub + lshr 1 + add + lshr (s - 1)`).
* **Unsigned remainder (`urem n x d`)**: `d = 1#n` folds to `0#n`, `d = 2^m` lowers to
  `and x (2^m - 1)`, and general `d` lowers to `q := udiv_const; x - q * d`.
* **Signed division (`sdiv n x d`)**: `d = 1#n` forwards `x`, positive `d = 2^m` (`1 ≤ m < n - 1`)
  lowers to signed bias-and-`ashr`, and general `d ∉ {0, 1, -1}` (positive and negative, including
  `INT_MIN`) uses untrusted Granlund-Montgomery `(A, s)` checked by `sDivCert`
  (`smulw` + optional `add`/`sub x` + optional `ashr s` + `lshr (n - 1)` + `add`).
* **Signed remainder (`srem n x d`)**: `d = 1#n` folds to `0#n`, and general `d ∉ {0, 1, -1}`
  lowers to `q := sdiv_const; x - q * d`.

Correctness (`LeanQbe/T/DivConstLemmas.lean`): `divConst_wp`, `divConst_wf`,
`Func.divConst_spec`, `Func.divConst_wf`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## PHOAS two-level operand flattening -/

/-- Flatten a two-level operand `Arg (Arg V) t` into `Arg V t`. -/
def divFlatArg {V : Ty → Type} {t : Ty} : Arg (Arg V) t → Arg V t
  | .var a => a
  | .imm c => .imm c

/-- Flatten a tuple of two-level operands into `Tup (Arg V) ts`. -/
abbrev divFlatArgs {V : Ty → Type} {ts : List Ty} :
    Tup (Arg (Arg V)) ts → Tup (Arg V) ts :=
  tupMapArg fun _ => divFlatArg

/-- Flatten operands of an `Op (Arg V) rs` into `Op V rs`. -/
def divFlatOp {V : Ty → Type} {rs : List Ty} (op : Op (Arg V) rs) : Op V rs :=
  ⟨op.code, divFlatArgs op.args⟩

/-- Lift a variable tuple `Tup V ts` into `Tup (Arg V) ts`. -/
abbrev divArgTup {V : Ty → Type} {ts : List Ty} (xs : Tup V ts) : Tup (Arg V) ts :=
  xs.map fun _ => Arg.var

/-! ## Total computable boolean certificates (trusted checkers) -/

/-- Certificate that `d = 2^m` with `2 ≤ n` and `1 ≤ m < n`. -/
def pow2ShiftCert (n : Nat) (d : BitVec n) (m : Nat) : Bool :=
  2 ≤ n && 1 ≤ m && m < n && d == BitVec.twoPow n m

/-- Certificate for unsigned no-add Granlund-Montgomery division (`1 ≤ M < 2^n`, `s < n`). -/
def uNoAddCert (n : Nat) (d : BitVec n) (M s : Nat) : Bool :=
  2 ≤ n && s < n && 0 < d.toNat && 1 ≤ M && M < 2 ^ n &&
    let pow := 2 ^ (n + s)
    pow ≤ M * d.toNat && (2 ^ n - 1) * (M * d.toNat - pow) < pow

/-- Certificate for unsigned add-shift Granlund-Montgomery division (`2^n ≤ M < 2^(n+1)`). -/
def uAddShiftCert (n : Nat) (d : BitVec n) (M s : Nat) : Bool :=
  2 ≤ n && 1 ≤ s && s ≤ n && 0 < d.toNat && 2 ^ n ≤ M && M < 2 ^ (n + 1) &&
    let pow := 2 ^ (n + s)
    pow ≤ M * d.toNat && (2 ^ n - 1) * (M * d.toNat - pow) < pow

/-- Certificate that `d = 2^m` is a positive signed power of two (`1 ≤ m < n - 1`). -/
def sPow2Cert (n : Nat) (d : BitVec n) (m : Nat) : Bool :=
  2 ≤ n && 1 ≤ m && m + 1 < n && d == BitVec.twoPow n m

/-- Certificate for signed Granlund-Montgomery division (`d ∉ {0, 1, -1}`, both signs). -/
def sDivCert (n : Nat) (d : BitVec n) (A s : Nat) : Bool :=
  2 ≤ n && d != 0#n && d != BitVec.allOnes n && d != 1#n &&
    1 ≤ A && A < 2 ^ n && s < n &&
    let H := 2 ^ (n - 1)
    let D := d.toInt.natAbs
    let B := 2 ^ (n + s)
    B < A * D &&
      let e := A * D - B
      let xSame := if 0 < d.toInt then H - 1 else H
      let xOpp := if 0 < d.toInt then H else H - 1
      let ancSame := xSame - (xSame + 1) % D
      let ancOpp := xOpp - (xOpp + 1) % D
      ancSame * e < B && xSame * e < 2 * B && ancOpp * e ≤ B && xOpp * e ≤ 2 * B

/-! ## Untrusted constant synthesizers -/

/-- Untrusted power-of-two shift finder for unsigned ops (`1 ≤ m < n`). -/
def findPow2Shift (n : Nat) (d : BitVec n) : Option Nat :=
  let m := Nat.log2 d.toNat
  if pow2ShiftCert n d m then some m else none

/-- Untrusted positive signed power-of-two finder (`1 ≤ m < n - 1`). -/
def findSPow2Shift (n : Nat) (d : BitVec n) : Option Nat :=
  let m := Nat.log2 d.toNat
  if sPow2Cert n d m then some m else none

/-- Untrusted Granlund-Montgomery unsigned magic `(M, s, addShift)` finder. -/
def findUMagic (n : Nat) (d : BitVec n) : Option (Nat × Nat × Bool) :=
  if d.toNat ≤ 1 then none
  else
    let s := Nat.log2 d.toNat
    let M1 := 2 ^ (n + s) / d.toNat + 1
    if uNoAddCert n d M1 s then some (M1, s, false)
    else
      let s2 := s + 1
      let M2 := 2 ^ (n + s2) / d.toNat + 1
      if uAddShiftCert n d M2 s2 then some (M2, s2, true)
      else none

/-- Bounded search over shift `s < n` for signed Granlund-Montgomery magic `(A, s)`. -/
def findSMagicAux (n : Nat) (d : BitVec n) (D : Nat) : Nat → Nat → Option (Nat × Nat)
  | 0, _ => none
  | fuel + 1, s =>
    let A := 2 ^ (n + s) / D + 1
    if sDivCert n d A s then some (A, s)
    else findSMagicAux n d D fuel (s + 1)

/-- Untrusted Granlund-Montgomery signed magic `(A, s)` finder. -/
def findSMagic (n : Nat) (d : BitVec n) : Option (Nat × Nat) :=
  let D := d.toInt.natAbs
  if D < 2 then none
  else findSMagicAux n d D n 0

/-! ## Certified instruction emitters -/

/-- Emit certified constant unsigned division for `n ∈ {32, 64}` and `d ≠ 0#n`. -/
def emitUDivConst {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (n : Nat) (x : Arg V (.bits n)) (d : BitVec n)
    (k : Arg V (.bits n) → Expr V L rs) : Option (Expr V L rs) :=
  if !(n == 32 || n == 64) then none
  else if d == 0#n then none
  else if d == 1#n then some (k x)
  else
    match findPow2Shift n d with
    | some m =>
      if pow2ShiftCert n d m then
        some (.let_ (op2 (.lshr (.bits n)) x (.imm (BitVec.ofNat n m))) fun (q, ()) => k (.var q))
      else none
    | none =>
      match findUMagic n d with
      | some (M, s, false) =>
        if uNoAddCert n d M s then
          some (
            .let_ (op2 (.umulw n) x (.imm (BitVec.ofNat n M))) fun (_, hi, ()) =>
            .let_ (op2 (.lshr (.bits n)) (.var hi) (.imm (BitVec.ofNat n s))) fun (q, ()) =>
            k (.var q))
        else none
      | some (M, s, true) =>
        if uAddShiftCert n d M s then
          some (
            .let_ (op2 (.umulw n) x (.imm (BitVec.ofNat n (M - 2 ^ n)))) fun (_, hi, ()) =>
            .let_ (op2 (.sub (.bits n)) x (.var hi)) fun (t1, ()) =>
            .let_ (op2 (.lshr (.bits n)) (.var t1) (.imm 1#n)) fun (t2, ()) =>
            .let_ (op2 (.add (.bits n)) (.var hi) (.var t2)) fun (t3, ()) =>
            .let_ (op2 (.lshr (.bits n)) (.var t3) (.imm (BitVec.ofNat n (s - 1)))) fun (q, ()) =>
            k (.var q))
        else none
      | none => none

/-- Emit certified constant unsigned remainder for `n ∈ {32, 64}` and `d ≠ 0#n`. -/
def emitURemConst {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (n : Nat) (x : Arg V (.bits n)) (d : BitVec n)
    (k : Arg V (.bits n) → Expr V L rs) : Option (Expr V L rs) :=
  if !(n == 32 || n == 64) then none
  else if d == 0#n then none
  else if d == 1#n then some (k (.imm 0#n))
  else
    match findPow2Shift n d with
    | some m =>
      if pow2ShiftCert n d m then
        some (.let_ (op2 (.and (.bits n)) x (.imm (BitVec.twoPow n m - 1#n))) fun (r, ()) =>
          k (.var r))
      else none
    | none =>
      emitUDivConst n x d fun q =>
        .let_ (op2 (.mul (.bits n)) q (.imm d)) fun (p, ()) =>
        .let_ (op2 (.sub (.bits n)) x (.var p)) fun (r, ()) =>
        k (.var r)

/-- Emit certified constant signed division for `n ∈ {32, 64}` and `d ∉ {0#n, -1#n}`. -/
def emitSDivConst {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (n : Nat) (x : Arg V (.bits n)) (d : BitVec n)
    (k : Arg V (.bits n) → Expr V L rs) : Option (Expr V L rs) :=
  if !(n == 32 || n == 64) then none
  else if d == 0#n || d == BitVec.allOnes n then none
  else if d == 1#n then some (k x)
  else
    match findSPow2Shift n d with
    | some m =>
      if sPow2Cert n d m then
        if m == 1 then
          some (
            .let_ (op2 (.lshr (.bits n)) x (.imm (BitVec.ofNat n (n - 1)))) fun (t1, ()) =>
            .let_ (op2 (.add (.bits n)) x (.var t1)) fun (t2, ()) =>
            .let_ (op2 (.ashr (.bits n)) (.var t2) (.imm 1#n)) fun (q, ()) =>
            k (.var q))
        else
          some (
            .let_ (op2 (.ashr (.bits n)) x (.imm (BitVec.ofNat n (n - 1)))) fun (t1, ()) =>
            .let_ (op2 (.lshr (.bits n)) (.var t1) (.imm (BitVec.ofNat n (n - m)))) fun (t2, ()) =>
            .let_ (op2 (.add (.bits n)) x (.var t2)) fun (t3, ()) =>
            .let_ (op2 (.ashr (.bits n)) (.var t3) (.imm (BitVec.ofNat n m))) fun (q, ()) =>
            k (.var q))
      else none
    | none =>
      match findSMagic n d with
      | some (A, s) =>
        if sDivCert n d A s then
          let mInt : Int := if 0 < d.toInt then (A : Int) else -(A : Int)
          let m : BitVec n := BitVec.ofInt n mInt
          let afterShift (t : Arg V (.bits n)) : Expr V L rs :=
            let finish (q0 : Arg V (.bits n)) : Expr V L rs :=
              .let_ (op2 (.lshr (.bits n)) q0 (.imm (BitVec.ofNat n (n - 1)))) fun (sgn, ()) =>
              .let_ (op2 (.add (.bits n)) q0 (.var sgn)) fun (q, ()) =>
              k (.var q)
            if s == 0 then finish t
            else .let_ (op2 (.ashr (.bits n)) t (.imm (BitVec.ofNat n s))) fun (q0, ()) =>
              finish (.var q0)
          some (
            .let_ (op2 (.smulw n) x (.imm m)) fun (_, hi, ()) =>
            if 0 < d.toInt && m.toInt < 0 then
              .let_ (op2 (.add (.bits n)) (.var hi) x) fun (t, ()) => afterShift (.var t)
            else if d.toInt < 0 && 0 < m.toInt then
              .let_ (op2 (.sub (.bits n)) (.var hi) x) fun (t, ()) => afterShift (.var t)
            else
              afterShift (.var hi))
        else none
      | none => none

/-- Emit certified constant signed remainder for `n ∈ {32, 64}` and `d ∉ {0#n, -1#n}`. -/
def emitSRemConst {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (n : Nat) (x : Arg V (.bits n)) (d : BitVec n)
    (k : Arg V (.bits n) → Expr V L rs) : Option (Expr V L rs) :=
  if !(n == 32 || n == 64) then none
  else if d == 0#n || d == BitVec.allOnes n then none
  else if d == 1#n then some (k (.imm 0#n))
  else
    emitSDivConst n x d fun q =>
      .let_ (op2 (.mul (.bits n)) q (.imm d)) fun (p, ()) =>
      .let_ (op2 (.sub (.bits n)) x (.var p)) fun (r, ()) =>
      k (.var r)

/-! ## PHOAS `divConst` pass -/

/-- Lower one `let_` operation with optional constant division/remainder replacement. -/
def divConstOp {V : Ty → Type} {L : List Ty → Type} {rs ts : List Ty}
    (op : Op (Arg V) ts) (k : Tup (Arg V) ts → Expr V L rs) : Expr V L rs :=
  let op' := divFlatOp op
  let fallback := .let_ op' fun xs => k (divArgTup xs)
  let ⟨code, args⟩ := op'
  match code, args with
  | .udiv n, (x, .imm d, ()) =>
    (emitUDivConst n x d fun res => k (res, ())).getD fallback
  | .urem n, (x, .imm d, ()) =>
    (emitURemConst n x d fun res => k (res, ())).getD fallback
  | .sdiv n, (x, .imm d, ()) =>
    (emitSDivConst n x d fun res => k (res, ())).getD fallback
  | .srem n, (x, .imm d, ()) =>
    (emitSRemConst n x d fun res => k (res, ())).getD fallback
  | _, _ => fallback

mutual
/-- Rewrite certified constant division/remainder ops across an `Expr (Arg V) L rs`. -/
def divConst {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    Expr (Arg V) L rs → Expr V L rs
  | .let_ op k => divConstOp op fun res => divConst (k res)
  | .load t a k => .load t (divFlatArg a) fun v => divConst (k (.var v))
  | .store v a k => .store (divFlatArg v) (divFlatArg a) (divConst k)
  | .call f args k =>
    .call f (divFlatArgs args) fun xs => divConst (k (divArgTup xs))
  | .jnz c t e => .jnz (divFlatArg c) (divConst t) (divConst e)
  | .jump j args => .jump j (divFlatArgs args)
  | .ret vs => .ret (divFlatArgs vs)
  | .exit f args => .exit f (divFlatArgs args)
  | .hlt => .hlt
  | .group bodies k =>
    .group (fun Js => divConstB (bodies Js)) (fun Js => divConst (k Js))

/-- Block-list companion of `divConst`. -/
def divConstB {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → Blocks (Arg V) L rs sig → Blocks V L rs sig
  | _, .nil => .nil
  | _, .cons b bs => .cons (fun xs => divConst (b (divArgTup xs))) (divConstB bs)
end

/-- Run constant division & remainder optimization on a closed typed function `Func`. -/
def Func.divConst {as rs : List Ty} (f : Func as rs) : Func as rs :=
  fun V L xs => LeanQbe.T.divConst (f (Arg V) L (divArgTup xs))

/-- Run constant division & remainder optimization on a named typed function `Fn`. -/
def Fn.divConst (fn : Fn) : Fn :=
  ⟨fn.name, fn.as, fn.rs, Func.divConst fn.body⟩

end LeanQbe.T
