module

public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0StepAttr
public import LeanQbe.T.Logic.ControlComb
public import LeanQbe.T.Logic.C0Agrees
public import LeanQbe.T.Logic.MemLemmas
public meta import Lean
public meta import LeanQbe.T.Logic.C0StepAttr
public meta import LeanQbe.T.Logic.C0Step

/-!
# ProofKit: Additive C0 / BitVec / Frame / Loop Combinators

Strictly additive proof-automation kit extending `C0Step`, `C0HeadStep`, `ControlComb`,
and `C0Agrees` without touching core pipeline modules:

1. **Additive `@[bv_c0]` rules & `c0_bv_omega`**:
   * Safe `@[bv_c0]` normalizations for `OfNat` BitVec literals, arbitrary `n ≤ w`
     `setWidth` widening (via `simproc`), shifts `<<<`/`>>>`, `udiv`/`umod`, `&&& 1`,
     and `(x <<< 1 ||| 1)`. Never rewrites `BitVec` equality globally.
   * `c0_bv_omega` tactic: normalizes BitVec comparisons and `.toNat` expressions,
     asserts `BitVec.isLt` bounds, applies `omega`-backed simplification for
     `(x - y).toNat` (`BitVec.toNat_sub_of_le`) and `a % b` (`Nat.mod_eq_of_lt`),
     and closes linear Nat/BitVec obligations via `omega`.
2. **`state_frame` / `state_frame!` tactics**:
   Recursively decomposes conjunctions and `Prop`-valued `structure`s (such as nested
   `LengthsOk`, `Preserves*`, `AgreesExcept`), and closes preserved fields
   (`{ s with f := v }.g = s.g`, `List.length_set`, projected invariants) cleanly.
3. **Structured loop & cursor combinators**:
   * `wp_while_state_mem`, `wp_while_state_agrees`, `c0_while_state`
   * `ArrayCursorInv`, `ArrayMutCursorInv`
   * `wp_while_cursor64`, `wp_while_cursor32`, `wp_while_mut_cursor64`
-/

set_option autoImplicit false

namespace LeanQbe.T.ProofKit

/-! ## 1. Pure Cursor Structures (`@[expose]`) -/

@[expose] public section

/-- Read-only array scan invariant over index slice `[lo, hi)` of `xs` paired with
arbitrary extra loop state `st : α`. -/
structure ArrayCursorInv {β : Type} {α : Type _} (lo hi : Nat) (xs : List β)
    (Inv : Nat → α → Prop) (idx : Nat) (st : α) : Prop where
  lo_le : lo ≤ idx
  idx_le : idx ≤ hi
  hi_le : hi ≤ xs.length
  inv : Inv idx st

/-- Mutating array scan invariant over index slice `[lo, hi)` starting from `xs₀`,
tracking that length is preserved and elements outside `[lo, idx)` still match `xs₀`. -/
structure ArrayMutCursorInv {β : Type} {α : Type _} (lo hi : Nat) (xs₀ : List β)
    (Inv : Nat → List β → α → Prop) (idx : Nat) (xs : List β) (st : α) : Prop where
  lo_le : lo ≤ idx
  idx_le : idx ≤ hi
  hi_le : hi ≤ xs₀.length
  len_eq : xs.length = xs₀.length
  outside_eq : OutsideSliceAgrees lo idx xs₀ xs
  inv : Inv idx xs st

end

/-! ## 2. Additive `@[bv_c0]` Normalization Rules -/

public section

private theorem nat_pow_pos_two (k : Nat) : 0 < 2 ^ k :=
  Nat.pow_pos (by decide)

@[bv_c0] theorem bv_c0_toNat_ofNat_lit {w n : Nat} :
    (@OfNat.ofNat (BitVec w) n BitVec.instOfNat).toNat = n % 2 ^ w :=
  rfl

@[bv_c0] theorem bv_c0_toNat_zero {w : Nat} :
    (0 : BitVec w).toNat = 0 :=
  BitVec.toNat_zero

theorem bv_c0_toNat_setWidth_of_le {n w : Nat} (x : BitVec n) (hle : n ≤ w) :
    (x.setWidth w).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) hle))

theorem bv_c0_toNat_setWidth_of_ble {n w : Nat} (x : BitVec n) (h : Nat.ble n w = true) :
    (x.setWidth w).toNat = x.toNat :=
  bv_c0_toNat_setWidth_of_le x (Nat.le_of_ble_eq_true h)

@[bv_c0 high] theorem bv_c0_zext1_32 (x : BitVec 1) : (x.setWidth 32).toNat = x.toNat :=
  bv_c0_toNat_setWidth_of_le x (by decide)

@[bv_c0 high] theorem bv_c0_zext1_64 (x : BitVec 1) : (x.setWidth 64).toNat = x.toNat :=
  bv_c0_toNat_setWidth_of_le x (by decide)

@[bv_c0 high] theorem bv_c0_zext8_16 (x : BitVec 8) : (x.setWidth 16).toNat = x.toNat :=
  bv_c0_toNat_setWidth_of_le x (by decide)

@[bv_c0 high] theorem bv_c0_zext_self {w : Nat} (x : BitVec w) :
    (x.setWidth w).toNat = x.toNat :=
  bv_c0_toNat_setWidth_of_le x (Nat.le_refl w)

@[bv_c0] theorem bv_c0_toNat_shiftLeft_nat {w : Nat} (x : BitVec w) (k : Nat) :
    (x <<< k).toNat = (x.toNat * 2 ^ k) % 2 ^ w := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

@[bv_c0] theorem bv_c0_toNat_shiftLeft_bv {w m : Nat} (x : BitVec w) (y : BitVec m) :
    (x <<< y).toNat = (x.toNat * 2 ^ y.toNat) % 2 ^ w := by
  rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

@[bv_c0] theorem bv_c0_toNat_ushiftRight_nat {w : Nat} (x : BitVec w) (k : Nat) :
    (x >>> k).toNat = x.toNat / 2 ^ k := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

@[bv_c0] theorem bv_c0_toNat_ushiftRight_bv {w m : Nat} (x : BitVec w) (y : BitVec m) :
    (x >>> y).toNat = x.toNat / 2 ^ y.toNat := by
  rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

@[bv_c0] theorem bv_c0_toNat_udiv {w : Nat} (x y : BitVec w) :
    (x / y).toNat = x.toNat / y.toNat :=
  BitVec.toNat_udiv

@[bv_c0] theorem bv_c0_toNat_umod {w : Nat} (x y : BitVec w) :
    (x % y).toNat = x.toNat % y.toNat :=
  BitVec.toNat_umod

theorem bv_c0_toNat_and_one_of_le {w : Nat} (x : BitVec w) (hw : 1 ≤ w) :
    (x &&& 1#w).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and, BitVec.toNat_one hw]
  simp [Nat.and_two_pow_sub_one_eq_mod x.toNat 1]

@[bv_c0 high] theorem bv_c0_toNat_and_one_64 (x : BitVec 64) :
    (x &&& 1#64).toNat = x.toNat % 2 :=
  bv_c0_toNat_and_one_of_le x (by decide)

@[bv_c0 high] theorem bv_c0_toNat_and_one_32 (x : BitVec 32) :
    (x &&& 1#32).toNat = x.toNat % 2 :=
  bv_c0_toNat_and_one_of_le x (by decide)

@[bv_c0 high] theorem bv_c0_toNat_and_one_16 (x : BitVec 16) :
    (x &&& 1#16).toNat = x.toNat % 2 :=
  bv_c0_toNat_and_one_of_le x (by decide)

@[bv_c0 high] theorem bv_c0_toNat_and_one_8 (x : BitVec 8) :
    (x &&& 1#8).toNat = x.toNat % 2 :=
  bv_c0_toNat_and_one_of_le x (by decide)

@[bv_c0 high] theorem bv_c0_toNat_and_bv_one_64 (x : BitVec 64) :
    (x &&& BitVec.ofNat 64 1).toNat = x.toNat % 2 :=
  bv_c0_toNat_and_one_64 x

@[bv_c0 high] theorem bv_c0_toNat_and_bv_one_32 (x : BitVec 32) :
    (x &&& BitVec.ofNat 32 1).toNat = x.toNat % 2 :=
  bv_c0_toNat_and_one_32 x

private theorem testBit_two_mul (k j : Nat) : (2 * k).testBit (j + 1) = k.testBit j := by
  have : 2 * k = k <<< 1 := by rw [Nat.shiftLeft_eq]; omega
  rw [this, Nat.testBit_shiftLeft]
  simp

private theorem testBit_two_mul_add_one (k j : Nat) :
    (2 * k + 1).testBit (j + 1) = k.testBit j := by
  rw [Nat.testBit_succ, show (2 * k + 1) / 2 = k by omega]

private theorem nat_two_mul_or_one (k : Nat) : (2 * k) ||| 1 = 2 * k + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  cases i with
  | zero =>
    simp [Nat.testBit_zero]
  | succ j =>
    have h1 : (1 : Nat).testBit (j + 1) = false := by simp [Nat.testBit_succ]
    simp [testBit_two_mul, testBit_two_mul_add_one, h1]

theorem bv_c0_toNat_shl1_or_one_of_le {w : Nat} (x : BitVec w) (hw : 1 ≤ w) :
    ((x <<< 1) ||| 1#w).toNat = (2 * x.toNat + 1) % 2 ^ w := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_one hw]
  have hdvd : 2 ∣ 2 ^ w := by
    refine ⟨2 ^ (w - 1), ?_⟩
    have hw' : w = (w - 1) + 1 := by omega
    calc
      2 ^ w = 2 ^ ((w - 1) + 1) := by rw [← hw']
      _ = 2 ^ (w - 1) * 2 := Nat.pow_succ 2 (w - 1)
      _ = 2 * 2 ^ (w - 1) := Nat.mul_comm _ _
  obtain ⟨m, hm⟩ := hdvd
  have heven : (x.toNat * 2 ^ 1) % 2 ^ w = 2 * (x.toNat % m) := by
    rw [Nat.pow_one, Nat.mul_comm x.toNat 2, hm, Nat.mul_mod_mul_left]
  rw [heven, nat_two_mul_or_one]
  have hm_pos : 0 < m := by
    have hpos := nat_pow_pos_two w
    omega
  have hlt : 2 * (x.toNat % m) + 1 < 2 ^ w := by
    have hmod : x.toNat % m < m := Nat.mod_lt _ hm_pos
    omega
  have hmod2 : 2 * (x.toNat % m) = (2 * x.toNat) % (2 * m) :=
    (Nat.mul_mod_mul_left 2 x.toNat m).symm
  rw [← Nat.mod_eq_of_lt hlt, hm, Nat.add_mod (2 * (x.toNat % m)) 1 (2 * m), hmod2,
    Nat.mod_mod, ← Nat.add_mod (2 * x.toNat) 1 (2 * m)]

@[bv_c0 high] theorem bv_c0_toNat_shl1_or_one_64 (x : BitVec 64) :
    ((x <<< 1) ||| 1#64).toNat = (2 * x.toNat + 1) % 2 ^ 64 :=
  bv_c0_toNat_shl1_or_one_of_le x (by decide)

@[bv_c0 high] theorem bv_c0_toNat_shl1_or_one_32 (x : BitVec 32) :
    ((x <<< 1) ||| 1#32).toNat = (2 * x.toNat + 1) % 2 ^ 32 :=
  bv_c0_toNat_shl1_or_one_of_le x (by decide)

@[bv_c0 high] theorem bv_c0_toNat_zext32_shl1_or_one (x : BitVec 32) :
    ((x.setWidth 64 <<< 1) ||| 1#64).toNat = 2 * x.toNat + 1 := by
  rw [bv_c0_toNat_shl1_or_one_64, bv_c0_toNat_setWidth_of_le x (by decide)]
  exact Nat.mod_eq_of_lt (by have := x.isLt; omega)

private theorem nat_two_mul_xor_one (k : Nat) : (2 * k) ^^^ 1 = 2 * k + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ j =>
    have h1 : (1 : Nat).testBit (j + 1) = false := by simp [Nat.testBit_succ]
    simp [testBit_two_mul, testBit_two_mul_add_one, h1]

private theorem nat_two_mul_add_one_xor_one (k : Nat) : (2 * k + 1) ^^^ 1 = 2 * k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ j =>
    have h1 : (1 : Nat).testBit (j + 1) = false := by simp [Nat.testBit_succ]
    simp [testBit_two_mul, testBit_two_mul_add_one, h1]

theorem bv_c0_toNat_xor_one_of_le {w : Nat} (x : BitVec w) (hw : 1 ≤ w) :
    (x ^^^ 1#w).toNat = if x.toNat % 2 = 0 then x.toNat + 1 else x.toNat - 1 := by
  rw [BitVec.toNat_xor, BitVec.toNat_one hw]
  split
  · rename_i hm
    have hx : x.toNat = 2 * (x.toNat / 2) := by omega
    calc
      x.toNat ^^^ 1 = (2 * (x.toNat / 2)) ^^^ 1 := by rw [← hx]
      _ = 2 * (x.toNat / 2) + 1 := nat_two_mul_xor_one (x.toNat / 2)
      _ = x.toNat + 1 := by omega
  · rename_i hm
    have hx : x.toNat = 2 * (x.toNat / 2) + 1 := by omega
    calc
      x.toNat ^^^ 1 = (2 * (x.toNat / 2) + 1) ^^^ 1 := by rw [← hx]
      _ = 2 * (x.toNat / 2) := nat_two_mul_add_one_xor_one (x.toNat / 2)
      _ = x.toNat - 1 := by omega

@[bv_c0 high] theorem bv_c0_toNat_xor_one_ushiftRight {w : Nat} (x : BitVec w) (hw : 1 ≤ w) :
    ((x ^^^ 1#w) >>> 1).toNat = x.toNat / 2 := by
  rw [bv_c0_toNat_ushiftRight_nat, bv_c0_toNat_xor_one_of_le x hw, Nat.pow_one]
  split <;> omega

@[bv_c0 high] theorem bv_c0_toNat_xor_one_ushiftRight_64 (x : BitVec 64) :
    ((x ^^^ 1#64) >>> 1).toNat = x.toNat / 2 :=
  bv_c0_toNat_xor_one_ushiftRight x (by decide)

@[bv_c0 high] theorem bv_c0_toNat_xor_one_ushiftRight_32 (x : BitVec 32) :
    ((x ^^^ 1#32) >>> 1).toNat = x.toNat / 2 :=
  bv_c0_toNat_xor_one_ushiftRight x (by decide)

/-! ### `c0_bv_omega`-only equality & subtraction bridges (NOT in `@[bv_c0]`) -/

theorem bv_c0_eq_iff {w : Nat} (a b : BitVec w) : a = b ↔ a.toNat = b.toNat :=
  BitVec.toNat_eq

theorem bv_c0_ne_iff {w : Nat} (a b : BitVec w) : a ≠ b ↔ a.toNat ≠ b.toNat := by
  simp [BitVec.toNat_eq]

theorem bv_c0_lt_iff {w : Nat} (a b : BitVec w) : a < b ↔ a.toNat < b.toNat :=
  BitVec.lt_def

theorem bv_c0_le_iff {w : Nat} (a b : BitVec w) : a ≤ b ↔ a.toNat ≤ b.toNat :=
  BitVec.le_def

theorem bv_c0_toNat_sub_of_le_toNat {w : Nat} (x y : BitVec w) (h : y.toNat ≤ x.toNat) :
    (x - y).toNat = x.toNat - y.toNat :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)

theorem bv_c0_toNat_xor_one_64 (x : BitVec 64) :
    (x ^^^ 1#64).toNat = if x.toNat % 2 = 0 then x.toNat + 1 else x.toNat - 1 :=
  bv_c0_toNat_xor_one_of_le x (by decide)

theorem bv_c0_toNat_xor_one_32 (x : BitVec 32) :
    (x ^^^ 1#32).toNat = if x.toNat % 2 = 0 then x.toNat + 1 else x.toNat - 1 :=
  bv_c0_toNat_xor_one_of_le x (by decide)

theorem bv_c0_toNat_xor_one_8 (x : BitVec 8) :
    (x ^^^ 1#8).toNat = if x.toNat % 2 = 0 then x.toNat + 1 else x.toNat - 1 :=
  bv_c0_toNat_xor_one_of_le x (by decide)

theorem bv_c0_ult_iff_toNat {w : Nat} (a b : BitVec w) :
    BitVec.ult a b = true ↔ a.toNat < b.toNat :=
  ⟨of_decide_eq_true, decide_eq_true⟩

theorem bv_c0_ule_iff_toNat {w : Nat} (a b : BitVec w) :
    BitVec.ule a b = true ↔ a.toNat ≤ b.toNat :=
  ⟨of_decide_eq_true, decide_eq_true⟩

end

/-! ## 3. Meta Infrastructure: `bv_c0` Simprocs, `c0_bv_omega`, `state_frame` -/

public section

open Lean Meta Elab Tactic

meta def evalNatExpr? (e : Lean.Expr) : MetaM (Option Nat) :=
  Meta.getNatValue? e

/-- Kernel-sound pre-`simproc` reducing `(x.setWidth w).toNat` to `x.toNat` for any concrete
widths `n ≤ w`, using `bv_c0_toNat_setWidth_of_ble` with `Eq.refl true`. -/
simproc ↑ [bv_c0] bv_c0_setWidth_toNat (BitVec.toNat (BitVec.setWidth _ _)) := fun e => do
  unless e.isAppOfArity ``BitVec.toNat 2 do return .continue
  let inner := e.appArg!
  unless inner.isAppOfArity ``BitVec.setWidth 3 do return .continue
  let args := inner.getAppArgs
  let nE := args[0]!
  let wE := args[1]!
  let xE := args[2]!
  let some n ← evalNatExpr? nE | return .continue
  let some w ← evalNatExpr? wE | return .continue
  if n ≤ w then
    let lhs := mkApp2 (mkConst ``BitVec.toNat) nE xE
    let reflTrue ← mkEqRefl (mkConst ``Bool.true)
    let prf := mkApp4 (mkConst ``bv_c0_toNat_setWidth_of_ble) nE wE xE reflTrue
    return .done { expr := lhs, proof? := some prf }
  return .continue

/-- Kernel-sound pre-`simproc` reducing concrete `(@OfNat.ofNat (BitVec w) n BitVec.instOfNat).toNat`
directly to the numeral `n` when `n < 2 ^ w`. -/
simproc ↑ [bv_c0] bv_c0_ofNat_toNat (BitVec.toNat (@OfNat.ofNat (BitVec _) _ _)) := fun e => do
  unless e.isAppOfArity ``BitVec.toNat 2 do return .continue
  let inner := e.appArg!
  unless inner.isAppOfArity ``OfNat.ofNat 3 do return .continue
  let args := inner.getAppArgs
  let tyE := args[0]!
  let nE := args[1]!
  let some w ← evalNatExpr? e.appFn!.appArg! | return .continue
  let some n ← evalNatExpr? nE | return .continue
  if n < 2 ^ w && tyE.isAppOfArity ``BitVec 1 then
    let numE := mkNatLit n
    let prf ← mkEqRefl e
    return .done { expr := numE, proof? := some prf }
  return .continue

private meta def propFactsFromLCtx : MetaM (List Lean.Expr) := do
  let mut facts : List Lean.Expr := []
  for decl in ← getLCtx do
    if !decl.isImplementationDetail then
      if ← isProp decl.type then
        facts := decl.toExpr :: facts
  return facts

private meta def tryProveWithOmega? (goalTy : Lean.Expr) : MetaM (Option Lean.Expr) := do
  withoutModifyingState do
    try
      let facts ← propFactsFromLCtx
      let mvar ← mkFreshExprSyntheticOpaqueMVar goalTy
      Lean.Elab.Tactic.Omega.omega facts mvar.mvarId!
      let prf ← instantiateMVars mvar
      if prf.hasExprMVar then return none
      return some prf
    catch _ =>
      return none

/-- Reduce `2 ^ k` for concrete Nat literals `k ≤ 64` so `omega` handles `x * 2 ^ k`
and `x / 2 ^ k` linearly. Uses plain kernel `Eq.refl`. -/
simproc c0PowSimproc ((2 : Nat) ^ _) := fun e => do
  unless e.isAppOfArity ``HPow.hPow 6 do return .continue
  let args := e.getAppArgs
  unless args[0]!.isConstOf ``Nat && args[1]!.isConstOf ``Nat && args[2]!.isConstOf ``Nat do
    return .continue
  let some b ← evalNatExpr? args[4]! | return .continue
  let some k ← evalNatExpr? args[5]! | return .continue
  if b == 2 && k ≤ 64 then
    let valE := mkNatLit (2 ^ k)
    let prf ← mkEqRefl e
    return .done { expr := valE, proof? := some prf }
  return .continue

/-- Post-`simproc` rewriting `(x - y).toNat` to `x.toNat - y.toNat` whenever `omega` proves
`y.toNat ≤ x.toNat` from local hypotheses. -/
simproc ↓ c0SubModSimproc (BitVec.toNat (_ - _)) := fun e => do
  unless e.isAppOfArity ``BitVec.toNat 2 do return .continue
  let inner := e.appArg!
  unless inner.isAppOfArity ``HSub.hSub 6 do return .continue
  let args := inner.getAppArgs
  let wE := e.appFn!.appArg!
  let xE := args[4]!
  let yE := args[5]!
  let xToNat := mkApp2 (mkConst ``BitVec.toNat) wE xE
  let yToNat := mkApp2 (mkConst ``BitVec.toNat) wE yE
  let condTy ← mkAppM ``LE.le #[yToNat, xToNat]
  let some hle ← tryProveWithOmega? condTy | return .continue
  let prf := mkApp4 (mkConst ``bv_c0_toNat_sub_of_le_toNat) wE xE yE hle
  let rhs ← mkAppM ``HSub.hSub #[xToNat, yToNat]
  return .visit { expr := rhs, proof? := some prf }

/-- Post-`simproc` rewriting `a % b` to `a` whenever `omega` proves `a < b` from local
hypotheses. -/
simproc ↓ c0ModLtSimproc ((_ : Nat) % _) := fun e => do
  unless e.isAppOfArity ``HMod.hMod 6 do return .continue
  let args := e.getAppArgs
  unless args[0]!.isConstOf ``Nat && args[1]!.isConstOf ``Nat && args[2]!.isConstOf ``Nat do
    return .continue
  let aE := args[4]!
  let bE := args[5]!
  let condTy ← mkAppM ``LT.lt #[aE, bE]
  let some hlt ← tryProveWithOmega? condTy | return .continue
  let prf := mkApp3 (mkConst ``Nat.mod_eq_of_lt) aE bE hlt
  return .visit { expr := aE, proof? := some prf }

private meta def collectToNatArgs (e : Lean.Expr) (seen : Std.HashSet Lean.Expr) :
    MetaM (Std.HashSet Lean.Expr) := do
  let ref ← IO.mkRef seen
  e.forEach fun sub => do
    if sub.hasLooseBVars then
      return
    if sub.isAppOfArity ``BitVec.toNat 2 then
      ref.modify (·.insert sub)
  ref.get

private meta def collectBitVecExprs (e : Lean.Expr) (seen : Std.HashSet Lean.Expr) :
    MetaM (Std.HashSet Lean.Expr) := do
  let ref ← IO.mkRef seen
  e.forEach fun sub => do
    if sub.hasLooseBVars then
      return
    try
      let ty ← whnf (← inferType sub)
      if ty.isAppOfArity ``BitVec 1 then
        let fn := sub.getAppFn
        let isArith := fn.isConstOf ``HAdd.hAdd || fn.isConstOf ``HSub.hSub ||
          fn.isConstOf ``HMul.hMul || fn.isConstOf ``HShiftLeft.hShiftLeft ||
          fn.isConstOf ``HShiftRight.hShiftRight || fn.isConstOf ``OfNat.ofNat ||
          fn.isConstOf ``BitVec.ofNat || fn.isConstOf ``BitVec.setWidth ||
          fn.isConstOf ``HAnd.hAnd || fn.isConstOf ``HOr.hOr ||
          fn.isConstOf ``HXor.hXor || fn.isConstOf ``HDiv.hDiv || fn.isConstOf ``HMod.hMod
        if !isArith then
          let wE := ty.appArg!
          ref.modify (·.insert (mkApp2 (mkConst ``BitVec.toNat) wE sub))
    catch _ => pure ()
  ref.get

private meta def injectBitVecBounds (mvar : MVarId) : MetaM MVarId :=
  mvar.withContext do
    let mut toNatTerms : Std.HashSet Lean.Expr := {}
    toNatTerms ← collectToNatArgs (← mvar.getType) toNatTerms
    toNatTerms ← collectBitVecExprs (← mvar.getType) toNatTerms
    for decl in ← getLCtx do
      if !decl.isImplementationDetail then
        if ← isProp decl.type then
          toNatTerms ← collectToNatArgs decl.type toNatTerms
          toNatTerms ← collectBitVecExprs decl.type toNatTerms
        else
          let ty ← whnf decl.type
          if ty.isAppOfArity ``BitVec 1 && !decl.toExpr.hasLooseBVars then
            let wE := ty.appArg!
            toNatTerms := toNatTerms.insert (mkApp2 (mkConst ``BitVec.toNat) wE decl.toExpr)
    let mut cur := mvar
    let mut idx : Nat := 0
    for term in toNatTerms do
      if term.isAppOfArity ``BitVec.toNat 2 then
        let wE := term.appFn!.appArg!
        let xE := term.appArg!
        let boundTy ← mkAppM ``LT.lt #[term, ← mkAppM ``HPow.hPow #[mkNatLit 2, wE]]
        let already ← cur.withContext do
          (← getLCtx).anyM fun d => do
            if d.isImplementationDetail then return false
            withoutModifyingState (isDefEq d.type boundTy)
        if !already then
          let prf := mkApp2 (mkConst ``BitVec.isLt) wE xE
          cur ← cur.assert (Lean.Name.mkSimple s!"_bv_lt_{idx}") boundTy prf
          let (_, cur') ← cur.intro1P
          cur := cur'
          idx := idx + 1
    return cur

/-- Simplify with `@[bv_c0]` at target and all non-dependent hypotheses. -/
elab "c0_bv_simp" : tactic => do
  evalTactic (← `(tactic| try simp only [bv_c0] at *))

private meta def addLocalNumEqs (thms : SimpTheorems) : MetaM SimpTheorems := do
  let mut res := thms
  for decl in ← getLCtx do
    if !decl.isImplementationDetail then
      if let some (_, lhs, rhs) := decl.type.eq? then
        if (← Meta.getNatValue? rhs).isSome && !lhs.hasLooseBVars then
          res ← res.add (.fvar decl.fvarId) #[] decl.toExpr
  return res

private meta def runBvOmegaSimpPass (includeSub : Bool) : TacticM Unit := do
  if (← getGoals).isEmpty then return
  let (g, tail) := match ← getGoals with
    | g :: gs => (g, gs)
    | [] => unreachable!
  let resGoal? ← g.withContext do
    let mut thms ← match (← getSimpExtension? `bv_c0) with
      | some ext => ext.getTheorems
      | none => pure {}
    if !includeSub then
      thms := thms.eraseCore (.decl ``BitVec.toNat_sub)
    for c in [``bv_c0_eq_iff, ``bv_c0_ne_iff, ``bv_c0_lt_iff, ``bv_c0_le_iff,
        ``bv_c0_ult_iff_toNat, ``bv_c0_ule_iff_toNat,
        ``bv_c0_toNat_xor_one_64, ``bv_c0_toNat_xor_one_32, ``bv_c0_toNat_xor_one_8,
        ``Bool.not_eq_true, ``Bool.decide_eq_true, ``Bool.decide_eq_false,
        ``Nat.mul_one, ``Nat.one_mul, ``Nat.add_zero, ``Nat.zero_add, ``Nat.mod_mod] do
      thms ← thms.addConst c
    thms ← addLocalNumEqs thms
    let mut simprocs : Simp.Simprocs := {}
    if let some bvSimpExt ← Simp.getSimprocExtension? `bv_c0 then
      simprocs ← bvSimpExt.getSimprocs
    simprocs ← simprocs.add ``bv_c0_setWidth_toNat false
    simprocs ← simprocs.add ``bv_c0_ofNat_toNat false
    simprocs ← simprocs.add ``c0PowSimproc false
    simprocs ← simprocs.add ``c0SubModSimproc includeSub
    simprocs ← simprocs.add ``c0ModLtSimproc true
    let ctx ← Simp.mkContext
      (config := { failIfUnchanged := false, maxSteps := 100000 })
      (simpTheorems := #[thms])
    let propIds := (← getLCtx).foldl (init := #[]) fun acc d =>
      if !d.isImplementationDetail then acc.push d.fvarId else acc
    let (res?, _) ← simpGoal g ctx #[simprocs] (simplifyTarget := true) (fvarIdsToSimp := propIds)
    return res?
  match resGoal? with
  | none => setGoals tail
  | some (_, g') => setGoals (g' :: tail)

/-- Normalize `BitVec` comparisons, `setWidth`, shifts `<<<`/`>>>`, `OfNat`/`BitVec.ofNat`,
`&&& 1`, and modular arithmetic (`BitVec.toNat_sub_of_le` / `Nat.mod_eq_of_lt`), assert
`BitVec.isLt` bounds, and close via `omega`. Never rewrites `BitVec` `=` globally outside. -/
elab "c0_bv_omega" : tactic => do
  evalTactic (← `(tactic| try (first | rfl | assumption)))
  if (← getGoals).isEmpty then return
  let (g, tail) := match ← getGoals with
    | g :: gs => (g, gs)
    | [] => unreachable!
  let g ← injectBitVecBounds g
  setGoals (g :: tail)
  runBvOmegaSimpPass (includeSub := false)
  if (← getGoals).isEmpty then return
  runBvOmegaSimpPass (includeSub := false)
  if (← getGoals).isEmpty then return
  runBvOmegaSimpPass (includeSub := true)
  if (← getGoals).isEmpty then return
  evalTactic (← `(tactic|
    first
    | rfl
    | assumption
    | omega
    | bv_omega))

/-! ### `state_frame` and `state_frame!` -/

private meta partial def unfoldOnceForFrame? (ty : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let fn := ty.getAppFn
  let some nm := fn.constName? | return none
  if nm == ``wp || nm == ``PrefixAgrees || nm == ``SliceAgrees ||
      nm == ``OutsideSliceAgrees || nm == ``And || nm == ``Eq || nm == ``Exists ||
      nm == ``LE.le || nm == ``LT.lt then
    return none
  let some (.defnInfo _) := (← getEnv).find? nm | return none
  let some unfolded ← unfoldDefinition? ty | return none
  let uFn := unfolded.getAppFn
  let some uNm := uFn.constName? | return none
  let env ← getEnv
  if uNm == ``And || isStructure env uNm || uNm == ``AgreesExcept ||
      uNm == ``PreservesCoreSlice || uNm == ``Eq then
    return some unfolded
  return none

private meta partial def collectPropProj (e ty : Lean.Expr) (depth : Nat)
    (acc : Array (Lean.Expr × Lean.Expr)) : MetaM (Array (Lean.Expr × Lean.Expr)) := do
  let acc0 := acc.push (e, ty)
  if depth == 0 then return acc0
  if ty.isAppOfArity ``And 2 then
    let a := ty.appFn!.appArg!
    let b := ty.appArg!
    let acc1 ← collectPropProj (mkApp3 (.const ``And.left []) a b e) a (depth - 1) acc0
    collectPropProj (mkApp3 (.const ``And.right []) a b e) b (depth - 1) acc1
  else
    let env ← getEnv
    let some structNm := ty.getAppFn.constName? | return acc0
    if isStructure env structNm then
      let mut out := acc0
      for fieldNm in getStructureFields env structNm do
        try
          let pe ← mkProjection e fieldNm
          let pty ← inferType pe
          if ← isProp pty then
            out ← collectPropProj pe pty (depth - 1) out
        catch _ => pure ()
      return out
    else if let some unfolded ← unfoldOnceForFrame? ty then
      collectPropProj e unfolded (depth - 1) acc0
    else
      return acc0

private meta def buildPropProjCache : MetaM (Array (Lean.Expr × Lean.Expr)) := do
  let mut acc : Array (Lean.Expr × Lean.Expr) := #[]
  for decl in ← getLCtx do
    if !decl.isImplementationDetail then
      if ← isProp decl.type then
        acc ← collectPropProj decl.toExpr decl.type 4 acc
  return acc

private meta def tryCloseWithCache (cache : Array (Lean.Expr × Lean.Expr)) (mvar : MVarId) :
    MetaM Bool :=
  mvar.withContext do
    let target ← instantiateMVars (← mvar.getType)
    for (pExpr, pTy) in cache do
      if ← withoutModifyingState (isDefEq pTy target) then
        if ← isDefEq pTy target then
          mvar.assign pExpr
          return true
      if target.eq?.isSome then
        if let some (_, pLhs, pRhs) := pTy.eq? then
          let symmTy ← mkEq pRhs pLhs
          if ← withoutModifyingState (isDefEq symmTy target) then
            if ← isDefEq symmTy target then
              mvar.assign (← mkEqSymm pExpr)
              return true
    return false

private meta def tryCloseFrameLeaf (cache : Array (Lean.Expr × Lean.Expr)) (aggressive : Bool)
    (mvar : MVarId) : TacticM Bool := do
  let saved ← saveState
  setGoals [mvar]
  try
    try
      evalTactic (← `(tactic| rfl))
      if (← getGoals).isEmpty then return true
    catch _ => pure ()
    try
      evalTactic (← `(tactic| trivial))
      if (← getGoals).isEmpty then return true
    catch _ => pure ()
    for g in (← getGoals) do
      if !(← tryCloseWithCache cache g) then
        pure ()
    let rem ← (← getGoals).filterM fun g => return !(← g.isAssigned)
    setGoals rem
    if (← getGoals).isEmpty then return true
    try
      evalTactic (← `(tactic|
        simp (config := { zeta := true, zetaDelta := true }) only
          [List.length_set, List.length_append, List.length_cons, List.length_nil,
           List.length_map, List.length_take, List.length_drop, List.length_replicate,
           LeanQbe.T.AgreesExcept, LeanQbe.T.PreservesCoreSlice]))
    catch _ => pure ()
    try
      evalTactic (← `(tactic|
        first
        | rfl
        | trivial
        | apply LeanQbe.T.AgreesExcept.refl
        | apply LeanQbe.T.PreservesCoreSlice.refl
        | apply LeanQbe.T.PrefixAgrees.refl
        | apply LeanQbe.T.SliceAgrees.refl
        | apply LeanQbe.T.OutsideSliceAgrees.refl))
      if (← getGoals).isEmpty then return true
    catch _ => pure ()
    let mut stillOpen : List MVarId := []
    for g in (← getGoals) do
      if !(← g.isAssigned) then
        if !(← tryCloseWithCache cache g) then
          stillOpen := stillOpen ++ [g]
    setGoals stillOpen
    if stillOpen.isEmpty then return true
    if aggressive then
      try
        evalTactic (← `(tactic| omega))
        if (← getGoals).isEmpty then return true
      catch _ => pure ()
    saved.restore
    return false
  catch _ =>
    saved.restore
    return false

private meta partial def splitFrameGoal (cache : Array (Lean.Expr × Lean.Expr)) (depth : Nat)
    (aggressive : Bool) (mvar : MVarId) : TacticM (List MVarId) := do
  if ← tryCloseFrameLeaf cache aggressive mvar then
    return []
  if depth == 0 then
    return [mvar]
  let target ← mvar.withContext do instantiateMVars (← mvar.getType)
  if target.isAppOfArity ``And 2 then
    setGoals [mvar]
    evalTactic (← `(tactic| apply And.intro))
    let sub ← getGoals
    let mut rem : List MVarId := []
    for g in sub do
      rem := rem ++ (← splitFrameGoal cache (depth - 1) aggressive g)
    return rem
  let env ← getEnv
  if let some structNm := target.getAppFn.constName? then
    if isStructure env structNm && (← mvar.withContext (isProp target)) then
      setGoals [mvar]
      evalTactic (← `(tactic| constructor))
      let sub ← getGoals
      let mut rem : List MVarId := []
      for g in sub do
        rem := rem ++ (← splitFrameGoal cache (depth - 1) aggressive g)
      return rem
  if let some unfolded ← mvar.withContext (unfoldOnceForFrame? target) then
    let mvar' ← mvar.change unfolded
    return ← splitFrameGoal cache (depth - 1) aggressive mvar'
  return [mvar]

private meta def runStateFrame (aggressive : Bool) : TacticM Unit := do
  let (g, tail) := match ← getGoals with
    | g :: gs => (g, gs)
    | [] => unreachable!
  let cache ← g.withContext buildPropProjCache
  let rem ← splitFrameGoal cache 8 aggressive g
  setGoals (rem ++ tail)

/-- Recursively splits `∧` and `Prop`-valued `structure`s (such as `LengthsOk` and
`Preserves*`) and closes preserved field obligations (`{ s with f := v }.g = s.g`,
`List.length_set`, `AgreesExcept`, and projected hypotheses from the local context),
leaving any non-trivial obligations as focused subgoals. -/
elab "state_frame" : tactic => runStateFrame false

/-- Variant of `state_frame` that also invokes `omega` on any remaining numeric leaf
obligations (e.g. index upper bounds). -/
elab "state_frame!" : tactic => runStateFrame true

/-! ## 4. Structured While-State and Array-Cursor Combinators -/

theorem ArrayCursorInv.ofNat_add_one {w : Nat} (k : Nat) :
    BitVec.ofNat w k + (1 : BitVec w) = BitVec.ofNat w (k + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, bv_c0_toNat_ofNat_lit]
  rw [← Nat.add_mod]

theorem ArrayCursorInv.toNat_ofNat_lt {w k : Nat} (hk : k < 2 ^ w) :
    (BitVec.ofNat w k).toNat = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

/-- Alias for `LeanQbe.T.wp_while_state` exported in `ProofKit`. -/
theorem c0_while_state {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    {α : Type _} (proj : α → Tup Val ts) (μ : α → Nat) (Inv : α → Mem 64 → Prop)
    (hentry : ∀ J : Cont ts, (∀ st m', Inv st m' → J (proj st) m') →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) (st : α) (m' : Mem 64), Inv st m' →
      (∀ st' m'', μ st' < μ st → Inv st' m'' → J (proj st') m'') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here (proj st)) m') :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  LeanQbe.T.wp_while_state proj μ Inv hentry hbody

/-- `wp_while_state` with pure invariant `Inv : α → Prop` separated from spatial
separation-logic state `MemPred : α → Mem 64 → Prop` and caller frame `R`. -/
theorem wp_while_state_mem {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    {α : Type _} (proj : α → Tup Val ts) (μ : α → Nat)
    (Inv : α → Prop) (MemPred : α → Mem 64 → Prop) (R : Mem 64 → Prop)
    (hentry : ∀ J : Cont ts,
      (∀ st ml, Inv st → (MemPred st ⋆ R) ml → J (proj st) ml) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) (st : α) (ml : Mem 64),
      Inv st → (MemPred st ⋆ R) ml →
      (∀ st' ml', μ st' < μ st → Inv st' → (MemPred st' ⋆ R) ml' → J (proj st') ml') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here (proj st)) ml) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  LeanQbe.T.wp_while_state proj μ (fun st ml => Inv st ∧ (MemPred st ⋆ R) ml)
    (fun J hJ => hentry J fun st ml hi hm => hJ st ml ⟨hi, hm⟩)
    (fun J st ml ⟨hi, hm⟩ hJ => hbody J st ml hi hm fun st' ml' hlt hi' hm' =>
      hJ st' ml' hlt ⟨hi', hm'⟩)

/-- `wp_while_state` carrying transitive `AgreesExcept mask s₀ (snap st)` and
`(MemPred (snap st) ⋆ R) ml` framing automatically across iterations. -/
theorem wp_while_state_agrees {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    {σ : Type} (mask : σ → σ) (s₀ : σ) (MemPred : σ → Mem 64 → Prop) (R : Mem 64 → Prop)
    {α : Type _} (snap : α → σ) (proj : α → Tup Val ts) (μ : α → Nat) (Inv : α → Prop)
    (hentry : ∀ J : Cont ts,
      (∀ st ml, AgreesExcept mask s₀ (snap st) → Inv st →
        (MemPred (snap st) ⋆ R) ml → J (proj st) ml) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) (st : α) (ml : Mem 64),
      AgreesExcept mask s₀ (snap st) → Inv st → (MemPred (snap st) ⋆ R) ml →
      (∀ st' ml', μ st' < μ st → AgreesExcept mask (snap st) (snap st') → Inv st' →
        (MemPred (snap st') ⋆ R) ml' → J (proj st') ml') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here (proj st)) ml) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  LeanQbe.T.wp_while_state proj μ
    (fun st ml => AgreesExcept mask s₀ (snap st) ∧ Inv st ∧ (MemPred (snap st) ⋆ R) ml)
    (fun J hJ => hentry J fun st ml hag hi hm => hJ st ml ⟨hag, hi, hm⟩)
    (fun J st ml ⟨hag, hi, hm⟩ hJ =>
      hbody J st ml hag hi hm fun st' ml' hlt hstep hi' hm' =>
        hJ st' ml' hlt ⟨AgreesExcept.trans hag hstep, hi', hm'⟩)

/-! ### `ArrayCursorInv` and `ArrayMutCursorInv` combinators -/

namespace ArrayCursorInv

theorem init {β : Type} {α : Type _} {lo hi : Nat} {xs : List β}
    {Inv : Nat → α → Prop} {st : α}
    (hle : lo ≤ hi) (hi_len : hi ≤ xs.length) (hinv : Inv lo st) :
    ArrayCursorInv lo hi xs Inv lo st :=
  ⟨Nat.le_refl lo, hle, hi_len, hinv⟩

theorem step {β : Type} {α : Type _} {lo hi idx : Nat} {xs : List β}
    {Inv : Nat → α → Prop} {st st' : α}
    (h : ArrayCursorInv lo hi xs Inv idx st) (hlt : idx < hi) (hinv : Inv (idx + 1) st') :
    ArrayCursorInv lo hi xs Inv (idx + 1) st' :=
  ⟨Nat.le_trans h.lo_le (Nat.le_succ idx), hlt, h.hi_le, hinv⟩

theorem idx_lt_length {β : Type} {α : Type _} {lo hi idx : Nat} {xs : List β}
    {Inv : Nat → α → Prop} {st : α}
    (h : ArrayCursorInv lo hi xs Inv idx st) (hlt : idx < hi) : idx < xs.length :=
  Nat.lt_of_lt_of_le hlt h.hi_le

theorem done {β : Type} {α : Type _} {lo hi idx : Nat} {xs : List β}
    {Inv : Nat → α → Prop} {st : α}
    (h : ArrayCursorInv lo hi xs Inv idx st) (hne : ¬ idx < hi) :
    idx = hi ∧ Inv hi st := by
  have heq : idx = hi := Nat.le_antisymm h.idx_le (Nat.not_lt.mp hne)
  subst heq
  exact ⟨rfl, h.inv⟩

end ArrayCursorInv

namespace ArrayMutCursorInv

theorem init {β : Type} {α : Type _} {lo hi : Nat} {xs₀ : List β}
    {Inv : Nat → List β → α → Prop} {st : α}
    (hle : lo ≤ hi) (hi_len : hi ≤ xs₀.length) (hinv : Inv lo xs₀ st) :
    ArrayMutCursorInv lo hi xs₀ Inv lo xs₀ st :=
  ⟨Nat.le_refl lo, hle, hi_len, rfl, OutsideSliceAgrees.refl lo lo xs₀, hinv⟩

theorem step_set {β : Type} {α : Type _} {lo hi idx : Nat} {xs₀ xs : List β}
    {Inv : Nat → List β → α → Prop} {st st' : α}
    (h : ArrayMutCursorInv lo hi xs₀ Inv idx xs st) (hlt : idx < hi) (v : β)
    (hinv : Inv (idx + 1) (xs.set idx v) st') :
    ArrayMutCursorInv lo hi xs₀ Inv (idx + 1) (xs.set idx v) st' := by
  have hmono : OutsideSliceAgrees lo (idx + 1) xs₀ xs :=
    h.outside_eq.mono (Nat.le_refl lo) (Nat.le_succ idx)
  refine ⟨Nat.le_trans h.lo_le (Nat.le_succ idx), hlt, h.hi_le, ?_, ?_, hinv⟩
  · simpa [List.length_set] using h.len_eq
  · exact hmono.update_set v h.lo_le (Nat.lt_succ_self idx)

theorem step_skip {β : Type} {α : Type _} {lo hi idx : Nat} {xs₀ xs : List β}
    {Inv : Nat → List β → α → Prop} {st st' : α}
    (h : ArrayMutCursorInv lo hi xs₀ Inv idx xs st) (hlt : idx < hi)
    (hinv : Inv (idx + 1) xs st') :
    ArrayMutCursorInv lo hi xs₀ Inv (idx + 1) xs st' :=
  ⟨Nat.le_trans h.lo_le (Nat.le_succ idx), hlt, h.hi_le, h.len_eq,
    h.outside_eq.mono (Nat.le_refl lo) (Nat.le_succ idx), hinv⟩

theorem idx_lt_length {β : Type} {α : Type _} {lo hi idx : Nat} {xs₀ xs : List β}
    {Inv : Nat → List β → α → Prop} {st : α}
    (h : ArrayMutCursorInv lo hi xs₀ Inv idx xs st) (hlt : idx < hi) : idx < xs.length := by
  rw [h.len_eq]
  exact Nat.lt_of_lt_of_le hlt h.hi_le

theorem get_unwritten {β : Type} {α : Type _} {lo hi idx : Nat} {xs₀ xs : List β}
    {Inv : Nat → List β → α → Prop} {st : α}
    (h : ArrayMutCursorInv lo hi xs₀ Inv idx xs st) {k : Nat} (hk : idx ≤ k) :
    xs[k]? = xs₀[k]? :=
  h.outside_eq.getElem?_ge hk

theorem prefix_eq {β : Type} {α : Type _} {lo hi idx : Nat} {xs₀ xs : List β}
    {Inv : Nat → List β → α → Prop} {st : α}
    (h : ArrayMutCursorInv lo hi xs₀ Inv idx xs st) :
    PrefixAgrees lo xs₀ xs :=
  h.outside_eq.to_prefix

theorem done {β : Type} {α : Type _} {lo hi idx : Nat} {xs₀ xs : List β}
    {Inv : Nat → List β → α → Prop} {st : α}
    (h : ArrayMutCursorInv lo hi xs₀ Inv idx xs st) (hne : ¬ idx < hi) :
    idx = hi ∧ xs.length = xs₀.length ∧ OutsideSliceAgrees lo hi xs₀ xs ∧ Inv hi xs st := by
  have heq : idx = hi := Nat.le_antisymm h.idx_le (Nat.not_lt.mp hne)
  subst heq
  exact ⟨rfl, h.len_eq, h.outside_eq, h.inv⟩

end ArrayMutCursorInv

/-- Read-only 64-bit array-cursor loop rule (`i64 :: tsRest`), managing index bounds
`ArrayCursorInv lo hi xs Inv idx st` and decreasing measure `hi - idx`. -/
theorem wp_while_cursor64 {Γ : Env} {rs tsRest : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64}
    {bodies : Tup Cont [i64 :: tsRest] → Blocks Val Cont rs [i64 :: tsRest]}
    {entry : Tup Cont [i64 :: tsRest] → Expr Val Cont rs}
    {β : Type} {α : Type _} (lo hi : Nat) (xs : List β) (proj : α → Tup Val tsRest)
    (Inv : Nat → α → Prop) (MemPred : Nat → α → Mem 64 → Prop) (R : Mem 64 → Prop)
    (hentry : ∀ J : Cont (i64 :: tsRest),
      (∀ idx st ml, ArrayCursorInv lo hi xs Inv idx st → (MemPred idx st ⋆ R) ml →
        J (BitVec.ofNat 64 idx, proj st) ml) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont (i64 :: tsRest)) (idx : Nat) (st : α) (ml : Mem 64),
      ArrayCursorInv lo hi xs Inv idx st → (MemPred idx st ⋆ R) ml →
      (∀ idx' st' ml', hi - idx' < hi - idx → ArrayCursorInv lo hi xs Inv idx' st' →
        (MemPred idx' st' ⋆ R) ml' → J (BitVec.ofNat 64 idx', proj st') ml') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here (BitVec.ofNat 64 idx, proj st)) ml) :
    wp Γ Q X (.group (sig := [i64 :: tsRest]) bodies entry) m :=
  LeanQbe.T.wp_while_state
    (α := Nat × α)
    (fun p => (BitVec.ofNat 64 p.1, proj p.2))
    (fun p => hi - p.1)
    (fun p ml => ArrayCursorInv lo hi xs Inv p.1 p.2 ∧ (MemPred p.1 p.2 ⋆ R) ml)
    (fun J hJ => hentry J fun idx st ml hinv hm => hJ (idx, st) ml ⟨hinv, hm⟩)
    (fun J ⟨idx, st⟩ ml ⟨hinv, hm⟩ hJ =>
      hbody J idx st ml hinv hm fun idx' st' ml' hlt hinv' hm' =>
        hJ (idx', st') ml' hlt ⟨hinv', hm'⟩)

/-- Read-only 32-bit array-cursor loop rule (`i32 :: tsRest`), managing index bounds
`ArrayCursorInv lo hi xs Inv idx st` and decreasing measure `hi - idx`. -/
theorem wp_while_cursor32 {Γ : Env} {rs tsRest : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64}
    {bodies : Tup Cont [i32 :: tsRest] → Blocks Val Cont rs [i32 :: tsRest]}
    {entry : Tup Cont [i32 :: tsRest] → Expr Val Cont rs}
    {β : Type} {α : Type _} (lo hi : Nat) (xs : List β) (proj : α → Tup Val tsRest)
    (Inv : Nat → α → Prop) (MemPred : Nat → α → Mem 64 → Prop) (R : Mem 64 → Prop)
    (hentry : ∀ J : Cont (i32 :: tsRest),
      (∀ idx st ml, ArrayCursorInv lo hi xs Inv idx st → (MemPred idx st ⋆ R) ml →
        J (BitVec.ofNat 32 idx, proj st) ml) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont (i32 :: tsRest)) (idx : Nat) (st : α) (ml : Mem 64),
      ArrayCursorInv lo hi xs Inv idx st → (MemPred idx st ⋆ R) ml →
      (∀ idx' st' ml', hi - idx' < hi - idx → ArrayCursorInv lo hi xs Inv idx' st' →
        (MemPred idx' st' ⋆ R) ml' → J (BitVec.ofNat 32 idx', proj st') ml') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here (BitVec.ofNat 32 idx, proj st)) ml) :
    wp Γ Q X (.group (sig := [i32 :: tsRest]) bodies entry) m :=
  LeanQbe.T.wp_while_state
    (α := Nat × α)
    (fun p => (BitVec.ofNat 32 p.1, proj p.2))
    (fun p => hi - p.1)
    (fun p ml => ArrayCursorInv lo hi xs Inv p.1 p.2 ∧ (MemPred p.1 p.2 ⋆ R) ml)
    (fun J hJ => hentry J fun idx st ml hinv hm => hJ (idx, st) ml ⟨hinv, hm⟩)
    (fun J ⟨idx, st⟩ ml ⟨hinv, hm⟩ hJ =>
      hbody J idx st ml hinv hm fun idx' st' ml' hlt hinv' hm' =>
        hJ (idx', st') ml' hlt ⟨hinv', hm'⟩)

/-- Mutating 64-bit array-cursor loop rule (`i64 :: tsRest`) carrying `ArrayMutCursorInv`
(length preservation and `OutsideSliceAgrees lo idx xs₀ xs`) and separated memory
predicate `MemPred idx xs st ⋆ R`. -/
theorem wp_while_mut_cursor64 {Γ : Env} {rs tsRest : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64}
    {bodies : Tup Cont [i64 :: tsRest] → Blocks Val Cont rs [i64 :: tsRest]}
    {entry : Tup Cont [i64 :: tsRest] → Expr Val Cont rs}
    {β : Type} {α : Type _} (lo hi : Nat) (xs₀ : List β) (proj : α → Tup Val tsRest)
    (Inv : Nat → List β → α → Prop) (MemPred : Nat → List β → α → Mem 64 → Prop)
    (R : Mem 64 → Prop)
    (hentry : ∀ J : Cont (i64 :: tsRest),
      (∀ idx xs st ml, ArrayMutCursorInv lo hi xs₀ Inv idx xs st →
        (MemPred idx xs st ⋆ R) ml → J (BitVec.ofNat 64 idx, proj st) ml) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont (i64 :: tsRest)) (idx : Nat) (xs : List β) (st : α) (ml : Mem 64),
      ArrayMutCursorInv lo hi xs₀ Inv idx xs st → (MemPred idx xs st ⋆ R) ml →
      (∀ idx' xs' st' ml', hi - idx' < hi - idx →
        ArrayMutCursorInv lo hi xs₀ Inv idx' xs' st' → (MemPred idx' xs' st' ⋆ R) ml' →
        J (BitVec.ofNat 64 idx', proj st') ml') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here (BitVec.ofNat 64 idx, proj st)) ml) :
    wp Γ Q X (.group (sig := [i64 :: tsRest]) bodies entry) m :=
  LeanQbe.T.wp_while_state
    (α := Nat × List β × α)
    (fun p => (BitVec.ofNat 64 p.1, proj p.2.2))
    (fun p => hi - p.1)
    (fun p ml => ArrayMutCursorInv lo hi xs₀ Inv p.1 p.2.1 p.2.2 ∧
      (MemPred p.1 p.2.1 p.2.2 ⋆ R) ml)
    (fun J hJ => hentry J fun idx xs st ml hinv hm => hJ (idx, xs, st) ml ⟨hinv, hm⟩)
    (fun J ⟨idx, xs, st⟩ ml ⟨hinv, hm⟩ hJ =>
      hbody J idx xs st ml hinv hm fun idx' xs' st' ml' hlt hinv' hm' =>
        hJ (idx', xs', st') ml' hlt ⟨hinv', hm'⟩)

section AxiomAudit
open Lean Elab Command

/-- Compile-time check that every listed declaration uses only `[propext, Classical.choice, Quot.sound]`. -/
syntax "check_std_axioms! " ident+ : command

elab_rules : command
  | `(check_std_axioms! $ids:ident*) => do
    let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
    for id in ids do
      let nm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
      let axs ← liftCoreM <| Lean.collectAxioms nm
      let bad := axs.filter (!allowed.contains ·)
      if !bad.isEmpty then
        throwError "check_std_axioms!: `{nm}` depends on disallowed axioms: {bad.toList}"

end AxiomAudit

end

end LeanQbe.T.ProofKit
