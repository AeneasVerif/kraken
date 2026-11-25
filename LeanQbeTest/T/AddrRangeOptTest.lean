module

public import LeanQbe.T.AddrRangeOptLemmas
public import LeanQbe.T.OptLemmas
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Logic.Rules
meta import LeanQbe.T.AddrRangeOpt
meta import LeanQbe.T.Opt

/-!
# Architecture-Neutral Tests of `LeanQbe.T.AddrRangeOpt` (`Func.addrRangeOpt`)

Verifies both `#3` (loop-aware address reassociation before `Licm`) and `#1c` (signed and
unsigned range-check collapse) at the typed-IR level:
1. Loop-aware reassociation rewrites `base + ((inv + iv) << s)`, commutative
   `base + ((zext(iv) + zext(inv)) << s)`, `base + ((iv - inv) << s)`, unshifted `base + (inv + iv)`,
   and displaced `base + (((inv + iv) << s) + disp)` so `Func.licm` / `Func.lateOpt` hoists the
   invariant base term out of the loop and `Func.dceP` drops the dead inner arithmetic.
2. Negative guards: constant offsets `base + ((iv + 3) << 2)` and same-depth sums
   `base + ((inv₁ + inv₂) << 2)` or `base + ((iv₁ + iv₂) << 2)` are never split unnecessarily.
3. Range-check collapse rewrites `(lo ≤s x && x <s hi)` / `(lo ≤u x && x <u hi)` → `(x - lo) <u (hi - lo)`,
   dual `or` forms `(x < lo || hi ≤ x)` → `(x - lo) ≥u (hi - lo)`, non-strict `<`/`≤`/`>`,
   zero-lower-bound fast path (`0 ≤ x && x < hi` → `x <u hi`), and empty/tautological ranges.
4. Relational well-formedness (`Func.addrRangeOpt_wf`, `Func.lateOpt_wf`), WP refinement proofs
   (`Func.addrRangeOpt_spec`, `Func.lateOpt_spec`), and strict `[propext, Classical.choice, Quot.sound]`
   axiom audit.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.AddrRangeOptTest

open LeanQbe.T

/-! ## Helpers -/

mutual
def countLoopLets (inLoop : Bool) {rs : List Ty} : TFlat rs → Nat
  | .let_ _ k => (if inLoop then 1 else 0) + countLoopLets inLoop k
  | .load _ _ k | .store _ _ k | .call _ _ _ k => countLoopLets inLoop k
  | .jnz _ t e => countLoopLets inLoop t + countLoopLets inLoop e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => 0
  | .group bodies k =>
    let isLp := !(Licm.computeLoopMask bodies).isEmpty
    countLoopLetsB (inLoop || isLp) bodies + countLoopLets inLoop k

def countLoopLetsB (inLoop : Bool) {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → Nat
  | _, .nil => 0
  | _, .cons b bs => countLoopLets inLoop b + countLoopLetsB inLoop bs
end

def funcLoopLets {as rs : List Ty} (f : Func as rs) : Nat :=
  countLoopLets false (reifyFunc f)

mutual
def countOuterLets {rs : List Ty} : TFlat rs → Nat
  | .let_ _ k => 1 + countOuterLets k
  | .load _ _ k | .store _ _ k | .call _ _ _ k => countOuterLets k
  | .jnz _ t e => countOuterLets t + countOuterLets e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => 0
  | .group _ k => countOuterLets k
end

def funcOuterLets {as rs : List Ty} (f : Func as rs) : Nat :=
  countOuterLets (reifyFunc f)

def isAndOrBoolCode : {as rs : List Ty} → OpCode as rs → Bool
  | _, _, .and .bool | _, _, .or .bool => true
  | _, _, _ => false

mutual
def hasAndOrBool {rs : List Ty} : TFlat rs → Bool
  | .let_ op k => isAndOrBoolCode op.code || hasAndOrBool k
  | .load _ _ k | .store _ _ k | .call _ _ _ k => hasAndOrBool k
  | .jnz _ t e => hasAndOrBool t || hasAndOrBool e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => false
  | .group bodies k => hasAndOrBoolB bodies || hasAndOrBool k

def hasAndOrBoolB {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Bool
  | _, .nil => false
  | _, .cons b bs => hasAndOrBool b || hasAndOrBoolB bs
end

def funcHasAndOrBool {as rs : List Ty} (f : Func as rs) : Bool :=
  hasAndOrBool (reifyFunc f)

/-! ## 1. Loop-Aware Address Reassociation (`#3`) -/

/-- `base + ((inv + iv) << 2)` inside a loop: `addrRangeOpt` reassociates to
`(base + (inv << 2)) + (iv << 2)`, letting `Licm` hoist `base + (inv << 2)` out of the loop. -/
def addrShlAddLoop : Func [i64, i64, i64] [i64] := fun _ _ (base, inv, n, ()) =>
  loop1 (ts := [i64, i64])
    (fun lp (iv, acc, ()) =>
      .let_ (op2 (.cmp .eq i64) (.var iv) (.var n)) fun (done, ()) =>
      .jnz (.var done) (.ret (.var acc, ()))
        (.let_ (op2 (.add i64) (.var inv) (.var iv)) fun (idx, ()) =>
         .let_ (op2 (.shl i64) (.var idx) (.imm 2)) fun (off, ()) =>
         .let_ (op2 (.add i64) (.var base) (.var off)) fun (ptr, ()) =>
         .load i32 (.var ptr) fun w =>
         .let_ (op1 (.zext 32 64) (.var w)) fun (w64, ()) =>
         .let_ (op2 (.add i64) (.var acc) (.var w64)) fun (acc', ()) =>
         .let_ (op2 (.add i64) (.var iv) (.imm 1)) fun (iv', ()) =>
         .jump lp (.var iv', .var acc', ())))
    (fun lp => .jump lp (.imm 0, .imm 0, ()))

theorem addrShlAddLoop_addrRangeOpt_out : Func.addrRangeOpt addrShlAddLoop =
    fun _ _ (base, inv, n, ()) =>
      loop1 (ts := [i64, i64])
        (fun lp (iv, acc, ()) =>
          .let_ (op2 (.cmp .eq i64) (.var iv) (.var n)) fun (done, ()) =>
          .jnz (.var done) (.ret (.var acc, ()))
            (.let_ (op2 (.add i64) (.var inv) (.var iv)) fun (idx, ()) =>
             .let_ (op2 (.shl i64) (.var idx) (.imm 2)) fun (_off, ()) =>
             .let_ (op2 (.shl i64) (.var inv) (.imm 2)) fun (invSh, ()) =>
             .let_ (op2 (.add i64) (.var base) (.var invSh)) fun (hbase, ()) =>
             .let_ (op2 (.shl i64) (.var iv) (.imm 2)) fun (ivSh, ()) =>
             .let_ (op2 (.add i64) (.var hbase) (.var ivSh)) fun (ptr, ()) =>
             .load i32 (.var ptr) fun w =>
             .let_ (op1 (.zext 32 64) (.var w)) fun (w64, ()) =>
             .let_ (op2 (.add i64) (.var acc) (.var w64)) fun (acc', ()) =>
             .let_ (op2 (.add i64) (.var iv) (.imm 1)) fun (iv', ()) =>
             .jump lp (.var iv', .var acc', ())))
        (fun lp => .jump lp (.imm 0, .imm 0, ())) := by
  t_kernel_rfl

-- After `lateCfg` (`Licm` + `DceParam`) and `lateOpt`, `inv << 2` and `base + (inv << 2)` hoist out!
#guard funcOuterLets (Func.lateCfg addrShlAddLoop) == 2
#guard funcLoopLets (Func.lateOpt addrShlAddLoop) < funcLoopLets addrShlAddLoop

/-- Commutative & `zext32` variant matching `full_has_ternary` / `full_sweep_copy`:
`base + ((zext(iv) + zext(inv)) << 2)`. `zext(inv)` keeps depth `0` via `isLicmPure`. -/
def addrShlAddCommZextLoop : Func [i64, i32, i32] [i64] := fun _ _ (base, inv, n, ()) =>
  loop1 (ts := [i32, i64])
    (fun lp (iv, acc, ()) =>
      .let_ (op2 (.cmp .eq i32) (.var iv) (.var n)) fun (done, ()) =>
      .jnz (.var done) (.ret (.var acc, ()))
        (.let_ (op1 (.zext 32 64) (.var iv)) fun (iv64, ()) =>
         .let_ (op1 (.zext 32 64) (.var inv)) fun (inv64, ()) =>
         .let_ (op2 (.add i64) (.var iv64) (.var inv64)) fun (idx, ()) =>
         .let_ (op2 (.shl i64) (.var idx) (.imm 2)) fun (off, ()) =>
         .let_ (op2 (.add i64) (.var base) (.var off)) fun (ptr, ()) =>
         .load i32 (.var ptr) fun w =>
         .let_ (op1 (.zext 32 64) (.var w)) fun (w64, ()) =>
         .let_ (op2 (.add i64) (.var acc) (.var w64)) fun (acc', ()) =>
         .let_ (op2 (.add i32) (.var iv) (.imm 1)) fun (iv', ()) =>
         .jump lp (.var iv', .var acc', ())))
    (fun lp => .jump lp (.imm 0, .imm 0, ()))

-- All 3 invariant ops (`zext inv`, `<< 2`, `base + ...`) hoist outside the loop!
#guard funcOuterLets (Func.lateCfg addrShlAddCommZextLoop) == 3
#guard funcLoopLets (Func.lateOpt addrShlAddCommZextLoop) < funcLoopLets addrShlAddCommZextLoop

/-- Subtract variant `base + ((iv - inv) << 2)`: hoists `inv << 2` and `base - (inv << 2)`. -/
def addrShlSubLoop : Func [i64, i64, i64] [i64] := fun _ _ (base, inv, n, ()) =>
  loop1 (ts := [i64, i64])
    (fun lp (iv, acc, ()) =>
      .let_ (op2 (.cmp .eq i64) (.var iv) (.var n)) fun (done, ()) =>
      .jnz (.var done) (.ret (.var acc, ()))
        (.let_ (op2 (.sub i64) (.var iv) (.var inv)) fun (idx, ()) =>
         .let_ (op2 (.shl i64) (.var idx) (.imm 2)) fun (off, ()) =>
         .let_ (op2 (.add i64) (.var base) (.var off)) fun (ptr, ()) =>
         .load i32 (.var ptr) fun w =>
         .let_ (op1 (.zext 32 64) (.var w)) fun (w64, ()) =>
         .let_ (op2 (.add i64) (.var acc) (.var w64)) fun (acc', ()) =>
         .let_ (op2 (.add i64) (.var iv) (.imm 1)) fun (iv', ()) =>
         .jump lp (.var iv', .var acc', ())))
    (fun lp => .jump lp (.imm 0, .imm 0, ()))

#guard funcOuterLets (Func.lateCfg addrShlSubLoop) == 2
#guard funcLoopLets (Func.lateOpt addrShlSubLoop) < funcLoopLets addrShlSubLoop

/-- Unshifted `base + (inv + iv)` byte-indexed loop: hoists `base + inv`. -/
def addrPlainLoop : Func [i64, i64, i64] [i64] := fun _ _ (base, inv, n, ()) =>
  loop1 (ts := [i64, i64])
    (fun lp (iv, acc, ()) =>
      .let_ (op2 (.cmp .eq i64) (.var iv) (.var n)) fun (done, ()) =>
      .jnz (.var done) (.ret (.var acc, ()))
        (.let_ (op2 (.add i64) (.var inv) (.var iv)) fun (idx, ()) =>
         .let_ (op2 (.add i64) (.var base) (.var idx)) fun (ptr, ()) =>
         .load i8 (.var ptr) fun b =>
         .let_ (op1 (.zext 8 64) (.var b)) fun (b64, ()) =>
         .let_ (op2 (.add i64) (.var acc) (.var b64)) fun (acc', ()) =>
         .let_ (op2 (.add i64) (.var iv) (.imm 1)) fun (iv', ()) =>
         .jump lp (.var iv', .var acc', ())))
    (fun lp => .jump lp (.imm 0, .imm 0, ()))

#guard funcOuterLets (Func.lateCfg addrPlainLoop) == 1
#guard funcLoopLets (Func.lateOpt addrPlainLoop) < funcLoopLets addrPlainLoop

/-- Displaced `base + (((inv + iv) << 2) + 8)`: preserves `+ 8` while hoisting `base + (inv << 2)`. -/
def addrShlAddDispLoop : Func [i64, i64, i64] [i64] := fun _ _ (base, inv, n, ()) =>
  loop1 (ts := [i64, i64])
    (fun lp (iv, acc, ()) =>
      .let_ (op2 (.cmp .eq i64) (.var iv) (.var n)) fun (done, ()) =>
      .jnz (.var done) (.ret (.var acc, ()))
        (.let_ (op2 (.add i64) (.var inv) (.var iv)) fun (idx, ()) =>
         .let_ (op2 (.shl i64) (.var idx) (.imm 2)) fun (sh, ()) =>
         .let_ (op2 (.add i64) (.var sh) (.imm 8)) fun (off, ()) =>
         .let_ (op2 (.add i64) (.var base) (.var off)) fun (ptr, ()) =>
         .load i32 (.var ptr) fun w =>
         .let_ (op1 (.zext 32 64) (.var w)) fun (w64, ()) =>
         .let_ (op2 (.add i64) (.var acc) (.var w64)) fun (acc', ()) =>
         .let_ (op2 (.add i64) (.var iv) (.imm 1)) fun (iv', ()) =>
         .jump lp (.var iv', .var acc', ())))
    (fun lp => .jump lp (.imm 0, .imm 0, ()))

#guard funcOuterLets (Func.lateCfg addrShlAddDispLoop) == 2
#guard funcLoopLets (Func.lateOpt addrShlAddDispLoop) < funcLoopLets addrShlAddDispLoop

/-- Negative guard: constant offset `base + ((iv + 3) << 2)` is NOT split so hardware `[b + i*4 + 12]`
stays intact without burning extra base registers. -/
def constOffsetLoop : Func [i64, i64] [i64] := fun _ _ (base, n, ()) =>
  loop1 (ts := [i64, i64])
    (fun lp (iv, acc, ()) =>
      .let_ (op2 (.cmp .eq i64) (.var iv) (.var n)) fun (done, ()) =>
      .jnz (.var done) (.ret (.var acc, ()))
        (.let_ (op2 (.add i64) (.var iv) (.imm 3)) fun (idx, ()) =>
         .let_ (op2 (.shl i64) (.var idx) (.imm 2)) fun (off, ()) =>
         .let_ (op2 (.add i64) (.var base) (.var off)) fun (ptr, ()) =>
         .load i32 (.var ptr) fun w =>
         .let_ (op1 (.zext 32 64) (.var w)) fun (w64, ()) =>
         .let_ (op2 (.add i64) (.var acc) (.var w64)) fun (acc', ()) =>
         .let_ (op2 (.add i64) (.var iv) (.imm 1)) fun (iv', ()) =>
         .jump lp (.var iv', .var acc', ())))
    (fun lp => .jump lp (.imm 0, .imm 0, ()))

theorem constOffsetLoop_addrRangeOpt_unchanged :
    Func.addrRangeOpt constOffsetLoop = constOffsetLoop := by
  t_kernel_rfl

/-- Negative guard: equal-depth variables `inv₁ + inv₂` inside `shl` are not reassociated. -/
def sameDepthLoop : Func [i64, i64, i64, i64] [i64] := fun _ _ (base, a, b, n, ()) =>
  loop1 (ts := [i64, i64])
    (fun lp (iv, acc, ()) =>
      .let_ (op2 (.cmp .eq i64) (.var iv) (.var n)) fun (done, ()) =>
      .jnz (.var done) (.ret (.var acc, ()))
        (.let_ (op2 (.add i64) (.var iv) (.var b)) fun (ivb, ()) =>
         .let_ (op2 (.add i64) (.var ivb) (.var iv)) fun (idx, ()) =>
         .let_ (op2 (.shl i64) (.var idx) (.imm 2)) fun (off, ()) =>
         .let_ (op2 (.add i64) (.var base) (.var off)) fun (ptr, ()) =>
         .let_ (op2 (.add i64) (.var ptr) (.var a)) fun (ptr', ()) =>
         .load i32 (.var ptr') fun w =>
         .let_ (op1 (.zext 32 64) (.var w)) fun (w64, ()) =>
         .let_ (op2 (.add i64) (.var acc) (.var w64)) fun (acc', ()) =>
         .let_ (op2 (.add i64) (.var iv) (.imm 1)) fun (iv', ()) =>
         .jump lp (.var iv', .var acc', ())))
    (fun lp => .jump lp (.imm 0, .imm 0, ()))

#guard funcOuterLets (Func.addrRangeOpt sameDepthLoop) == 0

/-! ## 2. Signed & Unsigned Range-Check Collapse (`#1c`) -/

/-- ASCII digit check matching `full_ingest_cl`: `0x30 <=s x && x <s 0x3a` → `(x - 0x30) <u 10`. -/
def signedDigitRangeFn : Func [i8] [.bool] := fun _ _ (x, ()) =>
  .let_ (op2 (.cmp .sge i8) (.var x) (.imm 0x30#8)) fun (c1, ()) =>
  .let_ (op2 (.cmp .slt i8) (.var x) (.imm 0x3a#8)) fun (c2, ()) =>
  .let_ (op2 (.and .bool) (.var c1) (.var c2)) fun (r, ()) =>
  .ret (.var r, ())

theorem signedDigitRangeFn_addrRangeOpt_out : Func.addrRangeOpt signedDigitRangeFn =
    fun _ _ (x, ()) =>
      .let_ (op2 (.cmp .sge i8) (.var x) (.imm 0x30#8)) fun (_, ()) =>
      .let_ (op2 (.cmp .slt i8) (.var x) (.imm 0x3a#8)) fun (_, ()) =>
      .let_ (op2 (.sub i8) (.var x) (.imm 0x30#8)) fun (t, ()) =>
      .let_ (op2 (.cmp .ult i8) (.var t) (.imm 10#8)) fun (r, ()) =>
      .ret (.var r, ()) := by
  t_kernel_rfl

#guard funcHasAndOrBool (Func.lateOpt signedDigitRangeFn) == false

/-- Non-strict signed interval `(-5 <s x && x <=s 10)` → `(-4 <=s x && x <s 11)` → `(x - (-4)) <u 15`. -/
def nonStrictSignedAndFn : Func [i32] [.bool] := fun _ _ (x, ()) =>
  .let_ (op2 (.cmp .sgt i32) (.var x) (.imm (-5#32))) fun (c1, ()) =>
  .let_ (op2 (.cmp .sle i32) (.var x) (.imm 10#32)) fun (c2, ()) =>
  .let_ (op2 (.and .bool) (.var c1) (.var c2)) fun (r, ()) =>
  .ret (.var r, ())

#guard funcHasAndOrBool (Func.lateOpt nonStrictSignedAndFn) == false

/-- Dual unsigned outside-range check `(x <u 10 || x >=u 20)` → `(x - 10) >=u 10`. -/
def unsignedOrRangeFn : Func [i32] [.bool] := fun _ _ (x, ()) =>
  .let_ (op2 (.cmp .ult i32) (.var x) (.imm 10#32)) fun (c1, ()) =>
  .let_ (op2 (.cmp .uge i32) (.var x) (.imm 20#32)) fun (c2, ()) =>
  .let_ (op2 (.or .bool) (.var c1) (.var c2)) fun (r, ()) =>
  .ret (.var r, ())

theorem unsignedOrRangeFn_lateOpt_out : Func.lateOpt unsignedOrRangeFn =
    fun _ _ (x, ()) =>
      .let_ (op2 (.sub i32) (.var x) (.imm 10#32)) fun (t, ()) =>
      .let_ (op2 (.cmp .uge i32) (.var t) (.imm 10#32)) fun (r, ()) =>
      .ret (.var r, ()) := by
  t_kernel_rfl

/-- Zero-lower-bound fast path `(0 <=s x && x <s 64)` collapses to a single `x <u 64` compare. -/
def zeroLoSignedRangeFn : Func [i32] [.bool] := fun _ _ (x, ()) =>
  .let_ (op2 (.cmp .sge i32) (.var x) (.imm 0#32)) fun (c1, ()) =>
  .let_ (op2 (.cmp .slt i32) (.var x) (.imm 64#32)) fun (c2, ()) =>
  .let_ (op2 (.and .bool) (.var c1) (.var c2)) fun (r, ()) =>
  .ret (.var r, ())

theorem zeroLoSignedRangeFn_lateOpt_out : Func.lateOpt zeroLoSignedRangeFn =
    fun _ _ (x, ()) =>
      .let_ (op2 (.cmp .ult i32) (.var x) (.imm 64#32)) fun (r, ()) =>
      .ret (.var r, ()) := by
  t_kernel_rfl

/-- Empty signed `and` (`10 <=s x && x <s 5`) and tautological `or` (`x <u 10 || 5 <=u x`) fold to
constants. -/
def emptyRangeFn : Func [i32] [.bool] := fun _ _ (x, ()) =>
  .let_ (op2 (.cmp .sge i32) (.var x) (.imm 10#32)) fun (c1, ()) =>
  .let_ (op2 (.cmp .slt i32) (.var x) (.imm 5#32)) fun (c2, ()) =>
  .let_ (op2 (.and .bool) (.var c1) (.var c2)) fun (r, ()) =>
  .ret (.var r, ())

def tautOrRangeFn : Func [i32] [.bool] := fun _ _ (x, ()) =>
  .let_ (op2 (.cmp .ult i32) (.var x) (.imm 10#32)) fun (c1, ()) =>
  .let_ (op2 (.cmp .uge i32) (.var x) (.imm 5#32)) fun (c2, ()) =>
  .let_ (op2 (.or .bool) (.var c1) (.var c2)) fun (r, ()) =>
  .ret (.var r, ())

theorem emptyRangeFn_lateOpt_out : Func.lateOpt emptyRangeFn = fun _ _ _ => .ret (.imm false, ()) := by
  t_kernel_rfl

theorem tautOrRangeFn_lateOpt_out : Func.lateOpt tautOrRangeFn = fun _ _ _ => .ret (.imm true, ()) := by
  t_kernel_rfl

/-! ## 3. Verified Well-Formedness & WP Refinement Specs -/

theorem addrShlAddLoop_wf : addrShlAddLoop.Wf := by t_wf_reify
theorem addrShlAddLoop_lateOpt_wf : (Func.lateOpt addrShlAddLoop).Wf :=
  Func.lateOpt_wf addrShlAddLoop_wf

theorem signedDigitRangeFn_wf : signedDigitRangeFn.Wf := by t_wf_reify
theorem unsignedOrRangeFn_wf : unsignedOrRangeFn.Wf := by t_wf_reify
theorem zeroLoSignedRangeFn_wf : zeroLoSignedRangeFn.Wf := by t_wf_reify

theorem addrShlAddLoop_zero_spec (Γ : Env) (base inv : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ (Func.lateOpt addrShlAddLoop) (base, inv, 0#64, ()) m
      (fun (r, ()) m' => r = 0#64 ∧ m' = m) X := by
  apply Func.lateOpt_spec addrShlAddLoop_wf
  dsimp only [Func.spec, Func.wp, addrShlAddLoop]
  refine wp_loop1 _ _
    (fun k (x : Tup Val [i64, i64]) m' => k = 0 ∧ x.1 = 0#64 ∧ x.2.1 = 0#64 ∧ m' = m) ?_ ?_
  · rintro _ _ ⟨iv, acc, ⟨⟩⟩ m' _ ⟨_, rfl, rfl, rfl⟩
    simp only [op2_eq_mk, wp_let_cmp_eq, vals_nil, vals_cons, Arg.val_var, liftCmp,
      CmpOp.evalBits, cast_eq, decide_true, wp_jnz, wp_ret]
    exact ⟨fun _ => ⟨trivial, trivial⟩, fun h => False.elim (by cases h)⟩
  · intro J hJ
    simp only [wp_jump, vals_nil, vals_cons, Arg.val_imm]
    exact hJ 0 (0#64, 0#64, ()) m ⟨rfl, rfl, rfl, rfl⟩

theorem signedDigitRangeFn_lateOpt_spec (Γ : Env) (x : BitVec 8) (m : Mem 64) (X : XPost) :
    Func.spec Γ (Func.lateOpt signedDigitRangeFn) (x, ()) m
      (fun (r, ()) m' => r = ((0x30#8).sle x && x.slt 0x3a#8) ∧ m' = m) X := by
  apply Func.lateOpt_spec signedDigitRangeFn_wf
  dsimp only [Func.spec, Func.wp, signedDigitRangeFn, wp, Op.wp, OpCode.wp_cmp, op2, vals,
    Arg.val, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, cast_eq, liftCmp, CmpOp.evalBits,
    lift2, Closed]
  exact ⟨rfl, rfl⟩

theorem unsignedOrRangeFn_lateOpt_spec (Γ : Env) (x : BitVec 32) (m : Mem 64) (X : XPost) :
    Func.spec Γ (Func.lateOpt unsignedOrRangeFn) (x, ()) m
      (fun (r, ()) m' => r = (x.ult 10#32 || (20#32).ule x) ∧ m' = m) X := by
  apply Func.lateOpt_spec unsignedOrRangeFn_wf
  dsimp only [Func.spec, Func.wp, unsignedOrRangeFn, wp, Op.wp, OpCode.wp_cmp, op2, vals,
    Arg.val, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, cast_eq, liftCmp, CmpOp.evalBits,
    lift2, Closed]
  exact ⟨rfl, rfl⟩

theorem zeroLoSignedRangeFn_lateOpt_spec (Γ : Env) (x : BitVec 32) (m : Mem 64) (X : XPost) :
    Func.spec Γ (Func.lateOpt zeroLoSignedRangeFn) (x, ()) m
      (fun (r, ()) m' => r = ((0#32).sle x && x.slt 64#32) ∧ m' = m) X := by
  apply Func.lateOpt_spec zeroLoSignedRangeFn_wf
  dsimp only [Func.spec, Func.wp, zeroLoSignedRangeFn, wp, Op.wp, OpCode.wp_cmp, op2, vals,
    Arg.val, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, cast_eq, liftCmp, CmpOp.evalBits,
    lift2, Closed]
  exact ⟨rfl, rfl⟩

/-! ## 4. Standard Axiom Audit -/

#print axioms LeanQbe.T.bv_shl_add
#print axioms LeanQbe.T.bv_shl_sub
#print axioms LeanQbe.T.bv_add_shl_add_disp
#print axioms LeanQbe.T.bv_add_shl_sub_disp
#print axioms LeanQbe.T.toRangeBound_eval
#print axioms LeanQbe.T.bv_range_and_u
#print axioms LeanQbe.T.bv_range_and_s
#print axioms LeanQbe.T.bv_range_or_u
#print axioms LeanQbe.T.bv_range_or_s
#print axioms LeanQbe.T.addrRangeSweep_wp
#print axioms LeanQbe.T.addrRangeSweep_wf
#print axioms LeanQbe.T.Func.addrRangeOpt_wf
#print axioms LeanQbe.T.Func.addrRangeOpt_spec
#print axioms LeanQbeTest.T.AddrRangeOptTest.addrShlAddLoop_zero_spec
#print axioms LeanQbeTest.T.AddrRangeOptTest.signedDigitRangeFn_lateOpt_spec
#print axioms LeanQbeTest.T.AddrRangeOptTest.unsignedOrRangeFn_lateOpt_spec
#print axioms LeanQbeTest.T.AddrRangeOptTest.zeroLoSignedRangeFn_lateOpt_spec

end LeanQbeTest.T.AddrRangeOptTest
