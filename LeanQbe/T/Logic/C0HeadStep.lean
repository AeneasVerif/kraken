module

public import LeanQbe.T.Logic.C0Step
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0StepAttr
public meta import LeanQbe.T.Logic.C0Step

/-!
# `O(1)` Head-Only C0 Symbolic Execution (`C0HeadStep`)

Provides an `O(1)`-per-step head-only symbolic executor for `LeanQbe.T.wp` / `Func.wp` that
eliminates both the `O(AST)` continuation walks of `c0_let_simp` and per-step `MVarId.change`
kernel `isDefEq` overhead:

1. **Direct `Op.mk`, `op1`, `op2`, and `op3` head lemmas** (`head_wp_*` and `head_wp_op{1,2,3}_*`):
   parameterized by already-reduced operand values (`ha : a.val = va`, `hb : b.val = vb`, closed
   by `O(1)` scalar `rfl`), so neither `Arg.val` nor `Prod.fst` wrappers leak into continuations
   `k` and straight-line `let_` steps perform **zero** `MVarId.change` calls.
2. **Shift-by-promoted-literal & constant-cast folding**: `head_wp_{shl,lshr,ashr}_imm` (for both
   `Op.mk` and `op2`) handles C0's `sext`-promoted shift constants (`h->cur_vars << 1`), and
   `head_wp_{zext,sext,trunc}_lit` folds constant bitvector casts at the head.
3. **Two-level `(footprintHead, AddrKey)` memory dispatch**: `headMemSolve` queries
   `C0Step.c0MemLemmasForAddr` first (`O(1)` bucket lookup + fast `assumption`/`rfl` before
   `ecancel`/`c0_bound`), falling back to remaining lemmas of `C0Step.c0MemLemmas` only on miss.
4. **Configurable tactics**: `c0_hstep`, `c0_hsteps`, `c0_hsteps!`, `c0_hsteps_nogrp`, and
   `c0_hsplit`, with automatic `.consumeMData`, `head_strip_le`, `Blocks.get` peeling, and stale
   memory hypothesis clearing.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.C0HeadStep

open LeanQbe.T
open Std.ExtHashMap

/-! ## 1. Universal `O(1)` Head-Step Lemma Suite (`Op.mk` and `op1`/`op2`/`op3`) -/

section HeadLemmas
variable {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}

abbrev K1 (rs : List Ty) (t : Ty) := Tup Val [t] → Expr Val Cont rs
abbrev K2 (rs : List Ty) (t u : Ty) := Tup Val [t, u] → Expr Val Cont rs

local notation "W " e => wp Γ Q X e m

theorem head_strip_le {a b : Nat} {P : Prop} (hle : a ≤ b) (hp : P) : a ≤ b ∧ P := ⟨hle, hp⟩

/-! ### Unary, binary, ternary, and multi-result operations (`Op.mk`) -/

theorem head_wp_copy {t : Ty} {a : Arg Val t} {va : Val t} {k : K1 rs t}
    (ha : a.val = va) (h : W (k (va, ()))) : W (.let_ (Op.mk (.copy t) (a, ())) k) := by
  subst ha; simpa only [wp_let_copy_eq] using h
theorem head_wp_add {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (va + vb, ()))) :
    W (.let_ (Op.mk (.add (.bits n)) (a, b, ())) k) := by
  subst ha hb
  simpa only [wp_let_add_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2] using h
theorem head_wp_sub {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (va - vb, ()))) :
    W (.let_ (Op.mk (.sub (.bits n)) (a, b, ())) k) := by
  subst ha hb
  simpa only [wp_let_sub_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2] using h
theorem head_wp_mul {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (va * vb, ()))) :
    W (.let_ (Op.mk (.mul (.bits n)) (a, b, ())) k) := by
  subst ha hb
  simpa only [wp_let_mul_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2] using h
theorem head_wp_neg {n : Nat} {a : Arg Val (.bits n)} {va : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (h : W (k (-va, ()))) : W (.let_ (Op.mk (.neg (.bits n)) (a, ())) k) := by
  subst ha; simpa only [wp_let_neg_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift1] using h
theorem head_wp_and {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (va &&& vb, ()))) :
    W (.let_ (Op.mk (.and (.bits n)) (a, b, ())) k) := by
  subst ha hb; simpa only [wp_let_and_eq, lift2] using h
theorem head_wp_or {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (va ||| vb, ()))) :
    W (.let_ (Op.mk (.or (.bits n)) (a, b, ())) k) := by
  subst ha hb; simpa only [wp_let_or_eq, lift2] using h
theorem head_wp_xor {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (va ^^^ vb, ()))) :
    W (.let_ (Op.mk (.xor (.bits n)) (a, b, ())) k) := by
  subst ha hb; simpa only [wp_let_xor_eq, lift2] using h
theorem head_wp_and_bool {a b : Arg Val .bool} {va vb : Bool} {k : K1 rs .bool}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (va && vb, ()))) :
    W (.let_ (Op.mk (.and .bool) (a, b, ())) k) := by
  subst ha hb; simpa only [wp_let_and_eq, lift2] using h
theorem head_wp_or_bool {a b : Arg Val .bool} {va vb : Bool} {k : K1 rs .bool}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (va || vb, ()))) :
    W (.let_ (Op.mk (.or .bool) (a, b, ())) k) := by
  subst ha hb; simpa only [wp_let_or_eq, lift2] using h
theorem head_wp_xor_bool {a b : Arg Val .bool} {va vb : Bool} {k : K1 rs .bool}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (va ^^ vb, ()))) :
    W (.let_ (Op.mk (.xor .bool) (a, b, ())) k) := by
  subst ha hb; simpa only [wp_let_xor_eq, lift2] using h
theorem head_wp_not_bits {n : Nat} {a : Arg Val (.bits n)} {va : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (h : W (k (~~~va, ()))) : W (.let_ (Op.mk (.not (.bits n)) (a, ())) k) := by
  subst ha; simpa only [wp_let_not_eq, lift1] using h
theorem head_wp_not_bool {a : Arg Val .bool} {va : Bool} {k : K1 rs .bool}
    (ha : a.val = va) (h : W (k (!va, ()))) : W (.let_ (Op.mk (.not .bool) (a, ())) k) := by
  subst ha; simpa only [wp_let_not_eq, lift1] using h
theorem head_wp_shl {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (va <<< (vb.toNat % n), ()))) :
    W (.let_ (Op.mk (.shl (.bits n)) (a, b, ())) k) := by
  subst ha hb
  simpa only [wp_let_shl_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2] using h
theorem head_wp_shl_imm {n : Nat} {a b : Arg Val (.bits n)} {va : BitVec n} {c : Nat}
    {k : K1 rs (.bits n)} (ha : a.val = va) (hc : b.val.toNat % n = c) (h : W (k (va <<< c, ()))) :
    W (.let_ (Op.mk (.shl (.bits n)) (a, b, ())) k) :=
  head_wp_shl ha rfl (by simpa only [hc] using h)
theorem head_wp_lshr {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (va >>> (vb.toNat % n), ()))) :
    W (.let_ (Op.mk (.lshr (.bits n)) (a, b, ())) k) := by
  subst ha hb
  simpa only [wp_let_lshr_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2] using h
theorem head_wp_lshr_imm {n : Nat} {a b : Arg Val (.bits n)} {va : BitVec n} {c : Nat}
    {k : K1 rs (.bits n)} (ha : a.val = va) (hc : b.val.toNat % n = c) (h : W (k (va >>> c, ()))) :
    W (.let_ (Op.mk (.lshr (.bits n)) (a, b, ())) k) :=
  head_wp_lshr ha rfl (by simpa only [hc] using h)
theorem head_wp_ashr {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (va.sshiftRight (vb.toNat % n), ()))) :
    W (.let_ (Op.mk (.ashr (.bits n)) (a, b, ())) k) := by
  subst ha hb
  simpa only [wp_let_ashr_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2] using h
theorem head_wp_ashr_imm {n : Nat} {a b : Arg Val (.bits n)} {va : BitVec n} {c : Nat}
    {k : K1 rs (.bits n)} (ha : a.val = va) (hc : b.val.toNat % n = c)
    (h : W (k (va.sshiftRight c, ()))) :
    W (.let_ (Op.mk (.ashr (.bits n)) (a, b, ())) k) :=
  head_wp_ashr ha rfl (by simpa only [hc] using h)
theorem head_wp_rotl {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (va.rotateLeft (vb.toNat % n), ()))) :
    W (.let_ (Op.mk (.rotl (.bits n)) (a, b, ())) k) := by
  subst ha hb
  simpa only [wp_let_rotl_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2] using h
theorem head_wp_rotr {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (va.rotateRight (vb.toNat % n), ()))) :
    W (.let_ (Op.mk (.rotr (.bits n)) (a, b, ())) k) := by
  subst ha hb
  simpa only [wp_let_rotr_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2] using h
theorem head_wp_clz {n : Nat} {a : Arg Val (.bits n)} {va : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (h : W (k (va.clz, ()))) : W (.let_ (Op.mk (.clz n) (a, ())) k) := by
  subst ha; simpa only [wp_let_clz_eq] using h
theorem head_wp_ctz {n : Nat} {a : Arg Val (.bits n)} {va : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (h : W (k (va.reverse.clz, ()))) : W (.let_ (Op.mk (.ctz n) (a, ())) k) := by
  subst ha; simpa only [wp_let_ctz_eq] using h
theorem head_wp_popcnt {n : Nat} {a : Arg Val (.bits n)} {va : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (h : W (k (va.cpop, ()))) : W (.let_ (Op.mk (.popcnt n) (a, ())) k) := by
  subst ha; simpa only [wp_let_popcnt_eq] using h
theorem head_wp_rbit {n : Nat} {a : Arg Val (.bits n)} {va : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (h : W (k (va.reverse, ()))) : W (.let_ (Op.mk (.rbit n) (a, ())) k) := by
  subst ha; simpa only [wp_let_rbit_eq] using h
theorem head_wp_zext {n w : Nat} {a : Arg Val (.bits n)} {va : BitVec n} {k : K1 rs (.bits w)}
    (ha : a.val = va) (hle : n ≤ w) (h : W (k (va.setWidth w, ()))) :
    W (.let_ (Op.mk (.zext n w) (a, ())) k) := by
  subst ha; rw [wp_let_zext_eq]; exact ⟨hle, h⟩
theorem head_wp_zext_lit {n w : Nat} {a : Arg Val (.bits n)} {v : BitVec w} {k : K1 rs (.bits w)}
    (hle : n ≤ w) (hv : a.val.setWidth w = v) (h : W (k (v, ()))) :
    W (.let_ (Op.mk (.zext n w) (a, ())) k) := head_wp_zext rfl hle (hv ▸ h)
theorem head_wp_sext {n w : Nat} {a : Arg Val (.bits n)} {va : BitVec n} {k : K1 rs (.bits w)}
    (ha : a.val = va) (hle : n ≤ w) (h : W (k (va.signExtend w, ()))) :
    W (.let_ (Op.mk (.sext n w) (a, ())) k) := by
  subst ha; rw [wp_let_sext_eq]; exact ⟨hle, h⟩
theorem head_wp_sext_lit {n w : Nat} {a : Arg Val (.bits n)} {v : BitVec w} {k : K1 rs (.bits w)}
    (hle : n ≤ w) (hv : a.val.signExtend w = v) (h : W (k (v, ()))) :
    W (.let_ (Op.mk (.sext n w) (a, ())) k) := head_wp_sext rfl hle (hv ▸ h)
theorem head_wp_trunc {n w : Nat} {a : Arg Val (.bits n)} {va : BitVec n} {k : K1 rs (.bits w)}
    (ha : a.val = va) (hle : w ≤ n) (h : W (k (va.setWidth w, ()))) :
    W (.let_ (Op.mk (.trunc n w) (a, ())) k) := by
  subst ha; rw [wp_let_trunc_eq]; exact ⟨hle, h⟩
theorem head_wp_trunc_lit {n w : Nat} {a : Arg Val (.bits n)} {v : BitVec w} {k : K1 rs (.bits w)}
    (hle : w ≤ n) (hv : a.val.setWidth w = v) (h : W (k (v, ()))) :
    W (.let_ (Op.mk (.trunc n w) (a, ())) k) := head_wp_trunc rfl hle (hv ▸ h)
theorem head_wp_ofBool {n : Nat} {a : Arg Val .bool} {va : Bool} {k : K1 rs (.bits n)}
    (ha : a.val = va) (h : W (k (BitVec.ofNat n va.toNat, ()))) :
    W (.let_ (Op.mk (.ofBool n) (a, ())) k) := by
  subst ha; simpa only [wp_let_ofBool_eq] using h
theorem head_wp_select {t : Ty} {c : Arg Val .bool} {a b : Arg Val t} {vc : Bool} {va vb : Val t}
    {k : K1 rs t} (hc : c.val = vc) (ha : a.val = va) (hb : b.val = vb)
    (h : W (k (if vc then va else vb, ()))) : W (.let_ (Op.mk (.select t) (c, a, b, ())) k) := by
  subst hc ha hb; simpa only [wp_let_select_eq] using h
theorem head_wp_cmp_bits {o : CmpOp} {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs .bool} (ha : a.val = va) (hb : b.val = vb) (h : W (k (o.evalBits va vb, ()))) :
    W (.let_ (Op.mk (.cmp o (.bits n) .bool rfl) (a, b, ())) k) := by
  subst ha hb
  simpa only [wp_let_cmp_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, cast_eq, liftCmp] using h
theorem head_wp_cmp_bool {o : CmpOp} {a b : Arg Val .bool} {va vb : Bool} {k : K1 rs .bool}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (o.evalBool va vb, ()))) :
    W (.let_ (Op.mk (.cmp o .bool .bool rfl) (a, b, ())) k) := by
  subst ha hb
  simpa only [wp_let_cmp_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, cast_eq, liftCmp] using h
theorem head_wp_cmp_eq {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs .bool}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k ((va == vb), ()))) :
    W (.let_ (Op.mk (.cmp .eq (.bits n) .bool rfl) (a, b, ())) k) :=
  head_wp_cmp_bits ha hb (evalBits_eq_beq va vb ▸ h)
theorem head_wp_cmp_ne {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs .bool}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k ((va != vb), ()))) :
    W (.let_ (Op.mk (.cmp .ne (.bits n) .bool rfl) (a, b, ())) k) :=
  head_wp_cmp_bits ha hb (evalBits_ne_bne va vb ▸ h)
theorem head_wp_cmp_ult {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs .bool}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (va.ult vb, ()))) :
    W (.let_ (Op.mk (.cmp .ult (.bits n) .bool rfl) (a, b, ())) k) :=
  head_wp_cmp_bits ha hb (evalBits_ult_eq va vb ▸ h)
theorem head_wp_cmp_ule {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs .bool}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (va.ule vb, ()))) :
    W (.let_ (Op.mk (.cmp .ule (.bits n) .bool rfl) (a, b, ())) k) :=
  head_wp_cmp_bits ha hb (evalBits_ule_eq va vb ▸ h)
theorem head_wp_cmp_ugt {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs .bool}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (vb.ult va, ()))) :
    W (.let_ (Op.mk (.cmp .ugt (.bits n) .bool rfl) (a, b, ())) k) :=
  head_wp_cmp_bits ha hb (evalBits_ugt_eq va vb ▸ h)
theorem head_wp_cmp_uge {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs .bool}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (vb.ule va, ()))) :
    W (.let_ (Op.mk (.cmp .uge (.bits n) .bool rfl) (a, b, ())) k) :=
  head_wp_cmp_bits ha hb (evalBits_uge_eq va vb ▸ h)
theorem head_wp_cmp_slt {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs .bool}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (va.slt vb, ()))) :
    W (.let_ (Op.mk (.cmp .slt (.bits n) .bool rfl) (a, b, ())) k) :=
  head_wp_cmp_bits ha hb (evalBits_slt_eq va vb ▸ h)
theorem head_wp_cmp_sle {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs .bool}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (va.sle vb, ()))) :
    W (.let_ (Op.mk (.cmp .sle (.bits n) .bool rfl) (a, b, ())) k) :=
  head_wp_cmp_bits ha hb (evalBits_sle_eq va vb ▸ h)
theorem head_wp_cmp_sgt {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs .bool}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (vb.slt va, ()))) :
    W (.let_ (Op.mk (.cmp .sgt (.bits n) .bool rfl) (a, b, ())) k) :=
  head_wp_cmp_bits ha hb (evalBits_sgt_eq va vb ▸ h)
theorem head_wp_cmp_sge {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs .bool}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (vb.sle va, ()))) :
    W (.let_ (Op.mk (.cmp .sge (.bits n) .bool rfl) (a, b, ())) k) :=
  head_wp_cmp_bits ha hb (evalBits_sge_eq va vb ▸ h)
theorem head_wp_udiv {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (hb : b.val = vb) (hne : vb ≠ 0) (h : W (k (va / vb, ()))) :
    W (.let_ (Op.mk (.udiv n) (a, b, ())) k) := by
  subst ha hb; rw [wp_let_udiv_eq]; exact ⟨hne, h⟩
theorem head_wp_urem {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (hb : b.val = vb) (hne : vb ≠ 0) (h : W (k (va % vb, ()))) :
    W (.let_ (Op.mk (.urem n) (a, b, ())) k) := by
  subst ha hb; rw [wp_let_urem_eq]; exact ⟨hne, h⟩
theorem head_wp_sdiv {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (hb : b.val = vb) (hd : sdivDefined va vb = true)
    (h : W (k (va.sdiv vb, ()))) : W (.let_ (Op.mk (.sdiv n) (a, b, ())) k) := by
  subst ha hb; rw [wp_let_sdiv_eq]; exact ⟨hd, h⟩
theorem head_wp_srem {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (hb : b.val = vb) (hd : sdivDefined va vb = true)
    (h : W (k (va.srem vb, ()))) : W (.let_ (Op.mk (.srem n) (a, b, ())) k) := by
  subst ha hb; rw [wp_let_srem_eq]; exact ⟨hd, h⟩
theorem head_wp_udiv0 {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (if vb = 0 then 0 else va / vb, ()))) :
    W (.let_ (Op.mk (.udiv0 n) (a, b, ())) k) := by
  subst ha hb; simpa only [wp_let_udiv0_eq] using h
theorem head_wp_sdiv0 {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (if vb = 0 then 0 else va.sdiv vb, ()))) :
    W (.let_ (Op.mk (.sdiv0 n) (a, b, ())) k) := by
  subst ha hb; simpa only [wp_let_sdiv0_eq] using h
theorem head_wp_addc {n : Nat} {a b : Arg Val (.bits n)} {c : Arg Val .bool} {va vb : BitVec n}
    {vc : Bool} {k : K2 rs (.bits n) .bool} (ha : a.val = va) (hb : b.val = vb) (hc : c.val = vc)
    (h : W (k (va + vb + BitVec.ofNat n vc.toNat,
      decide (2 ^ n ≤ va.toNat + vb.toNat + vc.toNat), ()))) :
    W (.let_ (Op.mk (.addc n) (a, b, c, ())) k) := by
  subst ha hb hc; simpa only [wp_let_addc_eq] using h
theorem head_wp_subb {n : Nat} {a b : Arg Val (.bits n)} {c : Arg Val .bool} {va vb : BitVec n}
    {vc : Bool} {k : K2 rs (.bits n) .bool} (ha : a.val = va) (hb : b.val = vb) (hc : c.val = vc)
    (h : W (k (va - vb - BitVec.ofNat n vc.toNat,
      decide (va.toNat < vb.toNat + vc.toNat), ()))) :
    W (.let_ (Op.mk (.subb n) (a, b, c, ())) k) := by
  subst ha hb hc; simpa only [wp_let_subb_eq] using h
theorem head_wp_umulw {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K2 rs (.bits n) (.bits n)} (ha : a.val = va) (hb : b.val = vb)
    (h : W (k (va * vb, BitVec.ofNat n (va.toNat * vb.toNat / 2 ^ n), ()))) :
    W (.let_ (Op.mk (.umulw n) (a, b, ())) k) := by
  subst ha hb; simpa only [wp_let_umulw_eq] using h

/-! ### Direct `op1`, `op2`, and `op3` head lemmas (zero `op*_eq_mk` conversion) -/

theorem head_wp_op1_copy {t : Ty} {a : Arg Val t} {va : Val t} {k : K1 rs t}
    (ha : a.val = va) (h : W (k (va, ()))) : W (.let_ (op1 (.copy t) a) k) := head_wp_copy ha h
theorem head_wp_op1_neg {n : Nat} {a : Arg Val (.bits n)} {va : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (h : W (k (-va, ()))) : W (.let_ (op1 (.neg (.bits n)) a) k) :=
  head_wp_neg ha h
theorem head_wp_op1_not_bits {n : Nat} {a : Arg Val (.bits n)} {va : BitVec n}
    {k : K1 rs (.bits n)} (ha : a.val = va) (h : W (k (~~~va, ()))) :
    W (.let_ (op1 (.not (.bits n)) a) k) := head_wp_not_bits ha h
theorem head_wp_op1_not_bool {a : Arg Val .bool} {va : Bool} {k : K1 rs .bool}
    (ha : a.val = va) (h : W (k (!va, ()))) : W (.let_ (op1 (.not .bool) a) k) :=
  head_wp_not_bool ha h
theorem head_wp_op1_clz {n : Nat} {a : Arg Val (.bits n)} {va : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (h : W (k (va.clz, ()))) : W (.let_ (op1 (.clz n) a) k) := head_wp_clz ha h
theorem head_wp_op1_ctz {n : Nat} {a : Arg Val (.bits n)} {va : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (h : W (k (va.reverse.clz, ()))) : W (.let_ (op1 (.ctz n) a) k) :=
  head_wp_ctz ha h
theorem head_wp_op1_popcnt {n : Nat} {a : Arg Val (.bits n)} {va : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (h : W (k (va.cpop, ()))) : W (.let_ (op1 (.popcnt n) a) k) :=
  head_wp_popcnt ha h
theorem head_wp_op1_rbit {n : Nat} {a : Arg Val (.bits n)} {va : BitVec n} {k : K1 rs (.bits n)}
    (ha : a.val = va) (h : W (k (va.reverse, ()))) : W (.let_ (op1 (.rbit n) a) k) :=
  head_wp_rbit ha h
theorem head_wp_op1_zext {n w : Nat} {a : Arg Val (.bits n)} {va : BitVec n} {k : K1 rs (.bits w)}
    (ha : a.val = va) (hle : n ≤ w) (h : W (k (va.setWidth w, ()))) :
    W (.let_ (op1 (.zext n w) a) k) := head_wp_zext ha hle h
theorem head_wp_op1_zext_lit {n w : Nat} {a : Arg Val (.bits n)} {v : BitVec w}
    {k : K1 rs (.bits w)} (hle : n ≤ w) (hv : a.val.setWidth w = v) (h : W (k (v, ()))) :
    W (.let_ (op1 (.zext n w) a) k) := head_wp_zext_lit hle hv h
theorem head_wp_op1_sext {n w : Nat} {a : Arg Val (.bits n)} {va : BitVec n} {k : K1 rs (.bits w)}
    (ha : a.val = va) (hle : n ≤ w) (h : W (k (va.signExtend w, ()))) :
    W (.let_ (op1 (.sext n w) a) k) := head_wp_sext ha hle h
theorem head_wp_op1_sext_lit {n w : Nat} {a : Arg Val (.bits n)} {v : BitVec w}
    {k : K1 rs (.bits w)} (hle : n ≤ w) (hv : a.val.signExtend w = v) (h : W (k (v, ()))) :
    W (.let_ (op1 (.sext n w) a) k) := head_wp_sext_lit hle hv h
theorem head_wp_op1_trunc {n w : Nat} {a : Arg Val (.bits n)} {va : BitVec n} {k : K1 rs (.bits w)}
    (ha : a.val = va) (hle : w ≤ n) (h : W (k (va.setWidth w, ()))) :
    W (.let_ (op1 (.trunc n w) a) k) := head_wp_trunc ha hle h
theorem head_wp_op1_trunc_lit {n w : Nat} {a : Arg Val (.bits n)} {v : BitVec w}
    {k : K1 rs (.bits w)} (hle : w ≤ n) (hv : a.val.setWidth w = v) (h : W (k (v, ()))) :
    W (.let_ (op1 (.trunc n w) a) k) := head_wp_trunc_lit hle hv h
theorem head_wp_op1_ofBool {n : Nat} {a : Arg Val .bool} {va : Bool} {k : K1 rs (.bits n)}
    (ha : a.val = va) (h : W (k (BitVec.ofNat n va.toNat, ()))) :
    W (.let_ (op1 (.ofBool n) a) k) := head_wp_ofBool ha h

theorem head_wp_op2_add {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs (.bits n)} (ha : a.val = va) (hb : b.val = vb) (h : W (k (va + vb, ()))) :
    W (.let_ (op2 (.add (.bits n)) a b) k) := head_wp_add ha hb h
theorem head_wp_op2_sub {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs (.bits n)} (ha : a.val = va) (hb : b.val = vb) (h : W (k (va - vb, ()))) :
    W (.let_ (op2 (.sub (.bits n)) a b) k) := head_wp_sub ha hb h
theorem head_wp_op2_mul {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs (.bits n)} (ha : a.val = va) (hb : b.val = vb) (h : W (k (va * vb, ()))) :
    W (.let_ (op2 (.mul (.bits n)) a b) k) := head_wp_mul ha hb h
theorem head_wp_op2_and {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs (.bits n)} (ha : a.val = va) (hb : b.val = vb) (h : W (k (va &&& vb, ()))) :
    W (.let_ (op2 (.and (.bits n)) a b) k) := head_wp_and ha hb h
theorem head_wp_op2_or {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs (.bits n)} (ha : a.val = va) (hb : b.val = vb) (h : W (k (va ||| vb, ()))) :
    W (.let_ (op2 (.or (.bits n)) a b) k) := head_wp_or ha hb h
theorem head_wp_op2_xor {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs (.bits n)} (ha : a.val = va) (hb : b.val = vb) (h : W (k (va ^^^ vb, ()))) :
    W (.let_ (op2 (.xor (.bits n)) a b) k) := head_wp_xor ha hb h
theorem head_wp_op2_and_bool {a b : Arg Val .bool} {va vb : Bool} {k : K1 rs .bool}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (va && vb, ()))) :
    W (.let_ (op2 (.and .bool) a b) k) := head_wp_and_bool ha hb h
theorem head_wp_op2_or_bool {a b : Arg Val .bool} {va vb : Bool} {k : K1 rs .bool}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (va || vb, ()))) :
    W (.let_ (op2 (.or .bool) a b) k) := head_wp_or_bool ha hb h
theorem head_wp_op2_xor_bool {a b : Arg Val .bool} {va vb : Bool} {k : K1 rs .bool}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (va ^^ vb, ()))) :
    W (.let_ (op2 (.xor .bool) a b) k) := head_wp_xor_bool ha hb h
theorem head_wp_op2_shl {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs (.bits n)} (ha : a.val = va) (hb : b.val = vb)
    (h : W (k (va <<< (vb.toNat % n), ()))) : W (.let_ (op2 (.shl (.bits n)) a b) k) :=
  head_wp_shl ha hb h
theorem head_wp_op2_shl_imm {n : Nat} {a b : Arg Val (.bits n)} {va : BitVec n} {c : Nat}
    {k : K1 rs (.bits n)} (ha : a.val = va) (hc : b.val.toNat % n = c) (h : W (k (va <<< c, ()))) :
    W (.let_ (op2 (.shl (.bits n)) a b) k) := head_wp_shl_imm ha hc h
theorem head_wp_op2_lshr {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs (.bits n)} (ha : a.val = va) (hb : b.val = vb)
    (h : W (k (va >>> (vb.toNat % n), ()))) : W (.let_ (op2 (.lshr (.bits n)) a b) k) :=
  head_wp_lshr ha hb h
theorem head_wp_op2_lshr_imm {n : Nat} {a b : Arg Val (.bits n)} {va : BitVec n} {c : Nat}
    {k : K1 rs (.bits n)} (ha : a.val = va) (hc : b.val.toNat % n = c) (h : W (k (va >>> c, ()))) :
    W (.let_ (op2 (.lshr (.bits n)) a b) k) := head_wp_lshr_imm ha hc h
theorem head_wp_op2_ashr {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs (.bits n)} (ha : a.val = va) (hb : b.val = vb)
    (h : W (k (va.sshiftRight (vb.toNat % n), ()))) : W (.let_ (op2 (.ashr (.bits n)) a b) k) :=
  head_wp_ashr ha hb h
theorem head_wp_op2_ashr_imm {n : Nat} {a b : Arg Val (.bits n)} {va : BitVec n} {c : Nat}
    {k : K1 rs (.bits n)} (ha : a.val = va) (hc : b.val.toNat % n = c)
    (h : W (k (va.sshiftRight c, ()))) : W (.let_ (op2 (.ashr (.bits n)) a b) k) :=
  head_wp_ashr_imm ha hc h
theorem head_wp_op2_rotl {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs (.bits n)} (ha : a.val = va) (hb : b.val = vb)
    (h : W (k (va.rotateLeft (vb.toNat % n), ()))) : W (.let_ (op2 (.rotl (.bits n)) a b) k) :=
  head_wp_rotl ha hb h
theorem head_wp_op2_rotr {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs (.bits n)} (ha : a.val = va) (hb : b.val = vb)
    (h : W (k (va.rotateRight (vb.toNat % n), ()))) : W (.let_ (op2 (.rotr (.bits n)) a b) k) :=
  head_wp_rotr ha hb h
theorem head_wp_op2_cmp_bits {o : CmpOp} {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs .bool} (ha : a.val = va) (hb : b.val = vb) (h : W (k (o.evalBits va vb, ()))) :
    W (.let_ (op2 (.cmp o (.bits n) .bool rfl) a b) k) := head_wp_cmp_bits ha hb h
theorem head_wp_op2_cmp_bool {o : CmpOp} {a b : Arg Val .bool} {va vb : Bool} {k : K1 rs .bool}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k (o.evalBool va vb, ()))) :
    W (.let_ (op2 (.cmp o .bool .bool rfl) a b) k) := head_wp_cmp_bool ha hb h
theorem head_wp_op2_cmp_eq {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs .bool}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k ((va == vb), ()))) :
    W (.let_ (op2 (.cmp .eq (.bits n) .bool rfl) a b) k) := head_wp_cmp_eq ha hb h
theorem head_wp_op2_cmp_ne {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n} {k : K1 rs .bool}
    (ha : a.val = va) (hb : b.val = vb) (h : W (k ((va != vb), ()))) :
    W (.let_ (op2 (.cmp .ne (.bits n) .bool rfl) a b) k) := head_wp_cmp_ne ha hb h
theorem head_wp_op2_cmp_ult {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs .bool} (ha : a.val = va) (hb : b.val = vb) (h : W (k (va.ult vb, ()))) :
    W (.let_ (op2 (.cmp .ult (.bits n) .bool rfl) a b) k) := head_wp_cmp_ult ha hb h
theorem head_wp_op2_cmp_ule {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs .bool} (ha : a.val = va) (hb : b.val = vb) (h : W (k (va.ule vb, ()))) :
    W (.let_ (op2 (.cmp .ule (.bits n) .bool rfl) a b) k) := head_wp_cmp_ule ha hb h
theorem head_wp_op2_cmp_ugt {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs .bool} (ha : a.val = va) (hb : b.val = vb) (h : W (k (vb.ult va, ()))) :
    W (.let_ (op2 (.cmp .ugt (.bits n) .bool rfl) a b) k) := head_wp_cmp_ugt ha hb h
theorem head_wp_op2_cmp_uge {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs .bool} (ha : a.val = va) (hb : b.val = vb) (h : W (k (vb.ule va, ()))) :
    W (.let_ (op2 (.cmp .uge (.bits n) .bool rfl) a b) k) := head_wp_cmp_uge ha hb h
theorem head_wp_op2_cmp_slt {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs .bool} (ha : a.val = va) (hb : b.val = vb) (h : W (k (va.slt vb, ()))) :
    W (.let_ (op2 (.cmp .slt (.bits n) .bool rfl) a b) k) := head_wp_cmp_slt ha hb h
theorem head_wp_op2_cmp_sle {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs .bool} (ha : a.val = va) (hb : b.val = vb) (h : W (k (va.sle vb, ()))) :
    W (.let_ (op2 (.cmp .sle (.bits n) .bool rfl) a b) k) := head_wp_cmp_sle ha hb h
theorem head_wp_op2_cmp_sgt {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs .bool} (ha : a.val = va) (hb : b.val = vb) (h : W (k (vb.slt va, ()))) :
    W (.let_ (op2 (.cmp .sgt (.bits n) .bool rfl) a b) k) := head_wp_cmp_sgt ha hb h
theorem head_wp_op2_cmp_sge {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs .bool} (ha : a.val = va) (hb : b.val = vb) (h : W (k (vb.sle va, ()))) :
    W (.let_ (op2 (.cmp .sge (.bits n) .bool rfl) a b) k) := head_wp_cmp_sge ha hb h
theorem head_wp_op2_udiv {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs (.bits n)} (ha : a.val = va) (hb : b.val = vb) (hne : vb ≠ 0)
    (h : W (k (va / vb, ()))) : W (.let_ (op2 (.udiv n) a b) k) := head_wp_udiv ha hb hne h
theorem head_wp_op2_urem {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs (.bits n)} (ha : a.val = va) (hb : b.val = vb) (hne : vb ≠ 0)
    (h : W (k (va % vb, ()))) : W (.let_ (op2 (.urem n) a b) k) := head_wp_urem ha hb hne h
theorem head_wp_op2_sdiv {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs (.bits n)} (ha : a.val = va) (hb : b.val = vb) (hd : sdivDefined va vb = true)
    (h : W (k (va.sdiv vb, ()))) : W (.let_ (op2 (.sdiv n) a b) k) := head_wp_sdiv ha hb hd h
theorem head_wp_op2_srem {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs (.bits n)} (ha : a.val = va) (hb : b.val = vb) (hd : sdivDefined va vb = true)
    (h : W (k (va.srem vb, ()))) : W (.let_ (op2 (.srem n) a b) k) := head_wp_srem ha hb hd h
theorem head_wp_op2_udiv0 {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs (.bits n)} (ha : a.val = va) (hb : b.val = vb)
    (h : W (k (if vb = 0 then 0 else va / vb, ()))) : W (.let_ (op2 (.udiv0 n) a b) k) :=
  head_wp_udiv0 ha hb h
theorem head_wp_op2_sdiv0 {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K1 rs (.bits n)} (ha : a.val = va) (hb : b.val = vb)
    (h : W (k (if vb = 0 then 0 else va.sdiv vb, ()))) : W (.let_ (op2 (.sdiv0 n) a b) k) :=
  head_wp_sdiv0 ha hb h
theorem head_wp_op2_umulw {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : K2 rs (.bits n) (.bits n)} (ha : a.val = va) (hb : b.val = vb)
    (h : W (k (va * vb, BitVec.ofNat n (va.toNat * vb.toNat / 2 ^ n), ()))) :
    W (.let_ (op2 (.umulw n) a b) k) := head_wp_umulw ha hb h
theorem head_wp_op3_select {t : Ty} {c : Arg Val .bool} {a b : Arg Val t} {vc : Bool}
    {va vb : Val t} {k : K1 rs t} (hc : c.val = vc) (ha : a.val = va) (hb : b.val = vb)
    (h : W (k (if vc then va else vb, ()))) : W (.let_ (op3 (.select t) c a b) k) :=
  head_wp_select hc ha hb h
theorem head_wp_op3_addc {n : Nat} {a b : Arg Val (.bits n)} {c : Arg Val .bool} {va vb : BitVec n}
    {vc : Bool} {k : K2 rs (.bits n) .bool} (ha : a.val = va) (hb : b.val = vb) (hc : c.val = vc)
    (h : W (k (va + vb + BitVec.ofNat n vc.toNat,
      decide (2 ^ n ≤ va.toNat + vb.toNat + vc.toNat), ()))) :
    W (.let_ (op3 (.addc n) a b c) k) := head_wp_addc ha hb hc h
theorem head_wp_op3_subb {n : Nat} {a b : Arg Val (.bits n)} {c : Arg Val .bool} {va vb : BitVec n}
    {vc : Bool} {k : K2 rs (.bits n) .bool} (ha : a.val = va) (hb : b.val = vb) (hc : c.val = vc)
    (h : W (k (va - vb - BitVec.ofNat n vc.toNat,
      decide (va.toNat < vb.toNat + vc.toNat), ()))) :
    W (.let_ (op3 (.subb n) a b c) k) := head_wp_subb ha hb hc h

/-! ### Memory, control, and terminal head lemmas -/

theorem head_wp_load {t : Ty} {a : Arg Val i64} {addr : BitVec 64} {k : Val t → Expr Val Cont rs}
    {v : Val t} (ha : a.val = addr) (hl : loadVal m t addr = some v) (hk : W (k v)) :
    W (.load t a k) := ⟨v, ha ▸ hl, hk⟩

theorem head_wp_store {t : Ty} {v : Arg Val t} {a : Arg Val i64} {val : Val t} {addr : BitVec 64}
    {k : Expr Val Cont rs} {P R : Mem 64 → Prop} (hv : v.val = val) (ha : a.val = addr)
    (hs : storeOk m t addr ∧ (P ⋆ R) (storeMem m t addr val))
    (hk : ∀ m', (P ⋆ R) m' → wp Γ Q X k m') : W (.store v a k) :=
  ⟨ha ▸ hs.1, hk _ (hv ▸ ha ▸ hs.2)⟩

theorem head_wp_jnz {c : Arg Val .bool} {vc : Bool} {e₁ e₂ : Expr Val Cont rs} (hc : c.val = vc)
    (h₁ : vc = true → W e₁) (h₂ : vc = false → W e₂) : W (.jnz c e₁ e₂) :=
  ⟨fun h => h₁ (hc ▸ h), fun h => h₂ (hc ▸ h)⟩

theorem head_wp_jump {ts : List Ty} {L L' : Cont ts} {args : Tup (Arg Val) ts} {vs : Tup Val ts}
    (hL : L = L') (hvs : vals args = vs) (h : L' vs m) : W (.jump L args) := by
  subst hL; subst hvs; exact h

theorem head_wp_ret {args : Tup (Arg Val) rs} {vs : Tup Val rs}
    (hvs : vals args = vs) (h : Q vs m) : W (.ret args) := by subst hvs; exact h

theorem head_wp_exit {as : List Ty} {f : Sym} {args : Tup (Arg Val) as} {vs : Tup Val as}
    (hvs : vals args = vs) (h : X f as vs m) : W (.exit f args) := by subst hvs; exact h

end HeadLemmas

/-! ## 2. Shallow `O(1)` Head Normalization & Operand Reduction -/

open Lean Meta Elab Tactic

meta initialize registerTraceClass `c0_hstep

/-- Reduce scalar projections (`Prod.fst`/`snd`, `Arg.val`, `vals`) ONLY on a small
operand/value expression; never traverses continuation lambdas `k`. -/
meta partial def reduceSmall (e : Lean.Expr) : Lean.Expr :=
  let rec go (x : Lean.Expr) : Lean.Expr :=
    let x := x.consumeMData.headBeta
    match x with
    | .proj ``Prod 0 arg =>
      let arg' := go arg
      if arg'.isAppOfArity ``Prod.mk 4 then go (arg'.getArg! 2) else .proj ``Prod 0 arg'
    | .proj ``Prod 1 arg =>
      let arg' := go arg
      if arg'.isAppOfArity ``Prod.mk 4 then go (arg'.getArg! 3) else .proj ``Prod 1 arg'
    | .app .. =>
      let fn := x.getAppFn.consumeMData
      let args := x.getAppArgs
      match fn.constName? with
      | some ``Prod.fst =>
        if args.size == 3 then
          let p := go args[2]!
          if p.isAppOfArity ``Prod.mk 4 then go (p.getArg! 2)
          else Lean.mkAppN fn (args.set! 2 p)
        else x
      | some ``Prod.snd =>
        if args.size == 3 then
          let p := go args[2]!
          if p.isAppOfArity ``Prod.mk 4 then go (p.getArg! 3)
          else Lean.mkAppN fn (args.set! 2 p)
        else x
      | some ``LeanQbe.T.Arg.val =>
        if args.size ≥ 2 then
          let a := go args.back!
          if (a.isAppOf ``LeanQbe.T.Arg.var || a.isAppOf ``LeanQbe.T.Arg.imm) &&
              a.getAppNumArgs ≥ 1 then go a.appArg!
          else Lean.mkAppN fn (args.set! (args.size - 1) a)
        else x
      | some ``LeanQbe.T.vals =>
        if args.size == 2 then
          let ts := args[0]!.consumeMData
          let xs := go args[1]!
          if ts.isAppOf ``List.nil then Lean.mkConst ``Unit.unit
          else if ts.isAppOfArity ``List.cons 3 && xs.isAppOfArity ``Prod.mk 4 then
            let t := ts.getArg! 1; let restTs := ts.getArg! 2
            let hd := go (Lean.mkApp2 (Lean.mkConst ``LeanQbe.T.Arg.val) t (xs.getArg! 2))
            let tl := go (Lean.mkApp2 (Lean.mkConst ``LeanQbe.T.vals) restTs (xs.getArg! 3))
            let valT := Lean.mkApp (Lean.mkConst ``LeanQbe.T.Val) t
            let tupTl := Lean.mkApp3 (Lean.mkConst ``LeanQbe.T.Tup)
              (Lean.mkConst ``LeanQbe.T.Ty) (Lean.mkConst ``LeanQbe.T.Val) restTs
            Lean.mkApp4 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) valT tupTl hd tl
          else Lean.mkAppN fn #[ts, xs]
        else x
      | some ``Prod.mk =>
        if args.size == 4 then Lean.mkAppN fn ((args.set! 2 (go args[2]!)).set! 3 (go args[3]!))
        else x
      | some ``LeanQbe.T.Arg.var | some ``LeanQbe.T.Arg.imm =>
        if args.size ≥ 1 then Lean.mkAppN fn (args.set! (args.size - 1) (go args.back!)) else x
      | _ =>
        if fn.constName? == some ``HAdd.hAdd || fn.constName? == some ``HSub.hSub ||
           fn.constName? == some ``HMul.hMul || fn.constName? == some ``HAnd.hAnd ||
           fn.constName? == some ``HOr.hOr || fn.constName? == some ``HXor.hXor ||
           fn.constName? == some ``HShiftLeft.hShiftLeft ||
           fn.constName? == some ``HShiftRight.hShiftRight ||
           fn.constName? == some ``BitVec.setWidth ||
           fn.constName? == some ``BitVec.signExtend ||
           fn.constName? == some ``BitVec.ult || fn.constName? == some ``BitVec.ule ||
           fn.constName? == some ``BitVec.slt || fn.constName? == some ``BitVec.sle ||
           fn.constName? == some ``BEq.beq || fn.constName? == some ``bne then
          Lean.mkAppN fn (args.map go)
        else x
    | _ => x
  go e

/-- Peel `Blocks.get (Blocks.cons b bs) .here/.there xs` and head beta-redexes in `O(1)`
without mutating the goal or walking continuations. -/
meta partial def peelBlocksGet (e : Lean.Expr) : Lean.Expr :=
  let e := e.consumeMData.headBeta
  if e.isAppOfArity ``LeanQbe.T.Blocks.get 8 then
    let bs := (e.getArg! 5).consumeMData.headBeta
    let idx := (e.getArg! 6).consumeMData.headBeta
    if bs.isAppOfArity ``LeanQbe.T.Blocks.cons 7 then
      if idx.isAppOf ``LeanQbe.T.Member.here then
        peelBlocksGet (Lean.mkApp (bs.getArg! 5) (e.getArg! 7))
      else if idx.isAppOfArity ``LeanQbe.T.Member.there 4 then
        peelBlocksGet <| Lean.mkAppN e.getAppFn
          #[e.getArg! 0, e.getArg! 1, e.getArg! 2, e.getArg! 3,
            bs.getArg! 4, bs.getArg! 6, idx.getArg! 3, e.getArg! 7]
      else e
    else e
  else e

/-- Shallow `O(1)` head normalization of an `Expr Val Cont rs` term: ONLY peels `Blocks.get`,
strips `mdata`, head-betas, and reduces immediate head operands (never walks continuations `k`). -/
meta partial def reduceHeadExpr (e : Lean.Expr) : Lean.Expr :=
  let e := peelBlocksGet e
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  let updArg (idx : Nat) : Lean.Expr :=
    let v' := reduceSmall args[idx]!
    if v' != args[idx]! then Lean.mkAppN fn (args.set! idx v') else e
  match fn.constName? with
  | some ``LeanQbe.T.Expr.let_ =>
    if args.size == 6 then
      let op := args[4]!.consumeMData.headBeta
      let op' :=
        if op.isAppOfArity ``LeanQbe.T.Op.mk 5 || op.isAppOfArity ``LeanQbe.T.op1 5 then
          Lean.mkAppN op.getAppFn (op.getAppArgs.set! 4 (reduceSmall (op.getArg! 4)))
        else if op.isAppOfArity ``LeanQbe.T.op2 7 then
          let oa := op.getAppArgs
          Lean.mkAppN op.getAppFn ((oa.set! 5 (reduceSmall oa[5]!)).set! 6 (reduceSmall oa[6]!))
        else if op.isAppOfArity ``LeanQbe.T.op3 9 then
          let oa := op.getAppArgs
          Lean.mkAppN op.getAppFn
            (((oa.set! 6 (reduceSmall oa[6]!)).set! 7 (reduceSmall oa[7]!)).set! 8
              (reduceSmall oa[8]!))
        else op
      if op' != args[4]! then Lean.mkAppN fn (args.set! 4 op') else e
    else e
  | some ``LeanQbe.T.Expr.load => if args.size == 6 then updArg 4 else e
  | some ``LeanQbe.T.Expr.store =>
    if args.size == 7 then
      let v' := reduceSmall args[4]!; let a' := reduceSmall args[5]!
      if v' != args[4]! || a' != args[5]! then Lean.mkAppN fn ((args.set! 4 v').set! 5 a') else e
    else e
  | some ``LeanQbe.T.Expr.jnz => if args.size == 6 then updArg 3 else e
  | some ``LeanQbe.T.Expr.jump | some ``LeanQbe.T.Expr.exit =>
    if args.size == 6 then updArg 5 else e
  | some ``LeanQbe.T.Expr.ret => if args.size == 4 then updArg 3 else e
  | _ => e

/-- Is `e` already headed by an `Expr` constructor? -/
private meta def isExprHead (e : Lean.Expr) : Bool :=
  match e.getAppFn.consumeMData.constName? with
  | some ``LeanQbe.T.Expr.let_ | some ``LeanQbe.T.Expr.load | some ``LeanQbe.T.Expr.store
  | some ``LeanQbe.T.Expr.jnz | some ``LeanQbe.T.Expr.jump | some ``LeanQbe.T.Expr.ret
  | some ``LeanQbe.T.Expr.exit | some ``LeanQbe.T.Expr.group | some ``LeanQbe.T.Expr.call
  | some ``LeanQbe.T.Expr.hlt => true
  | _ => false

/-- Expose the head `Expr` constructor in `O(1)`: first runs pure `peelBlocksGet`, and only calls
`whnfCore` when a tuple pattern-matching lambda (`fun (x, ()) => ...`) sits at the head. -/
private meta def whnfHeadExpr (e : Lean.Expr) : MetaM Lean.Expr := do
  let e := peelBlocksGet e
  if isExprHead e then return e
  let e' ← whnfCore e
  return peelBlocksGet e'

/-- Expose the head constructor of a stopped goal (`mdata`, head beta, `Blocks.get`, matchers)
ONCE right before returning control to the user (never called during straight-line stepping). -/
private meta def normStoppedGoal (g : MVarId) : TacticM MVarId :=
  g.withContext do
    let ty0 ← instantiateMVars (← g.getType)
    let ty := ty0.consumeMData.headBeta
    if ty.isAppOfArity ``LeanQbe.T.wp 6 then
      let e := ty.getArg! 4
      let e' ← whnfHeadExpr e
      if e' != e || ty != ty0 then
        return ← g.change (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e')) (checkDefEq := false)
    else if ty != ty0 then
      return ← g.change ty (checkDefEq := false)
    return g

private meta def reduceArgVal (tyExpr a : Lean.Expr) : Lean.Expr :=
  let a := a.consumeMData.headBeta
  if (a.isAppOf ``LeanQbe.T.Arg.var || a.isAppOf ``LeanQbe.T.Arg.imm) && a.getAppNumArgs ≥ 1 then
    reduceSmall a.appArg!
  else reduceSmall (Lean.mkApp2 (Lean.mkConst ``LeanQbe.T.Arg.val) tyExpr a)

private meta partial def pureNat? (e : Lean.Expr) : Option Nat :=
  let e := e.consumeMData.headBeta
  match e with
  | .lit (.natVal n) => some n
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then pureNat? (e.getArg! 1)
    else if e.isConstOf ``Nat.zero then some 0
    else if e.isAppOfArity ``Nat.succ 1 then (· + 1) <$> pureNat? (e.getArg! 0)
    else e.nat?

private meta def tyBitsWidthExpr? (t : Lean.Expr) : Option (Lean.Expr × Option Nat) :=
  let t := t.consumeMData.headBeta
  if t.isAppOfArity ``LeanQbe.T.Ty.bits 1 then some (t.getArg! 0, pureNat? (t.getArg! 0))
  else match t.constName? with
    | some ``LeanQbe.T.i8  => some (mkNatLit 8, some 8)
    | some ``LeanQbe.T.i16 => some (mkNatLit 16, some 16)
    | some ``LeanQbe.T.i32 => some (mkNatLit 32, some 32)
    | some ``LeanQbe.T.i64 => some (mkNatLit 64, some 64)
    | _ => none

private meta def bvTypeWidth? (ty : Lean.Expr) : Option Nat :=
  let ty := ty.consumeMData.headBeta
  if ty.isAppOfArity ``BitVec 1 then pureNat? (ty.getArg! 0)
  else if ty.isAppOfArity ``LeanQbe.T.Val 1 then (tyBitsWidthExpr? (ty.getArg! 0)).bind (·.2)
  else none

/-- Extract `(width, unsignedVal)` from a concrete `BitVec` literal (including `setWidth` and
`signExtend` of literals, e.g. C0's `sext 32 64 1#32`). -/
private meta partial def bvLitVal? (e : Lean.Expr) : Option (Nat × Nat) := do
  let e := e.consumeMData.headBeta
  if (e.isAppOf ``LeanQbe.T.Arg.imm || e.isAppOf ``LeanQbe.T.Arg.var) && e.getAppNumArgs ≥ 1 then
    return ← bvLitVal? e.appArg!
  if e.isAppOfArity ``BitVec.ofNat 2 then
    let w ← pureNat? (e.getArg! 0); let v ← pureNat? (e.getArg! 1); return (w, v % (2 ^ w))
  if e.isAppOfArity ``OfNat.ofNat 3 then
    let w ← bvTypeWidth? (e.getArg! 0); let v ← pureNat? (e.getArg! 1); return (w, v % (2 ^ w))
  if e.isAppOfArity ``BitVec.setWidth 3 then
    let w' ← pureNat? (e.getArg! 1); let (_, v) ← bvLitVal? (e.getArg! 2); return (w', v % (2 ^ w'))
  if e.isAppOfArity ``BitVec.signExtend 3 then
    let w' ← pureNat? (e.getArg! 1); let (w0, v) ← bvLitVal? (e.getArg! 2)
    return (w', ((BitVec.ofNat w0 v).signExtend w').toNat)
  none

/-! ## 3. Direct `O(1)` Proof-Term Construction for `Expr.let_` (Zero `g.change`) -/

private meta inductive OpForm where | mk | op1 | op2 | op3 deriving BEq

private meta partial def unpackProdTup (t : Lean.Expr) (acc : Array Lean.Expr) :
    Array Lean.Expr :=
  let t := t.consumeMData.headBeta
  if t.isAppOfArity ``Prod.mk 4 then unpackProdTup (t.getArg! 3) (acc.push (t.getArg! 2)) else acc

private meta def unpackOp? (op : Lean.Expr) : Option (OpForm × Lean.Expr × Array Lean.Expr) :=
  let op := op.consumeMData.headBeta
  if op.isAppOfArity ``LeanQbe.T.Op.mk 5 then
    some (.mk, (op.getArg! 3).consumeMData.headBeta, unpackProdTup (op.getArg! 4) #[])
  else if op.isAppOfArity ``LeanQbe.T.op1 5 then
    some (.op1, (op.getArg! 3).consumeMData.headBeta, #[op.getArg! 4])
  else if op.isAppOfArity ``LeanQbe.T.op2 7 then
    some (.op2, (op.getArg! 4).consumeMData.headBeta, #[op.getArg! 5, op.getArg! 6])
  else if op.isAppOfArity ``LeanQbe.T.op3 9 then
    some (.op3, (op.getArg! 5).consumeMData.headBeta, #[op.getArg! 6, op.getArg! 7, op.getArg! 8])
  else none

private meta def mkRefl0 (ty x : Lean.Expr) : Lean.Expr :=
  Lean.mkApp2 (Lean.mkConst ``Eq.refl [Level.succ Level.zero]) ty x
private meta def mkBvTy (n : Lean.Expr) : Lean.Expr := Lean.mkApp (Lean.mkConst ``BitVec) n
private meta def mkValTy (t : Lean.Expr) : Lean.Expr := Lean.mkApp (Lean.mkConst ``LeanQbe.T.Val) t
private meta def mkOfNatLit (n : Nat) : Lean.Expr :=
  let lit := mkNatLit n
  Lean.mkApp3 (Lean.mkConst ``OfNat.ofNat [Level.zero]) (Lean.mkConst ``Nat) lit
    (Lean.mkApp (Lean.mkConst ``instOfNatNat) lit)
private meta def mkBvLit (w v : Nat) : Lean.Expr :=
  Lean.mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkOfNatLit w) (mkOfNatLit v)

private meta def assignHead1 (g : MVarId) (lem : Name) (prefixArgs : Array Lean.Expr) :
    MetaM MVarId := do
  let cinfo ← getConstInfo lem
  let .forallE _ hkTy _ _ ← instantiateForall cinfo.type prefixArgs
    | throwError "C0HeadStep.assignHead1: unexpected type for {lem}"
  let hk ← mkFreshExprSyntheticOpaqueMVar hkTy
  g.assign (Lean.mkAppN (Lean.mkConst lem) (prefixArgs.push hk))
  return hk.mvarId!

private meta def assignHead2 (g : MVarId) (lem : Name) (prefixArgs : Array Lean.Expr) :
    MetaM (MVarId × MVarId) := do
  let cinfo ← getConstInfo lem
  let .forallE _ sTy body1 _ ← instantiateForall cinfo.type prefixArgs
    | throwError "C0HeadStep.assignHead2: unexpected first binder for {lem}"
  let hSide ← mkFreshExprSyntheticOpaqueMVar sTy
  let .forallE _ hkTy _ _ := body1.instantiate1 hSide
    | throwError "C0HeadStep.assignHead2: unexpected second binder for {lem}"
  let hk ← mkFreshExprSyntheticOpaqueMVar hkTy
  g.assign (Lean.mkAppN (Lean.mkConst lem) ((prefixArgs.push hSide).push hk))
  return (hSide.mvarId!, hk.mvarId!)

private meta def proveClosedDecide? (p : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let s ← saveState
  try
    let m ← mkFreshExprSyntheticOpaqueMVar p
    setGoals [m.mvarId!]
    evalTactic (← `(tactic| first | rfl | decide))
    if (← getUnsolvedGoals).isEmpty then return some (← instantiateMVars m)
    s.restore; return none
  catch _ => s.restore; return none

private meta def unpackCmpCode? (code : Lean.Expr) : Option (Name × Lean.Expr) :=
  match code.getAppFn.constName?, code.getAppNumArgs with
  | some ``LeanQbe.T.OpCode.cmp, 4 =>
    let argTy := (code.getArg! 1).consumeMData.headBeta
    (code.getArg! 0).consumeMData.getAppFn.constName?.map (·, argTy)
  | some ``LeanQbe.T.OpCode.eq,  1 => some (``LeanQbe.T.CmpOp.eq,  code.getArg! 0)
  | some ``LeanQbe.T.OpCode.ne,  1 => some (``LeanQbe.T.CmpOp.ne,  code.getArg! 0)
  | some ``LeanQbe.T.OpCode.ult, 1 => some (``LeanQbe.T.CmpOp.ult, code.getArg! 0)
  | some ``LeanQbe.T.OpCode.ule, 1 => some (``LeanQbe.T.CmpOp.ule, code.getArg! 0)
  | some ``LeanQbe.T.OpCode.ugt, 1 => some (``LeanQbe.T.CmpOp.ugt, code.getArg! 0)
  | some ``LeanQbe.T.OpCode.uge, 1 => some (``LeanQbe.T.CmpOp.uge, code.getArg! 0)
  | some ``LeanQbe.T.OpCode.slt, 1 => some (``LeanQbe.T.CmpOp.slt, code.getArg! 0)
  | some ``LeanQbe.T.OpCode.sle, 1 => some (``LeanQbe.T.CmpOp.sle, code.getArg! 0)
  | some ``LeanQbe.T.OpCode.sgt, 1 => some (``LeanQbe.T.CmpOp.sgt, code.getArg! 0)
  | some ``LeanQbe.T.OpCode.sge, 1 => some (``LeanQbe.T.CmpOp.sge, code.getArg! 0)
  | _, _ => none

private meta def cmpLemmas (cmpNm : Name) : Name × Name :=
  match cmpNm with
  | ``LeanQbe.T.CmpOp.eq  => (``head_wp_cmp_eq,  ``head_wp_op2_cmp_eq)
  | ``LeanQbe.T.CmpOp.ne  => (``head_wp_cmp_ne,  ``head_wp_op2_cmp_ne)
  | ``LeanQbe.T.CmpOp.ult => (``head_wp_cmp_ult, ``head_wp_op2_cmp_ult)
  | ``LeanQbe.T.CmpOp.ule => (``head_wp_cmp_ule, ``head_wp_op2_cmp_ule)
  | ``LeanQbe.T.CmpOp.ugt => (``head_wp_cmp_ugt, ``head_wp_op2_cmp_ugt)
  | ``LeanQbe.T.CmpOp.uge => (``head_wp_cmp_uge, ``head_wp_op2_cmp_uge)
  | ``LeanQbe.T.CmpOp.slt => (``head_wp_cmp_slt, ``head_wp_op2_cmp_slt)
  | ``LeanQbe.T.CmpOp.sle => (``head_wp_cmp_sle, ``head_wp_op2_cmp_sle)
  | ``LeanQbe.T.CmpOp.sgt => (``head_wp_cmp_sgt, ``head_wp_op2_cmp_sgt)
  | ``LeanQbe.T.CmpOp.sge => (``head_wp_cmp_sge, ``head_wp_op2_cmp_sge)
  | _                     => (``head_wp_cmp_bits, ``head_wp_op2_cmp_bits)

/-- Step a single `Expr.let_` directly in `O(1)` without calling `MVarId.change`. -/
private meta def stepLetHead (g : MVarId) (wpArgs : Array Lean.Expr) (op k : Lean.Expr) :
    TacticM (Option (List MVarId)) := do
  let Γ := wpArgs[0]!; let rs := wpArgs[1]!; let Q := wpArgs[2]!
  let X := wpArgs[3]!; let m := wpArgs[5]!
  let some (form, code, opArgs) := unpackOp? op | return none
  let isMk := form == .mk
  let boolTy := Lean.mkConst ``Bool
  let tyBool := Lean.mkConst ``LeanQbe.T.Ty.bool
  let codeNm := code.getAppFn.constName?
  let doUnaryBits (lemMk lemOp1 : Name) (nExpr a : Lean.Expr) : TacticM (Option (List MVarId)) := do
    let va := reduceArgVal (Lean.mkApp (Lean.mkConst ``LeanQbe.T.Ty.bits) nExpr) a
    let hk ← assignHead1 g (if isMk then lemMk else lemOp1)
      #[Γ, rs, Q, X, m, nExpr, a, va, k, mkRefl0 (mkBvTy nExpr) va]
    return some [hk]
  let doBinBits (lemMk lemOp2 : Name) (nExpr a b : Lean.Expr) :
      TacticM (Option (List MVarId)) := do
    let bvTy := mkBvTy nExpr; let tBits := Lean.mkApp (Lean.mkConst ``LeanQbe.T.Ty.bits) nExpr
    let va := reduceArgVal tBits a; let vb := reduceArgVal tBits b
    let hk ← assignHead1 g (if isMk then lemMk else lemOp2)
      #[Γ, rs, Q, X, m, nExpr, a, b, va, vb, k, mkRefl0 bvTy va, mkRefl0 bvTy vb]
    return some [hk]
  let doBinBool (lemMk lemOp2 : Name) (a b : Lean.Expr) : TacticM (Option (List MVarId)) := do
    let va := reduceArgVal tyBool a; let vb := reduceArgVal tyBool b
    let hk ← assignHead1 g (if isMk then lemMk else lemOp2)
      #[Γ, rs, Q, X, m, a, b, va, vb, k, mkRefl0 boolTy va, mkRefl0 boolTy vb]
    return some [hk]
  let doShift (lemImmMk lemImmOp2 lemMk lemOp2 : Name) (nExpr a b : Lean.Expr) :
      TacticM (Option (List MVarId)) := do
    let bvTy := mkBvTy nExpr; let tBits := Lean.mkApp (Lean.mkConst ``LeanQbe.T.Ty.bits) nExpr
    let va := reduceArgVal tBits a; let vb := reduceArgVal tBits b
    if let some (w, v) := bvLitVal? vb then
      let cLit := mkOfNatLit (v % w)
      let bVal := Lean.mkApp2 (Lean.mkConst ``LeanQbe.T.Arg.val) tBits b
      let natTy := Lean.mkConst ``Nat
      let modLhs := Lean.mkApp6 (Lean.mkConst ``HMod.hMod [Level.zero, Level.zero, Level.zero])
        natTy natTy natTy
        (Lean.mkApp2 (Lean.mkConst ``instHMod [Level.zero]) natTy (Lean.mkConst ``Nat.instMod))
        (Lean.mkApp2 (Lean.mkConst ``BitVec.toNat) nExpr bVal) nExpr
      let eqProp := Lean.mkApp3 (Lean.mkConst ``Eq [Level.succ Level.zero]) natTy modLhs cLit
      if let some hcPf ← proveClosedDecide? eqProp then
        let hk ← assignHead1 g (if isMk then lemImmMk else lemImmOp2)
          #[Γ, rs, Q, X, m, nExpr, a, b, va, cLit, k, mkRefl0 bvTy va, hcPf]
        return some [hk]
    doBinBits lemMk lemOp2 nExpr a b
  let doCast (lemMk lemOp1 lemLitMk lemLitOp1 : Name) (isTrunc isSext : Bool)
      (nExpr wExpr a : Lean.Expr) : TacticM (Option (List MVarId)) := do
    let tIn := Lean.mkApp (Lean.mkConst ``LeanQbe.T.Ty.bits) nExpr
    let va := reduceArgVal tIn a
    let leProp := Lean.mkApp4 (Lean.mkConst ``LE.le [Level.zero]) (Lean.mkConst ``Nat)
      (Lean.mkConst ``instLENat)
      (if isTrunc then wExpr else nExpr) (if isTrunc then nExpr else wExpr)
    let some hlePf ← proveClosedDecide? leProp | return none
    if let (some wNat, some (w0, v0)) := (pureNat? wExpr, bvLitVal? va) then
      let resNat := if isSext then ((BitVec.ofNat w0 v0).signExtend wNat).toNat else v0 % (2 ^ wNat)
      let vLit := mkBvLit wNat resNat
      let aVal := Lean.mkApp2 (Lean.mkConst ``LeanQbe.T.Arg.val) tIn a
      let castApp := Lean.mkApp3
        (Lean.mkConst (if isSext then ``BitVec.signExtend else ``BitVec.setWidth)) nExpr wExpr aVal
      let eqProp := Lean.mkApp3 (Lean.mkConst ``Eq [Level.succ Level.zero])
        (mkBvTy wExpr) castApp vLit
      if let some hvPf ← proveClosedDecide? eqProp then
        let hk ← assignHead1 g (if isMk then lemLitMk else lemLitOp1)
          #[Γ, rs, Q, X, m, nExpr, wExpr, a, vLit, k, hlePf, hvPf]
        return some [hk]
    let hk ← assignHead1 g (if isMk then lemMk else lemOp1)
      #[Γ, rs, Q, X, m, nExpr, wExpr, a, va, k, mkRefl0 (mkBvTy nExpr) va, hlePf]
    return some [hk]
  let doDiv (lemMk lemOp2 : Name) (nExpr a b : Lean.Expr) : TacticM (Option (List MVarId)) := do
    let bvTy := mkBvTy nExpr; let tBits := Lean.mkApp (Lean.mkConst ``LeanQbe.T.Ty.bits) nExpr
    let va := reduceArgVal tBits a; let vb := reduceArgVal tBits b
    let (hSide, hk) ← assignHead2 g (if isMk then lemMk else lemOp2)
      #[Γ, rs, Q, X, m, nExpr, a, b, va, vb, k, mkRefl0 bvTy va, mkRefl0 bvTy vb]
    let sideClosed ← do
      let s2 ← saveState
      try
        setGoals [hSide]; evalTactic (← `(tactic| c0_div_bound))
        if (← getUnsolvedGoals).isEmpty then pure true else do s2.restore; pure false
      catch _ => s2.restore; pure false
    return some ((if sideClosed then [] else [hSide]) ++ [hk])
  -- Unary ops
  if (form == .op1 || isMk) && opArgs.size == 1 then
    let a := opArgs[0]!
    match codeNm, code.getAppNumArgs with
    | some ``LeanQbe.T.OpCode.copy, 1 =>
      let t := code.getArg! 0; let va := reduceArgVal t a
      let hk ← assignHead1 g (if isMk then ``head_wp_copy else ``head_wp_op1_copy)
        #[Γ, rs, Q, X, m, t, a, va, k, mkRefl0 (mkValTy t) va]
      return some [hk]
    | some ``LeanQbe.T.OpCode.neg, 1 =>
      if let some (nE, _) := tyBitsWidthExpr? (code.getArg! 0) then
        return ← doUnaryBits ``head_wp_neg ``head_wp_op1_neg nE a
    | some ``LeanQbe.T.OpCode.not, 1 =>
      let t := (code.getArg! 0).consumeMData.headBeta
      if t.isConstOf ``LeanQbe.T.Ty.bool then
        let va := reduceArgVal tyBool a
        let hk ← assignHead1 g (if isMk then ``head_wp_not_bool else ``head_wp_op1_not_bool)
          #[Γ, rs, Q, X, m, a, va, k, mkRefl0 boolTy va]
        return some [hk]
      else if let some (nE, _) := tyBitsWidthExpr? t then
        return ← doUnaryBits ``head_wp_not_bits ``head_wp_op1_not_bits nE a
    | some ``LeanQbe.T.OpCode.clz, 1 =>
      return ← doUnaryBits ``head_wp_clz ``head_wp_op1_clz (code.getArg! 0) a
    | some ``LeanQbe.T.OpCode.ctz, 1 =>
      return ← doUnaryBits ``head_wp_ctz ``head_wp_op1_ctz (code.getArg! 0) a
    | some ``LeanQbe.T.OpCode.popcnt, 1 =>
      return ← doUnaryBits ``head_wp_popcnt ``head_wp_op1_popcnt (code.getArg! 0) a
    | some ``LeanQbe.T.OpCode.rbit, 1 =>
      return ← doUnaryBits ``head_wp_rbit ``head_wp_op1_rbit (code.getArg! 0) a
    | some ``LeanQbe.T.OpCode.zext, 2 =>
      return ← doCast ``head_wp_zext ``head_wp_op1_zext ``head_wp_zext_lit ``head_wp_op1_zext_lit
        false false (code.getArg! 0) (code.getArg! 1) a
    | some ``LeanQbe.T.OpCode.sext, 2 =>
      return ← doCast ``head_wp_sext ``head_wp_op1_sext ``head_wp_sext_lit ``head_wp_op1_sext_lit
        false true (code.getArg! 0) (code.getArg! 1) a
    | some ``LeanQbe.T.OpCode.trunc, 2 =>
      return ← doCast ``head_wp_trunc ``head_wp_op1_trunc ``head_wp_trunc_lit
        ``head_wp_op1_trunc_lit true false (code.getArg! 0) (code.getArg! 1) a
    | some ``LeanQbe.T.OpCode.ofBool, 1 =>
      let va := reduceArgVal tyBool a
      let hk ← assignHead1 g (if isMk then ``head_wp_ofBool else ``head_wp_op1_ofBool)
        #[Γ, rs, Q, X, m, code.getArg! 0, a, va, k, mkRefl0 boolTy va]
      return some [hk]
    | _, _ => pure ()
  -- Binary ops
  if (form == .op2 || isMk) && opArgs.size == 2 then
    let a := opArgs[0]!; let b := opArgs[1]!
    if let some (cmpNm, argTy) := unpackCmpCode? code then
      if argTy.isConstOf ``LeanQbe.T.Ty.bool then
        let va := reduceArgVal tyBool a; let vb := reduceArgVal tyBool b
        let hk ← assignHead1 g (if isMk then ``head_wp_cmp_bool else ``head_wp_op2_cmp_bool)
          #[Γ, rs, Q, X, m, Lean.mkConst cmpNm, a, b, va, vb, k,
            mkRefl0 boolTy va, mkRefl0 boolTy vb]
        return some [hk]
      else if let some (nE, _) := tyBitsWidthExpr? argTy then
        let (lemMk, lemOp2) := cmpLemmas cmpNm
        if lemMk == ``head_wp_cmp_bits then
          let bvTy := mkBvTy nE; let tBits := Lean.mkApp (Lean.mkConst ``LeanQbe.T.Ty.bits) nE
          let va := reduceArgVal tBits a; let vb := reduceArgVal tBits b
          let hk ← assignHead1 g (if isMk then lemMk else lemOp2)
            #[Γ, rs, Q, X, m, Lean.mkConst cmpNm, nE, a, b, va, vb, k,
              mkRefl0 bvTy va, mkRefl0 bvTy vb]
          return some [hk]
        else return ← doBinBits lemMk lemOp2 nE a b
    if code.getAppNumArgs == 1 then
      let arg0 := (code.getArg! 0).consumeMData.headBeta
      match codeNm with
      | some ``LeanQbe.T.OpCode.add =>
        if let some (nE, _) := tyBitsWidthExpr? arg0 then
          return ← doBinBits ``head_wp_add ``head_wp_op2_add nE a b
      | some ``LeanQbe.T.OpCode.sub =>
        if let some (nE, _) := tyBitsWidthExpr? arg0 then
          return ← doBinBits ``head_wp_sub ``head_wp_op2_sub nE a b
      | some ``LeanQbe.T.OpCode.mul =>
        if let some (nE, _) := tyBitsWidthExpr? arg0 then
          return ← doBinBits ``head_wp_mul ``head_wp_op2_mul nE a b
      | some ``LeanQbe.T.OpCode.and =>
        if arg0.isConstOf ``LeanQbe.T.Ty.bool then
          return ← doBinBool ``head_wp_and_bool ``head_wp_op2_and_bool a b
        else if let some (nE, _) := tyBitsWidthExpr? arg0 then
          return ← doBinBits ``head_wp_and ``head_wp_op2_and nE a b
      | some ``LeanQbe.T.OpCode.or =>
        if arg0.isConstOf ``LeanQbe.T.Ty.bool then
          return ← doBinBool ``head_wp_or_bool ``head_wp_op2_or_bool a b
        else if let some (nE, _) := tyBitsWidthExpr? arg0 then
          return ← doBinBits ``head_wp_or ``head_wp_op2_or nE a b
      | some ``LeanQbe.T.OpCode.xor =>
        if arg0.isConstOf ``LeanQbe.T.Ty.bool then
          return ← doBinBool ``head_wp_xor_bool ``head_wp_op2_xor_bool a b
        else if let some (nE, _) := tyBitsWidthExpr? arg0 then
          return ← doBinBits ``head_wp_xor ``head_wp_op2_xor nE a b
      | some ``LeanQbe.T.OpCode.shl =>
        if let some (nE, _) := tyBitsWidthExpr? arg0 then
          return ← doShift ``head_wp_shl_imm ``head_wp_op2_shl_imm
            ``head_wp_shl ``head_wp_op2_shl nE a b
      | some ``LeanQbe.T.OpCode.lshr =>
        if let some (nE, _) := tyBitsWidthExpr? arg0 then
          return ← doShift ``head_wp_lshr_imm ``head_wp_op2_lshr_imm
            ``head_wp_lshr ``head_wp_op2_lshr nE a b
      | some ``LeanQbe.T.OpCode.ashr =>
        if let some (nE, _) := tyBitsWidthExpr? arg0 then
          return ← doShift ``head_wp_ashr_imm ``head_wp_op2_ashr_imm
            ``head_wp_ashr ``head_wp_op2_ashr nE a b
      | some ``LeanQbe.T.OpCode.rotl =>
        if let some (nE, _) := tyBitsWidthExpr? arg0 then
          return ← doBinBits ``head_wp_rotl ``head_wp_op2_rotl nE a b
      | some ``LeanQbe.T.OpCode.rotr =>
        if let some (nE, _) := tyBitsWidthExpr? arg0 then
          return ← doBinBits ``head_wp_rotr ``head_wp_op2_rotr nE a b
      | some ``LeanQbe.T.OpCode.udiv => return ← doDiv ``head_wp_udiv ``head_wp_op2_udiv arg0 a b
      | some ``LeanQbe.T.OpCode.urem => return ← doDiv ``head_wp_urem ``head_wp_op2_urem arg0 a b
      | some ``LeanQbe.T.OpCode.sdiv => return ← doDiv ``head_wp_sdiv ``head_wp_op2_sdiv arg0 a b
      | some ``LeanQbe.T.OpCode.srem => return ← doDiv ``head_wp_srem ``head_wp_op2_srem arg0 a b
      | some ``LeanQbe.T.OpCode.udiv0 =>
        return ← doBinBits ``head_wp_udiv0 ``head_wp_op2_udiv0 arg0 a b
      | some ``LeanQbe.T.OpCode.sdiv0 =>
        return ← doBinBits ``head_wp_sdiv0 ``head_wp_op2_sdiv0 arg0 a b
      | some ``LeanQbe.T.OpCode.umulw =>
        return ← doBinBits ``head_wp_umulw ``head_wp_op2_umulw arg0 a b
      | _ => pure ()
  -- Ternary ops
  if (form == .op3 || isMk) && opArgs.size == 3 && code.getAppNumArgs == 1 then
    let a := opArgs[0]!; let b := opArgs[1]!; let c := opArgs[2]!; let arg0 := code.getArg! 0
    match codeNm with
    | some ``LeanQbe.T.OpCode.select =>
      let valTy := mkValTy arg0
      let vc := reduceArgVal tyBool a; let va := reduceArgVal arg0 b; let vb := reduceArgVal arg0 c
      let hk ← assignHead1 g (if isMk then ``head_wp_select else ``head_wp_op3_select)
        #[Γ, rs, Q, X, m, arg0, a, b, c, vc, va, vb, k,
          mkRefl0 boolTy vc, mkRefl0 valTy va, mkRefl0 valTy vb]
      return some [hk]
    | some ``LeanQbe.T.OpCode.addc | some ``LeanQbe.T.OpCode.subb =>
      let bvTy := mkBvTy arg0; let tBits := Lean.mkApp (Lean.mkConst ``LeanQbe.T.Ty.bits) arg0
      let va := reduceArgVal tBits a; let vb := reduceArgVal tBits b
      let vc := reduceArgVal tyBool c
      let lem := match codeNm with
        | some ``LeanQbe.T.OpCode.addc => if isMk then ``head_wp_addc else ``head_wp_op3_addc
        | _ => if isMk then ``head_wp_subb else ``head_wp_op3_subb
      let hk ← assignHead1 g lem
        #[Γ, rs, Q, X, m, arg0, a, b, c, va, vb, vc, k,
          mkRefl0 bvTy va, mkRefl0 bvTy vb, mkRefl0 boolTy vc]
      return some [hk]
    | _ => pure ()
  return none

/-! ## 4. Two-Level `(footprintHead, AddrKey)` Memory Solver (`O(1)` Dispatch) -/

private meta partial def sepClauses (e : Lean.Expr) : List Lean.Expr :=
  let e := e.consumeMData
  if e.isAppOf ``Std.ExtHashMap.sep && e.getAppNumArgs ≥ 2 then
    sepClauses (e.getArg! (e.getAppNumArgs - 2)) ++
      sepClauses (e.getArg! (e.getAppNumArgs - 1))
  else [e]

private meta def footprints : TacticM (Array Name) := withMainContext do
  let mut keys : Array Name := #[]
  for d in (← getLCtx).decls.toArray.reverse do
    let some d := d | continue
    if d.isImplementationDetail then continue
    let t := (← instantiateMVars d.type).consumeMData
    if t.isAppOf ``Std.ExtHashMap.sep && t.getAppNumArgs ≥ 3 then
      for c in sepClauses t.appFn! do
        if let some k := c.getAppFn.consumeMData.constName? then
          unless keys.contains k do keys := keys.push k
  return keys

private meta def closeWith (g : MVarId) (tac : TSyntax `tactic) : TacticM Bool := do
  if ← g.isAssigned then return true
  let s ← saveState
  try
    setGoals [g]; evalTactic tac
    if (← getUnsolvedGoals).isEmpty then return true
    s.restore; return false
  catch _ => s.restore; return false

private meta def closeFrameFast (g : MVarId) : TacticM Bool := do
  if ← g.isAssigned then return true
  let s ← saveState
  try withReducible g.assumption; return true
  catch _ => s.restore; withReducible (closeWith g (← `(tactic| c0_frame)))

private meta def closeBoundFast (g : MVarId) : TacticM Bool := do
  if ← g.isAssigned then return true
  let s ← saveState
  try g.assumption; return true catch _ => s.restore
  let s2 ← saveState
  try g.refl; return true catch _ => s2.restore
  closeWith g (← `(tactic| c0_bound))

private meta def ppGoalType (g : MVarId) : TacticM String :=
  g.withContext do return (← Meta.ppExpr (← instantiateMVars (← g.getType))).pretty

private meta inductive MemTryRes where
  | ok | applyFailed | frameFailed (msg : String) | sideFailed (msg : String)
  | unassigned (msg : String)

private meta def tryHeadMemLemma (g : MVarId) (nm : Name) : TacticM MemTryRes := do
  let s ← saveState
  let gs ← try withReducible <| g.apply (← mkConstWithFreshMVarLevels nm)
    catch _ => s.restore; return .applyFailed
  for g' in gs do
    let ty ← instantiateMVars (← g'.getType)
    if ty.isAppOf ``Std.ExtHashMap.sep then
      unless ← closeFrameFast g' do
        let msg ← ppGoalType g'; s.restore; return .frameFailed msg
  for g' in gs do
    if ← g'.isAssigned then continue
    if ← isProp (← g'.getType) then
      unless ← closeBoundFast g' do
        let msg ← ppGoalType g'; s.restore; return .sideFailed msg
  for g' in gs do
    unless ← g'.isAssigned do
      let msg ← ppGoalType g'; s.restore; return .unassigned msg
  return .ok

private meta def formatHeadMemDiag (isLoad : Bool) (goalStr : String) (keys untagged : Array Name)
    (triedCount : Nat) (nearMisses : Array String) : String :=
  let attr := if isLoad then "c0_load" else "c0_store"
  let header := s!"c0_hstep: no @[{attr}] lemma closed:\n  {goalStr}"
  let fpLine :=
    if keys.isEmpty then "\nfootprints: none (no separation-logic `⋆` hypothesis in local context)"
    else s!"\nfootprints: {keys}"
  let untaggedLine :=
    if untagged.isEmpty then "" else s!"\nuntagged footprints (missing @[{attr}]?): {untagged}"
  let detailLine :=
    if !nearMisses.isEmpty then
      let shown := nearMisses.toList.take 4
      let extra := if nearMisses.size > 4 then s!"\n  ... ({nearMisses.size - 4} more)" else ""
      "\ncandidate failures:\n" ++ String.intercalate "\n" shown ++ extra
    else if triedCount > 0 then
      s!"\nchecked {triedCount} @[{attr}] lemma(s), none matched the goal address/type"
    else ""
  header ++ fpLine ++ untaggedLine ++ detailLine

/-- Close a `loadVal m t addr = some ?v` (`isLoad := true`) or
`storeOk m t addr ∧ (?P ⋆ ?R) (storeMem m t addr val)` goal using two-level
`(footprintHead, AddrKey)` dispatch (`O(1)` on normal loads/stores), with a full-footprint
fallback on miss for reducible/`let`-bound address aliases. -/
meta def headMemSolveRes (isLoad : Bool) (g : MVarId) (addr : Lean.Expr) :
    TacticM (Except String Unit) := do
  setGoals [g]
  let keys ← footprints
  let env ← getEnv
  let mut tried : NameSet := {}
  let mut triedCount : Nat := 0
  let mut nearMisses : Array String := #[]
  let tryBatch (lems : Array Name) (tried : NameSet) (cnt : Nat) (near : Array String) :
      TacticM (Bool × NameSet × Nat × Array String) := do
    let mut tr := tried; let mut c := cnt; let mut nmArr := near
    for nm in lems do
      if tr.contains nm then continue
      tr := tr.insert nm; c := c + 1
      match ← tryHeadMemLemma g nm with
      | .ok => return (true, tr, c, nmArr)
      | .applyFailed => pure ()
      | .frameFailed s => nmArr := nmArr.push s!"  - `{nm}`: frame failed: {s}"
      | .sideFailed s => nmArr := nmArr.push s!"  - `{nm}`: side goal failed: {s}"
      | .unassigned s => nmArr := nmArr.push s!"  - `{nm}`: unassigned goal: {s}"
    return (false, tr, c, nmArr)
  -- Pass 1: `O(1)` two-level `(footprintHead, AddrKey)` bucket lookup across all footprints
  for k in keys do
    let (ok, tr, c, nr) ← tryBatch (C0Step.c0MemLemmasForAddr env isLoad k addr)
      tried triedCount nearMisses
    tried := tr; triedCount := c; nearMisses := nr
    if ok then return .ok ()
  -- Pass 2: Completeness fallback for any untried lemmas (reducible/`let`-bound aliases)
  let mut untagged : Array Name := #[]
  for k in keys do
    let allLems := C0Step.c0MemLemmas env isLoad k
    if allLems.isEmpty then untagged := untagged.push k
    let (ok, tr, c, nr) ← tryBatch allLems tried triedCount nearMisses
    tried := tr; triedCount := c; nearMisses := nr
    if ok then return .ok ()
  return .error (formatHeadMemDiag isLoad (← ppGoalType g) keys untagged triedCount nearMisses)

/-- Throwing variant of `headMemSolveRes`. -/
meta def headMemSolve (isLoad : Bool) (g : MVarId) (addr : Lean.Expr) : TacticM Unit := do
  match ← headMemSolveRes isLoad g addr with
  | .ok () => pure ()
  | .error msg => throwError msg

/-! ## 5. Configurable `O(1)` Head-Only Stepper (`HeadStepConfig`) -/

/-- Configuration controlling `Expr.group` unrolling, `Expr.jnz` splitting/pruning, and strict
memory diagnostics. -/
meta structure HeadStepConfig where
  unrollGroup : Bool := true
  splitJnz : Bool := true
  pruneJnz : Bool := true
  strictMem : Bool := false

/-- Result of a single head-stepper attempt. -/
meta inductive HeadStepRes where
  | progressed
  | stuck
  | memFailed (msg : String)

private meta def clearStaleMem (m0 : Lean.Expr) : TacticM Unit := withMainContext do
  let .fvar mId := m0 | return
  for d in (← getLCtx).decls.toArray.reverse do
    let some d := d | continue
    let t ← instantiateMVars d.type
    if t.isAppOf ``Std.ExtHashMap.sep && t.appArg! == m0 then
      try liftMetaTactic1 fun g => some <$> g.clear d.fvarId catch _ => pure ()
  try liftMetaTactic1 fun g => some <$> g.clear mId catch _ => pure ()

private meta def findJoinHyp (jId : FVarId) : TacticM (Option Lean.Expr) := withMainContext do
  for d in (← getLCtx).decls.toArray.reverse do
    let some d := d | continue
    let ok ← forallTelescopeReducing d.type fun xs concl => do
      if xs.size < 1 then return false
      let prem ← inferType xs[xs.size - 1]!
      return concl.getAppFn.isFVarOf jId && prem.isAppOf ``LeanQbe.T.wp
    if ok then return some d.toExpr
  return none

/-- Single `O(1)` symbolic-execution step on the main goal (zero `MVarId.change` on straight-line
`let_` / `load` / `store` / `jnz` / `jump` / `ret` / `exit` steps). -/
meta def headStepOnceRes (cfg : HeadStepConfig := {}) : TacticM HeadStepRes := withMainContext do
  let g ← getMainGoal
  let ty0 ← instantiateMVars (← g.getType)
  let ty := ty0.consumeMData.headBeta
  -- 1. Strip `a ≤ b ∧ P` goals automatically
  if ty.isAppOfArity ``And 2 then
    let lhs := (ty.getArg! 0).consumeMData.headBeta
    if lhs.isAppOfArity ``LE.le 4 && (lhs.getArg! 0).consumeMData.isConstOf ``Nat then
      if let some hlePf ← proveClosedDecide? lhs then
        let rhs := ty.getArg! 1
        let hp ← mkFreshExprSyntheticOpaqueMVar rhs
        g.assign (Lean.mkAppN (Lean.mkConst ``head_strip_le)
          #[lhs.getArg! 2, lhs.getArg! 3, rhs, hlePf, hp])
        setGoals [hp.mvarId!]
        return .progressed
    return .stuck
  -- 2. Unfold `Func.wp Γ fn_body ...` WITHOUT calling `c0_let_simp`
  if ty.isAppOf ``LeanQbe.T.Func.wp && ty.getAppNumArgs ≥ 4 then
    let some c := (ty.getArg! 3).consumeMData.getAppFn.constName? | return .stuck
    evalTactic (← `(tactic| unfold LeanQbe.T.Func.wp $(mkIdent c):ident))
    return .progressed
  -- 3. Dispatch on head constructor of `wp Γ Q X e m`
  if ty.isAppOfArity ``LeanQbe.T.wp 6 then
    let wpArgs := ty.getAppArgs
    let Γ := wpArgs[0]!; let rs := wpArgs[1]!; let Q := wpArgs[2]!
    let X := wpArgs[3]!; let m := wpArgs[5]!
    let e ← whnfHeadExpr wpArgs[4]!
    match e.getAppFn.constName? with
    | some ``LeanQbe.T.Expr.let_ =>
      if e.getAppNumArgs != 6 then return .stuck
      let s ← saveState
      try
        match ← stepLetHead g wpArgs (e.getArg! 4) (e.getArg! 5) with
        | some gs => setGoals gs; return .progressed
        | none => s.restore; return .stuck
      catch _ => s.restore; return .stuck
    | some ``LeanQbe.T.Expr.load =>
      if e.getAppNumArgs != 6 then return .stuck
      let s ← saveState
      let t := e.getArg! 3; let a := e.getArg! 4; let k := e.getArg! 5
      let addr := reduceArgVal (Lean.mkConst ``LeanQbe.T.i64) a
      let vMVar ← mkFreshExprMVar (some (mkValTy t))
      let (hl, hk) ← assignHead2 g ``head_wp_load
        #[Γ, rs, Q, X, m, t, a, addr, k, vMVar, mkRefl0 (mkBvTy (mkNatLit 64)) addr]
      match ← headMemSolveRes true hl addr with
      | .ok () => setGoals [hk]; return .progressed
      | .error msg => s.restore; return .memFailed msg
    | some ``LeanQbe.T.Expr.store =>
      if e.getAppNumArgs != 7 then return .stuck
      let s ← saveState
      let t := e.getArg! 3; let v := e.getArg! 4; let a := e.getArg! 5; let k := e.getArg! 6
      let val := reduceArgVal t v
      let addr := reduceArgVal (Lean.mkConst ``LeanQbe.T.i64) a
      let memTy ← inferType m
      let memPredTy := Lean.Expr.forallE `m memTy (.sort Level.zero) .default
      let pMVar ← mkFreshExprMVar (some memPredTy)
      let rMVar ← mkFreshExprMVar (some memPredTy)
      let (hs, hk) ← assignHead2 g ``head_wp_store
        #[Γ, rs, Q, X, m, t, v, a, val, addr, k, pMVar, rMVar,
          mkRefl0 (mkValTy t) val, mkRefl0 (mkBvTy (mkNatLit 64)) addr]
      match ← headMemSolveRes false hs addr with
      | .ok () =>
        let (_, hk') ← hk.intro `m
        let (hMemId, hk'') ← hk'.intro `hm
        setGoals [hk'']
        let hasEmp ← hk''.withContext do
          let hmTy ← instantiateMVars (← hMemId.getType)
          return hmTy.isAppOf ``Std.ExtHashMap.sep &&
            (sepClauses hmTy.appFn!).any (·.consumeMData.isConstOf ``Std.ExtHashMap.emp)
        if hasEmp then
          let hIdent := mkIdent `hm
          evalTactic (← `(tactic| try simp only [Std.ExtHashMap.sep_emp] at $hIdent:ident))
        clearStaleMem m
        return .progressed
      | .error msg => s.restore; return .memFailed msg
    | some ``LeanQbe.T.Expr.jnz =>
      if !cfg.splitJnz || e.getAppNumArgs != 6 then return .stuck
      let c := e.getArg! 3; let e1 := e.getArg! 4; let e2 := e.getArg! 5
      let vc := reduceArgVal (Lean.mkConst ``LeanQbe.T.Ty.bool) c
      let (h1, h2) ← assignHead2 g ``head_wp_jnz
        #[Γ, rs, Q, X, m, c, vc, e1, e2, mkRefl0 (Lean.mkConst ``Bool) vc]
      let processArm (arm : MVarId) : TacticM (Option MVarId) := do
        let (_, arm') ← arm.intro `hc
        setGoals [arm']
        let hc := mkIdent `hc
        evalTactic (← `(tactic| c0_cond $hc))
        if cfg.pruneJnz then
          evalTactic (← `(tactic| try (first
            | exact ($hc).elim | exact absurd rfl $hc | exact $hc rfl
            | exact absurd trivial $hc | (exfalso; c0_bound))))
        return (← getUnsolvedGoals).head?
      let mut out : Array MVarId := #[]
      if let some a1 ← processArm h1 then out := out.push a1
      if let some a2 ← processArm h2 then out := out.push a2
      setGoals out.toList
      return .progressed
    | some ``LeanQbe.T.Expr.jump =>
      if e.getAppNumArgs != 6 then return .stuck
      let ts := e.getArg! 3; let L := e.getArg! 4; let args := e.getArg! 5
      let L' := reduceSmall L
      let vs := reduceSmall (Lean.mkApp2 (Lean.mkConst ``LeanQbe.T.vals) ts args)
      let contTy := Lean.mkApp (Lean.mkConst ``LeanQbe.T.Cont) ts
      let tupTy := Lean.mkApp3 (Lean.mkConst ``LeanQbe.T.Tup)
        (Lean.mkConst ``LeanQbe.T.Ty) (Lean.mkConst ``LeanQbe.T.Val) ts
      let hk ← assignHead1 g ``head_wp_jump
        #[Γ, rs, Q, X, m, ts, L, L', args, vs, mkRefl0 contTy L', mkRefl0 tupTy vs]
      setGoals [hk]; return .progressed
    | some ``LeanQbe.T.Expr.ret =>
      if e.getAppNumArgs != 4 then return .stuck
      let args := e.getArg! 3
      let vs := reduceSmall (Lean.mkApp2 (Lean.mkConst ``LeanQbe.T.vals) rs args)
      let tupTy := Lean.mkApp3 (Lean.mkConst ``LeanQbe.T.Tup)
        (Lean.mkConst ``LeanQbe.T.Ty) (Lean.mkConst ``LeanQbe.T.Val) rs
      let hk ← assignHead1 g ``head_wp_ret #[Γ, rs, Q, X, m, args, vs, mkRefl0 tupTy vs]
      setGoals [hk]; return .progressed
    | some ``LeanQbe.T.Expr.exit =>
      if e.getAppNumArgs != 6 then return .stuck
      let f := e.getArg! 3; let as := e.getArg! 4; let args := e.getArg! 5
      let vs := reduceSmall (Lean.mkApp2 (Lean.mkConst ``LeanQbe.T.vals) as args)
      let tupTy := Lean.mkApp3 (Lean.mkConst ``LeanQbe.T.Tup)
        (Lean.mkConst ``LeanQbe.T.Ty) (Lean.mkConst ``LeanQbe.T.Val) as
      let hk ← assignHead1 g ``head_wp_exit #[Γ, rs, Q, X, m, as, f, args, vs, mkRefl0 tupTy vs]
      setGoals [hk]; return .progressed
    | some ``LeanQbe.T.Expr.group =>
      if cfg.unrollGroup && e.getAppNumArgs == 6 then
        if let .lam _ _ b _ := (e.getArg! 4).consumeMData then
          if !b.hasLooseBVars then
            setGoals [← normStoppedGoal g]
            let J := mkIdent `J; let hJ := mkIdent `hJ
            evalTactic (← `(tactic| refine LeanQbe.T.wp_unroll_group fun $J:ident $hJ:ident => ?_))
            return .progressed
      return .stuck
    | _ => return .stuck
  -- 4. Unfold join-continuation hypothesis `hJ`
  if let .fvar jId := (reduceSmall ty.getAppFn).consumeMData then
    if let some h ← findJoinHyp jId then
      let s ← saveState
      try let gs ← g.apply h; setGoals gs; return .progressed
      catch _ => s.restore; return .stuck
  return .stuck

/-- Single `O(1)` step on the main goal; `false` if stuck, throws on unmatched memory goal. -/
meta def headStepOnce (cfg : HeadStepConfig := {}) : TacticM Bool := do
  match ← headStepOnceRes cfg with
  | .progressed =>
    setGoals (← (← getUnsolvedGoals).mapM normStoppedGoal)
    return true
  | .stuck => return false
  | .memFailed msg => throwError msg

private meta partial def headStepsLoop (cfg : HeadStepConfig) (fuel : Nat) :
    TacticM (Bool × Option String) := do
  if fuel = 0 then return (false, none)
  let mut out : Array MVarId := #[]
  let mut anyProgressed := false
  let mut firstMemErr : Option String := none
  for g in ← getUnsolvedGoals do
    if ← g.isAssigned then continue
    setGoals [g]
    match ← headStepOnceRes cfg with
    | .progressed =>
      anyProgressed := true
      let (_, subErr) ← headStepsLoop cfg (fuel - 1)
      if firstMemErr.isNone then firstMemErr := subErr
      out := out ++ (← getUnsolvedGoals)
    | .stuck => out := out.push (← normStoppedGoal g)
    | .memFailed msg =>
      trace[c0_hstep] "{msg}"
      if cfg.strictMem then throwError msg
      if firstMemErr.isNone then firstMemErr := some msg
      out := out.push (← normStoppedGoal g)
  setGoals out.toList
  return (anyProgressed, firstMemErr)

/-- Repeatedly run `headStepOnceRes` up to `fuel` steps, normalizing stopped goals once. -/
meta def headSteps (cfg : HeadStepConfig := {}) (fuel : Nat := 10000) : TacticM Unit := do
  let (progressed, err?) ← headStepsLoop cfg fuel
  if !progressed then
    if let some msg := err? then throwError msg

/-! ## 6. Public Tactics (`c0_hstep`, `c0_hsteps`, `c0_hsteps!`, `c0_hsteps_nogrp`, `c0_hsplit`,
`c0_hfast`, `c0_split`, `c0_to_group`) -/

/-- Unwrap outer `MData` from `g`'s target with zero `isDefEq` overhead, returning the
potentially refreshed goal and consumed type. -/
private meta def unwrapGoalMData (g : MVarId) : TacticM (MVarId × Lean.Expr) := do
  let rawTy ← instantiateMVars (← g.getType)
  let ty := rawTy.consumeMData
  if rawTy.isMData then
    return (← g.change ty (checkDefEq := false), ty)
  return (g, ty)

/-- Check if `ty` (with outer `MData` stripped) is `LeanQbe.T.wp` on head expr `headName`. -/
private meta def isWpHeadExpr (ty : Lean.Expr) (headName : Name) : Bool :=
  let ty := ty.headBeta.consumeMData
  ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
    ((ty.getArg! 4).consumeMData.headBeta.consumeMData).isAppOf headName

/-- Single `O(1)` head-only C0 symbolic-execution step. -/
elab "c0_hstep" : tactic => do
  unless ← headStepOnce {} do throwError "c0_hstep: no step applies"

/-- Full `O(1)` head-only C0 symbolic executor (straight-line, joins, `jnz` with pruning). -/
elab "c0_hsteps" : tactic => headSteps {} 10000

/-- Strict `O(1)` head-only C0 symbolic executor: throws immediately on any unmatched `load` or
`store` goal. -/
elab "c0_hsteps!" : tactic => headSteps { strictMem := true } 10000

/-- Fast `O(1)` head-only C0 symbolic executor with `pruneJnz := false` (skips `bv_c0` branch
pruning on `jnz` conditions). -/
elab "c0_hfast" : tactic => headSteps { pruneJnz := false } 10000

/-- `O(1)` head-only C0 symbolic executor stopping before `Expr.group` (replaces `*_to_group`). -/
elab "c0_hsteps_nogrp" : tactic => headSteps { unrollGroup := false } 10000

/-- `O(1)` head-only C0 symbolic executor stopping before `Expr.jnz`, then splitting ONE `jnz`
without running `c0_bound` on live branches (replaces `fc_split` / `fc_split_fast` / `sw_split`). -/
elab "c0_hsplit" : tactic => do
  focus do
    let _ ← headStepsLoop { unrollGroup := false, splitJnz := false } 2000
    let _ ← headStepOnce { unrollGroup := false, splitJnz := true, pruneJnz := false }

private meta partial def c0SplitLoop (fuel : Nat) : TacticM Unit := do
  if fuel = 0 then return
  let g0 ← getMainGoal
  let (g, ty) ← unwrapGoalMData g0
  if g != g0 then replaceMainGoal [g]
  if isWpHeadExpr ty ``LeanQbe.T.Expr.jnz then
    let _ ← LeanQbe.T.C0Step.stepOnce
    return
  if ← LeanQbe.T.C0Step.stepOnce then c0SplitLoop (fuel - 1)

private meta partial def c0ToGroupLoop (fuel : Nat) : TacticM Unit := do
  if fuel = 0 then return
  let mut out : Array MVarId := #[]
  for g in ← getUnsolvedGoals do
    if ← g.isAssigned then continue
    let (g, ty) ← unwrapGoalMData g
    setGoals [g]
    if isWpHeadExpr ty ``LeanQbe.T.Expr.group then
      out := out.push g
    else if ← LeanQbe.T.C0Step.stepOnce then
      c0ToGroupLoop (fuel - 1)
      out := out ++ (← getUnsolvedGoals)
    else out := out.push g
  setGoals out.toList

/-- Step straight-line ops on the main goal via `C0Step.stepOnce` (unwrapping `MData`) until the
next `Expr.jnz`, then split it once. -/
elab "c0_split" : tactic => c0SplitLoop 100

/-- Step all goals via `C0Step.stepOnce` (unwrapping `MData`), stopping each branch at
`Expr.group`. -/
elab "c0_to_group" : tactic => c0ToGroupLoop 500

end LeanQbe.T.C0HeadStep
