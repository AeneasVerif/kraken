/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Minimize.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Ref.Base
public import LeanQbe.T.Examples.LratBytes
import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
import LeanQbe.T.Logic.C0Step

/-!
# Shared Minimization Tactics, `FullMinMarkInv` Lemmas & `ShrinkBaseInv` Helpers

Purely structural minimization helpers over `Proof.Spec` (`FullMinTactics`, `fullMinMarkInv_*`,
`fullMinMark_entails`, `trailCount8`, `RsnCov`, `ShrinkResolved`, `ShrinkBaseInv`, and `bv8`
lemmas) consumed across `Proof.Minimize`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Minimize

open Std Std.Sat
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

public section

/-! ## 1. BitVector Helper Lemmas & Scoped `FullMinTactics` -/

theorem bv8_eq_zero_of_masks (x : BitVec 8) (hdom : (x &&& 0xF1#8) = 0#8)
    (h8 : (x &&& 8#8) = 0#8) (h6 : (x &&& 6#8) = 0#8) : x = 0#8 := by
  revert x hdom h8 h6; decide

theorem bv8_zero_of_masks24 (x : BitVec 8) (hdom : (x &&& 0xF1#8) = 0#8)
    (h8 : (x &&& 8#8) = 0#8) (h2 : (x &&& 2#8) = 0#8) (h4 : (x &&& 4#8) = 0#8) :
    x = 0#8 := by
  revert x hdom h8 h2 h4; decide

theorem bv8_or_tag_dom :
    ∀ x : BitVec 8, (x &&& 0xF1#8) = 0#8 →
      ((x ||| 2#8) &&& 0xF1#8) = 0#8 ∧ ((x ||| 4#8) &&& 0xF1#8) = 0#8 ∧
      ((x ||| 8#8) &&& 0xF1#8) = 0#8 ∧ ((x &&& 0xF7#8) &&& 0xF1#8) = 0#8 := by
  decide

theorem bv8_bit_pres :
    ∀ x : BitVec 8,
      ((x ||| 4#8) &&& 2#8) = (x &&& 2#8) ∧
      ((x ||| 2#8) &&& 2#8) = 2#8 ∧
      ((x ||| 8#8) &&& 6#8) = (x &&& 6#8) ∧
      ((x ||| 8#8) &&& 2#8) = (x &&& 2#8) ∧
      ((x &&& 0xF7#8) &&& 6#8) = (x &&& 6#8) ∧
      ((x &&& 0xF7#8) &&& 2#8) = (x &&& 2#8) := by
  decide

theorem bv8_bit2_or_self :
    ∀ x : BitVec 8, (x &&& 2#8) ≠ 0#8 → (x ||| 2#8) = x := by decide

theorem bv8_bit4_or_self :
    ∀ x : BitVec 8, (x &&& 4#8) ≠ 0#8 → (x ||| 4#8) = x := by decide

theorem bv8_zext32_zero_iff (a : BitVec 8) :
    a.setWidth 32 = 0#32 ↔ a = 0#8 := by
  refine ⟨fun h => BitVec.eq_of_toNat_eq ?_, fun h => by subst h; rfl⟩
  have ha : a.toNat < 2 ^ 32 := by have := a.isLt; omega
  simpa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt ha] using congrArg BitVec.toNat h

theorem bv8_and_zext32_zero_iff (a b : BitVec 8) :
    (a.setWidth 32 &&& b.setWidth 32 = 0#32) ↔ (a &&& b = 0#8) := by
  have ha := a.isLt; have hb := b.isLt
  have hab : (a.toNat &&& b.toNat) < 2 ^ 8 := Nat.and_lt_two_pow a.toNat hb
  refine ⟨fun h => BitVec.eq_of_toNat_eq ?_, fun h => BitVec.eq_of_toNat_eq ?_⟩
  · simpa [BitVec.toNat_and, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (by omega : a.toNat < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : (a.toNat &&& b.toNat) < 2 ^ 32)] using
      congrArg BitVec.toNat h
  · simpa [BitVec.toNat_and, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (by omega : a.toNat < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 32)] using congrArg BitVec.toNat h

theorem bv8_or_zext32_trunc8 (a b : BitVec 8) :
    (a.setWidth 32 ||| b.setWidth 32).setWidth 8 = a ||| b := by
  ext i hi; simp [BitVec.getElem_or]

theorem bv8_and_zext32_trunc8 (a b : BitVec 8) :
    (a.setWidth 32 &&& b.setWidth 32).setWidth 8 = a &&& b := by
  ext i hi; simp [BitVec.getElem_and]

theorem bv64_lshr_1 (x : BitVec 64) : (x >>> 1).toNat = x.toNat / 2 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]

namespace FullMinTactics

@[scoped bv_c0] theorem bv_c0_lshr1_32 (x : BitVec 32) :
    (x >>> 1).toNat = x.toNat / 2 :=
  bv32_lshr_1 x

@[scoped bv_c0] theorem bv_c0_lshr1_64_ofNat (x : BitVec 64) :
    (x >>> (BitVec.toNat (1 : BitVec 64) % 64)).toNat = x.toNat / 2 :=
  bv64_lshr_1 x

@[scoped bv_c0] theorem bv_c0_zext8_32_zero (a : BitVec 8) :
    (a.setWidth 32 = 0#32) = (a = 0#8) :=
  propext (bv8_zext32_zero_iff a)

@[scoped bv_c0] theorem bv_c0_and8_zext32_zero (a b : BitVec 8) :
    (a.setWidth 32 &&& b.setWidth 32 = 0#32) = (a &&& b = 0#8) :=
  propext (bv8_and_zext32_zero_iff a b)

theorem ml_add32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.add i32) (a, b, ())) k) m =
      wp Γ Q X (k (a.val + b.val, ())) m := by simp [wp_let_add_eq, lift2]
theorem ml_add64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.add i64) (a, b, ())) k) m =
      wp Γ Q X (k (a.val + b.val, ())) m := by simp [wp_let_add_eq, lift2]
theorem ml_sub32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.sub i32) (a, b, ())) k) m =
      wp Γ Q X (k (a.val - b.val, ())) m := by simp [wp_let_sub_eq, lift2]
theorem ml_sub64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.sub i64) (a, b, ())) k) m =
      wp Γ Q X (k (a.val - b.val, ())) m := by simp [wp_let_sub_eq, lift2]
theorem ml_mul64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.mul i64) (a, b, ())) k) m =
      wp Γ Q X (k (a.val * b.val, ())) m := by simp [wp_let_mul_eq, lift2]
theorem ml_shl64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.shl i64) (a, b, ())) k) m =
      wp Γ Q X (k (a.val <<< (b.val.toNat % 64), ())) m := by simp [wp_let_shl_eq, lift2]
theorem ml_lshr32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.lshr i32) (a, b, ())) k) m =
      wp Γ Q X (k (a.val >>> (b.val.toNat % 32), ())) m := by simp [wp_let_lshr_eq, lift2]
theorem ml_lshr64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.lshr i64) (a, b, ())) k) m =
      wp Γ Q X (k (a.val >>> (b.val.toNat % 64), ())) m := by simp [wp_let_lshr_eq, lift2]
theorem ml_and32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.and i32) (a, b, ())) k) m =
      wp Γ Q X (k (a.val &&& b.val, ())) m := by simp [wp_let_and_eq, lift2]
theorem ml_or32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.or i32) (a, b, ())) k) m =
      wp Γ Q X (k (a.val ||| b.val, ())) m := by simp [wp_let_or_eq, lift2]
theorem ml_xor32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.xor i32) (a, b, ())) k) m =
      wp Γ Q X (k (a.val ^^^ b.val, ())) m := by simp [wp_let_xor_eq, lift2]
theorem ml_zext8_32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i8} {k m} :
    wp Γ Q X (.let_ (Op.mk (.zext 8 32) (a, ())) k) m =
      wp Γ Q X (k (a.val.setWidth 32, ())) m := by simp [wp_let_zext_eq]
theorem ml_zext8_64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i8} {k m} :
    wp Γ Q X (.let_ (Op.mk (.zext 8 64) (a, ())) k) m =
      wp Γ Q X (k (a.val.setWidth 64, ())) m := by simp [wp_let_zext_eq]
theorem ml_zext32_64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.zext 32 64) (a, ())) k) m =
      wp Γ Q X (k (a.val.setWidth 64, ())) m := by simp [wp_let_zext_eq]
theorem ml_sext32_64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.sext 32 64) (a, ())) k) m =
      wp Γ Q X (k (a.val.signExtend 64, ())) m := by simp [wp_let_sext_eq]
theorem ml_trunc32_8 {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.trunc 32 8) (a, ())) k) m =
      wp Γ Q X (k (a.val.setWidth 8, ())) m := by simp [wp_let_trunc_eq]
theorem ml_trunc64_32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.trunc 64 32) (a, ())) k) m =
      wp Γ Q X (k (a.val.setWidth 32, ())) m := by simp [wp_let_trunc_eq]
theorem ml_ult32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult i32 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val.ult b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ult_eq]
theorem ml_ule32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ule i32 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val.ule b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ule_eq]
theorem ml_ugt32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ugt i32 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (b.val.ult a.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ugt_eq]
theorem ml_uge32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .uge i32 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (b.val.ule a.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_uge_eq]
theorem ml_eq32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .eq i32 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val == b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_eq_beq]
theorem ml_ne32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ne i32 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val != b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ne_bne]
theorem ml_ult64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val.ult b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ult_eq]
theorem ml_ule64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ule i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val.ule b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ule_eq]
theorem ml_ugt64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ugt i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (b.val.ult a.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ugt_eq]
theorem ml_uge64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .uge i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (b.val.ule a.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_uge_eq]
theorem ml_eq64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .eq i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val == b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_eq_beq]
theorem ml_ne64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ne i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val != b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ne_bne]
theorem ml_copy_bool {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val .bool} {k m} :
    wp Γ Q X (.let_ (Op.mk (.copy .bool) (a, ())) k) m =
      wp Γ Q X (k (a.val, ())) m := by simp [wp_let_copy_eq]
theorem ml_copy8 {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i8} {k m} :
    wp Γ Q X (.let_ (Op.mk (.copy i8) (a, ())) k) m =
      wp Γ Q X (k (a.val, ())) m := by simp [wp_let_copy_eq]
theorem ml_copy32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.copy i32) (a, ())) k) m =
      wp Γ Q X (k (a.val, ())) m := by simp [wp_let_copy_eq]
theorem ml_copy64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.copy i64) (a, ())) k) m =
      wp Γ Q X (k (a.val, ())) m := by simp [wp_let_copy_eq]
theorem ml_fst {α β : Type _} (a : α) (b : β) : (a, b).fst = a := rfl
theorem ml_snd {α β : Type _} (a : α) (b : β) : (a, b).snd = b := rfl
theorem ml_lshr32_imm1 {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.lshr i32) (a, .imm 1, ())) k) m =
      wp Γ Q X (k (a.val >>> 1, ())) m := by simp [wp_let_lshr_eq, lift2]
theorem ml_lshr32_imm1' {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.lshr i32) (a, .imm 1#32, ())) k) m =
      wp Γ Q X (k (a.val >>> 1, ())) m := by simp [wp_let_lshr_eq, lift2]
theorem ml_jnz {Γ} {rs : List Ty} {Q : Post rs} {X} {c : Val .bool} {t e m} :
    wp Γ Q X (.jnz (.var c) t e) m =
      ((c = true → wp Γ Q X t m) ∧ (c = false → wp Γ Q X e m)) := rfl

scoped syntax "ml_jnz" : tactic
scoped macro_rules
  | `(tactic| ml_jnz) => `(tactic| rw [FullMinTactics.ml_jnz])

scoped syntax "ml_lets" : tactic
scoped macro_rules
  | `(tactic| ml_lets) => `(tactic| repeat (first
    | rw [ml_fst] | rw [ml_snd] | rw [ml_lshr32_imm1] | rw [ml_lshr32_imm1']
    | rw [ml_add32] | rw [ml_add64] | rw [ml_sub32] | rw [ml_sub64] | rw [ml_mul64]
    | rw [ml_shl64] | rw [ml_lshr32] | rw [ml_lshr64] | rw [ml_and32] | rw [ml_or32]
    | rw [ml_xor32] | rw [ml_zext8_32] | rw [ml_zext8_64] | rw [ml_zext32_64]
    | rw [ml_sext32_64] | rw [ml_trunc32_8] | rw [ml_trunc64_32]
    | rw [ml_ult32] | rw [ml_ule32] | rw [ml_ugt32] | rw [ml_uge32] | rw [ml_eq32] | rw [ml_ne32]
    | rw [ml_ult64] | rw [ml_ule64] | rw [ml_ugt64] | rw [ml_uge64] | rw [ml_eq64] | rw [ml_ne64]
    | rw [ml_copy_bool] | rw [ml_copy8] | rw [ml_copy32] | rw [ml_copy64]
    | rw [Arg.val_var] | rw [Arg.val_imm]))

@[scoped bv_c0] theorem bv_c0_lshr1_32_ofNat (x : BitVec 32) :
    (x >>> (BitVec.toNat (1 : BitVec 32) % 32)).toNat = x.toNat / 2 :=
  bv32_lshr_1 x

@[scoped bv_c0] theorem bv_c0_shl1_toNat {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 64) :
    (x <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat = 2 * x.toNat := by
  have h1 : BitVec.signExtend 64 (1 : BitVec 32) = (1 : BitVec 64) := rfl
  rw [h1]
  have hm : (1 : BitVec 64).toNat % 64 = 1 := rfl
  rw [hm, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]; omega

@[scoped bv_c0] theorem bv_c0_shl1_add1_toNat {x : BitVec 64} (hx : 2 * x.toNat + 1 < 2 ^ 64) :
    (x <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1).toNat = 2 * x.toNat + 1 := by
  have hsh := bv_c0_shl1_toNat (x := x) (by omega)
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_add, hsh, h1, Nat.mod_eq_of_lt hx]

@[scoped bv_c0] theorem bv_c0_tw0 : BitVec.setWidth 8 (0 : BitVec 32) = 0#8 := rfl
@[scoped bv_c0] theorem bv_c0_tw2 : BitVec.setWidth 8 (2 : BitVec 32) = 2#8 := rfl
@[scoped bv_c0] theorem bv_c0_tw4 : BitVec.setWidth 8 (4 : BitVec 32) = 4#8 := rfl
@[scoped bv_c0] theorem bv_c0_tw8 : BitVec.setWidth 8 (8 : BitVec 32) = 8#8 := rfl
@[scoped bv_c0] theorem bv_c0_zext8_32_0 : BitVec.setWidth 32 0#8 = 0#32 := rfl
@[scoped bv_c0] theorem bv_c0_div2_mod64 (x : BitVec 32) : x.toNat / 2 % 2 ^ 64 = x.toNat / 2 :=
  Nat.mod_eq_of_lt (by have := x.isLt; omega)
@[scoped bv_c0] theorem bv_c0_lt_mod64 (x : BitVec 32) : x.toNat % 2 ^ 64 = x.toNat :=
  Nat.mod_eq_of_lt (by have := x.isLt; omega)

scoped macro "ml_ld " lem:term : tactic =>
  `(tactic| (ml_lets; rw [LeanQbe.T.wp]; refine ⟨_, $lem, ?_⟩))

scoped macro "ml_st " m:ident ", " h:ident " := " lem:term : tactic =>
  `(tactic| ((ml_lets; apply LeanQbe.T.wp_store_sep; · exact $lem); intro $m:ident $h:ident))

end FullMinTactics

open FullArenaTactics
open scoped FullMinTactics

theorem xor1_div2 (n : Nat) : (n ^^^ 1) / 2 = n / 2 := by
  have h := litVar_litNeg n; unfold litVar litNeg at h; exact h

theorem xor1_xor1 (n : Nat) : (n ^^^ 1) ^^^ 1 = n := by
  have h := litNeg_litNeg n; unfold litNeg at h; exact h

theorem bv32_xor1_toNat_lt {x : BitVec 32} {mv : Nat} (hx : x.toNat < 2 * mv) :
    (x ^^^ 1#32).toNat = x.toNat ^^^ 1 ∧ (x ^^^ 1#32).toNat < 2 * mv := by
  have h1 : (1#32 : BitVec 32).toNat = 1 := rfl
  have hto : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := by rw [BitVec.toNat_xor, h1]
  have hv := xor1_div2 x.toNat
  exact ⟨hto, by omega⟩

theorem min_bv64_add1 {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + 1).toNat = x.toNat + 1 := by bv_omega
theorem min_bv64_sub1 {x : BitVec 64} (hx : 1 ≤ x.toNat) :
    (x - 1).toNat = x.toNat - 1 := by bv_omega
theorem min_bv64_sub {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by bv_omega
theorem bv64_pos_of_ne0 {x : BitVec 64} (h : ¬x = 0) : 1 ≤ x.toNat := by
  have h0 : (0 : BitVec 64).toNat = 0 := rfl
  exact Nat.pos_of_ne_zero fun hz => h (BitVec.eq_of_toNat_eq (hz.trans h0.symm))
theorem min_bv32_add1_toNat {x : BitVec 32} (hx : x.toNat + 1 < 2 ^ 32) :
    (x + 1).toNat = x.toNat + 1 := by bv_omega
theorem bv64_zext32_add2 (r : BitVec 32) :
    (r.setWidth 64 + 2).toNat = r.toNat + 2 := by bv_omega
theorem bv64_zext32_add3_add (r i : BitVec 32) :
    (r.setWidth 64 + 3 + i.setWidth 64).toNat = r.toNat + 3 + i.toNat := by bv_omega
theorem bv64_lt_zext32_add3 {a : Nat} (ha : a < 2 ^ 64) (r : BitVec 32) :
    (BitVec.ofNat 64 a).ult (r.setWidth 64 + 3) = true → a < r.toNat + 3 := by
  intro h; rw [BitVec.ult, decide_eq_true_eq] at h; bv_omega
theorem bv64_lt_zext32_add3_add {a : Nat} (ha : a < 2 ^ 64) (r c : BitVec 32) :
    (BitVec.ofNat 64 a).ult (r.setWidth 64 + 3 + c.setWidth 64) = true →
      a < r.toNat + 3 + c.toNat := by
  intro h; rw [BitVec.ult, decide_eq_true_eq] at h; bv_omega

theorem bv8_and2_of_or2 (a : BitVec 8) : ((a ||| 2#8) &&& 2#8) ≠ 0#8 := by revert a; decide
theorem bv8_and8_of_or8 (a : BitVec 8) : ((a ||| 8#8) &&& 8#8) ≠ 0#8 := by revert a; decide
theorem bv8_and8_clear (a : BitVec 8) :
    ((a &&& 0xF7#8) &&& 8#8) = 0#8 := by revert a; decide
theorem bv8_and2_pres_clear8 (a : BitVec 8) : ((a &&& 0xF7#8) &&& 2#8) = (a &&& 2#8) := by
  revert a; decide
theorem bv8_and6_pres_clear8 (a : BitVec 8) : ((a &&& 0xF7#8) &&& 6#8) = (a &&& 6#8) := by
  revert a; decide
theorem bv8_and_dom_clear8 {a : BitVec 8} (h : (a &&& 0xF1#8) = 0#8) :
    ((a &&& 0xF7#8) &&& 0xF1#8) = 0#8 := by revert a h; decide
theorem bv8_and_dom_or2 {a : BitVec 8} (h : (a &&& 0xF1#8) = 0#8) :
    ((a ||| 2#8) &&& 0xF1#8) = 0#8 := by revert a h; decide
theorem bv8_and_dom_or4 {a : BitVec 8} (h : (a &&& 0xF1#8) = 0#8) :
    ((a ||| 4#8) &&& 0xF1#8) = 0#8 := by revert a h; decide
theorem bv8_and2_pres_or4 (a : BitVec 8) : ((a ||| 4#8) &&& 2#8) = (a &&& 2#8) := by
  revert a; decide
theorem bv8_and2_pres_or8 (a : BitVec 8) : ((a ||| 8#8) &&& 2#8) = (a &&& 2#8) := by
  revert a; decide
theorem bv8_and8_pres_or2 {a : BitVec 8} (h : (a &&& 8#8) = 0#8) :
    ((a ||| 2#8) &&& 8#8) = 0#8 := by revert a h; decide
theorem bv8_and8_pres_or4 {a : BitVec 8} (h : (a &&& 8#8) = 0#8) :
    ((a ||| 4#8) &&& 8#8) = 0#8 := by revert a h; decide

theorem bv8_or8_c0 (a : BitVec 8) :
    (a.setWidth 32 ||| (BitVec.setWidth 8 (8 : BitVec 32)).setWidth 32).setWidth 8 = a ||| 8#8 :=
  bv8_or_zext32_trunc8 a 8#8

theorem bv8_and247_c0 (a : BitVec 8) :
    (a.setWidth 32 &&& (BitVec.setWidth 8 (247 : BitVec 32)).setWidth 32).setWidth 8 =
      a &&& 0xF7#8 :=
  bv8_and_zext32_trunc8 a 0xF7#8

theorem bv8_c0_bit_ne0 {a : BitVec 8} {n : BitVec 32}
    (h : (a.setWidth 32 &&& (n.setWidth 8).setWidth 32 !=
      ((0 : BitVec 32).setWidth 8).setWidth 32) = true) :
    (a &&& n.setWidth 8) ≠ 0#8 := by
  have h0 : ((0 : BitVec 32).setWidth 8).setWidth 32 = (0#32 : BitVec 32) := rfl
  rw [h0] at h; c0_cond h; exact h

theorem bv8_c0_bit_eq0 {a : BitVec 8} {n : BitVec 32}
    (h : (a.setWidth 32 &&& (n.setWidth 8).setWidth 32 !=
      ((0 : BitVec 32).setWidth 8).setWidth 32) = false) :
    (a &&& n.setWidth 8) = 0#8 := by
  have h0 : ((0 : BitVec 32).setWidth 8).setWidth 32 = (0#32 : BitVec 32) := rfl
  rw [h0] at h; c0_cond h; exact h

theorem bv8_c0_and8_eq0 {a : BitVec 8}
    (h : (a.setWidth 32 &&& ((8 : BitVec 32).setWidth 8).setWidth 32 ==
      ((0 : BitVec 32).setWidth 8).setWidth 32) = true) : (a &&& 8#8) = 0#8 := by
  have h0 : ((0 : BitVec 32).setWidth 8).setWidth 32 = (0#32 : BitVec 32) := rfl
  have h8 : ((8 : BitVec 32).setWidth 8).setWidth 32 = (8#8).setWidth 32 := rfl
  rw [h0, h8] at h; c0_cond h; exact h

theorem bv8_c0_and8_ne0 {a : BitVec 8}
    (h : (a.setWidth 32 &&& ((8 : BitVec 32).setWidth 8).setWidth 32 ==
      ((0 : BitVec 32).setWidth 8).setWidth 32) = false) : (a &&& 8#8) ≠ 0#8 := by
  have h0 : ((0 : BitVec 32).setWidth 8).setWidth 32 = (0#32 : BitVec 32) := rfl
  have h8 : ((8 : BitVec 32).setWidth 8).setWidth 32 = (8#8).setWidth 32 := rfl
  rw [h0, h8] at h; c0_cond h; exact h

/-! ## 2. `FullCoreState` / `FullWitnessInv` / `FullMinMarkInv` Helpers -/

abbrev minLitState (s : FullState) (mrk1 : List (BitVec 8))
    (mstk1 mclr1 : List (BitVec 32)) (mcl1 : Nat) (mcf1 : BitVec 64) : FullState :=
  { s with core := { s.core with
      mrk := mrk1, min_stk := mstk1, min_clr := mclr1,
      min_clr_len := mcl1, min_clr_full := mcf1 } }

theorem fullOtfsWitness_with_min {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullOtfsWitnessInv c F0 F_cur k)
    {tmp1 : List (BitVec 32)} {tl1 : Nat} {mrk1 : List (BitVec 8)}
    {mstk1 mclr1 : List (BitVec 32)} {mcl1 : Nat} {mcf1 : BitVec 64} :
    FullOtfsWitnessInv c F0 F_cur
      { k with tmp := tmp1, tmp_len := tl1, mrk := mrk1, min_stk := mstk1,
               min_clr := mclr1, min_clr_len := mcl1, min_clr_full := mcf1 } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem fullOtfsCoreInv_with_min {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {mrk1 : List (BitVec 8)}
    {mstk1 mclr1 : List (BitVec 32)} {mcl1 : Nat} {mcf1 : BitVec 64}
    (hmrk : mrk1.length = c.max_vars) (hmstk : mstk1.length = 2 * c.minDepth)
    (hmclr : mclr1.length = c.max_vars) (hmcl : mcl1 ≤ c.max_vars) :
    FullOtfsCoreInv c F0 (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1) := by
  obtain ⟨F_cur, hw⟩ := hcore.2
  exact ⟨⟨{ hcore.1.core_ok with
      mrk_len := hmrk, min_stk_len := hmstk,
      min_clr_len_arr := hmclr, min_clr_len_le := hmcl }, hcore.1.scratch_ok⟩,
    F_cur, fullOtfsWitness_with_min hw⟩

theorem fullOtfsCoreInv_with_min_tmp {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {tmp1 : List (BitVec 32)} {tl1 : Nat}
    {mrk1 : List (BitVec 8)} {mstk1 mclr1 : List (BitVec 32)}
    {mcl1 : Nat} {mcf1 : BitVec 64} {sc1 : FullScratch}
    (htmp : tmp1.length = c.max_vars) (htl : tl1 ≤ c.max_vars)
    (hmrk : mrk1.length = c.max_vars) (hmstk : mstk1.length = 2 * c.minDepth)
    (hmclr : mclr1.length = c.max_vars) (hmcl : mcl1 ≤ c.max_vars) (hsc : sc1.LengthsOk c) :
    FullOtfsCoreInv c F0 {
      core := { s.core with
        tmp := tmp1, tmp_len := tl1, mrk := mrk1, min_stk := mstk1,
        min_clr := mclr1, min_clr_len := mcl1, min_clr_full := mcf1 }
      scratch := sc1 } := by
  obtain ⟨F_cur, hw⟩ := hcore.2
  exact ⟨⟨{ hcore.1.core_ok with
      tmp_len_arr := htmp, tmp_len_le := htl, mrk_len := hmrk,
      min_stk_len := hmstk, min_clr_len_arr := hmclr, min_clr_len_le := hmcl }, hsc⟩,
    F_cur, fullOtfsWitness_with_min hw⟩

@[expose] def fullMinMarkStepCore (k : FullCoreState) (v : Nat) (tag : BitVec 8) :
    FullCoreState :=
  if k.cur_vars ≤ v ∨ (k.mrk[v]?.getD 0#8 &&& tag) ≠ 0#8 then k
  else fullMinMarkCore k v tag

@[expose] def fullMinMarkStepState (s : FullState) (v : Nat) (tag : BitVec 8) : FullState :=
  { s with core := fullMinMarkStepCore s.core v tag }

/-- Canonical state projection for `full_min_lit_dfs_m8` and `full_shrink_lower_m8`. -/
abbrev m8MinLitDfsState (s : FullState) (mrk : List (BitVec 8))
    (wsort mclr : List (BitVec 32)) (mcl : Nat) (mcf ticks : BitVec 64) : FullState :=
  { core := { s.core with
      mrk := mrk, min_clr := mclr, min_clr_len := mcl, min_clr_full := mcf },
    scratch := { s.scratch with wsort := wsort, search_ticks := ticks } }

/-- Canonical state projection for `full_shrink_blk_bool_m8`. -/
abbrev m8ShrinkBlkBoolState (s : FullState) (tmp : List (BitVec 32))
    (mrk : List (BitVec 8)) (mclr sstk wsort : List (BitVec 32))
    (mcl : Nat) (mcf ticks : BitVec 64) : FullState :=
  { core := { s.core with
      tmp := tmp, mrk := mrk, min_clr := mclr, min_clr_len := mcl, min_clr_full := mcf },
    scratch := { s.scratch with
      shrink_stk := sstk, wsort := wsort, search_ticks := ticks } }

/-- Block-shrink state projection with `work_stk1` and `res_sz` for `full_min_shrink_m6`. -/
abbrev s13BlkState (s : FullState) (tmp : List (BitVec 32))
    (mrk : List (BitVec 8)) (mclr sstk wsort ws1 : List (BitVec 32))
    (mcl : Nat) (mcf ticks resSz : BitVec 64) : FullState :=
  { core := { s.core with
      tmp := tmp, mrk := mrk, min_clr := mclr, min_clr_len := mcl, min_clr_full := mcf },
    scratch := { s.scratch with
      shrink_stk := sstk, wsort := wsort, search_ticks := ticks,
      work_stk1 := ws1, res_sz := resSz } }

/-- Canonical post-state projection for `full_min_shrink_m6`. -/
abbrev fullMinShrinkState (s : FullState) (tmp : List (BitVec 32)) (tl : Nat)
    (mrk : List (BitVec 8)) (mclr sstk wsort ws1 : List (BitVec 32)) (mcl : Nat)
    (mcf conf llits mrem ticks resSz : BitVec 64) : FullState :=
  { core := { s.core with
      tmp := tmp, tmp_len := tl, mrk := mrk, min_clr := mclr,
      min_clr_len := mcl, min_clr_full := mcf },
    scratch := { s.scratch with
      conflicts := conf, learned_lits := llits, min_removed := mrem,
      shrink_stk := sstk, wsort := wsort, search_ticks := ticks,
      work_stk1 := ws1, res_sz := resSz } }

theorem sortTmpMask_eq {s s' : FullState} (h : AgreesExcept Spec.sortTmpMask s s') :
    s' = FullState.mk { s.core with tmp := s'.core.tmp }
      { s.scratch with wsort := s'.scratch.wsort } := by
  rcases s with ⟨c1, sc1⟩; rcases s' with ⟨c2, sc2⟩
  cases c1; cases sc1; cases c2; cases sc2
  dsimp only [AgreesExcept, Spec.sortTmpMask] at h
  cases h; rfl

theorem minLitDfsMask_eq {s s' : FullState} (h : AgreesExcept Spec.minLitDfsMask s s') :
    s' = m8MinLitDfsState s s'.core.mrk s'.scratch.wsort s'.core.min_clr
      s'.core.min_clr_len s'.core.min_clr_full s'.scratch.search_ticks := by
  rcases s with ⟨c1, sc1⟩; rcases s' with ⟨c2, sc2⟩
  cases c1; cases sc1; cases c2; cases sc2
  dsimp only [AgreesExcept, Spec.minLitDfsMask, m8MinLitDfsState] at h ⊢
  cases h; rfl

theorem shrinkBlkMask_eq {s s' : FullState} (h : AgreesExcept Spec.shrinkBlkMask s s') :
    s' = m8ShrinkBlkBoolState s s'.core.tmp s'.core.mrk s'.core.min_clr
      s'.scratch.shrink_stk s'.scratch.wsort s'.core.min_clr_len s'.core.min_clr_full
      s'.scratch.search_ticks := by
  rcases s with ⟨c1, sc1⟩; rcases s' with ⟨c2, sc2⟩
  cases c1; cases sc1; cases c2; cases sc2
  dsimp only [AgreesExcept, Spec.shrinkBlkMask, m8ShrinkBlkBoolState] at h ⊢
  cases h; rfl

theorem minShrinkMask_eq {s s' : FullState} (h : AgreesExcept Spec.minShrinkMask s s') :
    s' = fullMinShrinkState s s'.core.tmp s'.core.tmp_len s'.core.mrk s'.core.min_clr
      s'.scratch.shrink_stk s'.scratch.wsort s'.scratch.work_stk1 s'.core.min_clr_len
      s'.core.min_clr_full s'.scratch.conflicts s'.scratch.learned_lits
      s'.scratch.min_removed s'.scratch.search_ticks s'.scratch.res_sz := by
  rcases s with ⟨c1, sc1⟩; rcases s' with ⟨c2, sc2⟩
  cases c1; cases sc1; cases c2; cases sc2
  dsimp only [AgreesExcept, Spec.minShrinkMask, fullMinShrinkState] at h ⊢
  cases h; rfl

theorem fullMinMarkInv_init {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) (hmc : FullMarksClear s) (keep : List Nat) :
    FullMinMarkInv s.core keep := by
  obtain ⟨F_cur, hw⟩ := hcore.2
  exact ⟨fun v hv => by rw [hmc v hv]; decide,
    fun _ v hv hnz => by rw [hmc v hv] at hnz; exact absurd rfl hnz,
    fun idx hi h => by
      have hv : (s.core.trl[idx]?.getD 0#32).toNat / 2 < s.core.cur_vars := by
        have := hw.trail_lits_lt idx hi; omega
      rw [hmc _ hv] at h; exact absurd rfl h⟩

theorem fullMinMarkInv_with_mstk {k : FullCoreState} {keep : List Nat}
    (h : FullMinMarkInv k keep) (mstk' : List (BitVec 32)) :
    FullMinMarkInv { k with min_stk := mstk' } keep :=
  ⟨h.mrk_dom, h.clr_cov, h.rem_sound⟩

theorem fullMinMarkCore_mrk_above {k : FullCoreState} {v : Nat} {tag : BitVec 8}
    (hv : v < k.cur_vars) :
    ∀ w, k.cur_vars ≤ w → (fullMinMarkCore k v tag).mrk[w]? = k.mrk[w]? := by
  intro w hw
  dsimp only [fullMinMarkCore]
  rw [List.getElem?_set_ne (by omega)]

theorem fullMinMarkCore_lengths {c : FullCfg} {k : FullCoreState} (hlen : k.LengthsOk c)
    {v : Nat} (tag : BitVec 8) :
    (fullMinMarkCore k v tag).LengthsOk c := by
  dsimp only [fullMinMarkCore]
  refine { hlen with
    mrk_len := by simp [hlen.mrk_len]
    min_clr_len_arr := by split <;> simp [hlen.min_clr_len_arr]
    min_clr_len_le := by
      dsimp only
      split
      · rename_i hc; have := hlen.cur_vars_le; omega
      · exact hlen.min_clr_len_le }

private theorem full_trail_xor_var_lt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullOtfsWitnessInv c F0 F_cur k) {j q : Nat} (hj : j < k.trail_end)
    (hjeq : (k.trl[j]?.getD 0#32).toNat = q ^^^ 1) : q / 2 < k.cur_vars := by
  have hlt := hw.trail_lits_lt j hj
  have hql : (q ^^^ 1) / 2 = q / 2 := litVar_litNeg q
  rw [hjeq, ← hql] at *; omega

private theorem full_clr_cov_mark_step {c : FullCfg} {k : FullCoreState}
    (hlen : k.LengthsOk c)
    (hdom : ∀ w < k.cur_vars, (k.mrk[w]?.getD 0#8 &&& 0xF1#8) = 0#8)
    (hcov : k.min_clr_full = 0#64 → ∀ w < k.cur_vars, (k.mrk[w]?.getD 0#8 &&& 6#8) ≠ 0#8 →
      ∃ j < k.min_clr_len, (k.min_clr[j]?.getD 0#32).toNat = w)
    {v : Nat} (hv : v < k.cur_vars)
    (hno8 : (k.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) (tag : BitVec 8) :
    let k' := fullMinMarkCore k v tag
    k'.min_clr_full = 0#64 → ∀ w < k'.cur_vars, (k'.mrk[w]?.getD 0#8 &&& 6#8) ≠ 0#8 →
      ∃ j < k'.min_clr_len, (k'.min_clr[j]?.getD 0#32).toNat = w := by
  dsimp only [fullMinMarkCore]
  intro hmcf w hw hnz
  have hmx := c.hmaxv; unfold Ref.dimacsBound at hmx
  have hcv := hlen.cur_vars_le
  have hmcll := hlen.min_clr_len_arr
  by_cases hcur0 : k.mrk[v]?.getD 0#8 = 0#8
  · by_cases hlt : k.min_clr_len < k.cur_vars
    · simp only [hcur0, hlt, and_self, not_true_eq_false, and_false, ↓reduceIte] at hmcf hnz ⊢
      by_cases hweq : w = v
      · subst w
        refine ⟨k.min_clr_len, by omega, ?_⟩
        rw [List.getElem?_set_self (by omega), Option.getD_some,
          bv32_ofNat_toNat (by omega)]
      · have hnz' : (k.mrk[w]?.getD 0#8 &&& 6#8) ≠ 0#8 := by
          simpa [List.getElem?_set_ne (Ne.symm hweq)] using hnz
        obtain ⟨j, hj, hjeq⟩ := hcov hmcf w hw hnz'
        exact ⟨j, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hjeq⟩
    · simp only [hcur0, hlt, not_false_eq_true, and_self, ↓reduceIte] at hmcf
      cases hmcf
  · simp only [hcur0, false_and, ↓reduceIte] at hmcf hnz ⊢
    by_cases hweq : w = v
    · subst w
      have h6 : (k.mrk[v]?.getD 0#8 &&& 6#8) ≠ 0#8 := fun h =>
        hcur0 (bv8_eq_zero_of_masks _ (hdom v hv) hno8 h)
      exact hcov hmcf v hv h6
    · have hnz' : (k.mrk[w]?.getD 0#8 &&& 6#8) ≠ 0#8 := by
        simpa [List.getElem?_set_ne (Ne.symm hweq)] using hnz
      exact hcov hmcf w hw hnz'

private theorem fullMinMarkInv_lift_sound {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k k' : FullCoreState} {keep : List Nat} (hw : FullOtfsWitnessInv c F0 F_cur k)
    (hk_eq : k'.cur_vars = k.cur_vars ∧ k'.trail_end = k.trail_end ∧ k'.trl = k.trl ∧
      k'.lvl = k.lvl ∧ k'.cur_level = k.cur_level ∧ k'.rsns = k.rsns ∧
      k'.arena = k.arena ∧ k'.arena_len = k.arena_len)
    (hmono : ∀ w < k.cur_vars,
      (k.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (k'.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hprev : FullMinMarkInv k keep) {idx : Nat} (hi : idx < k.trail_end)
    (h2' : (k.mrk[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) :
    let p := (k'.trl[idx]?.getD 0#32).toNat
    (p ^^^ 1) ∈ keep ∨
      (k'.lvl[p / 2]?.getD 0#32).toNat < k'.cur_level ∧
      let rsn := k'.rsns[p / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 ∧
      if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * k'.cur_vars ∧
        ∃ j < idx, (k'.trl[j]?.getD 0#32).toNat = ot ^^^ 1 ∧
          ((k'.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨ (k'.mrk[ot / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
      else
        rsn.toNat ∈ fullArenaClauseRefsCore k' ∧ fullArenaClauseGarbCore k' rsn.toNat = false ∧
        ∀ q ∈ fullArenaClauseLitsCore k' rsn.toNat,
          q = p ∨ ∃ j < idx, (k'.trl[j]?.getD 0#32).toNat = q ^^^ 1 ∧
            ((k'.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (k'.mrk[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) := by
  rcases hk_eq with ⟨hcv, _, htrl, hlvl, hcl, hrsn, har, hal⟩
  rw [hcv, htrl, hrsn, hlvl, hcl]
  have hr : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k := by
    simp [fullArenaClauseRefsCore, har, hal]
  have hcl' : ∀ r, fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := fun r => by
    simp [fullArenaClauseGarbCore, fullArenaHdrCore, fullArenaClauseLitsCore,
      fullArenaClauseSizeCore, har]
  rcases hprev.rem_sound idx hi h2' with hin | ⟨hlv, hne, hif⟩
  · exact Or.inl hin
  · refine Or.inr ⟨hlv, hne, ?_⟩
    split at hif <;> split
    · obtain ⟨hot, j, hj, hjeq, hdep⟩ := hif
      exact ⟨hot, j, hj, hjeq, hdep.elim Or.inl fun hj2 => Or.inr (hmono _ (by omega) hj2)⟩
    · rename_i h1 h2; exact absurd h1 h2
    · rename_i h1 h2; exact absurd h2 h1
    · obtain ⟨href, hng, hall⟩ := hif
      refine ⟨by rw [hr]; exact href, by rw [(hcl' _).1]; exact hng, fun q hq => ?_⟩
      rw [(hcl' _).2] at hq
      rcases hall q hq with rfl | ⟨j, hj, hjeq, hdep⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨j, hj, hjeq, hdep.elim Or.inl fun hj2 =>
          Or.inr (hmono _ (full_trail_xor_var_lt hw (Nat.lt_trans hj hi) hjeq) hj2)⟩

theorem fullMinMarkInv_set_bit8 {c : FullCfg} {F0 : CNF Nat} {s : FullState} {keep : List Nat}
    (hcore : FullOtfsCoreInv c F0 s) (hmin : FullMinMarkInv s.core keep)
    {v : Nat} (hv : v < s.core.cur_vars) :
    FullMinMarkInv { s.core with mrk := s.core.mrk.set v (s.core.mrk[v]?.getD 0#8 ||| 8#8) }
      keep := by
  obtain ⟨F_cur, hw⟩ := hcore.2
  let k' : FullCoreState :=
    { s.core with mrk := s.core.mrk.set v (s.core.mrk[v]?.getD 0#8 ||| 8#8) }
  change FullMinMarkInv k' keep
  have hlen := hcore.1.core_ok
  have hv_mrk : v < s.core.mrk.length := by rw [hlen.mrk_len]; have := hlen.cur_vars_le; omega
  have hbit2 : ∀ w < s.core.cur_vars,
      (k'.mrk[w]?.getD 0#8 &&& 2#8) = (s.core.mrk[w]?.getD 0#8 &&& 2#8) := fun w _ => by
    by_cases hweq : w = v
    · subst w
      simp [k', List.getElem?_set_self hv_mrk, (bv8_bit_pres _).2.2.2.1]
    · simp [k', List.getElem?_set_ne (Ne.symm hweq)]
  refine ⟨fun w hw' => ?_, fun hmcf w hw' hnz => ?_, fun idx hi h2 => ?_⟩
  · by_cases hweq : w = v
    · subst w
      simp [k', List.getElem?_set_self hv_mrk, (bv8_or_tag_dom _ (hmin.mrk_dom v hv)).2.2.1]
    · simp [k', List.getElem?_set_ne (Ne.symm hweq), hmin.mrk_dom w hw']
  · refine hmin.clr_cov hmcf w hw' ?_
    by_cases hweq : w = v
    · subst w
      simpa [k', List.getElem?_set_self hv_mrk, (bv8_bit_pres _).2.2.1] using hnz
    · simpa [k', List.getElem?_set_ne (Ne.symm hweq)] using hnz
  · have hvw : (s.core.trl[idx]?.getD 0#32).toNat / 2 < s.core.cur_vars := by
      have := hw.trail_lits_lt idx hi; omega
    exact fullMinMarkInv_lift_sound (k' := k') hw ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun w hw' h => by rwa [hbit2 w hw']) hmin hi (by rwa [← hbit2 _ hvw])

theorem fullMinMarkInv_clear_bit8 {c : FullCfg} {F0 : CNF Nat} {s : FullState} {keep : List Nat}
    (hcore : FullOtfsCoreInv c F0 s) (hmin : FullMinMarkInv s.core keep)
    {v : Nat} (hv : v < s.core.cur_vars) :
    FullMinMarkInv { s.core with mrk := s.core.mrk.set v (s.core.mrk[v]?.getD 0#8 &&& 0xF7#8) }
      keep := by
  obtain ⟨F_cur, hw⟩ := hcore.2
  let k' : FullCoreState :=
    { s.core with mrk := s.core.mrk.set v (s.core.mrk[v]?.getD 0#8 &&& 0xF7#8) }
  change FullMinMarkInv k' keep
  have hlen := hcore.1.core_ok
  have hv_mrk : v < s.core.mrk.length := by rw [hlen.mrk_len]; have := hlen.cur_vars_le; omega
  have hbit2 : ∀ w < s.core.cur_vars,
      (k'.mrk[w]?.getD 0#8 &&& 2#8) = (s.core.mrk[w]?.getD 0#8 &&& 2#8) := fun w _ => by
    by_cases hweq : w = v
    · subst w
      simp [k', List.getElem?_set_self hv_mrk, (bv8_bit_pres _).2.2.2.2.2]
    · simp [k', List.getElem?_set_ne (Ne.symm hweq)]
  refine ⟨fun w hw' => ?_, fun hmcf w hw' hnz => ?_, fun idx hi h2 => ?_⟩
  · by_cases hweq : w = v
    · subst w
      simp [k', List.getElem?_set_self hv_mrk, (bv8_or_tag_dom _ (hmin.mrk_dom v hv)).2.2.2]
    · simp [k', List.getElem?_set_ne (Ne.symm hweq), hmin.mrk_dom w hw']
  · refine hmin.clr_cov hmcf w hw' ?_
    by_cases hweq : w = v
    · subst w
      simpa [k', List.getElem?_set_self hv_mrk, (bv8_bit_pres _).2.2.2.2.1] using hnz
    · simpa [k', List.getElem?_set_ne (Ne.symm hweq)] using hnz
  · have hvw : (s.core.trl[idx]?.getD 0#32).toNat / 2 < s.core.cur_vars := by
      have := hw.trail_lits_lt idx hi; omega
    exact fullMinMarkInv_lift_sound (k' := k') hw ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun w hw' h => by rwa [hbit2 w hw']) hmin hi (by rwa [← hbit2 _ hvw])

theorem fullMinMarkInv_poison {c : FullCfg} {F0 : CNF Nat} {s : FullState} {keep : List Nat}
    (hcore : FullOtfsCoreInv c F0 s) (hmin : FullMinMarkInv s.core keep)
    {v : Nat} (hv : v < s.core.cur_vars) (hno8 : (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) :
    FullMinMarkInv (fullMinMarkCore s.core v 4#8) keep := by
  obtain ⟨F_cur, hw⟩ := hcore.2
  let k' := fullMinMarkCore s.core v 4#8
  change FullMinMarkInv k' keep
  have hlen := hcore.1.core_ok
  have hv_mrk : v < s.core.mrk.length := by rw [hlen.mrk_len]; have := hlen.cur_vars_le; omega
  have hbit2 : ∀ w < s.core.cur_vars,
      (k'.mrk[w]?.getD 0#8 &&& 2#8) = (s.core.mrk[w]?.getD 0#8 &&& 2#8) := fun w _ => by
    by_cases hweq : w = v
    · subst w
      simp [k', fullMinMarkCore, List.getElem?_set_self hv_mrk, (bv8_bit_pres _).1]
    · simp [k', fullMinMarkCore, List.getElem?_set_ne (Ne.symm hweq)]
  refine ⟨fun w hw' => ?_,
    full_clr_cov_mark_step hlen hmin.mrk_dom hmin.clr_cov hv hno8 4#8,
    fun idx hi h2 => ?_⟩
  · by_cases hweq : w = v
    · subst w
      simp [k', fullMinMarkCore, List.getElem?_set_self hv_mrk,
        (bv8_or_tag_dom _ (hmin.mrk_dom v hv)).2.1]
    · simp [k', fullMinMarkCore, List.getElem?_set_ne (Ne.symm hweq), hmin.mrk_dom w hw']
  · have hvw : (s.core.trl[idx]?.getD 0#32).toNat / 2 < s.core.cur_vars := by
      have := hw.trail_lits_lt idx hi; omega
    exact fullMinMarkInv_lift_sound (k' := k') hw ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun w hw' h => by rwa [hbit2 w hw']) hmin hi (by rwa [← hbit2 _ hvw])

theorem fullMinMarkInv_mark_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keep : List Nat} (hcore : FullOtfsCoreInv c F0 s) (hmin : FullMinMarkInv s.core keep)
    {l : Nat} (hl : l < 2 * s.core.cur_vars) (hkeep : l ∈ keep)
    (hfals : s.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hno8 : (s.core.mrk[l / 2]?.getD 0#8 &&& 8#8) = 0#8) :
    FullMinMarkInv (fullMinMarkCore s.core (l / 2) 2#8) keep := by
  obtain ⟨F_cur, hw⟩ := hcore.2
  let v := l / 2
  let k' := fullMinMarkCore s.core v 2#8
  change FullMinMarkInv k' keep
  have hlen := hcore.1.core_ok
  have hv : v < s.core.cur_vars := by omega
  have hv_mrk : v < s.core.mrk.length := by rw [hlen.mrk_len]; have := hlen.cur_vars_le; omega
  have hmono : ∀ w < s.core.cur_vars,
      (s.core.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (k'.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
    intro w _ hw2
    by_cases hweq : w = v
    · subst w
      simp [k', fullMinMarkCore, List.getElem?_set_self hv_mrk, (bv8_bit_pres _).2.1]
    · simpa [k', fullMinMarkCore, List.getElem?_set_ne (Ne.symm hweq)] using hw2
  refine ⟨fun w hw' => ?_,
    full_clr_cov_mark_step hlen hmin.mrk_dom hmin.clr_cov hv hno8 2#8,
    fun idx hi h2 => ?_⟩
  · by_cases hweq : w = v
    · subst w
      simp [k', fullMinMarkCore, List.getElem?_set_self hv_mrk,
        (bv8_or_tag_dom _ (hmin.mrk_dom v hv)).1]
    · simp [k', fullMinMarkCore, List.getElem?_set_ne (Ne.symm hweq), hmin.mrk_dom w hw']
  · have hi' : idx < s.core.trail_end := hi
    by_cases hveq : (s.core.trl[idx]?.getD 0#32).toNat / 2 = v
    · obtain ⟨j, hj, hjeq⟩ := (hw.vals_false_iff l hl).mp hfals
      have hj_idx : j = idx := hw.trail_vars_nodup j idx hj hi' (by
        rw [hjeq, show (l ^^^ 1) / 2 = v from litVar_litNeg l, hveq])
      subst hj_idx
      have hp : (l ^^^ 1) ^^^ 1 = l := litNeg_litNeg l
      exact Or.inl (by dsimp only [k', fullMinMarkCore]; rwa [hjeq, hp])
    · have h2' :
          (s.core.mrk[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
        simpa [k', fullMinMarkCore, List.getElem?_set_ne (Ne.symm hveq)] using h2
      exact fullMinMarkInv_lift_sound (k' := k') hw ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        hmono hmin hi' h2'

theorem fullMinMarkInv_mark_rem {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keep : List Nat} (hcore : FullOtfsCoreInv c F0 s) (hmin : FullMinMarkInv s.core keep)
    {idx0 : Nat} (hi0 : idx0 < s.core.trail_end)
    (hlvl : (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    (hno8 : (s.core.mrk[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) = 0#8)
    (hrsn : let p0 := (s.core.trl[idx0]?.getD 0#32).toNat
      let rsn := s.core.rsns[p0 / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 ∧
      if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * s.core.cur_vars ∧
        ∃ j < idx0, (s.core.trl[j]?.getD 0#32).toNat = ot ^^^ 1 ∧
          ((s.core.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨
            (s.core.mrk[ot / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
      else
        rsn.toNat ∈ fullArenaClauseRefsCore s.core ∧
        fullArenaClauseGarbCore s.core rsn.toNat = false ∧
        ∀ q ∈ fullArenaClauseLitsCore s.core rsn.toNat,
          q = p0 ∨ ∃ j < idx0, (s.core.trl[j]?.getD 0#32).toNat = q ^^^ 1 ∧
            ((s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨
              (s.core.mrk[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)) :
    FullMinMarkInv
      (fullMinMarkCore s.core ((s.core.trl[idx0]?.getD 0#32).toNat / 2) 2#8) keep := by
  obtain ⟨F_cur, hw⟩ := hcore.2
  let v := (s.core.trl[idx0]?.getD 0#32).toNat / 2
  let k' := fullMinMarkCore s.core v 2#8
  change FullMinMarkInv k' keep
  have hlen := hcore.1.core_ok
  have hv : v < s.core.cur_vars := by have := hw.trail_lits_lt idx0 hi0; omega
  have hv_mrk : v < s.core.mrk.length := by rw [hlen.mrk_len]; have := hlen.cur_vars_le; omega
  have hmono : ∀ w < s.core.cur_vars,
      (s.core.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (k'.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
    intro w _ hw2
    by_cases hweq : w = v
    · subst w
      simp [k', fullMinMarkCore, List.getElem?_set_self hv_mrk, (bv8_bit_pres _).2.1]
    · simpa [k', fullMinMarkCore, List.getElem?_set_ne (Ne.symm hweq)] using hw2
  refine ⟨fun w hw' => ?_,
    full_clr_cov_mark_step hlen hmin.mrk_dom hmin.clr_cov hv hno8 2#8,
    fun idx hi h2 => ?_⟩
  · by_cases hweq : w = v
    · subst w
      simp [k', fullMinMarkCore, List.getElem?_set_self hv_mrk,
        (bv8_or_tag_dom _ (hmin.mrk_dom v hv)).1]
    · simp [k', fullMinMarkCore, List.getElem?_set_ne (Ne.symm hweq), hmin.mrk_dom w hw']
  · have hi' : idx < s.core.trail_end := hi
    by_cases hveq : (s.core.trl[idx]?.getD 0#32).toNat / 2 = v
    · have hidx : idx = idx0 := hw.trail_vars_nodup idx idx0 hi' hi0 hveq; subst hidx
      obtain ⟨hne, hif⟩ := hrsn; refine Or.inr ⟨hlvl, hne, ?_⟩
      split at hif <;> split
      · obtain ⟨hot, j, hj, hjeq, hdep⟩ := hif
        have hot_v : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat / 2 < s.core.cur_vars := by omega
        exact ⟨hot, j, hj, hjeq, hdep.elim Or.inl fun hj2 => Or.inr (hmono _ hot_v hj2)⟩
      · rename_i h1 h2; exact absurd h1 h2
      · rename_i h1 h2; exact absurd h2 h1
      · obtain ⟨href, hng, hall⟩ := hif; refine ⟨href, hng, fun q hq => ?_⟩
        rcases hall q hq with rfl | ⟨j, hj, hjeq, hdep⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨j, hj, hjeq, hdep.elim Or.inl fun hj2 =>
            Or.inr (hmono _ (full_trail_xor_var_lt hw (Nat.lt_trans hj hi0) hjeq) hj2)⟩
    · have h2' :
          (s.core.mrk[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
        simpa [k', fullMinMarkCore, List.getElem?_set_ne (Ne.symm hveq)] using h2
      exact fullMinMarkInv_lift_sound (k' := k') hw ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        hmono hmin hi' h2'

theorem fullMinMarkInv_drop {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keep keep' : List Nat} (hcore : FullOtfsCoreInv c F0 s) (hmin : FullMinMarkInv s.core keep)
    {root_lit : Nat} (hsub : ∀ l ∈ keep, l = root_lit ∨ l ∈ keep')
    (hlvl : (s.core.lvl[root_lit / 2]?.getD 0#32).toNat < s.core.cur_level)
    {idx0 : Nat} (hi0 : idx0 < s.core.trail_end)
    (hroot : (s.core.trl[idx0]?.getD 0#32).toNat = root_lit ^^^ 1)
    (hrsn : let p0 := root_lit ^^^ 1
      let rsn := s.core.rsns[p0 / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 ∧
      if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * s.core.cur_vars ∧
        ∃ j < idx0, (s.core.trl[j]?.getD 0#32).toNat = ot ^^^ 1 ∧
          ((s.core.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨
            (s.core.mrk[ot / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
      else
        rsn.toNat ∈ fullArenaClauseRefsCore s.core ∧
        fullArenaClauseGarbCore s.core rsn.toNat = false ∧
        ∀ q ∈ fullArenaClauseLitsCore s.core rsn.toNat,
          q = p0 ∨ ∃ j < idx0, (s.core.trl[j]?.getD 0#32).toNat = q ^^^ 1 ∧
            ((s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨
              (s.core.mrk[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)) :
    FullMinMarkInv s.core keep' := by
  obtain ⟨F_cur, hw⟩ := hcore.2
  refine ⟨hmin.mrk_dom, hmin.clr_cov, fun idx hi h2 => ?_⟩
  rcases hmin.rem_sound idx hi h2 with hin | hok
  · rcases hsub _ hin with heq | hin'
    · have hv_eq : (s.core.trl[idx]?.getD 0#32).toNat / 2 =
          (s.core.trl[idx0]?.getD 0#32).toNat / 2 := by
        rw [hroot]
        have h1 : ((s.core.trl[idx]?.getD 0#32).toNat ^^^ 1) / 2 =
            (s.core.trl[idx]?.getD 0#32).toNat / 2 := litVar_litNeg _
        have h2' : (root_lit ^^^ 1) / 2 = root_lit / 2 := litVar_litNeg root_lit
        rw [← h1, heq, h2']
      have hidx : idx = idx0 := hw.trail_vars_nodup idx idx0 hi hi0 hv_eq
      subst hidx; rw [hroot]
      have hrl : (root_lit ^^^ 1) / 2 = root_lit / 2 := litVar_litNeg root_lit
      exact Or.inr ⟨by rw [hrl]; exact hlvl, hrsn⟩
    · exact Or.inl hin'
  · exact Or.inr hok

private theorem full_trail_lit_false_strong {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {keep : List Nat} (hw : FullOtfsWitnessInv c F0 F_cur k)
    (hmin : FullMinMarkInv k keep) (α : Nat → Bool) (hα : (cnfOfClauses F_cur).Sat α)
    (hkeep_false : ∀ l ∈ keep, α (litVar l) ≠ !(litSign l)) :
    ∀ i < k.trail_end, let p := (k.trl[i]?.getD 0#32).toNat
      (k.lvl[p / 2]?.getD 0#32).toNat = 0 ∨ (k.mrk[p / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 →
      α (litVar p) = !(litSign p) := by
  intro i hi p hcond
  rcases hcond with hl0 | hrem
  · exact (sat_cnfClause_singleton α p).mp
      (CNF.entails_clause_def.mp (hw.level0_sound i hi hl0) α hα)
  · rcases hmin.rem_sound i hi hrem with hin | ⟨hlvl_lt, hne, hif⟩
    · have hf := hkeep_false _ hin
      have hv : litVar (p ^^^ 1) = litVar p := litVar_litNeg p
      have hs : litSign (p ^^^ 1) = !(litSign p) := litSign_litNeg p
      rw [hv, hs] at hf; cases h1 : α (litVar p) <;> cases h2 : litSign p <;> simp_all
    · have hcontra : ∀ (q j : Nat), j < i → (k.trl[j]?.getD 0#32).toNat = q ^^^ 1 →
          ((k.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (k.mrk[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) →
          α (litVar q) = !(litSign q) → False := fun q j hj hjeq hjcond hqsat => by
        have hjq : (k.trl[j]?.getD 0#32).toNat / 2 = q / 2 := by rw [hjeq]; exact litVar_litNeg q
        have hjf := full_trail_lit_false_strong hw hmin α hα hkeep_false j
          (Nat.lt_trans hj hi) (by rw [hjq]; exact hjcond)
        have hv : litVar (q ^^^ 1) = litVar q := litVar_litNeg q
        have hs : litSign (q ^^^ 1) = !(litSign q) := litSign_litNeg q
        rw [hjeq, hv, hs] at hjf; cases h1 : α (litVar q) <;> cases h2 : litSign q <;> simp_all
      split at hif
      · rename_i hbin
        obtain ⟨_, j, hj, hjeq, hjcond⟩ := hif
        have hri := hw.reason_inv_below i hi hlvl_lt hne
        dsimp only at hri
        rw [ite_eq_left hbin] at hri
        obtain ⟨_, hent, _⟩ := hri
        obtain ⟨q, hq, hqsat⟩ := (clause_sat_cnfClause_iff α _).mp
          (CNF.entails_clause_def.mp hent α hα)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | hq
        · exact hqsat
        · exact False.elim (hcontra _ j hj hjeq hjcond (hq ▸ hqsat))
      · obtain ⟨href, hng, hall⟩ := hif
        obtain ⟨q, hq, hqsat⟩ := (clause_sat_cnfClause_iff α _).mp
          (CNF.entails_clause_def.mp (hw.arena.entails _ href hng) α hα)
        rcases hall q hq with rfl | ⟨j, hj, hjeq, hjcond⟩
        · exact hqsat
        · exact False.elim (hcontra q j hj hjeq hjcond hqsat)
termination_by i => i

theorem fullMinMark_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {orig keep : List Nat}
    (hw : FullOtfsWitnessInv c F0 F_cur k) (hmin : FullMinMarkInv k keep)
    (horig : (cnfOfClauses F_cur).EntailsClause (cnfClause orig))
    (hspec : ∀ l ∈ orig, l < 2 * k.cur_vars ∧ k.vals[l]?.getD 0#8 = 0xFF#8 ∧
      (l ∈ keep ∨ (k.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause keep) := by
  rw [CNF.entails_clause_def] at horig ⊢; intro α hα
  by_cases hsat : (keep.any fun l => α (litVar l) == !(litSign l)) = true
  · obtain ⟨l, hl, hlt⟩ := List.any_eq_true.mp hsat
    exact (clause_sat_cnfClause_iff α keep).mpr ⟨l, hl, beq_iff_eq.mp hlt⟩
  · exfalso
    have hkf : ∀ l ∈ keep, α (litVar l) ≠ !(litSign l) := fun l hl heq =>
      hsat (List.any_eq_true.mpr ⟨l, hl, beq_iff_eq.mpr heq⟩)
    obtain ⟨l, hl, hlsat⟩ := (clause_sat_cnfClause_iff α orig).mp (horig α hα)
    obtain ⟨hlt, hfals, hkm⟩ := hspec l hl
    rcases hkm with hin | hmrk
    · exact hkf l hin hlsat
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l hlt).mp hfals
      have hvar : (k.trl[i]?.getD 0#32).toNat / 2 = l / 2 := by rw [hieq]; exact litVar_litNeg l
      have htf := full_trail_lit_false_strong hw hmin α hα hkf i hi
        (Or.inr (by rw [hvar]; exact hmrk))
      have hv : litVar (l ^^^ 1) = litVar l := litVar_litNeg l
      have hs : litSign (l ^^^ 1) = !(litSign l) := litSign_litNeg l
      rw [hieq, hv, hs, hlsat] at htf; cases hls : litSign l <;> simp_all

theorem mem_filter_map_toNat_take {xs : List (BitVec 32)} {n l : Nat} :
    l ∈ ((xs.take n).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat ↔
      ∃ k < min n xs.length, ∃ b, xs[k]? = some b ∧ b ≠ 0xFFFFFFFF#32 ∧ b.toNat = l := by
  rw [List.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [List.mem_filter, List.mem_iff_getElem] at hb
    obtain ⟨⟨k, hk, hkb⟩, hne⟩ := hb
    rw [List.length_take] at hk
    rw [List.getElem_take] at hkb
    exact ⟨k, hk, b, by rw [List.getElem?_eq_getElem (by omega), hkb],
      decide_eq_true_eq.mp hne, rfl⟩
  · rintro ⟨k, hk, b, hkb, hne, rfl⟩
    refine ⟨b, List.mem_filter.mpr ⟨List.mem_iff_getElem.mpr
      ⟨k, by rw [List.length_take]; exact hk, ?_⟩, decide_eq_true_eq.mpr hne⟩, rfl⟩
    rw [List.getElem_take]
    rw [List.getElem?_eq_getElem (by omega)] at hkb
    exact Option.some.inj hkb

private theorem mem_filter_map_div2_take {xs : List (BitVec 32)} {n v : Nat} (hn : n ≤ xs.length) :
    v ∈ (((xs.take n).filter (· ≠ 0xFFFFFFFF#32)).map fun x => x.toNat / 2) ↔
      ∃ i < n, xs[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
        (xs[i]?.getD 0#32).toNat / 2 = v := by
  simp only [List.mem_map, List.mem_filter, List.mem_take_iff_getElem, decide_eq_true_eq]
  constructor
  · rintro ⟨x, ⟨⟨i, hi, rfl⟩, hne⟩, rfl⟩
    have hi' : i < n := by omega
    exact ⟨i, hi', by simp [show i < xs.length by omega]; exact hne,
      by simp [show i < xs.length by omega]⟩
  · rintro ⟨i, hi, hne, hv⟩
    exact ⟨xs[i]'(by omega), ⟨⟨i, by omega, rfl⟩,
      by simp [show i < xs.length by omega] at hne; exact hne⟩,
      by simp [show i < xs.length by omega] at hv; exact hv⟩

theorem nodup_filter_map_div2_iff : ∀ {xs : List (BitVec 32)} {n : Nat}, n ≤ xs.length →
    ((((xs.take n).filter (· ≠ 0xFFFFFFFF#32)).map fun x => x.toNat / 2).Nodup ↔
      ∀ i j, i < j → j < n → xs[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
        xs[j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
        (xs[i]?.getD 0#32).toNat / 2 ≠ (xs[j]?.getD 0#32).toNat / 2)
  | _, 0, _ => by simp
  | xs, n + 1, hn => by
    have ih := nodup_filter_map_div2_iff (xs := xs) (n := n) (by omega)
    rw [List.take_succ_eq_append_getElem (by omega), List.filter_append, List.map_append]
    by_cases hff : xs[n]'(by omega) = 0xFFFFFFFF#32
    · rw [show ([xs[n]'(by omega)] : List (BitVec 32)).filter (· ≠ 0xFFFFFFFF#32) = [] by
        simp [hff], List.map_nil, List.append_nil, ih]
      refine ⟨fun h i j hij hj hni hnj => h i j hij (by
        by_cases hjn : j = n
        · subst j; simp [show n < xs.length by omega, hff] at hnj
        · omega) hni hnj, fun h i j hij hj => h i j hij (by omega)⟩
    · rw [show ([xs[n]'(by omega)] : List (BitVec 32)).filter (· ≠ 0xFFFFFFFF#32) =
        [xs[n]'(by omega)] by simp [hff], List.map_singleton, List.nodup_append]
      have hm := mem_filter_map_div2_take (xs := xs) (n := n)
        (v := (xs[n]'(by omega)).toNat / 2) (by omega)
      simp only [List.nodup_cons, List.not_mem_nil, List.mem_singleton, not_false_eq_true, true_and,
        List.nodup_nil]
      refine ⟨fun ⟨hnd, hnin⟩ i j hij hj hni hnj heq => ?_, fun hall =>
        ⟨ih.mpr fun i j hij hj => hall i j hij (by omega), fun a ha b hb heq => by
          subst hb; subst heq; rw [hm] at ha; obtain ⟨i, hi, hni, heqi⟩ := ha
          exact hall i n hi (Nat.lt_succ_self n) hni
            (by simp [show n < xs.length by omega, hff])
            (by simp [show n < xs.length by omega, heqi])⟩⟩
      by_cases hjn : j = n
      · subst j
        have hn2 : (xs[n]?.getD 0#32).toNat / 2 = (xs[n]'(by omega)).toNat / 2 := by
          simp [show n < xs.length by omega]
        rw [hn2] at heq; exact hnin _ (hm.mpr ⟨i, by omega, hni, heq⟩) _ rfl rfl
      · exact ih.mp hnd i j hij (by omega) hni hnj heq

theorem nodup_filter_set_sent {xs : List (BitVec 32)} {n beg : Nat}
    (hn : n ≤ xs.length) (hbeg : beg < n)
    (hnd : (((xs.take n).filter (· ≠ 0xFFFFFFFF#32)).map fun x => x.toNat / 2).Nodup) :
    ((((xs.set beg 0xFFFFFFFF#32).take n).filter (· ≠ 0xFFFFFFFF#32)).map
      fun x => x.toNat / 2).Nodup := by
  rw [nodup_filter_map_div2_iff (by rw [List.length_set]; exact hn)]
  have hall := (nodup_filter_map_div2_iff hn).mp hnd
  intro i j hij hj hni hnj
  have hbi : i ≠ beg := fun h => by subst i; simp [show beg < xs.length by omega] at hni
  have hbj : j ≠ beg := fun h => by subst j; simp [show beg < xs.length by omega] at hnj
  rw [List.getElem?_set_ne (Ne.symm hbi)] at hni ⊢
  rw [List.getElem?_set_ne (Ne.symm hbj)] at hnj ⊢
  exact hall i j hij hj hni hnj

theorem nodup_filter_shrink_blk {lvl tmp tmp' : List (BitVec 32)} {n beg end_b blvl : Nat}
    (htl : n ≤ tmp.length) (htl' : n ≤ tmp'.length)
    (hnd : (((tmp.take n).filter (· ≠ 0xFFFFFFFF#32)).map fun x => x.toNat / 2).Nodup)
    (hout : ∀ k < n, (k < beg ∨ end_b ≤ k) → tmp'[k]? = tmp[k]?)
    (hin_lvl : ∀ k, beg ≤ k → k < end_b → tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      (lvl[(tmp'[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl)
    (hin_uniq : ∀ i j, beg ≤ i → i < j → j < end_b →
      tmp'[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      tmp'[j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 → False)
    (hother_lvl : ∀ k < n, (k < beg ∨ end_b ≤ k) →
      tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      (lvl[(tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠ blvl) :
    (((tmp'.take n).filter (· ≠ 0xFFFFFFFF#32)).map fun x => x.toNat / 2).Nodup := by
  rw [nodup_filter_map_div2_iff htl']
  have hall := (nodup_filter_map_div2_iff htl).mp hnd
  intro i j hij hj hni hnj heq
  by_cases hi_in : beg ≤ i ∧ i < end_b
  · by_cases hj_in : beg ≤ j ∧ j < end_b
    · exact hin_uniq i j hi_in.1 hij hj_in.2 hni hnj
    · have ho : j < beg ∨ end_b ≤ j := by omega
      have htj := hout j hj ho
      have hlj := hother_lvl j hj ho (by rwa [← htj])
      rw [← htj, ← heq] at hlj; exact hlj (hin_lvl i hi_in.1 hi_in.2 hni)
  · have hi_out : i < beg ∨ end_b ≤ i := by omega
    have hti := hout i (by omega) hi_out
    by_cases hj_in : beg ≤ j ∧ j < end_b
    · have hli := hother_lvl i (by omega) hi_out (by rwa [← hti])
      rw [← hti, heq] at hli; exact hli (hin_lvl j hj_in.1 hj_in.2 hnj)
    · have ho : j < beg ∨ end_b ≤ j := by omega
      have htj := hout j hj ho
      rw [hti] at hni heq; rw [htj] at hnj heq; exact hall i j hij hj hni hnj heq

theorem fullMinMarkSpec_step {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {Q' : Post []} {X' : XPost} (hlen : s.LengthsOk c)
    (hm : (FullMem c s ⋆ R) m) (v : BitVec 32) (hv : v.toNat < s.core.cur_vars) (tag : BitVec 8)
    (hpost : ∀ m', (FullMem c (fullMinMarkStepState s v.toNat tag) ⋆ R) m' → Q' () m') :
    Spec.minMarkSpec (c.hdr, v, tag, ()) m Q' X' := by
  dsimp only [Spec.minMarkSpec]
  refine FullContract.intro (w := ()) hlen trivial hm ?_
  intro () s' m' _ hs' hm'
  subst hs'
  dsimp only [fullMinMarkStepState, fullMinMarkStepCore, fullMinMarkState] at hpost ⊢
  by_cases hset : (s.core.mrk[v.toNat]?.getD 0#8 &&& tag) ≠ 0#8
  · have hc : s.core.cur_vars ≤ v.toNat ∨ (s.core.mrk[v.toNat]?.getD 0#8 &&& tag) ≠ 0#8 :=
      Or.inr hset
    simp only [eq_true hc, ↓reduceIte] at hpost hm' ⊢
    exact hpost m' hm'
  · have hc : ¬ (s.core.cur_vars ≤ v.toNat ∨ (s.core.mrk[v.toNat]?.getD 0#8 &&& tag) ≠ 0#8) :=
      fun h => h.elim (fun hle => by omega) hset
    simp only [eq_false hc, ↓reduceIte] at hpost hm' ⊢
    exact hpost m' hm'

theorem fullMinMarkStepState_lengths {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) (v : Nat) (tag : BitVec 8) :
    (fullMinMarkStepState s v tag).LengthsOk c := by
  dsimp only [fullMinMarkStepState, fullMinMarkStepCore]
  split
  · exact hlen
  · exact ⟨fullMinMarkCore_lengths hlen.core_ok tag, hlen.scratch_ok⟩

theorem fullMinMarkStepState_mrk_above {s : FullState} {v : Nat}
    (hv : v < s.core.cur_vars) (tag : BitVec 8) :
    ∀ w, s.core.cur_vars ≤ w → (fullMinMarkStepState s v tag).core.mrk[w]? = s.core.mrk[w]? := by
  intro w hw
  dsimp only [fullMinMarkStepState, fullMinMarkStepCore]
  split
  · rfl
  · exact fullMinMarkCore_mrk_above hv w hw

theorem fullMinMarkStepState_bit8_mono2 {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) {v : Nat} (hv : v < s.core.cur_vars) {tag : BitVec 8}
    (htag : tag = 2#8 ∨ tag = 4#8) (hno8 : (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) :
    (∀ w < s.core.cur_vars, ((fullMinMarkStepState s v tag).core.mrk[w]?.getD 0#8 &&& 8#8) =
      (s.core.mrk[w]?.getD 0#8 &&& 8#8)) ∧
    (∀ w < s.core.cur_vars, (s.core.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 →
      ((fullMinMarkStepState s v tag).core.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8) := by
  have hv_mrk : v < s.core.mrk.length := by
    rw [hlen.core_ok.mrk_len]; have := hlen.core_ok.cur_vars_le; omega
  dsimp only [fullMinMarkStepState, fullMinMarkStepCore, fullMinMarkCore]; split
  · exact ⟨fun _ _ => rfl, fun _ _ h => h⟩
  · refine ⟨fun w _ => ?_, fun w _ h2 => ?_⟩
    · dsimp only; by_cases hwe : w = v
      · subst w; rw [List.getElem?_set_self hv_mrk, Option.getD_some]
        rcases htag with rfl | rfl
        · exact (bv8_and8_pres_or2 hno8).trans hno8.symm
        · exact (bv8_and8_pres_or4 hno8).trans hno8.symm
      · rw [List.getElem?_set_ne (Ne.symm hwe)]
    · dsimp only; by_cases hwe : w = v
      · subst w; rw [List.getElem?_set_self hv_mrk, Option.getD_some]
        rcases htag with rfl | rfl
        · exact bv8_and2_of_or2 _
        · rwa [bv8_and2_pres_or4]
      · rwa [List.getElem?_set_ne (Ne.symm hwe)]

theorem fullMinMarkStepState_dom_clr {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c)
    (hdom : ∀ w < s.core.cur_vars, (s.core.mrk[w]?.getD 0#8 &&& 0xF1#8) = 0#8)
    (hcov : s.core.min_clr_full = 0#64 →
      ∀ w < s.core.cur_vars, (s.core.mrk[w]?.getD 0#8 &&& 6#8) ≠ 0#8 →
        ∃ k < s.core.min_clr_len, (s.core.min_clr[k]?.getD 0#32).toNat = w)
    {v : Nat} (hv : v < s.core.cur_vars) {tag : BitVec 8} (htag : tag = 2#8 ∨ tag = 4#8)
    (hno8 : (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) :
    let s' := fullMinMarkStepState s v tag
    (∀ w < s.core.cur_vars, (s'.core.mrk[w]?.getD 0#8 &&& 0xF1#8) = 0#8) ∧
    (s'.core.min_clr_full = 0#64 →
      ∀ w < s.core.cur_vars, (s'.core.mrk[w]?.getD 0#8 &&& 6#8) ≠ 0#8 →
        ∃ k < s'.core.min_clr_len, (s'.core.min_clr[k]?.getD 0#32).toNat = w) := by
  have hcv := hlen.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold Ref.dimacsBound at hmx
  have hv_mrk : v < s.core.mrk.length := by rw [hlen.core_ok.mrk_len]; omega
  dsimp only [fullMinMarkStepState, fullMinMarkStepCore]
  split
  · exact ⟨hdom, hcov⟩
  · refine ⟨fun w hw => ?_, ?_⟩
    · dsimp only [fullMinMarkCore]
      by_cases hwe : w = v
      · subst hwe
        rw [List.getElem?_set_self hv_mrk, Option.getD_some]
        rcases htag with rfl | rfl
        · exact bv8_and_dom_or2 (hdom w hw)
        · exact bv8_and_dom_or4 (hdom w hw)
      · rw [List.getElem?_set_ne (Ne.symm hwe)]; exact hdom w hw
    · intro hmcf w hw hnz
      dsimp only [fullMinMarkCore] at hmcf hnz ⊢
      by_cases hcur0 : s.core.mrk[v]?.getD 0#8 = 0#8
      · by_cases hlt : s.core.min_clr_len < s.core.cur_vars
        · simp only [hcur0, hlt, and_self, not_true_eq_false, and_false,
            ↓reduceIte] at hmcf hnz ⊢
          by_cases hweq : w = v
          · subst w
            refine ⟨s.core.min_clr_len, by omega, ?_⟩
            rw [List.getElem?_set_self (by rw [hlen.core_ok.min_clr_len_arr]; omega),
              Option.getD_some, bv32_ofNat_toNat (by omega)]
          · have hnz' : (s.core.mrk[w]?.getD 0#8 &&& 6#8) ≠ 0#8 := by
              simpa [List.getElem?_set_ne (Ne.symm hweq)] using hnz
            obtain ⟨k, hk, hkeq⟩ := hcov hmcf w hw hnz'
            exact ⟨k, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hkeq⟩
        · simp only [hcur0, hlt, not_false_eq_true, and_self, ↓reduceIte] at hmcf
          cases hmcf
      · simp only [hcur0, false_and, ↓reduceIte] at hmcf hnz ⊢
        by_cases hweq : w = v
        · subst w
          exact hcov hmcf v hv (fun h6 => hcur0 (bv8_eq_zero_of_masks _ (hdom v hv) hno8 h6))
        · exact hcov hmcf w hw (by simpa [List.getElem?_set_ne (Ne.symm hweq)] using hnz)

theorem fullMinMarkInv_step_poison {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keep : List Nat} (hcore : FullOtfsCoreInv c F0 s) (hmin : FullMinMarkInv s.core keep)
    {v : Nat} (hv : v < s.core.cur_vars) (hno8 : (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) :
    FullMinMarkInv (fullMinMarkStepState s v 4#8).core keep := by
  dsimp only [fullMinMarkStepState, fullMinMarkStepCore]
  split
  · exact hmin
  · exact fullMinMarkInv_poison hcore hmin hv hno8

theorem fullMinMarkInv_step_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keep : List Nat} (hcore : FullOtfsCoreInv c F0 s) (hmin : FullMinMarkInv s.core keep)
    {l : Nat} (hl : l < 2 * s.core.cur_vars) (hkeep : l ∈ keep)
    (hfals : s.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hno8 : (s.core.mrk[l / 2]?.getD 0#8 &&& 8#8) = 0#8) :
    FullMinMarkInv (fullMinMarkStepState s (l / 2) 2#8).core keep := by
  dsimp only [fullMinMarkStepState, fullMinMarkStepCore]
  split
  · exact hmin
  · exact fullMinMarkInv_mark_keep hcore hmin hl hkeep hfals hno8

theorem minLitState_step {s : FullState} {mrk1 : List (BitVec 8)}
    {mstk1 mclr1 : List (BitVec 32)} {mcl1 : Nat} {mcf1 : BitVec 64} (v : Nat) (tag : BitVec 8) :
    let st := minLitState s mrk1 mstk1 mclr1 mcl1 mcf1
    let st' := fullMinMarkStepState st v tag
    st' = minLitState s st'.core.mrk mstk1 st'.core.min_clr st'.core.min_clr_len
      st'.core.min_clr_full := by
  intro st st'
  dsimp only [st', fullMinMarkStepState, fullMinMarkStepCore, fullMinMarkCore, st, minLitState]
  split
  · rfl
  · rfl

/-! ## 3. `trailCount8`, `RsnCov`, `ShrinkResolved`, `ShrinkBaseInv` Helpers -/

@[expose] def trailCount8 (trl : List (BitVec 32)) (mrk : List (BitVec 8)) : Nat → Nat
  | 0 => 0
  | n + 1 => trailCount8 trl mrk n +
      if (mrk[(trl[n]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8 then 1 else 0

theorem trailCount8_mono {trl : List (BitVec 32)} {mrk : List (BitVec 8)}
    {a b : Nat} (h : a ≤ b) : trailCount8 trl mrk a ≤ trailCount8 trl mrk b := by
  induction b with
  | zero => simp [show a = 0 by omega]
  | succ b ih =>
    by_cases he : a = b + 1
    · subst he; exact le_refl _
    · exact Nat.le_trans (ih (by omega)) (Nat.le_add_right _ _)

theorem trailCount8_zero_of_all_zero {trl : List (BitVec 32)} {mrk : List (BitVec 8)}
    {cv lim : Nat} (hlt : ∀ i < lim, (trl[i]?.getD 0#32).toNat / 2 < cv)
    (h0 : ∀ w < cv, (mrk[w]?.getD 0#8 &&& 8#8) = 0#8) :
    ∀ n ≤ lim, trailCount8 trl mrk n = 0 := by
  intro n; induction n with
  | zero => intro _; rfl
  | succ n ih => intro hn; simp [trailCount8, ih (by omega), h0 _ (hlt n (by omega))]

theorem trailCount8_eq_zero_mem {trl : List (BitVec 32)} {mrk : List (BitVec 8)}
    {n j : Nat} (h : trailCount8 trl mrk n = 0) (hj : j < n) :
    (mrk[(trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) = 0#8 := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [trailCount8] at h
    by_cases hjn : j = n
    · subst hjn
      by_cases hnz : (mrk[(trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8
      · simp [hnz] at h
      · exact Decidable.not_not.mp hnz
    · exact ih (by omega) (by omega)

theorem trailCount8_eq_of_bit8_eq {trl : List (BitVec 32)} {mrk1 mrk2 : List (BitVec 8)}
    {n cv : Nat} (hlt : ∀ j < n, (trl[j]?.getD 0#32).toNat / 2 < cv)
    (heq : ∀ w < cv, (mrk2[w]?.getD 0#8 &&& 8#8) = (mrk1[w]?.getD 0#8 &&& 8#8)) :
    trailCount8 trl mrk2 n = trailCount8 trl mrk1 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [trailCount8, ih (fun j hj => hlt j (by omega)),
      heq _ (hlt n (Nat.lt_succ_self n))]

theorem trailCount8_set_bit8_le {trl : List (BitVec 32)} {mrk : List (BitVec 8)}
    {lim : Nat} (hnodup : ∀ i j, i < lim → j < lim →
      (trl[i]?.getD 0#32).toNat / 2 = (trl[j]?.getD 0#32).toNat / 2 → i = j)
    (v : Nat) : ∀ n ≤ lim,
    trailCount8 trl (mrk.set v (mrk[v]?.getD 0#8 ||| 8#8)) n ≤ trailCount8 trl mrk n + 1 := by
  intro n
  induction n with
  | zero => intro _; simp [trailCount8]
  | succ n ih =>
    intro hn
    by_cases hve : (trl[n]?.getD 0#32).toNat / 2 = v
    · have hpre : trailCount8 trl (mrk.set v (mrk[v]?.getD 0#8 ||| 8#8)) n =
          trailCount8 trl mrk n := by
        clear ih
        have hind : ∀ m ≤ n,
            trailCount8 trl (mrk.set v (mrk[v]?.getD 0#8 ||| 8#8)) m =
              trailCount8 trl mrk m := by
          intro m
          induction m with
          | zero => intro _; rfl
          | succ m ihm =>
            intro hm
            have hne : (trl[m]?.getD 0#32).toNat / 2 ≠ v := fun he => by
              have := hnodup m n (by omega) (by omega) (he.trans hve.symm); omega
            simp only [trailCount8, ihm (by omega), List.getElem?_set_ne (Ne.symm hne)]
        exact hind n (le_refl n)
      simp only [trailCount8, hpre]; split <;> split <;> omega
    · simp only [trailCount8, List.getElem?_set_ne (Ne.symm hve)]
      have := ih (by omega)
      omega

theorem trailCount8_step_zero {trl : List (BitVec 32)} {mrk : List (BitVec 8)} {n : Nat}
    (h : (mrk[(trl[n]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) = 0#8) :
    trailCount8 trl mrk (n + 1) = trailCount8 trl mrk n := by simp [trailCount8, h]

theorem trailCount8_step_nz {trl : List (BitVec 32)} {mrk : List (BitVec 8)} {n : Nat}
    (h : (mrk[(trl[n]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8) :
    trailCount8 trl mrk (n + 1) = trailCount8 trl mrk n + 1 := by simp [trailCount8, h]

theorem trailCount8_eq_of_zero_range {trl : List (BitVec 32)} {mrk : List (BitVec 8)}
    {a b : Nat} (hab : a ≤ b)
    (hz : ∀ j, a ≤ j → j < b → (mrk[(trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) = 0#8) :
    trailCount8 trl mrk b = trailCount8 trl mrk a := by
  induction b with
  | zero => simp [show a = 0 by omega]
  | succ b ih =>
    by_cases hbe : a = b + 1
    · subst hbe; rfl
    · rw [trailCount8_step_zero (hz b (by omega) (by omega)),
        ih (by omega) (fun j h1 h2 => hz j h1 (by omega))]

@[expose] def shrinkBlkSt (s : FullState) (tmp1 : List (BitVec 32)) (mrk1 : List (BitVec 8))
    (mstk1 mclr1 : List (BitVec 32)) (mcl1 : Nat) (mcf1 : BitVec 64)
    (sstk1 : List (BitVec 32)) : FullState :=
  { core := { s.core with
      tmp := tmp1, mrk := mrk1, min_stk := mstk1, min_clr := mclr1,
      min_clr_len := mcl1, min_clr_full := mcf1 }
    scratch := { s.scratch with shrink_stk := sstk1 } }

theorem coreInv_shrinkBlk {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {tmp1 : List (BitVec 32)} {mrk1 : List (BitVec 8)}
    {mstk1 mclr1 sstk1 : List (BitVec 32)} {mcl1 : Nat} {mcf1 : BitVec 64}
    (htmp : tmp1.length = c.max_vars) (hmrk : mrk1.length = c.max_vars)
    (hmstk : mstk1.length = 2 * c.minDepth) (hmclr : mclr1.length = c.max_vars)
    (hmcl : mcl1 ≤ c.max_vars) (hsstk : sstk1.length = c.max_vars) :
    FullOtfsCoreInv c F0 (shrinkBlkSt s tmp1 mrk1 mstk1 mclr1 mcl1 mcf1 sstk1) :=
  fullOtfsCoreInv_with_min_tmp hcore htmp hcore.1.core_ok.tmp_len_le hmrk hmstk hmclr hmcl
    { hcore.1.scratch_ok with shrink_stk_len := hsstk }

theorem shrinkBlkSt_step {s : FullState} {tmp1 : List (BitVec 32)}
    {mrk1 : List (BitVec 8)} {mstk1 mclr1 sstk1 : List (BitVec 32)} {mcl1 : Nat}
    {mcf1 : BitVec 64} (v : Nat) (tag : BitVec 8) :
    let sb := shrinkBlkSt s tmp1 mrk1 mstk1 mclr1 mcl1 mcf1 sstk1
    let sb' := fullMinMarkStepState sb v tag
    sb' = shrinkBlkSt s tmp1 sb'.core.mrk mstk1 sb'.core.min_clr sb'.core.min_clr_len
      sb'.core.min_clr_full sstk1 := by
  intro sb sb'
  dsimp only [sb', fullMinMarkStepState, fullMinMarkStepCore, fullMinMarkCore, sb, shrinkBlkSt]
  split <;> rfl

@[expose] def RsnCov (k : FullCoreState) (P : Nat → Prop) (idx : Nat) : Prop :=
  let p := (k.trl[idx]?.getD 0#32).toNat
  (k.lvl[p / 2]?.getD 0#32).toNat < k.cur_level ∧
  let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
  rsn ≠ 0xFFFFFFFF#32 ∧
  if (rsn &&& 0x80000000#32) ≠ 0#32 then
    let ot := (rsn &&& 0x7FFFFFFF#32).toNat
    ot < 2 * k.cur_vars ∧
    ∃ j < idx, (k.trl[j]?.getD 0#32).toNat = ot ^^^ 1 ∧
      ((k.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨ P (ot / 2))
  else
    rsn.toNat ∈ fullArenaClauseRefsCore k ∧ fullArenaClauseGarbCore k rsn.toNat = false ∧
    ∀ q ∈ fullArenaClauseLitsCore k rsn.toNat,
      q = p ∨ ∃ j < idx, (k.trl[j]?.getD 0#32).toNat = q ^^^ 1 ∧
        ((k.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ P (q / 2))

theorem rsnCov_mono {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {P1 P2 : Nat → Prop}
    (hP : ∀ w < s.core.cur_vars, P1 w → P2 w) {idx : Nat} (h : RsnCov s.core P1 idx) :
    RsnCov s.core P2 idx := by
  obtain ⟨F_cur, hw⟩ := hcore.2
  dsimp only [RsnCov] at h ⊢
  rcases h with ⟨hlv, hne, hif⟩
  refine ⟨hlv, hne, ?_⟩
  split at hif <;> split
  · obtain ⟨hot, j, hj, hjeq, hdep⟩ := hif
    exact ⟨hot, j, hj, hjeq, hdep.elim Or.inl fun h1 => Or.inr (hP _ (by omega) h1)⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · obtain ⟨href, hng, hall⟩ := hif
    refine ⟨href, hng, fun q hq => ?_⟩
    have hqlt := hw.arena.lits_lt _ href hng _ hq
    rcases hall q hq with rfl | ⟨j, hj, hjeq, hdep⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨j, hj, hjeq, hdep.elim Or.inl fun h1 => Or.inr (hP _ (by omega) h1)⟩

abbrev ShrinkResolved (k : FullCoreState) (mrk : List (BitVec 8)) (idx : Nat) : Prop :=
  RsnCov k (fun w => (mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 ∨ (mrk[w]?.getD 0#8 &&& 8#8) ≠ 0#8) idx

theorem remSound_lift_mrk2 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {mrk1 mrk2 : List (BitVec 8)}
    (hm2 : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    {idx : Nat} (h : RsnCov s.core (fun w => (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8) idx) :
    RsnCov s.core (fun w => (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8) idx :=
  rsnCov_mono hcore hm2 h

theorem shrinkResolved_mono {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {mrk1 mrk2 : List (BitVec 8)}
    (hm2 : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hm8 : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 8#8) ≠ 0#8)
    {idx : Nat} (hr : ShrinkResolved s.core mrk1 idx) :
    ShrinkResolved s.core mrk2 idx :=
  rsnCov_mono hcore (fun w hw h => h.elim (fun h2 => Or.inl (hm2 w hw h2))
    (fun h8 => Or.inr (hm8 w hw h8))) hr

theorem shrinkResolved_to_rem {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {mrk1 mrk2 : List (BitVec 8)}
    (hm2 : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hm8 : ∀ w < s.core.cur_vars,
      (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 → (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    {idx : Nat} (hr : ShrinkResolved s.core mrk1 idx) :
    RsnCov s.core (fun w => (mrk2[w]?.getD 0#8 &&& 2#8) ≠ 0#8) idx :=
  rsnCov_mono hcore (fun w hw h => h.elim (hm2 w hw) (hm8 w hw)) hr

structure ShrinkBaseInv (c : FullCfg) (s : FullState)
    (mrk1 : List (BitVec 8)) (mstk1 mclr1 : List (BitVec 32)) (mcl1 : Nat) (mcf1 : BitVec 64)
    (sstk1 : List (BitVec 32)) (slen : Nat) (keep0 : List Nat) : Prop where
  mrk_len : mrk1.length = c.max_vars
  mstk_len : mstk1.length = 2 * c.minDepth
  mclr_len : mclr1.length = c.max_vars
  mcl_le : mcl1 ≤ c.max_vars
  sstk_len : sstk1.length = c.max_vars
  slen_le : slen ≤ s.core.cur_vars
  mrk_above : ∀ w, s.core.cur_vars ≤ w → mrk1[w]? = s.core.mrk[w]?
  min_inv : FullMinMarkInv (shrinkBlkSt s s.core.tmp mrk1 mstk1 mclr1 mcl1 mcf1 sstk1).core keep0
  mono2 : ∀ w < s.core.cur_vars,
    (s.core.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk1[w]?.getD 0#8 &&& 2#8) ≠ 0#8
  bit8_sstk : ∀ w < s.core.cur_vars, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
    ∃ j < slen, (sstk1[j]?.getD 0#32).toNat = w
  sstk_lt : ∀ j < slen, (sstk1[j]?.getD 0#32).toNat < s.core.cur_vars

theorem shrinkBaseInv_core {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {mrk1 : List (BitVec 8)} {mstk1 mclr1 sstk1 : List (BitVec 32)}
    {mcl1 slen : Nat} {mcf1 : BitVec 64} {keep0 : List Nat}
    (hb : ShrinkBaseInv c s mrk1 mstk1 mclr1 mcl1 mcf1 sstk1 slen keep0) :
    FullOtfsCoreInv c F0 (shrinkBlkSt s s.core.tmp mrk1 mstk1 mclr1 mcl1 mcf1 sstk1) :=
  coreInv_shrinkBlk hcore hcore.1.core_ok.tmp_len_arr hb.mrk_len hb.mstk_len hb.mclr_len
    hb.mcl_le hb.sstk_len

theorem getElem?_getD_of_getElem {α : Type _} (d : α) {xs ys : List α}
    {i j : Nat} {hj : j < ys.length} (hxy : xs = ys) (hij : i = j) :
    xs[i]?.getD d = ys[j]'hj := by
  subst hxy hij; rw [List.getElem?_eq_getElem hj, Option.getD_some]

theorem shrink_arena_lits_mem {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {cref pos : Nat}
    (href : cref ∈ fullArenaClauseRefsCore s.core)
    (hp : pos < fullArenaClauseSizeCore s.core cref) :
    (s.core.arena[cref + 3 + pos]?.getD 0#32).toNat ∈ fullArenaClauseLitsCore s.core cref := by
  obtain ⟨_, hw⟩ := hcore.2
  have hwf := hw.arena.refs_wf cref href
  have hbd : cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena.length := by
    have := hwf.2.2.1; have := hwf.2.2.2.1
    have := hcore.1.core_ok.arena_len_le; have := hcore.1.core_ok.arena_len_arr; omega
  rw [mem_fullArenaClauseLitsCore_iff hbd]
  exact ⟨pos, hp, by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]⟩

theorem shrink_rsn_loop_done {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {mrk : List (BitVec 8)} {idx : Nat}
    (hi : idx < s.core.trail_end)
    (hlvl : (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level)
    (hrs : s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
      0xFFFFFFFF#32)
    (hcov :
      let rsn := s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
      let is_bin := (rsn &&& 0x80000000#32) ≠ 0#32
      let csz := if is_bin then 1 else fullArenaClauseSizeCore s.core rsn.toNat
      ∀ j < csz,
        let q := if is_bin then (rsn &&& 0x7FFFFFFF#32).toNat
                 else (s.core.arena[rsn.toNat + 3 + j]?.getD 0#32).toNat
        q = (s.core.trl[idx]?.getD 0#32).toNat ∨ ∃ m < idx,
          (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
          ((s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (mrk[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 ∨
            (mrk[q / 2]?.getD 0#8 &&& 8#8) ≠ 0#8)) :
    ShrinkResolved s.core mrk idx := by
  obtain ⟨_, hw⟩ := hcore.2
  have hr := hw.reason_inv_below idx hi hlvl hrs
  dsimp only [ShrinkResolved, RsnCov] at hr hcov ⊢
  refine ⟨hlvl, hrs, ?_⟩
  by_cases hbin : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
      0x80000000#32) ≠ 0#32
  · simp only [eq_true hbin, ↓reduceIte] at hr hcov ⊢
    refine ⟨hr.1, ?_⟩
    rcases hcov 0 (by omega) with heq | hex
    · exfalso; obtain ⟨m, hm, hmeq, _⟩ := hr.2.2
      have hln := litVar_litNeg (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat
      unfold litVar litNeg at hln
      have hmi := hw.trail_vars_nodup m idx (by omega) hi (by rw [hmeq, hln, heq]); omega
    · exact hex
  · simp only [eq_false hbin, ↓reduceIte] at hr hcov ⊢
    refine ⟨hr.1, hr.2.1, fun q hq => ?_⟩
    have hwf := hw.arena.refs_wf _ hr.1
    have hbd : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat + 3 +
        fullArenaClauseSizeCore s.core (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32).toNat ≤ s.core.arena.length := by
      have := hwf.2.2.1; have := hwf.2.2.2.1
      have := hcore.1.core_ok.arena_len_le; have := hcore.1.core_ok.arena_len_arr; omega
    obtain ⟨j, hj, hjeq⟩ := (mem_fullArenaClauseLitsCore_iff hbd).mp hq
    have hqj := hcov j hj
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some, hjeq] at hqj

end

end LeanQbe.T.Examples.Kissat.Proof.Minimize
