module

public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.Full2
import all Kraken.Mem
import all Kraken.Separation

/-!
# Soundness Proofs for Kissat `D-Full` Minimization & Shrinking (`Stage 4`, Part 1)

Defines scoped `FullMinTactics`, the purely structural `FullMinSpecs.FullMinMarkInv`,
all `8` function specs in `namespace FullMinSpecs` (zero collision with `FullSpec*`),
and proves parametric `(Γ : Env)` `Func.wp` theorems for the first `2` functions:
1. `full_tmp_less` (`full_tmp_less_wp`)
2. `full_min_mark` (`full_min_mark_wp`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Bitvector arithmetic lemmas and scoped `FullMinTactics` -/

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
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have ht := congrArg BitVec.toNat h
    have ha : a.toNat < 2 ^ 32 := by have := a.isLt; omega
    simpa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt ha] using ht
  · rintro rfl; rfl

theorem bv8_and_zext32_zero_iff (a b : BitVec 8) :
    (a.setWidth 32 &&& b.setWidth 32 = 0#32) ↔ (a &&& b = 0#8) := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have ht := congrArg BitVec.toNat h
    have ha : a.toNat < 2 ^ 8 := a.isLt
    have hb : b.toNat < 2 ^ 8 := b.isLt
    have hab : (a.toNat &&& b.toNat) < 2 ^ 8 := Nat.and_lt_two_pow a.toNat hb
    simpa [BitVec.toNat_and, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (by omega : a.toNat < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : (a.toNat &&& b.toNat) < 2 ^ 32)] using ht
  · intro h
    apply BitVec.eq_of_toNat_eq
    have ht := congrArg BitVec.toNat h
    have ha : a.toNat < 2 ^ 8 := a.isLt
    have hb : b.toNat < 2 ^ 8 := b.isLt
    simpa [BitVec.toNat_and, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (by omega : a.toNat < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 32)] using ht

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

theorem bv64_shl1_toNat {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 64) :
    (x <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat = 2 * x.toNat :=
  FullMinTactics.bv_c0_shl1_toNat hx

theorem bv64_shl1_add1_toNat {x : BitVec 64} (hx : 2 * x.toNat + 1 < 2 ^ 64) :
    (x <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1).toNat = 2 * x.toNat + 1 :=
  FullMinTactics.bv_c0_shl1_add1_toNat hx

theorem bv64_shl1_toNat_raw {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 64) :
    (x <<< ((1 : BitVec 64).toNat % 64)).toNat = 2 * x.toNat := by
  have hm : (1 : BitVec 64).toNat % 64 = 1 := rfl
  rw [hm, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]; omega

theorem bv64_shl1_add1_toNat_raw {x : BitVec 64} (hx : 2 * x.toNat + 1 < 2 ^ 64) :
    (x <<< ((1 : BitVec 64).toNat % 64) + 1).toNat = 2 * x.toNat + 1 := by
  have hsh := bv64_shl1_toNat_raw (x := x) (by omega)
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_add, hsh, h1, Nat.mod_eq_of_lt hx]

/-! ## 2. `FullCoreState` / `FullWitnessInv` / `FullCoreInv` minimization update helpers -/

abbrev minLitState (s : FullState) (mrk1 : List (BitVec 8))
    (mstk1 mclr1 : List (BitVec 32)) (mcl1 : Nat) (mcf1 : BitVec 64) : FullState :=
  { s with core := { s.core with
      mrk := mrk1, min_stk := mstk1, min_clr := mclr1,
      min_clr_len := mcl1, min_clr_full := mcf1 } }

theorem fullWitness_with_min {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    {tmp1 : List (BitVec 32)} {tl1 : Nat} {mrk1 : List (BitVec 8)}
    {mstk1 mclr1 : List (BitVec 32)} {mcl1 : Nat} {mcf1 : BitVec 64} :
    FullWitnessInv c F0 F_cur
      { k with tmp := tmp1, tmp_len := tl1, mrk := mrk1, min_stk := mstk1,
               min_clr := mclr1, min_clr_len := mcl1, min_clr_full := mcf1 } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem fullCoreInv_with_min {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullCoreInv c F0 s) {mrk1 : List (BitVec 8)}
    {mstk1 mclr1 : List (BitVec 32)} {mcl1 : Nat} {mcf1 : BitVec 64}
    (hmrk : mrk1.length = c.max_vars) (hmstk : mstk1.length = 2 * c.minDepth)
    (hmclr : mclr1.length = c.max_vars) (hmcl : mcl1 ≤ c.max_vars) :
    FullCoreInv c F0 (minLitState s mrk1 mstk1 mclr1 mcl1 mcf1) := by
  obtain ⟨F_cur, hw⟩ := hcore.witness
  exact ⟨⟨{ hcore.lengths.core_ok with
      mrk_len := hmrk, min_stk_len := hmstk,
      min_clr_len_arr := hmclr, min_clr_len_le := hmcl },
    hcore.lengths.scratch_ok⟩,
    ⟨F_cur, fullWitness_with_min hw⟩⟩

theorem fullCoreInv_with_min_tmp {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullCoreInv c F0 s) {tmp1 : List (BitVec 32)} {tl1 : Nat}
    {mrk1 : List (BitVec 8)} {mstk1 mclr1 : List (BitVec 32)}
    {mcl1 : Nat} {mcf1 : BitVec 64} {sc1 : FullScratch}
    (htmp : tmp1.length = c.max_vars) (htl : tl1 ≤ c.max_vars)
    (hmrk : mrk1.length = c.max_vars) (hmstk : mstk1.length = 2 * c.minDepth)
    (hmclr : mclr1.length = c.max_vars) (hmcl : mcl1 ≤ c.max_vars)
    (hsc : sc1.LengthsOk c) :
    FullCoreInv c F0 {
      core := { s.core with
        tmp := tmp1, tmp_len := tl1, mrk := mrk1, min_stk := mstk1,
        min_clr := mclr1, min_clr_len := mcl1, min_clr_full := mcf1 }
      scratch := sc1 } := by
  obtain ⟨F_cur, hw⟩ := hcore.witness
  exact ⟨⟨{ hcore.lengths.core_ok with
      tmp_len_arr := htmp, tmp_len_le := htl, mrk_len := hmrk, min_stk_len := hmstk,
      min_clr_len_arr := hmclr, min_clr_len_le := hmcl },
    hsc⟩,
    ⟨F_cur, fullWitness_with_min hw⟩⟩

/-! ## 3. Purely structural `FullMinMarkInv`, sorting predicates, and all `8` specs -/

namespace FullMinSpecs

/-- Purely structural minimization mark invariant on `FullCoreState` (independent of `F_cur`,
combining with ANY witness `FullWitnessInv c F0 F_cur k` to prove `F_cur`-entailment). -/
structure FullMinMarkInv (k : FullCoreState) (keep : List Nat) : Prop where
  mrk_dom : ∀ v < k.cur_vars, (k.mrk[v]?.getD 0#8 &&& 0xF1#8) = 0#8
  clr_cov : k.min_clr_full = 0#64 →
    ∀ v < k.cur_vars, (k.mrk[v]?.getD 0#8 &&& 6#8) ≠ 0#8 →
      ∃ j < k.min_clr_len, (k.min_clr[j]?.getD 0#32).toNat = v
  rem_sound : ∀ idx < k.trail_end,
    let p := (k.trl[idx]?.getD 0#32).toNat
    (k.mrk[p / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 →
    (p ^^^ 1) ∈ keep ∨
      let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 ∧
      if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * k.cur_vars ∧
        ∃ j < idx, (k.trl[j]?.getD 0#32).toNat = ot ^^^ 1 ∧
          ((k.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨ (k.mrk[ot / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
      else
        rsn.toNat ∈ fullArenaClauseRefsCore k ∧ fullArenaClauseGarbCore k rsn.toNat = false ∧
        ∀ q ∈ fullArenaClauseLitsCore k rsn.toNat,
          q = p ∨ ∃ j < idx, (k.trl[j]?.getD 0#32).toNat = q ^^^ 1 ∧
            ((k.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (k.mrk[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)

/-- Core state update performed by `full_min_mark(h, v, tag)` when `v < cur_vars` and
`(mrk[v] &&& tag) = 0#8`. -/
def fullMinMarkCore (k : FullCoreState) (v : Nat) (tag : BitVec 8) : FullCoreState :=
  let cur := k.mrk[v]?.getD 0#8
  let mclr' := if cur = 0#8 ∧ k.min_clr_len < k.cur_vars then
                 k.min_clr.set k.min_clr_len (BitVec.ofNat 32 v)
               else k.min_clr
  let mcl' := if cur = 0#8 ∧ k.min_clr_len < k.cur_vars then k.min_clr_len + 1 else k.min_clr_len
  let mcf' := if cur = 0#8 ∧ ¬ k.min_clr_len < k.cur_vars then 1#64 else k.min_clr_full
  { k with mrk := k.mrk.set v (cur ||| tag),
           min_clr := mclr', min_clr_len := mcl', min_clr_full := mcf' }

def fullMinMarkState (s : FullState) (v : Nat) (tag : BitVec 8) : FullState :=
  { s with core := fullMinMarkCore s.core v tag }

/-- Exact state transition of `full_min_mark(h, v, tag)` including early returns. -/
def fullMinMarkStepCore (k : FullCoreState) (v : Nat) (tag : BitVec 8) : FullCoreState :=
  if k.cur_vars ≤ v ∨ (k.mrk[v]?.getD 0#8 &&& tag) ≠ 0#8 then k
  else fullMinMarkCore k v tag

def fullMinMarkStepState (s : FullState) (v : Nat) (tag : BitVec 8) : FullState :=
  { s with core := fullMinMarkStepCore s.core v tag }

theorem fullMinMarkInv_init {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullCoreInv c F0 s) (hmc : FullMarksClear s) (keep : List Nat) :
    FullMinMarkInv s.core keep := by
  obtain ⟨F_cur, hw⟩ := hcore.witness
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

theorem fullMinMarkInv_with_tmp {k : FullCoreState} {keep : List Nat}
    (h : FullMinMarkInv k keep) (tmp' : List (BitVec 32)) :
    FullMinMarkInv { k with tmp := tmp' } keep :=
  ⟨h.mrk_dom, h.clr_cov, h.rem_sound⟩

theorem fullMinMarkInv_mrk_ne_zero_iff {k : FullCoreState} {keep : List Nat}
    (hmin : FullMinMarkInv k keep)
    (hno8 : ∀ v < k.cur_vars, (k.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) {v : Nat} (hv : v < k.cur_vars) :
    k.mrk[v]?.getD 0#8 ≠ 0#8 ↔ (k.mrk[v]?.getD 0#8 &&& 6#8) ≠ 0#8 := by
  constructor
  · intro hnz h6; exact hnz (bv8_eq_zero_of_masks _ (hmin.mrk_dom v hv) (hno8 v hv) h6)
  · intro h6 hz; rw [hz] at h6; exact absurd rfl h6

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
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) {j q : Nat} (hj : j < k.trail_end)
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
  have hmx := c.hmaxv; unfold dimacsBound at hmx
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
    {k k' : FullCoreState} {keep : List Nat} (hw : FullWitnessInv c F0 F_cur k)
    (hk_eq : k'.cur_vars = k.cur_vars ∧ k'.trail_end = k.trail_end ∧ k'.trl = k.trl ∧
      k'.lvl = k.lvl ∧ k'.rsns = k.rsns ∧ k'.arena = k.arena ∧ k'.arena_len = k.arena_len)
    (hmono : ∀ w < k.cur_vars,
      (k.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (k'.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hprev : FullMinMarkInv k keep) {idx : Nat} (hi : idx < k.trail_end)
    (h2' : (k.mrk[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) :
    let p := (k'.trl[idx]?.getD 0#32).toNat
    (p ^^^ 1) ∈ keep ∨
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
  rcases hk_eq with ⟨hcv, _, htrl, hlvl, hrsn, har, hal⟩
  rw [hcv, htrl, hrsn, hlvl]
  have hr : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k := by
    simp [fullArenaClauseRefsCore, har, hal]
  have hcl : ∀ r, fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := fun r => by
    simp [fullArenaClauseGarbCore, fullArenaHdrCore, fullArenaClauseLitsCore,
      fullArenaClauseSizeCore, har]
  rcases hprev.rem_sound idx hi h2' with hin | ⟨hne, hif⟩
  · exact Or.inl hin
  · refine Or.inr ⟨hne, ?_⟩
    split at hif <;> split
    · obtain ⟨hot, j, hj, hjeq, hdep⟩ := hif
      exact ⟨hot, j, hj, hjeq, hdep.elim Or.inl fun hj2 => Or.inr (hmono _ (by omega) hj2)⟩
    · rename_i h1 h2; exact absurd h1 h2
    · rename_i h1 h2; exact absurd h2 h1
    · obtain ⟨href, hng, hall⟩ := hif
      refine ⟨by rw [hr]; exact href, by rw [(hcl _).1]; exact hng, fun q hq => ?_⟩
      rw [(hcl _).2] at hq
      rcases hall q hq with rfl | ⟨j, hj, hjeq, hdep⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨j, hj, hjeq, hdep.elim Or.inl fun hj2 =>
          Or.inr (hmono _ (full_trail_xor_var_lt hw (Nat.lt_trans hj hi) hjeq) hj2)⟩

theorem fullMinMarkInv_set_bit8 {c : FullCfg} {F0 : CNF Nat} {s : FullState} {keep : List Nat}
    (hcore : FullCoreInv c F0 s) (hmin : FullMinMarkInv s.core keep)
    {v : Nat} (hv : v < s.core.cur_vars) :
    FullMinMarkInv { s.core with mrk := s.core.mrk.set v (s.core.mrk[v]?.getD 0#8 ||| 8#8) }
      keep := by
  obtain ⟨F_cur, hw⟩ := hcore.witness
  let k' : FullCoreState :=
    { s.core with mrk := s.core.mrk.set v (s.core.mrk[v]?.getD 0#8 ||| 8#8) }
  change FullMinMarkInv k' keep
  have hlen := hcore.lengths.core_ok
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
    exact fullMinMarkInv_lift_sound (k' := k') hw ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun w hw' h => by rwa [hbit2 w hw']) hmin hi (by rwa [← hbit2 _ hvw])

theorem fullMinMarkInv_clear_bit8 {c : FullCfg} {F0 : CNF Nat} {s : FullState} {keep : List Nat}
    (hcore : FullCoreInv c F0 s) (hmin : FullMinMarkInv s.core keep)
    {v : Nat} (hv : v < s.core.cur_vars) :
    FullMinMarkInv { s.core with mrk := s.core.mrk.set v (s.core.mrk[v]?.getD 0#8 &&& 0xF7#8) }
      keep := by
  obtain ⟨F_cur, hw⟩ := hcore.witness
  let k' : FullCoreState :=
    { s.core with mrk := s.core.mrk.set v (s.core.mrk[v]?.getD 0#8 &&& 0xF7#8) }
  change FullMinMarkInv k' keep
  have hlen := hcore.lengths.core_ok
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
    exact fullMinMarkInv_lift_sound (k' := k') hw ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun w hw' h => by rwa [hbit2 w hw']) hmin hi (by rwa [← hbit2 _ hvw])

theorem fullMinMarkInv_poison {c : FullCfg} {F0 : CNF Nat} {s : FullState} {keep : List Nat}
    (hcore : FullCoreInv c F0 s) (hmin : FullMinMarkInv s.core keep)
    {v : Nat} (hv : v < s.core.cur_vars) (hno8 : (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) :
    FullMinMarkInv (fullMinMarkCore s.core v 4#8) keep := by
  obtain ⟨F_cur, hw⟩ := hcore.witness
  let k' := fullMinMarkCore s.core v 4#8
  change FullMinMarkInv k' keep
  have hlen := hcore.lengths.core_ok
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
    exact fullMinMarkInv_lift_sound (k' := k') hw ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun w hw' h => by rwa [hbit2 w hw']) hmin hi (by rwa [← hbit2 _ hvw])

theorem fullMinMarkInv_mark_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keep : List Nat} (hcore : FullCoreInv c F0 s) (hmin : FullMinMarkInv s.core keep)
    {l : Nat} (hl : l < 2 * s.core.cur_vars) (hkeep : l ∈ keep)
    (hfals : s.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hno8 : (s.core.mrk[l / 2]?.getD 0#8 &&& 8#8) = 0#8) :
    FullMinMarkInv (fullMinMarkCore s.core (l / 2) 2#8) keep := by
  obtain ⟨F_cur, hw⟩ := hcore.witness
  let v := l / 2
  let k' := fullMinMarkCore s.core v 2#8
  change FullMinMarkInv k' keep
  have hlen := hcore.lengths.core_ok
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
    · have h2' : (s.core.mrk[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
        simpa [k', fullMinMarkCore, List.getElem?_set_ne (Ne.symm hveq)] using h2
      exact fullMinMarkInv_lift_sound (k' := k') hw ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        hmono hmin hi' h2'

theorem fullMinMarkInv_mark_rem {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keep : List Nat} (hcore : FullCoreInv c F0 s) (hmin : FullMinMarkInv s.core keep)
    {idx0 : Nat} (hi0 : idx0 < s.core.trail_end)
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
  obtain ⟨F_cur, hw⟩ := hcore.witness
  let v := (s.core.trl[idx0]?.getD 0#32).toNat / 2
  let k' := fullMinMarkCore s.core v 2#8
  change FullMinMarkInv k' keep
  have hlen := hcore.lengths.core_ok
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
      obtain ⟨hne, hif⟩ := hrsn; refine Or.inr ⟨hne, ?_⟩
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
    · have h2' : (s.core.mrk[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
        simpa [k', fullMinMarkCore, List.getElem?_set_ne (Ne.symm hveq)] using h2
      exact fullMinMarkInv_lift_sound (k' := k') hw ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        hmono hmin hi' h2'

theorem fullMinMarkInv_drop {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keep keep' : List Nat} (hcore : FullCoreInv c F0 s) (hmin : FullMinMarkInv s.core keep)
    {root_lit : Nat} (hsub : ∀ l ∈ keep, l = root_lit ∨ l ∈ keep')
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
  obtain ⟨F_cur, hw⟩ := hcore.witness
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
      subst hidx; rw [hroot]; exact Or.inr hrsn
    · exact Or.inl hin'
  · exact Or.inr hok

private theorem full_trail_lit_false_strong {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {keep : List Nat} (hw : FullWitnessInv c F0 F_cur k)
    (hmin : FullMinMarkInv k keep) (α : Nat → Bool) (hα : (cnfOfClauses F_cur).Sat α)
    (hkeep_false : ∀ l ∈ keep, α (litVar l) ≠ !(litSign l)) :
    ∀ i < k.trail_end, let p := (k.trl[i]?.getD 0#32).toNat
      (k.lvl[p / 2]?.getD 0#32).toNat = 0 ∨ (k.mrk[p / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 →
      α (litVar p) = !(litSign p) := by
  intro i hi p hcond
  rcases hcond with hl0 | hrem
  · exact (sat_cnfClause_singleton α p).mp
      (CNF.entails_clause_def.mp (hw.level0_sound i hi hl0) α hα)
  · rcases hmin.rem_sound i hi hrem with hin | ⟨hne, hif⟩
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
        have hri := hw.reason_inv i hi hne
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

/-- Universal `F_cur`-entailment soundness of clause minimization via `FullMinMarkInv`. -/
theorem fullMinMark_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {orig keep : List Nat}
    (hw : FullWitnessInv c F0 F_cur k) (hmin : FullMinMarkInv k keep)
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

/-! ### Sorting order & heap predicates (for `full_sort_tmp_sift` / `full_sort_tmp`) -/

def tmpKey (lvl tpos : List (BitVec 32)) (x : BitVec 32) : Nat × Nat :=
  let v := x.toNat / 2
  ((lvl[v]?.getD 0#32).toNat, (tpos[v]?.getD 0#32).toNat)

def tmpLt (lvl tpos : List (BitVec 32)) (a b : BitVec 32) : Prop :=
  (tmpKey lvl tpos a).1 < (tmpKey lvl tpos b).1 ∨
  ((tmpKey lvl tpos a).1 = (tmpKey lvl tpos b).1 ∧
   (tmpKey lvl tpos a).2 < (tmpKey lvl tpos b).2)

def tmpLe (lvl tpos : List (BitVec 32)) (a b : BitVec 32) : Prop :=
  ¬ tmpLt lvl tpos b a

def SortSliceEq (a b : List (BitVec 32)) (hi : Nat) : Prop :=
  (∀ j, 1 ≤ j → j < hi → ∃ i, 1 ≤ i ∧ i < hi ∧ a[j]? = b[i]?) ∧
  (∀ i, 1 ≤ i → i < hi → ∃ j, 1 ≤ j ∧ j < hi ∧ b[i]? = a[j]?)

def IsHeapAt (lvl tpos tmp : List (BitVec 32)) (i lim : Nat) : Prop :=
  (2 * i + 1 < lim →
    tmpLe lvl tpos (tmp[1 + (2 * i + 1)]?.getD 0#32) (tmp[1 + i]?.getD 0#32)) ∧
  (2 * i + 2 < lim →
    tmpLe lvl tpos (tmp[1 + (2 * i + 2)]?.getD 0#32) (tmp[1 + i]?.getD 0#32))

def IsMaxHeapFrom (lvl tpos tmp : List (BitVec 32)) (lo lim : Nat) : Prop :=
  ∀ i, lo ≤ i → i < lim → IsHeapAt lvl tpos tmp i lim

/-! ### All `8` function specifications in `FullMinSpecs` -/

def fullMinMarkSpec : Spec [i64, i32, i8] [] := fun (h, v, tag, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    let cur := s.core.mrk[v.toNat]?.getD 0#8
    if s.core.cur_vars ≤ v.toNat ∨ (cur &&& tag) ≠ 0#8 then
      Q () m
    else
      let mrk' := s.core.mrk.set v.toNat (cur ||| tag)
      if cur ≠ 0#8 then
        ∀ m', (FullMem c { s with core := { s.core with mrk := mrk' } } ⋆ R) m' → Q () m'
      else if s.core.min_clr_len < s.core.cur_vars then
        ∀ m', (FullMem c { s with core := { s.core with
          mrk := mrk', min_clr := s.core.min_clr.set s.core.min_clr_len v,
          min_clr_len := s.core.min_clr_len + 1 } } ⋆ R) m' → Q () m'
      else
        ∀ m', (FullMem c { s with core := { s.core with
          mrk := mrk', min_clr_full := 1#64 } } ⋆ R) m' → Q () m'

def fullTmpLessSpec : Spec [i64, i64, i32, i32] [.bool] :=
  fun (lvl_ptr, tpos_ptr, a, b, ()) m Q _ =>
    ∃ (lvl tpos : List (BitVec 32)) (R : Mem 64 → Prop),
      let va := a.toNat / 2
      let vb := b.toNat / 2
      let la := (lvl[va]?.getD 0#32).toNat
      let lb := (lvl[vb]?.getD 0#32).toNat
      va < lvl.length ∧ vb < lvl.length ∧ va < tpos.length ∧ vb < tpos.length ∧
      (array (t := i32) lvl_ptr lvl ⋆ array (t := i32) tpos_ptr tpos ⋆ R) m ∧
      Q (decide (la < lb ∨ (la = lb ∧
        (tpos[va]?.getD 0#32).toNat < (tpos[vb]?.getD 0#32).toNat)), ()) m

def fullSortTmpSiftSpec : Spec [i64, i64, i64, i64, i64] [] :=
  fun (tmp_ptr, lvl_ptr, tpos_ptr, start, n, ()) m Q _ =>
    ∃ (tmp lvl tpos : List (BitVec 32)) (R : Mem 64 → Prop),
      start.toNat < n.toNat ∧ 1 + n.toNat ≤ tmp.length ∧ n.toNat < 2 ^ 60 ∧
      (∀ k, 1 ≤ k → k < 1 + n.toNat →
        (tmp[k]?.getD 0#32).toNat / 2 < lvl.length ∧
        (tmp[k]?.getD 0#32).toNat / 2 < tpos.length) ∧
      IsMaxHeapFrom lvl tpos tmp (start.toNat + 1) n.toNat ∧
      (array (t := i32) tmp_ptr tmp ⋆ array (t := i32) lvl_ptr lvl ⋆
        array (t := i32) tpos_ptr tpos ⋆ R) m ∧
      ∀ tmp' m',
        tmp'.length = tmp.length →
        (∀ k, (k = 0 ∨ 1 + n.toNat ≤ k) → tmp'[k]? = tmp[k]?) →
        SortSliceEq tmp' tmp (1 + n.toNat) →
        IsMaxHeapFrom lvl tpos tmp' start.toNat n.toNat →
        (array (t := i32) tmp_ptr tmp' ⋆ array (t := i32) lvl_ptr lvl ⋆
          array (t := i32) tpos_ptr tpos ⋆ R) m' → Q () m'

def fullSortTmpSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.tmp_len ≤ c.max_vars ∧
    (∀ k, 1 ≤ k → k < s.core.tmp_len → (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ tmp' m',
      tmp'.length = c.max_vars →
      (0 < s.core.tmp_len → tmp'[0]? = s.core.tmp[0]?) →
      (∀ j, 1 ≤ j → j < s.core.tmp_len →
        ∃ i, 1 ≤ i ∧ i < s.core.tmp_len ∧ tmp'[j]? = s.core.tmp[i]?) →
      (∀ i, 1 ≤ i → i < s.core.tmp_len →
        ∃ j, 1 ≤ j ∧ j < s.core.tmp_len ∧ s.core.tmp[i]? = tmp'[j]?) →
      (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
        (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (FullMem c { s with core := { s.core with tmp := tmp' } } ⋆ R) m' → Q () m'

def fullMinLitSpec : Spec [i64, i32] [.bool] := fun (h, root_lit, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (keepSet : List Nat)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullCoreInv c F0 s ∧ FullMinMarkInv s.core keepSet ∧
    root_lit.toNat < 2 * s.core.cur_vars ∧ s.core.vals[root_lit.toNat]?.getD 0#8 = 0xFF#8 ∧
    (∀ v < s.core.cur_vars,
      (s.core.lvl[v]?.getD 0#32).toNat ≤
        (s.core.lvl[root_lit.toNat / 2]?.getD 0#32).toNat →
      (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) mrk' mstk' mclr' mcl' mcf' m',
      let s' : FullState := minLitState s mrk' mstk' mclr' mcl' mcf'
      s'.LengthsOk c →
      (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) →
      (∀ v < s.core.cur_vars,
        (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (∀ v < s.core.cur_vars,
        (mrk'[v]?.getD 0#8 &&& 8#8) = (s.core.mrk[v]?.getD 0#8 &&& 8#8)) →
      FullMinMarkInv s'.core keepSet →
      (ok = true →
        (∀ keep' : List Nat,
          (∀ l ∈ keepSet, l = root_lit.toNat ∨ l ∈ keep') → FullMinMarkInv s'.core keep') ∧
        FullMinMarkInv (fullMinMarkCore s'.core (root_lit.toNat / 2) 2#8) keepSet) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullShrinkLowerSpec : Spec [i64, i32, i32] [.bool] := fun (h, ot, ov, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (keepSet : List Nat)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullCoreInv c F0 s ∧ FullMinMarkInv s.core keepSet ∧
    ov.toNat = ot.toNat / 2 ∧ ot.toNat < 2 * s.core.cur_vars ∧
    s.core.vals[ot.toNat]?.getD 0#8 = 0xFF#8 ∧
    (∀ v < s.core.cur_vars,
      (s.core.lvl[v]?.getD 0#32).toNat ≤ (s.core.lvl[ov.toNat]?.getD 0#32).toNat →
      (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) mrk' mstk' mclr' mcl' mcf' m',
      let s' : FullState := minLitState s mrk' mstk' mclr' mcl' mcf'
      s'.LengthsOk c →
      (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) →
      (∀ v < s.core.cur_vars,
        (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (∀ v < s.core.cur_vars,
        (mrk'[v]?.getD 0#8 &&& 8#8) = (s.core.mrk[v]?.getD 0#8 &&& 8#8)) →
      FullMinMarkInv s'.core keepSet →
      (ok = true → (mrk'[ov.toNat]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullShrinkBlkSpec : Spec [i64, i64, i64, i32, i64] [] :=
  fun (h, beg, end_b, blvl, max_tr, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullCoreInv c F0 s ∧
      FullMinMarkInv s.core
        (((s.core.tmp.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) ∧
      (∀ v < s.core.cur_vars, (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) ∧
      1 ≤ beg.toNat ∧ beg.toNat < end_b.toNat ∧
      end_b.toNat ≤ s.core.tmp_len ∧ s.core.tmp_len ≤ s.core.cur_vars ∧
      0 < blvl.toNat ∧ blvl.toNat < s.core.cur_level ∧
      (∀ k, beg.toNat ≤ k → k < end_b.toNat →
        let l := (s.core.tmp[k]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        (s.core.lvl[l / 2]?.getD 0#32).toNat = blvl.toNat ∧
        (s.core.trail_pos[l / 2]?.getD 0#32).toNat ≤ max_tr.toNat) ∧
      (∀ k < s.core.tmp_len, s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
        let l := (s.core.tmp[k]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        (s.core.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ tmp' mrk' mstk' mclr' mcl' mcf' sstk' m',
        let s' : FullState := {
          core := { s.core with tmp := tmp', mrk := mrk', min_stk := mstk', min_clr := mclr',
                                min_clr_len := mcl', min_clr_full := mcf' }
          scratch := { s.scratch with shrink_stk := sstk' } }
        FullCoreInv c F0 s' →
        FullMinMarkInv s'.core
          (((tmp'.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) →
        (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) →
        (∀ v < s.core.cur_vars, (mrk'[v]?.getD 0#8 &&& 8#8) = 0#8) →
        (∀ v < s.core.cur_vars,
          (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
        (∀ k < s.core.tmp_len, (k < beg.toNat ∨ end_b.toNat ≤ k) → tmp'[k]? = s.core.tmp[k]?) →
        (∀ k, beg.toNat ≤ k → k < end_b.toNat → tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
          (s.core.lvl[(tmp'[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat) →
        (∀ F_cur, FullWitnessInv c F0 F_cur s.core →
          (cnfOfClauses F_cur).EntailsClause (cnfClause
            (((s.core.tmp.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)) →
          FullWitnessInv c F0 F_cur s'.core ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause
            (((tmp'.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))) →
        (∀ k < s.core.tmp_len, tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
          let l := (tmp'[k]?.getD 0#32).toNat
          l < 2 * s.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
          (mrk'[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) →
        (FullMem c s' ⋆ R) m' → Q () m'

def fullMinShrinkSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullInv c F0 s ∧ 1 ≤ s.core.tmp_len ∧ s.core.tmp_len ≤ s.core.cur_vars ∧
    (∀ k < s.core.tmp_len, let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
    (∀ k, 1 ≤ k → k < s.core.tmp_len →
      let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ tmp' tl' mrk' mstk' mclr' mcl' mcf' conf' llits' mrem' sstk' m',
      let s' : FullState := {
        core := { s.core with
          tmp := tmp', tmp_len := tl', mrk := mrk', min_stk := mstk', min_clr := mclr',
          min_clr_len := mcl', min_clr_full := mcf' }
        scratch := { s.scratch with
          conflicts := conf', learned_lits := llits', min_removed := mrem',
          shrink_stk := sstk' } }
      FullInv c F0 s' →
      (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) →
      1 ≤ tl' → tl' ≤ s.core.tmp_len → tmp'[0]? = s.core.tmp[0]? →
      (∀ j, 1 ≤ j → j < tl' →
        let l := (tmp'[j]?.getD 0#32).toNat
        let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        0 < lv ∧ lv < s.core.cur_level ∧
        lv ≤ (s.core.lvl[(tmp'[tl' - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (∀ i j, 1 ≤ i → i ≤ j → j < tl' →
        (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (∀ F_cur, FullWitnessInv c F0 F_cur s.core →
        (cnfOfClauses F_cur).EntailsClause (cnfClause
          ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) →
        FullWitnessInv c F0 F_cur s'.core ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat))) →
      (FullMem c s' ⋆ R) m' → Q () m'

end FullMinSpecs

open FullMinSpecs

/-! ## 4. `full_tmp_less_wp` -/

theorem full_tmp_less_wp (Γ : Env) :
    ∀ args m Q X, fullTmpLessSpec args m Q X →
      Func.wp Γ full_tmp_less_body args m Q X := by
  rintro ⟨lvl_ptr, tpos_ptr, a, b, ⟨⟩⟩ m Q X ⟨lvl, tpos, R, ha1, hb1, ha2, hb2, hm, hQ⟩
  unfold Func.wp full_tmp_less_body
  c0_steps!
  all_goals
    have ha32 := a.isLt; have hb32 := b.isLt
    have hia : (a.toNat % 18446744073709551616) >>> 1 = a.toNat / 2 := by
      rw [Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow, Nat.pow_one]
    have hib : (b.toNat % 18446744073709551616) >>> 1 = b.toNat / 2 := by
      rw [Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow, Nat.pow_one]
  · have hne : (lvl[a.toNat / 2]'ha1).toNat ≠ (lvl[b.toNat / 2]'hb1).toNat :=
      fun h => hc (BitVec.eq_of_toNat_eq h)
    simpa [BitVec.ult, hia, hib, List.getElem?_eq_getElem ha1,
      List.getElem?_eq_getElem hb1, hne] using hQ
  · have heq := congrArg BitVec.toNat hc
    simpa [BitVec.ult, hia, hib, List.getElem?_eq_getElem ha1, List.getElem?_eq_getElem hb1,
      List.getElem?_eq_getElem ha2, List.getElem?_eq_getElem hb2, heq] using hQ

/-! ## 5. `full_min_mark_wp` -/

theorem full_min_mark_wp (Γ : Env) :
    ∀ args m Q X, fullMinMarkSpec args m Q X →
      Func.wp Γ full_min_mark_body args m Q X := by
  rintro ⟨h, v, tag, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmrk_len := hlen.core_ok.mrk_len
  have hmclr_len := hlen.core_ok.min_clr_len_arr
  have hmcl_le := hlen.core_ok.min_clr_len_le
  unfold Func.wp full_min_mark_body; dsimp only [full_min_mark_body]
  ml_lets; rw [wp]; refine ⟨_, load_full_cur_vars hm, ?_⟩; ml_lets
  ml_jnz; refine ⟨fun hoob_bv => ?_, fun hlt_bv => ?_⟩
  · c0_cond hoob_bv
    have hoob : s.core.cur_vars ≤ v.toNat := by bv_omega
    ml_lets; rw [wp]
    simpa only [hoob, true_or, ↓reduceIte] using hQ
  · have hvlt : v.toNat < s.core.cur_vars := by c0_cond hlt_bv; bv_omega
    have hnot_oob : ¬ s.core.cur_vars ≤ v.toNat := by omega
    have hv_mrk : v.toNat < s.core.mrk.length := by omega
    ml_lets; rw [wp]; refine ⟨_, load_full_mark_ptr hm, ?_⟩; ml_lets
    rw [wp]; refine ⟨_, c0_load_full_mrk (i := v.setWidth 64) (by bv_omega) hm, ?_⟩
    c0_steps!
    · have hne : (s.core.mrk[v.toNat]?.getD 0#8 &&& tag) ≠ 0#8 := by
        rw [List.getElem?_eq_getElem hv_mrk, Option.getD_some]; exact hc
      simpa [hnot_oob, hne] using hQ
    · have hcl_lt : s.core.min_clr_len < s.core.cur_vars := by bv_omega
      have hadd1 : (BitVec.ofNat 64 s.core.min_clr_len + 1).toNat = s.core.min_clr_len + 1 := by
        rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [bv_c0_zext32_64, bv8_or_zext32_trunc8, hadd1, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : s.core.min_clr_len < 2 ^ 64)] at hm
      dsimp only at hQ
      rw [List.getElem?_eq_getElem hv_mrk, Option.getD_some] at hQ
      have hcur0 : s.core.mrk[v.toNat] = 0#8 := by assumption
      simp only [hnot_oob, hcur0, BitVec.zero_and, ne_eq, not_true_eq_false, or_self,
        ↓reduceIte, hcl_lt] at hQ
      rw [hcur0] at hm; exact hQ _ hm
    · have hcl_ge : ¬ s.core.min_clr_len < s.core.cur_vars := by bv_omega
      simp only [bv_c0_zext32_64, bv8_or_zext32_trunc8] at hm
      dsimp only at hQ
      rw [List.getElem?_eq_getElem hv_mrk, Option.getD_some] at hQ
      have hcur0 : s.core.mrk[v.toNat] = 0#8 := by assumption
      simp only [hnot_oob, hcur0, BitVec.zero_and, ne_eq, not_true_eq_false, or_self,
        ↓reduceIte, hcl_ge] at hQ
      rw [hcur0] at hm; exact hQ _ hm
    · simp only [bv_c0_zext32_64, bv8_or_zext32_trunc8] at hm
      dsimp only at hQ
      rw [List.getElem?_eq_getElem hv_mrk, Option.getD_some] at hQ
      have htag0 : s.core.mrk[v.toNat] &&& tag = 0#8 := by assumption
      have hcur_nz : s.core.mrk[v.toNat] ≠ 0#8 := by assumption
      simp only [hnot_oob, htag0, ne_eq, not_true_eq_false, or_self, ↓reduceIte,
        hcur_nz] at hQ
      exact hQ _ hm

/-! ## 6. Block-shrink trail bit-8 counter (`trailCount8`) -/

def trailCount8 (trl : List (BitVec 32)) (mrk : List (BitVec 8)) : Nat → Nat
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
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 : (mrk[(trl[n]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) = 0#8 :=
      h0 _ (hlt n (by omega))
    simp [trailCount8, h1, h2]

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
    simp only [trailCount8, ih (fun j hj => hlt j (by omega)), heq _ (hlt n (Nat.lt_succ_self n))]

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
    trailCount8 trl mrk (n + 1) = trailCount8 trl mrk n := by
  simp [trailCount8, h]

theorem trailCount8_step_nz {trl : List (BitVec 32)} {mrk : List (BitVec 8)} {n : Nat}
    (h : (mrk[(trl[n]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8) :
    trailCount8 trl mrk (n + 1) = trailCount8 trl mrk n + 1 := by
  simp [trailCount8, h]

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

end LeanQbe.T.Examples.Kissat.Full
