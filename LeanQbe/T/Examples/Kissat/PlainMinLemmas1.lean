module

public import LeanQbe.T.Examples.Kissat.PlainSpec
import all Kraken.Mem
import all Kraken.Separation

/-!
# Soundness Proofs for Kissat `D-Plain` Minimization Helpers (`Wave 2b Shard 5`, Part 1)

Proves parametric `(Γ : Env)` `Func.wp` specifications matching `PlainSpec.lean:1002-1006`:
1. `plain_clear_marks` (`plainClearMarksSpec`, `plain_clear_marks_wp`)
2. `plain_min_mark` (`plainMinMarkSpec`, `plain_min_mark_wp`)
3. `plain_tmp_less` (`plainTmpLessSpec`, `plain_tmp_less_wp`)
4. `plain_sort_tmp` (`plainSortTmpSpec`, `plain_sort_tmp_wp`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Plain

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Scoped tactic helpers and arithmetic lemmas -/

theorem bv8_eq_zero_of_masks (x : BitVec 8) (hdom : (x &&& 0xF1#8) = 0#8)
    (h8 : (x &&& 8#8) = 0#8) (h6 : (x &&& 6#8) = 0#8) : x = 0#8 := by
  revert x hdom h8 h6; decide

theorem bv8_zero_of_masks24 (x : BitVec 8) (hdom : (x &&& 0xF1#8) = 0#8)
    (h8 : (x &&& 8#8) = 0#8) (h2 : (x &&& 2#8) = 0#8) (h4 : (x &&& 4#8) = 0#8) :
    x = 0#8 := by
  revert x hdom h8 h2 h4; decide

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

namespace PlainMinTactics

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
  | `(tactic| ml_jnz) => `(tactic| rw [PlainMinTactics.ml_jnz])

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

end PlainMinTactics

open scoped PlainMinTactics

theorem bv64_shl1_toNat {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 64) :
    (x <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat = 2 * x.toNat :=
  PlainMinTactics.bv_c0_shl1_toNat hx

theorem bv64_shl1_add1_toNat {x : BitVec 64} (hx : 2 * x.toNat + 1 < 2 ^ 64) :
    (x <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1).toNat = 2 * x.toNat + 1 :=
  PlainMinTactics.bv_c0_shl1_add1_toNat hx

theorem bv64_shl1_toNat_raw {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 64) :
    (x <<< ((1 : BitVec 64).toNat % 64)).toNat = 2 * x.toNat := by
  have hm : (1 : BitVec 64).toNat % 64 = 1 := rfl
  rw [hm, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]; omega

theorem bv64_shl1_add1_toNat_raw {x : BitVec 64} (hx : 2 * x.toNat + 1 < 2 ^ 64) :
    (x <<< ((1 : BitVec 64).toNat % 64) + 1).toNat = 2 * x.toNat + 1 := by
  have hsh := bv64_shl1_toNat_raw (x := x) (by omega)
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_add, hsh, h1, Nat.mod_eq_of_lt hx]

theorem coreInv_with_min {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {mrk1 : List (BitVec 8)} {mstk1 mclr1 : List (BitVec 32)}
    {mcl1 : Nat} {mcf1 : BitVec 64}
    (hmrk : mrk1.length = c.mv) (hmstk : mstk1.length = 2 * c.minDepth)
    (hmclr : mclr1.length = c.mv) (hmcl : mcl1 ≤ c.mv) :
    PlainCoreInv c F0 { s with
      mrk := mrk1, min_stk := mstk1, min_clr := mclr1,
      min_clr_len := mcl1, min_clr_full := mcf1 } :=
  { hcore with
    lengths := { hcore.lengths with
      mrk_len := hmrk, min_stk_len := hmstk,
      min_clr_len_arr := hmclr, min_clr_len_le := hmcl }
    arena := { hcore.arena with len_ok := hcore.arena.len_ok }
    watches := hcore.watches.with_wstk rfl rfl rfl rfl }

abbrev minLitState (s : PlainState) (mrk1 : List (BitVec 8))
    (mstk1 mclr1 : List (BitVec 32)) (mcl1 : Nat) (mcf1 : BitVec 64) : PlainState :=
  { s with
    mrk := mrk1, min_stk := mstk1, min_clr := mclr1,
    min_clr_len := mcl1, min_clr_full := mcf1 }

theorem minMarkInv_with_mstk {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {keep : List Nat} (h : PlainMinMarkInv c F0 s keep) (mstk' : List (BitVec 32)) :
    PlainMinMarkInv c F0 { s with min_stk := mstk' } keep :=
  ⟨h.mrk_dom, h.clr_cov, h.rem_sound⟩

private theorem mrk_set_zero_pres {c : PlainCfg} {s : PlainState} {mrk1 : List (BitVec 8)}
    (hml : mrk1.length = c.mv)
    (hpres : ∀ w < c.mv, s.mrk[w]?.getD 0#8 = 0#8 → mrk1[w]?.getD 0#8 = 0#8)
    {v : Nat} (hv : v < c.mv) :
    ∀ w < c.mv, s.mrk[w]?.getD 0#8 = 0#8 → (mrk1.set v 0#8)[w]?.getD 0#8 = 0#8 := by
  intro w hw hz
  by_cases hwe : w = v
  · subst hwe; rw [List.getElem?_set_self (by omega)]; rfl
  · rw [List.getElem?_set_ne (Ne.symm hwe)]; exact hpres w hw hz

private theorem mrk_set_zero_cov {xs : List (BitVec 32)} {mrk1 : List (BitVec 8)}
    {mv lim lo i : Nat}
    (hml : mrk1.length = mv)
    (hcov : ∀ k, lo ≤ k → k < i → k < lim → (xs[k]?.getD 0#32).toNat / 2 < mv →
      mrk1[(xs[k]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8)
    (hi_xs : i < xs.length) (hv : (xs[i]'hi_xs).toNat / 2 < mv) :
    ∀ k, lo ≤ k → k < i + 1 → k < lim → (xs[k]?.getD 0#32).toNat / 2 < mv →
      (mrk1.set ((xs[i]'hi_xs).toNat / 2) 0#8)[(xs[k]?.getD 0#32).toNat / 2]?.getD 0#8 =
        0#8 := by
  intro k hklo hki hkl hkv
  let v := (xs[i]'hi_xs).toNat / 2
  by_cases hve : (xs[k]?.getD 0#32).toNat / 2 = v
  · rw [hve, List.getElem?_set_self (by omega)]; rfl
  · rw [List.getElem?_set_ne (Ne.symm hve)]
    have hne : k ≠ i := fun h => hve (by
      subst h; rw [List.getElem?_eq_getElem hi_xs, Option.getD_some])
    exact hcov k hklo (by omega) hkl hkv

private theorem mrk_unchanged_cov {xs : List (BitVec 32)} {mrk1 : List (BitVec 8)}
    {mv lim lo i : Nat}
    (hcov : ∀ k, lo ≤ k → k < i → k < lim → (xs[k]?.getD 0#32).toNat / 2 < mv →
      mrk1[(xs[k]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8)
    (hi_xs : i < xs.length) (hge : mv ≤ (xs[i]'hi_xs).toNat / 2) :
    ∀ k, lo ≤ k → k < i + 1 → k < lim → (xs[k]?.getD 0#32).toNat / 2 < mv →
      mrk1[(xs[k]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8 := by
  intro k hklo hki hkl hkv
  by_cases hke : k = i
  · subst hke; rw [List.getElem?_eq_getElem hi_xs, Option.getD_some] at hkv; omega
  · exact hcov k hklo (by omega) hkl hkv

/-! ## 2. `plain_tmp_less_wp` -/

theorem plain_tmp_less_wp (Γ : Env) :
    ∀ args m Q X, plainTmpLessSpec args m Q X →
      Func.wp Γ plain_tmp_less_body args m Q X := by
  rintro ⟨lvl_ptr, tpos_ptr, a, b, ⟨⟩⟩ m Q X ⟨lvl, tpos, R, ha1, hb1, ha2, hb2, hm, hQ⟩
  unfold Func.wp plain_tmp_less_body
  c0_steps!
  all_goals
    have ha32 := a.isLt; have hb32 := b.isLt
    have hia : (a.toNat % 18446744073709551616) >>> 1 = a.toNat / 2 := by
      rw [Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow, Nat.pow_one]
    have hib : (b.toNat % 18446744073709551616) >>> 1 = b.toNat / 2 := by
      rw [Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow, Nat.pow_one]
    have hma : a.toNat / 2 % 2 ^ 64 = a.toNat / 2 := Nat.mod_eq_of_lt (by omega)
    have hmb : b.toNat / 2 % 2 ^ 64 = b.toNat / 2 := Nat.mod_eq_of_lt (by omega)
  · have hc' : lvl[a.toNat / 2]'ha1 ≠ lvl[b.toNat / 2]'hb1 := by
      intro h; apply hc
      have h0 : lvl[a.toNat / 2 % 2 ^ 64]? = lvl[b.toNat / 2 % 2 ^ 64]? := by
        rw [hma, hmb, List.getElem?_eq_getElem ha1, List.getElem?_eq_getElem hb1, h]
      rw [List.getElem?_eq_getElem (by rw [hma]; exact ha1),
        List.getElem?_eq_getElem (by rw [hmb]; exact hb1), Option.some_inj] at h0
      exact h0
    have hne : (lvl[a.toNat / 2]'ha1).toNat ≠ (lvl[b.toNat / 2]'hb1).toNat :=
      fun h => hc' (BitVec.eq_of_toNat_eq h)
    simpa [BitVec.ult, hia, hib, List.getElem?_eq_getElem ha1,
      List.getElem?_eq_getElem hb1, hne] using hQ
  · have hc' : lvl[a.toNat / 2]'ha1 = lvl[b.toNat / 2]'hb1 := by
      have h0 : lvl[a.toNat / 2 % 2 ^ 64]? = lvl[b.toNat / 2 % 2 ^ 64]? := by
        rw [List.getElem?_eq_getElem (by rw [hma]; exact ha1),
          List.getElem?_eq_getElem (by rw [hmb]; exact hb1), hc]
      simp only [hma, hmb] at h0
      rw [List.getElem?_eq_getElem ha1, List.getElem?_eq_getElem hb1, Option.some_inj] at h0
      exact h0
    have heq := congrArg BitVec.toNat hc'
    simpa [BitVec.ult, hia, hib, List.getElem?_eq_getElem ha1, List.getElem?_eq_getElem hb1,
      List.getElem?_eq_getElem ha2, List.getElem?_eq_getElem hb2, heq] using hQ

/-! ## 3. `plain_clear_marks_wp` -/

theorem plain_clear_marks_wp (Γ : Env) :
    ∀ args m Q X, plainClearMarksSpec args m Q X →
      Func.wp Γ plain_clear_marks_body args m Q X := by
  rintro ⟨h, trail_from, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, htl_mv, hm, hQ⟩
  c0_steps!
  have hmv := c.hmv; unfold dimacsBound at hmv
  have htmp_len := hlen.tmp_len_arr
  have htrl_len := hlen.trl_len
  have hte_le := hlen.trail_end_le
  refine wp_loop_group (ts := [i64])
    (fun r (iv, ()) ml => ∃ i mrk1,
      1 ≤ i ∧ i ≤ max 1 s.tmp_len ∧ r = max 1 s.tmp_len - i ∧ iv = BitVec.ofNat 64 i ∧
      mrk1.length = c.mv ∧
      (∀ v < c.mv, s.mrk[v]?.getD 0#8 = 0#8 → mrk1[v]?.getD 0#8 = 0#8) ∧
      (∀ k, 1 ≤ k → k < i → k < s.tmp_len → (s.tmp[k]?.getD 0#32).toNat / 2 < c.mv →
        mrk1[(s.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8) ∧
      (PlainMem c { s with mrk := mrk1 } ⋆ R) ml) ?_ ?_
  · rintro L r ⟨iv, ⟨⟩⟩ ml ih ⟨i, mrk1, hi1, hile, rfl, rfl, hml1, hpres1, hclr1, hmem1⟩
    c0_steps!
    · have hilt : i < s.tmp_len := by bv_omega
      have hi_tmp : i < s.tmp.length := by omega
      have hadd1 : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
        rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]
      have hi64 : i < 2 ^ 64 := by omega
      have hv_lt : (s.tmp[i]'hi_tmp).toNat / 2 < c.mv := by
        simp only [Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt (by omega : c.mv < 2 ^ 64)] at hc
        bv_omega
      simp only [bv_c0_zext32_64, bv32_lshr_1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64] at hm
      refine ih (max 1 s.tmp_len - (i + 1)) _ _ (by omega) ⟨i + 1, mrk1.set _ 0#8,
        by omega, by omega, rfl, hadd1, by simp [hml1],
        mrk_set_zero_pres hml1 hpres1 hv_lt,
        mrk_set_zero_cov hml1 hclr1 hi_tmp hv_lt, by c0_frame⟩
    · have hilt : i < s.tmp_len := by bv_omega
      have hi_tmp : i < s.tmp.length := by omega
      have hadd1 : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
        rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]
      have hi64 : i < 2 ^ 64 := by omega
      have hv_ge : c.mv ≤ (s.tmp[i]'hi_tmp).toNat / 2 := by
        simp only [Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt (by omega : c.mv < 2 ^ 64)] at hc
        bv_omega
      refine ih (max 1 s.tmp_len - (i + 1)) _ _ (by omega) ⟨i + 1, mrk1,
        by omega, by omega, rfl, hadd1, hml1, hpres1,
        mrk_unchanged_cov hclr1 hi_tmp hv_ge, hmem1⟩
    · have hclr_all : ∀ k, 1 ≤ k → k < s.tmp_len → (s.tmp[k]?.getD 0#32).toNat / 2 < c.mv →
          mrk1[(s.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8 :=
        fun k hk1 hkt hkv => hclr1 k hk1 (by bv_omega) hkt hkv
      refine wp_loop_group (ts := [i64])
        (fun r2 (jv, ()) m2 => ∃ j mrk2,
          trail_from.toNat ≤ j ∧ j ≤ max trail_from.toNat s.trail_end ∧
          r2 = max trail_from.toNat s.trail_end - j ∧ jv = BitVec.ofNat 64 j ∧
          mrk2.length = c.mv ∧
          (∀ v < c.mv, s.mrk[v]?.getD 0#8 = 0#8 → mrk2[v]?.getD 0#8 = 0#8) ∧
          (∀ k, 1 ≤ k → k < s.tmp_len → (s.tmp[k]?.getD 0#32).toNat / 2 < c.mv →
            mrk2[(s.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8) ∧
          (∀ k, trail_from.toNat ≤ k → k < j → k < s.trail_end →
            (s.trl[k]?.getD 0#32).toNat / 2 < c.mv →
            mrk2[(s.trl[k]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8) ∧
          (PlainMem c { s with mrk := mrk2 } ⋆ R) m2) ?_ ?_
      · rintro L2 r2 ⟨jv, ⟨⟩⟩ m2 ih2
          ⟨j, mrk2, hjlo, hjhi, rfl, rfl, hml2, hpres2, hclrt2, hclrr2, hmem2⟩
        c0_steps!
        · have hjlt : j < s.trail_end := by bv_omega
          have hj_trl : j < s.trl.length := by omega
          have hadd1 : BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j + 1) := by
            rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]
          have hj64 : j < 2 ^ 64 := by omega
          have htv_lt : (s.trl[j]'hj_trl).toNat / 2 < c.mv := by
            simp only [Nat.mod_eq_of_lt hj64, Nat.mod_eq_of_lt (by omega : c.mv < 2 ^ 64)] at hc
            bv_omega
          simp only [bv_c0_zext32_64, bv32_lshr_1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj64] at hm
          refine ih2 (max trail_from.toNat s.trail_end - (j + 1)) _ _ (by omega)
            ⟨j + 1, mrk2.set _ 0#8, by omega, by omega, rfl, hadd1, by simp [hml2],
              mrk_set_zero_pres hml2 hpres2 htv_lt, ?_,
              mrk_set_zero_cov hml2 hclrr2 hj_trl htv_lt, by c0_frame⟩
          intro k hk1 hkt hkv
          by_cases hve : (s.tmp[k]?.getD 0#32).toNat / 2 = (s.trl[j]'hj_trl).toNat / 2
          · rw [hve, List.getElem?_set_self (by omega)]; rfl
          · rw [List.getElem?_set_ne (Ne.symm hve)]; exact hclrt2 k hk1 hkt hkv
        · have hjlt : j < s.trail_end := by bv_omega
          have hj_trl : j < s.trl.length := by omega
          have hadd1 : BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j + 1) := by
            rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]
          have hj64 : j < 2 ^ 64 := by omega
          have htv_ge : c.mv ≤ (s.trl[j]'hj_trl).toNat / 2 := by
            simp only [Nat.mod_eq_of_lt hj64, Nat.mod_eq_of_lt (by omega : c.mv < 2 ^ 64)] at hc
            bv_omega
          refine ih2 (max trail_from.toNat s.trail_end - (j + 1)) _ _ (by omega)
            ⟨j + 1, mrk2, by omega, by omega, rfl, hadd1, hml2, hpres2, hclrt2,
              mrk_unchanged_cov hclrr2 hj_trl htv_ge, hmem2⟩
        · exact hQ mrk2 m2 hml2 hpres2 hclrt2
            (fun k hklo hkt hkv => hclrr2 k hklo (by bv_omega) hkt hkv) hmem2
      · intro L2 hL2
        wp_unfold
        exact hL2 (max trail_from.toNat s.trail_end - trail_from.toNat) _ _
          ⟨trail_from.toNat, mrk1, Nat.le_refl _, Nat.le_max_left _ _, rfl,
            (bv_ofNat_toNat_eq trail_from).symm, hml1, hpres1, hclr_all,
            fun _ h1 h2 => by omega, hmem1⟩
  · intro L hL
    wp_unfold
    exact hL (max 1 s.tmp_len - 1) _ m
      ⟨1, s.mrk, Nat.le_refl _, Nat.le_max_left _ _, rfl, rfl, hlen.mrk_len,
        fun _ _ h => h, fun _ h1 h2 => by omega, hm⟩

/-! ## 4. `plain_min_mark_wp` -/

theorem plain_min_mark_wp (Γ : Env) :
    ∀ args m Q X, plainMinMarkSpec args m Q X →
      Func.wp Γ plain_min_mark_body args m Q X := by
  rintro ⟨h, v, tag, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  c0_steps
  · have hmv : c.mv < 2 ^ 28 := c.hmv
    have hoob : c.mv ≤ v.toNat := by bv_omega
    simpa only [hoob, true_or, ↓reduceIte] using hQ
  · rw [wp]
    refine ⟨_, c0_load_arena_mrk (i := v.setWidth 64) ?_ hm, ?_⟩
    · have hmv : c.mv < 2 ^ 28 := c.hmv
      have hmrk_len := hlen.mrk_len
      bv_omega
    · refine (fun (hmv : c.mv < 2 ^ 28) (hmrk_len : s.mrk.length = c.mv)
          (hmclr_len : s.min_clr.length = c.mv) (hmcl_le : s.min_clr_len ≤ c.mv) => ?_)
        c.hmv hlen.mrk_len hlen.min_clr_len_arr hlen.min_clr_len_le
      c0_steps!
      · have hnot_oob : ¬ c.mv ≤ v.toNat := by bv_omega
        have hvlt : v.toNat < c.mv := by bv_omega
        have hv_mrk : v.toNat < s.mrk.length := by rw [hmrk_len]; exact hvlt
        simp only [Nat.mod_eq_of_lt (by omega : v.toNat < 2 ^ 64)] at hc
        have hne : (s.mrk[v.toNat]?.getD 0#8 &&& tag) ≠ 0#8 := by
          rw [List.getElem?_eq_getElem hv_mrk, Option.getD_some]; exact hc
        simpa [hnot_oob, hne] using hQ
      · have hnot_oob : ¬ c.mv ≤ v.toNat := by bv_omega
        have hvlt : v.toNat < c.mv := by bv_omega
        have hv_mrk : v.toNat < s.mrk.length := by rw [hmrk_len]; exact hvlt
        simp only [Nat.mod_eq_of_lt (by omega : v.toNat < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : s.min_clr_len < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : c.mv < 2 ^ 64)] at *
        have hcl_lt : s.min_clr_len < c.mv := by bv_omega
        have hm' := ‹(PlainMem c _ ⋆ R) _›
        have hadd1 : (BitVec.ofNat 64 s.min_clr_len + 1).toNat = s.min_clr_len + 1 := by
          rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat,
            BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        simp only [bv_c0_zext32_64, bv8_or_zext32_trunc8, hadd1, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : s.min_clr_len < 2 ^ 64)] at hm'
        rw [List.getElem?_eq_getElem hv_mrk, Option.getD_some] at hQ
        split at hQ
        · rcases ‹c.mv ≤ _ ∨ _› with h | h
          · exact absurd h hnot_oob
          · exact absurd ‹s.mrk[v.toNat] &&& tag = 0#8› h
        · split at hQ
          · exact absurd ‹s.mrk[v.toNat] = 0#8› ‹s.mrk[v.toNat] ≠ 0#8›
          · exact hQ _ hm'
      · have hnot_oob : ¬ c.mv ≤ v.toNat := by bv_omega
        have hvlt : v.toNat < c.mv := by bv_omega
        have hv_mrk : v.toNat < s.mrk.length := by rw [hmrk_len]; exact hvlt
        simp only [Nat.mod_eq_of_lt (by omega : v.toNat < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : s.min_clr_len < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : c.mv < 2 ^ 64)] at *
        have hcl_ge : ¬ s.min_clr_len < c.mv := by bv_omega
        have hm' := ‹(PlainMem c _ ⋆ R) _›
        simp only [bv_c0_zext32_64, bv8_or_zext32_trunc8] at hm'
        rw [List.getElem?_eq_getElem hv_mrk, Option.getD_some] at hQ
        split at hQ
        · rcases ‹c.mv ≤ _ ∨ _› with h | h
          · exact absurd h hnot_oob
          · exact absurd ‹s.mrk[v.toNat] &&& tag = 0#8› h
        · split at hQ
          · exact absurd ‹s.mrk[v.toNat] = 0#8› ‹s.mrk[v.toNat] ≠ 0#8›
          · exact hQ _ hm'
      · have hnot_oob : ¬ c.mv ≤ v.toNat := by bv_omega
        have hvlt : v.toNat < c.mv := by bv_omega
        have hv_mrk : v.toNat < s.mrk.length := by rw [hmrk_len]; exact hvlt
        simp only [Nat.mod_eq_of_lt (by omega : v.toNat < 2 ^ 64)] at *
        have hm' := ‹(PlainMem c _ ⋆ R) _›
        simp only [bv_c0_zext32_64, bv8_or_zext32_trunc8] at hm'
        rw [List.getElem?_eq_getElem hv_mrk, Option.getD_some] at hQ
        split at hQ
        · rcases ‹c.mv ≤ _ ∨ _› with h | h
          · exact absurd h hnot_oob
          · exact absurd ‹s.mrk[v.toNat] &&& tag = 0#8› h
        · exact hQ _ hm'

/-! ## 5. `plain_sort_tmp_wp` -/

private def tmpKey (lvl tpos : List (BitVec 32)) (x : BitVec 32) : Nat × Nat :=
  let v := x.toNat / 2
  ((lvl[v]?.getD 0#32).toNat, (tpos[v]?.getD 0#32).toNat)

private def tmpLt (lvl tpos : List (BitVec 32)) (a b : BitVec 32) : Prop :=
  (tmpKey lvl tpos a).1 < (tmpKey lvl tpos b).1 ∨
  ((tmpKey lvl tpos a).1 = (tmpKey lvl tpos b).1 ∧
   (tmpKey lvl tpos a).2 < (tmpKey lvl tpos b).2)

private def tmpLe (lvl tpos : List (BitVec 32)) (a b : BitVec 32) : Prop :=
  ¬ tmpLt lvl tpos b a

private theorem tmpLe_refl (lvl tpos : List (BitVec 32)) (a : BitVec 32) :
    tmpLe lvl tpos a a := by
  simp only [tmpLe, tmpLt]; omega

private theorem tmpLt_mono_le {lvl tpos : List (BitVec 32)} {a b : BitVec 32}
    (h : tmpLt lvl tpos a b) : tmpLe lvl tpos a b := by
  simp only [tmpLe, tmpLt] at h ⊢; omega

private theorem tmpLe_trans {lvl tpos : List (BitVec 32)} {a b c : BitVec 32}
    (h1 : tmpLe lvl tpos a b) (h2 : tmpLe lvl tpos b c) : tmpLe lvl tpos a c := by
  simp only [tmpLe, tmpLt] at h1 h2 ⊢; omega

private theorem tmpLe_of_decide_false {lvl tpos : List (BitVec 32)} {a b : BitVec 32}
    (h : decide ((tmpKey lvl tpos a).1 < (tmpKey lvl tpos b).1 ∨
      ((tmpKey lvl tpos a).1 = (tmpKey lvl tpos b).1 ∧
       (tmpKey lvl tpos a).2 < (tmpKey lvl tpos b).2)) = false) :
    tmpLe lvl tpos b a := by
  simp only [decide_eq_false_iff_not] at h; exact h

private theorem tmpLt_of_decide_true {lvl tpos : List (BitVec 32)} {a b : BitVec 32}
    (h : decide ((tmpKey lvl tpos a).1 < (tmpKey lvl tpos b).1 ∨
      ((tmpKey lvl tpos a).1 = (tmpKey lvl tpos b).1 ∧
       (tmpKey lvl tpos a).2 < (tmpKey lvl tpos b).2)) = true) :
    tmpLt lvl tpos a b := by
  simp only [decide_eq_true_eq] at h; exact h

private theorem tmpLe_lvl {lvl tpos : List (BitVec 32)} {a b : BitVec 32}
    (h : tmpLe lvl tpos a b) :
    (lvl[a.toNat / 2]?.getD 0#32).toNat ≤ (lvl[b.toNat / 2]?.getD 0#32).toNat := by
  simp only [tmpLe, tmpLt, tmpKey] at h; omega

private def SortSliceEq (a b : List (BitVec 32)) (hi : Nat) : Prop :=
  (∀ j, 1 ≤ j → j < hi → ∃ i, 1 ≤ i ∧ i < hi ∧ a[j]? = b[i]?) ∧
  (∀ i, 1 ≤ i → i < hi → ∃ j, 1 ≤ j ∧ j < hi ∧ b[i]? = a[j]?)

private theorem sortSliceEq_refl (a : List (BitVec 32)) (hi : Nat) : SortSliceEq a a hi :=
  ⟨fun j h1 h2 => ⟨j, h1, h2, rfl⟩, fun i h1 h2 => ⟨i, h1, h2, rfl⟩⟩

private theorem sortSliceEq_trans {a b c : List (BitVec 32)} {hi : Nat}
    (h1 : SortSliceEq a b hi) (h2 : SortSliceEq b c hi) : SortSliceEq a c hi := by
  refine ⟨fun j hj1 hj2 => ?_, fun i hi1 hi2 => ?_⟩
  · obtain ⟨k, hk1, hk2, hjk⟩ := h1.1 j hj1 hj2
    obtain ⟨i, hi1, hi2, hki⟩ := h2.1 k hk1 hk2
    exact ⟨i, hi1, hi2, hjk.trans hki⟩
  · obtain ⟨k, hk1, hk2, hik⟩ := h2.2 i hi1 hi2
    obtain ⟨j, hj1, hj2, hkj⟩ := h1.2 k hk1 hk2
    exact ⟨j, hj1, hj2, hik.trans hkj⟩

private def sortSwap (xs : List (BitVec 32)) (u v : Nat)
    (hu : u < xs.length) (hv : v < xs.length) : List (BitVec 32) :=
  (xs.set u xs[v]).set v xs[u]

private theorem sortSwap_length {xs : List (BitVec 32)} {u v : Nat}
    {hu : u < xs.length} {hv : v < xs.length} :
    (sortSwap xs u v hu hv).length = xs.length := by
  simp [sortSwap]

private theorem sortSwap_getElem? {xs : List (BitVec 32)} {u v k : Nat}
    {hu : u < xs.length} {hv : v < xs.length} :
    (sortSwap xs u v hu hv)[k]? =
      if k = v then some xs[u] else if k = u then some xs[v] else xs[k]? := by
  dsimp only [sortSwap]
  by_cases hkv : k = v
  · subst hkv; simp [hv]
  · simp only [hkv, ↓reduceIte, List.getElem?_set_ne (Ne.symm hkv)]
    by_cases hku : k = u
    · subst hku; simp [hu]
    · simp [hku, List.getElem?_set_ne (Ne.symm hku)]

private theorem sortSwap_sliceEq {xs : List (BitVec 32)} {hi u v : Nat}
    {hu : u < xs.length} {hv : v < xs.length}
    (hu1 : 1 ≤ u) (hu2 : u < hi) (hv1 : 1 ≤ v) (hv2 : v < hi) :
    SortSliceEq (sortSwap xs u v hu hv) xs hi := by
  refine ⟨fun j hj1 hj2 => ?_, fun i hi1 hi2 => ?_⟩
  · rw [sortSwap_getElem?]
    by_cases h1 : j = v
    · subst h1; exact ⟨u, hu1, hu2, by simp [List.getElem?_eq_getElem hu]⟩
    · by_cases h2 : j = u
      · subst h2; exact ⟨v, hv1, hv2, by simp [h1, List.getElem?_eq_getElem hv]⟩
      · exact ⟨j, hj1, hj2, by simp [h1, h2]⟩
  · by_cases h1 : i = u
    · subst h1
      refine ⟨v, hv1, hv2, ?_⟩
      rw [sortSwap_getElem?, List.getElem?_eq_getElem hu]; simp
    · by_cases h2 : i = v
      · subst h2
        refine ⟨u, hu1, hu2, ?_⟩
        rw [sortSwap_getElem?, List.getElem?_eq_getElem hv]; simp [Ne.symm h1]
      · refine ⟨i, hi1, hi2, ?_⟩
        rw [sortSwap_getElem?]; simp [h1, h2]

private def IsHeapAt (lvl tpos tmp : List (BitVec 32)) (i lim : Nat) : Prop :=
  (2 * i + 1 < lim →
    tmpLe lvl tpos (tmp[1 + (2 * i + 1)]?.getD 0#32) (tmp[1 + i]?.getD 0#32)) ∧
  (2 * i + 2 < lim →
    tmpLe lvl tpos (tmp[1 + (2 * i + 2)]?.getD 0#32) (tmp[1 + i]?.getD 0#32))

private def IsMaxHeapFrom (lvl tpos tmp : List (BitVec 32)) (lo lim : Nat) : Prop :=
  ∀ i, lo ≤ i → i < lim → IsHeapAt lvl tpos tmp i lim

private theorem heap_root_max {lvl tpos tmp : List (BitVec 32)} {lim : Nat}
    (hh : IsMaxHeapFrom lvl tpos tmp 0 lim) :
    ∀ k, k < lim → tmpLe lvl tpos (tmp[1 + k]?.getD 0#32) (tmp[1]?.getD 0#32) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk
    rcases k with _ | k'
    · simpa using tmpLe_refl lvl tpos (tmp[1]?.getD 0#32)
    · let p := k' / 2
      have hpr := ih p (by omega) (by omega)
      have hnode := hh p (Nat.zero_le _) (by omega)
      have hchild : tmpLe lvl tpos (tmp[1 + (k' + 1)]?.getD 0#32) (tmp[1 + p]?.getD 0#32) := by
        rcases Nat.mod_two_eq_zero_or_one k' with hm | hm
        · have heq : k' + 1 = 2 * p + 1 := by omega
          simpa [heq] using hnode.1 (by omega)
        · have heq : k' + 1 = 2 * p + 2 := by omega
          simpa [heq] using hnode.2 (by omega)
      exact tmpLe_trans hchild hpr

private def SiftInv (c : PlainCfg) (s : PlainState) (tmp0 tmp_init tmp : List (BitVec 32))
    (lo0 r0 lim r : Nat) : Prop :=
  tmp.length = c.mv ∧
  (0 < s.tmp_len → tmp[0]? = tmp0[0]?) ∧
  SortSliceEq tmp tmp0 s.tmp_len ∧
  (∀ k, 1 ≤ k → k < s.tmp_len → (tmp[k]?.getD 0#32).toNat < 2 * c.mv) ∧
  (∀ k, 1 ≤ k → k < 1 + lim → ∃ j, 1 ≤ j ∧ j < 1 + lim ∧ tmp[k]? = tmp_init[j]?) ∧
  (∀ k, 1 + lim ≤ k → k < s.tmp_len → tmp[k]? = tmp_init[k]?) ∧
  r < lim ∧ lo0 ≤ r ∧ r0 ≤ r ∧
  (∀ i, lo0 ≤ i → i < lim → i ≠ r → IsHeapAt s.lvl s.trail_pos tmp i lim) ∧
  (r0 < r → 0 < r ∧
    (2 * r + 1 < lim →
      tmpLe s.lvl s.trail_pos (tmp[1 + (2 * r + 1)]?.getD 0#32)
        (tmp[1 + (r - 1) / 2]?.getD 0#32)) ∧
    (2 * r + 2 < lim →
      tmpLe s.lvl s.trail_pos (tmp[1 + (2 * r + 2)]?.getD 0#32)
        (tmp[1 + (r - 1) / 2]?.getD 0#32)))

private theorem siftInv_done_of_oob {c : PlainCfg} {s : PlainState}
    {tmp0 tmp_init tmp : List (BitVec 32)} {lo0 r0 lim r : Nat}
    (hi : SiftInv c s tmp0 tmp_init tmp lo0 r0 lim r) (hoob : lim ≤ 2 * r + 1) :
    IsMaxHeapFrom s.lvl s.trail_pos tmp lo0 lim := by
  intro i hi1 hi2
  by_cases hir : i = r
  · subst i; exact ⟨fun h => by omega, fun h => by omega⟩
  · exact hi.2.2.2.2.2.2.2.2.2.1 i hi1 hi2 hir

private theorem siftInv_done_of_ge {c : PlainCfg} {s : PlainState}
    {tmp0 tmp_init tmp : List (BitVec 32)} {lo0 r0 lim r ch : Nat}
    (hi : SiftInv c s tmp0 tmp_init tmp lo0 r0 lim r) (hc : ch < lim)
    (hch_eq : ch = 2 * r + 1 ∨ ch = 2 * r + 2)
    (hge : tmpLe s.lvl s.trail_pos (tmp[1 + ch]?.getD 0#32) (tmp[1 + r]?.getD 0#32))
    (hmax : (2 * r + 2 < lim →
      tmpLe s.lvl s.trail_pos (tmp[1 + (2 * r + 1)]?.getD 0#32) (tmp[1 + ch]?.getD 0#32) ∧
      tmpLe s.lvl s.trail_pos (tmp[1 + (2 * r + 2)]?.getD 0#32) (tmp[1 + ch]?.getD 0#32))) :
    IsMaxHeapFrom s.lvl s.trail_pos tmp lo0 lim := by
  intro i hi1 hi2
  by_cases hir : i = r
  · subst i
    constructor
    · intro h1
      by_cases h2 : 2 * r + 2 < lim
      · exact tmpLe_trans (hmax h2).1 hge
      · rcases hch_eq with rfl | rfl
        · exact hge
        · omega
    · intro h2; exact tmpLe_trans (hmax h2).2 hge
  · exact hi.2.2.2.2.2.2.2.2.2.1 i hi1 hi2 hir

private theorem siftInv_swap {c : PlainCfg} {s : PlainState}
    {tmp0 tmp_init tmp : List (BitVec 32)} {lo0 r0 lim r ch : Nat}
    (hi : SiftInv c s tmp0 tmp_init tmp lo0 r0 lim r)
    (hs_le : s.tmp_len ≤ c.mv) (hlim_tl : lim < s.tmp_len)
    (hlo0 : lo0 = r0 ∨ (lo0 = 0 ∧ r0 = 0))
    (hc1 : 2 * r + 1 ≤ ch) (hc2 : ch ≤ 2 * r + 2) (hch_lim : ch < lim)
    (hlt : tmpLt s.lvl s.trail_pos (tmp[1 + r]?.getD 0#32) (tmp[1 + ch]?.getD 0#32))
    (hmax : 2 * r + 2 < lim →
      tmpLe s.lvl s.trail_pos (tmp[1 + (2 * r + 1)]?.getD 0#32) (tmp[1 + ch]?.getD 0#32) ∧
      tmpLe s.lvl s.trail_pos (tmp[1 + (2 * r + 2)]?.getD 0#32) (tmp[1 + ch]?.getD 0#32)) :
    let hlen := hi.1
    let hu : 1 + r < tmp.length := by omega
    let hv : 1 + ch < tmp.length := by omega
    SiftInv c s tmp0 tmp_init (sortSwap tmp (1 + r) (1 + ch) hu hv) lo0 r0 lim ch := by
  intro hlen hu hv
  let tmp' := sortSwap tmp (1 + r) (1 + ch) hu hv
  have hrc_ne : r ≠ ch := by omega
  have hget (idx : Nat) :
      tmp'[idx]?.getD 0#32 =
        if idx = 1 + ch then tmp[1 + r]?.getD 0#32
        else if idx = 1 + r then tmp[1 + ch]?.getD 0#32
        else tmp[idx]?.getD 0#32 := by
    dsimp only [tmp']; rw [sortSwap_getElem?]
    by_cases h1 : idx = 1 + ch
    · simp only [h1, ↓reduceIte, List.getElem?_eq_getElem hu, Option.getD_some]
    · by_cases h2 : idx = 1 + r
      · rw [h2]; simp only [show 1 + r ≠ 1 + ch by omega, ↓reduceIte,
          List.getElem?_eq_getElem hv, Option.getD_some]
      · simp only [h1, h2, ↓reduceIte]
  have hpar_ch : (ch - 1) / 2 = r := by omega
  rcases hi with ⟨_, h0, hseq, hbd, hpin, hpout, hr_lim, hlo_r, hr0_r, hheap, hgp⟩
  refine ⟨sortSwap_length.trans hlen, ?_, ?_, ?_, ?_, ?_, hch_lim, by omega, by omega, ?_, ?_⟩
  · intro htp; rw [sortSwap_getElem?]
    simp only [show 0 ≠ 1 + ch by omega, show 0 ≠ 1 + r by omega, ↓reduceIte]
    exact h0 htp
  · exact sortSliceEq_trans (sortSwap_sliceEq (by omega) (by omega) (by omega) (by omega)) hseq
  · intro k hk1 hk2; rw [sortSwap_getElem?]
    by_cases h1 : k = 1 + ch
    · simp only [h1, ↓reduceIte]; have := hbd (1 + r) (by omega) (by omega)
      rwa [List.getElem?_eq_getElem hu, Option.getD_some] at this
    · by_cases h2 : k = 1 + r
      · rw [h2]; simp only [show 1 + r ≠ 1 + ch by omega, ↓reduceIte]
        have := hbd (1 + ch) (by omega) (by omega)
        rwa [List.getElem?_eq_getElem hv, Option.getD_some] at this
      · simp only [h1, h2, ↓reduceIte]; exact hbd k hk1 hk2
  · intro k hk1 hk2; rw [sortSwap_getElem?]
    by_cases h1 : k = 1 + ch
    · simp only [h1, ↓reduceIte]
      rw [← List.getElem?_eq_getElem hu]; exact hpin (1 + r) (by omega) (by omega)
    · by_cases h2 : k = 1 + r
      · rw [h2]; simp only [show 1 + r ≠ 1 + ch by omega, ↓reduceIte]
        rw [← List.getElem?_eq_getElem hv]; exact hpin (1 + ch) (by omega) (by omega)
      · simp only [h1, h2, ↓reduceIte]; exact hpin k hk1 hk2
  · intro k hk1 hk2; rw [sortSwap_getElem?]
    simp only [show k ≠ 1 + ch by omega, show k ≠ 1 + r by omega, ↓reduceIte]
    exact hpout k hk1 hk2
  · intro i hi1 hi2 hine
    by_cases hir : i = r
    · subst i
      have hrootv : tmp'[1 + r]?.getD 0#32 = tmp[1 + ch]?.getD 0#32 := by
        rw [hget]; simp only [show 1 + r ≠ 1 + ch by omega, ↓reduceIte]
      constructor
      · intro h1
        rw [hrootv]
        by_cases hc : 2 * r + 1 = ch
        · rw [hc, hget]; simp only [↓reduceIte]; exact tmpLt_mono_le hlt
        · have h2 : 2 * r + 2 < lim := by omega
          rw [hget]
          simp only [show 1 + (2 * r + 1) ≠ 1 + ch by omega,
            show 1 + (2 * r + 1) ≠ 1 + r by omega, ↓reduceIte]
          exact (hmax h2).1
      · intro h2
        rw [hrootv]
        by_cases hc : 2 * r + 2 = ch
        · rw [hc, hget]; simp only [↓reduceIte]; exact tmpLt_mono_le hlt
        · rw [hget]
          simp only [show 1 + (2 * r + 2) ≠ 1 + ch by omega,
            show 1 + (2 * r + 2) ≠ 1 + r by omega, ↓reduceIte]
          exact (hmax h2).2
    · have hiv : tmp'[1 + i]?.getD 0#32 = tmp[1 + i]?.getD 0#32 := by
        rw [hget]
        simp only [show 1 + i ≠ 1 + ch by omega, show 1 + i ≠ 1 + r by omega, ↓reduceIte]
      have hheap_i := hheap i hi1 hi2 hir
      constructor
      · intro h1
        rw [hiv]
        by_cases hcr : 2 * i + 1 = r
        · have hgt : r0 < r := by rcases hlo0 with rfl | ⟨rfl, rfl⟩ <;> omega
          rw [hcr, hget]; simp only [show 1 + r ≠ 1 + ch by omega, ↓reduceIte]
          have hgp' := hgp hgt
          rcases Nat.lt_or_eq_of_le hc1 with hc2_eq | hc1_eq
          · have hch2 : ch = 2 * r + 2 := by omega
            rw [hch2]; simpa [show (r - 1) / 2 = i by omega] using hgp'.2.2 (by omega)
          · rw [← hc1_eq]; simpa [show (r - 1) / 2 = i by omega] using hgp'.2.1 (by omega)
        · rw [hget]
          simp only [show 1 + (2 * i + 1) ≠ 1 + ch by omega,
            show 1 + (2 * i + 1) ≠ 1 + r by omega, ↓reduceIte]
          exact hheap_i.1 h1
      · intro h2
        rw [hiv]
        by_cases hcr : 2 * i + 2 = r
        · have hgt : r0 < r := by rcases hlo0 with rfl | ⟨rfl, rfl⟩ <;> omega
          rw [hcr, hget]; simp only [show 1 + r ≠ 1 + ch by omega, ↓reduceIte]
          have hgp' := hgp hgt
          rcases Nat.lt_or_eq_of_le hc1 with hc2_eq | hc1_eq
          · have hch2 : ch = 2 * r + 2 := by omega
            rw [hch2]; simpa [show (r - 1) / 2 = i by omega] using hgp'.2.2 (by omega)
          · rw [← hc1_eq]; simpa [show (r - 1) / 2 = i by omega] using hgp'.2.1 (by omega)
        · rw [hget]
          simp only [show 1 + (2 * i + 2) ≠ 1 + ch by omega,
            show 1 + (2 * i + 2) ≠ 1 + r by omega, ↓reduceIte]
          exact hheap_i.2 h2
  · intro _; refine ⟨by omega, ?_, ?_⟩
    · intro h1
      have hheap_c := hheap ch (by omega) hch_lim (by omega)
      rw [hget, hget, hpar_ch]
      simp only [show 1 + (2 * ch + 1) ≠ 1 + ch by omega,
        show 1 + (2 * ch + 1) ≠ 1 + r by omega, show 1 + r ≠ 1 + ch by omega, ↓reduceIte]
      exact hheap_c.1 h1
    · intro h2
      have hheap_c := hheap ch (by omega) hch_lim (by omega)
      rw [hget, hget, hpar_ch]
      simp only [show 1 + (2 * ch + 2) ≠ 1 + ch by omega,
        show 1 + (2 * ch + 2) ≠ 1 + r by omega, show 1 + r ≠ 1 + ch by omega, ↓reduceIte]
      exact hheap_c.2 h2

private def siftDownExpr (lim tmp_ptr lvl_ptr tpos_ptr : Val i64)
    (brk : Cont [i64]) (initRoot : Arg Val i64) : Expr Val Cont [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg Val i64) : Op Val [i64] :=
    Op.mk c (a, b, ())
  let ldTmp (idx : Val i64) (k : Val i32 → Expr Val Cont []) : Expr Val Cont [] :=
    .let_ (op64 (.add i64) (.var tmp_ptr) (.var idx)) fun a => .load i32 (.var a.fst) k
  let idxOff (o : BitVec 64) (v : Arg Val i64) (k : Tup Val [i64] → Expr Val Cont []) :
      Expr Val Cont [] :=
    .let_ (op64 (.add i64) (.imm o) v) fun s =>
      .let_ (op64 (.mul i64) (.var s.fst) (.imm 4)) k
  let callLess (l1 l2 : Val i32) (k : Tup Val [.bool] → Expr Val Cont []) : Expr Val Cont [] :=
    .call "plain_tmp_less" (as := [i64, i64, i32, i32]) (bs := [.bool])
      (.var lvl_ptr, .var tpos_ptr, .var l1, .var l2, ()) k
  .group (sig := [[i64]]) (fun Js => .cons (fun p => .jnz (.imm true)
    (.let_ (Op.mk (.sext 32 64) (.imm (1 : BitVec 32), ())) fun p_7 =>
      .let_ (op64 (.shl i64) (.var p.fst) (.var p_7.fst)) fun p_8 =>
        .let_ (op64 (.add i64) (.var p_8.fst) (.imm 1)) fun p_9 =>
          .let_ (Op.mk (.cmp .uge i64 .bool rfl) (.var p_9.fst, .var lim, ())) fun p_10 =>
            .jnz (.var p_10.fst) (.jump brk (.var p.fst, ()))
              (.group (sig := [[i64]]) (fun _ => .cons (fun p_11 =>
                idxOff 1 (.var p.fst) fun p_13 => ldTmp p_13.fst fun ld_3 =>
                idxOff 1 (.var p_11.fst) fun p_16 => ldTmp p_16.fst fun ld_4 =>
                callLess ld_3 ld_4 fun p_18 => .jnz (.var p_18.fst)
                  (idxOff 1 (.var p.fst) fun p_20 => ldTmp p_20.fst fun ld_5 =>
                    idxOff 1 (.var p.fst) fun px =>
                    .let_ (op64 (.add i64) (.var tmp_ptr) (.var px.fst)) fun pa =>
                    idxOff 1 (.var p_11.fst) fun p_23 => ldTmp p_23.fst fun ld_6 =>
                    .store (.var ld_6) (.var pa.fst)
                      (idxOff 1 (.var p_11.fst) fun py =>
                        .let_ (op64 (.add i64) (.var tmp_ptr) (.var py.fst)) fun pb =>
                        .store (.var ld_5) (.var pb.fst) (.jump Js.fst (.var p_11.fst, ()))))
                  (.jump brk (.var p.fst, ()))) .nil)
                (fun Js =>
                  .let_ (op64 (.add i64) (.var p_9.fst) (.imm 1)) fun pa =>
                  .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var pa.fst, .var lim, ()))
                    fun pb => .jnz (.var pb.fst)
                      (idxOff 1 (.var p_9.fst) fun p1 => ldTmp p1.fst fun ld_3 =>
                        idxOff 2 (.var p_9.fst) fun p2 => ldTmp p2.fst fun ld =>
                        callLess ld_3 ld fun pc => .jnz (.var pc.fst)
                          (.let_ (op64 (.add i64) (.var p_9.fst) (.imm 1)) fun pd =>
                            .jump Js.fst (.var pd.fst, ()))
                          (.jump Js.fst (.var p_9.fst, ())))
                      (.jump Js.fst (.var p_9.fst, ())))))
    (.jump brk (.var p.fst, ()))) .nil)
    (fun Js => .jump Js.fst (initRoot, ()))

private theorem plain_sift_down_wp {Γ : Env}
    (hTl : ∀ args m Q X, plainTmpLessSpec args m Q X →
      Γ "plain_tmp_less" [i64, i64, i32, i32] [.bool] args m Q X)
    {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop} {Q : Post []} {X}
    {tmp0 tmp_init : List (BitVec 32)} {lo0 : Nat} {r0_arg : Arg Val i64} {lim : Val i64}
    {brk : Cont [i64]}
    (hbrk : ∀ (r_end : BitVec 64) m' tmp',
      tmp'.length = c.mv →
      (0 < s.tmp_len → tmp'[0]? = tmp0[0]?) →
      SortSliceEq tmp' tmp0 s.tmp_len →
      (∀ k, 1 ≤ k → k < s.tmp_len → (tmp'[k]?.getD 0#32).toNat < 2 * c.mv) →
      (∀ k, 1 ≤ k → k < 1 + lim.toNat → ∃ j, 1 ≤ j ∧ j < 1 + lim.toNat ∧
        tmp'[k]? = tmp_init[j]?) →
      (∀ k, 1 + lim.toNat ≤ k → k < s.tmp_len → tmp'[k]? = tmp_init[k]?) →
      IsMaxHeapFrom s.lvl s.trail_pos tmp' lo0 lim.toNat →
      (PlainMem c { s with tmp := tmp' } ⋆ R) m' →
      brk (r_end, ()) m')
    (hlen : s.LengthsOk c) (hs_le : s.tmp_len ≤ c.mv) (hlim_tl : lim.toNat < s.tmp_len)
    (hlo0 : lo0 = r0_arg.val.toNat ∨ (lo0 = 0 ∧ r0_arg.val.toNat = 0))
    {m0 : Mem 64}
    (hsift0 : SiftInv c s tmp0 tmp_init tmp_init lo0 r0_arg.val.toNat lim.toNat r0_arg.val.toNat)
    (hm0 : (PlainMem c { s with tmp := tmp_init } ⋆ R) m0) :
    wp Γ Q X (siftDownExpr lim c.pTmp c.pLevel c.pTrailPos brk r0_arg) m0 := by
  dsimp only [siftDownExpr]
  let SiftLp : Nat → Tup Val [i64] → Mem 64 → Prop := fun n (r, ()) m1 =>
    n = lim.toNat - r.toNat ∧
    ∃ tmp1, SiftInv c s tmp0 tmp_init tmp1 lo0 r0_arg.val.toNat lim.toNat r.toNat ∧
      (PlainMem c { s with tmp := tmp1 } ⋆ R) m1
  refine wp_loop_group (ts := [i64]) SiftLp ?_ ?_
  · rintro J n ⟨r, ⟨⟩⟩ m1 hJ ⟨rfl, tmp1, hsi, hm1⟩
    rw [Blocks.get_here]; rw [wp]; refine ⟨fun _ => ?_, fun h_im => by cases h_im⟩
    ml_lets
    have hsi_cp := hsi
    rcases hsi with ⟨htl, h0, hseq, hbd, hpin, hpout, hr_lim, hlo_r, hr0_r, hheap, hgp⟩
    have hmv := c.hmv; unfold dimacsBound at hmv
    have h2r2 : 2 * r.toNat + 2 < 2 ^ 64 := by omega
    have hc1_nat : ((r <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)) + 1).toNat =
        2 * r.toNat + 1 := bv64_shl1_add1_toNat (x := r) (by omega)
    ml_jnz; refine ⟨fun hoob => ?_, fun hch_in => ?_⟩
    · change BitVec.ule lim ((r <<< _) + 1) = true at hoob
      rw [BitVec.ule, decide_eq_true_eq, hc1_nat] at hoob
      exact hbrk r m1 tmp1 htl h0 hseq hbd hpin hpout (siftInv_done_of_oob hsi_cp hoob) hm1
    · have hc1_lt : 2 * r.toNat + 1 < lim.toNat := by
        change BitVec.ule lim ((r <<< _) + 1) = false at hch_in
        rw [BitVec.ule, decide_eq_false_iff_not, hc1_nat] at hch_in; omega
      let c1 : BitVec 64 := r <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1
      have hc1_eq : c1.toNat = 2 * r.toNat + 1 := hc1_nat
      let ChJoin : Tup Val [i64] → Mem 64 → Prop := fun (ch, ()) m2 =>
        m2 = m1 ∧ 2 * r.toNat + 1 ≤ ch.toNat ∧ ch.toNat ≤ 2 * r.toNat + 2 ∧
        ch.toNat < lim.toNat ∧
        (2 * r.toNat + 2 < lim.toNat →
          tmpLe s.lvl s.trail_pos (tmp1[1 + (2 * r.toNat + 1)]?.getD 0#32)
            (tmp1[1 + ch.toNat]?.getD 0#32) ∧
          tmpLe s.lvl s.trail_pos (tmp1[1 + (2 * r.toNat + 2)]?.getD 0#32)
            (tmp1[1 + ch.toNat]?.getD 0#32))
      refine wp_join_group (ts := [i64]) ChJoin ?_ ?_
      · rintro J2 ⟨ch, ⟨⟩⟩ m2 ⟨rfl, hc_lo, hc_hi, hch_lim, hch_max⟩
        rw [Blocks.get_here]; ml_lets
        have hc1_bv : ((1 : BitVec 64) + r).toNat = 1 + r.toNat := by
          have h1 : (1 : BitVec 64).toNat = 1 := rfl
          rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
        have hc2_bv : ((1 : BitVec 64) + ch).toNat = 1 + ch.toNat := by
          have h1 : (1 : BitVec 64).toNat = 1 := rfl
          rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
        have hi_r : ((1 : BitVec 64) + r).toNat <
            ({ s with tmp := tmp1 } : PlainState).tmp.length := by
          dsimp only; rw [hc1_bv, htl]; omega
        have hi_c : ((1 : BitVec 64) + ch).toNat <
            ({ s with tmp := tmp1 } : PlainState).tmp.length := by
          dsimp only; rw [hc2_bv, htl]; omega
        rw [wp]; refine ⟨_, c0_load_arena_tmp (s := { s with tmp := tmp1 }) hi_r hm1, ?_⟩
        ml_lets; rw [wp]
        refine ⟨_, c0_load_arena_tmp (s := { s with tmp := tmp1 }) hi_c hm1, ?_⟩
        ml_lets
        let vr := tmp1[((1 : BitVec 64) + r).toNat]'hi_r
        let vc := tmp1[((1 : BitVec 64) + ch).toNat]'hi_c
        have hvr_eq : vr = tmp1[1 + r.toNat]'(by rw [htl]; omega) := by simp only [vr, hc1_bv]
        have hvc_eq : vc = tmp1[1 + ch.toNat]'(by rw [htl]; omega) := by simp only [vc, hc2_bv]
        have hvr_lt : vr.toNat < 2 * c.mv := by
          have := hbd (1 + r.toNat) (by omega) (by omega)
          rw [List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some] at this
          rwa [hvr_eq]
        have hvc_lt : vc.toNat < 2 * c.mv := by
          have := hbd (1 + ch.toNat) (by omega) (by omega)
          rw [List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some] at this
          rwa [hvc_eq]
        obtain ⟨R_tl, hR_tl⟩ : ∃ R_tl : Mem 64 → Prop,
            (array (t := i32) c.pLevel s.lvl ⋆ array (t := i32) c.pTrailPos s.trail_pos ⋆
              R_tl) m2 := ⟨_, by unfold PlainMem PlainCoreArrays at hm1; ecancel⟩
        apply wp_call_of_spec; apply hTl
        refine ⟨s.lvl, s.trail_pos, R_tl,
          by change vr.toNat / 2 < s.lvl.length; rw [hlen.lvl_len]; omega,
          by change vc.toNat / 2 < s.lvl.length; rw [hlen.lvl_len]; omega,
          by change vr.toNat / 2 < s.trail_pos.length; rw [hlen.trail_pos_len]; omega,
          by change vc.toNat / 2 < s.trail_pos.length; rw [hlen.trail_pos_len]; omega,
          hR_tl, ?_⟩
        · dsimp only; ml_lets; ml_jnz; refine ⟨fun hless => ?_, fun hge => ?_⟩
          · have hlt' : tmpLt s.lvl s.trail_pos
                (tmp1[1 + r.toNat]?.getD 0#32) (tmp1[1 + ch.toNat]?.getD 0#32) := by
              rw [List.getElem?_eq_getElem (by rw [htl]; omega),
                List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some,
                Option.getD_some, ← hvr_eq, ← hvc_eq]
              exact tmpLt_of_decide_true hless
            ml_lets; rw [wp]
            refine ⟨_, c0_load_arena_tmp (s := { s with tmp := tmp1 }) hi_r hm1, ?_⟩
            ml_lets; rw [wp]
            refine ⟨_, c0_load_arena_tmp (s := { s with tmp := tmp1 }) hi_c hm1, ?_⟩
            ml_lets; rw [wp]
            obtain ⟨hok1, hm2⟩ := c0_store_arena_tmp (s := { s with tmp := tmp1 })
              (i := 1 + r) (tmp1[((1 : BitVec 64) + ch).toNat]'hi_c) hi_r hm1
            refine ⟨hok1, ?_⟩
            ml_lets; rw [wp]
            let tmp1b := tmp1.set ((1 : BitVec 64) + r).toNat
              (tmp1[((1 : BitVec 64) + ch).toNat]'hi_c)
            have hi_c' : ((1 : BitVec 64) + ch).toNat <
                ({ s with tmp := tmp1b } : PlainState).tmp.length := by
              simpa [tmp1b] using hi_c
            obtain ⟨hok2, hm3⟩ := c0_store_arena_tmp (s := { s with tmp := tmp1b })
              (i := 1 + ch) (tmp1[((1 : BitVec 64) + r).toNat]'hi_r) hi_c' hm2
            refine ⟨hok2, ?_⟩
            let tmp2 := sortSwap tmp1 (1 + r.toNat) (1 + ch.toNat)
              (by rw [htl]; omega) (by rw [htl]; omega)
            have hm3' : (PlainMem c { s with tmp := tmp2 } ⋆ R)
                (storeMem (storeMem m2 i32 (c.pTmp + ((1 : BitVec 64) + r) * 4)
                  (tmp1[((1 : BitVec 64) + ch).toNat]'hi_c)) i32
                  (c.pTmp + ((1 : BitVec 64) + ch) * 4)
                  (tmp1[((1 : BitVec 64) + r).toNat]'hi_r)) := by
              simpa only [tmp2, tmp1b, sortSwap, hc1_bv, hc2_bv] using hm3
            exact hJ (lim.toNat - ch.toNat) (ch, ()) _ (by omega)
              ⟨rfl, tmp2, siftInv_swap hsi_cp hs_le hlim_tl hlo0 hc_lo hc_hi hch_lim
                hlt' hch_max, hm3'⟩
          · have hge' : tmpLe s.lvl s.trail_pos
                (tmp1[1 + ch.toNat]?.getD 0#32) (tmp1[1 + r.toNat]?.getD 0#32) := by
              rw [List.getElem?_eq_getElem (by rw [htl]; omega),
                List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some,
                Option.getD_some, ← hvr_eq, ← hvc_eq]
              exact tmpLe_of_decide_false hge
            have hch_eq' : ch.toNat = 2 * r.toNat + 1 ∨ ch.toNat = 2 * r.toNat + 2 := by omega
            exact hbrk r m2 tmp1 htl h0 hseq hbd hpin hpout
              (siftInv_done_of_ge hsi_cp hch_lim hch_eq' hge' hch_max) hm1
      · rintro J2 hJ2; ml_lets
        have hc2_bv : (c1 + 1).toNat = 2 * r.toNat + 2 := by
          have h1 : (1 : BitVec 64).toNat = 1 := rfl
          rw [BitVec.toNat_add, hc1_eq, h1, Nat.mod_eq_of_lt (by omega)]
        ml_jnz; refine ⟨fun hc2_lt => ?_, fun hc2_ge => ?_⟩
        · change (c1 + 1).ult lim = true at hc2_lt
          rw [BitVec.ult, decide_eq_true_eq, hc2_bv] at hc2_lt
          have h1c1 : ((1 : BitVec 64) + c1).toNat = 1 + (2 * r.toNat + 1) := by
            have h1 : (1 : BitVec 64).toNat = 1 := rfl
            rw [BitVec.toNat_add, hc1_eq, h1, Nat.mod_eq_of_lt (by omega)]
          have h2c1 : ((2 : BitVec 64) + c1).toNat = 1 + (2 * r.toNat + 2) := by
            have h2 : (2 : BitVec 64).toNat = 2 := rfl
            rw [BitVec.toNat_add, hc1_eq, h2, Nat.mod_eq_of_lt (by omega)]; omega
          have hi1 : ((1 : BitVec 64) + c1).toNat <
              ({ s with tmp := tmp1 } : PlainState).tmp.length := by
            dsimp only; rw [h1c1, htl]; omega
          have hi2 : ((2 : BitVec 64) + c1).toNat <
              ({ s with tmp := tmp1 } : PlainState).tmp.length := by
            dsimp only; rw [h2c1, htl]; omega
          ml_lets; rw [wp]; refine ⟨_, c0_load_arena_tmp (s := { s with tmp := tmp1 }) hi1 hm1, ?_⟩
          ml_lets; rw [wp]; refine ⟨_, c0_load_arena_tmp (s := { s with tmp := tmp1 }) hi2 hm1, ?_⟩
          ml_lets
          let v1 := tmp1[((1 : BitVec 64) + c1).toNat]'hi1
          let v2 := tmp1[((2 : BitVec 64) + c1).toNat]'hi2
          have hv1_eq : v1 = tmp1[1 + (2 * r.toNat + 1)]'(by rw [htl]; omega) := by
            simp only [v1, h1c1]
          have hv2_eq : v2 = tmp1[1 + (2 * r.toNat + 2)]'(by rw [htl]; omega) := by
            simp only [v2, h2c1]
          have hv1_lt : v1.toNat < 2 * c.mv := by
            have := hbd (1 + (2 * r.toNat + 1)) (by omega) (by omega)
            rw [List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some] at this
            rwa [hv1_eq]
          have hv2_lt : v2.toNat < 2 * c.mv := by
            have := hbd (1 + (2 * r.toNat + 2)) (by omega) (by omega)
            rw [List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some] at this
            rwa [hv2_eq]
          obtain ⟨R_tl, hR_tl⟩ : ∃ R_tl : Mem 64 → Prop,
              (array (t := i32) c.pLevel s.lvl ⋆ array (t := i32) c.pTrailPos s.trail_pos ⋆
                R_tl) m1 := ⟨_, by unfold PlainMem PlainCoreArrays at hm1; ecancel⟩
          apply wp_call_of_spec; apply hTl
          refine ⟨s.lvl, s.trail_pos, R_tl,
            by change v1.toNat / 2 < s.lvl.length; rw [hlen.lvl_len]; omega,
            by change v2.toNat / 2 < s.lvl.length; rw [hlen.lvl_len]; omega,
            by change v1.toNat / 2 < s.trail_pos.length; rw [hlen.trail_pos_len]; omega,
            by change v2.toNat / 2 < s.trail_pos.length; rw [hlen.trail_pos_len]; omega,
            hR_tl, ?_⟩
          · dsimp only; ml_lets; ml_jnz; refine ⟨fun hless => ?_, fun hge => ?_⟩
            · have hlt' : tmpLt s.lvl s.trail_pos
                  (tmp1[1 + (2 * r.toNat + 1)]?.getD 0#32)
                  (tmp1[1 + (2 * r.toNat + 2)]?.getD 0#32) := by
                rw [List.getElem?_eq_getElem (by rw [htl]; omega),
                  List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some,
                  Option.getD_some, ← hv1_eq, ← hv2_eq]
                exact tmpLt_of_decide_true hless
              ml_lets; apply hJ2; change ChJoin (c1 + 1, ()) m1
              refine ⟨rfl, by rw [hc2_bv]; omega, by rw [hc2_bv]; omega,
                by rw [hc2_bv]; exact hc2_lt, fun _ => ?_⟩
              rw [hc2_bv]; exact ⟨tmpLt_mono_le hlt', tmpLe_refl _ _ _⟩
            · have hge' : tmpLe s.lvl s.trail_pos
                  (tmp1[1 + (2 * r.toNat + 2)]?.getD 0#32)
                  (tmp1[1 + (2 * r.toNat + 1)]?.getD 0#32) := by
                rw [List.getElem?_eq_getElem (by rw [htl]; omega),
                  List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some,
                  Option.getD_some, ← hv1_eq, ← hv2_eq]
                exact tmpLe_of_decide_false hge
              ml_lets; apply hJ2; change ChJoin (c1, ()) m1
              refine ⟨rfl, by rw [hc1_eq]; omega, by rw [hc1_eq]; omega,
                by rw [hc1_eq]; exact hc1_lt, fun _ => ?_⟩
              rw [hc1_eq]; exact ⟨tmpLe_refl _ _ _, hge'⟩
        · change (c1 + 1).ult lim = false at hc2_ge
          rw [BitVec.ult, decide_eq_false_iff_not, hc2_bv] at hc2_ge
          ml_lets; apply hJ2; change ChJoin (c1, ()) m1
          exact ⟨rfl, by rw [hc1_eq]; omega, by rw [hc1_eq]; omega,
            by rw [hc1_eq]; exact hc1_lt, fun h => by omega⟩
  · intro J hJ; wp_unfold
    exact hJ (lim.toNat - r0_arg.val.toNat) (r0_arg.val, ()) m0 ⟨rfl, tmp_init, hsift0, hm0⟩

theorem plain_sort_tmp_wp (Γ : Env)
    (hTl : ∀ args m Q X, plainTmpLessSpec args m Q X →
      Γ "plain_tmp_less" [i64, i64, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, plainSortTmpSpec args m Q X →
      Func.wp Γ plain_sort_tmp_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, htle, hbd0, hm, hQ⟩
  unfold Func.wp plain_sort_tmp_body; dsimp only [plain_sort_tmp_body]
  rw [wp]; refine ⟨_, load_arena_tmp_len hm, ?_⟩; ml_lets
  ml_jnz; refine ⟨fun hle2 => ?_, fun hgt2 => ?_⟩
  · c0_cond hle2
    have htl2 : s.tmp_len ≤ 2 := by
      have hmv := c.hmv; unfold dimacsBound at hmv; bv_omega
    ml_lets; rw [wp]
    refine hQ s.tmp m hlen.tmp_len_arr (fun _ => rfl)
      (fun j h1 h2 => ⟨j, h1, h2, rfl⟩) (fun i h1 h2 => ⟨i, h1, h2, rfl⟩)
      (fun i j hi hij hj => by
        have hij' : i = j := by omega
        subst hij'; exact le_refl _)
      hm
  · have htl2 : 2 < s.tmp_len := by
      change (BitVec.ofNat 64 s.tmp_len).ule 2 = false at hgt2
      rw [BitVec.ule, decide_eq_false_iff_not] at hgt2
      have hmv := c.hmv; unfold dimacsBound at hmv
      have : (2 : BitVec 64).toNat = 2 := rfl
      rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hgt2; omega
    have hmv := c.hmv; unfold dimacsBound at hmv
    let n : BitVec 64 := BitVec.ofNat 64 s.tmp_len - 1
    have hn_eq : n.toNat = s.tmp_len - 1 := by
      dsimp only [n]
      have htle' : s.tmp_len < 2 ^ 64 := by omega
      have h1 : (1 : BitVec 64).toNat = 1 := rfl
      rw [BitVec.toNat_sub_of_le (by bv_omega), h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt htle']
    ml_lets; rw [wp]; refine ⟨_, load_arena_tmp_lits hm, ?_⟩
    ml_lets; rw [wp]; refine ⟨_, load_arena_level hm, ?_⟩
    ml_lets; rw [wp]; refine ⟨_, load_arena_trail_pos hm, ?_⟩
    ml_lets
    let Loop1Inv : Nat → Tup Val [i64] → Mem 64 → Prop := fun dec (start, ()) m1 =>
      dec = start.toNat ∧ start.toNat ≤ n.toNat / 2 ∧
      ∃ tmp1, tmp1.length = c.mv ∧
        (0 < s.tmp_len → tmp1[0]? = s.tmp[0]?) ∧
        SortSliceEq tmp1 s.tmp s.tmp_len ∧
        (∀ k, 1 ≤ k → k < s.tmp_len → (tmp1[k]?.getD 0#32).toNat < 2 * c.mv) ∧
        IsMaxHeapFrom s.lvl s.trail_pos tmp1 start.toNat n.toNat ∧
        (PlainMem c { s with tmp := tmp1 } ⋆ R) m1
    refine wp_loop_group (ts := [i64]) Loop1Inv ?_ ?_
    · rintro J1 dec ⟨start, ⟨⟩⟩ m1 hJ1 ⟨rfl, hst_le, tmp1, htl1, h01, hseq1, hbd1, hh1, hm1⟩
      rw [Blocks.get_here]; ml_lets
      ml_jnz; refine ⟨fun hst_pos => ?_, fun hst0 => ?_⟩
      · have hst_gt0 : 0 < start.toNat := by c0_cond hst_pos; bv_omega
        have hst_m1 : (start - 1).toNat = start.toNat - 1 := by
          have h1 : (1 : BitVec 64).toNat = 1 := rfl
          rw [BitVec.toNat_sub_of_le (by bv_omega), h1]
        have hst1_lt : (start - 1).toNat < n.toNat := by omega
        ml_lets
        refine wp_join_group (ts := [i64]) (fun (p', ()) m2 =>
          ∃ tmp2, tmp2.length = c.mv ∧
            (0 < s.tmp_len → tmp2[0]? = s.tmp[0]?) ∧
            SortSliceEq tmp2 s.tmp s.tmp_len ∧
            (∀ k, 1 ≤ k → k < s.tmp_len → (tmp2[k]?.getD 0#32).toNat < 2 * c.mv) ∧
            IsMaxHeapFrom s.lvl s.trail_pos tmp2 (start - 1).toNat n.toNat ∧
            (PlainMem c { s with tmp := tmp2 } ⋆ R) m2) ?_ ?_
        · rintro _ ⟨_, ⟨⟩⟩ m2 ⟨tmp2, htl2', h02, hseq2, hbd2, hh2, hm2⟩
          rw [Blocks.get_here]; ml_lets
          exact hJ1 (start - 1).toNat (start - 1, ()) m2 (by rw [hst_m1]; omega)
            ⟨rfl, by rw [hst_m1]; omega, tmp2, htl2', h02, hseq2, hbd2, hh2, hm2⟩
        · rintro Jbrk hJbrk
          have hsift0 : SiftInv c s s.tmp tmp1 tmp1 (start - 1).toNat (start - 1).toNat n.toNat
              (start - 1).toNat :=
            ⟨htl1, h01, hseq1, hbd1, fun k hk1 hk2 => ⟨k, hk1, hk2, rfl⟩,
              fun k _ _ => rfl, hst1_lt, le_refl _, le_refl _,
              fun i hi1 hi2 hine => hh1 i (by omega) hi2,
              fun hlt => absurd hlt (Nat.lt_irrefl _)⟩
          refine plain_sift_down_wp hTl (brk := Jbrk) (r0_arg := .var (start - 1))
            (fun r_end m2 tmp2 htl2' h02 hseq2 hbd2 _ _ hh2 hm2 =>
              hJbrk (r_end, ()) m2 ⟨tmp2, htl2', h02, hseq2, hbd2, hh2, hm2⟩)
            hlen htle (by omega) (Or.inl rfl) hsift0 hm1
      · have hst_eq0 : start.toNat = 0 := by
          change (0 : BitVec 64).ult start = false at hst0
          rw [BitVec.ult, decide_eq_false_iff_not] at hst0; bv_omega
        rw [hst_eq0] at hh1
        ml_lets
        let e0 : BitVec 64 := n - 1
        have he0 : e0.toNat = n.toNat - 1 := by
          dsimp only [e0]; have h1 : (1 : BitVec 64).toNat = 1 := rfl
          rw [BitVec.toNat_sub_of_le (by bv_omega), h1]
        let Loop2Inv : Nat → Tup Val [i64] → Mem 64 → Prop := fun dec2 (e, ()) m2 =>
          dec2 = e.toNat ∧ e.toNat < n.toNat ∧
          ∃ tmp2, tmp2.length = c.mv ∧
            (0 < s.tmp_len → tmp2[0]? = s.tmp[0]?) ∧
            SortSliceEq tmp2 s.tmp s.tmp_len ∧
            (∀ k, 1 ≤ k → k < s.tmp_len → (tmp2[k]?.getD 0#32).toNat < 2 * c.mv) ∧
            IsMaxHeapFrom s.lvl s.trail_pos tmp2 0 (e.toNat + 1) ∧
            (∀ j, e.toNat + 1 ≤ j → j < n.toNat → ∀ i, i ≤ j →
              tmpLe s.lvl s.trail_pos (tmp2[1 + i]?.getD 0#32) (tmp2[1 + j]?.getD 0#32)) ∧
            (PlainMem c { s with tmp := tmp2 } ⋆ R) m2
        refine wp_loop_group (ts := [i64]) Loop2Inv ?_ ?_
        · rintro J2 dec2 ⟨e, ⟨⟩⟩ m2 hJ2 ⟨rfl, he_lt, tmp2, htl2', h02, hseq2, hbd2,
            hh2, hsorted2, hm2⟩
          rw [Blocks.get_here]; ml_lets
          ml_jnz; refine ⟨fun he_pos => ?_, fun he0' => ?_⟩
          · have he_gt0 : 0 < e.toNat := by c0_cond he_pos; bv_omega
            have h1n : (1 : BitVec 64).toNat = 1 := rfl
            have h1e_bv : ((1 : BitVec 64) + e).toNat = 1 + e.toNat := by
              rw [BitVec.toNat_add, h1n, Nat.mod_eq_of_lt (by omega)]
            have hi1 : (1 : BitVec 64).toNat <
                ({ s with tmp := tmp2 } : PlainState).tmp.length := by
              dsimp only; rw [h1n, htl2']; omega
            have hie : ((1 : BitVec 64) + e).toNat <
                ({ s with tmp := tmp2 } : PlainState).tmp.length := by
              dsimp only; rw [h1e_bv, htl2']; omega
            ml_lets; rw [wp]
            refine ⟨_, c0_load_arena_tmp (s := { s with tmp := tmp2 }) (i := (1 : BitVec 64))
              hi1 hm2, ?_⟩
            ml_lets; rw [wp]
            refine ⟨_, c0_load_arena_tmp (s := { s with tmp := tmp2 }) hie hm2, ?_⟩
            ml_lets; rw [wp]
            obtain ⟨hok1, hm3⟩ := c0_store_arena_tmp (s := { s with tmp := tmp2 })
              (i := (1 : BitVec 64)) (tmp2[((1 : BitVec 64) + e).toNat]'hie) hi1 hm2
            refine ⟨hok1, ?_⟩
            ml_lets; rw [wp]
            let tmp2b := tmp2.set (1 : BitVec 64).toNat
              (tmp2[((1 : BitVec 64) + e).toNat]'hie)
            have hie' : ((1 : BitVec 64) + e).toNat <
                ({ s with tmp := tmp2b } : PlainState).tmp.length := by
              simpa [tmp2b] using hie
            obtain ⟨hok2, hm4⟩ := c0_store_arena_tmp (s := { s with tmp := tmp2b })
              (i := 1 + e) (tmp2[(1 : BitVec 64).toNat]'hi1) hie' hm3
            refine ⟨hok2, ?_⟩
            let tmp3 := sortSwap tmp2 1 (1 + e.toNat) (by rw [htl2']; omega) (by rw [htl2']; omega)
            have hm4' : (PlainMem c { s with tmp := tmp3 } ⋆ R)
                (storeMem (storeMem m2 i32 (c.pTmp + (1 : BitVec 64) * 4)
                  (tmp2[((1 : BitVec 64) + e).toNat]'hie)) i32
                  (c.pTmp + ((1 : BitVec 64) + e) * 4) (tmp2[(1 : BitVec 64).toNat]'hi1)) := by
              simpa only [tmp3, tmp2b, sortSwap, h1n, h1e_bv] using hm4
            have hget3 (idx : Nat) : tmp3[idx]?.getD 0#32 =
                if idx = 1 + e.toNat then tmp2[1]?.getD 0#32
                else if idx = 1 then tmp2[1 + e.toNat]?.getD 0#32
                else tmp2[idx]?.getD 0#32 := by
              dsimp only [tmp3]; rw [sortSwap_getElem?]
              by_cases h1 : idx = 1 + e.toNat
              · simp only [h1, ↓reduceIte,
                  List.getElem?_eq_getElem (by rw [htl2']; omega : 1 < tmp2.length),
                  Option.getD_some]
              · by_cases h2 : idx = 1
                · rw [h2]; simp only [show (1 : Nat) ≠ 1 + e.toNat by omega, ↓reduceIte,
                    List.getElem?_eq_getElem (by rw [htl2']; omega : 1 + e.toNat < tmp2.length),
                    Option.getD_some]
                · simp only [h1, h2, ↓reduceIte]
            have htl3 : tmp3.length = c.mv := sortSwap_length.trans htl2'
            have h03 : 0 < s.tmp_len → tmp3[0]? = s.tmp[0]? := fun htp => by
              rw [sortSwap_getElem?]
              simp only [show 0 ≠ 1 + e.toNat by omega, show (0 : Nat) ≠ 1 by omega, ↓reduceIte]
              exact h02 htp
            have hseq3 : SortSliceEq tmp3 s.tmp s.tmp_len :=
              sortSliceEq_trans (sortSwap_sliceEq (by omega) (by omega) (by omega) (by omega)) hseq2
            have hbd3 : ∀ k, 1 ≤ k → k < s.tmp_len → (tmp3[k]?.getD 0#32).toNat < 2 * c.mv := by
              intro k hk1 hk2; rw [sortSwap_getElem?]
              by_cases h1 : k = 1 + e.toNat
              · simp only [h1, ↓reduceIte]; have := hbd2 1 (by omega) (by omega)
                rwa [List.getElem?_eq_getElem (by rw [htl2']; omega), Option.getD_some] at this
              · by_cases h2 : k = 1
                · rw [h2]; simp only [show (1 : Nat) ≠ 1 + e.toNat by omega, ↓reduceIte]
                  have := hbd2 (1 + e.toNat) (by omega) (by omega)
                  rwa [List.getElem?_eq_getElem (by rw [htl2']; omega), Option.getD_some] at this
                · simp only [h1, h2, ↓reduceIte]; exact hbd2 k hk1 hk2
            have hmax3_tail : ∀ j, e.toNat ≤ j → j < n.toNat → ∀ i, i ≤ j →
                tmpLe s.lvl s.trail_pos (tmp3[1 + i]?.getD 0#32) (tmp3[1 + j]?.getD 0#32) := by
              intro j hj1 hj2 i hij
              by_cases hje : j = e.toNat
              · subst hje
                rw [hget3 (1 + e.toNat)]; simp only [↓reduceIte]
                by_cases hie' : i = e.toNat
                · subst hie'; rw [hget3 (1 + e.toNat)]; simp only [↓reduceIte]
                  exact tmpLe_refl _ _ _
                · by_cases hi0 : i = 0
                  · subst hi0; rw [hget3 1]
                    simp only [show (1 : Nat) ≠ 1 + e.toNat by omega, ↓reduceIte]
                    exact heap_root_max hh2 e.toNat (by omega)
                  · rw [hget3 (1 + i)]
                    simp only [show 1 + i ≠ 1 + e.toNat by omega, show 1 + i ≠ 1 by omega,
                      ↓reduceIte]
                    exact heap_root_max hh2 i (by omega)
              · have hje1 : e.toNat + 1 ≤ j := by omega
                rw [hget3 (1 + j)]
                simp only [show 1 + j ≠ 1 + e.toNat by omega, show 1 + j ≠ 1 by omega, ↓reduceIte]
                by_cases hie' : i = e.toNat
                · subst hie'; rw [hget3 (1 + e.toNat)]; simp only [↓reduceIte]
                  exact hsorted2 j hje1 hj2 0 (by omega)
                · by_cases hi0 : i = 0
                  · subst hi0; rw [hget3 1]
                    simp only [show (1 : Nat) ≠ 1 + e.toNat by omega, ↓reduceIte]
                    exact hsorted2 j hje1 hj2 e.toNat (by omega)
                  · rw [hget3 (1 + i)]
                    simp only [show 1 + i ≠ 1 + e.toNat by omega, show 1 + i ≠ 1 by omega,
                      ↓reduceIte]
                    exact hsorted2 j hje1 hj2 i hij
            have hsift3 : SiftInv c s s.tmp tmp3 tmp3 0 0 e.toNat 0 := by
              refine ⟨htl3, h03, hseq3, hbd3, fun k hk1 hk2 => ⟨k, hk1, hk2, rfl⟩,
                fun k _ _ => rfl, he_gt0, le_refl _, le_refl _, ?_, fun h => by omega⟩
              intro i _ hi2 hine
              have hhi2 := hh2 i (Nat.zero_le _) (by omega)
              have hiv : tmp3[1 + i]?.getD 0#32 = tmp2[1 + i]?.getD 0#32 := by
                rw [hget3]
                simp only [show 1 + i ≠ 1 + e.toNat by omega, show 1 + i ≠ 1 by omega, ↓reduceIte]
              constructor
              · intro h1; rw [hiv, hget3]
                simp only [show 1 + (2 * i + 1) ≠ 1 + e.toNat by omega,
                  show 1 + (2 * i + 1) ≠ 1 by omega, ↓reduceIte]
                exact hhi2.1 (by omega)
              · intro h2; rw [hiv, hget3]
                simp only [show 1 + (2 * i + 2) ≠ 1 + e.toNat by omega,
                  show 1 + (2 * i + 2) ≠ 1 by omega, ↓reduceIte]
                exact hhi2.2 (by omega)
            ml_lets
            have he_m1 : (e - 1).toNat = e.toNat - 1 := by
              have h1 : (1 : BitVec 64).toNat = 1 := rfl
              rw [BitVec.toNat_sub_of_le (by bv_omega), h1]
            refine wp_join_group (ts := [i64]) (fun (_, ()) m3 =>
              ∃ tmp4, tmp4.length = c.mv ∧
                (0 < s.tmp_len → tmp4[0]? = s.tmp[0]?) ∧
                SortSliceEq tmp4 s.tmp s.tmp_len ∧
                (∀ k, 1 ≤ k → k < s.tmp_len → (tmp4[k]?.getD 0#32).toNat < 2 * c.mv) ∧
                IsMaxHeapFrom s.lvl s.trail_pos tmp4 0 e.toNat ∧
                (∀ j, e.toNat ≤ j → j < n.toNat → ∀ i, i ≤ j →
                  tmpLe s.lvl s.trail_pos (tmp4[1 + i]?.getD 0#32) (tmp4[1 + j]?.getD 0#32)) ∧
                (PlainMem c { s with tmp := tmp4 } ⋆ R) m3) ?_ ?_
            · rintro _ ⟨_, ⟨⟩⟩ m3 ⟨tmp4, htl4, h04, hseq4, hbd4, hh4, hsorted4, hm4⟩
              rw [Blocks.get_here]; ml_lets
              exact hJ2 (e - 1).toNat (e - 1, ()) m3 (by rw [he_m1]; omega)
                ⟨rfl, by rw [he_m1]; omega, tmp4, htl4, h04, hseq4, hbd4,
                  by rw [he_m1, Nat.sub_add_cancel he_gt0]; exact hh4,
                  by rw [he_m1, Nat.sub_add_cancel he_gt0]; exact hsorted4, hm4⟩
            · rintro Jbrk2 hJbrk2
              refine plain_sift_down_wp hTl (brk := Jbrk2) (r0_arg := .imm 0)
                (fun r_end m3 tmp4 htl4 h04 hseq4 hbd4 hpin4 hpout4 hh4 hm4 => by
                  apply hJbrk2 (r_end, ()) m3
                  refine ⟨tmp4, htl4, h04, hseq4, hbd4, hh4, fun j hj1 hj2 i hij => ?_, hm4⟩
                  have hj_eq : tmp4[1 + j]? = tmp3[1 + j]? := hpout4 (1 + j) (by omega) (by omega)
                  rw [hj_eq]
                  by_cases hie_c : i < e.toNat
                  · obtain ⟨k, hk1, hk2, hik⟩ := hpin4 (1 + i) (by omega) (by omega)
                    rw [hik]
                    have hkm1 : k - 1 ≤ j := by omega
                    simpa [show 1 + (k - 1) = k by omega] using hmax3_tail j hj1 hj2 (k - 1) hkm1
                  · rw [hpout4 (1 + i) (by omega) (by omega)]
                    exact hmax3_tail j hj1 hj2 i hij)
                hlen htle (by omega) (Or.inr ⟨rfl, rfl⟩) hsift3 hm4'
          · have he_eq0 : e.toNat = 0 := by
              change (0 : BitVec 64).ult e = false at he0'
              rw [BitVec.ult, decide_eq_false_iff_not] at he0'; bv_omega
            rw [he_eq0] at hsorted2
            ml_lets; rw [wp]
            refine hQ tmp2 m2 htl2' h02 hseq2.1 hseq2.2 (fun i j hi1 hij hj => ?_) hm2
            by_cases hj1 : j = 1
            · subst hj1
              have hij' : i = 1 := by omega
              subst hij'; exact le_refl _
            · exact tmpLe_lvl (by
                simpa [show 1 + (i - 1) = i by omega, show 1 + (j - 1) = j by omega] using
                  hsorted2 (j - 1) (by omega) (by omega) (i - 1) (by omega))
        · intro J2 hJ2; wp_unfold
          exact hJ2 e0.toNat (e0, ()) m1 ⟨rfl, by omega, tmp1, htl1, h01, hseq1, hbd1,
            by rw [he0, Nat.sub_add_cancel (by omega)]; exact hh1,
            fun j hj1 => by rw [he0] at hj1; omega, hm1⟩
    · intro J1 hJ1; wp_unfold
      have hsh : ((n >>> ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64))).toNat =
          n.toNat / 2 := by
        have h1 : BitVec.signExtend 64 (1 : BitVec 32) = (1 : BitVec 64) := rfl
        have hm' : (1 : BitVec 64).toNat % 64 = 1 := rfl
        rw [h1, hm', bv64_lshr_1]
      have hh0 : IsMaxHeapFrom s.lvl s.trail_pos s.tmp (n.toNat / 2) n.toNat := by
        intro i hi1 hi2; exact ⟨fun h => by omega, fun h => by omega⟩
      exact hJ1 _ _ m ⟨hsh, le_refl _, s.tmp, hlen.tmp_len_arr, fun _ => rfl,
        sortSliceEq_refl _ _, hbd0, hh0, hm⟩

end LeanQbe.T.Examples.Kissat.Plain

