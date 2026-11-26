module

public import LeanQbe.T.Examples.Kissat.FullM5Sched
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem

/-!
# Shared Arithmetic, BitVector & `full_log10_q16` Helpers (`FullKissatMath`)

Deduplicated Q16 `log10` WP proof (`full_log10_q16_core_wp`), powers-of-10 bounds,
Q16 packing bounds, and shared `BitVec` / `C0` arithmetic helpers across Kissat proofs.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullKissatMath

open Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep

/-! ## 1. Powers of 10, Q16 Packing & `BitVec` Helpers -/

theorem pow10_lt_64 {d : Nat} (hd : d ≤ 19) : 10 ^ d < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hd) (by decide)

theorem pow10_succ_mul10 {d : Nat} {p : BitVec 64} (hd : d < 19) (hp : p.toNat ≤ 10 ^ d) :
    p.toNat * 10 ≤ 10 ^ (d + 1) ∧ p.toNat * 10 < 2 ^ 64 ∧ (p * 10#64).toNat = p.toNat * 10 := by
  have hpow : p.toNat * 10 ≤ 10 ^ (d + 1) := by
    rw [Nat.pow_succ]; exact Nat.mul_le_mul_right 10 hp
  have hlt64 : p.toNat * 10 < 2 ^ 64 := Nat.lt_of_le_of_lt hpow (pow10_lt_64 (by omega))
  have hmul : (p * 10#64).toNat = p.toNat * 10 := by
    rw [BitVec.toNat_mul, show (10#64).toNat = 10 from rfl, Nat.mod_eq_of_lt hlt64]
  exact ⟨hpow, hlt64, hmul⟩

theorem shift_split_65536 {k : Nat} (hk : k < 16) :
    (65536 >>> k) = (32768 >>> k) + (65536 >>> (k + 1)) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨
      k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem bv64_add_toNat {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem bv64_add1_toNat {g : BitVec 64} (h : g.toNat + 1 < 2 ^ 64) :
    (g + 1#64).toNat = g.toNat + 1 := bv64_add_toNat h

theorem bv64_sub_toNat {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by bv_omega

theorem bv64_sub1_toNat {f : BitVec 64} (hf : f ≠ 0#64) : (f - 1#64).toNat = f.toNat - 1 := by
  have hpos : 0 < f.toNat := Nat.pos_of_ne_zero fun h0 =>
    hf (BitVec.eq_of_toNat_eq (by simpa using h0))
  bv_omega

theorem bv64_shl1_toNat {v : BitVec 64} (h : 2 * v.toNat < 2 ^ 64) :
    (v <<< 1#64).toNat = 2 * v.toNat := by
  have hsh : v <<< 1#64 = v <<< (1#64).toNat := rfl
  rw [hsh, BitVec.toNat_shiftLeft, show (1#64).toNat = 1 by decide, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem bv64_ofNat_toNat {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem bv32_ofNat_toNat {n : Nat} (hn : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem zext_toNat {w1 w2 : Nat} (x : BitVec w1) (hle : w1 ≤ w2) :
    (x.setWidth w2).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right
    (by omega) hle))]

theorem bv64_trunc32_ofNat {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, bv64_ofNat_toNat (by omega), bv32_ofNat_toNat hn,
    Nat.mod_eq_of_lt hn]

theorem bv64_zext32_ushr1 (x : BitVec 32) :
    ((x.setWidth 64) >>> (BitVec.signExtend 64 (1 : BitVec 32)).toNat).toNat = x.toNat / 2 := by
  have h1 : (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 1 := rfl
  rw [h1]; bv_omega

theorem bv32_xor1_div2 (x : BitVec 32) : (x ^^^ 1#32).toNat / 2 = x.toNat / 2 := by
  have hsr : (x ^^^ 1#32) >>> 1 = x >>> 1 := by
    ext i hi
    simp [BitVec.getLsbD_xor, show (1#32).getLsbD (1 + i) = false by
      simp [BitVec.getLsbD_one]]
  have h1 : ((x ^^^ 1#32) >>> 1).toNat = (x ^^^ 1#32).toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h2 : (x >>> 1).toNat = x.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [← h1, ← h2, hsr]

private theorem nat_two_mul_or_one (k : Nat) : (2 * k) ||| 1 = 2 * k + 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ j =>
    rw [Nat.testBit_or]; simp only [Nat.testBit_succ]
    have h10 : Nat.testBit (1 / 2) j = false := by simp
    have hd1 : (2 * k) / 2 = k := by omega
    have hd2 : (2 * k + 1) / 2 = k := by omega
    rw [h10, hd1, hd2, Bool.or_false]

theorem bv32_lit_even {x : BitVec 64} (hx : x.toNat < 2 ^ 30) :
    ((x <<< 1#64).setWidth 32).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_setWidth, bv64_shl1_toNat (by omega), Nat.mod_eq_of_lt (by omega)]

theorem bv32_lit_odd {x : BitVec 64} (hx : x.toNat < 2 ^ 30) :
    (((x <<< 1#64).setWidth 32 ||| 1#32)).toNat = 2 * x.toNat + 1 := by
  rw [BitVec.toNat_or, bv32_lit_even hx, show (1#32 : BitVec 32).toNat = 1 by decide]
  exact nat_two_mul_or_one x.toNat

theorem q16_shl_bounds {x d frac : BitVec 64} (hd : d.toNat ≤ 19) (hf : frac.toNat < 65536)
    (h10 : 10 ≤ x.toNat → 1 ≤ d.toNat) :
    ((d <<< (16 : Nat)) + frac).toNat < 20 * 65536 ∧
    (10 ≤ x.toNat → 65536 ≤ ((d <<< (16 : Nat)) + frac).toNat) := by
  have hd_sh : (d <<< (16 : Nat)).toNat = d.toNat * 65536 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      show d.toNat * 2 ^ 16 = d.toNat * 65536 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hsum : ((d <<< (16 : Nat)) + frac).toNat = d.toNat * 65536 + frac.toNat := by
    rw [BitVec.toNat_add, hd_sh, Nat.mod_eq_of_lt (by omega)]
  exact ⟨by rw [hsum]; omega, fun hx => by have := h10 hx; rw [hsum]; omega⟩

theorem q16_mul_bounds {x d frac : BitVec 64} (hd : d.toNat ≤ 19) (hf : frac.toNat < 65536)
    (h10 : 10 ≤ x.toNat → 1 ≤ d.toNat) :
    (d * 65536#64 + frac).toNat < 20 * 65536 ∧
    (10 ≤ x.toNat → 65536 ≤ (d * 65536#64 + frac).toNat) := by
  have hmul : (d * 65536#64).toNat = d.toNat * 65536 := by bv_omega
  have hsum : (d * 65536#64 + frac).toNat = d.toNat * 65536 + frac.toNat := by
    rw [BitVec.toNat_add, hmul, Nat.mod_eq_of_lt (by omega)]
  exact ⟨by rw [hsum]; omega, fun hx => by have := h10 hx; rw [hsum]; omega⟩

/-! ## 2. Shared `wp_let` Math Combinators & `full_log10_q16` WP Core -/

theorem wp_let_ult64_m {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {hm : Ty.bool = Ty.mask i64} {a b : Arg Val i64}
    {k : Tup Val [.bool] → Expr Val Cont rs} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult i64 .bool hm) (a, b, ())) k) m =
      wp Γ Q X (k (BitVec.ult a.val b.val, ())) m := by
  have hc := @wp_let_cmp_eq Γ rs Q X m .ult i64 .bool hm (a, b, ()) k
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, liftCmp,
    evalBits_ult_eq, cast_eq] using hc

theorem wp_let_udiv64_m {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a b : Arg Val i64} {k : Tup Val [i64] → Expr Val Cont rs}
    (hb : b.val ≠ 0#64) :
    wp Γ Q X (.let_ (Op.mk (.udiv 64) (a, b, ())) k) m ↔
      wp Γ Q X (k (a.val / b.val, ())) m := by
  rw [wp_let_udiv_eq]; exact ⟨fun h => h.2, fun h => ⟨hb, h⟩⟩

theorem wp_let_udiv64_var_m {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a : Arg Val i64} {vb : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs}
    (hb : vb ≠ 0#64) :
    wp Γ Q X (.let_ (Op.mk (.udiv 64) (a, .var vb, ())) k) m ↔
      wp Γ Q X (k (a.val / vb, ())) m := wp_let_udiv64_m hb

theorem wp_let_udiv64_imm_m {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a : Arg Val i64} {ib : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs}
    (hb : ib ≠ 0#64) :
    wp Γ Q X (.let_ (Op.mk (.udiv 64) (a, .imm ib, ())) k) m ↔
      wp Γ Q X (k (a.val / ib, ())) m := wp_let_udiv64_m hb

/-- Shared WP theorem for the Q32 repeated-squaring `full_log10_q16` algorithm
(certifying both `FullM5Sched.full_log10_q16_body` and `FullM7Search.full_log10_q16_m7_body`). -/
theorem full_log10_q16_core_wp (Γ : Env) (x : BitVec 64) (m : Mem 64)
    (Q : Post [i64]) (X : XPost)
    (hQ : ∀ r : BitVec 64, r.toNat < 20 * 65536 →
      (10 ≤ x.toNat → 65536 ≤ r.toNat) → Q (r, ()) m) :
    Func.wp Γ FullM5Sched.full_log10_q16_body (x, ()) m Q X := by
  c0_hsteps_nogrp
  · have hx1 : x.toNat ≤ 1 := by c0_bound
    exact hQ 0#64 (by decide) (fun hx10 => by omega)
  · refine wp_loop_inv (ts := [i64, i64])
      (fun (d, pow10, ()) m1 =>
        m = m1 ∧ d.toNat ≤ 19 ∧ 1 ≤ pow10.toNat ∧ pow10.toNat ≤ 10 ^ d.toNat ∧
        (d.toNat = 0 → pow10.toNat = 1))
      (fun (d, _, ()) _ => 19 - d.toNat) ?_ ?_
    · intro J hJ
      c0_hsteps; exact hJ (0#64, 1#64, ()) m ⟨rfl, by decide, by decide, by decide, fun _ => rfl⟩
    · rintro J ⟨d, pow10, ⟨⟩⟩ _ ⟨rfl, hd19, hp1, hple, hd0p⟩ hJ
      refine wp_join_group (ts := []) (fun _ m1 => m = m1 ∧ (10 ≤ x.toNat → 1 ≤ d.toNat))
        ?_ ?_
      · rintro _ ⟨⟩ _ ⟨rfl, hd10⟩
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64, i64]) (fun (_, pm', ()) m2 => m = m2 ∧ 1 ≤ pm'.toNat)
          ?_ ?_
        · rintro _ ⟨xm', pm', ⟨⟩⟩ m2 ⟨hm2, hpm⟩
          subst m2
          have hpm_ne : pm' ≠ 0#64 := fun h0 => by subst h0; simp at hpm
          c0_hsteps_nogrp
          all_goals try exact hpm_ne
          refine wp_loop_inv (ts := [i64, i64, i64])
            (fun (_mv, frac, i, ()) m3 => m = m3 ∧ i.toNat ≤ 16 ∧ frac.toNat < 2 ^ i.toNat)
            (fun (_, _, i, ()) _ => 16 - i.toNat) ?_ ?_
          · intro J2 hJ2; c0_hsteps; exact hJ2 (_, 0#64, 0#64, ()) m ⟨rfl, by decide, by decide⟩
          · rintro J2 ⟨mv, frac, i, ⟨⟩⟩ m3 ⟨hm3, hi16, hfl⟩ hJ2
            subst m3; c0_hsteps
            · have hi_lt : i.toNat < 16 := by c0_bound
              have hf_lt : frac.toNat < 2 ^ 15 :=
                Nat.lt_of_lt_of_le hfl (Nat.pow_le_pow_right (by omega) (by omega))
              have hi1 : (i + 1#64).toNat = i.toNat + 1 := bv64_add1_toNat (by omega)
              have hf2p1 : (frac <<< (1 : Nat) + 1#64).toNat = 2 * frac.toNat + 1 := by bv_omega
              have hf2p1_lt : 2 * frac.toNat + 1 < 2 ^ (i.toNat + 1) := by rw [Nat.pow_succ]; omega
              exact hJ2 (_, (frac <<< (1 : Nat)) + 1#64, i + 1#64, ()) m (by dsimp only; omega)
                ⟨rfl, by omega, by rw [hi1, hf2p1]; exact hf2p1_lt⟩
            · have hi_lt : i.toNat < 16 := by c0_bound
              have hf_lt : frac.toNat < 2 ^ 15 :=
                Nat.lt_of_lt_of_le hfl (Nat.pow_le_pow_right (by omega) (by omega))
              have hf_sh : (frac <<< (1 : Nat)).toNat = 2 * frac.toNat := by
                rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
              have hf2_lt : 2 * frac.toNat < 2 ^ (i.toNat + 1) := by rw [Nat.pow_succ]; omega
              have hi1 : (i + 1#64).toNat = i.toNat + 1 := bv64_add1_toNat (by omega)
              exact hJ2 (_, frac <<< (1 : Nat), i + 1#64, ()) m (by dsimp only; omega)
                ⟨rfl, by omega, by rw [hi1, hf_sh]; exact hf2_lt⟩
            · have hflt : frac.toNat < 65536 :=
                Nat.lt_of_lt_of_le hfl (Nat.pow_le_pow_right (by omega) hi16)
              obtain ⟨hlt, hge⟩ := q16_shl_bounds hd19 hflt hd10
              exact hQ ((d <<< (16 : Nat)) + frac) hlt hge
        · intro _ hJm; c0_hsteps_nogrp
          · have hpm_gt : 100000000 < pow10.toNat := by c0_bound
            intro h0; have ht := congrArg BitVec.toNat h0
            change pow10.toNat / 100000000 = 0 at ht
            have hpos : 0 < pow10.toNat / 100000000 :=
              Nat.div_pos (Nat.le_of_lt hpm_gt) (by decide)
            omega
          · exact hJm (x / (pow10 / 100000000#64), 100000000#64, ()) m ⟨rfl, by decide⟩
          · exact hJm (x, pow10, ()) m ⟨rfl, hp1⟩
      · intro _ hJexit; c0_hsteps_nogrp
        · have hd_lt : d.toNat < 19 := by c0_bound
          obtain ⟨hp10, _, hp_mul⟩ := pow10_succ_mul10 hd_lt hple
          have hd1 : (d + 1#64).toNat = d.toNat + 1 := bv64_add1_toNat (by omega)
          exact hJ (d + 1#64, pow10 * 10#64, ()) m (by dsimp only; omega)
            ⟨rfl, by omega, by omega, by rw [hd1, hp_mul]; exact hp10,
             fun h0 => by rw [hd1] at h0; omega⟩
        · have hge : 19 ≤ d.toNat := by c0_bound
          exact hJexit () m ⟨rfl, fun _ => by omega⟩
        · have hlt : x.toNat / 10 < pow10.toNat := by
            have hdiv : (x / 10#64).toNat < pow10.toNat := by c0_bound
            have hmod : (x / 10#64).toNat = x.toNat / 10 := by bv_omega
            omega
          refine hJexit () m ⟨rfl, fun hx10 => ?_⟩
          rcases Nat.eq_zero_or_pos d.toNat with hd0 | hdpos
          · have hp1' := hd0p hd0; omega
          · exact hdpos

end LeanQbe.T.Examples.Kissat.FullKissatMath
