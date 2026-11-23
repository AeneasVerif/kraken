module

public import LeanQbe.T.Examples.Kissat.FullM7CongHash
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullCongLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.C0Agrees
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M7 Dynamic Congruence Hash Table Proofs — Part 0 (`FullM7CongHashProof0`)

M1-clean verification (`public section`, `0` `@[expose]`, `0` `import all`, `0` `maxHeartbeats`,
`0` `bv_decide`):
1. `M7CongHtCtrlOk` / `M7CongHtInv` invariants and bridges to `FullCongSpecs.CongHtInv`.
2. Parametric `(Γ : Env)` `Func.wp` proofs for all `5` functions (`full_cong_ht_hash_ent_m7`,
   `full_cong_ht_init_m7`, `full_cong_ht_grow_m7`, `full_cong_ht_lookup_m7`,
   `full_cong_ht_insert_m7`) preserving `SafetySlice.spec (fullSafetySlice c)` (`FullState.core`
   + `LengthsOk c`), `FullExtScratchPres`, and prefix `scratch_buf`.
3. Closed `5`-row `m7CongHashSpecTable`, `m7CongHashEnv`, `m7CongHash_moduleOk`, and
   `m7CongHashEnv_noExit`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7CongHash

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open Kraken.Bedrock2.Test

/-! ## 1. Pure Arithmetic & BitVec Helpers -/

section Helpers

theorem bv32_ofNat_toNat_lt {n : Nat} (h : n < 2 ^ 32) :
    (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem bv64_ofNat_toNat_lt {n : Nat} (h : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem bv64_zext32_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

private theorem bv64_trunc32_toNat {x : BitVec 64} (hx : x.toNat < 2 ^ 32) :
    (x.setWidth 32).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx]

theorem bv64_add1_lt {a : BitVec 64} {n : Nat} (ha : a.toNat < n) (hn : n < 2 ^ 64) :
    (a + 1#64).toNat = a.toNat + 1 :=
  show (a.toNat + 1) % 2 ^ 64 = a.toNat + 1 from Nat.mod_eq_of_lt (by omega)

private theorem bv64_sub_toNat {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)

theorem bv64_add_toNat {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem bv64_cap_sub_mod {a cap : Nat} (ha : a ≤ cap) (hc : cap < 2 ^ 64) :
    (2 ^ 64 - a + cap) % 2 ^ 64 = cap - a := by
  rw [show 2 ^ 64 - a + cap = (cap - a) + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

theorem bv64_add_ofNat_toNat {a : BitVec 64} (k : Nat) (hk : k < 2 ^ 64)
    (h : a.toNat + k < 2 ^ 64) : (a + BitVec.ofNat 64 k).toNat = a.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt h]

theorem bv64_zext32_add_ofNat (e : BitVec 32) (k : Nat) (hk : k < 2 ^ 32) :
    (e.setWidth 64 + BitVec.ofNat 64 k).toNat = e.toNat + k := by
  have he := e.isLt
  rw [bv64_add_ofNat_toNat k (by omega) (by rw [bv64_zext32_toNat]; omega), bv64_zext32_toNat]

private theorem bv64_shl1_toNat {a : BitVec 64} (ha : 2 * a.toNat < 2 ^ 64) :
    (a <<< (1#32 : BitVec 32).signExtend 64).toNat = 2 * a.toNat := by
  change (a <<< (1 : Nat)).toNat = 2 * a.toNat
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
  exact Nat.mod_eq_of_lt ha

theorem bv64_and_sub1_lt {x sz : BitVec 64} (hpos : 0 < sz.toNat) :
    (x &&& (sz - 1#64)).toNat < sz.toNat := by
  have hle : (x &&& (sz - 1#64)).toNat ≤ (sz - 1#64).toNat := by
    rw [BitVec.toNat_and]; exact Nat.and_le_right
  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
  have hsub : (sz - 1#64).toNat = sz.toNat - 1 := by
    rw [bv64_sub_toNat (by rw [h1]; omega), h1]
  omega

theorem pow2_16_mul_le (k : Nat) (hk : k ≤ 13) : 16 * 2 ^ k ≤ 131072 := by
  have hpow : 2 ^ k ≤ 2 ^ 13 := Nat.pow_le_pow_right (by omega) hk
  have h13 : 2 ^ 13 = 8192 := by decide
  omega

theorem bv64_pow2_and_sub1_zero {sz : BitVec 64} {k : Nat} (_hk : k ≤ 13)
    (heq : sz.toNat = 16 * 2 ^ k) : (sz &&& (sz - 1#64)) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have hpow : 16 * 2 ^ k = 2 ^ (k + 4) := by
    rw [Nat.pow_add, show (2 : Nat) ^ 4 = 16 from by decide, Nat.mul_comm]
  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
  have h2p := Nat.two_pow_pos k
  have hsub : (sz - 1#64).toNat = 2 ^ (k + 4) - 1 := by
    rw [bv64_sub_toNat (by rw [h1, heq]; omega), heq, hpow, h1]
  rw [BitVec.toNat_and, hsub, heq, hpow, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_self]
  rfl

theorem bv64_and_pow2_mod {x sz : BitVec 64} {k : Nat} (_hk : k ≤ 13)
    (heq : sz.toNat = 16 * 2 ^ k) :
    (x &&& (sz - 1#64)).toNat = x.toNat % sz.toNat := by
  have hpow : 16 * 2 ^ k = 2 ^ (k + 4) := by
    rw [Nat.pow_add, show (2 : Nat) ^ 4 = 16 from by decide, Nat.mul_comm]
  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
  have h2p := Nat.two_pow_pos k
  have hsub : (sz - 1#64).toNat = 2 ^ (k + 4) - 1 := by
    rw [bv64_sub_toNat (by rw [h1, heq]; omega), heq, hpow, h1]
  rw [BitVec.toNat_and, hsub, Nat.and_two_pow_sub_one_eq_mod, heq, hpow]

private theorem pow2_16_of_and_zero {sz : Nat} (hge : 16 ≤ sz) (hle : sz ≤ 131072)
    (hand : (BitVec.ofNat 64 sz &&& (BitVec.ofNat 64 sz - 1#64)) = 0#64) :
    ∃ k ≤ 13, sz = 16 * 2 ^ k := by
  have hlt64 : sz < 2 ^ 64 := by omega
  have h1c : (1#64 : BitVec 64).toNat = 1 := rfl
  have h1 : (BitVec.ofNat 64 sz &&& (BitVec.ofNat 64 sz - 1#64)).toNat = 0 := by
    rw [hand]; rfl
  rw [BitVec.toNat_and, bv64_sub_toNat (by
    rw [bv64_ofNat_toNat_lt hlt64, h1c]; omega),
    bv64_ofNat_toNat_lt hlt64, h1c] at h1
  have hb : ∀ n ≤ 131072, 16 ≤ n → (n &&& (n - 1)) = 0 →
      n = 16 ∨ n = 32 ∨ n = 64 ∨ n = 128 ∨ n = 256 ∨ n = 512 ∨ n = 1024 ∨ n = 2048 ∨
      n = 4096 ∨ n = 8192 ∨ n = 16384 ∨ n = 32768 ∨ n = 65536 ∨ n = 131072 := by
    intro n hle' hge' hn
    have hpow2 : ∀ t, t ≤ 17 → n < 2 ^ (t + 1) → 16 ≤ n → (n &&& (n - 1)) = 0 →
        ∃ j ≤ t, n = 2 ^ j := by
      intro t; induction t with
      | zero =>
        intro _ hlt _ _; exfalso; change n < 2 ^ 1 at hlt; omega
      | succ t ih =>
        intro _ hlt h16 ha
        by_cases hlt' : n < 2 ^ (t + 1)
        · obtain ⟨j, hj, rfl⟩ := ih (by omega) hlt' h16 ha; exact ⟨j, by omega, rfl⟩
        · have hge_t : 1 * 2 ^ (t + 1) ≤ n := by rw [Nat.one_mul]; omega
          have hbit : n.testBit (t + 1) = true := by
            have hd1 : n / 2 ^ (t + 1) = 1 := by
              have hlt_mul : n < (1 + 1) * 2 ^ (t + 1) := by
                rw [show 1 + 1 = 2 from rfl, Nat.mul_comm, ← Nat.pow_succ]; exact hlt
              exact Nat.div_eq_of_lt_le hge_t hlt_mul
            rw [Nat.testBit_eq_decide_div_mod_eq, hd1]; decide
          have hzero : ∀ b, b ≠ t + 1 → n.testBit b = false := by
            intro b hne
            by_cases hb1 : n.testBit b = false
            · exact hb1
            · exfalso
              have hbt : n.testBit b = true := by
                cases hb_v : n.testBit b
                · exact absurd hb_v hb1
                · rfl
              by_cases hltb : b < t + 1
              · have hm1 : (n - 1).testBit (t + 1) = true := by
                  have hd1 : (n - 1) / 2 ^ (t + 1) = 1 := by
                    have hlt_pow : n - 1 < (1 + 1) * 2 ^ (t + 1) := by
                      have hpow_s : 2 ^ (t + 2) = 2 * 2 ^ (t + 1) := by
                        rw [Nat.pow_succ]; omega
                      have hlt' : n < (1 + 1) * 2 ^ (t + 1) := by
                        rw [show 1 + 1 = 2 from rfl, Nat.mul_comm, ← Nat.pow_succ]; exact hlt
                      omega
                    have hge_pow : 1 * 2 ^ (t + 1) ≤ n - 1 := by
                      rw [Nat.one_mul]
                      by_cases he : n = 2 ^ (t + 1)
                      · subst he
                        have hb_mod : (2 ^ (t + 1)).testBit b = false :=
                          Nat.testBit_two_pow_of_ne (Ne.symm hne)
                        rw [hb_mod] at hbt; cases hbt
                      · omega
                    exact Nat.div_eq_of_lt_le hge_pow hlt_pow
                  rw [Nat.testBit_eq_decide_div_mod_eq, hd1]; decide
                have htest : (n &&& (n - 1)).testBit (t + 1) = true := by
                  rw [Nat.testBit_and, hbit, hm1]; rfl
                rw [ha] at htest; simp at htest
              · have hge_b : t + 2 ≤ b := by omega
                have h2b : 2 ^ (t + 2) ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hge_b
                have hlt_n : n < 2 ^ b := Nat.lt_of_lt_of_le hlt h2b
                have hb_f : n.testBit b = false := Nat.testBit_lt_two_pow hlt_n
                rw [hb_f] at hbt; cases hbt
          have heq_pow : n = 2 ^ (t + 1) := by
            apply Nat.eq_of_testBit_eq
            intro b
            by_cases hb2 : b = t + 1
            · subst hb2; rw [hbit, Nat.testBit_two_pow_self]
            · rw [hzero b hb2, Nat.testBit_two_pow_of_ne (Ne.symm hb2)]
          exact ⟨t + 1, Nat.le_refl _, heq_pow⟩
    have h218 : (2 : Nat) ^ 18 = 262144 := by decide
    obtain ⟨j, hj, rfl⟩ := hpow2 17 (Nat.le_refl _)
      (by rw [show (17 + 1) = 18 from rfl, h218]; omega)
      hge' hn
    have hj4 : 4 ≤ j := by
      rcases Nat.lt_or_ge j 4 with hlt4 | hge4
      · have hp : 2 ^ j ≤ 2 ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
        have h23 : (2 : Nat) ^ 3 = 8 := by decide
        rw [h23] at hp; omega
      · exact hge4
    have hj_cases : j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨
        j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 := by omega
    rcases hj_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rcases hb sz hle hge h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by decide, rfl⟩
  · exact ⟨1, by decide, rfl⟩
  · exact ⟨2, by decide, rfl⟩
  · exact ⟨3, by decide, rfl⟩
  · exact ⟨4, by decide, rfl⟩
  · exact ⟨5, by decide, rfl⟩
  · exact ⟨6, by decide, rfl⟩
  · exact ⟨7, by decide, rfl⟩
  · exact ⟨8, by decide, rfl⟩
  · exact ⟨9, by decide, rfl⟩
  · exact ⟨10, by decide, rfl⟩
  · exact ⟨11, by decide, rfl⟩
  · exact ⟨12, by decide, rfl⟩
  · exact ⟨13, by decide, rfl⟩

private theorem bv32_or8000_and7fff (v : BitVec 32) :
    ((v ||| 0x80000000#32) &&& 0x7FFFFFFF#32) = (v &&& 0x7FFFFFFF#32) := by
  apply BitVec.eq_of_toNat_eq
  apply Nat.eq_of_testBit_eq
  intro i
  rw [BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_or,
    Nat.testBit_and, Nat.testBit_or, Nat.testBit_and]
  have h8 : ∀ j < 32, (0x80000000#32 : BitVec 32).toNat.testBit j = decide (j = 31) := by decide
  have h7 : ∀ j < 32, (0x7FFFFFFF#32 : BitVec 32).toNat.testBit j = decide (j < 31) := by decide
  by_cases hi : i < 32
  · rw [h8 i hi, h7 i hi]
    by_cases h31 : i = 31
    · subst h31; simp
    · simp [h31]
  · have hlt : (0x7FFFFFFF#32 : BitVec 32).toNat < 2 ^ i :=
      Nat.lt_of_lt_of_le (BitVec.isLt _) (Nat.pow_le_pow_right (by omega) (Nat.not_lt.mp hi))
    rw [Nat.testBit_lt_two_pow hlt]; simp

private theorem bv32_and7fff_of_lt {v : BitVec 32} (h : v.toNat < 0x80000000) :
    (v &&& 0x7FFFFFFF#32) = v := by
  apply BitVec.eq_of_toNat_eq
  have h7 : (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 := by decide
  rw [BitVec.toNat_and, h7, Nat.and_two_pow_sub_one_eq_mod]
  have h231 : (2 : Nat) ^ 31 = 0x80000000 := by decide
  rw [h231]; exact Nat.mod_eq_of_lt h

private theorem bv32_or8000_ne_of_msb_zero {v r : BitVec 32}
    (hv : (v &&& 0x80000000#32) = 0#32) : v ≠ r ||| 0x80000000#32 := by
  intro heq
  have h1 : ((r ||| 0x80000000#32) &&& 0x80000000#32).getLsbD 31 = true := by
    rw [BitVec.getLsbD_and, BitVec.getLsbD_or]; simp
  have h2 : (v &&& 0x80000000#32).getLsbD 31 = false := by rw [hv]; decide
  rw [← heq] at h1; rw [h2] at h1; cases h1

private theorem bv32_eq_of_not_ne {a b : BitVec 32} (h : ¬ a ≠ b) : a = b :=
  if h0 : a = b then h0 else absurd h0 h

theorem mod_add_one_eq {x y n : Nat} (h : x = y % n) :
    (x + 1) % n = (y + 1) % n := by
  rw [h, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

theorem probe_visit_idx {hv n k : Nat} (hk : k < n) :
    ∃ i < n, (hv + i) % n = k := by
  have hn : 0 < n := by omega
  let h0 := hv % n
  have hh0 : h0 < n := Nat.mod_lt hv hn
  by_cases hle : h0 ≤ k
  · refine ⟨k - h0, by omega, ?_⟩
    rw [Nat.add_mod, show hv % n = h0 from rfl, Nat.mod_eq_of_lt (by omega : k - h0 < n),
      Nat.add_sub_cancel' hle, Nat.mod_eq_of_lt hk]
  · refine ⟨n - (h0 - k), by omega, ?_⟩
    have heq : h0 + (n - (h0 - k)) = k + n := by omega
    rw [Nat.add_mod, show hv % n = h0 from rfl, Nat.mod_eq_of_lt (by omega : n - (h0 - k) < n),
      heq, Nat.add_mod_right, Nat.mod_eq_of_lt hk]

private theorem scr_idx_add_eq {scr : List (BitVec 32)} {co : BitVec 64} (k : Nat)
    (hk64 : k < 2 ^ 64) (h1 : co.toNat + k < 2 ^ 64) (h2 : co.toNat + k < scr.length)
    (h3 : (BitVec.toNat co + BitVec.toNat (BitVec.ofNat 64 k)) % 2 ^ 64 < scr.length) :
    scr[(BitVec.toNat co + BitVec.toNat (BitVec.ofNat 64 k)) % 2 ^ 64]'h3 =
      scr[co.toNat + k]'h2 := by
  congr 1; rw [bv64_ofNat_toNat_lt hk64, Nat.mod_eq_of_lt h1]

theorem scr_idx_add_imm {scr : List (BitVec 32)} {co : BitVec 64} (k : Nat)
    {kv : BitVec 64} (hkv : kv.toNat = k)
    (h1 : co.toNat + k < 2 ^ 64) (h2 : co.toNat + k < scr.length)
    (h3 : (BitVec.toNat co + BitVec.toNat kv) % 2 ^ 64 < scr.length) :
    scr[(BitVec.toNat co + BitVec.toNat kv) % 2 ^ 64]'h3 = scr[co.toNat + k]'h2 := by
  congr 1; rw [hkv, Nat.mod_eq_of_lt h1]

theorem scr_idx_zext32_add1 {scr : List (BitVec 32)} {e : BitVec 32}
    (h2 : e.toNat + 1 < scr.length)
    (h3 : (BitVec.toNat e + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < scr.length) :
    scr[(BitVec.toNat e + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'h3 =
      scr[e.toNat + 1]'h2 := by
  have he := e.isLt
  congr 1; change (e.toNat + 1) % 2 ^ 64 = e.toNat + 1; exact Nat.mod_eq_of_lt (by omega)

theorem range_countP_le (n : Nat) (f : Nat → Bool) : (List.range n).countP f ≤ n :=
  Nat.le_trans List.countP_le_length (by rw [List.length_range]; exact Nat.le_refl n)

theorem range_countP_pos_exists {n : Nat} {f : Nat → Bool}
    (h : 0 < (List.range n).countP f) : ∃ k < n, f k = true := by
  rw [List.countP_pos_iff] at h
  obtain ⟨k, hk_mem, hk_f⟩ := h
  exact ⟨k, List.mem_range.mp hk_mem, hk_f⟩

theorem range_countP_ext {n : Nat} {f g : Nat → Bool} (h : ∀ k < n, f k = g k) :
    (List.range n).countP f = (List.range n).countP g :=
  List.countP_congr (fun k hk => by rw [h k (List.mem_range.mp hk)])

theorem range_countP_add (a b : Nat) (f : Nat → Bool) :
    (List.range (a + b)).countP f =
      (List.range a).countP f + (List.range b).countP (fun k => f (a + k)) := by
  rw [List.range_add, List.countP_append, List.countP_map]; rfl

theorem range_countP_set {scr : List (BitVec 32)} {ht_off n pos : Nat} {w : BitVec 32}
    (p : BitVec 32 → Bool) (hpos : pos < n) (harr : ht_off + pos < scr.length) :
    (List.range n).countP
        (fun k => p ((scr.set (ht_off + pos) w)[ht_off + k]?.getD 0xFFFFFFFF#32)) +
      (if p (scr[ht_off + pos]?.getD 0xFFFFFFFF#32) then 1 else 0) =
      (List.range n).countP (fun k => p (scr[ht_off + k]?.getD 0xFFFFFFFF#32)) +
      (if p w then 1 else 0) := by
  induction n with
  | zero => omega
  | succ m ih =>
    simp only [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil,
      Nat.zero_add]
    by_cases hmp : pos = m
    · subst hmp
      have hpre : (List.range pos).countP
          (fun k => p ((scr.set (ht_off + pos) w)[ht_off + k]?.getD 0xFFFFFFFF#32)) =
          (List.range pos).countP (fun k => p (scr[ht_off + k]?.getD 0xFFFFFFFF#32)) :=
        range_countP_ext fun k hk => by rw [List.getElem?_set_ne (by omega)]
      rw [hpre, List.getElem?_set_self harr, Option.getD_some]
      cases p w <;> cases p (scr[ht_off + pos]?.getD 0xFFFFFFFF#32) <;> simp <;> omega
    · have ih' := ih (by omega)
      have hne : (scr.set (ht_off + pos) w)[ht_off + m]?.getD 0xFFFFFFFF#32 =
          scr[ht_off + m]?.getD 0xFFFFFFFF#32 := by
        rw [List.getElem?_set_ne (by omega)]
      rw [hne]
      cases p (scr[ht_off + m]?.getD 0xFFFFFFFF#32) <;> simp <;> omega

end Helpers

/-! ## 2. Invariants, Downstream Bridges, & `Spec` Contracts -/

section Specs

/-- Valid power-of-2 congruence hash-table control block in `scr[ctrl_off ..< ctrl_off + 8)`. -/
abbrev M7CongHtCtrlOk (c : FullCfg) (scr : List (BitVec 32))
    (ctrl_off ht_off ht_sz : Nat) : Prop :=
  scr.length = c.scratch_cap ∧
  ctrl_off + 8 ≤ ht_off ∧
  ht_off + ht_sz ≤ c.scratch_cap ∧
  ht_off ≤ 0x7FFFFFFF ∧
  (∃ k ≤ 13, ht_sz = 16 * 2 ^ k) ∧
  scr[ctrl_off + 6]? = some (BitVec.ofNat 32 ht_off) ∧
  scr[ctrl_off + 7]? = some (BitVec.ofNat 32 ht_sz)

/-- Validated congruence hash-table slot invariant parameterized by entry predicate `ValidEnt`. -/
def M7CongHtInv (ValidEnt : BitVec 32 → Prop) (ht_off ht_sz : Nat)
    (scr : List (BitVec 32)) : Prop :=
  ∀ k < ht_sz,
    let ent := scr[ht_off + k]?.getD 0xFFFFFFFF#32
    ent = 0xFFFFFFFF#32 ∨ (ent.toNat < ht_off ∧ ValidEnt ent)

/-- Transport `M7CongHtInv` to canonical `FullCongSpecs.CongHtInv` (`FullM3CongBva` / `Full`). -/
theorem m7CongHtInv_to_congHtInv {F_cur : List (List Nat)} {cv0 g_len ht_off ht_sz : Nat}
    {scr0 scr : List (BitVec 32)}
    (h : M7CongHtInv (fun ent => FullCongSpecs.GateAt F_cur cv0 scr0 g_len ent.toNat)
      ht_off ht_sz scr) :
    FullCongSpecs.CongHtInv F_cur cv0 scr0 scr g_len ht_off ht_sz := fun k hk => by
  rcases h k hk with hem | ⟨_, hgat⟩
  · exact Or.inl hem
  · exact Or.inr hgat

/-- Transport `M7CongHtInv` monotonically across entry predicates. -/
theorem m7CongHtInv_mono {P Q : BitVec 32 → Prop} {ht_off ht_sz : Nat} {scr : List (BitVec 32)}
    (hPQ : ∀ e, e.toNat < ht_off → P e → Q e)
    (h : M7CongHtInv P ht_off ht_sz scr) : M7CongHtInv Q ht_off ht_sz scr := fun k hk => by
  rcases h k hk with hem | ⟨hlt, hp⟩
  · exact Or.inl hem
  · exact Or.inr ⟨hlt, hPQ _ hlt hp⟩

/-- Effective capacity upper bound `min (clamp16_131072 max_sz) (scratch_cap - ht_off)`. -/
abbrev m7CongHtTargetCap (c : FullCfg) (ht_off : Nat) (max_sz : BitVec 64) : Nat :=
  let lim := if max_sz = 0#64 then m7CongHashMaxSz
    else min m7CongHashMaxSz (max m7CongHashMinSz max_sz.toNat)
  min lim (c.scratch_cap - ht_off)

private theorem m7CongHtTargetCap_le_max (c : FullCfg) (ht_off : Nat) (max_sz : BitVec 64) :
    m7CongHtTargetCap c ht_off max_sz ≤ m7CongHashMaxSz := by
  unfold m7CongHtTargetCap
  refine Nat.le_trans (Nat.min_le_left _ _) ?_
  split
  · exact Nat.le_refl _
  · exact Nat.min_le_left _ _

/-- **#1 (`full_cong_ht_hash_ent_m7`)**: read-only `u64` hash helper over gate record `ent`. -/
abbrev m7CongHtHashEntSpec : Spec [i64, i32, i64] [i64] :=
  fun (h, _ent, _ht_off, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ hv : BitVec 64, Q (hv, ()) m

theorem m7CongHtHashEntSpec_noExit : ∀ a m Q X,
    m7CongHtHashEntSpec a m Q X → m7CongHtHashEntSpec a m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

/-- **#2 (`full_cong_ht_init_m7`)**: bounds-guarded dynamic HT initializer scaling up to
`131072` buckets inside `scratch_buf`, preserving `FullState.core` and `scr[0 ..< ctrl_off + 6)`. -/
abbrev m7CongHtInitSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (h, ctrl_off, ht_off, max_sz, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 64) (scr' : List (BitVec 32)) (rsz' : BitVec 64) (m' : Mem 64),
        let s' : FullState :=
          { s with scratch := { s.scratch with scratch_buf := scr', res_sz := rsz' } }
        scr'.length = c.scratch_cap → s'.LengthsOk c →
        PreservesCoreSlice FullState.core s s' → FullExtScratchPres s s' →
        (ret = 0#64 → scr' = s.scratch.scratch_buf ∧ rsz' = s.scratch.res_sz) →
        (ctrl_off.toNat + 8 ≤ ht_off.toNat → ht_off.toNat + 16 ≤ c.scratch_cap →
          ht_off.toNat ≤ 0x7FFFFFFF → ret ≠ 0#64) →
        (ret ≠ 0#64 →
          M7CongHtCtrlOk c scr' ctrl_off.toNat ht_off.toNat ret.toNat ∧
          ret.toNat ≤ m7CongHtTargetCap c ht_off.toNat max_sz ∧
          m7CongHtTargetCap c ht_off.toNat max_sz < 2 * ret.toNat ∧
          rsz' = 0#64 ∧
          (∀ j < ret.toNat, scr'[ht_off.toNat + j]? = some 0xFFFFFFFF#32) ∧
          (∀ idx < ht_off.toNat, idx ≠ ctrl_off.toNat + 6 → idx ≠ ctrl_off.toNat + 7 →
            scr'[idx]? = s.scratch.scratch_buf[idx]?)) →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

theorem m7CongHtInitSpec_noExit : ∀ a m Q X,
    m7CongHtInitSpec a m Q X → m7CongHtInitSpec a m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

/-- **#3 (`full_cong_ht_grow_m7`)**: doubles `ht_sz` up to `131072` via an in-place tagged
rehash (`0x80000000u`), capping gracefully at `old_sz` without OOM or silent wipe when tight. -/
abbrev m7CongHtGrowSpec : Spec [i64, i64] [i64] :=
  fun (h, ctrl_off, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap → s'.LengthsOk c →
        PreservesCoreSlice FullState.core s s' → FullExtScratchPres s s' →
        (∀ ht_off old_sz,
          M7CongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ht_off old_sz →
          ((m7CongHashMaxSz ≤ old_sz ∨ c.scratch_cap < ht_off + 2 * old_sz) →
            ret.toNat = old_sz ∧ scr' = s.scratch.scratch_buf) ∧
          (old_sz < m7CongHashMaxSz → ht_off + 2 * old_sz ≤ c.scratch_cap →
            ret.toNat = 2 * old_sz ∧
            M7CongHtCtrlOk c scr' ctrl_off.toNat ht_off (2 * old_sz) ∧
            (∀ idx < ht_off, idx ≠ ctrl_off.toNat + 7 →
              scr'[idx]? = s.scratch.scratch_buf[idx]?) ∧
            (∃ j < 2 * old_sz, scr'[ht_off + j]? = some 0xFFFFFFFF#32) ∧
            (∀ v : BitVec 32, v.toNat < ht_off →
              (∃ k0 < old_sz, s.scratch.scratch_buf[ht_off + k0]? = some v) →
              ∃ j < 2 * old_sz, scr'[ht_off + j]? = some v) ∧
            (∀ j < 2 * old_sz,
              scr'[ht_off + j]? = some 0xFFFFFFFF#32 ∨
              ∃ k0 < old_sz, ∃ raw : BitVec 32,
                s.scratch.scratch_buf[ht_off + k0]? = some raw ∧
                raw ≠ 0xFFFFFFFF#32 ∧
                scr'[ht_off + j]? = some (raw &&& 0x7FFFFFFF#32)))) →
        ((∀ ht_off old_sz,
          M7CongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ht_off old_sz → False) →
          scr' = s.scratch.scratch_buf) →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

theorem m7CongHtGrowSpec_noExit : ∀ a m Q X,
    m7CongHtGrowSpec a m Q X → m7CongHtGrowSpec a m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

/-- **#3b (`full_cong_ht_grow_clear_m7`)**: M6.2 `worklist` grow helper: doubles `ctrl[7]` up
to `min 131072 (cap - ht_off)`, clears `scr[ht_off ..< ht_off + new_sz)`, and resets `res_sz = 0`
for canonical `eval_gate` re-population, capping safely at `old_sz` without wipe when tight. -/
abbrev m7CongHtGrowClearSpec : Spec [i64, i64] [i64] :=
  fun (h, ctrl_off, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 64) (scr' : List (BitVec 32)) (rsz' : BitVec 64) (m' : Mem 64),
        let s' : FullState :=
          { s with scratch := { s.scratch with scratch_buf := scr', res_sz := rsz' } }
        scr'.length = c.scratch_cap → s'.LengthsOk c →
        PreservesCoreSlice FullState.core s s' → FullExtScratchPres s s' →
        (∀ ht_off old_sz,
          M7CongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ht_off old_sz →
          ((m7CongHashMaxSz ≤ old_sz ∨ c.scratch_cap < ht_off + 2 * old_sz) →
            ret.toNat = old_sz ∧ scr' = s.scratch.scratch_buf ∧ rsz' = s.scratch.res_sz) ∧
          (old_sz < m7CongHashMaxSz → ht_off + 2 * old_sz ≤ c.scratch_cap →
            ret.toNat = 2 * old_sz ∧
            M7CongHtCtrlOk c scr' ctrl_off.toNat ht_off (2 * old_sz) ∧
            rsz' = 0#64 ∧
            (∀ idx < ht_off, idx ≠ ctrl_off.toNat + 7 →
              scr'[idx]? = s.scratch.scratch_buf[idx]?) ∧
            (∀ j < 2 * old_sz, scr'[ht_off + j]? = some 0xFFFFFFFF#32))) →
        ((∀ ht_off old_sz,
          M7CongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ht_off old_sz → False) →
          scr' = s.scratch.scratch_buf ∧ rsz' = s.scratch.res_sz) →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

theorem m7CongHtGrowClearSpec_noExit : ∀ a m Q X,
    m7CongHtGrowClearSpec a m Q X → m7CongHtGrowClearSpec a m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

end Specs

/-! ## 3. Core Preservation, Slot-Origin, & Control-Layout Helpers -/

section CorePreservation

theorem scr_state_core_pres {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) (scr' : List (BitVec 32)) (hscrl : scr'.length = c.scratch_cap)
    (rsz' : BitVec 64) :
    let s' : FullState :=
      { s with scratch := { s.scratch with scratch_buf := scr', res_sz := rsz' } }
    s'.LengthsOk c ∧ PreservesCoreSlice FullState.core s s' ∧ FullExtScratchPres s s' :=
  ⟨⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hscrl }⟩, rfl, ⟨rfl, rfl⟩⟩

private theorem m7CongHtCtrlOk_grow {c : FullCfg} {scr1 scr2 : List (BitVec 32)}
    {ctrl_off ht_off k : Nat} (hk : k < 13)
    (hok : M7CongHtCtrlOk c scr1 ctrl_off ht_off (16 * 2 ^ k))
    (hl2 : scr2.length = c.scratch_cap) (hfit : ht_off + 2 * (16 * 2 ^ k) ≤ c.scratch_cap)
    (h6 : scr2[ctrl_off + 6]? = some (BitVec.ofNat 32 ht_off))
    (h7 : scr2[ctrl_off + 7]? = some (BitVec.ofNat 32 (2 * (16 * 2 ^ k)))) :
    M7CongHtCtrlOk c scr2 ctrl_off ht_off (2 * (16 * 2 ^ k)) := by
  refine ⟨hl2, hok.2.1, hfit, hok.2.2.2.1, ⟨k + 1, by omega, ?_⟩, h6, h7⟩
  rw [Nat.pow_succ]; omega

theorem m7CongHtCtrlOk_match_reads {c : FullCfg} {scr : List (BitVec 32)}
    {ctrl_off : BitVec 64} {ht_off old_sz : BitVec 64}
    (hco : ctrl_off.toNat + 8 ≤ c.scratch_cap) (hscrl : scr.length = c.scratch_cap)
    (hho : ht_off = (scr[ctrl_off.toNat + 6]'(by omega)).setWidth 64)
    (hsz : old_sz = (scr[ctrl_off.toNat + 7]'(by omega)).setWidth 64)
    {ho os : Nat} (hok : M7CongHtCtrlOk c scr ctrl_off.toNat ho os) :
    ho = ht_off.toNat ∧ os = old_sz.toNat := by
  have hsc := c.hscr; unfold dimacsBound at hsc
  have ho_lt : ho < 2 ^ 32 := by have := hok.2.2.2.1; omega
  have os_lt : os < 2 ^ 32 := by have := hok.2.2.1; omega
  obtain ⟨_, _, _, _, _, h6, h7⟩ := hok
  rw [List.getElem?_eq_getElem (by omega), Option.some.injEq] at h6 h7
  have e1 : ht_off.toNat = ho := by
    rw [hho, bv64_zext32_toNat, h6, bv32_ofNat_toNat_lt ho_lt]
  have e2 : old_sz.toNat = os := by
    rw [hsz, bv64_zext32_toNat, h7, bv32_ofNat_toNat_lt os_lt]
  exact ⟨e1.symm, e2.symm⟩

theorem m7CongHtCtrlOk_from_reads {c : FullCfg} {scr : List (BitVec 32)}
    {ctrl_off : BitVec 64} {ht_off old_sz : BitVec 64}
    (hscrl : scr.length = c.scratch_cap)
    (hco : ctrl_off.toNat + 8 ≤ c.scratch_cap)
    (hho : ht_off = ((scr[ctrl_off.toNat + 6]'(by omega)).setWidth 64))
    (hsz : old_sz = ((scr[ctrl_off.toNat + 7]'(by omega)).setWidth 64))
    (h1 : ctrl_off.toNat + 8 ≤ ht_off.toNat) (h2 : ht_off.toNat < c.scratch_cap)
    (h3 : ht_off.toNat ≤ 0x7FFFFFFF) (h4 : 16 ≤ old_sz.toNat)
    (h5 : (old_sz &&& (old_sz - 1#64)) = 0#64)
    (h6 : old_sz.toNat ≤ c.scratch_cap - ht_off.toNat) (hmax : old_sz.toNat ≤ m7CongHashMaxSz) :
    M7CongHtCtrlOk c scr ctrl_off.toNat ht_off.toNat old_sz.toNat := by
  have hsc := c.hscr; unfold dimacsBound at hsc
  have hand_sz : (BitVec.ofNat 64 old_sz.toNat &&& (BitVec.ofNat 64 old_sz.toNat - 1#64)) =
      0#64 := by
    simpa [BitVec.ofNat_toNat] using h5
  obtain ⟨k, hk, heq⟩ := pow2_16_of_and_zero h4 hmax hand_sz
  have he6 : scr[ctrl_off.toNat + 6]? = some (BitVec.ofNat 32 ht_off.toNat) := by
    rw [List.getElem?_eq_getElem (by omega)]; congr 1
    apply BitVec.eq_of_toNat_eq
    rw [hho, bv64_zext32_toNat, bv32_ofNat_toNat_lt (by omega)]
  have he7 : scr[ctrl_off.toNat + 7]? = some (BitVec.ofNat 32 old_sz.toNat) := by
    rw [List.getElem?_eq_getElem (by omega)]; congr 1
    apply BitVec.eq_of_toNat_eq
    rw [hsz, bv64_zext32_toNat, bv32_ofNat_toNat_lt (by omega)]
  exact ⟨hscrl, h1, by omega, h3, ⟨k, hk, heq⟩, he6, he7⟩

/-- Transport `M7CongHtInv` across a `grow_m7` or `insert_m7` transition. -/
theorem m7_slots_grow_inv {ValidEnt : BitVec 32 → Prop} {scr0 scr1 : List (BitVec 32)}
    {ht_off old_sz new_sz : Nat} (hle : ht_off ≤ 0x7FFFFFFF)
    (hinv : M7CongHtInv ValidEnt ht_off old_sz scr0)
    (horig : ∀ j < new_sz, scr1[ht_off + j]? = some 0xFFFFFFFF#32 ∨
      ∃ k0 < old_sz, ∃ raw : BitVec 32,
        scr0[ht_off + k0]? = some raw ∧ raw ≠ 0xFFFFFFFF#32 ∧
        (scr1[ht_off + j]? = some raw ∨
          scr1[ht_off + j]? = some (raw &&& 0x7FFFFFFF#32))) :
    M7CongHtInv ValidEnt ht_off new_sz scr1 := by
  intro j hj
  rcases horig j hj with hem | ⟨k0, hk0, raw, hget, hne, heq⟩
  · left; rw [hem, Option.getD_some]
  · rcases hinv k0 hk0 with hk0_em | ⟨hk0_lt, hk0_val⟩
    · rw [hget, Option.getD_some] at hk0_em; exact absurd hk0_em hne
    · have hget' : raw = scr0[ht_off + k0]?.getD 0xFFFFFFFF#32 := by rw [hget, Option.getD_some]
      rw [← hget'] at hk0_lt hk0_val
      have hmask : (raw &&& 0x7FFFFFFF#32) = raw := bv32_and7fff_of_lt (by omega)
      rcases heq with heq | heq
      · right; rw [heq, Option.getD_some]; exact ⟨hk0_lt, hk0_val⟩
      · rw [hmask] at heq; right; rw [heq, Option.getD_some]; exact ⟨hk0_lt, hk0_val⟩

/-- Slot invariant during in-place tagged rehash (`grow_m7` Step B). -/
private def SlotMigOk (c : FullCfg) (scr0 scr : List (BitVec 32))
    (ht_off old_sz new_sz : Nat) : Prop :=
  scr.length = c.scratch_cap ∧
  (∀ idx < ht_off, scr[idx]? = scr0[idx]?) ∧
  (∀ j < new_sz,
    scr[ht_off + j]? = some 0xFFFFFFFF#32 ∨
    ∃ k0 < old_sz, ∃ r0 : BitVec 32,
      scr0[ht_off + k0]? = some r0 ∧ r0 ≠ 0xFFFFFFFF#32 ∧
      (scr[ht_off + j]? = some r0 ∨ scr[ht_off + j]? = some (r0 ||| 0x80000000#32)))

/-- Entry-in-hand invariant during in-place tagged rehash (`grow_m7` Step B). -/
private def CurMigOk (scr0 : List (BitVec 32)) (ht_off old_sz : Nat) (cur : BitVec 32) : Prop :=
  cur = 0xFFFFFFFF#32 ∨
  (cur.toNat < ht_off ∧ ∃ k0 < old_sz, scr0[ht_off + k0]? = some cur ∧ cur ≠ 0xFFFFFFFF#32)

private theorem slotMigOk_set_empty {c : FullCfg} {scr0 scr : List (BitVec 32)}
    {ht_off old_sz new_sz pos : Nat} (hs : SlotMigOk c scr0 scr ht_off old_sz new_sz)
    (hpos : ht_off + pos < scr.length) :
    SlotMigOk c scr0 (scr.set (ht_off + pos) 0xFFFFFFFF#32) ht_off old_sz new_sz := by
  refine ⟨by rw [List.length_set]; exact hs.1, fun idx hidx => ?_, fun j hj => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hs.2.1 idx hidx
  · by_cases hjp : j = pos
    · subst hjp; left; rw [List.getElem?_set_self hpos]
    · rw [List.getElem?_set_ne (by omega)]; exact hs.2.2 j hj

private theorem slotMigOk_set_cur {c : FullCfg} {scr0 scr : List (BitVec 32)}
    {ht_off old_sz new_sz pos : Nat} {cur : BitVec 32}
    (hs : SlotMigOk c scr0 scr ht_off old_sz new_sz)
    (hcur : CurMigOk scr0 ht_off old_sz cur) (hne : cur ≠ 0xFFFFFFFF#32)
    (hpos : ht_off + pos < scr.length) :
    SlotMigOk c scr0 (scr.set (ht_off + pos) (cur ||| 0x80000000#32)) ht_off old_sz new_sz := by
  rcases hcur with rfl | ⟨hlt, k0, hk0, hget, hne'⟩
  · exact absurd rfl hne
  · refine ⟨by rw [List.length_set]; exact hs.1, fun idx hidx => ?_, fun j hj => ?_⟩
    · rw [List.getElem?_set_ne (by omega)]; exact hs.2.1 idx hidx
    · by_cases hjp : j = pos
      · subst hjp; right; refine ⟨k0, hk0, cur, hget, hne', Or.inr ?_⟩
        rw [List.getElem?_set_self hpos]
      · rw [List.getElem?_set_ne (by omega)]; exact hs.2.2 j hj

private theorem curMigOk_of_slot {c : FullCfg} {scr0 scr : List (BitVec 32)}
    {ht_off old_sz new_sz pos : Nat} {v : BitVec 32}
    (hs : SlotMigOk c scr0 scr ht_off old_sz new_sz) (hpos : pos < new_sz)
    (hv_get : scr[ht_off + pos]? = some v) (hv_ne : v ≠ 0xFFFFFFFF#32)
    (hv_msb : (v &&& 0x80000000#32) = 0#32) (hv_lt : v.toNat < ht_off) :
    CurMigOk scr0 ht_off old_sz v := by
  rcases hs.2.2 pos hpos with hem | ⟨k0, hk0, r0, hr0_get, hr0_ne, hr0_eq⟩
  · rw [hv_get] at hem; exact absurd (Option.some.inj hem) hv_ne
  · rcases hr0_eq with h1 | h1
    · rw [hv_get, Option.some.injEq] at h1; subst h1
      exact Or.inr ⟨hv_lt, k0, hk0, hr0_get, hr0_ne⟩
    · rw [hv_get, Option.some.injEq] at h1
      exact absurd h1 (bv32_or8000_ne_of_msb_zero hv_msb)

private abbrev htEmptyPred (x : BitVec 32) : Bool := decide (x = 0xFFFFFFFF#32)

private abbrev htUnmigPred (x : BitVec 32) : Bool :=
  decide (x ≠ 0xFFFFFFFF#32 ∧ (x &&& 0x80000000#32) = 0#32)

private theorem htOr8000_ne_ff {v : BitVec 32} (hlt : v.toNat < 0x7FFFFFFF) :
    v ||| 0x80000000#32 ≠ 0xFFFFFFFF#32 := by
  intro h
  have h1 := congrArg (fun x => (x &&& 0x7FFFFFFF#32).toNat) h
  rw [bv32_or8000_and7fff, bv32_and7fff_of_lt (by omega)] at h1
  have h2 : (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat = 0x7FFFFFFF := by decide
  rw [h2] at h1; omega

private theorem htOr8000_msb_ne_zero (v : BitVec 32) :
    (v ||| 0x80000000#32) &&& 0x80000000#32 ≠ 0#32 := by
  intro h
  have hb := congrArg (fun x => x.getLsbD 31) h
  simp at hb

private def SlotKeepOk (scr0 scr : List (BitVec 32)) (ht_off old_sz new_sz : Nat)
    (cur : BitVec 32) : Prop :=
  old_sz + (if cur = 0xFFFFFFFF#32 then 0 else 1) ≤
    (List.range new_sz).countP (fun k => htEmptyPred (scr[ht_off + k]?.getD 0xFFFFFFFF#32)) ∧
  (List.range new_sz).countP (fun k => htUnmigPred (scr[ht_off + k]?.getD 0xFFFFFFFF#32)) +
    (if cur = 0xFFFFFFFF#32 then 0 else 1) ≤ old_sz ∧
  (∀ v : BitVec 32, v.toNat < ht_off →
    (∃ k0 < old_sz, scr0[ht_off + k0]? = some v) →
    cur = v ∨ ∃ j < new_sz,
      scr[ht_off + j]? = some v ∨ scr[ht_off + j]? = some (v ||| 0x80000000#32))

private theorem slotKeepOk_init {scr0 scrk : List (BitVec 32)} {ht_off old_sz : Nat}
    (hold : ∀ j < old_sz, scrk[ht_off + j]? = scr0[ht_off + j]?)
    (hclr : ∀ j, old_sz ≤ j → j < 2 * old_sz → scrk[ht_off + j]? = some 0xFFFFFFFF#32) :
    SlotKeepOk scr0 scrk ht_off old_sz (2 * old_sz) 0xFFFFFFFF#32 := by
  have htwo : 2 * old_sz = old_sz + old_sz := by omega
  refine ⟨?_, ?_, fun v _ ⟨k0, hk0, hget⟩ => Or.inr ⟨k0, by omega, Or.inl (by
      rw [hold k0 hk0, hget])⟩⟩
  · rw [htwo, range_countP_add]
    have hhi : (List.range old_sz).countP
        (fun k => htEmptyPred (scrk[ht_off + (old_sz + k)]?.getD 0xFFFFFFFF#32)) = old_sz := by
      have h1 : (List.range old_sz).countP
          (fun k => htEmptyPred (scrk[ht_off + (old_sz + k)]?.getD 0xFFFFFFFF#32)) =
          (List.range old_sz).countP (fun _ => true) :=
        range_countP_ext fun k hk => by
          rw [hclr (old_sz + k) (by omega) (by omega), Option.getD_some]; decide
      rw [h1, List.countP_true, List.length_range]
    simp only [↓reduceIte, Nat.add_zero]
    rw [hhi]; omega
  · rw [htwo, range_countP_add]
    have hlo : (List.range old_sz).countP
        (fun k => htUnmigPred (scrk[ht_off + k]?.getD 0xFFFFFFFF#32)) ≤ old_sz :=
      range_countP_le _ _
    have hhi : (List.range old_sz).countP
        (fun k => htUnmigPred (scrk[ht_off + (old_sz + k)]?.getD 0xFFFFFFFF#32)) = 0 := by
      have h1 : (List.range old_sz).countP
          (fun k => htUnmigPred (scrk[ht_off + (old_sz + k)]?.getD 0xFFFFFFFF#32)) =
          (List.range old_sz).countP (fun _ => false) :=
        range_countP_ext fun k hk => by
          rw [hclr (old_sz + k) (by omega) (by omega), Option.getD_some]; decide
      have hzero : (List.range old_sz).countP (fun _ => false) = 0 := by simp
      rw [h1, hzero]
    simp only [↓reduceIte, Nat.add_zero]
    omega

private theorem slotKeepOk_set_empty {scr0 scr : List (BitVec 32)}
    {ht_off old_sz new_sz pos : Nat} {raw : BitVec 32}
    (hs : SlotKeepOk scr0 scr ht_off old_sz new_sz 0xFFFFFFFF#32)
    (hle : ht_off ≤ 0x7FFFFFFF) (hpos : pos < new_sz) (harr : ht_off + pos < scr.length)
    (hget : scr[ht_off + pos]? = some raw) (hne : raw ≠ 0xFFFFFFFF#32)
    (hmsb : (raw &&& 0x80000000#32) = 0#32) :
    SlotKeepOk scr0 (scr.set (ht_off + pos) 0xFFFFFFFF#32) ht_off old_sz new_sz raw := by
  have he_set := range_countP_set (w := 0xFFFFFFFF#32) htEmptyPred hpos harr
  have hu_set := range_countP_set (w := 0xFFFFFFFF#32) htUnmigPred hpos harr
  rw [hget, Option.getD_some] at he_set hu_set
  have hpe_raw : htEmptyPred raw = false := decide_eq_false hne
  have hpe_ff : htEmptyPred 0xFFFFFFFF#32 = true := decide_eq_true rfl
  have hpu_raw : htUnmigPred raw = true := decide_eq_true ⟨hne, hmsb⟩
  have hpu_ff : htUnmigPred 0xFFFFFFFF#32 = false := by decide
  rw [hpe_raw, hpe_ff] at he_set
  rw [hpu_raw, hpu_ff] at hu_set
  simp only [Bool.false_eq_true, ↓reduceIte] at he_set hu_set
  obtain ⟨he0, hu0, hv0⟩ := hs
  simp only [↓reduceIte, Nat.add_zero] at he0 hu0
  refine ⟨?_, ?_, fun v hv_lt hex => ?_⟩
  · rw [ite_eq_right hne]; omega
  · rw [ite_eq_right hne]; omega
  · by_cases hvr : v = raw
    · exact Or.inl hvr.symm
    · rcases hv0 v hv_lt hex with hcur | ⟨j, hj, hslot⟩
      · have hff : (0xFFFFFFFF#32 : BitVec 32).toNat = 0xFFFFFFFF := by decide
        rw [← hcur, hff] at hv_lt; omega
      · have hjne : j ≠ pos := by
          intro hjp; subst hjp
          rcases hslot with h1 | h1
          · rw [hget, Option.some.injEq] at h1; exact hvr h1.symm
          · rw [hget, Option.some.injEq] at h1
            exact absurd h1 (bv32_or8000_ne_of_msb_zero hmsb)
        refine Or.inr ⟨j, hj, ?_⟩
        rw [List.getElem?_set_ne (by omega)]
        exact hslot

private theorem slotKeepOk_set_mig_empty {scr0 scr : List (BitVec 32)}
    {ht_off old_sz new_sz pos : Nat} {cur : BitVec 32}
    (hs : SlotKeepOk scr0 scr ht_off old_sz new_sz cur)
    (hne : cur ≠ 0xFFFFFFFF#32) (hlt : cur.toNat < ht_off) (hle : ht_off ≤ 0x7FFFFFFF)
    (hpos : pos < new_sz) (harr : ht_off + pos < scr.length)
    (hget : scr[ht_off + pos]? = some 0xFFFFFFFF#32) :
    SlotKeepOk scr0 (scr.set (ht_off + pos) (cur ||| 0x80000000#32))
      ht_off old_sz new_sz 0xFFFFFFFF#32 := by
  have hcur_ne : cur ||| 0x80000000#32 ≠ 0xFFFFFFFF#32 := htOr8000_ne_ff (by omega)
  have he_set := range_countP_set (w := cur ||| 0x80000000#32) htEmptyPred hpos harr
  have hu_set := range_countP_set (w := cur ||| 0x80000000#32) htUnmigPred hpos harr
  rw [hget, Option.getD_some] at he_set hu_set
  have hpe_ff : htEmptyPred 0xFFFFFFFF#32 = true := decide_eq_true rfl
  have hpe_cur : htEmptyPred (cur ||| 0x80000000#32) = false := decide_eq_false hcur_ne
  have hpu_ff : htUnmigPred 0xFFFFFFFF#32 = false := by decide
  have hpu_cur : htUnmigPred (cur ||| 0x80000000#32) = false :=
    decide_eq_false (fun ⟨_, h⟩ => htOr8000_msb_ne_zero cur h)
  rw [hpe_ff, hpe_cur] at he_set
  rw [hpu_ff, hpu_cur] at hu_set
  simp only [Bool.false_eq_true, ↓reduceIte] at he_set hu_set
  obtain ⟨he0, hu0, hv0⟩ := hs
  rw [ite_eq_right hne] at he0 hu0
  refine ⟨?_, ?_, fun v hv_lt hex => ?_⟩
  · simp only [↓reduceIte, Nat.add_zero]; omega
  · simp only [↓reduceIte, Nat.add_zero]; omega
  · by_cases hvc : v = cur
    · subst hvc; exact Or.inr ⟨pos, hpos, Or.inr (List.getElem?_set_self harr)⟩
    · rcases hv0 v hv_lt hex with hcur | ⟨j, hj, hslot⟩
      · exact absurd hcur.symm hvc
      · have hv_ne_ff : v ≠ 0xFFFFFFFF#32 := by
          have hff : (0xFFFFFFFF#32 : BitVec 32).toNat = 0xFFFFFFFF := by decide
          intro h; rw [h, hff] at hv_lt; omega
        have hvo_ne_ff : v ||| 0x80000000#32 ≠ 0xFFFFFFFF#32 := htOr8000_ne_ff (by omega)
        have hjne : j ≠ pos := by
          intro hjp; subst hjp
          rcases hslot with h1 | h1
          · rw [hget, Option.some.injEq] at h1; exact hv_ne_ff h1.symm
          · rw [hget, Option.some.injEq] at h1; exact hvo_ne_ff h1.symm
        refine Or.inr ⟨j, hj, ?_⟩
        rw [List.getElem?_set_ne (by omega)]
        exact hslot

private theorem slotKeepOk_set_mig_swap {scr0 scr : List (BitVec 32)}
    {ht_off old_sz new_sz pos : Nat} {cur dst next_cur : BitVec 32}
    (hs : SlotKeepOk scr0 scr ht_off old_sz new_sz cur)
    (hne : cur ≠ 0xFFFFFFFF#32) (hlt : cur.toNat < ht_off) (hle : ht_off ≤ 0x7FFFFFFF)
    (hpos : pos < new_sz) (harr : ht_off + pos < scr.length)
    (hget : scr[ht_off + pos]? = some dst) (hdst_ne : dst ≠ 0xFFFFFFFF#32)
    (hdst_msb : (dst &&& 0x80000000#32) = 0#32)
    (hnext : (dst.toNat < ht_off ∧ next_cur = dst) ∨
      (ht_off ≤ dst.toNat ∧ next_cur = 0xFFFFFFFF#32)) :
    SlotKeepOk scr0 (scr.set (ht_off + pos) (cur ||| 0x80000000#32))
      ht_off old_sz new_sz next_cur := by
  have hcur_ne : cur ||| 0x80000000#32 ≠ 0xFFFFFFFF#32 := htOr8000_ne_ff (by omega)
  have he_set := range_countP_set (w := cur ||| 0x80000000#32) htEmptyPred hpos harr
  have hu_set := range_countP_set (w := cur ||| 0x80000000#32) htUnmigPred hpos harr
  rw [hget, Option.getD_some] at he_set hu_set
  have hpe_dst : htEmptyPred dst = false := decide_eq_false hdst_ne
  have hpe_cur : htEmptyPred (cur ||| 0x80000000#32) = false := decide_eq_false hcur_ne
  have hpu_dst : htUnmigPred dst = true := decide_eq_true ⟨hdst_ne, hdst_msb⟩
  have hpu_cur : htUnmigPred (cur ||| 0x80000000#32) = false :=
    decide_eq_false (fun ⟨_, h⟩ => htOr8000_msb_ne_zero cur h)
  rw [hpe_dst, hpe_cur] at he_set
  rw [hpu_dst, hpu_cur] at hu_set
  simp only [Bool.false_eq_true, ↓reduceIte] at he_set hu_set
  obtain ⟨he0, hu0, hv0⟩ := hs
  rw [ite_eq_right hne] at he0 hu0
  refine ⟨?_, ?_, fun v hv_lt hex => ?_⟩
  · rcases hnext with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · rw [ite_eq_right hdst_ne]; omega
    · simp only [↓reduceIte, Nat.add_zero]; omega
  · rcases hnext with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · rw [ite_eq_right hdst_ne]; omega
    · simp only [↓reduceIte, Nat.add_zero]; omega
  · by_cases hvc : v = cur
    · subst hvc; exact Or.inr ⟨pos, hpos, Or.inr (List.getElem?_set_self harr)⟩
    · by_cases hvd : v = dst
      · subst hvd
        rcases hnext with ⟨_, rfl⟩ | ⟨hle_d, _⟩
        · exact Or.inl rfl
        · omega
      · rcases hv0 v hv_lt hex with hcur | ⟨j, hj, hslot⟩
        · exact absurd hcur.symm hvc
        · have hjne : j ≠ pos := by
            intro hjp; subst hjp
            rcases hslot with h1 | h1
            · rw [hget, Option.some.injEq] at h1; exact hvd h1.symm
            · rw [hget, Option.some.injEq] at h1
              exact absurd h1 (bv32_or8000_ne_of_msb_zero hdst_msb)
          refine Or.inr ⟨j, hj, ?_⟩
          rw [List.getElem?_set_ne (by omega)]
          exact hslot

private theorem slotKeepOk_empty_exists {scr0 scr : List (BitVec 32)}
    {ht_off old_sz new_sz : Nat} {cur : BitVec 32}
    (hs : SlotKeepOk scr0 scr ht_off old_sz new_sz cur) (hpos : 0 < old_sz)
    (hfit : ht_off + new_sz ≤ scr.length) :
    ∃ k < new_sz, scr[ht_off + k]? = some 0xFFFFFFFF#32 := by
  have he := hs.1
  have hgt : 0 < (List.range new_sz).countP
      (fun k => htEmptyPred (scr[ht_off + k]?.getD 0xFFFFFFFF#32)) := by omega
  obtain ⟨k, hk, hpred⟩ := range_countP_pos_exists hgt
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hpred
  refine ⟨k, hk, ?_⟩
  rw [List.getElem?_eq_getElem (by omega), decide_eq_true_eq.mp hpred]

end CorePreservation

/-! ## 4. `Func.wp` Proofs `#1–#5` -/

section WpProofs

open scoped FullArenaTactics

local macro "m7_omega" : tactic =>
  `(tactic| (
    try simp only [bv64_zext32_toNat,
      show BitVec.toNat (0 : BitVec 64) = 0 from rfl,
      show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
      show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
      show BitVec.toNat (6 : BitVec 64) = 6 from rfl,
      show BitVec.toNat (7 : BitVec 64) = 7 from rfl,
      show BitVec.toNat (8 : BitVec 64) = 8 from rfl,
      show BitVec.toNat (16 : BitVec 64) = 16 from rfl,
      show BitVec.toNat (31 : BitVec 64) = 31 from rfl,
      show BitVec.toNat (131072 : BitVec 64) = 131072 from rfl,
      show BitVec.toNat (2147483647 : BitVec 64) = 2147483647 from rfl] at *
    omega))

/-- **#1 (`full_cong_ht_hash_ent_m7_wp`)**: total safety and read-only memory preservation. -/
theorem full_cong_ht_hash_ent_m7_wp (Γ : Env) :
    ∀ a m Q X, m7CongHtHashEntSpec a m Q X →
      Func.wp Γ full_cong_ht_hash_ent_m7_body a m Q X := by
  rintro ⟨h, ent, ht_off, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hlen, hm0, hQ⟩
  have hsc := c.hscr; unfold dimacsBound at hsc
  have hscrl := hlen.scratch_ok.scratch_buf_len
  have hent_lt : ent.toNat < 2 ^ 32 := ent.isLt
  unfold Func.wp full_cong_ht_hash_ent_m7_body
  c0_hsplit
  · c0_hsteps; exact hQ 0#64
  · have he2_le : ent.toNat + 2 ≤ ht_off.toNat := by
      have h2 := bv64_zext32_add_ofNat ent 2 (by decide)
      m7_omega
    clear hc; c0_hsplit
    · c0_hsteps; exact hQ 0#64
    · have hht_le : ht_off.toNat ≤ c.scratch_cap := by m7_omega
      have he1_arr : (ent.setWidth 64 + 1#64).toNat < s.scratch.scratch_buf.length := by
        rw [bv64_zext32_add_ofNat ent 1 (by decide)]; m7_omega
      clear hc; c0_hsplit
      · c0_hsteps; exact hQ 0#64
      · let mw := s.scratch.scratch_buf[ent.toNat + 1]'(by omega)
        let harity : BitVec 64 := (mw &&& 0xFF#32).setWidth 64
        have hm_congr : s.scratch.scratch_buf[(BitVec.toNat ent +
            BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
            change (ent.toNat + 1) % 2 ^ 64 < s.scratch.scratch_buf.length
            rw [Nat.mod_eq_of_lt (by omega)]; omega) =
            mw :=
          scr_idx_zext32_add1 (by omega) _
        have har_le31 : harity.toNat ≤ 31 := by
          rw [hm_congr] at hc
          have hhc : ¬ (31 : Nat) < (mw &&& 0xFF#32).toNat := hc
          dsimp only [harity]; rw [bv64_zext32_toNat]; exact Nat.not_lt.mp hhc
        clear hc; c0_hsplit
        · c0_hsteps; exact hQ 0#64
        · have hbound : ent.toNat + 2 + harity.toNat ≤ ht_off.toNat := by
            rw [hm_congr] at hc
            have hmod : (ent.toNat + BitVec.toNat (2 : BitVec 64) +
                (mw &&& (255 : BitVec 32)).toNat) % 2 ^ 64 =
                ent.toNat + 2 + (mw &&& 0xFF#32).toNat :=
              Nat.mod_eq_of_lt (by
                have h2n : BitVec.toNat (2 : BitVec 64) = 2 := rfl
                have h255 : (mw &&& (255 : BitVec 32)) = (mw &&& 0xFF#32) := rfl
                have : (mw &&& 0xFF#32).toNat = harity.toNat := (bv64_zext32_toNat _).symm
                rw [h255]; omega)
            rw [hmod] at hc
            dsimp only [harity] at *; m7_omega
          clear hc; c0_hsteps_nogrp
          refine wp_loop_inv
            (fun (_, i, ()) mi => mi = m0 ∧ i.toNat ≤ harity.toNat)
            (fun (_, i, ()) _ => harity.toNat - i.toNat)
            (fun J hJ => by c0_hsteps; exact hJ (_, 0#64, ()) m0 ⟨rfl, Nat.zero_le _⟩)
            (fun J ⟨hv, i, ⟨⟩⟩ mi ⟨hmi, hi_le⟩ ih => ?_)
          subst mi
          c0_hsplit
          · have hi_lt : i.toNat < harity.toNat := by
              rw [hm_congr] at hc; dsimp only [harity]; rw [bv64_zext32_toNat]; exact hc
            have hei_n : (ent.setWidth 64 + 2#64 + i).toNat = ent.toNat + 2 + i.toNat := by
              have h12 := bv64_zext32_add_ofNat ent 2 (by decide)
              rw [bv64_add_toNat (by rw [h12]; omega), h12]
            have hei_arr : (ent.setWidth 64 + 2#64 + i).toNat < s.scratch.scratch_buf.length := by
              rw [hei_n]; omega
            have hi1_n : (i + 1#64).toNat = i.toNat + 1 := bv64_add1_lt hi_lt (by omega)
            c0_hsteps
            exact ih (_, i + 1#64, ()) m0 (by dsimp only; omega) ⟨rfl, by omega⟩
          · c0_hsteps; exact hQ hv

/-- **#2 (`full_cong_ht_init_m7_wp`)**: bounds-guarded dynamic HT initializer up to `131072`. -/
theorem full_cong_ht_init_m7_wp (Γ : Env) :
    ∀ a m Q X, m7CongHtInitSpec a m Q X →
      Func.wp Γ full_cong_ht_init_m7_body a m Q X := by
  rintro ⟨h, ctrl_off, ht_off, max_sz, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hlen, hm0, hQ⟩
  have hsc := c.hscr; unfold dimacsBound at hsc
  have hscrl := hlen.scratch_ok.scratch_buf_len
  have hret0 : ¬ (ctrl_off.toNat + 8 ≤ ht_off.toNat ∧ ht_off.toNat + 16 ≤ c.scratch_cap ∧
      ht_off.toNat ≤ 0x7FFFFFFF) → Q (0#64, ()) m0 := fun hnot =>
    hQ 0#64 s.scratch.scratch_buf s.scratch.res_sz m0 hscrl hlen rfl ⟨rfl, rfl⟩
      (fun _ => ⟨rfl, rfl⟩) (fun h1 h2 h3 => False.elim (hnot ⟨h1, h2, h3⟩))
      (fun hne => absurd rfl hne) hm0
  unfold Func.wp full_cong_ht_init_m7_body
  c0_hsplit
  · c0_hsteps; exact hret0 fun ⟨h1, h2, _⟩ => by m7_omega
  · have hco_le : ctrl_off.toNat ≤ c.scratch_cap := by m7_omega
    clear hc; c0_hsplit
    · c0_hsteps; exact hret0 fun ⟨h1, h2, _⟩ => by
        have := ctrl_off.isLt; m7_omega
    · have hco8 : ctrl_off.toNat + 8 ≤ c.scratch_cap := by
        have := ctrl_off.isLt; m7_omega
      clear hc; c0_hsplit
      · c0_hsteps; exact hret0 fun ⟨h1, _, _⟩ => by m7_omega
      · have hco8_ht : ctrl_off.toNat + 8 ≤ ht_off.toNat := by m7_omega
        clear hc; c0_hsplit
        · c0_hsteps; exact hret0 fun ⟨_, h2, _⟩ => by m7_omega
        · have hht_lt_cap : ht_off.toNat < c.scratch_cap := by m7_omega
          clear hc; c0_hsplit
          · c0_hsteps; exact hret0 fun ⟨_, _, h3⟩ => by m7_omega
          · have hht_le7 : ht_off.toNat ≤ 0x7FFFFFFF := by m7_omega
            clear hc; c0_hsplit
            · c0_hsteps; exact hret0 fun ⟨_, h2, _⟩ => by
                have := ht_off.isLt; m7_omega
            · have hav16 : 16 ≤ c.scratch_cap - ht_off.toNat := by
                have := ht_off.isLt; m7_omega
              clear hc; c0_hsteps_nogrp
              refine wp_join_group (ts := [i64])
                (fun (lim0, ()) ml0 => ml0 = m0 ∧
                  lim0.toNat = (if max_sz = 0#64 then 131072 else max_sz.toNat))
                ?_ ?_
              · rintro _ ⟨lim0, ⟨⟩⟩ ml0 ⟨hml0, hlim0⟩; subst ml0
                c0_hsteps_nogrp
                refine wp_join_group (ts := [i64])
                  (fun (lim1, ()) ml1 => ml1 = m0 ∧
                    lim1.toNat = min 131072 (if max_sz = 0#64 then 131072 else max_sz.toNat))
                  ?_ ?_
                · rintro _ ⟨lim1, ⟨⟩⟩ ml1 ⟨hml1, hlim1⟩; subst ml1
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [i64])
                    (fun (lim2, ()) ml2 => ml2 = m0 ∧
                      lim2.toNat = min 131072
                        (max 16 (if max_sz = 0#64 then 131072 else max_sz.toNat)))
                    ?_ ?_
                  · rintro _ ⟨lim2, ⟨⟩⟩ ml2 ⟨hml2, hlim2⟩; subst ml2
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := [i64])
                      (fun (top, ()) mt => mt = m0 ∧ 16 ≤ top.toNat ∧
                        top.toNat = m7CongHtTargetCap c ht_off.toNat max_sz)
                      ?_ ?_
                    · rintro _ ⟨top, ⟨⟩⟩ mt ⟨hmt, htop16, htop_eq⟩; subst mt
                      have htop_le : top.toNat ≤ 131072 := by
                        rw [htop_eq]; exact m7CongHtTargetCap_le_max _ _ _
                      c0_hsteps_nogrp
                      refine wp_loop_inv
                        (fun (sz, ()) ms => ms = m0 ∧ ∃ k ≤ 13,
                          sz.toNat = 16 * 2 ^ k ∧ sz.toNat ≤ top.toNat)
                        (fun (sz, ()) _ => 131072 - sz.toNat)
                        (fun J hJ => by
                          c0_hsteps; exact hJ (16#64, ()) m0 ⟨rfl, 0, by decide, rfl, htop16⟩)
                        (fun J ⟨sz, ⟨⟩⟩ ms ⟨hms, k, hk_le, hsz_pow, hsz_top⟩ ih => ?_)
                      subst ms
                      have hsz_le_max : sz.toNat ≤ 131072 := by omega
                      c0_hsplit
                      · have h2le : 2 * sz.toNat ≤ top.toNat := by m7_omega
                        have hk_lt : k < 13 := by
                          rcases Nat.lt_or_ge k 13 with hlt | hge
                          · exact hlt
                          · obtain rfl : k = 13 := by omega
                            have h13 : 16 * 2 ^ 13 = 131072 := by decide
                            omega
                        have hshl : (sz <<< (1#32 : BitVec 32).signExtend 64).toNat =
                            2 * sz.toNat := bv64_shl1_toNat (by omega)
                        c0_hsteps
                        refine ih (sz <<< (1#32 : BitVec 32).signExtend 64, ()) m0
                          (by have h2p := Nat.two_pow_pos k; dsimp only; rw [hshl]; omega)
                          ⟨rfl, k + 1, by omega, ?_, by rw [hshl]; exact h2le⟩
                        rw [hshl, hsz_pow, Nat.pow_succ]; omega
                      · have htop_lt2 : top.toNat < 2 * sz.toNat := by m7_omega
                        clear hc
                        have hsz_lt_cap : ht_off.toNat + sz.toNat ≤ c.scratch_cap := by
                          rw [htop_eq] at hsz_top
                          have : m7CongHtTargetCap c ht_off.toNat max_sz ≤
                              c.scratch_cap - ht_off.toNat := Nat.min_le_right _ _
                          omega
                        have h6n : (ctrl_off + (6 : BitVec 64)).toNat = ctrl_off.toNat + 6 :=
                          bv64_add_ofNat_toNat 6 (by decide) (by omega)
                        have h7n : (ctrl_off + (7 : BitVec 64)).toNat = ctrl_off.toNat + 7 :=
                          bv64_add_ofNat_toNat 7 (by decide) (by omega)
                        have hco6_arr : (ctrl_off + (6 : BitVec 64)).toNat <
                            s.scratch.scratch_buf.length := by
                          rw [h6n]; omega
                        let scr_1 := s.scratch.scratch_buf.set (ctrl_off + (6 : BitVec 64)).toNat
                          (ht_off.setWidth 32)
                        have hco7_arr : (ctrl_off + (7 : BitVec 64)).toNat < scr_1.length := by
                          rw [List.length_set, h7n]; omega
                        let scr_2 := scr_1.set (ctrl_off + (7 : BitVec 64)).toNat (sz.setWidth 32)
                        have hscr2_len : scr_2.length = c.scratch_cap := by
                          simp [scr_2, scr_1, hscrl]
                        have he6_2 : scr_2[ctrl_off.toNat + 6]? =
                            some (BitVec.ofNat 32 ht_off.toNat) := by
                          dsimp only [scr_2, scr_1]
                          rw [List.getElem?_set_ne (by rw [h7n]; omega), ← h6n,
                            List.getElem?_set_self (by rw [h6n]; omega)]
                          rfl
                        have he7_2 : scr_2[ctrl_off.toNat + 7]? =
                            some (BitVec.ofNat 32 sz.toNat) := by
                          dsimp only [scr_2]
                          rw [← h7n, List.getElem?_set_self (by rw [List.length_set, h7n]; omega)]
                          rfl
                        have hpref_2 : ∀ idx < ht_off.toNat, idx ≠ ctrl_off.toNat + 6 →
                            idx ≠ ctrl_off.toNat + 7 →
                            scr_2[idx]? = s.scratch.scratch_buf[idx]? := by
                          intro idx _ hne6 hne7
                          dsimp only [scr_2, scr_1]
                          rw [List.getElem?_set_ne (by rw [h7n]; exact Ne.symm hne7),
                            List.getElem?_set_ne (by rw [h6n]; exact Ne.symm hne6)]
                        c0_hsteps_nogrp
                        have hfs := focus_full_scratch_buf hm; clear hm
                        generalize hR_scr : FullScrBufRest c { s with scratch :=
                            { s.scratch with scratch_buf := scr_2 } } ⋆ R = R_scr at hfs
                        refine wp_loop_inv (ts := [i64])
                          (fun ⟨k2, ⟨⟩⟩ mk => ∃ scrl : List (BitVec 32),
                            scrl.length = c.scratch_cap ∧ k2.toNat ≤ sz.toNat ∧
                            scrl[ctrl_off.toNat + 6]? = some (BitVec.ofNat 32 ht_off.toNat) ∧
                            scrl[ctrl_off.toNat + 7]? = some (BitVec.ofNat 32 sz.toNat) ∧
                            (∀ idx < ht_off.toNat, idx ≠ ctrl_off.toNat + 6 →
                              idx ≠ ctrl_off.toNat + 7 →
                              scrl[idx]? = s.scratch.scratch_buf[idx]?) ∧
                            (∀ j < k2.toNat, scrl[ht_off.toNat + j]? = some 0xFFFFFFFF#32) ∧
                            (array (t := i32) c.pScratchBuf scrl ⋆ R_scr) mk)
                          (fun ⟨k2, ⟨⟩⟩ _ => sz.toNat - k2.toNat)
                          (fun Jk hJk => by
                            c0_hsteps; exact hJk (0#64, ()) m ⟨scr_2, hscr2_len, Nat.zero_le _,
                              he6_2, he7_2, hpref_2, fun _ h => by simp at h, hfs⟩)
                          (fun Jk ⟨k2, ⟨⟩⟩ mk ⟨scrl, hscrll, hk2_le, h6l, h7l, hpl, hclrl, hmk⟩
                              ihk => ?_)
                        c0_hsplit
                        · have hk2_lt : k2.toNat < sz.toNat := hc
                          have hadd_n : (ht_off + k2).toNat = ht_off.toNat + k2.toNat :=
                            bv64_add_toNat (by omega)
                          have hadd_arr : (ht_off + k2).toNat < scrl.length := by
                            rw [hadd_n]; omega
                          have hk2_1 : (k2 + 1#64).toNat = k2.toNat + 1 :=
                            bv64_add1_lt hk2_lt (by omega)
                          c0_hsteps; rw [hadd_n] at hm
                          let scrl' := scrl.set (ht_off.toNat + k2.toNat) 0xFFFFFFFF#32
                          refine ihk (k2 + 1#64, ()) _ (by dsimp only; rw [hk2_1]; omega)
                            ⟨scrl', by simp [scrl', hscrll], by rw [hk2_1]; omega, ?_, ?_, ?_, ?_,
                              hm⟩
                          · rw [List.getElem?_set_ne (by omega)]; exact h6l
                          · rw [List.getElem?_set_ne (by omega)]; exact h7l
                          · intro idx hi h1 h2
                            rw [List.getElem?_set_ne (by omega)]; exact hpl idx hi h1 h2
                          · intro j hj; rw [hk2_1] at hj
                            by_cases hjk : j = k2.toNat
                            · subst hjk; rw [List.getElem?_set_self (by omega)]
                            · rw [List.getElem?_set_ne (by omega)]; exact hclrl j (by omega)
                        · have hk2_eq : k2.toNat = sz.toNat := by omega
                          rw [hk2_eq] at hclrl; subst hR_scr
                          have hm_un := unfocus_full_scratch_buf hmk; clear hmk
                          have hsz_ne : sz ≠ 0#64 := fun h => by
                            have h1 := congrArg BitVec.toNat h
                            have h2p := Nat.two_pow_pos k
                            change sz.toNat = 0 at h1; omega
                          c0_hsteps
                          refine hQ sz scrl 0#64 _ hscrll
                            (scr_state_core_pres hlen scrl hscrll 0#64).1
                            rfl ⟨rfl, rfl⟩
                            (fun h0 => absurd h0 hsz_ne) (fun _ _ _ => hsz_ne)
                            (fun _ => ⟨⟨hscrll, hco8_ht, hsz_lt_cap, hht_le7, ⟨k, hk_le, hsz_pow⟩,
                                h6l, h7l⟩,
                              by rwa [← htop_eq], by rwa [← htop_eq], rfl, hclrl, hpl⟩)
                            (by assumption)
                    · intro J hJ; c0_hsplit
                      · c0_hsteps; refine hJ (lim2, ()) m0 ⟨rfl, ?_, ?_⟩
                        · rw [hlim2]; exact Nat.le_min.mpr ⟨by decide, Nat.le_max_left _ _⟩
                        · unfold m7CongHtTargetCap m7CongHashMaxSz m7CongHashMinSz; dsimp only
                          rw [hlim2] at hc
                          have hlim2_le : lim2.toNat ≤ c.scratch_cap - ht_off.toNat := by
                            have := ht_off.isLt; exact Nat.not_lt.mp (by m7_omega)
                          have hlim2_eq_min : lim2.toNat =
                              (if max_sz = 0#64 then 131072
                               else min 131072 (max 16 max_sz.toNat)) := by
                            rw [hlim2]; by_cases h0 : max_sz = 0#64 <;> simp [h0]
                          rw [hlim2_eq_min] at hlim2_le ⊢
                          exact (Nat.min_eq_left hlim2_le).symm
                      · c0_hsteps; refine hJ (BitVec.ofNat 64 c.scratch_cap - ht_off, ()) m0
                          ⟨rfl, ?_, ?_⟩
                        · rw [bv64_sub_toNat (by rw [bv64_ofNat_toNat_lt (by omega)]; omega),
                            bv64_ofNat_toNat_lt (by omega)]; omega
                        · unfold m7CongHtTargetCap m7CongHashMaxSz m7CongHashMinSz; dsimp only
                          rw [bv64_sub_toNat (by rw [bv64_ofNat_toNat_lt (by omega)]; omega),
                            bv64_ofNat_toNat_lt (by omega)]
                          have hcap_le_lim2 : c.scratch_cap - ht_off.toNat ≤ lim2.toNat := by
                            rw [bv64_cap_sub_mod (by omega) (by omega)] at hc
                            exact Nat.not_lt.mp hc
                          have hlim2_eq_min : lim2.toNat =
                              (if max_sz = 0#64 then 131072
                               else min 131072 (max 16 max_sz.toNat)) := by
                            rw [hlim2]; by_cases h0 : max_sz = 0#64 <;> simp [h0]
                          rw [hlim2_eq_min] at hcap_le_lim2
                          exact (Nat.min_eq_right hcap_le_lim2).symm
                  · intro J hJ; c0_hsplit
                    · c0_hsteps; refine hJ (16#64, ()) m0 ⟨rfl, ?_⟩
                      rw [hlim1] at hc
                      have hlt : (if max_sz = 0#64 then 131072 else max_sz.toNat) < 16 := by
                        have : min 131072
                            (if max_sz = 0#64 then 131072 else max_sz.toNat) < 16 := by
                          m7_omega
                        omega
                      rw [Nat.max_eq_left (Nat.le_of_lt hlt)]; rfl
                    · c0_hsteps; refine hJ (lim1, ()) m0 ⟨rfl, ?_⟩
                      rw [hlim1] at hc
                      have hge : 16 ≤ (if max_sz = 0#64 then 131072 else max_sz.toNat) := by
                        have : 16 ≤ min 131072
                            (if max_sz = 0#64 then 131072 else max_sz.toNat) := by
                          m7_omega
                        omega
                      rw [hlim1, Nat.max_eq_right hge]
                · intro J hJ; c0_hsplit
                  · c0_hsteps; refine hJ (131072#64, ()) m0 ⟨rfl, ?_⟩
                    rw [hlim0] at hc
                    have hlt : 131072 < (if max_sz = 0#64 then 131072 else max_sz.toNat) := by
                      m7_omega
                    exact (Nat.min_eq_left (Nat.le_of_lt hlt)).symm
                  · c0_hsteps; refine hJ (lim0, ()) m0 ⟨rfl, ?_⟩
                    rw [hlim0] at hc
                    have hle : (if max_sz = 0#64 then 131072 else max_sz.toNat) ≤ 131072 := by
                      m7_omega
                    rw [hlim0, Nat.min_eq_right hle]
              · intro J hJ; c0_hsplit
                · have hmax0 : max_sz = 0#64 := hc
                  c0_hsteps
                  refine hJ (131072#64, ()) m0 ⟨rfl, by simp only [hmax0, ↓reduceIte]; rfl⟩
                · have hmax_ne : max_sz ≠ 0#64 := hc
                  c0_hsteps; refine hJ (max_sz, ()) m0 ⟨rfl, by simp only [hmax_ne, ↓reduceIte]⟩

/-- **#3 (`full_cong_ht_grow_m7_wp`)**: doubles `ht_sz` up to `131072` via in-place tagged
rehash (`0x80000000u`), capping cleanly when `ht_sz == 131072` or `ht_off + 2 * ht_sz > cap`. -/
theorem full_cong_ht_grow_m7_wp (Γ : Env)
    (hHashEnt : ∀ a m Q X, m7CongHtHashEntSpec a m Q X →
      Γ "full_cong_ht_hash_ent_m7" [i64, i32, i64] [i64] a m Q X) :
    ∀ a m Q X, m7CongHtGrowSpec a m Q X →
      Func.wp Γ full_cong_ht_grow_m7_body a m Q X := by
  rintro ⟨h, ctrl_off, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hlen, hm0, hQ⟩
  have hsc := c.hscr; unfold dimacsBound at hsc
  have hscrl := hlen.scratch_ok.scratch_buf_len
  have hfail_noctrl : ∀ ret : BitVec 64,
      (∀ ht_off old_sz, M7CongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ht_off old_sz →
        False) →
      Q (ret, ()) m0 := fun ret hno =>
    hQ ret s.scratch.scratch_buf m0 hscrl hlen rfl ⟨rfl, rfl⟩
      (fun ht os h => False.elim (hno ht os h)) (fun _ => rfl) hm0
  unfold Func.wp full_cong_ht_grow_m7_body
  c0_hsplit
  · c0_hsteps; exact hfail_noctrl 0#64 (fun _ _ hok => by
      have := hok.2.1; have := hok.2.2.1; m7_omega)
  · have hco_le : ctrl_off.toNat ≤ c.scratch_cap := by m7_omega
    clear hc; c0_hsplit
    · c0_hsteps; exact hfail_noctrl 0#64 (fun _ _ hok => by
        have := ctrl_off.isLt; have := hok.2.1; have := hok.2.2.1; m7_omega)
    · have hco8 : ctrl_off.toNat + 8 ≤ c.scratch_cap := by
        have := ctrl_off.isLt; m7_omega
      clear hc
      have h6n : (ctrl_off + 6#64).toNat = ctrl_off.toNat + 6 :=
        bv64_add_ofNat_toNat 6 (by decide) (by omega)
      have h7n : (ctrl_off + 7#64).toNat = ctrl_off.toNat + 7 :=
        bv64_add_ofNat_toNat 7 (by decide) (by omega)
      let ht_off_w := s.scratch.scratch_buf[ctrl_off.toNat + 6]'(by omega)
      let old_sz_w := s.scratch.scratch_buf[ctrl_off.toNat + 7]'(by omega)
      let ht_off : BitVec 64 := ht_off_w.setWidth 64
      let old_sz : BitVec 64 := old_sz_w.setWidth 64
      have hht_nat : ht_off_w.toNat = ht_off.toNat := (bv64_zext32_toNat _).symm
      have hos_nat : old_sz_w.toNat = old_sz.toNat := (bv64_zext32_toNat _).symm
      have hho_eq : ht_off = (s.scratch.scratch_buf[ctrl_off.toNat + 6]'(by omega)).setWidth 64 :=
        rfl
      have hsz_eq : old_sz = (s.scratch.scratch_buf[ctrl_off.toNat + 7]'(by omega)).setWidth 64 :=
        rfl
      have hs6a : s.scratch.scratch_buf[(BitVec.toNat ctrl_off + BitVec.toNat (6 : BitVec 64)) %
          2 ^ 64]'(by
          change (ctrl_off.toNat + 6) % 2 ^ 64 < s.scratch.scratch_buf.length
          rw [Nat.mod_eq_of_lt (by omega)]; omega) = ht_off_w :=
        scr_idx_add_imm 6 rfl (by omega) _ _
      have hs6b : s.scratch.scratch_buf[(ctrl_off + (6 : BitVec 64)).toNat]'(by
          change (ctrl_off.toNat + 6) % 2 ^ 64 < s.scratch.scratch_buf.length
          rw [Nat.mod_eq_of_lt (by omega)]; omega) = ht_off_w := hs6a
      have hs7a : s.scratch.scratch_buf[(BitVec.toNat ctrl_off + BitVec.toNat (7 : BitVec 64)) %
          2 ^ 64]'(by
          change (ctrl_off.toNat + 7) % 2 ^ 64 < s.scratch.scratch_buf.length
          rw [Nat.mod_eq_of_lt (by omega)]; omega) = old_sz_w :=
        scr_idx_add_imm 7 rfl (by omega) _ _
      have hs7b : s.scratch.scratch_buf[(ctrl_off + (7 : BitVec 64)).toNat]'(by
          change (ctrl_off.toNat + 7) % 2 ^ 64 < s.scratch.scratch_buf.length
          rw [Nat.mod_eq_of_lt (by omega)]; omega) = old_sz_w := hs7a
      have hbad_ht : ¬ (ctrl_off.toNat + 8 ≤ ht_off.toNat ∧ ht_off.toNat < c.scratch_cap ∧
          ht_off.toNat ≤ 0x7FFFFFFF) →
          ∀ ho os, M7CongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ho os → False :=
        fun hbad ho os hok => by
          apply hbad
          obtain ⟨rfl, rfl⟩ := m7CongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
          exact ⟨hok.2.1, Nat.lt_of_lt_of_le (by
              have ⟨k, _, he⟩ := hok.2.2.2.2.1; have := Nat.two_pow_pos k; omega) hok.2.2.1,
            hok.2.2.2.1⟩
      c0_hsplit
      · c0_hsteps; exact hfail_noctrl 0#64 (hbad_ht fun ⟨h1, _⟩ => by
          rw [hs6a, hht_nat] at hc
          change ht_off.toNat < (ctrl_off.toNat + BitVec.toNat 8) % 2 ^ 64 at hc
          m7_omega)
      · have h1 : ctrl_off.toNat + 8 ≤ ht_off.toNat := by
          rw [hs6a, hht_nat] at hc
          change ¬ ht_off.toNat < (ctrl_off.toNat + BitVec.toNat 8) % 2 ^ 64 at hc
          m7_omega
        clear hc; c0_hsplit
        · c0_hsteps; exact hfail_noctrl 0#64 (hbad_ht fun ⟨_, h2, _⟩ => by
            rw [hs6a, hht_nat] at hc
            change c.scratch_cap % 2 ^ 64 ≤ ht_off.toNat at hc; m7_omega)
        · have h2 : ht_off.toNat < c.scratch_cap := by
            rw [hs6a, hht_nat] at hc
            change ¬ c.scratch_cap % 2 ^ 64 ≤ ht_off.toNat at hc; m7_omega
          clear hc; c0_hsplit
          · c0_hsteps; exact hfail_noctrl 0#64 (hbad_ht fun ⟨_, _, h3⟩ => by
              rw [hs6a, hht_nat] at hc
              change BitVec.toNat 2147483647 < ht_off.toNat at hc; m7_omega)
          · have h3 : ht_off.toNat ≤ 0x7FFFFFFF := by
              rw [hs6a, hht_nat] at hc
              change ¬ BitVec.toNat 2147483647 < ht_off.toNat at hc; m7_omega
            clear hc
            have hbad_sz : ¬ (16 ≤ old_sz.toNat ∧ old_sz.toNat ≤ 131072 ∧
                (old_sz &&& (old_sz - 1#64)) = 0#64 ∧
                old_sz.toNat ≤ c.scratch_cap - ht_off.toNat) →
                ∀ ho os, M7CongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ho os → False :=
              fun hbad ho os hok => by
                apply hbad
                obtain ⟨rfl, rfl⟩ := m7CongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
                obtain ⟨k, hk, he⟩ := hok.2.2.2.2.1
                refine ⟨by rw [he]; have := Nat.two_pow_pos k; omega,
                  by rw [he]; exact pow2_16_mul_le k hk,
                  bv64_pow2_and_sub1_zero hk he,
                  by have := hok.2.2.1; omega⟩
            c0_hsplit
            · c0_hsteps; exact hfail_noctrl 0#64 (hbad_sz fun ⟨h4, _⟩ => by
                rw [hs7a, hos_nat] at hc
                change old_sz.toNat < BitVec.toNat 16 at hc; m7_omega)
            · have h4 : 16 ≤ old_sz.toNat := by
                rw [hs7a, hos_nat] at hc
                change ¬ old_sz.toNat < BitVec.toNat 16 at hc; m7_omega
              clear hc; c0_hsplit
              · c0_hsteps; exact hfail_noctrl 0#64 (hbad_sz fun ⟨_, hm, _⟩ => by
                  rw [hs7a, hos_nat] at hc
                  change BitVec.toNat 131072 < old_sz.toNat at hc; m7_omega)
              · have hmax : old_sz.toNat ≤ 131072 := by
                  rw [hs7a, hos_nat] at hc
                  change ¬ BitVec.toNat 131072 < old_sz.toNat at hc; m7_omega
                clear hc; c0_hsplit
                · c0_hsteps; exact hfail_noctrl 0#64 (hbad_sz fun ⟨_, _, h5, _⟩ => by
                    rw [hs7a] at hc; exact hc h5)
                · have h5 : (old_sz &&& (old_sz - 1#64)) = 0#64 := by
                    rw [hs7a] at hc; exact hc
                  clear hc; c0_hsplit
                  · c0_hsteps; exact hfail_noctrl 0#64 (hbad_sz fun ⟨_, _, _, h6⟩ => by
                      rw [hs6a, hht_nat, hs7a, hos_nat] at hc
                      change (2 ^ 64 - ht_off.toNat + c.scratch_cap) % 2 ^ 64 <
                        old_sz.toNat at hc
                      have := ht_off.isLt; m7_omega)
                  · have h6 : old_sz.toNat ≤ c.scratch_cap - ht_off.toNat := by
                      rw [hs6a, hht_nat, hs7a, hos_nat] at hc
                      change ¬ (2 ^ 64 - ht_off.toNat + c.scratch_cap) % 2 ^ 64 <
                        old_sz.toNat at hc
                      have := ht_off.isLt; m7_omega
                    clear hc
                    have hok_read : M7CongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat
                        ht_off.toNat old_sz.toNat :=
                      m7CongHtCtrlOk_from_reads hscrl hco8 hho_eq hsz_eq h1 h2 h3 h4 h5 h6 hmax
                    obtain ⟨k_exp, hk_exp_le, hos_pow⟩ := hok_read.2.2.2.2.1
                    c0_hsplit
                    · have heq_max : old_sz.toNat = 131072 := by
                        rw [hs7a] at hc; exact congrArg BitVec.toNat hc
                      c0_hsteps; try simp only [hs7b]
                      refine hQ old_sz s.scratch.scratch_buf m0 hscrl hlen rfl ⟨rfl, rfl⟩
                        (fun ho os hok => ?_) (fun hno => False.elim (hno _ _ hok_read)) hm0
                      obtain ⟨rfl, rfl⟩ := m7CongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
                      unfold m7CongHashMaxSz at *
                      exact ⟨fun _ => ⟨rfl, rfl⟩, fun hlt _ => absurd heq_max (by omega)⟩
                    · have hlt_max : old_sz.toNat < m7CongHashMaxSz := by
                        rw [hs7a] at hc
                        have hne : old_sz.toNat ≠ 131072 := fun h => hc (BitVec.eq_of_toNat_eq h)
                        unfold m7CongHashMaxSz; omega
                      have hk_lt13 : k_exp < 13 := by
                        rcases Nat.lt_or_ge k_exp 13 with hlt | hge
                        · exact hlt
                        · obtain rfl : k_exp = 13 := by omega
                          have h13 : 16 * 2 ^ 13 = 131072 := by decide
                          unfold m7CongHashMaxSz at hlt_max; omega
                      let new_sz : BitVec 64 := old_sz <<< (1#32 : BitVec 32).signExtend 64
                      have hnew_n : new_sz.toNat = 2 * old_sz.toNat :=
                        bv64_shl1_toNat (by unfold m7CongHashMaxSz at hlt_max; omega)
                      have hnew_le : new_sz.toNat ≤ m7CongHashMaxSz := by
                        unfold m7CongHashMaxSz at hlt_max ⊢
                        rw [hnew_n, hos_pow]
                        have : 2 * (16 * 2 ^ k_exp) = 16 * 2 ^ (k_exp + 1) := by
                          rw [Nat.pow_succ]; omega
                        rw [this]; exact pow2_16_mul_le (k_exp + 1) (by omega)
                      clear hc; c0_hsplit
                      · have hno_fit : c.scratch_cap < ht_off.toNat + 2 * old_sz.toNat := by
                          rw [hs6a, hht_nat, hs7a, hos_nat,
                            bv64_cap_sub_mod (Nat.le_of_lt h2) (by omega),
                            Nat.mod_eq_of_lt (by unfold m7CongHashMaxSz at hlt_max; omega)] at hc
                          omega
                        c0_hsteps; try simp only [hs7b]
                        refine hQ old_sz s.scratch.scratch_buf m0 hscrl hlen rfl
                          ⟨rfl, rfl⟩ (fun ho os hok => ?_)
                          (fun hno => False.elim (hno _ _ hok_read)) hm0
                        obtain ⟨rfl, rfl⟩ := m7CongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
                        exact ⟨fun _ => ⟨rfl, rfl⟩,
                          fun _ hfit => absurd hfit (Nat.not_le.mpr hno_fit)⟩
                      · have hfit : ht_off.toNat + 2 * old_sz.toNat ≤ c.scratch_cap := by
                          rw [hs6a, hht_nat, hs7a, hos_nat,
                            bv64_cap_sub_mod (Nat.le_of_lt h2) (by omega),
                            Nat.mod_eq_of_lt (by unfold m7CongHashMaxSz at hlt_max; omega)] at hc
                          omega
                        clear hc
                        have hfs := focus_full_scratch_buf hm0; clear hm0
                        generalize hR_scr : FullScrBufRest c s ⋆ R = R_scr at hfs
                        c0_hsteps_nogrp
                        refine wp_loop_inv (ts := [i64])
                          (fun ⟨k, ⟨⟩⟩ mk => ∃ scrk : List (BitVec 32),
                            scrk.length = c.scratch_cap ∧ old_sz.toNat ≤ k.toNat ∧
                            k.toNat ≤ new_sz.toNat ∧
                            (∀ idx < ht_off.toNat, scrk[idx]? = s.scratch.scratch_buf[idx]?) ∧
                            (∀ j < old_sz.toNat,
                              scrk[ht_off.toNat + j]? = s.scratch.scratch_buf[ht_off.toNat + j]?) ∧
                            (∀ j, old_sz.toNat ≤ j → j < k.toNat →
                              scrk[ht_off.toNat + j]? = some 0xFFFFFFFF#32) ∧
                            (array (t := i32) c.pScratchBuf scrk ⋆ R_scr) mk)
                          (fun ⟨k, ⟨⟩⟩ _ => new_sz.toNat - k.toNat)
                          (fun Jk hJk => by
                            c0_hsteps; try simp only [hs7b]
                            exact hJk (old_sz, ()) m0 ⟨s.scratch.scratch_buf, hscrl,
                              Nat.le_refl _, by omega, fun _ _ => rfl, fun _ _ => rfl,
                              fun _ h1 h2 => by omega, hfs⟩)
                          (fun Jk ⟨k, ⟨⟩⟩ mk ⟨scrk, hscrkl, hk_ge, hk_le, hpre, hold, hclr, hmk⟩
                              ihk => ?_)
                        c0_hsplit
                        · have hk_lt : k.toNat < new_sz.toNat := by
                            rw [hs7a, hos_nat,
                              Nat.mod_eq_of_lt (by unfold m7CongHashMaxSz at hlt_max; omega),
                              ← hnew_n] at hc
                            exact hc
                          have hadd_n : (ht_off + k).toNat = ht_off.toNat + k.toNat :=
                            bv64_add_toNat (by omega)
                          have hadd_arr : (ht_off + k).toNat < scrk.length := by
                            rw [hadd_n]; omega
                          have hk1_n : (k + 1#64).toNat = k.toNat + 1 :=
                            bv64_add1_lt hk_lt (by omega)
                          c0_hsteps; try simp only [hs6b] at hm
                          rw [hadd_n] at hm
                          let scrk' := scrk.set (ht_off.toNat + k.toNat) 0xFFFFFFFF#32
                          refine ihk (k + 1#64, ()) _ (by dsimp only; rw [hk1_n]; omega)
                            ⟨scrk', by simp [scrk', hscrkl], by rw [hk1_n]; omega,
                              by rw [hk1_n]; omega,
                              fun idx hi => by
                                rw [List.getElem?_set_ne (by omega)]; exact hpre idx hi,
                              fun j hj => by rw [List.getElem?_set_ne (by omega)]; exact hold j hj,
                              fun j h1' h2' => by
                                rw [hk1_n] at h2'
                                by_cases hjk : j = k.toNat
                                · subst hjk; rw [List.getElem?_set_self (by omega)]
                                · rw [List.getElem?_set_ne (by omega)]; exact hclr j h1' (by omega),
                              hm⟩
                        · have hk_eq : k.toNat = new_sz.toNat := by
                            rw [hs7a, hos_nat,
                              Nat.mod_eq_of_lt (by unfold m7CongHashMaxSz at hlt_max; omega),
                              ← hnew_n] at hc
                            exact Nat.le_antisymm hk_le (Nat.not_lt.mp hc)
                          rw [hk_eq] at hclr; clear hc
                          have hmig0 : SlotMigOk c s.scratch.scratch_buf scrk ht_off.toNat
                              old_sz.toNat new_sz.toNat := by
                            refine ⟨hscrkl, hpre, fun j hj => ?_⟩
                            by_cases hj_old : j < old_sz.toNat
                            · have hget := hold j hj_old
                              by_cases hem : s.scratch.scratch_buf[ht_off.toNat + j]? =
                                  some 0xFFFFFFFF#32
                              · left; rw [hget, hem]
                              · right
                                have hlt_len : ht_off.toNat + j < s.scratch.scratch_buf.length := by
                                  omega
                                refine ⟨j, hj_old, s.scratch.scratch_buf[ht_off.toNat + j]'hlt_len,
                                  ?_, ?_, Or.inl ?_⟩
                                · rw [List.getElem?_eq_getElem hlt_len]
                                · intro he; apply hem; rw [List.getElem?_eq_getElem hlt_len, he]
                                · rw [hget, List.getElem?_eq_getElem hlt_len]
                            · left; exact hclr j (by omega) hj
                          have hkeep0 : SlotKeepOk s.scratch.scratch_buf scrk ht_off.toNat
                              old_sz.toNat new_sz.toNat 0xFFFFFFFF#32 := by
                            simpa [hnew_n] using
                              slotKeepOk_init hold (fun j hj1 hj2 => hclr j hj1 (by omega))
                          c0_hsteps_nogrp
                          refine wp_loop_inv (ts := [i64])
                            (fun ⟨i, ⟨⟩⟩ mi => ∃ scri : List (BitVec 32),
                              i.toNat ≤ old_sz.toNat ∧
                              SlotMigOk c s.scratch.scratch_buf scri ht_off.toNat old_sz.toNat
                                new_sz.toNat ∧
                              SlotKeepOk s.scratch.scratch_buf scri ht_off.toNat old_sz.toNat
                                new_sz.toNat 0xFFFFFFFF#32 ∧
                              (array (t := i32) c.pScratchBuf scri ⋆ R_scr) mi)
                            (fun ⟨i, ⟨⟩⟩ _ => old_sz.toNat - i.toNat)
                            (fun Ji hJi => by
                              c0_hsteps; exact hJi (0#64, ()) mk
                                ⟨scrk, Nat.zero_le _, hmig0, hkeep0, hmk⟩)
                            (fun Ji ⟨i, ⟨⟩⟩ mi ⟨scri, hi_le, hmigi, hkeepi, hmi⟩ ihi => ?_)
                          c0_hsplit
                          · have hi_lt : i.toNat < old_sz.toNat := by
                              rw [hs7a, hos_nat] at hc; exact hc
                            have hi_add_n : (ht_off + i).toNat = ht_off.toNat + i.toNat :=
                              bv64_add_toNat (by omega)
                            have hi_add_arr : (ht_off + i).toNat < scri.length := by
                              rw [hi_add_n, hmigi.1]; omega
                            have hi1_n : (i + 1#64).toNat = i.toNat + 1 :=
                              bv64_add1_lt hi_lt (by omega)
                            c0_hsteps_nogrp
                            refine wp_join0
                              (fun mj => ∃ scrj : List (BitVec 32),
                                SlotMigOk c s.scratch.scratch_buf scrj ht_off.toNat old_sz.toNat
                                  new_sz.toNat ∧
                                SlotKeepOk s.scratch.scratch_buf scrj ht_off.toNat old_sz.toNat
                                  new_sz.toNat 0xFFFFFFFF#32 ∧
                                (array (t := i32) c.pScratchBuf scrj ⋆ R_scr) mj)
                              (fun _ mj ⟨scrj, hmigj, hkeepj, hmj⟩ => by
                                c0_hsteps; exact ihi (i + 1#64, ()) mj
                                  (by dsimp only; rw [hi1_n]; omega)
                                  ⟨scrj, by rw [hi1_n]; omega, hmigj, hkeepj, hmj⟩)
                              (fun Jj hJj => ?_)
                            c0_hsplit
                            · have hraw_ne :
                                  scri[(ht_off + i).toNat]'hi_add_arr ≠ 0xFFFFFFFF#32 := by
                                simp only [hs6a, hht_nat] at hc; exact hc
                              clear hc; c0_hsplit
                              · have hraw_msb : (scri[(ht_off + i).toNat]'hi_add_arr &&&
                                    0x80000000#32) = 0#32 := by
                                  simp only [hs6a, hht_nat] at hc
                                  first | exact hc | exact bv32_eq_of_not_ne hc
                                clear hc; c0_hsplit
                                · have hscril : scri.length = c.scratch_cap := hmigi.1
                                  have hraw_lt : (scri[(ht_off + i).toNat]'hi_add_arr).toNat <
                                      ht_off.toNat := by
                                    simp only [hs6a, hht_nat] at hc
                                    have hg : scri[(ht_off + i).toNat]'hi_add_arr =
                                        scri[(ht_off.toNat + BitVec.toNat i) % 2 ^ 64]'
                                          (by rw [hscril, Nat.mod_eq_of_lt (by omega)]; omega) :=
                                      list_getElem_congr
                                        (by rw [hi_add_n, Nat.mod_eq_of_lt (by omega)])
                                        hi_add_arr
                                        (by rw [hscril, Nat.mod_eq_of_lt (by omega)]; omega)
                                    exact congrArg BitVec.toNat hg ▸ hc
                                  let raw := scri[(ht_off + i).toNat]'hi_add_arr
                                  have hraw_get : scri[ht_off.toNat + i.toNat]? = some raw := by
                                    rw [List.getElem?_eq_getElem (by rw [hmigi.1]; omega)]
                                    congr 1; exact (list_getElem_congr hi_add_n hi_add_arr _).symm
                                  have hcur_ok0 : CurMigOk s.scratch.scratch_buf ht_off.toNat
                                      old_sz.toNat raw :=
                                    curMigOk_of_slot hmigi (by omega) hraw_get hraw_ne hraw_msb
                                      hraw_lt
                                  clear hc; c0_hsteps_nogrp
                                  let scrb0 := scri.set (ht_off.toNat + i.toNat) 0xFFFFFFFF#32
                                  have hm_b0 :
                                      (array (t := i32) c.pScratchBuf scrb0 ⋆ R_scr) m := by
                                    refine (congrArg
                                      (fun arr => (array (t := i32) c.pScratchBuf arr ⋆ R_scr) m)
                                      ?_).mp hm
                                    dsimp only [scrb0]; congr 1
                                    first | exact hi_add_n | (rw [hs6b]; exact hi_add_n)
                                  have hmig_b0 :
                                      SlotMigOk c s.scratch.scratch_buf scrb0 ht_off.toNat
                                      old_sz.toNat new_sz.toNat :=
                                    slotMigOk_set_empty hmigi (by rw [hmigi.1]; omega)
                                  have hkeep_b0 :
                                      SlotKeepOk s.scratch.scratch_buf scrb0 ht_off.toNat
                                      old_sz.toNat new_sz.toNat raw :=
                                    slotKeepOk_set_empty hkeepi hok_read.2.2.2.1 (by omega)
                                      (by rw [hmigi.1]; omega) hraw_get hraw_ne hraw_msb
                                  refine wp_loop_break_group (brkTs := [i32, i64])
                                    (lpTs := [i32, i64])
                                    (fun (_cb, _hb, ()) mb => ∃ scrb : List (BitVec 32),
                                      SlotMigOk c s.scratch.scratch_buf scrb ht_off.toNat
                                        old_sz.toNat new_sz.toNat ∧
                                      SlotKeepOk s.scratch.scratch_buf scrb ht_off.toNat
                                        old_sz.toNat new_sz.toNat 0xFFFFFFFF#32 ∧
                                      (array (t := i32) c.pScratchBuf scrb ⋆ R_scr) mb)
                                    (fun rem (curl, hops, ()) ml => ∃ scrl : List (BitVec 32),
                                      SlotMigOk c s.scratch.scratch_buf scrl ht_off.toNat
                                        old_sz.toNat new_sz.toNat ∧
                                      SlotKeepOk s.scratch.scratch_buf scrl ht_off.toNat
                                        old_sz.toNat new_sz.toNat curl ∧
                                      CurMigOk s.scratch.scratch_buf ht_off.toNat
                                        old_sz.toNat curl ∧
                                      curl ≠ 0xFFFFFFFF#32 ∧
                                      hops.toNat ≤ new_sz.toNat ∧
                                      (List.range new_sz.toNat).countP (fun k =>
                                        htUnmigPred (scrl[ht_off.toNat + k]?.getD
                                          0xFFFFFFFF#32)) + 1 + hops.toNat ≤ old_sz.toNat ∧
                                      rem = new_sz.toNat - hops.toNat ∧
                                      (array (t := i32) c.pScratchBuf scrl ⋆ R_scr) ml)
                                    ?_ ?_ ?_
                                  · rintro _ ⟨cb, hb, ⟨⟩⟩ mb ⟨scrb, hmigb, hkeepb, hmb⟩
                                    c0_hsteps; exact hJj mb ⟨scrb, hmigb, hkeepb, hmb⟩
                                  · rintro Bh Lh rem ⟨curl, hops, ⟨⟩⟩ ml hBh hLh
                                      ⟨scrl, hmigl, hkeepl, hcurl, hcur_ne, hhops_le, hunml, rfl,
                                        hml⟩
                                    c0_hsplit
                                    · have hhops_lt : hops.toNat < new_sz.toNat := by
                                        rw [hs7a, hos_nat, Nat.mod_eq_of_lt
                                            (by unfold m7CongHashMaxSz at hlt_max; omega),
                                          ← hnew_n] at hc
                                        exact hc
                                      have hcurl_lt : curl.toNat < ht_off.toNat := by
                                        rcases hcurl with rfl | ⟨hlt, _⟩
                                        · exact absurd rfl hcur_ne
                                        · exact hlt
                                      have hm_full : (FullMem c { s with scratch :=
                                          { s.scratch with scratch_buf := scrl } } ⋆ R) ml := by
                                        subst hR_scr; exact unfocus_full_scratch_buf hml
                                      clear hc; c0_hsteps; c0_call hHashEnt
                                      refine ⟨c, { s with scratch :=
                                          { s.scratch with scratch_buf := scrl } },
                                        R, rfl, ⟨hlen.core_ok,
                                          { hlen.scratch_ok with scratch_buf_len := hmigl.1 }⟩,
                                        hm_full, fun hv => ?_⟩
                                      let slot0 := hv &&& (new_sz - 1#64)
                                      have hslot0_lt : slot0.toNat < new_sz.toNat :=
                                        bv64_and_sub1_lt (by omega)
                                      c0_hsteps_nogrp
                                      refine wp_loop_break_group (brkTs := [i32, i64, i64])
                                        (lpTs := [i64, i64])
                                        (fun (cur_p, _sl_p, _p_p, ()) mp =>
                                          ∃ scrp : List (BitVec 32),
                                          SlotMigOk c s.scratch.scratch_buf scrp ht_off.toNat
                                            old_sz.toNat new_sz.toNat ∧
                                          SlotKeepOk s.scratch.scratch_buf scrp ht_off.toNat
                                            old_sz.toNat new_sz.toNat cur_p ∧
                                          CurMigOk s.scratch.scratch_buf ht_off.toNat
                                            old_sz.toNat cur_p ∧
                                          (cur_p = 0xFFFFFFFF#32 ∨
                                            (List.range new_sz.toNat).countP (fun k =>
                                              htUnmigPred (scrp[ht_off.toNat + k]?.getD
                                                0xFFFFFFFF#32)) + 1 + (hops.toNat + 1) ≤
                                              old_sz.toNat) ∧
                                          (array (t := i32) c.pScratchBuf scrp ⋆ R_scr) mp)
                                        (fun remp (slotp, pp, ()) mp =>
                                          ∃ scrp : List (BitVec 32),
                                          scrp = scrl ∧
                                          SlotMigOk c s.scratch.scratch_buf scrp ht_off.toNat
                                            old_sz.toNat new_sz.toNat ∧
                                          SlotKeepOk s.scratch.scratch_buf scrp ht_off.toNat
                                            old_sz.toNat new_sz.toNat curl ∧
                                          slotp.toNat = (slot0.toNat + pp.toNat) % new_sz.toNat ∧
                                          (∀ m < pp.toNat,
                                            scrp[ht_off.toNat + (slot0.toNat + m) % new_sz.toNat]?
                                              ≠ some 0xFFFFFFFF#32) ∧
                                          slotp.toNat < new_sz.toNat ∧ pp.toNat ≤ new_sz.toNat ∧
                                          remp = new_sz.toNat - pp.toNat ∧
                                          (array (t := i32) c.pScratchBuf scrp ⋆ R_scr) mp)
                                        ?_ ?_ ?_
                                      · rintro _ ⟨cur_p, sl_p, p_p, ⟨⟩⟩ mp
                                          ⟨scrp, hmigp, hkeepp, hcurp, hunmp, hmp⟩
                                        c0_hsplit
                                        · have hcp_eq : cur_p = 0xFFFFFFFF#32 := hc
                                          subst hcp_eq
                                          c0_hsteps; exact hBh (0xFFFFFFFF#32, hops, ()) mp
                                            ⟨scrp, hmigp, hkeepp, hmp⟩
                                        · have hhops1 : (hops + 1#64).toNat = hops.toNat + 1 :=
                                            bv64_add1_lt hhops_lt (by omega)
                                          rcases hunmp with hff | hunmp'
                                          · exact absurd hff hc
                                          · c0_hsteps
                                            exact hLh (new_sz.toNat - (hops + 1#64).toNat)
                                              (cur_p, hops + 1#64, ()) mp (by omega)
                                              ⟨scrp, hmigp, hkeepp, hcurp, hc, by omega,
                                                by rw [hhops1]; exact hunmp', rfl, hmp⟩
                                      · rintro Bp Lp remp ⟨slotp, pp, ⟨⟩⟩ mp hBp hLp
                                          ⟨scrp, hscrp_eq, hmigp, hkeepp, hslot_mod, hnoemp,
                                            hslot_lt, hpp_le, rfl, hmp⟩
                                        c0_hsplit
                                        · have hpp_lt : pp.toNat < new_sz.toNat := by
                                            rw [hs7a, hos_nat, Nat.mod_eq_of_lt
                                                (by unfold m7CongHashMaxSz at hlt_max; omega),
                                              ← hnew_n] at hc
                                            exact hc
                                          have hsl_add_n : (ht_off + slotp).toNat =
                                              ht_off.toNat + slotp.toNat :=
                                            bv64_add_toNat (by omega)
                                          have hsl_arr : (ht_off + slotp).toNat < scrp.length := by
                                            rw [hsl_add_n, hmigp.1]; omega
                                          clear hc; c0_hsplit
                                          · have hslot_get :
                                                scrp[ht_off.toNat + slotp.toNat]? =
                                                  some 0xFFFFFFFF#32 := by
                                              rw [List.getElem?_eq_getElem (by rw [hmigp.1]; omega)]
                                              congr 1; simp only [hs6a, hht_nat] at hc
                                              exact
                                                (list_getElem_congr hsl_add_n hsl_arr _).symm.trans
                                                  hc
                                            c0_hsteps; try simp only [hs6b] at hm
                                            rw [hsl_add_n] at hm
                                            exact hBp (0xFFFFFFFF#32, slotp, pp, ()) _
                                              ⟨scrp.set (ht_off.toNat + slotp.toNat)
                                                  (curl ||| 0x80000000#32),
                                               slotMigOk_set_cur hmigp hcurl hcur_ne
                                                 (by rw [hmigp.1]; omega),
                                               slotKeepOk_set_mig_empty hkeepp hcur_ne hcurl_lt
                                                 hok_read.2.2.2.1 (by omega)
                                                 (by rw [hmigp.1]; omega) hslot_get,
                                               Or.inl rfl, Or.inl rfl, hm⟩
                                          · have hdst_ne :
                                                scrp[(ht_off + slotp).toNat]'hsl_arr ≠
                                                  0xFFFFFFFF#32 := by
                                              simp only [hs6a, hht_nat] at hc; exact hc
                                            clear hc; c0_hsplit
                                            · have hdst_msb :
                                                  (scrp[(ht_off + slotp).toNat]'hsl_arr &&&
                                                    0x80000000#32) = 0#32 := by
                                                simp only [hs6a, hht_nat] at hc
                                                exact hc
                                              let dst := scrp[(ht_off + slotp).toNat]'hsl_arr
                                              have hdst_get :
                                                  scrp[ht_off.toNat + slotp.toNat]? = some dst := by
                                                rw [List.getElem?_eq_getElem
                                                    (by rw [hmigp.1]; omega)]
                                                congr 1
                                                exact (list_getElem_congr hsl_add_n hsl_arr _).symm
                                              have hscrpl : scrp.length = c.scratch_cap := hmigp.1
                                              clear hc; c0_hsteps_nogrp
                                              let scrp_s := scrp.set (ht_off.toNat + slotp.toNat)
                                                (curl ||| 0x80000000#32)
                                              have hm_s : (array (t := i32) c.pScratchBuf scrp_s ⋆
                                                  R_scr) m := by
                                                refine (congrArg
                                                  (fun arr => (array (t := i32) c.pScratchBuf
                                                    arr ⋆ R_scr) m) ?_).mp hm
                                                dsimp only [scrp_s]; congr 1
                                                first | exact hsl_add_n |
                                                  (rw [hs6b]; exact hsl_add_n)
                                              refine wp_join_group (ts := [i32])
                                                (fun (cur_n, ()) mn => mn = m ∧
                                                  CurMigOk s.scratch.scratch_buf ht_off.toNat
                                                    old_sz.toNat cur_n ∧
                                                  SlotKeepOk s.scratch.scratch_buf scrp_s
                                                    ht_off.toNat old_sz.toNat new_sz.toNat cur_n ∧
                                                  (cur_n = 0xFFFFFFFF#32 ∨
                                                    (List.range new_sz.toNat).countP (fun k =>
                                                      htUnmigPred (scrp_s[ht_off.toNat + k]?.getD
                                                        0xFFFFFFFF#32)) + 1 + (hops.toNat + 1) ≤
                                                      old_sz.toNat))
                                                ?_ ?_
                                              · rintro _ ⟨cur_n, ⟨⟩⟩ mn
                                                  ⟨hmn, hcur_n, hkeep_n, hunm_n⟩
                                                subst mn; c0_hsteps
                                                exact hBp (cur_n, slotp, pp, ()) _
                                                  ⟨scrp_s,
                                                   slotMigOk_set_cur hmigp hcurl hcur_ne
                                                     (by rw [hmigp.1]; omega),
                                                   hkeep_n, hcur_n, hunm_n, hm_s⟩
                                              · intro Jc hJc; c0_hsplit
                                                · have hdst_lt : dst.toNat < ht_off.toNat := by
                                                    simp only [hs6a, hht_nat] at hc
                                                    have hg : scrp[(ht_off + slotp).toNat]'hsl_arr =
                                                        scrp[(ht_off.toNat + BitVec.toNat slotp) %
                                                          2 ^ 64]'
                                                          (by rw [hscrpl, Nat.mod_eq_of_lt
                                                            (by omega)]; omega) :=
                                                      list_getElem_congr
                                                        (by rw [hsl_add_n, Nat.mod_eq_of_lt
                                                          (by omega)])
                                                        hsl_arr
                                                        (by rw [hscrpl, Nat.mod_eq_of_lt
                                                          (by omega)]; omega)
                                                    exact congrArg BitVec.toNat hg ▸ hc
                                                  have h6' : (ctrl_off + (6 : BitVec 64)).toNat =
                                                      ctrl_off.toNat + 6 := h6n
                                                  have hdst_raw :
                                                      scrp[(BitVec.setWidth 64
                                                        (s.scratch.scratch_buf[(ctrl_off +
                                                          (6 : BitVec 64)).toNat]'
                                                          (by rw [hscrl, h6']; omega)) +
                                                        slotp).toNat]'
                                                        (by rw [hs6b]; exact hsl_arr) = dst :=
                                                    list_getElem_congr
                                                      (congrArg (fun x => (BitVec.setWidth 64 x +
                                                        slotp).toNat) hs6b)
                                                      (by rw [hs6b]; exact hsl_arr) hsl_arr
                                                  have hdec_unm : (List.range new_sz.toNat).countP
                                                      (fun k => htUnmigPred
                                                        (scrp_s[ht_off.toNat + k]?.getD
                                                          0xFFFFFFFF#32)) + 1 ≤
                                                      (List.range new_sz.toNat).countP (fun k =>
                                                        htUnmigPred (scrp[ht_off.toNat + k]?.getD
                                                          0xFFFFFFFF#32)) := by
                                                    have hu := range_countP_set
                                                      (w := curl ||| 0x80000000#32) htUnmigPred
                                                      (pos := slotp.toNat) (n := new_sz.toNat)
                                                      (scr := scrp) (ht_off := ht_off.toNat)
                                                      (by omega) (by rw [hscrpl]; omega)
                                                    have hpd : htUnmigPred dst = true :=
                                                      decide_eq_true ⟨hdst_ne, hdst_msb⟩
                                                    have hpc :
                                                        htUnmigPred (curl ||| 0x80000000#32) =
                                                          false :=
                                                      decide_eq_false (fun ⟨_, h⟩ =>
                                                        htOr8000_msb_ne_zero curl h)
                                                    rw [hdst_get, Option.getD_some, hpd, hpc] at hu
                                                    simp only [Bool.false_eq_true,
                                                      ↓reduceIte] at hu
                                                    dsimp only [scrp_s]; omega
                                                  c0_hsteps; try simp only [hdst_raw]
                                                  exact hJc (dst, ()) _ ⟨rfl,
                                                    curMigOk_of_slot hmigp hslot_lt hdst_get
                                                      hdst_ne hdst_msb hdst_lt,
                                                    slotKeepOk_set_mig_swap hkeepp hcur_ne hcurl_lt
                                                      hok_read.2.2.2.1 (by omega)
                                                      (by rw [hscrpl]; omega) hdst_get hdst_ne
                                                      hdst_msb (Or.inl ⟨hdst_lt, rfl⟩),
                                                    Or.inr (by subst hscrp_eq; omega)⟩
                                                · have hdst_ge : ht_off.toNat ≤ dst.toNat := by
                                                    simp only [hs6a, hht_nat] at hc
                                                    have hg : scrp[(ht_off + slotp).toNat]'hsl_arr =
                                                        scrp[(ht_off.toNat + BitVec.toNat slotp) %
                                                          2 ^ 64]'
                                                          (by rw [hscrpl, Nat.mod_eq_of_lt
                                                            (by omega)]; omega) :=
                                                      list_getElem_congr
                                                        (by rw [hsl_add_n, Nat.mod_eq_of_lt
                                                          (by omega)])
                                                        hsl_arr
                                                        (by rw [hscrpl, Nat.mod_eq_of_lt
                                                          (by omega)]; omega)
                                                    have hc' := Nat.not_lt.mp hc
                                                    exact (congrArg BitVec.toNat hg) ▸ hc'
                                                  c0_hsteps; exact hJc (0xFFFFFFFF#32, ()) _
                                                    ⟨rfl, Or.inl rfl,
                                                     slotKeepOk_set_mig_swap hkeepp hcur_ne hcurl_lt
                                                       hok_read.2.2.2.1 (by omega)
                                                       (by rw [hscrpl]; omega) hdst_get hdst_ne
                                                       hdst_msb (Or.inr ⟨hdst_ge, rfl⟩),
                                                     Or.inl rfl⟩
                                            · have hpp1 : (pp + 1#64).toNat = pp.toNat + 1 :=
                                                bv64_add1_lt hpp_lt (by omega)
                                              have hnoemp' : ∀ m < (pp + 1#64).toNat,
                                                  scrp[ht_off.toNat +
                                                    (slot0.toNat + m) % new_sz.toNat]? ≠
                                                    some 0xFFFFFFFF#32 := by
                                                intro m hm_m; rw [hpp1] at hm_m
                                                rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hm_m)
                                                    with hm1 | rfl
                                                · exact hnoemp m hm1
                                                · rw [← hslot_mod]
                                                  intro he
                                                  rw [List.getElem?_eq_getElem
                                                      (by rw [hmigp.1]; omega),
                                                    Option.some.injEq] at he
                                                  apply hdst_ne
                                                  exact (list_getElem_congr
                                                    hsl_add_n hsl_arr _) ▸ he
                                              have hnext_slot :
                                                  ((slotp + 1#64) &&& (new_sz - 1#64)).toNat =
                                                    (slot0.toNat + (pp + 1#64).toNat) %
                                                      new_sz.toNat := by
                                                rw [bv64_and_pow2_mod (k := k_exp + 1) (by omega)
                                                    (by rw [hnew_n, hos_pow, Nat.pow_succ]; omega),
                                                  bv64_add1_lt hslot_lt (by omega), hpp1]
                                                exact mod_add_one_eq hslot_mod
                                              c0_hsteps; try simp only [hs7b]
                                              exact hLp (new_sz.toNat - (pp + 1#64).toNat)
                                                ((slotp + 1#64) &&& (new_sz - 1#64), pp + 1#64, ())
                                                mp (by omega)
                                                ⟨scrp, hscrp_eq, hmigp, hkeepp, hnext_slot,
                                                  hnoemp', bv64_and_sub1_lt (by omega),
                                                  by omega, rfl, hmp⟩
                                        · exfalso
                                          have hpp_eq : pp.toNat = new_sz.toNat := by
                                            rw [hs7a, hos_nat, Nat.mod_eq_of_lt
                                                (by unfold m7CongHashMaxSz at hlt_max; omega),
                                              ← hnew_n] at hc
                                            exact Nat.le_antisymm hpp_le (Nat.not_lt.mp hc)
                                          obtain ⟨k_emp, hk_emp, hget_emp⟩ :=
                                            slotKeepOk_empty_exists hkeepp (by omega)
                                              (by rw [hmigp.1]; omega)
                                          obtain ⟨m_hit, hm_hit, hmod_hit⟩ :=
                                            probe_visit_idx (hv := slot0.toNat) hk_emp
                                          exact hnoemp m_hit (by omega) (by rwa [hmod_hit])
                                      · intro _ Lp _ hLp
                                        have hslot0_eq :
                                            slot0.toNat = (slot0.toNat + 0) % new_sz.toNat := by
                                          rw [Nat.add_zero, Nat.mod_eq_of_lt hslot0_lt]
                                        c0_hsteps; try simp only [hs7b]
                                        exact hLp new_sz.toNat (slot0, 0#64, ())
                                          ml ⟨scrl, rfl, hmigl, hkeepl, by
                                            change slot0.toNat = (slot0.toNat + 0) % new_sz.toNat
                                            exact hslot0_eq,
                                            fun _ hm0 => by simp at hm0, hslot0_lt,
                                            Nat.zero_le _, rfl, hml⟩
                                    · exfalso
                                      have hhops_eq : hops.toNat = new_sz.toNat := by
                                        rw [hs7a, hos_nat, Nat.mod_eq_of_lt
                                            (by unfold m7CongHashMaxSz at hlt_max; omega),
                                          ← hnew_n] at hc
                                        exact Nat.le_antisymm hhops_le (Nat.not_lt.mp hc)
                                      omega
                                  · intro _ Lh _ hLh
                                    have h6' : (ctrl_off + (6 : BitVec 64)).toNat =
                                        ctrl_off.toNat + 6 := h6n
                                    have hraw_raw :
                                        scri[(BitVec.setWidth 64
                                          (s.scratch.scratch_buf[(ctrl_off +
                                            (6 : BitVec 64)).toNat]'
                                            (by rw [hscrl, h6']; omega)) + i).toNat]'
                                          (by rw [hs6b]; exact hi_add_arr) = raw :=
                                      list_getElem_congr
                                        (congrArg (fun x => (BitVec.setWidth 64 x + i).toNat) hs6b)
                                        (by rw [hs6b]; exact hi_add_arr) hi_add_arr
                                    have hunm_b0 : (List.range new_sz.toNat).countP (fun k =>
                                        htUnmigPred (scrb0[ht_off.toNat + k]?.getD 0xFFFFFFFF#32)) +
                                        1 + (0#64 : BitVec 64).toNat ≤ old_sz.toNat := by
                                      have hu := hkeep_b0.2.1
                                      rw [ite_eq_right hraw_ne] at hu
                                      change _ + 1 + 0 ≤ _; omega
                                    c0_hsteps; try simp only [hraw_raw]
                                    exact hLh new_sz.toNat (raw, 0#64, ()) _
                                      ⟨scrb0, hmig_b0, hkeep_b0, hcur_ok0, hraw_ne, Nat.zero_le _,
                                        hunm_b0, rfl, hm_b0⟩
                                · c0_hsteps; exact hJj _ ⟨scri, hmigi, hkeepi, by assumption⟩
                              · c0_hsteps; exact hJj _ ⟨scri, hmigi, hkeepi, by assumption⟩
                            · c0_hsteps; exact hJj _ ⟨scri, hmigi, hkeepi, by assumption⟩
                          · have hi_eq : i.toNat = old_sz.toNat := by
                              rw [hs7a, hos_nat] at hc
                              exact Nat.le_antisymm hi_le (Nat.not_lt.mp hc)
                            clear hc; c0_hsteps_nogrp
                            refine wp_loop_inv (ts := [i64])
                              (fun ⟨j, ⟨⟩⟩ mj => ∃ scrj : List (BitVec 32),
                                scrj.length = c.scratch_cap ∧ j.toNat ≤ new_sz.toNat ∧
                                (∀ idx < ht_off.toNat, scrj[idx]? = s.scratch.scratch_buf[idx]?) ∧
                                old_sz.toNat ≤ (List.range new_sz.toNat).countP (fun k =>
                                  htEmptyPred (scrj[ht_off.toNat + k]?.getD 0xFFFFFFFF#32)) ∧
                                (∀ v : BitVec 32, v.toNat < ht_off.toNat →
                                  (∃ k0 < old_sz.toNat,
                                    s.scratch.scratch_buf[ht_off.toNat + k0]? = some v) →
                                  (∃ q, j.toNat ≤ q ∧ q < new_sz.toNat ∧
                                    (scrj[ht_off.toNat + q]? = some v ∨
                                      scrj[ht_off.toNat + q]? = some (v ||| 0x80000000#32))) ∨
                                  (∃ q < j.toNat, scrj[ht_off.toNat + q]? = some v)) ∧
                                (∀ q, j.toNat ≤ q → q < new_sz.toNat →
                                  scrj[ht_off.toNat + q]? = some 0xFFFFFFFF#32 ∨
                                  ∃ k0 < old_sz.toNat, ∃ r0 : BitVec 32,
                                    s.scratch.scratch_buf[ht_off.toNat + k0]? = some r0 ∧
                                    r0 ≠ 0xFFFFFFFF#32 ∧
                                    (scrj[ht_off.toNat + q]? = some r0 ∨
                                      scrj[ht_off.toNat + q]? = some (r0 ||| 0x80000000#32))) ∧
                                (∀ q < j.toNat,
                                  scrj[ht_off.toNat + q]? = some 0xFFFFFFFF#32 ∨
                                  ∃ k0 < old_sz.toNat, ∃ r0 : BitVec 32,
                                    s.scratch.scratch_buf[ht_off.toNat + k0]? = some r0 ∧
                                    r0 ≠ 0xFFFFFFFF#32 ∧
                                    scrj[ht_off.toNat + q]? = some (r0 &&& 0x7FFFFFFF#32)) ∧
                                (array (t := i32) c.pScratchBuf scrj ⋆ R_scr) mj)
                              (fun ⟨j, ⟨⟩⟩ _ => new_sz.toNat - j.toNat)
                              (fun Jj hJj => by
                                have hemp0 := hkeepi.1
                                simp only [↓reduceIte, Nat.add_zero] at hemp0
                                c0_hsteps; exact hJj (0#64, ()) mi ⟨scri, hmigi.1, Nat.zero_le _,
                                  hmigi.2.1, hemp0, fun v hv hex => by
                                    rcases hkeepi.2.2 v hv hex with hbad | ⟨q, hq, hslot⟩
                                    · have hff : (0xFFFFFFFF#32 : BitVec 32).toNat = 0xFFFFFFFF :=
                                        by decide
                                      rw [← hbad, hff] at hv; omega
                                    · exact Or.inl ⟨q, Nat.zero_le _, hq, hslot⟩,
                                  fun q _ hq => hmigi.2.2 q hq,
                                  fun _ h => by simp at h, hmi⟩)
                              (fun Jj ⟨j, ⟨⟩⟩ mj
                                  ⟨scrj, hscrjl, hj_le, hprej, hempj, hkeepj, htailj, hdonej, hmj⟩
                                  ihj => ?_)
                            c0_hsplit
                            · have hj_lt : j.toNat < new_sz.toNat := by
                                rw [hs7a, hos_nat, Nat.mod_eq_of_lt
                                    (by unfold m7CongHashMaxSz at hlt_max; omega),
                                  ← hnew_n] at hc
                                exact hc
                              have hj_add_n : (ht_off + j).toNat = ht_off.toNat + j.toNat :=
                                bv64_add_toNat (by omega)
                              have hj_add_arr : (ht_off + j).toNat < scrj.length := by
                                rw [hj_add_n, hscrjl]; omega
                              have hj1_n : (j + 1#64).toNat = j.toNat + 1 :=
                                bv64_add1_lt hj_lt (by omega)
                              clear hc; c0_hsteps_nogrp
                              refine wp_join0
                                (fun m1 => ∃ scr1 : List (BitVec 32),
                                  scr1.length = c.scratch_cap ∧
                                  (∀ idx < ht_off.toNat, scr1[idx]? = s.scratch.scratch_buf[idx]?) ∧
                                  old_sz.toNat ≤ (List.range new_sz.toNat).countP (fun k =>
                                    htEmptyPred (scr1[ht_off.toNat + k]?.getD 0xFFFFFFFF#32)) ∧
                                  (∀ v : BitVec 32, v.toNat < ht_off.toNat →
                                    (∃ k0 < old_sz.toNat,
                                      s.scratch.scratch_buf[ht_off.toNat + k0]? = some v) →
                                    (∃ q, j.toNat + 1 ≤ q ∧ q < new_sz.toNat ∧
                                      (scr1[ht_off.toNat + q]? = some v ∨
                                        scr1[ht_off.toNat + q]? = some (v ||| 0x80000000#32))) ∨
                                    (∃ q < j.toNat + 1, scr1[ht_off.toNat + q]? = some v)) ∧
                                  (∀ q, j.toNat + 1 ≤ q → q < new_sz.toNat →
                                    scr1[ht_off.toNat + q]? = some 0xFFFFFFFF#32 ∨
                                    ∃ k0 < old_sz.toNat, ∃ r0 : BitVec 32,
                                      s.scratch.scratch_buf[ht_off.toNat + k0]? = some r0 ∧
                                      r0 ≠ 0xFFFFFFFF#32 ∧
                                      (scr1[ht_off.toNat + q]? = some r0 ∨
                                        scr1[ht_off.toNat + q]? = some (r0 ||| 0x80000000#32))) ∧
                                  (∀ q < j.toNat + 1,
                                    scr1[ht_off.toNat + q]? = some 0xFFFFFFFF#32 ∨
                                    ∃ k0 < old_sz.toNat, ∃ r0 : BitVec 32,
                                      s.scratch.scratch_buf[ht_off.toNat + k0]? = some r0 ∧
                                      r0 ≠ 0xFFFFFFFF#32 ∧
                                      scr1[ht_off.toNat + q]? = some (r0 &&& 0x7FFFFFFF#32)) ∧
                                  (array (t := i32) c.pScratchBuf scr1 ⋆ R_scr) m1)
                                (fun _ m1 ⟨scr1, h1', h2', he1', hk1', h3', h4', hm1⟩ => by
                                  c0_hsteps
                                  exact ihj (j + 1#64, ()) m1 (by dsimp only; rw [hj1_n]; omega)
                                    ⟨scr1, h1', by rw [hj1_n]; omega, h2', he1',
                                      fun v hv hex => by
                                        rw [← hj1_n] at *; exact hk1' v hv hex,
                                      fun q hq1 hq2 => h3' q (by rw [← hj1_n]; exact hq1) hq2,
                                      fun q hq => h4' q (by rw [← hj1_n]; exact hq), hm1⟩)
                                (fun J8 hJ8 => ?_)
                              c0_hsplit
                              · have hv_ne :
                                    scrj[(ht_off + j).toNat]'hj_add_arr ≠ 0xFFFFFFFF#32 := by
                                  simp only [hs6a, hht_nat] at hc; exact hc
                                let v := scrj[(ht_off + j).toNat]'hj_add_arr
                                have hv_get : scrj[ht_off.toNat + j.toNat]? = some v := by
                                  rw [List.getElem?_eq_getElem (by rw [hscrjl]; omega)]
                                  congr 1; exact (list_getElem_congr hj_add_n hj_add_arr _).symm
                                clear hc; c0_hsteps
                                let scr1 := scrj.set (ht_off.toNat + j.toNat) (v &&& 0x7FFFFFFF#32)
                                have hm1' : (array (t := i32) c.pScratchBuf scr1 ⋆ R_scr) m := by
                                  refine (congrArg
                                    (fun arr => (array (t := i32) c.pScratchBuf arr ⋆ R_scr) m)
                                    ?_).mp hm
                                  dsimp only [scr1, v]
                                  have h6' : (ctrl_off + (6 : BitVec 64)).toNat =
                                      ctrl_off.toNat + 6 := h6n
                                  have hj_con : (BitVec.setWidth 64
                                      (s.scratch.scratch_buf[(ctrl_off + (6 : BitVec 64)).toNat]'
                                        (by rw [hscrl, h6']; omega)) + j).toNat =
                                      ht_off.toNat + j.toNat := by
                                    rw [hs6b]; exact hj_add_n
                                  have hset_eq : ∀ {α : Type} (xs : List α) {i1 i2 : Nat}
                                      {a b : α}, i1 = i2 → a = b → xs.set i1 a = xs.set i2 b := by
                                    rintro _ _ _ _ _ _ rfl rfl; rfl
                                  exact hset_eq scrj hj_con (by
                                    congr 1
                                    exact list_getElem_congr (hj_con.trans hj_add_n.symm)
                                      (by rw [hscrjl, hj_con]; omega) hj_add_arr)
                                have hemp1 : old_sz.toNat ≤
                                    (List.range new_sz.toNat).countP (fun k =>
                                      htEmptyPred
                                        (scr1[ht_off.toNat + k]?.getD 0xFFFFFFFF#32)) := by
                                  have he_set := range_countP_set (scr := scrj)
                                    (ht_off := ht_off.toNat) (w := v &&& 0x7FFFFFFF#32)
                                    htEmptyPred hj_lt (by rw [hscrjl]; omega)
                                  have hv7_ne : v &&& 0x7FFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
                                    intro h
                                    have hlt : (v &&& 0x7FFFFFFF#32).toNat ≤ 0x7FFFFFFF := by
                                      have h7 :
                                          (0x7FFFFFFF#32 : BitVec 32).toNat = 0x7FFFFFFF := by
                                        decide
                                      rw [BitVec.toNat_and, h7]
                                      exact Nat.and_le_right
                                    have hff :
                                        (0xFFFFFFFF#32 : BitVec 32).toNat = 0xFFFFFFFF := by
                                      decide
                                    rw [h, hff] at hlt; omega
                                  have hpe_v : htEmptyPred v = false := decide_eq_false hv_ne
                                  have hpe_v7 : htEmptyPred (v &&& 0x7FFFFFFF#32) = false :=
                                    decide_eq_false hv7_ne
                                  rw [hv_get, Option.getD_some, hpe_v, hpe_v7] at he_set
                                  simp only [Bool.false_eq_true, ↓reduceIte] at he_set
                                  dsimp only [scr1]; omega
                                refine hJ8 _ ⟨scr1, by simp [scr1, hscrjl],
                                  fun idx hi => by
                                    rw [List.getElem?_set_ne (by omega)]; exact hprej idx hi,
                                  hemp1,
                                  fun w hw_lt hex => by
                                    rcases hkeepj w hw_lt hex with
                                        ⟨q, hqj, hqn, hqslot⟩ | ⟨q, hqj, hqslot⟩
                                    · by_cases hqj_eq : q = j.toNat
                                      · subst hqj_eq; right; refine ⟨j.toNat, by omega, ?_⟩
                                        dsimp only [scr1]
                                        rw [List.getElem?_set_self (by rw [hscrjl]; omega),
                                          Option.some.injEq]
                                        rw [hv_get] at hqslot
                                        rcases hqslot with hw1 | hw1
                                        · rw [Option.some.inj hw1, bv32_and7fff_of_lt (by omega)]
                                        · rw [Option.some.inj hw1, bv32_or8000_and7fff,
                                            bv32_and7fff_of_lt (by omega)]
                                      · left; refine ⟨q, by omega, hqn, ?_⟩
                                        dsimp only [scr1]
                                        rw [List.getElem?_set_ne (by omega)]; exact hqslot
                                    · right; refine ⟨q, by omega, ?_⟩
                                      dsimp only [scr1]
                                      rw [List.getElem?_set_ne (by omega)]; exact hqslot,
                                  fun q hq1 hq2 => by
                                    rw [List.getElem?_set_ne (by omega)]
                                    exact htailj q (by omega) hq2,
                                  fun q hq => ?_, hm1'⟩
                                by_cases hqj : q = j.toNat
                                · subst hqj; right
                                  rcases htailj j.toNat (Nat.le_refl _) hj_lt with hem |
                                      ⟨k0, hk0, r0, hr0g, hr0ne, hr0e⟩
                                  · rw [hv_get] at hem; exact absurd (Option.some.inj hem) hv_ne
                                  · refine ⟨k0, hk0, r0, hr0g, hr0ne, ?_⟩
                                    rw [List.getElem?_set_self (by rw [hscrjl]; omega)]; congr 1
                                    rw [hv_get] at hr0e
                                    rcases hr0e with hr | hr
                                    · rw [Option.some.inj hr]
                                    · rw [Option.some.inj hr, bv32_or8000_and7fff]
                                · rw [List.getElem?_set_ne (by omega)]; exact hdonej q (by omega)
                              · have hv_get :
                                    scrj[ht_off.toNat + j.toNat]? = some 0xFFFFFFFF#32 := by
                                  simp only [hs6a, hht_nat] at hc
                                  have hmod_n : (ht_off.toNat + BitVec.toNat j) % 2 ^ 64 =
                                      ht_off.toNat + j.toNat := Nat.mod_eq_of_lt (by omega)
                                  rw [List.getElem?_eq_getElem (by rw [hscrjl]; omega)]
                                  congr 1
                                  rw [← list_getElem_congr hmod_n (by rw [hscrjl, hmod_n]; omega)
                                    (by rw [hscrjl]; omega), hc]
                                  rfl
                                have hkeep1 : ∀ w : BitVec 32, w.toNat < ht_off.toNat →
                                    (∃ k0 < old_sz.toNat,
                                      s.scratch.scratch_buf[ht_off.toNat + k0]? = some w) →
                                    (∃ q, j.toNat + 1 ≤ q ∧ q < new_sz.toNat ∧
                                      (scrj[ht_off.toNat + q]? = some w ∨
                                        scrj[ht_off.toNat + q]? = some (w ||| 0x80000000#32))) ∨
                                    (∃ q < j.toNat + 1, scrj[ht_off.toNat + q]? = some w) := by
                                  intro w hw_lt hex
                                  rcases hkeepj w hw_lt hex with
                                      ⟨q, hqj, hqn, hqslot⟩ | ⟨q, hqj, hqslot⟩
                                  · by_cases hqj_eq : q = j.toNat
                                    · subst hqj_eq; rw [hv_get] at hqslot
                                      exfalso
                                      have hw_ne : w ≠ 0xFFFFFFFF#32 := by
                                        have hff :
                                            (0xFFFFFFFF#32 : BitVec 32).toNat = 0xFFFFFFFF := by
                                          decide
                                        intro h; rw [h, hff] at hw_lt; omega
                                      have hwo_ne : w ||| 0x80000000#32 ≠ 0xFFFFFFFF#32 :=
                                        htOr8000_ne_ff (by omega)
                                      rcases hqslot with h1 | h1
                                      · exact hw_ne (Option.some.inj h1).symm
                                      · exact hwo_ne (Option.some.inj h1).symm
                                    · exact Or.inl ⟨q, by omega, hqn, hqslot⟩
                                  · exact Or.inr ⟨q, by omega, hqslot⟩
                                c0_hsteps; refine hJ8 mj ⟨scrj, hscrjl, hprej, hempj, hkeep1,
                                  fun q hq1 hq2 => htailj q (by omega) hq2, fun q hq => ?_, hmj⟩
                                by_cases hqj : q = j.toNat
                                · subst hqj; left; exact hv_get
                                · exact hdonej q (by omega)
                            · have hj_eq : j.toNat = new_sz.toNat := by
                                rw [hs7a, hos_nat, Nat.mod_eq_of_lt
                                    (by unfold m7CongHashMaxSz at hlt_max; omega),
                                  ← hnew_n] at hc
                                exact Nat.le_antisymm hj_le (Nat.not_lt.mp hc)
                              rw [hj_eq] at hdonej hkeepj; clear hc
                              have h7n' : (ctrl_off + (7 : BitVec 64)).toNat = ctrl_off.toNat + 7 :=
                                bv64_add_ofNat_toNat 7 (by decide) (by omega)
                              have hco7_arr' :
                                  (ctrl_off + (7 : BitVec 64)).toNat < scrj.length := by
                                rw [hscrjl, h7n']; omega
                              let scr_fin := scrj.set (ctrl_off.toNat + 7) (new_sz.setWidth 32)
                              have hfin_len : scr_fin.length = c.scratch_cap := by
                                simp [scr_fin, hscrjl]
                              have hco6_fin : scr_fin[ctrl_off.toNat + 6]? =
                                  some (BitVec.ofNat 32 ht_off.toNat) := by
                                dsimp only [scr_fin]
                                rw [List.getElem?_set_ne (by omega), hprej _ (by omega)]
                                exact hok_read.2.2.2.2.2.1
                              have hco7_fin : scr_fin[ctrl_off.toNat + 7]? =
                                  some (BitVec.ofNat 32 (2 * old_sz.toNat)) := by
                                dsimp only [scr_fin]
                                rw [List.getElem?_set_self (by rw [hscrjl]; omega)]
                                congr 1; apply BitVec.eq_of_toNat_eq
                                rw [bv64_trunc32_toNat (by omega), hnew_n,
                                  bv32_ofNat_toNat_lt (by omega)]
                              have hpref_fin : ∀ idx < ht_off.toNat, idx ≠ ctrl_off.toNat + 7 →
                                  scr_fin[idx]? = s.scratch.scratch_buf[idx]? := by
                                intro idx hidx hne7
                                dsimp only [scr_fin]
                                rw [List.getElem?_set_ne (Ne.symm hne7)]
                                exact hprej idx hidx
                              have hemp_fin : ∃ q < 2 * old_sz.toNat,
                                  scr_fin[ht_off.toNat + q]? = some 0xFFFFFFFF#32 := by
                                have hgt : 0 < (List.range new_sz.toNat).countP (fun k =>
                                    htEmptyPred (scrj[ht_off.toNat + k]?.getD 0xFFFFFFFF#32)) := by
                                  omega
                                obtain ⟨q, hq, hpred⟩ := range_countP_pos_exists hgt
                                rw [List.getElem?_eq_getElem (by rw [hscrjl]; omega),
                                  Option.getD_some] at hpred
                                refine ⟨q, by omega, ?_⟩
                                dsimp only [scr_fin]
                                rw [List.getElem?_set_ne (by omega),
                                  List.getElem?_eq_getElem (by rw [hscrjl]; omega),
                                  decide_eq_true_eq.mp hpred]
                              have hkeep_fin : ∀ w : BitVec 32, w.toNat < ht_off.toNat →
                                  (∃ k0 < old_sz.toNat,
                                    s.scratch.scratch_buf[ht_off.toNat + k0]? = some w) →
                                  ∃ q < 2 * old_sz.toNat,
                                    scr_fin[ht_off.toNat + q]? = some w := by
                                intro w hw_lt hex
                                rcases hkeepj w hw_lt hex with
                                    ⟨q, hq1, hq2, _⟩ | ⟨q, hq, hget_q⟩
                                · exact absurd hq2 (by omega)
                                · refine ⟨q, by omega, ?_⟩
                                  dsimp only [scr_fin]
                                  rw [List.getElem?_set_ne (by omega)]; exact hget_q
                              subst hR_scr
                              c0_hsteps
                              have hm_fin : (array (t := i32) c.pScratchBuf scr_fin ⋆
                                  (FullScrBufRest c s ⋆ R)) m := by
                                refine (congrArg
                                  (fun arr => (array (t := i32) c.pScratchBuf arr ⋆
                                    (FullScrBufRest c s ⋆ R)) m) ?_).mp hm
                                dsimp only [scr_fin]
                                have hset_eq : ∀ {α : Type} (xs : List α) {i1 i2 : Nat}
                                    {a b : α}, i1 = i2 → a = b → xs.set i1 a = xs.set i2 b := by
                                  rintro _ _ _ _ _ _ rfl rfl; rfl
                                have h1eq : (1 : Nat) = (BitVec.signExtend 64 1#32).toNat := by
                                  decide
                                refine hset_eq scrj h7n' ?_
                                simp only [hs7b]
                                exact congrArg
                                  (fun x : Nat => BitVec.setWidth 32 (old_sz <<< x)) h1eq
                              try simp only [hs7b]
                              refine hQ new_sz scr_fin m hfin_len
                                (scr_state_core_pres hlen scr_fin hfin_len s.scratch.res_sz).1
                                rfl ⟨rfl, rfl⟩ (fun ho os hok => ?_)
                                (fun hno => False.elim (hno _ _ hok_read))
                                (unfocus_full_scratch_buf ?_)
                              · obtain ⟨rfl, rfl⟩ := m7CongHtCtrlOk_match_reads hco8 hscrl hho_eq
                                  hsz_eq hok
                                refine ⟨fun hbad => by
                                    rcases hbad with h1' | h2'
                                    · exact absurd hlt_max (Nat.not_lt.mpr h1')
                                    · exact absurd hfit (Nat.not_le.mpr h2'),
                                  fun _ _ => ⟨hnew_n, by
                                    have hok' := m7CongHtCtrlOk_grow hk_lt13
                                      (by simpa [hos_pow] using hok_read)
                                      hfin_len (by rw [← hos_pow]; exact hfit) hco6_fin
                                      (by rw [← hos_pow]; exact hco7_fin)
                                    rwa [← hos_pow] at hok', hpref_fin, hemp_fin, hkeep_fin,
                                    fun q hq => by
                                      have hne_7 : ctrl_off.toNat + 7 ≠ ht_off.toNat + q := by
                                        omega
                                      dsimp only [scr_fin]
                                      rw [List.getElem?_set_ne hne_7]
                                      exact hdonej q (by rwa [hnew_n])⟩⟩
                              · exact hm_fin

/-- **#3b (`full_cong_ht_grow_clear_m7_wp`)**: doubles `ctrl[7]` up to `min 131072 (cap - ht_off)`,
clears `scr[ht_off ..< ht_off + new_sz)`, and resets `res_sz = 0` for canonical `eval_gate`
re-population, capping safely at `old_sz` without wipe when headroom is tight. -/
theorem full_cong_ht_grow_clear_m7_wp (Γ : Env) :
    ∀ a m Q X, m7CongHtGrowClearSpec a m Q X →
      Func.wp Γ full_cong_ht_grow_clear_m7_body a m Q X := by
  rintro ⟨h, ctrl_off, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hlen, hm0, hQ⟩
  have hsc := c.hscr; unfold dimacsBound at hsc
  have hscrl := hlen.scratch_ok.scratch_buf_len
  have hfail_noctrl : ∀ ret : BitVec 64,
      (∀ ht_off old_sz, M7CongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ht_off old_sz →
        False) →
      Q (ret, ()) m0 := fun ret hno =>
    hQ ret s.scratch.scratch_buf s.scratch.res_sz m0 hscrl hlen rfl ⟨rfl, rfl⟩
      (fun ht os h => False.elim (hno ht os h)) (fun _ => ⟨rfl, rfl⟩) hm0
  unfold Func.wp full_cong_ht_grow_clear_m7_body
  c0_hsplit
  · c0_hsteps; exact hfail_noctrl 0#64 (fun _ _ hok => by
      have := hok.2.1; have := hok.2.2.1; m7_omega)
  · have hco_le : ctrl_off.toNat ≤ c.scratch_cap := by m7_omega
    clear hc; c0_hsplit
    · c0_hsteps; exact hfail_noctrl 0#64 (fun _ _ hok => by
        have := ctrl_off.isLt; have := hok.2.1; have := hok.2.2.1; m7_omega)
    · have hco8 : ctrl_off.toNat + 8 ≤ c.scratch_cap := by
        have := ctrl_off.isLt; m7_omega
      clear hc
      have h6n : (ctrl_off + 6#64).toNat = ctrl_off.toNat + 6 :=
        bv64_add_ofNat_toNat 6 (by decide) (by omega)
      have h7n : (ctrl_off + 7#64).toNat = ctrl_off.toNat + 7 :=
        bv64_add_ofNat_toNat 7 (by decide) (by omega)
      let ht_off_w := s.scratch.scratch_buf[ctrl_off.toNat + 6]'(by omega)
      let old_sz_w := s.scratch.scratch_buf[ctrl_off.toNat + 7]'(by omega)
      let ht_off : BitVec 64 := ht_off_w.setWidth 64
      let old_sz : BitVec 64 := old_sz_w.setWidth 64
      have hht_nat : ht_off_w.toNat = ht_off.toNat := (bv64_zext32_toNat _).symm
      have hos_nat : old_sz_w.toNat = old_sz.toNat := (bv64_zext32_toNat _).symm
      have hho_eq : ht_off = (s.scratch.scratch_buf[ctrl_off.toNat + 6]'(by omega)).setWidth 64 :=
        rfl
      have hsz_eq : old_sz = (s.scratch.scratch_buf[ctrl_off.toNat + 7]'(by omega)).setWidth 64 :=
        rfl
      have hs6a : s.scratch.scratch_buf[(BitVec.toNat ctrl_off + BitVec.toNat (6 : BitVec 64)) %
          2 ^ 64]'(by
          change (ctrl_off.toNat + 6) % 2 ^ 64 < s.scratch.scratch_buf.length
          rw [Nat.mod_eq_of_lt (by omega)]; omega) = ht_off_w :=
        scr_idx_add_imm 6 rfl (by omega) _ _
      have hs6b : s.scratch.scratch_buf[(ctrl_off + (6 : BitVec 64)).toNat]'(by
          change (ctrl_off.toNat + 6) % 2 ^ 64 < s.scratch.scratch_buf.length
          rw [Nat.mod_eq_of_lt (by omega)]; omega) = ht_off_w := hs6a
      have hs7a : s.scratch.scratch_buf[(BitVec.toNat ctrl_off + BitVec.toNat (7 : BitVec 64)) %
          2 ^ 64]'(by
          change (ctrl_off.toNat + 7) % 2 ^ 64 < s.scratch.scratch_buf.length
          rw [Nat.mod_eq_of_lt (by omega)]; omega) = old_sz_w :=
        scr_idx_add_imm 7 rfl (by omega) _ _
      have hs7b : s.scratch.scratch_buf[(ctrl_off + (7 : BitVec 64)).toNat]'(by
          change (ctrl_off.toNat + 7) % 2 ^ 64 < s.scratch.scratch_buf.length
          rw [Nat.mod_eq_of_lt (by omega)]; omega) = old_sz_w := hs7a
      have hbad_ht : ¬ (ctrl_off.toNat + 8 ≤ ht_off.toNat ∧ ht_off.toNat < c.scratch_cap ∧
          ht_off.toNat ≤ 0x7FFFFFFF) →
          ∀ ho os, M7CongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ho os → False :=
        fun hbad ho os hok => by
          apply hbad
          obtain ⟨rfl, rfl⟩ := m7CongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
          exact ⟨hok.2.1, Nat.lt_of_lt_of_le (by
              have ⟨k, _, he⟩ := hok.2.2.2.2.1; have := Nat.two_pow_pos k; omega) hok.2.2.1,
            hok.2.2.2.1⟩
      c0_hsplit
      · c0_hsteps; exact hfail_noctrl 0#64 (hbad_ht fun ⟨h1, _⟩ => by
          rw [hs6a, hht_nat] at hc
          change ht_off.toNat < (ctrl_off.toNat + BitVec.toNat 8) % 2 ^ 64 at hc; m7_omega)
      · have h1 : ctrl_off.toNat + 8 ≤ ht_off.toNat := by
          rw [hs6a, hht_nat] at hc
          change ¬ ht_off.toNat < (ctrl_off.toNat + BitVec.toNat 8) % 2 ^ 64 at hc; m7_omega
        clear hc; c0_hsplit
        · c0_hsteps; exact hfail_noctrl 0#64 (hbad_ht fun ⟨_, h2, _⟩ => by
            rw [hs6a, hht_nat] at hc
            change c.scratch_cap % 2 ^ 64 ≤ ht_off.toNat at hc; m7_omega)
        · have h2 : ht_off.toNat < c.scratch_cap := by
            rw [hs6a, hht_nat] at hc
            change ¬ c.scratch_cap % 2 ^ 64 ≤ ht_off.toNat at hc; m7_omega
          clear hc; c0_hsplit
          · c0_hsteps; exact hfail_noctrl 0#64 (hbad_ht fun ⟨_, _, h3⟩ => by
              rw [hs6a, hht_nat] at hc
              change BitVec.toNat 2147483647 < ht_off.toNat at hc; m7_omega)
          · have h3 : ht_off.toNat ≤ 0x7FFFFFFF := by
              rw [hs6a, hht_nat] at hc
              change ¬ BitVec.toNat 2147483647 < ht_off.toNat at hc; m7_omega
            clear hc
            have hbad_sz : ¬ (16 ≤ old_sz.toNat ∧ old_sz.toNat ≤ 131072 ∧
                (old_sz &&& (old_sz - 1#64)) = 0#64 ∧
                old_sz.toNat ≤ c.scratch_cap - ht_off.toNat) →
                ∀ ho os, M7CongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ho os → False :=
              fun hbad ho os hok => by
                apply hbad
                obtain ⟨rfl, rfl⟩ := m7CongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
                obtain ⟨k, hk, he⟩ := hok.2.2.2.2.1
                refine ⟨by rw [he]; have := Nat.two_pow_pos k; omega,
                  by rw [he]; exact pow2_16_mul_le k hk,
                  bv64_pow2_and_sub1_zero hk he,
                  by have := hok.2.2.1; omega⟩
            c0_hsplit
            · c0_hsteps; exact hfail_noctrl 0#64 (hbad_sz fun ⟨h4, _⟩ => by
                rw [hs7a, hos_nat] at hc
                change old_sz.toNat < BitVec.toNat 16 at hc; m7_omega)
            · have h4 : 16 ≤ old_sz.toNat := by
                rw [hs7a, hos_nat] at hc
                change ¬ old_sz.toNat < BitVec.toNat 16 at hc; m7_omega
              clear hc; c0_hsplit
              · c0_hsteps; exact hfail_noctrl 0#64 (hbad_sz fun ⟨_, hm, _⟩ => by
                  rw [hs7a, hos_nat] at hc
                  change BitVec.toNat 131072 < old_sz.toNat at hc; m7_omega)
              · have hmax : old_sz.toNat ≤ 131072 := by
                  rw [hs7a, hos_nat] at hc
                  change ¬ BitVec.toNat 131072 < old_sz.toNat at hc; m7_omega
                clear hc; c0_hsplit
                · c0_hsteps; exact hfail_noctrl 0#64 (hbad_sz fun ⟨_, _, h5, _⟩ => by
                    rw [hs7a] at hc; exact hc h5)
                · have h5 : (old_sz &&& (old_sz - 1#64)) = 0#64 := by
                    rw [hs7a] at hc; exact hc
                  clear hc; c0_hsplit
                  · c0_hsteps; exact hfail_noctrl 0#64 (hbad_sz fun ⟨_, _, _, h6⟩ => by
                      rw [hs6a, hht_nat, hs7a, hos_nat] at hc
                      change (2 ^ 64 - ht_off.toNat + c.scratch_cap) % 2 ^ 64 <
                        old_sz.toNat at hc
                      have := ht_off.isLt; m7_omega)
                  · have h6 : old_sz.toNat ≤ c.scratch_cap - ht_off.toNat := by
                      rw [hs6a, hht_nat, hs7a, hos_nat] at hc
                      change ¬ (2 ^ 64 - ht_off.toNat + c.scratch_cap) % 2 ^ 64 <
                        old_sz.toNat at hc
                      have := ht_off.isLt; m7_omega
                    clear hc
                    have hok_read : M7CongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat
                        ht_off.toNat old_sz.toNat :=
                      m7CongHtCtrlOk_from_reads hscrl hco8 hho_eq hsz_eq h1 h2 h3 h4 h5 h6 hmax
                    obtain ⟨k_exp, _, hos_pow⟩ := hok_read.2.2.2.2.1
                    c0_hsplit
                    · have heq_max : old_sz.toNat = 131072 := by
                        rw [hs7a] at hc; exact congrArg BitVec.toNat hc
                      c0_hsteps; try simp only [hs7b]
                      refine hQ old_sz s.scratch.scratch_buf s.scratch.res_sz m0 hscrl hlen rfl
                        ⟨rfl, rfl⟩ (fun ho os hok => ?_)
                        (fun hno => False.elim (hno _ _ hok_read)) hm0
                      obtain ⟨rfl, rfl⟩ := m7CongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
                      unfold m7CongHashMaxSz at *
                      exact ⟨fun _ => ⟨rfl, rfl, rfl⟩, fun hlt _ => absurd heq_max (by omega)⟩
                    · have hlt_max : old_sz.toNat < m7CongHashMaxSz := by
                        rw [hs7a] at hc
                        have hne : old_sz.toNat ≠ 131072 := fun h => hc (BitVec.eq_of_toNat_eq h)
                        unfold m7CongHashMaxSz; omega
                      have hk_lt13 : k_exp < 13 := by
                        rcases Nat.lt_or_ge k_exp 13 with hlt | hge
                        · exact hlt
                        · obtain rfl : k_exp = 13 := by omega
                          have h13 : 16 * 2 ^ 13 = 131072 := by decide
                          unfold m7CongHashMaxSz at hlt_max; omega
                      let new_sz : BitVec 64 := old_sz <<< (1#32 : BitVec 32).signExtend 64
                      have hnew_n : new_sz.toNat = 2 * old_sz.toNat :=
                        bv64_shl1_toNat (by unfold m7CongHashMaxSz at hlt_max; omega)
                      clear hc; c0_hsplit
                      · have hno_fit : c.scratch_cap < ht_off.toNat + 2 * old_sz.toNat := by
                          rw [hs6a, hht_nat, hs7a, hos_nat,
                            bv64_cap_sub_mod (Nat.le_of_lt h2) (by omega),
                            Nat.mod_eq_of_lt (by unfold m7CongHashMaxSz at hlt_max; omega)] at hc
                          omega
                        c0_hsteps; try simp only [hs7b]
                        refine hQ old_sz s.scratch.scratch_buf s.scratch.res_sz m0 hscrl hlen rfl
                          ⟨rfl, rfl⟩ (fun ho os hok => ?_)
                          (fun hno => False.elim (hno _ _ hok_read)) hm0
                        obtain ⟨rfl, rfl⟩ := m7CongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
                        exact ⟨fun _ => ⟨rfl, rfl, rfl⟩,
                          fun _ hfit => absurd hfit (Nat.not_le.mpr hno_fit)⟩
                      · have hfit : ht_off.toNat + 2 * old_sz.toNat ≤ c.scratch_cap := by
                          rw [hs6a, hht_nat, hs7a, hos_nat,
                            bv64_cap_sub_mod (Nat.le_of_lt h2) (by omega),
                            Nat.mod_eq_of_lt (by unfold m7CongHashMaxSz at hlt_max; omega)] at hc
                          omega
                        clear hc
                        have hfs := focus_full_scratch_buf hm0; clear hm0
                        generalize hR_scr : FullScrBufRest c s ⋆ R = R_scr at hfs
                        c0_hsteps_nogrp
                        refine wp_loop_inv (ts := [i64])
                          (fun ⟨k, ⟨⟩⟩ mk => ∃ scrk : List (BitVec 32),
                            scrk.length = c.scratch_cap ∧ k.toNat ≤ new_sz.toNat ∧
                            (∀ idx < ht_off.toNat, scrk[idx]? = s.scratch.scratch_buf[idx]?) ∧
                            (∀ j < k.toNat, scrk[ht_off.toNat + j]? = some 0xFFFFFFFF#32) ∧
                            (array (t := i32) c.pScratchBuf scrk ⋆ R_scr) mk)
                          (fun ⟨k, ⟨⟩⟩ _ => new_sz.toNat - k.toNat)
                          (fun Jk hJk => by
                            c0_hsteps; exact hJk (0#64, ()) m0 ⟨s.scratch.scratch_buf, hscrl,
                              Nat.zero_le _, fun _ _ => rfl, fun _ h => by simp at h, hfs⟩)
                          (fun Jk ⟨k, ⟨⟩⟩ mk ⟨scrk, hscrkl, hk_le, hpre, hclr, hmk⟩ ihk => ?_)
                        c0_hsplit
                        · have hk_lt : k.toNat < new_sz.toNat := by
                            rw [hs7a, hos_nat,
                              Nat.mod_eq_of_lt (by unfold m7CongHashMaxSz at hlt_max; omega),
                              ← hnew_n] at hc
                            exact hc
                          have hadd_n : (ht_off + k).toNat = ht_off.toNat + k.toNat :=
                            bv64_add_toNat (by omega)
                          have hadd_arr : (ht_off + k).toNat < scrk.length := by
                            rw [hadd_n]; omega
                          have hk1_n : (k + 1#64).toNat = k.toNat + 1 :=
                            bv64_add1_lt hk_lt (by omega)
                          c0_hsteps; try simp only [hs6b] at hm
                          rw [hadd_n] at hm
                          let scrk' := scrk.set (ht_off.toNat + k.toNat) 0xFFFFFFFF#32
                          refine ihk (k + 1#64, ()) _ (by dsimp only; rw [hk1_n]; omega)
                            ⟨scrk', by simp [scrk', hscrkl], by rw [hk1_n]; omega,
                              fun idx hi => by
                                rw [List.getElem?_set_ne (by omega)]; exact hpre idx hi,
                              fun j hj => by
                                rw [hk1_n] at hj
                                by_cases hjk : j = k.toNat
                                · subst hjk; rw [List.getElem?_set_self (by omega)]
                                · rw [List.getElem?_set_ne (by omega)]; exact hclr j (by omega),
                              hm⟩
                        · have hk_eq : k.toNat = new_sz.toNat := by
                            rw [hs7a, hos_nat,
                              Nat.mod_eq_of_lt (by unfold m7CongHashMaxSz at hlt_max; omega),
                              ← hnew_n] at hc
                            exact Nat.le_antisymm hk_le (Nat.not_lt.mp hc)
                          rw [hk_eq] at hclr; clear hc
                          have h7n' : (ctrl_off + (7 : BitVec 64)).toNat = ctrl_off.toNat + 7 :=
                            bv64_add_ofNat_toNat 7 (by decide) (by omega)
                          have hco7_arr' :
                              (ctrl_off + (7 : BitVec 64)).toNat < scrk.length := by
                            rw [hscrkl, h7n']; omega
                          let scr_fin := scrk.set (ctrl_off.toNat + 7) (new_sz.setWidth 32)
                          have hfin_len : scr_fin.length = c.scratch_cap := by
                            simp [scr_fin, hscrkl]
                          have hco6_fin : scr_fin[ctrl_off.toNat + 6]? =
                              some (BitVec.ofNat 32 ht_off.toNat) := by
                            dsimp only [scr_fin]
                            rw [List.getElem?_set_ne (by omega), hpre _ (by omega)]
                            exact hok_read.2.2.2.2.2.1
                          have hco7_fin : scr_fin[ctrl_off.toNat + 7]? =
                              some (BitVec.ofNat 32 (2 * old_sz.toNat)) := by
                            dsimp only [scr_fin]
                            rw [List.getElem?_set_self (by rw [hscrkl]; omega)]
                            congr 1; apply BitVec.eq_of_toNat_eq
                            rw [bv64_trunc32_toNat (by omega), hnew_n,
                              bv32_ofNat_toNat_lt (by omega)]
                          have hpref_fin : ∀ idx < ht_off.toNat, idx ≠ ctrl_off.toNat + 7 →
                              scr_fin[idx]? = s.scratch.scratch_buf[idx]? := by
                            intro idx hidx hne7
                            dsimp only [scr_fin]
                            rw [List.getElem?_set_ne (Ne.symm hne7)]
                            exact hpre idx hidx
                          have hclr_fin : ∀ q < 2 * old_sz.toNat,
                              scr_fin[ht_off.toNat + q]? = some 0xFFFFFFFF#32 := by
                            intro q hq
                            dsimp only [scr_fin]
                            rw [List.getElem?_set_ne (by omega)]
                            exact hclr q (by rwa [hnew_n])
                          subst hR_scr
                          have hm_un := unfocus_full_scratch_buf hmk; clear hmk
                          c0_hsteps
                          have hm_fin : (FullMem c { s with scratch :=
                              { s.scratch with scratch_buf := scr_fin, res_sz := 0#64 } } ⋆ R)
                              m := by
                            refine (congrArg (fun arr =>
                              (FullMem c { s with scratch :=
                                { s.scratch with scratch_buf := arr, res_sz := 0#64 } } ⋆ R)
                              m) ?_).mp hm
                            dsimp only [scr_fin]
                            have hset_eq : ∀ {α : Type} (xs : List α) {i1 i2 : Nat} {a b : α},
                                i1 = i2 → a = b → xs.set i1 a = xs.set i2 b := by
                              rintro _ _ _ _ _ _ rfl rfl; rfl
                            have h1eq : (1 : Nat) = (BitVec.signExtend 64 1#32).toNat := by
                              decide
                            refine hset_eq scrk h7n' ?_
                            simp only [hs7b]
                            exact congrArg (fun x : Nat => BitVec.setWidth 32 (old_sz <<< x)) h1eq
                          try simp only [hs7b]
                          refine hQ new_sz scr_fin 0#64 m hfin_len
                            (scr_state_core_pres hlen scr_fin hfin_len 0#64).1
                            rfl ⟨rfl, rfl⟩ (fun ho os hok => ?_)
                            (fun hno => False.elim (hno _ _ hok_read)) hm_fin
                          obtain ⟨rfl, rfl⟩ := m7CongHtCtrlOk_match_reads hco8 hscrl hho_eq
                            hsz_eq hok
                          refine ⟨fun hbad => by
                              rcases hbad with h1' | h2'
                              · exact absurd hlt_max (Nat.not_lt.mpr h1')
                              · exact absurd hfit (Nat.not_le.mpr h2'),
                            fun _ _ => ⟨hnew_n, by
                              have hok' := m7CongHtCtrlOk_grow hk_lt13
                                (by simpa [hos_pow] using hok_read)
                                hfin_len (by rw [← hos_pow]; exact hfit) hco6_fin
                                (by rw [← hos_pow]; exact hco7_fin)
                              rwa [← hos_pow] at hok', rfl, hpref_fin, hclr_fin⟩⟩

end WpProofs

end LeanQbe.T.Examples.Kissat.FullM7CongHash
