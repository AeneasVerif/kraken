/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityCongProof0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullCongLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.C0Agrees
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat 4.0.4 Congruence Hash Table Proofs (`FullFidelityCongProofHt`)

Parametric `(Γ : Env)` `Func.wp` proofs for all 6 upgraded dynamic hash-table functions in
`FullFidelityCong.lean` (`arity ≤ 64`, `ht_sz ≤ 1,048,576`):
1. `full_cong_ht_hash_ent_m7_wp` (`fidCongHtHashEntSpec`)
2. `full_cong_ht_init_m7_wp` (`fidCongHtInitSpec`)
3. `full_cong_ht_grow_m7_wp` (`fidCongHtGrowSpec`)
4. `full_cong_ht_grow_clear_m7_wp` (`fidCongHtGrowClearSpec`)
5. `full_cong_ht_lookup_m7_wp` (`fidCongHtLookupSpec`)
6. `full_cong_ht_insert_m7_wp` (`fidCongHtInsertSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityCong

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.FullM7CongHash (bv32_ofNat_toNat_lt bv64_ofNat_toNat_lt
  bv64_zext32_toNat bv64_add1_lt bv64_cap_sub_mod bv64_add_ofNat_toNat bv64_zext32_add_ofNat
  scr_idx_add_imm scr_idx_zext32_add1 scr_state_core_pres)
open Kraken.Bedrock2.Test

/-! ## 1. Pure BitVec & Power-of-2 Helpers (`≤ 1,048,576`) -/

section Helpers

private theorem fid_bv64_trunc32_toNat {x : BitVec 64} (hx : x.toNat < 2 ^ 32) :
    (x.setWidth 32).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx]

private theorem fid_bv64_sub_toNat {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)

private theorem fid_bv64_shl1_toNat {a : BitVec 64} (ha : 2 * a.toNat < 2 ^ 64) :
    (a <<< (1#32 : BitVec 32).signExtend 64).toNat = 2 * a.toNat := by
  change (a <<< (1 : Nat)).toNat = 2 * a.toNat
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
  exact Nat.mod_eq_of_lt ha

private theorem fid_bv64_pow2_and_sub1_zero {sz : BitVec 64} {k : Nat}
    (heq : sz.toNat = 16 * 2 ^ k) : (sz &&& (sz - 1#64)) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have hpow : 16 * 2 ^ k = 2 ^ (k + 4) := by
    rw [Nat.pow_add, show (2 : Nat) ^ 4 = 16 from by decide, Nat.mul_comm]
  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
  have h2p := Nat.two_pow_pos k
  have hsub : (sz - 1#64).toNat = 2 ^ (k + 4) - 1 := by
    rw [fid_bv64_sub_toNat (by rw [h1, heq]; omega), heq, hpow, h1]
  rw [BitVec.toNat_and, hsub, heq, hpow, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_self]
  rfl

private theorem pow2_16_of_and_zero_1m {sz : Nat} (hge : 16 ≤ sz) (hle : sz ≤ fidCongHashMaxSz)
    (hand : (BitVec.ofNat 64 sz &&& (BitVec.ofNat 64 sz - 1#64)) = 0#64) :
    ∃ k ≤ 16, sz = 16 * 2 ^ k := by
  unfold fidCongHashMaxSz at hle
  have hlt64 : sz < 2 ^ 64 := by omega
  have h1c : (1#64 : BitVec 64).toNat = 1 := rfl
  have h1 : (BitVec.ofNat 64 sz &&& (BitVec.ofNat 64 sz - 1#64)).toNat = 0 := by
    rw [hand]; rfl
  rw [BitVec.toNat_and, fid_bv64_sub_toNat (by rw [bv64_ofNat_toNat_lt hlt64, h1c]; omega),
    bv64_ofNat_toNat_lt hlt64, h1c] at h1
  have hpow2 : ∀ t, sz < 2 ^ (t + 1) → 16 ≤ sz → (sz &&& (sz - 1)) = 0 →
      ∃ j ≤ t, sz = 2 ^ j := by
    intro t; induction t with
    | zero => intro hlt _ _; exfalso; change sz < 2 ^ 1 at hlt; omega
    | succ t ih =>
      intro hlt h16 ha
      by_cases hlt' : sz < 2 ^ (t + 1)
      · obtain ⟨j, hj, rfl⟩ := ih hlt' h16 ha; exact ⟨j, by omega, rfl⟩
      · have hge_t : 1 * 2 ^ (t + 1) ≤ sz := by rw [Nat.one_mul]; omega
        have hbit : sz.testBit (t + 1) = true := by
          have hd1 : sz / 2 ^ (t + 1) = 1 := by
            have hlt_mul : sz < (1 + 1) * 2 ^ (t + 1) := by
              rw [show 1 + 1 = 2 from rfl, Nat.mul_comm, ← Nat.pow_succ]; exact hlt
            exact Nat.div_eq_of_lt_le hge_t hlt_mul
          rw [Nat.testBit_eq_decide_div_mod_eq, hd1]; decide
        have hzero : ∀ b, b ≠ t + 1 → sz.testBit b = false := by
          intro b hne
          by_cases hb1 : sz.testBit b = false
          · exact hb1
          · exfalso
            have hbt : sz.testBit b = true := by
              cases hb_v : sz.testBit b
              · exact absurd hb_v hb1
              · rfl
            by_cases hltb : b < t + 1
            · have hm1 : (sz - 1).testBit (t + 1) = true := by
                have hd1 : (sz - 1) / 2 ^ (t + 1) = 1 := by
                  have hlt_pow : sz - 1 < (1 + 1) * 2 ^ (t + 1) := by
                    have hlt2 : sz < (1 + 1) * 2 ^ (t + 1) := by
                      rw [show 1 + 1 = 2 from rfl, Nat.mul_comm, ← Nat.pow_succ]; exact hlt
                    omega
                  have hge_pow : 1 * 2 ^ (t + 1) ≤ sz - 1 := by
                    rw [Nat.one_mul]
                    by_cases he : sz = 2 ^ (t + 1)
                    · subst he
                      have hb_mod : (2 ^ (t + 1)).testBit b = false :=
                        Nat.testBit_two_pow_of_ne (Ne.symm hne)
                      rw [hb_mod] at hbt; cases hbt
                    · omega
                  exact Nat.div_eq_of_lt_le hge_pow hlt_pow
                rw [Nat.testBit_eq_decide_div_mod_eq, hd1]; decide
              have htest : (sz &&& (sz - 1)).testBit (t + 1) = true := by
                rw [Nat.testBit_and, hbit, hm1]; rfl
              rw [ha] at htest; simp at htest
            · have h2b : 2 ^ (t + 2) ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) (by omega)
              have hb_f : sz.testBit b = false :=
                Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt h2b)
              rw [hb_f] at hbt; cases hbt
        have heq_pow : sz = 2 ^ (t + 1) := by
          apply Nat.eq_of_testBit_eq; intro b
          by_cases hb2 : b = t + 1
          · subst hb2; rw [hbit, Nat.testBit_two_pow_self]
          · rw [hzero b hb2, Nat.testBit_two_pow_of_ne (Ne.symm hb2)]
        exact ⟨t + 1, Nat.le_refl _, heq_pow⟩
  have h221 : (2 : Nat) ^ 21 = 2097152 := by decide
  obtain ⟨j, hj_le, rfl⟩ := hpow2 20 (by rw [show 20 + 1 = 21 from rfl, h221]; omega) hge h1
  have hj4 : 4 ≤ j := by
    rcases Nat.lt_or_ge j 4 with hlt4 | hge4
    · have hp : 2 ^ j ≤ 2 ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
      have h23 : (2 : Nat) ^ 3 = 8 := by decide
      rw [h23] at hp; omega
    · exact hge4
  refine ⟨j - 4, by omega, ?_⟩
  rw [show (16 : Nat) = 2 ^ 4 from by decide, ← Nat.pow_add, Nat.add_sub_of_le hj4]

private theorem fid_bv32_or8000_and7fff (v : BitVec 32) :
    ((v ||| 0x80000000#32) &&& 0x7FFFFFFF#32) = (v &&& 0x7FFFFFFF#32) := by
  apply BitVec.eq_of_toNat_eq; apply Nat.eq_of_testBit_eq; intro i
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

private theorem fid_bv32_or8000_ne_of_msb_zero {v r : BitVec 32}
    (hv : (v &&& 0x80000000#32) = 0#32) : v ≠ r ||| 0x80000000#32 := by
  intro heq
  have h1 : ((r ||| 0x80000000#32) &&& 0x80000000#32).getLsbD 31 = true := by
    rw [BitVec.getLsbD_and, BitVec.getLsbD_or]; simp
  have h2 : (v &&& 0x80000000#32).getLsbD 31 = false := by rw [hv]; decide
  rw [← heq, h2] at h1; cases h1

private theorem fid_bv32_eq_of_not_ne {a b : BitVec 32} (h : ¬ a ≠ b) : a = b :=
  if h0 : a = b then h0 else absurd h0 h

private theorem fidCongHtCtrlOk_grow {c : FullCfg} {scr1 scr2 : List (BitVec 32)}
    {ctrl_off ht_off k : Nat} (hk : k < 16)
    (hok : FidCongHtCtrlOk c scr1 ctrl_off ht_off (16 * 2 ^ k))
    (hl2 : scr2.length = c.scratch_cap) (hfit : ht_off + 2 * (16 * 2 ^ k) ≤ c.scratch_cap)
    (h6 : scr2[ctrl_off + 6]? = some (BitVec.ofNat 32 ht_off))
    (h7 : scr2[ctrl_off + 7]? = some (BitVec.ofNat 32 (2 * (16 * 2 ^ k)))) :
    FidCongHtCtrlOk c scr2 ctrl_off ht_off (2 * (16 * 2 ^ k)) := by
  refine ⟨hl2, hok.2.1, hfit, hok.2.2.2.1, ⟨k + 1, by omega, ?_⟩, h6, h7⟩
  rw [Nat.pow_succ]; omega

private theorem fidCongHtCtrlOk_match_reads {c : FullCfg} {scr : List (BitVec 32)}
    {ctrl_off ht_off old_sz : BitVec 64}
    (hco : ctrl_off.toNat + 8 ≤ c.scratch_cap) (hscrl : scr.length = c.scratch_cap)
    (hho : ht_off = (scr[ctrl_off.toNat + 6]'(by omega)).setWidth 64)
    (hsz : old_sz = (scr[ctrl_off.toNat + 7]'(by omega)).setWidth 64)
    {ho os : Nat} (hok : FidCongHtCtrlOk c scr ctrl_off.toNat ho os) :
    ho = ht_off.toNat ∧ os = old_sz.toNat := by
  have hsc := c.hscr; unfold dimacsBound at hsc
  have ho_lt : ho < 2 ^ 32 := by have := hok.2.2.2.1; omega
  have os_lt : os < 2 ^ 32 := by have := hok.2.2.1; omega
  obtain ⟨_, _, _, _, _, h6, h7⟩ := hok
  rw [List.getElem?_eq_getElem (by omega), Option.some.injEq] at h6 h7
  have e1 : ht_off.toNat = ho := by rw [hho, bv64_zext32_toNat, h6, bv32_ofNat_toNat_lt ho_lt]
  have e2 : old_sz.toNat = os := by rw [hsz, bv64_zext32_toNat, h7, bv32_ofNat_toNat_lt os_lt]
  exact ⟨e1.symm, e2.symm⟩

private theorem fidCongHtCtrlOk_from_reads {c : FullCfg} {scr : List (BitVec 32)}
    {ctrl_off ht_off old_sz : BitVec 64}
    (hscrl : scr.length = c.scratch_cap) (hco : ctrl_off.toNat + 8 ≤ c.scratch_cap)
    (hho : ht_off = (scr[ctrl_off.toNat + 6]'(by omega)).setWidth 64)
    (hsz : old_sz = (scr[ctrl_off.toNat + 7]'(by omega)).setWidth 64)
    (h1 : ctrl_off.toNat + 8 ≤ ht_off.toNat) (h2 : ht_off.toNat < c.scratch_cap)
    (h3 : ht_off.toNat ≤ 0x7FFFFFFF) (h4 : 16 ≤ old_sz.toNat)
    (h5 : (old_sz &&& (old_sz - 1#64)) = 0#64)
    (h6 : old_sz.toNat ≤ c.scratch_cap - ht_off.toNat) (hmax : old_sz.toNat ≤ fidCongHashMaxSz) :
    FidCongHtCtrlOk c scr ctrl_off.toNat ht_off.toNat old_sz.toNat := by
  have hsc := c.hscr; unfold dimacsBound at hsc
  have hand_sz : (BitVec.ofNat 64 old_sz.toNat &&& (BitVec.ofNat 64 old_sz.toNat - 1#64)) =
      0#64 := by simpa [BitVec.ofNat_toNat] using h5
  obtain ⟨k, hk, heq⟩ := pow2_16_of_and_zero_1m h4 hmax hand_sz
  have he6 : scr[ctrl_off.toNat + 6]? = some (BitVec.ofNat 32 ht_off.toNat) := by
    rw [List.getElem?_eq_getElem (by omega)]; congr 1; apply BitVec.eq_of_toNat_eq
    rw [hho, bv64_zext32_toNat, bv32_ofNat_toNat_lt (by omega)]
  have he7 : scr[ctrl_off.toNat + 7]? = some (BitVec.ofNat 32 old_sz.toNat) := by
    rw [List.getElem?_eq_getElem (by omega)]; congr 1; apply BitVec.eq_of_toNat_eq
    rw [hsz, bv64_zext32_toNat, bv32_ofNat_toNat_lt (by omega)]
  exact ⟨hscrl, h1, by omega, h3, ⟨k, hk, heq⟩, he6, he7⟩

/-- Slot origin invariant during in-place tagged rehash (`full_cong_ht_grow_m7`). -/
private def FidSlotMigOk (c : FullCfg) (scr0 scr : List (BitVec 32))
    (ht_off old_sz new_sz : Nat) : Prop :=
  scr.length = c.scratch_cap ∧
  (∀ idx < ht_off, scr[idx]? = scr0[idx]?) ∧
  (∀ j < new_sz,
    scr[ht_off + j]? = some 0xFFFFFFFF#32 ∨
    ∃ k0 < old_sz, ∃ r0 : BitVec 32,
      scr0[ht_off + k0]? = some r0 ∧ r0 ≠ 0xFFFFFFFF#32 ∧
      (scr[ht_off + j]? = some r0 ∨ scr[ht_off + j]? = some (r0 ||| 0x80000000#32)))

/-- Entry-in-hand origin invariant during in-place tagged rehash (`full_cong_ht_grow_m7`). -/
private def FidCurMigOk (scr0 : List (BitVec 32)) (ht_off old_sz : Nat)
    (cur : BitVec 32) : Prop :=
  cur = 0xFFFFFFFF#32 ∨
  (cur.toNat < ht_off ∧ ∃ k0 < old_sz, scr0[ht_off + k0]? = some cur ∧ cur ≠ 0xFFFFFFFF#32)

private theorem fidSlotMigOk_set_empty {c : FullCfg} {scr0 scr : List (BitVec 32)}
    {ht_off old_sz new_sz pos : Nat} (hs : FidSlotMigOk c scr0 scr ht_off old_sz new_sz)
    (hpos : ht_off + pos < scr.length) :
    FidSlotMigOk c scr0 (scr.set (ht_off + pos) 0xFFFFFFFF#32) ht_off old_sz new_sz := by
  refine ⟨by rw [List.length_set]; exact hs.1, fun idx hidx => ?_, fun j hj => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hs.2.1 idx hidx
  · by_cases hjp : j = pos
    · subst hjp; left; rw [List.getElem?_set_self hpos]
    · rw [List.getElem?_set_ne (by omega)]; exact hs.2.2 j hj

private theorem fidSlotMigOk_set_cur {c : FullCfg} {scr0 scr : List (BitVec 32)}
    {ht_off old_sz new_sz pos : Nat} {cur : BitVec 32}
    (hs : FidSlotMigOk c scr0 scr ht_off old_sz new_sz)
    (hcur : FidCurMigOk scr0 ht_off old_sz cur) (hne : cur ≠ 0xFFFFFFFF#32)
    (hpos : ht_off + pos < scr.length) :
    FidSlotMigOk c scr0 (scr.set (ht_off + pos) (cur ||| 0x80000000#32)) ht_off old_sz new_sz := by
  rcases hcur with rfl | ⟨_, k0, hk0, hget, hne'⟩
  · exact absurd rfl hne
  · refine ⟨by rw [List.length_set]; exact hs.1, fun idx hidx => ?_, fun j hj => ?_⟩
    · rw [List.getElem?_set_ne (by omega)]; exact hs.2.1 idx hidx
    · by_cases hjp : j = pos
      · subst hjp; right; refine ⟨k0, hk0, cur, hget, hne', Or.inr ?_⟩
        rw [List.getElem?_set_self hpos]
      · rw [List.getElem?_set_ne (by omega)]; exact hs.2.2 j hj

private theorem fidCurMigOk_of_slot {c : FullCfg} {scr0 scr : List (BitVec 32)}
    {ht_off old_sz new_sz pos : Nat} {v : BitVec 32}
    (hs : FidSlotMigOk c scr0 scr ht_off old_sz new_sz) (hpos : pos < new_sz)
    (hv_get : scr[ht_off + pos]? = some v) (hv_ne : v ≠ 0xFFFFFFFF#32)
    (hv_msb : (v &&& 0x80000000#32) = 0#32) (hv_lt : v.toNat < ht_off) :
    FidCurMigOk scr0 ht_off old_sz v := by
  rcases hs.2.2 pos hpos with hem | ⟨k0, hk0, r0, hr0_get, hr0_ne, hr0_eq⟩
  · rw [hv_get] at hem; exact absurd (Option.some.inj hem) hv_ne
  · rcases hr0_eq with h1 | h1
    · rw [hv_get, Option.some.injEq] at h1; subst h1
      exact Or.inr ⟨hv_lt, k0, hk0, hr0_get, hr0_ne⟩
    · rw [hv_get, Option.some.injEq] at h1
      exact absurd h1 (fid_bv32_or8000_ne_of_msb_zero hv_msb)

end Helpers

/-! ## 2. `Func.wp` Proofs `#1–#6` -/

section WpProofs

open scoped FullArenaTactics

local macro "fid_omega" : tactic =>
  `(tactic| (
    try simp only [bv64_zext32_toNat,
      show BitVec.toNat (0 : BitVec 64) = 0 from rfl,
      show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
      show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
      show BitVec.toNat (6 : BitVec 64) = 6 from rfl,
      show BitVec.toNat (7 : BitVec 64) = 7 from rfl,
      show BitVec.toNat (8 : BitVec 64) = 8 from rfl,
      show BitVec.toNat (16 : BitVec 64) = 16 from rfl,
      show BitVec.toNat (64 : BitVec 64) = 64 from rfl,
      show BitVec.toNat (1048576 : BitVec 64) = 1048576 from rfl,
      show BitVec.toNat (2147483647 : BitVec 64) = 2147483647 from rfl] at *
    omega))

/-- **#1 (`full_cong_ht_hash_ent_m7_wp`)**: total safety and read-only memory preservation
(`arity ≤ 64`). -/
theorem full_cong_ht_hash_ent_m7_wp (Γ : Env) :
    ∀ a m Q X, fidCongHtHashEntSpec a m Q X →
      Func.wp Γ full_cong_ht_hash_ent_m7_body a m Q X := by
  rintro ⟨h, ent, ht_off, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hlen, hm0, hQ⟩
  have hsc := c.hscr; unfold dimacsBound at hsc
  have hscrl := hlen.scratch_ok.scratch_buf_len
  have hent_lt : ent.toNat < 2 ^ 32 := ent.isLt
  unfold Func.wp full_cong_ht_hash_ent_m7_body
  c0_hsplit
  · c0_hsteps; exact hQ 0#64
  · have he2_le : ent.toNat + 2 ≤ ht_off.toNat := by
      have h2 := bv64_zext32_add_ofNat ent 2 (by decide); fid_omega
    clear hc; c0_hsplit
    · c0_hsteps; exact hQ 0#64
    · have hht_le : ht_off.toNat ≤ c.scratch_cap := by fid_omega
      have he1_arr : (ent.setWidth 64 + 1#64).toNat < s.scratch.scratch_buf.length := by
        rw [bv64_zext32_add_ofNat ent 1 (by decide)]; fid_omega
      clear hc; c0_hsplit
      · c0_hsteps; exact hQ 0#64
      · let mw := s.scratch.scratch_buf[ent.toNat + 1]'(by omega)
        let harity : BitVec 64 := (mw &&& 0xFF#32).setWidth 64
        have hm_congr : s.scratch.scratch_buf[(BitVec.toNat ent +
            BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
            change (ent.toNat + 1) % 2 ^ 64 < s.scratch.scratch_buf.length
            rw [Nat.mod_eq_of_lt (by omega)]; omega) = mw :=
          scr_idx_zext32_add1 (by omega) _
        have har_le64 : harity.toNat ≤ 64 := by
          rw [hm_congr] at hc
          have hhc : ¬ (64 : Nat) < (mw &&& 0xFF#32).toNat := hc
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
            rw [hmod] at hc; dsimp only [harity] at *; fid_omega
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

/-- **#2 (`full_cong_ht_init_m7_wp`)**: bounds-guarded dynamic HT initializer scaling up to
`1,048,576` buckets (`FidCongHtCtrlOk` + all slots `0xFFFFFFFF#32` + `res_sz = 0`). -/
theorem full_cong_ht_init_m7_wp (Γ : Env) :
    ∀ a m Q X, fidCongHtInitSpec a m Q X →
      Func.wp Γ full_cong_ht_init_m7_body a m Q X := by
  rintro ⟨h, ctrl_off, ht_off, max_sz, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hlen, hm0, hQ⟩
  have hsc := c.hscr; unfold dimacsBound at hsc
  have hscrl := hlen.scratch_ok.scratch_buf_len
  have hret0 : Q (0#64, ()) m0 :=
    hQ 0#64 s.scratch.scratch_buf s.scratch.res_sz m0 hscrl hlen rfl ⟨rfl, rfl⟩
      (fun hne => absurd rfl hne) hm0
  unfold Func.wp full_cong_ht_init_m7_body
  c0_hsplit
  · c0_hsteps; exact hret0
  · have hco_le : ctrl_off.toNat ≤ c.scratch_cap := by fid_omega
    clear hc; c0_hsplit
    · c0_hsteps; exact hret0
    · have hco8 : ctrl_off.toNat + 8 ≤ c.scratch_cap := by have := ctrl_off.isLt; fid_omega
      clear hc; c0_hsplit
      · c0_hsteps; exact hret0
      · have hco8_ht : ctrl_off.toNat + 8 ≤ ht_off.toNat := by fid_omega
        clear hc; c0_hsplit
        · c0_hsteps; exact hret0
        · have hht_lt_cap : ht_off.toNat < c.scratch_cap := by fid_omega
          clear hc; c0_hsplit
          · c0_hsteps; exact hret0
          · have hht_le7 : ht_off.toNat ≤ 0x7FFFFFFF := by fid_omega
            clear hc; c0_hsplit
            · c0_hsteps; exact hret0
            · have hav16 : 16 ≤ c.scratch_cap - ht_off.toNat := by
                have := ht_off.isLt; fid_omega
              clear hc; c0_hsteps_nogrp
              refine wp_join_group (ts := [i64]) (fun (_, ()) ml0 => ml0 = m0) ?_ ?_
              · rintro _ ⟨lim0, ⟨⟩⟩ ml0 hml0; subst ml0
                c0_hsteps_nogrp
                refine wp_join_group (ts := [i64])
                  (fun (lim1, ()) ml1 => ml1 = m0 ∧ lim1.toNat ≤ 1048576) ?_ ?_
                · rintro _ ⟨lim1, ⟨⟩⟩ ml1 ⟨hml1, hlim1⟩; subst ml1
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [i64])
                    (fun (lim2, ()) ml2 => ml2 = m0 ∧ 16 ≤ lim2.toNat ∧ lim2.toNat ≤ 1048576)
                    ?_ ?_
                  · rintro _ ⟨lim2, ⟨⟩⟩ ml2 ⟨hml2, hlim2_lo, hlim2_hi⟩; subst ml2
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := [i64])
                      (fun (top, ()) mt => mt = m0 ∧ 16 ≤ top.toNat ∧ top.toNat ≤ 1048576 ∧
                        top.toNat ≤ c.scratch_cap - ht_off.toNat)
                      ?_ ?_
                    · rintro _ ⟨top, ⟨⟩⟩ mt ⟨hmt, htop16, htop_hi, htop_cap⟩; subst mt
                      c0_hsteps_nogrp
                      refine wp_loop_inv
                        (fun (sz, ()) ms => ms = m0 ∧ ∃ k ≤ 16,
                          sz.toNat = 16 * 2 ^ k ∧ sz.toNat ≤ top.toNat)
                        (fun (sz, ()) _ => 1048576 - sz.toNat)
                        (fun J hJ => by
                          c0_hsteps; exact hJ (16#64, ()) m0 ⟨rfl, 0, by decide, rfl, htop16⟩)
                        (fun J ⟨sz, ⟨⟩⟩ ms ⟨hms, k, hk_le, hsz_pow, hsz_top⟩ ih => ?_)
                      subst ms
                      have hsz_le_max : sz.toNat ≤ 1048576 := by omega
                      c0_hsplit
                      · have h2le : 2 * sz.toNat ≤ top.toNat := by fid_omega
                        have hk_lt : k < 16 := by
                          rcases Nat.lt_or_ge k 16 with hlt | hge
                          · exact hlt
                          · obtain rfl : k = 16 := by omega
                            have h16 : 16 * 2 ^ 16 = 1048576 := by decide
                            omega
                        have hshl : (sz <<< (1#32 : BitVec 32).signExtend 64).toNat =
                            2 * sz.toNat := fid_bv64_shl1_toNat (by omega)
                        c0_hsteps
                        refine ih (sz <<< (1#32 : BitVec 32).signExtend 64, ()) m0
                          (by have h2p := Nat.two_pow_pos k; dsimp only; rw [hshl]; omega)
                          ⟨rfl, k + 1, by omega, ?_, by rw [hshl]; exact h2le⟩
                        rw [hshl, hsz_pow, Nat.pow_succ]; omega
                      · clear hc
                        have hsz_lt_cap : ht_off.toNat + sz.toNat ≤ c.scratch_cap := by omega
                        have h6n : (ctrl_off + (6 : BitVec 64)).toNat = ctrl_off.toNat + 6 :=
                          bv64_add_ofNat_toNat 6 (by decide) (by omega)
                        have h7n : (ctrl_off + (7 : BitVec 64)).toNat = ctrl_off.toNat + 7 :=
                          bv64_add_ofNat_toNat 7 (by decide) (by omega)
                        have hco6_arr : (ctrl_off + (6 : BitVec 64)).toNat <
                            s.scratch.scratch_buf.length := by rw [h6n]; omega
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
                        c0_hsteps_nogrp
                        have hfs := focus_full_scratch_buf hm; clear hm
                        generalize hR_scr : FullScrBufRest c { s with scratch :=
                            { s.scratch with scratch_buf := scr_2 } } ⋆ R = R_scr at hfs
                        refine wp_loop_inv (ts := [i64])
                          (fun ⟨k2, ⟨⟩⟩ mk => ∃ scrl : List (BitVec 32),
                            scrl.length = c.scratch_cap ∧ k2.toNat ≤ sz.toNat ∧
                            scrl[ctrl_off.toNat + 6]? = some (BitVec.ofNat 32 ht_off.toNat) ∧
                            scrl[ctrl_off.toNat + 7]? = some (BitVec.ofNat 32 sz.toNat) ∧
                            (∀ j < k2.toNat, scrl[ht_off.toNat + j]? = some 0xFFFFFFFF#32) ∧
                            (array (t := i32) c.pScratchBuf scrl ⋆ R_scr) mk)
                          (fun ⟨k2, ⟨⟩⟩ _ => sz.toNat - k2.toNat)
                          (fun Jk hJk => by
                            c0_hsteps; exact hJk (0#64, ()) m ⟨scr_2, hscr2_len, Nat.zero_le _,
                              he6_2, he7_2, fun _ h => by simp at h, hfs⟩)
                          (fun Jk ⟨k2, ⟨⟩⟩ mk ⟨scrl, hscrll, hk2_le, h6l, h7l, hclrl, hmk⟩
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
                            ⟨scrl', by simp [scrl', hscrll], by rw [hk2_1]; omega, ?_, ?_, ?_, hm⟩
                          · rw [List.getElem?_set_ne (by omega)]; exact h6l
                          · rw [List.getElem?_set_ne (by omega)]; exact h7l
                          · intro j hj; rw [hk2_1] at hj
                            by_cases hjk : j = k2.toNat
                            · subst hjk; rw [List.getElem?_set_self (by omega)]
                            · rw [List.getElem?_set_ne (by omega)]; exact hclrl j (by omega)
                        · have hk2_eq : k2.toNat = sz.toNat := by omega
                          rw [hk2_eq] at hclrl; subst hR_scr
                          have hm_un := unfocus_full_scratch_buf hmk; clear hmk
                          c0_hsteps
                          exact hQ sz scrl 0#64 _ hscrll
                            (scr_state_core_pres hlen scrl hscrll 0#64).1 rfl ⟨rfl, rfl⟩
                            (fun _ => ⟨⟨hscrll, hco8_ht, hsz_lt_cap, hht_le7, ⟨k, hk_le, hsz_pow⟩,
                                h6l, h7l⟩, rfl, hclrl⟩)
                            (by assumption)
                    · intro J hJ; c0_hsplit
                      · c0_hsteps
                        have hle : lim2.toNat ≤ c.scratch_cap - ht_off.toNat := by
                          have := ht_off.isLt; exact Nat.not_lt.mp (by fid_omega)
                        exact hJ (lim2, ()) m0 ⟨rfl, hlim2_lo, hlim2_hi, hle⟩
                      · c0_hsteps
                        have hsub : (BitVec.ofNat 64 c.scratch_cap - ht_off).toNat =
                            c.scratch_cap - ht_off.toNat := by
                          rw [fid_bv64_sub_toNat (by rw [bv64_ofNat_toNat_lt (by omega)]; omega),
                            bv64_ofNat_toNat_lt (by omega)]
                        have hcap_le : c.scratch_cap - ht_off.toNat ≤ lim2.toNat := by
                          rw [bv64_cap_sub_mod (by omega) (by omega)] at hc
                          exact Nat.not_lt.mp hc
                        exact hJ (BitVec.ofNat 64 c.scratch_cap - ht_off, ()) m0
                          ⟨rfl, by omega, by omega, by omega⟩
                  · intro J hJ; c0_hsplit
                    · c0_hsteps; exact hJ (16#64, ()) m0 ⟨rfl, by decide, by decide⟩
                    · c0_hsteps; exact hJ (lim1, ()) m0 ⟨rfl, by fid_omega, hlim1⟩
                · intro J hJ; c0_hsplit
                  · c0_hsteps; exact hJ (1048576#64, ()) m0 ⟨rfl, by decide⟩
                  · c0_hsteps; exact hJ (lim0, ()) m0 ⟨rfl, by fid_omega⟩
              · intro J hJ; c0_hsplit
                · c0_hsteps; exact hJ (1048576#64, ()) m0 rfl
                · c0_hsteps; exact hJ (max_sz, ()) m0 rfl

/-- **#3 (`full_cong_ht_grow_m7_wp`)**: doubles `ht_sz` up to `1,048,576` via in-place tagged
rehash (`0x80000000u`), preserving slot origin (`0xFFFFFFFF#32` or `raw &&& 0x7FFFFFFF#32`). -/
theorem full_cong_ht_grow_m7_wp (Γ : Env)
    (hHash : ∀ a m Q X, fidCongHtHashEntSpec a m Q X →
      Γ "full_cong_ht_hash_ent_m7" [i64, i32, i64] [i64] a m Q X) :
    ∀ a m Q X, fidCongHtGrowSpec a m Q X →
      Func.wp Γ full_cong_ht_grow_m7_body a m Q X := by
  rintro ⟨h, ctrl_off, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hlen, hm0, hQ⟩
  have hsc := c.hscr; unfold dimacsBound at hsc
  have hscrl := hlen.scratch_ok.scratch_buf_len
  have hfail_noctrl : ∀ ret : BitVec 64,
      (∀ ht_off old_sz, FidCongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ht_off old_sz →
        False) → Q (ret, ()) m0 := fun ret hno =>
    hQ ret s.scratch.scratch_buf m0 hscrl hlen rfl ⟨rfl, rfl⟩
      (fun ht os h => False.elim (hno ht os h)) hm0
  unfold Func.wp full_cong_ht_grow_m7_body
  c0_hsplit
  · c0_hsteps; exact hfail_noctrl 0#64 (fun _ _ hok => by
      have := hok.2.1; have := hok.2.2.1; fid_omega)
  · have hco_le : ctrl_off.toNat ≤ c.scratch_cap := by fid_omega
    clear hc; c0_hsplit
    · c0_hsteps; exact hfail_noctrl 0#64 (fun _ _ hok => by
        have := ctrl_off.isLt; have := hok.2.1; have := hok.2.2.1; fid_omega)
    · have hco8 : ctrl_off.toNat + 8 ≤ c.scratch_cap := by have := ctrl_off.isLt; fid_omega
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
          ∀ ho os, FidCongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ho os → False :=
        fun hbad ho os hok => by
          apply hbad
          obtain ⟨rfl, rfl⟩ := fidCongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
          exact ⟨hok.2.1, Nat.lt_of_lt_of_le (by
              have ⟨k, _, he⟩ := hok.2.2.2.2.1; have := Nat.two_pow_pos k; omega) hok.2.2.1,
            hok.2.2.2.1⟩
      c0_hsplit
      · c0_hsteps; exact hfail_noctrl 0#64 (hbad_ht fun ⟨h1, _⟩ => by
          rw [hs6a, hht_nat] at hc
          change ht_off.toNat < (ctrl_off.toNat + BitVec.toNat 8) % 2 ^ 64 at hc; fid_omega)
      · have h1 : ctrl_off.toNat + 8 ≤ ht_off.toNat := by
          rw [hs6a, hht_nat] at hc
          change ¬ ht_off.toNat < (ctrl_off.toNat + BitVec.toNat 8) % 2 ^ 64 at hc; fid_omega
        clear hc; c0_hsplit
        · c0_hsteps; exact hfail_noctrl 0#64 (hbad_ht fun ⟨_, h2, _⟩ => by
            rw [hs6a, hht_nat] at hc
            change c.scratch_cap % 2 ^ 64 ≤ ht_off.toNat at hc; fid_omega)
        · have h2 : ht_off.toNat < c.scratch_cap := by
            rw [hs6a, hht_nat] at hc
            change ¬ c.scratch_cap % 2 ^ 64 ≤ ht_off.toNat at hc; fid_omega
          clear hc; c0_hsplit
          · c0_hsteps; exact hfail_noctrl 0#64 (hbad_ht fun ⟨_, _, h3⟩ => by
              rw [hs6a, hht_nat] at hc
              change BitVec.toNat 2147483647 < ht_off.toNat at hc; fid_omega)
          · have h3 : ht_off.toNat ≤ 0x7FFFFFFF := by
              rw [hs6a, hht_nat] at hc
              change ¬ BitVec.toNat 2147483647 < ht_off.toNat at hc; fid_omega
            clear hc
            have hbad_sz : ¬ (16 ≤ old_sz.toNat ∧ old_sz.toNat ≤ 1048576 ∧
                (old_sz &&& (old_sz - 1#64)) = 0#64 ∧
                old_sz.toNat ≤ c.scratch_cap - ht_off.toNat) →
                ∀ ho os, FidCongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ho os → False :=
              fun hbad ho os hok => by
                apply hbad
                obtain ⟨rfl, rfl⟩ := fidCongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
                obtain ⟨k, hk, he⟩ := hok.2.2.2.2.1
                refine ⟨by rw [he]; have := Nat.two_pow_pos k; omega,
                  by rw [he]; exact pow2_16_mul_le_1m k hk,
                  fid_bv64_pow2_and_sub1_zero he, by have := hok.2.2.1; omega⟩
            c0_hsplit
            · c0_hsteps; exact hfail_noctrl 0#64 (hbad_sz fun ⟨h4, _⟩ => by
                rw [hs7a, hos_nat] at hc
                change old_sz.toNat < BitVec.toNat 16 at hc; fid_omega)
            · have h4 : 16 ≤ old_sz.toNat := by
                rw [hs7a, hos_nat] at hc
                change ¬ old_sz.toNat < BitVec.toNat 16 at hc; fid_omega
              clear hc; c0_hsplit
              · c0_hsteps; exact hfail_noctrl 0#64 (hbad_sz fun ⟨_, hm, _⟩ => by
                  rw [hs7a, hos_nat] at hc
                  change BitVec.toNat 1048576 < old_sz.toNat at hc; fid_omega)
              · have hmax : old_sz.toNat ≤ 1048576 := by
                  rw [hs7a, hos_nat] at hc
                  change ¬ BitVec.toNat 1048576 < old_sz.toNat at hc; fid_omega
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
                      have := ht_off.isLt; fid_omega)
                  · have h6 : old_sz.toNat ≤ c.scratch_cap - ht_off.toNat := by
                      rw [hs6a, hht_nat, hs7a, hos_nat] at hc
                      change ¬ (2 ^ 64 - ht_off.toNat + c.scratch_cap) % 2 ^ 64 <
                        old_sz.toNat at hc
                      have := ht_off.isLt; fid_omega
                    clear hc
                    have hok_read : FidCongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat
                        ht_off.toNat old_sz.toNat :=
                      fidCongHtCtrlOk_from_reads hscrl hco8 hho_eq hsz_eq h1 h2 h3 h4 h5 h6 hmax
                    obtain ⟨k_exp, _, hos_pow⟩ := hok_read.2.2.2.2.1
                    c0_hsplit
                    · have heq_max : old_sz.toNat = 1048576 := by
                        rw [hs7a] at hc; exact congrArg BitVec.toNat hc
                      c0_hsteps; try simp only [hs7b]
                      refine hQ old_sz s.scratch.scratch_buf m0 hscrl hlen rfl ⟨rfl, rfl⟩
                        (fun ho os hok hlt _ => ?_) hm0
                      obtain ⟨rfl, rfl⟩ := fidCongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
                      unfold fidCongHashMaxSz at hlt; omega
                    · have hlt_max : old_sz.toNat < fidCongHashMaxSz := by
                        rw [hs7a] at hc
                        have hne : old_sz.toNat ≠ 1048576 := fun h => hc (BitVec.eq_of_toNat_eq h)
                        unfold fidCongHashMaxSz; omega
                      have hk_lt16 : k_exp < 16 := by
                        rcases Nat.lt_or_ge k_exp 16 with hlt | hge
                        · exact hlt
                        · obtain rfl : k_exp = 16 := by omega
                          have h16 : 16 * 2 ^ 16 = 1048576 := by decide
                          unfold fidCongHashMaxSz at hlt_max; omega
                      let new_sz : BitVec 64 := old_sz <<< (1#32 : BitVec 32).signExtend 64
                      have hnew_n : new_sz.toNat = 2 * old_sz.toNat :=
                        fid_bv64_shl1_toNat (by unfold fidCongHashMaxSz at hlt_max; omega)
                      have hnew_le : new_sz.toNat ≤ fidCongHashMaxSz := by
                        unfold fidCongHashMaxSz at hlt_max ⊢
                        rw [hnew_n, hos_pow]
                        have : 2 * (16 * 2 ^ k_exp) = 16 * 2 ^ (k_exp + 1) := by
                          rw [Nat.pow_succ]; omega
                        rw [this]; exact pow2_16_mul_le_1m (k_exp + 1) (by omega)
                      clear hc; c0_hsplit
                      · have hno_fit : c.scratch_cap < ht_off.toNat + 2 * old_sz.toNat := by
                          rw [hs6a, hht_nat, hs7a, hos_nat,
                            bv64_cap_sub_mod (Nat.le_of_lt h2) (by omega),
                            Nat.mod_eq_of_lt (by unfold fidCongHashMaxSz at hlt_max; omega)] at hc
                          omega
                        c0_hsteps; try simp only [hs7b]
                        refine hQ old_sz s.scratch.scratch_buf m0 hscrl hlen rfl ⟨rfl, rfl⟩
                          (fun ho os hok _ hfit => ?_) hm0
                        obtain ⟨rfl, rfl⟩ :=
                          fidCongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
                        omega
                      · have hfit : ht_off.toNat + 2 * old_sz.toNat ≤ c.scratch_cap := by
                          rw [hs6a, hht_nat, hs7a, hos_nat,
                            bv64_cap_sub_mod (Nat.le_of_lt h2) (by omega),
                            Nat.mod_eq_of_lt (by unfold fidCongHashMaxSz at hlt_max; omega)] at hc
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
                              fun _ _ _ => by omega, hfs⟩)
                          (fun Jk ⟨k, ⟨⟩⟩ mk ⟨scrk, hscrkl, hk_ge, hk_le, hpre, hold, hclr, hmk⟩
                              ihk => ?_)
                        c0_hsplit
                        · have hk_lt : k.toNat < new_sz.toNat := by
                            rw [hs7a, hos_nat,
                              Nat.mod_eq_of_lt (by unfold fidCongHashMaxSz at hlt_max; omega),
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
                              Nat.mod_eq_of_lt (by unfold fidCongHashMaxSz at hlt_max; omega),
                              ← hnew_n] at hc
                            exact Nat.le_antisymm hk_le (Nat.not_lt.mp hc)
                          rw [hk_eq] at hclr; clear hc
                          have hmig0 : FidSlotMigOk c s.scratch.scratch_buf scrk ht_off.toNat
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
                                  List.getElem?_eq_getElem hlt_len, ?_,
                                  Or.inl (by rw [hget, List.getElem?_eq_getElem hlt_len])⟩
                                intro he; apply hem; rw [List.getElem?_eq_getElem hlt_len, he]
                            · left; exact hclr j (by omega) hj
                          c0_hsteps_nogrp
                          refine wp_loop_inv (ts := [i64])
                            (fun ⟨i, ⟨⟩⟩ mi => ∃ scri : List (BitVec 32),
                              i.toNat ≤ old_sz.toNat ∧
                              FidSlotMigOk c s.scratch.scratch_buf scri ht_off.toNat old_sz.toNat
                                new_sz.toNat ∧
                              (array (t := i32) c.pScratchBuf scri ⋆ R_scr) mi)
                            (fun ⟨i, ⟨⟩⟩ _ => old_sz.toNat - i.toNat)
                            (fun Ji hJi => by
                              c0_hsteps; exact hJi (0#64, ()) mk ⟨scrk, Nat.zero_le _, hmig0, hmk⟩)
                            (fun Ji ⟨i, ⟨⟩⟩ mi ⟨scri, hi_le, hmigi, hmi⟩ ihi => ?_)
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
                                FidSlotMigOk c s.scratch.scratch_buf scrj ht_off.toNat old_sz.toNat
                                  new_sz.toNat ∧
                                (array (t := i32) c.pScratchBuf scrj ⋆ R_scr) mj)
                              (fun _ mj ⟨scrj, hmigj, hmj⟩ => by
                                c0_hsteps; exact ihi (i + 1#64, ()) mj
                                  (by dsimp only; rw [hi1_n]; omega)
                                  ⟨scrj, by rw [hi1_n]; omega, hmigj, hmj⟩)
                              (fun Jj hJj => ?_)
                            c0_hsplit
                            · have hraw_ne :
                                  scri[(ht_off + i).toNat]'hi_add_arr ≠ 0xFFFFFFFF#32 := by
                                simp only [hs6a, hht_nat] at hc; exact hc
                              clear hc; c0_hsplit
                              · have hraw_msb : (scri[(ht_off + i).toNat]'hi_add_arr &&&
                                    0x80000000#32) = 0#32 := by
                                  simp only [hs6a, hht_nat] at hc
                                  first | exact hc | exact fid_bv32_eq_of_not_ne hc
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
                                  have hcur_ok0 : FidCurMigOk s.scratch.scratch_buf ht_off.toNat
                                      old_sz.toNat raw :=
                                    fidCurMigOk_of_slot hmigi (by omega) hraw_get hraw_ne hraw_msb
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
                                      FidSlotMigOk c s.scratch.scratch_buf scrb0 ht_off.toNat
                                      old_sz.toNat new_sz.toNat :=
                                    fidSlotMigOk_set_empty hmigi (by rw [hmigi.1]; omega)
                                  refine wp_loop_break_group (brkTs := [i32, i64])
                                    (lpTs := [i32, i64])
                                    (fun (_cb, _hb, ()) mb => ∃ scrb : List (BitVec 32),
                                      FidSlotMigOk c s.scratch.scratch_buf scrb ht_off.toNat
                                        old_sz.toNat new_sz.toNat ∧
                                      (array (t := i32) c.pScratchBuf scrb ⋆ R_scr) mb)
                                    (fun rem (curl, hops, ()) ml => ∃ scrl : List (BitVec 32),
                                      FidSlotMigOk c s.scratch.scratch_buf scrl ht_off.toNat
                                        old_sz.toNat new_sz.toNat ∧
                                      FidCurMigOk s.scratch.scratch_buf ht_off.toNat
                                        old_sz.toNat curl ∧
                                      curl ≠ 0xFFFFFFFF#32 ∧
                                      hops.toNat ≤ new_sz.toNat ∧
                                      rem = new_sz.toNat - hops.toNat ∧
                                      (array (t := i32) c.pScratchBuf scrl ⋆ R_scr) ml)
                                    ?_ ?_ ?_
                                  · rintro _ ⟨cb, hb, ⟨⟩⟩ mb ⟨scrb, hmigb, hmb⟩
                                    c0_hsteps; exact hJj mb ⟨scrb, hmigb, hmb⟩
                                  · rintro Bh Lh rem ⟨curl, hops, ⟨⟩⟩ ml hBh hLh
                                      ⟨scrl, hmigl, hcurl, hcur_ne, hhops_le, rfl, hml⟩
                                    c0_hsplit
                                    · have hhops_lt : hops.toNat < new_sz.toNat := by
                                        rw [hs7a, hos_nat, Nat.mod_eq_of_lt
                                            (by unfold fidCongHashMaxSz at hlt_max; omega),
                                          ← hnew_n] at hc
                                        exact hc
                                      have hm_full : (FullMem c { s with scratch :=
                                          { s.scratch with scratch_buf := scrl } } ⋆ R) ml := by
                                        subst hR_scr; exact unfocus_full_scratch_buf hml
                                      clear hc; c0_hsteps; c0_call hHash
                                      refine ⟨c, { s with scratch :=
                                          { s.scratch with scratch_buf := scrl } },
                                        R, rfl, ⟨hlen.core_ok,
                                          { hlen.scratch_ok with scratch_buf_len := hmigl.1 }⟩,
                                        hm_full, fun hv => ?_⟩
                                      clear hm_full
                                      let slot0 := hv &&& (new_sz - 1#64)
                                      have hslot0_lt : slot0.toNat < new_sz.toNat :=
                                        bv64_and_sub1_lt (by omega)
                                      c0_hsteps_nogrp
                                      refine wp_loop_break_group (brkTs := [i32, i64, i64])
                                        (lpTs := [i64, i64])
                                        (fun (cur_p, _sl_p, _p_p, ()) mp =>
                                          ∃ scrp : List (BitVec 32),
                                            FidSlotMigOk c s.scratch.scratch_buf scrp ht_off.toNat
                                              old_sz.toNat new_sz.toNat ∧
                                            FidCurMigOk s.scratch.scratch_buf ht_off.toNat
                                              old_sz.toNat cur_p ∧
                                            (array (t := i32) c.pScratchBuf scrp ⋆ R_scr) mp)
                                        (fun remp (slotp, pp, ()) mp =>
                                          mp = ml ∧ slotp.toNat < new_sz.toNat ∧
                                          pp.toNat ≤ new_sz.toNat ∧
                                          remp = new_sz.toNat - pp.toNat)
                                        ?_ ?_ ?_
                                      · rintro _ ⟨cur_p, sl_p, p_p, ⟨⟩⟩ mp ⟨scrp, hmigp, hcurp, hmp⟩
                                        c0_hsplit
                                        · c0_hsteps; exact hBh (cur_p, hops, ()) mp
                                            ⟨scrp, hmigp, hmp⟩
                                        · have hhops1 : (hops + 1#64).toNat = hops.toNat + 1 :=
                                            bv64_add1_lt hhops_lt (by omega)
                                          c0_hsteps
                                          exact hLh (new_sz.toNat - (hops + 1#64).toNat)
                                            (cur_p, hops + 1#64, ()) mp (by omega)
                                            ⟨scrp, hmigp, hcurp, hc, by omega, rfl, hmp⟩
                                      · rintro Bp Lp remp ⟨slotp, pp, ⟨⟩⟩ mp hBp hLp
                                          ⟨hmp_eq, hslot_lt, hpp_le, rfl⟩
                                        subst mp
                                        c0_hsplit
                                        · have hpp_lt : pp.toNat < new_sz.toNat := by
                                            rw [hs7a, hos_nat, Nat.mod_eq_of_lt
                                                (by unfold fidCongHashMaxSz at hlt_max; omega),
                                              ← hnew_n] at hc
                                            exact hc
                                          have hsl_add_n : (ht_off + slotp).toNat =
                                              ht_off.toNat + slotp.toNat :=
                                            bv64_add_toNat (by omega)
                                          have hsl_arr : (ht_off + slotp).toNat < scrl.length := by
                                            rw [hsl_add_n, hmigl.1]; omega
                                          clear hc; c0_hsplit
                                          · c0_hsteps; try simp only [hs6b] at hm
                                            rw [hsl_add_n] at hm
                                            exact hBp (0xFFFFFFFF#32, slotp, pp, ()) _
                                              ⟨scrl.set (ht_off.toNat + slotp.toNat)
                                                  (curl ||| 0x80000000#32),
                                                fidSlotMigOk_set_cur hmigl hcurl hcur_ne
                                                  (by rw [hmigl.1]; omega),
                                                Or.inl rfl, hm⟩
                                          · have hdst_ne :
                                                scrl[(ht_off + slotp).toNat]'hsl_arr ≠
                                                  0xFFFFFFFF#32 := by
                                              simp only [hs6a, hht_nat] at hc; exact hc
                                            clear hc; c0_hsplit
                                            · have hdst_msb :
                                                  (scrl[(ht_off + slotp).toNat]'hsl_arr &&&
                                                    0x80000000#32) = 0#32 := by
                                                simp only [hs6a, hht_nat] at hc; exact hc
                                              let dst := scrl[(ht_off + slotp).toNat]'hsl_arr
                                              have hdst_get :
                                                  scrl[ht_off.toNat + slotp.toNat]? = some dst := by
                                                rw [List.getElem?_eq_getElem
                                                    (by rw [hmigl.1]; omega)]
                                                congr 1
                                                exact (list_getElem_congr hsl_add_n hsl_arr _).symm
                                              have hscrll : scrl.length = c.scratch_cap := hmigl.1
                                              clear hc; c0_hsteps_nogrp
                                              let scrl_s := scrl.set (ht_off.toNat + slotp.toNat)
                                                (curl ||| 0x80000000#32)
                                              have hm_s : (array (t := i32) c.pScratchBuf scrl_s ⋆
                                                  R_scr) m := by
                                                refine (congrArg
                                                  (fun arr => (array (t := i32) c.pScratchBuf
                                                    arr ⋆ R_scr) m) ?_).mp hm
                                                dsimp only [scrl_s]; congr 1
                                                first | exact hsl_add_n |
                                                  (rw [hs6b]; exact hsl_add_n)
                                              refine wp_join_group (ts := [i32])
                                                (fun (cur_n, ()) mn => mn = m ∧
                                                  FidCurMigOk s.scratch.scratch_buf ht_off.toNat
                                                    old_sz.toNat cur_n)
                                                ?_ ?_
                                              · rintro _ ⟨cur_n, ⟨⟩⟩ mn ⟨hmn, hcur_n⟩
                                                subst mn; c0_hsteps
                                                exact hBp (cur_n, slotp, pp, ()) _
                                                  ⟨scrl_s,
                                                    fidSlotMigOk_set_cur hmigl hcurl hcur_ne
                                                      (by rw [hmigl.1]; omega),
                                                    hcur_n, hm_s⟩
                                              · intro Jc hJc; c0_hsplit
                                                · have hdst_lt : dst.toNat < ht_off.toNat := by
                                                    simp only [hs6a, hht_nat] at hc
                                                    have hg : scrl[(ht_off + slotp).toNat]'hsl_arr =
                                                        scrl[(ht_off.toNat + BitVec.toNat slotp) %
                                                          2 ^ 64]'
                                                          (by rw [hscrll, Nat.mod_eq_of_lt
                                                            (by omega)]; omega) :=
                                                      list_getElem_congr
                                                        (by rw [hsl_add_n, Nat.mod_eq_of_lt
                                                          (by omega)])
                                                        hsl_arr
                                                        (by rw [hscrll, Nat.mod_eq_of_lt
                                                          (by omega)]; omega)
                                                    exact congrArg BitVec.toNat hg ▸ hc
                                                  have h6' : (ctrl_off + (6 : BitVec 64)).toNat =
                                                      ctrl_off.toNat + 6 := h6n
                                                  have hdst_raw :
                                                      scrl[(BitVec.setWidth 64
                                                        (s.scratch.scratch_buf[(ctrl_off +
                                                          (6 : BitVec 64)).toNat]'
                                                          (by rw [hscrl, h6']; omega)) +
                                                        slotp).toNat]'
                                                        (by rw [hs6b]; exact hsl_arr) = dst :=
                                                    list_getElem_congr
                                                      (congrArg (fun x => (BitVec.setWidth 64 x +
                                                        slotp).toNat) hs6b)
                                                      (by rw [hs6b]; exact hsl_arr) hsl_arr
                                                  c0_hsteps; try simp only [hdst_raw]
                                                  exact hJc (dst, ()) _ ⟨rfl,
                                                    fidCurMigOk_of_slot hmigl hslot_lt hdst_get
                                                      hdst_ne hdst_msb hdst_lt⟩
                                                · c0_hsteps
                                                  exact hJc (0xFFFFFFFF#32, ()) _ ⟨rfl, Or.inl rfl⟩
                                            · have hpp1 : (pp + 1#64).toNat = pp.toNat + 1 :=
                                                bv64_add1_lt hpp_lt (by omega)
                                              c0_hsteps; try simp only [hs7b]
                                              exact hLp (new_sz.toNat - (pp + 1#64).toNat)
                                                ((slotp + 1#64) &&& (new_sz - 1#64), pp + 1#64, ())
                                                ml (by omega)
                                                ⟨rfl, bv64_and_sub1_lt (by omega), by omega, rfl⟩
                                        · c0_hsteps
                                          exact hBp (curl, slotp, pp, ()) ml
                                            ⟨scrl, hmigl, hcurl, hml⟩
                                      · intro _ Lp _ hLp
                                        c0_hsteps; try simp only [hs7b]
                                        exact hLp new_sz.toNat (slot0, 0#64, ()) ml
                                          ⟨rfl, hslot0_lt, Nat.zero_le _, rfl⟩
                                    · c0_hsteps; exact hBh (curl, hops, ()) ml ⟨scrl, hmigl, hml⟩
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
                                    c0_hsteps; try simp only [hraw_raw]
                                    exact hLh new_sz.toNat (raw, 0#64, ()) _
                                      ⟨scrb0, hmig_b0, hcur_ok0, hraw_ne, Nat.zero_le _, rfl, hm_b0⟩
                                · c0_hsteps; exact hJj _ ⟨scri, hmigi, by assumption⟩
                              · c0_hsteps; exact hJj _ ⟨scri, hmigi, by assumption⟩
                            · c0_hsteps; exact hJj _ ⟨scri, hmigi, by assumption⟩
                          · clear hc; c0_hsteps_nogrp
                            refine wp_loop_inv (ts := [i64])
                              (fun ⟨j, ⟨⟩⟩ mj => ∃ scrj : List (BitVec 32),
                                scrj.length = c.scratch_cap ∧ j.toNat ≤ new_sz.toNat ∧
                                (∀ idx < ht_off.toNat, scrj[idx]? = s.scratch.scratch_buf[idx]?) ∧
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
                                c0_hsteps; exact hJj (0#64, ()) mi ⟨scri, hmigi.1, Nat.zero_le _,
                                  hmigi.2.1, fun q _ hq => hmigi.2.2 q hq,
                                  fun _ h => by simp at h, hmi⟩)
                              (fun Jj ⟨j, ⟨⟩⟩ mj
                                  ⟨scrj, hscrjl, hj_le, hprej, htailj, hdonej, hmj⟩ ihj => ?_)
                            c0_hsplit
                            · have hj_lt : j.toNat < new_sz.toNat := by
                                rw [hs7a, hos_nat, Nat.mod_eq_of_lt
                                    (by unfold fidCongHashMaxSz at hlt_max; omega),
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
                                (fun _ m1 ⟨scr1, h1', h2', h3', h4', hm1⟩ => by
                                  c0_hsteps
                                  exact ihj (j + 1#64, ()) m1 (by dsimp only; rw [hj1_n]; omega)
                                    ⟨scr1, h1', by rw [hj1_n]; omega, h2',
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
                                refine hJ8 _ ⟨scr1, by simp [scr1, hscrjl],
                                  fun idx hi => by
                                    rw [List.getElem?_set_ne (by omega)]; exact hprej idx hi,
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
                                    · rw [Option.some.inj hr, fid_bv32_or8000_and7fff]
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
                                c0_hsteps; refine hJ8 mj ⟨scrj, hscrjl, hprej,
                                  fun q hq1 hq2 => htailj q (by omega) hq2, fun q hq => ?_, hmj⟩
                                by_cases hqj : q = j.toNat
                                · subst hqj; left; exact hv_get
                                · exact hdonej q (by omega)
                            · have hj_eq : j.toNat = new_sz.toNat := by
                                rw [hs7a, hos_nat, Nat.mod_eq_of_lt
                                    (by unfold fidCongHashMaxSz at hlt_max; omega),
                                  ← hnew_n] at hc
                                exact Nat.le_antisymm hj_le (Nat.not_lt.mp hc)
                              rw [hj_eq] at hdonej; clear hc
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
                                rw [fid_bv64_trunc32_toNat (by omega), hnew_n,
                                  bv32_ofNat_toNat_lt (by omega)]
                              have hpref_fin : ∀ idx < ht_off.toNat, idx ≠ ctrl_off.toNat + 7 →
                                  scr_fin[idx]? = s.scratch.scratch_buf[idx]? := by
                                intro idx hidx hne7
                                dsimp only [scr_fin]
                                rw [List.getElem?_set_ne (Ne.symm hne7)]
                                exact hprej idx hidx
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
                                rfl ⟨rfl, rfl⟩ (fun ho os hok _ _ => ?_)
                                (unfocus_full_scratch_buf hm_fin)
                              obtain ⟨rfl, rfl⟩ :=
                                fidCongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
                              refine ⟨hnew_n, ?_, hpref_fin, fun q hq => ?_⟩
                              · have hok' := fidCongHtCtrlOk_grow hk_lt16
                                  (by simpa [hos_pow] using hok_read)
                                  hfin_len (by rw [← hos_pow]; exact hfit) hco6_fin
                                  (by rw [← hos_pow]; exact hco7_fin)
                                rwa [← hos_pow] at hok'
                              · dsimp only [scr_fin]
                                rw [List.getElem?_set_ne (by omega)]
                                exact hdonej q (by rwa [hnew_n])

/-- **#4 (`full_cong_ht_grow_clear_m7_wp`)**: doubles `ctrl[7]` up to `min 1M (cap - ht_off)`,
clears `scr[ht_off ..< ht_off + new_sz)`, and resets `res_sz = 0`. -/
theorem full_cong_ht_grow_clear_m7_wp (Γ : Env) :
    ∀ a m Q X, fidCongHtGrowClearSpec a m Q X →
      Func.wp Γ full_cong_ht_grow_clear_m7_body a m Q X := by
  rintro ⟨h, ctrl_off, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hlen, hm0, hQ⟩
  have hsc := c.hscr; unfold dimacsBound at hsc
  have hscrl := hlen.scratch_ok.scratch_buf_len
  have hfail_noctrl : ∀ ret : BitVec 64,
      (∀ ht_off old_sz, FidCongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ht_off old_sz →
        False) → Q (ret, ()) m0 := fun ret hno =>
    hQ ret s.scratch.scratch_buf s.scratch.res_sz m0 hscrl hlen rfl ⟨rfl, rfl⟩
      (fun ht os h => False.elim (hno ht os h)) hm0
  unfold Func.wp full_cong_ht_grow_clear_m7_body
  c0_hsplit
  · c0_hsteps; exact hfail_noctrl 0#64 (fun _ _ hok => by
      have := hok.2.1; have := hok.2.2.1; fid_omega)
  · have hco_le : ctrl_off.toNat ≤ c.scratch_cap := by fid_omega
    clear hc; c0_hsplit
    · c0_hsteps; exact hfail_noctrl 0#64 (fun _ _ hok => by
        have := ctrl_off.isLt; have := hok.2.1; have := hok.2.2.1; fid_omega)
    · have hco8 : ctrl_off.toNat + 8 ≤ c.scratch_cap := by have := ctrl_off.isLt; fid_omega
      clear hc
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
          ∀ ho os, FidCongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ho os → False :=
        fun hbad ho os hok => by
          apply hbad
          obtain ⟨rfl, rfl⟩ := fidCongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
          exact ⟨hok.2.1, Nat.lt_of_lt_of_le (by
              have ⟨k, _, he⟩ := hok.2.2.2.2.1; have := Nat.two_pow_pos k; omega) hok.2.2.1,
            hok.2.2.2.1⟩
      c0_hsplit
      · c0_hsteps; exact hfail_noctrl 0#64 (hbad_ht fun ⟨h1, _⟩ => by
          rw [hs6a, hht_nat] at hc
          change ht_off.toNat < (ctrl_off.toNat + BitVec.toNat 8) % 2 ^ 64 at hc; fid_omega)
      · have h1 : ctrl_off.toNat + 8 ≤ ht_off.toNat := by
          rw [hs6a, hht_nat] at hc
          change ¬ ht_off.toNat < (ctrl_off.toNat + BitVec.toNat 8) % 2 ^ 64 at hc; fid_omega
        clear hc; c0_hsplit
        · c0_hsteps; exact hfail_noctrl 0#64 (hbad_ht fun ⟨_, h2, _⟩ => by
            rw [hs6a, hht_nat] at hc
            change c.scratch_cap % 2 ^ 64 ≤ ht_off.toNat at hc; fid_omega)
        · have h2 : ht_off.toNat < c.scratch_cap := by
            rw [hs6a, hht_nat] at hc
            change ¬ c.scratch_cap % 2 ^ 64 ≤ ht_off.toNat at hc; fid_omega
          clear hc; c0_hsplit
          · c0_hsteps; exact hfail_noctrl 0#64 (hbad_ht fun ⟨_, _, h3⟩ => by
              rw [hs6a, hht_nat] at hc
              change BitVec.toNat 2147483647 < ht_off.toNat at hc; fid_omega)
          · have h3 : ht_off.toNat ≤ 0x7FFFFFFF := by
              rw [hs6a, hht_nat] at hc
              change ¬ BitVec.toNat 2147483647 < ht_off.toNat at hc; fid_omega
            clear hc
            have hbad_sz : ¬ (16 ≤ old_sz.toNat ∧ old_sz.toNat ≤ 1048576 ∧
                (old_sz &&& (old_sz - 1#64)) = 0#64 ∧
                old_sz.toNat ≤ c.scratch_cap - ht_off.toNat) →
                ∀ ho os, FidCongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ho os → False :=
              fun hbad ho os hok => by
                apply hbad
                obtain ⟨rfl, rfl⟩ := fidCongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
                obtain ⟨k, hk, he⟩ := hok.2.2.2.2.1
                refine ⟨by rw [he]; have := Nat.two_pow_pos k; omega,
                  by rw [he]; exact pow2_16_mul_le_1m k hk,
                  fid_bv64_pow2_and_sub1_zero he, by have := hok.2.2.1; omega⟩
            c0_hsplit
            · c0_hsteps; exact hfail_noctrl 0#64 (hbad_sz fun ⟨h4, _⟩ => by
                rw [hs7a, hos_nat] at hc
                change old_sz.toNat < BitVec.toNat 16 at hc; fid_omega)
            · have h4 : 16 ≤ old_sz.toNat := by
                rw [hs7a, hos_nat] at hc
                change ¬ old_sz.toNat < BitVec.toNat 16 at hc; fid_omega
              clear hc; c0_hsplit
              · c0_hsteps; exact hfail_noctrl 0#64 (hbad_sz fun ⟨_, hm, _⟩ => by
                  rw [hs7a, hos_nat] at hc
                  change BitVec.toNat 1048576 < old_sz.toNat at hc; fid_omega)
              · have hmax : old_sz.toNat ≤ 1048576 := by
                  rw [hs7a, hos_nat] at hc
                  change ¬ BitVec.toNat 1048576 < old_sz.toNat at hc; fid_omega
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
                      have := ht_off.isLt; fid_omega)
                  · have h6 : old_sz.toNat ≤ c.scratch_cap - ht_off.toNat := by
                      rw [hs6a, hht_nat, hs7a, hos_nat] at hc
                      change ¬ (2 ^ 64 - ht_off.toNat + c.scratch_cap) % 2 ^ 64 <
                        old_sz.toNat at hc
                      have := ht_off.isLt; fid_omega
                    clear hc
                    have hok_read : FidCongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat
                        ht_off.toNat old_sz.toNat :=
                      fidCongHtCtrlOk_from_reads hscrl hco8 hho_eq hsz_eq h1 h2 h3 h4 h5 h6 hmax
                    obtain ⟨k_exp, _, hos_pow⟩ := hok_read.2.2.2.2.1
                    c0_hsplit
                    · have heq_max : old_sz.toNat = 1048576 := by
                        rw [hs7a] at hc; exact congrArg BitVec.toNat hc
                      c0_hsteps; try simp only [hs7b]
                      refine hQ old_sz s.scratch.scratch_buf s.scratch.res_sz m0 hscrl hlen rfl
                        ⟨rfl, rfl⟩ (fun ho os hok hlt _ => ?_) hm0
                      obtain ⟨rfl, rfl⟩ := fidCongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
                      unfold fidCongHashMaxSz at hlt; omega
                    · have hlt_max : old_sz.toNat < fidCongHashMaxSz := by
                        rw [hs7a] at hc
                        have hne : old_sz.toNat ≠ 1048576 := fun h => hc (BitVec.eq_of_toNat_eq h)
                        unfold fidCongHashMaxSz; omega
                      have hk_lt16 : k_exp < 16 := by
                        rcases Nat.lt_or_ge k_exp 16 with hlt | hge
                        · exact hlt
                        · obtain rfl : k_exp = 16 := by omega
                          have h16 : 16 * 2 ^ 16 = 1048576 := by decide
                          unfold fidCongHashMaxSz at hlt_max; omega
                      let new_sz : BitVec 64 := old_sz <<< (1#32 : BitVec 32).signExtend 64
                      have hnew_n : new_sz.toNat = 2 * old_sz.toNat :=
                        fid_bv64_shl1_toNat (by unfold fidCongHashMaxSz at hlt_max; omega)
                      clear hc; c0_hsplit
                      · have hno_fit : c.scratch_cap < ht_off.toNat + 2 * old_sz.toNat := by
                          rw [hs6a, hht_nat, hs7a, hos_nat,
                            bv64_cap_sub_mod (Nat.le_of_lt h2) (by omega),
                            Nat.mod_eq_of_lt (by unfold fidCongHashMaxSz at hlt_max; omega)] at hc
                          omega
                        c0_hsteps; try simp only [hs7b]
                        refine hQ old_sz s.scratch.scratch_buf s.scratch.res_sz m0 hscrl hlen rfl
                          ⟨rfl, rfl⟩ (fun ho os hok _ hfit => ?_) hm0
                        obtain ⟨rfl, rfl⟩ :=
                          fidCongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
                        omega
                      · have hfit : ht_off.toNat + 2 * old_sz.toNat ≤ c.scratch_cap := by
                          rw [hs6a, hht_nat, hs7a, hos_nat,
                            bv64_cap_sub_mod (Nat.le_of_lt h2) (by omega),
                            Nat.mod_eq_of_lt (by unfold fidCongHashMaxSz at hlt_max; omega)] at hc
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
                              Nat.mod_eq_of_lt (by unfold fidCongHashMaxSz at hlt_max; omega),
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
                              Nat.mod_eq_of_lt (by unfold fidCongHashMaxSz at hlt_max; omega),
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
                            rw [fid_bv64_trunc32_toNat (by omega), hnew_n,
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
                            have h1eq : (1 : Nat) = (BitVec.signExtend 64 1#32).toNat := by decide
                            refine hset_eq scrk h7n' ?_
                            simp only [hs7b]
                            exact congrArg (fun x : Nat => BitVec.setWidth 32 (old_sz <<< x)) h1eq
                          try simp only [hs7b]
                          refine hQ new_sz scr_fin 0#64 m hfin_len
                            (scr_state_core_pres hlen scr_fin hfin_len 0#64).1
                            rfl ⟨rfl, rfl⟩ (fun ho os hok _ _ => ?_) hm_fin
                          obtain ⟨rfl, rfl⟩ :=
                            fidCongHtCtrlOk_match_reads hco8 hscrl hho_eq hsz_eq hok
                          refine ⟨hnew_n, ?_, rfl, hpref_fin, hclr_fin⟩
                          have hok' := fidCongHtCtrlOk_grow hk_lt16
                            (by simpa [hos_pow] using hok_read)
                            hfin_len (by rw [← hos_pow]; exact hfit) hco6_fin
                            (by rw [← hos_pow]; exact hco7_fin)
                          rwa [← hos_pow] at hok'

/-- **#5 (`full_cong_ht_lookup_m7_wp`)**: read-only linear probe over `scr` and `tmp`
(`arity ≤ 64`, `ht_sz ≤ 1,048,576`). -/
theorem full_cong_ht_lookup_m7_wp (Γ : Env) :
    ∀ a m Q X, fidCongHtLookupSpec a m Q X →
      Func.wp Γ full_cong_ht_lookup_m7_body a m Q X := by
  rintro ⟨h, ctrl_off, htag, harity, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hlen, hm0, hQ⟩
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx
  have hscrl := hlen.scratch_ok.scratch_buf_len
  have htmpl := hlen.core_ok.tmp_len_arr
  unfold Func.wp full_cong_ht_lookup_m7_body
  c0_hsplit
  · c0_hsteps; exact hQ 0xFFFFFFFF#32
  · have hco_le : ctrl_off.toNat ≤ c.scratch_cap := by fid_omega
    clear hc; c0_hsplit
    · c0_hsteps; exact hQ 0xFFFFFFFF#32
    · have hco8 : ctrl_off.toNat + 8 ≤ c.scratch_cap := by have := ctrl_off.isLt; fid_omega
      clear hc; c0_hsplit
      · c0_hsteps; exact hQ 0xFFFFFFFF#32
      · have hha64 : harity.toNat ≤ 64 := by fid_omega
        clear hc; c0_hsplit
        · c0_hsteps; exact hQ 0xFFFFFFFF#32
        · have hha_mv : harity.toNat ≤ c.max_vars := by fid_omega
          clear hc
          have h6n : (ctrl_off + 6#64).toNat = ctrl_off.toNat + 6 :=
            bv64_add_ofNat_toNat 6 (by decide) (by omega)
          have h7n : (ctrl_off + 7#64).toNat = ctrl_off.toNat + 7 :=
            bv64_add_ofNat_toNat 7 (by decide) (by omega)
          have hco6_arr : (ctrl_off + 6#64).toNat < s.scratch.scratch_buf.length := by
            rw [h6n]; omega
          have hco7_arr : (ctrl_off + 7#64).toNat < s.scratch.scratch_buf.length := by
            rw [h7n]; omega
          let ht_off_w := s.scratch.scratch_buf[ctrl_off.toNat + 6]'(by omega)
          let ht_sz_w := s.scratch.scratch_buf[ctrl_off.toNat + 7]'(by omega)
          let ht_off : BitVec 64 := ht_off_w.setWidth 64
          let ht_sz : BitVec 64 := ht_sz_w.setWidth 64
          have hht_nat : ht_off_w.toNat = ht_off.toNat := (bv64_zext32_toNat _).symm
          have hsz_nat : ht_sz_w.toNat = ht_sz.toNat := (bv64_zext32_toNat _).symm
          have hs6a : s.scratch.scratch_buf[(BitVec.toNat ctrl_off +
              BitVec.toNat (6 : BitVec 64)) % 2 ^ 64]'(by
              change (ctrl_off.toNat + 6) % 2 ^ 64 < s.scratch.scratch_buf.length
              rw [Nat.mod_eq_of_lt (by omega)]; omega) = ht_off_w :=
            scr_idx_add_imm 6 rfl (by omega) _ _
          have hs6b : s.scratch.scratch_buf[(ctrl_off + (6 : BitVec 64)).toNat]'(by
              change (ctrl_off.toNat + 6) % 2 ^ 64 < s.scratch.scratch_buf.length
              rw [Nat.mod_eq_of_lt (by omega)]; omega) = ht_off_w := hs6a
          have hs7a : s.scratch.scratch_buf[(BitVec.toNat ctrl_off +
              BitVec.toNat (7 : BitVec 64)) % 2 ^ 64]'(by
              change (ctrl_off.toNat + 7) % 2 ^ 64 < s.scratch.scratch_buf.length
              rw [Nat.mod_eq_of_lt (by omega)]; omega) = ht_sz_w :=
            scr_idx_add_imm 7 rfl (by omega) _ _
          have hs7b : s.scratch.scratch_buf[(ctrl_off + (7 : BitVec 64)).toNat]'(by
              change (ctrl_off.toNat + 7) % 2 ^ 64 < s.scratch.scratch_buf.length
              rw [Nat.mod_eq_of_lt (by omega)]; omega) = ht_sz_w := hs7a
          c0_hsplit
          · c0_hsteps; exact hQ 0xFFFFFFFF#32
          · clear hc; c0_hsplit
            · c0_hsteps; exact hQ 0xFFFFFFFF#32
            · have h2 : ht_off.toNat < c.scratch_cap := by
                rw [hs6a, hht_nat] at hc
                change ¬ c.scratch_cap % 2 ^ 64 ≤ ht_off.toNat at hc; fid_omega
              clear hc; c0_hsplit
              · c0_hsteps; exact hQ 0xFFFFFFFF#32
              · clear hc; c0_hsplit
                · c0_hsteps; exact hQ 0xFFFFFFFF#32
                · have h4 : 16 ≤ ht_sz.toNat := by
                    rw [hs7a, hsz_nat] at hc
                    change ¬ ht_sz.toNat < BitVec.toNat 16 at hc; fid_omega
                  clear hc; c0_hsplit
                  · c0_hsteps; exact hQ 0xFFFFFFFF#32
                  · have hmax : ht_sz.toNat ≤ 1048576 := by
                      rw [hs7a, hsz_nat] at hc
                      change ¬ BitVec.toNat 1048576 < ht_sz.toNat at hc; fid_omega
                    clear hc; c0_hsplit
                    · c0_hsteps; exact hQ 0xFFFFFFFF#32
                    · clear hc; c0_hsplit
                      · c0_hsteps; exact hQ 0xFFFFFFFF#32
                      · have h6 : ht_sz.toNat ≤ c.scratch_cap - ht_off.toNat := by
                          rw [hs6a, hht_nat, hs7a, hsz_nat] at hc
                          change ¬ (2 ^ 64 - ht_off.toNat + c.scratch_cap) % 2 ^ 64 <
                            ht_sz.toNat at hc
                          have := ht_off.isLt; fid_omega
                        clear hc; c0_hsteps_nogrp
                        refine wp_loop_inv (ts := [i64, i64])
                          (fun ⟨_, hi, ⟨⟩⟩ mi => mi = m0 ∧ hi.toNat ≤ harity.toNat)
                          (fun ⟨_, hi, ⟨⟩⟩ _ => harity.toNat - hi.toNat)
                          (fun J hJ => by
                            c0_hsteps; exact hJ (_, 0#64, ()) m0 ⟨rfl, Nat.zero_le _⟩)
                          (fun J ⟨hv, hi, ⟨⟩⟩ mi ⟨hmi, hi_le⟩ ih => ?_)
                        subst mi
                        c0_hsplit
                        · have hi_lt : hi.toNat < harity.toNat := by fid_omega
                          have hi_tmp : hi.toNat < s.core.tmp.length := by omega
                          have hi1_n : (hi + 1#64).toNat = hi.toNat + 1 :=
                            bv64_add1_lt hi_lt (by omega)
                          c0_hsteps
                          exact ih (_, hi + 1#64, ()) m0 (by dsimp only; omega) ⟨rfl, by omega⟩
                        · clear hc; c0_hsteps_nogrp
                          refine wp_loop_inv (ts := [i64, i64])
                            (fun ⟨slot, p, ⟨⟩⟩ mp => mp = m0 ∧ slot.toNat < ht_sz.toNat ∧
                              p.toNat ≤ ht_sz.toNat)
                            (fun ⟨_, p, ⟨⟩⟩ _ => ht_sz.toNat - p.toNat)
                            (fun Jp hJp => by
                              c0_hsteps; try simp only [hs7b]
                              exact hJp (hv &&& (ht_sz - 1#64), 0#64, ()) m0
                                ⟨rfl, bv64_and_sub1_lt (by omega), Nat.zero_le _⟩)
                            (fun Jp ⟨slot, p, ⟨⟩⟩ mp ⟨hmp, hslot_lt, hp_le⟩ ihp => ?_)
                          subst mp
                          c0_hsplit
                          · have hp_lt : p.toNat < ht_sz.toNat := by
                              rw [hs7a, hsz_nat] at hc; exact hc
                            have hsl_add_n : (ht_off + slot).toNat =
                                ht_off.toNat + slot.toNat := bv64_add_toNat (by omega)
                            have hsl_arr :
                                (ht_off + slot).toNat < s.scratch.scratch_buf.length := by
                              rw [hsl_add_n]; omega
                            let ent := s.scratch.scratch_buf[(ht_off + slot).toNat]'hsl_arr
                            have hent_lt : ent.toNat < 2 ^ 32 := ent.isLt
                            clear hc; c0_hsplit
                            · c0_hsteps; exact hQ 0xFFFFFFFF#32
                            · clear hc; c0_hsteps_nogrp
                              have hp1_n : (p + 1#64).toNat = p.toNat + 1 :=
                                bv64_add1_lt hp_lt (by omega)
                              refine wp_join0 (fun m2 => m2 = m0)
                                (fun _ m2 hm2 => by
                                  subst m2; c0_hsteps; try simp only [hs7b]
                                  exact ihp ((slot + 1#64) &&& (ht_sz - 1#64), p + 1#64, ()) m0
                                    (by dsimp only; omega)
                                    ⟨rfl, bv64_and_sub1_lt (by omega), by omega⟩)
                                (fun J2 hJ2 => ?_)
                              have hent_hc : s.scratch.scratch_buf[(ht_off.toNat +
                                  BitVec.toNat slot) % 2 ^ 64]'(by
                                  rw [hscrl, Nat.mod_eq_of_lt (by omega)]; omega) = ent := rfl
                              c0_hsplit
                              · have hfit_ent : ent.toNat + 2 + harity.toNat ≤ ht_off.toNat := by
                                  simp only [hs6a, hht_nat, hent_hc] at hc
                                  have h2n : BitVec.toNat (2 : BitVec 64) = 2 := rfl
                                  have hmod : (ent.toNat + BitVec.toNat (2 : BitVec 64) +
                                      harity.toNat) % 2 ^ 64 = ent.toNat + 2 + harity.toNat := by
                                    rw [h2n, Nat.mod_eq_of_lt (by fid_omega)]
                                  rw [hmod] at hc; exact hc
                                have he1_arr : (ent.setWidth 64 + 1#64).toNat <
                                    s.scratch.scratch_buf.length := by
                                  rw [bv64_zext32_add_ofNat ent 1 (by decide), hscrl]; omega
                                have h6' :
                                    (ctrl_off + (6 : BitVec 64)).toNat = ctrl_off.toNat + 6 := h6n
                                have h_ent_raw :
                                    s.scratch.scratch_buf[(BitVec.setWidth 64
                                      (s.scratch.scratch_buf[(ctrl_off + (6 : BitVec 64)).toNat]'
                                        (by rw [hscrl, h6']; omega)) + slot).toNat]'
                                      (by simp only [hs6b]; exact hsl_arr) = ent := by
                                  simp only [hs6b]; rfl
                                clear hc; try rw [h_ent_raw]
                                c0_hsteps_nogrp
                                refine wp_join0 (fun m3 => m3 = m0)
                                  (fun _ m3 hm3 => by subst m3; c0_hsteps; exact hJ2 m0 rfl)
                                  (fun J3 hJ3 => ?_)
                                c0_hsplit
                                · clear hc; c0_hsplit
                                  · clear hc; c0_hsteps_nogrp
                                    refine wp_loop_break_group (brkTs := [i32, i64]) (lpTs := [i64])
                                      (fun (_, _, ()) mb => mb = m0)
                                      (fun rem (k, ()) mk => mk = m0 ∧ k.toNat ≤ harity.toNat ∧
                                        rem = harity.toNat - k.toNat)
                                      ?_ ?_ ?_
                                    · rintro _ ⟨eq_b, kb, ⟨⟩⟩ mb hmb; subst mb
                                      c0_hsplit
                                      · c0_hsteps; exact hQ ent
                                      · c0_hsteps; exact hJ3 m0 rfl
                                    · rintro Bk Lk rem ⟨k, ⟨⟩⟩ mk hBk hLk ⟨hmk, hk_le, rfl⟩
                                      subst mk; c0_hsplit
                                      · have hk_lt : k.toNat < harity.toNat := by fid_omega
                                        have he2k_n : (ent.setWidth 64 + 2#64 + k).toNat =
                                            ent.toNat + 2 + k.toNat := by
                                          have h12 := bv64_zext32_add_ofNat ent 2 (by decide)
                                          rw [bv64_add_toNat (by rw [h12]; omega), h12]
                                        have he2k_arr : (ent.setWidth 64 + 2#64 + k).toNat <
                                            s.scratch.scratch_buf.length := by
                                          rw [he2k_n, hscrl]; omega
                                        have hk_tmp : k.toNat < s.core.tmp.length := by omega
                                        have hk1_n : (k + 1#64).toNat = k.toNat + 1 :=
                                          bv64_add1_lt hk_lt (by omega)
                                        clear hc; c0_hsplit
                                        · c0_hsteps; exact hBk (0#32, k, ()) m0 rfl
                                        · c0_hsteps
                                          exact hLk (harity.toNat - (k + 1#64).toNat)
                                            (k + 1#64, ()) m0 (by omega) ⟨rfl, by omega, rfl⟩
                                      · c0_hsteps; exact hBk (1#32, k, ()) m0 rfl
                                    · intro _ Lk _ hLk; c0_hsteps
                                      exact hLk harity.toNat (0#64, ()) m0
                                        ⟨rfl, Nat.zero_le _, rfl⟩
                                  · c0_hsteps; exact hJ3 m0 rfl
                                · c0_hsteps; exact hJ3 m0 rfl
                              · c0_hsteps; exact hJ2 m0 rfl
                          · c0_hsteps; exact hQ 0xFFFFFFFF#32

/-- **#6 (`full_cong_ht_insert_m7_wp`)**: inserts gate `ent` with auto-grow at 75% load
(`arity ≤ 64`, `ht_sz ≤ 1,048,576`), preserving `FullState.core`, `LengthsOk c`, and
`FullExtScratchPres`. -/
theorem full_cong_ht_insert_m7_wp (Γ : Env)
    (hHash : ∀ a m Q X, fidCongHtHashEntSpec a m Q X →
      Γ "full_cong_ht_hash_ent_m7" [i64, i32, i64] [i64] a m Q X)
    (hGrow : ∀ a m Q X, fidCongHtGrowSpec a m Q X →
      Γ "full_cong_ht_grow_m7" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fidCongHtInsertSpec a m Q X →
      Func.wp Γ full_cong_ht_insert_m7_body a m Q X := by
  rintro ⟨h, ctrl_off, ent, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hlen, hm0, hQ⟩
  have hsc := c.hscr; unfold dimacsBound at hsc
  have hscrl := hlen.scratch_ok.scratch_buf_len
  have hent_lt : ent.toNat < 2 ^ 32 := ent.isLt
  have hret_noop : Q (0xFFFFFFFF#32, ()) m0 :=
    hQ 0xFFFFFFFF#32 s.scratch.scratch_buf s.scratch.res_sz m0 hscrl hlen rfl ⟨rfl, rfl⟩ hm0
  unfold Func.wp full_cong_ht_insert_m7_body
  c0_hsplit
  · c0_hsteps; exact hret_noop
  · have hco_le : ctrl_off.toNat ≤ c.scratch_cap := by fid_omega
    clear hc; c0_hsplit
    · c0_hsteps; exact hret_noop
    · have hco8 : ctrl_off.toNat + 8 ≤ c.scratch_cap := by have := ctrl_off.isLt; fid_omega
      clear hc
      let ht_off_w := s.scratch.scratch_buf[ctrl_off.toNat + 6]'(by omega)
      let old_sz_w := s.scratch.scratch_buf[ctrl_off.toNat + 7]'(by omega)
      let ht_off : BitVec 64 := ht_off_w.setWidth 64
      let old_sz : BitVec 64 := old_sz_w.setWidth 64
      have hht_nat : ht_off_w.toNat = ht_off.toNat := (bv64_zext32_toNat _).symm
      have hos_nat : old_sz_w.toNat = old_sz.toNat := (bv64_zext32_toNat _).symm
      have hs6a : s.scratch.scratch_buf[(BitVec.toNat ctrl_off +
          BitVec.toNat (6 : BitVec 64)) % 2 ^ 64]'(by
          change (ctrl_off.toNat + 6) % 2 ^ 64 < s.scratch.scratch_buf.length
          rw [Nat.mod_eq_of_lt (by omega)]; omega) = ht_off_w :=
        scr_idx_add_imm 6 rfl (by omega) _ _
      have hs6b : s.scratch.scratch_buf[(ctrl_off + (6 : BitVec 64)).toNat]'(by
          change (ctrl_off.toNat + 6) % 2 ^ 64 < s.scratch.scratch_buf.length
          rw [Nat.mod_eq_of_lt (by omega)]; omega) = ht_off_w := hs6a
      have hs7a : s.scratch.scratch_buf[(BitVec.toNat ctrl_off +
          BitVec.toNat (7 : BitVec 64)) % 2 ^ 64]'(by
          change (ctrl_off.toNat + 7) % 2 ^ 64 < s.scratch.scratch_buf.length
          rw [Nat.mod_eq_of_lt (by omega)]; omega) = old_sz_w :=
        scr_idx_add_imm 7 rfl (by omega) _ _
      have hs7b : s.scratch.scratch_buf[(ctrl_off + (7 : BitVec 64)).toNat]'(by
          change (ctrl_off.toNat + 7) % 2 ^ 64 < s.scratch.scratch_buf.length
          rw [Nat.mod_eq_of_lt (by omega)]; omega) = old_sz_w := hs7a
      c0_hsplit
      · c0_hsteps; exact hret_noop
      · clear hc; c0_hsplit
        · c0_hsteps; exact hret_noop
        · have h2 : ht_off.toNat < c.scratch_cap := by
            rw [hs6a, hht_nat] at hc
            change ¬ c.scratch_cap % 2 ^ 64 ≤ ht_off.toNat at hc; fid_omega
          clear hc; c0_hsplit
          · c0_hsteps; exact hret_noop
          · clear hc; c0_hsplit
            · c0_hsteps; exact hret_noop
            · have h4 : 16 ≤ old_sz.toNat := by
                rw [hs7a, hos_nat] at hc
                change ¬ old_sz.toNat < BitVec.toNat 16 at hc; fid_omega
              clear hc; c0_hsplit
              · c0_hsteps; exact hret_noop
              · clear hc; c0_hsplit
                · c0_hsteps; exact hret_noop
                · clear hc; c0_hsplit
                  · c0_hsteps; exact hret_noop
                  · have h6 : old_sz.toNat ≤ c.scratch_cap - ht_off.toNat := by
                      rw [hs6a, hht_nat, hs7a, hos_nat] at hc
                      change ¬ (2 ^ 64 - ht_off.toNat + c.scratch_cap) % 2 ^ 64 <
                        old_sz.toNat at hc
                      have := ht_off.isLt; fid_omega
                    clear hc; c0_hsplit
                    · c0_hsteps; exact hret_noop
                    · have he2_le : ent.toNat + 2 ≤ ht_off.toNat := by
                        rw [hs6a, hht_nat] at hc
                        rw [Nat.mod_eq_of_lt (by fid_omega)] at hc; fid_omega
                      have he1_arr : (ent.setWidth 64 + 1#64).toNat <
                          s.scratch.scratch_buf.length := by
                        rw [bv64_zext32_add_ofNat ent 1 (by decide)]; omega
                      let mw := s.scratch.scratch_buf[ent.toNat + 1]'(by omega)
                      have hs_e1 : s.scratch.scratch_buf[(BitVec.toNat ent +
                          BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                          change (ent.toNat + 1) % 2 ^ 64 < s.scratch.scratch_buf.length
                          rw [Nat.mod_eq_of_lt (by omega)]; omega) = mw :=
                        scr_idx_zext32_add1 (by omega) _
                      let ea : BitVec 64 := (mw &&& 0xFF#32).setWidth 64
                      clear hc; c0_hsplit
                      · c0_hsteps; exact hret_noop
                      · have hea64 : ea.toNat ≤ 64 := by
                          rw [hs_e1] at hc
                          have h255 : (mw &&& (255 : BitVec 32)) = (mw &&& 0xFF#32) := rfl
                          have hhc : ¬ (64 : Nat) < (mw &&& (255 : BitVec 32)).toNat := hc
                          rw [h255] at hhc; dsimp only [ea]; rw [bv64_zext32_toNat]
                          exact Nat.not_lt.mp hhc
                        clear hc; c0_hsplit
                        · c0_hsteps; exact hret_noop
                        · have hea_fit : ent.toNat + 2 + ea.toNat ≤ ht_off.toNat := by
                            rw [hs6a, hht_nat, hs_e1] at hc
                            have h255 : (mw &&& (255 : BitVec 32)) = (mw &&& 0xFF#32) := rfl
                            have h2n : BitVec.toNat (2 : BitVec 64) = 2 := rfl
                            have hmod : (ent.toNat + BitVec.toNat (2 : BitVec 64) +
                                (mw &&& (255 : BitVec 32)).toNat) % 2 ^ 64 =
                                ent.toNat + 2 + ea.toNat := by
                              dsimp only [ea]; rw [h2n, h255, bv64_zext32_toNat]
                              exact Nat.mod_eq_of_lt (by omega)
                            change ¬ ht_off.toNat < (ent.toNat + BitVec.toNat (2 : BitVec 64) +
                                (mw &&& (255 : BitVec 32)).toNat) % 2 ^ 64 at hc
                            rw [hmod] at hc; exact Nat.not_lt.mp hc
                          clear hc; c0_hsteps_nogrp
                          refine wp_join_group (ts := [i64])
                            (fun (ht_sz1, ()) m1 => ∃ scr1 : List (BitVec 32),
                              scr1.length = c.scratch_cap ∧
                              16 ≤ ht_sz1.toNat ∧ ht_sz1.toNat ≤ c.scratch_cap - ht_off.toNat ∧
                              (FullMem c { s with scratch :=
                                { s.scratch with scratch_buf := scr1 } } ⋆ R) m1)
                            ?_ ?_
                          · rintro _ ⟨ht_sz1, ⟨⟩⟩ m1 ⟨scr1, hscr1l, hsz1_lo, hsz1_cap, hm1⟩
                            let s1 : FullState :=
                              { s with scratch := { s.scratch with scratch_buf := scr1 } }
                            have hs1_scrl : s1.scratch.scratch_buf.length = c.scratch_cap := hscr1l
                            have hs1_len : s1.LengthsOk c :=
                              ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hscr1l }⟩
                            change (FullMem c s1 ⋆ R) m1 at hm1
                            c0_hsteps_nogrp
                            c0_call hHash
                            refine ⟨c, s1, R, rfl, hs1_len, hm1, fun hv => ?_⟩
                            c0_hsteps_nogrp
                            refine wp_loop_inv (ts := [i64, i64])
                              (fun ⟨slot, p, ⟨⟩⟩ mp => mp = m1 ∧ slot.toNat < ht_sz1.toNat ∧
                                p.toNat ≤ ht_sz1.toNat)
                              (fun ⟨_, p, ⟨⟩⟩ _ => ht_sz1.toNat - p.toNat)
                              (fun Jp hJp => by
                                c0_hsteps; exact hJp (hv &&& (ht_sz1 - 1#64), 0#64, ()) m1
                                  ⟨rfl, bv64_and_sub1_lt (by omega), Nat.zero_le _⟩)
                              (fun Jp ⟨slot, p, ⟨⟩⟩ mp ⟨hmp, hslot_lt, hp_le⟩ ihp => ?_)
                            subst mp
                            c0_hsplit
                            · have hp_lt : p.toNat < ht_sz1.toNat := hc
                              have hsl_add_n : (ht_off + slot).toNat =
                                  ht_off.toNat + slot.toNat := bv64_add_toNat (by omega)
                              have hsl_arr : (ht_off + slot).toNat < scr1.length := by
                                rw [hsl_add_n, hscr1l]; omega
                              let cur := scr1[(ht_off + slot).toNat]'hsl_arr
                              have hcur_lt : cur.toNat < 2 ^ 32 := cur.isLt
                              clear hc; c0_hsplit
                              · try simp only [hs6b]
                                c0_hsteps
                                rw [hsl_add_n] at hm
                                let scr2 := scr1.set (ht_off.toNat + slot.toNat) ent
                                have hscr2l : scr2.length = c.scratch_cap := by simp [scr2, hscr1l]
                                exact hQ ent scr2 (s.scratch.res_sz + 1#64) _ hscr2l
                                  (scr_state_core_pres hlen scr2 hscr2l _).1 rfl ⟨rfl, rfl⟩ hm
                              · clear hc; c0_hsplit
                                · c0_hsteps
                                  exact hQ ent scr1 s.scratch.res_sz m1 hscr1l hs1_len rfl
                                    ⟨rfl, rfl⟩ hm1
                                · have hp1_n : (p + 1#64).toNat = p.toNat + 1 :=
                                    bv64_add1_lt hp_lt (by omega)
                                  clear hc; c0_hsteps_nogrp
                                  refine wp_join0 (fun m2 => m2 = m1)
                                    (fun _ m2 hm2 => by
                                      subst m2; c0_hsteps
                                      exact ihp ((slot + 1#64) &&& (ht_sz1 - 1#64), p + 1#64, ())
                                        m1 (by dsimp only; omega)
                                        ⟨rfl, bv64_and_sub1_lt (by omega), by omega⟩)
                                    (fun J2 hJ2 => ?_)
                                  have hcur_hc : s1.scratch.scratch_buf[(ht_off.toNat +
                                      BitVec.toNat slot) % 2 ^ 64]'(by
                                      rw [hs1_scrl, Nat.mod_eq_of_lt (by omega)]; omega) = cur :=
                                    rfl
                                  c0_hsplit
                                  · have hcur_fit : cur.toNat + 2 + ea.toNat ≤ ht_off.toNat := by
                                      simp only [hs6a, hht_nat, hcur_hc, hs_e1] at hc
                                      dsimp only [ea] at hc ⊢
                                      have h2n : BitVec.toNat (2 : BitVec 64) = 2 := rfl
                                      have h255 : (mw &&& (255 : BitVec 32)) = (mw &&& 0xFF#32) :=
                                        rfl
                                      rw [bv64_zext32_toNat]
                                      rw [h2n, h255, Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                                    have hc1_arr : (cur.setWidth 64 + 1#64).toNat <
                                        s1.scratch.scratch_buf.length := by
                                      rw [hs1_scrl, bv64_zext32_add_ofNat cur 1 (by decide)]; omega
                                    clear hc; try simp only [hs6b]
                                    c0_hsteps_nogrp
                                    refine wp_join0 (fun m3 => m3 = m1)
                                      (fun _ m3 hm3 => by subst m3; c0_hsteps; exact hJ2 m1 rfl)
                                      (fun J3 hJ3 => ?_)
                                    c0_hsplit
                                    · clear hc; c0_hsplit
                                      · clear hc; c0_hsteps_nogrp
                                        refine wp_loop_break_group (brkTs := [i32, i64])
                                          (lpTs := [i64])
                                          (fun (_, _, ()) mb => mb = m1)
                                          (fun rem (k, ()) mk => mk = m1 ∧ k.toNat ≤ ea.toNat ∧
                                            rem = ea.toNat - k.toNat)
                                          ?_ ?_ ?_
                                        · rintro _ ⟨eq_b, kb, ⟨⟩⟩ mb hmb; subst mb
                                          c0_hsplit
                                          · c0_hsteps
                                            exact hQ cur scr1 s.scratch.res_sz m1 hscr1l hs1_len
                                              rfl ⟨rfl, rfl⟩ hm1
                                          · c0_hsteps; exact hJ3 m1 rfl
                                        · rintro Bk Lk rem ⟨k, ⟨⟩⟩ mk hBk hLk ⟨hmk, hk_le, rfl⟩
                                          subst mk; c0_hsplit
                                          · have hk_lt : k.toNat < ea.toNat := by
                                              rw [hs_e1] at hc; dsimp only [ea]
                                              rw [bv64_zext32_toNat]; exact hc
                                            have hc2k_n : (cur.setWidth 64 + 2#64 + k).toNat =
                                                cur.toNat + 2 + k.toNat := by
                                              have h12 := bv64_zext32_add_ofNat cur 2 (by decide)
                                              rw [bv64_add_toNat (by rw [h12]; omega), h12]
                                            have hc2k_arr : (cur.setWidth 64 + 2#64 + k).toNat <
                                                s1.scratch.scratch_buf.length := by
                                              rw [hc2k_n, hs1_scrl]; omega
                                            have he2k_n : (ent.setWidth 64 + 2#64 + k).toNat =
                                                ent.toNat + 2 + k.toNat := by
                                              have h12 := bv64_zext32_add_ofNat ent 2 (by decide)
                                              rw [bv64_add_toNat (by rw [h12]; omega), h12]
                                            have he2k_arr : (ent.setWidth 64 + 2#64 + k).toNat <
                                                s1.scratch.scratch_buf.length := by
                                              rw [he2k_n, hs1_scrl]; omega
                                            have hk1_n : (k + 1#64).toNat = k.toNat + 1 :=
                                              bv64_add1_lt hk_lt (by omega)
                                            clear hc; c0_hsplit
                                            · c0_hsteps; exact hBk (0#32, k, ()) m1 rfl
                                            · c0_hsteps
                                              exact hLk (ea.toNat - (k + 1#64).toNat)
                                                (k + 1#64, ()) m1 (by omega) ⟨rfl, by omega, rfl⟩
                                          · c0_hsteps; exact hBk (1#32, k, ()) m1 rfl
                                        · intro _ Lk _ hLk; c0_hsteps
                                          exact hLk ea.toNat (0#64, ()) m1
                                            ⟨rfl, Nat.zero_le _, rfl⟩
                                      · c0_hsteps; exact hJ3 m1 rfl
                                    · c0_hsteps; exact hJ3 m1 rfl
                                  · c0_hsteps; exact hJ2 m1 rfl
                            · c0_hsteps
                              exact hQ 0xFFFFFFFF#32 scr1 s.scratch.res_sz m1 hscr1l hs1_len rfl
                                ⟨rfl, rfl⟩ hm1
                          · intro Js hJs; c0_hsplit
                            · clear hc; c0_hsteps_nogrp
                              refine wp_join_group (ts := []) (fun () mg => mg = m0) ?_ ?_
                              · rintro _ ⟨⟩ mg hmg; subst mg
                                c0_hsteps; c0_call hGrow
                                refine ⟨c, s, R, rfl, hlen, hm0,
                                  fun grown scr_g mg' hgl _ _ _ _ hmg' => ?_⟩
                                c0_hsteps_nogrp
                                refine wp_join_group (ts := [i64])
                                  (fun ⟨ht_sz2, ⟨⟩⟩ mg2 => mg2 = mg' ∧
                                    16 ≤ ht_sz2.toNat ∧ ht_sz2.toNat ≤ c.scratch_cap - ht_off.toNat)
                                  (fun _ ⟨ht_sz2, ⟨⟩⟩ mg2 ⟨hmg2, h16, hfit⟩ => by
                                    subst mg2; c0_hsteps
                                    exact hJs (ht_sz2, ()) mg' ⟨scr_g, hgl, h16, hfit, hmg'⟩)
                                  (fun J2 hJ2 => ?_)
                                c0_hsplit
                                · have h16g : 16 ≤ grown.toNat := by fid_omega
                                  clear hc; c0_hsplit
                                  · clear hc; c0_hsplit
                                    · have hfitg : grown.toNat ≤ c.scratch_cap - ht_off.toNat := by
                                        rw [hs6a, hht_nat,
                                          bv64_cap_sub_mod (Nat.le_of_lt h2) (by omega)] at hc
                                        exact hc
                                      c0_hsteps; exact hJ2 (grown, ()) mg' ⟨rfl, h16g, hfitg⟩
                                    · c0_hsteps; try simp only [hs7b]
                                      exact hJ2 (old_sz, ()) mg' ⟨rfl, h4, h6⟩
                                  · c0_hsteps; try simp only [hs7b]
                                    exact hJ2 (old_sz, ()) mg' ⟨rfl, h4, h6⟩
                                · c0_hsteps; try simp only [hs7b]
                                  exact hJ2 (old_sz, ()) mg' ⟨rfl, h4, h6⟩
                              · intro J1 hJ1
                                c0_hsplit
                                · c0_hsteps; exact hJ1 () m0 rfl
                                · clear hc; c0_hsplit
                                  · c0_hsteps; exact hJ1 () m0 rfl
                                  · c0_hsteps; try simp only [hs7b]
                                    exact hJs (old_sz, ()) m0
                                      ⟨s.scratch.scratch_buf, hscrl, h4, h6, hm0⟩
                            · c0_hsteps; try simp only [hs7b]
                              exact hJs (old_sz, ()) m0
                                ⟨s.scratch.scratch_buf, hscrl, h4, h6, hm0⟩

end WpProofs

end LeanQbe.T.Examples.Kissat.FullFidelityCong
