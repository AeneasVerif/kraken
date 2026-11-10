module

public import LeanQbe.Examples.LratBytesSpec
import all Kraken.Mem
import all Kraken.Separation

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.LratBytes

open Std Std.ExtHashMap Std.Sat
open Std.Tactic.BVDecide.LRAT.Internal
open Kraken.Bedrock2.Test
open LeanQbe.LratRup

/-! ## 1. Pure byte-scanner and `parseNat` helper lemmas -/

private theorem ptr_add_ofNat (base : Val) (a b : Nat) :
    base + BitVec.ofNat 64 a + BitVec.ofNat 64 b = base + BitVec.ofNat 64 (a + b) :=
  BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_add]; omega)

private theorem ptr_step_1 (base : Val) (i : Nat) :
    base + BitVec.ofNat 64 i + 1 = base + BitVec.ofNat 64 (i + 1) :=
  ptr_add_ofNat base i 1

private theorem cursor_eq_iff {base : Val} {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    base + BitVec.ofNat 64 i = base + BitVec.ofNat 64 j ↔ i = j := by
  constructor
  · intro h
    have h1 : (base + BitVec.ofNat 64 i) - base = (base + BitVec.ofNat 64 j) - base :=
      congrArg (· - base) h
    have h2 : BitVec.ofNat 64 i = BitVec.ofNat 64 j := by grind
    have h3 := congrArg BitVec.toNat h2
    simpa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using h3
  · rintro rfl; rfl

private theorem bv64_u8_eq {b k : UInt8} :
    BitVec.ofNat 64 b.toNat = BitVec.ofNat 64 k.toNat ↔ b = k := by
  have hb := b.toNat_lt
  have hk := k.toNat_lt
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp [Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : k.toNat < 2 ^ 64)] at this
    exact UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq this)
  · rintro rfl; rfl

private theorem boolVal_or (a b : Bool) : boolVal a ||| boolVal b = boolVal (a || b) := by
  cases a <;> cases b <;> decide

private theorem u8_le_iff_toNat {a b : UInt8} : a ≤ b ↔ a.toNat ≤ b.toNat :=
  UInt8.le_iff_toBitVec_le.trans BitVec.le_def

private theorem isWsByte_val (b : UInt8) :
    (boolVal (BitVec.ofNat 64 b.toNat == 32) |||
      boolVal ((BitVec.ofNat 64 b.toNat - 9).ult 5)) =
    boolVal (isDimacsWs b) := by
  rw [boolVal_or]
  congr 1
  have hb := b.toNat_lt
  unfold isDimacsWs
  have h1 : (BitVec.ofNat 64 b.toNat == (32 : Val)) = (b == 32) := by
    cases h : b == 32
    · rw [beq_eq_false_iff_ne] at h ⊢
      exact fun hc => h (bv64_u8_eq (k := 32) |>.mp hc)
    · rw [beq_iff_eq] at h ⊢
      exact bv64_u8_eq (k := 32) |>.mpr h
  have h2 : ((BitVec.ofNat 64 b.toNat - (9 : Val)).ult (5 : Val)) = (9 ≤ b && b ≤ 13) := by
    have hle9 : (9 ≤ b) ↔ 9 ≤ b.toNat := u8_le_iff_toNat
    have hle13 : (b ≤ 13) ↔ b.toNat ≤ 13 := u8_le_iff_toNat
    have hm : b.toNat % 2 ^ 64 = b.toNat := Nat.mod_eq_of_lt (by omega)
    simp only [BitVec.ult, BitVec.toNat_sub, BitVec.toNat_ofNat, hm]
    change decide ((2 ^ 64 - 9 + b.toNat) % 2 ^ 64 < 5) = (decide (9 ≤ b) && decide (b ≤ 13))
    by_cases h9 : 9 ≤ b.toNat
    · have hsub : (2 ^ 64 - 9 + b.toNat) % 2 ^ 64 = b.toNat - 9 := by omega
      rw [hsub]
      by_cases h13 : b.toNat ≤ 13 <;> simp [hle9, hle13, h9, h13] <;> omega
    · have hsub : (2 ^ 64 - 9 + b.toNat) % 2 ^ 64 = 2 ^ 64 - 9 + b.toNat := by omega
      rw [hsub]
      simp [hle9, h9]; omega
  rw [h1, h2]

private theorem u8_sub48_ult10 (b : UInt8) :
    (BitVec.ofNat 64 b.toNat - (48 : Val)).ult (10 : Val) = isDimacsDigit b := by
  have hb := b.toNat_lt
  unfold isDimacsDigit
  have hle48 : (48 ≤ b) ↔ 48 ≤ b.toNat := u8_le_iff_toNat
  have hle57 : (b ≤ 57) ↔ b.toNat ≤ 57 := u8_le_iff_toNat
  have hm : b.toNat % 2 ^ 64 = b.toNat := Nat.mod_eq_of_lt (by omega)
  simp only [BitVec.ult, BitVec.toNat_sub, BitVec.toNat_ofNat, hm]
  change decide ((2 ^ 64 - 48 + b.toNat) % 2 ^ 64 < 10) = (decide (48 ≤ b) && decide (b ≤ 57))
  by_cases h48 : 48 ≤ b.toNat
  · have hsub : (2 ^ 64 - 48 + b.toNat) % 2 ^ 64 = b.toNat - 48 := by omega
    rw [hsub]
    by_cases h57 : b.toNat ≤ 57 <;> simp [hle48, hle57, h48, h57] <;> omega
  · have hsub : (2 ^ 64 - 48 + b.toNat) % 2 ^ 64 = 2 ^ 64 - 48 + b.toNat := by omega
    rw [hsub]
    simp [hle48, h48]; omega

private theorem digit_bounds {b : UInt8} (hd : isDimacsDigit b = true) :
    48 ≤ b.toNat ∧ b.toNat - 48 < 10 ∧
      BitVec.ofNat 64 b.toNat - (48 : Val) = BitVec.ofNat 64 (b.toNat - 48) := by
  unfold isDimacsDigit at hd
  simp only [Bool.and_eq_true, decide_eq_true_eq, u8_le_iff_toNat] at hd
  have h1 : 48 ≤ b.toNat := hd.1
  have h2 : b.toNat ≤ 57 := hd.2
  refine ⟨h1, by omega, ?_⟩
  apply BitVec.eq_of_toNat_eq
  have hb := b.toNat_lt
  have hm1 : b.toNat % 2 ^ 64 = b.toNat := Nat.mod_eq_of_lt (by omega)
  have hm2 : (b.toNat - 48) % 2 ^ 64 = b.toNat - 48 := Nat.mod_eq_of_lt (by omega)
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, hm1, hm2]
  change (2 ^ 64 - 48 + b.toNat) % 2 ^ 64 = b.toNat - 48
  omega

private theorem skipWsCommentsAux_true_cons (c : UInt8) (bs : List UInt8) :
    skipWsCommentsAux true (c :: bs) =
      if c = 10 then skipWsCommentsAux false bs else skipWsCommentsAux true bs := by
  by_cases h : c = 10
  · subst h; rfl
  · simp [skipWsCommentsAux, h]

private theorem skipWsCommentsAux_false_cons (b : UInt8) (bs : List UInt8) :
    skipWsCommentsAux false (b :: bs) =
      if isDimacsWs b then skipWsCommentsAux false bs
      else if b == 99 then skipWsCommentsAux true bs
      else b :: bs := rfl

theorem parseDigitsAux_lt_bound {acc : Nat} {bs : List UInt8} {v : Nat} {rest : List UInt8}
    (hacc : acc < dimacsBound) (h : parseDigitsAux acc bs = some (v, rest)) :
    v < dimacsBound := by
  induction bs generalizing acc with
  | nil => simp [parseDigitsAux] at h; obtain ⟨rfl, _⟩ := h; exact hacc
  | cons b bs ih =>
    simp only [parseDigitsAux] at h
    split at h
    · split at h
      · rename_i hlt
        exact ih hlt h
      · nomatch h
    · split at h
      · simp at h; obtain ⟨rfl, _⟩ := h; exact hacc
      · nomatch h

theorem parseNat_lt_bound {bs : List UInt8} {v : Nat} {rest : List UInt8}
    (h : parseNat bs = some (v, rest)) : v < dimacsBound := by
  cases bs with
  | nil => nomatch h
  | cons b bs =>
    simp only [parseNat] at h
    split at h
    · rename_i hd
      have ⟨_, hd10, _⟩ := digit_bounds hd
      exact parseDigitsAux_lt_bound (by unfold dimacsBound; omega) h
    · nomatch h

/-! ## 2. QBE specifications for `isWsByte`, `skipWsCommentsQbe`, `skipWs1Qbe`, `readDimacsNat` -/

theorem isWsByte_spec {Γ : Env} {Q : Post} {X : XPost} {b : UInt8}
    {k : Val → Expr Val Cont} {m : Mem 64}
    (hk : wp Γ Q X (k (boolVal (isDimacsWs b))) [] [] m) :
    wp Γ Q X (isWsByte (BitVec.ofNat 64 b.toNat) k) [] [] m := by
  unfold isWsByte
  wp_unfold
  rwa [isWsByte_val]

theorem skipWsCommentsQbe_spec {Γ : Env} {Q : Post} {X : XPost}
    {base : Val} {bs : List UInt8} {i0 : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    {done : Val → Expr Val Cont}
    (hbase : base.toNat + bs.length < 2 ^ 64)
    (hi0 : i0 ≤ bs.length)
    (hm : (Eq (bs.At base) ⋆ R) m)
    (hdone : ∀ j, i0 ≤ j → j ≤ bs.length → bs.drop j = skipWsComments (bs.drop i0) →
      wp Γ Q X (done (base + BitVec.ofNat 64 j)) [] [] m) :
    wp Γ Q X (skipWsCommentsQbe (base + BitVec.ofNat 64 i0)
      (base + BitVec.ofNat 64 bs.length) done) [] [] m := by
  unfold skipWsCommentsQbe
  apply wp_join (fun as m' => ∃ j, i0 ≤ j ∧ j ≤ bs.length ∧
    bs.drop j = skipWsComments (bs.drop i0) ∧ as = [base + BitVec.ofNat 64 j] ∧ m' = m)
  · rintro _ m' ⟨j, hj1, hj2, hdrop, rfl, rfl⟩
    wp_unfold
    exact hdone j hj1 hj2 hdrop
  intro Jdone hJdone
  apply wp_loop (fun r as m' => ∃ i, i0 ≤ i ∧ i ≤ bs.length ∧ r = bs.length - i ∧
    skipWsCommentsAux false (bs.drop i) = skipWsComments (bs.drop i0) ∧
    as = [base + BitVec.ofNat 64 i] ∧ m' = m)
  · rintro Jswc r as m' ⟨i, hi1, hi2, rfl, hinv, rfl, hm_eq⟩ ih
    subst hm_eq
    wp_unfold
    refine ⟨fun heof => ?_, fun hneof => ?_⟩
    · have hi_eq : i = bs.length := (cursor_eq_iff (by omega) (by omega)).mp heof
      subst hi_eq
      refine hJdone _ _ ⟨bs.length, hi1, Nat.le_refl _, ?_, rfl, rfl⟩
      simpa [skipWsCommentsAux] using hinv
    · have hlt : i < bs.length := by
        rcases Nat.eq_or_lt_of_le hi2 with rfl | h
        · exact absurd rfl hneof
        · exact h
      have hdrop_i : bs.drop i = bs[i] :: bs.drop (i + 1) := List.drop_eq_getElem_cons hlt
      refine ⟨_, loadub_At hlt (by omega) hm, ?_⟩
      rw [ptr_step_1]
      refine isWsByte_spec ?_
      wp_unfold
      refine ⟨fun hws => ?_, fun hnws => ?_⟩
      · refine ih _ _ _ (by omega) ⟨i + 1, by omega, by omega, rfl, ?_, rfl, rfl⟩
        rw [hdrop_i, skipWsCommentsAux_false_cons] at hinv
        simpa [hws] using hinv
      · refine ⟨fun hisc => ?_, fun hnisc => ?_⟩
        · have hb99 : bs[i] = 99 := (bv64_u8_eq (k := 99)).mp hisc
          have hinv_c : skipWsCommentsAux true (bs.drop (i + 1)) = skipWsComments (bs.drop i0) := by
            rw [hdrop_i, skipWsCommentsAux_false_cons, hb99] at hinv
            have hnw99 : isDimacsWs 99 = false := by decide
            simpa [hnw99] using hinv
          apply wp_loop (fun r2 as2 m2 => ∃ k, i + 1 ≤ k ∧ k ≤ bs.length ∧ r2 = bs.length - k ∧
            skipWsCommentsAux true (bs.drop k) = skipWsComments (bs.drop i0) ∧
            as2 = [base + BitVec.ofNat 64 k] ∧ m2 = m')
          · rintro Jskl r2 as2 m2 ⟨k, hk1, hk2, rfl, hinv2, rfl, hm2_eq⟩ ih_skl
            subst hm2_eq
            wp_unfold
            refine ⟨fun hqeof => ?_, fun hnqeof => ?_⟩
            · have hk_eq : k = bs.length := (cursor_eq_iff (by omega) (by omega)).mp hqeof
              subst hk_eq
              refine hJdone _ _ ⟨bs.length, by omega, Nat.le_refl _, ?_, rfl, rfl⟩
              simpa [skipWsCommentsAux] using hinv2
            · have hklt : k < bs.length := by
                rcases Nat.eq_or_lt_of_le hk2 with rfl | h
                · exact absurd rfl hnqeof
                · exact h
              have hdrop_k : bs.drop k = bs[k] :: bs.drop (k + 1) := List.drop_eq_getElem_cons hklt
              refine ⟨_, loadub_At hklt (by omega) hm, ?_⟩
              rw [ptr_step_1]
              refine ⟨fun hisnl => ?_, fun hnisnl => ?_⟩
              · have hc10 : bs[k] = 10 := (bv64_u8_eq (k := 10)).mp hisnl
                refine ih _ _ _ (by omega) ⟨k + 1, by omega, by omega, rfl, ?_, rfl, rfl⟩
                rw [hdrop_k, skipWsCommentsAux_true_cons] at hinv2
                simpa [hc10] using hinv2
              · have hc10 : bs[k] ≠ 10 := fun h => hnisnl ((bv64_u8_eq (k := 10)).mpr h)
                refine ih_skl _ _ _ (by omega) ⟨k + 1, by omega, by omega, rfl, ?_, rfl, rfl⟩
                rw [hdrop_k, skipWsCommentsAux_true_cons] at hinv2
                simpa [hc10] using hinv2
          · intro Jskl hJskl
            wp_unfold
            exact hJskl _ _ _ ⟨i + 1, Nat.le_refl _, by omega, rfl, hinv_c, rfl, rfl⟩
        · have hb99 : (bs[i] == 99) = false :=
            beq_eq_false_iff_ne.mpr (fun h => hnisc ((bv64_u8_eq (k := 99)).mpr h))
          refine hJdone _ _ ⟨i, hi1, hi2, ?_, rfl, rfl⟩
          rw [hdrop_i, skipWsCommentsAux_false_cons, hnws, hb99] at hinv
          simpa [← hdrop_i] using hinv
  · intro Jswc hJswc
    wp_unfold
    exact hJswc _ _ _ ⟨i0, Nat.le_refl _, hi0, rfl, rfl, rfl, rfl⟩

theorem skipWs1Qbe_spec {Γ : Env} {Q : Post} {X : XPost} {fail : Cont}
    {base : Val} {bs : List UInt8} {i0 : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    {done : Val → Expr Val Cont}
    (hbase : base.toNat + bs.length < 2 ^ 64)
    (hi0 : i0 ≤ bs.length)
    (hm : (Eq (bs.At base) ⋆ R) m)
    (hfail : skipWs1 (bs.drop i0) = none → fail [] m)
    (hdone : ∀ j rest, skipWs1 (bs.drop i0) = some rest →
      i0 < j → j ≤ bs.length → bs.drop j = rest →
      wp Γ Q X (done (base + BitVec.ofNat 64 j)) [] [] m) :
    wp Γ Q X (skipWs1Qbe fail (base + BitVec.ofNat 64 i0)
      (base + BitVec.ofNat 64 bs.length) done) [] [] m := by
  unfold skipWs1Qbe
  wp_unfold
  refine ⟨fun heof0 => ?_, fun hneof0 => ?_⟩
  · have hi_eq : i0 = bs.length := (cursor_eq_iff (by omega) (by omega)).mp heof0
    subst hi_eq
    exact hfail (by simp [skipWs1])
  · have hlt0 : i0 < bs.length := by
      rcases Nat.eq_or_lt_of_le hi0 with rfl | h
      · exact absurd rfl hneof0
      · exact h
    have hdrop0 : bs.drop i0 = bs[i0] :: bs.drop (i0 + 1) := List.drop_eq_getElem_cons hlt0
    refine ⟨_, loadub_At hlt0 (by omega) hm, isWsByte_spec ?_⟩
    wp_unfold
    refine ⟨fun hws0 => ?_, fun hnws0 => ?_⟩
    · have hsw1 : skipWs1 (bs.drop i0) = some (skipWs (bs.drop (i0 + 1))) := by
        rw [hdrop0]; simp [skipWs1, hws0]
      apply wp_join (fun as m' => ∃ j, i0 < j ∧ j ≤ bs.length ∧
        bs.drop j = skipWs (bs.drop (i0 + 1)) ∧ as = [base + BitVec.ofNat 64 j] ∧ m' = m)
      · rintro _ _ ⟨j, hj1, hj2, hdrop, rfl, rfl⟩
        wp_unfold
        exact hdone j _ hsw1 hj1 hj2 hdrop
      intro Jdone hJdone
      apply wp_loop (fun r as m' => ∃ i, i0 < i ∧ i ≤ bs.length ∧ r = bs.length - i ∧
        skipWs (bs.drop i) = skipWs (bs.drop (i0 + 1)) ∧
        as = [base + BitVec.ofNat 64 i] ∧ m' = m)
      · rintro Jsw r as m' ⟨i, hi1, hi2, rfl, hinv, rfl, hm_eq⟩ ih
        subst hm_eq
        wp_unfold
        refine ⟨fun heof => ?_, fun hneof => ?_⟩
        · have hi_eq : i = bs.length := (cursor_eq_iff (by omega) (by omega)).mp heof
          subst hi_eq
          refine hJdone _ _ ⟨bs.length, hi1, Nat.le_refl _, ?_, rfl, rfl⟩
          simpa [skipWs] using hinv
        · have hlt : i < bs.length := by
            rcases Nat.eq_or_lt_of_le hi2 with rfl | h
            · exact absurd rfl hneof
            · exact h
          have hdrop_i : bs.drop i = bs[i] :: bs.drop (i + 1) := List.drop_eq_getElem_cons hlt
          refine ⟨_, loadub_At hlt (by omega) hm, isWsByte_spec ?_⟩
          wp_unfold
          refine ⟨fun hws => ?_, fun hnws => ?_⟩
          · rw [ptr_step_1]
            refine ih _ _ _ (by omega) ⟨i + 1, by omega, by omega, rfl, ?_, rfl, rfl⟩
            rw [hdrop_i, skipWs] at hinv
            simpa [hws] using hinv
          · refine hJdone _ _ ⟨i, hi1, hi2, ?_, rfl, rfl⟩
            rw [hdrop_i, skipWs, hnws] at hinv
            simpa [← hdrop_i] using hinv
      · intro Jsw hJsw
        wp_unfold
        rw [ptr_step_1]
        exact hJsw _ _ _ ⟨i0 + 1, by omega, by omega, rfl, rfl, rfl, rfl⟩
    · exact hfail (by rw [hdrop0]; simp [skipWs1, hnws0])

theorem readDimacsNat_spec {Γ : Env} {Q : Post} {X : XPost} {fail : Cont}
    {base : Val} {bs : List UInt8} {i0 : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    {done : Val → Val → Expr Val Cont}
    (hbase : base.toNat + bs.length < 2 ^ 64)
    (hi0 : i0 ≤ bs.length)
    (hm : (Eq (bs.At base) ⋆ R) m)
    (hfail : parseNat (bs.drop i0) = none → fail [] m)
    (hdone : ∀ v j rest, parseNat (bs.drop i0) = some (v, rest) →
      v < dimacsBound → i0 < j → j ≤ bs.length → bs.drop j = rest →
      wp Γ Q X (done (BitVec.ofNat 64 v) (base + BitVec.ofNat 64 j)) [] [] m) :
    wp Γ Q X (readDimacsNat fail (base + BitVec.ofNat 64 i0)
      (base + BitVec.ofNat 64 bs.length) done) [] [] m := by
  unfold readDimacsNat
  wp_unfold
  refine ⟨fun heof0 => ?_, fun hneof0 => ?_⟩
  · have hi_eq : i0 = bs.length := (cursor_eq_iff (by omega) (by omega)).mp heof0
    subst hi_eq
    exact hfail (by simp [parseNat])
  · have hlt0 : i0 < bs.length := by
      rcases Nat.eq_or_lt_of_le hi0 with rfl | h
      · exact absurd rfl hneof0
      · exact h
    have hdrop0 : bs.drop i0 = bs[i0] :: bs.drop (i0 + 1) := List.drop_eq_getElem_cons hlt0
    refine ⟨_, loadub_At hlt0 (by omega) hm, ?_⟩
    rw [u8_sub48_ult10]
    refine ⟨fun hd0 => ?_, fun hnd0 => ?_⟩
    · obtain ⟨_, hd0_lt, hd0_bv⟩ := digit_bounds hd0
      have hp0 : parseNat (bs.drop i0) = parseDigitsAux (bs[i0].toNat - 48) (bs.drop (i0 + 1)) := by
        rw [hdrop0]; simp [parseNat, hd0]
      apply wp_join (fun as m' => ∃ v j rest,
        parseNat (bs.drop i0) = some (v, rest) ∧ v < dimacsBound ∧
        i0 < j ∧ j ≤ bs.length ∧ bs.drop j = rest ∧
        as = [BitVec.ofNat 64 v, base + BitVec.ofNat 64 j] ∧ m' = m)
      · rintro _ _ ⟨v, j, rest, hp, hv, hj1, hj2, hdrop, rfl, rfl⟩
        wp_unfold
        exact hdone v j rest hp hv hj1 hj2 hdrop
      intro Jdone hJdone
      apply wp_loop (fun r as m' => ∃ i acc,
        i0 < i ∧ i ≤ bs.length ∧ r = bs.length - i ∧ acc < dimacsBound ∧
        parseDigitsAux acc (bs.drop i) = parseNat (bs.drop i0) ∧
        as = [base + BitVec.ofNat 64 i, BitVec.ofNat 64 acc] ∧ m' = m)
      · rintro Jpdig r as m' ⟨i, acc, hi1, hi2, rfl, hacc, hinv, rfl, hm_eq⟩ ih
        subst hm_eq
        wp_unfold
        refine ⟨fun heof => ?_, fun hneof => ?_⟩
        · have hi_eq : i = bs.length := (cursor_eq_iff (by omega) (by omega)).mp heof
          subst hi_eq
          refine hJdone _ _ ⟨acc, bs.length, [], ?_, hacc, hi1, Nat.le_refl _, by simp, rfl, rfl⟩
          simpa [parseDigitsAux] using hinv.symm
        · have hlt : i < bs.length := by
            rcases Nat.eq_or_lt_of_le hi2 with rfl | h
            · exact absurd rfl hneof
            · exact h
          have hdrop_i : bs.drop i = bs[i] :: bs.drop (i + 1) := List.drop_eq_getElem_cons hlt
          refine ⟨_, loadub_At hlt (by omega) hm, ?_⟩
          rw [u8_sub48_ult10]
          refine ⟨fun hd => ?_, fun hnd => ?_⟩
          · obtain ⟨_, hd_lt, hd_bv⟩ := digit_bounds hd
            rw [hd_bv]
            let acc2 := acc * 10 + (bs[i].toNat - 48)
            have hmul_add : BitVec.ofNat 64 acc * 10 + BitVec.ofNat 64 (bs[i].toNat - 48) =
                BitVec.ofNat 64 acc2 := by
              unfold dimacsBound at hacc
              apply BitVec.eq_of_toNat_eq
              simp [acc2, BitVec.toNat_add, BitVec.toNat_mul]
            rw [hmul_add]
            have hult_bound : (BitVec.ofNat 64 acc2).ult 268435456 = decide (acc2 < dimacsBound) := by
              unfold dimacsBound at hacc ⊢
              simp only [BitVec.ult, BitVec.toNat_ofNat]
              have : acc2 < 2 ^ 64 := by omega
              rw [Nat.mod_eq_of_lt this]
              congr 1
            rw [hult_bound]
            refine ⟨fun hokb => ?_, fun hnokb => ?_⟩
            · have hacc2 : acc2 < dimacsBound := of_decide_eq_true hokb
              rw [ptr_step_1]
              refine ih _ _ _ (by omega) ⟨i + 1, acc2, by omega, by omega, rfl, hacc2, ?_, rfl, rfl⟩
              rw [hdrop_i, parseDigitsAux] at hinv
              simpa [hd, hacc2, acc2] using hinv
            · have hnacc2 : ¬ acc2 < dimacsBound := of_decide_eq_false hnokb
              apply hfail
              rw [← hinv, hdrop_i, parseDigitsAux]
              simp [hd, hnacc2, acc2]
          · refine isWsByte_spec ?_
            wp_unfold
            refine ⟨fun hws => ?_, fun hnws => ?_⟩
            · refine hJdone _ _ ⟨acc, i, bs.drop i, ?_, hacc, hi1, hi2, rfl, rfl, rfl⟩
              rw [← hinv, hdrop_i, parseDigitsAux]
              simp [hnd, hws]
            · apply hfail
              rw [← hinv, hdrop_i, parseDigitsAux]
              simp [hnd, hnws]
      · intro Jpdig hJpdig
        wp_unfold
        rw [ptr_step_1, hd0_bv]
        exact hJpdig _ _ _ ⟨i0 + 1, bs[i0].toNat - 48, by omega, by omega, rfl,
          by unfold dimacsBound; omega, hp0.symm, rfl, rfl⟩
    · exact hfail (by rw [hdrop0]; simp [parseNat, hnd0])

/-! ## 3. Correctness of `lbParseDimacsHeader` -/

private def parseHeaderAfterCnf (bs3 : List UInt8) : Option (Nat × Nat × List UInt8) := do
  let bs4 ← skipWs1 bs3
  let (mv, bs5) ← parseNat bs4
  let bs6 ← skipWs1 bs5
  let (nc, bs7) ← parseNat bs6
  some (mv, nc, bs7)

private def parseHeaderCnfTag (bs2 : List UInt8) : Option (Nat × Nat × List UInt8) :=
  match bs2 with
  | 99 :: 110 :: 102 :: bs3 => parseHeaderAfterCnf bs3
  | _ => none

private theorem parseHeader_eq (bs : List UInt8) :
    parseHeader bs =
      match skipWsComments bs with
      | 112 :: bs1 => (skipWs1 bs1).bind parseHeaderCnfTag
      | _ => none := rfl

private theorem parseHeader_of_cons_112 (bs1 : List UInt8) :
    (match (112 : UInt8) :: bs1 with
     | 112 :: r => (skipWs1 r).bind parseHeaderCnfTag
     | _ => none) = (skipWs1 bs1).bind parseHeaderCnfTag := by
  split <;> grind

private theorem parseHeader_of_cons_ne112 {b : UInt8} (hb : b ≠ 112) (bs1 : List UInt8) :
    (match b :: bs1 with
     | 112 :: r => (skipWs1 r).bind parseHeaderCnfTag
     | _ => none) = none := by
  split <;> grind

private theorem parseHeaderCnfTag_ok (bs3 : List UInt8) :
    parseHeaderCnfTag (99 :: 110 :: 102 :: bs3) = parseHeaderAfterCnf bs3 := by
  unfold parseHeaderCnfTag; split <;> grind

private theorem parseHeaderCnfTag_short0 : parseHeaderCnfTag [] = none := rfl
private theorem parseHeaderCnfTag_short1 (a : UInt8) : parseHeaderCnfTag [a] = none := by
  unfold parseHeaderCnfTag; split <;> grind
private theorem parseHeaderCnfTag_short2 (a b : UInt8) : parseHeaderCnfTag [a, b] = none := by
  unfold parseHeaderCnfTag; split <;> grind
private theorem parseHeaderCnfTag_ne0 {a : UInt8} (ha : a ≠ 99) (r : List UInt8) :
    parseHeaderCnfTag (a :: r) = none := by
  unfold parseHeaderCnfTag; split <;> grind
private theorem parseHeaderCnfTag_ne1 (a : UInt8) {b : UInt8} (hb : b ≠ 110) (r : List UInt8) :
    parseHeaderCnfTag (a :: b :: r) = none := by
  unfold parseHeaderCnfTag; split <;> grind
private theorem parseHeaderCnfTag_ne2 (a b : UInt8) {c : UInt8} (hc : c ≠ 102) (r : List UInt8) :
    parseHeaderCnfTag (a :: b :: c :: r) = none := by
  unfold parseHeaderCnfTag; split <;> grind

private theorem region80_to_words10 {hdr : Val} {f : Mem 64} (hf : region hdr 80 f) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : Val,
      word8Array hdr [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9] f := by
  obtain ⟨ws, hlen, hwa⟩ := region_to_word8Array 10 (by decide) (by simpa using hf)
  rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | ⟨w8, _ | ⟨w9, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp at hlen
  exact ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, hwa⟩

theorem lbParseDimacsHeader_correct (Γ : Env) :
    ∀ args m Q X, lbParseDimacsHeaderSpec args m Q X → Func.spec Γ lbParseDimacsHeader args m Q X := by
  rintro args m Q X ⟨cnf_ptr, hdr, cnfBytes, R, rfl, hcnf, _, hm, hpost⟩
  unfold lbParseDimacsHeader Func.spec
  wp_unfold
  have hm_cnf : (Eq (cnfBytes.At cnf_ptr) ⋆ (region hdr 80 ⋆ R)) m := sep_cast hm (by ac_rfl)
  apply wp_join (fun as m' => as = [] ∧ m' = m ∧ parseHeader cnfBytes = none)
  · rintro _ _ ⟨rfl, rfl, hnone⟩
    wp_unfold
    apply hpost
    rw [hnone]
    exact ⟨rfl, hm⟩
  intro Jfail hJfail
  have hfail_of : parseHeader cnfBytes = none → Jfail [] m := fun h => hJfail [] m ⟨rfl, rfl, h⟩
  conv => arg 4; arg 1; rw [show cnf_ptr = cnf_ptr + BitVec.ofNat 64 0 by simp]
  refine skipWsCommentsQbe_spec (i0 := 0) hcnf (Nat.zero_le _) hm_cnf fun i1 _ hi1 hsw1 => ?_
  simp only [List.drop_zero] at hsw1
  wp_unfold
  refine ⟨fun heof1 => ?_, fun hneof1 => ?_⟩
  · have hi1_eq : i1 = cnfBytes.length := (cursor_eq_iff (by omega) (by omega)).mp heof1
    subst hi1_eq
    apply hfail_of
    rw [parseHeader_eq, ← hsw1]; simp
  · have hlt1 : i1 < cnfBytes.length := by
      rcases Nat.eq_or_lt_of_le hi1 with rfl | h
      · exact absurd rfl hneof1
      · exact h
    have hd1 : cnfBytes.drop i1 = cnfBytes[i1] :: cnfBytes.drop (i1 + 1) := List.drop_eq_getElem_cons hlt1
    refine ⟨_, loadub_At hlt1 (by omega) hm_cnf, fun hisp => ?_, fun hnisp => ?_⟩
    · have hp112 : cnfBytes[i1] = 112 := (bv64_u8_eq (k := 112)).mp hisp
      have hph1 : parseHeader cnfBytes = (skipWs1 (cnfBytes.drop (i1 + 1))).bind parseHeaderCnfTag := by
        rw [parseHeader_eq, ← hsw1, hd1, hp112, parseHeader_of_cons_112]
      rw [ptr_step_1]
      refine skipWs1Qbe_spec hcnf (by omega) hm_cnf
        (fun hnone => hfail_of (by rw [hph1, hnone]; rfl))
        fun i2 bs2 hbs2 _ hi2 hd2 => ?_
      wp_unfold
      refine ⟨fun heofc0 => ?_, fun hneofc0 => ?_⟩
      · have hi2_eq : i2 = cnfBytes.length := (cursor_eq_iff (by omega) (by omega)).mp heofc0
        subst hi2_eq
        apply hfail_of
        have hbs2_nil : bs2 = [] := by rw [← hd2]; simp
        rw [hph1, hbs2, hbs2_nil]; exact parseHeaderCnfTag_short0
      · have hlt2 : i2 < cnfBytes.length := by
          rcases Nat.eq_or_lt_of_le hi2 with rfl | h
          · exact absurd rfl hneofc0
          · exact h
        have hd2_0 : cnfBytes.drop i2 = cnfBytes[i2] :: cnfBytes.drop (i2 + 1) := List.drop_eq_getElem_cons hlt2
        refine ⟨_, loadub_At hlt2 (by omega) hm_cnf, fun hisc => ?_, fun hnisc => ?_⟩
        · have hc99 : cnfBytes[i2] = 99 := (bv64_u8_eq (k := 99)).mp hisc
          rw [ptr_step_1]
          refine ⟨fun heofc1 => ?_, fun hneofc1 => ?_⟩
          · have hi2_1 : i2 + 1 = cnfBytes.length := (cursor_eq_iff (by omega) (by omega)).mp heofc1
            apply hfail_of
            have hnil : cnfBytes.drop (i2 + 1) = [] := by rw [hi2_1]; simp
            rw [hph1, hbs2, ← hd2, hd2_0, hc99, hnil]; exact parseHeaderCnfTag_short1 99
          · have hlt2_1 : i2 + 1 < cnfBytes.length := by
              rcases Nat.eq_or_lt_of_le (show i2 + 1 ≤ cnfBytes.length by omega) with h | h
              · exact absurd ((cursor_eq_iff (by omega) (by omega)).mpr h) hneofc1
              · exact h
            have hd2_1 : cnfBytes.drop (i2 + 1) = cnfBytes[i2 + 1] :: cnfBytes.drop (i2 + 2) :=
              List.drop_eq_getElem_cons hlt2_1
            refine ⟨_, loadub_At hlt2_1 (by omega) hm_cnf, fun hisn => ?_, fun hnisn => ?_⟩
            · have hn110 : cnfBytes[i2 + 1] = 110 := (bv64_u8_eq (k := 110)).mp hisn
              rw [show cnf_ptr + BitVec.ofNat 64 i2 + 2 = cnf_ptr + BitVec.ofNat 64 (i2 + 2) from
                ptr_add_ofNat cnf_ptr i2 2]
              refine ⟨fun heofc2 => ?_, fun hneofc2 => ?_⟩
              · have hi2_2 : i2 + 2 = cnfBytes.length := (cursor_eq_iff (by omega) (by omega)).mp heofc2
                apply hfail_of
                have hnil : cnfBytes.drop (i2 + 2) = [] := by rw [hi2_2]; simp
                rw [hph1, hbs2, ← hd2, hd2_0, hc99, hd2_1, hn110, hnil]
                exact parseHeaderCnfTag_short2 99 110
              · have hlt2_2 : i2 + 2 < cnfBytes.length := by
                  rcases Nat.eq_or_lt_of_le (show i2 + 2 ≤ cnfBytes.length by omega) with h | h
                  · exact absurd ((cursor_eq_iff (by omega) (by omega)).mpr h) hneofc2
                  · exact h
                have hd2_2 : cnfBytes.drop (i2 + 2) = cnfBytes[i2 + 2] :: cnfBytes.drop (i2 + 3) :=
                  List.drop_eq_getElem_cons hlt2_2
                refine ⟨_, loadub_At hlt2_2 (by omega) hm_cnf, fun hisf => ?_, fun hnisf => ?_⟩
                · have hf102 : cnfBytes[i2 + 2] = 102 := (bv64_u8_eq (k := 102)).mp hisf
                  have hph2 : parseHeader cnfBytes = parseHeaderAfterCnf (cnfBytes.drop (i2 + 3)) := by
                    rw [hph1, hbs2, ← hd2, hd2_0, hc99, hd2_1, hn110, hd2_2, hf102]
                    exact parseHeaderCnfTag_ok _
                  rw [show cnf_ptr + BitVec.ofNat 64 i2 + 3 = cnf_ptr + BitVec.ofNat 64 (i2 + 3) from
                    ptr_add_ofNat cnf_ptr i2 3]
                  refine skipWs1Qbe_spec hcnf (by omega) hm_cnf
                    (fun hnone => hfail_of (by rw [hph2]; simp [parseHeaderAfterCnf, hnone]))
                    fun i3 bs4 hbs4 _ hi3 hd3 => ?_
                  subst hd3
                  refine readDimacsNat_spec hcnf hi3 hm_cnf
                    (fun hnone => hfail_of (by rw [hph2]; simp [parseHeaderAfterCnf, hbs4, hnone]))
                    fun mv i4 bs5 hbs5 hmv _ hi4 hd4 => ?_
                  subst hd4
                  refine skipWs1Qbe_spec hcnf hi4 hm_cnf
                    (fun hnone => hfail_of (by rw [hph2]; simp [parseHeaderAfterCnf, hbs4, hbs5, hnone]))
                    fun i5 bs6 hbs6 _ hi5 hd5 => ?_
                  subst hd5
                  refine readDimacsNat_spec hcnf hi5 hm_cnf
                    (fun hnone => hfail_of (by rw [hph2]; simp [parseHeaderAfterCnf, hbs4, hbs5, hbs6, hnone]))
                    fun nc i6 bs7 hbs7 hnc _ hi6 hd6 => ?_
                  wp_unfold
                  have hph_ok : parseHeader cnfBytes = some (mv, nc, bs7) := by
                    rw [hph2]; simp [parseHeaderAfterCnf, hbs4, hbs5, hbs6, hbs7]
                  have hm_hdr : (region hdr 80 ⋆ (Eq (cnfBytes.At cnf_ptr) ⋆ R)) m :=
                    sep_cast hm (by ac_rfl)
                  obtain ⟨f1, f2, hu, hd_m, hf1, hf2⟩ := hm_hdr
                  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, hwa⟩ := region80_to_words10 hf1
                  have hm0 : (word8Array hdr [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9] ⋆
                      (Eq (cnfBytes.At cnf_ptr) ⋆ R)) m := ⟨f1, f2, hu, hd_m, hwa, hf2⟩
                  have ⟨ok0, hm1⟩ := storel_word8Array (i := 0) (BitVec.ofNat 64 mv) (by simp) hm0
                  simp only [Nat.mul_zero, BitVec.add_zero, List.set_cons_zero] at ok0 hm1
                  have ⟨ok1, hm2⟩ := storel_word8Array (i := 1) (BitVec.ofNat 64 nc) (by simp) hm1
                  have ⟨ok9, hm3⟩ := storel_word8Array (i := 9) (cnf_ptr + BitVec.ofNat 64 i6) (by simp) hm2
                  refine ⟨ok0, ok1, ok9, ?_⟩
                  apply hpost
                  rw [hph_ok]
                  have hi6_eq : cnfBytes.length - bs7.length = i6 := by
                    rw [← hd6, List.length_drop]; omega
                  have hbs7_len : bs7.length ≤ cnfBytes.length := by
                    rw [← hd6, List.length_drop]; omega
                  refine ⟨rfl, hmv, hnc, by rw [hi6_eq, hd6], hbs7_len, w2, w3, w4, w5, w6, w7, w8, ?_⟩
                  rw [hi6_eq]
                  exact sep_cast hm3 (by simp only [List.set]; ac_rfl)
                · have hne102 : cnfBytes[i2 + 2] ≠ 102 := fun h => hnisf ((bv64_u8_eq (k := 102)).mpr h)
                  apply hfail_of
                  rw [hph1, hbs2, ← hd2, hd2_0, hc99, hd2_1, hn110, hd2_2]
                  exact parseHeaderCnfTag_ne2 99 110 hne102 _
            · have hne110 : cnfBytes[i2 + 1] ≠ 110 := fun h => hnisn ((bv64_u8_eq (k := 110)).mpr h)
              apply hfail_of
              rw [hph1, hbs2, ← hd2, hd2_0, hc99, hd2_1]
              exact parseHeaderCnfTag_ne1 99 hne110 _
        · have hne99 : cnfBytes[i2] ≠ 99 := fun h => hnisc ((bv64_u8_eq (k := 99)).mpr h)
          apply hfail_of
          rw [hph1, hbs2, ← hd2, hd2_0]
          exact parseHeaderCnfTag_ne0 hne99 _
    · have hne112 : cnfBytes[i1] ≠ 112 := fun h => hnisp ((bv64_u8_eq (k := 112)).mpr h)
      apply hfail_of
      rw [parseHeader_eq, ← hsw1, hd1]
      exact parseHeader_of_cons_ne112 hne112 _

/-! ## 4. Pure clause/body helpers and `lbParseDimacsBody_correct` -/

private theorem skipWsCommentsAux_length_le (inC : Bool) (bs : List UInt8) :
    (skipWsCommentsAux inC bs).length ≤ bs.length := by
  induction bs generalizing inC with
  | nil => cases inC <;> simp [skipWsCommentsAux]
  | cons b bs ih =>
    cases inC
    · rw [skipWsCommentsAux_false_cons]
      split
      · exact Nat.le_trans (ih false) (by simp)
      · split
        · exact Nat.le_trans (ih true) (by simp)
        · exact Nat.le_refl _
    · rw [skipWsCommentsAux_true_cons]
      split <;> exact Nat.le_trans (ih _) (by simp)

theorem skipWsComments_length_le (bs : List UInt8) :
    (skipWsComments bs).length ≤ bs.length :=
  skipWsCommentsAux_length_le false bs

private theorem parseDigitsAux_length_le {acc : Nat} {bs : List UInt8} {v : Nat} {rest : List UInt8}
    (h : parseDigitsAux acc bs = some (v, rest)) : rest.length ≤ bs.length := by
  induction bs generalizing acc with
  | nil => simp [parseDigitsAux] at h; obtain ⟨_, rfl⟩ := h; exact Nat.le_refl _
  | cons b bs ih =>
    simp only [parseDigitsAux] at h
    split at h
    · split at h
      · exact Nat.le_trans (ih h) (by simp)
      · nomatch h
    · split at h
      · simp at h; obtain ⟨_, rfl⟩ := h; exact Nat.le_refl _
      · nomatch h

theorem parseNat_length_lt {bs : List UInt8} {v : Nat} {rest : List UInt8}
    (h : parseNat bs = some (v, rest)) : rest.length < bs.length := by
  cases bs with
  | nil => nomatch h
  | cons b bs =>
    simp only [parseNat] at h
    split at h
    · have := parseDigitsAux_length_le h; simp; omega
    · nomatch h

private theorem parseClausePure_succ_nil {fuel mv poolRem : Nat} {acc : List Val} {bs : List UInt8}
    (h : skipWsComments bs = []) :
    parseClausePure (fuel + 1) mv poolRem acc bs = none := by
  simp [parseClausePure, h]

private theorem parseClausePure_succ_45 {fuel mv poolRem : Nat} {acc : List Val}
    {bs rest : List UInt8} (h : skipWsComments bs = 45 :: rest) :
    parseClausePure (fuel + 1) mv poolRem acc bs =
      if poolRem == 0 then none
      else match parseNat rest with
      | none => none
      | some (v, rest') =>
        if v == 0 || mv < v then none
        else parseClausePure fuel mv (poolRem - 1) (-BitVec.ofNat 64 v :: acc) rest' := by
  simp only [parseClausePure, h]
  rcases parseNat rest with _ | ⟨v, rest'⟩ <;> rfl

private theorem parseClausePure_succ_pos {fuel mv poolRem : Nat} {acc : List Val}
    {b : UInt8} {bs rest : List UInt8} (h : skipWsComments bs = b :: rest) (hb : b ≠ 45) :
    parseClausePure (fuel + 1) mv poolRem acc bs =
      if poolRem == 0 then none
      else match parseNat (b :: rest) with
      | none => none
      | some (v, rest') =>
        if v == 0 then some (acc.reverse, poolRem - 1, rest')
        else if mv < v then none
        else parseClausePure fuel mv (poolRem - 1) (BitVec.ofNat 64 v :: acc) rest' := by
  have := hb
  simp [parseClausePure, h]
  rcases parseNat (b :: rest) with _ | ⟨v, rest'⟩ <;> simp

theorem parseClausePure_fuel_irrel {f1 f2 mv poolRem : Nat} {acc : List Val} {bs : List UInt8}
    (h1 : bs.length < f1) (h2 : bs.length < f2) :
    parseClausePure f1 mv poolRem acc bs = parseClausePure f2 mv poolRem acc bs := by
  induction f1 generalizing f2 poolRem acc bs with
  | zero => omega
  | succ fuel1 ih =>
    cases f2 with
    | zero => omega
    | succ fuel2 =>
      have hsw_len := skipWsComments_length_le bs
      cases hsw : skipWsComments bs with
      | nil => rw [parseClausePure_succ_nil hsw, parseClausePure_succ_nil hsw]
      | cons b rest =>
        have hcr_len : (b :: rest).length ≤ bs.length := by rwa [← hsw]
        by_cases hb : b = 45
        · subst hb
          rw [parseClausePure_succ_45 hsw, parseClausePure_succ_45 hsw]
          split
          · rfl
          · cases hp : parseNat rest with
            | none => rfl
            | some vr =>
              obtain ⟨v, rest'⟩ := vr
              have hr_lt := parseNat_length_lt hp
              simp only [List.length_cons] at hcr_len
              dsimp
              split
              · rfl
              · exact ih (by omega) (by omega)
        · rw [parseClausePure_succ_pos hsw hb, parseClausePure_succ_pos hsw hb]
          split
          · rfl
          · cases hp : parseNat (b :: rest) with
            | none => rfl
            | some vr =>
              obtain ⟨v, rest'⟩ := vr
              have hr_lt := parseNat_length_lt hp
              dsimp
              split
              · rfl
              · split
                · rfl
                · exact ih (by omega) (by omega)

private theorem bv64_ofNat_slt_zero {v : Nat} (hv : v < 2 ^ 28) :
    (BitVec.ofNat 64 v).slt 0#64 = false := by
  unfold BitVec.slt BitVec.toInt
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : v < 2 ^ 64), decide_eq_false_iff_not]
  split <;> omega

theorem isValidLit_ofNat {mv v : Nat} (hv1 : 1 ≤ v) (hvm : v ≤ mv) (hmv : mv < dimacsBound) :
    IsValidLit mv (BitVec.ofNat 64 v) := by
  unfold dimacsBound at hmv
  have hslt := bv64_ofNat_slt_zero (v := v) (by omega)
  refine ⟨?_, ?_, ?_, by omega⟩
  · unfold IsInt32; grind
  · intro hz
    have := congrArg BitVec.toNat hz
    simp [Nat.mod_eq_of_lt (by omega : v < 2 ^ 64)] at this
    omega
  · unfold bvAbs
    rw [show (0 : BitVec 64) = 0#64 from rfl, hslt]
    simp [Nat.mod_eq_of_lt (by omega : v < 2 ^ 64), hvm]

theorem toLiteral_ofNat {v : Nat} (_hv1 : 1 ≤ v) (hvb : v < dimacsBound) :
    toLiteral (BitVec.ofNat 64 v) = (v, true) := by
  unfold dimacsBound at hvb
  have hslt := bv64_ofNat_slt_zero hvb
  unfold toLiteral bvAbs
  rw [show (0 : BitVec 64) = 0#64 from rfl, hslt]
  simp [Nat.mod_eq_of_lt (by omega : v < 2 ^ 64)]

theorem toLiteral_neg_ofNat {mv v : Nat} (hv1 : 1 ≤ v) (hvm : v ≤ mv) (hmv : mv < dimacsBound) :
    toLiteral (-BitVec.ofNat 64 v) = (v, false) := by
  have hval := isValidLit_ofNat hv1 hvm hmv
  rw [toLiteral_neg hval, toLiteral_ofNat hv1 (by omega)]
  rfl

private theorem toNat_add_ofNat {a : Val} {k : Nat} (h : a.toNat + k < 2 ^ 64) :
    (a + BitVec.ofNat 64 k).toNat = a.toNat + k := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem workCfg_hfit_eq (c : WorkCfg) :
    c.hdr.toNat + (80 + c.vBytes + c.tBytes + 8 * c.cap + 4 * c.poolInts) < 2 ^ 64 :=
  c.hfit

private theorem workCfg_pbase_toNat (c : WorkCfg) :
    c.pbase.toNat = c.hdr.toNat + 80 + c.vBytes + c.tBytes + 8 * c.cap ∧
      c.pbase.toNat + 4 * c.poolInts < 2 ^ 64 := by
  have hfit := workCfg_hfit_eq c
  have h1 : c.vb.toNat = c.hdr.toNat + 80 := by
    unfold WorkCfg.vb
    exact toNat_add_ofNat (a := c.hdr) (k := 80) (by omega)
  have h2 : c.tb.toNat = c.hdr.toNat + 80 + c.vBytes := by
    unfold WorkCfg.tb
    rw [toNat_add_ofNat (by omega), h1]
  have h3 : c.cb.toNat = c.hdr.toNat + 80 + c.vBytes + c.tBytes := by
    unfold WorkCfg.cb
    rw [toNat_add_ofNat (by omega), h2]
  have h4 : c.pbase.toNat = c.hdr.toNat + 80 + c.vBytes + c.tBytes + 8 * c.cap := by
    unfold WorkCfg.pbase
    rw [toNat_add_ofNat (by omega), h3]
  exact ⟨h4, by omega⟩

private theorem workCfg_pcur_ne_zero (c : WorkCfg) {u : Nat} (hu : u ≤ c.poolInts) :
    c.pbase + BitVec.ofNat 64 (4 * u) ≠ 0 := by
  obtain ⟨hpbase, hpfit⟩ := workCfg_pbase_toNat c
  intro hz
  have h : (c.pbase + BitVec.ofNat 64 (4 * u)).toNat = 0 := congrArg BitVec.toNat hz
  rw [toNat_add_ofNat (by omega)] at h
  omega

private theorem workCfg_wcur_eq_plim_iff (c : WorkCfg) {u : Nat} (hu : u ≤ c.poolInts) :
    c.pbase + BitVec.ofNat 64 (4 * u) = c.plim ↔ u = c.poolInts := by
  obtain ⟨_, hpfit⟩ := workCfg_pbase_toNat c
  unfold WorkCfg.plim
  rw [cursor_eq_iff (by omega) (by omega)]
  omega

private theorem sep4_1_front {A B C D : Mem 64 → Prop} : (((A ⋆ B) ⋆ C) ⋆ D) = (A ⋆ (B ⋆ C ⋆ D)) := by ac_rfl
private theorem sep4_2_front {A B C D : Mem 64 → Prop} : (((A ⋆ B) ⋆ C) ⋆ D) = (B ⋆ (A ⋆ C ⋆ D)) := by ac_rfl
private theorem sep4_ws_pack {A B C D : Mem 64 → Prop} : (((A ⋆ B) ⋆ C) ⋆ D) = ((B ⋆ (A ⋆ C)) ⋆ D) := by ac_rfl
private theorem sep4_cb_back {CB BF PZ Rest : Mem 64 → Prop} :
    (CB ⋆ ((BF ⋆ PZ) ⋆ Rest)) = (((BF ⋆ CB) ⋆ PZ) ⋆ Rest) := by ac_rfl
private theorem sep5_1_front {A B C D E : Mem 64 → Prop} :
    ((((A ⋆ B) ⋆ C) ⋆ D) ⋆ E) = (A ⋆ (B ⋆ C ⋆ D ⋆ E)) := by ac_rfl
private theorem sep5_reg_front {A B C D E : Mem 64 → Prop} :
    ((((A ⋆ B) ⋆ C) ⋆ D) ⋆ E) = (D ⋆ (A ⋆ B ⋆ C ⋆ E)) := by ac_rfl
private theorem sep5_zt_bm_front {A B C D E : Mem 64 → Prop} :
    ((((A ⋆ B) ⋆ C) ⋆ D) ⋆ E) = ((C ⋆ B) ⋆ (A ⋆ D ⋆ E)) := by ac_rfl
private theorem sep5_bm_back {BM A D E : Mem 64 → Prop} :
    (BM ⋆ ((A ⋆ D) ⋆ E)) = (((A ⋆ BM) ⋆ D) ⋆ E) := by ac_rfl
private theorem sep5_cb_front {ZT BF CB PU Rest : Mem 64 → Prop} :
    ((ZT ⋆ ((BF ⋆ CB) ⋆ PU)) ⋆ Rest) = (CB ⋆ ((BF ⋆ (PU ⋆ ZT)) ⋆ Rest)) := by ac_rfl
private theorem sep6_reg_back {W R2 A B C E : Mem 64 → Prop} :
    (W ⋆ (R2 ⋆ (((A ⋆ B) ⋆ C) ⋆ E))) = ((((A ⋆ B) ⋆ (C ⋆ W)) ⋆ R2) ⋆ E) := by ac_rfl

private def BodyFixed (c : WorkCfg) (cur0 : Val) : Mem 64 → Prop :=
  word8Array c.hdr (c.hdrWords c.pbase cur0) ⋆
  byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
  region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
  region c.tb c.tRaw ⋆
  region c.tlim (c.tBytes - c.tRaw)

private def BodyMid (c : WorkCfg) (cur0 : Val) (ptrs : List Val) (PoolUsed : Mem 64 → Prop) :
    Mem 64 → Prop :=
  BodyFixed c cur0 ⋆ word8Array c.cb ptrs ⋆ PoolUsed

private theorem bodyMid_load_hdr {c : WorkCfg} {cur0 : Val} {ptrs : List Val}
    {PoolUsed R : Mem 64 → Prop} {m : Mem 64} {i : Nat} (hi : i < 10)
    (hm : (BodyMid c cur0 ptrs PoolUsed ⋆ R) m) :
    loadVal m .l .l false (c.hdr + BitVec.ofNat 64 (8 * i)) =
      some ((c.hdrWords c.pbase cur0)[i]'(by simp [WorkCfg.hdrWords, hi])) := by
  unfold BodyMid BodyFixed at hm
  simp only [sep_assoc] at hm
  exact loadl_word8Array (by simp [WorkCfg.hdrWords, hi]) hm

private theorem collapse_body_state (c : WorkCfg) {cur0 : Val}
    {poolUsed accLen rem : Nat} {ptrs lits : List Val} {PoolUsed : Mem 64 → Prop} {m : Mem 64}
    (hplen : ptrs.length = c.cap)
    (hll : lits.length = accLen)
    (hsum : poolUsed + accLen + rem = c.poolInts)
    (hpu : ∀ f, PoolUsed f → region c.pbase (4 * poolUsed) f)
    (hm : (BodyMid c cur0 ptrs PoolUsed ⋆
      int4Array (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) lits ⋆
      region (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + accLen))) (4 * rem)) m) :
    region c.hdr c.activeBytes m := by
  unfold BodyMid BodyFixed at hm
  have hfit := workCfg_hfit_eq c
  have hmv := c.hmv
  unfold dimacsBound at hmv
  have hvb : c.mv + 1 ≤ c.vBytes := by unfold WorkCfg.vBytes; omega
  have htb : c.tRaw ≤ c.tBytes := by unfold WorkCfg.tBytes; omega
  let pcur := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
  let wcur := c.pbase + BitVec.ofNat 64 (4 * (poolUsed + accLen))
  have r_hdr : ∀ f, word8Array c.hdr (c.hdrWords c.pbase cur0) f → region c.hdr 80 f := fun f hf => by
    have := word8Array_to_region (by simp [WorkCfg.hdrWords]) hf
    simpa [WorkCfg.hdrWords] using this
  have r_val : ∀ f, byte1Array c.vb (assignBytes c.mv Assignment.empty) f →
      region c.vb (c.mv + 1) f := fun f hf => by
    have := byte1Array_to_region (by simp; omega) hf
    simpa using this
  have r_cb : ∀ f, word8Array c.cb ptrs f → region c.cb (8 * c.cap) f := fun f hf => by
    have := word8Array_to_region (by rw [hplen]; omega) hf
    rwa [hplen] at this
  have r_lits : ∀ f, int4Array pcur lits f → region pcur (4 * accLen) f := fun f hf => by
    have := int4Array_to_region (by rw [hll]; omega) hf
    rwa [hll] at this
  have hm1 : (region c.hdr 80 ⋆
      region c.vb (c.mv + 1) ⋆
      region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
      region c.tb c.tRaw ⋆
      region c.tlim (c.tBytes - c.tRaw) ⋆
      region c.cb (8 * c.cap) ⋆
      region c.pbase (4 * poolUsed) ⋆
      region pcur (4 * accLen) ⋆
      region wcur (4 * rem)) m :=
    sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
      r_hdr r_val) (fun _ h => h)) (fun _ h => h)) (fun _ h => h)) r_cb) hpu) r_lits) (fun _ h => h) m hm
  have hwcur : wcur = pcur + BitVec.ofNat 64 (4 * accLen) := by
    dsimp [wcur, pcur]
    rw [ptr_add_ofNat]
    congr 2; omega
  have e_ar : (region pcur (4 * accLen) ⋆ region wcur (4 * rem)) = region pcur (4 * (accLen + rem)) := by
    rw [hwcur]
    have : 4 * (accLen + rem) = 4 * accLen + 4 * rem := by omega
    rw [this, region_split (by omega)]
  have e_pool : (region c.pbase (4 * poolUsed) ⋆ region pcur (4 * (accLen + rem))) =
      region c.pbase (4 * c.poolInts) := by
    have : 4 * c.poolInts = 4 * poolUsed + 4 * (accLen + rem) := by omega
    rw [this, region_split (by omega)]
  have e_cb : (region c.cb (8 * c.cap) ⋆ region c.pbase (4 * c.poolInts)) =
      region c.cb (8 * c.cap + 4 * c.poolInts) := by
    conv => rhs; rw [region_split (by omega)]
    rfl
  have e_t : (region c.tb c.tRaw ⋆ region c.tlim (c.tBytes - c.tRaw)) = region c.tb c.tBytes := by
    have : c.tBytes = c.tRaw + (c.tBytes - c.tRaw) := by omega
    conv => rhs; rw [this, region_split (by omega)]
    rfl
  have e_v : (region c.vb (c.mv + 1) ⋆
      region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1))) =
      region c.vb c.vBytes := by
    have : c.vBytes = (c.mv + 1) + (c.vBytes - (c.mv + 1)) := by omega
    conv => rhs; rw [this, region_split (by omega)]
  have e_tcb : (region c.tb c.tBytes ⋆ region c.cb (8 * c.cap + 4 * c.poolInts)) =
      region c.tb (c.tBytes + (8 * c.cap + 4 * c.poolInts)) := by
    conv => rhs; rw [region_split (by omega)]
    rfl
  have e_vtcb : (region c.vb c.vBytes ⋆ region c.tb (c.tBytes + (8 * c.cap + 4 * c.poolInts))) =
      region c.vb (c.vBytes + (c.tBytes + (8 * c.cap + 4 * c.poolInts))) := by
    conv => rhs; rw [region_split (by omega)]
    rfl
  have e_all : (region c.hdr 80 ⋆ region c.vb (c.vBytes + (c.tBytes + (8 * c.cap + 4 * c.poolInts)))) =
      region c.hdr c.activeBytes := by
    have : c.activeBytes = 80 + (c.vBytes + (c.tBytes + (8 * c.cap + 4 * c.poolInts))) := by
      unfold WorkCfg.activeBytes; omega
    conv => rhs; rw [this, region_split (by omega)]
    rfl
  simp only [sep_assoc] at hm1
  rw [e_ar, e_pool, e_cb, ← sep_assoc (region c.tb c.tRaw), e_t, e_tcb,
      ← sep_assoc (region c.vb (c.mv + 1)), e_v, e_vtcb, e_all] at hm1
  exact hm1

private theorem bodyMid_finish {c : WorkCfg} {cnf_ptr cur0 : Val} {cnfBytes : List UInt8}
    {poolUsed poolRem : Nat} {ptrs : List Val} {table : List (Option (List Val))}
    {PoolUsed R : Mem 64 → Prop} {m : Mem 64}
    (hpsum : poolUsed + poolRem = c.poolInts)
    (htr : TableRel c.mv c.cap ptrs table PoolUsed)
    (hpu : ∀ f, PoolUsed f → region c.pbase (4 * poolUsed) f)
    (hm : ((Eq (cnfBytes.At cnf_ptr) ⋆
      BodyMid c cur0 ptrs PoolUsed ⋆
      region (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) (4 * poolRem)) ⋆ R) m) :
    let pcur := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
    storeOk m .l (c.hdr + 64) ∧
    (Eq (cnfBytes.At cnf_ptr) ⋆
      WorkState c poolUsed poolRem cur0 ptrs table PoolUsed ⋆ R)
      (storeMem m .l (c.hdr + 64) pcur) := by
  intro pcur
  rw [sep4_2_front] at hm
  unfold BodyMid BodyFixed at hm
  simp only [sep_assoc] at hm
  have ⟨ok_p64, hm_done⟩ := storel_word8Array (i := 8) pcur (by simp [WorkCfg.hdrWords]) hm
  have hset : (c.hdrWords c.pbase cur0).set 8 pcur = c.hdrWords pcur cur0 := rfl
  rw [hset] at hm_done
  simp only [← sep_assoc] at hm_done
  rw [sep4_ws_pack] at hm_done
  refine ⟨ok_p64, ?_⟩
  exact sep_mono (fun _ => sep_mono_r fun _ hws => ⟨hpsum, htr, hpu, hws⟩) hm_done

private theorem bodyMid_store_clause {c : WorkCfg} {cur0 pcur : Val} {cidNat : Nat}
    {ptrs clits : List Val} {PoolUsed Rest : Mem 64 → Prop} {m : Mem 64}
    (hcid : cidNat < ptrs.length)
    (hm : ((ZeroTermInts pcur clits ⋆ BodyMid c cur0 ptrs PoolUsed) ⋆ Rest) m) :
    storeOk m .l (c.cb + BitVec.ofNat 64 (8 * cidNat)) ∧
    (BodyMid c cur0 (ptrs.set cidNat pcur) (PoolUsed ⋆ ZeroTermInts pcur clits) ⋆ Rest)
      (storeMem m .l (c.cb + BitVec.ofNat 64 (8 * cidNat)) pcur) := by
  unfold BodyMid at hm ⊢
  rw [sep5_cb_front] at hm
  obtain ⟨ok_slot, hm_slot⟩ := storel_word8Array pcur hcid hm
  rw [sep4_cb_back] at hm_slot
  exact ⟨ok_slot, hm_slot⟩

private theorem initClauseTable_nil {cap : Nat} (hcap : 1 ≤ cap) :
    initClauseTable cap [] = List.replicate cap none := by
  unfold initClauseTable
  cases cap with
  | zero => omega
  | succ k => simp [List.replicate_succ]

private theorem initClauseTable_set {cap : Nat} {clauses : List (List Val)} (clits : List Val)
    (h : clauses.length + 1 < cap) :
    (initClauseTable cap clauses).set (clauses.length + 1) (some clits) =
      initClauseTable cap (clauses ++ [clits]) := by
  unfold initClauseTable
  have hpre : (none :: clauses.map some).length = clauses.length + 1 := by simp
  rw [List.cons_append]
  change ((none :: clauses.map some) ++ List.replicate (cap - (clauses.length + 1)) none).set
    (clauses.length + 1) (some clits) = _
  rw [List.set_append_right _ _ (by omega)]
  rw [hpre, Nat.sub_self]
  obtain ⟨d, hd⟩ : ∃ d, cap - (clauses.length + 1) = d + 1 := ⟨cap - (clauses.length + 2), by omega⟩
  have hd2 : cap - ((clauses ++ [clits]).length + 1) = d := by simp; omega
  rw [hd, hd2, List.replicate_succ, List.set_cons_zero]
  simp [List.map_append]

private theorem tableRel_set {mv cap cid : Nat} {ptrs : List Val}
    {table : List (Option (List Val))} {PoolUsed : Mem 64 → Prop} {pcur : Val} {clits : List Val}
    (htr : TableRel mv cap ptrs table PoolUsed)
    (hcid : cid < cap) (hpcur : pcur ≠ 0) (hclits : ∀ x ∈ clits, IsValidLit mv x) :
    TableRel mv cap (ptrs.set cid pcur) (table.set cid (some clits))
      (PoolUsed ⋆ ZeroTermInts pcur clits) := by
  obtain ⟨hplen, htlen, hrel⟩ := htr
  refine ⟨by simp [hplen], by simp [htlen], fun i hi => ?_⟩
  by_cases heq : i = cid
  · subst heq
    simp only [List.getElem_set_self]
    exact ⟨hpcur, hclits, PoolUsed, sep_comm _ _⟩
  · have hne : cid ≠ i := Ne.symm heq
    simp only [List.getElem_set_ne hne]
    have hi_orig := hrel i hi
    revert hi_orig
    cases table[i]'(htlen ▸ hi) with
    | none => intro hp; exact hp
    | some lits =>
      rintro ⟨hpne, hv, R_i, hpu_eq⟩
      refine ⟨hpne, hv, R_i ⋆ ZeroTermInts pcur clits, ?_⟩
      rw [hpu_eq, sep_assoc]

private theorem region_pop_int4 {wcur : Val} {rem : Nat} (hrem : 0 < rem) (hfit : 4 * rem ≤ 2 ^ 64)
    {f : Mem 64} (hf : region wcur (4 * rem) f) :
    ∃ v0 : Val, (int4 wcur v0 ⋆ region (wcur + 4) (4 * (rem - 1))) f := by
  have heq : 4 * rem = 4 + 4 * (rem - 1) := by omega
  rw [heq, region_split (by omega)] at hf
  obtain ⟨f1, f2, hu, hd, hf1, hf2⟩ := hf
  obtain ⟨xs, hlen, hia⟩ := region_to_int4Array 1 (by decide) (by simpa using hf1)
  rcases xs with _ | ⟨v0, _ | _⟩ <;> simp at hlen
  simp only [int4Array_cons, int4Array_nil, sep_emp] at hia
  exact ⟨v0, f1, f2, hu, hd, hia, hf2⟩

private theorem lit_store_raw {wcur : Val} {rem : Nat} (v : Val)
    {CNF BM ARR R : Mem 64 → Prop} {m : Mem 64}
    (hrem : 0 < rem) (hfit : 4 * rem ≤ 2 ^ 64)
    (hm : ((CNF ⋆ BM ⋆ ARR ⋆ region wcur (4 * rem)) ⋆ R) m) :
    storeOk m .w wcur ∧
    ((CNF ⋆ BM ⋆ (ARR ⋆ int4 wcur v) ⋆ region (wcur + 4) (4 * (rem - 1))) ⋆ R)
      (storeMem m .w wcur v) := by
  rw [sep5_reg_front] at hm
  obtain ⟨f_w, f_rest, hu, hd, hf_w, hf_rest⟩ := hm
  obtain ⟨v0, hv0_cell⟩ := region_pop_int4 hrem hfit hf_w
  have hm_cell : ((int4 wcur v0 ⋆ region (wcur + 4) (4 * (rem - 1))) ⋆ (CNF ⋆ BM ⋆ ARR ⋆ R)) m :=
    ⟨f_w, f_rest, hu, hd, hv0_cell, hf_rest⟩
  rw [sep_assoc] at hm_cell
  obtain ⟨ok_sw, hm_sw⟩ := store_int4 v hm_cell
  rw [sep6_reg_back] at hm_sw
  exact ⟨ok_sw, hm_sw⟩

theorem lbParseDimacsBody_correct (Γ : Env) :
    ∀ args m Q X, lbParseDimacsBodySpec args m Q X → Func.spec Γ lbParseDimacsBody args m Q X := by
  rintro args m Q X ⟨c, cnf_ptr, cnfBytes, idx0, R, rfl, hcnf, hidx0, hm, hpost⟩
  unfold lbParseDimacsBody Func.spec
  wp_unfold
  obtain ⟨f_ab, f_R, hu_top, hd_top, ⟨f_cnf, f_ws, hu_cw, hd_cw, h_cnf, hws0⟩, h_R⟩ := hm
  obtain ⟨_, htr0, _, hm_ws0⟩ := hws0
  dsimp only at hm_ws0
  have hpbase0 : c.pbase + BitVec.ofNat 64 (4 * 0) = c.pbase := by simp
  rw [hpbase0] at hm_ws0
  let cur0 := cnf_ptr + BitVec.ofNat 64 idx0
  have hm_ws_bm : (BodyMid c cur0 (List.replicate c.cap 0) emp ⋆ region c.pbase (4 * c.poolInts)) f_ws :=
    hm_ws0
  have hm_init : ((Eq (cnfBytes.At cnf_ptr) ⋆
      BodyMid c cur0 (List.replicate c.cap 0) emp ⋆
      region c.pbase (4 * c.poolInts)) ⋆ R) m := by
    have h1 : ((Eq (cnfBytes.At cnf_ptr) ⋆
        (BodyMid c cur0 (List.replicate c.cap 0) emp ⋆ region c.pbase (4 * c.poolInts))) ⋆ R) m :=
      ⟨f_ab, f_R, hu_top, hd_top, ⟨f_cnf, f_ws, hu_cw, hd_cw, h_cnf, hm_ws_bm⟩, h_R⟩
    rwa [← sep_assoc (Eq (cnfBytes.At cnf_ptr))] at h1
  have hm_bm_front : (BodyMid c cur0 (List.replicate c.cap 0) emp ⋆
      (Eq (cnfBytes.At cnf_ptr) ⋆ region c.pbase (4 * c.poolInts) ⋆ R)) m := by
    have h := hm_init; rwa [sep4_2_front] at h
  have hld0 := bodyMid_load_hdr (i := 0) (by decide) hm_bm_front
  simp only [Nat.mul_zero, BitVec.add_zero] at hld0
  have hld1 := bodyMid_load_hdr (i := 1) (by decide) hm_bm_front
  have hld6 := bodyMid_load_hdr (i := 6) (by decide) hm_bm_front
  have hld7 := bodyMid_load_hdr (i := 7) (by decide) hm_bm_front
  have hld8 := bodyMid_load_hdr (i := 8) (by decide) hm_bm_front
  have hld9 := bodyMid_load_hdr (i := 9) (by decide) hm_bm_front
  refine ⟨_, hld0, _, hld1, _, hld6, _, hld7, _, hld8, _, hld9, ?_⟩
  simp only [WorkCfg.hdrWords, List.getElem_cons_succ, List.getElem_cons_zero]
  apply wp_join (fun as m' => as = [] ∧
    parseBodyPure c.mv c.nc c.poolInts [] (cnfBytes.drop idx0) = none ∧
    (Eq (cnfBytes.At cnf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m')
  · rintro _ m' ⟨rfl, hnone, hm'⟩
    wp_unfold
    apply hpost
    rw [hnone]
    exact ⟨rfl, hm'⟩
  intro Jfail hJfail
  have hmv_lt := c.hmv
  have hnc_lt := c.hnc
  have hnc_cap := c.hnc_cap
  obtain ⟨_, hpfit⟩ := workCfg_pbase_toNat c
  apply wp_loop (fun r_cl as_cl m_cl =>
    ∃ (cidNat idx poolUsed poolRem : Nat) (revClauses : List (List Val))
      (ptrs : List Val) (PoolUsed : Mem 64 → Prop),
      1 ≤ cidNat ∧ cidNat ≤ c.nc + 1 ∧ r_cl = c.nc + 1 - cidNat ∧
      revClauses.length = cidNat - 1 ∧
      idx ≤ cnfBytes.length ∧
      poolUsed + poolRem = c.poolInts ∧
      as_cl = [BitVec.ofNat 64 cidNat, cnf_ptr + BitVec.ofNat 64 idx,
               c.pbase + BitVec.ofNat 64 (4 * poolUsed)] ∧
      parseBodyPure c.mv (c.nc + 1 - cidNat) poolRem revClauses (cnfBytes.drop idx) =
        parseBodyPure c.mv c.nc c.poolInts [] (cnfBytes.drop idx0) ∧
      TableRel c.mv c.cap ptrs (initClauseTable c.cap revClauses.reverse) PoolUsed ∧
      (∀ f, PoolUsed f → region c.pbase (4 * poolUsed) f) ∧
      ((Eq (cnfBytes.At cnf_ptr) ⋆
        BodyMid c cur0 ptrs PoolUsed ⋆
        region (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) (4 * poolRem)) ⋆ R) m_cl)
  · rintro Jcl r_cl as_cl m_cl
      ⟨cidNat, idx, poolUsed, poolRem, revClauses, ptrs, PoolUsed,
       hcid1, hcid2, rfl, hrev_len, hidx, hpsum, rfl, hbody_inv, htr, hpu, hm_cl⟩ ih_cl
    wp_unfold
    have hdone_cmp : (BitVec.ofNat 64 c.nc).ult (BitVec.ofNat 64 cidNat) = decide (c.nc < cidNat) := by
      unfold dimacsBound at hnc_lt
      simp only [BitVec.ult, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : c.nc < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : cidNat < 2 ^ 64)]
    rw [hdone_cmp]
    refine ⟨fun hdone => ?_, fun hndone => ?_⟩
    · have hcid_eq : cidNat = c.nc + 1 := by have := of_decide_eq_true hdone; omega
      subst hcid_eq
      simp only [Nat.sub_self] at hbody_inv
      have hm_cnf_cl : (Eq (cnfBytes.At cnf_ptr) ⋆
          (BodyMid c cur0 ptrs PoolUsed ⋆
            region (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) (4 * poolRem) ⋆ R)) m_cl := by
        have h := hm_cl; rwa [sep4_1_front] at h
      refine skipWsCommentsQbe_spec hcnf hidx hm_cnf_cl fun j _ hj hsw => ?_
      wp_unfold
      refine ⟨fun heof => ?_, fun hneof => ?_⟩
      · have hj_eq : j = cnfBytes.length := (cursor_eq_iff (by omega) (by omega)).mp heof
        subst hj_eq
        have his_emp : (skipWsComments (cnfBytes.drop idx)).isEmpty = true := by
          rw [← hsw]; simp
        have hbody_ok : parseBodyPure c.mv c.nc c.poolInts [] (cnfBytes.drop idx0) =
            some (revClauses.reverse, poolRem) := by
          rw [← hbody_inv]; simp [parseBodyPure, his_emp]
        obtain ⟨ok_p64, hm_done⟩ := bodyMid_finish hpsum htr hpu hm_cl
        refine ⟨ok_p64, ?_⟩
        apply hpost
        rw [hbody_ok]
        have hpu_eq : c.poolInts - poolRem = poolUsed := by omega
        refine ⟨rfl, by simp [hrev_len], by omega, ptrs, PoolUsed, ?_⟩
        rwa [hpu_eq]
      · have hj_lt : j < cnfBytes.length := by
          rcases Nat.eq_or_lt_of_le hj with rfl | h
          · exact absurd rfl hneof
          · exact h
        have his_emp : (skipWsComments (cnfBytes.drop idx)).isEmpty = false := by
          rw [← hsw, List.drop_eq_getElem_cons hj_lt]; rfl
        have hbody_none : parseBodyPure c.mv c.nc c.poolInts [] (cnfBytes.drop idx0) = none := by
          rw [← hbody_inv]; simp [parseBodyPure, his_emp]
        refine hJfail [] m_cl ⟨rfl, hbody_none, ?_⟩
        have hm_cl_emp : ((Eq (cnfBytes.At cnf_ptr) ⋆
            (BodyMid c cur0 ptrs PoolUsed ⋆
              int4Array (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) [] ⋆
              region (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + 0))) (4 * poolRem))) ⋆ R) m_cl := by
          simp only [int4Array_nil, sep_emp, Nat.add_zero]
          rwa [sep_assoc (Eq (cnfBytes.At cnf_ptr))] at hm_cl
        exact sep_mono (fun _ => sep_mono_r
          (fun _ hm_ws => collapse_body_state c htr.1 rfl (by omega) hpu hm_ws)) hm_cl_emp
    · have hcid_le : cidNat ≤ c.nc := by have := of_decide_eq_false hndone; omega
      have hrem_cls : c.nc + 1 - cidNat = (c.nc - cidNat) + 1 := by omega
      rw [hrem_cls] at hbody_inv
      let pcur := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
      apply wp_loop (fun r_lit as_lit m_lit =>
        ∃ (lidx rem : Nat) (acc : List Val),
          idx ≤ lidx ∧ lidx ≤ cnfBytes.length ∧ r_lit = cnfBytes.length - lidx ∧
          poolUsed + acc.length + rem = c.poolInts ∧
          acc.length + rem = poolRem ∧
          (∀ x ∈ acc, IsValidLit c.mv x) ∧
          as_lit = [cnf_ptr + BitVec.ofNat 64 lidx,
                    c.pbase + BitVec.ofNat 64 (4 * (poolUsed + acc.length))] ∧
          parseClausePure ((cnfBytes.drop lidx).length + 1) c.mv rem acc (cnfBytes.drop lidx) =
            parseClausePure ((cnfBytes.drop idx).length + 1) c.mv poolRem [] (cnfBytes.drop idx) ∧
          ((Eq (cnfBytes.At cnf_ptr) ⋆
            BodyMid c cur0 ptrs PoolUsed ⋆
            int4Array pcur acc.reverse ⋆
            region (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + acc.length))) (4 * rem)) ⋆ R) m_lit)
      · rintro Jlit r_lit as_lit m_lit
          ⟨lidx, rem, acc, hlidx1, hlidx2, rfl, hlsum, hlrem, hacc_val, rfl, hcl_inv, hm_lit⟩ ih_lit
        have hfail_lit : ∀ m',
            parseClausePure ((cnfBytes.drop lidx).length + 1) c.mv rem acc (cnfBytes.drop lidx) = none →
            ((Eq (cnfBytes.At cnf_ptr) ⋆
              BodyMid c cur0 ptrs PoolUsed ⋆
              int4Array pcur acc.reverse ⋆
              region (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + acc.length))) (4 * rem)) ⋆ R) m' →
            Jfail [] m' := fun m' hcl_none hm' => by
          have hb_none : parseBodyPure c.mv c.nc c.poolInts [] (cnfBytes.drop idx0) = none := by
            rw [← hbody_inv, parseBodyPure, ← hcl_inv, hcl_none]; rfl
          have hm'' : ((Eq (cnfBytes.At cnf_ptr) ⋆
              (BodyMid c cur0 ptrs PoolUsed ⋆
                int4Array pcur acc.reverse ⋆
                region (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + acc.length))) (4 * rem))) ⋆ R) m' := by
            simpa only [sep_assoc] using hm'
          exact hJfail [] m' ⟨rfl, hb_none,
            sep_mono (fun _ => sep_mono_r
              (fun _ hm_ws => collapse_body_state c htr.1 (by simp) hlsum hpu hm_ws)) hm''⟩
        have hm_cnf_lit : (Eq (cnfBytes.At cnf_ptr) ⋆
            (BodyMid c cur0 ptrs PoolUsed ⋆
              int4Array pcur acc.reverse ⋆
              region (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + acc.length))) (4 * rem) ⋆ R)) m_lit := by
          have h := hm_lit; rwa [sep5_1_front] at h
        refine skipWsCommentsQbe_spec hcnf hlidx2 hm_cnf_lit fun idx1 _ hidx1 hsw1 => ?_
        wp_unfold
        refine ⟨fun heof => ?_, fun hneof => ?_⟩
        · have hi1_eq : idx1 = cnfBytes.length := (cursor_eq_iff (by omega) (by omega)).mp heof
          subst hi1_eq
          refine hfail_lit m_lit (parseClausePure_succ_nil (by rw [← hsw1]; simp)) hm_lit
        · have hlt1 : idx1 < cnfBytes.length := by
            rcases Nat.eq_or_lt_of_le hidx1 with rfl | h
            · exact absurd rfl hneof
            · exact h
          have hd1 : cnfBytes.drop idx1 = cnfBytes[idx1] :: cnfBytes.drop (idx1 + 1) :=
            List.drop_eq_getElem_cons hlt1
          have hsw1' : skipWsComments (cnfBytes.drop lidx) = cnfBytes[idx1] :: cnfBytes.drop (idx1 + 1) := by
            rw [← hsw1, hd1]
          refine ⟨fun hfull => ?_, fun hnfull => ?_⟩
          · have hu_eq : poolUsed + acc.length = c.poolInts :=
              (workCfg_wcur_eq_plim_iff c (by omega)).mp hfull
            have hrem0 : rem = 0 := by omega
            refine hfail_lit m_lit ?_ hm_lit
            by_cases hb45 : cnfBytes[idx1] = 45
            · have hsw45 : skipWsComments (cnfBytes.drop lidx) = 45 :: cnfBytes.drop (idx1 + 1) := by
                rwa [hb45] at hsw1'
              rw [parseClausePure_succ_45 hsw45]; simp [hrem0]
            · rw [parseClausePure_succ_pos hsw1' hb45]; simp [hrem0]
          · have hrem_pos : 0 < rem := by
              rcases Nat.eq_zero_or_pos rem with rfl | h
              · exact absurd ((workCfg_wcur_eq_plim_iff c (by omega)).mpr (by omega)) hnfull
              · exact h
            let wcur := c.pbase + BitVec.ofNat 64 (4 * (poolUsed + acc.length))
            refine ⟨_, loadub_At hlt1 (by omega) hm_cnf_lit, fun his_neg => ?_, fun hnis_neg => ?_⟩
            · have hb45 : cnfBytes[idx1] = 45 := (bv64_u8_eq (k := 45)).mp his_neg
              have hsw45 : skipWsComments (cnfBytes.drop lidx) = 45 :: cnfBytes.drop (idx1 + 1) := by
                rwa [hb45] at hsw1'
              rw [ptr_step_1]
              refine readDimacsNat_spec hcnf (by omega) hm_cnf_lit
                (fun hnone => hfail_lit m_lit (by
                  rw [parseClausePure_succ_45 hsw45]; simp [Nat.ne_of_gt hrem_pos, hnone]) hm_lit)
                fun v idx2 rest' hp_v hv_lt _ hidx2 hd2 => ?_
              wp_unfold
              have hv0_iff : BitVec.ofNat 64 v = (0 : Val) ↔ v = 0 := by
                unfold dimacsBound at hv_lt
                simpa using cursor_eq_iff (base := 0) (i := v) (j := 0) (by omega) (by decide)
              refine ⟨fun hvz => ?_, fun hnvz => ?_⟩
              · have hv0 : v = 0 := hv0_iff.mp hvz
                refine hfail_lit m_lit ?_ hm_lit
                rw [parseClausePure_succ_45 hsw45]; simp [Nat.ne_of_gt hrem_pos, hp_v, hv0]
              · have hv_pos : 1 ≤ v := by have := mt hv0_iff.mpr hnvz; omega
                have hmv_cmp : (BitVec.ofNat 64 c.mv).ult (BitVec.ofNat 64 v) = decide (c.mv < v) := by
                  unfold dimacsBound at hmv_lt hv_lt
                  simp only [BitVec.ult, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega : c.mv < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega : v < 2 ^ 64)]
                rw [hmv_cmp]
                refine ⟨fun hvbig => ?_, fun hnvbig => ?_⟩
                · have hmv_v : c.mv < v := of_decide_eq_true hvbig
                  refine hfail_lit m_lit ?_ hm_lit
                  rw [parseClausePure_succ_45 hsw45]; simp [Nat.ne_of_gt hrem_pos, hp_v, hmv_v]
                · have hv_le : v ≤ c.mv := by have := of_decide_eq_false hnvbig; omega
                  let nlit : Val := -BitVec.ofNat 64 v
                  have hnlit_sub : (0 : Val) - BitVec.ofNat 64 v = nlit := BitVec.zero_sub _
                  rw [hnlit_sub]
                  have hnlit_val : IsValidLit c.mv nlit :=
                    isValidLit_neg (isValidLit_ofNat hv_pos hv_le hmv_lt)
                  obtain ⟨ok_sw, hm_sw⟩ := lit_store_raw nlit hrem_pos (by omega) hm_lit
                  have hwcur_eq : wcur = pcur + BitVec.ofNat 64 (4 * acc.reverse.length) := by
                    dsimp [wcur, pcur]; rw [List.length_reverse, ptr_add_ofNat]; congr 2; omega
                  have harr_next : int4Array pcur (nlit :: acc).reverse =
                      (int4Array pcur acc.reverse ⋆ int4 wcur nlit) := by
                    rw [List.reverse_cons, int4Array_append, int4Array_cons, int4Array_nil,
                        sep_emp, ← hwcur_eq]
                  have hwcur2 : wcur + 4 = c.pbase + BitVec.ofNat 64 (4 * (poolUsed + (nlit :: acc).length)) := by
                    change c.pbase + BitVec.ofNat 64 (4 * (poolUsed + acc.length)) + BitVec.ofNat 64 4 =
                      c.pbase + BitVec.ofNat 64 (4 * (poolUsed + (acc.length + 1)))
                    rw [ptr_add_ofNat]
                    exact congrArg (c.pbase + BitVec.ofNat 64 ·) (by omega)
                  refine ⟨ok_sw, ih_lit _ _ _ (by omega) ⟨idx2, rem - 1, nlit :: acc,
                    by omega, hidx2, rfl, by simp; omega, by simp; omega, ?_, ?_, ?_, ?_⟩⟩
                  · intro x hx
                    rcases List.mem_cons.mp hx with rfl | hx
                    · exact hnlit_val
                    · exact hacc_val x hx
                  · rw [hwcur2]
                  · rw [← hcl_inv, parseClausePure_succ_45 hsw45]
                    have h_ne0 : (rem == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
                    have hv_cond : (v == 0 || decide (c.mv < v)) = false := by simp; omega
                    simp only [h_ne0, Bool.false_eq_true, ↓reduceIte, hp_v, hv_cond]
                    rw [← hd2]
                    exact parseClausePure_fuel_irrel
                      (by simp only [List.length_drop]; omega)
                      (by simp only [List.length_drop]; omega)
                  · rwa [← harr_next, hwcur2] at hm_sw
            · have hb_ne45 : cnfBytes[idx1] ≠ 45 := fun h => hnis_neg ((bv64_u8_eq (k := 45)).mpr h)
              refine readDimacsNat_spec hcnf hidx1 hm_cnf_lit
                (fun hnone => hfail_lit m_lit (by
                  rw [parseClausePure_succ_pos hsw1' hb_ne45]
                  simp [Nat.ne_of_gt hrem_pos, ← hd1, hnone]) hm_lit)
                fun v idx2 rest' hp_v hv_lt _ hidx2 hd2 => ?_
              wp_unfold
              have hp_v' : parseNat (cnfBytes[idx1] :: cnfBytes.drop (idx1 + 1)) = some (v, rest') := by
                rwa [← hd1]
              have hv0_iff : BitVec.ofNat 64 v = (0 : Val) ↔ v = 0 := by
                unfold dimacsBound at hv_lt
                simpa using cursor_eq_iff (base := 0) (i := v) (j := 0) (by omega) (by decide)
              refine ⟨fun hvz => ?_, fun hnvz => ?_⟩
              · have hv0 : v = 0 := hv0_iff.mp hvz
                have hcl_ok : parseClausePure ((cnfBytes.drop idx).length + 1) c.mv poolRem []
                    (cnfBytes.drop idx) = some (acc.reverse, rem - 1, cnfBytes.drop idx2) := by
                  rw [← hcl_inv, parseClausePure_succ_pos hsw1' hb_ne45]
                  have h_ne0 : (rem == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
                  simp only [h_ne0, Bool.false_eq_true, ↓reduceIte, hp_v', hv0, beq_self_eq_true, hd2]
                obtain ⟨ok_z, hm_z⟩ := lit_store_raw 0 hrem_pos (by omega) hm_lit
                have hwcur_eq : wcur = pcur + BitVec.ofNat 64 (4 * acc.reverse.length) := by
                  dsimp [wcur, pcur]; rw [List.length_reverse, ptr_add_ofNat]; congr 2; omega
                have hzt : ZeroTermInts pcur acc.reverse =
                    (int4Array pcur acc.reverse ⋆ int4 wcur 0) := by
                  rw [zeroTermInts_eq_append, ← hwcur_eq]
                let poolUsed' := poolUsed + (acc.length + 1)
                have hwcur2 : wcur + 4 = c.pbase + BitVec.ofNat 64 (4 * poolUsed') := by
                  change c.pbase + BitVec.ofNat 64 (4 * (poolUsed + acc.length)) + BitVec.ofNat 64 4 =
                    c.pbase + BitVec.ofNat 64 (4 * (poolUsed + (acc.length + 1)))
                  rw [ptr_add_ofNat]
                  exact congrArg (c.pbase + BitVec.ofNat 64 ·) (by omega)
                rw [← hzt, sep5_zt_bm_front] at hm_z
                have hcid_mod : (BitVec.ofNat 64 cidNat).toNat = cidNat := by
                  unfold dimacsBound at hnc_lt
                  exact Nat.mod_eq_of_lt (by omega)
                rw [hcid_mod]
                have hcid_ptrs : cidNat < ptrs.length := by rw [htr.1]; omega
                obtain ⟨ok_slot, hm_slot⟩ := bodyMid_store_clause hcid_ptrs hm_z
                have hcid_step : BitVec.ofNat 64 cidNat + 1 = BitVec.ofNat 64 (cidNat + 1) :=
                  BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_add])
                refine ⟨ok_z, ok_slot, ?_⟩
                refine ih_cl _ _ _ (by omega)
                  ⟨cidNat + 1, idx2, poolUsed', rem - 1, acc.reverse :: revClauses,
                   ptrs.set cidNat pcur, PoolUsed ⋆ ZeroTermInts pcur acc.reverse,
                   by omega, by omega, rfl, by simp [hrev_len]; omega, hidx2, by omega,
                   by rw [hcid_step, hwcur2], ?_, ?_, ?_, ?_⟩
                · have hsub_eq : c.nc + 1 - (cidNat + 1) = c.nc - cidNat := by omega
                  rw [hsub_eq, ← hbody_inv, parseBodyPure, hcl_ok]; rfl
                · have hrev_app : (acc.reverse :: revClauses).reverse =
                      revClauses.reverse ++ [acc.reverse] := List.reverse_cons
                  have hcid_eq_len : cidNat = revClauses.reverse.length + 1 := by
                    simp [hrev_len]; omega
                  rw [hrev_app, ← initClauseTable_set acc.reverse (by simp [hrev_len]; omega),
                      ← hcid_eq_len]
                  refine tableRel_set htr (by omega) (workCfg_pcur_ne_zero c (by omega)) ?_
                  intro x hx; exact hacc_val x (List.mem_reverse.mp hx)
                · intro f hf
                  obtain ⟨f1, f2, hu_f, hd_f, hf1, hf2⟩ := hf
                  have hr1 := hpu f1 hf1
                  have hr2 : region pcur (4 * (acc.length + 1)) f2 := by
                    have := zeroTermInts_to_region (a := pcur) (xs := acc.reverse)
                      (by simp; omega) hf2
                    simpa using this
                  have hmul_eq : 4 * poolUsed' = 4 * poolUsed + 4 * (acc.length + 1) := by
                    dsimp [poolUsed']; omega
                  rw [hmul_eq, region_split (by omega)]
                  exact ⟨f1, f2, hu_f, hd_f, hr1, hr2⟩
                · rwa [hwcur2, sep5_bm_back] at hm_slot
              · have hv_pos : 1 ≤ v := by have := mt hv0_iff.mpr hnvz; omega
                have hmv_cmp : (BitVec.ofNat 64 c.mv).ult (BitVec.ofNat 64 v) = decide (c.mv < v) := by
                  unfold dimacsBound at hmv_lt hv_lt
                  simp only [BitVec.ult, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega : c.mv < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega : v < 2 ^ 64)]
                rw [hmv_cmp]
                refine ⟨fun hvbig => ?_, fun hnvbig => ?_⟩
                · have hmv_v : c.mv < v := of_decide_eq_true hvbig
                  refine hfail_lit m_lit ?_ hm_lit
                  rw [parseClausePure_succ_pos hsw1' hb_ne45]
                  have h_ne0 : (rem == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
                  have hv_ne0 : (v == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
                  simp only [h_ne0, hv_ne0, Bool.false_eq_true, ↓reduceIte, hp_v', hmv_v]
                · have hv_le : v ≤ c.mv := by have := of_decide_eq_false hnvbig; omega
                  let plit : Val := BitVec.ofNat 64 v
                  have hplit_val : IsValidLit c.mv plit := isValidLit_ofNat hv_pos hv_le hmv_lt
                  obtain ⟨ok_sw, hm_sw⟩ := lit_store_raw plit hrem_pos (by omega) hm_lit
                  have hwcur_eq : wcur = pcur + BitVec.ofNat 64 (4 * acc.reverse.length) := by
                    dsimp [wcur, pcur]; rw [List.length_reverse, ptr_add_ofNat]; congr 2; omega
                  have harr_next : int4Array pcur (plit :: acc).reverse =
                      (int4Array pcur acc.reverse ⋆ int4 wcur plit) := by
                    rw [List.reverse_cons, int4Array_append, int4Array_cons, int4Array_nil,
                        sep_emp, ← hwcur_eq]
                  have hwcur2 : wcur + 4 = c.pbase + BitVec.ofNat 64 (4 * (poolUsed + (plit :: acc).length)) := by
                    change c.pbase + BitVec.ofNat 64 (4 * (poolUsed + acc.length)) + BitVec.ofNat 64 4 =
                      c.pbase + BitVec.ofNat 64 (4 * (poolUsed + (acc.length + 1)))
                    rw [ptr_add_ofNat]
                    exact congrArg (c.pbase + BitVec.ofNat 64 ·) (by omega)
                  refine ⟨ok_sw, ih_lit _ _ _ (by omega) ⟨idx2, rem - 1, plit :: acc,
                    by omega, hidx2, rfl, by simp; omega, by simp; omega, ?_, ?_, ?_, ?_⟩⟩
                  · intro x hx
                    rcases List.mem_cons.mp hx with rfl | hx
                    · exact hplit_val
                    · exact hacc_val x hx
                  · rw [hwcur2]
                  · rw [← hcl_inv, parseClausePure_succ_pos hsw1' hb_ne45]
                    have h_ne0 : (rem == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
                    have hv_ne0 : (v == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
                    simp only [h_ne0, hv_ne0, Bool.false_eq_true, show ¬ c.mv < v by omega, ↓reduceIte, hp_v']
                    rw [← hd2]
                    exact parseClausePure_fuel_irrel
                      (by simp only [List.length_drop]; omega)
                      (by simp only [List.length_drop]; omega)
                  · rwa [← harr_next, hwcur2] at hm_sw
      · intro Jlit hJlit
        wp_unfold
        refine hJlit _ _ _ ⟨idx, poolRem, [], Nat.le_refl _, hidx, rfl,
          by simpa using hpsum, by simp, by simp, by simp, rfl, ?_⟩
        simp only [List.reverse_nil, int4Array_nil, sep_emp, List.length_nil, Nat.add_zero]
        exact hm_cl
  · intro Jcl hJcl
    wp_unfold
    refine hJcl _ _ _ ⟨1, idx0, 0, c.poolInts, [], List.replicate c.cap 0, emp,
      Nat.le_refl _, by omega, rfl, rfl, hidx0, by omega, by simp [cur0], by simp,
      by simpa [initClauseTable_nil (by omega : 1 ≤ c.cap)] using htr0,
      fun f hf => by simpa [region_zero] using hf, ?_⟩
    simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hm_init

/-! ## 5. Pure soundness of `parseBodyPure` -/

private theorem parseClauseAux_succ_45 {fuel mv : Nat} {acc : List (Literal Nat)}
    {bs rest : List UInt8} (h : skipWsComments bs = 45 :: rest) :
    parseClauseAux (fuel + 1) mv acc bs =
      match parseNat rest with
      | some (v, rest') =>
        if 1 ≤ v && v ≤ mv then parseClauseAux fuel mv ((v, false) :: acc) rest' else none
      | none => none := by
  simp only [parseClauseAux, h]
  rcases parseNat rest with _ | ⟨v, rest'⟩ <;> rfl

private theorem parseClauseAux_succ_pos_zero {fuel mv : Nat} {acc : List (Literal Nat)}
    {b : UInt8} {bs rest rest' : List UInt8}
    (h : skipWsComments bs = b :: rest) (hb : b ≠ 45)
    (hp : parseNat (b :: rest) = some (0, rest')) :
    parseClauseAux (fuel + 1) mv acc bs = some (CNF.Clause.ofLiterals acc.reverse, rest') := by
  have := hb
  simp [parseClauseAux, h, hp]

private theorem parseClauseAux_succ_pos_ne0 {fuel mv v : Nat} {acc : List (Literal Nat)}
    {b : UInt8} {bs rest rest' : List UInt8}
    (h : skipWsComments bs = b :: rest) (hb : b ≠ 45) (hv : v ≠ 0)
    (hp : parseNat (b :: rest) = some (v, rest')) :
    parseClauseAux (fuel + 1) mv acc bs =
      if 1 ≤ v && v ≤ mv then parseClauseAux fuel mv ((v, true) :: acc) rest' else none := by
  have := hb
  have := hv
  simp [parseClauseAux, h, hp]

private theorem parseClausePure_sound_aux {fuel mv poolRem : Nat} {acc : List Val} {bs : List UInt8}
    {clits : List Val} {poolRem' : Nat} {rest' : List UInt8}
    (hmv : mv < dimacsBound)
    (hacc : ∀ x ∈ acc, IsValidLit mv x)
    (hp : parseClausePure fuel mv poolRem acc bs = some (clits, poolRem', rest')) :
    parseClauseAux fuel mv (acc.map toLiteral) bs = some (toClause clits, rest') ∧
      (∀ x ∈ clits, IsValidLit mv x) := by
  induction fuel generalizing poolRem acc bs with
  | zero => nomatch hp
  | succ fuel ih =>
    cases hsw : skipWsComments bs with
    | nil => rw [parseClausePure_succ_nil hsw] at hp; nomatch hp
    | cons b rest =>
      by_cases hb45 : b = 45
      · subst hb45
        rw [parseClausePure_succ_45 hsw] at hp
        split at hp
        · nomatch hp
        · cases hpn : parseNat rest with
          | none => rw [hpn] at hp; nomatch hp
          | some vr =>
            obtain ⟨v, rest1⟩ := vr
            rw [hpn] at hp; dsimp at hp
            split at hp
            · nomatch hp
            · rename_i hnv
              simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at hnv
              have hv1 : 1 ≤ v := by omega
              have hvm : v ≤ mv := by omega
              have hval : IsValidLit mv (-BitVec.ofNat 64 v) :=
                isValidLit_neg (isValidLit_ofNat hv1 hvm hmv)
              obtain ⟨haux, hclits⟩ := ih (fun x hx => by
                rcases List.mem_cons.mp hx with rfl | hx
                · exact hval
                · exact hacc x hx) hp
              rw [parseClauseAux_succ_45 hsw, hpn]
              have hcond : (1 ≤ v && v ≤ mv) = true := by simp [hv1, hvm]
              simp only [hcond, ↓reduceIte]
              rw [List.map_cons, toLiteral_neg_ofNat hv1 hvm hmv] at haux
              exact ⟨haux, hclits⟩
      · rw [parseClausePure_succ_pos hsw hb45] at hp
        split at hp
        · nomatch hp
        · cases hpn : parseNat (b :: rest) with
          | none => rw [hpn] at hp; nomatch hp
          | some vr =>
            obtain ⟨v, rest1⟩ := vr
            rw [hpn] at hp; dsimp at hp
            by_cases hv0 : v = 0
            · subst hv0
              simp at hp
              obtain ⟨rfl, _, rfl⟩ := hp
              refine ⟨?_, fun x hx => hacc x (List.mem_reverse.mp hx)⟩
              rw [parseClauseAux_succ_pos_zero hsw hb45 hpn, ← List.map_reverse]; rfl
            · have hv0_f : (v == 0) = false := beq_eq_false_iff_ne.mpr hv0
              simp only [hv0_f, Bool.false_eq_true, ↓reduceIte] at hp
              split at hp
              · nomatch hp
              · rename_i hnv
                have hv1 : 1 ≤ v := by omega
                have hvm : v ≤ mv := by omega
                have hval : IsValidLit mv (BitVec.ofNat 64 v) := isValidLit_ofNat hv1 hvm hmv
                obtain ⟨haux, hclits⟩ := ih (fun x hx => by
                  rcases List.mem_cons.mp hx with rfl | hx
                  · exact hval
                  · exact hacc x hx) hp
                rw [parseClauseAux_succ_pos_ne0 hsw hb45 hv0 hpn]
                have hcond : (1 ≤ v && v ≤ mv) = true := by simp [hv1, hvm]
                simp only [hcond, ↓reduceIte]
                rw [List.map_cons, toLiteral_ofNat hv1 (by omega)] at haux
                exact ⟨haux, hclits⟩

private theorem parseBodyPure_sound_aux {mv k poolRem poolRem' : Nat}
    {revClauses clauses : List (List Val)} {bs : List UInt8}
    (hmv : mv < dimacsBound)
    (hrev : ∀ cl ∈ revClauses, ∀ x ∈ cl, IsValidLit mv x)
    (hbody : parseBodyPure mv k poolRem revClauses bs = some (clauses, poolRem')) :
    (∀ cnf0 : CNF Nat,
      parseClauses mv k (revClauses.reverse.foldl (fun c lits => c.add (toClause lits)) cnf0) bs =
        some (clauses.foldl (fun c lits => c.add (toClause lits)) cnf0)) ∧
    clauses.length = revClauses.length + k ∧
    (∀ cl ∈ clauses, ∀ x ∈ cl, IsValidLit mv x) := by
  induction k generalizing poolRem revClauses bs with
  | zero =>
    simp only [parseBodyPure] at hbody
    cases hsw : (skipWsComments bs).isEmpty
    · rw [hsw] at hbody; nomatch hbody
    · rw [hsw] at hbody; simp at hbody
      obtain ⟨rfl, _⟩ := hbody
      refine ⟨fun cnf0 => by simp [parseClauses, hsw], by simp,
        fun cl hcl => hrev cl (List.mem_reverse.mp hcl)⟩
  | succ k ih =>
    simp only [parseBodyPure] at hbody
    cases hcl : parseClausePure (bs.length + 1) mv poolRem [] bs with
    | none => rw [hcl] at hbody; nomatch hbody
    | some res =>
      obtain ⟨clits, poolRem1, bs'⟩ := res
      rw [hcl] at hbody; dsimp at hbody
      obtain ⟨hcl_aux, hcl_val⟩ := parseClausePure_sound_aux hmv (by simp) hcl
      have hparse_cl : parseClause mv bs = some (toClause clits, bs') := hcl_aux
      obtain ⟨hcnf_eq, hlen, hval_all⟩ := ih (fun cl hmem => by
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact hcl_val
        · exact hrev cl hmem) hbody
      refine ⟨fun cnf0 => ?_, by simp [hlen]; omega, hval_all⟩
      simp only [parseClauses, hparse_cl]
      dsimp
      have hfold : ((clits :: revClauses).reverse.foldl (fun c lits => c.add (toClause lits)) cnf0) =
          (revClauses.reverse.foldl (fun c lits => c.add (toClause lits)) cnf0).add (toClause clits) := by
        rw [List.reverse_cons, List.foldl_append]; rfl
      rw [← hfold]
      exact hcnf_eq cnf0

theorem parseBodyPure_sound {cnfBytes bodyRest : List UInt8} {mv nc poolInts poolRem' : Nat}
    {clauses : List (List Val)}
    (hhdr : parseHeader cnfBytes = some (mv, nc, bodyRest))
    (hmv : mv < dimacsBound)
    (hbody : parseBodyPure mv nc poolInts [] bodyRest = some (clauses, poolRem')) :
    parseDimacs cnfBytes =
      some (clauses.foldl (fun c lits => c.add (toClause lits)) CNF.empty) ∧
    clauses.length = nc ∧
    (∀ cl ∈ clauses, ∀ x ∈ cl, IsValidLit mv x) := by
  obtain ⟨hclauses, hlen, hval⟩ := parseBodyPure_sound_aux hmv (by simp) hbody
  refine ⟨?_, by simpa using hlen, hval⟩
  unfold parseDimacs
  rw [hhdr]; dsimp
  simpa using hclauses CNF.empty

/-! ## 6. DIMACS encoder round-trip (`parseDimacs_encodeDimacs`) -/

def ValidDimacsCnf (cnf : CNF Nat) : Prop :=
  cnfMaxVar cnf < dimacsBound ∧
  cnf.clauses.size < dimacsBound ∧
  ∀ cl ∈ cnf.clauses.toList, ∀ l ∈ cl.literals, 1 ≤ l.1

private theorem natToBytesAux_acc (fuel n : Nat) (acc : List UInt8) :
    natToBytesAux fuel n acc = natToBytesAux fuel n [] ++ acc := by
  induction fuel generalizing n acc with
  | zero => simp [natToBytesAux]
  | succ fuel ih =>
    simp only [natToBytesAux]
    split
    · simp
    · rw [ih (n / 10) (_ :: acc), ih (n / 10) [_], List.append_assoc, List.singleton_append]

private theorem natToBytesAux_fuel_irrel {f1 f2 n : Nat} (acc : List UInt8)
    (h1 : n < f1) (h2 : n < f2) :
    natToBytesAux f1 n acc = natToBytesAux f2 n acc := by
  induction f1 generalizing f2 n acc with
  | zero => omega
  | succ fuel1 ih =>
    cases f2 with
    | zero => omega
    | succ fuel2 =>
      simp only [natToBytesAux]
      split
      · rfl
      · exact ih _ (by omega) (by omega)

private theorem natToBytes_lt_10 {n : Nat} (h : n < 10) :
    natToBytes n = [(48 + n).toUInt8] := by
  unfold natToBytes
  simp [natToBytesAux, h, Nat.mod_eq_of_lt h]

private theorem natToBytes_ge_10 {n : Nat} (h : 10 ≤ n) :
    natToBytes n = natToBytes (n / 10) ++ [(48 + n % 10).toUInt8] := by
  unfold natToBytes
  conv => lhs; rw [natToBytesAux]
  simp only [show ¬ n < 10 by omega, ↓reduceIte]
  rw [natToBytesAux_acc, natToBytesAux_fuel_irrel (f2 := n / 10 + 1) [] (by omega) (by omega)]

private theorem digit_toNat {d : Nat} (hd : d < 10) :
    ((48 + d).toUInt8).toNat = 48 + d := by
  simp [Nat.toUInt8, Nat.mod_eq_of_lt (by omega : 48 + d < 256)]

private theorem isDimacsDigit_digit {d : Nat} (hd : d < 10) :
    isDimacsDigit ((48 + d).toUInt8) = true := by
  unfold isDimacsDigit
  simp only [Bool.and_eq_true, decide_eq_true_eq, u8_le_iff_toNat, digit_toNat hd]
  change 48 ≤ 48 + d ∧ 48 + d ≤ 57
  omega

private theorem isDimacsWs_of_digit {b : UInt8} (hd : isDimacsDigit b = true) :
    isDimacsWs b = false := by
  have ⟨h48, _, _⟩ := digit_bounds hd
  unfold isDimacsWs
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, Bool.and_eq_false_iff,
    decide_eq_false_iff_not, u8_le_iff_toNat]
  refine ⟨fun h => ?_, Or.inr ?_⟩
  · subst h; contradiction
  · change ¬ b.toNat ≤ 13; omega

private theorem isDimacsDigit_of_ws {b : UInt8} (hw : isDimacsWs b = true) :
    isDimacsDigit b = false := by
  cases hd : isDimacsDigit b
  · rfl
  · rw [isDimacsWs_of_digit hd] at hw; nomatch hw

private theorem ne_99_of_digit {b : UInt8} (hd : isDimacsDigit b = true) :
    (b == 99) = false := by
  have ⟨_, h10, _⟩ := digit_bounds hd
  rw [beq_eq_false_iff_ne]
  intro h; subst h
  change (99 : Nat) - 48 < 10 at h10
  omega

private theorem ne_45_of_digit {b : UInt8} (hd : isDimacsDigit b = true) : b ≠ 45 := by
  have ⟨h48, _, _⟩ := digit_bounds hd
  intro h; subst h
  change 48 ≤ 45 at h48
  omega

private theorem natToBytes_digits (n : Nat) :
    natToBytes n ≠ [] ∧ ∀ b ∈ natToBytes n, isDimacsDigit b = true := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < 10
    · rw [natToBytes_lt_10 h]
      refine ⟨by simp, fun b hb => ?_⟩
      rw [List.mem_singleton.mp hb]
      exact isDimacsDigit_digit h
    · rw [natToBytes_ge_10 (by omega)]
      obtain ⟨hne, hdig⟩ := ih (n / 10) (by omega)
      refine ⟨by simp, fun b hb => ?_⟩
      rcases List.mem_append.mp hb with hb | hb
      · exact hdig b hb
      · rw [List.mem_singleton.mp hb]
        exact isDimacsDigit_digit (by omega)

private theorem skipWs_natToBytes_append (n : Nat) (tail : List UInt8) :
    skipWs (natToBytes n ++ tail) = natToBytes n ++ tail := by
  obtain ⟨hne, hdig⟩ := natToBytes_digits n
  cases h : natToBytes n with
  | nil => exact absurd h hne
  | cons b bs =>
    have hb : isDimacsDigit b = true := hdig b (by simp [h])
    simp [skipWs, isDimacsWs_of_digit hb]

private theorem skipWsComments_natToBytes_append (n : Nat) (tail : List UInt8) :
    skipWsComments (natToBytes n ++ tail) = natToBytes n ++ tail := by
  obtain ⟨hne, hdig⟩ := natToBytes_digits n
  cases h : natToBytes n with
  | nil => exact absurd h hne
  | cons b bs =>
    have hb : isDimacsDigit b = true := hdig b (by simp [h])
    simp [skipWsComments, skipWsCommentsAux, isDimacsWs_of_digit hb, ne_99_of_digit hb]

private theorem parseNat_natToBytes_append {n : Nat} (hn : n < dimacsBound) (tail : List UInt8) :
    parseNat (natToBytes n ++ tail) = parseDigitsAux n tail := by
  induction n using Nat.strongRecOn generalizing tail with
  | ind n ih =>
    by_cases h : n < 10
    · rw [natToBytes_lt_10 h, List.singleton_append]
      simp only [parseNat, isDimacsDigit_digit h, ↓reduceIte, digit_toNat h]
      have hsub : 48 + n - 48 = n := by omega
      rw [hsub]
    · rw [natToBytes_ge_10 (by omega), List.append_assoc, List.singleton_append]
      rw [ih (n / 10) (by omega) (by omega)]
      have hd : n % 10 < 10 := by omega
      simp only [parseDigitsAux, isDimacsDigit_digit hd, ↓reduceIte, digit_toNat hd]
      have hacc : n / 10 * 10 + (48 + n % 10 - 48) = n := by omega
      simp only [hacc, hn, ↓reduceIte]

private theorem parseNat_natToBytes_ws {n : Nat} {w : UInt8} {rest : List UInt8}
    (hn : n < dimacsBound) (hw : isDimacsWs w = true) :
    parseNat (natToBytes n ++ w :: rest) = some (n, w :: rest) := by
  rw [parseNat_natToBytes_append hn]
  simp [parseDigitsAux, isDimacsDigit_of_ws hw, hw]

private theorem parseHeader_encodeDimacs {cnf : CNF Nat}
    (hmv : cnfMaxVar cnf < dimacsBound) (hnc : cnf.clauses.size < dimacsBound) :
    parseHeader (encodeDimacs cnf) =
      some (cnfMaxVar cnf, cnf.clauses.size, 10 :: cnf.clauses.toList.flatMap encodeDimacsClause) := by
  unfold encodeDimacs parseHeader
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hsw0 : skipWsComments
      (112 :: 32 :: 99 :: 110 :: 102 :: 32 ::
        (natToBytes (cnfMaxVar cnf) ++ 32 ::
          (natToBytes cnf.clauses.size ++ 10 :: cnf.clauses.toList.flatMap encodeDimacsClause))) =
      112 :: 32 :: 99 :: 110 :: 102 :: 32 ::
        (natToBytes (cnfMaxVar cnf) ++ 32 ::
          (natToBytes cnf.clauses.size ++ 10 :: cnf.clauses.toList.flatMap encodeDimacsClause)) := rfl
  have hws1 : skipWs1
      (32 :: 99 :: 110 :: 102 :: 32 ::
        (natToBytes (cnfMaxVar cnf) ++ 32 ::
          (natToBytes cnf.clauses.size ++ 10 :: cnf.clauses.toList.flatMap encodeDimacsClause))) =
      some (99 :: 110 :: 102 :: 32 ::
        (natToBytes (cnfMaxVar cnf) ++ 32 ::
          (natToBytes cnf.clauses.size ++ 10 :: cnf.clauses.toList.flatMap encodeDimacsClause))) := rfl
  have hws2 : skipWs1
      (32 :: (natToBytes (cnfMaxVar cnf) ++ 32 ::
        (natToBytes cnf.clauses.size ++ 10 :: cnf.clauses.toList.flatMap encodeDimacsClause))) =
      some (natToBytes (cnfMaxVar cnf) ++ 32 ::
        (natToBytes cnf.clauses.size ++ 10 :: cnf.clauses.toList.flatMap encodeDimacsClause)) := by
    simp [skipWs1, show isDimacsWs 32 = true by decide, skipWs_natToBytes_append]
  have hp1 := parseNat_natToBytes_ws (rest := natToBytes cnf.clauses.size ++
      10 :: cnf.clauses.toList.flatMap encodeDimacsClause) hmv (by decide : isDimacsWs 32 = true)
  have hws3 : skipWs1
      (32 :: (natToBytes cnf.clauses.size ++ 10 :: cnf.clauses.toList.flatMap encodeDimacsClause)) =
      some (natToBytes cnf.clauses.size ++ 10 :: cnf.clauses.toList.flatMap encodeDimacsClause) := by
    simp [skipWs1, show isDimacsWs 32 = true by decide, skipWs_natToBytes_append]
  have hp2 := parseNat_natToBytes_ws
      (rest := cnf.clauses.toList.flatMap encodeDimacsClause) hnc (by decide : isDimacsWs 10 = true)
  simp [hsw0, hws1, hws2, hp1, hws3, hp2]

private theorem foldl_lit_max_ge (ls : List (Literal Nat)) (m0 : Nat) :
    m0 ≤ ls.foldl (fun m' l => Nat.max m' l.1) m0 := by
  induction ls generalizing m0 with
  | nil => exact Nat.le_refl _
  | cons l ls ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private theorem mem_le_foldl_lit_max {ls : List (Literal Nat)} {l : Literal Nat} (m0 : Nat)
    (hl : l ∈ ls) : l.1 ≤ ls.foldl (fun m' x => Nat.max m' x.1) m0 := by
  induction ls generalizing m0 with
  | nil => nomatch hl
  | cons x ls ih =>
    rcases List.mem_cons.mp hl with rfl | hl
    · exact Nat.le_trans (Nat.le_max_right m0 l.1) (foldl_lit_max_ge ls _)
    · exact ih _ hl

private theorem foldl_clause_max_ge (cls : List (CNF.Clause Nat)) (m0 : Nat) :
    m0 ≤ cls.foldl (fun m cl => cl.literals.foldl (fun m' l => Nat.max m' l.1) m) m0 := by
  induction cls generalizing m0 with
  | nil => exact Nat.le_refl _
  | cons cl cls ih => exact Nat.le_trans (foldl_lit_max_ge cl.literals m0) (ih _)

private theorem mem_le_cnfMaxVar {cnf : CNF Nat} {cl : CNF.Clause Nat} {l : Literal Nat}
    (hcl : cl ∈ cnf.clauses.toList) (hl : l ∈ cl.literals) :
    l.1 ≤ cnfMaxVar cnf := by
  unfold cnfMaxVar
  rw [← Array.foldl_toList]
  suffices ∀ (cls : List (CNF.Clause Nat)) (m0 : Nat), cl ∈ cls →
      l.1 ≤ cls.foldl (fun m c => c.literals.foldl (fun m' x => Nat.max m' x.1) m) m0 from
    this cnf.clauses.toList 0 hcl
  intro cls
  induction cls with
  | nil => intro _ h; nomatch h
  | cons c cls ih =>
    intro m0 h
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (mem_le_foldl_lit_max m0 hl) (foldl_clause_max_ge cls _)
    · exact ih _ h

private theorem parseClauseAux_fuel_irrel {f1 f2 mv : Nat} {acc : List (Literal Nat)}
    {bs : List UInt8} (h1 : bs.length < f1) (h2 : bs.length < f2) :
    parseClauseAux f1 mv acc bs = parseClauseAux f2 mv acc bs := by
  induction f1 generalizing f2 acc bs with
  | zero => omega
  | succ fuel1 ih =>
    cases f2 with
    | zero => omega
    | succ fuel2 =>
      have hsw_len := skipWsComments_length_le bs
      cases hsw : skipWsComments bs with
      | nil => simp [parseClauseAux, hsw]
      | cons b rest =>
        have hcr_len : (b :: rest).length ≤ bs.length := by rwa [← hsw]
        by_cases hb : b = 45
        · subst hb
          rw [parseClauseAux_succ_45 hsw, parseClauseAux_succ_45 hsw]
          cases hpn : parseNat rest with
          | none => rfl
          | some vr =>
            obtain ⟨v, rest'⟩ := vr
            have hp_len := parseNat_length_lt hpn
            simp only
            split
            · exact ih (by simp at hcr_len; omega) (by simp at hcr_len; omega)
            · rfl
        · cases hpn : parseNat (b :: rest) with
          | none =>
            have _ := hb
            simp [parseClauseAux, hsw, hpn]
          | some vr =>
            obtain ⟨v, rest'⟩ := vr
            by_cases hv0 : v = 0
            · subst hv0
              rw [parseClauseAux_succ_pos_zero hsw hb hpn, parseClauseAux_succ_pos_zero hsw hb hpn]
            · have hp_len := parseNat_length_lt hpn
              rw [parseClauseAux_succ_pos_ne0 hsw hb hv0 hpn,
                  parseClauseAux_succ_pos_ne0 hsw hb hv0 hpn]
              split
              · exact ih (by omega) (by omega)
              · rfl

private theorem parseClauseAux_ws_cons {fuel mv : Nat} {acc : List (Literal Nat)}
    {w : UInt8} {bs : List UInt8} (hw : isDimacsWs w = true) :
    parseClauseAux fuel mv acc (w :: bs) = parseClauseAux fuel mv acc bs := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have hsw : skipWsComments (w :: bs) = skipWsComments bs := by
      simp [skipWsComments, skipWsCommentsAux, hw]
    simp only [parseClauseAux, hsw]

private theorem parseClause_ws_cons {mv : Nat} {w : UInt8} {bs : List UInt8}
    (hw : isDimacsWs w = true) :
    parseClause mv (w :: bs) = parseClause mv bs := by
  unfold parseClause
  rw [parseClauseAux_ws_cons hw]
  exact parseClauseAux_fuel_irrel (by simp; omega) (by omega)

private theorem encodeDimacsLit_length_ge_2 (l : Literal Nat) :
    2 ≤ (encodeDimacsLit l).length := by
  unfold encodeDimacsLit
  obtain ⟨hne, _⟩ := natToBytes_digits l.1
  have hpos : 1 ≤ (natToBytes l.1).length := by
    cases h : natToBytes l.1 with
    | nil => exact absurd h hne
    | cons _ _ => simp
  cases l.2 <;> simp <;> omega

private theorem parseClauseAux_encodeLits {ls : List (Literal Nat)} {fuel mv : Nat}
    {acc : List (Literal Nat)} {rest : List UInt8}
    (hmv : mv < dimacsBound)
    (hls : ∀ l ∈ ls, 1 ≤ l.1 ∧ l.1 ≤ mv)
    (hfuel : (ls.flatMap encodeDimacsLit ++ ([48, 10] ++ rest)).length < fuel) :
    parseClauseAux fuel mv acc (ls.flatMap encodeDimacsLit ++ ([48, 10] ++ rest)) =
      some (CNF.Clause.ofLiterals (acc.reverse ++ ls), 10 :: rest) := by
  induction ls generalizing fuel acc with
  | nil =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [List.flatMap_nil, List.nil_append, List.cons_append, List.append_nil]
      have hsw : skipWsComments (48 :: 10 :: rest) = 48 :: 10 :: rest := rfl
      have hpn : parseNat (48 :: 10 :: rest) = some (0, 10 :: rest) := rfl
      exact parseClauseAux_succ_pos_zero hsw (by decide) hpn
  | cons l ls ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      obtain ⟨v, pol⟩ := l
      obtain ⟨hv1, hvm⟩ := hls (v, pol) (by simp)
      have hv_lt : v < dimacsBound := Nat.lt_of_le_of_lt hvm hmv
      have hls' : ∀ x ∈ ls, 1 ≤ x.1 ∧ x.1 ≤ mv := fun x hx => hls x (by simp [hx])
      let tail := ls.flatMap encodeDimacsLit ++ ([48, 10] ++ rest)
      have hlen_lit := encodeDimacsLit_length_ge_2 (v, pol)
      have hfuel' : tail.length < fuel := by
        have happ : ((v, pol) :: ls).flatMap encodeDimacsLit ++ ([48, 10] ++ rest) =
            encodeDimacsLit (v, pol) ++ tail := by
          simp [tail, List.append_assoc]
        rw [happ, List.length_append] at hfuel
        omega
      simp only [List.flatMap_cons, List.append_assoc]
      change parseClauseAux (fuel + 1) mv acc (encodeDimacsLit (v, pol) ++ tail) = _
      have hcond : (1 ≤ v && v ≤ mv) = true := by simp [hv1, hvm]
      cases pol with
      | false =>
        have hlit : encodeDimacsLit (v, false) ++ tail = 45 :: (natToBytes v ++ 32 :: tail) := by
          simp [encodeDimacsLit]
        rw [hlit]
        have hsw : skipWsComments (45 :: (natToBytes v ++ 32 :: tail)) =
            45 :: (natToBytes v ++ 32 :: tail) := rfl
        have hpn := parseNat_natToBytes_ws (rest := tail) hv_lt (by decide : isDimacsWs 32 = true)
        rw [parseClauseAux_succ_45 hsw, hpn]
        simp only [hcond, ↓reduceIte]
        rw [parseClauseAux_ws_cons (by decide : isDimacsWs 32 = true), ih hls' hfuel']
        simp [List.reverse_cons]
      | true =>
        have hlit : encodeDimacsLit (v, true) ++ tail = natToBytes v ++ 32 :: tail := by
          simp [encodeDimacsLit]
        rw [hlit]
        have hsw := skipWsComments_natToBytes_append v (32 :: tail)
        have hpn := parseNat_natToBytes_ws (rest := tail) hv_lt (by decide : isDimacsWs 32 = true)
        obtain ⟨hne, hdig⟩ := natToBytes_digits v
        cases hnb : natToBytes v with
        | nil => exact absurd hnb hne
        | cons b bs_v =>
          have hb_dig : isDimacsDigit b = true := hdig b (by simp [hnb])
          have hb_ne45 : b ≠ 45 := ne_45_of_digit hb_dig
          rw [hnb, List.cons_append] at hsw hpn
          rw [List.cons_append]
          rw [parseClauseAux_succ_pos_ne0 hsw hb_ne45 (by omega) hpn]
          simp only [hcond, ↓reduceIte]
          rw [parseClauseAux_ws_cons (by decide : isDimacsWs 32 = true), ih hls' hfuel']
          simp [List.reverse_cons]

private theorem parseClause_encodeDimacsClause {mv : Nat} {cl : CNF.Clause Nat} {rest : List UInt8}
    (hmv : mv < dimacsBound)
    (hcl : ∀ l ∈ cl.literals, 1 ≤ l.1 ∧ l.1 ≤ mv) :
    parseClause mv (encodeDimacsClause cl ++ rest) = some (cl, 10 :: rest) := by
  unfold parseClause encodeDimacsClause
  rw [List.append_assoc]
  rw [parseClauseAux_encodeLits hmv hcl (by omega)]
  simp

private theorem parseClauses_encodeDimacsClauses {mv : Nat} {cls : List (CNF.Clause Nat)}
    (accCnf : CNF Nat) (hmv : mv < dimacsBound)
    (hcls : ∀ cl ∈ cls, ∀ l ∈ cl.literals, 1 ≤ l.1 ∧ l.1 ≤ mv) :
    parseClauses mv cls.length accCnf (10 :: cls.flatMap encodeDimacsClause) =
      some (cls.foldl CNF.add accCnf) := by
  induction cls generalizing accCnf with
  | nil =>
    have hsw : skipWsComments [10] = [] := rfl
    simp [parseClauses, hsw]
  | cons cl cls ih =>
    simp only [List.length_cons, List.flatMap_cons, parseClauses]
    rw [parseClause_ws_cons (by decide : isDimacsWs 10 = true),
        parseClause_encodeDimacsClause hmv (fun l hl => hcls cl (by simp) l hl)]
    dsimp
    exact ih (accCnf.add cl) (fun c hc => hcls c (by simp [hc]))

private theorem foldl_add_clauses_toList (cls : List (CNF.Clause Nat)) (init : CNF Nat) :
    (cls.foldl CNF.add init).clauses.toList = init.clauses.toList ++ cls := by
  induction cls generalizing init with
  | nil => simp
  | cons cl cls ih => simp [CNF.add, ih]

theorem parseDimacs_encodeDimacs {cnf : CNF Nat} (h : ValidDimacsCnf cnf) :
    parseDimacs (encodeDimacs cnf) = some cnf := by
  obtain ⟨hmv, hnc, hpos⟩ := h
  unfold parseDimacs
  rw [parseHeader_encodeDimacs hmv hnc]
  dsimp
  have hlen : cnf.clauses.size = cnf.clauses.toList.length := by simp
  rw [hlen, parseClauses_encodeDimacsClauses CNF.empty hmv
    (fun cl hcl l hl => ⟨hpos cl hcl l hl, mem_le_cnfMaxVar hcl hl⟩)]
  congr 1
  rcases cnf with ⟨arr⟩
  rcases hfold : arr.toList.foldl CNF.add CNF.empty with ⟨cs⟩
  have hlist := foldl_add_clauses_toList arr.toList CNF.empty
  rw [hfold] at hlist
  simp [CNF.empty] at hlist
  exact congrArg CNF.mk hlist

end LeanQbe.LratBytes
