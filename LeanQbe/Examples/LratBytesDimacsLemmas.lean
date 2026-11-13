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
open ProofUtil

/-! ## 1. Pure byte-scanner and `parseNat` helper lemmas -/

private theorem isWsByte_val (b : UInt8) :
    (boolVal (BitVec.ofNat 64 b.toNat == 32) |||
      boolVal ((BitVec.ofNat 64 b.toNat - 9).ult 5)) =
    boolVal (isDimacsWs b) := by
  rw [boolVal_or]; congr 1; unfold isDimacsWs
  grind

private theorem u8_sub48_ult10 (b : UInt8) :
    (BitVec.ofNat 64 b.toNat - (48 : Val)).ult (10 : Val) = isDimacsDigit b := by
  unfold isDimacsDigit
  simpa [u8_le_iff_toNat] using u8_sub_ult_eq 48 10 (by decide) (by decide) b

private theorem digit_bounds {b : UInt8} (hd : isDimacsDigit b = true) :
    48 ≤ b.toNat ∧ b.toNat - 48 < 10 ∧
      BitVec.ofNat 64 b.toNat - (48 : Val) = BitVec.ofNat 64 (b.toNat - 48) := by
  unfold isDimacsDigit at hd
  grind

private theorem skipWsCommentsAux_true_cons (c : UInt8) (bs : List UInt8) :
    skipWsCommentsAux true (c :: bs) =
      if c = 10 then skipWsCommentsAux false bs else skipWsCommentsAux true bs := by
  by_cases h : c = 10 <;> simp [skipWsCommentsAux, h]

private theorem skipWsCommentsAux_false_cons (b : UInt8) (bs : List UInt8) :
    skipWsCommentsAux false (b :: bs) =
      if isDimacsWs b then skipWsCommentsAux false bs
      else if b == 99 then skipWsCommentsAux true bs
      else b :: bs := rfl

/-! ## 2. QBE specifications for `isWsByte`, `skipWsCommentsQbe`, `skipWs1Qbe`, `readDimacsNat` -/

theorem isWsByte_spec {Γ : Env} {Q : Post} {X : XPost} {b : UInt8}
    {k : Val → Expr Val Cont} {m : Mem 64}
    (hk : wp Γ Q X (k (boolVal (isDimacsWs b))) [] [] m) :
    wp Γ Q X (isWsByte (BitVec.ofNat 64 b.toNat) k) [] [] m := by
  unfold isWsByte; wp_unfold; rwa [isWsByte_val]

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
  · rintro _ _ ⟨j, hj1, hj2, hdrop, rfl, rfl⟩; wp_unfold; exact hdone j hj1 hj2 hdrop
  intro Jdone hJdone
  apply wp_loop (fun r as m' => ∃ i, i0 ≤ i ∧ i ≤ bs.length ∧ r = bs.length - i ∧
    skipWsCommentsAux false (bs.drop i) = skipWsComments (bs.drop i0) ∧
    as = [base + BitVec.ofNat 64 i] ∧ m' = m)
  · rintro Jswc r as m' ⟨i, hi1, hi2, rfl, hinv, rfl, hm_eq⟩ ih
    subst m'
    wp_unfold
    refine cursor_eof_branch hi2 (by omega)
      (fun heq => by subst heq; exact hJdone _ _ ⟨bs.length, hi1, Nat.le_refl _, by simpa [skipWsCommentsAux] using hinv, rfl, rfl⟩)
      (fun hlt => ?_)
    have hdrop_i : bs.drop i = bs[i] :: bs.drop (i + 1) := List.drop_eq_getElem_cons hlt
    refine ⟨_, loadub_At hlt (by omega) hm, ?_⟩
    rw [ptr_step_1]
    refine isWsByte_spec ?_
    wp_unfold
    refine ⟨fun hws => ih _ _ _ (by omega) ⟨i + 1, by omega, by omega, rfl,
        by rw [hdrop_i, skipWsCommentsAux_false_cons] at hinv; simpa [hws] using hinv, rfl, rfl⟩,
      fun hnws => ⟨fun hisc => ?_, fun hnisc => ?_⟩⟩
    · have hb99 : bs[i] = 99 := (bv64_u8_eq (k := 99)).mp hisc
      have hinv_c : skipWsCommentsAux true (bs.drop (i + 1)) = skipWsComments (bs.drop i0) := by
        rw [hdrop_i, skipWsCommentsAux_false_cons, hb99] at hinv
        simpa [show isDimacsWs 99 = false by decide] using hinv
      apply wp_loop (fun r2 as2 m2 => ∃ k, i + 1 ≤ k ∧ k ≤ bs.length ∧ r2 = bs.length - k ∧
        skipWsCommentsAux true (bs.drop k) = skipWsComments (bs.drop i0) ∧
        as2 = [base + BitVec.ofNat 64 k] ∧ m2 = m)
      · rintro Jskl r2 as2 m2 ⟨k, hk1, hk2, rfl, hinv2, rfl, hm2_eq⟩ ih_skl
        subst m2
        wp_unfold
        refine cursor_eof_branch hk2 (by omega)
          (fun hkeq => by subst hkeq; exact hJdone _ _ ⟨bs.length, by omega, Nat.le_refl _, by simpa [skipWsCommentsAux] using hinv2, rfl, rfl⟩)
          (fun hklt => ?_)
        have hdrop_k : bs.drop k = bs[k] :: bs.drop (k + 1) := List.drop_eq_getElem_cons hklt
        refine ⟨_, loadub_At hklt (by omega) hm, ?_⟩
        rw [ptr_step_1]
        refine ⟨fun hisnl => ?_, fun hnisnl => ?_⟩
        · have hc10 : bs[k] = 10 := (bv64_u8_eq (k := 10)).mp hisnl
          exact ih _ _ _ (by omega) ⟨k + 1, by omega, by omega, rfl,
            by rw [hdrop_k, skipWsCommentsAux_true_cons] at hinv2; simpa [hc10] using hinv2, rfl, rfl⟩
        · have hc10 : bs[k] ≠ 10 := fun h => hnisnl ((bv64_u8_eq (k := 10)).mpr h)
          exact ih_skl _ _ _ (by omega) ⟨k + 1, by omega, by omega, rfl,
            by rw [hdrop_k, skipWsCommentsAux_true_cons] at hinv2; simpa [hc10] using hinv2, rfl, rfl⟩
      · intro Jskl hJskl; wp_unfold
        exact hJskl _ _ _ ⟨i + 1, Nat.le_refl _, by omega, rfl, hinv_c, rfl, rfl⟩
    · have hb99 : (bs[i] == 99) = false := beq_eq_false_iff_ne.mpr (fun h => hnisc ((bv64_u8_eq (k := 99)).mpr h))
      refine hJdone _ _ ⟨i, hi1, hi2, ?_, rfl, rfl⟩
      rw [hdrop_i, skipWsCommentsAux_false_cons, hnws, hb99] at hinv; simpa [← hdrop_i] using hinv
  · intro Jswc hJswc; wp_unfold; exact hJswc _ _ _ ⟨i0, Nat.le_refl _, hi0, rfl, rfl, rfl, rfl⟩

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
  unfold skipWs1Qbe; wp_unfold
  refine cursor_eof_branch hi0 (by omega)
    (fun heq => by subst heq; exact hfail (by simp [skipWs1]))
    (fun hlt0 => ?_)
  have hdrop0 : bs.drop i0 = bs[i0] :: bs.drop (i0 + 1) := List.drop_eq_getElem_cons hlt0
  refine ⟨_, loadub_At hlt0 (by omega) hm, isWsByte_spec ?_⟩
  wp_unfold
  refine ⟨fun hws0 => ?_, fun hnws0 => hfail (by rw [hdrop0]; simp [skipWs1, hnws0])⟩
  have hsw1 : skipWs1 (bs.drop i0) = some (skipWs (bs.drop (i0 + 1))) := by
    rw [hdrop0]; simp [skipWs1, hws0]
  apply wp_join (fun as m' => ∃ j, i0 < j ∧ j ≤ bs.length ∧
    bs.drop j = skipWs (bs.drop (i0 + 1)) ∧ as = [base + BitVec.ofNat 64 j] ∧ m' = m)
  · rintro _ _ ⟨j, hj1, hj2, hdrop, rfl, rfl⟩; wp_unfold; exact hdone j _ hsw1 hj1 hj2 hdrop
  intro Jdone hJdone
  apply wp_loop (fun r as m' => ∃ i, i0 < i ∧ i ≤ bs.length ∧ r = bs.length - i ∧
    skipWs (bs.drop i) = skipWs (bs.drop (i0 + 1)) ∧
    as = [base + BitVec.ofNat 64 i] ∧ m' = m)
  · rintro Jsw r as m' ⟨i, hi1, hi2, rfl, hinv, rfl, hm_eq⟩ ih
    subst m'
    wp_unfold
    refine cursor_eof_branch hi2 (by omega)
      (fun heq => by subst heq; exact hJdone _ _ ⟨bs.length, hi1, Nat.le_refl _, by simpa [skipWs] using hinv, rfl, rfl⟩)
      (fun hlt => ?_)
    have hdrop_i : bs.drop i = bs[i] :: bs.drop (i + 1) := List.drop_eq_getElem_cons hlt
    refine ⟨_, loadub_At hlt (by omega) hm, isWsByte_spec ?_⟩
    wp_unfold
    refine ⟨fun hws => by
        rw [ptr_step_1]
        exact ih _ _ _ (by omega) ⟨i + 1, by omega, by omega, rfl,
          by rw [hdrop_i, skipWs] at hinv; simpa [hws] using hinv, rfl, rfl⟩,
      fun hnws => hJdone _ _ ⟨i, hi1, hi2,
        by rw [hdrop_i, skipWs, hnws] at hinv; simpa [← hdrop_i] using hinv, rfl, rfl⟩⟩
  · intro Jsw hJsw; wp_unfold; rw [ptr_step_1]
    exact hJsw _ _ _ ⟨i0 + 1, by omega, by omega, rfl, rfl, rfl, rfl⟩

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
  unfold readDimacsNat; wp_unfold
  refine cursor_eof_branch hi0 (by omega)
    (fun heq => by subst heq; exact hfail (by simp [parseNat]))
    (fun hlt0 => ?_)
  have hdrop0 : bs.drop i0 = bs[i0] :: bs.drop (i0 + 1) := List.drop_eq_getElem_cons hlt0
  refine ⟨_, loadub_At hlt0 (by omega) hm, ?_⟩
  rw [u8_sub48_ult10]
  refine ⟨fun hd0 => ?_, fun hnd0 => hfail (by rw [hdrop0]; simp [parseNat, hnd0])⟩
  obtain ⟨_, _, hd0_bv⟩ := digit_bounds hd0
  have hp0 : parseNat (bs.drop i0) = parseDigitsAux (bs[i0].toNat - 48) (bs.drop (i0 + 1)) := by
    rw [hdrop0]; simp [parseNat, hd0]
  apply wp_join (fun as m' => ∃ v j rest,
    parseNat (bs.drop i0) = some (v, rest) ∧ v < dimacsBound ∧
    i0 < j ∧ j ≤ bs.length ∧ bs.drop j = rest ∧
    as = [BitVec.ofNat 64 v, base + BitVec.ofNat 64 j] ∧ m' = m)
  · rintro _ _ ⟨v, j, rest, hp, hv, hj1, hj2, hdrop, rfl, rfl⟩; wp_unfold; exact hdone v j rest hp hv hj1 hj2 hdrop
  intro Jdone hJdone
  apply wp_loop (fun r as m' => ∃ i acc,
    i0 < i ∧ i ≤ bs.length ∧ r = bs.length - i ∧ acc < dimacsBound ∧
    parseDigitsAux acc (bs.drop i) = parseNat (bs.drop i0) ∧
    as = [base + BitVec.ofNat 64 i, BitVec.ofNat 64 acc] ∧ m' = m)
  · rintro Jpdig r as m' ⟨i, acc, hi1, hi2, rfl, hacc, hinv, rfl, hm_eq⟩ ih
    subst m'
    wp_unfold
    refine cursor_eof_branch hi2 (by omega)
      (fun heq => by subst heq; exact hJdone _ _ ⟨acc, bs.length, [], by simpa [parseDigitsAux] using hinv.symm, hacc, hi1, Nat.le_refl _, by simp, rfl, rfl⟩)
      (fun hlt => ?_)
    have hdrop_i : bs.drop i = bs[i] :: bs.drop (i + 1) := List.drop_eq_getElem_cons hlt
    refine ⟨_, loadub_At hlt (by omega) hm, ?_⟩
    rw [u8_sub48_ult10]
    refine ⟨fun hd => ?_, fun hnd => isWsByte_spec (by
      wp_unfold
      refine ⟨fun hws => hJdone _ _ ⟨acc, i, bs.drop i, by rw [← hinv, hdrop_i, parseDigitsAux]; simp [hnd, hws], hacc, hi1, hi2, rfl, rfl, rfl⟩,
        fun hnws => hfail (by rw [← hinv, hdrop_i, parseDigitsAux]; simp [hnd, hnws])⟩)⟩
    obtain ⟨_, _, hd_bv⟩ := digit_bounds hd
    rw [hd_bv]
    let acc2 := acc * 10 + (bs[i].toNat - 48)
    have hmul_add : BitVec.ofNat 64 acc * 10 + BitVec.ofNat 64 (bs[i].toNat - 48) = BitVec.ofNat 64 acc2 := by
      unfold dimacsBound at hacc; apply BitVec.eq_of_toNat_eq; simp [acc2, BitVec.toNat_add, BitVec.toNat_mul]
    rw [hmul_add, show (268435456 : Val) = BitVec.ofNat 64 268435456 from rfl]
    unfold dimacsBound at hacc
    refine ult_branch (a := acc2) (b := 268435456) (by omega) (by decide)
      (fun hokb => by
        rw [ptr_step_1]
        have hokb' : acc2 < dimacsBound := hokb
        exact ih _ _ _ (by omega) ⟨i + 1, acc2, by omega, by omega, rfl, hokb',
          by rw [hdrop_i, parseDigitsAux] at hinv; simpa [hd, hokb', acc2] using hinv, rfl, rfl⟩)
      (fun hnokb => hfail (by
        have hnokb' : ¬ acc2 < dimacsBound := hnokb
        rw [← hinv, hdrop_i, parseDigitsAux]; simp [hd, hnokb', acc2]))
  · intro Jpdig hJpdig; wp_unfold; rw [ptr_step_1, hd0_bv]
    exact hJpdig _ _ _ ⟨i0 + 1, bs[i0].toNat - 48, by omega, by omega, rfl,
      by unfold dimacsBound; omega, hp0.symm, rfl, rfl⟩

/-! ## 3. Correctness of `lbParseDimacsHeader` -/

private def parseHeaderAfterCnf (bs3 : List UInt8) : Option (Nat × Nat × List UInt8) := do
  let bs4 ← skipWs1 bs3
  let (mv, bs5) ← parseNat bs4
  let bs6 ← skipWs1 bs5
  let (nc, bs7) ← parseNat bs6
  some (mv, nc, bs7)

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
  unfold lbParseDimacsHeader Func.spec; wp_unfold
  have hm_cnf : (Eq (cnfBytes.At cnf_ptr) ⋆ (region hdr 80 ⋆ R)) m := sep_ac hm
  apply wp_join (fun as m' => as = [] ∧ m' = m ∧ parseHeader cnfBytes = none)
  · rintro _ _ ⟨rfl, rfl, hnone⟩; wp_unfold; apply hpost; rw [hnone]; exact ⟨rfl, hm⟩
  intro Jfail hJfail
  have hfail_of : parseHeader cnfBytes = none → Jfail [] m := fun h => hJfail [] m ⟨rfl, rfl, h⟩
  conv => arg 4; arg 1; rw [show cnf_ptr = cnf_ptr + BitVec.ofNat 64 0 by simp]
  refine skipWsCommentsQbe_spec (i0 := 0) hcnf (Nat.zero_le _) hm_cnf fun i1 _ hi1 hsw1 => ?_
  simp only [List.drop_zero] at hsw1
  wp_unfold
  refine expectByte_branch (k := 112) hcnf hi1 hm_cnf
    (fun hnil => hfail_of (by unfold parseHeader; rw [← hsw1, hnil]))
    (fun hlt1 hp112 => ?_)
    (fun hlt1 hne112 => hfail_of (by
      unfold parseHeader; rw [← hsw1, List.drop_eq_getElem_cons hlt1]
      split
      · simp_all only [List.cons.injEq, ne_eq, false_and]
      · rfl))
  have hd1 := List.drop_eq_getElem_cons hlt1
  have hph1 : parseHeader cnfBytes =
      (skipWs1 (cnfBytes.drop (i1 + 1))).bind (fun
        | 99 :: 110 :: 102 :: bs3 => parseHeaderAfterCnf bs3
        | _ => none) := by
    unfold parseHeader; rw [← hsw1, hd1, hp112]; rfl
  rw [ptr_step_1]
  refine skipWs1Qbe_spec hcnf (by omega) hm_cnf
    (fun hnone => hfail_of (by rw [hph1, hnone]; rfl))
    fun i2 bs2 hbs2 _ hi2 hd2 => ?_
  wp_unfold
  refine expectByte_branch (k := 99) hcnf hi2 hm_cnf
    (fun hnil => hfail_of (by rw [hph1, hbs2, ← hd2, hnil]; rfl))
    (fun hlt2 hc99 => ?_)
    (fun hlt2 hne99 => hfail_of (by
      rw [hph1, hbs2, ← hd2, List.drop_eq_getElem_cons hlt2]
      dsimp only [Option.bind]
      split
      · simp_all only [List.cons.injEq, ne_eq, false_and]
      · rfl))
  have hd2_0 := List.drop_eq_getElem_cons hlt2
  rw [ptr_step_1]
  refine expectByte_branch (k := 110) hcnf (by omega) hm_cnf
    (fun hnil => hfail_of (by rw [hph1, hbs2, ← hd2, hd2_0, hc99, hnil]; rfl))
    (fun hlt2_1 hn110 => ?_)
    (fun hlt2_1 hne110 => hfail_of (by
      rw [hph1, hbs2, ← hd2, hd2_0, hc99, List.drop_eq_getElem_cons hlt2_1]
      dsimp only [Option.bind]
      split
      · simp_all only [List.cons.injEq, ne_eq, false_and, and_false]
      · rfl))
  have hd2_1 := List.drop_eq_getElem_cons hlt2_1
  rw [show (2 : Val) = BitVec.ofNat 64 2 from rfl, ptr_add_ofNat]
  refine expectByte_branch (k := 102) hcnf (by omega) hm_cnf
    (fun hnil => hfail_of (by rw [hph1, hbs2, ← hd2, hd2_0, hc99, hd2_1, hn110, hnil]; rfl))
    (fun hlt2_2 hf102 => ?_)
    (fun hlt2_2 hne102 => hfail_of (by
      rw [hph1, hbs2, ← hd2, hd2_0, hc99, hd2_1, hn110, List.drop_eq_getElem_cons hlt2_2]
      dsimp only [Option.bind]
      split
      · simp_all only [List.cons.injEq, ne_eq, false_and, and_false]
      · rfl))
  have hd2_2 := List.drop_eq_getElem_cons hlt2_2
  have hph2 : parseHeader cnfBytes = parseHeaderAfterCnf (cnfBytes.drop (i2 + 3)) := by
    rw [hph1, hbs2, ← hd2, hd2_0, hc99, hd2_1, hn110, hd2_2, hf102]; rfl
  rw [show (3 : Val) = BitVec.ofNat 64 3 from rfl, ptr_add_ofNat]
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
  have hm_re : (region hdr 80 ⋆ (Eq (cnfBytes.At cnf_ptr) ⋆ R)) m := sep_ac hm
  obtain ⟨f1, f2, hu, hd_m, hf1, hf2⟩ := hm_re
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, hwa⟩ := region80_to_words10 hf1
  have hm0 : (word8Array hdr [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9] ⋆
      (Eq (cnfBytes.At cnf_ptr) ⋆ R)) m := ⟨f1, f2, hu, hd_m, hwa, hf2⟩
  have ⟨ok0, hm1⟩ := storel_word8Array (i := 0) (BitVec.ofNat 64 mv) (by simp) hm0
  simp only [Nat.mul_zero, BitVec.add_zero, List.set_cons_zero] at ok0 hm1
  have ⟨ok1, hm2⟩ := storel_word8Array (i := 1) (BitVec.ofNat 64 nc) (by simp) hm1
  have ⟨ok9, hm3⟩ := storel_word8Array (i := 9) (cnf_ptr + BitVec.ofNat 64 i6) (by simp) hm2
  refine ⟨ok0, ok1, ok9, ?_⟩
  apply hpost; rw [hph_ok]
  have hi6_eq : cnfBytes.length - bs7.length = i6 := by rw [← hd6, List.length_drop]; omega
  refine ⟨rfl, hmv, hnc, by rw [hi6_eq, hd6], by rw [← hd6, List.length_drop]; omega,
    w2, w3, w4, w5, w6, w7, w8, ?_⟩
  rw [hi6_eq]; exact sep_ac hm3

/-! ## 4. Pure clause/body helpers and `lbParseDimacsBody_correct` -/

private theorem skipWsCommentsAux_length_le (inC : Bool) (bs : List UInt8) :
    (skipWsCommentsAux inC bs).length ≤ bs.length := by
  induction bs generalizing inC with
  | nil => cases inC <;> simp [skipWsCommentsAux]
  | cons b bs ih =>
    cases inC
    · rw [skipWsCommentsAux_false_cons]
      grind
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
    grind

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
              grind
        · rw [parseClausePure_succ_pos hsw hb, parseClausePure_succ_pos hsw hb]
          split
          · rfl
          · cases hp : parseNat (b :: rest) with
            | none => rfl
            | some vr =>
              obtain ⟨v, rest'⟩ := vr
              have hr_lt := parseNat_length_lt hp
              grind

theorem toLiteral_ofNat {v : Nat} (_hv1 : 1 ≤ v) (hvb : v < dimacsBound) :
    toLiteral (BitVec.ofNat 64 v) = (v, true) := by
  unfold dimacsBound at hvb
  have hslt : (BitVec.ofNat 64 v).slt 0#64 = false := by
    unfold BitVec.slt BitVec.toInt
    grind
  unfold toLiteral bvAbs
  grind

theorem toLiteral_neg_ofNat {mv v : Nat} (hv1 : 1 ≤ v) (hvm : v ≤ mv) (hmv : mv < dimacsBound) :
    toLiteral (-BitVec.ofNat 64 v) = (v, false) := by
  have hval := isValidLit_ofNat hv1 hvm hmv
  rw [toLiteral_neg hval, toLiteral_ofNat hv1 (by omega)]
  rfl

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
  have hfit := c.fit_active; have hmv := c.hmv; unfold dimacsBound at hmv; unfold WorkCfg.activeBytes at hfit
  let pcur := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
  let wcur := c.pbase + BitVec.ofNat 64 (4 * (poolUsed + accLen))
  have hwcur : wcur = pcur + BitVec.ofNat 64 (4 * accLen) := by
    dsimp [wcur, pcur]; rw [ptr_add_ofNat]; congr 2; omega
  have h4 : ∀ f, (int4Array pcur lits ⋆ region wcur (4 * rem)) f →
      region pcur (4 * (accLen + rem)) f := fun _ hf => by
    rw [← region_merge_eq (a := pcur) (n1 := 4 * accLen) (n2 := 4 * rem) (by omega) (by omega), ← hwcur]
    exact sep_mono (fun _ g => by have := int4Array_to_region (by rw [hll]; omega) g; rwa [hll] at this) hf
  have hm0 : (word8Array c.hdr (c.hdrWords c.pbase cur0) ⋆
      (byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
      (region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
      (region c.tb c.tRaw ⋆ (region c.tlim (c.tBytes - c.tRaw) ⋆
      (word8Array c.cb ptrs ⋆ (PoolUsed ⋆ (int4Array pcur lits ⋆ region wcur (4 * rem))))))))) m := by
    dsimp only [pcur, wcur]; exact sep_ac hm
  have hm1 : (region c.hdr 80 ⋆
      (region c.vb (c.mv + 1) ⋆
      (region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
      (region c.tb c.tRaw ⋆ (region c.tlim (c.tBytes - c.tRaw) ⋆
      (region c.cb (8 * c.cap) ⋆ (region c.pbase (4 * poolUsed) ⋆ region pcur (4 * (accLen + rem))))))))) m :=
    sep_mono2
      (fun _ hf => by have := word8Array_to_region (by simp [WorkCfg.hdrWords]) hf; simpa [WorkCfg.hdrWords] using this)
      (sep_mono2 (fun _ hf => by simpa using byte1Array_to_region (by simp; omega) hf)
      (sep_mono2 (fun _ h => h) (sep_mono2 (fun _ h => h) (sep_mono2 (fun _ h => h)
      (sep_mono2 (fun _ hf => by have := word8Array_to_region (by rw [hplen]; omega) hf; rwa [hplen] at this)
      (sep_mono2 hpu h4)))))) m hm0
  dsimp only [pcur] at hm1
  exact workCfg_regions_to_activeBytes c (poolUsedInts := poolUsed) (poolRemInts := accLen + rem)
    (by omega) (sep_ac hm1)

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
  have hm' : (word8Array c.hdr (c.hdrWords c.pbase cur0) ⋆
      (byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
       region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
       region c.tb c.tRaw ⋆ region c.tlim (c.tBytes - c.tRaw) ⋆
       word8Array c.cb ptrs ⋆ PoolUsed ⋆
       region (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) (4 * poolRem) ⋆
       Eq (cnfBytes.At cnf_ptr) ⋆ R)) m := by
    unfold BodyMid BodyFixed at hm; exact sep_ac hm
  have ⟨ok_p64, hm_done⟩ := storel_word8Array (i := 8) pcur (by simp [WorkCfg.hdrWords]) hm'
  have hset : (c.hdrWords c.pbase cur0).set 8 pcur = c.hdrWords pcur cur0 := rfl
  rw [hset] at hm_done
  have hm_ws : (Eq (cnfBytes.At cnf_ptr) ⋆
      (word8Array c.hdr (c.hdrWords pcur cur0) ⋆
        byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
        region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
        region c.tb c.tRaw ⋆ region c.tlim (c.tBytes - c.tRaw) ⋆
        word8Array c.cb ptrs ⋆ PoolUsed ⋆
        region pcur (4 * poolRem)) ⋆ R)
      (storeMem m .l (c.hdr + 64) pcur) := by
    dsimp only [pcur] at hm_done ⊢; exact sep_ac hm_done
  exact ⟨ok_p64, sep_mono_mid (B' := WorkState c poolUsed poolRem cur0 ptrs table PoolUsed)
    (fun _ hws => ⟨hpsum, htr, hpu, hws⟩) hm_ws⟩

private theorem bodyMid_store_clause {c : WorkCfg} {cur0 pcur : Val} {cidNat : Nat}
    {ptrs clits : List Val} {PoolUsed Rest : Mem 64 → Prop} {m : Mem 64}
    (hcid : cidNat < ptrs.length)
    (hm : ((ZeroTermInts pcur clits ⋆ BodyMid c cur0 ptrs PoolUsed) ⋆ Rest) m) :
    storeOk m .l (c.cb + BitVec.ofNat 64 (8 * cidNat)) ∧
    (BodyMid c cur0 (ptrs.set cidNat pcur) (PoolUsed ⋆ ZeroTermInts pcur clits) ⋆ Rest)
      (storeMem m .l (c.cb + BitVec.ofNat 64 (8 * cidNat)) pcur) := by
  unfold BodyMid at hm ⊢
  have hm' : (word8Array c.cb ptrs ⋆ (ZeroTermInts pcur clits ⋆ BodyFixed c cur0 ⋆ PoolUsed ⋆ Rest)) m :=
    sep_ac hm
  obtain ⟨ok_slot, hm_slot⟩ := storel_word8Array pcur hcid hm'
  exact ⟨ok_slot, sep_ac hm_slot⟩

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
  grind

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

private theorem lit_store_raw {wcur : Val} {rem : Nat} (v : Val)
    {CNF BM ARR R : Mem 64 → Prop} {m : Mem 64}
    (hrem : 0 < rem) (hfit : 4 * rem ≤ 2 ^ 64)
    (hm : ((CNF ⋆ BM ⋆ ARR ⋆ region wcur (4 * rem)) ⋆ R) m) :
    storeOk m .w wcur ∧
    ((CNF ⋆ BM ⋆ (ARR ⋆ int4 wcur v) ⋆ region (wcur + 4) (4 * (rem - 1))) ⋆ R)
      (storeMem m .w wcur v) := by
  obtain ⟨ok_sw, hm_sw⟩ := region_pop_store_int4 v hrem hfit (sep_ac hm : (region wcur (4 * rem) ⋆ (CNF ⋆ BM ⋆ ARR ⋆ R)) m)
  exact ⟨ok_sw, sep_ac hm_sw⟩

private theorem lit_fail_collapse (c : WorkCfg) {cnf_ptr cur0 : Val} {cnfBytes : List UInt8}
    {ptrs lits : List Val} {PoolUsed R : Mem 64 → Prop} {m : Mem 64}
    {poolUsed accLen rem : Nat}
    (hplen : ptrs.length = c.cap) (hll : lits.length = accLen)
    (hpsum : poolUsed + accLen + rem = c.poolInts)
    (hpu : ∀ f, PoolUsed f → region c.pbase (4 * poolUsed) f)
    (hm : ((Eq (cnfBytes.At cnf_ptr) ⋆
      BodyMid c cur0 ptrs PoolUsed ⋆
      int4Array (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) lits ⋆
      region (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + accLen))) (4 * rem)) ⋆ R) m) :
    (Eq (cnfBytes.At cnf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m := by
  have hm_re : (Eq (cnfBytes.At cnf_ptr) ⋆
      (BodyMid c cur0 ptrs PoolUsed ⋆
        int4Array (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) lits ⋆
        region (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + accLen))) (4 * rem)) ⋆ R) m :=
    sep_ac hm
  exact sep_mono_mid (B' := region c.hdr c.activeBytes) (fun _ hm_ws =>
    collapse_body_state c hplen hll hpsum hpu hm_ws) hm_re

private theorem bodyMid_clause_finish {c : WorkCfg} {cnf_ptr cur0 : Val} {cnfBytes : List UInt8}
    {cidNat poolUsed accLen rem : Nat} {ptrs acc : List Val}
    {revClauses : List (List Val)} {PoolUsed R : Mem 64 → Prop} {m : Mem 64}
    (hcid_lt : cidNat < c.cap) (hrev : revClauses.length = cidNat - 1) (hcid1 : 1 ≤ cidNat)
    (hacc_len : acc.length = accLen) (hrem_pos : 0 < rem)
    (hpsum : poolUsed + (accLen + 1) + (rem - 1) = c.poolInts) (hfit : 4 * rem ≤ 2 ^ 64)
    (htr : TableRel c.mv c.cap ptrs (initClauseTable c.cap revClauses.reverse) PoolUsed)
    (hpu : ∀ f, PoolUsed f → region c.pbase (4 * poolUsed) f)
    (hacc_val : ∀ x ∈ acc, IsValidLit c.mv x)
    (hm : ((Eq (cnfBytes.At cnf_ptr) ⋆
      BodyMid c cur0 ptrs PoolUsed ⋆
      int4Array (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) acc.reverse ⋆
      region (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + accLen))) (4 * rem)) ⋆ R) m) :
    let pcur := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
    let wcur := c.pbase + BitVec.ofNat 64 (4 * (poolUsed + accLen))
    let poolUsed' := poolUsed + (accLen + 1)
    storeOk m .w wcur ∧
    storeOk (storeMem m .w wcur 0) .l (c.cb + BitVec.ofNat 64 (8 * cidNat)) ∧
    TableRel c.mv c.cap (ptrs.set cidNat pcur)
      (initClauseTable c.cap (acc.reverse :: revClauses).reverse)
      (PoolUsed ⋆ ZeroTermInts pcur acc.reverse) ∧
    (∀ f, (PoolUsed ⋆ ZeroTermInts pcur acc.reverse) f → region c.pbase (4 * poolUsed') f) ∧
    ((Eq (cnfBytes.At cnf_ptr) ⋆
      BodyMid c cur0 (ptrs.set cidNat pcur) (PoolUsed ⋆ ZeroTermInts pcur acc.reverse) ⋆
      region (c.pbase + BitVec.ofNat 64 (4 * poolUsed')) (4 * (rem - 1))) ⋆ R)
      (storeMem (storeMem m .w wcur 0) .l (c.cb + BitVec.ofNat 64 (8 * cidNat)) pcur) := by
  dsimp only
  subst hacc_len
  obtain ⟨ok_z, hm_z⟩ := lit_store_raw 0 hrem_pos hfit hm
  have hwcur_eq : c.pbase + BitVec.ofNat 64 (4 * (poolUsed + acc.length)) =
      (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) + BitVec.ofNat 64 (4 * acc.reverse.length) := by
    rw [List.length_reverse, ptr_add_ofNat]; congr 2; omega
  have hwcur2 : (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + acc.length))) + 4 =
      c.pbase + BitVec.ofNat 64 (4 * (poolUsed + (acc.length + 1))) := by
    grind
  have hzt : ZeroTermInts (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) acc.reverse =
      (int4Array (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) acc.reverse ⋆
       int4 (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + acc.length))) 0) := by
    rw [zeroTermInts_eq_append, ← hwcur_eq]
  rw [← hzt] at hm_z
  have hm_z' : ((ZeroTermInts (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) acc.reverse ⋆
        BodyMid c cur0 ptrs PoolUsed) ⋆
      (Eq (cnfBytes.At cnf_ptr) ⋆
        region (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + (acc.length + 1)))) (4 * (rem - 1)) ⋆ R))
      (storeMem m .w (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + acc.length))) 0) := by
    rw [← hwcur2]; exact sep_ac hm_z
  obtain ⟨ok_slot, hm_slot⟩ := bodyMid_store_clause (by rw [htr.1]; exact hcid_lt) hm_z'
  refine ⟨ok_z, ok_slot, ?_, ?_, sep_ac hm_slot⟩
  · have hcid_eq_len : cidNat = revClauses.reverse.length + 1 := by simp [hrev]; omega
    rw [List.reverse_cons, ← initClauseTable_set acc.reverse (by simp [hrev]; omega), ← hcid_eq_len]
    exact tableRel_set htr hcid_lt (c.pcur_ne_zero (by omega))
      (fun x hx => hacc_val x (List.mem_reverse.mp hx))
  · intro f ⟨f1, f2, hu_f, hd_f, hf1, hf2⟩
    have hfa := c.fit_active; unfold WorkCfg.activeBytes at hfa
    have h4l : 4 * (acc.length + 1) ≤ 2 ^ 64 := by omega
    rw [show 4 * (poolUsed + (acc.length + 1)) = 4 * poolUsed + 4 * (acc.length + 1) by omega,
      region_split (by omega)]
    exact ⟨f1, f2, hu_f, hd_f, hpu f1 hf1, by simpa using zeroTermInts_to_region (by simp; omega) hf2⟩

private theorem bodyMid_lit_store {c : WorkCfg} {cnf_ptr cur0 : Val} {cnfBytes : List UInt8}
    {poolUsed accLen rem : Nat} {ptrs acc : List Val} {PoolUsed R : Mem 64 → Prop} {m : Mem 64}
    (lit : Val) (hacc_len : acc.length = accLen) (hrem_pos : 0 < rem)
    (hfit : 4 * rem ≤ 2 ^ 64)
    (hm : ((Eq (cnfBytes.At cnf_ptr) ⋆
      BodyMid c cur0 ptrs PoolUsed ⋆
      int4Array (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) acc.reverse ⋆
      region (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + accLen))) (4 * rem)) ⋆ R) m) :
    let wcur := c.pbase + BitVec.ofNat 64 (4 * (poolUsed + accLen))
    storeOk m .w wcur ∧
    ((Eq (cnfBytes.At cnf_ptr) ⋆
      BodyMid c cur0 ptrs PoolUsed ⋆
      int4Array (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) (lit :: acc).reverse ⋆
      region (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + (accLen + 1)))) (4 * (rem - 1))) ⋆ R)
      (storeMem m .w wcur lit) := by
  dsimp only; subst hacc_len
  obtain ⟨ok_sw, hm_sw⟩ := lit_store_raw lit hrem_pos hfit hm
  have hwcur_eq : c.pbase + BitVec.ofNat 64 (4 * (poolUsed + acc.length)) =
      (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) + BitVec.ofNat 64 (4 * acc.reverse.length) := by
    rw [List.length_reverse, ptr_add_ofNat]; congr 2; omega
  have hwcur2 : (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + acc.length))) + 4 =
      c.pbase + BitVec.ofNat 64 (4 * (poolUsed + (acc.length + 1))) := by
    grind
  have harr_next : int4Array (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) (lit :: acc).reverse =
      (int4Array (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) acc.reverse ⋆
       int4 (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + acc.length))) lit) := by
    rw [List.reverse_cons, int4Array_append, int4Array_cons, int4Array_nil, sep_emp, ← hwcur_eq]
  exact ⟨ok_sw, by rwa [← harr_next, hwcur2] at hm_sw⟩

theorem lbParseDimacsBody_correct (Γ : Env) :
    ∀ args m Q X, lbParseDimacsBodySpec args m Q X → Func.spec Γ lbParseDimacsBody args m Q X := by
  rintro args m Q X ⟨c, cnf_ptr, cnfBytes, idx0, R, rfl, hcnf, hidx0, hm, hpost⟩
  unfold lbParseDimacsBody Func.spec; wp_unfold
  obtain ⟨f_ab, f_R, hu_top, hd_top, ⟨f_cnf, f_ws, hu_cw, hd_cw, h_cnf, hws0⟩, h_R⟩ := hm
  obtain ⟨_, htr0, _, hm_ws0⟩ := hws0
  dsimp only at hm_ws0
  simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hm_ws0
  let cur0 := cnf_ptr + BitVec.ofNat 64 idx0
  have hm_init_raw : ((Eq (cnfBytes.At cnf_ptr) ⋆
      (word8Array c.hdr (c.hdrWords c.pbase cur0) ⋆
        byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
        region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
        region c.tb c.tRaw ⋆ region c.tlim (c.tBytes - c.tRaw) ⋆
        word8Array c.cb (List.replicate c.cap 0) ⋆
        emp ⋆ region c.pbase (4 * c.poolInts))) ⋆ R) m :=
    ⟨f_ab, f_R, hu_top, hd_top, ⟨f_cnf, f_ws, hu_cw, hd_cw, h_cnf, hm_ws0⟩, h_R⟩
  have hm_init : ((Eq (cnfBytes.At cnf_ptr) ⋆
      BodyMid c cur0 (List.replicate c.cap 0) emp ⋆
      region c.pbase (4 * c.poolInts)) ⋆ R) m := by
    unfold BodyMid BodyFixed; exact sep_ac hm_init_raw
  have hm_bm_front : (BodyMid c cur0 (List.replicate c.cap 0) emp ⋆
      (Eq (cnfBytes.At cnf_ptr) ⋆ region c.pbase (4 * c.poolInts) ⋆ R)) m := sep_ac hm_init
  have hld0 := bodyMid_load_hdr (i := 0) (by decide) hm_bm_front
  simp only [Nat.mul_zero, BitVec.add_zero] at hld0
  refine ⟨_, hld0, _, bodyMid_load_hdr (i := 1) (by decide) hm_bm_front,
    _, bodyMid_load_hdr (i := 6) (by decide) hm_bm_front,
    _, bodyMid_load_hdr (i := 7) (by decide) hm_bm_front,
    _, bodyMid_load_hdr (i := 8) (by decide) hm_bm_front,
    _, bodyMid_load_hdr (i := 9) (by decide) hm_bm_front, ?_⟩
  simp only [WorkCfg.hdrWords, List.getElem_cons_succ, List.getElem_cons_zero]
  apply wp_join (fun as m' => as = [] ∧
    parseBodyPure c.mv c.nc c.poolInts [] (cnfBytes.drop idx0) = none ∧
    (Eq (cnfBytes.At cnf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m')
  · rintro _ m' ⟨rfl, hnone, hm'⟩; wp_unfold; apply hpost; rw [hnone]; exact ⟨rfl, hm'⟩
  intro Jfail hJfail
  have hmv_lt := c.hmv; have hnc_lt := c.hnc; have hnc_cap := c.hnc_cap
  have hfit_active := c.fit_active
  have := c.toNat_vb; have := c.toNat_tb; have := c.toNat_cb; have := c.toNat_pbase
  unfold WorkCfg.activeBytes at hfit_active
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
    unfold dimacsBound at hnc_lt
    refine ult_branch (by omega) (by omega) (fun hdone => ?_) (fun hndone => ?_)
    · have hcid_eq : cidNat = c.nc + 1 := by omega
      subst hcid_eq; simp only [Nat.sub_self] at hbody_inv
      have hm_cl' : (Eq (cnfBytes.At cnf_ptr) ⋆ (BodyMid c cur0 ptrs PoolUsed ⋆
          region (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) (4 * poolRem) ⋆ R)) m_cl :=
        sep_ac hm_cl
      refine skipWsCommentsQbe_spec hcnf hidx hm_cl' fun j _ hj hsw => ?_
      wp_unfold
      refine cursor_eof_branch hj (by omega) (fun hj_eq => ?_) (fun hj_lt => ?_)
      · subst hj_eq
        have hbody_ok : parseBodyPure c.mv c.nc c.poolInts [] (cnfBytes.drop idx0) =
            some (revClauses.reverse, poolRem) := by
          rw [← hbody_inv]; simp [parseBodyPure, show (skipWsComments (cnfBytes.drop idx)).isEmpty = true by rw [← hsw]; simp]
        obtain ⟨ok_p64, hm_done⟩ := bodyMid_finish hpsum htr hpu hm_cl
        refine ⟨ok_p64, ?_⟩
        apply hpost; rw [hbody_ok]
        exact ⟨rfl, by simp [hrev_len], by omega, ptrs, PoolUsed, by rwa [show c.poolInts - poolRem = poolUsed by omega]⟩
      · have hbody_none : parseBodyPure c.mv c.nc c.poolInts [] (cnfBytes.drop idx0) = none := by
          rw [← hbody_inv]; simp [parseBodyPure, show (skipWsComments (cnfBytes.drop idx)).isEmpty = false by
            rw [← hsw, List.drop_eq_getElem_cons hj_lt]; rfl]
        refine hJfail [] m_cl ⟨rfl, hbody_none, ?_⟩
        have hm_cl_emp : ((Eq (cnfBytes.At cnf_ptr) ⋆
            BodyMid c cur0 ptrs PoolUsed ⋆
            int4Array (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) [] ⋆
            region (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + 0))) (4 * poolRem)) ⋆ R) m_cl := by
          simp only [int4Array_nil, sep_emp, Nat.add_zero]; exact hm_cl
        exact lit_fail_collapse c htr.1 rfl (by omega) hpu hm_cl_emp
    · have hcid_le : cidNat ≤ c.nc := by omega
      rw [show c.nc + 1 - cidNat = (c.nc - cidNat) + 1 by omega] at hbody_inv
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
            Jfail [] m' := fun m' hcl_none hm' =>
          hJfail [] m' ⟨rfl, by rw [← hbody_inv, parseBodyPure, ← hcl_inv, hcl_none]; rfl,
            lit_fail_collapse c htr.1 (by simp) hlsum hpu hm'⟩
        have hm_cnf_lit : (Eq (cnfBytes.At cnf_ptr) ⋆
            (BodyMid c cur0 ptrs PoolUsed ⋆
              int4Array pcur acc.reverse ⋆
              region (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + acc.length))) (4 * rem) ⋆ R)) m_lit :=
          sep_ac hm_lit
        refine skipWsCommentsQbe_spec hcnf hlidx2 hm_cnf_lit fun idx1 _ hidx1 hsw1 => ?_
        wp_unfold
        refine cursor_eof_branch hidx1 (by omega)
          (fun hi1_eq => by subst hi1_eq; exact hfail_lit m_lit (parseClausePure_succ_nil (by rw [← hsw1]; simp)) hm_lit)
          (fun hlt1 => ?_)
        have hd1 := List.drop_eq_getElem_cons hlt1
        have hsw1' : skipWsComments (cnfBytes.drop lidx) = cnfBytes[idx1] :: cnfBytes.drop (idx1 + 1) := by
          rw [← hsw1, hd1]
        have hfull_iff : c.pbase + BitVec.ofNat 64 (4 * (poolUsed + acc.length)) = c.plim ↔ rem = 0 := by
          rw [show poolUsed + acc.length = c.poolInts - rem by omega]
          exact c.pcur_eq_plim_iff (by omega)
        refine ⟨fun hfull => ?_, fun hnfull => ?_⟩
        · have hrem0 := hfull_iff.mp hfull
          refine hfail_lit m_lit ?_ hm_lit
          by_cases hb45 : cnfBytes[idx1] = 45
          · rw [parseClausePure_succ_45 (by rwa [hb45] at hsw1')]; simp [hrem0]
          · rw [parseClausePure_succ_pos hsw1' hb45]; simp [hrem0]
        · have hrem_pos : 0 < rem := Nat.pos_of_ne_zero (fun h0 => hnfull (hfull_iff.mpr h0))
          have hwcur2 : ∀ lit : Val,
              (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + acc.length))) + 4 =
                c.pbase + BitVec.ofNat 64 (4 * (poolUsed + (lit :: acc).length)) := fun lit => by
            grind
          have hstep_lit : ∀ (lit : Val) {idx2 : Nat} (hidx2 : idx2 ≤ cnfBytes.length) (hlidx : lidx < idx2),
              IsValidLit c.mv lit →
              parseClausePure ((cnfBytes.drop idx2).length + 1) c.mv (rem - 1) (lit :: acc) (cnfBytes.drop idx2) =
                parseClausePure ((cnfBytes.drop idx).length + 1) c.mv poolRem [] (cnfBytes.drop idx) →
              storeOk m_lit .w (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + acc.length))) ∧
                Jlit [cnf_ptr + BitVec.ofNat 64 idx2, (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + acc.length))) + 4]
                  (storeMem m_lit .w (c.pbase + BitVec.ofNat 64 (4 * (poolUsed + acc.length))) lit) :=
            fun lit idx2 hidx2 hlidx hlit_val hinv' => by
              obtain ⟨ok_sw, hm_sw⟩ := bodyMid_lit_store lit rfl hrem_pos (by omega) hm_lit
              exact ⟨ok_sw, ih_lit _ _ _ (by omega) ⟨idx2, rem - 1, lit :: acc,
                by omega, hidx2, rfl, by simp; omega, by simp; omega,
                fun x hx => by rcases List.mem_cons.mp hx with rfl | hx; exact hlit_val; exact hacc_val x hx,
                by rw [hwcur2 lit], hinv', hm_sw⟩⟩
          refine ⟨_, loadub_At hlt1 (by omega) hm_cnf_lit, fun his_neg => ?_, fun hnis_neg => ?_⟩
          · have hb45 : cnfBytes[idx1] = 45 := (bv64_u8_eq (k := 45)).mp his_neg
            have hsw45 : skipWsComments (cnfBytes.drop lidx) = 45 :: cnfBytes.drop (idx1 + 1) := by
              rwa [hb45] at hsw1'
            rw [ptr_step_1]
            refine readDimacsNat_spec hcnf (by omega) hm_cnf_lit
              (fun hnone => hfail_lit m_lit (by rw [parseClausePure_succ_45 hsw45]; simp [Nat.ne_of_gt hrem_pos, hnone]) hm_lit)
              fun v idx2 rest' hp_v hv_lt _ hidx2 hd2 => ?_
            wp_unfold; unfold dimacsBound at hv_lt hmv_lt
            refine bv_eq_zero_branch (v := v) (by omega)
              (fun hv0 => hfail_lit m_lit (by rw [parseClausePure_succ_45 hsw45]; simp [Nat.ne_of_gt hrem_pos, hp_v, hv0]) hm_lit)
              (fun hnvz => ?_)
            refine ult_branch (a := c.mv) (b := v) (by omega) (by omega)
              (fun hmv_v => hfail_lit m_lit (by rw [parseClausePure_succ_45 hsw45]; simp [Nat.ne_of_gt hrem_pos, hp_v, hmv_v]) hm_lit)
              (fun hnvbig => ?_)
            rw [show (0 : Val) - BitVec.ofNat 64 v = -BitVec.ofNat 64 v from by simp]
            have hnlit_val : IsValidLit c.mv (-BitVec.ofNat 64 v) :=
              isValidLit_neg (isValidLit_ofNat (mv := c.mv) (v := v) (by omega) (by omega)
                (by unfold dimacsBound; omega))
            have hinv_neg :
                parseClausePure ((cnfBytes.drop idx2).length + 1) c.mv (rem - 1)
                  ((-BitVec.ofNat 64 v) :: acc) (cnfBytes.drop idx2) =
                parseClausePure ((cnfBytes.drop idx).length + 1) c.mv poolRem []
                  (cnfBytes.drop idx) := by
              rw [← hcl_inv, parseClausePure_succ_45 hsw45]
              simp only [beq_eq_false_iff_ne.mpr (by omega : rem ≠ 0),
                beq_eq_false_iff_ne.mpr hnvz, Bool.false_eq_true, Bool.false_or,
                decide_eq_false_iff_not.mpr hnvbig, ↓reduceIte, hp_v, ← hd2]
              exact parseClausePure_fuel_irrel
                (by simp only [List.length_drop]; omega) (by simp only [List.length_drop]; omega)
            exact hstep_lit (-BitVec.ofNat 64 v) hidx2 (by omega) hnlit_val hinv_neg
          · have hb_ne45 : cnfBytes[idx1] ≠ 45 := fun h => hnis_neg ((bv64_u8_eq (k := 45)).mpr h)
            refine readDimacsNat_spec hcnf hidx1 hm_cnf_lit
              (fun hnone => hfail_lit m_lit (by
                rw [parseClausePure_succ_pos hsw1' hb_ne45]; simp [Nat.ne_of_gt hrem_pos, ← hd1, hnone]) hm_lit)
              fun v idx2 rest' hp_v hv_lt _ hidx2 hd2 => ?_
            wp_unfold; unfold dimacsBound at hv_lt hmv_lt
            have hp_v' : parseNat (cnfBytes[idx1] :: cnfBytes.drop (idx1 + 1)) = some (v, rest') := by rwa [← hd1]
            refine bv_eq_zero_branch (v := v) (by omega)
              (fun hv0 => ?_)
              (fun hnvz => ?_)
            · have hcl_ok : parseClausePure ((cnfBytes.drop idx).length + 1) c.mv poolRem []
                  (cnfBytes.drop idx) = some (acc.reverse, rem - 1, cnfBytes.drop idx2) := by
                rw [← hcl_inv, parseClausePure_succ_pos hsw1' hb_ne45]
                grind
              rw [show (BitVec.ofNat 64 cidNat).toNat = cidNat from Nat.mod_eq_of_lt (by omega)]
              obtain ⟨ok_z, ok_slot, htr', hpu', hm_slot⟩ := bodyMid_clause_finish (cidNat := cidNat)
                (by omega) hrev_len hcid1 rfl hrem_pos (by omega) (by omega) htr hpu hacc_val hm_lit
              refine ⟨ok_z, ok_slot, ih_cl _ _ _ (by omega)
                ⟨cidNat + 1, idx2, poolUsed + (acc.length + 1), rem - 1, acc.reverse :: revClauses,
                 ptrs.set cidNat pcur, PoolUsed ⋆ ZeroTermInts pcur acc.reverse,
                 by omega, by omega, rfl, by simp [hrev_len]; omega, hidx2, by omega,
                 by rw [show BitVec.ofNat 64 cidNat + (1 : Val) = BitVec.ofNat 64 (cidNat + 1) from
                      bv_add_ofNat cidNat 1,
                    hwcur2 0, List.length_cons], ?_, htr', hpu', hm_slot⟩⟩
              rw [show c.nc + 1 - (cidNat + 1) = c.nc - cidNat by omega, ← hbody_inv, parseBodyPure, hcl_ok]; rfl
            · refine ult_branch (a := c.mv) (b := v) (by omega) (by omega)
                (fun hmv_v => hfail_lit m_lit (by
                  rw [parseClausePure_succ_pos hsw1' hb_ne45]
                  simp only [beq_eq_false_iff_ne.mpr (by omega : rem ≠ 0),
                    beq_eq_false_iff_ne.mpr hnvz, Bool.false_eq_true, ↓reduceIte, hp_v', hmv_v]) hm_lit)
                (fun hnvbig => ?_)
              have hplit_val : IsValidLit c.mv (BitVec.ofNat 64 v) :=
                isValidLit_ofNat (mv := c.mv) (v := v) (by omega) (by omega)
                  (by unfold dimacsBound; omega)
              have hinv_pos :
                  parseClausePure ((cnfBytes.drop idx2).length + 1) c.mv (rem - 1)
                    (BitVec.ofNat 64 v :: acc) (cnfBytes.drop idx2) =
                  parseClausePure ((cnfBytes.drop idx).length + 1) c.mv poolRem []
                    (cnfBytes.drop idx) := by
                rw [← hcl_inv, parseClausePure_succ_pos hsw1' hb_ne45]
                simp only [beq_eq_false_iff_ne.mpr (by omega : rem ≠ 0),
                  beq_eq_false_iff_ne.mpr hnvz, Bool.false_eq_true,
                  hnvbig, ↓reduceIte, hp_v', ← hd2]
                exact parseClausePure_fuel_irrel
                  (by simp only [List.length_drop]; omega) (by simp only [List.length_drop]; omega)
              exact hstep_lit (BitVec.ofNat 64 v) hidx2 (by omega) hplit_val hinv_pos
      · intro Jlit hJlit; wp_unfold
        refine hJlit _ _ _ ⟨idx, poolRem, [], Nat.le_refl _, hidx, rfl,
          by simpa using hpsum, by simp, by simp, by simp, rfl, ?_⟩
        simp only [List.reverse_nil, int4Array_nil, sep_emp, List.length_nil, Nat.add_zero]; exact hm_cl
  · intro Jcl hJcl; wp_unfold
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
      grind

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
  grind

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
    grind

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
      grind

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
  grind

private theorem isDimacsWs_of_digit {b : UInt8} (hd : isDimacsDigit b = true) :
    isDimacsWs b = false := by
  have ⟨h48, _, _⟩ := digit_bounds hd
  unfold isDimacsWs
  grind

private theorem isDimacsDigit_of_ws {b : UInt8} (hw : isDimacsWs b = true) :
    isDimacsDigit b = false := by
  cases hd : isDimacsDigit b
  · rfl
  · rw [isDimacsWs_of_digit hd] at hw; nomatch hw

private theorem ne_99_of_digit {b : UInt8} (hd : isDimacsDigit b = true) :
    (b == 99) = false := by
  have ⟨_, h10, _⟩ := digit_bounds hd
  grind

private theorem ne_45_of_digit {b : UInt8} (hd : isDimacsDigit b = true) : b ≠ 45 := by
  have ⟨h48, _, _⟩ := digit_bounds hd
  grind

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
      grind
    · rw [natToBytes_ge_10 (by omega), List.append_assoc, List.singleton_append]
      rw [ih (n / 10) (by omega) (by omega)]
      have hd : n % 10 < 10 := by omega
      simp only [parseDigitsAux, isDimacsDigit_digit hd, ↓reduceIte, digit_toNat hd]
      grind

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
            grind
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
              grind

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
    grind
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
        grind
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
    grind

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
