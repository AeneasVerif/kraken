module

public import LeanQbe.T.Examples.LratBytesSpec
public import Kraken.SeparationTactics
import all Kraken.Mem
import all Kraken.Separation

/-!
# DIMACS header/body verification and encoder round-trip in `LeanQbe.T`

Proves:
1. `isWsByte_spec`, `skipWsCommentsQbe_spec`, `skipWs1Qbe_spec`, `readDimacsNat_spec`.
2. `lbParseDimacsHeader_correct` and `lbParseDimacsBody_correct`.
3. `parseBodyPure_sound` (relating `parseBodyPure` to `parseDimacs`).
4. `ValidDimacsCnf` and `parseDimacs_encodeDimacs`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.LratBytes

open Std Std.ExtHashMap Std.Sat
open Std.Tactic.BVDecide.LRAT.Internal
open Kraken.Bedrock2.Test
open LeanQbe.T
open LeanQbe.T.ProofUtil

/-! ## 1. Pure byte-scanner and `parseNat` helper lemmas -/

private theorem isWsByte_val (b : UInt8) :
    ((BitVec.ofNat 64 b.toNat == 32) ||
      (BitVec.ofNat 64 b.toNat - 9).ult 5) =
    isDimacsWs b := by
  unfold isDimacsWs
  rw [show (9 : BitVec 64) = BitVec.ofNat 64 9 from rfl,
      show (5 : BitVec 64) = BitVec.ofNat 64 5 from rfl,
      u8_sub_ult_eq 9 5 (by decide) (by decide) b]
  grind

private theorem u8_sub48_ult10 (b : UInt8) :
    (BitVec.ofNat 64 b.toNat - (48 : BitVec 64)).ult (10 : BitVec 64) = isDimacsDigit b := by
  unfold isDimacsDigit
  simpa [u8_le_iff_toNat] using u8_sub_ult_eq 48 10 (by decide) (by decide) b

private theorem digit_bounds {b : UInt8} (hd : isDimacsDigit b = true) :
    48 ≤ b.toNat ∧ b.toNat - 48 < 10 ∧
      BitVec.ofNat 64 b.toNat - (48 : BitVec 64) = BitVec.ofNat 64 (b.toNat - 48) := by
  unfold isDimacsDigit at hd; grind

private theorem skipWsCommentsAux_true_cons (c : UInt8) (bs : List UInt8) :
    skipWsCommentsAux true (c :: bs) =
      if c = 10 then skipWsCommentsAux false bs else skipWsCommentsAux true bs := by
  by_cases h : c = 10 <;> simp [skipWsCommentsAux, h]

private theorem skipWsCommentsAux_false_cons (b : UInt8) (bs : List UInt8) :
    skipWsCommentsAux false (b :: bs) =
      if isDimacsWs b then skipWsCommentsAux false bs
      else if b == 99 then skipWsCommentsAux true bs
      else b :: bs := rfl

/-! ## 2. `LeanQbe.T` specifications for `isWsByte`, `skipWsCommentsQbe`, `skipWs1Qbe`, `readDimacsNat` -/

theorem isWsByte_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {b : UInt8}
    {k : Bool → Expr Val Cont rs} {m : Mem 64}
    (hk : wp Γ Q X (k (isDimacsWs b)) m) :
    wp Γ Q X (isWsByte (BitVec.ofNat 64 b.toNat) k) m := by
  unfold isWsByte; wp_unfold; rwa [isWsByte_val]

theorem skipWsCommentsQbe_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {base : BitVec 64} {bs : List UInt8} {i0 : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    {done : BitVec 64 → Expr Val Cont rs}
    (hbase : base.toNat + bs.length < 2 ^ 64)
    (hi0 : i0 ≤ bs.length)
    (hm : (Eq (bs.At base) ⋆ R) m)
    (hdone : ∀ j, i0 ≤ j → j ≤ bs.length → bs.drop j = skipWsComments (bs.drop i0) →
      wp Γ Q X (done (base + BitVec.ofNat 64 j)) m) :
    wp Γ Q X (skipWsCommentsQbe (base + BitVec.ofNat 64 i0)
      (base + BitVec.ofNat 64 bs.length) done) m := by
  unfold skipWsCommentsQbe
  refine wp_join_group (fun (res_v, ()) m' => ∃ j, i0 ≤ j ∧ j ≤ bs.length ∧
    bs.drop j = skipWsComments (bs.drop i0) ∧ res_v = base + BitVec.ofNat 64 j ∧ m' = m) ?_ ?_
  · rintro _ ⟨res_v, ⟨⟩⟩ _ ⟨j, hj1, hj2, hdrop, rfl, rfl⟩
    dsimp only [Blocks.get_here]; exact hdone j hj1 hj2 hdrop
  intro Jdone hJdone
  refine wp_loop_group (fun r (p_v, ()) m' => ∃ i, i0 ≤ i ∧ i ≤ bs.length ∧ r = bs.length - i ∧
    skipWsCommentsAux false (bs.drop i) = skipWsComments (bs.drop i0) ∧
    p_v = base + BitVec.ofNat 64 i ∧ m' = m) ?_ ?_
  · rintro Jswc r ⟨p_v, ⟨⟩⟩ m' ih ⟨i, hi1, hi2, rfl, hinv, rfl, hm_eq⟩
    subst m'; dsimp only [Blocks.get_here]; wp_unfold
    refine cursor_loadu8_branch hbase hi2 hm
      (fun heq hnil => by
        subst heq
        exact hJdone _ _ ⟨bs.length, hi1, Nat.le_refl _,
          by simpa [hnil, skipWsCommentsAux] using hinv, rfl, rfl⟩)
      (fun hlt hdrop_i => ?_)
    rw [setWidth64_ofNat8, ptr_step_1]
    refine isWsByte_spec ?_
    wp_unfold
    refine ⟨fun hws => ih _ _ _ (by omega) ⟨i + 1, by omega, by omega, rfl,
        by rw [hdrop_i, skipWsCommentsAux_false_cons] at hinv; simpa [hws] using hinv, rfl, rfl⟩,
      fun hnws => ⟨fun hisc => ?_, fun hnisc => ?_⟩⟩
    · have hb99 : bs[i] = 99 := (bv64_u8_eq (k := 99)).mp hisc
      have hinv_c : skipWsCommentsAux true (bs.drop (i + 1)) = skipWsComments (bs.drop i0) := by
        rw [hdrop_i, skipWsCommentsAux_false_cons, hb99] at hinv
        simpa [show isDimacsWs 99 = false by decide] using hinv
      refine wp_loop_group (fun r2 (q_v, ()) m2 => ∃ k, i + 1 ≤ k ∧ k ≤ bs.length ∧
        r2 = bs.length - k ∧
        skipWsCommentsAux true (bs.drop k) = skipWsComments (bs.drop i0) ∧
        q_v = base + BitVec.ofNat 64 k ∧ m2 = m) ?_ ?_
      · rintro Jskl r2 ⟨q_v, ⟨⟩⟩ m2 ih_skl ⟨k, hk1, hk2, rfl, hinv2, rfl, hm2_eq⟩
        subst m2; dsimp only [Blocks.get_here]; wp_unfold
        refine cursor_loadu8_branch hbase hk2 hm
          (fun hkeq hnil => by
            subst hkeq
            exact hJdone _ _ ⟨bs.length, by omega, Nat.le_refl _,
              by simpa [hnil, skipWsCommentsAux] using hinv2, rfl, rfl⟩)
          (fun hklt hdrop_k => ?_)
        rw [setWidth64_ofNat8, ptr_step_1]
        refine ⟨fun hisnl => ?_, fun hnisnl => ?_⟩
        · have hc10 : bs[k] = 10 := (bv64_u8_eq (k := 10)).mp hisnl
          exact ih _ _ _ (by omega) ⟨k + 1, by omega, by omega, rfl,
            by rw [hdrop_k, skipWsCommentsAux_true_cons] at hinv2; simpa [hc10] using hinv2,
            rfl, rfl⟩
        · have hc10 : bs[k] ≠ 10 := fun h => hnisnl ((bv64_u8_eq (k := 10)).mpr h)
          exact ih_skl _ _ _ (by omega) ⟨k + 1, by omega, by omega, rfl,
            by rw [hdrop_k, skipWsCommentsAux_true_cons] at hinv2; simpa [hc10] using hinv2,
            rfl, rfl⟩
      · intro Jskl hJskl; wp_unfold
        exact hJskl _ _ _ ⟨i + 1, Nat.le_refl _, by omega, rfl, hinv_c, rfl, rfl⟩
    · have hb99 : (bs[i] == 99) = false :=
        beq_eq_false_iff_ne.mpr (fun h => hnisc ((bv64_u8_eq (k := 99)).mpr h))
      refine hJdone _ _ ⟨i, hi1, hi2, ?_, rfl, rfl⟩
      rw [hdrop_i, skipWsCommentsAux_false_cons, hnws, hb99] at hinv; simpa [← hdrop_i] using hinv
  · intro Jswc hJswc; wp_unfold; exact hJswc _ _ _ ⟨i0, Nat.le_refl _, hi0, rfl, rfl, rfl, rfl⟩

theorem skipWs1Qbe_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {fail : Cont []}
    {base : BitVec 64} {bs : List UInt8} {i0 : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    {done : BitVec 64 → Expr Val Cont rs}
    (hbase : base.toNat + bs.length < 2 ^ 64)
    (hi0 : i0 ≤ bs.length)
    (hm : (Eq (bs.At base) ⋆ R) m)
    (hfail : skipWs1 (bs.drop i0) = none → fail () m)
    (hdone : ∀ j rest, skipWs1 (bs.drop i0) = some rest →
      i0 < j → j ≤ bs.length → bs.drop j = rest →
      wp Γ Q X (done (base + BitVec.ofNat 64 j)) m) :
    wp Γ Q X (skipWs1Qbe fail (base + BitVec.ofNat 64 i0)
      (base + BitVec.ofNat 64 bs.length) done) m := by
  unfold skipWs1Qbe; wp_unfold
  refine cursor_loadu8_branch hbase hi0 hm
    (fun _ hnil => hfail (by simp [hnil, skipWs1]))
    (fun hlt0 hdrop0 => ?_)
  rw [setWidth64_ofNat8]
  refine isWsByte_spec ?_
  wp_unfold
  refine ⟨fun hws0 => ?_, fun hnws0 => hfail (by rw [hdrop0]; simp [skipWs1, hnws0])⟩
  have hsw1 : skipWs1 (bs.drop i0) = some (skipWs (bs.drop (i0 + 1))) := by
    rw [hdrop0]; simp [skipWs1, hws0]
  refine wp_join_group (fun (res_v, ()) m' => ∃ j, i0 < j ∧ j ≤ bs.length ∧
    bs.drop j = skipWs (bs.drop (i0 + 1)) ∧ res_v = base + BitVec.ofNat 64 j ∧ m' = m) ?_ ?_
  · rintro _ ⟨res_v, ⟨⟩⟩ _ ⟨j, hj1, hj2, hdrop, rfl, rfl⟩
    dsimp only [Blocks.get_here]; exact hdone j _ hsw1 hj1 hj2 hdrop
  intro Jdone hJdone
  refine wp_loop_group (fun r (p_v, ()) m' => ∃ i, i0 < i ∧ i ≤ bs.length ∧ r = bs.length - i ∧
    skipWs (bs.drop i) = skipWs (bs.drop (i0 + 1)) ∧
    p_v = base + BitVec.ofNat 64 i ∧ m' = m) ?_ ?_
  · rintro Jsw r ⟨p_v, ⟨⟩⟩ m' ih ⟨i, hi1, hi2, rfl, hinv, rfl, hm_eq⟩
    subst m'; dsimp only [Blocks.get_here]; wp_unfold
    refine cursor_loadu8_branch hbase hi2 hm
      (fun heq hnil => by
        subst heq
        exact hJdone _ _ ⟨bs.length, hi1, Nat.le_refl _,
          by simpa [hnil, skipWs] using hinv, rfl, rfl⟩)
      (fun hlt hdrop_i => ?_)
    rw [setWidth64_ofNat8]
    refine isWsByte_spec ?_
    wp_unfold
    refine ⟨fun hws => by
        rw [ptr_step_1]
        exact ih _ _ _ (by omega) ⟨i + 1, by omega, by omega, rfl,
          by rw [hdrop_i, skipWs] at hinv; simpa [hws] using hinv, rfl, rfl⟩,
      fun hnws => hJdone _ _ ⟨i, hi1, hi2,
        by rw [hdrop_i, skipWs, hnws] at hinv; simpa [← hdrop_i] using hinv, rfl, rfl⟩⟩
  · intro Jsw hJsw; wp_unfold; rw [ptr_step_1]
    exact hJsw _ _ _ ⟨i0 + 1, by omega, by omega, rfl, rfl, rfl, rfl⟩

theorem readDimacsNat_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {fail : Cont []}
    {base : BitVec 64} {bs : List UInt8} {i0 : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    {done : BitVec 64 → BitVec 64 → Expr Val Cont rs}
    (hbase : base.toNat + bs.length < 2 ^ 64)
    (hi0 : i0 ≤ bs.length)
    (hm : (Eq (bs.At base) ⋆ R) m)
    (hfail : parseNat (bs.drop i0) = none → fail () m)
    (hdone : ∀ v j rest, parseNat (bs.drop i0) = some (v, rest) →
      v < dimacsBound → i0 < j → j ≤ bs.length → bs.drop j = rest →
      wp Γ Q X (done (BitVec.ofNat 64 v) (base + BitVec.ofNat 64 j)) m) :
    wp Γ Q X (readDimacsNat fail (base + BitVec.ofNat 64 i0)
      (base + BitVec.ofNat 64 bs.length) done) m := by
  unfold readDimacsNat; wp_unfold
  refine cursor_loadu8_branch hbase hi0 hm
    (fun _ hnil => hfail (by simp [hnil, parseNat]))
    (fun hlt0 hdrop0 => ?_)
  rw [setWidth64_ofNat8, u8_sub48_ult10]
  refine ⟨fun hd0 => ?_, fun hnd0 => hfail (by rw [hdrop0]; simp [parseNat, hnd0])⟩
  obtain ⟨_, _, hd0_bv⟩ := digit_bounds hd0
  have hp0 : parseNat (bs.drop i0) = parseDigitsAux (bs[i0].toNat - 48) (bs.drop (i0 + 1)) := by
    rw [hdrop0]; simp [parseNat, hd0]
  refine wp_join_group (fun (val_v, res_v, ()) m' => ∃ v j rest,
    parseNat (bs.drop i0) = some (v, rest) ∧ v < dimacsBound ∧
    i0 < j ∧ j ≤ bs.length ∧ bs.drop j = rest ∧
    val_v = BitVec.ofNat 64 v ∧ res_v = base + BitVec.ofNat 64 j ∧ m' = m) ?_ ?_
  · rintro _ ⟨val_v, res_v, ⟨⟩⟩ _ ⟨v, j, rest, hp, hv, hj1, hj2, hdrop, rfl, rfl, rfl⟩
    dsimp only [Blocks.get_here]; exact hdone v j rest hp hv hj1 hj2 hdrop
  intro Jdone hJdone
  refine wp_loop_group (fun r (p_v, acc_v, ()) m' => ∃ i acc,
    i0 < i ∧ i ≤ bs.length ∧ r = bs.length - i ∧ acc < dimacsBound ∧
    parseDigitsAux acc (bs.drop i) = parseNat (bs.drop i0) ∧
    p_v = base + BitVec.ofNat 64 i ∧ acc_v = BitVec.ofNat 64 acc ∧ m' = m) ?_ ?_
  · rintro Jpdig r ⟨p_v, acc_v, ⟨⟩⟩ m' ih ⟨i, acc, hi1, hi2, rfl, hacc, hinv, rfl, rfl, hm_eq⟩
    subst m'; dsimp only [Blocks.get_here]; wp_unfold
    refine cursor_loadu8_branch hbase hi2 hm
      (fun heq hnil => by
        subst heq
        exact hJdone _ _ ⟨acc, bs.length, [],
          by simpa [hnil, parseDigitsAux] using hinv.symm, hacc, hi1, Nat.le_refl _,
          by simp, rfl, rfl, rfl⟩)
      (fun hlt hdrop_i => ?_)
    rw [setWidth64_ofNat8, u8_sub48_ult10]
    refine ⟨fun hd => ?_, fun hnd => isWsByte_spec (by
      wp_unfold
      refine ⟨fun hws => hJdone _ _ ⟨acc, i, bs.drop i,
          by rw [← hinv, hdrop_i, parseDigitsAux]; simp [hnd, hws],
          hacc, hi1, hi2, rfl, rfl, rfl, rfl⟩,
        fun hnws => hfail (by rw [← hinv, hdrop_i, parseDigitsAux]; simp [hnd, hnws])⟩)⟩
    obtain ⟨_, _, hd_bv⟩ := digit_bounds hd
    rw [hd_bv]
    let acc2 := acc * 10 + (bs[i].toNat - 48)
    have hmul_add : BitVec.ofNat 64 acc * 10 + BitVec.ofNat 64 (bs[i].toNat - 48) =
        BitVec.ofNat 64 acc2 := by
      unfold dimacsBound at hacc; apply BitVec.eq_of_toNat_eq
      simp [acc2, BitVec.toNat_add, BitVec.toNat_mul]
    rw [hmul_add, show (268435456 : BitVec 64) = BitVec.ofNat 64 268435456 from rfl]
    unfold dimacsBound at hacc
    refine ult_branch (a := acc2) (b := 268435456) (by omega) (by decide)
      (fun hokb => by
        rw [ptr_step_1]
        have hokb' : acc2 < dimacsBound := hokb
        exact ih _ _ _ (by omega) ⟨i + 1, acc2, by omega, by omega, rfl, hokb',
          by rw [hdrop_i, parseDigitsAux] at hinv; simpa [hd, hokb', acc2] using hinv,
          rfl, rfl, rfl⟩)
      (fun hnokb => hfail (by
        have hnokb' : ¬ acc2 < dimacsBound := hnokb
        rw [← hinv, hdrop_i, parseDigitsAux]; simp [hd, hnokb', acc2]))
  · intro Jpdig hJpdig; wp_unfold; rw [ptr_step_1, hd0_bv]
    exact hJpdig _ _ _ ⟨i0 + 1, bs[i0].toNat - 48, by omega, by omega, rfl,
      by unfold dimacsBound; omega, hp0.symm, rfl, rfl, rfl⟩

/-! ## 3. Correctness of `lbParseDimacsHeader` -/

private def parseHeaderAfterCnf (bs3 : List UInt8) : Option (Nat × Nat × List UInt8) := do
  let bs4 ← skipWs1 bs3
  let (mv, bs5) ← parseNat bs4
  let bs6 ← skipWs1 bs5
  let (nc, bs7) ← parseNat bs6
  some (mv, nc, bs7)

private theorem region80_to_words10 {hdr : BitVec 64} {f : Mem 64} (hf : region hdr 80 f) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : BitVec 64,
      word8Array hdr [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9] f := by
  obtain ⟨ws, hlen, hwa⟩ := region_to_word8Array 10 (by decide) (by simpa using hf)
  rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ |
    ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | ⟨w8, _ | ⟨w9, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at hlen
  exact ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, hwa⟩

private theorem bind_cnf_none {α : Type} {bs : List UInt8} {f : List UInt8 → Option α}
    (h : bs = [] ∨ (∃ b t, bs = b :: t ∧ b ≠ 99) ∨
      (∃ b t, bs = 99 :: b :: t ∧ b ≠ 110) ∨
      (∃ b t, bs = 99 :: 110 :: b :: t ∧ b ≠ 102)) :
    (some bs).bind (fun | 99 :: 110 :: 102 :: bs3 => f bs3 | _ => none) = none := by
  rcases h with rfl | ⟨b, t, rfl, hne⟩ | ⟨b, t, rfl, hne⟩ | ⟨b, t, rfl, hne⟩
  · rfl
  · dsimp only [Option.bind]; split <;> simp_all
  · dsimp only [Option.bind]; split <;> simp_all
  · dsimp only [Option.bind]; split <;> simp_all

theorem lbParseDimacsHeader_correct (Γ : Env) :
    ∀ args m Q X, lbParseDimacsHeaderSpec args m Q X →
      Func.spec Γ lbParseDimacsHeader args m Q X := by
  rintro _ m Q X ⟨cnf_ptr, hdr, cnfBytes, R, rfl, hcnf, _, hm, hpost⟩
  unfold lbParseDimacsHeader Func.spec Func.wp
  have hm_cnf : (Eq (cnfBytes.At cnf_ptr) ⋆ (region hdr 80 ⋆ R)) m := sep_ac hm
  refine wp_join_group (fun () m' => m' = m ∧ parseHeader cnfBytes = none) ?_ ?_
  · rintro _ ⟨⟩ _ ⟨rfl, hnone⟩
    dsimp only [Blocks.get_here]; wp_unfold; apply hpost; rw [hnone]; exact ⟨rfl, hm⟩
  intro Jfail hJfail
  have hfail_of : parseHeader cnfBytes = none → Jfail () m := fun h => hJfail () m ⟨rfl, h⟩
  dsimp only
  conv => arg 4; arg 1; rw [show cnf_ptr = cnf_ptr + BitVec.ofNat 64 0 by simp]
  refine skipWsCommentsQbe_spec (i0 := 0) hcnf (Nat.zero_le _) hm_cnf fun i1 _ hi1 hsw1 => ?_
  simp only [List.drop_zero] at hsw1
  wp_unfold
  refine expectByte_step 112 hcnf hi1 hm_cnf
    (fun hnil => hfail_of (by unfold parseHeader; rw [← hsw1, hnil]))
    (fun _ _ hd hne => hfail_of (by
      unfold parseHeader; rw [← hsw1, hd]
      split
      · exact absurd (List.cons.inj ‹_›).1 hne
      · rfl))
    (fun hi1' hd1 => ?_)
  have hph1 : parseHeader cnfBytes =
      (skipWs1 (cnfBytes.drop (i1 + 1))).bind (fun
        | 99 :: 110 :: 102 :: bs3 => parseHeaderAfterCnf bs3
        | _ => none) := by
    unfold parseHeader; rw [← hsw1, hd1]; rfl
  rw [ptr_step_1]
  refine skipWs1Qbe_spec hcnf hi1' hm_cnf
    (fun hnone => hfail_of (by rw [hph1, hnone]; rfl))
    fun i2 bs2 hbs2 _ hi2 hd2 => ?_
  wp_unfold
  refine expectByte_step 99 hcnf hi2 hm_cnf
    (fun hnil => hfail_of (by rw [hph1, hbs2, ← hd2, hnil]; rfl))
    (fun b t hd hne => hfail_of (by
      rw [hph1, hbs2, ← hd2, hd]; exact bind_cnf_none (Or.inr (Or.inl ⟨b, t, rfl, hne⟩))))
    (fun hi2_1 hd2_0 => ?_)
  rw [ptr_step_1]
  refine expectByte_step 110 hcnf hi2_1 hm_cnf
    (fun hnil => hfail_of (by rw [hph1, hbs2, ← hd2, hd2_0, hnil]; rfl))
    (fun b t hd hne => hfail_of (by
      rw [hph1, hbs2, ← hd2, hd2_0, hd]
      exact bind_cnf_none (Or.inr (Or.inr (Or.inl ⟨b, t, rfl, hne⟩)))))
    (fun hi2_2 hd2_1 => ?_)
  rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ptr_add_ofNat]
  refine expectByte_step 102 hcnf hi2_2 hm_cnf
    (fun hnil => hfail_of (by rw [hph1, hbs2, ← hd2, hd2_0, hd2_1, hnil]; rfl))
    (fun b t hd hne => hfail_of (by
      rw [hph1, hbs2, ← hd2, hd2_0, hd2_1, hd]
      exact bind_cnf_none (Or.inr (Or.inr (Or.inr ⟨b, t, rfl, hne⟩)))))
    (fun hi2_3 hd2_2 => ?_)
  have hph2 : parseHeader cnfBytes = parseHeaderAfterCnf (cnfBytes.drop (i2 + 3)) := by
    rw [hph1, hbs2, ← hd2, hd2_0, hd2_1, hd2_2]; rfl
  rw [show (3 : BitVec 64) = BitVec.ofNat 64 3 from rfl, ptr_add_ofNat]
  refine skipWs1Qbe_spec hcnf hi2_3 hm_cnf
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
    fun nc i6 bs7 hbs7 hnc _ _ hd6 => ?_
  wp_unfold
  have hph_ok : parseHeader cnfBytes = some (mv, nc, bs7) := by
    rw [hph2]; simp [parseHeaderAfterCnf, hbs4, hbs5, hbs6, hbs7]
  have hm_re : (region hdr 80 ⋆ (Eq (cnfBytes.At cnf_ptr) ⋆ R)) m := sep_ac hm
  obtain ⟨f1, f2, hu, hd_m, hf1, hf2⟩ := hm_re
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, hwa⟩ := region80_to_words10 hf1
  have hm0 : (word8Array hdr [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9] ⋆
      (Eq (cnfBytes.At cnf_ptr) ⋆ R)) m := ⟨f1, f2, hu, hd_m, hwa, hf2⟩
  have ⟨ok0, hm1⟩ := store_word8Array (i := 0) (BitVec.ofNat 64 mv) (by simp) hm0
  simp only [Nat.mul_zero, BitVec.add_zero, List.set_cons_zero] at ok0 hm1
  have ⟨ok1, hm2⟩ := store_word8Array (i := 1) (BitVec.ofNat 64 nc) (by simp) hm1
  have ⟨ok9, hm3⟩ := store_word8Array (i := 9) (cnf_ptr + BitVec.ofNat 64 i6) (by simp) hm2
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
    · rw [skipWsCommentsAux_false_cons]; grind
    · rw [skipWsCommentsAux_true_cons]; split <;> exact Nat.le_trans (ih _) (by simp)

theorem skipWsComments_length_le (bs : List UInt8) :
    (skipWsComments bs).length ≤ bs.length :=
  skipWsCommentsAux_length_le false bs

private theorem parseDigitsAux_length_le {acc : Nat} {bs : List UInt8} {v : Nat} {rest : List UInt8}
    (h : parseDigitsAux acc bs = some (v, rest)) : rest.length ≤ bs.length := by
  induction bs generalizing acc with
  | nil => simp [parseDigitsAux] at h; obtain ⟨_, rfl⟩ := h; exact Nat.le_refl _
  | cons b bs ih => simp only [parseDigitsAux] at h; grind

theorem parseNat_length_lt {bs : List UInt8} {v : Nat} {rest : List UInt8}
    (h : parseNat bs = some (v, rest)) : rest.length < bs.length := by
  cases bs with
  | nil => nomatch h
  | cons b bs =>
    simp only [parseNat] at h
    split at h
    · have := parseDigitsAux_length_le h; simp; omega
    · nomatch h

private theorem parseClausePure_succ_nil {fuel mv poolRem : Nat} {acc : List (BitVec 64)}
    {bs : List UInt8} (h : skipWsComments bs = []) :
    parseClausePure (fuel + 1) mv poolRem acc bs = none := by
  simp [parseClausePure, h]

private theorem parseClausePure_succ_45 {fuel mv poolRem : Nat} {acc : List (BitVec 64)}
    {bs rest : List UInt8} (h : skipWsComments bs = 45 :: rest) :
    parseClausePure (fuel + 1) mv poolRem acc bs =
      if poolRem == 0 then none
      else match parseNat rest with
      | none => none
      | some (v, rest') =>
        if v == 0 || mv < v then none
        else parseClausePure fuel mv (poolRem - 1) (-BitVec.ofNat 64 v :: acc) rest' := by
  simp only [parseClausePure, h]; rcases parseNat rest with _ | ⟨v, rest'⟩ <;> rfl

private theorem parseClausePure_succ_pos {fuel mv poolRem : Nat} {acc : List (BitVec 64)}
    {b : UInt8} {bs rest : List UInt8} (h : skipWsComments bs = b :: rest) (hb : b ≠ 45) :
    parseClausePure (fuel + 1) mv poolRem acc bs =
      if poolRem == 0 then none
      else match parseNat (b :: rest) with
      | none => none
      | some (v, rest') =>
        if v == 0 then some (acc.reverse, poolRem - 1, rest')
        else if mv < v then none
        else parseClausePure fuel mv (poolRem - 1) (BitVec.ofNat 64 v :: acc) rest' := by
  have := hb; simp [parseClausePure, h]
  rcases parseNat (b :: rest) with _ | ⟨v, rest'⟩ <;> simp

theorem parseClausePure_fuel_irrel {f1 f2 mv poolRem : Nat} {acc : List (BitVec 64)}
    {bs : List UInt8} (h1 : bs.length < f1) (h2 : bs.length < f2) :
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
        · subst hb; rw [parseClausePure_succ_45 hsw, parseClausePure_succ_45 hsw]
          split
          · rfl
          · rcases hp : parseNat rest with _ | ⟨v, rest'⟩
            · rfl
            · have := parseNat_length_lt hp; grind
        · rw [parseClausePure_succ_pos hsw hb, parseClausePure_succ_pos hsw hb]
          split
          · rfl
          · rcases hp : parseNat (b :: rest) with _ | ⟨v, rest'⟩
            · rfl
            · have := parseNat_length_lt hp; grind

theorem toLiteral_ofNat {v : Nat} (_hv1 : 1 ≤ v) (hvb : v < dimacsBound) :
    toLiteral (BitVec.ofNat 64 v) = (v, true) := by
  unfold dimacsBound at hvb
  have hslt : (BitVec.ofNat 64 v).slt 0#64 = false := by unfold BitVec.slt BitVec.toInt; grind
  unfold toLiteral bvAbs; grind

theorem toLiteral_neg_ofNat {mv v : Nat} (hv1 : 1 ≤ v) (hvm : v ≤ mv) (hmv : mv < dimacsBound) :
    toLiteral (-BitVec.ofNat 64 v) = (v, false) := by
  rw [toLiteral_neg (isValidLit_ofNat hv1 hvm hmv), toLiteral_ofNat hv1 (by omega)]; rfl

private theorem initClauseTable_nil {cap : Nat} (hcap : 1 ≤ cap) :
    initClauseTable cap [] = List.replicate cap none := by
  unfold initClauseTable; cases cap with | zero => omega | succ k => simp [List.replicate_succ]

private theorem initClauseTable_set {cap : Nat} {clauses : List (List (BitVec 64))}
    (clits : List (BitVec 64)) (h : clauses.length + 1 < cap) :
    (initClauseTable cap clauses).set (clauses.length + 1) (some clits) =
      initClauseTable cap (clauses ++ [clits]) := by
  unfold initClauseTable
  have hpre : (none :: clauses.map some).length = clauses.length + 1 := by simp
  rw [List.cons_append]
  change ((none :: clauses.map some) ++ List.replicate (cap - (clauses.length + 1)) none).set
    (clauses.length + 1) (some clits) = _
  rw [List.set_append_right _ _ (by omega), hpre, Nat.sub_self]
  obtain ⟨d, hd⟩ : ∃ d, cap - (clauses.length + 1) = d + 1 := ⟨cap - (clauses.length + 2), by omega⟩
  grind

private theorem tableRel_set {mv cap cid : Nat} {ptrs : List (BitVec 64)}
    {table : List (Option (List (BitVec 64)))} {PoolUsed : Mem 64 → Prop}
    {pcur : BitVec 64} {clits : List (BitVec 64)}
    (htr : TableRel mv cap ptrs table PoolUsed)
    (hcid : cid < cap) (hpcur : pcur ≠ 0) (hclits : ∀ x ∈ clits, IsValidLit mv x) :
    TableRel mv cap (ptrs.set cid pcur) (table.set cid (some clits))
      (PoolUsed ⋆ ZeroTermInts pcur clits) := by
  obtain ⟨hplen, htlen, hrel⟩ := htr
  refine ⟨by simp [hplen], by simp [htlen], fun i hi => ?_⟩
  by_cases heq : i = cid
  · subst heq; simp only [List.getElem_set_self]
    exact ⟨hpcur, hclits, PoolUsed, sep_comm _ _⟩
  · simp only [List.getElem_set_ne (Ne.symm heq)]
    have hi_orig := hrel i hi; revert hi_orig
    cases table[i]'(htlen ▸ hi) with
    | none => exact id
    | some lits =>
      rintro ⟨hpne, hv, R_i, hpu_eq⟩
      exact ⟨hpne, hv, R_i ⋆ ZeroTermInts pcur clits, by rw [hpu_eq, sep_assoc]⟩

private theorem body_clause_finish {c : WorkCfg} {cnf_ptr cur0 : BitVec 64} {cnfBytes : List UInt8}
    {cidNat poolUsed rem : Nat} {ptrs acc : List (BitVec 64)}
    {revClauses : List (List (BitVec 64))} {PoolUsed R : Mem 64 → Prop} {m : Mem 64}
    (hcid_lt : cidNat < c.cap) (hrev : revClauses.length = cidNat - 1) (hcid1 : 1 ≤ cidNat)
    (hrem_pos : 0 < rem) (hpsum : poolUsed + (acc.length + 1) + (rem - 1) = c.poolInts)
    (htr : TableRel c.mv c.cap ptrs (initClauseTable c.cap revClauses.reverse) PoolUsed)
    (hpu : ∀ f, PoolUsed f → region c.pbase (4 * poolUsed) f)
    (hacc_val : ∀ x ∈ acc, IsValidLit c.mv x)
    (hm : (Eq (cnfBytes.At cnf_ptr) ⋆
      (word8Array c.hdr (c.hdrWords c.pbase cur0) ⋆ wsFixed c ptrs PoolUsed ⋆
        int4Array (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) acc.reverse ⋆
        region (c.pbase + BitVec.ofNat 64 (4 * poolUsed) + BitVec.ofNat 64 (4 * acc.length))
          (4 * rem)) ⋆ R) m) :
    let pcur := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
    let wcur := pcur + BitVec.ofNat 64 (4 * acc.length)
    let poolUsed' := poolUsed + (acc.length + 1)
    storeOk m i32 wcur ∧
    storeOk (storeMem m i32 wcur 0#32) i64 (c.cb + BitVec.ofNat 64 (8 * cidNat)) ∧
    TableRel c.mv c.cap (ptrs.set cidNat pcur)
      (initClauseTable c.cap (acc.reverse :: revClauses).reverse)
      (PoolUsed ⋆ ZeroTermInts pcur acc.reverse) ∧
    (∀ f, (PoolUsed ⋆ ZeroTermInts pcur acc.reverse) f → region c.pbase (4 * poolUsed') f) ∧
    (Eq (cnfBytes.At cnf_ptr) ⋆
      (word8Array c.hdr (c.hdrWords c.pbase cur0) ⋆
        wsFixed c (ptrs.set cidNat pcur) (PoolUsed ⋆ ZeroTermInts pcur acc.reverse) ⋆
        region (c.pbase + BitVec.ofNat 64 (4 * poolUsed')) (4 * (rem - 1))) ⋆ R)
      (storeMem (storeMem m i32 wcur 0#32) i64 (c.cb + BitVec.ofNat 64 (8 * cidNat)) pcur) := by
  intro pcur wcur poolUsed'
  obtain ⟨ok_z, hpu', hm_z⟩ := wsFixed_finish_clause hrem_pos hpsum hpu hm
  unfold wsFixed at hm_z
  have hm_cb : (word8Array c.cb ptrs ⋆
      (word8Array c.hdr (c.hdrWords c.pbase cur0) ⋆
        byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
        region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
        region c.tb c.tRaw ⋆ region c.tlim (c.tBytes - c.tRaw) ⋆
        (PoolUsed ⋆ ZeroTermInts pcur acc.reverse) ⋆
        region (c.pbase + BitVec.ofNat 64 (4 * poolUsed')) (4 * (rem - 1)) ⋆
        Eq (cnfBytes.At cnf_ptr) ⋆ R)) (storeMem m i32 wcur 0#32) :=
    sep_cast hm_z (by dsimp only [pcur, poolUsed']; ac_rfl)
  obtain ⟨ok_slot, hm_slot⟩ := store_word8Array pcur (by rw [htr.1]; exact hcid_lt) hm_cb
  refine ⟨ok_z, ok_slot, ?_, hpu', ?_⟩
  · have hcid_eq_len : cidNat = revClauses.reverse.length + 1 := by simp [hrev]; omega
    rw [List.reverse_cons, ← initClauseTable_set acc.reverse (by simp [hrev]; omega), ← hcid_eq_len]
    have hfa := c.fit_active; unfold WorkCfg.activeBytes at hfa
    exact tableRel_set htr hcid_lt (c.pcur_ne_zero (by omega))
      (fun x hx => hacc_val x (List.mem_reverse.mp hx))
  · unfold wsFixed
    exact sep_cast hm_slot (by dsimp only [pcur, poolUsed']; ac_rfl)

theorem lbParseDimacsBody_correct (Γ : Env) :
    ∀ args m Q X, lbParseDimacsBodySpec args m Q X → Func.spec Γ lbParseDimacsBody args m Q X := by
  rintro _ m Q X ⟨c, cnf_ptr, cnfBytes, idx0, R, rfl, hcnf, hidx0, hm, hpost⟩
  unfold lbParseDimacsBody Func.spec Func.wp; wp_unfold
  obtain ⟨_, htr0, _, hm_u⟩ := workState_sep.mp (sep_ac hm :
    (WorkState c 0 c.poolInts (cnf_ptr + BitVec.ofNat 64 idx0)
      (List.replicate c.cap 0) (List.replicate c.cap none) emp ⋆
      (Eq (cnfBytes.At cnf_ptr) ⋆ R)) m)
  simp only [Nat.mul_zero, BitVec.add_zero] at hm_u
  let cur0 := cnf_ptr + BitVec.ofNat 64 idx0
  have hm_hdr :
      (word8Array c.hdr (c.hdrWords c.pbase cur0) ⋆
        (wsFixed c (List.replicate c.cap 0) emp ⋆ region c.pbase (4 * c.poolInts) ⋆
          Eq (cnfBytes.At cnf_ptr) ⋆ R)) m := by
    unfold wsFixed; exact sep_cast hm_u (by dsimp only [cur0]; ac_rfl)
  refine ⟨_, loadl_hdr 0 (by decide) hm_hdr (by simp),
    _, loadl_hdr 1 (by decide) hm_hdr rfl,
    _, loadl_hdr 6 (by decide) hm_hdr rfl,
    _, loadl_hdr 7 (by decide) hm_hdr rfl,
    _, loadl_hdr 8 (by decide) hm_hdr rfl,
    _, loadl_hdr 9 (by decide) hm_hdr rfl, ?_⟩
  simp only [WorkCfg.hdrWords, List.getElem_cons_succ, List.getElem_cons_zero]
  refine wp_join_group (fun () m' =>
    parseBodyPure c.mv c.nc c.poolInts [] (cnfBytes.drop idx0) = none ∧
    (Eq (cnfBytes.At cnf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m') ?_ ?_
  · rintro _ ⟨⟩ m' ⟨hnone, hm'⟩
    dsimp only [Blocks.get_here]; wp_unfold; apply hpost; rw [hnone]; exact ⟨rfl, hm'⟩
  intro Jfail hJfail
  have hmv_lt := c.hmv; have hnc_lt := c.hnc; have hnc_cap := c.hnc_cap
  have hfit_active := c.fit_active; unfold WorkCfg.activeBytes at hfit_active
  refine wp_loop_group (fun r_cl (cid_v, cur_v, pcur_v, ()) m_cl =>
    ∃ (cidNat idx poolUsed poolRem : Nat) (revClauses : List (List (BitVec 64)))
      (ptrs : List (BitVec 64)) (PoolUsed : Mem 64 → Prop),
      1 ≤ cidNat ∧ cidNat ≤ c.nc + 1 ∧ r_cl = c.nc + 1 - cidNat ∧
      revClauses.length = cidNat - 1 ∧ idx ≤ cnfBytes.length ∧
      poolUsed + poolRem = c.poolInts ∧
      cid_v = BitVec.ofNat 64 cidNat ∧ cur_v = cnf_ptr + BitVec.ofNat 64 idx ∧
      pcur_v = c.pbase + BitVec.ofNat 64 (4 * poolUsed) ∧
      parseBodyPure c.mv (c.nc + 1 - cidNat) poolRem revClauses (cnfBytes.drop idx) =
        parseBodyPure c.mv c.nc c.poolInts [] (cnfBytes.drop idx0) ∧
      TableRel c.mv c.cap ptrs (initClauseTable c.cap revClauses.reverse) PoolUsed ∧
      (∀ f, PoolUsed f → region c.pbase (4 * poolUsed) f) ∧
      (Eq (cnfBytes.At cnf_ptr) ⋆
        (word8Array c.hdr (c.hdrWords c.pbase cur0) ⋆ wsFixed c ptrs PoolUsed ⋆
          region (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) (4 * poolRem)) ⋆ R) m_cl) ?_ ?_
  · rintro Jcl r_cl ⟨cid_v, cur_v, pcur_v, ⟨⟩⟩ m_cl ih_cl
      ⟨cidNat, idx, poolUsed, poolRem, revClauses, ptrs, PoolUsed,
       hcid1, hcid2, rfl, hrev_len, hidx, hpsum, rfl, rfl, rfl, hbody_inv, htr, hpu, hm_cl⟩
    dsimp only [Blocks.get_here]; wp_unfold
    unfold dimacsBound at hnc_lt
    refine ult_branch (by omega) (by omega) (fun hdone => ?_) (fun hndone => ?_)
    · obtain rfl : cidNat = c.nc + 1 := by omega
      simp only [Nat.sub_self] at hbody_inv
      refine skipWsCommentsQbe_spec hcnf hidx (by ecancel) fun j _ hj hsw => ?_
      wp_unfold
      refine cursor_eof_branch hj (by omega) (fun hj_eq => ?_) (fun hj_lt => ?_)
      · subst hj_eq
        have hbody_ok : parseBodyPure c.mv c.nc c.poolInts [] (cnfBytes.drop idx0) =
            some (revClauses.reverse, poolRem) := by
          rw [← hbody_inv]
          simp [parseBodyPure, show (skipWsComments (cnfBytes.drop idx)).isEmpty = true by
            rw [← hsw]; simp]
        let pcur := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
        have hm_hdr_cl : (word8Array c.hdr (c.hdrWords c.pbase cur0) ⋆
            (wsFixed c ptrs PoolUsed ⋆ region pcur (4 * poolRem) ⋆
              Eq (cnfBytes.At cnf_ptr) ⋆ R)) m_cl :=
          sep_cast hm_cl (by dsimp only [pcur]; ac_rfl)
        obtain ⟨ok_p64, hm_done⟩ := store_word8Array (i := 8) pcur
          (by simp [WorkCfg.hdrWords]) hm_hdr_cl
        have hset : (c.hdrWords c.pbase cur0).set 8 pcur = c.hdrWords pcur cur0 := rfl
        rw [hset] at hm_done
        have hws_done : (WorkState c poolUsed poolRem cur0 ptrs
            (initClauseTable c.cap revClauses.reverse) PoolUsed ⋆
            (Eq (cnfBytes.At cnf_ptr) ⋆ R)) (storeMem m_cl i64 (c.hdr + 64) pcur) :=
          workState_sep.mpr ⟨hpsum, htr, hpu, by
            unfold wsFixed at hm_done; exact sep_cast hm_done (by dsimp only [pcur]; ac_rfl)⟩
        refine ⟨ok_p64, ?_⟩
        apply hpost; rw [hbody_ok]
        exact ⟨rfl, by simp [hrev_len], by omega, ptrs, PoolUsed,
          by rw [show c.poolInts - poolRem = poolUsed by omega]; exact sep_ac hws_done⟩
      · have hbody_none : parseBodyPure c.mv c.nc c.poolInts [] (cnfBytes.drop idx0) = none := by
          rw [← hbody_inv]; simp [parseBodyPure,
            show (skipWsComments (cnfBytes.drop idx)).isEmpty = false by
              rw [← hsw, List.drop_eq_getElem_cons hj_lt]; rfl]
        refine hJfail () m_cl ⟨hbody_none, ?_⟩
        refine wsFixed_fail_collapse c (pcur0 := c.pbase) (cur0 := cur0) (acc := [])
          htr.1 (by simp; omega) hpu ?_
        simp only [List.reverse_nil, int4Array_nil, sep_emp, List.length_nil,
          Nat.mul_zero, BitVec.add_zero]
        exact hm_cl
    · rw [show c.nc + 1 - cidNat = (c.nc - cidNat) + 1 by omega] at hbody_inv
      let pcur := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
      refine wp_loop_group (fun r_lit (lcur_v, wcur_v, ()) m_lit =>
        ∃ (lidx rem : Nat) (acc : List (BitVec 64)),
          idx ≤ lidx ∧ lidx ≤ cnfBytes.length ∧ r_lit = cnfBytes.length - lidx ∧
          poolUsed + acc.length + rem = c.poolInts ∧ acc.length + rem = poolRem ∧
          (∀ x ∈ acc, IsValidLit c.mv x) ∧
          lcur_v = cnf_ptr + BitVec.ofNat 64 lidx ∧
          wcur_v = pcur + BitVec.ofNat 64 (4 * acc.length) ∧
          parseClausePure ((cnfBytes.drop lidx).length + 1) c.mv rem acc (cnfBytes.drop lidx) =
            parseClausePure ((cnfBytes.drop idx).length + 1) c.mv poolRem [] (cnfBytes.drop idx) ∧
          (Eq (cnfBytes.At cnf_ptr) ⋆
            (word8Array c.hdr (c.hdrWords c.pbase cur0) ⋆ wsFixed c ptrs PoolUsed ⋆
              int4Array pcur acc.reverse ⋆
              region (pcur + BitVec.ofNat 64 (4 * acc.length)) (4 * rem)) ⋆ R) m_lit) ?_ ?_
      · rintro Jlit r_lit ⟨lcur_v, wcur_v, ⟨⟩⟩ m_lit ih_lit
          ⟨lidx, rem, acc, _, hlidx2, rfl, hlsum, hlrem, hacc_val, rfl, rfl, hcl_inv, hm_lit⟩
        dsimp only [Blocks.get_here]
        have hfail_lit : ∀ m',
            parseClausePure ((cnfBytes.drop lidx).length + 1) c.mv rem acc (cnfBytes.drop lidx) =
              none →
            (Eq (cnfBytes.At cnf_ptr) ⋆
              (word8Array c.hdr (c.hdrWords c.pbase cur0) ⋆ wsFixed c ptrs PoolUsed ⋆
                int4Array pcur acc.reverse ⋆
                region (pcur + BitVec.ofNat 64 (4 * acc.length)) (4 * rem)) ⋆ R) m' →
            Jfail () m' := fun m' hcl_none hm' =>
          hJfail () m' ⟨by rw [← hbody_inv, parseBodyPure, ← hcl_inv, hcl_none]; rfl,
            wsFixed_fail_collapse c htr.1 hlsum hpu hm'⟩
        refine skipWsCommentsQbe_spec hcnf hlidx2 (by ecancel) fun idx1 _ hidx1 hsw1 => ?_
        wp_unfold
        refine cursor_eof_branch hidx1 (by omega)
          (fun hi1_eq => by
            subst hi1_eq
            exact hfail_lit m_lit (parseClausePure_succ_nil (by rw [← hsw1]; simp)) hm_lit)
          (fun hlt1 => ?_)
        have hd1 := List.drop_eq_getElem_cons hlt1
        have hsw1' : skipWsComments (cnfBytes.drop lidx) =
            cnfBytes[idx1] :: cnfBytes.drop (idx1 + 1) := by rw [← hsw1, hd1]
        have hfull_iff : pcur + BitVec.ofNat 64 (4 * acc.length) = c.plim ↔ rem = 0 := by
          dsimp [pcur]
          rw [ptr_add_ofNat, show 4 * poolUsed + 4 * acc.length = 4 * (c.poolInts - rem) by omega]
          exact c.pcur_eq_plim_iff (by omega)
        refine ⟨fun hfull => ?_, fun hnfull => ?_⟩
        · have hrem0 := hfull_iff.mp hfull
          refine hfail_lit m_lit ?_ hm_lit
          by_cases hb45 : cnfBytes[idx1] = 45
          · rw [parseClausePure_succ_45 (by rwa [hb45] at hsw1')]; simp [hrem0]
          · rw [parseClausePure_succ_pos hsw1' hb45]; simp [hrem0]
        · have hrem_pos : 0 < rem := Nat.pos_of_ne_zero (fun h0 => hnfull (hfull_iff.mpr h0))
          have hstep_lit : ∀ (lit : BitVec 64) {idx2 : Nat} (hidx2 : idx2 ≤ cnfBytes.length)
              (_hlidx : lidx < idx2),
              IsValidLit c.mv lit →
              parseClausePure ((cnfBytes.drop idx2).length + 1) c.mv (rem - 1) (lit :: acc)
                (cnfBytes.drop idx2) =
                parseClausePure ((cnfBytes.drop idx).length + 1) c.mv poolRem []
                  (cnfBytes.drop idx) →
              storeOk m_lit i32 (pcur + BitVec.ofNat 64 (4 * acc.length)) ∧
                Jlit (cnf_ptr + BitVec.ofNat 64 idx2,
                      pcur + BitVec.ofNat 64 (4 * acc.length) + 4, ())
                  (storeMem m_lit i32 (pcur + BitVec.ofNat 64 (4 * acc.length)) (lit.setWidth 32)) :=
            fun lit idx2 hidx2 _ hlit_val hinv' => by
              obtain ⟨ok_sw, hm_sw⟩ := wsFixed_push_lit lit hrem_pos (by omega) hm_lit
              exact ⟨ok_sw, ih_lit _ _ _ (by omega) ⟨idx2, rem - 1, lit :: acc,
                by omega, hidx2, rfl, by simp; omega, by simp; omega,
                fun x hx => by
                  rcases List.mem_cons.mp hx with rfl | hx
                  · exact hlit_val
                  · exact hacc_val x hx,
                rfl, by simp only [List.length_cons, ptr4], hinv', hm_sw⟩⟩
          refine ⟨_, loadu8_At hlt1 (by omega) (by ecancel), ?_⟩
          rw [setWidth64_ofNat8]
          refine ⟨fun his_neg => ?_, fun hnis_neg => ?_⟩
          · have hb45 : cnfBytes[idx1] = 45 := (bv64_u8_eq (k := 45)).mp his_neg
            have hsw45 : skipWsComments (cnfBytes.drop lidx) =
                45 :: cnfBytes.drop (idx1 + 1) := by rwa [hb45] at hsw1'
            rw [ptr_step_1]
            refine readDimacsNat_spec hcnf (by omega) (by ecancel)
              (fun hnone => hfail_lit m_lit
                (by rw [parseClausePure_succ_45 hsw45]; simp [Nat.ne_of_gt hrem_pos, hnone]) hm_lit)
              fun v idx2 rest' hp_v hv_lt _ hidx2 hd2 => ?_
            wp_unfold; unfold dimacsBound at hv_lt hmv_lt
            refine bv_eq_zero_branch (v := v) (by omega)
              (fun hv0 => hfail_lit m_lit
                (by rw [parseClausePure_succ_45 hsw45]; simp [Nat.ne_of_gt hrem_pos, hp_v, hv0])
                hm_lit)
              (fun hnvz => ?_)
            refine ult_branch (a := c.mv) (b := v) (by omega) (by omega)
              (fun hmv_v => hfail_lit m_lit
                (by rw [parseClausePure_succ_45 hsw45]; simp [Nat.ne_of_gt hrem_pos, hp_v, hmv_v])
                hm_lit)
              (fun hnvbig => ?_)
            rw [show (0 : BitVec 64) - BitVec.ofNat 64 v = -BitVec.ofNat 64 v from by simp]
            have hnlit_val : IsValidLit c.mv (-BitVec.ofNat 64 v) :=
              isValidLit_neg (isValidLit_ofNat (mv := c.mv) (v := v) (by omega) (by omega)
                (by unfold dimacsBound; omega))
            refine hstep_lit (-BitVec.ofNat 64 v) hidx2 (by omega) hnlit_val ?_
            rw [← hcl_inv, parseClausePure_succ_45 hsw45]
            simp only [beq_eq_false_iff_ne.mpr (by omega : rem ≠ 0),
              beq_eq_false_iff_ne.mpr hnvz, Bool.false_eq_true, Bool.false_or,
              decide_eq_false_iff_not.mpr hnvbig, ↓reduceIte, hp_v, ← hd2]
            exact parseClausePure_fuel_irrel
              (by simp only [List.length_drop]; omega) (by simp only [List.length_drop]; omega)
          · have hb_ne45 : cnfBytes[idx1] ≠ 45 := fun h => hnis_neg ((bv64_u8_eq (k := 45)).mpr h)
            refine readDimacsNat_spec hcnf hidx1 (by ecancel)
              (fun hnone => hfail_lit m_lit (by
                rw [parseClausePure_succ_pos hsw1' hb_ne45]
                simp [Nat.ne_of_gt hrem_pos, ← hd1, hnone]) hm_lit)
              fun v idx2 rest' hp_v hv_lt _ hidx2 hd2 => ?_
            wp_unfold; unfold dimacsBound at hv_lt hmv_lt
            have hp_v' : parseNat (cnfBytes[idx1] :: cnfBytes.drop (idx1 + 1)) =
                some (v, rest') := by rwa [← hd1]
            refine bv_eq_zero_branch (v := v) (by omega) (fun hv0 => ?_) (fun hnvz => ?_)
            · have hcl_ok : parseClausePure ((cnfBytes.drop idx).length + 1) c.mv poolRem []
                  (cnfBytes.drop idx) = some (acc.reverse, rem - 1, cnfBytes.drop idx2) := by
                rw [← hcl_inv, parseClausePure_succ_pos hsw1' hb_ne45]; grind
              rw [show (BitVec.ofNat 64 cidNat).toNat = cidNat from Nat.mod_eq_of_lt (by omega)]
              obtain ⟨ok_z, ok_slot, htr', hpu', hm_slot⟩ := body_clause_finish (cidNat := cidNat)
                (by omega) hrev_len hcid1 hrem_pos (by omega) htr hpu hacc_val hm_lit
              have hwcur_step : pcur + BitVec.ofNat 64 (4 * acc.length) + 4 =
                  c.pbase + BitVec.ofNat 64 (4 * (poolUsed + (acc.length + 1))) := by
                dsimp [pcur]; grind
              refine ⟨ok_z, ok_slot, ih_cl _ _ _ (by omega)
                ⟨cidNat + 1, idx2, poolUsed + (acc.length + 1), rem - 1, acc.reverse :: revClauses,
                 ptrs.set cidNat pcur, PoolUsed ⋆ ZeroTermInts pcur acc.reverse,
                 by omega, by omega, rfl, by simp [hrev_len]; omega, hidx2, by omega,
                 bv_add_ofNat cidNat 1, rfl, hwcur_step,
                 ?_, htr', hpu', hm_slot⟩⟩
              rw [show c.nc + 1 - (cidNat + 1) = c.nc - cidNat by omega,
                ← hbody_inv, parseBodyPure, hcl_ok]
              rfl
            · refine ult_branch (a := c.mv) (b := v) (by omega) (by omega)
                (fun hmv_v => hfail_lit m_lit (by
                  rw [parseClausePure_succ_pos hsw1' hb_ne45]
                  simp only [beq_eq_false_iff_ne.mpr (by omega : rem ≠ 0),
                    beq_eq_false_iff_ne.mpr hnvz, Bool.false_eq_true, ↓reduceIte, hp_v', hmv_v])
                  hm_lit)
                (fun hnvbig => ?_)
              have hplit_val : IsValidLit c.mv (BitVec.ofNat 64 v) :=
                isValidLit_ofNat (mv := c.mv) (v := v) (by omega) (by omega)
                  (by unfold dimacsBound; omega)
              refine hstep_lit (BitVec.ofNat 64 v) hidx2 (by omega) hplit_val ?_
              rw [← hcl_inv, parseClausePure_succ_pos hsw1' hb_ne45]
              simp only [beq_eq_false_iff_ne.mpr (by omega : rem ≠ 0),
                beq_eq_false_iff_ne.mpr hnvz, Bool.false_eq_true, hnvbig, ↓reduceIte, hp_v', ← hd2]
              exact parseClausePure_fuel_irrel
                (by simp only [List.length_drop]; omega) (by simp only [List.length_drop]; omega)
      · intro Jlit hJlit; wp_unfold
        refine hJlit _ _ _ ⟨idx, poolRem, [], Nat.le_refl _, hidx, rfl,
          by simpa using hpsum, by simp, by simp, rfl, by simp [pcur], rfl, ?_⟩
        simp only [List.reverse_nil, int4Array_nil, sep_emp, List.length_nil,
          Nat.mul_zero, BitVec.add_zero]
        exact hm_cl
  · intro Jcl hJcl; wp_unfold
    have hm_init : (Eq (cnfBytes.At cnf_ptr) ⋆
        (word8Array c.hdr (c.hdrWords c.pbase cur0) ⋆ wsFixed c (List.replicate c.cap 0) emp ⋆
          region c.pbase (4 * c.poolInts)) ⋆ R) m := by
      unfold wsFixed; exact sep_cast hm_u (by dsimp only [cur0]; ac_rfl)
    refine hJcl _ _ _ ⟨1, idx0, 0, c.poolInts, [], List.replicate c.cap 0, emp,
      Nat.le_refl _, by omega, rfl, rfl, hidx0, by omega, rfl, rfl, by simp, by simp,
      by simpa [initClauseTable_nil (by omega : 1 ≤ c.cap)] using htr0,
      fun f hf => by simpa [region_zero] using hf, ?_⟩
    simpa only [Nat.mul_zero, BitVec.add_zero] using hm_init

/-! ## 5. Pure soundness of `parseBodyPure` -/

private theorem parseClauseAux_succ_45 {fuel mv : Nat} {acc : List (Literal Nat)}
    {bs rest : List UInt8} (h : skipWsComments bs = 45 :: rest) :
    parseClauseAux (fuel + 1) mv acc bs =
      match parseNat rest with
      | some (v, rest') =>
        if 1 ≤ v && v ≤ mv then parseClauseAux fuel mv ((v, false) :: acc) rest' else none
      | none => none := by
  simp only [parseClauseAux, h]; rcases parseNat rest with _ | ⟨v, rest'⟩ <;> rfl

private theorem parseClauseAux_succ_pos_zero {fuel mv : Nat} {acc : List (Literal Nat)}
    {b : UInt8} {bs rest rest' : List UInt8}
    (h : skipWsComments bs = b :: rest) (hb : b ≠ 45)
    (hp : parseNat (b :: rest) = some (0, rest')) :
    parseClauseAux (fuel + 1) mv acc bs = some (CNF.Clause.ofLiterals acc.reverse, rest') := by
  have := hb; simp [parseClauseAux, h, hp]

private theorem parseClauseAux_succ_pos_ne0 {fuel mv v : Nat} {acc : List (Literal Nat)}
    {b : UInt8} {bs rest rest' : List UInt8}
    (h : skipWsComments bs = b :: rest) (hb : b ≠ 45) (hv : v ≠ 0)
    (hp : parseNat (b :: rest) = some (v, rest')) :
    parseClauseAux (fuel + 1) mv acc bs =
      if 1 ≤ v && v ≤ mv then parseClauseAux fuel mv ((v, true) :: acc) rest' else none := by
  have := hb; have := hv; simp [parseClauseAux, h, hp]

private theorem parseClausePure_sound_aux {fuel mv poolRem : Nat} {acc : List (BitVec 64)}
    {bs : List UInt8} {clits : List (BitVec 64)} {poolRem' : Nat} {rest' : List UInt8}
    (hmv : mv < dimacsBound) (hacc : ∀ x ∈ acc, IsValidLit mv x)
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
      · subst hb45; rw [parseClausePure_succ_45 hsw] at hp
        split at hp
        · nomatch hp
        · rcases hpn : parseNat rest with _ | ⟨v, rest1⟩ <;> rw [hpn] at hp
          · nomatch hp
          · dsimp at hp; split at hp
            · nomatch hp
            · rename_i hnv
              simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at hnv
              have hv1 : 1 ≤ v := by omega
              have hvm : v ≤ mv := by omega
              have hval : IsValidLit mv (-BitVec.ofNat 64 v) :=
                isValidLit_neg (isValidLit_ofNat hv1 hvm hmv)
              obtain ⟨haux, hclits⟩ := ih (fun x hx => by
                rcases List.mem_cons.mp hx with rfl | hx; exact hval; exact hacc x hx) hp
              rw [parseClauseAux_succ_45 hsw, hpn]
              simp only [show (1 ≤ v && v ≤ mv) = true by simp [hv1, hvm], ↓reduceIte]
              rw [List.map_cons, toLiteral_neg_ofNat hv1 hvm hmv] at haux
              exact ⟨haux, hclits⟩
      · rw [parseClausePure_succ_pos hsw hb45] at hp
        split at hp
        · nomatch hp
        · rcases hpn : parseNat (b :: rest) with _ | ⟨v, rest1⟩ <;> rw [hpn] at hp
          · nomatch hp
          · dsimp at hp
            by_cases hv0 : v = 0
            · subst hv0; simp at hp; obtain ⟨rfl, _, rfl⟩ := hp
              refine ⟨?_, fun x hx => hacc x (List.mem_reverse.mp hx)⟩
              rw [parseClauseAux_succ_pos_zero hsw hb45 hpn, ← List.map_reverse]; rfl
            · simp only [beq_eq_false_iff_ne.mpr hv0, Bool.false_eq_true, ↓reduceIte] at hp
              split at hp
              · nomatch hp
              · have hv1 : 1 ≤ v := by omega
                have hvm : v ≤ mv := by omega
                have hval : IsValidLit mv (BitVec.ofNat 64 v) := isValidLit_ofNat hv1 hvm hmv
                obtain ⟨haux, hclits⟩ := ih (fun x hx => by
                  rcases List.mem_cons.mp hx with rfl | hx; exact hval; exact hacc x hx) hp
                rw [parseClauseAux_succ_pos_ne0 hsw hb45 hv0 hpn]
                simp only [show (1 ≤ v && v ≤ mv) = true by simp [hv1, hvm], ↓reduceIte]
                rw [List.map_cons, toLiteral_ofNat hv1 (by omega)] at haux
                exact ⟨haux, hclits⟩

private theorem parseBodyPure_sound_aux {mv k poolRem poolRem' : Nat}
    {revClauses clauses : List (List (BitVec 64))} {bs : List UInt8}
    (hmv : mv < dimacsBound) (hrev : ∀ cl ∈ revClauses, ∀ x ∈ cl, IsValidLit mv x)
    (hbody : parseBodyPure mv k poolRem revClauses bs = some (clauses, poolRem')) :
    (∀ cnf0 : CNF Nat,
      parseClauses mv k (revClauses.reverse.foldl (fun c lits => c.add (toClause lits)) cnf0) bs =
        some (clauses.foldl (fun c lits => c.add (toClause lits)) cnf0)) ∧
    clauses.length = revClauses.length + k ∧
    (∀ cl ∈ clauses, ∀ x ∈ cl, IsValidLit mv x) := by
  induction k generalizing poolRem revClauses bs with
  | zero =>
    simp only [parseBodyPure] at hbody
    cases hsw : (skipWsComments bs).isEmpty <;> rw [hsw] at hbody
    · nomatch hbody
    · simp at hbody; obtain ⟨rfl, _⟩ := hbody
      exact ⟨fun cnf0 => by simp [parseClauses, hsw], by simp,
        fun cl hcl => hrev cl (List.mem_reverse.mp hcl)⟩
  | succ k ih =>
    simp only [parseBodyPure] at hbody
    rcases hcl : parseClausePure (bs.length + 1) mv poolRem [] bs with
      _ | ⟨clits, poolRem1, bs'⟩ <;> rw [hcl] at hbody
    · nomatch hbody
    · obtain ⟨hcl_aux, hcl_val⟩ := parseClausePure_sound_aux hmv (by simp) hcl
      have hparse_cl : parseClause mv bs = some (toClause clits, bs') := hcl_aux
      obtain ⟨hcnf_eq, hlen, hval_all⟩ := ih (fun cl hmem => by
        rcases List.mem_cons.mp hmem with rfl | hmem; exact hcl_val; exact hrev cl hmem) hbody
      refine ⟨fun cnf0 => ?_, by simp [hlen]; omega, hval_all⟩
      simp only [parseClauses, hparse_cl]; grind

theorem parseBodyPure_sound {cnfBytes bodyRest : List UInt8} {mv nc poolInts poolRem' : Nat}
    {clauses : List (List (BitVec 64))}
    (hhdr : parseHeader cnfBytes = some (mv, nc, bodyRest))
    (hmv : mv < dimacsBound)
    (hbody : parseBodyPure mv nc poolInts [] bodyRest = some (clauses, poolRem')) :
    parseDimacs cnfBytes =
      some (clauses.foldl (fun c lits => c.add (toClause lits)) CNF.empty) ∧
    clauses.length = nc ∧
    (∀ cl ∈ clauses, ∀ x ∈ cl, IsValidLit mv x) := by
  obtain ⟨hclauses, hlen, hval⟩ := parseBodyPure_sound_aux hmv (by simp) hbody
  exact ⟨by unfold parseDimacs; grind, by simpa using hlen, hval⟩

/-! ## 6. DIMACS encoder round-trip (`parseDimacs_encodeDimacs`) -/

def ValidDimacsCnf (cnf : CNF Nat) : Prop :=
  cnfMaxVar cnf < dimacsBound ∧
  cnf.clauses.size < dimacsBound ∧
  ∀ cl ∈ cnf.clauses.toList, ∀ l ∈ cl.literals, 1 ≤ l.1

private theorem natToBytesAux_acc (fuel n : Nat) (acc : List UInt8) :
    natToBytesAux fuel n acc = natToBytesAux fuel n [] ++ acc := by
  induction fuel generalizing n acc with
  | zero => simp [natToBytesAux]
  | succ fuel ih => simp only [natToBytesAux]; grind

private theorem natToBytesAux_fuel_irrel {f1 f2 n : Nat} (acc : List UInt8)
    (h1 : n < f1) (h2 : n < f2) :
    natToBytesAux f1 n acc = natToBytesAux f2 n acc := by
  induction f1 generalizing f2 n acc with
  | zero => omega
  | succ fuel1 ih =>
    cases f2 with | zero => omega | succ fuel2 => simp only [natToBytesAux]; grind

private theorem natToBytes_lt_10 {n : Nat} (h : n < 10) :
    natToBytes n = [(48 + n).toUInt8] := by
  unfold natToBytes; simp [natToBytesAux, h, Nat.mod_eq_of_lt h]

private theorem natToBytes_ge_10 {n : Nat} (h : 10 ≤ n) :
    natToBytes n = natToBytes (n / 10) ++ [(48 + n % 10).toUInt8] := by
  unfold natToBytes; conv => lhs; rw [natToBytesAux]
  simp only [show ¬ n < 10 by omega, ↓reduceIte]
  rw [natToBytesAux_acc, natToBytesAux_fuel_irrel (f2 := n / 10 + 1) [] (by omega) (by omega)]

private theorem digit_toNat {d : Nat} (hd : d < 10) :
    ((48 + d).toUInt8).toNat = 48 + d := by
  simp [Nat.toUInt8, Nat.mod_eq_of_lt (by omega : 48 + d < 256)]

private theorem isDimacsDigit_digit {d : Nat} (hd : d < 10) :
    isDimacsDigit ((48 + d).toUInt8) = true := by unfold isDimacsDigit; grind

private theorem isDimacsWs_of_digit {b : UInt8} (hd : isDimacsDigit b = true) :
    isDimacsWs b = false := by have := digit_bounds hd; unfold isDimacsWs; grind

private theorem isDimacsDigit_of_ws {b : UInt8} (hw : isDimacsWs b = true) :
    isDimacsDigit b = false := by
  cases hd : isDimacsDigit b
  · rfl
  · rw [isDimacsWs_of_digit hd] at hw; nomatch hw

private theorem ne_99_of_digit {b : UInt8} (hd : isDimacsDigit b = true) : (b == 99) = false := by
  have := digit_bounds hd; grind

private theorem ne_45_of_digit {b : UInt8} (hd : isDimacsDigit b = true) : b ≠ 45 := by
  have := digit_bounds hd; grind

private theorem natToBytes_digits (n : Nat) :
    natToBytes n ≠ [] ∧ ∀ b ∈ natToBytes n, isDimacsDigit b = true := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < 10
    · rw [natToBytes_lt_10 h]
      exact ⟨by simp, fun b hb => by rw [List.mem_singleton.mp hb]; exact isDimacsDigit_digit h⟩
    · rw [natToBytes_ge_10 (by omega)]
      obtain ⟨_, hdig⟩ := ih (n / 10) (by omega)
      refine ⟨by simp, fun b hb => ?_⟩
      rcases List.mem_append.mp hb with hb | hb
      · exact hdig b hb
      · rw [List.mem_singleton.mp hb]; exact isDimacsDigit_digit (by omega)

private theorem skipWs_natToBytes_append (n : Nat) (tail : List UInt8) :
    skipWs (natToBytes n ++ tail) = natToBytes n ++ tail := by
  obtain ⟨hne, hdig⟩ := natToBytes_digits n
  rcases h : natToBytes n with _ | ⟨b, bs⟩
  · exact absurd h hne
  · simp [skipWs, isDimacsWs_of_digit (hdig b (by simp [h]))]

private theorem skipWsComments_natToBytes_append (n : Nat) (tail : List UInt8) :
    skipWsComments (natToBytes n ++ tail) = natToBytes n ++ tail := by
  obtain ⟨hne, hdig⟩ := natToBytes_digits n
  rcases h : natToBytes n with _ | ⟨b, bs⟩
  · exact absurd h hne
  · have hb := hdig b (by simp [h])
    simp [skipWsComments, skipWsCommentsAux, isDimacsWs_of_digit hb, ne_99_of_digit hb]

private theorem parseNat_natToBytes_append {n : Nat} (hn : n < dimacsBound) (tail : List UInt8) :
    parseNat (natToBytes n ++ tail) = parseDigitsAux n tail := by
  induction n using Nat.strongRecOn generalizing tail with
  | ind n ih =>
    by_cases h : n < 10
    · rw [natToBytes_lt_10 h, List.singleton_append]
      simp only [parseNat, isDimacsDigit_digit h, ↓reduceIte, digit_toNat h]; grind
    · rw [natToBytes_ge_10 (by omega), List.append_assoc, List.singleton_append,
        ih (n / 10) (by omega) (by omega)]
      have hd : n % 10 < 10 := by omega
      simp only [parseDigitsAux, isDimacsDigit_digit hd, ↓reduceIte, digit_toNat hd]; grind

private theorem parseNat_natToBytes_ws {n : Nat} {w : UInt8} {rest : List UInt8}
    (hn : n < dimacsBound) (hw : isDimacsWs w = true) :
    parseNat (natToBytes n ++ w :: rest) = some (n, w :: rest) := by
  rw [parseNat_natToBytes_append hn]; simp [parseDigitsAux, isDimacsDigit_of_ws hw, hw]

private theorem parseHeader_encodeDimacs {cnf : CNF Nat}
    (hmv : cnfMaxVar cnf < dimacsBound) (hnc : cnf.clauses.size < dimacsBound) :
    parseHeader (encodeDimacs cnf) =
      some (cnfMaxVar cnf, cnf.clauses.size,
        10 :: cnf.clauses.toList.flatMap encodeDimacsClause) := by
  unfold encodeDimacs parseHeader
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  let body := cnf.clauses.toList.flatMap encodeDimacsClause
  have hsw0 : skipWsComments (112 :: 32 :: 99 :: 110 :: 102 :: 32 ::
      (natToBytes (cnfMaxVar cnf) ++ 32 :: (natToBytes cnf.clauses.size ++ 10 :: body))) =
      112 :: 32 :: 99 :: 110 :: 102 :: 32 ::
        (natToBytes (cnfMaxVar cnf) ++ 32 :: (natToBytes cnf.clauses.size ++ 10 :: body)) := rfl
  have hws1 : skipWs1 (32 :: 99 :: 110 :: 102 :: 32 ::
      (natToBytes (cnfMaxVar cnf) ++ 32 :: (natToBytes cnf.clauses.size ++ 10 :: body))) =
      some (99 :: 110 :: 102 :: 32 ::
        (natToBytes (cnfMaxVar cnf) ++ 32 :: (natToBytes cnf.clauses.size ++ 10 :: body))) := rfl
  have hws2 : skipWs1 (32 :: (natToBytes (cnfMaxVar cnf) ++ 32 ::
      (natToBytes cnf.clauses.size ++ 10 :: body))) =
      some (natToBytes (cnfMaxVar cnf) ++ 32 :: (natToBytes cnf.clauses.size ++ 10 :: body)) := by
    simp [skipWs1, show isDimacsWs 32 = true by decide, skipWs_natToBytes_append]
  have hp1 := parseNat_natToBytes_ws (rest := natToBytes cnf.clauses.size ++ 10 :: body)
    hmv (by decide : isDimacsWs 32 = true)
  have hws3 : skipWs1 (32 :: (natToBytes cnf.clauses.size ++ 10 :: body)) =
      some (natToBytes cnf.clauses.size ++ 10 :: body) := by
    simp [skipWs1, show isDimacsWs 32 = true by decide, skipWs_natToBytes_append]
  have hp2 := parseNat_natToBytes_ws (rest := body) hnc (by decide : isDimacsWs 10 = true)
  simp [hsw0, hws1, hws2, hp1, hws3, hp2, body]

private theorem foldl_mono_ge {α : Type} (f : Nat → α → Nat) (hf : ∀ m x, m ≤ f m x)
    (xs : List α) (m0 : Nat) : m0 ≤ xs.foldl f m0 := by
  induction xs generalizing m0 with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact Nat.le_trans (hf m0 x) (ih _)

private theorem mem_le_foldl_lit_max {ls : List (Literal Nat)} {l : Literal Nat} (m0 : Nat)
    (hl : l ∈ ls) : l.1 ≤ ls.foldl (fun m' x => Nat.max m' x.1) m0 := by
  induction ls generalizing m0 with
  | nil => nomatch hl
  | cons x ls ih =>
    rcases List.mem_cons.mp hl with rfl | hl
    · exact Nat.le_trans (Nat.le_max_right m0 l.1)
        (foldl_mono_ge _ (fun _ _ => Nat.le_max_left _ _) ls _)
    · exact ih _ hl

private theorem mem_le_cnfMaxVar {cnf : CNF Nat} {cl : CNF.Clause Nat} {l : Literal Nat}
    (hcl : cl ∈ cnf.clauses.toList) (hl : l ∈ cl.literals) :
    l.1 ≤ cnfMaxVar cnf := by
  unfold cnfMaxVar; rw [← Array.foldl_toList]
  suffices ∀ (cls : List (CNF.Clause Nat)) (m0 : Nat), cl ∈ cls →
      l.1 ≤ cls.foldl (fun m c => c.literals.foldl (fun m' x => Nat.max m' x.1) m) m0 from
    this cnf.clauses.toList 0 hcl
  intro cls; induction cls with
  | nil => intro _ h; nomatch h
  | cons c cls ih =>
    intro m0 h
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (mem_le_foldl_lit_max m0 hl)
        (foldl_mono_ge _ (fun m c' => foldl_mono_ge _ (fun _ _ => Nat.le_max_left _ _)
          c'.literals m) cls _)
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
        · subst hb; rw [parseClauseAux_succ_45 hsw, parseClauseAux_succ_45 hsw]
          rcases hpn : parseNat rest with _ | ⟨v, rest'⟩
          · rfl
          · have := parseNat_length_lt hpn; grind
        · rcases hpn : parseNat (b :: rest) with _ | ⟨v, rest'⟩
          · have := hb; simp [parseClauseAux, hsw, hpn]
          · by_cases hv0 : v = 0
            · subst hv0
              rw [parseClauseAux_succ_pos_zero hsw hb hpn, parseClauseAux_succ_pos_zero hsw hb hpn]
            · have := parseNat_length_lt hpn
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
  have hpos : 1 ≤ (natToBytes l.1).length := by grind
  cases l.2 <;> simp <;> omega

private theorem parseClauseAux_encodeLits {ls : List (Literal Nat)} {fuel mv : Nat}
    {acc : List (Literal Nat)} {rest : List UInt8}
    (hmv : mv < dimacsBound) (hls : ∀ l ∈ ls, 1 ≤ l.1 ∧ l.1 ≤ mv)
    (hfuel : (ls.flatMap encodeDimacsLit ++ ([48, 10] ++ rest)).length < fuel) :
    parseClauseAux fuel mv acc (ls.flatMap encodeDimacsLit ++ ([48, 10] ++ rest)) =
      some (CNF.Clause.ofLiterals (acc.reverse ++ ls), 10 :: rest) := by
  induction ls generalizing fuel acc with
  | nil =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [List.flatMap_nil, List.nil_append, List.cons_append, List.append_nil]
      exact parseClauseAux_succ_pos_zero (h := rfl) (by decide) rfl
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
      have hfuel' : tail.length < fuel := by grind
      simp only [List.flatMap_cons, List.append_assoc]
      change parseClauseAux (fuel + 1) mv acc (encodeDimacsLit (v, pol) ++ tail) = _
      have hcond : (1 ≤ v && v ≤ mv) = true := by simp [hv1, hvm]
      have hpn := parseNat_natToBytes_ws (rest := tail) hv_lt (by decide : isDimacsWs 32 = true)
      cases pol with
      | false =>
        rw [show encodeDimacsLit (v, false) ++ tail = 45 :: (natToBytes v ++ 32 :: tail) by
          simp [encodeDimacsLit]]
        rw [parseClauseAux_succ_45 rfl, hpn]
        simp only [hcond, ↓reduceIte]
        rw [parseClauseAux_ws_cons (by decide : isDimacsWs 32 = true), ih hls' hfuel']
        simp [List.reverse_cons]
      | true =>
        rw [show encodeDimacsLit (v, true) ++ tail = natToBytes v ++ 32 :: tail by
          simp [encodeDimacsLit]]
        have hsw := skipWsComments_natToBytes_append v (32 :: tail)
        obtain ⟨hne, hdig⟩ := natToBytes_digits v
        rcases hnb : natToBytes v with _ | ⟨b, bs_v⟩
        · exact absurd hnb hne
        · have hb_ne45 : b ≠ 45 := ne_45_of_digit (hdig b (by simp [hnb]))
          rw [hnb, List.cons_append] at hsw hpn
          rw [List.cons_append, parseClauseAux_succ_pos_ne0 hsw hb_ne45 (by omega) hpn]
          simp only [hcond, ↓reduceIte]
          rw [parseClauseAux_ws_cons (by decide : isDimacsWs 32 = true), ih hls' hfuel']
          simp [List.reverse_cons]

private theorem parseClause_encodeDimacsClause {mv : Nat} {cl : CNF.Clause Nat} {rest : List UInt8}
    (hmv : mv < dimacsBound) (hcl : ∀ l ∈ cl.literals, 1 ≤ l.1 ∧ l.1 ≤ mv) :
    parseClause mv (encodeDimacsClause cl ++ rest) = some (cl, 10 :: rest) := by
  unfold parseClause encodeDimacsClause
  rw [List.append_assoc, parseClauseAux_encodeLits hmv hcl (by omega)]; simp

private theorem parseClauses_encodeDimacsClauses {mv : Nat} {cls : List (CNF.Clause Nat)}
    (accCnf : CNF Nat) (hmv : mv < dimacsBound)
    (hcls : ∀ cl ∈ cls, ∀ l ∈ cl.literals, 1 ≤ l.1 ∧ l.1 ≤ mv) :
    parseClauses mv cls.length accCnf (10 :: cls.flatMap encodeDimacsClause) =
      some (cls.foldl CNF.add accCnf) := by
  induction cls generalizing accCnf with
  | nil => simp [parseClauses, show skipWsComments [10] = [] from rfl]
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
  rw [parseHeader_encodeDimacs hmv hnc]; dsimp
  rw [show cnf.clauses.size = cnf.clauses.toList.length by simp,
    parseClauses_encodeDimacsClauses CNF.empty hmv
      (fun cl hcl l hl => ⟨hpos cl hcl l hl, mem_le_cnfMaxVar hcl hl⟩)]
  congr 1; rcases cnf with ⟨arr⟩
  rcases hfold : arr.toList.foldl CNF.add CNF.empty with ⟨cs⟩
  have hlist := foldl_add_clauses_toList arr.toList CNF.empty
  rw [hfold] at hlist; simp [CNF.empty] at hlist
  exact congrArg CNF.mk hlist

end LeanQbe.T.Examples.LratBytes
