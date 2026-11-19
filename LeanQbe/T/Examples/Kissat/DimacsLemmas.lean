module

public import LeanQbe.T.Examples.Kissat.DimacsLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Soundness Proofs for the Kissat C0 DIMACS Parser & Model Checker (`X1` Stage B1, Part 2)

Builds on `DimacsLemmas1` to prove:
5. `kissat_parse_header_wp` and `kissat_next_lit_wp`.
6. `kissat_check_model_exact_wp` and `kissat_check_model_wp`.
7. Closed environment soundness (`dimacsExactEnv_sound`, `dimacsExactEnv_moduleOk`,
   `dimacsEnv_sound`, `dimacsEnv_moduleOk`, `dimacsEnv_ofModule_ok`, `dimacsFns_sound_in`).
8. Headline soundness `kissat_check_model_sound` (`r = 1 → ∃ cnf, LratBytes.parseDimacs cnfBytes
   = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α`, via `CoreLemmas1.checkModel_sound`) and
   composable Stage-B2 bridge lemmas (`kissat_skip_ws_comments_spec`, `kissat_parse_header_spec`,
   `kissat_next_lit_spec`, `skipWsComments_at_eof_iff`, `parseClause_eq_nextLitPure`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open Kraken.Bedrock2.Test

/-! ## 5. `Func.wp` proofs for `kissat_parse_header` and `kissat_next_lit` -/

private theorem load_cnf_byte {cnf_ptr d mv nc cur val : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (hi : i < bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val ⋆ R) m) :
    loadVal m i8 (cnf_ptr + BitVec.ofNat 64 i) = some (BitVec.ofNat 8 bs[i].toNat) :=
  load_bytes_at hi hlen (sep_ac hm : (bytes cnf_ptr bs ⋆ (dimacsState d mv nc cur val ⋆ R)) m)

private theorem load_d_mv {cnf_ptr d mv nc cur val : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val ⋆ R) m) :
    loadVal m i64 d = some mv :=
  load_dimacs_mv (sep_ac hm : (dimacsState d mv nc cur val ⋆ (bytes cnf_ptr bs ⋆ R)) m)

private theorem load_d_nc {cnf_ptr d mv nc cur val : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val ⋆ R) m) :
    loadVal m i64 (d + 8) = some nc :=
  load_dimacs_nc (sep_ac hm : (dimacsState d mv nc cur val ⋆ (bytes cnf_ptr bs ⋆ R)) m)

private theorem load_d_cur {cnf_ptr d mv nc cur val : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val ⋆ R) m) :
    loadVal m i64 (d + 16) = some cur :=
  load_dimacs_cur (sep_ac hm : (dimacsState d mv nc cur val ⋆ (bytes cnf_ptr bs ⋆ R)) m)

private theorem load_d_val {cnf_ptr d mv nc cur val : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val ⋆ R) m) :
    loadVal m i64 (d + 24) = some val :=
  load_dimacs_val (sep_ac hm : (dimacsState d mv nc cur val ⋆ (bytes cnf_ptr bs ⋆ R)) m)

private theorem store_d_mv {cnf_ptr d mv nc cur val : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (mv' : BitVec 64)
    (hm : (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val ⋆ R) m) :
    storeOk m i64 d ∧
      (bytes cnf_ptr bs ⋆ dimacsState d mv' nc cur val ⋆ R) (storeMem m i64 d mv') := by
  have ⟨hok, hst⟩ :=
    store_dimacs_mv mv' (sep_ac hm : (dimacsState d mv nc cur val ⋆ (bytes cnf_ptr bs ⋆ R)) m)
  exact ⟨hok, sep_ac hst⟩

private theorem store_d_nc {cnf_ptr d mv nc cur val : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (nc' : BitVec 64)
    (hm : (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val ⋆ R) m) :
    storeOk m i64 (d + 8) ∧
      (bytes cnf_ptr bs ⋆ dimacsState d mv nc' cur val ⋆ R) (storeMem m i64 (d + 8) nc') := by
  have ⟨hok, hst⟩ :=
    store_dimacs_nc nc' (sep_ac hm : (dimacsState d mv nc cur val ⋆ (bytes cnf_ptr bs ⋆ R)) m)
  exact ⟨hok, sep_ac hst⟩

private theorem store_d_cur {cnf_ptr d mv nc cur val : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (cur' : BitVec 64)
    (hm : (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val ⋆ R) m) :
    storeOk m i64 (d + 16) ∧
      (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur' val ⋆ R) (storeMem m i64 (d + 16) cur') := by
  have ⟨hok, hst⟩ :=
    store_dimacs_cur cur' (sep_ac hm : (dimacsState d mv nc cur val ⋆ (bytes cnf_ptr bs ⋆ R)) m)
  exact ⟨hok, sep_ac hst⟩

private theorem store_d_val {cnf_ptr d mv nc cur val : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (val' : BitVec 64)
    (hm : (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val ⋆ R) m) :
    storeOk m i64 (d + 24) ∧
      (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val' ⋆ R) (storeMem m i64 (d + 24) val') := by
  have ⟨hok, hst⟩ :=
    store_dimacs_val val' (sep_ac hm : (dimacsState d mv nc cur val ⋆ (bytes cnf_ptr bs ⋆ R)) m)
  exact ⟨hok, sep_ac hst⟩

private theorem load_vals_byte {cnf_ptr d mv nc cur val vals_ptr : BitVec 64}
    {bs valsBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (hi : i < valsBytes.length) (hlen : valsBytes.length ≤ 2 ^ 64)
    (hm : (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val ⋆
      (bytes vals_ptr valsBytes ⋆ R)) m) :
    loadVal m i8 (vals_ptr + BitVec.ofNat 64 i) = some (BitVec.ofNat 8 valsBytes[i].toNat) :=
  load_bytes_at hi hlen
    (sep_ac hm : (bytes vals_ptr valsBytes ⋆
      (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val ⋆ R)) m)

private def parseHeaderTail (bs3 : List UInt8) : Option (Nat × Nat × List UInt8) := do
  let bs4 ← skipWs1 bs3
  let (mv, bs5) ← parseNat bs4
  let bs6 ← skipWs1 bs5
  let (nc, bs7) ← parseNat bs6
  some (mv, nc, bs7)

private theorem parseHeader_of_tail {bs : List UInt8} {i2 : Nat}
    (h1 : parseHeader bs = (skipWs1 (bs.drop i2)).bind (fun
      | 99 :: 110 :: 102 :: bs3 => parseHeaderTail bs3
      | _ => none))
    {i3 : Nat} {bs2 : List UInt8}
    (hws : skipWs1 (bs.drop i2) = some bs2)
    (hd : bs.drop i3 = bs2) :
    parseHeader bs = match bs.drop i3 with
      | 99 :: 110 :: 102 :: bs3 => parseHeaderTail bs3
      | _ => none := by
  rw [h1, hws, ← hd]; rfl

theorem kissat_parse_header_wp (Γ : Env)
    (hSwc : ∀ args m Q X, kissatSkipWsCommentsSpec args m Q X →
      Γ "kissat_skip_ws_comments" [i64, i64] [i64] args m Q X)
    (hWs1 : ∀ args m Q X, kissatSkipWs1Spec args m Q X →
      Γ "kissat_skip_ws1" [i64, i64] [.bool] args m Q X)
    (hNat : ∀ args m Q X, kissatReadNatSpec args m Q X →
      Γ "kissat_read_nat" [i64, i64] [.bool] args m Q X) :
    ∀ args m Q X, kissatParseHeaderSpec args m Q X →
      Func.wp Γ kissat_parse_header_body args m Q X := by
  rintro ⟨cnf_ptr, cend, d, ⟨⟩⟩ m Q X ⟨mv0, nc0, cur0, val0, bs, R, rfl, hfit, hm, hQ⟩
  unfold Func.wp kissat_parse_header_body; wp_unfold
  have hfail : ∀ mv' nc' cur' val' m', parseHeader bs = none →
      (bytes cnf_ptr bs ⋆ dimacsState d mv' nc' cur' val' ⋆ R) m' → Q (false, ()) m' :=
    fun mv' nc' cur' val' m' hnone hm' => by rw [hnone] at hQ; exact hQ mv' nc' cur' val' m' hm'
  apply wp_call_of_spec; apply hSwc
  refine ⟨cnf_ptr, bs, 0, dimacsState d mv0 nc0 cur0 val0 ⋆ R, by simp, rfl, hfit, Nat.zero_le _,
    sep_ac hm, fun i1 _ hi1 hsw1 => ?_⟩
  simp only [List.drop_zero] at hsw1
  wp_unfold; rw [cursor_ule_rev_eq hfit hi1]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun heq => hfail mv0 nc0 cur0 val0 m (by
      have hnil : skipWsComments bs = [] := by rw [← hsw1, heq]; simp
      simp [parseHeader, hnil]) hm,
    fun hne => ?_⟩
  have hlt1 : i1 < bs.length := by omega
  have hd1 := List.drop_eq_getElem_cons hlt1
  refine ⟨_, load_cnf_byte hlt1 (by omega) hm, ?_⟩
  have h112 : ((112 : BitVec 32).setWidth 8).setWidth 32 =
      (BitVec.ofNat 8 (112 : UInt8).toNat).setWidth 32 := rfl
  rw [h112, bv32_u8_eq]
  refine ⟨fun hne112 => hfail mv0 nc0 cur0 val0 m (by
      unfold parseHeader; rw [← hsw1, hd1]
      split
      · exact absurd (List.cons.inj ‹_›).1 hne112
      · rfl) hm,
    fun heq112 => ?_⟩
  have hph1 : parseHeader bs = (skipWs1 (bs.drop (i1 + 1))).bind (fun
      | 99 :: 110 :: 102 :: bs3 => parseHeaderTail bs3
      | _ => none) := by
    unfold parseHeader; rw [← hsw1, hd1, heq112]; rfl
  rw [ptr_step_1]
  obtain ⟨ok_c1, hm1⟩ := store_d_cur (cnf_ptr + BitVec.ofNat 64 (i1 + 1)) hm
  refine ⟨ok_c1, ?_⟩
  apply wp_call_of_spec; apply hWs1
  refine ⟨cnf_ptr, mv0, nc0, val0, bs, i1 + 1, R, rfl, hfit, by omega, hm1, ?_⟩
  cases hws1 : skipWs1 (bs.drop (i1 + 1)) with
  | none =>
    wp_unfold; exact hfail mv0 nc0 _ val0 _ (by rw [hph1, hws1]; rfl) hm1
  | some bs2 =>
    intro i2 m2 _ hi2 hd2 hm2
    have hph2 := parseHeader_of_tail hph1 hws1 hd2
    wp_unfold
    refine ⟨_, load_d_cur hm2, ?_⟩
    rw [cursor_ult_rev_false hfit hi2]
    simp only [Bool.false_eq_true, false_implies, true_implies, true_and]
    rw [cursor_sub_eq hfit hi2]
    have hlt3 : (BitVec.ofNat 64 (bs.length - i2)).ult (3 : BitVec 64) =
        decide (bs.length - i2 < 3) := by
      simp only [BitVec.ult, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : bs.length - i2 < 2 ^ 64)]; rfl
    rw [hlt3]; simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    refine ⟨fun hshort => hfail mv0 nc0 _ val0 m2 (by
        rw [hph2]
        have hlen : (bs.drop i2).length < 3 := by simp; omega
        split
        · rename_i hmat; rw [hmat] at hlen; simp at hlen; omega
        · rfl) hm2,
      fun hlong => ?_⟩
    have hi2_0 : i2 < bs.length := by omega
    have hi2_1 : i2 + 1 < bs.length := by omega
    have hi2_2 : i2 + 2 < bs.length := by omega
    have hd_3 : bs.drop i2 = bs[i2] :: bs[i2 + 1] :: bs[i2 + 2] :: bs.drop (i2 + 3) := by
      rw [List.drop_eq_getElem_cons hi2_0, List.drop_eq_getElem_cons hi2_1,
        List.drop_eq_getElem_cons hi2_2]
    refine ⟨_, load_cnf_byte hi2_0 (by omega) hm2, ?_⟩
    have h99 : ((99 : BitVec 32).setWidth 8).setWidth 32 =
        (BitVec.ofNat 8 (99 : UInt8).toNat).setWidth 32 := rfl
    rw [h99, bv32_u8_eq]
    refine ⟨fun hne99 => hfail mv0 nc0 _ val0 m2 (by
        rw [hph2, hd_3]; split
        · exact absurd (List.cons.inj ‹_›).1 hne99
        · rfl) hm2,
      fun heq99 => ?_⟩
    rw [ptr_step_1]
    refine ⟨_, load_cnf_byte hi2_1 (by omega) hm2, ?_⟩
    have h110 : ((110 : BitVec 32).setWidth 8).setWidth 32 =
        (BitVec.ofNat 8 (110 : UInt8).toNat).setWidth 32 := rfl
    rw [h110, bv32_u8_eq]
    refine ⟨fun hne110 => hfail mv0 nc0 _ val0 m2 (by
        rw [hph2, hd_3, heq99]; split
        · exact absurd (List.cons.inj (List.cons.inj ‹_›).2).1 hne110
        · rfl) hm2,
      fun heq110 => ?_⟩
    rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ptr_add_ofNat]
    refine ⟨_, load_cnf_byte hi2_2 (by omega) hm2, ?_⟩
    have h102 : ((102 : BitVec 32).setWidth 8).setWidth 32 =
        (BitVec.ofNat 8 (102 : UInt8).toNat).setWidth 32 := rfl
    rw [h102, bv32_u8_eq]
    refine ⟨fun hne102 => hfail mv0 nc0 _ val0 m2 (by
        rw [hph2, hd_3, heq99, heq110]; split
        · exact absurd (List.cons.inj (List.cons.inj (List.cons.inj ‹_›).2).2).1 hne102
        · rfl) hm2,
      fun heq102 => ?_⟩
    have hph3 : parseHeader bs = parseHeaderTail (bs.drop (i2 + 3)) := by
      rw [hph2, hd_3, heq99, heq110, heq102]; rfl
    rw [show (3 : BitVec 64) = BitVec.ofNat 64 3 from rfl, ptr_add_ofNat]
    obtain ⟨ok_c2, hm3⟩ := store_d_cur (cnf_ptr + BitVec.ofNat 64 (i2 + 3)) hm2
    refine ⟨ok_c2, ?_⟩
    apply wp_call_of_spec; apply hWs1
    refine ⟨cnf_ptr, mv0, nc0, val0, bs, i2 + 3, R, rfl, hfit, by omega, hm3, ?_⟩
    cases hws2 : skipWs1 (bs.drop (i2 + 3)) with
    | none =>
      wp_unfold
      exact hfail mv0 nc0 _ val0 _ (by rw [hph3]; simp [parseHeaderTail, hws2]) hm3
    | some bs4 =>
      intro i3 m3 _ hi3 hd3 hm4
      wp_unfold
      apply wp_call_of_spec; apply hNat
      refine ⟨cnf_ptr, mv0, nc0, val0, bs, i3, R, rfl, hfit, hi3, hm4, ?_⟩
      cases hpn1 : parseNat (bs.drop i3) with
      | none =>
        wp_unfold
        exact hfail mv0 nc0 _ val0 m3
          (by rw [hph3]; simp [parseHeaderTail, hws2, ← hd3, hpn1]) hm4
      | some p1 =>
        rcases p1 with ⟨mv, bs5⟩
        intro i4 m4 hmv _ hi4 hd4 hm5
        wp_unfold
        refine ⟨_, load_d_val hm5, ?_⟩
        apply wp_call_of_spec; apply hWs1
        refine ⟨cnf_ptr, mv0, nc0, BitVec.ofNat 64 mv, bs, i4, R, rfl, hfit, hi4, hm5, ?_⟩
        cases hws3 : skipWs1 (bs.drop i4) with
        | none =>
          wp_unfold
          exact hfail mv0 nc0 _ _ m4
            (by rw [hph3]; simp [parseHeaderTail, hws2, ← hd3, hpn1, ← hd4, hws3]) hm5
        | some bs6 =>
          intro i5 m5 _ hi5 hd5 hm6
          wp_unfold
          apply wp_call_of_spec; apply hNat
          refine ⟨cnf_ptr, mv0, nc0, BitVec.ofNat 64 mv, bs, i5, R, rfl, hfit, hi5, hm6, ?_⟩
          cases hpn2 : parseNat (bs.drop i5) with
          | none =>
            wp_unfold
            exact hfail mv0 nc0 _ _ m5
              (by rw [hph3]; simp [parseHeaderTail, hws2, ← hd3, hpn1, ← hd4, hws3, ← hd5, hpn2])
              hm6
          | some p2 =>
            rcases p2 with ⟨nc, bs7⟩
            intro i6 m6 hnc _ hi6 hd6 hm7
            wp_unfold
            refine ⟨_, load_d_val hm7, ?_⟩
            obtain ⟨ok_mv, hm8⟩ := store_d_mv (BitVec.ofNat 64 mv) hm7
            obtain ⟨ok_nc, hm9⟩ := store_d_nc (BitVec.ofNat 64 nc) hm8
            refine ⟨ok_mv, ok_nc, ?_⟩
            have hph_ok : parseHeader bs = some (mv, nc, bs7) := by
              rw [hph3]; simp [parseHeaderTail, hws2, ← hd3, hpn1, ← hd4, hws3, ← hd5, hpn2]
            rw [hph_ok] at hQ
            exact hQ i6 _ hmv hnc hi6 hd6 hm9

private theorem two_mul_or_one (k : Nat) : (2 * k) ||| 1 = 2 * k + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ j =>
    simp only [Nat.testBit_succ, Nat.div_eq_of_lt (by omega : 1 < 2),
      Nat.zero_testBit, Bool.or_false]
    congr 1; omega

private theorem bv_encode_neg_lit (v : Nat) (hv1 : 1 ≤ v) (hv : v < dimacsBound) :
    (BitVec.ofNat 64 v - 1) <<< (((1 : BitVec 32).signExtend 64).toNat % 64) ||| 1 =
      BitVec.ofNat 64 (mkLit (v - 1) false) := by
  unfold dimacsBound at hv
  have hs : ((1 : BitVec 32).signExtend 64).toNat % 64 = 1 := rfl
  have hsub : BitVec.ofNat 64 v - (1 : BitVec 64) = BitVec.ofNat 64 (v - 1) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
  rw [hs, hsub]
  apply BitVec.eq_of_toNat_eq
  simp only [mkLit, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_or, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : v - 1 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : (v - 1) <<< 1 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 2 * (v - 1) + 1 < 2 ^ 64),
    Nat.shiftLeft_eq, Nat.pow_one]
  change (v - 1) * 2 ||| 1 = 2 * (v - 1) + 1
  rw [Nat.mul_comm, two_mul_or_one]

private theorem bv_encode_pos_lit (v : Nat) (hv1 : 1 ≤ v) (hv : v < dimacsBound) :
    (BitVec.ofNat 64 v - 1) <<< (((1 : BitVec 32).signExtend 64).toNat % 64) =
      BitVec.ofNat 64 (mkLit (v - 1) true) := by
  unfold dimacsBound at hv
  have hs : ((1 : BitVec 32).signExtend 64).toNat % 64 = 1 := rfl
  have hsub : BitVec.ofNat 64 v - (1 : BitVec 64) = BitVec.ofNat 64 (v - 1) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
  rw [hs, hsub]
  apply BitVec.eq_of_toNat_eq
  simp only [mkLit, ↓reduceIte, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem kissat_next_lit_wp (Γ : Env)
    (hSwc : ∀ args m Q X, kissatSkipWsCommentsSpec args m Q X →
      Γ "kissat_skip_ws_comments" [i64, i64] [i64] args m Q X)
    (hNat : ∀ args m Q X, kissatReadNatSpec args m Q X →
      Γ "kissat_read_nat" [i64, i64] [.bool] args m Q X) :
    ∀ args m Q X, kissatNextLitSpec args m Q X →
      Func.wp Γ kissat_next_lit_body args m Q X := by
  rintro ⟨cend, d, ⟨⟩⟩ m Q X ⟨cnf_ptr, nc, val0, mv, bs, i0, R, rfl, hfit, hmv64, hi0, hm, hQ⟩
  unfold Func.wp kissat_next_lit_body; wp_unfold
  have herr : ∀ cur' val' m', nextLitPure mv (bs.drop i0) = .err →
      (bytes cnf_ptr bs ⋆ dimacsState d (BitVec.ofNat 64 mv) nc cur' val' ⋆ R) m' →
      Q (0#64, ()) m' := fun cur' val' m' he hm' => by rw [he] at hQ; exact hQ cur' val' m' hm'
  refine ⟨_, load_d_cur hm, ?_⟩
  apply wp_call_of_spec; apply hSwc
  refine ⟨cnf_ptr, bs, i0,
    dimacsState d (BitVec.ofNat 64 mv) nc (cnf_ptr + BitVec.ofNat 64 i0) val0 ⋆ R,
    rfl, rfl, hfit, hi0, sep_ac hm, fun i1 hi01 hi1 hsw1 => ?_⟩
  wp_unfold; rw [cursor_ule_rev_eq hfit hi1]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun heq => herr _ val0 m (by
      have hnil : skipWsComments (bs.drop i0) = [] := by rw [← hsw1, heq]; simp
      simp [nextLitPure, hnil]) hm,
    fun hne => ?_⟩
  have hlt1 : i1 < bs.length := by omega
  have hd1 := List.drop_eq_getElem_cons hlt1
  have hsw1' : skipWsComments (bs.drop i0) = bs[i1] :: bs.drop (i1 + 1) := by rw [← hsw1, hd1]
  refine ⟨_, load_cnf_byte hlt1 (by omega) hm, ?_⟩
  rw [setWidth64_ofNat8]
  refine ⟨fun h45 => ?_, fun hn45 => ?_⟩
  · have hb45 : bs[i1] = 45 := (bv64_u8_eq (k := 45)).mp h45
    have hnl45 : nextLitPure mv (bs.drop i0) =
        match parseNat (bs.drop (i1 + 1)) with
        | none => .err
        | some (v, rest') =>
          if 1 ≤ v && v ≤ mv then .lit (mkLit (v - 1) false) rest' else .err := by
      unfold nextLitPure; rw [hsw1', hb45]; rfl
    rw [ptr_step_1]
    obtain ⟨ok_c, hm1⟩ := store_d_cur (cnf_ptr + BitVec.ofNat 64 (i1 + 1)) hm
    refine ⟨ok_c, ?_⟩
    apply wp_call_of_spec; apply hNat
    refine ⟨cnf_ptr, BitVec.ofNat 64 mv, nc, val0, bs, i1 + 1, R, rfl, hfit, by omega, hm1, ?_⟩
    cases hpn : parseNat (bs.drop (i1 + 1)) with
    | none =>
      wp_unfold; exact herr _ val0 _ (by rw [hnl45, hpn]) hm1
    | some p =>
      rcases p with ⟨v, rest'⟩
      intro j m2 hv _ hj2 hdrop hm2
      unfold dimacsBound at hv
      wp_unfold
      refine ⟨_, load_d_val hm2, ?_⟩
      have hlt1_v : (BitVec.ofNat 64 v).ult (1 : BitVec 64) = decide (v < 1) := by
        simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : v < 2 ^ 64)]; rfl
      rw [hlt1_v]; simp only [decide_eq_true_eq, decide_eq_false_iff_not]
      refine ⟨fun hv0 => herr _ _ m2 (by
          have hcond : (1 ≤ v && v ≤ mv) = false := by simp; omega
          rw [hnl45, hpn]; simp [hcond]) hm2,
        fun hv1 => ?_⟩
      refine ⟨_, load_d_mv hm2, ?_⟩
      have hgt_mv : (BitVec.ofNat 64 mv).ult (BitVec.ofNat 64 v) = decide (mv < v) := by
        simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmv64,
          Nat.mod_eq_of_lt (by omega : v < 2 ^ 64)]
      rw [hgt_mv]; simp only [decide_eq_true_eq, decide_eq_false_iff_not]
      refine ⟨fun hbig => herr _ _ m2 (by
          have hcond : (1 ≤ v && v ≤ mv) = false := by simp; omega
          rw [hnl45, hpn]; simp [hcond]) hm2,
        fun hle => ?_⟩
      have hlit_eq := bv_encode_neg_lit v (by omega) (by unfold dimacsBound; omega)
      rw [hlit_eq]
      obtain ⟨ok_v, hm3⟩ := store_d_val (BitVec.ofNat 64 (mkLit (v - 1) false)) hm2
      refine ⟨ok_v, ?_⟩
      have hres : nextLitPure mv (bs.drop i0) = .lit (mkLit (v - 1) false) rest' := by
        have hcond : (1 ≤ v && v ≤ mv) = true := by simp; omega
        rw [hnl45, hpn]; simp [hcond]
      rw [hres] at hQ
      exact hQ j _ (by simp [mkLit]; omega) (by unfold dimacsBound; simp [mkLit]; omega)
        (by omega) hj2 hdrop hm3
  · have hb45 : bs[i1] ≠ 45 := fun h => hn45 ((bv64_u8_eq (k := 45)).mpr h)
    have hnl_pos : nextLitPure mv (bs.drop i0) =
        match parseNat (bs.drop i1) with
        | none => .err
        | some (0, rest') => .endClause rest'
        | some (v, rest') =>
          if v ≤ mv then .lit (mkLit (v - 1) true) rest' else .err := by
      unfold nextLitPure; rw [hsw1']
      simp only [beq_eq_false_iff_ne.mpr hb45, Bool.false_eq_true, ↓reduceIte, ← hd1]; rfl
    obtain ⟨ok_c, hm1⟩ := store_d_cur (cnf_ptr + BitVec.ofNat 64 i1) hm
    refine ⟨ok_c, ?_⟩
    apply wp_call_of_spec; apply hNat
    refine ⟨cnf_ptr, BitVec.ofNat 64 mv, nc, val0, bs, i1, R, rfl, hfit, hi1, hm1, ?_⟩
    cases hpn : parseNat (bs.drop i1) with
    | none =>
      wp_unfold; exact herr _ val0 _ (by rw [hnl_pos, hpn]) hm1
    | some p =>
      rcases p with ⟨v, rest'⟩
      intro j m2 hv _ hj2 hdrop hm2
      unfold dimacsBound at hv
      wp_unfold
      refine ⟨_, load_d_val hm2, ?_⟩
      refine bv_eq_zero_branch (by omega)
        (fun hv0 => by
          subst hv0
          have hres : nextLitPure mv (bs.drop i0) = .endClause rest' := by
            rw [hnl_pos, hpn]; rfl
          rw [hres] at hQ
          exact hQ j m2 (by omega) hj2 hdrop hm2)
        (fun hvnz => ?_)
      refine ⟨_, load_d_mv hm2, ?_⟩
      have hgt_mv : (BitVec.ofNat 64 mv).ult (BitVec.ofNat 64 v) = decide (mv < v) := by
        simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmv64,
          Nat.mod_eq_of_lt (by omega : v < 2 ^ 64)]
      rw [hgt_mv]; simp only [decide_eq_true_eq, decide_eq_false_iff_not]
      refine ⟨fun hbig => herr _ _ m2 (by
          rw [hnl_pos, hpn]
          cases v with
          | zero => exact absurd rfl hvnz
          | succ k => simp [show ¬ k + 1 ≤ mv by omega]) hm2,
        fun hle => ?_⟩
      have hlit_eq := bv_encode_pos_lit v (by omega) (by unfold dimacsBound; omega)
      rw [hlit_eq]
      obtain ⟨ok_v, hm3⟩ := store_d_val (BitVec.ofNat 64 (mkLit (v - 1) true)) hm2
      refine ⟨ok_v, ?_⟩
      have hres : nextLitPure mv (bs.drop i0) = .lit (mkLit (v - 1) true) rest' := by
        rw [hnl_pos, hpn]
        cases v with
        | zero => exact absurd rfl hvnz
        | succ k => simp [show k + 1 ≤ mv by omega]
      rw [hres] at hQ
      exact hQ j _ (by simp [mkLit]; omega) (by unfold dimacsBound; simp [mkLit]; omega)
        (by omega) hj2 hdrop hm3

/-! ## 6. `Func.wp` proofs for `kissat_check_model` -/

private theorem bv_lit_var_addr {l : Nat} (hl : l < 2 * dimacsBound) :
    ((BitVec.ofNat 64 l) >>> (((1 : BitVec 32).signExtend 64).toNat % 64)) <<<
        (((1 : BitVec 32).signExtend 64).toNat % 64) =
      BitVec.ofNat 64 (2 * litVar l) := by
  unfold dimacsBound at hl
  unfold litVar
  have hs : ((1 : BitVec 32).signExtend 64).toNat % 64 = 1 := rfl
  rw [hs]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

private theorem bv_lit_sign_zero_iff {l : Nat} (hl : l < 2 * dimacsBound) :
    ((BitVec.ofNat 64 l &&& (1 : BitVec 64)) = 0) ↔ litSign l = false := by
  unfold dimacsBound at hl
  unfold litSign
  rw [bv_and_one (by omega), bv_eq_zero_iff (by omega)]
  grind

theorem kissat_check_model_exact_wp (Γ : Env)
    (hHdr : ∀ args m Q X, kissatParseHeaderSpec args m Q X →
      Γ "kissat_parse_header" [i64, i64, i64] [.bool] args m Q X)
    (hLit : ∀ args m Q X, kissatNextLitSpec args m Q X →
      Γ "kissat_next_lit" [i64, i64] [i64] args m Q X)
    (hSwc : ∀ args m Q X, kissatSkipWsCommentsSpec args m Q X →
      Γ "kissat_skip_ws_comments" [i64, i64] [i64] args m Q X) :
    ∀ args m Q X, kissatCheckModelExactSpec args m Q X →
      Func.wp Γ kissat_check_model_body args m Q X := by
  rintro ⟨cnf_ptr, cend, d, vals_ptr, mv_max_v, ⟨⟩⟩ m Q X
    ⟨mv0, nc0, cur0, val0, bs, valsBytes, mv_max, R, rfl, rfl, hfit, hmvmax, hvals, hvlen, hm, hQ⟩
  unfold Func.wp kissat_check_model_body; wp_unfold
  have hret0 : ∀ mv' nc' cur' val' m', runKissatCheckModel bs valsBytes mv_max = false →
      (bytes cnf_ptr bs ⋆ dimacsState d mv' nc' cur' val' ⋆
        (bytes vals_ptr valsBytes ⋆ R)) m' →
      Q (0#64, ()) m' := fun mv' nc' cur' val' m' hf hm' =>
    hQ 0#64 mv' nc' cur' val' m' (by simp [hf]) (sep_ac hm')
  apply wp_call_of_spec; apply hHdr
  change kissatParseHeaderSpec (cnf_ptr, cnf_ptr + BitVec.ofNat 64 bs.length, d, ()) m _ _
  refine ⟨mv0, nc0, cur0, val0, bs, bytes vals_ptr valsBytes ⋆ R, rfl, hfit, sep_ac hm, ?_⟩
  cases hhdr : parseHeader bs with
  | none =>
    intro mv' nc' cur' val' m' hm'
    wp_unfold
    exact hret0 mv' nc' cur' val' m' (by simp [runKissatCheckModel, hhdr]) hm'
  | some p =>
    rcases p with ⟨mv, nc, rest0⟩
    intro idx0 m0 hmv hnc hidx0 hdrop0 hm0
    have hrun0 : runKissatCheckModel bs valsBytes mv_max =
        if mv > mv_max then false else checkClausesVals mv valsBytes nc (bs.drop idx0) := by
      simp [runKissatCheckModel, hhdr, hdrop0]
    wp_unfold
    refine ⟨_, load_d_mv hm0, ?_⟩
    have hgt : (BitVec.ofNat 64 mv_max).ult (BitVec.ofNat 64 mv) = decide (mv_max < mv) := by
      unfold dimacsBound at hmv
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmvmax,
        Nat.mod_eq_of_lt (by omega : mv < 2 ^ 64)]
    rw [hgt]; simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    refine ⟨fun hbig => hret0 _ _ _ _ m0
        (by rw [hrun0]; simp [show mv > mv_max by omega]) hm0,
      fun hle => ?_⟩
    have hmv_le : mv ≤ mv_max := by omega
    have hrun_cls : runKissatCheckModel bs valsBytes mv_max =
        checkClausesVals mv valsBytes nc (bs.drop idx0) := by
      rw [hrun0]; simp [show ¬ mv > mv_max by omega]
    refine wp_loop_group
      (fun r_cl (i_v, ()) m_cl => ∃ i idx val_cl,
        i ≤ nc ∧ r_cl = nc - i ∧ idx ≤ bs.length ∧
        i_v = BitVec.ofNat 64 i ∧
        checkClausesVals mv valsBytes (nc - i) (bs.drop idx) =
          runKissatCheckModel bs valsBytes mv_max ∧
        (bytes cnf_ptr bs ⋆
          dimacsState d (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
            (cnf_ptr + BitVec.ofNat 64 idx) val_cl ⋆
          (bytes vals_ptr valsBytes ⋆ R)) m_cl)
      ?_ ?_
    · rintro L r_cl ⟨i_v, ⟨⟩⟩ m_cl ih_cl ⟨i, idx, val_cl, hi_le, rfl, hidx, rfl, hcl_inv, hm_cl⟩
      wp_unfold
      refine ⟨_, load_d_nc hm_cl, ?_⟩
      have hlt_nc : (BitVec.ofNat 64 i).ult (BitVec.ofNat 64 nc) = decide (i < nc) := by
        unfold dimacsBound at hnc
        simp only [BitVec.ult, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : i < 2 ^ 64), Nat.mod_eq_of_lt (by omega : nc < 2 ^ 64)]
      rw [hlt_nc]; simp only [decide_eq_true_eq, decide_eq_false_iff_not]
      refine ⟨fun hilt => ?_, fun hnilt => ?_⟩
      · have hsub_eq : nc - i = (nc - (i + 1)) + 1 := by omega
        rw [hsub_eq] at hcl_inv
        refine wp_loop_break_group
          (fun (sat_v, ()) m_b => ∃ idx' val_b,
            idx' ≤ bs.length ∧
            checkClauseValsAux ((bs.drop idx).length + 1) mv valsBytes false (bs.drop idx) =
              some (sat_v, bs.drop idx') ∧
            (bytes cnf_ptr bs ⋆
              dimacsState d (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
                (cnf_ptr + BitVec.ofNat 64 idx') val_b ⋆
              (bytes vals_ptr valsBytes ⋆ R)) m_b)
          (fun r_lit (sat_v, ()) m_lit => ∃ lidx val_lit,
            idx ≤ lidx ∧ lidx ≤ bs.length ∧ r_lit = bs.length - lidx ∧
            checkClauseValsAux ((bs.drop lidx).length + 1) mv valsBytes sat_v (bs.drop lidx) =
              checkClauseValsAux ((bs.drop idx).length + 1) mv valsBytes false (bs.drop idx) ∧
            (bytes cnf_ptr bs ⋆
              dimacsState d (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
                (cnf_ptr + BitVec.ofNat 64 lidx) val_lit ⋆
              (bytes vals_ptr valsBytes ⋆ R)) m_lit)
          ?_ ?_ ?_
        · rintro _ ⟨sat_v, ⟨⟩⟩ m_b ⟨idx', val_b, hidx', hcl_res, hm_b⟩
          wp_unfold
          refine ⟨fun hsat => ?_, fun hnsat => ?_⟩
          · subst hsat
            have hi_step : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
              simpa using bv_add_ofNat i 1
            rw [hi_step]
            refine ih_cl (nc - (i + 1)) _ m_b (by omega)
              ⟨i + 1, idx', val_b, by omega, rfl, hidx', rfl, ?_, hm_b⟩
            rw [← hcl_inv, checkClausesVals, hcl_res]
          · subst hnsat
            exact hret0 _ _ _ _ m_b (by rw [← hcl_inv, checkClausesVals, hcl_res]) hm_b
        · rintro B2 L2 r_lit ⟨sat_v, ⟨⟩⟩ m_lit hB2 ih_lit
            ⟨lidx, val_lit, _, hlidx, rfl, hlit_inv, hm_lit⟩
          wp_unfold
          apply wp_call_of_spec; apply hLit
          change kissatNextLitSpec (cnf_ptr + BitVec.ofNat 64 bs.length, d, ()) m_lit _ _
          refine ⟨cnf_ptr, BitVec.ofNat 64 nc, val_lit, mv, bs, lidx,
            bytes vals_ptr valsBytes ⋆ R, rfl, hfit, by unfold dimacsBound at hmv; omega, hlidx,
            hm_lit, ?_⟩
          cases hnl : nextLitPure mv (bs.drop lidx) with
          | err =>
            intro cur' val' m_e hm_e
            wp_unfold
            refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
            have hnone : checkClauseValsAux ((bs.drop idx).length + 1) mv valsBytes false
                (bs.drop idx) = none := by
              rw [← hlit_inv, checkClauseValsAux, hnl]
            exact hret0 _ _ _ _ m_e (by rw [← hcl_inv, checkClausesVals, hnone]) hm_e
          | endClause rest' =>
            intro j m_e _ hj2 hdrop_e hm_e
            wp_unfold
            refine ⟨fun h => absurd h (by decide), fun _ =>
              ⟨fun _ => ?_, fun h => absurd rfl h⟩⟩
            have hres : checkClauseValsAux ((bs.drop idx).length + 1) mv valsBytes false
                (bs.drop idx) = some (sat_v, bs.drop j) := by
              rw [← hlit_inv, checkClauseValsAux, hnl, hdrop_e]
            exact hB2 (sat_v, ()) m_e ⟨j, 0#64, hj2, hres, hm_e⟩
          | lit l rest' =>
            intro j m_l hl_mv hl_bd hlj hj2 hdrop_l hm_l
            wp_unfold
            refine ⟨fun h => absurd h (by decide), fun _ =>
              ⟨fun h => absurd h (by decide), fun _ => ?_⟩⟩
            refine ⟨_, load_d_val hm_l, ?_⟩
            rw [bv_lit_var_addr hl_bd]
            have hv_lt : 2 * litVar l < valsBytes.length := by
              unfold litVar; omega
            refine ⟨_, load_vals_byte hv_lt hvlen hm_l, ?_⟩
            have hgetD : valsBytes.getD (2 * litVar l) 0 = valsBytes[2 * litVar l] := by
              simp [List.getD_eq_getElem?_getD, hv_lt]
            have hstep_lit : ∀ m_s, m_s = m_l →
                L2 (sat_v || evalLitVals valsBytes l, ()) m_s := fun m_s hms => by
              subst m_s
              refine ih_lit (bs.length - j) _ m_l (by omega) ⟨j, BitVec.ofNat 64 l,
                by omega, hj2, rfl, ?_, hm_l⟩
              have hstep_aux :
                  checkClauseValsAux ((bs.drop lidx).length + 1) mv valsBytes sat_v (bs.drop lidx) =
                  checkClauseValsAux (bs.drop lidx).length mv valsBytes
                    (sat_v || evalLitVals valsBytes l) (bs.drop j) := by
                rw [checkClauseValsAux, hnl, ← hdrop_l]
              rw [← hlit_inv, hstep_aux]
              exact checkClauseValsAux_fuel_irrel
                (by simp only [List.length_drop]; omega)
                (by simp only [List.length_drop]; omega)
            refine wp_join_group
              (fun (sat_n, ()) m_s => sat_n = (sat_v || evalLitVals valsBytes l) ∧ m_s = m_l)
              (fun _ ⟨sat_n, ⟨⟩⟩ m_s ⟨hsat_n, hms⟩ => by
                wp_unfold; rw [hsat_n]; exact hstep_lit m_s hms)
              (fun J3 hJ3 => ?_)
            wp_unfold
            rw [bv_lit_sign_zero_iff hl_bd]
            refine ⟨fun hpos => ?_, fun hneg => ?_⟩
            · refine wp_join_group
                (fun (sat_n, ()) m_s => sat_n = (sat_v || evalLitVals valsBytes l) ∧ m_s = m_l)
                (fun _ ⟨sat_n, ⟨⟩⟩ m_s hp => by wp_unfold; exact hJ3 _ _ hp)
                (fun J4 hJ4 => ?_)
              wp_unfold
              have h0 : ((0 : BitVec 32).setWidth 8).signExtend 32 = 0#32 := rfl
              rw [h0, i8_sext32_sgt_zero]
              refine ⟨fun hvp => hJ4 (true, ()) m_l
                  ⟨by unfold evalLitVals; rw [hgetD, hpos]; simp [hvp], rfl⟩,
                fun hnvp => hJ4 (sat_v, ()) m_l
                  ⟨by unfold evalLitVals; rw [hgetD, hpos]; simp [hnvp], rfl⟩⟩
            · have hsign : litSign l = true := by cases h : litSign l <;> simp_all
              refine wp_join_group
                (fun (sat_n, ()) m_s => sat_n = (sat_v || evalLitVals valsBytes l) ∧ m_s = m_l)
                (fun _ ⟨sat_n, ⟨⟩⟩ m_s hp => by wp_unfold; exact hJ3 _ _ hp)
                (fun J5 hJ5 => ?_)
              wp_unfold
              have h0 : ((0 : BitVec 32).setWidth 8).signExtend 32 = 0#32 := rfl
              rw [h0, i8_sext32_slt_zero]
              refine ⟨fun hvn => hJ5 (true, ()) m_l
                  ⟨by unfold evalLitVals; rw [hgetD, hsign]; simp [hvn], rfl⟩,
                fun hnvn => hJ5 (sat_v, ()) m_l
                  ⟨by unfold evalLitVals; rw [hgetD, hsign]; simp [hnvn], rfl⟩⟩
        · intro B2 L2 _ hL2; wp_unfold
          exact hL2 (bs.length - idx) _ m_cl ⟨idx, val_cl, Nat.le_refl _, hidx, rfl, rfl, hm_cl⟩
      · have hi_eq : i = nc := by omega
        subst i
        simp only [Nat.sub_self, checkClausesVals] at hcl_inv
        refine ⟨_, load_d_cur hm_cl, ?_⟩
        apply wp_call_of_spec; apply hSwc
        refine ⟨cnf_ptr, bs, idx,
          dimacsState d (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
            (cnf_ptr + BitVec.ofNat 64 idx) val_cl ⋆ (bytes vals_ptr valsBytes ⋆ R),
          rfl, rfl, hfit, hidx, sep_ac hm_cl, fun j _ hj hsw => ?_⟩
        wp_unfold
        obtain ⟨ok_c, hm_c⟩ := store_d_cur (cnf_ptr + BitVec.ofNat 64 j) hm_cl
        refine ⟨ok_c, _, load_d_cur hm_c, ?_⟩
        rw [cursor_eq_iff (by omega) (by omega)]
        refine ⟨fun hne => hret0 _ _ _ _ _ (by
            rw [← hcl_inv, ← hsw, List.drop_eq_getElem_cons (by omega : j < bs.length)]; rfl)
            hm_c,
          fun heq => hQ 1#64 _ _ _ _ _ (by
            have ht : runKissatCheckModel bs valsBytes mv_max = true := by
              rw [← hcl_inv, ← hsw, heq]; simp
            simp [ht]) (sep_ac hm_c)⟩
    · intro L hL; wp_unfold
      exact hL nc _ m0 ⟨0, idx0, BitVec.ofNat 64 nc, Nat.zero_le _, by simp, hidx0, rfl,
        by simpa using hrun_cls.symm, hm0⟩

theorem kissatCheckModelExactSpec_of_spec
    {args : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : kissatCheckModelSpec args m Q X) :
    kissatCheckModelExactSpec args m Q X := by
  obtain ⟨mv0, nc0, cur0, val0, cnfBytes, valsBytes, mv_max, R,
    hcend, hmvmax_eq, hfit, hmvmax, hvals, hvlen, hm, hQ⟩ := h
  refine ⟨mv0, nc0, cur0, val0, cnfBytes, valsBytes, mv_max, R,
    hcend, hmvmax_eq, hfit, hmvmax, hvals, hvlen, hm, fun r mv' nc' cur' val' m' hr hm' => ?_⟩
  cases hrun : runKissatCheckModel cnfBytes valsBytes mv_max with
  | false =>
    rw [hrun] at hr; simp only [Bool.false_eq_true, ↓reduceIte] at hr; subst hr
    exact hQ 0#64 mv' nc' cur' val' m' (Or.inl rfl) (fun hc => by cases hc) hm'
  | true =>
    rw [hrun] at hr; simp only [↓reduceIte] at hr; subst hr
    obtain ⟨cnf, _, hparse, _, hnu, hsat⟩ := runKissatCheckModel_sound hrun
    exact hQ 1#64 mv' nc' cur' val' m' (Or.inr rfl) (fun _ => ⟨cnf, hparse, hnu, hsat⟩) hm'

theorem kissat_check_model_wp (Γ : Env)
    (hHdr : ∀ args m Q X, kissatParseHeaderSpec args m Q X →
      Γ "kissat_parse_header" [i64, i64, i64] [.bool] args m Q X)
    (hLit : ∀ args m Q X, kissatNextLitSpec args m Q X →
      Γ "kissat_next_lit" [i64, i64] [i64] args m Q X)
    (hSwc : ∀ args m Q X, kissatSkipWsCommentsSpec args m Q X →
      Γ "kissat_skip_ws_comments" [i64, i64] [i64] args m Q X) :
    ∀ args m Q X, kissatCheckModelSpec args m Q X →
      Func.wp Γ kissat_check_model_body args m Q X :=
  fun args m Q X h =>
    kissat_check_model_exact_wp Γ hHdr hLit hSwc args m Q X (kissatCheckModelExactSpec_of_spec h)

/-! ## 7. Closed module soundness (`dimacsExactEnv`, `dimacsEnv`, `ModuleOk`) -/

private theorem mkDimacsEnv_sound
    (checkSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ args m Q X, checkSpec args m Q X → kissatCheckModelExactSpec args m Q X) :
    ∀ f ∈ dimacs_fns, ∀ args m Q X,
      mkDimacsEnv checkSpec f.name f.as f.rs args m Q X →
      Func.wp (mkDimacsEnv checkSpec) f.body args m Q X := by
  intro f hf args m Q X hspec
  simp only [dimacs_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact kissat_is_ws_wp _ args m Q X hspec
  · exact kissat_is_digit_wp _ args m Q X hspec
  · exact kissat_skip_ws_comments_wp _ (fun _ _ _ _ h => h) args m Q X hspec
  · exact kissat_skip_ws1_wp _ (fun _ _ _ _ h => h) args m Q X hspec
  · exact kissat_read_nat_wp _ (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) args m Q X hspec
  · exact kissat_parse_header_wp _ (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (fun _ _ _ _ h => h) args m Q X hspec
  · exact kissat_next_lit_wp _ (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) args m Q X hspec
  · exact kissat_check_model_exact_wp _ (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (fun _ _ _ _ h => h) args m Q X (hweaken args m Q X hspec)

/-- All 8 functions in `dimacs_fns` satisfy their exact contracts in `dimacsExactEnv`. -/
theorem dimacsExactEnv_sound :
    ∀ f ∈ dimacs_fns, ∀ args m Q X,
      dimacsExactEnv f.name f.as f.rs args m Q X →
      Func.wp dimacsExactEnv f.body args m Q X :=
  mkDimacsEnv_sound kissatCheckModelExactSpec (fun _ _ _ _ h => h)

/-- Acyclic `ModuleOk` proof for `dimacsModule` under `dimacsExactEnv`. -/
theorem dimacsExactEnv_moduleOk : ModuleOk dimacsExactEnv dimacsModule :=
  Module.moduleOk_of_checkAcyclic dimacsModule_checkAcyclic dimacsFns_wf dimacsExactEnv_sound

/-- All 8 functions in `dimacs_fns` satisfy their contracts in `dimacsEnv`. -/
theorem dimacsEnv_sound :
    ∀ f ∈ dimacs_fns, ∀ args m Q X,
      dimacsEnv f.name f.as f.rs args m Q X →
      Func.wp dimacsEnv f.body args m Q X :=
  mkDimacsEnv_sound kissatCheckModelSpec (fun _ _ _ _ => kissatCheckModelExactSpec_of_spec)

/-- Headline acyclic `ModuleOk` proof for `dimacsModule` under `dimacsEnv`. -/
theorem dimacsEnv_moduleOk : ModuleOk dimacsEnv dimacsModule :=
  Module.moduleOk_of_checkAcyclic dimacsModule_checkAcyclic dimacsFns_wf dimacsEnv_sound

/-- Restricted closed-module soundness (`Env.ofModule dimacsModule dimacsEnv`). -/
theorem dimacsEnv_ofModule_ok : ModuleOk (Env.ofModule dimacsModule dimacsEnv) dimacsModule :=
  dimacsEnv_moduleOk.ofModule

/-- Lift `dimacsEnv_sound` into any environment `Γ` (such as Stage-B2 `kissatEnv`) that
subsumes `dimacsEnv` on `dimacs_fns`. -/
theorem dimacsFns_sound_in (Γ : Env)
    (hSub : ∀ f ∈ dimacs_fns, ∀ args m Q X,
      dimacsEnv f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X) :
    ∀ f ∈ dimacs_fns, ∀ args m Q X,
      dimacsEnv f.name f.as f.rs args m Q X → Func.wp Γ f.body args m Q X := by
  intro f hf args m Q X hspec
  have hwf : Func.Wf f.body := dimacsFns_wf f hf
  have hok := dimacsEnv_moduleOk
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hf
  have hwp := hok.wp_restrict (pre := pre) (post := post) hsplit hspec
  refine wp_env_mono (fun g as bs xs m' P E hg => ?_) _ m hwp
  simp only [Env.restrict, dimacsModule, List.map_nil, List.append_nil, List.mem_map] at hg
  rcases hg with ⟨⟨fn, hfn, hsig⟩, hdim⟩
  have hfn' : fn ∈ dimacs_fns := by rw [hsplit]; exact List.mem_append_left _ hfn
  cases hsig
  exact hSub fn hfn' xs m' P E hdim

/-! ## 8. Headline `kissat_check_model_sound` and composable Stage-B2 bridges -/

/-- Headline soundness of `kissat_check_model`: on any valid DIMACS buffer, 4-word `KissatDimacs`
scratch struct, and `vals` byte array of length `≥ 2 * mv_max`, `kissat_check_model` terminates
cleanly (`X` unconstrained) returning `r ∈ {0, 1}`, and `r = 1` certifies
`∃ cnf, LratBytes.parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α`
(via `CoreLemmas1.checkModel_sound`). -/
theorem kissat_check_model_sound
    {cnf_ptr d vals_ptr : BitVec 64} {mv0 nc0 cur0 val0 : BitVec 64}
    {cnfBytes valsBytes : List UInt8} {mv_max : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hmvmax : mv_max < 2 ^ 64)
    (hvals : 2 * mv_max ≤ valsBytes.length)
    (hvlen : valsBytes.length ≤ 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ dimacsState d mv0 nc0 cur0 val0 ⋆
      bytes vals_ptr valsBytes ⋆ R) m) :
    Func.wp dimacsEnv kissat_check_model_body
      (cnf_ptr, cnf_ptr + BitVec.ofNat 64 cnfBytes.length, d, vals_ptr, BitVec.ofNat 64 mv_max, ())
      m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64) ∧
        (r = 1#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        ∃ mv' nc' cur' val',
          (bytes cnf_ptr cnfBytes ⋆ dimacsState d mv' nc' cur' val' ⋆
            bytes vals_ptr valsBytes ⋆ R) m')
      X :=
  dimacsEnv_sound kissat_check_model (by simp [dimacs_fns]) _ m _ X
    ⟨mv0, nc0, cur0, val0, cnfBytes, valsBytes, mv_max, R,
      rfl, rfl, hfit, hmvmax, hvals, hvlen, hm,
      fun _ mv' nc' cur' val' _ hr hsat hm' => ⟨hr, hsat, mv', nc', cur', val', hm'⟩⟩

/-- Closed-environment specification for `kissat_skip_ws_comments` under `dimacsEnv`. -/
theorem kissat_skip_ws_comments_spec
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 : Nat} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hi0 : i0 ≤ cnfBytes.length)
    (hm : (bytes cnf_ptr cnfBytes ⋆ R) m)
    (hQ : ∀ j, i0 ≤ j → j ≤ cnfBytes.length →
      cnfBytes.drop j = skipWsComments (cnfBytes.drop i0) →
      Q (cnf_ptr + BitVec.ofNat 64 j, ()) m) :
    Func.wp dimacsEnv kissat_skip_ws_comments_body
      (cnf_ptr + BitVec.ofNat 64 i0, cnf_ptr + BitVec.ofNat 64 cnfBytes.length, ()) m Q X :=
  dimacsEnv_sound kissat_skip_ws_comments (by simp [dimacs_fns]) _ m Q X
    ⟨cnf_ptr, cnfBytes, i0, R, rfl, rfl, hfit, hi0, hm, hQ⟩

/-- Closed-environment specification for `kissat_parse_header` under `dimacsEnv`. -/
theorem kissat_parse_header_spec
    {cnf_ptr d mv0 nc0 cur0 val0 : BitVec 64} {cnfBytes : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ dimacsState d mv0 nc0 cur0 val0 ⋆ R) m)
    (hQ : match parseHeader cnfBytes with
      | none =>
        ∀ mv' nc' cur' val' m',
          (bytes cnf_ptr cnfBytes ⋆ dimacsState d mv' nc' cur' val' ⋆ R) m' →
          Q (false, ()) m'
      | some (mv, nc, rest) =>
        ∀ j m', mv < dimacsBound → nc < dimacsBound →
          j ≤ cnfBytes.length → cnfBytes.drop j = rest →
          (bytes cnf_ptr cnfBytes ⋆
            dimacsState d (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
              (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆ R) m' →
          Q (true, ()) m') :
    Func.wp dimacsEnv kissat_parse_header_body
      (cnf_ptr, cnf_ptr + BitVec.ofNat 64 cnfBytes.length, d, ()) m Q X :=
  dimacsEnv_sound kissat_parse_header (by simp [dimacs_fns]) _ m Q X
    ⟨mv0, nc0, cur0, val0, cnfBytes, R, rfl, hfit, hm, hQ⟩

/-- Closed-environment specification for `kissat_next_lit` under `dimacsEnv`. -/
theorem kissat_next_lit_spec
    {cnf_ptr d nc val0 : BitVec 64} {mv : Nat} {cnfBytes : List UInt8} {i0 : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hmv64 : mv < 2 ^ 64)
    (hi0 : i0 ≤ cnfBytes.length)
    (hm : (bytes cnf_ptr cnfBytes ⋆
      dimacsState d (BitVec.ofNat 64 mv) nc (cnf_ptr + BitVec.ofNat 64 i0) val0 ⋆ R) m)
    (hQ : match nextLitPure mv (cnfBytes.drop i0) with
      | .err =>
        ∀ cur' val' m',
          (bytes cnf_ptr cnfBytes ⋆
            dimacsState d (BitVec.ofNat 64 mv) nc cur' val' ⋆ R) m' →
          Q (0#64, ()) m'
      | .endClause rest =>
        ∀ j m', i0 < j → j ≤ cnfBytes.length → cnfBytes.drop j = rest →
          (bytes cnf_ptr cnfBytes ⋆
            dimacsState d (BitVec.ofNat 64 mv) nc (cnf_ptr + BitVec.ofNat 64 j) 0#64 ⋆ R) m' →
          Q (1#64, ()) m'
      | .lit l rest =>
        ∀ j m', l < 2 * mv → l < 2 * dimacsBound →
          i0 < j → j ≤ cnfBytes.length → cnfBytes.drop j = rest →
          (bytes cnf_ptr cnfBytes ⋆
            dimacsState d (BitVec.ofNat 64 mv) nc
              (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 l) ⋆ R) m' →
          Q (2#64, ()) m') :
    Func.wp dimacsEnv kissat_next_lit_body
      (cnf_ptr + BitVec.ofNat 64 cnfBytes.length, d, ()) m Q X :=
  dimacsEnv_sound kissat_next_lit (by simp [dimacs_fns]) _ m Q X
    ⟨cnf_ptr, nc, val0, mv, cnfBytes, i0, R, rfl, hfit, hmv64, hi0, hm, hQ⟩

/-- Helper bridge for Stage B2 (`kissat_parse_body`): unique byte index after
`kissat_skip_ws_comments`. -/
theorem skipWsComments_drop_idx {bs : List UInt8} {i0 j : Nat}
    (hj : j ≤ bs.length) (hdrop : bs.drop j = skipWsComments (bs.drop i0)) :
    j = bs.length - (skipWsComments (bs.drop i0)).length := by
  have hlen := congrArg List.length hdrop
  simp only [List.length_drop] at hlen
  omega

/-- Helper bridge for Stage B2 (`kissat_parse_body`): pointer equality `cur == cnf_end` after
`kissat_skip_ws_comments` holds iff `skipWsComments (bs.drop i0)` is empty. -/
theorem skipWsComments_at_eof_iff {cnf_ptr : BitVec 64} {bs : List UInt8} {i0 j : Nat}
    (hfit : cnf_ptr.toNat + bs.length < 2 ^ 64) (hj : j ≤ bs.length)
    (hdrop : bs.drop j = skipWsComments (bs.drop i0)) :
    cnf_ptr + BitVec.ofNat 64 j = cnf_ptr + BitVec.ofNat 64 bs.length ↔
      (skipWsComments (bs.drop i0)).isEmpty = true := by
  rw [cursor_eq_iff (by omega) (by omega), ← hdrop]
  constructor
  · intro heq; subst heq; simp
  · intro hemp
    by_cases hlt : j < bs.length
    · rw [List.drop_eq_getElem_cons hlt] at hemp; cases hemp
    · omega

/-- Helper bridge for Stage B2 (`kissat_skip_clause_syntax` / `kissat_ingest_clause`):
one-step unfolding of `LratBytes.parseClause` via `nextLitPure`. -/
theorem parseClause_eq_nextLitPure (mv : Nat) (bs : List UInt8) :
    parseClause mv bs =
      match nextLitPure mv bs with
      | .err => none
      | .endClause rest' => some (CNF.Clause.ofLiterals [], rest')
      | .lit l rest' => parseClauseAux bs.length mv [kissatLitToDimacsLiteral l] rest' :=
  parseClauseAux_eq_nextLitPure bs.length mv [] bs

/-- Convert an `i8` typed `array` to a `bytes` slice so Stage B2 can invoke `kissat_check_model`. -/
theorem array_i8_eq_bytes (a : BitVec 64) (xs : List (BitVec 8)) (h : xs.length ≤ 2 ^ 64) :
    array (t := i8) a xs = bytes a (bytesOf (t := i8) xs) := by
  funext m; apply propext
  constructor
  · intro hm
    exact (array_eq_bytesOf (t := i8) a xs (by simpa [Ty.bytes, Ty.size, i8] using h) hm).symm
  · intro hm; rw [bytes] at hm; subst hm
    exact array_bytes (t := i8) a xs (by simpa [Ty.bytes, Ty.size, i8] using h)

end LeanQbe.T.Examples.Kissat
