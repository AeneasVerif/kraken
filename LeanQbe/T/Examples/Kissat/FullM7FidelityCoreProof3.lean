module
public import LeanQbe.T.Examples.Kissat.FullM7FidelityCore
public import LeanQbe.T.Examples.Kissat.FullM4BvaLemmas1
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `FullM7Fidelity` Core Proofs — Part 3 (`BVA` with `PH_BVA_Q`)
M1-clean UNSAT-only proofs (`public section`, `0` `@[expose]`, `0` `@[local]`, `0` `import all`,
`XPost := False`, `0` SAT proofs) for the three bit-25 (`PH_BVA_Q = 0x02000000`) BVA helpers:
1. `full_bva_match_large_fid_wp` (`fidBvaMatchLargeSpec`, `PH_BVA_Q` disjoint from `PH_VIV`)
2. `full_bva_scan_cands_fid_wp` (`FullM4Bva.m4BvaScanCandsSpec`)
3. `full_bva_filter_row_fid_wp` (`FullM4Bva.m4BvaFilterRowSpec`, calling
   `full_bva_match_large_fid`).
-/
set_option autoImplicit false
public section

namespace LeanQbe.T.Examples.Kissat.FullM7FidelityCore

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapTactics
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapScanHelpers
open LeanQbe.T.Examples.Kissat.FullM4Bva
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullBvaHeapTactics

/-! ## 1. `fidBvaMatchLargeSpec` & Pure Bit-25 (`PH_BVA_Q`) Arena Helpers -/

/-- Specification for `full_bva_match_large_fid`: identical to `fullBvaMatchLargeSpec` except
clearing and checking bit 25 (`PH_BVA_Q = 0x02000000`) instead of `PH_VIV`. -/
def fidBvaMatchLargeSpec : Spec [i64, i32, i32, i32] [.bool] :=
  fun (h, cur_cr, next_lit, d_ref, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R_mem : Mem 64 → Prop) (R_set : List Nat),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullArenaVarsNodup s ∧ s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64 ∧
      cur_cr.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cur_cr.toNat = false ∧
      d_ref.toNat ∈ fullArenaClauseRefs s ∧ R_set.Nodup ∧ (∀ x ∈ R_set, x < 2 * s.core.cur_vars) ∧
      fullArenaClauseSize s cur_cr.toNat = R_set.length + 1 ∧
      (∀ l < 2 * s.core.cur_vars, (s.core.lit_mark[l]?.getD 0#8 &&& 2#8) ≠ 0#8 → l ∈ R_set) ∧
      (FullMem c s ⋆ R_mem) m ∧ ∀ ok : Bool, (ok = true →
          fullArenaClauseGarb s d_ref.toNat = false ∧
          (fullArenaHdr s d_ref.toNat &&& 0x02000000#32) = 0#32 ∧
          fullArenaClauseSize s d_ref.toNat = fullArenaClauseSize s cur_cr.toNat ∧
          next_lit.toNat ∈ fullArenaClauseLits s d_ref.toNat ∧
          (fullArenaClauseLits s d_ref.toNat).Perm (next_lit.toNat :: R_set) ∧
          ((fullArenaClauseLits s d_ref.toNat).filter (· != next_lit.toNat)).Perm R_set ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause (next_lit.toNat :: R_set))) →
        Q (ok, ()) m

theorem fidBvaMatchLargeSpec_monoX {a m Q X X'} (h : fidBvaMatchLargeSpec a m Q X) :
    fidBvaMatchLargeSpec a m Q X' :=
  h
private theorem fid_bv32_bin_flag_zero_of_lt {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
    (x &&& 0x80000000#32) = 0#32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0x80000000#32).toNat = 2 ^ 31 from rfl,
    show (0#32).toNat = 0 from rfl]
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_two_pow]
  by_cases hk : k = 31
  · subst hk; simp [Nat.testBit_lt_two_pow h]
  · simp [Ne.symm hk]
private theorem fid_bv32_garb_zero_of_and_02480000 {x : BitVec 32}
    (h : (x &&& 0x02480000#32) = 0#32) : (x &&& 0x00080000#32) = 0#32 := by
  have h1 := congrArg (· &&& 0x00080000#32) h
  rw [BitVec.and_assoc, show (0x02480000#32 &&& 0x00080000#32) = 0x00080000#32 from rfl,
    BitVec.zero_and] at h1
  exact h1
private theorem fid_bv32_bvaq_zero_of_and_02480000 {x : BitVec 32}
    (h : (x &&& 0x02480000#32) = 0#32) : (x &&& 0x02000000#32) = 0#32 := by
  have h1 := congrArg (· &&& 0x02000000#32) h
  rw [BitVec.and_assoc, show (0x02480000#32 &&& 0x02000000#32) = 0x02000000#32 from rfl,
    BitVec.zero_and] at h1
  exact h1
private theorem fid_bv32_or_bvaq_garb (x : BitVec 32) :
    ((x ||| 0x02000000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) := by
  rw [BitVec.and_or_distrib_right,
    show (0x02000000#32 &&& 0x00080000#32) = 0#32 from rfl, BitVec.or_zero]
private theorem fid_bv32_or_bvaq_shrk (x : BitVec 32) :
    ((x ||| 0x02000000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) := by
  rw [BitVec.and_or_distrib_right,
    show (0x02000000#32 &&& 0x00800000#32) = 0#32 from rfl, BitVec.or_zero]
private theorem fid_bv32_bvaq_roundtrip {x : BitVec 32} (h : (x &&& 0x02000000#32) = 0#32) :
    ((x ||| 0x02000000#32) &&& ~~~0x02000000#32) = x := by
  rw [BitVec.and_or_distrib_right,
    show (0x02000000#32 &&& ~~~0x02000000#32) = 0#32 from rfl, BitVec.or_zero]
  have h1 : x = x &&& (~~~0x02000000#32 ||| 0x02000000#32) := by
    rw [show (~~~0x02000000#32 ||| 0x02000000#32) = BitVec.allOnes 32 from rfl, BitVec.and_allOnes]
  conv => rhs; rw [h1, BitVec.and_or_distrib_left, h, BitVec.or_zero]
private theorem fid_bv32_clear_bvaq_of_zero {x : BitVec 32} (hx : (x &&& 0x02000000#32) = 0#32) :
    (x &&& ~~~0x02000000#32) = x := by
  have h1 : x = x &&& (~~~0x02000000#32 ||| 0x02000000#32) := by
    rw [show (~~~0x02000000#32 ||| 0x02000000#32) = BitVec.allOnes 32 from rfl, BitVec.and_allOnes]
  conv => rhs; rw [h1, BitVec.and_or_distrib_left, hx, BitVec.or_zero]
private theorem fidArBvaq_congr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    {ar : List (BitVec 32)}
    (hpt : ∀ i < c.arena_cap, ar[i]? = s.core.arena[i]? ∨ (i ∈ fullArenaClauseRefsCore s.core ∧
        ar[i]? = some (s.core.arena[i]?.getD 0#32 ||| 0x02000000#32))) :
    fullArenaClauseRefsCore { s.core with arena := ar } = fullArenaClauseRefsCore s.core ∧
    (∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore { s.core with arena := ar } r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseSizeCore { s.core with arena := ar } r = fullArenaClauseSizeCore s.core r ∧
      fullArenaClauseLitsCore { s.core with arena := ar } r =
        fullArenaClauseLitsCore s.core r) := by
  have hal_le := hcl.arena_len_le
  have hgt_eq : ∀ r ∈ fullArenaClauseRefsCore s.core, ∀ i,
      r < i → i < fullArenaNextOff s.core.arena s.core.arena_len r →
      ar[i]? = s.core.arena[i]? := by
    intro r hr i hgt hlt
    have hwf := hw.arena.refs_wf r hr
    rcases hpt i (by omega) with heq | ⟨hi_ref, _⟩
    · exact heq
    · exfalso; have := fullArenaScanRefs_disjoint hr hi_ref hgt; omega
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core, fullArenaNextOff ar s.core.arena_len r =
      fullArenaNextOff s.core.arena s.core.arena_len r := by
    intro r hr
    have hwf := hw.arena.refs_wf r hr
    have h2eq : ar[r + 2]? = s.core.arena[r + 2]? := hgt_eq r hr (r + 2) (by omega) (by omega)
    rcases hpt r (by omega) with heq | ⟨_, hset_r⟩
    · exact fullArenaNextOff_congr_block heq h2eq fun i hi1 hi2 => hgt_eq r hr i (by omega) hi2
    · have h1 : ¬ (r + 3 > s.core.arena_len) := by omega
      have h2 : ¬ (r + 3 + (s.core.arena[r + 2]?.getD 0#32).toNat > s.core.arena_len) := by
        unfold fullArenaClauseSizeCore at hwf; omega
      unfold fullArenaNextOff
      simp only [h1, ↓reduceIte, h2eq, h2, hset_r, Option.getD_some, fid_bv32_or_bvaq_shrk]
      split
      · rename_i hshrk
        have hnxt_eq : fullArenaNextOff s.core.arena s.core.arena_len r =
            fullArenaSkipShrk s.core.arena s.core.arena_len
              (r + 3 + (s.core.arena[r + 2]?.getD 0#32).toNat)
              (s.core.arena_len - (r + 3 + (s.core.arena[r + 2]?.getD 0#32).toNat)) := by
          unfold fullArenaNextOff; simp only [h1, ↓reduceIte, h2]; rw [ite_eq_left hshrk]
        exact fullArenaSkipShrk_congr fun i hi1 hi2 =>
          hgt_eq r hr i (by omega) (by rw [hnxt_eq]; exact hi2)
      · rfl
  refine ⟨fullArenaClauseRefsCore_congr rfl hnxt, fun r hr => ?_⟩
  have hwf := hw.arena.refs_wf r hr
  have h2eq : ar[r + 2]? = s.core.arena[r + 2]? := hgt_eq r hr (r + 2) (by omega) (by omega)
  have hsz : fullArenaClauseSizeCore { s.core with arena := ar } r =
      fullArenaClauseSizeCore s.core r := by unfold fullArenaClauseSizeCore; rw [h2eq]
  refine ⟨?_, hsz, ?_⟩
  · unfold fullArenaClauseGarbCore fullArenaHdrCore
    rcases hpt r (by omega) with heq | ⟨_, hset_r⟩
    · rw [heq]
    · rw [hset_r, Option.getD_some, fid_bv32_or_bvaq_garb]
  · exact fullArenaClauseLitsCore_congr hsz fun j hj =>
      hgt_eq r hr (r + 3 + j) (by omega) (by omega)

/-! ## 2. `full_bva_match_large_fid_wp` -/

/-- Parametric `Func.wp` proof for `full_bva_match_large_fid`, certifying `fidBvaMatchLargeSpec`
with bit-25 (`PH_BVA_Q`) checks cleanly. -/
theorem full_bva_match_large_fid_wp (Γ : Env) :
    ∀ args m Q X, fidBvaMatchLargeSpec args m Q X →
      Func.wp Γ full_bva_match_large_fid_body args m Q X := by
  rintro ⟨h, cur_cr, next_lit, d_ref, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R_mem, R_set, rfl, hslen, hw, hnodup, hl0, hdm, hcur_ref, hcur_ng, hd_ref,
     hR_nd, hR_lt, hcur_sz, hlm2_sub, hm, hQ⟩
  have hmx := c.hmaxv; have har_b := c.harena; unfold dimacsBound at hmx har_b
  have hcl := hslen.core_ok; have har_len := hcl.arena_len_arr; have hal_le := hcl.arena_len_le
  have hlm_len := hcl.lit_mark_len; have hcv_le := hcl.cur_vars_le
  have hcur_wf := hw.arena.refs_wf cur_cr.toNat hcur_ref
  have hd_wf := hw.arena.refs_wf d_ref.toNat hd_ref
  have hcur_sz_eq : (s.core.arena[cur_cr.toNat + 2]'(by omega)).toNat =
      fullArenaClauseSize s cur_cr.toNat := by
    unfold fullArenaClauseSize fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hd_sz_eq : (s.core.arena[d_ref.toNat + 2]'(by omega)).toNat =
      fullArenaClauseSize s d_ref.toNat := by
    unfold fullArenaClauseSize fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hcur2_idx : (BitVec.setWidth 64 cur_cr + 2).toNat = cur_cr.toNat + 2 := by
    change (BitVec.setWidth 64 cur_cr + 2#64).toNat = _; c0_bound
  have hd2_idx : (BitVec.setWidth 64 d_ref + 2).toNat = d_ref.toNat + 2 := by
    change (BitVec.setWidth 64 d_ref + 2#64).toNat = _; c0_bound
  have hd0_idx : (BitVec.setWidth 64 d_ref).toNat = d_ref.toNat := by c0_bound
  c0_hsteps
  · exact hQ false (fun h => by cases h)
  · exact hQ false (fun h => by cases h)
  · have hsz_eq : fullArenaClauseSize s d_ref.toNat = fullArenaClauseSize s cur_cr.toNat := by
      have h1 : s.core.arena[(BitVec.setWidth 64 d_ref + 2).toNat]'(by rw [hd2_idx]; omega) =
          s.core.arena[(BitVec.setWidth 64 cur_cr + 2).toNat]'(by rw [hcur2_idx]; omega) := by
        assumption
      have h2 := congrArg BitVec.toNat h1; simp only [hd2_idx, hcur2_idx] at h2; omega
    have h0248 : (s.core.arena[d_ref.toNat]'(by omega) &&& 0x02480000#32) = 0#32 := by
      have h1 : (s.core.arena[(BitVec.setWidth 64 d_ref).toNat]'(by rw [hd0_idx]; omega) &&&
          0x02480000#32) = 0#32 := by assumption
      simpa only [hd0_idx] using h1
    have hd_ng : fullArenaClauseGarb s d_ref.toNat = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      simp [fid_bv32_garb_zero_of_and_02480000 h0248]
    have hd_nbvaq : (fullArenaHdr s d_ref.toNat &&& 0x02000000#32) = 0#32 := by
      unfold fullArenaHdr fullArenaHdrCore
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact fid_bv32_bvaq_zero_of_and_02480000 h0248
    let sz_bv := s.core.arena[(BitVec.setWidth 64 cur_cr + 2).toNat]'(by rw [hcur2_idx]; omega)
    have hsz_bv_nat : sz_bv.toNat = fullArenaClauseSize s cur_cr.toNat := by
      dsimp only [sz_bv]; simp only [hcur2_idx]; exact hcur_sz_eq
    have hd_lits_len : (fullArenaClauseLits s d_ref.toNat).length = sz_bv.toNat := by
      unfold fullArenaClauseLits
      rw [FullBvaFwdHelpers.fullArenaClauseLitsCore_length (by
        have := hd_wf.2.2.1; have := hd_wf.2.2.2.1; omega)]
      unfold fullArenaClauseSize at hsz_eq hsz_bv_nat; omega
    have hcur2_mod : (cur_cr.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 =
        cur_cr.toNat + 2 := by
      rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
    have hsz_mod : sz_bv = s.core.arena[(cur_cr.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
        rw [hcur2_mod]; omega) := by
      dsimp only [sz_bv]; simp only [hcur2_idx, hcur2_mod]
    refine wp_loop_inv
      (fun (j, seen_next, ()) ml =>
        ml = m ∧ j.toNat ≤ sz_bv.toNat ∧
        (seen_next = true → next_lit.toNat ∈ fullArenaClauseLits s d_ref.toNat) ∧
        (∀ k < j.toNat, let dl := (s.core.arena[d_ref.toNat + 3 + k]?.getD 0#32).toNat
          dl ≠ next_lit.toNat → dl ∈ R_set))
      (fun (j, _, _) _ => sz_bv.toNat - j.toNat)
      (fun J hJ => by
        c0_hsteps; exact hJ (0#32, false, ()) m ⟨rfl, Nat.zero_le _, (fun h => by cases h),
          fun _ h => by simp only [bv_c0] at h; omega⟩)
      (fun J (j, seen_next, ()) ml ⟨hml, hj_le, hseen, hall⟩ ih => ?_)
    rcases hml with rfl
    c0_hsteps
    · have hj_lt : j.toNat < sz_bv.toNat := by rw [hsz_mod]; c0_bound
      have hj_lt_d : j.toNat < fullArenaClauseSizeCore s.core d_ref.toNat := by
        unfold fullArenaClauseSize at hsz_eq hsz_bv_nat; omega
      have hdl_idx : (BitVec.setWidth 64 d_ref + 3 + BitVec.setWidth 64 j).toNat =
          d_ref.toNat + 3 + j.toNat := by
        change (BitVec.setWidth 64 d_ref + 3#64 + BitVec.setWidth 64 j).toNat = _; c0_bound
      have hdl_mod : (d_ref.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) % 2 ^ 64 =
          d_ref.toNat + 3 + j.toNat := by
        rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; omega
      have hdl_mem : (s.core.arena[d_ref.toNat + 3 + j.toNat]'(by omega)).toNat ∈
          fullArenaClauseLits s d_ref.toNat :=
        List.mem_of_getElem? (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem hj_lt_d (by omega))
      have hdl_lt := hw.arena.lits_lt d_ref.toNat hd_ref hd_ng _ hdl_mem
      have hdl_lt_lm : (s.core.arena[(BitVec.setWidth 64 d_ref + 3 +
          BitVec.setWidth 64 j).toNat]'(by rw [hdl_idx]; omega)).toNat <
            s.core.lit_mark.length := by
        have h1 : s.core.arena[(BitVec.setWidth 64 d_ref + 3 +
            BitVec.setWidth 64 j).toNat]'(by rw [hdl_idx]; omega) =
            s.core.arena[d_ref.toNat + 3 + j.toNat]'(by omega) := by simp only [hdl_idx]
        rw [h1]; omega
      c0_hsteps
      · exact hQ false (fun h => by cases h)
      · have hdl_eq : (s.core.arena[d_ref.toNat + 3 + j.toNat]'(by omega)) = next_lit := by
          have h1 : s.core.arena[(d_ref.toNat + BitVec.toNat (3 : BitVec 64) +
              j.toNat) % 2 ^ 64]'(by rw [hdl_mod]; omega) = next_lit := by assumption
          simpa only [hdl_mod] using h1
        have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
        refine ih (j + 1#32, true, ()) ml (by dsimp only; rw [hj1]; omega)
          ⟨rfl, by rw [hj1]; omega, fun _ => by rw [← hdl_eq]; exact hdl_mem, fun k hk hne => ?_⟩
        rw [hj1] at hk
        by_cases hkj : k = j.toNat
        · subst hkj
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hdl_eq] at hne
          exact absurd rfl hne
        · exact hall k (by omega) hne
      · exact hQ false (fun h => by cases h)
      · have hdl_in : (s.core.arena[d_ref.toNat + 3 + j.toNat]'(by omega)).toNat ∈ R_set := by
          apply hlm2_sub _ hdl_lt
          have h1 : ¬ (BitVec.setWidth 32 (s.core.lit_mark[(s.core.arena[(d_ref.toNat +
              BitVec.toNat (3 : BitVec 64) + j.toNat) % 2 ^ 64]'(by
              rw [hdl_mod]; omega)).toNat]'(by simp only [hdl_mod]; omega)) &&&
              BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 2)) =
              BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0) := by assumption
          simp only [hdl_mod] at h1; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          intro h0; apply h1; apply BitVec.eq_of_toNat_eq
          have h0' := congrArg BitVec.toNat h0
          simp only [BitVec.toNat_and, BitVec.toNat_setWidth,
            show (BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 2)).toNat = 2 from rfl,
            show (BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0)).toNat = 0 from rfl,
            show (2#8 : BitVec 8).toNat = 2 from rfl,
            show (0#8 : BitVec 8).toNat = 0 from rfl] at h0' ⊢
          have hlt8 := (s.core.lit_mark[(s.core.arena[d_ref.toNat + 3 + j.toNat]'(by
            omega)).toNat]'(by omega)).isLt
          rw [Nat.mod_eq_of_lt (Nat.lt_trans hlt8 (by decide))]; exact h0'
        have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
        refine ih (j + 1#32, seen_next, ()) ml (by dsimp only; rw [hj1]; omega)
          ⟨rfl, by rw [hj1]; omega, hseen, fun k hk hne => ?_⟩
        rw [hj1] at hk
        by_cases hkj : k = j.toNat
        · subst hkj; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hdl_in
        · exact hall k (by omega) hne
    · have hj_eq : j.toNat = sz_bv.toNat := by rw [hsz_mod]; c0_bound
      refine hQ seen_next fun htrue => ?_
      have hnext_in := hseen htrue
      have hD_nd : (fullArenaClauseLits s d_ref.toNat).Nodup :=
        nodup_of_map_div2 (hnodup d_ref.toNat hd_ref hd_ng)
      have hsub : ∀ x ∈ fullArenaClauseLits s d_ref.toNat, x ≠ next_lit.toNat → x ∈ R_set := by
        intro x hx hne
        obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem hx
        have hk_sz : k < sz_bv.toNat := by rw [← hd_lits_len]; exact hk_lt
        have hk_get := FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (k := s.core)
          (r := d_ref.toNat) (j := k) (by unfold fullArenaClauseSize at hsz_eq hsz_bv_nat; omega)
          (by have := hd_wf.2.2.1; have := hd_wf.2.2.2.1
              unfold fullArenaClauseSize at hsz_eq hsz_bv_nat; omega)
        have hx_eq : x = (s.core.arena[d_ref.toNat + 3 + k]?.getD 0#32).toNat := by
          have h1 : (fullArenaClauseLits s d_ref.toNat)[k]? = some x := by
            rw [List.getElem?_eq_getElem hk_lt, hk_eq]
          unfold fullArenaClauseLits at h1; rw [hk_get] at h1
          rw [← Option.some.inj h1, List.getElem?_eq_getElem (by
            have := hd_wf.2.2.1; have := hd_wf.2.2.2.1; have := hcl.arena_len_le
            unfold fullArenaClauseSize at hsz_eq hsz_bv_nat; omega), Option.getD_some]
        rw [hx_eq] at hne ⊢; exact hall k (by omega) hne
      have ⟨hperm, hfilt⟩ := bva_match_large_perm hR_nd hD_nd hnext_in
        (by rw [hd_lits_len, hsz_bv_nat, hcur_sz]) hsub
      exact ⟨hd_ng, hd_nbvaq, hsz_eq, hnext_in, hperm, hfilt,
        clause_entails_of_perm hperm (hw.arena.entails d_ref.toNat hd_ref hd_ng)⟩

/-! ## 3. `full_bva_scan_cands_fid_wp` (`m4BvaScanCandsSpec` with `PH_BVA_Q`) -/
private def FidScanArBvaqInv (c : FullCfg) (s : FullState) (ar ql : List (BitVec 32))
    (lo hi : Nat) : Prop :=
  ar.length = c.arena_cap ∧ ql.length = 2 * c.max_vars ∧ hi ≤ c.max_vars ∧
  (∀ t, lo ≤ t → t < hi → (ql[t]?.getD 0#32).toNat ∈ fullArenaClauseRefsCore s.core ∧
    (s.core.arena[(ql[t]?.getD 0#32).toNat]?.getD 0#32 &&& 0x02000000#32) = 0#32) ∧
  (∀ idx < c.arena_cap, ar[idx]? = s.core.arena[idx]? ∨
    (∃ t, lo ≤ t ∧ t < hi ∧ (ql[t]?.getD 0#32).toNat = idx ∧
      (s.core.arena[idx]?.getD 0#32 &&& 0x02000000#32) = 0#32 ∧
      ar[idx]? = some (s.core.arena[idx]?.getD 0#32 ||| 0x02000000#32)))
private theorem fidScanArBvaqInv_init {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c) :
    FidScanArBvaqInv c s s.core.arena s.scratch.work_stk2 0 0 :=
  ⟨hlen.core_ok.arena_len_arr, hlen.scratch_ok.work_stk2_len, Nat.zero_le _,
   fun _ _ h => by omega, fun _ _ => Or.inl rfl⟩
private theorem fidScanArBvaqInv_set_ql_hi {c : FullCfg} {s : FullState} {ar ql : List (BitVec 32)}
    {nql : Nat} (h : FidScanArBvaqInv c s ar ql 0 nql) {idx : Nat} (hidx : c.max_vars ≤ idx)
    (v : BitVec 32) : FidScanArBvaqInv c s ar (ql.set idx v) 0 nql := by
  obtain ⟨har, hql, hhi, hdom, hall⟩ := h
  refine ⟨har, by simp [hql], hhi, fun t h0 ht => ?_, fun i hi => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hdom t h0 ht
  · rcases hall i hi with heq | ⟨t, h0, ht, hqt, h0v, hset⟩
    · exact Or.inl heq
    · exact Or.inr ⟨t, h0, ht, by rw [List.getElem?_set_ne (by omega)]; exact hqt, h0v, hset⟩
private theorem fidScanArBvaqInv_push {c : FullCfg} {s : FullState} {ar ql : List (BitVec 32)}
    {nql : Nat} (h : FidScanArBvaqInv c s ar ql 0 nql) {dr : BitVec 32}
    (hnql_lt : nql < c.max_vars) (hdr_ref : dr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hdr_lt : dr.toNat < c.arena_cap)
    (hdr_nbvaq : (ar[dr.toNat]'(by rw [h.1]; exact hdr_lt) &&& 0x02000000#32) = 0#32) :
    (s.core.arena[dr.toNat]?.getD 0#32 &&& 0x02000000#32) = 0#32 ∧ FidScanArBvaqInv c s
      (ar.set dr.toNat ((ar[dr.toNat]'(by rw [h.1]; exact hdr_lt)) ||| 0x02000000#32))
      (ql.set nql dr) 0 (nql + 1) := by
  obtain ⟨har, hql, hhi, hdom, hall⟩ := h
  have horig : ar[dr.toNat]? = s.core.arena[dr.toNat]? := by
    rcases hall dr.toNat hdr_lt with heq | ⟨_, _, _, _, h0v, hset⟩
    · exact heq
    · rw [List.getElem?_eq_getElem (by omega)] at hset
      have hval := Option.some.inj hset
      have h1 : ((s.core.arena[dr.toNat]?.getD 0#32 ||| 0x02000000#32) &&& 0x02000000#32) =
          0x02000000#32 := by
        rw [BitVec.and_or_distrib_right,
          show (0x02000000#32 &&& 0x02000000#32) = 0x02000000#32 from rfl, h0v, BitVec.zero_or]
      rw [hval] at hdr_nbvaq; exact absurd (hdr_nbvaq.symm.trans h1) (by decide)
  have hs_nbvaq : (s.core.arena[dr.toNat]?.getD 0#32 &&& 0x02000000#32) = 0#32 := by
    rw [← horig, List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hdr_nbvaq
  refine ⟨hs_nbvaq, by simp [har], by simp [hql], by omega, fun t h0 ht => ?_, fun i hi => ?_⟩
  · by_cases htn : t = nql
    · subst htn; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact ⟨hdr_ref, hs_nbvaq⟩
    · rw [List.getElem?_set_ne (Ne.symm htn)]; exact hdom t h0 (by omega)
  · by_cases hid : i = dr.toNat
    · subst hid
      refine Or.inr ⟨nql, Nat.zero_le _, by omega,
        by rw [List.getElem?_set_self (by omega), Option.getD_some], hs_nbvaq, ?_⟩
      rw [List.getElem?_set_self (by omega)]
      have har_eq : ar[dr.toNat]'(by omega) = s.core.arena[dr.toNat]?.getD 0#32 := by
        rw [← horig, List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [har_eq]
    · rw [List.getElem?_set_ne (Ne.symm hid)]
      rcases hall i hi with heq | ⟨t, h0, ht, hqt, h0v, hset⟩
      · exact Or.inl heq
      · exact Or.inr ⟨t, h0, by omega,
          by rw [List.getElem?_set_ne (by omega)]; exact hqt, h0v, hset⟩
private theorem fidScanArBvaqInv_clear_step {c : FullCfg} {s : FullState}
    {ar ql : List (BitVec 32)} {ci nql : Nat} (hs_ar : s.core.arena.length = c.arena_cap)
    (h : FidScanArBvaqInv c s ar ql ci nql) (hci : ci < nql)
    (hidx_lt : (ql[ci]'(by rw [h.2.1]; have := h.2.2.1; omega)).toNat < c.arena_cap) :
    let idx := (ql[ci]'(by rw [h.2.1]; have := h.2.2.1; omega)).toNat
    FidScanArBvaqInv c s
      (ar.set idx ((ar[idx]'(by rw [h.1]; exact hidx_lt)) &&& ~~~0x02000000#32))
      ql (ci + 1) nql := by
  obtain ⟨har, hql, hhi, hdom, hall⟩ := h
  intro idx
  have hidx_eq : (ql[ci]?.getD 0#32).toNat = idx := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hidx_s0 : (s.core.arena[idx]?.getD 0#32 &&& 0x02000000#32) = 0#32 := by
    have := (hdom ci (Nat.le_refl _) hci).2; rwa [hidx_eq] at this
  have har_idx_clr :
      ((ar[idx]'(by omega)) &&& ~~~0x02000000#32) = s.core.arena[idx]?.getD 0#32 := by
    rcases hall idx hidx_lt with heq | ⟨_, _, _, _, _, hset⟩
    · have : ar[idx]'(by omega) = s.core.arena[idx]?.getD 0#32 := by
        rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [this]; exact fid_bv32_clear_bvaq_of_zero hidx_s0
    · rw [List.getElem?_eq_getElem (by omega)] at hset
      rw [Option.some.inj hset]; exact fid_bv32_bvaq_roundtrip hidx_s0
  refine ⟨by simp [har], hql, hhi, fun t ht1 ht2 => hdom t (by omega) ht2, fun i hi => ?_⟩
  by_cases hid : i = idx
  · subst hid; left
    rw [List.getElem?_set_self (by omega), har_idx_clr,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  · rw [List.getElem?_set_ne (Ne.symm hid)]
    rcases hall i hi with heq | ⟨t, ht1, ht2, hqt, h0v, hset⟩
    · exact Or.inl heq
    · have htne : t ≠ ci := fun h => by subst h; rw [hidx_eq] at hqt; exact hid hqt.symm
      exact Or.inr ⟨t, by omega, ht2, hqt, h0v, hset⟩
private theorem fidScanArBvaqInv_done {c : FullCfg} {s : FullState} {ar ql : List (BitVec 32)}
    {nql : Nat} (hs_ar : s.core.arena.length = c.arena_cap)
    (h : FidScanArBvaqInv c s ar ql nql nql) : ar = s.core.arena := by
  apply list_eq_of_getElem?_eq (by rw [h.1, hs_ar])
  intro i hi
  rcases h.2.2.2.2 i (by omega) with heq | ⟨t, ht1, ht2, _⟩
  · exact heq
  · omega
private def FidLmBit4Inv (c : FullCfg) (lm1 : List (BitVec 8)) (ql : List (BitVec 32))
    (lo hi : Nat) (lm : List (BitVec 8)) : Prop :=
  lm.length = 2 * c.max_vars ∧ hi ≤ c.max_vars ∧
  (∀ t, lo ≤ t → t < hi → (ql[c.max_vars + t]?.getD 0#32).toNat < 2 * c.max_vars) ∧
  ∀ l < 2 * c.max_vars, lm[l]? = lm1[l]? ∨
    (∃ t, lo ≤ t ∧ t < hi ∧ (ql[c.max_vars + t]?.getD 0#32).toNat = l ∧
      lm[l]? = some (lm1[l]?.getD 0#8 ||| 4#8))
private theorem fidLmBit4Inv_init {c : FullCfg} {lm1 : List (BitVec 8)} {ql : List (BitVec 32)}
    (hlm1 : lm1.length = 2 * c.max_vars) : FidLmBit4Inv c lm1 ql 0 0 lm1 :=
  ⟨hlm1, Nat.zero_le _, fun _ _ h => by omega, fun _ _ => Or.inl rfl⟩
private theorem fidLmBit4Inv_set_ql_lo {c : FullCfg} {lm1 lm : List (BitVec 8)}
    {ql : List (BitVec 32)} {hi idx : Nat} (h : FidLmBit4Inv c lm1 ql 0 hi lm)
    (hidx : idx < c.max_vars) (v : BitVec 32) : FidLmBit4Inv c lm1 (ql.set idx v) 0 hi lm := by
  obtain ⟨hlm, hhi, hdom, hall⟩ := h
  refine ⟨hlm, hhi, fun t h0 ht => ?_, fun l hl => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hdom t h0 ht
  · rcases hall l hl with heq | ⟨t, h0, ht, hqt, hset⟩
    · exact Or.inl heq
    · exact Or.inr ⟨t, h0, ht, by rw [List.getElem?_set_ne (by omega)]; exact hqt, hset⟩
private theorem fidLmBit4Inv_push {c : FullCfg} {lm1 lm : List (BitVec 8)} {ql : List (BitVec 32)}
    {nnou : Nat} (hql : ql.length = 2 * c.max_vars) (h : FidLmBit4Inv c lm1 ql 0 nnou lm)
    {cand : BitVec 32} (hnn : nnou < c.max_vars) (hc_lt : cand.toNat < 2 * c.max_vars) :
    FidLmBit4Inv c lm1 (ql.set (c.max_vars + nnou) cand) 0 (nnou + 1)
      (lm.set cand.toNat ((lm[cand.toNat]'(by rw [h.1]; exact hc_lt)) ||| 4#8)) := by
  obtain ⟨hlm, hhi, hdom, hall⟩ := h
  refine ⟨by simp [hlm], by omega, fun t h0 ht => ?_, fun l hl => ?_⟩
  · by_cases htn : t = nnou
    · subst htn; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hc_lt
    · rw [List.getElem?_set_ne (by omega)]; exact hdom t h0 (by omega)
  · by_cases hlc : l = cand.toNat
    · subst hlc
      refine Or.inr ⟨nnou, Nat.zero_le _, by omega,
        by rw [List.getElem?_set_self (by omega), Option.getD_some], ?_⟩
      rw [List.getElem?_set_self (by omega)]
      rcases hall cand.toNat hc_lt with heq | ⟨_, _, _, _, hset⟩
      · have : lm[cand.toNat]'(by omega) = lm1[cand.toNat]?.getD 0#8 := by
          rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [this]
      · rw [List.getElem?_eq_getElem (by omega)] at hset
        rw [Option.some.inj hset, bv8_or4_idem]
    · rw [List.getElem?_set_ne (Ne.symm hlc)]
      rcases hall l hl with heq | ⟨t, h0, ht, hqt, hset⟩
      · exact Or.inl heq
      · exact Or.inr ⟨t, h0, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hqt, hset⟩
private theorem fidLmBit4Inv_clear_step {c : FullCfg} {lm1 lm : List (BitVec 8)}
    {ql : List (BitVec 32)} {j nnou : Nat} (hlm1 : lm1.length = 2 * c.max_vars)
    (hql : ql.length = 2 * c.max_vars)
    (hlm1_b2 : ∀ l < 2 * c.max_vars, (lm1[l]?.getD 0#8 &&& 4#8) = 0#8)
    (h : FidLmBit4Inv c lm1 ql j nnou lm) (hj : j < nnou) :
    let cl := (ql[c.max_vars + j]'(by have := h.2.1; omega)).toNat
    cl < 2 * c.max_vars ∧ FidLmBit4Inv c lm1 ql (j + 1) nnou
      (lm.set cl ((lm[cl]'(by
        have hdom := h.2.2.1 j (Nat.le_refl _) hj
        rw [List.getElem?_eq_getElem (by have := h.2.1; omega), Option.getD_some] at hdom
        rw [h.1]; exact hdom)) &&& 0xFB#8)) := by
  obtain ⟨hlm, hhi, hdom, hall⟩ := h
  intro cl
  have hcl_eq : (ql[c.max_vars + j]?.getD 0#32).toNat = cl := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hcl_lt : cl < 2 * c.max_vars := by have := hdom j (Nat.le_refl _) hj; rwa [hcl_eq] at this
  have hclr : ((lm[cl]'(by omega)) &&& 0xFB#8) = lm1[cl]?.getD 0#8 := by
    apply bv8_clear_bit2_eq_of_or4 (hlm1_b2 cl hcl_lt)
    rcases hall cl hcl_lt with heq | ⟨_, _, _, _, hset⟩
    · left; rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some]
    · right; rw [List.getElem?_eq_getElem (by omega)] at hset; exact Option.some.inj hset
  refine ⟨hcl_lt, by simp [hlm], hhi, fun t ht1 ht2 => hdom t (by omega) ht2, fun i hi => ?_⟩
  by_cases hic : i = cl
  · subst hic; left
    rw [List.getElem?_set_self (by omega), hclr,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  · rw [List.getElem?_set_ne (Ne.symm hic)]
    rcases hall i hi with heq | ⟨t, ht1, ht2, hqt, hset⟩
    · exact Or.inl heq
    · have htne : t ≠ j := fun h => by subst h; rw [hcl_eq] at hqt; exact hic hqt.symm
      exact Or.inr ⟨t, by omega, ht2, hqt, hset⟩
private theorem fidLmBit4Inv_done {c : FullCfg} {lm1 lm : List (BitVec 8)} {ql : List (BitVec 32)}
    {nnou : Nat} (hlm1 : lm1.length = 2 * c.max_vars)
    (h : FidLmBit4Inv c lm1 ql nnou nnou lm) : lm = lm1 := by
  apply list_eq_of_getElem?_eq (by rw [h.1, hlm1])
  intro i hi
  rcases h.2.2.2 i (by omega) with heq | ⟨t, ht1, ht2, _⟩
  · exact heq
  · omega
private theorem fid_scan_cands_ar_lits_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {ar ql : List (BitVec 32)} {nql : Nat}
    (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hbvaq : FidScanArBvaqInv c s ar ql 0 nql) {r : Nat} (hr : r ∈ fullArenaClauseRefsCore s.core) :
    ar[r + 2]? = s.core.arena[r + 2]? ∧
    (∀ j < fullArenaClauseSizeCore s.core r, ar[r + 3 + j]? = s.core.arena[r + 3 + j]?) := by
  have hwf := hw.arena.refs_wf r hr; have hal := hcl.arena_len_le
  constructor
  · rcases hbvaq.2.2.2.2 (r + 2) (by omega) with heq | ⟨t, _, ht, hqt, _, _⟩
    · exact heq
    · exfalso
      have ht_ref := (hbvaq.2.2.2.1 t (Nat.zero_le _) ht).1; rw [hqt] at ht_ref
      rcases Nat.lt_or_gt_of_ne (by omega : r ≠ r + 2) with hlt | hgt
      · have := fullArenaScanRefs_disjoint hr ht_ref hlt; omega
      · omega
  · intro j hj
    rcases hbvaq.2.2.2.2 (r + 3 + j) (by omega) with heq | ⟨t, _, ht, hqt, _, _⟩
    · exact heq
    · exfalso
      have ht_ref := (hbvaq.2.2.2.1 t (Nat.zero_le _) ht).1; rw [hqt] at ht_ref
      have := fullArenaScanRefs_disjoint hr ht_ref (by omega); omega
private theorem fid_scan_cands_dr_info {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {arp qlp : List (BitVec 32)} {nqlp : Nat} {dr csz_bv : BitVec 32}
    (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hbvaqp : FidScanArBvaqInv c s arp qlp 0 nqlp)
    (hdr_ref : dr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hdr_lt : dr.toNat + 3 ≤ arp.length)
    (hdr_0248 : (arp[dr.toNat]'(by omega) &&& 0x02480000#32) = 0#32)
    (hdr_sz_ar : arp[dr.toNat + 2]'(by omega) = csz_bv) :
    (arp[dr.toNat]'(by omega) &&& 0x02000000#32) = 0#32 ∧
    fullArenaClauseGarbCore s.core dr.toNat = false ∧
    fullArenaClauseSizeCore s.core dr.toNat = csz_bv.toNat := by
  have harp_l := hbvaqp.1; have hdr_nbvaq := fid_bv32_bvaq_zero_of_and_02480000 hdr_0248
  have hdr_ng_ar := fid_bv32_garb_zero_of_and_02480000 hdr_0248
  refine ⟨hdr_nbvaq, ?_, ?_⟩
  · unfold fullArenaClauseGarbCore fullArenaHdrCore
    rcases hbvaqp.2.2.2.2 dr.toNat (by omega) with heq | ⟨_, _, _, _, _, hset'⟩
    · rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some]; simp [hdr_ng_ar]
    · rw [List.getElem?_eq_getElem (by omega)] at hset'
      rw [Option.some.inj hset', fid_bv32_or_bvaq_garb] at hdr_ng_ar; simp [hdr_ng_ar]
  · have h2 := (fid_scan_cands_ar_lits_eq hcl hw hbvaqp hdr_ref).1
    unfold fullArenaClauseSizeCore
    rw [← h2, List.getElem?_eq_getElem (by omega), Option.getD_some, hdr_sz_ar]
private theorem fid_scan_cands_stepB_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {arp qlA : List (BitVec 32)} {lm1 lmA : List (BitVec 8)}
    {nqlp nn1 : Nat} {dr : BitVec 32}
    (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hwp : FullWitnessInv c F0 F_cur { s.core with arena := arp }) (hl0 : s.core.cur_level = 0)
    (hbvaqA : FidScanArBvaqInv c s arp qlA 0 nqlp) (hlm4A : FidLmBit4Inv c lm1 qlA 0 nn1 lmA)
    (hnq_lt : nqlp < c.max_vars) (hdr_ref : dr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hdr_lt : dr.toNat < c.arena_cap)
    (hdr_nbvaq : (arp[dr.toNat]'(by rw [hbvaqA.1]; exact hdr_lt) &&& 0x02000000#32) = 0#32) :
    let ar1 := arp.set dr.toNat ((arp[dr.toNat]'(by rw [hbvaqA.1]; exact hdr_lt)) ||| 0x02000000#32)
    FidScanArBvaqInv c s ar1 (qlA.set nqlp dr) 0 (nqlp + 1) ∧
    FidLmBit4Inv c lm1 (qlA.set nqlp dr) 0 nn1 lmA ∧
    FullWitnessInv c F0 F_cur { s.core with arena := ar1 } := by
  have harp_l := hbvaqA.1
  have hcl_ar : ({ s.core with arena := arp }).LengthsOk c := { hcl with arena_len_arr := harp_l }
  have ⟨_, hbvaq_next⟩ := fidScanArBvaqInv_push hbvaqA hnq_lt hdr_ref hdr_lt hdr_nbvaq
  have hlm4_next := fidLmBit4Inv_set_ql_lo hlm4A hnq_lt dr
  have hwp_refs : dr.toNat ∈ fullArenaClauseRefsCore { s.core with arena := arp } := by
    have h1 := (fidArBvaq_congr hcl hw fun i hi => by
      rcases hbvaqA.2.2.2.2 i hi with heq | ⟨t, h0, ht, hqt, _, hset'⟩
      · exact Or.inl heq
      · have ht_ref := (hbvaqA.2.2.2.1 t h0 ht).1; rw [hqt] at ht_ref
        exact Or.inr ⟨ht_ref, hset'⟩).1
    rw [h1]; exact hdr_ref
  have ⟨_, _, hw_next, _⟩ := fullWitnessInv_set_hdr_bit20 hcl_ar hwp hl0 hwp_refs
    ((arp[dr.toNat]'(by omega)) ||| 0x02000000#32)
    (by unfold fullArenaHdrCore; dsimp only
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact fid_bv32_or_bvaq_garb _)
    (by unfold fullArenaHdrCore; dsimp only
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact fid_bv32_or_bvaq_shrk _)
  exact ⟨hbvaq_next, hlm4_next, hw_next⟩
private theorem fid_scan_cands_lmj_lift {c : FullCfg} {ar : List (BitVec 32)}
    {lm0 lmj : List (BitVec 8)} {qw j csz : Nat}
    (h : LmBit2Inv c ar lm0 qw 0 j lmj) (hj : j ≤ csz) :
    LmBit2Inv c ar lm0 qw 0 csz lmj :=
  ⟨h.1, fun l hl => by
    rcases h.2 l hl with heq | ⟨k, h0, hk, har', hset'⟩
    · exact Or.inl heq
    · exact Or.inr ⟨k, h0, by omega, har', hset'⟩⟩
private def fidScanCandsMpExpr (h : Val i64) (row_off cur_qn : Val i32) (init_lits : Val i64)
    (pVals pWvec pWstk pAr pLm pScr pCnt pCntd pFl pQl : Val i64)
    (Jq : Cont [i32, i32, i32]) (nql ncntd qi qw : Val i32) (J : Cont [i32, i32])
    (csz : Val i32) (Jm : Cont [i32, i32, i32, i32])
    (min_l min_d fc jf : Val i32) (Jscan : Cont [i32, i32, i32]) :
    Expr Val Cont [i32] :=
  let e0 := full_bva_scan_cands_fid_body Val Cont (h, row_off, cur_qn, init_lits, ())
  let e1 := eLoad64 pVals (eLet64 0#64 e0)
  let e2 := eLoad64 pWvec (eLet64 0#64 e1)
  let e3 := eLoad64 pWstk (eLet64 0#64 e2)
  let e4 := eLoad64 pAr (eLet64 0#64 e3)
  let e5 := eLoad64 pLm (eLet64 0#64 e4)
  let e6 := eLoad64 pScr (eLet64 0#64 e5)
  let e7 := eLoad64 pCnt (eLet64 0#64 e6)
  let e8 := eLoad64 pCntd (eLet64 0#64 e7)
  let e9 := eLoad64 pFl (eLet64 0#64 e8)
  let e10 := eLoad64 pQl (eLet64 0#64 e9)
  let e11 := eThen (eLetBool true (eGrp0_3 Jq (nql, ncntd, qi, ()) e10))
  let e12 := eLoad32 qw (eLet64 0#64 (eLet64 0#64 (eLet64 0#64 (eLet32 0#32 e11))))
  let eL := eElse (eLetBool true (eLet32 0#32 (eGrpBody_2 J e12)))
  let eCsz := eLoad32 csz (eLet64 0#64 (eLet64 0#64 (eLet64 0#64 (eLet64 0#64 eL))))
  let eAfter := eGrp0_4 Jm (min_l, min_d, fc, jf, ()) eCsz
  eGrpBody_3 Jscan eAfter
private def fidScanCandsUpdExpr (h : Val i64) (row_off cur_qn : Val i32) (init_lits : Val i64)
    (pVals pWvec pWstk pAr pLm pScr pCnt pCntd pFl pQl : Val i64)
    (Jq : Cont [i32, i32, i32]) (nql ncntd qi qw : Val i32) (J : Cont [i32, i32])
    (csz : Val i32) (Jm : Cont [i32, i32, i32, i32]) (min_l min_d fc jf : Val i32)
    (Jscan : Cont [i32, i32, i32]) (mxv : Val i64)
    (Jmp : Cont [i32, i32, i64, i32]) (JmpL : Cont [i32, i32, i64, i32])
    (nqlp ncp : Val i32) (mp mp2 : Val i64) (nnoup dr cand : Val i32) (ok : Val .bool)
    (djf : Val i32) (Jdj : Cont [i32, .bool, i32]) : Expr Val Cont [i32] :=
  let eIf := fidScanCandsMpExpr h row_off cur_qn init_lits pVals pWvec pWstk pAr pLm pScr pCnt pCntd
    pFl pQl Jq nql ncntd qi qw J csz Jm min_l min_d fc jf Jscan
  let eIn := eThen (eLetBool true (eThen (eLetBool true eIf)))
  let eMxv := eLoad64 mxv (eSkip 10 eIn)
  let eLoop := eThen (eLetBool true (eGrp0_mp JmpL (nqlp, ncp, mp, nnoup, ())
    (eGrpBody_mp Jmp eMxv)))
  let eNotBin := eElse (eSkip 6 eLoop)
  let eNotEnd := eElse (eSkip 1 eNotBin)
  let eNeQw := eElse (eLetBool true (eLet64 mp2 (eLoad32 dr (eSkip 2 eNotEnd))))
  let eHdrOk := eElse (eSkip 8 eNeQw)
  let eSzOk := eElse (eSkip 7 eHdrOk)
  eGrp0_dj Jdj (cand, ok, djf, ()) eSzOk
private theorem fid_scan_cands_upd_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {row_off cur_qn : Val i32} {init_lits : Val i64}
    {Jq : Cont [i32, i32, i32]} {nql ncntd qi qw csz min_l min_d fc jf : Val i32}
    {J : Cont [i32, i32]} {Jm : Cont [i32, i32, i32, i32]} {Jscan : Cont [i32, i32, i32]}
    {Jmp JmpL : Cont [i32, i32, i64, i32]}
    {nqlp ncp : Val i32} {mp mp2 : Val i64} {nnoup dr cand : Val i32} {ok : Val .bool}
    {djf : Val i32} {Jdj : Cont [i32, .bool, i32]}
    {arp wsp ws1p qlp : List (BitVec 32)} {lm1 lmp : List (BitVec 8)} {mlm : Mem 64}
    (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hl0 : s.core.cur_level = 0) (hil_le : init_lits.toNat ≤ 2 * s.core.cur_vars)
    (hncp_le : ncp.toNat ≤ init_lits.toNat)
    (hwsp_l : wsp.length = 2 * c.max_vars) (hws1p_l : ws1p.length = 2 * c.max_vars)
    (hbvaqp : FidScanArBvaqInv c s arp qlp 0 nqlp.toNat)
    (hlm4p : FidLmBit4Inv c lm1 qlp 0 nnoup.toNat lmp)
    (hwp : FullWitnessInv c F0 F_cur { s.core with arena := arp })
    (hcntdp : ∀ i < ncp.toNat, (ws1p[i]?.getD 0#32).toNat < init_lits.toNat)
    (hdr_ref : dr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hdr_lt_ar : dr.toNat + 3 ≤ arp.length)
    (hdr_nbvaq : (arp[dr.toNat]'(by omega) &&& 0x02000000#32) = 0#32)
    (hmlm : (FullMem c (FullState.mk { s.core with arena := arp, lit_mark := lmp }
      { s.scratch with wsort := wsp, work_stk1 := ws1p, work_stk2 := qlp }) ⋆ R) mlm)
    (hNext : ∀ nql' nc' nnou' ar' lm' ws' ws1' ql' m',
      nc'.toNat ≤ init_lits.toNat ∧ ws'.length = 2 * c.max_vars ∧
      ws1'.length = 2 * c.max_vars ∧ FidScanArBvaqInv c s ar' ql' 0 nql'.toNat ∧
      FidLmBit4Inv c lm1 ql' 0 nnou'.toNat lm' ∧
      FullWitnessInv c F0 F_cur { s.core with arena := ar' } ∧
      (∀ i < nc'.toNat, (ws1'[i]?.getD 0#32).toNat < init_lits.toNat) ∧
      (FullMem c (FullState.mk { s.core with arena := ar', lit_mark := lm' }
        { s.scratch with wsort := ws', work_stk1 := ws1', work_stk2 := ql' }) ⋆ R) m' →
      JmpL (nql', nc', mp2, nnou', ()) m') :
    wp Γ Q X (fidScanCandsUpdExpr c.hdr row_off cur_qn init_lits
      c.pVals c.pWvec c.pWstk c.pArena c.pLitMark c.pScratchBuf c.pWsort
      c.pWorkStk1 c.pFlags c.pWorkStk2 Jq nql ncntd qi qw J csz Jm min_l min_d fc jf Jscan
      (BitVec.ofNat 64 c.max_vars) Jmp JmpL nqlp ncp mp mp2 nnoup dr cand ok djf Jdj)
      mlm := by
  have hmx := c.hmaxv; have har_b := c.harena; unfold dimacsBound at hmx har_b
  have hcv_le := hcl.cur_vars_le; have hvals_len := hcl.vals_len; have hfl_len := hcl.flags_len
  have harp_l := hbvaqp.1; have hqlp_l := hbvaqp.2.1; have hlmp_l := hlm4p.1
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
  let mkSt (ar : List (BitVec 32)) (lm : List (BitVec 8)) (ws ws1 ws2 : List (BitVec 32)) :
      FullState :=
    { core := { s.core with arena := ar, lit_mark := lm }
      scratch := { s.scratch with wsort := ws, work_stk1 := ws1, work_stk2 := ws2 } }
  dsimp only [fidScanCandsUpdExpr, fidScanCandsMpExpr, eLet64, eLet32, eLetBool, eLoad64, eLoad32,
    eThen, eElse, eGrp0_3, eGrp0_4, eGrpBody_2, eGrpBody_3, eGrpBody_mp, eGrp0_mp, eGrp0_dj,
    eSkip, full_bva_scan_cands_fid_body]
  refine wp_join_state (α := BitVec 32 × BitVec 32 × BitVec 32 ×
      List (BitVec 32) × List (BitVec 8) × List (BitVec 32) ×
      List (BitVec 32) × List (BitVec 32))
    (fun ⟨nql', nc', nnou', _, _, _, _, _⟩ => (nql', nc', nnou', ()))
    (fun ⟨nql', nc', nnou', ar', lm', ws', ws1', ql'⟩ m' =>
      nc'.toNat ≤ init_lits.toNat ∧ ws'.length = 2 * c.max_vars ∧
      ws1'.length = 2 * c.max_vars ∧ FidScanArBvaqInv c s ar' ql' 0 nql'.toNat ∧
      FidLmBit4Inv c lm1 ql' 0 nnou'.toNat lm' ∧
      FullWitnessInv c F0 F_cur { s.core with arena := ar' } ∧
      (∀ i < nc'.toNat, (ws1'[i]?.getD 0#32).toNat < init_lits.toNat) ∧
      (FullMem c (mkSt ar' lm' ws' ws1' ql') ⋆ R) m')
    (fun _ ⟨nql', nc', nnou', ar', lm', ws', ws1', ql'⟩ m' h =>
      hNext nql' nc' nnou' ar' lm' ws' ws1' ql' m' h)
    (fun Jupd hJupd => ?_)
  c0_hsteps_nogrp
  · have hcand_il : cand.toNat < init_lits.toNat := by simp only [bv_c0] at *; omega
    have hcand_lt : cand.toNat < 2 * c.max_vars := by omega
    refine wp_join_state (α := BitVec 32 × List (BitVec 8) × List (BitVec 32))
      (fun ⟨nn1, _, _⟩ => (nn1, ()))
      (fun ⟨nn1, lmA, qlA⟩ mA =>
        FidScanArBvaqInv c s arp qlA 0 nqlp.toNat ∧ FidLmBit4Inv c lm1 qlA 0 nn1.toNat lmA ∧
        (FullMem c (mkSt arp lmA wsp ws1p qlA) ⋆ R) mA)
      (fun _ ⟨nn1, lmA, qlA⟩ mA ⟨hbvaqA, hlm4A, hmA⟩ => ?_)
      (fun Ja hJa => ?_)
    · clear hmlm
      dsimp only [mkSt] at hmA
      have hqlA_l := hbvaqA.2.1
      c0_hsteps_nogrp
      refine wp_join_state (α := BitVec 32 × List (BitVec 32) × List (BitVec 32))
        (fun ⟨nq1, _, _⟩ => (nq1, ()))
        (fun ⟨nq1, arB, qlB⟩ mB =>
          FidScanArBvaqInv c s arB qlB 0 nq1.toNat ∧ FidLmBit4Inv c lm1 qlB 0 nn1.toNat lmA ∧
          FullWitnessInv c F0 F_cur { s.core with arena := arB } ∧
          (FullMem c (mkSt arB lmA wsp ws1p qlB) ⋆ R) mB)
        (fun _ ⟨nq1, arB, qlB⟩ mB ⟨hbvaqB, hlm4B, hwB, hmB⟩ => ?_)
        (fun Jb hJb => ?_)
      · clear hmA
        dsimp only [mkSt] at hmB
        have hcand_ws : (BitVec.setWidth 64 cand).toNat < wsp.length := by rw [hset, hwsp_l]; omega
        c0_hsteps_nogrp
        refine wp_join_state1 (t := i32) (α := BitVec 32 × List (BitVec 32)) (fun st => st.1)
          (fun ⟨nc1, ws1C⟩ mC =>
            nc1.toNat ≤ init_lits.toNat ∧ ws1C.length = 2 * c.max_vars ∧
            (∀ i < nc1.toNat, (ws1C[i]?.getD 0#32).toNat < init_lits.toNat) ∧
            (FullMem c (mkSt arB lmA wsp ws1C qlB) ⋆ R) mC)
          (fun _ ⟨nc1, ws1C⟩ mC ⟨hnc1, hws1C_l, hcntdC, hmC⟩ => ?_)
          (fun Jc1 hJc1 => ?_)
        · clear hmB
          dsimp only [mkSt] at hmC; c0_hfast
          · exact hJupd ⟨nq1, nc1, nn1, arB, lmA, _, ws1C, qlB⟩ m
              ⟨hnc1, by simp [hwsp_l], hws1C_l, hbvaqB, hlm4B, hwB, hcntdC, hm⟩
          · exact hJupd ⟨nq1, nc1, nn1, arB, lmA, wsp, ws1C, qlB⟩ mC
              ⟨hnc1, hwsp_l, hws1C_l, hbvaqB, hlm4B, hwB, hcntdC, hmC⟩
        · c0_hfast
          · dsimp only at hm
            have hnc1_n : (ncp + 1#32).toNat = ncp.toNat + 1 := by simp only [bv_c0] at *; omega
            refine hJc1 ⟨ncp + 1#32, _⟩ m ⟨by rw [hnc1_n]; omega,
              by simp [hws1p_l], fun i hi => ?_, hm⟩
            rw [hnc1_n] at hi
            by_cases hie : i = ncp.toNat
            · subst hie
              rw [hset, List.getElem?_set_self (by rw [hws1p_l]; omega), Option.getD_some]
              exact hcand_il
            · rw [hset, List.getElem?_set_ne (Ne.symm hie)]; exact hcntdp i (by omega)
          · exact hJc1 ⟨ncp, ws1p⟩ mB ⟨hncp_le, hws1p_l, hcntdp, hmB⟩
          · exact hJc1 ⟨ncp, ws1p⟩ mB ⟨hncp_le, hws1p_l, hcntdp, hmB⟩
      · c0_hsplit
        · have hnq_lt : nqlp.toNat < c.max_vars := by simp only [bv_c0] at *; omega
          have hnq1 : (nqlp + 1#32).toNat = nqlp.toNat + 1 := by simp only [bv_c0]; omega
          have hnq_ql : (BitVec.setWidth 64 nqlp).toNat < qlA.length := by rw [hset, hqlA_l]; omega
          have hdr_ar : (BitVec.setWidth 64 dr).toNat < arp.length := by rw [hset]; omega
          c0_hfast
          have ⟨hbvaq_next, hlm4_next, hw_next⟩ :=
            fid_scan_cands_stepB_inv hcl hw hwp hl0 hbvaqA hlm4A hnq_lt hdr_ref (by omega) hdr_nbvaq
          simp only [hset] at hm
          exact hJb ⟨nqlp + 1#32, _, _⟩ m ⟨by rw [hnq1]; exact hbvaq_next, hlm4_next, hw_next, hm⟩
        · c0_hfast; exact hJb ⟨nqlp, arp, qlA⟩ mA ⟨hbvaqA, hlm4A, hwp, hmA⟩
    · c0_hsplit
      · have hnn_lt : nnoup.toNat < c.max_vars := by simp only [bv_c0] at *; omega
        have hnn1 : (nnoup + 1#32).toNat = nnoup.toNat + 1 := by simp only [bv_c0]; omega
        have hmxnn : (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64 nnoup).toNat =
            c.max_vars + nnoup.toNat := by simp only [bv_c0]; omega
        have hmxnn_ql : (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64 nnoup).toNat <
            qlp.length := by rw [hmxnn, hqlp_l]; omega
        have hcand_lm : (BitVec.setWidth 64 cand).toNat < lmp.length := by rw [hset, hlmp_l]; omega
        c0_hfast
        simp only [hmxnn] at hm; simp only [hset] at hm
        try simp only [bv8_trunc_or_4] at hm
        try simp only [bv8_trunc_or_w] at hm
        exact hJa ⟨nnoup + 1#32, _, _⟩ _
          ⟨fidScanArBvaqInv_set_ql_hi hbvaqp (by omega) cand,
           by rw [hnn1]; exact fidLmBit4Inv_push hqlp_l hlm4p hnn_lt hcand_lt, hm⟩
      · c0_hfast; exact hJa ⟨nnoup, lmp, qlp⟩ mlm ⟨hbvaqp, hlm4p, hmlm⟩
  all_goals
    exact hJupd ⟨nqlp, ncp, nnoup, arp, lmp, wsp, ws1p, qlp⟩ mlm
      ⟨hncp_le, hwsp_l, hws1p_l, hbvaqp, hlm4p, hwp, hcntdp, hmlm⟩
private theorem fid_scan_cands_mp_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {row_off cur_qn : Val i32} {init_lits : Val i64}
    {Jq : Cont [i32, i32, i32]} {nql ncntd qi qw csz min_l min_d fc jf : Val i32}
    {J : Cont [i32, i32]} {Jm : Cont [i32, i32, i32, i32]} {Jscan : Cont [i32, i32, i32]}
    {ar ws ws1 ws2 : List (BitVec 32)} {lm1 : List (BitVec 8)} {mf : Mem 64}
    (hcl : s.core.LengthsOk c) (_hsc : s.scratch.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) (hdw : DenseWatchesInv F_cur s.core)
    (hl0 : s.core.cur_level = 0) (hil_le : init_lits.toNat ≤ 2 * s.core.cur_vars)
    (hnc_le : ncntd.toNat ≤ init_lits.toNat)
    (hws_l : ws.length = 2 * c.max_vars) (hws1_l : ws1.length = 2 * c.max_vars)
    (hbvaq : FidScanArBvaqInv c s ar ws2 0 nql.toNat)
    (hw_ar : FullWitnessInv c F0 F_cur { s.core with arena := ar })
    (hcntd_ok : ∀ i < ncntd.toNat, (ws1[i]?.getD 0#32).toNat < init_lits.toNat)
    (hlm1_l : lm1.length = 2 * c.max_vars)
    (hlm1_b2 : ∀ l < 2 * c.max_vars, (lm1[l]?.getD 0#8 &&& 4#8) = 0#8)
    (hmin_ok : min_l ≠ 0xFFFFFFFF#32 →
      min_l.toNat < 2 * s.core.cur_vars ∧ min_d.toNat = fullWatchSizeCore s.core min_l.toNat)
    (hmf : (FullMem c (FullState.mk { s.core with arena := ar, lit_mark := lm1 }
      { s.scratch with wsort := ws, work_stk1 := ws1, work_stk2 := ws2 }) ⋆ R) mf)
    (hJscan : ∀ nql2 nc2 jf2 ar2 ws2' ws12 ql2 mf2,
      nc2.toNat ≤ init_lits.toNat ∧ ws2'.length = 2 * c.max_vars ∧
      ws12.length = 2 * c.max_vars ∧ FidScanArBvaqInv c s ar2 ql2 0 nql2.toNat ∧
      FullWitnessInv c F0 F_cur { s.core with arena := ar2 } ∧
      (∀ i < nc2.toNat, (ws12[i]?.getD 0#32).toNat < init_lits.toNat) ∧
      (FullMem c (FullState.mk { s.core with arena := ar2, lit_mark := lm1 }
        { s.scratch with wsort := ws2', work_stk1 := ws12, work_stk2 := ql2 }) ⋆ R) mf2 →
      Jscan (nql2, nc2, jf2, ()) mf2) :
    wp Γ Q X (fidScanCandsMpExpr c.hdr row_off cur_qn init_lits
      c.pVals c.pWvec c.pWstk c.pArena c.pLitMark c.pScratchBuf c.pWsort
      c.pWorkStk1 c.pFlags c.pWorkStk2 Jq nql ncntd qi qw J csz Jm min_l min_d fc jf Jscan)
      mf := by
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena
  unfold dimacsBound at hmx hwcap har_b
  have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len; have hws_len := hcl.wstk_len_arr
  have hal_le := hcl.arena_len_le; have hwlen_le := hcl.wlen_le
  have hvals_len := hcl.vals_len; have hfl_len := hcl.flags_len
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
  let mkSt (ar : List (BitVec 32)) (lm : List (BitVec 8)) (ws ws1 ws2 : List (BitVec 32)) :
      FullState :=
    { core := { s.core with arena := ar, lit_mark := lm }
      scratch := { s.scratch with wsort := ws, work_stk1 := ws1, work_stk2 := ws2 } }
  dsimp only [fidScanCandsMpExpr, eLet64, eLet32, eLetBool, eLoad64, eLoad32, eThen, eElse,
    eGrp0_3, eGrp0_4, eGrpBody_2, eGrpBody_3, full_bva_scan_cands_fid_body]
  c0_hfast
  · have hmin_ne : min_l ≠ 0xFFFFFFFF#32 := by assumption
    obtain ⟨hml_lt, hmd_eq⟩ := hmin_ok hmin_ne
    have hml_bd := hdw.layout.bounds min_l.toNat hml_lt
    have hml_sl := hdw.slices min_l.toNat hml_lt
    have h2ml_n : (BitVec.setWidth 64 min_l <<< (1 : Nat)).toNat = 2 * min_l.toNat := by
      simp only [bv_c0]; omega
    have h2ml_mod : 2 * min_l.toNat % 2 ^ 64 = 2 * min_l.toNat := Nat.mod_eq_of_lt (by omega)
    have hmoff_eq : (s.core.wvec[2 * min_l.toNat]'(by omega)).toNat =
        fullWatchOffCore s.core min_l.toNat := by
      unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    let moff0 := fullWatchOffCore s.core min_l.toNat
    let msz0 := fullWatchSizeCore s.core min_l.toNat
    c0_hsteps_nogrp
    refine wp_join_state (α := BitVec 32 × BitVec 32 × BitVec 64 × BitVec 32 ×
        List (BitVec 32) × List (BitVec 8) × List (BitVec 32) × List (BitVec 32) ×
        List (BitVec 32))
      (fun ⟨nql2, nc2, mp2, nnou2, _, _, _, _, _⟩ => (nql2, nc2, mp2, nnou2, ()))
      (fun ⟨nql2, nc2, _, nnou2, ar2, lm2, ws2', ws12, ql2⟩ mmp =>
        nc2.toNat ≤ init_lits.toNat ∧ ws2'.length = 2 * c.max_vars ∧
        ws12.length = 2 * c.max_vars ∧ FidScanArBvaqInv c s ar2 ql2 0 nql2.toNat ∧
        FidLmBit4Inv c lm1 ql2 0 nnou2.toNat lm2 ∧
        FullWitnessInv c F0 F_cur { s.core with arena := ar2 } ∧
        (∀ i < nc2.toNat, (ws12[i]?.getD 0#32).toNat < init_lits.toNat) ∧
        (FullMem c (mkSt ar2 lm2 ws2' ws12 ql2) ⋆ R) mmp)
      (fun _ ⟨nql2, nc2, _mp2, nnou2, ar2, lm2, ws2', ws12, ql2⟩ mmp
          ⟨hnc2, hws2'_l, hws12_l, hbvaq2, hlm4_2, hw2, hcntd2, hmmp⟩ => ?_)
      (fun Jmp hJmp => ?_)
    · clear hmf
      dsimp only [mkSt] at hmmp
      have hql2_l := hbvaq2.2.1
      refine wp_loop_inv
        (fun (j, ()) mj4 => ∃ lmj4,
          j.toNat ≤ nnou2.toNat ∧ FidLmBit4Inv c lm1 ql2 j.toNat nnou2.toNat lmj4 ∧
          (FullMem c (mkSt ar2 lmj4 ws2' ws12 ql2) ⋆ R) mj4)
        (fun (j, ()) _ => nnou2.toNat - j.toNat)
        (fun Jc4 hJc4 => by
          c0_hfast; exact hJc4 (0#32, ()) mmp ⟨lm2, Nat.zero_le _, hlm4_2, hmmp⟩)
        (fun Jc4 (j, ()) mj4 ⟨lmj4, hj4_le, hlmj4, hmj4⟩ ihc4 => ?_)
      clear hmmp; dsimp only [mkSt] at hmj4
      have hlmj4_l := hlmj4.1; have hnn2_le := hlmj4.2.1
      c0_hsplit
      · have hj4_lt : j.toNat < nnou2.toNat := by assumption
        have hj4_1 : (j + 1#32).toNat = j.toNat + 1 := by simp only [bv_c0]; omega
        have hmxj : (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64 j).toNat =
            c.max_vars + j.toNat := by simp only [bv_c0]; omega
        have hmxj_ql : (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64 j).toNat < ql2.length := by
          rw [hmxj, hql2_l]; omega
        have ⟨hcl_lt, hstep4⟩ := fidLmBit4Inv_clear_step hlm1_l hql2_l hlm1_b2 hlmj4 hj4_lt
        have hcl_lm : (BitVec.setWidth 64 (ql2[(BitVec.ofNat 64 c.max_vars +
            BitVec.setWidth 64 j).toNat]'hmxj_ql)).toNat < lmj4.length := by
          simp only [hmxj, hset]; omega
        c0_hfast
        simp only [hmxj] at hm; simp only [hset] at hm
        try simp only [bv8_trunc_and_fb] at hm
        try simp only [bv8_trunc_and_w] at hm
        exact ihc4 (j + 1#32, ()) m (by dsimp only; rw [hj4_1]; omega)
          ⟨_, by rw [hj4_1]; omega, by rw [hj4_1]; exact hstep4, hm⟩
      · have hj4_eq : j.toNat = nnou2.toNat := by omega
        rw [hj4_eq] at hlmj4
        have hlm_eq1 : lmj4 = lm1 := fidLmBit4Inv_done hlm1_l hlmj4; rw [hlm_eq1] at hmj4
        c0_hfast
        exact hJscan nql2 nc2 j ar2 ws2' ws12 ql2 mj4
          ⟨hnc2, hws2'_l, hws12_l, hbvaq2, hw2, hcntd2, hmj4⟩
    · refine wp_loop_inv
        (fun (nqlp, ncp, mp, nnoup, ()) mlm => ∃ arp lmp wsp ws1p qlp,
          moff0 ≤ mp.toNat ∧ mp.toNat ≤ moff0 + msz0 ∧ ncp.toNat ≤ init_lits.toNat ∧
          wsp.length = 2 * c.max_vars ∧ ws1p.length = 2 * c.max_vars ∧
          FidScanArBvaqInv c s arp qlp 0 nqlp.toNat ∧ FidLmBit4Inv c lm1 qlp 0 nnoup.toNat lmp ∧
          FullWitnessInv c F0 F_cur { s.core with arena := arp } ∧
          DenseWatchSliceOk F_cur s.core min_l.toNat mp.toNat (moff0 + msz0 - mp.toNat) ∧
          (∀ i < ncp.toNat, (ws1p[i]?.getD 0#32).toNat < init_lits.toNat) ∧
          (FullMem c (mkSt arp lmp wsp ws1p qlp) ⋆ R) mlm)
        (fun (_, _, mp, _, _) _ => moff0 + msz0 - mp.toNat)
        (fun JmpL hJmpL => by
          c0_hfast
          have h1 : (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 min_l <<<
              (1 : Nat)).toNat]'(by rw [h2ml_n]; omega))).toNat = moff0 := by
            simp only [h2ml_n, hset, hmoff_eq]; rfl
          dsimp only; exact hJmpL (nql, ncntd, _, 0#32, ()) mf
            ⟨ar, lm1, ws, ws1, ws2, by rw [h1]; exact Nat.le_refl _, by rw [h1]; omega,
             hnc_le, hws_l, hws1_l, hbvaq, fidLmBit4Inv_init hlm1_l, hw_ar,
             by simpa only [h1, Nat.add_sub_cancel_left] using hml_sl, hcntd_ok, hmf⟩)
        (fun JmpL (nqlp, ncp, mp, nnoup, ()) mlm
            ⟨arp, lmp, wsp, ws1p, qlp, hmp_ge, hmp_le, hncp_le, hwsp_l, hws1p_l, hbvaqp,
             hlm4p, hwp, hrem, hcntdp, hmlm⟩ ihmp => ?_)
      clear hmf; dsimp only [mkSt] at hmlm
      have harp_l := hbvaqp.1; have hqlp_l := hbvaqp.2.1; have hnqlp_le := hbvaqp.2.2.1
      have hlmp_l := hlm4p.1; have hnnoup_le := hlm4p.2.1
      have hm_end_mod : ((s.core.wvec[2 * min_l.toNat % 2 ^ 64]'(by
          rw [h2ml_mod]; omega)).toNat + min_d.toNat) % 2 ^ 64 = moff0 + msz0 := by
        simp only [h2ml_mod, hmoff_eq, hmd_eq]; exact Nat.mod_eq_of_lt (by omega)
      c0_hsplit
      · have hmp_lt : mp.toNat < moff0 + msz0 := by rw [← hm_end_mod]; assumption
        have hmp_ws : mp.toNat < s.core.wstk.length := by omega
        have hmp1_n : (mp + 1#64).toNat = mp.toNat + 1 := by simp only [bv_c0]; omega
        c0_hfast
        · have ⟨_, _, hrem_next⟩ :=
            FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hmp_ws (by assumption)
          exact ihmp (nqlp, ncp, mp + 1#64, nnoup, ()) mlm (by dsimp only; rw [hmp1_n]; omega)
            ⟨arp, lmp, wsp, ws1p, qlp, by rw [hmp1_n]; omega, by rw [hmp1_n]; omega,
             hncp_le, hwsp_l, hws1p_l, hbvaqp, hlm4p, hwp,
             by rw [hmp1_n, show moff0 + msz0 - (mp.toNat + 1) =
                  moff0 + msz0 - mp.toNat - 1 by omega]; exact hrem_next,
             hcntdp, hmlm⟩
        · exact hJmp ⟨nqlp, ncp, mp + 1#64, nnoup, arp, lmp, wsp, ws1p, qlp⟩ mlm
            ⟨hncp_le, hwsp_l, hws1p_l, hbvaqp, hlm4p, hwp, hcntdp, hmlm⟩
        · have ⟨_, hrem_next⟩ :=
            FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hmp_ws (by assumption)
          have hmp2_n : (mp + 1#64 + 1#64).toNat = mp.toNat + 2 := by simp only [bv_c0]; omega
          exact ihmp (nqlp, ncp, mp + 1#64 + 1#64, nnoup, ()) mlm
            (by dsimp only; rw [hmp2_n]; omega)
            ⟨arp, lmp, wsp, ws1p, qlp, by rw [hmp2_n]; omega, by rw [hmp2_n]; omega,
             hncp_le, hwsp_l, hws1p_l, hbvaqp, hlm4p, hwp,
             by rw [hmp2_n, show moff0 + msz0 - (mp.toNat + 2) =
                  moff0 + msz0 - mp.toNat - 2 by omega]; exact hrem_next,
             hcntdp, hmlm⟩
        · have ⟨h2le, hrem_next⟩ :=
            FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hmp_ws (by assumption)
          have hmp1_ws : mp.toNat + 1 < s.core.wstk.length := by omega
          have hmp1_mod : (mp.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = mp.toNat + 1 := by
            rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
          have ⟨_, hdr_ref, _⟩ :=
            FullBvaFwdHelpers.fwd_slice_occ_info hrem (by omega) hmp_ws hmp1_ws (by assumption)
          have hdr_wf := hw.arena.refs_wf _ hdr_ref
          have hmp2_n : (mp + 1#64 + 1#64).toNat = mp.toNat + 2 := by simp only [bv_c0]; omega
          let dr := s.core.wstk[mp.toNat + 1]'hmp1_ws
          have hdr_lt_ar : dr.toNat + 3 ≤ arp.length := by
            dsimp only [dr]; have := hdr_wf.1; have := hcl.arena_len_le; omega
          have hdr_eq : s.core.wstk[(mp + 1#64).toNat]'(by rw [hmp1_n]; exact hmp1_ws) = dr := by
            dsimp only [dr]; simp only [hmp1_n]
          have hdr_mod : s.core.wstk[(mp.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(
              by rw [hmp1_mod]; exact hmp1_ws) = dr := by dsimp only [dr]; simp only [hmp1_mod]
          have hdr2_n : (BitVec.setWidth 64 dr + 2).toNat = dr.toNat + 2 := by
            change (BitVec.setWidth 64 dr + 2#64).toNat = _; simp only [bv_c0]; omega
          have hdr0_ar : (BitVec.setWidth 64 (s.core.wstk[(mp.toNat +
              BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                rw [hmp1_mod]; exact hmp1_ws))).toNat < arp.length := by rw [hdr_mod, hset]; omega
          have hdr2_ar : (BitVec.setWidth 64 (s.core.wstk[(mp.toNat +
              BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                rw [hmp1_mod]; exact hmp1_ws)) + 2).toNat < arp.length := by
            rw [hdr_mod, hdr2_n]; omega
          have hdr0_ar' : (BitVec.setWidth 64 (s.core.wstk[(mp + 1#64).toNat]'(by
              rw [hmp1_n]; exact hmp1_ws))).toNat < arp.length := by rw [hdr_eq, hset]; omega
          have hdr2_ar' : (BitVec.setWidth 64 (s.core.wstk[(mp + 1#64).toNat]'(by
              rw [hmp1_n]; exact hmp1_ws)) + 2).toNat < arp.length := by rw [hdr_eq, hdr2_n]; omega
          c0_hsteps_nogrp
          · exact ihmp (nqlp, ncp, mp + 1#64 + 1#64, nnoup, ()) mlm
              (by dsimp only; rw [hmp2_n]; omega)
              ⟨arp, lmp, wsp, ws1p, qlp, by rw [hmp2_n]; omega, by rw [hmp2_n]; omega,
               hncp_le, hwsp_l, hws1p_l, hbvaqp, hlm4p, hwp,
               by rw [hmp2_n, show moff0 + msz0 - (mp.toNat + 2) =
                    moff0 + msz0 - mp.toNat - 2 by omega]; exact hrem_next,
               hcntdp, hmlm⟩
          · exact ihmp (nqlp, ncp, mp + 1#64 + 1#64, nnoup, ()) mlm
              (by dsimp only; rw [hmp2_n]; omega)
              ⟨arp, lmp, wsp, ws1p, qlp, by rw [hmp2_n]; omega, by rw [hmp2_n]; omega,
               hncp_le, hwsp_l, hws1p_l, hbvaqp, hlm4p, hwp,
               by rw [hmp2_n, show moff0 + msz0 - (mp.toNat + 2) =
                    moff0 + msz0 - mp.toNat - 2 by omega]; exact hrem_next,
               hcntdp, hmlm⟩
          · have hdr_0248 : (arp[dr.toNat]'(by omega) &&& 0x02480000#32) = 0#32 := by
              have h1 : (arp[(BitVec.setWidth 64
                  (s.core.wstk[(mp.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                    rw [hmp1_mod]; exact hmp1_ws))).toNat]'(by
                      rw [hdr_mod, hset]; omega) &&& (38273024 : BitVec 32)) = 0#32 := by
                simpa only [← hdr_mod] using (by assumption : _)
              simp only [hdr_mod] at h1
              simpa only [hset, show (38273024 : BitVec 32) = 0x02480000#32 from rfl] using h1
            have hdr_sz_ar : arp[dr.toNat + 2]'(by omega) = csz := by
              have hdr2_mod : (dr.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = dr.toNat + 2 :=
                by rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
              have h2 : arp[(dr.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                  rw [hdr2_mod]; omega) = csz := by
                simpa only [← hdr_mod] using (by assumption : _)
              simpa only [hdr2_mod] using h2
            have ⟨hdr_nbvaq, hdr_ng_s, hdr_sz_eq⟩ :=
              fid_scan_cands_dr_info hcl hw hbvaqp hdr_ref hdr_lt_ar hdr_0248 hdr_sz_ar
            c0_hsteps_nogrp
            refine wp_join_state (α := BitVec 32 × Bool × BitVec 32)
              (fun ⟨cand, ok, djf⟩ => (cand, ok, djf, ()))
              (fun _ mdj => mdj = mlm)
              (fun _ ⟨cand, ok, _djf⟩ mdj hmdj => ?_)
              (fun Jdj hJdj => ?_)
            · rcases hmdj with rfl
              dsimp only
              have hupd := fid_scan_cands_upd_wp (Γ := Γ) (Q := Q) (X := X) (row_off := row_off)
                (cur_qn := cur_qn) (Jq := Jq) (nql := nql) (ncntd := ncntd) (qi := qi) (qw := qw)
                (J := J) (csz := csz) (Jm := Jm) (min_l := min_l) (min_d := min_d) (fc := fc)
                (jf := jf) (Jscan := Jscan) (Jmp := fun _ _ => True) (JmpL := JmpL) (mp := mp)
                (mp2 := mp + 1#64 + 1#64)
                (dr := s.core.wstk[(mp + 1#64).toNat]'(by rw [hmp1_n]; exact hmp1_ws))
                (cand := cand) (ok := ok) (djf := _djf) (Jdj := fun _ _ => True)
                hcl hw hl0 hil_le hncp_le hwsp_l hws1p_l hbvaqp hlm4p hwp hcntdp
                (by rw [hdr_eq]; exact hdr_ref) (by rw [hdr_eq]; exact hdr_lt_ar)
                (by simpa only [hdr_eq] using hdr_nbvaq) hmlm
                (fun nql' nc' nnou' ar' lm' ws' ws1' ql' m'
                    ⟨hnc', hws', hws1', hbvaq', hlm4', hw', hcntd', hm'⟩ =>
                  ihmp (nql', nc', mp + 1#64 + 1#64, nnou', ()) m'
                    (by dsimp only; rw [hmp2_n]; omega)
                    ⟨ar', lm', ws', ws1', ql', by rw [hmp2_n]; omega, by rw [hmp2_n]; omega,
                     hnc', hws', hws1', hbvaq', hlm4', hw',
                     by rw [hmp2_n, show moff0 + msz0 - (mp.toNat + 2) =
                          moff0 + msz0 - mp.toNat - 2 by omega]; exact hrem_next,
                     hcntd', hm'⟩)
              dsimp only [fidScanCandsUpdExpr, fidScanCandsMpExpr, eLet64, eLet32, eLetBool,
                eLoad64, eLoad32, eThen, eElse, eGrp0_3, eGrp0_4, eGrpBody_2, eGrpBody_3,
                eGrpBody_mp, eGrp0_mp, eGrp0_dj, eSkip, full_bva_scan_cands_fid_body] at hupd
              exact hupd
            · refine wp_loop_inv
                (fun (cand, dj, ()) mdj => mdj = mlm ∧ dj.toNat ≤ csz.toNat)
                (fun (_, dj, _) _ => csz.toNat - dj.toNat)
                (fun Jd hJd => by
                  c0_hfast; exact hJd (0xFFFFFFFF#32, 0#32, ()) mlm ⟨rfl, Nat.zero_le _⟩)
                (fun Jd (cand, dj, ()) mdj ⟨hmdj, hdj_le⟩ ihd => ?_)
              rcases hmdj with rfl
              c0_hsplit
              · have hdj_lt : dj.toNat < csz.toNat := by assumption
                have hdj1 : (dj + 1#32).toNat = dj.toNat + 1 := by simp only [bv_c0]; omega
                have har_len := hcl.arena_len_arr
                have hdr_end : dr.toNat + 3 + csz.toNat ≤ s.core.arena_len := by
                  dsimp only [dr]; have := hdr_wf.2.2.1; have := hdr_wf.2.2.2.1; omega
                have hdj_sz : dj.toNat < fullArenaClauseSizeCore s.core dr.toNat := by
                  rw [hdr_sz_eq]; exact hdj_lt
                have hdrj_n : (BitVec.setWidth 64 dr + 3 + BitVec.setWidth 64 dj).toNat =
                    dr.toNat + 3 + dj.toNat := by
                  change (BitVec.setWidth 64 dr + 3#64 + BitVec.setWidth 64 dj).toNat = _
                  simp only [bv_c0]; omega
                have hdl_eq : arp[dr.toNat + 3 + dj.toNat]'(by omega) =
                    s.core.arena[dr.toNat + 3 + dj.toNat]'(by omega) := by
                  have h1 := (fid_scan_cands_ar_lits_eq hcl hw hbvaqp hdr_ref).2 dj.toNat hdj_sz
                  rw [List.getElem?_eq_getElem (by omega),
                    List.getElem?_eq_getElem (by omega)] at h1
                  exact Option.some.inj h1
                have hdl_lt : (arp[dr.toNat + 3 + dj.toNat]'(by omega)).toNat <
                    2 * s.core.cur_vars := by
                  rw [hdl_eq]
                  exact hw.arena.lits_lt dr.toNat hdr_ref hdr_ng_s _ (List.mem_of_getElem?
                    (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem hdj_sz (by omega)))
                have hdrj_ar : (BitVec.setWidth 64 (s.core.wstk[(mp.toNat +
                    BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                      rw [hmp1_mod]; exact hmp1_ws)) + 3 + BitVec.setWidth 64 dj).toNat <
                    arp.length := by rw [hdr_mod, hdrj_n, harp_l]; dsimp only [dr]; omega
                have hdl_lm : (BitVec.setWidth 64 (arp[(BitVec.setWidth 64
                    (s.core.wstk[(mp.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                      rw [hmp1_mod]; exact hmp1_ws)) + 3 +
                    BitVec.setWidth 64 dj).toNat]'hdrj_ar)).toNat < lmp.length := by
                  simp only [hdr_mod]; simp only [hdrj_n, hset]; omega
                have hdrj_ar' : (BitVec.setWidth 64 (s.core.wstk[(mp + 1#64).toNat]'(by
                    rw [hmp1_n]; exact hmp1_ws)) + 3 + BitVec.setWidth 64 dj).toNat <
                    arp.length := by rw [hdr_eq, hdrj_n, harp_l]; dsimp only [dr]; omega
                have hdl_lm' : (BitVec.setWidth 64 (arp[(BitVec.setWidth 64
                    (s.core.wstk[(mp + 1#64).toNat]'(by rw [hmp1_n]; exact hmp1_ws)) + 3 +
                    BitVec.setWidth 64 dj).toNat]'hdrj_ar')).toNat < lmp.length := by
                  simp only [hdr_eq]; simp only [hdrj_n, hset]; omega
                c0_hfast
                · exact hJdj ⟨cand, false, dj⟩ mdj rfl
                · exact hJdj ⟨cand, false, dj⟩ mdj rfl
                · exact ihd (_, dj + 1#32, ()) mdj (by dsimp only; rw [hdj1]; omega)
                    ⟨rfl, by rw [hdj1]; omega⟩
                · exact ihd (cand, dj + 1#32, ()) mdj (by dsimp only; rw [hdj1]; omega)
                    ⟨rfl, by rw [hdj1]; omega⟩
              · c0_hfast; exact hJdj ⟨cand, true, dj⟩ mdj rfl
      · c0_hfast
        exact hJmp ⟨nqlp, ncp, mp, nnoup, arp, lmp, wsp, ws1p, qlp⟩ mlm
          ⟨hncp_le, hwsp_l, hws1p_l, hbvaqp, hlm4p, hwp, hcntdp, hmlm⟩
  all_goals
    exact hJscan nql ncntd jf ar ws ws1 ws2 mf
      ⟨hnc_le, hws_l, hws1_l, hbvaq, hw_ar, hcntd_ok, hmf⟩

/-- Parametric `Func.wp` proof for `full_bva_scan_cands_fid`, certifying canonical
`FullM4Bva.m4BvaScanCandsSpec` using bit-25 (`PH_BVA_Q`) candidate suppression. -/
theorem full_bva_scan_cands_fid_wp (Γ : Env) :
    ∀ args m Q X, m4BvaScanCandsSpec args m Q X →
      Func.wp Γ full_bva_scan_cands_fid_body args m Q X := by
  rintro ⟨h, row_off, cur_qn, init_lits, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hslen, hw, hnodup, hext, hl0, hdm, hil_le, hlm_clr, hrow_bd, hqn_le,
     hrow_ok, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap har_b hscr_b
  have hcl := hslen.core_ok; have hsc := hslen.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len; have hws_len := hcl.wstk_len_arr
  have har_len := hcl.arena_len_arr; have hal_le := hcl.arena_len_le; have hwlen_le := hcl.wlen_le
  have hlm_len := hcl.lit_mark_len; have hvals_len := hcl.vals_len; have hfl_len := hcl.flags_len
  have hsb_len := hsc.scratch_buf_len; have hwsort_len := hsc.wsort_len
  have hws1_len := hsc.work_stk1_len; have hws2_len := hsc.work_stk2_len
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
  have hdw : DenseWatchesInv F_cur s.core := by
    have h1 := hw.watches; unfold ModeWatchesInv at h1; rwa [ite_eq_right hdm] at h1
  let mkSt (ar : List (BitVec 32)) (lm : List (BitVec 8)) (ws ws1 ws2 : List (BitVec 32)) :
      FullState :=
    { core := { s.core with arena := ar, lit_mark := lm }
      scratch := { s.scratch with wsort := ws, work_stk1 := ws1, work_stk2 := ws2 } }
  c0_hsteps
  refine wp_loop_inv
    (fun (nql, ncntd, qi, ()) ml => ∃ ar ws ws1 ws2,
      qi.toNat ≤ cur_qn.toNat ∧ ncntd.toNat ≤ init_lits.toNat ∧
      ws.length = 2 * c.max_vars ∧ ws1.length = 2 * c.max_vars ∧
      FidScanArBvaqInv c s ar ws2 0 nql.toNat ∧
      FullWitnessInv c F0 F_cur { s.core with arena := ar } ∧
      (∀ i < ncntd.toNat, (ws1[i]?.getD 0#32).toNat < init_lits.toNat) ∧
      (FullMem c (mkSt ar s.core.lit_mark ws ws1 ws2) ⋆ R) ml)
    (fun (_, _, qi, _) _ => cur_qn.toNat - qi.toNat)
    (fun Jq hJq => by
      c0_hsteps; exact hJq (0#32, 0#32, 0#32, ()) m
        ⟨s.core.arena, s.scratch.wsort, s.scratch.work_stk1, s.scratch.work_stk2,
         Nat.zero_le _, Nat.zero_le _, hwsort_len, hws1_len, fidScanArBvaqInv_init hslen,
         hw, fun _ h => by simp only [bv_c0] at h; omega, hm⟩)
    (fun Jq (nql, ncntd, qi, ()) ml
        ⟨ar, ws, ws1, ws2, hqi_le, hnc_le, hws_l, hws1_l, hbvaq, hw_ar, hcntd_ok, hml⟩ ihq => ?_)
  dsimp only [mkSt] at hml
  have har_l := hbvaq.1; have hws2_l := hbvaq.2.1; have hnql_le := hbvaq.2.2.1
  c0_hsteps_nogrp
  · have hqi_lt : qi.toNat < cur_qn.toNat := by c0_bound
    have hqi1 : (qi + 1#32).toNat = qi.toNat + 1 := by c0_bound
    have hrqi : (row_off + qi).toNat = row_off.toNat + qi.toNat := by c0_bound
    have hqw_ok := hrow_ok qi.toNat hqi_lt
    let qw := s.scratch.scratch_buf[row_off.toNat + qi.toNat]'(by omega)
    have hrqi_mod : (row_off.toNat + qi.toNat) % 2 ^ 32 = row_off.toNat + qi.toNat :=
      Nat.mod_eq_of_lt (by omega)
    have hqw_mod : s.scratch.scratch_buf[(row_off.toNat + qi.toNat) % 2 ^ 32]'(by
        rw [hrqi_mod]; omega) = qw := by dsimp only [qw]; simp only [hrqi_mod]
    have hqw_getD : s.scratch.scratch_buf[row_off.toNat + qi.toNat]?.getD 0#32 = qw := by
      dsimp only [qw]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [hqw_getD] at hqw_ok; c0_hstep; c0_hsplit
    · have hbin_ne : (qw &&& 0x80000000#32) ≠ 0#32 := by
        have h1 : (s.scratch.scratch_buf[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
          rw [hset, hrqi]; omega) &&& 0x80000000#32) ≠ 0#32 := by assumption
        simpa only [hset, hrqi] using h1
      rw [ite_eq_left hbin_ne] at hqw_ok
      let q := qw &&& 0x7FFFFFFF#32
      have hq_lt : q.toNat < 2 * s.core.cur_vars := hqw_ok
      have h2q_n : (BitVec.setWidth 64 q <<< (1 : Nat)).toNat = 2 * q.toNat := by c0_bound
      have h2q1_n : ((BitVec.setWidth 64 q <<< (1 : Nat)) + 1).toNat = 2 * q.toNat + 1 := by
        change ((BitVec.setWidth 64 q <<< (1 : Nat)) + 1#64).toNat = _; c0_bound
      have hq_bd := hdw.layout.bounds q.toNat hq_lt; have hq_sl := hdw.slices q.toNat hq_lt
      have hoff_eq : (s.core.wvec[2 * q.toNat]'(by omega)).toNat =
          fullWatchOffCore s.core q.toNat := by
        unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hsz_eq : (s.core.wvec[2 * q.toNat + 1]'(by omega)).toNat =
          fullWatchSizeCore s.core q.toNat := by
        unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      let qoff0 := fullWatchOffCore s.core q.toNat
      let qsz0 := fullWatchSizeCore s.core q.toNat
      have hq_eq : s.scratch.scratch_buf[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
          rw [hset, hrqi]; omega) &&& 0x7FFFFFFF#32 = q := by
        dsimp only [q, qw]; simp only [hset, hrqi]
      have hq_mod : s.scratch.scratch_buf[(row_off.toNat + qi.toNat) % 2 ^ 32]'(by
          rw [hrqi_mod]; omega) &&& (2147483647 : BitVec 32) = q := by rw [hqw_mod]; rfl
      have h2q_mod : 2 * q.toNat % 2 ^ 64 = 2 * q.toNat := Nat.mod_eq_of_lt (by omega)
      have h2q_wvec : (BitVec.setWidth 64 (s.scratch.scratch_buf[(BitVec.setWidth 64
          (row_off + qi)).toNat]'(by rw [hset, hrqi]; omega) &&& 0x7FFFFFFF#32) <<<
          (1 : Nat)).toNat < s.core.wvec.length := by rw [hq_eq, h2q_n]; omega
      have h2q1_wvec : ((BitVec.setWidth 64 (s.scratch.scratch_buf[(BitVec.setWidth 64
          (row_off + qi)).toNat]'(by rw [hset, hrqi]; omega) &&& 0x7FFFFFFF#32) <<<
          (1 : Nat)) + 1).toNat < s.core.wvec.length := by rw [hq_eq, h2q1_n]; omega
      c0_hsteps_nogrp
      refine wp_loop_inv
        (fun (nc, qp, ()) mlp => ∃ wsp ws1p,
          qoff0 ≤ qp.toNat ∧ qp.toNat ≤ qoff0 + qsz0 ∧ nc.toNat ≤ init_lits.toNat ∧
          wsp.length = 2 * c.max_vars ∧ ws1p.length = 2 * c.max_vars ∧
          DenseWatchSliceOk F_cur s.core q.toNat qp.toNat (qoff0 + qsz0 - qp.toNat) ∧
          (∀ i < nc.toNat, (ws1p[i]?.getD 0#32).toNat < init_lits.toNat) ∧
          (FullMem c (mkSt ar s.core.lit_mark wsp ws1p ws2) ⋆ R) mlp)
        (fun (_, qp, _) _ => qoff0 + qsz0 - qp.toNat)
        (fun Jp hJp => by
          c0_hfast
          have h1 : (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64
              (s.scratch.scratch_buf[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
                rw [hset, hrqi]; omega) &&& (2147483647 : BitVec 32)) <<< (1 : Nat)).toNat]'(by
              rw [show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl, hq_eq, h2q_n]
              omega))).toNat = qoff0 := by
            simp only [show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl, hq_eq]
            simp only [h2q_n, hset, hoff_eq]; rfl
          dsimp only; exact hJp (ncntd, _, ()) ml ⟨ws, ws1, by rw [h1]; exact Nat.le_refl _,
            by rw [h1]; omega, hnc_le, hws_l, hws1_l,
            by simpa only [h1, Nat.add_sub_cancel_left] using hq_sl, hcntd_ok, hml⟩)
        (fun Jp (nc, qp, ()) mlp
            ⟨wsp, ws1p, hqp_ge, hqp_le, hncp_le, hwsp_l, hws1p_l, hrem, hcntdp, hmlp⟩ ihp => ?_)
      clear hm hml; dsimp only [mkSt] at hmlp
      c0_hsplit
      · have hqp_lt : qp.toNat < qoff0 + qsz0 := by
          have hqend_mod : ((s.core.wvec[2 * q.toNat % 2 ^ 64]'(by rw [h2q_mod]; omega)).toNat +
              (s.core.wvec[(2 * q.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega)).toNat) % 2 ^ 64 =
              qoff0 + qsz0 := by
            simp only [h2q_mod, show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
              Nat.mod_eq_of_lt (by omega : 2 * q.toNat + 1 < 2 ^ 64), hoff_eq, hsz_eq]
            exact Nat.mod_eq_of_lt (by omega)
          rw [← hqend_mod]
          simpa only [← hq_mod] using (by assumption : _)
        have hqp_ws : qp.toNat < s.core.wstk.length := by omega
        have hqp1_n : (qp + 1#64).toNat = qp.toNat + 1 := by simp only [bv_c0]; omega
        c0_hsteps_nogrp; c0_hstep; c0_hsplit
        · have ⟨hc_lt2, _, hrem_next⟩ :=
            FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hqp_ws (by assumption)
          let cand := s.core.wstk[qp.toNat]'hqp_ws &&& 0x7FFFFFFF#32
          have hcand_lt : cand.toNat < 2 * s.core.cur_vars := hc_lt2
          have hcand_shr : (cand >>> (1 : Nat)).toNat < c.max_vars := by
            rw [bv32_lshr1_nat]; omega
          have hcand_ws : (BitVec.setWidth 64 cand).toNat < wsp.length := by
            rw [hset, hwsp_l]; omega
          c0_hsteps_nogrp
          refine wp_join_state1 (t := i32)
            (α := BitVec 32 × List (BitVec 32) × List (BitVec 32)) (fun st => st.1)
            (fun ⟨nc1, wsp1, ws1p1⟩ mf =>
              nc1.toNat ≤ init_lits.toNat ∧ wsp1.length = 2 * c.max_vars ∧
              ws1p1.length = 2 * c.max_vars ∧
              (∀ i < nc1.toNat, (ws1p1[i]?.getD 0#32).toNat < init_lits.toNat) ∧
              (FullMem c (mkSt ar s.core.lit_mark wsp1 ws1p1 ws2) ⋆ R) mf)
            (fun _ ⟨nc1, wsp1, ws1p1⟩ mf ⟨hnc1, hwsp1, hws1p1, hcntd1, hmf⟩ => by
              c0_hfast
              exact ihp (nc1, qp + 1#64, ()) mf (by dsimp only; rw [hqp1_n]; omega)
                ⟨wsp1, ws1p1, by rw [hqp1_n]; omega, by rw [hqp1_n]; omega, hnc1, hwsp1, hws1p1,
                 by rw [hqp1_n, show qoff0 + qsz0 - (qp.toNat + 1) = qoff0 + qsz0 - qp.toNat - 1
                      by omega]; exact hrem_next, hcntd1, hmf⟩)
            (fun Jc hJc => ?_)
          have hil_u32 : init_lits.toNat < 2 ^ 32 := by
            have := c.hmaxv; unfold dimacsBound at *; omega
          c0_hfast
          all_goals
            first
            | exact hJc ⟨nc, wsp, ws1p⟩ mlp ⟨hncp_le, hwsp_l, hws1p_l, hcntdp, hmlp⟩
            | (dsimp only at hm
               have hm' : (FullMem c (mkSt ar s.core.lit_mark _ _ ws2) ⋆ R) m := hm
               refine hJc ⟨_, _, _⟩ m ⟨?_, ?_, ?_, ?_, hm'⟩
               · first
                 | exact hncp_le
                 | (simp only [show (1 : BitVec 32) = 1#32 from rfl, bv_c0] at *; omega)
               · (try simp only [List.length_set]); exact hwsp_l
               · (try simp only [List.length_set]); exact hws1p_l
               · intro i hi
                 first
                 | exact hcntdp i hi
                 | (have hcand_il : (s.core.wstk[qp.toNat]'hqp_ws &&&
                        (2147483647 : BitVec 32)).toNat < init_lits.toNat := by
                      simp only [bv_c0] at *; omega
                    have hnc1 : (nc + (1 : BitVec 32)).toNat = nc.toNat + 1 := by
                      simp only [show (1 : BitVec 32) = 1#32 from rfl, bv_c0] at *; omega
                    rw [hnc1] at hi
                    by_cases hie : i = nc.toNat
                    · subst hie; rw [hset, List.getElem?_set_self (by omega), Option.getD_some]
                      exact hcand_il
                    · rw [hset, List.getElem?_set_ne (Ne.symm hie)]; exact hcntdp i (by omega)))
        · have ⟨h2le, hrem_next⟩ :=
            FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hqp_ws (by assumption)
          have hqp2_n : (qp + 2#64).toNat = qp.toNat + 2 := by simp only [bv_c0]; omega
          c0_hfast
          exact ihp (nc, qp + 2#64, ()) mlp (by dsimp only; rw [hqp2_n]; omega)
            ⟨wsp, ws1p, by rw [hqp2_n]; omega, by rw [hqp2_n]; omega, hncp_le, hwsp_l, hws1p_l,
             by rw [hqp2_n, show qoff0 + qsz0 - (qp.toNat + 2) = qoff0 + qsz0 - qp.toNat - 2
                  by omega]; exact hrem_next, hcntdp, hmlp⟩
      · c0_hfast
        exact ihq (nql, nc, qi + 1#32, ()) mlp (by dsimp only; rw [hqi1]; omega)
          ⟨ar, wsp, ws1p, ws2, by rw [hqi1]; omega, hncp_le, hwsp_l, hws1p_l, hbvaq, hw_ar,
           hcntdp, hmlp⟩
    · have hbin_eq : (qw &&& 0x80000000#32) = 0#32 := by
        have h1 : (s.scratch.scratch_buf[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
          rw [hset, hrqi]; omega) &&& 0x80000000#32) = 0#32 := by assumption
        simpa only [hset, hrqi] using h1
      rw [ite_eq_right (fun h' => h' hbin_eq)] at hqw_ok
      obtain ⟨hqw_ref, hqw_ng⟩ := hqw_ok
      have hqw_wf := hw.arena.refs_wf qw.toNat hqw_ref
      have hqw_sz_s : (s.core.arena[qw.toNat + 2]'(by omega)).toNat =
          fullArenaClauseSizeCore s.core qw.toNat := by
        unfold fullArenaClauseSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have har_lits_eq := fid_scan_cands_ar_lits_eq hcl hw hbvaq hqw_ref
      have hqw_sz_eq : (ar[qw.toNat + 2]'(by omega)).toNat =
          fullArenaClauseSizeCore s.core qw.toNat := by
        have h1 := har_lits_eq.1
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h1
        rw [Option.some.inj h1]; exact hqw_sz_s
      let csz_bv := ar[qw.toNat + 2]'(by omega)
      have hcsz_nat : csz_bv.toNat = fullArenaClauseSizeCore s.core qw.toNat := hqw_sz_eq
      have hqw_eq : s.scratch.scratch_buf[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
          rw [hset, hrqi]; omega) = qw := by dsimp only [qw]; simp only [hset, hrqi]
      have hqw2_n : (BitVec.setWidth 64 qw + 2).toNat = qw.toNat + 2 := by
        change (BitVec.setWidth 64 qw + 2#64).toNat = _; simp only [bv_c0]; omega
      have hqw2_mod : (qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = qw.toNat + 2 := by
        rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
      have hcsz_mod : csz_bv = ar[(qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
          rw [hqw2_mod]; omega) := by dsimp only [csz_bv]; simp only [hqw2_mod]
      have hqw2_ar : (BitVec.setWidth 64 (s.scratch.scratch_buf[(BitVec.setWidth 64
          (row_off + qi)).toNat]'(by rw [hset, hrqi]; omega)) + 2).toNat < ar.length := by
        rw [hqw_eq, hqw2_n, har_l]; have := hqw_wf.1; omega
      c0_hsteps_nogrp
      refine wp_join_state (α := BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × List (BitVec 8))
        (fun ⟨min_l, min_d, fc, jf, _⟩ => (min_l, min_d, fc, jf, ()))
        (fun ⟨min_l, min_d, _, _, lm1⟩ mf =>
          LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 csz_bv.toNat lm1 ∧
          (min_l ≠ 0xFFFFFFFF#32 → min_l.toNat < 2 * s.core.cur_vars ∧
            min_d.toNat = fullWatchSizeCore s.core min_l.toNat) ∧
          (FullMem c (mkSt ar lm1 ws ws1 ws2) ⋆ R) mf)
        (fun _ ⟨min_l, min_d, fc, _jf, lm1⟩ mf ⟨hlm1_inv, hmin_ok, hmf⟩ => ?_)
        (fun Jm hJm => ?_)
      · dsimp only [mkSt] at hmf
        c0_hsteps_nogrp
        refine wp_join_state (α := BitVec 32 × BitVec 32 × BitVec 32 × List (BitVec 32) ×
            List (BitVec 32) × List (BitVec 32) × List (BitVec 32))
          (fun ⟨nql2, nc2, jf2, _, _, _, _⟩ => (nql2, nc2, jf2, ()))
          (fun ⟨nql2, nc2, _, ar2, ws2', ws12, ql2⟩ mf2 =>
            nc2.toNat ≤ init_lits.toNat ∧ ws2'.length = 2 * c.max_vars ∧
            ws12.length = 2 * c.max_vars ∧ FidScanArBvaqInv c s ar2 ql2 0 nql2.toNat ∧
            FullWitnessInv c F0 F_cur { s.core with arena := ar2 } ∧
            (∀ i < nc2.toNat, (ws12[i]?.getD 0#32).toNat < init_lits.toNat) ∧
            (FullMem c (mkSt ar2 lm1 ws2' ws12 ql2) ⋆ R) mf2)
          (fun _ ⟨nql2, nc2, _jf2, ar2, ws2', ws12, ql2⟩ mf2
              ⟨hnc2, hws2'_l, hws12_l, hbvaq2, hw2, hcntd2, hmf2⟩ => ?_)
          (fun Jscan hJscan => ?_)
        · dsimp only [mkSt] at hmf2
          have har2_l := hbvaq2.1
          have har2_lits := (fid_scan_cands_ar_lits_eq hcl hw hbvaq2 hqw_ref).2
          refine wp_loop_inv
            (fun (j, ()) mj => ∃ lmj, j.toNat ≤ csz_bv.toNat ∧
              LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat j.toNat csz_bv.toNat lmj ∧
              (FullMem c (mkSt ar2 lmj ws2' ws12 ql2) ⋆ R) mj)
            (fun (j, ()) _ => csz_bv.toNat - j.toNat)
            (fun Jc2 hJc2 => by
              c0_hfast; exact hJc2 (0#32, ()) mf2 ⟨lm1, Nat.zero_le _, hlm1_inv, hmf2⟩)
            (fun Jc2 (j, ()) mj ⟨lmj, hj_le, hlmj_inv, hmj⟩ ihc2 => ?_)
          clear hm hml hmf hmf2; dsimp only [mkSt] at hmj
          have hlmj_l := hlmj_inv.1
          c0_hsplit
          · have hj_lt : j.toNat < csz_bv.toNat := by
              rw [hcsz_mod]
              simpa only [← hqw_mod] using (by assumption : _)
            have hcj_eq : ar2[qw.toNat + 3 + j.toNat]'(by omega) =
                s.core.arena[qw.toNat + 3 + j.toNat]'(by omega) := by
              have h1 := har2_lits j.toNat (by omega)
              rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h1
              exact Option.some.inj h1
            have hcj_lt : (s.core.arena[qw.toNat + 3 + j.toNat]'(by omega)).toNat <
                2 * s.core.cur_vars :=
              hw.arena.lits_lt qw.toNat hqw_ref hqw_ng _ (List.mem_of_getElem?
                (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (by omega) (by omega)))
            have hj1 : (j + 1#32).toNat = j.toNat + 1 := by simp only [bv_c0]; omega
            have hidx_n : (BitVec.setWidth 64 qw + 3 + BitVec.setWidth 64 j).toNat =
                qw.toNat + 3 + j.toNat := by
              change (BitVec.setWidth 64 qw + 3#64 + BitVec.setWidth 64 j).toNat = _
              simp only [bv_c0]; omega
            have hidx_ar : (BitVec.setWidth 64 (s.scratch.scratch_buf[(BitVec.setWidth 64
                (row_off + qi)).toNat]'(by rw [hset, hrqi]; omega)) + 3 +
                BitVec.setWidth 64 j).toNat < ar2.length := by rw [hqw_eq, hidx_n, har2_l]; omega
            have hcj_lm : (BitVec.setWidth 64 (ar2[(BitVec.setWidth 64
                (s.scratch.scratch_buf[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
                  rw [hset, hrqi]; omega)) + 3 + BitVec.setWidth 64 j).toNat]'hidx_ar)).toNat <
                lmj.length := by simp only [hqw_eq]; simp only [hidx_n, hset, hcj_eq]; omega
            c0_hfast
            simp only [hqw_eq] at hm; simp only [hidx_n, hset] at hm
            try simp only [bv8_trunc_and_fd] at hm
            try simp only [bv8_trunc_and_w] at hm
            have hstep : LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat (j.toNat + 1)
                csz_bv.toNat (lmj.set (ar2[qw.toNat + 3 + j.toNat]'(by omega)).toNat
                  ((lmj[(ar2[qw.toNat + 3 + j.toNat]'(by omega)).toNat]'(by
                    rw [hcj_eq]; omega)) &&& 0xFD#8)) := by
              have h0 := lmBit2Inv_clear_step hlm_len
                (fun l hl => (bv8_bit_zero_of_and_fe (hlm_clr l hl)).1)
                hlmj_inv hj_lt (by omega) (by omega)
              simpa only [← hcj_eq] using h0
            exact ihc2 (j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
              ⟨_, by rw [hj1]; omega, by rw [hj1]; exact hstep, hm⟩
          · have hj_eq : j.toNat = csz_bv.toNat := by
              rw [hcsz_mod] at hj_le ⊢
              have h1 : ¬ j.toNat < (ar[(qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                rw [hqw2_mod]; omega)).toNat := by
                simpa only [← hqw_mod] using (by assumption : _)
              omega
            rw [hj_eq] at hlmj_inv
            have hlm_rest : lmj = s.core.lit_mark := lmBit2Inv_done hlm_len hlmj_inv
            rw [hlm_rest] at hmj; c0_hfast
            exact ihq (nql2, nc2, qi + 1#32, ()) mj (by dsimp only; rw [hqi1]; omega)
              ⟨ar2, ws2', ws12, ql2, by rw [hqi1]; omega, hnc2, hws2'_l, hws12_l, hbvaq2, hw2,
               hcntd2, hmj⟩
        · dsimp only
          have hmp := fid_scan_cands_mp_wp (Γ := Γ) (Q := Q) (X := X) (row_off := row_off)
            (cur_qn := cur_qn) (Jq := Jq) (qi := qi)
            (qw := s.scratch.scratch_buf[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
              rw [hset, hrqi]; omega))
            (J := J)
            (csz := ar[(BitVec.setWidth 64 (s.scratch.scratch_buf[(BitVec.setWidth 64
              (row_off + qi)).toNat]'(by rw [hset, hrqi]; omega)) + 2).toNat]'hqw2_ar)
            (Jm := fun _ _ => True) (fc := fc) (jf := _jf)
            hcl hsc hw hdw hl0 hil_le hnc_le hws_l hws1_l hbvaq hw_ar hcntd_ok
            hlm1_inv.1 (fun l hl => by
              rw [lmBit2Inv_preserves_bit2 hlm1_inv hl]
              exact (bv8_bit_zero_of_and_fe (hlm_clr l hl)).2)
            hmin_ok hmf
            (fun nql2 nc2 jf2 ar2 ws2' ws12 ql2 mf2 h =>
              hJscan ⟨nql2, nc2, jf2, ar2, ws2', ws12, ql2⟩ mf2 h)
          dsimp only [fidScanCandsMpExpr, eLet64, eLet32, eLetBool, eLoad64, eLoad32, eThen, eElse,
            eGrp0_3, eGrp0_4, eGrpBody_2, eGrpBody_3, full_bva_scan_cands_fid_body] at hmp
          exact hmp
      · refine wp_loop_inv
          (fun (min_l, min_d, fc, j, ()) mj => ∃ lmj, j.toNat ≤ csz_bv.toNat ∧
            LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 j.toNat lmj ∧
            (min_l ≠ 0xFFFFFFFF#32 → min_l.toNat < 2 * s.core.cur_vars ∧
              min_d.toNat = fullWatchSizeCore s.core min_l.toNat) ∧
            (FullMem c (mkSt ar lmj ws ws1 ws2) ⋆ R) mj)
          (fun (_, _, _, j, _) _ => csz_bv.toNat - j.toNat)
          (fun JmL hJmL => by
            c0_hfast; exact hJmL (0xFFFFFFFF#32, 0xFFFFFFFF#32, 0#32, 0#32, ()) ml
              ⟨s.core.lit_mark, Nat.zero_le _, lmBit2Inv_init hlm_len,
               fun h => absurd rfl h, hml⟩)
          (fun JmL (min_l, min_d, fc, j, ()) mj ⟨lmj, hj_le, hlmj_inv, hmin_ok, hmj⟩ ihm => ?_)
        clear hm hml; dsimp only [mkSt] at hmj
        have hlmj_l := hlmj_inv.1
        c0_hsplit
        · have hj_lt : j.toNat < csz_bv.toNat := by
            rw [hcsz_mod]
            simpa only [← hqw_mod] using (by assumption : _)
          have hj1 : (j + 1#32).toNat = j.toNat + 1 := by simp only [bv_c0]; omega
          have hqwj_n : (BitVec.setWidth 64 qw + 3 + BitVec.setWidth 64 j).toNat =
              qw.toNat + 3 + j.toNat := by
            change (BitVec.setWidth 64 qw + 3#64 + BitVec.setWidth 64 j).toNat = _
            simp only [bv_c0]; omega
          have hl_eq : ar[qw.toNat + 3 + j.toNat]'(by omega) =
              s.core.arena[qw.toNat + 3 + j.toNat]'(by omega) := by
            have h1 := har_lits_eq.2 j.toNat (by omega)
            rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h1
            exact Option.some.inj h1
          have hl_lt : (ar[qw.toNat + 3 + j.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
            rw [hl_eq]; exact hw.arena.lits_lt qw.toNat hqw_ref hqw_ng _ (List.mem_of_getElem?
              (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (by omega) (by omega)))
          have h2l1_n : ((BitVec.setWidth 64 (ar[qw.toNat + 3 + j.toNat]'(by omega)) <<<
              (1 : Nat)) + 1).toNat = 2 * (ar[qw.toNat + 3 + j.toNat]'(by omega)).toNat + 1 := by
            change ((BitVec.setWidth 64 _ <<< (1 : Nat)) + 1#64).toNat = _
            simp only [bv_c0]; omega
          have hqwj_ar : (BitVec.setWidth 64 (s.scratch.scratch_buf[(BitVec.setWidth 64
              (row_off + qi)).toNat]'(by rw [hset, hrqi]; omega)) + 3 +
              BitVec.setWidth 64 j).toNat < ar.length := by rw [hqw_eq, hqwj_n, har_l]; omega
          have hl_lm : (BitVec.setWidth 64 (ar[(BitVec.setWidth 64
              (s.scratch.scratch_buf[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
                rw [hset, hrqi]; omega)) + 3 + BitVec.setWidth 64 j).toNat]'hqwj_ar)).toNat <
              lmj.length := by simp only [hqw_eq]; simp only [hqwj_n, hset]; omega
          have h2l1_wv : ((BitVec.setWidth 64 (ar[(BitVec.setWidth 64
              (s.scratch.scratch_buf[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
                rw [hset, hrqi]; omega)) + 3 + BitVec.setWidth 64 j).toNat]'hqwj_ar) <<<
              (1 : Nat)) + 1).toNat < s.core.wvec.length := by
            simp only [hqw_eq]; simp only [hqwj_n, h2l1_n]; omega
          have hlmj_lift := fid_scan_cands_lmj_lift hlmj_inv hj_le
          have hl_lt_s : (s.core.arena[qw.toNat + 3 + j.toNat]'(by omega)).toNat <
              2 * c.max_vars := by rw [← hl_eq]; omega
          have hstep2_base : LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 (j.toNat + 1)
              (lmj.set (ar[qw.toNat + 3 + j.toNat]'(by omega)).toNat
                ((lmj[(ar[qw.toNat + 3 + j.toNat]'(by omega)).toNat]'(by omega)) ||| 2#8)) := by
            have h0 := lmBit2Inv_or2 hlm_len hlmj_inv (by omega) hl_lt_s
            simpa only [← hl_eq] using h0
          c0_hfast
          · exact hJm ⟨min_l, min_d, fc + 1#32, j, lmj⟩ mj ⟨hlmj_lift, hmin_ok, hmj⟩
          · exact ihm (min_l, min_d, fc + 1#32, j + 1#32, ()) mj (by dsimp only; rw [hj1]; omega)
              ⟨lmj, by rw [hj1]; omega, by rw [hj1]; exact lmBit2Inv_skip hlmj_inv, hmin_ok, hmj⟩
          · refine ihm (_, _, fc, j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
              ⟨_, by rw [hj1]; omega, by rw [hj1]; exact hstep2_base, fun _ => ?_, ?_⟩
            · simp only [hqw_eq]; simp only [hqwj_n, h2l1_n]
              refine ⟨hl_lt, ?_⟩
              unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            · simp only [hqw_eq] at hm; simp only [hqwj_n, hset] at hm
              try simp only [bv8_trunc_or_2] at hm
              try simp only [bv8_trunc_or_w] at hm
              exact hm
          · refine ihm (_, _, fc, j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
              ⟨_, by rw [hj1]; omega, by rw [hj1]; exact hstep2_base, fun _ => ?_, ?_⟩
            · simp only [hqw_eq]; simp only [hqwj_n, h2l1_n]
              refine ⟨hl_lt, ?_⟩
              unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            · simp only [hqw_eq] at hm; simp only [hqwj_n, hset] at hm
              try simp only [bv8_trunc_or_2] at hm
              try simp only [bv8_trunc_or_w] at hm
              exact hm
          · refine ihm (min_l, min_d, fc, j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
              ⟨_, by rw [hj1]; omega, by rw [hj1]; exact hstep2_base, hmin_ok, ?_⟩
            simp only [hqw_eq] at hm; simp only [hqwj_n, hset] at hm
            try simp only [bv8_trunc_or_2] at hm
            try simp only [bv8_trunc_or_w] at hm
            exact hm
        · have hj_eq : j.toNat = csz_bv.toNat := by
            rw [hcsz_mod] at hj_le ⊢
            have h1 : ¬ j.toNat < (ar[(qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
              rw [hqw2_mod]; omega)).toNat := by
              simpa only [← hqw_mod] using (by assumption : _)
            omega
          rw [hj_eq] at hlmj_inv; c0_hfast
          exact hJm ⟨min_l, min_d, fc, j, lmj⟩ mj ⟨hlmj_inv, hmin_ok, hmj⟩
  · clear hm
    refine wp_loop_inv
      (fun (ci, ()) mci => ∃ arci,
        ci.toNat ≤ nql.toNat ∧ FidScanArBvaqInv c s arci ws2 ci.toNat nql.toNat ∧
        (FullMem c (mkSt arci s.core.lit_mark ws ws1 ws2) ⋆ R) mci)
      (fun (ci, ()) _ => nql.toNat - ci.toNat)
      (fun Jc hJc => by c0_hfast; exact hJc (0#32, ()) ml ⟨ar, Nat.zero_le _, hbvaq, hml⟩)
      (fun Jc (ci, ()) mci ⟨arci, hci_le, hbvaq_ci, hmci⟩ ihc => ?_)
    clear hml; dsimp only [mkSt] at hmci
    have harci_l := hbvaq_ci.1
    c0_hsplit
    · have hci_lt : ci.toNat < nql.toNat := by assumption
      have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by simp only [bv_c0]; omega
      have hidx_ref := (hbvaq_ci.2.2.2.1 ci.toNat (Nat.le_refl _) hci_lt).1
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hidx_ref
      have hidx_wf := hw.arena.refs_wf _ hidx_ref
      have hstep := fidScanArBvaqInv_clear_step har_len hbvaq_ci hci_lt (by omega)
      have hci_ws2 : (BitVec.setWidth 64 ci).toNat < ws2.length := by rw [hset, hws2_l]; omega
      have hidx_ar : (BitVec.setWidth 64 (ws2[(BitVec.setWidth 64 ci).toNat]'hci_ws2)).toNat <
          arci.length := by
        simp only [hset]; have := hidx_wf.1; have := hcl.arena_len_le; omega
      c0_hfast
      refine ihc (ci + 1#32, ()) m (by dsimp only; rw [hci1]; omega)
        ⟨_, by rw [hci1]; omega, by rw [hci1]; exact hstep, ?_⟩
      simp only [hset] at hm; exact hm
    · have hci_eq : ci.toNat = nql.toNat := by omega
      rw [hci_eq] at hbvaq_ci
      have har_rest : arci = s.core.arena := fidScanArBvaqInv_done har_len hbvaq_ci
      rw [har_rest] at hmci; c0_hfast; exact hQ ncntd ws ws1 ws2 mci
        ⟨hcl, { hsc with wsort_len := hws_l, work_stk1_len := hws1_l, work_stk2_len := hws2_l }⟩
        hnc_le hcntd_ok hmci

/-! ## 4. `full_bva_filter_row_fid_wp` (`m4BvaFilterRowSpec` with `PH_BVA_Q`) -/

private def FidFilterArBvaqInv (c : FullCfg) (s : FullState) (ar sb : List (BitVec 32))
    (nrow_off lo hi : Nat) : Prop :=
  ar.length = c.arena_cap ∧ sb.length = c.scratch_cap ∧ hi ≤ 256 ∧ (∀ nm, lo ≤ nm → nm < hi →
    let dr := sb[nrow_off + nm]?.getD 0#32
    (dr &&& 0x80000000#32) = 0#32 → dr.toNat ∈ fullArenaClauseRefsCore s.core ∧
      (s.core.arena[dr.toNat]?.getD 0#32 &&& 0x02000000#32) = 0#32) ∧
  ∀ i < c.arena_cap, ar[i]? = s.core.arena[i]? ∨ (∃ nm, lo ≤ nm ∧ nm < hi ∧
      let dr := sb[nrow_off + nm]?.getD 0#32
      (dr &&& 0x80000000#32) = 0#32 ∧ dr.toNat = i ∧
      (s.core.arena[i]?.getD 0#32 &&& 0x02000000#32) = 0#32 ∧
      ar[i]? = some (s.core.arena[i]?.getD 0#32 ||| 0x02000000#32))

private theorem fidFilterArBvaqInv_init {c : FullCfg} {s : FullState} (hslen : s.LengthsOk c)
    (nrow_off : Nat) :
    FidFilterArBvaqInv c s s.core.arena s.scratch.scratch_buf nrow_off 0 0 :=
  ⟨hslen.core_ok.arena_len_arr, hslen.scratch_ok.scratch_buf_len, Nat.zero_le _,
   fun _ _ h => by omega, fun _ _ => Or.inl rfl⟩

private theorem fidFilterArBvaqInv_congr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    {ar sb : List (BitVec 32)} {nrow_off lo hi : Nat}
    (h : FidFilterArBvaqInv c s ar sb nrow_off lo hi) :
    fullArenaClauseRefsCore { s.core with arena := ar } = fullArenaClauseRefsCore s.core ∧
    (∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore { s.core with arena := ar } r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseSizeCore { s.core with arena := ar } r = fullArenaClauseSizeCore s.core r ∧
      fullArenaClauseLitsCore { s.core with arena := ar } r = fullArenaClauseLitsCore s.core r) :=
  fidArBvaq_congr hcl hw fun i hi => by
    rcases h.2.2.2.2 i hi with heq | ⟨nm, hlo, hhi, hbin, hidx, _, hset⟩
    · exact Or.inl heq
    · have href := (h.2.2.2.1 nm hlo hhi hbin).1
      rw [hidx] at href; exact Or.inr ⟨href, hset⟩

private theorem fid_filter_row_ar_lits_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {ar sb : List (BitVec 32)} {nrow_off nqn : Nat}
    (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hbvaq : FidFilterArBvaqInv c s ar sb nrow_off 0 nqn)
    {r : Nat} (hr : r ∈ fullArenaClauseRefsCore s.core) :
    ∀ j < fullArenaClauseSizeCore s.core r, ar[r + 3 + j]? = s.core.arena[r + 3 + j]? := by
  intro j hj
  have hwf := hw.arena.refs_wf r hr; have hal := hcl.arena_len_le
  rcases hbvaq.2.2.2.2 (r + 3 + j) (by omega) with heq | ⟨nm, h0, hnm, h0b, hidx, _, _⟩
  · exact heq
  · exfalso
    have hnm_ref := (hbvaq.2.2.2.1 nm h0 hnm h0b).1; rw [hidx] at hnm_ref
    have := fullArenaScanRefs_disjoint hr hnm_ref (by omega); omega

private theorem fidFilterArBvaqInv_push_bin {c : FullCfg} {s : FullState}
    {ar sb : List (BitVec 32)} {nrow_off par_off nqn : Nat}
    (h : FidFilterArBvaqInv c s ar sb nrow_off 0 nqn)
    (hnqn : nqn < 256) (hdisj : nrow_off + 256 ≤ par_off) (hpar : par_off + 256 ≤ c.scratch_cap)
    {qw qi : BitVec 32} (hbin : (qw &&& 0x80000000#32) ≠ 0#32) :
    FidFilterArBvaqInv c s ar ((sb.set (nrow_off + nqn) qw).set (par_off + nqn) qi)
      nrow_off 0 (nqn + 1) := by
  obtain ⟨har, hsb, hhi, hdom, hall⟩ := h
  refine ⟨har, by simp [hsb], by omega, fun nm h0 hnm => ?_, fun i hi => ?_⟩
  · dsimp only; intro h0b
    by_cases hne : nm = nqn
    · subst hne
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
        Option.getD_some] at h0b
      exact absurd h0b hbin
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)] at h0b ⊢
      exact hdom nm h0 (by omega) h0b
  · rcases hall i hi with heq | ⟨nm, h0, hnm, h0b, hidx, h0v, hset⟩
    · exact Or.inl heq
    · refine Or.inr ⟨nm, h0, by omega, ?_, ?_, h0v, hset⟩
      · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact h0b
      · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hidx

private theorem fidFilterArBvaqInv_push_large {c : FullCfg} {s : FullState}
    {ar sb : List (BitVec 32)} {nrow_off par_off nqn : Nat}
    (h : FidFilterArBvaqInv c s ar sb nrow_off 0 nqn)
    (hnqn : nqn < 256) (hdisj : nrow_off + 256 ≤ par_off) (hpar : par_off + 256 ≤ c.scratch_cap)
    {dr qi : BitVec 32} (hdr_ref : dr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hdr_lt : dr.toNat < c.arena_cap) (hdr_bin : (dr &&& 0x80000000#32) = 0#32)
    (hdr_nbvaq : (ar[dr.toNat]'(by rw [h.1]; exact hdr_lt) &&& 0x02000000#32) = 0#32) :
    FidFilterArBvaqInv c s
      (ar.set dr.toNat ((ar[dr.toNat]'(by rw [h.1]; exact hdr_lt)) ||| 0x02000000#32))
      ((sb.set (nrow_off + nqn) dr).set (par_off + nqn) qi)
      nrow_off 0 (nqn + 1) := by
  obtain ⟨har, hsb, hhi, hdom, hall⟩ := h
  have horig : ar[dr.toNat]? = s.core.arena[dr.toNat]? := by
    rcases hall dr.toNat hdr_lt with heq | ⟨_, _, _, _, _, h0v, hset⟩
    · exact heq
    · rw [List.getElem?_eq_getElem (by omega)] at hset
      have hval := Option.some.inj hset
      have h1 : ((s.core.arena[dr.toNat]?.getD 0#32 ||| 0x02000000#32) &&& 0x02000000#32) =
          0x02000000#32 := by
        rw [BitVec.and_or_distrib_right,
          show (0x02000000#32 &&& 0x02000000#32) = 0x02000000#32 from rfl, h0v, BitVec.zero_or]
      rw [hval] at hdr_nbvaq; exact absurd (hdr_nbvaq.symm.trans h1) (by decide)
  have hs_nbvaq : (s.core.arena[dr.toNat]?.getD 0#32 &&& 0x02000000#32) = 0#32 := by
    rw [← horig, List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hdr_nbvaq
  refine ⟨by simp [har], by simp [hsb], by omega, fun nm h0 hnm => ?_, fun i hi => ?_⟩
  · dsimp only; intro h0b
    by_cases hne : nm = nqn
    · subst hne
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
      exact ⟨hdr_ref, hs_nbvaq⟩
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)] at h0b ⊢
      exact hdom nm h0 (by omega) h0b
  · by_cases hid : i = dr.toNat
    · subst hid
      refine Or.inr ⟨nqn, Nat.zero_le _, by omega, ?_, ?_, hs_nbvaq, ?_⟩
      · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
        exact hdr_bin
      · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
      · rw [List.getElem?_set_self (by omega)]
        have har_eq : ar[dr.toNat]'(by omega) = s.core.arena[dr.toNat]?.getD 0#32 := by
          rw [← horig, List.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [har_eq]
    · rw [List.getElem?_set_ne (Ne.symm hid)]
      rcases hall i hi with heq | ⟨nm, h0, hnm, h0b, hidx, h0v, hset⟩
      · exact Or.inl heq
      · refine Or.inr ⟨nm, h0, by omega, ?_, ?_, h0v, hset⟩
        · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact h0b
        · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hidx

private theorem fidFilterArBvaqInv_clear_bin {c : FullCfg} {s : FullState}
    {ar sb : List (BitVec 32)} {nrow_off qi nqn : Nat}
    (h : FidFilterArBvaqInv c s ar sb nrow_off qi nqn) (hqi : qi < nqn)
    (hbin : (sb[nrow_off + qi]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32) :
    FidFilterArBvaqInv c s ar sb nrow_off (qi + 1) nqn := by
  obtain ⟨har, hsb, hhi, hdom, hall⟩ := h
  refine ⟨har, hsb, hhi, fun nm h1 h2 => hdom nm (by omega) h2, fun i hi => ?_⟩
  rcases hall i hi with heq | ⟨nm, h1, h2, h0b, hidx, h0v, hset⟩
  · exact Or.inl heq
  · have hne : nm ≠ qi := fun he => by subst he; exact hbin h0b
    exact Or.inr ⟨nm, by omega, h2, h0b, hidx, h0v, hset⟩

private theorem fidFilterArBvaqInv_clear_large {c : FullCfg} {s : FullState}
    {ar sb : List (BitVec 32)}
    {nrow_off qi nqn : Nat} (hs_ar : s.core.arena.length = c.arena_cap)
    (h : FidFilterArBvaqInv c s ar sb nrow_off qi nqn) (hqi : qi < nqn)
    (hqr : nrow_off + qi < sb.length)
    (h0b : (sb[nrow_off + qi]'hqr &&& 0x80000000#32) = 0#32)
    (hdr_lt : (sb[nrow_off + qi]'hqr).toNat < c.arena_cap) :
    let dr := (sb[nrow_off + qi]'hqr).toNat
    FidFilterArBvaqInv c s
      (ar.set dr ((ar[dr]'(by rw [h.1]; exact hdr_lt)) &&& ~~~0x02000000#32))
      sb nrow_off (qi + 1) nqn := by
  obtain ⟨har, hsb, hhi, hdom, hall⟩ := h
  intro dr
  have hdr_eq : (sb[nrow_off + qi]?.getD 0#32).toNat = dr := by
    rw [List.getElem?_eq_getElem hqr, Option.getD_some]
  have h0b' : (sb[nrow_off + qi]?.getD 0#32 &&& 0x80000000#32) = 0#32 := by
    rw [List.getElem?_eq_getElem hqr, Option.getD_some]; exact h0b
  have hdr_s0 : (s.core.arena[dr]?.getD 0#32 &&& 0x02000000#32) = 0#32 := by
    have := (hdom qi (Nat.le_refl _) hqi h0b').2; rwa [hdr_eq] at this
  have har_clr : ((ar[dr]'(by omega)) &&& ~~~0x02000000#32) = s.core.arena[dr]?.getD 0#32 := by
    rcases hall dr hdr_lt with heq | ⟨_, _, _, _, _, _, hset⟩
    · have : ar[dr]'(by omega) = s.core.arena[dr]?.getD 0#32 := by
        rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [this]; exact fid_bv32_clear_bvaq_of_zero hdr_s0
    · rw [List.getElem?_eq_getElem (by omega)] at hset
      rw [Option.some.inj hset]; exact fid_bv32_bvaq_roundtrip hdr_s0
  refine ⟨by simp [har], hsb, hhi, fun nm h1 h2 => hdom nm (by omega) h2, fun i hi => ?_⟩
  by_cases hid : i = dr
  · subst hid; left
    rw [List.getElem?_set_self (by omega), har_clr,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  · rw [List.getElem?_set_ne (Ne.symm hid)]
    rcases hall i hi with heq | ⟨nm, h1, h2, hnb, hidx, h0v, hset⟩
    · exact Or.inl heq
    · have hne : nm ≠ qi := fun he => by subst he; rw [hdr_eq] at hidx; exact hid hidx.symm
      exact Or.inr ⟨nm, by omega, h2, hnb, hidx, h0v, hset⟩

private theorem fidFilterArBvaqInv_done {c : FullCfg} {s : FullState} {ar sb : List (BitVec 32)}
    {nrow_off nqn : Nat} (hs_ar : s.core.arena.length = c.arena_cap)
    (h : FidFilterArBvaqInv c s ar sb nrow_off nqn nqn) : ar = s.core.arena := by
  apply list_eq_of_getElem?_eq (by rw [h.1, hs_ar])
  intro i hi
  rcases h.2.2.2.2 i (by omega) with heq | ⟨nm, h1, h2, _⟩
  · exact heq
  · omega

private theorem fid_filter_row_bin_upd {c : FullCfg} {F_cur : List (List Nat)}
    {s : FullState} {ar sb : List (BitVec 32)}
    {row_off nrow_off par_off cur_qn nqn qi qw best_lit : BitVec 32}
    {res : List Nat} {step : Nat}
    (hsb_l : sb.length = c.scratch_cap)
    (hbvaq : FidFilterArBvaqInv c s ar sb nrow_off.toNat 0 nqn.toNat)
    (hnqn_lt : nqn.toNat < 256)
    (hnr_bd : nrow_off.toNat + 256 ≤ c.scratch_cap)
    (hpr_bd : par_off.toNat + 256 ≤ c.scratch_cap)
    (hdisj : nrow_off.toNat + 256 ≤ par_off.toNat)
    (hbin_ne : (qw &&& 0x80000000#32) ≠ 0#32)
    (hq_lt : (qw &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars)
    (hres_eq : res = [(qw &&& 0x7FFFFFFF#32).toNat])
    (hfr_q : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [(s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat,
        (qw &&& 0x7FFFFFFF#32).toNat]))
    (hbl_q_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [best_lit.toNat, (qw &&& 0x7FFFFFFF#32).toNat]))
    (hqi_lt : qi.toNat < cur_qn.toNat)
    (hres_lt : ∀ x ∈ res, x < 2 * s.core.cur_vars)
    (hres_nd : (res.map (· / 2)).Nodup)
    (hres_ent : ∀ t < step, (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res)))
    (hqw_getD : s.scratch.scratch_buf[row_off.toNat + qi.toNat]?.getD 0#32 = qw)
    (hfr_sb : ∀ idx < c.scratch_cap, ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 256) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 256) →
      sb[idx]? = s.scratch.scratch_buf[idx]?)
    (hent : ∀ nm < nqn.toNat, let pi := (sb[par_off.toNat + nm]?.getD 0#32).toNat
      pi < cur_qn.toNat ∧ ∃ res' : List Nat,
        (∀ x ∈ res', x < 2 * s.core.cur_vars) ∧ (res'.map (· / 2)).Nodup ∧
        M4BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res' ∧
        M4BvaRowEntryOk F_cur s best_lit.toNat (sb[nrow_off.toNat + nm]?.getD 0#32) res' ∧
        (∀ t < step, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res'))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res'))) :
    let sb1 := (sb.set (nrow_off.toNat + nqn.toNat) qw).set (par_off.toNat + nqn.toNat) qi
    FidFilterArBvaqInv c s ar sb1 nrow_off.toNat 0 (nqn.toNat + 1) ∧
    (∀ idx < c.scratch_cap, ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 256) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 256) →
      sb1[idx]? = s.scratch.scratch_buf[idx]?) ∧
    (∀ nm < nqn.toNat + 1, let pi := (sb1[par_off.toNat + nm]?.getD 0#32).toNat
      pi < cur_qn.toNat ∧ ∃ res' : List Nat,
        (∀ x ∈ res', x < 2 * s.core.cur_vars) ∧ (res'.map (· / 2)).Nodup ∧
        M4BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res' ∧
        M4BvaRowEntryOk F_cur s best_lit.toNat (sb1[nrow_off.toNat + nm]?.getD 0#32) res' ∧
        (∀ t < step, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res'))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res'))) := by
  let sb1 := (sb.set (nrow_off.toNat + nqn.toNat) qw).set (par_off.toNat + nqn.toNat) qi
  refine ⟨fidFilterArBvaqInv_push_bin hbvaq hnqn_lt hdisj hpr_bd hbin_ne, ?_, ?_⟩
  · intro idx hidx hnot1 hnot2
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hfr_sb idx hidx hnot1 hnot2
  · intro nm hnm
    by_cases hne : nm = nqn.toNat
    · subst hne
      have hpi_eq : (sb1[par_off.toNat + nqn.toNat]?.getD 0#32).toNat = qi.toNat := by
        dsimp only [sb1]; rw [List.getElem?_set_self (by simp [hsb_l]; omega)]; rfl
      have hnr_eq : sb1[nrow_off.toNat + nqn.toNat]?.getD 0#32 = qw := by
        dsimp only [sb1]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
      refine ⟨by rw [hpi_eq]; exact hqi_lt, res, hres_lt, hres_nd, ?_, ?_, hres_ent, ?_⟩
      · rw [hpi_eq, hqw_getD]; unfold M4BvaRowEntryOk; rw [ite_eq_left hbin_ne]
        exact ⟨hq_lt, hres_eq, hfr_q⟩
      · rw [hnr_eq]; unfold M4BvaRowEntryOk; rw [ite_eq_left hbin_ne]
        exact ⟨hq_lt, hres_eq, hbl_q_ent⟩
      · rw [hres_eq]; exact hbl_q_ent
    · have hpi_eq : sb1[par_off.toNat + nm]? = sb[par_off.toNat + nm]? := by
        dsimp only [sb1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      have hnr_eq : sb1[nrow_off.toNat + nm]? = sb[nrow_off.toNat + nm]? := by
        dsimp only [sb1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      dsimp only; rw [hpi_eq, hnr_eq]; exact hent nm (by omega)

private theorem fid_filter_row_mark_step {c : FullCfg} {s : FullState}
    {ar : List (BitVec 32)} {lmj : List (BitVec 8)} {qw j : BitVec 32}
    {res : List Nat} {step : Nat}
    (hlm_len : s.core.lit_mark.length = 2 * c.max_vars)
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hfr_b0 : (s.core.lit_mark[(s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat]?.getD 0#8 &&&
      1#8) ≠ 0#8)
    (hres_perm_f : res.Perm ((fullArenaClauseLitsCore s.core qw.toNat).filter
      (· != (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat)))
    (hlmj_inv : LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 j.toNat lmj)
    (hlmj_res : ∀ l < 2 * s.core.cur_vars, (lmj[l]?.getD 0#8 &&& 2#8) ≠ 0#8 → l ∈ res)
    (hqwj_ar : qw.toNat + 3 + j.toNat < ar.length)
    (hqwj_s : qw.toNat + 3 + j.toNat < s.core.arena.length)
    (hl_eq : ar[qw.toNat + 3 + j.toNat]'hqwj_ar = s.core.arena[qw.toNat + 3 + j.toNat]'hqwj_s)
    (hl_mem : (s.core.arena[qw.toNat + 3 + j.toNat]'hqwj_s).toNat ∈
      fullArenaClauseLitsCore s.core qw.toNat)
    (hl_lt : (ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat < 2 * s.core.cur_vars)
    (hb0_32 : (BitVec.setWidth 32 (lmj[(ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat]'(by
      rw [hlmj_inv.1]; omega)) &&& BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 1)) =
      BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0)) :
    let l := (ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat
    let lm1 := lmj.set l ((lmj[l]'(by rw [hlmj_inv.1]; omega)) ||| 2#8)
    LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 (j.toNat + 1) lm1 ∧
    (∀ x < 2 * s.core.cur_vars, (lm1[x]?.getD 0#8 &&& 2#8) ≠ 0#8 → x ∈ res) := by
  have hlmj_l := hlmj_inv.1
  have hl_b0_zero :
      (s.core.lit_mark[(ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat]?.getD 0#8 &&& 1#8) = 0#8 := by
    rw [← lmBit2Inv_preserves_bit0 hlmj_inv (by omega),
      List.getElem?_eq_getElem (by omega), Option.getD_some]
    apply BitVec.eq_of_toNat_eq
    have h0' := congrArg BitVec.toNat hb0_32; simp only [BitVec.toNat_and, BitVec.toNat_setWidth,
      show (BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 1)).toNat = 1 from rfl,
      show (BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0)).toNat = 0 from rfl,
      show (1#8 : BitVec 8).toNat = 1 from rfl, show (0#8 : BitVec 8).toNat = 0 from rfl] at h0' ⊢
    have hlt8 := (lmj[(ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat]'(by omega)).isLt
    rwa [Nat.mod_eq_of_lt (Nat.lt_trans hlt8 (by decide))] at h0'
  have hl_ne_fr : (ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat ≠
      (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat := fun heq => by
    rw [heq] at hl_b0_zero; exact hfr_b0 hl_b0_zero
  have hl_in_res : (ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat ∈ res := by
    apply hres_perm_f.mem_iff.mpr; rw [List.mem_filter]
    exact ⟨by rw [hl_eq]; exact hl_mem, bne_iff_ne.mpr hl_ne_fr⟩
  have hl_lt_s : (s.core.arena[qw.toNat + 3 + j.toNat]'hqwj_s).toNat < 2 * c.max_vars := by
    rw [← hl_eq]; omega
  have hstep2 : LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 (j.toNat + 1)
      (lmj.set (ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat
        ((lmj[(ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat]'(by omega)) ||| 2#8)) := by
    have h0 := lmBit2Inv_or2 hlm_len hlmj_inv hqwj_s hl_lt_s
    simpa only [← hl_eq] using h0
  refine ⟨hstep2, fun x hx hne => ?_⟩
  by_cases hle : x = (ar[qw.toNat + 3 + j.toNat]'hqwj_ar).toNat
  · rw [hle]; exact hl_in_res
  · rw [List.getElem?_set_ne (Ne.symm hle)] at hne; exact hlmj_res x hx hne

private theorem fid_filter_row_large_upd {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {ar sb : List (BitVec 32)} {lmj : List (BitVec 8)}
    {row_off nrow_off par_off cur_qn nqn qi qw dr best_lit : BitVec 32}
    {res : List Nat} {step : Nat}
    (hcl : s.core.LengthsOk c) (har_l : ar.length = c.arena_cap)
    (hsb_l : sb.length = c.scratch_cap)
    (hw_ar : FullWitnessInv c F0 F_cur { s.core with arena := ar })
    (hnd_ar : FullArenaVarsNodup
      (FullState.mk { s.core with arena := ar } { s.scratch with scratch_buf := sb }))
    (hl0 : s.core.cur_level = 0)
    (hbvaq : FidFilterArBvaqInv c s ar sb nrow_off.toNat 0 nqn.toNat)
    (hnqn_lt : nqn.toNat < 256)
    (hnr_bd : nrow_off.toNat + 256 ≤ c.scratch_cap)
    (hpr_bd : par_off.toNat + 256 ≤ c.scratch_cap)
    (hdisj : nrow_off.toNat + 256 ≤ par_off.toNat)
    (hrefs_ar : fullArenaClauseRefsCore { s.core with arena := ar } =
      fullArenaClauseRefsCore s.core)
    (hqw_ref : qw.toNat ∈ fullArenaClauseRefsCore s.core)
    (hqw_ng : fullArenaClauseGarbCore s.core qw.toNat = false)
    (hqw_sz3 : 3 ≤ fullArenaClauseSizeCore s.core qw.toNat)
    (hqw_sz256 : fullArenaClauseSizeCore s.core qw.toNat ≤ 256)
    (hqw_sz_ar : fullArenaClauseSizeCore { s.core with arena := ar } qw.toNat =
      fullArenaClauseSizeCore s.core qw.toNat)
    (hfr_mem : (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat ∈
      fullArenaClauseLitsCore s.core qw.toNat)
    (hres_perm_f : res.Perm ((fullArenaClauseLitsCore s.core qw.toNat).filter
      (· != (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat)))
    (hqw_perm : (fullArenaClauseLits s qw.toNat).Perm
      ((s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat :: res))
    (hbin_eq : (qw &&& 0x80000000#32) = 0#32)
    (hdr_ref : dr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hdr_lt_ar : dr.toNat + 3 ≤ ar.length)
    (hdr_ng_s : fullArenaClauseGarbCore { s.core with arena := ar } dr.toNat =
      fullArenaClauseGarbCore s.core dr.toNat)
    (hdr_sz_s : fullArenaClauseSizeCore { s.core with arena := ar } dr.toNat =
      fullArenaClauseSizeCore s.core dr.toNat)
    (hdr_lits_s : fullArenaClauseLitsCore { s.core with arena := ar } dr.toNat =
      fullArenaClauseLitsCore s.core dr.toNat)
    (hdr_ng_ar : fullArenaClauseGarb
      (FullState.mk { s.core with arena := ar, lit_mark := lmj }
        { s.scratch with scratch_buf := sb }) dr.toNat = false)
    (hdr_nbvaq_h : (fullArenaHdr
      (FullState.mk { s.core with arena := ar, lit_mark := lmj }
        { s.scratch with scratch_buf := sb }) dr.toNat &&& 0x02000000#32) = 0#32)
    (hdr_sz_eq_ar : fullArenaClauseSize
      (FullState.mk { s.core with arena := ar, lit_mark := lmj }
        { s.scratch with scratch_buf := sb }) dr.toNat =
      fullArenaClauseSize
      (FullState.mk { s.core with arena := ar, lit_mark := lmj }
        { s.scratch with scratch_buf := sb }) qw.toNat)
    (hbl_mem_ar : best_lit.toNat ∈ fullArenaClauseLits
      (FullState.mk { s.core with arena := ar, lit_mark := lmj }
        { s.scratch with scratch_buf := sb }) dr.toNat)
    (hdr_perm_ar : (fullArenaClauseLits
      (FullState.mk { s.core with arena := ar, lit_mark := lmj }
        { s.scratch with scratch_buf := sb }) dr.toNat).Perm (best_lit.toNat :: res))
    (hdr_filt_ar : ((fullArenaClauseLits
      (FullState.mk { s.core with arena := ar, lit_mark := lmj }
        { s.scratch with scratch_buf := sb }) dr.toNat).filter
      (· != best_lit.toNat)).Perm res)
    (hbl_res_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res)))
    (hqi_lt : qi.toNat < cur_qn.toNat)
    (hres_lt : ∀ x ∈ res, x < 2 * s.core.cur_vars)
    (hres_nd : (res.map (· / 2)).Nodup)
    (hres_ent : ∀ t < step, (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res)))
    (hqw_getD : s.scratch.scratch_buf[row_off.toNat + qi.toNat]?.getD 0#32 = qw)
    (hfr_sb : ∀ idx < c.scratch_cap, ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 256) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 256) →
      sb[idx]? = s.scratch.scratch_buf[idx]?)
    (hent : ∀ nm < nqn.toNat, let pi := (sb[par_off.toNat + nm]?.getD 0#32).toNat
      pi < cur_qn.toNat ∧ ∃ res' : List Nat,
        (∀ x ∈ res', x < 2 * s.core.cur_vars) ∧ (res'.map (· / 2)).Nodup ∧
        M4BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res' ∧
        M4BvaRowEntryOk F_cur s best_lit.toNat (sb[nrow_off.toNat + nm]?.getD 0#32) res' ∧
        (∀ t < step, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res'))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res')))
    (hhar_b : c.arena_cap < 2 * dimacsBound) :
    let ar1 := ar.set dr.toNat ((ar[dr.toNat]'(by omega)) ||| 0x02000000#32)
    let sb1 := (sb.set (nrow_off.toNat + nqn.toNat) dr).set (par_off.toNat + nqn.toNat) qi
    FidFilterArBvaqInv c s ar1 sb1 nrow_off.toNat 0 (nqn.toNat + 1) ∧
    FullWitnessInv c F0 F_cur { s.core with arena := ar1 } ∧ FullArenaVarsNodup
      (FullState.mk { s.core with arena := ar1 } { s.scratch with scratch_buf := sb1 }) ∧
    (∀ idx < c.scratch_cap, ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 256) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 256) →
      sb1[idx]? = s.scratch.scratch_buf[idx]?) ∧
    (∀ nm < nqn.toNat + 1, let pi := (sb1[par_off.toNat + nm]?.getD 0#32).toNat
      pi < cur_qn.toNat ∧ ∃ res' : List Nat,
        (∀ x ∈ res', x < 2 * s.core.cur_vars) ∧ (res'.map (· / 2)).Nodup ∧
        M4BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res' ∧
        M4BvaRowEntryOk F_cur s best_lit.toNat (sb1[nrow_off.toNat + nm]?.getD 0#32) res' ∧
        (∀ t < step, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res'))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res'))) := by
  unfold dimacsBound at hhar_b
  have hcl_ar : ({ s.core with arena := ar }).LengthsOk c := { hcl with arena_len_arr := har_l }
  have hdr_nbvaq_ar : (ar[dr.toNat]'(by omega) &&& 0x02000000#32) = 0#32 := by
    change (fullArenaHdrCore { s.core with arena := ar } dr.toNat &&& 0x02000000#32) = 0#32
      at hdr_nbvaq_h
    unfold fullArenaHdrCore at hdr_nbvaq_h; dsimp only at hdr_nbvaq_h
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdr_nbvaq_h
  have hdr_bin : (dr &&& 0x80000000#32) = 0#32 := fid_bv32_bin_flag_zero_of_lt (by omega)
  let ar1 := ar.set dr.toNat ((ar[dr.toNat]'(by omega)) ||| 0x02000000#32)
  let sb1 := (sb.set (nrow_off.toNat + nqn.toNat) dr).set (par_off.toNat + nqn.toNat) qi
  have hbvaq1 : FidFilterArBvaqInv c s ar1 sb1 nrow_off.toNat 0 (nqn.toNat + 1) :=
    fidFilterArBvaqInv_push_large hbvaq hnqn_lt (by omega) (by omega)
      hdr_ref (by omega) hdr_bin hdr_nbvaq_ar
  have hdr_ref_ar : dr.toNat ∈ fullArenaClauseRefsCore { s.core with arena := ar } := by
    rw [hrefs_ar]; exact hdr_ref
  have ⟨_, _, hw1, _⟩ := fullWitnessInv_set_hdr_bit20
    hcl_ar hw_ar hl0 hdr_ref_ar
    ((ar[dr.toNat]'(by omega)) ||| 0x02000000#32)
    (by unfold fullArenaHdrCore; dsimp only
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact fid_bv32_or_bvaq_garb _)
    (by unfold fullArenaHdrCore; dsimp only
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact fid_bv32_or_bvaq_shrk _)
  have hnd1 : FullArenaVarsNodup
      (FullState.mk { s.core with arena := ar1 } { s.scratch with scratch_buf := sb1 }) :=
    fullArenaVarsNodup_of_bit20
      (s := FullState.mk { s.core with arena := ar } { s.scratch with scratch_buf := sb1 })
      hcl_ar hw_ar hl0 hnd_ar hdr_ref_ar
      (by unfold fullArenaHdrCore; dsimp only
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          exact fid_bv32_or_bvaq_garb _)
      (by unfold fullArenaHdrCore; dsimp only
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          exact fid_bv32_or_bvaq_shrk _)
  refine ⟨hbvaq1, hw1, hnd1, ?_, ?_⟩
  · intro idx hidx hnot1 hnot2
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hfr_sb idx hidx hnot1 hnot2
  · intro nm hnm
    by_cases hne : nm = nqn.toNat
    · subst hne
      have hpi_eq : (sb1[par_off.toNat + nqn.toNat]?.getD 0#32).toNat = qi.toNat := by
        dsimp only [sb1]; rw [List.getElem?_set_self (by simp [hsb_l]; omega)]; rfl
      have hnr_eq : sb1[nrow_off.toNat + nqn.toNat]?.getD 0#32 = dr := by
        dsimp only [sb1]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
      refine ⟨by rw [hpi_eq]; exact hqi_lt, res, hres_lt, hres_nd, ?_, ?_, hres_ent, hbl_res_ent⟩
      · rw [hpi_eq, hqw_getD]; unfold M4BvaRowEntryOk
        rw [ite_eq_right (fun h' => h' hbin_eq)]
        exact ⟨hqw_ref, hqw_ng, hqw_sz3, hqw_sz256, hfr_mem, hres_perm_f, hqw_perm⟩
      · rw [hnr_eq]; unfold M4BvaRowEntryOk; rw [ite_eq_right (fun h' => h' hdr_bin)]
        change fullArenaClauseGarbCore { s.core with arena := ar } dr.toNat = false at hdr_ng_ar
        change fullArenaClauseSizeCore { s.core with arena := ar } dr.toNat =
          fullArenaClauseSizeCore { s.core with arena := ar } qw.toNat at hdr_sz_eq_ar
        change best_lit.toNat ∈ fullArenaClauseLitsCore { s.core with arena := ar } dr.toNat
          at hbl_mem_ar
        change (fullArenaClauseLitsCore { s.core with arena := ar } dr.toNat).Perm _ at hdr_perm_ar
        change ((fullArenaClauseLitsCore { s.core with arena := ar } dr.toNat).filter _).Perm _
          at hdr_filt_ar
        rw [hdr_ng_s] at hdr_ng_ar; rw [hdr_sz_s, hqw_sz_ar] at hdr_sz_eq_ar
        rw [hdr_lits_s] at hbl_mem_ar hdr_perm_ar hdr_filt_ar; unfold fullArenaClauseSize
        exact ⟨hdr_ref, hdr_ng_ar, by omega, by omega, hbl_mem_ar, hdr_filt_ar.symm, hdr_perm_ar⟩
    · have hpi_eq : sb1[par_off.toNat + nm]? = sb[par_off.toNat + nm]? := by
        dsimp only [sb1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      have hnr_eq : sb1[nrow_off.toNat + nm]? = sb[nrow_off.toNat + nm]? := by
        dsimp only [sb1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      dsimp only; rw [hpi_eq, hnr_eq]; exact hent nm (by omega)

private def fidEGrp0_2 {rs : List Ty} (J : Cont [i32, i32]) (xs : Tup Val [i32, i32]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32]]) bs _ =>
    match bs (J, ()) with | .cons f .nil => f xs
  | _ => .hlt

private def fidEGrpBody_0 {rs : List Ty} (J : Cont []) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[]]) _ body => body (J, ()) | _ => .hlt

private def fidEGrpBody_1 {rs : List Ty} (J : Cont [i32]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32]]) _ body => body (J, ()) | _ => .hlt

private def fidFilterRowMpExpr (h pWvec pWstk pAr pLm pScr : Val i64)
    (row_off nrow_off par_off cur_qn best_lit nqn qi qw csz min_l min_d j : Val i32)
    (J : Cont [i32, i32]) (Jend : Cont []) (Jbr : Cont [i32])
    (Jm : Cont [i32, i32, i32]) (Jm2 : Cont [i32]) : Expr Val Cont [i32] :=
  full_bva_filter_row_fid_body Val Cont (h, row_off, nrow_off, par_off, cur_qn, best_lit, ())
    |> eSkip 1 |> eLoad64 pWvec
    |> eSkip 1 |> eLoad64 pWstk
    |> eSkip 1 |> eLoad64 pAr
    |> eSkip 1 |> eLoad64 pLm
    |> eSkip 1 |> eLoad64 pScr
    |> fidEGrp0_2 J (nqn, qi, ())
    |> fidEGrpBody_0 Jend
    |> eSkip 1 |> eThen
    |> eSkip 1 |> eThen
    |> eSkip 4 |> eLoad32 qw
    |> fidEGrpBody_1 Jbr
    |> eSkip 2 |> eElse
    |> eSkip 4 |> eLoad32 csz
    |> eGrp0_3 Jm (min_l, min_d, j, ())
    |> eSkip 1 |> eElse
    |> fidEGrpBody_1 Jm2

private theorem fid_filter_row_mp_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    (hMatchLarge : ∀ args m Q X, fidBvaMatchLargeSpec args m Q X →
      Γ "full_bva_match_large_fid" [i64, i32, i32, i32] [.bool] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {row_off nrow_off par_off cur_qn best_lit nqn qi qw csz min_l min_d j :
      Val i32}
    {J : Cont [i32, i32]} {Jend : Cont []} {Jbr : Cont [i32]}
    {Jm : Cont [i32, i32, i32]} {Jm2 : Cont [i32]}
    {ar sb : List (BitVec 32)} {lmj : List (BitVec 8)} {res : List Nat} {step : Nat} {mj : Mem 64}
    (hcl : s.core.LengthsOk c) (hsc : s.scratch.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) (hdw : DenseWatchesInv F_cur s.core)
    (hl0 : s.core.cur_level = 0) (hdm : s.core.dense_mode ≠ 0#64)
    (hstep1 : 1 ≤ step) (hstep32 : step < 32)
    (_hrow_eq : row_off.toNat = 64 + (step - 1) * 256)
    (hnrow_eq : nrow_off.toNat = 64 + step * 256)
    (hpar_eq : par_off.toNat = 8256 + step * 256)
    (hscr16448 : 16448 ≤ c.scratch_cap)
    (har_l : ar.length = c.arena_cap) (hsb_l : sb.length = c.scratch_cap)
    (hlmj_l : lmj.length = 2 * c.max_vars)
    (hqi_lt : qi.toNat < cur_qn.toNat) (hnqn_lt : nqn.toNat < 256)
    (hw_ar : FullWitnessInv c F0 F_cur { s.core with arena := ar })
    (hnd_ar : FullArenaVarsNodup
      (FullState.mk { s.core with arena := ar } { s.scratch with scratch_buf := sb }))
    (hbvaq : FidFilterArBvaqInv c s ar sb nrow_off.toNat 0 nqn.toNat)
    (hqw_ref : qw.toNat ∈ fullArenaClauseRefsCore s.core)
    (hqw_ng : fullArenaClauseGarbCore s.core qw.toNat = false)
    (hqw_sz3 : 3 ≤ fullArenaClauseSize s qw.toNat)
    (hqw_sz256 : fullArenaClauseSize s qw.toNat ≤ 256)
    (hfr_mem : (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat ∈
      fullArenaClauseLits s qw.toNat)
    (hres_perm_f : res.Perm ((fullArenaClauseLits s qw.toNat).filter
      (· != (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat)))
    (hqw_perm : (fullArenaClauseLits s qw.toNat).Perm
      ((s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat :: res))
    (hbin_eq : (qw &&& 0x80000000#32) = 0#32)
    (hres_lt : ∀ x ∈ res, x < 2 * s.core.cur_vars)
    (hres_nd : (res.map (· / 2)).Nodup)
    (hres_ent : ∀ t < step, (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res)))
    (hqw_getD : s.scratch.scratch_buf[row_off.toNat + qi.toNat]?.getD 0#32 = qw)
    (hlmj_res : ∀ l < 2 * s.core.cur_vars, (lmj[l]?.getD 0#8 &&& 2#8) ≠ 0#8 → l ∈ res)
    (hmin_ok : min_l ≠ 0xFFFFFFFF#32 →
      min_l.toNat < 2 * s.core.cur_vars ∧ min_d.toNat = fullWatchSizeCore s.core min_l.toNat)
    (hfr_sb : ∀ idx < c.scratch_cap, ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 256) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 256) →
      sb[idx]? = s.scratch.scratch_buf[idx]?)
    (hent : ∀ nm < nqn.toNat, let pi := (sb[par_off.toNat + nm]?.getD 0#32).toNat
      pi < cur_qn.toNat ∧ ∃ res' : List Nat,
        (∀ x ∈ res', x < 2 * s.core.cur_vars) ∧ (res'.map (· / 2)).Nodup ∧
        M4BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res' ∧
        M4BvaRowEntryOk F_cur s best_lit.toNat (sb[nrow_off.toNat + nm]?.getD 0#32) res' ∧
        (∀ t < step, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res'))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res')))
    (hmj : (FullMem c (FullState.mk { s.core with arena := ar, lit_mark := lmj }
      { s.scratch with scratch_buf := sb }) ⋆ R) mj)
    (hJm2 : ∀ nqn2 ar2 sb2 mf2,
      nqn2.toNat ≤ 256 → FidFilterArBvaqInv c s ar2 sb2 nrow_off.toNat 0 nqn2.toNat →
      FullWitnessInv c F0 F_cur { s.core with arena := ar2 } → FullArenaVarsNodup
        (FullState.mk { s.core with arena := ar2 } { s.scratch with scratch_buf := sb2 }) →
      (∀ idx < c.scratch_cap, ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 256) →
        ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 256) →
        sb2[idx]? = s.scratch.scratch_buf[idx]?) →
      (∀ nm < nqn2.toNat, let pi := (sb2[par_off.toNat + nm]?.getD 0#32).toNat
        pi < cur_qn.toNat ∧ ∃ res' : List Nat,
          (∀ x ∈ res', x < 2 * s.core.cur_vars) ∧ (res'.map (· / 2)).Nodup ∧
          M4BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
            (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res' ∧
          M4BvaRowEntryOk F_cur s best_lit.toNat (sb2[nrow_off.toNat + nm]?.getD 0#32) res' ∧
          (∀ t < step, (cnfOfClauses F_cur).EntailsClause
            (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res'))) ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res'))) →
      (FullMem c (FullState.mk { s.core with arena := ar2, lit_mark := lmj }
        { s.scratch with scratch_buf := sb2 }) ⋆ R) mf2 →
      Jm2 (nqn2, ()) mf2) :
    wp Γ Q X (fidFilterRowMpExpr c.hdr c.pWvec c.pWstk c.pArena c.pLitMark c.pScratchBuf
      row_off nrow_off par_off cur_qn best_lit nqn qi qw csz min_l min_d j J Jend Jbr Jm Jm2)
      mj := by
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap har_b hscr_b
  have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len; have hws_len := hcl.wstk_len_arr
  have har_len := hcl.arena_len_arr; have hal_le := hcl.arena_len_le; have hwlen_le := hcl.wlen_le
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
  have hnqn1 : (nqn + 1#32).toNat = nqn.toNat + 1 := by simp only [bv_c0]; omega
  have hnrnq : (nrow_off + nqn).toNat = nrow_off.toNat + nqn.toNat := by simp only [bv_c0]; omega
  have hprnq : (par_off + nqn).toNat = par_off.toNat + nqn.toNat := by simp only [bv_c0]; omega
  have hnrnq_lt : (BitVec.setWidth 64 (nrow_off + nqn)).toNat < sb.length := by
    rw [hset, hnrnq, hsb_l]; omega
  have hprnq_lt : (BitVec.setWidth 64 (par_off + nqn)).toNat < sb.length := by
    rw [hset, hprnq, hsb_l]; omega
  have hqw_wf := hw.arena.refs_wf qw.toNat hqw_ref
  have ⟨hrefs_ar, hcl_ar⟩ := fidFilterArBvaqInv_congr hcl hw hbvaq
  have ⟨hqw_ng_ar, hqw_sz_ar, _⟩ := hcl_ar qw.toNat hqw_ref
  dsimp only [fidFilterRowMpExpr, eSkip, eLoad64, eLoad32, fidEGrp0_2, fidEGrpBody_0,
    fidEGrpBody_1, eGrp0_3, eThen, eElse, full_bva_filter_row_fid_body]
  c0_hsplit
  · have hmin_ne : min_l ≠ 0xFFFFFFFF#32 := by assumption
    obtain ⟨hml_lt, hmd_eq⟩ := hmin_ok hmin_ne
    have hml_bd := hdw.layout.bounds min_l.toNat hml_lt
    have hml_sl := hdw.slices min_l.toNat hml_lt
    have h2ml_n : (BitVec.setWidth 64 min_l <<< (1 : Nat)).toNat = 2 * min_l.toNat := by
      simp only [bv_c0]; omega
    have h2ml_mod : 2 * min_l.toNat % 2 ^ 64 = 2 * min_l.toNat := Nat.mod_eq_of_lt (by omega)
    have h2ml_wv : (BitVec.setWidth 64 min_l <<< (1 : Nat)).toNat < s.core.wvec.length := by
      rw [h2ml_n]; omega
    have hmoff_eq : (s.core.wvec[2 * min_l.toNat]'(by omega)).toNat =
        fullWatchOffCore s.core min_l.toNat := by
      unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    let moff0 := fullWatchOffCore s.core min_l.toNat
    let msz0 := fullWatchSizeCore s.core min_l.toNat
    have hm_end_mod : ((s.core.wvec[2 * min_l.toNat % 2 ^ 64]'(by
        rw [h2ml_mod]; omega)).toNat + min_d.toNat) % 2 ^ 64 = moff0 + msz0 := by
      simp only [h2ml_mod, hmoff_eq, hmd_eq]; exact Nat.mod_eq_of_lt (by omega)
    c0_hsteps_nogrp
    refine wp_join_state
      (α := BitVec 32 × BitVec 64 × List (BitVec 32) × List (BitVec 32))
      (fun st => (st.1, st.2.1, ()))
      (fun ⟨nqn2, _mp2, ar2, sb2⟩ mf2 =>
        nqn2.toNat ≤ 256 ∧ FidFilterArBvaqInv c s ar2 sb2 nrow_off.toNat 0 nqn2.toNat ∧
        FullWitnessInv c F0 F_cur { s.core with arena := ar2 } ∧ FullArenaVarsNodup
          (FullState.mk { s.core with arena := ar2 } { s.scratch with scratch_buf := sb2 }) ∧
        (∀ idx < c.scratch_cap, ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 256) →
          ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 256) →
          sb2[idx]? = s.scratch.scratch_buf[idx]?) ∧
        (∀ nm < nqn2.toNat, let pi := (sb2[par_off.toNat + nm]?.getD 0#32).toNat
          pi < cur_qn.toNat ∧ ∃ res' : List Nat,
            (∀ x ∈ res', x < 2 * s.core.cur_vars) ∧ (res'.map (· / 2)).Nodup ∧
            M4BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
              (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res' ∧
            M4BvaRowEntryOk F_cur s best_lit.toNat (sb2[nrow_off.toNat + nm]?.getD 0#32) res' ∧
            (∀ t < step, (cnfOfClauses F_cur).EntailsClause
              (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res'))) ∧
            (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res'))) ∧
        (FullMem c (FullState.mk { s.core with arena := ar2, lit_mark := lmj }
          { s.scratch with scratch_buf := sb2 }) ⋆ R) mf2)
      (fun _ ⟨nqn2, _mp2, ar2, sb2⟩ mf2 ⟨h1, h2, h3, h4, h5, h6, h7⟩ => by
        c0_hfast; exact hJm2 nqn2 ar2 sb2 mf2 h1 h2 h3 h4 h5 h6 h7)
      (fun Jmp hJmp => ?_)
    refine wp_loop_inv
      (fun (mp, ()) mmp =>
        moff0 ≤ mp.toNat ∧ mp.toNat ≤ moff0 + msz0 ∧ mmp = mj ∧
        DenseWatchSliceOk F_cur s.core min_l.toNat mp.toNat (moff0 + msz0 - mp.toNat))
      (fun (mp, ()) _ => moff0 + msz0 - mp.toNat)
      (fun JmpL hJmpL => by
        c0_hfast
        have h1 : (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 min_l <<<
            (1 : Nat)).toNat]'h2ml_wv)).toNat = moff0 := by
          simp only [h2ml_n, hset, hmoff_eq]; rfl
        dsimp only
        exact hJmpL (_, ()) mj ⟨by rw [h1]; exact Nat.le_refl _, by rw [h1]; omega, rfl,
          by simpa only [h1, Nat.add_sub_cancel_left] using hml_sl⟩)
      (fun JmpL (mp, ()) mmp ⟨hmp_ge, hmp_le, hmmp, hrem⟩ ihmp => ?_)
    rcases hmmp with rfl
    c0_hsplit
    · have hmp_lt : mp.toNat < moff0 + msz0 := by rw [← hm_end_mod]; assumption
      have hmp_ws : mp.toNat < s.core.wstk.length := by omega
      have hmp1_n : (mp + 1#64).toNat = mp.toNat + 1 := by simp only [bv_c0]; omega
      c0_hfast
      · have ⟨_, _, hrem_next⟩ :=
          FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hmp_ws (by assumption)
        exact ihmp (mp + 1#64, ()) mmp (by dsimp only; rw [hmp1_n]; omega)
          ⟨by rw [hmp1_n]; omega, by rw [hmp1_n]; omega, rfl,
           by rw [hmp1_n, show moff0 + msz0 - (mp.toNat + 1) =
                moff0 + msz0 - mp.toNat - 1 by omega]; exact hrem_next⟩
      · exact hJmp ⟨nqn, mp + 1#64, ar, sb⟩ mmp
          ⟨by omega, hbvaq, hw_ar, hnd_ar, hfr_sb, hent, hmj⟩
      · have ⟨h2le, hrem_next⟩ :=
          FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hmp_ws (by assumption)
        have hmp1_ws : mp.toNat + 1 < s.core.wstk.length := by omega
        have hmp1_ws' : (mp + 1#64).toNat < s.core.wstk.length := by rw [hmp1_n]; exact hmp1_ws
        have hmp1_mod : (mp.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = mp.toNat + 1 := by
          rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
        have ⟨_, hdr_ref, _⟩ :=
          FullBvaFwdHelpers.fwd_slice_occ_info hrem (by omega) hmp_ws hmp1_ws (by assumption)
        have hdr_wf := hw.arena.refs_wf _ hdr_ref
        have hmp2_n : (mp + 1#64 + 1#64).toNat = mp.toNat + 2 := by simp only [bv_c0]; omega
        let dr := s.core.wstk[mp.toNat + 1]'hmp1_ws
        have hdr_lt_ar : dr.toNat + 3 ≤ ar.length := by
          dsimp only [dr]; have := hdr_wf.1; have := hcl.arena_len_le; omega
        have hdr_eq : s.core.wstk[(mp + 1#64).toNat]'hmp1_ws' = dr := by
          dsimp only [dr]; simp only [hmp1_n]
        have hdr_mod : s.core.wstk[(mp.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(
            by rw [hmp1_mod]; exact hmp1_ws) = dr := by dsimp only [dr]; simp only [hmp1_mod]
        c0_call hMatchLarge
        have hres_nd_l : res.Nodup := nodup_of_map_div2 hres_nd
        have hqw_sz_res : fullArenaClauseSize
            (FullState.mk { s.core with arena := ar, lit_mark := lmj }
              { s.scratch with scratch_buf := sb }) qw.toNat = res.length + 1 := by
          change fullArenaClauseSizeCore { s.core with arena := ar } qw.toNat = _
          rw [hqw_sz_ar]
          have h1 := FullBvaFwdHelpers.fullArenaClauseLitsCore_length (k := s.core)
            (r := qw.toNat) (by have := hqw_wf.2.2.1; have := hqw_wf.2.2.2.1; omega)
          have h2 := hqw_perm.length_eq
          unfold fullArenaClauseLits at h2; simp only [List.length_cons] at h2; omega
        refine ⟨c, F0, F_cur, FullState.mk { s.core with arena := ar, lit_mark := lmj }
            { s.scratch with scratch_buf := sb }, R, res, rfl,
          ⟨{ hcl with arena_len_arr := har_l, lit_mark_len := hlmj_l },
           { hsc with scratch_buf_len := hsb_l }⟩,
          fullWitnessInv_with_litMark hw_ar lmj, hnd_ar, hl0, hdm,
          by change qw.toNat ∈ fullArenaClauseRefsCore { s.core with arena := ar }
             rw [hrefs_ar]; exact hqw_ref,
          by change fullArenaClauseGarbCore { s.core with arena := ar } qw.toNat = false
             rw [hqw_ng_ar]; exact hqw_ng,
          by show (s.core.wstk[(mp + 1#64).toNat]'hmp1_ws').toNat ∈ _
             rw [hdr_eq]; change dr.toNat ∈ fullArenaClauseRefsCore { s.core with arena := ar }
             rw [hrefs_ar]; exact hdr_ref,
          hres_nd_l, hres_lt, hqw_sz_res, hlmj_res, hmj, fun ok hok => ?_⟩
        c0_hfast
        · obtain ⟨hdr_ng_ar, hdr_nbvaq_h, hdr_sz_eq_ar, hbl_mem_ar, hdr_perm_ar,
            hdr_filt_ar, hbl_res_ent⟩ := hok (by assumption)
          have hdr_eq1 : s.core.wstk[(mp + (1 : BitVec 64)).toNat]'(by
              rw [show (1 : BitVec 64) = 1#64 from rfl, hmp1_n]; exact hmp1_ws) = dr := hdr_eq
          try rw [hdr_mod] at hdr_ng_ar hdr_nbvaq_h hdr_sz_eq_ar hbl_mem_ar
          try rw [hdr_mod] at hdr_perm_ar hdr_filt_ar
          try rw [hdr_eq1] at hdr_ng_ar hdr_nbvaq_h hdr_sz_eq_ar hbl_mem_ar
          try rw [hdr_eq1] at hdr_perm_ar hdr_filt_ar
          have ⟨hdr_ng_s, hdr_sz_s, hdr_lits_s⟩ := hcl_ar dr.toNat hdr_ref
          have hdr_ar_b : (BitVec.setWidth 64 (s.core.wstk[(mp.toNat +
              BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                rw [hmp1_mod]; exact hmp1_ws))).toNat < ar.length := by
            rw [hdr_mod, hset]; omega
          have hdr_ar_b' : (BitVec.setWidth 64 (s.core.wstk[(mp + 1#64).toNat]'(by
              rw [hmp1_n]; exact hmp1_ws))).toNat < ar.length := by
            rw [hdr_eq, hset]; omega
          c0_hfast
          have ⟨hbvaq1, hw1, hnd1, hfr1, hent1⟩ := fid_filter_row_large_upd hcl har_l hsb_l
            hw_ar hnd_ar hl0 hbvaq hnqn_lt (by omega) (by omega) (by omega) hrefs_ar
            hqw_ref hqw_ng hqw_sz3 hqw_sz256 hqw_sz_ar hfr_mem hres_perm_f hqw_perm
            hbin_eq hdr_ref hdr_lt_ar hdr_ng_s hdr_sz_s hdr_lits_s hdr_ng_ar hdr_nbvaq_h
            hdr_sz_eq_ar hbl_mem_ar hdr_perm_ar hdr_filt_ar hbl_res_ent hqi_lt hres_lt
            hres_nd hres_ent hqw_getD hfr_sb hent c.harena
          let ar1 := ar.set dr.toNat ((ar[dr.toNat]'(by omega)) ||| 0x02000000#32)
          let sb1 := (sb.set (nrow_off.toNat + nqn.toNat) dr).set (par_off.toNat + nqn.toNat) qi
          have hm1 : (FullMem c (FullState.mk { s.core with arena := ar1, lit_mark := lmj }
              { s.scratch with scratch_buf := sb1 }) ⋆ R) m := by
            dsimp only [ar1, sb1]
            try simp only [hdr_eq1] at hm
            simp only [hset, hnrnq, hprnq] at hm; exact hm
          exact hJmp ⟨nqn + 1#32, mp + 1#64 + 1#64, _, _⟩ m
            ⟨by rw [hnqn1]; omega, by rw [hnqn1]; exact hbvaq1, hw1, hnd1, hfr1,
             by rw [hnqn1]; exact hent1, hm1⟩
        · exact ihmp (mp + 1#64 + 1#64, ()) mmp (by dsimp only; rw [hmp2_n]; omega)
            ⟨by rw [hmp2_n]; omega, by rw [hmp2_n]; omega, rfl,
             by rw [hmp2_n, show moff0 + msz0 - (mp.toNat + 2) =
                  moff0 + msz0 - mp.toNat - 2 by omega]; exact hrem_next⟩
      · have ⟨h2le, hrem_next⟩ :=
          FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hmp_ws (by assumption)
        have hmp2_n : (mp + 1#64 + 1#64).toNat = mp.toNat + 2 := by simp only [bv_c0]; omega
        exact ihmp (mp + 1#64 + 1#64, ()) mmp (by dsimp only; rw [hmp2_n]; omega)
          ⟨by rw [hmp2_n]; omega, by rw [hmp2_n]; omega, rfl,
           by rw [hmp2_n, show moff0 + msz0 - (mp.toNat + 2) =
                moff0 + msz0 - mp.toNat - 2 by omega]; exact hrem_next⟩
    · c0_hfast
      exact hJmp ⟨nqn, mp, ar, sb⟩ mmp
        ⟨by omega, hbvaq, hw_ar, hnd_ar, hfr_sb, hent, hmj⟩
  · c0_hfast
    exact hJm2 nqn ar sb mj (by omega) hbvaq hw_ar hnd_ar hfr_sb hent hmj

/-- Parametric `Func.wp` proof for `full_bva_filter_row_fid`, certifying canonical
`FullM4Bva.m4BvaFilterRowSpec` while calling `full_bva_match_large_fid` at `fidBvaMatchLargeSpec`
with bit-25 (`PH_BVA_Q`) candidate suppression. -/
theorem full_bva_filter_row_fid_wp (Γ : Env)
    (hMatchLarge : ∀ args m Q X, fidBvaMatchLargeSpec args m Q X →
      Γ "full_bva_match_large_fid" [i64, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, m4BvaFilterRowSpec args m Q X →
      Func.wp Γ full_bva_filter_row_fid_body args m Q X := by
  rintro ⟨h, row_off, nrow_off, par_off, cur_qn, best_lit, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, step, rfl, hslen, hw, hnodup, hext, hl0, hdm, hstep1, hstep32, hscr16448,
     hrow_eq, hnrow_eq, hpar_eq, hqn_eq, hbl_lt, hmat, hlm_clr, hlm_b0, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap har_b hscr_b
  have hcl := hslen.core_ok; have hsc := hslen.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len; have hws_len := hcl.wstk_len_arr
  have har_len := hcl.arena_len_arr; have hal_le := hcl.arena_len_le; have hwlen_le := hcl.wlen_le
  have hlm_len := hcl.lit_mark_len; have hsb_len := hsc.scratch_buf_len
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
  have hdw : DenseWatchesInv F_cur s.core := by
    have h1 := hw.watches; unfold ModeWatchesInv at h1; rwa [ite_eq_right hdm] at h1
  have hrow_prev := hmat.2.2.2 (step - 1) (by omega)
  obtain ⟨hfr_lt, hqn_lo, hqn_hi, hrow_entries⟩ := hrow_prev
  rw [← hqn_eq] at hqn_lo hqn_hi hrow_entries; rw [← hrow_eq] at hrow_entries
  have hfr_b0 :
      (s.core.lit_mark[(s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat]?.getD 0#8 &&& 1#8) ≠
      0#8 := hlm_b0 (step - 1) (by omega)
  let mkSt (ar : List (BitVec 32)) (lm : List (BitVec 8)) (sb : List (BitVec 32)) : FullState :=
    { core := { s.core with arena := ar, lit_mark := lm }
      scratch := { s.scratch with scratch_buf := sb } }
  let FilterEntryOk (sb : List (BitVec 32)) (nqn : Nat) : Prop :=
    ∀ nm < nqn, let pi := (sb[par_off.toNat + nm]?.getD 0#32).toNat
      pi < cur_qn.toNat ∧
      ∃ res : List Nat, (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
        M4BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res ∧
        M4BvaRowEntryOk F_cur s best_lit.toNat (sb[nrow_off.toNat + nm]?.getD 0#32) res ∧
        (∀ t < step, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res))
  let SbFrame (sb : List (BitVec 32)) : Prop :=
    ∀ idx < c.scratch_cap, ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 256) →
      ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 256) → sb[idx]? = s.scratch.scratch_buf[idx]?
  c0_hsteps
  refine wp_loop_inv
    (fun (nqn, qi, ()) ml => ∃ ar sb, qi.toNat ≤ cur_qn.toNat ∧ nqn.toNat ≤ 256 ∧
      FidFilterArBvaqInv c s ar sb nrow_off.toNat 0 nqn.toNat ∧
      FullWitnessInv c F0 F_cur { s.core with arena := ar } ∧
      FullArenaVarsNodup (mkSt ar s.core.lit_mark sb) ∧ SbFrame sb ∧ FilterEntryOk sb nqn.toNat ∧
      (FullMem c (mkSt ar s.core.lit_mark sb) ⋆ R) ml)
    (fun (_, qi, _) _ => cur_qn.toNat - qi.toNat)
    (fun Jq hJq => by
      c0_hsteps
      exact hJq (0#32, 0#32, ()) m
        ⟨s.core.arena, s.scratch.scratch_buf, Nat.zero_le _, Nat.zero_le _,
         fidFilterArBvaqInv_init hslen nrow_off.toNat, hw, hnodup,
         fun _ _ _ _ => rfl, fun _ h => by simp only [bv_c0] at h; omega, hm⟩)
    (fun Jq (nqn, qi, ()) ml ⟨ar, sb, hqi_le, hnqn_le, hbvaq, hw_ar, hnd_ar, hfr_sb, hent, hml⟩
        ihq => ?_)
  dsimp only [mkSt] at hml
  have har_l := hbvaq.1; have hsb_l := hbvaq.2.1
  c0_hsteps_nogrp
  refine wp_join_state0 (α := Unit)
    (fun _ mf => mf = ml)
    (fun _ _ mf hmf => ?_)
    (fun Jend hJend => ?_)
  · rcases hmf with rfl
    refine wp_loop_inv
      (fun (ci, ()) mci => ∃ arci, ci.toNat ≤ nqn.toNat ∧
        FidFilterArBvaqInv c s arci sb nrow_off.toNat ci.toNat nqn.toNat ∧
        (FullMem c (mkSt arci s.core.lit_mark sb) ⋆ R) mci)
      (fun (ci, ()) _ => nqn.toNat - ci.toNat)
      (fun Jc hJc => by c0_hfast; exact hJc (0#32, ()) mf ⟨ar, Nat.zero_le _, hbvaq, hml⟩)
      (fun Jc (ci, ()) mci ⟨arci, hci_le, hbvaq_ci, hmci⟩ ihc => ?_)
    clear hm hml; dsimp only [mkSt] at hmci
    have harci_l := hbvaq_ci.1
    c0_hsteps_nogrp
    · have hci_lt : ci.toNat < nqn.toNat := by assumption
      have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by simp only [bv_c0]; omega
      have hnrci : (nrow_off + ci).toNat = nrow_off.toNat + ci.toNat := by simp only [bv_c0]; omega
      let dr := sb[nrow_off.toNat + ci.toNat]'(by omega)
      have hdr_eq : sb[(BitVec.setWidth 64 (nrow_off + ci)).toNat]'(by
          rw [hset, hnrci]; omega) = dr := by dsimp only [dr]; simp only [hset, hnrci]
      c0_hstep; c0_hsplit
      · have h0b : (dr &&& 0x80000000#32) = 0#32 := by
          have h1 : (sb[(BitVec.setWidth 64 (nrow_off + ci)).toNat]'(by
            rw [hset, hnrci]; omega) &&& 0x80000000#32) = 0#32 := by assumption
          rwa [hdr_eq] at h1
        have hdr_ref := (hbvaq_ci.2.2.2.1 ci.toNat (Nat.le_refl _) hci_lt (by
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact h0b)).1
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdr_ref
        have hdr_wf := hw.arena.refs_wf _ hdr_ref; have hstep := fidFilterArBvaqInv_clear_large
          har_len hbvaq_ci hci_lt (by omega) h0b (by omega)
        have hdr_ar_b : (BitVec.setWidth 64 (sb[(BitVec.setWidth 64 (nrow_off + ci)).toNat]'(by
            rw [hset, hnrci]; omega))).toNat < arci.length := by
          rw [hdr_eq, hset]; dsimp only [dr]; have := hdr_wf.1; have := hcl.arena_len_le; omega
        c0_hfast
        refine ihc (ci + 1#32, ()) m (by dsimp only; rw [hci1]; omega)
          ⟨_, by rw [hci1]; omega, by rw [hci1]; exact hstep, ?_⟩
        simp only [hset, hnrci] at hm; exact hm
      · have hbin : (sb[nrow_off.toNat + ci.toNat]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := by
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have h1 : (sb[(BitVec.setWidth 64 (nrow_off + ci)).toNat]'(by
            rw [hset, hnrci]; omega) &&& 0x80000000#32) ≠ 0#32 := by assumption
          rwa [hdr_eq] at h1
        c0_hfast
        exact ihc (ci + 1#32, ()) mci (by dsimp only; rw [hci1]; omega)
          ⟨arci, by rw [hci1]; omega,
           by rw [hci1]; exact fidFilterArBvaqInv_clear_bin hbvaq_ci hci_lt hbin, hmci⟩
    · have hci_eq : ci.toNat = nqn.toNat := by omega
      rw [hci_eq] at hbvaq_ci
      have har_rest : arci = s.core.arena := fidFilterArBvaqInv_done har_len hbvaq_ci
      rw [har_rest] at hmci
      exact hQ nqn sb mci ⟨hcl, { hsc with scratch_buf_len := hsb_l }⟩ hnqn_le hfr_sb hent hmci
  · c0_hsteps_nogrp
    · have hqi_lt : qi.toNat < cur_qn.toNat := by assumption
      have hnqn_lt : nqn.toNat < 256 := by
        have h1 : nqn.toNat < (256 : BitVec 32).toNat := by assumption
        simpa using h1
      have hqi1 : (qi + 1#32).toNat = qi.toNat + 1 := by simp only [bv_c0]; omega
      have hrqi : (row_off + qi).toNat = row_off.toNat + qi.toNat := by simp only [bv_c0]; omega
      have hnrnq : (nrow_off + nqn).toNat = nrow_off.toNat + nqn.toNat := by
        simp only [bv_c0]; omega
      have hprnq : (par_off + nqn).toNat = par_off.toNat + nqn.toNat := by
        simp only [bv_c0]; omega
      have hnqn1 : (nqn + 1#32).toNat = nqn.toNat + 1 := by simp only [bv_c0]; omega
      have hqw_sb_eq : sb[row_off.toNat + qi.toNat]? =
          s.scratch.scratch_buf[row_off.toNat + qi.toNat]? :=
        hfr_sb (row_off.toNat + qi.toNat) (by omega) (by omega) (by omega)
      let qw := s.scratch.scratch_buf[row_off.toNat + qi.toNat]'(by omega)
      have hqw_eq : sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
          rw [hset, hrqi]; omega) = qw := by
        have h1 : sb[row_off.toNat + qi.toNat]? = some qw := by
          rw [hqw_sb_eq, List.getElem?_eq_getElem (by omega)]
        rw [List.getElem?_eq_getElem (by omega)] at h1
        have h2 := Option.some.inj h1; simpa only [hset, hrqi] using h2
      have hrqi_mod : (row_off.toNat + qi.toNat) % 2 ^ 32 = row_off.toNat + qi.toNat :=
        Nat.mod_eq_of_lt (by omega)
      have hqw_mod : sb[(row_off.toNat + qi.toNat) % 2 ^ 32]'(by rw [hrqi_mod]; omega) = qw := by
        have h1 : sb[row_off.toNat + qi.toNat]? = some qw := by
          rw [hqw_sb_eq, List.getElem?_eq_getElem (by omega)]
        rw [List.getElem?_eq_getElem (by omega)] at h1
        have h2 := Option.some.inj h1; simpa only [hrqi_mod] using h2
      obtain ⟨res, hres_lt, hres_nd, hqw_ent, hres_ent, _⟩ := hrow_entries qi.toNat hqi_lt
      have hqw_getD : s.scratch.scratch_buf[row_off.toNat + qi.toNat]?.getD 0#32 = qw := by
        dsimp only [qw]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [hqw_getD] at hqw_ent; refine wp_join_state1 (t := i32)
        (α := BitVec 32 × List (BitVec 32) × List (BitVec 32)) (fun st => st.1)
        (fun ⟨nqn', ar', sb'⟩ mf =>
          nqn'.toNat ≤ 256 ∧ FidFilterArBvaqInv c s ar' sb' nrow_off.toNat 0 nqn'.toNat ∧
          FullWitnessInv c F0 F_cur { s.core with arena := ar' } ∧
          FullArenaVarsNodup (mkSt ar' s.core.lit_mark sb') ∧
          SbFrame sb' ∧ FilterEntryOk sb' nqn'.toNat ∧
          (FullMem c (mkSt ar' s.core.lit_mark sb') ⋆ R) mf)
        (fun _ ⟨nqn', ar', sb'⟩ mf ⟨hnqn', hbvaq', hw', hnd', hfr', hent', hmf⟩ => by
          c0_hfast
          exact ihq (nqn', qi + 1#32, ()) mf (by dsimp only; rw [hqi1]; omega)
            ⟨ar', sb', by rw [hqi1]; omega, hnqn', hbvaq', hw', hnd', hfr', hent', hmf⟩)
        (fun Jbr hJbr => ?_)
      c0_hsplit
      · have hbin_ne : (qw &&& 0x80000000#32) ≠ 0#32 := by
          have h1 : (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
            rw [hset, hrqi]; omega) &&& 0x80000000#32) ≠ 0#32 := by assumption
          rwa [hqw_eq] at h1
        unfold M4BvaRowEntryOk at hqw_ent; rw [ite_eq_left hbin_ne] at hqw_ent
        obtain ⟨hq_lt0, hres_eq, hfr_q⟩ := hqw_ent
        let q := qw &&& 0x7FFFFFFF#32
        have hq_lt : q.toNat < 2 * s.core.cur_vars := hq_lt0
        have hq_eq : sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
            rw [hset, hrqi]; omega) &&& 0x7FFFFFFF#32 = q := by rw [hqw_eq]
        have hq_mod : sb[(row_off.toNat + qi.toNat) % 2 ^ 32]'(by rw [hrqi_mod]; omega) &&&
            (2147483647 : BitVec 32) = q := by rw [hqw_mod]; rfl
        have h2q_mod : 2 * q.toNat % 2 ^ 64 = 2 * q.toNat := Nat.mod_eq_of_lt (by omega)
        have h2q_n : (BitVec.setWidth 64 q <<< (1 : Nat)).toNat = 2 * q.toNat := by c0_bound
        have h2q1_n : ((BitVec.setWidth 64 q <<< (1 : Nat)) + 1).toNat = 2 * q.toNat + 1 := by
          change ((BitVec.setWidth 64 q <<< (1 : Nat)) + 1#64).toNat = _; c0_bound
        have hq_bd := hdw.layout.bounds q.toNat hq_lt; have hq_sl := hdw.slices q.toNat hq_lt
        have hoff_eq : (s.core.wvec[2 * q.toNat]'(by omega)).toNat =
            fullWatchOffCore s.core q.toNat := by
          unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        have hsz_eq : (s.core.wvec[2 * q.toNat + 1]'(by omega)).toNat =
            fullWatchSizeCore s.core q.toNat := by
          unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        let qoff0 := fullWatchOffCore s.core q.toNat
        let qsz0 := fullWatchSizeCore s.core q.toNat
        have h2q_wvec : (BitVec.setWidth 64 (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
            rw [hset, hrqi]; omega) &&& 0x7FFFFFFF#32) <<< (1 : Nat)).toNat <
            s.core.wvec.length := by rw [hq_eq, h2q_n]; omega
        have h2q1_wvec : ((BitVec.setWidth 64 (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
            rw [hset, hrqi]; omega) &&& 0x7FFFFFFF#32) <<< (1 : Nat)) + 1).toNat <
            s.core.wvec.length := by rw [hq_eq, h2q1_n]; omega
        c0_hsteps_nogrp
        refine wp_join_state
          (α := BitVec 32 × BitVec 64 × List (BitVec 32)) (fun st => (st.1, st.2.1, ()))
          (fun ⟨nqn', _qp', sb'⟩ mf =>
            nqn'.toNat ≤ 256 ∧ FidFilterArBvaqInv c s ar sb' nrow_off.toNat 0 nqn'.toNat ∧
            SbFrame sb' ∧ FilterEntryOk sb' nqn'.toNat ∧
            (FullMem c (mkSt ar s.core.lit_mark sb') ⋆ R) mf)
          (fun _ ⟨nqn', _qp', sb'⟩ mf ⟨hnqn', hbvaq', hfr', hent', hmf⟩ => by
            c0_hfast
            exact hJbr ⟨nqn', ar, sb'⟩ mf ⟨hnqn', hbvaq', hw_ar, hnd_ar, hfr', hent', hmf⟩)
          (fun Jqp hJqp => ?_)
        refine wp_loop_inv
          (fun (qp, ()) mlp =>
            qoff0 ≤ qp.toNat ∧ qp.toNat ≤ qoff0 + qsz0 ∧ mlp = ml ∧
            DenseWatchSliceOk F_cur s.core q.toNat qp.toNat (qoff0 + qsz0 - qp.toNat))
          (fun (qp, ()) _ => qoff0 + qsz0 - qp.toNat)
          (fun Jp hJp => by
            c0_hfast
            have h1 : (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64
                (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
                  rw [hset, hrqi]; omega) &&& (2147483647 : BitVec 32)) <<< (1 : Nat)).toNat]'(by
                rw [show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl, hq_eq, h2q_n]
                omega))).toNat = qoff0 := by
              simp only [show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl, hq_eq]
              simp only [h2q_n, hset, hoff_eq]; rfl
            dsimp only
            exact hJp (_, ()) ml ⟨by rw [h1]; exact Nat.le_refl _, by rw [h1]; omega, rfl,
              by simpa only [h1, Nat.add_sub_cancel_left] using hq_sl⟩)
          (fun Jp (qp, ()) mlp ⟨hqp_ge, hqp_le, hmlp, hrem⟩ ihp => ?_)
        rcases hmlp with rfl
        clear hm
        c0_hsplit
        · have hqp_lt : qp.toNat < qoff0 + qsz0 := by
            have hqend_mod : ((s.core.wvec[2 * q.toNat % 2 ^ 64]'(by rw [h2q_mod]; omega)).toNat +
                (s.core.wvec[(2 * q.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                  rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega)).toNat) % 2 ^ 64 =
                qoff0 + qsz0 := by
              simp only [h2q_mod, show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
                Nat.mod_eq_of_lt (by omega : 2 * q.toNat + 1 < 2 ^ 64), hoff_eq, hsz_eq]
              exact Nat.mod_eq_of_lt (by omega)
            rw [← hqend_mod]
            simpa only [← hq_mod] using (by assumption : _)
          have hqp_ws : qp.toNat < s.core.wstk.length := by omega
          have hqp1_n : (qp + 1#64).toNat = qp.toNat + 1 := by simp only [bv_c0]; omega
          c0_hfast
          · have ⟨_, hq_bl_ent, _⟩ :=
              FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hqp_ws (by assumption)
            have hnw_bl : (s.core.wstk[qp.toNat]'hqp_ws &&& 0x7FFFFFFF#32) = best_lit := by
              assumption
            rw [hnw_bl] at hq_bl_ent
            have hbl_q_ent : (cnfOfClauses F_cur).EntailsClause
                (cnfClause [best_lit.toNat, q.toNat]) := bva_bin_swap_entails hq_bl_ent
            have ⟨hbvaq1, hfr1, hent1⟩ := fid_filter_row_bin_upd hsb_l hbvaq hnqn_lt (by omega)
              (by omega) (by omega) hbin_ne hq_lt hres_eq hfr_q hbl_q_ent hqi_lt hres_lt hres_nd
              (fun t ht => hres_ent t (by omega)) hqw_getD hfr_sb hent
            let sb1 := (sb.set (nrow_off.toNat + nqn.toNat) qw).set (par_off.toNat + nqn.toNat) qi
            have hm1 : (FullMem c (mkSt ar s.core.lit_mark sb1) ⋆ R) m := by
              dsimp only [mkSt, sb1]
              simp only [hqw_eq] at hm; simp only [hset, hnrnq, hprnq] at hm; exact hm
            exact hJqp ⟨nqn + 1#32, qp, sb1⟩ m
              ⟨by rw [hnqn1]; omega, by rw [hnqn1]; exact hbvaq1, hfr1,
               by rw [hnqn1]; exact hent1, hm1⟩
          · have ⟨_, _, hrem_next⟩ :=
              FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hqp_ws (by assumption)
            exact ihp (qp + 1#64, ()) mlp (by dsimp only; rw [hqp1_n]; omega)
              ⟨by rw [hqp1_n]; omega, by rw [hqp1_n]; omega, rfl,
               by rw [hqp1_n, show qoff0 + qsz0 - (qp.toNat + 1) = qoff0 + qsz0 - qp.toNat - 1
                    by omega]; exact hrem_next⟩
          · have ⟨h2le, hrem_next⟩ :=
              FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hqp_ws (by assumption)
            have hqp2_n : (qp + 2#64).toNat = qp.toNat + 2 := by simp only [bv_c0]; omega
            exact ihp (qp + 2#64, ()) mlp (by dsimp only; rw [hqp2_n]; omega)
              ⟨by rw [hqp2_n]; omega, by rw [hqp2_n]; omega, rfl,
               by rw [hqp2_n, show qoff0 + qsz0 - (qp.toNat + 2) = qoff0 + qsz0 - qp.toNat - 2
                    by omega]; exact hrem_next⟩
        · c0_hfast
          exact hJqp ⟨nqn, qp, sb⟩ mlp ⟨hnqn_le, hbvaq, hfr_sb, hent, hml⟩
      · have hbin_eq : (qw &&& 0x80000000#32) = 0#32 := by
          have h1 : (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
            rw [hset, hrqi]; omega) &&& 0x80000000#32) = 0#32 := by assumption
          rwa [hqw_eq] at h1
        unfold M4BvaRowEntryOk at hqw_ent; rw [ite_eq_right (fun h' => h' hbin_eq)] at hqw_ent
        obtain ⟨hqw_ref, hqw_ng, hqw_sz3, hqw_sz256, hfr_mem, hres_perm_f, hqw_perm⟩ := hqw_ent
        have hqw_wf := hw.arena.refs_wf qw.toNat hqw_ref
        have ⟨hrefs_ar, hcl_ar⟩ := fidFilterArBvaqInv_congr hcl hw hbvaq
        have ⟨hqw_ng_ar, hqw_sz_ar, hqw_lits_ar⟩ := hcl_ar qw.toNat hqw_ref
        have hqw2_lt : qw.toNat + 2 < ar.length := by have := hqw_wf.1; omega
        have hqw_sz_eq : (ar[qw.toNat + 2]'hqw2_lt).toNat =
            fullArenaClauseSizeCore s.core qw.toNat := by
          rw [← hqw_sz_ar]; unfold fullArenaClauseSizeCore
          rw [List.getElem?_eq_getElem hqw2_lt, Option.getD_some]
        let csz_bv := ar[qw.toNat + 2]'hqw2_lt
        have hcsz_nat : csz_bv.toNat = fullArenaClauseSizeCore s.core qw.toNat := hqw_sz_eq
        have hqw2_n : (BitVec.setWidth 64 qw + 2).toNat = qw.toNat + 2 := by
          change (BitVec.setWidth 64 qw + 2#64).toNat = _; simp only [bv_c0]; omega
        have hqw2_mod : (qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = qw.toNat + 2 := by
          rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
        have hcsz_mod : csz_bv = ar[(qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
            rw [hqw2_mod]; exact hqw2_lt) := by dsimp only [csz_bv]; simp only [hqw2_mod]
        have hqw2_ar : (BitVec.setWidth 64 (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
            rw [hset, hrqi]; omega)) + 2).toNat < ar.length := by
          rw [hqw_eq, hqw2_n, har_l]; have := hqw_wf.1; omega
        have hqw_lits_eq := fid_filter_row_ar_lits_eq hcl hw hbvaq hqw_ref
        c0_hsteps_nogrp
        refine wp_loop_inv
          (fun (min_l, min_d, j, ()) mj => ∃ lmj, j.toNat ≤ csz_bv.toNat ∧
            LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 j.toNat lmj ∧
            (∀ l < 2 * s.core.cur_vars, (lmj[l]?.getD 0#8 &&& 2#8) ≠ 0#8 → l ∈ res) ∧
            (min_l ≠ 0xFFFFFFFF#32 → min_l.toNat < 2 * s.core.cur_vars ∧
              min_d.toNat = fullWatchSizeCore s.core min_l.toNat) ∧
            (FullMem c (mkSt ar lmj sb) ⋆ R) mj)
          (fun (_, _, j, _) _ => csz_bv.toNat - j.toNat)
          (fun Jm hJm => by
            c0_hfast
            refine hJm (0xFFFFFFFF#32, 0xFFFFFFFF#32, 0#32, ()) ml
              ⟨s.core.lit_mark, Nat.zero_le _, lmBit2Inv_init hlm_len, fun l hl hne => ?_,
               fun h => absurd rfl h, hml⟩
            exact absurd (bv8_bit_zero_of_and_fe (hlm_clr l (by omega))).1 hne)
          (fun Jm (min_l, min_d, j, ()) mj ⟨lmj, hj_le, hlmj_inv, hlmj_res, hmin_ok, hmj⟩ ihm => ?_)
        clear hm hml; dsimp only [mkSt] at hmj
        have hlmj_l := hlmj_inv.1
        c0_hsplit
        · have hj_lt : j.toNat < csz_bv.toNat := by
            rw [hcsz_mod]
            simpa only [← hqw_mod] using (by assumption : _)
          have hj1 : (j + 1#32).toNat = j.toNat + 1 := by simp only [bv_c0]; omega
          have hqwj_n : (BitVec.setWidth 64 qw + 3 + BitVec.setWidth 64 j).toNat =
              qw.toNat + 3 + j.toNat := by
            change (BitVec.setWidth 64 qw + 3#64 + BitVec.setWidth 64 j).toNat = _
            simp only [bv_c0]; omega
          have hqwj_mod : (qw.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) % 2 ^ 64 =
              qw.toNat + 3 + j.toNat := by
            rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; omega
          have hqwj_lt : qw.toNat + 3 + j.toNat < s.core.arena.length := by
            have := hqw_wf.2.2.1; have := hqw_wf.2.2.2.1; omega
          have hl_eq : ar[qw.toNat + 3 + j.toNat]'(by omega) =
              s.core.arena[qw.toNat + 3 + j.toNat]'hqwj_lt := by
            have h1 := hqw_lits_eq j.toNat (by omega)
            rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hqwj_lt] at h1
            exact Option.some.inj h1
          have hl_mem : (s.core.arena[qw.toNat + 3 + j.toNat]'hqwj_lt).toNat ∈
              fullArenaClauseLitsCore s.core qw.toNat :=
            List.mem_of_getElem? (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem
              (by omega) (by omega))
          have hl_lt : (ar[qw.toNat + 3 + j.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
            rw [hl_eq]; exact hw.arena.lits_lt qw.toNat hqw_ref hqw_ng _ hl_mem
          have h2l1_n : ((BitVec.setWidth 64 (ar[qw.toNat + 3 + j.toNat]'(by omega)) <<<
              (1 : Nat)) + 1).toNat = 2 * (ar[qw.toNat + 3 + j.toNat]'(by omega)).toNat + 1 := by
            change ((BitVec.setWidth 64 _ <<< (1 : Nat)) + 1#64).toNat = _
            simp only [bv_c0]; omega
          have hw_get : (s.core.wvec[2 * (ar[qw.toNat + 3 + j.toNat]'(by omega)).toNat + 1]'(by
              omega)).toNat =
              fullWatchSizeCore s.core (ar[qw.toNat + 3 + j.toNat]'(by omega)).toNat := by
            unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have hqwj_ar : (BitVec.setWidth 64 (sb[(BitVec.setWidth 64
              (row_off + qi)).toNat]'(by rw [hset, hrqi]; omega)) + 3 +
              BitVec.setWidth 64 j).toNat < ar.length := by rw [hqw_eq, hqwj_n, har_l]; omega
          have hl_lm : (BitVec.setWidth 64 (ar[(BitVec.setWidth 64
              (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
                rw [hset, hrqi]; omega)) + 3 + BitVec.setWidth 64 j).toNat]'hqwj_ar)).toNat <
              lmj.length := by simp only [hqw_eq]; simp only [hqwj_n, hset]; omega
          have h2l1_wv : ((BitVec.setWidth 64 (ar[(BitVec.setWidth 64
              (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
                rw [hset, hrqi]; omega)) + 3 + BitVec.setWidth 64 j).toNat]'hqwj_ar) <<<
              (1 : Nat)) + 1).toNat < s.core.wvec.length := by
            simp only [hqw_eq]; simp only [hqwj_n, h2l1_n]; omega
          c0_hfast
          · have ⟨hstep2, hres_next⟩ := fid_filter_row_mark_step hlm_len hcv_le hfr_b0 hres_perm_f
              hlmj_inv hlmj_res (by omega) hqwj_lt hl_eq hl_mem hl_lt (by
                simp only [← hqwj_mod]; simpa only [← hqw_mod] using (by assumption : _))
            dsimp only at hm ⊢; simp only [hqw_eq] at hm; simp only [hqwj_n, hset] at hm
            try simp only [bv8_trunc_or_2] at hm
            try simp only [bv8_trunc_or_w] at hm
            refine ihm (_, _, j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
              ⟨_, by rw [hj1]; omega, by rw [hj1]; exact hstep2, hres_next, fun _ => ?_, hm⟩
            simp only [hqw_eq]; simp only [hqwj_n, h2l1_n]; exact ⟨hl_lt, hw_get⟩
          · have ⟨hstep2, hres_next⟩ := fid_filter_row_mark_step hlm_len hcv_le hfr_b0 hres_perm_f
              hlmj_inv hlmj_res (by omega) hqwj_lt hl_eq hl_mem hl_lt (by
                simp only [← hqwj_mod]; simpa only [← hqw_mod] using (by assumption : _))
            dsimp only at hm ⊢; simp only [hqw_eq] at hm; simp only [hqwj_n, hset] at hm
            try simp only [bv8_trunc_or_2] at hm
            try simp only [bv8_trunc_or_w] at hm
            refine ihm (_, _, j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
              ⟨_, by rw [hj1]; omega, by rw [hj1]; exact hstep2, hres_next, fun _ => ?_, hm⟩
            simp only [hqw_eq]; simp only [hqwj_n, h2l1_n]; exact ⟨hl_lt, hw_get⟩
          · have ⟨hstep2, hres_next⟩ := fid_filter_row_mark_step hlm_len hcv_le hfr_b0 hres_perm_f
              hlmj_inv hlmj_res (by omega) hqwj_lt hl_eq hl_mem hl_lt (by
                simp only [← hqwj_mod]; simpa only [← hqw_mod] using (by assumption : _))
            dsimp only at hm ⊢; simp only [hqw_eq] at hm; simp only [hqwj_n, hset] at hm
            try simp only [bv8_trunc_or_2] at hm
            try simp only [bv8_trunc_or_w] at hm
            exact ihm (min_l, min_d, j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
              ⟨_, by rw [hj1]; omega, by rw [hj1]; exact hstep2, hres_next, hmin_ok, hm⟩
          · exact ihm (min_l, min_d, j + 1#32, ()) mj (by dsimp only; rw [hj1]; omega)
              ⟨lmj, by rw [hj1]; omega, by rw [hj1]; exact lmBit2Inv_skip hlmj_inv, hlmj_res,
               hmin_ok, hmj⟩
        · have hj_eq : j.toNat = csz_bv.toNat := by
            rw [hcsz_mod] at hj_le ⊢
            have h1 : ¬ j.toNat < (ar[(qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
              rw [hqw2_mod]; exact hqw2_lt)).toNat := by
              simpa only [← hqw_mod] using (by assumption : _)
            omega
          rw [hj_eq] at hlmj_inv; c0_hsteps_nogrp
          refine wp_join_state1 (t := i32)
            (α := BitVec 32 × List (BitVec 32) × List (BitVec 32)) (fun st => st.1)
            (fun ⟨nqn2, ar2, sb2⟩ mf2 =>
              nqn2.toNat ≤ 256 ∧ FidFilterArBvaqInv c s ar2 sb2 nrow_off.toNat 0 nqn2.toNat ∧
              FullWitnessInv c F0 F_cur { s.core with arena := ar2 } ∧
              FullArenaVarsNodup (mkSt ar2 s.core.lit_mark sb2) ∧
              SbFrame sb2 ∧ FilterEntryOk sb2 nqn2.toNat ∧ (FullMem c (mkSt ar2 lmj sb2) ⋆ R) mf2)
            (fun _ ⟨nqn2, ar2, sb2⟩ mf2 ⟨hnqn2, hbvaq2, hw2, hnd2, hfr2, hent2, hmf2⟩ => ?_)
            (fun Jm2 hJm2 => ?_)
          · clear hmj hrow_entries hmat hlmj_res hmin_ok
            dsimp only [mkSt] at hmf2
            have har2_l := hbvaq2.1
            have har2_lits := fid_filter_row_ar_lits_eq hcl hw hbvaq2 hqw_ref
            refine wp_loop_inv
              (fun (k, ()) mk => ∃ lmk, k.toNat ≤ csz_bv.toNat ∧
                LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat k.toNat csz_bv.toNat lmk ∧
                (FullMem c (mkSt ar2 lmk sb2) ⋆ R) mk)
              (fun (k, ()) _ => csz_bv.toNat - k.toNat)
              (fun Jc2 hJc2 => by
                c0_hfast; exact hJc2 (0#32, ()) mf2 ⟨lmj, Nat.zero_le _, hlmj_inv, hmf2⟩)
              (fun Jc2 (k, ()) mk ⟨lmk, hk_le, hlmk_inv, hmk⟩ ihc2 => ?_)
            clear hmf2; dsimp only [mkSt] at hmk
            have hlmk_l := hlmk_inv.1
            c0_hsplit
            · have hk_lt : k.toNat < csz_bv.toNat := by
                rw [hcsz_mod]
                simpa only [← hqw_mod] using (by assumption : _)
              have hqwk_lt : qw.toNat + 3 + k.toNat < s.core.arena.length := by
                have := hqw_wf.2.2.1; have := hqw_wf.2.2.2.1; omega
              have hck_eq : ar2[qw.toNat + 3 + k.toNat]'(by omega) =
                  s.core.arena[qw.toNat + 3 + k.toNat]'hqwk_lt := by
                have h1 := har2_lits k.toNat (by omega)
                rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hqwk_lt] at h1
                exact Option.some.inj h1
              have hck_lt : (s.core.arena[qw.toNat + 3 + k.toNat]'hqwk_lt).toNat <
                  2 * s.core.cur_vars :=
                hw.arena.lits_lt qw.toNat hqw_ref hqw_ng _ (List.mem_of_getElem?
                  (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (by omega) (by omega)))
              have hk1 : (k + 1#32).toNat = k.toNat + 1 := by simp only [bv_c0]; omega
              have hidx_n : (BitVec.setWidth 64 qw + 3 + BitVec.setWidth 64 k).toNat =
                  qw.toNat + 3 + k.toNat := by
                change (BitVec.setWidth 64 qw + 3#64 + BitVec.setWidth 64 k).toNat = _
                simp only [bv_c0]; omega
              have hidx_ar : (BitVec.setWidth 64 (sb[(BitVec.setWidth 64
                  (row_off + qi)).toNat]'(by rw [hset, hrqi]; omega)) + 3 +
                  BitVec.setWidth 64 k).toNat < ar2.length := by rw [hqw_eq, hidx_n, har2_l]; omega
              have hck_lm : (BitVec.setWidth 64 (ar2[(BitVec.setWidth 64
                  (sb[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
                    rw [hset, hrqi]; omega)) + 3 + BitVec.setWidth 64 k).toNat]'hidx_ar)).toNat <
                  lmk.length := by simp only [hqw_eq]; simp only [hidx_n, hset, hck_eq]; omega
              c0_hfast
              simp only [hqw_eq] at hm; simp only [hidx_n, hset] at hm
              try simp only [bv8_trunc_and_fd] at hm
              try simp only [bv8_trunc_and_w] at hm
              have hstep : LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat (k.toNat + 1)
                  csz_bv.toNat (lmk.set (ar2[qw.toNat + 3 + k.toNat]'(by omega)).toNat
                    ((lmk[(ar2[qw.toNat + 3 + k.toNat]'(by omega)).toNat]'(by
                      rw [hck_eq]; omega)) &&& 0xFD#8)) := by
                have h0 := lmBit2Inv_clear_step hlm_len
                  (fun l hl => (bv8_bit_zero_of_and_fe (hlm_clr l hl)).1)
                  hlmk_inv hk_lt hqwk_lt (by omega)
                simpa only [← hck_eq] using h0
              exact ihc2 (k + 1#32, ()) m (by dsimp only; rw [hk1]; omega)
                ⟨_, by rw [hk1]; omega, by rw [hk1]; exact hstep, hm⟩
            · have hk_eq : k.toNat = csz_bv.toNat := by
                rw [hcsz_mod] at hk_le ⊢
                have h1 : ¬ k.toNat < (ar[(qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                  rw [hqw2_mod]; exact hqw2_lt)).toNat := by
                  simpa only [← hqw_mod] using (by assumption : _)
                omega
              rw [hk_eq] at hlmk_inv
              have hlm_rest : lmk = s.core.lit_mark := lmBit2Inv_done hlm_len hlmk_inv
              rw [hlm_rest] at hmk; c0_hfast
              exact hJbr ⟨nqn2, ar2, sb2⟩ mk ⟨hnqn2, hbvaq2, hw2, hnd2, hfr2, hent2, hmk⟩
          · clear hrow_entries hmat hlm_b0 hlm_clr hqw_lits_eq hqw_lits_ar
            dsimp only; simp only [hqw_eq]
            have hmp := fid_filter_row_mp_wp (Γ := Γ) (Q := Q) (X := X) hMatchLarge
              (J := Jq) (Jend := Jend) (Jbr := Jbr) (Jm := Jm) (Jm2 := Jm2)
              (csz := csz_bv) (j := j)
              hcl hsc hw hdw hl0 hdm hstep1 hstep32 hrow_eq hnrow_eq hpar_eq hscr16448
              har_l hsb_l hlmj_l hqi_lt hnqn_lt hw_ar hnd_ar hbvaq hqw_ref hqw_ng hqw_sz3 hqw_sz256
              hfr_mem hres_perm_f hqw_perm hbin_eq hres_lt hres_nd
              (fun t ht => hres_ent t (by omega)) hqw_getD hlmj_res hmin_ok hfr_sb hent hmj
              (fun nqn2 ar2 sb2 mf2 h1 h2 h3 h4 h5 h6 h7 =>
                hJm2 ⟨nqn2, ar2, sb2⟩ mf2 ⟨h1, h2, h3, h4, h5, h6, h7⟩)
            dsimp only [fidFilterRowMpExpr, eSkip, eLoad64, eLoad32, fidEGrp0_2, fidEGrpBody_0,
              fidEGrpBody_1, eGrp0_3, eThen, eElse, full_bva_filter_row_fid_body] at hmp
            exact hmp
    · exact hJend () ml rfl
    · exact hJend () ml rfl

end LeanQbe.T.Examples.Kissat.FullM7FidelityCore
