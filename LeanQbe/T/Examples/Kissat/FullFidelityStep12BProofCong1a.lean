/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep12BProofSpec
import LeanQbe.T.Examples.Kissat.FullCongLemmas1
import LeanQbe.T.Examples.Kissat.FullCongLemmas2
import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas1
import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof2a
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat Fidelity Step 12B — Congruence Proofs Part 1a (`FullFidelityStep12BProofCong1a`)

Parametric `(Γ : Env)` `Func.wp` proofs (`public section`, `0` `@[expose]` on theorems/lemmas,
`0` `import all`, `std3`, `XPost`-polymorphic) for:
1. `full_cong_enq_var_s12b_wp` (`step12BCongEnqVarSpec`, dynamic `occ_bkt ≤ 1,048,576`)
2. `full_cong_and_match_s12b_wp` (`step12BCongAndMatchSpec`, `O(ea + ua)` `lit_mark` + `u32`
   counter up to `congruenceandarity = 1,000,000`)
3. `full_cong_extract_and_clause_fid_s12b_wp` (`step12BCongExtractAndClauseSpec`, single-pass
   `O(D)` marked `WATCHES(not_lhs)` scan with inner tick metering & `tag = 3` wide-AND emission)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep12B

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
open LeanQbe.T.Examples.Kissat.FullM8FidV12
open LeanQbe.T.Examples.Kissat.FullFidelityCong
open scoped LeanQbe.T.Examples.Kissat.FullM3CongBva.M3HeadTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6CongSubst.M6HeadTactics
open scoped FullArenaTactics Full.FullCongTactics
open Kraken.Bedrock2.Test

/-! ## 1. Local Helpers -/

section Helpers

private theorem s12b_bv64_addk_lt_of {x : BitVec 64} {k : Nat} (hk : k < 2 ^ 64)
    (h : x.toNat + k < 2 ^ 64) : (x + BitVec.ofNat 64 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt h]

private theorem s12b_bv32_add1_lt_of {x : BitVec 32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem s12b_getElem?_eq_some_of_getD {α : Type _} [Inhabited α] {l : List α}
    {i : Nat} {v : α} (hi : i < l.length) (h : l[i]?.getD default = v) : l[i]? = some v := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some] at h
  rw [List.getElem?_eq_getElem hi, h]

private theorem s12b_getElem_of_getD {α : Type _} [Inhabited α] {xs : List α} {i : Nat}
    {v : α} (hi : i < xs.length) (h : xs[i]?.getD default = v) : xs[i]'hi = v := by
  rwa [List.getElem?_eq_getElem hi, Option.getD_some] at h

private theorem step12BCtrlLayout_frame_refl {c : FullCfg} {scr : List (BitVec 32)}
    {g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    (hlen : scr.length = c.scratch_cap)
    (h : Step12BCtrlLayout c scr g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz) :
    scr[ctrl_off]? = some (BitVec.ofNat 32 occ_bkt) ∧
    scr[ctrl_off + 1]? = some (BitVec.ofNat 32 bkt_off) ∧
    scr[ctrl_off + 2]? = some (BitVec.ofNat 32 inq_off) ∧
    scr[ctrl_off + 3]? = some (BitVec.ofNat 32 q_off) ∧
    scr[ctrl_off + 4]? = scr[ctrl_off + 4]? ∧
    scr[ctrl_off + 6]? = some (BitVec.ofNat 32 ht_off) ∧
    scr[ctrl_off + 7]? = some (BitVec.ofNat 32 ht_sz) ∧
    (∀ idx, idx ≠ ctrl_off + 5 →
      ¬ (q_off ≤ idx ∧ idx < q_off + occ_bkt) →
      ¬ (inq_off ≤ idx ∧ idx < inq_off + occ_bkt) → scr[idx]? = scr[idx]?) := by
  rcases h with ⟨h1, h2, _, _, s0, s1, s2, s3, s6, s7, _⟩
  exact ⟨s12b_getElem?_eq_some_of_getD (by omega) s0,
    s12b_getElem?_eq_some_of_getD (by omega) s1,
    s12b_getElem?_eq_some_of_getD (by omega) s2,
    s12b_getElem?_eq_some_of_getD (by omega) s3, rfl,
    s12b_getElem?_eq_some_of_getD (by omega) s6,
    s12b_getElem?_eq_some_of_getD (by omega) s7, fun _ _ _ _ => rfl⟩

private theorem s12b_fullWitnessInv_with_lm {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (lm' : List (BitVec 8)) :
    FullWitnessInv c F0 F_cur { k with lit_mark := lm' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

private theorem s12b_fullDenseInvW_with_lm_scr_rsz {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {lm' : List (BitVec 8)} {scr' : List (BitVec 32)} {rsz' : BitVec 64}
    (hlm : lm'.length = 2 * c.max_vars) (hscr : scr'.length = c.scratch_cap)
    (hclr : FullLitMarksClear c { s with core := { s.core with lit_mark := lm' } }) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with lit_mark := lm' }
        scratch := { s.scratch with scratch_buf := scr', res_sz := rsz' } } :=
  ⟨⟨{ hd.1.core_ok with lit_mark_len := hlm }, { hd.1.scratch_ok with scratch_buf_len := hscr }⟩,
   s12b_fullWitnessInv_with_lm hd.2.1 lm', hclr, hd.2.2.2.1,
   fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem s12b_filter_length_le_range {n : Nat} (p : Nat → Bool) :
    ((List.range n).filter p).length ≤ n := by
  calc ((List.range n).filter p).length
      ≤ (List.range n).length := List.length_filter_le p (List.range n)
    _ = n := List.length_range

private theorem s12b_filter_empty_eq_zero {n : Nat} {p : Nat → Bool}
    (h : ∀ x < n, p x = false) : ((List.range n).filter p).length = 0 := by
  have he : (List.range n).filter p = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx; rw [List.mem_range] at hx; rw [h x hx]; decide
  rw [he]; rfl

private theorem s12b_bv8_and3_eq1_ne0 {v : BitVec 8} (h : (v &&& 3#8) = 1#8) : v ≠ 0#8 := by
  intro h0; rw [h0] at h; cases h

private theorem s12b_bv8_and3_eq1_and2_eq0 {v : BitVec 8} (h : (v &&& 3#8) = 1#8) :
    (v &&& 2#8) = 0#8 := by
  have hall : ∀ x : BitVec 8, (x &&& 3#8) = 1#8 → (x &&& 2#8) = 0#8 := by decide
  exact hall v h

private theorem s12b_bv8_or2_and2_ne0 (v : BitVec 8) : ((v ||| 2#8) &&& 2#8) ≠ 0#8 := by
  have hall : ∀ x : BitVec 8, ((x ||| 2#8) &&& 2#8) ≠ 0#8 := by decide
  exact hall v

private theorem s12b_bv8_and5_c0 :
    ∀ x : BitVec 8,
      BitVec.setWidth 8 (BitVec.setWidth 32 x &&& 5#32) = x &&& 5#8 := by
  decide

private theorem s12b_bv8_or2_c0 :
    ∀ x : BitVec 8,
      BitVec.setWidth 8 (BitVec.setWidth 32 x ||| 2#32) = x ||| 2#8 := by
  decide

private theorem s12b_bv8_and5_and2_eq0 (v : BitVec 8) : ((v &&& 5#8) &&& 2#8) = 0#8 := by
  have hall : ∀ x : BitVec 8, ((x &&& 5#8) &&& 2#8) = 0#8 := by decide
  exact hall v

private theorem s12b_zext32_bv8_eq : ∀ (x y : BitVec 8),
    x.setWidth 32 = y.setWidth 32 → x = y := by decide

private theorem s12b_zext32_bv8_ne : ∀ (x y : BitVec 8),
    x.setWidth 32 ≠ y.setWidth 32 → x ≠ y := by decide

private theorem s12b_zext32_bv8_and3_eq1 : ∀ x : BitVec 8,
    (x.setWidth 32 &&& 3#32) = 1#32 → (x &&& 3#8) = 1#8 := by decide

private theorem s12b_mword_arity {n : Nat} (hn : n ≤ 1000000) :
    step12BGateArity (if n ≤ 64 then BitVec.ofNat 32 n
      else (3#32 <<< 28) ||| BitVec.ofNat 32 n) = n := by
  by_cases hle64 : n ≤ 64
  · rw [ite_eq_left hle64]
    have hne3 : (BitVec.ofNat 32 n >>> 28) ≠ 3#32 := by
      intro h3; have h := congrArg BitVec.toNat h3
      rw [BitVec.toNat_ushiftRight, bv32_ofNat_toNat (by omega),
        Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by omega)] at h
      simp at h
    rw [step12BGateArity_of_ne3 hne3, BitVec.toNat_and, bv32_ofNat_toNat (by omega),
      show (0xFF#32 : BitVec 32).toNat = 255 from rfl]
    simpa [Nat.mod_eq_of_lt (show n < 256 by omega)] using Nat.and_two_pow_sub_one_eq_mod n 8
  · rw [ite_eq_right hle64]
    have hlt28 : n < 2 ^ 28 := by omega
    have htag3 : (((3#32 <<< 28) ||| BitVec.ofNat 32 n) >>> 28) = 3#32 := by
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
      by_cases hk4 : k < 4
      · have h28k : 28 + k < 32 := by omega
        have hu0 : (BitVec.ofNat 32 n).getLsbD (28 + k) = false := by
          rw [BitVec.getLsbD_ofNat]; simp only [h28k, decide_true, Bool.true_and]
          exact m6_testBit_false_of_lt (Nat.lt_of_lt_of_le hlt28
            (Nat.pow_le_pow_right (by decide) (by omega)))
        rw [hu0]; simp [h28k, show ¬(28 + k < 28) by omega, show 28 + k - 28 = k by omega]
      · have h32 : ¬(28 + k < 32) := by omega
        have h30 : (3#32 : BitVec 32).getLsbD k = false := by
          rw [BitVec.getLsbD]
          exact m6_testBit_false_of_lt (Nat.lt_of_lt_of_le (by decide : 3 < 2 ^ 4)
            (Nat.pow_le_pow_right (by decide) (by omega)))
        have hu0 : (BitVec.ofNat 32 n).getLsbD (28 + k) = false := by
          rw [BitVec.getLsbD_ofNat]; simp [h32]
        simp [h32, h30, hu0]
    rw [step12BGateArity_of_eq3 htag3]
    have hmask_bit : ∀ j : Fin 32,
        (0x0FFFFFFF#32 : BitVec 32).getLsbD j.val = decide (j.val < 28) := by decide
    have hmask : (((3#32 <<< 28) ||| BitVec.ofNat 32 n) &&& 0x0FFFFFFF#32) =
        BitVec.ofNat 32 n := by
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
        hmask_bit ⟨k, hk⟩]
      by_cases hk28 : k < 28
      · simp [hk28]
      · have hu0 : (BitVec.ofNat 32 n).getLsbD k = false := by
          rw [BitVec.getLsbD_ofNat]; simp only [hk, decide_true, Bool.true_and]
          exact m6_testBit_false_of_lt (Nat.lt_of_lt_of_le hlt28
            (Nat.pow_le_pow_right (by decide) (by omega)))
        simp [hk28, hu0]
    rw [hmask, bv32_ofNat_toNat (by omega)]

private theorem s12b_bv32_xor1_inj {a b : BitVec 32} (h : (a ^^^ 1#32).toNat = (b ^^^ 1#32).toNat) :
    a.toNat = b.toNat := by
  have hbv : a ^^^ 1#32 = b ^^^ 1#32 := BitVec.eq_of_toNat_eq h
  have h1 : a = b := by
    have := congrArg (· ^^^ 1#32) hbv
    simpa [BitVec.xor_assoc] using this
  exact congrArg BitVec.toNat h1

private theorem s12b_dense_slice_step {F_cur : List (List Nat)} {k : FullCoreState}
    {a p rem : Nat} (hslice : DenseWatchSliceOk F_cur k a p rem) (hpos : 0 < rem) :
    ∃ w0 : BitVec 32, k.wstk[p]? = some w0 ∧
      ((w0 &&& 0x80000000#32) ≠ 0#32 ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [a, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
        DenseWatchSliceOk F_cur k a (p + 1) (rem - 1) ∨
       (w0 &&& 0x80000000#32) = 0#32 ∧ 2 ≤ rem ∧
        DenseWatchSliceOk F_cur k a (p + 2) (rem - 2)) := by
  cases hslice with
  | empty => omega
  | bin hp hf _ _ hent hrest => exact ⟨_, hp, Or.inl ⟨hf, hent, hrest⟩⟩
  | occ hp _ hf _ _ _ hrest => exact ⟨_, hp, Or.inr ⟨hf, by omega, hrest⟩⟩

private abbrev MarkSupp (base : List (BitVec 32)) (usz maxv : Nat)
    (lm : List (BitVec 8)) : Prop :=
  ∀ l < 2 * maxv, lm[l]?.getD 0#8 ≠ 0#8 →
    ∃ m < usz, l = ((base[m]?.getD 0#32) ^^^ 1#32).toNat

private abbrev MarkBit2Clear (base : List (BitVec 32)) (usz : Nat)
    (lm : List (BitVec 8)) : Prop :=
  ∀ m < usz, (lm[((base[m]?.getD 0#32) ^^^ 1#32).toNat]?.getD 0#8 &&& 2#8) = 0#8

end Helpers

/-! ## 2. `full_cong_enq_var_s12b_wp` (`step12BCongEnqVarSpec`) -/

theorem full_cong_enq_var_s12b_wp (_Γ : Env) :
    ∀ a m Q X, step12BCongEnqVarSpec a m Q X →
      Func.wp _Γ fidStep12BCongEnqVarFn.body a m Q X := by
  rintro ⟨h, ctrl_off, v, ⟨⟩⟩ m0 Q X ⟨c, s, g_len, ht_off, ht_sz, R, rfl, hlen, hq0, hm0, hQ⟩
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx
  have hscrl0 := hlen.scratch_ok.scratch_buf_len
  unfold fidStep12BCongEnqVarFn; dsimp only
  m6_split_fast
  · m6_steps
    refine hQ s.scratch.scratch_buf m0 hscrl0 hq0 (fun _ => rfl)
      (fun o b i q hlay => step12BCtrlLayout_frame_refl hscrl0 hlay) hm0
  · have hco_lt : ctrl_off.toNat < c.scratch_cap := by
      first
      | (simp only [BitVec.ule, decide_eq_false_iff_not, BitVec.toNat_ofNat,
           Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64)] at hc; omega)
      | (simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
           Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64)] at hc; exact hc)
    m6_split_fast
    · m6_steps
      refine hQ s.scratch.scratch_buf m0 hscrl0 hq0 (fun hcap => absurd hcap (by omega))
        (fun o b i q hlay => step12BCtrlLayout_frame_refl hscrl0 hlay) hm0
    · obtain ⟨occ_bkt, bkt_off, inq_off, q_off, hlay⟩ := hq0.elim
        (fun hcap => absurd hcap (by omega)) id
      have hlay_dup := hlay
      rcases hlay with ⟨h_co_cap, h_co8, hg_co, hg24, h_occ, h_bkt, h_inq, h_q, h_ht_o, h_ht_s,
        h_opos, h_ole, hpow, h_hpos, h_oq, h_qi, h_ib, h_bh, h_hc, h_qh, h_ql, h_qok⟩
      unfold step12BOccBktMax at h_ole
      have hco_n : ctrl_off.toNat < s.scratch.scratch_buf.length := by omega
      have hco2_n : (ctrl_off + 2#64).toNat = ctrl_off.toNat + 2 :=
        s12b_bv64_addk_lt_of (by decide) (by omega)
      have hco3_n : (ctrl_off + 3#64).toNat = ctrl_off.toNat + 3 :=
        s12b_bv64_addk_lt_of (by decide) (by omega)
      have hco4_n : (ctrl_off + 4#64).toNat = ctrl_off.toNat + 4 :=
        s12b_bv64_addk_lt_of (by decide) (by omega)
      have hco5_n : (ctrl_off + 5#64).toNat = ctrl_off.toNat + 5 :=
        s12b_bv64_addk_lt_of (by decide) (by omega)
      have hco2_arr : (ctrl_off + 2#64).toNat < s.scratch.scratch_buf.length := by omega
      have hco3_arr : (ctrl_off + 3#64).toNat < s.scratch.scratch_buf.length := by omega
      have hco4_arr : (ctrl_off + 4#64).toNat < s.scratch.scratch_buf.length := by omega
      have hco5_arr : (ctrl_off + 5#64).toNat < s.scratch.scratch_buf.length := by omega
      have hs0 : s.scratch.scratch_buf[ctrl_off.toNat]'hco_n = BitVec.ofNat 32 occ_bkt :=
        s12b_getElem_of_getD hco_n h_occ
      have hs2 : s.scratch.scratch_buf[(ctrl_off + 2#64).toNat]'hco2_arr =
          BitVec.ofNat 32 inq_off :=
        s12b_getElem_of_getD hco2_arr (by rw [hco2_n]; exact h_inq)
      have hs3 : s.scratch.scratch_buf[(ctrl_off + 3#64).toNat]'hco3_arr = BitVec.ofNat 32 q_off :=
        s12b_getElem_of_getD hco3_arr (by rw [hco3_n]; exact h_q)
      have hocc_eq : (s.scratch.scratch_buf[ctrl_off.toNat]'hco_n).toNat = occ_bkt := by
        rw [hs0, bv32_ofNat_toNat (by omega)]
      let b := v &&& (s.scratch.scratch_buf[ctrl_off.toNat]'hco_n - 1#32)
      have hb_lt : b.toNat < occ_bkt := by
        have := m6_bv32_and_sub1_lt (x := v) (n := s.scratch.scratch_buf[ctrl_off.toNat]'hco_n)
          (by rw [hocc_eq]; exact h_opos)
        rwa [hocc_eq] at this
      have hinqb_n :
          ((s.scratch.scratch_buf[(ctrl_off + 2#64).toNat]'hco2_arr).setWidth 64 +
            b.setWidth 64).toNat = inq_off + b.toNat := by
        rw [hs2, BitVec.toNat_add, bv_zext32_toNat, bv_zext32_toNat, bv32_ofNat_toNat (by omega)]
        exact Nat.mod_eq_of_lt (by omega)
      have hinqb_arr : ((s.scratch.scratch_buf[(ctrl_off + 2#64).toNat]'hco2_arr).setWidth 64 +
          b.setWidth 64).toNat < s.scratch.scratch_buf.length := by
        rw [hinqb_n]; omega
      m6_split_fast
      · clear hc; m6_split_fast
        · have hql_lt :
              (s.scratch.scratch_buf[(ctrl_off + 5#64).toNat]'hco5_arr).toNat < occ_bkt := by
            simp only [BitVec.ult, decide_eq_true_eq] at hc
            rwa [hocc_eq] at hc
          let q_head := s.scratch.scratch_buf[(ctrl_off + 4#64).toNat]'hco4_arr
          let q_len := s.scratch.scratch_buf[(ctrl_off + 5#64).toNat]'hco5_arr
          have hql_v : q_len.toNat < occ_bkt := hql_lt
          let tail := (q_head + q_len) &&& (s.scratch.scratch_buf[ctrl_off.toNat]'hco_n - 1#32)
          have htail_lt : tail.toNat < occ_bkt := by
            have := m6_bv32_and_sub1_lt (x := q_head + q_len)
              (n := s.scratch.scratch_buf[ctrl_off.toNat]'hco_n) (by rw [hocc_eq]; exact h_opos)
            rwa [hocc_eq] at this
          have hqh_v : q_head.toNat < occ_bkt := by
            dsimp only [q_head]; rw [← Option.getD_some (a := _[ _ ]) (b := 0#32),
              ← List.getElem?_eq_getElem hco4_arr, hco4_n]; exact h_qh
          have htail_mod : tail.toNat = (q_head.toNat + q_len.toNat) % occ_bkt := by
            dsimp only [tail]; rw [hs0, step12B_and_sub1_u32_eq_mod hpow]
            have hsum : (q_head + q_len).toNat = q_head.toNat + q_len.toNat := by
              rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
            rw [hsum]
          have hqt_n : ((s.scratch.scratch_buf[(ctrl_off + 3#64).toNat]'hco3_arr).setWidth 64 +
              tail.setWidth 64).toNat = q_off + tail.toNat := by
            rw [hs3, BitVec.toNat_add, bv_zext32_toNat, bv_zext32_toNat,
              bv32_ofNat_toNat (by omega)]
            exact Nat.mod_eq_of_lt (by omega)
          have hqt_arr : ((s.scratch.scratch_buf[(ctrl_off + 3#64).toNat]'hco3_arr).setWidth 64 +
              tail.setWidth 64).toNat < s.scratch.scratch_buf.length := by
            rw [hqt_n]; omega
          have hql1 : (q_len + 1#32).toNat = q_len.toNat + 1 := s12b_bv32_add1_lt_of (by omega)
          let scr1 := s.scratch.scratch_buf.set (inq_off + b.toNat) 1#32
          let scr2 := scr1.set (q_off + tail.toNat) b
          let scr3 := scr2.set (ctrl_off.toNat + 5) (q_len + 1#32)
          have hscrl3 : scr3.length = c.scratch_cap := by simp [scr3, scr2, scr1, hscrl0]
          have hql_n : q_len.toNat =
              (s.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat := by
            dsimp only [q_len]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            exact congrArg BitVec.toNat (list_getElem_congr hco5_n hco5_arr (by omega))
          have hqh_n : q_head.toNat =
              (s.scratch.scratch_buf[ctrl_off.toNat + 4]?.getD 0#32).toNat := by
            dsimp only [q_head]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            exact congrArg BitVec.toNat (list_getElem_congr hco4_n hco4_arr (by omega))
          have hsame_idx : ∀ i < 8, i ≠ 5 → scr3[ctrl_off.toNat + i]? =
              s.scratch.scratch_buf[ctrl_off.toNat + i]? := fun i hi hne5 => by
            dsimp only [scr3, scr2, scr1]
            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
              List.getElem?_set_ne (by omega)]
          have h5_set : scr3[ctrl_off.toNat + 5]?.getD 0#32 = q_len + 1#32 := by
            dsimp only [scr3]; rw [List.getElem?_set_self (by simp [scr2, scr1, hscrl0]; omega),
              Option.getD_some]
          have hlay3 : Step12BCtrlLayout c scr3 g_len ctrl_off.toNat occ_bkt bkt_off inq_off q_off
              ht_off ht_sz := by
            refine step12BCtrlLayout_same_tail hlay_dup (hscrl3.trans hscrl0.symm) ?_ hsame_idx ?_
            · rw [h5_set, hql1]; omega
            · intro k hk; rw [h5_set, hql1] at hk
              have he4 := hsame_idx 4 (by decide) (by decide)
              rw [he4]
              have hq_idx_lt : q_off + (q_head.toNat + k) % occ_bkt < inq_off + b.toNat := by
                have := Nat.mod_lt (q_head.toNat + k) h_opos; omega
              dsimp only [scr3, scr2, scr1]
              rw [← hqh_n, List.getElem?_set_ne (by omega)]
              by_cases hkt : (q_head.toNat + k) % occ_bkt = tail.toNat
              · rw [hkt, List.getElem?_set_self (by simp [hscrl0]; omega), Option.getD_some]
                exact hb_lt
              · have hk_ne : k ≠ q_len.toNat := fun he => hkt (by rw [he, htail_mod])
                rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), hqh_n]
                exact h_qok k (by rw [← hql_n]; omega)
          clear hc
          have hinqb_idx :
              (BitVec.setWidth 64 s.scratch.scratch_buf[(ctrl_off + 2).toNat] +
                BitVec.setWidth 64
                  (v &&& s.scratch.scratch_buf[BitVec.toNat ctrl_off] - 1)).toNat =
                inq_off + b.toNat := hinqb_n
          m6_let; refine wp_store_sep (FullArenaTactics.c0_store_full_scratch_buf 1#32
            (by change (BitVec.setWidth 64 s.scratch.scratch_buf[(ctrl_off + 2).toNat] +
                    BitVec.setWidth 64
                      (v &&& s.scratch.scratch_buf[BitVec.toNat ctrl_off] - 1)).toNat <
                  s.scratch.scratch_buf.length
                rw [hinqb_idx]; omega) hm0) ?_
          intro m1 hm1
          have hqt_arr1 : (q_off + tail.toNat) < scr1.length := by simp [scr1, hscrl0]; omega
          have hco5_arr2 : (ctrl_off.toNat + 5) < scr2.length := by simp [scr2, scr1]; omega
          have hhm1 : (FullMem c { s with scratch := { s.scratch with scratch_buf := scr1 } } ⋆ R)
              m1 := by dsimp only [scr1]; rw [← hinqb_idx]; exact hm1
          have hqt_idx :
              (BitVec.setWidth 64 s.scratch.scratch_buf[(ctrl_off + 3).toNat] +
                BitVec.setWidth 64
                  (q_head + q_len &&& s.scratch.scratch_buf[BitVec.toNat ctrl_off] - 1)).toNat =
                q_off + tail.toNat := hqt_n
          m6_let; refine wp_store_sep (FullArenaTactics.c0_store_full_scratch_buf b
            (by change (BitVec.setWidth 64 s.scratch.scratch_buf[(ctrl_off + 3).toNat] +
                    BitVec.setWidth 64
                      (q_head + q_len &&& s.scratch.scratch_buf[BitVec.toNat ctrl_off] -
                        1)).toNat < scr1.length
                rw [hqt_idx]; exact hqt_arr1) hhm1) ?_
          intro m2 hm2
          have hhm2 : (FullMem c { s with scratch := { s.scratch with scratch_buf := scr2 } } ⋆ R)
              m2 := by dsimp only [scr2]; rw [← hqt_idx]; exact hm2
          have hco5_idx : (ctrl_off + 5).toNat = ctrl_off.toNat + 5 := hco5_n
          m6_let; refine wp_store_sep (FullArenaTactics.c0_store_full_scratch_buf (q_len + 1#32)
            (by rw [hco5_idx]; exact hco5_arr2) hhm2) ?_
          intro m3 hm3
          have hhm3 : (FullMem c { s with scratch := { s.scratch with scratch_buf := scr3 } } ⋆ R)
              m3 := by dsimp only [scr3]; rw [← hco5_idx]; exact hm3
          m6_steps
          refine hQ scr3 m3 hscrl3 (Or.inr ⟨occ_bkt, bkt_off, inq_off, q_off, hlay3⟩)
            (fun hcap => absurd hcap (by omega)) (fun o1 b1 i1 q1 hlay1 => ?_) hhm3
          obtain ⟨rfl, rfl, rfl, rfl, _, _⟩ := step12BCtrlLayout_unique hlay_dup hlay1
          refine ⟨(hsame_idx 0 (by decide) (by decide)).trans
              (s12b_getElem?_eq_some_of_getD (by omega) h_occ),
            (hsame_idx 1 (by decide) (by decide)).trans
              (s12b_getElem?_eq_some_of_getD (by omega) h_bkt),
            (hsame_idx 2 (by decide) (by decide)).trans
              (s12b_getElem?_eq_some_of_getD (by omega) h_inq),
            (hsame_idx 3 (by decide) (by decide)).trans
              (s12b_getElem?_eq_some_of_getD (by omega) h_q),
            hsame_idx 4 (by decide) (by decide),
            (hsame_idx 6 (by decide) (by decide)).trans
              (s12b_getElem?_eq_some_of_getD (by omega) h_ht_o),
            (hsame_idx 7 (by decide) (by decide)).trans
              (s12b_getElem?_eq_some_of_getD (by omega) h_ht_s),
            fun idx hne5 hnq hni => ?_⟩
          dsimp only [scr3, scr2, scr1]
          have hne_q : q_off + tail.toNat ≠ idx := fun h => hnq (h ▸ ⟨by omega, by omega⟩)
          have hne_i : inq_off + b.toNat ≠ idx := fun h => hni (h ▸ ⟨by omega, by omega⟩)
          rw [List.getElem?_set_ne hne5.symm, List.getElem?_set_ne hne_q,
            List.getElem?_set_ne hne_i]
        · m6_steps
          refine hQ s.scratch.scratch_buf m0 hscrl0 (Or.inr ⟨occ_bkt, bkt_off, inq_off, q_off,
            hlay_dup⟩) (fun hcap => absurd hcap (by omega))
            (fun o1 b1 i1 q1 hl => ?_) hm0
          obtain ⟨rfl, rfl, rfl, rfl, _, _⟩ := step12BCtrlLayout_unique hlay_dup hl
          exact step12BCtrlLayout_frame_refl hscrl0 hl
      · m6_steps
        refine hQ s.scratch.scratch_buf m0 hscrl0 (Or.inr ⟨occ_bkt, bkt_off, inq_off, q_off,
          hlay_dup⟩) (fun hcap => absurd hcap (by omega))
          (fun o1 b1 i1 q1 hl => ?_) hm0
        obtain ⟨rfl, rfl, rfl, rfl, _, _⟩ := step12BCtrlLayout_unique hlay_dup hl
        exact step12BCtrlLayout_frame_refl hscrl0 hl

/-! ## 3. `full_cong_and_match_s12b_wp` (`step12BCongAndMatchSpec`) -/

theorem full_cong_and_match_s12b_wp (Γ : Env)
    (hFind : ∀ a m Q X, FullCongSpecs.fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, step12BCongAndMatchSpec a m Q X →
      Func.wp Γ fidStep12BCongAndMatchFn.body a m Q X := by
  rintro ⟨h, ent, ua, ⟨⟩⟩ m0 Q X
    ⟨maxA, c, F0, F_cur, s, scr0, g_len, R, hmaxA, rfl, hlen, hw, hmk0, hcl0, hrepr0, hg_cap,
     hpref, hgat, htag03, hua_cv, hm0, hQ⟩
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx
  unfold step12BCongAndArityMax at hmaxA
  have hcv_le := hlen.core_ok.cur_vars_le
  have hrl0 := hlen.core_ok.repr_len
  have hlml0 := hlen.core_ok.lit_mark_len
  have htmpl0 := hlen.core_ok.tmp_len_arr
  have hscrl0 := hlen.scratch_ok.scratch_buf_len
  have hvl0 := hlen.core_ok.vals_len
  let cv := s.core.cur_vars
  obtain ⟨lhs_ent, mword, he0, he1, _, hbd_e, hea_cv, hea_max, hrhs_e, hsem_e⟩ := hgat
  have htag03' : (mword >>> 28) = 0#32 ∨ (mword >>> 28) = 3#32 := by
    rwa [he1, Option.getD_some] at htag03
  have hand_e : AndGateDef (cnfOfClauses F_cur) lhs_ent.toNat
      (((scr0.drop (ent.toNat + 2)).take (step12BGateArity mword)).map BitVec.toNat) := by
    rcases hsem_e with ⟨_, hand⟩ | ⟨ht1, _⟩ | ⟨ht2, _⟩
    · exact hand
    · rcases htag03' with h0 | h3
      · have : (mword >>> 28).toNat = 0 := by rw [h0]; rfl
        omega
      · have : (mword >>> 28).toNat = 3 := by rw [h3]; rfl
        omega
    · rcases htag03' with h0 | h3
      · have : (mword >>> 28).toNat = 0 := by rw [h0]; rfl
        omega
      · have : (mword >>> 28).toNat = 3 := by rw [h3]; rfl
        omega
  let rhs := ((scr0.drop (ent.toNat + 2)).take (step12BGateArity mword)).map BitVec.toNat
  have hrl_rhs : rhs.length = step12BGateArity mword := by
    simp only [rhs, List.length_map, List.length_take, List.length_drop]
    rcases Nat.eq_zero_or_pos (step12BGateArity mword) with hz | hpos
    · exact Nat.min_eq_left (by omega)
    · obtain ⟨_, hr, _⟩ := hrhs_e (step12BGateArity mword - 1) (by omega)
      have := (List.getElem?_eq_some_iff.mp hr).1; omega
  have hnl_eq : (BitVec.ofNat 64 cv <<< (1 : Nat)).toNat = 2 * cv := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]
  have hret_false0 : Q (false, ()) m0 :=
    hQ false s.core.repr s.core.lit_mark m0 hrl0 hlml0 hmk0 hrepr0 (fun h => by cases h) hm0
  unfold fidStep12BCongAndMatchFn; dsimp only
  m6_split_fast
  · m6_steps; exact hret_false0
  have h2_le_ua : 2 ≤ ua.toNat := by
    simp only [BitVec.ult, decide_eq_false_iff_not] at hc; bv_omega
  clear hc; m6_split_fast
  · m6_steps; exact hret_false0
  have hua_le_max : ua.toNat ≤ 1000000 := by
    simp only [BitVec.ult, decide_eq_false_iff_not] at hc; bv_omega
  clear hc; m6_split_fast
  · m6_steps; exact hret_false0
  clear hc
  have he1_n : (ent.setWidth 64 + 1).toNat = ent.toNat + 1 := by
    rw [BitVec.toNat_add, bv_zext32_toNat, show (1 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have he1_arr : (ent.setWidth 64 + 1).toNat < s.scratch.scratch_buf.length := by omega
  have hst_e1 : s.scratch.scratch_buf[(ent.setWidth 64 + 1).toNat]'he1_arr = mword := by
    have h := (hpref (ent.toNat + 1) (by omega)).trans he1
    rw [← he1_n, List.getElem?_eq_getElem he1_arr] at h; exact Option.some.inj h
  m6_to_group
  refine wp_join_group (ts := [i32])
    (fun (ea, ()) mea => mea = m0 ∧ ea.toNat = step12BGateArity mword) ?_
    (fun Jea hJea => by
      m6_split_fast
      · have h3 : mword >>> 28 = 3#32 := by
          have := beq_iff_eq.mp hc; rwa [hst_e1] at this
        m6_steps; rw [hst_e1]
        exact hJea (mword &&& 0x0FFFFFFF#32, ()) m0 ⟨rfl, (step12BGateArity_of_eq3 h3).symm⟩
      · have hne3 : mword >>> 28 ≠ 3#32 := by
          have := beq_eq_false_iff_ne.mp hc; rwa [hst_e1] at this
        m6_steps; rw [hst_e1]
        exact hJea (mword &&& 0xFF#32, ()) m0 ⟨rfl, (step12BGateArity_of_ne3 hne3).symm⟩)
  rintro _ ⟨ea, ⟨⟩⟩ mea ⟨hmea, hea_eq⟩; subst mea
  m6_split_fast
  · m6_steps; exact hret_false0
  clear hc; m6_split_fast
  · m6_steps; exact hret_false0
  clear hc; m6_split_fast
  · m6_steps; exact hret_false0
  clear hc; m6_steps
  -- Loop 1: mark `tmp[0..ua)` in `lit_mark` and count `distinct_ua`
  refine wp_loop_inv (ts := [i32, i32])
    (fun (dist_ua, k, ()) mk => ∃ lm1 : List (BitVec 8),
      lm1.length = 2 * c.max_vars ∧ k.toNat ≤ ua.toNat ∧
      dist_ua.toNat = ((List.range (2 * cv)).filter (fun l => lm1[l]?.getD 0#8 == 1#8)).length ∧
      (∀ r < k.toNat, (s.core.tmp[r]?.getD 0#32).toNat < 2 * cv) ∧
      (∀ l < 2 * c.max_vars,
        lm1[l]?.getD 0#8 = 0#8 ∨ (l < 2 * cv ∧ lm1[l]?.getD 0#8 = 1#8)) ∧
      (∀ l < 2 * cv,
        lm1[l]?.getD 0#8 = 1#8 ↔ ∃ r < k.toNat, (s.core.tmp[r]?.getD 0#32).toNat = l) ∧
      (FullMem c { s with core := { s.core with lit_mark := lm1 } } ⋆ R) mk)
    (fun (_, k, ()) _ => ua.toNat - k.toNat)
    (fun J1 hJ1 => by
      m6_let; refine hJ1 (0#32, 0#32, ()) m0
        ⟨s.core.lit_mark, hlml0, Nat.zero_le _, ?_, fun _ h => absurd h (Nat.not_lt_zero _),
         fun l hl => Or.inl (hmk0.2 l hl), fun l hl => ?_, hm0⟩
      · exact (s12b_filter_empty_eq_zero fun x hx => by
          rw [hmk0.2 x (by omega)]; decide).symm
      · constructor
        · intro h1; rw [hmk0.2 l (by omega)] at h1; cases h1
        · rintro ⟨_, hr, _⟩; exact absurd hr (Nat.not_lt_zero _))
    (fun J1 (dist_ua, k, ()) mk ⟨lm1, hlml1, hk_le, hdist_eq, htmp_bd, hlm1_dom, hlm1_iff, hmk1⟩
      ih1 => ?_)
  m6_split_fast
  · have hk_lt : k.toNat < ua.toNat := by simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
    have hk_tmp : (k.setWidth 64).toNat < s.core.tmp.length := by rw [bv_zext32_toNat]; omega
    let tl := s.core.tmp[(k.setWidth 64).toNat]'hk_tmp
    have htl_eq : tl = s.core.tmp[k.toNat]?.getD 0#32 := by
      dsimp only [tl]; rw [List.getElem?_eq_getElem (by omega : k.toNat < s.core.tmp.length),
        Option.getD_some]; exact list_getElem_congr (bv_zext32_toNat k) _ _
    have hk1_n : (k + 1#32).toNat = k.toNat + 1 := s12b_bv32_add1_lt_of (by omega)
    clear hc; m6_split_fast
    · -- OOB `tl >= nlits`: clean `lm[tmp[0..k-1]] = 0` and return `false`
      clear hc; m6_steps
      refine wp_loop_inv (ts := [i32])
        (fun (ci, ()) mc => ∃ lmc : List (BitVec 8),
          lmc.length = 2 * c.max_vars ∧ ci.toNat ≤ k.toNat ∧
          (∀ l < 2 * c.max_vars, lmc[l]?.getD 0#8 = 0#8 ∨
            ∃ r, ci.toNat ≤ r ∧ r < k.toNat ∧ (s.core.tmp[r]?.getD 0#32).toNat = l) ∧
          (FullMem c { s with core := { s.core with lit_mark := lmc } } ⋆ R) mc)
        (fun (ci, ()) _ => k.toNat - ci.toNat)
        (fun Jc hJc => by
          m6_let; refine hJc (0#32, ()) mk ⟨lm1, hlml1, Nat.zero_le _, fun l hl => ?_, hmk1⟩
          rcases hlm1_dom l hl with h0 | ⟨hl_cv, h1⟩
          · exact Or.inl h0
          · obtain ⟨r, hr, heq⟩ := (hlm1_iff l hl_cv).mp h1
            exact Or.inr ⟨r, Nat.zero_le _, hr, heq⟩)
        (fun Jc (ci, ()) mc ⟨lmc, hlmlc, hci_le, hlmc_inv, hmc⟩ ihc => ?_)
      m6_split_fast
      · have hci_lt : ci.toNat < k.toNat := by
          simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
        have hci1_n : (ci + 1#32).toNat = ci.toNat + 1 := s12b_bv32_add1_lt_of (by omega)
        have hci_tmp : (ci.setWidth 64).toNat < s.core.tmp.length := by rw [bv_zext32_toNat]; omega
        let tc := s.core.tmp[(ci.setWidth 64).toNat]'hci_tmp
        have htc_eq : tc = s.core.tmp[ci.toNat]?.getD 0#32 := by
          dsimp only [tc]; rw [List.getElem?_eq_getElem (by omega : ci.toNat < s.core.tmp.length),
            Option.getD_some]; exact list_getElem_congr (bv_zext32_toNat ci) _ _
        have htc_lt : tc.toNat < 2 * cv := by rw [htc_eq]; exact htmp_bd ci.toNat hci_lt
        have htc_lm : (tc.setWidth 64).toNat < lmc.length := by rw [bv_zext32_toNat]; omega
        clear hc; m6_steps
        let lmc' := lmc.set (tc.setWidth 64).toNat 0#8
        exact ihc (ci + 1#32, ()) m (by dsimp only; omega)
          ⟨lmc', by simp [lmc', hlmlc], by omega, fun l hl => by
            dsimp only [lmc']
            by_cases hlt : l = (tc.setWidth 64).toNat
            · left; rw [hlt, List.getElem?_set_self htc_lm, Option.getD_some]
            · rw [List.getElem?_set_ne (Ne.symm hlt)]
              rcases hlmc_inv l hl with h0 | ⟨r, hr1, hr2, hr3⟩
              · exact Or.inl h0
              · right; refine ⟨r, ?_, hr2, hr3⟩
                have hne : r ≠ ci.toNat := fun he => by
                  subst he; apply hlt; rw [bv_zext32_toNat, htc_eq, hr3]
                omega, hm⟩
      · have hci_eq : ci.toNat = k.toNat := by
          simp only [BitVec.ult, decide_eq_false_iff_not] at hc; omega
        have hclr : FullLitMarksClear c { s with core := { s.core with lit_mark := lmc } } :=
          ⟨hmk0.1, fun l hl => by
            rcases hlmc_inv l hl with h0 | ⟨r, hr1, hr2, _⟩
            · exact h0
            · omega⟩
        clear hc; m6_steps
        exact hQ false s.core.repr lmc mc hrl0 hlmlc hclr hrepr0 (fun h => by cases h) hmc
    · have htl_lt : tl.toNat < 2 * cv := by
        simp only [BitVec.ule, decide_eq_false_iff_not, bv_zext32_toNat] at hc
        change ¬ (BitVec.ofNat 64 cv <<< (1 : Nat)).toNat ≤ tl.toNat at hc
        rw [hnl_eq] at hc; omega
      have htl_lm : (tl.setWidth 64).toNat < lm1.length := by rw [bv_zext32_toNat]; omega
      have htl_lm' : tl.toNat < lm1.length := by rw [bv_zext32_toNat] at htl_lm; exact htl_lm
      have hdist_le : dist_ua.toNat ≤ 2 * cv := by
        rw [hdist_eq]; exact s12b_filter_length_le_range _
      have hd1_n : (dist_ua + 1#32).toNat = dist_ua.toNat + 1 := s12b_bv32_add1_lt_of (by omega)
      clear hc; m6_to_group
      refine wp_join_group (ts := [i32])
        (fun (dist', ()) md => ∃ lm1' : List (BitVec 8),
          lm1'.length = 2 * c.max_vars ∧
          dist'.toNat = ((List.range (2 * cv)).filter (fun l => lm1'[l]?.getD 0#8 == 1#8)).length ∧
          (∀ l < 2 * c.max_vars,
            lm1'[l]?.getD 0#8 = 0#8 ∨ (l < 2 * cv ∧ lm1'[l]?.getD 0#8 = 1#8)) ∧
          (∀ l < 2 * cv, lm1'[l]?.getD 0#8 = 1#8 ↔
            ∃ r < (k + 1#32).toNat, (s.core.tmp[r]?.getD 0#32).toNat = l) ∧
          (FullMem c { s with core := { s.core with lit_mark := lm1' } } ⋆ R) md)
        (fun _ ⟨dist', ⟨⟩⟩ md ⟨lm1', hlml1', hdist', hdom', hiff', hmd⟩ => by
          m6_steps
          exact ih1 (dist', k + 1#32, ()) md (by dsimp only; omega)
            ⟨lm1', hlml1', by omega, hdist', fun r hr => by
              rw [hk1_n] at hr
              by_cases hrk : r = k.toNat
              · subst hrk; rwa [← htl_eq]
              · exact htmp_bd r (by omega),
             hdom', hiff', hmd⟩) ?_
      intro Jm1 hJm1; m6_split_fast
      · have hlm_tl0 : lm1[tl.toNat]?.getD 0#8 = 0#8 := by
          have h0 : lm1[(tl.setWidth 64).toNat]'htl_lm = 0#8 :=
            s12b_zext32_bv8_eq _ 0#8 (beq_iff_eq.mp hc)
          rw [List.getElem?_eq_getElem htl_lm', Option.getD_some,
            ← list_getElem_congr (bv_zext32_toNat tl) htl_lm htl_lm']
          exact h0
        clear hc; m6_steps
        let lm1' := lm1.set (tl.setWidth 64).toNat 1#8
        have hlm1'_set : lm1' = lm1.set tl.toNat 1#8 := by dsimp only [lm1']; rw [bv_zext32_toNat]
        refine hJm1 (dist_ua + 1#32, ()) m ⟨lm1', by simp [lm1', hlml1], ?_, ?_, ?_, hm⟩
        · rw [hd1_n, hdist_eq, hlm1'_set]
          exact (filter_length_flip_one (x0 := tl.toNat) (List.range (2 * cv)) List.nodup_range
            (List.mem_range.mpr htl_lt)
            (by rw [hlm_tl0]; decide)
            (by rw [List.getElem?_set_self htl_lm', Option.getD_some]; decide)
            (fun y _ hne => by rw [List.getElem?_set_ne hne.symm])).symm
        · intro l hl; rw [hlm1'_set]
          by_cases hltl : l = tl.toNat
          · subst hltl; right; rw [List.getElem?_set_self htl_lm', Option.getD_some]
            exact ⟨htl_lt, rfl⟩
          · rw [List.getElem?_set_ne (Ne.symm hltl)]; exact hlm1_dom l hl
        · intro l hl; rw [hlm1'_set, hk1_n]
          by_cases hltl : l = tl.toNat
          · subst hltl; rw [List.getElem?_set_self htl_lm', Option.getD_some]
            exact ⟨fun _ => ⟨k.toNat, by omega, congrArg BitVec.toNat htl_eq.symm⟩, fun _ => rfl⟩
          · rw [List.getElem?_set_ne (Ne.symm hltl), hlm1_iff l hl]
            constructor
            · rintro ⟨r, hr, heq⟩; exact ⟨r, by omega, heq⟩
            · rintro ⟨r, hr, heq⟩
              have hrne : r ≠ k.toNat := fun he => hltl (by rw [← heq, he, ← htl_eq])
              exact ⟨r, by omega, heq⟩
      · have hlm_tl1 : lm1[tl.toNat]?.getD 0#8 = 1#8 := by
          have hne0 : lm1[tl.toNat]?.getD 0#8 ≠ 0#8 := by
            rw [List.getElem?_eq_getElem htl_lm', Option.getD_some,
              ← list_getElem_congr (bv_zext32_toNat tl) htl_lm htl_lm']
            exact s12b_zext32_bv8_ne _ 0#8 (beq_eq_false_iff_ne.mp hc)
          rcases hlm1_dom tl.toNat (by omega) with h0 | ⟨_, h1⟩
          · exact absurd h0 hne0
          · exact h1
        clear hc; m6_steps
        refine hJm1 (dist_ua, ()) mk ⟨lm1, hlml1, hdist_eq, hlm1_dom, fun l hl => ?_, hmk1⟩
        rw [hlm1_iff l hl, hk1_n]
        constructor
        · rintro ⟨r, hr, heq⟩; exact ⟨r, by omega, heq⟩
        · rintro ⟨r, hr, heq⟩
          by_cases hrk : r = k.toNat
          · subst hrk; rw [← htl_eq] at heq; subst heq
            exact (hlm1_iff tl.toNat htl_lt).mp hlm_tl1
          · exact ⟨r, by omega, heq⟩
  -- Post Loop 1: `k = ua`, `lm1` has marked all `tmp[0..ua)`
  have hk_eq : k.toNat = ua.toNat := by
    simp only [BitVec.ult, decide_eq_false_iff_not] at hc; omega
  rw [hk_eq] at htmp_bd hlm1_iff
  clear hc; m6_to_group
  -- Loop 2: scan `ent`'s RHS literals `j = 0..ea-1`
  refine wp_loop_break_group (brkTs := [.bool, i32, i32]) (lpTs := [i32, i32])
    (fun (ok, matched, _, ()) mb => ∃ reprb lmb,
      reprb.length = 2 * c.max_vars ∧ lmb.length = 2 * c.max_vars ∧
      FullCongReprInv F_cur (2 * cv) reprb ∧
      (∀ l < 2 * c.max_vars, lmb[l]?.getD 0#8 = 0#8 ↔ lm1[l]?.getD 0#8 = 0#8) ∧
      (ok = true →
        matched.toNat = ((List.range (2 * cv)).filter (fun l => lmb[l]?.getD 0#8 == 2#8)).length ∧
        (∀ l < 2 * cv, lmb[l]?.getD 0#8 = 2#8 →
          lm1[l]?.getD 0#8 = 1#8 ∧
          ∃ p < step12BGateArity mword, LitEquiv (cnfOfClauses F_cur) (rhs[p]?.getD 0) l) ∧
        (∀ p < step12BGateArity mword, ∃ er < 2 * cv,
          LitEquiv (cnfOfClauses F_cur) (rhs[p]?.getD 0) er ∧
          (s.core.vals[er]?.getD 0#8 = 1#8 ∨
            ∃ q < ua.toNat, er = (s.core.tmp[q]?.getD 0#32).toNat))) ∧
      (FullMem c { s with core := { s.core with repr := reprb, lit_mark := lmb } } ⋆ R) mb)
    (fun rem (matched, j, ()) mj => ∃ reprj lmj,
      reprj.length = 2 * c.max_vars ∧ lmj.length = 2 * c.max_vars ∧
      j.toNat ≤ ea.toNat ∧ rem = ea.toNat - j.toNat ∧
      FullCongReprInv F_cur (2 * cv) reprj ∧
      matched.toNat = ((List.range (2 * cv)).filter (fun l => lmj[l]?.getD 0#8 == 2#8)).length ∧
      (∀ l < 2 * c.max_vars, lmj[l]?.getD 0#8 = 0#8 ↔ lm1[l]?.getD 0#8 = 0#8) ∧
      (∀ l < 2 * cv, lmj[l]?.getD 0#8 = 2#8 →
        lm1[l]?.getD 0#8 = 1#8 ∧
        ∃ p < j.toNat, LitEquiv (cnfOfClauses F_cur) (rhs[p]?.getD 0) l) ∧
      (∀ p < j.toNat, ∃ er < 2 * cv,
        LitEquiv (cnfOfClauses F_cur) (rhs[p]?.getD 0) er ∧
        (s.core.vals[er]?.getD 0#8 = 1#8 ∨
          ∃ q < ua.toNat, er = (s.core.tmp[q]?.getD 0#32).toNat)) ∧
      (FullMem c { s with core := { s.core with repr := reprj, lit_mark := lmj } } ⋆ R) mj)
    ?_ ?_ ?_
  · -- Post Loop 2: Loop 3 cleanup (`k = 0..ua-1`) + `return ok && (matched == distinct_ua)`
    rintro _ ⟨ok, matched, _, ⟨⟩⟩ mb ⟨reprb, lmb, hrlb, hlmlb, hreprb, hzero_b, hok_b, hmb⟩
    m6_steps
    refine wp_loop_inv (ts := [i32])
      (fun (k3, ()) mc => ∃ lmc : List (BitVec 8),
        lmc.length = 2 * c.max_vars ∧ k3.toNat ≤ ua.toNat ∧
        (∀ l < 2 * c.max_vars, lmc[l]?.getD 0#8 = 0#8 ∨
          ∃ r, k3.toNat ≤ r ∧ r < ua.toNat ∧ (s.core.tmp[r]?.getD 0#32).toNat = l) ∧
        (FullMem c { s with core := { s.core with repr := reprb, lit_mark := lmc } } ⋆ R) mc)
      (fun (k3, ()) _ => ua.toNat - k3.toNat)
      (fun J3 hJ3 => by
        m6_let; refine hJ3 (0#32, ()) mb ⟨lmb, hlmlb, Nat.zero_le _, fun l hl => ?_, hmb⟩
        rcases hlm1_dom l hl with h0 | ⟨hl_cv, h1⟩
        · exact Or.inl ((hzero_b l hl).mpr h0)
        · obtain ⟨r, hr, heq⟩ := (hlm1_iff l hl_cv).mp h1
          exact Or.inr ⟨r, Nat.zero_le _, hr, heq⟩)
      (fun J3 (k3, ()) mc ⟨lmc, hlmlc, hk3_le, hlmc_inv, hmc⟩ ih3 => ?_)
    m6_split_fast
    · have hk3_lt : k3.toNat < ua.toNat := by
        simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
      have hk31_n : (k3 + 1#32).toNat = k3.toNat + 1 := s12b_bv32_add1_lt_of (by omega)
      have hk3_tmp : (k3.setWidth 64).toNat < s.core.tmp.length := by rw [bv_zext32_toNat]; omega
      let tc := s.core.tmp[(k3.setWidth 64).toNat]'hk3_tmp
      have htc_eq : tc = s.core.tmp[k3.toNat]?.getD 0#32 := by
        dsimp only [tc]; rw [List.getElem?_eq_getElem (by omega : k3.toNat < s.core.tmp.length),
          Option.getD_some]; exact list_getElem_congr (bv_zext32_toNat k3) _ _
      have htc_lt : tc.toNat < 2 * cv := by rw [htc_eq]; exact htmp_bd k3.toNat hk3_lt
      have htc_lm : (tc.setWidth 64).toNat < lmc.length := by rw [bv_zext32_toNat]; omega
      clear hc; m6_steps
      let lmc' := lmc.set (tc.setWidth 64).toNat 0#8
      exact ih3 (k3 + 1#32, ()) m (by dsimp only; omega)
        ⟨lmc', by simp [lmc', hlmlc], by omega, fun l hl => by
          dsimp only [lmc']
          by_cases hlt : l = (tc.setWidth 64).toNat
          · left; rw [hlt, List.getElem?_set_self htc_lm, Option.getD_some]
          · rw [List.getElem?_set_ne (Ne.symm hlt)]
            rcases hlmc_inv l hl with h0 | ⟨r, hr1, hr2, hr3⟩
            · exact Or.inl h0
            · right; refine ⟨r, ?_, hr2, hr3⟩
              have hne : r ≠ k3.toNat := fun he => by
                subst he; apply hlt; rw [bv_zext32_toNat, htc_eq, hr3]
              omega, hm⟩
    · have hk3_eq : k3.toNat = ua.toNat := by
        simp only [BitVec.ult, decide_eq_false_iff_not] at hc; omega
      have hclr : FullLitMarksClear c
          { s with core := { s.core with repr := reprb, lit_mark := lmc } } :=
        ⟨hmk0.1, fun l hl => by
          rcases hlmc_inv l hl with h0 | ⟨r, hr1, hr2, _⟩
          · exact h0
          · omega⟩
      have hw_b : FullWitnessInv c F0 F_cur
          { s.core with repr := reprb, lit_mark := lmc } :=
        s12b_fullWitnessInv_with_lm (fullWitnessInv_with_repr hw reprb) lmc
      clear hc; m6_to_group
      refine wp_join_group (ts := [.bool])
        (fun (res, ()) mret => mret = mc ∧
          (res = true → ok = true ∧ matched = dist_ua))
        (fun _ ⟨res, ⟨⟩⟩ mret ⟨hmret, hres⟩ => by
          subst mret; m6_steps
          refine hQ res reprb lmc mc hrlb hlmlc hclr hreprb ?_ hmc
          intro hres_t
          obtain ⟨hok_t, hmd_eq⟩ := hres hres_t
          obtain ⟨hmat_eq, hbwd_b, hfwd_b⟩ := hok_b hok_t
          refine ⟨h2_le_ua, hua_le_max, ?_⟩
          rw [he0, Option.getD_some]
          refine andMatch_sound_equiv hw_b hcl0 hand_e ?_ ?_
          · intro p hp
            have hp' : p < step12BGateArity mword := by rw [← hrl_rhs]; exact hp
            have h1 := hfwd_b p hp'; dsimp only [rhs] at h1
            rw [List.getElem?_eq_getElem hp, Option.getD_some] at h1; exact h1
          · intro q hq
            have hq_lt : (s.core.tmp[q]?.getD 0#32).toNat < 2 * cv := htmp_bd q hq
            have hlm1_q : lm1[(s.core.tmp[q]?.getD 0#32).toNat]?.getD 0#8 = 1#8 :=
              (hlm1_iff _ hq_lt).mpr ⟨q, hq, rfl⟩
            have hlen_eq :
                ((List.range (2 * cv)).filter (fun l => lmb[l]?.getD 0#8 == 2#8)).length =
                ((List.range (2 * cv)).filter (fun l => lm1[l]?.getD 0#8 == 1#8)).length := by
              rw [← hmat_eq, ← hdist_eq, hmd_eq]
            have hq_is2 : (lmb[(s.core.tmp[q]?.getD 0#32).toNat]?.getD 0#8 == 2#8) = true :=
              filter_sub_length_eq_imp_forall (List.range (2 * cv))
                (fun l hl h2 => by
                  rw [List.mem_range] at hl
                  rw [(hbwd_b l hl (beq_iff_eq.mp h2)).1]; rfl)
                hlen_eq _ (List.mem_range.mpr hq_lt) (by rw [hlm1_q]; rfl)
            obtain ⟨_, p, hp, heq⟩ := hbwd_b _ hq_lt (beq_iff_eq.mp hq_is2)
            rw [← hrl_rhs] at hp; exact ⟨p, hp, heq⟩)
        (fun Jret hJret => by
          m6_split_fast
          · have hok_t : ok = true := hc
            clear hc; m6_split_fast
            · m6_steps
              exact hJret (true, ()) mc ⟨rfl, fun _ => ⟨hok_t, beq_iff_eq.mp hc⟩⟩
            · m6_steps
              exact hJret (false, ()) mc ⟨rfl, fun h => by cases h⟩
          · m6_steps
            exact hJret (false, ()) mc ⟨rfl, fun h => by cases h⟩)
  · -- Loop 2 body
    rintro B2 L2 rem ⟨matched, j, ⟨⟩⟩ mj hB2 hL2
      ⟨reprj, lmj, hrlj, hlmlj, hj_le, rfl, hreprj, hmat_eq, hzero_j, hbwd_j, hfwd_j, hmj⟩
    let stj : FullState := { s with core := { s.core with repr := reprj, lit_mark := lmj } }
    have hwj : FullWitnessInv c F0 F_cur stj.core :=
      s12b_fullWitnessInv_with_lm (fullWitnessInv_with_repr hw reprj) lmj
    m6_split_fast
    · have hj_lt : j.toNat < ea.toNat := by
        simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
      obtain ⟨rv, hrv_get, hrv_lt⟩ := hrhs_e j.toNat (hea_eq ▸ hj_lt)
      have hrhs_j : rhs[j.toNat]?.getD 0 = rv.toNat := by
        simp only [rhs, List.getElem?_map, List.getElem?_take,
          ite_eq_left (hea_eq ▸ hj_lt : j.toNat < step12BGateArity mword),
          List.getElem?_drop, hrv_get]
        rfl
      have he2j_lt : ent.toNat + 2 + j.toNat < c.scratch_cap := by omega
      have he2j_n : (ent.setWidth 64 + 2 + j.setWidth 64).toNat = ent.toNat + 2 + j.toNat :=
        bv64_add_zext32 (k := 2) (by rw [bv_zext32_toNat]; omega)
      have he2j_arr : (ent.setWidth 64 + 2 + j.setWidth 64).toNat <
          s.scratch.scratch_buf.length := by
        rw [he2j_n]; exact Nat.lt_of_lt_of_le he2j_lt (Nat.le_of_eq hscrl0.symm)
      have hst_e2j : s.scratch.scratch_buf[(ent.setWidth 64 + 2 + j.setWidth 64).toNat]'
          he2j_arr = rv := by
        have h := (hpref (ent.toNat + 2 + j.toNat) (by omega)).trans hrv_get
        rw [← he2j_n, List.getElem?_eq_getElem he2j_arr] at h; exact Option.some.inj h
      have hj1_n : (j + 1#32).toNat = j.toNat + 1 := s12b_bv32_add1_lt_of (by omega)
      clear hc; m6_steps; m6_call hFind
      refine ⟨F_cur, 2 * cv, reprj, FullReprRest c stj ⋆ R, hreprj,
        by rw [hst_e2j]; exact hrv_lt, focus_full_repr hmj,
        fun er repr_e me hrl_e hrepr_e _ her_lt her_eqv hme => ?_⟩
      let ste : FullState := { stj with core := { stj.core with repr := repr_e } }
      have hme' : (FullMem c ste ⋆ R) me := unfocus_full_repr hme; clear hme
      have hrl_e' : repr_e.length = 2 * c.max_vars := hrl_e.trans hrlj
      have hw_e : FullWitnessInv c F0 F_cur ste.core := fullWitnessInv_with_repr hwj repr_e
      have her_vals : (er.setWidth 64).toNat < ste.core.vals.length := by
        rw [bv_zext32_toNat]; dsimp [ste, stj]; rw [hvl0]; omega
      have her_vals' : er.toNat < ste.core.vals.length := by
        rw [bv_zext32_toNat] at her_vals; exact her_vals
      have hrv_er_eqv : LitEquiv (cnfOfClauses F_cur) (rhs[j.toNat]?.getD 0) er.toNat := by
        rw [hrhs_j]; rwa [hst_e2j] at her_eqv
      have hev_dom : ste.core.vals[er.toNat]'her_vals' = 0#8 ∨
          ste.core.vals[er.toNat]'her_vals' = 1#8 ∨
          ste.core.vals[er.toNat]'her_vals' = 0xFF#8 := by
        have hd := hw_e.vals_domain er.toNat her_lt
        rwa [List.getElem?_eq_getElem her_vals', Option.getD_some] at hd
      m6_split_fast
      · clear hc; m6_steps
        exact hB2 (false, matched, j, ()) me
          ⟨repr_e, lmj, hrl_e', hlmlj, hrepr_e, hzero_j, (fun h => by cases h), hme'⟩
      · have hev_nslt : ¬ (ste.core.vals[er.toNat]'her_vals').slt 0#8 = true :=
          bv8_not_slt0_of_signExtend32_nslt0 hev_dom (by
            rw [list_getElem_congr (bv_zext32_toNat er) her_vals her_vals'] at hc; exact hc)
        clear hc; m6_split_fast
        · have her_lm : (er.setWidth 64).toNat < ste.core.lit_mark.length := by
            rw [bv_zext32_toNat]; dsimp [ste, stj]; omega
          have her_lm' : er.toNat < lmj.length := by
            rw [bv_zext32_toNat] at her_lm; exact her_lm
          clear hc; m6_split_fast
          · clear hc; m6_steps
            exact hB2 (false, matched, j, ()) me
              ⟨repr_e, lmj, hrl_e', hlmlj, hrepr_e, hzero_j, (fun h => by cases h), hme'⟩
          · have hmv_ne0 : lmj[er.toNat]?.getD 0#8 ≠ 0#8 := by
              rw [List.getElem?_eq_getElem her_lm', Option.getD_some,
                ← list_getElem_congr (bv_zext32_toNat er) her_lm her_lm']
              exact s12b_zext32_bv8_ne _ 0#8 (beq_eq_false_iff_ne.mp hc)
            have hlm1_er1 : lm1[er.toNat]?.getD 0#8 = 1#8 := by
              have hne : lm1[er.toNat]?.getD 0#8 ≠ 0#8 := fun h0 =>
                hmv_ne0 ((hzero_j er.toNat (by omega)).mpr h0)
              rcases hlm1_dom er.toNat (by omega) with h0 | ⟨_, h1⟩
              · exact absurd h0 hne
              · exact h1
            have her_in_tmp : ∃ q < ua.toNat, er.toNat = (s.core.tmp[q]?.getD 0#32).toNat := by
              obtain ⟨q, hq, heq⟩ := (hlm1_iff er.toNat her_lt).mp hlm1_er1
              exact ⟨q, hq, heq.symm⟩
            have hmat_le : matched.toNat ≤ 2 * cv := by
              rw [hmat_eq]; exact s12b_filter_length_le_range _
            have hmat1_n : (matched + 1#32).toNat = matched.toNat + 1 :=
              s12b_bv32_add1_lt_of (by omega)
            clear hc; m6_to_group
            refine wp_join_group (ts := [i32])
              (fun (matched', ()) mm => ∃ lmj' : List (BitVec 8),
                lmj'.length = 2 * c.max_vars ∧
                matched'.toNat =
                  ((List.range (2 * cv)).filter (fun l => lmj'[l]?.getD 0#8 == 2#8)).length ∧
                (∀ l < 2 * c.max_vars, lmj'[l]?.getD 0#8 = 0#8 ↔ lm1[l]?.getD 0#8 = 0#8) ∧
                (∀ l < 2 * cv, lmj'[l]?.getD 0#8 = 2#8 → lm1[l]?.getD 0#8 = 1#8 ∧
                  ∃ p < (j + 1#32).toNat, LitEquiv (cnfOfClauses F_cur) (rhs[p]?.getD 0) l) ∧
                (FullMem c { s with core :=
                  { s.core with repr := repr_e, lit_mark := lmj' } } ⋆ R) mm)
              (fun _ ⟨matched', ⟨⟩⟩ mm ⟨lmj', hlmlj', hmat', hzero', hbwd', hmm⟩ => by
                m6_steps
                refine hL2 (ea.toNat - (j + 1#32).toNat) (matched', j + 1#32, ()) mm (by omega)
                  ⟨repr_e, lmj', hrl_e', hlmlj', by omega, rfl, hrepr_e, hmat', hzero', hbwd',
                   fun p hp => ?_, hmm⟩
                rw [hj1_n] at hp
                by_cases hpj : p = j.toNat
                · subst hpj; exact ⟨er.toNat, her_lt, hrv_er_eqv, Or.inr her_in_tmp⟩
                · exact hfwd_j p (by omega)) ?_
            intro Jm2 hJm2; m6_split_fast
            · have hlmj_er1 : lmj[er.toNat]?.getD 0#8 = 1#8 := by
                rw [List.getElem?_eq_getElem her_lm', Option.getD_some,
                  ← list_getElem_congr (bv_zext32_toNat er) her_lm her_lm']
                exact s12b_zext32_bv8_eq _ 1#8 (beq_iff_eq.mp hc)
              clear hc; m6_steps
              let lmj' := lmj.set (er.setWidth 64).toNat 2#8
              have hlmj'_set : lmj' = lmj.set er.toNat 2#8 := by
                dsimp only [lmj']; rw [bv_zext32_toNat]
              refine hJm2 (matched + 1#32, ()) m ⟨lmj', by simp [lmj', hlmlj], ?_, ?_, ?_, hm⟩
              · rw [hmat1_n, hmat_eq, hlmj'_set]
                exact (filter_length_flip_one (x0 := er.toNat) (List.range (2 * cv))
                  List.nodup_range (List.mem_range.mpr her_lt)
                  (by rw [hlmj_er1]; decide)
                  (by rw [List.getElem?_set_self her_lm', Option.getD_some]; decide)
                  (fun y _ hne => by rw [List.getElem?_set_ne hne.symm])).symm
              · intro l hl; rw [hlmj'_set]
                by_cases hler : l = er.toNat
                · subst hler; rw [List.getElem?_set_self her_lm', Option.getD_some, hlm1_er1]
                  constructor <;> intro h <;> cases h
                · rw [List.getElem?_set_ne (Ne.symm hler)]; exact hzero_j l hl
              · intro l hl h2; rw [hlmj'_set] at h2
                by_cases hler : l = er.toNat
                · subst hler; exact ⟨hlm1_er1, j.toNat, by omega, hrv_er_eqv⟩
                · rw [List.getElem?_set_ne (Ne.symm hler)] at h2
                  obtain ⟨h1, p, hp, heq⟩ := hbwd_j l hl h2
                  exact ⟨h1, p, by omega, heq⟩
            · clear hc; m6_steps
              refine hJm2 (matched, ()) me ⟨lmj, hlmlj, hmat_eq, hzero_j, fun l hl h2 => ?_, hme'⟩
              obtain ⟨h1, p, hp, heq⟩ := hbwd_j l hl h2
              exact ⟨h1, p, by omega, heq⟩
        · have hev_eq1 : s.core.vals[er.toNat]?.getD 0#8 = 1#8 := by
            have hne0 : (ste.core.vals[er.toNat]'her_vals').signExtend 32 ≠ 0#32 := by
              have hc' := beq_eq_false_iff_ne.mp hc
              rw [list_getElem_congr (bv_zext32_toNat er) her_vals her_vals'] at hc'; exact hc'
            have h1 := bv8_eq1_of_signExtend32_ne0_nslt0 hev_dom hne0 hev_nslt
            rw [List.getElem?_eq_getElem (by rw [hvl0]; omega), Option.getD_some]
            exact h1
          clear hc; m6_steps
          refine hL2 (ea.toNat - (j + 1#32).toNat) (matched, j + 1#32, ()) me (by omega)
            ⟨repr_e, lmj, hrl_e', hlmlj, by omega, rfl, hrepr_e, hmat_eq, hzero_j,
             fun l hl h2 => let ⟨h1, p, hp, heq⟩ := hbwd_j l hl h2; ⟨h1, p, by omega, heq⟩,
             fun p hp => ?_, hme'⟩
          rw [hj1_n] at hp
          by_cases hpj : p = j.toNat
          · subst hpj; exact ⟨er.toNat, her_lt, hrv_er_eqv, Or.inl hev_eq1⟩
          · exact hfwd_j p (by omega)
    · have hj_eq : j.toNat = ea.toNat := by
        simp only [BitVec.ult, decide_eq_false_iff_not] at hc; omega
      rw [hj_eq, hea_eq] at hbwd_j hfwd_j
      clear hc; m6_steps
      exact hB2 (true, matched, j, ()) mj
        ⟨reprj, lmj, hrlj, hlmlj, hreprj, hzero_j, fun _ => ⟨hmat_eq, hbwd_j, hfwd_j⟩, hmj⟩
  · -- Loop 2 entry
    intro _ L2 _ hL2; m6_steps
    refine hL2 ea.toNat (0#32, 0#32, ()) mk
      ⟨s.core.repr, lm1, hrl0, hlml1, Nat.zero_le _, by simp, hrepr0, ?_,
       fun _ _ => Iff.rfl, fun l hl h2 => ?_, fun _ h => absurd h (Nat.not_lt_zero _), hmk1⟩
    · exact (s12b_filter_empty_eq_zero fun x hx => by
        rcases hlm1_dom x (by omega) with h0 | ⟨_, h1⟩
        · rw [h0]; decide
        · rw [h1]; decide).symm
    · rcases hlm1_dom l (by omega) with h0 | ⟨_, h1⟩
      · rw [h0] at h2; cases h2
      · rw [h1] at h2; cases h2

/-! ## 4. `full_cong_extract_and_clause_fid_s12b_wp` (`step12BCongExtractAndClauseSpec`) -/

theorem full_cong_extract_and_clause_fid_s12b_wp (_Γ : Env) :
    ∀ a m Q X, step12BCongExtractAndClauseSpec a m Q X →
      Func.wp _Γ fidStep12BCongExtractAndClauseFn.body a m Q X := by
  rintro ⟨h, usz, g_len, g_cap, tick_lim, ⟨⟩⟩ m0 Q X
    ⟨maxA, c, F0, F_cur, s, R, hmaxA, rfl, hdw, hu3, humax, hucv, hgl_le, hgc_cap, hseq0,
     hbase_lt, hbase_uniq, hbase_ent, hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; have hsc := c.hscr
  unfold dimacsBound at hmx hwc hsc
  unfold step12BCongAndArityMax at hmaxA
  have hcl := hdw.1.core_ok; have hsl := hdw.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hlml0 := hcl.lit_mark_len
  have hwvl := hcl.wvec_len; have hwsl := hcl.wstk_len_arr; have hwle := hcl.wlen_le
  have hws1_l := hsl.work_stk1_len; have hws2_l := hsl.work_stk2_len
  have hscrl0 := hsl.scratch_buf_len
  have hmk0 := hdw.2.2.1; have hdm := hdw.2.2.2.2.2.2
  let cv := s.core.cur_vars
  let base := s.scratch.work_stk2
  have hbase_l : base.length = 2 * c.max_vars := hws2_l
  have hret_same : Q (g_len, ()) m0 :=
    hQ g_len s.core.lit_mark s.scratch.scratch_buf s.scratch.res_sz m0
      hdw (Nat.le_refl _) hgl_le (fun _ _ => rfl) hseq0 hm0
  have hnl_eq : (BitVec.ofNat 64 cv <<< (1 : Nat)).toNat = 2 * cv := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]
  have hnbm_lt : ∀ m < usz.toNat, ((base[m]?.getD 0#32) ^^^ 1#32).toNat < 2 * cv := fun m hm => by
    rw [FullCongHelpers.bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even (hbase_lt m hm)
  have hnbm_uniq : ∀ m1 < usz.toNat, ∀ m2 < usz.toNat, m1 ≠ m2 →
      ((base[m1]?.getD 0#32) ^^^ 1#32).toNat ≠ ((base[m2]?.getD 0#32) ^^^ 1#32).toNat :=
    fun m1 hm1 m2 hm2 hne heq => hbase_uniq m1 hm1 m2 hm2 hne (s12b_bv32_xor1_inj heq)
  unfold fidStep12BCongExtractAndClauseFn; dsimp only
  m6_split_fast
  · m6_steps; exact hret_same
  clear hc; m6_split_fast
  · m6_steps; exact hret_same
  clear hc; m6_split_fast
  · m6_steps; exact hret_same
  clear hc
  let arity := usz - 1#32
  have har_n : arity.toNat = usz.toNat - 1 := by dsimp only [arity]; bv_omega
  m6_split_fast
  · m6_steps; exact hret_same
  clear hc; m6_split_fast
  · m6_steps; exact hret_same
  clear hc; m6_steps
  -- Loop 1: Mark `base[0..usz)^1` with `5` (`nbc[bm] >= arity`) or `1`, tracking `first_i`
  refine wp_loop_inv (ts := [i32, i32, i32])
    (fun (first_i, _min_d, m_i, ()) mm => ∃ lm1 : List (BitVec 8),
      lm1.length = 2 * c.max_vars ∧ m_i.toNat ≤ usz.toNat ∧ first_i.toNat ≤ usz.toNat ∧
      MarkSupp base usz.toNat c.max_vars lm1 ∧
      MarkBit2Clear base usz.toNat lm1 ∧
      (FullMem c { s with core := { s.core with lit_mark := lm1 } } ⋆ R) mm)
    (fun (_, _, m_i, ()) _ => usz.toNat - m_i.toNat)
    (fun J1 hJ1 => by
      m6_let; refine hJ1 (usz, 0xFFFFFFFF#32, 0#32, ()) m0
        ⟨s.core.lit_mark, hlml0, Nat.zero_le _, Nat.le_refl _,
         fun l hl hne => absurd (hmk0.2 l hl) hne,
         fun m hm => by rw [hmk0.2 _ (by have := hnbm_lt m hm; omega)]; rfl, hm0⟩)
    (fun J1 (first_i, min_d, m_i, ()) mm ⟨lm1, hlml1, hm_le, hfi_le, hsupp1, hclr2_1, hmm1⟩
      ih1 => ?_)
  m6_split_fast
  · have hm_lt : m_i.toNat < usz.toNat := by
      simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
    have hm1_n : (m_i + 1#32).toNat = m_i.toNat + 1 := s12b_bv32_add1_lt_of (by omega)
    have hm_ws2 : (m_i.setWidth 64).toNat < base.length := by rw [bv_zext32_toNat]; omega
    let bm := base[(m_i.setWidth 64).toNat]'hm_ws2
    have hbm_eq : bm = base[m_i.toNat]?.getD 0#32 := by
      dsimp only [bm]; rw [List.getElem?_eq_getElem (by omega : m_i.toNat < base.length),
        Option.getD_some]; exact list_getElem_congr (bv_zext32_toNat m_i) _ _
    have hbm_lt : bm.toNat < 2 * cv := by rw [hbm_eq]; exact hbase_lt m_i.toNat hm_lt
    have hbm_ws1 : (bm.setWidth 64).toNat < s.scratch.work_stk1.length := by
      rw [bv_zext32_toNat, hws1_l]; omega
    let nbm := bm ^^^ 1#32
    have hnbm_m_lt : nbm.toNat < 2 * cv := by dsimp only [nbm]; rw [hbm_eq]; exact hnbm_lt _ hm_lt
    have hnbm_lm : (nbm.setWidth 64).toNat < lm1.length := by rw [bv_zext32_toNat]; omega
    have hnbm_lm' : nbm.toNat < lm1.length := by rw [bv_zext32_toNat] at hnbm_lm; exact hnbm_lm
    have hnbm_wv : (nbm.setWidth 64 <<< (1 : Nat) + 1#64).toNat < s.core.wvec.length := by
      rw [BitVec.toNat_add, FullCongHelpers.bv64_shl1_toNat, bv_zext32_toNat]
      show (2 * nbm.toNat % 2 ^ 64 + 1) % 2 ^ 64 < s.core.wvec.length; omega
    have hnbm_wv_se : (nbm.setWidth 64 <<< ((1#32 : BitVec 32).signExtend 64).toNat + 1#64).toNat <
        s.core.wvec.length := hnbm_wv
    have hnbm_wv_bv : (nbm.setWidth 64 <<< ((1#32 : BitVec 32).signExtend 64) + 1#64).toNat <
        s.core.wvec.length := hnbm_wv
    clear hc; m6_to_group
    refine wp_join_group (ts := [i32, i32])
      (fun (fi', _md', ()) mj => ∃ lmj : List (BitVec 8),
        lmj.length = 2 * c.max_vars ∧ fi'.toNat ≤ usz.toNat ∧
        MarkSupp base usz.toNat c.max_vars lmj ∧ MarkBit2Clear base usz.toNat lmj ∧
        (FullMem c { s with core := { s.core with lit_mark := lmj } } ⋆ R) mj)
      (fun _ ⟨fi', md', ⟨⟩⟩ mj ⟨lmj, hlmlj, hfi', hsupp', hclr2', hmj⟩ => by
        m6_steps
        exact ih1 (fi', md', m_i + 1#32, ()) mj (by dsimp only; omega)
          ⟨lmj, hlmlj, by omega, hfi', hsupp', hclr2', hmj⟩) ?_
    intro Jm1 hJm1; m6_split_fast
    · -- `nbc[bm] >= arity`: set `lm[nbm] = 5` and maybe update `first_i`
      clear hc; m6_to_group
      let lm5 := lm1.set (nbm.setWidth 64).toNat 5#8
      have hlm5_set : lm5 = lm1.set nbm.toNat 5#8 := by dsimp only [lm5]; rw [bv_zext32_toNat]
      have hlm5_len : lm5.length = 2 * c.max_vars := by simp [lm5, hlml1]
      have hlm5_supp : MarkSupp base usz.toNat c.max_vars lm5 := fun l hl hne => by
        rw [hlm5_set] at hne
        by_cases hln : l = nbm.toNat
        · exact ⟨m_i.toNat, hm_lt, hln.trans (by dsimp only [nbm]; rw [hbm_eq])⟩
        · rw [List.getElem?_set_ne (Ne.symm hln)] at hne; exact hsupp1 l hl hne
      have hlm5_clr2 : MarkBit2Clear base usz.toNat lm5 := fun m hm => by
        rw [hlm5_set]
        by_cases hln : ((base[m]?.getD 0#32) ^^^ 1#32).toNat = nbm.toNat
        · rw [hln, List.getElem?_set_self hnbm_lm', Option.getD_some]; rfl
        · rw [List.getElem?_set_ne (Ne.symm hln)]; exact hclr2_1 m hm
      refine wp_join_group (ts := [i32, i32])
        (fun (fi', _md', ()) mj => mj = m ∧ fi'.toNat ≤ usz.toNat)
        (fun _ ⟨fi', md', ⟨⟩⟩ mj ⟨hmj, hfi'⟩ => by
          subst mj; exact hJm1 (fi', md', ()) m ⟨lm5, hlm5_len, hfi', hlm5_supp, hlm5_clr2, hm⟩)
        (fun Jfi hJfi => by
          m6_steps; m6_split_fast
          · m6_steps; exact hJfi (m_i, _, ()) m ⟨rfl, by omega⟩
          · clear hc; m6_split_fast
            · m6_steps; exact hJfi (m_i, _, ()) m ⟨rfl, by omega⟩
            · m6_steps; exact hJfi (first_i, min_d, ()) m ⟨rfl, hfi_le⟩)
    · -- `nbc[bm] < arity`: set `lm[nbm] = 1`
      clear hc; m6_steps
      let lm1' := lm1.set (nbm.setWidth 64).toNat 1#8
      have hlm1'_set : lm1' = lm1.set nbm.toNat 1#8 := by dsimp only [lm1']; rw [bv_zext32_toNat]
      refine hJm1 (first_i, min_d, ()) m ⟨lm1', by simp [lm1', hlml1], hfi_le,
        fun l hl hne => by
          rw [hlm1'_set] at hne
          by_cases hln : l = nbm.toNat
          · exact ⟨m_i.toNat, hm_lt, hln.trans (by dsimp only [nbm]; rw [hbm_eq])⟩
          · rw [List.getElem?_set_ne (Ne.symm hln)] at hne; exact hsupp1 l hl hne,
        fun m hm => by
          rw [hlm1'_set]
          by_cases hln : ((base[m]?.getD 0#32) ^^^ 1#32).toNat = nbm.toNat
          · rw [hln, List.getElem?_set_self hnbm_lm', Option.getD_some]; rfl
          · rw [List.getElem?_set_ne (Ne.symm hln)]; exact hclr2_1 m hm, hm⟩
  -- Post Loop 1: `if (first_i < usz)` + outer step loop + cleanup loop
  clear hc; m6_to_group
  refine wp_join_group (ts := [i64, i32, i64])
    (fun (gl_out, _m_out, ticks_out, ()) mo => ∃ lm_o scr_o,
      lm_o.length = 2 * c.max_vars ∧ scr_o.length = c.scratch_cap ∧
      g_len.toNat ≤ gl_out.toNat ∧ gl_out.toNat ≤ g_cap.toNat ∧
      (∀ idx < g_len.toNat, scr_o[idx]? = s.scratch.scratch_buf[idx]?) ∧
      Step12BGateSeqOk maxA F_cur cv scr_o gl_out.toNat 0 ∧
      MarkSupp base usz.toNat c.max_vars lm_o ∧
      (FullMem c { s with
        core := { s.core with lit_mark := lm_o }
        scratch := { s.scratch with scratch_buf := scr_o } } ⋆ R) mo)
    ?_ ?_
  · -- Final cleanup loop: clear `lm[base[m] ^ 1] = 0`, store `h->res_sz = ticks`, return `gl_out`
    rintro _ ⟨gl_out, _, ticks_out, ⟨⟩⟩ mo
      ⟨lm_o, scr_o, hlml_o, hscrl_o, hgl_lo, hgl_hi, hpref_o, hseq_o, hsupp_o, hmo⟩
    m6_steps
    refine wp_loop_inv (ts := [i32])
      (fun (mc, ()) mmc => ∃ lmc : List (BitVec 8),
        lmc.length = 2 * c.max_vars ∧ mc.toNat ≤ usz.toNat ∧
        (∀ l < 2 * c.max_vars, lmc[l]?.getD 0#8 = 0#8 ∨
          ∃ m', mc.toNat ≤ m' ∧ m' < usz.toNat ∧ l = ((base[m']?.getD 0#32) ^^^ 1#32).toNat) ∧
        (FullMem c { s with
          core := { s.core with lit_mark := lmc }
          scratch := { s.scratch with scratch_buf := scr_o } } ⋆ R) mmc)
      (fun (mc, ()) _ => usz.toNat - mc.toNat)
      (fun Jcl hJcl => by
        m6_let; refine hJcl (0#32, ()) mo ⟨lm_o, hlml_o, Nat.zero_le _, fun l hl => ?_, hmo⟩
        by_cases hz : lm_o[l]?.getD 0#8 = 0#8
        · exact Or.inl hz
        · obtain ⟨m', hm', heq⟩ := hsupp_o l hl hz
          exact Or.inr ⟨m', Nat.zero_le _, hm', heq⟩)
      (fun Jcl (mc, ()) mmc ⟨lmc, hlmlc, hmc_le, hlmc_inv, hmmc⟩ ihcl => ?_)
    m6_split_fast
    · have hmc_lt : mc.toNat < usz.toNat := by
        simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
      have hmc1_n : (mc + 1#32).toNat = mc.toNat + 1 := s12b_bv32_add1_lt_of (by omega)
      have hmc_ws2 : (mc.setWidth 64).toNat < base.length := by rw [bv_zext32_toNat]; omega
      let nbc := base[(mc.setWidth 64).toNat]'hmc_ws2 ^^^ 1#32
      have hnbc_eq : nbc = (base[mc.toNat]?.getD 0#32) ^^^ 1#32 := by
        dsimp only [nbc]; congr 1
        rw [List.getElem?_eq_getElem (by omega : mc.toNat < base.length), Option.getD_some]
        exact list_getElem_congr (bv_zext32_toNat mc) _ _
      have hnbc_lt : nbc.toNat < 2 * cv := by rw [hnbc_eq]; exact hnbm_lt mc.toNat hmc_lt
      have hnbc_lm : (nbc.setWidth 64).toNat < lmc.length := by rw [bv_zext32_toNat]; omega
      clear hc; m6_steps
      let lmc' := lmc.set (nbc.setWidth 64).toNat 0#8
      exact ihcl (mc + 1#32, ()) m (by dsimp only; omega)
        ⟨lmc', by simp [lmc', hlmlc], by omega, fun l hl => by
          dsimp only [lmc']
          by_cases hln : l = (nbc.setWidth 64).toNat
          · left; rw [hln, List.getElem?_set_self hnbc_lm, Option.getD_some]
          · rw [List.getElem?_set_ne (Ne.symm hln)]
            rcases hlmc_inv l hl with h0 | ⟨m', hm1, hm2, hm3⟩
            · exact Or.inl h0
            · right; refine ⟨m', ?_, hm2, hm3⟩
              have hne : m' ≠ mc.toNat := fun he => by
                subst he; apply hln; rw [bv_zext32_toNat, hnbc_eq, hm3]
              omega, hm⟩
    · have hmc_eq : mc.toNat = usz.toNat := by
        simp only [BitVec.ult, decide_eq_false_iff_not] at hc; omega
      have hclr : FullLitMarksClear c { s with core := { s.core with lit_mark := lmc } } :=
        ⟨hmk0.1, fun l hl => by
          rcases hlmc_inv l hl with h0 | ⟨m', hm1, hm2, _⟩
          · exact h0
          · omega⟩
      clear hc; m6_steps
      exact hQ gl_out lmc scr_o ticks_out m
        (s12b_fullDenseInvW_with_lm_scr_rsz hdw hlmlc hscrl_o hclr)
        hgl_lo hgl_hi hpref_o hseq_o hm
  · -- `if (first_i < usz) { while (step < usz && gl + 2 + arity <= g_cap && ticks < tick_lim) }`
    intro Jout hJout; m6_split_fast
    · have hfi_lt : first_i.toNat < usz.toNat := by
        simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
      clear hc; m6_steps
      refine wp_loop_inv (ts := [i64, i32, i64, i32])
        (fun (gl, _m_s, ticks, step, ()) ms => ∃ lm_s scr_s,
          lm_s.length = 2 * c.max_vars ∧ scr_s.length = c.scratch_cap ∧
          step.toNat ≤ usz.toNat ∧ g_len.toNat ≤ gl.toNat ∧ gl.toNat ≤ g_cap.toNat ∧
          (∀ idx < g_len.toNat, scr_s[idx]? = s.scratch.scratch_buf[idx]?) ∧
          Step12BGateSeqOk maxA F_cur cv scr_s gl.toNat 0 ∧
          MarkSupp base usz.toNat c.max_vars lm_s ∧
          MarkBit2Clear base usz.toNat lm_s ∧
          (FullMem c { s with
            core := { s.core with lit_mark := lm_s }
            scratch := { s.scratch with scratch_buf := scr_s } } ⋆ R) ms)
        (fun (_, _, _, step, ()) _ => usz.toNat - step.toNat)
        (fun Js hJs => by
          m6_let; exact hJs (g_len, m_i, s.scratch.res_sz, 0#32, ()) mm
            ⟨lm1, s.scratch.scratch_buf, hlml1, hscrl0, Nat.zero_le _, Nat.le_refl _, hgl_le,
             fun _ _ => rfl, hseq0, hsupp1, hclr2_1, hmm1⟩)
        (fun Js (gl, m_s, ticks, step, ()) ms
          ⟨lm_s, scr_s, hlml_s, hscrl_s, hst_le, hgl_lo, hgl_hi, hpref_s, hseq_s, hsupp_s,
           hclr2_s, hms⟩ ihs => ?_)
      have hexit_s : Jout (gl, m_s, ticks, ()) ms :=
        hJout (gl, m_s, ticks, ()) ms
          ⟨lm_s, scr_s, hlml_s, hscrl_s, hgl_lo, hgl_hi, hpref_s, hseq_s, hsupp_s, hms⟩
      m6_split_fast
      · have hst_lt : step.toNat < usz.toNat := by
          simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
        have hst1_n : (step + 1#32).toNat = step.toNat + 1 := s12b_bv32_add1_lt_of (by omega)
        clear hc; m6_split_fast
        · have hgl_ar : gl.toNat + 2 + arity.toNat ≤ g_cap.toNat := by
            simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
          clear hc; m6_split_fast
          · clear hc; m6_to_group
            -- Ternary `i = (step == 0u) ? first_i : ((step <= first_i) ? (step - 1u) : step)`
            refine wp_join_group (ts := [i32])
              (fun (i, ()) mi => mi = ms ∧ i.toNat < usz.toNat) ?_
              (fun Ji hJi => by
                m6_split_fast
                · m6_let; exact hJi (first_i, ()) ms ⟨rfl, hfi_lt⟩
                · have hst_pos : 0 < step.toNat := by
                    have hne := beq_eq_false_iff_ne.mp hc
                    rcases Nat.eq_zero_or_pos step.toNat with hz | hp
                    · exact absurd (BitVec.eq_of_toNat_eq hz) hne
                    · exact hp
                  clear hc; m6_to_group
                  refine wp_join_group (ts := [i32])
                    (fun (i, ()) mi => mi = ms ∧ i.toNat < usz.toNat)
                    (fun _ ⟨i, ⟨⟩⟩ mi h => by m6_let; exact hJi (i, ()) mi h)
                    (fun Ji2 hJi2 => by
                      m6_split_fast
                      · have hle : step.toNat ≤ first_i.toNat := by
                          simp only [BitVec.ule, decide_eq_true_eq] at hc; exact hc
                        have hsub : (step - 1#32).toNat = step.toNat - 1 := by bv_omega
                        m6_steps; exact hJi2 (step - 1#32, ()) ms ⟨rfl, by omega⟩
                      · m6_let; exact hJi2 (step, ()) ms ⟨rfl, hst_lt⟩))
            rintro _ ⟨i, ⟨⟩⟩ mi ⟨hmi, hi_lt⟩; subst mi
            have hi_ws2 : (i.setWidth 64).toNat < base.length := by rw [bv_zext32_toNat]; omega
            let lhs := base[(i.setWidth 64).toNat]'hi_ws2
            have hlhs_eq : lhs = base[i.toNat]?.getD 0#32 := by
              dsimp only [lhs]
              rw [List.getElem?_eq_getElem (by omega : i.toNat < base.length), Option.getD_some]
              exact list_getElem_congr (bv_zext32_toNat i) _ _
            let not_lhs := lhs ^^^ 1#32
            have hnlhs_eq : not_lhs = (base[i.toNat]?.getD 0#32) ^^^ 1#32 := by
              dsimp only [not_lhs]; rw [hlhs_eq]
            have hnlhs_lt : not_lhs.toNat < 2 * cv := by
              rw [hnlhs_eq]; exact hnbm_lt i.toNat hi_lt
            have hnlhs_lm : (not_lhs.setWidth 64).toNat < lm_s.length := by
              rw [bv_zext32_toNat]; omega
            m6_to_group
            refine wp_join_group (ts := [i64, i32, i64])
              (fun (gl', _m', ticks', ()) mj => ∃ lm' scr',
                lm'.length = 2 * c.max_vars ∧ scr'.length = c.scratch_cap ∧
                g_len.toNat ≤ gl'.toNat ∧ gl'.toNat ≤ g_cap.toNat ∧
                (∀ idx < g_len.toNat, scr'[idx]? = s.scratch.scratch_buf[idx]?) ∧
                Step12BGateSeqOk maxA F_cur cv scr' gl'.toNat 0 ∧
                MarkSupp base usz.toNat c.max_vars lm' ∧
                MarkBit2Clear base usz.toNat lm' ∧
                (FullMem c { s with
                  core := { s.core with lit_mark := lm' }
                  scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) mj)
              (fun _ ⟨gl', m', ticks', ⟨⟩⟩ mj
                ⟨lm', scr', hlml', hscrl', hgl_lo', hgl_hi', hpref', hseq', hsupp', hclr2',
                 hmj⟩ => by
                m6_steps
                exact ihs (gl', m', ticks', step + 1#32, ()) mj (by dsimp only; omega)
                  ⟨lm', scr', hlml', hscrl', by omega, hgl_lo', hgl_hi', hpref', hseq', hsupp',
                   hclr2', hmj⟩) ?_
            intro Jcand hJcand; m6_split_fast
            · -- `(lm[not_lhs] & 4) != 0`: scan `WATCHES(not_lhs)`
              clear hc
              have hwat := hdw.2.1.watches; unfold ModeWatchesInv at hwat
              simp only [hdm, ↓reduceIte] at hwat
              have hw_bd := hwat.layout.bounds not_lhs.toNat hnlhs_lt
              have hslice0 : DenseWatchSliceOk F_cur s.core not_lhs.toNat
                  (fullWatchOffCore s.core not_lhs.toNat)
                  (fullWatchSizeCore s.core not_lhs.toNat) :=
                hwat.slices not_lhs.toNat hnlhs_lt
              have hshl0 : (not_lhs.setWidth 64 <<< (1 : Nat)).toNat = 2 * not_lhs.toNat := by
                rw [FullCongHelpers.bv64_shl1_toNat, bv_zext32_toNat]; omega
              have hshl1 : (not_lhs.setWidth 64 <<< (1 : Nat) + 1#64).toNat =
                  2 * not_lhs.toNat + 1 := by
                rw [BitVec.toNat_add, hshl0]
                show (2 * not_lhs.toNat + 1) % 2 ^ 64 = 2 * not_lhs.toNat + 1; omega
              have hwv0 : (not_lhs.setWidth 64 <<< (1 : Nat)).toNat < s.core.wvec.length := by omega
              have hwv1 : (not_lhs.setWidth 64 <<< (1 : Nat) + 1#64).toNat <
                  s.core.wvec.length := by omega
              m6_to_group
              generalize hoff_v :
                (s.core.wvec[(not_lhs.setWidth 64 <<< (1 : Nat)).toNat]'hwv0).setWidth 64 = off
              generalize hwsz_v :
                (s.core.wvec[(not_lhs.setWidth 64 <<< (1 : Nat) + 1#64).toNat]'hwv1).setWidth 64 =
                  wsz
              have hoff_n : off.toNat = fullWatchOffCore s.core not_lhs.toNat := by
                rw [← hoff_v, bv_zext32_toNat]; unfold fullWatchOffCore
                rw [List.getElem?_eq_getElem (by omega : 2 * not_lhs.toNat < s.core.wvec.length),
                  Option.getD_some]
                exact congrArg BitVec.toNat (list_getElem_congr hshl0 (by omega) (by omega))
              have hwsz_n : wsz.toNat = fullWatchSizeCore s.core not_lhs.toNat := by
                rw [← hwsz_v, bv_zext32_toNat]; unfold fullWatchSizeCore
                rw [List.getElem?_eq_getElem
                  (by omega : 2 * not_lhs.toNat + 1 < s.core.wvec.length), Option.getD_some]
                exact congrArg BitVec.toNat (list_getElem_congr hshl1 (by omega) (by omega))
              have hend_n : (off + wsz).toNat = off.toNat + wsz.toNat := by bv_omega
              refine wp_loop_break_group (brkTs := [i64, i64, i32]) (lpTs := [i64, i64, i32])
                (fun (ticks_w, _wp_w, matched, ()) mw => ∃ lmw : List (BitVec 8),
                  lmw.length = 2 * c.max_vars ∧
                  MarkSupp base usz.toNat c.max_vars lmw ∧
                  matched.toNat = ((List.range usz.toNat).filter (fun m =>
                    decide (m ≠ i.toNat ∧
                      (lmw[((base[m]?.getD 0#32) ^^^ 1#32).toNat]?.getD 0#8 &&& 2#8) ≠
                        0#8))).length ∧
                  (∀ m < usz.toNat, m ≠ i.toNat →
                    (lmw[((base[m]?.getD 0#32) ^^^ 1#32).toNat]?.getD 0#8 &&& 2#8) ≠ 0#8 →
                    (cnfOfClauses F_cur).EntailsClause (cnfClause
                      [litNeg (base[i.toNat]?.getD 0#32).toNat,
                       litNeg (base[m]?.getD 0#32).toNat])) ∧
                  (FullMem c { s with
                    core := { s.core with lit_mark := lmw }
                    scratch := { s.scratch with scratch_buf := scr_s } } ⋆ R) mw)
                (fun rem (ticks_w, wp, matched, ()) mw => ∃ lmw : List (BitVec 8),
                  lmw.length = 2 * c.max_vars ∧
                  wp.toNat ≤ (off + wsz).toNat ∧ rem = (off + wsz).toNat - wp.toNat ∧
                  DenseWatchSliceOk F_cur s.core not_lhs.toNat wp.toNat
                    ((off + wsz).toNat - wp.toNat) ∧
                  MarkSupp base usz.toNat c.max_vars lmw ∧
                  matched.toNat = ((List.range usz.toNat).filter (fun m =>
                    decide (m ≠ i.toNat ∧
                      (lmw[((base[m]?.getD 0#32) ^^^ 1#32).toNat]?.getD 0#8 &&& 2#8) ≠
                        0#8))).length ∧
                  (∀ m < usz.toNat, m ≠ i.toNat →
                    (lmw[((base[m]?.getD 0#32) ^^^ 1#32).toNat]?.getD 0#8 &&& 2#8) ≠ 0#8 →
                    (cnfOfClauses F_cur).EntailsClause (cnfClause
                      [litNeg (base[i.toNat]?.getD 0#32).toNat,
                       litNeg (base[m]?.getD 0#32).toNat])) ∧
                  (FullMem c { s with
                    core := { s.core with lit_mark := lmw }
                    scratch := { s.scratch with scratch_buf := scr_s } } ⋆ R) mw)
                ?_ ?_ ?_
              · -- Post watch-scan: `if (matched == arity) { emit }`, then clear bit 2 loop
                rintro _ ⟨ticks_w, _, matched, ⟨⟩⟩ mw
                  ⟨lmw, hlmlw, hsuppw, hmat_eq, hbins_w, hmw⟩
                m6_to_group
                refine wp_join_group (ts := [i64])
                  (fun (gl', ()) me => ∃ scre : List (BitVec 32),
                    scre.length = c.scratch_cap ∧
                    g_len.toNat ≤ gl'.toNat ∧ gl'.toNat ≤ g_cap.toNat ∧
                    (∀ idx < g_len.toNat, scre[idx]? = s.scratch.scratch_buf[idx]?) ∧
                    Step12BGateSeqOk maxA F_cur cv scre gl'.toNat 0 ∧
                    (FullMem c { s with
                      core := { s.core with lit_mark := lmw }
                      scratch := { s.scratch with scratch_buf := scre } } ⋆ R) me)
                  ?_ ?_
                · -- Bit-2 clear / candidate prune loop (`m = 0..usz-1`)
                  rintro _ ⟨gl', ⟨⟩⟩ me ⟨scre, hscrle, hgl_lo', hgl_hi', hpref', hseq', hme⟩
                  m6_steps
                  refine wp_loop_inv (ts := [i32])
                    (fun (mp, ()) mmp => ∃ lmp : List (BitVec 8),
                      lmp.length = 2 * c.max_vars ∧ mp.toNat ≤ usz.toNat ∧
                      MarkSupp base usz.toNat c.max_vars lmp ∧
                      (∀ m < mp.toNat,
                        (lmp[((base[m]?.getD 0#32) ^^^ 1#32).toNat]?.getD 0#8 &&& 2#8) = 0#8) ∧
                      (FullMem c { s with
                        core := { s.core with lit_mark := lmp }
                        scratch := { s.scratch with scratch_buf := scre } } ⋆ R) mmp)
                    (fun (mp, ()) _ => usz.toNat - mp.toNat)
                    (fun Jp hJp => by
                      m6_let; exact hJp (0#32, ()) me
                        ⟨lmw, hlmlw, Nat.zero_le _, hsuppw, fun _ h => absurd h (Nat.not_lt_zero _),
                         hme⟩)
                    (fun Jp (mp, ()) mmp ⟨lmp, hlmlp, hmp_le, hsuppp, hclr_p, hmmp⟩ ihp => ?_)
                  m6_split_fast
                  · have hmp_lt : mp.toNat < usz.toNat := by
                      simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                    have hmp1_n : (mp + 1#32).toNat = mp.toNat + 1 :=
                      s12b_bv32_add1_lt_of (by omega)
                    have hmp_ws2 : (mp.setWidth 64).toNat < base.length := by
                      rw [bv_zext32_toNat]; omega
                    let nbp := base[(mp.setWidth 64).toNat]'hmp_ws2 ^^^ 1#32
                    have hnbp_eq : nbp = (base[mp.toNat]?.getD 0#32) ^^^ 1#32 := by
                      dsimp only [nbp]; congr 1
                      rw [List.getElem?_eq_getElem (by omega : mp.toNat < base.length),
                        Option.getD_some]
                      exact list_getElem_congr (bv_zext32_toNat mp) _ _
                    have hnbp_lt : nbp.toNat < 2 * cv := by
                      rw [hnbp_eq]; exact hnbm_lt mp.toNat hmp_lt
                    have hnbp_lm : (nbp.setWidth 64).toNat < lmp.length := by
                      rw [bv_zext32_toNat]; omega
                    have hnbp_lm' : nbp.toNat < lmp.length := by
                      rw [bv_zext32_toNat] at hnbp_lm; exact hnbp_lm
                    clear hc; m6_to_group
                    refine wp_join_group (ts := [])
                      (fun () mq => ∃ lmq : List (BitVec 8),
                        lmq.length = 2 * c.max_vars ∧
                        MarkSupp base usz.toNat c.max_vars lmq ∧
                        (∀ m < (mp + 1#32).toNat,
                          (lmq[((base[m]?.getD 0#32) ^^^ 1#32).toNat]?.getD 0#8 &&& 2#8) = 0#8) ∧
                        (FullMem c { s with
                          core := { s.core with lit_mark := lmq }
                          scratch := { s.scratch with scratch_buf := scre } } ⋆ R) mq)
                      (fun _ ⟨⟩ mq ⟨lmq, hlmlq, hsuppq, hclrq, hmq⟩ => by
                        m6_steps
                        exact ihp (mp + 1#32, ()) mq (by dsimp only; omega)
                          ⟨lmq, hlmlq, by omega, hsuppq, hclrq, hmq⟩)
                      (fun Jq hJq => by
                        m6_split_fast
                        · clear hc; m6_steps
                          let mv := lmp[(nbp.setWidth 64).toNat]'hnbp_lm
                          let lmq := lmp.set (nbp.setWidth 64).toNat (mv &&& 5#8)
                          have hlmq_set : lmq = lmp.set nbp.toNat (mv &&& 5#8) := by
                            dsimp only [lmq]; rw [bv_zext32_toNat]
                          refine hJq () m ⟨lmq, by simp [lmq, hlmlp], fun l hl hne => ?_,
                            fun m hm => ?_, by
                              have h5 : BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 5) = 5#32 := rfl
                              have h1 : (1 : BitVec 32) = 1#32 := rfl
                              simpa only [lmq, mv, nbp, base, h5, h1, s12b_bv8_and5_c0] using hm⟩
                          · rw [hlmq_set] at hne
                            by_cases hln : l = nbp.toNat
                            · exact ⟨mp.toNat, hmp_lt, hln.trans (by rw [hnbp_eq])⟩
                            · rw [List.getElem?_set_ne (Ne.symm hln)] at hne; exact hsuppp l hl hne
                          · rw [hmp1_n] at hm; rw [hlmq_set]
                            by_cases hln : ((base[m]?.getD 0#32) ^^^ 1#32).toNat = nbp.toNat
                            · rw [hln, List.getElem?_set_self hnbp_lm', Option.getD_some]
                              exact s12b_bv8_and5_and2_eq0 mv
                            · rw [List.getElem?_set_ne (Ne.symm hln)]
                              have hne : m ≠ mp.toNat := fun he => hln (by rw [he, hnbp_eq])
                              exact hclr_p m (by omega)
                        · clear hc; m6_steps
                          let lmq := lmp.set (nbp.setWidth 64).toNat 1#8
                          have hlmq_set : lmq = lmp.set nbp.toNat 1#8 := by
                            dsimp only [lmq]; rw [bv_zext32_toNat]
                          refine hJq () m ⟨lmq, by simp [lmq, hlmlp], fun l hl hne => ?_,
                            fun m hm => ?_, hm⟩
                          · rw [hlmq_set] at hne
                            by_cases hln : l = nbp.toNat
                            · exact ⟨mp.toNat, hmp_lt, hln.trans (by rw [hnbp_eq])⟩
                            · rw [List.getElem?_set_ne (Ne.symm hln)] at hne; exact hsuppp l hl hne
                          · rw [hmp1_n] at hm; rw [hlmq_set]
                            by_cases hln : ((base[m]?.getD 0#32) ^^^ 1#32).toNat = nbp.toNat
                            · rw [hln, List.getElem?_set_self hnbp_lm', Option.getD_some]; rfl
                            · rw [List.getElem?_set_ne (Ne.symm hln)]
                              have hne : m ≠ mp.toNat := fun he => hln (by rw [he, hnbp_eq])
                              exact hclr_p m (by omega))
                  · have hmp_eq : mp.toNat = usz.toNat := by
                      simp only [BitVec.ult, decide_eq_false_iff_not] at hc; omega
                    rw [hmp_eq] at hclr_p
                    clear hc; m6_steps
                    exact hJcand (gl', mp, ticks_w, ()) mmp
                      ⟨lmp, scre, hlmlp, hscrle, hgl_lo', hgl_hi', hpref', hseq', hsuppp, hclr_p,
                       hmmp⟩
                · -- `if (matched == arity)` emission branch
                  intro Jem hJem; m6_split_fast
                  · have hmat_ar : matched.toNat = usz.toNat - 1 := by
                      have h := congrArg BitVec.toNat (beq_iff_eq.mp hc)
                      change matched.toNat = arity.toNat at h; rwa [har_n] at h
                    have hbins_all : ∀ k < usz.toNat, k ≠ i.toNat →
                        (cnfOfClauses F_cur).EntailsClause (cnfClause
                          [litNeg (base[i.toNat]?.getD 0#32).toNat,
                           litNeg (base[k]?.getD 0#32).toNat]) := by
                      intro k hk hki
                      have hlen_eq :
                          ((List.range usz.toNat).filter (fun m => decide (m ≠ i.toNat ∧
                            (lmw[((base[m]?.getD 0#32) ^^^ 1#32).toNat]?.getD 0#8 &&& 2#8) ≠
                              0#8))).length =
                          ((List.range usz.toNat).filter (fun m => decide (m ≠ i.toNat))).length :=
                        by rw [← hmat_eq, hmat_ar, filter_range_ne_length hi_lt]
                      have hdec := filter_sub_length_eq_imp_forall (List.range usz.toNat)
                        (fun m _ h => by
                          simp only [decide_eq_true_eq] at h ⊢; exact h.1)
                        hlen_eq k (List.mem_range.mpr hk) (by simp [hki])
                      simp only [decide_eq_true_eq] at hdec
                      exact hbins_w k hk hki hdec.2
                    have hgl0 : gl.toNat < scr_s.length := by omega
                    have hgl1_n : (gl + 1#64).toNat = gl.toNat + 1 := by bv_omega
                    have hgl1 : (gl + 1#64).toNat < scr_s.length := by omega
                    let mword_e : BitVec 32 :=
                      if usz.toNat - 1 ≤ 64 then BitVec.ofNat 32 (usz.toNat - 1)
                      else (3#32 <<< 28) ||| BitVec.ofNat 32 (usz.toNat - 1)
                    have har_bv : arity = BitVec.ofNat 32 (usz.toNat - 1) :=
                      BitVec.eq_of_toNat_eq (by rw [har_n, bv32_ofNat_toNat (by omega)])
                    clear hc; m6_to_group
                    refine wp_join_group (ts := [i32])
                      (fun (mw_e, ()) mmw => mmw = m ∧ mw_e = mword_e) ?_
                      (fun Jmw hJmw => by
                        m6_steps; m6_split_fast
                        · have hle64 : usz.toNat - 1 ≤ 64 := by
                            simp only [BitVec.ule, decide_eq_true_eq] at hc
                            change arity.toNat ≤ 64 at hc; omega
                          m6_let; exact hJmw (arity, ()) m ⟨rfl, by
                            dsimp only [mword_e]; rw [ite_eq_left hle64, har_bv]⟩
                        · have hgt64 : ¬ usz.toNat - 1 ≤ 64 := by
                            simp only [BitVec.ule, decide_eq_false_iff_not] at hc
                            change ¬ arity.toNat ≤ 64 at hc; omega
                          m6_steps; exact hJmw ((3#32 <<< 28) ||| arity, ()) m ⟨rfl, by
                            dsimp only [mword_e]; rw [ite_eq_right hgt64, har_bv]⟩)
                    rintro _ ⟨mw_e, ⟨⟩⟩ mmw ⟨hmmw, hmw_eq⟩; subst mmw; subst mw_e
                    have hgl1_s : (gl + 1#64).toNat < (scr_s.set gl.toNat lhs).length := by
                      rw [List.length_set]; exact hgl1
                    m6_steps
                    let scr0 := scr_s.set gl.toNat lhs
                    let scr1 := scr0.set (gl + 1#64).toNat mword_e
                    refine wp_loop_inv (ts := [i32, i32])
                      (fun (rk, j2, ()) mj2 => ∃ scrw : List (BitVec 32),
                        scrw.length = c.scratch_cap ∧ j2.toNat ≤ usz.toNat ∧
                        rk.toNat = (if j2.toNat ≤ i.toNat then j2.toNat else j2.toNat - 1) ∧
                        (∀ idx < gl.toNat, scrw[idx]? = scr_s[idx]?) ∧
                        scrw[gl.toNat]? = some lhs ∧
                        scrw[gl.toNat + 1]? = some mword_e ∧
                        (∀ k < j2.toNat, k ≠ i.toNat →
                          scrw[gl.toNat + 2 + (if k < i.toNat then k else k - 1)]? =
                            some ((base[k]?.getD 0#32) ^^^ 1#32)) ∧
                        (FullMem c { s with
                          core := { s.core with lit_mark := lmw }
                          scratch := { s.scratch with scratch_buf := scrw } } ⋆ R) mj2)
                      (fun (_, j2, ()) _ => usz.toNat - j2.toNat)
                      (fun Jw hJw => by
                        m6_let; refine hJw (0#32, 0#32, ()) m
                          ⟨scr1, by simp [scr1, scr0, hscrl_s], Nat.zero_le _, by simp,
                           fun idx hidx => ?_, ?_, ?_, (fun _ h => absurd h (Nat.not_lt_zero _)),
                           hm⟩
                        · dsimp only [scr1, scr0]
                          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                        · dsimp only [scr1, scr0]
                          rw [List.getElem?_set_ne (by omega), List.getElem?_set_self hgl0]
                        · dsimp only [scr1, scr0]; rw [← hgl1_n]
                          exact List.getElem?_set_self hgl1_s)
                      (fun Jw (rk, j2, ()) mj2
                        ⟨scrw, hscrlw, hj2_le, hrk_e, hprefw, hw0, hw1, hwrhs, hmj2⟩ ihw => ?_)
                    m6_split_fast
                    · have hj2_lt : j2.toNat < usz.toNat := by
                        simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                      have hj21_n : (j2 + 1#32).toNat = j2.toNat + 1 :=
                        s12b_bv32_add1_lt_of (by omega)
                      clear hc; m6_split_fast
                      · have hji : j2.toNat ≠ i.toNat := fun h =>
                          (bne_iff_ne.mp hc) (BitVec.eq_of_toNat_eq h)
                        have hj2_ws2 : (j2.setWidth 64).toNat < base.length := by
                          rw [bv_zext32_toNat]; omega
                        have hj2_ws2' : j2.toNat < base.length := by
                          rw [bv_zext32_toNat] at hj2_ws2; exact hj2_ws2
                        have hrk_lt : rk.toNat < arity.toNat := by
                          rw [hrk_e, har_n]; split <;> omega
                        have hrk1_n : (rk + 1#32).toNat = rk.toNat + 1 :=
                          s12b_bv32_add1_lt_of (by omega)
                        have hwr_n : (gl + 2 + rk.setWidth 64).toNat =
                            gl.toNat + 2 + rk.toNat :=
                          bv64_add_zext32 (k := 2) (by omega)
                        have hwr_sc : (gl + 2 + rk.setWidth 64).toNat < scrw.length := by
                          rw [hwr_n, hscrlw]; omega
                        clear hc; m6_steps
                        refine ihw (rk + 1#32, j2 + 1#32, ()) m (by dsimp only; omega)
                          ⟨scrw.set (gl + 2 + rk.setWidth 64).toNat
                            (base[(j2.setWidth 64).toNat]'hj2_ws2 ^^^ 1#32),
                           by simp [hscrlw], by omega,
                           by rw [hj21_n, hrk1_n, hrk_e]; split <;> split <;> omega,
                           fun idx hidx => by
                             rw [List.getElem?_set_ne (by omega)]; exact hprefw idx hidx,
                           by rw [List.getElem?_set_ne (by omega)]; exact hw0,
                           by rw [List.getElem?_set_ne (by omega)]; exact hw1,
                           fun k hk hkne => ?_, hm⟩
                        by_cases hkj : k = j2.toNat
                        · subst hkj
                          have hset_lt :
                              gl.toNat + 2 + (if j2.toNat < i.toNat then j2.toNat
                                else j2.toNat - 1) < scrw.length := by
                            rw [hscrlw]; split <;> omega
                          rw [hwr_n, hrk_e]
                          rw [show (if j2.toNat ≤ i.toNat then j2.toNat else j2.toNat - 1) =
                              if j2.toNat < i.toNat then j2.toNat else j2.toNat - 1 by
                                split <;> split <;> omega]
                          rw [List.getElem?_set_self hset_lt,
                            list_getElem_congr (bv_zext32_toNat j2) hj2_ws2 hj2_ws2',
                            List.getElem?_eq_getElem hj2_ws2', Option.getD_some]
                        · rw [List.getElem?_set_ne (by
                            rw [hwr_n, hrk_e]; split <;> split <;> omega)]
                          exact hwrhs k (by omega) hkne
                      · have hji : j2.toNat = i.toNat :=
                          congrArg BitVec.toNat (by simpa using hc)
                        clear hc; m6_steps
                        exact ihw (rk, j2 + 1#32, ()) mj2 (by dsimp only; omega)
                          ⟨scrw, hscrlw, by omega,
                           by rw [hj21_n, hrk_e]; split <;> split <;> omega,
                           hprefw, hw0, hw1, fun k hk hkne => hwrhs k (by omega) hkne, hmj2⟩
                    · have hj2_e : j2.toNat = usz.toNat := by
                        simp only [BitVec.ult, decide_eq_false_iff_not] at hc; omega
                      rw [hj2_e] at hwrhs
                      have hgat := step12B_andGate_of_emitted
                        (by unfold step12BCongAndArityMax; omega) hu3 humax hucv hi_lt hbase_lt
                        hbase_ent hbins_all (by omega) (hlhs_eq ▸ hw0) hw1 hwrhs
                      have hgl_next : (gl + 2#64 + arity.setWidth 64).toNat =
                          gl.toNat + 2 + (usz.toNat - 1) := by
                        rw [bv64_add_zext32 (k := 2) (by omega), har_n]
                      have hmw_ar : step12BGateArity mword_e = usz.toNat - 1 :=
                        s12b_mword_arity (by omega)
                      have hseq_new : Step12BGateSeqOk maxA F_cur cv scrw
                          (gl + 2#64 + arity.setWidth 64).toNat 0 := by
                        rw [hgl_next]
                        refine step12BGateSeqOk_append_gate hprefw hseq_s (.step hgat ?_) (by omega)
                        simpa [hw1, hmw_ar] using Step12BGateSeqOk.done
                      clear hc; m6_steps
                      exact hJem (gl + 2#64 + arity.setWidth 64, ()) mj2
                        ⟨scrw, hscrlw, by omega, by omega,
                         fun idx hidx => (hprefw idx (by omega)).trans (hpref_s idx hidx),
                         hseq_new, hmj2⟩
                  · clear hc; m6_steps
                    exact hJem (gl, ()) mw ⟨scr_s, hscrl_s, hgl_lo, hgl_hi, hpref_s, hseq_s, hmw⟩
              · -- Watch-scan loop body
                rintro Bw Lw rem ⟨ticks_w, wp, matched, ⟨⟩⟩ mw hBw hLw
                  ⟨lmw, hlmlw, hwp_le, rfl, hslice_w, hsuppw, hmat_eq, hbins_w, hmw⟩
                have hbw_cur : Bw (ticks_w, wp, matched, ()) mw :=
                  hBw (ticks_w, wp, matched, ()) mw ⟨lmw, hlmlw, hsuppw, hmat_eq, hbins_w, hmw⟩
                m6_split_fast
                · have hwp_lt : wp.toNat < (off + wsz).toNat := by
                    simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                  clear hc; m6_split_fast
                  · have htk_lt : ticks_w.toNat < tick_lim.toNat := by
                      simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                    have hwp_wstk : wp.toNat < s.core.wstk.length := by omega
                    have hwp1_n : (wp + 1#64).toNat = wp.toNat + 1 :=
                      bv64_add1_lt (by omega)
                    have hrem_pos : 0 < (off + wsz).toNat - wp.toNat := by omega
                    obtain ⟨w0, hw0_get, hstep⟩ := s12b_dense_slice_step hslice_w hrem_pos
                    have hw0_eq : s.core.wstk[wp.toNat]'hwp_wstk = w0 := by
                      rw [List.getElem?_eq_getElem hwp_wstk] at hw0_get
                      exact Option.some.inj hw0_get
                    clear hc; m6_split_fast
                    · -- Binary watch `(w0 & PW_BIN_FLAG) != 0`
                      have hbin_nz : (w0 &&& 0x80000000#32) ≠ 0#32 := by
                        rw [← hw0_eq]; exact bne_iff_ne.mp hc
                      obtain ⟨_, hent_bin, hrest⟩ | ⟨hf, _⟩ := hstep
                      · let ot := w0 &&& 0x7FFFFFFF#32
                        have hrest' : DenseWatchSliceOk F_cur s.core not_lhs.toNat
                            (wp + 1#64).toNat ((off + wsz).toNat - (wp + 1#64).toNat) := by
                          rw [hwp1_n, ← Nat.sub_sub]; exact hrest
                        have hlw_same : ∀ m_next : Mem 64,
                            (FullMem c { s with
                              core := { s.core with lit_mark := lmw }
                              scratch := { s.scratch with scratch_buf := scr_s } } ⋆ R) m_next →
                            Lw (ticks_w + 1#64, wp + 1#64, matched, ()) m_next :=
                          fun m_next hm_next =>
                            hLw ((off + wsz).toNat - (wp + 1#64).toNat)
                              (ticks_w + 1#64, wp + 1#64, matched, ()) m_next (by omega)
                              ⟨lmw, hlmlw, by omega, rfl, hrest', hsuppw, hmat_eq, hbins_w, hm_next⟩
                        clear hc; m6_steps; m6_split_fast
                        · have hot_lt : ot.toNat < 2 * cv := by
                            simp only [BitVec.ult, decide_eq_true_eq, bv_zext32_toNat] at hc
                            change (s.core.wstk[wp.toNat]'hwp_wstk &&& 0x7FFFFFFF#32).toNat <
                              (BitVec.ofNat 64 cv <<< (1 : Nat)).toNat at hc
                            rw [hw0_eq, hnl_eq] at hc; exact hc
                          have hot_lm : (ot.setWidth 64).toNat < lmw.length := by
                            rw [bv_zext32_toNat]; omega
                          have hot_lm' : ot.toNat < lmw.length := by
                            rw [bv_zext32_toNat] at hot_lm; exact hot_lm
                          clear hc; m6_split_fast
                          · have hot_ne : ot.toNat ≠ not_lhs.toNat := by
                              have h := bne_iff_ne.mp hc
                              rw [hw0_eq] at h
                              exact fun heq => h (BitVec.eq_of_toNat_eq heq)
                            have hot_lm_raw : ((s.core.wstk[wp.toNat]'hwp_wstk &&&
                                0x7FFFFFFF#32).setWidth 64).toNat < lmw.length := by
                              rw [hw0_eq]; exact hot_lm
                            clear hc; m6_steps; m6_split_fast
                            · -- `(lm[ot] & 3) == 1`: mark bit 2 and increment `matched`!
                              have hot_idx_eq : ((s.core.wstk[wp.toNat]'hwp_wstk &&&
                                  0x7FFFFFFF#32).setWidth 64).toNat = ot.toNat := by
                                rw [hw0_eq, bv_zext32_toNat]
                              have hlm_and3 : (lmw[ot.toNat]?.getD 0#8 &&& 3#8) = 1#8 := by
                                have h := s12b_zext32_bv8_and3_eq1 _ (beq_iff_eq.mp hc)
                                rw [List.getElem?_eq_getElem hot_lm', Option.getD_some,
                                  ← list_getElem_congr hot_idx_eq hot_lm_raw hot_lm']
                                exact h
                              have hlm_ne0 := s12b_bv8_and3_eq1_ne0 hlm_and3
                              have hlm_and2 := s12b_bv8_and3_eq1_and2_eq0 hlm_and3
                              obtain ⟨m0, hm0_lt, hot_m0⟩ := hsuppw ot.toNat (by omega) hlm_ne0
                              have hm0_ne_i : m0 ≠ i.toNat := fun he =>
                                hot_ne (hot_m0.trans (by rw [he, hnlhs_eq]))
                              have hmat_le : matched.toNat ≤ usz.toNat := by
                                rw [hmat_eq]; exact s12b_filter_length_le_range _
                              have hmat1_n : (matched + 1#32).toNat = matched.toNat + 1 :=
                                s12b_bv32_add1_lt_of (by omega)
                              have hent_m0 : (cnfOfClauses F_cur).EntailsClause (cnfClause
                                  [litNeg (base[i.toNat]?.getD 0#32).toNat,
                                   litNeg (base[m0]?.getD 0#32).toNat]) := by
                                have h1 : not_lhs.toNat =
                                    litNeg (base[i.toNat]?.getD 0#32).toNat := by
                                  rw [hnlhs_eq, FullCongHelpers.bv32_xor1_eq_litNeg]
                                have h2 : ot.toNat = litNeg (base[m0]?.getD 0#32).toNat := by
                                  rw [hot_m0, FullCongHelpers.bv32_xor1_eq_litNeg]
                                rw [← h1, ← h2]; exact hent_bin
                              clear hc; m6_steps
                              let lmw' := lmw.set
                                ((s.core.wstk[wp.toNat]'hwp_wstk &&&
                                  0x7FFFFFFF#32).setWidth 64).toNat
                                (lmw[((s.core.wstk[wp.toNat]'hwp_wstk &&&
                                  0x7FFFFFFF#32).setWidth 64).toNat]'hot_lm_raw ||| 2#8)
                              have hlmw'_set : lmw' =
                                  lmw.set ot.toNat (lmw[ot.toNat]?.getD 0#8 ||| 2#8) := by
                                dsimp only [lmw']
                                have hget : lmw[((s.core.wstk[wp.toNat]'hwp_wstk &&&
                                    0x7FFFFFFF#32).setWidth 64).toNat]'hot_lm_raw =
                                    lmw[ot.toNat]?.getD 0#8 := by
                                  rw [List.getElem?_eq_getElem hot_lm', Option.getD_some]
                                  exact list_getElem_congr hot_idx_eq hot_lm_raw hot_lm'
                                rw [hget, hot_idx_eq]
                              have hm_or : (FullMem c { s with
                                core := { s.core with lit_mark := lmw' }
                                scratch := { s.scratch with scratch_buf := scr_s } } ⋆ R) m := by
                                have h2 : BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 2) = 2#32 :=
                                  rfl
                                have hmk : (2147483647 : BitVec 32) = 0x7FFFFFFF#32 := rfl
                                simpa only [lmw', h2, hmk, s12b_bv8_or2_c0] using hm
                              refine hLw ((off + wsz).toNat - (wp + 1#64).toNat)
                                (ticks_w + 1#64, wp + 1#64, matched + 1#32, ()) m (by omega)
                                ⟨lmw', by simp [lmw', hlmlw], by omega, rfl, hrest',
                                 fun l hl hne => ?_, ?_, fun m hm hmi h2 => ?_, hm_or⟩
                              · rw [hlmw'_set] at hne
                                by_cases hlo : l = ot.toNat
                                · exact ⟨m0, hm0_lt, hlo.trans hot_m0⟩
                                · rw [List.getElem?_set_ne (Ne.symm hlo)] at hne
                                  exact hsuppw l hl hne
                              · rw [hmat1_n, hmat_eq, hlmw'_set]
                                exact (filter_length_flip_one (x0 := m0) (List.range usz.toNat)
                                  List.nodup_range (List.mem_range.mpr hm0_lt)
                                  (by rw [← hot_m0, hlm_and2]; simp)
                                  (by rw [← hot_m0, List.getElem?_set_self hot_lm',
                                        Option.getD_some]
                                      simp [hm0_ne_i, s12b_bv8_or2_and2_ne0])
                                  (fun y hy hne => by
                                    rw [List.mem_range] at hy
                                    have hne_ot : ((base[y]?.getD 0#32) ^^^ 1#32).toNat ≠
                                        ot.toNat := by
                                      rw [hot_m0]; exact hnbm_uniq y hy m0 hm0_lt hne
                                    rw [List.getElem?_set_ne hne_ot.symm])).symm
                              · rw [hlmw'_set] at h2
                                by_cases hmm0 : m = m0
                                · subst hmm0; exact hent_m0
                                · have hne_ot : ((base[m]?.getD 0#32) ^^^ 1#32).toNat ≠
                                      ot.toNat := by
                                    rw [hot_m0]; exact hnbm_uniq m hm m0 hm0_lt hmm0
                                  rw [List.getElem?_set_ne hne_ot.symm] at h2
                                  exact hbins_w m hm hmi h2
                            · clear hc; m6_steps; exact hlw_same mw hmw
                          · clear hc; m6_steps; exact hlw_same mw hmw
                        · clear hc; m6_steps; exact hlw_same mw hmw
                      · exact absurd hf hbin_nz
                    · -- Large/occ watch `(w0 & PW_BIN_FLAG) == 0`: skip second word
                      have hbin_z : (w0 &&& 0x80000000#32) = 0#32 := by
                        rw [← hw0_eq]; exact beq_iff_eq.mp (by simpa using hc)
                      obtain ⟨hnz, _⟩ | ⟨_, h2rem, hrest2⟩ := hstep
                      · exact absurd hbin_z hnz
                      · have hwp2_n : (wp + 1#64 + 1#64).toNat = wp.toNat + 2 := by bv_omega
                        have hrest2' : DenseWatchSliceOk F_cur s.core not_lhs.toNat
                            (wp + 1#64 + 1#64).toNat
                            ((off + wsz).toNat - (wp + 1#64 + 1#64).toNat) := by
                          rw [hwp2_n]; exact hrest2
                        clear hc; m6_split_fast
                        · clear hc; m6_steps
                          exact hBw (ticks_w + 1#64, wp + 1#64, matched, ()) mw
                            ⟨lmw, hlmlw, hsuppw, hmat_eq, hbins_w, hmw⟩
                        · clear hc; m6_steps
                          exact hLw ((off + wsz).toNat - (wp + 1#64 + 1#64).toNat)
                            (ticks_w + 1#64, wp + 1#64 + 1#64, matched, ()) mw (by omega)
                            ⟨lmw, hlmlw, by omega, rfl, hrest2', hsuppw, hmat_eq, hbins_w, hmw⟩
                  · clear hc; m6_steps; exact hbw_cur
                · clear hc; m6_steps; exact hbw_cur
              · -- Watch-scan loop entry
                intro _ Lw _ hLw; m6_steps
                refine hLw wsz.toNat (ticks, off, 0#32, ()) ms
                  ⟨lm_s, hlml_s, by omega, by omega, ?_, hsupp_s, ?_, ?_, hms⟩
                · rw [hend_n, Nat.add_sub_cancel_left, hoff_n, hwsz_n]; exact hslice0
                · exact (s12b_filter_empty_eq_zero fun m hm => by
                    rw [hclr2_s m hm]; simp).symm
                · intro m hm _ h2; exact absurd (hclr2_s m hm) h2
            · clear hc; m6_steps
              exact hJcand (gl, m_s, ticks, ()) ms
                ⟨lm_s, scr_s, hlml_s, hscrl_s, hgl_lo, hgl_hi, hpref_s, hseq_s, hsupp_s, hclr2_s,
                 hms⟩
          · clear hc; m6_steps; exact hexit_s
        · clear hc; m6_steps; exact hexit_s
      · clear hc; m6_steps; exact hexit_s
    · clear hc; m6_steps
      exact hJout (g_len, m_i, s.scratch.res_sz, ()) mm
        ⟨lm1, s.scratch.scratch_buf, hlml1, hscrl0, Nat.le_refl _, hgl_le, fun _ _ => rfl,
         hseq0, hsupp1, hmm1⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep12B

end
