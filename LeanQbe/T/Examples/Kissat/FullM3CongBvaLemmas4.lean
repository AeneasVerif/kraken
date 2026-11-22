module

public import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas3

/-!
# Kissat `D-Full` M3b Congruence & BVA/BVE Proofs — Part 4 (`#6`–`#8`)

Builds on `FullM3CongBvaLemmas3` to prove parametric `(Γ : Env)` `Func.wp` contracts for:
6. `full_congruence_dense` (`m3_congruence_dense_wp`)
7. `full_elim_collect_nbrs` (`m3_elim_collect_nbrs_wp`)
8. `full_elim_bve` (`m3_elim_bve_wp`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM3CongBva

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open Kraken.Bedrock2.Test

/-! ## 1. `#6` `m3_congruence_dense_wp` Helpers & Proof -/

section CongruenceDenseProof

open scoped FullArenaTactics FullCongTactics M3HeadTactics

private theorem bv64_ule_le {a b : BitVec 64} (h : a.ule b = true) : a.toNat ≤ b.toNat := by
  simpa [BitVec.ule] using h

private theorem bv64_ule_not_le {a b : BitVec 64} (h : a.ule b = false) : ¬ a.toNat ≤ b.toNat := by
  simpa [BitVec.ule] using h

private theorem bv64_ult_not_lt' {a b : BitVec 64} (h : a.ult b = false) : ¬ a.toNat < b.toNat :=
  bv64_ult_not_lt h

private theorem cd_ht_pow_step {ht_sz : BitVec 64} {k cap : Nat}
    (hk : k ≤ 10) (heq : ht_sz.toNat = 64 * 2 ^ k)
    (hlt : ht_sz.toNat < 65536) (hmul : ht_sz.toNat * 8 ≤ cap) :
    k + 1 ≤ 10 ∧ (ht_sz <<< (1#32 : BitVec 32).signExtend 64).toNat = 64 * 2 ^ (k + 1) ∧
    (ht_sz <<< (1#32 : BitVec 32).signExtend 64).toNat ≤ 65536 ∧
    (ht_sz <<< (1#32 : BitVec 32).signExtend 64).toNat ≤ cap := by
  have hk_lt : k < 10 :=
    Nat.lt_of_le_of_ne hk fun h => by subst h; rw [heq] at hlt; simp at hlt
  have hshl : (ht_sz <<< (1#32 : BitVec 32).signExtend 64).toNat = 2 * ht_sz.toNat := by
    change (ht_sz <<< (1 : Nat)).toNat = 2 * ht_sz.toNat
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
    exact Nat.mod_eq_of_lt (by omega)
  have h2k : 2 ^ k ≤ 2 ^ 9 := Nat.pow_le_pow_right (by omega) (by omega : k ≤ 9)
  have hpow : 64 * 2 ^ (k + 1) = 2 * (64 * 2 ^ k) := by rw [Nat.pow_succ]; omega
  refine ⟨by omega, by rw [hshl, heq, hpow], by rw [hshl, heq]; omega, by rw [hshl]; omega⟩

private theorem cd_ht_mul8_toNat {ht_sz : BitVec 64} (hle : ht_sz.toNat ≤ 65536) :
    (ht_sz * 8#64).toNat = ht_sz.toNat * 8 := by
  rw [BitVec.toNat_mul, show (8#64 : BitVec 64).toNat = 8 from rfl,
    Nat.mod_eq_of_lt (by omega)]

private theorem cd_repr_init_inv {F_cur : List (List Nat)} {repri : List (BitVec 32)}
    {cv0 maxv : Nat} (hrl : repri.length = 2 * maxv) (hcv : cv0 ≤ maxv)
    (hmax : maxv < 2 * dimacsBound)
    (hinit : ∀ k < 2 * cv0, repri[k]? = some (BitVec.ofNat 32 k)) :
    FullCongReprInv F_cur (2 * cv0) repri := by
  unfold dimacsBound at hmax
  refine ⟨⟨by omega, fun l hl => ?_⟩, fun l hl => ?_⟩
  · rw [hinit l hl, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact Nat.le_refl _
  · rw [hinit l hl, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact LitEquiv.refl _ _

private theorem cd_ht_clear_inv {F_cur : List (List Nat)} {cv0 g_len ht_off ht_sz : Nat}
    {scr0 scri : List (BitVec 32)} (hpref : ∀ idx < g_len, scri[idx]? = scr0[idx]?)
    (hinit : ∀ k < ht_sz, scri[ht_off + k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    (∀ idx < g_len, scri[idx]? = scr0[idx]?) ∧
    FullCongSpecs.CongHtInv F_cur cv0 scr0 scri g_len ht_off ht_sz :=
  ⟨hpref, fun k hk => Or.inl (hinit k hk)⟩

private theorem cd_workStepOk_of_scr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 g_len ht_off ht_sz : Nat}
    {scr0 scri : List (BitVec 32)} {st : FullState}
    (hok : WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 st)
    (hscrl : scri.length = c.scratch_cap)
    (hpref : ∀ idx < g_len, scri[idx]? = scr0[idx]?)
    (hht : FullCongSpecs.CongHtInv F_cur cv0 scr0 scri g_len ht_off ht_sz) :
    WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0
      { st with scratch := { st.scratch with scratch_buf := scri, res_sz := 0#64 } } := by
  have hext' := fullExtScratchOk_of_eq hok.2.2.2.2.1 rfl rfl rfl rfl
  exact ⟨⟨hok.1.core_ok, { hok.1.scratch_ok with scratch_buf_len := hscrl }⟩,
    hok.2.1, hok.2.2.1, hok.2.2.2.1, hext', hok.2.2.2.2.2.1, hok.2.2.2.2.2.2.1,
    hok.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.2.1,
    hok.2.2.2.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.2.2.2.1, hpref, hht⟩

private theorem cd_workStepOk_with_tmk {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 g_len ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {st : FullState} {tmki : List (BitVec 32)}
    (hok : WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 st)
    (htl : tmki.length = 2 * c.max_vars) :
    WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0
      { st with scratch := { st.scratch with tarjan_mark := tmki } } :=
  ⟨⟨hok.1.core_ok, { hok.1.scratch_ok with tarjan_mark_len := htl }⟩,
    hok.2.1, hok.2.2.1, hok.2.2.2.1, fullExtScratchOk_of_eq hok.2.2.2.2.1 rfl rfl rfl rfl,
    hok.2.2.2.2.2.1, hok.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.1,
    hok.2.2.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.2.2.2.1,
    hok.2.2.2.2.2.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

private theorem cd_denseInv_of_workStepOk {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 g_len ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {st : FullState}
    (hok : WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 st) :
    FullDenseInv c F0 st ∧ st.core.cur_vars = cv0 ∧ st.core.fuel = fuel0 :=
  ⟨⟨⟨hok.1, F_cur, hok.2.1⟩, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1,
    hok.2.2.2.2.2.1, hok.2.2.2.2.2.2.1⟩,
   hok.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.1⟩

private theorem cd_denseInv_with_tmk_res0 {c : FullCfg} {F0 : CNF Nat} {st : FullState}
    (hden : FullDenseInv c F0 st) {tmki : List (BitVec 32)} (htl : tmki.length = 2 * c.max_vars) :
    FullDenseInv c F0
      { st with scratch := { st.scratch with tarjan_mark := tmki, res_sz := 0#64 } } :=
  fullDenseInv_with_scratch_keep hden
    { hden.lengths.scratch_ok with tarjan_mark_len := htl } rfl rfl

private theorem cd_ht_set_step {g_len ht_off i : Nat} {scr0 scri : List (BitVec 32)}
    (hg_le : g_len ≤ ht_off) (hinv1 : ∀ idx < g_len, scri[idx]? = scr0[idx]?)
    (hinv2 : ∀ k < i, scri[ht_off + k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32)
    (hi_len : ht_off + i < scri.length) :
    (∀ idx < g_len, (scri.set (ht_off + i) 0xFFFFFFFF#32)[idx]? = scr0[idx]?) ∧
    (∀ k < i + 1,
      (scri.set (ht_off + i) 0xFFFFFFFF#32)[ht_off + k]?.getD 0xFFFFFFFF#32 =
        0xFFFFFFFF#32) := by
  refine ⟨fun idx hidx => ?_, fun k hk => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hinv1 idx hidx
  · by_cases hki : k = i
    · subst hki; rw [List.getElem?_set_self hi_len, Option.getD_some]
    · rw [List.getElem?_set_ne (by omega)]; exact hinv2 k (by omega)

/-- **#6 (`full_congruence_dense`)**: ticks-bounded dense congruence closure (adaptive HT up to
`65536`, epoch worklist, depth cap lifted), returning `1#64` or `20#64` (`F0.Unsat`). -/
theorem m3_congruence_dense_wp (Γ : Env)
    (hExtract : ∀ a m Q X, fullCongExtractTickSpec a m Q X →
      Γ "full_cong_extract" [i64, i64, i64] [i64] a m Q X)
    (hWork : ∀ a m Q X, m3CongWorkStepSpec a m Q X →
      Γ "full_cong_work_step" [i64, i64, i64, i64, i32] [i64] a m Q X) :
    ∀ a m Q X, m3CongruenceDenseSpec a m Q X → Func.wp Γ full_congruence_dense_body a m Q X := by
  rintro ⟨h, tick_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hden0, hm0, hQ⟩
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx
  have hcore0 := hden0.1
  have hmk0 := hden0.2.1
  have hnd0 := hden0.2.2.1
  have hext0 := hden0.2.2.2.1
  have hcl0 := hden0.2.2.2.2.1
  have hdm0 := hden0.2.2.2.2.2
  obtain ⟨F_cur, hw0⟩ := hcore0.witness
  have hlen0 := hcore0.lengths
  have hcv_le := hlen0.core_ok.cur_vars_le
  have hrl0 := hlen0.core_ok.repr_len
  have htl0 := hlen0.scratch_ok.tarjan_mark_len
  let cv0 := s.core.cur_vars; let fuel0 := s.core.fuel
  let ar0 := s.core.arena; let alen0 := s.core.arena_len
  unfold Func.wp full_congruence_dense_body
  m3_split_fast
  · m3_steps; exact hQ 1#64 s m0 hden0 rfl rfl (Or.inl rfl) (fun h => by cases h) hm0
  · have h256 : 256 ≤ c.scratch_cap := by
      have hnot := bv64_ult_not_lt hc
      rw [show (256 : BitVec 64).toNat = 256 from rfl, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)] at hnot
      omega
    clear hc; m3_split_fast
    · m3_steps; exact hQ 1#64 s m0 hden0 rfl rfl (Or.inl rfl) (fun h => by cases h) hm0
    · clear hc; m3_steps
      refine wp_loop_inv
        (fun (ht_sz, ()) mht => mht = m0 ∧ ∃ k : Nat,
          k ≤ 10 ∧ ht_sz.toNat = 64 * 2 ^ k ∧ ht_sz.toNat ≤ 65536 ∧
          ht_sz.toNat ≤ c.scratch_cap)
        (fun (ht_sz, ()) _ => 65536 - ht_sz.toNat)
        (fun Jht hJht => by
          m3_steps; exact hJht (64#64, ()) m0 ⟨rfl, 0, Nat.zero_le _, rfl, by decide, by
            change 64 ≤ c.scratch_cap; omega⟩)
        (fun Jht (ht_sz, ()) mht ⟨hmht, k, hk_le, hpow, h65, hsc_le⟩ ih_ht => ?_)
      subst hmht
      have hht_pos : 0 < ht_sz.toNat := by
        rw [hpow]; exact Nat.mul_pos (by decide) (Nat.two_pow_pos _)
      m3_to_group
      refine wp_join_group (ts := []) (fun () me => me = mht) ?_ ?_
      · rintro _ ⟨⟩ me rfl
        have hht_off_n : (BitVec.ofNat 64 c.scratch_cap - ht_sz).toNat =
            c.scratch_cap - ht_sz.toNat := by
          rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hsc_le)),
            BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        let ht_off := BitVec.ofNat 64 c.scratch_cap - ht_sz
        have hht_off_lt : ht_off.toNat + ht_sz.toNat ≤ c.scratch_cap := by
          dsimp only [ht_off]; rw [hht_off_n]; omega
        have hcv0_lt : cv0 < 2 ^ 32 := by dsimp only [cv0]; omega
        have hcv0_64 : cv0 < 2 ^ 64 := Nat.lt_trans hcv0_lt (by decide)
        have h2cv0_64 : 2 * cv0 < 2 ^ 64 := by omega
        have hcv0_le : cv0 ≤ c.max_vars := hcv_le
        m3_steps; m3_call hExtract
        refine ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hnd0, hcl0, by omega, hm0,
          fun g_len scr1 m1 hscrl1 hgl_le hseq1 hm1 => ?_⟩
        let s1 : FullState := { s with scratch := { s.scratch with scratch_buf := scr1 } }
        have hden1 : FullDenseInv c F0 s1 :=
          fullDenseInv_with_scratch_keep hden0 { hlen0.scratch_ok with scratch_buf_len := hscrl1 }
            rfl rfl
        m3_split_fast
        · m3_steps; exact hQ 1#64 s1 m1 hden1 rfl rfl (Or.inl rfl) (fun h => by cases h) hm1
        · have hg_pos : 0 < g_len.toNat := by
            have hne := beq_eq_false_iff_ne.mp hc
            rcases Nat.eq_zero_or_pos g_len.toNat with hz | hp
            · exact absurd (BitVec.eq_of_toNat_eq hz) hne
            · exact hp
          clear hc
          m3_steps
          refine wp_loop_inv
            (fun (i, ()) mi => ∃ repri : List (BitVec 32),
              repri.length = 2 * c.max_vars ∧ i.toNat ≤ 2 * cv0 ∧
              (∀ k' < i.toNat, repri[k']? = some (BitVec.ofNat 32 k')) ∧
              (FullMem c { s1 with core := { s1.core with repr := repri } } ⋆ R) mi)
            (fun (i, ()) _ => 2 * cv0 - i.toNat)
            (fun Ji hJi => by
              m3_steps; exact hJi (0#64, ()) m1 ⟨s1.core.repr, hrl0, Nat.zero_le _,
                fun _ h => by simp at h, hm1⟩)
            (fun Ji (i, ()) mi ⟨repri, hrli, hi_le, hinit, hmi⟩ ihi => ?_)
          m3_split_fast
          · have hi_lt : i.toNat < 2 * cv0 := by
              have hlt := bv64_ult_lt hc
              change i.toNat < (BitVec.ofNat 64 cv0 <<< (1 : Nat)).toNat at hlt
              rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt hcv0_64, Nat.mod_eq_of_lt h2cv0_64] at hlt
              exact hlt
            have hi1_n : (i + 1#64).toNat = i.toNat + 1 :=
              bv64_add1_toNat (n := 2 * cv0) hi_lt h2cv0_64
            have hi_arr : i.toNat < repri.length := by omega
            have hi_tr : i.setWidth 32 = BitVec.ofNat 32 i.toNat := by
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
            m3_steps
            exact ihi (i + 1#64, ()) m (by dsimp only; omega)
              ⟨repri.set i.toNat (i.setWidth 32), by simp [hrli], by omega,
               fun k' hk' => by
                 rw [hi1_n] at hk'
                 by_cases hki : k' = i.toNat
                 · subst hki; rw [List.getElem?_set_self (by omega), hi_tr]
                 · rw [List.getElem?_set_ne (Ne.symm hki)]; exact hinit k' (by omega),
               hm⟩
          · have hi_eq : i.toNat = 2 * cv0 := by
              have hnot := bv64_ult_not_lt hc
              change ¬ i.toNat < (BitVec.ofNat 64 cv0 <<< (1 : Nat)).toNat at hnot
              rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt hcv0_64, Nat.mod_eq_of_lt h2cv0_64] at hnot
              omega
            rw [hi_eq] at hinit
            have hrepr2 : FullCongReprInv F_cur (2 * cv0) repri :=
              cd_repr_init_inv hrli hcv_le hmx hinit
            let s2 : FullState := { s1 with core := { s1.core with repr := repri } }
            have hlen2 : s2.LengthsOk c := ⟨{ hlen0.core_ok with repr_len := hrli },
              { hlen0.scratch_ok with scratch_buf_len := hscrl1 }⟩
            have hw2 : FullWitnessInv c F0 F_cur s2.core := fullWitnessInv_with_repr hw0 repri
            clear hc; m3_steps
            refine wp_loop_inv
              (fun (i2, ()) mt => ∃ tmki : List (BitVec 32),
                tmki.length = 2 * c.max_vars ∧ i2.toNat ≤ cv0 ∧
                (FullMem c { s2 with scratch := { s2.scratch with tarjan_mark := tmki } } ⋆ R) mt)
              (fun (i2, ()) _ => cv0 - i2.toNat)
              (fun Jt hJt => by
                m3_steps
                exact hJt (0#64, ()) mi ⟨s2.scratch.tarjan_mark, htl0, Nat.zero_le _, hmi⟩)
              (fun Jt (i2, ()) mt ⟨tmki, htli, hi2_le, hmt⟩ iht => ?_)
            m3_split_fast
            · have hi2_lt : i2.toNat < cv0 := by
                have hlt := bv64_ult_lt hc
                rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv0_64] at hlt
              have hi2_arr : i2.toNat < tmki.length := by omega
              have hi2_1 : (i2 + 1#64).toNat = i2.toNat + 1 :=
                bv64_add1_toNat (n := cv0) hi2_lt hcv0_64
              m3_steps
              exact iht (i2 + 1#64, ()) m (by dsimp only; omega)
                ⟨tmki.set i2.toNat 1#32, by simp [htli], by omega, hm⟩
            · clear hc
              let s3 : FullState :=
                { s2 with scratch := { s2.scratch with tarjan_mark := tmki } }
              have hlen3 : s3.LengthsOk c :=
                ⟨hlen2.core_ok, { hlen2.scratch_ok with tarjan_mark_len := htli }⟩
              m3_steps
              refine wp_loop_inv
                (fun (i3, ()) ms => ∃ scri : List (BitVec 32),
                  scri.length = c.scratch_cap ∧ i3.toNat ≤ ht_sz.toNat ∧
                  (∀ idx < g_len.toNat, scri[idx]? = scr1[idx]?) ∧
                  (∀ k' < i3.toNat, scri[ht_off.toNat + k']?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) ∧
                  (FullMem c { s3 with scratch := { s3.scratch with scratch_buf := scri } } ⋆ R) ms)
                (fun (i3, ()) _ => ht_sz.toNat - i3.toNat)
                (fun Js hJs => by
                  m3_steps; exact hJs (0#64, ()) mt ⟨scr1, hscrl1, Nat.zero_le _,
                    fun _ _ => rfl, fun _ h => by simp at h, hmt⟩)
                (fun Js (i3, ()) ms ⟨scri, hscrl_i, hi3_le, hpref_i, hinit_i, hms⟩ ihs => ?_)
              m3_split_fast
              · have hi3_lt : i3.toNat < ht_sz.toNat := bv64_ult_lt hc
                have hi3_1 : (i3 + 1#64).toNat = i3.toNat + 1 :=
                  bv64_add1_toNat (n := ht_sz.toNat) hi3_lt (by omega)
                have hadd_n : (ht_off + i3).toNat = ht_off.toNat + i3.toNat := by
                  show (ht_off.toNat + i3.toNat) % 2 ^ 64 = ht_off.toNat + i3.toNat
                  exact Nat.mod_eq_of_lt (by omega)
                have hadd_arr : (ht_off + i3).toNat < scri.length := by rw [hadd_n]; omega
                m3_steps
                rw [hadd_n] at hm
                obtain ⟨hpref_i', hinit_i'⟩ := cd_ht_set_step (g_len := g_len.toNat)
                  (ht_off := ht_off.toNat) (i := i3.toNat) (by omega) hpref_i hinit_i
                  (by omega)
                exact ihs (i3 + 1#64, ()) m (by dsimp only; omega)
                  ⟨scri.set (ht_off.toNat + i3.toNat) 0xFFFFFFFF#32, by simp [hscrl_i], by omega,
                   hpref_i', hi3_1 ▸ hinit_i', hm⟩
              · have hi3_eq : i3.toNat = ht_sz.toNat := by
                  have := bv64_ult_not_lt hc; omega
                rw [hi3_eq] at hinit_i; clear hc
                obtain ⟨hpref4, hht4⟩ := cd_ht_clear_inv hpref_i hinit_i
                let s4 : FullState :=
                  { s3 with scratch := { s3.scratch with scratch_buf := scri, res_sz := 0#64 } }
                have hok4 : WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat
                    ht_sz.toNat scr1 s4 :=
                  ⟨⟨hlen3.core_ok, { hlen3.scratch_ok with scratch_buf_len := hscrl_i }⟩,
                   hw2, hmk0, hnd0, fullExtScratchOk_of_eq hext0 rfl rfl rfl rfl,
                   hcl0, hdm0, rfl, rfl, rfl, rfl, hrepr2, hpref4, hht4⟩
                m3_to_group
                refine wp_join_group (ts := [i64])
                  (fun (mp, ()) mmp => mmp = m ∧ mp.toNat ≤ 0x7FFFFFFF)
                  (fun _ ⟨mp, ⟨⟩⟩ mmp hmmp => by
                    obtain ⟨hmmp_eq, hmp_le⟩ := hmmp
                    rw [hmmp_eq]
                    m3_to_group
                    refine wp_loop_break_group
                      (fun _ mb => ∃ sb : FullState,
                        FullDenseInv c F0 sb ∧ sb.core.cur_vars = cv0 ∧
                        sb.core.fuel = fuel0 ∧ sb.scratch.tarjan_mark.length = 2 * c.max_vars ∧
                        (FullMem c sb ⋆ R) mb)
                      (fun rem (_, pass, ticks, rehashes, ()) ml => ∃ sp : FullState,
                        pass.toNat ≤ mp.toNat ∧ rem = mp.toNat - pass.toNat ∧
                        rehashes.toNat ≤ 4 ∧ sp.scratch.tarjan_mark.length = 2 * c.max_vars ∧
                        WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat
                          ht_sz.toNat scr1 sp ∧
                        (FullMem c sp ⋆ R) ml)
                      ?_ ?_ ?_
                    · rintro _ _ mb ⟨sb, hdenb, hcvb, hfub, htlb, hmb⟩
                      m3_steps
                      refine wp_loop_inv
                        (fun (ie, ()) me => ∃ tmke : List (BitVec 32),
                          tmke.length = 2 * c.max_vars ∧ ie.toNat ≤ cv0 ∧
                          (FullMem c { sb with scratch :=
                            { sb.scratch with tarjan_mark := tmke } } ⋆ R) me)
                        (fun (ie, ()) _ => cv0 - ie.toNat)
                        (fun Je hJe => by
                          m3_steps; exact hJe (0#64, ()) mb ⟨sb.scratch.tarjan_mark, htlb,
                            Nat.zero_le _, hmb⟩)
                        (fun Je (ie, ()) me ⟨tmke, htle, hie_le, hme⟩ ihe => ?_)
                      m3_split_fast
                      · have hie_lt : ie.toNat < cv0 := by
                          have hlt := bv64_ult_lt hc
                          change ie.toNat < (BitVec.ofNat 64 cv0).toNat at hlt
                          rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv0_64] at hlt
                        have hie_arr : ie.toNat < tmke.length := by omega
                        have hie1 : (ie + 1#64).toNat = ie.toNat + 1 :=
                          bv64_add1_toNat (n := cv0) hie_lt (by omega)
                        m3_steps
                        exact ihe (ie + 1#64, ()) m (by dsimp only; omega)
                          ⟨tmke.set ie.toNat 0#32, by simp [htle], by omega, hm⟩
                      · clear hc
                        let sf : FullState := { sb with scratch :=
                          { sb.scratch with tarjan_mark := tmke, res_sz := 0#64 } }
                        have hdenf : FullDenseInv c F0 sf := cd_denseInv_with_tmk_res0 hdenb htle
                        m3_steps
                        · have hinc : sf.core.inconsistent ≠ 0#64 := hc
                          obtain ⟨_, hw_f⟩ := hdenf.1.witness
                          exact hJ _ _ (hQ 20#64 sf m hdenf hcvb hfub (Or.inr rfl)
                            (fun _ => unsat_of_inconsistent_w hw_f hinc) hm)
                        · exact hJ _ _ (hQ 1#64 sf m hdenf hcvb hfub (Or.inl rfl)
                            (fun h => by cases h) hm)
                    · rintro B L rem ⟨i_lp, pass, ticks, rehashes, ⟨⟩⟩ ml hB hL
                        ⟨sp, hpass_le, rfl, hreh_le, htlp, hokp, hml⟩
                      have hcvp := hokp.2.2.2.2.2.2.2.1
                      have hfup := hokp.2.2.2.2.2.2.2.2.1
                      have hbrk_p : B (i_lp, pass, ticks, rehashes, ()) ml :=
                        hB (i_lp, pass, ticks, rehashes, ()) ml
                          ⟨sp, (cd_denseInv_of_workStepOk hokp).1, hcvp, hfup, htlp, hml⟩
                      m3_split_fast
                      · have hpass_lt : pass.toNat < mp.toNat := bv64_ult_lt hc
                        have hpass1 : (pass + 1#64).toNat = pass.toNat + 1 :=
                          bv64_add1_toNat (n := mp.toNat) hpass_lt (by omega)
                        clear hc; m3_split_fast
                        · clear hc; m3_split_fast
                          · clear hc
                            m3_steps; m3_call hWork
                            refine ⟨c, F0, F_cur, sp, scr1, R, rfl, hokp.1, hokp.2.1, hokp.2.2.1,
                              hokp.2.2.2.1, hokp.2.2.2.2.1, hokp.2.2.2.2.2.1, hokp.2.2.2.2.2.2.1,
                              hcvp ▸ hokp.2.2.2.2.2.2.2.2.2.2.2.1, hht_pos, by omega, by omega,
                              hcvp ▸ hseq1, hokp.2.2.2.2.2.2.2.2.2.2.2.2.1,
                              hcvp ▸ hokp.2.2.2.2.2.2.2.2.2.2.2.2.2,
                              hml, fun ret sq mq hlenq hwq hmkq hndq hextq hclq hdmq hcvq hfuq harq
                                halq hreprq hprefq hhtq hdomq _ hmq => ?_⟩
                            have hcvq0 : sq.core.cur_vars = cv0 := hcvq.trans hcvp
                            have hokq' : WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat
                                ht_off.toNat ht_sz.toNat scr1 sq :=
                              ⟨hlenq, hwq, hmkq, hndq, hextq, hclq, hdmq, hcvq0,
                               hfuq.trans hfup, harq.trans hokp.2.2.2.2.2.2.2.2.2.1,
                               halq.trans hokp.2.2.2.2.2.2.2.2.2.2.1,
                               hcvq0 ▸ hreprq, hprefq, hcvq0 ▸ hhtq⟩
                            have hdenq := (cd_denseInv_of_workStepOk hokq').1
                            have hfuq0 := hokq'.2.2.2.2.2.2.2.2.1
                            have htlq := hokq'.1.scratch_ok.tarjan_mark_len
                            m3_split_fast
                            · m3_steps
                              exact hB (i_lp, pass, ticks + (ret >>> 2#64), rehashes, ()) mq
                                ⟨sq, hdenq, hcvq0, hfuq0, htlq, hmq⟩
                            · clear hc
                              m3_to_group
                              refine wp_join_group (ts := [i64, i64])
                                (fun (_, r', ()) mj => ∃ sj : FullState,
                                  r'.toNat ≤ 4 ∧
                                  sj.scratch.tarjan_mark.length = 2 * c.max_vars ∧
                                  WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat
                                    ht_off.toNat ht_sz.toNat scr1 sj ∧ (FullMem c sj ⋆ R) mj)
                                (fun _ (i_j, r', ()) mj ⟨sj, hrj, htlj, hokj, hmj⟩ => by
                                  m3_steps
                                  exact hL (mp.toNat - (pass + 1#64).toNat)
                                    (i_j, pass + 1#64, ticks + (ret >>> 2#64), r', ()) mj
                                    (by omega) ⟨sj, by omega, rfl, hrj, htlj, hokj, hmj⟩)
                                ?_
                              intro Jre hJre
                              m3_to_group
                              refine wp_join_group (ts := []) (fun () me => me = mq)
                                (fun _ ⟨⟩ me hme => by
                                  rw [hme]; m3_split_fast
                                  · m3_steps
                                    exact hB (i_lp, pass, ticks + (ret >>> 2#64), rehashes, ()) mq
                                      ⟨sq, hdenq, hcvq0, hfuq0, htlq, hmq⟩
                                  · m3_let
                                    exact hJre (i_lp, rehashes, ()) mq
                                      ⟨sq, hreh_le, htlq, hokq', hmq⟩)
                                ?_
                              intro Jelse hJelse
                              m3_split_fast
                              · m3_split_fast
                                · have hreh_lt : rehashes.toNat < 4 := bv64_ult_lt hc
                                  have hreh1 : (rehashes + 1#64).toNat = rehashes.toNat + 1 :=
                                    bv64_add1_toNat (n := 4) hreh_lt (by decide)
                                  clear hc; m3_steps
                                  refine wp_loop_inv
                                    (fun (ir, ()) mr => ∃ scrr : List (BitVec 32),
                                      scrr.length = c.scratch_cap ∧ ir.toNat ≤ ht_sz.toNat ∧
                                      (∀ idx < g_len.toNat, scrr[idx]? = scr1[idx]?) ∧
                                      (∀ k' < ir.toNat,
                                        scrr[ht_off.toNat + k']?.getD 0xFFFFFFFF#32 =
                                          0xFFFFFFFF#32) ∧
                                      (FullMem c { sq with scratch :=
                                        { sq.scratch with scratch_buf := scrr } } ⋆ R) mr)
                                    (fun (ir, ()) _ => ht_sz.toNat - ir.toNat)
                                    (fun Jr hJr => by
                                      m3_steps; exact hJr (0#64, ()) mq
                                        ⟨sq.scratch.scratch_buf,
                                         hokq'.1.scratch_ok.scratch_buf_len, Nat.zero_le _,
                                         hprefq, fun _ h => by simp at h, hmq⟩)
                                    (fun Jr (ir, ()) mr
                                        ⟨scrr, hscrr, hir_le, hprefr, hinitr, hmr⟩ ihr => ?_)
                                  m3_split_fast
                                  · have hir_lt : ir.toNat < ht_sz.toNat := bv64_ult_lt hc
                                    have hir1 : (ir + 1#64).toNat = ir.toNat + 1 :=
                                      bv64_add1_toNat (n := ht_sz.toNat) hir_lt (by omega)
                                    have hadd_n : (ht_off + ir).toNat =
                                        ht_off.toNat + ir.toNat := by
                                      show (ht_off.toNat + ir.toNat) % 2 ^ 64 =
                                        ht_off.toNat + ir.toNat
                                      exact Nat.mod_eq_of_lt (by omega)
                                    have hadd_arr : (ht_off + ir).toNat < scrr.length := by
                                      rw [hadd_n]; omega
                                    m3_steps; rw [hadd_n] at hm
                                    obtain ⟨hprefr', hinitr'⟩ := cd_ht_set_step
                                      (g_len := g_len.toNat) (ht_off := ht_off.toNat)
                                      (i := ir.toNat) (by omega) hprefr hinitr (by omega)
                                    exact ihr (ir + 1#64, ()) m (by dsimp only; omega)
                                      ⟨scrr.set (ht_off.toNat + ir.toNat) 0xFFFFFFFF#32,
                                       by simp [hscrr], by omega, hprefr', hir1 ▸ hinitr', hm⟩
                                  · have hir_eq : ir.toNat = ht_sz.toNat := by
                                      have := bv64_ult_not_lt hc; omega
                                    rw [hir_eq] at hinitr; clear hc
                                    obtain ⟨hprefr', hhtr'⟩ := cd_ht_clear_inv hprefr hinitr
                                    let sr1 : FullState :=
                                      { sq with scratch := { sq.scratch with
                                        scratch_buf := scrr, res_sz := 0#64 } }
                                    have hokr1 := cd_workStepOk_of_scr hokq' hscrr hprefr' hhtr'
                                    m3_steps
                                    refine wp_loop_inv
                                      (fun (it, ()) mtt => ∃ tmkt : List (BitVec 32),
                                        tmkt.length = 2 * c.max_vars ∧ it.toNat ≤ cv0 ∧
                                        (FullMem c { sr1 with scratch :=
                                          { sr1.scratch with tarjan_mark := tmkt } } ⋆ R) mtt)
                                      (fun (it, ()) _ => cv0 - it.toNat)
                                      (fun Jt' hJt' => by
                                        m3_steps; exact hJt' (0#64, ()) m
                                          ⟨sr1.scratch.tarjan_mark, htlq, Nat.zero_le _, hm⟩)
                                      (fun Jt' (it, ()) mtt
                                          ⟨tmkt, htlt, hit_le, hmtt⟩ iht' => ?_)
                                    m3_split_fast
                                    · have hit_lt : it.toNat < cv0 := by
                                        have hlt := bv64_ult_lt hc
                                        change it.toNat < (BitVec.ofNat 64 cv0).toNat at hlt
                                        rwa [BitVec.toNat_ofNat,
                                          Nat.mod_eq_of_lt hcv0_64] at hlt
                                      have hit_arr : it.toNat < tmkt.length := by omega
                                      have hit1 : (it + 1#64).toNat = it.toNat + 1 :=
                                        bv64_add1_toNat (n := cv0) hit_lt (by omega)
                                      m3_steps
                                      exact iht' (it + 1#64, ()) m (by dsimp only; omega)
                                        ⟨tmkt.set it.toNat _, by simp [htlt], by omega, hm⟩
                                    · clear hc; m3_steps
                                      exact hJre (it, rehashes + 1#64, ()) mtt
                                        ⟨_, by omega, htlt, cd_workStepOk_with_tmk hokr1 htlt,
                                         hmtt⟩
                                · clear hc; m3_steps; exact hJelse () mq rfl
                              · clear hc; m3_steps; exact hJelse () mq rfl
                          · clear hc; m3_steps; exact hbrk_p
                        · clear hc; m3_steps; exact hbrk_p
                      · clear hc; m3_steps; exact hbrk_p
                    · intro _ Lp _ hLp; m3_steps
                      exact hLp mp.toNat (i3, 0#64, 0#64, 0#64, ()) m
                        ⟨s4, Nat.zero_le _, rfl, Nat.zero_le _, htli, hok4, hm⟩)
                  (fun Jmp hJmp => by
                    m3_split_fast
                    · m3_steps; exact hJmp (0x7FFFFFFF#64, ()) m ⟨rfl, by decide⟩
                    · have hle : ((BitVec.ofNat 64 cv0 <<< (1 : Nat)) + 4#64).toNat ≤
                          0x7FFFFFFF := by
                        have hnot := bv64_ult_not_lt hc
                        change ¬ (0x7FFFFFFF : BitVec 64).toNat <
                          ((BitVec.ofNat 64 cv0 <<< (1 : Nat)) + 4#64).toNat at hnot
                        rw [show (0x7FFFFFFF : BitVec 64).toNat = 0x7FFFFFFF from rfl] at hnot
                        omega
                      m3_let; exact hJmp (_, ()) m ⟨rfl, hle⟩)
      · intro Jht_exit hJht_exit
        m3_split_fast
        · have hmul_le : ht_sz.toNat * 8 ≤ c.scratch_cap := by
            have hle := bv64_ule_le hc
            rw [show (8 : BitVec 64) = 8#64 from rfl, cd_ht_mul8_toNat h65,
              BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hle
            exact hle
          clear hc; m3_split_fast
          · have hlt : ht_sz.toNat < 65536 := bv64_ult_lt hc
            obtain ⟨hk1, hpow1, h651, hsc1⟩ := cd_ht_pow_step hk_le hpow hlt hmul_le
            m3_steps; exact ih_ht (ht_sz <<< (1#32 : BitVec 32).signExtend 64, ()) mht
              (by dsimp only; rw [hpow1, hpow]; omega) ⟨rfl, k + 1, hk1, hpow1, h651, hsc1⟩
          · m3_let; exact hJht_exit () mht rfl
        · m3_let; exact hJht_exit () mht rfl

end CongruenceDenseProof

/-! ## 2. `#7` `m3_elim_collect_nbrs_wp` Helpers & Proof -/

section CollectNbrsProof

open scoped FullArenaTactics FullCongTactics M3HeadTactics

private abbrev colState (s : FullState) (mclr ws2 : List (BitVec 32)) : FullState :=
  { s with
    core := { s.core with min_clr := mclr }
    scratch := { s.scratch with work_stk2 := ws2 } }

private theorem col_mem_cast {c : FullCfg} {s : FullState}
    {mclr1 mclr2 ws1 ws2 : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c { s with
      core := { s.core with min_clr := mclr1 }
      scratch := { s.scratch with work_stk2 := ws1 } } ⋆ R) m)
    (h1 : mclr1 = mclr2) (h2 : ws1 = ws2) :
    (FullMem c (colState s mclr2 ws2) ⋆ R) m := by
  subst h1 h2; exact hm

private theorem colState_lens {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c)
    {mclr ws2 : List (BitVec 32)} (hml : mclr.length = c.max_vars)
    (hwl : ws2.length = 2 * c.max_vars) : (colState s mclr ws2).LengthsOk c :=
  ⟨{ hlen.core_ok with min_clr_len_arr := hml }, { hlen.scratch_ok with work_stk2_len := hwl }⟩

private theorem col_lit_toNat {v pol : BitVec 32} {cv : Nat} (hv : v.toNat < cv)
    (hpol : pol.toNat < 2) (hcv32 : 2 * cv < 2 ^ 32) :
    ((v <<< (1 : Nat)) ||| pol).toNat = 2 * v.toNat + pol.toNat := by
  have hp : pol = 0#32 ∨ pol = 1#32 := by
    rcases (by omega : pol.toNat = 0 ∨ pol.toNat = 1) with h0 | h1
    · left; exact BitVec.eq_of_toNat_eq h0
    · right; exact BitVec.eq_of_toNat_eq h1
  rcases hp with rfl | rfl
  · rw [BitVec.or_zero, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm,
      Nat.mod_eq_of_lt (by omega), show (0#32 : BitVec 32).toNat = 0 from rfl, Nat.add_zero]
  · have h1 : (v <<< (1 : Nat)) ||| 1#32 = BitVec.ofNat 32 (2 * v.toNat + 1) := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, hi,
        decide_true, Bool.true_and,
        show (1#32 : BitVec 32).getLsbD i = decide (i = 0) by cases i <;> simp]
      cases i with
      | zero => simp [Nat.testBit_zero]
      | succ k =>
        simp [Nat.testBit_succ, BitVec.testBit_toNat,
          show (2 * v.toNat + 1) / 2 = v.toNat by omega]
    rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      show (1#32 : BitVec 32).toNat = 1 from rfl]

private theorem col_wvec_idx_toNat {lit : BitVec 32} {cv : Nat} (_hl : lit.toNat < 2 * cv)
    (_hcv64 : 4 * cv < 2 ^ 64) :
    ((lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * lit.toNat) ∧
    ((lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat = 2 * lit.toNat + 1) := by
  have h1 : (lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * lit.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm, bv_zext32_toNat,
      Nat.mod_eq_of_lt (by omega)]
  refine ⟨h1, ?_⟩
  rw [BitVec.toNat_add, h1, show (1#64 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega)]

private theorem col_push_inv {ws2 : List (BitVec 32)} {nn : BitVec 64} {u : BitVec 32} {cv : Nat}
    (hu_lt : u.toNat < cv) (hnn_lt : nn.toNat < cv) (hcv_le : cv ≤ ws2.length)
    (hcv64 : cv < 2 ^ 64)
    (hsub : ∀ k < nn.toNat, (ws2[k]?.getD 0#32).toNat < cv) :
    (nn + 1#64).toNat = nn.toNat + 1 ∧
    (nn + 1#64).toNat ≤ cv ∧
    (ws2.set nn.toNat u).length = ws2.length ∧
    ∀ k < (nn + 1#64).toNat, ((ws2.set nn.toNat u)[k]?.getD 0#32).toNat < cv := by
  have hnn1 : (nn + 1#64).toNat = nn.toNat + 1 := bv64_add1_toNat (n := cv) hnn_lt hcv64
  refine ⟨hnn1, by omega, List.length_set, fun k hk => ?_⟩
  rw [hnn1] at hk
  by_cases hkn : k = nn.toNat
  · subst hkn; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hu_lt
  · rw [List.getElem?_set_ne (Ne.symm hkn)]; exact hsub k (by omega)

private theorem col_cr3_add_toNat {cr : BitVec 32} (hcr : cr.toNat + 3 < 2 ^ 64) :
    (cr.setWidth 64 + 3#64).toNat = cr.toNat + 3 := by
  rw [BitVec.toNat_add, bv_zext32_toNat, show (3#64 : BitVec 64).toNat = 3 from rfl,
    Nat.mod_eq_of_lt hcr]

private theorem col_cr3i_toNat {cr i : BitVec 32} {al : Nat}
    (hsz : cr.toNat + 3 + i.toNat < al) (hal64 : al < 2 ^ 64) :
    (cr.setWidth 64 + 3#64 + i.setWidth 64).toNat = cr.toNat + 3 + i.toNat := by
  have h3 : (cr.setWidth 64 + 3#64).toNat = cr.toNat + 3 :=
    col_cr3_add_toNat (by omega)
  rw [BitVec.toNat_add, h3, bv_zext32_toNat, Nat.mod_eq_of_lt (by omega)]

/-- **#7 (`full_elim_collect_nbrs`)**: collects active unassigned variable neighbors of `v` into
`work_stk2[0 ..< nn)` (clearing `min_clr` marks on exit), preserving `LengthsOk` and `< cv`. -/
theorem m3_elim_collect_nbrs_wp (Γ : Env) :
    ∀ a m Q X, m3ElimCollectNbrsSpec a m Q X →
      Func.wp Γ full_elim_collect_nbrs_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hden0, _htmk0, hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; have hac := c.harena
  unfold dimacsBound at hmx hwc hac
  obtain ⟨hcore0, _, _, _, _, _⟩ := hden0
  obtain ⟨F_cur, hw0⟩ := hcore0.witness
  have hlen0 := hcore0.lengths
  let cv := s.core.cur_vars
  have hcv_le : cv ≤ c.max_vars := hlen0.core_ok.cur_vars_le
  have hml0 : s.core.min_clr.length = c.max_vars := hlen0.core_ok.min_clr_len_arr
  have hwl0 : s.scratch.work_stk2.length = 2 * c.max_vars := hlen0.scratch_ok.work_stk2_len
  have hfl_len : s.core.flags.length = c.max_vars := hlen0.core_ok.flags_len
  have hv_len : s.core.vals.length = 2 * c.max_vars := hlen0.core_ok.vals_len
  have hwv_len : s.core.wvec.length = 4 * c.max_vars := hlen0.core_ok.wvec_len
  have hws_len : s.core.wstk.length = c.wcap := hlen0.core_ok.wstk_len_arr
  have hwlen_le : s.core.wlen ≤ c.wcap := hlen0.core_ok.wlen_le
  have har_len : s.core.arena.length = c.arena_cap := hlen0.core_ok.arena_len_arr
  have hal_le : s.core.arena_len ≤ c.arena_cap := hlen0.core_ok.arena_len_le
  unfold Func.wp full_elim_collect_nbrs_body
  m3_split_fast
  · m3_steps; exact hQ 0#64 s.core.min_clr s.scratch.work_stk2 m0 hlen0 (Nat.zero_le _)
      (fun _ hk => by simp at hk) hm0
  · have hv_lt : v.toNat < cv := by
      have hnot := bv64_ule_not_le hc
      rw [bv_zext32_toNat] at hnot
      have hmod : (BitVec.ofNat 64 cv).toNat = cv := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [hmod] at hnot; omega
    clear hc; m3_steps
    refine wp_loop_inv
      (fun (nn, pol, ()) mpol => ∃ mclr ws2 : List (BitVec 32),
        mclr.length = c.max_vars ∧ ws2.length = 2 * c.max_vars ∧
        pol.toNat ≤ 2 ∧ nn.toNat ≤ cv ∧
        (∀ k < nn.toNat, (ws2[k]?.getD 0#32).toNat < cv) ∧
        (FullMem c (colState s mclr ws2) ⋆ R) mpol)
      (fun (_, pol, ()) _ => 2 - pol.toNat)
      (fun Jp hJp => by
        m3_steps; exact hJp (0#64, 0#32, ()) m0 ⟨s.core.min_clr, s.scratch.work_stk2,
          hml0, hwl0, Nat.zero_le _, Nat.zero_le _, fun _ hk => by simp at hk, hm0⟩)
      (fun Jp (nn, pol, ()) mpol ⟨mclr, ws2, hml, hwl, hpol_le, hnn_le, hsub, hmpol⟩ ihp => ?_)
    m3_split_fast
    · have hpol_lt : pol.toNat < 2 := bv32_ult_lt hc
      have hpol1 : (pol + 1#32).toNat = pol.toNat + 1 :=
        bv32_add1_toNat (n := 2) hpol_lt (by decide)
      have hlit_n : ((v <<< (1 : Nat)) ||| pol).toNat = 2 * v.toNat + pol.toNat :=
        col_lit_toNat hv_lt hpol_lt (by omega)
      let lit := (v <<< (1 : Nat)) ||| pol
      have hlit_lt : lit.toNat < 2 * cv := by dsimp only [lit]; rw [hlit_n]; omega
      obtain ⟨hw0_n, hw1_n⟩ := col_wvec_idx_toNat hlit_lt (by omega)
      have hbd := hw0.watches.bounds lit.toNat hlit_lt
      unfold fullWatchOffCore fullWatchSizeCore at hbd
      have hw0_arr : (lit.setWidth 64 <<< (1 : Nat)).toNat < s.core.wvec.length := by
        rw [hw0_n, hwv_len]; omega
      have hw1_arr : (lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat < s.core.wvec.length := by
        rw [hw1_n, hwv_len]; omega
      have hoff_eq : (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hw0_arr).toNat =
          (s.core.wvec[2 * lit.toNat]?.getD 0#32).toNat := by
        rw [list_getElem_congr hw0_n hw0_arr (by rw [hwv_len]; omega),
          List.getElem?_eq_getElem (by rw [hwv_len]; omega), Option.getD_some]
      have hsz_eq : (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat]'hw1_arr).toNat =
          (s.core.wvec[2 * lit.toNat + 1]?.getD 0#32).toNat := by
        rw [list_getElem_congr hw1_n hw1_arr (by rw [hwv_len]; omega),
          List.getElem?_eq_getElem (by rw [hwv_len]; omega), Option.getD_some]
      let off := (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hw0_arr).setWidth 64
      let end_p := off +
        (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat]'hw1_arr).setWidth 64
      have hend_le : end_p.toNat ≤ c.wcap := by
        dsimp only [end_p, off]
        rw [BitVec.toNat_add, bv_zext32_toNat, bv_zext32_toNat, hoff_eq, hsz_eq,
          Nat.mod_eq_of_lt (by omega)]
        omega
      clear hc; m3_to_group
      refine wp_loop_break_group
        (fun (nn_b, _p_b, ()) mb => ∃ mclr_b ws2_b : List (BitVec 32),
          mclr_b.length = c.max_vars ∧ ws2_b.length = 2 * c.max_vars ∧
          nn_b.toNat ≤ cv ∧ (∀ k < nn_b.toNat, (ws2_b[k]?.getD 0#32).toNat < cv) ∧
          (FullMem c (colState s mclr_b ws2_b) ⋆ R) mb)
        (fun rem (nn_l, p, ()) ml => ∃ mclr_l ws2_l : List (BitVec 32),
          mclr_l.length = c.max_vars ∧ ws2_l.length = 2 * c.max_vars ∧
          p.toNat ≤ end_p.toNat ∧ rem = end_p.toNat - p.toNat ∧ nn_l.toNat ≤ cv ∧
          (∀ k < nn_l.toNat, (ws2_l[k]?.getD 0#32).toNat < cv) ∧
          (FullMem c (colState s mclr_l ws2_l) ⋆ R) ml)
        ?_ ?_ ?_
      · rintro _ ⟨nn_b, _p_b, ⟨⟩⟩ mb ⟨mclr_b, ws2_b, hmlb, hwlb, hnn_b, hsub_b, hmb⟩
        m3_steps; exact ihp (nn_b, pol + 1#32, ()) mb (by dsimp only; omega)
          ⟨mclr_b, ws2_b, hmlb, hwlb, by omega, hnn_b, hsub_b, hmb⟩
      · rintro B L rem ⟨nn_l, p, ⟨⟩⟩ ml hB hL
          ⟨mclr_l, ws2_l, hml_l, hwl_l, hp_le, rfl, hnn_l, hsub_l, hml⟩
        m3_split_fast
        · have hp_lt : p.toNat < end_p.toNat := bv64_ult_lt hc
          have hp_ws : p.toNat < s.core.wstk.length := by rw [hws_len]; omega
          have hp1 : (p + 1#64).toNat = p.toNat + 1 :=
            bv64_add1_toNat (n := end_p.toNat) hp_lt (by omega)
          let w0 := s.core.wstk[p.toNat]'hp_ws
          clear hc; m3_split_fast
          · -- Binary watch branch (`(w0 & PW_BIN_FLAG) != 0`)
            let u := (w0 &&& 0x7FFFFFFF#32) >>> 1#32
            clear hc; m3_to_group
            refine wp_join_group (ts := [i64])
              (fun (nn_j, ()) mj => ∃ mclr_j ws2_j : List (BitVec 32),
                mclr_j.length = c.max_vars ∧ ws2_j.length = 2 * c.max_vars ∧
                nn_j.toNat ≤ cv ∧ (∀ k < nn_j.toNat, (ws2_j[k]?.getD 0#32).toNat < cv) ∧
                (FullMem c (colState s mclr_j ws2_j) ⋆ R) mj)
              (fun _ ⟨nn_j, ⟨⟩⟩ mj ⟨mclr_j, ws2_j, hml_j, hwl_j, hnn_j, hsub_j, hmj⟩ => by
                m3_steps; exact hL (end_p.toNat - (p + 1#64).toNat) (nn_j, p + 1#64, ()) mj
                  (by omega) ⟨mclr_j, ws2_j, hml_j, hwl_j, by omega, rfl, hnn_j, hsub_j, hmj⟩)
              ?_
            intro Ju hJu
            m3_split_fast
            · have hu_lt : u.toNat < cv := by
                have hlt := bv64_ult_lt hc; rw [bv_zext32_toNat] at hlt
                rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hlt
              clear hc; m3_split_fast
              · clear hc
                have hu_mc : (u.setWidth 64).toNat < mclr_l.length := by
                  rw [bv_zext32_toNat]; omega
                m3_split_fast
                · clear hc
                  have hu_fl : (u.setWidth 64).toNat < s.core.flags.length := by
                    rw [bv_zext32_toNat, hfl_len]; omega
                  m3_split_fast
                  · clear hc
                    have hu_val : (u.setWidth 64 <<< (1 : Nat)).toNat < s.core.vals.length := by
                      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm,
                        bv_zext32_toNat, Nat.mod_eq_of_lt (by omega), hv_len]; omega
                    m3_split_fast
                    · clear hc; m3_steps
                      · have hnn_lt : nn_l.toNat < cv := by
                          rwa [Nat.mod_eq_of_lt (by omega)] at hc
                        let mclr' := mclr_l.set u.toNat 1#32
                        obtain ⟨hnn1, hnn1_le, hlen_w, hsub'⟩ :=
                          col_push_inv hu_lt hnn_lt (by omega) (by omega) hsub_l
                        exact hJ _ _ (hJu (nn_l + 1#64, ()) m ⟨mclr', ws2_l.set nn_l.toNat u,
                          by rw [List.length_set]; exact hml_l,
                          by rw [hwl_l] at hlen_w; exact hlen_w, hnn1_le, hsub',
                          col_mem_cast hm rfl rfl⟩)
                      · let mclr' := mclr_l.set u.toNat 1#32
                        exact hJ _ _ (hJu (nn_l, ()) m ⟨mclr', ws2_l,
                          by rw [List.length_set]; exact hml_l, hwl_l, hnn_l, hsub_l,
                          col_mem_cast hm rfl rfl⟩)
                    · m3_let; exact hJu (nn_l, ()) ml ⟨mclr_l, ws2_l, hml_l, hwl_l, hnn_l,
                        hsub_l, hml⟩
                  · m3_let; exact hJu (nn_l, ()) ml ⟨mclr_l, ws2_l, hml_l, hwl_l, hnn_l,
                      hsub_l, hml⟩
                · m3_let; exact hJu (nn_l, ()) ml ⟨mclr_l, ws2_l, hml_l, hwl_l, hnn_l,
                    hsub_l, hml⟩
              · m3_let; exact hJu (nn_l, ()) ml ⟨mclr_l, ws2_l, hml_l, hwl_l, hnn_l, hsub_l, hml⟩
            · m3_let; exact hJu (nn_l, ()) ml ⟨mclr_l, ws2_l, hml_l, hwl_l, hnn_l, hsub_l, hml⟩
          · -- Large/occurrence clause branch
            clear hc; m3_split_fast
            · m3_steps; exact hB (nn_l, p + 1#64, ()) ml
                ⟨mclr_l, ws2_l, hml_l, hwl_l, hnn_l, hsub_l, hml⟩
            · have hp1_lt : (p + 1#64).toNat < end_p.toNat := by
                have hnot := bv64_ule_not_le hc
                change ¬ end_p.toNat ≤ (p + 1#64).toNat at hnot; omega
              have hp1_ws : (p + 1#64).toNat < s.core.wstk.length := by rw [hws_len]; omega
              have hp2 : (p + 2#64).toNat = p.toNat + 2 := by
                rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl,
                  Nat.mod_eq_of_lt (by omega)]
              let cr := s.core.wstk[(p + 1#64).toNat]'hp1_ws
              have hp_cont : L (nn_l, p + 2#64, ()) ml :=
                hL (end_p.toNat - (p + 2#64).toNat) (nn_l, p + 2#64, ()) ml
                  (by omega) ⟨mclr_l, ws2_l, hml_l, hwl_l, by omega, rfl, hnn_l, hsub_l, hml⟩
              have hp_cont' : L (nn_l, p + 1#64 + 1#64, ()) ml := by
                have heq : p + 1#64 + 1#64 = p + 2#64 := by bv_omega
                rw [heq]; exact hp_cont
              clear hc; m3_split_fast
              · m3_steps; exact hp_cont'
              · have hcr3_le : cr.toNat + 3 ≤ s.core.arena_len := by
                  have hnot := bv64_ult_not_lt hc
                  change ¬ (BitVec.ofNat 64 s.core.arena_len).toNat <
                    (cr.setWidth 64 + 3#64).toNat at hnot
                  rw [col_cr3_add_toNat (by omega), BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega)] at hnot
                  omega
                have hcr_ar : cr.toNat < s.core.arena.length := by rw [har_len]; omega
                have hcr2_ar : (cr.setWidth 64 + 2#64).toNat < s.core.arena.length := by
                  rw [BitVec.toNat_add, bv_zext32_toNat, show (2#64 : BitVec 64).toNat = 2 from rfl,
                    Nat.mod_eq_of_lt (by omega), har_len]
                  omega
                let hdr :=
                  s.core.arena[(cr.setWidth 64).toNat]'(by rw [bv_zext32_toNat]; exact hcr_ar)
                let sz_c := s.core.arena[(cr.setWidth 64 + 2#64).toNat]'hcr2_ar
                clear hc; m3_split_fast
                · m3_steps; exact hp_cont'
                · clear hc; m3_split_fast
                  · m3_steps; exact hp_cont'
                  · have hcr3sz_le : cr.toNat + 3 + sz_c.toNat ≤ s.core.arena_len := by
                      have hnot := bv64_ult_not_lt hc
                      have hadd : (cr.setWidth 64 + 3#64 + sz_c.setWidth 64).toNat =
                          cr.toNat + 3 + sz_c.toNat := by
                        rw [BitVec.toNat_add, col_cr3_add_toNat (by omega), bv_zext32_toNat,
                          Nat.mod_eq_of_lt (by omega)]
                      change ¬ (BitVec.ofNat 64 s.core.arena_len).toNat <
                        (cr.setWidth 64 + 3#64 + sz_c.setWidth 64).toNat at hnot
                      rw [hadd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnot
                      omega
                    clear hc; m3_steps
                    refine wp_loop_inv
                      (fun (nn_i, i, ()) mi => ∃ mclr_i ws2_i : List (BitVec 32),
                        mclr_i.length = c.max_vars ∧ ws2_i.length = 2 * c.max_vars ∧
                        i.toNat ≤ sz_c.toNat ∧ nn_i.toNat ≤ cv ∧
                        (∀ k < nn_i.toNat, (ws2_i[k]?.getD 0#32).toNat < cv) ∧
                        (FullMem c (colState s mclr_i ws2_i) ⋆ R) mi)
                      (fun (_, i, ()) _ => sz_c.toNat - i.toNat)
                      (fun Ji hJi => by
                        m3_steps; exact hJi (nn_l, 0#32, ()) ml ⟨mclr_l, ws2_l, hml_l, hwl_l,
                          Nat.zero_le _, hnn_l, hsub_l, hml⟩)
                      (fun Ji (nn_i, i, ()) mi ⟨mclr_i, ws2_i, hml_i, hwl_i, hi_le, hnn_i,
                          hsub_i, hmi⟩ ihi => ?_)
                    m3_split_fast
                    · have hi_lt : i.toNat < sz_c.toNat := by
                        have hlt := bv32_ult_lt hc; change i.toNat < sz_c.toNat at hlt; exact hlt
                      have hi1 : (i + 1#32).toNat = i.toNat + 1 :=
                        bv32_add1_toNat (n := sz_c.toNat) hi_lt (by omega)
                      have hcri_ar : (cr.setWidth 64 + 3#64 + i.setWidth 64).toNat <
                          s.core.arena.length := by
                        rw [col_cr3i_toNat (al := s.core.arena_len) (by omega) (by omega), har_len]
                        omega
                      let u := (s.core.arena[(cr.setWidth 64 + 3#64 + i.setWidth 64).toNat]'
                        hcri_ar) >>> 1#32
                      clear hc; m3_to_group
                      refine wp_join_group (ts := [i64])
                        (fun (nn_j, ()) mj => ∃ mclr_j ws2_j : List (BitVec 32),
                          mclr_j.length = c.max_vars ∧ ws2_j.length = 2 * c.max_vars ∧
                          nn_j.toNat ≤ cv ∧
                          (∀ k < nn_j.toNat, (ws2_j[k]?.getD 0#32).toNat < cv) ∧
                          (FullMem c (colState s mclr_j ws2_j) ⋆ R) mj)
                        (fun _ ⟨nn_j, ⟨⟩⟩ mj ⟨mclr_j, ws2_j, hml_j, hwl_j, hnn_j, hsub_j, hmj⟩ => by
                          m3_steps; exact ihi (nn_j, i + 1#32, ()) mj (by dsimp only; omega)
                            ⟨mclr_j, ws2_j, hml_j, hwl_j, by omega, hnn_j, hsub_j, hmj⟩)
                        ?_
                      intro Ju hJu; m3_split_fast
                      · have hu_lt : u.toNat < cv := by
                          have hlt := bv64_ult_lt hc; rw [bv_zext32_toNat] at hlt
                          rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hlt
                        clear hc; m3_split_fast
                        · clear hc
                          have hu_mc : (u.setWidth 64).toNat < mclr_i.length := by
                            rw [bv_zext32_toNat]; omega
                          m3_split_fast
                          · clear hc
                            have hu_fl : (u.setWidth 64).toNat < s.core.flags.length := by
                              rw [bv_zext32_toNat, hfl_len]; omega
                            m3_split_fast
                            · clear hc
                              have hu_val :
                                  (u.setWidth 64 <<< (1 : Nat)).toNat < s.core.vals.length := by
                                rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm,
                                  bv_zext32_toNat, Nat.mod_eq_of_lt (by omega), hv_len]; omega
                              m3_split_fast
                              · clear hc; m3_steps
                                · have hnn_lt : nn_i.toNat < cv := by
                                    rwa [Nat.mod_eq_of_lt (by omega)] at hc
                                  let mclr' := mclr_i.set u.toNat 1#32
                                  obtain ⟨_, hnn1_le, hlen_w, hsub'⟩ :=
                                    col_push_inv hu_lt hnn_lt (by omega) (by omega) hsub_i
                                  exact hJ _ _ (hJu (nn_i + 1#64, ()) m
                                    ⟨mclr', ws2_i.set nn_i.toNat u,
                                     by rw [List.length_set]; exact hml_i,
                                     by rw [hwl_i] at hlen_w; exact hlen_w, hnn1_le, hsub',
                                     col_mem_cast hm rfl rfl⟩)
                                · let mclr' := mclr_i.set u.toNat 1#32
                                  exact hJ _ _ (hJu (nn_i, ()) m ⟨mclr', ws2_i,
                                    by rw [List.length_set]; exact hml_i, hwl_i, hnn_i, hsub_i,
                                    col_mem_cast hm rfl rfl⟩)
                              · m3_let; exact hJu (nn_i, ()) mi ⟨mclr_i, ws2_i, hml_i, hwl_i,
                                  hnn_i, hsub_i, hmi⟩
                            · m3_let; exact hJu (nn_i, ()) mi ⟨mclr_i, ws2_i, hml_i, hwl_i,
                                hnn_i, hsub_i, hmi⟩
                          · m3_let; exact hJu (nn_i, ()) mi ⟨mclr_i, ws2_i, hml_i, hwl_i, hnn_i,
                              hsub_i, hmi⟩
                        · m3_let; exact hJu (nn_i, ()) mi ⟨mclr_i, ws2_i, hml_i, hwl_i, hnn_i,
                            hsub_i, hmi⟩
                      · m3_let; exact hJu (nn_i, ()) mi ⟨mclr_i, ws2_i, hml_i, hwl_i, hnn_i,
                          hsub_i, hmi⟩
                    · clear hc; m3_steps
                      have hp_cont_i : L (nn_i, p + 1#64 + 1#64, ()) mi := by
                        have heq : p + 1#64 + 1#64 = p + 2#64 := by bv_omega
                        rw [heq]
                        exact hL (end_p.toNat - (p + 2#64).toNat) (nn_i, p + 2#64, ()) mi
                          (by omega) ⟨mclr_i, ws2_i, hml_i, hwl_i, by omega, rfl, hnn_i,
                            hsub_i, hmi⟩
                      exact hp_cont_i
        · clear hc; m3_steps
          exact hB (nn_l, p, ()) ml ⟨mclr_l, ws2_l, hml_l, hwl_l, hnn_l, hsub_l, hml⟩
      · intro _ Lp _ hLp; m3_steps
        exact hLp (end_p.toNat - off.toNat) (nn, off, ()) mpol
          ⟨mclr, ws2, hml, hwl, by
            dsimp only [end_p, off]
            rw [BitVec.toNat_add, bv_zext32_toNat, bv_zext32_toNat, hoff_eq, hsz_eq,
              Nat.mod_eq_of_lt (by omega)]
            omega, rfl, hnn_le, hsub, hmpol⟩
    · clear hc; m3_steps
      refine wp_loop_inv
        (fun (k, ()) mk => ∃ mclr_k : List (BitVec 32),
          mclr_k.length = c.max_vars ∧ k.toNat ≤ nn.toNat ∧
          (FullMem c (colState s mclr_k ws2) ⋆ R) mk)
        (fun (k, ()) _ => nn.toNat - k.toNat)
        (fun Jk hJk => by m3_steps; exact hJk (0#64, ()) mpol ⟨mclr, hml, Nat.zero_le _, hmpol⟩)
        (fun Jk (k, ()) mk ⟨mclr_k, hml_k, hk_le, hmk⟩ ihk => ?_)
      m3_split_fast
      · have hk_lt : k.toNat < nn.toNat := bv64_ult_lt hc
        have hk_ws : k.toNat < ws2.length := by omega
        have hk1 : (k + 1#64).toNat = k.toNat + 1 :=
          bv64_add1_toNat (n := nn.toNat) hk_lt (by omega)
        have hu_lt : (ws2[k.toNat]'hk_ws).toNat < cv := by
          have := hsub k.toNat hk_lt
          rwa [List.getElem?_eq_getElem hk_ws, Option.getD_some] at this
        have hu_mc : ((ws2[k.toNat]'hk_ws).setWidth 64).toNat < mclr_k.length := by
          rw [bv_zext32_toNat]; omega
        clear hc; m3_steps
        exact ihk (k + 1#64, ()) m (by dsimp only; omega)
          ⟨mclr_k.set (ws2[k.toNat]'hk_ws).toNat 0#32, by simp [hml_k], by omega, hm⟩
      · clear hc; m3_steps
        exact hQ nn mclr_k ws2 mk (colState_lens hlen0 hml_k hwl) hnn_le hsub hmk

end CollectNbrsProof

/-! ## 3. `#8` `m3_elim_bve_wp` Helpers & Proof -/

section ElimBveProof

open scoped FullArenaTactics FullCongTactics M3HeadTactics

private theorem bve_tmkZero_with_mclr_ws2 {s : FullState} (htmk : TmkZero s)
    (mclr' ws2' : List (BitVec 32)) : TmkZero (colState s mclr' ws2') :=
  htmk.congr rfl rfl

private theorem bve_tmkZero_with_flags {s : FullState} (htmk : TmkZero s)
    (fl' : List (BitVec 32)) : TmkZero { s with core := { s.core with flags := fl' } } :=
  htmk.congr rfl rfl

/-- **#8 (`full_elim_bve`)**: 16-pass `FL_ELIM_C` neighbor-rearming BVE loop preserving
`FullDenseInv`, `TmkZero`, and `fuel ≤`. -/
theorem m3_elim_bve_wp (Γ : Env)
    (hCollect : ∀ a m Q X, m3ElimCollectNbrsSpec a m Q X →
      Γ "full_elim_collect_nbrs" [i64, i32] [i64] a m Q X)
    (hBveVar : ∀ a m Q X, fullBveVarDefSpec a m Q X →
      Γ "full_bve_var" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, m3ElimBveSpec a m Q X → Func.wp Γ full_elim_bve_body a m Q X := by
  rintro ⟨h, bve_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hden0, htmk0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  let cv := s.core.cur_vars
  have hcv_le : cv ≤ c.max_vars := hden0.lengths.core_ok.cur_vars_le
  unfold Func.wp full_elim_bve_body
  m3_steps
  refine wp_loop_inv
    (fun (ci, ()) mc => ∃ mclr : List (BitVec 32),
      mclr.length = c.max_vars ∧ ci.toNat ≤ cv ∧
      (FullMem c { s with core := { s.core with min_clr := mclr } } ⋆ R) mc)
    (fun (ci, ()) _ => cv - ci.toNat)
    (fun Jc hJc => by
      m3_steps; exact hJc (0#64, ()) m0 ⟨s.core.min_clr, hden0.lengths.core_ok.min_clr_len_arr,
        Nat.zero_le _, hm0⟩)
    (fun Jc (ci, ()) mc ⟨mclr, hml, hci_le, hmc⟩ ihc => ?_)
  m3_split_fast
  · have hci_lt : ci.toNat < cv := by
      have hlt := bv64_ult_lt hc
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hlt
    have hci_arr : ci.toNat < mclr.length := by omega
    have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := bv64_add1_toNat (n := cv) hci_lt (by omega)
    clear hc; m3_steps
    exact ihc (ci + 1#64, ()) m (by dsimp only; omega)
      ⟨mclr.set ci.toNat 0#32, by simp [hml], by omega, hm⟩
  · clear hc
    let s1 : FullState := { s with core := { s.core with min_clr := mclr } }
    have hden1 : FullDenseInv c F0 s1 :=
      fullDenseInv_with_min_clr_work_stk2 hden0 hml hden0.lengths.scratch_ok.work_stk2_len
    have htmk1 : TmkZero s1 := htmk0.congr rfl rfl
    m3_to_group
    refine wp_loop_break_group
      (fun (_, _, res, ()) mb => ∃ sb : FullState,
        FullDenseInv c F0 sb ∧ TmkZero sb ∧ sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (res = 1#64 ∨ res = 2#64 ∨ res = 20#64) ∧ (res = 20#64 → F0.Unsat) ∧
        (FullMem c sb ⋆ R) mb)
      (fun rem (pass, tried, res, ()) ml => ∃ sp : FullState,
        pass.toNat ≤ 16 ∧ rem = 16 - pass.toNat ∧
        FullDenseInv c F0 sp ∧ TmkZero sp ∧ cv ≤ sp.core.cur_vars ∧
        sp.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (res = 1#64 ∨ res = 2#64 ∨ res = 20#64) ∧ (res = 20#64 → F0.Unsat) ∧
        (FullMem c sp ⋆ R) ml)
      ?_ ?_ ?_
    · rintro _ ⟨_, _, res_b, ⟨⟩⟩ mb ⟨sb, hdenb, htmkb, hfub, _, h20b, hmb⟩
      m3_steps
      · exact hJ _ _ (hQ 20#64 sb mb hdenb htmkb hfub (Or.inr rfl) (fun _ => h20b hc) hmb)
      · exact hJ _ _ (hQ 1#64 sb mb hdenb htmkb hfub (Or.inl rfl) (fun h => by cases h) hmb)
    · rintro B L rem ⟨pass, tried, res, ⟨⟩⟩ ml hB hL
        ⟨sp, hpass_le, rfl, hdenp, htmkp, hcv_p, hfup, hres_dom, h20p, hml⟩
      have hbrk_p : B (pass, tried, res, ()) ml :=
        hB (pass, tried, res, ()) ml ⟨sp, hdenp, htmkp, hfup, hres_dom, h20p, hml⟩
      m3_split_fast
      · have hpass_lt : pass.toNat < 16 := bv64_ult_lt hc
        have hpass1 : (pass + 1#64).toNat = pass.toNat + 1 :=
          bv64_add1_toNat (n := 16) hpass_lt (by decide)
        clear hc; m3_split_fast
        · clear hc; m3_split_fast
          · clear hc; m3_split_fast
            · clear hc; m3_split_fast
              · have hres_eq1 : res = 1#64 := beq_iff_eq.mp hc
                clear hc; m3_to_group
                refine wp_loop_break_group
                  (fun (tried_b, res_b, rearmed, _v_b, ()) mb => ∃ sb : FullState,
                    FullDenseInv c F0 sb ∧ TmkZero sb ∧ cv ≤ sb.core.cur_vars ∧
                    sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                    (res_b = 1#64 ∨ res_b = 2#64 ∨ res_b = 20#64) ∧ (res_b = 20#64 → F0.Unsat) ∧
                    (FullMem c sb ⋆ R) mb)
                  (fun rem_v (tried_l, rearmed, v, ()) mv => ∃ sv : FullState,
                    v.toNat ≤ cv ∧ rem_v = cv - v.toNat ∧
                    FullDenseInv c F0 sv ∧ TmkZero sv ∧ cv ≤ sv.core.cur_vars ∧
                    sv.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                    (FullMem c sv ⋆ R) mv)
                  ?_ ?_ ?_
                · rintro _ ⟨tried_b, res_b, rearmed, _v_b, ⟨⟩⟩ mb
                    ⟨sb, hdenb, htmkb, hcv_b, hfub, hresb, h20b, hmb⟩
                  m3_split_fast
                  · clear hc; m3_split_fast
                    · m3_steps; exact hB (pass, tried_b, res_b, ()) mb
                        ⟨sb, hdenb, htmkb, hfub, hresb, h20b, hmb⟩
                    · m3_steps
                      exact hL (16 - (pass + 1#64).toNat) (pass + 1#64, tried_b, res_b, ()) mb
                        (by omega) ⟨sb, by omega, rfl, hdenb, htmkb, hcv_b, hfub, hresb, h20b, hmb⟩
                  · m3_steps; exact hB (pass, tried_b, res_b, ()) mb
                      ⟨sb, hdenb, htmkb, hfub, hresb, h20b, hmb⟩
                · rintro Bv Lv rem_v ⟨tried_l, rearmed, v, ⟨⟩⟩ mv hBv hLv
                    ⟨sv, hv_le, rfl, hdenv, htmkv, hcv_v, hfuv, hmv⟩
                  have hcvv_le := hdenv.lengths.core_ok.cur_vars_le
                  have hbrk_v : Bv (tried_l, res, rearmed, v, ()) mv :=
                    hBv (tried_l, res, rearmed, v, ()) mv
                      ⟨sv, hdenv, htmkv, hcv_v, hfuv, Or.inl hres_eq1,
                       (fun h => by rw [hres_eq1] at h; cases h), hmv⟩
                  m3_split_fast
                  · have hv_lt : v.toNat < cv := by
                      have hlt := bv64_ult_lt hc
                      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hlt
                    have hv1 : (v + 1#64).toNat = v.toNat + 1 :=
                      bv64_add1_toNat (n := cv) hv_lt (by omega)
                    clear hc; m3_split_fast
                    · clear hc; m3_split_fast
                      · clear hc; m3_split_fast
                        · have hv_fl : v.toNat < sv.core.flags.length := by
                            rw [hdenv.lengths.core_ok.flags_len]; omega
                          have hv_shl : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
                            rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm,
                              Nat.mod_eq_of_lt (by omega)]
                          have hv_vals : (v <<< (1 : Nat)).toNat < sv.core.vals.length := by
                            rw [hv_shl, hdenv.lengths.core_ok.vals_len]; omega
                          clear hc; m3_to_group
                          refine wp_join_group (ts := [i64, i64, .bool])
                            (fun (tried', _, rearmed', ()) mj => ∃ sj : FullState,
                              FullDenseInv c F0 sj ∧ TmkZero sj ∧ cv ≤ sj.core.cur_vars ∧
                              sj.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sj ⋆ R) mj)
                            (fun _ ⟨tried', _, rearmed', ⟨⟩⟩ mj
                                ⟨sj, hdenj, htmkj, hcv_j, hfuj, hmj⟩ => by
                              m3_steps
                              exact hLv (cv - (v + 1#64).toNat)
                                (tried', rearmed', v + 1#64, ()) mj (by omega)
                                ⟨sj, by omega, rfl, hdenj, htmkj, hcv_j, hfuj, hmj⟩)
                            ?_
                          intro Jstep hJstep
                          have hkeep_v : Jstep (tried_l, res, rearmed, ()) mv :=
                            hJstep (tried_l, res, rearmed, ()) mv
                              ⟨sv, hdenv, htmkv, hcv_v, hfuv, hmv⟩
                          m3_split_fast
                          · clear hc; m3_split_fast
                            · clear hc; m3_steps
                              let fl' := sv.core.flags.set v.toNat
                                (sv.core.flags[v.toNat] &&& ~~~16#32)
                              let st1 : FullState :=
                                { sv with core := { sv.core with flags := fl' } }
                              have hden1 : FullDenseInv c F0 st1 :=
                                fullDenseInv_with_flags hdenv
                                  (by simp [fl', hdenv.lengths.core_ok.flags_len])
                              have htmk1 : TmkZero st1 := bve_tmkZero_with_flags htmkv fl'
                              have hm1 : (FullMem c st1 ⋆ R) m := by
                                simpa only [st1, fl', BitVec.and_comm,
                                  show (16 : BitVec 32) = 16#32 from rfl] using hm
                              have hv32 : (v.setWidth 32).toNat < st1.core.cur_vars := by
                                change (v.setWidth 32).toNat < sv.core.cur_vars
                                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; omega
                              m3_call hCollect
                              refine ⟨c, F0, st1, R, rfl, hden1, htmk1, hm1,
                                fun nn mclr2 ws2 m2 hlen2 hnn_le hws_lt hm2 => ?_⟩
                              let st2 : FullState := colState st1 mclr2 ws2
                              have hden2 : FullDenseInv c F0 st2 :=
                                fullDenseInv_with_min_clr_work_stk2 hden1
                                  hlen2.core_ok.min_clr_len_arr hlen2.scratch_ok.work_stk2_len
                              have htmk2 : TmkZero st2 :=
                                bve_tmkZero_with_mclr_ws2 htmk1 mclr2 ws2
                              m3_steps; m3_call hBveVar
                              refine ⟨c, F0, st2, R, rfl, hden2, htmk2, hv32, hm2,
                                fun br s3 m3 hden3 htmk3 hcv3 hfu3 hbr_dom hbr20 hm3 => ?_⟩
                              have hcv_3 : cv ≤ s3.core.cur_vars := Nat.le_trans hcv_v hcv3
                              have hfu_3 : s3.core.fuel.toNat ≤ s.core.fuel.toNat :=
                                Nat.le_trans hfu3 hfuv
                              m3_split_fast
                              · m3_steps
                                exact hBv (tried_l + 1#64, 20#64, rearmed, v, ()) m3
                                  ⟨s3, hden3, htmk3, hcv_3, hfu_3, Or.inr (Or.inr rfl),
                                   (fun _ => hbr20 (beq_iff_eq.mp hc)), hm3⟩
                              · clear hc; m3_to_group
                                refine wp_join_group (ts := [.bool])
                                  (fun (rearmed', ()) mj => ∃ sj : FullState,
                                    FullDenseInv c F0 sj ∧ TmkZero sj ∧ cv ≤ sj.core.cur_vars ∧
                                    sj.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                    (FullMem c sj ⋆ R) mj)
                                  (fun _ ⟨rearmed', ⟨⟩⟩ mj
                                      ⟨sj, hdenj, htmkj, hcv_j, hfuj, hmj⟩ => by
                                    m3_split_fast
                                    · m3_steps
                                      exact hBv (tried_l + 1#64, 2#64, rearmed', v, ()) mj
                                        ⟨sj, hdenj, htmkj, hcv_j, hfuj, Or.inr (Or.inl rfl),
                                         (fun h => by cases h), hmj⟩
                                    · m3_let
                                      exact hJstep (tried_l + 1#64, res, rearmed', ()) mj
                                        ⟨sj, hdenj, htmkj, hcv_j, hfuj, hmj⟩)
                                  ?_
                                intro Jre hJre
                                have hv_fl3 : v.toNat < s3.core.flags.length := by
                                  rw [hden3.lengths.core_ok.flags_len]
                                  have := hden3.lengths.core_ok.cur_vars_le; omega
                                have hnn_ws3 : nn.toNat ≤ s3.scratch.work_stk2.length := by
                                  rw [hden3.lengths.scratch_ok.work_stk2_len]
                                  have := hden3.lengths.core_ok.cur_vars_le
                                  change nn.toNat ≤ sv.core.cur_vars at hnn_le; omega
                                have hre_skip : Jre (rearmed, ()) m3 :=
                                  hJre (rearmed, ()) m3 ⟨s3, hden3, htmk3, hcv_3, hfu_3, hm3⟩
                                m3_to_group
                                refine wp_join_group (ts := []) (fun () mr => mr = m3)
                                  (fun _ ⟨⟩ mr hmr => by
                                    rw [hmr]
                                    m3_steps
                                    refine wp_loop_inv
                                      (fun (re_k, k, ()) mk => ∃ sk : FullState,
                                        FullDenseInv c F0 sk ∧ TmkZero sk ∧
                                        sk.core.cur_vars = s3.core.cur_vars ∧
                                        sk.core.fuel = s3.core.fuel ∧
                                        sk.scratch.work_stk2 = s3.scratch.work_stk2 ∧
                                        k.toNat ≤ nn.toNat ∧ (FullMem c sk ⋆ R) mk)
                                      (fun (_, k, ()) _ => nn.toNat - k.toNat)
                                      (fun Jk hJk => by
                                        m3_steps
                                        exact hJk (rearmed, 0#64, ()) m3
                                          ⟨s3, hden3, htmk3, rfl, rfl, rfl, Nat.zero_le _, hm3⟩)
                                      (fun Jk (re_k, k, ()) mk
                                          ⟨sk, hdenk, htmkk, hcvk, hfuk, hws2k, hk_le, hmk⟩
                                          ihk => ?_)
                                    m3_split_fast
                                    · have hk_lt : k.toNat < nn.toNat := bv64_ult_lt hc
                                      have hk_ws : k.toNat < sk.scratch.work_stk2.length := by
                                        rw [hws2k]; omega
                                      have hk1 : (k + 1#64).toNat = k.toNat + 1 :=
                                        bv64_add1_toNat (n := nn.toNat) hk_lt (by omega)
                                      let u := sk.scratch.work_stk2[k.toNat]'hk_ws
                                      have hcvk_le := hdenk.lengths.core_ok.cur_vars_le
                                      clear hc; m3_to_group
                                      refine wp_join_group (ts := [.bool])
                                        (fun (re_next, ()) mn => ∃ sn : FullState,
                                          FullDenseInv c F0 sn ∧ TmkZero sn ∧
                                          sn.core.cur_vars = s3.core.cur_vars ∧
                                          sn.core.fuel = s3.core.fuel ∧
                                          sn.scratch.work_stk2 = s3.scratch.work_stk2 ∧
                                          (FullMem c sn ⋆ R) mn)
                                        (fun _ ⟨re_next, ⟨⟩⟩ mn
                                            ⟨sn, hdenn, htmkn, hcvn, hfun, hws2n, hmn⟩ => by
                                          m3_steps
                                          exact ihk (re_next, k + 1#64, ()) mn
                                            (by dsimp only; omega)
                                            ⟨sn, hdenn, htmkn, hcvn, hfun, hws2n, by omega, hmn⟩)
                                        ?_
                                      intro Jk1 hJk1
                                      have hk_skip : Jk1 (re_k, ()) mk :=
                                        hJk1 (re_k, ()) mk
                                          ⟨sk, hdenk, htmkk, hcvk, hfuk, hws2k, hmk⟩
                                      m3_split_fast
                                      · have hu_lt : u.toNat < sk.core.cur_vars := by
                                          have hlt := bv64_ult_lt hc
                                          rw [hcvk]
                                          dsimp only [u] at hlt ⊢
                                          rw [bv_zext32_toNat, BitVec.toNat_ofNat,
                                            Nat.mod_eq_of_lt (by rw [← hcvk]; omega)] at hlt
                                          exact hlt
                                        have hu_fl :
                                            (u.setWidth 64).toNat < sk.core.flags.length := by
                                          rw [bv_zext32_toNat, hdenk.lengths.core_ok.flags_len]
                                          omega
                                        have hu_shl :
                                            (u.setWidth 64 <<< (1 : Nat)).toNat =
                                              2 * u.toNat := by
                                          rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
                                            Nat.mul_comm, bv_zext32_toNat,
                                            Nat.mod_eq_of_lt (by omega)]
                                        have hu_vals :
                                            (u.setWidth 64 <<< (1 : Nat)).toNat <
                                              sk.core.vals.length := by
                                          rw [hu_shl, hdenk.lengths.core_ok.vals_len]; omega
                                        clear hc; m3_split_fast
                                        · clear hc; m3_split_fast
                                          · clear hc; m3_to_group
                                            refine wp_join_group (ts := [.bool])
                                              (fun (re_u, ()) mu => mu = mk)
                                              (fun _ ⟨re_u, ⟨⟩⟩ mu hmu => by
                                                subst hmu
                                                m3_steps
                                                let fl' := sk.core.flags.set (u.setWidth 64).toNat
                                                  (sk.core.flags[(u.setWidth 64).toNat]'hu_fl |||
                                                    16#32)
                                                let sn : FullState :=
                                                  { sk with core := { sk.core with flags := fl' } }
                                                have hdenn : FullDenseInv c F0 sn :=
                                                  fullDenseInv_with_flags hdenk
                                                    (by simp [fl', hdenk.lengths.core_ok.flags_len])
                                                have htmkn : TmkZero sn :=
                                                  bve_tmkZero_with_flags htmkk fl'
                                                exact hJk1 (re_u, ()) m
                                                  ⟨sn, hdenn, htmkn, hcvk, hfuk, hws2k, hm⟩)
                                              (fun Ju hJu => by
                                                m3_split_fast
                                                · m3_let; exact hJu (true, ()) mk rfl
                                                · m3_let; exact hJu (re_k, ()) mk rfl)
                                          · m3_let; exact hk_skip
                                        · m3_let; exact hk_skip
                                      · m3_let; exact hk_skip
                                    · m3_steps
                                      exact hJre (re_k, ()) mk ⟨sk, hdenk, htmkk,
                                        by rw [hcvk]; exact hcv_3,
                                        by rw [hfuk]; exact hfu_3, hmk⟩)
                                  (fun Jbr hJbr => by
                                    m3_split_fast
                                    · m3_let; exact hJbr () m3 rfl
                                    · clear hc; m3_split_fast
                                      · m3_let; exact hJbr () m3 rfl
                                      · m3_let; exact hre_skip)
                            · m3_let; exact hkeep_v
                          · m3_let; exact hkeep_v
                        · clear hc; m3_steps; exact hbrk_v
                      · clear hc; m3_steps; exact hbrk_v
                    · clear hc; m3_steps; exact hbrk_v
                  · clear hc; m3_steps; exact hbrk_v
                · intro _ Lv _ hLv; m3_steps
                  exact hLv cv (tried, false, 0#64, ()) ml
                    ⟨sp, Nat.zero_le _, rfl, hdenp, htmkp, hcv_p, hfup, hml⟩
              · clear hc; m3_steps; exact hbrk_p
            · clear hc; m3_steps; exact hbrk_p
          · clear hc; m3_steps; exact hbrk_p
        · clear hc; m3_steps; exact hbrk_p
      · clear hc; m3_steps; exact hbrk_p
    · intro _ Lp _ hLp; m3_steps
      exact hLp 16 (0#64, 0#64, 1#64, ()) mc
        ⟨s1, Nat.zero_le _, rfl, hden1, htmk1, Nat.le_refl _, Nat.le_refl _, Or.inl rfl,
         (fun h => by cases h), hmc⟩

end ElimBveProof

end LeanQbe.T.Examples.Kissat.FullM3CongBva

