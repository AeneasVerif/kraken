module

public import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas5

/-!
# Kissat `D-Full` Canonical `FullSpec` Bridge Proofs — Part 8b (`Analyze` / `OTFS`, `7` fns)

Bridges all `7` already-proved Analyze/OTFS functions (`FullAnalyzeLemmas{1,2,3,5}`, table indices
`[62, 63, 64, 66, 67, 68, 77]`) directly onto canonical `FullSpec2` contracts and
`SpecEntry.Impl fullEnv`:
- `62`: `full_analyze_lit`
- `63`: `full_analyze_rsn`
- `64`: `full_clear_ana`
- `66`: `full_otfs_large`
- `67`: `full_otfs_bin`
- `68`: `full_otfs_subsume`
- `77`: `full_det_new_level`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.C0Step
open Kraken.Bedrock2.Test

/-! ## Part 1: Private `FullAnalyzeSpecs` ↔ canonical `FullSpec` adapters -/

section Adapters

private theorem anaMarksCov_to_anaWorkInv {c : FullCfg} {s : FullState}
    (h : FullAnaMarksCov c s) : FullAnalyzeSpecs.AnaWorkInv c s :=
  ⟨h.1, h.2.1, h.2.2.1, fun v hv hnz =>
    let ⟨k, hk, hkv⟩ := h.2.2.2 v hv hnz
    ⟨hkv ▸ (h.2.2.1 k hk).1, k, hk, hkv⟩⟩

private theorem anaWorkInv_to_anaMarksCov {c : FullCfg} {s : FullState}
    (h : FullAnalyzeSpecs.AnaWorkInv c s) : FullAnaMarksCov c s :=
  ⟨h.1, h.2.1, h.2.2.1, fun v hv hnz => (h.2.2.2 v hv hnz).2⟩

private theorem canonCut_to_anaCut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k) :
    FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt,
    fun idx hi hcond hne =>
      hcond.elim (fun hc => h.reason_inv_cut idx hc hne)
        (fun hlt => h.reason_inv_below idx hi hlt hne),
    fun idx hi hcond hne hlg =>
      hcond.elim (fun hc => h.reason_lit_mem_cut idx hc hne hlg)
        (fun hlt => h.reason_lit_mem_below idx hi hlt hne hlg)⟩

private theorem anaCut_to_canonCut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut k)
    (hcut : cut ≤ k.trail_end) : FullWitnessCutInv c F0 F_cur cut k :=
  ⟨⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt,
    fun idx hi hlt hne => h.reason_inv idx hi (Or.inr hlt) hne,
    fun idx hi hlt hne hlg => h.reason_lit_mem idx hi (Or.inr hlt) hne hlg⟩,
    hcut,
    fun idx hc hne => h.reason_inv idx (Nat.lt_of_lt_of_le hc hcut) (Or.inl hc) hne,
    fun idx hc hne hlg => h.reason_lit_mem idx (Nat.lt_of_lt_of_le hc hcut) (Or.inl hc) hne hlg⟩

private theorem anaConflOk_to_canonCut {F_cur : List (List Nat)} {cut : Nat} {s : FullState}
    (hct : s.core.confl_type = 1#64) (h : FullAnalyzeSpecs.FullConflOk F_cur cut s) :
    FullConflictOkCut F_cur cut s := by
  unfold FullAnalyzeSpecs.FullConflOk at h
  simp only [hct, ↓reduceIte] at h
  obtain ⟨h0lt, h1lt, hf0, hf1, hc0, hc1, hent⟩ := h
  refine ⟨Or.inl ⟨hct, h0lt, h1lt, hf0, hf1, hent⟩, ?_⟩
  simp only [hct, ↓reduceIte]
  exact ⟨hc0, hc1⟩

private theorem anaWatchPush_adapter {Γ : Env}
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, FullAnalyzeSpecs.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X := by
  rintro ⟨h, lit, w0, w1, cnt, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlay, hc1, hc2, hm, hQ⟩
  refine hPush _ m Q X ⟨c, s, R, rfl, hlen, hlay, hc1, hc2, hm,
    fun ok wv ws wl wu wso m' hlen' hlay' hoth hT hF hm' => ?_⟩
  refine hQ ok wv ws wl wu wso m' hlen' hlay' hoth hT (fun hf => ?_) hm'
  obtain ⟨hpres, hwhy⟩ := hF hf
  refine ⟨hpres, ?_⟩
  rcases hwhy with hlt | hcnt | hsame | hw0
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl hcnt)
  · exact Or.inr (Or.inr (Or.inl (congrArg FullState.core hsame)))
  · exact Or.inr (Or.inr (Or.inr hw0))

end Adapters

/-! ## Part 2: Canonical `*_bridge_wp` theorems (`7` fns) -/

section Bridges

open FullAnalyzeTactics FullAnalyzeHelpers
open scoped FullArenaTactics FullAnalyzeTactics

theorem full_analyze_lit_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullAnalyzeLitSpec a m Q X → Func.wp Γ full_analyze_lit_body a m Q X := by
  rintro ⟨h, lit, skip_var, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl32, htl_cv, htc_fit, hcov, hm, hQ⟩
  have hwork := anaMarksCov_to_anaWorkInv hcov
  refine full_analyze_lit_wp Γ _ m Q X
    ⟨c, s, R, rfl, hlen, hcl32, htl_cv, htc_fit, hwork, hm,
      fun ok mrk' tmp' ws1' mcl' tc' tl' ant' res' m' hlen' hwork' htl_le htl_ge htl_inc htc_ge
        hmpres htpres hnewm hnewt hant_eq hres_eq htc_eq hok hm' => ?_⟩
  refine hQ ok mrk' tmp' tc' tl' mcl' ws1' ant' res' m' hlen' (anaWorkInv_to_anaMarksCov hwork')
    htl_ge htl_inc htl_le htc_ge hant_eq hres_eq htc_eq ?_ htpres ?_ hnewt hok hm'
  · intro v hv hnz
    exact hmpres v (hwork.2.2.2 v hv hnz).1 hnz
  · intro v hv h0 hnz
    have hv_lt : v < s.core.cur_vars := (hwork'.2.2.2 v hv hnz).1
    obtain ⟨heq, hne, hpos, hle⟩ := hnewm v hv_lt h0 hnz
    exact ⟨heq, hv_lt, hne, hpos, hle⟩

theorem full_clear_ana_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullClearAnaSpec a m Q X → Func.wp Γ full_clear_ana_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm0, hQ⟩
  have hmax32 := fullInv_max_vars_lt32 c; have hcv_le := hlen.core_ok.cur_vars_le
  have hm_len := hlen.core_ok.mrk_len; have hmcl_le := hlen.core_ok.min_clr_len_le
  have hws_len := hlen.scratch_ok.work_stk1_len
  let LoopInv : Nat → List (BitVec 8) → Prop := fun i mrk' =>
    i ≤ s.core.min_clr_len ∧ mrk'.length = c.max_vars ∧
    (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 = 0#8) ∧
    (∀ k < i, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars →
      mrk'[(s.scratch.work_stk1[k]?.getD 0#32).toNat]?.getD 0#8 = 0#8)
  fa_steps
  refine wp_loop_group (fun r (iv, ()) ml => ∃ i mrk',
    r = s.core.min_clr_len - i ∧ iv = BitVec.ofNat 64 i ∧ LoopInv i mrk' ∧
    (FullMem c { s with core := { s.core with mrk := mrk' } } ⋆ R) ml) ?_ ?_
  · clear hm0; rintro L r ⟨iv, ⟨⟩⟩ ml ih ⟨i, mrk', rfl, rfl, ⟨hile, hml_l, hzero, hclr⟩, hml0⟩
    have himod : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
    have hcvmod : s.core.cur_vars % 2 ^ 64 = s.core.cur_vars := Nat.mod_eq_of_lt (by omega)
    fa_steps
    · have hilt : i < s.core.min_clr_len := by omega
      have hws_lt : i < s.scratch.work_stk1.length := by omega
      have hv_get : (s.scratch.work_stk1[i]?.getD 0#32).toNat =
          (s.scratch.work_stk1[i]'hws_lt).toNat := by
        rw [List.getElem?_eq_getElem hws_lt, Option.getD_some]
      have hidx_eq : s.scratch.work_stk1[i % 2 ^ 64]'(by rw [himod]; exact hws_lt) =
          s.scratch.work_stk1[i]'hws_lt := getElem_eq_of_idx himod
      have hv_lt : (s.scratch.work_stk1[i]'hws_lt).toNat < s.core.cur_vars := by
        have hlt_raw : (s.scratch.work_stk1[i % 2 ^ 64]'(by rw [himod]; exact hws_lt)).toNat <
            s.core.cur_vars % 2 ^ 64 := by assumption
        rw [congrArg BitVec.toNat hidx_eq, hcvmod] at hlt_raw; exact hlt_raw
      rw [show BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) from
        BitVec.eq_of_toNat_eq (by bv_omega)]
      refine ih (s.core.min_clr_len - (i + 1)) _ _ (by omega)
        ⟨i + 1, mrk'.set (s.scratch.work_stk1[i]'hws_lt).toNat 0#8, rfl, rfl,
          ⟨by omega, by simp [hml_l], fun v hv h0 => ?_, fun k hk hkv => ?_⟩, ?_⟩
      · by_cases hveq : v = (s.scratch.work_stk1[i]'hws_lt).toNat
        · rw [hveq, List.getElem?_set_self (by omega)]; rfl
        · rw [List.getElem?_set_ne (Ne.symm hveq)]; exact hzero v hv h0
      · by_cases hki : k = i
        · subst k; rw [hv_get, List.getElem?_set_self (by omega)]; rfl
        · by_cases heq : (s.scratch.work_stk1[k]?.getD 0#32).toNat =
              (s.scratch.work_stk1[i]'hws_lt).toNat
          · rw [heq, List.getElem?_set_self (by omega)]; rfl
          · rw [List.getElem?_set_ne (Ne.symm heq)]; exact hclr k (by omega) hkv
      · have hidx64 : s.scratch.work_stk1[(BitVec.ofNat 64 i).toNat]'(by
            rw [bv64_ofNat_toNat (by omega)]; exact hws_lt) = s.scratch.work_stk1[i]'hws_lt :=
          getElem_eq_of_idx (bv64_ofNat_toNat (by omega))
        have hmrk_eq : mrk'.set (BitVec.setWidth 64
            (s.scratch.work_stk1[(BitVec.ofNat 64 i).toNat]'(by
              rw [bv64_ofNat_toNat (by omega)]; exact hws_lt))).toNat 0#8 =
            mrk'.set (s.scratch.work_stk1[i]'hws_lt).toNat 0#8 := by rw [bv_c0_zext32_64, hidx64]
        rw [← hmrk_eq]; exact hm
    · have hilt : i < s.core.min_clr_len := by omega
      have hws_lt : i < s.scratch.work_stk1.length := by omega
      have hv_get : (s.scratch.work_stk1[i]?.getD 0#32).toNat =
          (s.scratch.work_stk1[i]'hws_lt).toNat := by
        rw [List.getElem?_eq_getElem hws_lt, Option.getD_some]
      have hidx_eq : s.scratch.work_stk1[i % 2 ^ 64]'(by rw [himod]; exact hws_lt) =
          s.scratch.work_stk1[i]'hws_lt := getElem_eq_of_idx himod
      have hv_ge : ¬ (s.scratch.work_stk1[i]'hws_lt).toNat < s.core.cur_vars := by
        have hge_raw : ¬ (s.scratch.work_stk1[i % 2 ^ 64]'(by rw [himod]; exact hws_lt)).toNat <
            s.core.cur_vars % 2 ^ 64 := by assumption
        rw [congrArg BitVec.toNat hidx_eq, hcvmod] at hge_raw; exact hge_raw
      rw [show BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) from
        BitVec.eq_of_toNat_eq (by bv_omega)]
      refine ih (s.core.min_clr_len - (i + 1)) _ _ (by omega)
        ⟨i + 1, mrk', rfl, rfl, ⟨by omega, hml_l, hzero, fun k hk hkv => ?_⟩, hml0⟩
      by_cases hki : k = i
      · subst k; rw [hv_get] at hkv; exact absurd hkv hv_ge
      · exact hclr k (by omega) hkv
    · have hieq : i = s.core.min_clr_len := by omega
      subst hieq; fa_steps
      refine hQ mrk' _ hml_l hzero hclr (fun hcov v hv => ?_) (by assumption)
      by_cases hz : s.core.mrk[v]?.getD 0#8 = 0#8
      · exact hzero v hv hz
      · obtain ⟨k, hk, hkv⟩ := hcov.2.2.2 v hv hz
        have hlt := (hcov.2.2.1 k hk).1
        exact hkv ▸ hclr k hk hlt
  · intro L hL; fa_steps
    refine hL s.core.min_clr_len _ m ⟨0, s.core.mrk, by omega, rfl,
      ⟨Nat.zero_le _, hm_len, fun _ _ h0 => h0, fun _ hk => by omega⟩, hm0⟩

private theorem fullMem_arena_gu_eq {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {ar1 ar2 : List (BitVec 32)} {gu : List (BitVec 32)} (h : ar1 = ar2)
    (hm : (FullMem c ⟨{ s.core with arena := ar1 }, { s.scratch with glue_used := gu }⟩ ⋆ R) m) :
    (FullMem c ⟨{ s.core with arena := ar2 }, { s.scratch with glue_used := gu }⟩ ⋆ R) m := by
  subst h; exact hm

private theorem b8_bv64_ite_iff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    (if P then (1#64 : BitVec 64) else 0#64) = BitVec.ofNat 64 (if Q then 1 else 0) := by
  by_cases hp : P
  · have hq : Q := h.mp hp; simp [hp, hq]
  · have hnq : ¬Q := mt h.mpr hp; simp [hp, hnq]

private theorem b8_res_step_of_lit {s_mrk mrk1 mrk2 : List (BitVec 8)} {mv v : Nat}
    {r0 r1 r2 : BitVec 64}
    (hmp0 : ∀ w < mv, s_mrk[w]?.getD 0#8 ≠ 0#8 → mrk1[w]?.getD 0#8 = s_mrk[w]?.getD 0#8)
    (hmp1 : ∀ w < mv, mrk1[w]?.getD 0#8 ≠ 0#8 → mrk2[w]?.getD 0#8 = mrk1[w]?.getD 0#8)
    (hnew1 : ∀ w < mv, mrk1[w]?.getD 0#8 = 0#8 → mrk2[w]?.getD 0#8 ≠ 0#8 → v = w)
    (hr1 : r1 = r0 + BitVec.ofNat 64 ((List.range mv).filter fun w =>
      decide (s_mrk[w]?.getD 0#8 = 0#8) && decide (mrk1[w]?.getD 0#8 ≠ 0#8)).length)
    (hr2 : r2 = r1 + if v < mv ∧ mrk1[v]?.getD 0#8 = 0#8 ∧ mrk2[v]?.getD 0#8 ≠ 0#8
      then 1#64 else 0#64) : r2 = r0 + BitVec.ofNat 64 ((List.range mv).filter fun w =>
      decide (s_mrk[w]?.getD 0#8 = 0#8) && decide (mrk2[w]?.getD 0#8 ≠ 0#8)).length := by
  let c1 := ((List.range mv).filter fun w =>
    decide (s_mrk[w]?.getD 0#8 = 0#8) && decide (mrk1[w]?.getD 0#8 ≠ 0#8)).length
  have hf := filter_step_of_lit (fun _ => true) (tc0 := 0) (tc1 := c1)
    (tc2 := c1 + if v < mv ∧ mrk1[v]?.getD 0#8 = 0#8 ∧ mrk2[v]?.getD 0#8 ≠ 0#8 ∧
      (true : Bool) = true then 1 else 0) hmp0 hmp1 hnew1 (Nat.zero_le _) (by simp [c1]) rfl
  simp only [Nat.sub_zero, Bool.and_true, and_true] at hf
  rw [hr2, hr1, BitVec.add_assoc]; congr 1; dsimp only [c1] at hf; rw [← hf]
  split <;> simp [BitVec.ofNat_add]

private abbrev CanonRsnPre (c : FullCfg) (s : FullState) (rsn_lits : List Nat)
    (skip_var : BitVec 32) (mrk' : List (BitVec 8)) (tmp' : List (BitVec 32))
    (tc' tl' : Nat) (res' : BitVec 64) : Prop :=
  (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
    mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8) ∧
  (∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?) ∧
  (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
    ∃ l ∈ rsn_lits, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
      0 < (s.core.lvl[v]?.getD 0#32).toNat ∧ (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level) ∧
  (∀ j, s.core.tmp_len ≤ j → j < tl' → let l := (tmp'[j]?.getD 0#32).toNat
    l ∈ rsn_lits ∧ l < 2 * s.core.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
    s.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
    (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧ mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
  (∀ j1 j2, s.core.tmp_len ≤ j1 → j1 < j2 → j2 < tl' →
    (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2) ∧
  (tc' - s.core.tmp_cnt = ((List.range s.core.cur_vars).filter fun w =>
    decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
    decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level)).length) ∧
  (res' = s.scratch.res_sz + BitVec.ofNat 64 ((List.range s.core.cur_vars).filter fun w =>
    decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length)

private theorem canon_rsn_step {c : FullCfg} {s : FullState} {l_bv skip_var : BitVec 32}
    {rsn_lits : List Nat} {mrk' mrk2 : List (BitVec 8)} {tmp' tmp2 : List (BitVec 32)}
    {tc' tl' tc2 tl2 : Nat} {res' res2 : BitVec 64}
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (htl_ge : s.core.tmp_len ≤ tl')
    (htl2_ge : tl' ≤ tl2) (htl2_inc : tl2 ≤ tl' + 1)
    (htc_ge : s.core.tmp_cnt ≤ tc') (hl_mem : l_bv.toNat ∈ rsn_lits)
    (hpre : CanonRsnPre c s rsn_lits skip_var mrk' tmp' tc' tl' res')
    (hmp2 : ∀ v < c.max_vars, mrk'[v]?.getD 0#8 ≠ 0#8 →
      mrk2[v]?.getD 0#8 = mrk'[v]?.getD 0#8) (htp2 : ∀ k < tl', tmp2[k]? = tmp'[k]?)
    (hnm2 : ∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8 → mrk2[v]?.getD 0#8 ≠ 0#8 →
      l_bv.toNat / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
      0 < (s.core.lvl[v]?.getD 0#32).toNat ∧ (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level)
    (hnt2 : ∀ j, tl' ≤ j → j < tl2 → (tmp2[j]?.getD 0#32).toNat = l_bv.toNat ∧
      l_bv.toNat / 2 < s.core.cur_vars ∧ l_bv.toNat / 2 ≠ skip_var.toNat ∧
      mrk'[l_bv.toNat / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.core.lvl[l_bv.toNat / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[l_bv.toNat / 2]?.getD 0#32).toNat < s.core.cur_level ∧
      mrk2[l_bv.toNat / 2]?.getD 0#8 ≠ 0#8)
    (hres2 : res2 = res' + if l_bv.toNat / 2 < s.core.cur_vars ∧
      mrk'[l_bv.toNat / 2]?.getD 0#8 = 0#8 ∧ mrk2[l_bv.toNat / 2]?.getD 0#8 ≠ 0#8
      then 1#64 else 0#64)
    (htc2_eq : tc2 = tc' + if l_bv.toNat / 2 < s.core.cur_vars ∧
      mrk'[l_bv.toNat / 2]?.getD 0#8 = 0#8 ∧ mrk2[l_bv.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
      (s.core.lvl[l_bv.toNat / 2]?.getD 0#32).toNat = s.core.cur_level then 1 else 0) :
    CanonRsnPre c s rsn_lits skip_var mrk2 tmp2 tc2 tl2 res2 := by
  obtain ⟨hmp, htp, hnm, hnt, hnd, hcnt, hres_l⟩ := hpre
  refine ⟨fun v hv hnz => by have h1 := hmp v hv hnz; rw [hmp2 v hv (by rwa [h1]), h1],
    fun k hk => by rw [htp2 k (by omega), htp k hk], fun v hv hs0 hmnz => ?_,
    fun j hj1 hj2 => ?_, fun j1 j2 hj1 hj12 hj2 => ?_, ?_, ?_⟩
  · by_cases hm1 : mrk'[v]?.getD 0#8 = 0#8
    · obtain ⟨rfl, hlt, hne', hpos, hle⟩ := hnm2 v hv hm1 hmnz
      exact ⟨l_bv.toNat, hl_mem, rfl, hlt, hne', hpos, hle⟩
    · exact hnm v hv hs0 hm1
  · by_cases hjold : j < tl'
    · rw [htp2 j hjold]; obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hnt j hj1 hjold
      exact ⟨h1, h2, h3, h4, h5, h6, by rw [hmp2 _ (by omega) h7]; exact h7⟩
    · obtain ⟨heq, hlt, hne', hm1_0, hpos, hcl, _⟩ := hnt2 j (by omega) hj2
      have hs0 : s.core.mrk[l_bv.toNat / 2]?.getD 0#8 = 0#8 :=
        Classical.byContradiction fun hnz => by
          rw [hmp _ (by omega) hnz] at hm1_0; exact hnz hm1_0
      exact ⟨by rwa [heq], by omega, by omega, by rwa [heq], by rwa [heq], by rwa [heq],
        by rwa [heq]⟩
  · by_cases hj2_old : j2 < tl'
    · rw [htp2 j1 (by omega), htp2 j2 hj2_old]; exact hnd j1 j2 hj1 hj12 hj2_old
    · have hj1_old : j1 < tl' := by omega
      rw [htp2 j1 hj1_old]; have h1 := (hnt j1 hj1 hj1_old).2.2.2.2.2.2
      obtain ⟨heq, _, _, hm1_0, _⟩ := hnt2 j2 (by omega) hj2
      rw [heq]; intro heq_v; rw [← heq_v] at hm1_0; exact absurd hm1_0 h1
  · exact filter_step_of_lit
      (fun w => decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level))
      (mv := s.core.cur_vars) (tc0 := s.core.tmp_cnt) (tc1 := tc') (v := l_bv.toNat / 2)
      (fun w hw => hmp w (by omega)) (fun w hw => hmp2 w (by omega))
      (fun w hw h0 hnz => (hnm2 w (by omega) h0 hnz).1) htc_ge hcnt
      (by simpa only [decide_eq_true_eq] using htc2_eq)
  · exact b8_res_step_of_lit (mv := s.core.cur_vars) (v := l_bv.toNat / 2)
      (fun w hw => hmp w (by omega)) (fun w hw => hmp2 w (by omega))
      (fun w hw h0 hnz => (hnm2 w (by omega) h0 hnz).1) hres_l hres2

private abbrev canonRsnState (s : FullState) (mrk' : List (BitVec 8))
    (tmp' ws1' arena' gu' : List (BitVec 32)) (mcl' tc' tl' : Nat) (ant' res' : BitVec 64) :
    FullState :=
  { s with core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                                 min_clr_len := mcl', arena := arena' }
           scratch := { s.scratch with work_stk1 := ws1', glue_used := gu',
                                       ant_sz := ant', res_sz := res' } }

theorem full_analyze_rsn_bridge_wp (Γ : Env)
    (hLit : ∀ a m Q X, fullAnalyzeLitSpec a m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullAnalyzeRsnSpec a m Q X → Func.wp Γ full_analyze_rsn_body a m Q X := by
  rintro ⟨h, rsn, skip_var, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, cut, s, R, rfl, hlen, hw, hcov, htl_cv, htc_fit, hrsn_ref, hm, hQ⟩
  have hmax32 := fullInv_max_vars_lt32 c; have hcv_le := hlen.core_ok.cur_vars_le
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have hgu_len := hlen.scratch_ok.glue_used_len
  have hcur32 : s.core.cur_level < 2 ^ 32 := by
    have := hw.cur_level_le; have := hlen.core_ok.trail_end_le; omega
  have hret_false_same : Q (false, ()) m :=
    hQ false s.core.mrk s.core.tmp s.core.tmp_cnt s.core.tmp_len s.core.min_clr_len s.core.arena
      s.scratch m hlen hw hcov ⟨rfl, rfl⟩ rfl (Nat.le_refl _) htl_cv (Nat.le_refl _) rfl
      (fun _ _ => ⟨rfl, rfl, rfl⟩) (fun _ _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ h0 h => absurd h0 h) (fun _ h1 h2 => by omega) (fun _ _ _ h1 h2 => by omega)
      (by rw [Nat.sub_self, eq_comm, List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro _ _; simp)
      (by rw [List.filter_eq_nil_iff.mpr (fun _ _ => by simp)]; simp) (fun hc => by cases hc) hm
  fa_unmdata; c0_step; c0_step
  · exact hret_false_same
  · c0_step
    · have hne : rsn ≠ 0xFFFFFFFF#32 := ‹_›; have hbin : (rsn &&& 0x80000000#32) ≠ 0#32 := ‹_›
      fa_steps
      refine wp_call_of_spec _ _ (hLit (c.hdr, rsn &&& 0x7FFFFFFF#32, skip_var, ()) _ _ _
        ⟨c, s, R, rfl, hlen, hcur32, htl_cv, by omega, hcov, hm, ?_⟩)
      intro ok mrk' tmp' tc' tl' mcl' ws1' ant' res' m' _ hlen' hcov' htl_ge _ htl_le htc_ge
        hant_eq hres_eq htc_eq hmpres htpres hnewm hnewt hok hm'
      fa_steps
      have hw' : FullWitnessCutInv c F0 F_cur cut
          (canonRsnState s mrk' tmp' ws1' s.core.arena s.scratch.glue_used
            mcl' tc' tl' ant' res').core :=
        anaCut_to_canonCut (same_core_fullWitnessCut (canonCut_to_anaCut hw)
          hlen'.core_ok.mrk_len hlen'.core_ok.tmp_len_arr hlen'.core_ok.min_clr_len_le htl_le
          (tc' := tc')) hw.cut_le
      have htc_f := filter_step_of_lit
        (fun w => decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level))
        (mv := s.core.cur_vars) (tc0 := s.core.tmp_cnt) (tc1 := s.core.tmp_cnt)
        (v := (rsn &&& 0x7FFFFFFF#32).toNat / 2) (fun _ _ _ => rfl)
        (fun w hw_lt => hmpres w (by omega)) (fun w hw_lt h0 hnz => (hnewm w (by omega) h0 hnz).1)
        (Nat.le_refl _) (by rw [Nat.sub_self, List.filter_eq_nil_iff.mpr (fun _ _ => by simp)]; rfl)
        (by simpa only [decide_eq_true_eq] using htc_eq)
      have hres_f := b8_res_step_of_lit (mv := s.core.cur_vars)
        (v := (rsn &&& 0x7FFFFFFF#32).toNat / 2) (r0 := s.scratch.res_sz)
        (r1 := s.scratch.res_sz) (fun _ _ _ => rfl) (fun w hw_lt => hmpres w (by omega))
        (fun w hw_lt h0 hnz => (hnewm w (by omega) h0 hnz).1)
        (by rw [List.filter_eq_nil_iff.mpr (fun _ _ => by simp)]; simp) hres_eq
      refine hQ ok mrk' tmp' tc' tl' mcl' s.core.arena
        { s.scratch with work_stk1 := ws1', ant_sz := ant', res_sz := res' } m'
        hlen' hw' hcov' ⟨rfl, rfl⟩ rfl htl_ge htl_le htc_ge rfl (fun _ _ => ⟨rfl, rfl, rfl⟩)
        hmpres htpres ?_ ?_ (fun _ _ _ h1 h2 => by omega) htc_f hres_f ?_ hm'
      · intro v hv h0 hnz; obtain ⟨rfl, hlt, hne', hpos, hle⟩ := hnewm v hv h0 hnz
        exact ⟨(rsn &&& 0x7FFFFFFF#32).toNat, (mem_fullRsnLits_bin hne hbin).mpr rfl,
          rfl, hlt, hne', hpos, hle⟩
      · intro j hj1 hj2; obtain ⟨heq, _, _, h0, hpos, hcl, hmk⟩ := hnewt j hj1 hj2
        exact ⟨(mem_fullRsnLits_bin hne hbin).mpr heq, by omega, by omega, by rwa [heq],
          by rwa [heq], by rwa [heq], by rwa [heq]⟩
      · intro hok'; obtain ⟨hvlt, hrest⟩ := hok hok'
        refine ⟨hne, ?_, fun l hl => ?_⟩
        · rw [hant_eq, fullRsnLits, ite_eq_right (fun h => hne h), ite_eq_left hbin,
            List.countP_cons, List.countP_nil, Nat.zero_add]
          exact congrArg (s.scratch.ant_sz + ·)
            (b8_bv64_ite_iff (by simp only [decide_eq_true_eq]))
        · simp only [fullRsnLits, ite_eq_right (fun h => hne h), ite_eq_left hbin,
            List.mem_singleton] at hl
          subst hl; refine ⟨hvlt, fun hne' => ?_⟩
          obtain ⟨hm1, h0r⟩ := hrest hne'; refine ⟨hm1, fun h0 => ?_⟩
          obtain ⟨hle, _, hlow⟩ := h0r h0
          exact ⟨hle, fun hpos hlt => let ⟨_, htget⟩ := hlow hpos hlt
            ⟨s.core.tmp_len, Nat.le_refl _, by omega, by rw [htget]; rfl⟩⟩
    · have hne : rsn ≠ 0xFFFFFFFF#32 := ‹_›; have hlarge : (rsn &&& 0x80000000#32) = 0#32 := ‹_›
      have href : rsn.toNat ∈ fullArenaClauseRefs s := hrsn_ref hne hlarge
      obtain ⟨hbd3, hsz3, hbd, hbd_le, _⟩ := hw.arena.refs_wf rsn.toNat href
      have hsz_get : (s.core.arena[rsn.toNat + 2]'(by omega)).toNat =
          fullArenaClauseSize s rsn.toNat := by
        unfold fullArenaClauseSize fullArenaClauseSizeCore
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hhdr_get : s.core.arena[rsn.toNat]'(by omega) = s.core.arena[rsn.toNat]?.getD 0#32 := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      fa_unmdata; (try c0_let_simp)
      c0_step; c0_step; c0_step; all_goals (try exact hret_false_same)
      c0_step; c0_step; c0_step; all_goals (try exact hret_false_same)
      c0_step; c0_step; all_goals (try exact hret_false_same)
      refine wp_join_group (ts := []) (fun () m1 => ∃ arena1 gu1,
          let s1 : FullState := { s with core := { s.core with arena := arena1 }
                                         scratch := { s.scratch with glue_used := gu1 } }
          FullWitnessCutInv c F0 F_cur cut s1.core ∧ s1.LengthsOk c ∧
          fullArenaClauseRefs s1 = fullArenaClauseRefs s ∧
          (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s1 r = fullArenaClauseSize s r ∧
            fullArenaClauseGarb s1 r = fullArenaClauseGarb s r ∧
            fullArenaClauseLits s1 r = fullArenaClauseLits s r) ∧
          (∀ k < fullArenaClauseSize s rsn.toNat,
            arena1[rsn.toNat + 3 + k]? = s.core.arena[rsn.toNat + 3 + k]?) ∧
          (FullMem c s1 ⋆ R) m1) ?_ ?_
      · rintro _ ⟨⟩ m1 ⟨arena1, gu1, hw1, hlen1, hrefs1, hcl1, har1_eq, hm1⟩
        fa_steps
        let s1 : FullState := { s with core := { s.core with arena := arena1 }
                                       scratch := { s.scratch with glue_used := gu1 } }
        have har1_len : arena1.length = c.arena_cap := hlen1.core_ok.arena_len_arr
        have har1_le : s.core.arena_len ≤ c.arena_cap := hlen1.core_ok.arena_len_le
        let sz : Nat := fullArenaClauseSize s rsn.toNat
        let antPred : Nat → Bool := fun l =>
          decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)
        let LoopInv : Nat → List (BitVec 8) → List (BitVec 32) → List (BitVec 32) →
            Nat → Nat → Nat → BitVec 64 → BitVec 64 → Prop :=
          fun i mrk' tmp' ws1' mcl' tc' tl' ant' res' =>
            i ≤ sz ∧ mrk'.length = c.max_vars ∧ tmp'.length = c.max_vars ∧
            ws1'.length = 2 * c.max_vars ∧ mcl' ≤ c.max_vars ∧
            s.core.tmp_len ≤ tl' ∧ tl' ≤ s.core.cur_vars ∧ s.core.tmp_cnt ≤ tc' ∧
            FullAnaMarksCov c (canonRsnState s1 mrk' tmp' ws1' arena1 gu1
              mcl' tc' tl' ant' res') ∧
            CanonRsnPre c s (fullArenaClauseLits s rsn.toNat) skip_var mrk' tmp' tc' tl' res' ∧
            (∀ w < s.core.cur_vars, s.core.mrk[w]?.getD 0#8 = 0#8 → mrk'[w]?.getD 0#8 ≠ 0#8 →
              (s.core.lvl[w]?.getD 0#32).toNat < s.core.cur_level →
              ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = w) ∧
            ant' = s.scratch.ant_sz +
              BitVec.ofNat 64 (((fullArenaClauseLits s rsn.toNat).take i).countP antPred) ∧
            ∀ k < i, let l := (s.core.arena[rsn.toNat + 3 + k]?.getD 0#32).toNat
              l / 2 < s.core.cur_vars ∧ (l / 2 ≠ skip_var.toNat →
                (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
                (s.core.mrk[l / 2]?.getD 0#8 = 0#8 →
                  (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
                  (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat →
                    (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level →
                    ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧
                      (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))
        refine wp_loop_group (fun r (iv, ()) ml => ∃ i mrk' tmp' ws1' mcl' tc' tl' ant' res',
          r = sz - i ∧ iv = BitVec.ofNat 32 i ∧ LoopInv i mrk' tmp' ws1' mcl' tc' tl' ant' res' ∧
          (FullMem c (canonRsnState s mrk' tmp' ws1' arena1 gu1 mcl' tc' tl' ant' res') ⋆ R) ml)
          ?_ ?_
        · rintro L r ⟨iv, ⟨⟩⟩ ml ih ⟨i, mrk', tmp', ws1', mcl', tc', tl', ant', res', rfl, rfl,
            ⟨hile, hml_l, htl_l, hws_l, hmcl_le, htl_ge, htl_le, htc_ge, hcov', hpre,
              hnewlow, hant_l, hdone⟩, hml⟩
          have ⟨hmpres, htpres, hnewm, hnewt, hnd_t, hcnt, hres_l⟩ := hpre
          have hsz_mod : (rsn.toNat + (2#64).toNat) % 2 ^ 64 = rsn.toNat + 2 := by
            change (rsn.toNat + 2) % 2 ^ 64 = rsn.toNat + 2; omega
          have hidx_eq : s.core.arena[(rsn.toNat + (2#64).toNat) % 2 ^ 64]'(by omega) =
              s.core.arena[rsn.toNat + 2]'(by omega) := by simp only [hsz_mod]
          rw [Blocks.get_here]; fa_unmdata; (try c0_let_simp); c0_step
          · have hi32 : i < 2 ^ 32 := by omega
            have hilt : i < sz := by
              have hlt_bv : i % 2 ^ 32 <
                  (s.core.arena[(rsn.toNat + (2#64).toNat) % 2 ^ 64]'(by omega)).toNat := ‹_›
              rw [Nat.mod_eq_of_lt hi32, hidx_eq, hsz_get] at hlt_bv; exact hlt_bv
            have hidx_l : ((rsn.setWidth 64 + 3) + (BitVec.ofNat 32 i).setWidth 64).toNat =
                rsn.toNat + 3 + i := by simp only [bv_c0, BitVec.reduceToNat]; omega
            have hilt_core : i < fullArenaClauseSizeCore s.core rsn.toNat := hilt
            have hidx_lt : (rsn.setWidth 64 + 3 + (BitVec.ofNat 32 i).setWidth 64).toNat <
                arena1.length := by rw [hidx_l, har1_len]; omega
            fa_steps
            have htc_le_cv : tc' - s.core.tmp_cnt ≤ s.core.cur_vars := by
              rw [hcnt]; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
            let st := canonRsnState s1 mrk' tmp' ws1' arena1 gu1 mcl' tc' tl' ant' res'
            have hst_len : st.LengthsOk c :=
              ⟨{ hlen1.core_ok with
                  mrk_len := hml_l, tmp_len_arr := htl_l
                  tmp_len_le := (by dsimp [st]; omega), min_clr_len_le := hmcl_le },
               { hlen1.scratch_ok with work_stk1_len := hws_l }⟩
            let l_bv : BitVec 32 := arena1[rsn.toNat + 3 + i]'(by omega)
            have hl_eq : l_bv = s.core.arena[rsn.toNat + 3 + i]'(by omega) := by
              have h1 : arena1[rsn.toNat + 3 + i]? = some l_bv :=
                List.getElem?_eq_getElem (by omega)
              rw [har1_eq i hilt, List.getElem?_eq_getElem (by omega)] at h1
              exact (Option.some.inj h1).symm
            have hl_get : (s.core.arena[rsn.toNat + 3 + i]?.getD 0#32).toNat = l_bv.toNat := by
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← hl_eq]
            have hl_mem : l_bv.toNat ∈ fullArenaClauseLits s rsn.toNat :=
              (mem_fullArenaClauseLitsCore_iff (by omega)).mpr ⟨i, hilt, by rw [← hl_eq]⟩
            rw [getElem_eq_of_idx (hi := hidx_lt) (hj := by omega) hidx_l]
            refine wp_call_of_spec _ _ (hLit (c.hdr, l_bv, skip_var, ()) _ _ _
              ⟨c, st, R, rfl, hst_len, hcur32, htl_le, by dsimp [st]; omega, hcov', hml, ?_⟩)
            intro ok2 mrk2 tmp2 tc2 tl2 mcl2 ws2 ant2 res2 m2 _ hlen2 hcov2 htl2_ge htl2_inc
              htl2_le htc2_ge hant2 hres2 htc2_eq hmpres2 htpres2 hnewm2 hnewt2 hok2 hm2
            dsimp only [st, s1] at *
            have hpre2 := canon_rsn_step hcv_le htl_ge htl2_ge htl2_inc htc_ge hl_mem hpre hmpres2
              htpres2 hnewm2 hnewt2 hres2 htc2_eq
            cases ok2 with
            | false =>
              wp_unfold; obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hpre2
              exact hQ false mrk2 tmp2 tc2 tl2 mcl2 arena1
                { s.scratch with work_stk1 := ws2, glue_used := gu1,
                                 ant_sz := ant2, res_sz := res2 } m2
                hlen2
                (anaCut_to_canonCut (same_core_fullWitnessCut (canonCut_to_anaCut hw1)
                  hlen2.core_ok.mrk_len hlen2.core_ok.tmp_len_arr hlen2.core_ok.min_clr_len_le
                  htl2_le (tc' := tc2)) hw1.cut_le)
                hcov2 ⟨rfl, rfl⟩ rfl (by omega) htl2_le (by omega) hrefs1 hcl1 h1 h2
                (fun v hv hs0 hmnz => let ⟨l, hl, hr⟩ := h3 v hv hs0 hmnz
                  ⟨l, (mem_fullRsnLits_large hne hlarge).mpr hl, hr⟩)
                (fun j hj1 hj2 => let ⟨ha, hr⟩ := h4 j hj1 hj2
                  ⟨(mem_fullRsnLits_large hne hlarge).mpr ha, hr⟩)
                h5 h6 h7 (fun hc => by cases hc) hm2
            | true =>
              wp_unfold; obtain ⟨hvlt, hrest⟩ := hok2 rfl
              have htake1 : (fullArenaClauseLits s rsn.toNat).take (i + 1) =
                  (fullArenaClauseLits s rsn.toNat).take i ++ [l_bv.toNat] := by
                have hlen_l : (fullArenaClauseLits s rsn.toNat).length = sz := by
                  simp [fullArenaClauseLits, fullArenaClauseLitsCore, sz,
                    fullArenaClauseSize]; omega
                rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some]
                congr 2; unfold fullArenaClauseLits fullArenaClauseLitsCore
                simp [List.getElem_map, List.getElem_take, List.getElem_drop, ← hl_eq]
              have hant2_eq : ant2 = s.scratch.ant_sz + BitVec.ofNat 64
                  (((fullArenaClauseLits s rsn.toNat).take (i + 1)).countP antPred) := by
                rw [hant2, hant_l, htake1, List.countP_append, List.countP_cons, List.countP_nil,
                  Nat.zero_add, BitVec.add_assoc, BitVec.ofNat_add]
                exact congrArg (s.scratch.ant_sz + ·) (congrArg _
                  (b8_bv64_ite_iff (by simp only [antPred, decide_eq_true_eq])))
              rw [show BitVec.ofNat 32 i + 1 = BitVec.ofNat 32 (i + 1) from
                BitVec.eq_of_toNat_eq (by bv_omega)]
              refine ih (sz - (i + 1)) _ _ (by omega)
                ⟨i + 1, mrk2, tmp2, ws2, mcl2, tc2, tl2, ant2, res2, rfl, rfl,
                  ⟨by omega, hlen2.core_ok.mrk_len, hlen2.core_ok.tmp_len_arr,
                    hlen2.scratch_ok.work_stk1_len, hlen2.core_ok.min_clr_len_le,
                    by omega, htl2_le, by omega, hcov2, hpre2, ?_, hant2_eq, ?_⟩, hm2⟩
              · intro w hw_lt hs0 hmnz2 hltcl
                by_cases hm1_w : mrk'[w]?.getD 0#8 = 0#8
                · obtain ⟨rfl, _, hne', hpos, _⟩ := hnewm2 w (by omega) hm1_w hmnz2
                  obtain ⟨_, htget⟩ := ((hrest hne').2 hm1_w).2.2 hpos hltcl
                  exact ⟨tl', htl_ge, by omega, by rw [htget]; rfl⟩
                · obtain ⟨j, hj1, hj2, hjeq⟩ := hnewlow w hw_lt hs0 hm1_w hltcl
                  exact ⟨j, hj1, by omega, by rw [htpres2 j hj2]; exact hjeq⟩
              · intro k hk; by_cases hki : k = i
                · subst hki; dsimp only; rw [hl_get]; refine ⟨hvlt, fun hne' => ?_⟩
                  obtain ⟨hpos_m, hm1_r⟩ := hrest hne'; refine ⟨hpos_m, fun hs0 => ?_⟩
                  by_cases hm1_w : mrk'[l_bv.toNat / 2]?.getD 0#8 = 0#8
                  · obtain ⟨hle, _, hlow⟩ := hm1_r hm1_w
                    exact ⟨hle, fun hpos hltcl => let ⟨_, htget⟩ := hlow hpos hltcl
                      ⟨tl', htl_ge, by omega, by rw [htget]; rfl⟩⟩
                  · obtain ⟨_, _, _, _, _, _, hle⟩ := hnewm _ (by omega) hs0 hm1_w
                    exact ⟨hle, fun _ hltcl =>
                      let ⟨j, hj1, hj2, hjeq⟩ := hnewlow _ hvlt hs0 hm1_w hltcl
                      ⟨j, hj1, by omega, by rw [htpres2 j hj2]; exact hjeq⟩⟩
                · obtain ⟨hkv, hkrest⟩ := hdone k (by omega)
                  refine ⟨hkv, fun hne' => ?_⟩; obtain ⟨h1, h2⟩ := hkrest hne'
                  refine ⟨fun hp => by rw [hmpres2 _ (by omega) (h1 hp)]; exact h1 hp, ?_⟩
                  intro hs0
                  obtain ⟨hle, hlow⟩ := h2 hs0
                  exact ⟨hle, fun hpos hltcl => let ⟨j, hj1, hj2, hjeq⟩ := hlow hpos hltcl
                    ⟨j, hj1, by omega, by rw [htpres2 j hj2]; exact hjeq⟩⟩
          · fa_steps
            have hi32 : i < 2 ^ 32 := by omega
            have hieq : i = sz := by
              have hge_bv : ¬ i % 2 ^ 32 <
                  (s.core.arena[(rsn.toNat + (2#64).toNat) % 2 ^ 64]'(by omega)).toNat := ‹_›
              rw [Nat.mod_eq_of_lt hi32, hidx_eq, hsz_get] at hge_bv; omega
            refine hQ true mrk' tmp' tc' tl' mcl' arena1
              { s.scratch with work_stk1 := ws1', glue_used := gu1,
                               ant_sz := ant', res_sz := res' } ml
              ⟨{ hlen1.core_ok with
                  mrk_len := hml_l, tmp_len_arr := htl_l
                  tmp_len_le := (by dsimp; omega), min_clr_len_le := hmcl_le },
               { hlen1.scratch_ok with work_stk1_len := hws_l }⟩
              (anaCut_to_canonCut (same_core_fullWitnessCut (canonCut_to_anaCut hw1)
                hml_l htl_l hmcl_le htl_le (tc' := tc')) hw1.cut_le)
              hcov' ⟨rfl, rfl⟩ rfl htl_ge htl_le htc_ge hrefs1 hcl1 hmpres htpres
              (fun v hv hs0 hmnz => let ⟨l, hl, hr⟩ := hnewm v hv hs0 hmnz
                ⟨l, (mem_fullRsnLits_large hne hlarge).mpr hl, hr⟩)
              (fun j hj1 hj2 => let ⟨h1, hr⟩ := hnewt j hj1 hj2
                ⟨(mem_fullRsnLits_large hne hlarge).mpr h1, hr⟩)
              hnd_t hcnt hres_l (fun _ => ⟨hne, ?_, fun l hl => by
                simp only [fullRsnLits, hne, hlarge, ↓reduceIte] at hl
                obtain ⟨k, hk, hget⟩ := (mem_fullArenaClauseLitsCore_iff (by omega)).mp hl
                have hkget : (s.core.arena[rsn.toNat + 3 + k]?.getD 0#32).toNat = l := by
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]
                have hd := hdone k (by rw [hieq]; exact hk); rwa [hkget] at hd⟩) hml
            · have hlen_l : (fullArenaClauseLits s rsn.toNat).length = sz := by
                simp only [fullArenaClauseLits, fullArenaClauseLitsCore, sz, fullArenaClauseSize,
                  List.length_map, List.length_take, List.length_drop]; have := har_len; omega
              rw [hant_l, hieq, List.take_of_length_le (Nat.le_of_eq hlen_l)]
              simp [fullRsnLits, hne, hlarge, antPred]
        · intro L hL; fa_steps
          refine hL sz _ m1 ⟨0, s.core.mrk, s.core.tmp, s.scratch.work_stk1, s.core.min_clr_len,
            s.core.tmp_cnt, s.core.tmp_len, s.scratch.ant_sz, s.scratch.res_sz, by omega, rfl,
            ⟨Nat.zero_le _, hlen1.core_ok.mrk_len, hlen1.core_ok.tmp_len_arr,
              hlen1.scratch_ok.work_stk1_len, hlen1.core_ok.min_clr_len_le, Nat.le_refl _,
              htl_cv, Nat.le_refl _, hcov, ⟨fun _ _ _ => rfl, fun _ _ => rfl,
                fun _ _ h0 hnz => absurd h0 hnz, fun _ h1 h2 => by omega,
                fun _ _ _ h1 h2 => by omega,
                by rw [Nat.sub_self, eq_comm, List.length_eq_zero_iff, List.filter_eq_nil_iff]
                   intro _ _; simp,
                by rw [List.filter_eq_nil_iff.mpr (fun _ _ => by simp)]; simp⟩,
              fun _ _ h0 hnz _ => absurd h0 hnz, (by simp), fun _ hk => by omega⟩, hm1⟩
      · intro Jred hJred
        clear hLit hQ htl_cv htc_fit hcov hrsn_ref hsz_get hret_false_same skip_var
        c0_let_simp; c0_step
        · c0_step
          refine wp_join_group (ts := [i64])
            (fun (gi, ()) m_gi => gi.toNat < 64 ∧ (FullMem c s ⋆ R) m_gi) ?_ ?_
          · rintro _ ⟨gi, ⟨⟩⟩ m_gi ⟨hgi_lt, hm_gi⟩; clear hm; c0_let_simp
            refine wp_join_group (ts := []) (fun () m_gu => ∃ gu1, gu1.length = 64 ∧
              (FullMem c ⟨s.core, { s.scratch with glue_used := gu1 }⟩ ⋆ R) m_gu) ?_ ?_
            · rintro _ ⟨⟩ m_gu ⟨gu1, hgu1, hm_gu⟩; clear hm_gi
              let s_gu : FullState := ⟨s.core, { s.scratch with glue_used := gu1 }⟩
              change (FullMem c s_gu ⋆ R) m_gu at hm_gu; c0_let_simp
              refine wp_join_group (ts := [i32])
                (fun (new_u, ()) m_nu => (FullMem c s_gu ⋆ R) m_nu) ?_ ?_
              · rintro _ ⟨new_u, ⟨⟩⟩ m_nu hm_nu; clear hm_gu; dsimp only [s_gu] at hm_nu
                fa_steps
                · obtain ⟨hw', hr', hcl'⟩ := arenaBumpUsage_preserves_fullWitnessCut hlen.core_ok
                    (canonCut_to_anaCut hw) href new_u
                  have har_u_eq : s.core.arena.set (rsn.setWidth 64).toNat
                      ((s.core.arena[rsn.toNat]'(by omega) &&& 134217727#32) |||
                        (new_u <<< (27 : BitVec 32))) =
                      s.core.arena.set rsn.toNat ((fullArenaHdrCore s.core rsn.toNat &&&
                        0x07FFFFFF#32) ||| (new_u <<< 27)) := by
                    rw [bv_c0_zext32_64, hhdr_get]; rfl
                  let arena_u := s.core.arena.set rsn.toNat
                    ((fullArenaHdrCore s.core rsn.toNat &&& 0x07FFFFFF#32) ||| (new_u <<< 27))
                  exact hJred () _ ⟨arena_u, gu1, anaCut_to_canonCut hw' hw.cut_le,
                    ⟨{ hlen.core_ok with arena_len_arr := by simp [arena_u, har_len] },
                     { hlen.scratch_ok with glue_used_len := hgu1 }⟩,
                    hr', hcl', fun k _ => List.getElem?_set_ne (by omega),
                    fullMem_arena_gu_eq har_u_eq hm⟩
                · exact hJred () _ ⟨s.core.arena, gu1, hw,
                    ⟨hlen.core_ok, { hlen.scratch_ok with glue_used_len := hgu1 }⟩,
                    rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl, hm_nu⟩
              · intro Jnu hJnu; fa_steps <;> exact hJnu _ _ hm_gu
            · intro Jgu hJgu; fa_steps
              · exact hJgu () _ ⟨s.scratch.glue_used.set gi.toNat
                  (s.scratch.glue_used[gi.toNat]'(by omega) + 1), by simp [hgu_len], hm⟩
              · exact hJgu () _ ⟨s.scratch.glue_used, hgu_len, hm_gi⟩
          · intro Jgi hJgi; fa_steps
            · exact hJgi _ _ ⟨by decide, hm⟩
            · refine hJgi _ _ ⟨?_, hm⟩; simp only [bv_c0, BitVec.reduceToNat] at *; omega
        · fa_steps
          exact hJred () _ ⟨s.core.arena, s.scratch.glue_used, hw, hlen, rfl,
            fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl, hm⟩

theorem full_otfs_large_bridge_wp (Γ : Env)
    (hUnw : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullOtfsLargeSpec a m Q X → Func.wp Γ full_otfs_large_body a m Q X := by
  rintro ⟨h, cref, uip, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, cut, idx_u, s, R, rfl, hlen, hw, hnd, hdm, hcref, hng, hu_lt,
      hiu_cut, ht_u, hr_u, hlev_u, hent, hm, hQ⟩
  have hiu_te : idx_u < s.core.trail_end := Nat.lt_of_lt_of_le hiu_cut hw.cut_le
  refine full_otfs_large_wp_weak Γ hUnw (anaWatchPush_adapter hPush) _ m Q X
    ⟨c, F0, F_cur, cut, idx_u, s, R, rfl, hlen, hdm, canonCut_to_anaCut hw, hnd, hcref, hng,
      hu_lt, hiu_cut, hiu_te, ht_u, hr_u, hlev_u, hent, hm,
      fun ok ar' wv' ws' wl' wu' oom' sc' m' hlen' hw' hnd' hll hext hws1 hws2 hres hrefs
        hok hm' => ?_⟩
  refine hQ ok ar' wv' ws' wl' wu' oom' sc' m' hlen' (anaCut_to_canonCut hw' (by dsimp; omega)) hnd'
    ⟨hll, hext⟩ hws1 hws2 hres hrefs (fun htrue => ?_) hm'
  obtain ⟨hr', hng', hlits⟩ := hok htrue
  exact ⟨hr', hng', fun l hl => let ⟨_, _, hv, hlvl⟩ := hlits l hl; ⟨hv, hlvl⟩⟩

theorem full_otfs_bin_bridge_wp (Γ : Env)
    (hUnw : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullOtfsBinSpec a m Q X → Func.wp Γ full_otfs_bin_body a m Q X := by
  rintro ⟨h, cref, uip, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, cut, idx_u, s, R, rfl, hlen, hw, hnd, hdm, hcref, hng, hu_lt,
      hiu_cut, ht_u, hr_u, hlev_u, hent, hm, hQ⟩
  have hiu_te : idx_u < s.core.trail_end := Nat.lt_of_lt_of_le hiu_cut hw.cut_le
  refine full_otfs_bin_wp_weak Γ hUnw (anaWatchPush_adapter hPush) _ m Q X
    ⟨c, F0, F_cur, cut, idx_u, s, R, rfl, hlen, hdm, canonCut_to_anaCut hw, hnd, hcref, hng,
      hu_lt, hiu_cut, hiu_te, ht_u, hr_u, hlev_u, hent, hm,
      fun ok ar' ag' nb' wv' ws' wl' wu' ct' c0' c1' cr' oom' sc' m' hlen' hw' hnd' hll hext hws1
        hws2 hres hrefs hok hm' => ?_⟩
  refine hQ ok ar' ag' wv' ws' wl' wu' nb' ct' cr' c0' c1' oom' sc' m' hlen'
    (anaCut_to_canonCut hw' (by dsimp; omega)) hnd' ⟨hll, hext⟩ hws1 hws2 hres hrefs
    (fun htrue => ?_) hm'
  obtain ⟨hct, hcf⟩ := hok htrue
  exact ⟨hct, anaConflOk_to_canonCut hct hcf⟩

theorem full_otfs_subsume_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullOtfsSubsumeSpec a m Q X → Func.wp Γ full_otfs_subsume_body a m Q X := by
  rintro ⟨h, new_confl, old_ctype, old_cref, to_bin, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, cut, s, R, rfl, hlen, hw, hnd, hpre, hm, hQ⟩
  by_cases hct : old_ctype = 2#64
  · subst old_ctype
    refine full_otfs_subsume_wp Γ _ m Q X
      ⟨c, F0, F_cur, cut, s, R, rfl, hlen, canonCut_to_anaCut hw, hnd, fun _ hcr => ?_, hm,
        fun ar' ag' ni' nr' m' hlen' hw' hrefs hnd' hcl hm' =>
          hQ ar' ag' ni' nr' m' hlen' (anaCut_to_canonCut hw' hw.cut_le) hnd' hrefs
            (fun r hr => ⟨(hcl r hr).1, fun hf => (hcl r hr).2 rfl (hf rfl)⟩) hm'⟩
    obtain ⟨hold, hnew, hnonact⟩ := hpre rfl hcr
    exact ⟨hold, fun hnt => hnew (Bool.eq_false_iff.mpr hnt),
      fun idx hidx hcond hne hlg => hnonact idx hidx hcond hne hlg⟩
  · have hsame : Q () m := hQ s.core.arena s.core.arena_garbage s.core.num_irred
      s.core.num_redundant m hlen hw hnd rfl (fun _ _ => ⟨rfl, fun _ => rfl⟩) hm
    fa_fast_steps
    · exact hsame
    all_goals (exfalso; exact hct ‹_›)

theorem full_det_new_level_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullDetNewLevelSpec a m Q X → Func.wp Γ full_det_new_level_body a m Q X :=
  full_det_new_level_wp Γ

end Bridges

/-! ## Part 3: Index-verified `SpecEntry.Impl fullEnv` summary (`7` fns) -/

section Summary

private theorem fullFns_nodup : (fullFns.map Fn.name).Nodup := by
  have hchk := full_acyclic
  simp only [fullModule, Module.checkAcyclic, Bool.and_eq_true] at hchk
  exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1

private theorem fullSpecTable_nodup (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ((fullSpecTable mainSpec).map SpecEntry.name).Nodup := by
  have h : (fullSpecTable mainSpec).map SpecEntry.name = fullFns.map Fn.name := by
    have hm := congrArg (List.map Prod.fst) (fullSpecTable_sigs mainSpec)
    simpa only [List.map_map, Function.comp_def] using hm
  rw [h]
  exact fullFns_nodup

private theorem mkFullEnv_row_at {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    (i : Nat) (e : SpecEntry)
    (hi : (fullSpecTable mainSpec)[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → mkFullEnv mainSpec e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) (fullSpecTable_nodup mainSpec) (hno xs m Q X h)

/-- Canonical `fullFns` / `fullSpecTable` indices of the `7` Analyze/OTFS functions. -/
@[expose] def fullBridge8bIndices : List Nat :=
  [62, 63, 64, 66, 67, 68, 77]

theorem fullBridge8bIndices_length : fullBridge8bIndices.length = 7 := rfl

theorem fullBridge8bIndices_nodup : fullBridge8bIndices.Nodup := by decide

/-- Index-verified `SpecEntry.Impl (mkFullEnv mainSpec)` summary covering all `7` Analyze/OTFS
functions (`full_analyze_lit`, `full_analyze_rsn`, `full_clear_ana`, `full_otfs_large`,
`full_otfs_bin`, `full_otfs_subsume`, `full_det_new_level`). -/
theorem full_bridge_8b_mk_ok (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ∀ n ∈ fullBridge8bIndices,
      ∃ fn row, fullFns[n]? = some fn ∧
        (fullSpecTable mainSpec)[n]? = some row ∧
        SpecEntry.Impl (mkFullEnv mainSpec) fn row := by
  let Γ := mkFullEnv mainSpec
  let hWPush := mkFullEnv_row_at (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  let hUnw := mkFullEnv_row_at (mainSpec := mainSpec) 56
    ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  let hAnaLit := mkFullEnv_row_at (mainSpec := mainSpec) 62
    ⟨"full_analyze_lit", [i64, i32, i32], [.bool], fullAnalyzeLitSpec, true⟩
  intro n hn
  simp only [fullBridge8bIndices, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨full_analyze_lit, _, rfl, rfl, .of (full_analyze_lit_bridge_wp Γ)⟩
  · exact ⟨full_analyze_rsn, _, rfl, rfl, .of (full_analyze_rsn_bridge_wp Γ hAnaLit)⟩
  · exact ⟨full_clear_ana, _, rfl, rfl, .of (full_clear_ana_bridge_wp Γ)⟩
  · exact ⟨full_otfs_large, _, rfl, rfl, .of (full_otfs_large_bridge_wp Γ hUnw hWPush)⟩
  · exact ⟨full_otfs_bin, _, rfl, rfl, .of (full_otfs_bin_bridge_wp Γ hUnw hWPush)⟩
  · exact ⟨full_otfs_subsume, _, rfl, rfl, .of (full_otfs_subsume_bridge_wp Γ)⟩
  · exact ⟨full_det_new_level, _, rfl, rfl, .of (full_det_new_level_bridge_wp Γ)⟩

/-- Index-verified `SpecEntry.Impl fullEnv` summary covering all `7` Analyze/OTFS functions against
`fullSpecTable fullSolveBytesSpec`. -/
theorem full_bridge_8b_ok :
    ∀ n ∈ fullBridge8bIndices,
      ∃ fn row, fullFns[n]? = some fn ∧
        (fullSpecTable fullSolveBytesSpec)[n]? = some row ∧
        SpecEntry.Impl fullEnv fn row :=
  full_bridge_8b_mk_ok fullSolveBytesSpec

end Summary

end LeanQbe.T.Examples.Kissat.Full
