module

public import LeanQbe.T.Examples.Kissat.FullM7BveGates
public import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof2
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullBvaFwdSpec
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Wave-4E (`FullM7BveGates`) Proofs — Part 0 (M7 Specs, `scan_lit`, `get_tern`)

M1-clean proof module (`public section`, `0` `@[expose]`, `0` `import all`, `private` helpers):
1. `full_fwd_scan_lit_m7_wp`: certifies `fullFwdScanLitM7Spec` (`wsz == 0 || wsz > 1000` limit).
2. M7 gate-extraction specs (`_noExit`, `_intro`, `_elim`, `fullFwdCheckClM7Spec_of_canon`).
3. `full_bve_get_tern_m7_wp`: certifies `fullBveGetTernM7Spec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7BveGates

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullBvaFwdHelpers
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

/-! ## 3. `full_fwd_scan_lit_m7` (`<= 1000`-occ Limit + Self-Subsumption) -/

private theorem m7_lit_compl_conflict {α : Nat → Bool} {l : Nat}
    (h1 : α (litVar l) = !litSign l)
    (h2 : α (litVar (l ^^^ 1)) = !litSign (l ^^^ 1)) : False := by
  simp only [litVar, litSign] at h1 h2
  rw [fullInv_var_xor1 l, m6_xor1_mod2 l] at h2
  rcases Nat.mod_two_eq_zero_or_one l with hm | hm <;>
    cases h : α (l / 2) <;> simp_all

private theorem m7_selfsub_bin {F : CNF Nat} {C : List Nat} {scan_lit ot : Nat}
    (hC : F.EntailsClause (cnfClause C))
    (hbin : F.EntailsClause (cnfClause [scan_lit, ot]))
    (hscan : scan_lit ∈ C) (hne : ot ^^^ 1 ≠ scan_lit) :
    F.EntailsClause (cnfClause (C.filter (· != (ot ^^^ 1)))) := by
  rw [CNF.entails_clause_def] at hC hbin ⊢
  intro α hα
  have hb := (clause_sat_cnfClause_iff α _).mp (hbin α hα)
  have hc := (clause_sat_cnfClause_iff α _).mp (hC α hα)
  rw [clause_sat_cnfClause_iff]
  obtain ⟨lb, hlb, hsb⟩ := hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hlb
  rcases hlb with hlb | hlb
  · rw [hlb] at hsb
    exact ⟨scan_lit, List.mem_filter.mpr ⟨hscan, bne_iff_ne.mpr hne.symm⟩, hsb⟩
  · obtain ⟨lc, hlc, hsc⟩ := hc
    refine ⟨lc, List.mem_filter.mpr ⟨hlc, bne_iff_ne.mpr fun heq => ?_⟩, hsc⟩
    rw [heq] at hsc; rw [hlb] at hsb; exact m7_lit_compl_conflict hsb hsc

private theorem m7_selfsub_clause {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    {C D : List Nat} {drop : Nat}
    (hC : (cnfOfClauses F_cur).EntailsClause (cnfClause C))
    (hD : (cnfOfClauses F_cur).EntailsClause (cnfClause D))
    (hD_lt : ∀ l ∈ D, l < 2 * k.cur_vars)
    (hD_nd : (D.map (· / 2)).Nodup)
    (hneg_mem : drop ^^^ 1 ∈ D)
    (hD_ok : ∀ l ∈ D, l ∈ C ∨ k.vals[l]?.getD 0#8 = 0xFF#8 ∨ l = drop ^^^ 1) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause (C.filter (· != drop))) := by
  have hdrop_not_D : drop ∉ D := by
    intro hmem
    obtain ⟨i, hi, heq1⟩ := List.mem_iff_getElem.mp hmem
    obtain ⟨j, hj, heq2⟩ := List.mem_iff_getElem.mp hneg_mem
    have hij : i ≠ j := fun h => by
      subst h; rw [heq1] at heq2
      have hmod := m6_xor1_mod2 drop
      have := congrArg (· % 2) heq2; omega
    have hdiv : (D.map (· / 2))[i]'(by simp [hi]) = (D.map (· / 2))[j]'(by simp [hj]) := by
      simp only [List.getElem_map, heq1, heq2, fullInv_var_xor1]
    exact hij (by
      rcases Nat.lt_trichotomy i j with hlt | rfl | hgt
      · exact False.elim ((List.pairwise_iff_getElem.mp hD_nd) i j (by simp [hi]) (by simp [hj])
          hlt hdiv)
      · rfl
      · exact False.elim ((List.pairwise_iff_getElem.mp hD_nd) j i (by simp [hj]) (by simp [hi])
          hgt hdiv.symm))
  rw [CNF.entails_clause_def] at hC hD ⊢
  intro α hα
  have hd := (clause_sat_cnfClause_iff α _).mp (hD α hα)
  have hc := (clause_sat_cnfClause_iff α _).mp (hC α hα)
  rw [clause_sat_cnfClause_iff]
  obtain ⟨ld, hld, hsd⟩ := hd
  rcases hD_ok ld hld with hmemC | hfalse | hcompl
  · have hne : ld ≠ drop := fun heq => hdrop_not_D (heq ▸ hld)
    exact ⟨ld, List.mem_filter.mpr ⟨hmemC, bne_iff_ne.mpr hne⟩, hsd⟩
  · exfalso
    have hneg := m6_vals_neg_entails hw hl0 (hD_lt ld hld) hfalse
    have hsn := (clause_sat_cnfClause_iff α _).mp ((CNF.entails_clause_def.mp hneg) α hα)
    obtain ⟨l', hl', hs'⟩ := hsn
    rw [List.mem_singleton] at hl'; rw [hl'] at hs'
    exact m7_lit_compl_conflict hsd hs'
  · obtain ⟨lc, hlc, hsc⟩ := hc
    refine ⟨lc, List.mem_filter.mpr ⟨hlc, bne_iff_ne.mpr fun heq => ?_⟩, hsc⟩
    rw [heq] at hsc; rw [hcompl] at hsd
    exact m7_lit_compl_conflict hsc hsd

/-- Contract for `full_fwd_scan_lit_m7`: read-only scan of up to `1000` occurrences on `scan_lit`
against `lit_mark` (marking exact literals of live `cref`). -/
def fullFwdScanLitM7Spec : Spec [i64, i32, i32, i32, .bool] [i32] :=
  fun (h, cref, sz, scan_lit, check_bins, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64 ∧ FullArenaVarsNodup s ∧
      cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
      sz.toNat = fullArenaClauseSize s cref.toNat ∧ scan_lit.toNat < 2 * s.core.cur_vars ∧
      (check_bins = true → scan_lit.toNat ∈ fullArenaClauseLits s cref.toNat) ∧
      (∀ x < 2 * s.core.cur_vars,
        s.core.lit_mark[x]?.getD 0#8 ≠ 0#8 ↔ x ∈ fullArenaClauseLits s cref.toNat) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r : BitVec 32,
        (r = 0xFFFFFFFF#32 ∨ r = 0xFFFFFFFE#32 ∨
          (r.toNat ∈ fullArenaClauseLits s cref.toNat ∧
            (cnfOfClauses F_cur).EntailsClause
              (cnfClause ((fullArenaClauseLits s cref.toNat).filter (· != r.toNat))))) →
        Q (r, ()) m

theorem fullFwdScanLitM7Spec_noExit :
    ∀ xs m Q X, fullFwdScanLitM7Spec xs m Q X →
      fullFwdScanLitM7Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullFwdScanLitM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {cref sz scan_lit : BitVec 32}
    {check_bins : Bool} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hl0 : s.core.cur_level = 0) (hdm : s.core.dense_mode ≠ 0#64)
    (hnd : FullArenaVarsNodup s) (href : cref.toNat ∈ fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s cref.toNat = false)
    (hsz : sz.toNat = fullArenaClauseSize s cref.toNat)
    (hscan : scan_lit.toNat < 2 * s.core.cur_vars)
    (hcb : check_bins = true → scan_lit.toNat ∈ fullArenaClauseLits s cref.toNat)
    (hlm : ∀ x < 2 * s.core.cur_vars,
      s.core.lit_mark[x]?.getD 0#8 ≠ 0#8 ↔ x ∈ fullArenaClauseLits s cref.toNat)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ r : BitVec 32,
      (r = 0xFFFFFFFF#32 ∨ r = 0xFFFFFFFE#32 ∨
        (r.toNat ∈ fullArenaClauseLits s cref.toNat ∧
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause ((fullArenaClauseLits s cref.toNat).filter (· != r.toNat))))) →
      Q (r, ()) m) :
    fullFwdScanLitM7Spec (h, cref, sz, scan_lit, check_bins, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hlen, hw, hl0, hdm, hnd, href, hng, hsz, hscan, hcb, hlm, hm, hQ⟩

/-- Certifies `fullFwdScanLitM7Spec` for `full_fwd_scan_lit_m7` (`wsz == 0 || wsz > 1000` skip). -/
theorem full_fwd_scan_lit_m7_wp (Γ : Env) :
    ∀ a m Q X, fullFwdScanLitM7Spec a m Q X →
      Func.wp Γ full_fwd_scan_lit_m7_body a m Q X := by
  rintro ⟨h, cref, sz, scan_lit, check_bins, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, R, rfl, hlen0, hw0, hl0, hdm0, hnd0, href0, hng0, hsz0, hscan_lt,
      hcb_mem, hlm_iff, hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; have harc := c.harena
  unfold dimacsBound at hmx hwc harc
  have hcv_le := hlen0.core_ok.cur_vars_le
  have hwlen_le := hlen0.core_ok.wlen_le
  have hdw0 : DenseWatchesInv F_cur s0.core := by
    have := hw0.watches; unfold ModeWatchesInv at this; rwa [ite_eq_right hdm0] at this
  have hbd := hdw0.layout.bounds scan_lit.toNat hscan_lt
  have hlv0 : (scan_lit.setWidth 64 <<< (1 : Nat)).toNat < s0.core.wvec.length := by
    rw [hlen0.core_ok.wvec_len]; c0_bound
  have hlv1 : (scan_lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat < s0.core.wvec.length := by
    rw [hlen0.core_ok.wvec_len]; c0_bound
  unfold Func.wp full_fwd_scan_lit_m7_body
  c0_hsteps_nogrp
  · c0_hsteps!; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)
  · c0_hsteps!; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)
  · let off_s := (s0.core.wvec[(scan_lit.setWidth 64 <<< (1 : Nat)).toNat]'hlv0).setWidth 64
    let sz_s := (s0.core.wvec[(scan_lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat]'hlv1).setWidth 64
    let end_s := off_s + sz_s
    have hoff_eq : off_s.toNat = fullWatchOffCore s0.core scan_lit.toNat := by
      unfold off_s fullWatchOffCore
      rw [List.getElem?_eq_getElem (by rw [hlen0.core_ok.wvec_len]; omega), Option.getD_some,
        m6_zext32_toNat]
      exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
    have hsz_s_eq : sz_s.toNat = fullWatchSizeCore s0.core scan_lit.toNat := by
      unfold sz_s fullWatchSizeCore
      rw [List.getElem?_eq_getElem (by rw [hlen0.core_ok.wvec_len]; omega), Option.getD_some,
        m6_zext32_toNat]
      exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
    have hend_eq : end_s.toNat = off_s.toNat + sz_s.toNat := by
      dsimp only [end_s]; rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have hsum_c0 :
        ((s0.core.wvec[2 * scan_lit.toNat % 2 ^ 64]'(by
            rw [hlen0.core_ok.wvec_len]; omega)).toNat +
          (s0.core.wvec[(2 * scan_lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
            rw [hlen0.core_ok.wvec_len]; simp; omega)).toNat) % 2 ^ 64 = end_s.toNat := by
      have h1 : (s0.core.wvec[2 * scan_lit.toNat % 2 ^ 64]'(by
          rw [hlen0.core_ok.wvec_len]; omega)).toNat = off_s.toNat := by
        rw [hoff_eq]; unfold fullWatchOffCore
        rw [List.getElem?_eq_getElem (by rw [hlen0.core_ok.wvec_len]; omega), Option.getD_some]
        exact congrArg BitVec.toNat (m6_getElem_congr (by omega) _ _)
      have h2 : (s0.core.wvec[(2 * scan_lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
          rw [hlen0.core_ok.wvec_len]; simp; omega)).toNat = sz_s.toNat := by
        rw [hsz_s_eq]; unfold fullWatchSizeCore
        rw [List.getElem?_eq_getElem (by rw [hlen0.core_ok.wvec_len]; omega), Option.getD_some]
        exact congrArg BitVec.toNat (m6_getElem_congr (by simp; omega) _ _)
      rw [h1, h2, Nat.mod_eq_of_lt (by omega), hend_eq]
    have hent_C := hw0.arena.entails cref.toNat href0 hng0
    refine wp_loop_break_group (brkTs := [i64]) (lpTs := [i64])
      (fun _ mb => mb = m0)
      (fun rem (p, ()) mp =>
        mp = m0 ∧ p.toNat ≤ end_s.toNat ∧ rem = end_s.toNat - p.toNat ∧
        DenseWatchSliceOk F_cur s0.core scan_lit.toNat p.toNat rem)
      ?_ ?_ ?_
    · rintro _ ⟨_, ⟨⟩⟩ mb rfl; c0_hsteps!; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)
    · rintro B L rem ⟨p, ⟨⟩⟩ mp hB hL ⟨rfl, hp_le, hrem, hslice⟩
      c0_hsplit
      ·
          have hp_lt : p.toNat < end_s.toNat := by rw [hsum_c0] at hc; exact hc
          have hpw : p.toNat < s0.core.wstk.length := by rw [hlen0.core_ok.wstk_len_arr]; omega
          have hp1_nat : (p + 1#64).toNat = p.toNat + 1 := by c0_bound
          cases hslice with
          | empty => omega
          | @bin _ rem1 w0 hwp hflag _ hot_lt hent_bin hrest =>
            have hw0_eq : s0.core.wstk[p.toNat]'hpw = w0 := by
              rw [List.getElem?_eq_getElem hpw] at hwp; exact Option.some.inj hwp
            let ot := w0 &&& 0x7FFFFFFF#32
            have hot_lt' : ot.toNat < 2 * s0.core.cur_vars := hot_lt
            have hot_lm : (ot.setWidth 64).toNat < s0.core.lit_mark.length := by
              rw [hlen0.core_ok.lit_mark_len, m6_zext32_toNat]; omega
            have hotn_lt : (ot ^^^ 1#32).toNat < 2 * s0.core.cur_vars := by
              change ot.toNat ^^^ 1 < 2 * s0.core.cur_vars
              have := fullInv_var_xor1 ot.toNat; omega
            have hotn_lm : ((ot ^^^ 1#32).setWidth 64).toNat < s0.core.lit_mark.length := by
              rw [hlen0.core_ok.lit_mark_len, m6_zext32_toNat]; omega
            have hot_lm_c0 :
                (BitVec.setWidth 64 (s0.core.wstk[p.toNat] &&& 0x7FFFFFFF#32)).toNat <
                  s0.core.lit_mark.length := by
              rw [hw0_eq]; exact hot_lm
            have hotn_lm_c0 :
                (BitVec.setWidth 64 ((s0.core.wstk[p.toNat] &&& 0x7FFFFFFF#32) ^^^ 1#32)).toNat <
                  s0.core.lit_mark.length := by
              rw [hw0_eq]; exact hotn_lm
            c0_hsplit
            · refine wp_join0 (P := fun mj => mj = mp)
                (fun _ mj hmj => by
                  rcases hmj.symm with rfl
                  c0_hsteps!
                  exact hL rem1 (p + 1#64, ()) mp (by omega)
                    ⟨rfl, by omega, by omega, by rw [hp1_nat]; exact hrest⟩)
                (fun J44 hJ44 => by
                  c0_hsplit
                  · have hcb_t : check_bins = true := by simpa using hc
                    c0_hsplit
                    · c0_hsteps!; exact hQ 0xFFFFFFFE#32 (Or.inr (Or.inl rfl))
                    · have hot_c0 : (s0.core.wstk[p.toNat]'hpw &&& 0x7FFFFFFF#32) = ot := by
                        dsimp only [ot]; rw [hw0_eq]
                      have hne_c0 : (s0.core.wstk[p.toNat]'hpw &&& 0x7FFFFFFF#32 ^^^ 1#32) =
                          ot ^^^ 1#32 := by rw [hot_c0]
                      c0_hsplit
                      · have hne_scan : (ot ^^^ 1#32).toNat ≠ scan_lit.toNat := fun h =>
                          hc (hne_c0.symm ▸ BitVec.eq_of_toNat_eq h)
                        c0_hsplit
                        · have hmem_drop :
                              (ot ^^^ 1#32).toNat ∈ fullArenaClauseLits s0 cref.toNat := by
                            apply (hlm_iff _ hotn_lt).mp
                            have hlt_l : (ot ^^^ 1#32).toNat < s0.core.lit_mark.length := by
                              rw [hlen0.core_ok.lit_mark_len]; omega
                            rw [List.getElem?_eq_getElem hlt_l, Option.getD_some]
                            intro heq0
                            apply hc
                            have hlm_eq :
                                s0.core.lit_mark[(s0.core.wstk[p.toNat]'hpw &&&
                                  0x7FFFFFFF#32).toNat ^^^ 1]'(by
                                    rw [hw0_eq]; change (ot ^^^ 1#32).toNat < _; omega) =
                                  s0.core.lit_mark[(ot ^^^ 1#32).toNat]'hlt_l :=
                              m6_getElem_congr (congrArg BitVec.toNat hne_c0) _ _
                            have h0 :
                                BitVec.setWidth 32 (s0.core.lit_mark[(s0.core.wstk[p.toNat]'hpw &&&
                                  0x7FFFFFFF#32).toNat ^^^ 1]'(by
                                    rw [hw0_eq]; change (ot ^^^ 1#32).toNat < _; omega)) =
                                  0#32 := by
                              rw [hlm_eq, heq0]; rfl
                            exact h0
                          c0_hsteps!
                          exact hne_c0.symm ▸ hQ (ot ^^^ 1#32) (Or.inr (Or.inr ⟨hmem_drop,
                            m7_selfsub_bin hent_C hent_bin (hcb_mem hcb_t) hne_scan⟩))
                        · c0_hsteps!; exact hJ44 mp rfl
                      · c0_hsteps!; exact hJ44 mp rfl
                  · c0_hsteps!; exact hJ44 mp rfl)
            · rw [hw0_eq] at hc; exact absurd hc hflag
          | @occ _ rem2 w0 cr hwp hwp1 hflag _ _ href_cr hrest =>
            have hw0_eq : s0.core.wstk[p.toNat]'hpw = w0 := by
              rw [List.getElem?_eq_getElem hpw] at hwp; exact Option.some.inj hwp
            have hp1_w : (p + 1#64).toNat < s0.core.wstk.length := by
              rw [hlen0.core_ok.wstk_len_arr]; omega
            have hp1_c0 : (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
              simp; omega
            have hcr_eq :
                s0.core.wstk[(p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                  rw [hlen0.core_ok.wstk_len_arr]; omega) = cr := by
              rw [List.getElem?_eq_getElem (by rw [hlen0.core_ok.wstk_len_arr]; omega)] at hwp1
              exact (m6_getElem_congr hp1_c0 _ _).trans (Option.some.inj hwp1)
            have hp2_nat : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by c0_bound
            have hrest' : DenseWatchSliceOk F_cur s0.core scan_lit.toNat
                (p + 1#64 + 1#64).toNat rem2 := by
              rw [hp2_nat]; exact hrest
            have hwf_cr := hw0.arena.refs_wf cr.toNat href_cr
            have hal_le := hlen0.core_ok.arena_len_le
            have har_len_cr : cr.toNat < s0.core.arena.length := by
              rw [hlen0.core_ok.arena_len_arr]; omega
            have hcr_ar : (cr.setWidth 64).toNat < s0.core.arena.length := by
              rw [hlen0.core_ok.arena_len_arr, m6_zext32_toNat]; omega
            c0_hsplit
            · rw [hw0_eq] at hc; exact absurd hflag hc
            · c0_hsplit
              · rw [hsum_c0] at hc; simp at hc; omega
              · c0_hsplit
                · c0_hsteps!
                  exact hL rem2 (p + 1#64 + 1#64, ()) mp (by omega)
                    ⟨rfl, by omega, by omega, hrest'⟩
                · c0_hsplit
                  · c0_hsteps!
                    exact hL rem2 (p + 1#64 + 1#64, ()) mp (by omega)
                      ⟨rfl, by omega, by omega, hrest'⟩
                  · simp only [hcr_eq] at hc ⊢
                    have hng_cr : fullArenaClauseGarb s0 cr.toNat = false := by
                      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                      rw [List.getElem?_eq_getElem har_len_cr, Option.getD_some]
                      have h0 : (s0.core.arena[cr.toNat]'har_len_cr &&& 0x00080000#32) = 0#32 := by
                        have hsub : (0x00080000#32 : BitVec 32) &&&
                            ((524288 : BitVec 32) ||| (4194304 : BitVec 32)) = 0x00080000#32 := by
                          decide
                        have h0r : (0 : BitVec 32) &&& 0x00080000#32 = 0#32 := rfl
                        have hc' := congrArg (· &&& 0x00080000#32) hc
                        rw [BitVec.and_assoc, BitVec.and_comm _ 0x00080000#32, hsub, h0r] at hc'
                        exact hc'
                      rw [h0]; rfl
                    have hcr2_ar : (cr.setWidth 64 + 2#64).toNat < s0.core.arena.length := by
                      rw [hlen0.core_ok.arena_len_arr]; c0_bound
                    have hcr_p1' : s0.core.wstk[(p + (1 : BitVec 64)).toNat]'(by
                        rw [hlen0.core_ok.wstk_len_arr, BitVec.toNat_add,
                          show ((1 : BitVec 64)).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
                        omega) = cr := by
                      have h1 : (p + (1 : BitVec 64)).toNat =
                          (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 := by
                        rw [BitVec.toNat_add]
                      exact (m6_getElem_congr h1 _ _).trans hcr_eq
                    have hdsz_bd :
                        (BitVec.setWidth 64 (s0.core.wstk[(p + (1 : BitVec 64)).toNat]'(by
                          rw [hlen0.core_ok.wstk_len_arr, BitVec.toNat_add,
                            show ((1 : BitVec 64)).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
                          omega)) + (2 : BitVec 64)).toNat < s0.core.arena.length := by
                      rw [hcr_p1']; simpa [show ((2 : BitVec 64)) = 2#64 from rfl] using hcr2_ar
                    let dsz := s0.core.arena[(cr.setWidth 64 + 2#64).toNat]'hcr2_ar
                    have hdsz_eq : dsz.toNat = fullArenaClauseSizeCore s0.core cr.toNat := by
                      unfold dsz fullArenaClauseSizeCore
                      rw [List.getElem?_eq_getElem (by rw [hlen0.core_ok.arena_len_arr]; omega),
                        Option.getD_some]
                      exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
                    have hdsz_idx :
                        (s0.core.wstk[(p.toNat + BitVec.toNat (1 : BitVec 64)) %
                            2 ^ 64].toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 =
                          (cr.setWidth 64 + 2#64).toNat := by
                      rw [hcr_eq]; c0_bound
                    have hdsz_eq' :
                        s0.core.arena[(s0.core.wstk[(p.toNat + BitVec.toNat (1 : BitVec 64)) %
                            2 ^ 64].toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64] = dsz :=
                      m6_getElem_congr hdsz_idx _ _
                    c0_hsplit
                    · c0_hsteps!
                      exact hL rem2 (p + 1#64 + 1#64, ()) mp (by omega)
                        ⟨rfl, by omega, by omega, hrest'⟩
                    · c0_hsteps_nogrp
                      refine wp_loop_break_group (brkTs := [i32, i32, i32]) (lpTs := [i32, i32])
                        (fun (miss_b, cand_b, j_b, ()) ms => ms = mp ∧
                          (miss_b = 0#32 →
                            j_b = dsz ∧
                            (cand_b ≠ 0xFFFFFFFF#32 →
                              cand_b.toNat ∈ fullArenaClauseLits s0 cref.toNat ∧
                              cand_b.toNat ^^^ 1 ∈ fullArenaClauseLits s0 cr.toNat ∧
                              ∀ t < dsz.toNat,
                                let dl := (s0.core.arena[cr.toNat + 3 + t]?.getD 0#32).toNat
                                dl ∈ fullArenaClauseLits s0 cref.toNat ∨
                                s0.core.vals[dl]?.getD 0#8 = 0xFF#8 ∨
                                dl = cand_b.toNat ^^^ 1)))
                        (fun rem_j (cand_j, j, ()) mj => mj = mp ∧
                          j.toNat ≤ dsz.toNat ∧ rem_j = dsz.toNat - j.toNat ∧
                          (cand_j = 0xFFFFFFFF#32 →
                            ∀ t < j.toNat,
                              let dl := (s0.core.arena[cr.toNat + 3 + t]?.getD 0#32).toNat
                              dl ∈ fullArenaClauseLits s0 cref.toNat ∨
                              s0.core.vals[dl]?.getD 0#8 = 0xFF#8) ∧
                          (cand_j ≠ 0xFFFFFFFF#32 →
                            cand_j.toNat ∈ fullArenaClauseLits s0 cref.toNat ∧
                            cand_j.toNat ^^^ 1 ∈ fullArenaClauseLits s0 cr.toNat ∧
                            ∀ t < j.toNat,
                              let dl := (s0.core.arena[cr.toNat + 3 + t]?.getD 0#32).toNat
                              dl ∈ fullArenaClauseLits s0 cref.toNat ∨
                              s0.core.vals[dl]?.getD 0#8 = 0xFF#8 ∨
                              dl = cand_j.toNat ^^^ 1))
                        ?_ ?_ ?_
                      · rintro _ ⟨miss_b, cand_b, j_b, ⟨⟩⟩ ms ⟨hm_s, hpost⟩
                        rcases hm_s.symm with rfl
                        c0_hsplit
                        · obtain ⟨_, hcand⟩ := hpost hc
                          c0_hsplit
                          · c0_hsteps!; exact hQ 0xFFFFFFFE#32 (Or.inr (Or.inl rfl))
                          · obtain ⟨hmemC, hnegD, hallD⟩ := hcand hc
                            have hD_ok : ∀ l ∈ fullArenaClauseLits s0 cr.toNat,
                                l ∈ fullArenaClauseLits s0 cref.toNat ∨
                                s0.core.vals[l]?.getD 0#8 = 0xFF#8 ∨
                                l = cand_b.toNat ^^^ 1 := fun l hl => by
                              change l ∈ fullArenaClauseLitsCore s0.core cr.toNat at hl
                              rw [mem_fullArenaClauseLitsCore_iff (by
                                rw [hlen0.core_ok.arena_len_arr]; omega)] at hl
                              obtain ⟨t, ht, rfl⟩ := hl
                              have h1 := hallD t (by omega)
                              have hlt_t : cr.toNat + 3 + t < s0.core.arena.length := by
                                rw [hlen0.core_ok.arena_len_arr]; omega
                              rwa [List.getElem?_eq_getElem hlt_t, Option.getD_some] at h1
                            c0_hsteps!
                            exact hQ cand_b (Or.inr (Or.inr ⟨hmemC,
                              m7_selfsub_clause hw0 hl0 hent_C
                                (hw0.arena.entails cr.toNat href_cr hng_cr)
                                (hw0.arena.lits_lt cr.toNat href_cr hng_cr)
                                (hnd0 cr.toNat href_cr hng_cr) hnegD hD_ok⟩))
                        · c0_hsteps!
                          exact hL rem2 (p + 1#64 + 1#64, ()) mp (by omega)
                            ⟨rfl, by omega, by omega, hrest'⟩
                      · rintro Bj Lj rem_j ⟨cand_j, j, ⟨⟩⟩ mj hBj hLj
                          ⟨hm_j, hj_le, rfl, hc_none, hc_some⟩
                        rcases hm_j.symm with rfl
                        c0_hsplit
                        · have hj_lt : j.toNat < dsz.toNat := by rw [hdsz_eq'] at hc; exact hc
                          have hcrj : (cr.setWidth 64 + 3#64 + j.setWidth 64).toNat <
                              s0.core.arena.length := by
                            rw [hlen0.core_ok.arena_len_arr]; c0_bound
                          let dl :=
                            s0.core.arena[(cr.setWidth 64 + 3#64 + j.setWidth 64).toNat]'hcrj
                          have hdl_eq : s0.core.arena[cr.toNat + 3 + j.toNat]?.getD 0#32 = dl := by
                            have hal := hlen0.core_ok.arena_len_arr
                            rw [List.getElem?_eq_getElem (by rw [hal]; omega), Option.getD_some]
                            exact m6_getElem_congr (by c0_bound) _ _
                          have hdl_memD : dl.toNat ∈ fullArenaClauseLits s0 cr.toNat := by
                            change dl.toNat ∈ fullArenaClauseLitsCore s0.core cr.toNat
                            rw [mem_fullArenaClauseLitsCore_iff (by
                              rw [hlen0.core_ok.arena_len_arr]; omega)]
                            exact ⟨j.toNat, by omega, congrArg BitVec.toNat
                              (m6_getElem_congr (by c0_bound) _ _)⟩
                          have hdl_lt : dl.toNat < 2 * s0.core.cur_vars :=
                            hw0.arena.lits_lt cr.toNat href_cr hng_cr _ hdl_memD
                          have hdl_lm : (dl.setWidth 64).toNat < s0.core.lit_mark.length := by
                            rw [hlen0.core_ok.lit_mark_len, m6_zext32_toNat]; omega
                          have hdl_v : (dl.setWidth 64).toNat < s0.core.vals.length := by
                            rw [hlen0.core_ok.vals_len, m6_zext32_toNat]; omega
                          have hdln_lt : (dl ^^^ 1#32).toNat < 2 * s0.core.cur_vars := by
                            change dl.toNat ^^^ 1 < 2 * s0.core.cur_vars
                            have := fullInv_var_xor1 dl.toNat; omega
                          have hdln_lm : ((dl ^^^ 1#32).setWidth 64).toNat <
                              s0.core.lit_mark.length := by
                            rw [hlen0.core_ok.lit_mark_len, m6_zext32_toNat]; omega
                          have hcrj_c0 :
                              (BitVec.setWidth 64 (s0.core.wstk[(p + (1 : BitVec 64)).toNat]'(by
                                rw [hlen0.core_ok.wstk_len_arr, BitVec.toNat_add,
                                  show ((1 : BitVec 64)).toNat = 1 from rfl,
                                  Nat.mod_eq_of_lt (by omega)]
                                omega)) + (3 : BitVec 64) + j.setWidth 64).toNat <
                                s0.core.arena.length := by
                            rw [hcr_p1']; exact hcrj
                          have hdl_c0_eq :
                              s0.core.arena[(BitVec.setWidth 64
                                  (s0.core.wstk[(p + (1 : BitVec 64)).toNat]'(by
                                    rw [hlen0.core_ok.wstk_len_arr, BitVec.toNat_add,
                                      show ((1 : BitVec 64)).toNat = 1 from rfl,
                                      Nat.mod_eq_of_lt (by omega)]
                                    omega)) + (3 : BitVec 64) + j.setWidth 64).toNat]'hcrj_c0 =
                                dl := by
                            dsimp only [dl]; exact m6_getElem_congr (by rw [hcr_p1']; rfl) _ _
                          have hdl_c0_lm :
                              (BitVec.setWidth 64 (s0.core.arena[(BitVec.setWidth 64
                                  (s0.core.wstk[(p + (1 : BitVec 64)).toNat]'(by
                                    rw [hlen0.core_ok.wstk_len_arr, BitVec.toNat_add,
                                      show ((1 : BitVec 64)).toNat = 1 from rfl,
                                      Nat.mod_eq_of_lt (by omega)]
                                    omega)) + (3 : BitVec 64) + j.setWidth 64).toNat])).toNat <
                                s0.core.lit_mark.length := by
                            rw [hdl_c0_eq]; exact hdl_lm
                          have hdl_c0_v :
                              (BitVec.setWidth 64 (s0.core.arena[(BitVec.setWidth 64
                                  (s0.core.wstk[(p + (1 : BitVec 64)).toNat]'(by
                                    rw [hlen0.core_ok.wstk_len_arr, BitVec.toNat_add,
                                      show ((1 : BitVec 64)).toNat = 1 from rfl,
                                      Nat.mod_eq_of_lt (by omega)]
                                    omega)) + (3 : BitVec 64) + j.setWidth 64).toNat])).toNat <
                                s0.core.vals.length := by
                            rw [hdl_c0_eq]; exact hdl_v
                          have hdln_c0_lm :
                              (BitVec.setWidth 64 ((s0.core.arena[(BitVec.setWidth 64
                                  (s0.core.wstk[(p + (1 : BitVec 64)).toNat]'(by
                                    rw [hlen0.core_ok.wstk_len_arr, BitVec.toNat_add,
                                      show ((1 : BitVec 64)).toNat = 1 from rfl,
                                      Nat.mod_eq_of_lt (by omega)]
                                    omega)) + (3 : BitVec 64) + j.setWidth 64).toNat]) ^^^
                                1#32)).toNat < s0.core.lit_mark.length := by
                            rw [hdl_c0_eq]; exact hdln_lm
                          have hdl_idx :
                              (s0.core.wstk[(p.toNat +
                                  BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat +
                                BitVec.toNat (3 : BitVec 64) + j.toNat) % 2 ^ 64 =
                                (cr.setWidth 64 + 3#64 + j.setWidth 64).toNat := by
                            rw [hcr_eq]; c0_bound
                          have hdl_c0_eq' :
                              s0.core.arena[(s0.core.wstk[(p.toNat +
                                  BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat +
                                BitVec.toNat (3 : BitVec 64) + j.toNat) % 2 ^ 64]'(by
                                  rw [hdl_idx]; exact hcrj) = dl :=
                            m6_getElem_congr hdl_idx _ _
                          have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
                          c0_hsteps_nogrp
                          refine wp_join_state_pure (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
                            (fun x => (x.1, x.2, ()))
                            (fun x =>
                              (x.2 = 0xFFFFFFFF#32 →
                                ∀ t < j.toNat + 1,
                                  let dl := (s0.core.arena[cr.toNat + 3 + t]?.getD 0#32).toNat
                                  dl ∈ fullArenaClauseLits s0 cref.toNat ∨
                                  s0.core.vals[dl]?.getD 0#8 = 0xFF#8) ∧
                              (x.2 ≠ 0xFFFFFFFF#32 →
                                x.2.toNat ∈ fullArenaClauseLits s0 cref.toNat ∧
                                x.2.toNat ^^^ 1 ∈ fullArenaClauseLits s0 cr.toNat ∧
                                ∀ t < j.toNat + 1,
                                  let dl := (s0.core.arena[cr.toNat + 3 + t]?.getD 0#32).toNat
                                  dl ∈ fullArenaClauseLits s0 cref.toNat ∨
                                  s0.core.vals[dl]?.getD 0#8 = 0xFF#8 ∨
                                  dl = x.2.toNat ^^^ 1))
                            (fun _ ⟨_, cand_n⟩ ⟨hc_n, hc_s⟩ => by
                              c0_hsteps!
                              exact hLj (dsz.toNat - (j + 1#32).toNat) (cand_n, j + 1#32, ()) mp
                                (by omega) ⟨rfl, by omega, rfl, by rw [hj1]; exact hc_n, by
                                  rw [hj1]; exact hc_s⟩)
                            (fun J75 hJ75 => by
                              have hstep_keep :
                                  (dl.toNat ∈ fullArenaClauseLits s0 cref.toNat ∨
                                    s0.core.vals[dl.toNat]?.getD 0#8 = 0xFF#8) →
                                  J75 (0#32, cand_j, ()) mp := fun hok =>
                                hJ75 (0#32, cand_j)
                                  ⟨fun hcn t ht => by
                                     rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp ht) with h | h
                                     · exact hc_none hcn t h
                                     · subst h; rw [hdl_eq]; exact hok,
                                   fun hcs => by
                                     obtain ⟨hmC, hnD, hall⟩ := hc_some hcs
                                     refine ⟨hmC, hnD, fun t ht => ?_⟩
                                     rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp ht) with h | h
                                     · exact hall t h
                                     · subst h; rw [hdl_eq]
                                       exact hok.imp id (fun hf => Or.inl hf)⟩
                              c0_hsplit
                              · c0_hsplit
                                · c0_hsplit
                                  · have hlm_dln_nz := hc
                                    c0_hsplit
                                    · have hcn : cand_j = 0xFFFFFFFF#32 := hc
                                      have hne_ff : (dl ^^^ 1#32) ≠ 0xFFFFFFFF#32 := fun h => by
                                        have hdln_ff : (dl ^^^ 1#32).toNat = 4294967295 :=
                                          congrArg BitVec.toNat h
                                        omega
                                      have hmem_dln :
                                          (dl ^^^ 1#32).toNat ∈
                                            fullArenaClauseLits s0 cref.toNat := by
                                        apply (hlm_iff _ hdln_lt).mp
                                        have hlt_l :
                                            (dl ^^^ 1#32).toNat < s0.core.lit_mark.length := by
                                          rw [hlen0.core_ok.lit_mark_len]; omega
                                        rw [List.getElem?_eq_getElem hlt_l, Option.getD_some]
                                        intro heq0
                                        apply hlm_dln_nz
                                        have hlm :
                                            s0.core.lit_mark[(s0.core.arena[(s0.core.wstk[(p.toNat +
                                                BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat +
                                                BitVec.toNat (3 : BitVec 64) +
                                                j.toNat) % 2 ^ 64] ^^^
                                                1#32).toNat]'(by rw [hdl_c0_eq']; exact hdln_lm) =
                                              0#8 :=
                                          (m6_getElem_congr (by rw [hdl_c0_eq']) _ hlt_l).trans heq0
                                        have hxor_nat :
                                            s0.core.arena[(s0.core.wstk[(p.toNat +
                                                BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat +
                                                BitVec.toNat (3 : BitVec 64) + j.toNat) %
                                                2 ^ 64].toNat ^^^ 1 =
                                              (s0.core.arena[(s0.core.wstk[(p.toNat +
                                                BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat +
                                                BitVec.toNat (3 : BitVec 64) +
                                                j.toNat) % 2 ^ 64] ^^^
                                                1#32).toNat := by
                                          rw [BitVec.toNat_xor, show (1#32).toNat = 1 from rfl]
                                        exact show
                                            BitVec.setWidth 32 (s0.core.lit_mark[_]'_) = 0#32 by
                                          rw [m6_getElem_congr hxor_nat _
                                            (by rw [hdl_c0_eq']; exact hdln_lm), hlm]; rfl
                                      have hneg_eq : (dl ^^^ 1#32).toNat ^^^ 1 = dl.toNat := by
                                        change (dl.toNat ^^^ 1) ^^^ 1 = dl.toNat
                                        exact litNeg_litNeg dl.toNat
                                      c0_hsteps!
                                      have hdl_j75 : J75 (0#32, dl ^^^ 1#32, ()) mp := by
                                        refine hJ75 (0#32, dl ^^^ 1#32)
                                          ⟨fun h => absurd h hne_ff, fun _ =>
                                            ⟨hmem_dln, by rw [hneg_eq]; exact hdl_memD, fun t ht =>
                                              by
                                              rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp ht)
                                                with h | h
                                              · exact (hc_none hcn t h).imp id (fun hf => Or.inl hf)
                                              · subst h; rw [hdl_eq]
                                                exact Or.inr (Or.inr (show dl.toNat =
                                                  ((0#32, dl ^^^ 1#32).2.toNat ^^^ 1) from
                                                  hneg_eq.symm))⟩⟩
                                      exact (congrArg (fun x => J75 (0#32, x ^^^ 1#32, ()) mp)
                                        hdl_c0_eq).mpr hdl_j75
                                    · c0_hsteps!
                                      exact hBj (1#32, cand_j, j, ()) mp ⟨rfl, fun h => by cases h⟩
                                  · c0_hsteps!
                                    exact hBj (1#32, cand_j, j, ()) mp ⟨rfl, fun h => by cases h⟩
                                · have hdl_ff : s0.core.vals[dl.toNat]?.getD 0#8 = 0xFF#8 := by
                                    have hdom := hw0.vals_domain dl.toNat hdl_lt
                                    have hlt_v : dl.toNat < s0.core.vals.length := by
                                      rw [hlen0.core_ok.vals_len]; omega
                                    rw [List.getElem?_eq_getElem hlt_v, Option.getD_some] at hdom ⊢
                                    rcases hdom with h0 | h1 | hff
                                    · have hbad :
                                          (0#32).sle ((s0.core.vals[s0.core.arena[(s0.core.wstk[(
                                              p.toNat + BitVec.toNat (1 : BitVec 64)) %
                                              2 ^ 64].toNat + BitVec.toNat (3 : BitVec 64) +
                                              j.toNat) % 2 ^ 64].toNat]'(by
                                                rw [hdl_c0_eq']; exact hlt_v)).signExtend 32) =
                                            true := by
                                        rw [m6_getElem_congr (by rw [hdl_c0_eq']) _ hlt_v, h0]
                                        decide
                                      exact absurd hc (by rw [hbad]; decide)
                                    · have hbad :
                                          (0#32).sle ((s0.core.vals[s0.core.arena[(s0.core.wstk[(
                                              p.toNat + BitVec.toNat (1 : BitVec 64)) %
                                              2 ^ 64].toNat + BitVec.toNat (3 : BitVec 64) +
                                              j.toNat) % 2 ^ 64].toNat]'(by
                                                rw [hdl_c0_eq']; exact hlt_v)).signExtend 32) =
                                            true := by
                                        rw [m6_getElem_congr (by rw [hdl_c0_eq']) _ hlt_v, h1]
                                        decide
                                      exact absurd hc (by rw [hbad]; decide)
                                    · exact hff
                                  c0_hsteps!; exact hstep_keep (Or.inr hdl_ff)
                              · have hdl_memC : dl.toNat ∈ fullArenaClauseLits s0 cref.toNat := by
                                  apply (hlm_iff _ hdl_lt).mp
                                  have hlt_l : dl.toNat < s0.core.lit_mark.length := by
                                    rw [hlen0.core_ok.lit_mark_len]; omega
                                  rw [List.getElem?_eq_getElem hlt_l, Option.getD_some]
                                  intro heq0
                                  apply hc
                                  have hlm :
                                      s0.core.lit_mark[s0.core.arena[(s0.core.wstk[(p.toNat +
                                          BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat +
                                          BitVec.toNat (3 : BitVec 64) + j.toNat) % 2 ^ 64].toNat]'(
                                            by rw [hdl_c0_eq']; exact hlt_l) = 0#8 :=
                                    (m6_getElem_congr (by rw [hdl_c0_eq']) _ hlt_l).trans heq0
                                  exact show BitVec.setWidth 32 (s0.core.lit_mark[_]'_) = 0#32 by
                                    rw [hlm]; rfl
                                c0_hsteps!; exact hstep_keep (Or.inl hdl_memC))
                        · rw [hdsz_eq'] at hc
                          have hj_eq : j = dsz := BitVec.eq_of_toNat_eq (by omega)
                          c0_hsteps!
                          exact hBj (0#32, cand_j, j, ()) mp
                            ⟨rfl, fun _ => ⟨hj_eq, by subst hj_eq; exact hc_some⟩⟩
                      · intro _ Lj _ hLj; c0_hsteps!
                        exact hLj dsz.toNat (0xFFFFFFFF#32, 0#32, ()) mp
                          ⟨rfl, Nat.zero_le _, by rw [show (0#32).toNat = 0 from rfl, Nat.sub_zero],
                           fun _ _ h => by rw [show (0#32).toNat = 0 from rfl] at h; omega,
                           fun h => absurd rfl h⟩
      · c0_hsteps!; exact hB (_, ()) mp rfl
    · intro _ L _ hL; c0_hsteps!
      exact hL sz_s.toNat (off_s, ()) m0
        ⟨rfl, by omega, by omega, by
          rw [hoff_eq, hsz_s_eq]; exact hdw0.slices scan_lit.toNat hscan_lt⟩

/-! ## 4. Shared M7 Specs & `full_bve_get_tern_m7` -/

/-- Contract for `full_fwd_check_cl_m7` (matches `FullM6BveFwd.fullFwdCheckClM6Spec`). -/
def fullFwdCheckClM7Spec : Spec [i64, i32] [.bool] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.red_refs = s.scratch.red_refs →
      (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem fullFwdCheckClM7Spec_noExit :
    ∀ xs m Q X, fullFwdCheckClM7Spec xs m Q X →
      fullFwdCheckClM7Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullFwdCheckClM7Spec_of_canon {a m Q X} (h : Full.fullFwdCheckClSpec a m Q X) :
    fullFwdCheckClM7Spec a m Q X := by
  rcases a with ⟨h_ptr, cref, ⟨⟩⟩
  rcases h with ⟨c, F0, F_cur, s, R, rfl, hdw, href, hm, hQ⟩
  exact ⟨c, F0, F_cur, s, R, rfl, hdw, href, hm,
    fun ok s' m' h1 h2 h3 h4 h5 _ _ h6 hm' => hQ ok s' m' h1 h2 h3 h4 h5 h6 hm'⟩

theorem fullFwdCheckClM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {cref : BitVec 32}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s)
    (href : cref.toNat ∈ fullArenaClauseRefs s) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.red_refs = s.scratch.red_refs →
      (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    fullFwdCheckClM7Spec (h, cref, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, href, hm, hQ⟩

theorem fullFwdCheckClM7Spec_elim {a m Q X} (h : fullFwdCheckClM7Spec a m Q X) :
    let (h_ptr, cref, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h_ptr = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) s' m',
        FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
        s'.core.arena_len = s.core.arena_len → s'.core.fuel = s.core.fuel →
        fullArenaClauseRefs s' = fullArenaClauseRefs s →
        s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
        s'.scratch.red_refs = s.scratch.red_refs →
        (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨h_ptr, cref, ⟨⟩⟩; exact h

/-- Contract for `full_bve_get_tern_m7`: extracts 2 unassigned literals of `cr`. -/
def fullBveGetTernM7Spec : Spec [i64, i32, i32, i32] [.bool] :=
  fun (h, _v_lit, cr, out_off, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
      cr.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cr.toNat = false ∧
      out_off.toNat + 2 ≤ c.scratch_cap ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < out_off.toNat ∨ out_off.toNat + 2 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem fullBveGetTernM7Spec_noExit :
    ∀ xs m Q X, fullBveGetTernM7Spec xs m Q X →
      fullBveGetTernM7Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullBveGetTernM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {v_lit cr out_off : BitVec 32}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s)
    (href : cr.toNat ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cr.toNat = false)
    (hout : out_off.toNat + 2 ≤ c.scratch_cap) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < out_off.toNat ∨ out_off.toNat + 2 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    fullBveGetTernM7Spec (h, v_lit, cr, out_off, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, href, hng, hout, hm, hQ⟩

/-- Certifies `fullBveGetTernM7Spec` for `full_bve_get_tern_m7`. -/
theorem full_bve_get_tern_m7_wp (Γ : Env) :
    ∀ a m Q X, fullBveGetTernM7Spec a m Q X →
      Func.wp Γ full_bve_get_tern_m7_body a m Q X := by
  rintro ⟨h, v_lit, cr, out_off, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, R, rfl, hdw0, href, hng, hout, hm0, hQ⟩
  have hmx := c.hmaxv; have harc := c.harena; have hsc := c.hscr
  unfold dimacsBound at hmx harc hsc
  have hwf := hdw0.2.1.arena.refs_wf cr.toNat href
  have hal_le := hdw0.1.core_ok.arena_len_le
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hcr2_ar : (cr.setWidth 64 + 2#64).toNat < s0.core.arena.length := by
    rw [hdw0.1.core_ok.arena_len_arr]; c0_bound
  let sz := s0.core.arena[(cr.setWidth 64 + 2#64).toNat]'hcr2_ar
  have hsz_eq : sz.toNat = fullArenaClauseSizeCore s0.core cr.toNat := by
    unfold sz fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.arena_len_arr]; omega), Option.getD_some]
    exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
  unfold Func.wp full_bve_get_tern_m7_body
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32, i32, i32, i32])
    (fun rem (cnt, l0, l1, i, ()) mi =>
      mi = m0 ∧ i.toNat ≤ sz.toNat ∧ rem = sz.toNat - i.toNat)
    ?_ ?_
  · rintro L rem ⟨cnt, l0, l1, i, ⟨⟩⟩ mi hL ⟨hm_eq, hi_le, rfl⟩
    subst mi
    c0_hsplit
    · have hi_lt : i.toNat < sz.toNat := hc
      have hcri : (cr.setWidth 64 + 3#64 + i.setWidth 64).toNat < s0.core.arena.length := by
        rw [hdw0.1.core_ok.arena_len_arr]; c0_bound
      let li := s0.core.arena[(cr.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hcri
      have hli_lt : li.toNat < 2 * s0.core.cur_vars := by
        have hmem : li.toNat ∈ fullArenaClauseLitsCore s0.core cr.toNat := by
          rw [mem_fullArenaClauseLitsCore_iff (by rw [hdw0.1.core_ok.arena_len_arr]; omega)]
          exact ⟨i.toNat, by omega, congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)⟩
        exact hdw0.2.1.arena.lits_lt cr.toNat href hng _ hmem
      have hli_v : (li.setWidth 64).toNat < s0.core.vals.length := by
        rw [hdw0.1.core_ok.vals_len, m6_zext32_toNat]; omega
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
      c0_hsteps_nogrp
      refine wp_join_state_pure (ts := [i32, i32, i32]) (α := BitVec 32 × BitVec 32 × BitVec 32)
        (fun x => (x.1, x.2.1, x.2.2, ())) (fun _ => True)
        (fun _ ⟨c', a', b'⟩ _ => by
          c0_hsteps!
          exact hL (sz.toNat - (i + 1#32).toNat) (c', a', b', i + 1#32, ()) m0 (by omega)
            ⟨rfl, by omega, rfl⟩)
        (fun J hJ => by
          c0_hsplit
          · c0_hsplit
            · c0_hsteps!
              exact hQ false s0.scratch.scratch_buf m0 hdw0.1.scratch_ok.scratch_buf_len
                (fun _ _ _ => rfl) hm0
            · c0_hsteps_nogrp
              refine wp_join_state_pure (ts := [i32, i32, i32])
                (α := BitVec 32 × BitVec 32 × BitVec 32)
                (fun x => (x.1, x.2.1, x.2.2, ())) (fun _ => True)
                (fun _ x _ => by c0_hsteps!; exact hJ x trivial)
                (fun J37 hJ37 => by
                  c0_hsplit
                  · c0_hsteps_nogrp
                    refine wp_join_state_pure (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
                      (fun p => (p.1, p.2, ())) (fun _ => True)
                      (fun _ ⟨a', b'⟩ _ => by
                        c0_hsteps!; exact hJ37 (cnt + 1#32, a', b') trivial)
                      (fun J42 hJ42 => by
                        c0_hsplit
                        · c0_hsteps!; exact hJ42 (li, l1) trivial
                        · c0_hsplit
                          · c0_hsteps!; exact hJ42 (l0, li) trivial
                          · c0_hsteps!
                            exact hQ false s0.scratch.scratch_buf m0
                              hdw0.1.scratch_ok.scratch_buf_len (fun _ _ _ => rfl) hm0)
                  · c0_hsteps!; exact hJ37 (cnt, l0, l1) trivial)
          · c0_hsteps!; exact hJ (cnt, l0, l1) trivial)
    · c0_hsplit
      · c0_hsteps!
        exact hQ false s0.scratch.scratch_buf m0 hdw0.1.scratch_ok.scratch_buf_len
          (fun _ _ _ => rfl) hm0
      · have ho0 : (out_off.setWidth 64).toNat < s0.scratch.scratch_buf.length := by
          rw [hdw0.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; omega
        have ho1 : ((out_off + 1#32).setWidth 64).toNat < s0.scratch.scratch_buf.length := by
          rw [hdw0.1.scratch_ok.scratch_buf_len, m6_zext32_toNat]; c0_bound
        c0_hsteps!
        exact hQ true _ _ (by simp [hdw0.1.scratch_ok.scratch_buf_len])
          (fun i hi hor => by
            rw [List.getElem?_set_ne (by rw [m6_zext32_toNat]; c0_bound),
              List.getElem?_set_ne (by rw [m6_zext32_toNat]; omega)]) hm
  · intro L hL; c0_hsteps!
    exact hL sz.toNat (0#32, 0#32, 0#32, 0#32, ()) m0 ⟨rfl, Nat.zero_le _, by simp⟩

/-- Contract for `full_bve_find_equiv_m7`. -/
def fullBveFindEquivM7Spec : Spec [i64, i32, i32] [.bool] := fun (h, np, nn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1088 ≤ c.scratch_cap ∧
    np.toNat ≤ 512 ∧ nn.toNat ≤ 512 ∧
    (∀ i < np.toNat, let w := s.scratch.scratch_buf[i]?.getD 0#32;
      (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars) ∧
    (∀ j < nn.toNat, let w := s.scratch.scratch_buf[512 + j]?.getD 0#32;
      (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) lm' scr' m',
      let s' : FullState :=
        { s with core := { s.core with lit_mark := lm' }
                 scratch := { s.scratch with scratch_buf := scr' } }
      FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1058 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem fullBveFindEquivM7Spec_noExit :
    ∀ xs m Q X, fullBveFindEquivM7Spec xs m Q X →
      fullBveFindEquivM7Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullBveFindEquivM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {np nn : BitVec 32}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (hsc : 1088 ≤ c.scratch_cap)
    (hnp : np.toNat ≤ 512) (hnn : nn.toNat ≤ 512)
    (hp : ∀ i < np.toNat, let w := s.scratch.scratch_buf[i]?.getD 0#32;
      (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars)
    (hn : ∀ j < nn.toNat, let w := s.scratch.scratch_buf[512 + j]?.getD 0#32;
      (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) lm' scr' m',
      let s' : FullState :=
        { s with core := { s.core with lit_mark := lm' }
                 scratch := { s.scratch with scratch_buf := scr' } }
      FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1058 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    fullBveFindEquivM7Spec (h, np, nn, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hsc, hnp, hnn, hp, hn, hm, hQ⟩

theorem fullBveFindEquivM7Spec_elim {a m Q X} (h : fullBveFindEquivM7Spec a m Q X) :
    let (hp, np, nn, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1088 ≤ c.scratch_cap ∧
      np.toNat ≤ 512 ∧ nn.toNat ≤ 512 ∧
      (∀ i < np.toNat, let w := s.scratch.scratch_buf[i]?.getD 0#32;
        (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars) ∧
      (∀ j < nn.toNat, let w := s.scratch.scratch_buf[512 + j]?.getD 0#32;
        (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) lm' scr' m',
        let s' : FullState :=
          { s with core := { s.core with lit_mark := lm' }
                   scratch := { s.scratch with scratch_buf := scr' } }
        FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 1024 ∨ 1058 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨hp, np, nn, ⟨⟩⟩; exact h

/-- Contract for `full_bve_find_and_m7`. -/
def fullBveFindAndM7Spec : Spec [i64, i32, i32, i32] [.bool] :=
  fun (h, lit, lit_n, opp_n, ()) m Q _ =>
    let lit_off := (lit &&& 1#32) <<< 9
    let opp_off := 512#32 - lit_off
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1088 ≤ c.scratch_cap ∧
      lit.toNat < 2 * s.core.cur_vars ∧ lit_n.toNat ≤ 512 ∧ opp_n.toNat ≤ 512 ∧
      (∀ i < lit_n.toNat, FullBveEntryOkW F_cur s lit.toNat
        (s.scratch.scratch_buf[lit_off.toNat + i]?.getD 0#32)) ∧
      (∀ j < opp_n.toNat, FullBveEntryOkW F_cur s (lit.toNat ^^^ 1)
        (s.scratch.scratch_buf[opp_off.toNat + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) lm' scr' m',
        let s' : FullState :=
          { s with core := { s.core with lit_mark := lm' }
                   scratch := { s.scratch with scratch_buf := scr' } }
        FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 1024 ∨ 1058 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem fullBveFindAndM7Spec_noExit :
    ∀ xs m Q X, fullBveFindAndM7Spec xs m Q X →
      fullBveFindAndM7Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullBveFindAndM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {lit lit_n opp_n : BitVec 32}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (hsc : 1088 ≤ c.scratch_cap)
    (hlit : lit.toNat < 2 * s.core.cur_vars) (hln : lit_n.toNat ≤ 512) (hon : opp_n.toNat ≤ 512)
    (hpl : ∀ i < lit_n.toNat, FullBveEntryOkW F_cur s lit.toNat
      (s.scratch.scratch_buf[((lit &&& 1#32) <<< 9).toNat + i]?.getD 0#32))
    (hnl : ∀ j < opp_n.toNat, FullBveEntryOkW F_cur s (lit.toNat ^^^ 1)
      (s.scratch.scratch_buf[(512#32 - ((lit &&& 1#32) <<< 9)).toNat + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) lm' scr' m',
      let s' : FullState :=
        { s with core := { s.core with lit_mark := lm' }
                 scratch := { s.scratch with scratch_buf := scr' } }
      FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1058 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    fullBveFindAndM7Spec (h, lit, lit_n, opp_n, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hsc, hlit, hln, hon, hpl, hnl, hm, hQ⟩

theorem fullBveFindAndM7Spec_elim {a m Q X} (h : fullBveFindAndM7Spec a m Q X) :
    let (hp, lit, ln, on_, _) := a
    let lo := (lit &&& 1#32) <<< 9
    let oo := 512#32 - lo
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1088 ≤ c.scratch_cap ∧
      lit.toNat < 2 * s.core.cur_vars ∧ ln.toNat ≤ 512 ∧ on_.toNat ≤ 512 ∧
      (∀ i < ln.toNat, FullBveEntryOkW F_cur s lit.toNat
        (s.scratch.scratch_buf[lo.toNat + i]?.getD 0#32)) ∧
      (∀ j < on_.toNat, FullBveEntryOkW F_cur s (lit.toNat ^^^ 1)
        (s.scratch.scratch_buf[oo.toNat + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) lm' scr' m',
        let s' : FullState :=
          { s with core := { s.core with lit_mark := lm' }
                   scratch := { s.scratch with scratch_buf := scr' } }
        FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 1024 ∨ 1058 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨hp, lit, ln, on_, ⟨⟩⟩; exact h

/-- Contract for `full_bve_match_tern_m7`. -/
def fullBveMatchTernM7Spec : Spec [i64, i32, i32, i32, i32, i32] [i32] :=
  fun (h, nl, _x, _y, n_off, nn, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1066 ≤ c.scratch_cap ∧
      n_off.toNat + nn.toNat ≤ 1024 ∧ nn.toNat ≤ 512 ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s nl.toNat
        (s.scratch.scratch_buf[n_off.toNat + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 32) scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 1058 ∨ 1059 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (r = 0xFFFFFFFF#32 ∨ (r &&& 0x7FFFFFFF#32).toNat < nn.toNat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

theorem fullBveMatchTernM7Spec_noExit :
    ∀ xs m Q X, fullBveMatchTernM7Spec xs m Q X →
      fullBveMatchTernM7Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullBveMatchTernM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {nl x y n_off nn : BitVec 32}
    {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (hsc : 1066 ≤ c.scratch_cap)
    (hnoff : n_off.toNat + nn.toNat ≤ 1024) (hnn : nn.toNat ≤ 512)
    (hn : ∀ j < nn.toNat, FullBveEntryOkW F_cur s nl.toNat
      (s.scratch.scratch_buf[n_off.toNat + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (r : BitVec 32) scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1058 ∨ 1059 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (r = 0xFFFFFFFF#32 ∨ (r &&& 0x7FFFFFFF#32).toNat < nn.toNat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    fullBveMatchTernM7Spec (h, nl, x, y, n_off, nn, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hsc, hnoff, hnn, hn, hm, hQ⟩

theorem fullBveMatchTernM7Spec_elim {a m Q X} (h : fullBveMatchTernM7Spec a m Q X) :
    let (hp, nl, _x, _y, n_off, nn, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1066 ≤ c.scratch_cap ∧
      n_off.toNat + nn.toNat ≤ 1024 ∧ nn.toNat ≤ 512 ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s nl.toNat
        (s.scratch.scratch_buf[n_off.toNat + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 32) scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 1058 ∨ 1059 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (r = 0xFFFFFFFF#32 ∨ (r &&& 0x7FFFFFFF#32).toNat < nn.toNat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m' := by
  rcases a with ⟨hp, nl, _x, _y, n_off, nn, ⟨⟩⟩; exact h

/-- Contract for `full_bve_find_ite_side_m7`. -/
def fullBveFindIteSideM7Spec : Spec [i64, i32, i32, i32, .bool] [.bool] :=
  fun (h, v, np, nn, _neg, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1066 ≤ c.scratch_cap ∧
      v.toNat < s.core.cur_vars ∧ np.toNat ≤ 512 ∧ nn.toNat ≤ 512 ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
        (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
        (s.scratch.scratch_buf[512 + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem fullBveFindIteSideM7Spec_noExit :
    ∀ xs m Q X, fullBveFindIteSideM7Spec xs m Q X →
      fullBveFindIteSideM7Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullBveFindIteSideM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {v np nn : BitVec 32} {neg : Bool}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (hsc : 1066 ≤ c.scratch_cap)
    (hv : v.toNat < s.core.cur_vars) (hnp : np.toNat ≤ 512) (hnn : nn.toNat ≤ 512)
    (hp : ∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32))
    (hn : ∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[512 + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    fullBveFindIteSideM7Spec (h, v, np, nn, neg, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hsc, hv, hnp, hnn, hp, hn, hm, hQ⟩

theorem fullBveFindIteSideM7Spec_elim {a m Q X} (h : fullBveFindIteSideM7Spec a m Q X) :
    let (hp, v, np, nn, _neg, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1066 ≤ c.scratch_cap ∧
      v.toNat < s.core.cur_vars ∧ np.toNat ≤ 512 ∧ nn.toNat ≤ 512 ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
        (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
        (s.scratch.scratch_buf[512 + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨hp, v, np, nn, _neg, ⟨⟩⟩; exact h

/-- Contract for `full_bve_find_ite_m7`. -/
def fullBveFindIteM7Spec : Spec [i64, i32, i32, i32] [.bool] := fun (h, v, np, nn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1066 ≤ c.scratch_cap ∧
    v.toNat < s.core.cur_vars ∧ np.toNat ≤ 512 ∧ nn.toNat ≤ 512 ∧
    (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
    (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[512 + j]?.getD 0#32)) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem fullBveFindIteM7Spec_noExit :
    ∀ xs m Q X, fullBveFindIteM7Spec xs m Q X →
      fullBveFindIteM7Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullBveFindIteM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {v np nn : BitVec 32}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (hsc : 1066 ≤ c.scratch_cap)
    (hv : v.toNat < s.core.cur_vars) (hnp : np.toNat ≤ 512) (hnn : nn.toNat ≤ 512)
    (hp : ∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32))
    (hn : ∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[512 + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    fullBveFindIteM7Spec (h, v, np, nn, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hsc, hv, hnp, hnn, hp, hn, hm, hQ⟩

theorem fullBveFindIteM7Spec_elim {a m Q X} (h : fullBveFindIteM7Spec a m Q X) :
    let (hp, v, np, nn, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1066 ≤ c.scratch_cap ∧
      v.toNat < s.core.cur_vars ∧ np.toNat ≤ 512 ∧ nn.toNat ≤ 512 ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
        (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
        (s.scratch.scratch_buf[512 + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 1024 ∨ 1066 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨hp, v, np, nn, ⟨⟩⟩; exact h

/-- Contract for `full_bve_xor_pat_m7` (read-only; permits temporary non-zero `lit_mark`). -/
def fullBveXorPatM7Spec : Spec [i64, i32, i32, i32] [i32] :=
  fun (h, _v_lit, cr, k, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      cr.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cr.toNat = false ∧
      1 ≤ k.toNat ∧ k.toNat ≤ 4 ∧ (FullMem c s ⋆ R) m ∧
      ∀ pat : BitVec 32, (pat = 0xFFFFFFFF#32 ∨ pat.toNat < 16) → Q (pat, ()) m

theorem fullBveXorPatM7Spec_noExit :
    ∀ xs m Q X, fullBveXorPatM7Spec xs m Q X →
      fullBveXorPatM7Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullBveXorPatM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {v_lit cr k : BitVec 32}
    {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (href : cr.toNat ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cr.toNat = false)
    (hk1 : 1 ≤ k.toNat) (hk4 : k.toNat ≤ 4) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ pat : BitVec 32, (pat = 0xFFFFFFFF#32 ∨ pat.toNat < 16) → Q (pat, ()) m) :
    fullBveXorPatM7Spec (h, v_lit, cr, k, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hlen, hw, href, hng, hk1, hk4, hm, hQ⟩

theorem fullBveXorPatM7Spec_elim {a m Q X} (h : fullBveXorPatM7Spec a m Q X) :
    let (hp, _vl, cr, k, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      cr.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cr.toNat = false ∧
      1 ≤ k.toNat ∧ k.toNat ≤ 4 ∧ (FullMem c s ⋆ R) m ∧
      ∀ pat : BitVec 32, (pat = 0xFFFFFFFF#32 ∨ pat.toNat < 16) → Q (pat, ()) m := by
  rcases a with ⟨hp, _vl, cr, k, ⟨⟩⟩; exact h

/-- Contract for `full_bve_find_xor_m7`. -/
def fullBveFindXorM7Spec : Spec [i64, i32, i32, i32] [.bool] := fun (h, v, np, nn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1088 ≤ c.scratch_cap ∧
    v.toNat < s.core.cur_vars ∧ np.toNat ≤ 512 ∧ nn.toNat ≤ 512 ∧
    (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
    (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[512 + j]?.getD 0#32)) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) lm' scr' m',
      let s' : FullState :=
        { s with core := { s.core with lit_mark := lm' }
                 scratch := { s.scratch with scratch_buf := scr' } }
      FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1096 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem fullBveFindXorM7Spec_noExit :
    ∀ xs m Q X, fullBveFindXorM7Spec xs m Q X →
      fullBveFindXorM7Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullBveFindXorM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {v np nn : BitVec 32}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (hsc : 1088 ≤ c.scratch_cap)
    (hv : v.toNat < s.core.cur_vars) (hnp : np.toNat ≤ 512) (hnn : nn.toNat ≤ 512)
    (hp : ∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32))
    (hn : ∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[512 + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) lm' scr' m',
      let s' : FullState :=
        { s with core := { s.core with lit_mark := lm' }
                 scratch := { s.scratch with scratch_buf := scr' } }
      FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 1024 ∨ 1096 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    fullBveFindXorM7Spec (h, v, np, nn, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hsc, hv, hnp, hnn, hp, hn, hm, hQ⟩

theorem fullBveFindXorM7Spec_elim {a m Q X} (h : fullBveFindXorM7Spec a m Q X) :
    let (hp, v, np, nn, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 1088 ≤ c.scratch_cap ∧
      v.toNat < s.core.cur_vars ∧ np.toNat ≤ 512 ∧ nn.toNat ≤ 512 ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
        (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
        (s.scratch.scratch_buf[512 + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) lm' scr' m',
        let s' : FullState :=
          { s with core := { s.core with lit_mark := lm' }
                   scratch := { s.scratch with scratch_buf := scr' } }
        FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 1024 ∨ 1096 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨hp, v, np, nn, ⟨⟩⟩; exact h

/-- Contract for `full_bve_gates_m7` (and `full_bve_def_k6_m7`). -/
def fullBveGatesM7Spec : Spec [i64, i32, i32, i32] [] := fun (h, v, np, nn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧ 1088 ≤ c.scratch_cap ∧
    v.toNat < s.core.cur_vars ∧ np.toNat ≤ 512 ∧ nn.toNat ≤ 512 ∧
    (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
    (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[512 + j]?.getD 0#32)) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ i < np.toNat, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
      (∀ j < nn.toNat, s'.scratch.scratch_buf[512 + j]? = s.scratch.scratch_buf[512 + j]?) →
      (FullMem c s' ⋆ R) m' → Q () m'

theorem fullBveGatesM7Spec_noExit :
    ∀ xs m Q X, fullBveGatesM7Spec xs m Q X →
      fullBveGatesM7Spec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem fullBveGatesM7Spec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {v np nn : BitVec 32}
    {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (htmk : TmkZero s)
    (hsc : 1088 ≤ c.scratch_cap) (hv : v.toNat < s.core.cur_vars)
    (hnp : np.toNat ≤ 512) (hnn : nn.toNat ≤ 512)
    (hp : ∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32))
    (hn : ∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[512 + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ s' m',
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ i < np.toNat, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
      (∀ j < nn.toNat, s'.scratch.scratch_buf[512 + j]? = s.scratch.scratch_buf[512 + j]?) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    fullBveGatesM7Spec (h, v, np, nn, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, htmk, hsc, hv, hnp, hnn, hp, hn, hm, hQ⟩

theorem fullBveGatesM7Spec_elim {a m Q X} (h : fullBveGatesM7Spec a m Q X) :
    let (hp, v, np, nn, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧ 1088 ≤ c.scratch_cap ∧
      v.toNat < s.core.cur_vars ∧ np.toNat ≤ 512 ∧ nn.toNat ≤ 512 ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
        (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
        (s.scratch.scratch_buf[512 + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ s' m',
        FullDenseInvW c F0 F_cur s' → TmkZero s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
        s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (∀ i < np.toNat, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
        (∀ j < nn.toNat, s'.scratch.scratch_buf[512 + j]? = s.scratch.scratch_buf[512 + j]?) →
        (FullMem c s' ⋆ R) m' → Q () m' := by
  rcases a with ⟨hp, v, np, nn, ⟨⟩⟩; exact h

end LeanQbe.T.Examples.Kissat.FullM7BveGates
