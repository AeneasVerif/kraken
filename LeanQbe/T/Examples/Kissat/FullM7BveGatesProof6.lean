module

public import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof6a
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Wave-4E (`FullM7BveGates`) Proofs — Part 6 (`def_k6`, `bve_gates`)

M1-clean proof module (`public section`, `0` `@[expose]`, `0` `import all`, `private` helpers):
- `full_bve_def_k6_m7_wp`: certifies `fullBveGatesM7Spec` for `full_bve_def_k6_m7`,
  parameterized over `(hWatch, hSolve, hCore)`.
- `full_bve_gates_m7_wp`: certifies `fullBveGatesM7Spec` for `full_bve_gates_m7`,
  parameterized over `(hEquiv, hAnd, hIte, hXor, hDefK6)`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7BveGates

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open Kraken.Bedrock2.Test

open scoped FullArenaTactics
open scoped K6Tactics P6Tactics

local macro "m7_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. `full_bve_def_k6_m7_wp` -/

/-- Parametric `Func.wp` proof for `full_bve_def_k6_m7`, certifying `fullBveGatesM7Spec`. -/
theorem full_bve_def_k6_m7_wp (Γ : Env)
    (hWatch : ∀ a m Q X, fullK6WatchM7Spec a m Q X →
      Γ "full_k6_watch_m7" [i64, i32, i32, i32, i32] [] a m Q X)
    (hSolve : ∀ a m Q X, fullK6SolveM7Spec a m Q X →
      Γ "full_k6_solve_m7" [i64, i64, i32] [i64] a m Q X)
    (hCore : ∀ a m Q X, fullK6CoreM7Spec a m Q X →
      Γ "full_k6_core_m7" [i64] [] a m Q X) :
    ∀ a m Q X, fullBveGatesM7Spec a m Q X →
      Func.wp Γ full_bve_def_k6_m7_body a m Q X := by
  rintro ⟨h, v, np, nn, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hdw0, htmk0, hsc1088, hv_lt, hnp512, hnn512,
    hp_ok, hn_ok, hm0, hQ⟩ := fullBveGatesM7Spec_elim hSpec
  have hmx := c.hmaxv; have hsc := c.hscr; unfold dimacsBound at hmx hsc
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hplnl := m7_p6_pl_nl_eq v (by omega)
  let acap_n : Nat := c.scratch_cap - 4008
  unfold Func.wp full_bve_def_k6_m7_body
  -- Guard: `scratch_cap < 8192 || np == 0 || nn == 0 || np + nn < 3 || np + nn > 128`
  c0_hsplit
  · c0_hsteps!
    exact hQ s0 m0 hdw0 htmk0 rfl rfl rfl (Nat.le_refl _) (fun _ _ => rfl) (fun _ _ => rfl) hm0
  · have hsc8192 : 8192 ≤ c.scratch_cap := by
      simp only [bv_c0, BitVec.reduceToNat] at hc; omega
    clear hc
    c0_hsplit
    · c0_hsteps!
      exact hQ s0 m0 hdw0 htmk0 rfl rfl rfl (Nat.le_refl _) (fun _ _ => rfl) (fun _ _ => rfl) hm0
    · have hnp_pos : 0 < np.toNat := by
        have hne : np ≠ 0#32 := hc
        exact Nat.pos_of_ne_zero fun hz => hne (BitVec.eq_of_toNat_eq hz)
      clear hc
      c0_hsplit
      · c0_hsteps!
        exact hQ s0 m0 hdw0 htmk0 rfl rfl rfl (Nat.le_refl _) (fun _ _ => rfl) (fun _ _ => rfl)
          hm0
      · have hnn_pos : 0 < nn.toNat := by
          have hne : nn ≠ 0#32 := hc
          exact Nat.pos_of_ne_zero fun hz => hne (BitVec.eq_of_toNat_eq hz)
        clear hc
        c0_hsplit
        · c0_hsteps!
          exact hQ s0 m0 hdw0 htmk0 rfl rfl rfl (Nat.le_refl _) (fun _ _ => rfl) (fun _ _ => rfl)
            hm0
        · have hsum_ge3 : 3 ≤ np.toNat + nn.toNat := by
            have hnlt : ¬ (np + nn).toNat < 3 := by simpa using hc
            rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)] at hnlt; omega
          clear hc
          c0_hsplit
          · c0_hsteps!
            exact hQ s0 m0 hdw0 htmk0 rfl rfl rfl (Nat.le_refl _) (fun _ _ => rfl)
              (fun _ _ => rfl) hm0
          · have hsum_le128 : np.toNat + nn.toNat ≤ 128 := by
              rw [Nat.mod_eq_of_lt (by omega)] at hc
              simp only [bv_c0, BitVec.reduceToNat] at hc; omega
            clear hc
            have hnp128 : np.toNat ≤ 128 := by omega
            have hnn128 : nn.toNat ≤ 128 := by omega
            have hacap_eq : ((BitVec.ofNat 64 c.scratch_cap - 4008#64).truncate 32) =
                BitVec.ofNat 32 acap_n := by
              apply BitVec.eq_of_toNat_eq
              dsimp only [acap_n]
              rw [BitVec.toNat_setWidth, BitVec.toNat_sub]
              simp only [BitVec.toNat_ofNat]
              omega
            have hacap_n_eq : (BitVec.ofNat 32 acap_n).toNat = acap_n := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp only [acap_n]; omega)]
            c0_hsteps_nogrp
            -- Join on `max_csz = (h->max_vars < 100ULL) ? (u32)h->max_vars : 100u`
            refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun mc => (mc, ()))
              (fun mc => 1 ≤ mc.toNat ∧ mc.toNat ≤ 100 ∧ mc.toNat ≤ c.max_vars) ?_ ?_
            · intro Jmc mc ⟨hmc_lo, hmc_hi, hmc_cv⟩
              -- Outer loop: `side < 2 && !abort_def && trivial_eid == 0xFFFFFFFF`
              c0_hsteps_nogrp
              refine wp_loop_group (ts := [i32, i32, i32, i32, i32, .bool, i32])
                (fun rem_s (nv_s, nc_s, alen_s, nunits_s, teid_s, ab_s, side_s, ()) ms =>
                  ∃ (exp_s tmk_s tmp_s scr_s : List (BitVec 32)),
                    let ss : FullState :=
                      { s0 with
                        core := { s0.core with tmp := tmp_s }
                        scratch :=
                          { s0.scratch with
                            wsort := exp_s, tarjan_mark := tmk_s, scratch_buf := scr_s } }
                    exp_s.length = 2 * c.max_vars ∧ tmk_s.length = 2 * c.max_vars ∧
                    tmp_s.length = c.max_vars ∧ scr_s.length = c.scratch_cap ∧
                    side_s.toNat ≤ 2 ∧
                    rem_s = (if !ab_s && teid_s == 0xFFFFFFFF#32 then 2 - side_s.toNat else 0) ∧
                    nv_s.toNat ≤ 64 ∧ nv_s.toNat ≤ 2 * s0.core.cur_vars ∧
                    nc_s.toNat ≤ 128 ∧ nunits_s.toNat ≤ nc_s.toNat ∧
                    alen_s.toNat ≤ acap_n ∧
                    (∀ k < 1096, scr_s[k]? = s0.scratch.scratch_buf[k]?) ∧
                    (∀ k < nv_s.toNat, (exp_s[k]?.getD 0#32).toNat < s0.core.cur_vars) ∧
                    (∀ u < s0.core.cur_vars, tmk_s[u]?.getD 0#32 ≠ 0#32 →
                      1 ≤ (tmk_s[u]?.getD 0#32).toNat ∧
                      (tmk_s[u]?.getD 0#32).toNat ≤ nv_s.toNat ∧
                      ∃ k < nv_s.toNat, (exp_s[k]?.getD 0#32).toNat = u) ∧
                    (∀ cid < nc_s.toNat,
                      (scr_s[1096 + 1888 + cid]?.getD 0#32).toNat +
                        ((scr_s[1096 + 2144 + cid]?.getD 0#32) &&& 0xFFFF#32).toNat ≤
                          alen_s.toNat ∧
                      ((scr_s[1096 + 2144 + cid]?.getD 0#32) &&& 0x40000000#32) = 0#32) ∧
                    (teid_s ≠ 0xFFFFFFFF#32 → (teid_s &&& 0x3FF#32).toNat < 512) ∧
                    (FullMem c ss ⋆ R) ms)
                ?_ ?_
              · rintro Ls rem_s ⟨nv_s, nc_s, alen_s, nunits_s, teid_s, ab_s, side_s, ⟨⟩⟩ ms hLs
                  ⟨exp_s, tmk_s, tmp_s, scr_s, hexpl, htmkl, htmpl, hscrl,
                   hside_le, rfl, hnv64, hnvcv, hnc128, hnu_le, hal_le, hscr_pre,
                   hexp_bnd, htmk_inv, hcls_ok, hteid_ok, hms⟩
                let ss : FullState :=
                  { s0 with
                    core := { s0.core with tmp := tmp_s }
                    scratch :=
                      { s0.scratch with
                        wsort := exp_s, tarjan_mark := tmk_s, scratch_buf := scr_s } }
                c0_hsteps_nogrp
                refine wp_join0
                  (fun me => ∃ tmk_e scr_e : List (BitVec 32),
                    let se : FullState :=
                      { s0 with
                        core := { s0.core with tmp := tmp_s }
                        scratch :=
                          { s0.scratch with
                            wsort := exp_s, tarjan_mark := tmk_e, scratch_buf := scr_e } }
                    tmk_e.length = 2 * c.max_vars ∧ scr_e.length = c.scratch_cap ∧
                    (∀ u < s0.core.cur_vars, tmk_e[u]?.getD 0#32 ≠ 0#32 →
                      ∃ k < nv_s.toNat, (exp_s[k]?.getD 0#32).toNat = u) ∧
                    (∀ k < 1096, scr_e[k]? = s0.scratch.scratch_buf[k]?) ∧
                    (∀ cid < nc_s.toNat,
                      (scr_e[1096 + 1888 + cid]?.getD 0#32).toNat +
                        ((scr_e[1096 + 2144 + cid]?.getD 0#32) &&& 0xFFFF#32).toNat ≤
                          alen_s.toNat ∧
                      ((scr_e[1096 + 2144 + cid]?.getD 0#32) &&& 0x40000000#32) = 0#32) ∧
                    (FullMem c se ⋆ R) me)
                  ?_ ?_
                · intro _ me ⟨tmk_e, scr_e, htmke_l, hscre_l, htmke_inv, hscre_pre, hcls_e, hme⟩
                  -- Clear `tmk` loop: `ci < nv_s`
                  c0_hsteps_nogrp
                  refine wp_loop_group (ts := [i32])
                    (fun rem_c (ci, ()) mc => ∃ tmk_c : List (BitVec 32),
                      let sc' : FullState :=
                        { s0 with
                          core := { s0.core with tmp := tmp_s }
                          scratch :=
                            { s0.scratch with
                              wsort := exp_s, tarjan_mark := tmk_c, scratch_buf := scr_e } }
                      tmk_c.length = 2 * c.max_vars ∧ ci.toNat ≤ nv_s.toNat ∧
                      rem_c = nv_s.toNat - ci.toNat ∧
                      (∀ u < s0.core.cur_vars, tmk_c[u]?.getD 0#32 ≠ 0#32 →
                        ∃ k, ci.toNat ≤ k ∧ k < nv_s.toNat ∧ (exp_s[k]?.getD 0#32).toNat = u) ∧
                      (FullMem c sc' ⋆ R) mc)
                    ?_ ?_
                  · rintro Lc rem_c ⟨ci, ⟨⟩⟩ mc hLc ⟨tmk_c, htmkc_l, hci_le, rfl, hrem_c, hmc⟩
                    c0_hsplit
                    · have hci_lt : ci.toNat < nv_s.toNat := hc
                      have hci_ws : (ci.setWidth 64).toNat < exp_s.length := by
                        rw [hexpl, m6_zext32_toNat]; omega
                      let lv_c := exp_s[(ci.setWidth 64).toNat]'hci_ws
                      have hlv_eq : (exp_s[ci.toNat]?.getD 0#32).toNat = lv_c.toNat := by
                        rw [List.getElem?_eq_getElem (by rw [hexpl]; omega), Option.getD_some]
                        exact congrArg BitVec.toNat
                          (m6_getElem_congr (m6_zext32_toNat ci).symm _ _)
                      have hlv_cv : lv_c.toNat < s0.core.cur_vars := by
                        rw [← hlv_eq]; exact hexp_bnd ci.toNat hci_lt
                      have hlv_tmk : (lv_c.setWidth 64).toNat < tmk_c.length := by
                        rw [htmkc_l, m6_zext32_toNat]; omega
                      have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by
                        rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                          Nat.mod_eq_of_lt (by omega)]
                      c0_hsteps!
                      refine hLc (nv_s.toNat - (ci + 1#32).toNat) (ci + 1#32, ()) _ (by omega)
                        ⟨tmk_c.set (lv_c.setWidth 64).toNat 0#32, by simp [htmkc_l], by omega, rfl,
                         ?_, hm⟩
                      rw [hci1, m6_zext32_toNat]
                      exact m7_p6_tmk_clear_step hci_lt hlv_eq (by rw [htmkc_l]; omega) hrem_c
                    · have hci_eq : ci.toNat = nv_s.toNat := by omega
                      have hclr_c : ∀ u < s0.core.cur_vars, tmk_c[u]?.getD 0#32 = 0#32 :=
                        m7_p6_tmk_clear_done (by simpa [hci_eq] using hrem_c)
                      let s_clr : FullState :=
                        { s0 with
                          core := { s0.core with tmp := tmp_s }
                          scratch :=
                            { s0.scratch with
                              wsort := exp_s, tarjan_mark := tmk_c, scratch_buf := scr_e } }
                      have hdw_clr := m7_p6_fullDenseInvW_def hdw0 htmpl hexpl htmkc_l hscre_l
                      have htmk_clr : TmkZero s_clr := fun u hu => hclr_c u hu
                      c0_hsplit
                      · have hte_ne : teid_s ≠ 0xFFFFFFFF#32 := hc
                        have hidx_lt : (teid_s &&& 0x3FF#32).toNat < 512 := hteid_ok hte_ne
                        have hwidx_bd := m7_p6_trivial_widx teid_s hidx_lt
                        let idx_t := teid_s &&& 0x3FF#32
                        have hidx_nat : (idx_t >>> (5 : Nat)).toNat < 16 := by
                          dsimp only [idx_t]
                          rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                            show 2 ^ 5 = 32 from rfl]
                          omega
                        have hm_scr : (P6Scr c.scratch_cap c.pScratchBuf scr_e ⋆
                            (m7_p6_fullWithoutScr c s_clr ⋆ R)) mc :=
                          m7_p6_scrBuf_split hsc8192 hscre_l hmc
                        c0_hsteps_nogrp
                        refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun m => (m, ()))
                          (fun mbase => mbase = 1024#32 ∨ mbase = 1040#32) ?_ ?_
                        · intro _ mbase hmbase
                          have hmbase_bd2 : 1024 ≤ (mbase + (idx_t >>> (5 : Nat))).toNat ∧
                              (mbase + (idx_t >>> (5 : Nat))).toNat < 1056 := by
                            rcases hmbase with rfl | rfl
                            · rw [BitVec.toNat_add,
                                show (1024#32 : BitVec 32).toNat = 1024 from rfl,
                                Nat.mod_eq_of_lt (by omega)]; omega
                            · rw [BitVec.toNat_add,
                                show (1040#32 : BitVec 32).toNat = 1040 from rfl,
                                Nat.mod_eq_of_lt (by omega)]; omega
                          have hmbase_ge := hmbase_bd2.1
                          have hmbase_lt := hmbase_bd2.2
                          have hmbase_bd : ((mbase + (idx_t >>> (5 : Nat))).setWidth 64).toNat <
                              8192 := by
                            rw [m6_zext32_toNat]; omega
                          c0_hsteps!
                          let scr_f := ((scr_e.set
                            (mbase + (idx_t >>> (5 : Nat))).toNat
                            (1#32 <<< ((idx_t &&& 31#32).toNat % 32))).set 1056 1#32).set 1057 1#32
                          have hscrf_l : scr_f.length = c.scratch_cap := by simp [scr_f, hscre_l]
                          have hm' := m7_p6_scrBuf_unsplit hm
                          rw [m6_zext32_toNat,
                            show (BitVec.ofNat 64 1056).toNat = 1056 from rfl,
                            show (BitVec.ofNat 64 1057).toNat = 1057 from rfl] at hm'
                          refine hQ _ _ (m7_p6_fullDenseInvW_def hdw0 htmpl hexpl htmkc_l hscrf_l)
                            htmk_clr rfl rfl rfl (Nat.le_refl _) (fun k hk => ?_)
                            (fun k hk => ?_)
                            (m7_p6_fullMem_subst hm' (by dsimp only [s_clr])
                              (by dsimp only [s_clr, idx_t, scr_f]; rfl))
                          · simp only [scr_f]
                            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                              List.getElem?_set_ne (by omega)]
                            exact hscre_pre k (by omega)
                          · simp only [scr_f]
                            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                              List.getElem?_set_ne (by omega)]
                            exact hscre_pre (512 + k) (by omega)
                        · intro _ hJm; c0_hsplit
                          · c0_hsteps!; exact hJm 1024#32 (Or.inl rfl)
                          · c0_hsteps!; exact hJm 1040#32 (Or.inr rfl)
                      · clear hc
                        c0_hsplit
                        · c0_hsteps!
                          exact hQ _ mc hdw_clr htmk_clr rfl rfl rfl (Nat.le_refl _)
                            (fun k hk => hscre_pre k (by omega))
                            (fun k hk => hscre_pre (512 + k) (by omega)) hmc
                        · have hab_f : ab_s = false := by
                            cases ab_s with
                            | false => rfl
                            | true => exact Bool.noConfusion hc
                          clear hc
                          c0_hsplit
                          · c0_hsteps!
                            exact hQ _ mc hdw_clr htmk_clr rfl rfl rfl (Nat.le_refl _)
                              (fun k hk => hscre_pre k (by omega))
                              (fun k hk => hscre_pre (512 + k) (by omega)) hmc
                          · have hnv_pos : 0 < nv_s.toNat :=
                              Nat.pos_of_ne_zero fun hz => hc (BitVec.eq_of_toNat_eq hz)
                            clear hc
                            c0_hsplit
                            · c0_hsteps!
                              exact hQ _ mc hdw_clr htmk_clr rfl rfl rfl (Nat.le_refl _)
                                (fun k hk => hscre_pre k (by omega))
                                (fun k hk => hscre_pre (512 + k) (by omega)) hmc
                            · have hnc_ge2 : 2 ≤ nc_s.toNat := by
                                have hnlt : ¬ nc_s.toNat < 2 := by simpa using hc
                                omega
                              clear hc
                              refine m7_p6_k6_init_solve_wp Γ Q X c s0 s_clr R _
                                nv_s nc_s alen_s _ nunits_s scr_e mc _
                                rfl hsc hsc8192 hscre_l rfl hnv_pos hnv64 hnc_ge2 hnc128 hal_le
                                hacap_eq hscre_pre hcls_e hmc fun scr_pre kb_w0 scr2 m_sp hsc2_l
                                  hpre_l hpre_take hpre2 hkbw0_eq hkbw0_ok hkbw0_l hs2_1 hs2_2
                                  hm_sp =>
                                m7_p6_k6_watch_solve_wp Γ hWatch hSolve hCore c s0 s_clr
                                  R scr_pre kb_w0 scr2 nc_s m_sp Q X hsc hsc8192 hnc128 rfl
                                  hsc2_l hpre_l hpre_take hpre2 hkbw0_eq hkbw0_ok hkbw0_l hs2_1
                                  hs2_2 hm_sp fun fl' scr' m' hfl' hsc' hpre' hm' =>
                                  let sf : FullState :=
                                    { s_clr with
                                      core := { s_clr.core with fuel := fl' }
                                      scratch := { s_clr.scratch with scratch_buf := scr' } }
                                  hQ sf m' (m7_p6_fullDenseInvW_fuel
                                    (m7_p6_fullDenseInvW_def hdw0 htmpl hexpl htmkc_l hsc') fl')
                                    htmk_clr rfl rfl rfl hfl'
                                    (fun k hk => hpre' k (by omega))
                                    (fun k hk => hpre' (512 + k) (by omega)) hm'
                  · intro Lc hLc; c0_hsteps!
                    exact hLc nv_s.toNat (0#32, ()) me
                      ⟨tmk_e, htmke_l, Nat.zero_le _, rfl,
                       fun u hu hnz => by
                         obtain ⟨k, hk, hwk⟩ := htmke_inv u hu hnz
                         exact ⟨k, Nat.zero_le _, hk, hwk⟩,
                       hme⟩
                · intro Jex hJex
                  -- Outer loop body & `side < 2 && !abort_def && teid == 0xFFFFFFFF`
                  have hdone_ex : Jex () ms :=
                    hJex ms ⟨tmk_s, scr_s, htmkl, hscrl,
                      fun u hu hnz => (htmk_inv u hu hnz).2.2, hscr_pre, hcls_ok, hms⟩
                  c0_hsplit
                  · have hside_lt : side_s.toNat < 2 := hc
                    clear hc
                    c0_hsplit
                    · c0_hsteps!; exact hdone_ex
                    · have hab_f : ab_s = false := by
                        cases ab_s with
                        | false => rfl
                        | true => exact Bool.noConfusion hc
                      clear hc
                      c0_hsplit
                      · have hteid_ff : teid_s = 0xFFFFFFFF#32 := hc
                        clear hc
                        have hside1 : (side_s + 1#32).toNat = side_s.toNat + 1 := by
                          rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                            Nat.mod_eq_of_lt (by omega)]
                        c0_hsteps_nogrp
                        refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
                          (fun c => (c, ()))
                          (fun cnt =>
                            (side_s = 0#32 → cnt = np) ∧ (side_s ≠ 0#32 → cnt = nn))
                          ?_ ?_
                        · intro _ cnt hcnt_eq
                          c0_hsteps_nogrp
                          refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
                            (fun o => (o, ()))
                            (fun off_s =>
                              (side_s = 0#32 → off_s = 0#32) ∧ (side_s ≠ 0#32 → off_s = 512#32))
                            ?_ ?_
                          · intro _ off_s hoff_eq
                            c0_hsteps_nogrp
                            refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
                              (fun e => (e, ()))
                              (fun except =>
                                (side_s = 0#32 → except = v <<< (1 : Nat)) ∧
                                (side_s ≠ 0#32 → except = ((v <<< (1 : Nat)) ||| 1#32)))
                              ?_ ?_
                            · intro _ except hexc_eq
                              have hcnt128 : cnt.toNat ≤ 128 := by
                                rcases Nat.lt_succ_iff_lt_or_eq.mp hside_lt with hs0 | hs1
                                · rw [hcnt_eq.1 (BitVec.eq_of_toNat_eq
                                    (Nat.lt_one_iff.mp hs0))]; exact hnp128
                                · rw [hcnt_eq.2 (fun h => by
                                    have := congrArg BitVec.toNat h
                                    simp only [BitVec.toNat_zero] at this; omega)]
                                  exact hnn128
                              have hoff_bd : off_s.toNat + cnt.toNat ≤ 1024 := by
                                rcases Nat.lt_succ_iff_lt_or_eq.mp hside_lt with hs0 | hs1
                                · have hs0b : side_s = 0#32 :=
                                    BitVec.eq_of_toNat_eq (Nat.lt_one_iff.mp hs0)
                                  rw [hoff_eq.1 hs0b, hcnt_eq.1 hs0b,
                                    show (0#32 : BitVec 32).toNat = 0 from rfl]; omega
                                · have hs1ne : side_s ≠ 0#32 := fun h => by
                                    have := congrArg BitVec.toNat h
                                    simp only [BitVec.toNat_zero] at this; omega
                                  rw [hoff_eq.2 hs1ne, hcnt_eq.2 hs1ne,
                                    show (512#32 : BitVec 32).toNat = 512 from rfl]; omega
                              have hexc_lt : except.toNat < 2 * s0.core.cur_vars := by
                                rcases Nat.lt_succ_iff_lt_or_eq.mp hside_lt with hs0 | hs1
                                · rw [hexc_eq.1 (BitVec.eq_of_toNat_eq
                                    (Nat.lt_one_iff.mp hs0)), hplnl.1]; omega
                                · rw [hexc_eq.2 (fun h => by
                                    have := congrArg BitVec.toNat h
                                    simp only [BitVec.toNat_zero] at this; omega), hplnl.2]
                                  omega
                              have hent : ∀ j < cnt.toNat, FullBveEntryOkW F_cur s0 except.toNat
                                  (s0.scratch.scratch_buf[off_s.toNat + j]?.getD 0#32) := by
                                intro j hj
                                rcases Nat.lt_succ_iff_lt_or_eq.mp hside_lt with hs0 | hs1
                                · have hs0b : side_s = 0#32 :=
                                    BitVec.eq_of_toNat_eq (Nat.lt_one_iff.mp hs0)
                                  rw [hcnt_eq.1 hs0b] at hj
                                  rw [hoff_eq.1 hs0b, hexc_eq.1 hs0b, hplnl.1,
                                    show (0#32 : BitVec 32).toNat = 0 from rfl, Nat.zero_add]
                                  exact hp_ok j hj
                                · have hs1ne : side_s ≠ 0#32 := fun h => by
                                    have := congrArg BitVec.toNat h
                                    simp only [BitVec.toNat_zero] at this; omega
                                  rw [hcnt_eq.2 hs1ne] at hj
                                  rw [hoff_eq.2 hs1ne, hexc_eq.2 hs1ne, hplnl.2,
                                    show (512#32 : BitVec 32).toNat = 512 from rfl]
                                  exact hn_ok j hj
                              c0_hsteps_nogrp
                              refine wp_loop_break_group
                                (brkTs := [i32, i32, i32, i32, i32, .bool, i32])
                                (lpTs := [i32, i32, i32, i32, .bool, i32])
                                (fun (nv_b, nc_b, al_b, nu_b, te_b, ab_b, _idx_b, ()) mb =>
                                  ∃ (exp_b tmk_b tmp_b scr_b : List (BitVec 32)),
                                    let sb : FullState :=
                                      { s0 with
                                        core := { s0.core with tmp := tmp_b }
                                        scratch :=
                                          { s0.scratch with
                                            wsort := exp_b, tarjan_mark := tmk_b,
                                            scratch_buf := scr_b } }
                                    exp_b.length = 2 * c.max_vars ∧ tmk_b.length = 2 * c.max_vars ∧
                                    tmp_b.length = c.max_vars ∧ scr_b.length = c.scratch_cap ∧
                                    nv_b.toNat ≤ 64 ∧ nv_b.toNat ≤ 2 * s0.core.cur_vars ∧
                                    nc_b.toNat ≤ 128 ∧ nu_b.toNat ≤ nc_b.toNat ∧
                                    al_b.toNat ≤ acap_n ∧
                                    (∀ k < 1096, scr_b[k]? = s0.scratch.scratch_buf[k]?) ∧
                                    (∀ k < nv_b.toNat,
                                      (exp_b[k]?.getD 0#32).toNat < s0.core.cur_vars) ∧
                                    (∀ u < s0.core.cur_vars, tmk_b[u]?.getD 0#32 ≠ 0#32 →
                                      1 ≤ (tmk_b[u]?.getD 0#32).toNat ∧
                                      (tmk_b[u]?.getD 0#32).toNat ≤ nv_b.toNat ∧
                                      ∃ k < nv_b.toNat, (exp_b[k]?.getD 0#32).toNat = u) ∧
                                    (∀ cid < nc_b.toNat,
                                      (scr_b[1096 + 1888 + cid]?.getD 0#32).toNat +
                                        ((scr_b[1096 + 2144 + cid]?.getD 0#32) &&&
                                          0xFFFF#32).toNat ≤ al_b.toNat ∧
                                      ((scr_b[1096 + 2144 + cid]?.getD 0#32) &&&
                                        0x40000000#32) = 0#32) ∧
                                    (te_b ≠ 0xFFFFFFFF#32 → (te_b &&& 0x3FF#32).toNat < 512) ∧
                                    (FullMem c sb ⋆ R) mb)
                                (fun rem_i (nv_i, nc_i, al_i, nu_i, ab_i, idx, ()) mi =>
                                  ∃ (exp_i tmk_i tmp_i scr_i : List (BitVec 32)),
                                    let si : FullState :=
                                      { s0 with
                                        core := { s0.core with tmp := tmp_i }
                                        scratch :=
                                          { s0.scratch with
                                            wsort := exp_i, tarjan_mark := tmk_i
                                            scratch_buf := scr_i } }
                                    exp_i.length = 2 * c.max_vars ∧ tmk_i.length = 2 * c.max_vars ∧
                                    tmp_i.length = c.max_vars ∧ scr_i.length = c.scratch_cap ∧
                                    idx.toNat ≤ cnt.toNat ∧
                                    rem_i = (if !ab_i then cnt.toNat - idx.toNat else 0) ∧
                                    nv_i.toNat ≤ 64 ∧ nv_i.toNat ≤ 2 * s0.core.cur_vars ∧
                                    nc_i.toNat ≤ 128 ∧ nu_i.toNat ≤ nc_i.toNat ∧
                                    al_i.toNat ≤ acap_n ∧
                                    (∀ k < 1096, scr_i[k]? = s0.scratch.scratch_buf[k]?) ∧
                                    (∀ k < nv_i.toNat,
                                      (exp_i[k]?.getD 0#32).toNat < s0.core.cur_vars) ∧
                                    (∀ u < s0.core.cur_vars, tmk_i[u]?.getD 0#32 ≠ 0#32 →
                                      1 ≤ (tmk_i[u]?.getD 0#32).toNat ∧
                                      (tmk_i[u]?.getD 0#32).toNat ≤ nv_i.toNat ∧
                                      ∃ k < nv_i.toNat, (exp_i[k]?.getD 0#32).toNat = u) ∧
                                    (∀ cid < nc_i.toNat,
                                      (scr_i[1096 + 1888 + cid]?.getD 0#32).toNat +
                                        ((scr_i[1096 + 2144 + cid]?.getD 0#32) &&&
                                          0xFFFF#32).toNat ≤ al_i.toNat ∧
                                      ((scr_i[1096 + 2144 + cid]?.getD 0#32) &&&
                                        0x40000000#32) = 0#32) ∧
                                    (FullMem c si ⋆ R) mi)
                                ?_ ?_ ?_
                              · rintro _ ⟨nv_b, nc_b, al_b, nu_b, te_b, ab_b, _idx_b, ⟨⟩⟩ mb
                                  ⟨exp_b, tmk_b, tmp_b, scr_b, h1, h2, h3, h4, h5, h6, h7, h8, h9,
                                   h10, h11, h12, h13, h14, h15⟩
                                c0_hsteps!
                                refine hLs _ (nv_b, nc_b, al_b, nu_b, te_b, ab_b, side_s + 1#32, ())
                                  mb ?_ ⟨exp_b, tmk_b, tmp_b, scr_b, h1, h2, h3, h4, by omega, rfl,
                                    h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
                                cases ab_b <;> cases hte : (te_b == 0xFFFFFFFF#32) <;>
                                  simp [hside1, hab_f, hteid_ff] <;> omega
                              · rintro Bi Li rem_i ⟨nv_i, nc_i, al_i, nu_i, ab_i, idx, ⟨⟩⟩ mi
                                  hBi hLi ⟨exp_i, tmk_i, tmp_i, scr_i, hexpi, htmki, htmpi, hscri,
                                   hidx_le, rfl, hnv64i, hnvcv_i, hnc128i, hnu_lei, hal_lei,
                                   hscr_prei, hexp_bndi, htmk_invi, hcls_oki, hmi⟩
                                let te_i := teid_s
                                have hteid_oki : te_i ≠ 0xFFFFFFFF#32 →
                                    (te_i &&& 0x3FF#32).toNat < 512 := hteid_ok
                                let si : FullState :=
                                  { s0 with
                                    core := { s0.core with tmp := tmp_i }
                                    scratch :=
                                      { s0.scratch with
                                        wsort := exp_i, tarjan_mark := tmk_i,
                                        scratch_buf := scr_i } }
                                c0_hsplit
                                · have hidx_lt : idx.toNat < cnt.toNat := hc
                                  clear hc
                                  c0_hsplit
                                  · have hab_ti : ab_i = true := hc
                                    rw [hab_ti]
                                    c0_hsteps!
                                    exact hBi (nv_i, nc_i, al_i, nu_i, te_i, true, idx, ()) mi
                                      ⟨exp_i, tmk_i, tmp_i, scr_i, hexpi, htmki, htmpi, hscri,
                                       hnv64i, hnvcv_i, hnc128i, hnu_lei, hal_lei, hscr_prei,
                                       hexp_bndi, htmk_invi, hcls_oki, hteid_oki, hmi⟩
                                  have hab_fi : ab_i = false := by
                                    cases ab_i with
                                    | false => rfl
                                    | true => exact Bool.noConfusion hc
                                  clear hc
                                  have hidx1 : (idx + 1#32).toNat = idx.toNat + 1 := by
                                    rw [BitVec.toNat_add,
                                      show (1#32 : BitVec 32).toNat = 1 from rfl,
                                      Nat.mod_eq_of_lt (by omega)]
                                  have hoff_lt : (off_s + idx).toNat < 1024 := by
                                    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega
                                  have hoff_eq : (off_s + idx).toNat = off_s.toNat + idx.toNat := by
                                    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
                                  have hsc_bd : ((off_s + idx).setWidth 64).toNat <
                                      scr_i.length := by
                                    rw [hscri, m6_zext32_toNat]; omega
                                  let w := scr_i[((off_s + idx).setWidth 64).toNat]'hsc_bd
                                  have hw_eq : s0.scratch.scratch_buf[off_s.toNat + idx.toNat]?.getD
                                      0#32 = w := by
                                    have hget := hscr_prei (off_s.toNat + idx.toNat) (by omega)
                                    rw [List.getElem?_eq_getElem (by rw [hscri]; omega)] at hget
                                    rw [← hget, Option.getD_some]
                                    exact m6_getElem_congr (by rw [m6_zext32_toNat, hoff_eq]) _ _
                                  have hw_ok : FullBveEntryOkW F_cur s0 except.toNat w := by
                                    rw [← hw_eq]; exact hent idx.toNat hidx_lt
                                  have heid :=
                                    m7_p6_eid_bounds hside_lt (by omega : idx.toNat < 128)
                                  let eid := (side_s <<< (10 : Nat)) ||| idx
                                  c0_hsteps_nogrp; c0_hstep; c0_hsplit
                                  · -- Binary occurrence entry `(w & PW_BIN_FLAG) != 0`
                                    have hw_bin : (w &&& 0x80000000#32) ≠ 0#32 := by
                                      simpa [w, m6_zext32_toNat, hoff_eq, BitVec.toNat_add,
                                        Nat.mod_eq_of_lt
                                          (by omega : off_s.toNat + idx.toNat < 2 ^ 32),
                                        Nat.mod_eq_of_lt
                                          (by omega : off_s.toNat + idx.toNat < 2 ^ 64)] using hc
                                    have hl_lt : (w &&& 0x7FFFFFFF#32).toNat <
                                        2 * s0.core.cur_vars :=
                                      m7_p6_entry_bin_bounds hw_ok hw_bin
                                    have hval_bd : ((w &&& 0x7FFFFFFF#32).setWidth 64).toNat <
                                        si.core.vals.length := by
                                      rw [hdw0.1.core_ok.vals_len, m6_zext32_toNat]; omega
                                    c0_hsplit
                                    · -- `lv_val < 0`: `trivial_eid = eid; break;`
                                      c0_hsteps!
                                      rw [hab_fi]
                                      exact hBi (nv_i, nc_i, al_i, nu_i, eid, false, idx, ()) mi
                                        ⟨exp_i, tmk_i, tmp_i, scr_i, hexpi, htmki, htmpi, hscri,
                                         hnv64i, hnvcv_i, hnc128i, hnu_lei, hal_lei, hscr_prei,
                                         hexp_bndi, htmk_invi, hcls_oki, fun _ => heid.2, hmi⟩
                                    · clear hc
                                      c0_hsteps_nogrp; c0_hstep; c0_hsplit
                                      · -- `lv_val == 0`: register `lv`, emit unit clause in `k`
                                        have hlv := m7_p6_shr1_lt hl_lt
                                        let l := w &&& 0x7FFFFFFF#32
                                        let lv := l >>> (1 : Nat)
                                        have hlv_cv : lv.toNat < s0.core.cur_vars := hlv.2
                                        have hlv_tmk : (lv.setWidth 64).toNat < tmk_i.length := by
                                          dsimp only [lv, l]
                                          rw [htmki, m6_zext32_toNat]; omega
                                        c0_hsteps_nogrp
                                        refine wp_join_group (ts := [i32, .bool])
                                          (fun (nv_j, ab_j, ()) mj =>
                                            ab_j = false ∧
                                            ∃ (exp_j tmk_j : List (BitVec 32)),
                                            let sj : FullState :=
                                              { si with scratch := { si.scratch with
                                                wsort := exp_j, tarjan_mark := tmk_j } }
                                            exp_j.length = 2 * c.max_vars ∧
                                            tmk_j.length = 2 * c.max_vars ∧
                                            nv_j.toNat ≤ 64 ∧ nv_j.toNat ≤ 2 * s0.core.cur_vars ∧
                                            (∀ k < nv_j.toNat,
                                              (exp_j[k]?.getD 0#32).toNat < s0.core.cur_vars) ∧
                                            (∀ u < s0.core.cur_vars, tmk_j[u]?.getD 0#32 ≠ 0#32 →
                                              1 ≤ (tmk_j[u]?.getD 0#32).toNat ∧
                                              (tmk_j[u]?.getD 0#32).toNat ≤ nv_j.toNat ∧
                                              ∃ k < nv_j.toNat, (exp_j[k]?.getD 0#32).toNat = u) ∧
                                            1 ≤ (tmk_j[lv.toNat]?.getD 0#32).toNat ∧
                                            (tmk_j[lv.toNat]?.getD 0#32).toNat ≤ nv_j.toNat ∧
                                            (FullMem c sj ⋆ R) mj)
                                          ?_ ?_
                                        · rintro _ ⟨nv_j, ab_j, ⟨⟩⟩ mj
                                            ⟨hab_j, exp_j, tmk_j, hexpj, htmkj, hnv64j, hnvcvj,
                                             hexpbj, htmkinvj, ht1j, ht2j, hmj⟩
                                          c0_hsplit
                                          · c0_hsteps!
                                            exact hBi (nv_j, nc_i, al_i, nu_i, te_i, true, idx, ())
                                              mj ⟨exp_j, tmk_j, tmp_i, scr_i, hexpj, htmkj, htmpi,
                                                hscri, hnv64j, hnvcvj, hnc128i, hnu_lei, hal_lei,
                                                hscr_prei, hexpbj, htmkinvj, hcls_oki, hteid_oki,
                                                hmj⟩
                                          · have hnc_lt128 : nc_i.toNat < 128 :=
                                              Nat.lt_of_not_le (show ¬ 128 ≤ nc_i.toNat from hc)
                                            clear hc
                                            c0_hsplit
                                            · c0_hsteps!
                                              exact hBi
                                                (nv_j, nc_i, al_i, nu_i, te_i, true, idx, ())
                                                mj ⟨exp_j, tmk_j, tmp_i, scr_i, hexpj, htmkj, htmpi,
                                                 hscri, hnv64j, hnvcvj, hnc128i, hnu_lei, hal_lei,
                                                 hscr_prei, hexpbj, htmkinvj, hcls_oki, hteid_oki,
                                                 hmj⟩
                                            · have hal1_le : al_i.toNat + 1 ≤ acap_n := by
                                                dsimp only [acap_n]
                                                rw [show (1096 : BitVec 32).toNat = 1096 from rfl,
                                                  show (2912 : BitVec 32).toNat = 2912 from rfl,
                                                  show (1 : BitVec 32).toNat = 1 from rfl] at hc
                                                omega
                                              clear hc
                                              have hal1 : (al_i + 1#32).toNat = al_i.toNat + 1 :=
                                                m7_p6_add1_toNat (by omega)
                                              have hnc1 : (nc_i + 1#32).toNat = nc_i.toNat + 1 :=
                                                m7_p6_add1_toNat (by omega)
                                              have hnu1 : (nu_i + 1#32).toNat = nu_i.toNat + 1 :=
                                                m7_p6_add1_toNat (by omega)
                                              have hlv_tmkj : (lv.setWidth 64).toNat <
                                                  tmk_j.length :=
                                                by rw [htmkj, m6_zext32_toNat]; omega
                                              have hbd_ar : 1096 + (((@OfNat.ofNat (BitVec 32)
                                                  2912 (BitVec.instOfNat)) + al_i).setWidth
                                                    64).toNat < c.scratch_cap := by
                                                rw [m7_p6_off_add 2912 (by decide) al_i (by omega)]
                                                dsimp only [acap_n] at hal1_le; omega
                                              have hbd_off : 1096 + (((@OfNat.ofNat (BitVec 32)
                                                  1888 (BitVec.instOfNat)) + nc_i).setWidth
                                                    64).toNat < c.scratch_cap := by
                                                rw [m7_p6_off_add 1888 (by decide) nc_i (by omega)]
                                                omega
                                              have hbd_met : 1096 + (((@OfNat.ofNat (BitVec 32)
                                                  2144 (BitVec.instOfNat)) + nc_i).setWidth
                                                    64).toNat < c.scratch_cap := by
                                                rw [m7_p6_off_add 2144 (by decide) nc_i (by omega)]
                                                omega
                                              have hbd_aux : 1096 + (((@OfNat.ofNat (BitVec 32)
                                                  2400 (BitVec.instOfNat)) + nc_i).setWidth
                                                    64).toNat < c.scratch_cap := by
                                                rw [m7_p6_off_add 2400 (by decide) nc_i (by omega)]
                                                omega
                                              have hbd_un : 1096 + (((@OfNat.ofNat (BitVec 32)
                                                  2656 (BitVec.instOfNat)) + nu_i).setWidth
                                                    64).toNat < c.scratch_cap := by
                                                rw [m7_p6_off_add 2656 (by decide) nu_i (by omega)]
                                                omega
                                              have hmj_scr := m7_p6_scrBuf_split hsc8192 hscri hmj
                                              c0_hsteps!
                                              have hm := m7_p6_scrBuf_unsplit hm
                                              rw [m7_p6_off_add 2912 (by decide) al_i (by omega),
                                                m7_p6_off_add 1888 (by decide) nc_i (by omega),
                                                m7_p6_off_add 2144 (by decide) nc_i (by omega),
                                                m7_p6_off_add 2400 (by decide) nc_i (by omega),
                                                m7_p6_off_add 2656 (by decide) nu_i
                                                  (by omega)] at hm
                                              simp only [← Nat.add_assoc] at hm
                                              let ulit :=
                                                (((tmk_j[(lv.setWidth 64).toNat]'hlv_tmkj -
                                                1#32) <<< (1 : Nat)) ||| (l &&& 1#32))
                                              let scr_u :=
                                                ((((scr_i.set (1096 + 2912 + al_i.toNat) ulit).set
                                                  (1096 + 1888 + nc_i.toNat) al_i).set
                                                  (1096 + 2144 + nc_i.toNat) 1#32).set
                                                  (1096 + 2400 + nc_i.toNat) eid).set
                                                  (1096 + 2656 + nu_i.toNat) nc_i
                                              rw [hab_j]
                                              refine hLi (cnt.toNat - (idx + 1#32).toNat)
                                                (nv_j, nc_i + 1#32, al_i + 1#32, nu_i + 1#32, false,
                                                  idx + 1#32, ()) _
                                                (by rw [hab_fi]; simp [hidx1]; omega)
                                                ⟨exp_j, tmk_j, tmp_i, scr_u, hexpj, htmkj,
                                                 htmpi, by simp [scr_u, hscri], by omega,
                                                 by simp, hnv64j, hnvcvj, by omega, by omega,
                                                 by omega, fun k hk => ?_, hexpbj, htmkinvj,
                                                 fun cid hcid => ?_, m7_p6_fullMem_subst hm⟩
                                              · dsimp only [scr_u]
                                                repeat rw [List.getElem?_set_ne (by omega)]
                                                exact hscr_prei k hk
                                              · dsimp only [scr_u]
                                                rcases Nat.lt_or_eq_of_le
                                                    (Nat.lt_succ_iff.mp (hnc1 ▸ hcid))
                                                  with hlt | rfl
                                                · rw [List.getElem?_set_ne (by omega),
                                                    List.getElem?_set_ne (by omega),
                                                    List.getElem?_set_ne (by omega),
                                                    List.getElem?_set_ne (by omega),
                                                    List.getElem?_set_ne (by omega)]
                                                  rw [List.getElem?_set_ne (by omega),
                                                    List.getElem?_set_ne (by omega),
                                                    List.getElem?_set_ne (by omega),
                                                    List.getElem?_set_ne (by omega),
                                                    List.getElem?_set_ne (by omega)]
                                                  have hprev := hcls_oki cid hlt
                                                  exact ⟨Nat.le_trans hprev.1 (by omega), hprev.2⟩
                                                · rw [List.getElem?_set_ne (by omega),
                                                    List.getElem?_set_ne (by omega),
                                                    List.getElem?_set_ne (by omega),
                                                    List.getElem?_set_self (by simp [hscri]; omega),
                                                    List.getElem?_set_ne (by omega),
                                                    List.getElem?_set_ne (by omega),
                                                    List.getElem?_set_self (by simp [hscri]; omega),
                                                    Option.getD_some, Option.getD_some,
                                                    show (1#32 &&& 0xFFFF#32 : BitVec 32).toNat = 1
                                                      from rfl,
                                                    show (1#32 &&& 0x40000000#32 : BitVec 32) = 0#32
                                                      from rfl]
                                                  rw [hal1]; exact ⟨Nat.le_refl _, rfl⟩
                                        · -- `if (tmk[lv] == 0)`
                                          intro _ hJ1
                                          c0_hsplit
                                          · have htmk0_lv : tmk_i[lv.toNat]?.getD 0#32 = 0#32 := by
                                              rw [List.getElem?_eq_getElem (by rw [htmki]; omega),
                                                Option.getD_some]
                                              rw [← m6_getElem_congr (m6_zext32_toNat lv) _ _]
                                              exact hc
                                            c0_hsplit
                                            · c0_hsteps!
                                              exact hBi
                                                (nv_i, nc_i, al_i, nu_i, te_i, true, idx, ())
                                                mi ⟨exp_i, tmk_i, tmp_i, scr_i, hexpi, htmki, htmpi,
                                                 hscri, hnv64i, hnvcv_i, hnc128i, hnu_lei, hal_lei,
                                                 hscr_prei, hexp_bndi, htmk_invi, hcls_oki,
                                                 hteid_oki, hmi⟩
                                            · have hnv64_lt : nv_i.toNat < 64 :=
                                                Nat.lt_of_not_le (show ¬ 64 ≤ nv_i.toNat from hc)
                                              clear hc
                                              c0_hsplit
                                              · c0_hsteps!
                                                exact hBi (nv_i, nc_i, al_i, nu_i, te_i, true, idx,
                                                    ()) mi
                                                  ⟨exp_i, tmk_i, tmp_i, scr_i, hexpi, htmki, htmpi,
                                                   hscri, hnv64i, hnvcv_i, hnc128i, hnu_lei,
                                                   hal_lei, hscr_prei, hexp_bndi, htmk_invi,
                                                   hcls_oki, hteid_oki, hmi⟩
                                              · have hnvcv_lt :
                                                    nv_i.toNat < 2 * s0.core.cur_vars := by
                                                  have hlt' : nv_i.toNat <
                                                      (2 * (s0.core.cur_vars % 2 ^ 64)) % 2 ^ 64 :=
                                                    by simpa [m6_zext32_toNat] using
                                                      Nat.lt_of_not_le hc
                                                  rw [Nat.mod_eq_of_lt (by omega),
                                                    Nat.mod_eq_of_lt (by omega)] at hlt'
                                                  exact hlt'
                                                have hexp_bd : (nv_i.setWidth 64).toNat <
                                                    exp_i.length := by
                                                  rw [hexpi, m6_zext32_toNat]; omega
                                                have hreg := m7_p6_tmk_reg hnv64_lt hnvcv_lt
                                                  (by rw [hexpi]; omega) htmki hcv_le hlv_cv
                                                  hexp_bndi htmk_invi
                                                c0_hsteps!
                                                rw [m6_zext32_toNat] at *
                                                exact hJ1 _ _ ⟨hab_fi, exp_i.set nv_i.toNat lv,
                                                  tmk_i.set lv.toNat (nv_i + 1#32),
                                                  by simp [hexpi], by simp [htmki], hreg.2.1,
                                                  hreg.2.2.1, hreg.2.2.2.1, hreg.2.2.2.2.1,
                                                  hreg.2.2.2.2.2.1, hreg.2.2.2.2.2.2, hm⟩
                                          · have htmk_nz : tmk_i[lv.toNat]?.getD 0#32 ≠ 0#32 := by
                                              rw [List.getElem?_eq_getElem (by rw [htmki]; omega),
                                                Option.getD_some]
                                              intro h0; apply hc
                                              simpa [lv, l, w, m6_zext32_toNat, BitVec.toNat_add,
                                                BitVec.toNat_ushiftRight,
                                                Nat.shiftRight_eq_div_pow,
                                                Nat.mod_eq_of_lt (by omega :
                                                  (off_s.toNat + idx.toNat) % 2 ^ 32 < 2 ^ 64)]
                                                using h0
                                            have hinv_lv := htmk_invi lv.toNat hlv_cv htmk_nz
                                            c0_hsteps!
                                            exact hJ1 _ _
                                              ⟨hab_fi, exp_i, tmk_i, hexpi, htmki, hnv64i,
                                               hnvcv_i, hexp_bndi, htmk_invi, hinv_lv.1,
                                               hinv_lv.2.1, hmi⟩
                                      · c0_hsteps!
                                        rw [hab_fi]
                                        exact hLi (cnt.toNat - (idx + 1#32).toNat)
                                          (nv_i, nc_i, al_i, nu_i, false, idx + 1#32, ()) mi
                                          (by rw [hab_fi]; simp [hidx1]; omega)
                                          ⟨exp_i, tmk_i, tmp_i, scr_i, hexpi, htmki, htmpi, hscri,
                                           by omega, by simp, hnv64i, hnvcv_i, hnc128i, hnu_lei,
                                           hal_lei, hscr_prei, hexp_bndi, htmk_invi, hcls_oki, hmi⟩
                                  · -- Large clause entry `(w & PW_BIN_FLAG) == 0`
                                    have hw_large : (w &&& 0x80000000#32) = 0#32 := by
                                      simpa [w, m6_zext32_toNat, hoff_eq, BitVec.toNat_add,
                                        Nat.mod_eq_of_lt
                                          (by omega : off_s.toNat + idx.toNat < 2 ^ 32),
                                        Nat.mod_eq_of_lt
                                          (by omega : off_s.toNat + idx.toNat < 2 ^ 64)] using hc
                                    obtain ⟨hw_sz_bd, hw_lits_lt⟩ :=
                                      m7_p6_entry_large_bounds hdw0 hw_ok hw_large
                                    have h2_nat : (2#64 : BitVec 64).toNat = 2 := rfl
                                    have hw_lt64 : w.toNat < 2 ^ 64 := by have := w.isLt; omega
                                    have hw2_eq : (w.setWidth 64 + 2#64).toNat = w.toNat + 2 := by
                                      rw [BitVec.toNat_add, BitVec.toNat_setWidth, h2_nat,
                                        Nat.mod_eq_of_lt hw_lt64,
                                        Nat.mod_eq_of_lt (by
                                          have := hdw0.1.core_ok.arena_len_le; omega)]
                                    have hw2_bd : (w.setWidth 64 + 2#64).toNat <
                                        s0.core.arena.length := by
                                      rw [hdw0.1.core_ok.arena_len_arr, hw2_eq]
                                      have := hdw0.1.core_ok.arena_len_le; omega
                                    let sz := s0.core.arena[(w.setWidth 64 + 2#64).toNat]'hw2_bd
                                    have hsz_eq : sz.toNat =
                                        (s0.core.arena[w.toNat + 2]?.getD 0#32).toNat := by
                                      dsimp only [sz]
                                      rw [List.getElem?_eq_getElem (by
                                        rw [hdw0.1.core_ok.arena_len_arr]
                                        have := hdw0.1.core_ok.arena_len_le; omega),
                                        Option.getD_some]
                                      exact congrArg BitVec.toNat (m6_getElem_congr hw2_eq _ _)
                                    c0_hsteps_nogrp
                                    refine wp_join_group (ts := [i32, .bool, .bool, i32, i32])
                                      (fun (nv_m, ab_m, sat_m, csz_m, _m_idx, ()) mm =>
                                        ∃ (exp_m tmk_m tmp_m : List (BitVec 32)),
                                          let sm : FullState :=
                                            { si with
                                              core := { si.core with tmp := tmp_m }
                                              scratch :=
                                                { si.scratch with
                                                  wsort := exp_m, tarjan_mark := tmk_m } }
                                          exp_m.length = 2 * c.max_vars ∧
                                          tmk_m.length = 2 * c.max_vars ∧
                                          tmp_m.length = c.max_vars ∧
                                          nv_m.toNat ≤ 64 ∧ nv_m.toNat ≤ 2 * s0.core.cur_vars ∧
                                          csz_m.toNat ≤ mc.toNat ∧
                                          (∀ k < nv_m.toNat,
                                            (exp_m[k]?.getD 0#32).toNat < s0.core.cur_vars) ∧
                                          (∀ u < s0.core.cur_vars, tmk_m[u]?.getD 0#32 ≠ 0#32 →
                                            1 ≤ (tmk_m[u]?.getD 0#32).toNat ∧
                                            (tmk_m[u]?.getD 0#32).toNat ≤ nv_m.toNat ∧
                                            ∃ k < nv_m.toNat, (exp_m[k]?.getD 0#32).toNat = u) ∧
                                          (FullMem c sm ⋆ R) mm)
                                      ?_ ?_
                                    · -- After `while (m < sz)`
                                      rintro _ ⟨nv_m, ab_m, sat_m, csz_m, _m_idx, ⟨⟩⟩ mm
                                        ⟨exp_m, tmk_m, tmp_m, hexpm, htmkm, htmpm, hnv64m, hnvcvm,
                                         hcszm, hexpbm, htmkinvm, hmm⟩
                                      c0_hsplit
                                      · have hab_tm : ab_m = true := by simpa using hc
                                        c0_hsteps!
                                        rw [hab_tm]
                                        exact hBi (nv_m, nc_i, al_i, nu_i, te_i, true, idx, ()) mm
                                          ⟨exp_m, tmk_m, tmp_m, scr_i, hexpm, htmkm, htmpm, hscri,
                                           hnv64m, hnvcvm, hnc128i, hnu_lei, hal_lei, hscr_prei,
                                           hexpbm, htmkinvm, hcls_oki, hteid_oki, hmm⟩
                                      · have hab_fm : ab_m = false := by
                                          cases ab_m with
                                          | false => rfl
                                          | true => exact Bool.noConfusion hc
                                        clear hc
                                        c0_hsteps_nogrp; c0_hstep; c0_hsplit
                                        · c0_hsteps!
                                          rw [hab_fm]
                                          exact hLi (cnt.toNat - (idx + 1#32).toNat)
                                            (nv_m, nc_i, al_i, nu_i, false, idx + 1#32, ()) mm
                                            (by rw [hab_fi]; simp [hidx1]; omega)
                                            ⟨exp_m, tmk_m, tmp_m, scr_i, hexpm, htmkm, htmpm, hscri,
                                             by omega, by simp, hnv64m, hnvcvm, hnc128i, hnu_lei,
                                             hal_lei, hscr_prei, hexpbm, htmkinvm, hcls_oki, hmm⟩
                                        · clear hc
                                          c0_hsplit
                                          · c0_hsteps!
                                            rw [hab_fm]
                                            exact hBi (nv_m, nc_i, al_i, nu_i, eid, false, idx, ())
                                              mm ⟨exp_m, tmk_m, tmp_m, scr_i, hexpm, htmkm, htmpm,
                                               hscri, hnv64m, hnvcvm, hnc128i, hnu_lei, hal_lei,
                                               hscr_prei, hexpbm, htmkinvm, hcls_oki,
                                               fun _ => heid.2, hmm⟩
                                          · have hcsz_pos : 0 < csz_m.toNat :=
                                              Nat.pos_of_ne_zero fun hz =>
                                                hc (BitVec.eq_of_toNat_eq hz)
                                            clear hc
                                            c0_hsplit
                                            · c0_hsteps!
                                              exact hBi
                                                (nv_m, nc_i, al_i, nu_i, te_i, true, idx, ())
                                                mm ⟨exp_m, tmk_m, tmp_m, scr_i, hexpm, htmkm, htmpm,
                                                 hscri, hnv64m, hnvcvm, hnc128i, hnu_lei, hal_lei,
                                                 hscr_prei, hexpbm, htmkinvm, hcls_oki, hteid_oki,
                                                 hmm⟩
                                            · have hnc_lt128 : nc_i.toNat < 128 :=
                                                Nat.lt_of_not_le (show ¬ 128 ≤ nc_i.toNat from hc)
                                              clear hc
                                              c0_hsplit
                                              · c0_hsteps!
                                                exact hBi (nv_m, nc_i, al_i, nu_i, te_i, true, idx,
                                                    ()) mm
                                                  ⟨exp_m, tmk_m, tmp_m, scr_i, hexpm, htmkm, htmpm,
                                                   hscri, hnv64m, hnvcvm, hnc128i, hnu_lei, hal_lei,
                                                   hscr_prei, hexpbm, htmkinvm, hcls_oki, hteid_oki,
                                                   hmm⟩
                                              · have halc_le :
                                                    al_i.toNat + csz_m.toNat ≤ acap_n := by
                                                  dsimp only [acap_n]
                                                  rw [show (1096 : BitVec 32).toNat = 1096 from rfl,
                                                    show (2912 : BitVec 32).toNat = 2912 from rfl]
                                                    at hc
                                                  omega
                                                clear hc
                                                -- Copy `tmp[0..csz_m)` to `k[2912 + al_i + m]`
                                                have hnc1 : (nc_i + 1#32).toNat = nc_i.toNat + 1 :=
                                                  m7_p6_add1_toNat (by omega)
                                                have halc_eq : (al_i + csz_m).toNat =
                                                    al_i.toNat + csz_m.toNat := by
                                                  rw [BitVec.toNat_add,
                                                    Nat.mod_eq_of_lt (by omega)]
                                                let s_base : FullState :=
                                                  { si with
                                                    core := { si.core with tmp := tmp_m }
                                                    scratch :=
                                                      { si.scratch with
                                                        wsort := exp_m, tarjan_mark := tmk_m,
                                                        scratch_buf := scr_i } }
                                                c0_hsteps_nogrp
                                                exact m7_p6_copy_clause_wp Γ Q X J c s_base R
                                                  _ _ nc_i al_i nu_i eid te_i csz_m ab_m
                                                  (fun k => s0.scratch.scratch_buf[k]?) mm
                                                  rfl rfl hsc8192 hsc hscri htmpm
                                                  hcsz_pos (by omega) (by omega) hnc_lt128 hnu_lei
                                                  halc_le hscr_prei hcls_oki
                                                  (m7_p6_fullMem_subst hmm)
                                                  fun nu_j _ scr_j mj hscj_l hnu_j hpre_j hcls_j
                                                    hmj => by
                                                    c0_hsteps!
                                                    rw [hab_fm]
                                                    exact hLi (cnt.toNat - (idx + 1#32).toNat)
                                                      (nv_m, nc_i + 1#32, al_i + csz_m, nu_j,
                                                        false, idx + 1#32, ()) mj
                                                      (by rw [hab_fi]; simp [hidx1]; omega)
                                                      ⟨exp_m, tmk_m, tmp_m, scr_j, hexpm, htmkm,
                                                       htmpm, hscj_l, by omega, by simp, hnv64m,
                                                       hnvcvm, by omega, by omega, by omega,
                                                       hpre_j, hexpbm, htmkinvm,
                                                       fun cid hcid => by
                                                         rw [hnc1] at hcid
                                                         rw [halc_eq]; exact hcls_j cid hcid,
                                                       hmj⟩
                                    · intro Bm hBm
                                      c0_hsteps_nogrp
                                      exact m7_p6_scan_large_wp Γ Q X Bm c si R _ _ _ _ _
                                        nv_i except w sz mc ab_i mi rfl rfl rfl rfl rfl
                                        hdw0.1.core_ok.arena_len_arr hdw0.1.core_ok.arena_len_le
                                        hdw0.1.core_ok.vals_len hcv_le hmx
                                        (by rw [hsz_eq]; exact hw_sz_bd)
                                        (fun j hj => hw_lits_lt j (by rw [← hsz_eq]; exact hj))
                                        hexpi htmki htmpi hmc_lo hmc_hi hmc_cv hnv64i hnvcv_i hab_fi
                                        hexp_bndi htmk_invi hmi
                                        fun nv_m ab_m sat_m csz_m m_idx exp_m tmk_m tmp_m mm
                                          hexpm htmkm htmpm hnv64m hnvcvm hcszm hexpbm htmkinvm
                                          hmm =>
                                        hBm (nv_m, ab_m, sat_m, csz_m, m_idx, ()) mm
                                          ⟨exp_m, tmk_m, tmp_m, hexpm, htmkm, htmpm, hnv64m, hnvcvm,
                                           hcszm, hexpbm, htmkinvm, hmm⟩
                                · -- `idx < cnt` false -> exit inner loop
                                  c0_hsteps!
                                  exact hBi (nv_i, nc_i, al_i, nu_i, te_i, ab_i, idx, ()) mi
                                    ⟨exp_i, tmk_i, tmp_i, scr_i, hexpi, htmki, htmpi, hscri, hnv64i,
                                     hnvcv_i, hnc128i, hnu_lei, hal_lei, hscr_prei, hexp_bndi,
                                     htmk_invi, hcls_oki, hteid_oki, hmi⟩
                              · intro _ Li _ hLi; c0_hsteps!
                                exact hLi (if !ab_s then cnt.toNat else 0)
                                  (nv_s, nc_s, alen_s, nunits_s, ab_s, 0#32, ()) ms
                                  ⟨exp_s, tmk_s, tmp_s, scr_s, hexpl, htmkl, htmpl, hscrl,
                                   Nat.zero_le _, by simp [hab_f], hnv64, hnvcv, hnc128, hnu_le,
                                   hal_le, hscr_pre, hexp_bnd, htmk_inv, hcls_ok, hms⟩
                            · intro _ hJe; c0_hsplit
                              · c0_hsteps!; exact hJe (v <<< (1 : Nat)) ⟨fun _ => rfl, fun h =>
                                  absurd hc h⟩
                              · c0_hsteps!; exact hJe ((v <<< (1 : Nat)) ||| 1#32)
                                  ⟨fun h => absurd h hc, fun _ => rfl⟩
                          · intro _ hJo; c0_hsplit
                            · c0_hsteps!; exact hJo 0#32 ⟨fun _ => rfl, fun h => absurd hc h⟩
                            · c0_hsteps!; exact hJo 512#32 ⟨fun h => absurd h hc, fun _ => rfl⟩
                        · intro _ hJc; c0_hsplit
                          · c0_hsteps!; exact hJc np ⟨fun _ => rfl, fun h => absurd hc h⟩
                          · c0_hsteps!; exact hJc nn ⟨fun h => absurd h hc, fun _ => rfl⟩
                      · c0_hsteps!; exact hdone_ex
                  · c0_hsteps!; exact hdone_ex
              · intro Ls hLs; c0_hsteps!
                exact hLs 2 (0#32, 0#32, 0#32, 0#32, 0xFFFFFFFF#32, false, 0#32, ()) m0
                  ⟨s0.scratch.wsort, s0.scratch.tarjan_mark, s0.core.tmp, s0.scratch.scratch_buf,
                   hdw0.1.scratch_ok.wsort_len, hdw0.1.scratch_ok.tarjan_mark_len,
                   hdw0.1.core_ok.tmp_len_arr, hdw0.1.scratch_ok.scratch_buf_len,
                   by decide, rfl, by decide, Nat.zero_le _, by decide, by decide, Nat.zero_le _,
                   fun _ _ => rfl, fun _ hk => by simp at hk,
                   fun u hu hnz => absurd (htmk0 u hu) hnz, fun cid hcid => by simp at hcid,
                   fun hne => absurd rfl hne, hm0⟩
            · intro _ hJmc
              c0_hsplit
              · have hmv_cv : 0 < c.max_vars := by omega
                have hmv_100 : c.max_vars < 100 := by
                  simp only [bv_c0, BitVec.reduceToNat] at hc
                  rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                have htr : ((BitVec.ofNat 64 c.max_vars).truncate 32).toNat = c.max_vars := by
                  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                c0_hsteps!
                exact hJmc ((BitVec.ofNat 64 c.max_vars).truncate 32)
                  ⟨by rw [htr]; exact hmv_cv, by rw [htr]; omega,
                   by rw [htr]; exact Nat.le_refl _⟩
              · have hmv_ge : 100 ≤ c.max_vars := by
                  simp only [bv_c0, BitVec.reduceToNat] at hc
                  rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
                c0_hsteps!; exact hJmc 100#32 ⟨by decide, by decide, hmv_ge⟩

/-! ## 4. `full_bve_gates_m7_wp` -/

/-- Parametric `Func.wp` proof for `full_bve_gates_m7`, certifying `fullBveGatesM7Spec`. -/
theorem full_bve_gates_m7_wp (Γ : Env)
    (hEquiv : ∀ a m Q X, fullBveFindEquivM7Spec a m Q X →
      Γ "full_bve_find_equiv_m7" [i64, i32, i32] [.bool] a m Q X)
    (hAnd : ∀ a m Q X, fullBveFindAndM7Spec a m Q X →
      Γ "full_bve_find_and_m7" [i64, i32, i32, i32] [.bool] a m Q X)
    (hIte : ∀ a m Q X, fullBveFindIteM7Spec a m Q X →
      Γ "full_bve_find_ite_m7" [i64, i32, i32, i32] [.bool] a m Q X)
    (hXor : ∀ a m Q X, fullBveFindXorM7Spec a m Q X →
      Γ "full_bve_find_xor_m7" [i64, i32, i32, i32] [.bool] a m Q X)
    (hDefK6 : ∀ a m Q X, fullBveGatesM7Spec a m Q X →
      Γ "full_bve_def_k6_m7" [i64, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullBveGatesM7Spec a m Q X →
      Func.wp Γ full_bve_gates_m7_body a m Q X := by
  rintro ⟨h, v, np, nn, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hdw0, htmk0, hsc1088, hv_lt, hnp512, hnn512,
    hp_ok, hn_ok, hm0, hQ⟩ := fullBveGatesM7Spec_elim hSpec
  have hmx := c.hmaxv; have hsc := c.hscr; unfold dimacsBound at hmx hsc
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hplnl := m7_p6_pl_nl_eq v (by omega)
  unfold Func.wp full_bve_gates_m7_body
  c0_hsteps_nogrp
  -- Zero `scr[1024 ..< 1058)`
  refine wp_loop_group (ts := [i32])
    (fun rem0 (k, ()) mk => ∃ scr0 : List (BitVec 32),
      let s0k : FullState := { s0 with scratch := { s0.scratch with scratch_buf := scr0 } }
      scr0.length = c.scratch_cap ∧ k.toNat ≤ 34 ∧ rem0 = 34 - k.toNat ∧
      (∀ i < 1024, scr0[i]? = s0.scratch.scratch_buf[i]?) ∧ (FullMem c s0k ⋆ R) mk)
    ?_ ?_
  · rintro L0 rem0 ⟨k, ⟨⟩⟩ mk hL0 ⟨scr0, hsc0, hk_le, rfl, hkeep0, hmk⟩
    c0_hsplit
    · have hk_lt : k.toNat < 34 := hc
      have hidx : ((1024#32 + k).setWidth 64).toNat < scr0.length := by
        rw [hsc0, m6_zext32_toNat]; c0_bound
      have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
      c0_hsteps!
      exact hL0 (34 - (k + 1#32).toNat) (k + 1#32, ()) _ (by omega)
        ⟨scr0.set ((1024#32 + k).setWidth 64).toNat 0#32, by simp [hsc0], by omega, rfl,
         fun i hi => by
           rw [List.getElem?_set_ne (by rw [m6_zext32_toNat]; c0_bound)]; exact hkeep0 i hi, hm⟩
    · have hdw1 := m7_p6_fullDenseInvW_def hdw0
        hdw0.1.core_ok.tmp_len_arr hdw0.1.scratch_ok.wsort_len
        hdw0.1.scratch_ok.tarjan_mark_len hsc0
      have htmk1 : TmkZero { s0 with scratch := { s0.scratch with scratch_buf := scr0 } } :=
        htmk0
      have hp1 : ∀ i < np.toNat, FullBveEntryOkW F_cur
          { s0 with scratch := { s0.scratch with scratch_buf := scr0 } } (2 * v.toNat)
          (scr0[i]?.getD 0#32) := fun i hi => by
        rw [hkeep0 i (by omega)]; exact hp_ok i hi
      have hn1 : ∀ j < nn.toNat, FullBveEntryOkW F_cur
          { s0 with scratch := { s0.scratch with scratch_buf := scr0 } } (2 * v.toNat + 1)
          (scr0[512 + j]?.getD 0#32) := fun j hj => by
        rw [hkeep0 (512 + j) (by omega)]; exact hn_ok j hj
      c0_hsplit
      · c0_hsteps!
        exact hQ _ mk hdw1 htmk1 rfl rfl rfl (Nat.le_refl _)
          (fun i hi => hkeep0 i (by omega))
          (fun j hj => hkeep0 (512 + j) (by omega)) hmk
      · clear hc
        c0_hsplit
        · c0_hsteps!
          exact hQ _ mk hdw1 htmk1 rfl rfl rfl (Nat.le_refl _)
            (fun i hi => hkeep0 i (by omega))
            (fun j hj => hkeep0 (512 + j) (by omega)) hmk
        · clear hc
          -- 1. `full_bve_find_equiv_m7`
          m7_call hEquiv
          refine fullBveFindEquivM7Spec_intro rfl hdw1 hsc1088 hnp512 hnn512
            (fun i hi hbin => m7_p6_entry_bin_bounds (hp1 i hi) hbin)
            (fun j hj hbin => m7_p6_entry_bin_bounds (hn1 j hj) hbin)
            hmk ?_
          intro ok_e lm_e scr_e m_e _ hdw_e hsce_l hkeep_e hm_e
          have hk_e : ∀ i < 1024, scr_e[i]? = s0.scratch.scratch_buf[i]? := fun i hi =>
            (hkeep_e i (by omega) (Or.inl hi)).trans (hkeep0 i hi)
          have htmk_e : TmkZero
              { s0 with
                core := { s0.core with lit_mark := lm_e }
                scratch := { s0.scratch with scratch_buf := scr_e } } := htmk0
          c0_hsplit
          · c0_hsteps!
            exact hQ _ m_e hdw_e htmk_e rfl rfl rfl (Nat.le_refl _)
              (fun i hi => hk_e i (by omega))
              (fun j hj => hk_e (512 + j) (by omega)) hm_e
          · clear hc
            c0_hsteps_nogrp
            -- 2. `full_bve_find_and_m7(h, pl, np, nn)`
            have hev0 : (((v <<< (1 : Nat)) &&& 1#32) <<< (9 : Nat)) = 0#32 :=
              BitVec.eq_of_toNat_eq (by
                rw [BitVec.toNat_shiftLeft, BitVec.toNat_and, hplnl.1,
                  show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod,
                  Nat.mul_mod_right]; rfl)
            have hodd1 : ((((v <<< (1 : Nat)) ||| 1#32) &&& 1#32) <<< (9 : Nat)) = 512#32 :=
              BitVec.eq_of_toNat_eq (by
                rw [BitVec.toNat_shiftLeft, BitVec.toNat_and, hplnl.2,
                  show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod,
                  show (2 * v.toNat + 1) % 2 = 1 by omega]; rfl)
            m7_call hAnd
            dsimp only [vals, Arg.val]
            refine fullBveFindAndM7Spec_intro rfl hdw_e hsc1088
              (by rw [show (v <<< OfNat.ofNat 1 : BitVec 32) = (v <<< (1 : Nat)) from rfl,
                    hplnl.1]; exact Nat.mul_lt_mul_of_pos_left hv_lt (by decide))
              hnp512 hnn512
              (fun i hi => by
                rw [show (v <<< OfNat.ofNat 1 : BitVec 32) = (v <<< (1 : Nat)) from rfl,
                  hplnl.1, hev0, show (0#32 : BitVec 32).toNat = 0 from rfl, Nat.zero_add,
                  hk_e i (by omega)]
                exact hp_ok i hi)
              (fun j hj => by
                rw [show (v <<< OfNat.ofNat 1 : BitVec 32) = (v <<< (1 : Nat)) from rfl,
                  hplnl.1, hev0, show (512#32 - 0#32 : BitVec 32).toNat = 512 from rfl,
                  m7_p6_xor_two_mul, hk_e (512 + j) (by omega)]
                exact hn_ok j hj)
              hm_e ?_
            intro ok_ap lm_ap scr_ap m_ap s_ap hdw_ap hscap_l hkeep_ap hm_ap
            have hk_ap : ∀ i < 1024, scr_ap[i]? = s0.scratch.scratch_buf[i]? := fun i hi =>
              (hkeep_ap i (by omega) (Or.inl hi)).trans (hk_e i hi)
            have htmk_ap : TmkZero
                { s0 with
                  core := { s0.core with lit_mark := lm_ap }
                  scratch := { s0.scratch with scratch_buf := scr_ap } } := htmk0
            c0_hsplit
            · c0_hsteps!
              exact hQ _ m_ap hdw_ap htmk_ap rfl rfl rfl (Nat.le_refl _)
                (fun i hi => hk_ap i (by omega))
                (fun j hj => hk_ap (512 + j) (by omega)) hm_ap
            · clear hc
              -- 3. `full_bve_find_and_m7(h, nl, nn, np)`
              m7_call hAnd
              dsimp only [vals, Arg.val]
              refine fullBveFindAndM7Spec_intro rfl hdw_ap hsc1088
                (by rw [show s_ap.core.cur_vars = s0.core.cur_vars from rfl,
                      show (v <<< OfNat.ofNat 1 ||| 1 : BitVec 32) =
                      ((v <<< (1 : Nat)) ||| 1#32) from rfl, hplnl.2]; omega)
                hnn512 hnp512
                (fun i hi => by
                  rw [show (v <<< OfNat.ofNat 1 ||| 1 : BitVec 32) =
                      ((v <<< (1 : Nat)) ||| 1#32) from rfl,
                    hplnl.2, hodd1, show (512#32 : BitVec 32).toNat = 512 from rfl,
                    hk_ap (512 + i) (by omega)]
                  exact hn_ok i hi)
                (fun j hj => by
                  rw [show (v <<< OfNat.ofNat 1 ||| 1 : BitVec 32) =
                      ((v <<< (1 : Nat)) ||| 1#32) from rfl,
                    hplnl.2, hodd1, show (512#32 - 512#32 : BitVec 32).toNat = 0 from rfl,
                    m7_p6_xor_two_mul_add1, Nat.zero_add, hk_ap j (by omega)]
                  exact hp_ok j hj)
                hm_ap ?_
              intro ok_an lm_an scr_an m_an _ hdw_an hscan_l hkeep_an hm_an
              have hk_an : ∀ i < 1024, scr_an[i]? = s0.scratch.scratch_buf[i]? := fun i hi =>
                (hkeep_an i (by omega) (Or.inl hi)).trans (hk_ap i hi)
              have htmk_an : TmkZero
                  { s0 with
                    core := { s0.core with lit_mark := lm_an }
                    scratch := { s0.scratch with scratch_buf := scr_an } } := htmk0
              c0_hsplit
              · c0_hsteps!
                exact hQ _ m_an hdw_an htmk_an rfl rfl rfl (Nat.le_refl _)
                  (fun i hi => hk_an i (by omega))
                  (fun j hj => hk_an (512 + j) (by omega)) hm_an
              · clear hc
                -- 4. `full_bve_find_ite_m7(h, v, np, nn)`
                m7_call hIte
                dsimp only [vals, Arg.val]
                refine fullBveFindIteM7Spec_intro rfl hdw_an (by omega) hv_lt hnp512 hnn512
                  (fun i hi => by rw [hk_an i (by omega)]; exact hp_ok i hi)
                  (fun j hj => by rw [hk_an (512 + j) (by omega)]; exact hn_ok j hj)
                  hm_an ?_
                intro ok_i scr_i m_i _ hsci_l hkeep_i hm_i
                have hdw_i := m7_p6_fullDenseInvW_def hdw_an
                  hdw_an.1.core_ok.tmp_len_arr hdw_an.1.scratch_ok.wsort_len
                  hdw_an.1.scratch_ok.tarjan_mark_len hsci_l
                have hk_i : ∀ k < 1024, scr_i[k]? = s0.scratch.scratch_buf[k]? := fun k hk =>
                  (hkeep_i k (by omega) (Or.inl hk)).trans (hk_an k hk)
                have htmk_i : TmkZero
                    { s0 with
                      core := { s0.core with lit_mark := lm_e }
                      scratch := { s0.scratch with scratch_buf := scr_i } } := htmk0
                c0_hsplit
                · c0_hsteps!
                  exact hQ _ m_i hdw_i htmk_i rfl rfl rfl (Nat.le_refl _)
                    (fun k hk => hk_i k (by omega))
                    (fun j hj => hk_i (512 + j) (by omega)) hm_i
                · clear hc
                  -- 5. `full_bve_find_xor_m7(h, v, np, nn)`
                  m7_call hXor
                  dsimp only [vals, Arg.val]
                  refine fullBveFindXorM7Spec_intro rfl hdw_i hsc1088 hv_lt hnp512 hnn512
                    (fun i hi => by rw [hk_i i (by omega)]; exact hp_ok i hi)
                    (fun j hj => by rw [hk_i (512 + j) (by omega)]; exact hn_ok j hj)
                    hm_i ?_
                  intro ok_x lm_x scr_x m_x _ hdw_x hscx_l hkeep_x hm_x
                  have hk_x : ∀ k < 1024, scr_x[k]? = s0.scratch.scratch_buf[k]? := fun k hk =>
                    (hkeep_x k (by omega) (Or.inl hk)).trans (hk_i k hk)
                  have htmk_x : TmkZero
                      { s0 with
                        core := { s0.core with lit_mark := lm_x }
                        scratch := { s0.scratch with scratch_buf := scr_x } } := htmk0
                  c0_hsplit
                  · c0_hsteps!
                    exact hQ _ m_x hdw_x htmk_x rfl rfl rfl (Nat.le_refl _)
                      (fun k hk => hk_x k (by omega))
                      (fun j hj => hk_x (512 + j) (by omega)) hm_x
                  · clear hc
                    -- 6. `full_bve_def_k6_m7(h, v, np, nn)`
                    c0_hsteps_nogrp
                    m7_call hDefK6
                    dsimp only [vals, Arg.val]
                    refine fullBveGatesM7Spec_intro rfl hdw_x htmk_x hsc1088 hv_lt hnp512 hnn512
                      (fun i hi => by rw [hk_x i (by omega)]; exact hp_ok i hi)
                      (fun j hj => by rw [hk_x (512 + j) (by omega)]; exact hn_ok j hj)
                      hm_x ?_
                    intro s_f m_f hdw_f htmk_f hcv_f har_f hal_f hfl_f hp_f hn_f hm_f
                    c0_hsteps!
                    exact hQ s_f m_f hdw_f htmk_f hcv_f har_f hal_f hfl_f
                      (fun i hi => (hp_f i hi).trans (hk_x i (by omega)))
                      (fun j hj => (hn_f j hj).trans (hk_x (512 + j) (by omega)))
                      hm_f
  · intro L0 hL0; c0_hsteps!
    exact hL0 34 (0#32, ()) m0 ⟨s0.scratch.scratch_buf, hdw0.1.scratch_ok.scratch_buf_len,
      Nat.zero_le _, rfl, fun _ _ => rfl, hm0⟩

end LeanQbe.T.Examples.Kissat.FullM7BveGates
