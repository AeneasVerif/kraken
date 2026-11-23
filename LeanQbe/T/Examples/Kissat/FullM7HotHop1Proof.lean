module

public import LeanQbe.T.Examples.Kissat.FullM7HotHop1
public import LeanQbe.T.Examples.Kissat.FullBvaHeapSpec
public import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas
import LeanQbe.T.Examples.Kissat.FullBvaFwdLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M7 Hot-Loop Proofs for `full_bva_hop1` & `full_bva_hop2` (`FullM7HotHop1Proof`)

M1-clean (`public section` with no attribute/import leaks or heartbeat overrides) verification
for `FullM7HotHop1`:
1. `full_bva_hop1_m7_wp`: proves canonical `FullBvaHeap.fullBvaHop1Spec` for `full_bva_hop1_m7_body`
   (`m7Hop1Fn`), handling scalarized `ant`, sunk `st1`/`cv`, and `ci`/`cend` clause-scan LSR.
2. `full_bva_hop2_m7_wp`: proves canonical `FullBvaHeap.fullBvaHop2Spec` for `full_bva_hop2_m7_body`
   (`m7Hop2Fn`), handling sunk `st2`/`cv`.
3. Closed `2`-row `m7HotHop1SpecTable`, `m7HotHop1Env`, `m7HotHop1Env_noExit`,
   `m7HotHop1_tableImpl`, `m7HotHop1_moduleOk : ModuleOk m7HotHop1Env m7HotHop1Module`,
   drop-in `m7Hop1Fn_wp` / `m7Hop2Fn_wp`, and concrete `Mem 64` UNSAT non-vacuity (`nv_m7_bva_hop1`,
   `nv_m7_bva_hop2`, `XPost := False`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7HotHop1

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapTactics
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapScanHelpers
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullBvaHeapTactics

/-! ## 1. Watch-Vec Bounds Helper & `Func.wp` Proofs -/

private theorem m7_hop_wvec_bounds {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvNoLm c F0 F_cur s) {sl : Nat}
    (hsl : sl < 2 * s.core.cur_vars) :
    fullWatchOffCore s.core sl + fullWatchSizeCore s.core sl ≤ s.core.wlen ∧
    DenseWatchSliceOk F_cur s.core sl (fullWatchOffCore s.core sl)
      (fullWatchSizeCore s.core sl) := by
  have hdw : DenseWatchesInv F_cur s.core := by
    have h := hinv.2.1.watches; unfold ModeWatchesInv at h
    rwa [ite_eq_right hinv.2.2.2.2.2] at h
  exact ⟨hdw.layout.bounds sl hsl, hdw.slices sl hsl⟩

/-- Exact canonical `fullBvaHop1Spec` correctness for scalarized/LSR `full_bva_hop1_m7_body`. -/
theorem full_bva_hop1_m7_wp (Γ : Env) :
    ∀ args m Q X, fullBvaHop1Spec args m Q X →
      Func.wp Γ full_bva_hop1_m7_body args m Q X := by
  rintro ⟨h, src_lit, dst_idx, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hsrc_lt, htc_le, hmclr_ok, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena
  unfold dimacsBound at hmx hwcap har_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hrepr_len := hcl.repr_len
  have hwv_len := hcl.wvec_len; have hws_len := hcl.wstk_len_arr; have har_len := hcl.arena_len_arr
  have hwlen_le := hcl.wlen_le; have hal_le := hcl.arena_len_le
  have hmclr_len := hcl.min_clr_len_arr
  have hsidx_lt : (src_lit >>> 1).toNat < s.core.cur_vars := by
    rw [bv32_lshr1_nat]; omega
  c0_hsteps_nogrp
  · exact hQ _ s.core.repr s.core.min_clr s.core.tmp_cnt s.scratch.ant_sz m
      hinv htc_le hmclr_ok (Nat.le_refl _) hm
  · refine wp_join_state1 (t := i64) (α := BitVec 64) (fun r => r) (fun _ ml => ml = m)
      (fun _ res0 ml hml => ?_) (fun J0 hJ0 => ?_)
    · subst ml
      c0_hsteps_nogrp
      refine wp_loop_inv
        (fun (res, ant, sgn, ()) ml =>
          sgn.toNat ≤ 2 ∧ ant.toNat ≤ s.scratch.ant_sz.toNat ∧ ml = m)
        (fun (_, _, sgn, _) _ => 2 - sgn.toNat)
        (fun Js hJs => by
          c0_hsteps
          exact hJs (res0, s.scratch.ant_sz, 0#32, ()) m ⟨by decide, Nat.le_refl _, rfl⟩)
        (fun Js (res, ant, sgn, ()) ml ⟨hsgn_le, hant_le, hml⟩ ihs => ?_)
      subst ml
      c0_hsteps_nogrp
      refine wp_join_state0 (α := PUnit)
        (fun _ mf => mf = m)
        (fun _ _ mf hmf => ?_)
        (fun Jend hJend => ?_)
      · subst mf
        c0_hsteps_nogrp
        refine wp_join_state1 (t := i64)
          (α := BitVec 64 × List (BitVec 32) × List (BitVec 32) × Nat) (fun st => st.1)
          (fun ⟨_resF, rpF, mcF, tcF⟩ mf1 =>
            FullDenseInvNoLm c F0 F_cur
              { core := { s.core with repr := rpF, min_clr := mcF, tmp_cnt := tcF }
                scratch := { s.scratch with ant_sz := ant } } ∧
            tcF ≤ s.core.cur_vars ∧
            (∀ i < tcF, (mcF[i]?.getD 0#32).toNat < c.max_vars) ∧
            (FullMem c
              { core := { s.core with repr := rpF, min_clr := mcF, tmp_cnt := tcF }
                scratch := { s.scratch with ant_sz := ant } } ⋆ R) mf1)
          (fun _ ⟨resF, rpF, mcF, tcF⟩ mf1 ⟨hinvF, htcF, hmcF, hmf1⟩ => by
            c0_hsteps; exact hQ resF rpF mcF tcF ant mf1 hinvF htcF hmcF hant_le hmf1)
          (fun Jant hJant => ?_)
        c0_hsteps_nogrp
        · refine wp_join_state1 (t := i64) (α := BitVec 64) (fun r => r)
            (fun _ ml => ml = m)
            (fun _ resC ml hml => ?_) (fun Jc hJc => ?_)
          · subst ml
            c0_hsteps
            · have htc1 : s.core.tmp_cnt + 1 ≤ s.core.cur_vars := by c0_bound
              have hinv' : FullDenseInvNoLm c F0 F_cur
                  { core := { s.core with
                      repr := repr64Set s.core.repr (src_lit >>> 1).toNat (resC + 1)
                      min_clr := s.core.min_clr.set s.core.tmp_cnt (src_lit >>> 1)
                      tmp_cnt := s.core.tmp_cnt + 1 }
                    scratch := { s.scratch with ant_sz := ant } } :=
                fullDenseInvNoLm_with_core_aux hinv (by rw [repr64Set_length, hrepr_len])
                  (by simp [hmclr_len]) hcl.tmp_len_arr hcl.flags_len hcl.tmp_len_le
                  { hsc with } rfl rfl
              have hm' : (FullMem c
                  { core := { s.core with
                      repr := repr64Set s.core.repr (src_lit >>> 1).toNat (resC + 1)
                      min_clr := s.core.min_clr.set s.core.tmp_cnt (src_lit >>> 1)
                      tmp_cnt := s.core.tmp_cnt + 1 }
                    scratch := { s.scratch with ant_sz := ant } } ⋆ R) m := by
                have h1 : (BitVec.ofNat 64 s.core.tmp_cnt + 1).toNat = s.core.tmp_cnt + 1 := by
                  change (BitVec.ofNat 64 s.core.tmp_cnt + 1#64).toNat = _; c0_bound
                have h2 : (BitVec.ofNat 64 s.core.tmp_cnt).toNat = s.core.tmp_cnt := by c0_bound
                have h3 : (BitVec.setWidth 64 (src_lit >>> 1)).toNat = (src_lit >>> 1).toNat := by
                  c0_bound
                rw [h1, h2, h3] at hm; exact hm
              exact hJant ⟨resC, _, _, s.core.tmp_cnt + 1⟩ m ⟨hinv', htc1, fun i hi => by
                by_cases hie : i = s.core.tmp_cnt
                · subst hie; rw [List.getElem?_set_self (by omega), Option.getD_some]; omega
                · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hmclr_ok i (by omega), hm'⟩
            · have hinv' : FullDenseInvNoLm c F0 F_cur
                  { core := { s.core with
                      repr := repr64Set s.core.repr (src_lit >>> 1).toNat (resC + 1) }
                    scratch := { s.scratch with ant_sz := ant } } :=
                fullDenseInvNoLm_with_core_aux hinv (by rw [repr64Set_length, hrepr_len])
                  hmclr_len hcl.tmp_len_arr hcl.flags_len hcl.tmp_len_le { hsc with } rfl rfl
              have hm' : (FullMem c
                  { core := { s.core with
                      repr := repr64Set s.core.repr (src_lit >>> 1).toNat (resC + 1) }
                    scratch := { s.scratch with ant_sz := ant } } ⋆ R) m := by
                have h3 : (BitVec.setWidth 64 (src_lit >>> 1)).toNat = (src_lit >>> 1).toNat := by
                  c0_bound
                rw [h3] at hm; exact hm
              exact hJant ⟨resC, _, s.core.min_clr, s.core.tmp_cnt⟩ m
                ⟨hinv', htc_le, hmclr_ok, hm'⟩
          · c0_hsteps
            · exact hJc 0x3FFFFFFFFFFFFFFF#64 m rfl
            · exact hJc res m rfl
        · have hinv0 : FullDenseInvNoLm c F0 F_cur
              { core := s.core, scratch := { s.scratch with ant_sz := ant } } :=
            fullDenseInvNoLm_with_core_aux hinv hrepr_len hmclr_len hcl.tmp_len_arr hcl.flags_len
              hcl.tmp_len_le { hsc with } rfl rfl
          exact hJant ⟨res, s.core.repr, s.core.min_clr, s.core.tmp_cnt⟩ m
            ⟨hinv0, htc_le, hmclr_ok, hm⟩
      · c0_hsteps
        · have hsgn_lt : sgn.toNat < 2 := by c0_bound
          have hsl_nat : (((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn).toNat =
              2 * (src_lit >>> (1 : Nat)).toNat + sgn.toNat := by
            have hs01 : sgn.toNat = 0 ∨ sgn.toNat = 1 := by omega
            rcases hs01 with h0 | h1
            · have hs0 : sgn = 0#32 := BitVec.eq_of_toNat_eq h0; subst hs0
              rw [BitVec.or_zero]; c0_bound
            · have hs1 : sgn = 1#32 := BitVec.eq_of_toNat_eq h1; subst hs1
              rw [FullBvaFwdTactics.bv32_or1_of_even (by c0_bound)]; c0_bound
          have hsl_lt : (((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn).toNat <
              2 * s.core.cur_vars := by omega
          obtain ⟨hbd_sl, hslice_sl⟩ := m7_hop_wvec_bounds hinv hsl_lt
          let sl : BitVec 32 := ((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn
          have hsl_lt_sl : sl.toNat < 2 * s.core.cur_vars := hsl_lt
          have hwv_sl0 : (BitVec.setWidth 64 sl <<< (1 : Nat)).toNat < s.core.wvec.length := by
            c0_bound
          have hwv_sl1 : ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1).toNat <
              s.core.wvec.length := by
            change ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1#64).toNat < _; c0_bound
          have hoff_eq : (s.core.wvec[2 * sl.toNat]'(by omega)).toNat =
              fullWatchOffCore s.core sl.toNat := by
            unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have hsz_eq : (s.core.wvec[2 * sl.toNat + 1]'(by omega)).toNat =
              fullWatchSizeCore s.core sl.toNat := by
            unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          let off0 := fullWatchOffCore s.core sl.toNat
          let sz0 := fullWatchSizeCore s.core sl.toNat
          have hoff_sz_le : off0 + sz0 ≤ s.core.wlen := hbd_sl
          have h2sl0 : (BitVec.setWidth 64 sl <<< (1 : Nat)).toNat = 2 * sl.toNat := by c0_bound
          have h2sl1 : ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1).toNat = 2 * sl.toNat + 1 := by
            change ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1#64).toNat = _; c0_bound
          have hoff_c0 : (BitVec.setWidth 64
              (s.core.wvec[(BitVec.setWidth 64 sl <<< (1 : Nat)).toNat]'hwv_sl0)).toNat = off0 := by
            rw [bv64_setWidth_32]; simp only [h2sl0]; exact hoff_eq
          have hmod0 : 2 * sl.toNat % 2 ^ 64 = 2 * sl.toNat := Nat.mod_eq_of_lt (by omega)
          have hmod1 : (2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * sl.toNat + 1 :=
            by c0_bound
          have hend_mod : ((s.core.wvec[2 * sl.toNat % 2 ^ 64]'(by rw [hmod0]; omega)).toNat +
              (s.core.wvec[(2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                rw [hmod1]; omega)).toNat) % 2 ^ 64 = off0 + sz0 := by
            simp only [hmod0, hmod1, hoff_eq, hsz_eq]; exact Nat.mod_eq_of_lt (by omega)
          c0_hsteps_nogrp
          refine wp_loop_inv
            (fun (res1, antp, p, ()) mlp =>
              off0 ≤ p.toNat ∧ p.toNat ≤ off0 + sz0 ∧ antp.toNat ≤ ant.toNat ∧
              DenseWatchSliceOk F_cur s.core sl.toNat p.toNat (off0 + sz0 - p.toNat) ∧ mlp = m)
            (fun (_, _, p, _) _ => off0 + sz0 - p.toNat)
            (fun Jp hJp => by
              c0_hfast
              exact hJp (res, ant, _, ()) m ⟨by rw [hoff_c0]; exact Nat.le_refl _,
                by rw [hoff_c0]; omega, Nat.le_refl _,
                by rw [hoff_c0, Nat.add_sub_cancel_left]; exact hslice_sl, rfl⟩)
            (fun Jp (res1, antp, p, ()) mlp ⟨hp_ge, hp_le, hantp_le, hrem, hmlp⟩ ihp => ?_)
          subst mlp
          c0_hfast
          · have hp_lt : p.toNat < off0 + sz0 := by rw [← hend_mod]; assumption
            have hp_ws : p.toNat < s.core.wstk.length := by omega
            have hant1 : (antp - 1#64).toNat ≤ ant.toNat := by simp only [bv_c0]; omega
            have hp1_n : (p + 1).toNat = p.toNat + 1 := by
              change (p + 1#64).toNat = _; simp only [bv_c0]; omega
            have hp1_mod : (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
              rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
            c0_hfast
            · have ⟨_, _, hrem_next⟩ := FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hp_ws
                (by assumption)
              exact ihp (_, antp - 1#64, p + 1, ()) m (by dsimp only; rw [hp1_n]; omega)
                ⟨by rw [hp1_n]; omega, by rw [hp1_n]; omega, hant1,
                 by rw [hp1_n, show off0 + sz0 - (p.toNat + 1) = off0 + sz0 - p.toNat - 1 by omega]
                    exact hrem_next, rfl⟩
            · have ⟨_, _, hrem_next⟩ := FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hp_ws
                (by assumption)
              exact ihp (_, antp - 1#64, p + 1, ()) m (by dsimp only; rw [hp1_n]; omega)
                ⟨by rw [hp1_n]; omega, by rw [hp1_n]; omega, hant1,
                 by rw [hp1_n, show off0 + sz0 - (p.toNat + 1) = off0 + sz0 - p.toNat - 1 by omega]
                    exact hrem_next, rfl⟩
            · have ⟨h2le, hrem_next⟩ := FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws
                (by assumption)
              have hp1_ws : p.toNat + 1 < s.core.wstk.length := by omega
              have ⟨_, hcr_ref, _⟩ := FullBvaFwdHelpers.fwd_slice_occ_info hrem (by omega) hp_ws
                hp1_ws (by assumption)
              have hcr_wf := hinv.2.1.arena.refs_wf _ hcr_ref
              have hp2_n : (p + 1 + 1).toNat = p.toNat + 2 := by
                change (p + 1#64 + 1#64).toNat = _; simp only [bv_c0]; omega
              let cr := s.core.wstk[p.toNat + 1]'hp1_ws
              have hcr_al : cr.toNat + 3 + fullArenaClauseSizeCore s.core cr.toNat ≤
                  s.core.arena_len := by
                have h1 := hcr_wf.2.2.1; have h2 := hcr_wf.2.2.2.1; dsimp only [cr]; omega
              have hcr_eq : s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws) = cr := by
                dsimp only [cr]; simp only [hp1_n]
              have hcr0_eq : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat = cr.toNat := by
                rw [bv64_setWidth_32, hcr_eq]
              have hcr_b0 : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat <
                  s.core.arena.length := by rw [hcr0_eq]; omega
              have hcr2_eq : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 2).toNat =
                  cr.toNat + 2 := by
                change (BitVec.setWidth 64 _ + 2#64).toNat = _
                rw [hcr_eq]; simp only [bv_c0]; omega
              have hcr_b2 : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 2).toNat <
                  s.core.arena.length := by rw [hcr2_eq]; omega
              have hsz_cr : (s.core.arena[cr.toNat + 2]'(by omega)).toNat =
                  fullArenaClauseSizeCore s.core cr.toNat := by
                unfold fullArenaClauseSizeCore
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              have hcr_sz_le : cr.toNat + 3 + (s.core.arena[cr.toNat + 2]'(by omega)).toNat ≤
                  s.core.arena.length := by rw [hsz_cr]; omega
              have hci0_bv : BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 3 =
                  BitVec.setWidth 64 cr + 3 := by rw [hcr_eq]
              have hci0_n : (BitVec.setWidth 64 cr + 3).toNat = cr.toNat + 3 := by
                change (BitVec.setWidth 64 cr + 3#64).toNat = _; simp only [bv_c0]; omega
              have hcend_n : (BitVec.setWidth 64 cr + 3 +
                  BitVec.setWidth 64 (s.core.arena[cr.toNat + 2]'(by omega))).toNat =
                  cr.toNat + 3 + (s.core.arena[cr.toNat + 2]'(by omega)).toNat := by
                change (BitVec.setWidth 64 cr + 3#64 +
                  BitVec.setWidth 64 (s.core.arena[cr.toNat + 2]'(by omega))).toNat = _
                simp only [bv_c0]; omega
              c0_hfast
              · clear hQ ihs hJend
                let ci0 : BitVec 64 := BitVec.setWidth 64 cr + 3
                let cend : BitVec 64 :=
                  ci0 + BitVec.setWidth 64 (s.core.arena[cr.toNat + 2]'(by omega))
                have hle0 : ci0.toNat ≤ cend.toNat := by
                  dsimp only [ci0, cend]; rw [hci0_n, hcend_n]; omega
                refine wp_loop_inv
                  (fun (resk, ci, ()) mk =>
                    ci.toNat ≤ cend.toNat ∧ mk = m)
                  (fun (_, ci, _) _ => cend.toNat - ci.toNat)
                  (fun Jk hJk => by
                    c0_hfast
                    exact hJk (res1, _, ()) m ⟨by
                      dsimp only [ci0, cend] at hle0
                      rw [hci0_bv]; exact hle0, rfl⟩)
                  (fun Jk (resk, ci, ()) mk ⟨hci_le, hmk⟩ ihk => ?_)
                subst mk; c0_hsplit
                · have hcr2_mod : (cr.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 =
                      cr.toNat + 2 := by
                    rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
                  have hci_lt : ci.toNat < cend.toNat := by
                    dsimp only [cend, ci0]; rw [hcend_n]
                    simp only [hp1_mod] at hc
                    change ci.toNat < (cr.toNat + BitVec.toNat (3 : BitVec 64) +
                      (s.core.arena[(cr.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                        rw [hcr2_mod]; omega)).toNat) % 2 ^ 64 at hc
                    simp only [hcr2_mod, show BitVec.toNat (3 : BitVec 64) = 3 from rfl] at hc
                    exact Nat.lt_of_lt_of_le hc (Nat.mod_le _ _)
                  have hcend_len : cend.toNat ≤ s.core.arena.length := by
                    dsimp only [cend, ci0]; rw [hcend_n]; exact hcr_sz_le
                  have hci_b : ci.toNat < s.core.arena.length := by omega
                  have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := by
                    simp only [bv_c0]; omega
                  c0_hfast
                  all_goals
                    exact ihk (_, ci + 1#64, ()) m (by dsimp only; rw [hci1]; omega)
                      ⟨by rw [hci1]; exact hci_lt, rfl⟩
                · c0_hfast
                  exact ihp (resk, antp - 1#64, p + 1 + 1, ()) m (by dsimp only; rw [hp2_n]; omega)
                    ⟨by rw [hp2_n]; omega, by rw [hp2_n]; omega, hant1,
                     by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                          by omega]; exact hrem_next, rfl⟩
              · exact ihp (res1, antp - 1#64, p + 1 + 1, ()) m (by dsimp only; rw [hp2_n]; omega)
                  ⟨by rw [hp2_n]; omega, by rw [hp2_n]; omega, hant1,
                   by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                        by omega]; exact hrem_next, rfl⟩
            · exfalso
              have ⟨h2le, _⟩ := FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws
                (by assumption)
              have hge : ¬ (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 <
                  ((s.core.wvec[2 * sl.toNat % 2 ^ 64]'(by rw [hmod0]; omega)).toNat +
                   (s.core.wvec[(2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                     rw [hmod1]; omega)).toNat) % 2 ^ 64 := by assumption
              rw [hend_mod, hp1_mod] at hge; omega
          all_goals
            exact ihs (res1, antp, sgn + 1#32, ()) m (by simp only [bv_c0]; omega)
              ⟨by simp only [bv_c0]; omega, Nat.le_trans hantp_le hant_le, rfl⟩
        · exact hJend () m rfl
        · exact hJend () m rfl
    · c0_hsteps
      · exact hJ0 1#64 m rfl
      · exact hJ0 0#64 m rfl

/-- Exact canonical `fullBvaHop2Spec` correctness for sunk-local `full_bva_hop2_m7_body`. -/
theorem full_bva_hop2_m7_wp (Γ : Env)
    (hHop1 : ∀ args m Q X, fullBvaHop1Spec args m Q X →
      Γ "full_bva_hop1" [i64, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, fullBvaHop2Spec args m Q X →
      Func.wp Γ full_bva_hop2_m7_body args m Q X := by
  rintro ⟨h, src_lit, dst_idx, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hsrc_lt, htc_le, htl_le, hmclr_ok, hshrk_ok, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena
  unfold dimacsBound at hmx hwcap har_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hsig_len := hsc.sim_sig_len
  have hshrk_len := hsc.shrink_stk_len
  have hwv_len := hcl.wvec_len; have hws_len := hcl.wstk_len_arr; have har_len := hcl.arena_len_arr
  have hwlen_le := hcl.wlen_le; have hal_le := hcl.arena_len_le
  have hsidx_lt : (src_lit >>> 1).toNat < s.core.cur_vars := by rw [bv32_lshr1_nat]; omega
  c0_hsteps_nogrp
  · exact hQ _ s.core.repr s.core.min_clr s.core.tmp_cnt s.core.tmp_len s.scratch.ant_sz
      s.scratch.sim_sig s.scratch.shrink_stk m hinv htc_le htl_le hmclr_ok hshrk_ok
      (Nat.le_refl _) hm
  · refine wp_join_state1 (t := i64) (α := BitVec 64) (fun r => r) (fun _ ml => m = ml)
      (fun _ res0 ml hml => ?_) (fun J0 hJ0 => ?_)
    · rcases hml with rfl
      c0_hsteps_nogrp
      let mkSt (rp mc : List (BitVec 32)) (tc : Nat) (ant : BitVec 64) : FullState :=
        { core := { s.core with repr := rp, min_clr := mc, tmp_cnt := tc }
          scratch := { s.scratch with ant_sz := ant } }
      refine wp_loop_inv
        (fun (res, sgn, ()) ml => ∃ rp mc tc ant,
          sgn.toNat ≤ 2 ∧ tc ≤ s.core.cur_vars ∧ ant.toNat ≤ s.scratch.ant_sz.toNat ∧
          FullDenseInvNoLm c F0 F_cur (mkSt rp mc tc ant) ∧
          (∀ i < tc, (mc[i]?.getD 0#32).toNat < c.max_vars) ∧
          (FullMem c (mkSt rp mc tc ant) ⋆ R) ml)
        (fun (_, sgn, _) _ => 2 - sgn.toNat)
        (fun Js hJs => by
          c0_hsteps; exact hJs (res0, 0#32, ()) m
            ⟨s.core.repr, s.core.min_clr, s.core.tmp_cnt, s.scratch.ant_sz, by decide, htc_le,
             Nat.le_refl _, hinv, hmclr_ok, hm⟩)
        (fun Js (res, sgn, ()) ml
            ⟨rp, mc, tc, ant, hsgn_le, htc, hant, hinv_s, hmc_ok, hml⟩ ihs => ?_)
      c0_hsteps_nogrp
      refine wp_join_state0
        (α := List (BitVec 32) × List (BitVec 32) × Nat × BitVec 64)
        (fun ⟨rpF, mcF, tcF, antF⟩ mf =>
          tcF ≤ s.core.cur_vars ∧ antF.toNat ≤ s.scratch.ant_sz.toNat ∧
          FullDenseInvNoLm c F0 F_cur (mkSt rpF mcF tcF antF) ∧
          (∀ i < tcF, (mcF[i]?.getD 0#32).toNat < c.max_vars) ∧
          (FullMem c (mkSt rpF mcF tcF antF) ⋆ R) mf)
        (fun _ ⟨rpF, mcF, tcF, antF⟩ mf ⟨htcF, hantF, hinvF, hmcF, hmf⟩ => ?_)
        (fun Jend hJend => ?_)
      · dsimp only [mkSt] at hmf hinvF
        c0_hsteps_nogrp
        refine wp_join_state1 (t := i64)
          (α := BitVec 64 × Nat × List (BitVec 64) × List (BitVec 32)) (fun st => st.1)
          (fun ⟨_resF, tlF, sigF, shrkF⟩ mf1 =>
            FullDenseInvNoLm c F0 F_cur
              { core := { s.core with repr := rpF, min_clr := mcF, tmp_cnt := tcF,
                                      tmp_len := tlF }
                scratch := { s.scratch with ant_sz := antF, sim_sig := sigF,
                                            shrink_stk := shrkF } } ∧
            tlF ≤ s.core.cur_vars ∧
            (∀ i < tlF, (shrkF[i]?.getD 0#32).toNat < c.max_vars) ∧
            (FullMem c
              { core := { s.core with repr := rpF, min_clr := mcF, tmp_cnt := tcF,
                                      tmp_len := tlF }
                scratch := { s.scratch with ant_sz := antF, sim_sig := sigF,
                                            shrink_stk := shrkF } } ⋆ R) mf1)
          (fun _ ⟨resF, tlF, sigF, shrkF⟩ mf1 ⟨hinv1, htl1, hshrk1, hmf1⟩ => by
            c0_hsteps
            exact hQ resF rpF mcF tcF tlF antF sigF shrkF mf1 hinv1 htcF htl1 hmcF hshrk1 hantF
              hmf1)
          (fun Jant hJant => ?_)
        c0_hsteps_nogrp
        · refine wp_join_state1 (t := i64) (α := BitVec 64) (fun r => r) (fun _ ml => mf = ml)
            (fun _ resC ml hml => ?_) (fun Jc hJc => ?_)
          · rcases hml with rfl
            c0_hsteps
            · have htl1 : s.core.tmp_len + 1 ≤ s.core.cur_vars := by c0_bound
              let sc1 : FullScratch :=
                { s.scratch with
                  ant_sz := antF
                  sim_sig := s.scratch.sim_sig.set (src_lit >>> 1).toNat (resC + 1)
                  shrink_stk := s.scratch.shrink_stk.set s.core.tmp_len (src_lit >>> 1) }
              have hinv' := fullDenseInvNoLm_with_core_aux (tc' := tcF) (tl' := s.core.tmp_len + 1)
                (sc' := sc1) hinvF hinvF.1.core_ok.repr_len hinvF.1.core_ok.min_clr_len_arr
                hcl.tmp_len_arr hcl.flags_len (by omega)
                { hsc with sim_sig_len := by simp [sc1, hsig_len],
                           shrink_stk_len := by simp [sc1, hshrk_len] }
                rfl rfl
              have hm' : (FullMem c
                  { core := { s.core with repr := rpF, min_clr := mcF, tmp_cnt := tcF,
                                          tmp_len := s.core.tmp_len + 1 }
                    scratch := sc1 } ⋆ R) m := by
                have h1 : (BitVec.ofNat 64 s.core.tmp_len + 1).toNat = s.core.tmp_len + 1 := by
                  change (BitVec.ofNat 64 s.core.tmp_len + 1#64).toNat = _; c0_bound
                have h2 : (BitVec.ofNat 64 s.core.tmp_len).toNat = s.core.tmp_len := by c0_bound
                have h3 : (BitVec.setWidth 64 (src_lit >>> 1)).toNat = (src_lit >>> 1).toNat := by
                  c0_bound
                dsimp only [sc1]; rw [h1, h2, h3] at hm; exact hm
              exact hJant ⟨resC, s.core.tmp_len + 1, _, _⟩ m
                ⟨by dsimp only [sc1] at hinv'; exact hinv', htl1, fun i hi => by
                  by_cases hie : i = s.core.tmp_len
                  · subst hie; rw [List.getElem?_set_self (by omega), Option.getD_some]; omega
                  · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hshrk_ok i (by omega), hm'⟩
            · let sc2 : FullScratch :=
                { s.scratch with
                  ant_sz := antF
                  sim_sig := s.scratch.sim_sig.set (src_lit >>> 1).toNat (resC + 1) }
              have hinv' := fullDenseInvNoLm_with_core_aux (tc' := tcF) (tl' := s.core.tmp_len)
                (sc' := sc2) hinvF hinvF.1.core_ok.repr_len hinvF.1.core_ok.min_clr_len_arr
                hcl.tmp_len_arr hcl.flags_len hcl.tmp_len_le
                { hsc with sim_sig_len := by simp [sc2, hsig_len] } rfl rfl
              have hm' : (FullMem c
                  { core := { s.core with repr := rpF, min_clr := mcF, tmp_cnt := tcF }
                    scratch := sc2 } ⋆ R) m := by
                have h3 : (BitVec.setWidth 64 (src_lit >>> 1)).toNat = (src_lit >>> 1).toNat := by
                  c0_bound
                dsimp only [sc2]; rw [h3] at hm; exact hm
              exact hJant ⟨resC, s.core.tmp_len, _, s.scratch.shrink_stk⟩ m
                ⟨by dsimp only [sc2] at hinv'; exact hinv', htl_le, hshrk_ok, hm'⟩
          · c0_hsteps
            · exact hJc 0x3FFFFFFFFFFFFFFF#64 mf rfl
            · exact hJc res mf rfl
        · exact hJant ⟨res, s.core.tmp_len, s.scratch.sim_sig, s.scratch.shrink_stk⟩ mf
            ⟨hinvF, htl_le, hshrk_ok, hmf⟩
      · dsimp only [mkSt] at hml
        c0_hsteps
        · have hsgn_lt : sgn.toNat < 2 := by c0_bound
          have hsl_nat : (((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn).toNat =
              2 * (src_lit >>> (1 : Nat)).toNat + sgn.toNat := by
            have hs01 : sgn.toNat = 0 ∨ sgn.toNat = 1 := by omega
            rcases hs01 with h0 | h1
            · have hs0 : sgn = 0#32 := BitVec.eq_of_toNat_eq h0; subst hs0
              rw [BitVec.or_zero]; c0_bound
            · have hs1 : sgn = 1#32 := BitVec.eq_of_toNat_eq h1; subst hs1
              rw [FullBvaFwdTactics.bv32_or1_of_even (by c0_bound)]; c0_bound
          have hsl_lt : (((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn).toNat <
              2 * s.core.cur_vars := by omega
          obtain ⟨hbd_sl, hslice_sl⟩ := m7_hop_wvec_bounds hinv hsl_lt
          let sl : BitVec 32 := ((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn
          have hsl_lt_sl : sl.toNat < 2 * s.core.cur_vars := hsl_lt
          have hwv_sl0 : (BitVec.setWidth 64 sl <<< (1 : Nat)).toNat < s.core.wvec.length := by
            c0_bound
          have hwv_sl1 : ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1).toNat <
              s.core.wvec.length := by
            change ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1#64).toNat < _; c0_bound
          have hoff_eq : (s.core.wvec[2 * sl.toNat]'(by omega)).toNat =
              fullWatchOffCore s.core sl.toNat := by
            unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have hsz_eq : (s.core.wvec[2 * sl.toNat + 1]'(by omega)).toNat =
              fullWatchSizeCore s.core sl.toNat := by
            unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          let off0 := fullWatchOffCore s.core sl.toNat
          let sz0 := fullWatchSizeCore s.core sl.toNat
          have hoff_sz_le : off0 + sz0 ≤ s.core.wlen := hbd_sl
          have h2sl0 : (BitVec.setWidth 64 sl <<< (1 : Nat)).toNat = 2 * sl.toNat := by c0_bound
          have h2sl1 : ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1).toNat = 2 * sl.toNat + 1 := by
            change ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1#64).toNat = _; c0_bound
          have hoff_c0 : (BitVec.setWidth 64
              (s.core.wvec[(BitVec.setWidth 64 sl <<< (1 : Nat)).toNat]'hwv_sl0)).toNat = off0 := by
            rw [bv64_setWidth_32]; simp only [h2sl0]; exact hoff_eq
          have hmod0 : 2 * sl.toNat % 2 ^ 64 = 2 * sl.toNat := Nat.mod_eq_of_lt (by omega)
          have hmod1 : (2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * sl.toNat + 1 :=
            by c0_bound
          have hend_mod : ((s.core.wvec[2 * sl.toNat % 2 ^ 64]'(by rw [hmod0]; omega)).toNat +
              (s.core.wvec[(2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                rw [hmod1]; omega)).toNat) % 2 ^ 64 = off0 + sz0 := by
            simp only [hmod0, hmod1, hoff_eq, hsz_eq]; exact Nat.mod_eq_of_lt (by omega)
          c0_hsteps_nogrp
          refine wp_loop_inv
            (fun (res1, p, ()) mlp => ∃ rpp mcp tcp antp,
              off0 ≤ p.toNat ∧ p.toNat ≤ off0 + sz0 ∧ tcp ≤ s.core.cur_vars ∧
              antp.toNat ≤ ant.toNat ∧ FullDenseInvNoLm c F0 F_cur (mkSt rpp mcp tcp antp) ∧
              (∀ i < tcp, (mcp[i]?.getD 0#32).toNat < c.max_vars) ∧
              DenseWatchSliceOk F_cur s.core sl.toNat p.toNat (off0 + sz0 - p.toNat) ∧
              (FullMem c (mkSt rpp mcp tcp antp) ⋆ R) mlp)
            (fun (_, p, _) _ => off0 + sz0 - p.toNat)
            (fun Jp hJp => by
              c0_hfast
              exact hJp (res, _, ()) ml ⟨rp, mc, tc, ant, by rw [hoff_c0]; exact Nat.le_refl _,
                by rw [hoff_c0]; omega, htc, Nat.le_refl _, hinv_s, hmc_ok,
                by rw [hoff_c0, Nat.add_sub_cancel_left]; exact hslice_sl, hml⟩)
            (fun Jp (res1, p, ()) mlp ⟨rpp, mcp, tcp, antp, hp_ge, hp_le, htcp, hantp, hinvp,
                hmcp_ok, hrem, hmlp⟩ ihp => ?_)
          dsimp only [mkSt] at hmlp
          c0_hfast
          · have hp_lt : p.toNat < off0 + sz0 := by rw [← hend_mod]; assumption
            have hp_ws : p.toNat < s.core.wstk.length := by omega
            have hant1 : (antp - 1#64).toNat ≤ ant.toNat := by simp only [bv_c0]; omega
            have hp1_n : (p + 1).toNat = p.toNat + 1 := by
              change (p + 1#64).toNat = _; simp only [bv_c0]; omega
            have hp1_mod : (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
              rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
            have hinvp1 : FullDenseInvNoLm c F0 F_cur (mkSt rpp mcp tcp (antp - 1#64)) :=
              fullDenseInvNoLm_with_core_aux (tc' := tcp) (tl' := s.core.tmp_len) hinvp
                hinvp.1.core_ok.repr_len hinvp.1.core_ok.min_clr_len_arr hcl.tmp_len_arr
                hcl.flags_len hcl.tmp_len_le { hsc with } rfl rfl
            c0_hfast
            · have ⟨hot_lt, _, hrem_next⟩ :=
                FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hp_ws (by assumption)
              c0_call hHop1
              refine ⟨c, F0, F_cur, mkSt rpp mcp tcp (antp - 1#64), R, rfl, hinvp1, hot_lt, htcp,
                hmcp_ok, hm, fun r1 rp1 mc1 tc1 ant1 m1 hinv1 htc1 hmc1 hant1' hm1 => ?_⟩
              c0_hfast
              exact ihp (res1 + r1, p + 1, ()) m1 (by dsimp only; rw [hp1_n]; omega)
                ⟨rp1, mc1, tc1, ant1, by rw [hp1_n]; omega, by rw [hp1_n]; omega, htc1,
                 Nat.le_trans hant1' hant1, hinv1, hmc1,
                 by rw [hp1_n, show off0 + sz0 - (p.toNat + 1) = off0 + sz0 - p.toNat - 1 by omega]
                    exact hrem_next, hm1⟩
            · have hm_flat : (FullMem c
                  { core := { s.core with repr := rpp, min_clr := mcp, tmp_cnt := tcp },
                    scratch := { s.scratch with ant_sz := antp - 1#64 } } ⋆ R) m := hm
              clear hm
              have ⟨h2le, hrem_next⟩ := FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws
                (by assumption)
              have hp1_ws : p.toNat + 1 < s.core.wstk.length := by omega
              have ⟨_, hcr_ref, _⟩ := FullBvaFwdHelpers.fwd_slice_occ_info hrem (by omega) hp_ws
                hp1_ws (by assumption)
              have hcr_wf := hinv.2.1.arena.refs_wf _ hcr_ref
              have hp2_n : (p + 1 + 1).toNat = p.toNat + 2 := by
                change (p + 1#64 + 1#64).toNat = _; simp only [bv_c0]; omega
              let cr := s.core.wstk[p.toNat + 1]'hp1_ws
              have hcr_al : cr.toNat + 3 + fullArenaClauseSizeCore s.core cr.toNat ≤
                  s.core.arena_len := by
                have h1 := hcr_wf.2.2.1; have h2 := hcr_wf.2.2.2.1; dsimp only [cr]; omega
              have hcr_eq : s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws) = cr := by
                dsimp only [cr]; simp only [hp1_n]
              have hcr0_eq : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat = cr.toNat := by
                rw [bv64_setWidth_32, hcr_eq]
              have hcr_b0 : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat <
                  s.core.arena.length := by rw [hcr0_eq]; omega
              have hcr2_eq : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 2).toNat =
                  cr.toNat + 2 := by
                change (BitVec.setWidth 64 _ + 2#64).toNat = _
                rw [hcr_eq]; simp only [bv_c0]; omega
              have hcr_b2 : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 2).toNat <
                  s.core.arena.length := by rw [hcr2_eq]; omega
              have hsz_cr : (s.core.arena[cr.toNat + 2]'(by omega)).toNat =
                  fullArenaClauseSizeCore s.core cr.toNat := by
                unfold fullArenaClauseSizeCore
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              have hcr_sz_le : cr.toNat + 3 + (s.core.arena[cr.toNat + 2]'(by omega)).toNat ≤
                  s.core.arena.length := by rw [hsz_cr]; omega
              c0_hfast
              · have hng_cr : fullArenaClauseGarbCore s.core cr.toNat = false := by
                  unfold fullArenaClauseGarbCore fullArenaHdrCore
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  have h1 : s.core.arena[(BitVec.setWidth 64
                      (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat]'hcr_b0 &&&
                      (524288#32 ||| 4194304#32) = 0#32 := by assumption
                  exact FullBvaFwdHelpers.garb_false_of_and_garb_red_eq_zero (by
                    simpa only [hcr0_eq] using h1)
                clear hQ ihs hJend
                refine wp_loop_inv
                  (fun (resk, k, ()) mk => ∃ rpk mck tck antk,
                    k.toNat ≤ (s.core.arena[cr.toNat + 2]'(by omega)).toNat ∧
                    tck ≤ s.core.cur_vars ∧ antk.toNat ≤ ant.toNat ∧
                    FullDenseInvNoLm c F0 F_cur (mkSt rpk mck tck antk) ∧
                    (∀ i < tck, (mck[i]?.getD 0#32).toNat < c.max_vars) ∧
                    (FullMem c (mkSt rpk mck tck antk) ⋆ R) mk)
                  (fun (_, k, _) _ => (s.core.arena[cr.toNat + 2]'(by omega)).toNat - k.toNat)
                  (fun Jk hJk => by
                    c0_hfast; exact hJk (res1, 0#32, ()) m
                      ⟨rpp, mcp, tcp, antp - 1#64, Nat.zero_le _, htcp, hant1, hinvp1, hmcp_ok,
                       hm_flat⟩)
                  (fun Jk (resk, k, ()) mk ⟨rpk, mck, tck, antk, hk_le, htck, hantk, hinvk,
                      hmck_ok, hmk⟩ ihk => ?_)
                dsimp only [mkSt] at hmk
                c0_hsplit
                · have hk_lt : k.toNat < (s.core.arena[cr.toNat + 2]'(by omega)).toNat := by
                    have h1 : k.toNat < (s.core.arena[(BitVec.setWidth 64
                        (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) +
                        2).toNat]'hcr_b2).toNat := by assumption
                    simpa only [hcr2_eq] using h1
                  have hk1 : (k + 1#32).toNat = k.toNat + 1 := by simp only [bv_c0]; omega
                  c0_hsplit
                  · have hcrk_b : (BitVec.setWidth 64
                        (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 3 +
                        BitVec.setWidth 64 k).toNat < s.core.arena.length := by
                      change (BitVec.setWidth 64 _ + 3#64 + BitVec.setWidth 64 k).toNat < _
                      rw [hcr_eq]; simp only [bv_c0]; omega
                    have hol_mem : (s.core.arena[cr.toNat + 3 + k.toNat]'(by omega)).toNat ∈
                        fullArenaClauseLitsCore s.core cr.toNat :=
                      List.mem_of_getElem? (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem
                        (by rw [← hsz_cr]; exact hk_lt) (by omega))
                    have hol_lt := hinv.2.1.arena.lits_lt cr.toNat hcr_ref hng_cr _ hol_mem
                    have hcrk_eq : (BitVec.setWidth 64 cr + 3 + BitVec.setWidth 64 k).toNat =
                        cr.toNat + 3 + k.toNat := by
                      change (BitVec.setWidth 64 cr + 3#64 + BitVec.setWidth 64 k).toNat = _
                      simp only [bv_c0]; omega
                    c0_hfast
                    · c0_call hHop1
                      refine ⟨c, F0, F_cur, mkSt rpk mck tck antk, R, rfl, hinvk, ?_, htck, hmck_ok,
                        hmk, fun r1 rp1 mc1 tc1 ant1 m1 hinv1 htc1 hmc1 hant1' hm1 => ?_⟩
                      · simpa only [hcr_eq, hcrk_eq] using hol_lt
                      · c0_hfast
                        exact ihk (resk + r1, k + 1#32, ()) m1 (by dsimp only; rw [hk1]; omega)
                          ⟨rp1, mc1, tc1, ant1, by rw [hk1]; omega, htc1,
                           Nat.le_trans hant1' hantk, hinv1, hmc1, hm1⟩
                    · exact ihk (resk, k + 1#32, ()) mk (by dsimp only; rw [hk1]; omega)
                        ⟨rpk, mck, tck, antk, by rw [hk1]; omega, htck, hantk, hinvk, hmck_ok, hmk⟩
                  · c0_hfast
                    exact ihp (resk, p + 1 + 1, ()) mk (by dsimp only; rw [hp2_n]; omega)
                      ⟨rpk, mck, tck, antk, by rw [hp2_n]; omega, by rw [hp2_n]; omega, htck, hantk,
                       hinvk, hmck_ok,
                       by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                            by omega]; exact hrem_next, hmk⟩
                · c0_hfast
                  exact ihp (resk, p + 1 + 1, ()) mk (by dsimp only; rw [hp2_n]; omega)
                    ⟨rpk, mck, tck, antk, by rw [hp2_n]; omega, by rw [hp2_n]; omega, htck, hantk,
                     hinvk, hmck_ok,
                     by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                          by omega]; exact hrem_next, hmk⟩
              · exact ihp (res1, p + 1 + 1, ()) m (by dsimp only; rw [hp2_n]; omega)
                  ⟨rpp, mcp, tcp, antp - 1#64, by rw [hp2_n]; omega, by rw [hp2_n]; omega, htcp,
                   hant1, hinvp1, hmcp_ok,
                   by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                        by omega]; exact hrem_next, hm_flat⟩
            · exfalso
              have ⟨h2le, _⟩ := FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws
                (by assumption)
              have hge : ¬ (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 <
                  ((s.core.wvec[2 * sl.toNat % 2 ^ 64]'(by rw [hmod0]; omega)).toNat +
                   (s.core.wvec[(2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                     rw [hmod1]; omega)).toNat) % 2 ^ 64 := by assumption
              rw [hend_mod, hp1_mod] at hge; omega
          all_goals
            exact ihs (res1, sgn + 1#32, ()) mlp (by simp only [bv_c0]; omega)
              ⟨rpp, mcp, tcp, antp, by simp only [bv_c0]; omega, htcp, Nat.le_trans hantp hant,
               hinvp, hmcp_ok, hmlp⟩
        · exact hJend ⟨rp, mc, tc, ant⟩ ml ⟨htc, hant, hinv_s, hmc_ok, hml⟩
        · exact hJend ⟨rp, mc, tc, ant⟩ ml ⟨htc, hant, hinv_s, hmc_ok, hml⟩
    · c0_hsteps
      · exact hJ0 1#64 m rfl
      · exact hJ0 0#64 m rfl

/-! ## 2. Closed `m7HotHop1Env`, `ModuleOk`, Drop-ins, & Concrete UNSAT Non-Vacuity -/

/-- Closed `2`-row specification table for `m7HotHop1Module` (`noExit := true`). -/
def m7HotHop1SpecTable : List SpecEntry :=
  [ ⟨"full_bva_hop1", [i64, i32, i32], [i64], fullBvaHop1Spec, true⟩
  , ⟨"full_bva_hop2", [i64, i32, i32], [i64], fullBvaHop2Spec, true⟩
  ]

/-- Closed specification environment for `m7HotHop1Module`. -/
def m7HotHop1Env : Env :=
  Env.ofTable m7HotHop1SpecTable

theorem m7HotHop1SpecTable_nodup : (m7HotHop1SpecTable.map SpecEntry.name).Nodup := by
  decide

theorem m7HotHop1SpecTable_noExit : ∀ e ∈ m7HotHop1SpecTable, e.noExit = true := by
  intro e he
  simp only [m7HotHop1SpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> rfl

theorem m7HotHop1Env_noExit :
    ∀ f as bs xs m Q X X',
      m7HotHop1Env f as bs xs m Q X → m7HotHop1Env f as bs xs m Q X' :=
  Env.ofTable_noExit m7HotHop1SpecTable_noExit

private theorem m7HotHop1Env_mem {e : SpecEntry} (he : e ∈ m7HotHop1SpecTable)
    {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X : XPost}
    (hno : e.noExit = true := by rfl)
    (h : e.spec xs m Q (fun _ _ _ _ => False)) :
    m7HotHop1Env e.name e.as e.rs xs m Q X :=
  Env.ofTable_of_mem he m7HotHop1SpecTable_nodup
    (by dsimp only [SpecEntry.eff]; rw [hno]; exact h)

/-- Drop-in `Fn` correctness for `m7Hop1Fn` against canonical `fullBvaHop1Spec`. -/
theorem m7Hop1Fn_wp (Γ : Env) :
    ∀ args m Q X, fullBvaHop1Spec args m Q X → Func.wp Γ m7Hop1Fn.body args m Q X :=
  full_bva_hop1_m7_wp Γ

/-- Drop-in `Fn` correctness for `m7Hop2Fn` against canonical `fullBvaHop2Spec`. -/
theorem m7Hop2Fn_wp (Γ : Env)
    (hHop1 : ∀ args m Q X, fullBvaHop1Spec args m Q X →
      Γ "full_bva_hop1" [i64, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, fullBvaHop2Spec args m Q X → Func.wp Γ m7Hop2Fn.body args m Q X :=
  full_bva_hop2_m7_wp Γ hHop1

/-- Row-by-row `TableImpl` witness for `m7HotHop1Fns` under `m7HotHop1Env`. -/
theorem m7HotHop1_tableImpl :
    TableImpl m7HotHop1Env m7HotHop1Fns m7HotHop1SpecTable := by
  have hHop1 : ∀ a m Q X, fullBvaHop1Spec a m Q X →
      m7HotHop1Env "full_bva_hop1" [i64, i32, i32] [i64] a m Q X :=
    fun _ _ _ _ h => m7HotHop1Env_mem
      (e := ⟨"full_bva_hop1", [i64, i32, i32], [i64], fullBvaHop1Spec, true⟩)
      (by simp [m7HotHop1SpecTable]) rfl h
  refine ⟨SpecEntry.Impl.of (full_bva_hop1_m7_wp m7HotHop1Env),
    SpecEntry.Impl.of (full_bva_hop2_m7_wp m7HotHop1Env hHop1), trivial⟩

private theorem m7HotHop1_allFns_wf : AllFns Fn.Wf m7HotHop1Module.fns :=
  ⟨m7Hop1Fn_wf, m7Hop2Fn_wf, trivial⟩

/-- Unconditional closed `ModuleOk` certifying `m7HotHop1Module` under `m7HotHop1Env`. -/
theorem m7HotHop1_moduleOk : ModuleOk m7HotHop1Env m7HotHop1Module :=
  Env.ofTable_moduleOk m7HotHop1_acyclic m7HotHop1_allFns_wf m7HotHop1_tableImpl

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bva_hop1_m7`. -/
theorem nv_m7_bva_hop1 :
    Func.wp m7HotHop1Env full_bva_hop1_m7_body
      (nvOneLitCfg.hdr, 0#32, 0#32, ()) nvBvaDenseMem
      (fun (_r, ()) m' => ∃ s',
        FullDenseInvNoLm nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  exact full_bva_hop1_m7_wp m7HotHop1Env _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], nvBvaDenseState, emp, rfl,
      FullDenseInvW.toNoLm nvBvaDense_invW, by decide, Nat.zero_le _,
      fun _ h => by simp [nvBvaDenseState, nvOneLitState] at h, hm,
      fun _ _ _ _ _ m' hnl _ _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hnl, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bva_hop2_m7`. -/
theorem nv_m7_bva_hop2 :
    Func.wp m7HotHop1Env full_bva_hop2_m7_body
      (nvOneLitCfg.hdr, 0#32, 0#32, ()) nvBvaDenseMem
      (fun (_r, ()) m' => ∃ s',
        FullDenseInvNoLm nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  have hHop1 : ∀ a m Q X, fullBvaHop1Spec a m Q X →
      m7HotHop1Env "full_bva_hop1" [i64, i32, i32] [i64] a m Q X :=
    fun _ _ _ _ h => m7HotHop1Env_mem
      (e := ⟨"full_bva_hop1", [i64, i32, i32], [i64], fullBvaHop1Spec, true⟩)
      (by simp [m7HotHop1SpecTable]) rfl h
  exact full_bva_hop2_m7_wp m7HotHop1Env hHop1 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], nvBvaDenseState, emp, rfl,
      FullDenseInvW.toNoLm nvBvaDense_invW, by decide, Nat.zero_le _, Nat.zero_le _,
      fun _ h => by simp [nvBvaDenseState, nvOneLitState] at h,
      fun _ h => by simp [nvBvaDenseState, nvOneLitState] at h, hm,
      fun _ _ _ _ _ _ _ _ m' hnl _ _ _ _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hnl, nvDeduceF0_unsat, hm'⟩⟩

end LeanQbe.T.Examples.Kissat.FullM7HotHop1

end
