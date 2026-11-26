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

/-! # Kissat M7 Hot-Loop Proofs (`FullM7HotHop1Proof`): `full_bva_hop1` & `full_bva_hop2` -/

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

/-! ## 1. Shared Setup Helpers & `Func.wp` Proofs -/

private abbrev hop1S (s : FullState) (rp mc : List (BitVec 32)) (tc : Nat) (ant : BitVec 64) :
    FullState :=
  { core := { s.core with repr := rp, min_clr := mc, tmp_cnt := tc },
    scratch := { s.scratch with ant_sz := ant } }
private abbrev hop2S (s : FullState) (rp mc : List (BitVec 32)) (tc tl : Nat) (ant : BitVec 64)
    (sig : List (BitVec 64)) (shrk : List (BitVec 32)) : FullState :=
  { core := { s.core with repr := rp, min_clr := mc, tmp_cnt := tc, tmp_len := tl },
    scratch := { s.scratch with ant_sz := ant, sim_sig := sig, shrink_stk := shrk } }
private theorem bv64_ofNat_add1 (n : Nat) (hn : n + 1 < 2 ^ 64) :
    (BitVec.ofNat 64 n + 1).toNat = n + 1 := by
  change (BitVec.ofNat 64 n + 1#64).toNat = _; c0_bound
private theorem bv64_ofNat_toNat (n : Nat) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by c0_bound
private theorem getElem?_set_lt_bound {xs : List (BitVec 32)} {k bound : Nat} {v : BitVec 32}
    (hv : v.toNat < bound) (hxs : ∀ i < k, (xs[i]?.getD 0#32).toNat < bound)
    (hk : k < xs.length) : ∀ i < k + 1, ((xs.set k v)[i]?.getD 0#32).toNat < bound := by
  intro i hi; by_cases hie : i = k
  · subst hie; rw [List.getElem?_set_self hk, Option.getD_some]; exact hv
  · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hxs i (by omega)
private theorem m7_hop_next_slice {F_cur : List (List Nat)} {s : FullState} {sl : Nat}
    {p p' : BitVec 64} {off0 sz0 k : Nat} (hp' : p'.toNat = p.toNat + k)
    (hrem : DenseWatchSliceOk F_cur s.core sl (p.toNat + k) (off0 + sz0 - p.toNat - k)) :
    DenseWatchSliceOk F_cur s.core sl p'.toNat (off0 + sz0 - p'.toNat) := by
  rw [hp', show off0 + sz0 - (p.toNat + k) = off0 + sz0 - p.toNat - k by omega]; exact hrem

private theorem m7_hop_garb_false {s : FullState} {p : BitVec 64}
    (hp1_n : (p + 1).toNat = p.toNat + 1) (hp1_ws : p.toNat + 1 < s.core.wstk.length)
    (hcr0_eq : (BitVec.setWidth 64 (s.core.wstk[(p + 1).toNat]'(by
      rw [hp1_n]; exact hp1_ws))).toNat = (s.core.wstk[p.toNat + 1]'hp1_ws).toNat)
    (hcr_b0 : (BitVec.setWidth 64 (s.core.wstk[(p + 1).toNat]'(by
      rw [hp1_n]; exact hp1_ws))).toNat < s.core.arena.length)
    (h1 : s.core.arena[(BitVec.setWidth 64 (s.core.wstk[(p + 1).toNat]'(by
      rw [hp1_n]; exact hp1_ws))).toNat]'hcr_b0 &&& (524288#32 ||| 4194304#32) = 0#32) :
    fullArenaClauseGarbCore s.core (s.core.wstk[p.toNat + 1]'hp1_ws).toNat = false := by
  unfold fullArenaClauseGarbCore fullArenaHdrCore
  rw [List.getElem?_eq_getElem (by rw [← hcr0_eq]; exact hcr_b0), Option.getD_some]
  exact FullBvaFwdHelpers.garb_false_of_and_garb_red_eq_zero (by simpa only [hcr0_eq] using h1)

private theorem m7_hop_watch_setup {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {src_lit sgn : BitVec 32} (sl : BitVec 32)
    (hinv : FullDenseInvNoLm c F0 F_cur s) (hsidx_lt : (src_lit >>> 1).toNat < s.core.cur_vars)
    (hsgn_lt : sgn.toNat < 2) (hsl_eq : sl = ((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn) :
    sl.toNat < 2 * s.core.cur_vars ∧
    (fullWatchOffCore s.core sl.toNat + fullWatchSizeCore s.core sl.toNat ≤ s.core.wlen ∧
      DenseWatchSliceOk F_cur s.core sl.toNat
        (fullWatchOffCore s.core sl.toNat) (fullWatchSizeCore s.core sl.toNat)) ∧
    ∃ (wv0 : (BitVec.setWidth 64 sl <<< (1 : Nat)).toNat < s.core.wvec.length)
      (wv1 : ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1).toNat < s.core.wvec.length)
      (mod0 : 2 * sl.toNat % 2 ^ 64 = 2 * sl.toNat)
      (mod1 : (2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * sl.toNat + 1)
      (hw0 : 2 * sl.toNat < s.core.wvec.length) (hw1 : 2 * sl.toNat + 1 < s.core.wvec.length),
      (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 sl <<< (1 : Nat)).toNat]'wv0)).toNat =
        fullWatchOffCore s.core sl.toNat ∧
      ((s.core.wvec[2 * sl.toNat % 2 ^ 64]'(by rw [mod0]; exact hw0)).toNat +
       (s.core.wvec[(2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
         rw [mod1]; exact hw1)).toNat) % 2 ^ 64 =
        fullWatchOffCore s.core sl.toNat + fullWatchSizeCore s.core sl.toNat := by
  have hmx := c.hmaxv; have hwcap := c.hwcap; unfold dimacsBound at hmx hwcap
  have hcl := hinv.1.core_ok; have hcv_le := hcl.cur_vars_le
  have hwv_len := hcl.wvec_len; have hwlen_le := hcl.wlen_le
  have hsl_nat : sl.toNat = 2 * (src_lit >>> (1 : Nat)).toNat + sgn.toNat := by
    rw [hsl_eq]; rcases (by omega : sgn.toNat = 0 ∨ sgn.toNat = 1) with h0 | h1
    · rw [show sgn = 0#32 from BitVec.eq_of_toNat_eq h0, BitVec.or_zero]; c0_bound
    · rw [show sgn = 1#32 from BitVec.eq_of_toNat_eq h1,
        FullBvaFwdTactics.bv32_or1_of_even (by c0_bound)]; c0_bound
  have hsl_lt : sl.toNat < 2 * s.core.cur_vars := by omega
  have hdw : DenseWatchesInv F_cur s.core := by
    have h := hinv.2.1.watches; unfold ModeWatchesInv at h; rwa [ite_eq_right hinv.2.2.2.2.2] at h
  have h2sl0 : (BitVec.setWidth 64 sl <<< (1 : Nat)).toNat = 2 * sl.toNat := by c0_bound
  have hmod0 : 2 * sl.toNat % 2 ^ 64 = 2 * sl.toNat := Nat.mod_eq_of_lt (by omega)
  have hmod1 : (2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * sl.toNat + 1 := by
    c0_bound
  have hw0 : 2 * sl.toNat < s.core.wvec.length := by omega
  have hw1 : 2 * sl.toNat + 1 < s.core.wvec.length := by omega
  have hoff_eq : (s.core.wvec[2 * sl.toNat]'hw0).toNat = fullWatchOffCore s.core sl.toNat := by
    unfold fullWatchOffCore; rw [List.getElem?_eq_getElem hw0, Option.getD_some]
  have hsz_eq : (s.core.wvec[2 * sl.toNat + 1]'hw1).toNat = fullWatchSizeCore s.core sl.toNat := by
    unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem hw1, Option.getD_some]
  refine ⟨hsl_lt, ⟨hdw.layout.bounds sl.toNat hsl_lt, hdw.slices sl.toNat hsl_lt⟩, by c0_bound,
    by change ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1#64).toNat < _; c0_bound, hmod0, hmod1,
    hw0, hw1, by rw [bv64_setWidth_32]; simp only [h2sl0]; exact hoff_eq, ?_⟩
  have := hdw.layout.bounds sl.toNat hsl_lt; simp only [hmod0, hmod1, hoff_eq, hsz_eq]
  exact Nat.mod_eq_of_lt (by omega)

private theorem m7_hop_occ_setup {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {p : BitVec 64}
    (hinv : FullDenseInvNoLm c F0 F_cur s) (hp1_n : (p + 1).toNat = p.toNat + 1)
    (hp1_ws : p.toNat + 1 < s.core.wstk.length)
    (hcr_ref : (s.core.wstk[p.toNat + 1]'hp1_ws).toNat ∈ fullArenaClauseRefsCore s.core) :
    let cr := s.core.wstk[p.toNat + 1]'hp1_ws
    let p1 := s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)
    ∃ hcr2_lt : cr.toNat + 2 < s.core.arena.length, p1 = cr ∧
      (BitVec.setWidth 64 p1).toNat = cr.toNat ∧
      (BitVec.setWidth 64 p1).toNat < s.core.arena.length ∧
      (BitVec.setWidth 64 p1 + 2).toNat = cr.toNat + 2 ∧
      (BitVec.setWidth 64 p1 + 2).toNat < s.core.arena.length ∧
      (s.core.arena[cr.toNat + 2]'hcr2_lt).toNat = fullArenaClauseSizeCore s.core cr.toNat ∧
      cr.toNat + 3 + (s.core.arena[cr.toNat + 2]'hcr2_lt).toNat ≤ s.core.arena.length := by
  have har_b := c.harena; unfold dimacsBound at har_b
  have hcl := hinv.1.core_ok; have har_len := hcl.arena_len_arr; have hal_le := hcl.arena_len_le
  have hcr_wf := hinv.2.1.arena.refs_wf _ hcr_ref
  have h1 := hcr_wf.2.2.1; have h2 := hcr_wf.2.2.2.1
  let cr := s.core.wstk[p.toNat + 1]'hp1_ws
  let p1 := s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)
  have hcr_eq : p1 = cr := by dsimp only [p1, cr]; simp only [hp1_n]
  have hcr0_eq : (BitVec.setWidth 64 p1).toNat = cr.toNat := by rw [bv64_setWidth_32, hcr_eq]
  have hcr2_eq : (BitVec.setWidth 64 p1 + 2).toNat = cr.toNat + 2 := by
    change (BitVec.setWidth 64 _ + 2#64).toNat = _; rw [hcr_eq]; simp only [bv_c0]; omega
  have hcr2_lt : cr.toNat + 2 < s.core.arena.length := by dsimp only [cr]; omega
  have hsz_cr : (s.core.arena[cr.toNat + 2]'hcr2_lt).toNat =
      fullArenaClauseSizeCore s.core cr.toNat := by
    unfold fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by dsimp only [cr]; omega), Option.getD_some]
  exact ⟨hcr2_lt, hcr_eq, hcr0_eq, by rw [hcr0_eq]; dsimp only [cr]; omega, hcr2_eq,
    by rw [hcr2_eq]; dsimp only [cr]; omega, hsz_cr, by rw [hsz_cr]; dsimp only [cr]; omega⟩

private theorem m7_hop_occ_absurd {P : Prop} {p : BitVec 64} {off0 sz0 lhs : Nat}
    (hp1_mod : (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1)
    (hend_mod : lhs = off0 + sz0) (h2le : 2 ≤ off0 + sz0 - p.toNat)
    (hge : ¬ (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < lhs) : P :=
  False.elim (by rw [hend_mod, hp1_mod] at hge; omega)

private theorem m7_hop_inv_aux {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvNoLm c F0 F_cur s)
    {rp mc shrk : List (BitVec 32)} {sig : List (BitVec 64)} {tc tl : Nat} {ant : BitVec 64}
    (hrp : rp.length = 2 * c.max_vars) (hmc : mc.length = c.max_vars)
    (htl : tl ≤ c.max_vars) (hsig : sig.length = c.max_vars)
    (hshrk : shrk.length = c.max_vars) :
    FullDenseInvNoLm c F0 F_cur (hop2S s rp mc tc tl ant sig shrk) :=
  fullDenseInvNoLm_with_core_aux hinv hrp hmc hinv.1.core_ok.tmp_len_arr hinv.1.core_ok.flags_len
    htl { hinv.1.scratch_ok with sim_sig_len := hsig, shrink_stk_len := hshrk } rfl rfl

/-- Exact canonical `fullBvaHop1Spec` correctness for scalarized/LSR `full_bva_hop1_m7_body`. -/
theorem full_bva_hop1_m7_wp (Γ : Env) :
    ∀ args m Q X, fullBvaHop1Spec args m Q X → Func.wp Γ full_bva_hop1_m7_body args m Q X := by
  rintro ⟨h, src_lit, dst_idx, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hsrc_lt, htc_le, hmclr_ok, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena
  unfold dimacsBound at hmx hwcap har_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok; have hcv_le := hcl.cur_vars_le
  have hrepr_len := hcl.repr_len; have hwv_len := hcl.wvec_len; have hws_len := hcl.wstk_len_arr
  have har_len := hcl.arena_len_arr; have hwlen_le := hcl.wlen_le
  have hal_le := hcl.arena_len_le; have hmclr_len := hcl.min_clr_len_arr
  have hsidx_lt : (src_lit >>> 1).toNat < s.core.cur_vars := by rw [bv32_lshr1_nat]; omega
  have hsw : (BitVec.setWidth 64 (src_lit >>> 1)).toNat = (src_lit >>> 1).toNat := by c0_bound
  c0_hsteps_nogrp
  · exact hQ _ s.core.repr s.core.min_clr s.core.tmp_cnt s.scratch.ant_sz m
      hinv htc_le hmclr_ok (Nat.le_refl _) hm
  · refine wp_join_state1 (t := i64) (α := BitVec 64) (fun r => r) (fun _ ml => ml = m)
      (fun _ res0 ml hml => ?_) (fun J0 hJ0 => ?_)
    · subst ml; c0_hsteps_nogrp
      refine wp_loop_inv
        (fun (_, ant, sgn, ()) ml => sgn.toNat ≤ 2 ∧ ant.toNat ≤ s.scratch.ant_sz.toNat ∧ ml = m)
        (fun (_, _, sgn, _) _ => 2 - sgn.toNat)
        (fun Js hJs => by
          c0_hsteps; exact hJs (res0, s.scratch.ant_sz, 0#32, ()) m ⟨by decide, Nat.le_refl _, rfl⟩)
        (fun Js (res, ant, sgn, ()) ml ⟨hsgn_le, hant_le, hml⟩ ihs => ?_)
      subst ml; c0_hsteps_nogrp
      refine wp_join_state0 (α := PUnit) (fun _ mf => mf = m)
        (fun _ _ mf hmf => ?_) (fun Jend hJend => ?_)
      · subst mf; c0_hsteps_nogrp
        refine wp_join_state1 (t := i64)
          (α := BitVec 64 × List (BitVec 32) × List (BitVec 32) × Nat) (fun st => st.1)
          (fun ⟨_resF, rpF, mcF, tcF⟩ mf1 => FullDenseInvNoLm c F0 F_cur (hop1S s rpF mcF tcF ant) ∧
            tcF ≤ s.core.cur_vars ∧ (∀ i < tcF, (mcF[i]?.getD 0#32).toNat < c.max_vars) ∧
            (FullMem c (hop1S s rpF mcF tcF ant) ⋆ R) mf1)
          (fun _ ⟨resF, rpF, mcF, tcF⟩ mf1 ⟨hinvF, htcF, hmcF, hmf1⟩ => by
            c0_hsteps; exact hQ resF rpF mcF tcF ant mf1 hinvF htcF hmcF hant_le hmf1)
          (fun Jant hJant => ?_)
        c0_hsteps_nogrp
        · refine wp_join_state1 (t := i64) (α := BitVec 64) (fun r => r) (fun _ ml => ml = m)
            (fun _ resC ml hml => ?_) (fun Jc hJc => ?_)
          · subst ml; c0_hsteps
            · have htc1 : s.core.tmp_cnt + 1 ≤ s.core.cur_vars := by c0_bound
              let rp' := repr64Set s.core.repr (src_lit >>> 1).toNat (resC + 1)
              let mc' := s.core.min_clr.set s.core.tmp_cnt (src_lit >>> 1)
              have hm' : (FullMem c (hop1S s rp' mc' (s.core.tmp_cnt + 1) ant) ⋆ R) m := by
                rw [bv64_ofNat_add1 s.core.tmp_cnt (by omega),
                    bv64_ofNat_toNat s.core.tmp_cnt (by omega), hsw] at hm; exact hm
              exact hJant ⟨resC, _, _, s.core.tmp_cnt + 1⟩ m
                ⟨m7_hop_inv_aux hinv (by simp [rp', repr64Set_length, hrepr_len])
                  (by simp [hmclr_len]) hcl.tmp_len_le hsc.sim_sig_len hsc.shrink_stk_len,
                 htc1, getElem?_set_lt_bound (by omega) hmclr_ok (by omega), hm'⟩
            · let rp' := repr64Set s.core.repr (src_lit >>> 1).toNat (resC + 1)
              have hm' : (FullMem c (hop1S s rp' s.core.min_clr s.core.tmp_cnt ant) ⋆ R) m := by
                rw [hsw] at hm; exact hm
              exact hJant ⟨resC, _, s.core.min_clr, s.core.tmp_cnt⟩ m
                ⟨m7_hop_inv_aux hinv (by simp [rp', repr64Set_length, hrepr_len])
                  hmclr_len hcl.tmp_len_le hsc.sim_sig_len hsc.shrink_stk_len,
                 htc_le, hmclr_ok, hm'⟩
          · c0_hsteps <;> first | exact hJc 0x3FFFFFFFFFFFFFFF#64 m rfl | exact hJc res m rfl
        · exact hJant ⟨res, s.core.repr, s.core.min_clr, s.core.tmp_cnt⟩ m
            ⟨m7_hop_inv_aux hinv hrepr_len hmclr_len hcl.tmp_len_le hsc.sim_sig_len
              hsc.shrink_stk_len, htc_le, hmclr_ok, hm⟩
      · c0_hsteps
        · have hsgn_lt : sgn.toNat < 2 := by c0_bound
          let sl : BitVec 32 := ((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn
          let off0 := fullWatchOffCore s.core sl.toNat; let sz0 := fullWatchSizeCore s.core sl.toNat
          obtain ⟨hsl_lt_sl, ⟨hoff_sz_le, hslice_sl⟩, hwv_sl0, hwv_sl1,
            hmod0, hmod1, hw0, hw1, hoff_c0, hend_mod⟩ :=
            m7_hop_watch_setup sl hinv hsidx_lt hsgn_lt rfl
          c0_hsteps_nogrp
          refine wp_loop_inv
            (fun (_, antp, p, ()) mlp => off0 ≤ p.toNat ∧ p.toNat ≤ off0 + sz0 ∧
              antp.toNat ≤ ant.toNat ∧
              DenseWatchSliceOk F_cur s.core sl.toNat p.toNat (off0 + sz0 - p.toNat) ∧ mlp = m)
            (fun (_, _, p, _) _ => off0 + sz0 - p.toNat)
            (fun Jp hJp => by
              c0_hfast; exact hJp (res, ant, _, ()) m ⟨by rw [hoff_c0]; exact Nat.le_refl _,
                by rw [hoff_c0]; omega, Nat.le_refl _,
                by rw [hoff_c0, Nat.add_sub_cancel_left]; exact hslice_sl, rfl⟩)
            (fun Jp (res1, antp, p, ()) mlp ⟨hp_ge, hp_le, hantp_le, hrem, hmlp⟩ ihp => ?_)
          subst mlp; c0_hfast
          · have hp_lt : p.toNat < off0 + sz0 := by rw [← hend_mod]; assumption
            have hp_ws : p.toNat < s.core.wstk.length := by omega
            have hant1 : (antp - 1#64).toNat ≤ ant.toNat := by simp only [bv_c0]; omega
            have hp1_n : (p + 1).toNat = p.toNat + 1 := by
              change (p + 1#64).toNat = _; simp only [bv_c0]; omega
            have hp1_mod : (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
              rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
            c0_hfast
            all_goals try
              (have ⟨_, _, hrem_next⟩ :=
                FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hp_ws (by assumption)
               exact ihp (_, antp - 1#64, p + 1, ()) m (by dsimp only; rw [hp1_n]; omega)
                 ⟨by rw [hp1_n]; omega, by rw [hp1_n]; omega, hant1,
                  m7_hop_next_slice hp1_n hrem_next, rfl⟩)
            · have ⟨h2le, hrem_next⟩ :=
                FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws (by assumption)
              have hp1_ws : p.toNat + 1 < s.core.wstk.length := by omega
              have ⟨_, hcr_ref, _⟩ :=
                FullBvaFwdHelpers.fwd_slice_occ_info hrem (by omega) hp_ws hp1_ws (by assumption)
              have hp2_n : (p + 1 + 1).toNat = p.toNat + 2 := by
                change (p + 1#64 + 1#64).toNat = _; simp only [bv_c0]; omega
              let cr := s.core.wstk[p.toNat + 1]'hp1_ws
              obtain ⟨hcr2_lt, hcr_eq, hcr0_eq, hcr_b0, hcr2_eq, hcr_b2, hsz_cr, hcr_sz_le⟩ :=
                m7_hop_occ_setup hinv hp1_n hp1_ws hcr_ref
              have hcend_n : (BitVec.setWidth 64 cr + 3 +
                  BitVec.setWidth 64 (s.core.arena[cr.toNat + 2]'hcr2_lt)).toNat =
                  cr.toNat + 3 + (s.core.arena[cr.toNat + 2]'hcr2_lt).toNat := by
                change (BitVec.setWidth 64 cr + 3#64 + _).toNat = _; simp only [bv_c0]; omega
              c0_hfast
              · clear hQ ihs hJend
                let ci0 : BitVec 64 := BitVec.setWidth 64 cr + 3
                let cend : BitVec 64 :=
                  ci0 + BitVec.setWidth 64 (s.core.arena[cr.toNat + 2]'hcr2_lt)
                refine wp_loop_inv (fun (_, ci, ()) mk => ci.toNat ≤ cend.toNat ∧ mk = m)
                  (fun (_, ci, _) _ => cend.toNat - ci.toNat)
                  (fun Jk hJk => by
                    have hci0_n : ci0.toNat = cr.toNat + 3 := by
                      change (BitVec.setWidth 64 cr + 3#64).toNat = _; simp only [bv_c0]; omega
                    c0_hfast; exact hJk (res1, _, ()) m ⟨by
                      dsimp only [ci0, cend] at hci0_n ⊢; rw [hcr_eq, hci0_n, hcend_n]; omega, rfl⟩)
                  (fun Jk (resk, ci, ()) mk ⟨hci_le, hmk⟩ ihk => ?_)
                subst mk; c0_hsplit
                · have hcr2_mod : (cr.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 =
                      cr.toNat + 2 := by
                    rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
                  have hci_lt : ci.toNat < cend.toNat := by
                    dsimp only [cend, ci0]; rw [hcend_n]; simp only [hp1_mod] at hc
                    change ci.toNat < (cr.toNat + BitVec.toNat (3 : BitVec 64) +
                      (s.core.arena[(cr.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                        rw [hcr2_mod]; omega)).toNat) % 2 ^ 64 at hc
                    simp only [hcr2_mod, show BitVec.toNat (3 : BitVec 64) = 3 from rfl] at hc
                    exact Nat.lt_of_lt_of_le hc (Nat.mod_le _ _)
                  have hci_b : ci.toNat < s.core.arena.length := by
                    dsimp only [cend, ci0] at hci_lt; rw [hcend_n] at hci_lt
                    exact Nat.lt_of_lt_of_le hci_lt hcr_sz_le
                  have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := by simp only [bv_c0]; omega
                  c0_hfast <;> exact ihk (_, ci + 1#64, ()) m (by dsimp only; rw [hci1]; omega)
                    ⟨by rw [hci1]; exact hci_lt, rfl⟩
                · c0_hfast; exact ihp (resk, antp - 1#64, p + 1 + 1, ()) m
                    (by dsimp only; rw [hp2_n]; omega) ⟨by rw [hp2_n]; omega,
                      by rw [hp2_n]; omega, hant1, m7_hop_next_slice hp2_n hrem_next, rfl⟩
              · exact ihp (res1, antp - 1#64, p + 1 + 1, ()) m (by dsimp only; rw [hp2_n]; omega)
                  ⟨by rw [hp2_n]; omega, by rw [hp2_n]; omega, hant1,
                   m7_hop_next_slice hp2_n hrem_next, rfl⟩
            · have ⟨h2le, _⟩ :=
                FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws (by assumption)
              exact m7_hop_occ_absurd hp1_mod hend_mod h2le (by assumption)
          all_goals
            exact ihs (res1, antp, sgn + 1#32, ()) m (by simp only [bv_c0]; omega)
              ⟨by simp only [bv_c0]; omega, Nat.le_trans hantp_le hant_le, rfl⟩
        all_goals exact hJend () m rfl
    · c0_hsteps <;> first | exact hJ0 1#64 m rfl | exact hJ0 0#64 m rfl

/-- Exact canonical `fullBvaHop2Spec` correctness for sunk-local `full_bva_hop2_m7_body`. -/
theorem full_bva_hop2_m7_wp (Γ : Env)
    (hHop1 : ∀ args m Q X, fullBvaHop1Spec args m Q X →
      Γ "full_bva_hop1" [i64, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, fullBvaHop2Spec args m Q X → Func.wp Γ full_bva_hop2_m7_body args m Q X := by
  rintro ⟨h, src_lit, dst_idx, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hsrc_lt, htc_le, htl_le, hmclr_ok, hshrk_ok, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena
  unfold dimacsBound at hmx hwcap har_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok; have hcv_le := hcl.cur_vars_le
  have hsig_len := hsc.sim_sig_len; have hshrk_len := hsc.shrink_stk_len
  have hwv_len := hcl.wvec_len; have hws_len := hcl.wstk_len_arr; have har_len := hcl.arena_len_arr
  have hwlen_le := hcl.wlen_le; have hal_le := hcl.arena_len_le
  have hsidx_lt : (src_lit >>> 1).toNat < s.core.cur_vars := by rw [bv32_lshr1_nat]; omega
  have hsw : (BitVec.setWidth 64 (src_lit >>> 1)).toNat = (src_lit >>> 1).toNat := by c0_bound
  c0_hsteps_nogrp
  · exact hQ _ s.core.repr s.core.min_clr s.core.tmp_cnt s.core.tmp_len s.scratch.ant_sz
      s.scratch.sim_sig s.scratch.shrink_stk m hinv htc_le htl_le hmclr_ok hshrk_ok
      (Nat.le_refl _) hm
  · refine wp_join_state1 (t := i64) (α := BitVec 64) (fun r => r) (fun _ ml => m = ml)
      (fun _ res0 ml hml => ?_) (fun J0 hJ0 => ?_)
    · rcases hml with rfl; c0_hsteps_nogrp
      refine wp_loop_inv
        (fun (res, sgn, ()) ml => ∃ rp mc tc ant,
          sgn.toNat ≤ 2 ∧ tc ≤ s.core.cur_vars ∧ ant.toNat ≤ s.scratch.ant_sz.toNat ∧
          FullDenseInvNoLm c F0 F_cur (hop1S s rp mc tc ant) ∧
          (∀ i < tc, (mc[i]?.getD 0#32).toNat < c.max_vars) ∧
          (FullMem c (hop1S s rp mc tc ant) ⋆ R) ml)
        (fun (_, sgn, _) _ => 2 - sgn.toNat)
        (fun Js hJs => by
          c0_hsteps; exact hJs (res0, 0#32, ()) m ⟨s.core.repr, s.core.min_clr, s.core.tmp_cnt,
            s.scratch.ant_sz, by decide, htc_le, Nat.le_refl _, hinv, hmclr_ok, hm⟩)
        (fun Js (res, sgn, ()) ml
            ⟨rp, mc, tc, ant, hsgn_le, htc, hant, hinv_s, hmc_ok, hml⟩ ihs => ?_)
      c0_hsteps_nogrp
      refine wp_join_state0 (α := List (BitVec 32) × List (BitVec 32) × Nat × BitVec 64)
        (fun ⟨rpF, mcF, tcF, antF⟩ mf => tcF ≤ s.core.cur_vars ∧
          antF.toNat ≤ s.scratch.ant_sz.toNat ∧
          FullDenseInvNoLm c F0 F_cur (hop1S s rpF mcF tcF antF) ∧
          (∀ i < tcF, (mcF[i]?.getD 0#32).toNat < c.max_vars) ∧
          (FullMem c (hop1S s rpF mcF tcF antF) ⋆ R) mf)
        (fun _ ⟨rpF, mcF, tcF, antF⟩ mf ⟨htcF, hantF, hinvF, hmcF, hmf⟩ => ?_)
        (fun Jend hJend => ?_)
      · c0_hsteps_nogrp
        refine wp_join_state1 (t := i64)
          (α := BitVec 64 × Nat × List (BitVec 64) × List (BitVec 32)) (fun st => st.1)
          (fun ⟨_resF, tlF, sigF, shrkF⟩ mf1 =>
            FullDenseInvNoLm c F0 F_cur (hop2S s rpF mcF tcF tlF antF sigF shrkF) ∧
            tlF ≤ s.core.cur_vars ∧ (∀ i < tlF, (shrkF[i]?.getD 0#32).toNat < c.max_vars) ∧
            (FullMem c (hop2S s rpF mcF tcF tlF antF sigF shrkF) ⋆ R) mf1)
          (fun _ ⟨resF, tlF, sigF, shrkF⟩ mf1 ⟨hinv1, htl1, hshrk1, hmf1⟩ => by
            c0_hsteps; exact hQ resF rpF mcF tcF tlF antF sigF shrkF mf1 hinv1 htcF htl1 hmcF
              hshrk1 hantF hmf1)
          (fun Jant hJant => ?_)
        c0_hsteps_nogrp
        · refine wp_join_state1 (t := i64) (α := BitVec 64) (fun r => r) (fun _ ml => mf = ml)
            (fun _ resC ml hml => ?_) (fun Jc hJc => ?_)
          · rcases hml with rfl; c0_hsteps
            · have htl1 : s.core.tmp_len + 1 ≤ s.core.cur_vars := by c0_bound
              let sig' := s.scratch.sim_sig.set (src_lit >>> 1).toNat (resC + 1)
              let shrk' := s.scratch.shrink_stk.set s.core.tmp_len (src_lit >>> 1)
              have hm' : (FullMem c (hop2S s rpF mcF tcF (s.core.tmp_len + 1) antF sig' shrk')
                  ⋆ R) m := by
                rw [bv64_ofNat_add1 s.core.tmp_len (by omega),
                    bv64_ofNat_toNat s.core.tmp_len (by omega), hsw] at hm; exact hm
              exact hJant ⟨resC, s.core.tmp_len + 1, sig', shrk'⟩ m
                ⟨m7_hop_inv_aux hinvF hinvF.1.core_ok.repr_len hinvF.1.core_ok.min_clr_len_arr
                  (by omega) (by dsimp [sig']; simp [hsig_len])
                  (by dsimp [shrk']; simp [hshrk_len]),
                 htl1, getElem?_set_lt_bound (by omega) hshrk_ok (by omega), hm'⟩
            · let sig' := s.scratch.sim_sig.set (src_lit >>> 1).toNat (resC + 1)
              have hm' : (FullMem c (hop2S s rpF mcF tcF s.core.tmp_len antF sig'
                  s.scratch.shrink_stk) ⋆ R) m := by rw [hsw] at hm; exact hm
              exact hJant ⟨resC, s.core.tmp_len, sig', s.scratch.shrink_stk⟩ m
                ⟨m7_hop_inv_aux hinvF hinvF.1.core_ok.repr_len hinvF.1.core_ok.min_clr_len_arr
                  hcl.tmp_len_le (by dsimp [sig']; simp [hsig_len]) hshrk_len,
                 htl_le, hshrk_ok, hm'⟩
          · c0_hsteps <;> first | exact hJc 0x3FFFFFFFFFFFFFFF#64 mf rfl | exact hJc res mf rfl
        · exact hJant ⟨res, s.core.tmp_len, s.scratch.sim_sig, s.scratch.shrink_stk⟩ mf
            ⟨hinvF, htl_le, hshrk_ok, hmf⟩
      · c0_hsteps
        · have hsgn_lt : sgn.toNat < 2 := by c0_bound
          let sl : BitVec 32 := ((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn
          let off0 := fullWatchOffCore s.core sl.toNat; let sz0 := fullWatchSizeCore s.core sl.toNat
          obtain ⟨hsl_lt_sl, ⟨hoff_sz_le, hslice_sl⟩, hwv_sl0, hwv_sl1,
            hmod0, hmod1, hw0, hw1, hoff_c0, hend_mod⟩ :=
            m7_hop_watch_setup sl hinv hsidx_lt hsgn_lt rfl
          c0_hsteps_nogrp
          refine wp_loop_inv
            (fun (res1, p, ()) mlp => ∃ rpp mcp tcp antp, off0 ≤ p.toNat ∧ p.toNat ≤ off0 + sz0 ∧
              tcp ≤ s.core.cur_vars ∧ antp.toNat ≤ ant.toNat ∧
              FullDenseInvNoLm c F0 F_cur (hop1S s rpp mcp tcp antp) ∧
              (∀ i < tcp, (mcp[i]?.getD 0#32).toNat < c.max_vars) ∧
              DenseWatchSliceOk F_cur s.core sl.toNat p.toNat (off0 + sz0 - p.toNat) ∧
              (FullMem c (hop1S s rpp mcp tcp antp) ⋆ R) mlp)
            (fun (_, p, _) _ => off0 + sz0 - p.toNat)
            (fun Jp hJp => by
              c0_hfast
              exact hJp (res, _, ()) ml ⟨rp, mc, tc, ant, by rw [hoff_c0]; exact Nat.le_refl _,
                by rw [hoff_c0]; omega, htc, Nat.le_refl _, hinv_s, hmc_ok,
                by rw [hoff_c0, Nat.add_sub_cancel_left]; exact hslice_sl, hml⟩)
            (fun Jp (res1, p, ()) mlp ⟨rpp, mcp, tcp, antp, hp_ge, hp_le, htcp, hantp, hinvp,
                hmcp_ok, hrem, hmlp⟩ ihp => ?_)
          c0_hfast
          · have hp_lt : p.toNat < off0 + sz0 := by rw [← hend_mod]; assumption
            have hp_ws : p.toNat < s.core.wstk.length := by omega
            have hant1 : (antp - 1#64).toNat ≤ ant.toNat := by simp only [bv_c0]; omega
            have hp1_n : (p + 1).toNat = p.toNat + 1 := by
              change (p + 1#64).toNat = _; simp only [bv_c0]; omega
            have hp1_mod : (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
              rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
            have hinvp1 : FullDenseInvNoLm c F0 F_cur (hop1S s rpp mcp tcp (antp - 1#64)) :=
              m7_hop_inv_aux hinvp hinvp.1.core_ok.repr_len hinvp.1.core_ok.min_clr_len_arr
                hcl.tmp_len_le hsc.sim_sig_len hsc.shrink_stk_len
            c0_hfast
            · have ⟨hot_lt, _, hrem_next⟩ :=
                FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hp_ws (by assumption)
              c0_call hHop1
              refine ⟨c, F0, F_cur, hop1S s rpp mcp tcp (antp - 1#64), R, rfl, hinvp1, hot_lt,
                htcp, hmcp_ok, hm, fun r1 rp1 mc1 tc1 ant1 m1 hinv1 htc1 hmc1 hant1' hm1 => ?_⟩
              c0_hfast
              exact ihp (res1 + r1, p + 1, ()) m1 (by dsimp only; rw [hp1_n]; omega)
                ⟨rp1, mc1, tc1, ant1, by rw [hp1_n]; omega, by rw [hp1_n]; omega, htc1,
                 Nat.le_trans hant1' hant1, hinv1, hmc1, m7_hop_next_slice hp1_n hrem_next, hm1⟩
            · have ⟨h2le, hrem_next⟩ :=
                FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws (by assumption)
              have hp1_ws : p.toNat + 1 < s.core.wstk.length := by omega
              have ⟨_, hcr_ref, _⟩ :=
                FullBvaFwdHelpers.fwd_slice_occ_info hrem (by omega) hp_ws hp1_ws (by assumption)
              have hp2_n : (p + 1 + 1).toNat = p.toNat + 2 := by
                change (p + 1#64 + 1#64).toNat = _; simp only [bv_c0]; omega
              let cr := s.core.wstk[p.toNat + 1]'hp1_ws
              obtain ⟨hcr2_lt, hcr_eq, hcr0_eq, hcr_b0, hcr2_eq, hcr_b2, hsz_cr, hcr_sz_le⟩ :=
                m7_hop_occ_setup hinv hp1_n hp1_ws hcr_ref
              have hcr_sz_le' : cr.toNat + 3 + (s.core.arena[cr.toNat + 2]'hcr2_lt).toNat ≤
                  s.core.arena.length := hcr_sz_le
              c0_hfast
              · have hng_cr := m7_hop_garb_false hp1_n hp1_ws hcr0_eq hcr_b0 (by assumption)
                clear hQ ihs hJend
                refine wp_loop_inv
                  (fun (resk, k, ()) mk => ∃ rpk mck tck antk,
                    k.toNat ≤ (s.core.arena[cr.toNat + 2]'hcr2_lt).toNat ∧
                    tck ≤ s.core.cur_vars ∧ antk.toNat ≤ ant.toNat ∧
                    FullDenseInvNoLm c F0 F_cur (hop1S s rpk mck tck antk) ∧
                    (∀ i < tck, (mck[i]?.getD 0#32).toNat < c.max_vars) ∧
                    (FullMem c (hop1S s rpk mck tck antk) ⋆ R) mk)
                  (fun (_, k, _) _ => (s.core.arena[cr.toNat + 2]'hcr2_lt).toNat - k.toNat)
                  (fun Jk hJk => by
                    c0_hfast; exact hJk (res1, 0#32, ()) m
                      ⟨rpp, mcp, tcp, antp - 1#64, Nat.zero_le _, htcp, hant1, hinvp1,
                       hmcp_ok, hm⟩)
                  (fun Jk (resk, k, ()) mk ⟨rpk, mck, tck, antk, hk_le, htck, hantk, hinvk,
                      hmck_ok, hmk⟩ ihk => ?_)
                c0_hsplit
                · have hk_lt : k.toNat < (s.core.arena[cr.toNat + 2]'hcr2_lt).toNat := by
                    have h1 : k.toNat < (s.core.arena[(BitVec.setWidth 64
                        (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) +
                        2).toNat]'hcr_b2).toNat := by assumption
                    simpa only [hcr2_eq] using h1
                  have hk1 : (k + 1#32).toNat = k.toNat + 1 := by simp only [bv_c0]; omega
                  c0_hsplit
                  · have hcrk_eq : (BitVec.setWidth 64 (s.core.wstk[(p + 1).toNat]'(by
                          rw [hp1_n]; exact hp1_ws)) + 3 + BitVec.setWidth 64 k).toNat =
                        cr.toNat + 3 + k.toNat := by
                      change (BitVec.setWidth 64 _ + 3#64 + BitVec.setWidth 64 k).toNat = _
                      rw [hcr_eq]; dsimp only [cr] at hcr_sz_le' hk_lt ⊢; simp only [bv_c0]; omega
                    have hcrk_b : (BitVec.setWidth 64 (s.core.wstk[(p + 1).toNat]'(by
                        rw [hp1_n]; exact hp1_ws)) + 3 + BitVec.setWidth 64 k).toNat <
                        s.core.arena.length := by rw [hcrk_eq]; omega
                    have hol_mem : (s.core.arena[cr.toNat + 3 + k.toNat]'(by omega)).toNat ∈
                        fullArenaClauseLitsCore s.core cr.toNat :=
                      List.mem_of_getElem? (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem
                        (by rw [← hsz_cr]; exact hk_lt) (by omega))
                    have hol_lt := hinv.2.1.arena.lits_lt cr.toNat hcr_ref hng_cr _ hol_mem
                    c0_hfast
                    · c0_call hHop1
                      refine ⟨c, F0, F_cur, hop1S s rpk mck tck antk, R, rfl, hinvk, ?_, htck,
                        hmck_ok, hmk, fun r1 rp1 mc1 tc1 ant1 m1 hinv1 htc1 hmc1 hant1' hm1 => ?_⟩
                      · have hge : s.core.arena[(BitVec.setWidth 64 (s.core.wstk[(p + 1).toNat]'(by
                              rw [hp1_n]; exact hp1_ws)) + 3 + BitVec.setWidth 64 k).toNat]'hcrk_b =
                            s.core.arena[cr.toNat + 3 + k.toNat]'(by omega) :=
                          Option.some.inj ((List.getElem?_eq_getElem hcrk_b).symm.trans
                            ((congrArg (s.core.arena[·]?) hcrk_eq).trans
                              (List.getElem?_eq_getElem (by omega))))
                        exact (congrArg BitVec.toNat hge).symm ▸ hol_lt
                      · c0_hfast
                        exact ihk (resk + r1, k + 1#32, ()) m1 (by dsimp only; rw [hk1]; omega)
                          ⟨rp1, mc1, tc1, ant1, by rw [hk1]; omega, htc1,
                           Nat.le_trans hant1' hantk, hinv1, hmc1, hm1⟩
                    · exact ihk (resk, k + 1#32, ()) mk (by dsimp only; rw [hk1]; omega)
                        ⟨rpk, mck, tck, antk, by rw [hk1]; omega, htck, hantk, hinvk, hmck_ok, hmk⟩
                  all_goals
                    (c0_hfast; exact ihp (resk, p + 1 + 1, ()) mk (by dsimp only; rw [hp2_n]; omega)
                      ⟨rpk, mck, tck, antk, by rw [hp2_n]; omega, by rw [hp2_n]; omega, htck,
                       hantk, hinvk, hmck_ok, m7_hop_next_slice hp2_n hrem_next, hmk⟩)
                · c0_hfast; exact ihp (resk, p + 1 + 1, ()) mk (by dsimp only; rw [hp2_n]; omega)
                    ⟨rpk, mck, tck, antk, by rw [hp2_n]; omega, by rw [hp2_n]; omega, htck,
                     hantk, hinvk, hmck_ok, m7_hop_next_slice hp2_n hrem_next, hmk⟩
              · exact ihp (res1, p + 1 + 1, ()) m (by dsimp only; rw [hp2_n]; omega)
                  ⟨rpp, mcp, tcp, antp - 1#64, by rw [hp2_n]; omega, by rw [hp2_n]; omega, htcp,
                   hant1, hinvp1, hmcp_ok, m7_hop_next_slice hp2_n hrem_next, hm⟩
            · have ⟨h2le, _⟩ :=
                FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws (by assumption)
              exact m7_hop_occ_absurd hp1_mod hend_mod h2le (by assumption)
          all_goals
            exact ihs (res1, sgn + 1#32, ()) mlp (by simp only [bv_c0]; omega)
              ⟨rpp, mcp, tcp, antp, by simp only [bv_c0]; omega, htcp, Nat.le_trans hantp hant,
               hinvp, hmcp_ok, hmlp⟩
        all_goals exact hJend ⟨rp, mc, tc, ant⟩ ml ⟨htc, hant, hinv_s, hmc_ok, hml⟩
    · c0_hsteps <;> first | exact hJ0 1#64 m rfl | exact hJ0 0#64 m rfl

/-! ## 2. Closed `m7HotHop1Env`, `ModuleOk`, Drop-ins, & Concrete UNSAT Non-Vacuity -/

/-- Closed `2`-row specification table for `m7HotHop1Module` (`noExit := true`). -/
def m7HotHop1SpecTable : List SpecEntry :=
  [ ⟨"full_bva_hop1", [i64, i32, i32], [i64], fullBvaHop1Spec, true⟩
  , ⟨"full_bva_hop2", [i64, i32, i32], [i64], fullBvaHop2Spec, true⟩ ]
/-- Closed specification environment for `m7HotHop1Module`. -/
def m7HotHop1Env : Env := Env.ofTable m7HotHop1SpecTable
theorem m7HotHop1SpecTable_nodup : (m7HotHop1SpecTable.map SpecEntry.name).Nodup := by decide
theorem m7HotHop1SpecTable_noExit : ∀ e ∈ m7HotHop1SpecTable, e.noExit = true := by
  intro e he; simp [m7HotHop1SpecTable] at he; rcases he with rfl | rfl <;> rfl
theorem m7HotHop1Env_noExit : ∀ f as bs xs m Q X X',
    m7HotHop1Env f as bs xs m Q X → m7HotHop1Env f as bs xs m Q X' :=
  Env.ofTable_noExit m7HotHop1SpecTable_noExit
private theorem m7HotHop1Env_hop1 : ∀ a m Q X, fullBvaHop1Spec a m Q X →
    m7HotHop1Env "full_bva_hop1" [i64, i32, i32] [i64] a m Q X :=
  fun _ _ _ _ h => Env.ofTable_of_mem (e := ⟨_, _, _, fullBvaHop1Spec, true⟩)
    (by simp [m7HotHop1SpecTable]) m7HotHop1SpecTable_nodup h
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
theorem m7HotHop1_tableImpl : TableImpl m7HotHop1Env m7HotHop1Fns m7HotHop1SpecTable :=
  ⟨SpecEntry.Impl.of (full_bva_hop1_m7_wp m7HotHop1Env),
   SpecEntry.Impl.of (full_bva_hop2_m7_wp m7HotHop1Env m7HotHop1Env_hop1), trivial⟩
/-- Unconditional closed `ModuleOk` certifying `m7HotHop1Module` under `m7HotHop1Env`. -/
theorem m7HotHop1_moduleOk : ModuleOk m7HotHop1Env m7HotHop1Module :=
  Env.ofTable_moduleOk m7HotHop1_acyclic ⟨m7Hop1Fn_wf, m7Hop2Fn_wf, trivial⟩ m7HotHop1_tableImpl
/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bva_hop1_m7`. -/
theorem nv_m7_bva_hop1 :
    Func.wp m7HotHop1Env full_bva_hop1_m7_body (nvOneLitCfg.hdr, 0#32, 0#32, ()) nvBvaDenseMem
      (fun (_r, ()) m' => ∃ s', FullDenseInvNoLm nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m') (fun _ _ _ _ => False) :=
  full_bva_hop1_m7_wp m7HotHop1Env _ _ _ _ ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], nvBvaDenseState,
    emp, rfl, FullDenseInvW.toNoLm nvBvaDense_invW, by decide, Nat.zero_le _,
    fun _ h => by simp [nvBvaDenseState, nvOneLitState] at h,
    by rw [sep_emp]; exact nvBvaDenseMem_ok,
    fun _ _ _ _ _ _ hnl _ _ _ hm' => ⟨_, hnl, nvDeduceF0_unsat, by rwa [sep_emp] at hm'⟩⟩
/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bva_hop2_m7`. -/
theorem nv_m7_bva_hop2 :
    Func.wp m7HotHop1Env full_bva_hop2_m7_body (nvOneLitCfg.hdr, 0#32, 0#32, ()) nvBvaDenseMem
      (fun (_r, ()) m' => ∃ s', FullDenseInvNoLm nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m') (fun _ _ _ _ => False) :=
  full_bva_hop2_m7_wp m7HotHop1Env m7HotHop1Env_hop1 _ _ _ _ ⟨nvOneLitCfg, nvOneLitF0,
    [[0], [1]], nvBvaDenseState, emp, rfl, FullDenseInvW.toNoLm nvBvaDense_invW, by decide,
    Nat.zero_le _, Nat.zero_le _, fun _ h => by simp [nvBvaDenseState, nvOneLitState] at h,
    fun _ h => by simp [nvBvaDenseState, nvOneLitState] at h,
    by rw [sep_emp]; exact nvBvaDenseMem_ok,
    fun _ _ _ _ _ _ _ _ _ hnl _ _ _ _ _ hm' => ⟨_, hnl, nvDeduceF0_unsat, by rwa [sep_emp] at hm'⟩⟩

end LeanQbe.T.Examples.Kissat.FullM7HotHop1

end
