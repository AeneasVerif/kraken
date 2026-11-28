/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Definition.WpFidExtract2
public import LeanQbe.T.Examples.Kissat.Src.Definition

/-!
# Kissat Fid K6 Definition Extraction WP Proof (`Proof.Definition.WpFidExtract`)

Flat `CanonicalEnv` `Func.wp` proof for `full_k6_extract_and_solve_fid`
(`Spec.fidK6ExtractSolveSpec`).

`0` legacy `Full*` imports; `0` `@[expose]` on theorems/lemmas/sections; every decl `<= 450` LOC;
every line `<= 100` cols.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Definition

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Definition
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FidK6Tactics M8K6bTactics FidK6cTactics

public section

private theorem fid_k6c_trunc_ofNat64_toNat (n : Nat) (hn : n < 2 ^ 32) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 n)).toNat = n := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64), Nat.mod_eq_of_lt hn]

private theorem fid_k6c_bv64_sub_toNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b ≤ a) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b).toNat = a - b := by
  rw [BitVec.toNat_sub_of_le]
  · simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : b < 2 ^ 64)]
  · change (BitVec.ofNat 64 b).toNat ≤ (BitVec.ofNat 64 a).toNat
    simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : b < 2 ^ 64), hb]

private theorem fid_k6c_off_mul {k : Nat} {mv : BitVec 32} (hmv : mv.toNat ≤ 8192)
    (hk : k ≤ 64) : (4224#32 + BitVec.ofNat 32 k * mv).toNat = 4224 + k * mv.toNat := by
  have hmul : k * mv.toNat ≤ 64 * 8192 := Nat.mul_le_mul hk hmv
  rw [BitVec.toNat_add, BitVec.toNat_mul, show (4224#32 : BitVec 32).toNat = 4224 from rfl,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : k * mv.toNat < 2 ^ 32), Nat.mod_eq_of_lt (by omega)]

private theorem fid_k6c_shl_bv32 {k : Nat} {x : BitVec 32} (hk : k ≤ 4)
    (hx : x.toNat < 2 ^ 28) : (x <<< k).toNat = x.toNat * 2 ^ k := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have hpow : 2 ^ k ≤ 16 := Nat.pow_le_pow_right (by omega) hk
  have hx' : x.toNat ≤ 2 ^ 28 - 1 := by omega
  have hmul : x.toNat * 2 ^ k ≤ (2 ^ 28 - 1) * 16 := Nat.mul_le_mul hx' hpow
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hmul (by decide))]

private theorem fid_k6c_side_setup {F_cur : List (List Nat)} {s : FullState}
    {v np nn side cnt off mask_off lit : BitVec 32}
    (hcv : 2 * s.core.cur_vars + 1 < 2 ^ 30) (hv : v.toNat < s.core.cur_vars)
    (hnp : np.toNat ≤ 2001) (hnn : nn.toNat ≤ 2001)
    (hside : side = 0#32 ∨ side = 1#32)
    (hpos : ∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32))
    (hneg : ∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[2001 + j]?.getD 0#32))
    (hcnt : (side = 0#32 → cnt = np) ∧ (side ≠ 0#32 → cnt = nn))
    (hoff : (side = 0#32 → off = 0#32) ∧ (side ≠ 0#32 → off = 2001#32))
    (hmb : (side = 0#32 → mask_off = 4002#32) ∧ (side ≠ 0#32 → mask_off = 4066#32))
    (hlit : (side = 0#32 → lit = v <<< 1) ∧ (side ≠ 0#32 → lit = (v <<< 1) ||| 1#32)) :
    cnt.toNat ≤ 2001 ∧
    (side = 0#32 ∧ off = 0#32 ∧ mask_off = 4002#32 ∨
      side = 1#32 ∧ off = 2001#32 ∧ mask_off = 4066#32) ∧
    ∀ k < cnt.toNat,
      FullBveEntryOkW F_cur s lit.toNat (s.scratch.scratch_buf[off.toNat + k]?.getD 0#32) := by
  have hsh := fid_k6c_bv32_shl1_add1_lt hv hcv
  rcases hside with rfl | rfl
  · refine ⟨by rw [hcnt.1 rfl]; exact hnp, Or.inl ⟨rfl, hoff.1 rfl, hmb.1 rfl⟩,
      fun k hk => ?_⟩
    rw [hcnt.1 rfl] at hk
    rw [hoff.1 rfl, hlit.1 rfl, hsh.1, show (0#32 : BitVec 32).toNat = 0 from rfl, Nat.zero_add]
    exact hpos k hk
  · have hne : (1#32 : BitVec 32) ≠ 0#32 := by decide
    refine ⟨by rw [hcnt.2 hne]; exact hnn, Or.inr ⟨rfl, hoff.2 hne, hmb.2 hne⟩,
      fun k hk => ?_⟩
    rw [hcnt.2 hne] at hk
    rw [hoff.2 hne, hlit.2 hne, hsh.2, show (2001#32 : BitVec 32).toNat = 2001 from rfl]
    exact hneg k hk

/-- Parametric `Func.wp` proof for `full_k6_extract_and_solve_fid`,
    certifying `fidK6ExtractSolveSpec`. -/
theorem full_k6_extract_and_solve_fid_wp (Γ : Env)
    (hMv : Γ.Has "full_bve_k6_mv_fid" fidBveK6MvSpec)
    (hWatch : Γ.Has "full_k6_watch_fid" fidK6WatchSpec)
    (hSolve : Γ.Has "full_k6_solve_fid" fidK6SolveSpec)
    (hCore : Γ.Has "full_k6_core_fid" fidK6CoreSpec) :
    ∀ a m Q X, fidK6ExtractSolveSpec a m Q X →
      Func.wp Γ full_k6_extract_and_solve_fid_body a m Q X := by
  rintro ⟨h, v, np, nn, second_pass, tick_lim, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hinv, htmk0, h16k, hv, hnp, hnn, hpos, hneg, hm0, hQ⟩ :=
    fidK6ExtractSolveSpec_elim hSpec
  have hscr_len : s0.scratch.scratch_buf.length = c.scratch_cap :=
    hinv.1.scratch_ok.scratch_buf_len
  have hscr_lt : c.scratch_cap < 2 ^ 28 := c.hscr
  have hcv_lt : 2 * s0.core.cur_vars + 1 < 2 ^ 30 := by
    have := hinv.1.core_ok.cur_vars_le; have := c.hmaxv
    simp only [dimacsBound] at this; omega
  have hmv_b := fidK6MaxV_bounds h16k
  unfold Func.wp full_k6_extract_and_solve_fid_body
  c0_hsteps_nogrp
  apply wp_call_of_spec; apply hMv
  refine fidBveK6MvSpec_intro ?_
  dsimp only [vals, Arg.val]
  rw [show (BitVec.ofNat 64 c.scratch_cap).toNat = c.scratch_cap from by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64)]]
  have hmv_eq : (BitVec.setWidth 32 (BitVec.ofNat 64 (fidK6MaxV c.scratch_cap))).toNat =
      fidK6MaxV c.scratch_cap := fid_k6c_trunc_ofNat64_toNat _ (by omega)
  let mv_s : BitVec 32 := BitVec.setWidth 32 (BitVec.ofNat 64 (fidK6MaxV c.scratch_cap))
  have hmv_lo : 256 ≤ mv_s.toNat := by dsimp only [mv_s]; rw [hmv_eq]; exact hmv_b.1
  have hmv_hi : mv_s.toNat ≤ 8192 := by dsimp only [mv_s]; rw [hmv_eq]; exact hmv_b.2.1
  have hmv_le_cap : 4224 + 45 * mv_s.toNat ≤ c.scratch_cap := by
    dsimp only [mv_s]; rw [hmv_eq]; exact hmv_b.2.2
  c0_hsteps_nogrp
  c0_hsplit
  · c0_hsteps_nogrp
    refine wp_join_state (ts := [i32]) (fun (max_csz : BitVec 32) => (max_csz, ()))
      (fun max_csz m' => max_csz.toNat ≤ c.max_vars ∧ max_csz.toNat ≤ 65535 ∧ m' = m0)
      ?_ ?_
    · intro _ max_csz m1 ⟨hmc1, hmc2, hm1⟩
      subst hm1
      c0_hsteps_nogrp
      have hcap_lt64 : c.scratch_cap < 2 ^ 64 := by omega
      have hmv2 : (mv_s <<< (1 : Nat)).toNat = 2 * mv_s.toNat := by
        have := fid_k6c_shl_bv32 (k := 1) (x := mv_s) (by decide) (by omega); omega
      have hmv4 : (mv_s <<< (2 : Nat)).toNat = 4 * mv_s.toNat := by
        have := fid_k6c_shl_bv32 (k := 2) (x := mv_s) (by decide) (by omega); omega
      have ho_vals : 4224#32 + 9#32 * mv_s = 4224#32 + BitVec.ofNat 32 9 * mv_s := rfl
      have hacap : (BitVec.setWidth 32
          (BitVec.ofNat 64 c.scratch_cap - BitVec.setWidth 64 (4224#32 + 45#32 * mv_s))).toNat =
          c.scratch_cap - (4224 + 45 * mv_s.toNat) := by
        have h45 : (4224#32 + 45#32 * mv_s).toNat = 4224 + 45 * mv_s.toNat :=
          fid_k6c_off_mul (k := 45) hmv_hi (by decide)
        rw [BitVec.toNat_setWidth, BitVec.toNat_sub_of_le]
        · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt64, fid_zext32_toNat, h45,
            Nat.mod_eq_of_lt (by omega)]
        · change (BitVec.setWidth 64 (4224#32 + 45#32 * mv_s)).toNat ≤
            (BitVec.ofNat 64 c.scratch_cap).toNat
          rw [fid_zext32_toNat, h45, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt64]
          exact hmv_le_cap
      let acap_s : BitVec 32 := BitVec.setWidth 32
        (BitVec.ofNat 64 c.scratch_cap - BitVec.setWidth 64 (4224#32 + 45#32 * mv_s))
      have hcap_eq : 4224 + 45 * mv_s.toNat + acap_s.toNat ≤ c.scratch_cap := by
        dsimp only [acap_s]; rw [hacap]; omega
      refine wp_loop_inv
        (Inv := fun (p : Tup Val [i32, i32, i32, i32, i32, Ty.bool, i32]) m1 =>
          ∃ tmp1 wsort1 tmk1 scr1,
            p.2.2.2.2.2.2.1.toNat ≤ 2 ∧
            p.1.toNat ≤ mv_s.toNat ∧ p.1.toNat ≤ 2 * s0.core.cur_vars ∧
            p.2.1.toNat ≤ 2 * mv_s.toNat ∧ p.2.2.1.toNat ≤ acap_s.toNat ∧
            p.2.2.2.1.toNat ≤ p.2.1.toNat ∧
            (p.2.2.2.2.1 ≠ 4294967295#32 → (p.2.2.2.2.1 &&& 2047#32).toNat < 2001) ∧
            tmp1.length = c.max_vars ∧ wsort1.length = 2 * c.max_vars ∧
            tmk1.length = 2 * c.max_vars ∧ scr1.length = c.scratch_cap ∧
            FidK6cTmkReg p.1.toNat s0.core.cur_vars wsort1 tmk1 ∧
            FidK6cClsOk mv_s.toNat p.2.1.toNat p.2.2.1.toNat p.2.2.2.1.toNat scr1 ∧
            (∀ i, i < 4002 → scr1[i]? = s0.scratch.scratch_buf[i]?) ∧
            (∀ i, 4132 ≤ i → i < 4192 → scr1[i]? = s0.scratch.scratch_buf[i]?) ∧
            (FullMem c (FidP6Work s0 tmp1 wsort1 tmk1 scr1) ⋆ R) m1)
        (μ := fun p _ => 2 - p.2.2.2.2.2.2.1.toNat) ?_ ?_
      · intro J hJ; c0_hsteps
        refine hJ (0#32, 0#32, 0#32, 0#32, 4294967295#32, false, 0#32, ()) _
          ⟨s0.core.tmp, s0.scratch.wsort, s0.scratch.tarjan_mark,
          s0.scratch.scratch_buf, by simp, by simp, by simp, by simp, by simp, by simp,
          fun hne => absurd rfl hne, hinv.1.core_ok.tmp_len_arr, hinv.1.scratch_ok.wsort_len,
          hinv.1.scratch_ok.tarjan_mark_len, hscr_len,
          fid_k6c_tmkReg_init s0.core.cur_vars _ _ htmk0,
          ⟨by simp, fun _ h => by simp at h, by simp⟩,
          fun _ _ => rfl, fun _ _ _ => rfl, ?_⟩
        simpa only [fid_k6c_work_self] using hm0
      · intro J ⟨v_nv, v_nc, v_al, v_nu, v_tv, v_ab, v_st, ⟨⟩⟩ m1
          ⟨tmp1, wsort1, tmk1, scr1, hst_le, h1, h2, h3, h4, h5, htv, htp1, hws1, htm1, hs1,
            hr1, hc1, hp0, hp1, hm1⟩ hcont
        try dsimp only [Blocks.get, Member.here]
        apply wp_unroll_group
        intro Js_1 hJs_1
        have hExit : Js_1 () m1 := by
          apply hJs_1; try dsimp only [Blocks.get, Member.here]
          exact fid_k6c_init_solve_wp hWatch hSolve hCore hinv h16k hmv_lo hmv_hi hcap_eq
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            htp1 hws1 htm1 hs1 h1 h2 h3 h4 h5 hr1 htv hc1 hp0 hp1 hm1 hQ
        clear hJs_1
        c0_hsteps_nogrp
        · exact hExit
        · have hst_lt : v_st.toNat < 2 := by bv_omega
          have hst1 : (v_st + 1#32).toNat = v_st.toNat + 1 :=
            fid_k6c_add1_toNat hst_lt (by omega)
          c0_hsteps_nogrp
          refine wp_join_state (ts := [i32]) (fun (p : BitVec 32) => (p, ()))
            (fun side ma => (side = 0#32 ∨ side = 1#32) ∧ ma = m1) ?_ ?_
          · intro _ side ma ⟨hside, hma⟩
            subst ma
            c0_hsteps_nogrp
            refine wp_join_state (ts := [i32]) (fun (p : BitVec 32) => (p, ()))
              (fun cnt mb => (side = 0#32 → cnt = np) ∧ (side ≠ 0#32 → cnt = nn) ∧ mb = m1)
              ?_ ?_
            · intro _ cnt mb ⟨hcnt0, hcnt1, hmb⟩
              subst mb
              c0_hsteps_nogrp
              refine wp_join_state (ts := [i32]) (fun (p : BitVec 32) => (p, ()))
                (fun off mc => (side = 0#32 → off = 0#32) ∧ (side ≠ 0#32 → off = 2001#32) ∧
                  mc = m1) ?_ ?_
              · intro _ off mc ⟨hoff0, hoff1, hmc⟩
                subst mc
                c0_hsteps_nogrp
                refine wp_join_state (ts := [i32]) (fun (p : BitVec 32) => (p, ()))
                  (fun mask_off md => (side = 0#32 → mask_off = 4002#32) ∧
                    (side ≠ 0#32 → mask_off = 4066#32) ∧ md = m1) ?_ ?_
                · intro _ mask_off md ⟨hmb0, hmb1, hmd⟩
                  subst md
                  c0_hsteps_nogrp
                  refine wp_join_state (ts := [i32]) (fun (p : BitVec 32) => (p, ()))
                    (fun lit me => (side = 0#32 → lit = v <<< 1) ∧
                      (side ≠ 0#32 → lit = (v <<< 1) ||| 1#32) ∧ me = m1) ?_ ?_
                  · intro _ lit me ⟨hlit0, hlit1, hme⟩
                    subst me
                    obtain ⟨hcnt_le, hoff_val, hent⟩ :=
                      fid_k6c_side_setup hcv_lt hv hnp hnn hside hpos hneg
                        ⟨hcnt0, hcnt1⟩ ⟨hoff0, hoff1⟩ ⟨hmb0, hmb1⟩ ⟨hlit0, hlit1⟩
                    c0_hsteps_nogrp
                    apply wp_unroll_group
                    intro K284 hK284
                    have hL284 : ∀ nv'' nc'' alen'' n_units'' triv'' (ab'' : Bool)
                        (j_out : BitVec 32) (tmp' wsort' tmk' scr' : List (BitVec 32))
                        (m' : Mem 64),
                        tmp'.length = c.max_vars → wsort'.length = 2 * c.max_vars →
                        tmk'.length = 2 * c.max_vars → scr'.length = c.scratch_cap →
                        nv''.toNat ≤ mv_s.toNat → nv''.toNat ≤ 2 * s0.core.cur_vars →
                        nc''.toNat ≤ 2 * mv_s.toNat → alen''.toNat ≤ acap_s.toNat →
                        n_units''.toNat ≤ nc''.toNat →
                        (triv'' ≠ 4294967295#32 → (triv'' &&& 2047#32).toNat < 2001) →
                        FidK6cTmkReg nv''.toNat s0.core.cur_vars wsort' tmk' →
                        FidK6cClsOk mv_s.toNat nc''.toNat alen''.toNat n_units''.toNat scr' →
                        (∀ i, i < 4002 → scr'[i]? = s0.scratch.scratch_buf[i]?) →
                        (∀ i, 4132 ≤ i → i < 4192 → scr'[i]? = s0.scratch.scratch_buf[i]?) →
                        (FullMem c (FidP6Work s0 tmp' wsort' tmk' scr') ⋆ R) m' →
                        K284 (nv'', nc'', alen'', n_units'', triv'', ab'', j_out, ()) m' := by
                      intro nv'' nc'' alen'' n_units'' triv'' ab'' j_out tmp' wsort' tmk' scr' m'
                        ht' hw' htm' hs' ha hb hd he hf hg hr hc' p0 p1 hm'
                      apply hK284; try dsimp only [Blocks.get, Member.here]
                      c0_hsteps
                      exact hcont (nv'', nc'', alen'', n_units'', triv'', ab'', v_st + 1#32, ()) m'
                        (by dsimp only; omega)
                        ⟨tmp', wsort', tmk', scr', by dsimp only; omega,
                          ha, hb, hd, he, hf, hg, ht', hw', htm', hs', hr, hc', p0, p1, hm'⟩
                    clear hK284
                    exact fid_k6c_inner_loop_wp (abort_in := v_ab) (second_pass := second_pass)
                      hinv hmv_lo hmv_hi hmv2 hcap_eq ⟨hmc1, hmc2⟩
                      htp1 hws1 htm1 hs1 rfl rfl rfl rfl rfl
                      h1 h2 h3 h4 h5 htv hside hcnt_le hoff_val hent hr1 hc1 hp0 hp1 hm1 hL284
                  · intro Jl hJl; c0_hsplit
                    · c0_hsteps; exact hJl (v <<< 1) m1
                        ⟨fun _ => rfl, fun h => absurd hc h, rfl⟩
                    · c0_hsteps; exact hJl ((v <<< 1) ||| 1#32) m1
                        ⟨fun h => absurd h hc, fun _ => rfl, rfl⟩
                · intro Jm hJm; c0_hsplit
                  · c0_hsteps; exact hJm 4002#32 m1
                      ⟨fun _ => rfl, fun h => absurd hc h, rfl⟩
                  · c0_hsteps; exact hJm 4066#32 m1
                      ⟨fun h => absurd h hc, fun _ => rfl, rfl⟩
              · intro Jo hJo; c0_hsplit
                · c0_hsteps; exact hJo 0#32 m1
                    ⟨fun _ => rfl, fun h => absurd hc h, rfl⟩
                · c0_hsteps; exact hJo 2001#32 m1
                    ⟨fun h => absurd h hc, fun _ => rfl, rfl⟩
            · intro Jc hJc; c0_hsplit
              · c0_hsteps; exact hJc np m1 ⟨fun _ => rfl, fun h => absurd hc h, rfl⟩
              · c0_hsteps; exact hJc nn m1
                  ⟨fun h => absurd h hc, fun _ => rfl, rfl⟩
          · intro Js hJs
            cases second_pass
            · c0_hsplit; c0_hsteps; refine hJs v_st m1 ⟨?_, rfl⟩
              rcases (by omega : v_st.toNat = 0 ∨ v_st.toNat = 1) with h0 | h1
              · left; exact BitVec.eq_of_toNat_eq h0
              · right; exact BitVec.eq_of_toNat_eq h1
            · c0_hsplit
              · c0_hsteps; refine hJs (1#32 - v_st) m1 ⟨?_, rfl⟩
                rcases (by omega : v_st.toNat = 0 ∨ v_st.toNat = 1) with h0 | h1
                · right; exact BitVec.eq_of_toNat_eq (by bv_omega)
                · left; exact BitVec.eq_of_toNat_eq (by bv_omega)
              · cases hc
        · exact hExit
        · exact hExit
    · intro Jm hJm
      c0_hsplit
      · c0_hsteps!; exact hJm (BitVec.setWidth 32 (BitVec.ofNat 64 c.max_vars)) m0
          ⟨by rw [fid_k6c_trunc_ofNat64_toNat _
                (by have := c.hmaxv; simp only [dimacsBound] at this; omega)]
              exact Nat.le_refl _,
           by have hc' : c.max_vars % 2 ^ 64 < 65535 := by simpa using hc
              have := c.hmaxv; simp only [dimacsBound] at this
              rw [fid_k6c_trunc_ofNat64_toNat _ (by omega)]
              rw [Nat.mod_eq_of_lt (by omega)] at hc'; omega,
           rfl⟩
      · c0_hsteps!; exact hJm 65535#32 m0
          ⟨by have hc' : ¬ c.max_vars % 2 ^ 64 < 65535 := by simpa using hc
              have := c.hmaxv; simp only [dimacsBound] at this
              rw [Nat.mod_eq_of_lt (by omega)] at hc'
              rw [show (65535#32 : BitVec 32).toNat = 65535 from rfl]; omega,
           by decide, rfl⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Definition
