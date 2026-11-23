/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7BcpHotProof1bExpr

/-!
# Kissat M7 Hot-Path Fused BCP Proofs — Part 1b0 (`Lp` Helper Sub-Lemmas)

Zero `import all`, plain `public section` (`0` `@[expose]`).
Proves `m7_lp_assign_tail_wp`, `m7_lp_repl_scan_wp`, `m7_lp_max_lvl_wp`, and
`m7_lp_repl_push_wp` against the exact AST builders in `FullM7BcpHotProof1bExpr`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7BcpHot

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FastCore
open LeanQbe.T.Examples.Kissat.FullM5Otfs
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeHelpers
open LeanQbe.T.Examples.Kissat.Full.FullPropDecSpecs hiding
  fullWatchPushSpec fullPropLitSpec fullPropagateIgnoreSpec fullPropagateSpec
  FullTrailExt FullArenaPermEq
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

attribute [local irreducible] fastPropMem

local macro "m7_hsteps" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps))

local macro "m7_hsteps_nogrp" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps_nogrp))

local macro "m7_hsplit" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsplit))

theorem m7_fpm_with_wvec (s0 sem : FullState) (wv' : List (BitVec 32)) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with wvec := wv' } } =
      fastPropMem s0 { sem with core := { sem.core with wvec := wv' } } := by
  unfold fastPropMem; rfl

theorem m7_fpm_with_wlen (s0 sem : FullState) (wl' : Nat) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with wlen := wl' } } =
      fastPropMem s0 { sem with core := { sem.core with wlen := wl' } } := by
  unfold fastPropMem; rfl

theorem m7_fpm_with_wusable (s0 sem : FullState) (wu' : BitVec 64) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with wusable := wu' } } =
      fastPropMem s0 { sem with core := { sem.core with wusable := wu' } } := by
  unfold fastPropMem; rfl

theorem m7_bv8_slt0_of_neg_sge (x : BitVec 8)
    (h : ¬ ((BitVec.signExtend 32 x).toInt ≥ 0)) :
    (BitVec.signExtend 32 x).slt 0#32 = true := by
  rw [BitVec.slt_eq_decide, show (0#32 : BitVec 32).toInt = 0 from by decide]
  exact decide_eq_true (by omega)

theorem m7_bv8_sle0_of_sge (x : BitVec 8)
    (h : (BitVec.signExtend 32 x).toInt ≥ 0) :
    (0#32).sle (BitVec.signExtend 32 x) = true := by
  rw [BitVec.sle_eq_decide, show (0#32 : BitVec 32).toInt = 0 from by decide]
  exact decide_eq_true (by omega)

theorem m7_garb_after_set1 (k : FullCoreState) {cref i : Nat} {v : BitVec 32} (h : i ≠ cref) :
    fullArenaClauseGarbCore { k with arena := k.arena.set i v } cref =
      fullArenaClauseGarbCore k cref := by
  unfold fullArenaClauseGarbCore fullArenaHdrCore
  rw [List.getElem?_set_ne h]

/-! ## 1. Inline Assignment Tail (`m7LpAssignTailExpr`) -/

theorem m7_lp_assign_tail_wp {Γ : Env} {rs : List Ty} {c : FullCfg}
    {s_disk sem : FullState} {vals' : List (BitVec 8)} {not_lit new_lit alvl : BitVec 32}
    {rec_ph : Bool} {te un uf tk_next p_next q_next v_idx : BitVec 64}
    {rsn_cref : Option (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    {J_lp : Cont [i64, i64, i64, i64, i64, i64]}
    (hmaxv : c.max_vars < 2 * dimacsBound)
    (hlen_sem : sem.LengthsOk c)
    (_hvals' : vals'.length = 2 * c.max_vars)
    (hte_lt : sem.core.trail_end < sem.core.cur_vars)
    (hte_eq : te.toNat = sem.core.trail_end)
    (hnew_lt : new_lit.toNat < 2 * sem.core.cur_vars)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (hvidx : v_idx.toNat = new_lit.toNat / 2)
    (hm : (FullMem c { fastPropMem s_disk sem with
        core := { (fastPropMem s_disk sem).core with vals := vals' } } ⋆ R) m)
    (hJ : ∀ (flags' : List (BitVec 32)) (ph' : List (BitVec 8))
        (un_n uf_n : BitVec 64) (m' : Mem 64),
      flags'.length = c.max_vars → ph'.length = c.max_vars →
      let rsn_val := match rsn_cref with
        | none => (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32
        | some cref => cref
      let sem' : FullState :=
        { core :=
            { sem.core with
              vals := vals', flags := flags'
              lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl
              rsns := sem.core.rsns.set (new_lit.toNat / 2)
                (if alvl = 0#32 then 0xFFFFFFFF#32 else rsn_val)
              trl := sem.core.trl.set sem.core.trail_end new_lit
              trail_pos := sem.core.trail_pos.set (new_lit.toNat / 2)
                (BitVec.ofNat 32 sem.core.trail_end)
              trail_end := sem.core.trail_end + 1
              unassigned := un_n, unflushed := uf_n }
          scratch := { sem.scratch with phases := ph' } }
      (FullMem c (fastPropMem s_disk sem') ⋆ R) m' →
      wp Γ Q X (.jump J_lp (.var (te + 1#64), (.var un_n, (.var uf_n,
        (.var tk_next, (.var p_next, (.var q_next, ()))))))) m') :
    wp Γ Q X (m7LpAssignTailExpr c.pLevel c.pReason c.pTrail c.pTrailPos c.pFlags c.pPhases
      rec_ph not_lit te un uf tk_next p_next q_next v_idx new_lit alvl rsn_cref J_lp) m := by
  unfold dimacsBound at hmaxv
  have hcv := hlen_sem.core_ok.cur_vars_le
  have hfl_len := hlen_sem.core_ok.flags_len
  have hph_len := hlen_sem.scratch_ok.phases_len
  have hlvl_len := hlen_sem.core_ok.lvl_len
  have hrsn_len := hlen_sem.core_ok.rsns_len
  have htp_len := hlen_sem.core_ok.trail_pos_len
  have htrl_len := hlen_sem.core_ok.trl_len
  have hv_mv : new_lit.toNat / 2 < c.max_vars := by omega
  have hte_mv : sem.core.trail_end < c.max_vars := by omega
  have h2cv_31 : not_lit.toNat < 2 ^ 31 := by omega
  have hm_v : (FullMem c (fastPropMem s_disk { sem with
      core := { sem.core with vals := vals' } }) ⋆ R) m := by
    simpa only [m7_fastPropMem_with_vals] using hm
  have htpos32 : te.setWidth 32 = BitVec.ofNat 32 sem.core.trail_end := by
    apply BitVec.eq_of_toNat_eq
    have hte32 : sem.core.trail_end < 2 ^ 32 := by omega
    rw [BitVec.toNat_setWidth, hte_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hte32]
  unfold m7LpAssignTailExpr
  refine wp_join_group (fun (un_n, ()) mu => mu = m) ?_ ?_
  · rintro _ ⟨un_n, ⟨⟩⟩ mu hmu
    dsimp only at hmu
    rw [hmu]
    clear hmu
    refine wp_join_group (fun _ mph => ∃ ph' : List (BitVec 8), ph'.length = c.max_vars ∧
        (FullMem c (fastPropMem s_disk { sem with
          core := { sem.core with vals := vals' }
          scratch := { sem.scratch with phases := ph' } }) ⋆ R) mph) ?_ ?_
    · rintro _ ⟨⟩ mph ⟨ph', hph', hmph⟩
      have hlvl_m : (fastPropMem s_disk { sem with
          core := { sem.core with vals := vals' }
          scratch := { sem.scratch with phases := ph' } }).core.lvl.length =
          c.max_vars := by
        rw [fastPropMem_lvl]; exact hlvl_len
      m7_hsteps_nogrp
      have hml : (FullMem c (fastPropMem s_disk { sem with
          core :=
            { sem.core with
              vals := vals', lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl }
          scratch := { sem.scratch with phases := ph' } }) ⋆ R) m := by
        simpa only [fastPropMem_lvl, hvidx, m7_fastPropMem_with_lvl] using hm
      clear hm
      let rsn_v : BitVec 32 := match rsn_cref with
        | none => (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32
        | some cref => cref
      have hrsn_bin : 2147483648#32 ||| not_lit =
          (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32 := by
        rw [m7_bv32_mask7f_eq h2cv_31, BitVec.or_comm]
      refine wp_join_group (fun (uf_n, ()) maf =>
          ∃ flags' : List (BitVec 32), flags'.length = c.max_vars ∧
          (FullMem c (fastPropMem s_disk { sem with
            core :=
              { sem.core with
                vals := vals', flags := flags'
                lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl
                rsns := sem.core.rsns.set (new_lit.toNat / 2)
                  (if alvl = 0#32 then 0xFFFFFFFF#32 else rsn_v) }
            scratch := { sem.scratch with phases := ph' } }) ⋆ R) maf) ?_ ?_
      · rintro _ ⟨uf_n, ⟨⟩⟩ maf ⟨flags', hfl', hmaf⟩
        have htp_m : (fastPropMem s_disk { sem with
            core :=
              { sem.core with
                vals := vals', flags := flags'
                lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl
                rsns := sem.core.rsns.set (new_lit.toNat / 2)
                  (if alvl = 0#32 then 0xFFFFFFFF#32 else rsn_v) }
            scratch := { sem.scratch with phases := ph' } }).core.trail_pos.length =
            c.max_vars := by
          rw [fastPropMem_trail_pos]; exact htp_len
        have htrl_m : (fastPropMem s_disk { sem with
            core :=
              { sem.core with
                vals := vals', flags := flags'
                lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl
                rsns := sem.core.rsns.set (new_lit.toNat / 2)
                  (if alvl = 0#32 then 0xFFFFFFFF#32 else rsn_v)
                trail_pos := sem.core.trail_pos.set (new_lit.toNat / 2)
                  (BitVec.ofNat 32 sem.core.trail_end) }
            scratch := { sem.scratch with phases := ph' } }).core.trl.length =
            c.max_vars := by
          rw [fastPropMem_trl]; exact htrl_len
        m7_hsteps
        refine wp_store_sep (FullArenaTactics.c0_store_full_trl new_lit
          (by rw [fastPropMem_trl, hte_eq, htrl_len]; exact hte_mv) hm) ?_
        intro mtr hmtr'; clear hm
        m7_hsteps
        have hmtr :
            (FullMem c (fastPropMem s_disk {
              core :=
                { sem.core with
                  vals := vals', flags := flags'
                  lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl
                  rsns := sem.core.rsns.set (new_lit.toNat / 2)
                    (if alvl = 0#32 then 0xFFFFFFFF#32 else rsn_v)
                  trl := sem.core.trl.set sem.core.trail_end new_lit
                  trail_pos := sem.core.trail_pos.set (new_lit.toNat / 2)
                    (BitVec.ofNat 32 sem.core.trail_end)
                  trail_end := sem.core.trail_end + 1
                  unassigned := un_n, unflushed := uf_n }
              scratch := { sem.scratch with phases := ph' } }) ⋆ R) mtr := by
          refine Eq.mp (congrArg (fun k => (FullMem c k ⋆ R) mtr) ?_) hmtr'
          unfold fastPropMem
          dsimp only
          simp only [hvidx, htpos32, hte_eq]
        rcases rsn_cref with _ | rsn_c <;> dsimp only [rsn_v] at hmtr
        · exact hJ flags' ph' un_n uf_n mtr hfl' hph' hmtr
        · exact hJ flags' ph' un_n uf_n mtr hfl' hph' hmtr
      · intro Junfl hJunfl
        have hrsn_m : (fastPropMem s_disk { sem with
            core :=
              { sem.core with
                vals := vals', lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl }
            scratch := { sem.scratch with phases := ph' } }).core.rsns.length =
            c.max_vars := by
          rw [fastPropMem_rsns]; exact hrsn_len
        have hfl_m' : (fastPropMem s_disk { sem with
            core :=
              { sem.core with
                vals := vals', lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl
                rsns := sem.core.rsns.set v_idx.toNat 0xFFFFFFFF#32 }
            scratch := { sem.scratch with phases := ph' } }).core.flags.length =
            c.max_vars := by
          rw [fastPropMem_flags]; exact hfl_len
        m7_hsplit
        · have hal0 : alvl = 0#32 := hc
          m7_hsteps_nogrp
          simp only [fastPropMem_rsns, m7_fastPropMem_with_rsns] at hm
          m7_hsteps
          refine hJunfl (uf + 1#64, ()) m
            ⟨sem.core.flags.set (new_lit.toNat / 2) ?fv_al0,
              by rw [List.length_set, hfl_len], ?hm_al0⟩
          case hm_al0 =>
            rw [show (if alvl = 0#32 then 0xFFFFFFFF#32 else rsn_v) = 0xFFFFFFFF#32 from
              by simp only [hal0, ↓reduceIte]]
            refine Eq.mp (congrArg (fun k => (FullMem c k ⋆ R) m) ?_) hm
            unfold fastPropMem; dsimp only; simp only [hvidx]; rfl
        · have hal_ne0 : alvl ≠ 0#32 := hc
          cases rsn_cref with
          | none =>
            m7_hsteps
            have hrsn_bin' : BitVec.ofNat 32 2147483648 ||| not_lit =
                (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32 := hrsn_bin
            have hmrs : (FullMem c (fastPropMem s_disk { sem with
                core :=
                  { sem.core with
                    vals := vals', lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl
                    rsns := sem.core.rsns.set (new_lit.toNat / 2)
                      ((not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32) }
                scratch := { sem.scratch with phases := ph' } }) ⋆ R) m := by
              refine Eq.mp ?_ hm
              congr 2
              unfold fastPropMem
              simp only [hvidx, show (2147483648 : BitVec 32) ||| not_lit =
                (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32 from hrsn_bin']
            exact hJunfl (uf, ()) m ⟨sem.core.flags, hfl_len, by
              simpa only [hal_ne0, ↓reduceIte, rsn_v] using hmrs⟩
          | some cref =>
            m7_hsteps
            have hmrs : (FullMem c (fastPropMem s_disk { sem with
                core :=
                  { sem.core with
                    vals := vals', lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl
                    rsns := sem.core.rsns.set (new_lit.toNat / 2) cref }
                scratch := { sem.scratch with phases := ph' } }) ⋆ R) m := by
              simpa only [fastPropMem_rsns, hvidx, m7_fastPropMem_with_rsns] using hm
            exact hJunfl (uf, ()) m ⟨sem.core.flags, hfl_len, by
              simpa only [hal_ne0, ↓reduceIte, rsn_v] using hmrs⟩
    · intro Jph hJph
      have hph_m : (fastPropMem s_disk { sem with
          core := { sem.core with vals := vals' } }).scratch.phases.length = c.max_vars := by
        rw [fastPropMem_phases]; exact hph_len
      m7_hsplit
      · refine wp_join_group (fun _ mph => ∃ ph' : List (BitVec 8), ph'.length = c.max_vars ∧
            (FullMem c (fastPropMem s_disk { sem with
              core := { sem.core with vals := vals' }
              scratch := { sem.scratch with phases := ph' } }) ⋆ R) mph) ?_ ?_
        · rintro _ ⟨⟩ mph ⟨ph', hph', hmph⟩
          m7_hsteps
          exact hJph () mph ⟨ph', hph', hmph⟩
        · intro Jp2 hJp2
          m7_hsplit
          · m7_hsteps
            rw [fastPropMem_phases, hvidx, m7_fastPropMem_with_phases] at hm
            exact hJp2 () m ⟨_, by rw [List.length_set, hph_len], hm⟩
          · m7_hsteps
            rw [fastPropMem_phases, hvidx, m7_fastPropMem_with_phases] at hm
            exact hJp2 () m ⟨_, by rw [List.length_set, hph_len], hm⟩
      · m7_hsteps
        exact hJph () m ⟨sem.scratch.phases, hph_len, hm_v⟩
  · intro Jun hJun
    have hfl_m : (fastPropMem s_disk { sem with
        core := { sem.core with vals := vals' } }).core.flags.length = c.max_vars := by
      rw [fastPropMem_flags]; exact hfl_len
    m7_hsteps
    · exact hJun (un - 1#64, ()) m rfl
    · exact hJun (un, ()) m rfl
    · exact hJun (un, ()) m rfl

/-! ## 2. Replacement Scan (`m7LpReplScanExpr`) & Max-Level (`m7LpMaxLvlExpr`) -/

theorem m7_lp_repl_scan_arg_wp {Γ : Env} {rs : List Ty} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s_pi s_disk sem : FullState}
    {not_lit cref : BitVec 32} {off_v p_v q_v end_v cbase bound_v : BitVec 64}
    {init_a : Arg Val i64} {lit_a : Arg Val i32} {found_a : Arg Val Ty.bool}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    {J_out : Cont [i64, i32, Ty.bool]}
    (har : c.arena_cap < 2 * dimacsBound)
    (hpi : PropLitInv c F0 F_cur s_pi sem not_lit.toNat off_v.toNat q_v.toNat p_v.toNat end_v.toNat)
    (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore sem.core)
    (hng : fullArenaClauseGarbCore sem.core cref.toNat = false)
    (hfit : cref.toNat + 3 + fullArenaClauseSizeCore sem.core cref.toNat ≤ sem.core.arena_len)
    (hcbase : cbase.toNat = cref.toNat + 3)
    (hbound : bound_v.toNat ≤ fullArenaClauseSizeCore sem.core cref.toNat)
    (hinit : init_a.val.toNat ≤ bound_v.toNat)
    (hexit_f : found_a.val = false)
    (hm : (FullMem c (fastPropMem s_disk sem) ⋆ R) m)
    (hJ : ∀ (ri : BitVec 64) (repl : BitVec 32) (found : Bool),
      ((found = true ∧ init_a.val.toNat ≤ ri.toNat ∧
        ∃ hr_lt : ri.toNat < bound_v.toNat,
          have hcsz : ri.toNat < fullArenaClauseSizeCore sem.core cref.toNat :=
            Nat.lt_of_lt_of_le hr_lt hbound
          have har_len : cref.toNat + 3 + ri.toNat < sem.core.arena.length := by
            rw [hpi.len.core_ok.arena_len_arr]
            exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hcsz _)
              (Nat.le_trans hfit hpi.len.core_ok.arena_len_le)
          repl = sem.core.arena[cref.toNat + 3 + ri.toNat]'har_len ∧
          repl.toNat < 2 * sem.core.cur_vars ∧
          ((sem.core.vals[repl.toNat]?.getD 0#8).signExtend 32).slt 0#32 = false) ∨
       (found = false ∧ repl = lit_a.val ∧ ri = bound_v ∧
        ∀ k, init_a.val.toNat ≤ k → k < bound_v.toNat → fullFindReplBad sem cref.toNat k)) →
      wp Γ Q X (.jump J_out (.var ri, (.var repl, (.var found, ())))) m) :
    wp Γ Q X (m7LpReplScanExpr c.pVals c.pArena cbase bound_v init_a lit_a found_a J_out) m := by
  unfold dimacsBound at har
  have haren := hpi.len.core_ok.arena_len_arr
  have halen_le := hpi.len.core_ok.arena_len_le
  have hvals_len := hpi.len.core_ok.vals_len
  have hcv := hpi.len.core_ok.cur_vars_le
  have hm_aren : (fastPropMem s_disk sem).core.arena.length = c.arena_cap := by
    rw [fastPropMem_arena]; exact haren
  have hm_vals : (fastPropMem s_disk sem).core.vals.length = 2 * c.max_vars := by
    rw [fastPropMem_vals]; exact hvals_len
  have hfit_cap : cref.toNat + 3 + fullArenaClauseSizeCore sem.core cref.toNat ≤ c.arena_cap :=
    Nat.le_trans hfit halen_le
  have hcap64 : c.arena_cap < 2 ^ 64 := Nat.lt_trans har (by decide)
  have hbd : cref.toNat + 3 + fullArenaClauseSizeCore sem.core cref.toNat ≤
      sem.core.arena.length := haren ▸ hfit_cap
  unfold m7LpReplScanExpr
  refine wp_loop_group (fun rem (idx, ()) ml =>
      ml = m ∧ rem = bound_v.toNat - idx.toNat ∧
      init_a.val.toNat ≤ idx.toNat ∧ idx.toNat ≤ bound_v.toNat ∧
      ∀ k, init_a.val.toNat ≤ k → k < idx.toNat → fullFindReplBad sem cref.toNat k) ?_ ?_
  · rintro L rem ⟨idx, ⟨⟩⟩ ml ih ⟨hml_eq, rfl, hinit_le, hidx_le, hbad⟩
    rw [hml_eq]; clear hml_eq
    m7_hsplit
    · have hidx_lt : idx.toNat < bound_v.toNat := hc
      have hcsz_lt : idx.toNat < fullArenaClauseSizeCore sem.core cref.toNat :=
        Nat.lt_of_lt_of_le hidx_lt hbound
      have hidx_ar : (cbase + idx).toNat = cref.toNat + 3 + idx.toNat := by
        rw [m7_bv64_add_toNat (by rw [hcbase]; omega), hcbase]
      have har_idx_lt : (cbase + idx).toNat < (fastPropMem s_disk sem).core.arena.length := by
        rw [hm_aren, hidx_ar]; omega
      have har_raw_lt : cref.toNat + 3 + idx.toNat < sem.core.arena.length := by
        rw [haren]; omega
      let cand := (fastPropMem s_disk sem).core.arena[(cbase + idx).toNat]'har_idx_lt
      have hcand_eq : cand = sem.core.arena[cref.toNat + 3 + idx.toNat]'har_raw_lt := by
        dsimp only [cand]
        exact (fc_getElem_arena s_disk sem).trans
          (fc_getElem_eq_of_idx hidx_ar (hidx_ar ▸ har_raw_lt) har_raw_lt)
      have hcand_mem : cand.toNat ∈ fullArenaClauseLitsCore sem.core cref.toNat :=
        (mem_fullArenaClauseLitsCore_iff hbd).mpr
          ⟨idx.toNat, hcsz_lt, congrArg BitVec.toNat hcand_eq.symm⟩
      have hcand_lt : cand.toNat < 2 * sem.core.cur_vars :=
        hpi.nw.arena.lits_lt cref.toNat hcr_ref hng cand.toNat hcand_mem
      have hcand_vals_m : (cand.setWidth 64).toNat < (fastPropMem s_disk sem).core.vals.length := by
        rw [hm_vals, bv_c0_zext32_64]; omega
      have hcand_vals_raw : cand.toNat < sem.core.vals.length := by
        rw [hvals_len]; omega
      have hidx1_n : (idx + 1#64).toNat = idx.toNat + 1 := m7_bv64_add1_toNat (by omega)
      let vb := (fastPropMem s_disk sem).core.vals[(cand.setWidth 64).toNat]'hcand_vals_m
      have hvb_eq : vb = sem.core.vals[cand.toNat]'hcand_vals_raw := by
        dsimp only [vb]
        exact (fc_getElem_vals s_disk sem).trans
          (fc_getElem_eq_of_idx (bv_c0_zext32_64 cand) _ hcand_vals_raw)
      m7_hsteps
      · have hcb_mod : (cbase.toNat + idx.toNat) % 2 ^ 64 = (cbase + idx).toNat :=
          (BitVec.toNat_add cbase idx).symm
        have hsle0 : (0#32).sle (BitVec.signExtend 32 vb) = true := by
          simpa only [vb, bv_c0_zext32_64, hcb_mod] using hc
        have hslt0 : ((sem.core.vals[cand.toNat]?.getD 0#8).signExtend 32).slt 0#32 = false := by
          rw [List.getElem?_eq_getElem hcand_vals_raw, Option.getD_some, ← hvb_eq]
          cases hlt : (BitVec.signExtend 32 vb).slt 0#32
          · rfl
          · rw [bv32_sle0_eq_not_slt0, hlt] at hsle0; simp at hsle0
        exact hJ idx cand true (Or.inl ⟨rfl, hinit_le, hidx_lt, hcand_eq, hcand_lt, by
          simpa only [hcand_eq] using hslt0⟩)
      · have hcb_mod : (cbase.toNat + idx.toNat) % 2 ^ 64 = (cbase + idx).toNat :=
          (BitVec.toNat_add cbase idx).symm
        have hnsle0 : (0#32).sle (BitVec.signExtend 32 vb) = false := by
          simpa only [vb, bv_c0_zext32_64, hcb_mod] using hc
        have hslt : (BitVec.signExtend 32 vb).slt 0#32 = true := by
          cases hlt : (BitVec.signExtend 32 vb).slt 0#32
          · rw [bv32_sle0_eq_not_slt0, hlt] at hnsle0; simp at hnsle0
          · rfl
        have hbad_idx : fullFindReplBad sem cref.toNat idx.toNat := by
          unfold fullFindReplBad
          refine Or.inr ?_
          rw [List.getElem?_eq_getElem har_raw_lt, Option.getD_some, ← hcand_eq,
            List.getElem?_eq_getElem hcand_vals_raw, Option.getD_some, ← hvb_eq]
          exact hslt
        exact ih _ (idx + 1#64, ()) m (by rw [hidx1_n]; omega)
          ⟨rfl, rfl, by rw [hidx1_n]; omega, by rw [hidx1_n]; omega, fun k hk1 hk2 => by
            rw [hidx1_n] at hk2
            rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk2) with hk' | rfl
            · exact hbad k hk1 hk'
            · exact hbad_idx⟩
    · have hidx_eq : idx = bound_v := BitVec.eq_of_toNat_eq (by omega)
      subst hidx_eq
      m7_hsteps
      rw [hexit_f] at *
      exact hJ idx lit_a.val false (Or.inr ⟨rfl, rfl, rfl, hbad⟩)
  · intro L hL
    m7_hsteps
    exact hL _ (init_a.val, ()) m ⟨rfl, rfl, Nat.le_refl _, hinit, fun _ hk1 hk2 => by omega⟩

theorem m7_lp_repl_scan_wp {Γ : Env} {rs : List Ty} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s_pi s_disk sem : FullState}
    {not_lit cref exit_lit : BitVec 32} {off_v p_v q_v end_v cbase bound_v init_idx : BitVec 64}
    {exit_found : Bool} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    {J_out : Cont [i64, i32, Ty.bool]}
    (har : c.arena_cap < 2 * dimacsBound)
    (hpi : PropLitInv c F0 F_cur s_pi sem not_lit.toNat off_v.toNat q_v.toNat p_v.toNat end_v.toNat)
    (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore sem.core)
    (hng : fullArenaClauseGarbCore sem.core cref.toNat = false)
    (hfit : cref.toNat + 3 + fullArenaClauseSizeCore sem.core cref.toNat ≤ sem.core.arena_len)
    (hcbase : cbase.toNat = cref.toNat + 3)
    (hbound : bound_v.toNat ≤ fullArenaClauseSizeCore sem.core cref.toNat)
    (hinit : init_idx.toNat ≤ bound_v.toNat)
    (hexit_f : exit_found = false)
    (hm : (FullMem c (fastPropMem s_disk sem) ⋆ R) m)
    (hJ : ∀ (ri : BitVec 64) (repl : BitVec 32) (found : Bool),
      ((found = true ∧ init_idx.toNat ≤ ri.toNat ∧
        ∃ hr_lt : ri.toNat < bound_v.toNat,
          have hcsz : ri.toNat < fullArenaClauseSizeCore sem.core cref.toNat :=
            Nat.lt_of_lt_of_le hr_lt hbound
          have har_len : cref.toNat + 3 + ri.toNat < sem.core.arena.length := by
            rw [hpi.len.core_ok.arena_len_arr]
            exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hcsz _)
              (Nat.le_trans hfit hpi.len.core_ok.arena_len_le)
          repl = sem.core.arena[cref.toNat + 3 + ri.toNat]'har_len ∧
          repl.toNat < 2 * sem.core.cur_vars ∧
          ((sem.core.vals[repl.toNat]?.getD 0#8).signExtend 32).slt 0#32 = false) ∨
       (found = false ∧ repl = exit_lit ∧ ri = bound_v ∧
        ∀ k, init_idx.toNat ≤ k → k < bound_v.toNat → fullFindReplBad sem cref.toNat k)) →
      wp Γ Q X (.jump J_out (.var ri, (.var repl, (.var found, ())))) m) :
    wp Γ Q X (m7LpReplScanExpr c.pVals c.pArena cbase bound_v (.var init_idx) (.var exit_lit)
      (.var exit_found) J_out) m :=
  m7_lp_repl_scan_arg_wp har hpi hcr_ref hng hfit hcbase hbound hinit hexit_f hm hJ

theorem m7_lp_max_lvl_wp {Γ : Env} {rs : List Ty} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s_pi s_disk sem : FullState} {not_lit cref other : BitVec 32}
    {off_v p_v q_v end_v cbase csz64 : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post rs} {X : XPost} {J_alvl : Cont [i32]}
    (har : c.arena_cap < 2 * dimacsBound)
    (hpi : PropLitInv c F0 F_cur s_pi sem not_lit.toNat off_v.toNat q_v.toNat p_v.toNat end_v.toNat)
    (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore sem.core)
    (hng : fullArenaClauseGarbCore sem.core cref.toNat = false)
    (hfit : cref.toNat + 3 + fullArenaClauseSizeCore sem.core cref.toNat ≤ sem.core.arena_len)
    (hcbase : cbase.toNat = cref.toNat + 3)
    (hcsz : csz64.toNat = fullArenaClauseSizeCore sem.core cref.toNat)
    (hm : (FullMem c (fastPropMem s_disk sem) ⋆ R) m)
    (hJ : ∀ alvl : BitVec 32,
      (∀ l ∈ fullArenaClauseLitsCore sem.core cref.toNat, l ≠ other.toNat →
        (sem.core.lvl[l / 2]?.getD 0#32).toNat ≤ alvl.toNat) →
      (alvl = 0#32 ∨ ∃ l ∈ fullArenaClauseLitsCore sem.core cref.toNat,
        l ≠ other.toNat ∧ alvl = sem.core.lvl[l / 2]?.getD 0#32) →
      wp Γ Q X (.jump J_alvl (.var alvl, ())) m) :
    wp Γ Q X (m7LpMaxLvlExpr c.pArena c.pLevel cbase csz64 other J_alvl) m := by
  unfold dimacsBound at har
  have haren := hpi.len.core_ok.arena_len_arr
  have halen_le := hpi.len.core_ok.arena_len_le
  have hlvl_len := hpi.len.core_ok.lvl_len
  have hcv := hpi.len.core_ok.cur_vars_le
  have hm_aren : (fastPropMem s_disk sem).core.arena.length = c.arena_cap := by
    rw [fastPropMem_arena]; exact haren
  have hm_lvl : (fastPropMem s_disk sem).core.lvl.length = c.max_vars := by
    rw [fastPropMem_lvl]; exact hlvl_len
  have hfit_cap : cref.toNat + 3 + fullArenaClauseSizeCore sem.core cref.toNat ≤ c.arena_cap :=
    Nat.le_trans hfit halen_le
  have hcap64 : c.arena_cap < 2 ^ 64 := Nat.lt_trans har (by decide)
  have hbd : cref.toNat + 3 + fullArenaClauseSizeCore sem.core cref.toNat ≤
      sem.core.arena.length := haren ▸ hfit_cap
  unfold m7LpMaxLvlExpr
  refine wp_loop_group (fun rem (mx, k, ()) ml =>
      ml = m ∧ rem = csz64.toNat - k.toNat ∧ k.toNat ≤ csz64.toNat ∧
      (∀ j < k.toNat, ∀ hj : cref.toNat + 3 + j < sem.core.arena.length,
        (sem.core.arena[cref.toNat + 3 + j]'hj).toNat ≠ other.toNat →
        (sem.core.lvl[(sem.core.arena[cref.toNat + 3 + j]'hj).toNat / 2]?.getD 0#32).toNat ≤
          mx.toNat) ∧
      (mx = 0#32 ∨ ∃ j < k.toNat, ∃ hj : cref.toNat + 3 + j < sem.core.arena.length,
        (sem.core.arena[cref.toNat + 3 + j]'hj).toNat ≠ other.toNat ∧
        mx = sem.core.lvl[(sem.core.arena[cref.toNat + 3 + j]'hj).toNat / 2]?.getD 0#32)) ?_ ?_
  · rintro L rem ⟨mx, k, ⟨⟩⟩ ml ih ⟨hml_eq, rfl, hk_le, hge, hatt⟩
    rw [hml_eq]; clear hml_eq
    m7_hsplit
    · have hk_lt : k.toNat < csz64.toNat := hc
      have hk_csz : k.toNat < fullArenaClauseSizeCore sem.core cref.toNat := hcsz ▸ hk_lt
      have hk_ar : (cbase + k).toNat = cref.toNat + 3 + k.toNat := by
        rw [m7_bv64_add_toNat (by rw [hcbase]; omega), hcbase]
      have har_m_lt : (cbase + k).toNat < (fastPropMem s_disk sem).core.arena.length := by
        rw [hm_aren, hk_ar]; omega
      have har_raw_lt : cref.toNat + 3 + k.toNat < sem.core.arena.length := by
        rw [haren]; omega
      let clit := (fastPropMem s_disk sem).core.arena[(cbase + k).toNat]'har_m_lt
      have hclit_eq : clit = sem.core.arena[cref.toNat + 3 + k.toNat]'har_raw_lt := by
        dsimp only [clit]
        exact (fc_getElem_arena s_disk sem).trans
          (fc_getElem_eq_of_idx hk_ar (hk_ar ▸ har_raw_lt) har_raw_lt)
      have hclit_mem : clit.toNat ∈ fullArenaClauseLitsCore sem.core cref.toNat :=
        (mem_fullArenaClauseLitsCore_iff hbd).mpr
          ⟨k.toNat, hk_csz, congrArg BitVec.toNat hclit_eq.symm⟩
      have hclit_lt : clit.toNat < 2 * sem.core.cur_vars :=
        hpi.nw.arena.lits_lt cref.toNat hcr_ref hng clit.toNat hclit_mem
      have hk1_n : (k + 1#64).toNat = k.toNat + 1 := m7_bv64_add1_toNat (by omega)
      m7_hsteps_nogrp
      refine wp_join_group (fun (mx', ()) mj =>
          mj = m ∧ mx.toNat ≤ mx'.toNat ∧
          (clit ≠ other →
            (sem.core.lvl[clit.toNat / 2]?.getD 0#32).toNat ≤ mx'.toNat) ∧
          (mx' = mx ∨ (clit ≠ other ∧ mx' = sem.core.lvl[clit.toNat / 2]?.getD 0#32))) ?_ ?_
      · rintro _ ⟨mx', ⟨⟩⟩ mj ⟨hmj, hmx_le, hcl_le, hmx_src⟩
        rw [hmj]; clear hmj
        m7_hsteps
        refine ih _ (mx', k + 1#64, ()) m (by rw [hk1_n]; omega)
          ⟨rfl, rfl, by rw [hk1_n]; omega, fun j hj1 hj_ar hne => ?_, ?_⟩
        · rw [hk1_n] at hj1
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj1) with hj' | rfl
          · exact Nat.le_trans (hge j hj' hj_ar hne) hmx_le
          · have hne' : clit ≠ other := fun heq => by
              apply hne; rw [← hclit_eq, heq]
            have hcl_eq' : sem.core.arena[cref.toNat + 3 + k.toNat]'hj_ar = clit := hclit_eq.symm
            rw [hcl_eq']
            exact hcl_le hne'
        · rcases hmx_src with rfl | ⟨hne, rfl⟩
          · exact hatt.imp id fun ⟨j, hj, hj_ar, hne', he⟩ =>
              ⟨j, by rw [hk1_n]; omega, hj_ar, hne', he⟩
          · refine Or.inr ⟨k.toNat, by rw [hk1_n]; omega, har_raw_lt, ?_, ?_⟩
            · rw [← hclit_eq]; exact fun h => hne (BitVec.eq_of_toNat_eq h)
            · rw [hclit_eq]
      · intro Jstep hJstep
        m7_hsplit
        · have hne : clit ≠ other := hc
          have hlvl_m_lt : ((clit >>> 1#32).setWidth 64).toNat <
              (fastPropMem s_disk sem).core.lvl.length := by
            rw [hm_lvl, m7_bv32_rshift1_toNat]; omega
          have hlvl_raw_lt : clit.toNat / 2 < sem.core.lvl.length := by
            rw [hlvl_len]; omega
          let lv := (fastPropMem s_disk sem).core.lvl[
            ((clit >>> 1#32).setWidth 64).toNat]'hlvl_m_lt
          have hlv_eq : lv = sem.core.lvl[clit.toNat / 2]?.getD 0#32 := by
            dsimp only [lv]
            rw [List.getElem?_eq_getElem hlvl_raw_lt, Option.getD_some]
            exact (fc_getElem_lvl s_disk sem).trans
              (fc_getElem_eq_of_idx (m7_bv32_rshift1_toNat clit) _ hlvl_raw_lt)
          m7_hsteps
          · have hlt : mx.toNat < lv.toNat := hc
            refine hJstep (lv, ()) m ⟨rfl, Nat.le_of_lt hlt,
              fun _ => by rw [hlv_eq]; exact Nat.le_refl _,
              Or.inr ⟨hne, hlv_eq⟩⟩
          · have hle : lv.toNat ≤ mx.toNat := Nat.le_of_not_lt hc
            refine hJstep (mx, ()) m ⟨rfl, Nat.le_refl _, fun _ => by rw [← hlv_eq]; exact hle,
              Or.inl rfl⟩
        · have heq : clit = other := by
            simpa only [clit, ← BitVec.toNat_add cbase k] using hc
          m7_hsteps
          exact hJstep (mx, ()) m ⟨rfl, Nat.le_refl _, fun h => absurd heq h, Or.inl rfl⟩
    · have hk_eq : k.toNat = fullArenaClauseSizeCore sem.core cref.toNat :=
        hcsz ▸ Nat.le_antisymm hk_le (Nat.le_of_not_lt hc)
      m7_hsteps
      refine hJ mx (fun l hl hne => ?_) ?_
      · obtain ⟨j, hj, hget⟩ := (mem_fullArenaClauseLitsCore_iff hbd).mp hl
        have hj_ar : cref.toNat + 3 + j < sem.core.arena.length := by rw [haren]; omega
        have hj_eq : (sem.core.arena[cref.toNat + 3 + j]'hj_ar).toNat = l := hget
        rw [← hj_eq]
        exact hge j (hk_eq ▸ hj) hj_ar (by rw [hj_eq]; exact hne)
      · rcases hatt with rfl | ⟨j, hj, hj_ar, hne, he⟩
        · exact Or.inl rfl
        · have hj_csz : j < fullArenaClauseSizeCore sem.core cref.toNat := hk_eq ▸ hj
          exact Or.inr ⟨(sem.core.arena[cref.toNat + 3 + j]'hj_ar).toNat,
            (mem_fullArenaClauseLitsCore_iff hbd).mpr ⟨j, hj_csz, rfl⟩, hne, he⟩
  · intro L hL
    m7_hsteps
    exact hL _ (0#32, 0#64, ()) m
      ⟨rfl, rfl, Nat.zero_le _, fun _ hj => by simp at hj, Or.inl rfl⟩

/-! ## 3. Inline Replacement Push (`m7LpReplPushExpr`) -/

private theorem m7_lp_ar_swap_wp {Γ : Env} {rs : List Ty} {c : FullCfg}
    {s_disk sem1 : FullState} {not_lit other repl : BitVec 32} {cbase ri : BitVec 64}
    {cref : Nat} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    {k : Expr Val Cont rs}
    (haren1 : sem1.core.arena.length = c.arena_cap)
    (hc0 : cbase.toNat = cref + 3) (hc1 : (cbase + 1#64).toNat = cref + 4)
    (hcri : (cbase + ri).toNat = cref + 3 + ri.toNat)
    (h0_lt : cref + 3 < c.arena_cap) (h1_lt : cref + 4 < c.arena_cap)
    (hri_lt : cref + 3 + ri.toNat < c.arena_cap)
    (hm : (FullMem c (fastPropMem s_disk sem1) ⋆ R) m)
    (hk : ∀ m3,
      let ar3 := ((sem1.core.arena.set (cref + 3) other).set (cref + 4) repl).set
        (cref + 3 + ri.toNat) not_lit
      (FullMem c (fastPropMem s_disk { sem1 with core := { sem1.core with arena := ar3 } }) ⋆
        R) m3 →
      wp Γ Q X k m3) :
    wp Γ Q X
      (.let_ (Op.mk (.mul i64) (.var cbase, (.imm 4#64, ()))) fun o0 =>
       .let_ (Op.mk (.add i64) (.var c.pArena, (.var o0.1, ()))) fun a0 =>
       .store (Arg.var (t := i32) other) (.var a0.1)
         (.let_ (Op.mk (.add i64) (.var cbase, (.imm 1#64, ()))) fun i1 =>
          .let_ (Op.mk (.mul i64) (.var i1.1, (.imm 4#64, ()))) fun o1 =>
          .let_ (Op.mk (.add i64) (.var c.pArena, (.var o1.1, ()))) fun a1 =>
          .store (Arg.var (t := i32) repl) (.var a1.1)
            (.let_ (Op.mk (.add i64) (.var cbase, (.var ri, ()))) fun ir =>
             .let_ (Op.mk (.mul i64) (.var ir.1, (.imm 4#64, ()))) fun or1 =>
             .let_ (Op.mk (.add i64) (.var c.pArena, (.var or1.1, ()))) fun ar1 =>
             .store (Arg.var (t := i32) not_lit) (.var ar1.1) k))) m := by
  have hm_ar : (fastPropMem s_disk sem1).core.arena.length = c.arena_cap := by
    rw [fastPropMem_arena]; exact haren1
  m7_hsteps_nogrp
  refine wp_store_sep (FullArenaTactics.c0_store_full_arena other
    (by rw [hm_ar, hc0]; exact h0_lt) hm) ?_
  intro m1 hm1; clear hm; dsimp only at hm1
  rw [hc0, fastPropMem_with_arena, fastPropMem_arena] at hm1
  m7_hsteps_nogrp
  have hm1_ar : (fastPropMem s_disk { sem1 with core :=
      { sem1.core with arena := sem1.core.arena.set (cref + 3) other } }).core.arena.length =
      c.arena_cap := by
    rw [fastPropMem_arena, List.length_set]; exact haren1
  refine wp_store_sep (FullArenaTactics.c0_store_full_arena repl
    (by rw [hm1_ar, hc1]; exact h1_lt) hm1) ?_
  intro m2 hm2; clear hm1; dsimp only at hm2
  rw [hc1, fastPropMem_with_arena, fastPropMem_arena] at hm2
  m7_hsteps_nogrp
  let sem_ar2 : FullState := { sem1 with core :=
    { sem1.core with arena := (sem1.core.arena.set (cref + 3) other).set (cref + 4) repl } }
  have hm2_ar : (fastPropMem s_disk sem_ar2).core.arena.length = c.arena_cap := by
    rw [fastPropMem_arena, List.length_set, List.length_set]; exact haren1
  refine wp_store_sep (FullArenaTactics.c0_store_full_arena not_lit
    (by rw [hm2_ar, hcri]; exact hri_lt) hm2) ?_
  intro m3 hm3; clear hm2; dsimp only at hm3
  rw [hcri, fastPropMem_with_arena, fastPropMem_arena] at hm3
  exact hk m3 hm3

theorem m7_lp_repl_push_wp {Γ : Env} {rs : List Ty} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s_base s_disk sem1 : FullState}
    {not_lit other cref repl : BitVec 32}
    {te un uf tk' p_v q end_v p2 off_v brk0 cbase ri : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    {J_ovf : Cont [i64, i64, i64, i64, i64, i64, i64, Ty.bool, i32, i32, i32, i64]}
    {J_lp : Cont [i64, i64, i64, i64, i64, i64]}
    (hmaxv : c.max_vars < 2 * dimacsBound) (har : c.arena_cap < 2 * dimacsBound)
    (hwc : c.wcap < 2 * dimacsBound)
    (hpi1 : PropLitInv c F0 F_cur s_base sem1 not_lit.toNat off_v.toNat q.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hcr_lt : cref.toNat < 0x80000000)
    (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore sem1.core)
    (hfit : cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤ sem1.core.arena_len)
    (har3 : sem1.core.arena[cref.toNat + 3]? = some other)
    (har4 : sem1.core.arena[cref.toNat + 4]? = some not_lit)
    (hri2 : 2 ≤ ri.toNat)
    (hri_lt : ri.toNat < fullArenaClauseSizeCore sem1.core cref.toNat)
    (har_ri : sem1.core.arena[cref.toNat + 3 + ri.toNat]? = some repl)
    (hrepl_lt : repl.toNat < 2 * sem1.core.cur_vars)
    (hrepl_ne : repl.toNat ≠ not_lit.toNat)
    (hnot_lt : not_lit.toNat < 2 * sem1.core.cur_vars)
    (hoth_lt : other.toNat < 2 * sem1.core.cur_vars)
    (hcbase : cbase.toNat = cref.toNat + 3)
    (hp2_eq : p2 = p_v + 2#64) (hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2)
    (hq_le : q.toNat ≤ p_v.toNat)
    (hm : (FullMem c (fastPropMem s_disk sem1) ⋆ R) m)
    (hJ_ovf : ∀ m_o, (FullMem c (fastPropMem s_disk sem1) ⋆ R) m_o →
      wp Γ Q X (.jump J_ovf (.var te, (.var un, (.var uf, (.var tk', (.var p2, (.var q,
        (.var brk0, (.imm true, (.var repl, (.var other, (.var cref, (.var ri, ())))))))))))))
        m_o)
    (hJ_lp : ∀ (sem4 : FullState) m_l,
      PropLitInv c F0 F_cur s_base sem4 not_lit.toNat off_v.toNat q.toNat
        p2.toNat end_v.toNat →
      sem4.core.oom = sem1.core.oom →
      sem4.core.confl_type = sem1.core.confl_type →
      sem4.core.trail_end = sem1.core.trail_end →
      sem4.core.unassigned = sem1.core.unassigned →
      sem4.core.unflushed = sem1.core.unflushed →
      (FullMem c (fastPropMem s_disk sem4) ⋆ R) m_l →
      wp Γ Q X (.jump J_lp (.var te, (.var un, (.var uf, (.var tk', (.var p2, (.var q, ())))))))
        m_l) :
    wp Γ Q X (m7LpReplPushExpr c.hdr c.pWstk c.pArena not_lit other cref te un uf tk' p2 q
      brk0 cbase ri repl J_ovf J_lp) m := by
  unfold dimacsBound at hmaxv har hwc
  have hcv := hpi1.len.core_ok.cur_vars_le
  have haren1 := hpi1.len.core_ok.arena_len_arr
  have halen1 := hpi1.len.core_ok.arena_len_le
  have hwvec1 := hpi1.len.core_ok.wvec_len
  have hwstk1 := hpi1.len.core_ok.wstk_len_arr
  have hwlen1 := hpi1.len.core_ok.wlen_le
  have hcap64 : c.arena_cap < 2 ^ 64 := Nat.lt_trans har (by decide)
  have hwc64 : c.wcap < 2 ^ 64 := Nat.lt_trans hwc (by decide)
  have hfit_cap : cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤ c.arena_cap :=
    Nat.le_trans hfit halen1
  have hcbase1 : (cbase + 1#64).toNat = cref.toNat + 4 := by
    rw [m7_bv64_add1_toNat (by rw [hcbase]; omega), hcbase]
  have hcbri : (cbase + ri).toNat = cref.toNat + 3 + ri.toNat := by
    rw [m7_bv64_add_toNat (by rw [hcbase]; omega), hcbase]
  have h0_lt : cref.toNat + 3 < c.arena_cap := by omega
  have h1_lt : cref.toNat + 4 < c.arena_cap := by omega
  have hri_lt_cap : cref.toNat + 3 + ri.toNat < c.arena_cap := by omega
  have hp2_n : p2.toNat = p_v.toNat + 2 := by
    have : p2 = p_v + 1#64 + 1#64 := by rw [hp2_eq, BitVec.add_assoc]; rfl
    rw [this, hp2_nat]
  have hswap := m7_swapCl_step hpi1 hcr_ref hfit har3 har4 hri2 hri_lt har_ri
  let ar3 := ((sem1.core.arena.set (cref.toNat + 3) other).set (cref.toNat + 4) repl).set
    (cref.toNat + 3 + ri.toNat) not_lit
  let st3 : FullState := { sem1 with core := { sem1.core with arena := ar3 } }
  have hswap_st3 : st3.core = { sem1.core with arena := st3.core.arena } ∧
      st3.scratch = sem1.scratch ∧ st3.LengthsOk c ∧
      FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st3.core) ∧
      SplitWatchesInv F_cur st3.core not_lit.toNat off_v.toNat q.toNat
        (p_v.toNat + 2) end_v.toNat ∧
      FullPropDecSpecs.FullArenaPermEq sem1.core st3.core ∧
      cref.toNat ∈ fullArenaClauseRefsCore st3.core := hswap
  have hcr_ref3 : cref.toNat ∈ fullArenaClauseRefsCore st3.core := hswap_st3.2.2.2.2.2.2
  have hlen3 : st3.LengthsOk c := hswap_st3.2.2.1
  have hnw3 := hswap_st3.2.2.2.1
  have hsw3 := hswap_st3.2.2.2.2.1
  have hperm13 := hswap_st3.2.2.2.2.2.1
  have haren3 : st3.core.arena.length = c.arena_cap := hlen3.core_ok.arena_len_arr
  have hwvec3 : st3.core.wvec.length = 4 * c.max_vars := hlen3.core_ok.wvec_len
  have hwstk3 : st3.core.wstk.length = c.wcap := hlen3.core_ok.wstk_len_arr
  have hoth_mask : other &&& 0x7FFFFFFF#32 = other := m7_bv32_mask7f_eq (by omega)
  let P_ok (mo : Mem 64) : Prop := ∃ sem4 : FullState,
    PropLitInv c F0 F_cur s_base sem4 not_lit.toNat off_v.toNat q.toNat
      p2.toNat end_v.toNat ∧
    sem4.core.oom = sem1.core.oom ∧ sem4.core.confl_type = sem1.core.confl_type ∧
    sem4.core.trail_end = sem1.core.trail_end ∧
    sem4.core.unassigned = sem1.core.unassigned ∧
    sem4.core.unflushed = sem1.core.unflushed ∧
    (FullMem c (fastPropMem s_disk sem4) ⋆ R) mo
  unfold m7LpReplPushExpr
  refine wp_join_group (fun x mj => x.1 = q ∧ P_ok mj) ?_ ?_
  · rintro _ ⟨q_out, _⟩ mj ⟨hq_eq, sem4, hpi4, hoom4, hct4, hte4, hun4, huf4, hmj⟩
    dsimp only at hq_eq
    rw [hq_eq]
    exact hJ_lp sem4 mj hpi4 hoom4 hct4 hte4 hun4 huf4 hmj
  · intro Jret hJret
    m7_hsplit
    · exact absurd (congrArg BitVec.toNat hc) hrepl_ne
    · have hm_wvec1 : (fastPropMem s_disk sem1).core.wvec.length = 4 * c.max_vars := by
        rw [fastPropMem_wvec]; exact hwvec1
      have hm_wstk1 : (fastPropMem s_disk sem1).core.wstk.length = c.wcap := by
        rw [fastPropMem_wstk]; exact hwstk1
      have hridx0 : (repl.setWidth 64 <<< (1 : Nat)).toNat = 2 * repl.toNat :=
        m7_bv64_shl1_u32_nat repl
      have hridx1 : ((repl.setWidth 64 <<< (1 : Nat)) + 1).toNat = 2 * repl.toNat + 1 :=
        m7_bv64_shl1_add1_nat repl
      have hridx0_lt : (repl.setWidth 64 <<< (1 : Nat)).toNat <
          (fastPropMem s_disk sem1).core.wvec.length := by
        rw [hm_wvec1, hridx0]; omega
      have hridx1_lt : ((repl.setWidth 64 <<< (1 : Nat)) + 1).toNat <
          (fastPropMem s_disk sem1).core.wvec.length := by
        rw [hm_wvec1, hridx1]; omega
      m7_hsteps_nogrp
      let off32 := (fastPropMem s_disk sem1).core.wvec[
        (repl.setWidth 64 <<< (1 : Nat)).toNat]'hridx0_lt
      let len32 := (fastPropMem s_disk sem1).core.wvec[
        ((repl.setWidth 64 <<< (1 : Nat)) + 1).toNat]'hridx1_lt
      have hoff_eq : (off32.setWidth 64).toNat = fullWatchOffCore sem1.core repl.toNat := by
        unfold fullWatchOffCore; rw [bv_c0_zext32_64]
        have hr0_raw : 2 * repl.toNat < sem1.core.wvec.length := by rw [hwvec1]; omega
        rw [List.getElem?_eq_getElem hr0_raw, Option.getD_some]
        exact congrArg BitVec.toNat
          ((fc_getElem_eq_of_idx hridx0 hridx0_lt
            (by rw [hm_wvec1, ← hwvec1]; exact hr0_raw)).trans (fc_getElem_wvec s_disk sem1))
      have hlen_eq : (len32.setWidth 64).toNat = fullWatchSizeCore sem1.core repl.toNat := by
        unfold fullWatchSizeCore; rw [bv_c0_zext32_64]
        have hr1_raw : 2 * repl.toNat + 1 < sem1.core.wvec.length := by rw [hwvec1]; omega
        rw [List.getElem?_eq_getElem hr1_raw, Option.getD_some]
        exact congrArg BitVec.toNat
          ((fc_getElem_eq_of_idx hridx1 hridx1_lt
            (by rw [hm_wvec1, ← hwvec1]; exact hr1_raw)).trans (fc_getElem_wvec s_disk sem1))
      have hwv0_eq :
          ((fastPropMem s_disk sem1).core.wvec[2 * repl.toNat % 2 ^ 64]'(by
            rw [hm_wvec1, Nat.mod_eq_of_lt (by omega)]; omega)).toNat =
          fullWatchOffCore sem1.core repl.toNat := by
        have hlt64 : 2 * repl.toNat < 2 ^ 64 := by omega
        have hidx0 : (repl.setWidth 64 <<< (1 : Nat)).toNat = 2 * repl.toNat % 2 ^ 64 := by
          rw [hridx0, Nat.mod_eq_of_lt hlt64]
        have heq := fc_getElem_eq_of_idx hidx0 hridx0_lt
          (by rw [hm_wvec1, Nat.mod_eq_of_lt hlt64]; omega)
        dsimp only [off32] at hoff_eq
        rw [bv_c0_zext32_64] at hoff_eq
        exact (congrArg BitVec.toNat heq).symm.trans hoff_eq
      have hwv1_eq :
          ((fastPropMem s_disk sem1).core.wvec[
            (2 * repl.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'(by
              rw [hm_wvec1, show (1 : BitVec 64).toNat = 1 from rfl,
                Nat.mod_eq_of_lt (by omega)]; omega)).toNat =
          fullWatchSizeCore sem1.core repl.toNat := by
        have hlt64 : 2 * repl.toNat + 1 < 2 ^ 64 := by omega
        have hidx1 : ((repl.setWidth 64 <<< (1 : Nat)) + 1).toNat =
            (2 * repl.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 := by
          rw [hridx1, show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt hlt64]
        have heq := fc_getElem_eq_of_idx hidx1 hridx1_lt
          (by rw [hm_wvec1, show (1 : BitVec 64).toNat = 1 from rfl,
                Nat.mod_eq_of_lt hlt64]; omega)
        dsimp only [len32] at hlen_eq
        rw [bv_c0_zext32_64] at hlen_eq
        exact (congrArg BitVec.toNat heq).symm.trans hlen_eq
      have hbd_r := hpi1.sw.layout.bounds repl.toNat hrepl_lt
      have hrsz3 : fullWatchSizeCore st3.core repl.toNat =
          fullWatchSizeCore sem1.core repl.toNat := rfl
      have hroff3 : fullWatchOffCore st3.core repl.toNat =
          fullWatchOffCore sem1.core repl.toNat := rfl
      have hnot_st3 : not_lit.toNat < 2 * st3.core.cur_vars := hnot_lt
      have hrepl_st3 : repl.toNat < 2 * st3.core.cur_vars := hrepl_lt
      refine wp_join_group (fun _ m1 => P_ok m1) ?_ ?_
      · rintro _ ⟨ovf1, rw1, oth1, cr1, ri1, ⟨⟩⟩ m1 hok
        m7_hsteps
        exact hJret (q, ovf1, rw1, oth1, cr1, ri1, ()) m1 ⟨rfl, hok⟩
      · intro Je1 hJe1
        refine wp_join_group (fun _ m2 => m2 = m) ?_ ?_
        · rintro _ ⟨⟩ m2 hm2; rw [hm2]; clear hm2
          refine wp_join_group (fun _ m3 => P_ok m3) ?_ ?_
          · rintro _ ⟨ovf3, rw3, oth3, cr3, ri3, ⟨⟩⟩ m3 hok
            m7_hsteps
            exact hJe1 (ovf3, rw3, oth3, cr3, ri3, ()) m3 hok
          · intro Je3 hJe3
            refine wp_join_group (fun _ ms => ms = m) ?_ ?_
            · rintro _ ⟨⟩ ms hms; rw [hms]; clear hms
              m7_hsplit
              · have hlen_pos : 0 < fullWatchSizeCore st3.core repl.toNat := by
                  rw [hrsz3, ← hwv1_eq]; exact hc
                m7_hsplit
                · have hpe0_n : (off32.setWidth 64 + len32.setWidth 64).toNat =
                      fullWatchOffCore st3.core repl.toNat +
                        fullWatchSizeCore st3.core repl.toNat := by
                    rw [m7_bv64_add_toNat (by rw [hoff_eq, hlen_eq]; omega), hoff_eq, hlen_eq,
                      hroff3, hrsz3]
                  have hwlen2_sem : fullWatchOffCore sem1.core repl.toNat +
                      fullWatchSizeCore sem1.core repl.toNat + 2 ≤ sem1.core.wlen := by
                    have hc' := hc
                    rw [fastPropMem_wlen, hwv0_eq, hwv1_eq,
                      show (2 : BitVec 64).toNat = 2 from rfl] at hc'
                    have hlt64 : fullWatchOffCore sem1.core repl.toNat +
                        fullWatchSizeCore sem1.core repl.toNat + 2 < 2 ^ 64 := by omega
                    have hwlen64 : sem1.core.wlen < 2 ^ 64 := by omega
                    rwa [Nat.mod_eq_of_lt hlt64, Nat.mod_eq_of_lt hwlen64] at hc'
                  have hwlen2_le : fullWatchOffCore st3.core repl.toNat +
                      fullWatchSizeCore st3.core repl.toNat + 2 ≤ st3.core.wlen :=
                    hwlen2_sem
                  have hpe1_n : (off32.setWidth 64 + len32.setWidth 64 + 1).toNat =
                      fullWatchOffCore st3.core repl.toNat +
                        fullWatchSizeCore st3.core repl.toNat + 1 := by
                    rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl, hpe0_n,
                      hroff3, hrsz3, Nat.mod_eq_of_lt (by omega)]
                  have hpe0_lt : (off32.setWidth 64 + len32.setWidth 64).toNat <
                      (fastPropMem s_disk sem1).core.wstk.length := by
                    rw [hm_wstk1, hpe0_n, hroff3, hrsz3]
                    exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans hwlen2_sem hwlen1)
                  m7_hsteps_nogrp
                  · have hidx0_ws : fullWatchOffCore st3.core repl.toNat +
                        fullWatchSizeCore st3.core repl.toNat < sem1.core.wstk.length := by
                      rw [hwstk1, hroff3, hrsz3]
                      exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans hwlen2_sem hwlen1)
                    have hsent0 : st3.core.wstk[fullWatchOffCore st3.core repl.toNat +
                        fullWatchSizeCore st3.core repl.toNat]? = some 0xFFFFFFFF#32 := by
                      rw [List.getElem?_eq_getElem hidx0_ws]
                      have hmod : fullWatchOffCore sem1.core repl.toNat +
                          fullWatchSizeCore sem1.core repl.toNat < 2 ^ 64 := by omega
                      have hidx0_eq : fullWatchOffCore st3.core repl.toNat +
                          fullWatchSizeCore st3.core repl.toNat =
                          (((fastPropMem s_disk sem1).core.wvec[2 * repl.toNat % 2 ^ 64]'(by
                              rw [hm_wvec1, Nat.mod_eq_of_lt (by omega)]; omega)).toNat +
                            ((fastPropMem s_disk sem1).core.wvec[
                              (2 * repl.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'(by
                                rw [hm_wvec1, show (1 : BitVec 64).toNat = 1 from rfl,
                                  Nat.mod_eq_of_lt (by omega)]; omega)).toNat) %
                            2 ^ 64 := by
                        rw [hwv0_eq, hwv1_eq, hroff3, hrsz3, Nat.mod_eq_of_lt hmod]
                      have hc_pe0 : (fastPropMem s_disk sem1).core.wstk[
                          (((fastPropMem s_disk sem1).core.wvec[2 * repl.toNat % 2 ^ 64]'(by
                              rw [hm_wvec1, Nat.mod_eq_of_lt (by omega)]; omega)).toNat +
                            ((fastPropMem s_disk sem1).core.wvec[
                              (2 * repl.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'(by
                                rw [hm_wvec1, show (1 : BitVec 64).toNat = 1 from rfl,
                                  Nat.mod_eq_of_lt (by omega)]; omega)).toNat) % 2 ^ 64]'(by
                            rw [hm_wstk1, hwv0_eq, hwv1_eq, Nat.mod_eq_of_lt hmod]
                            exact Nat.lt_of_lt_of_le (by omega)
                              (Nat.le_trans hwlen2_sem hwlen1)) = 0xFFFFFFFF#32 := by
                        assumption
                      have hmem0 : (fastPropMem s_disk sem1).core.wstk[
                          fullWatchOffCore st3.core repl.toNat +
                            fullWatchSizeCore st3.core repl.toNat]'(by
                              rw [fastPropMem_wstk]; exact hidx0_ws) = 0xFFFFFFFF#32 :=
                        (fc_getElem_eq_of_idx hidx0_eq _ _).trans hc_pe0
                      rw [fc_getElem_wstk] at hmem0
                      exact congrArg some hmem0
                    have hidx1_ws : fullWatchOffCore st3.core repl.toNat +
                        fullWatchSizeCore st3.core repl.toNat + 1 < sem1.core.wstk.length := by
                      rw [hwstk1, hroff3, hrsz3]
                      exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans hwlen2_sem hwlen1)
                    have hsent1 : st3.core.wstk[fullWatchOffCore st3.core repl.toNat +
                        fullWatchSizeCore st3.core repl.toNat + 1]? = some 0xFFFFFFFF#32 := by
                      rw [List.getElem?_eq_getElem hidx1_ws]
                      have hmod1 : fullWatchOffCore sem1.core repl.toNat +
                          fullWatchSizeCore sem1.core repl.toNat + 1 < 2 ^ 64 := by omega
                      have hidx1_eq : fullWatchOffCore st3.core repl.toNat +
                          fullWatchSizeCore st3.core repl.toNat + 1 =
                          (((fastPropMem s_disk sem1).core.wvec[2 * repl.toNat % 2 ^ 64]'(by
                              rw [hm_wvec1, Nat.mod_eq_of_lt (by omega)]; omega)).toNat +
                            ((fastPropMem s_disk sem1).core.wvec[
                              (2 * repl.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'(by
                                rw [hm_wvec1, show (1 : BitVec 64).toNat = 1 from rfl,
                                  Nat.mod_eq_of_lt (by omega)]; omega)).toNat +
                            (1 : BitVec 64).toNat) % 2 ^ 64 := by
                        rw [hwv0_eq, hwv1_eq, hroff3, hrsz3,
                          show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt hmod1]
                      have hmem1 : (fastPropMem s_disk sem1).core.wstk[
                          fullWatchOffCore st3.core repl.toNat +
                            fullWatchSizeCore st3.core repl.toNat + 1]'(by
                              rw [fastPropMem_wstk]; exact hidx1_ws) = 0xFFFFFFFF#32 :=
                        (fc_getElem_eq_of_idx hidx1_eq _ _).trans hc
                      rw [fc_getElem_wstk] at hmem1
                      exact congrArg some hmem1
                    dsimp only [off32, len32] at hpe0_n hpe1_n
                    refine m7_lp_ar_swap_wp haren1 hcbase hcbase1 hcbri h0_lt h1_lt
                      hri_lt_cap hm fun m3 hm3 => ?_
                    have hm3_ws : (fastPropMem s_disk st3).core.wstk.length = c.wcap := by
                      rw [fastPropMem_wstk]; exact hwstk3
                    m7_hsteps_nogrp
                    refine wp_store_sep (FullArenaTactics.c0_store_full_wstk other
                      (by rw [hm3_ws, hpe0_n, hroff3, hrsz3]
                          exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans hwlen2_sem hwlen1))
                      hm3) ?_
                    intro mw0 hmw0; clear hm3
                    rw [hpe0_n, fastPropMem_with_wstk] at hmw0
                    m7_hsteps_nogrp
                    refine wp_store_sep (FullArenaTactics.c0_store_full_wstk cref
                      (by rw [fastPropMem_wstk, List.length_set, fastPropMem_wstk,
                            hwstk1, hpe1_n, hroff3, hrsz3]
                          exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans hwlen2_sem hwlen1))
                      hmw0) ?_
                    intro mw1 hmw1; clear hmw0
                    rw [hpe1_n, fastPropMem_with_wstk] at hmw1
                    have hsz2_32 : (len32.setWidth 64 + 2#64).setWidth 32 =
                        BitVec.ofNat 32 (fullWatchSizeCore st3.core repl.toNat + 2) := by
                      apply BitVec.eq_of_toNat_eq
                      rw [BitVec.toNat_setWidth, m7_bv64_add2_toNat (by rw [hlen_eq]; omega),
                        hlen_eq, hrsz3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                    m7_hsteps_nogrp
                    refine wp_store_sep (FullArenaTactics.c0_store_full_wvec
                      ((len32.setWidth 64 + 2#64).setWidth 32)
                      (by rw [fastPropMem_wvec, hwvec1, hridx1]; omega) hmw1) ?_
                    intro mwv hmwv; clear hmw1
                    rw [hridx1, m7_fpm_with_wvec, fastPropMem_wvec, hsz2_32] at hmwv
                    m7_hsteps
                    · let wu' := sem1.core.wusable - 2#64
                      have hpi4 := m7_repl_sentinel_step (other := other) (wu' := wu') hpi1
                        hswap_st3.1 hswap_st3.2.1 hlen3 hnw3 hsw3 hperm13 hcr_lt hcr_ref3 hrepl_st3
                        hrepl_ne hnot_st3 hlen_pos hwlen2_le hsent0 hsent1 hpe0_n hp2_nat
                      rw [show (p_v + 1#64 + 1#64).toNat = p2.toNat from
                        hp2_nat.trans hp2_n.symm] at hpi4
                      have hhm : (FullMem c (fastPropMem s_disk { st3 with core :=
                          { st3.core with
                            wstk := (st3.core.wstk.set
                              (fullWatchOffCore st3.core repl.toNat +
                                fullWatchSizeCore st3.core repl.toNat) other).set
                              (fullWatchOffCore st3.core repl.toNat +
                                fullWatchSizeCore st3.core repl.toNat + 1) cref
                            wvec := st3.core.wvec.set (2 * repl.toNat + 1)
                              (BitVec.ofNat 32 (fullWatchSizeCore st3.core repl.toNat + 2))
                            wusable := wu' } }) ⋆ R) m := by
                        refine Eq.mp (congrArg (fun k => (FullMem c k ⋆ R) m) ?_) hm
                        unfold fastPropMem; rfl
                      exact hJe3 (false, 0#32, 0#32, 0#32, 0#64, ()) m
                        ⟨_, hpi4, rfl, rfl, rfl, rfl, rfl, by
                          rw [hpe0_n]
                          exact Eq.mp (congrArg (fun x => (FullMem c (fastPropMem s_disk
                            { st3 with core :=
                              { st3.core with
                                wstk := (st3.core.wstk.set
                                  (fullWatchOffCore st3.core repl.toNat +
                                    fullWatchSizeCore st3.core repl.toNat) x).set
                                  (fullWatchOffCore st3.core repl.toNat +
                                    fullWatchSizeCore st3.core repl.toNat + 1) cref
                                wvec := st3.core.wvec.set (2 * repl.toNat + 1)
                                  (BitVec.ofNat 32 (fullWatchSizeCore st3.core repl.toNat + 2))
                                wusable := wu' } }) ⋆ R) m) hoth_mask.symm) hhm⟩
                    · have hpi4 := m7_repl_sentinel_step (other := other) (wu' := st3.core.wusable)
                        hpi1 hswap_st3.1 hswap_st3.2.1 hlen3 hnw3 hsw3 hperm13 hcr_lt hcr_ref3
                        hrepl_st3 hrepl_ne hnot_st3 hlen_pos hwlen2_le hsent0 hsent1 hpe0_n
                        hp2_nat
                      rw [show (p_v + 1#64 + 1#64).toNat = p2.toNat from
                        hp2_nat.trans hp2_n.symm] at hpi4
                      have hhm : (FullMem c (fastPropMem s_disk { st3 with core :=
                          { st3.core with
                            wstk := (st3.core.wstk.set
                              (fullWatchOffCore st3.core repl.toNat +
                                fullWatchSizeCore st3.core repl.toNat) other).set
                              (fullWatchOffCore st3.core repl.toNat +
                                fullWatchSizeCore st3.core repl.toNat + 1) cref
                            wvec := st3.core.wvec.set (2 * repl.toNat + 1)
                              (BitVec.ofNat 32 (fullWatchSizeCore st3.core repl.toNat + 2))
                            wusable := st3.core.wusable } }) ⋆ R) mwv := by
                        refine Eq.mp (congrArg (fun k => (FullMem c k ⋆ R) mwv) ?_) hmwv
                        unfold fastPropMem; rfl
                      exact hJe3 (false, 0#32, 0#32, 0#32, 0#64, ()) mwv
                        ⟨_, hpi4, rfl, rfl, rfl, rfl, rfl, by
                          rw [hpe0_n]
                          exact Eq.mp (congrArg (fun x => (FullMem c (fastPropMem s_disk
                            { st3 with core :=
                              { st3.core with
                                wstk := (st3.core.wstk.set
                                  (fullWatchOffCore st3.core repl.toNat +
                                    fullWatchSizeCore st3.core repl.toNat) x).set
                                  (fullWatchOffCore st3.core repl.toNat +
                                    fullWatchSizeCore st3.core repl.toNat + 1) cref
                                wvec := st3.core.wvec.set (2 * repl.toNat + 1)
                                  (BitVec.ofNat 32 (fullWatchSizeCore st3.core repl.toNat + 2))
                                wusable := st3.core.wusable } }) ⋆ R) mwv)
                            hoth_mask.symm) hhm⟩
                  · exact hJ_ovf m hm
                  · exact hJ_ovf m hm
                · exact hJ_ovf m hm
              · exact hJ_ovf m hm
            · intro Jsnt hJsnt
              m7_hsplit
              · have hlen_pos : 0 < fullWatchSizeCore st3.core repl.toNat := by
                  rw [hrsz3, ← hwv1_eq]; exact hc
                m7_hsplit
                · have hend_wl : fullWatchOffCore st3.core repl.toNat +
                      fullWatchSizeCore st3.core repl.toNat = st3.core.wlen := by
                    have hc' := congrArg BitVec.toNat hc
                    simp only [BitVec.toNat_add, bv_c0_zext32_64, hwv0_eq, hwv1_eq,
                      fastPropMem_wlen, BitVec.toNat_ofNat] at hc'
                    have hlt64 : fullWatchOffCore sem1.core repl.toNat +
                        fullWatchSizeCore sem1.core repl.toNat < 2 ^ 64 := by omega
                    have hwlen64 : sem1.core.wlen < 2 ^ 64 := by omega
                    rwa [Nat.mod_eq_of_lt hlt64, Nat.mod_eq_of_lt hwlen64] at hc'
                  m7_hsplit
                  · have hfit2 : st3.core.wlen + 2 ≤ c.wcap := by
                      have hc' := hc
                      rw [fastPropMem_wlen] at hc'
                      have : sem1.core.wlen + 2 < 2 ^ 64 := by omega
                      simpa only [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt hwc64,
                        show (2 : BitVec 64).toNat = 2 from rfl, st3] using hc'
                    have hwl_st3 : st3.core.wlen = sem1.core.wlen := rfl
                    have hwl_m : (fastPropMem s_disk sem1).core.wlen = sem1.core.wlen :=
                      fastPropMem_wlen _ _
                    refine m7_lp_ar_swap_wp haren1 hcbase hcbase1 hcbri h0_lt h1_lt
                      hri_lt_cap hm fun m3 hm3 => ?_
                    m7_hsteps_nogrp
                    refine wp_store_sep (FullArenaTactics.c0_store_full_wstk other
                      (by rw [fastPropMem_wstk, hwl_m, hwstk3, m7_bv64_ofNat_toNat_lt (by omega)]
                          rw [hwl_st3] at hfit2; omega)
                      hm3) ?_
                    intro mw0 hmw0; clear hm3
                    rw [fastPropMem_with_wstk] at hmw0
                    m7_hsteps_nogrp
                    refine wp_store_sep (FullArenaTactics.c0_store_full_wstk cref
                      (by rw [fastPropMem_wstk, List.length_set, fastPropMem_wstk, hwl_m,
                            hwstk3, BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl,
                            m7_bv64_ofNat_toNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                          rw [hwl_st3] at hfit2; omega) hmw0) ?_
                    intro mw1 hmw1; clear hmw0
                    rw [fastPropMem_with_wstk] at hmw1
                    have hsz2_32 : (len32.setWidth 64 + 2#64).setWidth 32 =
                        BitVec.ofNat 32 (fullWatchSizeCore st3.core repl.toNat + 2) := by
                      apply BitVec.eq_of_toNat_eq
                      simp only [BitVec.toNat_setWidth, m7_bv64_add2_toNat (by rw [hlen_eq]; omega),
                        hlen_eq, hrsz3, BitVec.toNat_ofNat]
                    let ws3 := (st3.core.wstk.set st3.core.wlen other).set
                      (st3.core.wlen + 1) cref
                    have hr1_st3 : ((repl.setWidth 64 <<< (1 : Nat)) + 1).toNat <
                        (fastPropMem s_disk { st3 with core :=
                          { st3.core with wstk := ws3 } }).core.wvec.length := by
                      rw [fastPropMem_wvec, hwvec3, hridx1]; omega
                    m7_hsteps
                    refine wp_store_sep (FullArenaTactics.c0_store_full_wvec
                      ((len32.setWidth 64 + 2).setWidth 32)
                      (by rw [fastPropMem_wvec, hwvec1, hridx1]; omega) hm) ?_
                    intro mwv hmwv; clear hm
                    have hsz2' : (len32.setWidth 64 + 2).setWidth 32 =
                        BitVec.ofNat 32 (fullWatchSizeCore st3.core repl.toNat + 2) := hsz2_32
                    have hpi4 := m7_repl_end_step (other := other)
                      (rwend_v := BitVec.ofNat 64 st3.core.wlen) hpi1 hswap_st3.1 hswap_st3.2.1
                      hlen3 hnw3 hsw3 hperm13 hcr_lt hcr_ref3 hrepl_st3 hrepl_ne hnot_st3 hlen_pos
                      hend_wl hfit2
                      (by rw [m7_bv64_ofNat_toNat_lt (by omega)]; exact hend_wl.symm) hp2_nat
                    rw [show (p_v + 1#64 + 1#64).toNat = p2.toNat from
                      hp2_nat.trans hp2_n.symm] at hpi4
                    let ws3p := (st3.core.wstk.set st3.core.wlen other).set
                      (st3.core.wlen + 1) cref
                    have hmwv' : (FullMem c (fastPropMem s_disk { st3 with core :=
                        { st3.core with
                          wstk := ws3p
                          wvec := st3.core.wvec.set (2 * repl.toNat + 1)
                            (BitVec.ofNat 32 (fullWatchSizeCore st3.core repl.toNat + 2))
                          wlen := st3.core.wlen + 2 } }) ⋆ R) mwv := by
                      refine Eq.mp (congrArg (fun k => (FullMem c k ⋆ R) mwv) ?_) hmwv
                      unfold fastPropMem; dsimp only [ws3p]
                      have hwl_lt64 : sem1.core.wlen + 2 < 2 ^ 64 := by rw [← hwl_st3]; omega
                      simp only [hridx1, hsz2', BitVec.toNat_add,
                        show (1 : BitVec 64).toNat = 1 from rfl,
                        show (2 : BitVec 64).toNat = 2 from rfl,
                        m7_bv64_ofNat_toNat_lt
                          (Nat.lt_of_le_of_lt (Nat.le_add_right _ 2) hwl_lt64),
                        Nat.mod_eq_of_lt (by omega : sem1.core.wlen + 1 < 2 ^ 64),
                        Nat.mod_eq_of_lt hwl_lt64]
                      rfl
                    exact hJe3 (false, 0#32, 0#32, 0#32, 0#64, ()) mwv
                      ⟨_, hpi4, rfl, rfl, rfl, rfl, rfl, by
                        rw [m7_bv64_ofNat_toNat_lt (by omega)]
                        exact Eq.mp (congrArg (fun x => (FullMem c (fastPropMem s_disk
                          { st3 with core :=
                            { st3.core with
                              wstk := (st3.core.wstk.set st3.core.wlen x).set
                                (st3.core.wlen + 1) cref
                              wvec := st3.core.wvec.set (2 * repl.toNat + 1)
                                (BitVec.ofNat 32 (fullWatchSizeCore st3.core repl.toNat + 2))
                              wlen := st3.core.wlen + 2 } }) ⋆ R) mwv) hoth_mask.symm)
                          (by simpa only [st3] using hmwv')⟩
                  · exact hJsnt () m rfl
                · exact hJsnt () m rfl
              · exact hJsnt () m rfl
        · intro Je2 hJe2
          m7_hsplit
          · have hlen0 : fullWatchSizeCore st3.core repl.toNat = 0 := by
              have hc0 : ((fastPropMem s_disk sem1).core.wvec[
                  (2 * repl.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'(by
                    rw [hm_wvec1, show (1 : BitVec 64).toNat = 1 from rfl,
                      Nat.mod_eq_of_lt (by omega)]; omega)).toNat = 0 := by
                have h := congrArg BitVec.toNat hc
                rwa [bv_c0_zext32_64, show (0 : BitVec 64).toNat = 0 from rfl] at h
              rw [hrsz3, ← hwv1_eq]; exact hc0
            m7_hsplit
            · have hfit2 : st3.core.wlen + 2 ≤ c.wcap := by
                have hc' := hc
                rw [fastPropMem_wlen, show (2 : BitVec 64).toNat = 2 from rfl] at hc'
                have : sem1.core.wlen + 2 < 2 ^ 64 := by omega
                rwa [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt hwc64] at hc'
              have hwl_st3 : st3.core.wlen = sem1.core.wlen := rfl
              have hfit2_sem : sem1.core.wlen + 2 ≤ c.wcap := hfit2
              have hwl_m : (fastPropMem s_disk sem1).core.wlen = sem1.core.wlen :=
                fastPropMem_wlen _ _
              refine m7_lp_ar_swap_wp haren1 hcbase hcbase1 hcbri h0_lt h1_lt
                hri_lt_cap hm fun m3 hm3 => ?_
              m7_hsteps_nogrp
              refine wp_store_sep (FullArenaTactics.c0_store_full_wvec
                ((BitVec.ofNat 64 (fastPropMem s_disk sem1).core.wlen).setWidth 32)
                (by change (repl.setWidth 64 <<< (1 : Nat)).toNat < _
                    rw [fastPropMem_wvec, hwvec3, hridx0]; omega) hm3) ?_
              intro mwv0 hmwv0; clear hm3
              rw [hridx0, m7_fpm_with_wvec, fastPropMem_wlen, fastPropMem_wvec] at hmwv0
              m7_hsteps_nogrp
              refine wp_store_sep (FullArenaTactics.c0_store_full_wvec 2#32
                (by rw [fastPropMem_wvec, List.length_set, hwvec3, hridx1]; omega)
                hmwv0) ?_
              intro mwv1 hmwv1; clear hmwv0
              rw [hridx1, m7_fpm_with_wvec, fastPropMem_wvec] at hmwv1
              m7_hsteps_nogrp
              refine wp_store_sep (FullArenaTactics.c0_store_full_wstk other
                (by rw [fastPropMem_wstk, hwl_m, hwstk1, m7_bv64_ofNat_toNat_lt (by omega)]
                    omega) hmwv1) ?_
              intro mws0 hmws0; clear hmwv1
              rw [fastPropMem_with_wstk] at hmws0
              m7_hsteps_nogrp
              refine wp_store_sep (FullArenaTactics.c0_store_full_wstk cref
                (by rw [fastPropMem_wstk, List.length_set, fastPropMem_wstk, hwl_m,
                      hwstk1, BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl,
                      m7_bv64_ofNat_toNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                    omega) hmws0) ?_
              intro mws1 hmws1; clear hmws0
              have hwl32 : (BitVec.ofNat 64 sem1.core.wlen).setWidth 32 =
                  BitVec.ofNat 32 st3.core.wlen := by
                apply BitVec.eq_of_toNat_eq
                rw [BitVec.toNat_setWidth, m7_bv64_ofNat_toNat_lt (by omega),
                  m7_bv32_ofNat_toNat_lt (by omega), hwl_st3, Nat.mod_eq_of_lt (by omega)]
              simp only [fastPropMem_with_wstk, hwl_m, BitVec.toNat_add,
                show (1 : BitVec 64).toNat = 1 from rfl, hwl32] at hmws1
              m7_hsteps
              have hpi4 := m7_repl_empty_step (_sem := sem1) (other := other) hpi1 hswap_st3.1
                hswap_st3.2.1 hlen3 hnw3 hsw3 hperm13 hcr_lt hcr_ref3 hrepl_st3 hrepl_ne hnot_st3
                hlen0 hfit2 hq_le hp2_nat
              rw [show (p_v + 1#64 + 1#64).toNat = p2.toNat from
                hp2_nat.trans hp2_n.symm] at hpi4
              have hmws1' : (FullMem c (fastPropMem s_disk { st3 with core :=
                  { st3.core with
                    wvec := (st3.core.wvec.set (2 * repl.toNat)
                      (BitVec.ofNat 32 st3.core.wlen)).set (2 * repl.toNat + 1) 2#32
                    wstk := (st3.core.wstk.set st3.core.wlen other).set
                      (st3.core.wlen + 1) cref
                    wlen := st3.core.wlen + 2 } }) ⋆ R) m := by
                have hwl_lt64 : sem1.core.wlen + 2 < 2 ^ 64 := by rw [← hwl_st3]; omega
                refine Eq.mp (congrArg (fun k => (FullMem c k ⋆ R) m) ?_) hm
                unfold fastPropMem; dsimp only
                simp only [BitVec.toNat_add, show (2 : BitVec 64).toNat = 2 from rfl,
                  m7_bv64_ofNat_toNat_lt (Nat.lt_of_le_of_lt (Nat.le_add_right _ 2) hwl_lt64),
                  Nat.mod_eq_of_lt (by omega : sem1.core.wlen + 1 < 2 ^ 64),
                  Nat.mod_eq_of_lt hwl_lt64]
                rfl
              exact hJe1 (false, 0#32, 0#32, 0#32, 0#64, ()) m
                ⟨_, hpi4, rfl, rfl, rfl, rfl, rfl, by
                  exact Eq.mp (congrArg (fun x => (FullMem c (fastPropMem s_disk
                    { st3 with core :=
                      { st3.core with
                        wvec := (st3.core.wvec.set (2 * repl.toNat)
                          (BitVec.ofNat 32 st3.core.wlen)).set (2 * repl.toNat + 1) 2#32
                        wstk := (st3.core.wstk.set st3.core.wlen x).set
                          (st3.core.wlen + 1) cref
                        wlen := st3.core.wlen + 2 } }) ⋆ R) m) hoth_mask.symm) hmws1'⟩
            · exact hJe2 () m rfl
          · exact hJe2 () m rfl

end LeanQbe.T.Examples.Kissat.FullM7BcpHot
