/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof2b

/-!
# Kissat Fidelity Delayed-Watch BCP Proofs — Part 2c (Large-Clause Watch Step)

Plain `public section` (`0` `@[expose]`, `0` `import all`). Proves the delayed-buffer push
step, the found-replacement tail `fidLpReplDelExpr`, and the large-clause watch step
`fidLpLargeStepExpr` of `full_propagate_ignore_fid`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBcp

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FastCore
open LeanQbe.T.Examples.Kissat.FullM5Otfs
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM7BcpHot
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeHelpers
open LeanQbe.T.Examples.Kissat.Full.FullPropDecSpecs hiding
  fullWatchPushSpec fullPropLitSpec fullPropagateIgnoreSpec fullPropagateSpec
  FullTrailExt FullArenaPermEq
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

attribute [local irreducible] fastPropMem

local macro "fid_hsteps" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps))

local macro "fid_hsteps_nogrp" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps_nogrp))

local macro "fid_hsplit" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsplit))

/-! ## 1. Delayed-Buffer Push Step \& Found-Replacement Tail (`fidLpReplDelExpr`) -/

/-- Delayed-buffer push step (`del[3 * dlen ..< 3 * dlen + 3] = (repl, other, cref)`) after the
arena watch swap: re-establishes `PropLitInv` over the updated buffer and extends
`DelayedWatchesOk`. -/
theorem fid_repl_delay_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_orig sem1 st3 : FullState} {not_lit other repl cref : BitVec 32}
    {off_v q_v p2_n end_v dlen : Nat}
    (hpi1 : PropLitInv c F0 F_cur
      { s_orig with scratch := { s_orig.scratch with delayed := sem1.scratch.delayed } } sem1
      not_lit.toNat off_v q_v p2_n end_v)
    (hst3_core : st3.core = { sem1.core with arena := st3.core.arena })
    (hst3_sc : st3.scratch = sem1.scratch)
    (hlen3 : st3.LengthsOk c)
    (hnw3 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st3.core))
    (hsw3 : SplitWatchesInv F_cur st3.core not_lit.toNat off_v q_v p2_n end_v)
    (hperm13 : FullPropDecSpecs.FullArenaPermEq sem1.core st3.core)
    (hcr_lt : cref.toNat < 0x80000000)
    (hcr_ref1 : cref.toNat ∈ fullArenaClauseRefsCore sem1.core)
    (hrepl_lt : repl.toNat < 2 * sem1.core.cur_vars) (hrepl_ne : repl.toNat ≠ not_lit.toNat)
    (hoth_flag : (other &&& 0x80000000#32) = 0#32)
    (hdok : DelayedWatchesOk s_orig.core sem1.scratch.delayed dlen not_lit.toNat)
    (hdlen_lt : dlen < c.delayed_cap) :
    let del' : List (BitVec 32) :=
      ((sem1.scratch.delayed.set (3 * dlen) repl).set (3 * dlen + 1) other).set
        (3 * dlen + 2) cref
    let st4 : FullState := { st3 with scratch := { st3.scratch with delayed := del' } }
    PropLitInv c F0 F_cur { s_orig with scratch := { s_orig.scratch with delayed := del' } } st4
      not_lit.toNat off_v q_v p2_n end_v ∧
    DelayedWatchesOk s_orig.core del' (dlen + 1) not_lit.toNat := by
  intro del' st4
  have hdel_len3 := hlen3.scratch_ok.delayed_len_arr
  have hdel_len1 : sem1.scratch.delayed.length = 3 * c.delayed_cap := by
    rw [← hst3_sc]; exact hdel_len3
  have hlen4 : st4.LengthsOk c :=
    ⟨hlen3.core_ok, { hlen3.scratch_ok with delayed_len_arr := by simp [st4, del', hdel_len1] }⟩
  have hcore4 : st4.core = { sem1.core with arena := st3.core.arena } := hst3_core
  have hag4 : AgreesExcept propLitCoreMask
      ({ s_orig with scratch := { s_orig.scratch with delayed := del' } } : FullState).core
      st4.core := by
    have hag1 := hpi1.ag.update (fun k => { k with arena := st3.core.arena })
    rw [hcore4]; exact hag1
  have hcv1 : sem1.core.cur_vars = s_orig.core.cur_vars := hpi1.cur_vars_eq
  have href1 : fullArenaClauseRefsCore sem1.core = fullArenaClauseRefsCore s_orig.core :=
    hpi1.perm.1
  refine ⟨{ len := hlen4, nw := hnw3, sw := hsw3, ag := hag4
            tr := hpi1.tr.congr (by rw [hcore4]) (by rw [hcore4]) (by rw [hcore4])
            perm := hpi1.perm.trans hperm13
            sc_eq := by
              have hs1 := hpi1.sc_eq
              dsimp only [st4]; rw [hst3_sc, hs1]
            not_f := by rw [hcore4]; exact hpi1.not_f },
          delayedWatchesOk_push hdok (by rw [hdel_len1]; omega) (hcv1 ▸ hrepl_lt) hrepl_ne
            hoth_flag hcr_lt (href1 ▸ hcr_ref1)⟩

/-- Found-replacement tail: `repl == not_lit` is impossible (`not_lit` is false), the delayed
branch stores `(repl, other, cref)` into `h->delayed`, and the full-buffer branch exits with
`ovf = true` (arena untouched). -/
theorem fid_lp_repl_del_wp {Γ : Env} {rs : List Ty} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s_orig s_disk sem1 : FullState}
    {not_lit other cref repl : BitVec 32}
    {te un uf tk' p_v q end_v p2 off_v di dlim brk0 cbase ri : BitVec 64} {dlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    {J_ovf : Cont [i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool, i32, i32, i32, i64]}
    {J_lp : Cont [i64, i64, i64, i64, i64, i64, i64]}
    (har : c.arena_cap < 2 * dimacsBound)
    (hpi1 : PropLitInv c F0 F_cur
      { s_orig with scratch := { s_orig.scratch with delayed := sem1.scratch.delayed } } sem1
      not_lit.toNat off_v.toNat q.toNat (p_v.toNat + 2) end_v.toNat)
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
    (hoth_lt : other.toNat < 2 * sem1.core.cur_vars)
    (hcbase : cbase.toNat = cref.toNat + 3)
    (hdi : di.toNat = 3 * dlen) (hdlen : dlen ≤ c.delayed_cap)
    (hdlim : dlim.toNat = 3 * c.delayed_cap)
    (hdok : DelayedWatchesOk s_orig.core sem1.scratch.delayed dlen not_lit.toNat)
    (hm : (FullMem c (fastPropMem s_disk sem1) ⋆ R) m)
    (hJ_ovf : ∀ m_o, (FullMem c (fastPropMem s_disk sem1) ⋆ R) m_o →
      wp Γ Q X (.jump J_ovf (.var te, (.var un, (.var uf, (.var tk', (.var p2, (.var q,
        (.var di, (.var brk0, (.imm true, (.var repl, (.var other, (.var cref,
        (.var ri, ())))))))))))))) m_o)
    (hJ_lp : ∀ (sem4 : FullState) (di' : BitVec 64) (dlen' : Nat) (m_l : Mem 64),
      PropLitInv c F0 F_cur
        { s_orig with scratch := { s_orig.scratch with delayed := sem4.scratch.delayed } } sem4
        not_lit.toNat off_v.toNat q.toNat (p_v.toNat + 2) end_v.toNat →
      di'.toNat = 3 * dlen' → dlen' ≤ c.delayed_cap →
      DelayedWatchesOk s_orig.core sem4.scratch.delayed dlen' not_lit.toNat →
      (c.delayed_cap = 0 → sem4.scratch.delayed = sem1.scratch.delayed) →
      sem4.core.oom = sem1.core.oom → sem4.core.confl_type = sem1.core.confl_type →
      sem4.core.trail_end = sem1.core.trail_end →
      sem4.core.unassigned = sem1.core.unassigned →
      sem4.core.unflushed = sem1.core.unflushed →
      (FullMem c (fastPropMem s_disk sem4) ⋆ R) m_l →
      wp Γ Q X (.jump J_lp (.var te, (.var un, (.var uf, (.var tk', (.var p2, (.var q,
        (.var di', ())))))))) m_l) :
    wp Γ Q X (fidLpReplDelExpr c.pWstk c.pArena c.pDelayed dlim not_lit other cref te un uf tk'
      p2 q di brk0 cbase ri repl J_ovf J_lp) m := by
  have hdelc := c.hdel
  have hmaxv := c.hmaxv
  unfold dimacsBound at har hdelc hmaxv
  have hcv := hpi1.len.core_ok.cur_vars_le
  have haren1 := hpi1.len.core_ok.arena_len_arr
  have halen1 := hpi1.len.core_ok.arena_len_le
  have hdel1 := hpi1.len.scratch_ok.delayed_len_arr
  have hcap64 : c.arena_cap < 2 ^ 64 := Nat.lt_trans har (by decide)
  have hfit_cap : cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤
      c.arena_cap := Nat.le_trans hfit halen1
  have hcbase1 : (cbase + 1#64).toNat = cref.toNat + 4 := by
    rw [m7_bv64_add1_toNat (by rw [hcbase]; omega), hcbase]
  have hcbri : (cbase + ri).toNat = cref.toNat + 3 + ri.toNat := by
    rw [m7_bv64_add_toNat (by rw [hcbase]; omega), hcbase]
  have hswap := m7_swapCl_step hpi1 hcr_ref hfit har3 har4 hri2 hri_lt har_ri
  let ar3 := ((sem1.core.arena.set (cref.toNat + 3) other).set (cref.toNat + 4) repl).set
    (cref.toNat + 3 + ri.toNat) not_lit
  let st3 : FullState := { sem1 with core := { sem1.core with arena := ar3 } }
  have hswap_st3 : st3.core = { sem1.core with arena := st3.core.arena } ∧
      st3.scratch = sem1.scratch ∧ st3.LengthsOk c ∧
      FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st3.core) ∧
      SplitWatchesInv F_cur st3.core not_lit.toNat off_v.toNat q.toNat (p_v.toNat + 2) end_v.toNat ∧
      FullPropDecSpecs.FullArenaPermEq sem1.core st3.core ∧
      cref.toNat ∈ fullArenaClauseRefsCore st3.core := hswap
  obtain ⟨hst3_core, hst3_sc, hlen3, hnw3, hsw3, hperm13, _hcr_ref3⟩ := hswap_st3
  have hoth_mask : other &&& 0x7FFFFFFF#32 = other := m7_bv32_mask7f_eq (by omega)
  have hoth_flag : (other &&& 0x80000000#32) = 0#32 := by
    rw [← hoth_mask]; exact bv32_mask7f_flag0 other
  unfold fidLpReplDelExpr
  refine wp_join_group (fun x mj => ∃ (sem4 : FullState) (dlen' : Nat),
      x.1 = q ∧ x.2.1.toNat = 3 * dlen' ∧
      PropLitInv c F0 F_cur
        { s_orig with scratch := { s_orig.scratch with delayed := sem4.scratch.delayed } } sem4
        not_lit.toNat off_v.toNat q.toNat (p_v.toNat + 2) end_v.toNat ∧
      dlen' ≤ c.delayed_cap ∧
      DelayedWatchesOk s_orig.core sem4.scratch.delayed dlen' not_lit.toNat ∧
      (c.delayed_cap = 0 → sem4.scratch.delayed = sem1.scratch.delayed) ∧
      sem4.core.oom = sem1.core.oom ∧ sem4.core.confl_type = sem1.core.confl_type ∧
      sem4.core.trail_end = sem1.core.trail_end ∧
      sem4.core.unassigned = sem1.core.unassigned ∧
      sem4.core.unflushed = sem1.core.unflushed ∧
      (FullMem c (fastPropMem s_disk sem4) ⋆ R) mj) ?_ ?_
  · rintro _ ⟨q_out, di_out, _⟩ mj
      ⟨sem4, dlen', hq_eq, hdi', hpi4, hdl', hdok', hd0', h1, h2, h3, h4, h5, hmj⟩
    dsimp only at hq_eq hdi'
    subst hq_eq
    exact hJ_lp sem4 di_out dlen' mj hpi4 hdi' hdl' hdok' hd0' h1 h2 h3 h4 h5 hmj
  · intro Jret hJret
    fid_hsplit
    · exact absurd (congrArg BitVec.toNat hc) hrepl_ne
    · fid_hsplit
      · have hdi_lt : di.toNat < dlim.toNat := hc
        have hdlen_lt : dlen < c.delayed_cap := by omega
        refine fid_lp_ar_swap_wp haren1 hcbase hcbase1 hcbri (by omega) (by omega) (by omega)
          hm ?_
        intro m3 ar3' hm3
        have hdi1_nat : (di + 1).toNat = 3 * dlen + 1 := by
          rw [BitVec.toNat_add, hdi]; change (3 * dlen + 1) % 2 ^ 64 = 3 * dlen + 1
          exact Nat.mod_eq_of_lt (by omega)
        have hdi2_nat : (di + 2).toNat = 3 * dlen + 2 := by
          rw [BitVec.toNat_add, hdi]; change (3 * dlen + 2) % 2 ^ 64 = 3 * dlen + 2
          exact Nat.mod_eq_of_lt (by omega)
        have hdi3_nat : (di + 3).toNat = 3 * (dlen + 1) := by
          rw [BitVec.toNat_add, hdi]; change (3 * dlen + 3) % 2 ^ 64 = 3 * (dlen + 1)
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        have hdl3 : (fastPropMem s_disk st3).scratch.delayed.length = 3 * c.delayed_cap := by
          rw [fastPropMem_delayed]; exact hdel1
        fid_hsteps_nogrp
        refine wp_store_sep (FullArenaTactics.c0_store_full_delayed repl
          (by rw [hdl3]; omega) hm3) ?_
        intro m4 hm4; clear hm3; dsimp only at hm4
        rw [fastPropMem_delayed, fastPropMem_with_delayed, hdi] at hm4
        fid_hsteps_nogrp
        have hdl4 : (fastPropMem s_disk { st3 with scratch := { st3.scratch with
            delayed := st3.scratch.delayed.set (3 * dlen) repl } }).scratch.delayed.length =
            3 * c.delayed_cap := by
          rw [fastPropMem_delayed, List.length_set]; exact hdel1
        refine wp_store_sep (FullArenaTactics.c0_store_full_delayed other
          (by rw [hdl4]; omega) hm4) ?_
        intro m5 hm5; clear hm4; dsimp only at hm5
        rw [fastPropMem_delayed, fastPropMem_with_delayed, hdi1_nat] at hm5
        fid_hsteps_nogrp
        have hdl5 : (fastPropMem s_disk { st3 with scratch := { st3.scratch with
            delayed := (st3.scratch.delayed.set (3 * dlen) repl).set (3 * dlen + 1) other } }
            ).scratch.delayed.length = 3 * c.delayed_cap := by
          rw [fastPropMem_delayed, List.length_set, List.length_set]; exact hdel1
        refine wp_store_sep (FullArenaTactics.c0_store_full_delayed cref
          (by rw [hdl5]; omega) hm5) ?_
        intro m6 hm6; clear hm5; dsimp only at hm6
        rw [fastPropMem_delayed, fastPropMem_with_delayed, hdi2_nat] at hm6
        fid_hsteps
        have ⟨hpi4, hdok4⟩ := fid_repl_delay_step (st3 := st3) (other := other) hpi1 hst3_core
          hst3_sc hlen3 hnw3 hsw3 hperm13 hcr_lt hcr_ref hrepl_lt hrepl_ne hoth_flag hdok
          hdlen_lt
        let del4 : List (BitVec 32) :=
          ((sem1.scratch.delayed.set (3 * dlen) repl).set (3 * dlen + 1) other).set
            (3 * dlen + 2) cref
        exact hJret _ _ ⟨{ st3 with scratch := { st3.scratch with delayed := del4 } },
          dlen + 1, rfl, hdi3_nat, hpi4, by omega, hdok4,
          fun h0 => absurd h0 (by omega), rfl, rfl, rfl, rfl, rfl, hm6⟩
      · fid_hsteps
        exact hJ_ovf m hm

/-! ## 2. Large-Clause Watch Step (`fidLpLargeStepExpr`) -/

theorem fid_lp_large_step_wp {Γ : Env} {rs : List Ty} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s_base s_orig s_disk sem : FullState}
    {cur_lvl32 not_lit w0 nl_lvl : BitVec 32}
    {two_cv te un uf tk p q di dlim brk0 end_v off_v ignore_ref : BitVec 64} {rec_ph : Bool}
    {dlen : Nat} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    {J_ovf : Cont [i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool, i32, i32, i32, i64]}
    {J_lp : Cont [i64, i64, i64, i64, i64, i64, i64]}
    (hmaxv : c.max_vars < 2 * dimacsBound) (har : c.arena_cap < 2 * dimacsBound)
    (hwc : c.wcap < 2 * dimacsBound)
    (hsb : s_base =
      { s_orig with scratch := { s_orig.scratch with delayed := sem.scratch.delayed } })
    (hpi : PropLitInv c F0 F_cur s_base sem not_lit.toNat off_v.toNat q.toNat p.toNat end_v.toNat)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (htwo_cv : two_cv.toNat = 2 * sem.core.cur_vars)
    (hcur_lvl : cur_lvl32 = BitVec.ofNat 32 sem.core.cur_level)
    (hcl32 : sem.core.cur_level < 2 ^ 32)
    (hp_lt : p.toNat < end_v.toNat)
    (hw0_get : sem.core.wstk[p.toNat]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hte_eq : te.toNat = sem.core.trail_end)
    (hun_eq : un = sem.core.unassigned) (huf_eq : uf = sem.core.unflushed)
    (hoom : sem.core.oom = 0#64)
    (hnl : sem.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl)
    (hdi : di.toNat = 3 * dlen) (hdlen : dlen ≤ c.delayed_cap)
    (hdlim : dlim.toNat = 3 * c.delayed_cap)
    (hdok : DelayedWatchesOk s_orig.core sem.scratch.delayed dlen not_lit.toNat)
    (hm : (FullMem c (fastPropMem s_disk sem) ⋆ R) m)
    (hJ_ovf : ∀ {sem' : FullState} {tk' p' q' brk' : BitVec 64} {ovf' : Bool}
        {ovf_rw' ovf_oth' ovf_cr' : BitVec 32} {ovf_ri' : BitVec 64} {m' : Mem 64},
      PropLitInv c F0 F_cur s_base sem' not_lit.toNat off_v.toNat q'.toNat p'.toNat end_v.toNat →
      te.toNat = sem'.core.trail_end → sem'.core.oom = 0#64 →
      sem'.core.unassigned = sem.core.unassigned → sem'.core.unflushed = sem.core.unflushed →
      (ovf' = false → p.toNat ≤ p'.toNat ∧ brk' = 1#64 ∧ PropLitConfl F_cur ignore_ref sem'.core) →
      (ovf' = true → brk' = brk0 ∧ sem'.core.confl_type = sem.core.confl_type ∧
        p.toNat < p'.toNat ∧ p'.toNat ≤ end_v.toNat ∧ 2 ≤ p'.toNat - off_v.toNat ∧
        q'.toNat + 2 ≤ p'.toNat ∧
        ovf_cr'.toNat < 0x80000000 ∧ ovf_cr'.toNat ∈ fullArenaClauseRefsCore sem'.core ∧
        ovf_cr'.toNat + 3 + fullArenaClauseSizeCore sem'.core ovf_cr'.toNat ≤
          sem'.core.arena_len ∧
        ovf_oth'.toNat < 2 * sem'.core.cur_vars ∧ ovf_rw'.toNat < 2 * sem'.core.cur_vars ∧
        ovf_rw'.toNat ≠ not_lit.toNat ∧ 2 ≤ ovf_ri'.toNat ∧
        ovf_ri'.toNat < fullArenaClauseSizeCore sem'.core ovf_cr'.toNat ∧
        sem'.core.arena[ovf_cr'.toNat + 3]? = some ovf_oth' ∧
        sem'.core.arena[ovf_cr'.toNat + 4]? = some not_lit ∧
        sem'.core.arena[ovf_cr'.toNat + 3 + ovf_ri'.toNat]? = some ovf_rw') →
      (FullMem c (fastPropMem s_disk sem') ⋆ R) m' →
      wp Γ Q X (.jump J_ovf (.var te, (.var un, (.var uf, (.var tk', (.var p', (.var q',
        (.var di, (.var brk', (.var ovf', (.var ovf_rw', (.var ovf_oth', (.var ovf_cr',
        (.var ovf_ri', ())))))))))))))) m')
    (hJ_lp : ∀ {sem' : FullState} {te' un' uf' tk' p' q' di' : BitVec 64} {dlen' : Nat}
        {m' : Mem 64},
      PropLitInv c F0 F_cur
        { s_orig with scratch := { s_orig.scratch with delayed := sem'.scratch.delayed } } sem'
        not_lit.toNat off_v.toNat q'.toNat p'.toNat end_v.toNat →
      di'.toNat = 3 * dlen' → dlen' ≤ c.delayed_cap →
      DelayedWatchesOk s_orig.core sem'.scratch.delayed dlen' not_lit.toNat →
      (c.delayed_cap = 0 → sem'.scratch.delayed = sem.scratch.delayed) →
      p.toNat < p'.toNat → p'.toNat ≤ end_v.toNat →
      sem.core.trail_end ≤ sem'.core.trail_end →
      te'.toNat = sem'.core.trail_end → un' = sem'.core.unassigned → uf' = sem'.core.unflushed →
      sem'.core.oom = sem.core.oom → sem'.core.confl_type = sem.core.confl_type →
      (FullMem c (fastPropMem s_disk sem') ⋆ R) m' →
      wp Γ Q X (.jump J_lp (.var te', (.var un', (.var uf', (.var tk', (.var p', (.var q',
        (.var di', ())))))))) m') :
    wp Γ Q X (fidLpLargeStepExpr c.hdr ignore_ref c.pVals c.pWstk c.pArena c.pLevel c.pReason
      c.pTrail c.pTrailPos c.pFlags c.pPhases c.pDelayed dlim two_cv cur_lvl32 not_lit w0 nl_lvl
      rec_ph te un uf tk p q di brk0 J_ovf J_lp) m := by
  have hJ_lp' : ∀ {sem' : FullState} {te' un' uf' tk' p' q' : BitVec 64} {m' : Mem 64},
      PropLitInv c F0 F_cur s_base sem' not_lit.toNat off_v.toNat q'.toNat p'.toNat
        end_v.toNat →
      p.toNat < p'.toNat → p'.toNat ≤ end_v.toNat →
      sem.core.trail_end ≤ sem'.core.trail_end →
      te'.toNat = sem'.core.trail_end → un' = sem'.core.unassigned →
      uf' = sem'.core.unflushed →
      sem'.core.oom = sem.core.oom → sem'.core.confl_type = sem.core.confl_type →
      (FullMem c (fastPropMem s_disk sem') ⋆ R) m' →
      wp Γ Q X (.jump J_lp (.var te', (.var un', (.var uf', (.var tk', (.var p', (.var q',
        (.var di, ())))))))) m' := by
    intro sem' te' un' uf' tk' p' q' m' hpi' h1 h2 h3 h4 h5 h6 h7 h8 hm'
    have hd' : sem'.scratch.delayed = sem.scratch.delayed := by
      rw [fid_pi_delayed_eq hpi', hsb]
    subst hsb
    exact hJ_lp (fid_pi_rebase hpi') hdi hdlen (hd' ▸ hdok) (fun _ => hd') h1 h2 h3 h4 h5
      h6 h7 h8 hm'
  unfold dimacsBound at hmaxv har hwc
  have hcv := hpi.len.core_ok.cur_vars_le
  have hvals_len := hpi.len.core_ok.vals_len
  have haren_len := hpi.len.core_ok.arena_len_arr
  have halen_le := hpi.len.core_ok.arena_len_le
  have hlvl_len := hpi.len.core_ok.lvl_len
  have hwstk_len := hpi.len.core_ok.wstk_len_arr
  have ⟨hend_le, hwlen_le⟩ := hpi.end_lt_wcap hnot_lt
  have hend_wcap : end_v.toNat ≤ c.wcap := Nat.le_trans hend_le hwlen_le
  have hwc64 : c.wcap + 2 < 2 ^ 64 := Nat.lt_trans (Nat.add_lt_add_right hwc 2) (by decide)
  have hcap64 : c.arena_cap < 2 ^ 64 := Nat.lt_trans har (by decide)
  have hq_ge := hpi.sw.q_ge; have hq_le := hpi.sw.q_le_p; have hp_le := hpi.sw.p_le_end
  have hp_rem_pos : 0 < end_v.toNat - p.toNat := Nat.sub_pos_of_lt hp_lt
  obtain ⟨h2le, cref0, hcr_get, hcr_lt, hcr_ref, hrem2⟩ :=
    watchSlice_inv_large hpi.sw.rem_slice hp_rem_pos hw0_get hflag
  have h2_le_end : p.toNat + 2 ≤ end_v.toNat := by omega
  have hp1_n : (p + 1#64).toNat = p.toNat + 1 := m7_bv64_add1_toNat (by omega)
  have hp2_n : (p + 2#64).toNat = p.toNat + 2 := m7_bv64_add2_toNat (by omega)
  have hp2_n11 : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by
    have : p + 1#64 + 1#64 = p + 2#64 := by rw [BitVec.add_assoc]; rfl
    rw [this, hp2_n]
  have hp2_n11' : (p + (1 : BitVec 64) + (1 : BitVec 64)).toNat = p.toNat + 2 := hp2_n11
  have hq1_n : (q + 1#64).toNat = q.toNat + 1 := m7_bv64_add1_toNat (by omega)
  have hq2_n : (q + 2#64).toNat = q.toNat + 2 := m7_bv64_add2_toNat (by omega)
  have hp1_ws : (p + 1#64).toNat < (fastPropMem s_disk sem).core.wstk.length := by
    rw [fastPropMem_wstk, hwstk_len, hp1_n]; omega
  have hq_ws : q.toNat < (fastPropMem s_disk sem).core.wstk.length := by
    rw [fastPropMem_wstk, hwstk_len]; omega
  have hq1_ws : (q + 1#64).toNat < (fastPropMem s_disk sem).core.wstk.length := by
    rw [fastPropMem_wstk, hwstk_len, hq1_n]; omega
  have hcr_eq : (fastPropMem s_disk sem).core.wstk[(p + 1#64).toNat]'hp1_ws = cref0 := by
    rw [fc_getElem_wstk]
    exact Option.some.inj ((List.getElem?_eq_getElem (by rw [hwstk_len, hp1_n]; omega)).symm.trans
      (hp1_n ▸ hcr_get))
  have hcr_eq' :
      (fastPropMem s_disk sem).core.wstk[(p + (1 : BitVec 64)).toNat]'hp1_ws = cref0 := hcr_eq
  have hcr_eq_raw :
      sem.core.wstk[(p + (1 : BitVec 64)).toNat]'(by
        rw [hwstk_len, show (p + (1 : BitVec 64)).toNat = p.toNat + 1 from hp1_n]; omega) =
      cref0 := by
    rw [← fc_getElem_wstk (s0 := s_disk) (sem := sem)]; exact hcr_eq'
  have hsw_drop : SplitWatchesInv F_cur sem.core not_lit.toNat off_v.toNat q.toNat
      (p.toNat + 2) end_v.toNat :=
    hpi.sw.advance_rem (p' := p.toNat + 2) (by omega) h2_le_end (by simpa [Nat.sub_sub] using hrem2)
  have hpi_drop : PropLitInv c F0 F_cur s_base sem not_lit.toNat off_v.toNat q.toNat
      (p.toNat + 2) end_v.toNat :=
    { hpi with sw := hsw_drop }
  have hcr_wf := hpi.nw.arena.refs_wf cref0.toNat hcr_ref
  have hcsz3 : 3 ≤ fullArenaClauseSizeCore sem.core cref0.toNat := hcr_wf.2.1
  have hcr_fit : cref0.toNat + 3 + fullArenaClauseSizeCore sem.core cref0.toNat ≤
      sem.core.arena_len := Nat.le_trans hcr_wf.2.2.1 hcr_wf.2.2.2.1
  have hp2_n' : (p + (2 : BitVec 64)).toNat = p.toNat + 2 := hp2_n
  have hsem_sc :
      { sem with scratch := { sem.scratch with search_ticks := sem.scratch.search_ticks } } =
      sem := by
    cases sem; rfl
  unfold fidLpLargeStepExpr fidLpScanExpr fidLpNoReplExpr
  refine wp_join_group (fun () mc => (FullMem c (fastPropMem s_disk sem) ⋆ R) mc) ?_ ?_
  · rintro _ ⟨⟩ mc hm
    fid_hsteps_nogrp
    simp only [hcr_eq']
    have hcr0_m : (cref0.setWidth 64).toNat < (fastPropMem s_disk sem).core.arena.length := by
      rw [fastPropMem_arena, haren_len, bv_c0_zext32_64]
      exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans hcr_fit halen_le)
    fid_hsplit
    · have hpi_d := propLit_inv_drop (ticks' := sem.scratch.search_ticks) hpi hsw_drop hp2_n11
      rw [hp2_n11, ← hp2_n', hsem_sc] at hpi_d
      fid_hsteps
      exact hJ_lp' hpi_d (by rw [hp2_n']; omega) (by rw [hp2_n']; omega) (Nat.le_refl _) hte_eq
        hun_eq huf_eq rfl rfl hm
    · have hng0 : fullArenaClauseGarbCore sem.core cref0.toNat = false := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore
        have hg : sem.core.arena[cref0.toNat]? =
            some (sem.core.arena[cref0.toNat]'(by rw [haren_len]; omega)) :=
          List.getElem?_eq_getElem _
        have hfl_eq : (fastPropMem s_disk sem).core.arena[cref0.toNat]'(by
            rw [fastPropMem_arena, haren_len]; omega) =
            sem.core.arena[cref0.toNat]'(by rw [haren_len]; omega) :=
          fc_getElem_arena s_disk sem
        rw [hg, Option.getD_some, ← hfl_eq]
        simpa [show (524288 : BitVec 32) = 524288#32 from rfl] using hc
      have hcbase_n : (cref0.setWidth 64 + 3#64).toNat = cref0.toNat + 3 :=
        m7_bv64_add_toNat (by rw [bv_c0_zext32_64]; have := hcr_lt; simp; omega)
      have hcbase1_n : (cref0.setWidth 64 + 3#64 + 1#64).toNat = cref0.toNat + 4 := by
        rw [m7_bv64_add1_toNat (by rw [hcbase_n]; omega), hcbase_n]
      have hcr3_m : (cref0.setWidth 64 + 3#64).toNat <
          (fastPropMem s_disk sem).core.arena.length := by
        rw [fastPropMem_arena, haren_len, hcbase_n]; exact Nat.lt_of_lt_of_le (by omega)
          (Nat.le_trans hcr_fit halen_le)
      have hcr4_m : (cref0.setWidth 64 + 3#64 + 1#64).toNat <
          (fastPropMem s_disk sem).core.arena.length := by
        rw [fastPropMem_arena, haren_len, hcbase1_n]; exact Nat.lt_of_lt_of_le (by omega)
          (Nat.le_trans hcr_fit halen_le)
      fid_hsteps_nogrp
      let l0 := (fastPropMem s_disk sem).core.arena[(cref0.setWidth 64 + 3#64).toNat]'hcr3_m
      let l1 := (fastPropMem s_disk sem).core.arena[(cref0.setWidth 64 + 3#64 + 1#64).toNat]'hcr4_m
      have hl0_eq : l0 = sem.core.arena[cref0.toNat + 3]'(by rw [haren_len]; omega) :=
        (fc_getElem_arena s_disk sem).trans (fc_getElem_eq_of_idx hcbase_n _ _)
      have hl1_eq : l1 = sem.core.arena[cref0.toNat + 4]'(by rw [haren_len]; omega) :=
        (fc_getElem_arena s_disk sem).trans (fc_getElem_eq_of_idx hcbase1_n _ _)
      have hl0_get : sem.core.arena[cref0.toNat + 3]? = some l0 :=
        hl0_eq ▸ List.getElem?_eq_getElem (by rw [haren_len]; omega)
      have hl1_get : sem.core.arena[cref0.toNat + 4]? = some l1 :=
        hl1_eq ▸ List.getElem?_eq_getElem (by rw [haren_len]; omega)
      have hl0_idx' : (cref0.toNat + BitVec.toNat (3 : BitVec 64)) % 2 ^ 64 =
          (cref0.setWidth 64 + 3#64).toNat := by
        rw [hcbase_n, show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
          Nat.mod_eq_of_lt (by have := hcr_lt; omega)]
      have hl1_idx' : (cref0.toNat + BitVec.toNat (3 : BitVec 64) +
          BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = (cref0.setWidth 64 + 3#64 + 1#64).toNat := by
        rw [hcbase1_n, show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
          show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
          Nat.mod_eq_of_lt (by have := hcr_lt; omega)]
      have hidx0_m : (cref0.toNat + BitVec.toNat (3 : BitVec 64)) % 2 ^ 64 <
          (fastPropMem s_disk sem).core.arena.length := by rw [hl0_idx']; exact hcr3_m
      have hidx1_m : (cref0.toNat + BitVec.toNat (3 : BitVec 64) +
          BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 <
          (fastPropMem s_disk sem).core.arena.length := by rw [hl1_idx']; exact hcr4_m
      have hl0_hc : (fastPropMem s_disk sem).core.arena[
          (cref0.toNat + BitVec.toNat (3 : BitVec 64)) % 2 ^ 64]'hidx0_m = l0 :=
        fc_getElem_eq_of_idx hl0_idx' _ _
      have hl1_hc : (fastPropMem s_disk sem).core.arena[
          (cref0.toNat + BitVec.toNat (3 : BitVec 64) + BitVec.toNat (1 : BitVec 64)) %
            2 ^ 64]'hidx1_m = l1 :=
        fc_getElem_eq_of_idx hl1_idx' _ _
      refine wp_join_group (fun () mchk =>
          (FullMem c (fastPropMem s_disk sem) ⋆ R) mchk ∧ (l0 = not_lit ∨ l1 = not_lit)) ?_ ?_
      · rintro _ ⟨⟩ mchk ⟨hm, hwatch⟩
        let other := l0 ^^^ l1 ^^^ not_lit
        refine wp_join_group (fun () msw => ∃ sem1 : FullState,
            PropLitInv c F0 F_cur s_base sem1 not_lit.toNat off_v.toNat q.toNat
              (p.toNat + 2) end_v.toNat ∧
            sem1.core.oom = sem.core.oom ∧ sem1.core.confl_type = sem.core.confl_type ∧
            sem1.core.trail_end = sem.core.trail_end ∧
            sem1.core.unassigned = sem.core.unassigned ∧
            sem1.core.unflushed = sem.core.unflushed ∧
            sem1.core.arena_len = sem.core.arena_len ∧
            sem1.core.cur_level = sem.core.cur_level ∧
            cref0.toNat ∈ fullArenaClauseRefsCore sem1.core ∧
            fullArenaClauseGarbCore sem1.core cref0.toNat = false ∧
            fullArenaClauseSizeCore sem1.core cref0.toNat =
              fullArenaClauseSizeCore sem.core cref0.toNat ∧
            sem1.core.arena[cref0.toNat + 3]? = some other ∧
            sem1.core.arena[cref0.toNat + 4]? = some not_lit ∧
            sem1.core.lvl = sem.core.lvl ∧
            (FullMem c (fastPropMem s_disk sem1) ⋆ R) msw) ?_ ?_
        · rintro _ ⟨⟩ msw ⟨sem1, hpi1, hoom1, hct1, hte1, hun1, huf1, halen1, hcl1,
              hcr_ref1, hng1, hcsz1, har3, har4, hlvq1, hmsw⟩
          have hcv1 : sem1.core.cur_vars = sem.core.cur_vars :=
            hpi1.cur_vars_eq.trans hpi.cur_vars_eq.symm
          have haren1 := hpi1.len.core_ok.arena_len_arr
          have halen1_le := hpi1.len.core_ok.arena_len_le
          have hvals1 := hpi1.len.core_ok.vals_len
          have hlvl1 := hpi1.len.core_ok.lvl_len
          have hnot1 : not_lit.toNat < 2 * sem1.core.cur_vars := hcv1 ▸ hnot_lt
          have hfit1 : cref0.toNat + 3 + fullArenaClauseSizeCore sem1.core cref0.toNat ≤
              sem1.core.arena_len := by rw [hcsz1, halen1]; exact hcr_fit
          have hcsz3_1 : 3 ≤ fullArenaClauseSizeCore sem1.core cref0.toNat := hcsz1 ▸ hcsz3
          have hbd1 : cref0.toNat + 3 + fullArenaClauseSizeCore sem1.core cref0.toNat ≤
              sem1.core.arena.length := haren1 ▸ Nat.le_trans hfit1 halen1_le
          have hoth_mem : other.toNat ∈ fullArenaClauseLitsCore sem1.core cref0.toNat :=
            (mem_fullArenaClauseLitsCore_iff hbd1).mpr ⟨0, by omega,
              congrArg BitVec.toNat (Option.some.inj
                ((List.getElem?_eq_getElem (by rw [haren1]; omega)).symm.trans har3))⟩
          have hoth_lt : other.toNat < 2 * sem1.core.cur_vars :=
            hpi1.nw.arena.lits_lt cref0.toNat hcr_ref1 hng1 other.toNat hoth_mem
          have hnot_mem : not_lit.toNat ∈ fullArenaClauseLitsCore sem1.core cref0.toNat :=
            (mem_fullArenaClauseLitsCore_iff hbd1).mpr ⟨1, by omega,
              congrArg BitVec.toNat (Option.some.inj
                ((List.getElem?_eq_getElem (by rw [haren1]; omega)).symm.trans har4))⟩
          have hoth_vals_m : (other.setWidth 64).toNat <
              (fastPropMem s_disk sem1).core.vals.length := by
            rw [fastPropMem_vals, hvals1, bv_c0_zext32_64]; omega
          have hoth_vals_raw : other.toNat < sem1.core.vals.length := by rw [hvals1]; omega
          have hoth_mask : other &&& 0x7FFFFFFF#32 = other := m7_bv32_mask7f_eq (by omega)
          have hq_ws1 : q.toNat < (fastPropMem s_disk sem1).core.wstk.length := by
            rw [fastPropMem_wstk, hpi1.len.core_ok.wstk_len_arr, ← hwstk_len]
            rw [fastPropMem_wstk] at hq_ws; exact hq_ws
          have hq1_ws1 : (q + 1#64).toNat < (fastPropMem s_disk sem1).core.wstk.length := by
            rw [fastPropMem_wstk, hpi1.len.core_ok.wstk_len_arr, ← hwstk_len]
            rw [fastPropMem_wstk] at hq1_ws; exact hq1_ws
          let ov := (fastPropMem s_disk sem1).core.vals[(other.setWidth 64).toNat]'hoth_vals_m
          have hov_eq : ov = sem1.core.vals[other.toNat]'hoth_vals_raw :=
            (fc_getElem_vals s_disk sem1).trans
              (fc_getElem_eq_of_idx (bv_c0_zext32_64 other) _ hoth_vals_raw)
          have hoth_hc_idx :
              BitVec.toNat (lift2 (fun {n} (x1 x2 : BitVec n) => x1 ^^^ x2)
                (fun x1 x2 => x1 ^^ x2) i32
                (Arg.var (lift2 (fun {n} (x1 x2 : BitVec n) => x1 ^^^ x2)
                  (fun x1 x2 => x1 ^^ x2) i32
                  (Arg.var ((fastPropMem s_disk sem).core.arena[
                    (cref0.toNat + BitVec.toNat (3 : BitVec 64)) % 2 ^ 64]'hidx0_m)).val
                  (Arg.var ((fastPropMem s_disk sem).core.arena[
                    (cref0.toNat + BitVec.toNat (3 : BitVec 64) +
                      BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'hidx1_m)).val, ()).fst).val
                (Arg.var not_lit).val) = (other.setWidth 64).toNat := by
            have h1 : (lift2 (fun {n} (x1 x2 : BitVec n) => x1 ^^^ x2)
                (fun x1 x2 => x1 ^^ x2) i32
                (Arg.var ((fastPropMem s_disk sem).core.arena[
                  (cref0.toNat + BitVec.toNat (3 : BitVec 64)) % 2 ^ 64]'hidx0_m)).val
                (Arg.var ((fastPropMem s_disk sem).core.arena[
                  (cref0.toNat + BitVec.toNat (3 : BitVec 64) +
                    BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'hidx1_m)).val : BitVec 32) =
                l0 ^^^ l1 := by
              dsimp only [Arg.val]; rw [hl0_hc, hl1_hc]; rfl
            change BitVec.toNat (_ ^^^ not_lit) = (other.setWidth 64).toNat
            rw [h1, bv_c0_zext32_64]; rfl
          have hoth_hm_eq :
              (lift2 (fun {n} (x1 x2 : BitVec n) => x1 ^^^ x2) (fun x1 x2 => x1 ^^ x2) i32
                (Arg.var (lift2 (fun {n} (x1 x2 : BitVec n) => x1 ^^^ x2)
                  (fun x1 x2 => x1 ^^ x2) i32
                  (Arg.var ((fastPropMem s_disk sem).core.arena[
                    (cref0.setWidth 64 + (3 : BitVec 64)).toNat]'hcr3_m)).val
                  (Arg.var ((fastPropMem s_disk sem).core.arena[
                    (cref0.setWidth 64 + (3 : BitVec 64) +
                      (1 : BitVec 64)).toNat]'hcr4_m)).val, ()).fst).val
                (Arg.var not_lit).val : BitVec 32) = other := by
            simp only [Arg.val, fastPropMem_arena, show (3 : BitVec 64) = 3#64 from rfl,
              show (1 : BitVec 64) = 1#64 from rfl]
            change (_ ^^^ _) ^^^ not_lit = other
            rw [fc_getElem_eq_of_idx hcbase_n _ (by rw [haren_len]; omega), ← hl0_eq,
              fc_getElem_eq_of_idx hcbase1_n _ (by rw [haren_len]; omega), ← hl1_eq]
          fid_hsteps_nogrp
          fid_hsplit
          · fid_hsteps_nogrp
            simp only [fastPropMem_wstk, fastPropMem_with_wstk, hoth_hm_eq] at hm
            have hkeep := propLit_inv_keep_large hpi1 hpi1.sw hnot1 hq1_n hq2_n hp2_n11
              (Nat.add_le_add_right hq_le 2) hpi1.sw.p_le_end
              (bv32_mask7f_flag0 other) hcr_lt hcr_ref1
            rw [hoth_mask] at hkeep
            rw [show (p + (1 : BitVec 64) + (1 : BitVec 64)).toNat = (p + 2#64).toNat from
              hp2_n11'.trans hp2_n.symm] at hkeep
            fid_hsteps
            exact hJ_lp' hkeep (by rw [hp2_n']; omega) (by rw [hp2_n']; omega)
              (by simp [hte1]) (hte_eq.trans hte1.symm)
              (hun_eq.trans hun1.symm) (huf_eq.trans huf1.symm) hoom1 hct1 hm
          · have hov_nsgt : (0#32).slt (BitVec.signExtend 32 ov) = false := by
              simpa only [ov, hoth_hc_idx] using hc
            have hc2_n : (cref0.setWidth 64 + 2#64).toNat = cref0.toNat + 2 :=
              m7_bv64_add_toNat (by rw [bv_c0_zext32_64]; have := hcr_lt; simp; omega)
            have hc1_n : (cref0.setWidth 64 + 1#64).toNat = cref0.toNat + 1 :=
              m7_bv64_add1_toNat (by rw [bv_c0_zext32_64]; have := hcr_lt; omega)
            have hcr2_m : (cref0.setWidth 64 + 2#64).toNat <
                (fastPropMem s_disk sem1).core.arena.length := by
              rw [fastPropMem_arena, haren1, hc2_n]
              exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans hfit1 halen1_le)
            have hcr1_m : (cref0.setWidth 64 + 1#64).toNat <
                (fastPropMem s_disk sem1).core.arena.length := by
              rw [fastPropMem_arena, haren1, hc1_n]
              exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans hfit1 halen1_le)
            let csz32 := (fastPropMem s_disk sem1).core.arena[
              (cref0.setWidth 64 + 2#64).toNat]'hcr2_m
            let pos32 := (fastPropMem s_disk sem1).core.arena[
              (cref0.setWidth 64 + 1#64).toNat]'hcr1_m
            have hcsz64 : (csz32.setWidth 64).toNat =
                fullArenaClauseSizeCore sem1.core cref0.toNat := by
              unfold fullArenaClauseSizeCore
              have hcsz_eq : csz32 = sem1.core.arena[cref0.toNat + 2]'(by rw [haren1]; omega) :=
                (fc_getElem_arena s_disk sem1).trans (fc_getElem_eq_of_idx hc2_n _ _)
              rw [bv_c0_zext32_64, hcsz_eq,
                List.getElem?_eq_getElem (by rw [haren1]; omega), Option.getD_some]
            have hcsz64' : (BitVec.setWidth 64 ((fastPropMem s_disk sem1).core.arena[
                (cref0.setWidth 64 + (2 : BitVec 64)).toNat]'hcr2_m)).toNat =
                fullArenaClauseSizeCore sem1.core cref0.toNat := hcsz64
            fid_hsteps_nogrp
            refine wp_join_group (fun (st, ()) mst =>
                2 ≤ st.toNat ∧ st.toNat < fullArenaClauseSizeCore sem1.core cref0.toNat ∧
                (FullMem c (fastPropMem s_disk sem1) ⋆ R) mst) ?_ ?_
            · rintro _ ⟨st, ⟨⟩⟩ mst ⟨hst2, hst_lt, hmst⟩
              let ReplOk (ri : BitVec 64) (repl : BitVec 32) (found : Bool) : Prop :=
                (found = true ∧ 2 ≤ ri.toNat ∧
                  ∃ hr_lt : ri.toNat < fullArenaClauseSizeCore sem1.core cref0.toNat,
                    have har_len : cref0.toNat + 3 + ri.toNat < sem1.core.arena.length := by
                      rw [haren1]
                      exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans hfit1 halen1_le)
                    repl = sem1.core.arena[cref0.toNat + 3 + ri.toNat]'har_len ∧
                    repl.toNat < 2 * sem1.core.cur_vars ∧
                    ((sem1.core.vals[repl.toNat]?.getD 0#8).signExtend 32).slt 0#32 = false) ∨
                (found = false ∧
                  ∀ k, 2 ≤ k → k < fullArenaClauseSizeCore sem1.core cref0.toNat →
                    fullFindReplBad sem1 cref0.toNat k)
              refine wp_join_group (fun (ri1, repl1, found1, ()) mr1 =>
                  (FullMem c (fastPropMem s_disk sem1) ⋆ R) mr1 ∧
                  ((found1 = true ∧ st.toNat ≤ ri1.toNat ∧
                    ∃ hr_lt : ri1.toNat < fullArenaClauseSizeCore sem1.core cref0.toNat,
                      have har_len : cref0.toNat + 3 + ri1.toNat < sem1.core.arena.length := by
                        rw [haren1]
                        exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans hfit1 halen1_le)
                      repl1 = sem1.core.arena[cref0.toNat + 3 + ri1.toNat]'har_len ∧
                      repl1.toNat < 2 * sem1.core.cur_vars ∧
                      ((sem1.core.vals[repl1.toNat]?.getD 0#8).signExtend 32).slt 0#32 = false) ∨
                   (found1 = false ∧
                    ∀ k, st.toNat ≤ k → k < fullArenaClauseSizeCore sem1.core cref0.toNat →
                      fullFindReplBad sem1 cref0.toNat k))) ?_ ?_
              · rintro _ ⟨ri1, repl1, found1, ⟨⟩⟩ mr1 ⟨hmr1, hr1⟩
                refine wp_join_group (fun (ri, repl, found_f, ()) mr2 =>
                    (FullMem c (fastPropMem s_disk sem1) ⋆ R) mr2 ∧
                    ReplOk ri repl found_f) ?_ ?_
                · rintro _ ⟨ri, repl, found_f, ⟨⟩⟩ mr2 ⟨hmr2, hrep⟩
                  fid_hsplit
                  · rcases hrep with ⟨-, hri2, hri_lt, har_eq, hrepl_lt, hrepl_nneg⟩ | ⟨hf, -⟩
                    · have har_ri : sem1.core.arena[cref0.toNat + 3 + ri.toNat]? = some repl :=
                        har_eq ▸ List.getElem?_eq_getElem _
                      have hrepl_ne : repl.toNat ≠ not_lit.toNat := by
                        intro h
                        rw [h, hpi1.not_f] at hrepl_nneg
                        revert hrepl_nneg; decide
                      fid_hsteps_nogrp
                      rw [show (1 : BitVec 64) = 1#64 from rfl, hc1_n, fastPropMem_arena,
                        fastPropMem_with_arena] at hm
                      have hsr := m7_setSrch_step hpi1 hcr_ref1 hfit1 har3 har4 hri2 hri_lt har_ri
                        (ri32 := ri.setWidth 32)
                      let sem2 : FullState :=
                        { sem1 with
                          core :=
                            { sem1.core with
                              arena := sem1.core.arena.set (cref0.toNat + 1) (ri.setWidth 32) } }
                      have hcr_ref2 : cref0.toNat ∈ fullArenaClauseRefsCore sem2.core :=
                        hsr.2.2.2.1
                      have hfit2 : cref0.toNat + 3 + fullArenaClauseSizeCore sem2.core cref0.toNat ≤
                          sem2.core.arena_len := by
                        rw [hsr.2.2.2.2.1]; exact hfit1
                      have hcv2 : sem2.core.cur_vars = sem1.core.cur_vars := rfl
                      have hri_lt2 : ri.toNat < fullArenaClauseSizeCore sem2.core cref0.toNat := by
                        rw [hsr.2.2.2.2.1]; exact hri_lt
                      simp only [hoth_hm_eq]
                      have hd2 : sem2.core.lvl = sem2.core.lvl ∧
                          sem2.scratch.delayed = sem.scratch.delayed :=
                        ⟨rfl, by rw [fid_pi_delayed_eq hsr.1, hsb]⟩
                      refine fid_lp_repl_del_wp (s_orig := s_orig) har
                        (fid_pi_rebase (hsb ▸ hsr.1)) hcr_lt hcr_ref2
                        hfit2 hsr.2.2.2.2.2.1 hsr.2.2.2.2.2.2.1 hri2 hri_lt2 hsr.2.2.2.2.2.2.2
                        (hcv2 ▸ hrepl_lt) hrepl_ne (hcv2 ▸ hoth_lt) hcbase_n hdi hdlen hdlim
                        (hd2.2 ▸ hdok) hm ?_ ?_
                      · intro m_o hm_o
                        have hcr_fit2 : cref0.toNat + 3 +
                            fullArenaClauseSizeCore sem2.core cref0.toNat ≤ sem2.core.arena_len :=
                          hfit2
                        exact hJ_ovf (sem' := sem2) (hp2_n' ▸ hsr.1) (hte_eq.trans hte1.symm)
                          (by simpa only [sem2] using hoom1.trans hoom)
                          (by simpa only [sem2] using hun1) (by simpa only [sem2] using huf1)
                          (fun h => absurd h (by decide))
                          (fun _ => ⟨rfl, hct1, by rw [hp2_n']; omega, by rw [hp2_n']; omega,
                            by rw [hp2_n']; omega, by rw [hp2_n']; have := hpi.sw.q_le_p; omega,
                            hcr_lt, hcr_ref2, hcr_fit2, hcv2 ▸ hoth_lt,
                            hcv2 ▸ hrepl_lt, hrepl_ne, hri2, hri_lt2, hsr.2.2.2.2.2.1,
                            hsr.2.2.2.2.2.2.1, hsr.2.2.2.2.2.2.2⟩)
                          hm_o
                      · intro sem4 di' dlen' m_l hpi4 hdi4 hdl4 hdok4 hd04 hoom4 hct4 hte4 hun4
                          huf4 hm_l
                        exact hJ_lp (hp2_n' ▸ hpi4) hdi4 hdl4 hdok4
                          (fun h0 => (hd04 h0).trans hd2.2)
                          (by rw [hp2_n']; omega) (by rw [hp2_n']; omega)
                          (by
                            rw [hte4, show sem2.core.trail_end = sem1.core.trail_end from rfl, hte1]
                            exact Nat.le_refl _)
                          (hte_eq.trans (hte1.symm.trans hte4.symm))
                          (hun_eq.trans (hun4 ▸ hun1).symm)
                          (huf_eq.trans (huf4 ▸ huf1).symm)
                          (hoom4.trans hoom1) (hct4.trans hct1) hm_l
                    · exact absurd hc (by rw [hf]; decide)
                  · have hf_eq : found_f = false := by revert hc; cases found_f <;> simp
                    rcases hrep with ⟨hf, -⟩ | ⟨-, hbad_all⟩
                    · exact absurd (hf_eq.symm.trans hf) (by decide)
                    · fid_hsteps_nogrp
                      · simp only [fastPropMem_wstk, fastPropMem_with_wstk, hoth_hm_eq] at hm
                        let wstk2 := (sem1.core.wstk.set q.toNat other).set (q + 1#64).toNat cref0
                        have hkeep := propLit_inv_keep_large hpi1 hpi1.sw hnot1 hq1_n hq2_n hp2_n11
                          (Nat.add_le_add_right hq_le 2) hpi1.sw.p_le_end
                          (bv32_mask7f_flag0 other) hcr_lt hcr_ref1
                        rw [hoth_mask] at hkeep
                        rw [show (p + (1 : BitVec 64) + (1 : BitVec 64)).toNat =
                            (p + 2#64).toNat from hp2_n11'.trans hp2_n.symm] at hkeep
                        exact hJ_lp' hkeep (by rw [hp2_n']; omega) (by rw [hp2_n']; omega)
                          (by simp [hte1]) (hte_eq.trans hte1.symm)
                          (hun_eq.trans hun1.symm) (huf_eq.trans huf1.symm) hoom1 hct1 hm
                      · have hne_ign : cref0.setWidth 64 ≠ ignore_ref := by assumption
                        simp only [fastPropMem_wstk, hoth_hm_eq] at hm
                        let wstk2 := (sem1.core.wstk.set q.toNat other).set (q + 1#64).toNat cref0
                        have hbd_ar1 : cref0.toNat + 3 +
                            fullArenaClauseSizeCore sem1.core cref0.toNat ≤
                            sem1.core.arena.length := haren1 ▸ Nat.le_trans hfit1 halen1_le
                        have hunit := propLit_hunit hpi1.nw hcr_ref1 hng1 hbd_ar1 har3 har4
                          hpi1.not_f (fun k hk1 hk2 => by
                            have hb := hbad_all k hk1 (by
                              simpa only [fullArenaClauseSize, bv_c0_zext32_64] using hk2)
                            unfold fullFindReplBad at hb ⊢
                            simpa only [bv_c0_zext32_64] using hb)
                        have hslt_ov : (BitVec.signExtend 32 ov).slt 0#32 = true := by
                          simpa only [ov, hoth_hc_idx] using hc
                        have hov_f : sem1.core.vals[other.toNat]?.getD 0#8 = 0xFF#8 :=
                          propLit_vals_neg hpi1.nw hoth_lt hoth_vals_raw
                            (by rw [← hov_eq]; exact hslt_ov)
                        have ⟨hpi_c, hcf_c⟩ := propLit_large_confl hpi1 hnot1 hq_le hq1_n hq2_n
                          hp2_n11 hcr_lt hcr_ref1 hng1 hne_ign hov_f hunit
                        rw [hoth_mask,
                          show (p + (1 : BitVec 64) + (1 : BitVec 64)).toNat = (p + 2#64).toNat from
                            hp2_n11'.trans hp2_n.symm] at hpi_c
                        let sem_c : FullState :=
                          { sem1 with core :=
                            { sem1.core with
                              wstk := wstk2, confl_type := 2#64,
                              confl_ref := cref0.setWidth 64 } }
                        have hm_c : (FullMem c (fastPropMem s_disk sem_c) ⋆ R) m := by
                          simpa only [sem_c, wstk2, show (1 : BitVec 64) = 1#64 from rfl,
                            show (2 : BitVec 64) = 2#64 from rfl,
                            fid_fastPropMem_with_wstk_large_confl] using hm
                        exact hJ_ovf hpi_c (hte_eq.trans hte1.symm) (hoom1.trans hoom)
                          (hun1 ▸ rfl) (huf1 ▸ rfl)
                          (fun _ => ⟨by rw [hp2_n']; omega, rfl, hcf_c⟩)
                          (fun h => absurd h (by decide)) hm_c
                      · simp only [fastPropMem_wstk, fastPropMem_with_wstk, hoth_hm_eq] at hm
                        let wstk2 := (sem1.core.wstk.set q.toNat other).set (q + 1#64).toNat cref0
                        let sem2 : FullState :=
                          { sem1 with core := { sem1.core with wstk := wstk2 } }
                        have hkeep := propLit_inv_keep_large hpi1 hpi1.sw hnot1 hq1_n hq2_n hp2_n11
                          (Nat.add_le_add_right hq_le 2) hpi1.sw.p_le_end
                          (bv32_mask7f_flag0 other) hcr_lt hcr_ref1
                        rw [hoth_mask] at hkeep
                        rw [show (p + (1 : BitVec 64) + (1 : BitVec 64)).toNat =
                            (p + 2#64).toNat from hp2_n11'.trans hp2_n.symm] at hkeep
                        have hbd_ar1 : cref0.toNat + 3 +
                            fullArenaClauseSizeCore sem1.core cref0.toNat ≤
                            sem1.core.arena.length := haren1 ▸ Nat.le_trans hfit1 halen1_le
                        have hunit := propLit_hunit hpi1.nw hcr_ref1 hng1 hbd_ar1 har3 har4
                          hpi1.not_f (fun k hk1 hk2 => by
                            have hb := hbad_all k hk1 (by
                              simpa only [fullArenaClauseSize, bv_c0_zext32_64] using hk2)
                            unfold fullFindReplBad at hb ⊢
                            simpa only [bv_c0_zext32_64] using hb)
                        have hov_nslt : (BitVec.signExtend 32 ov).slt 0#32 = false := by
                          simpa only [ov, hoth_hc_idx] using hc
                        have hov_un : sem1.core.vals[other.toNat]?.getD 0#8 = 0#8 :=
                          propLit_vals_un hpi1.nw hoth_lt hoth_vals_raw
                            (by rw [← hov_eq]; exact hov_nsgt)
                            (by rw [← hov_eq]; exact hov_nslt)
                        have hpi2 : PropLitInv c F0 F_cur s_base sem2 not_lit.toNat off_v.toNat
                            (q + 2#64).toNat (p.toNat + 2) end_v.toNat := by
                          simpa only [sem2, wstk2, show (1 : BitVec 64) = 1#64 from rfl,
                            show (2 : BitVec 64) = 2#64 from rfl, hq1_n, hoth_mask, hp2_n]
                            using hkeep
                        have hcv2 : sem2.core.cur_vars = sem1.core.cur_vars := rfl
                        have hcl2 : sem2.core.cur_level = sem.core.cur_level := hcl1
                        have haren2 := hpi2.len.core_ok.arena_len_arr
                        have hvals2 := hpi2.len.core_ok.vals_len
                        have hlvl2 := hpi2.len.core_ok.lvl_len
                        have hcr_ref2 : cref0.toNat ∈ fullArenaClauseRefsCore sem2.core :=
                          hcr_ref1
                        have hng2 : fullArenaClauseGarbCore sem2.core cref0.toNat = false := hng1
                        have hfit2 : cref0.toNat + 3 +
                            fullArenaClauseSizeCore sem2.core cref0.toNat ≤
                            sem2.core.arena_len := hfit1
                        have hnl_eq : sem2.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl := by
                          rw [show sem2.core.lvl = sem.core.lvl from hlvq1]; exact hnl
                        have hte_lt2 : sem2.core.trail_end < sem2.core.cur_vars :=
                          m7_trail_end_lt_of_unassigned hpi2.nw (hcv2 ▸ hoth_lt) hov_un
                        fid_hsteps_nogrp
                        refine wp_join_group (ts := [i32]) (fun (alvlp, ()) mal =>
                            (FullMem c (fastPropMem s_disk sem2) ⋆ R) mal ∧
                            (∀ l ∈ fullArenaClauseLitsCore sem2.core cref0.toNat,
                              l ≠ other.toNat →
                              (sem2.core.lvl[l / 2]?.getD 0#32).toNat ≤ alvlp.toNat) ∧
                            (alvlp = 0#32 ∨ ∃ l ∈ fullArenaClauseLitsCore sem2.core cref0.toNat,
                              l ≠ other.toNat ∧ alvlp = sem2.core.lvl[l / 2]?.getD 0#32)) ?_ ?_
                        · rintro _ ⟨alvlp, ⟨⟩⟩ mal ⟨hmal, hmax_ge, hmax_att⟩
                          fid_hsteps_nogrp
                          have hoth_m : (other.setWidth 64).toNat <
                              (fastPropMem s_disk sem2).core.vals.length := by
                            rw [fastPropMem_vals, hvals2, bv_c0_zext32_64]; omega
                          refine wp_store_sep
                            (FullArenaTactics.c0_store_full_vals ((1#32).setWidth 8) hoth_m hmal)
                            ?_
                          intro mv1 hmv1; clear hmal; dsimp only at hmv1
                          rw [bv_c0_zext32_64, fastPropMem_vals,
                            show BitVec.setWidth 8 (1#32) = 1#8 from rfl,
                            m7_fastPropMem_with_vals] at hmv1
                          fid_hsteps_nogrp
                          have hnoth_m : ((other ^^^ 1#32).setWidth 64).toNat <
                              (fastPropMem s_disk { sem2 with core :=
                                { sem2.core with vals :=
                                  sem2.core.vals.set other.toNat 1#8 } }).core.vals.length := by
                            rw [fastPropMem_vals, List.length_set, hvals2, bv_c0_zext32_64,
                              BitVec.toNat_xor, show (1#32 : BitVec 32).toNat = 1 from rfl,
                              fc_nat_xor_one]
                            split <;> omega
                          refine wp_store_sep
                            (FullArenaTactics.c0_store_full_vals ((-1#32).setWidth 8) hnoth_m
                              hmv1) ?_
                          intro mv2 hmv2; clear hmv1; dsimp only at hmv2
                          have hnoth_n : ((other ^^^ 1#32).setWidth 64).toNat =
                              other.toNat ^^^ 1 := by
                            rw [bv_c0_zext32_64, BitVec.toNat_xor]; rfl
                          have hm1_8 : (-1#32 : BitVec 32).setWidth 8 = 0xFF#8 := by decide
                          rw [show (1 : BitVec 32) = 1#32 from rfl, hoth_hm_eq, hnoth_n, hm1_8,
                            fastPropMem_vals, m7_fastPropMem_with_vals] at hmv2
                          let vals' :=
                            (sem2.core.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
                          have hvals'_len : vals'.length = 2 * c.max_vars := by
                            simp [vals', List.length_set, hvals2]
                          fid_hsteps_nogrp
                          simp only [hoth_hm_eq]
                          refine fid_lp_assign_tail_wp hmaxv hpi2.len hvals'_len hte_lt2
                            (hte_eq.trans hte1.symm) (hcv2 ▸ hoth_lt) (hcv2 ▸ hnot1)
                            (m7_bv32_rshift1_toNat other)
                            (by simpa only [← m7_fastPropMem_with_vals] using hmv2) ?_
                          intro flags' ph' un_n uf_n m' hfl' hph' _rsn_val sem_n hm'
                          have hstep := m7_large_assign_step hpi2 hfl' hph' hcr_lt hcr_ref2 hng2
                            (hcv2 ▸ hnot1) (hcv2 ▸ hoth_lt) hov_un hnot_mem hoth_mem hunit
                            hnl_eq hmax_ge hmax_att (unas' := un_n) (unfl' := uf_n)
                          have hte1_n : (te + 1#64).toNat = sem2.core.trail_end + 1 :=
                            (m7_bv64_add1_toNat (by
                              rw [hte_eq, ← hte1]
                              exact Nat.lt_of_le_of_lt hte_lt2 (Nat.lt_of_le_of_lt
                                (Nat.le_trans hpi2.len.core_ok.cur_vars_le (Nat.le_of_lt hmaxv))
                                (by decide)))).trans
                              (congrArg (· + 1) (hte_eq.trans hte1.symm))
                          have hte_le_inc : sem.core.trail_end ≤ sem2.core.trail_end + 1 := by
                            rw [← hte1]; exact Nat.le_succ _
                          have hq2_n' : (q + (2 : BitVec 64)).toNat = q.toNat + 2 := hq2_n
                          have hinv_n := hstep.1
                          rw [hq2_n] at hinv_n
                          exact hJ_lp' (sem' := sem_n)
                            (by rw [hq2_n', hp2_n']; exact hinv_n)
                            (by rw [hp2_n']; omega)
                            (by rw [hp2_n']; omega) hte_le_inc
                            (hte1_n.trans rfl) rfl rfl hoom1 hct1 hm'
                        · intro J_alvl hJ_alvl
                          fid_hsplit
                          · simp only [hoth_hm_eq]
                            exact m7_lp_max_lvl_wp har (hp2_n ▸ hpi2) hcr_ref2 hng2 hfit2 hcbase_n
                              hcsz64' hm fun alvl hmg hma => hJ_alvl (alvl, ()) _ ⟨hm, hmg, hma⟩
                          · have hge_cl : nl_lvl.ult
                                (BitVec.ofNat 32 sem2.core.cur_level) = false := by
                              rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, Nat.not_lt,
                                hcl2, ← hcur_lvl]
                              exact Nat.le_of_not_lt hc
                            have hnf := m7_nonchrono_alvl_facts hpi2.nw hcr_ref2 hng2
                              hpi2.not_f hov_un hnot_mem hunit hnl_eq hge_cl (hcl2 ▸ hcl32)
                            fid_hsteps
                            exact hJ_alvl (nl_lvl, ()) _ ⟨hm, hnf.1, hnf.2⟩
                · intro J_r2 hJ_r2
                  fid_hsplit
                  · fid_hsteps
                    exact hJ_r2 (ri1, repl1, found1, ()) _ ⟨hmr1, by
                      rcases hr1 with ⟨rfl, hri_ge, hr_lt, hrep⟩ | ⟨hf, -⟩
                      · exact Or.inl ⟨rfl, le_trans hst2 hri_ge, hr_lt, hrep⟩
                      · exact absurd hc (by rw [hf]; decide)⟩
                  · have hf1 : found1 = false := by revert hc; cases found1 <;> simp
                    rcases hr1 with ⟨hf, -⟩ | ⟨-, hbad_hi⟩
                    · exact absurd (hf1.symm.trans hf) (by decide)
                    · refine wp_join_group (fun (wri, wrepl, wf, ()) mw =>
                          (FullMem c (fastPropMem s_disk sem1) ⋆ R) mw ∧
                          ReplOk wri wrepl wf) ?_ ?_
                      · rintro _ ⟨wri, wrepl, wf, ⟨⟩⟩ mw ⟨hmw, hwr⟩
                        fid_hsteps; exact hJ_r2 (wri, wrepl, wf, ()) mw ⟨hmw, hwr⟩
                      · intro J_w hJ_w
                        refine m7_lp_repl_scan_arg_wp har (hp2_n ▸ hpi1) hcr_ref1 hng1 hfit1
                          hcbase_n (le_of_lt hst_lt) (by change 2 ≤ st.toNat; exact hst2) hf1 hmr1
                          fun ri_w repl_w found_w hres => ?_
                        refine hJ_w (ri_w, repl_w, found_w, ()) _ ⟨hmr1, ?_⟩
                        rcases hres with ⟨rfl, hri2, hr_lt, hrep⟩ | ⟨rfl, -, -, hbad_lo⟩
                        · exact Or.inl ⟨rfl, hri2, Nat.lt_trans hr_lt hst_lt, hrep⟩
                        · refine Or.inr ⟨rfl, fun k hk2 hkc => ?_⟩
                          by_cases hkst : k < st.toNat
                          · exact hbad_lo k hk2 hkst
                          · exact hbad_hi k (Nat.le_of_not_lt hkst) hkc
              · intro J_r1 hJ_r1
                refine m7_lp_repl_scan_arg_wp har (hp2_n ▸ hpi1) hcr_ref1 hng1 hfit1 hcbase_n
                  (by simpa only [hcsz64'] using Nat.le_refl _)
                  (by simp only [Arg.val]; simpa only [hcsz64'] using Nat.le_of_lt hst_lt)
                  rfl hmst fun ri1 repl1 found1 hres => ?_
                refine hJ_r1 (ri1, repl1, found1, ()) _ ⟨hmst, ?_⟩
                rcases hres with ⟨rfl, hst_ri, hr_lt, hrep⟩ | ⟨rfl, -, -, hbad_hi⟩
                · exact Or.inl ⟨rfl, hst_ri, by rwa [← hcsz64], hrep⟩
                · exact Or.inr ⟨rfl, fun k hk1 hkc =>
                    hbad_hi k hk1 (by simpa only [← hcsz64'] using hkc)⟩
            · intro J_st hJ_st
              have hcsz3_1 : (2#64 : BitVec 64).toNat <
                  fullArenaClauseSizeCore sem1.core cref0.toNat :=
                hcsz1 ▸ Nat.lt_of_lt_of_le (by decide) hcsz3
              fid_hsplit
              · fid_hsteps
                exact hJ_st (2#64, ()) _ ⟨by decide, hcsz3_1, hmsw⟩
              · fid_hsplit
                · fid_hsteps
                  exact hJ_st (2#64, ()) _ ⟨by decide, hcsz3_1, hmsw⟩
                · have hpos2 : 2 ≤ (pos32.setWidth 64).toNat := by
                    rename_i hc1; exact Nat.le_of_not_lt hc1
                  have hpos_lt : (pos32.setWidth 64).toNat <
                      fullArenaClauseSizeCore sem1.core cref0.toNat := by
                    rw [← hcsz64']; exact Nat.lt_of_not_le hc
                  fid_hsteps
                  exact hJ_st (pos32.setWidth 64, ()) _ ⟨hpos2, hpos_lt, hmsw⟩
        · intro J_sw hJ_sw
          fid_hsplit
          · have hl0_eq_not : l0 = not_lit := by rw [← hl0_hc]; exact hc
            have hoth_l1 : other = l1 := by dsimp only [other]; rw [hl0_eq_not, fid_xor_cancel_l]
            have hsw01 := fastProp_js3_swap hpi_drop hcr_ref hng0 hcsz3 hcr_fit
              (hl0_eq.symm.trans hl0_eq_not) hl1_eq.symm
            fid_hsteps
            have hcr3_raw : cref0.toNat + 3 < sem.core.arena.length := by rw [haren_len]; omega
            have hcr4_raw : cref0.toNat + 4 < sem.core.arena.length := by rw [haren_len]; omega
            have hoth_val_eq :
                (lift2 (fun {n} (x1 x2 : BitVec n) => x1 ^^^ x2) (fun x1 x2 => x1 ^^ x2) i32
                  (Arg.var (lift2 (fun {n} (x1 x2 : BitVec n) => x1 ^^^ x2)
                    (fun x1 x2 => x1 ^^ x2) i32
                    (Arg.var (sem.core.arena[cref0.toNat + 3]'hcr3_raw)).val
                    (Arg.var (sem.core.arena[cref0.toNat + 4]'hcr4_raw)).val, ()).fst).val
                  (Arg.var not_lit).val : BitVec 32) = l1 := by
              change ((_ ^^^ _) ^^^ not_lit) = l1
              rw [show sem.core.arena[cref0.toNat + 3]'hcr3_raw = l0 from hl0_eq.symm,
                show sem.core.arena[cref0.toNat + 4]'hcr4_raw = l1 from hl1_eq.symm,
                hl0_eq_not]
              dsimp only [Arg.val]
              exact fid_xor_cancel_l not_lit l1
            simp only [fastPropMem_arena, fastPropMem_with_arena,
              show (3 : BitVec 64) = 3#64 from rfl, show (1 : BitVec 64) = 1#64 from rfl,
              hcbase1_n, hcbase_n, hoth_val_eq] at hm
            exact hJ_sw () m ⟨_, hsw01.1, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
              hsw01.2.1, hsw01.2.2.1, hsw01.2.2.2.1, hoth_l1 ▸ hsw01.2.2.2.2.1,
              hsw01.2.2.2.2.2, rfl, hm⟩
          · have hl0_ne : l0 ≠ not_lit := by rw [← hl0_hc]; exact hc
            have hl1_eq_not : l1 = not_lit := hwatch.resolve_left hl0_ne
            have hoth_l0 : other = l0 := by dsimp only [other]; rw [hl1_eq_not, fid_xor_cancel_r]
            fid_hsteps
            exact hJ_sw () mchk ⟨sem, hpi_drop, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hcr_ref, hng0,
              rfl, hoth_l0 ▸ hl0_get, hl1_eq_not ▸ hl1_get, rfl, hm⟩
      · intro J_chk hJ_chk
        fid_hsplit
        · fid_hsplit
          · have hpi_d := propLit_inv_drop (ticks' := sem.scratch.search_ticks) hpi hsw_drop hp2_n11
            rw [hp2_n11, ← hp2_n', hsem_sc] at hpi_d
            fid_hsteps
            exact hJ_lp' hpi_d (by rw [hp2_n']; omega) (by rw [hp2_n']; omega) (Nat.le_refl _)
              hte_eq hun_eq huf_eq rfl rfl hm
          · have hl1_eq : l1 = not_lit := by simpa only [hl1_hc] using hc
            fid_hsteps
            exact hJ_chk () mc ⟨hm, Or.inr hl1_eq⟩
        · have hl0_eq : l0 = not_lit := by simpa only [hl0_hc] using hc
          fid_hsteps
          exact hJ_chk () mc ⟨hm, Or.inl hl0_eq⟩
  · intro J_c hJ_c
    fid_hsplit
    · have hw0_lt : w0.toNat < 2 * sem.core.cur_vars := by rw [htwo_cv] at hc; exact hc
      have hw0_vals_m : (w0.setWidth 64).toNat < (fastPropMem s_disk sem).core.vals.length := by
        rw [fastPropMem_vals, hvals_len, bv_c0_zext32_64]; omega
      let vw := (fastPropMem s_disk sem).core.vals[(w0.setWidth 64).toNat]'hw0_vals_m
      fid_hsplit
      · fid_hsteps_nogrp
        simp only [fastPropMem_wstk, fastPropMem_with_wstk, hcr_eq_raw] at hm
        have hkeep := propLit_inv_keep_large hpi hsw_drop hnot_lt hq1_n hq2_n hp2_n11
          (Nat.add_le_add_right hq_le 2) h2_le_end hflag hcr_lt hcr_ref
        have hp2_n'' : (p + (1 : BitVec 64) + (1 : BitVec 64)).toNat = p.toNat + 2 := hp2_n11
        rw [hp2_n'', ← hp2_n'] at hkeep
        fid_hsteps
        exact hJ_lp' hkeep (by rw [hp2_n']; omega) (by rw [hp2_n']; omega) (Nat.le_refl _) hte_eq
          hun_eq huf_eq rfl rfl hm
      · fid_hsteps; exact hJ_c () m hm
    · fid_hsteps; exact hJ_c () m hm

end LeanQbe.T.Examples.Kissat.FullFidelityBcp
