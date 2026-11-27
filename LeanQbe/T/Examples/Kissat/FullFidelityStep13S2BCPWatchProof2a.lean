/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S2BCPWatchProof1
public import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof2d

/-!
# Kissat Fidelity Step 13 Shard S2-A Inner Loop — Part 2a (`FullFidelityStep13S2BCPWatchProof2a`)

Plain `public section` (`0` `@[expose]`, `0` `import all`, `<= 100` cols, every theorem `<= 320`
lines):
1. `s13_lp_no_repl_wp`: no-replacement tail (`wstk[q] = w0`, `cref == ignore_ref`, `isBeyond`
   conflict skip, non-chronological `alvl`, unit assign).
2. `s13_lp_scan_wp`: two-pass replacement scan + `repl` store / `s13_lp_repl_del_wp` /
   `s13_lp_no_repl_wp`.
3. `s13_lp_large_step_wp`: unswapped `[l0, l1]` large-clause watch step.
4. `s13_lp_loop_wp`: parameterized inner `while (p < end)` watch loop (`isBeyond : Bool`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S2

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FastCore
open LeanQbe.T.Examples.Kissat.FullM5Otfs
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM7BcpHot
open LeanQbe.T.Examples.Kissat.FullFidelityBcp
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeHelpers
open LeanQbe.T.Examples.Kissat.Full.FullPropDecSpecs hiding
  fullWatchPushSpec fullPropLitSpec fullPropagateIgnoreSpec fullPropagateSpec
  FullTrailExt FullArenaPermEq
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

attribute [local irreducible] fastPropMem

local macro "s13_hsteps" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps))

local macro "s13_hsteps_nogrp" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps_nogrp))

local macro "s13_hsplit" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsplit))

private theorem s13_bv8_sgt0_iff (x : BitVec 8) :
    (0#32).slt (BitVec.signExtend 32 x) = decide ((BitVec.signExtend 32 x).toInt > 0) := by
  rw [BitVec.slt_eq_decide, show (0#32 : BitVec 32).toInt = 0 from by decide]

private theorem s13_bv8_slt0_iff (x : BitVec 8) :
    (BitVec.signExtend 32 x).slt 0#32 = decide ((BitVec.signExtend 32 x).toInt < 0) := by
  rw [BitVec.slt_eq_decide, show (0#32 : BitVec 32).toInt = 0 from by decide]

/-! ## 0. Delayed-Buffer Replacement Step (`s13_lp_repl_del_wp`) -/

/-- Unswapped delayed-buffer push step (`l0 = not_lit ∨ l1 = not_lit`). -/
theorem s13_lp_repl_del_wp {Γ : Env} {rs : List Ty} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s_orig s_disk sem1 : FullState}
    {l0 l1 not_lit other cref repl : BitVec 32}
    {te un uf tk' p_v q end_v p2 off_v di dlim brk0 cbase ri : BitVec 64} {dlen : Nat}
    {isBeyond : Bool} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    {J_ovf : Cont (s13OvfSig isBeyond)}
    {J_lp : Cont [i64, i64, i64, i64, i64, i64, i64]}
    (har : c.arena_cap < 2 * dimacsBound)
    (hpi1 : PropLitInv c F0 F_cur
      { s_orig with scratch := { s_orig.scratch with delayed := sem1.scratch.delayed } } sem1
      not_lit.toNat off_v.toNat q.toNat (p_v.toNat + 2) end_v.toNat)
    (hcr_lt : cref.toNat < 0x80000000)
    (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore sem1.core)
    (hng1 : fullArenaClauseGarbCore sem1.core cref.toNat = false)
    (hfit : cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤ sem1.core.arena_len)
    (har3 : sem1.core.arena[cref.toNat + 3]? = some l0)
    (har4 : sem1.core.arena[cref.toNat + 4]? = some l1)
    (hwatch : l0 = not_lit ∨ l1 = not_lit)
    (hoth_eq : other = l0 ^^^ l1 ^^^ not_lit)
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
      wp Γ Q X (s13OvfJump isBeyond J_ovf (.var te) (.var un) (.var uf) (.var tk') (.var p2)
        (.var q) (.var di) (.var brk0) (.imm true) (.var repl) (.var other) (.var cref)
        (.var ri)) m_o)
    (hJ_lp : ∀ (sem4 : FullState) (di' : BitVec 64) (dlen' : Nat) (m_l : Mem 64),
      PropLitInv c F0 F_cur
        { s_orig with scratch := { s_orig.scratch with delayed := sem4.scratch.delayed } } sem4
        not_lit.toNat off_v.toNat q.toNat (p_v.toNat + 2) end_v.toNat →
      di'.toNat = 3 * dlen' → dlen' ≤ c.delayed_cap →
      DelayedWatchesOk s_orig.core sem4.scratch.delayed dlen' not_lit.toNat →
      (c.delayed_cap = 0 → sem4.scratch.delayed = sem1.scratch.delayed) →
      sem4.core.oom = sem1.core.oom → S13ConflEq sem1.core sem4.core →
      sem4.core.trail_end = sem1.core.trail_end →
      sem4.core.unassigned = sem1.core.unassigned → sem4.core.unflushed = sem1.core.unflushed →
      (FullMem c (fastPropMem s_disk sem4) ⋆ R) m_l →
      wp Γ Q X (.jump J_lp (.var te, (.var un, (.var uf, (.var tk', (.var p2, (.var q,
        (.var di', ())))))))) m_l) :
    wp Γ Q X (s13LpReplDelExpr isBeyond c.pWstk c.pArena c.pDelayed dlim not_lit other cref
      te un uf tk' p2 q di brk0 cbase ri repl J_ovf J_lp) m := by
  unfold dimacsBound at har
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv := hpi1.len.core_ok.cur_vars_le
  have haren1 := hpi1.len.core_ok.arena_len_arr
  have halen1 := hpi1.len.core_ok.arena_len_le
  have hdel_len := hpi1.len.scratch_ok.delayed_len_arr
  have hcsz3 : 3 ≤ fullArenaClauseSizeCore sem1.core cref.toNat :=
    (hpi1.nw.arena.refs_wf cref.toNat hcr_ref).2.1
  have hc0_n : cbase.toNat = cref.toNat + 3 := hcbase
  have hc1_n : (cbase + 1#64).toNat = cref.toNat + 4 :=
    (m7_bv64_add1_toNat (by rw [hc0_n]; omega)).trans (by rw [hc0_n])
  have hcri_n : (cbase + ri).toNat = cref.toNat + 3 + ri.toNat :=
    (m7_bv64_add_toNat (by rw [hc0_n]; omega)).trans (by rw [hc0_n])
  have h0_lt : cref.toNat + 3 < c.arena_cap := by omega
  have h1_lt : cref.toNat + 4 < c.arena_cap := by omega
  have hri_lt_cap : cref.toNat + 3 + ri.toNat < c.arena_cap := by omega
  have hoth_flag : (other &&& 0x80000000#32) = 0#32 := by
    rw [← m7_bv32_mask7f_eq (by omega : other.toNat < 2 ^ 31), BitVec.and_assoc,
      show (0x7FFFFFFF#32 &&& 0x80000000#32 : BitVec 32) = 0#32 from rfl, BitVec.and_zero]
  unfold s13LpReplDelExpr
  refine wp_join_group (fun x mj => ∃ (sem4 : FullState) (dlen' : Nat),
      x.1 = q ∧ x.2.1.toNat = 3 * dlen' ∧
      PropLitInv c F0 F_cur
        { s_orig with scratch := { s_orig.scratch with delayed := sem4.scratch.delayed } } sem4
        not_lit.toNat off_v.toNat q.toNat (p_v.toNat + 2) end_v.toNat ∧
      dlen' ≤ c.delayed_cap ∧
      DelayedWatchesOk s_orig.core sem4.scratch.delayed dlen' not_lit.toNat ∧
      (c.delayed_cap = 0 → sem4.scratch.delayed = sem1.scratch.delayed) ∧
      sem4.core.oom = sem1.core.oom ∧ S13ConflEq sem1.core sem4.core ∧
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
    s13_hsplit
    · exact absurd (congrArg BitVec.toNat hc) hrepl_ne
    · s13_hsplit
      · have hdlen_lt : dlen < c.delayed_cap := by
          have hlt : di.toNat < dlim.toNat := hc
          omega
        have hdi1_n : (di + 1).toNat = 3 * dlen + 1 := by
          rw [BitVec.toNat_add, hdi, show (1 : BitVec 64).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (by have := c.hdel; unfold dimacsBound at this; omega)]
        have hdi2_n : (di + 2).toNat = 3 * dlen + 2 := by
          rw [BitVec.toNat_add, hdi, show (2 : BitVec 64).toNat = 2 from rfl,
            Nat.mod_eq_of_lt (by have := c.hdel; unfold dimacsBound at this; omega)]
        have hdi3_n : (di + 3).toNat = 3 * (dlen + 1) := by
          rw [BitVec.toNat_add, hdi, show (3 : BitVec 64).toNat = 3 from rfl,
            Nat.mod_eq_of_lt (by have := c.hdel; unfold dimacsBound at this; omega)]; omega
        let ar3 := ((sem1.core.arena.set (cref.toNat + 3) other).set (cref.toNat + 4) repl).set
          (cref.toNat + 3 + ri.toNat) not_lit
        let st3 : FullState := { sem1 with core := { sem1.core with arena := ar3 } }
        have hsw := s13_ar_swap_nw hpi1.len.core_ok hpi1.nw hcr_ref hng1 hcsz3 hri2 hri_lt hfit har3
          har4 hwatch har_ri
        rw [← hoth_eq] at hsw
        have hlen3 : st3.LengthsOk c :=
          ⟨{ hpi1.len.core_ok with arena_len_arr := by simp [st3, ar3, haren1] },
           hpi1.len.scratch_ok⟩
        have hsw3 : SplitWatchesInv F_cur st3.core not_lit.toNat off_v.toNat q.toNat
            (p_v.toNat + 2) end_v.toNat :=
          hpi1.sw.with_nonwatch rfl rfl rfl rfl hsw.2.1.1
        have ⟨hpi4, hdok4⟩ := fid_repl_delay_step hpi1 (st3 := st3) rfl rfl hlen3 hsw.1 hsw3 hsw.2.1
          hcr_lt hcr_ref hrepl_lt hrepl_ne hoth_flag hdok hdlen_lt
        refine fid_lp_ar_swap_wp haren1 hc0_n hc1_n hcri_n h0_lt h1_lt hri_lt_cap hm ?_
        intro m3 ar3' hm3
        have hm_del_len : (fastPropMem s_disk st3).scratch.delayed.length = 3 * c.delayed_cap := by
          rw [fastPropMem_delayed]; exact hdel_len
        s13_hsteps_nogrp
        refine wp_store_sep (FullArenaTactics.c0_store_full_delayed repl
          (by rw [hm_del_len, hdi]; omega) hm3) ?_
        intro md1 hmd1; clear hm3; dsimp only at hmd1
        rw [fastPropMem_delayed, fastPropMem_with_delayed, hdi] at hmd1
        s13_hsteps_nogrp
        refine wp_store_sep (FullArenaTactics.c0_store_full_delayed other
          (by rw [fastPropMem_delayed, List.length_set, hdel_len, hdi1_n]; omega) hmd1) ?_
        intro md2 hmd2; clear hmd1; dsimp only at hmd2
        rw [fastPropMem_delayed, fastPropMem_with_delayed, hdi1_n] at hmd2
        s13_hsteps_nogrp
        refine wp_store_sep (FullArenaTactics.c0_store_full_delayed cref
          (by rw [fastPropMem_delayed, List.length_set, List.length_set, hdel_len, hdi2_n]; omega)
          hmd2) ?_
        intro md3 hmd3; clear hmd2; dsimp only at hmd3
        rw [fastPropMem_delayed, fastPropMem_with_delayed, hdi2_n] at hmd3
        s13_hsteps
        let del4 : List (BitVec 32) :=
          ((sem1.scratch.delayed.set (3 * dlen) repl).set (3 * dlen + 1) other).set
            (3 * dlen + 2) cref
        exact hJret _ _ ⟨{ st3 with scratch := { st3.scratch with delayed := del4 } },
          dlen + 1, rfl, hdi3_n, hpi4, by omega, hdok4,
          fun hc0 => absurd hc0 (by omega), rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, hmd3⟩
      · cases isBeyond <;> (s13_hsteps; exact hJ_ovf m hm)

/-! ## 1. No-Replacement Tail (`s13_lp_no_repl_wp`) -/

theorem s13_lp_no_repl_wp {Γ : Env} {rs : List Ty} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s_orig s_disk sem : FullState}
    {cur_lvl32 not_lit nl_lvl w0 l0 l1 cref : BitVec 32} {ov : BitVec 8}
    {te un uf tk1 p_v q end_v p2 off_v di cbase csz : BitVec 64}
    {ignore_ref : Arg Val i64} {ign_v : BitVec 64}
    {isBeyond rec_ph bigbig : Bool} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    {J_ovf : Cont (s13OvfSig isBeyond)}
    {J_lp : Cont [i64, i64, i64, i64, i64, i64, i64]}
    (hmaxv : c.max_vars < 2 * dimacsBound) (har : c.arena_cap < 2 * dimacsBound)
    (hwc : c.wcap < 2 * dimacsBound)
    (hign_val : ignore_ref.val = ign_v)
    (hpi : PropLitInv c F0 F_cur
      { s_orig with scratch := { s_orig.scratch with delayed := sem.scratch.delayed } } sem
      not_lit.toNat off_v.toNat q.toNat (p_v.toNat + 2) end_v.toNat)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (hcur_lvl : cur_lvl32 = BitVec.ofNat 32 sem.core.cur_level)
    (hcl32 : sem.core.cur_level < 2 ^ 32)
    (hw0_flag : (w0 &&& 0x80000000#32) = 0#32)
    (hq_le : q.toNat ≤ p_v.toNat) (hp2_le : p_v.toNat + 2 ≤ end_v.toNat)
    (hp2_n : (p_v + 2#64).toNat = p_v.toNat + 2)
    (hp2_n11 : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2)
    (hq1_n : (q + 1#64).toNat = q.toNat + 1) (hq2_n : (q + 2#64).toNat = q.toNat + 2)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore sem.core)
    (hng : fullArenaClauseGarbCore sem.core cref.toNat = false)
    (hfit : cref.toNat + 3 + fullArenaClauseSizeCore sem.core cref.toNat ≤ sem.core.arena_len)
    (har3 : sem.core.arena[cref.toNat + 3]? = some l0)
    (har4 : sem.core.arena[cref.toNat + 4]? = some l1)
    (hwatch : l0 = not_lit ∨ l1 = not_lit)
    (hoth_lt : (l0 ^^^ l1 ^^^ not_lit).toNat < 2 * sem.core.cur_vars)
    (hov_nsgt : (0#32).slt (BitVec.signExtend 32 ov) = false)
    (hov_eq : ov = sem.core.vals[(l0 ^^^ l1 ^^^ not_lit).toNat]?.getD 0#8)
    (hbad_all : ∀ k, 2 ≤ k → k < fullArenaClauseSizeCore sem.core cref.toNat →
      fullFindReplBad sem cref.toNat k)
    (hcbase : cbase.toNat = cref.toNat + 3)
    (hcsz : csz.toNat = fullArenaClauseSizeCore sem.core cref.toNat)
    (hte_eq : te.toNat = sem.core.trail_end) (hun_eq : un = sem.core.unassigned)
    (huf_eq : uf = sem.core.unflushed) (hoom : sem.core.oom = 0#64)
    (hnl : sem.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl)
    (_hp2_v : p2 = p_v + 2#64)
    (hm : (FullMem c (fastPropMem s_disk sem) ⋆ R) m)
    (hJ_ovf : isBeyond = false → ∀ {sem' : FullState} {q' brk' : BitVec 64} {m' : Mem 64},
      PropLitInv c F0 F_cur
        { s_orig with scratch := { s_orig.scratch with delayed := sem.scratch.delayed } } sem'
        not_lit.toNat off_v.toNat q'.toNat (p_v.toNat + 2) end_v.toNat →
      te.toNat = sem'.core.trail_end → sem'.core.oom = 0#64 →
      sem'.core.unassigned = sem.core.unassigned → sem'.core.unflushed = sem.core.unflushed →
      brk' = 1#64 → PropLitConfl F_cur ign_v sem'.core →
      (FullMem c (fastPropMem s_disk sem') ⋆ R) m' →
      wp Γ Q X (s13OvfJump isBeyond J_ovf (.var te) (.var un) (.var uf) (.var tk1) (.var p2)
        (.var q') (.var di) (.var brk') (.imm false) (.imm 0#32) (.imm 0#32) (.imm 0#32)
        (.imm 0#64)) m')
    (hJ_lp : ∀ {sem' : FullState} {te' un' uf' tk' q' : BitVec 64} {m' : Mem 64},
      PropLitInv c F0 F_cur
        { s_orig with scratch := { s_orig.scratch with delayed := sem.scratch.delayed } } sem'
        not_lit.toNat off_v.toNat q'.toNat (p_v.toNat + 2) end_v.toNat →
      sem.core.trail_end ≤ sem'.core.trail_end →
      te'.toNat = sem'.core.trail_end → un' = sem'.core.unassigned → uf' = sem'.core.unflushed →
      sem'.core.oom = sem.core.oom → S13ConflEq sem.core sem'.core →
      (FullMem c (fastPropMem s_disk sem') ⋆ R) m' →
      wp Γ Q X (.jump J_lp (.var te', (.var un', (.var uf', (.var tk', (.var p2, (.var q',
        (.var di, ())))))))) m') :
    wp Γ Q X (s13LpNoReplExpr isBeyond c.hdr c.pVals c.pWstk c.pArena c.pLevel c.pReason c.pTrail
      c.pTrailPos c.pFlags c.pPhases ignore_ref cur_lvl32 not_lit nl_lvl w0
      (l0 ^^^ l1 ^^^ not_lit) cref ov rec_ph bigbig te un uf tk1 p2 q di cbase csz J_ovf J_lp)
      m := by
  unfold dimacsBound at hmaxv har hwc
  let other := l0 ^^^ l1 ^^^ not_lit
  have hcv := hpi.len.core_ok.cur_vars_le
  have haren := hpi.len.core_ok.arena_len_arr
  have halen := hpi.len.core_ok.arena_len_le
  have hvals := hpi.len.core_ok.vals_len
  have hlvl := hpi.len.core_ok.lvl_len
  have hwstk := hpi.len.core_ok.wstk_len_arr
  have ⟨hend_le, hwlen_le⟩ := hpi.end_lt_wcap hnot_lt
  have hwc64 : c.wcap + 2 < 2 ^ 64 := Nat.lt_trans (Nat.add_lt_add_right hwc 2) (by decide)
  have hq_ws : q.toNat < (fastPropMem s_disk sem).core.wstk.length := by
    rw [fastPropMem_wstk, hwstk]; omega
  have hq1_ws : (q + 1#64).toNat < (fastPropMem s_disk sem).core.wstk.length := by
    rw [fastPropMem_wstk, hwstk, hq1_n]; omega
  let wstk2 := (sem.core.wstk.set q.toNat w0).set (q + 1#64).toNat cref
  let sem2 : FullState := { sem with core := { sem.core with wstk := wstk2 } }
  have hsw_drop : SplitWatchesInv F_cur sem.core not_lit.toNat off_v.toNat q.toNat
      (p_v.toNat + 2) end_v.toNat := hpi.sw
  have hkeep := propLit_inv_keep_large hpi hsw_drop hnot_lt hq1_n hq2_n hp2_n11
    (Nat.add_le_add_right hq_le 2) hpi.sw.p_le_end hw0_flag hcr_lt hcr_ref
  have hbd_ar : cref.toNat + 3 + fullArenaClauseSizeCore sem.core cref.toNat ≤
      sem.core.arena.length := haren ▸ Nat.le_trans hfit halen
  have hunit_sem : ∀ l ∈ fullArenaClauseLitsCore sem.core cref.toNat,
      l = other.toNat ∨ sem.core.vals[l]?.getD 0#8 = 0xFF#8 :=
    s13_clause_falsified_of_find_repl_none hpi.nw hcr_ref hng hbd_ar har3 har4 hwatch hpi.not_f
      hbad_all
  unfold s13LpNoReplExpr
  c0_hstraight
  have hm2 : (FullMem c (fastPropMem s_disk sem2) ⋆ R) m := by
    simpa only [sem2, wstk2, fastPropMem_wstk, fastPropMem_with_wstk,
      show (q + (1 : BitVec 64)).toNat = (q + 1#64).toNat from rfl] using hm
  clear hm
  have hpi2 : PropLitInv c F0 F_cur
      { s_orig with scratch := { s_orig.scratch with delayed := sem.scratch.delayed } } sem2
      not_lit.toNat off_v.toNat (q + 2#64).toNat (p_v.toNat + 2) end_v.toNat := by
    simpa only [sem2, wstk2, hq1_n, hq2_n, hp2_n11,
      show q + (1 : BitVec 64) = q + 1#64 from rfl,
      show q + (2 : BitVec 64) = q + 2#64 from rfl,
      show p_v + (1 : BitVec 64) + (1 : BitVec 64) = p_v + 1#64 + 1#64 from rfl] using hkeep
  s13_hsplit
  · s13_hsteps
    exact hJ_lp hpi2 (Nat.le_refl _) hte_eq hun_eq huf_eq rfl ⟨rfl, rfl, rfl, rfl⟩ hm2
  · have hne_ign : cref.setWidth 64 ≠ ign_v := by
      simpa only [hign_val] using hc
    s13_hsplit
    · cases isBeyond with
      | true =>
        s13_hsteps
        exact hJ_lp hpi2 (Nat.le_refl _) hte_eq hun_eq huf_eq rfl ⟨rfl, rfl, rfl, rfl⟩ hm2
      | false =>
        have hov_slt : (BitVec.signExtend 32 ov).slt 0#32 = true := by
          simpa only [show (0 : BitVec 32) = 0#32 from rfl] using hc
        have hov_f : sem.core.vals[other.toNat]?.getD 0#8 = 0xFF#8 :=
          (full_i8_vals_slt0 (hpi.nw.vals_domain other.toNat hoth_lt)).mp (hov_eq ▸ hov_slt)
        have hconfl := s13_large_confl_w0 hpi hnot_lt hq_le hq1_n hq2_n hp2_n11 hw0_flag hcr_lt
          hcr_ref hng hne_ign hov_f hunit_sem
        rw [hp2_n11] at hconfl
        let sem_c : FullState :=
          { sem2 with core := { sem2.core with confl_type := 2#64, confl_ref := cref.setWidth 64 } }
        simp only [Bool.false_eq_true, ↓reduceIte]
        s13_hsteps
        exact hJ_ovf rfl hconfl.1 hte_eq hoom rfl rfl rfl hconfl.2
          (by simpa only [sem_c, sem2, wstk2, fastPropMem, BitVec.ofNat_eq_ofNat,
            show (2 : BitVec 64) = 2#64 from rfl,
            show (q + (1 : BitVec 64)).toNat = (q + 1#64).toNat from rfl] using hm)
    · have hov_nslt : (BitVec.signExtend 32 ov).slt 0#32 = false := hc
      have hoth_lt' : other.toNat < 2 * sem.core.cur_vars := hoth_lt
      have hoth_raw : other.toNat < sem2.core.vals.length := by
        rw [hpi2.len.core_ok.vals_len]; omega
      have hov_un : sem2.core.vals[other.toNat]?.getD 0#8 = 0#8 := by
        refine propLit_vals_un hpi2.nw hoth_lt hoth_raw ?_ ?_
        · rw [List.getElem?_eq_getElem hoth_raw, Option.getD_some] at hov_eq
          change (0#32).slt (BitVec.signExtend 32 (sem.core.vals[other.toNat]'hoth_raw)) = false
          rw [← hov_eq]; exact hov_nsgt
        · rw [List.getElem?_eq_getElem hoth_raw, Option.getD_some] at hov_eq
          change (BitVec.signExtend 32 (sem.core.vals[other.toNat]'hoth_raw)).slt 0#32 = false
          rw [← hov_eq]; exact hov_nslt
      have hcsz3_sem : 3 ≤ fullArenaClauseSizeCore sem.core cref.toNat :=
        (hpi.nw.arena.refs_wf cref.toNat hcr_ref).2.1
      have hoth_mem : other.toNat ∈ fullArenaClauseLitsCore sem2.core cref.toNat := by
        rcases hwatch with rfl | rfl
        · have hoth1 : other = l1 := fid_xor_cancel_l l0 l1
          rw [hoth1]
          exact (mem_fullArenaClauseLitsCore_iff hbd_ar).mpr ⟨1, by omega,
            congrArg BitVec.toNat (Option.some.inj
              ((List.getElem?_eq_getElem (by omega)).symm.trans har4))⟩
        · have hoth0 : other = l0 := fid_xor_cancel_r l0 l1
          rw [hoth0]
          exact (mem_fullArenaClauseLitsCore_iff hbd_ar).mpr ⟨0, by omega,
            congrArg BitVec.toNat (Option.some.inj
              ((List.getElem?_eq_getElem (by omega)).symm.trans har3))⟩
      have hnot_mem : not_lit.toNat ∈ fullArenaClauseLitsCore sem2.core cref.toNat := by
        rcases hwatch with rfl | rfl
        · exact (mem_fullArenaClauseLitsCore_iff hbd_ar).mpr ⟨0, by omega,
            congrArg BitVec.toNat (Option.some.inj
              ((List.getElem?_eq_getElem (by omega)).symm.trans har3))⟩
        · exact (mem_fullArenaClauseLitsCore_iff hbd_ar).mpr ⟨1, by omega,
            congrArg BitVec.toNat (Option.some.inj
              ((List.getElem?_eq_getElem (by omega)).symm.trans har4))⟩
      have hte_lt2 : sem2.core.trail_end < sem2.core.cur_vars :=
        m7_trail_end_lt_of_unassigned hpi2.nw hoth_lt hov_un
      refine wp_join_group (ts := [i32]) (fun (alvlp, ()) mal =>
          (FullMem c (fastPropMem s_disk sem2) ⋆ R) mal ∧
          (∀ l ∈ fullArenaClauseLitsCore sem2.core cref.toNat, l ≠ other.toNat →
            (sem2.core.lvl[l / 2]?.getD 0#32).toNat ≤ alvlp.toNat) ∧
          (alvlp = 0#32 ∨ ∃ l ∈ fullArenaClauseLitsCore sem2.core cref.toNat,
            l ≠ other.toNat ∧ alvlp = sem2.core.lvl[l / 2]?.getD 0#32)) ?_ ?_
      · rintro _ ⟨alvlp, ⟨⟩⟩ mal ⟨hmal, hmax_ge, hmax_att⟩
        s13_hsteps_nogrp
        have hoth_m : (other.setWidth 64).toNat < (fastPropMem s_disk sem2).core.vals.length := by
          rw [fastPropMem_vals, hpi2.len.core_ok.vals_len, bv_c0_zext32_64]; omega
        refine wp_store_sep (FullArenaTactics.c0_store_full_vals ((1#32).setWidth 8) hoth_m hmal) ?_
        intro mv1 hmv1; clear hmal; dsimp only at hmv1
        rw [bv_c0_zext32_64, fastPropMem_vals, show BitVec.setWidth 8 (1#32) = 1#8 from rfl,
          m7_fastPropMem_with_vals] at hmv1
        s13_hsteps_nogrp
        have hnoth_m : ((other ^^^ 1#32).setWidth 64).toNat <
            (fastPropMem s_disk { sem2 with
              core := { sem2.core with vals := sem2.core.vals.set other.toNat 1#8 }
            }).core.vals.length := by
          rw [fastPropMem_vals, List.length_set, hpi2.len.core_ok.vals_len, bv_c0_zext32_64,
            BitVec.toNat_xor, show (1#32 : BitVec 32).toNat = 1 from rfl, fc_nat_xor_one]
          split <;> omega
        refine wp_store_sep
          (FullArenaTactics.c0_store_full_vals ((-1#32).setWidth 8) hnoth_m hmv1) ?_
        intro mv2 hmv2; clear hmv1; dsimp only at hmv2
        have hnoth_n : ((other ^^^ 1#32).setWidth 64).toNat = other.toNat ^^^ 1 := by
          rw [bv_c0_zext32_64, BitVec.toNat_xor]; rfl
        have hm1_8 : (-1#32 : BitVec 32).setWidth 8 = 0xFF#8 := by decide
        rw [show (1 : BitVec 32) = 1#32 from rfl, hnoth_n, hm1_8, fastPropMem_vals,
          m7_fastPropMem_with_vals] at hmv2
        let vals' := (sem2.core.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
        have hvals'_len : vals'.length = 2 * c.max_vars := by
          simp [vals', List.length_set, hpi2.len.core_ok.vals_len]
        s13_hsteps_nogrp
        refine s13_lp_assign_tail_wp hmaxv hpi2.len hvals'_len hte_lt2 hte_eq hoth_lt hnot_lt
          (m7_bv32_rshift1_toNat other) (by simpa only [← m7_fastPropMem_with_vals] using hmv2) ?_
        intro flags' ph' un_n uf_n jr m' hfl' hph' _ _ _ hm'
        let sem_n : FullState :=
          { core :=
              { sem2.core with
                vals := vals', flags := flags',
                lvl := sem2.core.lvl.set (other.toNat / 2) alvlp,
                rsns := sem2.core.rsns.set (other.toNat / 2)
                  (if alvlp = 0#32 then 0xFFFFFFFF#32 else cref),
                trl := sem2.core.trl.set sem2.core.trail_end other,
                trail_pos := sem2.core.trail_pos.set (other.toNat / 2)
                  (BitVec.ofNat 32 sem2.core.trail_end),
                trail_end := sem2.core.trail_end + 1,
                unassigned := un_n, unflushed := uf_n }
            scratch := { sem2.scratch with phases := ph' } }
        have hstep := m7_large_assign_step hpi2 hfl' hph' hcr_lt hcr_ref hng hnot_lt hoth_lt
          hov_un hnot_mem hoth_mem hunit_sem hnl hmax_ge hmax_att (unas' := un_n) (unfl' := uf_n)
        have hte1_n : (te + 1#64).toNat = sem2.core.trail_end + 1 :=
          (m7_bv64_add1_toNat (by
            have hte_s2 : sem2.core.trail_end < sem2.core.cur_vars := hte_lt2
            have hte2_eq : sem2.core.trail_end = sem.core.trail_end := rfl
            have hcv_s2 : sem2.core.cur_vars = sem.core.cur_vars := rfl
            rw [hte_eq, ← hte2_eq]; omega)).trans (congrArg (· + 1) hte_eq)
        have hinv_n := hstep.1
        refine hJ_lp (sem' := sem_n) ?_ (Nat.le_succ _) hte1_n rfl rfl rfl
          ⟨rfl, rfl, rfl, rfl⟩ hm'
        rw [show (q + (2 : BitVec 64)).toNat = (q + 2#64).toNat from rfl]; exact hinv_n
      · intro J_alvl hJ_alvl
        s13_hsplit
        · exact m7_lp_max_lvl_wp har (hp2_n ▸ hpi2)
            (show cref.toNat ∈ fullArenaClauseRefsCore sem2.core from hcr_ref)
            (show fullArenaClauseGarbCore sem2.core cref.toNat = false from hng)
            (show cref.toNat + 3 + fullArenaClauseSizeCore sem2.core cref.toNat ≤
              sem2.core.arena_len from hfit)
            hcbase
            (show csz.toNat = fullArenaClauseSizeCore sem2.core cref.toNat from hcsz)
            hm2 fun alvl hmg hma => hJ_alvl (alvl, ()) _ ⟨hm2, hmg, hma⟩
        · have hge_cl : nl_lvl.ult (BitVec.ofNat 32 sem2.core.cur_level) = false := by
            rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, Nat.not_lt, ← hcur_lvl]
            exact Nat.le_of_not_lt hc
          have hnf := m7_nonchrono_alvl_facts hpi2.nw hcr_ref hng hpi2.not_f hov_un
            hnot_mem hunit_sem hnl hge_cl (by simpa [sem2] using hcl32)
          s13_hsteps
          exact hJ_alvl (nl_lvl, ()) _ ⟨hm2, hnf.1, hnf.2⟩

/-! ## 2. Replacement Scan & Dispatch (`s13_lp_scan_wp`) -/

private theorem s13_setSrch_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_pi sem1 : FullState} {not_lit l0 l1 cref repl : BitVec 32}
    {ri_n : Nat} {ri32 : BitVec 32} {off_v p_v q_v end_v : BitVec 64}
    (hpi : PropLitInv c F0 F_cur s_pi sem1 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hcref : cref.toNat ∈ fullArenaClauseRefsCore sem1.core)
    (har3 : sem1.core.arena[cref.toNat + 3]? = some l0)
    (har4 : sem1.core.arena[cref.toNat + 4]? = some l1)
    (har_ri : sem1.core.arena[cref.toNat + 3 + ri_n]? = some repl) :
    let sem2 : FullState :=
      { sem1 with core := { sem1.core with arena := sem1.core.arena.set (cref.toNat + 1) ri32 } }
    PropLitInv c F0 F_cur s_pi sem2 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat ∧
    sem2.LengthsOk c ∧
    cref.toNat ∈ fullArenaClauseRefsCore sem2.core ∧
    fullArenaClauseSizeCore sem2.core cref.toNat = fullArenaClauseSizeCore sem1.core cref.toNat ∧
    sem2.core.arena[cref.toNat + 3]? = some l0 ∧
    sem2.core.arena[cref.toNat + 4]? = some l1 ∧
    sem2.core.arena[cref.toNat + 3 + ri_n]? = some repl := by
  intro sem2
  have haren := hpi.len.core_ok.arena_len_arr
  have hstep := full_setSrch_preserves_nw hpi.len.core_ok hpi.nw (srch := ri32) hcref
  have hlen2 : sem2.LengthsOk c :=
    ⟨{ hpi.len.core_ok with arena_len_arr := by simp [sem2, haren] }, hpi.len.scratch_ok⟩
  have hnw2 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c sem2.core) :=
    fullWitnessInv_nw_congr hlen2.core_ok.cur_vars_le hstep.1 rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl
  have hperm2 : FullPropDecSpecs.FullArenaPermEq sem1.core sem2.core := hstep.2
  have hsw2 := hpi.sw.with_nonwatch (k' := sem2.core) rfl rfl rfl rfl hperm2.1
  have hpi2 : PropLitInv c F0 F_cur s_pi sem2 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat :=
    { len := hlen2, nw := hnw2, sw := hsw2
      ag := hpi.ag.update (fun k => { k with arena := sem2.core.arena })
      tr := ⟨hpi.tr.te_ge, hpi.tr.trl_pref, hpi.tr.lvl_pres⟩
      perm := hpi.perm.trans hperm2, sc_eq := hpi.sc_eq, not_f := hpi.not_f }
  refine ⟨hpi2, hlen2, hperm2.1.symm ▸ hcref, (hperm2.2 _ hcref).1, ?_, ?_, ?_⟩
  · simp only [sem2]; rw [List.getElem?_set_ne (by omega)]; exact har3
  · simp only [sem2]; rw [List.getElem?_set_ne (by omega)]; exact har4
  · simp only [sem2]; rw [List.getElem?_set_ne (by omega)]; exact har_ri

theorem s13_lp_scan_wp {Γ : Env} {rs : List Ty} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s_orig s_disk sem : FullState}
    {cur_lvl32 not_lit nl_lvl w0 l0 l1 cref : BitVec 32} {ov : BitVec 8}
    {te un uf tk1 p_v q end_v p2 off_v di dlim brk0 cbase csz pos : BitVec 64}
    {dlen : Nat} {ignore_ref : Arg Val i64} {ign_v : BitVec 64}
    {isBeyond rec_ph bigbig : Bool} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    {J_ovf : Cont (s13OvfSig isBeyond)}
    {J_lp : Cont [i64, i64, i64, i64, i64, i64, i64]}
    (hmaxv : c.max_vars < 2 * dimacsBound) (har : c.arena_cap < 2 * dimacsBound)
    (hwc : c.wcap < 2 * dimacsBound)
    (hign_val : ignore_ref.val = ign_v)
    (hpi : PropLitInv c F0 F_cur
      { s_orig with scratch := { s_orig.scratch with delayed := sem.scratch.delayed } } sem
      not_lit.toNat off_v.toNat q.toNat (p_v.toNat + 2) end_v.toNat)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (hcur_lvl : cur_lvl32 = BitVec.ofNat 32 sem.core.cur_level)
    (hcl32 : sem.core.cur_level < 2 ^ 32)
    (hw0_flag : (w0 &&& 0x80000000#32) = 0#32)
    (hq_le : q.toNat ≤ p_v.toNat) (hp2_le : p_v.toNat + 2 ≤ end_v.toNat)
    (hp2_n : (p_v + 2#64).toNat = p_v.toNat + 2)
    (hp2_n11 : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2)
    (hq1_n : (q + 1#64).toNat = q.toNat + 1) (hq2_n : (q + 2#64).toNat = q.toNat + 2)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore sem.core)
    (hng : fullArenaClauseGarbCore sem.core cref.toNat = false)
    (hfit : cref.toNat + 3 + fullArenaClauseSizeCore sem.core cref.toNat ≤ sem.core.arena_len)
    (har3 : sem.core.arena[cref.toNat + 3]? = some l0)
    (har4 : sem.core.arena[cref.toNat + 4]? = some l1)
    (hwatch : l0 = not_lit ∨ l1 = not_lit)
    (hoth_lt : (l0 ^^^ l1 ^^^ not_lit).toNat < 2 * sem.core.cur_vars)
    (hov_nsgt : (0#32).slt (BitVec.signExtend 32 ov) = false)
    (hov_eq : ov = sem.core.vals[(l0 ^^^ l1 ^^^ not_lit).toNat]?.getD 0#8)
    (hcbase : cbase.toNat = cref.toNat + 3)
    (hcsz : csz.toNat = fullArenaClauseSizeCore sem.core cref.toNat)
    (hte_eq : te.toNat = sem.core.trail_end) (hun_eq : un = sem.core.unassigned)
    (huf_eq : uf = sem.core.unflushed) (hoom : sem.core.oom = 0#64)
    (hnl : sem.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl)
    (hdi : di.toNat = 3 * dlen) (hdlen : dlen ≤ c.delayed_cap)
    (hdlim : dlim.toNat = 3 * c.delayed_cap)
    (hdok : DelayedWatchesOk s_orig.core sem.scratch.delayed dlen not_lit.toNat)
    (hp2_v : p2 = p_v + 2#64)
    (hm : (FullMem c (fastPropMem s_disk sem) ⋆ R) m)
    (hJ_ovf : ∀ {sem' : FullState} {tk' q' brk' : BitVec 64} {ovf' : Bool}
        {ovf_rw' ovf_oth' ovf_cr' : BitVec 32} {ovf_ri' : BitVec 64} {m' : Mem 64},
      PropLitInv c F0 F_cur
        { s_orig with scratch := { s_orig.scratch with delayed := sem.scratch.delayed } } sem'
        not_lit.toNat off_v.toNat q'.toNat (p_v.toNat + 2) end_v.toNat →
      te.toNat = sem'.core.trail_end → sem'.core.oom = 0#64 →
      sem'.core.unassigned = sem.core.unassigned → sem'.core.unflushed = sem.core.unflushed →
      (ovf' = false → isBeyond = false ∧ brk' = 1#64 ∧ PropLitConfl F_cur ign_v sem'.core) →
      (ovf' = true → brk' = brk0 ∧ S13ConflEq sem.core sem'.core ∧
        2 ≤ (p_v.toNat + 2) - off_v.toNat ∧ q'.toNat + 2 ≤ p_v.toNat + 2 ∧
        ovf_cr'.toNat < 0x80000000 ∧ ovf_cr'.toNat ∈ fullArenaClauseRefsCore sem'.core ∧
        fullArenaClauseGarbCore sem'.core ovf_cr'.toNat = false ∧
        ovf_cr'.toNat + 3 + fullArenaClauseSizeCore sem'.core ovf_cr'.toNat ≤ sem'.core.arena_len ∧
        ovf_oth'.toNat < 2 * sem'.core.cur_vars ∧ ovf_rw'.toNat < 2 * sem'.core.cur_vars ∧
        ovf_rw'.toNat ≠ not_lit.toNat ∧ 2 ≤ ovf_ri'.toNat ∧
        ovf_ri'.toNat < fullArenaClauseSizeCore sem'.core ovf_cr'.toNat ∧
        ∃ l0' l1', (l0' = not_lit ∨ l1' = not_lit) ∧ ovf_oth' = l0' ^^^ l1' ^^^ not_lit ∧
          sem'.core.arena[ovf_cr'.toNat + 3]? = some l0' ∧
          sem'.core.arena[ovf_cr'.toNat + 4]? = some l1' ∧
          sem'.core.arena[ovf_cr'.toNat + 3 + ovf_ri'.toNat]? = some ovf_rw') →
      (FullMem c (fastPropMem s_disk sem') ⋆ R) m' →
      wp Γ Q X (s13OvfJump isBeyond J_ovf (.var te) (.var un) (.var uf) (.var tk') (.var p2)
        (.var q') (.var di) (.var brk') (.var ovf') (.var ovf_rw') (.var ovf_oth') (.var ovf_cr')
        (.var ovf_ri')) m')
    (hJ_lp : ∀ {sem' : FullState} {te' un' uf' tk' q' di' : BitVec 64} {dlen' : Nat}
        {m' : Mem 64},
      PropLitInv c F0 F_cur
        { s_orig with scratch := { s_orig.scratch with delayed := sem'.scratch.delayed } } sem'
        not_lit.toNat off_v.toNat q'.toNat (p_v.toNat + 2) end_v.toNat →
      di'.toNat = 3 * dlen' → dlen' ≤ c.delayed_cap →
      DelayedWatchesOk s_orig.core sem'.scratch.delayed dlen' not_lit.toNat →
      (c.delayed_cap = 0 → sem'.scratch.delayed = sem.scratch.delayed) →
      sem.core.trail_end ≤ sem'.core.trail_end →
      te'.toNat = sem'.core.trail_end → un' = sem'.core.unassigned → uf' = sem'.core.unflushed →
      sem'.core.oom = sem.core.oom → S13ConflEq sem.core sem'.core →
      (FullMem c (fastPropMem s_disk sem') ⋆ R) m' →
      wp Γ Q X (.jump J_lp (.var te', (.var un', (.var uf', (.var tk', (.var p2, (.var q',
        (.var di', ())))))))) m') :
    wp Γ Q X (s13LpScanExpr isBeyond c.hdr c.pVals c.pWstk c.pArena c.pLevel c.pReason c.pTrail
      c.pTrailPos c.pFlags c.pPhases c.pDelayed dlim ignore_ref cur_lvl32 not_lit nl_lvl w0
      (l0 ^^^ l1 ^^^ not_lit) cref ov rec_ph bigbig te un uf tk1 p2 q di brk0 cbase csz pos
      J_ovf J_lp) m := by
  unfold dimacsBound at hmaxv har hwc
  let other := l0 ^^^ l1 ^^^ not_lit
  have haren := hpi.len.core_ok.arena_len_arr
  have halen := hpi.len.core_ok.arena_len_le
  have hcsz3 : 3 ≤ fullArenaClauseSizeCore sem.core cref.toNat :=
    (hpi.nw.arena.refs_wf cref.toNat hcr_ref).2.1
  have hc1_n : (cref.setWidth 64 + 1#64).toNat = cref.toNat + 1 :=
    m7_bv64_add1_toNat (by rw [bv_c0_zext32_64]; have := hcr_lt; omega)
  have hcr1_m : (cref.setWidth 64 + 1#64).toNat < (fastPropMem s_disk sem).core.arena.length := by
    rw [fastPropMem_arena, haren, hc1_n]; exact Nat.lt_of_lt_of_le (by omega) halen
  let ReplOk (ri : BitVec 64) (repl : BitVec 32) (found : Bool) : Prop :=
    (found = true ∧ 2 ≤ ri.toNat ∧
      ∃ hr_lt : ri.toNat < fullArenaClauseSizeCore sem.core cref.toNat,
        have har_len : cref.toNat + 3 + ri.toNat < sem.core.arena.length := by
          rw [haren]; exact Nat.lt_of_lt_of_le (by omega) halen
        repl = sem.core.arena[cref.toNat + 3 + ri.toNat]'har_len ∧
        repl.toNat < 2 * sem.core.cur_vars ∧
        ((sem.core.vals[repl.toNat]?.getD 0#8).signExtend 32).slt 0#32 = false) ∨
    (found = false ∧
      ∀ k, 2 ≤ k → k < fullArenaClauseSizeCore sem.core cref.toNat →
        fullFindReplBad sem cref.toNat k)
  unfold s13LpScanExpr
  refine wp_join_group (fun (st, ()) mst =>
      2 ≤ st.toNat ∧ st.toNat < fullArenaClauseSizeCore sem.core cref.toNat ∧
      (FullMem c (fastPropMem s_disk sem) ⋆ R) mst) ?_ ?_
  · rintro _ ⟨st, ⟨⟩⟩ mst ⟨hst2, hst_lt, hmst⟩
    refine wp_join_group (fun (ri1, repl1, found1, ()) mr1 =>
        (FullMem c (fastPropMem s_disk sem) ⋆ R) mr1 ∧
        ((found1 = true ∧ st.toNat ≤ ri1.toNat ∧
          ∃ hr_lt : ri1.toNat < fullArenaClauseSizeCore sem.core cref.toNat,
            have har_len : cref.toNat + 3 + ri1.toNat < sem.core.arena.length := by
              rw [haren]; exact Nat.lt_of_lt_of_le (by omega) halen
            repl1 = sem.core.arena[cref.toNat + 3 + ri1.toNat]'har_len ∧
            repl1.toNat < 2 * sem.core.cur_vars ∧
            ((sem.core.vals[repl1.toNat]?.getD 0#8).signExtend 32).slt 0#32 = false) ∨
         (found1 = false ∧
          ∀ k, st.toNat ≤ k → k < fullArenaClauseSizeCore sem.core cref.toNat →
            fullFindReplBad sem cref.toNat k))) ?_ ?_
    · rintro _ ⟨ri1, repl1, found1, ⟨⟩⟩ mr1 ⟨hmr1, hr1⟩
      refine wp_join_group (fun (ri, repl, found_f, ()) mr2 =>
          (FullMem c (fastPropMem s_disk sem) ⋆ R) mr2 ∧ ReplOk ri repl found_f) ?_ ?_
      · rintro _ ⟨ri, repl, found_f, ⟨⟩⟩ mr2 ⟨hmr2, hrep⟩
        s13_hsplit
        · rcases hrep with ⟨-, hri2, hri_lt, har_eq, hrepl_lt, hrepl_nneg⟩ | ⟨hf, -⟩
          · have har_ri : sem.core.arena[cref.toNat + 3 + ri.toNat]? = some repl :=
              har_eq ▸ List.getElem?_eq_getElem _
            have hrepl_ne : repl.toNat ≠ not_lit.toNat := by
              intro h; rw [h, hpi.not_f] at hrepl_nneg; revert hrepl_nneg; decide
            s13_hsteps_nogrp
            rw [show (1 : BitVec 64) = 1#64 from rfl, hc1_n, fastPropMem_arena,
              fastPropMem_with_arena] at hm
            have hsr := s13_setSrch_step hpi hcr_ref har3 har4 har_ri (ri32 := ri.setWidth 32)
            let sem2 : FullState :=
              { sem with core := { sem.core with
                arena := sem.core.arena.set (cref.toNat + 1) (ri.setWidth 32) } }
            have hcr_ref2 : cref.toNat ∈ fullArenaClauseRefsCore sem2.core := hsr.2.2.1
            have hfit2 : cref.toNat + 3 + fullArenaClauseSizeCore sem2.core cref.toNat ≤
                sem2.core.arena_len := by rw [hsr.2.2.2.1]; exact hfit
            have hng2 : fullArenaClauseGarbCore sem2.core cref.toNat = false := by
              unfold fullArenaClauseGarbCore fullArenaHdrCore at hng ⊢
              simpa [sem2, List.getElem?_set_ne (by omega : cref.toNat + 1 ≠ cref.toNat)] using hng
            have hcv2 : sem2.core.cur_vars = sem.core.cur_vars := rfl
            have hri_lt2 : ri.toNat < fullArenaClauseSizeCore sem2.core cref.toNat := by
              rw [hsr.2.2.2.1]; exact hri_lt
            have hq_ge := hpi.sw.q_ge
            refine s13_lp_repl_del_wp (s_orig := s_orig) har (fid_pi_rebase hsr.1) hcr_lt hcr_ref2
              hng2 hfit2 hsr.2.2.2.2.1 hsr.2.2.2.2.2.1 hwatch rfl hri2 hri_lt2
              hsr.2.2.2.2.2.2 (hcv2 ▸ hrepl_lt) hrepl_ne (hcv2 ▸ hoth_lt) hcbase hdi hdlen hdlim
              (by rw [congrArg FullScratch.delayed hsr.1.sc_eq]; exact hdok) hm ?_ ?_
            · intro m_o hm_o
              cases isBeyond <;>
              exact hJ_ovf (sem' := sem2) hsr.1 hte_eq hoom rfl rfl (fun h => absurd h (by decide))
                (fun _ => ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, by omega, by omega, hcr_lt, hcr_ref2, hng2,
                  hfit2, hcv2 ▸ hoth_lt, hcv2 ▸ hrepl_lt, hrepl_ne, hri2, hri_lt2,
                  l0, l1, hwatch, rfl, hsr.2.2.2.2.1, hsr.2.2.2.2.2.1,
                  hsr.2.2.2.2.2.2⟩)
                hm_o
            · intro sem4 di' dlen' m_l hpi4 hdi4 hdl4 hdok4 hd04 hoom4 hct4 hte4 hun4 huf4 hm_l
              exact hJ_lp hpi4 hdi4 hdl4 hdok4 hd04 (by rw [hte4]; exact Nat.le_refl _)
                (hte_eq.trans hte4.symm) (hun_eq.trans hun4.symm) (huf_eq.trans huf4.symm)
                hoom4 hct4 hm_l
          · exact absurd hc (by rw [hf]; decide)
        · have hf_eq : found_f = false := by revert hc; cases found_f <;> simp
          rcases hrep with ⟨hf, -⟩ | ⟨-, hbad_all⟩
          · exact absurd (hf_eq.symm.trans hf) (by decide)
          · exact s13_lp_no_repl_wp hmaxv har hwc hign_val hpi hnot_lt hcur_lvl hcl32 hw0_flag
              hq_le hp2_le hp2_n hp2_n11 hq1_n hq2_n hcr_lt hcr_ref hng hfit har3 har4 hwatch
              hoth_lt hov_nsgt hov_eq hbad_all hcbase hcsz hte_eq hun_eq huf_eq hoom hnl hp2_v hmr2
              (fun hb {sem' q' brk' m'} hpi' hte' hoom' hun' huf' hbrk' hcf' hm' => by
                cases isBeyond
                · exact hJ_ovf hpi' hte' hoom' hun' huf' (fun _ => ⟨hb, hbrk', hcf'⟩)
                    (fun h => absurd h (by decide)) hm'
                · exact absurd hb (by decide))
              (fun {sem' te' un' uf' tk' q' m'} hpi' hte_ge hte' hun' huf' hoom' hct' hm' =>
                have hdel' : sem'.scratch.delayed = sem.scratch.delayed :=
                  @congrArg FullScratch _ sem'.scratch
                    { s_orig.scratch with
                      search_ticks := sem'.scratch.search_ticks, wsort := sem'.scratch.wsort,
                      phases := sem'.scratch.phases, delayed := sem.scratch.delayed }
                    FullScratch.delayed hpi'.sc_eq
                hJ_lp (fid_pi_rebase hpi') hdi hdlen (hdel' ▸ hdok) (fun _ => hdel')
                  hte_ge hte' hun' huf' hoom' hct' hm')
      · intro J_r2 hJ_r2
        s13_hsplit
        · s13_hsteps
          exact hJ_r2 (ri1, repl1, found1, ()) _ ⟨hmr1, by
            rcases hr1 with ⟨rfl, hri_ge, hr_lt, hrep⟩ | ⟨hf, -⟩
            · exact Or.inl ⟨rfl, le_trans hst2 hri_ge, hr_lt, hrep⟩
            · exact absurd hc (by rw [hf]; decide)⟩
        · have hf1 : found1 = false := by revert hc; cases found1 <;> simp
          rcases hr1 with ⟨hf, -⟩ | ⟨-, hbad_hi⟩
          · exact absurd (hf1.symm.trans hf) (by decide)
          · refine wp_join_group (fun (wri, wrepl, wf, ()) mw =>
                (FullMem c (fastPropMem s_disk sem) ⋆ R) mw ∧ ReplOk wri wrepl wf) ?_ ?_
            · rintro _ ⟨wri, wrepl, wf, ⟨⟩⟩ mw ⟨hmw, hwr⟩
              s13_hsteps; exact hJ_r2 (wri, wrepl, wf, ()) mw ⟨hmw, hwr⟩
            · intro J_w hJ_w
              refine m7_lp_repl_scan_arg_wp (s_pi := { s_orig with
                  scratch := { s_orig.scratch with delayed := sem.scratch.delayed } })
                har (hp2_n ▸ hpi) hcr_ref hng hfit hcbase (le_of_lt hst_lt) hst2 hf1 hmr1
                fun ri_w repl_w found_w hres => ?_
              refine hJ_w (ri_w, repl_w, found_w, ()) _ ⟨hmr1, ?_⟩
              rcases hres with ⟨rfl, hri2, hr_lt, hrep⟩ | ⟨rfl, -, -, hbad_lo⟩
              · exact Or.inl ⟨rfl, hri2, Nat.lt_trans hr_lt hst_lt, hrep⟩
              · refine Or.inr ⟨rfl, fun k hk2 hkc => ?_⟩
                by_cases hkst : k < st.toNat
                · exact hbad_lo k hk2 hkst
                · exact hbad_hi k (Nat.le_of_not_lt hkst) hkc
    · intro J_r1 hJ_r1
      refine m7_lp_repl_scan_arg_wp (s_pi := { s_orig with
          scratch := { s_orig.scratch with delayed := sem.scratch.delayed } })
        har (hp2_n ▸ hpi) hcr_ref hng hfit hcbase (by rw [hcsz]; exact Nat.le_refl _)
        (by rw [hcsz]; exact Nat.le_of_lt hst_lt) rfl hmst fun ri1 repl1 found1 hres => ?_
      refine hJ_r1 (ri1, repl1, found1, ()) _ ⟨hmst, ?_⟩
      rcases hres with ⟨rfl, hst_ri, hr_lt, hrep⟩ | ⟨rfl, -, -, hbad_hi⟩
      · exact Or.inl ⟨rfl, hst_ri, by rwa [← hcsz], hrep⟩
      · exact Or.inr ⟨rfl, fun k hk1 hkc => hbad_hi k hk1 (by rwa [← hcsz] at hkc)⟩
  · intro J_st hJ_st
    have hcsz3_lt : (2#64 : BitVec 64).toNat < fullArenaClauseSizeCore sem.core cref.toNat :=
      Nat.lt_of_lt_of_le (by decide) hcsz3
    s13_hsplit
    · s13_hsteps; exact hJ_st (2#64, ()) _ ⟨by decide, hcsz3_lt, hm⟩
    · s13_hsplit
      · s13_hsteps; exact hJ_st (2#64, ()) _ ⟨by decide, hcsz3_lt, hm⟩
      · have hpos2 : 2 ≤ pos.toNat := by rename_i hc1; exact Nat.le_of_not_lt hc1
        have hpos_lt : pos.toNat < fullArenaClauseSizeCore sem.core cref.toNat := by
          rw [← hcsz]; exact Nat.lt_of_not_le hc
        s13_hsteps; exact hJ_st (pos, ()) _ ⟨hpos2, hpos_lt, hm⟩

/-! ## 2. Large-Clause Watch Step (`s13LpLargeStepExpr`) & Inner Loop (`s13LpLoopExpr`) -/

theorem s13_lp_large_step_wp {Γ : Env} {rs : List Ty} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s_orig s_disk sem : FullState}
    {cur_lvl32 not_lit w0 nl_lvl : BitVec 32}
    {two_cv te un uf tk p q di dlim brk0 end_v off_v : BitVec 64}
    {ignore_ref : Arg Val i64} {ign_v : BitVec 64}
    {isBeyond rec_ph bigbig : Bool} {dlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    {J_ovf : Cont (s13OvfSig isBeyond)}
    {J_lp : Cont [i64, i64, i64, i64, i64, i64, i64]}
    (hmaxv : c.max_vars < 2 * dimacsBound) (har : c.arena_cap < 2 * dimacsBound)
    (hwc : c.wcap < 2 * dimacsBound)
    (hign_val : ignore_ref.val = ign_v)
    (hpi : PropLitInv c F0 F_cur
      { s_orig with scratch := { s_orig.scratch with delayed := sem.scratch.delayed } } sem
      not_lit.toNat off_v.toNat q.toNat p.toNat end_v.toNat)
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
      PropLitInv c F0 F_cur
        { s_orig with scratch := { s_orig.scratch with delayed := sem.scratch.delayed } } sem'
        not_lit.toNat off_v.toNat q'.toNat p'.toNat end_v.toNat →
      te.toNat = sem'.core.trail_end → sem'.core.oom = 0#64 →
      sem'.core.unassigned = sem.core.unassigned → sem'.core.unflushed = sem.core.unflushed →
      (ovf' = false → isBeyond = false ∧ p.toNat ≤ p'.toNat ∧ brk' = 1#64 ∧
        PropLitConfl F_cur ign_v sem'.core) →
      (ovf' = true → brk' = brk0 ∧ S13ConflEq sem.core sem'.core ∧
        p.toNat < p'.toNat ∧ p'.toNat ≤ end_v.toNat ∧ 2 ≤ p'.toNat - off_v.toNat ∧
        q'.toNat + 2 ≤ p'.toNat ∧
        ovf_cr'.toNat < 0x80000000 ∧ ovf_cr'.toNat ∈ fullArenaClauseRefsCore sem'.core ∧
        fullArenaClauseGarbCore sem'.core ovf_cr'.toNat = false ∧
        ovf_cr'.toNat + 3 + fullArenaClauseSizeCore sem'.core ovf_cr'.toNat ≤ sem'.core.arena_len ∧
        ovf_oth'.toNat < 2 * sem'.core.cur_vars ∧ ovf_rw'.toNat < 2 * sem'.core.cur_vars ∧
        ovf_rw'.toNat ≠ not_lit.toNat ∧ 2 ≤ ovf_ri'.toNat ∧
        ovf_ri'.toNat < fullArenaClauseSizeCore sem'.core ovf_cr'.toNat ∧
        ∃ l0' l1', (l0' = not_lit ∨ l1' = not_lit) ∧ ovf_oth' = l0' ^^^ l1' ^^^ not_lit ∧
          sem'.core.arena[ovf_cr'.toNat + 3]? = some l0' ∧
          sem'.core.arena[ovf_cr'.toNat + 4]? = some l1' ∧
          sem'.core.arena[ovf_cr'.toNat + 3 + ovf_ri'.toNat]? = some ovf_rw') →
      (FullMem c (fastPropMem s_disk sem') ⋆ R) m' →
      wp Γ Q X (s13OvfJump isBeyond J_ovf (.var te) (.var un) (.var uf) (.var tk') (.var p')
        (.var q') (.var di) (.var brk') (.var ovf') (.var ovf_rw') (.var ovf_oth') (.var ovf_cr')
        (.var ovf_ri')) m')
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
      sem'.core.oom = sem.core.oom → S13ConflEq sem.core sem'.core →
      (FullMem c (fastPropMem s_disk sem') ⋆ R) m' →
      wp Γ Q X (.jump J_lp (.var te', (.var un', (.var uf', (.var tk', (.var p', (.var q',
        (.var di', ())))))))) m') :
    wp Γ Q X (s13LpLargeStepExpr isBeyond c.hdr c.pVals c.pWstk c.pArena c.pLevel c.pReason
      c.pTrail c.pTrailPos c.pFlags c.pPhases c.pDelayed dlim ignore_ref two_cv cur_lvl32
      not_lit w0 nl_lvl rec_ph bigbig te un uf tk p q di brk0 J_ovf J_lp) m := by
  have hJ_lp' : ∀ {sem' : FullState} {te' un' uf' tk' q' : BitVec 64} {m' : Mem 64},
      PropLitInv c F0 F_cur
        { s_orig with scratch := { s_orig.scratch with delayed := sem.scratch.delayed } } sem'
        not_lit.toNat off_v.toNat q'.toNat (p.toNat + 2) end_v.toNat →
      sem.core.trail_end ≤ sem'.core.trail_end →
      te'.toNat = sem'.core.trail_end → un' = sem'.core.unassigned → uf' = sem'.core.unflushed →
      sem'.core.oom = sem.core.oom → S13ConflEq sem.core sem'.core →
      (FullMem c (fastPropMem s_disk sem') ⋆ R) m' →
      wp Γ Q X (.jump J_lp (.var te', (.var un', (.var uf', (.var tk', (.var (p + 2#64), (.var q',
        (.var di, ())))))))) m' := by
    intro sem' te' un' uf' tk' q' m' hpi' hte_ge hte' hun' huf' hoom' hct' hm'
    have hp2_n : (p + 2#64).toNat = p.toNat + 2 := by
      have ⟨hend_le, hwlen_le⟩ := hpi.end_lt_wcap hnot_lt
      have hwc' : c.wcap < 2 * dimacsBound := hwc
      unfold dimacsBound at hwc'
      exact m7_bv64_add2_toNat (by omega)
    have hdel' : sem'.scratch.delayed = sem.scratch.delayed :=
      @congrArg FullScratch _ sem'.scratch
        { s_orig.scratch with
          search_ticks := sem'.scratch.search_ticks, wsort := sem'.scratch.wsort,
          phases := sem'.scratch.phases, delayed := sem.scratch.delayed }
        FullScratch.delayed hpi'.sc_eq
    exact hJ_lp (hp2_n ▸ fid_pi_rebase hpi') hdi hdlen (hdel' ▸ hdok) (fun _ => hdel')
      (by rw [hp2_n]; omega) (by rw [hp2_n]; have := hpi'.sw.p_le_end; omega)
      hte_ge hte' hun' huf' hoom' hct' hm'
  unfold dimacsBound at hmaxv har hwc
  have hcv := hpi.len.core_ok.cur_vars_le
  have hvals_len := hpi.len.core_ok.vals_len
  have haren_len := hpi.len.core_ok.arena_len_arr
  have halen_le := hpi.len.core_ok.arena_len_le
  have hwstk_len := hpi.len.core_ok.wstk_len_arr
  have ⟨hend_le, hwlen_le⟩ := hpi.end_lt_wcap hnot_lt
  have hend_wcap : end_v.toNat ≤ c.wcap := Nat.le_trans hend_le hwlen_le
  have hq_ge := hpi.sw.q_ge; have hq_le := hpi.sw.q_le_p; have hp_le := hpi.sw.p_le_end
  have hp_rem_pos : 0 < end_v.toNat - p.toNat := Nat.sub_pos_of_lt hp_lt
  obtain ⟨_, cref0, hcr_get, hcr_lt, hcr_ref, hrem2⟩ :=
    watchSlice_inv_large hpi.sw.rem_slice hp_rem_pos hw0_get hflag
  have h2_le_end : p.toNat + 2 ≤ end_v.toNat := by omega
  have hp1_n : (p + 1#64).toNat = p.toNat + 1 := m7_bv64_add1_toNat (by omega)
  have hp2_n : (p + 2#64).toNat = p.toNat + 2 := m7_bv64_add2_toNat (by omega)
  have hp2_n11 : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by
    have : p + 1#64 + 1#64 = p + 2#64 := by rw [BitVec.add_assoc]; rfl
    rw [this, hp2_n]
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
  have hcr_eq_raw : sem.core.wstk[(p + (1 : BitVec 64)).toNat]'(by
      rw [hwstk_len, show (p + (1 : BitVec 64)).toNat = p.toNat + 1 from hp1_n]; omega) =
      cref0 := by
    rw [← fc_getElem_wstk (s0 := s_disk) (sem := sem)]; exact hcr_eq'
  have hsw_drop : SplitWatchesInv F_cur sem.core not_lit.toNat off_v.toNat q.toNat
      (p.toNat + 2) end_v.toNat :=
    hpi.sw.advance_rem (p' := p.toNat + 2) (by omega) h2_le_end (by simpa [Nat.sub_sub] using hrem2)
  have hpi_drop : PropLitInv c F0 F_cur
      { s_orig with scratch := { s_orig.scratch with delayed := sem.scratch.delayed } } sem
      not_lit.toNat off_v.toNat q.toNat (p.toNat + 2) end_v.toNat :=
    { hpi with sw := hsw_drop }
  have hcr_wf := hpi.nw.arena.refs_wf cref0.toNat hcr_ref
  have hcsz3 : 3 ≤ fullArenaClauseSizeCore sem.core cref0.toNat := hcr_wf.2.1
  have hcr_fit : cref0.toNat + 3 + fullArenaClauseSizeCore sem.core cref0.toNat ≤
      sem.core.arena_len := Nat.le_trans hcr_wf.2.2.1 hcr_wf.2.2.2.1
  have hsem_sc :
      { sem with scratch := { sem.scratch with search_ticks := sem.scratch.search_ticks } } =
      sem := by cases sem; rfl
  unfold s13LpLargeStepExpr
  refine wp_join_group (fun () mc => (FullMem c (fastPropMem s_disk sem) ⋆ R) mc) ?_ ?_
  · rintro _ ⟨⟩ mc hm
    s13_hsteps_nogrp
    simp only [hcr_eq']
    have hcr0_m : (cref0.setWidth 64).toNat < (fastPropMem s_disk sem).core.arena.length := by
      rw [fastPropMem_arena, haren_len, bv_c0_zext32_64]
      exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans hcr_fit halen_le)
    s13_hsplit
    · have hpi_d := propLit_inv_drop (ticks' := sem.scratch.search_ticks) hpi hsw_drop hp2_n11
      rw [hp2_n11, hsem_sc] at hpi_d
      s13_hsteps
      exact hJ_lp' hpi_d (Nat.le_refl _) hte_eq hun_eq huf_eq rfl ⟨rfl, rfl, rfl, rfl⟩ hm
    · have hng0 : fullArenaClauseGarbCore sem.core cref0.toNat = false := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore
        have hg : sem.core.arena[cref0.toNat]? =
            some (sem.core.arena[cref0.toNat]'(by rw [haren_len]; omega)) :=
          List.getElem?_eq_getElem _
        have hfl_eq : (fastPropMem s_disk sem).core.arena[cref0.toNat]'(by
            rw [fastPropMem_arena, haren_len]; omega) =
            sem.core.arena[cref0.toNat]'(by rw [haren_len]; omega) :=
          fc_getElem_arena s_disk sem
        have hcr_idx_mod : (p.toNat + 1) % 2 ^ 64 = (p + 1#64).toNat := by
          rw [hp1_n, Nat.mod_eq_of_lt (by omega)]
        have h524 : (sem.core.arena[cref0.toNat]'(by rw [haren_len]; omega) &&&
            0x00080000#32) = 0#32 := by
          rw [← hfl_eq]
          simpa only [hcr_idx_mod, hcr_eq, bv_c0_zext32_64,
            show (524288 : BitVec 32) = 0x00080000#32 from rfl,
            show (0 : BitVec 32) = 0#32 from rfl] using hc
        rw [hg, Option.getD_some, h524]; decide
      have hcbase_n : (cref0.setWidth 64 + 3#64).toNat = cref0.toNat + 3 :=
        m7_bv64_add_toNat (by rw [bv_c0_zext32_64]; have := hcr_lt; simp; omega)
      have hcbase1_n : (cref0.setWidth 64 + 3#64 + 1#64).toNat = cref0.toNat + 4 := by
        rw [m7_bv64_add1_toNat (by rw [hcbase_n]; omega), hcbase_n]
      have hcr3_m : (cref0.setWidth 64 + 3#64).toNat <
          (fastPropMem s_disk sem).core.arena.length := by
        rw [fastPropMem_arena, haren_len, hcbase_n]
        exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans hcr_fit halen_le)
      have hcr4_m : (cref0.setWidth 64 + 3#64 + 1#64).toNat <
          (fastPropMem s_disk sem).core.arena.length := by
        rw [fastPropMem_arena, haren_len, hcbase1_n]
        exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans hcr_fit halen_le)
      s13_hsteps_nogrp
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
      refine wp_join_group (ts := []) (fun () mchk =>
          (FullMem c (fastPropMem s_disk sem) ⋆ R) mchk ∧ (l0 = not_lit ∨ l1 = not_lit)) ?_ ?_
      · rintro _ ⟨⟩ mchk ⟨hm, hwatch⟩
        let other := l0 ^^^ l1 ^^^ not_lit
        have hbd0 : cref0.toNat + 3 + fullArenaClauseSizeCore sem.core cref0.toNat ≤
            sem.core.arena.length := haren_len ▸ Nat.le_trans hcr_fit halen_le
        have hoth_lt : other.toNat < 2 * sem.core.cur_vars := by
          rcases hwatch with rfl | rfl
          · have hoth_l1 : other = l1 := fid_xor_cancel_l l0 l1
            rw [hoth_l1]
            exact hpi.nw.arena.lits_lt cref0.toNat hcr_ref hng0 l1.toNat
              ((mem_fullArenaClauseLitsCore_iff hbd0).mpr ⟨1, by omega,
                congrArg BitVec.toNat hl1_eq.symm⟩)
          · have hoth_l0 : other = l0 := fid_xor_cancel_r l0 l1
            rw [hoth_l0]
            exact hpi.nw.arena.lits_lt cref0.toNat hcr_ref hng0 l0.toNat
              ((mem_fullArenaClauseLitsCore_iff hbd0).mpr ⟨0, by omega,
                congrArg BitVec.toNat hl0_eq.symm⟩)
        have hoth_vals_m : (other.setWidth 64).toNat <
            (fastPropMem s_disk sem).core.vals.length := by
          rw [fastPropMem_vals, hvals_len, bv_c0_zext32_64]; omega
        have hoth_vals_raw : other.toNat < sem.core.vals.length := by rw [hvals_len]; omega
        have hoth_mask : other &&& 0x7FFFFFFF#32 = other := m7_bv32_mask7f_eq (by omega)
        have hoth_flag0 : (other &&& 0x80000000#32) = 0#32 := by
          rw [← hoth_mask, BitVec.and_assoc,
            show (0x7FFFFFFF#32 &&& 0x80000000#32 : BitVec 32) = 0#32 from rfl, BitVec.and_zero]
        let ov := (fastPropMem s_disk sem).core.vals[(other.setWidth 64).toNat]'hoth_vals_m
        have hov_eq : ov = sem.core.vals[other.toNat]?.getD 0#8 := by
          rw [List.getElem?_eq_getElem hoth_vals_raw, Option.getD_some]
          exact (fc_getElem_vals s_disk sem).trans
            (fc_getElem_eq_of_idx (bv_c0_zext32_64 other) _ hoth_vals_raw)
        s13_hsteps_nogrp
        s13_hsplit
        · s13_hsteps_nogrp
          simp only [fastPropMem_wstk, fastPropMem_with_wstk] at hm
          have hkeep := propLit_inv_keep_large hpi hsw_drop hnot_lt hq1_n hq2_n hp2_n11
            (Nat.add_le_add_right hq_le 2) h2_le_end hoth_flag0 hcr_lt hcr_ref
          rw [show (p + (1 : BitVec 64) + (1 : BitVec 64)).toNat = p.toNat + 2 from by
              rw [show p + (1 : BitVec 64) + (1 : BitVec 64) = p + 2#64 from by
                rw [BitVec.add_assoc]; rfl, hp2_n]] at hkeep
          s13_hsteps
          exact hJ_lp' hkeep (Nat.le_refl _) hte_eq hun_eq huf_eq rfl ⟨rfl, rfl, rfl, rfl⟩
            (by simpa only [fastPropMem_wstk, fastPropMem_with_wstk, other, l0, l1,
              show (3 : BitVec 64) = 3#64 from rfl, show (1 : BitVec 64) = 1#64 from rfl,
              show (q + (1 : BitVec 64)).toNat = (q + 1#64).toNat from rfl] using hm)
        · have h0_rw : (fastPropMem s_disk sem).core.arena[(cref0.toNat +
              BitVec.toNat (3 : BitVec 64)) % 2 ^ 64]'(by
                rw [fastPropMem_arena, haren_len, show (3 : BitVec 64).toNat = 3 from rfl,
                  Nat.mod_eq_of_lt (by omega)]; exact Nat.lt_of_lt_of_le (by omega)
                  (Nat.le_trans hcr_fit halen_le)) = l0 := by
            refine (fc_getElem_eq_of_idx ?_ _ _).trans rfl
            rw [hcbase_n, show (3 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
          have h1_rw : (fastPropMem s_disk sem).core.arena[(cref0.toNat +
              BitVec.toNat (3 : BitVec 64) + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                rw [fastPropMem_arena, haren_len, show (3 : BitVec 64).toNat = 3 from rfl,
                  show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
                exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans hcr_fit halen_le)) =
              l1 := by
            refine (fc_getElem_eq_of_idx ?_ _ _).trans rfl
            rw [hcbase1_n, show (3 : BitVec 64).toNat = 3 from rfl,
              show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
          have hov_nsgt : (0#32).slt (BitVec.signExtend 32 ov) = false := by
            simpa only [ov, other, h0_rw, h1_rw, bv_c0_zext32_64,
              show (0 : BitVec 32) = 0#32 from rfl] using hc
          have hc2_n : (cref0.setWidth 64 + 2#64).toNat = cref0.toNat + 2 :=
            m7_bv64_add_toNat (by rw [bv_c0_zext32_64]; have := hcr_lt; simp; omega)
          have hc1_n : (cref0.setWidth 64 + 1#64).toNat = cref0.toNat + 1 :=
            m7_bv64_add1_toNat (by rw [bv_c0_zext32_64]; have := hcr_lt; omega)
          have hcr2_m : (cref0.setWidth 64 + 2#64).toNat <
              (fastPropMem s_disk sem).core.arena.length := by
            rw [fastPropMem_arena, haren_len, hc2_n]
            exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans hcr_fit halen_le)
          have hcr1_m : (cref0.setWidth 64 + 1#64).toNat <
              (fastPropMem s_disk sem).core.arena.length := by
            rw [fastPropMem_arena, haren_len, hc1_n]
            exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans hcr_fit halen_le)
          let csz32 := (fastPropMem s_disk sem).core.arena[(cref0.setWidth 64 + 2#64).toNat]'hcr2_m
          let pos32 := (fastPropMem s_disk sem).core.arena[(cref0.setWidth 64 + 1#64).toNat]'hcr1_m
          have hcsz64 :
              (csz32.setWidth 64).toNat = fullArenaClauseSizeCore sem.core cref0.toNat := by
            unfold fullArenaClauseSizeCore
            have hcsz_eq : csz32 = sem.core.arena[cref0.toNat + 2]'(by rw [haren_len]; omega) :=
              (fc_getElem_arena s_disk sem).trans (fc_getElem_eq_of_idx hc2_n _ _)
            rw [bv_c0_zext32_64, hcsz_eq, List.getElem?_eq_getElem (by rw [haren_len]; omega),
              Option.getD_some]
          s13_hsteps_nogrp
          refine s13_lp_scan_wp (s_orig := s_orig) hmaxv har hwc hign_val hpi_drop hnot_lt hcur_lvl
            hcl32 hflag hq_le h2_le_end hp2_n hp2_n11 hq1_n hq2_n hcr_lt hcr_ref hng0 hcr_fit
            hl0_get hl1_get hwatch hoth_lt hov_nsgt hov_eq hcbase_n hcsz64 hte_eq hun_eq huf_eq
            hoom hnl hdi hdlen hdlim hdok rfl hm ?_ ?_
          · intro sem' tk' q' brk' ovf' ovf_rw' ovf_oth' ovf_cr' ovf_ri' m' hpi' hte' hoom'
              hun' huf' hno hov hm'
            have hpi'' : PropLitInv c F0 F_cur
                { s_orig with scratch := { s_orig.scratch with delayed := sem.scratch.delayed } }
                sem' not_lit.toNat off_v.toNat q'.toNat (p + 2).toNat end_v.toNat := by
              rw [show p + (2 : BitVec 64) = p + 2#64 from rfl, hp2_n]; exact hpi'
            cases isBeyond <;>
            exact hJ_ovf hpi'' hte' hoom' hun' huf'
              (fun h => let ⟨hb0, hbrk, hcf⟩ := hno h
                ⟨hb0, by rw [show p + (2 : BitVec 64) = p + 2#64 from rfl, hp2_n]; omega,
                  hbrk, hcf⟩)
              (fun h => let ⟨hbrk, hct, hpo, hql, hlt, href, hng', hfit', hot', hrw', hne',
                hri2, hri_lt, l0', l1', hwt', hoth', hl0', hl1', hri'⟩ := hov h
                ⟨hbrk, hct, by rw [show p + (2 : BitVec 64) = p + 2#64 from rfl, hp2_n]; omega,
                  by rw [show p + (2 : BitVec 64) = p + 2#64 from rfl, hp2_n]; exact h2_le_end,
                  by rw [show p + (2 : BitVec 64) = p + 2#64 from rfl, hp2_n]; exact hpo,
                  by rw [show p + (2 : BitVec 64) = p + 2#64 from rfl, hp2_n]; exact hql,
                  hlt, href, hng', hfit', hot', hrw', hne', hri2, hri_lt,
                  l0', l1', hwt', hoth', hl0', hl1', hri'⟩)
              hm'
          · intro sem' te' un' uf' tk' q' di' dlen' m' hpi' hdi' hdl' hdok' hd0' hte_ge hte'
              hun' huf' hoom' hct' hm'
            exact hJ_lp (hp2_n ▸ hpi') hdi' hdl' hdok' hd0'
              (by rw [show (2 : BitVec 64) = 2#64 from rfl, hp2_n]; omega)
              (by rw [show (2 : BitVec 64) = 2#64 from rfl, hp2_n]; exact h2_le_end)
              hte_ge hte' hun' huf' hoom' hct' hm'
      · intro J_chk hJ_chk
        s13_hsplit
        · s13_hsplit
          · have hpi_d := propLit_inv_drop (ticks' := sem.scratch.search_ticks) hpi hsw_drop hp2_n11
            rw [hp2_n11, hsem_sc] at hpi_d
            s13_hsteps
            exact hJ_lp' hpi_d (Nat.le_refl _) hte_eq hun_eq huf_eq rfl ⟨rfl, rfl, rfl, rfl⟩ hm
          · have hmod1 : (cref0.toNat + BitVec.toNat (3 : BitVec 64) +
                BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
                (cref0.setWidth 64 + 3#64 + 1#64).toNat := by
              rw [hcbase1_n, show (3 : BitVec 64).toNat = 3 from rfl,
                show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
            have hl1_eq_not : l1 = not_lit :=
              (fc_getElem_eq_of_idx hmod1.symm _ _).trans hc
            s13_hsteps; exact hJ_chk () mc ⟨hm, Or.inr hl1_eq_not⟩
        · have hmod0 : (cref0.toNat + BitVec.toNat (3 : BitVec 64)) % 2 ^ 64 =
              (cref0.setWidth 64 + 3#64).toNat := by
            rw [hcbase_n, show (3 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
          have hl0_eq_not : l0 = not_lit :=
            (fc_getElem_eq_of_idx hmod0.symm _ _).trans hc
          s13_hsteps; exact hJ_chk () mc ⟨hm, Or.inl hl0_eq_not⟩
  · intro J_c hJ_c
    s13_hsplit
    · have hw0_lt : w0.toNat < 2 * sem.core.cur_vars := by rw [htwo_cv] at hc; exact hc
      have hw0_vals_m : (w0.setWidth 64).toNat < (fastPropMem s_disk sem).core.vals.length := by
        rw [fastPropMem_vals, hvals_len, bv_c0_zext32_64]; omega
      s13_hsplit
      · s13_hsteps_nogrp
        simp only [fastPropMem_wstk, fastPropMem_with_wstk, hcr_eq_raw] at hm
        have hkeep := propLit_inv_keep_large hpi hsw_drop hnot_lt hq1_n hq2_n hp2_n11
          (Nat.add_le_add_right hq_le 2) h2_le_end hflag hcr_lt hcr_ref
        rw [show p + (1 : BitVec 64) + (1 : BitVec 64) = p + 2#64 from by
          rw [BitVec.add_assoc]; rfl, hp2_n] at hkeep
        s13_hsteps
        let sem_k : FullState :=
          { sem with core := { sem.core with
            wstk := (sem.core.wstk.set q.toNat w0).set (q + 1#64).toNat cref0 } }
        exact hJ_lp' (sem' := sem_k) hkeep (Nat.le_refl _) hte_eq hun_eq huf_eq rfl
          ⟨rfl, rfl, rfl, rfl⟩
          (by simpa only [sem_k, fastPropMem_wstk, fastPropMem_with_wstk,
            show (q + (1 : BitVec 64)).toNat = (q + 1#64).toNat from rfl] using hm)
      · s13_hsteps; exact hJ_c () m hm
    · s13_hsteps; exact hJ_c () m hm

theorem s13_lp_loop_wp {Γ : Env} {rs : List Ty} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s_orig s_disk sem0 : FullState}
    {cur_lvl32 not_lit nl_lvl : BitVec 32}
    {two_cv te0 un0 uf0 tk0 p0 q0 di0 dlim end0 off0 brk0 : BitVec 64}
    {ignore_ref : Arg Val i64} {ign_v : BitVec 64}
    {isBeyond rec_ph bigbig : Bool} {dlen0 : Nat}
    {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post rs} {X : XPost}
    {J_ovf : Cont (s13OvfSig isBeyond)}
    (hmaxv : c.max_vars < 2 * dimacsBound) (har : c.arena_cap < 2 * dimacsBound)
    (hwc : c.wcap < 2 * dimacsBound)
    (hign_val : ignore_ref.val = ign_v)
    (hpi0 : PropLitInv c F0 F_cur
      { s_orig with scratch := { s_orig.scratch with delayed := sem0.scratch.delayed } } sem0
      not_lit.toNat off0.toNat q0.toNat p0.toNat end0.toNat)
    (hnot_lt : not_lit.toNat < 2 * sem0.core.cur_vars)
    (htwo_cv : two_cv.toNat = 2 * sem0.core.cur_vars)
    (hcur_lvl : cur_lvl32 = BitVec.ofNat 32 sem0.core.cur_level)
    (hcl32 : sem0.core.cur_level < 2 ^ 32)
    (hte0 : te0.toNat = sem0.core.trail_end) (hun0 : un0 = sem0.core.unassigned)
    (huf0 : uf0 = sem0.core.unflushed) (hoom0 : sem0.core.oom = 0#64)
    (hbrk0 : brk0 = 0#64)
    (hnl : ∀ k : FullCoreState, FullPropDecSpecs.FullTrailExt s_orig.core k →
      k.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl)
    (hdi0 : di0.toNat = 3 * dlen0) (hdlen0 : dlen0 ≤ c.delayed_cap)
    (hdlim : dlim.toNat = 3 * c.delayed_cap)
    (hdok0 : DelayedWatchesOk s_orig.core sem0.scratch.delayed dlen0 not_lit.toNat)
    (hd00 : c.delayed_cap = 0 → sem0.scratch.delayed = s_orig.scratch.delayed)
    (hm0 : (FullMem c (fastPropMem s_disk sem0) ⋆ R) m0)
    (hJ_ovf : ∀ {sem' : FullState} {te' un' uf' tk' p' q' di' brk' : BitVec 64} {ovf' : Bool}
        {ovf_rw' ovf_oth' ovf_cr' : BitVec 32} {ovf_ri' : BitVec 64} {dlen' : Nat} {m' : Mem 64},
      PropLitInv c F0 F_cur
        { s_orig with scratch := { s_orig.scratch with delayed := sem'.scratch.delayed } } sem'
        not_lit.toNat off0.toNat q'.toNat p'.toNat end0.toNat →
      di'.toNat = 3 * dlen' → dlen' ≤ c.delayed_cap →
      DelayedWatchesOk s_orig.core sem'.scratch.delayed dlen' not_lit.toNat →
      (c.delayed_cap = 0 → sem'.scratch.delayed = s_orig.scratch.delayed) →
      p0.toNat ≤ p'.toNat → sem0.core.trail_end ≤ sem'.core.trail_end →
      te'.toNat = sem'.core.trail_end → un' = sem'.core.unassigned → uf' = sem'.core.unflushed →
      sem'.core.oom = 0#64 →
      (ovf' = false →
        (brk' = 0#64 → p' = end0 ∧ S13ConflEq sem0.core sem'.core) ∧
        (brk' = 1#64 → isBeyond = false ∧ PropLitConfl F_cur ign_v sem'.core) ∧
        (brk' = 0#64 ∨ brk' = 1#64)) →
      (ovf' = true → brk' = 0#64 ∧ S13ConflEq sem0.core sem'.core ∧
        2 ≤ p'.toNat - off0.toNat ∧ q'.toNat + 2 ≤ p'.toNat ∧
        end0.toNat - p'.toNat < end0.toNat - p0.toNat ∧
        ovf_cr'.toNat < 0x80000000 ∧ ovf_cr'.toNat ∈ fullArenaClauseRefsCore sem'.core ∧
        fullArenaClauseGarbCore sem'.core ovf_cr'.toNat = false ∧
        ovf_cr'.toNat + 3 + fullArenaClauseSizeCore sem'.core ovf_cr'.toNat ≤ sem'.core.arena_len ∧
        ovf_oth'.toNat < 2 * sem'.core.cur_vars ∧ ovf_rw'.toNat < 2 * sem'.core.cur_vars ∧
        ovf_rw'.toNat ≠ not_lit.toNat ∧ 2 ≤ ovf_ri'.toNat ∧
        ovf_ri'.toNat < fullArenaClauseSizeCore sem'.core ovf_cr'.toNat ∧
        ∃ l0' l1', (l0' = not_lit ∨ l1' = not_lit) ∧ ovf_oth' = l0' ^^^ l1' ^^^ not_lit ∧
          sem'.core.arena[ovf_cr'.toNat + 3]? = some l0' ∧
          sem'.core.arena[ovf_cr'.toNat + 4]? = some l1' ∧
          sem'.core.arena[ovf_cr'.toNat + 3 + ovf_ri'.toNat]? = some ovf_rw') →
      (FullMem c (fastPropMem s_disk sem') ⋆ R) m' →
      wp Γ Q X (s13OvfJump isBeyond J_ovf (.var te') (.var un') (.var uf') (.var tk') (.var p')
        (.var q') (.var di') (.var brk') (.var ovf') (.var ovf_rw') (.var ovf_oth') (.var ovf_cr')
        (.var ovf_ri')) m') :
    wp Γ Q X (s13LpLoopExpr isBeyond c.hdr c.pVals c.pWstk c.pArena c.pLevel c.pReason c.pTrail
      c.pTrailPos c.pFlags c.pPhases c.pDelayed dlim ignore_ref two_cv cur_lvl32 not_lit nl_lvl
      rec_ph bigbig end0 brk0 te0 un0 uf0 tk0 p0 q0 di0 J_ovf) m0 := by
  subst hbrk0
  unfold s13LpLoopExpr
  refine wp_loop_group (fun rem (te_p, un_p, uf_p, tk_p, p_p, q_p, di_p, ()) mlp =>
      ∃ (sem_p : FullState) (dlen_p : Nat),
        rem = end0.toNat - p_p.toNat ∧ p0.toNat ≤ p_p.toNat ∧
        sem0.core.trail_end ≤ sem_p.core.trail_end ∧
        PropLitInv c F0 F_cur
          { s_orig with scratch := { s_orig.scratch with delayed := sem_p.scratch.delayed } }
          sem_p not_lit.toNat off0.toNat q_p.toNat p_p.toNat end0.toNat ∧
        di_p.toNat = 3 * dlen_p ∧ dlen_p ≤ c.delayed_cap ∧
        DelayedWatchesOk s_orig.core sem_p.scratch.delayed dlen_p not_lit.toNat ∧
        (c.delayed_cap = 0 → sem_p.scratch.delayed = s_orig.scratch.delayed) ∧
        te_p.toNat = sem_p.core.trail_end ∧ un_p = sem_p.core.unassigned ∧
        uf_p = sem_p.core.unflushed ∧ sem_p.core.oom = 0#64 ∧
        S13ConflEq sem0.core sem_p.core ∧
        (FullMem c (fastPropMem s_disk sem_p) ⋆ R) mlp) ?_ ?_
  · rintro J_lp rem ⟨te_p, un_p, uf_p, tk_p, p_p, q_p, di_p, ⟨⟩⟩ mlp ih
      ⟨sem_p, dlen_p, rfl, hp_ge, hte_ge, hpi_p, hdi_p, hdl_p, hdok_p, hd0_p, hte_p, hun_p,
        huf_p, hoom_p, hct_p, hmlp⟩
    have hcv_p0 : sem_p.core.cur_vars = sem0.core.cur_vars :=
      hpi_p.cur_vars_eq.trans hpi0.cur_vars_eq.symm
    have hnot_p : not_lit.toNat < 2 * sem_p.core.cur_vars := hcv_p0 ▸ hnot_lt
    have htwo_p : two_cv.toNat = 2 * sem_p.core.cur_vars := by rw [htwo_cv, hcv_p0]
    have hcl_p : sem_p.core.cur_level = sem0.core.cur_level :=
      (hpi_p.ag.get FullCoreState.cur_level).trans (hpi0.ag.get FullCoreState.cur_level).symm
    have hcur_p : cur_lvl32 = BitVec.ofNat 32 sem_p.core.cur_level := by rw [hcl_p, hcur_lvl]
    have hcl32_p : sem_p.core.cur_level < 2 ^ 32 := hcl_p ▸ hcl32
    have hnl_p : sem_p.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl := hnl _ hpi_p.tr
    s13_hsplit
    · have hp_lt : p_p.toNat < end0.toNat := hc
      have ⟨hend_le, hwlen_le⟩ := hpi_p.end_lt_wcap hnot_p
      have hp_ws : p_p.toNat < (fastPropMem s_disk sem_p).core.wstk.length := by
        rw [fastPropMem_wstk, hpi_p.len.core_ok.wstk_len_arr]
        exact lt_of_lt_of_le hp_lt (le_trans hend_le hwlen_le)
      have hw0_raw_lt : p_p.toNat < sem_p.core.wstk.length := by
        rw [hpi_p.len.core_ok.wstk_len_arr]
        exact lt_of_lt_of_le hp_lt (le_trans hend_le hwlen_le)
      let w0 := (fastPropMem s_disk sem_p).core.wstk[p_p.toNat]'hp_ws
      have hw0_get : sem_p.core.wstk[p_p.toNat]? = some w0 := by
        simpa only [w0, fc_getElem_wstk] using List.getElem?_eq_getElem hw0_raw_lt
      s13_hsteps_nogrp
      dsimp only at *
      s13_hsplit
      · refine s13_lp_bin_wp (ignore_ref := ign_v) hmaxv hwc hpi_p hnot_p hp_lt hw0_get hc
          hte_p hun_p huf_p hoom_p hnl_p hmlp ?_ ?_
        · intro hnb sem' p' q' brk' m' hpi' hp' hte' hoom' hun' huf' hbrk' hcf' hm'
          subst hnb
          have hd' : sem'.scratch.delayed = sem_p.scratch.delayed := by
            have h := congrArg FullScratch.delayed hpi'.sc_eq; exact h
          exact hJ_ovf (fid_pi_rebase hpi') hdi_p hdl_p (hd' ▸ hdok_p)
            (fun h0 => hd'.trans (hd0_p h0)) (le_trans hp_ge hp')
            (by rw [← hte', hte_p]; exact hte_ge) hte'
            (hun_p.trans hun'.symm) (huf_p.trans huf'.symm) hoom'
            (fun _ => ⟨fun h => absurd h (by rw [hbrk']; decide), fun _ => ⟨rfl, hcf'⟩,
              Or.inr hbrk'⟩)
            (fun h => absurd h (by decide)) hm'
        · intro sem' te' un' uf' tk' p' q' m' hpi' hp_inc hp'_end hte_inc hte' hun' huf'
            hoom' hct' hm'
          have hd' : sem'.scratch.delayed = sem_p.scratch.delayed := by
            have h := congrArg FullScratch.delayed hpi'.sc_eq; exact h
          exact ih (end0.toNat - p'.toNat) (te', un', uf', tk', p', q', di_p, ()) m'
            (by omega)
            ⟨sem', dlen_p, rfl, le_trans hp_ge (le_of_lt hp_inc), le_trans hte_ge hte_inc,
              fid_pi_rebase hpi', hdi_p, hdl_p, hd' ▸ hdok_p, fun h0 => hd'.trans (hd0_p h0),
              hte', hun', huf', hoom'.trans hoom_p, s13ConflEq_trans hct' hct_p, hm'⟩
      · have hflag : (w0 &&& 0x80000000#32) = 0#32 := by
          simpa only [w0, BitVec.ofNat_eq_ofNat,
            show (2147483648#32 : BitVec 32) = 0x80000000#32 from rfl] using hc
        refine s13_lp_large_step_wp hmaxv har hwc hign_val hpi_p hnot_p htwo_p
          hcur_p hcl32_p hp_lt hw0_get hflag hte_p hun_p huf_p hoom_p hnl_p hdi_p hdl_p hdlim
          hdok_p hmlp ?_ ?_
        · intro sem' tk' p' q' brk' ovf' ovf_rw' ovf_oth' ovf_cr' ovf_ri' m' hpi' hte' hoom'
            hun' huf' hno hov hm'
          have hd' : sem'.scratch.delayed = sem_p.scratch.delayed := by
            have h := congrArg FullScratch.delayed hpi'.sc_eq; exact h
          refine hJ_ovf (fid_pi_rebase hpi') hdi_p hdl_p (hd' ▸ hdok_p)
            (fun h0 => hd'.trans (hd0_p h0)) ?_ (by rw [← hte', hte_p]; exact hte_ge) hte'
            (hun_p.trans hun'.symm) (huf_p.trans huf'.symm) hoom' ?_ ?_ hm'
          · cases ovf'
            · exact le_trans hp_ge (hno rfl).2.1
            · exact le_trans hp_ge (le_of_lt (hov rfl).2.2.1)
          · intro hf; obtain ⟨hb0, _, rfl, hcf⟩ := hno hf
            exact ⟨fun h => absurd h (by decide), fun _ => ⟨hb0, hcf⟩, Or.inr rfl⟩
          · intro ht
            obtain ⟨rfl, hct', hp_inc, hp'_end, hp_off, hq_le', hcr_lt, hcr_ref, hng', hcr_fit,
              hoth_lt, hrw_lt, hrw_ne, hri2, hri_lt, l0', l1', hwt', hoth', har3, har4, har_ri⟩ :=
              hov ht
            dsimp only at hp_inc hp'_end
            exact ⟨rfl, s13ConflEq_trans hct' hct_p, hp_off, hq_le', by omega, hcr_lt, hcr_ref,
              hng', hcr_fit, hoth_lt, hrw_lt, hrw_ne, hri2, hri_lt, l0', l1', hwt', hoth', har3,
              har4, har_ri⟩
        · intro sem' te' un' uf' tk' p' q' di' dlen' m' hpi' hdi' hdl' hdok' hd0' hp_inc hp'_end
            hte_inc hte' hun' huf' hoom' hct' hm'
          dsimp only at hp_inc hp'_end
          exact ih (end0.toNat - p'.toNat) (te', un', uf', tk', p', q', di', ()) m'
            (by omega)
            ⟨sem', dlen', rfl, le_trans hp_ge (le_of_lt hp_inc), le_trans hte_ge hte_inc, hpi',
              hdi', hdl', hdok', fun h0 => (hd0' h0).trans (hd0_p h0), hte', hun', huf',
              hoom'.trans hoom_p, s13ConflEq_trans hct' hct_p, hm'⟩
    · have hp_end : p_p = end0 :=
        BitVec.eq_of_toNat_eq (le_antisymm hpi_p.sw.p_le_end (Nat.le_of_not_lt hc))
      cases isBeyond <;>
      · s13_hsteps
        exact hJ_ovf hpi_p hdi_p hdl_p hdok_p hd0_p hp_ge hte_ge hte_p hun_p huf_p hoom_p
          (fun _ => ⟨fun _ => ⟨hp_end, hct_p⟩, fun h => absurd h (by decide), Or.inl rfl⟩)
          (fun h => absurd h (by decide)) hmlp
  · intro J_lp hJ_lp
    s13_hsteps
    exact hJ_lp _ (te0, un0, uf0, tk0, p0, q0, di0, ()) m0
      ⟨sem0, dlen0, rfl, Nat.le_refl _, Nat.le_refl _, hpi0, hdi0, hdlen0, hdok0, hd00, hte0,
        hun0, huf0, hoom0, ⟨rfl, rfl, rfl, rfl⟩, hm0⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S2

end
