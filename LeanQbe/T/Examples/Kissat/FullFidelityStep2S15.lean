/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7WalkProof
public import LeanQbe.T.Examples.Kissat.FullM7SearchProof2
public import LeanQbe.T.Examples.Kissat.FullM8FidV12MiscProof
public import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof1
import all LeanQbe.T.Examples.Kissat.FullM7WalkProof
import all LeanQbe.T.Examples.Kissat.FullM7SearchProof2
import all LeanQbe.T.Examples.Kissat.FullM8FidV12MiscProof
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step-2 `S1.5` Delayed-Watch Call-Site Lifts (`FullFidelityStep2S15`)

Plain `public section` (`0` `@[expose]`, `0` exposed private imports, `std3` axioms only) lifting
the remaining `full_propagate` callers inside `fidStep2Module` to
`FullM6BcpS15.fullBcpS15Spec`:
1. `full_warmup_m7_s15_wp` (`FullM7Walk.full_warmup_m7_body`, covering both `"full_warmup_m7"`
   and `"full_warmup"` in `fidStep2Module`).
2. `full_lucky_late_m7_s15_wp` (`FullM7Search.full_lucky_late_m7_body`).
3. `m8_enter_dense_s15_wp` (`FullM8FidV12.m8_enter_dense_body`; the syntactic `"full_propagate"`
   branch is unreachable after `full_flush_trail`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6CompactFlush
open LeanQbe.T.Examples.Kissat.FullM7Walk
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullM8FidV12
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

/-! ## 1. `full_warmup_m7_s15_wp` (`FullM7Walk.full_warmup_m7_body` over `fullBcpS15Spec`) -/

section WarmupS15

attribute [local c0_load] FullArenaTactics.load_full_cur_level
attribute [local c0_load] FullArenaTactics.load_full_unflushed
attribute [local c0_load] FullArenaTactics.load_full_dense_mode
attribute [local c0_load] FullArenaTactics.load_full_unassigned
attribute [local c0_load] FullArenaTactics.load_full_inconsistent
attribute [local c0_load] FullArenaTactics.load_full_oom
attribute [local c0_load] FullArenaTactics.load_full_fuel
attribute [local c0_load] FullArenaTactics.load_full_cur_vars
attribute [local c0_load] FullArenaTactics.load_full_max_vars
attribute [local c0_load] FullArenaTactics.load_full_search_ticks
attribute [local c0_load] FullArenaTactics.load_full_probing
attribute [local c0_load] FullArenaTactics.load_full_stable
attribute [local c0_load] FullArenaTactics.load_full_trail_end
attribute [local c0_load] FullArenaTactics.load_full_propagated
attribute [local c0_load] FullArenaTactics.load_full_phases_ptr
attribute [local c0_load] FullArenaTactics.load_full_phases_best_ptr
attribute [local c0_load] FullArenaTactics.load_full_phases_target_ptr
attribute [local c0_load] FullArenaTactics.load_full_frame_trail_ptr
attribute [local c0_load] FullArenaTactics.load_full_frame_dec_ptr
attribute [local c0_load] FullArenaTactics.c0_load_full_phases
attribute [local c0_load] FullArenaTactics.c0_load_full_phases_best
attribute [local c0_load] FullArenaTactics.c0_load_full_phases_target
attribute [local c0_store] FullArenaTactics.c0_store_full_cur_level
attribute [local c0_store] FullArenaTactics.store_full_probing
attribute [local c0_store] FullArenaTactics.store_full_search_ticks
attribute [local c0_store] FullArenaTactics.c0_store_full_frame_trail
attribute [local c0_store] FullArenaTactics.c0_store_full_frame_dec

private theorem m7Propagate_s15_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont rs}
    (hProp : ∀ a m Q X, fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {s : FullState} {R : Mem 64 → Prop}
    (hhdr : args.fst.val = c.hdr) (hinv : FullCoreInv c F0 s) (hd0 : s.core.dense_mode = 0#64)
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) s' m', FullCoreInv c F0 s' → FullArenaPermEq s.core s'.core →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → s.core.propagated < s.core.trail_end → s'.core.fuel.toNat < s.core.fuel.toNat) →
      (r = 1#64 → s'.core.fuel.toNat < s.core.fuel.toNat) →
      FullExtScratchPres s s' →
      s'.core.probing = s.core.probing → s'.core.cur_level = s.core.cur_level →
      s'.core.dense_mode = s.core.dense_mode → s'.core.inconsistent = s.core.inconsistent →
      s'.core.cur_vars = s.core.cur_vars → s'.core.d_cur = s.core.d_cur →
      s'.core.d_val = s.core.d_val → s'.core.arena_garbage = s.core.arena_garbage →
      s'.core.first_reducible = s.core.first_reducible → s'.core.num_irred = s.core.num_irred →
      s'.core.num_redundant = s.core.num_redundant → s'.core.num_binary = s.core.num_binary →
      s'.core.tmp_cnt = s.core.tmp_cnt → s'.core.tmp_len = s.core.tmp_len →
      s'.core.min_clr_len = s.core.min_clr_len → s'.core.min_clr_full = s.core.min_clr_full →
      s'.core.lit_mark = s.core.lit_mark → s'.core.mrk = s.core.mrk →
      s'.core.tmp = s.core.tmp → s'.core.min_clr = s.core.min_clr →
      s'.core.frame_trail = s.core.frame_trail → s'.core.frame_dec = s.core.frame_dec →
      s'.core.repr = s.core.repr → s'.core.min_stk = s.core.min_stk →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (Expr.call "full_propagate" args k) m := by
  obtain ⟨hlen, F_cur, hw⟩ := hinv
  refine wp_call_of_spec args k ?_
  refine hProp _ _ _ _ ⟨c, F0, F_cur, s, R, hhdr, hlen, hw, hd0, hm, ?_⟩
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m' _ hs' hw' _ hperm _
    hfuel hr_dom hr0 hr1 _ _ hm'
  exact hk r _ m' ⟨hs', F_cur, hw'⟩ hperm hfuel hr_dom
    (fun h0 hlt => (hr0 h0).2.2 hlt) (fun h1 => (hr1 h1).1) ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hm'

/-- `full_warmup_m7_body` over delayed-watch `FullM6BcpS15.fullBcpS15Spec`, proving
`Full.fullWarmupSpec`. -/
theorem full_warmup_m7_s15_wp (Γ : Env)
    (hNDV : ∀ a m Q X, fullNextDecVarSpec a m Q X →
      Γ "full_next_dec_var" [i64] [i64] a m Q X)
    (hAssign : ∀ a m Q X, fullAssignSpec a m Q X →
      Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hProp : ∀ a m Q X, fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hBT : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (a : Tup Val [i64]) (m : Mem 64) (Q : Post []) (X : XPost)
    (hS : fullWarmupSpec a m Q X) :
    Func.wp Γ full_warmup_m7_body a m Q X := by
  rcases a with ⟨h, ⟨⟩⟩
  rcases hS with ⟨c, F0, s, R, hhdr, hinv, hd0, hm, hQ⟩
  subst hhdr
  have hlen := hinv.lengths
  have hmax := c.hmaxv
  have hdb : Examples.LratBytes.dimacsBound = 2 ^ 28 := rfl
  have hcl0_lt : s.core.cur_level ≤ s.core.cur_vars := by
    obtain ⟨_, hw0⟩ := hinv.witness
    exact Nat.le_trans hw0.cur_level_le hlen.core_ok.trail_end_le
  dsimp only [Func.wp, full_warmup_m7_body]
  c0_hsteps_nogrp
  c0_hsteps_nogrp
  · exact m7Warmup_close_Q hQ hinv (m7ArenaPermEq_refl _) (Nat.le_refl _)
      ⟨rfl, rfl⟩ (fun h => h) (m7WarmupCoreEq_refl _) rfl hm
  · exact m7Warmup_close_Q hQ hinv (m7ArenaPermEq_refl _) (Nat.le_refl _)
      ⟨rfl, rfl⟩ (fun h => h) (m7WarmupCoreEq_refl _) rfl hm
  · exact m7Warmup_close_Q hQ hinv (m7ArenaPermEq_refl _) (Nat.le_refl _)
      ⟨rfl, rfl⟩ (fun h => h) (m7WarmupCoreEq_refl _) rfl hm
  · exact m7Warmup_close_Q hQ hinv (m7ArenaPermEq_refl _) (Nat.le_refl _)
      ⟨rfl, rfl⟩ (fun h => h) (m7WarmupCoreEq_refl _) rfl hm
  · exact m7Warmup_close_Q hQ hinv (m7ArenaPermEq_refl _) (Nat.le_refl _)
      ⟨rfl, rfl⟩ (fun h => h) (m7WarmupCoreEq_refl _) rfl hm
  · exact m7Warmup_close_Q hQ hinv (m7ArenaPermEq_refl _) (Nat.le_refl _)
      ⟨rfl, rfl⟩ (fun h => h) (m7WarmupCoreEq_refl _) rfl hm
  · exact m7Warmup_close_Q hQ hinv (m7ArenaPermEq_refl _) (Nat.le_refl _)
      ⟨rfl, rfl⟩ (fun h => h) (m7WarmupCoreEq_refl _) rfl hm
  have hcv_le_entry : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
  have hcl_eq0 : BitVec.ofNat 64 s.core.cur_level = 0 := by assumption
  have hcl_entry : s.core.cur_level = 0 := by
    have h := congrArg BitVec.toNat hcl_eq0
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show s.core.cur_level < 2 ^ 64 by omega)] using h
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64])
    (fun _ mE => ∃ sE, FullCoreInv c F0 sE ∧ FullArenaPermEq s.core sE.core ∧
      sE.core.fuel.toNat ≤ s.core.fuel.toNat ∧ FullExtScratchPres s sE ∧
      M7WarmupCoreEq s.core sE.core ∧ sE.core.dense_mode = 0#64 ∧ (FullMem c sE ⋆ R) mE)
    (fun _ _ mE ⟨sE, hinvE, hpermE, hfuelE, hpresE, heqE, _, _hmE⟩ => by
      c0_hsteps_nogrp
      let sE1 : FullState := { sE with core := { sE.core with probing := 1#64 } }
      have hinvE1 : FullCoreInv c F0 sE1 := m7CoreInv_with_probing hinvE
      have hpermE1 : FullArenaPermEq s.core sE1.core := m7ArenaPermEq_with_probing hpermE
      refine m7Backtrack_call hBT rfl hinvE1 (Nat.zero_le _) ‹_› fun sB mB hinvB hpermB hclB
          hfuelB _ hdB _ hcvB halB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpresB hmB => ?_
      c0_hsteps
      let sF : FullState := FullState.mk
        { sB.core with probing := s.core.probing }
        { sB.scratch with search_ticks := s.scratch.search_ticks }
      have hinvF : FullCoreInv c F0 sF := m7CoreInv_with_st (m7CoreInv_with_probing hinvB)
      have hpermF : FullArenaPermEq s.core sF.core :=
        m7ArenaPermEq_with_probing (m7ArenaPermEq_trans hpermE1 hpermB)
      have hclF : sF.core.cur_level = s.core.cur_level := by
        show sB.core.cur_level = s.core.cur_level
        rw [hclB, hcl_entry]; simp
      have hfuelF : sF.core.fuel.toNat ≤ s.core.fuel.toNat := by
        change sB.core.fuel.toNat ≤ s.core.fuel.toNat
        rw [hfuelB]; exact hfuelE
      have heqF : M7WarmupCoreEq s.core sF.core := by
        refine m7WarmupCoreEq_trans heqE ?_
        constructor <;> assumption
      exact m7Warmup_close_Q hQ hinvF hpermF hfuelF
        ⟨hpresB.1.trans hpresE.1, hpresB.2.trans hpresE.2⟩ (fun h => h) heqF hclF ‹_›)
    (fun J46E hJ46E => by
      refine wp_loop_group (ts := [i64])
        (fun fn ⟨k, ⟨⟩⟩ mL => ∃ sL, k.toNat ≤ s.core.cur_vars ∧ fn = s.core.cur_vars - k.toNat ∧
          FullCoreInv c F0 sL ∧ FullArenaPermEq s.core sL.core ∧
          sL.core.fuel.toNat ≤ s.core.fuel.toNat ∧ FullExtScratchPres s sL ∧
          M7WarmupCoreEq s.core sL.core ∧ sL.core.dense_mode = 0#64 ∧ (FullMem c sL ⋆ R) mL)
        ?_ ?_
      · intro J46 fn ⟨k, ⟨⟩⟩ mL hJ46
          ⟨sL, hk_le, hfn, hinvL, hpermL, hfuelL, hpresL, heqL, hdL, hmL⟩
        have hcvL : sL.core.cur_vars = s.core.cur_vars := heqL.cur_vars_eq
        have hincL : sL.core.inconsistent = s.core.inconsistent := heqL.inconsistent_eq
        have hlenL := hinvL.lengths
        c0_hsplit
        · have hk_lt_bv : k.toNat < s.core.cur_vars % 2 ^ 64 := by assumption
          have hk_lt : k.toNat < s.core.cur_vars := by
            rw [Nat.mod_eq_of_lt (by omega)] at hk_lt_bv
            exact hk_lt_bv
          have hk1 : (k + 1#64).toNat = k.toNat + 1 :=
            m7p_bv64_add1_lt hk_lt (by omega)
          have hlt_n : s.core.cur_vars - (k.toNat + 1) < fn := by omega
          c0_hsplit
          · c0_hsplit
            · c0_hsplit
              · c0_hsteps_nogrp
                refine m7NextDecVar_call hNDV rfl hlenL hmL
                  fun r sL2 mL2 hcoreL2 hlenL2 hpresL2 hresL2 hmL2 => ?_
                have hinvL2 : FullCoreInv c F0 sL2 :=
                  ⟨hlenL2, by rw [hcoreL2]; exact hinvL.witness⟩
                have hpermL2 : FullArenaPermEq s.core sL2.core := by
                  rw [hcoreL2]; exact hpermL
                have hfuelL2 : sL2.core.fuel.toNat ≤ s.core.fuel.toNat := by
                  rw [hcoreL2]; exact hfuelL
                have hpresL20 : FullExtScratchPres s sL2 :=
                  ⟨hpresL2.1.trans hpresL.1, hpresL2.2.trans hpresL.2⟩
                have heqL2 : M7WarmupCoreEq s.core sL2.core := by
                  rw [hcoreL2]; exact heqL
                have hdL2 : sL2.core.dense_mode = 0#64 := by
                  rw [hcoreL2]; exact hdL
                c0_hsteps_nogrp
                c0_hsplit
                · c0_hsteps
                  exact hJ46E (k, ()) mL2
                    ⟨sL2, hinvL2, hpermL2, hfuelL2, hpresL20, heqL2, hdL2, hmL2⟩
                · have hr_spec : r.toNat < sL2.core.cur_vars ∧
                      sL2.core.vals[2 * r.toNat]?.getD 0#8 = 0#8 := by
                    rcases hresL2 with rfl | hok
                    · exact absurd rfl hc
                    · simpa [hcoreL2] using hok
                  have hr_lt : r.toNat < c.max_vars := by
                    have := hlenL2.core_ok.cur_vars_le; omega
                  have hr_ph : r.toNat < sL2.scratch.phases.length := by
                    rw [hlenL2.scratch_ok.phases_len]; exact hr_lt
                  have hr_pb : r.toNat < sL2.scratch.phases_best.length := by
                    rw [hlenL2.scratch_ok.phases_best_len]; exact hr_lt
                  have hr_pt : r.toNat < sL2.scratch.phases_target.length := by
                    rw [hlenL2.scratch_ok.phases_target_len]; exact hr_lt
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [i8])
                    (fun _ m61 => (FullMem c sL2 ⋆ R) m61)
                    (fun _ ⟨ph, ⟨⟩⟩ m61 hm61 => by
                      c0_hsteps_nogrp
                      refine wp_join_group (ts := [i32])
                        (fun ⟨lit, ⟨⟩⟩ m62 =>
                          (lit.toNat = 2 * r.toNat ∨ lit.toNat = 2 * r.toNat + 1) ∧
                          (FullMem c sL2 ⋆ R) m62)
                        (fun _ ⟨lit, ⟨⟩⟩ m62 ⟨hlit_eq, hm62⟩ => by
                          have hcl_L2 : sL2.core.cur_level ≤ sL2.core.cur_vars := by
                            obtain ⟨_, hwL2⟩ := hinvL2.witness
                            exact Nat.le_trans hwL2.cur_level_le hlenL2.core_ok.trail_end_le
                          c0_hsplit
                          · c0_hsteps
                            exact hJ46E (k, ()) m62
                              ⟨sL2, hinvL2, hpermL2, hfuelL2, hpresL20, heqL2, hdL2, hm62⟩
                          · have hmv := c.hmaxv
                            have hcv := hlenL2.core_ok.cur_vars_le
                            have hnlvl_le : sL2.core.cur_level + 1 ≤ c.max_vars := by
                              unfold Examples.LratBytes.dimacsBound at hmv
                              change ¬ c.max_vars % 2 ^ 64 <
                                  (sL2.core.cur_level + 1) % 2 ^ 64 at hc
                              have h1 : c.max_vars % 2 ^ 64 = c.max_vars :=
                                Nat.mod_eq_of_lt (by omega)
                              have h2 : (sL2.core.cur_level + 1) % 2 ^ 64 =
                                  sL2.core.cur_level + 1 :=
                                Nat.mod_eq_of_lt (by omega)
                              rw [h1, h2] at hc
                              omega
                            have hnlvl_ft : sL2.core.cur_level + 1 <
                                sL2.core.frame_trail.length := by
                              rw [hlenL2.core_ok.frame_trail_len]; omega
                            have hnlvl_fd : sL2.core.cur_level + 1 <
                                sL2.core.frame_dec.length := by
                              rw [hlenL2.core_ok.frame_dec_len]; omega
                            c0_hsteps_nogrp
                            let nlvl := sL2.core.cur_level + 1
                            let ft' := sL2.core.frame_trail.set nlvl
                              (BitVec.ofNat 32 sL2.core.trail_end)
                            let fd' := sL2.core.frame_dec.set nlvl lit
                            let sDec : FullState := { sL2 with core := { sL2.core with
                              frame_trail := ft', frame_dec := fd', cur_level := nlvl } }
                            have hlenDec : sDec.LengthsOk c :=
                              ⟨m7CoreLengths_decide hlenL2.core_ok
                                (by simp [ft', hlenL2.core_ok.frame_trail_len])
                                (by simp [fd', hlenL2.core_ok.frame_dec_len]),
                                hlenL2.scratch_ok⟩
                            have hdec_probe := full_decide_preserves_fullCore
                              (unas' := sL2.core.unassigned) (unfl' := sL2.core.unflushed)
                              hinvL2 hlenL2.scratch_ok hlenL2.core_ok.flags_len
                              hr_spec.1 hr_spec.2 hlit_eq
                            have hval0_lit : sL2.core.vals[lit.toNat]?.getD 0#8 = 0#8 :=
                              hdec_probe.2.1
                            have hte_lt : sL2.core.trail_end < sL2.core.cur_vars :=
                              hdec_probe.2.2.1
                            have hguard_false :
                                ¬(sDec.core.cur_vars ≤ lit.toNat / 2 ∨
                                  c.max_vars ≤ sDec.core.trail_end ∨
                                  sDec.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
                              have hv_eq : lit.toNat / 2 = r.toNat := by omega
                              have hcv_le2 := hlenL2.core_ok.cur_vars_le
                              intro hor
                              rcases hor with h1 | h2 | h3
                              · exact absurd (hv_eq ▸ h1) (Nat.not_le.mpr hr_spec.1)
                              · exact absurd h2
                                  (Nat.not_le.mpr (Nat.lt_of_lt_of_le hte_lt hcv_le2))
                              · exact h3 hval0_lit
                            have hte_bv : (BitVec.ofNat 64 sL2.core.trail_end).truncate 32 =
                                BitVec.ofNat 32 sL2.core.trail_end := by
                              apply BitVec.eq_of_toNat_eq; simp
                            have hcl_lt64 : sL2.core.cur_level < 2 ^ 64 := by
                              have := hcl_L2; have := hlenL2.core_ok.cur_vars_le
                              have := c.hmaxv; unfold Examples.LratBytes.dimacsBound at this; omega
                            have hnlvl_lt64 : sL2.core.cur_level + 1 < 2 ^ 64 := by
                              have := hcl_L2; have := hlenL2.core_ok.cur_vars_le
                              have := c.hmaxv; unfold Examples.LratBytes.dimacsBound at this; omega
                            have hnlvl_nat :
                                (BitVec.ofNat 64 sL2.core.cur_level + 1#64).toNat = nlvl := by
                              dsimp [nlvl]
                              rw [BitVec.toNat_ofNat,
                                Nat.mod_eq_of_lt hcl_lt64,
                                Nat.mod_eq_of_lt hnlvl_lt64]
                            refine wp_call_of_spec _ _ (hAssign _ _ _ _ ?_)
                            refine ⟨c, sDec, R, rfl, hlenDec,
                              (by dsimp [sDec, nlvl]; have := hnlvl_le; have := c.hmaxv;
                                  unfold Examples.LratBytes.dimacsBound at this; omega),
                              (by simp only [sDec, nlvl, ft', fd', ← hnlvl_nat, ← hte_bv]
                                  exact hm), ?_⟩
                            split
                            · rename_i h; exact False.elim (hguard_false h)
                            · intro v rsn' unfl' flagsA unassA phasesA mA hflA hphA sA' hmA
                              have hdec_ok := full_decide_preserves_fullCore
                                (unas' := unassA) (unfl' := sL2.core.unflushed) hinvL2
                                (m7ScratchLengths_with_phases hlenL2.scratch_ok hphA) hflA
                                hr_spec.1 hr_spec.2 hlit_eq
                              let sA : FullState :=
                                { core := { sL2.core with
                                    unassigned := unassA,
                                    trail_end := sL2.core.trail_end + 1,
                                    vals := (sL2.core.vals.set lit.toNat 1#8).set
                                      (lit.toNat ^^^ 1) 255#8,
                                    flags := flagsA,
                                    lvl := sL2.core.lvl.set (lit.toNat / 2)
                                      (BitVec.ofNat 32 nlvl),
                                    rsns := sL2.core.rsns.set (lit.toNat / 2) 4294967295#32,
                                    trl := sL2.core.trl.set sL2.core.trail_end lit,
                                    trail_pos := sL2.core.trail_pos.set (lit.toNat / 2)
                                      (BitVec.ofNat 32 sL2.core.trail_end),
                                    frame_trail := ft', frame_dec := fd', cur_level := nlvl },
                                  scratch := { sL2.scratch with phases := phasesA } }
                              have hsA_eq : sA = sA' := by
                                dsimp [sA, sA', sDec, v, rsn', unfl']
                              rw [← hsA_eq] at hmA
                              have hinvA : FullCoreInv c F0 sA := hdec_ok.1
                              have hpermA : FullArenaPermEq s.core sA.core := hpermL2
                              have hfuelA : sA.core.fuel.toNat ≤ s.core.fuel.toNat := hfuelL2
                              have hpresA : FullExtScratchPres s sA := hpresL20
                              have heqA : M7WarmupCoreEq s.core sA.core :=
                                ⟨heqL2.1, heqL2.2, heqL2.3, heqL2.4, heqL2.5, heqL2.6, heqL2.7,
                                  heqL2.8, heqL2.9, heqL2.10, heqL2.11, heqL2.12, heqL2.13,
                                  heqL2.14, heqL2.15, heqL2.16, heqL2.17, heqL2.18, heqL2.19,
                                  heqL2.20, heqL2.21⟩
                              have hdA : sA.core.dense_mode = 0#64 := hdL2
                              c0_hsteps_nogrp
                              refine wp_join_group (ts := [])
                                (fun _ mJ => ∃ sJ, FullCoreInv c F0 sJ ∧
                                  FullArenaPermEq s.core sJ.core ∧
                                  sJ.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                  FullExtScratchPres s sJ ∧ M7WarmupCoreEq s.core sJ.core ∧
                                  sJ.core.dense_mode = 0#64 ∧ (FullMem c sJ ⋆ R) mJ)
                                (fun _ ⟨⟩ mJ
                                    ⟨sJ, hinvJ, hpermJ, hfuelJ, hpresJ, heqJ, hdJ, hmJ⟩ => by
                                  c0_hsteps
                                  exact hJ46 (s.core.cur_vars - (k.toNat + 1)) (k + 1#64, ())
                                    mJ hlt_n
                                    ⟨sJ, by rw [hk1]; omega, by rw [hk1], hinvJ, hpermJ,
                                      hfuelJ, hpresJ, heqJ, hdJ, hmJ⟩)
                                (fun J75 hJ75 => by
                                  refine wp_loop_group (ts := [])
                                    (fun fn _ mP => ∃ sP, fn = sP.core.fuel.toNat ∧
                                      FullCoreInv c F0 sP ∧ FullArenaPermEq s.core sP.core ∧
                                      sP.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                      FullExtScratchPres s sP ∧ M7WarmupCoreEq s.core sP.core ∧
                                      sP.core.dense_mode = 0#64 ∧ (FullMem c sP ⋆ R) mP) ?_ ?_
                                  · intro J_prop fn ⟨⟩ mP hJ_prop
                                      ⟨sP, hfnP, hinvP, hpermP, hfuelP, hpresP, heqP, hdP, hmP⟩
                                    have hlenP := hinvP.lengths
                                    c0_hsplit
                                    · have hprop_lt : sP.core.propagated < sP.core.trail_end := by
                                        have := hlenP.core_ok.trail_end_le
                                        have := hlenP.core_ok.propagated_le
                                        have := hlenP.core_ok.cur_vars_le
                                        have := c.hmaxv
                                        unfold Examples.LratBytes.dimacsBound at this
                                        change (BitVec.ofNat 64 sP.core.propagated).toNat <
                                            (BitVec.ofNat 64 sP.core.trail_end).toNat at hc
                                        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                                          Nat.mod_eq_of_lt (by omega),
                                          Nat.mod_eq_of_lt (by omega)] at hc
                                        exact hc
                                      c0_hsplit
                                      · c0_hsplit
                                        · c0_hsteps_nogrp
                                          refine m7Propagate_s15_call hProp rfl hinvP hdP hmP
                                            fun r sP2 mP2 hinvP2 hpermP2 hfuelP2 hr_dom hr0_fuel
                                              hr1_fuel hpresP2 hprobP2 hclP2 hdP2 hincP2 hcvP2
                                              hd1P2 hd2P2 hgarbP2 hagP2 hfrP2 hniP2 hnrP2 hnbP2
                                              htcP2 htlP2 hmclP2 hmcfP2 hlmP2 hmrkP2 htmpP2 hmcP2
                                              hfdP2 hrepP2 hmstkP2 hmP2 => ?_
                                          have hpermP0 := m7ArenaPermEq_trans hpermP hpermP2
                                          have hfuelP0 : sP2.core.fuel.toNat ≤ s.core.fuel.toNat :=
                                            Nat.le_trans hfuelP2 hfuelP
                                          have hpresP0 : FullExtScratchPres s sP2 :=
                                            ⟨hpresP2.1.trans hpresP.1, hpresP2.2.trans hpresP.2⟩
                                          have heqP0 : M7WarmupCoreEq s.core sP2.core := by
                                            refine m7WarmupCoreEq_trans heqP ?_
                                            exact ⟨hd1P2, hd2P2, hcvP2, hpermP2.1,
                                              hgarbP2, hagP2, hfrP2, hniP2, hnrP2, hnbP2, htcP2,
                                              htlP2, hmclP2, hdP2, hincP2, hmcfP2, hlmP2, hmrkP2,
                                              htmpP2, hrepP2, hmstkP2⟩
                                          have hdP0 : sP2.core.dense_mode = 0#64 := by
                                            rw [hdP2, hdP]
                                          c0_hsplit
                                          · c0_hsteps; exact hJ75 () mP2
                                              ⟨sP2, hinvP2, hpermP0, hfuelP0, hpresP0, heqP0,
                                                hdP0, hmP2⟩
                                          · have hlt_fuel : sP2.core.fuel.toNat < fn := by
                                              rw [hfnP]
                                              rcases hr_dom with rfl | rfl | rfl
                                              · exact hr0_fuel rfl hprop_lt
                                              · exact hr1_fuel rfl
                                              · exact absurd rfl hc
                                            c0_hsteps
                                            exact hJ_prop sP2.core.fuel.toNat () mP2 hlt_fuel
                                              ⟨sP2, rfl, hinvP2, hpermP0, hfuelP0, hpresP0, heqP0,
                                                hdP0, hmP2⟩
                                        · c0_hsteps; exact hJ75 () mP
                                            ⟨sP, hinvP, hpermP, hfuelP, hpresP, heqP, hdP, hmP⟩
                                      · c0_hsteps; exact hJ75 () mP
                                          ⟨sP, hinvP, hpermP, hfuelP, hpresP, heqP, hdP, hmP⟩
                                    · c0_hsteps; exact hJ75 () mP
                                        ⟨sP, hinvP, hpermP, hfuelP, hpresP, heqP, hdP, hmP⟩
                                  · intro J_prop hJ_prop
                                    c0_hsteps
                                    exact hJ_prop sA.core.fuel.toNat () mA
                                      ⟨sA, rfl, hinvA, hpermA, hfuelA, hpresA, heqA, hdA, hmA⟩))
                        (fun J62 hJ62 => by
                          have hr29 : r.toNat < 2 ^ 29 := by
                            have := hr_lt
                            have := c.hmaxv
                            unfold Examples.LratBytes.dimacsBound at this
                            omega
                          c0_hsplit
                          · c0_hsteps
                            exact hJ62
                              (((r <<< BitVec.signExtend 64 1#32).truncate 32 ||| 1#32), ()) _
                              ⟨Or.inr (m7p_lit_neg_shl64 hr29), hm61⟩
                          · c0_hsteps
                            exact hJ62 (((r <<< BitVec.signExtend 64 1#32).truncate 32), ()) _
                              ⟨Or.inl (m7p_lit_pos_shl64 hr29), hm61⟩))
                    (fun J61 hJ61 => by
                      c0_hsplit
                      · c0_hsplit
                        · c0_hsteps; exact hJ61 _ _ hmL2
                        · c0_hsteps; exact hJ61 _ _ hmL2
                      · c0_hsteps; exact hJ61 _ _ hmL2)
              · c0_hsteps
                exact hJ46E (k, ()) mL ⟨sL, hinvL, hpermL, hfuelL, hpresL, heqL, hdL, hmL⟩
            · c0_hsteps
              exact hJ46E (k, ()) mL ⟨sL, hinvL, hpermL, hfuelL, hpresL, heqL, hdL, hmL⟩
          · c0_hsteps
            exact hJ46E (k, ()) mL ⟨sL, hinvL, hpermL, hfuelL, hpresL, heqL, hdL, hmL⟩
        · c0_hsteps
          exact hJ46E (k, ()) mL ⟨sL, hinvL, hpermL, hfuelL, hpresL, heqL, hdL, hmL⟩
      · intro J46 hJ46
        c0_hsteps
        exact hJ46 s.core.cur_vars (0#64, ()) m
          ⟨s, Nat.zero_le _, by simp, hinv, m7ArenaPermEq_refl _, Nat.le_refl _, ⟨rfl, rfl⟩,
            m7WarmupCoreEq_refl _, hd0, hm⟩)

end WarmupS15

/-! ## 2. `full_lucky_late_m7_s15_wp` (`FullM7Search` over `fullBcpS15Spec`) -/

section LuckyLateS15

private theorem fid2_strip_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
private theorem fid2_strip_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
private theorem fid2_strip_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

local macro "fid2_strip" : tactic =>
  `(tactic| first | apply fid2_strip_32_64 | apply fid2_strip_8_32 | apply fid2_strip_8_64)
local macro "fid2_unmdata" : tactic =>
  `(tactic| first | change LeanQbe.T.Func.wp _ _ _ _ _ _ | change LeanQbe.T.wp _ _ _ _ _)
local elab "fid2_hsteps_ns" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 10000
local macro "fid2_steps_raw" : tactic =>
  `(tactic| (
    (try fid2_unmdata)
    (repeat fid2_strip)
    fid2_hsteps_ns
    repeat (any_goals (fid2_strip; repeat fid2_strip); fid2_hsteps_ns)))
local macro "fid2_jnz_split" h:ident : tactic =>
  `(tactic|
    ((try fid2_unmdata); rw [wp_jnz]; dsimp only [Arg.val]
     refine ⟨fun $h => ?_, fun $h => ?_⟩))
local macro "fid2_call" hSpec:term : tactic =>
  `(tactic| (fid2_unmdata; c0_call $hSpec))

/-- `full_lucky_late_m7_body` over delayed-watch `FullM6BcpS15.fullBcpS15Spec`, proving
`FullM7Search.m7LuckyLateSpec`. -/
theorem full_lucky_late_m7_s15_wp (Γ : Env)
    (hPolar : EnvSpec Γ "full_lucky_polar_m7" fullLuckyPolarSpec)
    (hScan : EnvSpec Γ "full_lucky_scan" fullLuckyScanSpec)
    (hAssign : EnvSpec Γ "full_assign" fullAssignSpec)
    (hBt : EnvSpec Γ "full_backtrack" fullBacktrackSpec)
    (hProp : EnvSpec Γ "full_propagate" fullBcpS15Spec) :
    ∀ a m Q X, m7LuckyLateSpec a m Q X → Func.wp Γ full_lucky_late_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hspec
  obtain ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩ := m7LuckyLateSpec_elim hspec
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  unfold Func.wp full_lucky_late_m7_body
  fid2_steps_raw
  fid2_jnz_split hinc
  · have hinc_ne : s.core.inconsistent ≠ 0#64 := by simpa using hinc
    have hunsat : F0.Unsat := hsp.inconsistent_unsat hinc_ne
    fid2_steps_raw
    let s' : FullState := { s with core := { s.core with probing := 0#64 } }
    have hsp' : FullSparseInv c F0 s' := fullSparseInv_with_probing hsp 0#64
    exact hQ 20#64 s' m hsp'.1.lengths (Or.inr (Or.inr (Or.inr rfl))) (Nat.le_refl _) rfl
      (fun _ => hunsat) (fun h => by rcases h with h | h <;> cases h)
      (fun h => by cases h) (by assumption)
  · fid2_steps_raw
    refine wp_join_group (ts := [])
      (fun _ m1 => ∃ s1 : FullState, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
        s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1) ?_ ?_
    · rintro J1 ⟨⟩ m1 ⟨s1, hsp1, hcl1_0, hfl1, hm1⟩
      rw [Blocks.get_here]
      fid2_steps_raw
      refine wp_join_group (ts := [])
        (fun _ m2 => ∃ s2 : FullState, FullSparseInv c F0 s2 ∧ s2.core.cur_level = 0 ∧
          s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s2 ⋆ R) m2) ?_ ?_
      · rintro J2 ⟨⟩ m2 ⟨s2, hsp2, hcl2_0, hfl2, hm2⟩
        rw [Blocks.get_here]
        fid2_steps_raw
        let s3 : FullState := { s2 with core := { s2.core with probing := 1#64 } }
        have hsp3 : FullSparseInv c F0 s3 := fullSparseInv_with_probing hsp2 1#64
        have hcl3_0 : s3.core.cur_level = 0 := hcl2_0
        fid2_call hPolar
        refine ⟨c, F0, s3, R, rfl, hsp3.1, by assumption, ?_⟩
        intro pol hpol
        fid2_steps_raw
        fid2_jnz_split hpol0
        · fid2_steps_raw
          refine wp_loop_inv (ts := [i64])
            (fun (idx, ()) ml => ∃ st : FullState,
              idx.toNat ≤ s3.core.cur_vars ∧ st.core.cur_vars = s3.core.cur_vars ∧
              FullSparseInv c F0 st ∧ st.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullMem c st ⋆ R) ml)
            (fun (idx, ()) _ => s3.core.cur_vars - idx.toNat) ?_ ?_
          · intro Jloop hJloop
            fid2_steps_raw
            exact hJloop (0#64, ()) _ ⟨s3, Nat.zero_le _, rfl, hsp3, hfl2, by assumption⟩
          · rintro Jloop ⟨idx, ⟨⟩⟩ ml ⟨st, hidx_le, hcv_eq, hst, hfl, hml⟩ hJloop
            rw [Blocks.get_here]
            have hcv_le := hst.1.lengths.core_ok.cur_vars_le
            have hcl_ok := hst.1.lengths.core_ok
            fid2_steps_raw
            fid2_jnz_split hidx_lt_cv
            · have hidx_lt : idx.toNat < st.core.cur_vars := by
                have hlt : idx.toNat < st.core.cur_vars % 2 ^ 64 := by
                  simpa [BitVec.ult] using hidx_lt_cv
                rw [Nat.mod_eq_of_lt (by omega)] at hlt; exact hlt
              have hidx1_nat : (idx + 1#64).toNat = idx.toNat + 1 :=
                p2_bv64_add1_toNat (by omega)
              have hidx_fl : idx.toNat < st.core.flags.length := by rw [hcl_ok.flags_len]; omega
              have h2v : (idx <<< 1#64).toNat = 2 * idx.toNat :=
                M7SearchTactics.bv64_shl1_toNat (by omega)
              have hidx2_vl : (idx <<< 1#64).toNat < st.core.vals.length := by
                rw [h2v, hcl_ok.vals_len]; omega
              fid2_steps_raw
              refine wp_join_group (ts := []) (fun _ mn =>
                ∃ st' : FullState, st'.core.cur_vars = s3.core.cur_vars ∧
                  FullSparseInv c F0 st' ∧ st'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                  (FullMem c st' ⋆ R) mn) ?_ ?_
              · rintro Jnext ⟨⟩ mn ⟨st', hcv', hst', hfl', hmn⟩
                rw [Blocks.get_here]
                fid2_steps_raw
                exact hJloop (idx + 1#64, ()) mn (by dsimp only; rw [hidx1_nat]; omega)
                  ⟨st', by rw [hidx1_nat]; omega, hcv', hst', hfl', hmn⟩
              · intro Jnext hJnext
                fid2_steps_raw
                fid2_jnz_split hact
                · fid2_steps_raw
                  fid2_jnz_split hval0_b
                  · have hval0 : st.core.vals[2 * idx.toNat]?.getD 0#8 = 0#8 := by
                      rw [← h2v, List.getElem?_eq_getElem hidx2_vl, Option.getD_some]
                      exact p2_sext32_eq0 _ (by simpa using hval0_b)
                    fid2_steps_raw
                    fid2_jnz_split hfuel0
                    · fid2_steps_raw
                      refine p2_lucky_bt0_wp hBt hst hml
                        fun s_bt mb _ hfl_b hsp_b hcl0_b hmb => ?_
                      fid2_steps_raw
                      let s' : FullState := { s_bt with core := { s_bt.core with probing := 0#64 } }
                      have hsp' : FullSparseInv c F0 s' := fullSparseInv_with_probing hsp_b 0#64
                      have hfl' : s'.core.fuel.toNat ≤ s.core.fuel.toNat := by
                        change s_bt.core.fuel.toNat ≤ s.core.fuel.toNat; rw [hfl_b]; exact hfl
                      exact hQ 2#64 s' _ hsp'.1.lengths (Or.inr (Or.inl rfl)) hfl' rfl
                        (fun h => by cases h) (fun _ => ⟨hsp', hcl0_b⟩)
                        (fun h => by cases h) (by assumption)
                    · have hfl_ne : st.core.fuel ≠ 0#64 := by simpa using hfuel0
                      have hfl_sub : (st.core.fuel - 1#64).toNat = st.core.fuel.toNat - 1 :=
                        p2_bv64_sub1_toNat hfl_ne
                      let st1 : FullState :=
                        { st with core := { st.core with fuel := st.core.fuel - 1#64 } }
                      have hst1 : FullSparseInv c F0 st1 :=
                        fullSparseInv_with_fuel hst (st.core.fuel - 1#64)
                      have hfl1 : st1.core.fuel.toNat ≤ s.core.fuel.toNat := by
                        change (st.core.fuel - 1#64).toNat ≤ s.core.fuel.toNat
                        rw [hfl_sub]; omega
                      fid2_steps_raw
                      refine wp_join_group (ts := [i32]) (fun (lit, _) mlit =>
                        (FullMem c st1 ⋆ R) mlit ∧
                          (lit.toNat = 2 * idx.toNat ∨ lit.toNat = 2 * idx.toNat + 1)) ?_ ?_
                      · rintro Jlit ⟨lit, ⟨⟩⟩ mlit ⟨hmlit, hlit_eq⟩
                        rw [Blocks.get_here]
                        obtain ⟨_, hw_1⟩ := hst1.1.witness
                        have hcv1_le := hst1.1.lengths.core_ok.cur_vars_le
                        have hcl1_le : st1.core.cur_level ≤ st1.core.trail_end := hw_1.cur_level_le
                        have hte1_le : st1.core.trail_end ≤ st1.core.cur_vars :=
                          hst1.1.lengths.core_ok.trail_end_le
                        have hnlvl_bv : (BitVec.ofNat 64 st1.core.cur_level + 1#64).toNat =
                            st1.core.cur_level + 1 := by
                          have := p2_bv64_ofNat_toNat (n := st1.core.cur_level) (by omega)
                          bv_omega
                        fid2_steps_raw
                        fid2_jnz_split hnlvl_gt
                        · fid2_steps_raw
                          refine p2_lucky_bt0_wp hBt hst1 hmlit
                            fun s_bt mb _ hfl_b hsp_b hcl0_b hmb => ?_
                          fid2_steps_raw
                          let s' : FullState :=
                            { s_bt with core := { s_bt.core with probing := 0#64 } }
                          have hsp' : FullSparseInv c F0 s' :=
                            fullSparseInv_with_probing hsp_b 0#64
                          have hfl' : s'.core.fuel.toNat ≤ s.core.fuel.toNat := by
                            change s_bt.core.fuel.toNat ≤ s.core.fuel.toNat
                            rw [hfl_b]; exact hfl1
                          exact hQ 0#64 s' _ hsp'.1.lengths (Or.inl rfl) hfl' rfl
                            (fun h => by cases h) (fun _ => ⟨hsp', hcl0_b⟩)
                            (fun h => by cases h) (by assumption)
                        · have hdec1 := p2_fullSparseInv_of_m7Decide hst1
                            hst1.1.lengths.core_ok.flags_len
                            hst1.1.lengths.scratch_ok.phases_len hidx_lt hval0 hlit_eq
                            (flags' := st1.core.flags) (unas' := st1.core.unassigned)
                            (unfl' := st1.core.unflushed) (phases' := st1.scratch.phases)
                          have hun := hdec1.2.1
                          have hte_lt := hdec1.2.2.1
                          have hnlvl_le := hdec1.2.2.2
                          let nlvl := st1.core.cur_level + 1
                          let ftrl' := st1.core.frame_trail.set nlvl
                            (BitVec.ofNat 32 st1.core.trail_end)
                          let fdec' := st1.core.frame_dec.set nlvl lit
                          let s_dec : FullState :=
                            { st1 with core := { st1.core with
                                cur_level := nlvl, frame_trail := ftrl', frame_dec := fdec' } }
                          have hftrl1 := hst1.1.lengths.core_ok.frame_trail_len
                          have hfdec1 := hst1.1.lengths.core_ok.frame_dec_len
                          have hdec_len : s_dec.LengthsOk c :=
                            ⟨{ hst1.1.lengths.core_ok with
                                frame_trail_len := by
                                  dsimp only [s_dec, ftrl']; rw [List.length_set]; exact hftrl1
                                frame_dec_len := by
                                  dsimp only [s_dec, fdec']; rw [List.length_set]; exact hfdec1 },
                              hst1.1.lengths.scratch_ok⟩
                          have hte_bv : (BitVec.ofNat 64 st1.core.trail_end).setWidth 32 =
                              BitVec.ofNat 32 st1.core.trail_end := by
                            apply BitVec.eq_of_toNat_eq
                            rw [BitVec.toNat_setWidth, p2_bv64_ofNat_toNat (by omega),
                              M7SearchTactics.bv32_ofNat_toNat (by omega),
                              Nat.mod_eq_of_lt (by omega)]
                          have hnlvl_lt_len :
                              (BitVec.ofNat 64 st1.core.cur_level + 1#64).toNat <
                                st1.core.frame_trail.length := by
                            rw [hnlvl_bv, hftrl1]; omega
                          have hnlvl_lt_dlen :
                              (BitVec.ofNat 64 st1.core.cur_level + 1#64).toNat <
                                st1.core.frame_dec.length := by
                            rw [hnlvl_bv, hfdec1]; omega
                          fid2_steps_raw
                          have hidx_lt1 : idx.toNat < st1.core.cur_vars := hidx_lt
                          have hte_lt' : st1.core.trail_end < st1.core.cur_vars := hte_lt
                          have hte_max : st1.core.trail_end < c.max_vars :=
                            Nat.lt_of_lt_of_le hte_lt' hcv1_le
                          have hlit_v : lit.toNat / 2 = idx.toNat := by omega
                          have hng : ¬ (s_dec.core.cur_vars ≤ lit.toNat / 2 ∨
                              c.max_vars ≤ s_dec.core.trail_end ∨
                              s_dec.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
                            change ¬ (st1.core.cur_vars ≤ lit.toNat / 2 ∨
                              c.max_vars ≤ st1.core.trail_end ∨
                              st1.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8)
                            simp only [hun, ne_eq, not_true_eq_false, or_false]
                            rw [hlit_v]; omega
                          fid2_call hAssign
                          refine ⟨c, s_dec, R, rfl, hdec_len, by dsimp [s_dec, nlvl]; omega,
                            ?_, ?_⟩
                          · dsimp only [s_dec, ftrl', fdec', nlvl]
                            have h1 :
                                (BitVec.ofNat 64 st1.core.cur_level + (1 : BitVec 64)).toNat =
                                  st1.core.cur_level + 1 := hnlvl_bv
                            rw [← h1, ← hte_bv]
                            assumption
                          · simp only [hng, ↓reduceIte]
                            intro flags' unas' phases' ma hfl_len hph_len hma
                            have hsp_asn0 := (p2_fullSparseInv_of_m7Decide hst1 hfl_len hph_len
                              hidx_lt hval0 hlit_eq (flags' := flags') (unas' := unas')
                              (unfl' := st1.core.unflushed) (phases' := phases')).1
                            let s_asn : FullState :=
                              { core := { s_dec.core with
                                  vals := (st1.core.vals.set lit.toNat 1#8).set
                                    (lit.toNat ^^^ 1) 0xFF#8
                                  flags := flags'
                                  lvl := st1.core.lvl.set (lit.toNat / 2)
                                    (BitVec.ofNat 32 nlvl)
                                  rsns := st1.core.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32
                                  trl := st1.core.trl.set st1.core.trail_end lit
                                  trail_pos := st1.core.trail_pos.set (lit.toNat / 2)
                                    (BitVec.ofNat 32 st1.core.trail_end)
                                  trail_end := st1.core.trail_end + 1
                                  unassigned := unas', unflushed := st1.core.unflushed }
                                scratch := { st1.scratch with phases := phases' } }
                            have hsp_asn : FullSparseInv c F0 s_asn := by
                              have hnl_ne0 : nlvl ≠ 0 := by dsimp [nlvl]; omega
                              simpa only [s_asn, s_dec, ftrl', fdec'] using hsp_asn0
                            have hma' : (FullMem c s_asn ⋆ R) ma := by
                              have hnl_ne0 : nlvl ≠ 0 := by dsimp [nlvl]; omega
                              have hff : (4294967295 : BitVec 32) = 0xFFFFFFFF#32 := rfl
                              simpa only [s_asn, s_dec, hnl_ne0, ↓reduceIte, hff] using hma
                            obtain ⟨F_cur_a, hw_a⟩ := hsp_asn.1.witness
                            fid2_steps_raw
                            fid2_call hProp
                            refine ⟨c, F0, F_cur_a, s_asn, R, rfl, hsp_asn.1.lengths, hw_a,
                              hsp_asn.2.2.2.2, hma', ?_⟩
                            dsimp only
                            intro pr vals'' flags'' lvl'' rsns'' trl'' tp'' te'' prop''
                              unass'' unfl'' wvec'' arena'' wstk'' wlen'' wu'' fuel'' ctype''
                              cref'' c0'' c1'' oom'' ticks'' wsort'' phases'' delayed'' mp
                              hlen_p hw_p htr_p hperm_p _ hfl_p hr_or _ _ _ _ hm_p
                            let s_p : FullState :=
                              { core := { s_asn.core with
                                  vals := vals'', flags := flags'', lvl := lvl'', rsns := rsns'',
                                  trl := trl'', trail_pos := tp'', trail_end := te'',
                                  propagated := prop'', unassigned := unass'', unflushed := unfl'',
                                  wvec := wvec'', arena := arena'', wstk := wstk'', wlen := wlen'',
                                  wusable := wu'', fuel := fuel'', confl_type := ctype'',
                                  confl_ref := cref'', confl_lit0 := c0'', confl_lit1 := c1'',
                                  oom := oom'' }
                                scratch := { s_asn.scratch with
                                  search_ticks := ticks'', wsort := wsort'', phases := phases'',
                                  delayed := delayed'' } }
                            have hsp_p : FullSparseInv c F0 s_p :=
                              fullSparseInv_of_fullPropagate hsp_asn hlen_p hw_p hperm_p
                                rfl rfl rfl rfl rfl
                            have hfl_p' : s_p.core.fuel.toNat ≤ s.core.fuel.toNat :=
                              Nat.le_trans hfl_p hfl1
                            have hcv_p : s_p.core.cur_vars = s3.core.cur_vars := by
                              change st.core.cur_vars = s3.core.cur_vars; exact hcv_eq
                            fid2_steps_raw
                            fid2_jnz_split hpr2
                            · fid2_steps_raw
                              refine p2_lucky_bt0_wp hBt hsp_p hm_p
                                fun s_bt mb _ hfl_b hsp_b hcl0_b hmb => ?_
                              fid2_steps_raw
                              let s' : FullState :=
                                { s_bt with core := { s_bt.core with probing := 0#64 } }
                              have hsp' : FullSparseInv c F0 s' :=
                                fullSparseInv_with_probing hsp_b 0#64
                              have hfl' : s'.core.fuel.toNat ≤ s.core.fuel.toNat := by
                                change s_bt.core.fuel.toNat ≤ s.core.fuel.toNat
                                rw [hfl_b]; exact hfl_p'
                              exact hQ 2#64 s' _ hsp'.1.lengths (Or.inr (Or.inl rfl)) hfl' rfl
                                (fun h => by cases h) (fun _ => ⟨hsp', hcl0_b⟩)
                                (fun h => by cases h) (by assumption)
                            · fid2_steps_raw
                              fid2_jnz_split hpr1
                              · fid2_steps_raw
                                refine p2_lucky_bt0_wp hBt hsp_p hm_p
                                  fun s_bt mb _ hfl_b hsp_b hcl0_b hmb => ?_
                                fid2_steps_raw
                                let s' : FullState :=
                                  { s_bt with core := { s_bt.core with probing := 0#64 } }
                                have hsp' : FullSparseInv c F0 s' :=
                                  fullSparseInv_with_probing hsp_b 0#64
                                have hfl' : s'.core.fuel.toNat ≤ s.core.fuel.toNat := by
                                  change s_bt.core.fuel.toNat ≤ s.core.fuel.toNat
                                  rw [hfl_b]; exact hfl_p'
                                exact hQ 0#64 s' _ hsp'.1.lengths (Or.inl rfl) hfl' rfl
                                  (fun h => by cases h) (fun _ => ⟨hsp', hcl0_b⟩)
                                  (fun h => by cases h) (by assumption)
                              · fid2_steps_raw
                                exact hJnext () mp ⟨s_p, hcv_p, hsp_p, hfl_p', hm_p⟩
                      · intro Jlit hJlit
                        fid2_steps_raw
                        fid2_jnz_split hsp_cond
                        · fid2_steps_raw
                          have hlt30 : idx.toNat < 2 ^ 30 := by omega
                          exact hJlit (_, ()) _
                            ⟨by assumption, Or.inl (M7SearchTactics.bv32_lit_even hlt30)⟩
                        · fid2_steps_raw
                          have hlt30 : idx.toNat < 2 ^ 30 := by omega
                          exact hJlit (_, ()) _
                            ⟨by assumption, Or.inr (M7SearchTactics.bv32_lit_odd hlt30)⟩
                  · fid2_steps_raw; exact hJnext () ml ⟨st, hcv_eq, hst, hfl, hml⟩
                · fid2_steps_raw; exact hJnext () ml ⟨st, hcv_eq, hst, hfl, hml⟩
            · fid2_steps_raw
              let st' : FullState := { st with core := { st.core with probing := 0#64 } }
              have hst' : FullSparseInv c F0 st' := fullSparseInv_with_probing hst 0#64
              exact hQ 10#64 st' _ hst'.1.lengths (Or.inr (Or.inr (Or.inl rfl))) hfl rfl
                (fun h => absurd h (by decide)) (fun h => by rcases h with h | h <;> cases h)
                (fun _ => hst'.2.2.2.1.2) (by assumption)
        · let LuckyRet : Tup Val [i64] → Mem 64 → Prop := fun (r, _) mr =>
            ∃ sr : FullState, sr.LengthsOk c ∧ (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) ∧
              sr.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (r = 20#64 → F0.Unsat) ∧
              (r = 0#64 ∨ r = 2#64 → FullSparseInv c F0 sr ∧ sr.core.cur_level = 0) ∧
              (r = 10#64 → sr.scratch.extend_len ≤ c.extend_cap) ∧ (FullMem c sr ⋆ R) mr
          fid2_steps_raw
          fid2_call hScan
          refine ⟨c, F0, s3, R, rfl, hsp3, hcl3_0, by assumption, ?_⟩
          intro r1 s1_ m1_ hlen1_ hr1_ hfl1_ huns1_ h02_1_ h10_1_ hm1_
          fid2_steps_raw
          refine wp_join_group (ts := [i64]) LuckyRet ?_ ?_
          · rintro JsA ⟨rA, ⟨⟩⟩ mA ⟨srA, hlenA, hrA, hflA, hunsA, h02A, h10A, hmA⟩
            rw [Blocks.get_here]
            fid2_steps_raw
            refine wp_join_group (ts := [i64]) LuckyRet ?_ ?_
            · rintro JsB ⟨rB, ⟨⟩⟩ mB ⟨srB, hlenB, hrB, hflB, hunsB, h02B, h10B, hmB⟩
              rw [Blocks.get_here]
              fid2_steps_raw
              refine wp_join_group (ts := [i64]) LuckyRet ?_ ?_
              · rintro JsC ⟨rC, ⟨⟩⟩ mC ⟨srC, hlenC, hrC, hflC, hunsC, h02C, h10C, hmC⟩
                rw [Blocks.get_here]
                fid2_steps_raw
                let sr' : FullState := { srC with core := { srC.core with probing := 0#64 } }
                have hlenC' : sr'.LengthsOk c :=
                  ⟨{ hlenC.core_ok with vals_len := hlenC.core_ok.vals_len }, hlenC.scratch_ok⟩
                exact hQ rC sr' _ hlenC' hrC hflC rfl hunsC
                  (fun h02 => let ⟨hspC, hclC⟩ := h02C h02
                    ⟨fullSparseInv_with_probing hspC 0#64, hclC⟩)
                  h10C (by assumption)
              · intro JsC hJsC
                fid2_steps_raw
                fid2_jnz_split hrB0
                · obtain ⟨hspB, hclB⟩ := h02B (Or.inl (by simpa using hrB0))
                  fid2_steps_raw
                  fid2_call hScan
                  refine ⟨c, F0, srB, R, rfl, hspB, hclB, hmB, ?_⟩
                  intro r4 s4 m4 hlen4 hr4 hfl4 huns4 h02_4 h10_4 hm4
                  exact hJsC (r4, ()) m4 ⟨s4, hlen4, hr4, Nat.le_trans hfl4 hflB, huns4, h02_4,
                    h10_4, hm4⟩
                · fid2_steps_raw
                  exact hJsC (rB, ()) mB ⟨srB, hlenB, hrB, hflB, hunsB, h02B, h10B, hmB⟩
            · intro JsB hJsB
              fid2_steps_raw
              fid2_jnz_split hrA0
              · obtain ⟨hspA, hclA⟩ := h02A (Or.inl (by simpa using hrA0))
                fid2_steps_raw
                fid2_call hScan
                refine ⟨c, F0, srA, R, rfl, hspA, hclA, hmA, ?_⟩
                intro r3 s3_ m3 hlen3 hr3 hfl3 huns3 h02_3 h10_3 hm3
                exact hJsB (r3, ()) m3 ⟨s3_, hlen3, hr3, Nat.le_trans hfl3 hflA, huns3, h02_3,
                  h10_3, hm3⟩
              · fid2_steps_raw
                exact hJsB (rA, ()) mA ⟨srA, hlenA, hrA, hflA, hunsA, h02A, h10A, hmA⟩
          · intro JsA hJsA
            fid2_steps_raw
            fid2_jnz_split hr10
            · obtain ⟨hsp1_, hcl1_⟩ := h02_1_ (Or.inl (by simpa using hr10))
              fid2_steps_raw
              fid2_call hScan
              refine ⟨c, F0, s1_, R, rfl, hsp1_, hcl1_, hm1_, ?_⟩
              intro r2 s2_ m2 hlen2 hr2 hfl2_ huns2 h02_2 h10_2 hm2
              exact hJsA (r2, ()) m2 ⟨s2_, hlen2, hr2, Nat.le_trans hfl2_ (Nat.le_trans hfl1_ hfl2),
                huns2, h02_2, h10_2, hm2⟩
            · fid2_steps_raw
              exact hJsA (r1, ()) m1_ ⟨s1_, hlen1_, hr1_, Nat.le_trans hfl1_ hfl2, huns1_,
                h02_1_, h10_1_, hm1_⟩
      · intro J2 hJ2
        fid2_steps_raw
        fid2_jnz_split hprop_lt
        · obtain ⟨F_cur1, hw1⟩ := hsp1.1.witness
          fid2_steps_raw
          fid2_call hProp
          refine ⟨c, F0, F_cur1, s1, R, rfl, hsp1.1.lengths, hw1, hsp1.2.2.2.2, hm1, ?_⟩
          dsimp only
          intro pr0 vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena'
            wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m_p
            hlen_p hw_p htr_p hperm_p _ hfl_p hr_or _ h1_p _ _ hm_p
          let s_p : FullState :=
            { core := { s1.core with
                vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
                unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk',
                wlen := wlen', wusable := wu', fuel := fuel', confl_type := ctype',
                confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
              scratch := { s1.scratch with
                search_ticks := ticks', wsort := wsort', phases := phases',
                delayed := delayed' } }
          have hsp_p : FullSparseInv c F0 s_p :=
            fullSparseInv_of_fullPropagate hsp1 hlen_p hw_p hperm_p rfl rfl rfl rfl rfl
          have hfl_p' : s_p.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl_p hfl1
          have hcl_p0 : s_p.core.cur_level = 0 := hcl1_0
          fid2_steps_raw
          fid2_jnz_split hpr0_1
          · obtain ⟨_, _, hconf⟩ := h1_p (by simpa using hpr0_1)
            have hunsat : F0.Unsat := FullM7Search.level0_unsat_of_conflict_okW hw_p hcl_p0 hconf
            fid2_steps_raw
            let s_inc : FullState :=
              { s_p with core := { s_p.core with inconsistent := 1#64, probing := 0#64 } }
            have hlen_inc : s_inc.LengthsOk c :=
              ⟨{ hlen_p.core_ok with vals_len := hlen_p.core_ok.vals_len }, hlen_p.scratch_ok⟩
            exact hQ 20#64 s_inc _ hlen_inc (Or.inr (Or.inr (Or.inr rfl))) hfl_p'
              rfl (fun _ => hunsat) (fun h => by rcases h with h | h <;> cases h)
              (fun h => by cases h) (by assumption)
          · fid2_steps_raw
            fid2_jnz_split hpr0_2
            · fid2_steps_raw
              let s_pr : FullState := { s_p with core := { s_p.core with probing := 0#64 } }
              have hsp_pr : FullSparseInv c F0 s_pr := fullSparseInv_with_probing hsp_p 0#64
              exact hQ 2#64 s_pr _ hsp_pr.1.lengths (Or.inr (Or.inl rfl)) hfl_p' rfl
                (fun h => by cases h) (fun _ => ⟨hsp_pr, hcl_p0⟩) (fun h => by cases h)
                (by assumption)
            · fid2_steps_raw
              exact hJ2 () m_p ⟨s_p, hsp_p, hcl_p0, hfl_p', hm_p⟩
        · fid2_steps_raw
          exact hJ2 () m1 ⟨s1, hsp1, hcl1_0, hfl1, hm1⟩
    · intro J1 hJ1
      fid2_steps_raw
      fid2_jnz_split hcl0
      · fid2_steps_raw
        refine p2_lucky_bt0_wp hBt hsp hm fun s1 m1 _ hfl_eq hsp1 hcl1_0 hm1 => ?_
        fid2_steps_raw
        exact hJ1 () m1 ⟨s1, hsp1, hcl1_0, by rw [hfl_eq]; exact Nat.le_refl _, hm1⟩
      · have hcl_lt64 : s.core.cur_level < 2 ^ 64 := by
          have := hsp.1.lengths.core_ok.trail_end_le
          have := hsp.1.lengths.core_ok.cur_vars_le
          obtain ⟨_, hw0⟩ := hsp.1.witness
          have := hw0.cur_level_le; omega
        have hcl_eq0 : s.core.cur_level = 0 := by
          have h := hcl0
          simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_lt64] at h
          exact Nat.eq_zero_of_not_pos (of_decide_eq_false h)
        fid2_steps_raw
        exact hJ1 () m ⟨s, hsp, hcl_eq0, Nat.le_refl _, hm⟩

end LuckyLateS15

/-! ## 3. `m8_enter_dense_s15_wp` (`FullM8FidV12.m8_enter_dense_body` over `fullBcpS15Spec`) -/

section EnterDenseS15

open LeanQbe.T.Examples.Kissat.FullFastSched
open FullDenseWatchHelpers

/-- `FullM8FidV12.m8_enter_dense_body` with unused `hProp` typed at `fullBcpS15Spec`. -/
theorem m8_enter_dense_s15_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hFlush : ∀ a m Q X, fullFlushTrailSpec a m Q X →
      Γ "full_flush_trail" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweepBins : ∀ a m Q X, fullSweepBinsSpec a m Q X →
      Γ "full_sweep_bins" [i64] [] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Func.wp Γ m8_enter_dense_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp0, hm, hQ⟩
  let _ := hProp
  obtain ⟨F_cur, hspw0⟩ := hsp0.exists_witness
  have har_cap : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hclv_lt : s.core.cur_level < 2 ^ 64 := by
    have := hspw0.2.1.cur_level_le; have := hspw0.1.core_ok.trail_end_le
    have := hspw0.1.core_ok.cur_vars_le; omega
  unfold Func.wp m8_enter_dense_body
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s1 m1 => M8EnterOk c F0 F_cur s s1 ∧ s1.core.dense_mode = 0#64 ∧
      (FullMem c s1 ⋆ R) m1) ?_ ?_
  · rintro _ s1 m1 ⟨hok1, hdm1, hm1⟩
    clear hm hsp0 hspw0
    have hspw1 : FullSparseInvW c F0 F_cur s1 :=
      ⟨hok1.1, hok1.2.1, hok1.2.2.1, hok1.2.2.2.1, hok1.2.2.2.2.1, hdm1⟩
    c0_hsplit
    · c0_hsteps
      exact hQ false s1 m1 hok1.2.2.2.2.2.1 hok1.2.2.2.2.2.2 (by simp)
        (fun _ => hspw1.toSparse) hm1
    · c0_hsplit
      · exact absurd hdm1 hc
      · c0_hsteps; c0_call hFlush
        refine ⟨c, F0, s1, R, rfl, hspw1.toSparse, hm1, ?_⟩
        intro fr s1p m1p hsp1p _ _ hfl1p hcl1p_fn _ _ _ hm1p
        have hcl1p : s1p.core.cur_level = 0 := hcl1p_fn hok1.2.2.2.2.2.1
        have hfl1p' : s1p.core.fuel.toNat ≤ s.core.fuel.toNat :=
          Nat.le_trans hfl1p hok1.2.2.2.2.2.2
        c0_hsplit
        · c0_hsteps
          exact hQ false s1p m1p hcl1p hfl1p' (by simp) (fun _ => hsp1p) hm1p
        · refine wp_join_state0 (α := FullState)
            (fun s1u m1u => FullSparseInv c F0 s1u ∧ s1u.core.cur_level = 0 ∧
              s1u.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1u ⋆ R) m1u) ?_ ?_
          · rintro _ s1u m1u ⟨hsp1u, hcl1u, hfl1u', hm1u⟩
            obtain ⟨F_cur1, hspw1p⟩ := hsp1u.exists_witness
            have hdm1p : s1u.core.dense_mode = 0#64 := hspw1p.2.2.2.2.2
            c0_hsteps
            c0_call hSweepBins
            refine ⟨c, F0, F_cur1, s1u, R, rfl, hspw1p.1, hspw1p.2.1, hm1u,
              fun wvec2 wstk2 wlen2 nb2 wsort2 m2 hlen2 _ hd2 hw2 hm2 => ?_⟩
            let s2 : FullState :=
              { s1u with
                core := { s1u.core with
                  wvec := wvec2, wstk := wstk2, wlen := wlen2, wusable := 0#64, num_binary := nb2 }
                scratch := { s1u.scratch with wsort := wsort2 } }
            have hok2 : M8EnterOk c F0 F_cur1 s s2 :=
              ⟨hlen2, hw2, hspw1p.2.2.1, hspw1p.2.2.2.1, hspw1p.2.2.2.2.1, hcl1u, hfl1u'⟩
            c0_hsteps_nogrp
            refine wp_loop_inv
              (fun (p, ()) mP =>
                p.toNat ≤ s2.core.arena_len ∧
                (p.toNat = s2.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s2) ∧
                ∃ sP : FullState,
                  M8EnterOk c F0 F_cur1 s sP ∧ DenseWatchesInv F_cur1 sP.core ∧
                  sP.core.arena = s2.core.arena ∧ sP.core.arena_len = s2.core.arena_len ∧
                  sP.core.dense_mode = 0#64 ∧ (FullMem c sP ⋆ R) mP)
              (fun (p, ()) _ => s2.core.arena_len - p.toNat)
              (fun JP hLoopP => by
                c0_hsteps
                refine hLoopP (0#64, ()) m2 ⟨Nat.zero_le _, ?_, s2, hok2, hd2, rfl, rfl, hdm1p, hm2⟩
                by_cases hz : s2.core.arena_len = 0
                · exact Or.inl hz.symm
                · exact Or.inr (FullDenseWatchHelpers.fullArenaClauseRefs_zero_mem hw2.arena
                    (Nat.pos_of_ne_zero hz)))
              (fun JP ⟨p, ⟨⟩⟩ mP ⟨hp_le, hp_mem, sP, hokP, hdP, harP, halenP, hdmP, hmP⟩
                  hLoopP => ?_)
            have halP := hokP.1.core_ok.arena_len_le
            have haarP := hokP.1.core_ok.arena_len_arr
            have hrefsP : fullArenaClauseRefs sP = fullArenaClauseRefs s2 := by
              unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [harP, halenP]
            c0_hsplit
            · have hp_lt : p.toNat < sP.core.arena_len := by c0_bound
              have hp_in : p.toNat ∈ fullArenaClauseRefs sP := by
                rw [hrefsP]; exact hp_mem.resolve_left (by omega)
              have hp_wf := hokP.2.1.arena.refs_wf p.toNat hp_in
              have hp_lt32 : p.toNat < 2 ^ 32 := by omega
              have hp_trunc : (p.setWidth 32).toNat = p.toNat := by bv_omega
              have hnb := fullArenaNextOff_bounds (ar := sP.core.arena) (alen := sP.core.arena_len)
                (cref := p.toNat) hp_wf.1
              have hnxt_mem := fullArenaClauseRefs_next_mem hokP.2.1.arena hp_in
              c0_hsteps_nogrp
              refine wp_join_state0 (α := FullState)
                (fun sN mN => M8EnterOk c F0 F_cur1 s sN ∧ DenseWatchesInv F_cur1 sN.core ∧
                  sN.core.arena = s2.core.arena ∧ sN.core.arena_len = s2.core.arena_len ∧
                  sN.core.dense_mode = 0#64 ∧ (FullMem c sN ⋆ R) mN)
                (fun _ sN mN ⟨hokN, hdN, harN, halenN, hdmN, hmN⟩ => by
                  c0_hsteps; c0_call hArenaNext
                  refine ⟨c, sN, R, rfl, hokN.1, hmN, ?_⟩
                  have hn_eq : ((BitVec.ofNat 32 (fullArenaNextOff sN.core.arena sN.core.arena_len
                      (p.setWidth 32).toNat)).setWidth 64).toNat =
                      fullArenaNextOff sP.core.arena sP.core.arena_len p.toNat := by
                    rw [harN, halenN, ← harP, ← halenP, hp_trunc, BitVec.toNat_setWidth,
                      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
                      Nat.mod_eq_of_lt (by omega)]
                  c0_hsteps
                  exact hLoopP (_, ()) mN (by dsimp only; rw [hn_eq]; omega)
                    ⟨by rw [hn_eq]; omega,
                      by rw [hn_eq]
                         rcases hnxt_mem with hend | hmem
                         · exact Or.inl (hend.trans halenP)
                         · exact Or.inr (hrefsP ▸ hmem),
                      sN, hokN, hdN, harN, halenN, hdmN, hmN⟩)
                (fun JN hJN => ?_)
              c0_hsteps_nogrp
              · have hsz_eq : (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat =
                    fullArenaClauseSizeCore sP.core p.toNat := by
                  have hp2 : (p + 2#64).toNat = p.toNat + 2 := by c0_bound
                  unfold fullArenaClauseSizeCore
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; simp only [hp2]
                have hsz_ge3 : 3 ≤ (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat := by
                  rw [hsz_eq]; exact hp_wf.2.1
                have hsz_lt31 :
                    (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat < 2 ^ 31 := by
                  rw [hsz_eq]; have := hp_wf.2.2.1; have := hp_wf.2.2.2.1; omega
                have hmask := bv32_mask_7fffffff_props hsz_ge3 hsz_lt31
                have hp_lt31 : (p.setWidth 32).toNat < 0x80000000 := by rw [hp_trunc]; omega
                have hp_neff : p.setWidth 32 ≠ 0xFFFFFFFF#32 := fun heq => by
                  rw [heq] at hp_lt31; revert hp_lt31; decide
                refine wp_loop_inv
                  (fun (k, ()) mK =>
                    k.toNat ≤ (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat ∧
                    ∃ sK : FullState,
                      M8EnterOk c F0 F_cur1 s sK ∧ DenseWatchesInv F_cur1 sK.core ∧
                      sK.core.arena = s2.core.arena ∧ sK.core.arena_len = s2.core.arena_len ∧
                      sK.core.dense_mode = 0#64 ∧ (FullMem c sK ⋆ R) mK)
                  (fun (k, ()) _ => (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat - k.toNat)
                  (fun JK hLoopK => by
                    c0_hsteps
                    exact hLoopK (0#32, ()) mP
                      ⟨Nat.zero_le _, sP, hokP, hdP, harP, halenP, hdmP, hmP⟩)
                  (fun JK ⟨k, ⟨⟩⟩ mK ⟨hk_le, sK, hokK, hdK, harK, halenK, hdmK, hmK⟩ hLoopK => ?_)
                have haarK := hokK.1.core_ok.arena_len_arr
                c0_hsplit
                · have hk_lt : k.toNat < (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat := by
                    c0_bound
                  have hidx_eq : (p + 3#64 + k.setWidth 64).toNat = p.toNat + 3 + k.toNat := by
                    have := hp_wf.2.2.1; have := hp_wf.2.2.2.1; bv_omega
                  have hidx_lt : (p + 3#64 + k.setWidth 64).toNat < sK.core.arena.length := by
                    rw [hidx_eq]; rw [hsz_eq] at hk_lt
                    have := hp_wf.2.2.1; have := hp_wf.2.2.2.1
                    have := hokK.1.core_ok.arena_len_le; omega
                  c0_hsteps; c0_call hWatchPush
                  refine ⟨c, sK, R, rfl, hokK.1, hdK.layout, by simp,
                    fun _ => ⟨hmask.2.1, hp_neff⟩, hmK,
                    fun ok wvecK' wstkK' wlenK' wuK' wsortK' mK' hlenK' hlayK' hothK' hokT
                      hokF hmK' => ?_⟩
                  let sK' : FullState :=
                    { sK with
                      core := { sK.core with wvec := wvecK', wstk := wstkK', wlen := wlenK',
                                             wusable := wuK' }
                      scratch := { sK.scratch with wsort := wsortK' } }
                  have hp_inK : (p.setWidth 32).toNat ∈ fullArenaClauseRefsCore sK.core := by
                    rw [hp_trunc]; unfold fullArenaClauseRefsCore
                    rw [harK, halenK, ← harP, ← halenP]; exact hp_in
                  have hdK' : DenseWatchesInv F_cur1 sK'.core :=
                    fullWatchPush_preserves_denseWatchesInv hdK hlayK' rfl (fun _ r => r)
                      hmask.1 hmask.2.2 hp_lt31 hp_inK hothK'
                      (fun ht => by
                        obtain ⟨hl, _, hsz', hpre', hw0', hw1'⟩ := hokT ht
                        exact ⟨hl, hsz', hpre', hw0', hw1' rfl⟩) (fun hf => (hokF hf).1)
                  have hwK' : FullWitnessInv c F0 F_cur1 sK'.core :=
                    { hokK.2.1 with
                      arena := { hokK.2.1.arena with len_ok := hokK.2.1.arena.len_ok }
                      watches := by
                        rw [ModeWatchesInv, ite_eq_left hdmK]
                        exact denseWatchesInv_toWatchesInv hdK' }
                  have hokK' : M8EnterOk c F0 F_cur1 s sK' :=
                    ⟨hlenK', hwK', hokK.2.2.1, hokK.2.2.2.1, hokK.2.2.2.2.1, hokK.2.2.2.2.2.1,
                      hokK.2.2.2.2.2.2⟩
                  c0_hsplit
                  · have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                    c0_hsteps
                    exact hLoopK (k + 1#32, ()) mK' (by dsimp only; omega)
                      ⟨by omega, sK', hokK', hdK', harK, halenK, hdmK, hmK'⟩
                  · c0_hsteps
                    let sOom : FullState := { sK' with core := { sK'.core with oom := 0#64 } }
                    have hlenOom : sOom.LengthsOk c :=
                      ⟨{ hlenK'.core_ok with vals_len := hlenK'.core_ok.vals_len },
                        hlenK'.scratch_ok⟩
                    have hwOom := FullDenseWatchHelpers.fullWitnessInv_with_oom hwK' 0#64
                    c0_call hSweep
                    refine ⟨c, F0, F_cur1, sOom, R, rfl, hlenOom, hwOom, hokK'.2.2.2.1, hdmK,
                      fun hpos => by
                        change 0 < sK.core.cur_level at hpos; have := hokK.2.2.2.2.2.1; omega,
                      hm, ?_⟩
                    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ scS mS sS hlenS _ hextS _ hllS
                      hwS hndS _ _ _ _ _ hmS
                    have hspS : FullSparseInv c F0 sS :=
                      ⟨⟨hlenS, F_cur1, hwS⟩, hokK'.2.2.1, hndS, ⟨hllS, hextS ▸ hokK'.2.2.2.2.1.2⟩,
                        hdmK⟩
                    c0_hsteps
                    exact hQ false sS mS hokK'.2.2.2.2.2.1 hokK'.2.2.2.2.2.2
                      (by simp) (fun _ => hspS) hmS
                · c0_hsteps; exact hJN sK mK ⟨hokK, hdK, harK, halenK, hdmK, hmK⟩
              all_goals exact hJN sP mP ⟨hokP, hdP, harP, halenP, hdmP, hmP⟩
            · c0_hsteps
              let sFin : FullState := { sP with core := { sP.core with dense_mode := 1#64 } }
              have hlenFin : sFin.LengthsOk c :=
                ⟨{ hokP.1.core_ok with vals_len := hokP.1.core_ok.vals_len }, hokP.1.scratch_ok⟩
              have hwFin : FullWitnessInv c F0 F_cur1 sFin.core :=
                fullWitnessInv_with_dense_mode_nz hokP.2.1 hdP (by decide)
              have hdenFin : FullDenseInv c F0 sFin :=
                ⟨⟨hlenFin, F_cur1, hwFin⟩, hokP.2.2.1, hokP.2.2.2.1, hokP.2.2.2.2.1,
                  hokP.2.2.2.2.2.1, show (1#64 : BitVec 64) ≠ 0#64 by decide⟩
              exact hQ true sFin _ hokP.2.2.2.2.2.1 hokP.2.2.2.2.2.2
                (fun _ => hdenFin) (by simp) hm
          · intro J1u hJ1u
            c0_hsteps_nogrp
            exact hJ1u s1p m1p ⟨hsp1p, hcl1p, hfl1p', hm1p⟩
  · intro J1 hJ1; c0_hsplit
    · c0_hsteps; c0_call hBacktrack
      refine ⟨c, s, R, rfl, hspw0.1, hclv_lt, fun _ => by
        have := hspw0.2.1.cur_level_le; have := hspw0.1.core_ok.trail_end_le
        have := hspw0.1.core_ok.cur_vars_le; omega,
        hspw0.2.1.trail_lits_lt, hm, ?_⟩
      intro _ _ _ _ _ _ _ cl1 _ sc1 m1 s1 hlen1 _ _ hcl1 hprsc1 _ _ _ hw_le _ hm1
      have hw1 := hw_le F0 F_cur hspw0.2.1 (Nat.zero_le _)
      have hl01 : s1.core.cur_level = 0 := by dsimp only [s1]; rw [hcl1]; simp
      have hsp1 := m6cf_fullSparseInvW_after_bt0 hspw0 hlen1 hw1 hprsc1.1 rfl rfl rfl rfl rfl
      c0_hsteps
      exact hJ1 s1 m1 ⟨⟨hsp1.1, hsp1.2.1, hsp1.2.2.1, hsp1.2.2.2.1, hsp1.2.2.2.2.1, hl01,
        Nat.le_refl _⟩, hsp1.2.2.2.2.2, hm1⟩
    · have hl00 : s.core.cur_level = 0 := by
        have hnat := congrArg BitVec.toNat hc
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclv_lt] at hnat; exact hnat
      c0_hsteps
      exact hJ1 s m ⟨⟨hspw0.1, hspw0.2.1, hspw0.2.2.1, hspw0.2.2.2.1, hspw0.2.2.2.2.1, hl00,
        Nat.le_refl _⟩, hspw0.2.2.2.2.2, hm⟩

end EnterDenseS15

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep2

end
