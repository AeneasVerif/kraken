/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep7BvaSpec
public import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof2a0
public import LeanQbe.T.Examples.Kissat.FullM4BvaLemmas1
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
import LeanQbe.T.Examples.Kissat.FullM4BvaLemmas2
import LeanQbe.T.Examples.Kissat.FullBvaFwdLemmas1
import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas5
import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
import LeanQbe.T.Examples.Kissat.FullBridgeLemmas3
import LeanQbe.T.Examples.Kissat.FullIngestLemmas2
public import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Agrees

/-!
# Kissat Fidelity Step-7 BVA Commit Helpers (`FullFidelityStep7Proof2a0`)

Helper module for `full_bva_commit_step7_wp` (`FullFidelityStep7Proof2a`):
1. `S7StOk`: `FullFidelityBva.FidBvaStOk` plus `res_sz` preservation (Step-7 `full_bva_try_lit`
   stores `h->res_sz = best_k` before calling `full_bva_commit`, and `full_factor` reads it back).
2. `s7_bva_large_watch_wp` / `s7_bva_large_top_wp`: the large-clause copy + watch-push + unwatch
   rollback subtree (`FullFidelityBva.fidBvaLargeTopExpr`, character-identical C in Step 7),
   re-proved over `S7StOk`.
3. `Step7RowRefOk` transport lemmas (`step7RowRefOk_of_entry`, `step7RowRefOk_mono`).
4. Pure row-compaction buffer invariants (`S7Geom`, `S7CompInv`, `S7RowInv`, `s7CompInv_step`,
   `s7CompInv_zero`) for the Step-7 `row[q][fi] := row[q][par[q+1][fi]]` loop.
All public names live in the shard-local namespace `FullFidelityStep7Proof2a`.
-/

set_option autoImplicit false

local elab "c0_hsteps_np" : tactic => LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

local elab "c0_hsteps_nogrp_np" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof2a

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open FullBvaHeap FullBvaHeap.FullBvaHeapHelpers FullBvaHeap.FullBvaHeapTactics
open FullBvaHeap.FullBvaHeapScanHelpers FullM4Bva
open LeanQbe.T.Examples.Kissat.FullFidelityBva LeanQbe.T.Examples.Kissat.FullFidelityStep7
open scoped FullArenaTactics FullBvaHeapTactics

/-! ## 1. `S7StOk` & Copied Private Helpers -/

/-- `FidBvaStOk` plus `res_sz` preservation across the Step-7 commit phases. -/
abbrev S7StOk (c : FullCfg) (F0 : CNF Nat) (F_next : List (List Nat))
    (s st : FullState) : Prop :=
  FullDenseInvW c F0 F_next st ∧ st.core.cur_vars = s.core.cur_vars + 1 ∧
  st.core.fuel = s.core.fuel ∧ st.scratch.scratch_buf = s.scratch.scratch_buf ∧
  st.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  st.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ FidBvaArenaMono s.core st.core ∧
  st.scratch.res_sz = s.scratch.res_sz

private theorem nodup_lt_length_le : ∀ {n : Nat} {xs : List Nat},
    xs.Nodup → (∀ x ∈ xs, x < n) → xs.length ≤ n
  | 0, [], _, _ => Nat.zero_le _
  | 0, x :: _, _, hlt => absurd (hlt x (by simp)) (by omega)
  | n + 1, xs, hnd, hlt => by
    by_cases hn : n ∈ xs
    · have hperm := List.perm_cons_erase hn; have hnd' := List.nodup_cons.mp (hnd.perm hperm)
      have hlt' : ∀ y ∈ xs.erase n, y < n := fun y hy => by
        have hmem := List.mem_of_mem_erase hy
        have hne : y ≠ n := fun he => by subst he; exact hnd'.1 hy
        have := hlt y hmem; omega
      have ih := nodup_lt_length_le hnd'.2 hlt'
      have hlen := hperm.length_eq; simp only [List.length_cons] at hlen; omega
    · have hlt' : ∀ y ∈ xs, y < n := fun y hy => by
        have hne : y ≠ n := fun he => by subst he; exact hn hy
        have := hlt y hy; omega
      exact Nat.le_trans (nodup_lt_length_le hnd hlt') (Nat.le_succ _)

private theorem fullDenseInvW_of_append_clause {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s) {sz : Nat}
    (hsz3 : 3 ≤ sz) {ar' wvec' wstk' fl' wsort' : List (BitVec 32)} {wlen' : Nat}
    {wu' ni' : BitVec 64}
    (hlen' : let k' := { s.core with
      arena := ar', arena_len := s.core.arena_len + 3 + sz, wvec := wvec', wstk := wstk',
      wlen := wlen', wusable := wu', flags := fl', num_irred := ni' }
      ({ s with core := k', scratch := { s.scratch with wsort := wsort' } } :
        FullState).LengthsOk c)
    (hhold : ∀ i < s.core.arena_len, ar'[i]? = s.core.arena[i]?)
    (hns : (ar'[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hsz_new : (ar'[s.core.arena_len + 2]?.getD 0#32).toNat = sz)
    (hlits_lt : ∀ l ∈ fullArenaClauseLitsCore { s.core with arena := ar' } s.core.arena_len,
      l < 2 * s.core.cur_vars)
    (hlits_nd : ((fullArenaClauseLitsCore { s.core with arena := ar' }
      s.core.arena_len).map (· / 2)).Nodup)
    (hlits_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore { s.core with arena := ar' } s.core.arena_len)))
    (hwat' : ModeWatchesInv F_cur { s.core with
      arena := ar', arena_len := s.core.arena_len + 3 + sz, wvec := wvec', wstk := wstk',
      wlen := wlen', wusable := wu', flags := fl', num_irred := ni' }) :
    let s' : FullState := { s with
      core := { s.core with
        arena := ar', arena_len := s.core.arena_len + 3 + sz, wvec := wvec', wstk := wstk',
        wlen := wlen', wusable := wu', flags := fl', num_irred := ni' },
      scratch := { s.scratch with wsort := wsort' } }
    FullDenseInvW c F0 F_cur s' ∧ FidBvaArenaMono s.core s'.core := by
  intro s'; have hw := hinv.2.1; have hcl := hinv.1.core_ok
  have hnxt_hold := hw.arena.arenaNextOff_extend (alen' := s.core.arena_len + 3 + sz)
    (by omega) hhold
  have hrefs :
      fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
    fullArenaClauseRefsCore_append hw.arena hsz3 rfl hhold hns hsz_new
  have hold_garb : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1; unfold fullArenaClauseGarbCore fullArenaHdrCore s'
    simp [hhold r (by omega)]
  have hold_sz : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1; unfold fullArenaClauseSizeCore s'
    simp [hhold (r + 2) (by omega)]
  have hold_lits : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun r hr => by
    have hwf := hw.arena.refs_wf r hr
    exact fullArenaClauseLitsCore_congr (hold_sz r hr) fun j hj => hhold (r + 3 + j) (by omega)
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨Or.inr (by dsimp [s']; omega), ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hwf := hw.arena.refs_wf r hr; rw [hnxt_hold r hr, hold_sz r hr]
        refine ⟨by dsimp [s']; omega, hwf.2.1, hwf.2.2.1, by dsimp [s']; omega, ?_⟩
        rcases hwf.2.2.2.2 with he | h3 <;> right <;> dsimp [s'] <;> omega
      · have hnxt_new : fullArenaNextOff s'.core.arena s'.core.arena_len s.core.arena_len =
            s.core.arena_len + 3 + sz := by unfold fullArenaNextOff s'; simp [hsz_new, hns]
        rw [hnxt_new, show fullArenaClauseSizeCore s'.core s.core.arena_len = sz from hsz_new]
        refine ⟨by dsimp [s']; omega, hsz3, by omega, by dsimp [s']; omega, Or.inl (by dsimp [s'])⟩
    · intro r hr hsh; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hr3 := (hw.arena.refs_wf r hr).1
        have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore at hsh ⊢; dsimp only [s'] at hsh; rwa [hhold r (by omega)] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
        exact ⟨t, by rw [hold_sz r hr]; exact ht1, by dsimp only [s']; omega,
          by dsimp only [s']; rw [hhold t ht2]; exact hsent⟩
      · unfold fullArenaHdrCore at hsh; dsimp only [s'] at hsh; exact absurd hns hsh
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hw.arena.lits_lt r hr hng
      · exact hlits_lt
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hw.arena.entails r hr hng
      · exact hlits_ent
  have hno_rsn : ∀ idx < s.core.trail_end,
      s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
    fun idx hidx => hw.level0_rsn_none idx hidx (by
      have := hw.lvl_le idx hidx; have := hinv.2.2.2.2.2.1; omega)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := harena', watches := hwat',
      reason_inv := fun idx hidx hne => absurd (hno_rsn idx hidx) hne,
      reason_lit_mem := fun idx hidx hne _ => absurd (hno_rsn idx hidx) hne }
  have hnodup' : FullArenaVarsNodup s' := fun r hr hng => by
    change r ∈ fullArenaClauseRefsCore s'.core at hr
    rw [hrefs, List.mem_append, List.mem_singleton] at hr; rcases hr with hr | rfl
    · change fullArenaClauseGarbCore s'.core r = false at hng; rw [hold_garb r hr] at hng
      change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup
      rw [hold_lits r hr]; exact hinv.2.2.2.1 r hr hng
    · exact hlits_nd
  have hext' : FullExtScratchOk c s' := ⟨(fun i hi => by
    rcases hinv.2.2.2.2.1.1 i hi with h1 | h2
    · exact Or.inl h1
    · refine Or.inr ?_
      change _ ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact List.mem_append_left _ h2),
    hinv.2.2.2.2.1.2⟩
  exact ⟨⟨hlen', hw', hinv.2.2.1, hnodup', hext', hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩,
    fun r hr => ⟨by rw [hrefs]; exact List.mem_append_left _ hr, hold_sz r hr, hold_lits r hr⟩⟩

private theorem fullDenseInvW_with_num_irred {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    (ni' : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with num_irred := ni' } } :=
  ⟨⟨{ hinv.1.core_ok with vals_len := hinv.1.core_ok.vals_len }, hinv.1.scratch_ok⟩,
   { hinv.2.1 with
     arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }
     watches := hinv.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

private theorem fullDenseInvW_set_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {tmp' : List (BitVec 32)} (htmp : tmp'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with tmp := tmp' } } :=
  fullDenseInv_with_core_aux (tc' := s.core.tmp_cnt) (tl' := s.core.tmp_len) (sc' := s.scratch)
    hinv hinv.1.core_ok.repr_len hinv.1.core_ok.min_clr_len_arr htmp hinv.1.core_ok.flags_len
    hinv.1.core_ok.tmp_len_le hinv.1.scratch_ok rfl rfl

private theorem fullArenaLitsCore_eq_map {k : FullCoreState} {r sz : Nat}
    (hsz : fullArenaClauseSizeCore k r = sz) (hb : r + 3 + sz ≤ k.arena.length) :
    fullArenaClauseLitsCore k r =
      (List.range sz).map (fun j => (k.arena[r + 3 + j]?.getD 0#32).toNat) := by
  apply List.ext_getElem?; intro j; by_cases hj : j < sz
  · rw [FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (by omega) (by omega),
      List.getElem?_map, List.getElem?_range hj, Option.map_some,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  · rw [List.getElem?_eq_none (by
        rw [FullBvaFwdHelpers.fullArenaClauseLitsCore_length (by omega), hsz]; omega),
      List.getElem?_eq_none (by simp; omega)]

private theorem bv32_lit_mask_eq {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
    (x &&& 0x7FFFFFFF#32) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h]

private theorem wp_jump_eq {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost}
    {L : Cont ts} {args : Tup (Arg Val) ts} {m : Mem 64} :
    wp Γ Q X (.jump L args) m = L (vals args) m := rfl

private theorem is_wp_goal {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {e : Expr Val Cont rs} {m : Mem 64} (h : wp Γ Q X e m) : wp Γ Q X e m := h

local macro "fid_hsteps_to_jump" : tactic =>
  `(tactic| repeat (
    apply is_wp_goal
    first | (rw [wp_jump_eq]; dsimp only [vals, Arg.val]) | c0_hstep))

/-! ## 2. Large-Clause Copy / Watch-Push / Rollback over `S7StOk` -/

theorem s7_bva_large_watch_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hWPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hUnwatch : ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_next : List (List Nat)} {s stm : FullState}
    {R : Mem 64 → Prop} {tk : Val i32} {J6 : Cont [.bool]}
    {tmpj arj : List (BitVec 32)} {mjc : Mem 64} (hstm : S7StOk c F0 F_next s stm)
    (htmpj_l : tmpj.length = c.max_vars)
    (htk_ge3 : 3 ≤ tk.toNat) (htk_le_mv : tk.toNat ≤ c.max_vars)
    (hncr_cap : stm.core.arena_len + 3 + tk.toNat ≤ c.arena_cap)
    (hhold_j : ∀ i < stm.core.arena_len, arj[i]? = stm.core.arena[i]?)
    (hns_cp : (arj[stm.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hsz_cp : (arj[stm.core.arena_len + 2]?.getD 0#32).toNat = tk.toNat)
    (hnew_lt : ∀ l ∈ fullArenaClauseLitsCore { stm.core with arena := arj } stm.core.arena_len,
      l < 2 * stm.core.cur_vars)
    (hnew_nd : ((fullArenaClauseLitsCore { stm.core with arena := arj }
      stm.core.arena_len).map (· / 2)).Nodup)
    (hnew_ent : (cnfOfClauses F_next).EntailsClause
      (cnfClause (fullArenaClauseLitsCore { stm.core with arena := arj } stm.core.arena_len)))
    (htmp_lt : ∀ t (ht : t < tk.toNat),
      (tmpj[t]'(by rw [htmpj_l]; omega)).toNat < 2 * (s.core.cur_vars + 1))
    (hlen_cp : ({ stm with core := { stm.core with
        tmp := tmpj, arena := arj, arena_len := stm.core.arena_len + 3 + tk.toNat } } :
      FullState).LengthsOk c)
    (hrefs_cp : fullArenaClauseRefsCore
        { stm.core with
          tmp := tmpj, arena := arj, arena_len := stm.core.arena_len + 3 + tk.toNat } =
      fullArenaClauseRefsCore stm.core ++ [stm.core.arena_len])
    (hwat_cp : ModeWatchesInv F_next
      { stm.core with tmp := tmpj, arena := arj, arena_len := stm.core.arena_len + 3 + tk.toNat })
    (hmjc : (FullMem c { stm with core := { stm.core with
      tmp := tmpj, arena := arj, arena_len := stm.core.arena_len + 3 + tk.toNat } } ⋆ R) mjc)
    (hDone : ∀ (ok' : Bool) st1 m1, (FullMem c st1 ⋆ R) m1 →
      S7StOk c F0 F_next s st1 → J6 (ok', ()) m1) :
    wp Γ Q X (fidBvaLargeWatchExpr c.hdr c.pArena c.pFlags c.pTmp tk
      (BitVec.ofNat 64 stm.core.arena_len) J6) mjc := by
  obtain ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono, hresm⟩ := hstm
  have hmx := c.hmaxv; have har_b := c.harena; unfold dimacsBound at hmx har_b
  have hclm := hinvm.1.core_ok; let old_cv := s.core.cur_vars; let ncr0 := stm.core.arena_len
  let st_tmp : FullState := { stm with core := { stm.core with tmp := tmpj } }
  have hinv_tmp : FullDenseInvW c F0 F_next st_tmp := fullDenseInvW_set_tmp hinvm htmpj_l
  let st_cp : FullState :=
    { st_tmp with core := { st_tmp.core with arena := arj, arena_len := ncr0 + 3 + tk.toNat } }
  have hncr_nat : (BitVec.ofNat 64 ncr0).toNat = ncr0 := by have := hclm.arena_len_le; c0_bound
  have hcv_le := hclm.cur_vars_le
  have htk_lt31 : tk.toNat < 2 ^ 31 := by omega
  dsimp only [fidBvaLargeWatchExpr, fidBZext, fidBOp64, fidBOp32, fidBCmp32, fidBPtr32, fidBLd32]
  refine wp_join_group (ts := [.bool, i32])
    (fun (ok', _, ()) mw => ∃ stw : FullState,
      (FullMem c stw ⋆ R) mw ∧ S7StOk c F0 F_next s stw)
    (fun _ (ok', _, ()) mw ⟨stw, hmw, hstw⟩ => by
      refine wp_join_state0 (α := FullState)
        (fun stf mf => (FullMem c stf ⋆ R) mf ∧ S7StOk c F0 F_next s stf)
        (fun _ stf mf ⟨hmf, hstf⟩ => by fid_hsteps_to_jump; exact hDone ok' stf mf hmf hstf)
        (fun Jni hJni => by
          obtain ⟨hinvw, hcvw, hfuelw, hsbw, htmw, htrw, hmonow, hresw⟩ := hstw; c0_hsplit
          · fid_hsteps_to_jump
            exact hJni _ m ⟨hm, fullDenseInvW_with_num_irred hinvw _, hcvw, hfuelw,
              hsbw, htmw, htrw, hmonow, hresw⟩
          · fid_hsteps_to_jump
            exact hJni _ mw ⟨hmw, hinvw, hcvw, hfuelw, hsbw, htmw, htrw, hmonow, hresw⟩))
    (fun Jw_exit hJw_exit => ?_)
  refine wp_loop_inv
    (fun (jw, ()) mjw => ∃ wvecw wstkw flw wsortw wlenw wuw, jw.toNat ≤ tk.toNat ∧
      let sw : FullState :=
        { st_cp with core := { st_cp.core with wvec := wvecw, wstk := wstkw, wlen := wlenw,
                                               wusable := wuw, flags := flw }
                     scratch := { st_cp.scratch with wsort := wsortw } }
      sw.LengthsOk c ∧ ModeWatchesInv F_next sw.core ∧ (FullMem c sw ⋆ R) mjw)
    (fun (jw, _) _ => tk.toNat - jw.toNat) (fun Jw hJw => by
      fid_hsteps_to_jump; exact hJw (0#32, ()) mjc
        ⟨st_cp.core.wvec, st_cp.core.wstk, st_cp.core.flags,
         st_cp.scratch.wsort, st_cp.core.wlen, st_cp.core.wusable, Nat.zero_le _,
         hlen_cp, hwat_cp, hmjc⟩)
    (fun Jw (jw, ()) mjw ⟨wvecw, wstkw, flw, wsortw, wlenw, wuw, hjw_le, hlenw,
        hwatw, hmjw⟩ ihw => ?_)
  let sw : FullState :=
    { st_cp with core := { st_cp.core with wvec := wvecw, wstk := wstkw, wlen := wlenw,
                                           wusable := wuw, flags := flw }
                 scratch := { st_cp.scratch with wsort := wsortw } }
  c0_hsplit
  · have hjw_lt : jw.toNat < tk.toNat := by c0_bound
    have hjw1 : (jw + 1#32).toNat = jw.toNat + 1 := by c0_bound
    have hjw_tmp : jw.toNat < tmpj.length := by omega
    have hjw_tmp_sw : (BitVec.setWidth 64 jw).toNat < sw.core.tmp.length := by
      rw [bv64_setWidth_32]; exact hjw_tmp
    have htk_mask : (tk &&& (2147483647 : BitVec 32)) = tk := bv32_lit_mask_eq htk_lt31
    have htk_ne : (tk &&& (2147483647 : BitVec 32)) ≠ 0xFFFFFFFF#32 := by
      rw [htk_mask]; intro h; have := congrArg BitVec.toNat h
      have : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl; omega
    have hncr32_nat : (BitVec.setWidth 32 (BitVec.ofNat 64 ncr0)).toNat = ncr0 := by
      have := hclm.arena_len_le; c0_bound
    have hncr32_ne : BitVec.setWidth 32 (BitVec.ofNat 64 ncr0) ≠ 0xFFFFFFFF#32 := by
      intro h; have := congrArg BitVec.toNat h; rw [hncr32_nat] at this
      have := hclm.arena_len_le; have : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl; omega
    c0_hsteps; c0_call hWPush
    refine ⟨c, sw, R, rfl, hlenw, hwatw.layout, (fun h => absurd h (by decide)),
      (fun _ => ⟨htk_ne, hncr32_ne⟩), hmjw,
      fun okw wvec' wstk' wlen' wu' wsort' mw' hlenw' hlayw' hothw hokt hokf hmw' => ?_⟩
    have hwatw' : ModeWatchesInv F_next
        { sw.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } := by
      refine fullWatchPush_preserves_modeWatchesInv (cnt := 2#32) hwatw hlayw'
        rfl rfl (fun _ hr => hr) (fun h => absurd h (by decide)) ?_ hothw hokt
        (fun hf => (hokf hf).1)
      intro _; have htk_nb : (tk &&& 0x80000000#32) = 0#32 :=
        bv32_bin_flag_zero_of_lt htk_lt31
      refine ⟨by rw [htk_mask]; exact htk_nb, fun _ => by rw [htk_mask]; omega,
        by rw [hncr32_nat]; have := hclm.arena_len_le; omega, ?_⟩
      change (BitVec.setWidth 32 (BitVec.ofNat 64 ncr0)).toNat ∈ fullArenaClauseRefsCore st_cp.core
      rw [hncr32_nat, hrefs_cp]; exact List.mem_append_right _ (by dsimp only [ncr0]; simp)
    have htv_shr : (BitVec.setWidth 64 ((tmpj[(BitVec.setWidth 64 jw).toNat]'(by
        rw [bv64_setWidth_32]; exact hjw_tmp)) >>> (1 : BitVec 32))).toNat < flw.length := by
      rw [bv64_setWidth_32, bv32_lshr1_bv, hlenw'.core_ok.flags_len]
      simp only [bv64_setWidth_32]; have := htmp_lt jw.toNat hjw_lt; omega
    have htv_shr_n : (BitVec.setWidth 64 ((tmpj[(BitVec.setWidth 64 jw).toNat]'(by
        rw [bv64_setWidth_32]; exact hjw_tmp)) >>> (1 : Nat))).toNat < flw.length := by
      rw [bv64_setWidth_32, bv32_lshr1_nat, hlenw'.core_ok.flags_len]
      simp only [bv64_setWidth_32]; have := htmp_lt jw.toNat hjw_lt; omega
    c0_hsteps_nogrp
    · c0_hsteps_nogrp
      refine wp_join_group (ts := [i32]) (fun (_ : Tup Val [i32]) mf => mf = mw')
        (fun _ _ mf hmf => by
          subst mf; fid_hsteps_to_jump
          refine ihw (jw + 1#32, ()) m (by dsimp only; rw [hjw1]; omega)
            ⟨wvec', wstk', _, wsort', wlen', wu', by rw [hjw1]; omega, ?_, ?_, hm⟩
          · exact ⟨{ hlenw'.core_ok with flags_len := by simp [hlenw'.core_ok.flags_len] },
              hlenw'.scratch_ok⟩
          · exact hwatw'.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr))
        (fun Jt hJt => by
          c0_hsplit
          · fid_hsteps_to_jump; exact hJt (64#32, ()) mw' rfl
          · fid_hsteps_to_jump; exact hJt (32#32, ()) mw' rfl)
    · let sw_fail : FullState :=
        { sw with core := { sw.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                         wusable := wu' }
                  scratch := { sw.scratch with wsort := wsort' } }
      refine wp_loop_inv
        (fun (uk, ()) muk => ∃ wvecu wstku wuu, uk.toNat ≤ jw.toNat ∧ let su : FullState :=
            { sw_fail with core := { sw_fail.core with wvec := wvecu, wstk := wstku,
                                                       wusable := wuu } }
          su.LengthsOk c ∧ ModeWatchesInv F_next su.core ∧ (FullMem c su ⋆ R) muk)
        (fun (uk, _) _ => jw.toNat - uk.toNat) (fun Juk hJuk => by
          fid_hsteps_to_jump
          exact hJuk (0#32, ()) mw' ⟨wvec', wstk', wu', Nat.zero_le _, hlenw', hwatw', hmw'⟩)
        (fun Juk (uk, ()) muk ⟨wvecu, wstku, wuu, huk_le, hlenu, hwatu, hmuk⟩ ihuk => ?_)
      let su : FullState :=
        { sw_fail with core := { sw_fail.core with wvec := wvecu, wstk := wstku, wusable := wuu } }
      c0_hsplit
      · have huk_lt : uk.toNat < jw.toNat := by c0_bound
        have huk1 : (uk + 1#32).toNat = uk.toNat + 1 := by c0_bound
        have huk_tmp : (BitVec.setWidth 64 uk).toNat < su.core.tmp.length := by
          rw [bv64_setWidth_32, hlenu.core_ok.tmp_len_arr]; omega
        c0_hsteps; c0_call hUnwatch; refine ⟨c, su, R, rfl, hlenu, hwatu.layout, hmuk,
          fun wvecu' wstku' wuu' mu' hlenu' _ hwatu' hmu' => ?_⟩
        fid_hsteps_to_jump; exact ihuk (uk + 1#32, ()) mu' (by dsimp only; rw [huk1]; omega)
          ⟨wvecu', wstku', wuu', by rw [huk1]; omega, hlenu', hwatu' F_next hwatu, hmu'⟩
      · have hncr_ar_u : (BitVec.ofNat 64 ncr0).toNat < su.core.arena.length := by
          rw [hncr_nat, hlenu.core_ok.arena_len_arr]; omega
        fid_hsteps_to_jump; have ⟨hinv_app, hmono_app⟩ := fullDenseInvW_of_append_clause hinv_tmp
          htk_ge3 hlenu hhold_j hns_cp hsz_cp hnew_lt hnew_nd hnew_ent hwatu
        have hncr_ref : ncr0 ∈ fullArenaClauseRefsCore su.core := by
          change ncr0 ∈ fullArenaClauseRefsCore st_cp.core
          rw [hrefs_cp]; exact List.mem_append_right _ (by dsimp only [ncr0]; simp)
        have ⟨hinv_mg, hmono_mg⟩ := fullDenseInvW_of_markGarb hinv_app hncr_ref
          (su.core.arena_garbage + 3#64 + BitVec.setWidth 64 tk)
        have hm_mg : (FullMem c { su with core := { su.core with
            arena := su.core.arena.set ncr0 (fullArenaHdrCore su.core ncr0 ||| 0x00080000#32)
            arena_garbage := su.core.arena_garbage + 3#64 + BitVec.setWidth 64 tk } } ⋆ R) m := by
          have hhdr : fullArenaHdrCore su.core ncr0 =
              su.core.arena[ncr0]'(by rw [hlenu.core_ok.arena_len_arr]; omega) := by
            unfold fullArenaHdrCore
            rw [List.getElem?_eq_getElem (by rw [hlenu.core_ok.arena_len_arr]; omega),
              Option.getD_some]
          rw [hhdr]; dsimp only [ncr0] at hncr_nat ⊢
          simp only [hncr_nat, show (524288 : BitVec 32) = 0x00080000#32 from rfl,
            show (3 : BitVec 64) = 3#64 from rfl] at hm ⊢
          exact hm
        exact hJw_exit (false, jw, ()) m ⟨_, hm_mg, hinv_mg, hcvm, hfuelm, hsbm, htmm, htrm,
          fidBvaArenaMono_trans hmono (fidBvaArenaMono_trans hmono_app hmono_mg), hresm⟩
  · fid_hsteps_to_jump
    have ⟨hinv_app, hmono_app⟩ := fullDenseInvW_of_append_clause hinv_tmp
      htk_ge3 hlenw hhold_j hns_cp hsz_cp hnew_lt hnew_nd hnew_ent hwatw
    exact hJw_exit (true, jw, ()) mjw ⟨sw, hmjw, hinv_app, hcvm, hfuelm, hsbm, htmm, htrm,
      fidBvaArenaMono_trans hmono hmono_app, hresm⟩

theorem s7_bva_large_top_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hAllocCl : ∀ a m Q X, Full.fullAllocClSpec a m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] a m Q X)
    (hWPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hUnwatch : ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur F_next : List (List Nat)} {s stm : FullState}
    {R : Mem 64 → Prop} {best_k mi c_top fresh : Val i32}
    {J4 : Cont [i32, .bool]} {J6 : Cont [.bool]} {mm : Mem 64} {resm : List Nat}
    (hinv : FullDenseInvW c F0 F_cur s)
    (hbk_sc : best_k.toNat < c.scratch_cap)
    (hfresh1 : (fresh ^^^ 1#32).toNat = 2 * s.core.cur_vars + 1)
    (hresm_lt : ∀ x ∈ resm, x < 2 * s.core.cur_vars) (hresm_nd : (resm.map (· / 2)).Nodup)
    (hresm_ent : (cnfOfClauses F_next).EntailsClause (cnfClause ((2 * s.core.cur_vars + 1) ::
      resm)))
    (hct_ref0 : c_top.toNat ∈ fullArenaClauseRefsCore s.core)
    (hct_ng0 : fullArenaClauseGarbCore s.core c_top.toNat = false)
    (hct_sz3 : 3 ≤ fullArenaClauseSizeCore s.core c_top.toNat)
    (hfbk_mem : (s.scratch.scratch_buf[best_k.toNat]?.getD 0#32).toNat ∈
      fullArenaClauseLitsCore s.core c_top.toNat)
    (hres_perm_f : resm.Perm ((fullArenaClauseLitsCore s.core c_top.toNat).filter
      (· != (s.scratch.scratch_buf[best_k.toNat]?.getD 0#32).toNat)))
    (hmm : (FullMem c stm ⋆ R) mm) (hstm : S7StOk c F0 F_next s stm)
    (hAbort : ∀ st1 m1, (FullMem c st1 ⋆ R) m1 → S7StOk c F0 F_next s st1 →
      J4 (mi, false, ()) m1)
    (hDone : ∀ (ok' : Bool) st1 m1, (FullMem c st1 ⋆ R) m1 →
      S7StOk c F0 F_next s st1 → J6 (ok', ()) m1) :
    wp Γ Q X (fidBvaLargeTopExpr c.hdr c.pArena c.pScratchBuf c.pFlags c.pTmp
      best_k mi c_top fresh J4 J6) mm := by
  obtain ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono, hresm⟩ := hstm
  have hmx := c.hmaxv; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx har_b hscr_b; have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hclm := hinvm.1.core_ok; have hscm := hinvm.1.scratch_ok; have hcv_le :=
    hclm.cur_vars_le; have hsb_len := hsc.scratch_buf_len; let old_cv := s.core.cur_vars
  obtain ⟨hct_refm, hct_szm, hct_litsm⟩ := hmono c_top.toNat hct_ref0
  have hct_wfm := hinvm.2.1.arena.refs_wf c_top.toNat hct_refm
  have hct_sz_eq : (stm.core.arena[c_top.toNat + 2]'(by
      have := hclm.arena_len_le; have := hclm.arena_len_arr; omega)).toNat =
      fullArenaClauseSizeCore s.core c_top.toNat := by
    rw [← hct_szm]; unfold fullArenaClauseSizeCore; rw [List.getElem?_eq_getElem (by
      have := hclm.arena_len_le; have := hclm.arena_len_arr; omega), Option.getD_some]
  let csz_bv := stm.core.arena[c_top.toNat + 2]'(by
    have := hclm.arena_len_le; have := hclm.arena_len_arr; omega)
  have hcsz_s : csz_bv.toNat = fullArenaClauseSizeCore s.core c_top.toNat := hct_sz_eq
  let C_lits := fullArenaClauseLitsCore s.core c_top.toNat
  have hC_len : C_lits.length = csz_bv.toNat := by
    rw [hcsz_s]; exact FullBvaFwdHelpers.fullArenaClauseLitsCore_length (by
      have := (hinv.2.1.arena.refs_wf c_top.toNat hct_ref0).2.2.1
      have := (hinv.2.1.arena.refs_wf c_top.toNat hct_ref0).2.2.2.1
      have := hcl.arena_len_le; have := hcl.arena_len_arr; omega)
  have hC_nd_vars : (C_lits.map (· / 2)).Nodup := hinv.2.2.2.1 c_top.toNat hct_ref0 hct_ng0
  have hC_nd : C_lits.Nodup := nodup_of_map_div2 hC_nd_vars
  have hC_len_le_cv : csz_bv.toNat ≤ old_cv := by
    rw [← hC_len, ← List.length_map (· / 2)]; exact nodup_lt_length_le hC_nd_vars fun v hv => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
      have := hinv.2.1.arena.lits_lt c_top.toNat hct_ref0 hct_ng0 l hl; omega
  let flit := s.scratch.scratch_buf[best_k.toNat]'(by omega)
  have hbk_sb : (BitVec.setWidth 64 best_k).toNat < stm.scratch.scratch_buf.length := by
    rw [bv64_setWidth_32, hscm.scratch_buf_len]; omega
  have hflit_eq : stm.scratch.scratch_buf[(BitVec.setWidth 64 best_k).toNat]'hbk_sb = flit := by
    dsimp only [flit]; simp only [hsbm, bv64_setWidth_32]
  have hfbk_mem' : flit.toNat ∈ C_lits := by
    simpa only [flit, List.getElem?_eq_getElem (by omega : best_k.toNat <
      s.scratch.scratch_buf.length), Option.getD_some] using hfbk_mem
  have hfilt_len : (C_lits.filter (· != flit.toNat)).length + 1 = csz_bv.toNat := by
    rw [← hC_len]; exact filter_ne_nodup_length hC_nd hfbk_mem'
  have hct2_n : (BitVec.setWidth 64 c_top + 2).toNat = c_top.toNat + 2 := by
    change (BitVec.setWidth 64 c_top + 2#64).toNat = _; c0_bound
  have hct2_ar : (BitVec.setWidth 64 c_top + 2).toNat < stm.core.arena.length := by
    rw [hct2_n]; have := hclm.arena_len_le; have := hclm.arena_len_arr; omega
  have htmp0_lt : 0 < stm.core.tmp.length := by rw [hclm.tmp_len_arr]; omega
  dsimp only [fidBvaLargeTopExpr, fidBZext, fidBOp64, fidBOp32, fidBCmp32, fidBPtr32, fidBLd32]
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (tk, j, ()) mj => ∃ tmpj : List (BitVec 32),
      j.toNat ≤ csz_bv.toNat ∧ tmpj.length = c.max_vars ∧
      tk.toNat = 1 + ((C_lits.take j.toNat).filter (· != flit.toNat)).length ∧
      tmpj[0]? = some (fresh ^^^ 1#32) ∧ (∀ t, 1 ≤ t → t < tk.toNat →
        (tmpj[t]?.getD 0#32).toNat = ((C_lits.take j.toNat).filter (· != flit.toNat))[t - 1]?.getD
          0) ∧
      (FullMem c { stm with core := { stm.core with tmp := tmpj } } ⋆ R) mj)
    (fun (_, j, _) _ => csz_bv.toNat - j.toNat) (fun Jf hJf => by
      dsimp only [wp, vals, Arg.val]
      exact hJf (1#32, 0#32, ()) m ⟨_, Nat.zero_le _, by simp [hclm.tmp_len_arr], rfl,
        by rw [show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat = 0 from rfl,
          List.getElem?_set_self (by rw [hclm.tmp_len_arr]; omega)]; rfl,
        fun _ h1 h2 => by simp only [bv_c0] at h2; omega, hm⟩)
    (fun Jf (tk, j, ()) mj ⟨tmpj, hj_le, htmpj_l, htk_eq, htmp0, htmp_rest, hmj⟩ ihf => ?_)
  c0_hsteps
  · have hj_lt : j.toNat < csz_bv.toNat := by
      have h1 : j.toNat < (stm.core.arena[(BitVec.setWidth 64 c_top + 2).toNat]'hct2_ar).toNat :=
        by assumption
      simpa only [hct2_n] using h1
    have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
    have hctj_n : (BitVec.setWidth 64 c_top + 3 + BitVec.setWidth 64 j).toNat =
        c_top.toNat + 3 + j.toNat := by
      change (BitVec.setWidth 64 c_top + 3#64 + BitVec.setWidth 64 j).toNat = _; c0_bound
    have hctj_ar : c_top.toNat + 3 + j.toNat < stm.core.arena.length := by
      have := hclm.arena_len_le; have := hclm.arena_len_arr; omega
    have hCj_eq : C_lits[j.toNat]'(by rw [hC_len]; exact hj_lt) =
        (stm.core.arena[c_top.toNat + 3 + j.toNat]'hctj_ar).toNat := by
      have h1 := FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (k := stm.core)
        (r := c_top.toNat) (j := j.toNat) (by rw [hct_szm]; omega) hctj_ar
      rw [hct_litsm, List.getElem?_eq_getElem (by rw [hC_len]; exact hj_lt)] at h1
      exact Option.some.inj h1
    have htake_succ := FullBvaFwdHelpers.take_succ_filter_eq (l := C_lits)
      (i := j.toNat) (x := flit.toNat) (by rw [hC_len]; exact hj_lt)
    have hsub_len : ((C_lits.take (j.toNat + 1)).filter (· != flit.toNat)).length ≤
        (C_lits.filter (· != flit.toNat)).length :=
      List.Sublist.length_le (List.Sublist.filter _ (List.take_sublist _ _))
    have hctj_mod : (c_top.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) % 2 ^ 64 =
        c_top.toNat + 3 + j.toNat := by
      rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; omega
    c0_hsteps_nogrp; refine wp_join_group (ts := [i32])
      (fun (tk', ()) m' => ∃ tmp' : List (BitVec 32), tmp'.length = c.max_vars ∧
        tk'.toNat = 1 + ((C_lits.take (j.toNat + 1)).filter (· != flit.toNat)).length ∧
        tmp'[0]? = some (fresh ^^^ 1#32) ∧
        (∀ t, 1 ≤ t → t < tk'.toNat → (tmp'[t]?.getD 0#32).toNat =
          ((C_lits.take (j.toNat + 1)).filter (· != flit.toNat))[t - 1]?.getD 0) ∧
        (FullMem c { stm with core := { stm.core with tmp := tmp' } } ⋆ R) m')
      (fun _ (tk', ()) m' ⟨tmp', htl', htk', h0', hrest', hm'⟩ => by
        fid_hsteps_to_jump; exact ihf (tk', j + 1#32, ()) m' (by dsimp only; rw [hj1]; omega)
          ⟨tmp', by rw [hj1]; omega, htl', by rw [hj1]; exact htk', h0',
           fun t ht1 ht2 => by rw [hj1]; exact hrest' t ht1 ht2, hm'⟩)
      (fun Jif hJif => ?_)
    c0_hsplit
    · have hne_bv : stm.core.arena[c_top.toNat + 3 + j.toNat]'hctj_ar ≠ flit := by
        have h1 : ¬ stm.core.arena[(c_top.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) %
            2 ^ 64]'(by rw [hctj_mod]; exact hctj_ar) =
            stm.scratch.scratch_buf[best_k.toNat]'(by rw [hscm.scratch_buf_len]; omega) := by
          assumption
        simpa only [hctj_mod, flit, hsbm] using h1
      have hne_nat : C_lits[j.toNat]'(by rw [hC_len]; exact hj_lt) ≠ flit.toNat := by
        rw [hCj_eq]; intro h; exact hne_bv (BitVec.eq_of_toNat_eq h)
      have htk_succ_eq : ((C_lits.take (j.toNat + 1)).filter (· != flit.toNat)).length =
          ((C_lits.take j.toNat).filter (· != flit.toNat)).length + 1 := by
        rw [htake_succ, ite_eq_left (bne_iff_ne.mpr hne_nat), List.length_append]; rfl
      have htk_lt_tmp : tk.toNat < tmpj.length := by omega
      have htk1 : (tk + 1#32).toNat = tk.toNat + 1 := by c0_bound
      fid_hsteps_to_jump; refine hJif (tk + 1#32, ()) m
        ⟨tmpj.set tk.toNat (stm.core.arena[c_top.toNat + 3 + j.toNat]'hctj_ar),
         by simp [htmpj_l], by rw [htk1, htk_succ_eq]; omega,
         by rw [List.getElem?_set_ne (by omega)]; exact htmp0, fun t ht1 ht2 => ?_, ?_⟩
      · rw [htk1] at ht2; rw [htake_succ, ite_eq_left (bne_iff_ne.mpr hne_nat)]
        by_cases hte : t = tk.toNat
        · subst hte
          rw [List.getElem?_set_self htk_lt_tmp, Option.getD_some,
            List.getElem?_append_right (by omega),
            show tk.toNat - 1 - ((C_lits.take j.toNat).filter (· != flit.toNat)).length = 0 by
              omega]
          simp [hCj_eq]
        · rw [List.getElem?_set_ne (Ne.symm hte), List.getElem?_append_left (by omega)]
          exact htmp_rest t ht1 (by omega)
      · simp only [hctj_n, bv64_setWidth_32] at hm; exact hm
    · have heq_bv : stm.core.arena[c_top.toNat + 3 + j.toNat]'hctj_ar = flit := by
        have h1 : stm.core.arena[(c_top.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) %
            2 ^ 64]'(by rw [hctj_mod]; exact hctj_ar) =
            stm.scratch.scratch_buf[best_k.toNat]'(by rw [hscm.scratch_buf_len]; omega) := by
          assumption
        simpa only [hctj_mod, flit, hsbm] using h1
      have heq_nat : (C_lits[j.toNat]'(by rw [hC_len]; exact hj_lt) != flit.toNat) = false := by
        rw [hCj_eq, heq_bv]; simp
      have htake_eq : (C_lits.take (j.toNat + 1)).filter (· != flit.toNat) =
          (C_lits.take j.toNat).filter (· != flit.toNat) := by
        rw [htake_succ, heq_nat]; simp
      dsimp only [wp, vals, Arg.val]; exact hJif (tk, ()) mj
        ⟨tmpj, htmpj_l, by rw [htake_eq]; exact htk_eq, htmp0,
         fun t ht1 ht2 => by rw [htake_eq]; exact htmp_rest t ht1 ht2, hmj⟩
  · have hj_eq : j.toNat = csz_bv.toNat := by
      have h1 : ¬ j.toNat < (stm.core.arena[(BitVec.setWidth 64 c_top + 2).toNat]'hct2_ar).toNat :=
        by assumption
      have h2 : ¬ j.toNat < csz_bv.toNat := (by simpa only [hct2_n] using h1); omega
    rw [hj_eq, ← hC_len, List.take_length] at htk_eq htmp_rest
    have htk_csz : tk.toNat = csz_bv.toNat := by omega
    let st_tmp : FullState := { stm with core := { stm.core with tmp := tmpj } }
    have hinv_tmp : FullDenseInvW c F0 F_next st_tmp := fullDenseInvW_set_tmp hinvm htmpj_l
    c0_call hAllocCl; refine ⟨c, st_tmp, R, rfl, hinv_tmp.1, hmj, ?_⟩; split
    · fid_hsteps_to_jump; exact hAbort st_tmp mj hmj ⟨hinv_tmp, hcvm, hfuelm, hsbm, htmm, htrm,
        hmono, hresm⟩
    · intro ar1 ma1; dsimp only; intro hlen_a1 hhold_a1 hns_a1 hng_a1 _ hsz_a1 hma1
      have hncr_nat : (BitVec.ofNat 64 stm.core.arena_len).toNat = stm.core.arena_len := by
        have := hclm.arena_len_le; c0_bound
      c0_hsteps_nogrp
      · let ncr0 := stm.core.arena_len
        have hncr_cap : ncr0 + 3 + tk.toNat ≤ c.arena_cap := hlen_a1.core_ok.arena_len_le
        refine wp_loop_inv
          (fun (jc, ()) mjc => ∃ arj : List (BitVec 32), jc.toNat ≤ tk.toNat ∧
            arj.length = c.arena_cap ∧ (∀ i < ncr0, arj[i]? = stm.core.arena[i]?) ∧
            arj[ncr0]? = ar1[ncr0]? ∧ arj[ncr0 + 2]? = ar1[ncr0 + 2]? ∧
            (∀ t < jc.toNat, arj[ncr0 + 3 + t]? = tmpj[t]?) ∧
            (FullMem c { st_tmp with core := { st_tmp.core with
              arena := arj, arena_len := ncr0 + 3 + tk.toNat } } ⋆ R) mjc)
          (fun (jc, _) _ => tk.toNat - jc.toNat) (fun Jcp hJcp => by
            fid_hsteps_to_jump
            exact hJcp (0#32, ()) ma1 ⟨ar1, Nat.zero_le _, hlen_a1.core_ok.arena_len_arr,
              hhold_a1, rfl, rfl, fun _ h => by simp only [bv_c0] at h; omega, hma1⟩)
          (fun Jcp (jc, ()) mjc ⟨arj, hjc_le, harj_l, hhold_j, harj0, harj2, hcp_j, hmjc⟩ ihcp =>
            ?_)
        c0_hsteps_nogrp
        · have hjc_lt : jc.toNat < tk.toNat := by c0_bound
          have hjc1 : (jc + 1#32).toNat = jc.toNat + 1 := by c0_bound
          have hncr_jc : (BitVec.ofNat 64 st_tmp.core.arena_len + 3 +
              BitVec.setWidth 64 jc).toNat = ncr0 + 3 + jc.toNat := by
            change (BitVec.ofNat 64 ncr0 + 3#64 + BitVec.setWidth 64 jc).toNat = _; c0_bound
          have hjc_tmp : jc.toNat < tmpj.length := by omega
          fid_hsteps_to_jump; refine ihcp (jc + 1#32, ()) m (by dsimp only; rw [hjc1]; omega)
            ⟨arj.set (ncr0 + 3 + jc.toNat) (tmpj[jc.toNat]'hjc_tmp),
             by rw [hjc1]; omega, by simp [harj_l],
             fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact hhold_j i hi,
             by rw [List.getElem?_set_ne (by omega)]; exact harj0,
             by rw [List.getElem?_set_ne (by omega)]; exact harj2, fun t ht => by
               rw [hjc1] at ht; by_cases hte : t = jc.toNat
               · subst hte; rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem hjc_tmp]
               · rw [List.getElem?_set_ne (by omega)]; exact hcp_j t (by omega),
             by simp only [hncr_jc, bv64_setWidth_32] at hm; exact hm⟩
        · have hjc_eq : jc.toNat = tk.toNat := by c0_bound
          rw [hjc_eq] at hcp_j
          let st_cp : FullState :=
            { st_tmp with core := { st_tmp.core with arena := arj,
                                                     arena_len := ncr0 + 3 + tk.toNat } }
          have hlen_cp : st_cp.LengthsOk c :=
            ⟨{ hlen_a1.core_ok with arena_len_arr := harj_l }, hlen_a1.scratch_ok⟩
          have hns_cp : (arj[ncr0]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
            rw [harj0]; exact hns_a1
          have hsz_cp : (arj[ncr0 + 2]?.getD 0#32).toNat = tk.toNat := by
            rw [harj2]; exact hsz_a1
          have hrefs_cp : fullArenaClauseRefsCore st_cp.core =
              fullArenaClauseRefsCore stm.core ++ [ncr0] :=
            fullArenaClauseRefsCore_append hinvm.2.1.arena (by omega) rfl hhold_j hns_cp hsz_cp
          have hwat_cp : ModeWatchesInv F_next st_cp.core :=
            hinvm.2.1.watches.with_wstk rfl rfl rfl rfl rfl
              (fun r hr => by rw [hrefs_cp]; exact List.mem_append_left _ hr)
          have hnew_lits_eq : fullArenaClauseLitsCore { stm.core with arena := arj } ncr0 =
              (2 * old_cv + 1) :: C_lits.filter (· != flit.toNat) := by
            rw [fullArenaLitsCore_eq_map (sz := tk.toNat)
              (by unfold fullArenaClauseSizeCore; exact hsz_cp) (by dsimp only; omega)]
            apply List.ext_getElem?; intro t; cases t with
            | zero =>
              rw [List.getElem?_map, List.getElem?_range (by omega), Option.map_some,
                Nat.add_zero, hcp_j 0 (by omega), htmp0, Option.getD_some, hfresh1]; rfl
            | succ t' =>
              by_cases ht : t' + 1 < tk.toNat
              · rw [List.getElem?_map, List.getElem?_range ht, Option.map_some,
                  hcp_j (t' + 1) ht, htmp_rest (t' + 1) (by omega) ht, Nat.add_sub_cancel,
                  List.getElem?_cons_succ,
                  List.getElem?_eq_getElem (by omega : t' < (C_lits.filter (· !=
                    flit.toNat)).length),
                  Option.getD_some]
              · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
          have hnew_perm : (fullArenaClauseLitsCore { stm.core with arena := arj }
              ncr0).Perm ((2 * old_cv + 1) :: resm) := by
            rw [hnew_lits_eq]; have hf' : resm.Perm (C_lits.filter (· != flit.toNat)) := by
              simpa only [flit, List.getElem?_eq_getElem (by omega : best_k.toNat <
                s.scratch.scratch_buf.length), Option.getD_some] using hres_perm_f
            exact List.Perm.cons _ hf'.symm
          have hnew_lt :
              ∀ l ∈ fullArenaClauseLitsCore { stm.core with arena := arj } ncr0,
              l < 2 * stm.core.cur_vars := by
            intro l hl; rw [hcvm]; rcases List.mem_cons.mp (hnew_perm.subset hl) with rfl | hr
            · omega
            · have := hresm_lt l hr; omega
          have hnew_nd : ((fullArenaClauseLitsCore { stm.core with arena := arj }
              ncr0).map (· / 2)).Nodup := by
            have hp := hnew_perm.map (· / 2)
            refine (List.nodup_cons.mpr ⟨?_, hresm_nd⟩).perm hp.symm
            intro hmem; obtain ⟨x, hx, hdiv⟩ := List.mem_map.mp hmem
            have := hresm_lt x hx; dsimp only [old_cv] at *; omega
          have hnew_ent : (cnfOfClauses F_next).EntailsClause
              (cnfClause (fullArenaClauseLitsCore { stm.core with arena := arj } ncr0)) :=
            clause_entails_of_perm hnew_perm.symm hresm_ent
          have htmp_lt :
              ∀ t (ht : t < tk.toNat), (tmpj[t]'(by omega)).toNat < 2 * (old_cv + 1) := by
            intro t ht; have hmem : (tmpj[t]'(by omega)).toNat ∈
                fullArenaClauseLitsCore { stm.core with arena := arj } ncr0 := by
              rw [fullArenaLitsCore_eq_map (sz := tk.toNat)
                (by unfold fullArenaClauseSizeCore; exact hsz_cp) (by dsimp only; omega)]
              refine List.mem_map.mpr ⟨t, List.mem_range.mpr ht, ?_⟩
              rw [hcp_j t ht, List.getElem?_eq_getElem (by omega), Option.getD_some]
            simpa only [hcvm] using hnew_lt _ hmem
          exact s7_bva_large_watch_wp (stm := stm) hWPush hUnwatch
            ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono, hresm⟩ htmpj_l (by omega) (by omega)
            hncr_cap hhold_j hns_cp hsz_cp hnew_lt hnew_nd hnew_ent (fun t ht => htmp_lt t ht)
            hlen_cp hrefs_cp hwat_cp hmjc hDone
/-! ## 3. `Step7RowRefOk` Transport Lemmas -/

/-- A Fidelity BVA row entry of a dense state is a valid Step-7 matrix ref. -/
theorem step7RowRefOk_of_entry {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s) {fr : Nat} {w : BitVec 32}
    {res : List Nat} (h : FidBvaRowEntryOk F_cur s fr w res) : Step7RowRefOk s w := by
  unfold FidBvaRowEntryOk at h; unfold Step7RowRefOk
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · rw [ite_eq_left hb] at h; rw [ite_eq_left hb]; exact h.1
  · rw [ite_eq_right hb] at h; rw [ite_eq_right hb]
    obtain ⟨href, hng, _, _, _, _, _⟩ := h
    have hwf := hinv.2.1.arena.refs_wf w.toNat href
    exact ⟨href, Nat.le_trans hwf.2.2.1 hwf.2.2.2.1,
      fun l hl => hinv.2.1.arena.lits_lt w.toNat href hng l hl⟩

/-- `Step7RowRefOk` survives arena growth (`FidBvaArenaMono`) and `cur_vars` growth. -/
theorem step7RowRefOk_mono {c : FullCfg} {F : List (List Nat)} {s st : FullState}
    {w : BitVec 32} (h : Step7RowRefOk s w) (hmono : FidBvaArenaMono s.core st.core)
    (hcv : s.core.cur_vars ≤ st.core.cur_vars) (har : FullArenaClausesInv c F st.core) :
    Step7RowRefOk st w := by
  unfold Step7RowRefOk at h ⊢
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · rw [ite_eq_left hb] at h ⊢; omega
  · rw [ite_eq_right hb] at h ⊢
    obtain ⟨href, _, hlits⟩ := h
    obtain ⟨href', _, hl⟩ := hmono w.toNat href
    have hwf := har.refs_wf w.toNat href'
    refine ⟨href', Nat.le_trans hwf.2.2.1 hwf.2.2.2.1, fun l hl' => ?_⟩
    have hmem : l ∈ fullArenaClauseLits s w.toNat := by
      change l ∈ fullArenaClauseLitsCore s.core w.toNat; rw [← hl]; exact hl'
    have := hlits l hmem; omega

/-! ## 4. Phase-2 Row Compaction: Pure Buffer Invariants -/

section Compaction

/-- Row offset `ro r = sb0[sc + r]`. -/
abbrev s7Ro (sc : Nat) (sb0 : List (BitVec 32)) (r : Nat) : Nat := (sb0[sc + r]?.getD 0#32).toNat
/-- Row length `qn r = sb0[2 * sc + r]`. -/
abbrev s7Qn (sc : Nat) (sb0 : List (BitVec 32)) (r : Nat) : Nat :=
  (sb0[2 * sc + r]?.getD 0#32).toNat
/-- Parent offset `po r = sb0[3 * sc + r]`. -/
abbrev s7Po (sc : Nat) (sb0 : List (BitVec 32)) (r : Nat) : Nat :=
  (sb0[3 * sc + r]?.getD 0#32).toNat

/-- Monotone bump geometry of rows `0 ..= bk` of the original buffer `sb0`. -/
@[expose] def S7Geom (sc cap bk : Nat) (sb0 : List (BitVec 32)) : Prop :=
  4 * sc ≤ cap ∧ bk < sc ∧
  (∀ r ≤ bk, 4 * sc ≤ s7Ro sc sb0 r ∧ s7Ro sc sb0 r + s7Qn sc sb0 r ≤ cap) ∧
  (∀ r ≤ bk, 0 < r → 4 * sc ≤ s7Po sc sb0 r ∧ s7Ro sc sb0 r + s7Qn sc sb0 r ≤ s7Po sc sb0 r ∧
    s7Po sc sb0 r + s7Qn sc sb0 r ≤ cap) ∧
  (∀ r r', r < r' → r' ≤ bk → s7Qn sc sb0 r' ≤ s7Qn sc sb0 r ∧
    s7Ro sc sb0 r + s7Qn sc sb0 r ≤ s7Ro sc sb0 r' ∧
    (0 < r → s7Po sc sb0 r + s7Qn sc sb0 r ≤ s7Ro sc sb0 r'))

theorem s7Geom_of {c : FullCfg} {F_cur : List (List Nat)} {s : FullState} {bk bump : Nat}
    (hmat : FidBvaMatrixInv c F_cur s (bk + 1) bump) (hlay : Step7BvaLayout c s (bk + 1)) :
    S7Geom (fidStepsCap c.scratch_cap) c.scratch_cap bk s.scratch.scratch_buf := by
  obtain ⟨_, _, hss, _, hb2, hrows⟩ := hmat
  obtain ⟨hl1, hl2⟩ := hlay
  dsimp only [S7Geom, s7Ro, s7Qn, s7Po]
  refine ⟨fidStepsCap_mul4_le _, by omega, fun r hr => ?_, fun r hr hr0 => ?_,
    fun r r' hrr hr' => hl2 r r' hrr (by omega)⟩
  · obtain ⟨_, hro, _, hroq, _, _⟩ := hrows r (by omega)
    exact ⟨hro, by omega⟩
  · obtain ⟨_, _, _, _, hpo, _⟩ := hrows r (by omega)
    obtain ⟨hpo1, hpo2⟩ := hpo hr0
    exact ⟨hpo1, hl1 r (by omega) hr0, by omega⟩

theorem s7Geom_qn_le {sc cap bk : Nat} {sb0 : List (BitVec 32)} (hg : S7Geom sc cap bk sb0)
    {r : Nat} (hr : r ≤ bk) : s7Qn sc sb0 bk ≤ s7Qn sc sb0 r := by
  rcases Nat.lt_or_eq_of_le hr with h | h
  · exact (hg.2.2.2.2 r bk h (Nat.le_refl _)).1
  · subst h; exact Nat.le_refl _

/-- Outer row-compaction invariant at `fs_i = i`: header cells except the compacted row
lengths `2 * sc + r` (`i ≤ r < bk`, now `mnv`) are unchanged, rows `i ..= bk` hold `mn` valid
(`P`) entries, rows / parents below `i` are untouched, and parent row `i` points below
`qn (i - 1)`. -/
@[expose] def S7CompInv (sc cap bk mn i : Nat) (mnv : BitVec 32) (sb0 sbv : List (BitVec 32))
    (P : BitVec 32 → Prop) : Prop :=
  sbv.length = cap ∧
  (∀ idx < 4 * sc, (∀ r, i ≤ r → r < bk → idx ≠ 2 * sc + r) → sbv[idx]? = sb0[idx]?) ∧
  (∀ r, i ≤ r → r < bk → sbv[2 * sc + r]? = some mnv) ∧
  (∀ r, i ≤ r → r ≤ bk → ∀ j < mn, P (sbv[s7Ro sc sb0 r + j]?.getD 0#32)) ∧
  (∀ r < i, ∀ j < s7Qn sc sb0 r, sbv[s7Ro sc sb0 r + j]? = sb0[s7Ro sc sb0 r + j]?) ∧
  (∀ r, 0 < r → r < i → ∀ j < s7Qn sc sb0 r,
    sbv[s7Po sc sb0 r + j]? = sb0[s7Po sc sb0 r + j]?) ∧
  (0 < i → ∀ j < mn, (sbv[s7Po sc sb0 i + j]?.getD 0#32).toNat < s7Qn sc sb0 (i - 1))

/-- Inner invariant while compacting row `q` of `sbv` into `sbw`: only row `q` and parent block
`q` change, row `q` keeps valid entries, and parent block `q` keeps pointers below
`qn (q - 1)`. -/
@[expose] def S7RowInv (sc cap q : Nat) (sb0 sbv sbw : List (BitVec 32))
    (P : BitVec 32 → Prop) : Prop :=
  sbw.length = cap ∧
  (∀ idx, ¬ (s7Ro sc sb0 q ≤ idx ∧ idx < s7Ro sc sb0 q + s7Qn sc sb0 q) →
    (0 < q → ¬ (s7Po sc sb0 q ≤ idx ∧ idx < s7Po sc sb0 q + s7Qn sc sb0 q)) →
    sbw[idx]? = sbv[idx]?) ∧
  (∀ j < s7Qn sc sb0 q, P (sbw[s7Ro sc sb0 q + j]?.getD 0#32)) ∧
  (0 < q → ∀ j < s7Qn sc sb0 q,
    (sbw[s7Po sc sb0 q + j]?.getD 0#32).toNat < s7Qn sc sb0 (q - 1))

variable {sc cap bk mn : Nat} {mnv : BitVec 32} {sb0 : List (BitVec 32)} {P : BitVec 32 → Prop}

theorem s7CompInv_base (hlen : sb0.length = cap)
    (hrow : ∀ j < mn, P (sb0[s7Ro sc sb0 bk + j]?.getD 0#32))
    (hpar : 0 < bk → ∀ j < mn,
      (sb0[s7Po sc sb0 bk + j]?.getD 0#32).toNat < s7Qn sc sb0 (bk - 1)) :
    S7CompInv sc cap bk mn bk mnv sb0 sb0 P := by
  refine ⟨hlen, fun _ _ _ => rfl, fun r h1 h2 => absurd h2 (by omega), fun r h1 h2 j hj => ?_,
    fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, hpar⟩
  have : r = bk := by omega
  subst this; exact hrow j hj

theorem s7RowInv_init {i : Nat} {sbv : List (BitVec 32)}
    (hc : S7CompInv sc cap bk mn i mnv sb0 sbv P) (hi : 1 ≤ i)
    (hrow : ∀ j < s7Qn sc sb0 (i - 1), P (sb0[s7Ro sc sb0 (i - 1) + j]?.getD 0#32))
    (hpar : 0 < i - 1 → ∀ j < s7Qn sc sb0 (i - 1),
      (sb0[s7Po sc sb0 (i - 1) + j]?.getD 0#32).toNat < s7Qn sc sb0 (i - 1 - 1)) :
    S7RowInv sc cap (i - 1) sb0 sbv sbv P := by
  obtain ⟨hlen, _, _, _, hE, hF, _⟩ := hc
  refine ⟨hlen, fun _ _ _ => rfl, fun j hj => ?_, fun hq j hj => ?_⟩
  · rw [hE (i - 1) (by omega) j hj]; exact hrow j hj
  · rw [hF (i - 1) hq (by omega) j hj]; exact hpar hq j hj

/-- Reading parent block `i` while compacting row `i - 1` sees the (compacted) parents of
row `i`, all `< qn (i - 1)`. -/
theorem s7_par_read {i : Nat} {sbv sbw : List (BitVec 32)} (hg : S7Geom sc cap bk sb0)
    (hc : S7CompInv sc cap bk mn i mnv sb0 sbv P) (hw : S7RowInv sc cap (i - 1) sb0 sbv sbw P)
    (hi : 1 ≤ i) (hib : i ≤ bk) (hmn : mn = s7Qn sc sb0 bk) {fi : Nat} (hfi : fi < mn) :
    sbw[s7Po sc sb0 i + fi]? = sbv[s7Po sc sb0 i + fi]? ∧
    (sbw[s7Po sc sb0 i + fi]?.getD 0#32).toNat < s7Qn sc sb0 (i - 1) := by
  have g1 := hg.2.2.2.2 (i - 1) i (by omega) hib
  have g2 := hg.2.2.2.1 i hib (by omega)
  have hbsc : bk < sc := hg.2.1
  have hqi := s7Geom_qn_le hg hib
  have heq : sbw[s7Po sc sb0 i + fi]? = sbv[s7Po sc sb0 i + fi]? :=
    hw.2.1 _ (by omega) (fun hq => by have := g1.2.2 hq; omega)
  exact ⟨heq, by rw [heq]; exact hc.2.2.2.2.2.2 (by omega) fi hfi⟩

theorem s7RowInv_step_pos {q : Nat} {sbv sbw : List (BitVec 32)} (hg : S7Geom sc cap bk sb0)
    (hw : S7RowInv sc cap q sb0 sbv sbw P) (hq0 : 0 < q) (hqb : q ≤ bk) {fi fj : Nat}
    (hfi : fi < s7Qn sc sb0 q) (hfj : fj < s7Qn sc sb0 q) {v1 v2 : BitVec 32}
    (hv1 : sbw[s7Po sc sb0 q + fj]? = some v1)
    (hv2 : (sbw.set (s7Po sc sb0 q + fi) v1)[s7Ro sc sb0 q + fj]? = some v2) :
    S7RowInv sc cap q sb0 sbv
      ((sbw.set (s7Po sc sb0 q + fi) v1).set (s7Ro sc sb0 q + fi) v2) P := by
  obtain ⟨hlen, hframe, hrow, hpar⟩ := hw
  have g := hg.2.2.2.1 q hqb hq0
  have g0 := hg.2.2.1 q hqb
  have hbsc : bk < sc := hg.2.1
  have hv2' : sbw[s7Ro sc sb0 q + fj]? = some v2 := by
    rw [List.getElem?_set_ne (by omega)] at hv2; exact hv2
  refine ⟨by simp [hlen], fun idx h1 h2 => ?_, fun j hj => ?_, fun _ j hj => ?_⟩
  · have h2' := h2 hq0
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hframe idx h1 h2
  · by_cases hje : j = fi
    · subst hje
      rw [List.getElem?_set_self (by simp [hlen]; omega), Option.getD_some]
      have := hrow fj hfj; rw [hv2', Option.getD_some] at this; exact this
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hrow j hj
  · rw [List.getElem?_set_ne (by omega)]
    by_cases hje : j = fi
    · subst hje
      rw [List.getElem?_set_self (by omega), Option.getD_some]
      have := hpar hq0 fj hfj; rw [hv1, Option.getD_some] at this; exact this
    · rw [List.getElem?_set_ne (by omega)]; exact hpar hq0 j hj

theorem s7RowInv_step_zero {sbv sbw : List (BitVec 32)} (hg : S7Geom sc cap bk sb0)
    (hw : S7RowInv sc cap 0 sb0 sbv sbw P) {fi fj : Nat}
    (hfi : fi < s7Qn sc sb0 0) (hfj : fj < s7Qn sc sb0 0) {v2 : BitVec 32}
    (hv2 : sbw[s7Ro sc sb0 0 + fj]? = some v2) :
    S7RowInv sc cap 0 sb0 sbv (sbw.set (s7Ro sc sb0 0 + fi) v2) P := by
  obtain ⟨hlen, hframe, hrow, _⟩ := hw
  have g0 := hg.2.2.1 0 (Nat.zero_le _)
  have hbsc : bk < sc := hg.2.1
  refine ⟨by simp [hlen], fun idx h1 h2 => ?_, fun j hj => ?_, fun h => absurd h (by omega)⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hframe idx h1 h2
  · by_cases hje : j = fi
    · subst hje
      rw [List.getElem?_set_self (by omega), Option.getD_some]
      have := hrow fj hfj; rw [hv2, Option.getD_some] at this; exact this
    · rw [List.getElem?_set_ne (by omega)]; exact hrow j hj

theorem s7CompInv_step {i : Nat} {sbv sbw : List (BitVec 32)} (hg : S7Geom sc cap bk sb0)
    (hc : S7CompInv sc cap bk mn i mnv sb0 sbv P) (hw : S7RowInv sc cap (i - 1) sb0 sbv sbw P)
    (hi : 1 ≤ i) (hib : i ≤ bk) (hmn : mn = s7Qn sc sb0 bk) :
    S7CompInv sc cap bk mn (i - 1) mnv sb0 (sbw.set (2 * sc + (i - 1)) mnv) P := by
  obtain ⟨hlen, hB, hC, hD, hE, hF, _⟩ := hc
  obtain ⟨hwlen, hframe, hrow, hpar⟩ := hw
  have g4 := hg.1
  have hbsc : bk < sc := hg.2.1
  have gq := hg.2.2.1 (i - 1) (by omega)
  have gqp : 0 < i - 1 → _ := hg.2.2.2.1 (i - 1) (by omega)
  have hqmn : mn ≤ s7Qn sc sb0 (i - 1) := hmn ▸ s7Geom_qn_le hg (by omega)
  -- header cells are below every row / parent block
  have hhdr : ∀ idx < 4 * sc, sbw[idx]? = sbv[idx]? := fun idx hidx =>
    hframe idx (by omega) (fun hq => by have := gqp hq; omega)
  refine ⟨by simp [hwlen], fun idx hidx hne => ?_, fun r h1 h2 => ?_,
    fun r h1 h2 j hj => ?_, fun r hr j hj => ?_, fun r hr0 hr j hj => ?_, fun hq j hj => ?_⟩
  · rw [List.getElem?_set_ne (fun h => hne (i - 1) (Nat.le_refl _) (by omega) h.symm),
      hhdr idx hidx]
    exact hB idx hidx (fun r h1 h2 => hne r (by omega) h2)
  · by_cases hr : r = i - 1
    · subst hr; rw [List.getElem?_set_self (by omega)]
    · rw [List.getElem?_set_ne (by omega), hhdr _ (by omega)]; exact hC r (by omega) h2
  · have gr := hg.2.2.1 r h2
    rw [List.getElem?_set_ne (by omega)]
    by_cases hr : r = i - 1
    · subst hr; exact hrow j (by omega)
    · have g := hg.2.2.2.2 (i - 1) r (by omega) h2
      rw [hframe _ (by omega) (fun hq => by have := g.2.2 hq; omega)]
      exact hD r (by omega) h2 j hj
  · have gr := hg.2.2.1 r (by omega)
    have g := hg.2.2.2.2 r (i - 1) hr (by omega)
    rw [List.getElem?_set_ne (by omega),
      hframe _ (by omega) (fun hq => by have := gqp hq; omega)]
    exact hE r (by omega) j hj
  · have gr := hg.2.2.2.1 r (by omega) hr0
    have g := hg.2.2.2.2 r (i - 1) hr (by omega)
    have g' := g.2.2 hr0
    rw [List.getElem?_set_ne (by omega),
      hframe _ (by omega) (fun hq => by have := gqp hq; omega)]
    exact hF r hr0 (by omega) j hj
  · have gp := gqp hq
    rw [List.getElem?_set_ne (by omega)]
    exact hpar hq j (by omega)

/-- Every entry of rows `0 ..= bk` of a Fidelity matrix is a valid Step-7 ref in any later state
`st` with a monotone arena and more variables. -/
theorem s7_rows_ok {c : FullCfg} {F0 : CNF Nat} {F_cur F' : List (List Nat)} {s st : FullState}
    {bk bump : Nat} (hinv : FullDenseInvW c F0 F_cur s)
    (hmat : FidBvaMatrixInv c F_cur s (bk + 1) bump) (hmono : FidBvaArenaMono s.core st.core)
    (hcv : s.core.cur_vars ≤ st.core.cur_vars) (har : FullArenaClausesInv c F' st.core) :
    ∀ r ≤ bk, ∀ j < s7Qn (fidStepsCap c.scratch_cap) s.scratch.scratch_buf r,
      Step7RowRefOk st (s.scratch.scratch_buf[s7Ro (fidStepsCap c.scratch_cap)
        s.scratch.scratch_buf r + j]?.getD 0#32) := by
  intro r hr j hj
  obtain ⟨_, _, _, _, _, hm⟩ := hmat.2.2.2.2.2 r (by omega)
  obtain ⟨_, _, _, hok, _, _⟩ := hm j hj
  exact step7RowRefOk_mono (step7RowRefOk_of_entry hinv hok) hmono hcv har

/-- Parent pointers of rows `0 < r ≤ bk` point below `qn (r - 1)`. -/
theorem s7_pars_ok {c : FullCfg} {F_cur : List (List Nat)} {s : FullState} {bk bump : Nat}
    (hmat : FidBvaMatrixInv c F_cur s (bk + 1) bump) :
    ∀ r ≤ bk, 0 < r → ∀ j < s7Qn (fidStepsCap c.scratch_cap) s.scratch.scratch_buf r,
      (s.scratch.scratch_buf[s7Po (fidStepsCap c.scratch_cap) s.scratch.scratch_buf r +
        j]?.getD 0#32).toNat < s7Qn (fidStepsCap c.scratch_cap) s.scratch.scratch_buf (r - 1) := by
  intro r hr hr0 j hj
  obtain ⟨_, _, _, _, _, hm⟩ := hmat.2.2.2.2.2 r (by omega)
  obtain ⟨_, _, _, _, _, hpar⟩ := hm j hj
  exact (hpar hr0).1

/-- After compaction (`fs_i = 0`) every row `q ≤ bk` keeps its fresh literal and offset, has
length `mn`, fits in the buffer, and holds `mn` valid (`P`) entries. -/
theorem s7CompInv_zero {sbv : List (BitVec 32)} (hg : S7Geom sc cap bk sb0)
    (hc : S7CompInv sc cap bk mn 0 mnv sb0 sbv P) (hmn : mn = s7Qn sc sb0 bk)
    (hmnv : mnv.toNat = mn) :
    ∀ q ≤ bk, sbv[q]? = sb0[q]? ∧ s7Ro sc sbv q = s7Ro sc sb0 q ∧ s7Qn sc sbv q = mn ∧
      s7Ro sc sb0 q + mn ≤ cap ∧ ∀ j < mn, P (sbv[s7Ro sc sbv q + j]?.getD 0#32) := by
  intro q hq
  obtain ⟨_, hB, hC, hD, _, _, _⟩ := hc
  have g4 := hg.1
  have hbsc : bk < sc := hg.2.1
  have gq := hg.2.2.1 q hq
  have hqmn : mn ≤ s7Qn sc sb0 q := hmn ▸ s7Geom_qn_le hg hq
  have hro : s7Ro sc sbv q = s7Ro sc sb0 q := by
    simp only [s7Ro]; rw [hB (sc + q) (by omega) (fun r _ _ => by omega)]
  refine ⟨hB q (by omega) (fun r _ _ => by omega), hro, ?_, by omega, fun j hj => ?_⟩
  · rcases Nat.lt_or_eq_of_le hq with h | h
    · simp only [s7Qn]; rw [hC q (Nat.zero_le _) h, Option.getD_some, hmnv]
    · simp only [s7Qn]; rw [hB (2 * sc + q) (by omega) (fun r _ h2 => by omega), h]
      exact hmn.symm
  · rw [hro]; exact hD q (Nat.zero_le _) hq j hj

end Compaction

end LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof2a

end
