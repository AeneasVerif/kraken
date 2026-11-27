/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S2BCPWatchProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof2b
public import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof2d
public import LeanQbe.T.Examples.Kissat.FullM7BcpHotProof1c
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0Step

/-!
# Kissat Fidelity Step 13 Shard S2-A Inner-Loop Proofs (`FullFidelityStep13S2BCPWatchProof1`)

Plain `public section` (`@[expose]` ONLY on concrete AST `Expr` builders, `0` `@[expose]` on
theorems, `0` `import all`, `<= 100` cols, every theorem `<= 380` lines):
1. `jumpreasons` (`bigbig`) binary-reason soundness lemmas (`s13_bin_resolve`,
   `s13_bin_jumpreason_nw_step`, `s13_bin_jumpreason_step`).
2. Unswapped large-clause arena swap (`s13_ar_swap_nw`), `s13_clause_falsified_of_find_repl_none`,
   and `s13_large_confl_w0` (keeping raw `w0`).
3. Shared parameterized AST builders (`s13LpAssignTailExpr`, `s13LpBinStepExpr isBeyond`,
   `s13LpReplDelExpr`, `s13LpNoReplExpr isBeyond`, `s13LpScanExpr isBeyond`,
   `s13LpLargeStepExpr isBeyond`, `s13LpLoopExpr isBeyond`) covering both
   `full_propagate_ignore{_hot}` (`isBeyond = false`) and
   `full_propagate_beyond_m7` (`isBeyond = true`).
4. Inner-loop step proofs `s13_lp_bin_wp` and `s13_lp_repl_del_wp`.
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

/-! ## 1. `jumpreasons` (`bigbig`) Binary-Reason & Unswapped-Arena Lemmas -/

/-- Binary resolution: from `(not_lit ^ 1, ot)` and `(not_lit, blk)`, derive `(blk, ot)`. -/
theorem s13_bin_resolve {F : CNF Nat} {not_lit ot blk : Nat}
    (h1 : F.EntailsClause (cnfClause [not_lit ^^^ 1, ot]))
    (h2 : F.EntailsClause (cnfClause [not_lit, blk])) :
    F.EntailsClause (cnfClause [blk, ot]) := by
  rw [CNF.entails_clause_def] at h1 h2 ⊢
  intro α hα
  have hs1 := h1 α hα
  have hs2 := h2 α hα
  simp only [clause_sat_cnfClause_iff, List.mem_cons, List.not_mem_nil, or_false] at hs1 hs2 ⊢
  rcases hs1 with ⟨l1, hl1_eq, hl1⟩ <;> rcases hs2 with ⟨l2, hl2_eq, hl2⟩
  rcases hl1_eq with hl1_eq | hl1_eq <;> rcases hl2_eq with hl2_eq | hl2_eq <;>
    (try rw [hl1_eq] at hl1) <;> (try rw [hl2_eq] at hl2)
  · exfalso
    have hsat1 : (cnfClause [litNeg not_lit]).Sat α := by
      change (cnfClause [not_lit ^^^ 1]).Sat α
      exact (sat_cnfClause_singleton α (not_lit ^^^ 1)).mpr hl1
    have hsat2 : (cnfClause [not_lit]).Sat α :=
      (sat_cnfClause_singleton α not_lit).mpr hl2
    exact absurd hsat2 ((sat_cnfClause_litNeg_iff α not_lit).mp hsat1)
  · exact ⟨_, Or.inl rfl, hl2⟩
  · exact ⟨_, Or.inr rfl, hl1⟩
  · exact ⟨_, Or.inl rfl, hl2⟩

/-- `jumpreasons` binary-assign step on `WithEmptyWatchesCore`: supports either the immediate
binary reason `PW_BIN_FLAG | not_lit` or an inherited binary reason `nr = rsns[not_lit / 2]`. -/
theorem s13_bin_jumpreason_nw_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c)
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k))
    {not_lit other jr : BitVec 32} {flags' : List (BitVec 32)} {unas' unfl' : BitVec 64}
    (hnot_lt : not_lit.toNat < 2 * k.cur_vars) (hother_lt : other.toNat < 2 * k.cur_vars)
    (hun : k.vals[other.toNat]?.getD 0#8 = 0#8)
    (hnot_false : k.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [not_lit.toNat, other.toNat]))
    (hjr : jr = ((not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32) ∨
      (k.lvl[not_lit.toNat / 2]?.getD 0#32 ≠ 0#32 ∧
        let nr := k.rsns[not_lit.toNat / 2]?.getD 0xFFFFFFFF#32
        nr ≠ 0xFFFFFFFF#32 ∧ (nr &&& 0x80000000#32) ≠ 0#32 ∧ jr = nr)) :
    let alvl := k.lvl[not_lit.toNat / 2]?.getD 0#32
    let v := other.toNat / 2
    let rsn' := if alvl = 0#32 then 0xFFFFFFFF#32 else jr
    let k' : FullCoreState :=
      { k with
        vals := (k.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
        flags := flags', lvl := k.lvl.set v alvl, rsns := k.rsns.set v rsn'
        trl := k.trl.set k.trail_end other
        trail_pos := k.trail_pos.set v (BitVec.ofNat 32 k.trail_end)
        trail_end := k.trail_end + 1, unassigned := unas', unflushed := unfl' }
    FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k') ∧
    k'.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 ∧ FullPropDecSpecs.FullTrailExt k k' := by
  intro alvl v rsn' k'
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv; have hcv := hlen.cur_vars_le
  obtain ⟨i, hi, hieq⟩ := (hnw.vals_false_iff not_lit.toNat hnot_lt).mp hnot_false
  have hvar_i : (k.trl[i]?.getD 0#32).toNat / 2 = not_lit.toNat / 2 := by
    rw [hieq, fullInv_var_xor1]
  have halvl_le : alvl.toNat ≤ k.cur_level := by
    have := hnw.lvl_le i hi; rwa [hvar_i] at this
  have hbin_props : ∀ {lit : BitVec 32}, lit.toNat < 2 * k.cur_vars →
      let r := (lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32
      r ≠ 0xFFFFFFFF#32 ∧ (r &&& 0x80000000#32) ≠ 0#32 ∧ (r &&& 0x7FFFFFFF#32).toNat = lit.toNat :=
    fun {lit} h => bv32_bin_rsn_props (x := lit) (by omega)
  rcases hjr with rfl | ⟨_, hnr_ne, hnr_flag, rfl⟩
  · obtain ⟨hne_ff, hflag, hlo⟩ := hbin_props hnot_lt
    exact unitAssign_preserves_fullWitness_nw hlen hnw hother_lt hun hnot_lt hnot_false
      hne_ff halvl_le
      (fun hl0 => entails_of_mem_or_false hent fun l hl => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with hl | hl <;> rw [hl]
        · have hli : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
            rw [hvar_i]; change alvl.toNat = 0; rw [hl0]; rfl
          exact Or.inr (by have hs := hnw.level0_sound i hi hli; rwa [hieq] at hs)
        · exact Or.inl (by simp))
      (fun _ => by
        simp only [hflag, ne_eq, not_false_eq_true, ↓reduceIte, hlo]
        exact ⟨hnot_lt, cnfClause_swap2 hent, i, hi, hieq, Nat.le_refl _⟩)
      (fun _ hlg => absurd hlg hflag)
  · let nr := k.rsns[not_lit.toNat / 2]?.getD 0xFFFFFFFF#32
    have hrs := hnw.reason_inv i hi (by
      change k.rsns[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32
      rwa [hvar_i])
    have hflag_i : (k.rsns[(k.trl[i]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := by rwa [hvar_i]
    rw [ite_eq_left hflag_i] at hrs
    have hnot_vars_nr : nr = k.rsns[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 := by
      rw [hvar_i]
    rw [← hnot_vars_nr] at hrs
    obtain ⟨hot_lt, hot_ent, m0, hm0, hm0_eq, hmlvl⟩ := hrs
    rw [hieq] at hot_ent
    rw [hvar_i] at hmlvl
    exact unitAssign_preserves_fullWitness_nw hlen hnw hother_lt hun hnot_lt hnot_false
      hnr_ne halvl_le
      (fun hl0 => entails_of_mem_or_false hent fun l hl => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with hl | hl <;> rw [hl]
        · have hli : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
            rw [hvar_i]; change alvl.toNat = 0; rw [hl0]; rfl
          exact Or.inr (by have hs := hnw.level0_sound i hi hli; rwa [hieq] at hs)
        · exact Or.inl (by simp))
      (fun _ => by
        simp only [hnr_flag, ne_eq, not_false_eq_true, ↓reduceIte]
        exact ⟨hot_lt, s13_bin_resolve hot_ent hent, m0, Nat.lt_trans hm0 hi, hm0_eq, hmlvl⟩)
      (fun _ hlg => absurd hlg hnr_flag)

/-- `PropLitInv`-lifting wrapper around `s13_bin_jumpreason_nw_step` for `s13_lp_bin_wp`. -/
theorem s13_bin_jumpreason_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_pi sem : FullState} {not_lit blk nl_lvl0 jr : BitVec 32}
    {off_v p_v q_v end_v : BitVec 64}
    {wstk' flags' : List (BitVec 32)} {ph' : List (BitVec 8)} {unas' unfl' : BitVec 64}
    (hpi : PropLitInv c F0 F_cur s_pi sem not_lit.toNat off_v.toNat q_v.toNat p_v.toNat end_v.toNat)
    (hsw : SplitWatchesInv F_cur { sem.core with wstk := wstk' } not_lit.toNat off_v.toNat
      (q_v.toNat + 1) (p_v.toNat + 1) end_v.toNat)
    (hwstk : wstk'.length = c.wcap) (hfl : flags'.length = c.max_vars)
    (hph : ph'.length = c.max_vars)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (hblk_lt : blk.toNat < 2 * sem.core.cur_vars)
    (hun : sem.core.vals[blk.toNat]?.getD 0#8 = 0#8)
    (hnl : sem.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [not_lit.toNat, blk.toNat]))
    (hp1 : (p_v + 1#64).toNat = p_v.toNat + 1) (hq1 : (q_v + 1#64).toNat = q_v.toNat + 1)
    (hjr : jr = ((not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32) ∨
      (nl_lvl0 ≠ 0#32 ∧
        let nr := sem.core.rsns[not_lit.toNat / 2]?.getD 0xFFFFFFFF#32
        nr ≠ 0xFFFFFFFF#32 ∧ (nr &&& 0x80000000#32) ≠ 0#32 ∧ jr = nr)) :
    let rsn' := if nl_lvl0 = 0#32 then 0xFFFFFFFF#32 else jr
    let sem2 : FullState :=
      { core :=
          { sem.core with
            wstk := wstk'
            vals := (sem.core.vals.set blk.toNat 1#8).set (blk.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := sem.core.lvl.set (blk.toNat / 2) nl_lvl0
            rsns := sem.core.rsns.set (blk.toNat / 2) rsn'
            trl := sem.core.trl.set sem.core.trail_end blk
            trail_pos := sem.core.trail_pos.set (blk.toNat / 2) (BitVec.ofNat 32 sem.core.trail_end)
            trail_end := sem.core.trail_end + 1, unassigned := unas', unflushed := unfl' }
        scratch := { sem.scratch with phases := ph' } }
    PropLitInv c F0 F_cur s_pi sem2 not_lit.toNat off_v.toNat (q_v + 1#64).toNat
      (p_v + 1#64).toNat end_v.toNat ∧
    sem2.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 := by
  intro rsn' sem2
  let sem1c : FullCoreState := { sem.core with wstk := wstk' }
  have hlen1 : sem1c.LengthsOk c := { hpi.len.core_ok with wstk_len_arr := hwstk }
  have hnw1 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c sem1c) :=
    fullWitnessInv_nw_congr hlen1.cur_vars_le hpi.nw rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl
  have hjr' : jr = ((not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32) ∨
      (sem1c.lvl[not_lit.toNat / 2]?.getD 0#32 ≠ 0#32 ∧
        let nr := sem1c.rsns[not_lit.toNat / 2]?.getD 0xFFFFFFFF#32
        nr ≠ 0xFFFFFFFF#32 ∧ (nr &&& 0x80000000#32) ≠ 0#32 ∧ jr = nr) := by
    simpa only [sem1c, hnl] using hjr
  have hstep := s13_bin_jumpreason_nw_step hlen1 hnw1 hnot_lt hblk_lt hun hpi.not_f hent hjr'
    (flags' := flags') (unas' := unas') (unfl' := unfl')
  have hstep' :
      let sem1core : FullCoreState := { sem.core with wstk := wstk' }
      let k2 : FullCoreState :=
        { sem1core with
          vals := (sem1core.vals.set blk.toNat 1#8).set (blk.toNat ^^^ 1) 0xFF#8
          flags := flags', lvl := sem1core.lvl.set (blk.toNat / 2) nl_lvl0
          rsns := sem1core.rsns.set (blk.toNat / 2) (if nl_lvl0 = 0#32 then 0xFFFFFFFF#32 else jr)
          trl := sem1core.trl.set sem1core.trail_end blk
          trail_pos := sem1core.trail_pos.set (blk.toNat / 2) (BitVec.ofNat 32 sem1core.trail_end)
          trail_end := sem1core.trail_end + 1, unassigned := unas', unflushed := unfl' }
      FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k2) ∧
      k2.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 ∧ FullPropDecSpecs.FullTrailExt sem1core k2 := by
    simpa only [sem1c, rsn', ← hnl] using hstep
  have hm := fastPropMem_eq_of_eq (q_v := q_v.toNat + 1) (p_v := p_v.toNat + 1) hpi hsw hwstk
    hfl hph hnot_lt hblk_lt hun hnl hstep'
  have hpi2 : PropLitInv c F0 F_cur s_pi sem2 not_lit.toNat off_v.toNat (q_v + 1#64).toNat
      (p_v + 1#64).toNat end_v.toNat := by
    refine ⟨hm.1, hm.2.1, ?_, hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2.1, hm.2.2.2.2.2.2.1,
      hm.2.2.2.2.2.2.2.1⟩
    rw [hq1, hp1]; exact hm.2.2.1
  refine ⟨hpi2, ?_⟩
  dsimp only [sem2]
  exact hm.2.2.2.2.2.2.2.2

/-- Generalized arena-watch swap `ar[cbase] = other; ar[cbase+1] = repl; ar[cbase+ri] = not_lit`
from unswapped `[l0, l1]` (`l0 = not_lit ∨ l1 = not_lit`). -/
theorem s13_ar_swap_nw {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c)
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k))
    {cref : Nat} {l0 l1 not_lit repl : BitVec 32} {ri : Nat}
    (hcref : cref ∈ fullArenaClauseRefsCore k) (hng : fullArenaClauseGarbCore k cref = false)
    (hcsz3 : 3 ≤ fullArenaClauseSizeCore k cref) (hri2 : 2 ≤ ri)
    (hri_lt : ri < fullArenaClauseSizeCore k cref)
    (hfit : cref + 3 + fullArenaClauseSizeCore k cref ≤ k.arena_len)
    (hl0 : k.arena[cref + 3]? = some l0) (hl1 : k.arena[cref + 4]? = some l1)
    (hwatch : l0 = not_lit ∨ l1 = not_lit)
    (har_ri : k.arena[cref + 3 + ri]? = some repl) :
    let other := l0 ^^^ l1 ^^^ not_lit
    let ar' := ((k.arena.set (cref + 3) other).set (cref + 4) repl).set (cref + 3 + ri) not_lit
    let k' : FullCoreState := { k with arena := ar' }
    FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k') ∧
    FullPropDecSpecs.FullArenaPermEq k k' ∧
    cref ∈ fullArenaClauseRefsCore k' ∧
    fullArenaClauseGarbCore k' cref = false ∧
    fullArenaClauseSizeCore k' cref = fullArenaClauseSizeCore k cref := by
  intro other ar' k'
  have halen := hlen.arena_len_arr; have halen_le := hlen.arena_len_le
  have hbd : cref + 3 + fullArenaClauseSizeCore k cref ≤ k.arena.length := by omega
  have hl0_eq : k.arena[cref + 3 + 0]'(by omega) = l0 :=
    Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hl0)
  have hl1_eq : k.arena[cref + 3 + 1]'(by omega) = l1 :=
    Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hl1)
  have hri_eq : k.arena[cref + 3 + ri]'(by omega) = repl :=
    Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans har_ri)
  rcases hwatch with rfl | rfl
  · have hoth : other = l1 := fid_xor_cancel_l l0 l1
    have hsw1 := full_swapLits_preserves_nw hlen hnw (cref := cref) (k1 := 0) (k2 := 1)
      hcref (by omega) (by omega)
    let k1 : FullCoreState :=
      { k with arena := (k.arena.set (cref + 3 + 0) l1).set (cref + 3 + 1) l0 }
    have hlen1 : k1.LengthsOk c := { hlen with arena_len_arr := by simp [k1, halen] }
    have hnw1 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k1) := by
      simpa only [k1, hl0_eq, hl1_eq] using hsw1.1
    have hperm1 : FullPropDecSpecs.FullArenaPermEq k k1 := by
      simpa only [k1, hl0_eq, hl1_eq] using hsw1.2
    have hcref1 : cref ∈ fullArenaClauseRefsCore k1 := hperm1.1 ▸ hcref
    have hsz1 : fullArenaClauseSizeCore k1 cref = fullArenaClauseSizeCore k cref :=
      (hperm1.2 cref hcref).1
    have hsw2 := full_swapLits_preserves_nw hlen1 hnw1 (cref := cref) (k1 := 1) (k2 := ri)
      hcref1 (by omega) (by omega)
    have har_eq : ((k1.arena.set (cref + 3 + 1) (k1.arena[cref + 3 + ri]'(by
        simp [k1, halen]; omega))).set (cref + 3 + ri)
        (k1.arena[cref + 3 + 1]'(by simp [k1, halen]; omega))) = ar' := by
      apply List.ext_getElem (by simp [k1, ar'])
      intro idx hidx hidx2
      refine Option.some.inj ?_
      rw [← List.getElem?_eq_getElem hidx, ← List.getElem?_eq_getElem hidx2]
      dsimp only [ar', k1]
      have hlen_k1 : ((k.arena.set (cref + 3 + 0) l1).set (cref + 3 + 1) l0).length =
          k.arena.length := by simp
      have hri_lt_k1 :
          cref + 3 + ri < ((k.arena.set (cref + 3 + 0) l1).set (cref + 3 + 1) l0).length := by
        rw [hlen_k1]; omega
      have h1_lt_k1 :
          cref + 3 + 1 < ((k.arena.set (cref + 3 + 0) l1).set (cref + 3 + 1) l0).length := by
        rw [hlen_k1]; omega
      have hget1_ri : ((k.arena.set (cref + 3 + 0) l1).set (cref + 3 + 1) l0)[cref + 3 + ri]? =
          some repl := by
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), har_ri]
      have hget1_1 : ((k.arena.set (cref + 3 + 0) l1).set (cref + 3 + 1) l0)[cref + 3 + 1]? =
          some l0 := by
        rw [List.getElem?_set_self (by rw [List.length_set]; omega)]
      by_cases hri' : idx = cref + 3 + ri
      · subst hri'
        rw [List.getElem?_set_self (by simp; omega), List.getElem?_set_self (by simp; omega)]
        exact (List.getElem?_eq_getElem h1_lt_k1).symm.trans hget1_1
      · rw [List.getElem?_set_ne (Ne.symm hri'), List.getElem?_set_ne (Ne.symm hri')]
        by_cases h4' : idx = cref + 4
        · subst h4'
          rw [show
              ((k.arena.set (cref + 3 + 0) l1).set (cref + 3 + 1) l0)[cref + 3 + ri]'hri_lt_k1 =
              repl from
            Option.some.inj ((List.getElem?_eq_getElem hri_lt_k1).symm.trans hget1_ri)]
          rw [List.getElem?_set_self h1_lt_k1, List.getElem?_set_self (by simp; omega)]
        · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
          by_cases h3' : idx = cref + 3
          · subst h3'
            rw [hoth, List.getElem?_set_self (by simp; omega),
              List.getElem?_set_ne (by omega), Nat.add_zero,
              List.getElem?_set_self (by omega)]
          · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
              Nat.add_zero, List.getElem?_set_ne (by omega)]
    have hperm2 : FullPropDecSpecs.FullArenaPermEq k1 k' := by
      simpa only [k', har_eq] using hsw2.2
    have hperm : FullPropDecSpecs.FullArenaPermEq k k' := hperm1.trans hperm2
    refine ⟨by simpa only [k', har_eq] using hsw2.1, hperm, hperm.1 ▸ hcref,
      (hperm.2 cref hcref).2.1.trans hng, (hperm.2 cref hcref).1⟩
  · have hoth : other = l0 := fid_xor_cancel_r l0 l1
    have hsw2 := full_swapLits_preserves_nw hlen hnw (cref := cref) (k1 := 1) (k2 := ri)
      hcref (by omega) (by omega)
    have har_eq : ((k.arena.set (cref + 3 + 1) (k.arena[cref + 3 + ri]'(by omega))).set
        (cref + 3 + ri) (k.arena[cref + 3 + 1]'(by omega))) = ar' := by
      apply List.ext_getElem (by simp [ar'])
      intro idx hidx hidx2
      refine Option.some.inj ?_
      rw [← List.getElem?_eq_getElem hidx, ← List.getElem?_eq_getElem hidx2]
      dsimp only [ar']
      by_cases hri' : idx = cref + 3 + ri
      · subst hri'
        rw [List.getElem?_set_self (by simp; omega), List.getElem?_set_self (by simp; omega)]
        exact (List.getElem?_eq_getElem (by omega)).symm.trans hl1
      · rw [List.getElem?_set_ne (Ne.symm hri'), List.getElem?_set_ne (Ne.symm hri')]
        by_cases h4' : idx = cref + 4
        · subst h4'
          rw [show k.arena[cref + 3 + ri]'(by omega) = repl from hri_eq]
          rw [List.getElem?_set_self (by omega), List.getElem?_set_self (by simp; omega)]
        · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
          by_cases h3' : idx = cref + 3
          · subst h3'; rw [hoth, List.getElem?_set_self (by omega)]; exact hl0
          · rw [List.getElem?_set_ne (by omega)]
    have hperm : FullPropDecSpecs.FullArenaPermEq k k' := by
      simpa only [k', har_eq] using hsw2.2
    refine ⟨by simpa only [k', har_eq] using hsw2.1, hperm, hperm.1 ▸ hcref,
      (hperm.2 cref hcref).2.1.trans hng, (hperm.2 cref hcref).1⟩

/-- Unit-clause deduction from `!found` on unswapped watched literals
(`l0 = not_lit ∨ l1 = not_lit`). -/
theorem s13_clause_falsified_of_find_repl_none {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {st : FullState} {cref : Nat} {l0 l1 not_lit : BitVec 32}
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st.core))
    (hcref : cref ∈ fullArenaClauseRefs st) (hng : fullArenaClauseGarb st cref = false)
    (hbd : cref + 3 + fullArenaClauseSize st cref ≤ st.core.arena.length)
    (hl0 : st.core.arena[cref + 3]? = some l0) (hl1 : st.core.arena[cref + 4]? = some l1)
    (hwatch : l0 = not_lit ∨ l1 = not_lit)
    (hnot_false : st.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hfind : ∀ k, 2 ≤ k → k < fullArenaClauseSize st cref → fullFindReplBad st cref k) :
    let other := l0 ^^^ l1 ^^^ not_lit
    ∀ l ∈ fullArenaClauseLits st cref, l = other.toNat ∨ st.core.vals[l]?.getD 0#8 = 0xFF#8 := by
  intro other l hl
  obtain ⟨k, hk, hget⟩ := (mem_fullArenaClauseLitsCore_iff hbd).mp hl
  have h3 : 3 ≤ fullArenaClauseSize st cref := (hnw.arena.refs_wf cref hcref).2.1
  match k with
  | 0 =>
    have hl0' : (st.core.arena[cref + 3]'(by omega)) = l0 :=
      Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hl0)
    rcases hwatch with rfl | rfl
    · exact Or.inr (by rw [← hget]; simpa [hl0'] using hnot_false)
    · have hoth : other = l0 := fid_xor_cancel_r l0 l1
      exact Or.inl (by rw [← hget, hoth]; simpa using congrArg BitVec.toNat hl0')
  | 1 =>
    have hl1' : (st.core.arena[cref + 3 + 1]'(by omega)) = l1 :=
      Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hl1)
    rcases hwatch with rfl | rfl
    · have hoth : other = l1 := fid_xor_cancel_l l0 l1
      exact Or.inl (by rw [← hget, hoth]; simpa using congrArg BitVec.toNat hl1')
    · exact Or.inr (by rw [← hget]; simpa [hl1'] using hnot_false)
  | k' + 2 =>
    have hlt : l < 2 * st.core.cur_vars := hnw.arena.lits_lt cref hcref hng l hl
    have hf := hfind (k' + 2) (by omega) hk
    unfold fullFindReplBad at hf
    have hidx_lt : cref + 3 + (k' + 2) < st.core.arena.length := by
      have hk_sz : k' + 2 < fullArenaClauseSize st cref := hk
      exact Nat.lt_of_lt_of_le (by omega) hbd
    rw [List.getElem?_eq_getElem hidx_lt, Option.getD_some, hget] at hf
    exact Or.inr ((full_i8_vals_slt0 (hnw.vals_domain l hlt)).mp (hf.resolve_left (by omega)))

/-- Large-clause conflict packaging writing raw `w0` into `wstk[q]`. -/
theorem s13_large_confl_w0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st1 : FullState} {ignore_ref : BitVec 64} {not_lit w0 other cref : BitVec 32}
    {off_v p_v q_v end_v : BitVec 64}
    (hpi1 : PropLitInv c F0 F_cur s st1 not_lit.toNat off_v.toNat q_v.toNat (p_v.toNat + 2)
      end_v.toNat)
    (hnot_lt : not_lit.toNat < 2 * st1.core.cur_vars) (hq_le : q_v.toNat ≤ p_v.toNat)
    (hq1 : (q_v + 1#64).toNat = q_v.toNat + 1) (hq2 : (q_v + 2#64).toNat = q_v.toNat + 2)
    (hp2 : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2)
    (hw0_flag : (w0 &&& 0x80000000#32) = 0#32)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore st1.core)
    (hng : fullArenaClauseGarbCore st1.core cref.toNat = false)
    (hne_ign : cref.setWidth 64 ≠ ignore_ref)
    (hov_f : st1.core.vals[other.toNat]?.getD 0#8 = 0xFF#8)
    (hunit : ∀ l ∈ fullArenaClauseLitsCore st1.core cref.toNat,
      l = other.toNat ∨ st1.core.vals[l]?.getD 0#8 = 0xFF#8) :
    let st2 : FullState :=
      { st1 with core :=
        { st1.core with
          wstk := (st1.core.wstk.set q_v.toNat w0).set (q_v + 1#64).toNat cref
          confl_type := 2#64, confl_ref := cref.setWidth 64 } }
    PropLitInv c F0 F_cur s st2 not_lit.toNat off_v.toNat (q_v + 2#64).toNat
      (p_v + 1#64 + 1#64).toNat end_v.toNat ∧
    PropLitConfl F_cur ignore_ref st2.core := by
  intro st2
  have hcr64 : (cref.setWidth 64).toNat = cref.toNat := bv_c0_zext32_64 cref
  have hlen_w := hpi1.len.core_ok.wstk_len_arr
  have hp_le := hpi1.sw.p_le_end
  have ⟨hend_le, hwlen_le⟩ := hpi1.end_lt_wcap hnot_lt
  have hlen2 : st2.LengthsOk c :=
    ⟨{ hpi1.len.core_ok with wstk_len_arr := by simp [st2, hlen_w] }, hpi1.len.scratch_ok⟩
  have hsw2 := hpi1.sw.write_large hnot_lt hq_le (by rw [hlen_w]; omega)
    (by rw [hlen_w]; omega) hw0_flag hcr_lt hcr_ref
  have hws_eq : st2.core.wstk = (st1.core.wstk.set q_v.toNat w0).set (q_v.toNat + 1) cref := by
    dsimp only [st2]; rw [hq1]
  have hsw2' : SplitWatchesInv F_cur st2.core not_lit.toNat off_v.toNat (q_v.toNat + 2)
      (p_v.toNat + 2) end_v.toNat :=
    hsw2.with_nonwatch (k' := st2.core) rfl rfl hws_eq rfl rfl
  refine ⟨{ len := hlen2
            nw := fullWitnessInv_nw_congr hlen2.core_ok.cur_vars_le hpi1.nw
              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            sw := by rw [hp2, hq2]; exact hsw2'
            ag := hpi1.ag.update (fun k => { k with
              wstk := st2.core.wstk, confl_type := 2#64, confl_ref := cref.setWidth 64 })
            tr := hpi1.tr.congr rfl rfl rfl, perm := hpi1.perm
            sc_eq := hpi1.sc_eq, not_f := hpi1.not_f },
    Or.inr ⟨Or.inr ⟨rfl,
      by dsimp only [st2]; rw [hcr64]; exact hcr_ref,
      by dsimp only [st2]; rw [hcr64]; exact hng,
      fun l hl => by
        dsimp only [st2] at hl; rw [hcr64] at hl
        rcases hunit l hl with rfl | hf
        · exact hov_f
        · exact hf⟩,
      fun _ => by simpa [st2] using hne_ign⟩⟩

/-! ## 2. Shared Parameterized Inner-Loop AST Builders (`isBeyond : Bool`) -/

/-- Step-13 inline assignment tail: identical to `fidLpAssignTailExpr` except `rsn_cref = none`
adds `bigbig` binary `jumpreasons` lookup (`nr = rsns[not_lit >> 1]`). -/
@[expose] def s13LpAssignTailExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (lvl rsns trl tpos flags phases : V i64) (rec_ph bigbig : V Ty.bool)
    (not_lit : V i32) (te un uf tk_next p_next q_next di_next : V i64)
    (v_idx : V i64) (new_lit alvl : V i32) (rsn_cref : Option (V i32))
    (J_lp : L [i64, i64, i64, i64, i64, i64, i64]) : Expr V L rs :=
  Expr.group (sig := [[i64]])
    (fun J_un => Blocks.cons
      (fun unp => Expr.group (sig := [[]])
        (fun J_ph => Blocks.cons
          (fun _ =>
            Expr.let_ ⟨OpCode.mul i64, (Arg.var v_idx, Arg.imm 4, ())⟩ fun o1 =>
            Expr.let_ ⟨OpCode.add i64, (Arg.var lvl, Arg.var o1.fst, ())⟩ fun a1 =>
            Expr.store (Arg.var alvl) (Arg.var a1.fst)
              (Expr.group (sig := [[i64]])
                (fun J_uf => Blocks.cons
                  (fun ufp =>
                    Expr.let_ ⟨OpCode.mul i64, (Arg.var v_idx, Arg.imm 4, ())⟩ fun o2 =>
                    Expr.let_ ⟨OpCode.add i64, (Arg.var tpos, Arg.var o2.fst, ())⟩ fun a2 =>
                    Expr.let_ ⟨OpCode.trunc 64 32, (Arg.var te, ())⟩ fun te32 =>
                    Expr.store (Arg.var te32.fst) (Arg.var a2.fst)
                      (Expr.let_ ⟨OpCode.mul i64, (Arg.var te, Arg.imm 4, ())⟩ fun o3 =>
                      Expr.let_ ⟨OpCode.add i64, (Arg.var trl, Arg.var o3.fst, ())⟩ fun a3 =>
                      Expr.store (Arg.var new_lit) (Arg.var a3.fst)
                        (Expr.let_ ⟨OpCode.add i64, (Arg.var te, Arg.imm 1, ())⟩ fun te1 =>
                        Expr.jump J_lp (Arg.var te1.fst, Arg.var unp.fst, Arg.var ufp.fst,
                          Arg.var tk_next, Arg.var p_next, Arg.var q_next, Arg.var di_next,
                          ()))))
                  Blocks.nil)
                (fun J_uf =>
                  Expr.let_ ⟨OpCode.cmp CmpOp.eq i32, (Arg.var alvl, Arg.imm 0, ())⟩ fun z =>
                  Expr.jnz (Arg.var z.fst)
                    (Expr.let_ ⟨OpCode.mul i64, (Arg.var v_idx, Arg.imm 4, ())⟩ fun o4 =>
                    Expr.let_ ⟨OpCode.add i64, (Arg.var rsns, Arg.var o4.fst, ())⟩ fun a4 =>
                    Expr.store (Arg.imm (t := i32) 4294967295) (Arg.var a4.fst)
                      (Expr.let_ ⟨OpCode.mul i64, (Arg.var v_idx, Arg.imm 4, ())⟩ fun o5 =>
                      Expr.let_ ⟨OpCode.add i64, (Arg.var flags, Arg.var o5.fst, ())⟩ fun a5 =>
                      Expr.let_ ⟨OpCode.mul i64, (Arg.var v_idx, Arg.imm 4, ())⟩ fun o6 =>
                      Expr.let_ ⟨OpCode.add i64, (Arg.var flags, Arg.var o6.fst, ())⟩ fun a6 =>
                      Expr.load i32 (Arg.var a6.fst) fun fl =>
                      Expr.let_ ⟨OpCode.not i32, (Arg.imm 1, ())⟩ fun nm =>
                      Expr.let_ ⟨OpCode.and i32, (Arg.var fl, Arg.var nm.fst, ())⟩ fun fl' =>
                      Expr.store (Arg.var fl'.fst) (Arg.var a5.fst)
                        (Expr.let_ ⟨OpCode.add i64, (Arg.var uf, Arg.imm 1, ())⟩ fun uf1 =>
                        Expr.jump J_uf.fst (Arg.var uf1.fst, ()))))
                    (match rsn_cref with
                    | none =>
                      Expr.let_ ⟨OpCode.or i32,
                        (Arg.imm 2147483648, Arg.var not_lit, ())⟩ fun jr0 =>
                      Expr.group (sig := [[i32]])
                        (fun J_jr => Blocks.cons
                          (fun jrp =>
                            Expr.let_ ⟨OpCode.mul i64, (Arg.var v_idx, Arg.imm 4, ())⟩ fun o4 =>
                            Expr.let_ ⟨OpCode.add i64, (Arg.var rsns, Arg.var o4.fst, ())⟩ fun a4 =>
                            Expr.store (Arg.var jrp.fst) (Arg.var a4.fst)
                              (Expr.jump J_uf.fst (Arg.var uf, ())))
                          Blocks.nil)
                        (fun J_jr =>
                          Expr.jnz (Arg.var bigbig)
                            (Expr.let_ ⟨OpCode.lshr i32, (Arg.var not_lit, Arg.imm 1, ())⟩ fun nv =>
                            Expr.let_ ⟨OpCode.zext 32 64, (Arg.var nv.fst, ())⟩ fun nv64 =>
                            Expr.let_ ⟨OpCode.mul i64, (Arg.var nv64.fst, Arg.imm 4, ())⟩ fun no4 =>
                            Expr.let_ ⟨OpCode.add i64,
                              (Arg.var rsns, Arg.var no4.fst, ())⟩ fun na4 =>
                            Expr.load i32 (Arg.var na4.fst) fun nr =>
                            Expr.group (sig := [[i32]])
                              (fun Js_1 => Blocks.cons
                                (fun p => Expr.jump J_jr.fst (Arg.var p.fst, ())) Blocks.nil)
                              (fun Js =>
                                Expr.let_ ⟨OpCode.cmp CmpOp.ne i32,
                                  (Arg.var nr, Arg.imm 4294967295, ())⟩ fun cne =>
                                Expr.jnz (Arg.var cne.fst)
                                  (Expr.let_ ⟨OpCode.and i32,
                                    (Arg.var nr, Arg.imm 2147483648, ())⟩ fun nbf =>
                                  Expr.let_ ⟨OpCode.cmp CmpOp.ne i32,
                                    (Arg.var nbf.fst, Arg.imm 0, ())⟩ fun cbf =>
                                  Expr.jnz (Arg.var cbf.fst)
                                    (Expr.jump Js.fst (Arg.var nr, ()))
                                    (Expr.jump Js.fst (Arg.var jr0.fst, ())))
                                  (Expr.jump Js.fst (Arg.var jr0.fst, ()))))
                            (Expr.jump J_jr.fst (Arg.var jr0.fst, ())))
                    | some cref =>
                      Expr.let_ ⟨OpCode.mul i64, (Arg.var v_idx, Arg.imm 4, ())⟩ fun o4 =>
                      Expr.let_ ⟨OpCode.add i64, (Arg.var rsns, Arg.var o4.fst, ())⟩ fun a4 =>
                      Expr.store (Arg.var cref) (Arg.var a4.fst)
                        (Expr.jump J_uf.fst (Arg.var uf, ()))))))
          Blocks.nil)
        (fun J_ph =>
          Expr.jnz (Arg.var rec_ph)
            (Expr.group (sig := [[]])
              (fun J_p2 => Blocks.cons (fun _ => Expr.jump J_ph.fst ()) Blocks.nil)
              (fun J_p2 =>
                Expr.let_ ⟨OpCode.and i32, (Arg.var new_lit, Arg.imm 1, ())⟩ fun b1 =>
                Expr.let_ ⟨OpCode.cmp CmpOp.ne i32, (Arg.var b1.fst, Arg.imm 0, ())⟩ fun c1 =>
                Expr.jnz (Arg.var c1.fst)
                  (Expr.let_ ⟨OpCode.add i64, (Arg.var phases, Arg.var v_idx, ())⟩ fun pa =>
                  Expr.let_ ⟨OpCode.neg i32, (Arg.imm 1, ())⟩ fun m1 =>
                  Expr.let_ ⟨OpCode.trunc 32 8, (Arg.var m1.fst, ())⟩ fun b =>
                  Expr.store (Arg.var b.fst) (Arg.var pa.fst) (Expr.jump J_p2.fst ()))
                  (Expr.let_ ⟨OpCode.add i64, (Arg.var phases, Arg.var v_idx, ())⟩ fun pa =>
                  Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 1, ())⟩ fun b =>
                  Expr.store (Arg.var b.fst) (Arg.var pa.fst) (Expr.jump J_p2.fst ()))))
            (Expr.jump J_ph.fst ())))
      Blocks.nil)
    (fun J_un =>
      Expr.let_ ⟨OpCode.mul i64, (Arg.var v_idx, Arg.imm 4, ())⟩ fun o =>
      Expr.let_ ⟨OpCode.add i64, (Arg.var flags, Arg.var o.fst, ())⟩ fun a =>
      Expr.load i32 (Arg.var a.fst) fun fl =>
      Expr.let_ ⟨OpCode.and i32, (Arg.var fl, Arg.imm 1, ())⟩ fun fl1 =>
      Expr.let_ ⟨OpCode.cmp CmpOp.ne i32, (Arg.var fl1.fst, Arg.imm 0, ())⟩ fun c1 =>
      Expr.jnz (Arg.var c1.fst)
        (Expr.let_ ⟨OpCode.cmp CmpOp.ugt i64, (Arg.var un, Arg.imm 0, ())⟩ fun c2 =>
        Expr.jnz (Arg.var c2.fst)
          (Expr.let_ ⟨OpCode.sub i64, (Arg.var un, Arg.imm 1, ())⟩ fun un1 =>
          Expr.jump J_un.fst (Arg.var un1.fst, ()))
          (Expr.jump J_un.fst (Arg.var un, ())))
        (Expr.jump J_un.fst (Arg.var un, ())))

/-- Step-13 `J_ovf` block signature (`12` args when `isBeyond = true`, `13` when `false`). -/
abbrev s13OvfSig (isBeyond : Bool) : List Ty :=
  if isBeyond then
    [i64, i64, i64, i64, i64, i64, i64, Ty.bool, i32, i32, i32, i64]
  else
    [i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool, i32, i32, i32, i64]

/-- Step-13 `J_ovf` exit jump (`brk` omitted when `isBeyond = true`). -/
abbrev s13OvfJump {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (isBeyond : Bool) (J_ovf : L (s13OvfSig isBeyond))
    (te un uf tk p q di brk : Arg V i64) (ovf : Arg V Ty.bool)
    (rw oth cr : Arg V i32) (ri : Arg V i64) : Expr V L rs :=
  match isBeyond, J_ovf with
  | true, J => Expr.jump J (te, un, uf, tk, p, q, di, ovf, rw, oth, cr, ri, ())
  | false, J => Expr.jump J (te, un, uf, tk, p, q, di, brk, ovf, rw, oth, cr, ri, ())

/-- Step-13 binary watch step: on `bv < 0`, records conflict when `isBeyond = false` or
`continue`s when `isBeyond = true`. -/
@[expose] def s13LpBinStepExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (isBeyond : Bool) (hdr vals wstk lvl rsns trl tpos flags phases : V i64)
    (rec_ph bigbig : V Ty.bool) (not_lit w0 nl_lvl : V i32) (te un uf tk p q di : V i64)
    (J_ovf : L (s13OvfSig isBeyond))
    (J_lp : L [i64, i64, i64, i64, i64, i64, i64]) : Expr V L rs :=
  Expr.let_ ⟨OpCode.add i64, (Arg.var p, Arg.imm 1, ())⟩ fun p1 =>
  Expr.let_ ⟨OpCode.and i32, (Arg.var w0, Arg.imm 2147483647, ())⟩ fun blk =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var blk.fst, ())⟩ fun blk64 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var vals, Arg.var blk64.fst, ())⟩ fun vp =>
  Expr.load i8 (Arg.var vp.fst) fun vb =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var q, Arg.imm 4, ())⟩ fun qo =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var qo.fst, ())⟩ fun qp =>
  Expr.store (Arg.var w0) (Arg.var qp.fst)
    (Expr.let_ ⟨OpCode.add i64, (Arg.var q, Arg.imm 1, ())⟩ fun q1 =>
    Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun z8 =>
    Expr.let_ ⟨OpCode.sext 8 32, (Arg.var vb, ())⟩ fun s1 =>
    Expr.let_ ⟨OpCode.sext 8 32, (Arg.var z8.fst, ())⟩ fun s2 =>
    Expr.let_ ⟨OpCode.cmp CmpOp.sgt i32, (Arg.var s1.fst, Arg.var s2.fst, ())⟩ fun gt =>
    Expr.jnz (Arg.var gt.fst)
      (Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf, Arg.var tk,
        Arg.var p1.fst, Arg.var q1.fst, Arg.var di, ()))
      (Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun z8' =>
      Expr.let_ ⟨OpCode.sext 8 32, (Arg.var vb, ())⟩ fun s1' =>
      Expr.let_ ⟨OpCode.sext 8 32, (Arg.var z8'.fst, ())⟩ fun s2' =>
      Expr.let_ ⟨OpCode.cmp CmpOp.slt i32, (Arg.var s1'.fst, Arg.var s2'.fst, ())⟩ fun lt =>
      Expr.jnz (Arg.var lt.fst)
        (if isBeyond then
          Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf, Arg.var tk,
            Arg.var p1.fst, Arg.var q1.fst, Arg.var di, ())
         else
          Expr.let_ ⟨OpCode.add i64, (Arg.var hdr, Arg.imm 528, ())⟩ fun pct =>
          Expr.store (Arg.imm (t := i64) 1) (Arg.var pct.fst)
            (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var not_lit, ())⟩ fun nl64 =>
            Expr.let_ ⟨OpCode.add i64, (Arg.var hdr, Arg.imm 536, ())⟩ fun pcl0 =>
            Expr.store (Arg.var nl64.fst) (Arg.var pcl0.fst)
              (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var blk.fst, ())⟩ fun bl64 =>
              Expr.let_ ⟨OpCode.add i64, (Arg.var hdr, Arg.imm 544, ())⟩ fun pcl1 =>
              Expr.store (Arg.var bl64.fst) (Arg.var pcl1.fst)
                (s13OvfJump isBeyond J_ovf (Arg.var te) (Arg.var un) (Arg.var uf) (Arg.var tk)
                  (Arg.var p1.fst) (Arg.var q1.fst) (Arg.var di) (Arg.imm 1) (Arg.imm false)
                  (Arg.imm 0) (Arg.imm 0) (Arg.imm 0) (Arg.imm 0)))))
        (Expr.let_ ⟨OpCode.add i64, (Arg.var tk, Arg.imm 1, ())⟩ fun tk1 =>
        Expr.let_ ⟨OpCode.lshr i32, (Arg.var blk.fst, Arg.imm 1, ())⟩ fun bv =>
        Expr.let_ ⟨OpCode.zext 32 64, (Arg.var bv.fst, ())⟩ fun bv64 =>
        Expr.let_ ⟨OpCode.zext 32 64, (Arg.var blk.fst, ())⟩ fun bl64' =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var vals, Arg.var bl64'.fst, ())⟩ fun vp1 =>
        Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 1, ())⟩ fun bpos =>
        Expr.store (Arg.var bpos.fst) (Arg.var vp1.fst)
          (Expr.let_ ⟨OpCode.xor i32, (Arg.var blk.fst, Arg.imm 1, ())⟩ fun nblk =>
          Expr.let_ ⟨OpCode.zext 32 64, (Arg.var nblk.fst, ())⟩ fun nb64 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var vals, Arg.var nb64.fst, ())⟩ fun vp2 =>
          Expr.let_ ⟨OpCode.neg i32, (Arg.imm 1, ())⟩ fun m1 =>
          Expr.let_ ⟨OpCode.trunc 32 8, (Arg.var m1.fst, ())⟩ fun bneg =>
          Expr.store (Arg.var bneg.fst) (Arg.var vp2.fst)
            (s13LpAssignTailExpr lvl rsns trl tpos flags phases rec_ph bigbig not_lit
              te un uf tk1.fst p1.fst q1.fst di bv64.fst blk.fst nl_lvl none J_lp)))))

/-- Found-replacement tail parameterized over `isBeyond` (`s13OvfSig isBeyond`). -/
@[expose] def s13LpReplDelExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (isBeyond : Bool) (wstk arena del dlim : V i64) (not_lit other cref : V i32)
    (te un uf tk' p2 q di brk0 cbase ri : V i64) (repl : V i32)
    (J_ovf : L (s13OvfSig isBeyond))
    (J_lp : L [i64, i64, i64, i64, i64, i64, i64]) : Expr V L rs :=
  Expr.group (sig := [[i64, i64, Ty.bool, i32, i32, i32, i64]])
    (fun J_ret => Blocks.cons
      (fun r =>
        Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf, Arg.var tk',
          Arg.var p2, Arg.var r.fst, Arg.var r.snd.fst, ()))
      Blocks.nil)
    (fun J_ret =>
      Expr.let_ ⟨OpCode.cmp CmpOp.eq i32, (Arg.var repl, Arg.var not_lit, ())⟩ fun ce =>
      Expr.jnz (Arg.var ce.fst)
        (fidLpArSwapExpr arena not_lit other repl cbase ri
          (Expr.let_ ⟨OpCode.mul i64, (Arg.var q, Arg.imm 4, ())⟩ fun q0 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var q0.fst, ())⟩ fun qp0 =>
          Expr.store (Arg.var other) (Arg.var qp0.fst)
            (Expr.let_ ⟨OpCode.add i64, (Arg.var q, Arg.imm 1, ())⟩ fun qi1 =>
            Expr.let_ ⟨OpCode.mul i64, (Arg.var qi1.fst, Arg.imm 4, ())⟩ fun q1 =>
            Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var q1.fst, ())⟩ fun qp1 =>
            Expr.store (Arg.var cref) (Arg.var qp1.fst)
              (Expr.let_ ⟨OpCode.add i64, (Arg.var q, Arg.imm 2, ())⟩ fun q2 =>
              Expr.jump J_ret.fst (Arg.var q2.fst, Arg.var di, Arg.imm false, Arg.imm 0,
                Arg.imm 0, Arg.imm 0, Arg.imm 0, ())))))
        (Expr.let_ ⟨OpCode.cmp CmpOp.ult i64, (Arg.var di, Arg.var dlim, ())⟩ fun cd =>
        Expr.jnz (Arg.var cd.fst)
          (fidLpArSwapExpr arena not_lit other repl cbase ri
            (Expr.let_ ⟨OpCode.mul i64, (Arg.var di, Arg.imm 4, ())⟩ fun d0 =>
            Expr.let_ ⟨OpCode.add i64, (Arg.var del, Arg.var d0.fst, ())⟩ fun dp0 =>
            Expr.store (Arg.var repl) (Arg.var dp0.fst)
              (Expr.let_ ⟨OpCode.add i64, (Arg.var di, Arg.imm 1, ())⟩ fun di1 =>
              Expr.let_ ⟨OpCode.mul i64, (Arg.var di1.fst, Arg.imm 4, ())⟩ fun d1 =>
              Expr.let_ ⟨OpCode.add i64, (Arg.var del, Arg.var d1.fst, ())⟩ fun dp1 =>
              Expr.store (Arg.var other) (Arg.var dp1.fst)
                (Expr.let_ ⟨OpCode.add i64, (Arg.var di, Arg.imm 2, ())⟩ fun di2 =>
                Expr.let_ ⟨OpCode.mul i64, (Arg.var di2.fst, Arg.imm 4, ())⟩ fun d2 =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var del, Arg.var d2.fst, ())⟩ fun dp2 =>
                Expr.store (Arg.var cref) (Arg.var dp2.fst)
                  (Expr.let_ ⟨OpCode.add i64, (Arg.var di, Arg.imm 3, ())⟩ fun di3 =>
                  Expr.jump J_ret.fst (Arg.var q, Arg.var di3.fst, Arg.imm false, Arg.imm 0,
                    Arg.imm 0, Arg.imm 0, Arg.imm 0, ()))))))
          (s13OvfJump isBeyond J_ovf (Arg.var te) (Arg.var un) (Arg.var uf) (Arg.var tk')
            (Arg.var p2) (Arg.var q) (Arg.var di) (Arg.var brk0) (Arg.imm true) (Arg.var repl)
            (Arg.var other) (Arg.var cref) (Arg.var ri))))

/-- Step-13 no-replacement tail: stores `w0`, checks `cref == ignore_ref`, skips conflict when
`isBeyond = true`, else assigns unit. -/
@[expose] def s13LpNoReplExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (isBeyond : Bool) (hdr vals wstk arena lvl rsns trl tpos flags phases : V i64)
    (ignore_ref : Arg V i64) (cur_lvl32 not_lit nl_lvl w0 other cref : V i32) (ov : V i8)
    (rec_ph bigbig : V Ty.bool) (te un uf tk1 p2 q di cbase csz : V i64)
    (J_ovf : L (s13OvfSig isBeyond))
    (J_lp : L [i64, i64, i64, i64, i64, i64, i64]) : Expr V L rs :=
  Expr.let_ ⟨OpCode.mul i64, (Arg.var q, Arg.imm 4, ())⟩ fun q0 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var q0.fst, ())⟩ fun qp0 =>
  Expr.store (Arg.var w0) (Arg.var qp0.fst)
    (Expr.let_ ⟨OpCode.add i64, (Arg.var q, Arg.imm 1, ())⟩ fun qi1 =>
    Expr.let_ ⟨OpCode.mul i64, (Arg.var qi1.fst, Arg.imm 4, ())⟩ fun q1 =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var q1.fst, ())⟩ fun qp1 =>
    Expr.store (Arg.var cref) (Arg.var qp1.fst)
      (Expr.let_ ⟨OpCode.add i64, (Arg.var q, Arg.imm 2, ())⟩ fun q2 =>
      Expr.let_ ⟨OpCode.zext 32 64, (Arg.var cref, ())⟩ fun cr64d =>
      Expr.let_ ⟨OpCode.cmp CmpOp.eq i64, (Arg.var cr64d.fst, ignore_ref, ())⟩ fun eqig =>
      Expr.jnz (Arg.var eqig.fst)
        (Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf, Arg.var tk1, Arg.var p2,
          Arg.var q2.fst, Arg.var di, ()))
        (Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun z8' =>
        Expr.let_ ⟨OpCode.sext 8 32, (Arg.var ov, ())⟩ fun s1' =>
        Expr.let_ ⟨OpCode.sext 8 32, (Arg.var z8'.fst, ())⟩ fun s2' =>
        Expr.let_ ⟨OpCode.cmp CmpOp.slt i32, (Arg.var s1'.fst, Arg.var s2'.fst, ())⟩ fun lt =>
        Expr.jnz (Arg.var lt.fst)
          (if isBeyond then
            Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf, Arg.var tk1, Arg.var p2,
              Arg.var q2.fst, Arg.var di, ())
           else
            Expr.let_ ⟨OpCode.add i64, (Arg.var hdr, Arg.imm 528, ())⟩ fun pct =>
            Expr.store (Arg.imm (t := i64) 2) (Arg.var pct.fst)
              (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var cref, ())⟩ fun cr64e =>
              Expr.let_ ⟨OpCode.add i64, (Arg.var hdr, Arg.imm 176, ())⟩ fun pcr =>
              Expr.store (Arg.var cr64e.fst) (Arg.var pcr.fst)
                (s13OvfJump isBeyond J_ovf (Arg.var te) (Arg.var un) (Arg.var uf) (Arg.var tk1)
                  (Arg.var p2) (Arg.var q2.fst) (Arg.var di) (Arg.imm 1) (Arg.imm false)
                  (Arg.imm 0) (Arg.imm 0) (Arg.imm 0) (Arg.imm 0))))
          (Expr.let_ ⟨OpCode.add i64, (Arg.var tk1, Arg.imm 1, ())⟩ fun tk2 =>
          Expr.group (sig := [[i32]])
            (fun J_alvl => Blocks.cons
              (fun alvlp =>
                Expr.let_ ⟨OpCode.lshr i32, (Arg.var other, Arg.imm 1, ())⟩ fun ovv =>
                Expr.let_ ⟨OpCode.zext 32 64, (Arg.var ovv.fst, ())⟩ fun ov64 =>
                Expr.let_ ⟨OpCode.zext 32 64, (Arg.var other, ())⟩ fun ot64 =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var vals, Arg.var ot64.fst, ())⟩ fun vp1 =>
                Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 1, ())⟩ fun bpos =>
                Expr.store (Arg.var bpos.fst) (Arg.var vp1.fst)
                  (Expr.let_ ⟨OpCode.xor i32, (Arg.var other, Arg.imm 1, ())⟩ fun noth =>
                  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var noth.fst, ())⟩ fun no64 =>
                  Expr.let_ ⟨OpCode.add i64, (Arg.var vals, Arg.var no64.fst, ())⟩ fun vp2 =>
                  Expr.let_ ⟨OpCode.neg i32, (Arg.imm 1, ())⟩ fun m1 =>
                  Expr.let_ ⟨OpCode.trunc 32 8, (Arg.var m1.fst, ())⟩ fun bneg =>
                  Expr.store (Arg.var bneg.fst) (Arg.var vp2.fst)
                    (s13LpAssignTailExpr lvl rsns trl tpos flags phases rec_ph bigbig not_lit te un
                      uf tk2.fst p2 q2.fst di ov64.fst other alvlp.fst (some cref) J_lp)))
              Blocks.nil)
            (fun J_alvl =>
              Expr.let_ ⟨OpCode.cmp CmpOp.ult i32, (Arg.var nl_lvl, Arg.var cur_lvl32, ())⟩
                fun lt =>
              Expr.jnz (Arg.var lt.fst)
                (m7LpMaxLvlExpr arena lvl cbase csz other J_alvl.fst)
                (Expr.jump J_alvl.fst (Arg.var nl_lvl, ())))))))

/-- Step-13 search-start normalization + replacement scan + dispatch. -/
@[expose] def s13LpScanExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (isBeyond : Bool) (hdr vals wstk arena lvl rsns trl tpos flags phases del dlim : V i64)
    (ignore_ref : Arg V i64) (cur_lvl32 not_lit nl_lvl w0 other cref : V i32) (ov : V i8)
    (rec_ph bigbig : V Ty.bool) (te un uf tk1 p2 q di brk0 cbase csz pos : V i64)
    (J_ovf : L (s13OvfSig isBeyond))
    (J_lp : L [i64, i64, i64, i64, i64, i64, i64]) : Expr V L rs :=
  Expr.group (sig := [[i64]])
    (fun J_st => Blocks.cons
      (fun st =>
        Expr.group (sig := [[i64, i32, Ty.bool]])
          (fun J_r1 => Blocks.cons
            (fun s1p =>
              Expr.group (sig := [[i64, i32, Ty.bool]])
                (fun J_r2 => Blocks.cons
                  (fun s2p =>
                    Expr.jnz (Arg.var s2p.snd.snd.fst)
                      (Expr.let_ ⟨OpCode.add i64, (Arg.var tk1, Arg.imm 1, ())⟩ fun tk2 =>
                      Expr.let_ ⟨OpCode.zext 32 64, (Arg.var cref, ())⟩ fun cr64c =>
                      Expr.let_ ⟨OpCode.add i64, (Arg.var cr64c.fst, Arg.imm 1, ())⟩ fun psi2 =>
                      Expr.let_ ⟨OpCode.mul i64, (Arg.var psi2.fst, Arg.imm 4, ())⟩ fun pso2 =>
                      Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var pso2.fst, ())⟩
                        fun psp2 =>
                      Expr.let_ ⟨OpCode.trunc 64 32, (Arg.var s2p.fst, ())⟩ fun ri32 =>
                      Expr.store (Arg.var ri32.fst) (Arg.var psp2.fst)
                        (s13LpReplDelExpr isBeyond wstk arena del dlim not_lit other cref te un uf
                          tk2.fst p2 q di brk0 cbase s2p.fst s2p.snd.fst J_ovf J_lp))
                      (s13LpNoReplExpr isBeyond hdr vals wstk arena lvl rsns trl tpos flags phases
                        ignore_ref cur_lvl32 not_lit nl_lvl w0 other cref ov rec_ph bigbig te un uf
                        tk1 p2 q di cbase csz J_ovf J_lp))
                  Blocks.nil)
                (fun J_r2 =>
                  Expr.jnz (Arg.var s1p.snd.snd.fst)
                    (Expr.jump J_r2.fst (Arg.var s1p.fst, Arg.var s1p.snd.fst,
                      Arg.var s1p.snd.snd.fst, ()))
                    (Expr.group (sig := [[i64, i32, Ty.bool]])
                      (fun J_w => Blocks.cons
                        (fun wp => Expr.jump J_r2.fst (Arg.var wp.fst, Arg.var wp.snd.fst,
                          Arg.var wp.snd.snd.fst, ()))
                        Blocks.nil)
                      (fun J_w => m7LpReplScanExpr vals arena cbase st.fst (Arg.imm 2)
                        (Arg.var s1p.snd.fst) (Arg.var s1p.snd.snd.fst) J_w.fst))))
            Blocks.nil)
          (fun J_r1 =>
            m7LpReplScanExpr vals arena cbase csz (Arg.var st.fst) (Arg.imm 0) (Arg.imm false)
              J_r1.fst))
      Blocks.nil)
    (fun J_st =>
      Expr.let_ ⟨OpCode.cmp CmpOp.ult i64, (Arg.var pos, Arg.imm 2, ())⟩ fun lt2 =>
      Expr.jnz (Arg.var lt2.fst)
        (Expr.jump J_st.fst (Arg.imm 2, ()))
        (Expr.let_ ⟨OpCode.cmp CmpOp.uge i64, (Arg.var pos, Arg.var csz, ())⟩ fun gec =>
        Expr.jnz (Arg.var gec.fst)
          (Expr.jump J_st.fst (Arg.imm 2, ()))
          (Expr.jump J_st.fst (Arg.var pos, ()))))

/-- Step-13 large-clause watch step: no eager `l0 == not_lit` swap before `ov > 0` / repl scan. -/
@[expose] def s13LpLargeStepExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (isBeyond : Bool) (hdr vals wstk arena lvl rsns trl tpos flags phases del dlim : V i64)
    (ignore_ref : Arg V i64) (two_cv : V i64) (cur_lvl32 not_lit w0 nl_lvl : V i32)
    (rec_ph bigbig : V Ty.bool) (te un uf tk p q di brk0 : V i64)
    (J_ovf : L (s13OvfSig isBeyond))
    (J_lp : L [i64, i64, i64, i64, i64, i64, i64]) : Expr V L rs :=
  Expr.group (sig := [[]])
    (fun J_c => Blocks.cons
      (fun _ =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var p, Arg.imm 1, ())⟩ fun p1 =>
        Expr.let_ ⟨OpCode.mul i64, (Arg.var p1.fst, Arg.imm 4, ())⟩ fun po1 =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var po1.fst, ())⟩ fun pp1 =>
        Expr.load i32 (Arg.var pp1.fst) fun cref =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var p, Arg.imm 2, ())⟩ fun p2 =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var tk, Arg.imm 1, ())⟩ fun tk1 =>
        Expr.let_ ⟨OpCode.zext 32 64, (Arg.var cref, ())⟩ fun cr64 =>
        Expr.let_ ⟨OpCode.mul i64, (Arg.var cr64.fst, Arg.imm 4, ())⟩ fun fo =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var fo.fst, ())⟩ fun fp =>
        Expr.load i32 (Arg.var fp.fst) fun fl =>
        Expr.let_ ⟨OpCode.and i32, (Arg.var fl, Arg.imm 524288, ())⟩ fun flg =>
        Expr.let_ ⟨OpCode.cmp CmpOp.ne i32, (Arg.var flg.fst, Arg.imm 0, ())⟩ fun gar =>
        Expr.jnz (Arg.var gar.fst)
          (Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf, Arg.var tk1.fst,
            Arg.var p2.fst, Arg.var q, Arg.var di, ()))
          (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var cref, ())⟩ fun cr64' =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var cr64'.fst, Arg.imm 3, ())⟩ fun cbase =>
          Expr.let_ ⟨OpCode.mul i64, (Arg.var cbase.fst, Arg.imm 4, ())⟩ fun o0 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var o0.fst, ())⟩ fun a0 =>
          Expr.load i32 (Arg.var a0.fst) fun l0 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var cbase.fst, Arg.imm 1, ())⟩ fun i1 =>
          Expr.let_ ⟨OpCode.mul i64, (Arg.var i1.fst, Arg.imm 4, ())⟩ fun o1 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var o1.fst, ())⟩ fun a1 =>
          Expr.load i32 (Arg.var a1.fst) fun l1 =>
          Expr.group (sig := [[]])
            (fun J_chk => Blocks.cons
              (fun _ =>
                Expr.let_ ⟨OpCode.xor i32, (Arg.var l0, Arg.var l1, ())⟩ fun x1 =>
                Expr.let_ ⟨OpCode.xor i32, (Arg.var x1.fst, Arg.var not_lit, ())⟩ fun other =>
                Expr.let_ ⟨OpCode.zext 32 64, (Arg.var other.fst, ())⟩ fun o64 =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var vals, Arg.var o64.fst, ())⟩ fun vp =>
                Expr.load i8 (Arg.var vp.fst) fun ov =>
                Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun z8 =>
                Expr.let_ ⟨OpCode.sext 8 32, (Arg.var ov, ())⟩ fun s1 =>
                Expr.let_ ⟨OpCode.sext 8 32, (Arg.var z8.fst, ())⟩ fun s2 =>
                Expr.let_ ⟨OpCode.cmp CmpOp.sgt i32, (Arg.var s1.fst, Arg.var s2.fst, ())⟩ fun gt =>
                Expr.jnz (Arg.var gt.fst)
                  (Expr.let_ ⟨OpCode.mul i64, (Arg.var q, Arg.imm 4, ())⟩ fun q0 =>
                  Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var q0.fst, ())⟩ fun qp0 =>
                  Expr.store (Arg.var other.fst) (Arg.var qp0.fst)
                    (Expr.let_ ⟨OpCode.add i64, (Arg.var q, Arg.imm 1, ())⟩ fun qi1 =>
                    Expr.let_ ⟨OpCode.mul i64, (Arg.var qi1.fst, Arg.imm 4, ())⟩ fun q1 =>
                    Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var q1.fst, ())⟩ fun qp1 =>
                    Expr.store (Arg.var cref) (Arg.var qp1.fst)
                      (Expr.let_ ⟨OpCode.add i64, (Arg.var q, Arg.imm 2, ())⟩ fun q2 =>
                      Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf,
                        Arg.var tk1.fst, Arg.var p2.fst, Arg.var q2.fst, Arg.var di, ()))))
                  (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var cref, ())⟩ fun cr64a =>
                  Expr.let_ ⟨OpCode.add i64, (Arg.var cr64a.fst, Arg.imm 2, ())⟩ fun szi =>
                  Expr.let_ ⟨OpCode.mul i64, (Arg.var szi.fst, Arg.imm 4, ())⟩ fun szo =>
                  Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var szo.fst, ())⟩ fun szp =>
                  Expr.load i32 (Arg.var szp.fst) fun csz32 =>
                  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var csz32, ())⟩ fun csz =>
                  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var cref, ())⟩ fun cr64b =>
                  Expr.let_ ⟨OpCode.add i64, (Arg.var cr64b.fst, Arg.imm 1, ())⟩ fun psi =>
                  Expr.let_ ⟨OpCode.mul i64, (Arg.var psi.fst, Arg.imm 4, ())⟩ fun pso =>
                  Expr.let_ ⟨OpCode.add i64, (Arg.var arena, Arg.var pso.fst, ())⟩ fun psp =>
                  Expr.load i32 (Arg.var psp.fst) fun pos32 =>
                  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var pos32, ())⟩ fun pos =>
                  s13LpScanExpr isBeyond hdr vals wstk arena lvl rsns trl tpos flags phases del
                    dlim ignore_ref cur_lvl32 not_lit nl_lvl w0 other.fst cref ov rec_ph bigbig te
                    un uf tk1.fst p2.fst q di brk0 cbase.fst csz.fst pos.fst J_ovf J_lp))
              Blocks.nil)
            (fun J_chk =>
              Expr.let_ ⟨OpCode.cmp CmpOp.ne i32, (Arg.var l0, Arg.var not_lit, ())⟩ fun ne0 =>
              Expr.jnz (Arg.var ne0.fst)
                (Expr.let_ ⟨OpCode.cmp CmpOp.ne i32, (Arg.var l1, Arg.var not_lit, ())⟩ fun ne1 =>
                Expr.jnz (Arg.var ne1.fst)
                  (Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf, Arg.var tk1.fst,
                    Arg.var p2.fst, Arg.var q, Arg.var di, ()))
                  (Expr.jump J_chk.fst ()))
                (Expr.jump J_chk.fst ()))))
      Blocks.nil)
    (fun J_c =>
      Expr.let_ ⟨OpCode.zext 32 64, (Arg.var w0, ())⟩ fun w64 =>
      Expr.let_ ⟨OpCode.cmp CmpOp.ult i64, (Arg.var w64.fst, Arg.var two_cv, ())⟩ fun ltv =>
      Expr.jnz (Arg.var ltv.fst)
        (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var w0, ())⟩ fun w64' =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var vals, Arg.var w64'.fst, ())⟩ fun vp =>
        Expr.load i8 (Arg.var vp.fst) fun vw =>
        Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun z8 =>
        Expr.let_ ⟨OpCode.sext 8 32, (Arg.var vw, ())⟩ fun s1 =>
        Expr.let_ ⟨OpCode.sext 8 32, (Arg.var z8.fst, ())⟩ fun s2 =>
        Expr.let_ ⟨OpCode.cmp CmpOp.sgt i32, (Arg.var s1.fst, Arg.var s2.fst, ())⟩ fun gt =>
        Expr.jnz (Arg.var gt.fst)
          (Expr.let_ ⟨OpCode.add i64, (Arg.var p, Arg.imm 1, ())⟩ fun p1 =>
          Expr.let_ ⟨OpCode.mul i64, (Arg.var p1.fst, Arg.imm 4, ())⟩ fun po1 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var po1.fst, ())⟩ fun pp1 =>
          Expr.load i32 (Arg.var pp1.fst) fun cref =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var p, Arg.imm 2, ())⟩ fun p2 =>
          Expr.let_ ⟨OpCode.mul i64, (Arg.var q, Arg.imm 4, ())⟩ fun qo0 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var qo0.fst, ())⟩ fun qp0 =>
          Expr.store (Arg.var w0) (Arg.var qp0.fst)
            (Expr.let_ ⟨OpCode.add i64, (Arg.var q, Arg.imm 1, ())⟩ fun qi1 =>
            Expr.let_ ⟨OpCode.mul i64, (Arg.var qi1.fst, Arg.imm 4, ())⟩ fun qo1 =>
            Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var qo1.fst, ())⟩ fun qp1 =>
            Expr.store (Arg.var cref) (Arg.var qp1.fst)
              (Expr.let_ ⟨OpCode.add i64, (Arg.var q, Arg.imm 2, ())⟩ fun q2 =>
              Expr.jump J_lp (Arg.var te, Arg.var un, Arg.var uf, Arg.var tk,
                Arg.var p2.fst, Arg.var q2.fst, Arg.var di, ()))))
          (Expr.jump J_c.fst ()))
        (Expr.jump J_c.fst ()))

/-- Step-13 inner `while (p < end)` watch loop (state `(te, un, uf, tk, p, q, di)`). -/
@[expose] def s13LpLoopExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (isBeyond : Bool) (hdr vals wstk arena lvl rsns trl tpos flags phases del dlim : V i64)
    (ignore_ref : Arg V i64) (two_cv : V i64) (cur_lvl32 not_lit nl_lvl : V i32)
    (rec_ph bigbig : V Ty.bool) (end0 brk0 te0 un0 uf0 tk0 p0 q0 di0 : V i64)
    (J_ovf : L (s13OvfSig isBeyond)) :
    Expr V L rs :=
  Expr.group (sig := [[i64, i64, i64, i64, i64, i64, i64]])
    (fun J_lp => Blocks.cons
      (fun lp =>
        Expr.let_ ⟨OpCode.cmp CmpOp.ult i64, (Arg.var lp.snd.snd.snd.snd.fst, Arg.var end0, ())⟩
          fun c =>
        Expr.jnz (Arg.var c.fst)
          (Expr.let_ ⟨OpCode.mul i64, (Arg.var lp.snd.snd.snd.snd.fst, Arg.imm 4, ())⟩ fun po =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var wstk, Arg.var po.fst, ())⟩ fun pp =>
          Expr.load i32 (Arg.var pp.fst) fun w0 =>
          Expr.let_ ⟨OpCode.and i32, (Arg.var w0, Arg.imm 2147483648, ())⟩ fun bin =>
          Expr.let_ ⟨OpCode.cmp CmpOp.ne i32, (Arg.var bin.fst, Arg.imm 0, ())⟩ fun isbin =>
          Expr.jnz (Arg.var isbin.fst)
            (s13LpBinStepExpr isBeyond hdr vals wstk lvl rsns trl tpos flags phases rec_ph bigbig
              not_lit w0 nl_lvl lp.fst lp.snd.fst lp.snd.snd.fst lp.snd.snd.snd.fst
              lp.snd.snd.snd.snd.fst lp.snd.snd.snd.snd.snd.fst lp.snd.snd.snd.snd.snd.snd.fst
              J_ovf J_lp.fst)
            (s13LpLargeStepExpr isBeyond hdr vals wstk arena lvl rsns trl tpos
              flags phases del dlim ignore_ref two_cv cur_lvl32 not_lit w0 nl_lvl rec_ph bigbig
              lp.fst lp.snd.fst lp.snd.snd.fst lp.snd.snd.snd.fst lp.snd.snd.snd.snd.fst
              lp.snd.snd.snd.snd.snd.fst lp.snd.snd.snd.snd.snd.snd.fst brk0 J_ovf J_lp.fst))
          (s13OvfJump isBeyond J_ovf (Arg.var lp.fst) (Arg.var lp.snd.fst)
            (Arg.var lp.snd.snd.fst) (Arg.var lp.snd.snd.snd.fst)
            (Arg.var lp.snd.snd.snd.snd.fst) (Arg.var lp.snd.snd.snd.snd.snd.fst)
            (Arg.var lp.snd.snd.snd.snd.snd.snd.fst)
            (Arg.var brk0) (Arg.imm false) (Arg.imm 0) (Arg.imm 0) (Arg.imm 0) (Arg.imm 0)))
      Blocks.nil)
    (fun J_lp =>
      Expr.jump J_lp.fst (Arg.var te0, Arg.var un0, Arg.var uf0, Arg.var tk0,
        Arg.var p0, Arg.var q0, Arg.var di0, ()))

/-! ## 3. Inline Assignment Tail, Binary Step, \& Delayed-Push WP (`<= 250` lines each) -/

theorem s13_lp_assign_tail_wp {Γ : Env} {rs : List Ty} {c : FullCfg}
    {s_disk sem : FullState} {vals' : List (BitVec 8)} {not_lit new_lit alvl : BitVec 32}
    {rec_ph bigbig : Bool} {te un uf tk_next p_next q_next di_next v_idx : BitVec 64}
    {rsn_cref : Option (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    {J_lp : Cont [i64, i64, i64, i64, i64, i64, i64]}
    (hmaxv : c.max_vars < 2 * dimacsBound) (hlen_sem : sem.LengthsOk c)
    (_hvals' : vals'.length = 2 * c.max_vars)
    (hte_lt : sem.core.trail_end < sem.core.cur_vars) (hte_eq : te.toNat = sem.core.trail_end)
    (hnew_lt : new_lit.toNat < 2 * sem.core.cur_vars)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (hvidx : v_idx.toNat = new_lit.toNat / 2)
    (hm : (FullMem c { fastPropMem s_disk sem with
        core := { (fastPropMem s_disk sem).core with vals := vals' } } ⋆ R) m)
    (hJ : ∀ (flags' : List (BitVec 32)) (ph' : List (BitVec 8))
        (un_n uf_n : BitVec 64) (jr : BitVec 32) (m' : Mem 64),
      flags'.length = c.max_vars → ph'.length = c.max_vars →
      (rsn_cref = none → jr = ((not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32) ∨
        (alvl ≠ 0#32 ∧ bigbig = true ∧
          let nr := sem.core.rsns[not_lit.toNat / 2]?.getD 0xFFFFFFFF#32
          nr ≠ 0xFFFFFFFF#32 ∧ (nr &&& 0x80000000#32) ≠ 0#32 ∧ jr = nr)) →
      let rsn_val := rsn_cref.getD jr
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
        (.var tk_next, (.var p_next, (.var q_next, (.var di_next, ())))))))) m') :
    wp Γ Q X (s13LpAssignTailExpr c.pLevel c.pReason c.pTrail c.pTrailPos c.pFlags c.pPhases
      rec_ph bigbig not_lit te un uf tk_next p_next q_next di_next v_idx new_lit alvl rsn_cref
      J_lp) m := by
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
  unfold s13LpAssignTailExpr
  refine wp_join_group (fun (un_n, ()) mu => mu = m) ?_ ?_
  · rintro _ ⟨un_n, ⟨⟩⟩ mu hmu
    dsimp only at hmu; rw [hmu]; clear hmu
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
      s13_hsteps_nogrp
      have hml : (FullMem c (fastPropMem s_disk { sem with
          core :=
            { sem.core with
              vals := vals', lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl }
          scratch := { sem.scratch with phases := ph' } }) ⋆ R) m := by
        simpa only [fastPropMem_lvl, hvidx, m7_fastPropMem_with_lvl] using hm
      clear hm
      have hrsn_bin : 2147483648#32 ||| not_lit =
          (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32 := by
        rw [m7_bv32_mask7f_eq h2cv_31, BitVec.or_comm]
      refine wp_join_group (fun (uf_n, ()) maf =>
          ∃ (flags' : List (BitVec 32)) (jr : BitVec 32), flags'.length = c.max_vars ∧
          (rsn_cref = none → jr = ((not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32) ∨
            (alvl ≠ 0#32 ∧ bigbig = true ∧
              let nr := sem.core.rsns[not_lit.toNat / 2]?.getD 0xFFFFFFFF#32
              nr ≠ 0xFFFFFFFF#32 ∧ (nr &&& 0x80000000#32) ≠ 0#32 ∧ jr = nr)) ∧
          (FullMem c (fastPropMem s_disk { sem with
            core :=
              { sem.core with
                vals := vals', flags := flags'
                lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl
                rsns := sem.core.rsns.set (new_lit.toNat / 2)
                  (if alvl = 0#32 then 0xFFFFFFFF#32 else rsn_cref.getD jr) }
            scratch := { sem.scratch with phases := ph' } }) ⋆ R) maf) ?_ ?_
      · rintro _ ⟨uf_n, ⟨⟩⟩ maf ⟨flags', jr, hfl', hjr_ok, hmaf⟩
        have htp_m : (fastPropMem s_disk { sem with
            core :=
              { sem.core with
                vals := vals', flags := flags'
                lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl
                rsns := sem.core.rsns.set (new_lit.toNat / 2)
                  (if alvl = 0#32 then 0xFFFFFFFF#32 else rsn_cref.getD jr) }
            scratch := { sem.scratch with phases := ph' } }).core.trail_pos.length =
            c.max_vars := by
          rw [fastPropMem_trail_pos]; exact htp_len
        have htrl_m : (fastPropMem s_disk { sem with
            core :=
              { sem.core with
                vals := vals', flags := flags'
                lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl
                rsns := sem.core.rsns.set (new_lit.toNat / 2)
                  (if alvl = 0#32 then 0xFFFFFFFF#32 else rsn_cref.getD jr)
                trail_pos := sem.core.trail_pos.set (new_lit.toNat / 2)
                  (BitVec.ofNat 32 sem.core.trail_end) }
            scratch := { sem.scratch with phases := ph' } }).core.trl.length =
            c.max_vars := by
          rw [fastPropMem_trl]; exact htrl_len
        s13_hsteps
        refine wp_store_sep (FullArenaTactics.c0_store_full_trl new_lit
          (by rw [fastPropMem_trl, hte_eq, htrl_len]; exact hte_mv) hm) ?_
        intro mtr hmtr'; clear hm
        s13_hsteps
        have hmtr :
            (FullMem c (fastPropMem s_disk {
              core :=
                { sem.core with
                  vals := vals', flags := flags'
                  lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl
                  rsns := sem.core.rsns.set (new_lit.toNat / 2)
                    (if alvl = 0#32 then 0xFFFFFFFF#32 else rsn_cref.getD jr)
                  trl := sem.core.trl.set sem.core.trail_end new_lit
                  trail_pos := sem.core.trail_pos.set (new_lit.toNat / 2)
                    (BitVec.ofNat 32 sem.core.trail_end)
                  trail_end := sem.core.trail_end + 1
                  unassigned := un_n, unflushed := uf_n }
              scratch := { sem.scratch with phases := ph' } }) ⋆ R) mtr := by
          refine Eq.mp (congrArg (fun k => (FullMem c k ⋆ R) mtr) ?_) hmtr'
          unfold fastPropMem; dsimp only; simp only [hvidx, htpos32, hte_eq]
        exact hJ flags' ph' un_n uf_n jr mtr hfl' hph' hjr_ok hmtr
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
        s13_hsplit
        · have hal0 : alvl = 0#32 := hc
          s13_hsteps_nogrp
          simp only [fastPropMem_rsns, m7_fastPropMem_with_rsns] at hm
          s13_hsteps
          have hf_lt_m : new_lit.toNat / 2 < sem.core.flags.length := by rw [hfl_len]; exact hv_mv
          have hf_idx_eq : (fastPropMem s_disk { sem with
              core :=
                { sem.core with
                  vals := vals', lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl
                  rsns := sem.core.rsns.set v_idx.toNat 0xFFFFFFFF#32 }
              scratch := { sem.scratch with phases := ph' } }).core.flags[v_idx.toNat]'(by
                rw [hfl_m']; exact hvidx ▸ hv_mv) =
              sem.core.flags[new_lit.toNat / 2]'hf_lt_m :=
            Option.some.inj (by
              rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem,
                fastPropMem_flags, hvidx])
          let fv_al0 := sem.core.flags[new_lit.toNat / 2]'hf_lt_m &&& ~~~1#32
          refine hJunfl (uf + 1#64, ()) m
            ⟨sem.core.flags.set (new_lit.toNat / 2) fv_al0,
              ((not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32),
              by rw [List.length_set, hfl_len], (fun _ => Or.inl rfl), ?_⟩
          simp only [hal0, ↓reduceIte, hvidx, fastPropMem_flags,
            m7_fastPropMem_with_flags] at hm ⊢
          exact hm
        · have hal_ne0 : alvl ≠ 0#32 := hc
          cases rsn_cref with
          | none =>
            have hnot_r1 : (not_lit >>> 1#32).toNat = not_lit.toNat / 2 := bv32_lshr_1 not_lit
            have hnot_r64 : ((not_lit >>> 1#32).setWidth 64).toNat = not_lit.toNat / 2 := by
              rw [bv_c0_zext32_64, hnot_r1]
            have hnot_rsn : ((not_lit >>> 1#32).setWidth 64).toNat <
                (fastPropMem s_disk { sem with
                  core :=
                    { sem.core with
                      vals := vals', lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl }
                  scratch := { sem.scratch with phases := ph' } }).core.rsns.length := by
              rw [fastPropMem_rsns, hrsn_len, hnot_r64]
              omega
            refine wp_join_group (ts := [i32]) (fun (jrp, ()) mjr => mjr = m ∧
                (jrp = ((not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32) ∨
                  (alvl ≠ 0#32 ∧ bigbig = true ∧
                    let nr := sem.core.rsns[not_lit.toNat / 2]?.getD 0xFFFFFFFF#32
                    nr ≠ 0xFFFFFFFF#32 ∧ (nr &&& 0x80000000#32) ≠ 0#32 ∧ jrp = nr)))
              (fun _ ⟨jrp, ⟨⟩⟩ mjr ⟨hmjr, hjrp⟩ => by
                subst mjr; s13_hsteps
                exact hJunfl (uf, ()) m ⟨sem.core.flags, jrp, hfl_len, (fun _ => hjrp), by
                  simpa only [hal_ne0, ↓reduceIte, Option.getD_none, fastPropMem_rsns, hvidx,
                    m7_fastPropMem_with_rsns] using hm⟩)
              (fun J_jr hJ_jr => by
                have hrsn_bin' : BitVec.ofNat 32 2147483648 ||| not_lit =
                    (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32 := hrsn_bin
                c0_hstraight
                refine wp_jnz_of (fun hbig => ?_) (fun hnbig => ?_)
                · have hbig' : bigbig = true := by simpa only [Arg.val_var] using hbig
                  c0_hstraight
                  have hnr_eq : (fastPropMem s_disk { sem with
                      core :=
                        { sem.core with
                          vals := vals', lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl }
                      scratch := { sem.scratch with phases := ph' } }).core.rsns[
                      ((not_lit >>> 1#32).setWidth 64).toNat]'hnot_rsn =
                      sem.core.rsns[not_lit.toNat / 2]?.getD 0xFFFFFFFF#32 := by
                    rw [List.getElem?_eq_getElem (by rw [hrsn_len]; omega), Option.getD_some]
                    simp only [fastPropMem_rsns]
                    exact fc_getElem_eq_of_idx hnot_r64 _ _
                  refine wp_join_group (ts := [i32]) (fun (jrp, ()) mjr => mjr = m ∧
                      (jrp = ((not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32) ∨
                        (alvl ≠ 0#32 ∧ bigbig = true ∧
                          let nr := sem.core.rsns[not_lit.toNat / 2]?.getD 0xFFFFFFFF#32
                          nr ≠ 0xFFFFFFFF#32 ∧ (nr &&& 0x80000000#32) ≠ 0#32 ∧ jrp = nr)))
                    (fun _ ⟨jrp, ⟨⟩⟩ mjr ⟨hmjr, hjrp⟩ => by
                      subst mjr; s13_hsteps; exact hJ_jr _ m ⟨rfl, hjrp⟩)
                    (fun Js hJs => by
                      c0_hstraight
                      refine wp_jnz_of (fun hcne_raw => ?_) (fun _ => by
                        s13_hsteps; exact hJs _ m ⟨rfl, Or.inl hrsn_bin'⟩)
                      have hcne : sem.core.rsns[not_lit.toNat / 2]?.getD 0xFFFFFFFF#32 ≠
                          0xFFFFFFFF#32 := by
                        have h1 := bne_iff_ne.mp hcne_raw
                        dsimp only [Arg.val_var] at h1
                        rwa [← hnr_eq]
                      c0_hstraight
                      refine wp_jnz_of (fun hcb_raw => ?_) (fun _ => by
                        s13_hsteps; exact hJs _ m ⟨rfl, Or.inl hrsn_bin'⟩)
                      have hcb : (sem.core.rsns[not_lit.toNat / 2]?.getD 0xFFFFFFFF#32 &&&
                            0x80000000#32) ≠ 0#32 := by
                        have h1 := bne_iff_ne.mp hcb_raw
                        dsimp only [Arg.val_var] at h1
                        rwa [← hnr_eq]
                      s13_hsteps
                      exact hJs _ m ⟨rfl, Or.inr ⟨hal_ne0, hbig', hcne, hcb, hnr_eq⟩⟩)
                · s13_hsteps; exact hJ_jr _ m ⟨rfl, Or.inl hrsn_bin'⟩)
          | some cref =>
            s13_hsteps
            have hmrs : (FullMem c (fastPropMem s_disk { sem with
                core :=
                  { sem.core with
                    vals := vals', lvl := sem.core.lvl.set (new_lit.toNat / 2) alvl
                    rsns := sem.core.rsns.set (new_lit.toNat / 2) cref }
                scratch := { sem.scratch with phases := ph' } }) ⋆ R) m := by
              simpa only [fastPropMem_rsns, hvidx, m7_fastPropMem_with_rsns] using hm
            exact hJunfl (uf, ()) m ⟨sem.core.flags, 0#32, hfl_len,
              (fun hne => by cases hne),
              by simpa only [hal_ne0, ↓reduceIte, Option.getD_some] using hmrs⟩
    · intro Jph hJph
      have hph_m : (fastPropMem s_disk { sem with
          core := { sem.core with vals := vals' } }).scratch.phases.length = c.max_vars := by
        rw [fastPropMem_phases]; exact hph_len
      s13_hsplit
      · refine wp_join_group (fun _ mph => ∃ ph' : List (BitVec 8), ph'.length = c.max_vars ∧
            (FullMem c (fastPropMem s_disk { sem with
              core := { sem.core with vals := vals' }
              scratch := { sem.scratch with phases := ph' } }) ⋆ R) mph) ?_ ?_
        · rintro _ ⟨⟩ mph ⟨ph', hph', hmph⟩
          s13_hsteps; exact hJph () mph ⟨ph', hph', hmph⟩
        · intro Jp2 hJp2
          s13_hsplit
          · s13_hsteps
            rw [fastPropMem_phases, hvidx, m7_fastPropMem_with_phases] at hm
            exact hJp2 () m ⟨_, by rw [List.length_set, hph_len], hm⟩
          · s13_hsteps
            rw [fastPropMem_phases, hvidx, m7_fastPropMem_with_phases] at hm
            exact hJp2 () m ⟨_, by rw [List.length_set, hph_len], hm⟩
      · s13_hsteps; exact hJph () m ⟨sem.scratch.phases, hph_len, hm_v⟩
  · intro Jun hJun
    have hfl_m : (fastPropMem s_disk { sem with
        core := { sem.core with vals := vals' } }).core.flags.length = c.max_vars := by
      rw [fastPropMem_flags]; exact hfl_len
    s13_hsteps
    · exact hJun (un - 1#64, ()) m rfl
    · exact hJun (un, ()) m rfl
    · exact hJun (un, ()) m rfl

abbrev S13ConflEq (k0 k1 : FullCoreState) : Prop :=
  k1.confl_type = k0.confl_type ∧ k1.confl_ref = k0.confl_ref ∧
  k1.confl_lit0 = k0.confl_lit0 ∧ k1.confl_lit1 = k0.confl_lit1

theorem s13ConflEq_trans {a b c : FullCoreState} (h1 : S13ConflEq b c) (h2 : S13ConflEq a b) :
    S13ConflEq a c :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1, h1.2.2.2.trans h2.2.2.2⟩

theorem s13_lp_bin_wp {Γ : Env} {rs : List Ty} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s_base s_disk sem : FullState} {not_lit w0 nl_lvl : BitVec 32}
    {te un uf tk p q di end_v off_v ignore_ref : BitVec 64} {isBeyond rec_ph bigbig : Bool}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    {J_ovf : Cont (s13OvfSig isBeyond)}
    {J_lp : Cont [i64, i64, i64, i64, i64, i64, i64]}
    (hmaxv : c.max_vars < 2 * dimacsBound) (hwc : c.wcap < 2 * dimacsBound)
    (hpi : PropLitInv c F0 F_cur s_base sem not_lit.toNat off_v.toNat q.toNat p.toNat end_v.toNat)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (hp_lt : p.toNat < end_v.toNat)
    (hw0_get : sem.core.wstk[p.toNat]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32)
    (hte_eq : te.toNat = sem.core.trail_end)
    (hun_eq : un = sem.core.unassigned) (huf_eq : uf = sem.core.unflushed)
    (hoom : sem.core.oom = 0#64)
    (hnl : sem.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl)
    (hm : (FullMem c (fastPropMem s_disk sem) ⋆ R) m)
    (hJ_ovf : isBeyond = false → ∀ {sem' : FullState} {p' q' brk' : BitVec 64} {m' : Mem 64},
      PropLitInv c F0 F_cur s_base sem' not_lit.toNat off_v.toNat q'.toNat p'.toNat end_v.toNat →
      p.toNat ≤ p'.toNat → te.toNat = sem'.core.trail_end → sem'.core.oom = 0#64 →
      sem'.core.unassigned = sem.core.unassigned → sem'.core.unflushed = sem.core.unflushed →
      brk' = 1#64 → PropLitConfl F_cur ignore_ref sem'.core →
      (FullMem c (fastPropMem s_disk sem') ⋆ R) m' →
      wp Γ Q X (s13OvfJump isBeyond J_ovf (.var te) (.var un) (.var uf) (.var tk) (.var p')
        (.var q') (.var di) (.var brk') (.imm false) (.imm 0#32) (.imm 0#32) (.imm 0#32)
        (.imm 0#64)) m')
    (hJ_lp : ∀ {sem' : FullState} {te' un' uf' tk' p' q' : BitVec 64} {m' : Mem 64},
      PropLitInv c F0 F_cur s_base sem' not_lit.toNat off_v.toNat q'.toNat p'.toNat end_v.toNat →
      p.toNat < p'.toNat → p'.toNat ≤ end_v.toNat →
      sem.core.trail_end ≤ sem'.core.trail_end →
      te'.toNat = sem'.core.trail_end → un' = sem'.core.unassigned → uf' = sem'.core.unflushed →
      sem'.core.oom = sem.core.oom → S13ConflEq sem.core sem'.core →
      (FullMem c (fastPropMem s_disk sem') ⋆ R) m' →
      wp Γ Q X (.jump J_lp (.var te', (.var un', (.var uf', (.var tk', (.var p', (.var q',
        (.var di, ())))))))) m') :
    wp Γ Q X (s13LpBinStepExpr isBeyond c.hdr c.pVals c.pWstk c.pLevel c.pReason c.pTrail
      c.pTrailPos c.pFlags c.pPhases rec_ph bigbig not_lit w0 nl_lvl te un uf tk p q di
      J_ovf J_lp) m := by
  unfold dimacsBound at hmaxv hwc
  have hcv := hpi.len.core_ok.cur_vars_le
  have hfl_len := hpi.len.core_ok.flags_len
  have hph_len := hpi.len.scratch_ok.phases_len
  have hvals_len := hpi.len.core_ok.vals_len
  have hlvl_len := hpi.len.core_ok.lvl_len
  have hwstk_len := hpi.len.core_ok.wstk_len_arr
  have ⟨hend_le, hwlen_le⟩ := hpi.end_lt_wcap hnot_lt
  have hend_wcap : end_v.toNat ≤ c.wcap := Nat.le_trans hend_le hwlen_le
  have hq_ge := hpi.sw.q_ge; have hq_le := hpi.sw.q_le_p; have hp_le := hpi.sw.p_le_end
  have hp_rem_pos : 0 < end_v.toNat - p.toNat := Nat.sub_pos_of_lt hp_lt
  have hp1_n : (p + 1#64).toNat = p.toNat + 1 := m7_bv64_add1_toNat (by omega)
  have hq1_n : (q + 1#64).toNat = q.toNat + 1 := m7_bv64_add1_toNat (by omega)
  have hq_lt_ws : q.toNat < sem.core.wstk.length := by rw [hwstk_len]; omega
  obtain ⟨hother_lt, hent, hrem1⟩ :=
    watchSlice_inv_bin hpi.sw.rem_slice hp_rem_pos hw0_get hflag
  have hsw1 := (hpi.sw.advance_rem (p' := p.toNat + 1) (Nat.le_succ _) hp_lt
    (by simpa [Nat.sub_sub] using hrem1)).write_bin
    (c := c) hcv hnot_lt hq_le hq_lt_ws hflag hother_lt hent
  let blk := w0 &&& 2147483647#32
  have hblk_eq : blk = w0 &&& 0x7FFFFFFF#32 := rfl
  let wstk1 := sem.core.wstk.set q.toNat w0
  let sem1 : FullState := { sem with core := { sem.core with wstk := wstk1 } }
  have hws1_len : sem1.core.wstk.length = c.wcap := by
    simpa [sem1, wstk1, List.length_set] using hwstk_len
  have hlen1 : sem1.LengthsOk c :=
    ⟨{ hpi.len.core_ok with wstk_len_arr := by simp [sem1, wstk1, hwstk_len] },
     hpi.len.scratch_ok⟩
  have hnw1 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c sem1.core) :=
    fullWitnessInv_nw_congr hlen1.core_ok.cur_vars_le hpi.nw
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hblk_vals_m : (blk.setWidth 64).toNat < (fastPropMem s_disk sem).core.vals.length := by
    rw [fastPropMem_vals, hvals_len, bv_c0_zext32_64, hblk_eq]; omega
  have hblk_vals_raw : blk.toNat < sem.core.vals.length := by rw [hvals_len, hblk_eq]; omega
  have hm_ws : q.toNat < (fastPropMem s_disk sem).core.wstk.length := by
    rw [fastPropMem_wstk]; exact hq_lt_ws
  let vb := (fastPropMem s_disk sem).core.vals[blk.toNat]'(by
    rw [← bv_c0_zext32_64 blk]; exact hblk_vals_m)
  have hvb_eq : vb = sem.core.vals[blk.toNat]'hblk_vals_raw :=
    (fc_getElem_vals s_disk sem).trans (fc_getElem_eq_of_idx rfl _ hblk_vals_raw)
  have hvb_1 : vb = sem1.core.vals[blk.toNat]'(by simp [sem1]; exact hblk_vals_raw) := hvb_eq
  have hpi1 : PropLitInv c F0 F_cur s_base sem1 not_lit.toNat off_v.toNat
      (q + 1#64).toNat (p + 1#64).toNat end_v.toNat := by
    rw [hq1_n, hp1_n]
    exact ⟨hlen1, hnw1, hsw1, hpi.ag.update (fun k => { k with wstk := wstk1 }),
      hpi.tr.congr rfl rfl rfl, hpi.perm, hpi.sc_eq, hpi.not_f⟩
  have hp1_n' : (p + (1 : BitVec 64)).toNat = p.toNat + 1 := hp1_n
  unfold s13LpBinStepExpr
  s13_hsplit
  · rw [fastPropMem_with_wstk, fastPropMem_wstk] at hm
    s13_hsteps
    exact hJ_lp hpi1 (by rw [hp1_n']; omega) (by rw [hp1_n']; omega) (Nat.le_refl _) hte_eq
      hun_eq huf_eq rfl ⟨rfl, rfl, rfl, rfl⟩ hm
  · rw [fastPropMem_with_wstk, fastPropMem_wstk] at hm
    have hnsgt : (0#32).slt (BitVec.signExtend 32 vb) = false := by
      simpa only [vb, blk, show (2147483647 : BitVec 32) = 2147483647#32 from rfl,
        show (0 : BitVec 32) = 0#32 from rfl] using hc
    s13_hsplit
    · cases isBeyond with
      | true =>
        simp only [↓reduceIte]
        s13_hsteps
        exact hJ_lp hpi1 (by rw [hp1_n']; omega) (by rw [hp1_n']; omega) (Nat.le_refl _) hte_eq
          hun_eq huf_eq rfl ⟨rfl, rfl, rfl, rfl⟩ hm
      | false =>
        have hslt : (BitVec.signExtend 32 vb).slt 0#32 = true := by
          simpa only [vb, blk, show (2147483647 : BitVec 32) = 2147483647#32 from rfl,
            show (0 : BitVec 32) = 0#32 from rfl] using hc
        have hov_f : sem.core.vals[blk.toNat]?.getD 0#8 = 0xFF#8 :=
          propLit_vals_neg hpi.nw hother_lt hblk_vals_raw (by rw [← hvb_eq]; exact hslt)
        have ⟨hpi_c, hcf_c⟩ := propLit_bin_confl (ignore_ref := ignore_ref) hpi hsw1
          hnot_lt hother_lt hent hov_f hp1_n hq1_n
        let sem_c : FullState :=
          { sem1 with core := { sem1.core with
            confl_type := 1#64, confl_lit0 := not_lit.setWidth 64,
            confl_lit1 := blk.setWidth 64 } }
        have hpi_c' : PropLitInv c F0 F_cur s_base sem_c not_lit.toNat off_v.toNat
            (q + 1#64).toNat (p + 1#64).toNat end_v.toNat := by
          have hlen_c : sem_c.LengthsOk c :=
            ⟨{ hpi_c.len.core_ok with wstk_len_arr := hws1_len },
             hpi_c.len.scratch_ok⟩
          exact ⟨hlen_c,
            fullWitnessInv_nw_congr hlen_c.core_ok.cur_vars_le hpi_c.nw rfl rfl rfl rfl rfl rfl
              rfl rfl rfl rfl rfl rfl rfl,
            hpi_c.sw.with_nonwatch rfl rfl rfl rfl rfl,
            hpi.ag.update (fun k => { k with
              wstk := wstk1, confl_type := 1#64, confl_lit0 := not_lit.setWidth 64,
              confl_lit1 := blk.setWidth 64 }),
            hpi_c.tr.congr rfl rfl rfl, hpi_c.perm, hpi_c.sc_eq, hpi_c.not_f⟩
        have hcf_c' : PropLitConfl F_cur ignore_ref sem_c.core := by
          rcases hcf_c with hbad | ⟨h1 | h2, _⟩
          · exact Or.inl hbad
          · exact Or.inr ⟨Or.inl h1, fun hc2 => by change (1#64) = 2#64 at hc2; cases hc2⟩
          · exfalso; have ht2 := h2.1; dsimp only at ht2; cases ht2
        simp only [Bool.false_eq_true, ↓reduceIte]
        s13_hsteps
        refine hJ_ovf rfl hpi_c' (by rw [hp1_n']; omega) hte_eq hoom rfl rfl rfl hcf_c' ?_
        unfold fastPropMem at hm ⊢
        exact hm
    · have hnslt : (BitVec.signExtend 32 vb).slt 0#32 = false := by
        simpa only [vb, blk, show (2147483647 : BitVec 32) = 2147483647#32 from rfl,
          show (0 : BitVec 32) = 0#32 from rfl] using hc
      have hov_un : sem1.core.vals[blk.toNat]?.getD 0#8 = 0#8 :=
        propLit_vals_un hnw1 hother_lt (by simp [sem1]; exact hblk_vals_raw)
          (by rw [← hvb_1]; exact hnsgt) (by rw [← hvb_1]; exact hnslt)
      have hte_lt : sem1.core.trail_end < sem1.core.cur_vars :=
        m7_trail_end_lt_of_unassigned hnw1 hother_lt hov_un
      s13_hsteps_nogrp
      have hblk_m : (blk.setWidth 64).toNat < (fastPropMem s_disk sem1).core.vals.length := by
        rw [fastPropMem_vals, hvals_len, bv_c0_zext32_64, hblk_eq]; omega
      refine wp_store_sep (FullArenaTactics.c0_store_full_vals ((1#32).setWidth 8) hblk_m hm) ?_
      intro mv1 hmv1; clear hm; dsimp only at hmv1
      rw [bv_c0_zext32_64, fastPropMem_vals, show (2147483647 : BitVec 32) = 2147483647#32 from rfl,
        show BitVec.setWidth 8 (1#32) = 1#8 from rfl, m7_fastPropMem_with_vals] at hmv1
      s13_hsteps_nogrp
      have hnblk_m : ((blk ^^^ 1#32).setWidth 64).toNat <
          (fastPropMem s_disk { sem1 with core :=
            { sem1.core with vals := sem1.core.vals.set blk.toNat 1#8 } }).core.vals.length := by
        rw [fastPropMem_vals, List.length_set, hvals_len, bv_c0_zext32_64, BitVec.toNat_xor,
          show (1#32 : BitVec 32).toNat = 1 from rfl, fc_nat_xor_one, hblk_eq]
        split <;> omega
      refine wp_store_sep (FullArenaTactics.c0_store_full_vals ((-1#32).setWidth 8) hnblk_m hmv1)
        ?_
      intro mv2 hmv2; clear hmv1; dsimp only at hmv2
      have hnblk_n : ((blk ^^^ 1#32).setWidth 64).toNat = blk.toNat ^^^ 1 := by
        rw [bv_c0_zext32_64, BitVec.toNat_xor]; rfl
      have hm1_8 : (-1#32 : BitVec 32).setWidth 8 = 0xFF#8 := by decide
      rw [show (2147483647 : BitVec 32) = 2147483647#32 from rfl,
        show (1 : BitVec 32) = 1#32 from rfl,
        show (w0 &&& 2147483647#32) ^^^ 1#32 = blk ^^^ 1#32 from rfl,
        hnblk_n, hm1_8, fastPropMem_vals, m7_fastPropMem_with_vals] at hmv2
      let vals' := (sem1.core.vals.set blk.toNat 1#8).set (blk.toNat ^^^ 1) 0xFF#8
      have hvals'_len : vals'.length = 2 * c.max_vars := by
        simpa [vals', List.length_set, sem1] using hvals_len
      s13_hsteps_nogrp
      refine s13_lp_assign_tail_wp hmaxv hlen1 hvals'_len hte_lt hte_eq hother_lt hnot_lt
        (m7_bv32_rshift1_toNat blk) (by simpa only [← m7_fastPropMem_with_vals] using hmv2) ?_
      intro flags' ph' un_n uf_n jr m' hfl' hph' hjr _ sem_n hm'
      have hjr' : jr = ((not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32) ∨
          (nl_lvl ≠ 0#32 ∧
            let nr := sem1.core.rsns[not_lit.toNat / 2]?.getD 0xFFFFFFFF#32
            nr ≠ 0xFFFFFFFF#32 ∧ (nr &&& 0x80000000#32) ≠ 0#32 ∧ jr = nr) := by
        rcases hjr rfl with h1 | ⟨h2, _, h3, h4, h5⟩
        · exact Or.inl h1
        · exact Or.inr ⟨h2, h3, h4, h5⟩
      have hstep := s13_bin_jumpreason_step hpi hsw1 hws1_len hfl' hph' hnot_lt hother_lt hov_un
        (by simpa [sem1] using hnl) hent hp1_n hq1_n (unas' := un_n) (unfl' := uf_n) hjr'
      have hcv_le := hpi.len.core_ok.cur_vars_le
      have hte_lt_s : sem.core.trail_end < sem.core.cur_vars := hte_lt
      have hte1_n : (te + 1#64).toNat = sem.core.trail_end + 1 := by
        rw [m7_bv64_add1_toNat (by rw [hte_eq]; omega), hte_eq]
      have hte_le_inc : sem.core.trail_end ≤ sem.core.trail_end + 1 := Nat.le_succ _
      have hq1_n' : (q + (1 : BitVec 64)).toNat = q.toNat + 1 := hq1_n
      have hinv_n := hstep.1
      rw [hq1_n, hp1_n] at hinv_n
      exact hJ_lp (sem' := sem_n) (by dsimp only; rw [hq1_n', hp1_n']; exact hinv_n)
        (by dsimp only; rw [hp1_n']; omega) (by dsimp only; rw [hp1_n']; omega)
        hte_le_inc hte1_n rfl rfl rfl ⟨rfl, rfl, rfl, rfl⟩ hm'

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S2

end
