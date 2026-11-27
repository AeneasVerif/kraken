/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S2OTFSUnit
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S2BCPWatchProof2c
public import LeanQbe.T.Examples.Kissat.FullM5OtfsLemmas4a
public import LeanQbe.T.Examples.Kissat.FullM5OtfsLemmas4b
import LeanQbe.T.Examples.Kissat.FullLearnAnaLemmas1
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0Step

/-!
# Kissat Fidelity Step 13 Shard S2-B Specs & Core Proofs (`FullFidelityStep13S2OTFSUnitProof0a`)

Plain `public section` (`@[expose]` ONLY on `def` specs, `0` `@[expose]` on theorems/lemmas,
`0` `import all`, `<= 100` cols, every theorem `<= 320` lines):
1. Step-13 `S2-B` & cross-shard specs (`step13Wm4SetSpec`, `step13OtfsLargeSpec`,
   `step13EagerSubsumeSpec`, `step13AddClauseSpec`, `step13LearnClauseM6Spec`) + `_monoX`.
2. `full_update_classify_fid_step13_wp` (`step13UpdateClassifyM6Spec`, calling `m6_wm4_get` /
   `m6_wm4_set`).
3. `full_one_lit_confl_step13_wp` (`Full.fullOneLitConflSpec`, calling `"full_backtrack_ac_fid"`
   with binary `jumpreasons` on `confl_type == 1` and `m5_oneLit_large_branch_wp` reuse).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S2

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM5Otfs
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeHelpers
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullAnalyzeTactics
open FullLearnAnaTactics
open scoped FullLearnAnaTactics
open Kraken.Bedrock2.Test

/-! ## 1. Step-13 `S2-B` & Cross-Shard Specs -/

/-- Step-13 contract for `m6_wm4_set(h, v)`: identical to `m6HdrW2aSpec [i64] []`. -/
@[expose] def step13Wm4SetSpec : Spec [i64, i64] [] :=
  m6HdrW2aSpec [i64] []

theorem step13Wm4SetSpec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post []}
    {X X' : XPost} (h : step13Wm4SetSpec xs m Q X) : step13Wm4SetSpec xs m Q X' :=
  m6HdrW2aSpec_monoX h

/-- Step-13 contract for `full_otfs_large`: extends `Full.fullOtfsLargeSpec` by allowing
`s'.core.flags` (`flags'`) to mark irredundant OTFS literals with `|= 24u`. -/
@[expose] def step13OtfsLargeSpec : Spec [i64, i32, i32] [.bool] :=
  fun (h, cref, uip, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut idx_u : Nat) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut s.core ∧
      FullArenaVarsNodup s ∧ s.core.dense_mode = 0#64 ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
      fullArenaClauseGarb s cref.toNat = false ∧ uip.toNat < 2 * s.core.cur_vars ∧
      idx_u < cut ∧ (s.core.trl[idx_u]?.getD 0#32).toNat = uip.toNat ∧
      s.core.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref ∧
      (s.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = s.core.cur_level ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((fullArenaClauseLits s cref.toNat).filter fun l =>
          decide (l ≠ uip.toNat ∧ (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∨
            l = (s.core.arena[cref.toNat + 3]?.getD 0#32).toNat ∨
            l = (s.core.arena[cref.toNat + 4]?.getD 0#32).toNat)))) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) flags' arena' wvec' wstk' wlen' wu' oom' sc' m',
        let s' : FullState :=
          { s with
            core := { s.core with flags := flags', arena := arena', wvec := wvec',
                                  wstk := wstk', wlen := wlen', wusable := wu', oom := oom' }
            scratch := sc' }
        s'.LengthsOk c → FullWitnessCutInv c F0 F_cur idx_u s'.core → FullArenaVarsNodup s' →
        FullExtScratchPres s s' → sc'.work_stk1 = s.scratch.work_stk1 →
        sc'.work_stk2 = s.scratch.work_stk2 → sc'.res_sz = s.scratch.res_sz →
        fullArenaClauseRefs s' = fullArenaClauseRefs s →
        (ok = true → cref.toNat ∈ fullArenaClauseRefs s' ∧
          fullArenaClauseGarb s' cref.toNat = false ∧
          ∀ l ∈ fullArenaClauseLits s' cref.toNat, s'.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
            ((s'.core.lvl[l / 2]?.getD 0#32).toNat = s'.core.cur_level →
              ∃ m < idx_u, (s'.core.trl[m]?.getD 0#32).toNat = l ^^^ 1)) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem step13OtfsLargeSpec_monoX {xs : Tup Val [i64, i32, i32]} {m : Mem 64} {Q : Post [.bool]}
    {X X' : XPost} (h : step13OtfsLargeSpec xs m Q X) :
    step13OtfsLargeSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, ⟨⟩⟩; exact h

/-- Step-13 contract for `full_eager_subsume`: extends `Full.fullEagerSubsumeSpec` by threading
`nr'` (`h->num_redundant` decrement when a subsumed redundant clause is garbage-marked). -/
@[expose] def step13EagerSubsumeSpec : Spec [i64, i64] [] :=
  fun (h, new_ref, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧
      (∀ k < s.core.tmp_len, (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars) ∧
      (new_ref.toNat < 0x80000000 → new_ref.toNat ∈ fullArenaClauseRefs s) ∧ (FullMem c s ⋆ R) m ∧
      ∀ arena' ag' nr' sc' m',
        let s' : FullState :=
          { s with
            core := { s.core with arena := arena', arena_garbage := ag', num_redundant := nr' }
            scratch := sc' }
        FullSparseInvW c F0 F_cur s' → sc'.work_stk2 = s.scratch.work_stk2 →
        (FullMem c s' ⋆ R) m' → Q () m'

theorem step13EagerSubsumeSpec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post []}
    {X X' : XPost} (h : step13EagerSubsumeSpec xs m Q X) :
    step13EagerSubsumeSpec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

/-- Step-13 contract for `full_add_clause`: extends `Full.fullAddClauseSpec` by allowing
`s'.core.flags` (`flags'`) updates in the `len = 2` binary-clause branch. -/
@[expose] def step13AddClauseSpec : Spec [i64, i32, i32, .bool] [i64] :=
  fun (h, len, _glue, _red, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ s.core.dense_mode = 0#64 ∧
      len.toNat ≤ c.max_vars ∧
      (2 ≤ len.toNat →
        (∀ l ∈ (s.core.tmp.take len.toNat).map BitVec.toNat, l < 2 * s.core.cur_vars) ∧
        ((s.core.tmp.take len.toNat).map fun x => x.toNat / 2).Nodup ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.core.tmp.take len.toNat).map BitVec.toNat))) ∧
      (FullMem c s ⋆ R) m ∧
      if len.toNat < 2 then Q (0xFFFFFFFF#64, ()) m
      else if len.toNat = 2 then
        ∀ r flags' wvec' wstk' wlen' wusable' nb' wsort' m',
          let s' : FullState :=
            { s with core := { s.core with flags := flags', wvec := wvec', wstk := wstk',
                                           wlen := wlen', wusable := wusable',
                                           num_binary := nb' }
                     scratch := { s.scratch with wsort := wsort' } }
          (r = 0xFFFFFFFF#64 ∨ r = 0xFFFFFFFE#64) →
          s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → (FullMem c s' ⋆ R) m' → Q (r, ()) m'
      else
        ∀ r arena' alen' wvec' wstk' wlen' wusable' fred' ni' nr' wsort' m',
          let s' : FullState :=
            { s with core := { s.core with arena := arena', arena_len := alen', wvec := wvec',
                                           wstk := wstk', wlen := wlen', wusable := wusable',
                                           first_reducible := fred', num_irred := ni',
                                           num_redundant := nr' }
                     scratch := { s.scratch with wsort := wsort' } }
          (r = 0xFFFFFFFF#64 ∨ r = BitVec.ofNat 64 s.core.arena_len) →
          s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
          (∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s') →
          (FullArenaVarsNodup s → FullArenaVarsNodup s') →
          (r = BitVec.ofNat 64 s.core.arena_len → alen' = s.core.arena_len + 3 + len.toNat ∧
            s.core.arena_len ∈ fullArenaClauseRefs s' ∧
            fullArenaClauseGarb s' s.core.arena_len = false ∧
            fullArenaClauseLits s' s.core.arena_len =
              (s.core.tmp.take len.toNat).map BitVec.toNat) →
          (FullMem c s' ⋆ R) m' → Q (r, ()) m'

theorem step13AddClauseSpec_monoX {xs : Tup Val [i64, i32, i32, .bool]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost} (h : step13AddClauseSpec xs m Q X) :
    step13AddClauseSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, _, ⟨⟩⟩; exact h

/-- Step-13 `FullM6HdrMem`-threaded contract for `full_learn_clause_m6`: matches
`step10LearnClauseM6Spec` while dropping the unused `lv ≤ lvl[tmp[tmp_len - 1]]` precondition
after `S4`'s `full_min_shrink_m6` reversal to descending level order. -/
@[expose] def step13LearnClauseM6Spec : Spec [i64, i64] [i64] :=
  fun (h, _glue, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ext : List (BitVec 64))
      (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧
      FullOtfsInvW c F0 F_cur s ∧ 0 < s.core.cur_level ∧
      1 ≤ s.core.tmp_len ∧ s.core.tmp_len ≤ s.core.cur_vars ∧
      (List.map (fun x => x.toNat / 2) (List.take s.core.tmp_len s.core.tmp)).Nodup ∧
      (∀ k, k < s.core.tmp_len →
        let l := (s.core.tmp[k]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 255#8) ∧
      (∀ k, 1 ≤ k → k < s.core.tmp_len →
        let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
        0 < lv ∧ lv < s.core.cur_level) ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause (List.map BitVec.toNat (List.take s.core.tmp_len s.core.tmp))) ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
        M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        s'.scratch.work_stk2 = s.scratch.work_stk2 →
        (r = 20#64 →
          F0.Unsat ∧ FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
        (r = 0#64 → FullSparseInvW c F0 F_cur s') →
        (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

theorem step13LearnClauseM6Spec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost} (h : step13LearnClauseM6Spec xs m Q X) :
    step13LearnClauseM6Spec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

/-! ## 2. `full_update_classify_fid` (`step13UpdateClassifyM6Spec`) -/

/-- `full_update_classify_fid` computes `bigbig` over `num_binary`/`num_irred` and updates
`watermarks[4]` bit 1 via `m6_wm4_get` / `m6_wm4_set`, preserving `FullM6HdrMem c ext s`. -/
theorem full_update_classify_fid_step13_wp (Γ : Env)
    (hGet : ∀ a m Q X, step13Wm4GetSpec a m Q X → Γ "m6_wm4_get" [i64] [i64] a m Q X)
    (hSet : ∀ a m Q X, step13Wm4SetSpec a m Q X → Γ "m6_wm4_set" [i64, i64] [] a m Q X) :
    ∀ a m Q X, step13UpdateClassifyM6Spec a m Q X →
      Func.wp Γ fidStep13S2UpdateClassifyFn.body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hspec
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hspec
  dsimp only [Func.wp, fidStep13S2UpdateClassifyFn, full_update_classify_fid_body]
  have hnb := FullArenaTactics.load_full_num_binary (fullM6HdrMem_focus_full hm)
  have hni := FullArenaTactics.load_full_num_irred (fullM6HdrMem_focus_full hm)
  c0_hsteps_nogrp
  refine wp_load_of hnb ?_
  c0_hsteps_nogrp
  refine wp_load_of hni ?_
  c0_hsteps_nogrp
  refine wp_join_group (ts := [.bool]) (fun _ m0 => m0 = m) ?_ ?_
  · rintro _ ⟨_bb, ⟨⟩⟩ m0 rfl
    c0_hsteps_nogrp
    c0_call hGet
    refine ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, fun wm4 hm1 => ?_⟩
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ m2 => m2 = m0) ?_ ?_
    · rintro _ ⟨wm4', ⟨⟩⟩ m2 rfl
      c0_hsteps_nogrp
      c0_call hSet
      exact m6HdrW2aSpec_of rfl hcfg hext hlen hm1 fun _ ext' s' m' hc hl hs hx hinit hm' =>
        hQ () ext' s' m' hc hl hs hx hinit hm'
    · intro Jw hJw
      c0_hsplit
      · c0_hsteps; exact hJw _ _ rfl
      · c0_hsteps; exact hJw _ _ rfl
  · intro Jb hJb
    c0_hsplit
    · c0_hsteps_nogrp
      refine wp_load_of hnb ?_
      c0_hsplit
      · c0_hsteps; exact hJb _ _ rfl
      · c0_hsteps; exact hJb _ _ rfl
    · c0_hsteps; exact hJb _ _ rfl

/-! ## 3. `full_one_lit_confl` (`Full.fullOneLitConflSpec`) -/

private theorem s13_chronoAssign_bin_preserves_fullWitness {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hlen : s.LengthsOk c)
    (hw : Full.FullWitnessInv c F0 F_cur s.core) {lit jr : BitVec 32} {alvl : Nat}
    {flags' : List (BitVec 32)} {unassigned' unflushed' : BitVec 64}
    (hlit : lit.toNat < 2 * s.core.cur_vars) (hun : s.core.vals[lit.toNat]?.getD 0#8 = 0#8)
    (halvl_le : alvl ≤ s.core.cur_level) (hjr_ne : jr ≠ 0xFFFFFFFF#32)
    (hjr_hi : (jr &&& 0x80000000#32) ≠ 0#32)
    (hl0 : alvl = 0 → (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]))
    (hrsn : 0 < alvl →
      let ot := (jr &&& 0x7FFFFFFF#32).toNat
      ot < 2 * s.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, ot]) ∧
      ∃ m < s.core.trail_end, (s.core.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
        (s.core.lvl[ot / 2]?.getD 0#32).toNat ≤ alvl) :
    let v := lit.toNat / 2
    let rsn' := if alvl = 0 then 0xFFFFFFFF#32 else jr
    Full.FullWitnessInv c F0 F_cur
      { s.core with
        vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
        flags := flags', lvl := s.core.lvl.set v (BitVec.ofNat 32 alvl)
        rsns := s.core.rsns.set v rsn', trl := s.core.trl.set s.core.trail_end lit
        trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
        trail_end := s.core.trail_end + 1
        unassigned := unassigned', unflushed := unflushed' } := by
  intro v rsn'
  let k' : FullCoreState :=
    { s.core with
      vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
      flags := flags', lvl := s.core.lvl.set v (BitVec.ofNat 32 alvl)
      rsns := s.core.rsns.set v rsn', trl := s.core.trl.set s.core.trail_end lit
      trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
      trail_end := s.core.trail_end + 1, unassigned := unassigned', unflushed := unflushed' }
  have hcl := hlen.core_ok
  have hte_lt : s.core.trail_end < s.core.cur_vars := hw.trail_end_lt_of_unassigned hlit hun
  have hnot_var : ∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ v :=
    (hw.vals_zero_iff hlit).mp hun
  have hne_lit : lit.toNat ^^^ 1 ≠ lit.toNat := litNeg_ne_self lit.toNat
  have hv_lt : v < c.max_vars := by have := hcl.cur_vars_le; omega
  have hte_max : s.core.trail_end < c.max_vars := by have := hcl.cur_vars_le; omega
  have halvl_lt32 : alvl < 2 ^ 32 := by
    have := Full.fullInv_max_vars_lt32 c; have := hw.cur_level_le; have := hcl.cur_vars_le; omega
  have hte_lt32 : s.core.trail_end < 2 ^ 32 := by have := Full.fullInv_max_vars_lt32 c; omega
  have htrl_get : ∀ i < s.core.trail_end + 1, (k'.trl[i]?.getD 0#32).toNat =
      if i = s.core.trail_end then lit.toNat else (s.core.trl[i]?.getD 0#32).toNat := fun i _ => by
    by_cases he : i = s.core.trail_end
    · subst he; simp [k', List.getElem?_set_self (by rw [hcl.trl_len]; exact hte_max)]
    · simp [k', he, List.getElem?_set_ne (Ne.symm he)]
  have hlvl_get : ∀ w < s.core.cur_vars, (k'.lvl[w]?.getD 0#32).toNat =
      if w = v then alvl else (s.core.lvl[w]?.getD 0#32).toNat := fun w _ => by
    by_cases he : w = v
    · subst he; simp [k', List.getElem?_set_self (by rw [hcl.lvl_len]; exact hv_lt),
        bv32_ofNat_toNat halvl_lt32]
    · simp [k', he, List.getElem?_set_ne (Ne.symm he)]
  have hvals_get : ∀ l < 2 * s.core.cur_vars, k'.vals[l]?.getD 0#8 =
      if l = lit.toNat ^^^ 1 then 0xFF#8 else if l = lit.toNat then 1#8
      else s.core.vals[l]?.getD 0#8 := fun l hl => by
    have hcm := hcl.cur_vars_le
    by_cases h1 : l = lit.toNat ^^^ 1
    · subst h1; simp only [k', ↓reduceIte]
      rw [List.getElem?_set_self (by simp [hcl.vals_len]; omega)]; rfl
    · simp only [k', h1, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : l = lit.toNat
      · subst h2; simp only [↓reduceIte]
        rw [List.getElem?_set_self (by rw [hcl.vals_len]; omega)]; rfl
      · simp only [h2, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h2)]
  have hrsn_get : ∀ w < s.core.cur_vars, k'.rsns[w]?.getD 0xFFFFFFFF#32 =
      if w = v then rsn' else s.core.rsns[w]?.getD 0xFFFFFFFF#32 := fun w _ => by
    by_cases he : w = v
    · subst he; simp [k', List.getElem?_set_self (by rw [hcl.rsns_len]; exact hv_lt)]
    · simp [k', he, List.getElem?_set_ne (Ne.symm he)]
  have hlt_w : ∀ i, i < s.core.trail_end → (s.core.trl[i]?.getD 0#32).toNat / 2 < s.core.cur_vars :=
    fun i hi => by have := hw.trail_lits_lt i hi; omega
  have hlift_rsn : ∀ {up p0 : Nat} {rv : BitVec 32} {p_lvl : Nat}, up ≤ s.core.trail_end →
      (rv &&& 0x80000000#32) ≠ 0#32 → p0 / 2 < s.core.cur_vars →
      (k'.lvl[p0 / 2]?.getD 0#32).toNat = p_lvl →
      (let ot := (rv &&& 0x7FFFFFFF#32).toNat
       ot < 2 * s.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [p0, ot]) ∧
       ∃ m < up, (s.core.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
         (s.core.lvl[ot / 2]?.getD 0#32).toNat ≤ p_lvl) →
      let ot := (rv &&& 0x7FFFFFFF#32).toNat
      ot < 2 * k'.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [p0, ot]) ∧
      ∃ m < up, (k'.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
        (k'.lvl[ot / 2]?.getD 0#32).toNat ≤ (k'.lvl[p0 / 2]?.getD 0#32).toNat := by
    rintro up p0 rv p_lvl hup _ _ hpl ⟨hlt, hent, m, hm, hmeq, hlvl_le⟩
    have hm' : m < s.core.trail_end := Nat.lt_of_lt_of_le hm hup
    have hot_v : (rv &&& 0x7FFFFFFF#32).toNat / 2 ≠ v := fun heqv => by
      have hme := hnot_var m hm'; rw [hmeq] at hme
      exact hme (by simpa [fullInv_var_xor1] using heqv)
    exact ⟨hlt, hent, m, hm,
      by rw [htrl_get m (by omega)]; simp [show m ≠ s.core.trail_end by omega, hmeq],
      by rw [hpl, hlvl_get _ (by omega), ite_eq_right hot_v]; exact hlvl_le⟩
  exact {
    ext_sound := hw.ext_sound, inconsistent_sound := hw.inconsistent_sound
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr
    cur_level_le := Nat.le_trans hw.cur_level_le (Nat.le_succ _)
    trail_lits_lt := fun i hi => by
      dsimp only at hi ⊢; rw [htrl_get i hi]
      split <;> (first | exact hlit | exact hw.trail_lits_lt i (by omega))
    trail_vars_nodup := fun i j hi hj hveq => by
      dsimp only at hi hj ⊢; rw [htrl_get i hi, htrl_get j hj] at hveq
      split at hveq <;> split at hveq
      · omega
      · exact absurd hveq.symm (hnot_var j (by omega))
      · exact absurd hveq (hnot_var i (by omega))
      · exact hw.trail_vars_nodup i j (by omega) (by omega) hveq
    vals_domain := fun l hl => by
      dsimp only at hl ⊢; rw [hvals_get l hl]
      split; exact Or.inr (Or.inr rfl); split; exact Or.inr (Or.inl rfl); exact hw.vals_domain l hl
    vals_true_iff := fun l hl => by
      dsimp only at hl ⊢; rw [hvals_get l hl]; constructor
      · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
        · simp [hneg] at h1
        · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
          · exact ⟨s.core.trail_end, by omega, by rw [htrl_get _ (by omega)]; simp [hpos]⟩
          · simp only [hpos, ↓reduceIte] at h1
            obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl).mp h1
            exact ⟨i, by omega, by
              rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
      · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq; by_cases hie : i = s.core.trail_end
        · simp only [hie, ↓reduceIte] at heq; subst heq; simp [Ne.symm hne_lit]
        · simp only [hie, ↓reduceIte] at heq
          have hlv : l / 2 ≠ v := by rw [← heq]; exact hnot_var i (by omega)
          simp only [show l ≠ lit.toNat ^^^ 1 from fun h => hlv (by rw [h, fullInv_var_xor1]),
            show l ≠ lit.toNat from fun h => hlv (by rw [h]), ↓reduceIte]
          exact (hw.vals_true_iff l hl).mpr ⟨i, by omega, heq⟩
    vals_false_iff := fun l hl => by
      dsimp only at hl ⊢; rw [hvals_get l hl]; constructor
      · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
        · exact ⟨s.core.trail_end, by omega, by
            rw [htrl_get _ (by omega)]; simp only [↓reduceIte, hneg]; exact (litNeg_litNeg _).symm⟩
        · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
          · simp [hpos] at h1
          · simp only [hpos, ↓reduceIte] at h1
            obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp h1
            exact ⟨i, by omega, by
              rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
      · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq; by_cases hie : i = s.core.trail_end
        · simp only [hie, ↓reduceIte] at heq
          have hl_eq : l = lit.toNat ^^^ 1 := by
            have h := congrArg litNeg heq
            change lit.toNat ^^^ 1 = litNeg (litNeg l) at h
            rw [litNeg_litNeg] at h; exact h.symm
          simp [hl_eq]
        · simp only [hie, ↓reduceIte] at heq
          have hlv : l / 2 ≠ v := by
            have h := hnot_var i (by omega); rw [heq] at h; rwa [fullInv_var_xor1] at h
          simp only [show l ≠ lit.toNat ^^^ 1 from fun h => hlv (by rw [h, fullInv_var_xor1]),
            show l ≠ lit.toNat from fun h => hlv (by rw [h]), ↓reduceIte]
          exact (hw.vals_false_iff l hl).mpr ⟨i, by omega, heq⟩
    lvl_le := fun i hi => by
      dsimp only at hi ⊢; change (k'.lvl[(k'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ _
      rw [htrl_get i hi]; by_cases hie : i = s.core.trail_end
      · simp only [hie, ↓reduceIte]; rw [hlvl_get v (by omega)]; simpa using halvl_le
      · have hilt : i < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte]
        rw [hlvl_get _ (hlt_w i hilt), ite_eq_right (hnot_var i hilt)]; exact hw.lvl_le i hilt
    dec_earliest := fun i j hi hj hleq hdec => by
      dsimp only at hi hj hleq hdec ⊢; change _ ≤ _ at ⊢
      rw [htrl_get i hi] at hleq; rw [htrl_get j hj] at hleq hdec
      by_cases hje : j = s.core.trail_end
      · subst hje; simp only [↓reduceIte] at hleq hdec
        rw [hlvl_get v (by omega), hrsn_get v (by omega)] at hdec; simp only [↓reduceIte] at hdec
        have hal0 : alvl ≠ 0 := by omega
        simp [rsn', hal0, hjr_ne] at hdec
      · by_cases hie : i = s.core.trail_end
        · omega
        · have hilt : i < s.core.trail_end := by omega
          have hjlt : j < s.core.trail_end := by omega
          simp only [hie, hje, ↓reduceIte] at hleq hdec
          rw [hlvl_get _ (hlt_w i hilt), hlvl_get _ (hlt_w j hjlt)] at hleq
          rw [hlvl_get _ (hlt_w j hjlt), hrsn_get _ (hlt_w j hjlt)] at hdec
          simp only [hnot_var i hilt, hnot_var j hjlt, ↓reduceIte] at hleq hdec
          exact hw.dec_earliest i j hilt hjlt hleq hdec
    levels_inhabited := fun L hL1 hLle => by
      dsimp only at hL1 hLle ⊢; obtain ⟨i, hi, hli⟩ := hw.levels_inhabited L hL1 hLle
      exact ⟨i, by omega, by
        rw [htrl_get i (by omega), ite_eq_right (by omega), hlvl_get _ (hlt_w i hi),
          ite_eq_right (hnot_var i hi)]; exact hli⟩
    level0_sound := fun i hi hli => by
      dsimp only at hi hli ⊢; rw [htrl_get i hi] at hli ⊢; by_cases hie : i = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hli ⊢; rw [hlvl_get v (by omega)] at hli
        simp only [↓reduceIte] at hli; exact hl0 hli
      · have hilt : i < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte] at hli ⊢
        rw [hlvl_get _ (hlt_w i hilt), ite_eq_right (hnot_var i hilt)] at hli
        exact hw.level0_sound i hilt hli
    trail_pos_inv := fun i hi => by
      dsimp only at hi ⊢; rw [htrl_get i hi]; by_cases hie : i = s.core.trail_end
      · subst hie; simp only [↓reduceIte]
        rw [List.getElem?_set_self (by rw [hcl.trail_pos_len]; exact hv_lt),
          Option.getD_some, bv32_ofNat_toNat hte_lt32]
      · have hilt : i < s.core.trail_end := by omega
        simp only [hie, ↓reduceIte, List.getElem?_set_ne (Ne.symm (hnot_var i hilt))]
        exact hw.trail_pos_inv i hilt
    level0_rsn_none := fun idx hidx hli => by
      dsimp only at hidx hli ⊢; rw [htrl_get idx hidx] at hli ⊢
      by_cases hie : idx = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hli ⊢; rw [hlvl_get v (by omega)] at hli
        simp only [↓reduceIte] at hli; rw [hrsn_get v (by omega)]; simp [rsn', hli]
      · have hilt : idx < s.core.trail_end := by omega
        have hnv := hnot_var idx hilt
        simp only [hie, ↓reduceIte] at hli ⊢
        rw [hlvl_get _ (hlt_w idx hilt), ite_eq_right hnv] at hli
        rw [hrsn_get _ (hlt_w idx hilt), ite_eq_right hnv]; exact hw.level0_rsn_none idx hilt hli
    frame_trail_lt := fun L hL => Nat.le_trans (hw.frame_trail_lt L hL) (Nat.le_succ _)
    frame_trail_mono := hw.frame_trail_mono
    frame_trail_before_lt := fun L hL1 hLle i hi => by
      dsimp only at hL1 hLle hi ⊢
      have hi_le : i < s.core.trail_end := Nat.lt_of_lt_of_le hi (hw.frame_trail_lt L hLle)
      rw [htrl_get i (by omega), ite_eq_right (by omega), hlvl_get _ (hlt_w i hi_le),
        ite_eq_right (hnot_var i hi_le)]
      exact hw.frame_trail_before_lt L hL1 hLle i hi
    frame_dec_lt := hw.frame_dec_lt
    reason_inv := fun idx hidx hne => by
      dsimp only at hidx hne ⊢; rw [htrl_get idx hidx] at hne ⊢
      by_cases hie : idx = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hne ⊢; rw [hrsn_get v (by omega)] at hne ⊢
        simp only [↓reduceIte] at hne ⊢; by_cases hal0 : alvl = 0
        · simp [rsn', hal0] at hne
        · have hrs := hrsn (Nat.zero_lt_of_ne_zero hal0)
          simp only [rsn', hal0, ↓reduceIte] at hne hrs ⊢
          have hkv : (k'.lvl[lit.toNat / 2]?.getD 0#32).toNat = alvl := by
            change (k'.lvl[v]?.getD 0#32).toNat = alvl
            rw [hlvl_get v (by omega), ite_eq_left rfl]
          rw [ite_eq_left hjr_hi]
          exact hlift_rsn (Nat.le_refl _) hjr_hi (Nat.div_lt_of_lt_mul hlit) hkv hrs
      · have hilt : idx < s.core.trail_end := by omega
        have hnv := hnot_var idx hilt
        simp only [hie, ↓reduceIte] at hne ⊢
        rw [hrsn_get _ (hlt_w idx hilt), ite_eq_right hnv] at hne ⊢
        have hrs := hw.reason_inv idx hilt hne
        by_cases hlg : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32
        · rw [ite_eq_right (fun h => h hlg)] at hrs ⊢
          refine ⟨hrs.1, hrs.2.1, fun q hq => ?_⟩
          exact (hrs.2.2 q
            (by simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore] using hq)).elim
            Or.inl fun ⟨m, hm, hmeq, hmlv⟩ => Or.inr ⟨m, by omega,
              by rw [htrl_get m (by omega)]; simp [show m ≠ s.core.trail_end by omega, hmeq], by
                have hm' : m < s.core.trail_end := Nat.lt_of_lt_of_le hm (by omega)
                have hq_lt := hw.arena.lits_lt _ hrs.1 hrs.2.1 q
                  (by simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore] using hq)
                have hqv : q / 2 ≠ v := fun heqv => by
                  have hme := hnot_var m hm'; rw [hmeq] at hme
                  exact hme (by simpa [fullInv_var_xor1] using heqv)
                rw [hlvl_get _ (hlt_w idx hilt), hlvl_get _ (by omega),
                  ite_eq_right hnv, ite_eq_right hqv]; exact hmlv⟩
        · rw [ite_eq_left hlg] at hrs ⊢
          exact hlift_rsn (by omega) hlg (hlt_w idx hilt)
            (by rw [hlvl_get _ (hlt_w idx hilt), ite_eq_right hnv]) hrs
    reason_lit_mem := fun idx hidx hne hlg => by
      dsimp only at hidx hne hlg ⊢; rw [htrl_get idx hidx] at hne hlg ⊢
      by_cases hie : idx = s.core.trail_end
      · simp only [hie, ↓reduceIte] at hne hlg ⊢; rw [hrsn_get v (by omega)] at hne hlg ⊢
        simp only [↓reduceIte] at hne hlg ⊢; by_cases hal0 : alvl = 0
        · simp [rsn', hal0] at hne
        · simp [rsn', hal0] at hlg; exact absurd hlg hjr_hi
      · have hilt : idx < s.core.trail_end := by omega
        have hnv := hnot_var idx hilt
        simp only [hie, ↓reduceIte] at hne hlg ⊢
        rw [hrsn_get _ (hlt_w idx hilt), ite_eq_right hnv] at hne hlg ⊢
        simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore] using
          hw.reason_lit_mem idx hilt hne hlg }

private theorem s13_oneLit_bin_assign_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut1 clvl jlvl : Nat} {s s1 s2 : FullState}
    {forced other : BitVec 32} {jlvlv nlvl : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m2 : Mem 64}
    (hAss : ∀ args m Q X, Full.fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    (hobt : M5OneLitBtInv c F0 F_cur s s1 cut1 clvl)
    (hjv_eq : jlvlv.toNat = jlvl) (hj_lt32 : jlvl < 2 ^ 32)
    (hjlvl_le : jlvl ≤ nlvl.toNat) (hnlvl_lt : nlvl.toNat < clvl)
    (hforced_lt : forced.toNat < 2 * s1.core.cur_vars)
    (hother_lt : other.toNat < 2 * s1.core.cur_vars)
    (hforced_lvl : (s1.core.lvl[forced.toNat / 2]?.getD 0#32).toNat = clvl)
    (hother_lvl : (s1.core.lvl[other.toNat / 2]?.getD 0#32).toNat = jlvl)
    (hother_f : s1.core.vals[other.toNat]?.getD 0#8 = 0xFF#8)
    (hent_fo : (cnfOfClauses F_cur).EntailsClause (cnfClause [forced.toNat, other.toNat]))
    (hs2_len : s2.LengthsOk c) (hs2_cl : s2.core.cur_level = nlvl.toNat)
    (hs2_fu : s2.core.fuel = s1.core.fuel) (hs2_ws2 : s2.scratch.work_stk2 = s1.scratch.work_stk2)
    (hs2_ll : s2.scratch.last_learned = s1.scratch.last_learned)
    (hs2_el : s2.scratch.extend_len = s1.scratch.extend_len)
    (hs2_dm : s2.core.dense_mode = 0#64) (hs2_pr : s2.core.probing = s1.core.probing)
    (hs2_cv : s2.core.cur_vars = s1.core.cur_vars)
    (hs2_mk : s2.core.mrk = s1.core.mrk) (hs2_lm : s2.core.lit_mark = s1.core.lit_mark)
    (hs2_ar : s2.core.arena = s1.core.arena) (hs2_al : s2.core.arena_len = s1.core.arena_len)
    (hs2_vals : ∀ l < 2 * s1.core.cur_vars, s2.core.vals[l]?.getD 0#8 =
      if (s1.core.lvl[l / 2]?.getD 0#32).toNat ≤ nlvl.toNat then s1.core.vals[l]?.getD 0#8 else 0#8)
    (hs2_lvl : ∀ i < s1.core.trail_end, let v := (s1.core.trl[i]?.getD 0#32).toNat / 2
      s2.core.lvl[v]?.getD 0#32 =
        if (s1.core.lvl[v]?.getD 0#32).toNat ≤ nlvl.toNat then s1.core.lvl[v]?.getD 0#32 else 0#32)
    (hw2 : Full.FullWitnessInv c F0 F_cur s2.core) (hm2 : (FullMem c s2 ⋆ R) m2)
    (hQ : M5OneLitPost c F0 F_cur s R Q) :
    wp Γ Q X
      (Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                   args := (Arg.var other, Arg.imm 2147483647#32, ()) } fun p26 =>
       Expr.let_ { sig := [i32, i32], code := OpCode.or i32,
                   args := (Arg.var p26.fst, Arg.imm 2147483648#32, ()) } fun p27 =>
       Expr.group (sig := [[i32]]) (fun _Jol => Blocks.cons (fun (jr_ol : Tup Val [i32]) =>
         Expr.let_ { sig := [i64], code := OpCode.trunc 64 32, args := (Arg.var jlvlv, ()) }
           fun p28 =>
         Expr.call (as := [i64, i32, i32, i32]) "full_assign_lvl"
           (Arg.var c.hdr, Arg.var forced, Arg.var jr_ol.fst, Arg.var p28.fst, ())
           fun (_ : Tup Val []) => Expr.ret (Arg.imm 1#64, ())) Blocks.nil) fun Jol =>
       Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
                   args := (Arg.var jlvlv, Arg.imm 0#64, ()) } fun p29 =>
       Expr.jnz (Arg.var p29.fst)
         (Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var c.hdr, Arg.imm 88#64, ()) } fun p30 =>
          Expr.load i64 (Arg.var p30.fst) fun rsns_ol =>
          Expr.let_ { sig := [i32, i32], code := OpCode.lshr i32,
                      args := (Arg.var other, Arg.imm 1#32, ()) } fun p31 =>
          Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p31.fst, ()) }
            fun p32 =>
          Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                      args := (Arg.var p32.fst, Arg.imm 4#64, ()) } fun p33 =>
          Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var rsns_ol, Arg.var p33.fst, ()) } fun p34 =>
          Expr.load i32 (Arg.var p34.fst) fun nr_ol =>
          Expr.group (sig := [[i32]]) (fun _Js1 => Blocks.cons (fun (p : Tup Val [i32]) =>
            Expr.jump Jol.fst (Arg.var p.fst, ())) Blocks.nil) fun Js =>
          Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
                      args := (Arg.var nr_ol, Arg.imm 4294967295#32, ()) } fun p35 =>
          Expr.jnz (Arg.var p35.fst)
            (Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                         args := (Arg.var nr_ol, Arg.imm 2147483648#32, ()) } fun p36 =>
             Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
                         args := (Arg.var p36.fst, Arg.imm 0#32, ()) } fun p37 =>
             Expr.jnz (Arg.var p37.fst)
               (Expr.jump Js.fst (Arg.var nr_ol, ()))
               (Expr.jump Js.fst (Arg.var p27.fst, ())))
            (Expr.jump Js.fst (Arg.var p27.fst, ())))
         (Expr.jump Jol.fst (Arg.var p27.fst, ()))) m2 := by
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv2 := hs2_len.core_ok.cur_vars_le
  have h2cv2 : 2 * s2.core.cur_vars < 2 ^ 31 - 1 := by omega
  have hother_lt2 : other.toNat < 2 * s2.core.cur_vars := hs2_cv ▸ hother_lt
  have hforced_lt2 : forced.toNat < 2 * s2.core.cur_vars := hs2_cv ▸ hforced_lt
  have hf_un : s2.core.vals[forced.toNat]?.getD 0#8 = 0#8 := by
    rw [hs2_vals _ hforced_lt, ite_eq_right (by omega)]
  have hother_f2 : s2.core.vals[other.toNat]?.getD 0#8 = 0xFF#8 := by
    rw [hs2_vals _ hother_lt, ite_eq_left (by omega)]; exact hother_f
  have hother_lvl2 : (s2.core.lvl[other.toNat / 2]?.getD 0#32).toNat = jlvl := by
    obtain ⟨m0, hm0, hm0_eq⟩ := (hobt.hw1.vals_false_iff other.toNat hother_lt).mp hother_f
    have hlv := hs2_lvl m0 hm0; dsimp only at hlv; rw [hm0_eq, fullInv_var_xor1] at hlv
    rw [hother_lvl, ite_eq_left hjlvl_le] at hlv
    have : (s2.core.lvl[other.toNat / 2]?.getD 0#32).toNat =
        (s1.core.lvl[other.toNat / 2]?.getD 0#32).toNat := congrArg BitVec.toNat hlv
    omega
  have htr_eq : jlvlv.setWidth 32 = BitVec.ofNat 32 jlvl := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_setWidth, hjv_eq, bv32_ofNat_toNat hj_lt32, Nat.mod_eq_of_lt hj_lt32])
  have hj_z : (jlvlv.setWidth 32 = 0#32) ↔ jlvl = 0 := by
    rw [htr_eq]; constructor
    · intro h; simpa [bv32_ofNat_toNat hj_lt32] using congrArg BitVec.toNat h
    · intro h; simp [h]
  have hng_guard : ¬ (s2.core.cur_vars ≤ forced.toNat / 2 ∨
      c.max_vars ≤ s2.core.trail_end ∨ s2.core.vals[forced.toNat]?.getD 0#8 ≠ 0#8) := by
    have hte2_lt := hw2.trail_end_lt_of_unassigned hforced_lt2 hf_un
    exact not_or.mpr ⟨Nat.not_le.mpr (Nat.div_lt_of_lt_mul hforced_lt2), not_or.mpr
      ⟨Nat.not_le.mpr (by omega), fun h => h hf_un⟩⟩
  let jr0 := (other &&& 0x7FFFFFFF#32) ||| 0x80000000#32
  have hbin_p := FullAnalyzeTactics.bin_rsn_mask_props (l := other) (by omega)
  c0_to_group
  refine wp_join_group (ts := [i32]) (fun (jr, ()) m_j =>
    m_j = m2 ∧ jr ≠ 0xFFFFFFFF#32 ∧ (jr &&& 0x80000000#32) ≠ 0#32 ∧
    let ot := (jr &&& 0x7FFFFFFF#32).toNat
    ot < 2 * s2.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [forced.toNat, ot]) ∧
    s2.core.vals[ot]?.getD 0#8 = 0xFF#8 ∧ (s2.core.lvl[ot / 2]?.getD 0#32).toNat ≤ jlvl) ?_ ?_
  · rintro _ ⟨jr, ⟨⟩⟩ m_j ⟨rfl, hjr_ne, hjr_hi, hot_lt, hent_j, hot_f, hot_lvl⟩
    fa_fast_steps_nogrp
    c0_call hAss
    refine ⟨c, s2, R, rfl, hs2_len, hm2, ?_⟩
    simp only [hng_guard, ↓reduceIte]
    intro fl' unass3 ph' m3 hfl3 hph3 hm3
    let v := forced.toNat / 2
    let rsn' := if jlvl = 0 then 0xFFFFFFFF#32 else jr
    let s3 : FullState :=
      { s2 with
        core :=
          { s2.core with
            vals := (s2.core.vals.set forced.toNat 1#8).set (forced.toNat ^^^ 1) 0xFF#8
            flags := fl', lvl := s2.core.lvl.set v (BitVec.ofNat 32 jlvl)
            rsns := s2.core.rsns.set v rsn', trl := s2.core.trl.set s2.core.trail_end forced
            trail_pos := s2.core.trail_pos.set v (BitVec.ofNat 32 s2.core.trail_end)
            trail_end := s2.core.trail_end + 1, unassigned := unass3
            unflushed := if jlvlv.setWidth 32 = 0#32
              then s2.core.unflushed + 1#64 else s2.core.unflushed }
        scratch := { s2.scratch with phases := ph' } }
    have hlen3 : s3.LengthsOk c :=
      ⟨{ hs2_len.core_ok with
          vals_len := by simp [s3, hs2_len.core_ok.vals_len], flags_len := hfl3,
          lvl_len := by simp [s3, hs2_len.core_ok.lvl_len],
          rsns_len := by simp [s3, hs2_len.core_ok.rsns_len],
          trl_len := by simp [s3, hs2_len.core_ok.trl_len],
          trail_pos_len := by simp [s3, hs2_len.core_ok.trail_pos_len],
          trail_end_le := by
            have := hw2.trail_end_lt_of_unassigned hforced_lt2 hf_un; dsimp [s3]; omega,
          propagated_le := Nat.le_trans hs2_len.core_ok.propagated_le (Nat.le_succ _) },
       { hs2_len.scratch_ok with phases_len := by dsimp [s3]; exact hph3 }⟩
    have hmarks3 : Full.FullLitMarksClear c s3 :=
      ⟨fun w hw => by change s2.core.mrk[w]?.getD 0#8 = 0#8; rw [hs2_mk]; exact hobt.marks1.1 w hw,
       fun l hl => by
         change s2.core.lit_mark[l]?.getD 0#8 = 0#8; rw [hs2_lm]; exact hobt.marks1.2 l hl⟩
    have hrefs : fullArenaClauseRefsCore s3.core = fullArenaClauseRefsCore s1.core := by
      simp [fullArenaClauseRefsCore, s3, hs2_ar, hs2_al]
    have hnd3 : Full.FullArenaVarsNodup s3 := fun r hr hng => by
      change r ∈ fullArenaClauseRefsCore s3.core at hr; rw [hrefs] at hr
      change ((fullArenaClauseLitsCore s3.core r).map (· / 2)).Nodup
      simp only [fullArenaClauseLitsCore, fullArenaClauseSizeCore, s3, hs2_ar]
      exact hobt.nodup1 r hr
        (by simpa [fullArenaClauseGarbCore, fullArenaHdrCore, s3, hs2_ar] using hng)
    have hext3 : Full.FullExtScratchOk c s3 :=
      ⟨fun i hi => by
        change _ = _ ∨ _ ∈ fullArenaClauseRefsCore s3.core
        rw [hrefs, hs2_ll]; exact hobt.ext1.1 i hi,
       by change s2.scratch.extend_len ≤ c.extend_cap; rw [hs2_el]; exact hobt.ext1.2⟩
    have h_s2_false : ∃ m_ot < s2.core.trail_end,
        (s2.core.trl[m_ot]?.getD 0#32).toNat = (jr &&& 0x7FFFFFFF#32).toNat ^^^ 1 ∧
        (s2.core.lvl[(jr &&& 0x7FFFFFFF#32).toNat / 2]?.getD 0#32).toNat ≤ jlvl := by
      obtain ⟨m_ot, hm_ot, hmeq⟩ := (hw2.vals_false_iff _ hot_lt).mp hot_f
      exact ⟨m_ot, hm_ot, hmeq, hot_lvl⟩
    have hl0 : jlvl = 0 → (cnfOfClauses F_cur).EntailsClause (cnfClause [forced.toNat]) := by
      intro hj0; subst hj0
      obtain ⟨m_ot, hm_ot, hmeq, hml0⟩ := h_s2_false
      have htr0 : (s2.core.lvl[(s2.core.trl[m_ot]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
        rw [hmeq, fullInv_var_xor1]; omega
      exact entails_of_mem_or_false hent_j fun l hl => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        exact hl.elim (fun h => h ▸ Or.inl List.mem_cons_self) fun h =>
          Or.inr (h ▸ by have hs := hw2.level0_sound m_ot hm_ot htr0; rwa [hmeq] at hs)
    have hrsn2 : 0 < jlvl →
        let ot := (jr &&& 0x7FFFFFFF#32).toNat
        ot < 2 * s2.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause
          (cnfClause [forced.toNat, ot]) ∧
        ∃ m < s2.core.trail_end, (s2.core.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
          (s2.core.lvl[ot / 2]?.getD 0#32).toNat ≤ jlvl := fun _ =>
      ⟨hot_lt, hent_j, h_s2_false⟩
    have hw3 := s13_chronoAssign_bin_preserves_fullWitness hs2_len hw2 hforced_lt2 hf_un
      (hs2_cl ▸ hjlvl_le) hjr_ne hjr_hi hl0 hrsn2 (flags' := fl')
      (unassigned' := unass3) (unflushed' := s3.core.unflushed)
    have hrsn_eq : (if jlvlv.setWidth 32 = 0#32 then 0xFFFFFFFF#32 else jr) = rsn' := by
      by_cases hj : jlvl = 0
      · rw [ite_eq_left (hj_z.mpr hj)]; simp [rsn', hj]
      · rw [ite_eq_right (fun h => hj (hj_z.mp h))]; simp [rsn', hj]
    fa_fast_steps
    exact hQ 1#64 s3 m3 hlen3 (Or.inr (Or.inl rfl)) (hs2_cv.trans hobt.cv_eq)
      (hs2_fu.trans hobt.fuel_eq) (hs2_ws2.trans hobt.ws2_eq) hs2_dm
      (hs2_pr.trans hobt.prob_eq) hmarks3 hnd3 hext3 (fun _ h => by cases h)
      (fun h => by cases h) (fun _ => ⟨hw3, by dsimp [s3]; have := hobt.cl_le; omega⟩)
      (fun h => by cases h) (fun h => by cases h)
      (m5_fullMem_of_eq hm3 (by dsimp only [s3, rsn', v]; rw [hrsn_eq, htr_eq]) rfl)
  · intro Jol hJol
    have hjr0_ok : jr0 ≠ 0xFFFFFFFF#32 ∧ (jr0 &&& 0x80000000#32) ≠ 0#32 ∧
        (jr0 &&& 0x7FFFFFFF#32).toNat < 2 * s2.core.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause [forced.toNat, (jr0 &&& 0x7FFFFFFF#32).toNat]) ∧
        s2.core.vals[(jr0 &&& 0x7FFFFFFF#32).toNat]?.getD 0#8 = 0xFF#8 ∧
        (s2.core.lvl[(jr0 &&& 0x7FFFFFFF#32).toNat / 2]?.getD 0#32).toNat ≤ jlvl := by
      refine ⟨hbin_p.1, hbin_p.2.1, ?_⟩
      rw [hbin_p.2.2]
      exact ⟨hother_lt2, hent_fo, hother_f2, Nat.le_of_eq hother_lvl2⟩
    c0_hsplit
    · have hjpos : 0 < jlvl := by
        have hlt : 0 < jlvlv.toNat := by assumption
        omega
      have hv_lt : other.toNat / 2 < c.max_vars := by omega
      have hidx_o : ((other >>> 1#32).setWidth 64).toNat = other.toNat / 2 := by
        rw [bv_c0_zext32_64]; simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      have hbd_rsns : ((other >>> 1#32).setWidth 64).toNat < s2.core.rsns.length := by
        rw [hidx_o, hs2_len.core_ok.rsns_len]; exact hv_lt
      c0_hsteps_nogrp
      refine wp_load_of (FullArenaTactics.load_full_reason_ptr hm2) ?_
      c0_hsteps_nogrp
      refine wp_load_of (FullArenaTactics.c0_load_full_rsns hbd_rsns hm2) ?_
      let nr_ol := s2.core.rsns[((other >>> 1#32).setWidth 64).toNat]'hbd_rsns
      c0_to_group
      refine wp_join_group (ts := [i32]) (fun (jr2, ()) m_j2 =>
        m_j2 = m2 ∧ jr2 ≠ 0xFFFFFFFF#32 ∧ (jr2 &&& 0x80000000#32) ≠ 0#32 ∧
        let ot := (jr2 &&& 0x7FFFFFFF#32).toNat
        ot < 2 * s2.core.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [forced.toNat, ot]) ∧
        s2.core.vals[ot]?.getD 0#8 = 0xFF#8 ∧ (s2.core.lvl[ot / 2]?.getD 0#32).toNat ≤ jlvl) ?_ ?_
      · rintro _ ⟨jr2, ⟨⟩⟩ m_j2 hok
        fa_fast_steps
        exact hJol (jr2, ()) m_j2 hok
      · intro Js hJs
        c0_hsplit
        · c0_hsplit
          · have hnr_ne : nr_ol ≠ 0xFFFFFFFF#32 := by assumption
            have hnr_hi : (nr_ol &&& 0x80000000#32) ≠ 0#32 := by assumption
            obtain ⟨m_o, hm_o, hm_oeq⟩ := (hw2.vals_false_iff other.toNat hother_lt2).mp hother_f2
            have hvar_o : (s2.core.trl[m_o]?.getD 0#32).toNat / 2 = other.toNat / 2 := by
              rw [hm_oeq, fullInv_var_xor1]
            have hrsn_get : s2.core.rsns[(s2.core.trl[m_o]?.getD 0#32).toNat / 2]?.getD
                0xFFFFFFFF#32 = nr_ol := by
              rw [hvar_o, List.getElem?_eq_getElem (by rw [hs2_len.core_ok.rsns_len]; exact hv_lt),
                Option.getD_some]
              exact Option.some.inj (by
                rw [← List.getElem?_eq_getElem (by rw [hs2_len.core_ok.rsns_len]; exact hv_lt),
                    ← List.getElem?_eq_getElem hbd_rsns, hidx_o])
            have hinv_r := hw2.reason_inv m_o hm_o (by rw [hrsn_get]; exact hnr_ne)
            rw [hrsn_get, ite_eq_left (fun h => absurd h hnr_hi)] at hinv_r
            obtain ⟨hot_lt, hent_ot, m_t, hm_t, hmt_eq, hot_lv⟩ := hinv_r
            have hot_f : s2.core.vals[(nr_ol &&& 0x7FFFFFFF#32).toNat]?.getD 0#8 = 0xFF#8 :=
              (hw2.vals_false_iff _ hot_lt).mpr ⟨m_t, Nat.lt_trans hm_t hm_o, hmt_eq⟩
            have hent_neg_other : (cnfOfClauses F_cur).EntailsClause
                (cnfClause [other.toNat ^^^ 1, (nr_ol &&& 0x7FFFFFFF#32).toNat]) := by
              rwa [← hm_oeq]
            have hent_res := s13_bin_resolve hent_neg_other
              (entails_of_mem_or_false hent_fo fun l hl =>
              Or.inl (by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
                rcases hl with rfl | rfl
                · exact Or.inr rfl
                · exact Or.inl rfl))
            fa_fast_steps
            exact hJs (nr_ol, ()) m2 ⟨rfl, hnr_ne, hnr_hi, hot_lt, hent_res, hot_f,
              by rw [← hother_lvl2, ← hvar_o]; exact hot_lv⟩
          · fa_fast_steps; exact hJs (jr0, ()) m2 ⟨rfl, hjr0_ok⟩
        · fa_fast_steps; exact hJs (jr0, ()) m2 ⟨rfl, hjr0_ok⟩
    · fa_fast_steps; exact hJol (jr0, ()) m2 ⟨rfl, hjr0_ok⟩

private theorem s13_oneLit_bin_swap_if {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut1 clvl : Nat} {s s1 : FullState} {a b la lb : BitVec 32}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m1 : Mem 64}
    (hBt : ∀ args m Q X, Full.fullBacktrackSpec args m Q X →
      Γ "full_backtrack_ac_fid" [i64, i64] [] args m Q X)
    (hAss : ∀ args m Q X, Full.fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    (hobt : M5OneLitBtInv c F0 F_cur s s1 cut1 clvl)
    (ha_lt : a.toNat < 2 * s.core.cur_vars) (hb_lt : b.toNat < 2 * s.core.cur_vars)
    (hla_val : la.toNat = (s.core.lvl[a.toNat / 2]?.getD 0#32).toNat)
    (hlb_val : lb.toNat = (s.core.lvl[b.toNat / 2]?.getD 0#32).toNat)
    (hmax : clvl = max la.toNat lb.toNat) (hne : la ≠ lb)
    (hfa : s.core.vals[a.toNat]?.getD 0#8 = 0xFF#8)
    (hfb : s.core.vals[b.toNat]?.getD 0#8 = 0xFF#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat]))
    (hm1 : (FullMem c s1 ⋆ R) m1) (hQ : M5OneLitPost c F0 F_cur s R Q) :
    let forced := if la > lb then a else b
    let other := if la > lb then b else a
    let jlvl : Nat := if la > lb then lb.toNat else la.toNat
    ∀ nlvl : BitVec 64,
      (0 < s1.core.cur_level → jlvl < s1.core.cur_level →
        jlvl ≤ nlvl.toNat ∧ nlvl.toNat < s1.core.cur_level) →
      wp Γ Q X
        (Expr.call (as := [i64, i64]) "full_backtrack_ac_fid"
            (Arg.var c.hdr, Arg.var nlvl, ()) fun (_ : Tup Val []) =>
          Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                      args := (Arg.var other, Arg.imm 2147483647#32, ()) } fun p26 =>
          Expr.let_ { sig := [i32, i32], code := OpCode.or i32,
                      args := (Arg.var p26.fst, Arg.imm 2147483648#32, ()) } fun p27 =>
          Expr.group (sig := [[i32]]) (fun _Jol => Blocks.cons (fun (jr_ol : Tup Val [i32]) =>
            Expr.let_ { sig := [i64], code := OpCode.trunc 64 32,
                        args := (Arg.var (BitVec.ofNat 64 jlvl), ()) } fun p28 =>
            Expr.call (as := [i64, i32, i32, i32]) "full_assign_lvl"
              (Arg.var c.hdr, Arg.var forced, Arg.var jr_ol.fst, Arg.var p28.fst, ())
              fun (_ : Tup Val []) => Expr.ret (Arg.imm 1#64, ())) Blocks.nil) fun Jol =>
          Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
                      args := (Arg.var (BitVec.ofNat 64 jlvl), Arg.imm 0#64, ()) } fun p29 =>
          Expr.jnz (Arg.var p29.fst)
            (Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var c.hdr, Arg.imm 88#64, ()) } fun p30 =>
             Expr.load i64 (Arg.var p30.fst) fun rsns_ol =>
             Expr.let_ { sig := [i32, i32], code := OpCode.lshr i32,
                         args := (Arg.var other, Arg.imm 1#32, ()) } fun p31 =>
             Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p31.fst, ()) }
               fun p32 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                         args := (Arg.var p32.fst, Arg.imm 4#64, ()) } fun p33 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var rsns_ol, Arg.var p33.fst, ()) } fun p34 =>
             Expr.load i32 (Arg.var p34.fst) fun nr_ol =>
             Expr.group (sig := [[i32]]) (fun _Js1 => Blocks.cons (fun (p : Tup Val [i32]) =>
               Expr.jump Jol.fst (Arg.var p.fst, ())) Blocks.nil) fun Js =>
             Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
                         args := (Arg.var nr_ol, Arg.imm 4294967295#32, ()) } fun p35 =>
             Expr.jnz (Arg.var p35.fst)
               (Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                            args := (Arg.var nr_ol, Arg.imm 2147483648#32, ()) } fun p36 =>
                Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
                            args := (Arg.var p36.fst, Arg.imm 0#32, ()) } fun p37 =>
                Expr.jnz (Arg.var p37.fst)
                  (Expr.jump Js.fst (Arg.var nr_ol, ()))
                  (Expr.jump Js.fst (Arg.var p27.fst, ())))
               (Expr.jump Js.fst (Arg.var p27.fst, ())))
            (Expr.jump Jol.fst (Arg.var p27.fst, ()))) m1 := by
  intro forced other jlvl nlvl hnlvl
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv; have hcv := hobt.len1.core_ok.cur_vars_le
  have h2cv : 2 * s.core.cur_vars < 2 ^ 31 - 1 := by have := hobt.cv_eq; omega
  have hjlt : jlvl < clvl := by
    dsimp only [jlvl]; split <;> rename_i hgt
    · have : lb.toNat < la.toNat := hgt; omega
    · have : la.toNat ≤ lb.toNat := Nat.not_lt.mp hgt
      have hneq : la.toNat ≠ lb.toNat := fun he => hne (BitVec.eq_of_toNat_eq he); omega
  obtain ⟨hjl_le_nl, hnl_lt⟩ := hnlvl (hobt.cl1_eq ▸ hobt.cl_pos) (hobt.cl1_eq ▸ hjlt)
  rw [hobt.cl1_eq] at hnl_lt
  c0_call hBt
  refine ⟨c, s1, R, rfl, hobt.len1, by
    have := hobt.hw1.cur_level_le; have := hobt.len1.core_ok.trail_end_le; omega,
    fun _ => by
      have := hobt.hw1.cur_level_le; have := hobt.len1.core_ok.trail_end_le; omega,
    hobt.hw1.trail_lits_lt, hm1, ?_⟩
  dsimp only
  intro vals2 lvl2 rsns2 trl2 tp2 te2 prop2 cl2 unass2 sc2 m2 hlen2 _ _ hcl2 hpres _ _ hvl2 _ hw2
    hm2
  have hcl2_eq : cl2 = nlvl.toNat := by rw [hcl2, hobt.cl1_eq]; omega
  have hw2' := hw2 F0 F_cur hobt.hw1.toFullOtfsWitnessInv (by rw [hobt.cl1_eq]; exact hnl_lt)
  obtain ⟨hvals2, hlvl2⟩ := hvl2 ⟨F0, F_cur, Or.inr hobt.hw1.toFullOtfsWitnessInv⟩
  have hforced_lt : forced.toNat < 2 * s1.core.cur_vars := by
    rw [hobt.cv_eq]; dsimp only [forced]; split <;> assumption
  have hother_lt : other.toNat < 2 * s1.core.cur_vars := by
    rw [hobt.cv_eq]; dsimp only [other]; split <;> assumption
  have hforced_lvl : (s1.core.lvl[forced.toNat / 2]?.getD 0#32).toNat = clvl := by
    dsimp only [forced]; split
    · have : lb.toNat < la.toNat := ‹la > lb›
      rw [hobt.lvl_keep _ ha_lt hfa (by omega), ← hla_val]; omega
    · have : la.toNat ≤ lb.toNat := Nat.not_lt.mp ‹¬ la > lb›
      rw [hobt.lvl_keep _ hb_lt hfb (by omega), ← hlb_val]; omega
  have hother_lvl : (s1.core.lvl[other.toNat / 2]?.getD 0#32).toNat = jlvl := by
    dsimp only [other, jlvl]; split
    · rw [hobt.lvl_keep _ hb_lt hfb (by rw [← hlb_val]; omega), hlb_val]
    · rw [hobt.lvl_keep _ ha_lt hfa (by rw [← hla_val]; omega), hla_val]
  have hother_f : s1.core.vals[other.toNat]?.getD 0#8 = 0xFF#8 := by
    dsimp only [other]; split
    · rw [hobt.vals_keep _ hb_lt (by rw [← hlb_val]; omega)]; exact hfb
    · rw [hobt.vals_keep _ ha_lt (by rw [← hla_val]; omega)]; exact hfa
  have hent_fo : (cnfOfClauses F_cur).EntailsClause (cnfClause [forced.toNat, other.toNat]) := by
    dsimp only [forced, other]; split
    · exact hent
    · exact entails_of_mem_or_false hent fun l hl => Or.inl (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
        rcases hl with rfl | rfl <;> simp)
  have hj_lt32 : jlvl < 2 ^ 32 := by
    have := Full.fullInv_max_vars_lt32 c; have := hobt.hw1.cur_level_le
    have := hobt.len1.core_ok.trail_end_le; have := hobt.cl1_eq; omega
  exact s13_oneLit_bin_assign_wp hAss hobt (bv64_ofNat_toNat (lt_trans hj_lt32 (by decide)))
    hj_lt32 hjl_le_nl hnl_lt hforced_lt hother_lt hforced_lvl hother_lvl hother_f hent_fo
    hlen2 hcl2_eq rfl hpres.2.2.1 hpres.1.1 hpres.1.2 hobt.dm0 rfl rfl rfl rfl rfl rfl
    hvals2 hlvl2 hw2' hm2 hQ

private theorem s13_oneLit_bin_branch_wp (Γ : Env)
    (hDet : ∀ args m Q X, Full.fullDetNewLevelSpec args m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] args m Q X)
    (hBt : ∀ args m Q X, Full.fullBacktrackSpec args m Q X →
      Γ "full_backtrack_ac_fid" [i64, i64] [] args m Q X)
    (hAss : ∀ args m Q X, Full.fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat} {s : FullState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m : Mem 64}
    (hlen : s.LengthsOk c) (hdm : s.core.dense_mode = 0#64)
    (hw : Full.FullWitnessCutInv c F0 F_cur cut s.core) (hmarks : Full.FullLitMarksClear c s)
    (hnd : Full.FullArenaVarsNodup s) (hext : Full.FullExtScratchOk c s)
    (hconfl : Full.FullConflictOkCut F_cur cut s)
    (hbin : s.core.confl_type = 1#64) (hm : (FullMem c s ⋆ R) m)
    (hQ : M5OneLitPost c F0 F_cur s R Q) :
    Func.wp Γ full_one_lit_confl_body (c.hdr, ()) m Q X := by
  have hmax32 := Full.fullInv_max_vars_lt32 c; have hcv_le := hlen.core_ok.cur_vars_le
  have hlvl_len := hlen.core_ok.lvl_len; have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcl_lt64 : s.core.cur_level < 2 ^ 64 := by
    have := hw.cur_level_le; have := hlen.core_ok.trail_end_le; omega
  have hret_bt0 {cut1 clvl : Nat} {s1 : FullState} {m1 : Mem 64}
      (hobt : M5OneLitBtInv c F0 F_cur s s1 cut1 clvl)
      (hm1 : (FullMem c s1 ⋆ R) m1) : Q (0#64, ()) m1 :=
    hQ 0#64 s1 m1 hobt.len1 (Or.inl rfl) hobt.cv_eq hobt.fuel_eq hobt.ws2_eq hobt.dm0 hobt.prob_eq
      hobt.marks1 hobt.nodup1 hobt.ext1 (fun _ h => by cases h) (fun h => by cases h)
      (fun h => by cases h) (fun h => by cases h)
      (fun _ => ⟨cut1, hobt.cut1_le, hobt.hw1, hobt.cl1_eq ▸ hobt.cl_pos,
        hobt.cl1_eq ▸ hobt.cl_le, hobt.confl1⟩) hm1
  have hconfl0 : Full.FullConflictOkCut F_cur cut s := hconfl
  have hbin_cf : s.core.confl_lit0.toNat < 2 * s.core.cur_vars ∧
      s.core.confl_lit1.toNat < 2 * s.core.cur_vars ∧
      s.core.vals[s.core.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
      s.core.vals[s.core.confl_lit1.toNat]?.getD 0#8 = 0xFF#8 ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [s.core.confl_lit0.toNat, s.core.confl_lit1.toNat]) := by
    rcases hconfl.1 with ⟨_, h0, h1, fa, fb, he⟩ | ⟨hbad, _⟩
    · exact ⟨h0, h1, fa, fb, he⟩
    · exact absurd (hbin.symm.trans hbad) (by decide)
  obtain ⟨h0lt, h1lt, hfa, hfb, hent⟩ := hbin_cf
  dsimp only [Func.wp, full_one_lit_confl_body]
  c0_hsteps_nogrp
  c0_hsplit
  · have h0_32 : s.core.confl_lit0.toNat < 2 ^ 32 := by omega
    have h1_32 : s.core.confl_lit1.toNat < 2 ^ 32 := by omega
    let a := s.core.confl_lit0.setWidth 32; let b := s.core.confl_lit1.setWidth 32
    have ha_eq : a.toNat = s.core.confl_lit0.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h0_32]
    have hb_eq : b.toNat = s.core.confl_lit1.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h1_32]
    have ha_bd : (BitVec.setWidth 64 (a >>> 1)).toNat < s.core.lvl.length := by
      rw [bv_c0_zext32_64, bv32_lshr_1, hlvl_len, ha_eq]; omega
    have hb_bd : (BitVec.setWidth 64 (b >>> 1)).toNat < s.core.lvl.length := by
      rw [bv_c0_zext32_64, bv32_lshr_1, hlvl_len, hb_eq]; omega
    let la := s.core.lvl[(BitVec.setWidth 64 (a >>> 1)).toNat]'ha_bd
    let lb := s.core.lvl[(BitVec.setWidth 64 (b >>> 1)).toNat]'hb_bd
    have hla_64 : la.setWidth 64 = BitVec.ofNat 64 la.toNat := BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_setWidth, bv64_ofNat_toNat (by omega), Nat.mod_eq_of_lt (by omega)])
    have hlb_64 : lb.setWidth 64 = BitVec.ofNat 64 lb.toNat := BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_setWidth, bv64_ofNat_toNat (by omega), Nat.mod_eq_of_lt (by omega)])
    have hla_val : la.toNat = (s.core.lvl[a.toNat / 2]?.getD 0#32).toNat := by
      dsimp only [la]; rw [List.getElem?_eq_getElem (by rw [hlvl_len]; omega), Option.getD_some]
      have hidx : (BitVec.setWidth 64 (a >>> 1)).toNat = a.toNat / 2 := by
        rw [bv_c0_zext32_64, bv32_lshr_1]
      exact congrArg BitVec.toNat (Option.some.inj (by
        rw [← List.getElem?_eq_getElem ha_bd,
            ← List.getElem?_eq_getElem (by rw [hlvl_len]; omega), hidx]))
    have hlb_val : lb.toNat = (s.core.lvl[b.toNat / 2]?.getD 0#32).toNat := by
      dsimp only [lb]; rw [List.getElem?_eq_getElem (by rw [hlvl_len]; omega), Option.getD_some]
      have hidx : (BitVec.setWidth 64 (b >>> 1)).toNat = b.toNat / 2 := by
        rw [bv_c0_zext32_64, bv32_lshr_1]
      exact congrArg BitVec.toNat (Option.some.inj (by
        rw [← List.getElem?_eq_getElem hb_bd,
            ← List.getElem?_eq_getElem (by rw [hlvl_len]; omega), hidx]))
    have hla_le : la.toNat ≤ s.core.cur_level := by
      obtain ⟨ma, hma, hma_eq⟩ := (hw.vals_false_iff _ h0lt).mp hfa
      have h1 := hw.lvl_le ma hma; rw [hma_eq, fullInv_var_xor1, ← ha_eq] at h1; omega
    have hlb_le : lb.toNat ≤ s.core.cur_level := by
      obtain ⟨mb, hmb, hmb_eq⟩ := (hw.vals_false_iff _ h1lt).mp hfb
      have h1 := hw.lvl_le mb hmb; rw [hmb_eq, fullInv_var_xor1, ← hb_eq] at h1; omega
    fa_fast_steps_nogrp
    refine wp_join_group (ts := [i64]) (fun (clvlv, ()) m0 =>
        m0 = m ∧ clvlv = BitVec.ofNat 64 (max la.toNat lb.toNat)) ?_ ?_
    · rintro _ ⟨clvlv, ⟨⟩⟩ m0 ⟨rfl, rfl⟩
      let clvl := max la.toNat lb.toNat
      have hcl_le : clvl ≤ s.core.cur_level := Nat.max_le.mpr ⟨hla_le, hlb_le⟩
      fa_fast_steps_nogrp
      · have hcl0 : clvl = 0 := ofNat64_eq_zero (by omega) ‹_›
        have hl0a : (s.core.lvl[a.toNat / 2]?.getD 0#32).toNat = 0 := by omega
        have hl0b : (s.core.lvl[b.toNat / 2]?.getD 0#32).toNat = 0 := by omega
        exact hQ 20#64 s m0 hlen (Or.inr (Or.inr (Or.inr rfl))) rfl rfl rfl hdm rfl hmarks hnd
          hext (fun _ h => by cases h)
          (fun _ => ⟨unsat_of_level0_bin_conflict (m5_canonCut_to_anaCut hw) h0lt h1lt
            (ha_eq ▸ hl0a) (hb_eq ▸ hl0b) hfa hfb hent, rfl⟩)
          (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm
      · have hcl_pos : 0 < clvl := ofNat64_pos ‹_›
        have hbt_lt : ∀ l, (s.core.confl_type = 1#64 ∧
            (l = s.core.confl_lit0.toNat ∨ l = s.core.confl_lit1.toNat)) ∨
            (s.core.confl_type ≠ 1#64 ∧ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat) →
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ clvl := fun l hl => by
          rcases hl with ⟨_, rfl | rfl⟩ | ⟨hbad, _⟩
          · rw [← ha_eq, ← hla_val]; exact Nat.le_max_left _ _
          · rw [← hb_eq, ← hlb_val]; exact Nat.le_max_right _ _
          · exact absurd hbin hbad
        refine wp_join_group (ts := []) (fun () m1 =>
            ∃ s1 cut1, M5OneLitBtInv c F0 F_cur s s1 cut1 clvl ∧ (FullMem c s1 ⋆ R) m1) ?_ ?_
        · rintro _ ⟨⟩ m1 ⟨s1, cut1, hobt, hm1⟩
          fa_fast_steps_nogrp
          · exact hret_bt0 hobt hm1
          · have hne : la ≠ lb := ‹_›
            refine wp_join_group (ts := [i32]) (fun (fc, ()) mf =>
                mf = m1 ∧ fc = if la > lb then a else b) ?_ ?_
            · rintro _ ⟨fc, ⟨⟩⟩ mf ⟨rfl, rfl⟩
              refine wp_join_group (ts := [i32]) (fun (oc, ()) mo =>
                  mo = mf ∧ oc = if la > lb then b else a) ?_ ?_
              · rintro _ ⟨oc, ⟨⟩⟩ mo ⟨rfl, rfl⟩
                refine wp_join_group (ts := [i64]) (fun (jc, ()) mj =>
                    mj = mo ∧ jc = BitVec.ofNat 64
                      (if la > lb then lb.toNat else la.toNat)) ?_ ?_
                · rintro _ ⟨jc, ⟨⟩⟩ mj ⟨rfl, rfl⟩
                  fa_fast_steps_nogrp; c0_call hDet
                  refine ⟨c, s1, R, rfl, hobt.len1, by
                    have := hobt.hw1.cur_level_le; have := hobt.len1.core_ok.trail_end_le
                    have := hobt.len1.core_ok.cur_vars_le; omega,
                    hm1, fun nlvl _ hnlvl => ?_⟩
                  have hjl_lt64 : (if la > lb then lb.toNat else la.toNat) < 2 ^ 64 := by
                    split <;> omega
                  exact s13_oneLit_bin_swap_if hBt hAss hobt (ha_eq ▸ h0lt) (hb_eq ▸ h1lt)
                    hla_val hlb_val rfl hne (ha_eq ▸ hfa) (hb_eq ▸ hfb)
                    (ha_eq ▸ hb_eq ▸ hent) hm1 hQ nlvl
                    (by simpa only [bv64_ofNat_toNat hjl_lt64] using hnlvl)
                · intro Jj hJj; fa_fast_steps
                  · have hgt : la > lb := BitVec.lt_def.mpr (by dsimp only [la, lb]; assumption)
                    exact hJj _ _ ⟨rfl, by rw [ite_eq_left hgt]; exact hlb_64⟩
                  · have hng : ¬ la > lb := fun h =>
                      (by dsimp only [la, lb]; assumption : ¬ lb.toNat < la.toNat)
                        (BitVec.lt_def.mp h)
                    exact hJj _ _ ⟨rfl, by rw [ite_eq_right hng]; exact hla_64⟩
              · intro Jo hJo; fa_fast_steps
                · have hgt : la > lb := BitVec.lt_def.mpr (by dsimp only [la, lb]; assumption)
                  exact hJo _ _ ⟨rfl, by simp [hgt, b]⟩
                · have hng : ¬ la > lb := fun h =>
                    (by dsimp only [la, lb]; assumption : ¬ lb.toNat < la.toNat)
                      (BitVec.lt_def.mp h)
                  exact hJo _ _ ⟨rfl, by simp [hng, a]⟩
            · intro Jf hJf; fa_fast_steps
              · have hgt : la > lb := BitVec.lt_def.mpr (by dsimp only [la, lb]; assumption)
                exact hJf _ _ ⟨rfl, by simp [hgt, a]⟩
              · have hng : ¬ la > lb := fun h =>
                  (by dsimp only [la, lb]; assumption : ¬ lb.toNat < la.toNat) (BitVec.lt_def.mp h)
                exact hJf _ _ ⟨rfl, by simp [hng, b]⟩
        · intro Jbt hJbt; fa_fast_steps_nogrp
          · have hlt_cl : s.core.cur_level > clvl := by
              have hb : clvl % 2 ^ 64 < s.core.cur_level % 2 ^ 64 := ‹_›
              rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hcl_lt64] at hb; exact hb
            c0_call hBt
            refine ⟨c, s, R, rfl, hlen, hcl_lt64,
              fun _ => by have := hw.cur_level_le; have := hlen.core_ok.trail_end_le
                          rw [bv64_ofNat_toNat (by omega)]; omega,
              hw.trail_lits_lt, hm, ?_⟩
            have hcl_lt64' : clvl < 2 ^ 64 := by omega
            dsimp only
            intro vals1 lvl1 rsns1 trl1 tp1 te1 prop1 cl1 unass1 sc1 m1 hlen1 _ _ hcl1 hpres _ _
              hvl1 _ hw1 hm1
            have hcl1_eq : cl1 = clvl := by rw [hcl1, bv64_ofNat_toNat hcl_lt64']; omega
            obtain ⟨hvs1, hls1⟩ := hvl1 ⟨F0, F_cur, Or.inr hw.toFullOtfsWitnessInv⟩
            obtain ⟨cut1, hobt⟩ := m5_oneLit_after_bt hlen hdm hw hmarks hnd hext hw.cut_le hconfl0
              hcl_pos hcl_le hbt_lt (Or.inr ⟨hlt_cl, hlen1, hcl1_eq,
                rfl, hpres.2.2.1, hpres.1.1, hpres.1.2, hdm, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                fun l hl => by have h := hvs1 l hl; rw [bv64_ofNat_toNat hcl_lt64'] at h; exact h,
                fun i hi => by have h := hls1 i hi; rw [bv64_ofNat_toNat hcl_lt64'] at h; exact h,
                hw1 F0 F_cur hw.toFullOtfsWitnessInv (by rw [bv64_ofNat_toNat hcl_lt64']; omega)⟩)
            exact hJbt () m1 ⟨_, cut1, hobt, hm1⟩
          · have hle_cl : s.core.cur_level ≤ clvl := by
              have hb : ¬ clvl % 2 ^ 64 < s.core.cur_level % 2 ^ 64 := ‹_›
              rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hcl_lt64] at hb; omega
            obtain ⟨cut1, hobt⟩ := m5_oneLit_after_bt hlen hdm hw hmarks hnd hext hw.cut_le hconfl0
              hcl_pos hcl_le hbt_lt (Or.inl ⟨hle_cl, rfl⟩)
            exact hJbt () m0 ⟨s, cut1, hobt, hm⟩
    · intro Jmx hJmx
      have ha_i : s.core.confl_lit0.toNat % 2 ^ 32 / 2 = (BitVec.setWidth 64 (a >>> 1)).toNat := by
        rw [bv_c0_zext32_64, bv32_lshr_1, ha_eq, Nat.mod_eq_of_lt h0_32]
      have hb_i : s.core.confl_lit1.toNat % 2 ^ 32 / 2 = (BitVec.setWidth 64 (b >>> 1)).toNat := by
        rw [bv_c0_zext32_64, bv32_lshr_1, hb_eq, Nat.mod_eq_of_lt h1_32]
      fa_fast_steps
      · have hle : lb.toNat ≤ la.toNat := by
          have hc : (s.core.lvl[s.core.confl_lit1.toNat % 2 ^ 32 / 2]'(by
              rw [hlvl_len]; omega)).toNat ≤
              (s.core.lvl[s.core.confl_lit0.toNat % 2 ^ 32 / 2]'(by
              rw [hlvl_len]; omega)).toNat := ‹_›
          simpa only [la, lb, ← ha_i, ← hb_i] using hc
        exact hJmx _ _ ⟨rfl, by rw [Nat.max_eq_left hle]; exact hla_64⟩
      · have hgt : la.toNat < lb.toNat := by
          have hc : ¬ (s.core.lvl[s.core.confl_lit1.toNat % 2 ^ 32 / 2]'(by
              rw [hlvl_len]; omega)).toNat ≤
              (s.core.lvl[s.core.confl_lit0.toNat % 2 ^ 32 / 2]'(by
              rw [hlvl_len]; omega)).toNat := ‹_›
          have h1 : la.toNat = (s.core.lvl[s.core.confl_lit0.toNat % 2 ^ 32 / 2]'(by
              rw [hlvl_len]; omega)).toNat := congrArg BitVec.toNat (Option.some.inj (by
            rw [← List.getElem?_eq_getElem ha_bd,
                ← List.getElem?_eq_getElem (by rw [hlvl_len]; omega), ha_i]))
          have h2 : lb.toNat = (s.core.lvl[s.core.confl_lit1.toNat % 2 ^ 32 / 2]'(by
              rw [hlvl_len]; omega)).toNat := congrArg BitVec.toNat (Option.some.inj (by
            rw [← List.getElem?_eq_getElem hb_bd,
                ← List.getElem?_eq_getElem (by rw [hlvl_len]; omega), hb_i]))
          omega
        exact hJmx _ _ ⟨rfl, by rw [Nat.max_eq_right (Nat.le_of_lt hgt)]; exact hlb_64⟩

section RenameHelpers
mutual
  private inductive S13RenameRel (σ : Sym → Sym) :
      {rs : List Ty} → Expr Val Cont rs → Expr Val Cont rs → Prop
    | let_ {rs ts : List Ty} (op : Op Val ts) {k₁ k₂ : Tup Val ts → Expr Val Cont rs}
        (hk : ∀ r, S13RenameRel σ (k₁ r) (k₂ r)) :
        S13RenameRel σ (.let_ op k₁) (.let_ op k₂)
    | load {rs : List Ty} (t : Ty) (a : Arg Val i64) {k₁ k₂ : Val t → Expr Val Cont rs}
        (hk : ∀ v, S13RenameRel σ (k₁ v) (k₂ v)) :
        S13RenameRel σ (.load t a k₁) (.load t a k₂)
    | store {rs : List Ty} {t : Ty} (v : Arg Val t) (a : Arg Val i64)
        {k₁ k₂ : Expr Val Cont rs} (hk : S13RenameRel σ k₁ k₂) :
        S13RenameRel σ (.store v a k₁) (.store v a k₂)
    | call {rs as bs : List Ty} (f₁ f₂ : Sym) (hf : σ f₁ = f₂) (args : Tup (Arg Val) as)
        {k₁ k₂ : Tup Val bs → Expr Val Cont rs} (hk : ∀ r, S13RenameRel σ (k₁ r) (k₂ r)) :
        S13RenameRel σ (.call f₁ args k₁) (.call f₂ args k₂)
    | jnz {rs : List Ty} (c : Arg Val .bool) {t₁ t₂ e₁ e₂ : Expr Val Cont rs}
        (ht : S13RenameRel σ t₁ t₂) (he : S13RenameRel σ e₁ e₂) :
        S13RenameRel σ (.jnz c t₁ e₁) (.jnz c t₂ e₂)
    | jump {rs ts : List Ty} (j : Cont ts) (args : Tup (Arg Val) ts) :
        S13RenameRel σ (.jump j args) (.jump j args)
    | ret {rs : List Ty} (vs : Tup (Arg Val) rs) :
        S13RenameRel σ (.ret vs) (.ret vs)
    | exit {rs as : List Ty} (f : Sym) (args : Tup (Arg Val) as) :
        S13RenameRel σ (.exit f args) (.exit f args)
    | hlt {rs : List Ty} : S13RenameRel σ (.hlt (rs := rs)) .hlt
    | group {rs : List Ty} {sig : List (List Ty)}
        {b₁ b₂ : Tup Cont sig → Blocks Val Cont rs sig}
        {k₁ k₂ : Tup Cont sig → Expr Val Cont rs}
        (hb : ∀ Js, S13RenameBRel σ (b₁ Js) (b₂ Js))
        (hk : ∀ Js, S13RenameRel σ (k₁ Js) (k₂ Js)) :
        S13RenameRel σ (.group b₁ k₁) (.group b₂ k₂)

  private inductive S13RenameBRel (σ : Sym → Sym) :
      {rs : List Ty} → {sig : List (List Ty)} →
      Blocks Val Cont rs sig → Blocks Val Cont rs sig → Prop
    | nil {rs : List Ty} : S13RenameBRel σ (.nil (rs := rs)) .nil
    | cons {rs : List Ty} {ts : List Ty} {sig : List (List Ty)}
        {b₁ b₂ : Tup Val ts → Expr Val Cont rs}
        {bs₁ bs₂ : Blocks Val Cont rs sig}
        (hb : ∀ xs, S13RenameRel σ (b₁ xs) (b₂ xs))
        (hbs : S13RenameBRel σ bs₁ bs₂) :
        S13RenameBRel σ (.cons b₁ bs₁) (.cons b₂ bs₂)
end

mutual
  private theorem s13_renameRel_wp (σ : Sym → Sym) (Γ : Env) {rs : List Ty}
      {Q : Post rs} {X : XPost} :
      ∀ {e₁ e₂ : Expr Val Cont rs}, S13RenameRel σ e₁ e₂ →
        ∀ m, wp (fun f as bs => Γ (σ f) as bs) Q X e₁ m → wp Γ Q X e₂ m
    | _, _, .let_ _ hk, m, h =>
      Op.wp_mono (fun r hr => s13_renameRel_wp σ Γ (hk r) m hr) h
    | _, _, .load _ _ hk, _, ⟨v, hv, hr⟩ => ⟨v, hv, s13_renameRel_wp σ Γ (hk v) _ hr⟩
    | _, _, .store _ _ hk, _, ⟨hs, hr⟩ => ⟨hs, s13_renameRel_wp σ Γ hk _ hr⟩
    | _, _, .call f₁ _ hf _ hk, _, ⟨P, E, hcall, hcont⟩ =>
      ⟨P, E, hf ▸ hcall,
       ⟨fun r m' hr => s13_renameRel_wp σ Γ (hk r) m' (hcont.1 r m' hr), hcont.2⟩⟩
    | _, _, .jnz _ ht he, m, ⟨h1, h2⟩ =>
      ⟨fun hc => s13_renameRel_wp σ Γ ht m (h1 hc),
       fun hc => s13_renameRel_wp σ Γ he m (h2 hc)⟩
    | _, _, .jump _ _, _, h => h
    | _, _, .ret _, _, h => h
    | _, _, .exit _ _, _, h => h
    | _, _, .hlt, _, h => h
    | _, _, .group hb hk, m, h => fun Js hcl =>
      s13_renameRel_wp σ Γ (hk Js) m
        (h Js (s13_renameBRel_closed σ Γ (hb Js) Js hcl))

  private theorem s13_renameBRel_closed (σ : Sym → Sym) (Γ : Env) {rs : List Ty}
      {Q : Post rs} {X : XPost} :
      ∀ {sig : List (List Ty)} {bs₁ bs₂ : Blocks Val Cont rs sig},
        S13RenameBRel σ bs₁ bs₂ → ∀ Js,
        Closed Γ Q X bs₂ Js → Closed (fun f as bs => Γ (σ f) as bs) Q X bs₁ Js
    | _, _, _, .nil, (), _ => trivial
    | _, _, _, .cons hb hbs, (_, Js), h =>
      ⟨fun xs m hr => h.1 xs m (s13_renameRel_wp σ Γ (hb xs) m hr),
       s13_renameBRel_closed σ Γ hbs Js h.2⟩
end
end RenameHelpers

private theorem s13_wp_let_inv {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost}
    {op : Op Val ts} {k : Tup Val ts → Expr Val Cont rs} {m : Mem 64}
    (h : wp Γ Q X (.let_ op k) m) : op.wp (fun r => wp Γ Q X (k r) m) := h

private theorem s13_wp_load_of {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {a : Arg Val i64} {k : Val i64 → Expr Val Cont rs} {v : BitVec 64} {m : Mem 64}
    (hld : loadVal m i64 a.val = some v) (hk : wp Γ Q X (k v) m) :
    wp Γ Q X (.load i64 a k) m := ⟨v, hld, hk⟩

private theorem s13_wp_jnz_false_of {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : Arg Val .bool} {t e : Expr Val Cont rs} {m : Mem 64}
    (hc : c.val = false) (he : wp Γ Q X e m) :
    wp Γ Q X (.jnz c t e) m :=
  ⟨fun h => absurd h (by simp [hc]), fun _ => he⟩

/-- `full_one_lit_confl` satisfies canonical `Full.fullOneLitConflSpec`: `confl_type == 1`
preserves binary `jumpreasons` (`jr_ol`) via `s13_bin_resolve`, and `confl_type != 1` transports
`m5_oneLit_large_branch_wp` to `"full_backtrack_ac_fid"`. -/
theorem full_one_lit_confl_step13_wp (Γ : Env)
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hDet : ∀ args m Q X, Full.fullDetNewLevelSpec args m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] args m Q X)
    (hBt : ∀ args m Q X, Full.fullBacktrackSpec args m Q X →
      Γ "full_backtrack_ac_fid" [i64, i64] [] args m Q X)
    (hAss : ∀ args m Q X, Full.fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X)
    (hUnw : ∀ args m Q X, Full.fullUnwatchLargeSpec args m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] args m Q X)
    (hPush : ∀ args m Q X, Full.fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, Full.fullOneLitConflSpec args m Q X →
      Func.wp Γ fidStep13S2OneLitConflFn.body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, cut, s, R, rfl, hcutInv, hconfl, hm, hQ⟩
  obtain ⟨hlen, hw, hmarks, hnd, hext, hdm⟩ := hcutInv
  have hQ' : M5OneLitPost c F0 F_cur s R Q :=
    fun r s' m' hlen' hr hcv hfu hws2 hdm' _ hmk' hnd' hext' _ h20 h1 h2 h0 hm' =>
      hQ r s' m' hlen' hr hcv hfu hws2
        (fun h20r => let ⟨hu, heq⟩ := h20 h20r
          ⟨hu, heq ▸ ⟨hlen, hw.toFullOtfsWitnessInv, hmarks, hnd, hext, hdm⟩,
            by rw [heq]; exact Nat.le_refl _, by rw [heq]⟩)
        (fun h1r => let ⟨hw', hlt⟩ := h1 h1r
          ⟨⟨hlen', hw', hmk', hnd', hext', hdm'⟩, hlt⟩)
        (fun h2r => ⟨hlen', h2 h2r, hmk', hnd', hext', hdm'⟩)
        (fun h0r => let ⟨cut', hcut'le, hw', hpos, hle, hcf'⟩ := h0 h0r
          ⟨cut', hcut'le, ⟨hlen', hw', hmk', hnd', hext', hdm'⟩, hpos, hle, hcf'⟩)
        hm'
  by_cases hbin : s.core.confl_type = 1#64
  · exact s13_oneLit_bin_branch_wp Γ hDet hBt hAss hlen hdm hw hmarks hnd hext hconfl hbin hm hQ'
  · let σ : Sym → Sym := fun fn => if fn = "full_backtrack" then "full_backtrack_ac_fid" else fn
    have hm5 : Func.wp (fun fn as bs => Γ (σ fn) as bs) full_one_lit_confl_m5_body
        (c.hdr, ()) m Q X :=
      m5_oneLit_large_branch_wp (fun fn as bs => Γ (σ fn) as bs)
        (fun a m' Q' X' h' => hDefrag a m' Q' X' h')
        (fun a m' Q' X' h' => hDet a m' Q' X' h')
        (fun a m' Q' X' h' => by simpa [σ] using hBt a m' Q' X' h')
        (fun a m' Q' X' h' => hAss a m' Q' X' h')
        (fun a m' Q' X' h' => hUnw a m' Q' X' h')
        (fun a m' Q' X' h' => hPush a m' Q' X' h')
        hlen hdm hw hmarks hnd hext hw.cut_le hconfl hbin hm hQ'
    have hld_lvl := FullArenaTactics.load_full_level_ptr hm
    have hld_ar := FullArenaTactics.load_full_arena_ptr hm
    have hld_ct := FullArenaTactics.load_full_confl_type hm
    change wp _ Q X (full_one_lit_confl_m5_body Val Cont (c.hdr, ())) m at hm5
    dsimp only [full_one_lit_confl_m5_body] at hm5
    have hm5 := s13_wp_let_inv hm5
    dsimp only [Op.wp, OpCode.wp, Arg.val, vals, lift2, lift1] at hm5
    rcases hm5 with ⟨_, hld', hm5⟩; dsimp only [Arg.val] at hld'; rw [hld_lvl] at hld'; cases hld'
    have hm5 := s13_wp_let_inv hm5
    dsimp only [Op.wp, OpCode.wp, Arg.val, vals, lift2, lift1] at hm5
    rcases hm5 with ⟨_, hld', hm5⟩; dsimp only [Arg.val] at hld'; rw [hld_ar] at hld'; cases hld'
    have hm5 := s13_wp_let_inv hm5
    dsimp only [Op.wp, OpCode.wp, Arg.val, vals, lift2, lift1] at hm5
    rcases hm5 with ⟨_, hld', hm5⟩; dsimp only [Arg.val] at hld'; rw [hld_ct] at hld'; cases hld'
    have hm5 := s13_wp_let_inv hm5
    dsimp only [Op.wp, OpCode.wp, Arg.val, vals, lift2, lift1] at hm5
    have hm5_else := hm5.2 (decide_eq_false hbin)
    dsimp only [Func.wp, fidStep13S2OneLitConflFn, full_one_lit_confl_body]
    change Op.wp _ _; dsimp only [Op.wp, OpCode.wp, Arg.val, vals, lift2, lift1]
    refine s13_wp_load_of hld_lvl ?_
    change Op.wp _ _; dsimp only [Op.wp, OpCode.wp, Arg.val, vals, lift2, lift1]
    refine s13_wp_load_of hld_ar ?_
    change Op.wp _ _; dsimp only [Op.wp, OpCode.wp, Arg.val, vals, lift2, lift1]
    refine s13_wp_load_of hld_ct ?_
    change Op.wp _ _; dsimp only [Op.wp, OpCode.wp, Arg.val, vals, lift2, lift1]
    refine s13_wp_jnz_false_of (decide_eq_false hbin) ?_
    refine s13_renameRel_wp σ Γ ?_ m hm5_else
    repeat (first
      | (intro)
      | (rfl)
      | apply S13RenameRel.let_
      | apply S13RenameRel.load
      | apply S13RenameRel.store
      | apply S13RenameRel.call
      | apply S13RenameRel.jnz
      | apply S13RenameRel.jump
      | apply S13RenameRel.ret
      | apply S13RenameRel.exit
      | apply S13RenameRel.hlt
      | apply S13RenameRel.group
      | apply S13RenameBRel.cons
      | apply S13RenameBRel.nil
      | exact ([] : List Ty))

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S2
