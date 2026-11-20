module

public import LeanQbe.T.Examples.Kissat.FullBveBvaLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` UNSAT-Only BVE/BCE Proofs — Part 2 (`Stage 4`, BVE/BCE Shard)

Provides:
1. Collision-free shared transport, pigeonhole, and semantic-resolution lemmas inside
   `FullBveBvaHelpers` (`nodup_lt_length_le`, `FullDenseInvW` updates across `tmp`/`lit_mark`/
   `scratch`/`markGarb`/`full_delete_binary`, `ResolveTmpInv`, `SideCovered`, and cleanup loops).
2. Parametric `(Γ : Env)` `Func.wp` proof for `full_bve_resolve_pair`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Scoped group-stepping helper & pure/invariant `FullBveBvaHelpers` -/

namespace FullBveBvaTactics

open Lean Meta Elab Tactic

/-- Step C0 goals via `c0_step` until hitting an `Expr.group` node (up to fuel `200`). -/
scoped elab "bve_to_group" : tactic => do
  evalTactic (← `(tactic| try change LeanQbe.T.Func.wp _ _ _ _ _ _))
  evalTactic (← `(tactic| try change LeanQbe.T.wp _ _ _ _ _))
  for _ in [:200] do
    let g ← getMainGoal
    let ty ← instantiateMVars (← g.getType)
    let ty := ty.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
      let e := (ty.getArg! 4).headBeta
      if e.isAppOf ``LeanQbe.T.Expr.group then break
    evalTactic (← `(tactic| c0_step))

@[scoped c0_store] theorem store_full_tmp0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.core.tmp.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 0#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 0#64) v) := by
  simpa using FullArenaTactics.store_full_tmp (i := 0) v hi hm

end FullBveBvaTactics

namespace FullBveBvaHelpers

open FullBveBvaSpecs

theorem bv32_add1_toNat {x : BitVec 32} {n : Nat} (hx : x.toNat < n) (hn : n < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by bv_omega

/-! ### 1.1 Pigeonhole & `List` slice helpers -/

private theorem nodup_length_le_filter_ne_succ {m : Nat} {xs : List Nat}
    (hn : xs.Nodup) : xs.length ≤ (xs.filter (fun y => decide (y ≠ m))).length + 1 := by
  induction xs with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at hn
    by_cases ham : a = m
    · subst ham
      have hfil : t.filter (fun y => decide (y ≠ a)) = t :=
        List.filter_eq_self.mpr fun y hy => decide_eq_true (fun h => hn.1 (h ▸ hy))
      rw [List.length_cons, List.filter_cons_of_neg (by simp), hfil]; exact Nat.le_refl _
    · simp only [List.filter_cons, decide_eq_true ham, ↓reduceIte, List.length_cons]
      exact Nat.succ_le_succ (ih hn.2)

theorem nodup_lt_length_le :
    ∀ {m : Nat} {xs : List Nat}, xs.Nodup → (∀ x ∈ xs, x < m) → xs.length ≤ m
  | 0, xs, _, hb => by
    cases xs with
    | nil => simp
    | cons x _ => exact absurd (hb x (by simp)) (by omega)
  | m + 1, xs, hn, hb => by
    have ih := nodup_lt_length_le (m := m) (xs := xs.filter (fun y => decide (y ≠ m)))
      (hn.filter _) fun x hx => by
        rw [List.mem_filter, decide_eq_true_iff] at hx
        have := hb x hx.1; omega
    have hle := nodup_length_le_filter_ne_succ (m := m) hn
    omega

theorem take_set_append {α : Type} {xs : List α} {r : Nat} {v : α} (hr : r < xs.length) :
    (xs.set r v).take (r + 1) = xs.take r ++ [v] := by
  apply List.ext_getElem
  · simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hr),
      Nat.min_eq_left (Nat.succ_le_of_lt hr)]
  · intro i hi1 hi2
    by_cases hir : i < r
    · have hi_xs : i < xs.length := by omega
      rw [List.getElem_take, List.getElem_set_ne (by omega), List.getElem_append_left
        (by simp [List.length_take]; omega), List.getElem_take]
    · have hieq : i = r := by
        simp only [List.length_take, List.length_set, Nat.min_eq_left (Nat.succ_le_of_lt hr)]
          at hi1
        omega
      subst hieq
      rw [List.getElem_take, List.getElem_set_self (by simp [hr]), List.getElem_append_right
        (by simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hr)])]
      simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hr)]

theorem bv32_shl1_or1_eq_xor (v : BitVec 32) : (v <<< 1) ||| 1#32 = (v <<< 1) ^^^ 1#32 := by
  ext i hi
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp
  · have h1 : (1#32 : BitVec 32)[i] = false := by
      rw [BitVec.getElem_eq_testBit_toNat, show (1#32 : BitVec 32).toNat = 1 by rfl,
        Nat.testBit, Nat.shiftRight_eq_div_pow,
        Nat.div_eq_of_lt (Nat.one_lt_two_pow (by omega : i ≠ 0))]; rfl
    simp [h1]

/-! ### 1.2 Shared `FullDenseInvW` transport helpers -/

theorem fullDenseInvW_with_tmp_litMark {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {lm' : List (BitVec 8)} {tmp' : List (BitVec 32)} {tl' : Nat}
    (hll : lm'.length = 2 * c.max_vars) (htl : tmp'.length = c.max_vars)
    (htll : tl' ≤ c.max_vars) (hlmc : ∀ l < 2 * c.max_vars, lm'[l]?.getD 0#8 = 0#8) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with lit_mark := lm', tmp := tmp', tmp_len := tl' } } :=
  ⟨⟨{ h.1.core_ok with lit_mark_len := hll, tmp_len_arr := htl, tmp_len_le := htll },
     h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   ⟨h.2.2.1.1, hlmc⟩, h.2.2.2.1, ⟨fun i hi => h.2.2.2.2.1.1 i hi, h.2.2.2.2.1.2⟩,
   h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fullDenseInvW_with_scratch {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (h : FullDenseInvW c F0 F_cur s) (hlen' : s'.LengthsOk c)
    (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hext : FullExtScratchOk c s') : FullDenseInvW c F0 F_cur s' := by
  have heq : s'.core = s.core := fullCoreState_agrees_with_scratch hcore
  refine ⟨hlen', ?_, ?_, ?_, hext, ?_, ?_⟩
  · rw [heq]; exact h.2.1
  · unfold FullLitMarksClear at *; rw [heq]; exact h.2.2.1
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    rw [heq]; exact h.2.2.2.1
  · rw [heq]; exact h.2.2.2.2.2.1
  · rw [heq]; exact h.2.2.2.2.2.2

theorem fullDenseInvW_of_delete_binary {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {wvec' wstk' : List (BitVec 32)} {wu' nb' : BitVec 64}
    (hlen' : ({ s with core := { s.core with
      wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' } } : FullState
      ).LengthsOk c)
    (hwat : ∀ F, ModeWatchesInv F s.core →
      ModeWatchesInv F { s.core with
        wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' }) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with
        wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' } } :=
  ⟨hlen', { h.2.1 with
    arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
    watches := hwat F_cur h.2.1.watches },
   h.2.2.1, h.2.2.2.1, ⟨fun i hi => h.2.2.2.2.1.1 i hi, h.2.2.2.2.1.2⟩,
   h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private theorem garb_or_ne0 (x : BitVec 32) :
    ((x ||| 0x00080000#32) &&& 0x00080000#32) ≠ 0#32 := by
  intro h; have h19 := congrArg (·[19]) h
  revert h19; simp [show (0x00080000#32)[19] = true from rfl]

theorem fullDenseInvW_markGarb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {cref : Nat}
    (href : cref ∈ fullArenaClauseRefs s) (ag' : BitVec 64) :
    let s' : FullState :=
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } }
    fullArenaClauseRefs s' = fullArenaClauseRefs s ∧ FullDenseInvW c F0 F_cur s' := by
  intro s'
  have hw := h.2.1
  have hcl := h.1.core_ok
  have hmg := hw.arena.markGarb hcl href ag'
  have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := hmg.1
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with arena_len_arr := by simp [s', hcl.arena_len_arr] }, h.1.scratch_ok⟩
  have hnodup' : FullArenaVarsNodup s' := by
    intro r hr hng
    rw [hrefs] at hr
    by_cases hrc : r = cref
    · subst r
      have har_len : cref < s.core.arena.length := by
        have := hcl.arena_len_le; have := hcl.arena_len_arr
        have := (hw.arena.refs_wf cref href).1; omega
      have hset : s'.core.arena[cref]? = some (fullArenaHdr s cref ||| 0x00080000#32) :=
        List.getElem?_set_self har_len
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng
      rw [hset, Option.getD_some] at hng
      simp only [bne, beq_iff_eq, Bool.not_eq_false'] at hng
      exact absurd hng (garb_or_ne0 (fullArenaHdr s cref))
    · have hdisj : r + 3 + fullArenaClauseSize s r ≤ cref ∨ cref + 3 ≤ r := by
        rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
        · exact Or.inl (hw.arena.disjoint hr href hlt)
        · exact Or.inr (by have := hw.arena.disjoint href hr hgt; omega)
      have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
        have := (hw.arena.refs_wf r hr).2.2.1; have := (hw.arena.refs_wf r hr).2.2.2.1
        have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
      have hlits : fullArenaClauseLits s' r = fullArenaClauseLits s r :=
        (fullArenaClauseLitsCore_set_outside hbd hdisj).2
      have hng0 : fullArenaClauseGarb s r = false := by
        unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng ⊢
        simpa [s', List.getElem?_set_ne (Ne.symm hrc)] using hng
      rw [hlits]; exact h.2.2.2.1 r hr hng0
  have hext' : FullExtScratchOk c s' :=
    ⟨fun i hi => by
      have hi0 := h.2.2.2.2.1.1 i hi
      dsimp only; rw [hrefs]; exact hi0,
     h.2.2.2.2.1.2⟩
  refine ⟨hrefs, hlen',
    { hw with
      arena := hmg.2
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl fun r hr => by
        change r ∈ fullArenaClauseRefs s'; rw [hrefs]; exact hr
      reason_inv := fun idx hidx hne => by
        have hlv : (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
          have := hw.lvl_le idx hidx; have := h.2.2.2.2.2.1; omega
        exact absurd (hw.level0_rsn_none idx hidx hlv) hne
      reason_lit_mem := fun idx hidx hne => by
        have hlv : (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
          have := hw.lvl_le idx hidx; have := h.2.2.2.2.2.1; omega
        exact absurd (hw.level0_rsn_none idx hidx hlv) hne },
    h.2.2.1, hnodup', hext', h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-! ### 1.3 Level-0 literal semantics, resolvent `tmp` invariant, & cleanup -/

theorem bv8_sgt0_iff_eq1 {v : BitVec 8} (hv : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) :
    BitVec.slt 0#8 v ↔ v = 1#8 := by
  rcases hv with rfl | rfl | rfl <;> decide

theorem witness_lit_false_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hlv0 : s.core.cur_level = 0)
    {l : Nat} (hl : l < 2 * s.core.cur_vars) (hf : s.core.vals[l]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1]) := by
  obtain ⟨idx, hidx, htrl⟩ := (hw.vals_false_iff l hl).mp hf
  have hlv : (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le idx hidx; omega
  have hent := hw.level0_sound idx hidx hlv
  rwa [htrl] at hent

theorem tmpMark_clear_step {lm : List (BitVec 8)} {tmp : List (BitVec 32)}
    {len k n : Nat} (hk_lt : k < tmp.length) (hidx_lt : (tmp[k]'hk_lt).toNat < n)
    (hml : lm.length = n)
    (hcov : ∀ l < n,
      ((∃ r < k, (tmp[r]?.getD 0#32).toNat = l) ∨
       (∀ r < len, (tmp[r]?.getD 0#32).toNat ≠ l)) → lm[l]? = some 0#8) :
    let idx := (tmp[k]'hk_lt).toNat
    ∀ l < n,
      ((∃ r < k + 1, (tmp[r]?.getD 0#32).toNat = l) ∨
       (∀ r < len, (tmp[r]?.getD 0#32).toNat ≠ l)) →
      (lm.set idx 0#8)[l]? = some 0#8 := by
  intro idx l hl hc
  by_cases heq : l = idx
  · subst heq; rw [List.getElem?_set_self (by omega)]
  · rw [List.getElem?_set_ne (Ne.symm heq)]
    refine hcov l hl ?_
    rcases hc with ⟨r, hr, hrl⟩ | hnone
    · left
      have hrk : r ≠ k := by
        rintro rfl; apply heq
        rw [← hrl, List.getElem?_eq_getElem hk_lt, Option.getD_some]
      exact ⟨r, by omega, hrl⟩
    · exact Or.inr hnone

structure ResolveTmpInv (c : FullCfg) (s : FullState) (rlen : Nat)
    (tmp : List (BitVec 32)) (lm : List (BitVec 8)) : Prop where
  cur_le : s.core.cur_vars ≤ c.max_vars
  rlen_le : rlen ≤ s.core.cur_vars
  tmp_len : tmp.length = c.max_vars
  lm_len : lm.length = 2 * c.max_vars
  lits_lt : ∀ k < rlen, (tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars
  vars_nodup : ((tmp.take rlen).map fun x => x.toNat / 2).Nodup
  marked : ∀ l < 2 * c.max_vars,
    (∃ k < rlen, (tmp[k]?.getD 0#32).toNat = l) → lm[l]? = some 1#8
  unmarked : ∀ l < 2 * c.max_vars,
    (∀ k < rlen, (tmp[k]?.getD 0#32).toNat ≠ l) → lm[l]? = some 0#8

theorem ResolveTmpInv.init {c : FullCfg} {s : FullState} (hcl : s.core.LengthsOk c)
    (hlmc : ∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8) :
    ResolveTmpInv c s 0 s.core.tmp s.core.lit_mark :=
  ⟨hcl.cur_vars_le, Nat.zero_le _, hcl.tmp_len_arr, hcl.lit_mark_len, fun _ hk => by omega,
   by simp, fun _ _ ⟨_, hk, _⟩ => by omega, fun l hl _ => by
     have := hlmc l hl
     rw [List.getElem?_eq_getElem (by rw [hcl.lit_mark_len]; exact hl), Option.getD_some] at this
     rw [List.getElem?_eq_getElem (by rw [hcl.lit_mark_len]; exact hl), this]⟩

theorem ResolveTmpInv.not_mem_of_lm0 {c : FullCfg} {s : FullState} {rlen : Nat}
    {tmp : List (BitVec 32)} {lm : List (BitVec 8)} (h : ResolveTmpInv c s rlen tmp lm)
    {l : Nat} (hl : l < 2 * c.max_vars) (hlm : lm[l]? = some 0#8) :
    ∀ k < rlen, (tmp[k]?.getD 0#32).toNat ≠ l := by
  intro k hk heq
  have h1 := h.marked l hl ⟨k, hk, heq⟩
  rw [hlm] at h1; cases h1

theorem ResolveTmpInv.mem_of_lm_ne0 {c : FullCfg} {s : FullState} {rlen : Nat}
    {tmp : List (BitVec 32)} {lm : List (BitVec 8)} (h : ResolveTmpInv c s rlen tmp lm)
    {l : Nat} (hl : l < 2 * c.max_vars) (hlm : lm[l]? ≠ some 0#8) :
    l ∈ (tmp.take rlen).map BitVec.toNat := by
  have hex : ∃ k < rlen, (tmp[k]?.getD 0#32).toNat = l :=
    Classical.byContradiction fun hne =>
      hlm (h.unmarked l hl fun k hk heq => hne ⟨k, hk, heq⟩)
  obtain ⟨k, hk, heq⟩ := hex
  have hk_lt : k < tmp.length := by
    rw [h.tmp_len]; exact Nat.lt_of_lt_of_le hk (Nat.le_trans h.rlen_le h.cur_le)
  have htk : k < (tmp.take rlen).length := by
    rw [List.length_take_of_le (by rw [h.tmp_len]; exact Nat.le_trans h.rlen_le h.cur_le)]; exact hk
  rw [← heq, List.getElem?_eq_getElem hk_lt, Option.getD_some, List.mem_map]
  refine ⟨(tmp.take rlen)[k]'htk, List.getElem_mem htk, ?_⟩
  rw [List.getElem_take]

private theorem nat_div2_eq_iff {a b : Nat} (h : a / 2 = b / 2) : a = b ∨ a = b ^^^ 1 := by
  have hle := litNeg_eq b
  rcases Nat.mod_two_eq_zero_or_one b with hb | hb
  · simp only [litNeg, hb, ↓reduceIte] at hle; rw [hle]; omega
  · simp only [litNeg, show b % 2 ≠ 0 by omega, ↓reduceIte] at hle; rw [hle]; omega

theorem ResolveTmpInv.rlen_lt_of_unmarked {c : FullCfg} {s : FullState} {rlen : Nat}
    {tmp : List (BitVec 32)} {lm : List (BitVec 8)} (h : ResolveTmpInv c s rlen tmp lm)
    {l : BitVec 32} (hl : l.toNat < 2 * s.core.cur_vars)
    (hlm0 : lm[l.toNat]? = some 0#8) (hlm1 : lm[l.toNat ^^^ 1]? = some 0#8) :
    rlen < s.core.cur_vars := by
  have hl_mv : l.toNat < 2 * c.max_vars := by have := h.cur_le; omega
  have hl1_mv : l.toNat ^^^ 1 < 2 * c.max_vars := FullBveBvaTactics.nat_xor1_lt_two_mul hl_mv
  have hn0 := h.not_mem_of_lm0 hl_mv hlm0
  have hn1 := h.not_mem_of_lm0 hl1_mv hlm1
  have htk_len : (tmp.take rlen).length = rlen :=
    List.length_take_of_le (by rw [h.tmp_len]; exact Nat.le_trans h.rlen_le h.cur_le)
  have hnotin : l.toNat / 2 ∉ (tmp.take rlen).map fun x => x.toNat / 2 := by
    intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨x, hx, hdiv⟩ := hmem
    rw [List.mem_iff_getElem] at hx
    obtain ⟨k, hkt, hkx⟩ := hx
    have hkr : k < rlen := by rw [htk_len] at hkt; exact hkt
    have hkl : k < tmp.length := by rw [h.tmp_len]; have := h.cur_le; have := h.rlen_le; omega
    rw [List.getElem_take] at hkx
    have hdiv' : (tmp[k]?.getD 0#32).toNat / 2 = l.toNat / 2 := by
      rw [List.getElem?_eq_getElem hkl, Option.getD_some, hkx]; exact hdiv
    rcases nat_div2_eq_iff hdiv' with h0 | h1
    · exact hn0 k hkr h0
    · exact hn1 k hkr h1
  have hnd : (l.toNat / 2 :: (tmp.take rlen).map fun x => x.toNat / 2).Nodup :=
    List.nodup_cons.mpr ⟨hnotin, h.vars_nodup⟩
  have hbd : ∀ v ∈ l.toNat / 2 :: (tmp.take rlen).map fun x => x.toNat / 2,
      v < s.core.cur_vars := by
    intro v hv
    rw [List.mem_cons] at hv
    rcases hv with rfl | hmem
    · omega
    · rw [List.mem_map] at hmem
      obtain ⟨x, hx, rfl⟩ := hmem
      rw [List.mem_iff_getElem] at hx
      obtain ⟨k, hkt, rfl⟩ := hx
      have hkr : k < rlen := by rw [htk_len] at hkt; exact hkt
      have hkl : k < tmp.length := by rw [h.tmp_len]; have := h.cur_le; have := h.rlen_le; omega
      rw [List.getElem_take]
      have := h.lits_lt k hkr
      rw [List.getElem?_eq_getElem hkl, Option.getD_some] at this; omega
  have hlen := nodup_lt_length_le hnd hbd
  simp only [List.length_cons, List.length_map, htk_len] at hlen
  omega

theorem ResolveTmpInv.push {c : FullCfg} {s : FullState} {rlen : Nat}
    {tmp : List (BitVec 32)} {lm : List (BitVec 8)} (h : ResolveTmpInv c s rlen tmp lm)
    {l : BitVec 32} (hl : l.toNat < 2 * s.core.cur_vars)
    (hlm0 : lm[l.toNat]? = some 0#8) (hlm1 : lm[l.toNat ^^^ 1]? = some 0#8) :
    rlen < s.core.cur_vars ∧
    ResolveTmpInv c s (rlen + 1) (tmp.set rlen l) (lm.set l.toNat 1#8) ∧
    (∀ z ∈ (tmp.take rlen).map BitVec.toNat,
      z ∈ ((tmp.set rlen l).take (rlen + 1)).map BitVec.toNat) ∧
    l.toNat ∈ ((tmp.set rlen l).take (rlen + 1)).map BitVec.toNat := by
  have hrlt := h.rlen_lt_of_unmarked hl hlm0 hlm1
  have hrtmp : rlen < tmp.length := by rw [h.tmp_len]; have := h.cur_le; omega
  have hrlm : l.toNat < lm.length := by rw [h.lm_len]; have := h.cur_le; omega
  have hl_mv : l.toNat < 2 * c.max_vars := by have := h.cur_le; omega
  have hl1_mv : l.toNat ^^^ 1 < 2 * c.max_vars := FullBveBvaTactics.nat_xor1_lt_two_mul hl_mv
  have hn0 := h.not_mem_of_lm0 hl_mv hlm0
  have hn1 := h.not_mem_of_lm0 hl1_mv hlm1
  have htk_len : (tmp.take rlen).length = rlen :=
    List.length_take_of_le (by rw [h.tmp_len]; exact Nat.le_trans h.rlen_le h.cur_le)
  have hnotin : l.toNat / 2 ∉ (tmp.take rlen).map fun x => x.toNat / 2 := by
    intro hmem; rw [List.mem_map] at hmem; obtain ⟨x, hx, hdiv⟩ := hmem
    rw [List.mem_iff_getElem] at hx; obtain ⟨k, hkt, hkx⟩ := hx
    have hkr : k < rlen := by rw [htk_len] at hkt; exact hkt
    have hkl : k < tmp.length := by omega
    rw [List.getElem_take] at hkx
    have hdiv' : (tmp[k]?.getD 0#32).toNat / 2 = l.toNat / 2 := by
      rw [List.getElem?_eq_getElem hkl, Option.getD_some, hkx]; exact hdiv
    rcases nat_div2_eq_iff hdiv' with h0 | h1
    · exact hn0 k hkr h0
    · exact hn1 k hkr h1
  refine ⟨hrlt, ?_, ?_, ?_⟩
  · refine ⟨h.cur_le, by omega, by simp [h.tmp_len], by simp [h.lm_len], ?_, ?_, ?_, ?_⟩
    · intro k hk
      by_cases hkr : k = rlen
      · subst hkr; rw [List.getElem?_set_self hrtmp, Option.getD_some]; exact hl
      · rw [List.getElem?_set_ne (Ne.symm hkr)]; exact h.lits_lt k (by omega)
    · rw [take_set_append hrtmp, List.map_append, List.nodup_append]
      refine ⟨h.vars_nodup, by simp, fun a ha1 b hb => ?_⟩
      rw [List.mem_map] at hb; obtain ⟨y, hy, rfl⟩ := hb
      rw [List.mem_singleton.mp hy]; exact fun heq => hnotin (heq ▸ ha1)
    · intro l' hl' hex
      by_cases hl'eq : l' = l.toNat
      · subst hl'eq; rw [List.getElem?_set_self hrlm]
      · rw [List.getElem?_set_ne (Ne.symm hl'eq)]
        obtain ⟨k, hk, heq⟩ := hex
        have hkr : k ≠ rlen := by
          rintro rfl; apply hl'eq
          rw [← heq, List.getElem?_set_self hrtmp, Option.getD_some]
        rw [List.getElem?_set_ne (Ne.symm hkr)] at heq
        exact h.marked l' hl' ⟨k, by omega, heq⟩
    · intro l' hl' hnone
      have hl'ne : l.toNat ≠ l' := by
        have := hnone rlen (Nat.lt_succ_self rlen)
        rw [List.getElem?_set_self hrtmp, Option.getD_some] at this; exact this
      rw [List.getElem?_set_ne hl'ne]
      exact h.unmarked l' hl' fun k hk => by
        have := hnone k (Nat.lt_succ_of_lt hk)
        rwa [List.getElem?_set_ne (by omega)] at this
  · intro z hz; rw [take_set_append hrtmp, List.map_append]; exact List.mem_append_left _ hz
  · rw [take_set_append hrtmp, List.map_append]; exact List.mem_append_right _ (by simp)

def SideCovered (F_cur : List (List Nat)) (piv : Nat) (R : List Nat) (x : Nat) : Prop :=
  x = piv ∨ x ∈ R ∨ (cnfOfClauses F_cur).EntailsClause (cnfClause [x ^^^ 1])

theorem SideCovered.mono {F_cur : List (List Nat)} {piv : Nat} {R1 R2 : List Nat}
    (hsub : ∀ z ∈ R1, z ∈ R2) {x : Nat} (hx : SideCovered F_cur piv R1 x) :
    SideCovered F_cur piv R2 x := by
  rcases hx with rfl | hmem | hent
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (hsub _ hmem))
  · exact Or.inr (Or.inr hent)

theorem side_entails_of_clause {F_cur : List (List Nat)} {piv : Nat} {R xs : List Nat}
    (hxs : (cnfOfClauses F_cur).EntailsClause (cnfClause xs))
    (hcov : ∀ x ∈ xs, SideCovered F_cur piv R x) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause (piv :: R)) := by
  rw [CNF.entails_clause_def] at hxs ⊢
  intro α hα
  obtain ⟨x, hx, hsat⟩ := (clause_sat_cnfClause_iff α xs).mp (hxs α hα)
  rcases hcov x hx with rfl | hmem | hent
  · exact (clause_sat_cnfClause_iff α _).mpr ⟨x, List.mem_cons_self, hsat⟩
  · exact (clause_sat_cnfClause_iff α _).mpr ⟨x, List.mem_cons_of_mem _ hmem, hsat⟩
  · have hneg := CNF.entails_clause_def.mp hent α hα
    have hln : x ^^^ 1 = litNeg x := rfl
    rw [hln] at hneg
    exact absurd ((sat_cnfClause_singleton α x).mpr hsat) ((sat_cnfClause_litNeg_iff α x).mp hneg)

theorem side_entails_of_bin {F_cur : List (List Nat)} {piv ot : Nat} {R : List Nat}
    (hbin : (cnfOfClauses F_cur).EntailsClause (cnfClause [piv, ot]))
    (hcov : SideCovered F_cur piv R ot) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause (piv :: R)) :=
  side_entails_of_clause hbin fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact hcov

theorem resolve_pivots_entails {F_cur : List (List Nat)} {v : Nat} {R : List Nat}
    (hp : (cnfOfClauses F_cur).EntailsClause (cnfClause (2 * v :: R)))
    (hn : (cnfOfClauses F_cur).EntailsClause (cnfClause ((2 * v + 1) :: R))) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause R) := by
  rw [CNF.entails_clause_def] at hp hn ⊢
  intro α hα
  by_cases hsat : (cnfClause [2 * v]).Sat α
  · obtain ⟨y, hy, hys⟩ := (clause_sat_cnfClause_iff α _).mp (hn α hα)
    rw [List.mem_cons] at hy
    rcases hy with rfl | hyr
    · have hle : 2 * v + 1 = litNeg (2 * v) := by
        rw [litNeg_eq, ite_eq_left (by omega)]
      have hsat1 := (sat_cnfClause_singleton α (2 * v + 1)).mpr hys
      rw [hle] at hsat1
      exact absurd hsat ((sat_cnfClause_litNeg_iff α (2 * v)).mp hsat1)
    · exact (clause_sat_cnfClause_iff α R).mpr ⟨y, hyr, hys⟩
  · obtain ⟨y, hy, hys⟩ := (clause_sat_cnfClause_iff α _).mp (hp α hα)
    rw [List.mem_cons] at hy
    rcases hy with rfl | hyr
    · exact absurd ((sat_cnfClause_singleton α _).mpr hys) hsat
    · exact (clause_sat_cnfClause_iff α R).mpr ⟨y, hyr, hys⟩

theorem resolve_lit_sideCovered_of_val_ne0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core)
    (hlv0 : s.core.cur_level = 0) {piv : Nat} {R : List Nat} {l : Nat}
    (hl : l < 2 * s.core.cur_vars) (hsgt : ¬ BitVec.slt 0#8 (s.core.vals[l]?.getD 0#8))
    (hne0 : s.core.vals[l]?.getD 0#8 ≠ 0#8) : SideCovered F_cur piv R l := by
  have hdom := hw.vals_domain l hl
  have hne1 : s.core.vals[l]?.getD 0#8 ≠ 1#8 := fun h => hsgt ((bv8_sgt0_iff_eq1 hdom).mpr h)
  have hff : s.core.vals[l]?.getD 0#8 = 0xFF#8 := by
    rcases hdom with h | h | h
    · exact absurd h hne0
    · exact absurd h hne1
    · exact h
  exact Or.inr (Or.inr (witness_lit_false_entails hw hlv0 hl hff))

theorem resolve_lit_sideCovered_of_marked {c : FullCfg} {F_cur : List (List Nat)}
    {s : FullState} {rlen : Nat} {tmp : List (BitVec 32)} {lm : List (BitVec 8)}
    (htmp : ResolveTmpInv c s rlen tmp lm) {piv : Nat} {l : Nat}
    (hl : l < 2 * s.core.cur_vars) (hlmne : lm[l]? ≠ some 0#8) :
    SideCovered F_cur piv ((tmp.take rlen).map BitVec.toNat) l :=
  Or.inr (Or.inl (htmp.mem_of_lm_ne0 (by have := htmp.cur_le; omega) hlmne))

theorem entails_clause_of_subset {F : CNF Nat} {xs ys : List Nat}
    (hxs : F.EntailsClause (cnfClause xs)) (hsub : ∀ x ∈ xs, x ∈ ys) :
    F.EntailsClause (cnfClause ys) := by
  rw [CNF.entails_clause_def] at hxs ⊢
  intro α hα
  obtain ⟨x, hx, hsat⟩ := (clause_sat_cnfClause_iff α xs).mp (hxs α hα)
  exact (clause_sat_cnfClause_iff α ys).mpr ⟨x, hsub x hx, hsat⟩

theorem resolve_clause_step_push {c : FullCfg} {F_cur : List (List Nat)}
    {s : FullState} {rlen i piv cr : Nat} {tmp : List (BitVec 32)} {lm : List (BitVec 8)}
    {R0 : List Nat}
    (htmp : ResolveTmpInv c s rlen tmp lm)
    (hsub0 : ∀ z ∈ R0, z ∈ (tmp.take rlen).map BitVec.toNat)
    (hcov : ∀ k < i, SideCovered F_cur piv ((tmp.take rlen).map BitVec.toNat)
      (s.core.arena[cr + 3 + k]?.getD 0#32).toNat)
    (hi_ar : cr + 3 + i < s.core.arena.length)
    {l : BitVec 32} (hl_eq : s.core.arena[cr + 3 + i]'hi_ar = l)
    (hl : l.toNat < 2 * s.core.cur_vars)
    (hlm0 : lm[l.toNat]? = some 0#8) (hlm1 : lm[l.toNat ^^^ 1]? = some 0#8) :
    rlen < s.core.cur_vars ∧
    ResolveTmpInv c s (rlen + 1) (tmp.set rlen l) (lm.set l.toNat 1#8) ∧
    (∀ z ∈ R0, z ∈ ((tmp.set rlen l).take (rlen + 1)).map BitVec.toNat) ∧
    (∀ k < i + 1, SideCovered F_cur piv (((tmp.set rlen l).take (rlen + 1)).map BitVec.toNat)
      (s.core.arena[cr + 3 + k]?.getD 0#32).toNat) := by
  obtain ⟨hrlt, hinv', hsub', hmem⟩ := htmp.push hl hlm0 hlm1
  refine ⟨hrlt, hinv', fun z hz => hsub' z (hsub0 z hz), fun k hk => ?_⟩
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | rfl
  · exact (hcov k hlt).mono hsub'
  · rw [List.getElem?_eq_getElem hi_ar, Option.getD_some, hl_eq]
    exact Or.inr (Or.inl hmem)

theorem resolve_clause_step_keep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {rlen i piv cr : Nat} {tmp : List (BitVec 32)} {lm : List (BitVec 8)}
    (hw : FullWitnessInv c F0 F_cur s.core) (hlv0 : s.core.cur_level = 0)
    (htmp : ResolveTmpInv c s rlen tmp lm)
    (hcov : ∀ k < i, SideCovered F_cur piv ((tmp.take rlen).map BitVec.toNat)
      (s.core.arena[cr + 3 + k]?.getD 0#32).toNat)
    (hi_ar : cr + 3 + i < s.core.arena.length)
    (hl_eq : (s.core.arena[cr + 3 + i]'hi_ar).toNat = piv ∨
      ((s.core.arena[cr + 3 + i]'hi_ar).toNat < 2 * s.core.cur_vars ∧
        (¬ BitVec.slt 0#8 (s.core.vals[(s.core.arena[cr + 3 + i]'hi_ar).toNat]?.getD 0#8) ∧
         (s.core.vals[(s.core.arena[cr + 3 + i]'hi_ar).toNat]?.getD 0#8 ≠ 0#8 ∨
          lm[(s.core.arena[cr + 3 + i]'hi_ar).toNat]? ≠ some 0#8)))) :
    ∀ k < i + 1, SideCovered F_cur piv ((tmp.take rlen).map BitVec.toNat)
      (s.core.arena[cr + 3 + k]?.getD 0#32).toNat := by
  intro k hk
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | rfl
  · exact hcov k hlt
  · rw [List.getElem?_eq_getElem hi_ar, Option.getD_some]
    rcases hl_eq with hpiv | ⟨hl_lt, hsgt, hne0 | hlmne⟩
    · exact Or.inl hpiv
    · exact resolve_lit_sideCovered_of_val_ne0 hw hlv0 hl_lt hsgt hne0
    · exact resolve_lit_sideCovered_of_marked htmp hl_lt hlmne

theorem resolve_clause_finish {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {cr sz piv : Nat} {R : List Nat}
    (hw : FullWitnessInv c F0 F_cur s.core) (hcl : s.core.LengthsOk c)
    (href : cr ∈ fullArenaClauseRefs s) (hgarb : fullArenaClauseGarb s cr = false)
    (hsz : sz = fullArenaClauseSize s cr)
    (hcov : ∀ k < sz, SideCovered F_cur piv R (s.core.arena[cr + 3 + k]?.getD 0#32).toNat) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause (piv :: R)) := by
  have hwf := hw.arena.refs_wf cr href
  have harl := hcl.arena_len_arr; have harle := hcl.arena_len_le
  have hbd : cr + 3 + fullArenaClauseSizeCore s.core cr ≤ s.core.arena.length := by
    unfold fullArenaClauseSizeCore at hwf ⊢; omega
  refine side_entails_of_clause (hw.arena.entails cr href hgarb) fun x hx => ?_
  unfold fullArenaClauseLits at hx
  rw [mem_fullArenaClauseLitsCore_iff hbd] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  have hcovk := hcov k (by rw [hsz]; exact hk)
  rwa [List.getElem?_eq_getElem (by unfold fullArenaClauseSizeCore at hbd; omega),
    Option.getD_some] at hcovk

theorem bv8_eq_zero_of_zext32 {x : BitVec 8} (h : BitVec.setWidth 32 x = 0#32) : x = 0#8 := by
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat h
  simpa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 32)] using this

theorem bv8_eq_zero_of_sext32 {x : BitVec 8} (h : BitVec.signExtend 32 x = 0#32) : x = 0#8 := by
  apply BitVec.eq_of_toInt_eq
  have := congrArg BitVec.toInt h
  simpa [BitVec.toInt_signExtend_of_le (by decide : 8 ≤ 32)] using this

theorem bv8_sgt0_of_sext32 {x : BitVec 8}
    (h : BitVec.slt 0#32 (BitVec.signExtend 32 x) = false) : ¬ BitVec.slt 0#8 x := by
  intro hlt
  simp only [BitVec.slt, BitVec.toInt_zero, BitVec.toInt_signExtend_of_le (by decide : 8 ≤ 32),
    decide_eq_true_eq, decide_eq_false_iff_not] at h hlt
  exact h hlt

end FullBveBvaHelpers

section
open FullBveBvaTactics FullBveBvaSpecs FullBveBvaHelpers
open scoped FullArenaTactics FullBveBvaTactics

private def ResolvePcPost (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (v rlen : BitVec 32) (taut : Bool) (m_pc : Mem 64) : Prop :=
  ∃ (lm_pc : List (BitVec 8)) (tmp_pc : List (BitVec 32)),
    ResolveTmpInv c s rlen.toNat tmp_pc lm_pc ∧
    (taut = false →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause (2 * v.toNat :: (tmp_pc.take rlen.toNat).map BitVec.toNat))) ∧
    (FullMem c { s with core := { s.core with lit_mark := lm_pc, tmp := tmp_pc } } ⋆ R) m_pc

private def ResolveNcPost (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (rlen : BitVec 32) (taut : Bool) (m_nc : Mem 64) : Prop :=
  ∃ (lm_nc : List (BitVec 8)) (tmp_nc : List (BitVec 32)),
    ResolveTmpInv c s rlen.toNat tmp_nc lm_nc ∧
    (taut = false →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((tmp_nc.take rlen.toNat).map BitVec.toNat))) ∧
    (FullMem c { s with core := { s.core with lit_mark := lm_nc, tmp := tmp_nc } } ⋆ R) m_nc

private def ResolveClrInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (rlen' : BitVec 32) (tmp_nc : List (BitVec 32)) (k : BitVec 32) (mk : Mem 64) : Prop :=
  k.toNat ≤ rlen'.toNat ∧
  ∃ lm_k : List (BitVec 8),
    lm_k.length = 2 * c.max_vars ∧
    (∀ l < 2 * c.max_vars,
      ((∃ r < k.toNat, (tmp_nc[r]?.getD 0#32).toNat = l) ∨
       (∀ r < rlen'.toNat, (tmp_nc[r]?.getD 0#32).toNat ≠ l)) →
      lm_k[l]? = some 0#8) ∧
    (FullMem c { s with core := { s.core with lit_mark := lm_k, tmp := tmp_nc } } ⋆ R) mk

private def ResolveNcLoopInv (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (v nc : BitVec 32) (nsz : Nat) (rlen : BitVec 32)
    (tmp_pc : List (BitVec 32)) (rli ii : BitVec 32) (mi : Mem 64) : Prop :=
  ii.toNat ≤ nsz ∧
  ∃ lmi tmpi,
    ResolveTmpInv c s rli.toNat tmpi lmi ∧
    (∀ z ∈ (tmp_pc.take rlen.toNat).map BitVec.toNat,
      z ∈ (tmpi.take rli.toNat).map BitVec.toNat) ∧
    (∀ k < ii.toNat, SideCovered F_cur (2 * v.toNat + 1)
      ((tmpi.take rli.toNat).map BitVec.toNat)
      (s.core.arena[nc.toNat + 3 + k]?.getD 0#32).toNat) ∧
    (FullMem c { s with core := { s.core with lit_mark := lmi, tmp := tmpi } } ⋆ R) mi

private def ResolvePcLoopInv (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (v pc : BitVec 32) (psz : Nat)
    (rli ii : BitVec 32) (mi : Mem 64) : Prop :=
  ii.toNat ≤ psz ∧
  ∃ lmi tmpi,
    ResolveTmpInv c s rli.toNat tmpi lmi ∧
    (∀ k < ii.toNat, SideCovered F_cur (2 * v.toNat)
      ((tmpi.take rli.toNat).map BitVec.toNat)
      (s.core.arena[pc.toNat + 3 + k]?.getD 0#32).toNat) ∧
    (FullMem c { s with core := { s.core with lit_mark := lmi, tmp := tmpi } } ⋆ R) mi

private def resolveClrExpr (hdr pTmp pLitMark : Val i64) (rlen : Val i32)
    (taut : Val Ty.bool) : Expr Val Cont [Ty.bool] :=
  Expr.group (sig := [[i32]]) (fun Js => Blocks.cons (fun p =>
    Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i32) (Arg.var p.fst, Arg.var rlen, ())) fun p_2 =>
    Expr.jnz (Arg.var p_2.fst)
      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p.fst, ())) fun p1 =>
       Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p1.fst, Arg.imm 4, ())) fun p2 =>
       Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pTmp, Arg.var p2.fst, ())) fun p3 =>
       Expr.load i32 (Arg.var p3.fst) fun ld =>
       Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld, ())) fun p4 =>
       Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pLitMark, Arg.var p4.fst, ())) fun p5 =>
       Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p_3 =>
       Expr.store (Arg.var p_3.fst) (Arg.var p5.fst)
         (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p.fst, Arg.imm 1, ())) fun p6 =>
          Expr.jump Js.fst (Arg.var p6.fst, ())))
      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var rlen, ())) fun p_3 =>
       Expr.let_ (Op.mk (OpCode.add i64) (Arg.var hdr, Arg.imm 192, ())) fun p_4 =>
       Expr.store (Arg.var p_3.fst) (Arg.var p_4.fst)
         (Expr.let_ (Op.mk (OpCode.not Ty.bool) (Arg.var taut, ())) fun p7 =>
          Expr.ret (Arg.var p7.fst, ())))) Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.imm 0, ())

private def resolveLoopExpr (c : FullCfg) (J : Cont [i32, Ty.bool, i32])
    (cr sz piv : Val i32) (rlen0 : Arg Val i32) : Expr Val Cont [Ty.bool] :=
  Expr.group (sig := [[i32, i32]]) (fun Js => Blocks.cons (fun p =>
    Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i32) (Arg.var p.snd.fst, Arg.var sz, ())) fun p_1 =>
    Expr.jnz (Arg.var p_1.fst)
      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var cr, ())) fun p_2 =>
       Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_2.fst, Arg.imm 3, ())) fun p_3 =>
       Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p.snd.fst, ())) fun p_4 =>
       Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_3.fst, Arg.var p_4.fst, ())) fun p_5 =>
       Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_5.fst, Arg.imm 4, ())) fun p_6 =>
       Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pArena, Arg.var p_6.fst, ())) fun p_7 =>
       Expr.load i32 (Arg.var p_7.fst) fun ld =>
       Expr.group (sig := [[i32, Ty.bool]]) (fun Js_1 => Blocks.cons (fun p_8 =>
         Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p.snd.fst, Arg.imm 1, ())) fun p_9 =>
         Expr.jump Js.fst (Arg.var p_8.fst, Arg.var p_9.fst, ())) Blocks.nil)
         fun Js_2 =>
         Expr.let_ (Op.mk (OpCode.cmp CmpOp.ne i32) (Arg.var ld, Arg.var piv, ())) fun p_8 =>
         Expr.jnz (Arg.var p_8.fst)
           (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld, ())) fun p_9 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pVals, Arg.var p_9.fst, ())) fun p_10 =>
            Expr.load i8 (Arg.var p_10.fst) fun ld_1 =>
            Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p_11 =>
            Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var ld_1, ())) fun p_12 =>
            Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p_11.fst, ())) fun p_13 =>
            Expr.let_ (Op.mk (OpCode.cmp CmpOp.sgt i32)
                (Arg.var p_12.fst, Arg.var p_13.fst, ())) fun p_14 =>
            Expr.jnz (Arg.var p_14.fst)
              (Expr.jump J (Arg.var p.fst, Arg.imm true, Arg.var p.snd.fst, ()))
              (Expr.let_ (Op.mk (OpCode.xor i32) (Arg.var ld, Arg.imm 1, ())) fun p_15 =>
               Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_15.fst, ())) fun p_16 =>
               Expr.let_ (Op.mk (OpCode.add i64)
                   (Arg.var c.pLitMark, Arg.var p_16.fst, ())) fun p_17 =>
               Expr.load i8 (Arg.var p_17.fst) fun ld_2 =>
               Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p_18 =>
               Expr.let_ (Op.mk (OpCode.zext 8 32) (Arg.var ld_2, ())) fun p_19 =>
               Expr.let_ (Op.mk (OpCode.zext 8 32) (Arg.var p_18.fst, ())) fun p_20 =>
               Expr.let_ (Op.mk (OpCode.cmp CmpOp.ne i32)
                   (Arg.var p_19.fst, Arg.var p_20.fst, ())) fun p_21 =>
               Expr.jnz (Arg.var p_21.fst)
                 (Expr.jump J (Arg.var p.fst, Arg.imm true, Arg.var p.snd.fst, ()))
                 (Expr.group (sig := [[i32]]) (fun Js_3 => Blocks.cons (fun p_22 =>
                    Expr.jump Js_2.fst (Arg.var p_22.fst, Arg.imm false, ())) Blocks.nil)
                    fun Js_4 =>
                    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld, ())) fun p_22 =>
                    Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pVals, Arg.var p_22.fst, ())) fun p_23 =>
                    Expr.load i8 (Arg.var p_23.fst) fun ld_3 =>
                    Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p_24 =>
                    Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var ld_3, ())) fun p_25 =>
                    Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p_24.fst, ())) fun p_26 =>
                    Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i32)
                        (Arg.var p_25.fst, Arg.var p_26.fst, ())) fun p_27 =>
                    Expr.jnz (Arg.var p_27.fst)
                      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld, ())) fun p_28 =>
                       Expr.let_ (Op.mk (OpCode.add i64)
                           (Arg.var c.pLitMark, Arg.var p_28.fst, ())) fun p_29 =>
                       Expr.load i8 (Arg.var p_29.fst) fun ld_4 =>
                       Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p_30 =>
                       Expr.let_ (Op.mk (OpCode.zext 8 32) (Arg.var ld_4, ())) fun p_31 =>
                       Expr.let_ (Op.mk (OpCode.zext 8 32) (Arg.var p_30.fst, ())) fun p_32 =>
                       Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i32)
                           (Arg.var p_31.fst, Arg.var p_32.fst, ())) fun p_33 =>
                       Expr.jnz (Arg.var p_33.fst)
                         (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld, ())) fun p_34 =>
                          Expr.let_ (Op.mk (OpCode.add i64)
                              (Arg.var c.pLitMark, Arg.var p_34.fst, ())) fun p_35 =>
                          Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 1, ())) fun p_36 =>
                          Expr.store (Arg.var p_36.fst) (Arg.var p_35.fst)
                            (Expr.let_ (Op.mk (OpCode.zext 32 64)
                                 (Arg.var p.fst, ())) fun p_37 =>
                             Expr.let_ (Op.mk (OpCode.mul i64)
                                 (Arg.var p_37.fst, Arg.imm 4, ())) fun p_38 =>
                             Expr.let_ (Op.mk (OpCode.add i64)
                                 (Arg.var c.pTmp, Arg.var p_38.fst, ())) fun p_39 =>
                             Expr.store (Arg.var ld) (Arg.var p_39.fst)
                               (Expr.let_ (Op.mk (OpCode.add i32)
                                    (Arg.var p.fst, Arg.imm 1, ())) fun p_40 =>
                                Expr.jump Js_4.fst (Arg.var p_40.fst, ()))))
                         (Expr.jump Js_4.fst (Arg.var p.fst, ())))
                      (Expr.jump Js_4.fst (Arg.var p.fst, ())))))
           (Expr.jump Js_2.fst (Arg.var p.fst, Arg.imm false, ())))
      (Expr.jump J (Arg.var p.fst, Arg.imm false, Arg.var p.snd.fst, ()))) Blocks.nil)
    fun Js => Expr.jump Js.fst (rlen0, Arg.imm 0, ())

private theorem resolve_pair_clr_wp (Γ : Env) (Q : Post [Ty.bool]) (X : XPost)
    (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop)
    (hdw : FullDenseInvW c F0 F_cur s)
    (hQ : ∀ (ok : Bool) lm' tmp' tl' m',
      let s' : FullState :=
        { s with core := { s.core with lit_mark := lm', tmp := tmp', tmp_len := tl' } }
      FullDenseInvW c F0 F_cur s' → tl' ≤ s.core.cur_vars →
      (ok = true → (∀ k < tl', (tmp'[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
        ((tmp'.take tl').map fun x => x.toNat / 2).Nodup ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat))) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m')
    (rlen' : Val i32) (taut' : Val Ty.bool) (m_nc : Mem 64)
    (hp : ResolveNcPost c F_cur s R rlen' taut' m_nc) :
    wp Γ Q X (resolveClrExpr c.hdr c.pTmp c.pLitMark rlen' taut') m_nc := by
  have hcl := hdw.1.core_ok; have hcv := hcl.cur_vars_le
  rcases hp with ⟨lm_nc, tmp_nc, hrt_nc, hnc_ent, hm_nc⟩
  unfold resolveClrExpr
  refine wp_loop_inv (ts := [i32])
    (fun (k, _) mk => ResolveClrInv c s R rlen' tmp_nc k mk)
    (fun (k, _) _ => rlen'.toNat - k.toNat) ?_ ?_
  · intro Jk hJk; bve_steps!
    exact hJk (0#32, PUnit.unit) m_nc ⟨Nat.zero_le _, lm_nc, hrt_nc.lm_len,
      fun l hl hc => by
        rcases hc with ⟨r, hr, _⟩ | hnone
        · bv_omega
        · exact hrt_nc.unmarked l hl hnone, hm_nc⟩
  · rintro Jk ⟨k, ⟨⟩⟩ mk ⟨hk_le, lm_k, hlml_k, hcov_k, hm_k⟩ ihk
    bve_steps
    · have hk_lt : k.toNat < rlen'.toNat := by bv_omega
      have hk_tmp : k.toNat < tmp_nc.length := by
        rw [hrt_nc.tmp_len]; exact Nat.lt_of_lt_of_le hk_lt (Nat.le_trans hrt_nc.rlen_le hcv)
      have hl_lt : (tmp_nc[k.toNat]'hk_tmp).toNat < 2 * c.max_vars := by
        have := hrt_nc.lits_lt k.toNat hk_lt
        rw [List.getElem?_eq_getElem hk_tmp, Option.getD_some] at this; omega
      have hk_lm : (BitVec.setWidth 64 (tmp_nc[(BitVec.setWidth 64 k).toNat]'(by
          rw [bv_c0_zext32_64]; exact hk_tmp))).toNat < lm_k.length := by
        simp only [bv_c0_zext32_64] at *; rw [hlml_k]; exact hl_lt
      bve_steps!
      have hcov' := tmpMark_clear_step (n := 2 * c.max_vars) hk_tmp hl_lt hlml_k hcov_k
      refine ihk (k + 1#32, PUnit.unit) _ (by bv_omega)
        ⟨by bv_omega, lm_k.set (tmp_nc[k.toNat]'hk_tmp).toNat 0#8, by simp [hlml_k],
          fun l hl hc => ?_, ?_⟩
      · rw [show (k + 1#32).toNat = k.toNat + 1 from by bv_omega] at hc
        exact hcov' l hl hc
      · simp only [bv_c0_zext32_64] at hm ⊢; exact hm
    · have hk_eq : k.toNat = rlen'.toNat := by bv_omega
      have hlz : ∀ l < 2 * c.max_vars, lm_k[l]?.getD 0#8 = 0#8 := fun l hl => by
        have h0 : lm_k[l]? = some 0#8 := hcov_k l hl (by
          by_cases hex : ∃ r < rlen'.toNat, (tmp_nc[r]?.getD 0#32).toNat = l
          · exact Or.inl (hk_eq ▸ hex)
          · exact Or.inr fun r hr heq => hex ⟨r, hr, heq⟩)
        rw [h0, Option.getD_some]
      bve_steps!
      have hinv' := fullDenseInvW_with_tmp_litMark hdw hlml_k hrt_nc.tmp_len
        (Nat.le_trans hrt_nc.rlen_le hcv) hlz
      refine hQ (!taut') lm_k tmp_nc rlen'.toNat _ hinv' hrt_nc.rlen_le (fun hok => ?_) ?_
      · have htf : taut' = false := by revert hok; cases taut' <;> decide
        refine ⟨hrt_nc.lits_lt, hrt_nc.vars_nodup, hnc_ent htf⟩
      · simpa only [bv_c0_zext32_64] using hm

private theorem resolve_pair_nc_loop_wp (Γ : Env) (Q : Post [Ty.bool]) (X : XPost)
    (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop)
    (v nc nsz rlen : Val i32) (hw : FullWitnessInv c F0 F_cur s.core)
    (hcl : FullCoreState.LengthsOk c s.core) (hlv0 : s.core.cur_level = 0)
    (hnl_nat : ((v <<< 1) ||| 1#32).toNat = 2 * v.toNat + 1)
    (lm_pc : List (BitVec 8)) (tmp_pc : List (BitVec 32))
    (hrt_pc : ResolveTmpInv c s rlen.toNat tmp_pc lm_pc)
    (hpc_ent' : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (2 * v.toNat :: (tmp_pc.take rlen.toNat).map BitVec.toNat)))
    (hnc_ref : nc.toNat ∈ fullArenaClauseRefs s)
    (hnc_garb : fullArenaClauseGarb s nc.toNat = false)
    (hnsz_nat : nsz.toNat = fullArenaClauseSize s nc.toNat)
    (hnc_bd : nc.toNat + 3 + nsz.toNat ≤ s.core.arena_len)
    (J_nc : Cont [i32, Ty.bool])
    (hAfterNc : ∀ (rlen' : Val i32) (taut' : Val .bool) (m_nc : Mem 64),
      ResolveNcPost c F_cur s R rlen' taut' m_nc → J_nc (rlen', taut', PUnit.unit) m_nc)
    (J : Cont [i32, Ty.bool, i32])
    (hJ : ∀ (xs : Tup Val [i32, Ty.bool, i32]) (m' : Mem 64),
      wp Γ Q X ((Blocks.cons (fun (p : Tup Val [i32, Ty.bool, i32]) =>
        Expr.jump J_nc (Arg.var p.fst, Arg.var p.snd.fst, ()))
        Blocks.nil).get Member.here xs) m' → J xs m')
    (m_pc : Mem 64)
    (hm_pc : (FullMem c { s with core := { s.core with lit_mark := lm_pc, tmp := tmp_pc } } ⋆ R)
      m_pc) :
    wp Γ Q X (resolveLoopExpr c J nc nsz ((v <<< 1) ||| 1#32) (Arg.var rlen)) m_pc := by
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have hcv := hcl.cur_vars_le; have harl := hcl.arena_len_arr
  have harle := hcl.arena_len_le; have hvalsl := hcl.vals_len
  unfold resolveLoopExpr
  refine wp_loop_inv (ts := [i32, i32])
    (fun (rli, ii, _) mi => ResolveNcLoopInv c F_cur s R v nc nsz.toNat rlen tmp_pc rli ii mi)
    (fun (_, ii, _) _ => nsz.toNat - ii.toNat) ?_ ?_
  · intro Ji hJi; bve_steps!
    exact hJi (rlen, 0#32, PUnit.unit) m_pc ⟨Nat.zero_le _, lm_pc, tmp_pc, hrt_pc,
      fun _ hz => hz, fun _ hk => by exfalso; bv_omega, hm_pc⟩
  · rintro Ji ⟨rli, ii, ⟨⟩⟩ mi ⟨hii_le, lmi, tmpi, hrti, hsub_i, hcov_i, hm_i⟩ ihi
    bve_steps
    · have hii_lt : ii.toNat < nsz.toNat := by bv_omega
      have hi1_eq : (ii + 1#32).toNat = ii.toNat + 1 :=
        bv32_add1_toNat hii_lt (by have := hnc_bd; omega)
      have hmu_dec : nsz.toNat - (ii + 1#32).toNat < nsz.toNat - ii.toNat := by omega
      have hii1_le : (ii + 1#32).toNat ≤ nsz.toNat := by omega
      have har_idx : (BitVec.setWidth 64 nc + 3 + BitVec.setWidth 64 ii).toNat <
          s.core.arena.length := by bv_omega
      have har_nat : (BitVec.setWidth 64 nc + 3 + BitVec.setWidth 64 ii).toNat =
          nc.toNat + 3 + ii.toNat := by bv_omega
      have hc_idx : (nc.toNat + (3 : BitVec 64).toNat + ii.toNat) % 2 ^ 64 =
          nc.toNat + 3 + ii.toNat := by bv_omega
      let l := s.core.arena[nc.toNat + 3 + ii.toNat]'(by omega)
      have hl_nc : l.toNat < 2 * s.core.cur_vars := by
        apply hw.arena.lits_lt nc.toNat hnc_ref hnc_garb
        have hbd_nc : nc.toNat + 3 + fullArenaClauseSize s nc.toNat ≤
            s.core.arena.length := by rw [← hnsz_nat]; omega
        rw [mem_fullArenaClauseLitsCore_iff hbd_nc]
        exact ⟨ii.toNat, by simpa [fullArenaClauseSize, ← hnsz_nat] using hii_lt, rfl⟩
      have hl_mv : l.toNat < 2 * c.max_vars := by omega
      have hl1_mv : (l ^^^ 1#32).toNat < 2 * c.max_vars := bv32_xor_1_lt hl_mv
      have hl_vals : (BitVec.setWidth 64
          (s.core.arena[(nc.setWidth 64 + 3 + ii.setWidth 64).toNat]'har_idx)).toNat <
          s.core.vals.length := by
        rw [bv_c0_zext32_64, hvalsl]; simp only [har_nat]; exact hl_mv
      have hl1_lm : (BitVec.setWidth 64
          ((s.core.arena[(nc.setWidth 64 + 3 + ii.setWidth 64).toNat]'har_idx) ^^^
            1#32)).toNat < lmi.length := by
        rw [bv_c0_zext32_64, hrti.lm_len]; simp only [har_nat]; exact hl1_mv
      have hl_lm : (BitVec.setWidth 64
          (s.core.arena[(nc.setWidth 64 + 3 + ii.setWidth 64).toNat]'har_idx)).toNat <
          lmi.length := by
        rw [bv_c0_zext32_64, hrti.lm_len]; simp only [har_nat]; exact hl_mv
      bve_steps
      · exact hAfterNc rli true mi ⟨lmi, tmpi, hrti, fun h => Bool.noConfusion h, hm_i⟩
      · exact hAfterNc rli true mi ⟨lmi, tmpi, hrti, fun h => Bool.noConfusion h, hm_i⟩
      · have hi_ar2 : nc.toNat + 3 + ii.toNat < s.core.arena.length := by omega
        have hlm0 : lmi[l.toNat]? = some 0#8 := by
          rw [List.getElem?_eq_getElem (by rw [hrti.lm_len]; exact hl_mv), Option.some.injEq]
          have hhc : BitVec.setWidth 32 (lmi[(s.core.arena[(BitVec.toNat nc + BitVec.toNat 3 +
              BitVec.toNat ii) % 2 ^ 64]'(by rw [hc_idx]; omega)).toNat]'(by
              simp only [hc_idx, hrti.lm_len]; exact hl_mv)) = 0#32 := hc
          simp only [hc_idx] at hhc; exact bv8_eq_zero_of_zext32 hhc
        have hlm1 : lmi[l.toNat ^^^ 1]? = some 0#8 := by
          rw [List.getElem?_eq_getElem (by rw [hrti.lm_len]; exact hl1_mv), Option.some.injEq]
          have hna : BitVec.setWidth 32 (lmi[(s.core.arena[(BitVec.toNat nc + BitVec.toNat 3 +
              BitVec.toNat ii) % 2 ^ 64]'(by rw [hc_idx]; omega)).toNat ^^^ 1]'(by
              simp only [hc_idx, hrti.lm_len]; exact hl1_mv)) = 0#32 := by assumption
          simp only [hc_idx] at hna; exact bv8_eq_zero_of_zext32 hna
        have hrlt : rli.toNat < tmpi.length := by
          rw [hrti.tmp_len]
          exact Nat.lt_of_lt_of_le (hrti.rlen_lt_of_unmarked hl_nc hlm0 hlm1) hcv
        have hr_tmp : (BitVec.setWidth 64 rli).toNat < tmpi.length := by
          rw [bv_c0_zext32_64]; exact hrlt
        bve_steps!
        obtain ⟨hrlt', hrt', hsub', hcov'⟩ := resolve_clause_step_push hrti
          hsub_i hcov_i hi_ar2 rfl hl_nc hlm0 hlm1
        have hr1_eq : (rli + 1#32).toNat = rli.toNat + 1 := bv32_add1_toNat hrlt' (by omega)
        refine ihi (rli + 1#32, ii + 1#32, PUnit.unit) _ hmu_dec
          ⟨hii1_le, _, _, by rw [hr1_eq]; exact hrt', by rw [hr1_eq]; exact hsub',
            by rw [hr1_eq, hi1_eq]; exact hcov', ?_⟩
        simp only [bv_c0_zext32_64, har_nat] at hm ⊢; exact hm
      · have hhs : (0#32).slt (BitVec.signExtend 32 (s.core.vals[(s.core.arena[(
            BitVec.toNat nc + BitVec.toNat 3 + BitVec.toNat ii) % 2 ^ 64]'(by
            rw [hc_idx]; omega)).toNat]'(by
            simp only [hc_idx, hvalsl]; exact hl_mv))) = false := by assumption
        simp only [hc_idx] at hhs
        have hsgt : ¬ BitVec.slt 0#8 (s.core.vals[l.toNat]?.getD 0#8) := by
          rw [List.getElem?_eq_getElem (by rw [hvalsl]; exact hl_mv), Option.getD_some]
          exact bv8_sgt0_of_sext32 hhs
        have hlmne : lmi[l.toNat]? ≠ some 0#8 := by
          intro h0
          rw [List.getElem?_eq_getElem (by rw [hrti.lm_len]; exact hl_mv), Option.some.injEq] at h0
          have h0z : BitVec.setWidth 32 (lmi[(s.core.arena[(BitVec.toNat nc +
              BitVec.toNat (3 : BitVec 64) + BitVec.toNat ii) % 2 ^ 64]'(by
              rw [hc_idx]; omega)).toNat]'(by
              simp only [hc_idx, hrti.lm_len]; exact hl_mv)) = 0#32 := by
            simp only [hc_idx]; rw [h0]; rfl
          exact absurd h0z hc
        refine ihi (rli, ii + 1#32, PUnit.unit) mi hmu_dec
          ⟨hii1_le, lmi, tmpi, hrti, hsub_i, ?_, hm_i⟩
        rw [hi1_eq]
        exact resolve_clause_step_keep hw hlv0 hrti hcov_i (by omega)
          (Or.inr ⟨hl_nc, hsgt, Or.inr hlmne⟩)
      · have hhs : (0#32).slt (BitVec.signExtend 32 (s.core.vals[(s.core.arena[(
            BitVec.toNat nc + BitVec.toNat 3 + BitVec.toNat ii) % 2 ^ 64]'(by
            rw [hc_idx]; omega)).toNat]'(by
            simp only [hc_idx, hvalsl]; exact hl_mv))) = false := by assumption
        simp only [hc_idx] at hhs
        have hsgt : ¬ BitVec.slt 0#8 (s.core.vals[l.toNat]?.getD 0#8) := by
          rw [List.getElem?_eq_getElem (by rw [hvalsl]; exact hl_mv), Option.getD_some]
          exact bv8_sgt0_of_sext32 hhs
        have hv0 : s.core.vals[l.toNat]?.getD 0#8 ≠ 0#8 := fun h0 => by
          rw [List.getElem?_eq_getElem (by rw [hvalsl]; exact hl_mv), Option.getD_some] at h0
          have h0z : BitVec.signExtend 32 (s.core.vals[(s.core.arena[(BitVec.toNat nc +
              BitVec.toNat (3 : BitVec 64) + BitVec.toNat ii) % 2 ^ 64]'(by
              rw [hc_idx]; omega)).toNat]'(by
              simp only [hc_idx, hvalsl]; exact hl_mv)) = 0#32 := by
            simp only [hc_idx]; rw [h0]; rfl
          exact absurd h0z hc
        refine ihi (rli, ii + 1#32, PUnit.unit) mi hmu_dec
          ⟨hii1_le, lmi, tmpi, hrti, hsub_i, ?_, hm_i⟩
        rw [hi1_eq]
        exact resolve_clause_step_keep hw hlv0 hrti hcov_i (by omega)
          (Or.inr ⟨hl_nc, hsgt, Or.inl hv0⟩)
    · have hii_lt : ii.toNat < nsz.toNat := by assumption
      have hi1_eq : (ii + 1#32).toNat = ii.toNat + 1 :=
        bv32_add1_toNat hii_lt (by have := hnc_bd; omega)
      have hc_idx : (nc.toNat + (3 : BitVec 64).toNat + ii.toNat) % 2 ^ 64 =
          nc.toNat + 3 + ii.toNat := by bv_omega
      refine ihi (rli, ii + 1#32, PUnit.unit) mi (by dsimp only; rw [hi1_eq]; omega)
        ⟨by omega, lmi, tmpi, hrti, hsub_i, ?_, hm_i⟩
      rw [hi1_eq]
      exact resolve_clause_step_keep hw hlv0 hrti hcov_i (by omega) (Or.inl (by
        have heq := congrArg BitVec.toNat hc
        simp only [hc_idx] at heq; rw [← hnl_nat]; exact heq))
    · have hii_eq : ii.toNat = nsz.toNat := Nat.le_antisymm hii_le (Nat.not_lt.mp hc)
      refine hAfterNc rli false mi ⟨lmi, tmpi, hrti, fun _ => ?_, hm_i⟩
      have hp_new := entails_clause_of_subset hpc_ent' fun z hz => by
        rw [List.mem_cons] at hz ⊢
        rcases hz with rfl | hz
        · exact Or.inl rfl
        · exact Or.inr (hsub_i z hz)
      have hn_new := resolve_clause_finish hw hcl hnc_ref hnc_garb hnsz_nat (hii_eq ▸ hcov_i)
      exact resolve_pivots_entails hp_new hn_new

private theorem resolve_pair_pc_loop_wp (Γ : Env) (Q : Post [Ty.bool]) (X : XPost)
    (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop)
    (v pc psz : Val i32) (hw : FullWitnessInv c F0 F_cur s.core)
    (hcl : FullCoreState.LengthsOk c s.core) (hlv0 : s.core.cur_level = 0)
    (hlmc : ∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8)
    (hpl_nat : (v <<< 1).toNat = 2 * v.toNat)
    (hpc_ref : pc.toNat ∈ fullArenaClauseRefs s)
    (hpc_garb : fullArenaClauseGarb s pc.toNat = false)
    (hpsz_nat : psz.toNat = fullArenaClauseSize s pc.toNat)
    (hpc_bd : pc.toNat + 3 + psz.toNat ≤ s.core.arena_len)
    (J_pc : Cont [i32, Ty.bool])
    (hAfterPc : ∀ (rlen : Val i32) (taut : Val .bool) (m_pc : Mem 64),
      ResolvePcPost c F_cur s R v rlen taut m_pc → J_pc (rlen, taut, PUnit.unit) m_pc)
    (J : Cont [i32, Ty.bool, i32])
    (hJ : ∀ (xs : Tup Val [i32, Ty.bool, i32]) (m' : Mem 64),
      wp Γ Q X ((Blocks.cons (fun (p : Tup Val [i32, Ty.bool, i32]) =>
        Expr.jump J_pc (Arg.var p.fst, Arg.var p.snd.fst, ()))
        Blocks.nil).get Member.here xs) m' → J xs m')
    (m : Mem 64) (hm : (FullMem c s ⋆ R) m) :
    wp Γ Q X (resolveLoopExpr c J pc psz (v <<< 1) (Arg.imm 0)) m := by
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have hcv := hcl.cur_vars_le; have harl := hcl.arena_len_arr
  have harle := hcl.arena_len_le; have hvalsl := hcl.vals_len
  unfold resolveLoopExpr
  refine wp_loop_inv (ts := [i32, i32])
    (fun (rli, ii, _) mi => ResolvePcLoopInv c F_cur s R v pc psz.toNat rli ii mi)
    (fun (_, ii, _) _ => psz.toNat - ii.toNat) ?_ ?_
  · intro Ji hJi; bve_steps!
    exact hJi (0#32, 0#32, PUnit.unit) m ⟨Nat.zero_le _, s.core.lit_mark, s.core.tmp,
      ResolveTmpInv.init hcl hlmc, fun _ hk => by exfalso; bv_omega, hm⟩
  · rintro Ji ⟨rli, ii, ⟨⟩⟩ mi ⟨hii_le, lmi, tmpi, hrti, hcov_i, hm_i⟩ ihi
    bve_steps
    · have hii_lt : ii.toNat < psz.toNat := by bv_omega
      have hi1_eq : (ii + 1#32).toNat = ii.toNat + 1 :=
        bv32_add1_toNat hii_lt (by have := hpc_bd; omega)
      have hmu_dec : psz.toNat - (ii + 1#32).toNat < psz.toNat - ii.toNat := by omega
      have hii1_le : (ii + 1#32).toNat ≤ psz.toNat := by omega
      have har_idx : (BitVec.setWidth 64 pc + 3 + BitVec.setWidth 64 ii).toNat <
          s.core.arena.length := by bv_omega
      have har_nat : (BitVec.setWidth 64 pc + 3 + BitVec.setWidth 64 ii).toNat =
          pc.toNat + 3 + ii.toNat := by bv_omega
      have hc_idx : (pc.toNat + (3 : BitVec 64).toNat + ii.toNat) % 2 ^ 64 =
          pc.toNat + 3 + ii.toNat := by bv_omega
      let l := s.core.arena[pc.toNat + 3 + ii.toNat]'(by omega)
      have hl_pc : l.toNat < 2 * s.core.cur_vars := by
        apply hw.arena.lits_lt pc.toNat hpc_ref hpc_garb
        have hbd_pc : pc.toNat + 3 + fullArenaClauseSize s pc.toNat ≤
            s.core.arena.length := by rw [← hpsz_nat]; omega
        rw [mem_fullArenaClauseLitsCore_iff hbd_pc]
        exact ⟨ii.toNat, by simpa [fullArenaClauseSize, ← hpsz_nat] using hii_lt, rfl⟩
      have hl_mv : l.toNat < 2 * c.max_vars := by omega
      have hl1_mv : (l ^^^ 1#32).toNat < 2 * c.max_vars := bv32_xor_1_lt hl_mv
      have hl_vals : (BitVec.setWidth 64
          (s.core.arena[(pc.setWidth 64 + 3 + ii.setWidth 64).toNat]'har_idx)).toNat <
          s.core.vals.length := by
        rw [bv_c0_zext32_64, hvalsl]; simp only [har_nat]; exact hl_mv
      have hl1_lm : (BitVec.setWidth 64
          ((s.core.arena[(pc.setWidth 64 + 3 + ii.setWidth 64).toNat]'har_idx) ^^^
            1#32)).toNat < lmi.length := by
        rw [bv_c0_zext32_64, hrti.lm_len]; simp only [har_nat]; exact hl1_mv
      have hl_lm : (BitVec.setWidth 64
          (s.core.arena[(pc.setWidth 64 + 3 + ii.setWidth 64).toNat]'har_idx)).toNat <
          lmi.length := by
        rw [bv_c0_zext32_64, hrti.lm_len]; simp only [har_nat]; exact hl_mv
      bve_steps
      · exact hAfterPc rli true mi ⟨lmi, tmpi, hrti, fun h => Bool.noConfusion h, hm_i⟩
      · exact hAfterPc rli true mi ⟨lmi, tmpi, hrti, fun h => Bool.noConfusion h, hm_i⟩
      · have hi_ar2 : pc.toNat + 3 + ii.toNat < s.core.arena.length := by omega
        have hlm0 : lmi[l.toNat]? = some 0#8 := by
          rw [List.getElem?_eq_getElem (by rw [hrti.lm_len]; exact hl_mv), Option.some.injEq]
          have hhc : BitVec.setWidth 32 (lmi[(s.core.arena[(BitVec.toNat pc + BitVec.toNat 3 +
              BitVec.toNat ii) % 2 ^ 64]'(by rw [hc_idx]; omega)).toNat]'(by
              simp only [hc_idx, hrti.lm_len]; exact hl_mv)) = 0#32 := hc
          simp only [hc_idx] at hhc; exact bv8_eq_zero_of_zext32 hhc
        have hlm1 : lmi[l.toNat ^^^ 1]? = some 0#8 := by
          rw [List.getElem?_eq_getElem (by rw [hrti.lm_len]; exact hl1_mv), Option.some.injEq]
          have hna : BitVec.setWidth 32 (lmi[(s.core.arena[(BitVec.toNat pc + BitVec.toNat 3 +
              BitVec.toNat ii) % 2 ^ 64]'(by rw [hc_idx]; omega)).toNat ^^^ 1]'(by
              simp only [hc_idx, hrti.lm_len]; exact hl1_mv)) = 0#32 := by assumption
          simp only [hc_idx] at hna; exact bv8_eq_zero_of_zext32 hna
        have hrlt : rli.toNat < tmpi.length := by
          rw [hrti.tmp_len]
          exact Nat.lt_of_lt_of_le (hrti.rlen_lt_of_unmarked hl_pc hlm0 hlm1) hcv
        have hr_tmp : (BitVec.setWidth 64 rli).toNat < tmpi.length := by
          rw [bv_c0_zext32_64]; exact hrlt
        bve_steps!
        obtain ⟨hrlt', hrt', _, hcov'⟩ := resolve_clause_step_push (R0 := []) hrti
          (fun _ hz => nomatch hz) hcov_i hi_ar2 rfl hl_pc hlm0 hlm1
        have hr1_eq : (rli + 1#32).toNat = rli.toNat + 1 := bv32_add1_toNat hrlt' (by omega)
        refine ihi (rli + 1#32, ii + 1#32, PUnit.unit) _ hmu_dec
          ⟨hii1_le, _, _, by rw [hr1_eq]; exact hrt',
            by rw [hr1_eq, hi1_eq]; exact hcov', ?_⟩
        simp only [bv_c0_zext32_64, har_nat] at hm ⊢; exact hm
      · have hhs : (0#32).slt (BitVec.signExtend 32 (s.core.vals[(s.core.arena[(
            BitVec.toNat pc + BitVec.toNat 3 + BitVec.toNat ii) % 2 ^ 64]'(by
            rw [hc_idx]; omega)).toNat]'(by
            simp only [hc_idx, hvalsl]; exact hl_mv))) = false := by assumption
        simp only [hc_idx] at hhs
        have hsgt : ¬ BitVec.slt 0#8 (s.core.vals[l.toNat]?.getD 0#8) := by
          rw [List.getElem?_eq_getElem (by rw [hvalsl]; exact hl_mv), Option.getD_some]
          exact bv8_sgt0_of_sext32 hhs
        have hlmne : lmi[l.toNat]? ≠ some 0#8 := by
          intro h0
          rw [List.getElem?_eq_getElem (by rw [hrti.lm_len]; exact hl_mv), Option.some.injEq] at h0
          have h0z : BitVec.setWidth 32 (lmi[(s.core.arena[(BitVec.toNat pc +
              BitVec.toNat (3 : BitVec 64) + BitVec.toNat ii) % 2 ^ 64]'(by
              rw [hc_idx]; omega)).toNat]'(by
              simp only [hc_idx, hrti.lm_len]; exact hl_mv)) = 0#32 := by
            simp only [hc_idx]; rw [h0]; rfl
          exact absurd h0z hc
        refine ihi (rli, ii + 1#32, PUnit.unit) mi hmu_dec
          ⟨hii1_le, lmi, tmpi, hrti, ?_, hm_i⟩
        rw [hi1_eq]
        exact resolve_clause_step_keep hw hlv0 hrti hcov_i (by omega)
          (Or.inr ⟨hl_pc, hsgt, Or.inr hlmne⟩)
      · have hhs : (0#32).slt (BitVec.signExtend 32 (s.core.vals[(s.core.arena[(
            BitVec.toNat pc + BitVec.toNat 3 + BitVec.toNat ii) % 2 ^ 64]'(by
            rw [hc_idx]; omega)).toNat]'(by
            simp only [hc_idx, hvalsl]; exact hl_mv))) = false := by assumption
        simp only [hc_idx] at hhs
        have hsgt : ¬ BitVec.slt 0#8 (s.core.vals[l.toNat]?.getD 0#8) := by
          rw [List.getElem?_eq_getElem (by rw [hvalsl]; exact hl_mv), Option.getD_some]
          exact bv8_sgt0_of_sext32 hhs
        have hv0 : s.core.vals[l.toNat]?.getD 0#8 ≠ 0#8 := fun h0 => by
          rw [List.getElem?_eq_getElem (by rw [hvalsl]; exact hl_mv), Option.getD_some] at h0
          have h0z : BitVec.signExtend 32 (s.core.vals[(s.core.arena[(BitVec.toNat pc +
              BitVec.toNat (3 : BitVec 64) + BitVec.toNat ii) % 2 ^ 64]'(by
              rw [hc_idx]; omega)).toNat]'(by
              simp only [hc_idx, hvalsl]; exact hl_mv)) = 0#32 := by
            simp only [hc_idx]; rw [h0]; rfl
          exact absurd h0z hc
        refine ihi (rli, ii + 1#32, PUnit.unit) mi hmu_dec
          ⟨hii1_le, lmi, tmpi, hrti, ?_, hm_i⟩
        rw [hi1_eq]
        exact resolve_clause_step_keep hw hlv0 hrti hcov_i (by omega)
          (Or.inr ⟨hl_pc, hsgt, Or.inl hv0⟩)
    · have hii_lt : ii.toNat < psz.toNat := by assumption
      have hi1_eq : (ii + 1#32).toNat = ii.toNat + 1 :=
        bv32_add1_toNat hii_lt (by have := hpc_bd; omega)
      have hc_idx : (pc.toNat + (3 : BitVec 64).toNat + ii.toNat) % 2 ^ 64 =
          pc.toNat + 3 + ii.toNat := by bv_omega
      refine ihi (rli, ii + 1#32, PUnit.unit) mi (by dsimp only; rw [hi1_eq]; omega)
        ⟨by omega, lmi, tmpi, hrti, ?_, hm_i⟩
      rw [hi1_eq]
      exact resolve_clause_step_keep hw hlv0 hrti hcov_i (by omega) (Or.inl (by
        have heq := congrArg BitVec.toNat hc
        simp only [hc_idx] at heq; rw [← hpl_nat]; exact heq))
    · have hii_eq : ii.toNat = psz.toNat := Nat.le_antisymm hii_le (Nat.not_lt.mp hc)
      exact hAfterPc rli false mi ⟨lmi, tmpi, hrti, fun _ =>
        resolve_clause_finish hw hcl hpc_ref hpc_garb hpsz_nat (hii_eq ▸ hcov_i), hm_i⟩

theorem full_bve_resolve_pair_wp (Γ : Env) :
    ∀ args m Q X, fullBveResolvePairSpec args m Q X →
      Func.wp Γ full_bve_resolve_pair_body args m Q X := by
  rintro ⟨h, v, pc, nc, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hdw, hv_lt, hpc, hnc, hm, hQ⟩
  have hmv := c.hmaxv; have harc := c.harena; unfold dimacsBound at hmv harc
  have hlen := hdw.1; have hcl := hlen.core_ok; have hw := hdw.2.1
  have hcv := hcl.cur_vars_le; have harl := hcl.arena_len_arr; have harle := hcl.arena_len_le
  have hvalsl := hcl.vals_len; have hlml := hcl.lit_mark_len; have htmpl := hcl.tmp_len_arr
  have hlmc := hdw.2.2.1.2; have hlv0 := hdw.2.2.2.2.2.1
  have hpl_nat : (v <<< 1).toNat = 2 * v.toNat := by bv_omega
  have hnl_bv : (v <<< 1) ||| 1#32 = (v <<< 1) ^^^ 1#32 := bv32_shl1_or1_eq_xor v
  have hnl_nat : ((v <<< 1) ||| 1#32).toNat = 2 * v.toNat + 1 := by
    rw [hnl_bv]; have hle := litNeg_eq (2 * v.toNat)
    simp only [litNeg, show (2 * v.toNat) % 2 = 0 by omega, ↓reduceIte] at hle
    change ((v <<< 1).toNat ^^^ 1) = _; rw [hpl_nat, hle]
  unfold Func.wp full_bve_resolve_pair_body
  bve_to_group
  refine wp_unroll_group fun J_pc hJ_pc => ?_
  try c0_let_simp
  have hAfterPc : ∀ (rlen : Val i32) (taut : Val .bool) (m_pc : Mem 64),
      ResolvePcPost c F_cur s R v rlen taut m_pc → J_pc (rlen, taut, PUnit.unit) m_pc := by
    rintro rlen taut m_pc ⟨lm_pc, tmp_pc, hrt_pc, hpc_ent, hm_pc⟩
    apply hJ_pc; bve_to_group
    refine wp_unroll_group fun J_nc hJ_nc => ?_
    try c0_let_simp
    have hAfterNc : ∀ (rlen' : Val i32) (taut' : Val .bool) (m_nc : Mem 64),
        ResolveNcPost c F_cur s R rlen' taut' m_nc → J_nc (rlen', taut', PUnit.unit) m_nc := by
      intro rlen' taut' m_nc hp
      apply hJ_nc; rw [Blocks.get_here]
      exact resolve_pair_clr_wp Γ Q X c F0 F_cur s R hdw hQ rlen' taut' m_nc hp
    clear hJ_nc
    bve_steps
    · have htt : taut = true := hc
      exact hAfterNc rlen taut m_pc
        ⟨lm_pc, tmp_pc, hrt_pc, fun h => Bool.noConfusion (htt.symm.trans h), hm_pc⟩
    · have hbin_nc : (nc &&& 0x80000000#32) ≠ 0#32 := hc
      have htf : taut = false := by assumption
      subst htf
      have hpc_ent' := hpc_ent rfl
      unfold FullBveEntryOkW at hnc; rw [ite_eq_left hbin_nc] at hnc
      obtain ⟨hl_nc, hn_ent⟩ := hnc
      have hl_mv : (nc &&& 0x7FFFFFFF#32).toNat < 2 * c.max_vars := by omega
      have hl1_mv : ((nc &&& 0x7FFFFFFF#32) ^^^ 1#32).toNat < 2 * c.max_vars :=
        bv32_xor_1_lt hl_mv
      have hl_vals : (BitVec.setWidth 64 (nc &&& 0x7FFFFFFF#32)).toNat <
          s.core.vals.length := by rw [bv_c0_zext32_64, hvalsl]; exact hl_mv
      have hl1_lm : (BitVec.setWidth 64 ((nc &&& 0x7FFFFFFF#32) ^^^ 1#32)).toNat <
          lm_pc.length := by rw [bv_c0_zext32_64, hrt_pc.lm_len]; exact hl1_mv
      have hl_lm : (BitVec.setWidth 64 (nc &&& 0x7FFFFFFF#32)).toNat < lm_pc.length := by
        rw [bv_c0_zext32_64, hrt_pc.lm_len]; exact hl_mv
      bve_steps
      · exact hAfterNc rlen true m_pc
          ⟨lm_pc, tmp_pc, hrt_pc, fun h => Bool.noConfusion h, hm_pc⟩
      · exact hAfterNc rlen true m_pc
          ⟨lm_pc, tmp_pc, hrt_pc, fun h => Bool.noConfusion h, hm_pc⟩
      · have hlm0 : lm_pc[(nc &&& 0x7FFFFFFF#32).toNat]? = some 0#8 := by
          rw [List.getElem?_eq_getElem (by rw [hrt_pc.lm_len]; exact hl_mv), Option.some.injEq]
          exact bv8_eq_zero_of_zext32 hc
        have hlm1 : lm_pc[(nc &&& 0x7FFFFFFF#32).toNat ^^^ 1]? = some 0#8 := by
          rw [List.getElem?_eq_getElem (by rw [hrt_pc.lm_len]; exact hl1_mv), Option.some.injEq]
          have hna : BitVec.setWidth 32 (lm_pc[(nc &&& 0x7FFFFFFF#32).toNat ^^^ 1]'(
              by rw [hrt_pc.lm_len]; exact hl1_mv)) = 0#32 := by assumption
          exact bv8_eq_zero_of_zext32 hna
        have hrlt : rlen.toNat < tmp_pc.length := by
          rw [hrt_pc.tmp_len]
          exact Nat.lt_of_lt_of_le (hrt_pc.rlen_lt_of_unmarked hl_nc hlm0 hlm1) hcv
        have hr_tmp : (BitVec.setWidth 64 rlen).toNat < tmp_pc.length := by
          rw [bv_c0_zext32_64]; exact hrlt
        bve_steps!
        obtain ⟨_, hrt', hsub', hmem⟩ := hrt_pc.push hl_nc hlm0 hlm1
        have hr1_eq : (rlen + 1#32).toNat = rlen.toNat + 1 := by bv_omega
        refine hAfterNc (rlen + 1#32) false m
          ⟨lm_pc.set (nc &&& 0x7FFFFFFF#32).toNat 1#8,
            tmp_pc.set rlen.toNat (nc &&& 0x7FFFFFFF#32), ?_, fun _ => ?_, ?_⟩
        · rw [hr1_eq]; exact hrt'
        · rw [hr1_eq]
          have hp_new := entails_clause_of_subset hpc_ent' fun z hz => by
            rw [List.mem_cons] at hz ⊢
            rcases hz with rfl | hz
            · exact Or.inl rfl
            · exact Or.inr (hsub' z hz)
          have hn_new := side_entails_of_bin hn_ent (Or.inr (Or.inl hmem))
          exact resolve_pivots_entails hp_new hn_new
        · simp only [bv_c0_zext32_64] at hm ⊢; exact hm
      · have hhs : (0#32).slt (BitVec.signExtend 32 (s.core.vals[(nc &&&
            0x7FFFFFFF#32).toNat]'(by rw [hvalsl]; exact hl_mv))) = false := by assumption
        have hsgt : ¬ BitVec.slt 0#8 (s.core.vals[(nc &&& 0x7FFFFFFF#32).toNat]?.getD 0#8) := by
          rw [List.getElem?_eq_getElem (by rw [hvalsl]; exact hl_mv), Option.getD_some]
          exact bv8_sgt0_of_sext32 hhs
        have hcov_l : SideCovered F_cur (2 * v.toNat + 1)
            ((tmp_pc.take rlen.toNat).map BitVec.toNat) (nc &&& 0x7FFFFFFF#32).toNat := by
          by_cases hv0 : s.core.vals[(nc &&& 0x7FFFFFFF#32).toNat]?.getD 0#8 = 0#8
          · have hlmne : lm_pc[(nc &&& 0x7FFFFFFF#32).toNat]? ≠ some 0#8 := by
              intro h0
              rw [List.getElem?_eq_getElem (by rw [hrt_pc.lm_len]; exact hl_mv),
                Option.some.injEq] at h0
              have h0z : BitVec.setWidth 32 (lm_pc[(nc &&& 0x7FFFFFFF#32).toNat]'(
                  by rw [hrt_pc.lm_len]; exact hl_mv)) = 0#32 := by rw [h0]; rfl
              exact absurd h0z hc
            exact resolve_lit_sideCovered_of_marked hrt_pc hl_nc hlmne
          · exact resolve_lit_sideCovered_of_val_ne0 hw hlv0 hl_nc hsgt hv0
        exact hAfterNc rlen false m_pc ⟨lm_pc, tmp_pc, hrt_pc,
          fun _ => resolve_pivots_entails hpc_ent' (side_entails_of_bin hn_ent hcov_l), hm_pc⟩
      · have hhs : (0#32).slt (BitVec.signExtend 32 (s.core.vals[(nc &&&
            0x7FFFFFFF#32).toNat]'(by rw [hvalsl]; exact hl_mv))) = false := by assumption
        have hsgt : ¬ BitVec.slt 0#8 (s.core.vals[(nc &&& 0x7FFFFFFF#32).toNat]?.getD 0#8) := by
          rw [List.getElem?_eq_getElem (by rw [hvalsl]; exact hl_mv), Option.getD_some]
          exact bv8_sgt0_of_sext32 hhs
        have hv0 : s.core.vals[(nc &&& 0x7FFFFFFF#32).toNat]?.getD 0#8 ≠ 0#8 := fun h0 => by
          rw [List.getElem?_eq_getElem (by rw [hvalsl]; exact hl_mv), Option.getD_some] at h0
          have h0z : BitVec.signExtend 32 (s.core.vals[(nc &&& 0x7FFFFFFF#32).toNat]'(
              by rw [hvalsl]; exact hl_mv)) = 0#32 := by rw [h0]; rfl
          exact absurd h0z hc
        exact hAfterNc rlen false m_pc ⟨lm_pc, tmp_pc, hrt_pc,
          fun _ => resolve_pivots_entails hpc_ent'
            (side_entails_of_bin hn_ent
              (resolve_lit_sideCovered_of_val_ne0 hw hlv0 hl_nc hsgt hv0)), hm_pc⟩
    · have hnb_nc : ¬ (nc &&& 0x80000000#32) ≠ 0#32 := fun h => h hc
      have htf : taut = false := by assumption
      subst htf
      have hpc_ent' := hpc_ent rfl
      unfold FullBveEntryOkW at hnc; rw [ite_eq_right hnb_nc] at hnc
      obtain ⟨hnc_ref, hnc_garb⟩ := hnc
      have hnc_wf := hw.arena.refs_wf nc.toNat hnc_ref
      have hnc2_nat : (BitVec.setWidth 64 nc + 2).toNat = nc.toNat + 2 := by bv_omega
      have hnc2_lt : (BitVec.setWidth 64 nc + 2).toNat < s.core.arena.length := by bv_omega
      let nsz := s.core.arena[nc.toNat + 2]'(by omega)
      have hnsz_eq : s.core.arena[(BitVec.setWidth 64 nc + 2).toNat]'hnc2_lt = nsz := by
        simp only [nsz, hnc2_nat]
      have hnsz_nat : nsz.toNat = fullArenaClauseSize s nc.toNat := by
        unfold fullArenaClauseSize fullArenaClauseSizeCore nsz
        rw [List.getElem?_eq_getElem (by omega : nc.toNat + 2 < s.core.arena.length),
          Option.getD_some]
      have hnc_bd : nc.toNat + 3 + nsz.toNat ≤ s.core.arena_len := by
        rw [hnsz_nat]; exact Nat.le_trans hnc_wf.2.2.1 hnc_wf.2.2.2.1
      bve_steps!
      simp only [hnsz_eq]
      refine resolve_pair_nc_loop_wp Γ Q X c F0 F_cur s R v nc nsz rlen hw hcl hlv0 hnl_nat
        lm_pc tmp_pc hrt_pc hpc_ent' hnc_ref hnc_garb hnsz_nat hnc_bd _ ?_ J hJ m_pc hm_pc
      intro rlen' taut' m_nc hp
      bve_steps
      exact hAfterNc rlen' taut' m_nc hp
  clear hJ_pc hnc hnl_bv hnl_nat
  bve_steps
  · have hbin_pc : (pc &&& 0x80000000#32) ≠ 0#32 := hc
    unfold FullBveEntryOkW at hpc; rw [ite_eq_left hbin_pc] at hpc
    obtain ⟨hl_pc, hp_ent⟩ := hpc
    have hl_mv : (pc &&& 0x7FFFFFFF#32).toNat < 2 * c.max_vars := by omega
    have hl1_mv : ((pc &&& 0x7FFFFFFF#32) ^^^ 1#32).toNat < 2 * c.max_vars := bv32_xor_1_lt hl_mv
    have hl_vals : (BitVec.setWidth 64 (pc &&& 0x7FFFFFFF#32)).toNat < s.core.vals.length := by
      rw [bv_c0_zext32_64, hvalsl]; exact hl_mv
    have hrt0 := ResolveTmpInv.init hcl hlmc
    bve_steps
    · exact hAfterPc 0#32 true m
        ⟨s.core.lit_mark, s.core.tmp, hrt0, fun h => Bool.noConfusion h, hm⟩
    · have hl_lm : (BitVec.setWidth 64 (pc &&& 0x7FFFFFFF#32)).toNat < s.core.lit_mark.length :=
        by rw [bv_c0_zext32_64, hlml]; exact hl_mv
      have hl_tmp : (BitVec.setWidth 64 (0#32 : BitVec 32)).toNat < s.core.tmp.length := by
        bv_omega
      bve_steps!
      have hlm0 : s.core.lit_mark[(pc &&& 0x7FFFFFFF#32).toNat]? = some 0#8 := by
        have := hlmc _ hl_mv
        rw [List.getElem?_eq_getElem (by rw [hlml]; exact hl_mv), Option.getD_some] at this
        rw [List.getElem?_eq_getElem (by rw [hlml]; exact hl_mv), this]
      have hlm1 : s.core.lit_mark[(pc &&& 0x7FFFFFFF#32).toNat ^^^ 1]? = some 0#8 := by
        have h1lt : (pc &&& 0x7FFFFFFF#32).toNat ^^^ 1 < 2 * c.max_vars := by
          simpa only [bv32_xor_1_toNat] using hl1_mv
        have hthis := hlmc _ h1lt
        rw [List.getElem?_eq_getElem (by rw [hlml]; exact h1lt), Option.getD_some] at hthis
        rw [List.getElem?_eq_getElem (by rw [hlml]; exact h1lt), hthis]
      obtain ⟨_, hrt1, _, hmem1⟩ := hrt0.push hl_pc hlm0 hlm1
      have h1_eq : (0#32 + 1#32 : BitVec 32).toNat = 1 := rfl
      refine hAfterPc (0#32 + 1#32) false m
        ⟨s.core.lit_mark.set (pc &&& 0x7FFFFFFF#32).toNat 1#8,
          s.core.tmp.set 0 (pc &&& 0x7FFFFFFF#32), by rw [h1_eq]; exact hrt1, fun _ => ?_, ?_⟩
      · rw [h1_eq]; exact side_entails_of_bin hp_ent (Or.inr (Or.inl hmem1))
      · simp only [bv_c0_zext32_64] at hm ⊢; exact hm
    · have hhs : (0#32).slt (BitVec.signExtend 32 (s.core.vals[(pc &&&
          0x7FFFFFFF#32).toNat]'(by rw [hvalsl]; exact hl_mv))) = false := by assumption
      have hsgt : ¬ BitVec.slt 0#8 (s.core.vals[(pc &&& 0x7FFFFFFF#32).toNat]?.getD 0#8) := by
        rw [List.getElem?_eq_getElem (by rw [hvalsl]; exact hl_mv), Option.getD_some]
        exact bv8_sgt0_of_sext32 hhs
      have hv0 : s.core.vals[(pc &&& 0x7FFFFFFF#32).toNat]?.getD 0#8 ≠ 0#8 := fun h0 => by
        rw [List.getElem?_eq_getElem (by rw [hvalsl]; exact hl_mv), Option.getD_some] at h0
        have h0z : BitVec.signExtend 32 (s.core.vals[(pc &&& 0x7FFFFFFF#32).toNat]'(
            by rw [hvalsl]; exact hl_mv)) = 0#32 := by rw [h0]; rfl
        exact absurd h0z hc
      exact hAfterPc 0#32 false m ⟨s.core.lit_mark, s.core.tmp, hrt0,
        fun _ => side_entails_of_bin hp_ent
          (resolve_lit_sideCovered_of_val_ne0 hw hlv0 hl_pc hsgt hv0), hm⟩
  · have hnb_pc : ¬ (pc &&& 0x80000000#32) ≠ 0#32 := fun h => h hc
    unfold FullBveEntryOkW at hpc; rw [ite_eq_right hnb_pc] at hpc
    obtain ⟨hpc_ref, hpc_garb⟩ := hpc
    have hpc_wf := hw.arena.refs_wf pc.toNat hpc_ref
    have hpc2_nat : (BitVec.setWidth 64 pc + 2).toNat = pc.toNat + 2 := by bv_omega
    have hpc2_lt : (BitVec.setWidth 64 pc + 2).toNat < s.core.arena.length := by bv_omega
    let psz := s.core.arena[pc.toNat + 2]'(by omega)
    have hpsz_eq : s.core.arena[(BitVec.setWidth 64 pc + 2).toNat]'hpc2_lt = psz := by
      simp only [psz, hpc2_nat]
    have hpsz_nat : psz.toNat = fullArenaClauseSize s pc.toNat := by
      unfold fullArenaClauseSize fullArenaClauseSizeCore psz
      rw [List.getElem?_eq_getElem (by omega : pc.toNat + 2 < s.core.arena.length),
        Option.getD_some]
    have hpc_bd : pc.toNat + 3 + psz.toNat ≤ s.core.arena_len := by
      rw [hpsz_nat]; exact Nat.le_trans hpc_wf.2.2.1 hpc_wf.2.2.2.1
    bve_steps!
    simp only [hpsz_eq]
    exact resolve_pair_pc_loop_wp Γ Q X c F0 F_cur s R v pc psz hw hcl hlv0 hlmc hpl_nat
      hpc_ref hpc_garb hpsz_nat hpc_bd J_pc hAfterPc J hJ m hm

end

end LeanQbe.T.Examples.Kissat.Full
