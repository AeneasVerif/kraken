/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4Analysis
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofMin2
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofMin
import LeanQbe.T.Examples.Kissat.FullMinLemmas3
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 S4-B Proof 3a (`step13MinShrinkSpec`, Reverse, Compact & Clean)

UNSAT-only, callee-parametric helpers (`public section`, `0` `@[expose]` on theorems, `0`
`import all`, `XPost`-polymorphic) for Step-13 `fidStep13S4MinShrinkM6Fn` (`full_min_shrink_m6`):
1. `step13MinShrinkSpec` (approved Step-13 lift: allows `work_stk1'` / `res_sz'` writes and drops
   the ascending `lv ≤ lvl[tmp'[tl' - 1]]` ordering postcondition because Step-13 reverses
   `tmp[1..keep-1]` into descending-level block order).
2. `s13_min_shrink_rev_wp`, `s13_min_shrink_compact_loop_wp`, `s13_min_shrink_clean_wp`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S4

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full hiding
  FullMinMarkInv fullMinMarkCore fullMinMarkState fullMinMarkSpec
  fullMinLitSpec fullShrinkLowerSpec fullShrinkBlkSpec fullMinShrinkSpec
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Full.FullMinSpecs
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullMinTactics
open Kraken.Bedrock2.Test

private theorem is_wp_let {Γ rs Q X ts} {op : Op Val ts} {k : Tup Val ts → Expr Val Cont rs}
    {m : Mem 64} (h : wp Γ Q X (.let_ op k) m) : wp Γ Q X (.let_ op k) m := h
local macro "s13_lets" : tactic => `(tactic| repeat (apply is_wp_let; c0_hstep))

/-! ## 1. Step-13 `step13MinShrinkSpec` & State Builders -/

abbrev s13BlkState (s : FullState) (tmp : List (BitVec 32)) (mrk : List (BitVec 8))
    (mclr sstk wsort ws1 : List (BitVec 32)) (mcl : Nat) (mcf ticks resSz : BitVec 64) :
    FullState :=
  { core := { s.core with
      tmp := tmp, mrk := mrk, min_clr := mclr, min_clr_len := mcl, min_clr_full := mcf },
    scratch := { s.scratch with
      shrink_stk := sstk, wsort := wsort, search_ticks := ticks,
      work_stk1 := ws1, res_sz := resSz } }

abbrev step13MinShrinkState (s : FullState) (tmp : List (BitVec 32)) (tl : Nat)
    (mrk : List (BitVec 8)) (mclr sstk wsort ws1 : List (BitVec 32)) (mcl : Nat)
    (mcf conf llits mrem ticks resSz : BitVec 64) : FullState :=
  { core := { s.core with
      tmp := tmp, tmp_len := tl, mrk := mrk, min_clr := mclr,
      min_clr_len := mcl, min_clr_full := mcf },
    scratch := { s.scratch with
      conflicts := conf, learned_lits := llits, min_removed := mrem,
      shrink_stk := sstk, wsort := wsort, search_ticks := ticks,
      work_stk1 := ws1, res_sz := resSz } }

/-- Step-13 `full_min_shrink_m6` specification: extends `m8MinShrinkSpec` with `work_stk1'` /
`res_sz'` writes and drops `lv ≤ lvl[tmp'[tl' - 1]]` (descending-level block order). -/
def step13MinShrinkSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullOtfsWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
    1 ≤ s.core.tmp_len ∧ s.core.tmp_len ≤ s.core.cur_vars ∧
    ((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) ∧
    (∀ k < s.core.tmp_len, let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
    (∀ k, 1 ≤ k → k < s.core.tmp_len →
      let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level) ∧
    (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.core.cur_level ∧
    (FullMem c s ⋆ R) m ∧
    ∀ tmp' tl' mrk' mclr' sstk' wsort' ws1' mcl' mcf' conf' llits' mrem' ticks' resSz' m',
      let s' := step13MinShrinkState s tmp' tl' mrk' mclr' sstk' wsort' ws1' mcl' mcf' conf'
        llits' mrem' ticks' resSz'
      s'.LengthsOk c → FullOtfsWitnessInv c F0 F_cur s'.core → FullLitMarksClear c s' →
      1 ≤ tl' → tl' ≤ s.core.tmp_len → tmp'[0]? = s.core.tmp[0]? →
      ((tmp'.take tl').map fun x => x.toNat / 2).Nodup →
      (∀ j, 1 ≤ j → j < tl' →
        let l := (tmp'[j]?.getD 0#32).toNat
        let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        0 < lv ∧ lv < s.core.cur_level) →
      (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat)) →
      (FullMem c s' ⋆ R) m' → Q () m'

theorem step13MinShrinkSpec_monoX {xs : Tup Val [i64]} {m : Mem 64}
    {Q : Post []} {X X' : XPost}
    (h : step13MinShrinkSpec xs m Q X) : step13MinShrinkSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem step13MinShrinkSpec_of {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hlen : s.LengthsOk c) (hw : FullOtfsWitnessInv c F0 F_cur s.core)
    (hlm : FullLitMarksClear c s)
    (htl1 : 1 ≤ s.core.tmp_len) (htl_cv : s.core.tmp_len ≤ s.core.cur_vars)
    (hnd : ((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup)
    (hEnt : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)))
    (hvals : ∀ k < s.core.tmp_len, let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hlvls : ∀ k, 1 ≤ k → k < s.core.tmp_len →
      let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level)
    (h0_lvl : (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
      s.core.cur_level)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ tmp' tl' mrk' mclr' sstk' wsort' ws1' mcl' mcf' conf' llits' mrem' ticks' resSz' m',
      let s' := step13MinShrinkState s tmp' tl' mrk' mclr' sstk' wsort' ws1' mcl' mcf' conf'
        llits' mrem' ticks' resSz'
      s'.LengthsOk c → FullOtfsWitnessInv c F0 F_cur s'.core → FullLitMarksClear c s' →
      1 ≤ tl' → tl' ≤ s.core.tmp_len → tmp'[0]? = s.core.tmp[0]? →
      ((tmp'.take tl').map fun x => x.toNat / 2).Nodup →
      (∀ j, 1 ≤ j → j < tl' →
        let l := (tmp'[j]?.getD 0#32).toNat
        let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        0 < lv ∧ lv < s.core.cur_level) →
      (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat)) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    step13MinShrinkSpec (c.hdr, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hlm, htl1, htl_cv, hnd, hEnt, hvals, hlvls, h0_lvl, hm,
   hQ⟩

theorem step13MinShrinkSpec_elim {h m Q X} (hs : step13MinShrinkSpec (h, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullOtfsWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
      1 ≤ s.core.tmp_len ∧ s.core.tmp_len ≤ s.core.cur_vars ∧
      ((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) ∧
      (∀ k < s.core.tmp_len, let l := (s.core.tmp[k]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
      (∀ k, 1 ≤ k → k < s.core.tmp_len →
        let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
        0 < lv ∧ lv < s.core.cur_level) ∧
      (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.core.cur_level ∧
      (FullMem c s ⋆ R) m ∧
      ∀ tmp' tl' mrk' mclr' sstk' wsort' ws1' mcl' mcf' conf' llits' mrem' ticks' resSz' m',
        let s' := step13MinShrinkState s tmp' tl' mrk' mclr' sstk' wsort' ws1' mcl' mcf' conf'
          llits' mrem' ticks' resSz'
        s'.LengthsOk c → FullOtfsWitnessInv c F0 F_cur s'.core → FullLitMarksClear c s' →
        1 ≤ tl' → tl' ≤ s.core.tmp_len → tmp'[0]? = s.core.tmp[0]? →
        ((tmp'.take tl').map fun x => x.toNat / 2).Nodup →
        (∀ j, 1 ≤ j → j < tl' →
          let l := (tmp'[j]?.getD 0#32).toNat
          let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
          l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
          0 < lv ∧ lv < s.core.cur_level) →
        (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat)) →
        (FullMem c s' ⋆ R) m' → Q () m' := hs

/-! ## 2. Shared Min-Shrink Lemmas & Block-Loop Invariant -/

theorem s13ListTakeSuccSet {α : Type _} {xs : List α} {i : Nat} (v : α)
    (hi : i < xs.length) :
    (xs.set i v).take (i + 1) = xs.take i ++ [v] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i => simp [List.set, List.take_succ_cons, ih (by simpa using hi)]

theorem s13ListFilterNeEqSelf {xs : List (BitVec 32)} {k : Nat}
    (hk : k ≤ xs.length)
    (hne : ∀ j < k, xs[j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) :
    (xs.take k).filter (· ≠ 0xFFFFFFFF#32) = xs.take k := by
  rw [List.filter_eq_self]; intro b hb
  rw [List.mem_iff_getElem] at hb; obtain ⟨j, hj, rfl⟩ := hb
  rw [List.length_take] at hj; rw [List.getElem_take]
  have h1 := hne j (by omega)
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1
  exact decide_eq_true h1

theorem s13MinMarkInvMrkNeZeroIff {k : FullCoreState} {keep : List Nat}
    (hmin : FullMinMarkInv k keep) (hno8 : ∀ v < k.cur_vars, (k.mrk[v]?.getD 0#8 &&& 8#8) = 0#8)
    {v : Nat} (hv : v < k.cur_vars) :
    k.mrk[v]?.getD 0#8 ≠ 0#8 ↔ (k.mrk[v]?.getD 0#8 &&& 6#8) ≠ 0#8 := by
  have hd := hmin.mrk_dom v hv; have h8 := hno8 v hv
  generalize k.mrk[v]?.getD 0#8 = b at hd h8 ⊢; revert b hd h8; decide

theorem s13MinShrinkScratchOk {c : FullCfg} {sc : FullScratch} (hok : sc.LengthsOk c)
    {sstk' wsort' ws1' : List (BitVec 32)} {conf' llits' mrem' ticks' resSz' : BitVec 64}
    (hsstk : sstk'.length = c.max_vars) (hws : wsort'.length = 2 * c.max_vars)
    (hws1 : ws1'.length = 2 * c.max_vars) :
    ({ sc with
      conflicts := conf', learned_lits := llits', min_removed := mrem',
      shrink_stk := sstk', wsort := wsort', search_ticks := ticks',
      work_stk1 := ws1', res_sz := resSz' } : FullScratch).LengthsOk c :=
  { hok with shrink_stk_len := hsstk, wsort_len := hws, work_stk1_len := hws1 }

theorem s13CoreInv_blk {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hcore : FullOtfsCoreInv c F0 s) {tmp1 : List (BitVec 32)} {mrk1 : List (BitVec 8)}
    {mclr1 sstk1 wsort1 ws1 : List (BitVec 32)} {mcl1 : Nat}
    {mcf1 ticks1 resSz1 : BitVec 64}
    (htmp : tmp1.length = c.max_vars) (hmrk : mrk1.length = c.max_vars)
    (hmclr : mclr1.length = c.max_vars) (hmcl : mcl1 ≤ c.max_vars)
    (hsstk : sstk1.length = c.max_vars) (hws : wsort1.length = 2 * c.max_vars)
    (hws1 : ws1.length = 2 * c.max_vars) :
    FullOtfsCoreInv c F0
      (s13BlkState s tmp1 mrk1 mclr1 sstk1 wsort1 ws1 mcl1 mcf1 ticks1 resSz1) :=
  ⟨⟨{ hcore.1.core_ok with
        tmp_len_arr := htmp, mrk_len := hmrk, min_clr_len_arr := hmclr, min_clr_len_le := hmcl },
      { hcore.1.scratch_ok with
        shrink_stk_len := hsstk, wsort_len := hws, work_stk1_len := hws1 }⟩,
    let ⟨F_cur, hw⟩ := hcore.2
    ⟨F_cur, { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }⟩⟩

theorem s13Blk_step {s : FullState} {tmp : List (BitVec 32)} {mrk : List (BitVec 8)}
    {mclr sstk wsort ws1 : List (BitVec 32)} {mcl v : Nat} {mcf ticks resSz : BitVec 64}
    {b : BitVec 8} :
    s13BlkState s tmp (fullMinMarkStepState
        (s13BlkState s tmp mrk mclr sstk wsort ws1 mcl mcf ticks resSz) v b).core.mrk
      (fullMinMarkStepState
        (s13BlkState s tmp mrk mclr sstk wsort ws1 mcl mcf ticks resSz) v b).core.min_clr
      sstk wsort ws1
      (fullMinMarkStepState
        (s13BlkState s tmp mrk mclr sstk wsort ws1 mcl mcf ticks resSz) v b).core.min_clr_len
      (fullMinMarkStepState
        (s13BlkState s tmp mrk mclr sstk wsort ws1 mcl mcf ticks resSz) v b).core.min_clr_full
      ticks resSz =
    fullMinMarkStepState (s13BlkState s tmp mrk mclr sstk wsort ws1 mcl mcf ticks resSz) v b := by
  dsimp only [s13BlkState, fullMinMarkStepState, fullMinMarkStepCore]
  split <;> rfl

theorem s13MinShrinkPostSort {c : FullCfg} {s : FullState}
    (htl1 : 1 ≤ s.core.tmp_len) (htl_cv : s.core.tmp_len ≤ s.core.cur_vars)
    (hcv : s.core.cur_vars ≤ c.max_vars) (htmp_len : s.core.tmp.length = c.max_vars)
    (htmp_vals : ∀ k < s.core.tmp_len, let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8)
    (htmp_lvls : ∀ k, 1 ≤ k → k < s.core.tmp_len →
      let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level)
    {tmp1 : List (BitVec 32)} (ht1_len : tmp1.length = c.max_vars)
    (ht1_0 : 1 ≤ s.core.tmp_len → tmp1[0]? = s.core.tmp[0]?)
    (ht1_r : ∀ k, 1 ≤ k → k < s.core.tmp_len →
      ∃ i, 1 ≤ i ∧ i < s.core.tmp_len ∧ tmp1[k]? = s.core.tmp[i]?)
    (ht1_l : ∀ i, 1 ≤ i → i < s.core.tmp_len →
      ∃ k, 1 ≤ k ∧ k < s.core.tmp_len ∧ s.core.tmp[i]? = tmp1[k]?) :
    let keep0 := ((tmp1.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat
    keep0 = (tmp1.take s.core.tmp_len).map BitVec.toNat ∧
    (∀ F_cur, (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) →
      (cnfOfClauses F_cur).EntailsClause (cnfClause keep0)) ∧
    (∀ k < s.core.tmp_len, tmp1[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
      (tmp1[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.vals[(tmp1[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 ∧
      (tmp1[k]?.getD 0#32).toNat ∈ keep0) ∧
    (∀ k, 1 ≤ k → k < s.core.tmp_len →
      let lv := (s.core.lvl[(tmp1[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level) := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hff : (0xFFFFFFFF#32 : BitVec 32).toNat = 4294967295 := rfl
  have hlt1 : ∀ k < s.core.tmp_len, (tmp1[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.vals[(tmp1[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 := fun k hk => by
    cases k with
    | zero => rw [ht1_0 htl1]; exact htmp_vals 0 hk
    | succ k' =>
      obtain ⟨i, _, hi2, heq⟩ := ht1_r (k' + 1) (by omega) hk
      rw [heq]; exact htmp_vals i hi2
  have hkeep_eq : ((tmp1.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat =
      (tmp1.take s.core.tmp_len).map BitVec.toNat := by
    rw [s13ListFilterNeEqSelf (by omega) fun j hj => by
      have h1 := (hlt1 j hj).1
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1 ⊢
      intro heq; have hto := congrArg BitVec.toNat heq; rw [hff] at hto; omega]
  refine ⟨hkeep_eq, ?_, ?_, fun k hk1 hk2 => by
      obtain ⟨i, hi1, hi2, heq⟩ := ht1_r k hk1 hk2; rw [heq]; exact htmp_lvls i hi1 hi2⟩
  · intro F_cur hEnt0; rw [hkeep_eq]; rw [CNF.entails_clause_def] at hEnt0 ⊢
    intro α hα; obtain ⟨l, hl, hsat⟩ := (clause_sat_cnfClause_iff α _).mp (hEnt0 α hα)
    refine (clause_sat_cnfClause_iff α _).mpr ⟨l, ?_, hsat⟩
    rw [List.mem_map] at hl ⊢; obtain ⟨b, hb, rfl⟩ := hl
    rw [List.mem_iff_getElem] at hb; obtain ⟨i, hi, rfl⟩ := hb
    rw [List.length_take] at hi; rw [List.getElem_take]
    obtain ⟨j, hj, heq⟩ : ∃ j < s.core.tmp_len, s.core.tmp[i]? = tmp1[j]? := by
      cases i with
      | zero => exact ⟨0, htl1, (ht1_0 htl1).symm⟩
      | succ i' =>
        obtain ⟨j, _, hj2, heq⟩ := ht1_l (i' + 1) (by omega) (by omega)
        exact ⟨j, hj2, heq⟩
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at heq
    exact ⟨tmp1[j]'(by omega), List.mem_iff_getElem.mpr ⟨j, by rw [List.length_take]; omega,
      by rw [List.getElem_take]⟩, by rw [Option.some.inj heq]⟩
  · intro k hk; have hkv := hlt1 k hk
    have hk_ne : tmp1[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; intro heq
      have hto := congrArg BitVec.toNat heq; have h1' := hkv.1
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1'
      rw [hff] at hto; omega
    have hk_mem : (tmp1[k]?.getD 0#32).toNat ∈
        ((tmp1.take s.core.tmp_len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat := by
      rw [hkeep_eq, List.mem_map]
      exact ⟨tmp1[k]'(by omega), List.mem_iff_getElem.mpr ⟨k, by rw [List.length_take]; omega,
        by rw [List.getElem_take]⟩, by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]⟩
    exact ⟨hk_ne, hkv.1, hkv.2, hk_mem⟩

theorem s13MinLitStepState {c : FullCfg} {F0 : CNF Nat} {s_orig cur : FullState}
    {keepLen idx : Nat} (hidx_kl : idx < keepLen) (hkl_cv : keepLen ≤ cur.core.cur_vars)
    (hcore : FullOtfsCoreInv c F0 cur)
    (_hmin : FullMinMarkInv cur.core
      (((cur.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
    (hent : ∀ F_cur, FullOtfsWitnessInv c F0 F_cur s_orig.core →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((s_orig.core.tmp.take s_orig.core.tmp_len).map BitVec.toNat)) →
      FullOtfsWitnessInv c F0 F_cur cur.core ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause
        (((cur.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)))
    (hnd : ((s_orig.core.tmp.take s_orig.core.tmp_len).map fun x => x.toNat / 2).Nodup →
      (∀ k, 1 ≤ k → k < s_orig.core.tmp_len →
        (s_orig.core.lvl[(s_orig.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠
        (s_orig.core.lvl[(s_orig.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (((cur.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map
        fun x => x.toNat / 2).Nodup)
    (hab : ∀ v, cur.core.cur_vars ≤ v → cur.core.mrk[v]? = s_orig.core.mrk[v]?)
    (hno8 : ∀ v < cur.core.cur_vars, (cur.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8)
    (hrem : ∀ k < keepLen, cur.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      let l := (cur.core.tmp[k]?.getD 0#32).toNat
      l < 2 * cur.core.cur_vars ∧ cur.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
      (cur.core.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
    {root_lit : BitVec 32} (hroot_eq : cur.core.tmp[idx]? = some root_lit)
    (hroot_ne : root_lit ≠ 0xFFFFFFFF#32)
    {ok : Bool} {mrk' : List (BitVec 8)} {wsort' mclr' : List (BitVec 32)}
    {mcl' : Nat} {mcf' ticks' : BitVec 64}
    (hlen' : (m8MinLitDfsState cur mrk' wsort' mclr' mcl' mcf' ticks').LengthsOk c)
    (hab' : ∀ v, cur.core.cur_vars ≤ v → mrk'[v]? = cur.core.mrk[v]?)
    (hmono2 : ∀ v < cur.core.cur_vars,
      (cur.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hbit8 : ∀ v < cur.core.cur_vars,
      (mrk'[v]?.getD 0#8 &&& 8#8) = (cur.core.mrk[v]?.getD 0#8 &&& 8#8))
    (hmin' : FullMinMarkInv (m8MinLitDfsState cur mrk' wsort' mclr' mcl' mcf' ticks').core
      (((cur.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
    (hok_true : ok = true →
      (∀ keep', (∀ l ∈ (((cur.core.tmp.take keepLen).filter
            (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat), l = root_lit.toNat ∨ l ∈ keep') →
        FullMinMarkInv (m8MinLitDfsState cur mrk' wsort' mclr' mcl' mcf' ticks').core keep') ∧
      FullMinMarkInv (fullMinMarkCore
          (m8MinLitDfsState cur mrk' wsort' mclr' mcl' mcf' ticks').core
          (root_lit.toNat / 2) 2#8)
        (((cur.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)) :
    let tmp_n := if ok then cur.core.tmp.set idx 0xFFFFFFFF#32 else cur.core.tmp
    let st_n : FullState := s13BlkState cur tmp_n mrk' mclr' cur.scratch.shrink_stk wsort'
      cur.scratch.work_stk1 mcl' mcf' ticks' cur.scratch.res_sz
    FullOtfsCoreInv c F0 st_n ∧
    FullMinMarkInv st_n.core
      (((tmp_n.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) ∧
    (∀ F_cur, FullOtfsWitnessInv c F0 F_cur s_orig.core →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((s_orig.core.tmp.take s_orig.core.tmp_len).map BitVec.toNat)) →
      FullOtfsWitnessInv c F0 F_cur st_n.core ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause
        (((tmp_n.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))) ∧
    (((s_orig.core.tmp.take s_orig.core.tmp_len).map fun x => x.toNat / 2).Nodup →
      (∀ k, 1 ≤ k → k < s_orig.core.tmp_len →
        (s_orig.core.lvl[(s_orig.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠
        (s_orig.core.lvl[(s_orig.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (((tmp_n.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map
        fun x => x.toNat / 2).Nodup) ∧
    (∀ v, cur.core.cur_vars ≤ v → mrk'[v]? = s_orig.core.mrk[v]?) ∧
    (∀ v < cur.core.cur_vars, (mrk'[v]?.getD 0#8 &&& 8#8) = 0#8) ∧
    (∀ k < keepLen, tmp_n[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      let l := (tmp_n[k]?.getD 0#32).toNat
      l < 2 * cur.core.cur_vars ∧ cur.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
      (mrk'[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
    (∀ k, idx < k → k < keepLen → tmp_n[k]? = cur.core.tmp[k]?) := by
  have hrm_b : cur.core.tmp[idx]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
    rw [hroot_eq, Option.getD_some]; exact hroot_ne
  have hrb := hrem idx hidx_kl hrm_b
  have hr_nat : (cur.core.tmp[idx]?.getD 0#32).toNat = root_lit.toNat := by
    rw [hroot_eq, Option.getD_some]
  have hcur_w : cur.scratch.shrink_stk.length = c.max_vars := hcore.1.scratch_ok.shrink_stk_len
  have hcur_ws1 : cur.scratch.work_stk1.length = 2 * c.max_vars :=
    hcore.1.scratch_ok.work_stk1_len
  cases ok with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨s13CoreInv_blk hcore hcore.1.core_ok.tmp_len_arr hlen'.core_ok.mrk_len
        hlen'.core_ok.min_clr_len_arr hlen'.core_ok.min_clr_len_le hcur_w
        hlen'.scratch_ok.wsort_len hcur_ws1,
      hmin', fun F_cur hw hEnt0 =>
        let ⟨hwc, hEc⟩ := hent F_cur hw hEnt0
        ⟨{ hwc with
            arena := { hwc.arena with len_ok := hwc.arena.len_ok }
            watches := hwc.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }, hEc⟩,
      hnd, fun v hv => (hab' v hv).trans (hab v hv),
      fun v hv => by rw [hbit8 v hv]; exact hno8 v hv,
      fun k hk hne => by
        have hrk := hrem k hk hne
        exact ⟨hrk.1, hrk.2.1,
          hmono2 ((cur.core.tmp[k]?.getD 0#32).toNat / 2) (by omega) hrk.2.2⟩,
      fun _ _ _ => trivial⟩
  | true =>
    simp only [↓reduceIte]; let tmp_n := cur.core.tmp.set idx 0xFFFFFFFF#32
    let st_base := m8MinLitDfsState cur mrk' wsort' mclr' mcl' mcf' ticks'
    let st_n : FullState :=
      s13BlkState cur tmp_n mrk' mclr' cur.scratch.shrink_stk wsort' cur.scratch.work_stk1
        mcl' mcf' ticks' cur.scratch.res_sz
    have htl_n : tmp_n.length = c.max_vars := by
      dsimp only [tmp_n]; rw [List.length_set, hcore.1.core_ok.tmp_len_arr]
    have hcore_n : FullOtfsCoreInv c F0 st_n :=
      s13CoreInv_blk hcore htl_n hlen'.core_ok.mrk_len hlen'.core_ok.min_clr_len_arr
        hlen'.core_ok.min_clr_len_le hcur_w hlen'.scratch_ok.wsort_len hcur_ws1
    let keep' := ((tmp_n.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat
    have hsub : ∀ l ∈ (((cur.core.tmp.take keepLen).filter
        (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat), l = root_lit.toNat ∨ l ∈ keep' := by
      intro l hl; rw [mem_filter_map_toNat_take] at hl; obtain ⟨k, hk, b, hkb, hne, rfl⟩ := hl
      by_cases hke : k = idx
      · subst k; rw [hkb] at hroot_eq; left; exact congrArg BitVec.toNat (Option.some.inj hroot_eq)
      · right; exact mem_filter_map_toNat_take.mpr ⟨k,
          by dsimp only [tmp_n]; rw [List.length_set]; exact hk, b,
          by dsimp only [tmp_n]; rw [List.getElem?_set_ne (Ne.symm hke)]; exact hkb, hne, rfl⟩
    have hmin_base : FullMinMarkInv st_base.core keep' := (hok_true rfl).1 keep' hsub
    have hmin_n : FullMinMarkInv st_n.core keep' :=
      ⟨hmin_base.mrk_dom, hmin_base.clr_cov, hmin_base.rem_sound⟩
    have hent_n : ∀ F_cur, FullOtfsWitnessInv c F0 F_cur s_orig.core →
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s_orig.core.tmp.take s_orig.core.tmp_len).map BitVec.toNat)) →
        FullOtfsWitnessInv c F0 F_cur st_n.core ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause keep') := by
      intro F_cur hw hEnt0; obtain ⟨hwc, hEc⟩ := hent F_cur hw hEnt0
      have hwb : FullOtfsWitnessInv c F0 F_cur st_base.core :=
        { hwc with
          arena := { hwc.arena with len_ok := hwc.arena.len_ok }
          watches := hwc.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
      refine ⟨{ hwc with
          arena := { hwc.arena with len_ok := hwc.arena.len_ok }
          watches := hwc.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
        fullMinMark_entails hwb hmin_base hEc fun l hl => ?_⟩
      rw [mem_filter_map_toNat_take] at hl; obtain ⟨k, hk, b, hkb, hne, rfl⟩ := hl
      have hrk := hrem k (lt_of_lt_of_le hk (Nat.min_le_left _ _))
        (by rw [hkb, Option.getD_some]; exact hne)
      have hbk : (cur.core.tmp[k]?.getD 0#32).toNat = b.toNat := by rw [hkb, Option.getD_some]
      rw [hbk] at hrk
      refine ⟨hrk.1, hrk.2.1, ?_⟩
      rcases hsub b.toNat (mem_filter_map_toNat_take.mpr ⟨k, hk, b, hkb, hne, rfl⟩) with
        heqb | hin
      · right; rw [heqb, ← hr_nat]; exact hmono2 _ (by omega) hrb.2.2
      · exact Or.inl hin
    have hkl_lt_c : keepLen ≤ cur.core.tmp.length := by
      rw [hcore.1.core_ok.tmp_len_arr]; exact le_trans hkl_cv hcore.1.core_ok.cur_vars_le
    have hidx_lt' : idx < cur.core.tmp.length := lt_of_lt_of_le hidx_kl hkl_lt_c
    have hnb : ∀ k, tmp_n[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 → k ≠ idx := fun k hk => by
      rintro rfl; exact hk (by dsimp only [tmp_n]; rw [List.getElem?_set_self hidx_lt']; rfl)
    refine ⟨hcore_n, hmin_n, hent_n,
      fun hnd0 hne0 => nodup_filter_set_sent hkl_lt_c hidx_kl (hnd hnd0 hne0),
      fun v hv => (hab' v hv).trans (hab v hv),
      fun v hv => by rw [hbit8 v hv]; exact hno8 v hv,
      fun k hk hne => ?_,
      fun _ _ _ => by rw [List.getElem?_set_ne (by omega)]⟩
    · have hke := Ne.symm (hnb k hne)
      rw [List.getElem?_set_ne hke] at hne ⊢; have hrk := hrem k hk hne
      exact ⟨hrk.1, hrk.2.1, hmono2 ((cur.core.tmp[k]?.getD 0#32).toNat / 2) (by omega) hrk.2.2⟩

structure S13BlkLoopInv (c : FullCfg) (F0 : CNF Nat) (s s_c1 : FullState)
    (tlen beg : Nat) (cur : FullState) : Prop where
  core : FullOtfsCoreInv c F0 cur
  min_inv : FullMinMarkInv cur.core
    (((cur.core.tmp.take tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)
  entails : ∀ F_cur, FullOtfsWitnessInv c F0 F_cur s.core →
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) →
    FullOtfsWitnessInv c F0 F_cur cur.core ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause
      (((cur.core.tmp.take tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
  nodup : ((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup →
    (∀ k, 1 ≤ k → k < s.core.tmp_len →
      (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠
      (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
    (((cur.core.tmp.take tlen).filter (· ≠ 0xFFFFFFFF#32)).map
      fun x => x.toNat / 2).Nodup
  mrk_above : ∀ v, s.core.cur_vars ≤ v → cur.core.mrk[v]? = s.core.mrk[v]?
  no8 : ∀ v < s.core.cur_vars, (cur.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8
  cv_eq : cur.core.cur_vars = s.core.cur_vars
  tl_eq : cur.core.tmp_len = s.core.tmp_len
  lvl_eq : cur.core.lvl = s.core.lvl
  vals_eq : cur.core.vals = s.core.vals
  clvl_eq : cur.core.cur_level = s.core.cur_level
  tpos_eq : cur.core.trail_pos = s.core.trail_pos
  zero_eq : cur.core.tmp[0]? = s_c1.core.tmp[0]?
  tail_eq : ∀ k, beg ≤ k → k < tlen → cur.core.tmp[k]? = s_c1.core.tmp[k]?
  beg_bnd : 1 < beg → beg < tlen →
    (s.core.lvl[(s_c1.core.tmp[beg - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
    (s.core.lvl[(s_c1.core.tmp[beg]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
  rem_mrk : ∀ k < tlen, cur.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
    let l := (cur.core.tmp[k]?.getD 0#32).toNat
    l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
    (cur.core.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8
  post_lvls : ∀ k, 1 ≤ k → k < tlen →
    cur.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
    (s.core.lvl[(cur.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
    (s.core.lvl[(s_c1.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat

/-! ## 3. Permutation Invariant & Step-13 Descending Block Reverse (`s13MinRevExpr`) -/

abbrev S13TmpRevInv (tmp0 tmp : List (BitVec 32)) (keep : Nat) : Prop :=
  tmp.length = tmp0.length ∧ tmp[0]? = tmp0[0]? ∧
  (tmp.take keep).Perm (tmp0.take keep) ∧
  ∀ j, 1 ≤ j → j < keep → ∃ i, 1 ≤ i ∧ i < keep ∧ tmp[j]? = tmp0[i]?

theorem s13TmpRevInv_refl (tmp0 : List (BitVec 32)) (keep : Nat) :
    S13TmpRevInv tmp0 tmp0 keep :=
  ⟨rfl, rfl, .refl _, fun j hj1 hj2 => ⟨j, hj1, hj2, rfl⟩⟩

theorem s13TmpRevInv_swap {tmp0 tmp : List (BitVec 32)} {keep a b : Nat}
    (h : S13TmpRevInv tmp0 tmp keep) (ha1 : 1 ≤ a) (ha : a < keep) (hb1 : 1 ≤ b) (hb : b < keep)
    (hkl : keep ≤ tmp0.length) (hat : a < tmp.length) (hbt : b < tmp.length) :
    S13TmpRevInv tmp0 ((tmp.set a (tmp[b]'hbt)).set b (tmp[a]'hat)) keep := by
  obtain ⟨hl, h0, hp, hmem⟩ := h
  have hta : a < (tmp.take keep).length := by simp; omega
  have htb : b < (tmp.take keep).length := by simp; omega
  refine ⟨by simp [hl], ?_, ?_, fun j hj1 hj2 => ?_⟩
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), h0]
  · rw [List.take_set, List.take_set]
    have e1 : tmp[b]'hbt = (tmp.take keep)[b]'htb := by simp [List.getElem_take]
    have e2 : tmp[a]'hat = (tmp.take keep)[a]'hta := by simp [List.getElem_take]
    rw [e1, e2]; exact (Full.list_swap_perm _ hta htb).trans hp
  · by_cases hjb : j = b
    · subst j
      rw [List.getElem?_set_self (by rw [List.length_set]; exact hbt),
        ← List.getElem?_eq_getElem hat]
      exact hmem a ha1 ha
    · rw [List.getElem?_set_ne (Ne.symm hjb)]
      by_cases hja : j = a
      · subst j
        rw [List.getElem?_set_self hat, ← List.getElem?_eq_getElem hbt]
        exact hmem b hb1 hb
      · rw [List.getElem?_set_ne (Ne.symm hja)]; exact hmem j hj1 hj2

theorem s13TmpRevInv_entails {F_cur : List (List Nat)} {tmp0 tmp : List (BitVec 32)} {keep : Nat}
    (h : S13TmpRevInv tmp0 tmp keep)
    (hEnt : (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp0.take keep).map BitVec.toNat))) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp.take keep).map BitVec.toNat)) := by
  rw [CNF.entails_clause_def] at hEnt ⊢; intro α hα
  obtain ⟨l, hl, hsat⟩ := (clause_sat_cnfClause_iff α _).mp (hEnt α hα)
  exact (clause_sat_cnfClause_iff α _).mpr ⟨l, ((h.2.2.1.map BitVec.toNat).mem_iff).mpr hl, hsat⟩

private theorem s13_bv64_zext32_lshr_sext1 (x : BitVec 32) :
    (x.setWidth 64 >>> (1 : BitVec 32).signExtend 64).toNat = x.toNat / 2 := by
  rw [show (1 : BitVec 32).signExtend 64 = 1#64 from rfl,
    show ∀ y : BitVec 64, y >>> 1#64 = y >>> 1 from fun _ => rfl]
  bv_omega

private theorem s13_bv64_sub1 {x : BitVec 64} (hx : 0 < x.toNat) :
    (x - 1).toNat = x.toNat - 1 := by
  bv_omega

abbrev s13MinRevLoopExpr {V : Ty → Type} {C : List Ty → Type}
    (pTmp lo0 hi0 : V i64) (K : Expr V C []) : Expr V C [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .group (sig := [[i64, i64]]) (fun Js => .cons (fun p =>
    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p.fst, .var p.snd.fst, ())) fun b =>
    .jnz (.var b.fst)
      (.let_ (op64 (.mul i64) (.var p.fst) (.imm 4)) fun o1 =>
       .let_ (op64 (.add i64) (.var pTmp) (.var o1.fst)) fun a1 =>
       .load i32 (.var a1.fst) fun sw =>
       .let_ (op64 (.mul i64) (.var p.fst) (.imm 4)) fun o2 =>
       .let_ (op64 (.add i64) (.var pTmp) (.var o2.fst)) fun a2 =>
       .let_ (op64 (.mul i64) (.var p.snd.fst) (.imm 4)) fun o3 =>
       .let_ (op64 (.add i64) (.var pTmp) (.var o3.fst)) fun a3 =>
       .load i32 (.var a3.fst) fun vhi =>
       .store (.var vhi) (.var a2.fst)
         (.let_ (op64 (.mul i64) (.var p.snd.fst) (.imm 4)) fun o4 =>
          .let_ (op64 (.add i64) (.var pTmp) (.var o4.fst)) fun a4 =>
          .store (.var sw) (.var a4.fst)
            (.let_ (op64 (.add i64) (.var p.fst) (.imm 1)) fun nlo =>
             .let_ (op64 (.sub i64) (.var p.snd.fst) (.imm 1)) fun nhi =>
             .jump Js.fst (.var nlo.fst, .var nhi.fst, ()))))
      K) .nil)
    fun Js => .jump Js.fst (.var lo0, .var hi0, ())

abbrev s13MinRevExpr {V : Ty → Type} {C : List Ty → Type}
    (pTmp pLvl keep : V i64) (K : Expr V C []) : Expr V C [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .group (sig := [[]]) (fun _ => .cons (fun _ => K) .nil) fun J32 =>
  .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var keep, .imm 2, ())) fun bgt =>
  .jnz (.var bgt.fst)
    (.let_ (op64 (.sub i64) (.var keep) (.imm 1)) fun hi0 =>
     .group (sig := [[i64, i64]]) (fun J35 => .cons (fun p =>
       .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p.fst, .var p.snd.fst, ())) fun b =>
       .jnz (.var b.fst)
         (.let_ (op64 (.mul i64) (.var p.fst) (.imm 4)) fun o1 =>
          .let_ (op64 (.add i64) (.var pTmp) (.var o1.fst)) fun a1 =>
          .load i32 (.var a1.fst) fun sw =>
          .let_ (op64 (.mul i64) (.var p.fst) (.imm 4)) fun o2 =>
          .let_ (op64 (.add i64) (.var pTmp) (.var o2.fst)) fun a2 =>
          .let_ (op64 (.mul i64) (.var p.snd.fst) (.imm 4)) fun o3 =>
          .let_ (op64 (.add i64) (.var pTmp) (.var o3.fst)) fun a3 =>
          .load i32 (.var a3.fst) fun vhi =>
          .store (.var vhi) (.var a2.fst)
            (.let_ (op64 (.mul i64) (.var p.snd.fst) (.imm 4)) fun o4 =>
             .let_ (op64 (.add i64) (.var pTmp) (.var o4.fst)) fun a4 =>
             .store (.var sw) (.var a4.fst)
               (.let_ (op64 (.add i64) (.var p.fst) (.imm 1)) fun nlo =>
                .let_ (op64 (.sub i64) (.var p.snd.fst) (.imm 1)) fun nhi =>
                .jump J35.fst (.var nlo.fst, .var nhi.fst, ()))))
         (.group (sig := [[i64]]) (fun J39 => .cons (fun rb =>
           .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var rb.fst, .var keep, ())) fun brb =>
           .jnz (.var brb.fst)
             (.let_ (op64 (.mul i64) (.var rb.fst) (.imm 4)) fun o1 =>
              .let_ (op64 (.add i64) (.var pTmp) (.var o1.fst)) fun a1 =>
              .load i32 (.var a1.fst) fun v44 =>
              .let_ (Op.mk (.zext 32 64) (.var v44, ())) fun v45 =>
              .let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun v46 =>
              .let_ (op64 (.lshr i64) (.var v45.fst) (.var v46.fst)) fun v47 =>
              .let_ (op64 (.mul i64) (.var v47.fst) (.imm 4)) fun v48 =>
              .let_ (op64 (.add i64) (.var pLvl) (.var v48.fst)) fun v49 =>
              .load i32 (.var v49.fst) fun rl =>
              .let_ (op64 (.add i64) (.var rb.fst) (.imm 1)) fun re0 =>
              .group (sig := [[i64]]) (fun J52 => .cons (fun re =>
                .group (sig := [[]]) (fun _ => .cons (fun _ =>
                  .let_ (op64 (.sub i64) (.var re.fst) (.imm 1)) fun rh0 =>
                  s13MinRevLoopExpr pTmp rb.fst rh0.fst (.jump J39.fst (.var re.fst, ()))) .nil)
                  fun J54 =>
                .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var re.fst, .var keep, ())) fun bre =>
                .jnz (.var bre.fst)
                  (.let_ (op64 (.mul i64) (.var re.fst) (.imm 4)) fun o2 =>
                   .let_ (op64 (.add i64) (.var pTmp) (.var o2.fst)) fun a2 =>
                   .load i32 (.var a2.fst) fun v58 =>
                   .let_ (Op.mk (.zext 32 64) (.var v58, ())) fun v59 =>
                   .let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun v60 =>
                   .let_ (op64 (.lshr i64) (.var v59.fst) (.var v60.fst)) fun v61 =>
                   .let_ (op64 (.mul i64) (.var v61.fst) (.imm 4)) fun v62 =>
                   .let_ (op64 (.add i64) (.var pLvl) (.var v62.fst)) fun v63 =>
                   .load i32 (.var v63.fst) fun v64 =>
                   .let_ (Op.mk (.cmp .eq i32 .bool rfl) (.var v64, .var rl, ())) fun beq =>
                   .jnz (.var beq.fst)
                     (.let_ (op64 (.add i64) (.var re.fst) (.imm 1)) fun re1 =>
                      .jump J52.fst (.var re1.fst, ()))
                     (.jump J54.fst ()))
                  (.jump J54.fst ())) .nil)
                fun J52 => .jump J52.fst (.var re0.fst, ()))
             (.jump J32.fst ())) .nil)
           fun J39 => .jump J39.fst (.imm 1, ()))) .nil)
       fun J35 => .jump J35.fst (.imm 1, .var hi0.fst, ()))
    (.jump J32.fst ())

private theorem s13_min_rev_loop_wp {Γ : Env} {c : FullCfg} {s : FullState}
    {tmp0 : List (BitVec 32)} {keep : Nat} {lo0 hi0 : Val i64} {R : Mem 64 → Prop}
    {Q : Post []} {X : XPost} {K : Expr Val Cont []} {m : Mem 64}
    (_hlen : s.LengthsOk c) (hkl : keep ≤ c.max_vars) (ht0 : tmp0.length = c.max_vars)
    (hinv0 : S13TmpRevInv tmp0 s.core.tmp keep)
    (hlo1 : 1 ≤ lo0.toNat) (hhi_lt : hi0.toNat < keep)
    (hm : (FullMem c s ⋆ R) m)
    (hK : ∀ tmp' m', S13TmpRevInv tmp0 tmp' keep →
      (FullMem c { s with core := { s.core with tmp := tmp' } } ⋆ R) m' → wp Γ Q X K m') :
    wp Γ Q X (s13MinRevLoopExpr c.pTmp lo0 hi0 K) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  dsimp only [s13MinRevLoopExpr]
  refine wp_loop_group (ts := [i64, i64]) (fun n (lo, hi, ()) mk =>
      n = hi.toNat - lo.toNat ∧ 1 ≤ lo.toNat ∧ hi.toNat < keep ∧
      ∃ tmp_k, S13TmpRevInv tmp0 tmp_k keep ∧
        (FullMem c { s with core := { s.core with tmp := tmp_k } } ⋆ R) mk) ?_
    (fun Js hJs => by
      s13_lets; exact hJs (hi0.toNat - lo0.toNat) (lo0, hi0, ()) m
        ⟨rfl, hlo1, hhi_lt, s.core.tmp, hinv0, hm⟩)
  rintro Js n ⟨lo, hi, ⟨⟩⟩ mk hJs ⟨rfl, hlo_1, hhi_k, tmp_k, hinv_k, hmk⟩
  let st_k : FullState := { s with core := { s.core with tmp := tmp_k } }
  rw [Blocks.get_here]; s13_lets; ml_jnz; refine ⟨fun hlt => ?_, fun hge => ?_⟩
  · c0_cond hlt
    have htl : tmp_k.length = c.max_vars := hinv_k.1.trans ht0
    have hlo_arr : lo.toNat < st_k.core.tmp.length := by dsimp only [st_k]; omega
    have hhi_arr : hi.toNat < st_k.core.tmp.length := by dsimp only [st_k]; omega
    ml_ld c0_load_full_tmp (s := st_k) (i := lo) hlo_arr hmk
    let sw := st_k.core.tmp[lo.toNat]'hlo_arr
    ml_ld c0_load_full_tmp (s := st_k) (i := hi) hhi_arr hmk
    let vhi := st_k.core.tmp[hi.toNat]'hhi_arr
    ml_st m1, hm1 := c0_store_full_tmp (s := st_k) (i := lo) vhi hlo_arr hmk
    let st1 : FullState := { st_k with core := { st_k.core with tmp := tmp_k.set lo.toNat vhi } }
    have hhi_arr1 : hi.toNat < st1.core.tmp.length := by
      dsimp only [st1]; rw [List.length_set]; omega
    ml_st m2, hm2 := c0_store_full_tmp (s := st1) (i := hi) sw hhi_arr1 hm1
    have hinv_n : S13TmpRevInv tmp0 ((tmp_k.set lo.toNat vhi).set hi.toNat sw) keep :=
      s13TmpRevInv_swap hinv_k hlo_1 (by omega) (by omega) hhi_k (by omega) hlo_arr hhi_arr
    have hlo_add : (lo + 1).toNat = lo.toNat + 1 := min_bv64_add1 (by omega)
    have hhi_sub : (hi - 1).toNat = hi.toNat - 1 := s13_bv64_sub1 (by omega)
    s13_lets
    exact hJs ((hi - 1).toNat - (lo + 1).toNat) (lo + 1, hi - 1, ()) m2 (by omega)
      ⟨rfl, by omega, by omega, (tmp_k.set lo.toNat vhi).set hi.toNat sw, hinv_n, hm2⟩
  · exact hK tmp_k mk hinv_k hmk

theorem s13_min_shrink_rev_wp {Γ : Env} {c : FullCfg} {s : FullState}
    {keep_bv : Val i64} {R : Mem 64 → Prop} {Q : Post []} {X : XPost} {K : Expr Val Cont []}
    {m : Mem 64}
    (hlen : s.LengthsOk c) (hkp_cv : keep_bv.toNat ≤ s.core.cur_vars)
    (hlits_lt : ∀ j, 1 ≤ j → j < keep_bv.toNat →
      (s.core.tmp[j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hK : ∀ tmp' m', S13TmpRevInv s.core.tmp tmp' keep_bv.toNat →
      (FullMem c { s with core := { s.core with tmp := tmp' } } ⋆ R) m' → wp Γ Q X K m') :
    wp Γ Q X (s13MinRevExpr c.pTmp c.pLevel keep_bv K) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv := hlen.core_ok.cur_vars_le; have htl0 := hlen.core_ok.tmp_len_arr
  have hlvl_len := hlen.core_ok.lvl_len
  dsimp only [s13MinRevExpr]
  refine wp_join_group (ts := []) (fun _ mf =>
      ∃ tmp_f, S13TmpRevInv s.core.tmp tmp_f keep_bv.toNat ∧
        (FullMem c { s with core := { s.core with tmp := tmp_f } } ⋆ R) mf)
    (fun _ ⟨⟩ mf ⟨tmp_f, hinv_f, hmf⟩ => by rw [Blocks.get_here]; exact hK tmp_f mf hinv_f hmf) ?_
  rintro J32 hJ32; s13_lets; ml_jnz; refine ⟨fun hgt => ?_, fun hle => ?_⟩
  · c0_cond hgt
    have hkp2 : 2 < keep_bv.toNat := by
      simpa only [show (2 : BitVec 64).toNat = 2 from rfl] using hgt
    have hhi0 : (keep_bv - 1).toNat = keep_bv.toNat - 1 := s13_bv64_sub1 (by omega)
    s13_lets
    refine s13_min_rev_loop_wp (keep := keep_bv.toNat) hlen (by omega) htl0
      (s13TmpRevInv_refl _ _) (by exact le_refl _) (by rw [hhi0]; omega) hm
      fun tmp1 m1 hinv1 hm1 => ?_
    refine wp_loop_group (ts := [i64]) (fun n (rb, ()) mrb =>
        n = keep_bv.toNat - rb.toNat ∧ 1 ≤ rb.toNat ∧ rb.toNat ≤ keep_bv.toNat ∧
        ∃ tmp_r, S13TmpRevInv s.core.tmp tmp_r keep_bv.toNat ∧
          (FullMem c { s with core := { s.core with tmp := tmp_r } } ⋆ R) mrb) ?_
      (fun J39 hJ39 => by
        s13_lets; exact hJ39 (keep_bv.toNat - 1) (1#64, ()) m1
          ⟨by exact rfl, by exact le_refl _, by change 1 ≤ keep_bv.toNat; omega, tmp1, hinv1, hm1⟩)
    rintro J39 n ⟨rb, ⟨⟩⟩ mrb hJ39 ⟨rfl, hrb1, hrb_le, tmp_r, hinv_r, hmrb⟩
    let st_r : FullState := { s with core := { s.core with tmp := tmp_r } }
    have hlen_r : st_r.LengthsOk c :=
      ⟨{ hlen.core_ok with tmp_len_arr := hinv_r.1.trans htl0 }, hlen.scratch_ok⟩
    rw [Blocks.get_here]; s13_lets; ml_jnz; refine ⟨fun hrb_lt => ?_, fun hrb_ge => ?_⟩
    · c0_cond hrb_lt
      have hrb_arr : rb.toNat < st_r.core.tmp.length := by
        dsimp only [st_r]; rw [hinv_r.1, htl0]; omega
      ml_ld c0_load_full_tmp (s := st_r) (i := rb) hrb_arr hmrb
      let v44 := st_r.core.tmp[rb.toNat]'hrb_arr
      have hv44_lt : v44.toNat < 2 * s.core.cur_vars := by
        obtain ⟨i, hi1, hi2, heq⟩ := hinv_r.2.2.2 rb.toNat hrb1 hrb_lt
        have hi := hlits_lt i hi1 hi2
        rw [← heq, List.getElem?_eq_getElem hrb_arr, Option.getD_some] at hi; exact hi
      have hv47_lt : (v44.setWidth 64 >>> (1 : BitVec 32).signExtend 64).toNat <
          st_r.core.lvl.length := by
        rw [s13_bv64_zext32_lshr_sext1]; dsimp only [st_r]; rw [hlvl_len]; omega
      s13_lets
      ml_ld c0_load_full_lvl (s := st_r) (i := v44.setWidth 64 >>> (1 : BitVec 32).signExtend 64)
        hv47_lt hmrb
      let rl := st_r.core.lvl[(v44.setWidth 64 >>> (1 : BitVec 32).signExtend 64).toNat]'hv47_lt
      have hrb1_nat : (rb + 1).toNat = rb.toNat + 1 := min_bv64_add1 (by omega)
      s13_lets
      refine wp_loop_group (ts := [i64]) (fun n_e (re, ()) mre =>
          n_e = keep_bv.toNat - re.toNat ∧ mre = mrb ∧
          rb.toNat < re.toNat ∧ re.toNat ≤ keep_bv.toNat) ?_
        (fun J52 hJ52 => by
          s13_lets; exact hJ52 (keep_bv.toNat - (rb + 1).toNat) (rb + 1, ()) mrb
            ⟨rfl, rfl, by omega, by omega⟩)
      rintro J52 n_e ⟨re, ⟨⟩⟩ mre hJ52 ⟨rfl, hmre, hrb_re, hre_le⟩
      subst mre; rw [Blocks.get_here]
      refine wp_join_group (ts := []) (fun _ m54 => m54 = mrb)
        (fun _ ⟨⟩ m54 hm54 => by
          subst m54; rw [Blocks.get_here]; s13_lets
          have hrh0 : (re - 1).toNat = re.toNat - 1 := s13_bv64_sub1 (by omega)
          refine s13_min_rev_loop_wp hlen_r (by omega) htl0 hinv_r hrb1 (by rw [hrh0]; omega) hmrb
            fun tmp_n mn hinv_n hmn => ?_
          exact hJ39 (keep_bv.toNat - re.toNat) (re, ()) mn (by omega)
            ⟨rfl, by omega, hre_le, tmp_n, hinv_n, hmn⟩) ?_
      rintro J54 hJ54; s13_lets; ml_jnz; refine ⟨fun hre_lt => ?_, fun _ => hJ54 () mrb rfl⟩
      c0_cond hre_lt
      have hre_arr : re.toNat < st_r.core.tmp.length := by
        dsimp only [st_r]; rw [hinv_r.1, htl0]; omega
      ml_ld c0_load_full_tmp (s := st_r) (i := re) hre_arr hmrb
      let v58 := st_r.core.tmp[re.toNat]'hre_arr
      have hv58_lt : v58.toNat < 2 * s.core.cur_vars := by
        obtain ⟨i, hi1, hi2, heq⟩ := hinv_r.2.2.2 re.toNat (by omega) hre_lt
        have hi := hlits_lt i hi1 hi2
        rw [← heq, List.getElem?_eq_getElem hre_arr, Option.getD_some] at hi; exact hi
      have hv61_lt : (v58.setWidth 64 >>> (1 : BitVec 32).signExtend 64).toNat <
          st_r.core.lvl.length := by
        rw [s13_bv64_zext32_lshr_sext1]; dsimp only [st_r]; rw [hlvl_len]; omega
      s13_lets
      ml_ld c0_load_full_lvl (s := st_r) (i := v58.setWidth 64 >>> (1 : BitVec 32).signExtend 64)
        hv61_lt hmrb
      s13_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => hJ54 () mrb rfl⟩
      have hre1 : (re + 1).toNat = re.toNat + 1 := min_bv64_add1 (by omega)
      s13_lets
      exact hJ52 (keep_bv.toNat - (re + 1).toNat) (re + 1, ()) mrb (by omega)
        ⟨rfl, rfl, by omega, by omega⟩
    · exact hJ32 () mrb ⟨tmp_r, hinv_r, hmrb⟩
  · exact hJ32 () m ⟨s.core.tmp, s13TmpRevInv_refl _ _, hm⟩

/-! ## 4. ASTs & WP Lemmas for Mark-Init, Compact & Clean (`s13MinCleanExpr`) -/

abbrev s13MinMarkInitExpr {V : Ty → Type} {C : List Ty → Type} (p orig_tlen pTmp : V i64)
    (K : Expr V C []) : Expr V C [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .group (sig := [[i64]]) (fun Js => .cons (fun p_14 =>
    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p_14.fst, .var orig_tlen, ())) fun p_15 =>
    .jnz (.var p_15.fst)
      (.let_ (op64 (.mul i64) (.var p_14.fst) (.imm 4)) fun p_16 =>
       .let_ (op64 (.add i64) (.var pTmp) (.var p_16.fst)) fun p_17 =>
       .load i32 (.var p_17.fst) fun ld =>
       .let_ (Op.mk (.lshr i32) (.var ld, .imm 1, ())) fun p_18 =>
       .let_ (Op.mk (.trunc 32 8) (.imm 2, ())) fun p_19 =>
       .call "full_min_mark" (as := [i64, i32, i8]) (bs := [])
         (.var p, .var p_18.fst, .var p_19.fst, ()) fun _ =>
       .let_ (op64 (.add i64) (.var p_14.fst) (.imm 1)) fun p =>
       .jump Js.fst (.var p.fst, ()))
      K) .nil)
    (fun Js => .jump Js.fst (.imm 0, ()))

abbrev s13MinCompactLoopExpr {V : Ty → Type} {C : List Ty → Type} (bound pTmp : V i64)
    (K : V i64 → Expr V C []) : Expr V C [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .group (sig := [[i64, i64]]) (fun Js => .cons (fun p_18 =>
    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p_18.snd.fst, .var bound, ())) fun p_19 =>
    .jnz (.var p_19.fst)
      (.group (sig := [[i64]]) (fun _Js_1 => .cons (fun p =>
        .let_ (op64 (.add i64) (.var p_18.snd.fst) (.imm 1)) fun p_20 =>
        .jump Js.fst (.var p.fst, .var p_20.fst, ())) .nil) fun Js =>
       .let_ (op64 (.mul i64) (.var p_18.snd.fst) (.imm 4)) fun p =>
       .let_ (op64 (.add i64) (.var pTmp) (.var p.fst)) fun p =>
       .load i32 (.var p.fst) fun ld =>
       .let_ (Op.mk (.cmp .ne i32 .bool rfl) (.var ld, .imm 4294967295, ())) fun p =>
       .jnz (.var p.fst)
         (.let_ (op64 (.mul i64) (.var p_18.fst) (.imm 4)) fun p =>
          .let_ (op64 (.add i64) (.var pTmp) (.var p.fst)) fun p =>
          .let_ (op64 (.mul i64) (.var p_18.snd.fst) (.imm 4)) fun p_20 =>
          .let_ (op64 (.add i64) (.var pTmp) (.var p_20.fst)) fun p_21 =>
          .load i32 (.var p_21.fst) fun ld =>
          .store (.var ld) (.var p.fst)
            (.let_ (op64 (.add i64) (.var p_18.fst) (.imm 1)) fun p =>
             .jump Js.fst (.var p.fst, ())))
         (.jump Js.fst (.var p_18.fst, ())))
      (K p_18.fst)) .nil)
    (fun Js => .jump Js.fst (.imm 1, .imm 1, ()))

abbrev s13MinCleanExpr {V : Ty → Type} {C : List Ty → Type}
    (p cv orig_tlen pTmp pLvl pMark keep : V i64) : Expr V C [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .group (sig := [[]]) (fun _Js => .cons (fun _ =>
    .let_ (op64 (.add i64) (.var p) (.imm 272)) fun p_22 =>
    .store (t := i64) (.imm 0) (.var p_22.fst)
      (.let_ (op64 (.add i64) (.var p) (.imm 280)) fun p_23 =>
       .store (t := i64) (.imm 0) (.var p_23.fst)
         (.let_ (op64 (.add i64) (.var p) (.imm 192)) fun p_24 =>
          .store (.var keep) (.var p_24.fst)
            (s13MinRevExpr pTmp pLvl keep
              (.let_ (op64 (.add i64) (.var p) (.imm 352)) fun p_25 =>
               .load i64 (.var p_25.fst) fun ld =>
               .let_ (op64 (.sub i64) (.var orig_tlen) (.var keep)) fun p_26 =>
               .let_ (op64 (.add i64) (.var ld) (.var p_26.fst)) fun p_27 =>
               .let_ (op64 (.add i64) (.var p) (.imm 352)) fun p_28 =>
               .store (.var p_27.fst) (.var p_28.fst)
                 (.let_ (op64 (.add i64) (.var p) (.imm 344)) fun p_29 =>
                  .load i64 (.var p_29.fst) fun ld =>
                  .let_ (op64 (.add i64) (.var ld) (.var keep)) fun p_30 =>
                  .let_ (op64 (.add i64) (.var p) (.imm 344)) fun p =>
                  .store (.var p_30.fst) (.var p.fst) (.ret ()))))))) .nil)
    (fun Js =>
      .let_ (op64 (.add i64) (.var p) (.imm 280)) fun p_21 =>
      .load i64 (.var p_21.fst) fun ld_7 =>
      .let_ (Op.mk (.cmp .ne i64 .bool rfl) (.var ld_7, .imm 0, ())) fun p_22 =>
      .jnz (.var p_22.fst)
        (.group (sig := [[i64]]) (fun Js_1 => .cons (fun p =>
          .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p.fst, .var cv, ())) fun p_23 =>
          .jnz (.var p_23.fst)
            (.let_ (op64 (.add i64) (.var pMark) (.var p.fst)) fun p_24 =>
             .let_ (Op.mk (.trunc 32 8) (.imm 0, ())) fun p_25 =>
             .store (.var p_25.fst) (.var p_24.fst)
               (.let_ (op64 (.add i64) (.var p.fst) (.imm 1)) fun p =>
                .jump Js_1.fst (.var p.fst, ())))
            (.jump Js.fst ())) .nil)
          (fun Js => .jump Js.fst (.imm 0, ())))
        (.let_ (op64 (.add i64) (.var p) (.imm 240)) fun p_23 =>
         .load i64 (.var p_23.fst) fun ld_8 =>
         .group (sig := [[i64]]) (fun Js_1 => .cons (fun p_24 =>
           .let_ (op64 (.add i64) (.var p) (.imm 272)) fun p =>
           .load i64 (.var p.fst) fun ld_9 =>
           .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p_24.fst, .var ld_9, ())) fun p =>
           .jnz (.var p.fst)
             (.let_ (op64 (.mul i64) (.var p_24.fst) (.imm 4)) fun p =>
              .let_ (op64 (.add i64) (.var ld_8) (.var p.fst)) fun p =>
              .load i32 (.var p.fst) fun ld_10 =>
              .group (sig := [[]]) (fun _ => .cons (fun _ =>
                .let_ (op64 (.add i64) (.var p_24.fst) (.imm 1)) fun p =>
                .jump Js_1.fst (.var p.fst, ())) .nil) fun Js =>
              .let_ (Op.mk (.zext 32 64) (.var ld_10, ())) fun p =>
              .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p.fst, .var cv, ())) fun p =>
              .jnz (.var p.fst)
                (.let_ (Op.mk (.zext 32 64) (.var ld_10, ())) fun p =>
                 .let_ (op64 (.add i64) (.var pMark) (.var p.fst)) fun p =>
                 .let_ (Op.mk (.trunc 32 8) (.imm 0, ())) fun p_25 =>
                 .store (.var p_25.fst) (.var p.fst) (.jump Js.fst ()))
                (.jump Js.fst ()))
             (.jump Js.fst ())) .nil)
           (fun Js => .jump Js.fst (.imm 0, ()))))

theorem s13_min_shrink_compact_loop_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {s : FullState} {tlen : Nat} {tlen_bv : BitVec 64} {R : Mem 64 → Prop}
    {Q : Post []} {X : XPost}
    (hcore : FullOtfsCoreInv c F0 s) (ht1 : 1 ≤ tlen) (ht_cv : tlen ≤ s.core.cur_vars)
    (htlen_eq : tlen_bv.toNat = tlen)
    (h0ne : s.core.tmp[0]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hvals : ∀ k < tlen, s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hlvls : ∀ k, 1 ≤ k → k < tlen → s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level)
    {m : Mem 64} (hm : (FullMem c s ⋆ R) m)
    {K : Val i64 → Expr Val Cont []}
    (hK : ∀ (keep_bv : Val i64) (tmp_c : List (BitVec 32)) (mc : Mem 64),
      let s_c : FullState := { s with core := { s.core with tmp := tmp_c } }
      let keep := keep_bv.toNat
      tmp_c.length = c.max_vars → 1 ≤ keep → keep ≤ tlen → tmp_c[0]? = s.core.tmp[0]? →
      (tmp_c.take keep).map BitVec.toNat =
        ((s.core.tmp.take tlen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat →
      (∀ k < keep, tmp_c[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) →
      (∀ j, 1 ≤ j → j < keep →
        let l := (tmp_c[j]?.getD 0#32).toNat; let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        0 < lv ∧ lv < s.core.cur_level) →
      (FullMem c s_c ⋆ R) mc → wp Γ Q X (K keep_bv) mc) :
    wp Γ Q X (s13MinCompactLoopExpr tlen_bv c.pTmp K) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hlen := hcore.1.core_ok; have hcv := hlen.cur_vars_le
  have h1v : (1#64 : BitVec 64).toNat = 1 := rfl
  dsimp only [s13MinCompactLoopExpr]
  refine wp_loop_group (ts := [i64, i64]) (fun n (keep_bv, k_bv, ()) mk =>
      n = tlen - k_bv.toNat ∧ 1 ≤ keep_bv.toNat ∧ keep_bv.toNat ≤ k_bv.toNat ∧ k_bv.toNat ≤ tlen ∧
      ∃ (tmp_k : List (BitVec 32)),
        let st_k : FullState := { s with core := { s.core with tmp := tmp_k } }
        tmp_k.length = c.max_vars ∧ tmp_k[0]? = s.core.tmp[0]? ∧
        (∀ j, k_bv.toNat ≤ j → j < tlen → tmp_k[j]? = s.core.tmp[j]?) ∧
        (tmp_k.take keep_bv.toNat).map BitVec.toNat =
          ((s.core.tmp.take k_bv.toNat).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat ∧
        (∀ j < keep_bv.toNat, tmp_k[j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) ∧
        (∀ j, 1 ≤ j → j < keep_bv.toNat →
          let l := (tmp_k[j]?.getD 0#32).toNat; let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
          l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧ 0 < lv ∧
          lv < s.core.cur_level) ∧
        (FullMem c st_k ⋆ R) mk) ?_
    (fun Js hJs => by
      s13_lets
      have h0tl : 0 < s.core.tmp.length := by rw [hlen.tmp_len_arr]; omega
      have htk1 : s.core.tmp.take 1 = [s.core.tmp[0]'h0tl] := by
        generalize hxs : s.core.tmp = xs at h0tl ⊢
        cases xs with | nil => simp at h0tl | cons _ _ => rfl
      have h0ne' : s.core.tmp[0]'h0tl ≠ 0xFFFFFFFF#32 := by
        rwa [List.getElem?_eq_getElem h0tl, Option.getD_some] at h0ne
      have hkf0 : (s.core.tmp.take (1#64).toNat).map BitVec.toNat =
          ((s.core.tmp.take (1#64).toNat).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat := by
        rw [h1v, htk1]; simp [h0ne']
      exact hJs (tlen - 1) (1#64, 1#64, ()) m
        ⟨by rw [h1v], by rw [h1v]; exact le_refl _, by rw [h1v]; exact le_refl _,
          by rw [h1v]; exact ht1, s.core.tmp, hlen.tmp_len_arr, rfl, (fun _ _ _ => rfl),
          hkf0, (fun j hj => by rw [h1v] at hj; obtain rfl : j = 0 := (by omega); exact h0ne),
          (fun j hj1 hj2 => by rw [h1v] at hj2; omega), hm⟩)
  rintro Js n ⟨keep_bv, k_bv, ⟨⟩⟩ mk hJs ⟨rfl, hkp1, hkp_k, hk_tl, tmp_k, htk_len, htk0, htail,
    hf_eq, hkp_ne, hkp_ok, hmk⟩
  let st_k : FullState := { s with core := { s.core with tmp := tmp_k } }
  rw [Blocks.get_here]; s13_lets; ml_jnz; refine ⟨fun hk_lt => ?_, fun hk_ge => ?_⟩
  · have hkx : k_bv.toNat < tlen := by
      rw [BitVec.ult, decide_eq_true_eq, htlen_eq] at hk_lt; exact hk_lt
    have hk_arr : k_bv.toNat < st_k.core.tmp.length := by dsimp only [st_k]; rw [htk_len]; omega
    have hk1 : (k_bv + 1).toNat = k_bv.toNat + 1 := min_bv64_add1 (by omega)
    refine wp_join_group (ts := [i64]) (fun (keep_n, ()) m_n =>
        1 ≤ keep_n.toNat ∧ keep_n.toNat ≤ k_bv.toNat + 1 ∧
        ∃ tmp_n,
          let st_n : FullState := { s with core := { s.core with tmp := tmp_n } }
          tmp_n.length = c.max_vars ∧ tmp_n[0]? = s.core.tmp[0]? ∧
          (∀ j, k_bv.toNat + 1 ≤ j → j < tlen → tmp_n[j]? = s.core.tmp[j]?) ∧
          (tmp_n.take keep_n.toNat).map BitVec.toNat =
            ((s.core.tmp.take (k_bv.toNat + 1)).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat ∧
          (∀ j < keep_n.toNat, tmp_n[j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) ∧
          (∀ j, 1 ≤ j → j < keep_n.toNat →
            let l := (tmp_n[j]?.getD 0#32).toNat; let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
            l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧ 0 < lv ∧
            lv < s.core.cur_level) ∧
          (FullMem c st_n ⋆ R) m_n)
      (fun _ ⟨keep_n, ⟨⟩⟩ m_n ⟨hkn1, hkn_le, tmp_n, htn_len, htn0, hntail, hnf_eq, hkn_ne,
          hkn_ok, hmn⟩ => by
        rw [Blocks.get_here]; s13_lets
        exact hJs (tlen - (k_bv + 1).toNat) (keep_n, k_bv + 1, ()) m_n (by omega)
          ⟨rfl, hkn1, by rw [hk1]; exact hkn_le, by rw [hk1]; exact hkx,
            tmp_n, htn_len, htn0, fun j hj1 hj2 => hntail j (by rw [hk1] at hj1; exact hj1) hj2,
            by rw [hk1]; exact hnf_eq, hkn_ne, hkn_ok, hmn⟩) ?_
    rintro Jkp hJkp
    ml_ld c0_load_full_tmp (s := st_k) (i := k_bv) hk_arr hmk
    let v_k := st_k.core.tmp[k_bv.toNat]'hk_arr
    have hvk_orig : tmp_k[k_bv.toNat]? = s.core.tmp[k_bv.toNat]? := htail k_bv.toNat (le_refl _) hkx
    have htake_k1 : s.core.tmp.take (k_bv.toNat + 1) =
        s.core.tmp.take k_bv.toNat ++ [v_k] := by
      rw [List.take_add_one, ← hvk_orig, List.getElem?_eq_getElem hk_arr]; rfl
    s13_lets; ml_jnz; refine ⟨fun hne => ?_, fun heq => ?_⟩
    · have hvk_ne : v_k ≠ 0xFFFFFFFF#32 := by c0_cond hne; exact hne
      have hvk_ne' : s.core.tmp[k_bv.toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
        rw [← hvk_orig, List.getElem?_eq_getElem hk_arr, Option.getD_some]; exact hvk_ne
      have hk_keep : keep_bv.toNat < st_k.core.tmp.length := by
        dsimp only [st_k]; rw [htk_len]; omega
      ml_ld c0_load_full_tmp (s := st_k) (i := k_bv) hk_arr hmk
      ml_st mk', hmk' := c0_store_full_tmp (s := st_k) (i := keep_bv) v_k hk_keep hmk
      let tmp_n := tmp_k.set keep_bv.toNat v_k
      have hkp1_nat : (keep_bv + 1).toNat = keep_bv.toNat + 1 := min_bv64_add1 (by omega)
      have hv_orig_get : (s.core.tmp[k_bv.toNat]?.getD 0#32).toNat = v_k.toNat := by
        rw [← hvk_orig, List.getElem?_eq_getElem hk_arr, Option.getD_some]
      have hvk_vals := hvals k_bv.toNat hkx hvk_ne'
      have hvk_lvls : 0 < (s.core.lvl[v_k.toNat / 2]?.getD 0#32).toNat ∧
          (s.core.lvl[v_k.toNat / 2]?.getD 0#32).toNat < s.core.cur_level := by
        rw [← hv_orig_get]; exact hlvls k_bv.toNat (by omega) hkx hvk_ne'
      s13_lets
      refine hJkp (keep_bv + 1, ()) mk' ⟨by rw [hkp1_nat]; omega, by rw [hkp1_nat]; omega,
        tmp_n, by simp [tmp_n, htk_len], by rw [List.getElem?_set_ne (by omega)]; exact htk0,
        fun j hj1 hj2 => by rw [List.getElem?_set_ne (by omega)]; exact htail j (by omega) hj2,
        ?_, fun j hj => ?_, fun j hj1 hj2 => ?_, hmk'⟩
      · rw [hkp1_nat, s13ListTakeSuccSet _ (by rw [htk_len]; omega), List.map_append, hf_eq,
          htake_k1, List.filter_append, List.filter_cons, decide_eq_true hvk_ne]
        simp
      · rw [hkp1_nat] at hj; by_cases hjk : j = keep_bv.toNat
        · subst j; rw [List.getElem?_set_self (by rw [htk_len]; omega), Option.getD_some]
          exact hvk_ne
        · rw [List.getElem?_set_ne (Ne.symm hjk)]; exact hkp_ne j (by omega)
      · rw [hkp1_nat] at hj2; by_cases hjk : j = keep_bv.toNat
        · subst j; rw [List.getElem?_set_self (by rw [htk_len]; omega), Option.getD_some]
          rw [hv_orig_get] at hvk_vals
          exact ⟨hvk_vals.1, hvk_vals.2, hvk_lvls.1, hvk_lvls.2⟩
        · rw [List.getElem?_set_ne (Ne.symm hjk)]; exact hkp_ok j hj1 (by omega)
    · have hvk_eq : v_k = 0xFFFFFFFF#32 := by c0_cond heq; exact heq
      refine hJkp (keep_bv, ()) mk ⟨hkp1, by omega, tmp_k, htk_len, htk0,
        fun j hj1 hj2 => htail j (by omega) hj2, ?_, hkp_ne, hkp_ok, hmk⟩
      rw [hf_eq, htake_k1, List.filter_append, List.filter_cons,
        decide_eq_false (by simpa using hvk_eq)]
      simp
  · c0_cond hk_ge
    have hk_eq : k_bv.toNat = tlen := by rw [htlen_eq] at hk_ge; omega
    subst hk_eq
    exact hK keep_bv tmp_k mk htk_len hkp1 hkp_k htk0 hf_eq hkp_ne hkp_ok hmk

theorem s13_min_shrink_clean_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {keep_bv orig_tlen_bv : Val i64} {R : Mem 64 → Prop} {Q : Post []} {X : XPost}
    (hcore : FullOtfsCoreInv c F0 s) (htl_cv : keep_bv.toNat ≤ s.core.cur_vars)
    (_hkeep_le : keep_bv.toNat ≤ orig_tlen_bv.toNat)
    (_horig_le : orig_tlen_bv.toNat ≤ s.core.cur_vars)
    (hmin : FullMinMarkInv s.core
      (((s.core.tmp.take keep_bv.toNat).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
    (hno8 : ∀ v < s.core.cur_vars, (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8)
    (hlits_lt : ∀ j, 1 ≤ j → j < keep_bv.toNat →
      (s.core.tmp[j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    {m : Mem 64} (hm : (FullMem c s ⋆ R) m)
    (hpost : ∀ (tmp_f : List (BitVec 32)) (mrk' : List (BitVec 8)) (m' : Mem 64),
      let s' : FullState :=
        { s with
          core := { s.core with tmp := tmp_f, tmp_len := keep_bv.toNat, mrk := mrk',
                                min_clr_len := 0, min_clr_full := 0#64 }
          scratch := { s.scratch with
            min_removed := s.scratch.min_removed + (orig_tlen_bv - keep_bv),
            learned_lits := s.scratch.learned_lits + keep_bv } }
      S13TmpRevInv s.core.tmp tmp_f keep_bv.toNat →
      mrk'.length = c.max_vars → (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) →
      FullMarksClear s' → (FullMem c s' ⋆ R) m' → Q () m') :
    wp Γ Q X (s13MinCleanExpr c.hdr (BitVec.ofNat 64 s.core.cur_vars) orig_tlen_bv c.pTmp c.pLevel
      c.pMark keep_bv) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hlen := hcore.1.core_ok; have hcv := hlen.cur_vars_le
  have h0v : (0#64 : BitVec 64).toNat = 0 := rfl
  have hz8 : (0 : BitVec 32).setWidth 8 = 0#8 := rfl
  have hcv_bv : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars :=
    Nat.mod_eq_of_lt (by omega)
  dsimp only [s13MinCleanExpr]
  refine wp_join_group (ts := []) (fun _ m' =>
      ∃ (mrk' : List (BitVec 8)), mrk'.length = c.max_vars ∧
        (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) ∧
        (∀ v < s.core.cur_vars, mrk'[v]?.getD 0#8 = 0#8) ∧
        (FullMem c { s with core := { s.core with mrk := mrk' } } ⋆ R) m') ?_ ?_
  · rintro _ ⟨⟩ mf ⟨mrk', hml', hab', hmc', hmf⟩
    rw [Blocks.get_here]; s13_lets
    ml_st m1, hm1 := store_full_min_clr_len (s := { s with core := { s.core with mrk := mrk' } })
      0 (Nat.zero_lt_succ _) hmf
    ml_st m2, hm2 := store_full_min_clr_full
      (s := { s with core := { s.core with mrk := mrk', min_clr_len := 0 } }) 0#64 hm1
    ml_st m3, hm3 := c0_store_full_tmp_len
      (s := { s with core := { s.core with mrk := mrk', min_clr_len := 0, min_clr_full := 0#64 } })
      keep_bv hm2
    let s3 : FullState :=
      { s with core := { s.core with tmp_len := keep_bv.toNat, mrk := mrk',
                                     min_clr_len := 0, min_clr_full := 0#64 } }
    have hlen3 : s3.LengthsOk c :=
      ⟨{ hlen with tmp_len_le := le_trans htl_cv hcv, mrk_len := hml',
                   min_clr_len_le := Nat.zero_le _ }, hcore.1.scratch_ok⟩
    refine s13_min_shrink_rev_wp hlen3 htl_cv hlits_lt hm3 fun tmp_f m3r hinv_r hm3r => ?_
    let s3r : FullState := { s3 with core := { s3.core with tmp := tmp_f } }
    ml_ld load_full_min_removed (s := s3r) hm3r; s13_lets
    ml_st m4, hm4 := store_full_min_removed (s := s3r)
      (s.scratch.min_removed + (orig_tlen_bv - keep_bv)) hm3r
    ml_ld load_full_learned_lits
      (s := { s3r with scratch := { s3r.scratch with
        min_removed := s.scratch.min_removed + (orig_tlen_bv - keep_bv) } }) hm4
    s13_lets
    ml_st m5, hm5 := store_full_learned_lits
      (s := { s3r with scratch := { s3r.scratch with
        min_removed := s.scratch.min_removed + (orig_tlen_bv - keep_bv) } })
      (s.scratch.learned_lits + keep_bv) hm4
    rw [wp]; exact hpost tmp_f mrk' m5 hinv_r hml' hab' hmc' hm5
  rintro Js hJs; ml_ld load_full_min_clr_full hm; s13_lets; ml_jnz
  refine ⟨fun hnf => ?_, fun hf => ?_⟩
  · refine wp_loop_group (ts := [i64]) (fun n (v, ()) mv =>
        n = s.core.cur_vars - v.toNat ∧ v.toNat ≤ s.core.cur_vars ∧
        ∃ mrk_v : List (BitVec 8), mrk_v.length = c.max_vars ∧
          (∀ w, s.core.cur_vars ≤ w → mrk_v[w]? = s.core.mrk[w]?) ∧
          (∀ w < v.toNat, mrk_v[w]?.getD 0#8 = 0#8) ∧
          (FullMem c { s with core := { s.core with mrk := mrk_v } } ⋆ R) mv) ?_
      (fun J1 hJ1 => by
        s13_lets; exact hJ1 s.core.cur_vars (0#64, ()) m ⟨by rw [h0v]; omega,
          by rw [h0v]; exact Nat.zero_le _, s.core.mrk, hlen.mrk_len, fun _ _ => rfl,
          fun _ h => by rw [h0v] at h; omega, hm⟩)
    rintro J1 n ⟨v, ⟨⟩⟩ mv hJ1 ⟨rfl, hv_le, mrk_v, hml_v, hab_v, hzero_v, hm_v⟩
    let st_v : FullState := { s with core := { s.core with mrk := mrk_v } }
    rw [Blocks.get_here]; s13_lets; ml_jnz; refine ⟨fun hlt => ?_, fun hge => ?_⟩
    · have hvx : v.toNat < s.core.cur_vars := by
        rw [BitVec.ult, decide_eq_true_eq, hcv_bv] at hlt; exact hlt
      have hvm : v.toNat < st_v.core.mrk.length := by dsimp only [st_v]; rw [hml_v]; omega
      s13_lets
      ml_st mn, hmn := c0_store_full_mrk (s := st_v) (i := v) ((0 : BitVec 32).setWidth 8) hvm hm_v
      rw [hz8] at hmn
      have hv1 : (v + 1).toNat = v.toNat + 1 := min_bv64_add1 (by omega)
      s13_lets
      refine hJ1 (s.core.cur_vars - (v + 1).toNat) (v + 1, ()) mn (by omega)
        ⟨by rw [hv1], by rw [hv1]; omega, mrk_v.set v.toNat 0#8, by rw [List.length_set, hml_v],
          fun w hw => by rw [List.getElem?_set_ne (by omega)]; exact hab_v w hw,
          fun w hw => by
            rw [hv1] at hw; by_cases hwe : w = v.toNat
            · subst w; rw [List.getElem?_set_self (by rw [hml_v]; omega), Option.getD_some]
            · rw [List.getElem?_set_ne (Ne.symm hwe)]; exact hzero_v w (by omega),
          hmn⟩
    · have hve : v.toNat = s.core.cur_vars := by
        rw [BitVec.ult, decide_eq_false_iff_not, hcv_bv] at hge; omega
      exact hJs () mv ⟨mrk_v, hml_v, hab_v, fun w hw => hzero_v w (by omega), hm_v⟩
  · have hnf' : s.core.min_clr_full = 0#64 := by c0_cond hf; exact hf
    ml_ld load_full_min_clr_ptr hm; s13_lets
    refine wp_loop_group (ts := [i64]) (fun n (z, ()) mz =>
        n = s.core.min_clr_len - z.toNat ∧ z.toNat ≤ s.core.min_clr_len ∧
        ∃ mrk_z : List (BitVec 8), mrk_z.length = c.max_vars ∧
          (∀ w, s.core.cur_vars ≤ w → mrk_z[w]? = s.core.mrk[w]?) ∧
          (∀ w < s.core.cur_vars, mrk_z[w]?.getD 0#8 ≠ 0#8 →
            ∃ k, z.toNat ≤ k ∧ k < s.core.min_clr_len ∧ (s.core.min_clr[k]?.getD 0#32).toNat = w) ∧
          (FullMem c { s with core := { s.core with mrk := mrk_z } } ⋆ R) mz) ?_
      (fun J2 hJ2 => by
        s13_lets; refine hJ2 s.core.min_clr_len (0#64, ()) m
          ⟨by rw [h0v]; omega, by rw [h0v]; exact Nat.zero_le _, s.core.mrk, hlen.mrk_len,
            fun _ _ => rfl, fun w hw hnz => ?_, hm⟩
        obtain ⟨k, hk, hke⟩ :=
          hmin.clr_cov hnf' w hw ((s13MinMarkInvMrkNeZeroIff hmin hno8 hw).mp hnz)
        exact ⟨k, by rw [h0v]; exact Nat.zero_le _, hk, hke⟩)
    rintro J2 n ⟨z, ⟨⟩⟩ mz hJ2 ⟨rfl, hzle, mrk_z, hml_z, hab_z, hcov_z, hm_z⟩
    let st_z : FullState := { s with core := { s.core with mrk := mrk_z } }
    rw [Blocks.get_here]; ml_ld load_full_min_clr_len (s := st_z) hm_z; s13_lets; ml_jnz
    have hmcl_bv : (BitVec.ofNat 64 s.core.min_clr_len).toNat = s.core.min_clr_len :=
      Nat.mod_eq_of_lt (by have := hlen.min_clr_len_le; omega)
    refine ⟨fun hlt => ?_, fun hge => ?_⟩
    · have hzm : z.toNat < s.core.min_clr_len := by
        rw [BitVec.ult, decide_eq_true_eq, hmcl_bv] at hlt; exact hlt
      have hzl : z.toNat < st_z.core.min_clr.length := by
        dsimp only [st_z]; rw [hlen.min_clr_len_arr]; have := hlen.min_clr_len_le; omega
      have hz1 : (z + 1).toNat = z.toNat + 1 :=
        min_bv64_add1 (by have := hlen.min_clr_len_le; omega)
      ml_ld c0_load_full_min_clr (s := st_z) (i := z) hzl hm_z
      let v32 := st_z.core.min_clr[z.toNat]'hzl
      refine wp_join_group (ts := []) (fun _ mn =>
          ∃ mrk_n : List (BitVec 8), mrk_n.length = c.max_vars ∧
            (∀ w, s.core.cur_vars ≤ w → mrk_n[w]? = s.core.mrk[w]?) ∧
            (∀ w < s.core.cur_vars, mrk_n[w]?.getD 0#8 ≠ 0#8 →
              ∃ k, z.toNat + 1 ≤ k ∧ k < s.core.min_clr_len ∧
                (s.core.min_clr[k]?.getD 0#32).toNat = w) ∧
            (FullMem c { s with core := { s.core with mrk := mrk_n } } ⋆ R) mn)
        (fun _ ⟨⟩ mn ⟨mrk_n, hml_n, hab_n, hcov_n, hm_n⟩ => by
          rw [Blocks.get_here]; s13_lets
          exact hJ2 (s.core.min_clr_len - (z + 1).toNat) (z + 1, ()) mn (by omega)
            ⟨by rw [hz1], by rw [hz1]; omega, mrk_n, hml_n, hab_n,
              by simpa only [hz1] using hcov_n, hm_n⟩) ?_
      rintro Jstep hJstep
      s13_lets; ml_jnz; refine ⟨fun hvlt => ?_, fun hvge => ?_⟩
      · have hv_lt : v32.toNat < s.core.cur_vars := by
          rw [BitVec.ult, decide_eq_true_eq, bv_c0_zext32_64, hcv_bv] at hvlt; exact hvlt
        have hvm : (v32.setWidth 64).toNat < st_z.core.mrk.length := by
          dsimp only [st_z]; rw [hml_z, bv_c0_zext32_64]; omega
        s13_lets; ml_st mn, hmn := c0_store_full_mrk (s := st_z) (i := v32.setWidth 64)
          ((0 : BitVec 32).setWidth 8) hvm hm_z
        rw [hz8, bv_c0_zext32_64] at hmn
        refine hJstep () mn ⟨mrk_z.set v32.toNat 0#8, by rw [List.length_set, hml_z],
          fun w hw => by rw [List.getElem?_set_ne (by omega)]; exact hab_z w hw,
          fun w hw hnz => ?_, hmn⟩
        have hwne : w ≠ v32.toNat := by
          rintro rfl; rw [List.getElem?_set_self (by rw [hml_z]; omega)] at hnz; exact hnz rfl
        rw [List.getElem?_set_ne (Ne.symm hwne)] at hnz
        obtain ⟨k, hk1, hk2, hke⟩ := hcov_z w hw hnz
        have hknz : k ≠ z.toNat := by
          rintro rfl; rw [List.getElem?_eq_getElem hzl, Option.getD_some] at hke
          exact hwne hke.symm
        exact ⟨k, by omega, hk2, hke⟩
      · have hvx : s.core.cur_vars ≤ v32.toNat := by
          rw [BitVec.ult, decide_eq_false_iff_not, not_lt, bv_c0_zext32_64, hcv_bv] at hvge
          exact hvge
        refine hJstep () mz ⟨mrk_z, hml_z, hab_z, fun w hw hnz => ?_, hm_z⟩
        obtain ⟨k, hk1, hk2, hke⟩ := hcov_z w hw hnz
        have hknz : k ≠ z.toNat := by
          rintro rfl; dsimp only [v32] at hvx
          rw [show st_z.core.min_clr[z.toNat]'hzl =
                (some (st_z.core.min_clr[z.toNat]'hzl)).getD 0#32 from rfl,
            ← List.getElem?_eq_getElem hzl, hke] at hvx
          omega
        exact ⟨k, by omega, hk2, hke⟩
    · have hze : z.toNat = s.core.min_clr_len := by
        rw [BitVec.ult, decide_eq_false_iff_not, hmcl_bv] at hge; omega
      exact hJs () mz ⟨mrk_z, hml_z, hab_z, fun w hw => by
        by_cases hz : mrk_z[w]?.getD 0#8 = 0#8; · exact hz
        exfalso; obtain ⟨k, hk1, hk2, _⟩ := hcov_z w hw hz; omega, hm_z⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S4

end
