module

public import LeanQbe.T.Examples.Kissat.FullM6WatchGc
public import LeanQbe.T.Examples.Kissat.FullSpec2
public import LeanQbe.T.Examples.Kissat.FullReduceLemmas2
public import LeanQbe.T.Examples.Kissat.FullIngestLemmas1

/-!
# Kissat M6 Watch/GC Proofs Part 1: Radix Sort, Watch Defrag, `lit_rank`, & Binary Dedup

Proves:
1. `full_wstack_radix_sort_m6_wp`: 256-bucket LSB radix sort with `max_off` early exit.
2. `full_wstack_defrag_m6_wp` against exact canonical `Full.fullWstackDefragSpec`.
3. `full_lit_rank_m6_wp` against exact canonical `Full.fullLitRankSpec`.
4. `full_sweep_bins_range_m6_wp` & `full_sweep_bins_m6_wp` against `Full.fullSweepBinsSpec`
   (with `wsort`-stamped binary watch deduplication and optional large-watch prefix keeping).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6WatchGc

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat.Full
open FullReduceHelpers
open FullReduceSpecs (ModeWatchSliceOk BinOnlyWatchSliceOk)
open Kraken.Bedrock2.Test
open scoped FullArenaTactics

/-! ## 0. Strictly scoped tactics & separation helpers -/

namespace M6Tactics1

private theorem strip_le_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
private theorem strip_le_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
private theorem strip_le_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

@[scoped bv_c0 high] private theorem bv64_and255_toNat (x : BitVec 64) :
    (x &&& 255#64).toNat = x.toNat % 256 := by
  rw [BitVec.toNat_and, show (255#64).toNat = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

scoped macro "m6_strip" : tactic =>
  `(tactic| first | apply strip_le_32_64 | apply strip_le_8_32 | apply strip_le_8_64)
scoped macro "m6_unmdata" : tactic =>
  `(tactic| first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)
scoped macro "m6_steps" : tactic =>
  `(tactic| (
    (try m6_unmdata)
    (repeat m6_strip)
    c0_steps
    repeat (any_goals (m6_strip; repeat m6_strip); c0_steps)))

open Lean Elab Tactic in
scoped elab "m6_to_group" : tactic => do
  let mut stk : List MVarId := ← getUnsolvedGoals
  let mut out : Array MVarId := #[]
  for _ in [:5000] do
    match stk with
    | [] => break
    | g :: rest =>
      stk := rest
      if ← g.isAssigned then continue
      setGoals [g]
      let _ ← evalTactic (← `(tactic| try m6_unmdata))
      let g ← getMainGoal
      let ty ← Lean.instantiateMVars (← g.getType)
      let ty := ty.consumeMData.headBeta
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Blocks.get then
        let _ ← evalTactic (← `(tactic| try dsimp only [Blocks.get_here, Blocks.get_there]))
        let _ ← evalTactic (← `(tactic| try m6_unmdata))
      let g ← getMainGoal
      let ty ← Lean.instantiateMVars (← g.getType)
      let ty := ty.consumeMData.headBeta
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.group then
        out := out.push g
      else if ← (try LeanQbe.T.C0Step.stepOnce catch _ => pure false) then
        stk := (← getUnsolvedGoals) ++ stk
      else out := out.push g
  setGoals (out.toList ++ stk)

open Lean Elab Tactic in
scoped elab "m6_c0_steps" : tactic => do
  let mut stk : List MVarId := ← getUnsolvedGoals
  let mut out : Array MVarId := #[]
  for _ in [:5000] do
    match stk with
    | [] => break
    | g :: rest =>
      stk := rest
      if ← g.isAssigned then continue
      setGoals [g]
      let _ ← evalTactic (← `(tactic| try m6_unmdata))
      let g ← getMainGoal
      let ty ← Lean.instantiateMVars (← g.getType)
      let ty := ty.consumeMData.headBeta
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Blocks.get then
        let _ ← evalTactic (← `(tactic| try dsimp only [Blocks.get_here, Blocks.get_there]))
        let _ ← evalTactic (← `(tactic| try m6_unmdata))
      let _ ← evalTactic (← `(tactic| repeat m6_strip))
      if ← (try LeanQbe.T.C0Step.stepOnce catch _ => pure false) then
        stk := (← getUnsolvedGoals) ++ stk
      else out := out.push g
  setGoals (out.toList ++ stk)

open Lean Elab Tactic in
scoped elab "m6_split" : tactic => do
  for _ in [:100] do
    let _ ← evalTactic (← `(tactic| try m6_unmdata))
    let ty ← Lean.instantiateMVars (← (← getMainGoal).getType)
    let ty := ty.consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Blocks.get then
      let _ ← evalTactic (← `(tactic| try dsimp only [Blocks.get_here, Blocks.get_there]))
      let _ ← evalTactic (← `(tactic| try m6_unmdata))
    let ty ← Lean.instantiateMVars (← (← getMainGoal).getType)
    let ty := ty.consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
      let _ ← LeanQbe.T.C0Step.stepOnce; break
    if !(← LeanQbe.T.C0Step.stepOnce) then break

open Lean Elab Tactic in
scoped elab "m6_split_fast" : tactic => do
  for _ in [:100] do
    let _ ← evalTactic (← `(tactic| try m6_unmdata))
    let ty := (← Lean.instantiateMVars (← (← getMainGoal).getType)).consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Blocks.get then
      let _ ← evalTactic (← `(tactic| try dsimp only [Blocks.get_here, Blocks.get_there]))
      let _ ← evalTactic (← `(tactic| try m6_unmdata))
    let ty := (← Lean.instantiateMVars (← (← getMainGoal).getType)).consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
      let hc := mkIdent `hc
      evalTactic (← `(tactic|
        refine wp_jnz_of (fun $hc:ident => ?_) (fun $hc:ident => ?_)))
      evalTactic (← `(tactic| all_goals
        ((try simp only [Arg.val_var, Arg.val_imm] at $hc:ident)
         c0_cond $hc; try (exfalso; c0_bound))))
      break
    if !(← LeanQbe.T.C0Step.stepOnce) then break

open Lean Elab Tactic in
scoped elab "m6_to_jnz" : tactic => do
  for _ in [:100] do
    let _ ← evalTactic (← `(tactic| try m6_unmdata))
    let ty := (← Lean.instantiateMVars (← (← getMainGoal).getType)).consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Blocks.get then
      let _ ← evalTactic (← `(tactic| try dsimp only [Blocks.get_here, Blocks.get_there]))
      let _ ← evalTactic (← `(tactic| try m6_unmdata))
    let ty := (← Lean.instantiateMVars (← (← getMainGoal).getType)).consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.jnz then break
    if !(← LeanQbe.T.C0Step.stepOnce) then break

open Lean Elab Tactic in
scoped elab "m6_usteps" : tactic => do
  for _ in [:100] do
    let _ ← evalTactic (← `(tactic| try m6_unmdata))
    let ty := (← Lean.instantiateMVars (← (← getMainGoal).getType)).consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Blocks.get then
      let _ ← evalTactic (← `(tactic| try dsimp only [Blocks.get_here, Blocks.get_there]))
      let _ ← evalTactic (← `(tactic| try m6_unmdata))
    let ty := (← Lean.instantiateMVars (← (← getMainGoal).getType)).consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        (((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.store ∨
         ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.jnz) then break
    if !(← LeanQbe.T.C0Step.stepOnce) then break

open Lean Elab Tactic in
scoped elab "m6_nojoin" : tactic => do
  let mut stk : List MVarId := ← getUnsolvedGoals
  let mut out : Array MVarId := #[]
  for _ in [:5000] do
    match stk with
    | [] => break
    | g :: rest =>
      stk := rest
      if ← g.isAssigned then continue
      setGoals [g]
      let _ ← evalTactic (← `(tactic| try m6_unmdata))
      let ty := (← Lean.instantiateMVars (← (← getMainGoal).getType)).consumeMData.headBeta
      if ty.getAppFn.isFVar then
        out := out.push g
      else
        if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
            ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Blocks.get then
          let _ ← evalTactic (← `(tactic| try dsimp only [Blocks.get_here, Blocks.get_there]))
          let _ ← evalTactic (← `(tactic| try m6_unmdata))
        let _ ← evalTactic (← `(tactic| repeat m6_strip))
        if ← (try LeanQbe.T.C0Step.stepOnce catch _ => pure false) then
          stk := (← getUnsolvedGoals) ++ stk
        else out := out.push g
  setGoals (out.toList ++ stk)

end M6Tactics1

open scoped M6Tactics1

/-! ## 1. Counting-sort & separation-logic helpers (`private`) -/

private def wsVal (ws : List (BitVec 32)) (i : Nat) : Nat := (ws[i]?.getD 0#32).toNat

private def WsCovers (ws : List (BitVec 32)) (n nlits : Nat) (sz : Nat → Nat) : Prop :=
  (∀ i < n, wsVal ws i < nlits ∧ 0 < sz (wsVal ws i)) ∧
  (∀ a < n, ∀ b < n, a ≠ b → wsVal ws a ≠ wsVal ws b) ∧
  (∀ l < nlits, 0 < sz l → ∃ i < n, wsVal ws i = l)

private def SortedRange (key : Nat → Nat) (ws : List (BitVec 32)) (lo hi : Nat) : Prop :=
  ∀ i j, lo ≤ i → i ≤ j → j < hi → key (wsVal ws i) ≤ key (wsVal ws j)

private def SplitLe (key : Nat → Nat) (ws : List (BitVec 32)) (mid hi : Nat) : Prop :=
  ∀ i < mid, ∀ j, mid ≤ j → j < hi → key (wsVal ws i) ≤ key (wsVal ws j)

private def swapIdx (i j k : Nat) : Nat :=
  if k = i then j else if k = j then i else k

private theorem swapIdx_invol (i j k : Nat) : swapIdx i j (swapIdx i j k) = k := by
  unfold swapIdx; grind

private theorem wsVal_swap {ws : List (BitVec 32)} {i j : Nat}
    (hi : i < ws.length) (hj : j < ws.length) (k : Nat) :
    wsVal ((ws.set i (ws[j]'hj)).set j (ws[i]'hi)) k = wsVal ws (swapIdx i j k) := by
  unfold wsVal swapIdx
  by_cases hkj : k = j
  · subst hkj; rw [List.getElem?_set_self (by simp; omega)]
    by_cases hki : k = i <;> simp [hki, List.getElem?_eq_getElem hi]
  · rw [List.getElem?_set_ne (by omega)]
    by_cases hki : k = i
    · subst hki; rw [List.getElem?_set_self (by omega)]; simp [List.getElem?_eq_getElem hj]
    · rw [List.getElem?_set_ne (by omega)]; simp [hki, hkj]

private theorem wsCovers_swap {ws : List (BitVec 32)} {n nlits i j : Nat} {sz : Nat → Nat}
    (hc : WsCovers ws n nlits sz) (hi : i < n) (hj : j < n) (hn : n ≤ ws.length) :
    WsCovers ((ws.set i (ws[j]'(by omega))).set j (ws[i]'(by omega))) n nlits sz := by
  obtain ⟨hb, hnd, hcov⟩ := hc
  have hlt : ∀ k < n, swapIdx i j k < n := fun k hk => by unfold swapIdx; grind
  refine ⟨fun k hk => by rw [wsVal_swap (by omega) (by omega)]; exact hb _ (hlt k hk),
    fun a ha b hb' hab => by
      rw [wsVal_swap (by omega) (by omega), wsVal_swap (by omega) (by omega)]
      refine hnd _ (hlt a ha) _ (hlt b hb') fun heq => hab ?_
      simpa [swapIdx_invol] using congrArg (swapIdx i j) heq,
    fun l hl hsz => by
      obtain ⟨k, hk, hkl⟩ := hcov l hl hsz
      exact ⟨swapIdx i j k, hlt k hk, by
        rw [wsVal_swap (by omega) (by omega), swapIdx_invol]; exact hkl⟩⟩

private theorem list_perm_take_of_drop_eq {α : Type} {l1 l2 : List α} {n : Nat}
    (hlen : l1.length = l2.length) (hn : n ≤ l2.length)
    (hperm : l1.Perm l2) (hsuf : ∀ i, n ≤ i → l1[i]? = l2[i]?) :
    (l1.take n).Perm (l2.take n) := by
  have hdrop : l1.drop n = l2.drop n := by
    apply List.ext_getElem
    · simp [List.length_drop, hlen]
    · intro i hi _; simp only [List.length_drop] at hi
      rw [List.getElem_drop, List.getElem_drop]
      have heq := hsuf (n + i) (by omega)
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at heq
      exact Option.some.inj heq
  have hsplit : (l1.take n ++ l2.drop n).Perm (l2.take n ++ l2.drop n) := by
    rw [← hdrop, List.take_append_drop, hdrop, List.take_append_drop]; exact hperm
  exact (List.perm_append_right_iff (l2.drop n)).mp hsplit

private theorem wsCovers_of_perm_suffix {ws ws' : List (BitVec 32)} {n nlits : Nat}
    {sz : Nat → Nat} (hcov : WsCovers ws n nlits sz)
    (hlen : ws'.length = ws.length) (hn : n ≤ ws.length)
    (hperm : ws'.Perm ws) (hsuf : ∀ i, n ≤ i → ws'[i]? = ws[i]?) :
    WsCovers ws' n nlits sz := by
  have htp := list_perm_take_of_drop_eq hlen hn hperm hsuf
  have hlen_tk' : (ws'.take n).length = n := by rw [List.length_take]; omega
  have hlen_tk : (ws.take n).length = n := by rw [List.length_take]; omega
  have hmem_tk : ∀ (l : List (BitVec 32)), (l.take n).length = n → ∀ x,
      (∃ i < n, l[i]? = some x) ↔ x ∈ l.take n := fun l hlk x => by
    constructor
    · rintro ⟨i, hi, heq⟩; have hilt : i < l.length := by rw [List.length_take] at hlk; omega
      rw [List.getElem?_eq_getElem hilt, Option.some.injEq] at heq; subst heq
      have hgm := List.getElem_mem (l := l.take n) (n := i) (by omega)
      rwa [List.getElem_take] at hgm
    · intro hx; obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      have hilt : i < l.length := by rw [hlk] at hi; rw [List.length_take] at hlk; omega
      refine ⟨i, by omega, ?_⟩; rw [List.getElem?_eq_getElem hilt, List.getElem_take]
  have hmem_iff : ∀ x, (∃ i < n, ws'[i]? = some x) ↔ (∃ i < n, ws[i]? = some x) := fun x =>
    (hmem_tk ws' hlen_tk' x).trans (htp.mem_iff.trans (hmem_tk ws hlen_tk x).symm)
  have hnd : (ws.take n).Nodup := List.pairwise_iff_getElem.mpr fun i j hi hj hij => by
    rw [List.getElem_take, List.getElem_take]
    intro heq; apply hcov.2.1 i (by omega) j (by omega) (by omega)
    unfold wsVal; rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
      Option.getD_some, Option.getD_some, heq]
  have hnd' : (ws'.take n).Nodup := htp.nodup_iff.mpr hnd
  refine ⟨fun i hi => ?_, fun a ha b hb hab => ?_, fun l hl hsz => ?_⟩
  · obtain ⟨j, hj, hjeq⟩ :=
      (hmem_iff (ws'[i]'(by omega))).mp ⟨i, hi, List.getElem?_eq_getElem (by omega)⟩
    have hveq : wsVal ws' i = wsVal ws j := by
      unfold wsVal; rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
        hjeq, Option.getD_some]
    rw [hveq]; exact hcov.1 j hj
  · have hlt : a < b ∨ b < a := Nat.lt_or_gt_of_ne hab
    intro hveq
    have heqv : (ws'.take n)[a]'(by omega) = (ws'.take n)[b]'(by omega) := by
      rw [List.getElem_take, List.getElem_take]; apply BitVec.eq_of_toNat_eq
      unfold wsVal at hveq
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
        Option.getD_some, Option.getD_some] at hveq
      exact hveq
    rcases hlt with h1 | h2
    · exact List.pairwise_iff_getElem.mp hnd' a b (by omega) (by omega) h1 heqv
    · exact List.pairwise_iff_getElem.mp hnd' b a (by omega) (by omega) h2 heqv.symm
  · obtain ⟨j, hj, hjl⟩ := hcov.2.2 l hl hsz
    obtain ⟨i, hi, hieq⟩ :=
      (hmem_iff (ws[j]'(by omega))).mpr ⟨j, hj, List.getElem?_eq_getElem (by omega)⟩
    refine ⟨i, hi, ?_⟩
    unfold wsVal at hjl ⊢; rw [hieq, Option.getD_some]
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hjl; exact hjl

private theorem wsCovers_of_perm_prefix {ws ws' : List (BitVec 32)} {n nlits : Nat}
    {sz : Nat → Nat} (hcov : WsCovers ws n nlits sz)
    (hn : n ≤ ws.length) (hn' : n ≤ ws'.length)
    (hperm : (ws'.take n).Perm (ws.take n)) : WsCovers ws' n nlits sz := by
  have hlen_tk' : (ws'.take n).length = n := by rw [List.length_take]; omega
  have hlen_tk : (ws.take n).length = n := by rw [List.length_take]; omega
  have hmem_tk : ∀ (l : List (BitVec 32)), (l.take n).length = n → ∀ x,
      (∃ i < n, l[i]? = some x) ↔ x ∈ l.take n := fun l hlk x => by
    constructor
    · rintro ⟨i, hi, heq⟩; have hilt : i < l.length := by rw [List.length_take] at hlk; omega
      rw [List.getElem?_eq_getElem hilt, Option.some.injEq] at heq; subst heq
      have hgm := List.getElem_mem (l := l.take n) (n := i) (by omega)
      rwa [List.getElem_take] at hgm
    · intro hx; obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      have hilt : i < l.length := by rw [hlk] at hi; rw [List.length_take] at hlk; omega
      refine ⟨i, by omega, ?_⟩; rw [List.getElem?_eq_getElem hilt, List.getElem_take]
  have hmem_iff : ∀ x, (∃ i < n, ws'[i]? = some x) ↔ (∃ i < n, ws[i]? = some x) := fun x =>
    (hmem_tk ws' hlen_tk' x).trans (hperm.mem_iff.trans (hmem_tk ws hlen_tk x).symm)
  have hnd : (ws.take n).Nodup := List.pairwise_iff_getElem.mpr fun i j hi hj hij => by
    rw [List.getElem_take, List.getElem_take]
    intro heq; apply hcov.2.1 i (by omega) j (by omega) (by omega)
    unfold wsVal; rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
      Option.getD_some, Option.getD_some, heq]
  have hnd' : (ws'.take n).Nodup := hperm.nodup_iff.mpr hnd
  refine ⟨fun i hi => ?_, fun a ha b hb hab => ?_, fun l hl hsz => ?_⟩
  · obtain ⟨j, hj, hjeq⟩ :=
      (hmem_iff (ws'[i]'(by omega))).mp ⟨i, hi, List.getElem?_eq_getElem (by omega)⟩
    have hveq : wsVal ws' i = wsVal ws j := by
      unfold wsVal; rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
        hjeq, Option.getD_some]
    rw [hveq]; exact hcov.1 j hj
  · have hlt : a < b ∨ b < a := Nat.lt_or_gt_of_ne hab
    intro hveq
    have heqv : (ws'.take n)[a]'(by omega) = (ws'.take n)[b]'(by omega) := by
      rw [List.getElem_take, List.getElem_take]; apply BitVec.eq_of_toNat_eq
      unfold wsVal at hveq
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
        Option.getD_some, Option.getD_some] at hveq
      exact hveq
    rcases hlt with h1 | h2
    · exact List.pairwise_iff_getElem.mp hnd' a b (by omega) (by omega) h1 heqv
    · exact List.pairwise_iff_getElem.mp hnd' b a (by omega) (by omega) h2 heqv.symm
  · obtain ⟨j, hj, hjl⟩ := hcov.2.2 l hl hsz
    obtain ⟨i, hi, hieq⟩ :=
      (hmem_iff (ws[j]'(by omega))).mpr ⟨j, hj, List.getElem?_eq_getElem (by omega)⟩
    refine ⟨i, hi, ?_⟩
    unfold wsVal at hjl ⊢; rw [hieq, Option.getD_some]
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hjl; exact hjl

private theorem wsortMaxHeap_root_ge {wvec ws : List (BitVec 32)} {hi : Nat}
    (hmax : FullWsortMaxHeap wvec ws 0 hi) :
    ∀ i < hi,
      (wvec[2 * wsVal ws i]?.getD 0#32).toNat ≤ (wvec[2 * wsVal ws 0]?.getD 0#32).toNat := by
  intro i; induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hilt; rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact Nat.le_refl _
    · have hrec := ih _ (show (i - 1) / 2 < i by omega) (by omega)
      have hstep := hmax ((i - 1) / 2) (by omega) (by omega)
      by_cases hodd : i = 2 * ((i - 1) / 2) + 1
      · have := hstep.1 (by omega); rw [← hodd] at this; exact Nat.le_trans this hrec
      · have := hstep.2 (by omega)
        rw [← show i = 2 * ((i - 1) / 2) + 2 by omega] at this; exact Nat.le_trans this hrec

private theorem wsort_extract_swap_step {wvec ws : List (BitVec 32)} {e n : Nat}
    (hmax : FullWsortMaxHeap wvec ws 0 (e + 1))
    (hsp : SplitLe (fun l => (wvec[2 * l]?.getD 0#32).toNat) ws (e + 1) n)
    (hsrt : SortedRange (fun l => (wvec[2 * l]?.getD 0#32).toNat) ws (e + 1) n)
    (he : 0 < e) (hen : e < n) (hn : n ≤ ws.length) :
    let ws' := (ws.set 0 (ws[e]'(by omega))).set e (ws[0]'(by omega))
    let key := fun l => (wvec[2 * l]?.getD 0#32).toNat
    FullWsortMaxHeap wvec ws' 1 e ∧ SplitLe key ws' e n ∧ SortedRange key ws' e n := by
  intro ws' key; have hsw := wsVal_swap (ws := ws) (i := 0) (j := e) (by omega) (by omega)
  have hroot := wsortMaxHeap_root_ge hmax
  have hfix : ∀ k, 0 < k → k < e → swapIdx 0 e k = k := fun k _ _ => by unfold swapIdx; grind
  refine ⟨fun p hp hpe => ?_, fun i hi j hj1 hj2 => ?_, fun i j hi1 hij hj2 => ?_⟩
  · have hstep := hmax p (by omega) (by omega)
    constructor
    · intro h1; have hsw1 := hsw (2 * p + 1); have hswp := hsw p; unfold wsVal at hsw1 hswp
      dsimp only [ws']; rw [hsw1, hswp, hfix _ hp hpe, hfix _ (by omega) h1]
      exact hstep.1 (by omega)
    · intro h2; have hsw2 := hsw (2 * p + 2); have hswp := hsw p; unfold wsVal at hsw2 hswp
      dsimp only [ws']; rw [hsw2, hswp, hfix _ hp hpe, hfix _ (by omega) h2]
      exact hstep.2 (by omega)
  · dsimp only [key] at *; rw [hsw i, hsw j]
    have hisw : swapIdx 0 e i < e + 1 := by unfold swapIdx; grind
    by_cases hje : j = e
    · subst hje; rw [show swapIdx 0 j j = 0 by unfold swapIdx; grind]; exact hroot _ hisw
    · rw [show swapIdx 0 e j = j by unfold swapIdx; grind]; exact hsp _ hisw _ (by omega) hj2
  · dsimp only [key] at *; rw [hsw i, hsw j]
    by_cases hie : i = e
    · subst hie; rw [show swapIdx 0 i i = 0 by unfold swapIdx; grind]
      by_cases hje : j = i
      · subst hje; rw [show swapIdx 0 j j = 0 by unfold swapIdx; grind]; exact Nat.le_refl _
      · rw [show swapIdx 0 i j = j by unfold swapIdx; grind]
        exact hsp 0 (by omega) j (by omega) hj2
    · rw [show swapIdx 0 e i = i by unfold swapIdx; grind,
        show swapIdx 0 e j = j by unfold swapIdx; grind]
      exact hsrt i j (by omega) hij hj2

private theorem wsort_extract_perm_post {wvec ws ws' : List (BitVec 32)} {e n : Nat}
    (hlen : ws'.length = ws.length) (hen : e ≤ n) (hn : n ≤ ws.length)
    (hperm : ws'.Perm ws) (hsuf : ∀ i, e ≤ i → ws'[i]? = ws[i]?)
    (hsp : SplitLe (fun l => (wvec[2 * l]?.getD 0#32).toNat) ws e n)
    (hsrt : SortedRange (fun l => (wvec[2 * l]?.getD 0#32).toNat) ws e n) :
    let key := fun l => (wvec[2 * l]?.getD 0#32).toNat
    SplitLe key ws' e n ∧ SortedRange key ws' e n := by
  intro key; have htp := list_perm_take_of_drop_eq hlen (by omega) hperm hsuf
  have htk' : (ws'.take e).length = e := by rw [List.length_take]; omega
  have htk : (ws.take e).length = e := by rw [List.length_take]; omega
  refine ⟨fun i hi j hj1 hj2 => ?_, fun i j hi1 hij hj2 => ?_⟩
  · have hmem : ws'[i]'(by omega) ∈ ws'.take e := by
      have hgm := List.getElem_mem (l := ws'.take e) (n := i) (by rw [htk']; exact hi)
      rwa [List.getElem_take] at hgm
    obtain ⟨i0, hi0, hget0⟩ := List.mem_iff_getElem.mp (htp.mem_iff.mp hmem)
    rw [htk] at hi0; rw [List.getElem_take] at hget0
    have hvi : wsVal ws' i = wsVal ws i0 := by
      unfold wsVal; rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
        Option.getD_some, Option.getD_some, hget0]
    have hvj : wsVal ws' j = wsVal ws j := by unfold wsVal; rw [hsuf j hj1]
    dsimp only [key] at *; rw [hvi, hvj]; exact hsp i0 hi0 j hj1 hj2
  · have hvi : wsVal ws' i = wsVal ws i := by unfold wsVal; rw [hsuf i hi1]
    have hvj : wsVal ws' j = wsVal ws j := by unfold wsVal; rw [hsuf j (by omega)]
    dsimp only [key] at *; rw [hvi, hvj]; exact hsrt i j hi1 hij hj2

private theorem defrag_sorted_gap {s : FullState} {ws : List (BitVec 32)} {n : Nat}
    (hlay : WatchStackLayout s.core)
    (hcov : WsCovers ws n (2 * s.core.cur_vars) (fullWatchSize s))
    (hsrt : SortedRange (fullWatchOff s) ws 0 n) {i j : Nat} (hij : i < j) (hjn : j < n) :
    fullWatchOff s (wsVal ws i) + fullWatchSize s (wsVal ws i) ≤ fullWatchOff s (wsVal ws j) := by
  have hi := hcov.1 i (by omega); have hj := hcov.1 j hjn
  have hle := hsrt i j (by omega) (by omega) hjn
  rcases hlay.disjoint _ _ hi.1 hj.1 (hcov.2.1 i (by omega) j hjn (by omega)) hi.2 hj.2 with h | h
  · exact h
  · exfalso; unfold fullWatchOff fullWatchSize at *; omega

private theorem wvec_set_even_eq {wvec : List (BitVec 32)} {l : Nat} {v : BitVec 32}
    (hl : 2 * l < wvec.length) (j : Nat) :
    (wvec.set (2 * l) v)[2 * j + 1]? = wvec[2 * j + 1]? ∧
    (j ≠ l → (wvec.set (2 * l) v)[2 * j]? = wvec[2 * j]?) ∧
    (wvec.set (2 * l) v)[2 * l]? = some v :=
  ⟨List.getElem?_set_ne (by omega), fun _ => List.getElem?_set_ne (by omega),
   List.getElem?_set_self hl⟩

private theorem defrag_finalize {s : FullState}
    {wvecC wstkC wsort2 : List (BitVec 32)} {n p : Nat} (hlay : WatchStackLayout s.core)
    (hcov : WsCovers wsort2 n (2 * s.core.cur_vars) (fullWatchSize s)) (_hp1 : 1 ≤ p)
    (hsz : ∀ l < 2 * s.core.cur_vars, (wvecC[2 * l + 1]?.getD 0#32).toNat = fullWatchSize s l)
    (hzero : ∀ l < 2 * s.core.cur_vars,
      fullWatchSize s l = 0 → (wvecC[2 * l]?.getD 0#32).toNat = 0)
    (hdone : ∀ j < n, let l := wsVal wsort2 j; let off := (wvecC[2 * l]?.getD 0#32).toNat;
      1 ≤ off ∧ off + fullWatchSize s l ≤ p ∧
      ∀ k < fullWatchSize s l, wstkC[off + k]? = s.core.wstk[fullWatchOff s l + k]?)
    (hdisj : ∀ a < n, ∀ b < n, a ≠ b →
      let la := wsVal wsort2 a; let lb := wsVal wsort2 b;
      (wvecC[2 * la]?.getD 0#32).toNat + fullWatchSize s la ≤
        (wvecC[2 * lb]?.getD 0#32).toNat ∨
      (wvecC[2 * lb]?.getD 0#32).toNat + fullWatchSize s lb ≤
        (wvecC[2 * la]?.getD 0#32).toNat) :
    let s' : FullState :=
      { s with core := { s.core with wvec := wvecC, wstk := wstkC, wlen := p, wusable := 0#64 }
               scratch := { s.scratch with wsort := wsort2 } }
    WatchStackLayout s'.core ∧
      ∀ l < 2 * s.core.cur_vars, fullWatchSize s' l = fullWatchSize s l ∧
        ∀ k < fullWatchSize s l,
          s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]? := by
  intro s'; have hsz' : ∀ l < 2 * s.core.cur_vars, fullWatchSize s' l = fullWatchSize s l := hsz
  refine ⟨⟨fun l hl => ?_, fun l hl hp => ?_, fun l1 l2 h1 h2 hne hp1 hp2 => ?_,
    fun l hl k hk => ?_⟩, fun l hl => ⟨hsz' l hl, fun k hk => ?_⟩⟩
  · change fullWatchOffCore s'.core l + fullWatchSizeCore s'.core l ≤ p
    rw [show fullWatchSizeCore s'.core l = fullWatchSize s' l from rfl, hsz' l hl]
    rcases Nat.eq_zero_or_pos (fullWatchSize s l) with hz | hp
    · change (wvecC[2 * l]?.getD 0#32).toNat + _ ≤ p; rw [hz, hzero l hl hz]; omega
    · obtain ⟨j, hj, rfl⟩ := hcov.2.2 l hl hp; exact (hdone j hj).2.1
  · rw [show fullWatchSizeCore s'.core l = fullWatchSize s' l from rfl, hsz' l hl] at hp
    obtain ⟨j, hj, rfl⟩ := hcov.2.2 l hl hp; exact (hdone j hj).1
  · rw [show fullWatchSizeCore s'.core l1 = fullWatchSize s' l1 from rfl, hsz' l1 h1] at hp1 ⊢
    rw [show fullWatchSizeCore s'.core l2 = fullWatchSize s' l2 from rfl, hsz' l2 h2] at hp2 ⊢
    obtain ⟨a, ha, rfl⟩ := hcov.2.2 l1 h1 hp1; obtain ⟨b, hb, rfl⟩ := hcov.2.2 l2 h2 hp2
    exact hdisj a ha b hb fun hab => hne (by rw [hab])
  · rw [show fullWatchSizeCore s'.core l = fullWatchSize s' l from rfl, hsz' l hl] at hk
    obtain ⟨j, hj, rfl⟩ := hcov.2.2 l hl (by omega)
    change wstkC[(wvecC[2 * wsVal wsort2 j]?.getD 0#32).toNat + k]? ≠ _
    rw [(hdone j hj).2.2 k hk]; exact hlay.no_sentinel _ hl k hk
  · obtain ⟨j, hj, rfl⟩ := hcov.2.2 l hl (by omega); exact (hdone j hj).2.2 k hk

private def fullWvecOff (wvec : List (BitVec 32)) (l : Nat) : Nat :=
  (wvec[2 * l]?.getD 0#32).toNat

private theorem bv_getElem_toNat_eq {xs : List (BitVec 32)} {i j : Nat}
    (hi : i < xs.length) (hij : j = i) : (xs[j]'(hij ▸ hi)).toNat = (xs[i]'hi).toNat := by
  subst hij; rfl

private theorem full_lt_getElem?_eq {xs : List (BitVec 32)} {i : Nat} (hi : i < xs.length) :
    (xs[i]'hi) = xs[i]?.getD 0#32 := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some]

private theorem bv32_mask_lt256 (x : BitVec 64) : (x &&& 255#64).toNat = x.toNat % 256 := by
  rw [BitVec.toNat_and, show (255#64).toNat = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

private theorem div_pow2_mod_256_shift (off sh : Nat) :
    (off / 2 ^ sh) % 256 * 2 ^ sh + off % 2 ^ sh = off % 2 ^ (sh + 8) := by
  have h0 : off = 2 ^ sh * (off / 2 ^ sh) + off % 2 ^ sh := (Nat.div_add_mod off (2 ^ sh)).symm
  have h1 : off / 2 ^ sh = 256 * ((off / 2 ^ sh) / 256) + (off / 2 ^ sh) % 256 :=
    (Nat.div_add_mod (off / 2 ^ sh) 256).symm
  have hpow : 2 ^ (sh + 8) = 2 ^ sh * 256 := by rw [Nat.pow_add]
  have hlt1 : (off / 2 ^ sh) % 256 < 256 := Nat.mod_lt _ (by decide)
  have hlt2 : off % 2 ^ sh < 2 ^ sh := Nat.mod_lt _ (Nat.two_pow_pos sh)
  have hcomb : off = (2 ^ sh * 256) * ((off / 2 ^ sh) / 256) +
      ((off / 2 ^ sh) % 256 * 2 ^ sh + off % 2 ^ sh) := by
    calc
      off = 2 ^ sh * (256 * ((off / 2 ^ sh) / 256) + (off / 2 ^ sh) % 256) + off % 2 ^ sh := by
        rw [← h1]; exact h0
      _ = (2 ^ sh * 256) * ((off / 2 ^ sh) / 256) +
            ((off / 2 ^ sh) % 256 * 2 ^ sh + off % 2 ^ sh) := by
        rw [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm (2 ^ sh) ((off / 2 ^ sh) % 256), Nat.add_assoc]
  have hlt_all : (off / 2 ^ sh) % 256 * 2 ^ sh + off % 2 ^ sh < 2 ^ sh * 256 := by
    have hmul : (off / 2 ^ sh) % 256 * 2 ^ sh + 2 ^ sh ≤ 256 * 2 ^ sh := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hlt1
    rw [Nat.mul_comm 256 (2 ^ sh)] at hmul; omega
  rw [hpow]; conv => rhs; rw [hcomb]
  simp [Nat.mod_eq_of_lt hlt_all]

private def FullCoreU32BNoWvec (c : FullCfg) (k : FullCoreState) : Mem 64 → Prop :=
  array (t := i32) c.pFrameTrail k.frame_trail ⋆ array (t := i32) c.pFrameDec k.frame_dec ⋆
  array (t := i32) c.pRepr k.repr ⋆ array (t := i32) c.pMinStk k.min_stk

private def FullScrWksNoWsort (c : FullCfg) (sc : FullScratch) : Mem 64 → Prop :=
  array (t := i32) c.pWorkStk1 sc.work_stk1 ⋆ array (t := i32) c.pWorkStk2 sc.work_stk2 ⋆
  array (t := i32) c.pTarjanMark sc.tarjan_mark ⋆
  array (t := i32) c.pTarjanReach sc.tarjan_reach

private def FullWvecWsortRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  Kissat.dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur
      s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
  (Full.FullCoreByteArrs c s.core ⋆ Full.FullCoreU32A c s.core ⋆ FullCoreU32BNoWvec c s.core ⋆
    Full.FullCoreDynArrs c s.core) ⋆
  (Full.FullScrByteArrs c s.scratch ⋆ Full.FullScrU32A c s.scratch ⋆
    FullScrWksNoWsort c s.scratch ⋆
    Full.FullScrMetaArrs c s.scratch ⋆ Full.FullScrDynArrs c s.scratch) ⋆ c.pad

private theorem fullMem_eq_wvec_wsort (c : FullCfg) (s : FullState) :
    FullMem c s = (array (t := i32) c.pWvec s.core.wvec ⋆
      array (t := i32) c.pWsort s.scratch.wsort ⋆ FullWvecWsortRest c s) := by
  unfold FullMem Full.FullCoreArrays Full.FullScratchArrays Full.FullCoreU32B Full.FullScrWksArrs
    FullWvecWsortRest FullCoreU32BNoWvec FullScrWksNoWsort
  ac_rfl

private theorem focus_wvec_wsort {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pWsort s.scratch.wsort ⋆
      (FullWvecWsortRest c s ⋆ R)) m := by
  rw [fullMem_eq_wvec_wsort, sep_assoc] at hm; exact hm

private theorem unfocus_wvec_wsort {c : FullCfg} {s : FullState} {ws' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m' : Mem 64}
    (hm' : (array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pWsort ws' ⋆
      (FullWvecWsortRest c s ⋆ R)) m') :
    (FullMem c { s with scratch := { s.scratch with wsort := ws' } } ⋆ R) m' := by
  rw [fullMem_eq_wvec_wsort, sep_assoc]; exact hm'

private theorem array32_split_3 {a : BitVec 64} {xs : List (BitVec 32)} {k1 k2 : Nat}
    (h1 : k1 ≤ k2) (h2 : k2 ≤ xs.length) :
    array (t := i32) a xs =
      (array (t := i32) a (xs.take k1) ⋆
       array (t := i32) (a + BitVec.ofNat 64 (4 * k1)) ((xs.drop k1).take (k2 - k1)) ⋆
       array (t := i32) (a + BitVec.ofNat 64 (4 * k2)) (xs.drop k2)) := by
  have hlen1 : (xs.take k1).length = k1 := by rw [List.length_take]; omega
  have hlen2 : ((xs.drop k1).take (k2 - k1)).length = k2 - k1 := by
    rw [List.length_take, List.length_drop]; omega
  have hcm : (xs.drop k1).take (k2 - k1) ++ xs.drop k2 = xs.drop k1 := by
    have hd : (xs.drop k1).drop (k2 - k1) = xs.drop k2 := by
      rw [List.drop_drop]; congr 1; omega
    have ht := List.take_append_drop (k2 - k1) (xs.drop k1)
    rwa [hd] at ht
  have hcomb : xs.take k1 ++ (xs.drop k1).take (k2 - k1) ++ xs.drop k2 = xs := by
    rw [List.append_assoc, hcm, List.take_append_drop]
  conv => lhs; rw [← hcomb]
  rw [array_append, array_append]
  simp only [Ty.bytes, Ty.size, i32, List.length_append, hlen1, hlen2,
    show (32 + 7) / 8 = 4 from rfl, show k1 + (k2 - k1) = k2 by omega, sep_assoc]

private theorem array32_split_4 {a : BitVec 64} {xs : List (BitVec 32)} {k1 k2 k3 : Nat}
    (h1 : k1 ≤ k2) (h2 : k2 ≤ k3) (h3 : k3 ≤ xs.length) :
    array (t := i32) a xs =
      (array (t := i32) a (xs.take k1) ⋆
       array (t := i32) (a + BitVec.ofNat 64 (4 * k1)) ((xs.drop k1).take (k2 - k1)) ⋆
       array (t := i32) (a + BitVec.ofNat 64 (4 * k2)) ((xs.drop k2).take (k3 - k2)) ⋆
       array (t := i32) (a + BitVec.ofNat 64 (4 * k3)) (xs.drop k3)) := by
  rw [array32_split_3 (k1 := k1) (k2 := k2) h1 (by omega)]
  have hdrop : array (t := i32) (a + BitVec.ofNat 64 (4 * k2)) (xs.drop k2) =
      (array (t := i32) (a + BitVec.ofNat 64 (4 * k2)) ((xs.drop k2).take (k3 - k2)) ⋆
       array (t := i32) (a + BitVec.ofNat 64 (4 * k3)) (xs.drop k3)) := by
    have hcm : (xs.drop k2).take (k3 - k2) ++ xs.drop k3 = xs.drop k2 := by
      have hd : (xs.drop k2).drop (k3 - k2) = xs.drop k3 := by
        rw [List.drop_drop]; congr 1; omega
      have ht := List.take_append_drop (k3 - k2) (xs.drop k2)
      rwa [hd] at ht
    conv => lhs; rw [← hcm]
    rw [array_append]
    simp only [Ty.bytes, Ty.size, i32, List.length_take, List.length_drop,
      show (32 + 7) / 8 = 4 from rfl]
    have hln : min (k3 - k2) (xs.length - k2) = k3 - k2 := by omega
    rw [hln, BitVec.add_assoc, show BitVec.ofNat 64 (4 * k2) + BitVec.ofNat 64 (4 * (k3 - k2)) =
      BitVec.ofNat 64 (4 * k3) from by rw [← BitVec.ofNat_add]; congr 1; omega]
  rw [hdrop]; ac_rfl

/-! ## 2. Counting-sort pure list/index invariants & `full_wstack_radix_sort_m6_wp` -/

private def countLt (bkts : Nat → Nat) (n b : Nat) : Nat :=
  (List.range n).countP (fun j => decide (bkts j < b))

private def countEqUpTo (bkts : Nat → Nat) (k b : Nat) : Nat :=
  (List.range k).countP (fun j => decide (bkts j = b))

private theorem countLt_zero (bkts : Nat → Nat) (n : Nat) : countLt bkts n 0 = 0 := by
  unfold countLt; simp [List.countP_eq_length_filter]

private theorem countLt_top {bkts : Nat → Nat} {n : Nat} (hb : ∀ j < n, bkts j < 256) :
    countLt bkts n 256 = n := by
  unfold countLt
  rw [List.countP_eq_length_filter, List.filter_eq_self.mpr ?_, List.length_range]
  intro j hj; simp only [List.mem_range] at hj; simp [hb j hj]

private theorem countLt_succ (bkts : Nat → Nat) (n b : Nat) :
    countLt bkts n (b + 1) = countLt bkts n b + countEqUpTo bkts n b := by
  unfold countLt countEqUpTo
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.countP_append, List.countP_append, List.countP_append, ih]
    simp only [List.countP_cons, List.countP_nil]
    by_cases h1 : bkts k < b <;> by_cases h2 : bkts k = b <;>
      by_cases h3 : bkts k < b + 1 <;> simp [h1, h2, h3] <;> omega

private theorem countLt_mono {bkts : Nat → Nat} {n a b : Nat} (hle : a ≤ b) :
    countLt bkts n a ≤ countLt bkts n b := by
  have hinc : ∀ d, countLt bkts n a ≤ countLt bkts n (a + d) := fun d => by
    induction d with
    | zero => simp
    | succ d ih => rw [← Nat.add_assoc, countLt_succ]; omega
  simpa [show a + (b - a) = b by omega] using hinc (b - a)

private theorem countEqUpTo_zero (bkts : Nat → Nat) (b : Nat) : countEqUpTo bkts 0 b = 0 := by
  unfold countEqUpTo; simp

private theorem countEqUpTo_succ (bkts : Nat → Nat) (k b : Nat) :
    countEqUpTo bkts (k + 1) b = countEqUpTo bkts k b + if bkts k = b then 1 else 0 := by
  unfold countEqUpTo; rw [List.range_succ, List.countP_append]
  simp [List.countP_cons, decide_eq_true_eq]

private theorem countEqUpTo_mono {bkts : Nat → Nat} {k1 k2 b : Nat} (hlt : k1 < k2)
    (heq : bkts k1 = b) : countEqUpTo bkts k1 b < countEqUpTo bkts k2 b := by
  have hstep : ∀ d, countEqUpTo bkts k1 b < countEqUpTo bkts (k1 + 1 + d) b := by
    intro d; induction d with
    | zero => simp [countEqUpTo_succ, heq]
    | succ d ih => rw [← Nat.add_assoc, countEqUpTo_succ]; omega
  simpa [show k1 + 1 + (k2 - (k1 + 1)) = k2 by omega] using hstep (k2 - (k1 + 1))

private theorem countEqUpTo_le_of_le {bkts : Nat → Nat} {k1 k2 b : Nat} (hle : k1 ≤ k2) :
    countEqUpTo bkts k1 b ≤ countEqUpTo bkts k2 b := by
  have hstep : ∀ d, countEqUpTo bkts k1 b ≤ countEqUpTo bkts (k1 + d) b := by
    intro d; induction d with
    | zero => simp
    | succ d ih => rw [← Nat.add_assoc, countEqUpTo_succ]; omega
  simpa [show k1 + (k2 - k1) = k2 by omega] using hstep (k2 - k1)

private def bktPlace (bkts : Nat → Nat) (n k : Nat) : Nat :=
  countLt bkts n (bkts k) + countEqUpTo bkts k (bkts k)

private theorem bktPlace_lt {bkts : Nat → Nat} {n k : Nat} (hk : k < n)
    (hb : ∀ j < n, bkts j < 256) : bktPlace bkts n k < n := by
  unfold bktPlace
  have h1 : countEqUpTo bkts k (bkts k) < countEqUpTo bkts n (bkts k) :=
    countEqUpTo_mono hk rfl
  have hlt256 := hb k hk
  have h2 : countLt bkts n (bkts k + 1) ≤ countLt bkts n 256 := countLt_mono (by omega)
  rw [countLt_succ, countLt_top hb] at h2
  omega

private theorem bktPlace_lt_of_order {bkts : Nat → Nat} {n k1 k2 : Nat}
    (hk1 : k1 < n) (_hk2 : k2 < n)
    (hord : bkts k1 < bkts k2 ∨ (bkts k1 = bkts k2 ∧ k1 < k2)) :
    bktPlace bkts n k1 < bktPlace bkts n k2 := by
  rcases hord with hlt | ⟨heq, hk⟩
  · have h1 : countEqUpTo bkts k1 (bkts k1) < countEqUpTo bkts n (bkts k1) :=
      countEqUpTo_mono hk1 rfl
    have h2 : countLt bkts n (bkts k1 + 1) ≤ countLt bkts n (bkts k2) := countLt_mono (by omega)
    rw [countLt_succ] at h2
    unfold bktPlace; omega
  · unfold bktPlace; rw [heq]; have := countEqUpTo_mono hk heq; omega

private theorem bktPlace_inj {bkts : Nat → Nat} {n k1 k2 : Nat}
    (hk1 : k1 < n) (hk2 : k2 < n) (hne : k1 ≠ k2) :
    bktPlace bkts n k1 ≠ bktPlace bkts n k2 := by
  rcases Nat.lt_or_gt_of_ne hne with h12 | h21
  · rcases Nat.lt_trichotomy (bkts k1) (bkts k2) with hb1 | hb2 | hb3
    · exact Nat.ne_of_lt (bktPlace_lt_of_order hk1 hk2 (Or.inl hb1))
    · exact Nat.ne_of_lt (bktPlace_lt_of_order hk1 hk2 (Or.inr ⟨hb2, h12⟩))
    · exact Nat.ne_of_gt (bktPlace_lt_of_order hk2 hk1 (Or.inl hb3))
  · rcases Nat.lt_trichotomy (bkts k2) (bkts k1) with hb1 | hb2 | hb3
    · exact Nat.ne_of_gt (bktPlace_lt_of_order hk2 hk1 (Or.inl hb1))
    · exact Nat.ne_of_gt (bktPlace_lt_of_order hk2 hk1 (Or.inr ⟨hb2, h21⟩))
    · exact Nat.ne_of_lt (bktPlace_lt_of_order hk1 hk2 (Or.inl hb3))

private theorem bktPlace_order_back {bkts : Nat → Nat} {n k1 k2 : Nat}
    (hk1 : k1 < n) (hk2 : k2 < n) (hp : bktPlace bkts n k1 < bktPlace bkts n k2) :
    bkts k1 < bkts k2 ∨ (bkts k1 = bkts k2 ∧ k1 < k2) := by
  by_cases hb : bkts k1 < bkts k2
  · exact Or.inl hb
  · by_cases heq : bkts k1 = bkts k2
    · refine Or.inr ⟨heq, ?_⟩
      by_cases hlt : k1 < k2
      · exact hlt
      · exfalso
        rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt hlt) with rfl | hk21
        · omega
        · exact absurd (bktPlace_lt_of_order hk2 hk1 (Or.inr ⟨heq.symm, hk21⟩)) (by omega)
    · have h21 : bkts k2 < bkts k1 := by omega
      exact absurd (bktPlace_lt_of_order hk2 hk1 (Or.inl h21)) (by omega)

private theorem nodup_map_inj {α β : Type} {f : α → β} :
    ∀ {l : List α}, l.Nodup → (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: xs, hnd, hinj => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, nodup_map_inj hnd.2 fun x hx y hy =>
      hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)⟩
    rw [List.mem_map] at hmem
    obtain ⟨b, hb, hfb⟩ := hmem
    have heq := hinj a (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb) hfb.symm
    subst heq; exact hnd.1 hb

private theorem nodup_perm_of_subset_eq_len {α : Type} [DecidableEq α] :
    ∀ {l1 l2 : List α}, l1.Nodup → l2.Nodup → (∀ x ∈ l1, x ∈ l2) →
      l1.length = l2.length → l1.Perm l2
  | [], [], _, _, _, _ => List.Perm.nil
  | [], _ :: _, _, _, _, hlen => by simp at hlen
  | a :: xs, ys, hnd1, hnd2, hsub, hlen => by
    rw [List.nodup_cons] at hnd1
    have ha_mem : a ∈ ys := hsub a (List.mem_cons_self ..)
    have hsub' : ∀ x ∈ xs, x ∈ ys.erase a := fun x hx => by
      have hne : x ≠ a := fun h => hnd1.1 (h ▸ hx)
      exact List.mem_erase_of_ne hne |>.mpr (hsub x (List.mem_cons_of_mem _ hx))
    have hnd_er : (ys.erase a).Nodup := hnd2.erase a
    have hlen_er : xs.length = (ys.erase a).length := by
      rw [List.length_erase_of_mem ha_mem]; simp at hlen; omega
    have hperm_tail := nodup_perm_of_subset_eq_len hnd1.2 hnd_er hsub' hlen_er
    exact (hperm_tail.cons a).trans (List.perm_cons_erase ha_mem).symm

private theorem bktPlace_perm_range {bkts : Nat → Nat} {n : Nat}
    (hb : ∀ j < n, bkts j < 256) :
    ((List.range n).map (bktPlace bkts n)).Perm (List.range n) := by
  have hnd : ((List.range n).map (bktPlace bkts n)).Nodup := by
    refine nodup_map_inj List.nodup_range fun x hx y hy hxy => ?_
    simp only [List.mem_range] at hx hy
    by_cases hxy_eq : x = y
    · exact hxy_eq
    · exact absurd hxy (bktPlace_inj hx hy hxy_eq)
  have hsub : ∀ p ∈ (List.range n).map (bktPlace bkts n), p ∈ List.range n := by
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    simp only [List.mem_range] at hk ⊢
    exact bktPlace_lt hk hb
  exact nodup_perm_of_subset_eq_len hnd List.nodup_range hsub (by simp)

private theorem bktPlace_surj {bkts : Nat → Nat} {n p : Nat} (hb : ∀ j < n, bkts j < 256)
    (hp : p < n) : ∃ k < n, bktPlace bkts n k = p := by
  have hmem : p ∈ (List.range n).map (bktPlace bkts n) :=
    (bktPlace_perm_range hb).mem_iff.mpr (List.mem_range.mpr hp)
  rw [List.mem_map] at hmem
  obtain ⟨k, hk, hkp⟩ := hmem
  exact ⟨k, List.mem_range.mp hk, hkp⟩

private theorem perm_of_bktPlace {ws tmp : List (BitVec 32)} {bkts : Nat → Nat} {n : Nat}
    (hb : ∀ j < n, bkts j < 256) (hn_ws : n ≤ ws.length) (hn_tmp : n ≤ tmp.length)
    (hmap : ∀ k < n, tmp[bktPlace bkts n k]? = ws[k]?) :
    (tmp.take n).Perm (ws.take n) := by
  have hp_r := (bktPlace_perm_range hb).symm
  have hp_map := hp_r.map (fun p => tmp[p]?.getD 0#32)
  have h1 : ((List.range n).map (fun p => tmp[p]?.getD 0#32)) = tmp.take n := by
    apply List.ext_getElem (by simp; omega)
    intro i hi _; simp only [List.length_map, List.length_range] at hi
    rw [List.getElem_map, List.getElem_range, List.getElem_take,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  have h2 : (((List.range n).map (bktPlace bkts n)).map (fun p => tmp[p]?.getD 0#32)) =
      ws.take n := by
    rw [List.map_map]
    apply List.ext_getElem (by simp; omega)
    intro i hi _; simp only [List.length_map, List.length_range] at hi
    rw [List.getElem_map, List.getElem_range, Function.comp_apply, List.getElem_take,
      hmap i hi, List.getElem?_eq_getElem (by omega), Option.getD_some]
  rwa [h1, h2] at hp_map

private theorem bv_mul4_eq (i : BitVec 64) : i * 4#64 = BitVec.ofNat 64 (4 * i.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mul_comm]

private theorem bv_shl1_eq (i : BitVec 64) :
    i <<< 1#64 = BitVec.ofNat 64 (2 * i.toNat) := by
  apply BitVec.eq_of_toNat_eq
  change (i <<< (1 : Nat)).toNat = (BitVec.ofNat 64 (2 * i.toNat)).toNat
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  simp [Nat.shiftLeft_eq, Nat.mul_comm]

private theorem arr32_load_mul4 {a : BitVec 64} {xs : List (BitVec 32)} {F : Mem 64 → Prop}
    {i : BitVec 64} {m : Mem 64} (hi : i.toNat < xs.length)
    (h : (array (t := i32) a xs ⋆ F) m) :
    loadVal m i32 (a + i * 4#64) = some (xs[i.toNat]'hi) := by
  rw [bv_mul4_eq]; simpa [Ty.bytes, Ty.size, i32] using loadVal_array (t := i32) (by decide) hi h

private theorem arr32_store_mul4 {a : BitVec 64} {xs : List (BitVec 32)} {F : Mem 64 → Prop}
    {i : BitVec 64} {v : BitVec 32} {m : Mem 64} (hi : i.toNat < xs.length)
    (h : (array (t := i32) a xs ⋆ F) m) :
    storeOk m i32 (a + i * 4#64) ∧
      (array (t := i32) a (xs.set i.toNat v) ⋆ F) (storeMem m i32 (a + i * 4#64) v) := by
  rw [bv_mul4_eq]; simpa [Ty.bytes, Ty.size, i32] using store_array (t := i32) v (by decide) hi h

def fullWstackRadixSortSpec : Spec [i64, i64, i64, i64, i64, i64] [] :=
  fun (wvec_ptr, ws_ptr, tmp_ptr, cnt_ptr, n, max_off, ()) m Q _ =>
    ∃ (wvec ws tmp cnt : List (BitVec 32)) (R : Mem 64 → Prop),
      n.toNat ≤ ws.length ∧ n.toNat ≤ tmp.length ∧ 256 ≤ cnt.length ∧
      n.toNat < 2 ^ 31 ∧ max_off.toNat < 2 ^ 32 ∧
      (∀ j < n.toNat,
        2 * wsVal ws j + 1 < wvec.length ∧ fullWvecOff wvec (wsVal ws j) ≤ max_off.toNat) ∧
      (array (t := i32) wvec_ptr wvec ⋆ array (t := i32) ws_ptr ws ⋆
        array (t := i32) tmp_ptr tmp ⋆ array (t := i32) cnt_ptr cnt ⋆ R) m ∧
      ∀ ws' tmp' cnt' m',
        ws'.length = ws.length → tmp'.length = tmp.length → cnt'.length = cnt.length →
        (ws'.take n.toNat).Perm (ws.take n.toNat) →
        SortedRange (fullWvecOff wvec) ws' 0 n.toNat →
        (∀ i, n.toNat ≤ i → ws'[i]? = ws[i]?) →
        (array (t := i32) wvec_ptr wvec ⋆ array (t := i32) ws_ptr ws' ⋆
          array (t := i32) tmp_ptr tmp' ⋆ array (t := i32) cnt_ptr cnt' ⋆ R) m' → Q () m'

theorem full_wstack_radix_sort_m6_wp (Γ : Env) :
    ∀ a m Q X, fullWstackRadixSortSpec a m Q X →
      Func.wp Γ full_wstack_radix_sort_m6_body a m Q X := by
  rintro ⟨wvec_ptr, ws_ptr, tmp_ptr, cnt_ptr, n, max_off, ⟨⟩⟩ m Q X
    ⟨wvec, ws, tmp, cnt, R, hnw, hnt, hcnt, hn_bd, hmax_bd, hkeys, hm, hQ⟩
  m6_to_group
  refine wp_loop_inv
    (fun (shift, ()) mS =>
      (shift.toNat = 0 ∨ shift.toNat = 8 ∨ shift.toNat = 16 ∨ shift.toNat = 24 ∨
        shift.toNat = 32) ∧
      ∃ wsS tmpS cntS : List (BitVec 32),
        wsS.length = ws.length ∧ tmpS.length = tmp.length ∧ cntS.length = cnt.length ∧
        (wsS.take n.toNat).Perm (ws.take n.toNat) ∧
        (∀ i, n.toNat ≤ i → wsS[i]? = ws[i]?) ∧
        SortedRange (fun l => fullWvecOff wvec l % 2 ^ shift.toNat) wsS 0 n.toNat ∧
        (array (t := i32) wvec_ptr wvec ⋆ array (t := i32) ws_ptr wsS ⋆
          array (t := i32) tmp_ptr tmpS ⋆ array (t := i32) cnt_ptr cntS ⋆ R) mS)
    (fun (shift, ()) _ => 32 - shift.toNat)
    (fun JS hLoopS => ?_) ?_
  · m6_c0_steps
    refine hLoopS (0#64, ()) m ⟨Or.inl rfl, ws, tmp, cnt, rfl, rfl, rfl, List.Perm.refl _,
      fun _ _ => rfl, fun _ _ _ _ _ => by
        simp only [show (0#64).toNat = 0 from rfl, Nat.pow_zero, Nat.mod_one, Nat.le_refl], hm⟩
  · rintro JS ⟨shift, ⟨⟩⟩ mS ⟨hsh_dom, wsS, tmpS, cntS, hwsL, htmpL, hcntL, hpermS, hsufS,
      hsrtS, hmS⟩ hLoopS
    clear hm
    have hkeysS : ∀ j < n.toNat,
        2 * wsVal wsS j + 1 < wvec.length ∧ fullWvecOff wvec (wsVal wsS j) ≤ max_off.toNat := by
      intro j hj
      have hj' : j < (wsS.take n.toNat).length := by rw [List.length_take]; omega
      have hmem : wsS[j]'(by omega) ∈ wsS.take n.toNat := by
        have hgm := List.getElem_mem (l := wsS.take n.toNat) (n := j) hj'
        rwa [List.getElem_take] at hgm
      obtain ⟨j0, hj0, hget0⟩ := List.mem_iff_getElem.mp (hpermS.mem_iff.mp hmem)
      rw [List.length_take] at hj0; have hj0_lt : j0 < n.toNat := by omega
      rw [List.getElem_take] at hget0
      have heq : wsVal wsS j = wsVal ws j0 := by
        unfold wsVal; rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
          Option.getD_some, Option.getD_some, hget0]
      rw [heq]; exact hkeys j0 hj0_lt
    m6_split
    · have hsh_lt32 : shift.toNat < 32 := by c0_bound
      have hsh_vals : shift.toNat = 0 ∨ shift.toNat = 8 ∨ shift.toNat = 16 ∨
          shift.toNat = 24 := by omega
      have hsh64 : shift.toNat % 64 = shift.toNat := Nat.mod_eq_of_lt (by omega)
      m6_split
      · -- `(max_off >>> shift) != 0#64`
        have hne0 : max_off.toNat / 2 ^ shift.toNat ≠ 0 := by
          intro h0; apply hc; apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ushiftRight, hsh64, Nat.shiftRight_eq_div_pow, h0]; rfl
        clear hc
        let bkts : Nat → Nat := fun j => (fullWvecOff wvec (wsVal wsS j) / 2 ^ shift.toNat) % 256
        have hbkts_lt : ∀ j < n.toNat, bkts j < 256 := fun j _ => Nat.mod_lt _ (by decide)
        -- Loop 1: zero `cnt[0..256)`
        m6_to_group
        refine wp_loop_inv (ts := [i64])
          (fun (b, ()) m1 => b.toNat ≤ 256 ∧ ∃ cnt1 : List (BitVec 32),
            cnt1.length = cnt.length ∧ (∀ k < b.toNat, cnt1[k]? = some 0#32) ∧
            (array (t := i32) wvec_ptr wvec ⋆ array (t := i32) ws_ptr wsS ⋆
              array (t := i32) tmp_ptr tmpS ⋆ array (t := i32) cnt_ptr cnt1 ⋆ R) m1)
          (fun (b, ()) _ => 256 - b.toNat) (fun J1 hLoop1 => ?_) ?_
        · m6_c0_steps
          exact hLoop1 (0#64, ()) mS ⟨by simp, cntS, hcntL, fun _ hk => by simp at hk, hmS⟩
        · rintro J1 ⟨b, ⟨⟩⟩ m1 ⟨hb_le, cnt1, hcnt1, hzero1, hm1⟩ hLoop1
          m6_split
          · have hb_lt : b.toNat < 256 := by c0_bound
            have hb1 : (b + 1#64).toNat = b.toNat + 1 := by bv_omega
            have hb_cnt : b.toNat < cnt1.length := by omega
            m6_c0_steps
            refine hLoop1 (b + 1#64, ()) _ (by dsimp only; rw [hb1]; omega)
              ⟨by rw [hb1]; omega, cnt1.set b.toNat 0#32, by simp [hcnt1], fun k hk => ?_,
               sep_ac hm⟩
            rw [hb1] at hk
            by_cases hkb : k = b.toNat
            · subst hkb; exact List.getElem?_set_self (by omega)
            · rw [List.getElem?_set_ne (by omega)]; exact hzero1 k (by omega)
          · have hb_eq : b.toNat = 256 := by c0_bound
            rw [hb_eq] at hzero1
            -- Loop 2: count buckets `j = 0..n`
            m6_c0_steps
            refine wp_loop_inv (ts := [i64])
              (fun (j, ()) m2 => j.toNat ≤ n.toNat ∧ ∃ cnt2 : List (BitVec 32),
                cnt2.length = cnt.length ∧
                (∀ b < 256, (cnt2[b]?.getD 0#32).toNat = countEqUpTo bkts j.toNat b) ∧
                (array (t := i32) wvec_ptr wvec ⋆ array (t := i32) ws_ptr wsS ⋆
                  array (t := i32) tmp_ptr tmpS ⋆ array (t := i32) cnt_ptr cnt2 ⋆ R) m2)
              (fun (j, ()) _ => n.toNat - j.toNat) (fun J2 hLoop2 => ?_) ?_
            · m6_c0_steps
              refine hLoop2 (0#64, ()) m1 ⟨by simp, cnt1, hcnt1, fun b hb => by
                rw [hzero1 b hb]; simp [countEqUpTo_zero], hm1⟩
            · rintro J2 ⟨j, ⟨⟩⟩ m2 ⟨hj_le, cnt2, hcnt2, hcnt_eq, hm2⟩ hLoop2
              m6_split
              · have hj_lt : j.toNat < n.toNat := by c0_bound
                have hj_ws : j.toNat < wsS.length := by omega
                have hlit_info := hkeysS j.toNat hj_lt
                have hlit_idx : 2 * (wsS[j.toNat]'hj_ws).toNat < wvec.length := by
                  have h := hlit_info.1; unfold wsVal at h
                  rw [List.getElem?_eq_getElem hj_ws, Option.getD_some] at h; omega
                let off32 := wvec[2 * (wsS[j.toNat]'hj_ws).toNat]'hlit_idx
                have hoff_val : off32.toNat = fullWvecOff wvec (wsVal wsS j.toNat) := by
                  dsimp only [off32]; unfold fullWvecOff wsVal
                  rw [List.getElem?_eq_getElem hj_ws, Option.getD_some,
                    List.getElem?_eq_getElem hlit_idx, Option.getD_some]
                have hidx_ws : ((wsS[j.toNat]'hj_ws).setWidth 64 <<< 1).toNat =
                    2 * (wsS[j.toNat]'hj_ws).toNat := by
                  rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide)]
                  simp [Nat.shiftLeft_eq]; omega
                have hbkt_raw :
                    ((BitVec.setWidth 64 wvec[(BitVec.setWidth 64 wsS[j.toNat] <<< 1).toNat] >>>
                      (shift.toNat % 64) &&& 255).toNat) = bkts j.toNat := by
                  have hgw : wvec[(BitVec.setWidth 64 wsS[j.toNat] <<< 1).toNat]'(by
                      rw [hidx_ws]; exact hlit_idx) = off32 := by
                    dsimp only [off32]; congr 1
                  rw [show (255 : BitVec 64) = 255#64 from rfl, hgw, bv32_mask_lt256,
                    BitVec.toNat_ushiftRight, zext_toNat off32 (by decide), hsh64,
                    Nat.shiftRight_eq_div_pow, hoff_val]
                have hbkt_lt : bkts j.toNat < 256 := hbkts_lt j.toNat hj_lt
                have hle_j : countEqUpTo bkts j.toNat (bkts j.toNat) ≤ j.toNat :=
                  Nat.le_trans List.countP_le_length (by simp)
                have hj1 : (j + 1#64).toNat = j.toNat + 1 := by bv_omega
                m6_c0_steps
                have hm' :
                    (array (t := i32) wvec_ptr wvec ⋆ array (t := i32) ws_ptr wsS ⋆
                      array (t := i32) tmp_ptr tmpS ⋆
                      array (t := i32) cnt_ptr
                        (cnt2.set (bkts j.toNat) ((cnt2[bkts j.toNat]'(by omega)) + 1#32)) ⋆
                      R) m := by
                  have h1 :
                      cnt2.set
                        ((BitVec.setWidth 64
                            wvec[(BitVec.setWidth 64 wsS[j.toNat] <<< 1).toNat] >>>
                            (shift.toNat % 64) &&& 255).toNat)
                        (cnt2[(BitVec.setWidth 64
                            wvec[(BitVec.setWidth 64 wsS[j.toNat] <<< 1).toNat] >>>
                            (shift.toNat % 64) &&& 255).toNat] + 1#32) =
                      cnt2.set (bkts j.toNat) ((cnt2[bkts j.toNat]'(by omega)) + 1#32) := by
                    simp only [hbkt_raw]
                  rw [← h1]; exact sep_ac hm
                refine hLoop2 (j + 1#64, ()) _ (by dsimp only; rw [hj1]; omega)
                  ⟨by rw [hj1]; omega,
                   cnt2.set (bkts j.toNat) ((cnt2[bkts j.toNat]'(by omega)) + 1#32),
                   by simp [hcnt2], fun b hb => ?_, hm'⟩
                rw [hj1, countEqUpTo_succ]
                by_cases hbb : bkts j.toNat = b
                · subst hbb; rw [List.getElem?_set_self (by omega), Option.getD_some,
                    BitVec.toNat_add, BitVec.toNat_ofNat, full_lt_getElem?_eq (by omega),
                    hcnt_eq _ hb]
                  simp only [↓reduceIte]; exact Nat.mod_eq_of_lt (by omega)
                · rw [List.getElem?_set_ne hbb]; simp only [hbb, ↓reduceIte]; exact hcnt_eq b hb
              · have hj_eq : j.toNat = n.toNat := by
                  have : ¬ (j.toNat < n.toNat) := by c0_bound
                  omega
                rw [hj_eq] at hcnt_eq
                -- Loop 3: prefix sums over `b = 0..256`
                m6_c0_steps
                refine wp_loop_inv (ts := [i64, i64])
                  (fun (b, sum, ()) m3 =>
                    b.toNat ≤ 256 ∧ sum.toNat = countLt bkts n.toNat b.toNat ∧
                    ∃ cnt3 : List (BitVec 32), cnt3.length = cnt.length ∧
                      (∀ k < b.toNat, (cnt3[k]?.getD 0#32).toNat = countLt bkts n.toNat k) ∧
                      (∀ k, b.toNat ≤ k → k < 256 →
                        (cnt3[k]?.getD 0#32).toNat = countEqUpTo bkts n.toNat k) ∧
                      (array (t := i32) wvec_ptr wvec ⋆ array (t := i32) ws_ptr wsS ⋆
                        array (t := i32) tmp_ptr tmpS ⋆ array (t := i32) cnt_ptr cnt3 ⋆ R) m3)
                  (fun (b, _, ()) _ => 256 - b.toNat) (fun J3 hLoop3 => ?_) ?_
                · m6_c0_steps
                  exact hLoop3 (0#64, 0#64, ()) m2 ⟨by simp, by simp [countLt_zero], cnt2, hcnt2,
                    fun _ hk => by simp at hk, fun k _ hk => hcnt_eq k hk, hm2⟩
                · rintro J3 ⟨b, sum, ⟨⟩⟩ m3 ⟨hb3, hsum, cnt3, hcnt3, hpref3, hrem3, hm3⟩ hLoop3
                  m6_split
                  · have hb_lt : b.toNat < 256 := by c0_bound
                    have hb_len : b.toNat < cnt3.length := by omega
                    have hsum_le : sum.toNat ≤ n.toNat := by
                      rw [hsum]; have := countLt_top hbkts_lt
                      have hle := countLt_mono (bkts := bkts) (n := n.toNat)
                        (show b.toNat ≤ 256 by omega)
                      omega
                    have hcb_le : (cnt3[b.toNat]'hb_len).toNat =
                        countEqUpTo bkts n.toNat b.toNat := by
                      rw [full_lt_getElem?_eq hb_len]; exact hrem3 b.toNat (by omega) hb_lt
                    have hsum_new_le : sum.toNat + (cnt3[b.toNat]'hb_len).toNat ≤ n.toNat := by
                      rw [hsum, hcb_le, ← countLt_succ]
                      have hle := countLt_mono (bkts := bkts) (n := n.toNat)
                        (show b.toNat + 1 ≤ 256 by omega)
                      rw [countLt_top hbkts_lt] at hle; exact hle
                    have hb1 : (b + 1#64).toNat = b.toNat + 1 := by bv_omega
                    m6_c0_steps
                    refine hLoop3 (b + 1#64, sum + (cnt3[b.toNat]'hb_len).setWidth 64, ()) _
                      (by dsimp only; rw [hb1]; omega)
                      ⟨by rw [hb1]; omega, ?_, cnt3.set b.toNat (sum.setWidth 32),
                       by simp [hcnt3], fun k hk => ?_, fun k hk1 hk2 => ?_, sep_ac hm⟩
                    · rw [hb1, countLt_succ, ← hsum, ← hcb_le, BitVec.toNat_add,
                        zext_toNat _ (by decide)]
                      exact Nat.mod_eq_of_lt (by omega)
                    · rw [hb1] at hk
                      by_cases hkb : k = b.toNat
                      · subst hkb; rw [List.getElem?_set_self hb_len, Option.getD_some,
                          BitVec.toNat_setWidth, hsum]; exact Nat.mod_eq_of_lt (by omega)
                      · rw [List.getElem?_set_ne (Ne.symm hkb)]; exact hpref3 k (by omega)
                    · rw [hb1] at hk1
                      rw [List.getElem?_set_ne (by omega)]; exact hrem3 k (by omega) hk2
                  · have hb_eq : b.toNat = 256 := by c0_bound
                    rw [hb_eq] at hpref3
                    -- Loop 4: scatter `wsS[0..n)` into `tmpS[0..n)` using `bktPlace`
                    m6_c0_steps
                    refine wp_loop_inv (ts := [i64])
                      (fun (j, ()) m4 => j.toNat ≤ n.toNat ∧
                        ∃ (tmp4 cnt4 : List (BitVec 32)),
                          tmp4.length = tmp.length ∧ cnt4.length = cnt.length ∧
                          (∀ bb < 256, (cnt4[bb]?.getD 0#32).toNat =
                            countLt bkts n.toNat bb + countEqUpTo bkts j.toNat bb) ∧
                          (∀ k < j.toNat, tmp4[bktPlace bkts n.toNat k]? = wsS[k]?) ∧
                          (array (t := i32) wvec_ptr wvec ⋆ array (t := i32) ws_ptr wsS ⋆
                            array (t := i32) tmp_ptr tmp4 ⋆ array (t := i32) cnt_ptr cnt4 ⋆ R) m4)
                      (fun (j, ()) _ => n.toNat - j.toNat) (fun J4 hLoop4 => ?_) ?_
                    · m6_c0_steps
                      exact hLoop4 (0#64, ()) m3 ⟨by simp, tmpS, cnt3, htmpL, hcnt3,
                        fun bb hbb => by
                          rw [show (0#64).toNat = 0 from rfl, countEqUpTo_zero, Nat.add_zero]
                          exact hpref3 bb hbb,
                        fun _ hk => by simp at hk, hm3⟩
                    · rintro J4 ⟨j, ⟨⟩⟩ m4 ⟨hj_le, tmp4, cnt4, htmp4, hcnt4, hcnt_p, hscat, hm4⟩
                        hLoop4
                      m6_split
                      · have hj_lt : j.toNat < n.toNat := by c0_bound
                        have hj_ws : j.toNat < wsS.length := by omega
                        have hlit_info := hkeysS j.toNat hj_lt
                        have hlit_idx : 2 * (wsS[j.toNat]'hj_ws).toNat < wvec.length := by
                          have h := hlit_info.1; unfold wsVal at h
                          rw [List.getElem?_eq_getElem hj_ws, Option.getD_some] at h; omega
                        let off32 := wvec[2 * (wsS[j.toNat]'hj_ws).toNat]'hlit_idx
                        have hoff_val : off32.toNat = fullWvecOff wvec (wsVal wsS j.toNat) := by
                          dsimp only [off32]; unfold fullWvecOff wsVal
                          rw [List.getElem?_eq_getElem hj_ws, Option.getD_some,
                            List.getElem?_eq_getElem hlit_idx, Option.getD_some]
                        have hidx_ws : ((wsS[j.toNat]'hj_ws).setWidth 64 <<< 1).toNat =
                            2 * (wsS[j.toNat]'hj_ws).toNat := by
                          rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide)]
                          simp [Nat.shiftLeft_eq]; omega
                        have hbkt_raw :
                            ((BitVec.setWidth 64
                                wvec[(BitVec.setWidth 64 wsS[j.toNat] <<< 1).toNat] >>>
                              (shift.toNat % 64) &&& 255).toNat) = bkts j.toNat := by
                          have hgw : wvec[(BitVec.setWidth 64 wsS[j.toNat] <<< 1).toNat]'(by
                              rw [hidx_ws]; exact hlit_idx) = off32 := by
                            dsimp only [off32]; congr 1
                          rw [show (255 : BitVec 64) = 255#64 from rfl, hgw, bv32_mask_lt256,
                            BitVec.toNat_ushiftRight, zext_toNat off32 (by decide), hsh64,
                            Nat.shiftRight_eq_div_pow, hoff_val]
                        have hbkt_lt : bkts j.toNat < 256 := hbkts_lt j.toNat hj_lt
                        have hpos_val : (cnt4[bkts j.toNat]'(by omega)).toNat =
                            bktPlace bkts n.toNat j.toNat := by
                          rw [full_lt_getElem?_eq (by omega)]; exact hcnt_p _ hbkt_lt
                        have hpos_lt : bktPlace bkts n.toNat j.toNat < n.toNat :=
                          bktPlace_lt hj_lt hbkts_lt
                        let pos64 := (cnt4[bkts j.toNat]'(by omega)).setWidth 64
                        have hpos64 : pos64.toNat = bktPlace bkts n.toNat j.toNat := by
                          rw [zext_toNat _ (by decide), hpos_val]
                        let cnt4' := cnt4.set (bkts j.toNat) ((pos64 + 1#64).setWidth 32)
                        have hj1 : (j + 1#64).toNat = j.toNat + 1 := by bv_omega
                        m6_c0_steps
                        have hcnt_eq' :
                            cnt4.set (BitVec.setWidth 64
                              wvec[(BitVec.setWidth 64 wsS[j.toNat] <<< 1).toNat] >>>
                              (shift.toNat % 64) &&& 255).toNat
                              (BitVec.setWidth 32
                                (BitVec.setWidth 64
                                  cnt4[(BitVec.setWidth 64
                                    wvec[(BitVec.setWidth 64 wsS[j.toNat] <<< 1).toNat] >>>
                                    (shift.toNat % 64) &&& 255).toNat] + 1)) = cnt4' := by
                          dsimp only [cnt4', pos64]
                          simp only [hbkt_raw, show (1 : BitVec 64) = 1#64 from rfl]
                        have hpos_raw :
                            (cnt4[(BitVec.setWidth 64
                                wvec[(BitVec.setWidth 64 wsS[j.toNat] <<< 1).toNat] >>>
                                (shift.toNat % 64) &&& 255).toNat]'(by
                              rw [hbkt_raw]; omega)).setWidth 64 = pos64 := by
                          dsimp only [pos64]; simp only [hbkt_raw]
                        have hpos_nat :
                            ((cnt4[(BitVec.setWidth 64
                                wvec[(BitVec.setWidth 64 wsS[j.toNat] <<< 1).toNat] >>>
                                (shift.toNat % 64) &&& 255).toNat]'(by
                              rw [hbkt_raw]; omega)).setWidth 64).toNat =
                              bktPlace bkts n.toNat j.toNat := by
                          rw [hpos_raw]; exact hpos64
                        have hhmA :
                            (array (t := i32) tmp_ptr tmp4 ⋆ (array (t := i32) wvec_ptr wvec ⋆
                              array (t := i32) ws_ptr wsS ⋆ array (t := i32) cnt_ptr cnt4' ⋆
                              R)) m := by
                          rw [← hcnt_eq']; exact sep_ac hm
                        have hst4b := arr32_store_mul4 (v := wsS[j.toNat]'hj_ws)
                          (by rw [hpos_nat]; omega) hhmA
                        apply wp_store_sep hst4b
                        intro m2 hm2; m6_c0_steps
                        have hm' :
                            (array (t := i32) wvec_ptr wvec ⋆ array (t := i32) ws_ptr wsS ⋆
                              array (t := i32) tmp_ptr
                                (tmp4.set (bktPlace bkts n.toNat j.toNat)
                                  (wsS[j.toNat]'hj_ws)) ⋆
                              array (t := i32) cnt_ptr cnt4' ⋆ R) m2 := by
                          rw [← hpos_nat]; exact sep_ac hm2
                        refine hLoop4 (j + 1#64, ()) _ (by dsimp only; rw [hj1]; omega)
                          ⟨by rw [hj1]; omega,
                           tmp4.set (bktPlace bkts n.toNat j.toNat) (wsS[j.toNat]'hj_ws),
                           cnt4', by simp [htmp4], by simp [cnt4', hcnt4],
                           fun bb hbb => ?_, fun k hk => ?_, hm'⟩
                        · rw [hj1, countEqUpTo_succ]
                          by_cases hbb2 : bkts j.toNat = bb
                          · subst hbb2; dsimp only [cnt4']
                            rw [List.getElem?_set_self (by omega), Option.getD_some,
                              BitVec.toNat_setWidth, BitVec.toNat_add, hpos64]
                            unfold bktPlace
                            have hlt32 : countLt bkts n.toNat (bkts j.toNat) +
                                countEqUpTo bkts j.toNat (bkts j.toNat) + 1 < 2 ^ 32 := by
                              have hlt := hpos_lt; unfold bktPlace at hlt; omega
                            have hlt64 : countLt bkts n.toNat (bkts j.toNat) +
                                countEqUpTo bkts j.toNat (bkts j.toNat) + 1 < 2 ^ 64 := by omega
                            rw [show (1#64).toNat = 1 from rfl, Nat.mod_eq_of_lt hlt64,
                              Nat.mod_eq_of_lt hlt32, Nat.add_assoc]; simp
                          · dsimp only [cnt4']; rw [List.getElem?_set_ne hbb2]; simp [hbb2]
                            exact hcnt_p bb hbb
                        · rw [hj1] at hk
                          by_cases hkj : k = j.toNat
                          · subst hkj; rw [List.getElem?_set_self (by omega),
                              List.getElem?_eq_getElem hj_ws]
                          · have hne := bktPlace_inj (bkts := bkts) (hk1 := by omega)
                              (hk2 := hj_lt) (show k ≠ j.toNat by omega)
                            rw [List.getElem?_set_ne (by omega)]; exact hscat k (by omega)
                      · have hj_eq : j.toNat = n.toNat := by
                          have : ¬ (j.toNat < n.toNat) := by c0_bound
                          omega
                        rw [hj_eq] at hscat
                        -- Loop 5: copy `tmp4[0..n)` back into `wsS[0..n)`
                        m6_c0_steps
                        refine wp_loop_inv (ts := [i64])
                          (fun (j, ()) m5 => j.toNat ≤ n.toNat ∧ ∃ ws5 : List (BitVec 32),
                            ws5.length = ws.length ∧
                            (∀ k < j.toNat, ws5[k]? = tmp4[k]?) ∧
                            (∀ k, j.toNat ≤ k → ws5[k]? = wsS[k]?) ∧
                            (array (t := i32) wvec_ptr wvec ⋆ array (t := i32) ws_ptr ws5 ⋆
                              array (t := i32) tmp_ptr tmp4 ⋆ array (t := i32) cnt_ptr cnt4 ⋆
                              R) m5)
                          (fun (j, ()) _ => n.toNat - j.toNat) (fun J5 hLoop5 => ?_) ?_
                        · m6_c0_steps; exact hLoop5 (0#64, ()) m4 ⟨by simp, wsS, hwsL,
                            fun _ hk => by simp at hk, fun _ _ => rfl, hm4⟩
                        · rintro J5 ⟨j, ⟨⟩⟩ m5 ⟨hj5, ws5, hws5, hpre5, hsuf5, hm5⟩ hLoop5
                          m6_split
                          · have hj_lt : j.toNat < n.toNat := by c0_bound
                            have hj_t : j.toNat < tmp4.length := by omega
                            have hj_w : j.toNat < ws5.length := by omega
                            have hj1 : (j + 1#64).toNat = j.toNat + 1 := by bv_omega
                            m6_c0_steps
                            refine hLoop5 (j + 1#64, ()) _ (by dsimp only; rw [hj1]; omega)
                              ⟨by rw [hj1]; omega, ws5.set j.toNat (tmp4[j.toNat]'hj_t),
                               by simp [hws5], fun k hk => ?_, fun k hk => ?_, sep_ac hm⟩
                            · rw [hj1] at hk
                              by_cases hkj : k = j.toNat
                              · subst hkj; rw [List.getElem?_set_self (by omega),
                                  List.getElem?_eq_getElem (by omega)]
                              · rw [List.getElem?_set_ne (by omega)]; exact hpre5 k (by omega)
                            · rw [hj1] at hk; rw [List.getElem?_set_ne (by omega)]
                              exact hsuf5 k (by omega)
                          · have hj_eq2 : j.toNat = n.toNat := by
                              have : ¬ (j.toNat < n.toNat) := by c0_bound
                              omega
                            rw [hj_eq2] at hpre5 hsuf5
                            have hws5_take : ∀ k < n.toNat, ws5[k]? = tmp4[k]? := hpre5
                            have hsh8 : (shift + 8#64).toNat = shift.toNat + 8 := by bv_omega
                            have hperm5 : (ws5.take n.toNat).Perm (ws.take n.toNat) := by
                              have hpt : (tmp4.take n.toNat).Perm (wsS.take n.toNat) :=
                                perm_of_bktPlace hbkts_lt (by omega) (by omega) hscat
                              have hpe : ws5.take n.toNat = tmp4.take n.toNat := by
                                apply List.ext_getElem (by simp [List.length_take]; omega)
                                intro i hi _; simp only [List.length_take] at hi
                                have hi_n : i < n.toNat := by omega
                                rw [List.getElem_take, List.getElem_take]
                                exact Option.some.inj (by
                                  rw [← List.getElem?_eq_getElem (by omega),
                                    ← List.getElem?_eq_getElem (by omega)]
                                  exact hws5_take i hi_n)
                              rw [hpe]; exact hpt.trans hpermS
                            have hsrt5 : SortedRange
                                (fun l => fullWvecOff wvec l % 2 ^ (shift + 8#64).toNat)
                                ws5 0 n.toNat := by
                              intro p1 p2 _ hp12 hp2
                              rcases Nat.eq_or_lt_of_le hp12 with rfl | hp12_lt
                              · exact Nat.le_refl _
                              obtain ⟨k1, hk1, hpk1⟩ := bktPlace_surj hbkts_lt (p := p1) (by omega)
                              obtain ⟨k2, hk2, hpk2⟩ := bktPlace_surj hbkts_lt (p := p2) hp2
                              have hw1 : wsVal ws5 p1 = wsVal wsS k1 := by
                                unfold wsVal
                                rw [hws5_take p1 (by omega), ← hpk1, hscat k1 hk1]
                              have hw2 : wsVal ws5 p2 = wsVal wsS k2 := by
                                unfold wsVal
                                rw [hws5_take p2 hp2, ← hpk2, hscat k2 hk2]
                              dsimp only
                              rw [hsh8, hw1, hw2, ← div_pow2_mod_256_shift _ shift.toNat,
                                ← div_pow2_mod_256_shift _ shift.toNat]
                              rcases bktPlace_order_back hk1 hk2
                                  (by rw [hpk1, hpk2]; exact hp12_lt)
                                with hb_lt | ⟨hb_eq, hk12⟩
                              · have hlt_m := hb_lt; dsimp only [bkts] at hlt_m
                                have hmod_lt : fullWvecOff wvec (wsVal wsS k1) % 2 ^ shift.toNat <
                                    2 ^ shift.toNat := Nat.mod_lt _ (Nat.two_pow_pos _)
                                have hmul_le : (fullWvecOff wvec (wsVal wsS k1) /
                                    2 ^ shift.toNat) % 256 * 2 ^ shift.toNat + 2 ^ shift.toNat ≤
                                    (fullWvecOff wvec (wsVal wsS k2) / 2 ^ shift.toNat) % 256 *
                                      2 ^ shift.toNat := by
                                  rw [← Nat.succ_mul]
                                  exact Nat.mul_le_mul_right _ hlt_m
                                omega
                              · have hle_low := hsrtS k1 k2 (by omega) (by omega) hk2
                                dsimp only at hle_low; dsimp only [bkts] at hb_eq
                                rw [hb_eq]; omega
                            m6_c0_steps
                            refine hLoopS (shift + 8#64, ()) m5 (by dsimp only; rw [hsh8]; omega)
                              ⟨by rcases hsh_vals with h0 | h0 | h0 | h0 <;>
                                  rw [hsh8, h0] <;> simp,
                               ws5, tmp4, cnt4, hws5, htmp4, hcnt4, hperm5,
                               fun i hi => by rw [hsuf5 i hi, hsufS i hi], hsrt5, hm5⟩
      · have hdiv0 : max_off.toNat / 2 ^ shift.toNat = 0 := by
          have h1 : (max_off >>> (shift.toNat % 64)).toNat = (0#64).toNat := by
            exact congrArg BitVec.toNat hc
          rw [hsh64, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at h1
          exact h1
        have hmax_lt : max_off.toNat < 2 ^ shift.toNat :=
          (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).mp hdiv0
        have hsrt_fin : SortedRange (fullWvecOff wvec) wsS 0 n.toNat := by
          intro i j hi hij hj
          have hi_le : fullWvecOff wvec (wsVal wsS i) ≤ max_off.toNat :=
            (hkeysS i (by omega)).2
          have hj_le : fullWvecOff wvec (wsVal wsS j) ≤ max_off.toNat := (hkeysS j hj).2
          have hmod_i : fullWvecOff wvec (wsVal wsS i) % 2 ^ shift.toNat =
              fullWvecOff wvec (wsVal wsS i) := Nat.mod_eq_of_lt (by omega)
          have hmod_j : fullWvecOff wvec (wsVal wsS j) % 2 ^ shift.toNat =
              fullWvecOff wvec (wsVal wsS j) := Nat.mod_eq_of_lt (by omega)
          rw [← hmod_i, ← hmod_j]; exact hsrtS i j hi hij hj
        m6_c0_steps
        exact hQ wsS tmpS cntS _ hwsL htmpL hcntL hpermS hsrt_fin hsufS hmS
    · have hsh32 : shift.toNat = 32 := by
        have hlt : ¬ (shift.toNat < 32) := by c0_bound
        rcases hsh_dom with h0 | h0 | h0 | h0 | h0 <;> omega
      have hsrt_fin : SortedRange (fullWvecOff wvec) wsS 0 n.toNat := by
        intro i j hi hij hj
        have hi_lt : fullWvecOff wvec (wsVal wsS i) < 2 ^ 32 :=
          Nat.lt_of_le_of_lt (hkeysS i (by omega)).2 hmax_bd
        have hj_lt : fullWvecOff wvec (wsVal wsS j) < 2 ^ 32 :=
          Nat.lt_of_le_of_lt (hkeysS j hj).2 hmax_bd
        have hmod_i : fullWvecOff wvec (wsVal wsS i) % 2 ^ shift.toNat =
            fullWvecOff wvec (wsVal wsS i) := Nat.mod_eq_of_lt (by rw [hsh32]; exact hi_lt)
        have hmod_j : fullWvecOff wvec (wsVal wsS j) % 2 ^ shift.toNat =
            fullWvecOff wvec (wsVal wsS j) := Nat.mod_eq_of_lt (by rw [hsh32]; exact hj_lt)
        rw [← hmod_i, ← hmod_j]; exact hsrtS i j hi hij hj
      m6_c0_steps
      exact hQ wsS tmpS cntS _ hwsL htmpL hcntL hpermS hsrt_fin hsufS hmS

/-! ## 3. `full_wstack_defrag_m6_wp` (`Full.fullWstackDefragSpec`) -/

private theorem sep_reassoc_split {A B C D E F G Rest R : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ (C ⋆ (D ⋆ (E ⋆ (F ⋆ (G ⋆ (Rest ⋆ R)))))))) m) :
    (A ⋆ B ⋆ E ⋆ F ⋆ (C ⋆ D ⋆ G ⋆ Rest ⋆ R)) m := sep_ac h

private theorem sep_reassoc_unsplit {A B C D E F G Rest R : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ (E ⋆ (F ⋆ (C ⋆ (D ⋆ (G ⋆ (Rest ⋆ R)))))))) m) :
    (A ⋆ (B ⋆ (C ⋆ (D ⋆ (E ⋆ (F ⋆ (G ⋆ (Rest ⋆ R)))))))) m := sep_ac h

private theorem sep_rot4_front {W WS WT Rest R : Mem 64 → Prop} {m : Mem 64}
    (h : (W ⋆ (WS ⋆ (WT ⋆ (Rest ⋆ R)))) m) : (WT ⋆ (W ⋆ (WS ⋆ (Rest ⋆ R)))) m := sep_ac h

private theorem sep_rot4_back {WT W WS Rest R : Mem 64 → Prop} {m : Mem 64}
    (h : (WT ⋆ (W ⋆ (WS ⋆ (Rest ⋆ R)))) m) : (W ⋆ (WS ⋆ (WT ⋆ (Rest ⋆ R)))) m := sep_ac h

private theorem full_wvec_wsort_split3 {c : FullCfg} {s : FullState} {n : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (h2n : 2 * n + 256 ≤ 2 * c.max_vars)
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pWvec s.core.wvec ⋆
      array (t := i32) c.pWsort (s.scratch.wsort.take n) ⋆
      array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * n))
        ((s.scratch.wsort.drop n).take n) ⋆
      array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * (2 * n)))
        ((s.scratch.wsort.drop (2 * n)).take 256) ⋆
      (array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * (2 * n + 256)))
        (s.scratch.wsort.drop (2 * n + 256)) ⋆ FullWvecWsortRest c s ⋆ R)) m := by
  have hws : s.scratch.wsort.length = 2 * c.max_vars := hlen.scratch_ok.wsort_len
  have hm1 := focus_wvec_wsort hm
  rw [array32_split_4 (a := c.pWsort) (xs := s.scratch.wsort) (k1 := n) (k2 := 2 * n)
    (k3 := 2 * n + 256) (by omega) (by omega) (by rw [hws]; exact h2n)] at hm1
  simp only [show 2 * n - n = n by omega, show 2 * n + 256 - 2 * n = 256 by omega] at hm1
  exact sep_ac hm1

private theorem full_wvec_wsort_unsplit3 {c : FullCfg} {s : FullState} {n : Nat}
    {ws1 tmp1 cnt1 : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (h2n : 2 * n + 256 ≤ 2 * c.max_vars)
    (hws1 : ws1.length = n) (htmp1 : tmp1.length = n) (hcnt1 : cnt1.length = 256)
    (hm : (array (t := i32) c.pWvec s.core.wvec ⋆
      array (t := i32) c.pWsort ws1 ⋆
      array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * n)) tmp1 ⋆
      array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * (2 * n))) cnt1 ⋆
      (array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * (2 * n + 256)))
        (s.scratch.wsort.drop (2 * n + 256)) ⋆ FullWvecWsortRest c s ⋆ R)) m) :
    let wsort' := ws1 ++ tmp1 ++ cnt1 ++ s.scratch.wsort.drop (2 * n + 256)
    wsort'.length = 2 * c.max_vars ∧ wsort'.take n = ws1 ∧
    (FullMem c { s with scratch := { s.scratch with wsort := wsort' } } ⋆ R) m := by
  have hws : s.scratch.wsort.length = 2 * c.max_vars := hlen.scratch_ok.wsort_len
  let wsort' := ws1 ++ tmp1 ++ cnt1 ++ s.scratch.wsort.drop (2 * n + 256)
  have hlen' : wsort'.length = 2 * c.max_vars := by
    simp [wsort', hws1, htmp1, hcnt1, List.length_drop, hws]; omega
  have htk' : wsort'.take n = ws1 := by
    simp [wsort', List.append_assoc, hws1]
  have hre : array (t := i32) c.pWsort wsort' =
      (array (t := i32) c.pWsort ws1 ⋆
       array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * n)) tmp1 ⋆
       array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * (2 * n))) cnt1 ⋆
       array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * (2 * n + 256)))
         (s.scratch.wsort.drop (2 * n + 256))) := by
    dsimp only [wsort']
    rw [array_append, array_append, array_append]
    simp only [Ty.bytes, Ty.size, i32, List.length_append, hws1, htmp1, hcnt1,
      show (32 + 7) / 8 = 4 from rfl]
    have hmul2 : 4 * (n + n) = 4 * (2 * n) := by omega
    have hmul3 : 4 * (n + n + 256) = 4 * (2 * n + 256) := by omega
    rw [hmul2, hmul3]
  refine ⟨hlen', htk', unfocus_wvec_wsort ?_⟩
  rw [hre]; exact sep_ac hm

private def FullWvecWsortWstkRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  Kissat.dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur
      s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
  (Full.FullCoreByteArrs c s.core ⋆ Full.FullCoreU32A c s.core ⋆ FullCoreU32BNoWvec c s.core ⋆
    array (t := i32) c.pArena s.core.arena) ⋆
  (Full.FullScrByteArrs c s.scratch ⋆ Full.FullScrU32A c s.scratch ⋆
    FullScrWksNoWsort c s.scratch ⋆
    Full.FullScrMetaArrs c s.scratch ⋆ Full.FullScrDynArrs c s.scratch) ⋆ c.pad

private theorem fullMem_eq_wvec_wsort_wstk (c : FullCfg) (s : FullState) :
    FullMem c s = (array (t := i32) c.pWvec s.core.wvec ⋆
      array (t := i32) c.pWsort s.scratch.wsort ⋆
      array (t := i32) c.pWstk s.core.wstk ⋆ FullWvecWsortWstkRest c s) := by
  unfold FullMem Full.FullCoreArrays Full.FullScratchArrays Full.FullCoreU32B
    Full.FullCoreDynArrs Full.FullScrWksArrs FullWvecWsortWstkRest FullCoreU32BNoWvec
    FullScrWksNoWsort
  ac_rfl

private theorem full_wstack_defrag_wstk_split {c : FullCfg} {s : FullState} {n : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (hn_ws : n ≤ 2 * c.max_vars)
    (hn : s.core.wlen + n + 256 ≤ c.wcap) (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pWvec s.core.wvec ⋆
      array (t := i32) c.pWsort (s.scratch.wsort.take n) ⋆
      array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * s.core.wlen))
        ((s.core.wstk.drop s.core.wlen).take n) ⋆
      array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * (s.core.wlen + n)))
        ((s.core.wstk.drop (s.core.wlen + n)).take 256) ⋆
      (array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * n)) (s.scratch.wsort.drop n) ⋆
       array (t := i32) c.pWstk (s.core.wstk.take s.core.wlen) ⋆
       array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * (s.core.wlen + n + 256)))
         (s.core.wstk.drop (s.core.wlen + n + 256)) ⋆
       FullWvecWsortWstkRest c s ⋆ R)) m := by
  have hws : s.scratch.wsort.length = 2 * c.max_vars := hlen.scratch_ok.wsort_len
  have hwst : s.core.wstk.length = c.wcap := hlen.core_ok.wstk_len_arr
  have hwle : s.core.wlen ≤ c.wcap := hlen.core_ok.wlen_le
  have hm1 : (array (t := i32) c.pWvec s.core.wvec ⋆
      array (t := i32) c.pWsort s.scratch.wsort ⋆
      array (t := i32) c.pWstk s.core.wstk ⋆ (FullWvecWsortWstkRest c s ⋆ R)) m := by
    rw [fullMem_eq_wvec_wsort_wstk, sep_assoc] at hm; exact hm
  have hws_sp : s.scratch.wsort.take n ++ s.scratch.wsort.drop n = s.scratch.wsort :=
    List.take_append_drop _ _
  have hws_arr : array (t := i32) c.pWsort s.scratch.wsort =
      (array (t := i32) c.pWsort (s.scratch.wsort.take n) ⋆
       array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * n)) (s.scratch.wsort.drop n)) := by
    conv => lhs; rw [← hws_sp]
    rw [array_append]
    simp only [Ty.bytes, Ty.size, i32, List.length_take, hws,
      show min n (2 * c.max_vars) = n by omega, show (32 + 7) / 8 = 4 from rfl]
  have hwstk_arr : array (t := i32) c.pWstk s.core.wstk =
      (array (t := i32) c.pWstk (s.core.wstk.take s.core.wlen) ⋆
       array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * s.core.wlen))
         ((s.core.wstk.drop s.core.wlen).take n) ⋆
       array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * (s.core.wlen + n)))
         ((s.core.wstk.drop (s.core.wlen + n)).take 256) ⋆
       array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * (s.core.wlen + n + 256)))
         (s.core.wstk.drop (s.core.wlen + n + 256))) := by
    rw [array32_split_4 (a := c.pWstk) (xs := s.core.wstk) (k1 := s.core.wlen)
      (k2 := s.core.wlen + n) (k3 := s.core.wlen + n + 256)
      (by omega) (by omega) (by rw [hwst]; exact hn)]
    simp only [show s.core.wlen + n - s.core.wlen = n by omega,
      show s.core.wlen + n + 256 - (s.core.wlen + n) = 256 by omega]
  rw [hws_arr, hwstk_arr] at hm1
  simp only [sep_assoc] at hm1
  exact sep_reassoc_split (Rest := FullWvecWsortWstkRest c s) hm1

private theorem full_wstack_defrag_wstk_unsplit {c : FullCfg} {s : FullState} {n : Nat}
    {ws1 tmp1 cnt1 : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (hn_ws : n ≤ 2 * c.max_vars)
    (hn : s.core.wlen + n + 256 ≤ c.wcap)
    (hws1 : ws1.length = n) (htmp1 : tmp1.length = n) (hcnt1 : cnt1.length = 256)
    (hm : (array (t := i32) c.pWvec s.core.wvec ⋆
      array (t := i32) c.pWsort ws1 ⋆
      array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * s.core.wlen)) tmp1 ⋆
      array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * (s.core.wlen + n))) cnt1 ⋆
      (array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * n)) (s.scratch.wsort.drop n) ⋆
       array (t := i32) c.pWstk (s.core.wstk.take s.core.wlen) ⋆
       array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * (s.core.wlen + n + 256)))
         (s.core.wstk.drop (s.core.wlen + n + 256)) ⋆
       FullWvecWsortWstkRest c s ⋆ R)) m) :
    let wsort' := ws1 ++ s.scratch.wsort.drop n
    let wstk' := s.core.wstk.take s.core.wlen ++ tmp1 ++ cnt1 ++
      s.core.wstk.drop (s.core.wlen + n + 256)
    wsort'.length = 2 * c.max_vars ∧ wstk'.length = c.wcap ∧ wsort'.take n = ws1 ∧
    (∀ k < s.core.wlen, wstk'[k]? = s.core.wstk[k]?) ∧
    (FullMem c { s with core := { s.core with wstk := wstk' }
                        scratch := { s.scratch with wsort := wsort' } } ⋆ R) m := by
  have hws : s.scratch.wsort.length = 2 * c.max_vars := hlen.scratch_ok.wsort_len
  have hwst : s.core.wstk.length = c.wcap := hlen.core_ok.wstk_len_arr
  have hwle : s.core.wlen ≤ c.wcap := hlen.core_ok.wlen_le
  let wsort' := ws1 ++ s.scratch.wsort.drop n
  let wstk' := s.core.wstk.take s.core.wlen ++ tmp1 ++ cnt1 ++
    s.core.wstk.drop (s.core.wlen + n + 256)
  have hlen_ws : wsort'.length = 2 * c.max_vars := by
    simp [wsort', hws1, List.length_drop, hws]; omega
  have hlen_stk : wstk'.length = c.wcap := by
    simp [wstk', htmp1, hcnt1, List.length_take, List.length_drop, hwst]; omega
  have htk_ws : wsort'.take n = ws1 := by
    simp [wsort', hws1]
  have hpre_stk : ∀ k < s.core.wlen, wstk'[k]? = s.core.wstk[k]? := by
    intro k hk
    have hlt1 : k < (s.core.wstk.take s.core.wlen).length := by rw [List.length_take]; omega
    dsimp only [wstk']
    rw [List.append_assoc, List.append_assoc, List.getElem?_append_left hlt1,
      List.getElem?_eq_getElem hlt1, List.getElem_take, List.getElem?_eq_getElem (by omega)]
  have hre_ws : array (t := i32) c.pWsort wsort' =
      (array (t := i32) c.pWsort ws1 ⋆
       array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * n)) (s.scratch.wsort.drop n)) := by
    dsimp only [wsort']; rw [array_append]
    simp [Ty.bytes, Ty.size, i32, hws1, show (32 + 7) / 8 = 4 from rfl]
  have hre_stk : array (t := i32) c.pWstk wstk' =
      (array (t := i32) c.pWstk (s.core.wstk.take s.core.wlen) ⋆
       array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * s.core.wlen)) tmp1 ⋆
       array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * (s.core.wlen + n))) cnt1 ⋆
       array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * (s.core.wlen + n + 256)))
         (s.core.wstk.drop (s.core.wlen + n + 256))) := by
    dsimp only [wstk']; rw [array_append, array_append, array_append]
    have hlt1 : (s.core.wstk.take s.core.wlen).length = s.core.wlen := by
      rw [List.length_take]; omega
    simp only [Ty.bytes, Ty.size, i32, List.length_append, hlt1, htmp1, hcnt1,
      show (32 + 7) / 8 = 4 from rfl]
  refine ⟨hlen_ws, hlen_stk, htk_ws, hpre_stk, ?_⟩
  rw [fullMem_eq_wvec_wsort_wstk, hre_ws, hre_stk]
  simp only [sep_assoc] at hm ⊢
  exact sep_reassoc_unsplit (Rest := FullWvecWsortWstkRest c s) hm

private theorem fi_list_getElem_toNat_eq {xs : List (BitVec 32)} {i j : Nat}
    (hi : i < xs.length) (hji : j = i) :
    (xs[j]'(hji ▸ hi)).toNat = (xs[i]'hi).toNat := by subst hji; rfl

private theorem bv64_ofNat_toNat_id {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

private theorem bv64_add1_nat {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by bv_omega

private def DefragScanInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) :
    Tup Val [i64, i64, i64, i64, Ty.bool] → Mem 64 → Prop
  | (n, l, max_off, prev_off, sorted, ()), m1 =>
    l.toNat ≤ 2 * s.core.cur_vars ∧ n.toNat ≤ l.toNat ∧
    max_off.toNat ≤ c.wcap ∧ prev_off.toNat ≤ max_off.toNat ∧
    ∃ (wvec1 wsort1 : List (BitVec 32)),
      wvec1.length = 4 * c.max_vars ∧ wsort1.length = 2 * c.max_vars ∧
      (∀ j < 2 * s.core.cur_vars, wvec1[2 * j + 1]? = s.core.wvec[2 * j + 1]?) ∧
      (∀ j < 2 * s.core.cur_vars,
        0 < fullWatchSize s j → wvec1[2 * j]? = s.core.wvec[2 * j]?) ∧
      (∀ j < l.toNat, fullWatchSize s j = 0 → wvec1[2 * j]? = some 0#32) ∧
      WsCovers wsort1 n.toNat l.toNat (fullWatchSize s) ∧
      (∀ j < n.toNat, fullWatchOff s (wsVal wsort1 j) ≤ max_off.toNat) ∧
      (sorted = true → SortedRange (fullWatchOff s) wsort1 0 n.toNat ∧
        ∀ j < n.toNat, fullWatchOff s (wsVal wsort1 j) ≤ prev_off.toNat) ∧
      (FullMem c { s with core := { s.core with wvec := wvec1 },
                          scratch := { s.scratch with wsort := wsort1 } } ⋆ R) m1

private def DefragCompactInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (n : Nat) (wsort2 : List (BitVec 32)) : Tup Val [i64, i64] → Mem 64 → Prop
  | (p, i, ()), mC =>
    1 ≤ p.toNat ∧ p.toNat ≤ s.core.wlen ∧ i.toNat ≤ n ∧
    (i.toNat < n → p.toNat ≤ fullWatchOff s (wsVal wsort2 i.toNat)) ∧
    ∃ wvecC wstkC : List (BitVec 32), wvecC.length = 4 * c.max_vars ∧
      wstkC.length = c.wcap ∧
      (∀ j < 2 * s.core.cur_vars,
        (wvecC[2 * j + 1]?.getD 0#32).toNat = fullWatchSize s j) ∧
      (∀ j < 2 * s.core.cur_vars,
        fullWatchSize s j = 0 → (wvecC[2 * j]?.getD 0#32).toNat = 0) ∧
      (∀ j < i.toNat, let l := wsVal wsort2 j
        let off := (wvecC[2 * l]?.getD 0#32).toNat
        1 ≤ off ∧ off + fullWatchSize s l ≤ p.toNat ∧
        ∀ k < fullWatchSize s l, wstkC[off + k]? = s.core.wstk[fullWatchOff s l + k]?) ∧
      (∀ a < i.toNat, ∀ b < i.toNat, a ≠ b →
        let la := wsVal wsort2 a; let lb := wsVal wsort2 b
        (wvecC[2 * la]?.getD 0#32).toNat + fullWatchSize s la ≤
          (wvecC[2 * lb]?.getD 0#32).toNat ∨
        (wvecC[2 * lb]?.getD 0#32).toNat + fullWatchSize s lb ≤
          (wvecC[2 * la]?.getD 0#32).toNat) ∧
      (∀ j, i.toNat ≤ j → j < n → let l := wsVal wsort2 j
        (wvecC[2 * l]?.getD 0#32).toNat = fullWatchOff s l ∧ ∀ k < fullWatchSize s l,
          wstkC[fullWatchOff s l + k]? = s.core.wstk[fullWatchOff s l + k]?) ∧
      (FullMem c { s with core := { s.core with wvec := wvecC, wstk := wstkC },
                          scratch := { s.scratch with wsort := wsort2 } } ⋆ R) mC

private def DefragSortPost (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (wvec1 : List (BitVec 32)) (n : Nat) (_ : Tup Val []) (m2 : Mem 64) : Prop :=
  ∃ wstk2 wsort2 : List (BitVec 32),
    wstk2.length = c.wcap ∧ wsort2.length = 2 * c.max_vars ∧
    (∀ i < s.core.wlen, wstk2[i]? = s.core.wstk[i]?) ∧
    WsCovers wsort2 n (2 * s.core.cur_vars) (fullWatchSize s) ∧
    SortedRange (fullWatchOff s) wsort2 0 n ∧
    (FullMem c { s with core := { s.core with wvec := wvec1, wstk := wstk2 },
                        scratch := { s.scratch with wsort := wsort2 } } ⋆ R) m2

private def DefragHeapInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (wvec1 : List (BitVec 32)) (n : Nat) : Tup Val [i64] → Mem 64 → Prop
  | (st, ()), mB =>
    st.toNat ≤ n ∧ ∃ wsB : List (BitVec 32),
      wsB.length = 2 * c.max_vars ∧
      WsCovers wsB n (2 * s.core.cur_vars) (fullWatchSize s) ∧
      FullWsortMaxHeap wvec1 wsB st.toNat n ∧
      (FullMem c { s with core := { s.core with wvec := wvec1 },
                          scratch := { s.scratch with wsort := wsB } } ⋆ R) mB

private def DefragExtractInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (wvec1 : List (BitVec 32)) (n : Nat) : Tup Val [i64] → Mem 64 → Prop
  | (e, ()), mE =>
    e.toNat < n ∧ ∃ wsE : List (BitVec 32),
      wsE.length = 2 * c.max_vars ∧
      WsCovers wsE n (2 * s.core.cur_vars) (fullWatchSize s) ∧
      FullWsortMaxHeap wvec1 wsE 0 (e.toNat + 1) ∧
      SplitLe (fullWvecOff wvec1) wsE (e.toNat + 1) n ∧
      SortedRange (fullWvecOff wvec1) wsE (e.toNat + 1) n ∧
      (FullMem c { s with core := { s.core with wvec := wvec1 },
                          scratch := { s.scratch with wsort := wsE } } ⋆ R) mE

local macro "m6_tiny_simp" : tactic =>
  `(tactic| simp only [
      LeanQbe.T.op1_eq_mk, LeanQbe.T.op2_eq_mk,
      LeanQbe.T.wp_let_add_eq, LeanQbe.T.wp_let_mul_eq, LeanQbe.T.wp_let_sub_eq,
      LeanQbe.T.wp_let_sext_eq, LeanQbe.T.wp_let_cmp_eq,
      LeanQbe.T.OpCode.ugt, LeanQbe.T.vals_nil, LeanQbe.T.vals_cons,
      LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm,
      LeanQbe.T.Ty.hasFloat_vec, LeanQbe.T.Ty.hasFloat, LeanQbe.T.Ty.isFloatTree,
      LeanQbe.T.evalBits_ugt_eq, LeanQbe.T.lift1, LeanQbe.T.lift2, LeanQbe.T.liftCmp,
      cast_eq, BitVec.reduceSignExtend, BitVec.reduceMul, BitVec.reduceAdd, BitVec.reduceSub])

local macro "m6_tiny_lets" : tactic =>
  `(tactic| try repeat (first | (m6_strip; try m6_tiny_simp) | m6_tiny_simp))

private theorem defrag_scan_step_cov {ws1 : List (BitVec 32)} {n l : Nat} {sz : Nat → Nat}
    {w : BitVec 32} (hw : w.toNat = l) (hcov1 : WsCovers ws1 n l sz)
    (hn_lt : n < ws1.length) (hszp : 0 < sz l) :
    WsCovers (ws1.set n w) (n + 1) (l + 1) sz := by
  have hws_at : ∀ k, wsVal (ws1.set n w) k = if k = n then l else wsVal ws1 k := fun k => by
    unfold wsVal; by_cases hk : k = n
    · subst hk; rw [List.getElem?_set_self hn_lt, Option.getD_some, hw]; simp
    · rw [List.getElem?_set_ne (Ne.symm hk)]; simp [hk]
  refine ⟨fun i hi => by
      rw [hws_at]; split
      · exact ⟨Nat.lt_succ_self l, hszp⟩
      · have := hcov1.1 i (by omega); exact ⟨by omega, this.2⟩,
    fun a ha b hb hab => by
      rw [hws_at, hws_at]; split <;> split
      · omega
      · have := (hcov1.1 b (by omega)).1; omega
      · have := (hcov1.1 a (by omega)).1; omega
      · exact hcov1.2.1 a (by omega) b (by omega) hab,
    fun j hj hzj => by
      by_cases hjl : j = l
      · subst hjl; exact ⟨n, by omega, by rw [hws_at]; simp⟩
      · obtain ⟨i, hi, hij⟩ := hcov1.2.2 j (by omega) hzj
        exact ⟨i, by omega, by rw [hws_at]; simp [show i ≠ n by omega]; exact hij⟩⟩

private theorem defrag_scan_step_sorted {ws1 : List (BitVec 32)} {key : Nat → Nat}
    {n l prev_off : Nat} {w : BitVec 32} (hw : w.toNat = l) (hn_lt : n < ws1.length)
    {sorted : Bool}
    (hsrt1 : sorted = true → SortedRange key ws1 0 n ∧ ∀ j < n, key (wsVal ws1 j) ≤ prev_off)
    (hge_prev : prev_off ≤ key l) (hs_old : sorted = true) :
    SortedRange key (ws1.set n w) 0 (n + 1) ∧ ∀ j < n + 1, key (wsVal (ws1.set n w) j) ≤ key l := by
  have hws_at : ∀ k, wsVal (ws1.set n w) k = if k = n then l else wsVal ws1 k := fun k => by
    unfold wsVal; by_cases hk : k = n
    · subst hk; rw [List.getElem?_set_self hn_lt, Option.getD_some, hw]; simp
    · rw [List.getElem?_set_ne (Ne.symm hk)]; simp [hk]
  obtain ⟨hsrt_old, hprev_old⟩ := hsrt1 hs_old
  refine ⟨fun a b ha hab hb => ?_, fun j hj => ?_⟩
  · rw [hws_at, hws_at]
    by_cases han : a = n <;> by_cases hbn : b = n
    · subst han hbn; simp
    · omega
    · subst hbn; simp only [han, ↓reduceIte]
      exact Nat.le_trans (hprev_old a (by omega)) hge_prev
    · simp only [han, hbn, ↓reduceIte]; exact hsrt_old a b ha hab (by omega)
  · rw [hws_at]; by_cases hjn : j = n
    · subst hjn; simp only [↓reduceIte]; exact Nat.le_refl _
    · simp only [hjn, ↓reduceIte]; exact Nat.le_trans (hprev_old j (by omega)) hge_prev

private theorem defrag_compact_copy_inv {s : FullState} {wvecC wstkK wsort2 : List (BitVec 32)}
    {p i n : Nat} {pv : BitVec 32} {wstkC : List (BitVec 32)}
    (hi_lt : i < n) (hp1 : 1 ≤ p) (hpv : pv.toNat = p)
    (hcov2 : WsCovers wsort2 n (2 * s.core.cur_vars) (fullWatchSize s))
    (hlay : WatchStackLayout s.core) (hsrt2 : SortedRange (fullWatchOff s) wsort2 0 n)
    (hwv_lt : 2 * wsVal wsort2 i < wvecC.length)
    (hszC : ∀ j < 2 * s.core.cur_vars, (wvecC[2 * j + 1]?.getD 0#32).toNat = fullWatchSize s j)
    (hzeroC : ∀ j < 2 * s.core.cur_vars, fullWatchSize s j = 0 →
      (wvecC[2 * j]?.getD 0#32).toNat = 0)
    (hdoneC : ∀ j < i,
      let l := wsVal wsort2 j
      let off := (wvecC[2 * l]?.getD 0#32).toNat
      1 ≤ off ∧ off + fullWatchSize s l ≤ p ∧
        ∀ k < fullWatchSize s l, wstkC[off + k]? = s.core.wstk[fullWatchOff s l + k]?)
    (hdisjC : ∀ a < i, ∀ b < i, a ≠ b →
      let la := wsVal wsort2 a
      let lb := wsVal wsort2 b
      (wvecC[2 * la]?.getD 0#32).toNat + fullWatchSize s la ≤
        (wvecC[2 * lb]?.getD 0#32).toNat ∨
      (wvecC[2 * lb]?.getD 0#32).toNat + fullWatchSize s lb ≤
        (wvecC[2 * la]?.getD 0#32).toNat)
    (hremC : ∀ j, i ≤ j → j < n →
      let l := wsVal wsort2 j
      (wvecC[2 * l]?.getD 0#32).toNat = fullWatchOff s l ∧
        ∀ k < fullWatchSize s l, wstkC[fullWatchOff s l + k]? = s.core.wstk[fullWatchOff s l + k]?)
    (hpreK : ∀ idx < p, wstkK[idx]? = wstkC[idx]?)
    (hpostK : ∀ idx, fullWatchOff s (wsVal wsort2 i) + fullWatchSize s (wsVal wsort2 i) ≤ idx →
      wstkK[idx]? = wstkC[idx]?)
    (hcopK : ∀ r < fullWatchSize s (wsVal wsort2 i),
      wstkK[p + r]? = s.core.wstk[fullWatchOff s (wsVal wsort2 i) + r]?) :
    let wvecD := wvecC.set (2 * wsVal wsort2 i) pv
    (∀ j < 2 * s.core.cur_vars, (wvecD[2 * j + 1]?.getD 0#32).toNat = fullWatchSize s j) ∧
    (∀ j < 2 * s.core.cur_vars, fullWatchSize s j = 0 →
      (wvecD[2 * j]?.getD 0#32).toNat = 0) ∧
    (∀ j < i + 1,
      let l := wsVal wsort2 j
      let off := (wvecD[2 * l]?.getD 0#32).toNat
      1 ≤ off ∧ off + fullWatchSize s l ≤ p + fullWatchSize s (wsVal wsort2 i) ∧
        ∀ k < fullWatchSize s l, wstkK[off + k]? = s.core.wstk[fullWatchOff s l + k]?) ∧
    (∀ a < i + 1, ∀ b < i + 1, a ≠ b →
      let la := wsVal wsort2 a
      let lb := wsVal wsort2 b
      (wvecD[2 * la]?.getD 0#32).toNat + fullWatchSize s la ≤
        (wvecD[2 * lb]?.getD 0#32).toNat ∨
      (wvecD[2 * lb]?.getD 0#32).toNat + fullWatchSize s lb ≤
        (wvecD[2 * la]?.getD 0#32).toNat) ∧
    (∀ j, i + 1 ≤ j → j < n →
      let l := wsVal wsort2 j
      (wvecD[2 * l]?.getD 0#32).toNat = fullWatchOff s l ∧
        ∀ k < fullWatchSize s l,
          wstkK[fullWatchOff s l + k]? = s.core.wstk[fullWatchOff s l + k]?) := by
  have hlit_info := hcov2.1 i hi_lt
  have hset := wvec_set_even_eq (wvec := wvecC) (l := wsVal wsort2 i) (v := pv) hwv_lt
  refine ⟨fun j hj => by rw [(hset j).1]; exact hszC j hj,
    fun j hj hzj => by
      have hne : j ≠ wsVal wsort2 i := fun heq => by subst heq; have := hlit_info.2; omega
      rw [(hset j).2.1 hne]; exact hzeroC j hj hzj,
    fun j hj => ?_, fun a ha b hb hab => ?_, fun j hj1 hj2 => ?_⟩
  · dsimp only; by_cases hji : j = i
    · subst j; rw [(hset 0).2.2, Option.getD_some, hpv]
      exact ⟨hp1, Nat.le_refl _, fun r hr => hcopK r hr⟩
    · have hne := hcov2.2.1 j (by omega) i hi_lt hji
      rw [(hset _).2.1 hne]; have hd := hdoneC j (by omega)
      exact ⟨hd.1, Nat.le_trans hd.2.1 (Nat.le_add_right _ _),
        fun r hr => by rw [hpreK _ (by omega)]; exact hd.2.2 r hr⟩
  · dsimp only; by_cases hai : a = i
    · subst a; have hne := hcov2.2.1 b (by omega) i hi_lt (by omega)
      rw [(hset 0).2.2, (hset _).2.1 hne, Option.getD_some, hpv]
      exact Or.inr (hdoneC b (by omega)).2.1
    · by_cases hbi : b = i
      · subst b; have hne := hcov2.2.1 a (by omega) i hi_lt (by omega)
        rw [(hset 0).2.2, (hset _).2.1 hne, Option.getD_some, hpv]
        exact Or.inl (hdoneC a (by omega)).2.1
      · have hna := hcov2.2.1 a (by omega) i hi_lt hai
        have hnb := hcov2.2.1 b (by omega) i hi_lt hbi
        rw [(hset _).2.1 hna, (hset _).2.1 hnb]
        exact hdisjC a (by omega) b (by omega) hab
  · dsimp only; have hne := hcov2.2.1 j hj2 i hi_lt (by omega)
    rw [(hset _).2.1 hne]
    have hgap := defrag_sorted_gap hlay hcov2 hsrt2 (i := i) (j := j) (by omega) hj2
    have hr := hremC j (by omega) hj2
    exact ⟨hr.1, fun r hr' => by rw [hpostK _ (by omega)]; exact hr.2 r hr'⟩

private theorem defrag_extract_done {s : FullState} {wvec1 wsE : List (BitVec 32)} {n : Nat}
    (hoff1 : ∀ j < 2 * s.core.cur_vars, 0 < fullWatchSize s j →
      wvec1[2 * j]? = s.core.wvec[2 * j]?)
    (hcovE : WsCovers wsE n (2 * s.core.cur_vars) (fullWatchSize s))
    (hspE : SplitLe (fullWvecOff wvec1) wsE 1 n)
    (hsrtE : SortedRange (fullWvecOff wvec1) wsE 1 n) :
    SortedRange (fullWatchOff s) wsE 0 n := by
  intro i j hi hij hj
  have hkey_eq : ∀ k < n, fullWvecOff wvec1 (wsVal wsE k) = fullWatchOff s (wsVal wsE k) :=
    fun k hk => by
      have := hcovE.1 k hk; unfold fullWvecOff fullWatchOff fullWatchOffCore
      rw [hoff1 _ this.1 this.2]
  rw [← hkey_eq i (by omega), ← hkey_eq j hj]
  rcases Nat.eq_zero_or_pos i with rfl | hip
  · rcases Nat.eq_zero_or_pos j with rfl | hjp
    · exact Nat.le_refl _
    · exact hspE 0 (by omega) j (by omega) hj
  · exact hsrtE i j (by omega) hij hj

private theorem defrag_scan_zero_inv {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {n l max_off prev_off : BitVec 64} {sorted : Bool}
    {wvec1 wsort1 : List (BitVec 32)} {m : Mem 64}
    (hl_lt : l.toNat < 2 * s.core.cur_vars) (hn_le : n.toNat ≤ l.toNat)
    (hmax_le : max_off.toNat ≤ c.wcap) (hprev_le : prev_off.toNat ≤ max_off.toNat)
    (hwv1 : wvec1.length = 4 * c.max_vars) (hws1 : wsort1.length = 2 * c.max_vars)
    (hsz1 : ∀ j < 2 * s.core.cur_vars, wvec1[2 * j + 1]? = s.core.wvec[2 * j + 1]?)
    (hoff1 : ∀ j < 2 * s.core.cur_vars, 0 < fullWatchSize s j → wvec1[2 * j]? = s.core.wvec[2 * j]?)
    (hzero1 : ∀ j < l.toNat, fullWatchSize s j = 0 → wvec1[2 * j]? = some 0#32)
    (hcov1 : WsCovers wsort1 n.toNat l.toNat (fullWatchSize s))
    (hmax_elt : ∀ j < n.toNat, fullWatchOff s (wsVal wsort1 j) ≤ max_off.toNat)
    (hsrt1 : sorted = true → SortedRange (fullWatchOff s) wsort1 0 n.toNat ∧
      ∀ j < n.toNat, fullWatchOff s (wsVal wsort1 j) ≤ prev_off.toNat)
    (hsz0 : fullWatchSize s l.toNat = 0)
    (hl2 : (l <<< (1 : Nat)).toNat = 2 * l.toNat)
    (hlp1 : (l + 1).toNat = l.toNat + 1)
    (hset : ∀ j, (wvec1.set (l <<< (1 : Nat)).toNat 0#32)[2 * j + 1]? = wvec1[2 * j + 1]? ∧
      (j ≠ l.toNat → (wvec1.set (l <<< (1 : Nat)).toNat 0#32)[2 * j]? = wvec1[2 * j]?) ∧
      (wvec1.set (2 * l.toNat) 0#32)[2 * l.toNat]? = some 0#32)
    (hm : (FullMem c { s with
        core := { s.core with wvec := wvec1.set (l <<< (1 : Nat)).toNat 0#32 },
        scratch := { s.scratch with wsort := wsort1 } } ⋆ R) m) :
    DefragScanInv c s R (n, l + 1, max_off, prev_off, sorted, ()) m :=
  ⟨by omega, by omega, hmax_le, hprev_le, _, wsort1, by rw [List.length_set, hwv1], hws1,
   fun j hj => (hset j).1.trans (hsz1 j hj),
   fun j hj hp => ((hset j).2.1 fun heq => by subst heq; omega).trans (hoff1 j hj hp),
   fun j hj hzj => by
     by_cases hjl : j = l.toNat
     · subst hjl; rw [hl2]; exact (hset l.toNat).2.2
     · exact ((hset j).2.1 hjl).trans (hzero1 j (by omega) hzj),
   ⟨fun i hi => ⟨by have := (hcov1.1 i hi).1; omega, (hcov1.1 i hi).2⟩, hcov1.2.1,
    fun j hj hzj => hcov1.2.2 j
      (if hjl : j = l.toNat then by subst hjl; omega else by omega) hzj⟩,
   hmax_elt, hsrt1, hm⟩

private theorem defrag_scan_pos_inv {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {n l max_off prev_off : BitVec 64} {sorted : Bool}
    {wvec1 wsort1 : List (BitVec 32)} {off64 : BitVec 64} {m : Mem 64}
    (hl_lt : l.toNat < 2 * s.core.cur_vars) (hn_le : n.toNat ≤ l.toNat)
    (hmax_le : max_off.toNat ≤ c.wcap) (_hprev_le : prev_off.toNat ≤ max_off.toNat)
    (hwv1 : wvec1.length = 4 * c.max_vars) (hws1 : wsort1.length = 2 * c.max_vars)
    (hn_ws_len : n.toNat < wsort1.length)
    (hsz1 : ∀ j < 2 * s.core.cur_vars, wvec1[2 * j + 1]? = s.core.wvec[2 * j + 1]?)
    (hoff1 : ∀ j < 2 * s.core.cur_vars, 0 < fullWatchSize s j → wvec1[2 * j]? = s.core.wvec[2 * j]?)
    (hzero1 : ∀ j < l.toNat, fullWatchSize s j = 0 → wvec1[2 * j]? = some 0#32)
    (hcov1 : WsCovers wsort1 n.toNat l.toNat (fullWatchSize s))
    (hmax_elt : ∀ j < n.toNat, fullWatchOff s (wsVal wsort1 j) ≤ max_off.toNat)
    (hsrt1 : sorted = true → SortedRange (fullWatchOff s) wsort1 0 n.toNat ∧
      ∀ j < n.toNat, fullWatchOff s (wsVal wsort1 j) ≤ prev_off.toNat)
    (hszp : 0 < fullWatchSize s l.toNat) (hoff_le_cap : fullWatchOff s l.toNat ≤ c.wcap)
    (hoff64_nat : off64.toNat = fullWatchOff s l.toNat)
    (hlp1 : (l + 1).toNat = l.toNat + 1) (hnp1 : (n + 1).toNat = n.toNat + 1)
    (htr : (l.setWidth 32).toNat = l.toNat)
    (hm : (FullMem c { s with core := { s.core with wvec := wvec1 },
                              scratch := { s.scratch with
                                wsort := wsort1.set n.toNat (l.setWidth 32) } } ⋆ R) m) :
    let new_sorted := if off64.ult prev_off then false else sorted
    let new_max := if max_off.ult off64 then off64 else max_off
    DefragScanInv c s R (n + 1, l + 1, new_max, off64, new_sorted, ()) m := by
  have hws_at : ∀ k, wsVal (wsort1.set n.toNat (l.setWidth 32)) k =
      if k = n.toNat then l.toNat else wsVal wsort1 k := fun k => by
    unfold wsVal; by_cases hk : k = n.toNat
    · subst hk; rw [List.getElem?_set_self hn_ws_len, Option.getD_some, htr]; simp
    · rw [List.getElem?_set_ne (Ne.symm hk)]; simp [hk]
  refine ⟨by omega, by omega, ?_, ?_, wvec1, wsort1.set n.toNat (l.setWidth 32), hwv1,
    by rw [List.length_set, hws1], hsz1, hoff1,
    fun j hj hzj => hzero1 j (if hjl : j = l.toNat then by subst hjl; omega else by omega) hzj,
    by rw [hlp1, hnp1]; exact defrag_scan_step_cov htr hcov1 hn_ws_len hszp,
    fun j hj => ?_, fun hns => ?_, hm⟩
  · split
    · rw [hoff64_nat]; exact hoff_le_cap
    · exact hmax_le
  · split
    · rw [hoff64_nat]; exact Nat.le_refl _
    · next hult =>
      by_cases hgt : off64.toNat ≤ max_off.toNat
      · exact hgt
      · exfalso; apply hult; simp only [BitVec.ult, decide_eq_true_eq]; omega
  · rw [hws_at]
    by_cases hjn : j = n.toNat
    · subst hjn; simp only [↓reduceIte]; split
      · rw [hoff64_nat]; exact Nat.le_refl _
      · next hult =>
        have hle : off64.toNat ≤ max_off.toNat := by
          by_cases hgt : off64.toNat ≤ max_off.toNat
          · exact hgt
          · exfalso; apply hult; simp only [BitVec.ult, decide_eq_true_eq]; omega
        rwa [hoff64_nat] at hle
    · simp only [hjn, ↓reduceIte]
      have h1 := hmax_elt j (by omega)
      split
      · next hult =>
        have hlt : max_off.toNat < off64.toNat := by simpa [BitVec.ult] using hult
        omega
      · exact h1
  · have hs_t : sorted = true ∧ ¬ (off64.toNat < prev_off.toNat) := by
      by_cases hult : off64.ult prev_off = true
      · simp [hult] at hns
      · simp only [hult, Bool.false_eq_true, ↓reduceIte] at hns
        exact ⟨hns, fun hlt => hult (by simpa [BitVec.ult] using hlt)⟩
    rw [hnp1, hoff64_nat]
    exact defrag_scan_step_sorted htr hn_ws_len hsrt1 (by rw [← hoff64_nat]; omega) hs_t.1

private theorem defrag_compact_keep_inv {s : FullState} {wvecC wstkC wsort2 : List (BitVec 32)}
    {p i n : Nat}
    (hp1 : 1 ≤ p) (hi_lt : i < n)
    (hdoneC : ∀ j < i,
      let l := wsVal wsort2 j; let off := (wvecC[2 * l]?.getD 0#32).toNat
      1 ≤ off ∧ off + fullWatchSize s l ≤ p ∧
      ∀ k < fullWatchSize s l, wstkC[off + k]? = s.core.wstk[fullWatchOff s l + k]?)
    (hdisjC : ∀ a < i, ∀ b < i, a ≠ b →
      let la := wsVal wsort2 a; let lb := wsVal wsort2 b
      (wvecC[2 * la]?.getD 0#32).toNat + fullWatchSize s la ≤
        (wvecC[2 * lb]?.getD 0#32).toNat ∨
      (wvecC[2 * lb]?.getD 0#32).toNat + fullWatchSize s lb ≤
        (wvecC[2 * la]?.getD 0#32).toNat)
    (hremC : ∀ j, i ≤ j → j < n →
      let l := wsVal wsort2 j
      (wvecC[2 * l]?.getD 0#32).toNat = fullWatchOff s l ∧
      ∀ k < fullWatchSize s l, wstkC[fullWatchOff s l + k]? = s.core.wstk[fullWatchOff s l + k]?)
    (hoff_eq_p : fullWatchOff s (wsVal wsort2 i) = p) :
    (∀ j < i + 1,
      let l := wsVal wsort2 j; let off := (wvecC[2 * l]?.getD 0#32).toNat
      1 ≤ off ∧ off + fullWatchSize s l ≤ p + fullWatchSize s (wsVal wsort2 i) ∧
      ∀ k < fullWatchSize s l, wstkC[off + k]? = s.core.wstk[fullWatchOff s l + k]?) ∧
    (∀ a < i + 1, ∀ b < i + 1, a ≠ b →
      let la := wsVal wsort2 a; let lb := wsVal wsort2 b
      (wvecC[2 * la]?.getD 0#32).toNat + fullWatchSize s la ≤
        (wvecC[2 * lb]?.getD 0#32).toNat ∨
      (wvecC[2 * lb]?.getD 0#32).toNat + fullWatchSize s lb ≤
        (wvecC[2 * la]?.getD 0#32).toNat) := by
  refine ⟨fun j hj => ?_, fun a ha b hb hab => ?_⟩
  · dsimp only; by_cases hji : j = i
    · subst j; have hr := hremC i (by omega) hi_lt; rw [hr.1, hoff_eq_p]
      exact ⟨hp1, by omega, fun r hr' => by rw [← hoff_eq_p]; exact hr.2 r hr'⟩
    · have hd := hdoneC j (by omega); exact ⟨hd.1, by omega, hd.2.2⟩
  · dsimp only; by_cases hai : a = i
    · subst a; rw [(hremC i (by omega) hi_lt).1, hoff_eq_p]
      exact Or.inr (hdoneC b (by omega)).2.1
    · by_cases hbi : b = i
      · subst b; rw [(hremC i (by omega) hi_lt).1, hoff_eq_p]
        exact Or.inl (hdoneC a (by omega)).2.1
      · exact hdisjC a (by omega) b (by omega) hab

private theorem defrag_branch1_done {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {wvec1 wsort1 ws' tmp' cnt' : List (BitVec 32)} {n : Nat} {m' : Mem 64}
    (hlen1 : FullState.LengthsOk c { s with
        core := { s.core with wvec := wvec1 },
        scratch := { s.scratch with wsort := wsort1 } })
    (hwsl : s.core.wstk.length = c.wcap)
    (hoff1 : ∀ j < 2 * s.core.cur_vars, 0 < fullWatchSize s j → wvec1[2 * j]? = s.core.wvec[2 * j]?)
    (hcov1 : WsCovers wsort1 n (2 * s.core.cur_vars) (fullWatchSize s))
    (h2n_le : 2 * n + 256 ≤ 2 * c.max_vars)
    (hws' : ws'.length = n) (htmp' : tmp'.length = n) (hcnt' : cnt'.length = 256)
    (hperm' : (wsort1.take n).Perm ws')
    (hsrt' : SortedRange (fullWvecOff wvec1) ws' 0 n)
    (hm' : (array (t := i32) c.pWvec wvec1 ⋆ array (t := i32) c.pWsort ws' ⋆
      array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * n)) tmp' ⋆
      array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * (2 * n))) cnt' ⋆
      (array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * (2 * n + 256)))
        (wsort1.drop (2 * n + 256)) ⋆
        FullWvecWsortRest c { s with
          core := { s.core with wvec := wvec1 },
          scratch := { s.scratch with wsort := wsort1 } } ⋆ R)) m') :
    DefragSortPost c s R wvec1 n () m' := by
  have hws1 : wsort1.length = 2 * c.max_vars := hlen1.scratch_ok.wsort_len
  have hrec := full_wvec_wsort_unsplit3 hlen1 h2n_le hws' htmp' hcnt' hm'
  have hcov' : WsCovers (ws' ++ tmp' ++ cnt' ++ wsort1.drop (2 * n + 256))
      n (2 * s.core.cur_vars) (fullWatchSize s) :=
    wsCovers_of_perm_prefix hcov1 (by omega) (by rw [hrec.1]; omega)
      (by rw [hrec.2.1]; exact hperm'.symm)
  have hsrt_fin : SortedRange (fullWatchOff s)
      (ws' ++ tmp' ++ cnt' ++ wsort1.drop (2 * n + 256)) 0 n := by
    intro i j hi hij hj
    have hki := hcov'.1 i (by omega); have hkj := hcov'.1 j hj
    unfold fullWatchOff fullWatchOffCore
    rw [← hoff1 _ hki.1 hki.2, ← hoff1 _ hkj.1 hkj.2]
    have hv (k : Nat) (hk : k < n) :
        wsVal (ws' ++ tmp' ++ cnt' ++ wsort1.drop (2 * n + 256)) k = wsVal ws' k := by
      unfold wsVal; rw [List.append_assoc, List.append_assoc,
        List.getElem?_append_left (by rw [hws']; exact hk)]
    rw [hv i (by omega), hv j hj]; exact hsrt' i j hi hij hj
  exact ⟨s.core.wstk, _, hwsl, hrec.1, fun _ _ => rfl, hcov', hsrt_fin, hrec.2.2⟩

private theorem defrag_branch2_done {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {wvec1 wsort1 ws' tmp' cnt' : List (BitVec 32)} {n : Nat} {m' : Mem 64}
    (hlen1 : FullState.LengthsOk c { s with
        core := { s.core with wvec := wvec1 },
        scratch := { s.scratch with wsort := wsort1 } })
    (hoff1 : ∀ j < 2 * s.core.cur_vars, 0 < fullWatchSize s j → wvec1[2 * j]? = s.core.wvec[2 * j]?)
    (hcov1 : WsCovers wsort1 n (2 * s.core.cur_vars) (fullWatchSize s))
    (hn_ws : n ≤ 2 * c.max_vars) (hcap_le : s.core.wlen + n + 256 ≤ c.wcap)
    (hws' : ws'.length = n) (htmp' : tmp'.length = n) (hcnt' : cnt'.length = 256)
    (hperm' : (wsort1.take n).Perm ws')
    (hsrt' : SortedRange (fullWvecOff wvec1) ws' 0 n)
    (hm' : (array (t := i32) c.pWvec wvec1 ⋆ array (t := i32) c.pWsort ws' ⋆
      array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * s.core.wlen)) tmp' ⋆
      array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * (s.core.wlen + n))) cnt' ⋆
      (array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * n)) (wsort1.drop n) ⋆
       array (t := i32) c.pWstk (s.core.wstk.take s.core.wlen) ⋆
       array (t := i32) (c.pWstk + BitVec.ofNat 64 (4 * (s.core.wlen + n + 256)))
         (s.core.wstk.drop (s.core.wlen + n + 256)) ⋆
       FullWvecWsortWstkRest c { s with
         core := { s.core with wvec := wvec1 },
         scratch := { s.scratch with wsort := wsort1 } } ⋆ R)) m') :
    DefragSortPost c s R wvec1 n () m' := by
  have hws1 : wsort1.length = 2 * c.max_vars := hlen1.scratch_ok.wsort_len
  have hrec := full_wstack_defrag_wstk_unsplit hlen1 hn_ws hcap_le hws' htmp' hcnt' hm'
  have hcov' : WsCovers (ws' ++ wsort1.drop n) n (2 * s.core.cur_vars) (fullWatchSize s) :=
    wsCovers_of_perm_prefix hcov1 (by omega) (by rw [hrec.1]; omega)
      (by rw [hrec.2.2.1]; exact hperm'.symm)
  have hsrt_fin : SortedRange (fullWatchOff s) (ws' ++ wsort1.drop n) 0 n := by
    intro i j hi hij hj
    have hki := hcov'.1 i (by omega); have hkj := hcov'.1 j hj
    unfold fullWatchOff fullWatchOffCore
    rw [← hoff1 _ hki.1 hki.2, ← hoff1 _ hkj.1 hkj.2]
    have hv (k : Nat) (hk : k < n) : wsVal (ws' ++ wsort1.drop n) k = wsVal ws' k := by
      unfold wsVal; rw [List.getElem?_append_left (by rw [hws']; exact hk)]
    rw [hv i (by omega), hv j hj]; exact hsrt' i j hi hij hj
  exact ⟨_, _, hrec.2.1, hrec.1, hrec.2.2.2.1, hcov', hsrt_fin, hrec.2.2.2.2⟩

private theorem defrag_extract_next {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {wvec1 wsE ws' : List (BitVec 32)} {e n : Nat} {e_bv : BitVec 64}
    {h0 : 0 < wsE.length} {he_len : e < wsE.length} {m' : Mem 64}
    (hn_le : n ≤ 2 * c.max_vars) (he_pos : 0 < e) (he_lt : e < n)
    (_he_nat : e_bv.toNat = e) (hem1 : (e_bv - 1).toNat = e - 1)
    (hwsE : wsE.length = 2 * c.max_vars)
    (hws' : ws'.length = ((wsE.set 0 (wsE[e]'he_len)).set e (wsE[0]'h0)).length)
    (hmaxE : FullWsortMaxHeap wvec1 wsE 0 (e + 1))
    (hspE : SplitLe (fullWvecOff wvec1) wsE (e + 1) n)
    (hsrtE : SortedRange (fullWvecOff wvec1) wsE (e + 1) n)
    (hcovE : WsCovers wsE n (2 * s.core.cur_vars) (fullWatchSize s))
    (hperm' : ws'.Perm ((wsE.set 0 (wsE[e]'he_len)).set e (wsE[0]'h0)))
    (hsuf' : ∀ i, i < 0 ∨ e ≤ i →
      ws'[i]? = ((wsE.set 0 (wsE[e]'he_len)).set e (wsE[0]'h0))[i]?)
    (hmax' : FullWsortMaxHeap wvec1 ws' 0 e)
    (hm' : (FullMem c { s with
        core := { s.core with wvec := wvec1 },
        scratch := { s.scratch with wsort := ws' } } ⋆ R) m') :
    DefragExtractInv c s R wvec1 n (e_bv - 1, ()) m' := by
  have hsw_step := wsort_extract_swap_step hmaxE hspE hsrtE he_pos he_lt (by omega)
  have hsw_cov := wsCovers_swap hcovE (i := 0) (j := e) (by omega) he_lt (by omega)
  let wsSwap := (wsE.set 0 (wsE[e]'he_len)).set e (wsE[0]'h0)
  have hlen_sw : n ≤ wsSwap.length := by
    rw [List.length_set, List.length_set, hwsE]; exact hn_le
  have hcov' := wsCovers_of_perm_suffix hsw_cov hws' hlen_sw hperm' fun i hi =>
    hsuf' i (Or.inr (Nat.le_trans (Nat.le_of_lt he_lt) hi))
  have hperm_ps := wsort_extract_perm_post (e := e) (n := n) (wvec := wvec1) hws'
    (by omega) hlen_sw hperm' (fun i hi => hsuf' i (Or.inr hi)) hsw_step.2.1 hsw_step.2.2
  have hep : (e_bv - 1).toNat + 1 = e := by rw [hem1]; omega
  refine ⟨by rw [hem1]; omega, ws', by rw [hws']; simp [hwsE], hcov',
    by rw [hep]; exact hmax', by rw [hep]; exact hperm_ps.1, by rw [hep]; exact hperm_ps.2, hm'⟩

theorem full_wstack_defrag_m6_wp (Γ : Env)
    (hSift : ∀ a m Q X, fullWsortSiftSpec a m Q X →
      Γ "full_wsort_sift" [i64, i64, i64, i64] [] a m Q X)
    (hRadix : ∀ a m Q X, fullWstackRadixSortSpec a m Q X →
      Γ "full_wstack_radix_sort_m6" [i64, i64, i64, i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Func.wp Γ full_wstack_defrag_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlay, hm, hQ⟩
  have hcl := hlen.core_ok; have hsl := hlen.scratch_ok
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv; unfold dimacsBound at hmx
  have hwcap : c.wcap < 2 * dimacsBound := c.hwcap; unfold dimacsBound at hwcap
  have hcv_le := hcl.cur_vars_le
  have hwle := hcl.wlen_le; have hwvl := hcl.wvec_len; have hwsl := hcl.wstk_len_arr
  have hwsrt_l := hsl.wsort_len
  m6_steps
  · refine hQ s.core.wvec s.core.wstk s.core.wlen s.scratch.wsort _
      ⟨{ hcl with wlen_le := hwle }, hsl⟩
      (hlay.with_wstk rfl rfl rfl rfl) id (fun _ _ => ⟨rfl, fun _ _ => rfl⟩) hm
  · have hwlen_gt1 : 1 < s.core.wlen := by c0_bound
    have hwsl_pos : 0 < s.core.wstk.length := by omega
    have hnlits : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
      rw [BitVec.toNat_shiftLeft, bv64_ofNat_toNat_id (by omega)]
      simp [Nat.shiftLeft_eq]; omega
    clear hc
    refine wp_loop_inv (DefragScanInv c s R)
      (fun (_, l, _, _, _, ()) _ => 2 * s.core.cur_vars - l.toNat)
      (fun J hLoop => ?_) ?_
    · m6_steps
      refine hLoop _ _ ⟨by simp, by simp, by simp, by simp, s.core.wvec, s.scratch.wsort,
        hwvl, hwsrt_l, fun _ _ => rfl, fun _ _ _ => rfl, fun _ hj => by simp at hj,
        ⟨fun _ hi => by simp at hi, fun _ hi => by simp at hi, fun _ hl => by simp at hl⟩,
        fun _ hi => by simp at hi, fun _ => ⟨fun _ _ _ _ hj => by simp at hj,
          fun _ hi => by simp at hi⟩, hm⟩
    · rintro J ⟨n, l, max_off, prev_off, sorted, ⟨⟩⟩ m1
        ⟨hl_le, hn_le, hmax_le, hprev_le, wvec1, wsort1, hwv1, hws1,
         hsz1, hoff1, hzero1, hcov1, hmax_elt, hsrt1, hm1⟩ hLoop
      clear hm
      m6_split
      · have hl_lt : l.toNat < 2 * s.core.cur_vars := by
          have : l.toNat < (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat := by c0_bound
          omega
        have hl2 : (l <<< (1 : Nat)).toNat = 2 * l.toNat := by
          rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
        have hl2p1 : ((l <<< (1 : Nat)) + 1).toNat = 2 * l.toNat + 1 := by
          rw [BitVec.toNat_add, hl2]; simp; omega
        have hl2_lt : (l <<< (1 : Nat)).toNat < wvec1.length := by omega
        have hl2p1_lt : ((l <<< (1 : Nat)) + 1).toNat < wvec1.length := by omega
        have hsz_eq : (wvec1[((l <<< (1 : Nat)) + 1).toNat]'hl2p1_lt).toNat =
            fullWatchSize s l.toNat := by
          unfold fullWatchSize fullWatchSizeCore
          have h1 := hsz1 l.toNat hl_lt; rw [← h1]
          have h2 : wvec1[((l <<< (1 : Nat)) + 1).toNat]'hl2p1_lt =
              wvec1[2 * l.toNat + 1]'(by omega) := by congr 1
          rw [h2, List.getElem?_eq_getElem (by omega), Option.getD_some]
        m6_split
        · have hsz0 : fullWatchSize s l.toNat = 0 := by
            have hix : (l.toNat * 2 + 1) % 2 ^ 64 = 2 * l.toNat + 1 := by omega
            have h1 : (wvec1[(l.toNat * 2 + 1) % 2 ^ 64]'(by omega)).toNat =
                fullWatchSize s l.toNat := by
              rw [fi_list_getElem_toNat_eq (by omega) hix]
              unfold fullWatchSize fullWatchSizeCore
              rw [← hsz1 l.toNat hl_lt, List.getElem?_eq_getElem (by omega), Option.getD_some]
            have hc0 : (wvec1[(l.toNat * 2 + 1) % 2 ^ 64]'(by omega)).toNat = 0 := by
              have hc' : wvec1[(l.toNat * 2 + 1) % 2 ^ 64]'(by omega) = 0#32 := by
                have h2 : 2 * l.toNat + 1 = l.toNat * 2 + 1 := Nat.mul_comm 2 l.toNat ▸ rfl
                simpa [h2] using hc
              exact congrArg BitVec.toNat hc'
            omega
          have hset := wvec_set_even_eq (wvec := wvec1) (l := l.toNat) (v := 0#32) (by omega)
          have hlp1 : (l + 1).toNat = l.toNat + 1 := by bv_omega
          m6_c0_steps
          refine hLoop _ _ (by dsimp only; omega)
            (defrag_scan_zero_inv hl_lt hn_le hmax_le hprev_le hwv1 hws1 hsz1 hoff1 hzero1 hcov1
              hmax_elt hsrt1 hsz0 hl2 hlp1 (by simpa only [hl2] using hset) hm)
        · have hszp : 0 < fullWatchSize s l.toNat := by
            have hix : (l.toNat * 2 + 1) % 2 ^ 64 = 2 * l.toNat + 1 := by omega
            have h1 : (wvec1[(l.toNat * 2 + 1) % 2 ^ 64]'(by omega)).toNat =
                fullWatchSize s l.toNat := by
              rw [fi_list_getElem_toNat_eq (by omega) hix]
              unfold fullWatchSize fullWatchSizeCore
              rw [← hsz1 l.toNat hl_lt, List.getElem?_eq_getElem (by omega), Option.getD_some]
            rw [← h1]
            exact Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq (by
              have h2 : 2 * l.toNat + 1 = l.toNat * 2 + 1 := Nat.mul_comm 2 l.toNat ▸ rfl
              simpa [h2] using h0))
          have hoff_eq_s : (wvec1[(l <<< (1 : Nat)).toNat]'hl2_lt).toNat =
              fullWatchOff s l.toNat := by
            have h1 := hoff1 l.toNat hl_lt hszp
            unfold fullWatchOff fullWatchOffCore; rw [← h1]
            have h2 : wvec1[(l <<< (1 : Nat)).toNat]'hl2_lt =
                wvec1[2 * l.toNat]'(by omega) := by congr 1
            rw [h2, List.getElem?_eq_getElem (by omega), Option.getD_some]
          have hoff_le_cap : fullWatchOff s l.toNat ≤ c.wcap := by
            have := hlay.bounds l.toNat hl_lt
            unfold fullWatchOff fullWatchSize at *; omega
          let off64 := (wvec1[(l <<< (1 : Nat)).toNat]'hl2_lt).setWidth 64
          have hoff64_nat : off64.toNat = fullWatchOff s l.toNat := by
            rw [zext_toNat _ (by decide), hoff_eq_s]
          have hlp1 : (l + 1).toNat = l.toNat + 1 := by bv_omega
          have hnp1 : (n + 1).toNat = n.toNat + 1 := by bv_omega
          have htr : (l.setWidth 32).toNat = l.toNat := by
            rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
          have hws_at : ∀ k, wsVal (wsort1.set n.toNat (l.setWidth 32)) k =
              if k = n.toNat then l.toNat else wsVal wsort1 k := fun k => by
            unfold wsVal; by_cases hk : k = n.toNat
            · subst hk; rw [List.getElem?_set_self (by omega), Option.getD_some, htr]; simp
            · rw [List.getElem?_set_ne (by omega)]; simp [hk]
          let new_sorted := if off64.ult prev_off then false else sorted
          let new_max := if max_off.ult off64 then off64 else max_off
          m6_to_group
          refine wp_join_group (ts := [.bool])
            (fun (nsort, ()) mJ => nsort = new_sorted ∧ mJ = m1) ?_ ?_
          · rintro _ ⟨nsort, ⟨⟩⟩ mJ ⟨rfl, hmJ⟩
            rw [hmJ] at *
            m6_to_group
            refine wp_join_group (ts := [i64])
              (fun (nmax, ()) mJ2 => nmax = new_max ∧ mJ2 = m1) ?_ ?_
            · rintro _ ⟨nmax, ⟨⟩⟩ mJ2 ⟨rfl, hmJ2⟩
              rw [hmJ2] at *
              have hn_ws_len : n.toNat < wsort1.length := by omega
              m6_usteps
              apply wp_store_sep
              · exact FullArenaTactics.c0_store_full_wsort _ hn_ws_len hm1
              intro m hm; m6_c0_steps; dsimp only at hm
              exact hLoop _ _ (by dsimp only; omega)
                (defrag_scan_pos_inv hl_lt hn_le hmax_le hprev_le hwv1 hws1 hn_ws_len hsz1 hoff1
                  hzero1 hcov1 hmax_elt hsrt1 hszp hoff_le_cap hoff64_nat hlp1 hnp1 htr hm)
            · intro J2 hJ2; m6_split
              · have hult2 : max_off.ult off64 = true := by
                  simp only [BitVec.ult, decide_eq_true_eq]; rw [hoff64_nat, ← hoff_eq_s]
                  have hget : wvec1[(l <<< (1 : Nat)).toNat]'hl2_lt =
                      wvec1[2 * l.toNat % 2 ^ 64]'(by omega) := by congr 1; try omega
                  rw [hget]; exact hc
                m6_c0_steps
                exact hJ2 (off64, ()) m1 ⟨by simp [new_max, hult2], rfl⟩
              · have hult2 : max_off.ult off64 = false := by
                  simp only [BitVec.ult, decide_eq_false_iff_not]; rw [hoff64_nat, ← hoff_eq_s]
                  have hget : wvec1[(l <<< (1 : Nat)).toNat]'hl2_lt =
                      wvec1[2 * l.toNat % 2 ^ 64]'(by omega) := by congr 1; try omega
                  rw [hget]; omega
                m6_c0_steps
                exact hJ2 (max_off, ()) m1 ⟨by simp [new_max, hult2], rfl⟩
          · intro J0 hJ0; m6_split
            · have hult1 : off64.ult prev_off = true := by
                simp only [BitVec.ult, decide_eq_true_eq]; rw [hoff64_nat, ← hoff_eq_s]
                have hget : wvec1[(l <<< (1 : Nat)).toNat]'hl2_lt =
                    wvec1[2 * l.toNat % 2 ^ 64]'(by omega) := by congr 1; try omega
                rw [hget]; exact hc
              m6_c0_steps
              exact hJ0 (false, ()) m1 ⟨by simp only [new_sorted, hult1, ↓reduceIte], rfl⟩
            · have hult1 : off64.ult prev_off = false := by
                simp only [BitVec.ult, decide_eq_false_iff_not]; rw [hoff64_nat, ← hoff_eq_s]
                have hget : wvec1[(l <<< (1 : Nat)).toNat]'hl2_lt =
                    wvec1[2 * l.toNat % 2 ^ 64]'(by omega) := by congr 1; try omega
                rw [hget]; omega
              m6_c0_steps
              exact hJ0 (sorted, ()) m1
                ⟨by simp only [new_sorted, hult1, Bool.false_eq_true, ↓reduceIte], rfl⟩
      · have hl_eq : l.toNat = 2 * s.core.cur_vars := by
          have : ¬ (l.toNat < (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat) := by c0_bound
          omega
        rw [hl_eq] at hzero1 hcov1 hn_le
        m6_split
        · have hn0 : n.toNat = 0 := by rw [show n = 0#64 from by simpa using hc]; rfl
          have hfin := defrag_finalize (s := s) (wvecC := wvec1) (wstkC := s.core.wstk.set 0 0#32)
            (wsort2 := wsort1) (n := 0) (p := 1) hlay (by simpa [hn0] using hcov1) (by omega)
            (fun j hj => by have := hsz1 j hj; unfold fullWatchSize fullWatchSizeCore; rw [this])
            (fun j hj hz => by rw [hzero1 j hj hz]; rfl) (fun _ _ => by omega) (fun _ _ => by omega)
          have hm1_w : (array (t := i32) c.pWstk s.core.wstk ⋆
              (array (t := i32) c.pWvec wvec1 ⋆ (array (t := i32) c.pWsort wsort1 ⋆
                (FullWvecWsortWstkRest c s ⋆ R)))) m1 := by
            let s0' : FullState := { s with core := { s.core with wvec := wvec1 }
                                            scratch := { s.scratch with wsort := wsort1 } }
            have hrest_eq : FullWvecWsortWstkRest c s0' = FullWvecWsortWstkRest c s := rfl
            rw [fullMem_eq_wvec_wsort_wstk] at hm1; dsimp only at hm1; rw [hrest_eq] at hm1
            simp only [sep_assoc] at hm1; exact sep_rot4_front hm1
          m6_c0_steps
          have hm0_full : (FullMem c { s with
              core := { s.core with wvec := wvec1, wstk := s.core.wstk.set 0 0#32 }
              scratch := { s.scratch with wsort := wsort1 } } ⋆ R) m := by
            let s0'' : FullState := { s with
              core := { s.core with wvec := wvec1, wstk := s.core.wstk.set 0 0#32 }
              scratch := { s.scratch with wsort := wsort1 } }
            have hrest_eq : FullWvecWsortWstkRest c s0'' = FullWvecWsortWstkRest c s := rfl
            rw [fullMem_eq_wvec_wsort_wstk]; dsimp only; rw [hrest_eq]
            simp only [sep_assoc] at hm ⊢; exact sep_rot4_back hm
          m6_steps
          exact hQ wvec1 (s.core.wstk.set 0 0#32) 1 wsort1 _
            ⟨{ hcl with wvec_len := hwv1, wstk_len_arr := by simp [hwsl],
                        wlen_le := by dsimp only; omega }, { hsl with wsort_len := hws1 }⟩
            hfin.1 (fun _ => by omega) hfin.2 hm
        · have hn_pos : 0 < n.toNat :=
            Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
          clear hLoop J
          refine wp_join_group (ts := []) (DefragSortPost c s R wvec1 n.toNat) ?_ ?_
          · rintro _ _ m2 ⟨wstk2, wsort2, hwst2, hws2, hwstk_pre, hcov2, hsrt2, hm2⟩
            clear hm1 wsort1 hws1 hcov1 hmax_elt hsrt1; m6_to_group
            refine wp_loop_inv (DefragCompactInv c s R n.toNat wsort2)
              (fun (_, i, ()) _ => n.toNat - i.toNat) (fun J hLoop => ?_) ?_
            · m6_steps
              refine hLoop _ _ ⟨by simp, by simp; omega, by simp, fun h0 => ?_, wvec1, wstk2,
                hwv1, hwst2, fun j hj => by unfold fullWatchSize fullWatchSizeCore; rw [hsz1 j hj],
                fun j hj hz => by rw [hzero1 j hj hz]; rfl,
                fun _ hj => by simp at hj, fun _ ha => by simp at ha,
                fun j _ hjn => ⟨by have := hcov2.1 j hjn
                                   unfold fullWatchOff fullWatchOffCore; rw [hoff1 _ this.1 this.2],
                  fun k hk => hwstk_pre _
                    (by have := hcov2.1 j hjn; have := hlay.bounds _ this.1
                        have := hcl.wlen_le
                        dsimp only [fullWatchOff, fullWatchSize] at *; omega)⟩,
                hm2⟩
              have hc0 := hcov2.1 0 (by simpa using h0); simpa using hlay.pos_off _ hc0.1 hc0.2
            · rintro J ⟨p, i, ⟨⟩⟩ mC ⟨hp1, hple, hile, hp_off, wvecC, wstkC,
                hwvC, hwsC, hszC, hzeroC, hdoneC, hdisjC, hremC, hmC⟩ hLoop
              clear hm2; m6_split
              · have hi_lt : i.toNat < n.toNat := by c0_bound
                have hlit_info := hcov2.1 i.toNat hi_lt
                let wi := wsort2[i.toNat]'(by omega)
                have hlit_eq : wi.toNat = wsVal wsort2 i.toNat := by
                  unfold wsVal; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                have hlit_cv : wi.toNat < 2 * s.core.cur_vars := hlit_eq ▸ hlit_info.1
                have hlit2 : (wi.setWidth 64 <<< (1 : Nat)).toNat = 2 * wsVal wsort2 i.toNat := by
                  rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide), hlit_eq]
                  simp [Nat.shiftLeft_eq]; omega
                have hlit2p1 : ((wi.setWidth 64 <<< (1 : Nat)) + 1).toNat =
                    2 * wsVal wsort2 i.toNat + 1 := by rw [BitVec.toNat_add, hlit2]; simp; omega
                have hlit2_lt : (wi.setWidth 64 <<< (1 : Nat)).toNat < wvecC.length := by omega
                have hlit2p1_lt : ((wi.setWidth 64 <<< (1 : Nat)) + 1).toNat < wvecC.length := by
                  omega
                have hoff_i : (wvecC[(wi.setWidth 64 <<< (1 : Nat)).toNat]'hlit2_lt).toNat =
                    fullWatchOff s (wsVal wsort2 i.toNat) := by
                  rw [fi_list_getElem_toNat_eq (by omega) hlit2]
                  have h1 := (hremC i.toNat (by omega) hi_lt).1
                  rwa [List.getElem?_eq_getElem (by have := hlit_info.1; omega),
                    Option.getD_some] at h1
                have hsz_i : (wvecC[((wi.setWidth 64 <<< (1 : Nat)) + 1).toNat]'hlit2p1_lt).toNat =
                    fullWatchSize s (wsVal wsort2 i.toNat) := by
                  rw [fi_list_getElem_toNat_eq (by omega) hlit2p1]
                  have h1 := hszC _ hlit_info.1
                  rwa [List.getElem?_eq_getElem (by have := hlit_info.1; omega),
                    Option.getD_some] at h1
                have hbd_i : fullWatchOff s (wsVal wsort2 i.toNat) +
                    fullWatchSize s (wsVal wsort2 i.toNat) ≤ s.core.wlen :=
                  hlay.bounds _ hlit_info.1
                have hp_le_off : p.toNat ≤ fullWatchOff s (wsVal wsort2 i.toNat) := hp_off hi_lt
                have hps_le : p.toNat + fullWatchSize s (wsVal wsort2 i.toNat) ≤ s.core.wlen := by
                  omega
                have hip1 : (i + 1).toNat = i.toNat + 1 := by bv_omega
                have hpnxt : (p + (wvecC[((wi.setWidth 64 <<< (1 : Nat)) + 1).toNat]'
                    hlit2p1_lt).setWidth 64).toNat =
                    p.toNat + fullWatchSize s (wsVal wsort2 i.toNat) := by
                  rw [BitVec.toNat_add, zext_toNat _ (by decide), hsz_i]; omega
                m6_to_group
                refine wp_join_group (fun _ mD => ∃ (wvecD wstkD : List (BitVec 32)),
                  wvecD.length = 4 * c.max_vars ∧ wstkD.length = c.wcap ∧
                  (∀ j < 2 * s.core.cur_vars,
                    (wvecD[2 * j + 1]?.getD 0#32).toNat = fullWatchSize s j) ∧
                  (∀ j < 2 * s.core.cur_vars,
                    fullWatchSize s j = 0 → (wvecD[2 * j]?.getD 0#32).toNat = 0) ∧
                  (∀ j < i.toNat + 1,
                    let l := wsVal wsort2 j; let off := (wvecD[2 * l]?.getD 0#32).toNat
                    1 ≤ off ∧
                    off + fullWatchSize s l ≤ p.toNat + fullWatchSize s (wsVal wsort2 i.toNat) ∧
                    ∀ k < fullWatchSize s l, wstkD[off + k]? = s.core.wstk[fullWatchOff s l + k]?) ∧
                  (∀ a < i.toNat + 1, ∀ b < i.toNat + 1, a ≠ b →
                    let la := wsVal wsort2 a; let lb := wsVal wsort2 b
                    (wvecD[2 * la]?.getD 0#32).toNat + fullWatchSize s la ≤
                      (wvecD[2 * lb]?.getD 0#32).toNat ∨
                    (wvecD[2 * lb]?.getD 0#32).toNat + fullWatchSize s lb ≤
                      (wvecD[2 * la]?.getD 0#32).toNat) ∧
                  (∀ j, i.toNat + 1 ≤ j → j < n.toNat → let l := wsVal wsort2 j
                    (wvecD[2 * l]?.getD 0#32).toNat = fullWatchOff s l ∧ ∀ k < fullWatchSize s l,
                      wstkD[fullWatchOff s l + k]? = s.core.wstk[fullWatchOff s l + k]?) ∧
                  (FullMem c { s with core := { s.core with wvec := wvecD, wstk := wstkD },
                                      scratch := { s.scratch with wsort := wsort2 } } ⋆ R) mD) ?_ ?_
                · rintro _ _ mD ⟨wvecD, wstkD, hwvD, hwsD, hszD, hzeroD, hdoneD, hdisjD, hremD, hmD⟩
                  m6_steps
                  refine hLoop (p + (wvecC[((wi.setWidth 64 <<< (1 : Nat)) + 1).toNat]'
                      hlit2p1_lt).setWidth 64, i + 1, ()) _ (by simp only [hip1]; omega)
                    ⟨by omega, by omega, by rw [hip1]; omega, fun hi1 => ?_, wvecD, wstkD,
                     hwvD, hwsD, hszD, hzeroD, ?_, ?_, ?_, hmD⟩
                  · rw [hpnxt, hip1]; rw [hip1] at hi1
                    exact Nat.le_trans (Nat.add_le_add_left (Nat.le_refl _) _)
                      (Nat.le_trans (Nat.add_le_add_right hp_le_off _)
                        (defrag_sorted_gap hlay hcov2 hsrt2 (by omega) hi1))
                  · intro j hj; rw [hpnxt]; exact hdoneD j (by rw [hip1] at hj; omega)
                  · exact fun a ha b hb =>
                      hdisjD a (by rw [hip1] at ha; omega) b (by rw [hip1] at hb; omega)
                  · exact fun j hj1 hj2 => hremD j (by rw [hip1] at hj1; omega) hj2
                · intro JD hJD; clear hLoop hQ; m6_split
                  · have hne : fullWatchOff s (wsVal wsort2 i.toNat) ≠ p.toNat := by
                      have h := hc
                      intro heq; apply h; apply BitVec.eq_of_toNat_eq
                      have hix : 2 * (wsort2[i.toNat]'(by omega)).toNat % 2 ^ 64 =
                          2 * wsVal wsort2 i.toNat := by
                        unfold wsVal
                        rw [List.getElem?_eq_getElem (by omega : i.toNat < wsort2.length),
                          Option.getD_some]
                        exact Nat.mod_eq_of_lt (by omega)
                      have hget : (wvecC[2 * (wsort2[i.toNat]'(by omega)).toNat % 2 ^ 64]'(by
                          rw [hix]; omega)).toNat = fullWatchOff s (wsVal wsort2 i.toNat) := by
                        rw [fi_list_getElem_toNat_eq (by omega) hix]
                        have h1 := (hremC i.toNat (by omega) hi_lt).1
                        rwa [List.getElem?_eq_getElem (by have := hlit_info.1; omega),
                          Option.getD_some] at h1
                      rw [zext_toNat _ (by decide), hget, heq]
                    refine wp_loop_inv
                      (fun (k, ()) mK => k.toNat ≤ fullWatchSize s (wsVal wsort2 i.toNat) ∧
                        ∃ wstkK : List (BitVec 32), wstkK.length = c.wcap ∧
                          (∀ idx < p.toNat, wstkK[idx]? = wstkC[idx]?) ∧
                          (∀ idx, fullWatchOff s (wsVal wsort2 i.toNat) + k.toNat ≤ idx →
                            wstkK[idx]? = wstkC[idx]?) ∧
                          (∀ r < k.toNat, wstkK[p.toNat + r]? =
                            s.core.wstk[fullWatchOff s (wsVal wsort2 i.toNat) + r]?) ∧
                          (∀ r, k.toNat ≤ r → r < fullWatchSize s (wsVal wsort2 i.toNat) →
                            wstkK[fullWatchOff s (wsVal wsort2 i.toNat) + r]? =
                              s.core.wstk[fullWatchOff s (wsVal wsort2 i.toNat) + r]?) ∧
                          (FullMem c { s with core := { s.core with wvec := wvecC, wstk := wstkK },
                                              scratch := { s.scratch with wsort := wsort2 } } ⋆ R)
                            mK)
                      (fun (k, ()) _ => fullWatchSize s (wsVal wsort2 i.toNat) - k.toNat)
                      (fun JK hLoopK => ?_) ?_
                    · m6_c0_steps; exact hLoopK _ _ ⟨by simp, wstkC, hwsC, fun _ _ => rfl,
                        fun _ _ => rfl, fun _ hr => by simp at hr,
                        fun r _ hr => (hremC i.toNat (by omega) hi_lt).2 r hr, hmC⟩
                    · rintro JK ⟨k, ⟨⟩⟩ mK ⟨hk_le, wstkK, hwsK, hpreK, hpostK, hcopK, hsrcK, hmK⟩
                        hLoopK
                      clear hmC; m6_split_fast
                      · have hk_lt : k.toNat < fullWatchSize s (wsVal wsort2 i.toNat) := by
                          have hix : ((wi.setWidth 64 <<< (1 : Nat)).toNat +
                              (1 : Val i64).toNat) % 2 ^ 64 = 2 * wsVal wsort2 i.toNat + 1 := by
                            rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide), Nat.shiftLeft_eq,
                              hlit_eq]; simp; omega
                          have hsz_hc : (wvecC[((wi.setWidth 64 <<< (1 : Nat)).toNat +
                              (1 : Val i64).toNat) % 2 ^ 64]'(by rw [hix]; omega)).toNat =
                              fullWatchSize s (wsVal wsort2 i.toNat) := by
                            rw [fi_list_getElem_toNat_eq (by omega) hix]
                            have h1 := hszC _ hlit_info.1
                            rwa [List.getElem?_eq_getElem (by have := hlit_info.1; omega),
                              Option.getD_some] at h1
                          have : k.toNat < (wvecC[((wi.setWidth 64 <<< (1 : Nat)).toNat +
                              (1 : Val i64).toNat) % 2 ^ 64]'(by rw [hix]; omega)).toNat := by
                            c0_bound
                          omega
                        have hkp1 : (k + 1).toNat = k.toNat + 1 := by bv_omega
                        have hpk : (p + k).toNat = p.toNat + k.toNat := by bv_omega
                        have hok_eq : (BitVec.setWidth 64
                            (wvecC[(wi.setWidth 64 <<< (1 : Nat)).toNat]'hlit2_lt) + k).toNat =
                            fullWatchOff s (wsVal wsort2 i.toNat) + k.toNat := by
                          rw [BitVec.toNat_add, zext_toNat _ (by decide), hoff_i]; omega
                        have hok_lt : (BitVec.setWidth 64
                            (wvecC[(wi.setWidth 64 <<< (1 : Nat)).toNat]'hlit2_lt) + k).toNat <
                            wstkK.length := by rw [hok_eq, hwsK]; omega
                        have hok_lt' : (BitVec.setWidth 64
                            wvecC[(BitVec.setWidth 64 (wsort2[i.toNat]'(by omega)) <<< 1).toNat] +
                            k).toNat < wstkK.length := hok_lt
                        have hp_lt_off : p.toNat < fullWatchOff s (wsVal wsort2 i.toNat) :=
                          Nat.lt_of_le_of_ne hp_le_off hne.symm
                        m6_usteps; apply wp_store_sep
                        · simp only [Arg.val_var]
                          exact FullArenaTactics.c0_store_full_wstk _
                            (by rw [hwsK, hpk]; omega) hmK
                        intro m hm; clear hmK; m6_nojoin
                        refine hLoopK (k + 1, ()) _ (by simp only [hkp1]; omega)
                          ⟨by omega, _, by simp [hwsK],
                           fun idx hidx => by
                             rw [List.getElem?_set_ne (by omega)]
                             exact hpreK idx hidx,
                           fun idx hidx => by
                             rw [List.getElem?_set_ne (by omega)]
                             exact hpostK idx (by omega),
                           fun r hr => ?_, fun r hr1 hr2 => by
                             have hr1' : k.toNat ≤ r := by
                               rw [hkp1] at hr1; exact Nat.le_of_succ_le hr1
                             rw [List.getElem?_set_ne (by
                               rw [hpk]
                               exact Nat.ne_of_lt (Nat.lt_of_lt_of_le
                                 (Nat.add_lt_add_right hp_lt_off k.toNat)
                                 (Nat.add_le_add_left hr1' _)))]
                             exact hsrcK r hr1' hr2, hm⟩
                        by_cases hrk : r = k.toNat
                        · subst hrk
                          have hpk_lt : p.toNat + k.toNat < wstkK.length := by rw [hwsK]; omega
                          have hok_eq' : (BitVec.setWidth 64 wvecC[(BitVec.setWidth 64
                              wsort2[i.toNat] <<< 1).toNat] + k).toNat =
                              fullWatchOff s (wsVal wsort2 i.toNat) + k.toNat := hok_eq
                          dsimp only
                          rw [hpk, List.getElem?_set_self hpk_lt,
                            ← List.getElem?_eq_getElem hok_lt', hok_eq']
                          exact hsrcK k.toNat (by omega) hk_lt
                        · rw [List.getElem?_set_ne (by omega)]
                          exact hcopK r (by omega)
                      · have hk_eq : k.toNat = fullWatchSize s (wsVal wsort2 i.toNat) := by
                          have hix : ((wi.setWidth 64 <<< (1 : Nat)).toNat +
                              (1 : Val i64).toNat) % 2 ^ 64 = 2 * wsVal wsort2 i.toNat + 1 := by
                            rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide), Nat.shiftLeft_eq,
                              hlit_eq]; simp; omega
                          have hsz_hc : (wvecC[((wi.setWidth 64 <<< (1 : Nat)).toNat +
                              (1 : Val i64).toNat) % 2 ^ 64]'(by rw [hix]; omega)).toNat =
                              fullWatchSize s (wsVal wsort2 i.toNat) := by
                            rw [fi_list_getElem_toNat_eq (by omega) hix]
                            have h1 := hszC _ hlit_info.1
                            rwa [List.getElem?_eq_getElem (by have := hlit_info.1; omega),
                              Option.getD_some] at h1
                          have : ¬ (k.toNat < (wvecC[((wi.setWidth 64 <<< (1 : Nat)).toNat +
                              (1 : Val i64).toNat) % 2 ^ 64]'(by rw [hix]; omega)).toNat) := by
                            c0_bound
                          omega
                        have hp32 : (p.setWidth 32).toNat = p.toNat := by
                          rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
                        rw [hk_eq] at hcopK hpostK
                        m6_usteps; apply wp_store_sep
                        · simp only [Arg.val_var]
                          exact FullArenaTactics.c0_store_full_wvec _
                            (by rw [hwvC, hlit2]; omega) hmK
                        intro m hm; m6_nojoin
                        have hinv := defrag_compact_copy_inv hi_lt hp1 hp32 hcov2 hlay hsrt2
                          (by omega) hszC hzeroC hdoneC hdisjC hremC hpreK hpostK hcopK
                        dsimp only at hm; rw [hlit2] at hm
                        refine hJD _ _ ⟨_, wstkK, by rw [List.length_set, hwvC], hwsK,
                          hinv.1, hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2, hm⟩
                  · have hoff_eq_p : fullWatchOff s (wsVal wsort2 i.toNat) = p.toNat := by
                      have h := congrArg BitVec.toNat hc; rw [zext_toNat _ (by decide)] at h
                      have hix : 2 * wi.toNat % 2 ^ 64 = 2 * wsVal wsort2 i.toNat := by
                        unfold wi wsVal
                        rw [List.getElem?_eq_getElem (by omega : i.toNat < wsort2.length),
                          Option.getD_some]
                        exact Nat.mod_eq_of_lt (by omega)
                      have hget : (wvecC[2 * wi.toNat % 2 ^ 64]'(by rw [hix]; omega)).toNat =
                          fullWatchOff s (wsVal wsort2 i.toNat) := by
                        rw [fi_list_getElem_toNat_eq (by omega) hix]
                        have h1 := (hremC i.toNat (by omega) hi_lt).1
                        rwa [List.getElem?_eq_getElem (by have := hlit_info.1; omega),
                          Option.getD_some] at h1
                      exact hget.symm.trans h
                    have hinv_k := defrag_compact_keep_inv hp1 hi_lt hdoneC hdisjC hremC hoff_eq_p
                    exact hJD _ _ ⟨wvecC, wstkC, hwvC, hwsC, hszC, hzeroC, hinv_k.1, hinv_k.2,
                      fun j hj1 hj2 => hremC j (by omega) hj2, hmC⟩
              · have hi_eq : i.toNat = n.toNat := by
                  have hlt : ¬ (i.toNat < n.toNat) := by c0_bound
                  omega
                m6_c0_steps; rw [hi_eq] at hdoneC hdisjC
                have hfin := defrag_finalize hlay hcov2 hp1 hszC hzeroC hdoneC hdisjC
                refine hQ wvecC wstkC p.toNat wsort2 _
                  ⟨{ hcl with wvec_len := hwvC, wstk_len_arr := hwsC,
                              wlen_le := by dsimp only; omega }, { hsl with wsort_len := hws2 }⟩
                  hfin.1 (fun _ => hp1) hfin.2 hm
          · intro JS hJS
            clear hQ hcl hsl hsz1 hzero1 hwvl hwle hwsrt_l hwlen_gt1 hwsl_pos hnlits
            let s1 : FullState :=
              { s with core := { s.core with wvec := wvec1 }
                       scratch := { s.scratch with wsort := wsort1 } }
            have hlen1 : FullState.LengthsOk c s1 :=
              ⟨{ hlen.core_ok with wvec_len := hwv1 }, { hlen.scratch_ok with wsort_len := hws1 }⟩
            m6_split_fast
            · exact hJS _ _ ⟨s.core.wstk, wsort1, hwsl, hws1, fun _ _ => rfl,
                hcov1, (hsrt1 hc).1, hm1⟩
            · clear hc; m6_split_fast
              · have hn_gt1 : 1 < n.toNat := by c0_bound
                clear hc; m6_split_fast
                · have h2n_le : 2 * n.toNat + 256 ≤ 2 * c.max_vars := by
                    have h256 : BitVec.toNat (256 : BitVec 64) = 256 := rfl
                    have hm1' : c.max_vars % 2 ^ 64 = c.max_vars := Nat.mod_eq_of_lt (by omega)
                    have hm2' : (2 * c.max_vars) % 2 ^ 64 = 2 * c.max_vars :=
                      Nat.mod_eq_of_lt (by omega)
                    have hm3' : (2 * n.toNat + 256) % 2 ^ 64 = 2 * n.toNat + 256 :=
                      Nat.mod_eq_of_lt (by omega)
                    have h1 := hc; rw [h256, hm1', hm2', hm3'] at h1; exact h1
                  m6_c0_steps; c0_call hRadix
                  have hsp := full_wvec_wsort_split3 hlen1 h2n_le hm1
                  have hlen_w : (wsort1.take n.toNat).length = n.toNat := by simp; omega
                  have hlen_t : ((wsort1.drop n.toNat).take n.toNat).length = n.toNat := by
                    simp; omega
                  have hlen_c : ((wsort1.drop (2 * n.toNat)).take 256).length = 256 := by
                    simp; omega
                  have hp1_eq : c.pWsort + n * 4 =
                      c.pWsort + BitVec.ofNat 64 (4 * n.toNat) := by
                    congr 1; apply BitVec.eq_of_toNat_eq
                    rw [BitVec.toNat_mul, show (4 : BitVec 64).toNat = 4 from rfl,
                      bv64_ofNat_toNat_id (by omega), Nat.mod_eq_of_lt (by omega)]; omega
                  have hp2_eq : c.pWsort + (n <<< (1 : Nat)) * 4 =
                      c.pWsort + BitVec.ofNat 64 (4 * (2 * n.toNat)) := by
                    congr 1; apply BitVec.eq_of_toNat_eq
                    rw [BitVec.toNat_mul, BitVec.toNat_shiftLeft,
                      show (4 : BitVec 64).toNat = 4 from rfl,
                      Nat.shiftLeft_eq, bv64_ofNat_toNat_id (by omega),
                      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
                  refine ⟨wvec1, wsort1.take n.toNat, (wsort1.drop n.toNat).take n.toNat,
                    (wsort1.drop (2 * n.toNat)).take 256,
                    (array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * (2 * n.toNat + 256)))
                      (wsort1.drop (2 * n.toNat + 256)) ⋆ FullWvecWsortRest c s1 ⋆ R),
                    by omega, by omega, by omega, by omega, by omega, fun j hj => ?_, ?_, ?_⟩
                  · have hget_tk : (wsort1.take n.toNat)[j]?.getD 0#32 = wsort1[j]?.getD 0#32 := by
                      simp [hj]
                    have hi := hcov1.1 j hj
                    have hwv_k : wsVal (wsort1.take n.toNat) j = wsVal wsort1 j := by
                      unfold wsVal; rw [hget_tk]
                    rw [hwv_k]; refine ⟨by omega, ?_⟩
                    unfold fullWvecOff; rw [hoff1 _ hi.1 hi.2]; exact hmax_elt j hj
                  · simp only [i32] at *
                    rw [hp1_eq, hp2_eq]; exact hsp
                  · intro ws' tmp' cnt' m' hws' htmp' hcnt' hperm' hsrt' _ hm'
                    rw [hp1_eq, hp2_eq] at hm'
                    have hperm1 := hperm'
                    rw [List.take_of_length_le (Nat.le_of_eq (hws'.trans hlen_w)),
                      List.take_of_length_le (Nat.le_of_eq hlen_w)] at hperm1
                    have hpost := defrag_branch1_done hlen1 hwsl hoff1 hcov1 h2n_le
                      (by omega) (by omega) (by omega) hperm1.symm hsrt' hm'
                    first
                    | exact hJS _ _ hpost
                    | (apply hJ; dsimp only [Blocks.get_here]; rw [wp_jump]; exact hJS _ _ hpost)
                · m6_to_jnz; apply wp_jnz_of <;> intro hc
                  · have hcap_le : s.core.wlen + n.toNat + 256 ≤ c.wcap := by
                      have hwle' : s.core.wlen ≤ c.wcap := hlen.core_ok.wlen_le
                      have hwlen_bd : (BitVec.ofNat 64 s.core.wlen).toNat = s.core.wlen :=
                        bv64_ofNat_toNat_id (by omega)
                      have hwcap_bd : (BitVec.ofNat 64 c.wcap).toNat = c.wcap :=
                        bv64_ofNat_toNat_id (by omega)
                      rw [Arg.val_var, BitVec.ule, decide_eq_true_eq, BitVec.toNat_add,
                        BitVec.toNat_sub_of_le (BitVec.le_def.mpr
                          (by rw [hwlen_bd, hwcap_bd]; omega)),
                        hwlen_bd, hwcap_bd, show (256 : BitVec 64).toNat = 256 from rfl,
                        Nat.mod_eq_of_lt (by omega)] at hc
                      omega
                    clear hc
                    m6_c0_steps; c0_call hRadix
                    have hsp := full_wstack_defrag_wstk_split hlen1 (by omega) hcap_le hm1
                    have hq1_eq : c.pWstk + BitVec.ofNat 64 s.core.wlen * 4 =
                        c.pWstk + BitVec.ofNat 64 (4 * s.core.wlen) := by
                      congr 1; apply BitVec.eq_of_toNat_eq
                      rw [BitVec.toNat_mul, bv64_ofNat_toNat_id (by omega),
                        show (4 : BitVec 64).toNat = 4 from rfl, bv64_ofNat_toNat_id (by omega),
                        Nat.mod_eq_of_lt (by omega)]; omega
                    have hq2_eq : c.pWstk + BitVec.ofNat 64 s.core.wlen * 4 + n * 4 =
                        c.pWstk + BitVec.ofNat 64 (4 * (s.core.wlen + n.toNat)) := by
                      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
                      rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_mul,
                        bv64_ofNat_toNat_id (by omega), show (4 : BitVec 64).toNat = 4 from rfl,
                        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
                        bv64_ofNat_toNat_id (by omega), Nat.mod_eq_of_lt (by omega)]; omega
                    have hlen_w2 : (wsort1.take n.toNat).length = n.toNat := by simp; omega
                    have hlen_t2 : ((s.core.wstk.drop s.core.wlen).take n.toNat).length =
                        n.toNat := by simp [hwsl]; omega
                    have hlen_c2 :
                        ((s.core.wstk.drop (s.core.wlen + n.toNat)).take 256).length = 256 := by
                      simp [hwsl]; omega
                    refine ⟨wvec1, wsort1.take n.toNat,
                      (s.core.wstk.drop s.core.wlen).take n.toNat,
                      (s.core.wstk.drop (s.core.wlen + n.toNat)).take 256,
                      (array (t := i32) (c.pWsort + BitVec.ofNat 64 (4 * n.toNat))
                        (wsort1.drop n.toNat) ⋆
                       array (t := i32) c.pWstk (s.core.wstk.take s.core.wlen) ⋆
                       array (t := i32)
                         (c.pWstk + BitVec.ofNat 64 (4 * (s.core.wlen + n.toNat + 256)))
                         (s.core.wstk.drop (s.core.wlen + n.toNat + 256)) ⋆
                       FullWvecWsortWstkRest c s1 ⋆ R),
                      Nat.le_of_eq hlen_w2.symm, Nat.le_of_eq hlen_t2.symm,
                      Nat.le_of_eq hlen_c2.symm,
                      by omega, by omega, fun j hj => ?_, ?_, ?_⟩
                    · have hi := hcov1.1 j hj
                      have hwv_k : wsVal (wsort1.take n.toNat) j = wsVal wsort1 j := by
                        unfold wsVal; simp [hj]
                      rw [hwv_k]; refine ⟨by omega, ?_⟩
                      unfold fullWvecOff; rw [hoff1 _ hi.1 hi.2]; exact hmax_elt j hj
                    · rw [hq2_eq, hq1_eq]; exact hsp
                    · intro ws' tmp' cnt' m' hws' htmp' hcnt' hperm' hsrt' _ hm'
                      rw [hq2_eq, hq1_eq] at hm'
                      have hperm2 := hperm'
                      rw [List.take_of_length_le (Nat.le_of_eq (hws'.trans hlen_w2)),
                        List.take_of_length_le (Nat.le_of_eq hlen_w2)] at hperm2
                      have hpost := defrag_branch2_done hlen1 hoff1 hcov1 (by omega) hcap_le
                        (by omega) (by omega) (by omega) hperm2.symm hsrt' hm'
                      apply hJ; dsimp only [Blocks.get_here]; rw [wp_jump]
                      first
                      | exact hJS _ _ hpost
                      | (apply ‹∀ (xs : Tup Val []) (m' : Mem 64),
                           wp Γ Q X ((Blocks.cons (fun _ => Expr.jump JS ())
                             Blocks.nil).get Member.here xs) m' → _›
                         dsimp only [Blocks.get_here]; rw [wp_jump]; exact hJS _ _ hpost)
                  · -- Branch 3: `full_wsort_sift` heapsort fallback
                    clear hc hRadix hmax_elt hprev_le hmax_le; m6_to_group
                    refine wp_loop_inv (DefragHeapInv c s R wvec1 n.toNat)
                      (fun ((st : Val i64), ()) _ => st.toNat) (fun JB hLoopB => ?_) ?_
                    · m6_tiny_lets; rw [wp_jump]; try m6_tiny_simp
                      have hshr : (n >>> (1 : Nat)).toNat = n.toNat / 2 := by
                        rw [BitVec.toNat_ushiftRight]; simp [Nat.shiftRight_eq_div_pow]
                      refine hLoopB _ _ ⟨by rw [hshr]; exact Nat.div_le_self _ _, wsort1, hws1,
                        hcov1, fun _ hi _ => by rw [hshr] at hi; exact ⟨by omega, by omega⟩, hm1⟩
                    · rintro JB ⟨st, ⟨⟩⟩ mB ⟨hst_le, wsB, hwsB, hcovB, hmaxB, hmB⟩ hLoopB
                      clear hm1; m6_to_jnz; apply wp_jnz_of <;> intro hc
                      · have hst_pos : 0 < st.toNat := by
                          rw [Arg.val_var, BitVec.ult, decide_eq_true_eq] at hc; exact hc
                        have hstm1 : (st - 1).toNat = st.toNat - 1 := by bv_omega
                        clear hc; m6_tiny_lets; c0_call hSift
                        refine ⟨2 * s.core.cur_vars, wvec1, wsB, _, by rw [hwv1]; omega,
                          Nat.lt_of_lt_of_le (by rw [hstm1]; exact Nat.sub_lt hst_pos Nat.one_pos)
                            hst_le,
                          by omega, by rw [hwsB]; exact Nat.le_trans hn_le (by omega),
                          fun i hi => (hcovB.1 i hi).1,
                          by rw [hstm1, show st.toNat - 1 + 1 = st.toNat by omega]; exact hmaxB,
                          focus_wvec_wsort hmB, ?_⟩
                        intro ws' m' hws' hperm' hsuf' hmax' hm'
                        have hm'' := unfocus_wvec_wsort
                          (s := { s with core := { s.core with wvec := wvec1 },
                                         scratch := { s.scratch with wsort := wsB } }) hm'
                        have hcov' := wsCovers_of_perm_suffix hcovB (by rw [hws'])
                          (hwsB ▸ Nat.le_trans hn_le (Nat.mul_le_mul_left 2 hcv_le)) hperm'
                          fun i hi => hsuf' i (Or.inr hi)
                        m6_tiny_lets
                        exact hLoopB _ _
                          (by dsimp only; rw [hstm1]; exact Nat.sub_lt hst_pos Nat.one_pos)
                          ⟨by rw [hstm1]; exact Nat.le_trans (Nat.sub_le _ 1) hst_le,
                           ws', by rw [hws', hwsB], hcov', hmax', hm''⟩
                      · have hst0 : st.toNat = 0 := by
                          (try simp only [Arg.val_var] at hc)
                          rw [BitVec.ult, decide_eq_false_iff_not,
                            show (0 : BitVec 64).toNat = 0 from rfl] at hc
                          omega
                        rw [hst0] at hmaxB
                        clear hc hLoopB JB st hst_le hst0
                        refine wp_loop_inv (DefragExtractInv c s R wvec1 n.toNat)
                          (fun ((e : Val i64), ()) _ => e.toNat) (fun JE hLoopE => ?_) ?_
                        · m6_tiny_lets; rw [wp_jump]; try m6_tiny_simp
                          have hnm1 : (n - 1).toNat = n.toNat - 1 := by bv_omega
                          have hnm1p1 : (n - 1).toNat + 1 = n.toNat := by rw [hnm1]; omega
                          refine hLoopE _ _ ⟨by rw [hnm1]; exact Nat.sub_lt hn_pos Nat.one_pos,
                            wsB, hwsB, hcovB, by rw [hnm1p1]; exact hmaxB,
                            fun _ _ _ _ _ => by rw [hnm1p1] at *; omega,
                            fun _ _ _ _ _ => by rw [hnm1p1] at *; omega, hmB⟩
                        · rintro JE ⟨e, ⟨⟩⟩ mE
                            ⟨he_lt, wsE, hwsE, hcovE, hmaxE, hspE, hsrtE, hmE⟩ hLoopE
                          clear hmB wsB hwsB hcovB hmaxB; m6_to_jnz; apply wp_jnz_of <;> intro hc
                          · have he_pos : 0 < e.toNat := by
                              rw [Arg.val_var, BitVec.ult, decide_eq_true_eq] at hc; omega
                            have hem1 : (e - 1).toNat = e.toNat - 1 := by bv_omega
                            have h0_lt : 0 < wsE.length := hwsE ▸ Nat.lt_of_lt_of_le he_pos
                              (Nat.le_trans (Nat.le_of_lt he_lt)
                                (Nat.le_trans hn_le (Nat.mul_le_mul_left 2 hcv_le)))
                            have he_len : e.toNat < wsE.length := hwsE ▸ Nat.lt_of_lt_of_le he_lt
                              (Nat.le_trans hn_le (Nat.mul_le_mul_left 2 hcv_le))
                            clear hc
                            m6_tiny_lets
                            apply wp_load_of
                            · simp only [Arg.val_var]
                              exact FullArenaTactics.c0_load_full_wsort (i := 0#64) (s := { s with
                                core := { s.core with wvec := wvec1 },
                                scratch := { s.scratch with wsort := wsE } })
                                h0_lt hmE
                            m6_tiny_lets
                            apply wp_load_of
                            · simp only [Arg.val_var]
                              exact FullArenaTactics.c0_load_full_wsort (i := e) (s := { s with
                                core := { s.core with wvec := wvec1 },
                                scratch := { s.scratch with wsort := wsE } })
                                he_len hmE
                            m6_tiny_lets
                            apply wp_store_sep
                            · simp only [Arg.val_var]
                              exact FullArenaTactics.c0_store_full_wsort (i := 0#64) (s := { s with
                                core := { s.core with wvec := wvec1 },
                                scratch := { s.scratch with wsort := wsE } })
                                _ h0_lt hmE
                            intro m_sw0 hm_sw0
                            m6_tiny_lets
                            apply wp_store_sep
                            · simp only [Arg.val_var]
                              exact FullArenaTactics.c0_store_full_wsort (i := e) (s := { s with
                                core := { s.core with wvec := wvec1 },
                                scratch := { s.scratch with wsort := wsE.set 0 _ } })
                                _ (by rw [List.length_set]; exact he_len) hm_sw0
                            intro m_sw hm_sw
                            m6_tiny_lets
                            have hsw_step :=
                              wsort_extract_swap_step hmaxE hspE hsrtE he_pos he_lt (by omega)
                            have hsw_cov := wsCovers_swap hcovE (i := 0) (j := e.toNat) (by omega)
                              he_lt (by omega)
                            let wsSwap :=
                              (wsE.set 0 (wsE[e.toNat]'he_len)).set e.toNat (wsE[0]'h0_lt)
                            have hm_sw' : (FullMem c { s with
                                core := { s.core with wvec := wvec1 },
                                scratch := { s.scratch with wsort := wsSwap } } ⋆ R) m_sw := hm_sw
                            m6_tiny_lets; c0_call hSift
                            refine ⟨2 * s.core.cur_vars, wvec1, wsSwap, _, by rw [hwv1]; omega,
                              by simp; exact he_pos, by omega, by simp [wsSwap]; omega,
                              fun i hi => (hsw_cov.1 i (by omega)).1, by simp; exact hsw_step.1,
                              focus_wvec_wsort hm_sw', ?_⟩
                            intro ws' m' hws' hperm' hsuf' hmax' hm'
                            have hm'' := unfocus_wvec_wsort
                              (s := { s with core := { s.core with wvec := wvec1 },
                                             scratch := { s.scratch with wsort := wsSwap } }) hm'
                            m6_tiny_lets
                            exact hLoopE _ _
                              (by dsimp only; rw [hem1]; exact Nat.sub_lt he_pos Nat.one_pos)
                              (defrag_extract_next
                                (Nat.le_trans hn_le (Nat.mul_le_mul_left 2 hcv_le))
                                he_pos he_lt rfl hem1 hwsE hws' hmaxE hspE hsrtE hcovE hperm'
                                (fun i hi => by simpa using hsuf' i hi) hmax' hm'')
                          · have he0 : e.toNat = 0 := by
                              (try simp only [Arg.val_var] at hc)
                              rw [BitVec.ult, decide_eq_false_iff_not,
                                show (0 : BitVec 64).toNat = 0 from rfl] at hc
                              omega
                            rw [he0] at hspE hsrtE
                            m6_tiny_lets; rw [wp_jump]; apply hJ
                            dsimp only [Blocks.get_here]; rw [wp_jump]
                            refine ‹∀ xs m', wp Γ Q X ((Blocks.cons
                              (fun _ => Expr.jump JS ()) Blocks.nil).get
                                Member.here xs) m' → _› _ _ ?_
                            dsimp only [Blocks.get_here]; rw [wp_jump]
                            exact hJS _ _ ⟨s.core.wstk, wsE, hwsl, hwsE, fun _ _ => rfl,
                              hcovE, defrag_extract_done hoff1 hcovE hspE hsrtE, hmE⟩
              · -- `n ≤ 1`
                have hn1 : n.toNat ≤ 1 := by
                  have hnot : ¬ (1 < n.toNat) := by c0_bound
                  omega
                rw [wp_jump]
                exact hJS _ _ ⟨s.core.wstk, wsort1, hwsl, hws1, fun _ _ => rfl,
                  hcov1, fun i j _ hij hj => by
                    have heq : i = j := by omega
                    subst heq; exact Nat.le_refl _, hm1⟩

/-! ## 4. `full_lit_rank_m6_wp`, `full_sweep_bins_range_m6_wp`, & `full_sweep_bins_m6_wp` -/

theorem full_lit_rank_m6_wp (Γ : Env) :
    ∀ a m Q X, fullLitRankSpec a m Q X → Func.wp Γ full_lit_rank_m6_body a m Q X := by
  rintro ⟨vals_ptr, lvl_ptr, l, ⟨⟩⟩ m Q X ⟨vals, lvl, R, hl_v, hl_l, hm, hQ⟩
  have hsh : (l >>> 1#32).toNat = l.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hsh_l : (l >>> 1#32).toNat < lvl.length := by rw [hsh]; exact hl_l
  m6_steps <;> exact hQ _

theorem fullWstackRadixSortSpec_xirrel {a m Q X X'}
    (h : fullWstackRadixSortSpec a m Q X) : fullWstackRadixSortSpec a m Q X' := h

end LeanQbe.T.Examples.Kissat.FullM6WatchGc
