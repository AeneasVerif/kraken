module

public import LeanQbe.T.Examples.Kissat.FullPropDecLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Chronological BCP Core Transitions & Watch Compaction (`Stage 4`, Part 2)

Builds on `FullPropDecLemmas1` to provide:
1. `PH_SHRK`-aware arena swap preservation (`full_swapCl_preserves_nw`, `full_setSrch_preserves_nw`,
   `full_swapLits_preserves_nw`, with `FullArenaPermEq` preserving `FullArenaVarsNodup`).
2. Fixed-`F_cur` chronological unit-propagation transitions (`unitAssign_preserves_fullWitness_nw`,
   `full_bin_assign_nw_step`, `full_large_assign_nw_step`).
3. Mid-compaction watch-slice invariant `SplitWatchesInv` (`init`, `with_nonwatch`, `advance_rem`,
   `write_bin`, `write_large`, `after_push`, `finish`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
  LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat Kraken.Bedrock2.Test
open FullPropDecSpecs
open scoped FullArenaTactics FullPropDecTactics

/-! ## 1. List-swap permutation & `PH_SHRK`-aware arena swap lemmas -/

private theorem count_set_eq {α : Type} [BEq α] [LawfulBEq α] (xs : List α) {i : Nat}
    (hi : i < xs.length) (v a : α) :
    (xs.set i v).count a + (if xs[i] == a then 1 else 0) =
      xs.count a + (if v == a then 1 else 0) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x tl ih =>
    cases i with
    | zero => simp [List.count_cons]; omega
    | succ i' =>
      simp only [List.set_cons_succ, List.count_cons, List.getElem_cons_succ]
      have := ih (i := i') (by simp at hi; omega)
      omega

private theorem list_swap_perm {α : Type} [BEq α] [LawfulBEq α] (xs : List α) {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) :
    ((xs.set i xs[j]).set j xs[i]).Perm xs := by
  rw [List.perm_iff_count]; intro a
  have h1 := count_set_eq xs hi xs[j] a
  have h2 := count_set_eq (xs.set i xs[j]) (i := j) (by simp [hj]) xs[i] a
  by_cases hij : i = j
  · subst hij; simp only [List.getElem_set_self] at h2; omega
  · simp only [List.getElem_set_ne hij] at h2; omega

/-- Updating `ar[cref + 1] := srch` and swapping `ar[cref + 3 + k1]` with `ar[cref + 3 + k2]`
preserves `PH_SHRK`-aware `FullWitnessInv` (with empty watches) and `FullArenaPermEq`. -/
theorem full_swapCl_preserves_nw {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c)
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k))
    {cref k1 k2 : Nat} {srch : BitVec 32} (hcref : cref ∈ fullArenaClauseRefsCore k)
    (hk1 : k1 < fullArenaClauseSizeCore k cref) (hk2 : k2 < fullArenaClauseSizeCore k cref) :
    have hbd : cref + 3 + fullArenaClauseSizeCore k cref ≤ k.arena.length := by
      have h1 : cref + 3 + fullArenaClauseSizeCore k cref ≤
          fullArenaNextOff k.arena k.arena_len cref := (hnw.arena.refs_wf cref hcref).2.2.1
      have h2 : fullArenaNextOff k.arena k.arena_len cref ≤ k.arena_len :=
        (hnw.arena.refs_wf cref hcref).2.2.2.1
      have h3 := hlen.arena_len_le; have h4 := hlen.arena_len_arr; omega
    let l1 := k.arena[cref + 3 + k1]'(by omega)
    let l2 := k.arena[cref + 3 + k2]'(by omega)
    let arena' := ((k.arena.set (cref + 1) srch).set (cref + 3 + k1) l2).set (cref + 3 + k2) l1
    let k' : FullCoreState := { k with arena := arena' }
    FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k') ∧ FullArenaPermEq k k' := by
  intro hbd l1 l2 arena' k'
  have hmc : cref + 3 ≤ k.arena_len ∧ 3 ≤ fullArenaClauseSizeCore k cref ∧
      cref + 3 + fullArenaClauseSizeCore k cref ≤ fullArenaNextOff k.arena k.arena_len cref ∧
      fullArenaNextOff k.arena k.arena_len cref ≤ k.arena_len ∧
      (fullArenaNextOff k.arena k.arena_len cref = k.arena_len ∨
       fullArenaNextOff k.arena k.arena_len cref + 3 ≤ k.arena_len) :=
    hnw.arena.refs_wf cref hcref
  have har0 : arena'[cref]? = k.arena[cref]? := by
    simp only [arena']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have har2 : arena'[cref + 2]? = k.arena[cref + 2]? := by
    simp only [arena']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have har_out : ∀ i, (i < cref ∨ cref + 3 + fullArenaClauseSizeCore k cref ≤ i) →
      arena'[i]? = k.arena[i]? := fun i hi => by
    simp only [arena']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have hout : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore k r ≤ cref ∧
        fullArenaNextOff k.arena k.arena_len r ≤ cref) ∨
      (cref + 3 + fullArenaClauseSizeCore k cref ≤ r) := fun r hr hne => by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨hnw.arena.disjoint hr hcref hlt, fullArenaScanRefs_disjoint hr hcref hlt⟩
    · exact Or.inr (hnw.arena.disjoint hcref hr hgt)
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaNextOff k'.arena k.arena_len r = fullArenaNextOff k.arena k.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst hrc
      exact fullArenaNextOff_congr_block har0 har2 fun j hj1 _ => har_out j (Or.inr hj1)
    · rcases hout r hr hrc with ⟨h1, h2⟩ | hgt
      · have h3 : 3 ≤ fullArenaClauseSizeCore k r := (hnw.arena.refs_wf r hr).2.1
        exact fullArenaNextOff_congr_block (har_out r (Or.inl (by omega)))
          (har_out (r + 2) (Or.inl (by omega))) fun j _ hj2 => har_out j (Or.inl (by omega))
      · exact fullArenaNextOff_congr_block (har_out r (Or.inr hgt))
          (har_out (r + 2) (Or.inr (by omega))) fun j _ _ => har_out j (Or.inr (by omega))
  have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hsz_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r := fun r hr => by
    unfold fullArenaClauseSizeCore; dsimp only [k']
    by_cases hrc : r = cref
    · subst hrc; exact congrArg (fun o => (o.getD 0#32).toNat) har2
    · rcases hout r hr hrc with ⟨h1, _⟩ | hgt
      · have h3 : 3 ≤ fullArenaClauseSizeCore k r := (hnw.arena.refs_wf r hr).2.1
        rw [har_out (r + 2) (Or.inl (by omega))]
      · rw [har_out (r + 2) (Or.inr (by omega))]
  have hgarb_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := fun r hr => by
    unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [k']
    by_cases hrc : r = cref
    · subst hrc; rw [har0]
    · rcases hout r hr hrc with ⟨h1, _⟩ | hgt
      · rw [har_out r (Or.inl (by omega))]
      · rw [har_out r (Or.inr hgt)]
  have hperm_all : ∀ r ∈ fullArenaClauseRefsCore k,
      (fullArenaClauseLitsCore k' r).Perm (fullArenaClauseLitsCore k r) := by
    intro r hr
    have hbd_r : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length := by
      have h1 : r + 3 + fullArenaClauseSizeCore k r ≤ fullArenaNextOff k.arena k.arena_len r :=
        (hnw.arena.refs_wf r hr).2.2.1
      have h2 : fullArenaNextOff k.arena k.arena_len r ≤ k.arena_len :=
        (hnw.arena.refs_wf r hr).2.2.2.1
      have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
    by_cases hrc : r = cref
    · subst r
      let xs := fullArenaClauseLitsCore k cref
      have hxs_len : xs.length = fullArenaClauseSizeCore k cref := by
        simp only [xs, fullArenaClauseLitsCore, List.length_map, List.length_take, List.length_drop]
        omega
      have hxs_get : ∀ j (hj : j < fullArenaClauseSizeCore k cref),
          xs[j]'(by omega) = (k.arena[cref + 3 + j]'(by omega)).toNat := fun j hj => by
        simp [xs, fullArenaClauseLitsCore]
      have heq_lits : fullArenaClauseLitsCore k' cref =
          ((xs.set k1 (xs[k2]'(by omega))).set k2 (xs[k1]'(by omega))) := by
        apply List.ext_getElem
        · simp only [fullArenaClauseLitsCore, hsz_eq cref hr, List.length_map, List.length_take,
            List.length_drop, List.length_set, hxs_len, k', arena']
          omega
        · intro j hj1 _
          have hj : j < fullArenaClauseSizeCore k cref := by
            simp only [fullArenaClauseLitsCore, hsz_eq cref hr, List.length_map, List.length_take,
              List.length_drop, k', arena'] at hj1; omega
          simp only [fullArenaClauseLitsCore, List.getElem_map, List.getElem_take,
            List.getElem_drop, k', arena']
          by_cases h2 : j = k2
          · subst j; simp [List.getElem_set_self, l1]; exact (hxs_get k1 hk1).symm
          · rw [List.getElem_set_ne (by omega : cref + 3 + k2 ≠ cref + 3 + j),
              List.getElem_set_ne (by omega : k2 ≠ j)]
            by_cases h1 : j = k1
            · subst j; simp [List.getElem_set_self, l2]; exact (hxs_get k2 hk2).symm
            · rw [List.getElem_set_ne (by omega : cref + 3 + k1 ≠ cref + 3 + j),
                List.getElem_set_ne (by omega : cref + 1 ≠ cref + 3 + j),
                List.getElem_set_ne (by omega : k1 ≠ j), hxs_get j hj]
      rw [heq_lits]
      exact list_swap_perm xs (by omega) (by omega)
    · have hlits_eq : fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r :=
        fullArenaClauseLitsCore_eq_of_hold hbd_r (by simp [k', arena', hbd_r]) (hsz_eq r hr)
          fun j hj => by
            dsimp only [k']
            rcases hout r hr hrc with ⟨h1, _⟩ | hgt
            · exact har_out (r + 3 + j) (Or.inl (by omega))
            · exact har_out (r + 3 + j) (Or.inr (by omega))
      rw [hlits_eq]
  have hmem_iff : ∀ r ∈ fullArenaClauseRefsCore k, ∀ l,
      l ∈ fullArenaClauseLitsCore k' r ↔ l ∈ fullArenaClauseLitsCore k r := fun r hr l =>
    (hperm_all r hr).mem_iff
  have harena' : FullArenaClausesInv c F_cur (withEmptyWatchesCore c k') := by
    refine ⟨hnw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; change r ∈ fullArenaClauseRefsCore k' at hr; rw [hrefs] at hr
      have hwf := hnw.arena.refs_wf r hr
      have hsz_r : fullArenaClauseSizeCore (withEmptyWatchesCore c k') r =
          fullArenaClauseSizeCore k r := hsz_eq r hr
      have hnxt_r : fullArenaNextOff (withEmptyWatchesCore c k').arena
          (withEmptyWatchesCore c k').arena_len r = fullArenaNextOff k.arena k.arena_len r :=
        hnxt r hr
      rw [hsz_r, hnxt_r]; exact hwf
    · intro r hr hsh; change r ∈ fullArenaClauseRefsCore k' at hr; rw [hrefs] at hr
      have hsh0 : (fullArenaHdrCore (withEmptyWatchesCore c k) r &&& 0x00800000#32) ≠ 0#32 := by
        unfold fullArenaHdrCore at hsh ⊢; dsimp only [withEmptyWatchesCore, k'] at hsh ⊢
        by_cases hrc : r = cref
        · subst hrc; rwa [har0] at hsh
        · rcases hout r hr hrc with ⟨h1, _⟩ | hgt
          · rwa [har_out r (Or.inl (by omega))] at hsh
          · rwa [har_out r (Or.inr hgt)] at hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := hnw.arena.shrk_term r hr hsh0
      have hr3 : r + 3 ≤ k.arena_len := (hnw.arena.refs_wf r hr).1
      obtain ⟨t0, ht0_lo, ht0_lt, ht0_nxt, ht0_sent⟩ :=
        fullArenaNextOff_hits_sentinel hr3 hsh0 ht1 ht2 hsent
      have ht0_lo' : r + 3 + fullArenaClauseSizeCore k r ≤ t0 := ht0_lo
      have ht0_nxt' : t0 < fullArenaNextOff k.arena k.arena_len r := by
        change fullArenaNextOff k.arena k.arena_len r = t0 + 1 at ht0_nxt; omega
      have ht0_out : t0 < cref ∨ cref + 3 + fullArenaClauseSizeCore k cref ≤ t0 := by
        by_cases hrc : r = cref
        · subst hrc; exact Or.inr ht0_lo'
        · rcases hout r hr hrc with ⟨_, h2⟩ | hgt
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)
      refine ⟨t0, by rw [show fullArenaClauseSizeCore (withEmptyWatchesCore c k') r =
          fullArenaClauseSizeCore k r from hsz_eq r hr]; exact ht0_lo',
        show t0 < k.arena_len by have ht2' : t < k.arena_len := ht2; omega, ?_⟩
      change arena'[t0]? = some 0xFFFFFFFF#32
      rw [har_out t0 ht0_out]; exact ht0_sent
    · intro r hr hng l hl; change r ∈ fullArenaClauseRefsCore k' at hr; rw [hrefs] at hr
      have hng0 : fullArenaClauseGarbCore k r = false := (hgarb_eq r hr).symm.trans hng
      exact hnw.arena.lits_lt r hr hng0 l ((hmem_iff r hr l).mp hl)
    · intro r hr hng; change r ∈ fullArenaClauseRefsCore k' at hr; rw [hrefs] at hr
      have hng0 : fullArenaClauseGarbCore k r = false := (hgarb_eq r hr).symm.trans hng
      exact entails_of_mem_or_false (hnw.arena.entails r hr hng0) fun l hl =>
        Or.inl ((hmem_iff r hr l).mpr hl)
  refine ⟨{ hnw with
    arena := harena'
    watches := fullWatchesInv_empty c F_cur k' hlen.cur_vars_le
    reason_inv := fun idx hidx hne => by
      have hrs := hnw.reason_inv idx hidx hne
      dsimp only [withEmptyWatchesCore, k'] at hrs ⊢
      by_cases hb : (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
      · rw [ite_eq_left hb] at hrs ⊢; exact hrs
      · rw [ite_eq_right hb] at hrs ⊢
        refine ⟨hrefs ▸ hrs.1, (hgarb_eq _ hrs.1).trans hrs.2.1,
          fun q hq => hrs.2.2 q ((hmem_iff _ hrs.1 q).mp hq)⟩
    reason_lit_mem := fun idx hidx hne hlg => by
      have hrs := hnw.reason_inv idx hidx hne
      have hb : ¬ (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
      rw [ite_eq_right hb] at hrs
      exact (hmem_iff _ hrs.1 _).mpr (hnw.reason_lit_mem idx hidx hne hlg) },
    ⟨hrefs, fun r hr => ⟨hsz_eq r hr, hgarb_eq r hr, hperm_all r hr⟩⟩⟩

theorem full_setSrch_preserves_nw {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c)
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k))
    {cref : Nat} {srch : BitVec 32} (hcref : cref ∈ fullArenaClauseRefsCore k) :
    let k' : FullCoreState := { k with arena := k.arena.set (cref + 1) srch }
    FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k') ∧ FullArenaPermEq k k' := by
  have h3 : 3 ≤ fullArenaClauseSizeCore k cref := (hnw.arena.refs_wf cref hcref).2.1
  have hbd : cref + 3 + fullArenaClauseSizeCore k cref ≤ k.arena.length := by
    have h1 : cref + 3 + fullArenaClauseSizeCore k cref ≤
        fullArenaNextOff k.arena k.arena_len cref := (hnw.arena.refs_wf cref hcref).2.2.1
    have h2 : fullArenaNextOff k.arena k.arena_len cref ≤ k.arena_len :=
      (hnw.arena.refs_wf cref hcref).2.2.2.1
    have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
  have hsw := full_swapCl_preserves_nw hlen hnw (cref := cref) (k1 := 0) (k2 := 0) (srch := srch)
    hcref (by omega) (by omega)
  have heq : ((k.arena.set (cref + 1) srch).set (cref + 3 + 0)
      (k.arena[cref + 3 + 0]'(by omega))).set (cref + 3 + 0)
      (k.arena[cref + 3 + 0]'(by omega)) = k.arena.set (cref + 1) srch := by
    apply List.ext_getElem (by simp)
    intro i hi _
    by_cases h1 : i = cref + 3 + 0
    · subst h1; simp [List.getElem_set_ne (by omega : cref + 1 ≠ cref + 3 + 0)]
    · rw [List.getElem_set_ne (Ne.symm h1), List.getElem_set_ne (Ne.symm h1)]
  simpa only [heq] using hsw

theorem full_swapLits_preserves_nw {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c)
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k))
    {cref k1 k2 : Nat} (hcref : cref ∈ fullArenaClauseRefsCore k)
    (hk1 : k1 < fullArenaClauseSizeCore k cref) (hk2 : k2 < fullArenaClauseSizeCore k cref) :
    have hbd : cref + 3 + fullArenaClauseSizeCore k cref ≤ k.arena.length := by
      have h1 : cref + 3 + fullArenaClauseSizeCore k cref ≤
          fullArenaNextOff k.arena k.arena_len cref := (hnw.arena.refs_wf cref hcref).2.2.1
      have h2 : fullArenaNextOff k.arena k.arena_len cref ≤ k.arena_len :=
        (hnw.arena.refs_wf cref hcref).2.2.2.1
      have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
    let l1 := k.arena[cref + 3 + k1]'(by omega)
    let l2 := k.arena[cref + 3 + k2]'(by omega)
    let k' : FullCoreState :=
      { k with arena := (k.arena.set (cref + 3 + k1) l2).set (cref + 3 + k2) l1 }
    FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k') ∧ FullArenaPermEq k k' := by
  intro hbd l1 l2 k'
  have h1lt : cref + 1 < k.arena.length := by omega
  have hsw := full_swapCl_preserves_nw hlen hnw (cref := cref) (k1 := k1) (k2 := k2)
    (srch := k.arena[cref + 1]'h1lt) hcref hk1 hk2
  have heq : k.arena.set (cref + 1) (k.arena[cref + 1]'h1lt) = k.arena :=
    List.set_getElem_self h1lt
  simpa only [heq] using hsw

theorem full_clause_falsified_of_find_repl_none {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {st : FullState} {cref not_lit other : Nat}
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st.core))
    (hcref : cref ∈ fullArenaClauseRefs st) (hng : fullArenaClauseGarb st cref = false)
    (hbd : cref + 3 + fullArenaClauseSize st cref ≤ st.core.arena.length)
    (hother_at : (st.core.arena[cref + 3]'(by
      have h3 : 3 ≤ fullArenaClauseSize st cref := (hnw.arena.refs_wf cref hcref).2.1
      omega)).toNat = other)
    (hnot_at : (st.core.arena[cref + 4]'(by
      have h3 : 3 ≤ fullArenaClauseSize st cref := (hnw.arena.refs_wf cref hcref).2.1
      omega)).toNat = not_lit)
    (hnot_false : st.core.vals[not_lit]?.getD 0#8 = 0xFF#8)
    (hfind : ∀ k, 2 ≤ k → k < fullArenaClauseSize st cref → fullFindReplBad st cref k) :
    ∀ l ∈ fullArenaClauseLits st cref, l = other ∨ st.core.vals[l]?.getD 0#8 = 0xFF#8 := by
  intro l hl
  obtain ⟨k, hk, hget⟩ := (mem_fullArenaClauseLitsCore_iff hbd).mp hl
  have h3 : 3 ≤ fullArenaClauseSize st cref := (hnw.arena.refs_wf cref hcref).2.1
  match k with
  | 0 => exact Or.inl (by simpa using hget.symm.trans hother_at)
  | 1 =>
    have h4 : (st.core.arena[cref + 3 + 1]'(by omega)).toNat = not_lit := hnot_at
    exact Or.inr (by rw [← hget, h4]; exact hnot_false)
  | k' + 2 =>
    have hlt : l < 2 * st.core.cur_vars := hnw.arena.lits_lt cref hcref hng l hl
    have hbd' : cref + 3 + fullArenaClauseSizeCore st.core cref ≤ st.core.arena.length := hbd
    have hf := hfind (k' + 2) (by omega) hk
    unfold fullFindReplBad at hf
    rw [List.getElem?_eq_getElem (show cref + 3 + (k' + 2) < st.core.arena.length by omega),
      Option.getD_some, hget] at hf
    exact Or.inr ((full_i8_vals_slt0 (hnw.vals_domain l hlt)).mp (hf.resolve_left (by omega)))

/-! ## 2. Fixed-`F_cur` chronological unit-propagation transitions -/

/-- Fixed-`F_cur` chronological unit-propagation step (`rsn ≠ 0xFFFFFFFF`, `alvl ≤ cur_level`)
preserving `FullWitnessInv` (with empty watches), `FullTrailExt`, and `not_lit` falsified. -/
theorem unitAssign_preserves_fullWitness_nw {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hlen : k.LengthsOk c)
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k))
    {lit rsn alvl : BitVec 32} {not_lit : Nat}
    {flags' : List (BitVec 32)} {unas' unfl' : BitVec 64}
    (hlit : lit.toNat < 2 * k.cur_vars) (hun : k.vals[lit.toNat]?.getD 0#8 = 0#8)
    (hnot_lt : not_lit < 2 * k.cur_vars) (hnot_false : k.vals[not_lit]?.getD 0#8 = 0xFF#8)
    (hrsn_ne : rsn ≠ 0xFFFFFFFF#32) (halvl_le : alvl.toNat ≤ k.cur_level)
    (hl0 : alvl = 0#32 → (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]))
    (hrsn : alvl ≠ 0#32 →
      if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * k.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, ot]) ∧
        ∃ m < k.trail_end, (k.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
          (k.lvl[ot / 2]?.getD 0#32).toNat ≤ alvl.toNat
      else
        rsn.toNat ∈ fullArenaClauseRefsCore k ∧ fullArenaClauseGarbCore k rsn.toNat = false ∧
        ∀ q ∈ fullArenaClauseLitsCore k rsn.toNat,
          q = lit.toNat ∨ ∃ m < k.trail_end, (k.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
            (k.lvl[q / 2]?.getD 0#32).toNat ≤ alvl.toNat)
    (hrsn_mem : alvl ≠ 0#32 → (rsn &&& 0x80000000#32) = 0#32 →
      lit.toNat ∈ fullArenaClauseLitsCore k rsn.toNat) :
    let v := lit.toNat / 2
    let rsn' := if alvl = 0#32 then 0xFFFFFFFF#32 else rsn
    let k' : FullCoreState :=
      { k with
        vals := (k.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
        flags := flags', lvl := k.lvl.set v alvl, rsns := k.rsns.set v rsn'
        trl := k.trl.set k.trail_end lit
        trail_pos := k.trail_pos.set v (BitVec.ofNat 32 k.trail_end)
        trail_end := k.trail_end + 1, unassigned := unas', unflushed := unfl' }
    FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k') ∧
    k'.vals[not_lit]?.getD 0#8 = 0xFF#8 ∧ FullTrailExt k k' := by
  intro v rsn' k'
  have hte_lt : k.trail_end < k.cur_vars := hnw.trail_end_lt_of_unassigned hlit hun
  have hcl_le : k.cur_level ≤ k.trail_end := hnw.cur_level_le
  have htl_lt : ∀ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat < 2 * k.cur_vars :=
    hnw.trail_lits_lt
  have hnot_var : ∀ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat / 2 ≠ v :=
    (hnw.vals_zero_iff hlit).mp hun
  have hne_lit : lit.toNat ^^^ 1 ≠ lit.toNat := litNeg_ne_self lit.toNat
  have hv_lt : v < c.max_vars := by have := hlen.cur_vars_le; omega
  have hte_max : k.trail_end < c.max_vars := by have := hlen.cur_vars_le; omega
  have hte_lt32 : k.trail_end < 2 ^ 32 := by have := fullInv_max_vars_lt32 c; omega
  have htrl_get : ∀ i < k.trail_end + 1,
      (k'.trl[i]?.getD 0#32).toNat =
        if i = k.trail_end then lit.toNat else (k.trl[i]?.getD 0#32).toNat := fun i _ => by
    by_cases he : i = k.trail_end
    · subst he; simp [k', List.getElem?_set_self (by rw [hlen.trl_len]; exact hte_max)]
    · simp [k', he, List.getElem?_set_ne (Ne.symm he)]
  have hlvl_get : ∀ w < k.cur_vars,
      (k'.lvl[w]?.getD 0#32).toNat =
        if w = v then alvl.toNat else (k.lvl[w]?.getD 0#32).toNat := fun w _ => by
    by_cases he : w = v
    · subst he; simp [k', List.getElem?_set_self (by rw [hlen.lvl_len]; exact hv_lt)]
    · simp [k', he, List.getElem?_set_ne (Ne.symm he)]
  have hvals_get : ∀ l < 2 * k.cur_vars,
      k'.vals[l]?.getD 0#8 =
        if l = lit.toNat ^^^ 1 then 0xFF#8 else if l = lit.toNat then 1#8
        else k.vals[l]?.getD 0#8 := fun l hl => by
    have hcm := hlen.cur_vars_le
    by_cases h1 : l = lit.toNat ^^^ 1
    · subst h1; dsimp only [k']; simp only [↓reduceIte]
      rw [List.getElem?_set_self (by simp [hlen.vals_len]; omega)]; rfl
    · dsimp only [k']; simp only [h1, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : l = lit.toNat
      · subst h2; simp only [↓reduceIte]
        rw [List.getElem?_set_self (by rw [hlen.vals_len]; omega)]; rfl
      · simp only [h2, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h2)]
  have hrsn_get : ∀ w < k.cur_vars,
      k'.rsns[w]?.getD 0xFFFFFFFF#32 =
        if w = v then rsn' else k.rsns[w]?.getD 0xFFFFFFFF#32 := fun w _ => by
    by_cases he : w = v
    · subst he; simp [k', List.getElem?_set_self (by rw [hlen.rsns_len]; exact hv_lt)]
    · simp [k', he, List.getElem?_set_ne (Ne.symm he)]
  have hw' : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k') :=
    { ext_sound := hnw.ext_sound, inconsistent_sound := hnw.inconsistent_sound
      arena := { hnw.arena with len_ok := hnw.arena.len_ok }
      watches := fullWatchesInv_empty c F_cur k' hlen.cur_vars_le
      cur_level_le := by change k.cur_level ≤ k.trail_end + 1; omega
      trail_lits_lt := fun i hi => by
        change i < k.trail_end + 1 at hi
        change (k'.trl[i]?.getD 0#32).toNat < 2 * k.cur_vars; rw [htrl_get i hi]; split
        · exact hlit
        · exact htl_lt i (by omega)
      trail_vars_nodup := fun i j hi hj hveq => by
        change i < k.trail_end + 1 at hi; change j < k.trail_end + 1 at hj
        change (k'.trl[i]?.getD 0#32).toNat / 2 = (k'.trl[j]?.getD 0#32).toNat / 2 at hveq
        rw [htrl_get i hi, htrl_get j hj] at hveq
        split at hveq <;> split at hveq
        · omega
        · exact absurd hveq.symm (hnot_var j (by omega))
        · exact absurd hveq (hnot_var i (by omega))
        · exact hnw.trail_vars_nodup i j (show i < k.trail_end by omega)
            (show j < k.trail_end by omega) hveq
      vals_domain := fun l hl => by
        change l < 2 * k.cur_vars at hl; change _ ∨ _ ∨ _; rw [hvals_get l hl]
        split; · exact Or.inr (Or.inr rfl)
        split; · exact Or.inr (Or.inl rfl)
        exact hnw.vals_domain l hl
      vals_true_iff := fun l hl => by
        change l < 2 * k.cur_vars at hl
        change k'.vals[l]?.getD 0#8 = 1#8 ↔ ∃ i < k.trail_end + 1, (k'.trl[i]?.getD 0#32).toNat = l
        rw [hvals_get l hl]; constructor
        · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
          · simp [hneg] at h1
          · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
            · exact ⟨k.trail_end, by omega, by rw [htrl_get _ (by omega)]; simp [hpos]⟩
            · simp only [hpos, ↓reduceIte] at h1
              obtain ⟨i, hi, heq⟩ := (hnw.vals_true_iff l hl).mp h1
              have hi' : i < k.trail_end := hi
              exact ⟨i, by omega,
                by rw [htrl_get i (by omega)]; simp [show i ≠ k.trail_end by omega, heq]⟩
        · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
          by_cases hie : i = k.trail_end
          · simp only [hie, ↓reduceIte] at heq; subst heq; simp [Ne.symm hne_lit]
          · simp only [hie, ↓reduceIte] at heq
            have hlv : l / 2 ≠ v := by rw [← heq]; exact hnot_var i (by omega)
            have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
            have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
            simp only [h1, h2, ↓reduceIte]
            exact (hnw.vals_true_iff l hl).mpr ⟨i, show i < k.trail_end by omega, heq⟩
      vals_false_iff := fun l hl => by
        change l < 2 * k.cur_vars at hl
        change k'.vals[l]?.getD 0#8 = 0xFF#8 ↔
          ∃ i < k.trail_end + 1, (k'.trl[i]?.getD 0#32).toNat = l ^^^ 1
        rw [hvals_get l hl]; constructor
        · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
          · exact ⟨k.trail_end, by omega, by
              rw [htrl_get _ (by omega)]; simp only [↓reduceIte, hneg]
              exact (litNeg_litNeg _).symm⟩
          · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
            · simp [hpos] at h1
            · simp only [hpos, ↓reduceIte] at h1
              obtain ⟨i, hi, heq⟩ := (hnw.vals_false_iff l hl).mp h1
              have hi' : i < k.trail_end := hi
              exact ⟨i, by omega,
                by rw [htrl_get i (by omega)]; simp [show i ≠ k.trail_end by omega, heq]⟩
        · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
          by_cases hie : i = k.trail_end
          · simp only [hie, ↓reduceIte] at heq
            have hl_eq : l = lit.toNat ^^^ 1 := by
              have h := congrArg litNeg heq; have h1 : litNeg (l ^^^ 1) = l := litNeg_litNeg l
              rw [h1] at h; exact h.symm
            simp [hl_eq]
          · simp only [hie, ↓reduceIte] at heq
            have hlv : l / 2 ≠ v := by
              have h := hnot_var i (by omega); rw [heq] at h; rwa [fullInv_var_xor1] at h
            have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
            have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
            simp only [h1, h2, ↓reduceIte]
            exact (hnw.vals_false_iff l hl).mpr ⟨i, show i < k.trail_end by omega, heq⟩
      lvl_le := fun i hi => by
        change i < k.trail_end + 1 at hi
        change (k'.lvl[(k'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ k.cur_level
        rw [htrl_get i hi]; by_cases hie : i = k.trail_end
        · simp only [hie, ↓reduceIte]; rw [hlvl_get v (by omega)]; simpa using halvl_le
        · have hilt : i < k.trail_end := by omega
          simp only [hie, ↓reduceIte]
          rw [hlvl_get _ (by have := htl_lt i hilt; omega)]
          simp only [hnot_var i hilt, ↓reduceIte]; exact hnw.lvl_le i hilt
      dec_earliest := fun i j hi hj hleq hdec => by
        change i < k.trail_end + 1 at hi; change j < k.trail_end + 1 at hj
        dsimp only [withEmptyWatchesCore] at hleq hdec
        rw [htrl_get i hi] at hleq; rw [htrl_get j hj] at hleq hdec
        by_cases hje : j = k.trail_end
        · subst hje; simp only [↓reduceIte] at hdec
          rw [hlvl_get v (by omega), hrsn_get v (by omega)] at hdec; simp only [↓reduceIte] at hdec
          have hal0 : alvl ≠ 0#32 := fun h0 => by rw [h0] at hdec; exact absurd hdec.1 (by decide)
          exact absurd (by simpa [rsn', hal0] using hdec.2) hrsn_ne
        · by_cases hie : i = k.trail_end
          · omega
          · have hilt : i < k.trail_end := by omega
            have hjlt : j < k.trail_end := by omega
            simp only [hie, hje, ↓reduceIte] at hleq hdec
            rw [hlvl_get _ (by have := htl_lt i hilt; omega),
              hlvl_get _ (by have := htl_lt j hjlt; omega)] at hleq
            rw [hlvl_get _ (by have := htl_lt j hjlt; omega),
              hrsn_get _ (by have := htl_lt j hjlt; omega)] at hdec
            simp only [hnot_var i hilt, hnot_var j hjlt, ↓reduceIte] at hleq hdec
            exact hnw.dec_earliest i j hilt hjlt hleq hdec
      levels_inhabited := fun L hL1 hLle => by
        obtain ⟨i, hi, hli⟩ := hnw.levels_inhabited L hL1 hLle
        have hi' : i < k.trail_end := hi
        refine ⟨i, by change i < k.trail_end + 1; omega, ?_⟩
        change (k'.lvl[(k'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = L
        rw [htrl_get i (by omega)]; simp only [show i ≠ k.trail_end by omega, ↓reduceIte]
        rw [hlvl_get _ (by have := htl_lt i hi'; omega)]; simp [hnot_var i hi', hli]
      level0_sound := fun i hi hli => by
        change i < k.trail_end + 1 at hi
        change (k'.lvl[(k'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 at hli
        change (cnfOfClauses F_cur).EntailsClause (cnfClause [(k'.trl[i]?.getD 0#32).toNat])
        rw [htrl_get i hi] at hli ⊢
        by_cases hie : i = k.trail_end
        · simp only [hie, ↓reduceIte] at hli ⊢
          rw [hlvl_get v (by omega)] at hli; simp only [↓reduceIte] at hli
          exact hl0 (BitVec.eq_of_toNat_eq (by simpa using hli))
        · have hilt : i < k.trail_end := by omega
          simp only [hie, ↓reduceIte] at hli ⊢
          rw [hlvl_get _ (by have := htl_lt i hilt; omega)] at hli
          simp only [hnot_var i hilt, ↓reduceIte] at hli; exact hnw.level0_sound i hilt hli
      trail_pos_inv := fun i hi => by
        change i < k.trail_end + 1 at hi
        change (k'.trail_pos[(k'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = i
        rw [htrl_get i hi]; by_cases hie : i = k.trail_end
        · subst hie; simp only [↓reduceIte]; dsimp only [k']
          rw [List.getElem?_set_self (by rw [hlen.trail_pos_len]; exact hv_lt),
            Option.getD_some, bv32_ofNat_toNat hte_lt32]
        · have hilt : i < k.trail_end := by omega
          simp only [hie, ↓reduceIte]; dsimp only [k']
          rw [List.getElem?_set_ne (Ne.symm (hnot_var i hilt))]; exact hnw.trail_pos_inv i hilt
      level0_rsn_none := fun idx hidx hli => by
        change idx < k.trail_end + 1 at hidx
        dsimp only [withEmptyWatchesCore] at hli ⊢; rw [htrl_get idx hidx] at hli ⊢
        by_cases hie : idx = k.trail_end
        · simp only [hie, ↓reduceIte] at hli ⊢
          rw [hlvl_get v (by omega)] at hli; simp only [↓reduceIte] at hli
          rw [hrsn_get v (by omega)]
          have hz : alvl = 0#32 := BitVec.eq_of_toNat_eq (by simpa using hli)
          simp [rsn', hz]
        · have hilt : idx < k.trail_end := by omega
          simp only [hie, ↓reduceIte] at hli ⊢; have hnv := hnot_var idx hilt
          rw [hlvl_get _ (by have := htl_lt idx hilt; omega)] at hli
          simp only [hnv, ↓reduceIte] at hli
          rw [hrsn_get _ (by have := htl_lt idx hilt; omega)]
          simp only [hnv, ↓reduceIte]; exact hnw.level0_rsn_none idx hilt hli
      frame_trail_lt := fun L hL => by
        have hft : (k.frame_trail[L]?.getD 0#32).toNat ≤ k.trail_end := hnw.frame_trail_lt L hL
        change (k.frame_trail[L]?.getD 0#32).toNat ≤ k.trail_end + 1; omega
      frame_trail_mono := hnw.frame_trail_mono
      frame_trail_before_lt := fun L hL1 hLle i hi => by
        have hilt : i < k.trail_end := Nat.lt_of_lt_of_le hi (hnw.frame_trail_lt L hLle)
        change (k'.lvl[(k'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < L
        rw [htrl_get i (by omega)]; simp only [show i ≠ k.trail_end by omega, ↓reduceIte]
        rw [hlvl_get _ (by have := htl_lt i hilt; omega)]
        simp only [hnot_var i hilt, ↓reduceIte]; exact hnw.frame_trail_before_lt L hL1 hLle i hi
      frame_dec_lt := hnw.frame_dec_lt
      reason_inv := fun idx hidx hne => by
        change idx < k.trail_end + 1 at hidx
        dsimp only [withEmptyWatchesCore] at hne ⊢; rw [htrl_get idx hidx] at hne ⊢
        by_cases hie : idx = k.trail_end
        · simp only [hie, ↓reduceIte] at hne ⊢
          rw [hrsn_get v (by omega)] at hne ⊢; simp only [↓reduceIte] at hne ⊢
          by_cases hal0 : alvl = 0#32
          · simp [rsn', hal0] at hne
          · have hrs := hrsn hal0; simp only [rsn', hal0, ↓reduceIte] at hne hrs ⊢
            by_cases hbin : (rsn &&& 0x80000000#32) ≠ 0#32
            · rw [ite_eq_left hbin] at hrs ⊢
              obtain ⟨m, hm, hmeq, hlvl_le⟩ := hrs.2.2
              refine ⟨hrs.1, hrs.2.1, m, hm, ?_, ?_⟩
              · rw [htrl_get m (by omega)]; simp [show m ≠ k.trail_end by omega, hmeq]
              · have hot_v : (rsn &&& 0x7FFFFFFF#32).toNat / 2 ≠ v := by
                  intro heqv; have hme := hnot_var m hm; rw [hmeq] at hme
                  exact hme (by simpa [fullInv_var_xor1] using heqv)
                rw [hlvl_get v (by omega), hlvl_get _ (by have := hrs.1; omega)]
                rw [ite_eq_left rfl, ite_eq_right hot_v]; exact hlvl_le
            · rw [ite_eq_right hbin] at hrs ⊢
              refine ⟨hrs.1, hrs.2.1, fun q hq => ?_⟩
              have hq' : q ∈ fullArenaClauseLitsCore k rsn.toNat := hq
              refine (hrs.2.2 q hq').elim Or.inl fun ⟨m, hm, hmeq, hlvl_le⟩ =>
                Or.inr ⟨m, hm, ?_, ?_⟩
              · rw [htrl_get m (by omega)]; simp [show m ≠ k.trail_end by omega, hmeq]
              · have hq_lt : q < 2 * k.cur_vars := hnw.arena.lits_lt _ hrs.1 hrs.2.1 q hq'
                have hqv : q / 2 ≠ v := by
                  intro heqv; have hme := hnot_var m hm; rw [hmeq] at hme
                  exact hme (by simpa [fullInv_var_xor1] using heqv)
                rw [hlvl_get v (by omega), hlvl_get _ (by omega)]; simpa [hqv] using hlvl_le
        · have hilt : idx < k.trail_end := by omega
          simp only [hie, ↓reduceIte] at hne ⊢; have hnv := hnot_var idx hilt
          rw [hrsn_get _ (by have := htl_lt idx hilt; omega)] at hne ⊢
          simp only [hnv, ↓reduceIte] at hne ⊢
          have hrs := hnw.reason_inv idx hilt hne
          by_cases hbin : (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
              0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
          · rw [ite_eq_left hbin] at hrs ⊢
            obtain ⟨m, hm, hmeq, hlvl_le⟩ := hrs.2.2
            refine ⟨hrs.1, hrs.2.1, m, hm, ?_, ?_⟩
            · rw [htrl_get m (by omega)]; simp [show m ≠ k.trail_end by omega, hmeq]
            · have hot_v : ((k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
                  0xFFFFFFFF#32) &&& 0x7FFFFFFF#32).toNat / 2 ≠ v := by
                intro heqv; have hme := hnot_var m (by omega); rw [hmeq] at hme
                exact hme (by simpa [fullInv_var_xor1] using heqv)
              have hot_lt : ((k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
                  0xFFFFFFFF#32) &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars := hrs.1
              rw [hlvl_get _ (by omega), hlvl_get _ (by have := htl_lt idx hilt; omega)]
              rw [ite_eq_right hot_v, ite_eq_right hnv]; exact hlvl_le
          · rw [ite_eq_right hbin] at hrs ⊢
            refine ⟨hrs.1, hrs.2.1, fun q hq => ?_⟩
            refine (hrs.2.2 q hq).elim Or.inl fun ⟨m, hm, hmeq, hlvl_le⟩ => Or.inr ⟨m, hm, ?_, ?_⟩
            · rw [htrl_get m (by omega)]; simp [show m ≠ k.trail_end by omega, hmeq]
            · have hq_lt : q < 2 * k.cur_vars := hnw.arena.lits_lt _ hrs.1 hrs.2.1 q hq
              have hqv : q / 2 ≠ v := by
                intro heqv; have hme := hnot_var m (by omega); rw [hmeq] at hme
                exact hme (by simpa [fullInv_var_xor1] using heqv)
              rw [hlvl_get _ (by omega), hlvl_get _ (by have := htl_lt idx hilt; omega)]
              simpa [hnv, hqv] using hlvl_le
      reason_lit_mem := fun idx hidx hne hlg => by
        change idx < k.trail_end + 1 at hidx
        dsimp only [withEmptyWatchesCore] at hne hlg ⊢; rw [htrl_get idx hidx] at hne hlg ⊢
        by_cases hie : idx = k.trail_end
        · simp only [hie, ↓reduceIte] at hne hlg ⊢
          rw [hrsn_get v (by omega)] at hne hlg ⊢; simp only [↓reduceIte] at hne hlg ⊢
          by_cases hal0 : alvl = 0#32
          · simp [rsn', hal0] at hne
          · simp only [rsn', hal0, ↓reduceIte] at hne hlg ⊢; exact hrsn_mem hal0 hlg
        · have hilt : idx < k.trail_end := by omega
          simp only [hie, ↓reduceIte] at hne hlg ⊢; have hnv := hnot_var idx hilt
          rw [hrsn_get _ (by have := htl_lt idx hilt; omega)] at hne hlg ⊢
          simp only [hnv, ↓reduceIte] at hne hlg ⊢; exact hnw.reason_lit_mem idx hilt hne hlg }
  refine ⟨hw', ?_, ⟨by dsimp [k']; omega, fun i hi => List.getElem?_set_ne (by omega),
    fun i hi => List.getElem?_set_ne (Ne.symm (hnot_var i hi))⟩⟩
  obtain ⟨i, hi, heq⟩ := (hnw.vals_false_iff not_lit hnot_lt).mp hnot_false
  have hi' : i < k.trail_end := hi
  refine (hw'.vals_false_iff not_lit hnot_lt).mpr ⟨i, by change i < k.trail_end + 1; omega, ?_⟩
  rw [htrl_get i (by omega)]; simp [show i ≠ k.trail_end by omega, heq]

/-- Chronological binary-watch `full_assign_lvl` at `alvl = lvl[not_lit / 2]`. -/
theorem full_bin_assign_nw_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c)
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k))
    {not_lit other : BitVec 32} {flags' : List (BitVec 32)} {unas' unfl' : BitVec 64}
    (hnot_lt : not_lit.toNat < 2 * k.cur_vars) (hother_lt : other.toNat < 2 * k.cur_vars)
    (hun : k.vals[other.toNat]?.getD 0#8 = 0#8)
    (hnot_false : k.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [not_lit.toNat, other.toNat])) :
    let bin_rsn := (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    let alvl := k.lvl[not_lit.toNat / 2]?.getD 0#32
    let v := other.toNat / 2
    let rsn' := if alvl = 0#32 then 0xFFFFFFFF#32 else bin_rsn
    let k' : FullCoreState :=
      { k with
        vals := (k.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
        flags := flags', lvl := k.lvl.set v alvl, rsns := k.rsns.set v rsn'
        trl := k.trl.set k.trail_end other
        trail_pos := k.trail_pos.set v (BitVec.ofNat 32 k.trail_end)
        trail_end := k.trail_end + 1, unassigned := unas', unflushed := unfl' }
    FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k') ∧
    k'.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 ∧ FullTrailExt k k' := by
  intro bin_rsn alvl v rsn' k'
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv; have hcv := hlen.cur_vars_le
  obtain ⟨hne_ff, hflag, hlo⟩ := bv32_bin_rsn_props (x := not_lit) (by omega)
  obtain ⟨i, hi, hieq⟩ := (hnw.vals_false_iff not_lit.toNat hnot_lt).mp hnot_false
  have hvar_i : (k.trl[i]?.getD 0#32).toNat / 2 = not_lit.toNat / 2 := by
    rw [hieq, fullInv_var_xor1]
  have halvl_le : alvl.toNat ≤ k.cur_level := by
    have := hnw.lvl_le i hi; rwa [hvar_i] at this
  exact unitAssign_preserves_fullWitness_nw hlen hnw hother_lt hun hnot_lt hnot_false
    hne_ff halvl_le
    (fun hl0 => entails_of_mem_or_false hent fun l hl => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · have hli : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
          rw [hvar_i]; change alvl.toNat = 0; rw [hl0]; rfl
        exact Or.inr (by have hs := hnw.level0_sound i hi hli; rwa [hieq] at hs)
      · exact Or.inl (by simp))
    (fun _ => by
      dsimp only [bin_rsn]; simp only [hflag, ne_eq, not_false_eq_true, ↓reduceIte, hlo]
      exact ⟨hnot_lt, cnfClause_swap2 hent, i, hi, hieq, Nat.le_refl _⟩)
    (fun _ hlg => absurd hlg hflag)

/-- Chronological large-clause `full_assign_lvl` at `alvl = full_assign_level(h, cref, other)`. -/
theorem full_large_assign_nw_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c)
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k))
    {cref other alvl : BitVec 32} {not_lit : Nat}
    {flags' : List (BitVec 32)} {unas' unfl' : BitVec 64}
    (hcr_lt : cref.toNat < 0x80000000) (hcref : cref.toNat ∈ fullArenaClauseRefsCore k)
    (hng : fullArenaClauseGarbCore k cref.toNat = false)
    (hother_lt : other.toNat < 2 * k.cur_vars) (hun : k.vals[other.toNat]?.getD 0#8 = 0#8)
    (hnot_lt : not_lit < 2 * k.cur_vars) (hnot_false : k.vals[not_lit]?.getD 0#8 = 0xFF#8)
    (hother_mem : other.toNat ∈ fullArenaClauseLitsCore k cref.toNat)
    (hunit : ∀ l ∈ fullArenaClauseLitsCore k cref.toNat,
      l = other.toNat ∨ k.vals[l]?.getD 0#8 = 0xFF#8)
    (hmax_ge : ∀ l ∈ fullArenaClauseLitsCore k cref.toNat, l ≠ other.toNat →
      (k.lvl[l / 2]?.getD 0#32).toNat ≤ alvl.toNat)
    (hmax_att : alvl = 0#32 ∨ ∃ l ∈ fullArenaClauseLitsCore k cref.toNat,
      l ≠ other.toNat ∧ alvl = k.lvl[l / 2]?.getD 0#32) :
    let v := other.toNat / 2
    let rsn' := if alvl = 0#32 then 0xFFFFFFFF#32 else cref
    let k' : FullCoreState :=
      { k with
        vals := (k.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
        flags := flags', lvl := k.lvl.set v alvl, rsns := k.rsns.set v rsn'
        trl := k.trl.set k.trail_end other
        trail_pos := k.trail_pos.set v (BitVec.ofNat 32 k.trail_end)
        trail_end := k.trail_end + 1, unassigned := unas', unflushed := unfl' }
    FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k') ∧
    k'.vals[not_lit]?.getD 0#8 = 0xFF#8 ∧ FullTrailExt k k' := by
  intro v rsn' k'
  have hcr_ne_ff : cref ≠ 0xFFFFFFFF#32 := fun h => by
    rw [h] at hcr_lt; revert hcr_lt; decide
  have hcr_flag : (cref &&& 0x80000000#32) = 0#32 := by
    apply BitVec.eq_of_toNat_eq
    have hhi : (0x80000000#32).toNat = 2 ^ 31 := by decide
    simp only [BitVec.toNat_and, hhi, BitVec.toNat_ofNat]
    exact Nat.eq_of_testBit_eq fun i => by
      rw [Nat.testBit_and, Nat.testBit_two_pow]
      by_cases hi : 31 = i
      · subst hi
        have hlt31 : cref.toNat < 2 ^ 31 := hcr_lt
        simp [Nat.testBit_lt_two_pow hlt31]
      · simp [hi]
  have halvl_le : alvl.toNat ≤ k.cur_level := by
    rcases hmax_att with rfl | ⟨l, hl, hne, rfl⟩
    · exact Nat.zero_le _
    · have hfl := (hunit l hl).resolve_left hne
      obtain ⟨i, hi, hieq⟩ := (hnw.vals_false_iff l (hnw.arena.lits_lt _ hcref hng l hl)).mp hfl
      have := hnw.lvl_le i hi; rwa [hieq, fullInv_var_xor1] at this
  exact unitAssign_preserves_fullWitness_nw hlen hnw hother_lt hun hnot_lt hnot_false
    hcr_ne_ff halvl_le
    (fun hl0 => entails_of_mem_or_false (hnw.arena.entails cref.toNat hcref hng) fun l hl => by
      rcases hunit l hl with rfl | hfl
      · exact Or.inl (by simp)
      · have hne : l ≠ other.toNat := fun heq => by rw [heq, hun] at hfl; cases hfl
        have hlt := hnw.arena.lits_lt cref.toNat hcref hng l hl
        obtain ⟨i, hi, hieq⟩ := (hnw.vals_false_iff l hlt).mp hfl
        have hle := hmax_ge l hl hne
        have hli : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
          rw [hieq, fullInv_var_xor1]; rw [hl0] at hle; simp at hle; exact hle
        exact Or.inr (by have hs := hnw.level0_sound i hi hli; rwa [hieq] at hs))
    (fun _ => by
      simp only [hcr_flag, ne_eq, not_true_eq_false, ↓reduceIte]
      refine ⟨hcref, hng, fun q hq => ?_⟩
      rcases hunit q hq with rfl | hfq
      · exact Or.inl rfl
      · have hne : q ≠ other.toNat := fun heq => by rw [heq, hun] at hfq; cases hfq
        obtain ⟨m, hm, hmeq⟩ :=
          (hnw.vals_false_iff q (hnw.arena.lits_lt cref.toNat hcref hng q hq)).mp hfq
        exact Or.inr ⟨m, hm, hmeq, hmax_ge q hq hne⟩)
    (fun _ _ => hother_mem)

/-! ## 3. Mid-compaction watch-slice invariant (`SplitWatchesInv`) -/

/-- Mid-compaction watch invariant for `full_prop_lit`: `not_lit`'s slice `[off, end_v)` is split
into valid compacted prefix `[off, q)` and valid uninspected suffix `[p, end_v)`. -/
structure SplitWatchesInv (F_cur : List (List Nat)) (k : FullCoreState)
    (not_lit off q p end_v : Nat) : Prop where
  layout : WatchStackLayout k
  off_eq : fullWatchOffCore k not_lit = off
  sz_eq : fullWatchSizeCore k not_lit = end_v - off
  sz_pos : 0 < end_v - off
  q_ge : off ≤ q
  q_le_p : q ≤ p
  p_le_end : p ≤ end_v
  other_slices : ∀ l < 2 * k.cur_vars, l ≠ not_lit →
    WatchSliceOk F_cur k l (fullWatchOffCore k l) (fullWatchSizeCore k l)
  kept_slice : WatchSliceOk F_cur k not_lit off (q - off)
  rem_slice : WatchSliceOk F_cur k not_lit p (end_v - p)

theorem SplitWatchesInv.init {F_cur : List (List Nat)} {k : FullCoreState} {not_lit : Nat}
    (hnot_lt : not_lit < 2 * k.cur_vars)
    (hwat : WatchesInv F_cur k) (hpos : 0 < fullWatchSizeCore k not_lit) :
    SplitWatchesInv F_cur k not_lit (fullWatchOffCore k not_lit) (fullWatchOffCore k not_lit)
      (fullWatchOffCore k not_lit) (fullWatchOffCore k not_lit + fullWatchSizeCore k not_lit) :=
  { layout := hwat.layout, off_eq := rfl, sz_eq := by omega, sz_pos := by omega
    q_ge := Nat.le_refl _, q_le_p := Nat.le_refl _, p_le_end := by omega
    other_slices := fun l hl _ => hwat.slices l hl
    kept_slice := by simp only [Nat.sub_self]; exact .empty
    rem_slice := by simpa only [Nat.add_sub_cancel_left] using hwat.slices not_lit hnot_lt }

theorem SplitWatchesInv.with_nonwatch {F_cur : List (List Nat)} {k k' : FullCoreState}
    {not_lit off q p end_v : Nat} (h : SplitWatchesInv F_cur k not_lit off q p end_v)
    (hvars : k'.cur_vars = k.cur_vars) (hwv : k'.wvec = k.wvec) (hws : k'.wstk = k.wstk)
    (hwl : k'.wlen = k.wlen) (href : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k) :
    SplitWatchesInv F_cur k' not_lit off q p end_v := by
  have hF : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ hx => hx
  have hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k' :=
    fun _ hr => href ▸ hr
  have hwo : ∀ l, fullWatchOffCore k' l = fullWatchOffCore k l := fun l => by
    unfold fullWatchOffCore; rw [hwv]
  have hwsz : ∀ l, fullWatchSizeCore k' l = fullWatchSizeCore k l := fun l => by
    unfold fullWatchSizeCore; rw [hwv]
  refine
    { layout := h.layout.with_wstk hvars hwv hws hwl
      off_eq := by rw [hwo]; exact h.off_eq, sz_eq := by rw [hwsz]; exact h.sz_eq
      sz_pos := h.sz_pos, q_ge := h.q_ge, q_le_p := h.q_le_p, p_le_end := h.p_le_end
      other_slices := fun l hl hne => by
        rw [hwo, hwsz]
        exact WatchSliceOk.mono (k := k) (k' := k') hF (by omega) hsub (fun _ _ _ => by rw [hws])
          (h.other_slices l (hvars ▸ hl) hne)
      kept_slice :=
        WatchSliceOk.mono (k := k) (k' := k') hF (by omega) hsub (fun _ _ _ => by rw [hws])
          h.kept_slice
      rem_slice :=
        WatchSliceOk.mono (k := k) (k' := k') hF (by omega) hsub (fun _ _ _ => by rw [hws])
          h.rem_slice }

theorem SplitWatchesInv.advance_rem {F_cur : List (List Nat)} {k : FullCoreState}
    {not_lit off q p p' end_v : Nat}
    (h : SplitWatchesInv F_cur k not_lit off q p end_v) (hp : p ≤ p') (hp' : p' ≤ end_v)
    (hrem' : WatchSliceOk F_cur k not_lit p' (end_v - p')) :
    SplitWatchesInv F_cur k not_lit off q p' end_v :=
  { h with q_le_p := Nat.le_trans h.q_le_p hp, p_le_end := hp', rem_slice := hrem' }

theorem SplitWatchesInv.write_bin {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    {not_lit off q p end_v : Nat} {w0 : BitVec 32}
    (h : SplitWatchesInv F_cur k not_lit off q (p + 1) end_v)
    (hcv : k.cur_vars ≤ c.max_vars) (hnot_lt : not_lit < 2 * k.cur_vars)
    (hqp : q ≤ p) (hq_lt : q < k.wstk.length)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [not_lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    SplitWatchesInv F_cur { k with wstk := k.wstk.set q w0 }
      not_lit off (q + 1) (p + 1) end_v := by
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have hne_ff : w0 ≠ 0xFFFFFFFF#32 := binWatchWord_ne_sentinel (by omega)
  have hF : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ hx => hx
  let k' : FullCoreState := { k with wstk := k.wstk.set q w0 }
  have hq_range : off ≤ q ∧ q < end_v := ⟨h.q_ge, by have := h.p_le_end; omega⟩
  refine
    { layout :=
        { bounds := h.layout.bounds, pos_off := h.layout.pos_off, disjoint := h.layout.disjoint
          no_sentinel := fun l hl j hj => by
            change (k.wstk.set q w0)[fullWatchOffCore k l + j]? ≠ some 0xFFFFFFFF#32
            by_cases he : fullWatchOffCore k l + j = q
            · rw [he, List.getElem?_set_self hq_lt]; simp [hne_ff]
            · rw [List.getElem?_set_ne (Ne.symm he)]; exact h.layout.no_sentinel l hl j hj }
      off_eq := h.off_eq, sz_eq := h.sz_eq, sz_pos := h.sz_pos
      q_ge := by omega, q_le_p := by omega, p_le_end := h.p_le_end
      other_slices := fun l hl hne => by
        change WatchSliceOk F_cur k' l (fullWatchOffCore k l) (fullWatchSizeCore k l)
        by_cases hsz0 : fullWatchSizeCore k l = 0
        · rw [hsz0]; exact .empty
        · have hdisj := h.layout.disjoint l not_lit hl hnot_lt hne (by omega)
            (by rw [h.sz_eq]; exact h.sz_pos)
          rw [h.off_eq, h.sz_eq] at hdisj
          exact WatchSliceOk.mono (k := k) (k' := k') hF (Nat.le_refl _) (fun _ hr => hr)
            (fun j hj1 hj2 => by dsimp only [k']; exact List.getElem?_set_ne (by omega))
            (h.other_slices l hl hne)
      kept_slice := by
        rw [show q + 1 - off = (q - off) + 1 by have := h.q_ge; omega]
        refine WatchSliceOk.append_bin (k := k) (k' := k') (p' := off) (Nat.le_refl _)
          (fun _ hr => hr) (fun j hj => by dsimp only [k']; exact List.getElem?_set_ne (by omega))
          h.kept_slice ?_ hflag hne_ff hlt hent
        dsimp only [k']; rw [show off + (q - off) = q by have := h.q_ge; omega,
          List.getElem?_set_self hq_lt]
      rem_slice := WatchSliceOk.mono (k := k) (k' := k') hF (Nat.le_refl _) (fun _ hr => hr)
        (fun j hj1 _ => by dsimp only [k']; exact List.getElem?_set_ne (by omega)) h.rem_slice }

theorem SplitWatchesInv.write_large {F_cur : List (List Nat)} {k : FullCoreState}
    {not_lit off q p end_v : Nat} {w0 cref : BitVec 32}
    (h : SplitWatchesInv F_cur k not_lit off q (p + 2) end_v)
    (hnot_lt : not_lit < 2 * k.cur_vars) (hqp : q ≤ p)
    (hq_lt : q < k.wstk.length) (hq1_lt : q + 1 < k.wstk.length)
    (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hlt : cref.toNat < 0x80000000) (href : cref.toNat ∈ fullArenaClauseRefsCore k) :
    SplitWatchesInv F_cur { k with wstk := (k.wstk.set q w0).set (q + 1) cref }
      not_lit off (q + 2) (p + 2) end_v := by
  have hne_w0 : w0 ≠ 0xFFFFFFFF#32 := fun hff => by
    rw [hff] at hflag; exact absurd hflag (by decide)
  have hne_cr : cref ≠ 0xFFFFFFFF#32 := fun hff => by rw [hff] at hlt; revert hlt; decide
  have hF : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ hx => hx
  let k' : FullCoreState := { k with wstk := (k.wstk.set q w0).set (q + 1) cref }
  have hq_range : off ≤ q ∧ q + 1 < end_v := ⟨h.q_ge, by have := h.p_le_end; omega⟩
  refine
    { layout :=
        { bounds := h.layout.bounds, pos_off := h.layout.pos_off, disjoint := h.layout.disjoint
          no_sentinel := fun l hl j hj => by
            change ((k.wstk.set q w0).set (q + 1) cref)[fullWatchOffCore k l + j]? ≠
              some 0xFFFFFFFF#32
            by_cases h1 : fullWatchOffCore k l + j = q + 1
            · rw [h1, List.getElem?_set_self (by simp; exact hq1_lt)]; simp [hne_cr]
            · rw [List.getElem?_set_ne (Ne.symm h1)]
              by_cases h0 : fullWatchOffCore k l + j = q
              · rw [h0, List.getElem?_set_self hq_lt]; simp [hne_w0]
              · rw [List.getElem?_set_ne (Ne.symm h0)]; exact h.layout.no_sentinel l hl j hj }
      off_eq := h.off_eq, sz_eq := h.sz_eq, sz_pos := h.sz_pos
      q_ge := by omega, q_le_p := by omega, p_le_end := h.p_le_end
      other_slices := fun l hl hne => by
        change WatchSliceOk F_cur k' l (fullWatchOffCore k l) (fullWatchSizeCore k l)
        by_cases hsz0 : fullWatchSizeCore k l = 0
        · rw [hsz0]; exact .empty
        · have hdisj := h.layout.disjoint l not_lit hl hnot_lt hne (by omega)
            (by rw [h.sz_eq]; exact h.sz_pos)
          rw [h.off_eq, h.sz_eq] at hdisj
          exact WatchSliceOk.mono (k := k) (k' := k') hF (Nat.le_refl _) (fun _ hr => hr)
            (fun j hj1 hj2 => by
              dsimp only [k']
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
            (h.other_slices l hl hne)
      kept_slice := by
        rw [show q + 2 - off = (q - off) + 2 by have := h.q_ge; omega]
        refine WatchSliceOk.append_large (k := k) (k' := k') (p' := off) (Nat.le_refl _)
          (fun _ hr => hr) (fun j hj => by
            dsimp only [k']
            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
          h.kept_slice ?_ ?_ hflag hlt href
        · dsimp only [k']; rw [show off + (q - off) = q by have := h.q_ge; omega,
            List.getElem?_set_ne (by omega), List.getElem?_set_self hq_lt]
        · dsimp only [k']; rw [show off + (q - off) + 1 = q + 1 by have := h.q_ge; omega,
            List.getElem?_set_self (by simp; exact hq1_lt)]
      rem_slice := WatchSliceOk.mono (k := k) (k' := k') hF (Nat.le_refl _) (fun _ hr => hr)
        (fun j hj1 _ => by
          dsimp only [k']
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]) h.rem_slice }

theorem SplitWatchesInv.after_push {F_cur : List (List Nat)} {k k' : FullCoreState}
    {not_lit repl off q p end_v : Nat} {w0 cref : BitVec 32} {pok : Bool}
    (h : SplitWatchesInv F_cur k not_lit off q p end_v)
    (hvars : k'.cur_vars = k.cur_vars)
    (hnot_lt : not_lit < 2 * k.cur_vars) (hrepl_lt : repl < 2 * k.cur_vars) (hne : repl ≠ not_lit)
    (href_eq : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k)
    (hlay' : WatchStackLayout k')
    (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hlt : cref.toNat < 0x80000000) (href : cref.toNat ∈ fullArenaClauseRefsCore k)
    (hpres_other : ∀ l < 2 * k.cur_vars, l ≠ repl →
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ j < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + j]? = k.wstk[fullWatchOffCore k l + j]?)
    (hpok_t : pok = true →
      fullWatchSizeCore k' repl = fullWatchSizeCore k repl + 2 ∧
      (∀ j < fullWatchSizeCore k repl,
        k'.wstk[fullWatchOffCore k' repl + j]? = k.wstk[fullWatchOffCore k repl + j]?) ∧
      k'.wstk[fullWatchOffCore k' repl + fullWatchSizeCore k repl]? = some w0 ∧
      k'.wstk[fullWatchOffCore k' repl + fullWatchSizeCore k repl + 1]? = some cref)
    (hpok_f : pok = false →
      fullWatchSizeCore k' repl = fullWatchSizeCore k repl ∧
      ∀ j < fullWatchSizeCore k repl,
        k'.wstk[fullWatchOffCore k' repl + j]? = k.wstk[fullWatchOffCore k repl + j]?) :
    let off' := fullWatchOffCore k' not_lit
    SplitWatchesInv F_cur k' not_lit off' (off' + (q - off)) (off' + (p - off))
      (off' + (end_v - off)) := by
  intro off'
  have hF : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ hx => hx
  have hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k' :=
    fun _ hr => href_eq ▸ hr
  obtain ⟨hsz_not, hget_not⟩ := hpres_other not_lit hnot_lt (Ne.symm hne)
  rw [h.off_eq, h.sz_eq] at hget_not
  have hq_ge := h.q_ge; have hq_le := h.q_le_p; have hp_le := h.p_le_end
  refine
    { layout := hlay', off_eq := rfl
      sz_eq := by rw [hsz_not, h.sz_eq]; omega
      sz_pos := by have := h.sz_pos; omega
      q_ge := by omega, q_le_p := by omega, p_le_end := by omega
      other_slices := fun l hl hln => by
        have hl0 : l < 2 * k.cur_vars := hvars ▸ hl
        by_cases hlr : l = repl
        · subst hlr; cases pok with
          | false =>
            obtain ⟨hsz_r, hget_r⟩ := hpok_f rfl; rw [hsz_r]
            exact WatchSliceOk.relocate (k := k) (k' := k') hF (by omega) hsub hget_r
              (h.other_slices l hl0 hln)
          | true =>
            obtain ⟨hsz_r, hget_r, hw0, hcr⟩ := hpok_t rfl; rw [hsz_r]
            exact WatchSliceOk.append_large (k := k) (k' := k') (by omega) hsub hget_r
              (h.other_slices l hl0 hln) hw0 hcr hflag hlt (hsub _ href)
        · obtain ⟨hsz_l, hget_l⟩ := hpres_other l hl0 hlr; rw [hsz_l]
          exact WatchSliceOk.relocate (k := k) (k' := k') hF (by omega) hsub hget_l
            (h.other_slices l hl0 hln)
      kept_slice := by
        rw [show off' + (q - off) - off' = q - off by omega]
        exact WatchSliceOk.relocate (k := k) (k' := k') hF (by omega) hsub
          (fun j hj => hget_not j (by omega)) h.kept_slice
      rem_slice := by
        rw [show off' + (end_v - off) - (off' + (p - off)) = end_v - p by omega]
        refine WatchSliceOk.relocate (k := k) (k' := k') hF (by omega) hsub (fun j hj => ?_)
          h.rem_slice
        have hj' := hget_not ((p - off) + j) (by omega)
        rwa [show off' + (p - off + j) = off' + (p - off) + j by omega,
          show off + (p - off + j) = p + j by omega] at hj' }

theorem SplitWatchesInv.finish {c : FullCfg} {F_cur : List (List Nat)} {k0 : FullCoreState}
    {not_lit off q0 p0 end_v : Nat} {wstk' : List (BitVec 32)} {wu' : BitVec 64}
    (h : SplitWatchesInv F_cur k0 not_lit off q0 p0 end_v)
    (hnot_lt : not_lit < 2 * k0.cur_vars) (hcv : k0.cur_vars ≤ c.max_vars)
    (hwv_len : k0.wvec.length = 4 * c.max_vars) (hwlen_le : k0.wlen ≤ c.wcap)
    (hkeep_pre : ∀ j, off ≤ j → j < q0 → wstk'[j]? = k0.wstk[j]?)
    (hkeep_suf : ∀ j < end_v - p0, wstk'[q0 + j]? = k0.wstk[p0 + j]?)
    (hkeep_out : ∀ j, (j < off ∨ end_v ≤ j) → wstk'[j]? = k0.wstk[j]?) :
    let q_fin := q0 + (end_v - p0)
    let k' : FullCoreState :=
      { k0 with
        wstk := wstk'
        wvec := k0.wvec.set (2 * not_lit + 1) (BitVec.ofNat 32 (q_fin - off))
        wusable := wu' }
    WatchesInv F_cur k' := by
  intro q_fin k'
  have hwcap := c.hwcap; unfold dimacsBound at hwcap
  have hnot_bd : off + (end_v - off) ≤ k0.wlen := by
    have := h.layout.bounds not_lit hnot_lt; rwa [h.off_eq, h.sz_eq] at this
  have hqfin_le : q_fin ≤ end_v := by
    dsimp only [q_fin]; have := h.q_le_p; have := h.p_le_end; omega
  have hsz_lt32 : q_fin - off < 2 ^ 32 := by omega
  have hwo : ∀ l, fullWatchOffCore k' l = fullWatchOffCore k0 l := fun l => by
    unfold fullWatchOffCore; dsimp only [k']; rw [List.getElem?_set_ne (by omega)]
  have hwsz_ne : ∀ l, l ≠ not_lit → fullWatchSizeCore k' l = fullWatchSizeCore k0 l :=
    fun l hne => by
    unfold fullWatchSizeCore; dsimp only [k']; rw [List.getElem?_set_ne (by omega)]
  have hwsz_not : fullWatchSizeCore k' not_lit = q_fin - off := by
    unfold fullWatchSizeCore; dsimp only [k']
    rw [List.getElem?_set_self (by omega), Option.getD_some, bv32_ofNat_toNat hsz_lt32]
  have hF : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ hx => hx
  have hslice_not : WatchSliceOk F_cur k' not_lit off (q_fin - off) := by
    have hpre : WatchSliceOk F_cur k' not_lit off (q0 - off) :=
      WatchSliceOk.mono (k := k0) (k' := k') hF (Nat.le_refl _) (fun _ hr => hr)
        (fun j hj1 hj2 => hkeep_pre j hj1 (by have := h.q_ge; omega)) h.kept_slice
    have hsuf : WatchSliceOk F_cur k' not_lit q0 (end_v - p0) :=
      WatchSliceOk.relocate (k := k0) (k' := k') hF (Nat.le_refl _) (fun _ hr => hr)
        hkeep_suf h.rem_slice
    rw [show q_fin - off = (q0 - off) + (end_v - p0) by dsimp only [q_fin]; have := h.q_ge; omega]
    exact watchSlice_append hpre ((show off + (q0 - off) = q0 by have := h.q_ge; omega).symm ▸ hsuf)
  have hslice_all : ∀ l < 2 * k'.cur_vars,
      WatchSliceOk F_cur k' l (fullWatchOffCore k' l) (fullWatchSizeCore k' l) := by
    intro l hl; by_cases hln : l = not_lit
    · subst hln; rw [hwo, h.off_eq, hwsz_not]; exact hslice_not
    · rw [hwo, hwsz_ne l hln]
      by_cases hsz0 : fullWatchSizeCore k0 l = 0
      · rw [hsz0]; exact .empty
      · have hdisj := h.layout.disjoint l not_lit hl hnot_lt hln (by omega)
          (by rw [h.sz_eq]; exact h.sz_pos)
        rw [h.off_eq, h.sz_eq] at hdisj
        exact WatchSliceOk.mono (k := k0) (k' := k') hF (Nat.le_refl _) (fun _ hr => hr)
          (fun j hj1 hj2 => hkeep_out j (by omega)) (h.other_slices l hl hln)
  refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_)
    (fun l1 l2 h1 h2 hne hp1 hp2 => ?_) hslice_all
  · by_cases hln : l = not_lit
    · subst hln; rw [hwo, h.off_eq, hwsz_not]; dsimp only [k']; omega
    · rw [hwo, hwsz_ne l hln]; exact h.layout.bounds l hl
  · rw [hwo]; by_cases hln : l = not_lit
    · subst hln; exact h.layout.pos_off l hl (by rw [h.sz_eq]; exact h.sz_pos)
    · exact h.layout.pos_off l hl (by rwa [← hwsz_ne l hln])
  · rw [hwo, hwo]; by_cases h1n : l1 = not_lit
    · subst h1n; rw [h.off_eq, hwsz_not, hwsz_ne l2 (Ne.symm hne)]
      have hd := h.layout.disjoint l1 l2 h1 h2 hne (by rw [h.sz_eq]; exact h.sz_pos)
        (by rwa [← hwsz_ne l2 (Ne.symm hne)])
      rw [h.off_eq, h.sz_eq] at hd; omega
    · by_cases h2n : l2 = not_lit
      · subst h2n; rw [h.off_eq, hwsz_not, hwsz_ne l1 h1n]
        have hd := h.layout.disjoint l1 l2 h1 h2 hne (by rwa [← hwsz_ne l1 h1n])
          (by rw [h.sz_eq]; exact h.sz_pos)
        rw [h.off_eq, h.sz_eq] at hd; omega
      · rw [hwsz_ne l1 h1n, hwsz_ne l2 h2n]
        exact h.layout.disjoint l1 l2 h1 h2 hne (by rwa [← hwsz_ne l1 h1n])
          (by rwa [← hwsz_ne l2 h2n])

/-! ## 4. `full_prop_lit` framing mask, `PropLitInv`, and branch helpers -/

/-- Conflict/OOM witness predicate for `full_prop_lit` (`ok = false` postcondition). -/
def PropLitConfl (F_cur : List (List Nat)) (ignore_ref : BitVec 64) (k : FullCoreState) : Prop :=
  k.oom ≠ 0#64 ∨ (FullConflOkW F_cur k ∧ (k.confl_type = 2#64 → k.confl_ref ≠ ignore_ref))

theorem PropLitConfl.congr {F_cur : List (List Nat)} {ignore_ref : BitVec 64}
    {k k' : FullCoreState} (h : PropLitConfl F_cur ignore_ref k)
    (hcv : k'.cur_vars = k.cur_vars) (hoom : k'.oom = k.oom) (hct : k'.confl_type = k.confl_type)
    (hcr : k'.confl_ref = k.confl_ref) (hc0 : k'.confl_lit0 = k.confl_lit0)
    (hc1 : k'.confl_lit1 = k.confl_lit1) (hv : k'.vals = k.vals)
    (hal : k'.arena_len = k.arena_len) (har : k'.arena = k.arena) :
    PropLitConfl F_cur ignore_ref k' := by
  have href : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k := by
    unfold fullArenaClauseRefsCore; rw [hal, har]
  have hgb : ∀ r, fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := fun r => by
    unfold fullArenaClauseGarbCore fullArenaHdrCore; rw [har]
  have hlt : ∀ r, fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := fun r => by
    unfold fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har]
  unfold PropLitConfl FullConflOkW at h ⊢
  rw [hoom, hct, hcr, hc0, hc1, hv, hcv, href, hgb, hlt]
  exact h

/-- Inductive array-copy step for Loop 2 of `full_prop_lit` (`wstk[q] = wstk[p]`). -/
theorem propLit_loop2_step {w0 wc : List (BitVec 32)} {off q0 p0 p end_v : Nat}
    (hoff_q0 : off ≤ q0) (hq0_p0 : q0 ≤ p0) (hp0_p : p0 ≤ p) (hp_end : p < end_v)
    (hp_lt : p < wc.length) (hq_lt : q0 + (p - p0) < wc.length)
    (hpre : ∀ k, off ≤ k → k < q0 → wc[k]? = w0[k]?)
    (hsuf : ∀ k < p - p0, wc[q0 + k]? = w0[p0 + k]?)
    (hrem : ∀ k, p ≤ k → k < end_v → wc[k]? = w0[k]?)
    (hout : ∀ k, (k < off ∨ end_v ≤ k) → wc[k]? = w0[k]?) :
    let wc' := wc.set (q0 + (p - p0)) (wc[p]'hp_lt)
    (∀ k, off ≤ k → k < q0 → wc'[k]? = w0[k]?) ∧
    (∀ k < p + 1 - p0, wc'[q0 + k]? = w0[p0 + k]?) ∧
    (∀ k, p + 1 ≤ k → k < end_v → wc'[k]? = w0[k]?) ∧
    (∀ k, (k < off ∨ end_v ≤ k) → wc'[k]? = w0[k]?) := by
  intro wc'
  refine ⟨fun k hk1 hk2 => (List.getElem?_set_ne (by omega)).trans (hpre k hk1 hk2),
    fun k hk => ?_,
    fun k hk1 hk2 => (List.getElem?_set_ne (by omega)).trans (hrem k (by omega) hk2),
    fun k hk => (List.getElem?_set_ne (by omega)).trans (hout k hk)⟩
  by_cases hke : k = p - p0
  · subst hke
    rw [List.getElem?_set_self hq_lt, ← List.getElem?_eq_getElem hp_lt]
    have hp_eq : p0 + (p - p0) = p := by omega
    rw [hp_eq]; exact hrem p (Nat.le_refl _) hp_end
  · exact (List.getElem?_set_ne (by omega)).trans (hsuf k (by omega))

/-- Inductive sentinel-fill step for Loop 3 of `full_prop_lit` (`wstk[k] = 0xFFFFFFFFu`). -/
theorem propLit_loop3_step {w2 wk : List (BitVec 32)} {q_fin k end_v : Nat}
    (hq_k : q_fin ≤ k) (hk_end : k < end_v)
    (hkeep : ∀ i, (i < q_fin ∨ end_v ≤ i) → wk[i]? = w2[i]?) :
    ∀ i, (i < q_fin ∨ end_v ≤ i) → (wk.set k 0xFFFFFFFF#32)[i]? = w2[i]? := fun i hi =>
  (List.getElem?_set_ne (by omega)).trans (hkeep i hi)

def propLitCoreMask (k : FullCoreState) : FullCoreState :=
  { k with
    vals := [], flags := [], lvl := [], rsns := [], trl := [], trail_pos := [], trail_end := 0,
    unassigned := 0#64, unflushed := 0#64, wvec := [], arena := [], wstk := [], wlen := 0,
    wusable := 0#64, confl_type := 0#64, confl_ref := 0#64, confl_lit0 := 0#64,
    confl_lit1 := 0#64, oom := 0#64 }

theorem propLit_eq_upd {s st : FullState} (h : AgreesExcept propLitCoreMask s.core st.core)
    (hsc : st.scratch = { s.scratch with
      search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
      phases := st.scratch.phases }) :
    st =
      { core :=
          { s.core with
            vals := st.core.vals, flags := st.core.flags, lvl := st.core.lvl, rsns := st.core.rsns,
            trl := st.core.trl, trail_pos := st.core.trail_pos, trail_end := st.core.trail_end,
            unassigned := st.core.unassigned, unflushed := st.core.unflushed, wvec := st.core.wvec,
            arena := st.core.arena, wstk := st.core.wstk, wlen := st.core.wlen,
            wusable := st.core.wusable, confl_type := st.core.confl_type,
            confl_ref := st.core.confl_ref, confl_lit0 := st.core.confl_lit0,
            confl_lit1 := st.core.confl_lit1, oom := st.core.oom }
        scratch := { s.scratch with
          search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
          phases := st.scratch.phases } } := by
  have h1 := h.get FullCoreState.d_cur; have h2 := h.get FullCoreState.d_val
  have h3 := h.get FullCoreState.cur_vars; have h4 := h.get FullCoreState.arena_len
  have h5 := h.get FullCoreState.arena_garbage; have h6 := h.get FullCoreState.first_reducible
  have h7 := h.get FullCoreState.num_irred; have h8 := h.get FullCoreState.num_redundant
  have h9 := h.get FullCoreState.num_binary; have h10 := h.get FullCoreState.probing
  have h11 := h.get FullCoreState.propagated; have h12 := h.get FullCoreState.cur_level
  have h13 := h.get FullCoreState.fuel; have h14 := h.get FullCoreState.tmp_cnt
  have h15 := h.get FullCoreState.tmp_len; have h16 := h.get FullCoreState.min_clr_len
  have h17 := h.get FullCoreState.min_clr_full; have h18 := h.get FullCoreState.dense_mode
  have h19 := h.get FullCoreState.inconsistent; have h20 := h.get FullCoreState.lit_mark
  have h21 := h.get FullCoreState.mrk; have h22 := h.get FullCoreState.tmp
  have h23 := h.get FullCoreState.min_clr; have h24 := h.get FullCoreState.frame_trail
  have h25 := h.get FullCoreState.frame_dec; have h26 := h.get FullCoreState.repr
  have h27 := h.get FullCoreState.min_stk
  cases st with | mk stc stsc =>
  cases s with | mk sc ssc =>
  dsimp only at hsc; rw [hsc]
  cases stc; cases sc; simp only at *; subst_vars; rfl

theorem FullScratch.LengthsOk.with_ticks {c : FullCfg} {sc : FullScratch}
    (hok : sc.LengthsOk c) (t : BitVec 64) :
    ({ sc with search_ticks := t } : FullScratch).LengthsOk c :=
  { hok with walk_vals_len := hok.walk_vals_len }

/-- Loop-body invariant bundle for `full_prop_lit`. -/
structure PropLitInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s st : FullState)
    (not_lit off q p end_v : Nat) : Prop where
  len : st.LengthsOk c
  nw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st.core)
  sw : SplitWatchesInv F_cur st.core not_lit off q p end_v
  ag : AgreesExcept propLitCoreMask s.core st.core
  tr : FullTrailExt s.core st.core
  perm : FullArenaPermEq s.core st.core
  sc_eq : st.scratch = { s.scratch with
    search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
    phases := st.scratch.phases }
  not_f : st.core.vals[not_lit]?.getD 0#8 = 0xFF#8

theorem PropLitInv.cur_vars_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {not_lit off q p end_v : Nat}
    (h : PropLitInv c F0 F_cur s st not_lit off q p end_v) :
    st.core.cur_vars = s.core.cur_vars := h.ag.get FullCoreState.cur_vars

theorem PropLitInv.dense_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {not_lit off q p end_v : Nat}
    (h : PropLitInv c F0 F_cur s st not_lit off q p end_v) :
    st.core.dense_mode = s.core.dense_mode := h.ag.get FullCoreState.dense_mode

theorem PropLitInv.end_lt_wcap {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {not_lit off q p end_v : Nat}
    (h : PropLitInv c F0 F_cur s st not_lit off q p end_v)
    (hnot_lt : not_lit < 2 * st.core.cur_vars) :
    end_v ≤ st.core.wlen ∧ st.core.wlen ≤ c.wcap := by
  have hb := h.sw.layout.bounds not_lit hnot_lt
  rw [h.sw.off_eq, h.sw.sz_eq] at hb
  have hge := h.sw.q_ge; have hqp := h.sw.q_le_p; have hpe := h.sw.p_le_end
  exact ⟨by omega, h.len.core_ok.wlen_le⟩

theorem propLit_vals_neg {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {l : Nat}
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k)) (hl : l < 2 * k.cur_vars)
    (hlt : l < k.vals.length) (hslt : ((k.vals[l]'hlt).signExtend 32).slt 0#32 = true) :
    k.vals[l]?.getD 0#8 = 0xFF#8 := by
  have hget : k.vals[l]?.getD 0#8 = k.vals[l]'hlt := by simp [List.getElem?_eq_getElem hlt]
  rw [hget]; exact (full_i8_vals_slt0 (by rw [← hget]; exact hnw.vals_domain l hl)).mp hslt

theorem propLit_vals_un {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {l : Nat}
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k)) (hl : l < 2 * k.cur_vars)
    (hlt : l < k.vals.length)
    (hnp : (0#32).slt ((k.vals[l]'hlt).signExtend 32) = false)
    (hnn : ((k.vals[l]'hlt).signExtend 32).slt 0#32 = false) :
    k.vals[l]?.getD 0#8 = 0#8 := by
  have hget : k.vals[l]?.getD 0#8 = k.vals[l]'hlt := by simp [List.getElem?_eq_getElem hlt]
  rw [hget]
  exact i8_vals_eq0_of_not_pos_neg (by rw [← hget]; exact hnw.vals_domain l hl) hnp hnn

theorem propLit_hunit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {st : FullState} {cref other not_lit : BitVec 32}
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st.core))
    (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore st.core)
    (hng : fullArenaClauseGarbCore st.core cref.toNat = false)
    (hfit : cref.toNat + 3 + fullArenaClauseSizeCore st.core cref.toNat ≤ st.core.arena.length)
    (har3 : st.core.arena[cref.toNat + 3]? = some other)
    (har4 : st.core.arena[cref.toNat + 4]? = some not_lit)
    (hnot_f : st.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hbad : ∀ k, 2 ≤ k → k < fullArenaClauseSize st (cref.setWidth 64).toNat →
      fullFindReplBad st (cref.setWidth 64).toNat k) :
    ∀ l ∈ fullArenaClauseLitsCore st.core cref.toNat,
      l = other.toNat ∨ st.core.vals[l]?.getD 0#8 = 0xFF#8 := by
  have hcr64 : (cref.setWidth 64).toNat = cref.toNat := bv_c0_zext32_64 cref
  have hcsz3 : 3 ≤ fullArenaClauseSizeCore st.core cref.toNat :=
    (hnw.arena.refs_wf cref.toNat hcr_ref).2.1
  have h3 : (st.core.arena[cref.toNat + 3]'(by omega)).toNat = other.toNat :=
    congrArg BitVec.toNat (Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans har3))
  have h4 : (st.core.arena[cref.toNat + 4]'(by omega)).toNat = not_lit.toNat :=
    congrArg BitVec.toNat (Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans har4))
  exact full_clause_falsified_of_find_repl_none hnw hcr_ref hng (by omega) h3 h4 hnot_f
    (fun k hk1 hk2 => by have hb := hbad k hk1 (by rwa [hcr64]); rwa [hcr64] at hb)

theorem propLit_inv_drop {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {not_lit off q p p' end_v : Nat} {ticks' : BitVec 64}
    (hpi : PropLitInv c F0 F_cur s st not_lit off q p end_v)
    (hsw : SplitWatchesInv F_cur st.core not_lit off q (p + 2) end_v) (hp' : p' = p + 2) :
    PropLitInv c F0 F_cur s
      { st with scratch := { st.scratch with search_ticks := ticks' } }
      not_lit off q p' end_v :=
  { len := ⟨hpi.len.core_ok, hpi.len.scratch_ok.with_ticks ticks'⟩
    nw := hpi.nw
    sw := hp'.symm ▸ hsw
    ag := hpi.ag, tr := hpi.tr, perm := hpi.perm
    sc_eq := by dsimp only; rw [hpi.sc_eq]
    not_f := hpi.not_f }

theorem propLit_inv_keep_large {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {not_lit off p0 : Nat} {q_v p_v end_v : BitVec 64} {w0 cref : BitVec 32}
    (hpi : PropLitInv c F0 F_cur s st not_lit off q_v.toNat p0 end_v.toNat)
    (hsw : SplitWatchesInv F_cur st.core not_lit off q_v.toNat (p_v.toNat + 2) end_v.toNat)
    (hnot_lt : not_lit < 2 * st.core.cur_vars)
    (hq1 : (q_v + (1 : BitVec 64)).toNat = q_v.toNat + 1)
    (hq2 : (q_v + (2 : BitVec 64)).toNat = q_v.toNat + 2)
    (hp2 : (p_v + (1 : BitVec 64) + (1 : BitVec 64)).toNat = p_v.toNat + 2)
    (hq_le : q_v.toNat + 2 ≤ p_v.toNat + 2) (hp_le : p_v.toNat + 2 ≤ end_v.toNat)
    (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore st.core) :
    PropLitInv c F0 F_cur s
      { st with core := { st.core with
          wstk := (st.core.wstk.set q_v.toNat w0).set (q_v + (1 : BitVec 64)).toNat cref } }
      not_lit off (q_v + (2 : BitVec 64)).toNat
      (p_v + (1 : BitVec 64) + (1 : BitVec 64)).toNat end_v.toNat := by
  have hlen_w := hpi.len.core_ok.wstk_len_arr
  have ⟨hend_le, hwlen_le⟩ := hpi.end_lt_wcap hnot_lt
  have hlen1 : ({ st with core := { st.core with
      wstk := (st.core.wstk.set q_v.toNat w0).set (q_v + (1 : BitVec 64)).toNat cref } } :
      FullState).LengthsOk c :=
    ⟨{ hpi.len.core_ok with wstk_len_arr := by simp [hlen_w] }, hpi.len.scratch_ok⟩
  have hsw1 := hsw.write_large hnot_lt (by omega) (by omega) (by omega) hflag hcr_lt hcr_ref
  exact
    { len := hlen1
      nw := fullWitnessInv_nw_congr hlen1.core_ok.cur_vars_le hpi.nw
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      sw := by rw [hp2, hq2]; exact hsw1.with_nonwatch rfl rfl (by simp only [hq1]) rfl rfl
      ag := hpi.ag.update (fun k => { k with wstk := _ })
      tr := hpi.tr.congr rfl rfl rfl, perm := hpi.perm
      sc_eq := hpi.sc_eq, not_f := hpi.not_f }

theorem propLit_bin_confl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {ignore_ref : BitVec 64} {not_lit w0 : BitVec 32}
    {off_v p_v q_v end_v : BitVec 64}
    (hpi : PropLitInv c F0 F_cur s st not_lit.toNat off_v.toNat q_v.toNat p_v.toNat end_v.toNat)
    (hsw1 : SplitWatchesInv F_cur { st.core with wstk := st.core.wstk.set q_v.toNat w0 }
      not_lit.toNat off_v.toNat (q_v.toNat + 1) (p_v.toNat + 1) end_v.toNat)
    (hnot_lt : not_lit.toNat < 2 * st.core.cur_vars)
    (hother_lt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * st.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [not_lit.toNat, (w0 &&& 0x7FFFFFFF#32).toNat]))
    (hov_f : st.core.vals[(w0 &&& 0x7FFFFFFF#32).toNat]?.getD 0#8 = 0xFF#8)
    (hp1 : (p_v + 1#64).toNat = p_v.toNat + 1) (hq1 : (q_v + 1#64).toNat = q_v.toNat + 1) :
    let other := w0 &&& 0x7FFFFFFF#32
    let st1 : FullState :=
      { st with core :=
        { st.core with
          wstk := st.core.wstk.set q_v.toNat w0, confl_type := 1#64,
          confl_lit0 := not_lit.setWidth 64, confl_lit1 := other.setWidth 64,
          confl_ref := 0xFFFFFFFF#64 } }
    PropLitInv c F0 F_cur s st1 not_lit.toNat off_v.toNat (q_v + 1#64).toNat (p_v + 1#64).toNat
      end_v.toNat ∧ PropLitConfl F_cur ignore_ref st1.core := by
  intro other st1
  have hlen1 : st1.LengthsOk c :=
    ⟨{ hpi.len.core_ok with wstk_len_arr := by simp [st1, hpi.len.core_ok.wstk_len_arr] },
     hpi.len.scratch_ok⟩
  refine ⟨{ len := hlen1
            nw := fullWitnessInv_nw_congr hlen1.core_ok.cur_vars_le hpi.nw
              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            sw := by rw [hp1, hq1]; exact hsw1.with_nonwatch rfl rfl rfl rfl rfl
            ag := hpi.ag.update (fun k => { k with
              wstk := st1.core.wstk, confl_type := 1#64, confl_lit0 := not_lit.setWidth 64,
              confl_lit1 := other.setWidth 64, confl_ref := 0xFFFFFFFF#64 })
            tr := hpi.tr.congr rfl rfl rfl, perm := hpi.perm
            sc_eq := hpi.sc_eq, not_f := hpi.not_f },
    Or.inr ⟨Or.inl ⟨rfl,
      by change (not_lit.setWidth 64).toNat < _; rw [bv_c0_zext32_64]; exact hnot_lt,
      by change (other.setWidth 64).toNat < _; rw [bv_c0_zext32_64]; exact hother_lt,
      by change (cnfOfClauses F_cur).EntailsClause
           (cnfClause [(not_lit.setWidth 64).toNat, (other.setWidth 64).toNat])
         rw [bv_c0_zext32_64, bv_c0_zext32_64]; exact hent,
      by change st.core.vals[(not_lit.setWidth 64).toNat]?.getD 0#8 = 0xFF#8
         rw [bv_c0_zext32_64]; exact hpi.not_f,
      by change st.core.vals[(other.setWidth 64).toNat]?.getD 0#8 = 0xFF#8
         rw [bv_c0_zext32_64]; exact hov_f⟩,
      fun h2 => by change (1#64) = 2#64 at h2; cases h2⟩⟩

theorem propLit_large_confl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st1 : FullState} {ignore_ref : BitVec 64} {not_lit other cref : BitVec 32}
    {off_v p_v q_v end_v : BitVec 64}
    (hpi1 : PropLitInv c F0 F_cur s st1 not_lit.toNat off_v.toNat q_v.toNat (p_v.toNat + 2)
      end_v.toNat)
    (hnot_lt : not_lit.toNat < 2 * st1.core.cur_vars) (hq_le : q_v.toNat ≤ p_v.toNat)
    (hq1 : (q_v + (1 : BitVec 64)).toNat = q_v.toNat + 1)
    (hq2 : (q_v + (2 : BitVec 64)).toNat = q_v.toNat + 2)
    (hp2 : (p_v + (1 : BitVec 64) + (1 : BitVec 64)).toNat = p_v.toNat + 2)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore st1.core)
    (hng : fullArenaClauseGarbCore st1.core cref.toNat = false)
    (hne_ign : cref.setWidth 64 ≠ ignore_ref)
    (hov_f : st1.core.vals[other.toNat]?.getD 0#8 = 0xFF#8)
    (hunit : ∀ l ∈ fullArenaClauseLitsCore st1.core cref.toNat,
      l = other.toNat ∨ st1.core.vals[l]?.getD 0#8 = 0xFF#8) :
    let st2 : FullState :=
      { st1 with core :=
        { st1.core with
          wstk := (st1.core.wstk.set q_v.toNat (other &&& 0x7FFFFFFF#32)).set
            (q_v + (1 : BitVec 64)).toNat cref
          confl_type := 2#64, confl_ref := cref.setWidth 64 } }
    PropLitInv c F0 F_cur s st2 not_lit.toNat off_v.toNat (q_v + (2 : BitVec 64)).toNat
      (p_v + (1 : BitVec 64) + (1 : BitVec 64)).toNat end_v.toNat ∧
    PropLitConfl F_cur ignore_ref st2.core := by
  intro st2
  have hcr64 : (cref.setWidth 64).toNat = cref.toNat := bv_c0_zext32_64 cref
  have hlen_w := hpi1.len.core_ok.wstk_len_arr
  have ⟨hend_le, hwlen_le⟩ := hpi1.end_lt_wcap hnot_lt
  have hlen2 : st2.LengthsOk c :=
    ⟨{ hpi1.len.core_ok with wstk_len_arr := by simp [st2, hlen_w] }, hpi1.len.scratch_ok⟩
  have hp_le := hpi1.sw.p_le_end
  have hsw2 := hpi1.sw.write_large hnot_lt hq_le (by omega) (by omega)
    (bv32_mask7f_flag0 other) hcr_lt hcr_ref
  refine ⟨{ len := hlen2
            nw := fullWitnessInv_nw_congr hlen2.core_ok.cur_vars_le hpi1.nw
              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            sw := by
              rw [hp2, hq2]
              exact hsw2.with_nonwatch rfl rfl (by simp only [st2, hq1]) rfl rfl
            ag := hpi1.ag.update (fun k => { k with
              wstk := st2.core.wstk, confl_type := 2#64, confl_ref := cref.setWidth 64 })
            tr := hpi1.tr.congr rfl rfl rfl, perm := hpi1.perm
            sc_eq := hpi1.sc_eq, not_f := hpi1.not_f },
    Or.inr ⟨Or.inr ⟨rfl,
      by change (cref.setWidth 64).toNat ∈ _; rwa [hcr64],
      by change fullArenaClauseGarbCore st1.core (cref.setWidth 64).toNat = false; rwa [hcr64],
      fun l hl => by
        change st1.core.vals[l]?.getD 0#8 = 0xFF#8
        have hl' : l ∈ fullArenaClauseLitsCore st1.core cref.toNat := by
          change l ∈ fullArenaClauseLitsCore st1.core (cref.setWidth 64).toNat at hl
          rwa [hcr64] at hl
        rcases hunit l hl' with rfl | hfl; exact hov_f; exact hfl⟩,
      fun _ => hne_ign⟩⟩

theorem propLit_measure_lt {a b c d : Nat} (h1 : a ≤ b) (h2 : b + 2 ≤ c) :
    (d + (c - a)) - (d + (b + 2 - a)) < c - b := by omega

end LeanQbe.T.Examples.Kissat.Full
