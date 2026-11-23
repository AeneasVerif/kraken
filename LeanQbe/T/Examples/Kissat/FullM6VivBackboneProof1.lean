module

public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof0
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat M6 Vivification — Core Vivification Helpers (`9` Functions)

Defines specs and proves UNSAT-sound `Func.wp` (`XPost := False`, `0` SAT model proofs) for the
`9` lightweight vivification core functions in `FullM6VivBackbone.lean`:
1. `full_viv_unreason_m6_wp` (`NonActiveReason` enforcement via `full_backtrack`)
2. `full_viv_watch_rank_m6_wp` (read-only 2WL rank)
3. `full_viv_best_watch_m6_wp` (in-place 2-watch selection sort on `work_stk2`)
4. `full_viv_mark_garb_m6_wp` (unreason + unwatch + `PH_GARB` marking)
5. `full_viv_subsumes_bin_m6_wp` (read-only binary subsumption check)
6. `full_viv_subsumes_cl_m6_wp` (read-only arena-clause subsumption check)
7. `full_viv_best_implied_m6_wp` (read-only min-`tpos` implied literal selection)
8. `full_viv_reestablish_m6_wp` (2WL watch-invariant backtrack repair)
9. `full_viv_inst_check_m6_wp` (instantiation resolvent subset certificate + `lit_mark` cleanup)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6VivBackbone

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open FullVivTopTactics
open scoped FullArenaTactics FullVivTopTactics

/-! ## 1. Per-Function Specifications (`9` Core Vivification Helpers) -/

section Specs

/-- `full_viv_unreason_m6(h, cref)`: guarantees `NonActiveReason s'.core cref.toNat` while
preserving `FullSparseInvW`, arena, `tmp`, `work_stk2`, `red_refs`, and `tarjan_reach`. -/
@[expose] def fullVivUnreasonM6Spec : Spec [i64, i32] [] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullSparseInvW c F0 F_cur s' → NonActiveReason s'.core cref.toNat →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
      s'.core.arena_len = s.core.arena_len → s'.core.probing = s.core.probing →
      s'.core.fuel = s.core.fuel → s'.core.tmp = s.core.tmp →
      s'.scratch.work_stk2 = s.scratch.work_stk2 → s'.scratch.red_refs = s.scratch.red_refs →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- `full_viv_watch_rank_m6(h, lit)`: read-only 2WL watch-selection priority key. -/
@[expose] def fullVivWatchRankM6Spec : Spec [i64, i32] [i64] := fun (h, lit, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ lit.toNat < 2 * s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ r : BitVec 64, Q (r, ()) m

/-- `full_viv_best_watch_m6(h, olen)`: permutes `work_stk2[0 ..< olen)` to place the 2 highest-rank
watch literals at slots `0, 1`. -/
@[expose] def fullVivBestWatchM6Spec : Spec [i64, i32] [] := fun (h, olen, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ olen.toNat ≤ c.max_vars ∧
    (∀ i < olen.toNat, (s.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ ws2' m',
      ws2'.length = 2 * c.max_vars →
      (ws2'.take olen.toNat).Perm (s.scratch.work_stk2.take olen.toNat) →
      (FullMem c { s with scratch := { s.scratch with work_stk2 := ws2' } } ⋆ R) m' → Q () m'

/-- `full_viv_mark_garb_m6(h, cref)`: unreasons, unwatches, and marks `cref` with `PH_GARB`
preserving `FullSparseInvW`, `fullArenaClauseRefs`, `red_refs`, and `tarjan_reach`. -/
@[expose] def fullVivMarkGarbM6Spec : Spec [i64, i32] [] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena_len = s.core.arena_len → s'.core.probing = s.core.probing →
      s'.core.fuel = s.core.fuel → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- `full_viv_subsumes_bin_m6(h, a, b)`: read-only binary subsumption test against `lit_mark` and
level-0 falsified literals. -/
@[expose] def fullVivSubsumesBinM6Spec : Spec [i64, i32, i32] [.bool] :=
  fun (h, a, b, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ a.toNat < 2 * s.core.cur_vars ∧ b.toNat < 2 * s.core.cur_vars ∧
      (FullMem c s ⋆ R) m ∧ ∀ ok : Bool, Q (ok, ()) m

/-- `full_viv_subsumes_cl_m6(h, rcr, sz)`: read-only arena clause subsumption test against
`lit_mark` and level-0 falsified literals. -/
@[expose] def fullVivSubsumesClM6Spec : Spec [i64, i32, i32] [.bool] :=
  fun (h, rcr, _sz, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      rcr.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s rcr.toNat = false ∧
      (FullMem c s ⋆ R) m ∧ ∀ ok : Bool, Q (ok, ()) m

/-- `full_viv_best_implied_m6(h, sz)`: read-only scan selecting the earliest-assigned (`min tpos`)
satisfied literal in `tmp[0 ..< sz)`, or `0xFFFFFFFF#32` if none. -/
@[expose] def fullVivBestImpliedM6Spec : Spec [i64, i32] [i32] := fun (h, sz, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ sz.toNat ≤ c.max_vars ∧
    (∀ k < sz.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r : BitVec 32,
      (r ≠ 0xFFFFFFFF#32 → r.toNat < 2 * s.core.cur_vars ∧ s.core.vals[r.toNat]?.getD 0#8 = 1#8) →
      Q (r, ()) m

/-- `full_viv_reestablish_m6(h, cref)`: 2WL watch-invariant backtrack repair preserving
`FullSparseInvW`, arena, `red_refs`, and `tarjan_reach`. -/
@[expose] def fullVivReestablishM6Spec : Spec [i64, i32] [] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.probing = s.core.probing → s'.core.fuel = s.core.fuel →
      s'.scratch.red_refs = s.scratch.red_refs →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- `full_viv_inst_check_m6(h, sz, iolen, not_lit)`: verifies every literal in
`work_stk2[0 ..< iolen)` is either `not_lit` or present in `tmp[0 ..< sz - 1)` while leaving
`lit_mark` completely cleared (`FullLitMarksClear`). -/
@[expose] def fullVivInstCheckM6Spec : Spec [i64, i32, i32, i32] [.bool] :=
  fun (h, sz, iolen, not_lit, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ 1 ≤ sz.toNat ∧ sz.toNat ≤ c.max_vars ∧
      iolen.toNat ≤ c.max_vars ∧
      (∀ k < sz.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (∀ i < iolen.toNat, (s.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) lm' m',
        let s' : FullState := { s with core := { s.core with lit_mark := lm' } }
        FullSparseInvW c F0 F_cur s' →
        (ok = true → ∀ i < iolen.toNat,
          s.scratch.work_stk2[i]?.getD 0#32 = not_lit ∨
          ∃ k, k + 1 < sz.toNat ∧
            s.scratch.work_stk2[i]?.getD 0#32 = s.core.tmp[k]?.getD 0#32) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

end Specs

/-! ## 2. Pure Permutation & `NonActiveReason` Helpers -/

section Helpers

private theorem bv32_lshr1_toNat (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 := by
  change (x >>> (1 : Nat)).toNat = x.toNat / 2
  rw [BitVec.toNat_ushiftRight]; simp [Nat.shiftRight_eq_div_pow]

private theorem bv8_zext32_eq0_iff (x : BitVec 8) : x.setWidth 32 = 0#32 ↔ x = 0#8 := by
  revert x; decide

private theorem nonActiveReason_of_level0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0) (cref : Nat) :
    NonActiveReason k cref := fun idx hidx hne _ => by
  have hlv : (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le idx hidx; omega
  exact absurd (hw.level0_rsn_none idx hidx hlv) hne

private theorem list_swap_perm {α : Type} (xs : List α) {i j : Nat} (hi : i < xs.length)
    (hj : j < xs.length) (hij : i < j) :
    ((xs.set i (xs[j]'hj)).set j (xs[i]'hi)).Perm xs := by
  let a := xs[i]'hi; let b := xs[j]'hj
  let p1 := xs.take i
  let p2 := (xs.drop (i + 1)).take (j - i - 1)
  let p3 := xs.drop (j + 1)
  have hlen1 : p1.length = i := by simp [p1, List.length_take]; omega
  have hlen2 : p2.length = j - i - 1 := by
    simp [p2, List.length_take, List.length_drop]; omega
  have hxs : xs = p1 ++ (a :: (p2 ++ b :: p3)) := by
    refine List.ext_getElem? fun k => ?_
    by_cases h1 : k < i
    · rw [List.getElem?_append_left (by omega), List.getElem?_take]; simp [h1]
    · rw [List.getElem?_append_right (by omega), hlen1]
      by_cases h2 : k = i
      · subst h2; simp [a, List.getElem?_eq_getElem hi]
      · rw [show k - i = (k - (i + 1)) + 1 by omega, List.getElem?_cons_succ]
        by_cases h3 : k < j
        · rw [List.getElem?_append_left (by omega), List.getElem?_take,
            ite_eq_left (by omega : k - (i + 1) < j - i - 1), List.getElem?_drop,
            show i + 1 + (k - (i + 1)) = k by omega]
        · rw [List.getElem?_append_right (by omega), hlen2]
          by_cases h4 : k = j
          · subst k; rw [show j - (i + 1) - (j - i - 1) = 0 by omega]
            simp [b, List.getElem?_eq_getElem hj]
          · rw [show k - (i + 1) - (j - i - 1) = (k - (j + 1)) + 1 by omega,
              List.getElem?_cons_succ, List.getElem?_drop, show j + 1 + (k - (j + 1)) = k by omega]
  have hsw : (xs.set i b).set j a = p1 ++ (b :: (p2 ++ a :: p3)) := by
    refine List.ext_getElem? fun k => ?_
    by_cases h4 : k = j
    · subst k
      rw [List.getElem?_set_self (by simp; omega), List.getElem?_append_right (by omega), hlen1,
        show j - i = (j - (i + 1)) + 1 by omega, List.getElem?_cons_succ,
        List.getElem?_append_right (by omega), hlen2,
        show j - (i + 1) - (j - i - 1) = 0 by omega]
      rfl
    · rw [List.getElem?_set_ne (Ne.symm h4)]
      by_cases h2 : k = i
      · subst k
        rw [List.getElem?_set_self hi, List.getElem?_append_right (by omega), hlen1, Nat.sub_self]
        rfl
      · rw [List.getElem?_set_ne (Ne.symm h2)]
        by_cases h1 : k < i
        · rw [List.getElem?_append_left (by omega), List.getElem?_take]; simp [h1]
        · rw [List.getElem?_append_right (by omega), hlen1,
            show k - i = (k - (i + 1)) + 1 by omega, List.getElem?_cons_succ]
          by_cases h3 : k < j
          · rw [List.getElem?_append_left (by omega), List.getElem?_take,
              ite_eq_left (by omega : k - (i + 1) < j - i - 1), List.getElem?_drop,
              show i + 1 + (k - (i + 1)) = k by omega]
          · rw [List.getElem?_append_right (by omega), hlen2,
              show k - (i + 1) - (j - i - 1) = (k - (j + 1)) + 1 by omega,
              List.getElem?_cons_succ, List.getElem?_drop, show j + 1 + (k - (j + 1)) = k by omega]
  rw [hsw, hxs]
  have hmid : (b :: (p2 ++ a :: p3)).Perm (a :: (p2 ++ b :: p3)) := by
    have h1 : (b :: (p2 ++ a :: p3)).Perm (p2 ++ b :: a :: p3) := List.perm_middle.symm
    have h2 : (p2 ++ b :: a :: p3).Perm (p2 ++ a :: b :: p3) :=
      List.Perm.append_left p2 (List.Perm.swap a b p3)
    have h3 : (p2 ++ a :: b :: p3).Perm (a :: (p2 ++ b :: p3)) := List.perm_middle
    exact h1.trans (h2.trans h3)
  exact List.Perm.append_left p1 hmid

private theorem list_take_swap_perm {α : Type} (xs : List α) {n i j : Nat}
    (hn : n ≤ xs.length) (hi : i < n) (hj : j < n) (hij : i < j) :
    (((xs.set i (xs[j]'(by omega))).set j (xs[i]'(by omega))).take n).Perm (xs.take n) := by
  have heq : ((xs.set i (xs[j]'(by omega))).set j (xs[i]'(by omega))).take n =
      (((xs.take n).set i ((xs.take n)[j]'(by simp [List.length_take]; omega))).set j
        ((xs.take n)[i]'(by simp [List.length_take]; omega))) := by
    refine List.ext_getElem? fun k => ?_
    by_cases hkn : k < n
    · rw [List.getElem?_take, ite_eq_left hkn]
      by_cases hkj : k = j
      · subst k
        rw [List.getElem?_set_self (by simp; omega),
          List.getElem?_set_self (by simp [List.length_take]; omega), List.getElem_take]
      · rw [List.getElem?_set_ne (Ne.symm hkj), List.getElem?_set_ne (Ne.symm hkj)]
        by_cases hki : k = i
        · subst k
          rw [List.getElem?_set_self (by omega),
            List.getElem?_set_self (by simp [List.length_take]; omega), List.getElem_take]
        · rw [List.getElem?_set_ne (Ne.symm hki), List.getElem?_set_ne (Ne.symm hki),
            List.getElem?_take, ite_eq_left hkn]
    · rw [List.getElem?_eq_none (by simp [List.length_take]; omega),
        List.getElem?_eq_none (by simp [List.length_take]; omega)]
  rw [heq]
  exact list_swap_perm (xs.take n) (by simp [List.length_take]; omega)
    (by simp [List.length_take]; omega) hij

private theorem ws2_lt_of_perm {ws2 orig : List (BitVec 32)} {n B : Nat}
    (hln : n ≤ ws2.length) (hperm : (ws2.take n).Perm (orig.take n))
    (hlt : ∀ k < n, (orig[k]?.getD 0#32).toNat < B) :
    ∀ i < n, (ws2[i]?.getD 0#32).toNat < B := fun i hi => by
  have hm : ws2[i]'(by omega) ∈ orig.take n := hperm.mem_iff.mp (by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp [List.length_take]; omega, by simp [List.getElem_take]⟩)
  obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.mp hm
  have hkn : k < n := by rw [List.length_take] at hk; omega
  have hko : k < orig.length := by rw [List.length_take] at hk; omega
  have hget := hlt k hkn
  rw [List.getElem_take] at hkeq
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← hkeq]
  rwa [List.getElem?_eq_getElem hko, Option.getD_some] at hget

end Helpers

/-! ## 3. `full_viv_unreason_m6_wp`, `full_viv_watch_rank_m6_wp`, `full_viv_best_watch_m6_wp` -/

section UnreasonAndWatch

/-- `full_viv_unreason_m6` satisfies `fullVivUnreasonM6Spec` parametrically in `Γ`. -/
theorem full_viv_unreason_m6_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X) :
    ∀ args m Q X, fullVivUnreasonM6Spec args m Q X →
      Func.wp Γ full_viv_unreason_m6_body args m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hsp0, hm0, hQ⟩
  have hcl0 := hsp0.1.core_ok; have hw0 := hsp0.2.1
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl_lt : s.core.cur_level < 2 ^ 64 := by
    have := hw0.cur_level_le; have := hcl0.trail_end_le; have := hcl0.cur_vars_le; omega
  have hte_lt : s.core.trail_end < 2 ^ 64 := by
    have := hcl0.trail_end_le; have := hcl0.cur_vars_le; omega
  unfold Func.wp full_viv_unreason_m6_body
  fvt_to_group
  · have hcl_eq0 : s.core.cur_level = 0 := by
      have h0 : (BitVec.ofNat 64 s.core.cur_level).toNat = 0 := by rw [hc]; rfl
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_lt] at h0
    fvt_steps
    exact hQ s m0 hsp0 (nonActiveReason_of_level0 hw0 hcl_eq0 cref.toNat)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl hm0
  · fvt_to_group
    refine wp_loop_inv (ts := [i64])
      (fun (i_v, ()) mi =>
        m0 = mi ∧ i_v.toNat ≤ s.core.trail_end ∧
        ∀ idx < i_v.toNat,
          let rsn := s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
          rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ cref.toNat)
      (fun (i_v, _) _ => s.core.trail_end - i_v.toNat) ?_ ?_
    · intro J hJ; fvt_steps; exact hJ (0#64, ()) m0 ⟨rfl, Nat.zero_le _, fun _ h => by simp at h⟩
    · rintro J ⟨i_v, ⟨⟩⟩ mi ⟨rfl, hi_le, hpre⟩ ih
      fvt_step; fvt_step
      · have hi_lt : i_v.toNat < s.core.trail_end := by
          have : i_v.toNat < (BitVec.ofNat 64 s.core.trail_end).toNat := by c0_bound
          rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hte_lt] at this
        have hi_trl : i_v.toNat < s.core.trl.length := by
          have := hcl0.trl_len; have := hcl0.trail_end_le; have := hcl0.cur_vars_le; omega
        have hlit_lt := hw0.trail_lits_lt i_v.toNat hi_lt
        rw [List.getElem?_eq_getElem hi_trl, Option.getD_some] at hlit_lt
        have hv_lt : (s.core.trl[i_v.toNat]'hi_trl >>> 1#32).toNat < s.core.rsns.length := by
          rw [bv32_lshr1_toNat, hcl0.rsns_len]; have := hcl0.cur_vars_le; omega
        have hi1 : (i_v + 1#64).toNat = i_v.toNat + 1 := by bv_omega
        have hrsn_eq : s.core.rsns[(s.core.trl[i_v.toNat]'hi_trl >>> 1#32).toNat]'hv_lt =
            s.core.rsns[(s.core.trl[i_v.toNat]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 := by
          rw [List.getElem?_eq_getElem hi_trl, Option.getD_some,
            ← bv32_lshr1_toNat (s.core.trl[i_v.toNat]'hi_trl),
            List.getElem?_eq_getElem hv_lt, Option.getD_some]
        fvt_steps
        · -- Found `cref` as active reason -> `full_backtrack(h, 0ULL); return;`
          c0_call hBacktrack
          refine ⟨c, s, R, rfl, hsp0.1, hcl_lt,
            (fun _ => by
              have : s.core.cur_level ≤ c.max_vars := by
                have := hw0.cur_level_le; have := hcl0.trail_end_le; have := hcl0.cur_vars_le
                omega
              change 0 < c.max_vars; omega),
            hw0.trail_lits_lt, hm0,
            fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
              hlen_bt _ _ hcl_bt hpres_bt hsc_bt _ _ hw_bt _ hm_bt => ?_⟩
          have hsp_bt : FullSparseInvW c F0 F_cur _ :=
            FullVivTop.FullSparseInvW.of_backtrack hsp0 (Nat.zero_le _) hlen_bt hpres_bt
              (hw_bt F0 F_cur hw0 (Nat.zero_le _))
          rcases hsc_bt with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
          have hcl_bt0 : cl' = 0 := by rw [hcl_bt]; simp
          fvt_steps
          exact hQ _ m_bt hsp_bt (nonActiveReason_of_level0 hsp_bt.2.1 hcl_bt0 cref.toNat)
            rfl rfl rfl rfl rfl rfl rfl rfl rfl hm_bt
        · -- `rsn ≠ cref`
          refine ih (i_v + 1#64, ()) m0 (by dsimp only; omega) ⟨rfl, by omega, fun idx hidx => ?_⟩
          rw [hi1] at hidx
          rcases (by omega : idx < i_v.toNat ∨ idx = i_v.toNat) with h1 | rfl
          · exact hpre idx h1
          · dsimp only; intro _ _ heq
            have hne : s.core.rsns[(s.core.trl[i_v.toNat]'hi_trl >>> 1#32).toNat]'hv_lt ≠
                cref := by c0_bound
            rw [hrsn_eq] at hne; exact hne (BitVec.eq_of_toNat_eq heq)
        · -- `(rsn &&& 0x80000000#32) ≠ 0#32`
          refine ih (i_v + 1#64, ()) m0 (by dsimp only; omega) ⟨rfl, by omega, fun idx hidx => ?_⟩
          rw [hi1] at hidx
          rcases (by omega : idx < i_v.toNat ∨ idx = i_v.toNat) with h1 | rfl
          · exact hpre idx h1
          · dsimp only; intro _ h0
            have hne : (s.core.rsns[(s.core.trl[i_v.toNat]'hi_trl >>> 1#32).toNat]'hv_lt &&&
                0x80000000#32) ≠ 0#32 := by c0_bound
            rw [hrsn_eq] at hne; exact absurd h0 hne
        · -- `rsn = 0xFFFFFFFF#32`
          refine ih (i_v + 1#64, ()) m0 (by dsimp only; omega) ⟨rfl, by omega, fun idx hidx => ?_⟩
          rw [hi1] at hidx
          rcases (by omega : idx < i_v.toNat ∨ idx = i_v.toNat) with h1 | rfl
          · exact hpre idx h1
          · dsimp only; intro hne
            have heq : s.core.rsns[(s.core.trl[i_v.toNat]'hi_trl >>> 1#32).toNat]'hv_lt =
                0xFFFFFFFF#32 := by c0_bound
            rw [hrsn_eq] at heq; exact absurd heq hne
      · have hi_eq : i_v.toNat = s.core.trail_end := by
          have : (BitVec.ofNat 64 s.core.trail_end).toNat ≤ i_v.toNat := by c0_bound
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hte_lt] at this; omega
        fvt_steps
        exact hQ s m0 hsp0 (fun idx hidx => hpre idx (hi_eq ▸ hidx))
          rfl rfl rfl rfl rfl rfl rfl rfl rfl hm0

/-- `full_viv_watch_rank_m6` satisfies `fullVivWatchRankM6Spec` parametrically in `Γ`. -/
theorem full_viv_watch_rank_m6_wp (Γ : Env) :
    ∀ args m Q X, fullVivWatchRankM6Spec args m Q X →
      Func.wp Γ full_viv_watch_rank_m6_body args m Q X := by
  rintro ⟨h, lit, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlit, hm, hQ⟩
  have hcl := hlen.core_ok; have hcv := hcl.cur_vars_le
  have hvl : lit.toNat < s.core.vals.length := by rw [hcl.vals_len]; omega
  have hll : (lit >>> 1#32).toNat < s.core.lvl.length := by
    rw [bv32_lshr1_toNat, hcl.lvl_len]; omega
  unfold Func.wp full_viv_watch_rank_m6_body
  fvt_steps <;> exact hQ _

/-- `full_viv_best_watch_m6` satisfies `fullVivBestWatchM6Spec` parametrically in `Γ`. -/
theorem full_viv_best_watch_m6_wp (Γ : Env)
    (hRank : ∀ a m Q X, fullVivWatchRankM6Spec a m Q X →
      Γ "full_viv_watch_rank_m6" [i64, i32] [i64] a m Q X) :
    ∀ args m Q X, fullVivBestWatchM6Spec args m Q X →
      Func.wp Γ full_viv_best_watch_m6_body args m Q X := by
  rintro ⟨h, olen, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hlen0, hol_le, hlt0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hws2_0 := hlen0.scratch_ok.work_stk2_len
  unfold Func.wp full_viv_best_watch_m6_body
  fvt_to_group
  refine wp_loop_inv (ts := [i32])
    (fun (pos, ()) mp =>
      pos.toNat ≤ 2 ∧ pos.toNat ≤ olen.toNat ∧
      ∃ ws2, ws2.length = 2 * c.max_vars ∧
        (ws2.take olen.toNat).Perm (s.scratch.work_stk2.take olen.toNat) ∧
        (FullMem c { s with scratch := { s.scratch with work_stk2 := ws2 } } ⋆ R) mp)
    (fun (pos, _) _ => 2 - pos.toNat) ?_ ?_
  · intro J hJ; fvt_steps
    exact hJ (0#32, ()) m0 ⟨by decide, Nat.zero_le _, s.scratch.work_stk2, hws2_0, .refl _, hm0⟩
  · rintro J ⟨pos, ⟨⟩⟩ mp ⟨hpos_le2, hpos_le, ws2, hws2_len, hperm, hm_p⟩ ih
    let sp : FullState := { s with scratch := { s.scratch with work_stk2 := ws2 } }
    have hlen_p : sp.LengthsOk c :=
      ⟨hlen0.core_ok, { hlen0.scratch_ok with work_stk2_len := hws2_len }⟩
    have hlt_p : ∀ i < olen.toNat, (ws2[i]?.getD 0#32).toNat < 2 * s.core.cur_vars :=
      ws2_lt_of_perm (by omega) hperm hlt0
    fvt_steps
    · have hpos_lt2 : pos.toNat < 2 := by c0_bound
      have hpos_lt : pos.toNat < olen.toNat := by c0_bound
      have hpos_ws : pos.toNat < ws2.length := by omega
      have hpos1_eq : (pos + 1#32).toNat = pos.toNat + 1 := by bv_omega
      have hlit_pos : (ws2[pos.toNat]'hpos_ws).toNat < 2 * s.core.cur_vars := by
        have := hlt_p pos.toNat hpos_lt
        rwa [List.getElem?_eq_getElem hpos_ws, Option.getD_some] at this
      c0_call hRank
      refine ⟨c, sp, R, rfl, hlen_p, hlit_pos, hm_p, fun brank0 => ?_⟩
      fvt_to_group
      -- Inner scan `k = pos + 1 ..< olen`
      refine wp_loop_inv (ts := [i32, i64, i32])
        (fun (best, brank, k, ()) mk =>
          mp = mk ∧ pos.toNat ≤ best.toNat ∧ best.toNat < olen.toNat ∧
          pos.toNat < k.toNat ∧ k.toNat ≤ olen.toNat)
        (fun (_, _, k, _) _ => olen.toNat - k.toNat) ?_ ?_
      · intro Jk hJk; fvt_steps
        exact hJk (pos, brank0, pos + 1#32, ()) mp
          ⟨rfl, Nat.le_refl _, hpos_lt, by omega, by omega⟩
      · rintro Jk ⟨best, brank, k, ⟨⟩⟩ mk ⟨rfl, hbp, hbo, hpk, hk_le⟩ ihk
        fvt_step; fvt_step
        · have hk_lt : k.toNat < olen.toNat := by c0_bound
          have hk_ws : k.toNat < ws2.length := by omega
          have hk1_eq : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
          have hlit_k : (ws2[k.toNat]'hk_ws).toNat < 2 * s.core.cur_vars := by
            have := hlt_p k.toNat hk_lt
            rwa [List.getElem?_eq_getElem hk_ws, Option.getD_some] at this
          fvt_steps
          c0_call hRank
          refine ⟨c, sp, R, rfl, hlen_p, hlit_k, hm_p, fun rk => ?_⟩
          fvt_steps
          · exact ihk (k, rk, k + 1#32, ()) mp (by dsimp only; omega)
              ⟨rfl, by omega, hk_lt, by omega, by omega⟩
          · exact ihk (best, brank, k + 1#32, ()) mp (by dsimp only; omega)
              ⟨rfl, hbp, hbo, by omega, by omega⟩
        · -- After inner scan: `if (best != pos)` swap `out[pos]` and `out[best]`
          fvt_steps
          · have hne : best.toNat ≠ pos.toNat := fun h => by
              have : best ≠ pos := by c0_bound
              exact this (BitVec.eq_of_toNat_eq h)
            have hbest_ws : best.toNat < ws2.length := by omega
            let ws2' := (ws2.set pos.toNat (ws2[best.toNat]'hbest_ws)).set best.toNat
              (ws2[pos.toNat]'hpos_ws)
            have hperm' : (ws2'.take olen.toNat).Perm (s.scratch.work_stk2.take olen.toNat) :=
              (list_take_swap_perm ws2 (by omega) hpos_lt hbo (by omega)).trans hperm
            fvt_steps
            exact ih (pos + 1#32, ()) _ (by dsimp only; omega)
              ⟨by omega, by omega, ws2', by simp [ws2', hws2_len], hperm', by assumption⟩
          · exact ih (pos + 1#32, ()) mp (by dsimp only; omega)
              ⟨by omega, by omega, ws2, hws2_len, hperm, hm_p⟩
    · exact hQ ws2 mp hws2_len hperm hm_p
    · exact hQ ws2 mp hws2_len hperm hm_p

end UnreasonAndWatch

/-! ## 4. `full_viv_mark_garb_m6_wp`, `full_viv_subsumes_{bin,cl}_m6_wp` -/

section MarkGarbAndSubsume

/-- `full_viv_mark_garb_m6` satisfies `fullVivMarkGarbM6Spec` parametrically in `Γ`. -/
theorem full_viv_mark_garb_m6_wp (Γ : Env)
    (hUnreason : ∀ a m Q X, fullVivUnreasonM6Spec a m Q X →
      Γ "full_viv_unreason_m6" [i64, i32] [] a m Q X)
    (hUnwatch : ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X) :
    ∀ args m Q X, fullVivMarkGarbM6Spec args m Q X →
      Func.wp Γ full_viv_mark_garb_m6_body args m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s0, R, rfl, hsp0, href0, hm0, hQ⟩
  have hmx := c.hmaxv; have harc := c.harena; unfold dimacsBound at hmx harc
  unfold Func.wp full_viv_mark_garb_m6_body
  c0_call hUnreason
  refine ⟨c, F0, F_cur, s0, R, rfl, hsp0, hm0,
    fun s1 m1 hsp1 hna1 hcv1 har1 hal1 hpr1 hfu1 _ _ hrr1 htr1 hm1 => ?_⟩
  have href1 : cref.toNat ∈ fullArenaClauseRefs s1 := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har1, hal1]; exact href0
  have hrefs1 : fullArenaClauseRefs s1 = fullArenaClauseRefs s0 := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har1, hal1]
  have hwf1 := hsp1.2.1.arena.refs_wf cref.toNat href1
  have hcl1 := hsp1.1.core_ok
  have hcr0_lt : cref.toNat < s1.core.arena.length := by
    have := hcl1.arena_len_arr; have := hcl1.arena_len_le; omega
  have hcr2_lt : (cref.setWidth 64 + 2#64).toNat < s1.core.arena.length := by
    have := hcl1.arena_len_arr; have := hcl1.arena_len_le; bv_omega
  have hcr3_lt : (cref.setWidth 64 + 3#64).toNat < s1.core.arena.length := by
    have := hcl1.arena_len_arr; have := hcl1.arena_len_le; bv_omega
  have hcr4_lt : (cref.setWidth 64 + 4#64).toNat < s1.core.arena.length := by
    have := hcl1.arena_len_arr; have := hcl1.arena_len_le; bv_omega
  fvt_steps
  · exact hQ s1 m1 hsp1 hcv1 hal1 hpr1 hfu1 hrefs1 hrr1 htr1 hm1
  · have hlay1 : WatchStackLayout s1.core := by
      have hmw := hsp1.2.1.watches; unfold ModeWatchesInv at hmw
      rw [ite_eq_left hsp1.2.2.2.2.2] at hmw; exact hmw.layout
    c0_call hUnwatch
    refine ⟨c, s1, R, rfl, hsp1.1, hlay1, hm1,
      fun wvec2 wstk2 wu2 m2 hlen2 hlay2 hmw2 hm2 => ?_⟩
    let s2 : FullState :=
      { s1 with core := { s1.core with wvec := wvec2, wstk := wstk2, wusable := wu2 } }
    have hsp2 : FullSparseInvW c F0 F_cur s2 :=
      ⟨hlen2,
        { hsp1.2.1 with
          arena := { hsp1.2.1.arena with len_ok := hsp1.2.1.arena.len_ok }
          watches := hmw2 F_cur hsp1.2.1.watches },
        hsp1.2.2.1, hsp1.2.2.2.1, hsp1.2.2.2.2.1, hsp1.2.2.2.2.2⟩
    fvt_steps
    c0_call hUnwatch
    refine ⟨c, s2, R, rfl, hsp2.1, hlay2, hm2,
      fun wvec3 wstk3 wu3 m3 hlen3 _ hmw3 hm3 => ?_⟩
    let s3 : FullState :=
      { s2 with core := { s2.core with wvec := wvec3, wstk := wstk3, wusable := wu3 } }
    have hsp3 : FullSparseInvW c F0 F_cur s3 :=
      ⟨hlen3,
        { hsp2.2.1 with
          arena := { hsp2.2.1.arena with len_ok := hsp2.2.1.arena.len_ok }
          watches := hmw3 F_cur hsp2.2.1.watches },
        hsp2.2.2.1, hsp2.2.2.2.1, hsp2.2.2.2.2.1, hsp2.2.2.2.2.2⟩
    have hhdr3 : s1.core.arena[cref.toNat]'hcr0_lt = fullArenaHdr s3 cref.toNat := by
      unfold fullArenaHdr fullArenaHdrCore; dsimp only [s3, s2]
      rw [List.getElem?_eq_getElem hcr0_lt, Option.getD_some]
    fvt_to_group
    refine wp_join_group (ts := [])
      (fun () mf => ∃ ni' nr',
        let sf : FullState :=
          { s3 with core :=
            { s3.core with
              arena := s3.core.arena.set cref.toNat (fullArenaHdr s3 cref.toNat ||| 0x00080000#32)
              arena_garbage := s3.core.arena_garbage + 3#64 +
                (s1.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_lt).setWidth 64
              num_irred := ni', num_redundant := nr' } }
        (FullMem c sf ⋆ R) mf) ?_ ?_
    · rintro _ ⟨⟩ mf ⟨ni', nr', hmf⟩
      fvt_steps
      obtain ⟨hsp_f, hrefs_f⟩ := markGarb_hnonact_preserves_fullSparseW hsp3 href1 hna1
        (s3.core.arena_garbage + 3#64 +
          (s1.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_lt).setWidth 64)
        ni' nr' (s3.scratch.viv_cnt + 1#64)
      exact hQ _ _ hsp_f hcv1 hal1 hpr1 hfu1 (hrefs_f.trans hrefs1) hrr1 htr1 (by assumption)
    · intro Jf hJf
      have har_eq : s3.core.arena.set cref.toNat (s1.core.arena[cref.toNat]'hcr0_lt ||| 524288) =
          s3.core.arena.set cref.toNat (fullArenaHdr s3 cref.toNat ||| 0x00080000#32) := by
        rw [hhdr3]; rfl
      fvt_steps
      · exact hJf () _ ⟨s3.core.num_irred, s3.core.num_redundant - 1#64, by rw [← har_eq]; exact hm⟩
      · exact hJf () _ ⟨s3.core.num_irred, s3.core.num_redundant, by rw [← har_eq]; exact hm⟩
      · exact hJf () _ ⟨s3.core.num_irred - 1#64, s3.core.num_redundant, by rw [← har_eq]; exact hm⟩
      · exact hJf () _ ⟨s3.core.num_irred, s3.core.num_redundant, by rw [← har_eq]; exact hm⟩

/-- `full_viv_subsumes_bin_m6` satisfies `fullVivSubsumesBinM6Spec` parametrically in `Γ`. -/
theorem full_viv_subsumes_bin_m6_wp (Γ : Env) :
    ∀ args m Q X, fullVivSubsumesBinM6Spec args m Q X →
      Func.wp Γ full_viv_subsumes_bin_m6_body args m Q X := by
  rintro ⟨h, a, b, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, ha, hb, hm, hQ⟩
  have hcl := hlen.core_ok; have hcv := hcl.cur_vars_le
  have ha_lm : a.toNat < s.core.lit_mark.length := by rw [hcl.lit_mark_len]; omega
  have hb_lm : b.toNat < s.core.lit_mark.length := by rw [hcl.lit_mark_len]; omega
  have ha_v : a.toNat < s.core.vals.length := by rw [hcl.vals_len]; omega
  have hb_v : b.toNat < s.core.vals.length := by rw [hcl.vals_len]; omega
  have ha_l : (a >>> 1#32).toNat < s.core.lvl.length := by
    rw [bv32_lshr1_toNat, hcl.lvl_len]; omega
  have hb_l : (b >>> 1#32).toNat < s.core.lvl.length := by
    rw [bv32_lshr1_toNat, hcl.lvl_len]; omega
  unfold Func.wp full_viv_subsumes_bin_m6_body
  fvt_steps <;> exact hQ _

/-- `full_viv_subsumes_cl_m6` satisfies `fullVivSubsumesClM6Spec` parametrically in `Γ`. -/
theorem full_viv_subsumes_cl_m6_wp (Γ : Env) :
    ∀ args m Q X, fullVivSubsumesClM6Spec args m Q X →
      Func.wp Γ full_viv_subsumes_cl_m6_body args m Q X := by
  rintro ⟨h, rcr, sz, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, href, hng, hm0, hQ⟩
  have hcl := hlen.core_ok; have hcv := hcl.cur_vars_le
  have harc := c.harena; unfold dimacsBound at harc
  have hwf := hw.arena.refs_wf rcr.toNat href
  have hbd : rcr.toNat + 3 + fullArenaClauseSizeCore s.core rcr.toNat ≤ s.core.arena.length := by
    have := hcl.arena_len_arr; have := hcl.arena_len_le; omega
  have hrcr2_eq : (rcr.setWidth 64 + 2#64).toNat = rcr.toNat + 2 := by bv_omega
  have hrcr2_lt : (rcr.setWidth 64 + 2#64).toNat < s.core.arena.length := by omega
  let rsz := s.core.arena[(rcr.setWidth 64 + 2#64).toNat]'hrcr2_lt
  have hrsz_eq : rsz.toNat = fullArenaClauseSizeCore s.core rcr.toNat := by
    unfold fullArenaClauseSizeCore; dsimp only [rsz]
    rw [← hrcr2_eq, List.getElem?_eq_getElem hrcr2_lt, Option.getD_some]
  unfold Func.wp full_viv_subsumes_cl_m6_body
  fvt_steps
  · exact hQ false
  · refine wp_loop_inv (ts := [i32])
      (fun (j, ()) mj => m0 = mj ∧ j.toNat ≤ rsz.toNat)
      (fun (j, _) _ => rsz.toNat - j.toNat) ?_ ?_
    · intro J hJ; fvt_steps; exact hJ (0#32, ()) m0 ⟨rfl, Nat.zero_le _⟩
    · rintro J ⟨j, ⟨⟩⟩ mj ⟨rfl, hj_le⟩ ih
      fvt_step; fvt_step
      · have hj_lt : j.toNat < rsz.toNat := by dsimp only [rsz]; c0_bound
        have hidx_eq : (rcr.setWidth 64 + 3#64 + j.setWidth 64).toNat =
            rcr.toNat + 3 + j.toNat := by bv_omega
        have hidx_lt : (rcr.setWidth 64 + 3#64 + j.setWidth 64).toNat < s.core.arena.length := by
          omega
        let sl := s.core.arena[(rcr.setWidth 64 + 3#64 + j.setWidth 64).toNat]'hidx_lt
        have hsl_lt : sl.toNat < 2 * s.core.cur_vars := by
          have hmem : sl.toNat ∈ fullArenaClauseLitsCore s.core rcr.toNat := by
            refine (mem_fullArenaClauseLitsCore_iff hbd).mpr ⟨j.toNat, by omega, ?_⟩
            dsimp only [sl]; simp only [hidx_eq]
          exact hw.arena.lits_lt rcr.toNat href hng _ hmem
        have hsl_lm : sl.toNat < s.core.lit_mark.length := by rw [hcl.lit_mark_len]; omega
        have hsl_v : sl.toNat < s.core.vals.length := by rw [hcl.vals_len]; omega
        have hsl_l : (sl >>> 1#32).toNat < s.core.lvl.length := by
          rw [bv32_lshr1_toNat, hcl.lvl_len]; omega
        have hj1 : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
        fvt_steps
        · exact ih (j + 1#32, ()) m0 (by dsimp only; omega) ⟨rfl, by omega⟩
        · exact hQ false
        · exact hQ false
        · exact ih (j + 1#32, ()) m0 (by dsimp only; omega) ⟨rfl, by omega⟩
      · fvt_steps; exact hQ true

end MarkGarbAndSubsume

/-! ## 5. `best_implied`, `reestablish`, and `inst_check` -/

section ImpliedReestablishInst

/-- `full_viv_best_implied_m6` satisfies `fullVivBestImpliedM6Spec` parametrically in `Γ`. -/
theorem full_viv_best_implied_m6_wp (Γ : Env) :
    ∀ args m Q X, fullVivBestImpliedM6Spec args m Q X →
      Func.wp Γ full_viv_best_implied_m6_body args m Q X := by
  rintro ⟨h, sz, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hsz_le, htmp_lt, hm0, hQ⟩
  have hcl := hsp.1.core_ok; have hw := hsp.2.1; have hcv := hcl.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  unfold Func.wp full_viv_best_implied_m6_body
  fvt_to_group
  refine wp_loop_inv (ts := [i32, i32, i32])
    (fun (best, _bpos, i, ()) mi =>
      m0 = mi ∧ i.toNat ≤ sz.toNat ∧
      (best ≠ 0xFFFFFFFF#32 →
        best.toNat < 2 * s.core.cur_vars ∧ s.core.vals[best.toNat]?.getD 0#8 = 1#8))
    (fun (_, _, i, _) _ => sz.toNat - i.toNat) ?_ ?_
  · intro J hJ; fvt_steps
    exact hJ (0xFFFFFFFF#32, 0xFFFFFFFF#32, 0#32, ()) m0
      ⟨rfl, Nat.zero_le _, fun h => absurd rfl h⟩
  · rintro J ⟨best, bpos, i, ⟨⟩⟩ mi ⟨rfl, hi_le, hbest⟩ ih
    fvt_step; fvt_step
    · have hi_lt : i.toNat < sz.toNat := by c0_bound
      have hi_tmp : i.toNat < s.core.tmp.length := by rw [hcl.tmp_len_arr]; omega
      let l := s.core.tmp[i.toNat]'hi_tmp
      have hl_lt : l.toNat < 2 * s.core.cur_vars := by
        have := htmp_lt i.toNat hi_lt
        rwa [List.getElem?_eq_getElem hi_tmp, Option.getD_some] at this
      have hl_v : l.toNat < s.core.vals.length := by rw [hcl.vals_len]; omega
      have hl_tp : (l >>> 1#32).toNat < s.core.trail_pos.length := by
        rw [bv32_lshr1_toNat, hcl.trail_pos_len]; omega
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
      fvt_steps
      · have hv1 : s.core.vals[l.toNat]?.getD 0#8 = 1#8 := by
          rw [List.getElem?_eq_getElem hl_v, Option.getD_some]
          have hdom := hw.vals_domain l.toNat hl_lt
          rw [List.getElem?_eq_getElem hl_v, Option.getD_some] at hdom
          exact (bv8_dom_sgt0_iff hdom).mp (by assumption)
        exact ih (l, _, i + 1#32, ()) m0 (by dsimp only; omega)
          ⟨rfl, by omega, fun _ => ⟨hl_lt, hv1⟩⟩
      · have hv1 : s.core.vals[l.toNat]?.getD 0#8 = 1#8 := by
          rw [List.getElem?_eq_getElem hl_v, Option.getD_some]
          have hdom := hw.vals_domain l.toNat hl_lt
          rw [List.getElem?_eq_getElem hl_v, Option.getD_some] at hdom
          exact (bv8_dom_sgt0_iff hdom).mp (by assumption)
        exact ih (l, _, i + 1#32, ()) m0 (by dsimp only; omega)
          ⟨rfl, by omega, fun _ => ⟨hl_lt, hv1⟩⟩
      · exact ih (best, bpos, i + 1#32, ()) m0 (by dsimp only; omega) ⟨rfl, by omega, hbest⟩
      · exact ih (best, bpos, i + 1#32, ()) m0 (by dsimp only; omega) ⟨rfl, by omega, hbest⟩
    · fvt_steps; exact hQ best hbest

/-- `full_viv_reestablish_m6` satisfies `fullVivReestablishM6Spec` parametrically in `Γ`. -/
theorem full_viv_reestablish_m6_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X) :
    ∀ args m Q X, fullVivReestablishM6Spec args m Q X →
      Func.wp Γ full_viv_reestablish_m6_body args m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hsp, href, hm0, hQ⟩
  have hcl := hsp.1.core_ok; have hw := hsp.2.1; have hcv := hcl.cur_vars_le
  have hmx := c.hmaxv; have harc := c.harena; unfold dimacsBound at hmx harc
  have hwf := hw.arena.refs_wf cref.toNat href
  have hcl_le : s.core.cur_level ≤ c.max_vars := by
    have := hw.cur_level_le; have := hcl.trail_end_le; omega
  have hcl_lt64 : s.core.cur_level < 2 ^ 64 := by omega
  have hcr0_lt : cref.toNat < s.core.arena.length := by
    have := hcl.arena_len_arr; have := hcl.arena_len_le; omega
  have hcr0_bv : (cref.setWidth 64).toNat < s.core.arena.length := by bv_omega
  have hbd : cref.toNat + 3 + fullArenaClauseSizeCore s.core cref.toNat ≤
      s.core.arena.length := by
    have := hcl.arena_len_arr; have := hcl.arena_len_le; omega
  have hcr3_eq : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3 := by bv_omega
  have hcr4_eq : (cref.setWidth 64 + 4#64).toNat = cref.toNat + 4 := by bv_omega
  have hcr3_lt : (cref.setWidth 64 + 3#64).toNat < s.core.arena.length := by
    have := hwf.2.1; omega
  have hcr4_lt : (cref.setWidth 64 + 4#64).toNat < s.core.arena.length := by
    have := hwf.2.1; omega
  unfold Func.wp full_viv_reestablish_m6_body
  fvt_steps
  · exact hQ s m0 hsp rfl rfl rfl rfl rfl rfl rfl hm0
  · exact hQ s m0 hsp rfl rfl rfl rfl rfl rfl rfl hm0
  · have hng : fullArenaClauseGarb s cref.toNat = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
      rw [List.getElem?_eq_getElem hcr0_lt, Option.getD_some]
      have h0 : (s.core.arena[cref.toNat]'hcr0_lt &&& 0x00080000#32) = 0#32 := by assumption
      simp [h0]
    let l0 := s.core.arena[(cref.setWidth 64 + 3#64).toNat]'hcr3_lt
    let l1 := s.core.arena[(cref.setWidth 64 + 4#64).toNat]'hcr4_lt
    have hl0_lt : l0.toNat < 2 * s.core.cur_vars :=
      hw.arena.lits_lt cref.toNat href hng _
        ((mem_fullArenaClauseLitsCore_iff hbd).mpr ⟨0, by have := hwf.2.1; omega, by
          dsimp only [l0]; simp only [hcr3_eq, Nat.add_zero]⟩)
    have hl1_lt : l1.toNat < 2 * s.core.cur_vars :=
      hw.arena.lits_lt cref.toNat href hng _
        ((mem_fullArenaClauseLitsCore_iff hbd).mpr ⟨1, by have := hwf.2.1; omega, by
          dsimp only [l1]; simp only [hcr4_eq]⟩)
    have hl0_v : l0.toNat < s.core.vals.length := by rw [hcl.vals_len]; omega
    have hl1_v : l1.toNat < s.core.vals.length := by rw [hcl.vals_len]; omega
    have hl0_l : (l0 >>> 1#32).toNat < s.core.lvl.length := by
      rw [bv32_lshr1_toNat, hcl.lvl_len]; omega
    have hl1_l : (l1 >>> 1#32).toNat < s.core.lvl.length := by
      rw [bv32_lshr1_toNat, hcl.lvl_len]; omega
    -- Step through `lvl0`/`lvl1` ternaries and `new_lvl` selection to final `if`
    fvt_to_group
    refine wp_join_group (ts := [i64]) (fun _ m1 => m0 = m1)
      (fun _ ⟨_, ⟨⟩⟩ m1 hm1 => by
        subst hm1; fvt_to_group
        refine wp_join_group (ts := [i64]) (fun _ m2 => m0 = m2)
          (fun _ ⟨_, ⟨⟩⟩ m2 hm2 => by
            subst hm2; fvt_to_group
            refine wp_join_group (ts := [i64]) (fun _ m3 => m0 = m3)
              (fun _ ⟨nl, ⟨⟩⟩ m3 hm3 => by
                subst hm3; fvt_to_group
                refine wp_join_group (ts := [])
                  (fun _ mf => ∃ sf, FullSparseInvW c F0 F_cur sf ∧
                    sf.core.cur_vars = s.core.cur_vars ∧ sf.core.arena = s.core.arena ∧
                    sf.core.arena_len = s.core.arena_len ∧ sf.core.probing = s.core.probing ∧
                    sf.core.fuel = s.core.fuel ∧ sf.scratch.red_refs = s.scratch.red_refs ∧
                    sf.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ (FullMem c sf ⋆ R) mf)
                  (fun _ _ mf ⟨sf, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ => by
                    fvt_steps; exact hQ sf mf h1 h2 h3 h4 h5 h6 h7 h8 h9)
                  (fun J4 hJ4 => by
                    fvt_steps
                    · have hlt : (nl - 1).toNat < s.core.cur_level := by
                        have h1 : (nl - 1).toNat < (BitVec.ofNat 64 s.core.cur_level).toNat := by
                          c0_bound
                        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_lt64] at h1
                      c0_call hBacktrack
                      refine ⟨c, s, R, rfl, hsp.1, hcl_lt64, fun _ => by omega, hw.trail_lits_lt,
                        hm0, fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
                          hlen_bt _ _ _ hpres_bt hsc_bt _ _ hw_bt _ hm_bt => ?_⟩
                      have hsp_bt : FullSparseInvW c F0 F_cur _ :=
                        FullVivTop.FullSparseInvW.of_backtrack hsp (Nat.le_of_lt hlt) hlen_bt
                          hpres_bt (hw_bt F0 F_cur hw (Nat.le_of_lt hlt))
                      rcases hsc_bt with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
                      fvt_steps
                      exact hJ4 () m_bt ⟨_, hsp_bt, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm_bt⟩
                    · exact hJ4 () m0 ⟨s, hsp, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm0⟩
                    · exact hJ4 () m0 ⟨s, hsp, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm0⟩))
              (fun J3 hJ3 => by fvt_steps <;> exact hJ3 (_, ()) m0 rfl))
          (fun J2 hJ2 => by fvt_steps <;> exact hJ2 (_, ()) m0 rfl))
      (fun J1 hJ1 => by fvt_steps <;> exact hJ1 (_, ()) m0 rfl)

/-- `full_viv_inst_check_m6` satisfies `fullVivInstCheckM6Spec` parametrically in `Γ`. -/
theorem full_viv_inst_check_m6_wp (Γ : Env) :
    ∀ args m Q X, fullVivInstCheckM6Spec args m Q X →
      Func.wp Γ full_viv_inst_check_m6_body args m Q X := by
  rintro ⟨h, sz, iolen, not_lit, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hsp0, hsz_pos, hsz_le, hiol_le, htmp_lt, hws2_lt, hm0, hQ⟩
  have hcl0 := hsp0.1.core_ok; have hcv := hcl0.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hlm0_len := hcl0.lit_mark_len
  unfold Func.wp full_viv_inst_check_m6_body
  fvt_to_group
  -- Loop 1: mark `lm[tmp[k]] = 1` for `k + 1 < sz`
  refine wp_loop_inv (ts := [i32])
    (fun (k, ()) mk =>
      k.toNat + 1 ≤ sz.toNat ∧
      ∃ lm1 : List (BitVec 8), lm1.length = 2 * c.max_vars ∧
        (∀ l < 2 * c.max_vars,
          lm1[l]?.getD 0#8 ≠ 0#8 ↔
            ∃ t < k.toNat, (s.core.tmp[t]?.getD 0#32).toNat = l) ∧
        (FullMem c { s with core := { s.core with lit_mark := lm1 } } ⋆ R) mk)
    (fun (k, _) _ => sz.toNat - 1 - k.toNat) ?_ ?_
  · intro J1 hJ1; fvt_steps
    exact hJ1 (0#32, ()) m0 ⟨by simp; omega, s.core.lit_mark, hlm0_len,
      fun l hl => ⟨fun h => absurd (hsp0.2.2.1.2 l hl) h, fun ⟨_, ht, _⟩ => by simp at ht⟩, hm0⟩
  · rintro J1 ⟨k, ⟨⟩⟩ m_k ⟨hk_le, lm1, hlm1_len, hlm1_iff, hmk⟩ ih1
    fvt_step; fvt_step
    · have hk1_lt : k.toNat + 1 < sz.toNat := by
        have h1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
        have : (k + 1#32).toNat < sz.toNat := by c0_bound
        omega
      have hk1_eq : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
      have hk_tmp : k.toNat < s.core.tmp.length := by rw [hcl0.tmp_len_arr]; omega
      let l := s.core.tmp[k.toNat]'hk_tmp
      have hl_lt : l.toNat < 2 * c.max_vars := by
        have := htmp_lt k.toNat (by omega)
        rw [List.getElem?_eq_getElem hk_tmp, Option.getD_some] at this
        dsimp only [l]; omega
      have hl_lm : l.toNat < lm1.length := by omega
      fvt_steps
      let lm1' := lm1.set l.toNat 1#8
      refine ih1 (k + 1#32, ()) _ (by dsimp only; omega)
        ⟨by omega, lm1', by simp [lm1', hlm1_len], fun q hq => ?_, by assumption⟩
      by_cases hql : q = l.toNat
      · subst hql; dsimp only [lm1']
        rw [List.getElem?_set_self hl_lm, Option.getD_some]
        refine ⟨fun _ => ⟨k.toNat, by omega, ?_⟩, fun _ => by decide⟩
        rw [List.getElem?_eq_getElem hk_tmp, Option.getD_some]
      · dsimp only [lm1']; rw [List.getElem?_set_ne (Ne.symm hql), hlm1_iff q hq]
        constructor
        · rintro ⟨t, ht, hteq⟩; exact ⟨t, by omega, hteq⟩
        · rintro ⟨t, ht, hteq⟩
          rw [hk1_eq] at ht
          rcases (by omega : t < k.toNat ∨ t = k.toNat) with h1 | rfl
          · exact ⟨t, h1, hteq⟩
          · rw [List.getElem?_eq_getElem hk_tmp, Option.getD_some] at hteq
            exact absurd hteq.symm hql
    · have hk_end : k.toNat + 1 = sz.toNat := by
        have h1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
        have : sz.toNat ≤ (k + 1#32).toNat := by c0_bound
        omega
      -- Loop 2: scan `i < iolen` with `break`
      fvt_to_group
      refine wp_loop_break_group (brkTs := [.bool, i32]) (lpTs := [i32])
        (fun (ok_b, _ib, ()) mb =>
          m_k = mb ∧
          (ok_b = true → ∀ i < iolen.toNat,
            s.scratch.work_stk2[i]?.getD 0#32 = not_lit ∨
            ∃ t, t + 1 < sz.toNat ∧
              s.scratch.work_stk2[i]?.getD 0#32 = s.core.tmp[t]?.getD 0#32))
        (fun rem (i, ()) mi =>
          m_k = mi ∧ i.toNat ≤ iolen.toNat ∧ rem = iolen.toNat - i.toNat ∧
          ∀ j < i.toNat,
            s.scratch.work_stk2[j]?.getD 0#32 = not_lit ∨
            ∃ t, t + 1 < sz.toNat ∧
              s.scratch.work_stk2[j]?.getD 0#32 = s.core.tmp[t]?.getD 0#32)
        ?_ ?_ ?_
      · -- After Loop 2: Loop 3 clears `lm[tmp[k2]] = 0` for `k2 + 1 < sz`
        rintro _ ⟨ok_b, _ib, ⟨⟩⟩ mb ⟨rfl, hok_b⟩
        fvt_to_group
        refine wp_loop_inv (ts := [i32])
          (fun (k2, ()) m2 =>
            k2.toNat + 1 ≤ sz.toNat ∧
            ∃ lm2 : List (BitVec 8), lm2.length = 2 * c.max_vars ∧
              (∀ l < 2 * c.max_vars,
                lm2[l]?.getD 0#8 ≠ 0#8 →
                  ∃ t, k2.toNat ≤ t ∧ t + 1 < sz.toNat ∧ (s.core.tmp[t]?.getD 0#32).toNat = l) ∧
              (FullMem c { s with core := { s.core with lit_mark := lm2 } } ⋆ R) m2)
          (fun (k2, _) _ => sz.toNat - 1 - k2.toNat) ?_ ?_
        · intro J3 hJ3; fvt_steps
          exact hJ3 (0#32, ()) m_k ⟨by simp; omega, lm1, hlm1_len, fun l hl hnz => by
            obtain ⟨t, ht, hteq⟩ := (hlm1_iff l hl).mp hnz
            exact ⟨t, Nat.zero_le _, by omega, hteq⟩, hmk⟩
        · rintro J3 ⟨k2, ⟨⟩⟩ m2 ⟨hk2_le, lm2, hlm2_len, hlm2_dom, hm2⟩ ih3
          fvt_step; fvt_step
          · have hk2_lt : k2.toNat + 1 < sz.toNat := by
              have h1 : (k2 + 1#32).toNat = k2.toNat + 1 := by bv_omega
              have : (k2 + 1#32).toNat < sz.toNat := by c0_bound
              omega
            have hk2_1 : (k2 + 1#32).toNat = k2.toNat + 1 := by bv_omega
            have hk2_tmp : k2.toNat < s.core.tmp.length := by rw [hcl0.tmp_len_arr]; omega
            let l2 := s.core.tmp[k2.toNat]'hk2_tmp
            have hl2_lt : l2.toNat < 2 * c.max_vars := by
              have := htmp_lt k2.toNat (by omega)
              rw [List.getElem?_eq_getElem hk2_tmp, Option.getD_some] at this
              dsimp only [l2]; omega
            have hl2_lm : l2.toNat < lm2.length := by omega
            fvt_steps
            let lm2' := lm2.set l2.toNat 0#8
            refine ih3 (k2 + 1#32, ()) _ (by dsimp only; omega)
              ⟨by omega, lm2', by simp [lm2', hlm2_len], fun q hq hnz => ?_, by assumption⟩
            by_cases hql : q = l2.toNat
            · subst hql; dsimp only [lm2'] at hnz
              rw [List.getElem?_set_self hl2_lm, Option.getD_some] at hnz
              exact absurd rfl hnz
            · dsimp only [lm2'] at hnz; rw [List.getElem?_set_ne (Ne.symm hql)] at hnz
              obtain ⟨t, ht1, ht2, hteq⟩ := hlm2_dom q hq hnz
              have hne_t : t ≠ k2.toNat := fun he => by
                subst he; rw [List.getElem?_eq_getElem hk2_tmp, Option.getD_some] at hteq
                exact hql hteq.symm
              exact ⟨t, by omega, ht2, hteq⟩
          · have hk2_end : k2.toNat + 1 = sz.toNat := by
              have h1 : (k2 + 1#32).toNat = k2.toNat + 1 := by bv_omega
              have : sz.toNat ≤ (k2 + 1#32).toNat := by c0_bound
              omega
            have hclr : FullLitMarksClear c { s with core := { s.core with lit_mark := lm2 } } :=
              ⟨hsp0.2.2.1.1, fun l hl => Classical.byContradiction fun hnz => by
                obtain ⟨t, ht1, ht2, _⟩ := hlm2_dom l hl hnz; omega⟩
            have hsp_f : FullSparseInvW c F0 F_cur
                { s with core := { s.core with lit_mark := lm2 } } :=
              ⟨⟨{ hcl0 with lit_mark_len := hlm2_len }, hsp0.1.scratch_ok⟩,
                { hsp0.2.1 with
                  arena := { hsp0.2.1.arena with len_ok := hsp0.2.1.arena.len_ok }
                  watches := hsp0.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
                hclr, hsp0.2.2.2.1, hsp0.2.2.2.2.1, hsp0.2.2.2.2.2⟩
            fvt_steps; exact hQ ok_b lm2 m2 hsp_f hok_b hm2
      · -- Loop 2 body
        intro B L rem ⟨i, ⟨⟩⟩ mi hB hL ⟨rfl, hi_le, hrem, hprev⟩
        subst hrem
        fvt_step; fvt_step
        · have hi_lt : i.toNat < iolen.toNat := by c0_bound
          have hi_ws : i.toNat < s.scratch.work_stk2.length := by
            rw [hsp0.1.scratch_ok.work_stk2_len]; omega
          let x := s.scratch.work_stk2[i.toNat]'hi_ws
          have hx_lt : x.toNat < 2 * c.max_vars := by
            have := hws2_lt i.toNat hi_lt
            rw [List.getElem?_eq_getElem hi_ws, Option.getD_some] at this
            dsimp only [x]; omega
          have hx_lm : x.toNat < lm1.length := by omega
          have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
          fvt_steps
          · -- `x != not_lit && lm1[x] == 0` -> `ok = false; break;`
            exact hB (false, i, ()) m_k ⟨rfl, fun h => by cases h⟩
          · -- `x != not_lit && lm1[x] != 0`
            have hnz : lm1[x.toNat]?.getD 0#8 ≠ 0#8 := by
              rw [List.getElem?_eq_getElem hx_lm, Option.getD_some]
              intro h0
              have hne32 : (lm1[x.toNat]'hx_lm).setWidth 32 ≠ 0#32 := by assumption
              exact hne32 ((bv8_zext32_eq0_iff _).mpr h0)
            obtain ⟨t, ht, hteq⟩ := (hlm1_iff x.toNat hx_lt).mp hnz
            refine hL (iolen.toNat - (i + 1#32).toNat) (i + 1#32, ()) m_k (by omega)
              ⟨rfl, by omega, rfl, fun j hj => ?_⟩
            rw [hi1] at hj
            rcases (by omega : j < i.toNat ∨ j = i.toNat) with h1 | rfl
            · exact hprev j h1
            · right; refine ⟨t, by omega, ?_⟩
              rw [List.getElem?_eq_getElem hi_ws, Option.getD_some]
              exact BitVec.eq_of_toNat_eq hteq.symm
          · -- `x == not_lit`
            have hxeq : x = not_lit := by c0_bound
            refine hL (iolen.toNat - (i + 1#32).toNat) (i + 1#32, ()) m_k (by omega)
              ⟨rfl, by omega, rfl, fun j hj => ?_⟩
            rw [hi1] at hj
            rcases (by omega : j < i.toNat ∨ j = i.toNat) with h1 | rfl
            · exact hprev j h1
            · left; rw [List.getElem?_eq_getElem hi_ws, Option.getD_some]; exact hxeq
        · have hi_eq : i.toNat = iolen.toNat := by
            have : iolen.toNat ≤ i.toNat := by c0_bound
            omega
          fvt_steps
          exact hB (true, i, ()) m_k ⟨rfl, fun _ j hj => hprev j (hi_eq ▸ hj)⟩
      · intro B L _ hL; fvt_steps
        exact hL iolen.toNat (0#32, ()) m_k ⟨rfl, Nat.zero_le _, by simp, fun _ h => by simp at h⟩

end ImpliedReestablishInst

end LeanQbe.T.Examples.Kissat.FullM6VivBackbone
