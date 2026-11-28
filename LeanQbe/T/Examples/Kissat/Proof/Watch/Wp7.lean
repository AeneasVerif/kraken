/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Helpers
public import LeanQbe.T.Examples.Kissat.Src.Watch

import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Grind
import LeanQbe.T.Logic.ControlComb

/-! # Watch WP Proofs Part 7: `full_has_ternary`

Proves `Func.wp` for `full_has_ternary` (`Proof.Spec.fullHasTernarySpec`)
using `CanonicalEnv` (`Γ.Sat Spec.specs`). -/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Watch

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Grind
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Watch
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test
open scoped FullArenaTactics

public section

private theorem ht_wvec_get {c : FullCfg} {k : FullCoreState} (hl : k.LengthsOk c)
    (_hcv : c.max_vars < 2 * 2 ^ 28) (x : BitVec 32) (hx : x.toNat < 2 * k.cur_vars)
    (hw1 : (BitVec.setWidth 64 x <<< 1 + 1).toNat < k.wvec.length) :
    k.wvec[(BitVec.setWidth 64 x <<< 1 + 1).toNat]'hw1 = k.wvec[2 * x.toNat + 1]?.getD 0#32 := by
  have hcv_le := hl.cur_vars_le; have hwvl := hl.wvec_len
  rw [list_getElem_congr hw1 (bv64_shl1_add1_lit x),
    List.getElem?_eq_getElem (by omega), Option.getD_some]

private theorem ht_slice_pop_step {F_cur : List (List Nat)} {k : FullCoreState} {a p rem : Nat}
    (hslice : if k.dense_mode = 0#64 then WatchSliceOk F_cur k a p rem
      else DenseWatchSliceOk F_cur k a p rem) (hpos : 0 < rem) :
    ∃ w0 : BitVec 32, k.wstk[p]? = some w0 ∧
      ((w0 &&& 0x80000000#32) ≠ 0#32 ∧
        (if k.dense_mode = 0#64 then WatchSliceOk F_cur k a (p + 1) (rem - 1)
         else DenseWatchSliceOk F_cur k a (p + 1) (rem - 1)) ∨
       (w0 &&& 0x80000000#32) = 0#32 ∧ 2 ≤ rem ∧
        ∃ cr : BitVec 32, k.wstk[p + 1]? = some cr ∧ cr.toNat ∈ fullArenaClauseRefsCore k ∧
        (if k.dense_mode = 0#64 then WatchSliceOk F_cur k a (p + 2) (rem - 2)
         else DenseWatchSliceOk F_cur k a (p + 2) (rem - 2))) := by
  by_cases hdm : k.dense_mode = 0#64
  · simp only [hdm, ↓reduceIte] at hslice ⊢
    cases hslice with
    | empty => omega
    | bin hp hf _ _ _ hrest => exact ⟨_, hp, Or.inl ⟨hf, hrest⟩⟩
    | large hp hp1 hf _ href hrest =>
      exact ⟨_, hp, Or.inr ⟨hf, by omega, _, hp1, href, by simpa [Nat.add_sub_cancel] using hrest⟩⟩
  · simp only [hdm, ↓reduceIte] at hslice ⊢
    cases hslice with
    | empty => omega
    | bin hp hf _ _ _ hrest => exact ⟨_, hp, Or.inl ⟨hf, hrest⟩⟩
    | occ hp hp1 hf _ _ href hrest =>
      exact ⟨_, hp, Or.inr ⟨hf, by omega, _, hp1, href, by simpa [Nat.add_sub_cancel] using hrest⟩⟩

private theorem ht_garb_false_of_and_480000 {hdr : BitVec 32}
    (h : (hdr &&& 0x00480000#32) = 0#32) :
    ((hdr &&& 0x00080000#32) != 0#32) = false := by
  have hz : (hdr &&& 0x00080000#32) = 0#32 := by
    calc hdr &&& 0x00080000#32
        = (hdr &&& 0x00480000#32) &&& 0x00080000#32 := by
          rw [BitVec.and_assoc, show (0x00480000#32 &&& 0x00080000#32) = 0x00080000#32 by decide]
      _ = 0#32 := by rw [h]; decide
  simp [hz]

private theorem ht_not_mem_erase_of_nodup {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {xs : List α} {x : α}, xs.Nodup → x ∉ xs.erase x
  | [], _, _ => by simp
  | y :: ys, x, hnd => by
    rw [List.nodup_cons] at hnd
    simp only [List.erase_cons]
    split
    · rename_i h; have : y = x := by simpa using h
      subst this; exact hnd.1
    · rename_i h; have hne : y ≠ x := by simpa using h
      simp only [List.mem_cons]
      rintro (rfl | hx)
      · exact hne rfl
      · exact ht_not_mem_erase_of_nodup hnd.2 hx

private theorem ht_nodup_lt_length_le : ∀ {n : Nat} {xs : List Nat},
    xs.Nodup → (∀ x ∈ xs, x < n) → xs.length ≤ n := by
  intro n; induction n with
  | zero =>
    intro xs _ hlt; cases xs with
    | nil => exact Nat.le_refl 0
    | cons x _ => exfalso; have := hlt x List.mem_cons_self; omega
  | succ n ih =>
    intro xs hnd hlt
    by_cases hmem : n ∈ xs
    · have hnd' : (xs.erase n).Nodup := hnd.erase n
      have hlt' : ∀ x ∈ xs.erase n, x < n := fun x hx => by
        have hxm : x ∈ xs := List.mem_of_mem_erase hx
        have hne : x ≠ n := fun heq => by
          subst heq; exact ht_not_mem_erase_of_nodup hnd hx
        have := hlt x hxm; omega
      have hle := ih hnd' hlt'
      have hlen : (xs.erase n).length = xs.length - 1 := List.length_erase_of_mem hmem
      have hpos : 0 < xs.length := List.length_pos_of_mem hmem; omega
    · have hlt' : ∀ x ∈ xs, x < n := fun x hx => by
        have hne : x ≠ n := fun h => hmem (h ▸ hx)
        have := hlt x hx; omega
      exact Nat.le_trans (ih hnd hlt') (Nat.le_succ n)

private theorem ht_nodup_of_map {α β : Type} {f : α → β} {xs : List α}
    (h : (xs.map f).Nodup) : xs.Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons a as ih =>
    rw [List.map_cons, List.nodup_cons] at h
    exact List.nodup_cons.mpr ⟨fun ha => h.1 (List.mem_map_of_mem ha), ih h.2⟩

private theorem ht_fullArenaClauseSize_le_cur_vars {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) (hnodup : FullArenaVarsNodup s) {r : Nat}
    (hr : r ∈ fullArenaClauseRefs s) (hg : fullArenaClauseGarb s r = false) :
    fullArenaClauseSize s r ≤ s.core.cur_vars := by
  have hwf := hw.arena.refs_wf r hr
  have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
    have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr; omega
  have hlen_lits : (fullArenaClauseLits s r).length = fullArenaClauseSizeCore s.core r := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    simp only [List.length_map, List.length_take, List.length_drop]; omega
  have hnd := hnodup r hr hg
  have hle := ht_nodup_lt_length_le (n := s.core.cur_vars) hnd fun v hv => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
    have hl_lt : l < 2 * s.core.cur_vars := hw.arena.lits_lt r hr hg l hl; omega
  rw [List.length_map, hlen_lits] at hle; exact hle

private theorem ht_nodup_len3_subset {xs : List Nat} {a b c : Nat}
    (hlen : xs.length = 3) (ha : a ∈ xs) (hb : b ∈ xs) (hc : c ∈ xs)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ x ∈ xs, x = a ∨ x = b ∨ x = c := by
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | _⟩⟩⟩
  · simp at hlen
  · simp at hlen
  · simp at hlen
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb hc hx
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl <;> rcases hx with rfl | rfl | rfl <;>
      simp_all
  · simp at hlen

private theorem ht_entails_of_eval_mem {f : CNF Nat} {xs : List Nat}
    (h : ∀ α : Nat → Bool, f.Sat α → ∃ l ∈ xs, evalLitVal α l = true) :
    f.EntailsClause (cnfClause xs) := by
  rw [CNF.entails_clause_def]; intro α hα
  rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true]; exact h α hα

private theorem ht_ternary_of_unassigned_hits {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) (_hnd : FullArenaVarsNodup s)
    (hcl0 : s.core.cur_level = 0) {cr : Nat} {a b cl : BitVec 32}
    (hcr : cr ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cr = false)
    (hnosat : ∀ k < fullArenaClauseSizeCore s.core cr,
      s.core.vals[(s.core.arena[cr + 3 + k]?.getD 0#32).toNat]?.getD 0#8 ≠ 1#8)
    (hcnt : ((fullArenaClauseLits s cr).filter
      (fun l => s.core.vals[l]?.getD 0#8 == 0#8)).length = 3)
    (ha : a.toNat ∈ (fullArenaClauseLits s cr).filter
      (fun l => s.core.vals[l]?.getD 0#8 == 0#8))
    (hb : b.toNat ∈ (fullArenaClauseLits s cr).filter
      (fun l => s.core.vals[l]?.getD 0#8 == 0#8))
    (hc : cl.toNat ∈ (fullArenaClauseLits s cr).filter
      (fun l => s.core.vals[l]?.getD 0#8 == 0#8))
    (hab : a ≠ b) (hac : a ≠ cl) (hbc : b ≠ cl) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat, cl.toNat]) := by
  have hwf := hw.arena.refs_wf cr hcr
  have hbd : cr + 3 + fullArenaClauseSizeCore s.core cr ≤ s.core.arena.length := by
    have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr; omega
  let unass := (fullArenaClauseLits s cr).filter (fun l => s.core.vals[l]?.getD 0#8 == 0#8)
  have hsub := ht_nodup_len3_subset hcnt ha hb hc
    (fun h => hab (BitVec.eq_of_toNat_eq h))
    (fun h => hac (BitVec.eq_of_toNat_eq h))
    (fun h => hbc (BitVec.eq_of_toNat_eq h))
  refine ht_entails_of_eval_mem fun α hα => ?_
  have hsat_cl := CNF.entails_clause_def.mp (hw.arena.entails cr hcr hng) α hα
  rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true] at hsat_cl
  obtain ⟨l, hl_mem, hl_true⟩ := hsat_cl
  have hl_lt : l < 2 * s.core.cur_vars := hw.arena.lits_lt cr hcr hng l hl_mem
  have hv_dom := hw.vals_domain l hl_lt
  obtain ⟨k, hk_lt, hget_k⟩ := (mem_fullArenaClauseLitsCore_iff hbd).mp hl_mem
  have hne1 : s.core.vals[l]?.getD 0#8 ≠ 1#8 := by
    have h := hnosat k hk_lt
    have hget_a : s.core.arena[cr + 3 + k]?.getD 0#32 = s.core.arena[cr + 3 + k]'(by omega) := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    rwa [hget_a, hget_k] at h
  rcases hv_dom with hv0 | hv1 | hvm1
  · have hl_un : l ∈ unass := List.mem_filter.mpr ⟨hl_mem, by simp [hv0]⟩
    rcases hsub l hl_un with rfl | rfl | rfl
    · exact ⟨a.toNat, by simp, hl_true⟩
    · exact ⟨b.toNat, by simp, hl_true⟩
    · exact ⟨cl.toNat, by simp, hl_true⟩
  · exact absurd hv1 hne1
  · exfalso
    obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl_lt).mp hvm1
    have hlvl0 : (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
      have := hw.lvl_le i hi; omega
    have hunit := hw.level0_sound i hi hlvl0; rw [heq] at hunit
    have hsat_u := CNF.entails_clause_def.mp hunit α hα
    rw [← clauseEvalVal_iff, clauseEvalVal] at hsat_u; have hln : l ^^^ 1 = litNeg l := rfl
    simp only [List.any_cons, List.any_nil, Bool.or_false, hln, evalLitVal_litNeg,
      hl_true] at hsat_u
    cases hsat_u

private def HtClauseInv (s : FullState) (a b cl : BitVec 32) (cr sz : Nat)
    (dist : Bool) (st : Nat × BitVec 32 × Nat) : Prop :=
  let (nf, mask, i) := st
  i ≤ sz ∧
  (dist = true →
    (∀ k < i, s.core.vals[(s.core.arena[cr + 3 + k]?.getD 0#32).toNat]?.getD 0#8 ≠ 1#8) ∧
    nf = (((fullArenaClauseLits s cr).take i).filter
      (fun l => s.core.vals[l]?.getD 0#8 == 0#8)).length ∧
    ((mask &&& 1#32) ≠ 0#32 → a.toNat ∈ ((fullArenaClauseLits s cr).take i).filter
      (fun l => s.core.vals[l]?.getD 0#8 == 0#8)) ∧
    ((mask &&& 2#32) ≠ 0#32 → b.toNat ∈ ((fullArenaClauseLits s cr).take i).filter
      (fun l => s.core.vals[l]?.getD 0#8 == 0#8)) ∧
    ((mask &&& 4#32) ≠ 0#32 → cl.toNat ∈ ((fullArenaClauseLits s cr).take i).filter
      (fun l => s.core.vals[l]?.getD 0#8 == 0#8)))

private theorem ht_sext8_eq_zero {x : BitVec 8}
    (h : BitVec.signExtend 32 x = 0#32) : x = 0#8 := by
  c0_bv_bit_grind

private theorem ht_take_succ {α : Type} :
    ∀ (xs : List α) {i : Nat} (hi : i < xs.length),
      xs.take (i + 1) = xs.take i ++ [xs[i]'hi]
  | [], _, hi => nomatch hi
  | _ :: _, 0, _ => by simp
  | x :: xs, i + 1, hi => by
    simp only [List.take_succ_cons, List.cons_append, List.getElem_cons_succ]
    congr 1; exact ht_take_succ xs (Nat.lt_of_succ_lt_succ hi)

private theorem ht_or_and_ne_zero (x y k : BitVec 32) (h : (x ||| y) &&& k ≠ 0#32) :
    x &&& k ≠ 0#32 ∨ y &&& k ≠ 0#32 := by
  by_cases hx : x &&& k = 0#32 <;> by_cases hy : y &&& k = 0#32
  · exfalso; apply h
    have hd : (x ||| y) &&& k = (x &&& k) ||| (y &&& k) := BitVec.eq_of_getLsbD_eq fun i => by
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
      intro _; cases x.getLsbD i <;> cases y.getLsbD i <;> cases k.getLsbD i <;> rfl
    rw [hd, hx, hy, BitVec.or_zero]
  · exact Or.inr hy
  · exact Or.inl hx
  · exact Or.inl hx

private theorem ht_lits_take_succ {s : FullState} {cr i : Nat}
    (hbd : cr + 3 + fullArenaClauseSizeCore s.core cr ≤ s.core.arena.length)
    (hi : i < fullArenaClauseSizeCore s.core cr) :
    (fullArenaClauseLits s cr).take (i + 1) =
      (fullArenaClauseLits s cr).take i ++ [(s.core.arena[cr + 3 + i]'(by omega)).toNat] := by
  have hlen : (fullArenaClauseLits s cr).length = fullArenaClauseSizeCore s.core cr := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    simp only [List.length_map, List.length_take, List.length_drop]; omega
  have hget : (fullArenaClauseLits s cr)[i]'(by rw [hlen]; exact hi) =
      (s.core.arena[cr + 3 + i]'(by omega)).toNat := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
  rw [← hget]; exact ht_take_succ (fullArenaClauseLits s cr) (by rw [hlen]; exact hi)

private theorem ht_clause_step_skip {s : FullState} {a b cl : BitVec 32} {cr sz i nf : Nat}
    {mask : BitVec 32} {dist : Bool} (hsz : sz = fullArenaClauseSizeCore s.core cr)
    (hbd : cr + 3 + sz ≤ s.core.arena.length) (hi : i < sz)
    (hinv : HtClauseInv s a b cl cr sz dist (nf, mask, i))
    {v : BitVec 8}
    (hv_eq : v = s.core.vals[(s.core.arena[cr + 3 + i]'(by omega)).toNat]?.getD 0#8)
    (hne1 : v ≠ 1#8) (hne0 : v ≠ 0#8) :
    HtClauseInv s a b cl cr sz dist (nf, mask, i + 1) := by
  refine ⟨by omega, fun hd => ?_⟩
  obtain ⟨hnosat, hnf, ha, hb, hc⟩ := hinv.2 hd
  have htk := ht_lits_take_succ (s := s) (cr := cr) (i := i) (hsz ▸ hbd) (hsz ▸ hi)
  have hfilt : ((fullArenaClauseLits s cr).take (i + 1)).filter
      (fun l => s.core.vals[l]?.getD 0#8 == 0#8) =
      ((fullArenaClauseLits s cr).take i).filter
      (fun l => s.core.vals[l]?.getD 0#8 == 0#8) := by
    rw [htk, List.filter_append, List.filter_cons]
    simp [hv_eq ▸ beq_false_of_ne hne0]
  refine ⟨fun k hk => ?_, hfilt ▸ hnf, hfilt ▸ ha, hfilt ▸ hb, hfilt ▸ hc⟩
  by_cases hki : k = i
  · subst hki
    have h_ak : s.core.arena[cr + 3 + k]?.getD 0#32 = s.core.arena[cr + 3 + k]'(by omega) := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [h_ak, ← hv_eq]; exact hne1
  · exact hnosat k (by omega)

private theorem ht_clause_step_unassigned {s : FullState} {a b cl : BitVec 32} {cr sz i nf : Nat}
    {mask hit : BitVec 32} {dist : Bool} (hsz : sz = fullArenaClauseSizeCore s.core cr)
    (hbd : cr + 3 + sz ≤ s.core.arena.length) (hi : i < sz)
    (hinv : HtClauseInv s a b cl cr sz dist (nf, mask, i))
    (hv0 : s.core.vals[(s.core.arena[cr + 3 + i]'(by omega)).toNat]?.getD 0#8 = 0#8)
    (hh1 : (hit &&& 1#32) ≠ 0#32 → (s.core.arena[cr + 3 + i]'(by omega)).toNat = a.toNat)
    (hh2 : (hit &&& 2#32) ≠ 0#32 → (s.core.arena[cr + 3 + i]'(by omega)).toNat = b.toNat)
    (hh4 : (hit &&& 4#32) ≠ 0#32 → (s.core.arena[cr + 3 + i]'(by omega)).toNat = cl.toNat) :
    HtClauseInv s a b cl cr sz dist (nf + 1, mask ||| hit, i + 1) := by
  refine ⟨by omega, fun hd => ?_⟩
  obtain ⟨hnosat, hnf, ha, hb, hc⟩ := hinv.2 hd
  have htk := ht_lits_take_succ (s := s) (cr := cr) (i := i) (hsz ▸ hbd) (hsz ▸ hi)
  have hfilt : ((fullArenaClauseLits s cr).take (i + 1)).filter
      (fun l => s.core.vals[l]?.getD 0#8 == 0#8) =
      ((fullArenaClauseLits s cr).take i).filter
        (fun l => s.core.vals[l]?.getD 0#8 == 0#8) ++
      [(s.core.arena[cr + 3 + i]'(by omega)).toNat] := by
    rw [htk, List.filter_append]; simp [hv0]
  have hmem_of : ∀ (k : BitVec 32) (n : Nat)
      (hm : (mask &&& k) ≠ 0#32 → n ∈ ((fullArenaClauseLits s cr).take i).filter
        (fun l => s.core.vals[l]?.getD 0#8 == 0#8))
      (hh : (hit &&& k) ≠ 0#32 → (s.core.arena[cr + 3 + i]'(by omega)).toNat = n),
      ((mask ||| hit) &&& k) ≠ 0#32 → n ∈ ((fullArenaClauseLits s cr).take (i + 1)).filter
        (fun l => s.core.vals[l]?.getD 0#8 == 0#8) := fun k n hm hh hk => by
    rw [hfilt, List.mem_append, List.mem_singleton]
    rcases ht_or_and_ne_zero mask hit k hk with hmk | hhk
    · exact Or.inl (hm hmk)
    · exact Or.inr (hh hhk).symm
  refine ⟨fun k hk => ?_, ?_, hmem_of 1#32 a.toNat ha hh1, hmem_of 2#32 b.toNat hb hh2,
    hmem_of 4#32 cl.toNat hc hh4⟩
  · by_cases hki : k = i
    · subst hki
      have h_ak : s.core.arena[cr + 3 + k]?.getD 0#32 = s.core.arena[cr + 3 + k]'(by omega) := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [h_ak, hv0]; decide
    · exact hnosat k (by omega)
  · rw [hfilt, List.length_append, List.length_singleton, hnf]

private theorem ht_hit_flags (lit a b cl : BitVec 32) :
    let e1 : BitVec 32 := if lit = a then 1#32 else 0#32
    let e2 : BitVec 32 := if lit = b then e1 ||| 2#32 else e1
    let e3 : BitVec 32 := if lit = cl then e2 ||| 4#32 else e2
    ((e3 &&& 1#32) ≠ 0#32 → lit = a) ∧
    ((e3 &&& 2#32) ≠ 0#32 → lit = b) ∧
    ((e3 &&& 4#32) ≠ 0#32 → lit = cl) := by
  dsimp only
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    (by_cases h1 : lit = a <;> by_cases h2 : lit = b <;> by_cases h3 : lit = cl <;>
      simp_all <;> exact absurd h (by decide))

private theorem ht_clause_garb_false {s : FullState} {cr : Nat}
    (harr : cr < s.core.arena.length)
    (hc : (s.core.arena[cr]'harr &&& ((524288 : BitVec 32) ||| 4194304)) = 0#32) :
    fullArenaClauseGarb s cr = false := by
  have hor : ((524288 : BitVec 32) ||| 4194304) = 0x00480000#32 := by decide
  rw [hor] at hc
  unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
  rw [List.getElem?_eq_getElem harr, Option.getD_some]
  exact ht_garb_false_of_and_480000 hc

private theorem ht_clause_lit_lt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hcl : s.core.LengthsOk c)
    {cr sz i : Nat} (hcr : cr ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cr = false)
    (hsz : sz = fullArenaClauseSizeCore s.core cr) (hbd : cr + 3 + sz ≤ s.core.arena.length)
    (hi : i < sz) :
    (s.core.arena[cr + 3 + i]'(by omega)).toNat < 2 * s.core.cur_vars ∧
    (s.core.arena[cr + 3 + i]'(by omega)).toNat < s.core.vals.length := by
  have hm : (s.core.arena[cr + 3 + i]'(by omega)).toNat ∈ fullArenaClauseLits s cr :=
    (mem_fullArenaClauseLitsCore_iff (hsz ▸ hbd)).mpr ⟨i, hsz ▸ hi, rfl⟩
  have hlt := hw.arena.lits_lt cr hcr hng _ hm
  have hcv := hcl.cur_vars_le; have hvl := hcl.vals_len
  exact ⟨hlt, by omega⟩

private theorem ht_clause_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hnd : FullArenaVarsNodup s) (hcl0 : s.core.cur_level = 0)
    {cr : Nat} {a b cl : BitVec 32} (hcr : cr ∈ fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s cr = false)
    (_hsz_eq : fullArenaClauseSizeCore s.core cr = (s.core.arena[cr + 2]?.getD 0#32).toNat)
    {nf : Nat} {mask : BitVec 32}
    (hdist : (a ≠ b ∧ a ≠ cl ∧ b ≠ cl) →
      (∀ k < fullArenaClauseSizeCore s.core cr,
        s.core.vals[(s.core.arena[cr + 3 + k]?.getD 0#32).toNat]?.getD 0#8 ≠ 1#8) ∧
      nf = ((fullArenaClauseLits s cr).filter (fun l => s.core.vals[l]?.getD 0#8 == 0#8)).length ∧
      ((mask &&& 1#32) ≠ 0#32 → a.toNat ∈ (fullArenaClauseLits s cr).filter
        (fun l => s.core.vals[l]?.getD 0#8 == 0#8)) ∧
      ((mask &&& 2#32) ≠ 0#32 → b.toNat ∈ (fullArenaClauseLits s cr).filter
        (fun l => s.core.vals[l]?.getD 0#8 == 0#8)) ∧
      ((mask &&& 4#32) ≠ 0#32 → cl.toNat ∈ (fullArenaClauseLits s cr).filter
        (fun l => s.core.vals[l]?.getD 0#8 == 0#8)))
    (hnf : nf = 3) (hmask : mask = 7#32) :
    a ≠ b → a ≠ cl → b ≠ cl →
    (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat, cl.toNat]) := by
  intro hab hac hbc
  obtain ⟨hnosat, hcnt, ha, hb, hc⟩ := hdist ⟨hab, hac, hbc⟩
  have h1 : (7#32 : BitVec 32) &&& 1#32 ≠ 0#32 := by decide
  have h2 : (7#32 : BitVec 32) &&& 2#32 ≠ 0#32 := by decide
  have h4 : (7#32 : BitVec 32) &&& 4#32 ≠ 0#32 := by decide
  exact ht_ternary_of_unassigned_hits hlen hw hnd hcl0 hcr hng hnosat
    (hnf ▸ hcnt.symm) (ha (hmask ▸ h1)) (hb (hmask ▸ h2)) (hc (hmask ▸ h4)) hab hac hbc

theorem full_has_ternary_wp (Γ : Env) (_hΓ : Γ.Sat Spec.specs)
    (args : Tup Val [i64, i32, i32, i32]) (m0 : Mem 64) (Q : Post [.bool]) (X : XPost) :
    fullHasTernarySpec args m0 Q X → Func.wp Γ full_has_ternary_body args m0 Q X := by
  rcases args with ⟨h, a, b, cl, ⟨⟩⟩
  rintro ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, ha_lt, hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; have hac := c.harena
  unfold dimacsBound at hmx hwc hac; have hcl := hlen.core_ok
  have hcv_le := hcl.cur_vars_le; have hwvl := hcl.wvec_len
  have hwsl := hcl.wstk_len_arr; have hwle := hcl.wlen_le
  have harl := hcl.arena_len_arr; have hale := hcl.arena_len_le; have hvl := hcl.vals_len
  have h1_64 : (1 : BitVec 64).toNat = 1 := rfl
  have h2_64 : (2 : BitVec 64).toNat = 2 := rfl
  have ha_v : a.toNat < s.core.vals.length := by omega
  have ha_sh1 : (BitVec.setWidth 64 a <<< 1 + 1).toNat = 2 * a.toNat + 1 := bv64_shl1_add1_lit a
  have ha_w1 : (BitVec.setWidth 64 a <<< 1 + 1).toNat < s.core.wvec.length := by omega
  have h2cv_64 : (BitVec.ofNat 64 s.core.cur_vars <<< 1).toNat = 2 * s.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64), Nat.shiftLeft_eq, Nat.pow_one,
      Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]
  unfold Func.wp full_has_ternary_body
  c0_hstraight
  c0_hsplit
  · c0_hsteps
    exact hQ false (fun h => by cases h)
  · c0_hstraight
    let InvScan1 : BitVec 32 × BitVec 32 → Mem 64 → Prop := fun st m1 =>
      m1 = m0 ∧ st.1.toNat < 2 * s.core.cur_vars ∧
      st.2 = s.core.wvec[2 * st.1.toNat + 1]?.getD 0#32
    apply wp_join_state (fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ())) InvScan1
    · rintro _ ⟨scan1, min1⟩ m1 ⟨hm1, hsc1_lt, hmin1⟩
      subst m1
      dsimp only at hsc1_lt hmin1 ⊢
      c0_hstraight
      let InvScan : BitVec 32 × BitVec 32 → Mem 64 → Prop := fun st m2 =>
        m2 = m0 ∧ st.1.toNat < 2 * s.core.cur_vars ∧
        st.2 = s.core.wvec[2 * st.1.toNat + 1]?.getD 0#32
      apply wp_join_state (fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ())) InvScan
      · rintro _ ⟨scan, min_sz⟩ m2 ⟨hm2, hsc_lt, hmin_eq⟩
        subst m2
        dsimp only at hsc_lt hmin_eq ⊢
        c0_hstraight
        c0_hsplit
        · c0_hsteps; exact hQ false (fun h => by cases h)
        · c0_hstraight
          let InvDist : Bool → Mem 64 → Prop := fun dist md =>
            md = m0 ∧ (dist = true ↔ (a ≠ b ∧ a ≠ cl ∧ b ≠ cl))
          apply wp_join_state (fun d : Bool => (d, ())) InvDist
          · intro _ dist md ⟨hmd, hdist_iff⟩
            subst md
            c0_hstraight
            have hsc_bd := hw.watches.bounds scan.toNat hsc_lt
            have hsc_sh0 := bv64_shl1_lit scan; have hsc_sh1 := bv64_shl1_add1_lit scan
            have hsc_w0 : (BitVec.setWidth 64 scan <<< 1).toNat < s.core.wvec.length := by omega
            have hsc_w1 : (BitVec.setWidth 64 scan <<< 1 + 1).toNat < s.core.wvec.length := by
              omega
            let off_bv :=
              (s.core.wvec[(BitVec.setWidth 64 scan <<< 1).toNat]'hsc_w0).setWidth 64
            let wsz_bv := min_sz.setWidth 64
            have hoff_n : off_bv.toNat = fullWatchOffCore s.core scan.toNat := by
              dsimp only [off_bv]
              rw [BitVec.toNat_setWidth, list_getElem_congr hsc_w0 hsc_sh0]
              unfold fullWatchOffCore
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
                Nat.mod_eq_of_lt (by omega)]
            have hwsz_n : wsz_bv.toNat = fullWatchSizeCore s.core scan.toNat := by
              dsimp only [wsz_bv]; rw [BitVec.toNat_setWidth, hmin_eq]
              unfold fullWatchSizeCore; rw [Nat.mod_eq_of_lt (by omega)]
            have hend_n : (off_bv + wsz_bv).toNat = off_bv.toNat + wsz_bv.toNat := by
              rw [BitVec.toNat_add, hoff_n, hwsz_n, Nat.mod_eq_of_lt (by omega)]
            have hslice0 := modeWatchesInv_slice_mode hw.watches hsc_lt
            have h_idx0 : 2 * scan.toNat % 2 ^ 64 = 2 * scan.toNat := Nat.mod_eq_of_lt (by omega)
            have h_end_raw :
                (s.core.wvec[2 * scan.toNat % 2 ^ 64]'(by rw [h_idx0]; omega)).toNat +
                    min_sz.toNat = (off_bv + wsz_bv).toNat := by
              rw [list_getElem_congr _ h_idx0, hend_n, hoff_n, hwsz_n, hmin_eq]
              unfold fullWatchOffCore fullWatchSizeCore
              rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
              simp only [Option.getD_some]
            apply wp_join_state (fun p : BitVec 64 => (p, ())) (fun _ mb => mb = m0)
            · intro _ _ mb hmb
              subst mb
              c0_hsteps; exact hQ false (fun h => by cases h)
            · intro B hB
              let InvW : Nat → Mem 64 → Prop := fun p ml =>
                ml = m0 ∧ off_bv.toNat ≤ p ∧ p ≤ (off_bv + wsz_bv).toNat ∧
                (if s.core.dense_mode = 0#64 then
                   WatchSliceOk F_cur s.core scan.toNat p ((off_bv + wsz_bv).toNat - p)
                 else DenseWatchSliceOk F_cur s.core scan.toNat p ((off_bv + wsz_bv).toNat - p))
              apply wp_while_state (fun p => (BitVec.ofNat 64 p, ()))
                (fun p => (off_bv + wsz_bv).toNat - p) InvW
              · intro L hL
                c0_hsteps
                have hof_eq : off_bv = BitVec.ofNat 64 off_bv.toNat :=
                  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
                exact (congrArg (fun x => L (x, ()) m0) hof_eq).mpr
                  (hL off_bv.toNat m0 ⟨rfl, Nat.le_refl _, by omega,
                    by simpa [hend_n, hoff_n, hwsz_n] using hslice0⟩)
              · intro L p ml ⟨hml, hp_ge, hp_le, hslice⟩ ih
                subst ml
                dsimp only at hp_ge hp_le hslice ⊢
                have hp_bv : (BitVec.ofNat 64 p).toNat = p := Nat.mod_eq_of_lt (by omega)
                c0_hsplit
                · have hp_lt : p < (off_bv + wsz_bv).toNat := by
                    rw [Nat.mod_eq_of_lt (show p < 2 ^ 64 by omega), h_end_raw,
                      Nat.mod_eq_of_lt (show (off_bv + wsz_bv).toNat < 2 ^ 64 by omega)] at hc
                    exact hc
                  have hp_w : p < s.core.wstk.length := by omega
                  obtain ⟨w0, hw0_get, hcase⟩ := ht_slice_pop_step hslice (by omega)
                  have hw0_eq : s.core.wstk[p]'hp_w = w0 := by
                    rw [List.getElem?_eq_getElem hp_w] at hw0_get; exact Option.some.inj hw0_get
                  c0_hstraight
                  c0_hsplit
                  · rcases hcase with ⟨_, hrest⟩ | ⟨hf0, _⟩
                    · c0_hsteps; rw [bv64_ofNat_add1 (by omega)]
                      exact ih (p + 1) m0 (by omega)
                        ⟨rfl, by omega, by omega, by simpa [Nat.sub_sub] using hrest⟩
                    · exfalso
                      simp only [Nat.mod_eq_of_lt (show p < 2 ^ 64 by omega)] at hc
                      rw [hw0_eq] at hc; exact hc hf0
                  · rcases hcase with ⟨hf1, _⟩ | ⟨_, hrem2, cr, hcr_get, hcr_ref, hrest2⟩
                    · exfalso
                      simp only [Nat.mod_eq_of_lt (show p < 2 ^ 64 by omega)] at hc
                      rw [hw0_eq] at hc; exact hf1 hc
                    · have hp1_w : p + 1 < s.core.wstk.length := by omega
                      have hcr_eq : s.core.wstk[p + 1]'hp1_w = cr := by
                        rw [List.getElem?_eq_getElem hp1_w] at hcr_get
                        exact Option.some.inj hcr_get
                      have hcr_wf := hw.arena.refs_wf cr.toNat hcr_ref
                      have hcr_arr : cr.toNat < s.core.arena.length := by omega
                      have hp2_bv : BitVec.ofNat 64 p + 1 + 1 = BitVec.ofNat 64 (p + 2) := by
                        rw [bv64_ofNat_add1 (by omega), bv64_ofNat_add1 (by omega)]
                      c0_hsplit
                      · exfalso
                        rw [h1_64, Nat.mod_eq_of_lt (show p + 1 < 2 ^ 64 by omega), h_end_raw,
                          Nat.mod_eq_of_lt (show (off_bv + wsz_bv).toNat < 2 ^ 64 by omega)] at hc
                        omega
                      · have hp1_n : (BitVec.ofNat 64 p + 1).toNat = p + 1 := by
                          rw [bv64_ofNat_add1 (by omega), BitVec.toNat_ofNat,
                            Nat.mod_eq_of_lt (by omega)]
                        have hcr_64 : (cr.setWidth 64).toNat = cr.toNat := by
                          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                        have hstk_cr : s.core.wstk[(BitVec.ofNat 64 p + 1).toNat]'(by
                            rw [hp1_n]; exact hp1_w) = cr := by
                          rw [list_getElem_congr _ hp1_n, hcr_eq]
                        have hcr0_w : (BitVec.setWidth 64 (s.core.wstk[(BitVec.ofNat 64 p +
                            1).toNat]'(by rw [hp1_n]; exact hp1_w))).toNat <
                            s.core.arena.length := by
                          rw [hstk_cr, hcr_64]; exact hcr_arr
                        have hcr2_w : (BitVec.setWidth 64 (s.core.wstk[(BitVec.ofNat 64 p +
                            1).toNat]'(by rw [hp1_n]; exact hp1_w)) + 2).toNat <
                            s.core.arena.length := by
                          rw [hstk_cr, BitVec.toNat_add, hcr_64, h2_64,
                            Nat.mod_eq_of_lt (by omega)]
                          omega
                        have hp1_mod : (p + (1 : BitVec 64).toNat) % 2 ^ 64 = p + 1 := by
                          rw [h1_64, Nat.mod_eq_of_lt (by omega)]
                        have hstk_cr_mod :
                            s.core.wstk[(p + (1 : BitVec 64).toNat) % 2 ^ 64]'(by
                              rw [hp1_mod]; exact hp1_w) = cr := by
                          rw [list_getElem_congr _ hp1_mod, hcr_eq]
                        c0_hsplit
                        · c0_hsteps; rw [hp2_bv]
                          exact ih (p + 2) m0 (by omega)
                            ⟨rfl, by omega, by omega, by simpa [Nat.sub_sub] using hrest2⟩
                        · have hng : fullArenaClauseGarb s cr.toNat = false := by
                            have hhdr_eq := list_getElem_congr (by rw [hstk_cr_mod]; exact hcr_arr)
                              (congrArg BitVec.toNat hstk_cr_mod)
                            rw [hhdr_eq] at hc
                            exact ht_clause_garb_false hcr_arr hc
                          clear hc; c0_hsplit
                          · c0_hsteps; rw [hp2_bv]
                            exact ih (p + 2) m0 (by omega)
                              ⟨rfl, by omega, by omega, by simpa [Nat.sub_sub] using hrest2⟩
                          · let sz_n := fullArenaClauseSizeCore s.core cr.toNat
                            have hsz_cv : sz_n ≤ s.core.cur_vars :=
                              ht_fullArenaClauseSize_le_cur_vars hlen hw hnd hcr_ref hng
                            clear hc; c0_hstraight
                            let InvExit : Nat × BitVec 32 × Nat → Mem 64 → Prop := fun st me =>
                              me = m0 ∧ st.1 ≤ 4 ∧ (st.2.1 = 7#32 →
                                HtClauseInv s a b cl cr.toNat sz_n dist (st.1, st.2.1, sz_n))
                            apply wp_join_state (fun st : Nat × BitVec 32 × Nat =>
                                (BitVec.ofNat 32 st.1, st.2.1,
                                 BitVec.ofNat 64 (cr.toNat + 3 + st.2.2), ())) InvExit
                            · rintro _ ⟨nf_e, mask_e, i_e⟩ me ⟨hme, hnf_e, hinv_e⟩
                              subst me; dsimp only at hnf_e hinv_e ⊢
                              c0_hsplit
                              · have hnf_3 : nf_e = 3 := by
                                  have hto := congrArg BitVec.toNat hc
                                  simpa [BitVec.toNat_ofNat,
                                    Nat.mod_eq_of_lt (show nf_e < 2 ^ 32 by omega)] using hto
                                clear hc; c0_hsplit
                                · c0_hsteps
                                  have hmask_7 : mask_e = 7#32 := hc
                                  have hlen_lits :
                                      (fullArenaClauseLits s cr.toNat).length = sz_n := by
                                    unfold fullArenaClauseLits fullArenaClauseLitsCore
                                    simp only [List.length_map, List.length_take, List.length_drop]
                                    omega
                                  refine hQ true fun _ hab hac hbc => ht_clause_post hlen hw hnd
                                    hcl0 hcr_ref hng rfl (fun _ => ?_) hnf_3 hmask_7 hab hac hbc
                                  have hht := (hinv_e hmask_7).2 (hdist_iff.mpr ⟨hab, hac, hbc⟩)
                                  rwa [List.take_of_length_le (Nat.le_of_eq hlen_lits)] at hht
                                · c0_hsteps; rw [hp2_bv]
                                  exact ih (p + 2) m0 (by omega)
                                    ⟨rfl, by omega, by omega, by simpa [Nat.sub_sub] using hrest2⟩
                              · c0_hsteps; rw [hp2_bv]
                                exact ih (p + 2) m0 (by omega)
                                  ⟨rfl, by omega, by omega, by simpa [Nat.sub_sub] using hrest2⟩
                            · intro Js hJs
                              let InvC : Nat × BitVec 32 × Nat → Mem 64 → Prop := fun st mi =>
                                mi = m0 ∧ st.1 ≤ 3 ∧ HtClauseInv s a b cl cr.toNat sz_n dist st
                              apply wp_while_state (fun st : Nat × BitVec 32 × Nat =>
                                  (BitVec.ofNat 32 st.1, st.2.1,
                                   BitVec.ofNat 64 (cr.toNat + 3 + st.2.2), ()))
                                (fun st => sz_n - st.2.2) InvC
                              · intro Ji hJi; c0_hsteps
                                have hinit_idx : BitVec.setWidth 64 (s.core.wstk[(BitVec.ofNat 64
                                      p + 1).toNat]'(by rw [hp1_n]; exact hp1_w)) + 3 =
                                    BitVec.ofNat 64 (cr.toNat + 3 + 0) := by
                                  have h3_64 : (3 : BitVec 64).toNat = 3 := rfl
                                  rw [hstk_cr]; exact BitVec.eq_of_toNat_eq (by
                                    rw [BitVec.toNat_add, hcr_64, h3_64, BitVec.toNat_ofNat,
                                      Nat.mod_eq_of_lt (by omega)])
                                rw [hinit_idx]
                                exact hJi (0, 0#32, 0) m0 ⟨rfl, Nat.zero_le _, Nat.zero_le _,
                                  fun _ => ⟨fun k hk => by omega, rfl,
                                    fun h => absurd h (by decide),
                                    fun h => absurd h (by decide),
                                    fun h => absurd h (by decide)⟩⟩
                              · rintro Ji ⟨nf_i, mask_i, i_v⟩ mi ⟨hmi, hnf_le, hi_inv⟩ ih_i
                                subst mi; dsimp only at hnf_le hi_inv ⊢
                                have hi_le : i_v ≤ sz_n := hi_inv.1
                                have hi_lt64 : cr.toNat + 3 + i_v < 2 ^ 64 := by omega
                                have hidx_bv : (BitVec.ofNat 64 (cr.toNat + 3 + i_v)).toNat =
                                    cr.toNat + 3 + i_v := Nat.mod_eq_of_lt hi_lt64
                                have h3_64 : (3 : BitVec 64).toNat = 3 := rfl
                                have hcr2_mod_idx : ((s.core.wstk[(p + (1 : BitVec 64).toNat) %
                                      2 ^ 64]'(by rw [hp1_mod]; exact hp1_w)).toNat +
                                      (2 : BitVec 64).toNat) % 2 ^ 64 = cr.toNat + 2 := by
                                  rw [hstk_cr_mod, h2_64, Nat.mod_eq_of_lt (by omega)]
                                have h_end_mod :
                                    ((s.core.wstk[(p + (1 : BitVec 64).toNat) % 2 ^ 64]'(by
                                      rw [hp1_mod]; exact hp1_w)).toNat + (3 : BitVec 64).toNat +
                                      (s.core.arena[((s.core.wstk[(p + (1 : BitVec 64).toNat) %
                                        2 ^ 64]'(by rw [hp1_mod]; exact hp1_w)).toNat +
                                        (2 : BitVec 64).toNat) % 2 ^ 64]'(by
                                        rw [hcr2_mod_idx]; omega)).toNat) % 2 ^ 64 =
                                      cr.toNat + 3 + sz_n := by
                                  have h_sz_get : s.core.arena[((s.core.wstk[(p +
                                      (1 : BitVec 64).toNat) % 2 ^ 64]'(by
                                      rw [hp1_mod]; exact hp1_w)).toNat +
                                      (2 : BitVec 64).toNat) % 2 ^ 64]'(by
                                      rw [hcr2_mod_idx]; omega) =
                                      s.core.arena[cr.toNat + 2]'(by omega) :=
                                    list_getElem_congr _ hcr2_mod_idx
                                  rw [h_sz_get, congrArg BitVec.toNat hstk_cr_mod, h3_64]
                                  unfold sz_n fullArenaClauseSizeCore
                                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
                                    Nat.mod_eq_of_lt (by omega)]
                                c0_hsplit
                                · have hi_lt : i_v < sz_n := by
                                    rw [Nat.mod_eq_of_lt hi_lt64, h_end_mod] at hc; omega
                                  have hi_arr : (BitVec.ofNat 64 (cr.toNat + 3 + i_v)).toNat <
                                      s.core.arena.length := by rw [hidx_bv]; omega
                                  let lit := s.core.arena[cr.toNat + 3 + i_v]'(by omega)
                                  have hl_get := list_getElem_congr hi_arr hidx_bv
                                  obtain ⟨_, hl_v0⟩ :=
                                    ht_clause_lit_lt hw hcl hcr_ref hng rfl (by omega) hi_lt
                                  have hl_bv_n : (BitVec.setWidth 64 (s.core.arena[(BitVec.ofNat 64
                                      (cr.toNat + 3 + i_v)).toNat]'hi_arr)).toNat = lit.toNat := by
                                    rw [hl_get, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                                  have hl_v : (BitVec.setWidth 64 (s.core.arena[(BitVec.ofNat 64
                                      (cr.toNat + 3 + i_v)).toNat]'hi_arr)).toNat <
                                      s.core.vals.length := hl_bv_n ▸ hl_v0
                                  have hstep_idx : BitVec.ofNat 64 (cr.toNat + 3 + i_v) + 1 =
                                      BitVec.ofNat 64 (cr.toNat + 3 + (i_v + 1)) := by
                                    simpa [Nat.add_assoc] using
                                      bv64_ofNat_add1 (by omega : cr.toNat + 3 + i_v + 1 < 2 ^ 64)
                                  let v_val := s.core.vals[lit.toNat]'hl_v0
                                  have hm_idx := Nat.mod_eq_of_lt hi_lt64
                                  have hl_mod_eq : ∀ prf,
                                      s.core.arena[(cr.toNat + 3 + i_v) % 2 ^ 64]'prf = lit :=
                                    fun _ => list_getElem_congr _ hm_idx
                                  have hval_mod_eq : ∀ prf1 prf2,
                                      s.core.vals[(s.core.arena[(cr.toNat + 3 + i_v) %
                                        2 ^ 64]'prf1).toNat]'prf2 = v_val := fun _ _ =>
                                    list_getElem_congr _ (congrArg BitVec.toNat (hl_mod_eq _))
                                  have hv_get' : s.core.vals[lit.toNat]?.getD 0#8 = v_val := by
                                    rw [List.getElem?_eq_getElem hl_v0, Option.getD_some]
                                  have h1_32 : (1 : BitVec 32).toNat = 1 := rfl
                                  have hnf1_32 : nf_i + 1 < 2 ^ 32 := by omega
                                  have hnf_add : BitVec.ofNat 32 nf_i + 1 =
                                      BitVec.ofNat 32 (nf_i + 1) := BitVec.eq_of_toNat_eq (by
                                    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h1_32,
                                      Nat.mod_eq_of_lt (show nf_i < 2 ^ 32 by omega),
                                      Nat.mod_eq_of_lt hnf1_32])
                                  c0_hsplit
                                  · c0_hsteps; rw [hstep_idx]
                                    exact hJs (nf_i, 8#32, i_v + 1) m0
                                      ⟨rfl, by omega, fun h => by cases h⟩
                                  · have hv_ne1 : v_val ≠ 1#8 := by
                                      intro h1; rw [hval_mod_eq, h1] at hc
                                      exact absurd hc (by decide)
                                    clear hc; c0_hstraight
                                    let InvNext : Nat × BitVec 32 → Mem 64 → Prop := fun st mn =>
                                      mn = m0 ∧ st.1 ≤ 3 ∧
                                      HtClauseInv s a b cl cr.toNat sz_n dist (st.1, st.2, i_v + 1)
                                    apply wp_join_state (fun st : Nat × BitVec 32 =>
                                        (BitVec.ofNat 32 st.1, st.2, ())) InvNext
                                    · rintro _ ⟨nf_n, mask_n⟩ mn ⟨hmn, hnf_n, hinv_n⟩
                                      subst mn; c0_hsteps; rw [hstep_idx]
                                      exact ih_i (nf_n, mask_n, i_v + 1) m0 (by dsimp only; omega)
                                        ⟨rfl, hnf_n, hinv_n⟩
                                    · intro Js1 hJs1
                                      c0_hsplit
                                      · have hv_eq0 : v_val = 0#8 := by
                                          rw [hval_mod_eq] at hc; exact ht_sext8_eq_zero hc
                                        clear hc; c0_hsplit
                                        · c0_hsteps; rw [hstep_idx, hnf_add]
                                          exact hJs (nf_i + 1, 8#32, i_v + 1) m0
                                            ⟨rfl, by omega, fun h => by cases h⟩
                                        · have hnf1_le : nf_i + 1 ≤ 3 := by
                                            have h3_32 : (3 : BitVec 32).toNat = 3 := rfl
                                            rw [h3_32, h1_32, Nat.mod_eq_of_lt hnf1_32] at hc; omega
                                          clear hc; c0_hstraight
                                          let exp1 : BitVec 32 := if lit = a then 1#32 else 0#32
                                          let exp2 : BitVec 32 :=
                                            if lit = b then exp1 ||| 2#32 else exp1
                                          let exp3 : BitVec 32 :=
                                            if lit = cl then exp2 ||| 4#32 else exp2
                                          apply wp_join_state (fun hit : BitVec 32 => (hit, ()))
                                            (fun hit mh => mh = m0 ∧ hit = exp1)
                                          · rintro _ hit1 mh ⟨hmh, rfl⟩; subst mh; c0_hstraight
                                            apply wp_join_state (fun hit : BitVec 32 => (hit, ()))
                                              (fun hit mh => mh = m0 ∧ hit = exp2)
                                            · rintro _ hit2 mh2 ⟨hmh2, rfl⟩; subst mh2; c0_hstraight
                                              apply wp_join_state
                                                (fun hit : BitVec 32 => (hit, ()))
                                                (fun hit mh => mh = m0 ∧ hit = exp3)
                                              · rintro _ hit3 mh3 ⟨hmh3, rfl⟩; subst mh3
                                                c0_hstraight
                                                apply wp_join0 (fun m5 =>
                                                  m5 = m0 ∧ (dist = true → exp3 ≠ 0#32))
                                                · intro _ m5 ⟨hm5, _⟩; subst m5; c0_hsteps
                                                  rw [hnf_add]
                                                  have hfl := ht_hit_flags lit a b cl
                                                  exact hJs1 (nf_i + 1, mask_i ||| exp3) m0
                                                    ⟨rfl, hnf1_le,
                                                      ht_clause_step_unassigned rfl (by omega) hi_lt
                                                        hi_inv (hv_get'.trans hv_eq0)
                                                        (fun h => congrArg BitVec.toNat (hfl.1 h))
                                                        (fun h => congrArg BitVec.toNat (hfl.2.1 h))
                                                        (fun h =>
                                                          congrArg BitVec.toNat (hfl.2.2 h))⟩
                                                · intro J5 hJ5; c0_hsplit
                                                  · c0_hsplit
                                                    · c0_hsteps; rw [hstep_idx, hnf_add]
                                                      exact hJs (nf_i + 1, 8#32, i_v + 1) m0
                                                        ⟨rfl, by omega, fun h => by cases h⟩
                                                    · c0_hsteps; exact hJ5 m0
                                                        ⟨rfl, fun h => by rw [h] at hc; cases hc⟩
                                                  · c0_hsteps; exact hJ5 m0 ⟨rfl, fun _ => hc⟩
                                              · intro J4 hJ4; c0_hsplit <;>
                                                  (have hc' := hl_mod_eq _ ▸ hc; c0_hsteps;
                                                    exact hJ4 _ m0 ⟨rfl, by simp [exp3, hc']⟩)
                                            · intro J3 hJ3; c0_hsplit <;>
                                                (have hc' := hl_mod_eq _ ▸ hc; c0_hsteps;
                                                  exact hJ3 _ m0 ⟨rfl, by simp [exp2, hc']⟩)
                                          · intro J2 hJ2; c0_hsplit <;>
                                              (have hc' := hl_mod_eq _ ▸ hc; c0_hsteps;
                                                exact hJ2 _ m0 ⟨rfl, by simp [exp1, hc']⟩)
                                      · have hv_ne0 : v_val ≠ 0#8 := by
                                          intro h0; apply hc; rw [hval_mod_eq, h0]; rfl
                                        c0_hsteps
                                        exact hJs1 (nf_i, mask_i) m0
                                          ⟨rfl, hnf_le, ht_clause_step_skip rfl (by omega) hi_lt
                                            hi_inv hv_get'.symm hv_ne1 hv_ne0⟩
                                · have hi_eq : i_v = sz_n := by
                                    rw [Nat.mod_eq_of_lt hi_lt64, h_end_mod] at hc; omega
                                  c0_hsteps
                                  exact hJs (nf_i, mask_i, i_v) m0
                                    ⟨rfl, by omega, fun _ => hi_eq ▸ hi_inv⟩
                · c0_hsteps; exact hB (BitVec.ofNat 64 p) m0 rfl
          · intro Jd hJd
            c0_hsplit
            · c0_hsplit
              · c0_hsplit <;> c0_hsteps <;> exact hJd _ m0 ⟨rfl, by simp_all⟩
              · c0_hsteps; exact hJd false m0 ⟨rfl, by simp_all⟩
            · c0_hsteps; exact hJd false m0 ⟨rfl, by simp_all⟩
      · intro Jc hJc; c0_hsplit
        · have hcl_lt : cl.toNat < 2 * s.core.cur_vars := by
            simp only [Nat.mod_eq_of_lt (show s.core.cur_vars < 2 ^ 64 by omega),
              Nat.mod_eq_of_lt (show 2 * s.core.cur_vars < 2 ^ 64 by omega)] at hc; exact hc
          have hcl_v : cl.toNat < s.core.vals.length := by omega
          c0_hsplit
          · c0_hsteps; exact hQ false (fun h => by cases h)
          · c0_hstraight
            apply wp_join_state (fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ()))
              (fun st m1 => m1 = m0 ∧ st.1.toNat < 2 * s.core.cur_vars ∧
                st.2 = s.core.wvec[2 * st.1.toNat + 1]?.getD 0#32)
            · intro _ ⟨sc', mn'⟩ m1 hm1; c0_hsteps; exact hJc (sc', mn') m1 hm1
            · intro Jc' hJc'
              have hcl_sh1 := bv64_shl1_add1_lit cl
              have hcl_w1 : (BitVec.setWidth 64 cl <<< 1 + 1).toNat < s.core.wvec.length := by
                omega
              c0_hsplit
              · c0_hsteps; rw [ht_wvec_get hcl (by omega) cl hcl_lt hcl_w1]
                exact hJc' (cl, s.core.wvec[2 * cl.toNat + 1]?.getD 0#32) m0 ⟨rfl, hcl_lt, rfl⟩
              · c0_hsteps; exact hJc' (scan1, min1) m0 ⟨rfl, hsc1_lt, hmin1⟩
        · c0_hsteps; exact hJc (scan1, min1) m0 ⟨rfl, hsc1_lt, hmin1⟩
    · intro Jb hJb; c0_hsplit
      · have hb_lt : b.toNat < 2 * s.core.cur_vars := by
          simp only [Nat.mod_eq_of_lt (show s.core.cur_vars < 2 ^ 64 by omega),
            Nat.mod_eq_of_lt (show 2 * s.core.cur_vars < 2 ^ 64 by omega)] at hc; exact hc
        have hb_v : b.toNat < s.core.vals.length := by omega
        c0_hsplit
        · c0_hsteps; exact hQ false (fun h => by cases h)
        · c0_hstraight
          apply wp_join_state (fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ()))
            (fun st m1 => m1 = m0 ∧ st.1.toNat < 2 * s.core.cur_vars ∧
              st.2 = s.core.wvec[2 * st.1.toNat + 1]?.getD 0#32)
          · intro _ ⟨sc', mn'⟩ m1 hm1; c0_hsteps; exact hJb (sc', mn') m1 hm1
          · intro Jb' hJb'
            have hb_sh1 := bv64_shl1_add1_lit b
            have hb_w1 : (BitVec.setWidth 64 b <<< 1 + 1).toNat < s.core.wvec.length := by omega
            c0_hsplit
            · c0_hsteps; rw [ht_wvec_get hcl (by omega) b hb_lt hb_w1]
              exact hJb' (b, s.core.wvec[2 * b.toNat + 1]?.getD 0#32) m0 ⟨rfl, hb_lt, rfl⟩
            · c0_hsteps; rw [ht_wvec_get hcl (by omega) a ha_lt ha_w1]
              exact hJb' (a, s.core.wvec[2 * a.toNat + 1]?.getD 0#32) m0 ⟨rfl, ha_lt, rfl⟩
      · c0_hsteps; rw [ht_wvec_get hcl (by omega) a ha_lt ha_w1]
        exact hJb (a, s.core.wvec[2 * a.toNat + 1]?.getD 0#32) m0 ⟨rfl, ha_lt, rfl⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Watch
