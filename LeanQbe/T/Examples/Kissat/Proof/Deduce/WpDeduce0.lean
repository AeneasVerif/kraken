/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Base
public import LeanQbe.T.Examples.Kissat.Proof.Deduce.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpCommon
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts2
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics

/-!
# Kissat 1-UIP Conflict Analysis & OTFS Resolvent Theory (`Proof.Deduce.WpDeduce0`)

Pure semantic invariants and transitions for `full_deduce_1uip_m6_hdr` (`public section`,
`0` legacy imports, `0` `import all`, `0` `@[expose]` on theorems/lemmas/sections).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Deduce

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-! ## 1. Pure List, BitVec & CNF Resolution Helpers -/

theorem ded_bv32_xor1_toNat (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 :=
  bv32_xor_1 x

theorem ded_lit_xor1_div2 (l : Nat) : (l ^^^ 1) / 2 = l / 2 := by
  simpa [litVar, litNeg] using litVar_litNeg l

theorem ded_lit_xor1_xor1 (l : Nat) : (l ^^^ 1) ^^^ 1 = l := by
  simpa [litNeg] using litNeg_litNeg l

theorem ded_lit_eq_of_div2_eq_falsified {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullOtfsWitnessInv c F0 F_cur k) {a b : Nat}
    (ha : a < 2 * k.cur_vars) (hb : b < 2 * k.cur_vars)
    (hfa : k.vals[a]?.getD 0#8 = 0xFF#8) (hfb : k.vals[b]?.getD 0#8 = 0xFF#8)
    (hdiv : a / 2 = b / 2) : a = b := by
  obtain ⟨ia, hia, haeq⟩ := (hw.vals_false_iff a ha).mp hfa
  obtain ⟨ib, hib, hbeq⟩ := (hw.vals_false_iff b hb).mp hfb
  have hi := hw.trail_vars_nodup ia ib hia hib (by
    rw [haeq, hbeq, ded_lit_xor1_div2, ded_lit_xor1_div2, hdiv])
  subst hi
  have hxor : a ^^^ 1 = b ^^^ 1 := by rw [← haeq, hbeq]
  have h1 := congrArg (· ^^^ 1) hxor
  simpa only [ded_lit_xor1_xor1] using h1

theorem ded_clause_entails_of_subset {f : CNF Nat} {c1 c2 : List Nat}
    (h : f.EntailsClause (cnfClause c1)) (hsub : ∀ l ∈ c1, l ∈ c2) :
    f.EntailsClause (cnfClause c2) :=
  entails_of_mem_or_false h fun l hl => Or.inl (hsub l hl)

theorem ded_clause_entails_strip {f : CNF Nat} {c1 c2 : List Nat}
    (h : f.EntailsClause (cnfClause c1))
    (hstep : ∀ l ∈ c1, l ∈ c2 ∨ f.EntailsClause (cnfClause [l ^^^ 1])) :
    f.EntailsClause (cnfClause c2) := by
  refine entails_of_mem_or_false h fun l hl => ?_
  rcases hstep l hl with hm | hu
  · exact Or.inl hm
  · exact Or.inr (by rw [show Ref.litNeg l = l ^^^ 1 from rfl]; exact hu)

theorem ded_clause_entails_resolve_step {f : CNF Nat} {p : Nat} {c1 r c2 : List Nat}
    (h1 : f.EntailsClause (cnfClause c1)) (hr : f.EntailsClause (cnfClause r))
    (hc1 : ∀ l ∈ c1, l = p ^^^ 1 ∨ l ∈ c2 ∨ f.EntailsClause (cnfClause [l ^^^ 1]))
    (hr1 : ∀ q ∈ r, q = p ∨ q ∈ c2 ∨ f.EntailsClause (cnfClause [q ^^^ 1])) :
    f.EntailsClause (cnfClause c2) := by
  refine entails_resolve_to (p := p) hr h1 (fun q hq => ?_) (fun l hl => ?_)
  · rcases hr1 q hq with rfl | hm | hu
    · exact Or.inl rfl
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr (by rw [show Ref.litNeg q = q ^^^ 1 from rfl]; exact hu))
  · rcases hc1 l hl with hp | hm | hu
    · exact Or.inl (by rw [show Ref.litNeg p = p ^^^ 1 from rfl]; exact hp)
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr (by rw [show Ref.litNeg l = l ^^^ 1 from rfl]; exact hu))

private theorem ded_filter_length_disjoint_add {α : Type} (p1 p2 : α → Bool) :
    ∀ xs : List α, (∀ x ∈ xs, ¬ (p1 x = true ∧ p2 x = true)) →
      (xs.filter fun x => p1 x || p2 x).length =
        (xs.filter p1).length + (xs.filter p2).length
  | [], _ => rfl
  | x :: xs, hdisj => by
    have hx := hdisj x List.mem_cons_self
    have ih := ded_filter_length_disjoint_add p1 p2 xs
      fun y hy => hdisj y (List.mem_cons_of_mem _ hy)
    cases h1 : p1 x <;> cases h2 : p2 x <;> simp_all <;> omega

theorem ded_nodup_map_on {α β : Type} {f : α → β} {xs : List α}
    (hinj : ∀ x1 ∈ xs, ∀ x2 ∈ xs, f x1 = f x2 → x1 = x2) (hx : xs.Nodup) :
    (xs.map f).Nodup :=
  List.pairwise_map.mpr
    (hx.imp_of_mem fun {x1 x2} h1 h2 hne heq => hne (hinj x1 h1 x2 h2 heq))

theorem ded_nodup_length_eq_of_map_bij {α β : Type} (f : α → β)
    {xs : List α} {ys : List β} (hx : xs.Nodup) (hy : ys.Nodup)
    (hmem : ∀ x ∈ xs, f x ∈ ys)
    (hinj : ∀ x1 ∈ xs, ∀ x2 ∈ xs, f x1 = f x2 → x1 = x2)
    (hsurj : ∀ y ∈ ys, ∃ x ∈ xs, f x = y) : xs.length = ys.length := by
  have hmap_nd : (xs.map f).Nodup := ded_nodup_map_on hinj hx
  have hle1 : (xs.map f).length ≤ ys.length :=
    List.Nodup.length_le_of_subset hmap_nd (fun y hy' => by
      obtain ⟨x, hx', rfl⟩ := List.mem_map.mp hy'; exact hmem x hx')
  have hle2 : ys.length ≤ (xs.map f).length :=
    List.Nodup.length_le_of_subset hy (fun y hy' => by
      obtain ⟨x, hx', rfl⟩ := hsurj y hy'; exact List.mem_map_of_mem hx')
  rw [List.length_map] at hle1 hle2; omega

/-! ## 2. 1-UIP State Invariants & Static Field Pack -/

/-- Lower-level literals accumulated in `tmp[1 ..< tl)`. -/
@[expose] def fullLowerLits (tmp : List (BitVec 32)) (tl : Nat) : List Nat :=
  ((tmp.take tl).drop 1).map BitVec.toNat

/-- Trail indices in `[0 ..< idx)` that are marked in `mrk` and at `k.cur_level`. -/
@[expose] def fullCurTrailIdxs (k : FullCoreState) (mrk : List (BitVec 8)) (idx : Nat) :
    List Nat :=
  (List.range idx).filter fun j =>
    decide (mrk[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
      (k.lvl[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = k.cur_level)

/-- Negated current-level trail literals remaining to be resolved. -/
@[expose] def fullCurLits (k : FullCoreState) (mrk : List (BitVec 8)) (idx : Nat) : List Nat :=
  (fullCurTrailIdxs k mrk idx).map fun j => (k.trl[j]?.getD 0#32).toNat ^^^ 1

/-- Current active resolvent during 1-UIP loop: remaining cur-level literals plus lower-level
literals stored in `tmp[1 ..< tl)`. -/
@[expose] def fullActiveResolvent (k : FullCoreState) (tmp : List (BitVec 32))
    (mrk : List (BitVec 8)) (tl idx : Nat) : List Nat :=
  fullCurLits k mrk idx ++ fullLowerLits tmp tl

/-- Invariant on the lower-level literals stored in `tmp[1 ..< tl)`. -/
@[expose] def FullLowerInv (_c : FullCfg) (k : FullCoreState) (tmp : List (BitVec 32))
    (mrk : List (BitVec 8)) (tl : Nat) : Prop :=
  (∀ j, 1 ≤ j → j < tl →
    let l := (tmp[j]?.getD 0#32).toNat
    l < 2 * k.cur_vars ∧ k.vals[l]?.getD 0#8 = 0xFF#8 ∧
      0 < (k.lvl[l / 2]?.getD 0#32).toNat ∧
      (k.lvl[l / 2]?.getD 0#32).toNat < k.cur_level ∧ mrk[l / 2]?.getD 0#8 ≠ 0#8) ∧
  (∀ j1 j2, 1 ≤ j1 → j1 < j2 → j2 < tl →
    (tmp[j1]?.getD 0#32).toNat / 2 ≠ (tmp[j2]?.getD 0#32).toNat / 2)

/-- Every marked variable `< cur_vars` has `0 < lvl ≤ cur_level`, and if `< cur_level` appears in
`tmp[1 ..< tl)`. -/
@[expose] def FullMarksCov (k : FullCoreState) (tmp : List (BitVec 32))
    (mrk : List (BitVec 8)) (tl : Nat) : Prop :=
  ∀ v < k.cur_vars, mrk[v]?.getD 0#8 ≠ 0#8 →
    0 < (k.lvl[v]?.getD 0#32).toNat ∧ (k.lvl[v]?.getD 0#32).toNat ≤ k.cur_level ∧
      ((k.lvl[v]?.getD 0#32).toNat < k.cur_level →
        ∃ j, 1 ≤ j ∧ j < tl ∧ (tmp[j]?.getD 0#32).toNat / 2 = v)

/-- Every marked cur-level trail position lies strictly below `lim`. -/
@[expose] def FullCurMarksBelow (te : Nat) (k : FullCoreState) (mrk : List (BitVec 8))
    (lim : Nat) : Prop :=
  ∀ j < te, mrk[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 →
    (k.lvl[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = k.cur_level → j < lim

/-- Fields unchanged throughout 1-UIP deduction (`cur_vars`, `cur_level`, trail, levels, reasons,
values, `fuel`, `dense_mode`, `lit_mark`). -/
structure FullDeduceStaticEq (k0 k : FullCoreState) : Prop where
  cv : k.cur_vars = k0.cur_vars
  cl : k.cur_level = k0.cur_level
  te : k.trail_end = k0.trail_end
  trl : k.trl = k0.trl
  lvl : k.lvl = k0.lvl
  rsns : k.rsns = k0.rsns
  vals : k.vals = k0.vals
  fuel : k.fuel = k0.fuel
  dm : k.dense_mode = k0.dense_mode
  lm : k.lit_mark = k0.lit_mark

/-- Loop invariant for 1-UIP conflict analysis (with optional OTFS cut-shrink at `cut`). -/
structure FullDeduceStateInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cut idx : Nat) (s sn : FullState) : Prop where
  len : sn.LengthsOk c
  hw : FullWitnessCutInv c F0 F_cur cut sn.core
  cov : FullAnaMarksCov c sn
  ext : FullExtScratchPres s sn
  ws2 : sn.scratch.work_stk2 = s.scratch.work_stk2
  nd : FullArenaVarsNodup sn
  hrefs : fullArenaClauseRefs sn = fullArenaClauseRefs s
  stat : FullDeduceStaticEq s.core sn.core
  tl_ge : 1 ≤ sn.core.tmp_len
  tl_cv : sn.core.tmp_len ≤ sn.core.cur_vars
  tc_eq : sn.core.tmp_cnt = (fullCurTrailIdxs sn.core sn.core.mrk idx).length
  low : FullLowerInv c sn.core sn.core.tmp sn.core.mrk sn.core.tmp_len
  mcov : FullMarksCov sn.core sn.core.tmp sn.core.mrk sn.core.tmp_len
  cmcut : FullCurMarksBelow idx sn.core sn.core.mrk cut
  ent : (cnfOfClauses F_cur).EntailsClause
    (cnfClause (fullActiveResolvent sn.core sn.core.tmp sn.core.mrk sn.core.tmp_len idx))
  res_eq : sn.scratch.res_sz = BitVec.ofNat 64 ((sn.core.tmp_len - 1) + sn.core.tmp_cnt)

theorem fullDeduceStaticEq_refl (k : FullCoreState) : FullDeduceStaticEq k k :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem FullDeduceStaticEq.trans {k0 k1 k2 : FullCoreState}
    (h01 : FullDeduceStaticEq k0 k1) (h12 : FullDeduceStaticEq k1 k2) :
    FullDeduceStaticEq k0 k2 :=
  ⟨h12.cv.trans h01.cv, h12.cl.trans h01.cl, h12.te.trans h01.te, h12.trl.trans h01.trl,
   h12.lvl.trans h01.lvl, h12.rsns.trans h01.rsns, h12.vals.trans h01.vals,
   h12.fuel.trans h01.fuel, h12.dm.trans h01.dm, h12.lm.trans h01.lm⟩

/-! ## 3. Resolvent Index, Membership & UIP Exit Lemmas -/

theorem fullLowerLits_one (tmp : List (BitVec 32)) : fullLowerLits tmp 1 = [] := by
  unfold fullLowerLits; cases tmp <;> simp

theorem fullLowerLits_take_eq {tmp : List (BitVec 32)} {tl : Nat} {uip : BitVec 32}
    (h1 : 1 ≤ tl) (h0 : tmp[0]? = some uip) :
    (tmp.take tl).map BitVec.toNat = uip.toNat :: fullLowerLits tmp tl := by
  cases tmp with
  | nil => simp at h0
  | cons x xs =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0; subst h0
    cases tl with
    | zero => omega
    | succ n => simp [fullLowerLits]

theorem fullLowerLits_mem_iff {tmp : List (BitVec 32)} {tl : Nat}
    (htl : tl ≤ tmp.length) {l : Nat} :
    l ∈ fullLowerLits tmp tl ↔ ∃ j, 1 ≤ j ∧ j < tl ∧ (tmp[j]?.getD 0#32).toNat = l := by
  unfold fullLowerLits
  rw [List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hx
    rw [List.getElem_drop, List.getElem_take] at hget
    have hlt : 1 + i < tl := by
      rw [List.length_drop, List.length_take, Nat.min_eq_left htl] at hi; omega
    refine ⟨1 + i, by omega, hlt, ?_⟩
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]
  · rintro ⟨j, hj1, hj2, hget⟩
    have hj_len : j < (tmp.take tl).length := by
      rw [List.length_take, Nat.min_eq_left htl]; exact hj2
    refine ⟨tmp[j]'(by omega), ?_, ?_⟩
    · rw [List.mem_iff_getElem]
      refine ⟨j - 1, by rw [List.length_drop]; omega, ?_⟩
      rw [List.getElem_drop, List.getElem_take]; simp [show 1 + (j - 1) = j by omega]
    · rw [← hget, List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem fullLowerLits_length {tmp : List (BitVec 32)} {tl : Nat}
    (_h1 : 1 ≤ tl) (htl : tl ≤ tmp.length) :
    (fullLowerLits tmp tl).length = tl - 1 := by
  unfold fullLowerLits
  rw [List.length_map, List.length_drop, List.length_take, Nat.min_eq_left htl]

theorem fullLowerLits_vars_nodup {c : FullCfg} {k : FullCoreState} {tmp : List (BitVec 32)}
    {mrk : List (BitVec 8)} {tl : Nat} (hlow : FullLowerInv c k tmp mrk tl)
    (htl : tl ≤ tmp.length) : ((fullLowerLits tmp tl).map (· / 2)).Nodup := by
  unfold fullLowerLits List.Nodup
  rw [List.map_map, List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hlen : (((tmp.take tl).drop 1).map ((fun x => x / 2) ∘ BitVec.toNat)).length =
      tl - 1 := by
    rw [List.length_map, List.length_drop, List.length_take, Nat.min_eq_left htl]
  rw [hlen] at hi hj
  simp only [List.getElem_map, Function.comp_apply, List.getElem_drop, List.getElem_take]
  have hne := hlow.2 (1 + i) (1 + j) (by omega) (by omega) (by omega)
  rwa [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
    Option.getD_some, Option.getD_some] at hne

theorem fullTmpTake_uip_nodup {c : FullCfg} {k : FullCoreState} {tmp : List (BitVec 32)}
    {mrk : List (BitVec 8)} {tl : Nat} {uip : BitVec 32}
    (h1 : 1 ≤ tl) (htl : tl ≤ tmp.length) (h0 : tmp[0]? = some uip)
    (hlow : FullLowerInv c k tmp mrk tl)
    (huip : (k.lvl[uip.toNat / 2]?.getD 0#32).toNat = k.cur_level) :
    ((tmp.take tl).map fun x => x.toNat / 2).Nodup := by
  have h0_eq : (tmp.take tl).map (fun x : BitVec 32 => x.toNat / 2) =
      (uip.toNat / 2) :: ((fullLowerLits tmp tl).map (· / 2)) := by
    cases tmp with
    | nil => simp at h0
    | cons x xs =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h0; subst h0
      cases tl with
      | zero => omega
      | succ n => simp [fullLowerLits, List.map_map]; rfl
  rw [h0_eq, List.nodup_cons]
  refine ⟨?_, fullLowerLits_vars_nodup hlow htl⟩
  intro hmem
  rw [List.mem_map] at hmem
  obtain ⟨l, hl, hdiv⟩ := hmem
  obtain ⟨j, hj1, hj2, hj_eq⟩ := (fullLowerLits_mem_iff htl).mp hl
  have hj_lt := (hlow.1 j hj1 hj2).2.2.2.1
  rw [hj_eq, hdiv, huip] at hj_lt; omega

theorem fullCurTrailIdxs_succ_true {k : FullCoreState} {mrk : List (BitVec 8)} {idx : Nat}
    (hm : mrk[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8)
    (hl : (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = k.cur_level) :
    fullCurTrailIdxs k mrk (idx + 1) = fullCurTrailIdxs k mrk idx ++ [idx] := by
  unfold fullCurTrailIdxs
  rw [List.range_succ, List.filter_append, List.filter_cons]
  simp [hm, hl]

theorem fullCurTrailIdxs_succ_eq_self {k : FullCoreState} {mrk : List (BitVec 8)} {idx : Nat}
    (hnot : ¬ (mrk[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
      (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = k.cur_level)) :
    fullCurTrailIdxs k mrk (idx + 1) = fullCurTrailIdxs k mrk idx := by
  unfold fullCurTrailIdxs
  rw [List.range_succ, List.filter_append, List.filter_cons]
  simp only [decide_eq_false hnot, Bool.false_eq_true, ↓reduceIte, List.filter_nil,
    List.append_nil]

theorem fullCurLits_succ_true {k : FullCoreState} {mrk : List (BitVec 8)} {idx : Nat}
    (hm : mrk[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8)
    (hl : (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = k.cur_level) :
    fullCurLits k mrk (idx + 1) =
      fullCurLits k mrk idx ++ [(k.trl[idx]?.getD 0#32).toNat ^^^ 1] := by
  unfold fullCurLits
  rw [fullCurTrailIdxs_succ_true hm hl, List.map_append, List.map_singleton]

theorem fullCurLits_succ_eq_self {k : FullCoreState} {mrk : List (BitVec 8)} {idx : Nat}
    (hnot : ¬ (mrk[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
      (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = k.cur_level)) :
    fullCurLits k mrk (idx + 1) = fullCurLits k mrk idx := by
  unfold fullCurLits; rw [fullCurTrailIdxs_succ_eq_self hnot]

theorem fullCurTrailIdxs_mem_iff {k : FullCoreState} {mrk : List (BitVec 8)} {idx j : Nat} :
    j ∈ fullCurTrailIdxs k mrk idx ↔
      j < idx ∧ mrk[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
        (k.lvl[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = k.cur_level := by
  unfold fullCurTrailIdxs
  rw [List.mem_filter, List.mem_range, decide_eq_true_iff]

theorem fullCurTrailIdxs_vars_nodup {k : FullCoreState} {mrk : List (BitVec 8)} {idx : Nat}
    (hidx : idx ≤ k.trail_end)
    (hnd : ∀ i j, i < k.trail_end → j < k.trail_end →
      (k.trl[i]?.getD 0#32).toNat / 2 = (k.trl[j]?.getD 0#32).toNat / 2 → i = j) :
    ((fullCurTrailIdxs k mrk idx).map fun j => (k.trl[j]?.getD 0#32).toNat / 2).Nodup := by
  refine ded_nodup_map_on (fun i hi j hj heq => ?_) (List.Pairwise.filter _ List.nodup_range)
  have hi' := (fullCurTrailIdxs_mem_iff.mp hi).1
  have hj' := (fullCurTrailIdxs_mem_iff.mp hj).1
  exact hnd i j (Nat.lt_of_lt_of_le hi' hidx) (Nat.lt_of_lt_of_le hj' hidx) heq

theorem fullActiveResolvent_le_cur_vars {c : FullCfg} {k : FullCoreState}
    {tmp : List (BitVec 32)} {mrk : List (BitVec 8)} {tl idx : Nat}
    (hidx : idx ≤ k.trail_end) (htl1 : 1 ≤ tl) (htl_len : tl ≤ tmp.length)
    (hlow : FullLowerInv c k tmp mrk tl)
    (hlit_lt : ∀ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat < 2 * k.cur_vars)
    (hnd : ∀ i j, i < k.trail_end → j < k.trail_end →
      (k.trl[i]?.getD 0#32).toNat / 2 = (k.trl[j]?.getD 0#32).toNat / 2 → i = j) :
    (tl - 1) + (fullCurTrailIdxs k mrk idx).length ≤ k.cur_vars := by
  let vsL := (fullLowerLits tmp tl).map (· / 2)
  let vsC := (fullCurTrailIdxs k mrk idx).map fun j => (k.trl[j]?.getD 0#32).toNat / 2
  have hndL : vsL.Nodup := fullLowerLits_vars_nodup hlow htl_len
  have hndC : vsC.Nodup := fullCurTrailIdxs_vars_nodup hidx hnd
  have hdisj : ∀ v ∈ vsL, v ∉ vsC := by
    intro v hvL hvC
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hvL
    obtain ⟨j, hj1, hj2, hjeq⟩ := (fullLowerLits_mem_iff htl_len).mp hl
    obtain ⟨i, hi, hieq⟩ := List.mem_map.mp hvC
    have hci := fullCurTrailIdxs_mem_iff.mp hi
    have hlt := (hlow.1 j hj1 hj2).2.2.2.1
    rw [hjeq, ← hieq, hci.2.2] at hlt; omega
  have hndAll : (vsL ++ vsC).Nodup := List.nodup_append.mpr
    ⟨hndL, hndC, fun v hvL w hvC heq => hdisj v hvL (heq ▸ hvC)⟩
  have hsub : vsL ++ vsC ⊆ List.range k.cur_vars := by
    intro v hv; rw [List.mem_range]
    rcases List.mem_append.mp hv with hvL | hvC
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hvL
      obtain ⟨j, hj1, hj2, hjeq⟩ := (fullLowerLits_mem_iff htl_len).mp hl
      have hlt := (hlow.1 j hj1 hj2).1; rw [← hjeq]; omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hvC
      have hi1 := (fullCurTrailIdxs_mem_iff.mp hi).1
      have hlt := hlit_lt i (Nat.lt_of_lt_of_le hi1 hidx); omega
  have hle := List.Nodup.length_le_of_subset hndAll hsub
  rw [List.length_append, List.length_map, List.length_map,
    fullLowerLits_length htl1 htl_len, List.length_range] at hle
  exact hle

theorem fullDeduce_uip_entails {F_cur : List (List Nat)} {k : FullCoreState}
    {tmp : List (BitVec 32)} {mrk : List (BitVec 8)} {tl idx' : Nat} {p_bv : BitVec 32}
    (hct0 : (fullCurTrailIdxs k mrk idx').length = 0)
    (hm : mrk[(k.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8)
    (hl : (k.lvl[(k.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32).toNat = k.cur_level)
    (hp_get : (k.trl[idx']?.getD 0#32).toNat = p_bv.toNat)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullActiveResolvent k tmp mrk tl (idx' + 1)))) :
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((p_bv ^^^ 1#32).toNat :: fullLowerLits tmp tl)) := by
  have hnil : fullCurTrailIdxs k mrk idx' = [] := List.eq_nil_of_length_eq_zero hct0
  have hcl : fullCurLits k mrk (idx' + 1) = [p_bv.toNat ^^^ 1] := by
    rw [fullCurLits_succ_true hm hl]
    unfold fullCurLits; rw [hnil, hp_get]; rfl
  refine ded_clause_entails_of_subset hent fun l hl => ?_
  unfold fullActiveResolvent at hl
  rw [hcl, List.singleton_append] at hl
  rwa [ded_bv32_xor1_toNat]

theorem fullAnaMarksCov_of_clear {c : FullCfg} {s : FullState}
    (hm : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) (hmcl : s.core.min_clr_len = 0) :
    FullAnaMarksCov c s :=
  ⟨by rw [hmcl]; exact Nat.zero_le _, by rw [hmcl]; simp,
   fun k hk => by omega,
   fun v hv hnz => absurd (hm v hv) hnz⟩

theorem fullDeduceStateInv_with_counts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx : Nat} {s s0 s1 : FullState}
    (hs0 : FullDeduceStateInv c F0 F_cur cut idx s s0) (hlen1 : s1.LengthsOk c)
    (hw1 : FullWitnessCutInv c F0 F_cur cut s1.core) (hcov1 : FullAnaMarksCov c s1)
    (hnd1 : FullArenaVarsNodup s1) (hrefs1 : fullArenaClauseRefs s1 = fullArenaClauseRefs s)
    (hext1 : FullExtScratchPres s s1) (hws2 : s1.scratch.work_stk2 = s.scratch.work_stk2)
    (hcore : s1.core.cur_vars = s0.core.cur_vars ∧ s1.core.cur_level = s0.core.cur_level ∧
      s1.core.trail_end = s0.core.trail_end ∧ s1.core.trl = s0.core.trl ∧
      s1.core.lvl = s0.core.lvl ∧ s1.core.rsns = s0.core.rsns ∧ s1.core.vals = s0.core.vals ∧
      s1.core.fuel = s0.core.fuel ∧ s1.core.dense_mode = s0.core.dense_mode ∧
      s1.core.lit_mark = s0.core.lit_mark ∧ s1.core.tmp_cnt = s0.core.tmp_cnt ∧
      s1.core.tmp_len = s0.core.tmp_len ∧ s1.core.mrk = s0.core.mrk ∧
      s1.core.tmp = s0.core.tmp)
    (hres : s1.scratch.res_sz = s0.scratch.res_sz) :
    FullDeduceStateInv c F0 F_cur cut idx s s1 := by
  obtain ⟨hcv, hcl, hte, htrl, hlvl, hrsns, hvals, hfu, hdm, hlm, htc, htl, hmrk, htmp⟩ := hcore
  have hst : FullDeduceStaticEq s.core s1.core :=
    ⟨hcv.trans hs0.stat.cv, hcl.trans hs0.stat.cl, hte.trans hs0.stat.te,
     htrl.trans hs0.stat.trl, hlvl.trans hs0.stat.lvl, hrsns.trans hs0.stat.rsns,
     hvals.trans hs0.stat.vals, hfu.trans hs0.stat.fuel, hdm.trans hs0.stat.dm,
     hlm.trans hs0.stat.lm⟩
  refine ⟨hlen1, hw1, hcov1, hext1, hws2, hnd1, hrefs1, hst,
    htl ▸ hs0.tl_ge, htl ▸ hcv ▸ hs0.tl_cv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [htc]; unfold fullCurTrailIdxs; rw [htrl, hmrk, hlvl, hcl]; exact hs0.tc_eq
  · unfold FullLowerInv; rw [hcv, hvals, hlvl, hcl, htmp, hmrk, htl]; exact hs0.low
  · unfold FullMarksCov; rw [hcv, hlvl, hcl, htmp, hmrk, htl]; exact hs0.mcov
  · have hcm := hs0.cmcut
    unfold FullCurMarksBelow at hcm ⊢
    rw [htrl, hmrk, hlvl, hcl]; exact hcm
  · unfold fullActiveResolvent fullLowerLits fullCurLits fullCurTrailIdxs
    rw [htmp, htl, htrl, hlvl, hcl, hmrk]; exact hs0.ent
  · rw [hres, htl, htc]; exact hs0.res_eq

/-! ## 4. Seed Literal & Reason Transition Semantics -/

private theorem ded_filter_length_flip_one {α : Type} (p0 p1 : α → Bool) (m : α) :
    ∀ xs : List α, xs.Nodup → m ∈ xs → p0 m = false → p1 m = true →
      (∀ x ∈ xs, x ≠ m → p1 x = p0 x) →
      (xs.filter p1).length = (xs.filter p0).length + 1
  | [], _, hm, _, _, _ => by simp at hm
  | x :: xs, hnd, hm, hp0, hp1, heq => by
    rw [List.nodup_cons] at hnd
    have htail : ∀ y ∈ xs, y ≠ m → p1 y = p0 y := fun y hy => heq y (List.mem_cons_of_mem _ hy)
    by_cases hxm : x = m
    · subst hxm
      have hsub : xs.filter p1 = xs.filter p0 := List.filter_congr fun y hy =>
        htail y hy (fun h => hnd.1 (h ▸ hy))
      simp [hp0, hp1, hsub]
    · have hm' : m ∈ xs := (List.mem_cons.mp hm).resolve_left (Ne.symm hxm)
      have hpx := heq x List.mem_cons_self hxm
      have ih := ded_filter_length_flip_one p0 p1 m xs hnd.2 hm' hp0 hp1 htail
      cases h0x : p0 x <;> simp [hpx, h0x, ih] <;> omega

private theorem ded_seed_lit_counts {F0 : CNF Nat} {F_cur : List (List Nat)} {c : FullCfg}
    {cut : Nat} {k k' : FullCoreState} {mrk' : List (BitVec 8)} {tmp' : List (BitVec 32)}
    {tc' tl' : Nat} {res' : BitVec 64} {lit : BitVec 32}
    (hlen : k.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut k)
    (_htl_ge : 1 ≤ k.tmp_len) (_htl_cv : k.tmp_len ≤ k.cur_vars)
    (htc_eq : k.tmp_cnt = (fullCurTrailIdxs k k.mrk k.trail_end).length)
    (_hres : k.tmp_len - 1 + k.tmp_cnt < 2 ^ 64)
    (hres_eq : res' = BitVec.ofNat 64 (k.tmp_len - 1 + k.tmp_cnt) +
      if lit.toNat / 2 < k.cur_vars ∧ k.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧
          mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8 then 1#64 else 0#64)
    (htc_spec : tc' = k.tmp_cnt +
      if lit.toNat / 2 < k.cur_vars ∧ k.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧
          mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
          (k.lvl[lit.toNat / 2]?.getD 0#32).toNat = k.cur_level then 1 else 0)
    (htl_ge' : k.tmp_len ≤ tl') (htl_le' : tl' ≤ k.tmp_len + 1)
    (hmp : ∀ v < c.max_vars, k.mrk[v]?.getD 0#8 ≠ 0#8 → mrk'[v]?.getD 0#8 = k.mrk[v]?.getD 0#8)
    (hnm : ∀ v < c.max_vars, k.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
      lit.toNat / 2 = v ∧ v < k.cur_vars ∧ v ≠ (0xFFFFFFFF#32).toNat ∧
        0 < (k.lvl[v]?.getD 0#32).toNat ∧ (k.lvl[v]?.getD 0#32).toNat ≤ k.cur_level)
    (hnt : ∀ j, k.tmp_len ≤ j → j < tl' → (tmp'[j]?.getD 0#32).toNat = lit.toNat ∧
      lit.toNat / 2 < k.cur_vars ∧ lit.toNat / 2 ≠ (0xFFFFFFFF#32).toNat ∧
      k.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧ 0 < (k.lvl[lit.toNat / 2]?.getD 0#32).toNat ∧
      (k.lvl[lit.toNat / 2]?.getD 0#32).toNat < k.cur_level ∧ mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8)
    (hok : lit.toNat / 2 < k.cur_vars ∧
      ((0 < (k.lvl[lit.toNat / 2]?.getD 0#32).toNat → mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8) ∧
        (k.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 →
          (k.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ k.cur_level ∧
          (0 < (k.lvl[lit.toNat / 2]?.getD 0#32).toNat →
            (k.lvl[lit.toNat / 2]?.getD 0#32).toNat = k.cur_level → tc' = k.tmp_cnt + 1) ∧
          (0 < (k.lvl[lit.toNat / 2]?.getD 0#32).toNat →
            (k.lvl[lit.toNat / 2]?.getD 0#32).toNat < k.cur_level →
            tl' = k.tmp_len + 1 ∧ tmp'[k.tmp_len]? = some lit))))
    (hlit_lt : lit.toNat < 2 * k.cur_vars) (hlit_f : k.vals[lit.toNat]?.getD 0#8 = 0xFF#8)
    (hk' : k'.trl = k.trl ∧ k'.lvl = k.lvl ∧ k'.cur_level = k.cur_level ∧
      k'.trail_end = k.trail_end ∧ k'.cur_vars = k.cur_vars) :
    tc' = (fullCurTrailIdxs k' mrk' k'.trail_end).length ∧
    res' = BitVec.ofNat 64 ((tl' - 1) + tc') := by
  obtain ⟨htrl, hlvl, hcl, hte, _hcv⟩ := hk'
  have hcv_le := hlen.cur_vars_le
  have htc_len : tc' = (fullCurTrailIdxs k mrk' k.trail_end).length := by
    let p0 : Nat → Bool := fun j => decide (k.mrk[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
      (k.lvl[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = k.cur_level)
    let p1 : Nat → Bool := fun j => decide (mrk'[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
      (k.lvl[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = k.cur_level)
    change tc' = ((List.range k.trail_end).filter p1).length
    have hagree : ∀ j ∈ List.range k.trail_end,
        k.mrk[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8 →
        mrk'[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 →
        lit.toNat / 2 = (k.trl[j]?.getD 0#32).toNat / 2 := fun j hj hm0 hmnz => by
      have hv := hw.trail_lits_lt j (List.mem_range.mp hj)
      exact (hnm _ (by omega) hm0 hmnz).1
    by_cases hcond : lit.toNat / 2 < k.cur_vars ∧ k.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧
        mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
        (k.lvl[lit.toNat / 2]?.getD 0#32).toNat = k.cur_level
    · obtain ⟨m, hm, hmeq⟩ := (hw.vals_false_iff lit.toNat hlit_lt).mp hlit_f
      have hmdiv : (k.trl[m]?.getD 0#32).toNat / 2 = lit.toNat / 2 := by
        rw [hmeq, ded_lit_xor1_div2]
      have hflip : ((List.range k.trail_end).filter p1).length =
          ((List.range k.trail_end).filter p0).length + 1 := by
        refine ded_filter_length_flip_one p0 p1 m (List.range k.trail_end) List.nodup_range
          (List.mem_range.mpr hm) (by simp [p0, hmdiv, hcond.2.1])
          (by simp [p1, hmdiv, hcond.2.2.1, hcond.2.2.2]) fun j hj hne => ?_
        have hj_te := List.mem_range.mp hj
        have hvd : (k.trl[j]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := fun h =>
          hne (hw.trail_vars_nodup j m hj_te hm (by rw [h, hmdiv]))
        have hmrk_eq : (mrk'[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8) ↔
            (k.mrk[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8) := by
          constructor
          · intro h1 h0; exact hvd (hagree j hj h0 h1).symm
          · intro h0; have hv := hw.trail_lits_lt j hj_te
            rw [hmp _ (by omega) h0]; exact h0
        rw [Bool.eq_iff_iff]; simp only [p0, p1, decide_eq_true_iff]; rw [hmrk_eq]
      unfold fullCurTrailIdxs at htc_eq
      rw [hflip, ← htc_eq, htc_spec, ite_eq_left hcond]
    · have hsame : ((List.range k.trail_end).filter p1).length =
          ((List.range k.trail_end).filter p0).length := by
        congr 1; apply List.filter_congr; intro j hj
        have hj_te := List.mem_range.mp hj
        have hv := hw.trail_lits_lt j hj_te
        by_cases hm0 : k.mrk[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8
        · by_cases hmnz : mrk'[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8
          · have hdiv := hagree j hj hm0 hmnz
            have hlev : (k.lvl[lit.toNat / 2]?.getD 0#32).toNat ≠ k.cur_level := fun h =>
              hcond ⟨hok.1, by rwa [hdiv], by rwa [hdiv], h⟩
            simp [p0, p1, ← hdiv, hlev]
          · simp [p0, p1, hm0, hmnz]
        · rw [Bool.eq_iff_iff]; simp only [p0, p1, decide_eq_true_iff]
          rw [hmp _ (by omega) hm0]
      unfold fullCurTrailIdxs at htc_eq
      rw [hsame, ← htc_eq, htc_spec, ite_eq_right hcond, Nat.add_zero]
  have htc_eq' : tc' = (fullCurTrailIdxs k' mrk' k'.trail_end).length := by
    rw [htc_len]; unfold fullCurTrailIdxs; rw [htrl, hlvl, hcl, hte]
  have hres_nat : (tl' - 1) + tc' = (k.tmp_len - 1 + k.tmp_cnt) +
      if lit.toNat / 2 < k.cur_vars ∧ k.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧
          mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8 then 1 else 0 := by
    by_cases hm0 : k.mrk[lit.toNat / 2]?.getD 0#8 = 0#8
    · by_cases hmnz : mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8
      · have hlev := (hnm _ (by omega) hm0 hmnz).2.2.2
        rcases Nat.lt_or_eq_of_le hlev.2 with hlt | heq
        · obtain ⟨htl1, _⟩ := (hok.2.2 hm0).2.2 hlev.1 hlt
          rw [htl1, htc_spec, ite_eq_right (fun h => by omega),
            ite_eq_left ⟨hok.1, hm0, hmnz⟩]; omega
        · have htl_eq : tl' = k.tmp_len := Classical.byContradiction fun hne => by
            have hlt := hnt k.tmp_len (le_refl _) (by omega); omega
          rw [htl_eq, htc_spec, ite_eq_left ⟨hok.1, hm0, hmnz, heq⟩,
            ite_eq_left ⟨hok.1, hm0, hmnz⟩]; omega
      · have htl_eq : tl' = k.tmp_len := Classical.byContradiction fun hne =>
          hmnz (hnt k.tmp_len (le_refl _) (by omega)).2.2.2.2.2.2
        rw [htl_eq, htc_spec, ite_eq_right (fun h => hmnz h.2.2.1),
          ite_eq_right (fun h => hmnz h.2.2)]; omega
    · have htl_eq : tl' = k.tmp_len := Classical.byContradiction fun hne =>
        hm0 (hnt k.tmp_len (le_refl _) (by omega)).2.2.2.1
      rw [htl_eq, htc_spec, ite_eq_right (fun h => hm0 h.2.1),
        ite_eq_right (fun h => hm0 h.2.1)]; omega
  refine ⟨htc_eq', ?_⟩
  rw [hres_eq, hres_nat]; split <;> simp [BitVec.ofNat_add]

theorem deduce_seed_lit_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat}
    {s sa : FullState} {lit : BitVec 32}
    {mrk' : List (BitVec 8)} {tmp' : List (BitVec 32)} {tc' tl' mcl' : Nat}
    {ws1' : List (BitVec 32)} {ant' res' : BitVec 64}
    (hlen_a : sa.LengthsOk c) (hw_a : FullWitnessCutInv c F0 F_cur cut sa.core)
    (hnd_a : FullArenaVarsNodup sa) (hrefs_a : fullArenaClauseRefs sa = fullArenaClauseRefs s)
    (hext_a : FullExtScratchPres s sa) (hws2_a : sa.scratch.work_stk2 = s.scratch.work_stk2)
    (hstat_a : FullDeduceStaticEq s.core sa.core)
    (htl_a1 : 1 ≤ sa.core.tmp_len) (htc_a : sa.core.tmp_cnt ≤ 1)
    (htca_eq : sa.core.tmp_cnt = (fullCurTrailIdxs sa.core sa.core.mrk sa.core.trail_end).length)
    (hlow_a : FullLowerInv c sa.core sa.core.tmp sa.core.mrk sa.core.tmp_len)
    (hmcov_a : FullMarksCov sa.core sa.core.tmp sa.core.mrk sa.core.tmp_len)
    (hcm_a : FullCurMarksBelow sa.core.trail_end sa.core sa.core.mrk cut)
    (hres_a : sa.scratch.res_sz =
      BitVec.ofNat 64 ((sa.core.tmp_len - 1) + sa.core.tmp_cnt))
    (hlit_lt : lit.toNat < 2 * sa.core.cur_vars)
    (hlit_f : sa.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8)
    (hlit_cut : (sa.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = sa.core.cur_level →
      ∃ m < cut, (sa.core.trl[m]?.getD 0#32).toNat = lit.toNat ^^^ 1)
    (sb : FullState)
    (hsb_c : sb.core = { sa.core with mrk := mrk', tmp := tmp', tmp_cnt := tc',
                                      tmp_len := tl', min_clr_len := mcl' })
    (hsb_sc : sb.scratch = { sa.scratch with work_stk1 := ws1', ant_sz := ant', res_sz := res' })
    (hlen_b : sb.LengthsOk c) (hcov_b : FullAnaMarksCov c sb)
    (htl_b_cv : tl' ≤ sa.core.cur_vars) (htl_b_ge : sa.core.tmp_len ≤ tl')
    (htl_b_le : tl' ≤ sa.core.tmp_len + 1)
    (hmp : ∀ v < c.max_vars, sa.core.mrk[v]?.getD 0#8 ≠ 0#8 →
      mrk'[v]?.getD 0#8 = sa.core.mrk[v]?.getD 0#8)
    (htp : ∀ k < sa.core.tmp_len, tmp'[k]? = sa.core.tmp[k]?)
    (hnm : ∀ v < c.max_vars, sa.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
      lit.toNat / 2 = v ∧ v < sa.core.cur_vars ∧ v ≠ (0xFFFFFFFF#32).toNat ∧
        0 < (sa.core.lvl[v]?.getD 0#32).toNat ∧
        (sa.core.lvl[v]?.getD 0#32).toNat ≤ sa.core.cur_level)
    (hnt : ∀ j, sa.core.tmp_len ≤ j → j < tl' → (tmp'[j]?.getD 0#32).toNat = lit.toNat ∧
      lit.toNat / 2 < sa.core.cur_vars ∧ lit.toNat / 2 ≠ (0xFFFFFFFF#32).toNat ∧
      sa.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧
      0 < (sa.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ∧
      (sa.core.lvl[lit.toNat / 2]?.getD 0#32).toNat < sa.core.cur_level ∧
      mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8)
    (hres_b : res' = sa.scratch.res_sz +
      if lit.toNat / 2 < sa.core.cur_vars ∧ sa.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧
          mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8 then 1#64 else 0#64)
    (htc_b : tc' = sa.core.tmp_cnt +
      if lit.toNat / 2 < sa.core.cur_vars ∧ sa.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧
          mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
          (sa.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = sa.core.cur_level then 1 else 0)
    (hok : lit.toNat / 2 < sa.core.cur_vars ∧
      ((0 < (sa.core.lvl[lit.toNat / 2]?.getD 0#32).toNat → mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8) ∧
        (sa.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 →
          (sa.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ sa.core.cur_level ∧
          (0 < (sa.core.lvl[lit.toNat / 2]?.getD 0#32).toNat →
            (sa.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = sa.core.cur_level →
            tc' = sa.core.tmp_cnt + 1) ∧
          (0 < (sa.core.lvl[lit.toNat / 2]?.getD 0#32).toNat →
            (sa.core.lvl[lit.toNat / 2]?.getD 0#32).toNat < sa.core.cur_level →
            tl' = sa.core.tmp_len + 1 ∧ tmp'[sa.core.tmp_len]? = some lit)))) :
    sb.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut sb.core ∧ FullAnaMarksCov c sb ∧
      FullExtScratchPres s sb ∧ sb.scratch.work_stk2 = s.scratch.work_stk2 ∧
      FullArenaVarsNodup sb ∧ fullArenaClauseRefs sb = fullArenaClauseRefs s ∧
      FullDeduceStaticEq s.core sb.core ∧ 1 ≤ sb.core.tmp_len ∧
      sb.core.tmp_len ≤ sb.core.cur_vars ∧
      sb.core.tmp_cnt = (fullCurTrailIdxs sb.core sb.core.mrk sb.core.trail_end).length ∧
      FullLowerInv c sb.core sb.core.tmp sb.core.mrk sb.core.tmp_len ∧
      FullMarksCov sb.core sb.core.tmp sb.core.mrk sb.core.tmp_len ∧
      FullCurMarksBelow sb.core.trail_end sb.core sb.core.mrk cut ∧
      ((cnfOfClauses F_cur).EntailsClause
        (cnfClause (fullLowerLits sa.core.tmp sa.core.tmp_len)) →
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause (fullLowerLits sb.core.tmp sb.core.tmp_len))) ∧
      (lit.toNat ∈ fullActiveResolvent sb.core sb.core.tmp sb.core.mrk sb.core.tmp_len
          sb.core.trail_end ∨
        (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat ^^^ 1])) ∧
      sb.scratch.res_sz = BitVec.ofNat 64 ((sb.core.tmp_len - 1) + sb.core.tmp_cnt) := by
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hlen_a.core_ok.cur_vars_le
  have hsb_te : sb.core.trail_end = sa.core.trail_end := by rw [hsb_c]
  have hsb_trl : sb.core.trl = sa.core.trl := by rw [hsb_c]
  have hsb_lvl : sb.core.lvl = sa.core.lvl := by rw [hsb_c]
  have hsb_cl : sb.core.cur_level = sa.core.cur_level := by rw [hsb_c]
  have hsb_cv : sb.core.cur_vars = sa.core.cur_vars := by rw [hsb_c]
  have hsb_vals : sb.core.vals = sa.core.vals := by rw [hsb_c]
  have hsb_mrk : sb.core.mrk = mrk' := by rw [hsb_c]
  have hsb_tmp : sb.core.tmp = tmp' := by rw [hsb_c]
  have hsb_tc : sb.core.tmp_cnt = tc' := by rw [hsb_c]
  have hsb_tl : sb.core.tmp_len = tl' := by rw [hsb_c]
  have hsb_res : sb.scratch.res_sz = res' := by rw [hsb_sc]
  have hhw_b : FullWitnessCutInv c F0 F_cur cut sb.core := by
    rw [hsb_c]; exact deduce_same_core_cut hw_a mrk' tmp' tc' tl' mcl'
  have hnd_b : FullArenaVarsNodup sb := by
    unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseRefsCore
      fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore fullArenaClauseLits
      fullArenaClauseLitsCore fullArenaClauseSizeCore at hnd_a ⊢
    rw [hsb_c]; exact hnd_a
  have hrefs_b : fullArenaClauseRefs sb = fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [hsb_c]; exact hrefs_a
  have hstat_b : FullDeduceStaticEq s.core sb.core :=
    hstat_a.trans (by rw [hsb_c]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  have hext_b : FullExtScratchPres s sb :=
    fullExtScratchPres_trans hext_a ⟨by rw [hsb_sc], by rw [hsb_sc]⟩
  have hws2_b : sb.scratch.work_stk2 = s.scratch.work_stk2 := by rw [hsb_sc]; exact hws2_a
  have htl_b1 : 1 ≤ tl' := Nat.le_trans htl_a1 htl_b_ge
  have hlow_b : FullLowerInv c sb.core tmp' mrk' tl' := by
    unfold FullLowerInv
    rw [hsb_cv, hsb_vals, hsb_lvl, hsb_cl]
    refine ⟨fun j hj1 hj2 => ?_, fun j1 j2 hj1 hj12 hj2 => ?_⟩
    · by_cases hja : j < sa.core.tmp_len
      · have hj_t := hlow_a.1 j hj1 hja
        have hltp : tmp'[j]?.getD 0#32 = sa.core.tmp[j]?.getD 0#32 := by rw [htp j hja]
        have hv_lt : (sa.core.tmp[j]?.getD 0#32).toNat / 2 < c.max_vars := by omega
        rw [hltp]; refine ⟨hj_t.1, hj_t.2.1, hj_t.2.2.1, hj_t.2.2.2.1, ?_⟩
        rw [hmp _ hv_lt hj_t.2.2.2.2]; exact hj_t.2.2.2.2
      · obtain ⟨heq, hv, _, hm0, hp, hlt, hmnz⟩ := hnt j (by omega) hj2
        rw [heq]; exact ⟨hlit_lt, hlit_f, hp, hlt, hmnz⟩
    · by_cases hj2a : j2 < sa.core.tmp_len
      · have h1 := htp j1 (by omega); have h2 := htp j2 hj2a
        have h12 := hlow_a.2 j1 j2 hj1 hj12 hj2a
        rwa [← h1, ← h2] at h12
      · by_cases hj1a : j1 < sa.core.tmp_len
        · have hj1_m := (hlow_a.1 j1 hj1 hj1a).2.2.2.2
          have hj1_p := htp j1 hj1a
          have hj2_nt := hnt j2 (by omega) hj2
          intro heq; rw [hj1_p, hj2_nt.1] at heq
          rw [heq] at hj1_m; exact absurd hj2_nt.2.2.2.1 hj1_m
        · omega
  have hmcov_b : FullMarksCov sb.core tmp' mrk' tl' := by
    unfold FullMarksCov
    rw [hsb_cv, hsb_lvl, hsb_cl]
    intro v hv hmnz
    by_cases hm0 : sa.core.mrk[v]?.getD 0#8 = 0#8
    · obtain ⟨hveq, hv_lt, _, hp, hle⟩ := hnm v (by omega) hm0 hmnz
      refine ⟨hp, hle, fun hlt => ⟨sa.core.tmp_len, htl_a1, ?_, ?_⟩⟩
      · have := ((hok.2.2 (by rwa [hveq])).2.2 (by rwa [hveq]) (by rwa [hveq])).1; omega
      · have ht_some := ((hok.2.2 (by rwa [hveq])).2.2 (by rwa [hveq]) (by rwa [hveq])).2
        rw [ht_some, Option.getD_some, hveq]
    · obtain ⟨hp, hle, hmem⟩ := hmcov_a v hv hm0
      refine ⟨hp, hle, fun hlt => ?_⟩
      obtain ⟨j, hj1, hj2, hjeq⟩ := hmem hlt
      exact ⟨j, hj1, Nat.lt_of_lt_of_le hj2 htl_b_ge, by rw [htp j hj2, hjeq]⟩
  have hcm_b : FullCurMarksBelow sb.core.trail_end sb.core mrk' cut := by
    unfold FullCurMarksBelow
    rw [hsb_te, hsb_trl, hsb_lvl, hsb_cl]
    intro j hj hmnz hlev
    by_cases hm0 : sa.core.mrk[(sa.core.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8
    · have hv := hw_a.trail_lits_lt j hj
      have hdiv := (hnm _ (by omega) hm0 hmnz).1
      obtain ⟨m, hm_cut, hmeq⟩ := hlit_cut (by rwa [hdiv])
      have hjeq := hw_a.trail_vars_nodup j m hj (Nat.lt_of_lt_of_le hm_cut hw_a.cut_le)
        (by rw [hmeq, ded_lit_xor1_div2, hdiv])
      rwa [hjeq]
    · exact hcm_a j hj hm0 hlev
  have htc_res := ded_seed_lit_counts hlen_a.core_ok hw_a htl_a1 (Nat.le_trans htl_b_ge htl_b_cv)
    (res' := res') htca_eq (by omega) (by rw [hres_a] at hres_b; exact hres_b) htc_b
    htl_b_ge htl_b_le hmp hnm hnt hok hlit_lt hlit_f ⟨hsb_trl, hsb_lvl, hsb_cl, hsb_te, hsb_cv⟩
  have hlow_sub : ∀ l ∈ fullLowerLits sa.core.tmp sa.core.tmp_len,
      l ∈ fullLowerLits sb.core.tmp sb.core.tmp_len := fun l hl => by
    obtain ⟨j, hj1, hj2, hjeq⟩ := (fullLowerLits_mem_iff
      (by rw [hlen_a.core_ok.tmp_len_arr]; exact hlen_a.core_ok.tmp_len_le)).mp hl
    rw [hsb_tmp, hsb_tl]
    exact (fullLowerLits_mem_iff (by
      rw [← hsb_tmp, hlen_b.core_ok.tmp_len_arr]
      exact Nat.le_trans htl_b_cv hcv_le)).mpr
      ⟨j, hj1, Nat.lt_of_lt_of_le hj2 htl_b_ge, by rw [htp j hj2, hjeq]⟩
  have hlit_disj : lit.toNat ∈ fullActiveResolvent sb.core sb.core.tmp sb.core.mrk
      sb.core.tmp_len sb.core.trail_end ∨
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat ^^^ 1]) := by
    rcases Nat.eq_zero_or_pos (sa.core.lvl[lit.toNat / 2]?.getD 0#32).toNat with h0 | hpos
    · right
      obtain ⟨m, hm, hmeq⟩ := (hw_a.vals_false_iff lit.toNat hlit_lt).mp hlit_f
      have hs := hw_a.level0_sound m hm (by rwa [hmeq, ded_lit_xor1_div2])
      rwa [hmeq] at hs
    · left; unfold fullActiveResolvent; rw [List.mem_append]
      have hm_nz : sb.core.mrk[lit.toNat / 2]?.getD 0#8 ≠ 0#8 := by
        rw [hsb_mrk]; exact hok.2.1 hpos
      have hlev : (sb.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ sb.core.cur_level := by
        rw [hsb_lvl, hsb_cl]
        obtain ⟨m, hm, hmeq⟩ := (hw_a.vals_false_iff lit.toNat hlit_lt).mp hlit_f
        have hl := hw_a.lvl_le m hm; rwa [hmeq, ded_lit_xor1_div2] at hl
      rcases Nat.lt_or_eq_of_le hlev with hlt | heq
      · right
        have hmcv : (sb.core.lvl[lit.toNat / 2]?.getD 0#32).toNat < sb.core.cur_level := hlt
        rw [hsb_mrk] at hm_nz
        rw [hsb_tmp, hsb_tl]
        obtain ⟨j, hj1, hj2, hjeq⟩ :=
          (hmcov_b (lit.toNat / 2) (by rw [hsb_cv]; exact hok.1) hm_nz).2.2 hmcv
        refine (fullLowerLits_mem_iff
          (by rw [← hsb_tmp, hlen_b.core_ok.tmp_len_arr];
              exact Nat.le_trans htl_b_cv hcv_le)).mpr ⟨j, hj1, hj2, ?_⟩
        have hlt_j : (tmp'[j]?.getD 0#32).toNat < 2 * sb.core.cur_vars :=
          (hlow_b.1 j hj1 hj2).1
        have hf_j : sb.core.vals[(tmp'[j]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 :=
          (hlow_b.1 j hj1 hj2).2.1
        exact ded_lit_eq_of_div2_eq_falsified hhw_b.toFullOtfsWitnessInv
          hlt_j (by omega) hf_j (by rw [hsb_vals]; exact hlit_f) hjeq
      · left
        obtain ⟨m, hm, hmeq⟩ := (hhw_b.vals_false_iff lit.toNat (by omega)).mp
          (by rw [hsb_vals]; exact hlit_f)
        unfold fullCurLits; rw [List.mem_map]
        refine ⟨m, fullCurTrailIdxs_mem_iff.mpr ⟨hm, ?_, ?_⟩, ?_⟩
        · rwa [hmeq, ded_lit_xor1_div2]
        · rwa [hmeq, ded_lit_xor1_div2]
        · rw [hmeq, ded_lit_xor1_xor1]
  refine ⟨hlen_b, hhw_b, hcov_b, hext_b, hws2_b, hnd_b, hrefs_b, hstat_b,
    by rw [hsb_tl]; exact htl_b1, by rw [hsb_tl, hsb_cv]; exact htl_b_cv,
    by rw [hsb_tc, hsb_mrk]; exact htc_res.1, by rw [hsb_mrk, hsb_tmp, hsb_tl]; exact hlow_b,
    by rw [hsb_mrk, hsb_tmp, hsb_tl]; exact hmcov_b, by rw [hsb_mrk]; exact hcm_b,
    fun hl => ded_clause_entails_of_subset hl hlow_sub, hlit_disj,
    by rw [hsb_res, hsb_tl, hsb_tc]; exact htc_res.2⟩

theorem deduce_seed_bin_sem {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat}
    {s sa sb : FullState}
    (hent_bin : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [s.core.confl_lit0.toNat, s.core.confl_lit1.toNat]))
    (hl0_res : s.core.confl_lit0.toNat ∈ fullActiveResolvent sa.core sa.core.tmp sa.core.mrk
        sa.core.tmp_len sa.core.trail_end ∨
      (cnfOfClauses F_cur).EntailsClause (cnfClause [s.core.confl_lit0.toNat ^^^ 1]))
    (hl1_res : s.core.confl_lit1.toNat ∈ fullActiveResolvent sb.core sb.core.tmp sb.core.mrk
        sb.core.tmp_len sb.core.trail_end ∨
      (cnfOfClauses F_cur).EntailsClause (cnfClause [s.core.confl_lit1.toNat ^^^ 1]))
    (hl0_mono : s.core.confl_lit0.toNat ∈ fullActiveResolvent sa.core sa.core.tmp sa.core.mrk
        sa.core.tmp_len sa.core.trail_end →
      s.core.confl_lit0.toNat ∈ fullActiveResolvent sb.core sb.core.tmp sb.core.mrk
        sb.core.tmp_len sb.core.trail_end)
    (hlen : sb.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut sb.core)
    (hcov : FullAnaMarksCov c sb) (hext : FullExtScratchPres s sb)
    (hws2 : sb.scratch.work_stk2 = s.scratch.work_stk2) (hnd : FullArenaVarsNodup sb)
    (hrefs : fullArenaClauseRefs sb = fullArenaClauseRefs s)
    (hstat : FullDeduceStaticEq s.core sb.core) (htl1 : 1 ≤ sb.core.tmp_len)
    (htl_cv : sb.core.tmp_len ≤ sb.core.cur_vars)
    (htc : sb.core.tmp_cnt = (fullCurTrailIdxs sb.core sb.core.mrk sb.core.trail_end).length)
    (hlow : FullLowerInv c sb.core sb.core.tmp sb.core.mrk sb.core.tmp_len)
    (hmcov : FullMarksCov sb.core sb.core.tmp sb.core.mrk sb.core.tmp_len)
    (hcm : FullCurMarksBelow sb.core.trail_end sb.core sb.core.mrk cut)
    (hres : sb.scratch.res_sz = BitVec.ofNat 64 ((sb.core.tmp_len - 1) + sb.core.tmp_cnt)) :
    FullDeduceStateInv c F0 F_cur cut sb.core.trail_end s sb := by
  refine ⟨hlen, hw, hcov, hext, hws2, hnd, hrefs, hstat, htl1, htl_cv, htc, hlow, hmcov, hcm,
    ?_, hres⟩
  refine ded_clause_entails_strip hent_bin fun l hl => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · exact hl0_res.imp hl0_mono id
  · exact hl1_res

/-! ## 5. General Reason-Analysis Transition (`deduce_analyzeRsn_core`) -/

private theorem ded_rsn_counts_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut lim extra : Nat} {k k' : FullCoreState} {mrk' : List (BitVec 8)}
    {tmp' : List (BitVec 32)} {tc' tl' : Nat} {res' : BitVec 64}
    {skip_var : BitVec 32} {lits : List Nat}
    (hlen : k.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut k)
    (htl_ge : 1 ≤ k.tmp_len) (_htl_cv : k.tmp_len ≤ k.cur_vars)
    (_htl_len' : tl' ≤ tmp'.length) (htl_ge' : k.tmp_len ≤ tl') (_htl_cv' : tl' ≤ k.cur_vars)
    (htc_eq : k.tmp_cnt = (fullCurTrailIdxs k k.mrk lim).length) (hlim : lim ≤ k.trail_end)
    (hcnt_spec : tc' - k.tmp_cnt = ((List.range k.cur_vars).filter fun w =>
      decide (k.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
      decide ((k.lvl[w]?.getD 0#32).toNat = k.cur_level)).length)
    (htc_ge : k.tmp_cnt ≤ tc')
    (hres_spec : res' = BitVec.ofNat 64 ((k.tmp_len - 1) + k.tmp_cnt + extra) + BitVec.ofNat 64
      ((List.range k.cur_vars).filter fun w =>
        decide (k.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length)
    (hnm : ∀ v < c.max_vars, k.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
      ∃ l ∈ lits, l / 2 = v ∧ v < k.cur_vars ∧ v ≠ skip_var.toNat ∧
        0 < (k.lvl[v]?.getD 0#32).toNat ∧ (k.lvl[v]?.getD 0#32).toNat ≤ k.cur_level)
    (hnt : ∀ j, k.tmp_len ≤ j → j < tl' → let l := (tmp'[j]?.getD 0#32).toNat
      l ∈ lits ∧ l < 2 * k.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
      k.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (k.lvl[l / 2]?.getD 0#32).toNat ∧
      (k.lvl[l / 2]?.getD 0#32).toNat < k.cur_level ∧ mrk'[l / 2]?.getD 0#8 ≠ 0#8)
    (hnd_j : ∀ j1 j2, k.tmp_len ≤ j1 → j1 < j2 → j2 < tl' →
      (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2)
    (hok_lits : ∀ l ∈ lits, l / 2 < k.cur_vars ∧ (l / 2 ≠ skip_var.toNat →
      (0 < (k.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
      (k.mrk[l / 2]?.getD 0#8 = 0#8 →
        (k.lvl[l / 2]?.getD 0#32).toNat ≤ k.cur_level ∧
        (0 < (k.lvl[l / 2]?.getD 0#32).toNat → (k.lvl[l / 2]?.getD 0#32).toNat < k.cur_level →
          ∃ j, k.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = l / 2))))
    (hmp : ∀ v < c.max_vars, k.mrk[v]?.getD 0#8 ≠ 0#8 → mrk'[v]?.getD 0#8 = k.mrk[v]?.getD 0#8)
    (hcur_tr : ∀ l ∈ lits, l / 2 ≠ skip_var.toNat →
      k.mrk[l / 2]?.getD 0#8 = 0#8 → (k.lvl[l / 2]?.getD 0#32).toNat = k.cur_level →
      ∃ m < lim, (k.trl[m]?.getD 0#32).toNat / 2 = l / 2)
    (hk' : k'.trl = k.trl ∧ k'.lvl = k.lvl ∧ k'.cur_level = k.cur_level) :
    tc' = (fullCurTrailIdxs k' mrk' lim).length ∧
      res' = BitVec.ofNat 64 ((tl' - 1) + tc' + extra) := by
  have hcv_le := hlen.cur_vars_le
  -- 1) `tl' - k.tmp_len` equals count of newly marked vars with `lvl < cur_level`
  let xs_lt : List Nat := (List.range (tl' - k.tmp_len)).map fun i => k.tmp_len + i
  let p_lt : Nat → Bool := fun w =>
    decide (k.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
      decide ((k.lvl[w]?.getD 0#32).toNat < k.cur_level)
  let p_eq : Nat → Bool := fun w =>
    decide (k.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
      decide ((k.lvl[w]?.getD 0#32).toNat = k.cur_level)
  let p_all : Nat → Bool := fun w =>
    decide (k.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8)
  have hlt_eq : tl' - k.tmp_len = ((List.range k.cur_vars).filter p_lt).length := by
    have hbij := ded_nodup_length_eq_of_map_bij (fun j => (tmp'[j]?.getD 0#32).toNat / 2)
      (xs := xs_lt) (ys := (List.range k.cur_vars).filter p_lt)
      (ded_nodup_map_on (fun a _ b _ h => by omega) List.nodup_range)
      (List.Pairwise.filter _ List.nodup_range)
      (fun j hj => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
        have hi' := List.mem_range.mp hi
        obtain ⟨_, hlt, _, hm0, _, hlv, hmnz⟩ := hnt (k.tmp_len + i) (by omega) (by omega)
        simp [p_lt, List.mem_filter, List.mem_range,
          show (tmp'[k.tmp_len + i]?.getD 0#32).toNat / 2 < k.cur_vars by omega, hm0, hlv, hmnz])
      (fun j1 hj1 j2 hj2 heq => by
        obtain ⟨i1, hi1, rfl⟩ := List.mem_map.mp hj1
        obtain ⟨i2, hi2, rfl⟩ := List.mem_map.mp hj2
        have hi1' := List.mem_range.mp hi1; have hi2' := List.mem_range.mp hi2
        rcases Nat.lt_trichotomy i1 i2 with h | rfl | h
        · exact absurd heq (hnd_j _ _ (by omega) (by omega) (by omega))
        · rfl
        · exact absurd heq.symm (hnd_j _ _ (by omega) (by omega) (by omega)))
      (fun w hw => by
        rw [List.mem_filter, List.mem_range] at hw
        simp only [p_lt, Bool.and_eq_true, decide_eq_true_iff] at hw
        obtain ⟨hw_cv, ⟨hm0, hmnz⟩, hlv⟩ := hw
        obtain ⟨l, hl, hdiv, _, hne, hpos, _⟩ := hnm w (by omega) hm0 hmnz
        obtain ⟨j, hj1, hj2, hjeq⟩ :=
          (((hok_lits l hl).2 (by rwa [hdiv])).2 (by rwa [hdiv])).2
            (by rwa [hdiv]) (by rwa [hdiv])
        exact ⟨j, List.mem_map.mpr ⟨j - k.tmp_len, List.mem_range.mpr (by omega), by omega⟩,
          hjeq.trans hdiv⟩)
    simpa [xs_lt, List.length_map, List.length_range] using hbij
  have hpart : ((List.range k.cur_vars).filter p_all).length =
      ((List.range k.cur_vars).filter p_lt).length +
        ((List.range k.cur_vars).filter p_eq).length := by
    have hcongr : (List.range k.cur_vars).filter p_all =
        (List.range k.cur_vars).filter (fun w => p_lt w || p_eq w) := by
      apply List.filter_congr; intro w hw
      have hw_cv := List.mem_range.mp hw
      rw [Bool.eq_iff_iff]
      simp only [p_all, p_lt, p_eq, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff]
      constructor
      · rintro ⟨hm0, hmnz⟩
        obtain ⟨_, _, _, _, _, _, hle⟩ := hnm w (by omega) hm0 hmnz
        rcases Nat.lt_or_eq_of_le hle with h | h
        · exact Or.inl ⟨⟨hm0, hmnz⟩, h⟩
        · exact Or.inr ⟨⟨hm0, hmnz⟩, h⟩
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    rw [hcongr]
    exact ded_filter_length_disjoint_add p_lt p_eq (List.range k.cur_vars) fun w _ h => by
      simp only [p_lt, p_eq, Bool.and_eq_true, decide_eq_true_iff] at h; omega
  have hres_final : res' = BitVec.ofNat 64 ((tl' - 1) + tc' + extra) := by
    rw [hres_spec, hpart, ← hlt_eq, ← hcnt_spec, ← BitVec.ofNat_add]
    congr 1; omega
  -- 2) `tc'` equals `(fullCurTrailIdxs k' mrk' lim).length`
  let newIdxs : List Nat := (fullCurTrailIdxs k mrk' lim).filter fun i =>
    decide (k.mrk[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8)
  have hpart_idx : (fullCurTrailIdxs k mrk' lim).length =
      (fullCurTrailIdxs k k.mrk lim).length + newIdxs.length := by
    let q0 : Nat → Bool := fun i =>
      decide (k.mrk[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
        (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = k.cur_level)
    let q1 : Nat → Bool := fun i =>
      decide (k.mrk[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8 ∧
        mrk'[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
        (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = k.cur_level)
    have hcongr1 : fullCurTrailIdxs k mrk' lim =
        (List.range lim).filter (fun i => q0 i || q1 i) := by
      unfold fullCurTrailIdxs; apply List.filter_congr; intro i hi
      have hi_te : i < k.trail_end := Nat.lt_of_lt_of_le (List.mem_range.mp hi) hlim
      have hv := hw.trail_lits_lt i hi_te
      rw [Bool.eq_iff_iff]; simp only [q0, q1, Bool.or_eq_true, decide_eq_true_iff]
      constructor
      · rintro ⟨hmnz, hlev⟩
        by_cases hm0 : k.mrk[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8
        · exact Or.inr ⟨hm0, hmnz, hlev⟩
        · exact Or.inl ⟨hm0, hlev⟩
      · rintro (⟨hm0, hlev⟩ | ⟨_, hmnz, hlev⟩)
        · exact ⟨by rw [hmp _ (by omega) hm0]; exact hm0, hlev⟩
        · exact ⟨hmnz, hlev⟩
    have hcongr2 : newIdxs = (List.range lim).filter q1 := by
      simp only [newIdxs, fullCurTrailIdxs, List.filter_filter]
      apply List.filter_congr; intro i _
      rw [Bool.eq_iff_iff]; simp only [q1, Bool.and_eq_true, decide_eq_true_iff]
    change (fullCurTrailIdxs k mrk' lim).length =
      ((List.range lim).filter q0).length + newIdxs.length
    rw [hcongr1, hcongr2]
    exact ded_filter_length_disjoint_add q0 q1 (List.range lim) fun i _ h => by
      simp only [q0, q1, decide_eq_true_iff] at h; exact h.1.1 h.2.1
  have hnew_bij : newIdxs.length = ((List.range k.cur_vars).filter p_eq).length := by
    refine ded_nodup_length_eq_of_map_bij (fun i => (k.trl[i]?.getD 0#32).toNat / 2)
      (xs := newIdxs) (ys := (List.range k.cur_vars).filter p_eq)
      (List.Pairwise.filter _ (List.Pairwise.filter _ List.nodup_range))
      (List.Pairwise.filter _ List.nodup_range)
      (fun i hi => by
        rw [List.mem_filter, decide_eq_true_iff] at hi
        obtain ⟨hi1, hm0⟩ := hi
        obtain ⟨hi_lim, hmnz, hlev⟩ := fullCurTrailIdxs_mem_iff.mp hi1
        have hi_lt := hw.trail_lits_lt i (Nat.lt_of_lt_of_le hi_lim hlim)
        simp [p_eq, List.mem_filter, List.mem_range, show (k.trl[i]?.getD 0#32).toNat / 2 <
          k.cur_vars by omega, hm0, hmnz, hlev])
      (fun i1 hi1 i2 hi2 heq => by
        rw [List.mem_filter] at hi1 hi2
        have h1 := (fullCurTrailIdxs_mem_iff.mp hi1.1).1
        have h2 := (fullCurTrailIdxs_mem_iff.mp hi2.1).1
        exact hw.trail_vars_nodup i1 i2 (Nat.lt_of_lt_of_le h1 hlim)
          (Nat.lt_of_lt_of_le h2 hlim) heq)
      (fun w hw_mem => by
        rw [List.mem_filter, List.mem_range] at hw_mem
        simp only [p_eq, Bool.and_eq_true, decide_eq_true_iff] at hw_mem
        obtain ⟨hw_cv, ⟨hm0, hmnz⟩, hlev⟩ := hw_mem
        obtain ⟨l, hl, hdiv, _, hne, _, _⟩ := hnm w (by omega) hm0 hmnz
        obtain ⟨m, hm_lim, hm_div⟩ :=
          hcur_tr l hl (by rw [hdiv]; exact hne) (by rw [hdiv]; exact hm0)
            (by rw [hdiv]; exact hlev)
        refine ⟨m, ?_, hm_div.trans hdiv⟩
        rw [List.mem_filter, fullCurTrailIdxs_mem_iff, decide_eq_true_iff]
        exact ⟨⟨hm_lim, by rwa [hm_div, hdiv], by rwa [hm_div, hdiv]⟩, by rwa [hm_div, hdiv]⟩)
  have htc_fin : tc' = (fullCurTrailIdxs k' mrk' lim).length := by
    have heq_f : fullCurTrailIdxs k' mrk' lim = fullCurTrailIdxs k mrk' lim := by
      unfold fullCurTrailIdxs; rw [hk'.1, hk'.2.1, hk'.2.2]
    rw [heq_f, hpart_idx, hnew_bij, ← htc_eq, ← hcnt_spec]; omega
  exact ⟨htc_fin, hres_final⟩

theorem ded_rsn_inv_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut lim extra : Nat} {s sl s2 : FullState} {rsn skip_var : BitVec 32}
    (hlen_l : sl.LengthsOk c) (hw_l : FullWitnessCutInv c F0 F_cur cut sl.core)
    (hstat_l : FullDeduceStaticEq s.core sl.core)
    (htl_ge : 1 ≤ sl.core.tmp_len) (htl_cv : sl.core.tmp_len ≤ sl.core.cur_vars)
    (htc_eq : sl.core.tmp_cnt = (fullCurTrailIdxs sl.core sl.core.mrk lim).length)
    (hlim : lim ≤ sl.core.trail_end) (hcut_lim : lim ≤ cut)
    (hlow_l : FullLowerInv c sl.core sl.core.tmp sl.core.mrk sl.core.tmp_len)
    (hmcov_l : FullMarksCov sl.core sl.core.tmp sl.core.mrk sl.core.tmp_len)
    (hcm_l : FullCurMarksBelow lim sl.core sl.core.mrk cut)
    (hres_l : sl.scratch.res_sz =
      BitVec.ofNat 64 ((sl.core.tmp_len - 1) + sl.core.tmp_cnt + extra))
    (hs2_c : s2.core.cur_vars = sl.core.cur_vars ∧ s2.core.cur_level = sl.core.cur_level ∧
      s2.core.trail_end = sl.core.trail_end ∧ s2.core.trl = sl.core.trl ∧
      s2.core.lvl = sl.core.lvl ∧ s2.core.rsns = sl.core.rsns ∧
      s2.core.vals = sl.core.vals ∧ s2.core.fuel = sl.core.fuel ∧
      s2.core.dense_mode = sl.core.dense_mode ∧ s2.core.lit_mark = sl.core.lit_mark)
    (hlen2 : s2.LengthsOk c) (hw2 : FullWitnessCutInv c F0 F_cur cut s2.core)
    (hcov2 : FullAnaMarksCov c s2) (hext2 : FullExtScratchPres sl s2)
    (hws2_2 : s2.scratch.work_stk2 = sl.scratch.work_stk2)
    (htl2_ge : sl.core.tmp_len ≤ s2.core.tmp_len) (htl2_cv : s2.core.tmp_len ≤ sl.core.cur_vars)
    (htc2_ge : sl.core.tmp_cnt ≤ s2.core.tmp_cnt)
    (hrefs2 : fullArenaClauseRefs s2 = fullArenaClauseRefs sl)
    (hnd2 : FullArenaVarsNodup s2)
    (hmp : ∀ v < c.max_vars, sl.core.mrk[v]?.getD 0#8 ≠ 0#8 →
      s2.core.mrk[v]?.getD 0#8 = sl.core.mrk[v]?.getD 0#8)
    (htp : ∀ k < sl.core.tmp_len, s2.core.tmp[k]? = sl.core.tmp[k]?)
    (hnm : ∀ v < c.max_vars, sl.core.mrk[v]?.getD 0#8 = 0#8 → s2.core.mrk[v]?.getD 0#8 ≠ 0#8 →
      ∃ l ∈ fullRsnLits sl rsn, l / 2 = v ∧ v < sl.core.cur_vars ∧ v ≠ skip_var.toNat ∧
        0 < (sl.core.lvl[v]?.getD 0#32).toNat ∧
        (sl.core.lvl[v]?.getD 0#32).toNat ≤ sl.core.cur_level)
    (hnt : ∀ j, sl.core.tmp_len ≤ j → j < s2.core.tmp_len →
      let l := (s2.core.tmp[j]?.getD 0#32).toNat
      l ∈ fullRsnLits sl rsn ∧ l < 2 * sl.core.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
      sl.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (sl.core.lvl[l / 2]?.getD 0#32).toNat ∧
      (sl.core.lvl[l / 2]?.getD 0#32).toNat < sl.core.cur_level ∧
      s2.core.mrk[l / 2]?.getD 0#8 ≠ 0#8)
    (hnd_j : ∀ j1 j2, sl.core.tmp_len ≤ j1 → j1 < j2 → j2 < s2.core.tmp_len →
      (s2.core.tmp[j1]?.getD 0#32).toNat / 2 ≠ (s2.core.tmp[j2]?.getD 0#32).toNat / 2)
    (hcnt : s2.core.tmp_cnt - sl.core.tmp_cnt = ((List.range sl.core.cur_vars).filter fun w =>
      decide (sl.core.mrk[w]?.getD 0#8 = 0#8) && decide (s2.core.mrk[w]?.getD 0#8 ≠ 0#8) &&
      decide ((sl.core.lvl[w]?.getD 0#32).toNat = sl.core.cur_level)).length)
    (hres2 : s2.scratch.res_sz = sl.scratch.res_sz + BitVec.ofNat 64
      ((List.range sl.core.cur_vars).filter fun w =>
        decide (sl.core.mrk[w]?.getD 0#8 = 0#8) && decide (s2.core.mrk[w]?.getD 0#8 ≠ 0#8)).length)
    (hok_lits : ∀ l ∈ fullRsnLits sl rsn, l / 2 < sl.core.cur_vars ∧
      (l / 2 ≠ skip_var.toNat →
        (0 < (sl.core.lvl[l / 2]?.getD 0#32).toNat → s2.core.mrk[l / 2]?.getD 0#8 ≠ 0#8) ∧
        (sl.core.mrk[l / 2]?.getD 0#8 = 0#8 →
          (sl.core.lvl[l / 2]?.getD 0#32).toNat ≤ sl.core.cur_level ∧
          (0 < (sl.core.lvl[l / 2]?.getD 0#32).toNat →
            (sl.core.lvl[l / 2]?.getD 0#32).toNat < sl.core.cur_level →
            ∃ j, sl.core.tmp_len ≤ j ∧ j < s2.core.tmp_len ∧
              (s2.core.tmp[j]?.getD 0#32).toNat / 2 = l / 2))))
    (hrsn_fals : ∀ l ∈ fullRsnLits sl rsn, l / 2 ≠ skip_var.toNat →
      sl.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hcur_tr : ∀ l ∈ fullRsnLits sl rsn, l / 2 ≠ skip_var.toNat →
      sl.core.mrk[l / 2]?.getD 0#8 = 0#8 →
      (sl.core.lvl[l / 2]?.getD 0#32).toNat = sl.core.cur_level →
      ∃ m < lim, (sl.core.trl[m]?.getD 0#32).toNat / 2 = l / 2)
    (hext_sl : FullExtScratchPres s sl) (hws2_sl : sl.scratch.work_stk2 = s.scratch.work_stk2)
    (hrefs_sl : fullArenaClauseRefs sl = fullArenaClauseRefs s) :
    s2.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut s2.core ∧ FullAnaMarksCov c s2 ∧
      FullExtScratchPres s s2 ∧ s2.scratch.work_stk2 = s.scratch.work_stk2 ∧
      FullArenaVarsNodup s2 ∧ fullArenaClauseRefs s2 = fullArenaClauseRefs s ∧
      FullDeduceStaticEq s.core s2.core ∧ 1 ≤ s2.core.tmp_len ∧
      s2.core.tmp_len ≤ s2.core.cur_vars ∧
      s2.core.tmp_cnt = (fullCurTrailIdxs s2.core s2.core.mrk lim).length ∧
      FullLowerInv c s2.core s2.core.tmp s2.core.mrk s2.core.tmp_len ∧
      FullMarksCov s2.core s2.core.tmp s2.core.mrk s2.core.tmp_len ∧
      FullCurMarksBelow lim s2.core s2.core.mrk cut ∧
      s2.scratch.res_sz = BitVec.ofNat 64 ((s2.core.tmp_len - 1) + s2.core.tmp_cnt + extra) ∧
      (∀ l ∈ fullRsnLits sl rsn, l / 2 ≠ skip_var.toNat →
        0 < (s2.core.lvl[l / 2]?.getD 0#32).toNat → s2.core.mrk[l / 2]?.getD 0#8 ≠ 0#8) := by
  rcases hs2_c with ⟨hcv2, hcl2, hte2, htrl2, hlvl2, hrs2, hvals2, hfu2, hdm2, hlm2⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hlen_l.core_ok.cur_vars_le
  have hstat2 : FullDeduceStaticEq s.core s2.core :=
    hstat_l.trans ⟨hcv2, hcl2, hte2, htrl2, hlvl2, hrs2, hvals2, hfu2, hdm2, hlm2⟩
  have htl2_ge1 : 1 ≤ s2.core.tmp_len := Nat.le_trans htl_ge htl2_ge
  have hlow2 : FullLowerInv c s2.core s2.core.tmp s2.core.mrk s2.core.tmp_len := by
    unfold FullLowerInv
    rw [hcv2, hvals2, hlvl2, hcl2]
    refine ⟨fun j hj1 hj2 => ?_, fun j1 j2 hj1 hj12 hj2 => ?_⟩
    · by_cases hja : j < sl.core.tmp_len
      · have hj_t := hlow_l.1 j hj1 hja
        have hltp : s2.core.tmp[j]?.getD 0#32 = sl.core.tmp[j]?.getD 0#32 := by rw [htp j hja]
        rw [hltp]; refine ⟨hj_t.1, hj_t.2.1, hj_t.2.2.1, hj_t.2.2.2.1, ?_⟩
        rw [hmp _ (by omega) hj_t.2.2.2.2]; exact hj_t.2.2.2.2
      · obtain ⟨hlm, hlt, hne, _, hp, hlv, hmnz⟩ := hnt j (by omega) hj2
        exact ⟨hlt, hrsn_fals _ hlm hne, hp, hlv, hmnz⟩
    · by_cases hj2a : j2 < sl.core.tmp_len
      · have h1 := htp j1 (by omega); have h2 := htp j2 hj2a
        have h12 := hlow_l.2 j1 j2 hj1 hj12 hj2a
        rwa [← h1, ← h2] at h12
      · by_cases hj1a : j1 < sl.core.tmp_len
        · have hj1_m := (hlow_l.1 j1 hj1 hj1a).2.2.2.2
          have hj1_p := htp j1 hj1a
          have hj2_nt := hnt j2 (by omega) hj2
          intro heq; rw [hj1_p] at heq; rw [heq] at hj1_m; exact absurd hj2_nt.2.2.2.1 hj1_m
        · exact hnd_j j1 j2 (by omega) hj12 hj2
  have hmcov2 : FullMarksCov s2.core s2.core.tmp s2.core.mrk s2.core.tmp_len := by
    unfold FullMarksCov
    rw [hcv2, hlvl2, hcl2]
    intro v hv hmnz
    by_cases hm0 : sl.core.mrk[v]?.getD 0#8 = 0#8
    · obtain ⟨l, hl, hdiv, _, hne, hp, hle⟩ := hnm v (by omega) hm0 hmnz
      refine ⟨hp, hle, fun hlt => ?_⟩
      obtain ⟨j, hj1, hj2, hjeq⟩ :=
        (((hok_lits l hl).2 (by rwa [hdiv])).2 (by rwa [hdiv])).2
          (by rwa [hdiv]) (by rwa [hdiv])
      exact ⟨j, by omega, hj2, hjeq.trans hdiv⟩
    · obtain ⟨hp, hle, hmem⟩ := hmcov_l v hv hm0
      refine ⟨hp, hle, fun hlt => ?_⟩
      obtain ⟨j, hj1, hj2, hjeq⟩ := hmem hlt
      exact ⟨j, hj1, Nat.lt_of_lt_of_le hj2 htl2_ge, by rw [htp j hj2, hjeq]⟩
  have hcm2 : FullCurMarksBelow lim s2.core s2.core.mrk cut := by
    unfold FullCurMarksBelow
    rw [htrl2, hlvl2, hcl2]
    intro j hj hmnz hlev
    have hj_te : j < sl.core.trail_end := Nat.lt_of_lt_of_le hj hlim
    by_cases hm0 : sl.core.mrk[(sl.core.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8
    · have hv := hw_l.trail_lits_lt j hj_te
      obtain ⟨l, hl, hdiv, _, hne, _, _⟩ := hnm _ (by omega) hm0 hmnz
      obtain ⟨m, hm_lim, hm_div⟩ :=
        hcur_tr l hl (by rwa [hdiv]) (by rwa [hdiv]) (by rw [hdiv, hlev])
      have hjeq := hw_l.trail_vars_nodup j m hj_te (Nat.lt_of_lt_of_le hm_lim hlim)
        (by rw [hm_div, hdiv])
      omega
    · exact hcm_l j hj hm0 hlev
  have htc_res := ded_rsn_counts_eq hlen_l.core_ok hw_l htl_ge htl_cv
    (extra := extra) (res' := s2.scratch.res_sz) (lits := fullRsnLits sl rsn)
    (by rw [hlen2.core_ok.tmp_len_arr]; exact Nat.le_trans htl2_cv hcv_le)
    htl2_ge htl2_cv htc_eq hlim hcnt htc2_ge
    (by have h := hres2; rw [hres_l] at h; exact h)
    hnm hnt hnd_j hok_lits hmp hcur_tr ⟨htrl2, hlvl2, hcl2⟩
  refine ⟨hlen2, hw2, hcov2, fullExtScratchPres_trans hext_sl hext2,
    hws2_2.trans hws2_sl, hnd2, hrefs2.trans hrefs_sl, hstat2, htl2_ge1,
    by rw [hcv2]; exact htl2_cv, htc_res.1, hlow2, hmcov2, hcm2, htc_res.2, fun l hl hne hp => ?_⟩
  rw [hlvl2] at hp
  exact ((hok_lits l hl).2 hne).1 hp

theorem ded_rsn_lit_resolved_or_falsified {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut lim : Nat} {s2 : FullState} {lits : List Nat}
    {skip_var : BitVec 32}
    (hw2 : FullWitnessCutInv c F0 F_cur cut s2.core)
    (hlow2 : FullLowerInv c s2.core s2.core.tmp s2.core.mrk s2.core.tmp_len)
    (hmcov2 : FullMarksCov s2.core s2.core.tmp s2.core.mrk s2.core.tmp_len)
    (htl_len : s2.core.tmp_len ≤ s2.core.tmp.length)
    (hlit_lt : ∀ l ∈ lits, l / 2 < s2.core.cur_vars)
    (hlit_mem : ∀ l ∈ lits, l / 2 ≠ skip_var.toNat →
      s2.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        ((s2.core.lvl[l / 2]?.getD 0#32).toNat = s2.core.cur_level →
          ∃ m < lim, (s2.core.trl[m]?.getD 0#32).toNat = l ^^^ 1))
    (hall_mrk : ∀ l ∈ lits, l / 2 ≠ skip_var.toNat →
      0 < (s2.core.lvl[l / 2]?.getD 0#32).toNat → s2.core.mrk[l / 2]?.getD 0#8 ≠ 0#8)
    (_hlim : lim ≤ s2.core.trail_end) :
    ∀ l ∈ lits, l / 2 ≠ skip_var.toNat →
      l ∈ fullActiveResolvent s2.core s2.core.tmp s2.core.mrk s2.core.tmp_len lim ∨
        (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1]) := by
  intro l hl hne
  have hl_div : l / 2 < s2.core.cur_vars := hlit_lt l hl
  have hlt : l < 2 * s2.core.cur_vars := by omega
  obtain ⟨hf, htr⟩ := hlit_mem l hl hne
  rcases Nat.eq_zero_or_pos (s2.core.lvl[l / 2]?.getD 0#32).toNat with h0 | hpos
  · right
    obtain ⟨m, hm, hmeq⟩ := (hw2.vals_false_iff l hlt).mp hf
    have hs := hw2.level0_sound m hm (by rwa [hmeq, ded_lit_xor1_div2])
    rwa [hmeq] at hs
  · left; unfold fullActiveResolvent; rw [List.mem_append]
    have hm_nz := hall_mrk l hl hne hpos
    have hcov := hmcov2 (l / 2) hl_div hm_nz
    rcases Nat.lt_or_eq_of_le hcov.2.1 with hlt_lv | heq_lv
    · right
      obtain ⟨j, hj1, hj2, hjeq⟩ := hcov.2.2 hlt_lv
      refine (fullLowerLits_mem_iff htl_len).mpr ⟨j, hj1, hj2, ?_⟩
      have hlj := hlow2.1 j hj1 hj2
      exact ded_lit_eq_of_div2_eq_falsified hw2.toFullOtfsWitnessInv
        hlj.1 hlt hlj.2.1 hf hjeq
    · left
      obtain ⟨m, hm_lim, hmeq⟩ := htr heq_lv
      unfold fullCurLits; rw [List.mem_map]
      refine ⟨m, fullCurTrailIdxs_mem_iff.mpr ⟨hm_lim, ?_, ?_⟩, ?_⟩
      · rwa [hmeq, ded_lit_xor1_div2]
      · rwa [hmeq, ded_lit_xor1_div2]
      · rw [hmeq, ded_lit_xor1_xor1]

theorem deduce_seed_rsn_pre {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat}
    {sl : FullState}
    (hlen : sl.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut sl.core)
    (hconfl : FullConflictOkCut F_cur cut sl) (hnbin : sl.core.confl_type ≠ 1#64) :
    let rsn := sl.core.confl_ref.truncate 32
    sl.core.confl_type = 2#64 ∧ sl.core.confl_ref.toNat + 3 ≤ sl.core.arena_len ∧
      rsn.toNat = sl.core.confl_ref.toNat ∧ rsn ≠ 0xFFFFFFFF#32 ∧
      rsn &&& 0x80000000#32 = 0#32 ∧ rsn.toNat ∈ fullArenaClauseRefs sl ∧
      fullRsnLits sl rsn = fullArenaClauseLits sl sl.core.confl_ref.toNat := by
  have hcok : sl.core.confl_type = 2#64 ∧
      sl.core.confl_ref.toNat ∈ fullArenaClauseRefs sl ∧
      fullArenaClauseGarb sl sl.core.confl_ref.toNat = false ∧
      (∀ l ∈ fullArenaClauseLits sl sl.core.confl_ref.toNat,
        sl.core.vals[l]?.getD 0#8 = 0xFF#8) := by
    rcases hconfl.1 with h1 | h2
    · exact absurd h1.1 hnbin
    · exact h2
  have href := hw.arena.refs_wf _ hcok.2.1
  have hare := hlen.core_ok.arena_len_le
  have hcap := c.harena; unfold dimacsBound at hcap
  obtain ⟨htr, hne, hmask⟩ := bv64_confl_ref_u32 (r := sl.core.confl_ref) (by omega)
  have hlits : fullRsnLits sl (sl.core.confl_ref.truncate 32) =
      fullArenaClauseLits sl sl.core.confl_ref.toNat := by
    unfold fullRsnLits
    rw [ite_eq_right hne, ite_eq_right (fun h => h hmask), htr]
  exact ⟨hcok.1, href.1, htr, hne, hmask, by rw [htr]; exact hcok.2.1, hlits⟩

theorem deduce_loop_rsn_pre {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut idx' : Nat}
    {s1 : FullState}
    (hw1 : FullWitnessCutInv c F0 F_cur cut s1.core)
    (hcm1 : FullCurMarksBelow (idx' + 1) s1.core s1.core.mrk cut)
    (_hidx_te : idx' < s1.core.trail_end)
    (hm_p : s1.core.mrk[(s1.core.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8)
    (hl_p : (s1.core.lvl[(s1.core.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
      s1.core.cur_level) :
    let p_bv := s1.core.trl[idx']?.getD 0#32
    let rsn := s1.core.rsns[p_bv.toNat / 2]?.getD 0xFFFFFFFF#32
    idx' < cut ∧ (rsn ≠ 0xFFFFFFFF#32 → rsn &&& 0x80000000#32 = 0#32 →
      rsn.toNat ∈ fullArenaClauseRefs s1) := by
  have hcut : idx' < cut := hcm1 idx' (Nat.lt_succ_self _) hm_p hl_p
  refine ⟨hcut, fun hrsn hnb => ?_⟩
  have hinv := hw1.reason_inv_cut idx' hcut hrsn
  rw [ite_eq_right (fun h => h hnb)] at hinv
  exact hinv.1

end LeanQbe.T.Examples.Kissat.Proof.Deduce
