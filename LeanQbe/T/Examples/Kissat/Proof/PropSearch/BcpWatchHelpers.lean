/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
import LeanQbe.T.Logic.C0Step
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat BCP Watch, Arena, Unit-Assign & Flush Helpers (`Proof.PropSearch.BcpWatchHelpers`)

Canonical non-legacy helper layer for `Proof/PropSearch/` (`0` legacy imports,
`0` `@[expose]` on theorems/lemmas):
1. Pure `BitVec`, `List`, `CNF`, `FullTrailExt`/`FullTrailRsnsPres`/`FullArenaPermEq`,
   `FullConflOkW`, `WatchSliceOk`, and `FullWitnessInv` (`nw`) helpers.
2. Arena clause-swap/search/falsification lemmas and `unitAssign_preserves_fullWitness_nw`
   (including `FullTrailRsnsPres`), `full_{bin,large}_assign_nw_step`, `s13_bin_resolve`,
   and `s13_ar_swap_nw`.
3. `SplitWatchesInv`, `DelayedWatchesOk`, and delayed-watch flush layout lemmas
   (`p0_*`, `s15_*`, `fid_watches_congr`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.PropSearch

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec

/-! ## 1. BitVec, List, CNF, Conflict, `WatchSliceOk`, & `FullWitnessInv` Helpers -/

theorem bv32_sle0_eq_not_slt0 (x : BitVec 32) : (0#32).sle x = !(x.slt 0#32) := by
  simp only [BitVec.sle, BitVec.slt]
  change decide (0 ≤ x.toInt) = !decide (x.toInt < 0)
  by_cases h : x.toInt < 0 <;> simp [h, show (0 ≤ x.toInt) ↔ ¬(x.toInt < 0) by omega]

theorem bv64_sub1_toNat {f : BitVec 64} (hf : f ≠ 0#64) : (f - 1#64).toNat = f.toNat - 1 := by
  have hpos : 0 < f.toNat := Nat.pos_of_ne_zero fun h0 =>
    hf (BitVec.eq_of_toNat_eq (by simpa using h0))
  bv_omega

theorem bv64_add_toNat {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by simp [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem bv64_add2_toNat {a : BitVec 64} (h : a.toNat + 2 < 2 ^ 64) :
    (a + (2 : BitVec 64)).toNat = a.toNat + 2 := bv64_add_toNat h

theorem bv64_add3_toNat {a : BitVec 64} (h : a.toNat + 3 < 2 ^ 64) :
    (a + (3 : BitVec 64)).toNat = a.toNat + 3 := bv64_add_toNat h

theorem bv64_sub_toNat {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)]

theorem bv64_shl1_u32 (x : BitVec 32) : (x.setWidth 64 <<< 1#64).toNat = 2 * x.toNat := by
  have hx := x.isLt
  have h1 : (x.setWidth 64 <<< 1#64).toNat = ((x.setWidth 64).toNat * 2) % 2 ^ 64 := by
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [h1, bv_c0_zext32_64, Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]

theorem bv64_ofNat_toNat_lt {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem bv32_ofNat_toNat_lt {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem bv32_mask7f_flag0 (x : BitVec 32) :
    ((x &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 := by
  apply BitVec.eq_of_toNat_eq; apply Nat.eq_of_testBit_eq; intro b
  rw [BitVec.toNat_and, BitVec.toNat_and,
    show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl,
    show (0x80000000#32 : BitVec 32).toNat = 2 ^ 31 from rfl,
    show (0#32 : BitVec 32).toNat = 0 from rfl, Nat.testBit_and, Nat.testBit_and]
  by_cases hb : b = 31
  · subst hb; simp [show (2 ^ 31 - 1 : Nat).testBit 31 = false by decide,
      show (0 : Nat).testBit 31 = false by decide]
  · have h0 : (2 ^ 31 : Nat).testBit b = false := by
      rw [Nat.testBit_two_pow]; exact decide_eq_false (Ne.symm hb)
    simp [h0, Nat.testBit_eq_decide_div_mod_eq, Nat.zero_div]

theorem bv32_bin_rsn_props {x : BitVec 32} (hx : x.toNat < 2 ^ 31 - 1) :
    let rsn := (x &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    rsn ≠ 0xFFFFFFFF#32 ∧ (rsn &&& 0x80000000#32) ≠ 0#32 ∧
    (rsn &&& 0x7FFFFFFF#32).toNat = x.toNat := by
  have hx_lt : x.toNat < 2 ^ 31 := by omega
  have hm : (x &&& 0x7FFFFFFF#32).toNat = x.toNat := by
    rw [BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx_lt]
  have hr : ((x &&& 0x7FFFFFFF#32) ||| 0x80000000#32).toNat = x.toNat + 2 ^ 31 := by
    rw [BitVec.toNat_or, show (0x80000000#32 : BitVec 32).toNat = 2 ^ 31 from rfl, hm]
    apply Nat.eq_of_testBit_eq; intro b
    simp only [Nat.testBit_or]
    rcases Nat.lt_trichotomy b 31 with hb | rfl | hb
    · have hpow : 2 ^ 31 = 2 ^ b * (2 * 2 ^ (30 - b)) := by
        rw [show 31 = b + (1 + (30 - b)) by omega, Nat.pow_add, Nat.pow_add, Nat.pow_one]
      have htb2 : (2 ^ 31 : Nat).testBit b = false := by
        rw [Nat.testBit_two_pow]; exact decide_eq_false (by omega)
      rw [htb2, Bool.or_false, Nat.testBit_eq_decide_div_mod_eq,
        Nat.testBit_eq_decide_div_mod_eq, hpow,
        Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide))]
      congr 2; omega
    · simp [Nat.testBit_eq_decide_div_mod_eq, show x.toNat / 2 ^ 31 = 0 by omega,
        show (x.toNat + 2 ^ 31) / 2 ^ 31 = 1 by omega]
    · have h2b : 2 ^ 32 ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) (by omega)
      have htb2 : (2 ^ 31 : Nat).testBit b = false := by
        rw [Nat.testBit_two_pow]; exact decide_eq_false (by omega)
      have h231 : 2 ^ 31 < 2 ^ 32 := by decide
      rw [htb2, Bool.or_false, Nat.testBit_lt_two_pow (by omega),
        Nat.testBit_lt_two_pow (by omega)]
  refine ⟨?_, ?_, ?_⟩
  · intro heq; have h1 := congrArg BitVec.toNat heq; rw [hr] at h1
    change x.toNat + 2 ^ 31 = 2 ^ 32 - 1 at h1; omega
  · intro heq; have h1 := congrArg (·[31]) heq
    have h31 : ((x &&& 0x7FFFFFFF#32) ||| 0x80000000#32)[31] = true := by
      rw [BitVec.getElem_eq_testBit_toNat, hr, Nat.testBit_eq_decide_div_mod_eq]
      simp [show (x.toNat + 2 ^ 31) / 2 ^ 31 = 1 by omega]
    have h80 : (0x80000000#32 : BitVec 32)[31] = true := by
      rw [BitVec.getElem_eq_testBit_toNat]; decide
    simp [BitVec.getElem_and, h31, h80] at h1
  · rw [BitVec.toNat_and, hr, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    change (x.toNat + 2 ^ 31) % 2 ^ 31 = x.toNat; omega

theorem full_i8_vals_slt0 {v : BitVec 8} (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) :
    (v.signExtend 32).slt 0#32 = true ↔ v = 0xFF#8 := by
  rcases hdom with rfl | rfl | rfl <;> decide

theorem i8_vals_eq0_of_not_pos_neg {v : BitVec 8} (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (h1 : (0#32).slt (v.signExtend 32) = false) (h2 : (v.signExtend 32).slt 0#32 = false) :
    v = 0#8 := by
  rcases hdom with rfl | rfl | rfl
  · rfl
  · simp at h1
  · simp at h2

theorem i8_vals_ne_of_slt_false {v1 v2 : BitVec 8}
    (_hdom1 : v1 = 0#8 ∨ v1 = 1#8 ∨ v1 = 0xFF#8)
    (hs1 : (0#32).slt (v1.signExtend 32) = true)
    (hs2 : (0#32).slt (v2.signExtend 32) = false) : v1 ≠ v2 := by
  intro heq; subst heq; simp_all

theorem cnfClause_swap2 {F0 : CNF Nat} {a b : Nat}
    (h : F0.EntailsClause (cnfClause [a, b])) : F0.EntailsClause (cnfClause [b, a]) := by
  rw [CNF.entails_clause_def] at h ⊢
  intro α hα; obtain ⟨l, hl, hsat⟩ := (clause_sat_cnfClause_iff α [a, b]).mp (h α hα)
  apply (clause_sat_cnfClause_iff α [b, a]).mpr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
  rcases hl with rfl | rfl
  · exact ⟨l, Or.inr rfl, hsat⟩
  · exact ⟨l, Or.inl rfl, hsat⟩

theorem resolve_unit_binary {F : CNF Nat} {a b : Nat}
    (hbin : F.EntailsClause (cnfClause [a, b]))
    (hunit : F.EntailsClause (cnfClause [b ^^^ 1])) :
    F.EntailsClause (cnfClause [a]) := by
  rw [CNF.entails_clause_def] at hbin hunit ⊢
  intro α hα
  obtain ⟨l, hl, hsat⟩ := (clause_sat_cnfClause_iff α [a, b]).mp (hbin α hα)
  have hu := hunit α hα
  change CNF.Clause.Sat α (cnfClause [litNeg b]) at hu
  rw [sat_cnfClause_litNeg_iff, sat_cnfClause_singleton] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · exact (sat_cnfClause_singleton α l).mpr hsat
  · exact absurd hsat hu

theorem entails_clause_resolve_unit_all {F : CNF Nat} {lits : List Nat} {u : Nat}
    (hcl : F.EntailsClause (cnfClause lits))
    (hunit : ∀ q ∈ lits, q ≠ u → F.EntailsClause (cnfClause [q ^^^ 1])) :
    F.EntailsClause (cnfClause [u]) := by
  rw [CNF.entails_clause_def] at hcl ⊢
  intro α hα
  obtain ⟨q, hq, hsat⟩ := (clause_sat_cnfClause_iff α lits).mp (hcl α hα)
  by_cases hqu : q = u
  · subst hqu; exact (sat_cnfClause_singleton α q).mpr hsat
  · have hu := (CNF.entails_clause_def.mp (hunit q hq hqu)) α hα
    change CNF.Clause.Sat α (cnfClause [litNeg q]) at hu
    rw [sat_cnfClause_litNeg_iff, sat_cnfClause_singleton] at hu
    exact absurd hsat hu

theorem fid_xor_cancel_l (a b : BitVec 32) : a ^^^ b ^^^ a = b := by
  rw [BitVec.xor_comm (a ^^^ b) a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem fid_xor_cancel_r (a b : BitVec 32) : a ^^^ b ^^^ b = a := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem list_swap_perm {α : Type} [DecidableEq α] (xs : List α) {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) :
    ((xs.set i xs[j]).set j xs[i]).Perm xs := by
  by_cases heq : i = j
  · subst heq; simp [List.set_getElem_self]
  · refine List.perm_iff_count.mpr fun a => ?_
    have hc (ys : List α) (k : Nat) (hk : k < ys.length) (v : α) :
        (ys.set k v).count a = ys.count a + (if a = v then 1 else 0) -
          (if a = ys[k] then 1 else 0) := by
      induction ys generalizing k with
      | nil => simp at hk
      | cons y ys ih =>
        cases k with
        | zero =>
          simp only [List.set_cons_zero, List.getElem_cons_zero, List.count_cons, beq_iff_eq]
          have h1 : (y = a) ↔ (a = y) := eq_comm
          have h2 : (v = a) ↔ (a = v) := eq_comm
          simp only [h1, h2]
          by_cases hay : a = y <;> by_cases hav : a = v <;> simp [hay, hav] <;> omega
        | succ k =>
          simp only [List.set_cons_succ, List.count_cons, List.getElem_cons_succ, beq_iff_eq]
          have hle : (if a = ys[k]'(by simpa using hk) then 1 else 0) ≤ ys.count a := by
            split <;> simp_all
          have := ih k (by simpa using hk); omega
    have hset1 : j < (xs.set i xs[j]).length := by simpa using hj
    have hget : (xs.set i xs[j])[j]'hset1 = xs[j] := by rw [List.getElem_set_ne heq]
    rw [hc (xs.set i xs[j]) j hset1 xs[i], hget, hc xs i hi xs[j]]
    have hi_le : (if a = xs[i] then 1 else 0) ≤ xs.count a := by split <;> simp_all
    have hj_le : (if a = xs[j] then 1 else 0) ≤ xs.count a := by split <;> simp_all
    by_cases hai : a = xs[i]
    · by_cases haj : a = xs[j]
      · rw [ite_eq_left hai, ite_eq_left haj]; omega
      · rw [ite_eq_left hai] at hi_le ⊢; rw [ite_eq_right haj]; omega
    · by_cases haj : a = xs[j]
      · rw [ite_eq_right hai]; rw [ite_eq_left haj] at hj_le ⊢; omega
      · rw [ite_eq_right hai, ite_eq_right haj]; omega

/-! ## 1.1 Canonical `FullConflOkW`, `FullTrailExt`, `FullTrailRsnsPres`, & `FullArenaPermEq` -/

/-- Weak conflict witness matching `Proof.Spec.FullConflictOkW` (`confl_type = 2#64` for large). -/
@[expose] def FullConflOkW (F_cur : List (List Nat)) (k : FullCoreState) : Prop :=
  (k.confl_type = 1#64 ∧ k.confl_lit0.toNat < 2 * k.cur_vars ∧
    k.confl_lit1.toNat < 2 * k.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [k.confl_lit0.toNat, k.confl_lit1.toNat]) ∧
    k.vals[k.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
    k.vals[k.confl_lit1.toNat]?.getD 0#8 = 0xFF#8) ∨
  (k.confl_type = 2#64 ∧ k.confl_ref.toNat ∈ fullArenaClauseRefsCore k ∧
    fullArenaClauseGarbCore k k.confl_ref.toNat = false ∧
    ∀ l ∈ fullArenaClauseLitsCore k k.confl_ref.toNat, k.vals[l]?.getD 0#8 = 0xFF#8)

theorem fullConflOkW_to_fullConflictOkW {F_cur : List (List Nat)} {s : FullState}
    (h : FullConflOkW F_cur s.core) : FullConflictOkW F_cur s := by
  rcases h with ⟨ht, h0, h1, hent, hf0, hf1⟩ | ⟨ht, hr, hng, hfals⟩
  · exact Or.inl ⟨ht, h0, h1, hf0, hf1, hent⟩
  · exact Or.inr ⟨ht, hr, hng, hfals⟩

theorem fullTrailExt_refl (k : FullCoreState) : FullTrailExt k k :=
  ⟨Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl⟩

theorem fullTrailExt_trans {k1 k2 k3 : FullCoreState}
    (h1 : FullTrailExt k1 k2) (h2 : FullTrailExt k2 k3) : FullTrailExt k1 k3 :=
  ⟨Nat.le_trans h1.1 h2.1,
   fun i hi => (h2.2.1 i (by have := h1.1; omega)).trans (h1.2.1 i hi),
   fun i hi => by
     have h2l := h2.2.2 i (by have := h1.1; omega)
     rw [h1.2.1 i hi] at h2l; exact h2l.trans (h1.2.2 i hi)⟩

theorem fullTrailExt_congr {k0 k1 k2 : FullCoreState} (h : FullTrailExt k0 k1)
    (hte : k2.trail_end = k1.trail_end) (htrl : k2.trl = k1.trl) (hlvl : k2.lvl = k1.lvl) :
    FullTrailExt k0 k2 :=
  ⟨hte.symm ▸ h.1, fun i hi => htrl ▸ h.2.1 i hi, fun i hi => hlvl ▸ h.2.2 i hi⟩

theorem fullTrailRsnsPres_refl (k : FullCoreState) : FullTrailRsnsPres k k :=
  fun _ _ => rfl

theorem fullTrailRsnsPres_trans {k1 k2 k3 : FullCoreState}
    (ht : FullTrailExt k1 k2) (h1 : FullTrailRsnsPres k1 k2) (h2 : FullTrailRsnsPres k2 k3) :
    FullTrailRsnsPres k1 k3 := fun i hi => by
  have h2r := h2 i (Nat.lt_of_lt_of_le hi ht.1)
  rw [ht.2.1 i hi] at h2r; exact h2r.trans (h1 i hi)

theorem fullTrailRsnsPres_congr {k0 k1 k2 : FullCoreState} (h : FullTrailRsnsPres k0 k1)
    (hr : k2.rsns = k1.rsns) : FullTrailRsnsPres k0 k2 :=
  fun i hi => hr ▸ h i hi

theorem fullArenaPermEq_refl (k : FullCoreState) : FullArenaPermEq k k :=
  ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩

theorem fullArenaPermEq_trans {k1 k2 k3 : FullCoreState}
    (h1 : FullArenaPermEq k1 k2) (h2 : FullArenaPermEq k2 k3) : FullArenaPermEq k1 k3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun r hr =>
    let ⟨s1, g1, p1⟩ := h1.2.2 r hr
    let ⟨s2, g2, p2⟩ := h2.2.2 r (h1.2.1.symm ▸ hr)
    ⟨s2.trans s1, g2.trans g1, p2.trans p1⟩⟩

/-! ## 1.2 `WatchSliceOk` & `withEmptyWatchesCore` `FullWitnessInv` Helpers -/

theorem watchSlice_relocate {F F' : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} (hF : (cnfOfClauses F').Entails (cnfOfClauses F))
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F k lit p rem) : WatchSliceOk F' k' lit p' rem :=
  fullWatchSlice_relocate hF hvars hsub hwstk h

theorem watchSlice_append {F_cur : List (List Nat)} {k : FullCoreState} {lit p len1 len2 : Nat}
    (h1 : WatchSliceOk F_cur k lit p len1)
    (h2 : WatchSliceOk F_cur k lit (p + len1) len2) :
    WatchSliceOk F_cur k lit p (len1 + len2) := by
  induction h1 with
  | @empty p => simpa using h2
  | @bin p rem w h0 hf hne hl he _ ih =>
    rw [show p + (rem + 1) = (p + 1) + rem by omega] at h2
    rw [show rem + 1 + len2 = (rem + len2) + 1 by omega]
    exact .bin h0 hf hne hl he (ih h2)
  | @large p rem w cr h0 h1 hf hl hr _ ih =>
    rw [show p + (rem + 2) = (p + 2) + rem by omega] at h2
    rw [show rem + 2 + len2 = (rem + len2) + 2 by omega]
    exact .large h0 h1 hf hl hr (ih h2)

theorem watchSlice_append_bin {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hpre : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F_cur k lit p rem)
    (hat : k'.wstk[p' + rem]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k'.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    WatchSliceOk F_cur k' lit p' (rem + 1) :=
  fullWatchSlice_append_bin hvars hsub hpre h hat hflag hne hlt hent

theorem watchSlice_append_large {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 cref : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hpre : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F_cur k lit p rem)
    (hat0 : k'.wstk[p' + rem]? = some w0) (hat1 : k'.wstk[p' + rem + 1]? = some cref)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hlt : cref.toNat < 0x80000000)
    (href : cref.toNat ∈ fullArenaClauseRefsCore k') :
    WatchSliceOk F_cur k' lit p' (rem + 2) :=
  fullWatchSlice_append_large hvars hsub hpre h hat0 hat1 hflag hlt href

theorem watchSlice_inv_bin {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p len : Nat} {w0 : BitVec 32}
    (h : WatchSliceOk F_cur k lit p len) (hlen : 0 < len)
    (hget : k.wstk[p]? = some w0) (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) :
    (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
    WatchSliceOk F_cur k lit (p + 1) (len - 1) := by
  cases h with
  | empty => omega
  | bin h0 _ _ hlt hent hrest =>
    have hw := Option.some.inj (h0.symm.trans hget); subst hw
    exact ⟨hlt, hent, by simpa using hrest⟩
  | large h0 _ hf _ _ _ =>
    have hw := Option.some.inj (h0.symm.trans hget); subst hw; exact absurd hf hflag

theorem watchSlice_inv_large {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p len : Nat} {w0 : BitVec 32}
    (h : WatchSliceOk F_cur k lit p len) (hlen : 0 < len)
    (hget : k.wstk[p]? = some w0) (hflag : (w0 &&& 0x80000000#32) = 0#32) :
    2 ≤ len ∧
    ∃ cref : BitVec 32, k.wstk[p + 1]? = some cref ∧
      cref.toNat < 0x80000000 ∧ cref.toNat ∈ fullArenaClauseRefsCore k ∧
      WatchSliceOk F_cur k lit (p + 2) (len - 2) := by
  cases h with
  | empty => omega
  | bin h0 hf _ _ _ _ =>
    have hw := Option.some.inj (h0.symm.trans hget); subst hw; exact absurd hflag hf
  | large h0 h1 _ hlt href hrest =>
    exact ⟨by omega, _, h1, hlt, href, by simpa using hrest⟩

theorem watchesInv_with_wstk {F_cur : List (List Nat)} {k k' : FullCoreState}
    (h : WatchesInv F_cur k) (hvars : k'.cur_vars = k.cur_vars)
    (hw : k'.wvec = k.wvec) (hs : k'.wstk = k.wstk) (hl : k'.wlen = k.wlen)
    (ha : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k') :
    WatchesInv F_cur k' := by
  refine ⟨h.layout.with_wstk hvars hw hs hl, fun l hl' => ?_⟩
  simpa [fullWatchOffCore, fullWatchSizeCore, hw] using
    (h.slices l (hvars ▸ hl')).mono (by rw [CNF.entails_def]; exact fun _ p => p)
      (by omega) ha (fun _ _ _ => by simp [hs])

/-- Clear watches on `FullCoreState` while preserving all non-watch invariants mid-compaction. -/
@[expose] def withEmptyWatchesCore (c : FullCfg) (k : FullCoreState) : FullCoreState :=
  { k with wvec := List.replicate (4 * c.max_vars) 0#32, wlen := 0, dense_mode := 0#64 }

private theorem wew_cur_vars (c : FullCfg) (k : FullCoreState) :
    (withEmptyWatchesCore c k).cur_vars = k.cur_vars := rfl
private theorem wew_arena_len (c : FullCfg) (k : FullCoreState) :
    (withEmptyWatchesCore c k).arena_len = k.arena_len := rfl
private theorem wew_arena (c : FullCfg) (k : FullCoreState) :
    (withEmptyWatchesCore c k).arena = k.arena := rfl
private theorem wew_trail_end (c : FullCfg) (k : FullCoreState) :
    (withEmptyWatchesCore c k).trail_end = k.trail_end := rfl
private theorem wew_cur_level (c : FullCfg) (k : FullCoreState) :
    (withEmptyWatchesCore c k).cur_level = k.cur_level := rfl
private theorem wew_lvl (c : FullCfg) (k : FullCoreState) :
    (withEmptyWatchesCore c k).lvl = k.lvl := rfl
private theorem wew_rsns (c : FullCfg) (k : FullCoreState) :
    (withEmptyWatchesCore c k).rsns = k.rsns := rfl
private theorem wew_trl (c : FullCfg) (k : FullCoreState) :
    (withEmptyWatchesCore c k).trl = k.trl := rfl
private theorem wew_trail_pos (c : FullCfg) (k : FullCoreState) :
    (withEmptyWatchesCore c k).trail_pos = k.trail_pos := rfl
private theorem wew_frame_trail (c : FullCfg) (k : FullCoreState) :
    (withEmptyWatchesCore c k).frame_trail = k.frame_trail := rfl
private theorem wew_refs (c : FullCfg) (k : FullCoreState) :
    fullArenaClauseRefsCore (withEmptyWatchesCore c k) = fullArenaClauseRefsCore k := rfl
private theorem wew_sz (c : FullCfg) (k : FullCoreState) (r : Nat) :
    fullArenaClauseSizeCore (withEmptyWatchesCore c k) r = fullArenaClauseSizeCore k r := rfl
private theorem wew_garb (c : FullCfg) (k : FullCoreState) (r : Nat) :
    fullArenaClauseGarbCore (withEmptyWatchesCore c k) r = fullArenaClauseGarbCore k r := rfl
private theorem wew_lits (c : FullCfg) (k : FullCoreState) (r : Nat) :
    fullArenaClauseLitsCore (withEmptyWatchesCore c k) r = fullArenaClauseLitsCore k r := rfl

attribute [local simp] wew_cur_vars wew_arena_len wew_arena wew_trail_end wew_cur_level
  wew_lvl wew_rsns wew_trl wew_trail_pos wew_frame_trail wew_refs wew_sz wew_garb wew_lits

private theorem nw_refs_wf {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k))
    {cref : Nat} (href : cref ∈ fullArenaClauseRefsCore k) :
    cref + 3 ≤ k.arena_len ∧ 3 ≤ fullArenaClauseSizeCore k cref ∧
    cref + 3 + fullArenaClauseSizeCore k cref ≤ fullArenaNextOff k.arena k.arena_len cref ∧
    fullArenaNextOff k.arena k.arena_len cref ≤ k.arena_len :=
  let ⟨h1, h2, h3, h4, _⟩ := hnw.arena.refs_wf cref href
  ⟨h1, h2, h3, h4⟩

theorem fullWatchesInv_empty (c : FullCfg) (F_cur : List (List Nat)) (k : FullCoreState)
    (hcv : k.cur_vars ≤ c.max_vars) :
    ModeWatchesInv F_cur (withEmptyWatchesCore c k) := by
  have hw0 : ∀ l < 2 * k.cur_vars,
      fullWatchOffCore (withEmptyWatchesCore c k) l = 0 ∧
      fullWatchSizeCore (withEmptyWatchesCore c k) l = 0 := fun l hl => by
    unfold fullWatchOffCore fullWatchSizeCore withEmptyWatchesCore
    simp [show 2 * l < 4 * c.max_vars by omega, show 2 * l + 1 < 4 * c.max_vars by omega]
  simp only [ModeWatchesInv, withEmptyWatchesCore, ↓reduceIte]
  refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_)
    (fun l1 _ h1 _ _ hp1 _ => ?_) (fun l hl => ?_)
  · dsimp only at hl ⊢; obtain ⟨ho, hs⟩ := hw0 l hl
    change fullWatchOffCore (withEmptyWatchesCore c k) l +
      fullWatchSizeCore (withEmptyWatchesCore c k) l ≤ 0; omega
  · dsimp only at hl; obtain ⟨_, hs⟩ := hw0 l hl
    change 0 < fullWatchSizeCore (withEmptyWatchesCore c k) l at hp; omega
  · dsimp only at h1; obtain ⟨_, hs⟩ := hw0 l1 h1
    change 0 < fullWatchSizeCore (withEmptyWatchesCore c k) l1 at hp1; omega
  · dsimp only at hl; obtain ⟨ho, hs⟩ := hw0 l hl
    change WatchSliceOk F_cur (withEmptyWatchesCore c k) l
      (fullWatchOffCore (withEmptyWatchesCore c k) l)
      (fullWatchSizeCore (withEmptyWatchesCore c k) l)
    rw [ho, hs]; exact .empty

theorem fullWitnessInv_to_nw {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hcv : k.cur_vars ≤ c.max_vars) (hw : FullWitnessInv c F0 F_cur k) :
    FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k) :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := fullWatchesInv_empty c F_cur k hcv }

theorem fullWitnessInv_of_nw {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k))
    (hdm : k.dense_mode = 0#64) (hwat : WatchesInv F_cur k) :
    FullWitnessInv c F0 F_cur k :=
  { hnw with
    arena := { hnw.arena with len_ok := hnw.arena.len_ok }
    watches := by simp only [ModeWatchesInv, hdm, ↓reduceIte]; exact hwat }

theorem fullWitnessInv_nw_congr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k k' : FullCoreState} (hcv' : k'.cur_vars ≤ c.max_vars)
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k))
    (hcv : k'.cur_vars = k.cur_vars) (hinc : k'.inconsistent = k.inconsistent)
    (hal : k'.arena_len = k.arena_len) (har : k'.arena = k.arena)
    (hte : k'.trail_end = k.trail_end) (hcl : k'.cur_level = k.cur_level)
    (hv : k'.vals = k.vals) (hl : k'.lvl = k.lvl) (hr : k'.rsns = k.rsns)
    (ht : k'.trl = k.trl) (htp : k'.trail_pos = k.trail_pos)
    (hft : k'.frame_trail = k.frame_trail) (hfd : k'.frame_dec = k.frame_dec) :
    FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k') := by
  have href : fullArenaClauseRefsCore (withEmptyWatchesCore c k') =
      fullArenaClauseRefsCore (withEmptyWatchesCore c k) := by
    unfold fullArenaClauseRefsCore withEmptyWatchesCore; rw [hal, har]
  have hsz : ∀ r, fullArenaClauseSizeCore (withEmptyWatchesCore c k') r =
      fullArenaClauseSizeCore (withEmptyWatchesCore c k) r := fun r => by
    unfold fullArenaClauseSizeCore withEmptyWatchesCore; rw [har]
  have hgb : ∀ r, fullArenaClauseGarbCore (withEmptyWatchesCore c k') r =
      fullArenaClauseGarbCore (withEmptyWatchesCore c k) r := fun r => by
    unfold fullArenaClauseGarbCore fullArenaHdrCore withEmptyWatchesCore; rw [har]
  have hlt : ∀ r, fullArenaClauseLitsCore (withEmptyWatchesCore c k') r =
      fullArenaClauseLitsCore (withEmptyWatchesCore c k) r := fun r => by
    unfold fullArenaClauseLitsCore withEmptyWatchesCore; rw [har]
    simp only [fullArenaClauseSizeCore]
  refine
    { ext_sound := hcv.symm ▸ hnw.ext_sound
      inconsistent_sound := fun h => hnw.inconsistent_sound (hinc ▸ h)
      arena :=
        { len_ok := hal.symm ▸ hnw.arena.len_ok
          refs_wf := fun r hmem => by
            have := hnw.arena.refs_wf r (href ▸ hmem)
            rw [hsz r]; simpa only [withEmptyWatchesCore, hal, har] using this
          shrk_term := fun r hmem hsh => by
            have hsh0 :
                (fullArenaHdrCore (withEmptyWatchesCore c k) r &&& 0x00800000#32) ≠ 0#32 := by
              simpa only [fullArenaHdrCore, withEmptyWatchesCore, har] using hsh
            obtain ⟨t, ht1, ht2, hs⟩ := hnw.arena.shrk_term r (href ▸ hmem) hsh0
            exact ⟨t, by rw [hsz r]; exact ht1, hal.symm ▸ ht2,
              by simpa only [withEmptyWatchesCore, har] using hs⟩
          lits_lt := fun r hmem hng l hlm => hcv.symm ▸
            hnw.arena.lits_lt r (href ▸ hmem) (hgb r ▸ hng) l (hlt r ▸ hlm)
          entails := fun r hmem hng => by
            rw [hlt r]; exact hnw.arena.entails r (href ▸ hmem) (hgb r ▸ hng) }
      watches := fullWatchesInv_empty c F_cur k' hcv'
      cur_level_le := by change k'.cur_level ≤ k'.trail_end; rw [hcl, hte]; exact hnw.cur_level_le
      trail_lits_lt := fun i hi => by
        change (k'.trl[i]?.getD 0#32).toNat < 2 * k'.cur_vars; rw [ht, hcv]
        exact hnw.trail_lits_lt i (hte ▸ hi)
      trail_vars_nodup := fun i j hi hj heq =>
        hnw.trail_vars_nodup i j (hte ▸ hi) (hte ▸ hj)
          (by simpa only [withEmptyWatchesCore, ht] using heq)
      vals_domain := fun l hl' => by
        simpa only [withEmptyWatchesCore, hv] using hnw.vals_domain l (hcv ▸ hl')
      vals_true_iff := fun l hl' => by
        simpa only [withEmptyWatchesCore, hv, hte, ht] using hnw.vals_true_iff l (hcv ▸ hl')
      vals_false_iff := fun l hl' => by
        simpa only [withEmptyWatchesCore, hv, hte, ht] using hnw.vals_false_iff l (hcv ▸ hl')
      lvl_le := fun i hi => by
        simpa only [withEmptyWatchesCore, hl, ht, hcl] using hnw.lvl_le i (hte ▸ hi)
      dec_earliest := fun i j hi hj hleq hdec =>
        hnw.dec_earliest i j (hte ▸ hi) (hte ▸ hj)
          (by simpa only [withEmptyWatchesCore, hl, ht] using hleq)
          (by simpa only [withEmptyWatchesCore, hl, ht, hr] using hdec)
      levels_inhabited := fun L hL1 hLle => by
        simpa only [withEmptyWatchesCore, hte, hl, ht] using hnw.levels_inhabited L hL1 (hcl ▸ hLle)
      level0_sound := fun i hi hl0 => by
        simpa only [withEmptyWatchesCore, ht] using
          hnw.level0_sound i (hte ▸ hi) (by simpa only [withEmptyWatchesCore, hl, ht] using hl0)
      trail_pos_inv := fun i hi => by
        simpa only [withEmptyWatchesCore, ht, htp] using hnw.trail_pos_inv i (hte ▸ hi)
      level0_rsn_none := fun idx hidx hl0 => by
        simpa only [withEmptyWatchesCore, ht, hr] using
          hnw.level0_rsn_none idx (hte ▸ hidx)
            (by simpa only [withEmptyWatchesCore, hl, ht] using hl0)
      frame_trail_lt := fun L hL => by
        simpa only [withEmptyWatchesCore, hft, hte] using hnw.frame_trail_lt L (hcl ▸ hL)
      frame_trail_mono := fun L1 L2 h1 h2 => by
        simpa only [withEmptyWatchesCore, hft] using hnw.frame_trail_mono L1 L2 h1 (hcl ▸ h2)
      frame_trail_before_lt := fun L hL1 hLle i hi => by
        simpa only [withEmptyWatchesCore, hl, ht] using
          hnw.frame_trail_before_lt L hL1 (hcl ▸ hLle) i
            (by simpa only [withEmptyWatchesCore, hft] using hi)
      frame_dec_lt := fun L hL1 hLle => by
        simpa only [withEmptyWatchesCore, hfd, hcv] using hnw.frame_dec_lt L hL1 (hcl ▸ hLle)
      reason_inv := fun idx hidx hne => by
        dsimp only at hidx hne ⊢
        simp only [wew_trail_end, wew_trl, wew_rsns] at hidx hne
        have hri := hnw.reason_inv idx (hte ▸ hidx) (by
          simp only [wew_trl, wew_rsns, ht, hr] at hne ⊢; exact hne)
        dsimp only at hri ⊢
        split at hri <;> split
        · simp only [wew_trl, wew_rsns, wew_cur_vars, wew_lvl] at hri ⊢
          rw [ht, hr, hcv, hl]; exact hri
        · simp only [wew_trl, wew_rsns, ht, hr] at *; contradiction
        · simp only [wew_trl, wew_rsns, ht, hr] at *; contradiction
        · simp only [wew_trl, wew_rsns, wew_lvl, wew_refs, wew_garb, wew_lits] at hri ⊢
          rcases hri with ⟨hr_ref, hr_ng, hq⟩
          have href0 : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k := by
            simpa only [wew_refs] using href
          have hgb0 : ∀ r, fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := fun r => by
            simpa only [wew_garb] using hgb r
          have hlt0 : ∀ r, fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := fun r => by
            simpa only [wew_lits] using hlt r
          refine ⟨by rw [ht, hr]; exact href0 ▸ hr_ref,
            by rw [ht, hr]; exact hgb0 _ ▸ hr_ng, fun q hq_mem => ?_⟩
          rw [ht, hr, hlt0] at hq_mem
          rcases hq q hq_mem with hq_eq | ⟨m, hm, hm_eq, hm_lvl⟩
          · rw [ht]; exact Or.inl hq_eq
          · rw [ht, hl]; exact Or.inr ⟨m, hm, hm_eq, hm_lvl⟩
      reason_lit_mem := fun idx hidx hne hlg => by
        simp only [wew_trail_end, wew_trl, wew_rsns, wew_lits] at hidx hne hlg ⊢
        have hrm := hnw.reason_lit_mem idx (hte ▸ hidx)
          (by simp only [wew_trl, wew_rsns, ht, hr] at hne ⊢; exact hne)
          (by simp only [wew_trl, wew_rsns, ht, hr] at hlg ⊢; exact hlg)
        simp only [wew_trl, wew_rsns, wew_lits] at hrm
        have hlt0 : ∀ r, fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := fun r => by
          simpa only [wew_lits] using hlt r
        rw [ht, hr, hlt0]; exact hrm }

theorem fullWitnessInv_vals_zero_xor1 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) {v : Nat} (hv : v < k.cur_vars)
    (hz : k.vals[2 * v]?.getD 0#8 = 0#8) : k.vals[2 * v + 1]?.getD 0#8 = 0#8 := by
  have h1 := (hw.vals_zero_iff (by omega : 2 * v < 2 * k.cur_vars)).mp hz
  exact (hw.vals_zero_iff (by omega : 2 * v + 1 < 2 * k.cur_vars)).mpr fun i hi => by
    have := h1 i hi; omega

theorem fullWitnessInv_level0_unsat_of_conflOkW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (_hl0 : k.cur_level = 0) (hc : FullConflOkW F_cur k) : F0.Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hent, hf0, hf1⟩ | ⟨_, href, hg, hfals⟩
  · refine hw.ext_sound.2
      (unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => Or.inr ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h0lt).mp hf0
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h1lt).mp hf1
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
  · refine hw.ext_sound.2 (unsat_of_entails_nil
      (entails_of_mem_or_false (hw.arena.entails _ href hg) fun l hl => Or.inr ?_))
    obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l (hw.arena.lits_lt _ href hg l hl)).mp (hfals l hl)
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs

theorem fullWitnessInv_with_fuel_prop {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (fuel' : BitVec 64) (prop' : Nat) :
    FullWitnessInv c F0 F_cur { k with fuel := fuel', propagated := prop' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

/-! ## 2. Arena Clause Swap / Search / Falsification & Unit-Assign `nw` Helpers -/

theorem full_swapLits_preserves_nw {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hl : k.LengthsOk c)
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k)) {cref k1 k2 : Nat}
    (href : cref ∈ fullArenaClauseRefsCore k)
    (hk1 : k1 < fullArenaClauseSizeCore k cref) (hk2 : k2 < fullArenaClauseSizeCore k cref) :
    let k' : FullCoreState := { k with
      arena := (k.arena.set (cref + 3 + k1) (k.arena[cref + 3 + k2]'(by
        have hwf := nw_refs_wf hnw href
        have ha := hl.arena_len_arr; have hle := hl.arena_len_le; omega))).set (cref + 3 + k2)
        (k.arena[cref + 3 + k1]'(by
          have hwf := nw_refs_wf hnw href
          have ha := hl.arena_len_arr; have hle := hl.arena_len_le; omega)) }
    FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k') ∧ FullArenaPermEq k k' := by
  intro k'
  have hwf := nw_refs_wf hnw href
  have ha := hl.arena_len_arr; have hle := hl.arena_len_le
  have hfit : cref + 3 + fullArenaClauseSizeCore k cref ≤ k.arena_len := by omega
  have hdiff : ∀ j, j ∈ fullArenaClauseRefsCore k → j ≠ cref →
      j + 3 + fullArenaClauseSizeCore k j ≤ cref ∨
        cref + 3 + fullArenaClauseSizeCore k cref ≤ j := fun j hj hne => by
    rcases Nat.lt_trichotomy j cref with hlt | heq' | hlt
    · left; have := fullArenaScanRefs_disjoint hj href hlt
      have hwj := nw_refs_wf hnw hj; omega
    · exact absurd heq' hne
    · right; have := fullArenaScanRefs_disjoint href hj hlt; omega
  have hk'_hdr : ∀ j ∈ fullArenaClauseRefsCore k,
      k'.arena[j]? = k.arena[j]? ∧ k'.arena[j + 2]? = k.arena[j + 2]? := fun j hj => by
    have hwj := nw_refs_wf hnw hj
    by_cases heq : j = cref
    · subst heq; constructor <;>
        (dsimp only [k']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
    · have hdj := hdiff j hj heq
      constructor <;>
        (dsimp only [k']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
  have hnxt_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaNextOff k'.arena k.arena_len r = fullArenaNextOff k.arena k.arena_len r :=
    fun r hr =>
      fullArenaNextOff_congr_block (hk'_hdr r hr).1 (hk'_hdr r hr).2 fun t ht1 ht2 => by
        dsimp only [k']
        have hwr := nw_refs_wf hnw hr
        change r + 3 + fullArenaClauseSizeCore k r ≤ t at ht1
        have hne1 : t ≠ cref + 3 + k1 := by
          rcases Nat.lt_trichotomy r cref with hlt | rfl | hlt
          · have := fullArenaScanRefs_disjoint hr href hlt; omega
          · omega
          · have := fullArenaScanRefs_disjoint href hr hlt; omega
        have hne2 : t ≠ cref + 3 + k2 := by
          rcases Nat.lt_trichotomy r cref with hlt | rfl | hlt
          · have := fullArenaScanRefs_disjoint hr href hlt; omega
          · omega
          · have := fullArenaScanRefs_disjoint href hr hlt; omega
        rw [List.getElem?_set_ne hne2.symm, List.getElem?_set_ne hne1.symm]
  have har_congr : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k :=
    fullArenaClauseRefsCore_congr rfl hnxt_eq
  have hsz_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r := fun r hr => by
    unfold fullArenaClauseSizeCore; rw [(hk'_hdr r hr).2]
  have hgb_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := fun r hr => by
    unfold fullArenaClauseGarbCore fullArenaHdrCore; rw [(hk'_hdr r hr).1]
  have hperm : ∀ r ∈ fullArenaClauseRefsCore k,
      (fullArenaClauseLitsCore k' r).Perm (fullArenaClauseLitsCore k r) := fun r hr => by
    by_cases heq : r = cref
    · subst heq; unfold fullArenaClauseLitsCore; rw [hsz_eq r hr]
      let lits := (k.arena.drop (r + 3)).take (fullArenaClauseSizeCore k r)
      have hlen_drop : lits.length = fullArenaClauseSizeCore k r := by
        dsimp only [lits]; rw [List.length_take, List.length_drop]; omega
      have hdrop_eq : (k'.arena.drop (r + 3)).take (fullArenaClauseSizeCore k r) =
          (lits.set k1 (lits[k2]'(by omega))).set k2 (lits[k1]'(by omega)) := by
        apply List.ext_getElem (by simp [List.length_take, List.length_drop, k', ha]; omega)
        intro i hi1 hi2
        have hi_lt : i < fullArenaClauseSizeCore k r := by
          rw [List.length_take, List.length_drop] at hi1
          simp only [k', List.length_set] at hi1; omega
        rw [List.getElem_take, List.getElem_drop]
        by_cases hik2 : i = k2
        · subst hik2; dsimp only [k', lits]
          rw [List.getElem_set_self, List.getElem_set_self, List.getElem_take, List.getElem_drop]
        · by_cases hik1 : i = k1
          · subst hik1; dsimp only [k', lits]
            rw [List.getElem_set_ne (by omega), List.getElem_set_self,
              List.getElem_set_ne (Ne.symm hik2), List.getElem_set_self,
              List.getElem_take, List.getElem_drop]
          · simp only [k', lits]
            rw [List.getElem_set_ne (by omega), List.getElem_set_ne (by omega),
              List.getElem_set_ne (by omega), List.getElem_set_ne (by omega),
              List.getElem_take, List.getElem_drop]
      rw [hdrop_eq]; exact (list_swap_perm lits (by omega) (by omega)).map _
    · have hle_len : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena_len := by
        have hw := nw_refs_wf hnw hr; omega
      have hdj := hdiff r hr heq
      rw [fullArenaClauseLitsCore_eq_of_hold (k := k) (k' := k') (by omega)
        (by dsimp only [k']; rw [List.length_set, List.length_set, ha]; omega)
        (hsz_eq r hr) fun j hj => by
          dsimp only [k']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]]
  have hnw' : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k') :=
    { hnw with
      arena :=
        { len_ok := hnw.arena.len_ok
          refs_wf := fun r hr => by
            have hr0 : r ∈ fullArenaClauseRefsCore k := har_congr ▸ hr
            have hw0 := hnw.arena.refs_wf r hr0
            simp only [wew_arena_len, wew_arena, wew_sz] at hw0 ⊢
            rw [hsz_eq r hr0, hnxt_eq r hr0]; exact hw0
          shrk_term := fun r hr hsh => by
            have hr0 : r ∈ fullArenaClauseRefsCore k := har_congr ▸ hr
            have hsh0 : (fullArenaHdrCore (withEmptyWatchesCore c k) r &&&
                0x00800000#32) ≠ 0#32 := by
              unfold fullArenaHdrCore withEmptyWatchesCore at hsh ⊢
              rw [show k'.arena[r]? = k.arena[r]? from (hk'_hdr r hr0).1] at hsh; exact hsh
            obtain ⟨t, ht1, ht2, hs⟩ := hnw.arena.shrk_term r hr0 hsh0
            have hw0 := nw_refs_wf hnw hr0
            obtain ⟨t0, ht0_lo, _, ht0_nxt, ht0_sent⟩ := fullArenaNextOff_hits_sentinel hw0.1
              (by simpa only [fullArenaHdrCore, wew_arena] using hsh0)
              (by simpa only [wew_sz, fullArenaClauseSizeCore, wew_arena] using ht1)
              (by simpa only [wew_arena_len] using ht2)
              (by simpa only [wew_arena] using hs)
            change r + 3 + fullArenaClauseSizeCore k r ≤ t0 at ht0_lo
            have hnxt_t0 : fullArenaNextOff k.arena k.arena_len r = t0 + 1 := ht0_nxt
            have hdif : t0 ≠ cref + 3 + k1 ∧ t0 ≠ cref + 3 + k2 := by
              rcases Nat.lt_trichotomy r cref with hlt | rfl | hlt
              · have := fullArenaScanRefs_disjoint hr0 href hlt; omega
              · omega
              · have := fullArenaScanRefs_disjoint href hr0 hlt; omega
            refine ⟨t0, by simp only [wew_sz, hsz_eq r hr0]; exact ht0_lo,
              by simp only [wew_arena_len]; change t0 < k.arena_len; omega, ?_⟩
            simp only [wew_arena]; dsimp only [k']
            rw [List.getElem?_set_ne (Ne.symm hdif.2), List.getElem?_set_ne (Ne.symm hdif.1)]
            exact ht0_sent
          lits_lt := fun r hr hng l hl => by
            have hr0 : r ∈ fullArenaClauseRefsCore k := har_congr ▸ hr
            exact hnw.arena.lits_lt r hr0 ((hgb_eq r hr0).symm.trans hng) l
              ((hperm r hr0).mem_iff.mp hl)
          entails := fun r hr hng => by
            have hr0 : r ∈ fullArenaClauseRefsCore k := har_congr ▸ hr
            have hent := hnw.arena.entails r hr0 ((hgb_eq r hr0).symm.trans hng)
            rw [CNF.entails_clause_def] at hent ⊢; intro α hα
            obtain ⟨l, hl, hsat⟩ :=
              (clause_sat_cnfClause_iff α (fullArenaClauseLitsCore k r)).mp (hent α hα)
            exact (clause_sat_cnfClause_iff α _).mpr ⟨l, (hperm r hr0).mem_iff.mpr hl, hsat⟩ }
      watches := fullWatchesInv_empty c F_cur k' hl.cur_vars_le
      reason_inv := fun idx hidx hne => by
        have hri := hnw.reason_inv idx hidx hne; dsimp only at hri ⊢
        split at hri <;> split
        · simp only [wew_trl, wew_rsns, wew_cur_vars, wew_lvl] at hri ⊢; exact hri
        · simp only [wew_trl, wew_rsns] at *; contradiction
        · simp only [wew_trl, wew_rsns] at *; contradiction
        · simp only [wew_trl, wew_rsns, wew_lvl, wew_refs, wew_garb, wew_lits] at hri ⊢
          let rsn := (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat
          refine ⟨har_congr.symm ▸ hri.1, (hgb_eq rsn hri.1).trans hri.2.1, fun q hq =>
            hri.2.2 q ((hperm rsn hri.1).mem_iff.mp hq)⟩
      reason_lit_mem := fun idx hidx hne hlg => by
        have hrm := hnw.reason_lit_mem idx hidx hne hlg
        let rsn := (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat
        have hri := hnw.reason_inv idx hidx hne
        dsimp only at hri
        split at hri
        · rename_i hbf; simp only [wew_trl, wew_rsns] at hbf hlg; rw [hlg] at hbf; cases hbf rfl
        · simp only [wew_trl, wew_rsns, wew_refs, wew_lits] at hri hrm ⊢
          exact (hperm rsn hri.1).mem_iff.mpr hrm }
  exact ⟨hnw', rfl, har_congr, fun r hr => ⟨hsz_eq r hr, hgb_eq r hr, hperm r hr⟩⟩

theorem full_swapCl_preserves_nw {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hl : k.LengthsOk c)
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k)) {cref : Nat}
    (href : cref ∈ fullArenaClauseRefsCore k) :
    let k' : FullCoreState := { k with
      arena := (k.arena.set (cref + 3) (k.arena[cref + 4]'(by
        have hwf := hnw.arena.refs_wf cref href
        have ha := hl.arena_len_arr; have hle := hl.arena_len_le
        dsimp only [withEmptyWatchesCore] at hwf; omega))).set (cref + 4)
        (k.arena[cref + 3]'(by
          have hwf := hnw.arena.refs_wf cref href
          have ha := hl.arena_len_arr; have hle := hl.arena_len_le
          dsimp only [withEmptyWatchesCore] at hwf; omega)) }
    FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k') ∧ FullArenaPermEq k k' := by
  have hwf := hnw.arena.refs_wf cref href; dsimp only [withEmptyWatchesCore] at hwf
  have hsz3 : 3 ≤ fullArenaClauseSizeCore k cref := hwf.2.1
  simpa only [Nat.add_zero] using full_swapLits_preserves_nw hl hnw href (k1 := 0) (k2 := 1)
    (by omega) (by omega)

theorem full_setSrch_preserves_nw {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hl : k.LengthsOk c)
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k)) {cref : Nat} {srch : BitVec 32}
    (href : cref ∈ fullArenaClauseRefsCore k) :
    let k' : FullCoreState := { k with arena := k.arena.set (cref + 1) srch }
    FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k') ∧ FullArenaPermEq k k' := by
  intro k'
  have hwf := nw_refs_wf hnw href
  have ha := hl.arena_len_arr; have hle := hl.arena_len_le
  have hdiff : ∀ j, j ∈ fullArenaClauseRefsCore k → j ≠ cref →
      j + 3 + fullArenaClauseSizeCore k j ≤ cref ∨ cref + 3 ≤ j := fun j hj hne => by
    rcases Nat.lt_trichotomy j cref with hlt | heq' | hlt
    · left; have := fullArenaScanRefs_disjoint hj href hlt
      have hwj := nw_refs_wf hnw hj; omega
    · exact absurd heq' hne
    · right; have := fullArenaScanRefs_disjoint href hj hlt; omega
  have hk'_hdr : ∀ j ∈ fullArenaClauseRefsCore k,
      k'.arena[j]? = k.arena[j]? ∧ k'.arena[j + 2]? = k.arena[j + 2]? := fun j hj => by
    have hwj := nw_refs_wf hnw hj
    by_cases heq : j = cref
    · subst heq; constructor <;> (dsimp only [k']; rw [List.getElem?_set_ne (by omega)])
    · have hdj := hdiff j hj heq
      constructor <;> (dsimp only [k']; rw [List.getElem?_set_ne (by omega)])
  have hnxt_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaNextOff k'.arena k.arena_len r = fullArenaNextOff k.arena k.arena_len r :=
    fun r hr =>
      fullArenaNextOff_congr_block (hk'_hdr r hr).1 (hk'_hdr r hr).2 fun t ht1 ht2 => by
        dsimp only [k']
        have hwr := nw_refs_wf hnw hr
        change r + 3 + fullArenaClauseSizeCore k r ≤ t at ht1
        have hne1 : t ≠ cref + 1 := by
          rcases Nat.lt_trichotomy r cref with hlt | rfl | hlt
          · have := fullArenaScanRefs_disjoint hr href hlt; omega
          · omega
          · have := fullArenaScanRefs_disjoint href hr hlt; omega
        exact List.getElem?_set_ne hne1.symm
  have har_congr : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k :=
    fullArenaClauseRefsCore_congr rfl hnxt_eq
  have hsz_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r := fun r hr => by
    unfold fullArenaClauseSizeCore; rw [(hk'_hdr r hr).2]
  have hgb_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := fun r hr => by
    unfold fullArenaClauseGarbCore fullArenaHdrCore; rw [(hk'_hdr r hr).1]
  have hlits_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := fun r hr => by
    have hle_len : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena_len := by
      have hw := nw_refs_wf hnw hr; omega
    refine fullArenaClauseLitsCore_eq_of_hold (by omega)
      (by dsimp only [k']; rw [List.length_set, ha]; omega) (hsz_eq r hr) fun j hj => ?_
    dsimp only [k']
    by_cases heq : r = cref
    · subst heq; rw [List.getElem?_set_ne (by omega)]
    · rcases hdiff r hr heq with h | h <;> rw [List.getElem?_set_ne (by omega)]
  have hnw' : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k') :=
    { hnw with
      arena :=
        { len_ok := hnw.arena.len_ok
          refs_wf := fun r hr => by
            have hr0 : r ∈ fullArenaClauseRefsCore k := har_congr ▸ hr
            have hw0 := hnw.arena.refs_wf r hr0
            simp only [wew_arena_len, wew_arena, wew_sz] at hw0 ⊢
            rw [hsz_eq r hr0, hnxt_eq r hr0]; exact hw0
          shrk_term := fun r hr hsh => by
            have hr0 : r ∈ fullArenaClauseRefsCore k := har_congr ▸ hr
            have hsh0 : (fullArenaHdrCore (withEmptyWatchesCore c k) r &&&
                0x00800000#32) ≠ 0#32 := by
              unfold fullArenaHdrCore withEmptyWatchesCore at hsh ⊢
              rw [show k'.arena[r]? = k.arena[r]? from (hk'_hdr r hr0).1] at hsh; exact hsh
            obtain ⟨t, ht1, ht2, hs⟩ := hnw.arena.shrk_term r hr0 hsh0
            have hw0 := nw_refs_wf hnw hr0
            obtain ⟨t0, ht0_lo, _, ht0_nxt, ht0_sent⟩ := fullArenaNextOff_hits_sentinel hw0.1
              (by simpa only [fullArenaHdrCore, wew_arena] using hsh0)
              (by simpa only [wew_sz, fullArenaClauseSizeCore, wew_arena] using ht1)
              (by simpa only [wew_arena_len] using ht2)
              (by simpa only [wew_arena] using hs)
            change r + 3 + fullArenaClauseSizeCore k r ≤ t0 at ht0_lo
            have hnxt_t0 : fullArenaNextOff k.arena k.arena_len r = t0 + 1 := ht0_nxt
            have hdif : t0 ≠ cref + 1 := by
              rcases Nat.lt_trichotomy r cref with hlt | rfl | hlt
              · have := fullArenaScanRefs_disjoint hr0 href hlt; omega
              · omega
              · have := fullArenaScanRefs_disjoint href hr0 hlt; omega
            refine ⟨t0, by simp only [wew_sz, hsz_eq r hr0]; exact ht0_lo,
              by simp only [wew_arena_len]; change t0 < k.arena_len; omega, ?_⟩
            simp only [wew_arena]; dsimp only [k']
            rw [List.getElem?_set_ne (Ne.symm hdif)]; exact ht0_sent
          lits_lt := fun r hr hng l hl => by
            have hr0 : r ∈ fullArenaClauseRefsCore k := har_congr ▸ hr
            simp only [wew_lits] at hl
            rw [hlits_eq r hr0] at hl
            exact hnw.arena.lits_lt r hr0 ((hgb_eq r hr0).symm.trans hng) l hl
          entails := fun r hr hng => by
            have hr0 : r ∈ fullArenaClauseRefsCore k := har_congr ▸ hr
            simp only [wew_lits]
            rw [hlits_eq r hr0]; exact hnw.arena.entails r hr0 ((hgb_eq r hr0).symm.trans hng) }
      watches := fullWatchesInv_empty c F_cur k' hl.cur_vars_le
      reason_inv := fun idx hidx hne => by
        have hri := hnw.reason_inv idx hidx hne; dsimp only at hri ⊢
        split at hri <;> split
        · simp only [wew_trl, wew_rsns, wew_cur_vars, wew_lvl] at hri ⊢; exact hri
        · simp only [wew_trl, wew_rsns] at *; contradiction
        · simp only [wew_trl, wew_rsns] at *; contradiction
        · simp only [wew_trl, wew_rsns, wew_lvl, wew_refs, wew_garb, wew_lits] at hri ⊢
          let rsn := (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat
          refine ⟨har_congr.symm ▸ hri.1, (hgb_eq rsn hri.1).trans hri.2.1, fun q hq => by
            rw [hlits_eq rsn hri.1] at hq; exact hri.2.2 q hq⟩
      reason_lit_mem := fun idx hidx hne hlg => by
        have hrm := hnw.reason_lit_mem idx hidx hne hlg
        let rsn := (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat
        have hri := hnw.reason_inv idx hidx hne
        dsimp only at hri
        split at hri
        · rename_i hbf; simp only [wew_trl, wew_rsns] at hbf hlg; rw [hlg] at hbf; cases hbf rfl
        · simp only [wew_trl, wew_rsns, wew_refs, wew_lits] at hri hrm ⊢
          rw [hlits_eq rsn hri.1]; exact hrm }
  exact ⟨hnw', rfl, har_congr, fun r hr => ⟨hsz_eq r hr, hgb_eq r hr, hlits_eq r hr ▸ .refl _⟩⟩

/-- Predicate capturing that arena literal index `k` of clause `cref` is falsified or OOB. -/
@[expose] def fullFindReplBad (s : FullState) (cref k : Nat) : Prop :=
  2 * s.core.cur_vars ≤ (s.core.arena[cref + 3 + k]?.getD 0#32).toNat ∨
  ((s.core.vals[(s.core.arena[cref + 3 + k]?.getD 0#32).toNat]?.getD 0#8).signExtend 32).slt
    0#32 = true

theorem full_clause_falsified_of_find_repl_none {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hl : s.LengthsOk c)
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c s.core))
    {cref not_lit other : Nat}
    (href : cref ∈ fullArenaClauseRefsCore s.core)
    (hng : fullArenaClauseGarbCore s.core cref = false)
    (hnot_f : s.core.vals[not_lit]?.getD 0#8 = 0xFF#8)
    (hl0 : (s.core.arena[cref + 3]?.getD 0#32).toNat = other)
    (hl1 : (s.core.arena[cref + 4]?.getD 0#32).toNat = not_lit)
    (hbad : ∀ r, 2 ≤ r → r < fullArenaClauseSizeCore s.core cref → fullFindReplBad s cref r) :
    ∀ l ∈ fullArenaClauseLitsCore s.core cref,
      l = other ∨ s.core.vals[l]?.getD 0#8 = 0xFF#8 := by
  have hwf := nw_refs_wf hnw href
  have hfit : cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena.length := by
    have := hl.core_ok.arena_len_arr; have := hl.core_ok.arena_len_le; omega
  intro l hl_mem
  obtain ⟨j, hj, hj_eq⟩ := (mem_fullArenaClauseLitsCore_iff hfit).mp hl_mem
  have hl_lt := hnw.arena.lits_lt cref href hng l hl_mem
  rcases Nat.lt_trichotomy j 1 with hj0 | rfl | hj2
  · have : j = 0 := by omega
    subst this; left
    rw [← hj_eq, ← hl0, List.getElem?_eq_getElem (by omega), Option.getD_some]
  · right
    have heq : l = not_lit := by
      rw [← hj_eq, ← hl1, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact heq ▸ hnot_f
  · right
    have hb := hbad j hj2 hj
    unfold fullFindReplBad at hb
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hj_eq] at hb
    rcases hb with hoob | hslt
    · simp at hl_lt; omega
    · simp at hl_lt; exact (full_i8_vals_slt0 (hnw.vals_domain l hl_lt)).mp hslt

theorem unitAssign_preserves_fullWitness_nw {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hl : k.LengthsOk c)
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k)) {lit rsn alvl : BitVec 32}
    (halvl : alvl.toNat ≤ k.cur_level) (hlit : lit.toNat < 2 * k.cur_vars)
    (hun : k.vals[lit.toNat]?.getD 0#8 = 0#8)
    (hnot_l0 : alvl = 0#32 → (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]))
    (hbin : alvl ≠ 0#32 → (rsn &&& 0x80000000#32) ≠ 0#32 →
      let ot := (rsn &&& 0x7FFFFFFF#32).toNat
      ot < 2 * k.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, ot]) ∧
      ∃ m < k.trail_end, (k.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
        (k.lvl[ot / 2]?.getD 0#32).toNat ≤ alvl.toNat)
    (hlarge : alvl ≠ 0#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn ≠ 0xFFFFFFFF#32 →
      rsn.toNat ∈ fullArenaClauseRefsCore k ∧ fullArenaClauseGarbCore k rsn.toNat = false ∧
      lit.toNat ∈ fullArenaClauseLitsCore k rsn.toNat ∧
      ∀ q ∈ fullArenaClauseLitsCore k rsn.toNat,
        q = lit.toNat ∨ ∃ m < k.trail_end, (k.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
          (k.lvl[q / 2]?.getD 0#32).toNat ≤ alvl.toNat)
    (hnondec : alvl ≠ 0#32 → rsn ≠ 0xFFFFFFFF#32)
    (flags' : List (BitVec 32)) (unassigned' unflushed' : BitVec 64) :
    let v := lit.toNat / 2
    let rsn' := if alvl = 0#32 then 0xFFFFFFFF#32 else rsn
    let k_next : FullCoreState :=
      { k with
        vals := (k.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
        flags := flags', lvl := k.lvl.set v alvl, rsns := k.rsns.set v rsn'
        trl := k.trl.set k.trail_end lit
        trail_pos := k.trail_pos.set v (BitVec.ofNat 32 k.trail_end)
        trail_end := k.trail_end + 1, unassigned := unassigned', unflushed := unflushed' }
    FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k_next) ∧
    FullTrailExt k k_next ∧ FullTrailRsnsPres k k_next := by
  intro v rsn' k_next
  have hlit' : lit.toNat < 2 * (withEmptyWatchesCore c k).cur_vars := hlit
  have hun' : (withEmptyWatchesCore c k).vals[lit.toNat]?.getD 0#8 = 0#8 := hun
  have hte_lt : k.trail_end < k.cur_vars := hnw.trail_end_lt_of_unassigned hlit' hun'
  have hnot_var : ∀ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat / 2 ≠ v :=
    (hnw.vals_zero_iff hlit').mp hun'
  have hnlit_lt : (lit.toNat ^^^ 1) < 2 * k.cur_vars := litNeg_lt_two_mul hlit
  have hne_lit : lit.toNat ^^^ 1 ≠ lit.toNat := litNeg_ne_self lit.toNat
  have hv_lt : v < c.max_vars := by have := hl.cur_vars_le; omega
  have hte_max : k.trail_end < c.max_vars := by have := hl.cur_vars_le; omega
  have hte_lt32 : k.trail_end < 2 ^ 32 := by have := fullInv_max_vars_lt32 c; omega
  have htrl_get : ∀ i < k.trail_end + 1, (k_next.trl[i]?.getD 0#32).toNat =
      if i = k.trail_end then lit.toNat else (k.trl[i]?.getD 0#32).toNat := fun i _ => by
    by_cases he : i = k.trail_end
    · subst he; simp [k_next, List.getElem?_set_self (by rw [hl.trl_len]; exact hte_max)]
    · simp [k_next, he, List.getElem?_set_ne (Ne.symm he)]
  have hlvl_get : ∀ w < k.cur_vars, (k_next.lvl[w]?.getD 0#32).toNat =
      if w = v then alvl.toNat else (k.lvl[w]?.getD 0#32).toNat := fun w _ => by
    by_cases he : w = v
    · subst he; simp [k_next, List.getElem?_set_self (by rw [hl.lvl_len]; exact hv_lt)]
    · simp [k_next, he, List.getElem?_set_ne (Ne.symm he)]
  have hvals_get : ∀ l < 2 * k.cur_vars, k_next.vals[l]?.getD 0#8 =
      if l = lit.toNat ^^^ 1 then 0xFF#8 else if l = lit.toNat then 1#8
      else k.vals[l]?.getD 0#8 := fun l hl_bd => by
    have hcm := hl.cur_vars_le
    by_cases h1 : l = lit.toNat ^^^ 1
    · subst h1; dsimp only [k_next]; simp only [↓reduceIte]
      rw [List.getElem?_set_self (by simp [hl.vals_len]; omega)]; rfl
    · dsimp only [k_next]; simp only [h1, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : l = lit.toNat
      · subst h2
        have hlt_v : lit.toNat < k.vals.length := by rw [hl.vals_len]; omega
        rw [List.getElem?_set_self hlt_v]; simp
      · simp [h2, List.getElem?_set_ne (Ne.symm h2)]
  have hnodup : ∀ i j, i < k.trail_end + 1 → j < k.trail_end + 1 →
      (k_next.trl[i]?.getD 0#32).toNat / 2 = (k_next.trl[j]?.getD 0#32).toNat / 2 → i = j := by
    intro i j hi hj heq
    rw [htrl_get i hi, htrl_get j hj] at heq
    by_cases hi_e : i = k.trail_end <;> by_cases hj_e : j = k.trail_end
    · exact hi_e.trans hj_e.symm
    · simp [hi_e, hj_e] at heq; exact absurd heq.symm (hnot_var j (by omega))
    · simp [hi_e, hj_e] at heq; exact absurd heq (hnot_var i (by omega))
    · simp [hi_e, hj_e] at heq; exact hnw.trail_vars_nodup i j
        (show i < k.trail_end by omega) (show j < k.trail_end by omega) heq
  have htr_ext : FullTrailExt k k_next :=
    ⟨Nat.le_succ _,
     fun i hi => by simp only [k_next]; rw [List.getElem?_set_ne (by omega)],
     fun i hi => by
       simp only [k_next]; rw [List.getElem?_set_ne (Ne.symm (hnot_var i hi))]⟩
  have htr_rsns : FullTrailRsnsPres k k_next := fun i hi => by
    simp only [k_next]; exact List.getElem?_set_ne (Ne.symm (hnot_var i hi))
  refine ⟨?_, htr_ext, htr_rsns⟩
  refine
    { ext_sound := hnw.ext_sound, inconsistent_sound := hnw.inconsistent_sound
      arena :=
        { len_ok := hnw.arena.len_ok
          refs_wf := hnw.arena.refs_wf
          shrk_term := hnw.arena.shrk_term
          lits_lt := fun r hr hng l hl_m => by
            simpa only [wew_cur_vars] using hnw.arena.lits_lt r hr hng l hl_m
          entails := hnw.arena.entails }
      watches := fullWatchesInv_empty c F_cur k_next hl.cur_vars_le
      cur_level_le := by
        have := hnw.cur_level_le; simp only [wew_cur_level, wew_trail_end] at this ⊢
        change k.cur_level ≤ k.trail_end + 1; omega
      trail_lits_lt := fun i hi => by
        simp only [wew_trail_end, wew_trl, wew_cur_vars] at hi ⊢; dsimp only [k_next] at hi
        rw [htrl_get i hi]; split
        · exact hlit
        · exact hnw.trail_lits_lt i (show i < k.trail_end by omega)
      trail_vars_nodup := hnodup
      vals_domain := fun l hl_bd => by
        simp only [wew_cur_vars] at hl_bd
        change k_next.vals[l]?.getD 0#8 = 0#8 ∨ k_next.vals[l]?.getD 0#8 = 1#8 ∨
          k_next.vals[l]?.getD 0#8 = 0xFF#8
        rw [hvals_get l hl_bd]; split
        · exact Or.inr (Or.inr rfl)
        · split
          · exact Or.inr (Or.inl rfl)
          · exact hnw.vals_domain l hl_bd
      vals_true_iff := fun l hl_bd => by
        simp only [wew_cur_vars] at hl_bd
        change k_next.vals[l]?.getD 0#8 = 1#8 ↔
          ∃ i < k.trail_end + 1, (k_next.trl[i]?.getD 0#32).toNat = l
        rw [hvals_get l hl_bd]; constructor
        · intro h1; by_cases hn : l = lit.toNat ^^^ 1
          · simp [hn] at h1
          · simp only [hn, ↓reduceIte] at h1; by_cases hl0 : l = lit.toNat
            · exact ⟨k.trail_end, by omega, by rw [htrl_get _ (by omega)]; simp [hl0]⟩
            · simp only [hl0, ↓reduceIte] at h1
              obtain ⟨i, hi, heq⟩ := (hnw.vals_true_iff l hl_bd).mp h1
              simp only [wew_trail_end, wew_trl] at hi heq
              exact ⟨i, by omega, by
                rw [htrl_get i (by omega)]; simp [show i ≠ k.trail_end by omega, heq]⟩
        · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
          by_cases hie : i = k.trail_end
          · simp [hie] at heq; subst heq; simp [hne_lit.symm]
          · simp only [hie, ↓reduceIte] at heq
            have hne_l : l ≠ lit.toNat := fun h => by
              subst h; exact hnot_var i (by omega) (by rw [heq])
            have hne_nl : l ≠ lit.toNat ^^^ 1 := fun h => by
              subst h; exact hnot_var i (by omega) (by rw [heq, fullInv_var_xor1])
            simp only [hne_nl, hne_l, ↓reduceIte]
            exact (hnw.vals_true_iff l hl_bd).mpr ⟨i, show i < k.trail_end by omega, heq⟩
      vals_false_iff := fun l hl_bd => by
        simp only [wew_cur_vars] at hl_bd
        change k_next.vals[l]?.getD 0#8 = 0xFF#8 ↔
          ∃ i < k.trail_end + 1, (k_next.trl[i]?.getD 0#32).toNat = l ^^^ 1
        rw [hvals_get l hl_bd]; constructor
        · intro hff; by_cases hn : l = lit.toNat ^^^ 1
          · exact ⟨k.trail_end, by omega, by
              rw [htrl_get _ (by omega)]; simp [hn]; exact (litNeg_litNeg _).symm⟩
          · simp only [hn, ↓reduceIte] at hff; by_cases hl0 : l = lit.toNat
            · simp [hl0] at hff
            · simp only [hl0, ↓reduceIte] at hff
              obtain ⟨i, hi, heq⟩ := (hnw.vals_false_iff l hl_bd).mp hff
              simp only [wew_trail_end, wew_trl] at hi heq
              exact ⟨i, by omega, by
                rw [htrl_get i (by omega)]; simp [show i ≠ k.trail_end by omega, heq]⟩
        · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
          by_cases hie : i = k.trail_end
          · simp [hie] at heq
            have hln : l = lit.toNat ^^^ 1 := by rw [heq]; exact (litNeg_litNeg l).symm
            simp [hln]
          · simp only [hie, ↓reduceIte] at heq
            have hne_l : l ≠ lit.toNat := fun h => by
              subst h; exact hnot_var i (by omega) (by rw [heq, fullInv_var_xor1])
            have hne_nl : l ≠ lit.toNat ^^^ 1 := fun h => by
              subst h; exact hnot_var i (by omega) (by rw [heq, fullInv_var_xor1, fullInv_var_xor1])
            simp only [hne_nl, hne_l, ↓reduceIte]
            exact (hnw.vals_false_iff l hl_bd).mpr ⟨i, show i < k.trail_end by omega, heq⟩
      lvl_le := fun i hi => by
        simp only [wew_trail_end, wew_trl, wew_lvl, wew_cur_level] at hi ⊢
        dsimp only [k_next] at hi
        change (k_next.lvl[(k_next.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ k.cur_level
        rw [htrl_get i hi]; by_cases hie : i = k.trail_end
        · subst hie; simp only [↓reduceIte]; rw [hlvl_get v (by omega)]; simp [halvl]
        · simp only [hie, ↓reduceIte]
          have hilt : i < k.trail_end := by omega
          have hlti := hnw.trail_lits_lt i hilt; simp only [wew_trl, wew_cur_vars] at hlti
          rw [hlvl_get _ (by omega)]; simp only [hnot_var i hilt, ↓reduceIte]
          exact hnw.lvl_le i hilt
      dec_earliest := fun i j hi hj hleq hdec => by
        simp only [wew_trail_end, wew_trl, wew_lvl, wew_rsns] at hi hj hleq hdec ⊢
        dsimp only [k_next] at hi hj
        have hvj_eq : (k_next.trl[j]?.getD 0#32).toNat / 2 < k.cur_vars := by
          rw [htrl_get j hj]; split; · omega
          · have hjlt : j < k.trail_end := by omega
            have hltj := hnw.trail_lits_lt j hjlt
            simp only [wew_trl, wew_cur_vars] at hltj; omega
        by_cases hje : j = k.trail_end
        · subst hje; exfalso; rw [htrl_get k.trail_end hj] at hdec; simp only [↓reduceIte] at hdec
          have hlv0 : 0 < alvl.toNat := by
            rw [hlvl_get v (by omega)] at hdec; simp only [↓reduceIte] at hdec; exact hdec.1
          have hne0 : alvl ≠ 0#32 := fun h => by subst h; simp at hlv0
          have hrs := hdec.2; dsimp only [k_next] at hrs
          rw [List.getElem?_set_self (by rw [hl.rsns_len]; exact hv_lt)] at hrs
          simp only [rsn', hne0, ↓reduceIte] at hrs; exact hnondec hne0 hrs
        · by_cases hie : i = k.trail_end
          · omega
          · have hjlt : j < k.trail_end := by omega
            have hilt : i < k.trail_end := by omega
            have hi_ne : (k.trl[i]?.getD 0#32).toNat / 2 ≠ v := hnot_var i hilt
            have hj_ne : (k.trl[j]?.getD 0#32).toNat / 2 ≠ v := hnot_var j hjlt
            have hil := hnw.trail_lits_lt i hilt; have hjl := hnw.trail_lits_lt j hjlt
            simp only [wew_trl, wew_cur_vars] at hil hjl
            rw [htrl_get i hi] at hleq; rw [htrl_get j hj] at hleq hdec
            simp only [hie, hje, ↓reduceIte] at hleq hdec
            rw [hlvl_get _ (by omega)] at hleq; rw [hlvl_get _ (by omega)] at hleq hdec
            simp only [hi_ne, hj_ne, ↓reduceIte] at hleq hdec
            have hdec' : k_next.rsns[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
                k.rsns[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 := by
              dsimp only [k_next]; rw [List.getElem?_set_ne (Ne.symm hj_ne)]
            rw [hdec'] at hdec; exact hnw.dec_earliest i j hilt hjlt hleq hdec
      levels_inhabited := fun L hL1 hLle => by
        simp only [wew_cur_level, wew_trail_end, wew_trl, wew_lvl] at hLle ⊢
        dsimp only [k_next] at hLle ⊢
        obtain ⟨i, hi, heq⟩ := hnw.levels_inhabited L hL1 hLle
        simp only [wew_trail_end, wew_trl, wew_lvl] at hi heq
        have hlt := hnw.trail_lits_lt i hi; simp only [wew_cur_vars, wew_trl] at hlt
        refine ⟨i, by omega, ?_⟩; rw [htrl_get i (by omega)]
        simp only [show i ≠ k.trail_end by omega, ↓reduceIte]
        rw [hlvl_get _ (by omega)]; simp [hnot_var i hi, heq]
      level0_sound := fun i hi hl0 => by
        simp only [wew_trail_end, wew_trl, wew_lvl] at hi hl0 ⊢; dsimp only [k_next] at hi
        rw [htrl_get i hi] at hl0 ⊢; by_cases hie : i = k.trail_end
        · subst hie; simp only [↓reduceIte] at hl0 ⊢
          rw [hlvl_get v (by omega)] at hl0; simp only [↓reduceIte] at hl0
          exact hnot_l0 (BitVec.eq_of_toNat_eq (by simpa using hl0))
        · simp only [hie, ↓reduceIte] at hl0 ⊢; have hilt : i < k.trail_end := by omega
          have hlt := hnw.trail_lits_lt i hilt; simp only [wew_cur_vars, wew_trl] at hlt
          rw [hlvl_get _ (by omega)] at hl0
          simp only [hnot_var i hilt, ↓reduceIte] at hl0; exact hnw.level0_sound i hilt hl0
      trail_pos_inv := fun i hi => by
        simp only [wew_trail_end, wew_trl, wew_trail_pos] at hi ⊢; dsimp only [k_next] at hi
        rw [htrl_get i hi]; by_cases hie : i = k.trail_end
        · subst hie; simp only [↓reduceIte]; dsimp only [k_next]
          rw [List.getElem?_set_self (by rw [hl.trail_pos_len]; exact hv_lt)]
          exact bv32_ofNat_toNat_lt hte_lt32
        · simp only [hie, ↓reduceIte]; have hilt : i < k.trail_end := by omega
          dsimp only [k_next]; rw [List.getElem?_set_ne (Ne.symm (hnot_var i hilt))]
          exact hnw.trail_pos_inv i hilt
      level0_rsn_none := fun idx hidx hl0 => by
        simp only [wew_trail_end, wew_trl, wew_lvl, wew_rsns] at hidx hl0 ⊢
        dsimp only [k_next] at hidx
        rw [htrl_get idx hidx] at hl0 ⊢; by_cases hie : idx = k.trail_end
        · subst hie; simp only [↓reduceIte] at hl0 ⊢
          rw [hlvl_get v (by omega)] at hl0; simp only [↓reduceIte] at hl0
          have ha0 : alvl = 0#32 := BitVec.eq_of_toNat_eq (by simpa using hl0)
          dsimp only [k_next]; rw [List.getElem?_set_self (by rw [hl.rsns_len]; exact hv_lt)]
          simp [rsn', ha0]
        · simp only [hie, ↓reduceIte] at hl0 ⊢; have hilt : idx < k.trail_end := by omega
          have hlt := hnw.trail_lits_lt idx hilt; simp only [wew_cur_vars, wew_trl] at hlt
          rw [hlvl_get _ (by omega)] at hl0
          simp only [hnot_var idx hilt, ↓reduceIte] at hl0
          dsimp only [k_next]; rw [List.getElem?_set_ne (Ne.symm (hnot_var idx hilt))]
          exact hnw.level0_rsn_none idx hilt hl0
      frame_trail_lt := fun L hL => by
        have := hnw.frame_trail_lt L hL
        simp only [wew_frame_trail, wew_trail_end] at this ⊢; dsimp only [k_next]; omega
      frame_trail_mono := hnw.frame_trail_mono
      frame_trail_before_lt := fun L hL1 hLle i hi => by
        simp only [wew_cur_level, wew_frame_trail, wew_trl, wew_lvl] at hLle hi ⊢
        have hft_le := hnw.frame_trail_lt L hLle
        simp only [wew_frame_trail, wew_trail_end] at hft_le
        have hilt : i < k.trail_end := Nat.lt_of_lt_of_le hi hft_le
        rw [htrl_get i (by omega)]; simp only [show i ≠ k.trail_end by omega, ↓reduceIte]
        have hlt := hnw.trail_lits_lt i hilt; simp only [wew_cur_vars, wew_trl] at hlt
        rw [hlvl_get _ (by omega)]
        simp only [hnot_var i hilt, ↓reduceIte]; exact hnw.frame_trail_before_lt L hL1 hLle i hi
      frame_dec_lt := hnw.frame_dec_lt
      reason_inv := fun idx hidx hne => by
        dsimp only at hidx hne ⊢
        simp only [wew_trail_end, wew_trl, wew_rsns] at hidx hne; dsimp only [k_next] at hidx
        by_cases hie : idx = k.trail_end
        · subst hie
          have hp_eq : (k_next.trl[k.trail_end]?.getD 0#32).toNat = lit.toNat := by
            rw [htrl_get k.trail_end (by omega)]; simp
          have hrsn_eq : k_next.rsns[lit.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn' := by
            dsimp only [k_next]; rw [List.getElem?_set_self (by rw [hl.rsns_len]; exact hv_lt)]; rfl
          have hne' : rsn' ≠ 0xFFFFFFFF#32 := by simpa only [hp_eq, hrsn_eq] using hne
          have ha0 : alvl ≠ 0#32 := fun h => by subst h; simp [rsn'] at hne'
          have hrsn_val : rsn' = rsn := by simp [rsn', ha0]
          have hlv_v : (k_next.lvl[lit.toNat / 2]?.getD 0#32).toNat = alvl.toNat := by
            simpa only [↓reduceIte] using hlvl_get v (by omega)
          simp only [wew_trl, wew_rsns, wew_cur_vars, wew_lvl, wew_refs, wew_garb,
            wew_lits, hp_eq, hrsn_eq, hrsn_val]
          split
          · rename_i hbf
            obtain ⟨hot, hent, m, hm_lt, htrl_m, hlvl_m⟩ := hbin ha0 hbf
            refine ⟨hot, hent, m, hm_lt,
              by dsimp only [k_next]; rw [List.getElem?_set_ne (by omega)]; exact htrl_m, ?_⟩
            rw [hlv_v]; rw [hlvl_get _ (by omega)]
            have hm_var : (k.trl[m]?.getD 0#32).toNat / 2 ≠ v := hnot_var m hm_lt
            rw [htrl_m, fullInv_var_xor1] at hm_var
            simp only [hm_var, ↓reduceIte]; exact hlvl_m
          · rename_i hbf
            obtain ⟨href, hng, _, hall⟩ := hlarge ha0 (Classical.not_not.mp hbf) (hnondec ha0)
            refine ⟨href, hng, fun q hq => ?_⟩
            rcases hall q hq with rfl | ⟨m, hm_lt, htrl_m, hlvl_m⟩
            · exact Or.inl rfl
            · right; have hm_var : (k.trl[m]?.getD 0#32).toNat / 2 ≠ v := hnot_var m hm_lt
              rw [htrl_m, fullInv_var_xor1] at hm_var
              refine ⟨m, hm_lt,
                by dsimp only [k_next]; rw [List.getElem?_set_ne (by omega)]; exact htrl_m, ?_⟩
              have hq_lt := hnw.arena.lits_lt _ href hng q hq
              simp only [wew_cur_vars] at hq_lt
              rw [hlv_v, hlvl_get _ (by omega)]; simp only [hm_var, ↓reduceIte]; exact hlvl_m
        · have hilt : idx < k.trail_end := by omega
          have hp_eq : (k_next.trl[idx]?.getD 0#32).toNat = (k.trl[idx]?.getD 0#32).toNat := by
            rw [htrl_get idx hidx]; simp [hie]
          have hvar_ne : (k.trl[idx]?.getD 0#32).toNat / 2 ≠ v := hnot_var idx hilt
          have hrsn_eq : k_next.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
              k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 := by
            dsimp only [k_next]; rw [List.getElem?_set_ne (Ne.symm hvar_ne)]
          have hri := hnw.reason_inv idx hilt (by
            simpa only [wew_trl, wew_rsns, hp_eq, hrsn_eq] using hne)
          dsimp only at hri ⊢
          split at hri <;> split
          · simp only [wew_trl, wew_rsns, wew_cur_vars, wew_lvl, hp_eq, hrsn_eq] at hri ⊢
            obtain ⟨hot, hent, m, hm_lt, htrl_m, hlvl_m⟩ := hri
            have hm_var : (k.trl[m]?.getD 0#32).toNat / 2 ≠ v := hnot_var m (by omega)
            rw [htrl_m, fullInv_var_xor1] at hm_var
            refine ⟨hot, hent, m, hm_lt,
              by dsimp only [k_next]; rw [List.getElem?_set_ne (by omega)]; exact htrl_m, ?_⟩
            have hlt_p := hnw.trail_lits_lt idx hilt; simp only [wew_cur_vars, wew_trl] at hlt_p
            rw [hlvl_get _ (by omega), hlvl_get _ (by omega)]
            simp only [hm_var, hvar_ne, ↓reduceIte]; exact hlvl_m
          · simp only [wew_trl, wew_rsns, hp_eq, hrsn_eq] at *; contradiction
          · simp only [wew_trl, wew_rsns, hp_eq, hrsn_eq] at *; contradiction
          · simp only [wew_trl, wew_rsns, wew_lvl, wew_refs, wew_garb,
              wew_lits, hp_eq, hrsn_eq] at hri ⊢
            refine ⟨hri.1, hri.2.1, fun q hq => ?_⟩
            rcases hri.2.2 q hq with rfl | ⟨m, hm_lt, htrl_m, hlvl_m⟩
            · exact Or.inl rfl
            · right; have hm_var : (k.trl[m]?.getD 0#32).toNat / 2 ≠ v := hnot_var m (by omega)
              rw [htrl_m, fullInv_var_xor1] at hm_var
              refine ⟨m, hm_lt,
                by dsimp only [k_next]; rw [List.getElem?_set_ne (by omega)]; exact htrl_m, ?_⟩
              have hlt_p := hnw.trail_lits_lt idx hilt
              have hlt_q := hnw.arena.lits_lt _ hri.1 hri.2.1 q hq
              simp only [wew_cur_vars, wew_trl] at hlt_p hlt_q
              rw [hlvl_get _ (by omega), hlvl_get _ (by omega)]
              simp only [hm_var, hvar_ne, ↓reduceIte]; exact hlvl_m
      reason_lit_mem := fun idx hidx hne hlg => by
        simp only [wew_trail_end, wew_trl, wew_rsns, wew_lits] at hidx hne hlg ⊢
        dsimp only [k_next] at hidx
        by_cases hie : idx = k.trail_end
        · subst hie
          have hp_eq : (k_next.trl[k.trail_end]?.getD 0#32).toNat = lit.toNat := by
            rw [htrl_get k.trail_end (by omega)]; simp
          have hrsn_eq : k_next.rsns[v]?.getD 0xFFFFFFFF#32 = rsn' := by
            dsimp only [k_next]; rw [List.getElem?_set_self (by rw [hl.rsns_len]; exact hv_lt)]; rfl
          simp only [hp_eq] at hne hlg ⊢; change _ at hne hlg ⊢; rw [hrsn_eq] at hne hlg ⊢
          have ha0 : alvl ≠ 0#32 := fun h => by subst h; simp [rsn'] at hne
          have hrsn_val : rsn' = rsn := by simp [rsn', ha0]
          rw [hrsn_val] at hlg ⊢; exact (hlarge ha0 hlg (hnondec ha0)).2.2.1
        · have hilt : idx < k.trail_end := by omega
          have hp_eq : (k_next.trl[idx]?.getD 0#32).toNat = (k.trl[idx]?.getD 0#32).toNat := by
            rw [htrl_get idx hidx]; simp [hie]
          have hvar_ne : (k.trl[idx]?.getD 0#32).toNat / 2 ≠ v := hnot_var idx hilt
          have hrsn_eq : k_next.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
              k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 := by
            dsimp only [k_next]; rw [List.getElem?_set_ne (Ne.symm hvar_ne)]
          have hrm := hnw.reason_lit_mem idx hilt
            (by simpa only [wew_trl, wew_rsns, hp_eq, hrsn_eq] using hne)
            (by simpa only [wew_trl, wew_rsns, hp_eq, hrsn_eq] using hlg)
          simp only [wew_trl, wew_rsns, wew_lits] at hrm; rw [hp_eq, hrsn_eq]; exact hrm }

theorem full_bin_assign_nw_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hl : k.LengthsOk c)
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k)) {not_lit blk alvl : BitVec 32}
    (halvl : alvl.toNat ≤ k.cur_level) (hblk_lt : blk.toNat < 2 * k.cur_vars)
    (hun : k.vals[blk.toNat]?.getD 0#8 = 0#8)
    (hnot_lt : not_lit.toNat < 2 * k.cur_vars)
    (hnot_f : k.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [not_lit.toNat, blk.toNat]))
    (hnl_le : (k.lvl[not_lit.toNat / 2]?.getD 0#32).toNat ≤ alvl.toNat)
    (halvl_eq : alvl = 0#32 ↔ (k.lvl[not_lit.toNat / 2]?.getD 0#32) = 0#32)
    (flags' : List (BitVec 32)) (unassigned' unflushed' : BitVec 64) :
    let v := blk.toNat / 2
    let rsn0 := (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    let rsn' := if alvl = 0#32 then 0xFFFFFFFF#32 else rsn0
    let k_next : FullCoreState :=
      { k with
        vals := (k.vals.set blk.toNat 1#8).set (blk.toNat ^^^ 1) 0xFF#8
        flags := flags', lvl := k.lvl.set v alvl, rsns := k.rsns.set v rsn'
        trl := k.trl.set k.trail_end blk
        trail_pos := k.trail_pos.set v (BitVec.ofNat 32 k.trail_end)
        trail_end := k.trail_end + 1, unassigned := unassigned', unflushed := unflushed' }
    FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k_next) ∧
    FullTrailExt k k_next ∧ FullTrailRsnsPres k k_next := by
  have hnot_max : not_lit.toNat < 2 ^ 31 - 1 := by
    have hmax := c.hmaxv; unfold dimacsBound at hmax; have := hl.cur_vars_le; omega
  have hrs := bv32_bin_rsn_props hnot_max
  obtain ⟨m, hm, hm_eq⟩ := (hnw.vals_false_iff not_lit.toNat
    (by simp only [wew_cur_vars]; exact hnot_lt)).mp hnot_f
  simp only [wew_trail_end, wew_trl] at hm hm_eq
  have hent_sw := cnfClause_swap2 hent
  refine unitAssign_preserves_fullWitness_nw hl hnw halvl hblk_lt hun ?_ ?_ ?_ ?_
    flags' unassigned' unflushed'
  · intro ha0; have hnl0 : (k.lvl[not_lit.toNat / 2]?.getD 0#32) = 0#32 := halvl_eq.mp ha0
    have hlvl_m : (k.lvl[(k.trl[m]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
      rw [hm_eq, fullInv_var_xor1, hnl0]; rfl
    have hsnd := hnw.level0_sound m hm hlvl_m
    simp only [wew_trl] at hsnd; rw [hm_eq] at hsnd; exact resolve_unit_binary hent_sw hsnd
  · intro _ _; dsimp only; rw [hrs.2.2]; exact ⟨hnot_lt, hent_sw, m, hm, hm_eq, hnl_le⟩
  · intro _ h0; exact absurd h0 hrs.2.1
  · intro _; exact hrs.1

theorem full_large_assign_nw_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hl : k.LengthsOk c)
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k))
    {not_lit other cref alvl : BitVec 32} (hcr_lt : cref.toNat < 0x80000000)
    (hcref : cref.toNat ∈ fullArenaClauseRefsCore k)
    (hng : fullArenaClauseGarbCore k cref.toNat = false)
    (hother_lt : other.toNat < 2 * k.cur_vars) (hun : k.vals[other.toNat]?.getD 0#8 = 0#8)
    (_hnot_lt : not_lit.toNat < 2 * k.cur_vars)
    (_hnot_f : k.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hother_mem : other.toNat ∈ fullArenaClauseLitsCore k cref.toNat)
    (hunit : ∀ l ∈ fullArenaClauseLitsCore k cref.toNat,
      l = other.toNat ∨ k.vals[l]?.getD 0#8 = 0xFF#8)
    (hmax_ge : ∀ l ∈ fullArenaClauseLitsCore k cref.toNat, l ≠ other.toNat →
      (k.lvl[l / 2]?.getD 0#32).toNat ≤ alvl.toNat)
    (hmax_att : alvl = 0#32 ∨ ∃ l ∈ fullArenaClauseLitsCore k cref.toNat,
      l ≠ other.toNat ∧ alvl = k.lvl[l / 2]?.getD 0#32)
    (flags' : List (BitVec 32)) (unassigned' unflushed' : BitVec 64) :
    let v := other.toNat / 2
    let rsn' := if alvl = 0#32 then 0xFFFFFFFF#32 else cref
    let k_next : FullCoreState :=
      { k with
        vals := (k.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
        flags := flags', lvl := k.lvl.set v alvl, rsns := k.rsns.set v rsn'
        trl := k.trl.set k.trail_end other
        trail_pos := k.trail_pos.set v (BitVec.ofNat 32 k.trail_end)
        trail_end := k.trail_end + 1, unassigned := unassigned', unflushed := unflushed' }
    FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k_next) ∧
    FullTrailExt k k_next ∧ FullTrailRsnsPres k k_next := by
  have halvl_le : alvl.toNat ≤ k.cur_level := by
    rcases hmax_att with rfl | ⟨l, hl_mem, _, rfl⟩
    · simp
    · rcases hunit l hl_mem with rfl | hlf
      · contradiction
      · obtain ⟨i, hi, _⟩ := (hnw.vals_false_iff l (hnw.arena.lits_lt cref.toNat hcref hng l
          hl_mem)).mp hlf
        have hli := hnw.lvl_le i hi
        dsimp only [withEmptyWatchesCore] at hli; rwa [‹(k.trl[i]?.getD 0#32).toNat = l ^^^ 1›,
          fullInv_var_xor1] at hli
  have hcr_ne : cref ≠ 0xFFFFFFFF#32 := fun heq => by subst heq; revert hcr_lt; decide
  have hcr_flag0 : (cref &&& 0x80000000#32) = 0#32 := by
    apply BitVec.eq_of_toNat_eq; apply Nat.eq_of_testBit_eq; intro b
    rw [BitVec.toNat_and, show (0x80000000#32 : BitVec 32).toNat = 2 ^ 31 from rfl,
      show (0#32 : BitVec 32).toNat = 0 from rfl, Nat.testBit_and]
    by_cases hb : b = 31
    · subst hb
      simp [Nat.testBit_lt_two_pow (show cref.toNat < 2 ^ 31 from hcr_lt),
        show (0 : Nat).testBit 31 = false by decide]
    · have h0 : (2 ^ 31 : Nat).testBit b = false := by
        rw [Nat.testBit_two_pow]; exact decide_eq_false (Ne.symm hb)
      simp [h0, Nat.testBit_eq_decide_div_mod_eq, Nat.zero_div]
  refine unitAssign_preserves_fullWitness_nw hl hnw halvl_le hother_lt hun ?_ ?_ ?_ ?_
    flags' unassigned' unflushed'
  · intro ha0
    have hent := hnw.arena.entails cref.toNat hcref hng
    refine entails_clause_resolve_unit_all hent fun l hl_mem hne => ?_
    rcases hunit l hl_mem with rfl | hlf
    · contradiction
    · obtain ⟨i, hi, hi_eq⟩ := (hnw.vals_false_iff l (hnw.arena.lits_lt cref.toNat hcref hng l
          hl_mem)).mp hlf
      simp only [wew_trail_end, wew_trl] at hi hi_eq
      have hll : (k.lvl[l / 2]?.getD 0#32).toNat = 0 := by
        have := hmax_ge l hl_mem hne; rw [ha0] at this; simp at this; exact this
      have hsnd := hnw.level0_sound i hi
        (by simp only [wew_trl, wew_lvl]; rw [hi_eq, fullInv_var_xor1]; exact hll)
      simp only [wew_trl] at hsnd; rw [hi_eq] at hsnd; exact hsnd
  · intro _ hbf; exact absurd hcr_flag0 hbf
  · intro _ _ _; refine ⟨hcref, hng, hother_mem, fun q hq => ?_⟩
    rcases hunit q hq with rfl | hqf
    · exact Or.inl rfl
    · right; obtain ⟨m, hm, hm_eq⟩ := (hnw.vals_false_iff q (hnw.arena.lits_lt cref.toNat
          hcref hng q hq)).mp hqf
      exact ⟨m, hm, hm_eq, hmax_ge q hq fun hq_o => by subst hq_o; simp [hqf] at hun⟩
  · intro _; exact hcr_ne

theorem s13_bin_resolve {F : CNF Nat} {not_lit ot blk : Nat}
    (h1 : F.EntailsClause (cnfClause [ot, blk]))
    (h2 : F.EntailsClause (cnfClause [not_lit, ot ^^^ 1])) :
    F.EntailsClause (cnfClause [not_lit, blk]) := by
  rw [CNF.entails_clause_def] at h1 h2 ⊢
  intro α hα
  obtain ⟨l1, hl1, hs1⟩ := (clause_sat_cnfClause_iff α [ot, blk]).mp (h1 α hα)
  obtain ⟨l2, hl2, hs2⟩ := (clause_sat_cnfClause_iff α [not_lit, ot ^^^ 1]).mp (h2 α hα)
  apply (clause_sat_cnfClause_iff α [not_lit, blk]).mpr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl1 hl2 ⊢
  rcases hl1 with rfl | rfl
  · rcases hl2 with rfl | rfl
    · exact ⟨l2, Or.inl rfl, hs2⟩
    · have hu : CNF.Clause.Sat α (cnfClause [litNeg l1]) :=
        (sat_cnfClause_singleton α (litNeg l1)).mpr hs2
      rw [sat_cnfClause_litNeg_iff, sat_cnfClause_singleton] at hu
      exact absurd hs1 hu
  · exact ⟨l1, Or.inr rfl, hs1⟩

theorem s13_ar_swap_nw {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hl : k.LengthsOk c)
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k)) {cref ri : Nat}
    {srch l1 repl : BitVec 32} (hcref : cref ∈ fullArenaClauseRefsCore k)
    (hsz3 : 3 ≤ fullArenaClauseSizeCore k cref)
    (hfit : cref + 3 + fullArenaClauseSizeCore k cref ≤ k.arena_len)
    (hri2 : 2 ≤ ri) (hri_lt : ri < fullArenaClauseSizeCore k cref)
    (hl1 : k.arena[cref + 4]? = some l1)
    (hrepl : k.arena[cref + 3 + ri]? = some repl) :
    let k' : FullCoreState :=
      { k with arena := ((k.arena.set (cref + 1) srch).set (cref + 4) repl).set (cref + 3 + ri) l1 }
    FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k') ∧ FullArenaPermEq k k' ∧
    k'.arena[cref + 4]? = some repl ∧ k'.arena[cref + 3 + ri]? = some l1 := by
  intro k'
  have ha := hl.arena_len_arr; have hle := hl.arena_len_le
  have ⟨hnw1, hperm1⟩ := full_setSrch_preserves_nw hl hnw (srch := srch) hcref
  let k1 : FullCoreState := { k with arena := k.arena.set (cref + 1) srch }
  have hl1_k1 : k1.LengthsOk c := { hl with arena_len_arr := by simp [k1, ha] }
  have hcref1 : cref ∈ fullArenaClauseRefsCore k1 := hperm1.2.1.symm ▸ hcref
  have hk1_sz : fullArenaClauseSizeCore k1 cref = fullArenaClauseSizeCore k cref :=
    (hperm1.2.2 _ hcref).1
  have h1_4 : k1.arena[cref + 3 + 1]'(by simp [k1, ha]; omega) = l1 := by
    have : k1.arena[cref + 4]? = some l1 := by
      simp only [k1]; rw [List.getElem?_set_ne (by omega)]; exact hl1
    rw [List.getElem?_eq_getElem (by simp [k1, ha]; omega)] at this
    exact Option.some.inj this
  have h1_ri : k1.arena[cref + 3 + ri]'(by simp [k1, ha]; omega) = repl := by
    have : k1.arena[cref + 3 + ri]? = some repl := by
      simp only [k1]; rw [List.getElem?_set_ne (by omega)]; exact hrepl
    rw [List.getElem?_eq_getElem (by simp [k1, ha]; omega)] at this
    exact Option.some.inj this
  have ⟨hnw2, hperm2⟩ := full_swapLits_preserves_nw hl1_k1 hnw1 hcref1 (k1 := 1) (k2 := ri)
    (by omega) (by omega)
  let ar2 := (k1.arena.set (cref + 3 + 1) (k1.arena[cref + 3 + ri]'(by simp [k1, ha]; omega))).set
    (cref + 3 + ri) (k1.arena[cref + 3 + 1]'(by simp [k1, ha]; omega))
  have hk'_eq : k' = { k1 with arena := ar2 } := by simp only [k', k1, ar2, h1_4, h1_ri]
  rw [← hk'_eq] at hnw2 hperm2
  refine ⟨hnw2, fullArenaPermEq_trans hperm1 hperm2, ?_, ?_⟩
  · simp only [k']; rw [List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by rw [List.length_set, ha]; omega)]
  · simp only [k']; rw [List.getElem?_set_self
      (by rw [List.length_set, List.length_set, ha]; omega)]

end LeanQbe.T.Examples.Kissat.Proof.PropSearch
