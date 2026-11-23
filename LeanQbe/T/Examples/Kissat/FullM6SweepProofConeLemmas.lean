module

public import LeanQbe.T.Examples.Kissat.FullM6SweepProofDenseProp

/-!
# Kissat `D-Full` M6 — Scaled BFS Cone Extraction Scoped Tactics & Lemmas

1. `M6SweepTactics`: strictly scoped `@[scoped c0_load]` / `@[scoped c0_store]` / `@[scoped bv_c0]`
   helpers for `FullMem` (`pTmp`, `pWorkStk1`), dynamic `K6` shrinkage, and cone bitvectors.
2. Pure `BitVec`, list, `FullDenseInvW`, `ConeModelSet`, and `k6ShrinkNv_preserves_inv`
   (handling arbitrary `trl_end ≤ nv` from level-0 unit propagation during cone construction).
3. `M6ConeInv` loop invariant and transition helpers (`m6ConeInv_init`, `m6ConeInv_push_var`,
   `m6_cone_call_add_clause`, `m6_cone_k_unassigned_step`, `m6_cone_exit_post`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Sweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Sweep
open Kraken.Bedrock2.Test

open K6MemATactics K6PtrTactics

/-! ## 1. Strictly Scoped `FullMem` & Sweeping Tactics (`M6SweepTactics`) -/

namespace M6SweepTactics

open FullArenaTactics
open scoped FullArenaTactics

attribute [scoped bv_c0 high] bv_c0_zext32_64
attribute [scoped bv_c0] bv32_lshr_1 bv32_and_1 bv32_xor_1 List.length_set Bool.false_eq_true

@[scoped bv_c0] theorem m6_bv32_zero : (0 : BitVec 32) = 0#32 := rfl
@[scoped bv_c0] theorem m6_bv32_one : (1 : BitVec 32) = 1#32 := rfl
@[scoped bv_c0] theorem m6_bv32_two : (2 : BitVec 32) = 2#32 := rfl

@[scoped bv_c0] theorem m6_fullState_core (k : FullCoreState) (sc : FullScratch) :
    ({ core := k, scratch := sc } : FullState).core = k := rfl

@[scoped bv_c0] theorem m6_fullState_scratch (k : FullCoreState) (sc : FullScratch) :
    ({ core := k, scratch := sc } : FullState).scratch = sc := rfl

@[scoped bv_c0] theorem m6_bv64_and_1023 (x : BitVec 64) :
    (x &&& BitVec.ofNat 64 1023).toNat = x.toNat % 1024 := by
  rw [BitVec.toNat_and, show (BitVec.ofNat 64 1023).toNat = 1023 from rfl]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 10

@[scoped bv_c0] theorem m6_bv32_shl1_nat (x : BitVec 32) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem m6_bv32_shl1_mod32 (x : BitVec 32) :
    x <<< ((1#32 : BitVec 32).toNat % 32) = x <<< (1 : Nat) := rfl

@[scoped c0_load] theorem load_m6_tmp0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pTmp = some s.core.tmp[0] := by
  simpa using load_full_tmp (i := 0) hi hm

@[scoped c0_store] theorem store_m6_tmp0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pTmp ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
        (storeMem m i32 c.pTmp v) := by
  simpa using store_full_tmp (i := 0) v hi hm

@[scoped c0_store] theorem store_m6_tmp1 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 1 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 4) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 1 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 4) v) := by
  simpa using store_full_tmp (i := 1) v hi hm

@[scoped c0_load] theorem load_m6_ws1_0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.scratch.work_stk1.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pWorkStk1 = some s.scratch.work_stk1[0] := by
  simpa using load_full_work_stk1 (i := 0) hi hm

@[scoped c0_store] theorem store_m6_ws1_0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pWorkStk1 ∧
      (FullMem c { s with scratch := { s.scratch with
        work_stk1 := s.scratch.work_stk1.set 0 v } } ⋆ R)
        (storeMem m i32 c.pWorkStk1 v) := by
  simpa using store_full_work_stk1 (i := 0) v hi hm

scoped macro "m6_steps" : tactic =>
  `(tactic| (
      (try change Func.wp _ _ _ _ _ _); (try change wp _ _ _ _ _)
      c0_hsteps!))

scoped macro "m6_split" : tactic =>
  `(tactic| (
      (try change Func.wp _ _ _ _ _ _); (try change wp _ _ _ _ _)
      c0_hsplit))

scoped macro "m6_to_group" : tactic =>
  `(tactic| (
      (try change Func.wp _ _ _ _ _ _); (try change wp _ _ _ _ _)
      c0_hsteps_nogrp))

scoped macro "m6_csteps!" : tactic =>
  `(tactic| (
      (try change Func.wp _ _ _ _ _ _); (try change wp _ _ _ _ _)
      c0_steps!))

scoped macro "m6_call " h:ident : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

end M6SweepTactics

open scoped FullArenaTactics M6SweepTactics

/-! ## 2. Pure BitVector, List, & `FullMem` Frame Helpers -/

theorem m6_bv32_add1 {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
    (x + 1#32).toNat = x.toNat + 1 := by bv_omega

theorem m6_bv64_add1 {x : BitVec 64} (h : x.toNat < 2 ^ 63) :
    (x + 1#64).toNat = x.toNat + 1 := by bv_omega

theorem m6_bv32_shr1_toNat (x : BitVec 32) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem m6_bv32_and1_toNat (x : BitVec 32) : (x &&& 1#32).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and, show (1#32).toNat = 1 from rfl]
  simp [Nat.and_two_pow_sub_one_eq_mod x.toNat 1]

theorem m6_bv32_shl1_or_pol (v pol : BitVec 32) (hv : v.toNat < 2 ^ 31) (hp : pol.toNat < 2) :
    ((v <<< (1 : Nat)) ||| pol).toNat = 2 * v.toNat + pol.toNat := by
  have h1 : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega : v.toNat * 2 < 2 ^ 32)]
    omega
  rcases (by omega : pol.toNat = 0 ∨ pol.toNat = 1) with h0 | h1p
  · have hp0 : pol = 0#32 := BitVec.eq_of_toNat_eq h0
    rw [hp0, BitVec.or_zero, h1, show (0#32).toNat = 0 from rfl]; omega
  · have hp1 : pol = 1#32 := BitVec.eq_of_toNat_eq h1p
    rw [hp1, BitVec.toNat_or, h1, show (1#32).toNat = 1 from rfl]
    apply Nat.eq_of_testBit_eq; intro i; cases i with
    | zero => simp [Nat.testBit_zero]
    | succ j =>
      rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
        show (1 : Nat) / 2 = 0 from rfl, show (2 * v.toNat) / 2 = v.toNat by omega,
        show (2 * v.toNat + 1) / 2 = v.toNat by omega, Nat.zero_testBit, Bool.or_false]

theorem m6_bv32_shl1_or_and1 (t l : BitVec 32) (ht : t.toNat < 2 ^ 31) :
    ((t <<< (1 : Nat)) ||| (l &&& 1#32)).toNat = 2 * t.toNat + l.toNat % 2 := by
  have h1 : (l &&& 1#32).toNat < 2 := by rw [m6_bv32_and1_toNat]; omega
  simpa [m6_bv32_and1_toNat] using m6_bv32_shl1_or_pol t (l &&& 1#32) ht h1

theorem m6_bv32_add1_sub1_eq (x : BitVec 32) : x + 1#32 - 1#32 = x := by bv_omega

theorem m6_bv32_add1_sub1_toNat (x : BitVec 32) :
    (x + (1 : BitVec 32) - (1 : BitVec 32)).toNat = x.toNat := by bv_omega

theorem m6_bv32_ofNat_add1 (x : BitVec 32) :
    BitVec.ofNat 32 (x.toNat + 1) = x + 1#32 := by bv_omega

theorem m6_bv32_ofNat_add1_sub1 (q : BitVec 32) :
    BitVec.ofNat 32 (q.toNat + 1) - 1#32 = q := by bv_omega

theorem m6_bv64_shl1 (x : BitVec 32) :
    (x.setWidth 64 <<< (1 : Nat)).toNat = 2 * x.toNat := by
  have hx := x.isLt
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : x.toNat * 2 < 2 ^ 64)]; omega

theorem m6_bv64_shl1_add1 (x : BitVec 32) :
    ((x.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * x.toNat + 1 := by
  have hx := x.isLt
  rw [BitVec.toNat_add, m6_bv64_shl1, show (1#64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega : 2 * x.toNat + 1 < 2 ^ 64)]

theorem m6_bv32_garb_false_of_and_garb_red {hdr mask : BitVec 32}
    (h : (hdr &&& (0x00080000#32 ||| mask)) = 0#32) :
    (hdr &&& 0x00080000#32) = 0#32 := by
  ext i hi
  have hi0 := congrArg (·[i]) h
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_zero hi] at hi0 ⊢
  cases h19 : (0x00080000#32)[i]
  · simp
  · rw [h19, Bool.true_or, Bool.and_true] at hi0; simp [hi0]

theorem m6_getElem_eq_getD {α : Type} (xs : List α) {i : Nat}
    (h : i < xs.length) (d : α) : xs[i]'h = xs[i]?.getD d := by
  rw [List.getElem?_eq_getElem h, Option.getD_some]

theorem m6_list_getElem_congr {α : Type} {xs : List α} {i j : Nat}
    (hij : i = j) (hi : i < xs.length) (hj : j < xs.length) :
    xs[i]'hi = xs[j]'hj := by subst hij; rfl

theorem m6_list_drop_set_lt {α : Type _} (xs : List α) {k i : Nat} (v : α) (hik : i < k) :
    (xs.set i v).drop k = xs.drop k := by
  apply List.ext_getElem
  · simp
  · intro j _ _
    simp only [List.getElem_drop]
    rw [List.getElem_set_ne (by omega)]

theorem m6_list_drop_set_ge {α : Type _} (xs : List α) {k i : Nat} (v : α) (hki : k ≤ i) :
    (xs.set i v).drop k = (xs.drop k).set (i - k) v := by
  apply List.ext_getElem
  · simp
  · intro j _ _
    simp only [List.getElem_drop]
    by_cases hji : j = i - k
    · subst hji; simp only [show k + (i - k) = i by omega, List.getElem_set_self]
    · rw [List.getElem_set_ne (by omega), List.getElem_set_ne (Ne.symm hji), List.getElem_drop]

theorem m6_list_take_set_ge {α : Type _} (xs : List α) {n i : Nat} (v : α) (hni : n ≤ i) :
    (xs.set i v).take n = xs.take n := by
  apply List.ext_getElem
  · simp
  · intro j hj1 _
    have hj : j < n := by simp at hj1; omega
    simp only [List.getElem_take]
    rw [List.getElem_set_ne (by omega)]

theorem m6_list_take_set_lt {α : Type _} (xs : List α) {n i : Nat} (v : α) (hin : i < n) :
    (xs.set i v).take n = (xs.take n).set i v := by
  apply List.ext_getElem
  · simp
  · intro j hj1 _
    have hj : j < n ∧ j < xs.length := by simp at hj1; omega
    simp only [List.getElem_take]
    by_cases hji : j = i
    · subst hji; simp only [List.getElem_set_self]
    · rw [List.getElem_set_ne (Ne.symm hji), List.getElem_set_ne (Ne.symm hji), List.getElem_take]

theorem m6_inj_lt_of_missing (f : Nat → Nat) {n m x : Nat}
    (hinj : ∀ i j, i < n → j < n → f i = f j → i = j)
    (hlt : ∀ i < n, f i < m) (hx : x < m) (hmiss : ∀ i < n, f i ≠ x) : n < m := by
  let xs := (List.range n).map f
  have hnd : xs.Nodup := List.pairwise_iff_getElem.mpr fun i j hi hj hij => by
    simp only [xs, List.length_map, List.length_range] at hi hj
    simp only [xs, List.getElem_map, List.getElem_range]
    exact fun heq => Nat.ne_of_lt hij (hinj i j hi hj heq)
  have hnot : x ∉ xs := by
    intro hm; obtain ⟨i, hi, heq⟩ := List.mem_map.mp hm
    rw [List.mem_range] at hi; exact hmiss i hi heq
  have hle := k6_nodup_subset_length (List.nodup_cons.mpr ⟨hnot, hnd⟩) fun y hy => by
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact hx
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy'
      rw [List.mem_range] at hi; exact hlt i hi
  simp only [xs, List.length_cons, List.length_map, List.length_range] at hle
  omega

theorem m6_pack_nv_nc (nv nc : BitVec 32) (hnv : nv.toNat ≤ 8192) (hnc : nc.toNat ≤ 24576) :
    let r := nv.setWidth 64 ||| (nc.setWidth 64 <<< (16 : Nat))
    (r &&& 0xFFFF#64).toNat = nv.toNat ∧
    (r >>> (16 : Nat)).toNat = nc.toNat ∧
    r.toNat = nv.toNat + nc.toNat * 2 ^ 16 := by
  intro r
  have hlt16 : ∀ {x : Nat}, x < 2 ^ 16 → ∀ j, 16 ≤ j → x.testBit j = false := fun hx j hj =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hj))
  have hmask : ∀ j, Nat.testBit 65535 j = decide (j < 16) := fun j => by
    rw [show (65535 : Nat) = 2 ^ 16 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  have h1 : (r &&& 0xFFFF#64) = nv.setWidth 64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [r, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and, hmask]
    by_cases h16 : i < 16
    · have h32 : i < 32 := by omega
      simp [h16, h32]
    · simp only [h16, decide_false, Bool.and_false]
      rw [BitVec.getLsbD]
      exact (hlt16 (by omega : nv.toNat < 2 ^ 16) i (by omega)).symm
  have h2 : (r >>> (16 : Nat)) = nc.setWidth 64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [r, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth]
    by_cases h64 : 16 + i < 64
    · simp only [h64, decide_true, Bool.true_and, show 16 + i - 16 = i by omega]
      rw [BitVec.getLsbD, hlt16 (by omega : nv.toNat < 2 ^ 16) (16 + i) (by omega), Bool.false_or]
      by_cases hi32 : i < 32
      · simp [hi, hi32]
      · have hf : nc.toNat.testBit i = false := hlt16 (by omega : nc.toNat < 2 ^ 16) i (by omega)
        simp [BitVec.getLsbD, hf]
    · have hf : nc.toNat.testBit i = false := hlt16 (by omega : nc.toNat < 2 ^ 16) i (by omega)
      simp [h64, BitVec.getLsbD, hf]
  have hr_sum_bv : r = BitVec.ofNat 64 (nv.toNat + nc.toNat * 2 ^ 16) := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [r, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
    change _ = Nat.testBit (nv.toNat + nc.toNat * 2 ^ 16) i
    rw [show nv.toNat + nc.toNat * 2 ^ 16 = 2 ^ 16 * nc.toNat + nv.toNat by omega,
      Nat.testBit_two_pow_mul_add]
    · by_cases h16 : i < 16
      · simp [h16, BitVec.getLsbD]
      · have hge16 : 16 ≤ i := by omega
        simp only [h16, decide_false, ↓reduceIte, Bool.not_false, Bool.true_and,
          show i - 16 < 64 by omega, decide_true]
        simp [BitVec.getLsbD, hlt16 (by omega : nv.toNat < 2 ^ 16) i hge16]
    · omega
  exact ⟨by rw [h1, bv_c0_zext32_64], by rw [h2, bv_c0_zext32_64],
    by rw [hr_sum_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]⟩

/-- Lift a cone-local literal `l < 2 * nv` back to a global literal via `cone_v`. -/
def m6ConeLift (cone_v : List (BitVec 32)) (l : Nat) : Nat :=
  (cone_v[l / 2]?.getD 0#32).toNat * 2 + l % 2

theorem coneLift_of_tmk_pair {cone_v : List (BitVec 32)} {idx v l : Nat}
    (hw : (cone_v[idx]?.getD 0#32).toNat = v) (hl : l / 2 = v) :
    m6ConeLift cone_v (2 * idx + l % 2) = l := by
  unfold m6ConeLift
  rw [show (2 * idx + l % 2) / 2 = idx by omega,
    show (2 * idx + l % 2) % 2 = l % 2 by omega, hw]
  omega

theorem coneLift_sat_iff {cone_v : List (BitVec 32)} {α : Nat → Bool} {l : Nat} :
    (cnfClause [l]).Sat (fun i => α (cone_v[i]?.getD 0#32).toNat) ↔
      (cnfClause [m6ConeLift cone_v l]).Sat α := by
  simp only [sat_cnfClause_singleton, m6ConeLift, litVar, litSign]
  have hd : ((cone_v[l / 2]?.getD 0#32).toNat * 2 + l % 2) / 2 =
      (cone_v[l / 2]?.getD 0#32).toNat := by omega
  have hm : ((cone_v[l / 2]?.getD 0#32).toNat * 2 + l % 2) % 2 = l % 2 := by omega
  rw [hd, hm]

theorem semEntails_coneModelSet_of_entails {F_cur : List (List Nat)}
    {ws1 : List (BitVec 32)} {nv : Nat} {lits : List Nat}
    (hlts : ∀ l ∈ lits, l < 2 * nv)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause (lits.map (m6ConeLift ws1)))) :
    SemEntails (ConeModelSet F_cur ws1 nv) lits := by
  intro β ⟨α, hα, hβ⟩
  have hsat := (CNF.entails_clause_def.mp hent) α hα
  rw [clause_sat_cnfClause_iff] at hsat ⊢
  obtain ⟨gl, hgl_m, hgl_s⟩ := hsat
  obtain ⟨l, hl_m, rfl⟩ := List.mem_map.mp hgl_m
  refine ⟨l, hl_m, ?_⟩
  have hl_lt := hlts l hl_m
  have hvar : litVar (m6ConeLift ws1 l) = (ws1[l / 2]?.getD 0#32).toNat := by
    unfold litVar m6ConeLift; omega
  have hsign : litSign (m6ConeLift ws1 l) = litSign l := by
    unfold litSign m6ConeLift; simp [Nat.add_mod]
  rw [hvar, hsign] at hgl_s
  rw [show litVar l = l / 2 from rfl, hβ (l / 2) (by omega)]
  exact hgl_s

theorem coneModelSet_push_var {F_cur : List (List Nat)} {ws1 : List (BitVec 32)} {nv : Nat}
    {ov : BitVec 32} (β : Nat → Bool)
    (h : ConeModelSet F_cur (ws1.set nv ov) (nv + 1) β) :
    ConeModelSet F_cur ws1 nv β := by
  obtain ⟨α, hα, hβ⟩ := h
  refine ⟨α, hα, fun i hi => ?_⟩
  have h1 := hβ i (by omega)
  rwa [List.getElem?_set_ne (by omega : nv ≠ i)] at h1

theorem coneModelSet_mono_nv {F_cur : List (List Nat)} {ws1 ws1' : List (BitVec 32)}
    {n1 n2 : Nat} (hle : n1 ≤ n2) (heq : ∀ i < n1, ws1'[i]? = ws1[i]?)
    {β : Nat → Bool} (h : ConeModelSet F_cur ws1' n2 β) :
    ConeModelSet F_cur ws1 n1 β := by
  obtain ⟨α, hα, hβ⟩ := h
  refine ⟨α, hα, fun i hi => ?_⟩
  have h1 := hβ i (by omega)
  rwa [heq i hi] at h1

theorem m6_lvl0_false_not_sat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {l : Nat} (hlt : l < 2 * k.cur_vars) (hfalse : k.vals[l]?.getD 0#8 = 0xFF#8)
    {α : Nat → Bool} (hα : (cnfOfClauses F_cur).Sat α) : ¬ (cnfClause [l]).Sat α := by
  obtain ⟨idx, hidx, htrl⟩ := (hw.vals_false_iff l hlt).mp hfalse
  have hlvl0 : (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le idx hidx; omega
  have hent := hw.level0_sound idx hidx hlvl0
  rw [htrl, CNF.entails_clause_def] at hent
  have hneg : (cnfClause [litNeg l]).Sat α := hent α hα
  simp only [sat_cnfClause_singleton, litVar_litNeg, litSign_litNeg] at hneg ⊢
  intro hsat; rw [hsat] at hneg; cases hb : litSign l <;> simp [hb] at hneg

theorem m6_trl_end_le_of_bdd {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State} {nv : Nat}
    (hinv : K6Inv L P ks) (htrl_bdd : ∀ l ∈ k6TrailLits ks, l < 2 * nv) :
    ks.trl_end.toNat ≤ nv := by
  have hm := L.hmaxV
  have hte_le := hinv.assign.trl_end_le
  have hnv := hinv.clauses.nv_le
  have hte_len : ks.trl_end.toNat ≤ ks.trl.length := by rw [hinv.shapes.trl_len]; omega
  have hle := k6_nodup_subset_length (n := nv) hinv.assign.trl_nodup fun v hv => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
    have := htrl_bdd l hl; omega
  unfold k6TrailLits at hle
  simpa [List.length_map, List.length_take, Nat.min_eq_left hte_len] using hle

theorem k6ShrinkNv_preserves_inv {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks : K6State} {nv : BitVec 32}
    (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks)
    (hnv1 : 1 ≤ nv.toNat) (hnv_max : nv.toNat ≤ L.maxV) (hks_nv : ks.nv = L.mv32)
    (_hlvl0 : ks.lvl = 0#32) (hna0 : ks.nassump = 0#32)
    (hbdd : K6LitsBounded nv.toNat ks)
    (htrl_bdd : ∀ l ∈ k6TrailLits ks, l < 2 * nv.toNat) :
    let ks' := ((((((ks.putHdr .nv nv).putHdr .unass (nv - ks.trl_end)).putHdr .qlast
      (nv - 1#32)).putHdr .qsearch (nv - 1#32)).putHdr .qstamp nv)).putArr .qnext
      (nv.toNat - 1) 0xFFFFFFFF#32
    K6Inv L P ks' ∧ K6TrailSynced ks' ∧ ks'.nv = nv := by
  intro ks'
  have hte_le : ks.trl_end.toNat ≤ nv.toNat := m6_trl_end_le_of_bdd hinv htrl_bdd
  have hnv_le_old : nv.toNat ≤ ks.nv.toNat := by
    rw [hks_nv, k6_mv32_toNat]; exact hnv_max
  have hsh' : ks'.ShapesOk L :=
    ((((((hinv.shapes.putHdr _ _).putHdr _ _).putHdr _ _).putHdr _ _).putHdr _ _).putArr _ _ _)
  have h_nv : ks'.nv = nv := rfl
  have h_nc : ks'.nc = ks.nc := rfl
  have h_lvl : ks'.lvl = ks.lvl := rfl
  have h_prop : ks'.prop = ks.prop := rfl
  have h_te : ks'.trl_end = ks.trl_end := rfl
  have h_unass : ks'.unass = nv - ks.trl_end := rfl
  have h_incons : ks'.incons = ks.incons := rfl
  have h_alen : ks'.alen = ks.alen := rfl
  have h_acap : ks'.acap = ks.acap := rfl
  have h_na : ks'.nassump = ks.nassump := rfl
  have h_nkl : ks'.nkl = ks.nkl := rfl
  have h_nana : ks'.nana = ks.nana := rfl
  have h_mv : ks'.max_v = ks.max_v := rfl
  have h_mo : ks'.max_orig = ks.max_orig := rfl
  have h_mc : ks'.max_cl = ks.max_cl := rfl
  have h_lvlArr : ks'.lvlArr = ks.lvlArr := rfl
  have h_rsn : ks'.rsn = ks.rsn := rfl
  have h_trl : ks'.trl = ks.trl := rfl
  have h_flags : ks'.flags = ks.flags := rfl
  have h_assump : ks'.assump = ks.assump := rfl
  have h_vals : ks'.vals = ks.vals := rfl
  have h_clOff : ks'.clOff = ks.clOff := rfl
  have h_clSz : ks'.clSz = ks.clSz := rfl
  have h_arena : ks'.arena = ks.arena := rfl
  have h_kcl : ∀ cid, k6ClauseSize ks' cid = k6ClauseSize ks cid := fun _ => rfl
  have h_koff : ∀ cid, k6ClauseOff ks' cid = k6ClauseOff ks cid := fun _ => rfl
  have h_klits : ∀ cid, k6ClauseLits ks' cid = k6ClauseLits ks cid := fun _ => rfl
  have hcl' : K6ClausesOk L P ks' :=
    { acap_eq := h_acap ▸ hinv.clauses.acap_eq
      max_v_eq := h_mv ▸ hinv.clauses.max_v_eq
      max_orig_eq := h_mo ▸ hinv.clauses.max_orig_eq
      max_cl_eq := h_mc ▸ hinv.clauses.max_cl_eq
      nv_le := by rw [h_nv]; exact hnv_max
      nc_le := by rw [h_nc]; exact hinv.clauses.nc_le
      alen_le := by rw [h_alen]; exact hinv.clauses.alen_le
      nassump_le := by rw [h_na]; exact hinv.clauses.nassump_le
      nkl_le := by rw [h_nkl]; exact hinv.clauses.nkl_le
      nana_le := by rw [h_nana]; exact hinv.clauses.nana_le
      cl_wf := fun cid hc => by
        rw [h_nc] at hc
        have hw := hinv.clauses.cl_wf cid hc
        rw [h_kcl, h_koff, h_alen, h_klits, h_nv]
        exact ⟨hw.1, hw.2.1, hbdd.1 cid hc, hw.2.2.2⟩
      cl_mono := fun c1 c2 h12 h2c => by
        rw [h_nc] at h2c
        simpa only [h_koff, h_kcl] using hinv.clauses.cl_mono c1 c2 h12 h2c
      incons_ok := fun hi => hinv.clauses.incons_ok (h_incons ▸ hi)
      assump_ok := fun i hi => by
        rw [h_na] at hi; rw [hna0] at hi; simp at hi
      flags_clean := fun v hv => by
        rw [h_nv] at hv; rw [h_flags]
        exact hinv.clauses.flags_clean v (by omega) }
  have hwat' : K6WatchesOk ks' := by
    obtain ⟨chains, hlen, hnd, hch, hmem⟩ := hinv.watches
    refine ⟨chains.take (2 * nv.toNat), by rw [h_nv, List.length_take, hlen]; omega, ?_,
      fun l hl => ?_, fun l hl w hw => ?_⟩
    · have hcat : chains = chains.take (2 * nv.toNat) ++ chains.drop (2 * nv.toNat) :=
        (List.take_append_drop _ _).symm
      rw [hcat, List.flatten_append, List.nodup_append] at hnd
      exact hnd.1
    · rw [h_nv] at hl
      have hget : (chains.take (2 * nv.toNat))[l]? = chains[l]? := List.getElem?_take_of_lt hl
      rw [hget]; exact hch l (by omega)
    · rw [h_nv] at hl
      have hget : (chains.take (2 * nv.toNat))[l]? = chains[l]? := List.getElem?_take_of_lt hl
      rw [hget] at hw
      have hm := hmem l (by omega) w hw
      rw [h_nv, h_nc, h_kcl, h_koff, h_klits, h_arena]
      exact ⟨hm.1, hm.2.1, hm.2.2.1, hbdd.2 w hm.1, hm.2.2.2.2⟩
  have hun_eq : (nv - ks.trl_end).toNat + ks.trl_end.toNat = nv.toNat := by bv_omega
  have hasgn' : K6BaseAssignOk P ks' :=
    { trl_end_le := by rw [h_te, h_nv]; exact hte_le
      prop_le := by rw [h_prop, h_te]; exact hinv.assign.prop_le
      unass_eq := by rw [h_unass, h_te, h_nv]; exact hun_eq
      vals_dom := fun l hl => by
        rw [h_nv] at hl; rw [h_vals]; exact hinv.assign.vals_dom l (by omega)
      vals_neg_iff := fun l hl => by
        rw [h_nv] at hl; rw [h_vals]; exact hinv.assign.vals_neg_iff l (by omega)
      vals_nz_iff_trl := fun l hl => by
        rw [h_nv] at hl; rw [h_vals, h_te, h_trl]
        exact hinv.assign.vals_nz_iff_trl l (by omega)
      trl_nodup := by
        simpa only [k6TrailLits, h_trl, h_te] using hinv.assign.trl_nodup
      trl_lt := fun l hl => by
        simp only [k6TrailLits, h_trl, h_te] at hl
        rw [h_nv]; exact htrl_bdd l hl
      trl_lvl_le := fun v hv => by
        rw [h_nv] at hv; rw [h_lvlArr, h_lvl]; exact hinv.assign.trl_lvl_le v (by omega)
      unass_lvl_zero := fun v hv hz => by
        rw [h_nv] at hv; rw [h_vals] at hz; rw [h_lvlArr, h_rsn]
        exact hinv.assign.unass_lvl_zero v (by omega) hz
      trl_lvl_mono := fun i j hij hj => by
        rw [h_te] at hj; rw [h_lvlArr, h_trl]
        exact hinv.assign.trl_lvl_mono i j hij hj
      dec_earliest := fun i j hji hi hpos heq => by
        rw [h_te] at hi; rw [h_lvlArr, h_trl] at hpos heq; rw [h_rsn, h_trl]
        exact hinv.assign.dec_earliest i j hji hi hpos heq
      lvl0_ok := fun i hi hl0 => by
        rw [h_te] at hi; rw [h_trl, h_lvlArr] at hl0; rw [h_trl, h_vals]
        exact hinv.assign.lvl0_ok i hi hl0 }
  have hsync' : K6TrailSynced ks' := fun i hi => by
    rw [h_te] at hi; rw [h_trl, h_vals]; exact hsync i hi
  have hrsn' : K6ReasonOk ks' := fun i hi => by
    rw [h_te] at hi
    simpa only [h_trl, h_rsn, h_nc, h_klits] using hinv.reasons i hi
  exact ⟨⟨hsh', hcl', hwat', hasgn', hrsn'⟩, hsync', rfl⟩

def m6ConeMask (t : FullState) : FullState :=
  { core := { t.core with tmp := [] }
    scratch := { t.scratch with work_stk1 := [], tarjan_mark := [], scratch_buf := [] } }

theorem m6ConeMask_core_eq {s st : FullState} (h : AgreesExcept m6ConeMask s st) :
    st.core = { s.core with tmp := st.core.tmp } := by
  have hc : ({ st.core with tmp := [] } : FullCoreState) = { s.core with tmp := [] } :=
    congrArg FullState.core h
  cases h1 : st.core; cases h2 : s.core
  rw [h1, h2] at hc; cases hc; rfl

theorem m6ConeMask_state_eq {s st : FullState} (h : AgreesExcept m6ConeMask s st) :
    st = { s with
      core := { s.core with tmp := st.core.tmp }
      scratch := { s.scratch with
        work_stk1 := st.scratch.work_stk1
        tarjan_mark := st.scratch.tarjan_mark
        scratch_buf := st.scratch.scratch_buf } } := by
  have hc := m6ConeMask_core_eq h
  have hs : (m6ConeMask st).scratch = (m6ConeMask s).scratch := congrArg FullState.scratch h
  cases st with | mk c1 sc1 => cases s with | mk c2 sc2 =>
  dsimp only [m6ConeMask] at hc hs ⊢
  cases sc1; cases sc2; cases hs; rw [hc]

theorem m6ConeMask_preserves_dense {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} (hag : AgreesExcept m6ConeMask s st)
    (hlen : st.LengthsOk c) (hdw : FullDenseInvW c F0 F_cur s) :
    FullDenseInvW c F0 F_cur st := by
  have hc0 := m6ConeMask_core_eq hag
  generalize st.core.tmp = tmp' at hc0
  have hll : st.scratch.last_learned = s.scratch.last_learned := hag.get (·.scratch.last_learned)
  have hex : st.scratch.extend_len = s.scratch.extend_len := hag.get (·.scratch.extend_len)
  have hw_orig := hdw.2.1
  have hw' : FullWitnessInv c F0 F_cur { s.core with tmp := tmp' } :=
    { hw_orig with
      arena := { hw_orig.arena with len_ok := hw_orig.arena.len_ok }
      watches := hw_orig.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
  refine ⟨hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc0]; exact hw'
  · have hmc := hdw.2.2.1
    exact ⟨fun v hv => by simpa [hc0] using hmc.1 v hv,
      fun l hl => by simpa [hc0] using hmc.2 l hl⟩
  · have hnda := hdw.2.2.2.1; intro r hr hng
    dsimp only [fullArenaClauseRefs, fullArenaClauseGarb, fullArenaClauseLits] at hr hng ⊢
    simp only [fullArenaClauseRefsCore, fullArenaClauseGarbCore, fullArenaClauseLitsCore, hc0]
      at hr hng ⊢
    exact hnda r hr hng
  · refine ⟨fun i hi => ?_, by simpa [hex] using hdw.2.2.2.2.1.2⟩
    have h1 := hdw.2.2.2.2.1.1 i hi
    dsimp only at h1 ⊢; rw [hll, fullArenaClauseRefs, hc0]; exact h1
  · rw [hc0]; exact hdw.2.2.2.2.2.1
  · rw [hc0]; exact hdw.2.2.2.2.2.2

theorem m6ConeMask_upd_tmp {s st : FullState} (tmp' : List (BitVec 32))
    (h : AgreesExcept m6ConeMask s st) :
    AgreesExcept m6ConeMask s { st with core := { st.core with tmp := tmp' } } :=
  h.update (fun x => { x with core := { x.core with tmp := tmp' } }) fun _ => rfl

theorem m6ConeMask_upd_tmk {s st : FullState} (tmk' : List (BitVec 32))
    (h : AgreesExcept m6ConeMask s st) :
    AgreesExcept m6ConeMask s { st with scratch := { st.scratch with tarjan_mark := tmk' } } :=
  h.update (fun x => { x with scratch := { x.scratch with tarjan_mark := tmk' } }) fun _ => rfl

theorem m6ConeMask_upd_tmk_ws1 {s st : FullState} (tmk' ws1' : List (BitVec 32))
    (h : AgreesExcept m6ConeMask s st) :
    AgreesExcept m6ConeMask s
      { st with scratch := { st.scratch with tarjan_mark := tmk', work_stk1 := ws1' } } :=
  h.update
    (fun x => { x with scratch := { x.scratch with tarjan_mark := tmk', work_stk1 := ws1' } })
    fun _ => rfl

def m6SweepAddRestTmp (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  FullCoreByteArrs c s.core ⋆
  (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
   array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
   array (t := i32) c.pTrailPos s.core.trail_pos ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
  FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
  FullScrMetaArrs c s.scratch ⋆
  (array (t := i32) c.pDelayed s.scratch.delayed ⋆ array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
   array (t := i32) c.pExtendStk s.scratch.extend_stk) ⋆ c.pad

theorem m6_focus_addCl_tmp {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMem c s ⋆ R) m) :
    (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
      array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
      array (t := i32) c.pTmp s.core.tmp ⋆ (m6SweepAddRestTmp c s ⋆ R)) m := by
  unfold FullMem FullCoreArrays FullCoreU32A FullScratchArrays FullScrDynArrs at hm
  unfold m6SweepAddRestTmp; ecancel

theorem m6_unfocus_addCl_tmp {c : FullCfg} {s : FullState} {scr' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array64 (c.hdr + 32) (Full.hdrTailWords c
        { s with scratch := { s.scratch with scratch_buf := scr' } }) ⋆
      array (t := i32) c.pScratchBuf scr' ⋆
      array (t := i32) c.pTmp s.core.tmp ⋆ (m6SweepAddRestTmp c s ⋆ R)) m) :
    (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m := by
  let sc' : FullScratch := { s.scratch with scratch_buf := scr' }
  change (array64 (c.hdr + 32) (Full.hdrTailWords c { core := s.core, scratch := sc' }) ⋆
    array (t := i32) c.pScratchBuf scr' ⋆
    array (t := i32) c.pTmp s.core.tmp ⋆ (m6SweepAddRestTmp c s ⋆ R)) m at hm
  have hSB : FullScrByteArrs c sc' = FullScrByteArrs c s.scratch := rfl
  have hSA : FullScrU32A c sc' = FullScrU32A c s.scratch := rfl
  have hSW : FullScrWksArrs c sc' = FullScrWksArrs c s.scratch := rfl
  have hSM : FullScrMetaArrs c sc' = FullScrMetaArrs c s.scratch := rfl
  have hd : sc'.delayed = s.scratch.delayed := rfl
  have hr : sc'.red_refs = s.scratch.red_refs := rfl
  have he : sc'.extend_stk = s.scratch.extend_stk := rfl
  have hsb : sc'.scratch_buf = scr' := rfl
  change (FullMem c { s with scratch := sc' } ⋆ R) m
  unfold FullMem FullCoreArrays FullCoreU32A FullScratchArrays FullScrDynArrs
  dsimp only
  rw [hSB, hSA, hSW, hSM, hd, hr, he, hsb]
  unfold m6SweepAddRestTmp at hm; ecancel

/-! ## 3. `M6ConeInv` Loop Invariant & Transition Lemmas -/

structure M6ConeInv (F_cur : List (List Nat)) (L : K6Layout)
    (st : FullState) (nv nc : Nat) : Prop where
  nv_ge1 : 1 ≤ nv
  nv_leMax : nv ≤ L.maxV
  nv_le_cv : nv ≤ st.core.cur_vars
  nc_le : nc ≤ L.maxOrig
  scr_len : st.scratch.scratch_buf.length = L.scrLen
  k6_inv : K6Inv L (ConeModelSet F_cur st.scratch.work_stk1 nv)
    (k6StateOfScratch L st.scratch.scratch_buf)
  k6_sync : K6TrailSynced (k6StateOfScratch L st.scratch.scratch_buf)
  k6_nv : (k6StateOfScratch L st.scratch.scratch_buf).nv = L.mv32
  k6_lvl : (k6StateOfScratch L st.scratch.scratch_buf).lvl = 0#32
  k6_na : (k6StateOfScratch L st.scratch.scratch_buf).nassump = 0#32
  k6_bdd : K6LitsBounded nv (k6StateOfScratch L st.scratch.scratch_buf)
  k6_trl_bdd : ∀ l ∈ k6TrailLits (k6StateOfScratch L st.scratch.scratch_buf), l < 2 * nv
  fwd : ∀ i < nv,
    (st.scratch.work_stk1[i]?.getD 0#32).toNat < st.core.cur_vars ∧
    st.scratch.tarjan_mark[(st.scratch.work_stk1[i]?.getD 0#32).toNat]?.getD 0#32 =
      BitVec.ofNat 32 (i + 1)
  rev : ∀ v < st.core.cur_vars,
    st.scratch.tarjan_mark[v]?.getD 0#32 = 0#32 ∨
    ∃ i < nv,
      (st.scratch.work_stk1[i]?.getD 0#32).toNat = v ∧
      st.scratch.tarjan_mark[v]?.getD 0#32 = BitVec.ofNat 32 (i + 1)

theorem m6ConeInv_tmp_irrel {F_cur : List (List Nat)} {L : K6Layout} {st : FullState}
    {nv nc : Nat} {tmp' : List (BitVec 32)} (h : M6ConeInv F_cur L st nv nc) :
    M6ConeInv F_cur L { st with core := { st.core with tmp := tmp' } } nv nc :=
  ⟨h.nv_ge1, h.nv_leMax, h.nv_le_cv, h.nc_le, h.scr_len, h.k6_inv, h.k6_sync, h.k6_nv,
   h.k6_lvl, h.k6_na, h.k6_bdd, h.k6_trl_bdd, h.fwd, h.rev⟩

theorem m6ConeInv_init {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout} {s : FullState}
    {scr0 : List (BitVec 32)} {root_v : BitVec 32}
    (hlen : s.LengthsOk c) (hL_len : L.scrLen = c.scratch_cap)
    (hroot : root_v.toNat < s.core.cur_vars) (htmk : M6TmkZero s)
    (hscr0 : scr0.length = c.scratch_cap)
    (hK : ∀ P, K6Inv L P (k6StateOfScratch L scr0))
    (hsy : K6TrailSynced (k6StateOfScratch L scr0))
    (hnv : (k6StateOfScratch L scr0).nv = L.mv32)
    (hnc : (k6StateOfScratch L scr0).nc = 0#32)
    (hlvl : (k6StateOfScratch L scr0).lvl = 0#32)
    (htr : (k6StateOfScratch L scr0).trl_end = 0#32)
    (hna : (k6StateOfScratch L scr0).nassump = 0#32) :
    let s1 : FullState :=
      { s with scratch :=
        { s.scratch with
          scratch_buf := scr0
          work_stk1 := s.scratch.work_stk1.set 0 root_v
          tarjan_mark := s.scratch.tarjan_mark.set root_v.toNat 1#32 } }
    s1.LengthsOk c ∧ AgreesExcept m6ConeMask s s1 ∧ M6ConeInv F_cur L s1 1 0 := by
  intro s1
  have hm := L.hmaxV
  have hcv_le := hlen.core_ok.cur_vars_le
  have hwk_len := hlen.scratch_ok.work_stk1_len
  have htm_len := hlen.scratch_ok.tarjan_mark_len
  refine ⟨⟨hlen.core_ok, { hlen.scratch_ok with
      work_stk1_len := by simp [s1, hwk_len]
      tarjan_mark_len := by simp [s1, htm_len]
      scratch_buf_len := by simp [s1, hscr0] }⟩,
    rfl,
    { nv_ge1 := Nat.le_refl 1
      nv_leMax := by omega
      nv_le_cv := by dsimp [s1]; omega
      nc_le := Nat.zero_le _
      scr_len := by dsimp [s1]; rw [hscr0, hL_len]
      k6_inv := hK _
      k6_sync := hsy
      k6_nv := hnv
      k6_lvl := hlvl
      k6_na := hna
      k6_bdd := ⟨fun cid hc => by rw [hnc] at hc; simp at hc,
                 fun w hw => by rw [hnc] at hw; simp at hw⟩
      k6_trl_bdd := fun l hl => by
        unfold k6TrailLits at hl; rw [htr] at hl; simp at hl
      fwd := fun i hi => by
        have hi0 : i = 0 := by omega
        subst hi0; dsimp only [s1]
        rw [List.getElem?_set_self (by omega), Option.getD_some,
          List.getElem?_set_self (by omega), Option.getD_some]
        exact ⟨hroot, rfl⟩
      rev := fun v hv => by
        dsimp only [s1]
        by_cases hvr : v = root_v.toNat
        · subst hvr; right; refine ⟨0, Nat.zero_lt_one, ?_, ?_⟩
          · rw [List.getElem?_set_self (by omega), Option.getD_some]
          · rw [List.getElem?_set_self (by omega), Option.getD_some]
        · left; rw [List.getElem?_set_ne (Ne.symm hvr)]; exact htmk v hv }⟩

theorem m6ConeInv_push_var {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {s : FullState} {nv nc : Nat} {ov : BitVec 32}
    (hlen : s.LengthsOk c) (hc : M6ConeInv F_cur L s nv nc)
    (hnv_max : nv < L.maxV) (hov : ov.toNat < s.core.cur_vars)
    (hmiss : s.scratch.tarjan_mark[ov.toNat]?.getD 0#32 = 0#32) :
    nv < s.core.cur_vars ∧
    let s' : FullState :=
      { s with scratch :=
        { s.scratch with
          tarjan_mark := s.scratch.tarjan_mark.set ov.toNat (BitVec.ofNat 32 (nv + 1))
          work_stk1 := s.scratch.work_stk1.set nv ov } }
    M6ConeInv F_cur L s' (nv + 1) nc := by
  have hm := L.hmaxV
  have hcv_le := hlen.core_ok.cur_vars_le
  have hwk_len := hlen.scratch_ok.work_stk1_len
  have htm_len := hlen.scratch_ok.tarjan_mark_len
  have hne_ov : ∀ i < nv, (s.scratch.work_stk1[i]?.getD 0#32).toNat ≠ ov.toNat := fun i hi heq => by
    have hti := (hc.fwd i hi).2; rw [heq, hmiss] at hti
    have htn := congrArg BitVec.toNat hti
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i + 1 < 2 ^ 32)] at htn; omega
  have hnv_lt : nv < s.core.cur_vars :=
    m6_inj_lt_of_missing (fun i => (s.scratch.work_stk1[i]?.getD 0#32).toNat)
      (fun i j hi hj heq => by
        have hti := (hc.fwd i hi).2; have htj := (hc.fwd j hj).2
        rw [heq] at hti
        have htn := congrArg BitVec.toNat (hti.symm.trans htj)
        simp only [BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : i + 1 < 2 ^ 32),
          Nat.mod_eq_of_lt (by omega : j + 1 < 2 ^ 32)] at htn; omega)
      (fun i hi => (hc.fwd i hi).1) hov hne_ov
  refine ⟨hnv_lt, ?_⟩
  intro s'
  have hwk_lt : ∀ i < nv, s'.scratch.work_stk1[i]? = s.scratch.work_stk1[i]? := fun i hi =>
    List.getElem?_set_ne (by omega)
  have hwk_nv : s'.scratch.work_stk1[nv]? = some ov := List.getElem?_set_self (by omega)
  exact
    { nv_ge1 := by omega
      nv_leMax := by omega
      nv_le_cv := by dsimp [s']; omega
      nc_le := hc.nc_le
      scr_len := hc.scr_len
      k6_inv := hc.k6_inv.mono_P (fun β hβ => coneModelSet_push_var β hβ)
      k6_sync := hc.k6_sync
      k6_nv := hc.k6_nv
      k6_lvl := hc.k6_lvl
      k6_na := hc.k6_na
      k6_bdd := ⟨fun cid hcid l hl => Nat.lt_trans (hc.k6_bdd.1 cid hcid l hl) (by omega),
                 fun w hw => Nat.lt_trans (hc.k6_bdd.2 w hw) (by omega)⟩
      k6_trl_bdd := fun l hl => Nat.lt_trans (hc.k6_trl_bdd l hl) (by omega)
      fwd := fun i hi => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · rw [hwk_lt i hi']
          have hne := hne_ov i hi'
          refine ⟨(hc.fwd i hi').1, ?_⟩
          dsimp only [s']; rw [List.getElem?_set_ne (Ne.symm hne)]; exact (hc.fwd i hi').2
        · rw [hwk_nv, Option.getD_some]
          refine ⟨hov, ?_⟩
          dsimp only [s']; rw [List.getElem?_set_self (by omega), Option.getD_some]
      rev := fun v hv => by
        dsimp only [s']
        by_cases hvo : v = ov.toNat
        · subst hvo; right; refine ⟨nv, by omega, ?_, ?_⟩
          · rw [hwk_nv, Option.getD_some]
          · rw [List.getElem?_set_self (by omega), Option.getD_some]
        · rw [List.getElem?_set_ne (Ne.symm hvo)]
          rcases hc.rev v hv with hz | ⟨i, hi, hwi, hti⟩
          · exact Or.inl hz
          · exact Or.inr ⟨i, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hwi, hti⟩ }

theorem m6_cone_clause_entails_filtered {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} {cr : Nat} {kept : List Nat}
    (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    (href : cr ∈ fullArenaClauseRefsCore k) (hng : fullArenaClauseGarbCore k cr = false)
    (hcov : ∀ l ∈ fullArenaClauseLitsCore k cr, k.vals[l]?.getD 0#8 = 0xFF#8 ∨ l ∈ kept) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause kept) := by
  rw [CNF.entails_clause_def]; intro α hα
  have hent := hw.arena.entails cr href hng; rw [CNF.entails_clause_def] at hent
  obtain ⟨l, hl_mem, hl_sat⟩ := (clause_sat_cnfClause_iff _ _).mp (hent α hα)
  rcases hcov l hl_mem with hfals | hkept
  · exact absurd ((sat_cnfClause_singleton _ _).mpr hl_sat)
      (m6_lvl0_false_not_sat hw hl0 (hw.arena.lits_lt cr href hng l hl_mem) hfals hα)
  · exact (clause_sat_cnfClause_iff _ _).mpr ⟨l, hkept, hl_sat⟩

theorem m6_arenaClauseLitsCore_mem_iff {k : FullCoreState} {cr l : Nat}
    (hbd : cr + 3 + (k.arena[cr + 2]?.getD 0#32).toNat ≤ k.arena.length) :
    l ∈ fullArenaClauseLitsCore k cr ↔
      ∃ i < (k.arena[cr + 2]?.getD 0#32).toNat, (k.arena[cr + 3 + i]?.getD 0#32).toNat = l := by
  unfold fullArenaClauseLitsCore fullArenaClauseSizeCore
  generalize (k.arena[cr + 2]?.getD 0#32).toNat = sz at hbd ⊢
  simp only [List.mem_map]; constructor
  · rintro ⟨w, hw, rfl⟩; obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hw
    simp only [List.length_take, List.length_drop,
      Nat.min_eq_left (by omega : sz ≤ k.arena.length - (cr + 3))] at hi
    refine ⟨i, hi, ?_⟩; simp only [List.getElem_take, List.getElem_drop] at heq
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, heq]
  · rintro ⟨i, hi, rfl⟩
    have hmem : ((k.arena.drop (cr + 3)).take sz)[i]'(by simp; omega) ∈
        (k.arena.drop (cr + 3)).take sz := List.getElem_mem _
    exact ⟨k.arena[cr + 3 + i]'(by omega),
      by simpa [List.getElem_take, List.getElem_drop] using hmem,
      by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]⟩

theorem m6_cone_occ_hdr_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st_w : FullState} {cr sz : BitVec 32} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) (hnd : FullArenaVarsNodup s)
    (har_eq : st_w.core.arena = s.core.arena) (hcr_ref : cr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hsz_core : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat)
    (hgr0 : (st_w.core.arena[cr.toNat]'(by
      have := (hw.arena.refs_wf cr.toNat hcr_ref).1; have := hlen.core_ok.arena_len_le
      rw [har_eq, hlen.core_ok.arena_len_arr]; omega) &&& (0x00080000#32 ||| 0x00400000#32)) =
      0#32) :
    fullArenaClauseGarbCore s.core cr.toNat = false ∧
    cr.toNat + 3 + sz.toNat ≤ s.core.arena_len ∧ sz.toNat ≤ s.core.cur_vars ∧
    cr.toNat + 3 + sz.toNat ≤ s.core.arena.length := by
  have hwf := hw.arena.refs_wf cr.toNat hcr_ref
  have hal := hlen.core_ok.arena_len_le; have har := hlen.core_ok.arena_len_arr
  have hng : fullArenaClauseGarbCore s.core cr.toNat = false := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have h0 := m6_bv32_garb_false_of_and_garb_red hgr0; simp [har_eq] at h0; simp [h0]
  have hsz_le : cr.toNat + 3 + sz.toNat ≤ s.core.arena_len := by have := hwf.2.2; omega
  have hsz_cv : sz.toNat ≤ s.core.cur_vars := by
    have hlen_lits : (fullArenaClauseLits s cr.toNat).length = sz.toNat := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore
      rw [List.length_map, List.length_take, List.length_drop, ← hsz_core]
      exact Nat.min_eq_left (by omega)
    rw [← hlen_lits]
    have hle := k6_nodup_subset_length (n := s.core.cur_vars)
      (hnd cr.toNat hcr_ref hng) fun v hv => by
        rcases List.mem_map.mp hv with ⟨l, hl, rfl⟩
        have := hw.arena.lits_lt cr.toNat hcr_ref hng l hl; omega
    simpa [List.length_map] using hle
  exact ⟨hng, hsz_le, hsz_cv, by omega⟩

theorem m6_cone_bin_lits_ok {st : FullState}
    {cv qi pol lit ot ov nv : BitVec 32} {iov : Nat}
    (hqi_lt : qi.toNat < nv.toNat) (hnv_lt31 : nv.toNat < 2 ^ 31) (hpol_lt : pol.toNat < 2)
    (hlit_eq : lit.toNat = 2 * cv.toNat + pol.toNat) (hov_eq : ov.toNat = ot.toNat / 2)
    (hiov : iov < nv.toNat)
    (htca : st.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 (qi.toNat + 1))
    (hwca : (st.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat)
    (htov : st.scratch.tarjan_mark[ov.toNat]?.getD 0#32 = BitVec.ofNat 32 (iov + 1))
    (hwov : (st.scratch.work_stk1[iov]?.getD 0#32).toNat = ov.toNat) :
    let l0 := (((st.scratch.tarjan_mark[cv.toNat]?.getD 0#32) - 1#32) <<< (1 : Nat)) ||| pol
    let l1 := (((st.scratch.tarjan_mark[ov.toNat]?.getD 0#32) - 1#32) <<< (1 : Nat)) |||
      (ot &&& 1#32)
    l0.toNat < 2 * nv.toNat ∧ l1.toNat < 2 * nv.toNat ∧
    m6ConeLift st.scratch.work_stk1 l0.toNat = lit.toNat ∧
    m6ConeLift st.scratch.work_stk1 l1.toNat = ot.toNat := by
  intro l0 l1
  have hm0 : BitVec.ofNat 32 (qi.toNat + 1) - 1#32 = BitVec.ofNat 32 qi.toNat := by bv_omega
  have hm1 : BitVec.ofNat 32 (iov + 1) - 1#32 = BitVec.ofNat 32 iov := by bv_omega
  have hl0 : l0.toNat = 2 * qi.toNat + pol.toNat := by
    dsimp only [l0]; rw [htca, hm0]
    have := m6_bv32_shl1_or_pol (BitVec.ofNat 32 qi.toNat) pol
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega) hpol_lt
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : qi.toNat < 2 ^ 32)] using this
  have hl1 : l1.toNat = 2 * iov + ot.toNat % 2 := by
    dsimp only [l1]; rw [htov, hm1]
    have := m6_bv32_shl1_or_and1 (BitVec.ofNat 32 iov) ot
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : iov < 2 ^ 32)] using this
  refine ⟨by omega, by omega, ?_, by rw [hl1]; exact coneLift_of_tmk_pair hwov hov_eq.symm⟩
  rw [hl0]; simpa [show lit.toNat % 2 = pol.toNat by omega] using
    coneLift_of_tmk_pair (cone_v := st.scratch.work_stk1) (idx := qi.toNat) (v := cv.toNat)
      (l := lit.toNat) hwca (by omega)

theorem m6_cone_bin_tmp_prep {c : FullCfg} {F_cur : List (List Nat)}
    {st_a : FullState} {nv_a lit ot l0_b l1_b : BitVec 32}
    (hla : st_a.LengthsOk c) (htmp_a1 : 1 < st_a.core.tmp.length)
    (hl0_lt : l0_b.toNat < 2 * nv_a.toNat) (hl1_lt : l1_b.toNat < 2 * nv_a.toNat)
    (hlift0 : m6ConeLift st_a.scratch.work_stk1 l0_b.toNat = lit.toNat)
    (hlift1 : m6ConeLift st_a.scratch.work_stk1 l1_b.toNat = ot.toNat)
    (hent_bin : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, ot.toNat])) :
    let st_ab : FullState :=
      { st_a with core := { st_a.core with tmp := (st_a.core.tmp.set 0 l0_b).set 1 l1_b } }
    st_ab.LengthsOk c ∧
    (∀ j < 2, (st_ab.core.tmp[j]?.getD 0#32).toNat < 2 * nv_a.toNat) ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause
      ((st_ab.core.tmp.take 2).map
        (fun x => m6ConeLift st_ab.scratch.work_stk1 x.toNat))) := by
  intro st_ab
  have htmp_a := hla.core_ok.tmp_len_arr
  refine ⟨⟨{ hla.core_ok with tmp_len_arr := by simp [st_ab, htmp_a] }, hla.scratch_ok⟩,
    fun j hj => ?_, ?_⟩
  · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · dsimp only [st_ab]
      rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by omega), Option.getD_some]
      exact hl0_lt
    · dsimp only [st_ab]
      rw [List.getElem?_set_self (by simp; omega), Option.getD_some]
      exact hl1_lt
  · have htake : st_ab.core.tmp.take 2 = [l0_b, l1_b] := by
      dsimp only [st_ab]
      cases h_t : st_a.core.tmp with
      | nil => simp [h_t] at htmp_a1
      | cons x0 tl0 =>
        cases tl0 with
        | nil => simp [h_t] at htmp_a1
        | cons x1 tl1 => simp
    rw [htake]; simpa only [List.map_cons, List.map_nil, st_ab, hlift0, hlift1] using hent_bin

theorem m6_cone_call_add_clause {Γ : Env}
    (hAddCl : M6EnvSpec Γ "full_k6_add_clause" k6AddClauseSpec)
    {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout} {s0 st : FullState}
    {nv nc sz : BitVec 32} {aSz : Arg Val i32}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    {k : Tup Val [.bool] → Expr Val Cont [i64]}
    (haSz : aSz.val = sz) (hL_len : L.scrLen = c.scratch_cap)
    (hL_mv : L.maxV = k6MaxV c.scratch_cap)
    (hlen : st.LengthsOk c) (hag : AgreesExcept m6ConeMask s0 st)
    (hcone : M6ConeInv F_cur L st nv.toNat nc.toNat)
    (hnc : nc.toNat < L.maxOrig) (hsz28 : sz.toNat < 2 ^ 28)
    (hsz_tmp : sz.toNat ≤ st.core.tmp.length)
    (hlts : ∀ j < sz.toNat, (st.core.tmp[j]?.getD 0#32).toNat < 2 * nv.toNat)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause
      ((st.core.tmp.take sz.toNat).map (fun x => m6ConeLift st.scratch.work_stk1 x.toNat))))
    (hm : (FullMem c st ⋆ R) m)
    (hk : ∀ (ok : Bool) (st' : FullState) (m' : Mem 64),
      st'.LengthsOk c → AgreesExcept m6ConeMask s0 st' →
      M6ConeInv F_cur L st' nv.toNat (if ok then nc + 1#32 else nc).toNat →
      (ok = false → st'.scratch.scratch_buf = st.scratch.scratch_buf) →
      st'.scratch.tarjan_mark = st.scratch.tarjan_mark →
      st'.scratch.work_stk1 = st.scratch.work_stk1 →
      (FullMem c st' ⋆ R) m' → wp Γ Q X (k (ok, ())) m') :
    wp Γ Q X (Expr.call (as := [i64, i64, i32]) (bs := [.bool])
      "full_k6_add_clause" (Arg.var c.hdr, Arg.var c.pTmp, aSz, ()) k) m := by
  have hm_L := L.hmaxV
  have hnv_le : nv.toNat ≤ L.maxV := hcone.nv_leMax
  have hlts_ks : ∀ j < sz.toNat,
      (st.core.tmp[j]?.getD 0#32).toNat <
        2 * (k6StateOfScratch L st.scratch.scratch_buf).nv.toNat := fun j hj => by
    rw [hcone.k6_nv, k6_mv32_toNat]; have := hlts j hj; omega
  have hsem : SemEntails (ConeModelSet F_cur st.scratch.work_stk1 nv.toNat)
      ((st.core.tmp.take sz.toNat).map BitVec.toNat) := by
    refine semEntails_coneModelSet_of_entails (fun l hl => ?_) ?_
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
      have hjl : j < sz.toNat := by rw [List.length_take] at hj; omega
      have hxj := hlts j hjl
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hxj
      rwa [List.getElem_take]
    · simp only [List.map_map]; simpa [Function.comp_def] using hent
  refine wp_call_of_spec _ k ?_
  dsimp only [vals]; rw [Arg.val_var, haSz]
  refine hAddCl (c.hdr, c.pTmp, sz, ()) m (fun r m' => wp Γ Q X (k r) m') X
    ⟨c, st, ConeModelSet F_cur st.scratch.work_stk1 nv.toNat, L, st.scratch.scratch_buf,
      st.core.tmp, m6SweepAddRestTmp c st ⋆ R,
      rfl, hlen, rfl, hL_len, hL_mv, hcone.k6_inv, hcone.k6_sync, hcone.k6_lvl,
      hsz_tmp, hsz28, hlts_ks, hsem, m6_focus_addCl_tmp hm,
      fun ok scr' m' hsl hpre hK' hsy' hlvl' hnv' hna' _ hfalse _ hbdd' hm' => ?_⟩
  let st' : FullState := { st with scratch := { st.scratch with scratch_buf := scr' } }
  have hlen' : st'.LengthsOk c := ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hsl }⟩
  have hag' : AgreesExcept m6ConeMask s0 st' := hag.update _ (fun _ => rfl)
  have hhdr : Full.hdrTailWords c st' = Full.hdrTailWords c st := rfl
  have hm_un := m6_unfocus_addCl_tmp hm'
  obtain ⟨hbdd_nv, htrl_nv⟩ := hbdd' nv.toNat hlts hcone.k6_bdd hcone.k6_trl_bdd
  have hnc1 : (nc + 1#32).toNat = nc.toNat + 1 := by unfold K6Layout.maxOrig at hnc; bv_omega
  have hscr_false : ok = false → st'.scratch.scratch_buf = st.scratch.scratch_buf := fun hok => by
    have hks_eq := hfalse hok
    have hsh0 := hcone.k6_inv.shapes
    have hscr_L : st.scratch.scratch_buf.length = L.scrLen := hcone.scr_len
    have hscr'_L : scr'.length = L.scrLen := hsl.trans hL_len.symm
    have hkb_le : L.k6Base ≤ st.scratch.scratch_buf.length := by
      rw [hscr_L]; unfold K6Layout.scrLen; omega
    have hkb_le' : L.k6Base ≤ scr'.length := by rw [hscr'_L]; unfold K6Layout.scrLen; omega
    have hfix0 : L.k6Fixed ≤ (st.scratch.scratch_buf.drop L.k6Base).length := by
      rw [List.length_drop, hscr_L]; unfold K6Layout.scrLen; omega
    have hfix' : L.k6Fixed ≤ (scr'.drop L.k6Base).length := by
      rw [List.length_drop, hscr'_L]; unfold K6Layout.scrLen; omega
    have htk_eq : scr'.take L.k6Base = st.scratch.scratch_buf.take L.k6Base := by
      apply List.ext_getElem
      · rw [List.length_take_of_le hkb_le', List.length_take_of_le hkb_le]
      · intro i hi1 _
        have hi : i < L.k6Base := by rw [List.length_take_of_le hkb_le'] at hi1; exact hi1
        rw [List.getElem_take, List.getElem_take]
        exact Option.some.inj (by
          rw [← List.getElem?_eq_getElem (by omega), ← List.getElem?_eq_getElem (by omega)]
          exact hpre i hi)
    have hdrop_eq : scr'.drop L.k6Base = st.scratch.scratch_buf.drop L.k6Base := by
      rw [← K6State.toSlab_ofSlab hfix', ← K6State.toSlab_ofSlab hfix0]
      exact congrArg K6State.toSlab hks_eq
    dsimp only [st']
    rw [← List.take_append_drop L.k6Base scr', htk_eq, hdrop_eq, List.take_append_drop]
  cases ok
  · refine hk false st' m' hlen' hag'
      { hcone with scr_len := hsl.trans hL_len.symm, k6_inv := hK', k6_sync := hsy',
                   k6_nv := hnv'.trans hcone.k6_nv, k6_lvl := hlvl',
                   k6_na := hna'.trans hcone.k6_na, k6_bdd := hbdd_nv, k6_trl_bdd := htrl_nv }
      hscr_false rfl rfl hm_un
  · refine hk true st' m' hlen' hag'
      { hcone with nc_le := by simp only [↓reduceIte, hnc1]; omega,
                   scr_len := hsl.trans hL_len.symm, k6_inv := hK', k6_sync := hsy',
                   k6_nv := hnv'.trans hcone.k6_nv, k6_lvl := hlvl',
                   k6_na := hna'.trans hcone.k6_na, k6_bdd := hbdd_nv, k6_trl_bdd := htrl_nv }
      hscr_false rfl rfl hm_un

theorem m6_cone_k_unassigned_step {c : FullCfg}
    {F_cur : List (List Nat)} {L : K6Layout} {s st_k st_u : FullState}
    {cr sz k cnt nv_k nv_u lit_k : BitVec 32} {nc_w ilv : Nat}
    (hlu : st_u.LengthsOk c) (htmpu_eq : st_u.core.tmp = st_k.core.tmp)
    (hwku_eq : ∀ j < nv_k.toNat, st_u.scratch.work_stk1[j]? = st_k.scratch.work_stk1[j]?)
    (hnvku : nv_k.toNat ≤ nv_u.toNat) (hnvu_max : nv_u.toNat ≤ L.maxV)
    (hk_lt : k.toNat < sz.toNat) (hsz_cv : sz.toNat ≤ s.core.cur_vars)
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hcnt_le : cnt.toNat ≤ k.toNat)
    (hlit_ar : (s.core.arena[cr.toNat + 3 + k.toNat]?.getD 0#32).toNat = lit_k.toNat)
    (hilv : ilv < nv_u.toNat)
    (hwlv : (st_u.scratch.work_stk1[ilv]?.getD 0#32).toNat = lit_k.toNat / 2)
    (htlv_v : st_u.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32 = BitVec.ofNat 32 (ilv + 1))
    (hlts_k : ∀ j < cnt.toNat, (st_k.core.tmp[j]?.getD 0#32).toNat < 2 * nv_k.toNat)
    (hcov_k : ∀ i < k.toNat,
      let l := (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat
      s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨
      l ∈ (st_k.core.tmp.take cnt.toNat).map
        (fun x => m6ConeLift st_k.scratch.work_stk1 x.toNat))
    (hvars_k : ∀ j < cnt.toNat, ∃ p < k.toNat,
      (s.core.arena[cr.toNat + 3 + p]?.getD 0#32).toNat / 2 =
        (st_k.scratch.work_stk1[(st_k.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hnd_k : ∀ j1 j2, j1 < cnt.toNat → j2 < cnt.toNat → j1 ≠ j2 →
      (st_k.core.tmp[j1]?.getD 0#32).toNat / 2 ≠ (st_k.core.tmp[j2]?.getD 0#32).toNat / 2)
    (hnd_cl : ((fullArenaClauseLits s cr.toNat).map (· / 2)).Nodup)
    (hcr_bd : cr.toNat + 3 + sz.toNat ≤ s.core.arena.length)
    (hsz_core : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat)
    (_hc_u : M6ConeInv F_cur L st_u nv_u.toNat nc_w) :
    let new_l : BitVec 32 :=
      (((st_u.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32) - 1#32) <<< (1 : Nat)) |||
        (lit_k &&& 1#32)
    let st_u' : FullState :=
      { st_u with core := { st_u.core with tmp := st_u.core.tmp.set cnt.toNat new_l } }
    (cnt + 1#32).toNat = cnt.toNat + 1 ∧ st_u'.LengthsOk c ∧
    (∀ j < (cnt + 1#32).toNat, (st_u'.core.tmp[j]?.getD 0#32).toNat < 2 * nv_u.toNat) ∧
    (∀ i < (k + 1#32).toNat,
      let l := (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat
      s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨
      l ∈ (st_u'.core.tmp.take (cnt + 1#32).toNat).map
        (fun x => m6ConeLift st_u'.scratch.work_stk1 x.toNat)) ∧
    (∀ j < (cnt + 1#32).toNat, ∃ p < (k + 1#32).toNat,
      (s.core.arena[cr.toNat + 3 + p]?.getD 0#32).toNat / 2 =
        (st_u'.scratch.work_stk1[(st_u'.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
    (∀ j1 j2, j1 < (cnt + 1#32).toNat → j2 < (cnt + 1#32).toNat → j1 ≠ j2 →
      (st_u'.core.tmp[j1]?.getD 0#32).toNat / 2 ≠ (st_u'.core.tmp[j2]?.getD 0#32).toNat / 2) := by
  intro new_l st_u'
  have hmL := L.hmaxV
  have htmp_u := hlu.core_ok.tmp_len_arr
  have htmp_k : st_k.core.tmp.length = c.max_vars := htmpu_eq ▸ htmp_u
  have hdb : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hcnt_lt32 : cnt.toNat < 2 ^ 31 := by unfold dimacsBound at hdb; omega
  have hk_lt32 : k.toNat < 2 ^ 31 := by unfold dimacsBound at hdb; omega
  have hcnt1 : (cnt + 1#32).toNat = cnt.toNat + 1 := by bv_omega
  have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
  have hm1 : BitVec.ofNat 32 (ilv + 1) - 1#32 = BitVec.ofNat 32 ilv := by bv_omega
  have hnew_n : new_l.toNat = 2 * ilv + lit_k.toNat % 2 := by
    simp only [new_l, htlv_v, hm1]
    have := m6_bv32_shl1_or_and1 (BitVec.ofNat 32 ilv) lit_k
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : ilv < 2 ^ 32)] using this
  have hnew_lift : m6ConeLift st_u'.scratch.work_stk1 new_l.toNat = lit_k.toNat :=
    by rw [hnew_n]; exact coneLift_of_tmk_pair hwlv rfl
  have htake_u' : st_u'.core.tmp.take (cnt + 1#32).toNat =
      st_u.core.tmp.take cnt.toNat ++ [new_l] := by
    have hlen_tk : (st_u.core.tmp.take cnt.toNat).length = cnt.toNat := by simp [htmp_u]; omega
    rw [hcnt1]; dsimp only [st_u']; apply List.ext_getElem; · simp [htmp_u]; omega
    intro j hj1 _; have hj : j < cnt.toNat + 1 := by simp [htmp_u] at hj1; omega
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · rw [List.getElem_take, List.getElem_set_ne (by omega : cnt.toNat ≠ j),
        List.getElem_append_left (by omega), List.getElem_take]
    · simp [List.getElem_take, List.getElem_set_self, List.getElem_append_right, hlen_tk]
  have hcl_vlen : ((fullArenaClauseLits s cr.toNat).map (· / 2)).length = sz.toNat := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    rw [List.length_map, List.length_map, List.length_take, List.length_drop, ← hsz_core]
    exact Nat.min_eq_left (by omega)
  have hne_prev : ∀ j < cnt.toNat,
      (st_k.core.tmp[j]?.getD 0#32).toNat / 2 ≠ ilv := fun j hj heq => by
    obtain ⟨p, hp, hpeq⟩ := hvars_k j hj
    have hj_lt := hlts_k j hj
    have hwk_p := hwku_eq _ (by omega : (st_k.core.tmp[j]?.getD 0#32).toNat / 2 < nv_k.toNat)
    rw [heq] at hwk_p hpeq
    have hvar_eq : (s.core.arena[cr.toNat + 3 + p]?.getD 0#32).toNat / 2 = lit_k.toNat / 2 := by
      rw [hpeq, ← hwk_p, hwlv]
    have hp_v : p < ((fullArenaClauseLits s cr.toNat).map (· / 2)).length := by omega
    have hk_v : k.toNat < ((fullArenaClauseLits s cr.toNat).map (· / 2)).length := by omega
    have hinj := k6_list_nodup_getElem_inj hnd_cl hp_v hk_v
    have hgp : ((fullArenaClauseLits s cr.toNat).map (· / 2))[p]'hp_v =
        (s.core.arena[cr.toNat + 3 + p]?.getD 0#32).toNat / 2 := by
      refine Option.some.inj ?_
      rw [← List.getElem?_eq_getElem hp_v]
      unfold fullArenaClauseLits fullArenaClauseLitsCore
      have hbd_p : cr.toNat + 3 + p < s.core.arena.length := by omega
      rw [List.getElem?_map, List.getElem?_map, List.getElem?_take_of_lt (by omega),
        List.getElem?_drop, List.getElem?_eq_getElem hbd_p]
      simp only [Option.map_some, Option.getD_some]
    have hgk : ((fullArenaClauseLits s cr.toNat).map (· / 2))[k.toNat]'hk_v =
        lit_k.toNat / 2 := by
      refine Option.some.inj ?_
      rw [← List.getElem?_eq_getElem hk_v]
      unfold fullArenaClauseLits fullArenaClauseLitsCore
      have hbd_k : cr.toNat + 3 + k.toNat < s.core.arena.length := by omega
      rw [List.getElem?_map, List.getElem?_map, List.getElem?_take_of_lt (by omega),
        List.getElem?_drop, ← hlit_ar, List.getElem?_eq_getElem hbd_k]
      simp only [Option.map_some, Option.getD_some]
    have hpk := hinj (by rw [hgp, hgk, hvar_eq])
    omega
  refine ⟨hcnt1, ⟨{ hlu.core_ok with tmp_len_arr := by simp [st_u', htmp_u] }, hlu.scratch_ok⟩,
    fun j hj => ?_, fun i hi => ?_, fun j hj => ?_, fun j1 j2 hj1 hj2 hne => ?_⟩
  · rw [hcnt1] at hj; rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · dsimp only [st_u']; rw [List.getElem?_set_ne (by omega : cnt.toNat ≠ j), htmpu_eq]
      exact Nat.lt_of_lt_of_le (hlts_k j hlt) (by omega)
    · dsimp only [st_u']; rw [List.getElem?_set_self (by omega), Option.getD_some]; omega
  · rw [hk1] at hi; rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · rcases hcov_k i hlt with hfals | hmem
      · exact Or.inl hfals
      · right; rw [htake_u', List.map_append]; apply List.mem_append_left
        rcases List.mem_map.mp hmem with ⟨x, hx, heq_l⟩
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
        have hj_cnt : j < cnt.toNat := by simp at hj; omega
        have hx_lt := hlts_k j hj_cnt
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hx_lt
        have hwk_eq_x : st_u.scratch.work_stk1[(st_k.core.tmp[j]'(by omega)).toNat / 2]? =
            st_k.scratch.work_stk1[(st_k.core.tmp[j]'(by omega)).toNat / 2]? :=
          hwku_eq _ (by omega)
        have hel : st_u.core.tmp[j]'(by omega) = st_k.core.tmp[j]'(by omega) := by
          simp only [htmpu_eq]
        refine List.mem_map.mpr ⟨st_u.core.tmp[j]'(by omega), ?_, ?_⟩
        · have hmem' : (st_u.core.tmp.take cnt.toNat)[j]'(by simp [htmp_u]; omega) ∈
              st_u.core.tmp.take cnt.toNat := List.getElem_mem _
          rwa [List.getElem_take] at hmem'
        · rw [List.getElem_take] at heq_l
          dsimp only [m6ConeLift, st_u'] at heq_l ⊢
          rw [hel, hwk_eq_x]; exact heq_l
    · right; rw [htake_u', List.map_append]
      exact List.mem_append_right _ (by simp [hlit_ar, hnew_lift])
  · rw [hcnt1] at hj; rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · obtain ⟨p, hp, hpeq⟩ := hvars_k j hlt
      have hj_lt := hlts_k j hlt
      refine ⟨p, by omega, ?_⟩
      dsimp only [st_u']
      rw [List.getElem?_set_ne (by omega : cnt.toNat ≠ j), htmpu_eq,
        hwku_eq _ (by omega)]
      exact hpeq
    · refine ⟨k.toNat, by rw [hk1]; omega, ?_⟩
      dsimp only [st_u']
      rw [List.getElem?_set_self (by omega), Option.getD_some,
        show new_l.toNat / 2 = ilv by omega, hwlv, hlit_ar]
  · rw [hcnt1] at hj1 hj2
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj1 with h1 | rfl <;>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj2 with h2 | rfl
    · dsimp only [st_u']
      rw [List.getElem?_set_ne (by omega : cnt.toNat ≠ j1),
        List.getElem?_set_ne (by omega : cnt.toNat ≠ j2), htmpu_eq]
      exact hnd_k j1 j2 h1 h2 hne
    · dsimp only [st_u']
      rw [List.getElem?_set_ne (by omega : cnt.toNat ≠ j1),
        List.getElem?_set_self (by omega), Option.getD_some, htmpu_eq,
        show new_l.toNat / 2 = ilv by omega]
      exact hne_prev j1 h1
    · dsimp only [st_u']
      rw [List.getElem?_set_ne (by omega : cnt.toNat ≠ j2),
        List.getElem?_set_self (by omega), Option.getD_some, htmpu_eq,
        show new_l.toNat / 2 = ilv by omega]
      exact (hne_prev j2 h2).symm
    · exact absurd rfl hne

theorem m6_cone_exit_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {L : K6Layout} {s st_e : FullState} {R : Mem 64 → Prop} {Q : Post [i64]}
    {nv nc : BitVec 32} {m : Mem 64}
    (hdw : FullDenseInvW c F0 F_cur s) (hcap : k6MinScr ≤ c.scratch_cap)
    (hL_len : L.scrLen = c.scratch_cap) (hL_mv : L.maxV = k6MaxV c.scratch_cap)
    (hlen_e : st_e.LengthsOk c) (hag_e : AgreesExcept m6ConeMask s st_e)
    (hcone_e : M6ConeInv F_cur L st_e nv.toNat nc.toNat)
    (hm : (K6MemA L (L.kPtr c.pScratchBuf)
        (((((((k6StateOfScratch L st_e.scratch.scratch_buf).putHdr .nv nv).putHdr .unass
          (nv - (k6StateOfScratch L st_e.scratch.scratch_buf).trl_end)).putHdr .qlast
          (nv - 1#32)).putHdr .qsearch (nv - 1#32)).putHdr .qstamp nv).putArr .qnext
          (nv.toNat - 1) 0xFFFFFFFF#32) ⋆ (FullK6Frame c L st_e ⋆ R)) m)
    (hQ : ∀ (r : BitVec 64) (tmp' ws1' tmk' scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState :=
        { s with
          core := { s.core with tmp := tmp' }
          scratch :=
            { s.scratch with work_stk1 := ws1', tarjan_mark := tmk', scratch_buf := scr' } }
      let nv' := (r &&& 0xFFFF#64).toNat
      let nc' := (r >>> 16).toNat
      FullDenseInvW c F0 F_cur s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.core.vals = s.core.vals → s'.core.inconsistent = s.core.inconsistent →
      M6SweepConeOk F_cur s' nv' →
      nc' ≤ 3 * k6MaxV c.scratch_cap → r.toNat = nv' + nc' * 2 ^ 16 →
      (∀ v < s.core.cur_vars, tmk'[v]?.getD 0#32 ≠ 0#32 →
        ∃ i < nv', (ws1'[i]?.getD 0#32).toNat = v) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    Q (nv.setWidth 64 ||| (nc.setWidth 64 <<< (16 : Nat)), ()) m := by
  have hmL := L.hmaxV
  have hscr_e := hcone_e.scr_len
  have hkb_le : L.k6Base ≤ st_e.scratch.scratch_buf.length := by
    rw [hscr_e]; unfold K6Layout.scrLen; omega
  let ks_e := k6StateOfScratch L st_e.scratch.scratch_buf
  have hnv1 : 1 ≤ nv.toNat := hcone_e.nv_ge1
  have hnv_max : nv.toNat ≤ L.maxV := hcone_e.nv_leMax
  have hnc_max : nc.toNat ≤ L.maxOrig := hcone_e.nc_le
  obtain ⟨hinv_f, _, hnv_f⟩ := k6ShrinkNv_preserves_inv hcone_e.k6_inv hcone_e.k6_sync hnv1
    hnv_max hcone_e.k6_nv hcone_e.k6_lvl hcone_e.k6_na hcone_e.k6_bdd hcone_e.k6_trl_bdd
  let ks_f := ((((((ks_e.putHdr .nv nv).putHdr .unass (nv - ks_e.trl_end)).putHdr .qlast
    (nv - 1#32)).putHdr .qsearch (nv - 1#32)).putHdr .qstamp nv)).putArr .qnext
    (nv.toNat - 1) 0xFFFFFFFF#32
  have hsh_f : ks_f.ShapesOk L := hinv_f.shapes
  let scr_f := st_e.scratch.scratch_buf.take L.k6Base ++ ks_f.toSlab
  let s_f : FullState := { st_e with scratch := { st_e.scratch with scratch_buf := scr_f } }
  have hm_join : (FullMem c s_f ⋆ R) m := by
    obtain ⟨_, hkm⟩ := k6MemA_to_mem hm
    exact fullMem_join_k6 hkb_le hsh_f (sep_ac hkm)
  have hscr_f_len : scr_f.length = c.scratch_cap := by
    dsimp only [scr_f]
    rw [List.length_append, List.length_take_of_le hkb_le, ks_f.toSlab_length hsh_f, ← hL_len]
    unfold K6Layout.scrLen; omega
  have hlen_f : s_f.LengthsOk c :=
    ⟨hlen_e.core_ok, { hlen_e.scratch_ok with scratch_buf_len := hscr_f_len }⟩
  have hag_f : AgreesExcept m6ConeMask s s_f := hag_e.update _ (fun _ => rfl)
  have hdw_f := m6ConeMask_preserves_dense hag_f hlen_f hdw
  have htk_len : (st_e.scratch.scratch_buf.take L.k6Base).length = L.k6Base :=
    List.length_take_of_le hkb_le
  have hof_f : k6StateOfScratch L scr_f = ks_f := by
    unfold k6StateOfScratch; dsimp only [scr_f]
    rw [k6_slab_drop_exact _ _ htk_len]
    exact K6State.ofSlab_toSlab hsh_f
  have hK_f : K6ScratchInv (ConeModelSet F_cur st_e.scratch.work_stk1 nv.toNat) scr_f := by
    have hin : K6Inv L (ConeModelSet F_cur st_e.scratch.work_stk1 nv.toNat)
        (k6StateOfScratch L scr_f) := hof_f ▸ hinv_f
    exact hin.to_scratchInv (hscr_f_len.trans hL_len.symm)
      (by rw [hscr_f_len]; exact hL_mv) (by rw [hscr_f_len]; exact hcap)
      (by rw [hscr_f_len]; exact c.hscr)
  have hpk := m6_pack_nv_nc nv nc (by omega) (by unfold K6Layout.maxOrig at hnc_max; omega)
  let r := nv.setWidth 64 ||| (nc.setWidth 64 <<< (16 : Nat))
  have hnv_bv : nv = BitVec.ofNat 32 nv.toNat := BitVec.eq_of_toNat_eq (by simp)
  have hscr_f_ge : k6MinScr ≤ scr_f.length := by rw [hscr_f_len]; exact hcap
  have hscr_f_lt : scr_f.length < dimacsBound := by rw [hscr_f_len]; exact c.hscr
  have hof_can :
      (k6StateOfScratch (k6LayoutOfCap scr_f.length hscr_f_ge hscr_f_lt) scr_f).nv =
        BitVec.ofNat 32 nv.toNat := by
    rw [k6LayoutOfCap_eq (hL_len.trans hscr_f_len.symm) (by rw [hscr_f_len]; exact hL_mv)
      hscr_f_ge hscr_f_lt, hof_f, hnv_f]
    exact BitVec.eq_of_toNat_eq (by simp)
  have hQ' := hQ r st_e.core.tmp st_e.scratch.work_stk1 st_e.scratch.tarjan_mark scr_f m
  rw [← m6ConeMask_state_eq hag_f, hpk.1, hpk.2.1] at hQ'
  refine hQ' hdw_f (hag_e.get (·.core.cur_vars)) (hag_e.get (·.core.fuel))
    (hag_e.get (·.core.vals)) (hag_e.get (·.core.inconsistent))
    ⟨hnv1, by rw [hscr_f_len, ← hL_mv]; exact hnv_max, hcone_e.nv_le_cv,
      fun i hi => (hcone_e.fwd i hi).1, hK_f, ⟨hscr_f_ge, hscr_f_lt, hof_can⟩⟩
    (by rw [← hL_mv]; exact hnc_max) hpk.2.2
    (fun v hv hne => by
      have hcv_e := hag_e.get (·.core.cur_vars)
      rcases hcone_e.rev v (hcv_e.symm ▸ hv) with hz | ⟨i, hi, hwi, _⟩
      · exact absurd hz hne
      · exact ⟨i, hi, hwi⟩)
    hm_join

end LeanQbe.T.Examples.Kissat.FullM6Sweep
