module

public import LeanQbe.T.Examples.Kissat.CorePlusSpec
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Core+` Conflict-Analysis Clause & 1UIP Helpers (`Stage 2`, Part 1)

Builds directly on `CorePlusSpec` to prove:
1. `kissat_analyze_clause_wp` against `corePlusAnalyzeClauseSpec` using `C0Step` (`c0_steps`).
2. Pure 1UIP semantic-resolvent and list-counting helpers (`lowerLits`, `curTrailIdxs`, `curLits`,
   `activeResolvent`, `LowerInv`, `MarksCov`, `analyzeClause_preserves`,
   `clear_marks_restores_marksClear`, `tmp_take_eq_cons_lowerLits`, `swap_tmp_props`) used by
   `CorePlusAnalyzeLemmas`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.CorePlus

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Counting, framing, and local `C0Step` helpers -/

theorem filter_length_flip_one {α : Type} (p p' : α → Bool) (k : α) :
    ∀ (xs : List α), xs.Nodup → k ∈ xs →
      p k = false → p' k = true → (∀ x ∈ xs, x ≠ k → p' x = p x) →
      (xs.filter p').length = (xs.filter p).length + 1
  | [], _, hmem, _, _, _ => by simp at hmem
  | x :: xs, hnd, hmem, hpk, hp'k, hagree => by
    rw [List.nodup_cons] at hnd
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · have hfeq : xs.filter p' = xs.filter p := List.filter_congr fun y hy =>
        hagree y (List.mem_cons_of_mem _ hy) (fun heq => hnd.1 (heq ▸ hy))
      simp [hpk, hp'k, hfeq]
    · have hx := hagree x List.mem_cons_self (fun heq => hnd.1 (heq ▸ hmem'))
      have ih := filter_length_flip_one p p' k xs hnd.2 hmem' hpk hp'k
        fun y hy => hagree y (List.mem_cons_of_mem _ hy)
      cases hp : p x <;> simp [hx, hp, ih] <;> omega

theorem filter_length_eq_zero_of_false {α : Type} {p : α → Bool} {xs : List α}
    (h : ∀ x ∈ xs, p x = false) : (xs.filter p).length = 0 := by
  have hnil : xs.filter p = [] := List.filter_eq_nil_iff.mpr fun x hx => by simp [h x hx]
  simp [hnil]

theorem nodup_length_le_of_subset {α : Type} [DecidableEq α] :
    ∀ {xs ys : List α}, xs.Nodup → (∀ x ∈ xs, x ∈ ys) → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, ys, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have hx : x ∈ ys := hsub x List.mem_cons_self
    have hle := nodup_length_le_of_subset hnd.2 fun y hy =>
      (List.mem_erase_of_ne (by rintro rfl; exact hnd.1 hy)).mpr
        (hsub y (List.mem_cons_of_mem _ hy))
    have := List.length_erase_of_mem hx; have := List.length_pos_of_mem hx
    simp only [List.length_cons]; omega

theorem nodup_length_eq_of_bij {xs ys : List Nat} (f : Nat → Nat)
    (hxs : xs.Nodup) (hys : ys.Nodup)
    (hmap : ∀ x ∈ xs, f x ∈ ys)
    (hinj : ∀ x1 ∈ xs, ∀ x2 ∈ xs, f x1 = f x2 → x1 = x2)
    (hsurj : ∀ y ∈ ys, ∃ x ∈ xs, f x = y) : xs.length = ys.length := by
  have h1 : (xs.map f).length ≤ ys.length :=
    nodup_length_le_of_subset (nodup_map_of_inj hxs hinj) fun y hy => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; exact hmap x hx
  have h2 : ys.length ≤ (xs.map f).length :=
    nodup_length_le_of_subset hys fun y hy => by
      obtain ⟨x, hx, rfl⟩ := hsurj y hy; exact List.mem_map_of_mem hx
  rw [List.length_map] at h1 h2; omega

theorem filter_length_add_of_disj {α : Type} (p1 p2 : α → Bool) :
    ∀ (xs : List α), (∀ x ∈ xs, ¬ (p1 x = true ∧ p2 x = true)) →
      (xs.filter fun x => p1 x || p2 x).length = (xs.filter p1).length + (xs.filter p2).length
  | [], _ => rfl
  | x :: xs, hdisj => by
    have htail := filter_length_add_of_disj p1 p2 xs fun y hy => hdisj y (List.mem_cons_of_mem _ hy)
    have hx := hdisj x List.mem_cons_self
    cases hp1 : p1 x <;> cases hp2 : p2 x <;> simp_all <;> omega

theorem range_succ_filter (n : Nat) (p : Nat → Bool) :
    (List.range (n + 1)).filter p = (List.range n).filter p ++ if p n then [n] else [] := by
  rw [List.range_succ, List.filter_append]; cases hp : p n <;> simp [hp]

theorem CorePlusState.LengthsOk.with_ac {c : CorePlusCfg} {s : CorePlusState}
    (hlen : s.LengthsOk c) {mrk' : List (BitVec 8)} {tmp' : List (BitVec 32)} {tc' tl' : Nat}
    (hm : mrk'.length = c.mv) (ht : tmp'.length = c.mv)
    (htc : tc' < 2 ^ 64) (htl : tl' < 2 ^ 64) :
    ({ s with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl' } :
      CorePlusState).LengthsOk c :=
  { hlen with mrk_len := hm, tmp_len_arr := ht, tmp_cnt_lt := htc, tmp_len_lt := htl }

theorem CorePlusCoreInv.with_ac {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    (hcore : CorePlusCoreInv c F0 s) {mrk' : List (BitVec 8)} {tmp' : List (BitVec 32)}
    {tc' tl' : Nat} (hm : mrk'.length = c.mv) (ht : tmp'.length = c.mv)
    (htc : tc' < 2 ^ 64) (htl : tl' < 2 ^ 64) :
    CorePlusCoreInv c F0 { s with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl' } :=
  { hcore with
    lengths := hcore.lengths.with_ac hm ht htc htl
    clauses := { hcore.clauses with bounds := hcore.clauses.bounds } }

attribute [local bv_c0] bv32_lshr_1

theorem strip_wp {Γ rs Q X e m} (h : wp (rs := rs) Γ Q X e m) : wp Γ Q X e m := h
theorem strip_fwp {as rs Γ f args m Q X} (h : Func.wp (as := as) (rs := rs) Γ f args m Q X) :
    Func.wp Γ f args m Q X := h
theorem strip_le_wp {a b : Nat} {P : Prop} (h : a ≤ b) (hp : P) : a ≤ b ∧ P := ⟨h, hp⟩

/-- `c0_steps` extended to strip `have`-introduced `mdata` and cast width side-conditions. -/
local macro "cp_steps" : tactic =>
  `(tactic| (
    try (first | refine strip_fwp ?_ | refine strip_wp ?_)
    repeat (any_goals (first
      | refine strip_le_wp (by decide) ?_
      | c0_step))))

theorem bv8_zext32_eq0_prop (b : BitVec 8) :
    (b.setWidth 32 = 0#32) = (b = 0#8) :=
  propext (bv8_zext32_eq_zero b)

attribute [local bv_c0] bv8_zext32_eq0_prop

@[local c0_load] private theorem c0_load_cls_off {c : CorePlusCfg} {s : CorePlusState}
    {R : Mem 64 → Prop} {m : Mem 64} {cid : BitVec 32}
    (h : (CorePlusMem c s ⋆ R) m) (hi : 4 * cid.toNat < s.cls.length) :
    loadVal m i32 (c.pClauses + cid.setWidth 64 * 16) = some (s.cls[4 * cid.toNat]'hi) := by
  rw [bv32_mul16_eq]; exact load_arena_cls hi h

@[local c0_load] private theorem c0_load_cls_size {c : CorePlusCfg} {s : CorePlusState}
    {R : Mem 64 → Prop} {m : Mem 64} {cid : BitVec 32}
    (h : (CorePlusMem c s ⋆ R) m) (hi : 4 * cid.toNat + 1 < s.cls.length) :
    loadVal m i32 (c.pClauses + cid.setWidth 64 * 16 + 4) = some (s.cls[4 * cid.toNat + 1]'hi) := by
  rw [bv32_mul16_eq, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ptr_add_ofNat,
    show 4 * (4 * cid.toNat) + 4 = 4 * (4 * cid.toNat + 1) by omega]
  exact load_arena_cls hi h

@[local c0_load] private theorem c0_load_lpool_off {c : CorePlusCfg} {s : CorePlusState}
    {R : Mem 64 → Prop} {m : Mem 64} {off : BitVec 32} {i : BitVec 64}
    (h : (CorePlusMem c s ⋆ R) m) (hi : off.toNat + i.toNat < s.lpool.length) :
    loadVal m i32 (c.pLpool + off.setWidth 64 * 4 + i * 4) =
      some (s.lpool[off.toNat + i.toNat]'hi) := by
  rw [bv32_mul4_eq, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat,
    ptr_add_ofNat, ← Nat.mul_add]
  exact load_arena_lpool hi h

/-! ## 2. `kissat_analyze_clause` `Func.wp` proof -/

private structure AcInv (c : CorePlusCfg) (s : CorePlusState) (cid skip_var off sz : Nat)
    (i : Nat) (mrk' : List (BitVec 8)) (tmp' : List (BitVec 32)) (tc' tl' : Nat) : Prop where
  i_le : i ≤ sz
  mrk_len : mrk'.length = c.mv
  tmp_len_arr : tmp'.length = c.mv
  tl_ge : s.tmp_len ≤ tl'
  tl_le : tl' ≤ c.mv
  tc_ge : s.tmp_cnt ≤ tc'
  mpres : ∀ v < c.mv, s.mrk[v]?.getD 0#8 ≠ 0#8 → mrk'[v]?.getD 0#8 = s.mrk[v]?.getD 0#8
  tpres : ∀ k < s.tmp_len, tmp'[k]? = s.tmp[k]?
  newm : ∀ v < c.mv, s.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
    ∃ l ∈ clauseLits s cid, l / 2 = v ∧ v ≠ skip_var ∧
      0 < (s.lvl[v]?.getD 0#32).toNat ∧ (s.lvl[v]?.getD 0#32).toNat ≤ s.cur_level
  newlow : ∀ v < c.mv, s.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
    (s.lvl[v]?.getD 0#32).toNat < s.cur_level →
    ∃ j, s.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = v
  newt : ∀ j, s.tmp_len ≤ j → j < tl' →
    let l := (tmp'[j]?.getD 0#32).toNat
    l ∈ clauseLits s cid ∧ l < 2 * c.mv ∧ l / 2 ≠ skip_var ∧
    0 < (s.lvl[l / 2]?.getD 0#32).toNat ∧ (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level ∧
    mrk'[l / 2]?.getD 0#8 ≠ 0#8
  cnt : tc' - s.tmp_cnt =
    ((List.range c.mv).filter fun v =>
      decide (s.mrk[v]?.getD 0#8 = 0#8) && decide (mrk'[v]?.getD 0#8 ≠ 0#8) &&
      decide ((s.lvl[v]?.getD 0#32).toNat = s.cur_level)).length
  done : ∀ k < i,
    let l := (s.lpool[off + k]?.getD 0#32).toNat
    l / 2 < c.mv ∧
    (l / 2 ≠ skip_var →
      (0 < (s.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
      (s.mrk[l / 2]?.getD 0#8 = 0#8 →
        (s.lvl[l / 2]?.getD 0#32).toNat ≤ s.cur_level ∧
        (0 < (s.lvl[l / 2]?.getD 0#32).toNat → (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level →
          ∃ j, s.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))

private theorem acInv_step_same {c : CorePlusCfg} {s : CorePlusState} {cid skip_var off sz i : Nat}
    {mrk' : List (BitVec 8)} {tmp' : List (BitVec 32)} {tc' tl' : Nat}
    (h : AcInv c s cid skip_var off sz i mrk' tmp' tc' tl') (hilt : i < sz)
    (hv : (s.lpool[off + i]?.getD 0#32).toNat / 2 < c.mv)
    (hcur : let v := (s.lpool[off + i]?.getD 0#32).toNat / 2
      v ≠ skip_var →
      (0 < (s.lvl[v]?.getD 0#32).toNat → mrk'[v]?.getD 0#8 ≠ 0#8) ∧
      (s.mrk[v]?.getD 0#8 = 0#8 →
        (s.lvl[v]?.getD 0#32).toNat ≤ s.cur_level ∧
        (0 < (s.lvl[v]?.getD 0#32).toNat → (s.lvl[v]?.getD 0#32).toNat < s.cur_level →
          ∃ j, s.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = v))) :
    AcInv c s cid skip_var off sz (i + 1) mrk' tmp' tc' tl' :=
  { h with
    i_le := by omega
    done := fun k hk => by
      by_cases hki : k = i
      · subst hki; exact ⟨hv, hcur⟩
      · exact h.done k (by omega) }

private theorem acInv_step_cur {c : CorePlusCfg} {s : CorePlusState} {cid skip_var off sz i : Nat}
    {mrk' : List (BitVec 8)} {tmp' : List (BitVec 32)} {tc' tl' : Nat} {l_bv : BitVec 32}
    (h : AcInv c s cid skip_var off sz i mrk' tmp' tc' tl') (hilt : i < sz)
    (hl_get : (s.lpool[off + i]?.getD 0#32).toNat = l_bv.toNat)
    (hl_mem : l_bv.toNat ∈ clauseLits s cid) (hvlt : l_bv.toNat / 2 < c.mv)
    (hne : l_bv.toNat / 2 ≠ skip_var)
    (hm0 : mrk'[l_bv.toNat / 2]?.getD 0#8 = 0#8)
    (hsm0 : s.mrk[l_bv.toNat / 2]?.getD 0#8 = 0#8)
    (hpos : 0 < (s.lvl[l_bv.toNat / 2]?.getD 0#32).toNat)
    (heq : (s.lvl[l_bv.toNat / 2]?.getD 0#32).toNat = s.cur_level) :
    AcInv c s cid skip_var off sz (i + 1) (mrk'.set (l_bv.toNat / 2) 1#8) tmp' (tc' + 1) tl' := by
  let v := l_bv.toNat / 2
  have hmget : ∀ w < c.mv,
      (mrk'.set v 1#8)[w]?.getD 0#8 = if w = v then 1#8 else mrk'[w]?.getD 0#8 := fun w hw => by
    by_cases hwe : w = v
    · subst hwe; rw [List.getElem?_set_self (by rw [h.mrk_len]; exact hw)]; simp
    · rw [List.getElem?_set_ne (Ne.symm hwe)]; simp [hwe]
  refine ⟨by omega, by simp [h.mrk_len], h.tmp_len_arr, h.tl_ge, h.tl_le, by have := h.tc_ge; omega,
    fun w hw hnz => by
      rw [hmget w hw]; split
      · subst_vars; exact absurd hsm0 hnz
      · exact h.mpres w hw hnz,
    h.tpres,
    fun w hw hs0 hmnz => by
      rw [hmget w hw] at hmnz; split at hmnz
      · subst_vars; exact ⟨l_bv.toNat, hl_mem, rfl, hne, hpos, by dsimp [v]; omega⟩
      · exact h.newm w hw hs0 hmnz,
    fun w hw hs0 hmnz hlt => by
      rw [hmget w hw] at hmnz; split at hmnz
      · subst_vars; dsimp [v] at hlt; omega
      · exact h.newlow w hw hs0 hmnz hlt,
    fun j hj1 hj2 => by
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.newt j hj1 hj2
      refine ⟨h1, h2, h3, h4, h5, ?_⟩
      rw [hmget _ (by omega)]; split; · decide
      · exact h6,
    ?_, fun k hk => ?_⟩
  · have hflip := filter_length_flip_one
      (fun w => decide (s.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
        decide ((s.lvl[w]?.getD 0#32).toNat = s.cur_level))
      (fun w => decide (s.mrk[w]?.getD 0#8 = 0#8) && decide ((mrk'.set v 1#8)[w]?.getD 0#8 ≠ 0#8) &&
        decide ((s.lvl[w]?.getD 0#32).toNat = s.cur_level))
      v (List.range c.mv) List.nodup_range (List.mem_range.mpr hvlt)
      (by simp [v, hm0]) (by simp [v, hsm0, hmget v hvlt, heq])
      (fun w hw hne => by rw [hmget w (List.mem_range.mp hw), ite_eq_right hne])
    rw [hflip, ← h.cnt]; have := h.tc_ge; omega
  · by_cases hki : k = i
    · subst hki; dsimp only; rw [hl_get]
      refine ⟨hvlt, fun _ =>
        ⟨fun _ => by rw [hmget v hvlt]; simp, fun _ => ⟨by omega, fun _ _ => by omega⟩⟩⟩
    · obtain ⟨hkv, hkrest⟩ := h.done k (by omega)
      refine ⟨hkv, fun hne' => ⟨fun hp => ?_, (hkrest hne').2⟩⟩
      rw [hmget _ hkv]; split; · decide
      · exact (hkrest hne').1 hp

private theorem acInv_step_low {c : CorePlusCfg} {s : CorePlusState} {cid skip_var off sz i : Nat}
    {mrk' : List (BitVec 8)} {tmp' : List (BitVec 32)} {tc' tl' : Nat} {l_bv : BitVec 32}
    (h : AcInv c s cid skip_var off sz i mrk' tmp' tc' tl') (hilt : i < sz) (htl_lt : tl' < c.mv)
    (hl_get : (s.lpool[off + i]?.getD 0#32).toNat = l_bv.toNat)
    (hl_mem : l_bv.toNat ∈ clauseLits s cid) (hvlt : l_bv.toNat / 2 < c.mv)
    (hne : l_bv.toNat / 2 ≠ skip_var)
    (hsm0 : s.mrk[l_bv.toNat / 2]?.getD 0#8 = 0#8)
    (hpos : 0 < (s.lvl[l_bv.toNat / 2]?.getD 0#32).toNat)
    (hlt : (s.lvl[l_bv.toNat / 2]?.getD 0#32).toNat < s.cur_level) :
    AcInv c s cid skip_var off sz (i + 1)
      (mrk'.set (l_bv.toNat / 2) 1#8) (tmp'.set tl' l_bv) tc' (tl' + 1) := by
  let v := l_bv.toNat / 2
  have hmget : ∀ w < c.mv,
      (mrk'.set v 1#8)[w]?.getD 0#8 = if w = v then 1#8 else mrk'[w]?.getD 0#8 := fun w hw => by
    by_cases hwe : w = v
    · subst hwe; rw [List.getElem?_set_self (by rw [h.mrk_len]; exact hw)]; simp
    · rw [List.getElem?_set_ne (Ne.symm hwe)]; simp [hwe]
  have htl_arr : tl' < tmp'.length := by rw [h.tmp_len_arr]; exact htl_lt
  refine ⟨by omega, by simp [h.mrk_len], by simp [h.tmp_len_arr], by have := h.tl_ge; omega,
    by omega, h.tc_ge,
    fun w hw hnz => by
      rw [hmget w hw]; split
      · subst_vars; exact absurd hsm0 hnz
      · exact h.mpres w hw hnz,
    fun k hk => by rw [List.getElem?_set_ne (by have := h.tl_ge; omega)]; exact h.tpres k hk,
    fun w hw hs0 hmnz => by
      rw [hmget w hw] at hmnz; split at hmnz
      · subst_vars; exact ⟨l_bv.toNat, hl_mem, rfl, hne, hpos, by dsimp [v]; omega⟩
      · exact h.newm w hw hs0 hmnz,
    fun w hw hs0 hmnz hlt' => by
      rw [hmget w hw] at hmnz; split at hmnz
      · subst_vars; exact ⟨tl', h.tl_ge, by omega, by rw [List.getElem?_set_self htl_arr]; rfl⟩
      · obtain ⟨j, hj1, hj2, hjeq⟩ := h.newlow w hw hs0 hmnz hlt'
        exact ⟨j, hj1, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hjeq⟩,
    fun j hj1 hj2 => by
      by_cases hje : j = tl'
      · subst hje; rw [List.getElem?_set_self htl_arr, Option.getD_some]
        exact ⟨hl_mem, by omega, hne, hpos, hlt, by rw [hmget v hvlt]; simp⟩
      · rw [List.getElem?_set_ne (Ne.symm hje)]
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.newt j hj1 (by omega)
        refine ⟨h1, h2, h3, h4, h5, ?_⟩
        rw [hmget _ (by omega)]; split; · decide
        · exact h6,
    ?_, fun k hk => ?_⟩
  · rw [h.cnt]; congr 1; apply List.filter_congr; intro w hw
    rw [hmget w (List.mem_range.mp hw)]
    by_cases hwe : w = v
    · subst hwe; simp [show (s.lvl[v]?.getD 0#32).toNat ≠ s.cur_level by dsimp [v]; omega]
    · simp [hwe]
  · by_cases hki : k = i
    · subst hki; dsimp only; rw [hl_get]
      refine ⟨hvlt, fun _ => ⟨fun _ => by rw [hmget v hvlt]; simp, fun _ =>
        ⟨by omega, fun _ _ =>
          ⟨tl', h.tl_ge, by omega, by rw [List.getElem?_set_self htl_arr]; rfl⟩⟩⟩⟩
    · obtain ⟨hkv, hkrest⟩ := h.done k (by omega)
      refine ⟨hkv, fun hne' => ⟨fun hp => ?_, fun hs0 => ?_⟩⟩
      · rw [hmget _ hkv]; split; · decide
        · exact (hkrest hne').1 hp
      · obtain ⟨hle, hlow⟩ := (hkrest hne').2 hs0
        refine ⟨hle, fun hp hlt' => ?_⟩
        obtain ⟨j, hj1, hj2, hjeq⟩ := hlow hp hlt'
        exact ⟨j, hj1, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hjeq⟩

theorem kissat_analyze_clause_wp (Γ : Env) :
    ∀ args m Q X, corePlusAnalyzeClauseSpec args m Q X →
      Func.wp Γ kissat_analyze_clause_body args m Q X := by
  rintro ⟨h, cid, skip_var, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, htl_mv, htc_fit, hm, hQ⟩
  have hmv := c.hmv; have hmc := c.hmax_c; have hlc := c.hlcap
  unfold dimacsBound at hmv hmc hlc
  have hcls_len := hlen.cls_len; have hlp_len := hlen.lpool_len
  have hnc_le := hlen.num_clauses_le; have hll_le := hlen.lit_len_le
  have hret_same : Q (false, ()) m := by
    refine hQ false s.mrk s.tmp s.tmp_cnt s.tmp_len m hlen (Nat.le_refl _) htl_mv (Nat.le_refl _)
      (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ h0 hnz => absurd h0 hnz)
      (fun _ h1 h2 => by omega) ?_ (fun hc => by cases hc) hm
    rw [Nat.sub_self, filter_length_eq_zero_of_false]
    intro v _; by_cases h0 : s.mrk[v]?.getD 0#8 = 0#8 <;> simp [h0]
  cp_steps
  · exact hret_same
  · exact hret_same
  · exact hret_same
  have hcid_lt : cid.toNat < s.num_clauses := by c0_bound
  generalize hoff_def : s.cls[4 * cid.toNat]'(by omega) = off_bv
  generalize hsz_def : s.cls[4 * cid.toNat + 1]'(by omega) = sz_bv
  have hoff_eq : clauseOff s cid.toNat = off_bv.toNat := by
    unfold clauseOff; rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hoff_def]
  have hsz_eq : clauseSize s cid.toNat = sz_bv.toNat := by
    unfold clauseSize; rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hsz_def]
  have hbd : clauseOff s cid.toNat + clauseSize s cid.toNat ≤ s.lit_len := by
    rw [hoff_eq, hsz_eq]; have := off_bv.isLt; have := sz_bv.isLt; c0_bound
  have hbd_lp : clauseOff s cid.toNat + clauseSize s cid.toNat ≤ s.lpool.length := by omega
  have hret_false : ∀ i mrk' tmp' tc' tl' ml,
      AcInv c s cid.toNat skip_var.toNat off_bv.toNat sz_bv.toNat i mrk' tmp' tc' tl' →
      (CorePlusMem c { s with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl' } ⋆ R) ml →
      Q (false, ()) ml := by
    intro i mrk' tmp' tc' tl' ml hi hml
    have hcnt_le : tc' - s.tmp_cnt ≤ c.mv := by
      rw [hi.cnt]; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
    exact hQ false mrk' tmp' tc' tl' ml
      (hlen.with_ac hi.mrk_len hi.tmp_len_arr (by have := hi.tc_ge; omega)
        (by have := hi.tl_le; omega))
      hi.tl_ge hi.tl_le hi.tc_ge hi.mpres hi.tpres hi.newm hi.newt hi.cnt
      (fun hc => by cases hc) hml
  refine wp_loop_inv
    (fun (iv, ()) ml => ∃ mrk' tmp' tc' tl',
      AcInv c s cid.toNat skip_var.toNat off_bv.toNat sz_bv.toNat iv.toNat mrk' tmp' tc' tl' ∧
      (CorePlusMem c { s with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl' } ⋆ R) ml)
    (fun (iv, ()) _ => sz_bv.toNat - iv.toNat) (fun J hJ => ?_) (fun J ⟨iv, ⟨⟩⟩ ml hinv ih => ?_)
  · cp_steps
    refine hJ (0#64, ()) m ⟨s.mrk, s.tmp, s.tmp_cnt, s.tmp_len,
      ⟨Nat.zero_le _, hlen.mrk_len, hlen.tmp_len_arr, Nat.le_refl _, htl_mv, Nat.le_refl _,
        fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ h0 hnz => absurd h0 hnz,
        fun _ _ h0 hnz _ => absurd h0 hnz, fun _ h1 h2 => by omega, ?_,
        fun k hk => by simp at hk⟩, hm⟩
    rw [Nat.sub_self, filter_length_eq_zero_of_false]
    intro v _; by_cases h0 : s.mrk[v]?.getD 0#8 = 0#8 <;> simp [h0]
  · obtain ⟨mrk', tmp', tc', tl', hli, hml⟩ := hinv
    have hm_len := hli.mrk_len; have ht_len := hli.tmp_len_arr
    have hlvl_len := hlen.lvl_len; have hcl_lt := hlen.cur_level_lt
    have hcnt_le : tc' - s.tmp_cnt ≤ c.mv := by
      rw [hli.cnt]; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
    have htl_le := hli.tl_le; have htc_ge := hli.tc_ge; have hi_le := hli.i_le
    have hsz_isLt := sz_bv.isLt; have hoff_isLt := off_bv.isLt
    cp_steps
    · exact hret_false _ _ _ _ _ _ hli hml
    · exact hret_false _ _ _ _ _ _ hli hml
    · -- Branch: `vlvl == cur_lvl` -> mark and increment `tmp_cnt`
      have hilt : iv.toNat < sz_bv.toNat := by c0_bound
      have hl_lt : off_bv.toNat + iv.toNat < s.lpool.length := by omega
      have hvlt_raw : (s.lpool[off_bv.toNat + iv.toNat]'hl_lt).toNat / 2 < c.mv := by c0_bound
      obtain ⟨l_bv, hl_bv⟩ : ∃ x, s.lpool[off_bv.toNat + iv.toNat]'hl_lt = x := ⟨_, rfl⟩
      have hl_eq : (s.lpool[off_bv.toNat + iv.toNat]?.getD 0#32).toNat = l_bv.toNat := by
        rw [List.getElem?_eq_getElem hl_lt, Option.getD_some, hl_bv]
      have hl_mem : l_bv.toNat ∈ clauseLits s cid.toNat :=
        (mem_clauseLits_iff hbd_lp).mpr
          ⟨iv.toNat, by rw [hsz_eq]; exact hilt, by simp [hoff_eq, hl_bv]⟩
      have hvlt : l_bv.toNat / 2 < c.mv := by rwa [hl_bv] at hvlt_raw
      have hv_mod : l_bv.toNat / 2 % 2 ^ 64 = l_bv.toNat / 2 := Nat.mod_eq_of_lt (by omega)
      simp only [hl_bv, hv_mod] at *
      have hne_bv : ¬ (l_bv >>> 1 = skip_var) := by assumption
      have hne : l_bv.toNat / 2 ≠ skip_var.toNat := fun heq => hne_bv (by
        apply BitVec.eq_of_toNat_eq; rw [bv32_lshr_1]; exact heq)
      have hm0_bv : mrk'[l_bv.toNat / 2]'(by omega) = 0#8 := by assumption
      have hm0 : mrk'[l_bv.toNat / 2]?.getD 0#8 = 0#8 := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hm0_bv
      have hsm0 : s.mrk[l_bv.toNat / 2]?.getD 0#8 = 0#8 := by
        by_cases h0 : s.mrk[l_bv.toNat / 2]?.getD 0#8 = 0#8
        · exact h0
        · rw [hli.mpres _ hvlt h0] at hm0; exact absurd hm0 h0
      have hlvl_get : (s.lvl[l_bv.toNat / 2]?.getD 0#32).toNat =
          (s.lvl[l_bv.toNat / 2]'(by omega)).toNat := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have heq_bv : s.lvl[l_bv.toNat / 2]'(by omega) =
          (BitVec.ofNat 64 s.cur_level).setWidth 32 := by assumption
      have hstep := acInv_step_cur hli hilt hl_eq hl_mem
        hvlt hne hm0 hsm0 (by rw [hlvl_get]; c0_bound)
        (by rw [hlvl_get, heq_bv]; simp [bv_c0, Nat.mod_eq_of_lt hcl_lt])
      have hcnt_le' : tc' + 1 - s.tmp_cnt ≤ c.mv := by
        rw [hstep.cnt]; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
      have hiv1 : (iv + 1).toNat = iv.toNat + 1 := by c0_bound
      have htc1 : (BitVec.ofNat 64 tc' + 1).toNat = tc' + 1 := by c0_bound
      have hidx_mrk : ((l_bv >>> 1).setWidth 64).toNat = l_bv.toNat / 2 := by
        rw [bv_c0_zext32_64, bv32_lshr_1]
      refine ih _ _ (by dsimp only; omega) ⟨_, _, _, _, ?_, by assumption⟩
      rw [hiv1, htc1, hidx_mrk]; exact hstep
    · exact hret_false _ _ _ _ _ _ hli hml
    · -- Branch: `0 < vlvl < cur_lvl`, `tmp_len < mv` -> mark and append to `tmp`
      have hilt : iv.toNat < sz_bv.toNat := by c0_bound
      have hl_lt : off_bv.toNat + iv.toNat < s.lpool.length := by omega
      have hvlt_raw : (s.lpool[off_bv.toNat + iv.toNat]'hl_lt).toNat / 2 < c.mv := by c0_bound
      obtain ⟨l_bv, hl_bv⟩ : ∃ x, s.lpool[off_bv.toNat + iv.toNat]'hl_lt = x := ⟨_, rfl⟩
      have hl_eq : (s.lpool[off_bv.toNat + iv.toNat]?.getD 0#32).toNat = l_bv.toNat := by
        rw [List.getElem?_eq_getElem hl_lt, Option.getD_some, hl_bv]
      have hl_mem : l_bv.toNat ∈ clauseLits s cid.toNat :=
        (mem_clauseLits_iff hbd_lp).mpr
          ⟨iv.toNat, by rw [hsz_eq]; exact hilt, by simp [hoff_eq, hl_bv]⟩
      have hvlt : l_bv.toNat / 2 < c.mv := by rwa [hl_bv] at hvlt_raw
      have hv_mod : l_bv.toNat / 2 % 2 ^ 64 = l_bv.toNat / 2 := Nat.mod_eq_of_lt (by omega)
      simp only [hl_bv, hv_mod] at *
      have hne_bv : ¬ (l_bv >>> 1 = skip_var) := by assumption
      have hne : l_bv.toNat / 2 ≠ skip_var.toNat := fun heq => hne_bv (by
        apply BitVec.eq_of_toNat_eq; rw [bv32_lshr_1]; exact heq)
      have hm0_bv : mrk'[l_bv.toNat / 2]'(by omega) = 0#8 := by assumption
      have hm0 : mrk'[l_bv.toNat / 2]?.getD 0#8 = 0#8 := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hm0_bv
      have hsm0 : s.mrk[l_bv.toNat / 2]?.getD 0#8 = 0#8 := by
        by_cases h0 : s.mrk[l_bv.toNat / 2]?.getD 0#8 = 0#8
        · exact h0
        · rw [hli.mpres _ hvlt h0] at hm0; exact absurd hm0 h0
      have hlvl_get : (s.lvl[l_bv.toNat / 2]?.getD 0#32).toNat =
          (s.lvl[l_bv.toNat / 2]'(by omega)).toNat := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hne_bv_cl : ¬ (s.lvl[l_bv.toNat / 2]'(by omega) =
          (BitVec.ofNat 64 s.cur_level).setWidth 32) := by assumption
      have hne_cl : (s.lvl[l_bv.toNat / 2]'(by omega)).toNat ≠ s.cur_level := fun heq =>
        hne_bv_cl (by
          apply BitVec.eq_of_toNat_eq
          simp [bv_c0, Nat.mod_eq_of_lt hcl_lt, heq])
      have hvl_le : (s.lvl[l_bv.toNat / 2]'(by omega)).toNat ≤ s.cur_level := by c0_bound
      have hvl_pos : 0 < (s.lvl[l_bv.toNat / 2]'(by omega)).toNat := by c0_bound
      have hstep := acInv_step_low hli hilt (by c0_bound) hl_eq hl_mem
        hvlt hne hsm0 (by rw [hlvl_get]; exact hvl_pos) (by rw [hlvl_get]; omega)
      have hiv1 : (iv + 1).toNat = iv.toNat + 1 := by c0_bound
      have htl1 : (BitVec.ofNat 64 tl' + 1).toNat = tl' + 1 := by c0_bound
      have htl0 : (BitVec.ofNat 64 tl').toNat = tl' := by c0_bound
      have hidx_mrk : ((l_bv >>> 1).setWidth 64).toNat = l_bv.toNat / 2 := by
        rw [bv_c0_zext32_64, bv32_lshr_1]
      refine ih _ _ (by dsimp only; omega) ⟨_, _, _, _, ?_, by assumption⟩
      rw [hiv1, htl1, htl0, hidx_mrk]; exact hstep
    · -- Branch: `vlvl == 0`
      have hilt : iv.toNat < sz_bv.toNat := by c0_bound
      have hl_lt : off_bv.toNat + iv.toNat < s.lpool.length := by omega
      have hvlt_raw : (s.lpool[off_bv.toNat + iv.toNat]'hl_lt).toNat / 2 < c.mv := by c0_bound
      obtain ⟨l_bv, hl_bv⟩ : ∃ x, s.lpool[off_bv.toNat + iv.toNat]'hl_lt = x := ⟨_, rfl⟩
      have hl_eq : (s.lpool[off_bv.toNat + iv.toNat]?.getD 0#32).toNat = l_bv.toNat := by
        rw [List.getElem?_eq_getElem hl_lt, Option.getD_some, hl_bv]
      have hvlt : l_bv.toNat / 2 < c.mv := by rwa [hl_bv] at hvlt_raw
      have hv_mod : l_bv.toNat / 2 % 2 ^ 64 = l_bv.toNat / 2 := Nat.mod_eq_of_lt (by omega)
      simp only [hl_bv, hv_mod] at *
      have hstep := acInv_step_same hli hilt (by rw [hl_eq]; exact hvlt) (fun _ => by
        rw [hl_eq, List.getElem?_eq_getElem (by omega), Option.getD_some]
        have hlvl0 : (s.lvl[l_bv.toNat / 2]'(by omega)).toNat = 0 := by c0_bound
        exact ⟨fun hp => by omega, fun _ => ⟨by omega, fun hp => by omega⟩⟩)
      have hiv1 : (iv + 1).toNat = iv.toNat + 1 := by c0_bound
      refine ih _ _ (by dsimp only; omega) ⟨_, _, _, _, ?_, hml⟩
      rw [hiv1]; exact hstep
    · -- Branch: `mrk[v] != 0`
      have hilt : iv.toNat < sz_bv.toNat := by c0_bound
      have hl_lt : off_bv.toNat + iv.toNat < s.lpool.length := by omega
      have hvlt_raw : (s.lpool[off_bv.toNat + iv.toNat]'hl_lt).toNat / 2 < c.mv := by c0_bound
      obtain ⟨l_bv, hl_bv⟩ : ∃ x, s.lpool[off_bv.toNat + iv.toNat]'hl_lt = x := ⟨_, rfl⟩
      have hl_eq : (s.lpool[off_bv.toNat + iv.toNat]?.getD 0#32).toNat = l_bv.toNat := by
        rw [List.getElem?_eq_getElem hl_lt, Option.getD_some, hl_bv]
      have hvlt : l_bv.toNat / 2 < c.mv := by rwa [hl_bv] at hvlt_raw
      have hv_mod : l_bv.toNat / 2 % 2 ^ 64 = l_bv.toNat / 2 := Nat.mod_eq_of_lt (by omega)
      simp only [hl_bv, hv_mod] at *
      have hmnz_bv : ¬ mrk'[l_bv.toNat / 2]'(by omega) = 0#8 := by assumption
      have hmnz : mrk'[l_bv.toNat / 2]?.getD 0#8 ≠ 0#8 := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hmnz_bv
      have hstep := acInv_step_same hli hilt (by rw [hl_eq]; exact hvlt) (fun _ => by
        rw [hl_eq]; refine ⟨fun _ => hmnz, fun hs0 => ?_⟩
        obtain ⟨_, _, _, _, _, hle⟩ := hli.newm _ hvlt hs0 hmnz
        exact ⟨hle, fun _ hlt => hli.newlow _ hvlt hs0 hmnz hlt⟩)
      have hiv1 : (iv + 1).toNat = iv.toNat + 1 := by c0_bound
      refine ih _ _ (by dsimp only; omega) ⟨_, _, _, _, ?_, hml⟩
      rw [hiv1]; exact hstep
    · -- Branch: `v == skip_var`
      have hilt : iv.toNat < sz_bv.toNat := by c0_bound
      have hl_lt : off_bv.toNat + iv.toNat < s.lpool.length := by omega
      have hvlt_raw : (s.lpool[off_bv.toNat + iv.toNat]'hl_lt).toNat / 2 < c.mv := by c0_bound
      obtain ⟨l_bv, hl_bv⟩ : ∃ x, s.lpool[off_bv.toNat + iv.toNat]'hl_lt = x := ⟨_, rfl⟩
      have hl_eq : (s.lpool[off_bv.toNat + iv.toNat]?.getD 0#32).toNat = l_bv.toNat := by
        rw [List.getElem?_eq_getElem hl_lt, Option.getD_some, hl_bv]
      have hvlt : l_bv.toNat / 2 < c.mv := by rwa [hl_bv] at hvlt_raw
      simp only [hl_bv] at *
      have heq_bv : l_bv >>> 1 = skip_var := by assumption
      have hstep := acInv_step_same hli hilt (by rw [hl_eq]; exact hvlt) (fun hne => by
        have := congrArg BitVec.toNat heq_bv; rw [bv32_lshr_1] at this; rw [hl_eq] at hne; omega)
      have hiv1 : (iv + 1).toNat = iv.toNat + 1 := by c0_bound
      refine ih _ _ (by dsimp only; omega) ⟨_, _, _, _, ?_, hml⟩
      rw [hiv1]; exact hstep
    · -- Loop exit: `iv ≥ sz`, return `true`
      refine hQ true mrk' tmp' tc' tl' ml
        (hlen.with_ac hm_len ht_len (by omega) (by omega))
        hli.tl_ge htl_le htc_ge hli.mpres hli.tpres hli.newm hli.newt hli.cnt ?_ hml
      intro _
      refine ⟨hcid_lt, hbd, fun l hl => ?_⟩
      obtain ⟨k, hk, hget⟩ := (mem_clauseLits_iff hbd_lp).mp hl
      have hk' : k < iv.toNat := by rw [hsz_eq] at hk; c0_bound
      have hget' : (s.lpool[off_bv.toNat + k]?.getD 0#32).toNat = l := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; simpa [hoff_eq] using hget
      simpa [hget'] using hli.done k hk'

/-! ## 3. Pure 1UIP semantic-resolvent helpers -/

/-- Lower-level literals accumulated in `tmp[1 ..< tl)`. -/
def lowerLits (tmp : List (BitVec 32)) (tl : Nat) : List Nat :=
  ((tmp.drop 1).take (tl - 1)).map BitVec.toNat

/-- Marked current-level trail indices strictly below `idx`. -/
def curTrailIdxs (s : CorePlusState) (mrk : List (BitVec 8)) (idx : Nat) : List Nat :=
  (List.range idx).filter fun j =>
    let v := (s.trl[j]?.getD 0#32).toNat / 2
    decide (mrk[v]?.getD 0#8 ≠ 0#8) && decide ((s.lvl[v]?.getD 0#32).toNat = s.cur_level)

/-- Negated marked current-level trail literals strictly below `idx`. -/
def curLits (s : CorePlusState) (mrk : List (BitVec 8)) (idx : Nat) : List Nat :=
  (curTrailIdxs s mrk idx).map fun j => (s.trl[j]?.getD 0#32).toNat ^^^ 1

/-- Active 1UIP resolvent clause (`lowerLits ++ curLits`). -/
def activeResolvent (s : CorePlusState) (tmp : List (BitVec 32)) (mrk : List (BitVec 8))
    (tl idx : Nat) : List Nat :=
  lowerLits tmp tl ++ curLits s mrk idx

/-- Well-formedness of lower-level literals in `tmp[1 ..< tl)`. -/
def LowerInv (c : CorePlusCfg) (s : CorePlusState) (tmp : List (BitVec 32))
    (mrk : List (BitVec 8)) (tl : Nat) : Prop :=
  ∀ j, 1 ≤ j → j < tl →
    let l := (tmp[j]?.getD 0#32).toNat
    l < 2 * c.mv ∧ s.vals[l]?.getD 0#8 = 0xFF#8 ∧
    0 < (s.lvl[l / 2]?.getD 0#32).toNat ∧ (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level ∧
    mrk[l / 2]?.getD 0#8 ≠ 0#8

/-- Coverage of all nonzero entries in `mrk` by `tmp[1 ..< tl)` or `cur_level` trail entries. -/
def MarksCov (c : CorePlusCfg) (s : CorePlusState) (tmp : List (BitVec 32))
    (mrk : List (BitVec 8)) (tl : Nat) : Prop :=
  ∀ v < c.mv, mrk[v]?.getD 0#8 ≠ 0#8 →
    (∃ j, 1 ≤ j ∧ j < tl ∧ (tmp[j]?.getD 0#32).toNat / 2 = v) ∨
    (∃ j < s.trail_end, (s.trl[j]?.getD 0#32).toNat / 2 = v ∧
      (s.lvl[v]?.getD 0#32).toNat = s.cur_level)

theorem mem_lowerLits_iff {tmp : List (BitVec 32)} {tl l : Nat}
    (h1 : 1 ≤ tl) (hle : tl ≤ tmp.length) :
    l ∈ lowerLits tmp tl ↔ ∃ j, 1 ≤ j ∧ j < tl ∧ (tmp[j]?.getD 0#32).toNat = l := by
  unfold lowerLits; rw [List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hx
    have hklt : k < tl - 1 := by rw [List.length_take, List.length_drop] at hk; omega
    rw [List.getElem_take, List.getElem_drop] at hget
    exact ⟨1 + k, by omega, by omega,
      by rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]⟩
  · rintro ⟨j, hj1, hjlt, hget⟩
    have hlt : j - 1 < ((tmp.drop 1).take (tl - 1)).length := by
      rw [List.length_take, List.length_drop]; omega
    refine ⟨tmp[j]'(by omega), ?_,
      by rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hget⟩
    simpa [List.getElem_take, List.getElem_drop, Nat.add_comm, show 1 + (j - 1) = j by omega] using
      List.getElem_mem hlt

theorem curTrailIdxs_succ_true {s : CorePlusState} {mrk : List (BitVec 8)} {idx : Nat}
    (hm : mrk[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8)
    (hl : (s.lvl[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.cur_level) :
    curTrailIdxs s mrk (idx + 1) = curTrailIdxs s mrk idx ++ [idx] := by
  unfold curTrailIdxs; rw [range_succ_filter]; simp [hm, hl]

theorem curTrailIdxs_succ_false {s : CorePlusState} {mrk : List (BitVec 8)} {idx : Nat}
    (h : ¬ (mrk[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
      (s.lvl[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.cur_level)) :
    curTrailIdxs s mrk (idx + 1) = curTrailIdxs s mrk idx := by
  unfold curTrailIdxs; rw [range_succ_filter]
  by_cases h1 : mrk[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8
  · simp [h1, show (s.lvl[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠ s.cur_level from
      fun he => h ⟨h1, he⟩]
  · simp [h1]

theorem curLits_succ_true {s : CorePlusState} {mrk : List (BitVec 8)} {idx : Nat}
    (hm : mrk[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8)
    (hl : (s.lvl[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.cur_level) :
    curLits s mrk (idx + 1) = curLits s mrk idx ++ [(s.trl[idx]?.getD 0#32).toNat ^^^ 1] := by
  unfold curLits; rw [curTrailIdxs_succ_true hm hl, List.map_append]; rfl

theorem curLits_succ_false {s : CorePlusState} {mrk : List (BitVec 8)} {idx : Nat}
    (h : ¬ (mrk[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
      (s.lvl[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.cur_level)) :
    curLits s mrk (idx + 1) = curLits s mrk idx := by
  unfold curLits; rw [curTrailIdxs_succ_false h]

/-- Bridge from `corePlusAnalyzeClauseSpec` (`ok = true`) to the 1UIP analysis invariant. -/
theorem analyzeClause_preserves {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    (hcore : CorePlusCoreInv c F0 s)
    {mrk mrk' : List (BitVec 8)} {tmp tmp' : List (BitVec 32)}
    {tc tc' tl tl' idx cid skip_var : Nat}
    (hidx : idx ≤ s.trail_end) (h1 : 1 ≤ tl) (htl_le : tl ≤ tl') (htl'_mv : tl' ≤ c.mv)
    (ht_len : tmp.length = c.mv) (ht'_len : tmp'.length = c.mv)
    (htc_eq : tc = (curTrailIdxs s mrk idx).length) (htc_le : tc ≤ tc')
    (hlow : LowerInv c s tmp mrk tl) (hcov : MarksCov c s tmp mrk tl)
    (hcid : cid < s.num_clauses)
    (hclause : ∀ q ∈ clauseLits s cid,
      q / 2 = skip_var ∨ ∃ k < idx, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1)
    (hmpres : ∀ v < c.mv, mrk[v]?.getD 0#8 ≠ 0#8 → mrk'[v]?.getD 0#8 = mrk[v]?.getD 0#8)
    (htpres : ∀ k < tl, tmp'[k]? = tmp[k]?)
    (hnewm : ∀ v < c.mv, mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
      ∃ l ∈ clauseLits s cid, l / 2 = v ∧ v ≠ skip_var ∧
        0 < (s.lvl[v]?.getD 0#32).toNat ∧ (s.lvl[v]?.getD 0#32).toNat ≤ s.cur_level)
    (hnewt : ∀ j, tl ≤ j → j < tl' →
      let l := (tmp'[j]?.getD 0#32).toNat
      l ∈ clauseLits s cid ∧ l < 2 * c.mv ∧ l / 2 ≠ skip_var ∧
      0 < (s.lvl[l / 2]?.getD 0#32).toNat ∧ (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level ∧
      mrk'[l / 2]?.getD 0#8 ≠ 0#8)
    (hcnt : tc' - tc =
      ((List.range c.mv).filter fun v =>
        decide (mrk[v]?.getD 0#8 = 0#8) && decide (mrk'[v]?.getD 0#8 ≠ 0#8) &&
        decide ((s.lvl[v]?.getD 0#32).toNat = s.cur_level)).length)
    (hall : ∀ l ∈ clauseLits s cid,
      l / 2 < c.mv ∧
      (l / 2 ≠ skip_var →
        (0 < (s.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
        (mrk[l / 2]?.getD 0#8 = 0#8 →
          (s.lvl[l / 2]?.getD 0#32).toNat ≤ s.cur_level ∧
          (0 < (s.lvl[l / 2]?.getD 0#32).toNat → (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level →
            ∃ j, tl ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))) :
    tc' = (curTrailIdxs s mrk' idx).length ∧
    LowerInv c s tmp' mrk' tl' ∧ MarksCov c s tmp' mrk' tl' ∧
    (∀ l ∈ lowerLits tmp tl, l ∈ lowerLits tmp' tl') ∧
    (∀ l ∈ curLits s mrk idx, l ∈ curLits s mrk' idx) ∧
    (∀ q ∈ clauseLits s cid,
      q / 2 = skip_var ∨ q ∈ activeResolvent s tmp' mrk' tl' idx ∨
        F0.EntailsClause (cnfClause [litNeg q])) := by
  have hlow' : LowerInv c s tmp' mrk' tl' := fun j hj1 hjlt => by
    by_cases hjold : j < tl
    · rw [htpres j hjold]
      obtain ⟨h1', h2', h3', h4', h5'⟩ := hlow j hj1 hjold
      exact ⟨h1', h2', h3', h4', by rw [hmpres _ (by omega) h5']; exact h5'⟩
    · obtain ⟨hmem, hlt, hne, hpos, hcl, hmk⟩ := hnewt j (by omega) hjlt
      rcases hclause _ hmem with heq | ⟨k, hk, hkeq⟩
      · exact absurd heq hne
      · exact ⟨hlt, (hcore.vals_false_iff _ hlt).mpr ⟨k, by omega, hkeq⟩, hpos, hcl, hmk⟩
  have hcov' : MarksCov c s tmp' mrk' tl' := fun v hv hnz' => by
    by_cases hv0 : mrk[v]?.getD 0#8 = 0#8
    · obtain ⟨l, hlmem, rfl, hne, hpos, hle⟩ := hnewm v hv hv0 hnz'
      by_cases hcl : (s.lvl[l / 2]?.getD 0#32).toNat = s.cur_level
      · rcases hclause l hlmem with heq | ⟨k, hk, hkeq⟩
        · exact absurd heq hne
        · exact Or.inr ⟨k, by omega, by rw [hkeq]; exact litVar_litNeg l, hcl⟩
      · obtain ⟨j, hj1, hj2, hjeq⟩ := ((hall l hlmem).2 hne).2 hv0 |>.2 hpos (by omega)
        exact Or.inl ⟨j, by omega, hj2, hjeq⟩
    · rcases hcov v hv hv0 with ⟨j, hj1, hj2, hjeq⟩ | htrl
      · exact Or.inl ⟨j, hj1, by omega, by rw [htpres j hj2]; exact hjeq⟩
      · exact Or.inr htrl
  have htc' : tc' = (curTrailIdxs s mrk' idx).length := by
    let pOld : Nat → Bool := fun j =>
      let v := (s.trl[j]?.getD 0#32).toNat / 2
      decide (mrk[v]?.getD 0#8 ≠ 0#8) && decide ((s.lvl[v]?.getD 0#32).toNat = s.cur_level)
    let pNew : Nat → Bool := fun j =>
      let v := (s.trl[j]?.getD 0#32).toNat / 2
      decide (mrk[v]?.getD 0#8 = 0#8) && decide (mrk'[v]?.getD 0#8 ≠ 0#8) &&
        decide ((s.lvl[v]?.getD 0#32).toNat = s.cur_level)
    have hsplit : curTrailIdxs s mrk' idx =
        (List.range idx).filter (fun j => pOld j || pNew j) := by
      unfold curTrailIdxs; apply List.filter_congr; intro j hj
      have hjlt : j < idx := List.mem_range.mp hj
      have hvlt : (s.trl[j]?.getD 0#32).toNat / 2 < c.mv := by
        have := hcore.trail_lits_lt j (by omega); omega
      dsimp only [pOld, pNew]
      by_cases h0 : mrk[(s.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8
      · simp [h0]
      · rw [hmpres _ hvlt h0]; simp [h0]
    have hadd : (curTrailIdxs s mrk' idx).length =
        ((List.range idx).filter pOld).length + ((List.range idx).filter pNew).length := by
      rw [hsplit]
      exact filter_length_add_of_disj pOld pNew (List.range idx) fun j _ ⟨h1, h2⟩ => by
        simp [pOld, pNew] at h1 h2; exact h1.1 h2.1.1
    have hbij : ((List.range idx).filter pNew).length =
        ((List.range c.mv).filter fun v =>
          decide (mrk[v]?.getD 0#8 = 0#8) && decide (mrk'[v]?.getD 0#8 ≠ 0#8) &&
          decide ((s.lvl[v]?.getD 0#32).toNat = s.cur_level)).length := by
      refine nodup_length_eq_of_bij (fun j => (s.trl[j]?.getD 0#32).toNat / 2)
        (List.Nodup.sublist List.filter_sublist List.nodup_range)
        (List.Nodup.sublist List.filter_sublist List.nodup_range) (fun j hj => ?_)
        (fun j1 hj1 j2 hj2 heq => ?_) (fun v hv => ?_)
      · rw [List.mem_filter, List.mem_range] at hj ⊢
        exact ⟨by have := hcore.trail_lits_lt j (by omega); omega, hj.2⟩
      · rw [List.mem_filter, List.mem_range] at hj1 hj2
        exact hcore.trail_vars_nodup j1 j2 (by omega) (by omega) heq
      · rw [List.mem_filter, List.mem_range] at hv
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
        obtain ⟨hvlt, ⟨hm0, hmnz'⟩, hcl⟩ := hv
        obtain ⟨l, hlmem, rfl, hne, _, _⟩ := hnewm v hvlt hm0 hmnz'
        rcases hclause l hlmem with heq | ⟨k, hk, hkeq⟩
        · exact absurd heq hne
        · have hkvar : (s.trl[k]?.getD 0#32).toNat / 2 = l / 2 := by
            rw [hkeq]; exact litVar_litNeg l
          exact ⟨k, List.mem_filter.mpr
            ⟨List.mem_range.mpr hk, by simp [pNew, hkvar, hm0, hmnz', hcl]⟩, hkvar⟩
    have hold_eq : ((List.range idx).filter pOld).length = tc := htc_eq.symm
    omega
  refine ⟨htc', hlow', hcov', fun l hl => ?_, fun l hl => ?_, fun q hq => ?_⟩
  · obtain ⟨j, hj1, hj2, hget⟩ := (mem_lowerLits_iff h1 (by omega)).mp hl
    exact (mem_lowerLits_iff (by omega) (by omega)).mpr
      ⟨j, hj1, by omega, by rw [htpres j hj2]; exact hget⟩
  · unfold curLits curTrailIdxs at hl ⊢
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl
    rw [List.mem_filter, List.mem_range] at hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
    have hvlt : (s.trl[j]?.getD 0#32).toNat / 2 < c.mv := by
      have := hcore.trail_lits_lt j (by omega); omega
    exact List.mem_map.mpr ⟨j, List.mem_filter.mpr ⟨List.mem_range.mpr hj.1,
      by simp [hmpres _ hvlt hj.2.1, hj.2.1, hj.2.2]⟩, rfl⟩
  · rcases hclause q hq with heq | ⟨k, hk, hkeq⟩
    · exact Or.inl heq
    · by_cases hskip : q / 2 = skip_var
      · exact Or.inl hskip
      · right
        have hqlt : q < 2 * c.mv := hcore.clauses.lits_lt cid hcid q hq
        have hq_fals : s.vals[q]?.getD 0#8 = 0xFF#8 :=
          (hcore.vals_false_iff q hqlt).mpr ⟨k, by omega, hkeq⟩
        have hkvar : (s.trl[k]?.getD 0#32).toNat / 2 = q / 2 := by rw [hkeq]; exact litVar_litNeg q
        by_cases hvl0 : (s.lvl[q / 2]?.getD 0#32).toNat = 0
        · right; have hs0 := hcore.level0_sound k (by omega) (by rw [hkvar]; exact hvl0)
          rwa [hkeq] at hs0
        · left
          have hq_mrk' : mrk'[q / 2]?.getD 0#8 ≠ 0#8 := ((hall q hq).2 hskip).1 (by omega)
          by_cases hcl : (s.lvl[q / 2]?.getD 0#32).toNat = s.cur_level
          · apply List.mem_append_right
            refine List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_range.mpr hk,
              by simp [hkvar, hq_mrk', hcl]⟩, by rw [hkeq]; exact litNeg_litNeg q⟩
          · apply List.mem_append_left
            rw [mem_lowerLits_iff (by omega) (by omega)]
            rcases hcov' (q / 2) (by omega) hq_mrk' with ⟨j, hj1, hj2, hjeq⟩ | ⟨_, _, _, hbad⟩
            · obtain ⟨hl_lt, hl_fals, _, _, _⟩ := hlow' j hj1 hj2
              exact ⟨j, hj1, hj2, hcore.falsified_lit_unique hl_lt hqlt hjeq hl_fals hq_fals⟩
            · omega

/-- `kissat_clear_marks(h, idx)` restores `MarksClear` once `curTrailIdxs s mrk idx = []`. -/
theorem clear_marks_restores_marksClear {c : CorePlusCfg} {s : CorePlusState}
    {tmp : List (BitVec 32)} {mrk mrk' : List (BitVec 8)} {tl idx : Nat}
    (hcov : MarksCov c s tmp mrk tl) (hzero : (curTrailIdxs s mrk idx).length = 0)
    (hpres : ∀ v < c.mv, mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 = 0#8)
    (hclrt : ∀ i, 1 ≤ i → i < tl → (tmp[i]?.getD 0#32).toNat / 2 < c.mv →
      mrk'[(tmp[i]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8)
    (hclrr : ∀ j, idx ≤ j → j < s.trail_end → (s.trl[j]?.getD 0#32).toNat / 2 < c.mv →
      mrk'[(s.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8) :
    ∀ v < c.mv, mrk'[v]?.getD 0#8 = 0#8 := fun v hv => by
  by_cases hm0 : mrk[v]?.getD 0#8 = 0#8
  · exact hpres v hv hm0
  · rcases hcov v hv hm0 with ⟨i, hi1, hilt, hveq⟩ | ⟨j, hjlt, hveq, hcl⟩
    · rw [← hveq]; exact hclrt i hi1 hilt (by omega)
    · have hjge : idx ≤ j := by
        by_cases hlt : j < idx
        · exfalso
          have hmem : j ∈ curTrailIdxs s mrk idx :=
            List.mem_filter.mpr ⟨List.mem_range.mpr hlt, by simp [hveq, hm0, hcl]⟩
          have := List.length_pos_of_mem hmem; omega
        · omega
      rw [← hveq]; exact hclrr j hjge hjlt (by omega)

theorem tmp_take_eq_cons_lowerLits {tmp : List (BitVec 32)} {tl : Nat} {uip : BitVec 32}
    (h1 : 1 ≤ tl) (_hle : tl ≤ tmp.length) (h0 : tmp[0]? = some uip) :
    (tmp.take tl).map BitVec.toNat = uip.toNat :: lowerLits tmp tl := by
  unfold lowerLits
  cases tmp with
  | nil => simp at h0
  | cons x xs =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0; subst h0
    cases tl with
    | zero => omega
    | succ k => simp [List.take_succ_cons]

theorem swap_tmp_props {tmp : List (BitVec 32)} {tl max_idx : Nat} {uip : BitVec 32}
    (h2 : 2 ≤ tl) (hle : tl ≤ tmp.length) (_hm1 : 1 ≤ max_idx) (hmlt : max_idx < tl)
    (h0 : tmp[0]? = some uip) :
    let w1 := tmp[1]'(by omega)
    let wm := tmp[max_idx]'(by omega)
    let tmp_sw := (tmp.set 1 wm).set max_idx w1
    (∀ l, l ∈ (tmp_sw.take tl).map BitVec.toNat ↔ l ∈ (tmp.take tl).map BitVec.toNat) ∧
    (∀ l ∈ (tmp_sw.take tl).map BitVec.toNat,
      l = uip.toNat ∨ ∃ j, 1 ≤ j ∧ j < tl ∧ (tmp[j]?.getD 0#32).toNat = l) := by
  intro w1 wm tmp_sw
  have hmem_take : ∀ (xs : List (BitVec 32)), tl ≤ xs.length → ∀ l,
      l ∈ (xs.take tl).map BitVec.toNat ↔ ∃ j, j < tl ∧ (xs[j]?.getD 0#32).toNat = l := by
    intro xs hxs l; rw [List.mem_map]; constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hx
      have hjlt : j < tl := by rw [List.length_take] at hj; omega
      rw [List.getElem_take] at hget
      exact ⟨j, hjlt, by rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]⟩
    · rintro ⟨j, hj, hget⟩
      have hj' : j < (xs.take tl).length := by rw [List.length_take]; omega
      exact ⟨xs[j]'(by omega), by simpa [List.getElem_take] using List.getElem_mem hj',
        by rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hget⟩
  have hiff : ∀ l, l ∈ (tmp_sw.take tl).map BitVec.toNat ↔ l ∈ (tmp.take tl).map BitVec.toNat := by
    intro l; rw [hmem_take tmp_sw (by simp [tmp_sw]; omega), hmem_take tmp hle]; constructor
    · rintro ⟨j, hj, hget⟩
      by_cases hjm : j = max_idx
      · subst j; rw [List.getElem?_set_self (by simp; omega), Option.getD_some] at hget
        exact ⟨1, by omega,
          by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hget⟩
      · rw [List.getElem?_set_ne (Ne.symm hjm)] at hget
        by_cases hj1 : j = 1
        · subst j; rw [List.getElem?_set_self (by omega), Option.getD_some] at hget
          exact ⟨max_idx, hmlt,
            by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hget⟩
        · rw [List.getElem?_set_ne (Ne.symm hj1)] at hget; exact ⟨j, hj, hget⟩
    · rintro ⟨j, hj, hget⟩
      by_cases hj1 : j = 1
      · subst j; refine ⟨max_idx, hmlt, ?_⟩
        rw [List.getElem?_set_self (by simp; omega), Option.getD_some]
        rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hget
      · by_cases hjm : j = max_idx
        · subst j; refine ⟨1, by omega, ?_⟩
          rw [List.getElem?_set_ne hj1, List.getElem?_set_self (by omega), Option.getD_some]
          rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hget
        · refine ⟨j, hj, ?_⟩
          rw [List.getElem?_set_ne (Ne.symm hjm), List.getElem?_set_ne (Ne.symm hj1)]; exact hget
  refine ⟨hiff, fun l hl => ?_⟩
  obtain ⟨j, hj, hget⟩ := (hmem_take tmp hle l).mp ((hiff l).mp hl)
  cases j with
  | zero => rw [h0, Option.getD_some] at hget; exact Or.inl hget.symm
  | succ k => exact Or.inr ⟨k + 1, by omega, hj, hget⟩

end LeanQbe.T.Examples.Kissat.CorePlus
