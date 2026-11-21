module

public import LeanQbe.T.Examples.Kissat.FullIngestLemmas1

/-!
# Kissat `D-Full` Stage-4 Chronological Backtrack Proof (`FullIngestLemmas2`)

Proves `full_backtrack_preserves_otfsWitness` (supporting both `FullWitnessInv` and
`FullOtfsWitnessInv` when backtracking below `cur_level`) and the parametric `(Γ : Env)`
theorem `full_backtrack_wp`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat Kraken.Bedrock2.Test

open scoped FullArenaTactics FullIngestTactics
open FullIngestSpecs

/-! ## 1. `full_backtrack` invariant & trail-compaction helpers -/

private theorem fullWitnessInv_subst_lvl_rsns {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k' : FullCoreState} {lvl0 rsns0 : List (BitVec 32)}
    (hw : FullWitnessInv c F0 F_cur { k' with lvl := lvl0, rsns := rsns0 })
    (hlvl : ∀ i < k'.trail_end,
      k'.lvl[(k'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 =
        lvl0[(k'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32)
    (hrsn : ∀ i < k'.trail_end,
      k'.rsns[(k'.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
        rsns0[(k'.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32) :
    FullWitnessInv c F0 F_cur k' :=
  { ext_sound := hw.ext_sound, inconsistent_sound := hw.inconsistent_sound
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
    cur_level_le := hw.cur_level_le, trail_lits_lt := hw.trail_lits_lt
    trail_vars_nodup := hw.trail_vars_nodup, vals_domain := hw.vals_domain
    vals_true_iff := hw.vals_true_iff, vals_false_iff := hw.vals_false_iff
    lvl_le := fun i hi => by simpa [hlvl i hi] using hw.lvl_le i hi
    dec_earliest := fun i j hi hj hleq hdec => by
      have h := hw.dec_earliest i j hi hj
      rw [hlvl i hi, hlvl j hj] at hleq; rw [hlvl j hj, hrsn j hj] at hdec; exact h hleq hdec
    levels_inhabited := fun L h1 h2 =>
      let ⟨i, hi, heq⟩ := hw.levels_inhabited L h1 h2; ⟨i, hi, by rw [hlvl i hi]; exact heq⟩
    level0_sound := fun i hi hl0 => hw.level0_sound i hi (by simpa [hlvl i hi] using hl0)
    trail_pos_inv := hw.trail_pos_inv
    level0_rsn_none := fun idx hidx hl0 => by
      rw [hlvl idx hidx] at hl0; rw [hrsn idx hidx]; exact hw.level0_rsn_none idx hidx hl0
    frame_trail_lt := hw.frame_trail_lt, frame_trail_mono := hw.frame_trail_mono
    frame_trail_before_lt := fun L h1 h2 i hi => by
      have hlt : i < k'.trail_end := lt_of_lt_of_le hi (hw.frame_trail_lt L h2)
      have h := hw.frame_trail_before_lt L h1 h2 i hi; rw [hlvl i hlt]; exact h
    frame_dec_lt := hw.frame_dec_lt
    reason_inv := fun idx hidx hne => by
      have h := hw.reason_inv idx hidx; rw [hrsn idx hidx] at hne ⊢
      by_cases hb : (rsns0[(k'.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
          0x80000000#32) ≠ 0#32
      · have h' := h hne; rw [ite_eq_left hb] at h' ⊢
        obtain ⟨h1, h2, m, hm, hmeq, hlv⟩ := h'
        have hm' : m < k'.trail_end := by omega
        have hmt := hlvl m hm'; rw [hmeq, fullInv_var_xor1] at hmt
        exact ⟨h1, h2, m, hm, hmeq, by rw [hmt, hlvl idx hidx]; exact hlv⟩
      · have h' := h hne; rw [ite_eq_right hb] at h' ⊢
        obtain ⟨h1, h2, hall⟩ := h'
        refine ⟨h1, h2, fun q hq => (hall q hq).elim Or.inl fun ⟨m, hm, hmeq, hlv⟩ => Or.inr ?_⟩
        have hm' : m < k'.trail_end := by omega
        have hmt := hlvl m hm'; rw [hmeq, fullInv_var_xor1] at hmt
        exact ⟨m, hm, hmeq, by rw [hmt, hlvl idx hidx]; exact hlv⟩
    reason_lit_mem := fun idx hidx hne hbin => by
      rw [hrsn idx hidx] at hne hbin ⊢; exact hw.reason_lit_mem idx hidx hne hbin }

private theorem otfs_vals_zero_iff {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullOtfsWitnessInv c F0 F_cur k) {l : Nat} (hl : l < 2 * k.cur_vars) :
    k.vals[l]?.getD 0#8 = 0#8 ↔
      ∀ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat / 2 ≠ l / 2 := by
  constructor
  · intro hv0 i hi hdiv
    rcases (litVar_eq_iff (k.trl[i]?.getD 0#32).toNat l).mp hdiv with heq | heq
    · have h1 := (hw.vals_true_iff l hl).mpr ⟨i, hi, heq⟩; rw [hv0] at h1; cases h1
    · have h1 := (hw.vals_false_iff l hl).mpr ⟨i, hi, by rw [heq]; unfold litNeg; rfl⟩
      rw [hv0] at h1; cases h1
  · intro hne
    rcases hw.vals_domain l hl with hv | hv | hv
    · exact hv
    · obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl).mp hv
      exact False.elim (hne i hi (by rw [heq]))
    · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp hv
      exact False.elim (hne i hi (by rw [heq, fullInv_var_xor1]))

private def FullBtDistinct (s : FullState) : Prop :=
  (∀ i j, i < s.core.trail_end → j < s.core.trail_end →
    (s.core.trl[i]?.getD 0#32).toNat / 2 = (s.core.trl[j]?.getD 0#32).toNat / 2 → i = j) ∧
  (∀ i < s.core.trail_end,
    (s.core.trail_pos[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = i)

private def fullBtKeep (s : FullState) (target_lvl q_start p : Nat) : List (BitVec 32) :=
  s.core.trl.take q_start ++ ((s.core.trl.take p).drop q_start).filter fun lit =>
    decide ((s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ target_lvl)

private def FullBtStepEq (s : FullState) (target_lvl q_start q p : Nat)
    (vals1 : List (BitVec 8)) (lvl1 rsns1 trl1 tp1 : List (BitVec 32)) : Prop :=
  open Classical in
  q = (fullBtKeep s target_lvl q_start p).length ∧
  (∀ i < q, (trl1[i]?.getD 0#32).toNat =
    ((fullBtKeep s target_lvl q_start p)[i]?.getD 0#32).toNat) ∧
  (∀ i < q, (tp1[(trl1[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = i) ∧
  (∀ l < 2 * s.core.cur_vars, vals1[l]?.getD 0#8 =
    if ∃ j, q_start ≤ j ∧ j < p ∧ (s.core.trl[j]?.getD 0#32).toNat / 2 = l / 2 ∧
        target_lvl < (s.core.lvl[l / 2]?.getD 0#32).toNat then
      0#8 else s.core.vals[l]?.getD 0#8) ∧
  (∀ v < s.core.cur_vars, lvl1[v]?.getD 0#32 =
    if ∃ j, q_start ≤ j ∧ j < p ∧ (s.core.trl[j]?.getD 0#32).toNat / 2 = v ∧
        target_lvl < (s.core.lvl[v]?.getD 0#32).toNat then
      0#32 else s.core.lvl[v]?.getD 0#32) ∧
  (∀ v < s.core.cur_vars, rsns1[v]?.getD 0xFFFFFFFF#32 =
    if ∃ j, q_start ≤ j ∧ j < p ∧ (s.core.trl[j]?.getD 0#32).toNat / 2 = v ∧
        target_lvl < (s.core.lvl[v]?.getD 0#32).toNat then
      0xFFFFFFFF#32 else s.core.rsns[v]?.getD 0xFFFFFFFF#32)

private theorem fullBtKeep_mem_idx {s : FullState} {target_lvl q_start p i : Nat}
    (hq : q_start ≤ p) (hp : p ≤ s.core.trl.length)
    (hi : i < (fullBtKeep s target_lvl q_start p).length) :
    ∃ m < p, (fullBtKeep s target_lvl q_start p)[i]'hi = s.core.trl[m]?.getD 0#32 ∧
      (q_start ≤ m →
        (s.core.lvl[(s.core.trl[m]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl) := by
  unfold fullBtKeep at hi ⊢
  by_cases hil : i < (s.core.trl.take q_start).length
  · rw [List.getElem_append_left hil, List.getElem_take]
    simp only [List.length_take, Nat.min_eq_left (by omega : q_start ≤ s.core.trl.length)] at hil
    exact ⟨i, by omega, by rw [List.getElem?_eq_getElem (by omega), Option.getD_some],
      fun hbad => absurd hbad (by omega)⟩
  · rw [List.getElem_append_right (Nat.le_of_not_lt hil)]
    let flt := ((s.core.trl.take p).drop q_start).filter
      fun lit => decide ((s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ target_lvl)
    have hflt_i : i - (s.core.trl.take q_start).length < flt.length := by
      simp only [flt, List.length_append] at hi ⊢; omega
    have hm1 := (List.mem_filter.mp (List.getElem_mem hflt_i)).1
    obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.mp hm1
    simp only [List.length_drop, List.length_take, Nat.min_eq_left hp] at hk
    simp only [List.getElem_drop, List.getElem_take] at hkeq
    have hfl2 : (s.core.lvl[(s.core.trl[q_start + k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        target_lvl := by
      have h2 := of_decide_eq_true (List.mem_filter.mp (List.getElem_mem hflt_i)).2
      rw [← hkeq] at h2
      rwa [List.getElem?_eq_getElem (by omega : q_start + k < s.core.trl.length), Option.getD_some]
    exact ⟨q_start + k, by omega, by
      rw [← hkeq, List.getElem?_eq_getElem (by omega : q_start + k < s.core.trl.length),
        Option.getD_some],
      fun _ => hfl2⟩

private theorem fullBtKeep_succ {s : FullState} {target_lvl q_start p : Nat}
    (hq : q_start ≤ p) (hp : p < s.core.trl.length) :
    fullBtKeep s target_lvl q_start (p + 1) =
      fullBtKeep s target_lvl q_start p ++
        if (s.core.lvl[(s.core.trl[p]'hp).toNat / 2]?.getD 0#32).toNat ≤ target_lvl then
          [s.core.trl[p]'hp] else [] := by
  unfold fullBtKeep
  have htk : s.core.trl.take (p + 1) = s.core.trl.take p ++ [s.core.trl[p]'hp] :=
    List.take_add_one.trans (by simp [List.getElem?_eq_getElem hp])
  have hlen : (s.core.trl.take p).length = p := by rw [List.length_take, Nat.min_eq_left (by omega)]
  have hdr : (s.core.trl.take (p + 1)).drop q_start =
      (s.core.trl.take p).drop q_start ++ [s.core.trl[p]'hp] := by
    rw [htk, List.drop_append_of_le_length (by omega)]
  rw [hdr, List.filter_append, ← List.append_assoc]; congr 1
  simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq]

private theorem fullBtStepEq_init {s : FullState} {target_lvl q_start : Nat}
    (hq : q_start ≤ s.core.trail_end) (hte : s.core.trail_end ≤ s.core.trl.length) :
    FullBtDistinct s →
    FullBtStepEq s target_lvl q_start q_start q_start
      s.core.vals s.core.lvl s.core.rsns s.core.trl s.core.trail_pos := by
  open Classical in
  intro hdist
  have hke : fullBtKeep s target_lvl q_start q_start = s.core.trl.take q_start := by
    unfold fullBtKeep; simp
  have hno : ∀ w, ¬ ∃ j, q_start ≤ j ∧ j < q_start ∧
      (s.core.trl[j]?.getD 0#32).toNat / 2 = w ∧
      target_lvl < (s.core.lvl[w]?.getD 0#32).toNat := fun _ ⟨_, h1, h2, _⟩ => by omega
  refine ⟨by rw [hke, List.length_take, Nat.min_eq_left (by omega)], fun i hi => ?_,
    fun i hi => hdist.2 i (by omega), fun l _ => by simp [hno (l / 2)],
    fun v _ => by simp [hno v], fun v _ => by simp [hno v]⟩
  rw [hke, List.getElem?_take]; simp [hi]

private theorem fullBtStepEq_keep_ex {s : FullState} {target_lvl q_start p w : Nat}
    (hp : p < s.core.trail_end) (hte : s.core.trail_end ≤ s.core.trl.length)
    (hlvs : (s.core.lvl[(s.core.trl[p]'(by omega)).toNat / 2]?.getD 0#32).toNat ≤ target_lvl) :
    ((∃ j, q_start ≤ j ∧ j < p ∧ (s.core.trl[j]?.getD 0#32).toNat / 2 = w ∧
        target_lvl < (s.core.lvl[w]?.getD 0#32).toNat) ↔
      (∃ j, q_start ≤ j ∧ j < p + 1 ∧ (s.core.trl[j]?.getD 0#32).toNat / 2 = w ∧
        target_lvl < (s.core.lvl[w]?.getD 0#32).toNat)) :=
  ⟨fun ⟨j, h1, h2, h3, h4⟩ => ⟨j, h1, by omega, h3, h4⟩,
   fun ⟨j, h1, h2, h3, h4⟩ => by
     by_cases hjp : j = p
     · subst hjp; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h3
       rw [h3] at hlvs; exact False.elim (Nat.not_le_of_lt h4 hlvs)
     · exact ⟨j, h1, by omega, h3, h4⟩⟩

private theorem fullBtStepEq_keep {s : FullState} {target_lvl q_start q p : Nat}
    {vals1 : List (BitVec 8)} {lvl1 rsns1 trl1 tp1 : List (BitVec 32)}
    (hq : q_start ≤ q) (hqp : q ≤ p) (hp : p < s.core.trail_end)
    (hte : s.core.trail_end ≤ s.core.trl.length) (hte32 : s.core.trail_end < 2 ^ 32)
    (htrl_l : trl1.length = s.core.trl.length)
    (htpl : tp1.length = s.core.lvl.length) (hcur : s.core.cur_vars ≤ s.core.lvl.length)
    (hlit_lt : (s.core.trl[p]'(by omega)).toNat < 2 * s.core.cur_vars)
    (hstep : FullBtStepEq s target_lvl q_start q p vals1 lvl1 rsns1 trl1 tp1)
    (hdist : FullBtDistinct s)
    (hlv : (lvl1[(s.core.trl[p]'(by omega)).toNat / 2]?.getD 0#32).toNat ≤ target_lvl) :
    let lit := s.core.trl[p]'(by omega)
    let v := lit.toNat / 2
    FullBtStepEq s target_lvl q_start (q + 1) (p + 1) vals1 lvl1 rsns1
      (trl1.set q lit) (tp1.set v (BitVec.ofNat 32 q)) := by
  open Classical in
  intro lit v
  have hv_lt : v < s.core.cur_vars := Nat.div_lt_of_lt_mul hlit_lt
  have hnv : ¬ ∃ j, q_start ≤ j ∧ j < p ∧ (s.core.trl[j]?.getD 0#32).toNat / 2 = v ∧
      target_lvl < (s.core.lvl[v]?.getD 0#32).toNat := by
    rintro ⟨j, _, hj, hveq, _⟩
    exact absurd (hdist.1 j p (by omega) hp (by
      rw [hveq, List.getElem?_eq_getElem (by omega), Option.getD_some])) (by omega)
  have hlvl_v : lvl1[v]?.getD 0#32 = s.core.lvl[v]?.getD 0#32 := by
    rw [hstep.2.2.2.2.1 v hv_lt, ite_eq_right (fun hex => absurd hex hnv)]
  have hlvs : (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ target_lvl := by
    simpa [lit, v, ← hlvl_v] using hlv
  have hks := fullBtKeep_succ (s := s) (target_lvl := target_lvl) (q_start := q_start) (p := p)
    (by omega) (by omega)
  have hks_ite : (if (s.core.lvl[(s.core.trl[p]'(by omega)).toNat / 2]?.getD 0#32).toNat ≤
      target_lvl then [s.core.trl[p]'(by omega)] else []) = [s.core.trl[p]'(by omega)] :=
    ite_eq_left hlvs
  rw [hks_ite] at hks
  have hlen_keep : (fullBtKeep s target_lvl q_start (p + 1)).length = q + 1 := by
    rw [hks, List.length_append, ← hstep.1]; simp
  refine ⟨hlen_keep.symm, fun i hi => ?_, fun i hi => ?_, fun l hl => ?_, fun w hw => ?_,
    fun w hw => ?_⟩
  · rw [hks]
    by_cases hiq : i = q
    · subst hiq
      rw [List.getElem?_set_self (by omega),
        List.getElem?_append_right (by rw [← hstep.1]; exact Nat.le_refl _)]
      simp [← hstep.1, lit]
    · rw [List.getElem?_set_ne (Ne.symm hiq), List.getElem?_append_left (by rw [← hstep.1]; omega)]
      exact hstep.2.1 i (by omega)
  · by_cases hiq : i = q
    · subst hiq
      rw [List.getElem?_set_self (by omega), Option.getD_some,
        List.getElem?_set_self (by omega), Option.getD_some, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    · rw [List.getElem?_set_ne (Ne.symm hiq)]
      have hne_v : (trl1[i]?.getD 0#32).toNat / 2 ≠ v := by
        have hiq_lt : i < q := by omega
        have hid := hstep.2.1 i hiq_lt
        have hi_keep : i < (fullBtKeep s target_lvl q_start p).length := by
          rw [← hstep.1]; exact hiq_lt
        obtain ⟨m, hm, hmeq, _⟩ := fullBtKeep_mem_idx (s := s) (target_lvl := target_lvl)
          (q_start := q_start) (p := p) (by omega) (by omega) (i := i) hi_keep
        have hm_eq : (trl1[i]?.getD 0#32).toNat = (s.core.trl[m]?.getD 0#32).toNat := by
          rw [hid, List.getElem?_eq_getElem hi_keep, Option.getD_some, hmeq]
        intro hveq
        have heq_idx := hdist.1 m p (by omega) hp (by
          rw [← hm_eq, hveq, List.getElem?_eq_getElem (by omega), Option.getD_some])
        omega
      rw [List.getElem?_set_ne hne_v.symm]; exact hstep.2.2.1 i (by omega)
  · rw [hstep.2.2.2.1 l hl, propext (fullBtStepEq_keep_ex hp hte hlvs)]
  · rw [hstep.2.2.2.2.1 w hw, propext (fullBtStepEq_keep_ex hp hte hlvs)]
  · rw [hstep.2.2.2.2.2 w hw, propext (fullBtStepEq_keep_ex hp hte hlvs)]

open Classical in
private theorem fullBtStepEq_pop_arr {s : FullState} {target_lvl q_start p v w : Nat}
    {arr arr0 : List (BitVec 32)} {df : BitVec 32} (hq : q_start ≤ p)
    (hp : p < s.core.trail_end) (_hte : s.core.trail_end ≤ s.core.trl.length)
    (harr_l : arr.length = s.core.lvl.length) (hv_l : v < s.core.lvl.length)
    (hveq : (s.core.trl[p]?.getD 0#32).toNat / 2 = v)
    (hlv : target_lvl < (s.core.lvl[v]?.getD 0#32).toNat)
    (hprev : arr[w]?.getD df =
      if ∃ j, q_start ≤ j ∧ j < p ∧ (s.core.trl[j]?.getD 0#32).toNat / 2 = w ∧
          target_lvl < (s.core.lvl[w]?.getD 0#32).toNat then df else arr0[w]?.getD df) :
    (arr.set v df)[w]?.getD df =
      if ∃ j, q_start ≤ j ∧ j < p + 1 ∧ (s.core.trl[j]?.getD 0#32).toNat / 2 = w ∧
          target_lvl < (s.core.lvl[w]?.getD 0#32).toNat then df else arr0[w]?.getD df := by
  by_cases hwv : w = v
  · subst hwv; rw [List.getElem?_set_self (by omega), Option.getD_some]
    split
    · rfl
    · rename_i hneg; exact False.elim (hneg ⟨p, hq, by omega, hveq, hlv⟩)
  · rw [List.getElem?_set_ne (Ne.symm hwv), hprev]; congr 1; apply propext
    exact ⟨fun ⟨j, hj1, hj2, hjeq, hjlt⟩ => ⟨j, hj1, by omega, hjeq, hjlt⟩,
      fun ⟨j, hj1, hj2, hjeq, hjlt⟩ => by
        by_cases hjp : j = p
        · subst hjp; exact absurd (hjeq.symm.trans hveq) hwv
        · exact ⟨j, hj1, by omega, hjeq, hjlt⟩⟩

private theorem fullBtStepEq_pop {s : FullState} {target_lvl q_start q p : Nat}
    {vals1 : List (BitVec 8)} {lvl1 rsns1 trl1 tp1 : List (BitVec 32)}
    (hq : q_start ≤ q) (hqp : q ≤ p) (hp : p < s.core.trail_end)
    (hvals_l : vals1.length = 2 * s.core.lvl.length)
    (hlvl_l : lvl1.length = s.core.lvl.length) (hrsn_l : rsns1.length = s.core.lvl.length)
    (hcur : s.core.cur_vars ≤ s.core.lvl.length) (hte : s.core.trail_end ≤ s.core.trl.length)
    (hlit_lt : (s.core.trl[p]'(by omega)).toNat < 2 * s.core.cur_vars)
    (hstep : FullBtStepEq s target_lvl q_start q p vals1 lvl1 rsns1 trl1 tp1)
    (hdist : FullBtDistinct s)
    (hlt : target_lvl < (lvl1[(s.core.trl[p]'(by omega)).toNat / 2]?.getD 0#32).toNat) :
    let lit := s.core.trl[p]'(by omega)
    let v := lit.toNat / 2
    FullBtStepEq s target_lvl q_start q (p + 1)
      ((vals1.set lit.toNat 0#8).set (lit.toNat ^^^ 1) 0#8)
      (lvl1.set v 0#32) (rsns1.set v 0xFFFFFFFF#32) trl1 tp1 := by
  open Classical in
  intro lit v
  have hv_lt : v < s.core.cur_vars := Nat.div_lt_of_lt_mul hlit_lt
  have hnv : ¬ ∃ j, q_start ≤ j ∧ j < p ∧ (s.core.trl[j]?.getD 0#32).toNat / 2 = v ∧
      target_lvl < (s.core.lvl[v]?.getD 0#32).toNat := by
    rintro ⟨j, _, hj, hveq, _⟩
    exact absurd (hdist.1 j p (by omega) hp (by
      rw [hveq, List.getElem?_eq_getElem (by omega), Option.getD_some])) (by omega)
  have hlvl_v : lvl1[v]?.getD 0#32 = s.core.lvl[v]?.getD 0#32 := by
    rw [hstep.2.2.2.2.1 v hv_lt, ite_eq_right (fun hex => absurd hex hnv)]
  have hlv_gt : target_lvl < (s.core.lvl[v]?.getD 0#32).toNat := by rwa [← hlvl_v]
  have hks := fullBtKeep_succ (s := s) (target_lvl := target_lvl) (q_start := q_start) (p := p)
    (by omega) (by omega)
  have hnot_le : ¬ ((s.core.lvl[(s.core.trl[p]'(by omega)).toNat / 2]?.getD 0#32).toNat ≤
      target_lvl) := by simpa [lit, v] using Nat.not_le_of_lt hlv_gt
  rw [ite_eq_right (fun h => absurd h hnot_le), List.append_nil] at hks
  have hne_lit : lit.toNat ≠ lit.toNat ^^^ 1 := fun heq => by
    have htb := congrArg (·.testBit 0) heq; rw [Nat.testBit_xor] at htb
    cases h0 : lit.toNat.testBit 0 <;> simp [h0] at htb
  have hxor_lt : lit.toNat ^^^ 1 < 2 * s.core.cur_vars := by
    have hd : (lit.toNat ^^^ 1) / 2 = v := fullInv_var_xor1 _; omega
  have hveq : (s.core.trl[p]?.getD 0#32).toNat / 2 = v := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  refine ⟨by rw [hks, hstep.1], by rw [hks]; exact hstep.2.1, hstep.2.2.1,
    fun l hl => ?_,
    fun w hw => fullBtStepEq_pop_arr (by omega) hp hte hlvl_l (by omega) hveq hlv_gt
      (hstep.2.2.2.2.1 w hw),
    fun w hw => fullBtStepEq_pop_arr (by omega) hp hte hrsn_l (by omega) hveq hlv_gt
      (hstep.2.2.2.2.2 w hw)⟩
  · by_cases hlv : l / 2 = v
    · have hc : l = lit.toNat ∨ l = lit.toNat ^^^ 1 := (litVar_eq_iff l lit.toNat).mp hlv
      have hset0 : ((vals1.set lit.toNat 0#8).set (lit.toNat ^^^ 1) 0#8)[l]?.getD 0#8 = 0#8 := by
        rcases hc with rfl | rfl
        · rw [List.getElem?_set_ne hne_lit.symm, List.getElem?_set_self (by omega),
            Option.getD_some]
        · rw [List.getElem?_set_self (by simp [hvals_l]; omega), Option.getD_some]
      have hex : ∃ j, q_start ≤ j ∧ j < p + 1 ∧
          (s.core.trl[j]?.getD 0#32).toNat / 2 = l / 2 ∧
          target_lvl < (s.core.lvl[l / 2]?.getD 0#32).toNat :=
        ⟨p, by omega, by omega, by rw [hveq, hlv], by rwa [hlv]⟩
      rw [hset0, eq_true hex, ite_true]
    · have hne1 : l ≠ lit.toNat := fun heq => hlv (by simp [heq, v])
      have hne2 : l ≠ lit.toNat ^^^ 1 := fun heq => hlv (by simp [heq, fullInv_var_xor1, v])
      rw [List.getElem?_set_ne hne2.symm, List.getElem?_set_ne hne1.symm, hstep.2.2.2.1 l hl]
      congr 1; apply propext
      exact ⟨fun ⟨j, hj1, hj2, hjeq, hjlt⟩ => ⟨j, hj1, by omega, hjeq, hjlt⟩,
        fun ⟨j, hj1, hj2, hjeq, hjlt⟩ => by
          by_cases hjp : j = p
          · subst hjp; rw [hveq] at hjeq; exact absurd hjeq.symm hlv
          · exact ⟨j, hj1, by omega, hjeq, hjlt⟩⟩

private def btAuxList (c : FullCfg) (s : FullState) (target_lvl : Nat)
    (arr' arr0 : List (BitVec 32)) (df : BitVec 32) : List (BitVec 32) :=
  open Classical in
  (List.range c.max_vars).map fun v =>
    if ∃ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat / 2 = v then arr'[v]?.getD df
    else if (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl then arr0[v]?.getD df else df

private theorem btAuxList_len (c : FullCfg) (s : FullState) (target_lvl : Nat)
    (arr' arr0 : List (BitVec 32)) (df : BitVec 32) :
    (btAuxList c s target_lvl arr' arr0 df).length = c.max_vars := by simp [btAuxList]

private theorem btAuxList_get (c : FullCfg) (s : FullState) (target_lvl q_start : Nat)
    (arr' arr0 : List (BitVec 32)) (df : BitVec 32)
    (hon : ∀ i < s.core.trail_end,
      target_lvl < (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat →
      q_start ≤ i)
    (harr_yes : ∀ v < s.core.cur_vars,
      (∃ j, q_start ≤ j ∧ j < s.core.trail_end ∧ (s.core.trl[j]?.getD 0#32).toNat / 2 = v ∧
        target_lvl < (s.core.lvl[v]?.getD 0#32).toNat) →
      arr'[v]?.getD df = df)
    (harr_no : ∀ v < s.core.cur_vars,
      (¬ ∃ j, q_start ≤ j ∧ j < s.core.trail_end ∧ (s.core.trl[j]?.getD 0#32).toNat / 2 = v ∧
        target_lvl < (s.core.lvl[v]?.getD 0#32).toNat) →
      arr'[v]?.getD df = arr0[v]?.getD df)
    {v : Nat} (hv : v < s.core.cur_vars) (hcv : s.core.cur_vars ≤ c.max_vars) :
    (btAuxList c s target_lvl arr' arr0 df)[v]?.getD df =
      if (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl then arr0[v]?.getD df else df := by
  open Classical in
  have hv_mx : v < c.max_vars := Nat.lt_of_lt_of_le hv hcv
  simp only [btAuxList, List.getElem?_map, List.getElem?_range hv_mx, Option.map_some,
    Option.getD_some]
  split
  · rename_i hex
    by_cases hlv : (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl
    · simp only [hlv, ↓reduceIte]
      exact harr_no v hv (fun ⟨_, _, _, _, hbad⟩ => absurd hbad (by omega))
    · obtain ⟨i, hi, hiveq⟩ := hex
      simp only [hlv, ↓reduceIte]
      exact harr_yes v hv ⟨i, hon i hi (by rw [hiveq]; omega), hi, hiveq, by omega⟩
  · rfl

private theorem btAuxList_get_kept (c : FullCfg) (s : FullState) (target_lvl : Nat)
    (arr' arr0 : List (BitVec 32)) (df : BitVec 32) {v m : Nat}
    (hv_mx : v < c.max_vars) (hm : m < s.core.trail_end)
    (hm_eq : v = (s.core.trl[m]?.getD 0#32).toNat / 2) :
    arr'[v]?.getD df = (btAuxList c s target_lvl arr' arr0 df)[v]?.getD df := by
  open Classical in
  simp only [btAuxList, List.getElem?_map, List.getElem?_range hv_mx, Option.map_some,
    Option.getD_some]
  split
  · rfl
  · rename_i hneg; exact False.elim (hneg ⟨m, hm, hm_eq.symm⟩)

private theorem filter_range_strictMono {n : Nat} {p : Nat → Bool}
    {i j : Nat} (hi : i < ((List.range n).filter p).length)
    (hj : j < ((List.range n).filter p).length) (hij : i < j) :
    ((List.range n).filter p)[i] < ((List.range n).filter p)[j] :=
  (List.pairwise_iff_getElem.mp (List.Pairwise.sublist List.filter_sublist
    List.pairwise_lt_range)) i j hi hj hij

private theorem nodup_map_succ (l : List Nat) (h : l.Nodup) : (l.map (· + 1)).Nodup := by
  induction h with
  | nil => exact .nil
  | @cons a l ha _ ih =>
    exact .cons (fun _ hx heq => by
      obtain ⟨y, hy, hyEq⟩ := List.mem_map.mp hx
      have hne := ha y hy
      dsimp only at heq hyEq
      omega) ih

private theorem le_of_surj_range1 {m k : Nat} (f : Nat → Nat)
    (h : ∀ L, 1 ≤ L → L ≤ m → ∃ i < k, f i = L) : m ≤ k := by
  let xs := (List.range k).map f
  let ys := (List.range m).map (· + 1)
  have hsub : ys ⊆ xs := fun L hL => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hL
    have ht' := List.mem_range.mp ht
    obtain ⟨i, hi, heq⟩ := h (t + 1) (by omega) (by omega)
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, heq⟩
  have hlen := (nodup_map_succ (List.range m) List.nodup_range).length_le_of_subset hsub
  simpa only [ys, xs, List.length_map, List.length_range] using hlen

private theorem chronoBacktrack_of_otfs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen0 : s.LengthsOk c) (hw : FullOtfsWitnessInv c F0 F_cur s.core)
    {target_lvl trail_end' propagated' : Nat}
    {vals' : List (BitVec 8)} {lvl' rsns' trl' trail_pos' : List (BitVec 32)}
    {unassigned' : BitVec 64} {scratch' : FullScratch}
    (_hlen' : ({ s with
      core := { s.core with vals := vals', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := trail_pos', trail_end := trail_end',
                            propagated := propagated', cur_level := target_lvl,
                            unassigned := unassigned' }
      scratch := scratch' } : FullState).LengthsOk c)
    (hlt : target_lvl < s.core.cur_level)
    (htrl_eq : ∀ i < trail_end',
      (trl'[i]?.getD 0#32).toNat =
        let q_start := min (s.core.frame_trail[target_lvl + 1]?.getD 0#32).toNat s.core.trail_end
        let keptTail := ((s.core.trl.take s.core.trail_end).drop q_start).filter fun lit =>
          decide ((s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ target_lvl)
        (((s.core.trl.take q_start ++ keptTail)[i]?).getD 0#32).toNat)
    (hte_len :
      let q_start := min (s.core.frame_trail[target_lvl + 1]?.getD 0#32).toNat s.core.trail_end
      let keptTail := ((s.core.trl.take s.core.trail_end).drop q_start).filter fun lit =>
        decide ((s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ target_lvl)
      trail_end' = (s.core.trl.take q_start ++ keptTail).length)
    (hvals_eq : ∀ l < 2 * s.core.cur_vars,
      vals'[l]?.getD 0#8 =
        if (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl then s.core.vals[l]?.getD 0#8 else 0#8)
    (hlvl_eq : ∀ v < s.core.cur_vars,
      lvl'[v]?.getD 0#32 =
        if (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl then s.core.lvl[v]?.getD 0#32 else 0#32)
    (hrsn_eq : ∀ v < s.core.cur_vars,
      rsns'[v]?.getD 0xFFFFFFFF#32 =
        if (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl then
          s.core.rsns[v]?.getD 0xFFFFFFFF#32 else 0xFFFFFFFF#32)
    (htpos_eq : ∀ i < trail_end',
      (trail_pos'[(trl'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = i) :
    FullWitnessInv c F0 F_cur
      { s.core with vals := vals', lvl := lvl', rsns := rsns',
                    trl := trl', trail_pos := trail_pos', trail_end := trail_end',
                    propagated := propagated', cur_level := target_lvl,
                    unassigned := unassigned' } := by
  let k' : FullCoreState :=
    { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := trail_pos',
                  trail_end := trail_end', propagated := propagated', cur_level := target_lvl,
                  unassigned := unassigned' }
  have hcl := hlen0.core_ok
  have hte' : k'.trail_end = trail_end' := rfl
  have hcv' : k'.cur_vars = s.core.cur_vars := rfl
  have hclv' : k'.cur_level = target_lvl := rfl
  let q_start := min (s.core.frame_trail[target_lvl + 1]?.getD 0#32).toNat s.core.trail_end
  let keepPred : Nat → Bool := fun j =>
    decide ((s.core.lvl[(s.core.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl)
  let keptIdx := (List.range s.core.trail_end).filter keepPred
  have hq_le : q_start ≤ s.core.trail_end := Nat.min_le_right _ _
  have htrl_le : s.core.trail_end ≤ s.core.trl.length := by
    have := hcl.trail_end_le; have := hcl.cur_vars_le; have := hcl.trl_len; omega
  have hpref_keep : ∀ j < q_start, keepPred j = true := fun j hj => by
    have hbef := hw.frame_trail_before_lt (target_lvl + 1) (by omega) (by omega) j
      (by omega : j < (s.core.frame_trail[target_lvl + 1]?.getD 0#32).toNat)
    simp only [keepPred, decide_eq_true_eq]; omega
  have htake_eq : s.core.trl.take s.core.trail_end =
      (List.range s.core.trail_end).map fun j => s.core.trl[j]?.getD 0#32 :=
    List.ext_getElem (by simp [List.length_take, Nat.min_eq_left htrl_le]) fun j hj1 _ => by
      simp only [List.length_take, Nat.min_eq_left htrl_le] at hj1
      simp only [List.getElem_take, List.getElem_map, List.getElem_range]
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hsplit_range : List.range s.core.trail_end =
      List.range q_start ++ (List.range (s.core.trail_end - q_start)).map (· + q_start) := by
    have hsum : s.core.trail_end = q_start + (s.core.trail_end - q_start) := by omega
    conv => lhs; rw [hsum, List.range_add]
    congr 1; apply List.map_congr_left; intro x _; omega
  have hkeep_eq :
      s.core.trl.take q_start ++ ((s.core.trl.take s.core.trail_end).drop q_start).filter
        (fun lit => decide ((s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ target_lvl)) =
      keptIdx.map (fun j => s.core.trl[j]?.getD 0#32) := by
    have ht1 : s.core.trl.take q_start =
        (List.range q_start).map fun j => s.core.trl[j]?.getD 0#32 :=
      List.ext_getElem
        (by simp [List.length_take, Nat.min_eq_left (by omega : q_start ≤ s.core.trl.length)])
        fun j hj1 _ => by
          simp only [List.length_take,
            Nat.min_eq_left (by omega : q_start ≤ s.core.trl.length)] at hj1
          simp only [List.getElem_take, List.getElem_map, List.getElem_range]
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have ht2 : (s.core.trl.take s.core.trail_end).drop q_start =
        ((List.range (s.core.trail_end - q_start)).map (· + q_start)).map
          fun j => s.core.trl[j]?.getD 0#32 :=
      List.ext_getElem
        (by simp [List.length_drop, List.length_take, Nat.min_eq_left htrl_le]) fun j hj1 _ => by
          simp only [List.length_drop, List.length_take, Nat.min_eq_left htrl_le] at hj1
          simp only [List.getElem_drop, List.getElem_take, List.getElem_map, List.getElem_range]
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; congr 1; omega
    have hf1 : (List.range q_start).filter keepPred = List.range q_start :=
      List.filter_eq_self.mpr fun j hj => hpref_keep j (List.mem_range.mp hj)
    have hf2 :
        (((List.range (s.core.trail_end - q_start)).map (· + q_start)).map
            fun j => s.core.trl[j]?.getD 0#32).filter
          (fun lit => decide ((s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ target_lvl)) =
        (((List.range (s.core.trail_end - q_start)).filter
            fun t => keepPred (t + q_start)).map (· + q_start)).map
          fun j => s.core.trl[j]?.getD 0#32 := by rw [List.filter_map, List.filter_map]; rfl
    rw [ht1, ht2, hf2, ← List.map_append]; congr 1
    dsimp only [keptIdx]; conv => rhs; rw [hsplit_range, List.filter_append, hf1, List.filter_map]
    rfl
  have hte_eq : trail_end' = keptIdx.length := by rw [hte_len, hkeep_eq, List.length_map]
  have htrl_idx : ∀ i (hi : i < trail_end'),
      (trl'[i]?.getD 0#32).toNat = (s.core.trl[keptIdx[i]'(hte_eq ▸ hi)]?.getD 0#32).toNat :=
    fun i hi => by
      have he := htrl_eq i hi; dsimp only at he; rw [he, hkeep_eq]
      simp [List.getElem?_map, List.getElem?_eq_getElem (hte_eq ▸ hi)]
  have hkept_pred : ∀ i (hi : i < trail_end'),
      (s.core.lvl[(trl'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl := fun i hi => by
    rw [htrl_idx i hi]
    have hm : keptIdx[i]'(hte_eq ▸ hi) ∈ (List.range s.core.trail_end).filter keepPred :=
      List.getElem_mem (l := keptIdx) (hte_eq ▸ hi)
    exact of_decide_eq_true (List.mem_filter.mp hm).2
  have hkept_lt : ∀ i (hi : i < trail_end'), keptIdx[i]'(hte_eq ▸ hi) < s.core.trail_end :=
    fun i hi => by
      have hm : keptIdx[i]'(hte_eq ▸ hi) ∈ (List.range s.core.trail_end).filter keepPred :=
        List.getElem_mem (l := keptIdx) (hte_eq ▸ hi)
      exact List.mem_range.mp (List.mem_filter.mp hm).1
  have hlvl_kept : ∀ i (hi : i < trail_end'),
      (lvl'[(trl'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
        (s.core.lvl[(trl'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := fun i hi => by
    have hlt_v : (trl'[i]?.getD 0#32).toNat / 2 < s.core.cur_vars := by
      rw [htrl_idx i hi]; exact Nat.div_lt_of_lt_mul (hw.trail_lits_lt _ (hkept_lt i hi))
    rw [hlvl_eq _ hlt_v, ite_eq_left (hkept_pred i hi)]
  have hof_mem : ∀ m < s.core.trail_end,
      (s.core.lvl[(s.core.trl[m]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl →
      ∃ i, ∃ (hi : i < trail_end'), keptIdx[i]'(hte_eq ▸ hi) = m := fun m hm hml => by
    have hmem : m ∈ keptIdx :=
      List.mem_filter.mpr ⟨List.mem_range.mpr hm, decide_eq_true hml⟩
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
    exact ⟨i, hte_eq ▸ hi, heq⟩
  have hold_lits_lt : ∀ i < trail_end', (trl'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars :=
    fun i hi => by rw [htrl_idx i hi]; exact hw.trail_lits_lt _ (hkept_lt i hi)
  have hsub_ex : ∀ {p : Nat},
      (∃ i < trail_end', (trl'[i]?.getD 0#32).toNat = p) ↔
      (∃ j < s.core.trail_end, (s.core.trl[j]?.getD 0#32).toNat = p ∧
        (s.core.lvl[p / 2]?.getD 0#32).toNat ≤ target_lvl) := by
    intro p; constructor
    · rintro ⟨i, hi, heq⟩
      have hkp := hkept_pred i hi; rw [heq] at hkp
      rw [htrl_idx i hi] at heq
      exact ⟨keptIdx[i]'(hte_eq ▸ hi), hkept_lt i hi, heq, hkp⟩
    · rintro ⟨j, hj, heq, hkp⟩
      obtain ⟨i, hi, hieq⟩ := hof_mem j hj (by rwa [heq])
      exact ⟨i, hi, by rw [htrl_idx i hi, hieq, heq]⟩
  have hft_le_old : ∀ L ≤ target_lvl, (s.core.frame_trail[L]?.getD 0#32).toNat ≤ q_start :=
    fun L hL => Nat.le_min.mpr
      ⟨hw.frame_trail_mono L (target_lvl + 1) (by omega) (by omega), hw.frame_trail_lt L (by omega)⟩
  have hkeep_pref_idx : ∀ j < q_start,
      ∃ i, ∃ (hi : i < trail_end'), keptIdx[i]'(hte_eq ▸ hi) = j ∧ i = j := fun j hj => by
    have hk_eq : (List.range q_start).filter keepPred = List.range q_start :=
      List.filter_eq_self.mpr fun x hx => hpref_keep x (List.mem_range.mp hx)
    have hsplit_k : keptIdx = List.range q_start ++
        ((List.range (s.core.trail_end - q_start)).map (· + q_start)).filter keepPred := by
      dsimp only [keptIdx]; rw [hsplit_range, List.filter_append, hk_eq]
    have hj_len : j < keptIdx.length := by
      rw [hsplit_k, List.length_append, List.length_range]; omega
    refine ⟨j, hte_eq ▸ hj_len, ?_, rfl⟩
    simp only [hsplit_k, List.getElem_append_left (by rw [List.length_range]; exact hj),
      List.getElem_range]
  have hinhab' : ∀ L, 1 ≤ L → L ≤ target_lvl →
      ∃ i < trail_end', (lvl'[(trl'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = L := by
    intro L hL1 hLle
    obtain ⟨j, hj, hlj⟩ := hw.levels_inhabited L hL1 (by omega)
    obtain ⟨i, hi, hieq⟩ := hof_mem j hj (by omega)
    exact ⟨i, hi, by rw [hlvl_kept i hi, htrl_idx i hi, hieq, hlj]⟩
  have hft_lt' : ∀ L ≤ target_lvl, (s.core.frame_trail[L]?.getD 0#32).toNat ≤ trail_end' := by
    intro L hL; have h1 := hft_le_old L hL
    have h2 : (s.core.trl.take q_start).length = q_start := by
      rw [List.length_take, Nat.min_eq_left (by omega)]
    dsimp only [q_start] at h1 h2; rw [hte_len]; rw [List.length_append, h2]; omega
  refine
    { ext_sound := hw.ext_sound, inconsistent_sound := hw.inconsistent_sound,
      arena := { hw.arena with len_ok := hw.arena.len_ok },
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr),
      cur_level_le := le_of_surj_range1
        (fun i => (lvl'[(trl'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) hinhab',
      trail_lits_lt := hold_lits_lt,
      trail_vars_nodup := fun i j hi hj hveq => by
        rw [hte'] at hi hj; rw [htrl_idx i hi, htrl_idx j hj] at hveq
        have hidx_eq := hw.trail_vars_nodup _ _ (hkept_lt i hi) (hkept_lt j hj) hveq
        by_cases hne : i = j
        · exact hne
        · rcases Nat.lt_or_gt_of_ne hne with h1 | h2
          · exact absurd hidx_eq
              (Nat.ne_of_lt (filter_range_strictMono (hte_eq ▸ hi) (hte_eq ▸ hj) h1))
          · exact absurd hidx_eq.symm
              (Nat.ne_of_lt (filter_range_strictMono (hte_eq ▸ hj) (hte_eq ▸ hi) h2)),
      vals_domain := fun l hl => by
        rw [hvals_eq l (hcv' ▸ hl)]; split; exact hw.vals_domain l (hcv' ▸ hl); exact Or.inl rfl,
      vals_true_iff := fun l hl => by
        rw [hcv'] at hl; rw [hvals_eq l hl, hte', hsub_ex]
        by_cases hlv : (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl
        · simp only [hlv, ↓reduceIte, and_true]; exact hw.vals_true_iff l hl
        · simp only [hlv, ↓reduceIte, and_false, exists_const, iff_false]; decide,
      vals_false_iff := fun l hl => by
        rw [hcv'] at hl; rw [hvals_eq l hl, hte', hsub_ex, fullInv_var_xor1]
        by_cases hlv : (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl
        · simp only [hlv, ↓reduceIte, and_true]; exact hw.vals_false_iff l hl
        · simp only [hlv, ↓reduceIte, and_false, exists_const, iff_false]; decide,
      lvl_le := fun i hi => by rw [hte'] at hi; rw [hclv', hlvl_kept i hi]; exact hkept_pred i hi,
      dec_earliest := fun i j hi hj hleq hdec => by
        rw [hte'] at hi hj; dsimp only at hleq hdec ⊢
        rw [hlvl_kept i hi, hlvl_kept j hj] at hleq; rw [hlvl_kept j hj] at hdec
        have hjv : (trl'[j]?.getD 0#32).toNat / 2 < s.core.cur_vars :=
          Nat.div_lt_of_lt_mul (hold_lits_lt j hj)
        rw [hrsn_eq _ hjv, ite_eq_left (hkept_pred j hj)] at hdec
        rw [htrl_idx i hi, htrl_idx j hj] at hleq
        rw [htrl_idx j hj] at hdec
        have hjk := hw.dec_earliest _ _ (hkept_lt i hi) (hkept_lt j hj) hleq hdec
        by_cases hij : j ≤ i
        · exact hij
        · have hstrict : keptIdx[i]'(hte_eq ▸ hi) < keptIdx[j]'(hte_eq ▸ hj) :=
            @filter_range_strictMono s.core.trail_end keepPred i j
              (hte_eq ▸ hi) (hte_eq ▸ hj) (Nat.lt_of_not_le hij)
          omega,
      levels_inhabited := hinhab',
      level0_sound := fun i hi hl0 => by
        rw [hte'] at hi; rw [hlvl_kept i hi] at hl0; rw [htrl_idx i hi] at hl0 ⊢
        exact hw.level0_sound _ (hkept_lt i hi) hl0,
      trail_pos_inv := htpos_eq,
      level0_rsn_none := fun idx hidx hl0 => by
        rw [hte'] at hidx
        rw [show k'.trl = trl' from rfl, show k'.lvl = lvl' from rfl] at hl0
        rw [show k'.trl = trl' from rfl, show k'.rsns = rsns' from rfl]
        rw [hlvl_kept idx hidx] at hl0
        have hv : (trl'[idx]?.getD 0#32).toNat / 2 < s.core.cur_vars :=
          Nat.div_lt_of_lt_mul (hold_lits_lt idx hidx)
        rw [hrsn_eq _ hv, ite_eq_left (hkept_pred idx hidx)]
        rw [htrl_idx idx hidx] at hl0 ⊢
        exact hw.level0_rsn_none _ (hkept_lt idx hidx) hl0,
      frame_trail_lt := hft_lt',
      frame_trail_mono := fun L1 L2 h1 h2 =>
        hw.frame_trail_mono L1 L2 h1 (by rw [hclv'] at h2; omega),
      frame_trail_before_lt := fun L hL1 hLle i hi => by
        rw [hclv'] at hLle
        have hfq := Nat.lt_of_lt_of_le hi (hft_le_old L hLle)
        obtain ⟨i', hi', hieq, hii'⟩ := hkeep_pref_idx i hfq
        rw [show k'.trl = trl' from rfl, show k'.lvl = lvl' from rfl]
        rw [← hii', hlvl_kept i' hi', htrl_idx i' hi', hieq]
        exact hw.frame_trail_before_lt L hL1 (by omega) i hi,
      frame_dec_lt := fun L hL1 hLle => by
        rw [hclv'] at hLle; exact hw.frame_dec_lt L hL1 (by omega),
      reason_inv := fun idx hidx hne => by
        rw [hte'] at hidx
        rw [show k'.trl = trl' from rfl, show k'.rsns = rsns' from rfl] at hne
        rw [show k'.trl = trl' from rfl, show k'.rsns = rsns' from rfl,
          show k'.lvl = lvl' from rfl, show k'.cur_vars = s.core.cur_vars from rfl,
          show fullArenaClauseRefsCore k' = fullArenaClauseRefsCore s.core from rfl,
          show fullArenaClauseGarbCore k' = fullArenaClauseGarbCore s.core from rfl,
          show fullArenaClauseLitsCore k' = fullArenaClauseLitsCore s.core from rfl]
        have hv : (trl'[idx]?.getD 0#32).toNat / 2 < s.core.cur_vars :=
          Nat.div_lt_of_lt_mul (hold_lits_lt idx hidx)
        have hkp := hkept_pred idx hidx
        rw [hrsn_eq _ hv, ite_eq_left hkp, htrl_idx idx hidx] at hne ⊢
        have hv_kept : (s.core.trl[keptIdx[idx]'(hte_eq ▸ hidx)]?.getD 0#32).toNat / 2 <
            s.core.cur_vars := by rw [← htrl_idx idx hidx]; exact hv
        have hkp_kept : (s.core.lvl[(s.core.trl[keptIdx[idx]'(hte_eq ▸ hidx)]?.getD
            0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl := by
          rw [← htrl_idx idx hidx]; exact hkp
        have hrs := hw.reason_inv_below _ (hkept_lt idx hidx) (by omega) hne
        by_cases hbin : (s.core.rsns[(s.core.trl[keptIdx[idx]'(hte_eq ▸ hidx)]?.getD
            0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
        · rw [ite_eq_left hbin] at hrs ⊢
          obtain ⟨m, hm, hmeq, hlvl_le⟩ := hrs.2.2
          have hmt : (s.core.lvl[((s.core.rsns[(s.core.trl[keptIdx[idx]'(hte_eq ▸ hidx)]?.getD
              0#32).toNat / 2]?.getD 0xFFFFFFFF#32) &&& 0x7FFFFFFF#32).toNat / 2]?.getD
              0#32).toNat ≤ target_lvl := by
            have := hkp; rw [htrl_idx idx hidx] at this; omega
          have hm_p : (s.core.lvl[(s.core.trl[m]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
              target_lvl := by rw [hmeq, fullInv_var_xor1]; exact hmt
          obtain ⟨m', hm', hm'_eq⟩ := hof_mem m (by have := hkept_lt idx hidx; omega) hm_p
          have hm'_lt : m' < idx := by
            by_cases hlt_mi : m' < idx
            · exact hlt_mi
            · rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt hlt_mi) with rfl | hgt
              · omega
              · have hs : keptIdx[idx]'(hte_eq ▸ hidx) < keptIdx[m']'(hte_eq ▸ hm') :=
                  @filter_range_strictMono s.core.trail_end keepPred idx m'
                    (hte_eq ▸ hidx) (hte_eq ▸ hm') hgt
                omega
          have hot_v : ((s.core.rsns[(s.core.trl[keptIdx[idx]'(hte_eq ▸ hidx)]?.getD
              0#32).toNat / 2]?.getD 0xFFFFFFFF#32) &&& 0x7FFFFFFF#32).toNat / 2 <
              s.core.cur_vars := Nat.div_lt_of_lt_mul hrs.1
          refine ⟨hrs.1, hrs.2.1, m', hm'_lt, by rw [htrl_idx m' hm', hm'_eq, hmeq], ?_⟩
          rw [hlvl_eq _ hot_v, ite_eq_left hmt, hlvl_eq _ hv_kept, ite_eq_left hkp_kept]
          exact hlvl_le
        · rw [ite_eq_right hbin] at hrs ⊢
          refine ⟨hrs.1, hrs.2.1, fun q hq => ?_⟩
          refine (hrs.2.2 q hq).elim Or.inl fun ⟨m, hm, hmeq, hlvl_le⟩ => Or.inr ?_
          have hmt : (s.core.lvl[q / 2]?.getD 0#32).toNat ≤ target_lvl := by
            have := hkp; rw [htrl_idx idx hidx] at this; omega
          have hm_p : (s.core.lvl[(s.core.trl[m]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
              target_lvl := by rw [hmeq, fullInv_var_xor1]; exact hmt
          obtain ⟨m', hm', hm'_eq⟩ := hof_mem m (by have := hkept_lt idx hidx; omega) hm_p
          have hm'_lt : m' < idx := by
            by_cases hlt_mi : m' < idx
            · exact hlt_mi
            · rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt hlt_mi) with rfl | hgt
              · omega
              · have hs : keptIdx[idx]'(hte_eq ▸ hidx) < keptIdx[m']'(hte_eq ▸ hm') :=
                  @filter_range_strictMono s.core.trail_end keepPred idx m'
                    (hte_eq ▸ hidx) (hte_eq ▸ hm') hgt
                omega
          have hqv : q / 2 < s.core.cur_vars :=
            Nat.div_lt_of_lt_mul (hw.arena.lits_lt _ hrs.1 hrs.2.1 q hq)
          refine ⟨m', hm'_lt, by rw [htrl_idx m' hm', hm'_eq, hmeq], ?_⟩
          rw [hlvl_eq _ hqv, ite_eq_left hmt, hlvl_eq _ hv_kept, ite_eq_left hkp_kept]
          exact hlvl_le,
      reason_lit_mem := fun idx hidx hne hlg => by
        rw [hte'] at hidx
        rw [show k'.trl = trl' from rfl, show k'.rsns = rsns' from rfl] at hne hlg
        rw [show k'.trl = trl' from rfl, show k'.rsns = rsns' from rfl,
          show fullArenaClauseLitsCore k' = fullArenaClauseLitsCore s.core from rfl]
        have hv : (trl'[idx]?.getD 0#32).toNat / 2 < s.core.cur_vars :=
          Nat.div_lt_of_lt_mul (hold_lits_lt idx hidx)
        have hkp := hkept_pred idx hidx
        rw [hrsn_eq _ hv, ite_eq_left hkp, htrl_idx idx hidx] at hne hlg ⊢
        rw [htrl_idx idx hidx] at hkp
        exact hw.reason_lit_mem_below _ (hkept_lt idx hidx) (by omega) hne hlg }

private theorem full_backtrack_noop_clear_of_otfs {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {target_lvl : Nat}
    (hw : FullOtfsWitnessInv c F0 F_cur s.core) (hle : s.core.cur_level ≤ target_lvl) :
    (∀ l < 2 * s.core.cur_vars, s.core.vals[l]?.getD 0#8 =
      if (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl then s.core.vals[l]?.getD 0#8
      else 0#8) ∧
    (∀ i < s.core.trail_end,
      let v := (s.core.trl[i]?.getD 0#32).toNat / 2
      s.core.lvl[v]?.getD 0#32 =
        if (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl then s.core.lvl[v]?.getD 0#32
        else 0#32) :=
  ⟨fun l hl => by
    by_cases hlv : (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl
    · simp [hlv]
    · simp only [hlv, ↓reduceIte]
      exact (otfs_vals_zero_iff hw hl).mpr fun i hi heq => by
        have := hw.lvl_le i hi; rw [heq] at this; omega,
   fun i hi => by
    have hli := hw.lvl_le i hi; dsimp only; rw [ite_eq_left (by omega)]⟩

private theorem full_backtrack_clear_of_otfs {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    {target_lvl trail_end' q_start : Nat}
    {vals' : List (BitVec 8)} {lvl' rsns' trl' tp' : List (BitVec 32)}
    (hw : FullOtfsWitnessInv c F0 F_cur s.core) (hlt : target_lvl < s.core.cur_level)
    (hq_def : q_start =
      min (s.core.frame_trail[target_lvl + 1]?.getD 0#32).toNat s.core.trail_end)
    (hstep : FullBtStepEq s target_lvl q_start trail_end' s.core.trail_end
      vals' lvl' rsns' trl' tp') :
    (∀ i < s.core.trail_end,
      target_lvl < (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat →
      q_start ≤ i) ∧
    (∀ l < 2 * s.core.cur_vars, vals'[l]?.getD 0#8 =
      if (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl then s.core.vals[l]?.getD 0#8
      else 0#8) ∧
    (∀ i < s.core.trail_end,
      let v := (s.core.trl[i]?.getD 0#32).toNat / 2
      lvl'[v]?.getD 0#32 =
        if (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl then s.core.lvl[v]?.getD 0#32
        else 0#32) := by
  open Classical in
  have hon : ∀ i < s.core.trail_end,
      target_lvl < (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat →
      q_start ≤ i := fun i _ hgt => by
    rcases Nat.lt_or_ge i q_start with hi_q | hge
    · rw [hq_def] at hi_q
      have hbf := hw.frame_trail_before_lt (target_lvl + 1) (by omega) hlt i (by omega)
      omega
    · exact hge
  refine ⟨hon, fun l hl => ?_, fun i hi => ?_⟩
  · rw [hstep.2.2.2.1 l hl]
    by_cases hlv : (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl
    · simp only [hlv, ↓reduceIte]
      rw [ite_eq_right (fun ⟨_, _, _, _, hbad⟩ => absurd hbad (by omega))]
    · have hgt : target_lvl < (s.core.lvl[l / 2]?.getD 0#32).toNat := by omega
      simp only [hlv, ↓reduceIte]
      by_cases hex : ∃ j, q_start ≤ j ∧ j < s.core.trail_end ∧
          (s.core.trl[j]?.getD 0#32).toNat / 2 = l / 2 ∧
          target_lvl < (s.core.lvl[l / 2]?.getD 0#32).toNat
      · simp only [hex, ↓reduceIte]
      · simp only [hex, ↓reduceIte]; apply (otfs_vals_zero_iff hw hl).mpr
        intro i hi hveq; apply hex; exact ⟨i, hon i hi (by rwa [hveq]), hi, hveq, hgt⟩
  · have hv_lt : (s.core.trl[i]?.getD 0#32).toNat / 2 < s.core.cur_vars :=
      Nat.div_lt_of_lt_mul (hw.trail_lits_lt i hi)
    dsimp only; rw [hstep.2.2.2.2.1 _ hv_lt]
    by_cases hlv :
        (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl
    · simp only [hlv, ↓reduceIte]
      exact ite_eq_right (fun ⟨_, _, _, _, hbad⟩ => absurd hbad (by omega))
    · simp only [hlv, ↓reduceIte]
      have hgt :
          target_lvl < (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
        omega
      exact ite_eq_left ⟨i, hon i hi hgt, hi, rfl, hgt⟩

private theorem full_backtrack_preserves_otfsWitness {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    {target_lvl trail_end' propagated' q_start : Nat}
    {vals' : List (BitVec 8)} {lvl' rsns' trl' tp' : List (BitVec 32)}
    {unassigned' : BitVec 64} {scr' : FullScratch}
    (hlen0 : s.LengthsOk c) (hw : FullOtfsWitnessInv c F0 F_cur s.core)
    (hlt : target_lvl < s.core.cur_level)
    (hq_def : q_start =
      min (s.core.frame_trail[target_lvl + 1]?.getD 0#32).toNat s.core.trail_end)
    (hlen' : ({ s with
      core := { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                            trail_pos := tp', trail_end := trail_end', propagated := propagated',
                            cur_level := target_lvl, unassigned := unassigned' }
      scratch := scr' } : FullState).LengthsOk c)
    (hstep : FullBtStepEq s target_lvl q_start trail_end' s.core.trail_end
      vals' lvl' rsns' trl' tp') :
    FullWitnessInv c F0 F_cur
      { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                    trail_pos := tp', trail_end := trail_end', propagated := propagated',
                    cur_level := target_lvl, unassigned := unassigned' } := by
  open Classical in
  let k' : FullCoreState :=
    { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                  trail_pos := tp', trail_end := trail_end', propagated := propagated',
                  cur_level := target_lvl, unassigned := unassigned' }
  have hcl := hlen0.core_ok
  have hte_lt : s.core.trail_end ≤ s.core.trl.length := by
    have := hcl.trail_end_le; have := hcl.cur_vars_le; have := hcl.trl_len; omega
  have hq_le : q_start ≤ s.core.trail_end := by rw [hq_def]; exact Nat.min_le_right _ _
  let lvlAux := btAuxList c s target_lvl lvl' s.core.lvl 0#32
  let rsnsAux := btAuxList c s target_lvl rsns' s.core.rsns 0xFFFFFFFF#32
  obtain ⟨hon, hvals_eq, _⟩ := full_backtrack_clear_of_otfs hw hlt hq_def hstep
  have hkeep_eq : fullBtKeep s target_lvl q_start s.core.trail_end =
      let qs := min (s.core.frame_trail[target_lvl + 1]?.getD 0#32).toNat s.core.trail_end
      s.core.trl.take qs ++ ((s.core.trl.take s.core.trail_end).drop qs).filter fun lit =>
        decide ((s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ target_lvl) := by
    rw [← hq_def]; rfl
  have hlenAux : ({ s with
      core := { k' with lvl := lvlAux, rsns := rsnsAux }
      scratch := scr' } : FullState).LengthsOk c :=
    ⟨{ hlen'.core_ok with lvl_len := btAuxList_len _ _ _ _ _ _,
                          rsns_len := btAuxList_len _ _ _ _ _ _ }, hlen'.scratch_ok⟩
  have hw' := chronoBacktrack_of_otfs hlen0 hw hlenAux hlt
    (fun i hi => by have h := hstep.2.1 i hi; rwa [hkeep_eq] at h)
    (by have h := hstep.1; rwa [hkeep_eq] at h)
    hvals_eq
    (fun v hv => btAuxList_get c s target_lvl q_start lvl' s.core.lvl 0#32 hon
      (fun w hw hex => by simp only [hstep.2.2.2.2.1 w hw, hex, ↓reduceIte])
      (fun w hw hnex => by simp only [hstep.2.2.2.2.1 w hw, hnex, ↓reduceIte]) hv hcl.cur_vars_le)
    (fun v hv => btAuxList_get c s target_lvl q_start rsns' s.core.rsns 0xFFFFFFFF#32 hon
      (fun w hw hex => by simp only [hstep.2.2.2.2.2 w hw, hex, ↓reduceIte])
      (fun w hw hnex => by simp only [hstep.2.2.2.2.2 w hw, hnex, ↓reduceIte]) hv hcl.cur_vars_le)
    hstep.2.2.1
  have htr_mem : ∀ i < trail_end', ∃ m < s.core.trail_end,
      (trl'[i]?.getD 0#32).toNat = (s.core.trl[m]?.getD 0#32).toNat ∧
      (q_start ≤ m →
        (s.core.lvl[(s.core.trl[m]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl) :=
    fun i hi => by
      have heq := hstep.2.1 i hi
      obtain ⟨m, hm, hmeq, hm_kept⟩ := fullBtKeep_mem_idx (s := s) (target_lvl := target_lvl)
        hq_le hte_lt (i := i) (by rw [← hstep.1]; exact hi)
      exact ⟨m, hm, by
        rw [heq, List.getElem?_eq_getElem (by rw [← hstep.1]; exact hi), Option.getD_some, hmeq],
        hm_kept⟩
  have hswap := fullWitnessInv_subst_lvl_rsns (F_cur := F_cur)
    (k' := k') (lvl0 := lvlAux) (rsns0 := rsnsAux) hw'
    (fun i hi => by
      obtain ⟨m, hm, hmeq, _⟩ := htr_mem i hi
      have hv_lt : (trl'[i]?.getD 0#32).toNat / 2 < s.core.cur_vars := by
        rw [hmeq]; exact Nat.div_lt_of_lt_mul (hw.trail_lits_lt m hm)
      exact btAuxList_get_kept c s target_lvl lvl' s.core.lvl 0#32
        (Nat.lt_of_lt_of_le hv_lt hcl.cur_vars_le) hm (by rw [hmeq]))
    (fun i hi => by
      obtain ⟨m, hm, hmeq, _⟩ := htr_mem i hi
      have hv_lt : (trl'[i]?.getD 0#32).toNat / 2 < s.core.cur_vars := by
        rw [hmeq]; exact Nat.div_lt_of_lt_mul (hw.trail_lits_lt m hm)
      exact btAuxList_get_kept c s target_lvl rsns' s.core.rsns 0xFFFFFFFF#32
        (Nat.lt_of_lt_of_le hv_lt hcl.cur_vars_le) hm (by rw [hmeq]))
  have hrs_eq : ∀ i < trail_end',
      k'.rsns[(k'.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
        s.core.rsns[(k'.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ∧
      k'.lvl[(k'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 =
        s.core.lvl[(k'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 := by
    intro i hi; obtain ⟨m, hm, hmeq, hm_kept⟩ := htr_mem i hi
    have hv_lt : (k'.trl[i]?.getD 0#32).toNat / 2 < s.core.cur_vars :=
      Nat.div_lt_of_lt_mul (hswap.trail_lits_lt i hi)
    have hl_le : (s.core.lvl[(k'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        target_lvl := by
      have h1 := hswap.lvl_le i hi
      by_cases hneg : ∃ j, q_start ≤ j ∧ j < s.core.trail_end ∧
          (s.core.trl[j]?.getD 0#32).toNat / 2 = (k'.trl[i]?.getD 0#32).toNat / 2 ∧
          target_lvl < (s.core.lvl[(k'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      · obtain ⟨j, hjq, hj, hveq, hbad⟩ := hneg
        have heq := hw.trail_vars_nodup j m hj hm (by dsimp only [k'] at hveq; rw [hveq, hmeq])
        subst heq; have hle := hm_kept hjq
        rw [show (k'.trl[i]?.getD 0#32).toNat = (s.core.trl[j]?.getD 0#32).toNat from hmeq] at hbad
        exact False.elim (Nat.not_le_of_lt hbad hle)
      · rw [show k'.lvl = lvl' from rfl, hstep.2.2.2.2.1 _ hv_lt, ite_eq_right hneg] at h1
        exact h1
    have hn : ¬ ∃ j, q_start ≤ j ∧ j < s.core.trail_end ∧
        (s.core.trl[j]?.getD 0#32).toNat / 2 = (k'.trl[i]?.getD 0#32).toNat / 2 ∧
        target_lvl < (s.core.lvl[(k'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat :=
      fun ⟨_, _, _, _, hbad⟩ => absurd hbad (by omega)
    exact ⟨by rw [show k'.rsns = rsns' from rfl, hstep.2.2.2.2.2 _ hv_lt, ite_eq_right hn],
           by rw [show k'.lvl = lvl' from rfl, hstep.2.2.2.2.1 _ hv_lt, ite_eq_right hn]⟩
  exact
    { hswap with
      ext_sound := hw.ext_sound, inconsistent_sound := hw.inconsistent_sound,
      arena := { len_ok := hw.arena.len_ok, refs_wf := hw.arena.refs_wf,
                 shrk_term := hw.arena.shrk_term, lits_lt := hw.arena.lits_lt,
                 entails := hw.arena.entails },
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr),
      level0_sound := fun i hi hl0 => by
        obtain ⟨m, hm, hmeq, _⟩ := htr_mem i hi
        rw [(hrs_eq i hi).2] at hl0; dsimp only [k'] at hl0 hmeq ⊢
        rw [hmeq] at hl0 ⊢; exact hw.level0_sound m hm hl0,
      reason_inv := fun idx hidx hne => by
        have hrs' := hswap.reason_inv idx hidx hne
        by_cases hb : (k'.rsns[(k'.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
            0x80000000#32) ≠ 0#32
        · rw [ite_eq_left hb] at hrs' ⊢
          obtain ⟨hot, _, m, hm, hmeq_m, hlvl_le⟩ := hrs'
          obtain ⟨m0, hm0, hmeq0, _⟩ := htr_mem idx hidx
          have hrs_eq0 := (hrs_eq idx hidx).1
          have hne0 : s.core.rsns[(s.core.trl[m0]?.getD 0#32).toNat / 2]?.getD
              0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
            dsimp only [k'] at hne hrs_eq0 hmeq0; rwa [← hmeq0, ← hrs_eq0]
          have hb0 : (s.core.rsns[(s.core.trl[m0]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
              0x80000000#32) ≠ 0#32 := by
            dsimp only [k'] at hb hrs_eq0 hmeq0; rwa [← hmeq0, ← hrs_eq0]
          have hlv0 : (s.core.lvl[(s.core.trl[m0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
              s.core.cur_level := by
            have h1 := hswap.lvl_le idx hidx
            rw [(hrs_eq idx hidx).2] at h1; dsimp only [k'] at h1 hmeq0 ⊢
            rw [← hmeq0]; omega
          have ho := hw.reason_inv_below m0 hm0 hlv0 hne0
          rw [ite_eq_left hb0] at ho
          dsimp only [k'] at hmeq0 hrs_eq0 hot ⊢
          rw [hmeq0] at hrs_eq0 hot ⊢
          rw [hrs_eq0] at hot ⊢
          exact ⟨hot, ho.2.1, m, hm, by rwa [← hrs_eq0, ← hmeq0], by rwa [← hrs_eq0, ← hmeq0]⟩
        · rw [ite_eq_right hb] at hrs' ⊢; exact hrs' }

/-! ## 2. `full_backtrack` `Func.wp` proof -/

private theorem backtrackScrFrame_refl (s : FullState) : BacktrackScrFrame s s :=
  ⟨⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, s.scratch.target_assigned,
    s.scratch.best_assigned, s.scratch.phases_target, s.scratch.phases_best, s.scratch.heap,
    s.scratch.pos, s.scratch.heap_len, s.scratch.q_search_idx, s.scratch.q_search_stamp, rfl⟩

private theorem backtrackScrFrame_of_save {s s1 : FullState}
    (h : FullProbeScratchPres s s1 ∧ ∃ ta' ba' pt' pb', s1.scratch = { s.scratch with
      target_assigned := ta', best_assigned := ba', phases_target := pt', phases_best := pb' }) :
    BacktrackScrFrame s s1 := by
  obtain ⟨hp, ta', ba', pt', pb', hsc⟩ := h
  exact ⟨hp, ta', ba', pt', pb', s.scratch.heap, s.scratch.pos, s.scratch.heap_len,
    s.scratch.q_search_idx, s.scratch.q_search_stamp, hsc⟩

private theorem backtrackScrFrame_of_heapPush {s s1 s2 : FullState} {coreU : FullCoreState}
    (h1 : BacktrackScrFrame s s1)
    (h2 : FullProbeScratchPres { core := coreU, scratch := s1.scratch } s2 ∧
      ∃ hp' ps' hl', s2.scratch = { s1.scratch with heap := hp', pos := ps', heap_len := hl' }) :
    BacktrackScrFrame s s2 := by
  obtain ⟨hp1, ta1, ba1, pt1, pb1, _, _, _, qsi1, qss1, hsc1⟩ := h1
  obtain ⟨hp2, hp', ps', hl', hsc2⟩ := h2
  exact ⟨hp1.trans hp2, ta1, ba1, pt1, pb1, hp', ps', hl', qsi1, qss1, by rw [hsc2, hsc1]⟩

private theorem backtrackScrFrame_qsearch {s st : FullState} {qi qs : BitVec 64}
    (h : BacktrackScrFrame s st) :
    BacktrackScrFrame s
      { st with scratch := { st.scratch with q_search_idx := qi, q_search_stamp := qs } } := by
  obtain ⟨hp, ta, ba, pt, pb, hp', ps', hl', _, _, hsc⟩ := h
  exact ⟨hp, ta, ba, pt, pb, hp', ps', hl', qi, qs, by dsimp only; rw [hsc]⟩

theorem full_backtrack_wp (Γ : Env)
    (hSave : ∀ a m Q X, fullSaveTargetBestSpec a m Q X →
      Γ "full_save_target_best" [i64] [] a m Q X)
    (hHeapPush : ∀ a m Q X, fullHeapPushSpec a m Q X →
      Γ "full_heap_push" [i64, i32] [] a m Q X) :
    ∀ a m Q X, fullBacktrackSpec a m Q X → Func.wp Γ full_backtrack_body a m Q X := by
  rintro ⟨h, target_lvl, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl64, htgt_mx, htrl_lits, hm, hQ⟩
  have hcl := hlen.core_ok; have hsl := hlen.scratch_ok
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hcl.cur_vars_le; have hte_le := hcl.trail_end_le
  full_steps
  · have hle : s.core.cur_level ≤ target_lvl.toNat := by
      rw [Nat.mod_eq_of_lt hcl64] at hc; exact hc
    have hte_self : s.core.trail_end ≤ s.core.trail_end := le_refl _
    exact hQ s.core.vals s.core.lvl s.core.rsns s.core.trl s.core.trail_pos s.core.trail_end
      s.core.propagated s.core.cur_level s.core.unassigned s.scratch m hlen hte_self
      hcl.propagated_le (Nat.min_eq_left hle).symm (backtrackScrFrame_refl s)
      htrl_lits (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun ⟨_, _, hw⟩ => full_backtrack_noop_clear_of_otfs (hw.elim FullWitnessInv.toOtfs id) hle)
      (fun _ _ hw _ => hw) (fun _ _ _ hlt => False.elim (by omega)) hm
  · have htgt_lt : target_lvl.toNat < s.core.cur_level := by
      rw [Nat.mod_eq_of_lt hcl64] at hc; omega
    have htgt_cmax : target_lvl.toNat < c.max_vars := htgt_mx htgt_lt
    clear hc
    c0_call hSave
    refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
    intro _ s1 m1 hcore1 hlen1 hscr1 hm1
    change (FullMem c s1 ⋆ R) m1 at hm1
    have hscr1' : BacktrackScrFrame s s1 := backtrackScrFrame_of_save hscr1
    have hc1_eq : s1.core = s.core := fullCoreState_agrees_with_scratch hcore1
    rcases s1 with ⟨c1, sc1⟩; dsimp only at hc1_eq; subst hc1_eq; clear hm hscr1
    have hcl1 := hlen1.core_ok; have hsl1 := hlen1.scratch_ok
    have htl1 : (target_lvl + 1).toNat = target_lvl.toNat + 1 := by bv_omega
    have hft_len : s.core.frame_trail.length = c.max_vars + 1 := hcl1.frame_trail_len
    have hft_idx_lt : (target_lvl + 1).toNat < s.core.frame_trail.length := by rw [htl1]; omega
    c0_to_group
    refine wp_join_group (ts := [i64])
      (fun (qv, ()) m2 =>
        qv.toNat = min (s.core.frame_trail[target_lvl.toNat + 1]?.getD 0#32).toNat
          s.core.trail_end ∧ m2 = m1) ?_ ?_
    · rintro _ ⟨qv, ⟨⟩⟩ m2 ⟨hqv_eq, rfl⟩
      let q_start := min (s.core.frame_trail[target_lvl.toNat + 1]?.getD 0#32).toNat
        s.core.trail_end
      have hqs_eq : q_start = min (s.core.frame_trail[target_lvl.toNat + 1]?.getD 0#32).toNat
          s.core.trail_end := rfl
      have hqs_le : q_start ≤ s.core.trail_end := Nat.min_le_right _ _
      c0_to_group
      refine wp_loop_inv
        (fun (q, p, ()) mL =>
          q_start ≤ q.toNat ∧ q.toNat ≤ p.toNat ∧ p.toNat ≤ s.core.trail_end ∧
          ∃ (vals1 : List (BitVec 8)) (lvl1 rsns1 trl1 tp1 : List (BitVec 32))
            (unass1 : BitVec 64) (scL : FullScratch),
            let sL : FullState :=
              { core := { s.core with vals := vals1, lvl := lvl1, rsns := rsns1, trl := trl1,
                                      trail_pos := tp1, unassigned := unass1 }
                scratch := scL }
            sL.LengthsOk c ∧ BacktrackScrFrame s sL ∧
            (∀ i, p.toNat ≤ i → trl1[i]? = s.core.trl[i]?) ∧
            (∀ i < q.toNat, (trl1[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
            (∀ l < 2 * s.core.cur_vars, (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl.toNat →
              vals1[l]?.getD 0#8 = s.core.vals[l]?.getD 0#8) ∧
            (∀ v < s.core.cur_vars, lvl1[v]?.getD 0#32 = s.core.lvl[v]?.getD 0#32 ∨
              target_lvl.toNat < (s.core.lvl[v]?.getD 0#32).toNat) ∧
            (FullBtDistinct s →
              FullBtStepEq s target_lvl.toNat q_start q.toNat p.toNat
                vals1 lvl1 rsns1 trl1 tp1) ∧ (FullMem c sL ⋆ R) mL)
        (fun (_, p, ()) _ => s.core.trail_end - p.toNat)
        (fun J hLoop => ?_) ?_
      · full_steps
        exact hLoop _ _ ⟨by omega, by simp [hqv_eq], by omega,
          s.core.vals, s.core.lvl, s.core.rsns, s.core.trl, s.core.trail_pos,
          s.core.unassigned, sc1, hlen1, hscr1', fun _ _ => rfl,
          fun i hi => htrl_lits i (by omega), fun _ _ _ => rfl, fun _ _ => Or.inl rfl,
          fun hd => by
            simpa [hqv_eq] using fullBtStepEq_init (by omega) (by rw [hcl1.trl_len]; omega) hd,
          hm1⟩
      · rintro J ⟨q, p, ⟨⟩⟩ mL ⟨hq_ge, hqp, hp_le, vals1, lvl1, rsns1, trl1, tp1, unass1, scL,
          hlenL, hscrL, hremL, htrl_q_lits, hvals_lowL, hlvl_lowL, hstepL, hmL⟩ hLoop
        clear hm1
        have hclL := hlenL.core_ok; have hslL := hlenL.scratch_ok
        have hvlL := hclL.vals_len; have hllL_len := hclL.lvl_len
        have hrslL := hclL.rsns_len; have htrlL := hclL.trl_len
        have htplL := hclL.trail_pos_len; have hflL := hclL.flags_len
        have hqslL := hslL.q_stamp_len
        dsimp only at hvlL hllL_len hrslL htrlL htplL hflL hqslL
        c0_split
        · have hp_lt : p.toNat < s.core.trail_end := by
            rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
          have htrl_p_eq : trl1[p.toNat]? = s.core.trl[p.toNat]? := hremL p.toNat (le_refl _)
          have hlit_s_lt : p.toNat < s.core.trl.length := by rw [hcl1.trl_len]; omega
          have hlit_1_lt : p.toNat < trl1.length := by rw [htrlL]; omega
          have hlit_eq : trl1[p.toNat]'hlit_1_lt = s.core.trl[p.toNat]'hlit_s_lt :=
            Option.some.inj (by
              rw [← List.getElem?_eq_getElem hlit_1_lt, htrl_p_eq,
                List.getElem?_eq_getElem hlit_s_lt])
          have hlit_lt : (trl1[p.toNat]'hlit_1_lt).toNat < 2 * s.core.cur_vars := by
            rw [hlit_eq]; simpa [List.getElem?_eq_getElem hlit_s_lt] using htrl_lits p.toNat hp_lt
          have hv_lt : (trl1[p.toNat]'hlit_1_lt).toNat / 2 < s.core.cur_vars :=
            Nat.div_lt_of_lt_mul hlit_lt
          have hv_sh : ((trl1[p.toNat]'hlit_1_lt >>> 1).setWidth 64).toNat =
              (trl1[p.toNat]'hlit_1_lt).toNat / 2 := by
            rw [zext_toNat _ (by decide), bv32_lshr_1]
          clear hc
          have hp1 : (p + 1).toNat = p.toNat + 1 := by bv_omega
          c0_to_group
          refine wp_join_group (ts := [i64])
            (fun (q', ()) mK =>
              q_start ≤ q'.toNat ∧ q'.toNat ≤ p.toNat + 1 ∧
              ∃ (valsK : List (BitVec 8)) (lvlK rsnsK trlK tpK : List (BitVec 32))
                (unassK : BitVec 64) (scK : FullScratch),
                let sK : FullState :=
                  { core := { s.core with vals := valsK, lvl := lvlK, rsns := rsnsK,
                                          trl := trlK, trail_pos := tpK, unassigned := unassK }
                    scratch := scK }
                sK.LengthsOk c ∧ BacktrackScrFrame s sK ∧
                (∀ i, p.toNat + 1 ≤ i → trlK[i]? = s.core.trl[i]?) ∧
                (∀ i < q'.toNat, (trlK[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
                (∀ l < 2 * s.core.cur_vars,
                  (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl.toNat →
                  valsK[l]?.getD 0#8 = s.core.vals[l]?.getD 0#8) ∧
                (∀ v < s.core.cur_vars, lvlK[v]?.getD 0#32 = s.core.lvl[v]?.getD 0#32 ∨
                  target_lvl.toNat < (s.core.lvl[v]?.getD 0#32).toNat) ∧
                (FullBtDistinct s →
                  FullBtStepEq s target_lvl.toNat q_start q'.toNat (p.toNat + 1)
                    valsK lvlK rsnsK trlK tpK) ∧ (FullMem c sK ⋆ R) mK) ?_ ?_
          · rintro _ ⟨q', ⟨⟩⟩ mK ⟨hq'1, hq'2, valsK, lvlK, rsnsK, trlK, tpK, unassK, scK,
              hlenK, hscrK, hremK, htrlK, hvals_lowK, hlvl_lowK, hstepK, hmK⟩
            full_steps
            exact hLoop _ _ (by dsimp only; omega)
              ⟨hq'1, by omega, by omega, valsK, lvlK, rsnsK, trlK, tpK, unassK, scK,
               hlenK, hscrK, fun i hi => hremK i (by omega), htrlK,
               hvals_lowK, hlvl_lowK, fun hd => by rw [hp1]; exact hstepK hd, hmK⟩
          · intro JQ_out hJQ_out; clear hLoop; c0_to_group
            refine wp_join_group (ts := [])
              (fun _ mE => target_lvl.toNat <
                (lvl1[(s.core.trl[p.toNat]'hlit_s_lt).toNat / 2]?.getD 0#32).toNat ∧ mE = mL)
              ?_ ?_
            · rintro _ _ mE ⟨hgt_lv, rfl⟩
              c0_split
              full_steps
              have hlit_2_lt : (trl1[p.toNat]'hlit_1_lt).toNat < vals1.length := by omega
              have hlit_neg_lt : ((trl1[p.toNat]'hlit_1_lt).toNat ^^^ 1) < vals1.length := by
                have := fullInv_var_xor1 (trl1[p.toNat]'hlit_1_lt).toNat; omega
              c0_to_group
              refine wp_join_group
                (fun _ mU => ∃ unass2 : BitVec 64,
                  (FullMem c { core := { s.core with
                                vals := (vals1.set (trl1[p.toNat]'hlit_1_lt).toNat 0#8).set
                                  ((trl1[p.toNat]'hlit_1_lt).toNat ^^^ 1) 0#8,
                                lvl := lvl1.set ((trl1[p.toNat]'hlit_1_lt).toNat / 2) 0#32,
                                rsns := rsns1.set ((trl1[p.toNat]'hlit_1_lt).toNat / 2)
                                  0xFFFFFFFF#32,
                                trl := trl1, trail_pos := tp1, unassigned := unass2 },
                               scratch := scL } ⋆ R) mU)
                ?_ ?_
              · rintro _ _ mU ⟨unass2, hmU⟩
                let coreU : FullCoreState :=
                  { s.core with
                    vals := (vals1.set (trl1[p.toNat]'hlit_1_lt).toNat 0#8).set
                      ((trl1[p.toNat]'hlit_1_lt).toNat ^^^ 1) 0#8,
                    lvl := lvl1.set ((trl1[p.toNat]'hlit_1_lt).toNat / 2) 0#32,
                    rsns := rsns1.set ((trl1[p.toNat]'hlit_1_lt).toNat / 2) 0xFFFFFFFF#32,
                    trl := trl1, trail_pos := tp1, unassigned := unass2 }
                have hclU : coreU.LengthsOk c :=
                  { hclL with vals_len := by dsimp only [coreU]; simp [hvlL],
                              lvl_len := by dsimp only [coreU]; simp [hllL_len],
                              rsns_len := by dsimp only [coreU]; simp [hrslL] }
                have hlenU : ({ core := coreU, scratch := scL } : FullState).LengthsOk c :=
                  ⟨hclU, hslL⟩
                c0_to_group
                refine wp_join_group
                  (fun _ mS => ∃ scS : FullScratch, scS.LengthsOk c ∧
                    BacktrackScrFrame s { core := coreU, scratch := scS } ∧
                    (FullMem c { core := coreU, scratch := scS } ⋆ R) mS) ?_ ?_
                · rintro _ _ mS ⟨scS, hslS, hscrS, hmS⟩
                  clear hmU
                  full_steps
                  have hlit_toNat : ∀ h,
                      (s.core.trl[p.toNat]'h).toNat = (trl1[p.toNat]'hlit_1_lt).toNat :=
                    fun _ => congrArg BitVec.toNat hlit_eq.symm
                  have hv_s : target_lvl.toNat <
                      (s.core.lvl[(trl1[p.toNat]'hlit_1_lt).toNat / 2]?.getD 0#32).toNat := by
                    rcases hlvl_lowL ((trl1[p.toNat]'hlit_1_lt).toNat / 2) hv_lt with hl_eq | h_gt
                    · rw [← hl_eq, ← hlit_toNat hlit_s_lt]; exact hgt_lv
                    · exact h_gt
                  have hvals_pop : ∀ l < 2 * s.core.cur_vars,
                      (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl.toNat →
                      coreU.vals[l]?.getD 0#8 = s.core.vals[l]?.getD 0#8 := by
                    intro l hl hlow
                    have hdiv_ne : l / 2 ≠ (trl1[p.toNat]'hlit_1_lt).toNat / 2 := fun heq => by
                      rw [heq] at hlow; omega
                    have hne1 : l ≠ (trl1[p.toNat]'hlit_1_lt).toNat := fun heq =>
                      hdiv_ne (congrArg (· / 2) heq)
                    have hne2 : l ≠ (trl1[p.toNat]'hlit_1_lt).toNat ^^^ 1 := fun heq => by
                      apply hdiv_ne; rw [heq, fullInv_var_xor1]
                    dsimp only [coreU]
                    rw [List.getElem?_set_ne hne2.symm, List.getElem?_set_ne hne1.symm]
                    exact hvals_lowL l hl hlow
                  have hlvl_pop : ∀ v < s.core.cur_vars,
                      coreU.lvl[v]?.getD 0#32 = s.core.lvl[v]?.getD 0#32 ∨
                      target_lvl.toNat < (s.core.lvl[v]?.getD 0#32).toNat := by
                    intro v hv; dsimp only [coreU]
                    by_cases hveq : v = (trl1[p.toNat]'hlit_1_lt).toNat / 2
                    · subst hveq; exact Or.inr hv_s
                    · rw [List.getElem?_set_ne (Ne.symm hveq)]; exact hlvl_lowL v hv
                  have hpop : FullBtDistinct s →
                      FullBtStepEq s target_lvl.toNat q_start q.toNat (p.toNat + 1)
                        ((vals1.set (trl1[p.toNat]'hlit_1_lt).toNat 0#8).set
                          ((trl1[p.toNat]'hlit_1_lt).toNat ^^^ 1) 0#8)
                        (lvl1.set ((trl1[p.toNat]'hlit_1_lt).toNat / 2) 0#32)
                        (rsns1.set ((trl1[p.toNat]'hlit_1_lt).toNat / 2) 0xFFFFFFFF#32)
                        trl1 tp1 := fun hd => by
                    have hp0 := fullBtStepEq_pop hq_ge hqp hp_lt
                      (by rw [hcl1.lvl_len]; exact hvlL) (by rw [hcl1.lvl_len]; exact hllL_len)
                      (by rw [hcl1.lvl_len]; exact hrslL) (by rw [hcl1.lvl_len]; exact hcv_le)
                      (by rw [hcl1.trl_len]; omega)
                      (by simpa [List.getElem?_eq_getElem hlit_s_lt] using htrl_lits p.toNat hp_lt)
                      (hstepL hd) hd hgt_lv
                    dsimp only at hp0; rwa [hlit_toNat] at hp0
                  exact hJQ_out (q, ()) mS
                    ⟨hq_ge, by omega, _, _, _, trl1, tp1, unass2, scS,
                     ⟨hclU, hslS⟩, hscrS, fun i hi => hremL i (by omega), htrl_q_lits,
                     hvals_pop, hlvl_pop, hpop, hmS⟩
                · intro JS hJS; clear hQ hJQ_out hstepL hremL htrl_q_lits; c0_split
                  · full_steps; c0_call hHeapPush
                    refine ⟨c, { core := coreU, scratch := scL }, R, rfl, hlenU, hmU, ?_⟩
                    intro _ sS mS hcoreS hlenS hscrS hmS
                    have hfrS := backtrackScrFrame_of_heapPush hscrL hscrS
                    have hcS : sS.core = coreU := fullCoreState_agrees_with_scratch hcoreS
                    rcases sS with ⟨cS, scS⟩; dsimp only at hcS; subst hcS
                    full_steps
                    exact hJS () mS ⟨scS, hlenS.scratch_ok, hfrS, hmS⟩
                  · c0_split
                    · full_steps
                      exact hJS () _ ⟨{ scL with
                        q_search_idx := (trl1[p.toNat]'hlit_1_lt >>> 1).setWidth 64,
                        q_search_stamp :=
                          (scL.q_stamp[((trl1[p.toNat]'hlit_1_lt >>> 1).setWidth 64).toNat]'(by
                            omega)).setWidth 64 },
                        { hslL with wsort_len := hslL.wsort_len },
                        backtrackScrFrame_qsearch hscrL, by assumption⟩
                    · full_steps; exact hJS () _ ⟨scL, hslL, hscrL, by assumption⟩
              · intro JU hJU; clear hQ hJQ_out hstepL hremL htrl_q_lits; c0_split
                · full_steps; exact hJU () _ ⟨unass1 + 1, by assumption⟩
                · full_steps; exact hJU () _ ⟨unass1, by assumption⟩
            · intro J1 hJ1; clear hQ; c0_split
              · c0_split
                · full_steps
                  have hqp1 : (q + 1).toNat = q.toNat + 1 := by bv_omega
                  have hq32 : q.setWidth 32 = BitVec.ofNat 32 q.toNat :=
                    BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_setWidth])
                  have hle_lv :
                      (lvl1[(s.core.trl[p.toNat]'hlit_s_lt).toNat / 2]?.getD 0#32).toNat ≤
                        target_lvl.toNat := by
                    have hc' : (lvl1[(trl1[p.toNat]'hlit_1_lt).toNat / 2 ^ 1]?.getD 0#32).toNat ≤
                        target_lvl.toNat := by
                      rw [List.getElem?_eq_getElem (by rw [hllL_len]; simp [Nat.pow_one]; omega),
                        Option.getD_some]
                      exact hc
                    rw [Nat.pow_one] at hc'
                    rwa [← hlit_eq]
                  have hkp : FullBtDistinct s →
                      FullBtStepEq s target_lvl.toNat q_start (q + 1).toNat (p.toNat + 1)
                        vals1 lvl1 rsns1 (trl1.set q.toNat (trl1[p.toNat]'hlit_1_lt))
                        (tp1.set ((trl1[p.toNat]'hlit_1_lt).toNat / 2) (q.setWidth 32)) :=
                    fun hd => by
                      have htrlp := htrl_lits p.toNat hp_lt
                      rw [List.getElem?_eq_getElem hlit_s_lt, Option.getD_some] at htrlp
                      have hk0 := fullBtStepEq_keep hq_ge hqp hp_lt
                        (by rw [hcl1.trl_len]; omega) (by omega) (by rw [htrlL, hcl1.trl_len])
                        (by rw [htplL, hcl1.lvl_len]) (by rw [hcl1.lvl_len]; exact hcv_le)
                        htrlp (hstepL hd) hd hle_lv
                      dsimp only at hk0; rw [hqp1, hq32, hlit_eq]; exact hk0
                  refine hJQ_out (q + 1, ()) m
                    ⟨by omega, by omega, vals1, lvl1, rsns1,
                     trl1.set q.toNat (trl1[p.toNat]'hlit_1_lt),
                     tp1.set ((trl1[p.toNat]'hlit_1_lt).toNat / 2) (q.setWidth 32),
                     unass1, scL,
                     ⟨{ hclL with trl_len := by simp [htrlL], trail_pos_len := by simp [htplL] },
                      hslL⟩, hscrL,
                     fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact hremL i (by omega),
                     fun i hi => by
                       rw [hqp1] at hi; by_cases hiq : i = q.toNat
                       · subst hiq; rw [List.getElem?_set_self (by omega), Option.getD_some]
                         exact hlit_lt
                       · rw [List.getElem?_set_ne (Ne.symm hiq)]; exact htrl_q_lits i (by omega),
                     hvals_lowL, hlvl_lowL, hkp, by rw [← hv_sh]; exact hm⟩
                · full_steps
                  have hgt_lv : target_lvl.toNat <
                      (lvl1[(s.core.trl[p.toNat]'hlit_s_lt).toNat / 2]?.getD 0#32).toNat := by
                    have hc' : ¬ (lvl1[(trl1[p.toNat]'hlit_1_lt).toNat / 2 ^ 1]?.getD
                        0#32).toNat ≤ target_lvl.toNat := by
                      rw [List.getElem?_eq_getElem (by rw [hllL_len]; simp [Nat.pow_one]; omega),
                        Option.getD_some]
                      exact hc
                    rw [Nat.pow_one] at hc'
                    rw [← hlit_eq]; omega
                  exact hJ1 () mL ⟨hgt_lv, rfl⟩
        · have hp_eq : p.toNat = s.core.trail_end := by
            rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
          rw [hp_eq] at hqp hstepL; clear hLoop hc
          c0_to_group
          refine wp_join_group
            (fun _ mP => (FullMem c { core := { s.core with
                vals := vals1, lvl := lvl1, rsns := rsns1, trl := trl1, trail_pos := tp1,
                trail_end := q.toNat, propagated := min s.core.propagated q_start,
                unassigned := unass1 }, scratch := scL } ⋆ R) mP) ?_ ?_
          · rintro _ _ mP hmP; c0_to_group
            refine wp_join_group
              (fun _ mF => (FullMem c { core := { s.core with
                  vals := vals1, lvl := lvl1, rsns := rsns1, trl := trl1, trail_pos := tp1,
                  trail_end := q.toNat,
                  propagated := min (min s.core.propagated q_start) q.toNat,
                  unassigned := unass1 }, scratch := scL } ⋆ R) mF) ?_ ?_
            · rintro _ _ mF hmF; clear hmP; full_steps
              have hlenF : ({ s with
                  core := { s.core with vals := vals1, lvl := lvl1, rsns := rsns1, trl := trl1,
                                        trail_pos := tp1, trail_end := q.toNat,
                                        propagated := min (min s.core.propagated q_start) q.toNat,
                                        cur_level := target_lvl.toNat, unassigned := unass1 }
                  scratch := scL } : FullState).LengthsOk c :=
                ⟨{ hclL with trail_end_le := by dsimp only; omega,
                             propagated_le := by dsimp only; omega }, hslL⟩
              have hlvl_fin : ∀ v < s.core.cur_vars,
                  (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl.toNat →
                  lvl1[v]?.getD 0#32 = s.core.lvl[v]?.getD 0#32 := fun v hv hlow =>
                (hlvl_lowL v hv).elim id fun hgt => False.elim (by omega)
              exact hQ vals1 lvl1 rsns1 trl1 tp1 q.toNat
                (min (min s.core.propagated q_start) q.toNat) target_lvl.toNat unass1 scL m
                hlenF hqp (Nat.min_le_right _ _) (Nat.min_eq_right (le_of_lt htgt_lt)).symm
                hscrL htrl_q_lits hvals_lowL hlvl_fin
                (fun ⟨_, _, hw⟩ =>
                  let hot := hw.elim FullWitnessInv.toOtfs id
                  (full_backtrack_clear_of_otfs hot htgt_lt hqs_eq
                    (hstepL ⟨hot.trail_vars_nodup, hot.trail_pos_inv⟩)).2)
                (fun F0 F_cur hw0 _ =>
                  full_backtrack_preserves_otfsWitness hlen (FullWitnessInv.toOtfs hw0)
                    htgt_lt hqs_eq hlenF (hstepL ⟨hw0.trail_vars_nodup, hw0.trail_pos_inv⟩))
                (fun F0 F_cur hw0 _ =>
                  full_backtrack_preserves_otfsWitness hlen hw0 htgt_lt hqs_eq hlenF
                    (hstepL ⟨hw0.trail_vars_nodup, hw0.trail_pos_inv⟩))
                hm
            · intro JF hJF; full_steps
              rw [Nat.min_eq_left (Nat.le_trans (Nat.min_le_right _ _) hq_ge)] at hJF
              exact hJF () mP hmP
          · intro JP hJP
            clear hQ hstepL hremL htrl_q_lits hscrL hlenL hclL hslL htrl_lits hvals_lowL hlvl_lowL
            c0_split
            · full_steps
              have hgt_qs : q_start < s.core.propagated := by
                have := hcl.propagated_le; simp only [Nat.reducePow] at hc; rw [hqs_eq]; omega
              rw [Nat.min_eq_right (le_of_lt hgt_qs)] at hJP; rw [hqv_eq] at hm
              exact hJP () m hm
            · full_steps
              have hle_qs : s.core.propagated ≤ q_start := by
                have := hcl.propagated_le
                rw [Nat.mod_eq_of_lt (by omega)] at hc; rw [hqv_eq] at hc; omega
              rw [Nat.min_eq_left hle_qs] at hJP; exact hJP () m hm
    · intro JQ hJQ; clear hQ; c0_split
      · full_steps
        have hgt_q : s.core.trail_end <
            (s.core.frame_trail[target_lvl.toNat + 1]?.getD 0#32).toNat := by
          have h1 : s.core.trail_end <
              (s.core.frame_trail[(target_lvl.toNat + 1) % 2 ^ 64]?.getD 0#32).toNat := by
            rw [List.getElem?_eq_getElem (by rw [hft_len]; omega), Option.getD_some]
            rw [Nat.mod_eq_of_lt (by omega : s.core.trail_end < 2 ^ 64)] at hc; exact hc
          rwa [Nat.mod_eq_of_lt (by omega)] at h1
        exact hJQ _ _ ⟨by rw [Nat.min_eq_right (le_of_lt hgt_q), bv64_ofNat_toNat (by omega)], rfl⟩
      · full_steps
        have hle_q : (s.core.frame_trail[target_lvl.toNat + 1]?.getD 0#32).toNat ≤
            s.core.trail_end := by
          have h1 : (s.core.frame_trail[(target_lvl.toNat + 1) % 2 ^ 64]?.getD 0#32).toNat ≤
              s.core.trail_end := by
            rw [List.getElem?_eq_getElem (by rw [hft_len]; omega), Option.getD_some]
            rw [Nat.mod_eq_of_lt (by omega : s.core.trail_end < 2 ^ 64)] at hc; omega
          rwa [Nat.mod_eq_of_lt (by omega)] at h1
        exact hJQ _ _ ⟨by
          rw [Nat.min_eq_left hle_q, zext_toNat _ (by decide), ← htl1,
            List.getElem?_eq_getElem (by omega), Option.getD_some], rfl⟩

end LeanQbe.T.Examples.Kissat.Full
