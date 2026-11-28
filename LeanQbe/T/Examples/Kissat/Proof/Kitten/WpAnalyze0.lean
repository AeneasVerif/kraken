/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Kitten.WpAnaClause

/-!
# Kissat `full_k6_analyze` Helpers (`Kissat.Proof.Kitten.WpAnalyze0`)

Pure invariant, resolvent, backtracking, learned-clause, and `K6TailEq` helpers supporting
`full_k6_analyze_wp`. Zero legacy `Full*` imports; zero `@[expose]` on theorems/lemmas;
`<= 100` cols; every decl `<= 450` LOC.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Kitten

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Kitten.Spec
open LeanQbe.T.Examples.Kissat.Src.Kitten

open K6MemATactics K6PtrTactics
open scoped K6MemATactics K6PtrTactics

theorem k6a_init_anaInv {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks) (hlvl_pos : 0 < ks.lvl.toNat)
    (hvdec : ∃ v < ks.nv.toNat, ks.lvlArr[v]?.getD 0#32 = ks.lvl) :
    let ks0 : K6State := { ks with nkl := 1#32, nana := 0#32, openCnt := 0#32 }
    K6AnaInv L P ks0 ks.trl_end.toNat ∧ K6AnaPreserved ks ks0 ∧ K6TailEq L ks ks0 := by
  intro ks0; have hm := L.hmaxV
  have heq : ks0 = ((ks.putHdr .nkl 1#32).putHdr .nana 0#32).putHdr .openCnt 0#32 := by k6_ext
  have hsh0 : ks0.ShapesOk L := by
    rw [heq]; exact ((hinv.shapes.putHdr .nkl 1#32).putHdr .nana 0#32).putHdr .openCnt 0#32
  have hnv_pos : 1 ≤ ks.nv.toNat := by obtain ⟨v, hv, _⟩ := hvdec; omega
  have hfl_clean := hinv.clauses.flags_clean
  have hfilt0 : ((List.range ks.trl_end.toNat).filter fun j =>
      let v := (ks0.trl[j]?.getD 0#32).toNat / 2
      decide (ks0.lvlArr[v]?.getD 0#32 = ks0.lvl ∧
        (ks0.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32)) = [] := by
    rw [List.filter_eq_nil_iff]; intro j hj; rw [List.mem_range] at hj
    have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
      rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; have := hinv.clauses.nv_le; omega
    have hlt := hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hj htrl_len)
    simp only [decide_eq_true_eq]; intro h
    exact h.2 (hfl_clean _ (by change (ks.trl[j]?.getD 0#32).toNat / 2 < ks.nv.toNat; omega))
  refine ⟨⟨hsh0, hinv.clauses.acap_eq, hinv.clauses.max_v_eq, hinv.clauses.max_orig_eq,
    hinv.clauses.max_cl_eq, hinv.clauses.nv_le, hinv.clauses.nc_le, hinv.clauses.alen_le,
    hinv.clauses.nassump_le, hlvl_pos, Nat.le_refl _, hinv.clauses.cl_wf, hinv.clauses.cl_mono,
    hinv.clauses.incons_ok, hinv.clauses.assump_ok, hinv.watches,
    k6BaseAssignOk_cast hinv.assign rfl rfl rfl rfl rfl rfl rfl rfl rfl, hsync, hinv.reasons,
    by change 1 ≤ (1#32 : BitVec 32).toNat; decide, by change 1 ≤ ks.nv.toNat; exact hnv_pos,
    by change (0#32 : BitVec 32).toNat ≤ ks.nv.toNat; simp,
    by change ((ks.ana.take 0).map BitVec.toNat).Nodup; simp,
    fun i hi => by change i < (0#32 : BitVec 32).toNat at hi; simp at hi,
    fun v hv => ⟨fun h => absurd (hfl_clean v hv) h,
      fun ⟨_, hi, _⟩ => by change _ < (0#32 : BitVec 32).toNat at hi; simp at hi⟩,
    fun i hi1 hi2 => by change i < (1#32 : BitVec 32).toNat at hi2; simp at hi2; omega,
    fun v hv hnz _ => absurd (hfl_clean v hv) hnz,
    fun v hv hnz => absurd (hfl_clean v hv) hnz,
    by change (((ks.kl.take 1).drop 1).map _).Nodup
       have : (ks.kl.take 1).drop 1 = [] := List.drop_eq_nil_of_le (by simp; omega)
       rw [this]; simp,
    by rw [hfilt0]; rfl,
    fun v hv hnz _ => absurd (hfl_clean v hv) hnz⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
     rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩⟩

theorem k6a_resolvent_step_skip {L : K6Layout} {P : (Nat → Bool) → Prop} {st : K6State}
    {idx' : Nat} (hinv : K6AnaInv L P st (idx' + 1))
    (hskip : ¬ ((st.flags[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32 ∧
      st.lvlArr[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 = st.lvl)) :
    K6AnaInv L P st idx' ∧ k6ResolventLits st (idx' + 1) = k6ResolventLits st idx' := by
  have hdec_f : decide (st.lvlArr[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 = st.lvl ∧
      (st.flags[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32) = false :=
    decide_eq_false fun h => hskip ⟨h.2, h.1⟩
  have hop_eq : st.openCnt.toNat = ((List.range idx').filter fun j =>
      let v := (st.trl[j]?.getD 0#32).toNat / 2
      decide (st.lvlArr[v]?.getD 0#32 = st.lvl ∧
        (st.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32)).length := by
    have h := hinv.open_eq; rw [List.range_succ, List.filter_append, List.filter_cons] at h
    simpa only [hdec_f, Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil] using h
  refine ⟨⟨hinv.shapes, hinv.acap_eq, hinv.max_v_eq, hinv.max_orig_eq, hinv.max_cl_eq,
    hinv.nv_le, hinv.nc_le, hinv.alen_le, hinv.nassump_le, hinv.lvl_pos,
    by have := hinv.idx_le; omega, hinv.cl_wf, hinv.cl_mono, hinv.incons_ok, hinv.assump_ok,
    hinv.watches, hinv.assign, hinv.synced, hinv.reasons, hinv.nkl_pos, hinv.nkl_le, hinv.nana_le,
    hinv.ana_nodup, hinv.ana_lt, hinv.flags_seen, hinv.kl_nonTop, hinv.kl_injective, hinv.nkl_count,
    hinv.kl_nodup, hop_eq, hinv.seen_in_trl⟩, ?_⟩
  unfold k6ResolventLits; rw [List.range_succ, List.filterMap_append, List.filterMap_cons,
    List.filterMap_nil]
  have hno : ¬ (st.lvlArr[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 = st.lvl ∧
      (st.flags[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32) :=
    fun h => hskip ⟨h.2, h.1⟩
  simp [hno]

theorem k6a_resolvent_step_hit {L : K6Layout} {P : (Nat → Bool) → Prop} {st : K6State}
    {idx' : Nat} (hinv : K6AnaInv L P st (idx' + 1))
    (hhit : (st.flags[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32 ∧
      st.lvlArr[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 = st.lvl) :
    let p := st.trl[idx']?.getD 0#32
    let st1 : K6State := { st with openCnt := st.openCnt - 1#32 }
    0 < st.openCnt.toNat ∧ K6AnaInv L P st1 idx' ∧ K6AnaPreserved st st1 ∧
    K6TailEq L st st1 ∧
    ∀ x ∈ k6ResolventLits st (idx' + 1), x ∈ (p.toNat ^^^ 1) :: k6ResolventLits st1 idx' := by
  intro p st1
  have hdec_t : decide (st.lvlArr[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 = st.lvl ∧
      (st.flags[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32) = true :=
    decide_eq_true ⟨hhit.2, hhit.1⟩
  have hop_succ : st.openCnt.toNat = ((List.range idx').filter fun j =>
      let v := (st.trl[j]?.getD 0#32).toNat / 2
      decide (st.lvlArr[v]?.getD 0#32 = st.lvl ∧
        (st.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32)).length + 1 := by
    have h := hinv.open_eq; rw [List.range_succ, List.filter_append, List.filter_cons] at h
    simpa only [hdec_t, ↓reduceIte, List.filter_nil, List.length_append, List.length_singleton]
      using h
  have hpos : 0 < st.openCnt.toNat := by omega
  have hsub : (st.openCnt - 1#32).toNat = st.openCnt.toNat - 1 := by bv_omega
  have hsh1 : st1.ShapesOk L := by
    have heq : st1 = st.putHdr .openCnt (st.openCnt - 1#32) := by k6_ext
    rw [heq]; exact hinv.shapes.putHdr .openCnt _
  have hinv1 : K6AnaInv L P st1 idx' :=
    ⟨hsh1, hinv.acap_eq, hinv.max_v_eq, hinv.max_orig_eq, hinv.max_cl_eq, hinv.nv_le, hinv.nc_le,
     hinv.alen_le, hinv.nassump_le, hinv.lvl_pos,
     by change idx' ≤ st.trl_end.toNat; have := hinv.idx_le; omega,
     hinv.cl_wf, hinv.cl_mono, hinv.incons_ok, hinv.assump_ok, hinv.watches,
     k6BaseAssignOk_cast hinv.assign rfl rfl rfl rfl rfl rfl rfl rfl rfl, hinv.synced,
     hinv.reasons, hinv.nkl_pos, hinv.nkl_le, hinv.nana_le, hinv.ana_nodup, hinv.ana_lt,
     hinv.flags_seen, hinv.kl_nonTop, hinv.kl_injective, hinv.nkl_count, hinv.kl_nodup,
     by change (st.openCnt - 1#32).toNat = ((List.range idx').filter fun j =>
          let v := (st.trl[j]?.getD 0#32).toNat / 2
          decide (st.lvlArr[v]?.getD 0#32 = st.lvl ∧
            (st.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32)).length
        rw [hsub, hop_succ]; omega,
     hinv.seen_in_trl⟩
  refine ⟨hpos, hinv1, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩, fun x hx => ?_⟩
  rw [k6a_mem_resolvent_iff] at hx; rw [List.mem_cons, k6a_mem_resolvent_iff]
  rcases hx with ⟨j, hj, htrl, hlvl, hfl⟩ | hr
  · by_cases hji : j = idx'
    · left; subst hji; have hx_eq : p.toNat = x ^^^ 1 := htrl; rw [hx_eq, k6_nat_xor1_xor1]
    · right; left; exact ⟨j, by omega, htrl, hlvl, hfl⟩
  · right; right; exact hr

theorem k6a_uip_exit {L : K6Layout} {P : (Nat → Bool) → Prop} {st1 : K6State} {idx' : Nat}
    (hinv : K6AnaInv L P st1 idx') (hop0 : st1.openCnt = 0#32) :
    k6ResolventLits st1 idx' = ((st1.kl.take st1.nkl.toNat).drop 1).map BitVec.toNat := by
  have hfilt_nil : ((List.range idx').filter fun j =>
      let v := (st1.trl[j]?.getD 0#32).toNat / 2
      decide (st1.lvlArr[v]?.getD 0#32 = st1.lvl ∧
        (st1.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32)) = [] := by
    have h := hinv.open_eq; rw [hop0] at h
    exact List.eq_nil_of_length_eq_zero (by simpa using h.symm)
  have hno : ∀ j < idx', ¬ (st1.lvlArr[(st1.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32 = st1.lvl ∧
      (st1.flags[(st1.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32) := by
    intro j hj hc
    have hmem : j ∈ ((List.range idx').filter fun j =>
        let v := (st1.trl[j]?.getD 0#32).toNat / 2
        decide (st1.lvlArr[v]?.getD 0#32 = st1.lvl ∧
          (st1.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32)) :=
      List.mem_filter.mpr ⟨List.mem_range.mpr hj, decide_eq_true hc⟩
    rw [hfilt_nil] at hmem; cases hmem
  unfold k6ResolventLits
  have hfm : ((List.range idx').filterMap fun j =>
      let l := (st1.trl[j]?.getD 0#32).toNat
      if st1.lvlArr[l / 2]?.getD 0#32 = st1.lvl ∧ (st1.flags[l / 2]?.getD 0#32 &&& 2#32) ≠ 0#32
      then some (l ^^^ 1) else none) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro j hj; rw [List.mem_range] at hj; dsimp only; rw [k6a_ite_f (hno j hj)]
  rw [hfm, List.nil_append]

theorem k6a_rsn_pre {L : K6Layout} {P : (Nat → Bool) → Prop} {st1 : K6State} {idx' : Nat}
    (hinv : K6AnaInv L P st1 idx') (hidx' : idx' < st1.trl_end.toNat)
    (hpos : 0 < st1.openCnt.toNat)
    (hlvl_p : st1.lvlArr[(st1.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 = st1.lvl) :
    let p := st1.trl[idx']?.getD 0#32; let pv := p >>> 1
    let rsn := st1.rsn[pv.toNat]?.getD 0#32
    p.toNat < 2 * st1.nv.toNat ∧ pv.toNat = p.toNat / 2 ∧ pv.toNat < st1.nv.toNat ∧
    rsn ≠ 0xFFFFFFFF#32 ∧ rsn.toNat < st1.nc.toNat ∧
    p.toNat ∈ k6ClauseLits st1 rsn.toNat ∧
    (∀ l ∈ k6ClauseLits st1 rsn.toNat, l / 2 = pv.toNat → l = p.toNat) ∧
    (∀ l ∈ k6ClauseLits st1 rsn.toNat, l / 2 ≠ pv.toNat →
      st1.vals[l]? = some 2#32 ∧ ∃ j < idx', (st1.trl[j]?.getD 0#32).toNat = l ^^^ 1) := by
  intro p pv rsn; have hm := L.hmaxV
  have htrl_len : st1.trl_end.toNat ≤ st1.trl.length := by
    rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; have := hinv.nv_le; omega
  have hp_lt : p.toNat < 2 * st1.nv.toNat :=
    hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hidx' htrl_len)
  obtain ⟨hpv_eq, hpv_lt⟩ := k6_bv32_div2_lt hp_lt
  have hrl : p.toNat / 2 < st1.rsn.length := by
    rw [hinv.shapes.rsn_len]; have := hinv.nv_le; omega
  have hfilt_ne : ((List.range idx').filter fun j =>
      let v := (st1.trl[j]?.getD 0#32).toNat / 2
      decide (st1.lvlArr[v]?.getD 0#32 = st1.lvl ∧
        (st1.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32)) ≠ [] := by
    intro hnil; have h := hinv.open_eq; rw [hnil] at h; simp at h; omega
  obtain ⟨j0, hj0_mem⟩ := List.exists_mem_of_ne_nil _ hfilt_ne
  rw [List.mem_filter, List.mem_range, decide_eq_true_eq] at hj0_mem
  have hrsn_ne : rsn ≠ 0xFFFFFFFF#32 := by
    have hd := hinv.assign.dec_earliest idx' j0 hj0_mem.1 hidx'
      (by rw [hlvl_p]; exact hinv.lvl_pos) (hj0_mem.2.1.trans hlvl_p.symm)
    dsimp only [rsn]; rw [hpv_eq, List.getElem?_eq_getElem hrl, Option.getD_some]
    simpa only [p, List.getElem?_eq_getElem hrl, Option.getD_some] using hd
  have hro := hinv.reasons idx' hidx'; dsimp only at hro
  have hrsn_eq : st1.rsn[p.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn := by
    dsimp only [rsn, pv]; rw [hpv_eq]
    simp only [List.getElem?_eq_getElem hrl, Option.getD_some]
  rw [hrsn_eq] at hro
  rcases hro with hff | ⟨hr_lt, hp_mem, hall⟩
  · exact absurd hff hrsn_ne
  · refine ⟨hp_lt, hpv_eq, hpv_lt, hrsn_ne, hr_lt, hp_mem, ?_, ?_⟩
    · intro l hl hlv; by_cases hlp : l = p.toNat
      · exact hlp
      · exfalso; obtain ⟨j, hj, hjeq⟩ := hall l hl hlp
        have hvar : (st1.trl[j]?.getD 0#32).toNat / 2 = p.toNat / 2 := by
          rw [hjeq, k6a_xor1_div2, hlv, hpv_eq]
        exact k6_trl_nodup_var_ne hinv.shapes hinv.nv_le hinv.assign
          (Nat.lt_trans hj hidx') hidx' (by omega) hvar
    · intro l hl hne
      have hlp : l ≠ p.toNat := fun heq => hne (by rw [heq, hpv_eq])
      obtain ⟨j, hj, hjeq⟩ := hall l hl hlp
      have hsy := hinv.synced j (Nat.lt_trans hj hidx'); dsimp only at hsy
      rw [hjeq, k6_nat_xor1_xor1] at hsy; exact ⟨hsy.2, j, hj, hjeq⟩

theorem k6a_swap_kl_preserves {L : K6Layout} {P : (Nat → Bool) → Prop}
    {stClean : K6State} {uip wi jlvl : BitVec 32}
    (hinv : K6Inv L P stClean) (hsync : K6TrailSynced stClean)
    (hnkl_pos : 1 ≤ stClean.nkl.toNat) (hnkl_le : stClean.nkl.toNat ≤ stClean.nv.toNat)
    (hwi : 2 ≤ stClean.nkl.toNat → 1 ≤ wi.toNat ∧ wi.toNat < stClean.nkl.toNat)
    (hkl_nt : ∀ k, 1 ≤ k → k < stClean.nkl.toNat →
      let l := (stClean.kl[k]?.getD 0#32).toNat
      l < 2 * stClean.nv.toNat ∧ 0 < (stClean.lvlArr[l / 2]?.getD 0#32).toNat ∧
      (stClean.lvlArr[l / 2]?.getD 0#32).toNat ≤ jlvl.toNat ∧ stClean.vals[l]? = some 2#32) :
    let stKl0 := stClean.putArr .kl 0 uip
    let stSw := if 2 ≤ stClean.nkl.toNat ∧ wi ≠ 1#32 then
      (stKl0.putArr .kl 1 (stKl0.kl[wi.toNat]?.getD 0#32)).putArr .kl wi.toNat
        (stKl0.kl[1]?.getD 0#32)
      else stKl0
    K6Inv L P stSw ∧ K6TrailSynced stSw ∧ K6AnaPreserved stClean stSw ∧ K6TailEq L stClean stSw ∧
    stSw.nkl = stClean.nkl ∧ stSw.nana = stClean.nana ∧ stSw.ana = stClean.ana ∧
    stSw.kl[0]? = some uip ∧
    (∀ x ∈ uip.toNat :: ((stClean.kl.take stClean.nkl.toNat).drop 1).map BitVec.toNat,
      x ∈ (stSw.kl.take stClean.nkl.toNat).map BitVec.toNat) ∧
    (∀ k, 1 ≤ k → k < stSw.nkl.toNat →
      let l := (stSw.kl[k]?.getD 0#32).toNat
      l < 2 * stSw.nv.toNat ∧ 0 < (stSw.lvlArr[l / 2]?.getD 0#32).toNat ∧
      (stSw.lvlArr[l / 2]?.getD 0#32).toNat ≤ jlvl.toNat ∧ stSw.vals[l]? = some 2#32) := by
  intro stKl0 stSw; have hm := L.hmaxV
  have hnv := hinv.clauses.nv_le; have hkl_len : stClean.kl.length = L.maxV := hinv.shapes.kl_len
  have hsh0 : stKl0.ShapesOk L := hinv.shapes.putArr .kl 0 uip
  have hshSw : stSw.ShapesOk L := by
    dsimp only [stSw]; by_cases hc : 2 ≤ stClean.nkl.toNat ∧ wi ≠ 1#32
    · rw [k6a_ite_t hc]; exact (hsh0.putArr .kl _ _).putArr .kl _ _
    · rw [k6a_ite_f hc]; exact hsh0
  have hfr : ∃ kl', stSw = { stClean with kl := kl' } := by
    dsimp only [stSw, stKl0]; by_cases hc : 2 ≤ stClean.nkl.toNat ∧ wi ≠ 1#32
    · rw [k6a_ite_t hc]; exact ⟨_, by k6_ext⟩
    · rw [k6a_ite_f hc]; exact ⟨_, by k6_ext⟩
  obtain ⟨kl', hfr_eq⟩ := hfr
  have hpres : K6AnaPreserved stClean stSw := by
    rw [hfr_eq]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have htlSw : K6TailEq L stClean stSw := by
    rw [hfr_eq]; exact ⟨rfl, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  have ⟨hinvSw, hsyncSw⟩ := k6a_inv_of_ana_clean hinv hsync hshSw hpres
    (by rw [hfr_eq]; exact hinv.clauses.nkl_le) (by rw [hfr_eq]; exact hinv.clauses.nana_le)
    (by rw [hfr_eq]; exact hinv.clauses.flags_clean)
  have hkl0_0 : stKl0.kl[0]? = some uip := by
    dsimp only [stKl0]; k6_field; exact List.getElem?_set_self (by omega)
  have hkl0_pos : ∀ k, 1 ≤ k → stKl0.kl[k]? = stClean.kl[k]? := fun k hk => by
    dsimp only [stKl0]; k6_field; exact List.getElem?_set_ne (by omega)
  have hsw_nkl : stSw.nkl = stClean.nkl := by rw [hfr_eq]
  have hsw0 : stSw.kl[0]? = some uip := by
    dsimp only [stSw]; by_cases hc : 2 ≤ stClean.nkl.toNat ∧ wi ≠ 1#32
    · rw [k6a_ite_t hc]; have ⟨hw1, _⟩ := hwi hc.1
      k6_field; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hkl0_0
    · rw [k6a_ite_f hc]; exact hkl0_0
  have hmem_of_idx : ∀ k < stClean.nkl.toNat,
      (stSw.kl[k]?.getD 0#32).toNat ∈ (stSw.kl.take stSw.nkl.toNat).map BitVec.toNat := by
    intro k hk; have hk_len : k < stSw.kl.length := by rw [hshSw.kl_len]; omega
    rw [List.mem_map]; refine ⟨stSw.kl[k]'hk_len, ?_, by simp [List.getElem?_eq_getElem hk_len]⟩
    rw [List.mem_take_iff_getElem]; exact ⟨k, by rw [hsw_nkl]; omega, rfl⟩
  have hbij : ∀ k, 1 ≤ k → k < stClean.nkl.toNat →
      ∃ k', 1 ≤ k' ∧ k' < stClean.nkl.toNat ∧ stSw.kl[k]? = stClean.kl[k']? := by
    intro k hk1 hk_lt; by_cases hc : 2 ≤ stClean.nkl.toNat ∧ wi ≠ 1#32
    · obtain ⟨hw1, hw_lt⟩ := hwi hc.1
      have hkl_sw : stSw.kl = (stKl0.kl.set 1 (stKl0.kl[wi.toNat]?.getD 0#32)).set wi.toNat
          (stKl0.kl[1]?.getD 0#32) := by dsimp only [stSw]; rw [k6a_ite_t hc]; k6_field
      have hl1 : 1 < stClean.kl.length := by omega
      have hlw : wi.toNat < stClean.kl.length := by omega
      by_cases hkw : k = wi.toNat
      · subst hkw; refine ⟨1, by omega, by omega, ?_⟩
        rw [hkl_sw, List.getElem?_set_self (by rw [List.length_set, hsh0.kl_len]; omega),
          hkl0_pos 1 (by omega), List.getElem?_eq_getElem hl1, Option.getD_some]
      · by_cases hk_1 : k = 1
        · subst hk_1; refine ⟨wi.toNat, hw1, hw_lt, ?_⟩
          rw [hkl_sw, List.getElem?_set_ne (by omega),
            List.getElem?_set_self (by rw [hsh0.kl_len]; omega),
            hkl0_pos wi.toNat hw1, List.getElem?_eq_getElem hlw, Option.getD_some]
        · refine ⟨k, hk1, hk_lt, ?_⟩
          rw [hkl_sw, List.getElem?_set_ne (Ne.symm hkw), List.getElem?_set_ne (Ne.symm hk_1),
            hkl0_pos k hk1]
    · refine ⟨k, hk1, hk_lt, ?_⟩
      have hkl_sw : stSw.kl = stKl0.kl := by dsimp only [stSw]; rw [k6a_ite_f hc]
      rw [hkl_sw, hkl0_pos k hk1]
  refine ⟨hinvSw, hsyncSw, hpres, htlSw, hsw_nkl, by rw [hfr_eq], by rw [hfr_eq], hsw0, ?_, ?_⟩
  · intro x hx; rw [← hsw_nkl]; rcases List.mem_cons.mp hx with rfl | hx_tl
    · have h0 := hmem_of_idx 0 (by omega); rwa [hsw0, Option.getD_some] at h0
    · rw [List.mem_map] at hx_tl; obtain ⟨b, hb, rfl⟩ := hx_tl
      rw [List.mem_iff_getElem] at hb; obtain ⟨k, hk, rfl⟩ := hb
      have hk1 : k + 1 < stClean.nkl.toNat := by simp [List.length_take, hkl_len] at hk; omega
      have hb_eq : (((stClean.kl.take stClean.nkl.toNat).drop 1)[k]'hk) =
          stClean.kl[k + 1]?.getD 0#32 := by
        simp only [List.getElem_drop, List.getElem_take]
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; congr 1; omega
      rw [hb_eq]; by_cases hc : 2 ≤ stClean.nkl.toNat ∧ wi ≠ 1#32
      · obtain ⟨hw1, hw_lt⟩ := hwi hc.1
        have hkl_sw : stSw.kl = (stKl0.kl.set 1 (stKl0.kl[wi.toNat]?.getD 0#32)).set wi.toNat
            (stKl0.kl[1]?.getD 0#32) := by dsimp only [stSw]; rw [k6a_ite_t hc]; k6_field
        have h1 : stSw.kl[wi.toNat]? = stClean.kl[1]? := by
          have hlen_w : wi.toNat < (stKl0.kl.set 1 (stKl0.kl[wi.toNat]?.getD 0#32)).length := by
            rw [List.length_set, hsh0.kl_len]; omega
          rw [hkl_sw, List.getElem?_set_self hlen_w, hkl0_pos 1 (by omega),
            List.getElem?_eq_getElem (by omega : 1 < stClean.kl.length), Option.getD_some]
        have h2 : stSw.kl[1]? = stClean.kl[wi.toNat]? := by
          rw [hkl_sw, List.getElem?_set_ne (by bv_omega),
            List.getElem?_set_self (by rw [hsh0.kl_len]; omega), hkl0_pos wi.toNat hw1,
            List.getElem?_eq_getElem (by omega : wi.toNat < stClean.kl.length), Option.getD_some]
        by_cases hk_1 : k + 1 = 1
        · rw [hk_1, ← h1]; exact hmem_of_idx wi.toNat hw_lt
        · by_cases hk_w : k + 1 = wi.toNat
          · rw [hk_w, ← h2]; exact hmem_of_idx 1 (by omega)
          · have h3 : stSw.kl[k + 1]? = stClean.kl[k + 1]? := by
              rw [hkl_sw, List.getElem?_set_ne (Ne.symm hk_w), List.getElem?_set_ne (Ne.symm hk_1),
                hkl0_pos (k + 1) (by omega)]
            rw [← h3]; exact hmem_of_idx (k + 1) hk1
      · have h3 : stSw.kl[k + 1]? = stClean.kl[k + 1]? := by
          have hkl_sw : stSw.kl = stKl0.kl := by dsimp only [stSw]; rw [k6a_ite_f hc]
          rw [hkl_sw, hkl0_pos (k + 1) (by omega)]
        rw [← h3]; exact hmem_of_idx (k + 1) hk1
  · intro k hk1 hk_lt; rw [hsw_nkl] at hk_lt
    obtain ⟨k', hk'1, hk'lt, hkeq⟩ := hbij k hk1 hk_lt
    dsimp only; rw [hkeq, hfr_eq]; exact hkl_nt k' hk'1 hk'lt

theorem k6a_after_bt_facts {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks stSw ksBt : K6State} {uip jlvl : BitVec 32}
    (hinvSw : K6Inv L P stSw) (hsyncSw : K6TrailSynced stSw) (hpresSw : K6AnaPreserved ks stSw)
    (huip_lt : uip.toNat < 2 * ks.nv.toNat)
    (huip_lvl : ks.lvlArr[uip.toNat / 2]?.getD 0#32 = ks.lvl)
    (hjlvl_lt : jlvl.toNat < ks.lvl.toNat)
    (hinvBt : K6Inv L P ksBt) (hlvlBt : ksBt.lvl = jlvl)
    (hte_le : ksBt.trl_end.toNat ≤ stSw.trl_end.toNat) (hbtPres : K6BtPreserved stSw ksBt)
    (hbtKept : ∀ i < ksBt.trl_end.toNat,
      ksBt.trl[i]? = stSw.trl[i]? ∧ ksBt.rsn[(ksBt.trl[i]?.getD 0#32).toNat / 2]? =
        stSw.rsn[(ksBt.trl[i]?.getD 0#32).toNat / 2]? ∧
      (ksBt.lvlArr[(ksBt.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ jlvl.toNat)
    (hB1 : ∀ i < stSw.trl_end.toNat,
      (stSw.lvlArr[(stSw.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ jlvl.toNat →
      i < ksBt.trl_end.toNat) :
    (¬ ∃ i < ksBt.trl_end.toNat, (ksBt.trl[i]?.getD 0#32).toNat / 2 = uip.toNat / 2) ∧
    ksBt.vals[uip.toNat]? = some 0#32 ∧ ksBt.trl_end.toNat < ksBt.nv.toNat ∧
    (∀ l < 2 * ks.nv.toNat, stSw.vals[l]? = some 2#32 →
      (ks.lvlArr[l / 2]?.getD 0#32).toNat ≤ jlvl.toNat →
      ∃ j < ksBt.trl_end.toNat, (ksBt.trl[j]?.getD 0#32).toNat = l ^^^ 1) ∧
    (∀ d ∈ k6TrailDecisions ksBt, ∃ i < ks.trl_end.toNat,
      (ks.trl[i]?.getD 0#32).toNat = d ∧ d ∈ k6TrailDecisions ks ∧
      (ks.lvlArr[d / 2]?.getD 0#32).toNat ≤ jlvl.toNat) ∧
    (∀ i < ks.trl_end.toNat,
      (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ jlvl.toNat →
      i < ksBt.trl_end.toNat ∧ ksBt.trl[i]? = ks.trl[i]? ∧
      ksBt.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? =
        ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?) := by
  have hm := L.hmaxV; have hnv_eq : ksBt.nv = ks.nv := hbtPres.nv.trans hpresSw.nv
  have hnv := hinvBt.clauses.nv_le
  have htrl_i : ∀ i < ksBt.trl_end.toNat, ksBt.trl[i]? = ks.trl[i]? := fun i hi =>
    (hbtKept i hi).1.trans (by rw [hpresSw.trl])
  have huip_none : ¬ ∃ i < ksBt.trl_end.toNat,
      (ksBt.trl[i]?.getD 0#32).toNat / 2 = uip.toNat / 2 := by
    rintro ⟨i, hi, hiv⟩
    have hkept := hbtPres.lvlArr_kept i hi; rw [hiv, hpresSw.lvlArr] at hkept
    have hle := hinvBt.assign.trl_lvl_le (uip.toNat / 2) (by rw [hnv_eq]; omega)
    rw [hkept, huip_lvl, hlvlBt] at hle; omega
  have huip_v0 : ksBt.vals[uip.toNat]? = some 0#32 := by
    have hlen : uip.toNat < ksBt.vals.length := by
      rw [hinvBt.shapes.vals_len]; rw [hnv_eq] at hnv; omega
    have h0 : ksBt.vals[uip.toNat]?.getD 0#32 = 0#32 := by
      by_cases h : ksBt.vals[uip.toNat]?.getD 0#32 = 0#32
      · exact h
      · exact absurd ((hinvBt.assign.vals_nz_iff_trl uip.toNat
        (by rw [hnv_eq]; exact huip_lt)).mp h) huip_none
    rw [List.getElem?_eq_getElem hlen] at h0 ⊢; exact congrArg some h0
  have hte_lt_nv : ksBt.trl_end.toNat < ksBt.nv.toNat :=
    k6_trl_end_lt_of_unassigned hinvBt.shapes hnv hinvBt.assign (by rw [hnv_eq]; exact huip_lt)
      (by simp [huip_v0])
  have htrl_len_bt : ksBt.trl_end.toNat ≤ ksBt.trl.length := by
    rw [hinvBt.shapes.trl_len]; have := hinvBt.assign.trl_end_le; omega
  have htrl_len_ks : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [← hpresSw.trl, ← hpresSw.trl_end, hinvSw.shapes.trl_len]
    have := hinvSw.assign.trl_end_le; have := hinvSw.clauses.nv_le; omega
  refine ⟨huip_none, huip_v0, hte_lt_nv, ?_, ?_, ?_⟩
  · intro l hl hval hlv
    obtain ⟨j, hj, hjeq⟩ :=
      k6_falsified_to_trail hinvSw.assign hsyncSw (by rw [hpresSw.nv]; exact hl) hval
    have hj_lv : (stSw.lvlArr[(stSw.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        jlvl.toNat := by rw [hjeq, k6a_xor1_div2, hpresSw.lvlArr]; exact hlv
    have hj_bt := hB1 j hj hj_lv
    exact ⟨j, hj_bt, by rw [htrl_i j hj_bt, ← hpresSw.trl, hjeq]⟩
  · intro d hd
    obtain ⟨i, hi_bt, hd_eq, hpos_bt, hrsn_bt⟩ := (k6_mem_trailDecisions_iff htrl_len_bt).mp hd
    have hi_ks : i < ks.trl_end.toNat := by rw [← hpresSw.trl_end]; omega
    have hkept := hbtPres.lvlArr_kept i hi_bt; have hrsn_k := (hbtKept i hi_bt).2.1
    rw [htrl_i i hi_bt] at hd_eq hkept hrsn_k
    rw [hpresSw.lvlArr] at hkept; rw [hpresSw.rsn] at hrsn_k
    have hpos_ks : 0 < (ks.lvlArr[d / 2]?.getD 0#32).toNat := by
      rw [← hd_eq, ← hkept, hd_eq]; exact hpos_bt
    have hrsn_ks : ks.rsn[d / 2]?.getD 0#32 = 0xFFFFFFFF#32 := by
      rw [← hd_eq, ← hrsn_k, hd_eq]; exact hrsn_bt
    have hd_ks : d ∈ k6TrailDecisions ks :=
      (k6_mem_trailDecisions_iff htrl_len_ks).mpr ⟨i, hi_ks, hd_eq, hpos_ks, hrsn_ks⟩
    have hlv_le : (ks.lvlArr[d / 2]?.getD 0#32).toNat ≤ jlvl.toNat := by
      have h1 := (hbtKept i hi_bt).2.2; rw [htrl_i i hi_bt, hkept, hd_eq] at h1; exact h1
    exact ⟨i, hi_ks, hd_eq, hd_ks, hlv_le⟩
  · intro i hi hlv
    have hi_bt := hB1 i (by rw [hpresSw.trl_end]; exact hi)
      (by rw [hpresSw.lvlArr, hpresSw.trl]; exact hlv)
    have hkept := hbtPres.lvlArr_kept i hi_bt
    rw [htrl_i i hi_bt, hpresSw.lvlArr] at hkept; exact ⟨hi_bt, htrl_i i hi_bt, hkept⟩

theorem k6a_assignStep_decisions_eq {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks : K6State} {lit rsn : BitVec 32} (hinv : K6Inv L P ks)
    (hlit : lit.toNat < 2 * ks.nv.toNat) (hte_lt : ks.trl_end.toNat < ks.nv.toNat)
    (hunass : ¬ ∃ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = lit.toNat / 2)
    (hnot_dec : ks.lvl = 0#32 ∨ rsn ≠ 0xFFFFFFFF#32) :
    let ks' := k6AssignStep ks lit rsn
    k6TrailDecisions ks' = k6TrailDecisions ks ∧
    (0 < ks'.lvl.toNat → ∃ i < ks'.trl_end.toNat,
      ks'.lvlArr[(ks'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = ks'.lvl) ∧
    (∀ i < ks.trl_end.toNat, i < ks'.trl_end.toNat ∧ ks'.trl[i]? = ks.trl[i]? ∧
      ks'.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? =
        ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?) := by
  intro ks'; have hm := L.hmaxV; have hnv := hinv.clauses.nv_le
  have hte1 : (ks.trl_end + 1#32).toNat = ks.trl_end.toNat + 1 := by bv_omega
  have hv_eq : (lit >>> 1).toNat = lit.toNat / 2 := (k6_bv32_div2_lt hlit).1
  have hte_len : ks.trl_end.toNat < ks.trl.length := by rw [hinv.shapes.trl_len]; omega
  have hv_len : lit.toNat / 2 < ks.lvlArr.length := by rw [hinv.shapes.lvlArr_len]; omega
  have hr_len : lit.toNat / 2 < ks.rsn.length := by rw [hinv.shapes.rsn_len]; omega
  have htr_self : ks'.trl[ks.trl_end.toNat]? = some lit := List.getElem?_set_self hte_len
  have htr_old : ∀ k < ks.trl_end.toNat, ks'.trl[k]? = ks.trl[k]? := fun k hk =>
    List.getElem?_set_ne (by omega)
  have hlv_self : ks'.lvlArr[lit.toNat / 2]? = some ks.lvl := by
    dsimp only [ks', k6AssignStep]; rw [hv_eq]; exact List.getElem?_set_self hv_len
  have hlv_ne : ∀ v, v ≠ lit.toNat / 2 → ks'.lvlArr[v]? = ks.lvlArr[v]? := fun v hne => by
    dsimp only [ks', k6AssignStep]; rw [hv_eq]; exact List.getElem?_set_ne (Ne.symm hne)
  have hrs_self : ks'.rsn[lit.toNat / 2]? = some rsn := by
    dsimp only [ks', k6AssignStep]; rw [hv_eq]; exact List.getElem?_set_self hr_len
  have hrs_ne : ∀ v, v ≠ lit.toNat / 2 → ks'.rsn[v]? = ks.rsn[v]? := fun v hne => by
    dsimp only [ks', k6AssignStep]; rw [hv_eq]; exact List.getElem?_set_ne (Ne.symm hne)
  have htrl_take : ks'.trl.take ks'.trl_end.toNat = ks.trl.take ks.trl_end.toNat ++ [lit] := by
    change (ks.trl.set ks.trl_end.toNat lit).take (ks.trl_end + 1#32).toNat = _
    rw [hte1, List.take_add_one, List.take_set_of_le (Nat.le_refl _),
      List.getElem?_set_self hte_len, Option.toList_some]
  have hnot_cond : ¬ (0 < ks.lvl.toNat ∧ rsn = 0xFFFFFFFF#32) := by
    rcases hnot_dec with h0 | hne
    · rw [h0]; simp
    · exact fun h => hne h.2
  refine ⟨?_,
    fun _ => ⟨ks.trl_end.toNat, (by change ks.trl_end.toNat < (ks.trl_end + 1#32).toNat; omega),
      by rw [htr_self, Option.getD_some, hlv_self, Option.getD_some]; rfl⟩,
    fun i hi => ⟨(by change i < (ks.trl_end + 1#32).toNat; omega), htr_old i hi,
      hlv_ne _ fun h => hunass ⟨i, hi, h⟩⟩⟩
  unfold k6TrailDecisions
  rw [htrl_take, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
    hlv_self, hrs_self, Option.getD_some, Option.getD_some, k6a_ite_f hnot_cond, List.append_nil]
  refine k6a_filterMap_congr fun x hx => ?_
  rw [List.mem_take_iff_getElem] at hx; obtain ⟨i, hi, rfl⟩ := hx
  have hne_v : (ks.trl[i]'(by omega)).toNat / 2 ≠ lit.toNat / 2 := fun h =>
    hunass ⟨i, by omega, by
      rw [List.getElem?_eq_getElem (by omega : i < ks.trl.length), Option.getD_some]; exact h⟩
  rw [hlv_ne _ hne_v, hrs_ne _ hne_v]

theorem k6a_clear_flags_tail {L : K6Layout} {ks stB : K6State} {fls : List (BitVec 32)}
    (htlB : K6TailEq L ks stB)
    (htl_fl : ∀ v, stB.nv.toNat ≤ v → v < L.maxV → fls[v]? = stB.flags[v]?) :
    K6TailEq L ks { stB with flags := fls } := by
  refine k6TailEq_trans htlB ⟨rfl, fun v hv hvm => ?_⟩
  exact ⟨rfl, rfl, htl_fl v hv hvm, rfl, rfl, rfl, rfl⟩

theorem k6a_setQueue_tail {L : K6Layout} {ksBt : K6State} {qf ql qs qst : BitVec 32}
    {qp qn qsa : List (BitVec 32)} :
    K6TailEq L ksBt
      { ksBt with qfirst := qf, qlast := ql, qsearch := qs, qstamp := qst,
                  qprev := qp, qnext := qn, qstampArr := qsa } :=
  ⟨rfl, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem k6a_nkl2_watch_prep {L : K6Layout} {P : (Nat → Bool) → Prop} {ks stSw ksBt st5 : K6State}
    {ar7 : List (BitVec 32)} {uip : BitVec 32}
    (hinv5 : K6Inv L P st5) (hst5_eq : ∃ qf ql qs qst qp qn qsa, st5 =
      { ksBt with qfirst := qf, qlast := ql, qsearch := qs, qstamp := qst,
                  qprev := qp, qnext := qn, qstampArr := qsa })
    (hbtPres : K6BtPreserved stSw ksBt) (hpresSw : K6AnaPreserved ks stSw)
    (hsw0 : stSw.kl[0]? = some uip) (huip_lt_k : uip.toNat < 2 * ks.nv.toNat)
    (hsw1_lt : (stSw.kl[1]?.getD 0#32).toNat < 2 * stSw.nv.toNat)
    (hte_lt_nv : ksBt.trl_end.toNat < ksBt.nv.toNat) (har7_len : ar7.length = L.acap) :
    let stM := (((({ st5 with arena := ar7 } : K6State).putHdr .alen
      (st5.alen + st5.nkl)).putArr .clOff st5.nc.toNat st5.alen).putArr .clSz st5.nc.toNat
      st5.nkl).putHdr .nc (st5.nc + 1#32)
    let stW := k6WatchStep stM st5.nc (st5.kl[0]?.getD 0#32) (st5.kl[1]?.getD 0#32)
    stM.ShapesOk L ∧ stM.max_v = L.mv32 ∧
    (stM.kl[0]?.getD 0#32).toNat < 2 * stM.nv.toNat ∧
    (stM.kl[1]?.getD 0#32).toNat < 2 * stM.nv.toNat ∧
    stW.ShapesOk L ∧ stW.max_v = L.mv32 ∧
    k6WatchStep stM st5.nc (stM.kl[0]?.getD 0#32) (stM.kl[1]?.getD 0#32) = stW ∧
    stW.trl_end.toNat < stW.nv.toNat := by
  intro stM stW
  obtain ⟨qf, ql, qs, qst, qp, qn, qsa, hst5⟩ := hst5_eq
  have hshM : stM.ShapesOk L := by
    have h0 : ({ st5 with arena := ar7 } : K6State).ShapesOk L :=
      { hinv5.shapes with arena_len := har7_len }
    exact (((h0.putHdr .alen _).putArr .clOff _ _).putArr .clSz _ _).putHdr .nc _
  have hshW : stW.ShapesOk L := k6WatchStep_preserves_shapes hshM _ _ _
  have hbt_nv : ksBt.nv = ks.nv := hbtPres.nv.trans hpresSw.nv
  have hk0 : (stM.kl[0]?.getD 0#32).toNat < 2 * stM.nv.toNat := by
    dsimp only [stM]; k6_field; rw [hst5, hbtPres.kl, hsw0, Option.getD_some]
    dsimp only; rw [hbt_nv]; omega
  have hk1 : (stM.kl[1]?.getD 0#32).toNat < 2 * stM.nv.toNat := by
    dsimp only [stM]; k6_field; rw [hst5, hbtPres.kl, hbtPres.nv]
    have h1 := hsw1_lt; rw [hpresSw.nv, ← hbt_nv] at h1; omega
  have hteW : stW.trl_end.toNat < stW.nv.toNat := by
    have hte1 : stW.trl_end = st5.trl_end := by
      dsimp only [stW, k6WatchStep, k6WatchStep0, stM]; k6_field
    have hnv1 : stW.nv = st5.nv := by dsimp only [stW, k6WatchStep, k6WatchStep0, stM]; k6_field
    rw [hte1, hnv1, hst5]; exact hte_lt_nv
  exact ⟨hshM, by dsimp only [stM]; k6_field; exact hinv5.clauses.max_v_eq, hk0, hk1, hshW,
    by dsimp only [stW, k6WatchStep, k6WatchStep0, stM]; k6_field; exact hinv5.clauses.max_v_eq,
    by dsimp only [stW, stM]; k6_field, hteW⟩

theorem k6a_ana_loop_p_facts {L : K6Layout} {P : (Nat → Bool) → Prop} {st : K6State}
    {idx_bv : BitVec 32} (hinvL : K6AnaInv L P st idx_bv.toNat) (hidx_pos : 0 < idx_bv.toNat)
    (hidx_sub : (idx_bv - 1#32).toNat = idx_bv.toNat - 1) :
    let p := st.trl[idx_bv.toNat - 1]?.getD 0#32
    idx_bv.toNat - 1 < st.trl_end.toNat ∧ (idx_bv - 1#32).toNat < szV L ∧
    p.toNat < 2 * st.nv.toNat ∧ (p >>> 1).toNat = p.toNat / 2 ∧ (p >>> 1).toNat < szV L ∧
    idx_bv.toNat = (idx_bv.toNat - 1) + 1 ∧ st.trl[(idx_bv - 1#32).toNat]?.getD 0#32 = p ∧
    (st.trl[(idx_bv - 1#32).toNat]?.getD 0#32 >>> 1).toNat < szV L := by
  intro p
  have hidx'_lt : idx_bv.toNat - 1 < st.trl_end.toNat := by have := hinvL.idx_le; omega
  have hidx'_mv : (idx_bv - 1#32).toNat < szV L := by
    unfold szV; rw [hidx_sub]; have := hinvL.assign.trl_end_le; have := hinvL.nv_le; omega
  have htrl_lenL : st.trl_end.toNat ≤ st.trl.length := by
    rw [hinvL.shapes.trl_len]; have := hinvL.assign.trl_end_le; have := hinvL.nv_le; omega
  have hp_lt : p.toNat < 2 * st.nv.toNat :=
    hinvL.assign.trl_lt _ (k6_mem_trailLits_of_lt hidx'_lt htrl_lenL)
  obtain ⟨hpv_eq, hpv_lt⟩ := k6_bv32_div2_lt hp_lt
  have hpv_mv : (p >>> 1).toNat < szV L := by unfold szV; have := hinvL.nv_le; omega
  have hp_eq : st.trl[(idx_bv - 1#32).toNat]?.getD 0#32 = p := by rw [hidx_sub]
  exact ⟨hidx'_lt, hidx'_mv, hp_lt, hpv_eq, hpv_mv, by omega, hp_eq, by rw [hp_eq]; exact hpv_mv⟩

theorem k6a_ana_mtf_exit_inv {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks stF stSw ksBt st5 : K6State} {uip : BitVec 32} (hinvBt : K6Inv L P ksBt)
    (hsyncBt : K6TrailSynced ksBt) (htl_bt : K6TailEq L ks ksBt)
    (hbtPres : K6BtPreserved stSw ksBt) (_hsw_nkl : stSw.nkl = stF.nkl)
    (hsw_mem :
      ∀ x ∈ uip.toNat :: ((stF.kl.take stF.nkl.toNat).drop 1).map BitVec.toNat,
        x ∈ (stSw.kl.take stSw.nkl.toNat).map BitVec.toNat)
    (hent_uip :
      SemEntails P (uip.toNat :: ((stF.kl.take stF.nkl.toNat).drop 1).map BitVec.toNat))
    (hsh5 : st5.ShapesOk L)
    (hst5_eq : ∃ qf ql qs qst qp qn qsa, st5 =
      { ksBt with qfirst := qf, qlast := ql, qsearch := qs, qstamp := qst,
                  qprev := qp, qnext := qn, qstampArr := qsa }) :
    K6Inv L P st5 ∧ K6TrailSynced st5 ∧ K6TailEq L ks st5 ∧
    SemEntails P ((st5.kl.take st5.nkl.toNat).map BitVec.toNat) ∧
    st5.acap.toNat = L.acap ∧ st5.max_cl.toNat = L.maxCl := by
  obtain ⟨qf, ql, qs, qst, qp, qn, qsa, hst5⟩ := hst5_eq
  have hac := L.hacap; have hm_v := L.hmaxV
  have hinv5 : K6Inv L P st5 := by
    rw [hst5] at hsh5 ⊢
    exact k6a_setQueue_preserves_inv hinvBt hsh5.qprev_len hsh5.qnext_len hsh5.qstampArr_len
  have hsync5 : K6TrailSynced st5 := by rw [hst5]; exact hsyncBt
  have htl_st5 : K6TailEq L ks st5 := by
    rw [hst5]
    exact k6TailEq_trans htl_bt (k6a_setQueue_tail (qf := qf) (ql := ql) (qs := qs)
      (qst := qst) (qp := qp) (qn := qn) (qsa := qsa))
  have hent_kl5 : SemEntails P ((st5.kl.take st5.nkl.toNat).map BitVec.toNat) := by
    rw [hst5, hbtPres.kl, hbtPres.nkl]
    exact k6a_semEntails_subset hsw_mem hent_uip
  have hca5 : st5.acap.toNat = L.acap := by
    rw [hinv5.clauses.acap_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by unfold dimacsBound at hac; omega)]
  have hmc5 : st5.max_cl.toNat = L.maxCl := by
    rw [hinv5.clauses.max_cl_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by unfold K6Layout.maxCl; omega)]
  exact ⟨hinv5, hsync5, htl_st5, hent_kl5, hca5, hmc5⟩

end LeanQbe.T.Examples.Kissat.Proof.Kitten
end
