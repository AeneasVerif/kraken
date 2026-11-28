/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Kitten.Tactics

/-!
# Trail, Refutation, & Assignment Invariant Lemmas (`Kissat.Proof.Kitten.LemmasTrail`)

Covers `K6Inv.mono_P`, `K6ScratchInv.mono_P`, `k6ClausesOk_cast`, `k6BaseAssignOk_cast`,
`k6AddTicks_preserves_inv`, `k6SetStatus_preserves_inv`, `k6_trailSynced_of_lvl0`, clause/trail
membership and refutation helpers (`k6_conflict_unsat_lvl0`, `k6_conflict_unsat_assumps`,
`k6_falsified_assump_unsat`), and `k6AssignStep_preserves_inv` / `k6SetIncons_preserves_inv`.

Zero legacy `Full*` imports; zero `@[expose]` on theorems/lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Kitten

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec

open K6MemATactics K6PtrTactics
open scoped K6MemATactics K6PtrTactics

/-! ## 1. Model-Set Monotonicity & Invariant Field-Cast Helpers -/

theorem K6Inv.mono_P {L : K6Layout} {P P' : (Nat → Bool) → Prop} {ks : K6State}
    (himp : ∀ β, P' β → P β) (h : K6Inv L P ks) : K6Inv L P' ks :=
  { shapes := h.shapes
    clauses := { h.clauses with
      cl_wf := fun cid hc => let w := h.clauses.cl_wf cid hc
        ⟨w.1, w.2.1, w.2.2.1, fun β hβ => w.2.2.2 β (himp β hβ)⟩
      incons_ok := fun hi β hβ => h.clauses.incons_ok hi β (himp β hβ) }
    watches := h.watches
    assign := { h.assign with
      lvl0_ok := fun i hi hl0 => let w := h.assign.lvl0_ok i hi hl0
        ⟨w.1, w.2.1, fun β hβ => w.2.2 β (himp β hβ)⟩ }
    reasons := h.reasons }

theorem K6ScratchInv.mono_P {P P' : (Nat → Bool) → Prop} {scr : List (BitVec 32)}
    (himp : ∀ β, P' β → P β) (h : K6ScratchInv P scr) : K6ScratchInv P' scr :=
  ⟨h.1, h.2.1, h.2.2.mono_P himp⟩

theorem k6ClausesOk_cast {L : K6Layout} {P : (Nat → Bool) → Prop} {ks ks' : K6State}
    (h : K6ClausesOk L P ks)
    (h1 : ks'.acap = ks.acap) (h2 : ks'.max_v = ks.max_v) (h3 : ks'.max_orig = ks.max_orig)
    (h4 : ks'.max_cl = ks.max_cl) (h5 : ks'.nv = ks.nv) (h6 : ks'.nc = ks.nc)
    (h7 : ks'.alen = ks.alen) (h8 : ks'.nassump = ks.nassump) (h9 : ks'.nkl = ks.nkl)
    (h10 : ks'.nana = ks.nana) (h11 : ks'.incons = ks.incons) (h12 : ks'.assump = ks.assump)
    (h13 : ks'.flags = ks.flags) (h14 : ks'.clOff = ks.clOff) (h15 : ks'.clSz = ks.clSz)
    (h16 : ks'.arena = ks.arena) : K6ClausesOk L P ks' := by
  rcases h with ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩
  refine ⟨h1.trans c1, h2.trans c2, h3.trans c3, h4.trans c4, h5 ▸ c5, h6 ▸ c6, h7 ▸ c7,
    h8 ▸ c8, h9 ▸ c9, h10 ▸ c10, ?_, ?_, h11 ▸ c13, ?_, ?_⟩
  · intro cid hc; rw [h6] at hc
    have := c11 cid hc
    simp only [k6ClauseSize, k6ClauseOff, k6ClauseLits, h14, h15, h16, h7, h5]; exact this
  · intro c1' c2' hlt hc; rw [h6] at hc
    simp only [k6ClauseSize, k6ClauseOff, h14, h15]; exact c12 c1' c2' hlt hc
  · intro i hi; rw [h8] at hi; rw [h12, h5]; exact c14 i hi
  · intro v hv; rw [h5] at hv; rw [h13]; exact c15 v hv

theorem k6BaseAssignOk_cast {P : (Nat → Bool) → Prop} {ks ks' : K6State}
    (h : K6BaseAssignOk P ks)
    (h1 : ks'.nv = ks.nv) (h2 : ks'.lvl = ks.lvl) (h3 : ks'.prop = ks.prop)
    (h4 : ks'.trl_end = ks.trl_end) (h5 : ks'.unass = ks.unass)
    (h6 : ks'.lvlArr = ks.lvlArr) (h7 : ks'.rsn = ks.rsn)
    (h8 : ks'.trl = ks.trl) (h9 : ks'.vals = ks.vals) : K6BaseAssignOk P ks' := by
  rcases h with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩
  refine ⟨by rw [h4, h1]; exact a1, by rw [h3, h4]; exact a2, by rw [h5, h4, h1]; exact a3,
    fun l hl => by rw [h1] at hl; rw [h9]; exact a4 l hl,
    fun l hl => by rw [h1] at hl; rw [h9]; exact a5 l hl,
    fun l hl => by rw [h1] at hl; rw [h9, h4, h8]; exact a6 l hl,
    by unfold k6TrailLits; rw [h8, h4]; exact a7,
    fun l hl => by unfold k6TrailLits at hl; rw [h8, h4] at hl; rw [h1]; exact a8 l hl,
    fun v hv => by rw [h1] at hv; rw [h6, h2]; exact a9 v hv,
    fun v hv hv0 => by rw [h1] at hv; rw [h9] at hv0; rw [h6, h7]; exact a10 v hv hv0,
    fun i j hij hj => by rw [h4] at hj; rw [h6, h8]; exact a11 i j hij hj,
    fun i j hij hi hp heq => by
      rw [h4] at hi; rw [h6, h8] at hp heq; rw [h7, h8]; exact a12 i j hij hi hp heq,
    fun i hi => by rw [h4] at hi; dsimp only; rw [h8, h6, h9]; exact a13 i hi⟩

theorem k6AddTicks_preserves_inv {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (tk' : BitVec 32) : K6Inv L P (ks.putHdr .ticks tk') :=
  ⟨hinv.shapes.putHdr .ticks tk',
   k6ClausesOk_cast hinv.clauses (by k6_field) (by k6_field) (by k6_field) (by k6_field)
     (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field)
     (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field),
   by dsimp only [K6State.putHdr]; exact hinv.watches,
   k6BaseAssignOk_cast hinv.assign (by k6_field) (by k6_field) (by k6_field) (by k6_field)
     (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field),
   by dsimp only [K6State.putHdr]; exact hinv.reasons⟩

theorem k6SetStatus_preserves_inv {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (st' : BitVec 32) : K6Inv L P (ks.putHdr .status st') :=
  ⟨hinv.shapes.putHdr .status st',
   k6ClausesOk_cast hinv.clauses (by k6_field) (by k6_field) (by k6_field) (by k6_field)
     (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field)
     (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field),
   by dsimp only [K6State.putHdr]; exact hinv.watches,
   k6BaseAssignOk_cast hinv.assign (by k6_field) (by k6_field) (by k6_field) (by k6_field)
     (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field),
   by dsimp only [K6State.putHdr]; exact hinv.reasons⟩

/-! ## 2. Trail, Clause-Literal, & Refutation Helpers -/

theorem k6_mem_clauseLits_iff {ks : K6State} {cid : Nat}
    (hbd : k6ClauseOff ks cid + k6ClauseSize ks cid ≤ ks.arena.length) {l : Nat} :
    l ∈ k6ClauseLits ks cid ↔
      ∃ n < k6ClauseSize ks cid, (ks.arena[k6ClauseOff ks cid + n]?.getD 0#32).toNat = l := by
  unfold k6ClauseLits; rw [List.mem_map]; constructor
  · rintro ⟨b, hb, rfl⟩; rw [List.mem_iff_getElem] at hb; obtain ⟨n, hn, rfl⟩ := hb
    have hns : n < k6ClauseSize ks cid := by simp [List.length_take] at hn; omega
    have hlt : k6ClauseOff ks cid + n < ks.arena.length := by omega
    exact ⟨n, hns, by simp [List.getElem_take, List.getElem_drop, List.getElem?_eq_getElem hlt]⟩
  · rintro ⟨n, hn, rfl⟩
    have hlt : k6ClauseOff ks cid + n < ks.arena.length := by omega
    refine ⟨ks.arena[k6ClauseOff ks cid + n]'hlt, ?_, by simp [List.getElem?_eq_getElem hlt]⟩
    rw [List.mem_iff_getElem]
    exact ⟨n, by simp [List.length_take, List.length_drop]; omega,
      by simp [List.getElem_take, List.getElem_drop]⟩

theorem k6_mem_trailLits_of_lt {ks : K6State} {i : Nat}
    (hi : i < ks.trl_end.toNat) (hle : ks.trl_end.toNat ≤ ks.trl.length) :
    (ks.trl[i]?.getD 0#32).toNat ∈ k6TrailLits ks := by
  unfold k6TrailLits; rw [List.mem_map]
  refine ⟨ks.trl[i]'(by omega), ?_,
    by simp [List.getElem?_eq_getElem (by omega : i < ks.trl.length)]⟩
  rw [List.mem_iff_getElem]; exact ⟨i, by simp [List.length_take]; omega, by simp⟩

theorem k6_trailSynced_of_lvl0 {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hl0 : ks.lvl = 0#32) : K6TrailSynced ks := fun i hi => by
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; have := hinv.clauses.nv_le; omega
  have hl_lt := hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hi htrl_len)
  have hle := hinv.assign.trl_lvl_le ((ks.trl[i]?.getD 0#32).toNat / 2) (by omega)
  rw [hl0] at hle
  have h0 : ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = 0#32 :=
    BitVec.eq_of_toNat_eq (Nat.eq_zero_of_le_zero hle)
  have ok := hinv.assign.lvl0_ok i hi h0
  exact ⟨ok.1, ok.2.1⟩

theorem k6_mem_trailDecisions_iff {ks : K6State} {d : Nat}
    (hle : ks.trl_end.toNat ≤ ks.trl.length) :
    d ∈ k6TrailDecisions ks ↔
      ∃ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat = d ∧
        0 < (ks.lvlArr[d / 2]?.getD 0#32).toNat ∧ ks.rsn[d / 2]?.getD 0#32 = 0xFFFFFFFF#32 := by
  unfold k6TrailDecisions; rw [List.mem_filterMap]; constructor
  · rintro ⟨l, hl, hif⟩; obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
    have hlt : i < ks.trl_end.toNat := by simp at hi; omega
    simp only [List.getElem_take] at hif
    have h1 : i < ks.trl.length := by omega
    split at hif
    · rename_i hc; simp only [Option.some.injEq] at hif
      refine ⟨i, hlt, ?_, hif ▸ hc.1, hif ▸ hc.2⟩
      rw [List.getElem?_eq_getElem h1, Option.getD_some]; exact hif
    · simp at hif
  · rintro ⟨i, hi, hteq, hpos, hrs⟩
    have h1 : i < ks.trl.length := by omega
    refine ⟨ks.trl[i], ?_, ?_⟩
    · rw [List.mem_iff_getElem]; exact ⟨i, by simp [List.length_take]; omega, by simp⟩
    · rw [List.getElem?_eq_getElem h1, Option.getD_some] at hteq
      rw [hteq]; simp [hpos, hrs]

theorem k6_trl_nodup_var_ne {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hsh : ks.ShapesOk L) (hnv : ks.nv.toNat ≤ L.maxV) (hba : K6BaseAssignOk P ks)
    {i j : Nat} (hi : i < ks.trl_end.toNat) (hj : j < ks.trl_end.toNat) (hne : i ≠ j) :
    (ks.trl[i]?.getD 0#32).toNat / 2 ≠ (ks.trl[j]?.getD 0#32).toNat / 2 := by
  have hte := hba.trl_end_le
  have hlen : ks.trl_end.toNat ≤ ks.trl.length := by rw [hsh.trl_len]; omega
  have hnd := hba.trl_nodup; unfold k6TrailLits at hnd; rw [List.map_map] at hnd
  have hm_len : (List.map ((fun x => x / 2) ∘ BitVec.toNat)
      (ks.trl.take ks.trl_end.toNat)).length = ks.trl_end.toNat := by
    simp [List.length_take]; omega
  intro heq
  exact hne (k6_list_nodup_getElem_inj hnd (by omega) (by omega) (by
    simp only [List.getElem_map, List.getElem_take, Function.comp_def]
    rw [List.getElem?_eq_getElem (by omega : i < ks.trl.length),
      List.getElem?_eq_getElem (by omega : j < ks.trl.length), Option.getD_some,
      Option.getD_some] at heq
    exact heq))

theorem k6_trl_end_lt_of_unassigned {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hsh : ks.ShapesOk L) (hnv : ks.nv.toNat ≤ L.maxV) (hba : K6BaseAssignOk P ks)
    {l : Nat} (hl : l < 2 * ks.nv.toNat) (h0 : ks.vals[l]?.getD 0#32 = 0#32) :
    ks.trl_end.toNat < ks.nv.toNat := by
  have hle := hba.trl_end_le
  by_cases hlt : ks.trl_end.toNat < ks.nv.toNat
  · exact hlt
  · exfalso
    have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by rw [hsh.trl_len]; omega
    have hv_mem := k6_nodup_mem_of_length_ge (n := ks.nv.toNat) hba.trl_nodup (fun x hx => by
      rw [List.mem_map] at hx; obtain ⟨t, ht, rfl⟩ := hx; have := hba.trl_lt t ht; omega)
      (by simp [k6TrailLits, List.length_take]; omega) (v := l / 2) (by omega)
    rw [List.mem_map] at hv_mem; obtain ⟨t, ht, htv⟩ := hv_mem
    unfold k6TrailLits at ht; rw [List.mem_map] at ht; obtain ⟨bv, hbv, rfl⟩ := ht
    obtain ⟨i, hi, heq_bv⟩ := List.getElem_of_mem hbv
    have hi_te : i < ks.trl_end.toNat := by simp [List.length_take] at hi; omega
    simp only [List.getElem_take] at heq_bv
    have hnz := (hba.vals_nz_iff_trl l hl).mpr ⟨i, hi_te, by
      rw [List.getElem?_eq_getElem (by omega : i < ks.trl.length), Option.getD_some, heq_bv]
      exact htv⟩
    exact hnz h0

theorem k6_vals_xor1_zero {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) {l : Nat} (hl : l < 2 * ks.nv.toNat)
    (hz : ks.vals[l]?.getD 0#32 = 0#32) : ks.vals[l ^^^ 1]?.getD 0#32 = 0#32 := by
  have hnl : l ^^^ 1 < 2 * ks.nv.toNat := by
    rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  rcases hinv.assign.vals_dom (l ^^^ 1) hnl with h0 | h1 | h2
  · exact h0
  · exfalso; have hneg := (hinv.assign.vals_neg_iff (l ^^^ 1) hnl).mp h1
    rw [k6_nat_xor1_xor1, hz] at hneg; cases hneg
  · exfalso; have hneg := (hinv.assign.vals_neg_iff l hl).mpr h2; rw [hz] at hneg; cases hneg

theorem k6_falsified_to_trail {P : (Nat → Bool) → Prop} {ks : K6State}
    (hba : K6BaseAssignOk P ks) (hsync : K6TrailSynced ks) {l : Nat} (hl : l < 2 * ks.nv.toNat)
    (hfals : ks.vals[l]? = some 2#32) :
    ∃ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat = l ^^^ 1 := by
  obtain ⟨i, hi, hveq⟩ := (hba.vals_nz_iff_trl l hl).mp (by simp [hfals])
  have hs := hsync i hi
  let tl := (ks.trl[i]?.getD 0#32).toNat
  change ks.vals[tl]? = some 1#32 ∧ ks.vals[tl ^^^ 1]? = some 2#32 at hs
  rcases (litVar_eq_iff tl l).mp (by simpa [litVar] using hveq) with heq | heq
  · rw [heq, hfals] at hs; cases hs.1
  · exact ⟨i, hi, heq⟩

theorem k6_falsified_lvl0_entails {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hlvl0 : ks.lvl = 0#32) {l : Nat} (hl : l < 2 * ks.nv.toNat)
    (hfals : ks.vals[l]? = some 2#32) :
    (∃ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat = l ^^^ 1) ∧
    SemEntails P [l ^^^ 1] := by
  obtain ⟨i, hi, hveq⟩ := (hinv.assign.vals_nz_iff_trl l hl).mp (by simp [hfals])
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; have := hinv.clauses.nv_le; omega
  let tl := (ks.trl[i]?.getD 0#32).toNat
  have htl_lt : tl < 2 * ks.nv.toNat :=
    hinv.assign.trl_lt tl (k6_mem_trailLits_of_lt hi htrl_len)
  have hl0 : ks.lvlArr[tl / 2]?.getD 0#32 = 0#32 := by
    have hle := hinv.assign.trl_lvl_le (tl / 2) (by omega)
    rw [hlvl0] at hle; exact BitVec.eq_of_toNat_eq (Nat.eq_zero_of_le_zero hle)
  have hok := hinv.assign.lvl0_ok i hi hl0
  change ks.vals[tl]? = some 1#32 ∧ ks.vals[tl ^^^ 1]? = some 2#32 ∧ SemEntails P [tl] at hok
  rcases (litVar_eq_iff tl l).mp (by simpa [litVar] using hveq) with heq | heq
  · rw [heq, hfals] at hok; cases hok.1
  · rw [show litNeg l = l ^^^ 1 from rfl] at heq
    exact ⟨⟨i, hi, heq⟩, heq ▸ hok.2.2⟩

theorem k6_conflict_unsat_lvl0 {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hlvl0 : ks.lvl = 0#32) {cid : Nat} (hcid : cid < ks.nc.toNat)
    (hfals : ∀ l ∈ k6ClauseLits ks cid, ks.vals[l]? = some 2#32) : ∀ β, ¬ P β :=
  fun β hβ => by
    obtain ⟨l, hl, hs⟩ := (clause_sat_cnfClause_iff β _).mp
      ((hinv.clauses.cl_wf cid hcid).2.2.2 β hβ)
    have hneg := (k6_falsified_lvl0_entails hinv hlvl0
      ((hinv.clauses.cl_wf cid hcid).2.2.1 l hl) (hfals l hl)).2 β hβ
    exact absurd ((sat_cnfClause_singleton β l).mpr hs)
      ((sat_cnfClause_litNeg_iff β l).mp hneg)

theorem k6_trail_entails_assumps {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hdec : ∀ d ∈ k6TrailDecisions ks, d ∈ k6AssumpLits ks)
    {β : Nat → Bool} (hP : P β) (hA : (unitsCnf (k6AssumpLits ks)).Sat β) :
    ∀ i < ks.trl_end.toNat, (cnfClause [(ks.trl[i]?.getD 0#32).toNat]).Sat β := by
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; have := hinv.clauses.nv_le; omega
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hi
    let l := (ks.trl[i]?.getD 0#32).toNat
    rcases hinv.reasons i hi with hrsn | ⟨hr_lt, hl_mem, hoth⟩
    · by_cases hl0 : ks.lvlArr[l / 2]?.getD 0#32 = 0#32
      · exact (hinv.assign.lvl0_ok i hi hl0).2.2 β hP
      · have hpos : 0 < (ks.lvlArr[l / 2]?.getD 0#32).toNat :=
          Nat.pos_of_ne_zero fun hz => hl0 (BitVec.eq_of_toNat_eq hz)
        have hl_lt := hinv.assign.trl_lt l (k6_mem_trailLits_of_lt hi htrl_len)
        have hrl : l / 2 < ks.rsn.length := by
          rw [hinv.shapes.rsn_len]; have := hinv.clauses.nv_le; omega
        have hrsn' : ks.rsn[l / 2]?.getD 0#32 = 0xFFFFFFFF#32 := by
          rw [List.getElem?_eq_getElem hrl, Option.getD_some] at hrsn ⊢; exact hrsn
        have hd_mem : l ∈ k6TrailDecisions ks :=
          (k6_mem_trailDecisions_iff htrl_len).mpr ⟨i, hi, rfl, hpos, hrsn'⟩
        exact (sat_unitsCnf_iff β (k6AssumpLits ks)).mp hA l (hdec l hd_mem)
    · have hce := (hinv.clauses.cl_wf _ hr_lt).2.2.2 β hP
      obtain ⟨x, hx_mem, hxs⟩ := (clause_sat_cnfClause_iff β _).mp hce
      by_cases hxl : x = l
      · rw [hxl] at hxs; exact (sat_cnfClause_singleton β l).mpr hxs
      · obtain ⟨j, hj_lt, hj_eq⟩ := hoth x hx_mem hxl
        have hjs := ih j hj_lt (Nat.lt_trans hj_lt hi)
        rw [hj_eq] at hjs
        exact absurd ((sat_cnfClause_singleton β x).mpr hxs)
          ((sat_cnfClause_litNeg_iff β x).mp hjs)

theorem k6_conflict_unsat_assumps {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks)
    (hdec : ∀ d ∈ k6TrailDecisions ks, d ∈ k6AssumpLits ks)
    {cid : Nat} (hcid : cid < ks.nc.toNat)
    (hfals : ∀ l ∈ k6ClauseLits ks cid, ks.vals[l]? = some 2#32) :
    ∀ β, P β → ¬ (unitsCnf (k6AssumpLits ks)).Sat β := fun β hP hA => by
  obtain ⟨l, hl_mem, hls⟩ := (clause_sat_cnfClause_iff β _).mp
    ((hinv.clauses.cl_wf cid hcid).2.2.2 β hP)
  have hl_lt := (hinv.clauses.cl_wf cid hcid).2.2.1 l hl_mem
  obtain ⟨i, hi, hieq⟩ := k6_falsified_to_trail hinv.assign hsync hl_lt (hfals l hl_mem)
  have hts := k6_trail_entails_assumps hinv hdec hP hA i hi
  rw [hieq] at hts
  exact (sat_cnfClause_litNeg_iff β l).mp hts ((sat_cnfClause_singleton β l).mpr hls)

theorem k6_falsified_assump_unsat {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks)
    (hdec : ∀ d ∈ k6TrailDecisions ks, d ∈ k6AssumpLits ks)
    {i : Nat} (hi : i < ks.nassump.toNat)
    (hfals : ks.vals[(ks.assump[i]?.getD 0#32).toNat]? = some 2#32) :
    ∀ β, P β → ¬ (unitsCnf (k6AssumpLits ks)).Sat β := fun β hP hA => by
  let a := (ks.assump[i]?.getD 0#32).toNat
  have ha_lt := hinv.clauses.assump_ok i hi
  have ha_mem : a ∈ k6AssumpLits ks := by
    unfold k6AssumpLits; rw [List.mem_map]
    have hlen : ks.nassump.toNat ≤ ks.assump.length := by
      rw [hinv.shapes.assump_len]; exact hinv.clauses.nassump_le
    refine ⟨ks.assump[i]?.getD 0#32, ?_, rfl⟩
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp [List.length_take]; omega,
      by simp [List.getElem?_eq_getElem (by omega : i < ks.assump.length)]⟩
  have hsa := (sat_unitsCnf_iff β (k6AssumpLits ks)).mp hA a ha_mem
  obtain ⟨j, hj, hjeq⟩ := k6_falsified_to_trail hinv.assign hsync ha_lt hfals
  have hts := k6_trail_entails_assumps hinv hdec hP hA j hj
  rw [hjeq] at hts
  exact (sat_cnfClause_litNeg_iff β a).mp hts hsa

/-! ## 3. Assignment Step & `incons` Flag Preservation -/

theorem k6AssignStep_preserves_shapes {L : K6Layout} {ks : K6State} (h : ks.ShapesOk L)
    (lit rsn : BitVec 32) : (k6AssignStep ks lit rsn).ShapesOk L :=
  { h with lvlArr_len := by simp [k6AssignStep, h.lvlArr_len]
           rsn_len := by simp [k6AssignStep, h.rsn_len]
           trl_len := by simp [k6AssignStep, h.trl_len]
           flags_len := by simp [k6AssignStep, h.flags_len]
           vals_len := by simp [k6AssignStep, h.vals_len] }

private theorem k6_flags_bit1_preserved (fl : BitVec 32) (b : Bool) :
    ((if b then fl ||| 1#32 else fl &&& ~~~1#32) &&& 2#32) = (fl &&& 2#32) := by
  cases b <;> ext i hi
  · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.getElem_and, BitVec.getElem_not]
    have h1 : (1#32 : BitVec 32)[i] = false ∨ (2#32 : BitVec 32)[i] = false := by
      revert i hi; decide
    rcases h1 with h | h <;> simp [h]
  · simp only [↓reduceIte, BitVec.getElem_and, BitVec.getElem_or]
    have h1 : (1#32 : BitVec 32)[i] = false ∨ (2#32 : BitVec 32)[i] = false := by
      revert i hi; decide
    rcases h1 with h | h <;> simp [h]

theorem k6AssignStep_preserves_inv {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks)
    {lit rsn : BitVec 32} (hlit : lit.toNat < 2 * ks.nv.toNat)
    (hun : ks.vals[lit.toNat]? = some 0#32)
    (hlvl0 : ks.lvl = 0#32 → SemEntails P [lit.toNat])
    (hdec : 0 < ks.lvl.toNat → rsn = 0xFFFFFFFF#32 →
      ∀ i < ks.trl_end.toNat, ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 ≠ ks.lvl)
    (hrsn_ok : rsn = 0xFFFFFFFF#32 ∨
      (rsn.toNat < ks.nc.toNat ∧ lit.toNat ∈ k6ClauseLits ks rsn.toNat ∧
       ∀ x ∈ k6ClauseLits ks rsn.toNat, x ≠ lit.toNat →
         ∃ j < ks.trl_end.toNat, (ks.trl[j]?.getD 0#32).toNat = x ^^^ 1)) :
    K6Inv L P (k6AssignStep ks lit rsn) ∧ K6TrailSynced (k6AssignStep ks lit rsn) := by
  have hm := L.hmaxV
  let ks' := k6AssignStep ks lit rsn
  have hsh' := k6AssignStep_preserves_shapes hinv.shapes lit rsn
  have hnv := hinv.clauses.nv_le
  have hte_lt := k6_trl_end_lt_of_unassigned hinv.shapes hnv hinv.assign hlit (by simp [hun])
  have hun_pos : 0 < ks.unass.toNat := by have := hinv.assign.unass_eq; omega
  have e_te : ks'.trl_end.toNat = ks.trl_end.toNat + 1 := by
    dsimp only [ks', k6AssignStep]; bv_omega
  have e_un : ks'.unass.toNat = ks.unass.toNat - 1 := by
    dsimp only [ks', k6AssignStep]; simp only [hun_pos, ite_true]; bv_omega
  have hnl_eq : (lit ^^^ 1#32).toNat = lit.toNat ^^^ 1 := by simp
  have hv_eq : (lit >>> 1).toNat = lit.toNat / 2 := (k6_bv32_div2_lt hlit).1
  have hlit_len : lit.toNat < 2 * L.maxV := by omega
  have hnl_len : lit.toNat ^^^ 1 < 2 * L.maxV := by
    rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  have hv_len : lit.toNat / 2 < L.maxV := by omega
  have hte_len : ks.trl_end.toNat < L.maxV := by omega
  have hne_nl : lit.toNat ≠ lit.toNat ^^^ 1 := by
    rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  have hnot_trl : ∀ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := by
    intro i hi heq; have hnz := (hinv.assign.vals_nz_iff_trl lit.toNat hlit).mpr ⟨i, hi, heq⟩
    simp [hun] at hnz
  have hvals_lit : ks'.vals[lit.toNat]? = some 1#32 := by
    dsimp only [ks', k6AssignStep]
    rw [hnl_eq, List.getElem?_set_ne hne_nl.symm,
      List.getElem?_set_self (by rw [hinv.shapes.vals_len]; omega)]
  have hvals_nl : ks'.vals[lit.toNat ^^^ 1]? = some 2#32 := by
    dsimp only [ks', k6AssignStep]
    rw [hnl_eq, List.getElem?_set_self (by simp [hinv.shapes.vals_len]; omega)]
  have hvals_other : ∀ x, x / 2 ≠ lit.toNat / 2 → ks'.vals[x]? = ks.vals[x]? := fun x hne => by
    have hx1 : lit.toNat ≠ x := by
      rcases k6_nat_xor1_cases x with ⟨_, _⟩ | ⟨_, _⟩ <;>
        rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
    have hx2 : lit.toNat ^^^ 1 ≠ x := by
      rcases k6_nat_xor1_cases x with ⟨_, _⟩ | ⟨_, _⟩ <;>
        rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
    dsimp only [ks', k6AssignStep]; rw [hnl_eq, List.getElem?_set_ne hx2, List.getElem?_set_ne hx1]
  have htrl_lt_idx : ∀ i < ks.trl_end.toNat, ks'.trl[i]? = ks.trl[i]? := fun i hi => by
    dsimp only [ks', k6AssignStep]; exact List.getElem?_set_ne (by omega)
  have htrl_end_idx : ks'.trl[ks.trl_end.toNat]? = some lit := by
    dsimp only [ks', k6AssignStep]
    exact List.getElem?_set_self (by rw [hinv.shapes.trl_len]; omega)
  have hlvl_other : ∀ v, v ≠ lit.toNat / 2 → ks'.lvlArr[v]? = ks.lvlArr[v]? := fun v hne => by
    dsimp only [ks', k6AssignStep]; rw [hv_eq]; exact List.getElem?_set_ne hne.symm
  have hlvl_v : ks'.lvlArr[lit.toNat / 2]? = some ks.lvl := by
    dsimp only [ks', k6AssignStep]; rw [hv_eq]
    exact List.getElem?_set_self (by rw [hinv.shapes.lvlArr_len]; omega)
  have hrsn_other : ∀ v, v ≠ lit.toNat / 2 → ks'.rsn[v]? = ks.rsn[v]? := fun v hne => by
    dsimp only [ks', k6AssignStep]; rw [hv_eq]; exact List.getElem?_set_ne hne.symm
  have hrsn_v : ks'.rsn[lit.toNat / 2]? = some rsn := by
    dsimp only [ks', k6AssignStep]; rw [hv_eq]
    exact List.getElem?_set_self (by rw [hinv.shapes.rsn_len]; omega)
  have hcl' : K6ClausesOk L P ks' :=
    { hinv.clauses with
      flags_clean := fun v hv => by
        by_cases hvv : v = lit.toNat / 2
        · subst hvv
          have hfl : ks'.flags[lit.toNat / 2]?.getD 0#32 =
              if (lit &&& 1#32) ≠ 0#32 then ks.flags[lit.toNat / 2]?.getD 0#32 ||| 1#32
              else ks.flags[lit.toNat / 2]?.getD 0#32 &&& ~~~1#32 := by
            dsimp only [ks', k6AssignStep]
            rw [hv_eq, List.getElem?_set_self (by rw [hinv.shapes.flags_len]; omega),
              Option.getD_some]
          rw [hfl]
          by_cases hc : (lit &&& 1#32) ≠ 0#32
          · simpa [hc] using (k6_flags_bit1_preserved
              (ks.flags[lit.toNat / 2]?.getD 0#32) true).trans
              (hinv.clauses.flags_clean (lit.toNat / 2) hv)
          · simpa [hc] using (k6_flags_bit1_preserved
              (ks.flags[lit.toNat / 2]?.getD 0#32) false).trans
              (hinv.clauses.flags_clean (lit.toNat / 2) hv)
        · have hf : ks'.flags[v]? = ks.flags[v]? := by
            dsimp only [ks', k6AssignStep]; rw [hv_eq]; exact List.getElem?_set_ne (Ne.symm hvv)
          rw [hf]; exact hinv.clauses.flags_clean v hv }
  have hsync' : K6TrailSynced ks' := fun i hi => by
    rw [e_te] at hi
    by_cases hie : i = ks.trl_end.toNat
    · subst hie
      change ks'.vals[(ks'.trl[ks.trl_end.toNat]?.getD 0#32).toNat]? = some 1#32 ∧
        ks'.vals[(ks'.trl[ks.trl_end.toNat]?.getD 0#32).toNat ^^^ 1]? = some 2#32
      rw [htrl_end_idx, Option.getD_some]; exact ⟨hvals_lit, hvals_nl⟩
    · have hi' : i < ks.trl_end.toNat := by omega
      let l := (ks.trl[i]?.getD 0#32).toNat
      have hne_v := hnot_trl i hi'
      have hne_vx : (l ^^^ 1) / 2 ≠ lit.toNat / 2 := by
        rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
      change ks'.vals[(ks'.trl[i]?.getD 0#32).toNat]? = some 1#32 ∧
        ks'.vals[(ks'.trl[i]?.getD 0#32).toNat ^^^ 1]? = some 2#32
      rw [htrl_lt_idx i hi']; change ks'.vals[l]? = some 1#32 ∧ ks'.vals[l ^^^ 1]? = some 2#32
      rw [hvals_other l hne_v, hvals_other (l ^^^ 1) hne_vx]; exact hsync i hi'
  have htrl_take : ks'.trl.take ks'.trl_end.toNat = ks.trl.take ks.trl_end.toNat ++ [lit] := by
    apply List.ext_getElem
    · have hlen1 : ks'.trl.length = L.maxV := hsh'.trl_len
      rw [List.length_take, List.length_append, List.length_cons, List.length_nil,
        e_te, hlen1, List.length_take, hinv.shapes.trl_len,
        Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
    · intro i hi1 _
      have h1 : i < ks.trl_end.toNat + 1 := by simp [List.length_take, e_te] at hi1; omega
      simp only [List.getElem_take]
      by_cases hie : i = ks.trl_end.toNat
      · subst hie
        have hgl : ks'.trl[ks.trl_end.toNat]'(by rw [hsh'.trl_len]; omega) = lit := by
          have := htrl_end_idx; rw [List.getElem?_eq_getElem (by rw [hsh'.trl_len]; omega)] at this
          exact Option.some.inj this
        rw [hgl, List.getElem_append_right (by simp [List.length_take, hinv.shapes.trl_len]; omega)]
        simp [List.length_take, hinv.shapes.trl_len,
          show min ks.trl_end.toNat L.maxV = ks.trl_end.toNat by omega]
      · have hi' : i < ks.trl_end.toNat := by omega
        have hgl : ks'.trl[i]'(by rw [hsh'.trl_len]; omega) =
            ks.trl[i]'(by rw [hinv.shapes.trl_len]; omega) := by
          have := htrl_lt_idx i hi'
          rw [List.getElem?_eq_getElem (by rw [hsh'.trl_len]; omega),
            List.getElem?_eq_getElem (by rw [hinv.shapes.trl_len]; omega)] at this
          exact Option.some.inj this
        rw [hgl, List.getElem_append_left (by simp [List.length_take, hinv.shapes.trl_len]; omega),
          List.getElem_take]
  have hba' : K6BaseAssignOk P ks' := by
    refine ⟨by rw [e_te]; change ks.trl_end.toNat + 1 ≤ ks.nv.toNat; omega,
      by rw [e_te]; change ks.prop.toNat ≤ ks.trl_end.toNat + 1; have := hinv.assign.prop_le; omega,
      by rw [e_un, e_te]; change (ks.unass.toNat - 1) + (ks.trl_end.toNat + 1) = ks.nv.toNat
         have := hinv.assign.unass_eq; omega,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro l hl; by_cases hv : l / 2 = lit.toNat / 2
      · rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;>
          rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩
        · rw [show l = lit.toNat by omega, hvals_lit]; exact Or.inr (Or.inl rfl)
        · rw [show l = lit.toNat ^^^ 1 by omega, hvals_nl]; exact Or.inr (Or.inr rfl)
        · rw [show l = lit.toNat ^^^ 1 by omega, hvals_nl]; exact Or.inr (Or.inr rfl)
        · rw [show l = lit.toNat by omega, hvals_lit]; exact Or.inr (Or.inl rfl)
      · rw [hvals_other l hv]; exact hinv.assign.vals_dom l hl
    · intro l hl; by_cases hv : l / 2 = lit.toNat / 2
      · rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;>
          rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩
        · rw [show l = lit.toNat by omega, hvals_lit, hvals_nl]; simp
        · rw [show l = lit.toNat ^^^ 1 by omega, k6_nat_xor1_xor1, hvals_nl, hvals_lit]; simp
        · rw [show l = lit.toNat ^^^ 1 by omega, k6_nat_xor1_xor1, hvals_nl, hvals_lit]; simp
        · rw [show l = lit.toNat by omega, hvals_lit, hvals_nl]; simp
      · have hvx : (l ^^^ 1) / 2 ≠ lit.toNat / 2 := by
          rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
        rw [hvals_other l hv, hvals_other (l ^^^ 1) hvx]; exact hinv.assign.vals_neg_iff l hl
    · intro l hl; constructor
      · intro hnz; by_cases hv : l / 2 = lit.toNat / 2
        · exact ⟨ks.trl_end.toNat, by rw [e_te]; omega,
            by rw [htrl_end_idx, Option.getD_some]; exact hv.symm⟩
        · rw [hvals_other l hv] at hnz
          obtain ⟨i, hi, hiv⟩ := (hinv.assign.vals_nz_iff_trl l hl).mp hnz
          exact ⟨i, by rw [e_te]; omega, by rw [htrl_lt_idx i hi]; exact hiv⟩
      · rintro ⟨i, hi, hiv⟩; rw [e_te] at hi
        by_cases hie : i = ks.trl_end.toNat
        · subst hie; rw [htrl_end_idx, Option.getD_some] at hiv
          rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;>
            rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩
          · rw [show l = lit.toNat by omega, hvals_lit]; decide
          · rw [show l = lit.toNat ^^^ 1 by omega, hvals_nl]; decide
          · rw [show l = lit.toNat ^^^ 1 by omega, hvals_nl]; decide
          · rw [show l = lit.toNat by omega, hvals_lit]; decide
        · have hi' : i < ks.trl_end.toNat := by omega
          rw [htrl_lt_idx i hi'] at hiv
          have hv : l / 2 ≠ lit.toNat / 2 := by rw [← hiv]; exact hnot_trl i hi'
          rw [hvals_other l hv]; exact (hinv.assign.vals_nz_iff_trl l hl).mpr ⟨i, hi', hiv⟩
    · unfold k6TrailLits; rw [htrl_take, List.map_append, List.map_append, List.nodup_append]
      refine ⟨hinv.assign.trl_nodup, by simp, fun x hx y hy heq => ?_⟩
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy; subst hy; subst heq
      rw [List.mem_map] at hx; obtain ⟨l0, hl0, hlv⟩ := hx
      rw [List.mem_map] at hl0; obtain ⟨b, hb, rfl⟩ := hl0
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
      have hi' : i < ks.trl_end.toNat := by simp [List.length_take] at hi; omega
      simp only [List.getElem_take] at hlv
      exact hnot_trl i hi'
        (by rw [List.getElem?_eq_getElem (by rw [hinv.shapes.trl_len]; omega), Option.getD_some]
            exact hlv)
    · intro l hl; unfold k6TrailLits at hl; rw [htrl_take, List.map_append, List.mem_append] at hl
      rcases hl with hl | hl
      · exact hinv.assign.trl_lt l hl
      · simp at hl; subst hl; exact hlit
    · intro v hv; by_cases hvv : v = lit.toNat / 2
      · subst hvv; rw [hlvl_v, Option.getD_some]; exact Nat.le_refl _
      · rw [hlvl_other v hvv]; exact hinv.assign.trl_lvl_le v hv
    · intro v hv hz
      have hne : v ≠ lit.toNat / 2 := fun h => by
        subst h; rcases k6_nat_xor1_cases lit.toNat with ⟨he, _⟩ | ⟨_, hx⟩
        · rw [← he, hvals_lit] at hz; cases hz
        · rw [← hx, hvals_nl] at hz; cases hz
      rw [hvals_other (2 * v) (by omega)] at hz
      rw [hlvl_other v hne, hrsn_other v hne]; exact hinv.assign.unass_lvl_zero v hv hz
    · intro i j hij hj; rw [e_te] at hj
      by_cases hje : j = ks.trl_end.toNat
      · subst hje; rw [htrl_end_idx, Option.getD_some, hlvl_v, Option.getD_some]
        by_cases hie : i = ks.trl_end.toNat
        · subst hie; rw [htrl_end_idx, Option.getD_some, hlvl_v, Option.getD_some]
          exact Nat.le_refl _
        · have hi' : i < ks.trl_end.toNat := by omega
          rw [htrl_lt_idx i hi', hlvl_other _ (hnot_trl i hi')]
          have hli := hinv.assign.trl_lt _
            (k6_mem_trailLits_of_lt hi' (by rw [hinv.shapes.trl_len]; omega))
          exact hinv.assign.trl_lvl_le _ (by omega)
      · have hj' : j < ks.trl_end.toNat := by omega
        have hi' : i < ks.trl_end.toNat := by omega
        rw [htrl_lt_idx i hi', htrl_lt_idx j hj', hlvl_other _ (hnot_trl i hi'),
          hlvl_other _ (hnot_trl j hj')]
        exact hinv.assign.trl_lvl_mono i j hij hj'
    · intro i j hji hi hpos hlvl_eq; rw [e_te] at hi
      by_cases hie : i = ks.trl_end.toNat
      · subst hie
        have hj' : j < ks.trl_end.toNat := by omega
        rw [htrl_end_idx, Option.getD_some, hlvl_v, Option.getD_some] at hpos hlvl_eq
        rw [htrl_lt_idx j hj', hlvl_other _ (hnot_trl j hj')] at hlvl_eq
        rw [htrl_end_idx, Option.getD_some, hrsn_v, Option.getD_some]
        intro hrs_eq; exact hdec hpos hrs_eq j hj' hlvl_eq
      · have hi' : i < ks.trl_end.toNat := by omega
        have hj' : j < ks.trl_end.toNat := by omega
        rw [htrl_lt_idx i hi', hlvl_other _ (hnot_trl i hi')] at hpos hlvl_eq
        rw [htrl_lt_idx j hj', hlvl_other _ (hnot_trl j hj')] at hlvl_eq
        rw [htrl_lt_idx i hi', hrsn_other _ (hnot_trl i hi')]
        exact hinv.assign.dec_earliest i j hji hi' hpos hlvl_eq
    · intro i hi; dsimp only; intro hl0; rw [e_te] at hi
      by_cases hie : i = ks.trl_end.toNat
      · subst hie
        rw [htrl_end_idx, Option.getD_some, hlvl_v, Option.getD_some] at hl0
        rw [htrl_end_idx, Option.getD_some]; exact ⟨hvals_lit, hvals_nl, hlvl0 hl0⟩
      · have hi' : i < ks.trl_end.toNat := by omega
        let l := (ks.trl[i]?.getD 0#32).toNat
        have hne_v := hnot_trl i hi'
        have hne_vx : (l ^^^ 1) / 2 ≠ lit.toNat / 2 := by
          rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
        rw [htrl_lt_idx i hi'] at hl0 ⊢
        change ks'.lvlArr[l / 2]?.getD 0#32 = 0#32 at hl0
        rw [hlvl_other (l / 2) hne_v] at hl0
        change ks'.vals[l]? = some 1#32 ∧ ks'.vals[l ^^^ 1]? = some 2#32 ∧ SemEntails P [l]
        rw [hvals_other l hne_v, hvals_other (l ^^^ 1) hne_vx]; exact hinv.assign.lvl0_ok i hi' hl0
  have hre' : K6ReasonOk ks' := fun i hi => by
    rw [e_te] at hi
    by_cases hie : i = ks.trl_end.toNat
    · subst hie
      change let l := (ks'.trl[ks.trl_end.toNat]?.getD 0#32).toNat
             let r := ks'.rsn[l / 2]?.getD 0#32; _
      rw [htrl_end_idx, Option.getD_some, hrsn_v, Option.getD_some]
      rcases hrsn_ok with rfl | ⟨hr_lt, hmem, hoth⟩
      · exact Or.inl rfl
      · right; refine ⟨hr_lt, hmem, fun x hx hne => ?_⟩
        obtain ⟨j, hj, hje⟩ := hoth x hx hne
        exact ⟨j, hj, by rw [htrl_lt_idx j hj]; exact hje⟩
    · have hi' : i < ks.trl_end.toNat := by omega
      change let l := (ks'.trl[i]?.getD 0#32).toNat; let r := ks'.rsn[l / 2]?.getD 0#32; _
      rw [htrl_lt_idx i hi', hrsn_other _ (hnot_trl i hi')]
      rcases hinv.reasons i hi' with hnone | ⟨hr_lt, hmem, hoth⟩
      · exact Or.inl hnone
      · right; refine ⟨hr_lt, hmem, fun x hx hne => ?_⟩
        obtain ⟨j, hj, hje⟩ := hoth x hx hne
        exact ⟨j, by omega, by rw [htrl_lt_idx j (by omega)]; exact hje⟩
  exact ⟨⟨hsh', hcl', hinv.watches, hba', hre'⟩, hsync'⟩

theorem k6SetIncons_preserves_inv {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hunsat : ∀ β, ¬ P β) :
    K6Inv L P (ks.putHdr .incons 1#32) := by
  dsimp only [K6State.putHdr]
  exact
    { shapes := hinv.shapes.putHdr .incons 1#32
      clauses := { hinv.clauses with incons_ok := fun _ => hunsat }
      watches := hinv.watches
      assign := ⟨hinv.assign.trl_end_le, hinv.assign.prop_le, hinv.assign.unass_eq,
        hinv.assign.vals_dom, hinv.assign.vals_neg_iff, hinv.assign.vals_nz_iff_trl,
        hinv.assign.trl_nodup, hinv.assign.trl_lt, hinv.assign.trl_lvl_le,
        hinv.assign.unass_lvl_zero, hinv.assign.trl_lvl_mono, hinv.assign.dec_earliest,
        hinv.assign.lvl0_ok⟩
      reasons := hinv.reasons }

theorem k6LitsBounded_mono {M1 M2 : Nat} {ks : K6State} (hle : M1 ≤ M2) (h : K6LitsBounded M1 ks) :
    K6LitsBounded M2 ks :=
  ⟨fun cid hc l hl => Nat.lt_of_lt_of_le (h.1 cid hc l hl) (by omega),
   fun w hw => Nat.lt_of_lt_of_le (h.2 w hw) (by omega)⟩

end LeanQbe.T.Examples.Kissat.Proof.Kitten

end
