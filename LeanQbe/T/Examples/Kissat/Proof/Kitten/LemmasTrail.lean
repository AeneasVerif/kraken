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
membership and refutation helpers, and `k6AssignStep_preserves_inv` / `k6SetIncons_preserves_inv`.

Zero legacy `Full*` imports; zero `@[expose]` on theorems/lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Kitten

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.C0Grind
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec

open K6MemATactics K6PtrTactics
open scoped K6MemATactics K6PtrTactics

/-! ## 1. Model-Set Monotonicity & Invariant Field-Cast Helpers -/

theorem K6Inv.mono_P {L : K6Layout} {P P' : (Nat → Bool) → Prop} {ks : K6State}
    (himp : ∀ β, P' β → P β) (h : K6Inv L P ks) : K6Inv L P' ks :=
  { shapes := h.shapes, watches := h.watches, reasons := h.reasons
    clauses := { h.clauses with
      cl_wf := fun cid hc => let w := h.clauses.cl_wf cid hc
        ⟨w.1, w.2.1, w.2.2.1, fun β hβ => w.2.2.2 β (himp β hβ)⟩
      incons_ok := fun hi β hβ => h.clauses.incons_ok hi β (himp β hβ) }
    assign := { h.assign with
      lvl0_ok := fun i hi hl0 => let w := h.assign.lvl0_ok i hi hl0
        ⟨w.1, w.2.1, fun β hβ => w.2.2 β (himp β hβ)⟩ } }

theorem K6ScratchInv.mono_P {P P' : (Nat → Bool) → Prop} {scr : List (BitVec 32)}
    (himp : ∀ β, P' β → P β) (h : K6ScratchInv P scr) : K6ScratchInv P' scr :=
  ⟨h.1, h.2.1, h.2.2.mono_P himp⟩

theorem k6TrailSynced_cast {ks ks' : K6State} (hs : K6TrailSynced ks)
    (h_te : ks'.trl_end = ks.trl_end := by
      first | rfl | (try simp only [k6WatchStep, k6WatchStep0]; k6_field))
    (h_tr : ks'.trl = ks.trl := by
      first | rfl | (try simp only [k6WatchStep, k6WatchStep0]; k6_field))
    (h_va : ks'.vals = ks.vals := by
      first | rfl | (try simp only [k6WatchStep, k6WatchStep0]; k6_field)) :
    K6TrailSynced ks' := fun i hi => by dsimp only; rw [h_tr, h_va]; exact hs i (h_te ▸ hi)

theorem k6ClausesOk_cast {L : K6Layout} {P : (Nat → Bool) → Prop} {ks ks' : K6State}
    (hc : K6ClausesOk L P ks)
    (h1 : ks'.acap = ks.acap := by first | rfl | k6_field)
    (h2 : ks'.max_v = ks.max_v := by first | rfl | k6_field)
    (h3 : ks'.max_orig = ks.max_orig := by first | rfl | k6_field)
    (h4 : ks'.max_cl = ks.max_cl := by first | rfl | k6_field)
    (h5 : ks'.nv = ks.nv := by first | rfl | k6_field)
    (h6 : ks'.nc = ks.nc := by first | rfl | k6_field)
    (h7 : ks'.alen = ks.alen := by first | rfl | k6_field)
    (h8 : ks'.nassump = ks.nassump := by first | rfl | k6_field)
    (h9 : ks'.incons = ks.incons ∨ (ks'.incons ≠ 0#32 → ∀ β, ¬ P β) := by
      left; first | rfl | k6_field)
    (h10 : ks'.assump = ks.assump := by first | rfl | k6_field)
    (h11 : ks'.clOff = ks.clOff := by first | rfl | k6_field)
    (h12 : ks'.clSz = ks.clSz := by first | rfl | k6_field)
    (h13 : ks'.arena = ks.arena := by first | rfl | k6_field)
    (h_nkl : ks'.nkl = ks.nkl ∨ ks'.nkl.toNat ≤ L.maxV := by left; first | rfl | k6_field)
    (h_nana : ks'.nana = ks.nana ∨ ks'.nana.toNat ≤ L.maxV := by left; first | rfl | k6_field)
    (h_fl : ks'.flags = ks.flags ∨
      (∀ v < ks'.nv.toNat, (ks'.flags[v]?.getD 0#32 &&& 2#32) = 0#32) := by
      left; first | rfl | k6_field) :
    K6ClausesOk L P ks' :=
  ⟨h1.trans hc.acap_eq, h2.trans hc.max_v_eq, h3.trans hc.max_orig_eq, h4.trans hc.max_cl_eq,
   h5 ▸ hc.nv_le, h6 ▸ hc.nc_le, h7 ▸ hc.alen_le, h8 ▸ hc.nassump_le,
   h_nkl.elim (fun h => h ▸ hc.nkl_le) id, h_nana.elim (fun h => h ▸ hc.nana_le) id,
   fun cid hcid => by
     rw [h6] at hcid; simp only [k6ClauseSize, k6ClauseOff, k6ClauseLits, h11, h12, h13, h7, h5]
     exact hc.cl_wf cid hcid,
   fun c1 c2 hlt hcid => by
     rw [h6] at hcid; simp only [k6ClauseSize, k6ClauseOff, h11, h12]
     exact hc.cl_mono c1 c2 hlt hcid,
   h9.elim (fun h => h ▸ hc.incons_ok) id,
   fun i hi => by rw [h8] at hi; rw [h10, h5]; exact hc.assump_ok i hi,
   h_fl.elim (fun h v hv => by rw [h5] at hv; rw [h]; exact hc.flags_clean v hv) id⟩

theorem k6BaseAssignOk_cast {P : (Nat → Bool) → Prop} {ks ks' : K6State}
    (ha : K6BaseAssignOk P ks)
    (h1 : ks'.nv = ks.nv := by first | rfl | (try simp only [k6WatchStep, k6WatchStep0]; k6_field))
    (h2 : ks'.trl_end = ks.trl_end := by
      first | rfl | (try simp only [k6WatchStep, k6WatchStep0]; k6_field))
    (h3 : ks'.prop = ks.prop := by
      first | rfl | (try simp only [k6WatchStep, k6WatchStep0]; k6_field))
    (h4 : ks'.unass = ks.unass := by
      first | rfl | (try simp only [k6WatchStep, k6WatchStep0]; k6_field))
    (h5 : ks'.vals = ks.vals := by
      first | rfl | (try simp only [k6WatchStep, k6WatchStep0]; k6_field))
    (h6 : ks'.trl = ks.trl := by
      first | rfl | (try simp only [k6WatchStep, k6WatchStep0]; k6_field))
    (h7 : ks'.lvl = ks.lvl := by
      first | rfl | (try simp only [k6WatchStep, k6WatchStep0]; k6_field))
    (h8 : ks'.lvlArr = ks.lvlArr := by
      first | rfl | (try simp only [k6WatchStep, k6WatchStep0]; k6_field))
    (h9 : ks'.rsn = ks.rsn := by
      first | rfl | (try simp only [k6WatchStep, k6WatchStep0]; k6_field)) :
    K6BaseAssignOk P ks' :=
  ⟨by rw [h2, h1]; exact ha.trl_end_le, by rw [h3, h2]; exact ha.prop_le,
   by rw [h4, h2, h1]; exact ha.unass_eq,
   fun l hl => by rw [h1] at hl; rw [h5]; exact ha.vals_dom l hl,
   fun l hl => by rw [h1] at hl; rw [h5]; exact ha.vals_neg_iff l hl,
   fun l hl => by rw [h1] at hl; rw [h5, h2, h6]; exact ha.vals_nz_iff_trl l hl,
   by unfold k6TrailLits; rw [h6, h2]; exact ha.trl_nodup,
   fun l hl => by unfold k6TrailLits at hl; rw [h6, h2] at hl; rw [h1]; exact ha.trl_lt l hl,
   fun v hv => by rw [h1] at hv; rw [h8, h7]; exact ha.trl_lvl_le v hv,
   fun v hv hz => by rw [h1] at hv; rw [h5] at hz; rw [h8, h9]; exact ha.unass_lvl_zero v hv hz,
   fun i j hij hj => by rw [h2] at hj; rw [h8, h6]; exact ha.trl_lvl_mono i j hij hj,
   fun i j hji hi hp heq => by
     rw [h2] at hi; rw [h8, h6] at hp heq; rw [h9, h6]; exact ha.dec_earliest i j hji hi hp heq,
   fun i hi => by rw [h2] at hi; dsimp only; rw [h6, h8, h5]; exact ha.lvl0_ok i hi⟩

theorem k6Inv_cast {L : K6Layout} {P : (Nat → Bool) → Prop} {ks ks' : K6State}
    (hinv : K6Inv L P ks) (hsh : ks'.ShapesOk L)
    (h1 : ks'.acap = ks.acap := by first | rfl | k6_field)
    (h2 : ks'.max_v = ks.max_v := by first | rfl | k6_field)
    (h3 : ks'.max_orig = ks.max_orig := by first | rfl | k6_field)
    (h4 : ks'.max_cl = ks.max_cl := by first | rfl | k6_field)
    (h5 : ks'.nv = ks.nv := by first | rfl | k6_field)
    (h6 : ks'.nc = ks.nc := by first | rfl | k6_field)
    (h7 : ks'.alen = ks.alen := by first | rfl | k6_field)
    (h8 : ks'.nassump = ks.nassump := by first | rfl | k6_field)
    (h9 : ks'.incons = ks.incons ∨ (ks'.incons ≠ 0#32 → ∀ β, ¬ P β) := by
      left; first | rfl | k6_field)
    (h10 : ks'.lvl = ks.lvl := by first | rfl | k6_field)
    (h11 : ks'.prop = ks.prop := by first | rfl | k6_field)
    (h12 : ks'.trl_end = ks.trl_end := by first | rfl | k6_field)
    (h13 : ks'.unass = ks.unass := by first | rfl | k6_field)
    (h14 : ks'.lvlArr = ks.lvlArr := by first | rfl | k6_field)
    (h15 : ks'.rsn = ks.rsn := by first | rfl | k6_field)
    (h16 : ks'.trl = ks.trl := by first | rfl | k6_field)
    (h17 : ks'.assump = ks.assump := by first | rfl | k6_field)
    (h18 : ks'.vals = ks.vals := by first | rfl | k6_field)
    (h19 : ks'.whead = ks.whead := by first | rfl | k6_field)
    (h20 : ks'.wnext = ks.wnext := by first | rfl | k6_field)
    (h21 : ks'.wblit = ks.wblit := by first | rfl | k6_field)
    (h22 : ks'.clOff = ks.clOff := by first | rfl | k6_field)
    (h23 : ks'.clSz = ks.clSz := by first | rfl | k6_field)
    (h24 : ks'.arena = ks.arena := by first | rfl | k6_field)
    (h_nkl : ks'.nkl = ks.nkl ∨ ks'.nkl.toNat ≤ L.maxV := by left; first | rfl | k6_field)
    (h_nana : ks'.nana = ks.nana ∨ ks'.nana.toNat ≤ L.maxV := by left; first | rfl | k6_field)
    (h_fl : ks'.flags = ks.flags ∨
      (∀ v < ks'.nv.toNat, (ks'.flags[v]?.getD 0#32 &&& 2#32) = 0#32) := by
      left; first | rfl | k6_field) :
    K6Inv L P ks' := by
  refine ⟨hsh, k6ClausesOk_cast hinv.clauses h1 h2 h3 h4 h5 h6 h7 h8 h9 h17 h22 h23 h24
    h_nkl h_nana h_fl, ?_, k6BaseAssignOk_cast hinv.assign h5 h12 h11 h13 h18 h16 h10 h14 h15, ?_⟩
  · obtain ⟨ch, hch1, hch2, hch3, hch4⟩ := hinv.watches
    refine ⟨ch, h5 ▸ hch1, hch2, fun l hl => by rw [h5] at hl; rw [h20, h19]; exact hch3 l hl,
      fun l hl w hw => by
        rw [h5] at hl
        simp only [k6ClauseSize, k6ClauseOff, k6ClauseLits, h5, h6, h22, h23, h24, h21]
        exact hch4 l hl w hw⟩
  · intro i hi; rw [h12] at hi
    simpa only [h16, h15, h6, k6ClauseLits, k6ClauseOff, k6ClauseSize, h22, h23, h24] using
      hinv.reasons i hi

theorem k6AddTicks_preserves_inv {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (tk' : BitVec 32) : K6Inv L P (ks.putHdr .ticks tk') :=
  k6Inv_cast hinv (hinv.shapes.putHdr .ticks tk')

theorem k6SetStatus_preserves_inv {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (st' : BitVec 32) : K6Inv L P (ks.putHdr .status st') :=
  k6Inv_cast hinv (hinv.shapes.putHdr .status st')

/-! ## 2. Trail, Clause-Literal, & Refutation Helpers -/

theorem k6_mem_clauseLits_iff {ks : K6State} {cid : Nat}
    (hbd : k6ClauseOff ks cid + k6ClauseSize ks cid ≤ ks.arena.length) {l : Nat} :
    l ∈ k6ClauseLits ks cid ↔
      ∃ n < k6ClauseSize ks cid, (ks.arena[k6ClauseOff ks cid + n]?.getD 0#32).toNat = l := by
  unfold k6ClauseLits; rw [List.mem_map]; constructor
  · rintro ⟨b, hb, rfl⟩; obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hb
    have hns : n < k6ClauseSize ks cid := by simp [List.length_take] at hn; omega
    exact ⟨n, hns, by simp [List.getElem_take, List.getElem_drop,
      List.getElem?_eq_getElem (by omega : k6ClauseOff ks cid + n < ks.arena.length)]⟩
  · rintro ⟨n, hn, rfl⟩
    have hlt : k6ClauseOff ks cid + n < ks.arena.length := by omega
    refine ⟨ks.arena[k6ClauseOff ks cid + n]'hlt, List.mem_iff_getElem.mpr ⟨n,
      by simp [List.length_take, List.length_drop]; omega, by
        simp [List.getElem_take, List.getElem_drop]⟩,
      by simp [List.getElem?_eq_getElem hlt]⟩

theorem k6_mem_trailLits_of_lt {ks : K6State} {i : Nat}
    (hi : i < ks.trl_end.toNat) (hle : ks.trl_end.toNat ≤ ks.trl.length) :
    (ks.trl[i]?.getD 0#32).toNat ∈ k6TrailLits ks := by
  unfold k6TrailLits; rw [List.mem_map]
  exact ⟨ks.trl[i]'(by omega), List.mem_iff_getElem.mpr ⟨i, by simp [List.length_take]; omega,
    by simp⟩,
    by simp [List.getElem?_eq_getElem (by omega : i < ks.trl.length)]⟩

theorem k6_trailSynced_of_lvl0 {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hl0 : ks.lvl = 0#32) : K6TrailSynced ks := fun i hi => by
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; have := hinv.clauses.nv_le; omega
  have hl_lt := hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hi htrl_len)
  have hle := hinv.assign.trl_lvl_le ((ks.trl[i]?.getD 0#32).toNat / 2) (by omega)
  rw [hl0] at hle
  have ok := hinv.assign.lvl0_ok i hi (BitVec.eq_of_toNat_eq (Nat.eq_zero_of_le_zero hle))
  exact ⟨ok.1, ok.2.1⟩

theorem k6_mem_trailDecisions_iff {ks : K6State} {d : Nat}
    (hle : ks.trl_end.toNat ≤ ks.trl.length) :
    d ∈ k6TrailDecisions ks ↔
      ∃ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat = d ∧
        0 < (ks.lvlArr[d / 2]?.getD 0#32).toNat ∧ ks.rsn[d / 2]?.getD 0#32 = 0xFFFFFFFF#32 := by
  unfold k6TrailDecisions; rw [List.mem_filterMap]; constructor
  · rintro ⟨l, hl, hif⟩; obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
    have hlt : i < ks.trl_end.toNat := by simp at hi; omega
    simp only [List.getElem_take] at hif; split at hif
    · rename_i hc; simp only [Option.some.injEq] at hif
      refine ⟨i, hlt, ?_, hif ▸ hc.1, hif ▸ hc.2⟩
      rw [List.getElem?_eq_getElem (by omega : i < ks.trl.length), Option.getD_some]; exact hif
    · simp at hif
  · rintro ⟨i, hi, hteq, hpos, hrs⟩
    have h1 : i < ks.trl.length := by omega
    refine ⟨ks.trl[i], List.mem_iff_getElem.mpr ⟨i, by simp [List.length_take]; omega, by simp⟩, ?_⟩
    rw [List.getElem?_eq_getElem h1, Option.getD_some] at hteq; rw [hteq]; simp [hpos, hrs]

theorem k6_trl_nodup_var_ne {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hsh : ks.ShapesOk L) (hnv : ks.nv.toNat ≤ L.maxV) (hba : K6BaseAssignOk P ks)
    {i j : Nat} (hi : i < ks.trl_end.toNat) (hj : j < ks.trl_end.toNat) (hne : i ≠ j) :
    (ks.trl[i]?.getD 0#32).toNat / 2 ≠ (ks.trl[j]?.getD 0#32).toNat / 2 := by
  have hte := hba.trl_end_le
  have hlen : ks.trl_end.toNat ≤ ks.trl.length := by rw [hsh.trl_len]; omega
  have hnd := hba.trl_nodup; unfold k6TrailLits at hnd; rw [List.map_map] at hnd
  have hm_len : (List.map ((fun x => x / 2) ∘ BitVec.toNat)
      (ks.trl.take ks.trl_end.toNat)).length = ks.trl_end.toNat := by simp [List.length_take]; omega
  intro heq
  exact hne (k6_list_nodup_getElem_inj hnd (by omega) (by omega) (by
    simp only [List.getElem_map, List.getElem_take, Function.comp_def]
    rw [List.getElem?_eq_getElem (by omega : i < ks.trl.length),
      List.getElem?_eq_getElem (by omega : j < ks.trl.length), Option.getD_some,
      Option.getD_some] at heq; exact heq))

theorem k6_trl_end_lt_of_unassigned {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hsh : ks.ShapesOk L) (hnv : ks.nv.toNat ≤ L.maxV) (hba : K6BaseAssignOk P ks)
    {l : Nat} (hl : l < 2 * ks.nv.toNat) (h0 : ks.vals[l]?.getD 0#32 = 0#32) :
    ks.trl_end.toNat < ks.nv.toNat := by
  have hle := hba.trl_end_le
  by_cases hlt : ks.trl_end.toNat < ks.nv.toNat
  · exact hlt
  · exfalso; have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by rw [hsh.trl_len]; omega
    have hv_mem := k6_nodup_mem_of_length_ge (n := ks.nv.toNat) hba.trl_nodup (fun x hx => by
      rw [List.mem_map] at hx; obtain ⟨t, ht, rfl⟩ := hx; have := hba.trl_lt t ht; omega)
      (by simp [k6TrailLits, List.length_take]; omega) (v := l / 2) (by omega)
    rw [List.mem_map] at hv_mem; obtain ⟨t, ht, htv⟩ := hv_mem
    unfold k6TrailLits at ht; rw [List.mem_map] at ht; obtain ⟨bv, hbv, rfl⟩ := ht
    obtain ⟨i, hi, heq_bv⟩ := List.getElem_of_mem hbv
    have hi_te : i < ks.trl_end.toNat := by simp [List.length_take] at hi; omega
    simp only [List.getElem_take] at heq_bv
    exact (hba.vals_nz_iff_trl l hl).mpr ⟨i, hi_te, by
      rw [List.getElem?_eq_getElem (by omega : i < ks.trl.length), Option.getD_some, heq_bv]
      exact htv⟩ h0

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
  rcases (litVar_eq_iff (ks.trl[i]?.getD 0#32).toNat l).mp (by simpa [litVar] using hveq) with
      h | h
  · change ks.vals[(ks.trl[i]?.getD 0#32).toNat]? = some 1#32 ∧ _ at hs
    rw [h, hfals] at hs; cases hs.1
  · exact ⟨i, hi, h⟩

theorem k6_falsified_lvl0_entails {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hlvl0 : ks.lvl = 0#32) {l : Nat} (hl : l < 2 * ks.nv.toNat)
    (hfals : ks.vals[l]? = some 2#32) :
    (∃ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat = l ^^^ 1) ∧ SemEntails P [l ^^^ 1] := by
  obtain ⟨i, hi, hveq⟩ := (hinv.assign.vals_nz_iff_trl l hl).mp (by simp [hfals])
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; have := hinv.clauses.nv_le; omega
  have htl_lt := hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hi htrl_len)
  have hle := hinv.assign.trl_lvl_le ((ks.trl[i]?.getD 0#32).toNat / 2) (by omega)
  rw [hlvl0] at hle
  have hok := hinv.assign.lvl0_ok i hi (BitVec.eq_of_toNat_eq (Nat.eq_zero_of_le_zero hle))
  rcases (litVar_eq_iff (ks.trl[i]?.getD 0#32).toNat l).mp (by simpa [litVar] using hveq) with
      h | h
  · rw [h, hfals] at hok; cases hok.1
  · rw [show litNeg l = l ^^^ 1 from rfl] at h; exact ⟨⟨i, hi, h⟩, h ▸ hok.2.2⟩

theorem k6_conflict_unsat_lvl0 {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hlvl0 : ks.lvl = 0#32) {cid : Nat} (hcid : cid < ks.nc.toNat)
    (hfals : ∀ l ∈ k6ClauseLits ks cid, ks.vals[l]? = some 2#32) : ∀ β, ¬ P β := fun β hβ => by
  obtain ⟨l, hl, hs⟩ := (clause_sat_cnfClause_iff β _).mp ((hinv.clauses.cl_wf cid hcid).2.2.2 β hβ)
  have hneg := (k6_falsified_lvl0_entails hinv hlvl0
    ((hinv.clauses.cl_wf cid hcid).2.2.1 l hl) (hfals l hl)).2 β hβ
  exact absurd ((sat_cnfClause_singleton β l).mpr hs) ((sat_cnfClause_litNeg_iff β l).mp hneg)

theorem k6_trail_entails_assumps {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hdec : ∀ d ∈ k6TrailDecisions ks, d ∈ k6AssumpLits ks)
    {β : Nat → Bool} (hP : P β) (hA : (unitsCnf (k6AssumpLits ks)).Sat β) :
    ∀ i < ks.trl_end.toNat, (cnfClause [(ks.trl[i]?.getD 0#32).toNat]).Sat β := by
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; have := hinv.clauses.nv_le; omega
  intro i; induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hi; let l := (ks.trl[i]?.getD 0#32).toNat
    rcases hinv.reasons i hi with hrsn | ⟨hr_lt, _, hoth⟩
    · by_cases hl0 : ks.lvlArr[l / 2]?.getD 0#32 = 0#32
      · exact (hinv.assign.lvl0_ok i hi hl0).2.2 β hP
      · have hpos : 0 < (ks.lvlArr[l / 2]?.getD 0#32).toNat :=
          Nat.pos_of_ne_zero fun hz => hl0 (BitVec.eq_of_toNat_eq hz)
        have hl_lt := hinv.assign.trl_lt l (k6_mem_trailLits_of_lt hi htrl_len)
        have hrl : l / 2 < ks.rsn.length := by
          rw [hinv.shapes.rsn_len]; have := hinv.clauses.nv_le; omega
        have hrsn' : ks.rsn[l / 2]?.getD 0#32 = 0xFFFFFFFF#32 := by
          rw [List.getElem?_eq_getElem hrl, Option.getD_some] at hrsn ⊢; exact hrsn
        exact (sat_unitsCnf_iff β (k6AssumpLits ks)).mp hA l
          (hdec l ((k6_mem_trailDecisions_iff htrl_len).mpr ⟨i, hi, rfl, hpos, hrsn'⟩))
    · obtain ⟨x, hx_mem, hxs⟩ := (clause_sat_cnfClause_iff β _).mp
        ((hinv.clauses.cl_wf _ hr_lt).2.2.2 β hP)
      by_cases hxl : x = l
      · rw [hxl] at hxs; exact (sat_cnfClause_singleton β l).mpr hxs
      · obtain ⟨j, hj_lt, hj_eq⟩ := hoth x hx_mem hxl
        have hjs := ih j hj_lt (Nat.lt_trans hj_lt hi); rw [hj_eq] at hjs
        exact absurd ((sat_cnfClause_singleton β x).mpr hxs) ((sat_cnfClause_litNeg_iff β x).mp hjs)

theorem k6_conflict_unsat_assumps {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks)
    (hdec : ∀ d ∈ k6TrailDecisions ks, d ∈ k6AssumpLits ks)
    {cid : Nat} (hcid : cid < ks.nc.toNat)
    (hfals : ∀ l ∈ k6ClauseLits ks cid, ks.vals[l]? = some 2#32) :
    ∀ β, P β → ¬ (unitsCnf (k6AssumpLits ks)).Sat β := fun β hP hA => by
  obtain ⟨l, hl_mem, hls⟩ :=
    (clause_sat_cnfClause_iff β _).mp ((hinv.clauses.cl_wf cid hcid).2.2.2 β hP)
  obtain ⟨i, hi, hieq⟩ := k6_falsified_to_trail hinv.assign hsync
    ((hinv.clauses.cl_wf cid hcid).2.2.1 l hl_mem) (hfals l hl_mem)
  have hts := k6_trail_entails_assumps hinv hdec hP hA i hi; rw [hieq] at hts
  exact (sat_cnfClause_litNeg_iff β l).mp hts ((sat_cnfClause_singleton β l).mpr hls)

theorem k6_falsified_assump_unsat {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks)
    (hdec : ∀ d ∈ k6TrailDecisions ks, d ∈ k6AssumpLits ks)
    {i : Nat} (hi : i < ks.nassump.toNat)
    (hfals : ks.vals[(ks.assump[i]?.getD 0#32).toNat]? = some 2#32) :
    ∀ β, P β → ¬ (unitsCnf (k6AssumpLits ks)).Sat β := fun β hP hA => by
  let a := (ks.assump[i]?.getD 0#32).toNat
  have hlen : ks.nassump.toNat ≤ ks.assump.length := by
    rw [hinv.shapes.assump_len]; exact hinv.clauses.nassump_le
  have ha_mem : a ∈ k6AssumpLits ks := by
    unfold k6AssumpLits; rw [List.mem_map]
    exact ⟨ks.assump[i]?.getD 0#32, List.mem_iff_getElem.mpr ⟨i, by simp [List.length_take]; omega,
      by simp [List.getElem?_eq_getElem (by omega : i < ks.assump.length)]⟩, rfl⟩
  obtain ⟨j, hj, hjeq⟩ :=
    k6_falsified_to_trail hinv.assign hsync (hinv.clauses.assump_ok i hi) hfals
  have hts := k6_trail_entails_assumps hinv hdec hP hA j hj; rw [hjeq] at hts
  exact (sat_cnfClause_litNeg_iff β a).mp hts
    ((sat_unitsCnf_iff β (k6AssumpLits ks)).mp hA a ha_mem)

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
  cases b <;> c0_bv_bit_grind

theorem k6_lit_var_cases {l m : Nat} (h : l / 2 = m / 2) :
    (l = m ∧ l ^^^ 1 = m ^^^ 1) ∨ (l = m ^^^ 1 ∧ l ^^^ 1 = m) := by
  rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases k6_nat_xor1_cases m with ⟨_, _⟩ | ⟨_, _⟩ <;>
    (first | exact Or.inl ⟨by omega, by omega⟩ | exact Or.inr ⟨by omega, by omega⟩)

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
  have hm := L.hmaxV; have hnv := hinv.clauses.nv_le; let ks' := k6AssignStep ks lit rsn
  have hsh' := k6AssignStep_preserves_shapes hinv.shapes lit rsn
  have hte_lt := k6_trl_end_lt_of_unassigned hinv.shapes hnv hinv.assign hlit (by simp [hun])
  have hun_pos : 0 < ks.unass.toNat := by have := hinv.assign.unass_eq; omega
  have e_te : ks'.trl_end.toNat = ks.trl_end.toNat + 1 := by
    dsimp only [ks', k6AssignStep]; bv_omega
  have e_un : ks'.unass.toNat = ks.unass.toNat - 1 := by
    dsimp only [ks', k6AssignStep]; simp only [hun_pos, ite_true]; bv_omega
  have hnl_eq : (lit ^^^ 1#32).toNat = lit.toNat ^^^ 1 := by simp
  have hv_eq : (lit >>> 1).toNat = lit.toNat / 2 := (k6_bv32_div2_lt hlit).1
  have hxor_l := k6_nat_xor1_cases lit.toNat
  have hne_nl : lit.toNat ≠ lit.toNat ^^^ 1 := by rcases hxor_l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  have hnot_trl : ∀ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 :=
    fun i hi heq => by
      have := (hinv.assign.vals_nz_iff_trl lit.toNat hlit).mpr ⟨i, hi, heq⟩; simp [hun] at this
  have hvals_lit : ks'.vals[lit.toNat]? = some 1#32 := by
    dsimp only [ks', k6AssignStep]
    rw [hnl_eq, List.getElem?_set_ne hne_nl.symm,
      List.getElem?_set_self (by rw [hinv.shapes.vals_len]; omega)]
  have hvals_nl : ks'.vals[lit.toNat ^^^ 1]? = some 2#32 := by
    dsimp only [ks', k6AssignStep]
    rw [hnl_eq, List.getElem?_set_self (by simp [hinv.shapes.vals_len]; omega)]
  have hvals_other : ∀ x, x / 2 ≠ lit.toNat / 2 → ks'.vals[x]? = ks.vals[x]? := fun x hne => by
    have hx2 : lit.toNat ^^^ 1 ≠ x := fun h =>
      hne (by rw [← h]; rcases hxor_l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    dsimp only [ks', k6AssignStep]
    rw [hnl_eq, List.getElem?_set_ne hx2, List.getElem?_set_ne (fun h => hne (by rw [← h]))]
  have htrl_lt_idx : ∀ i < ks.trl_end.toNat, ks'.trl[i]? = ks.trl[i]? := fun i hi =>
    List.getElem?_set_ne (by omega)
  have htrl_end_idx : ks'.trl[ks.trl_end.toNat]? = some lit :=
    List.getElem?_set_self (by rw [hinv.shapes.trl_len]; omega)
  have hvar_other : ∀ v, v ≠ lit.toNat / 2 →
      ks'.lvlArr[v]? = ks.lvlArr[v]? ∧ ks'.rsn[v]? = ks.rsn[v]? ∧
      ks'.flags[v]? = ks.flags[v]? := fun v hne => by
    dsimp only [ks', k6AssignStep]; rw [hv_eq]
    exact ⟨List.getElem?_set_ne hne.symm, List.getElem?_set_ne hne.symm,
      List.getElem?_set_ne hne.symm⟩
  have hlvl_v : ks'.lvlArr[lit.toNat / 2]? = some ks.lvl := by
    dsimp only [ks', k6AssignStep]; rw [hv_eq]
    exact List.getElem?_set_self (by rw [hinv.shapes.lvlArr_len]; omega)
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
          rw [hfl]; split
          · exact (k6_flags_bit1_preserved _ true).trans (hinv.clauses.flags_clean _ hv)
          · exact (k6_flags_bit1_preserved _ false).trans (hinv.clauses.flags_clean _ hv)
        · rw [(hvar_other v hvv).2.2]; exact hinv.clauses.flags_clean v hv }
  have hsync' : K6TrailSynced ks' := fun i hi => by
    rw [e_te] at hi; by_cases hie : i = ks.trl_end.toNat
    · subst hie
      change ks'.vals[(ks'.trl[ks.trl_end.toNat]?.getD 0#32).toNat]? = some 1#32 ∧
        ks'.vals[(ks'.trl[ks.trl_end.toNat]?.getD 0#32).toNat ^^^ 1]? = some 2#32
      rw [htrl_end_idx, Option.getD_some]; exact ⟨hvals_lit, hvals_nl⟩
    · have hi' : i < ks.trl_end.toNat := by omega
      let l := (ks.trl[i]?.getD 0#32).toNat
      have hne_vx : (l ^^^ 1) / 2 ≠ lit.toNat / 2 := by
        have := hnot_trl i hi'; rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
      change ks'.vals[(ks'.trl[i]?.getD 0#32).toNat]? = some 1#32 ∧
        ks'.vals[(ks'.trl[i]?.getD 0#32).toNat ^^^ 1]? = some 2#32
      rw [htrl_lt_idx i hi']; change ks'.vals[l]? = some 1#32 ∧ ks'.vals[l ^^^ 1]? = some 2#32
      rw [hvals_other l (hnot_trl i hi'), hvals_other (l ^^^ 1) hne_vx]; exact hsync i hi'
  have htrl_take : ks'.trl.take ks'.trl_end.toNat = ks.trl.take ks.trl_end.toNat ++ [lit] := by
    change (ks.trl.set ks.trl_end.toNat lit).take ks'.trl_end.toNat = _
    rw [e_te, List.take_add_one, List.take_set_of_le (Nat.le_refl _),
      List.getElem?_set_self (by rw [hinv.shapes.trl_len]; omega), Option.toList_some]
  have hba' : K6BaseAssignOk P ks' := by
    refine ⟨by change ks'.trl_end.toNat ≤ ks.nv.toNat; omega,
      by change ks.prop.toNat ≤ ks'.trl_end.toNat; have := hinv.assign.prop_le; omega,
      by change ks'.unass.toNat + ks'.trl_end.toNat = ks.nv.toNat
         have := hinv.assign.unass_eq; omega,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro l hl; by_cases hv : l / 2 = lit.toNat / 2
      · rcases k6_lit_var_cases hv with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · exact Or.inr (Or.inl (by simp [hvals_lit]))
        · exact Or.inr (Or.inr (by simp [hvals_nl]))
      · rw [hvals_other l hv]; exact hinv.assign.vals_dom l hl
    · intro l hl; by_cases hv : l / 2 = lit.toNat / 2
      · rcases k6_lit_var_cases hv with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> simp [hx, hvals_lit, hvals_nl]
      · have hvx : (l ^^^ 1) / 2 ≠ lit.toNat / 2 := by
          rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
        rw [hvals_other l hv, hvals_other (l ^^^ 1) hvx]; exact hinv.assign.vals_neg_iff l hl
    · intro l hl; constructor
      · intro hnz; by_cases hv : l / 2 = lit.toNat / 2
        · exact ⟨ks.trl_end.toNat, by omega, by rw [htrl_end_idx, Option.getD_some]; exact hv.symm⟩
        · rw [hvals_other l hv] at hnz
          obtain ⟨i, hi, hiv⟩ := (hinv.assign.vals_nz_iff_trl l hl).mp hnz
          exact ⟨i, by omega, by rw [htrl_lt_idx i hi]; exact hiv⟩
      · rintro ⟨i, hi, hiv⟩; rw [e_te] at hi; by_cases hie : i = ks.trl_end.toNat
        · subst hie; rw [htrl_end_idx, Option.getD_some] at hiv
          rcases k6_lit_var_cases hiv.symm with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [hvals_lit, hvals_nl]
        · have hi' : i < ks.trl_end.toNat := by omega
          rw [htrl_lt_idx i hi'] at hiv
          rw [hvals_other l (hiv ▸ hnot_trl i hi')]
          exact (hinv.assign.vals_nz_iff_trl l hl).mpr ⟨i, hi', hiv⟩
    · unfold k6TrailLits; rw [htrl_take, List.map_append, List.map_append, List.nodup_append]
      refine ⟨hinv.assign.trl_nodup, by simp, fun x hx y hy heq => ?_⟩
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy; subst hy; subst heq
      rw [List.mem_map] at hx; obtain ⟨l0, hl0, hlv⟩ := hx; rw [List.mem_map] at hl0
      obtain ⟨b, hb, rfl⟩ := hl0; obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
      have hi' : i < ks.trl_end.toNat := by simp [List.length_take] at hi; omega
      simp only [List.getElem_take] at hlv
      exact hnot_trl i hi' (by
        rw [List.getElem?_eq_getElem (by rw [hinv.shapes.trl_len]; omega), Option.getD_some]
        exact hlv)
    · intro l hl; unfold k6TrailLits at hl; rw [htrl_take, List.map_append, List.mem_append] at hl
      rcases hl with hl | hl
      · exact hinv.assign.trl_lt l hl
      · simp at hl; subst hl; exact hlit
    · intro v hv; by_cases hvv : v = lit.toNat / 2
      · subst hvv; rw [hlvl_v, Option.getD_some]; exact Nat.le_refl _
      · rw [(hvar_other v hvv).1]; exact hinv.assign.trl_lvl_le v hv
    · intro v hv hz
      have hne : v ≠ lit.toNat / 2 := fun h => by
        subst h; rcases hxor_l with ⟨he, _⟩ | ⟨_, hx⟩
        · rw [← he, hvals_lit] at hz; cases hz
        · rw [← hx, hvals_nl] at hz; cases hz
      rw [hvals_other (2 * v) (by omega)] at hz; rw [(hvar_other v hne).1, (hvar_other v hne).2.1]
      exact hinv.assign.unass_lvl_zero v hv hz
    · intro i j hij hj; rw [e_te] at hj; by_cases hje : j = ks.trl_end.toNat
      · subst hje; rw [htrl_end_idx, Option.getD_some, hlvl_v, Option.getD_some]
        by_cases hie : i = ks.trl_end.toNat
        · subst hie; rw [htrl_end_idx, Option.getD_some, hlvl_v, Option.getD_some]
          exact Nat.le_refl _
        · have hi' : i < ks.trl_end.toNat := by omega
          rw [htrl_lt_idx i hi', (hvar_other _ (hnot_trl i hi')).1]
          have hli := hinv.assign.trl_lt _
            (k6_mem_trailLits_of_lt hi' (by rw [hinv.shapes.trl_len]; omega))
          exact hinv.assign.trl_lvl_le _ (by omega)
      · have hj' : j < ks.trl_end.toNat := by omega
        have hi' : i < ks.trl_end.toNat := by omega
        rw [htrl_lt_idx i hi', htrl_lt_idx j hj', (hvar_other _ (hnot_trl i hi')).1,
          (hvar_other _ (hnot_trl j hj')).1]; exact hinv.assign.trl_lvl_mono i j hij hj'
    · intro i j hji hi hpos hlvl_eq; rw [e_te] at hi; by_cases hie : i = ks.trl_end.toNat
      · subst hie; have hj' : j < ks.trl_end.toNat := by omega
        rw [htrl_end_idx, Option.getD_some, hlvl_v, Option.getD_some] at hpos hlvl_eq
        rw [htrl_lt_idx j hj', (hvar_other _ (hnot_trl j hj')).1] at hlvl_eq
        rw [htrl_end_idx, Option.getD_some, hrsn_v, Option.getD_some]
        exact fun hrs_eq => hdec hpos hrs_eq j hj' hlvl_eq
      · have hi' : i < ks.trl_end.toNat := by omega
        have hj' : j < ks.trl_end.toNat := by omega
        rw [htrl_lt_idx i hi', (hvar_other _ (hnot_trl i hi')).1] at hpos hlvl_eq
        rw [htrl_lt_idx j hj', (hvar_other _ (hnot_trl j hj')).1] at hlvl_eq
        rw [htrl_lt_idx i hi', (hvar_other _ (hnot_trl i hi')).2.1]
        exact hinv.assign.dec_earliest i j hji hi' hpos hlvl_eq
    · intro i hi; dsimp only; intro hl0; rw [e_te] at hi; by_cases hie : i = ks.trl_end.toNat
      · subst hie; rw [htrl_end_idx, Option.getD_some, hlvl_v, Option.getD_some] at hl0
        rw [htrl_end_idx, Option.getD_some]; exact ⟨hvals_lit, hvals_nl, hlvl0 hl0⟩
      · have hi' : i < ks.trl_end.toNat := by omega
        let l := (ks.trl[i]?.getD 0#32).toNat
        have hne_vx : (l ^^^ 1) / 2 ≠ lit.toNat / 2 := by
          have := hnot_trl i hi'; rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
        rw [htrl_lt_idx i hi'] at hl0 ⊢; change ks'.lvlArr[l / 2]?.getD 0#32 = 0#32 at hl0
        rw [(hvar_other (l / 2) (hnot_trl i hi')).1] at hl0
        change ks'.vals[l]? = some 1#32 ∧ ks'.vals[l ^^^ 1]? = some 2#32 ∧ SemEntails P [l]
        rw [hvals_other l (hnot_trl i hi'), hvals_other (l ^^^ 1) hne_vx]
        exact hinv.assign.lvl0_ok i hi' hl0
  have hre' : K6ReasonOk ks' := fun i hi => by
    rw [e_te] at hi; by_cases hie : i = ks.trl_end.toNat
    · subst hie; change let l := (ks'.trl[ks.trl_end.toNat]?.getD 0#32).toNat
             let r := ks'.rsn[l / 2]?.getD 0#32; _
      rw [htrl_end_idx, Option.getD_some, hrsn_v, Option.getD_some]
      rcases hrsn_ok with rfl | ⟨hr_lt, hmem, hoth⟩
      · exact Or.inl rfl
      · right; exact ⟨hr_lt, hmem, fun x hx hne => let ⟨j, hj, hje⟩ := hoth x hx hne
          ⟨j, hj, by rw [htrl_lt_idx j hj]; exact hje⟩⟩
    · have hi' : i < ks.trl_end.toNat := by omega
      change let l := (ks'.trl[i]?.getD 0#32).toNat; let r := ks'.rsn[l / 2]?.getD 0#32; _
      rw [htrl_lt_idx i hi', (hvar_other _ (hnot_trl i hi')).2.1]
      rcases hinv.reasons i hi' with hnone | ⟨hr_lt, hmem, hoth⟩
      · exact Or.inl hnone
      · right; exact ⟨hr_lt, hmem, fun x hx hne => let ⟨j, hj, hje⟩ := hoth x hx hne
          ⟨j, by omega, by rw [htrl_lt_idx j (by omega)]; exact hje⟩⟩
  exact ⟨⟨hsh', hcl', hinv.watches, hba', hre'⟩, hsync'⟩

theorem k6SetIncons_preserves_inv {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hunsat : ∀ β, ¬ P β) : K6Inv L P (ks.putHdr .incons 1#32) :=
  k6Inv_cast hinv (hinv.shapes.putHdr .incons 1#32) (h9 := Or.inr fun _ => hunsat)

theorem k6LitsBounded_mono {M1 M2 : Nat} {ks : K6State} (hle : M1 ≤ M2) (h : K6LitsBounded M1 ks) :
    K6LitsBounded M2 ks :=
  ⟨fun cid hc l hl => Nat.lt_of_lt_of_le (h.1 cid hc l hl) (by omega),
   fun w hw => Nat.lt_of_lt_of_le (h.2 w hw) (by omega)⟩

end LeanQbe.T.Examples.Kissat.Proof.Kitten

end
