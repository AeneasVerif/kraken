/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Kitten.WpBtFlip
public import LeanQbe.T.Examples.Kissat.Proof.Kitten.WpPropagate
public import LeanQbe.T.Examples.Kissat.Proof.Kitten.WpAnalyze

/-!
# Step-13 `Func.wp` Proof for `full_k6_solve` (`12/14`, `Kissat.Proof.Kitten.WpSolve`)

Certifies `full_k6_solve_wp` (`step13K6SolveSpec`) against `Src.Kitten.full_k6_solve_body`
with `K6TailEq` preservation. Zero legacy `Full*` imports; zero `@[expose]` on theorems/lemmas;
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

/-! ## 1. Solve Loop Invariants & Helper Lemmas -/

private def K6LvlNonempty (ks : K6State) : Prop :=
  ∀ L0, 0 < L0 → L0 ≤ ks.lvl.toNat →
    ∃ i < ks.trl_end.toNat, (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = L0

private def K6FreeDecLate (ks : K6State) : Prop :=
  ∀ p < ks.trl_end.toNat,
    0 < (ks.lvlArr[(ks.trl[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat →
    ks.rsn[(ks.trl[p]?.getD 0#32).toNat / 2]?.getD 0#32 = 0xFFFFFFFF#32 →
    (ks.trl[p]?.getD 0#32).toNat ∉ k6AssumpLits ks →
    ∀ a ∈ k6AssumpLits ks, ∃ q < p, (ks.trl[q]?.getD 0#32).toNat = a

private structure K6SolveFrame (L : K6Layout) (ks0 ks : K6State) : Prop where
  nv : ks.nv = ks0.nv
  tail : K6TailEq L ks0 ks
  nassump : ks.nassump = ks0.nassump
  assump : ks.assump = ks0.assump
  neq : ks.neq = ks0.neq

private theorem K6SolveFrame.trans {L : K6Layout} {ks0 ks1 ks2 : K6State}
    (h1 : K6SolveFrame L ks0 ks1) (h2 : K6SolveFrame L ks1 ks2) : K6SolveFrame L ks0 ks2 :=
  ⟨h2.nv.trans h1.nv, k6TailEq_trans h1.tail h2.tail,
   h2.nassump.trans h1.nassump, h2.assump.trans h1.assump, h2.neq.trans h1.neq⟩

private structure K6SolveLoopInv (L : K6Layout) (P : (Nat → Bool) → Prop)
    (ks0 ks : K6State) (confl : BitVec 32) : Prop where
  inv : K6Inv L P ks
  sync : K6TrailSynced ks
  frame : K6SolveFrame L ks0 ks
  lvlne : K6LvlNonempty ks
  late : K6FreeDecLate ks
  confl_ok : confl ≠ 0xFFFFFFFF#32 →
    confl.toNat < ks.nc.toNat ∧ ∀ l ∈ k6ClauseLits ks confl.toNat, ks.vals[l]? = some 2#32

private theorem k6_lvl_le_trl_end {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hne : K6LvlNonempty ks) : ks.lvl.toNat ≤ ks.trl_end.toNat := by
  have hstep : ∀ lv, lv ≤ ks.lvl.toNat → 0 < lv →
      ∃ i < ks.trl_end.toNat, lv - 1 ≤ i ∧
        (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = lv := by
    intro lv; induction lv with
    | zero => intro _ hz; omega
    | succ lv ih =>
      intro hle _; obtain ⟨i, hi, hiv⟩ := hne (lv + 1) (Nat.succ_pos lv) hle
      by_cases hL0 : lv = 0
      · subst hL0; exact ⟨i, hi, Nat.zero_le _, hiv⟩
      · obtain ⟨j, hj, hj_le, hjv⟩ := ih (by omega) (Nat.pos_of_ne_zero hL0)
        refine ⟨i, hi, ?_, hiv⟩
        by_cases hlt : lv ≤ i
        · omega
        · exfalso; have hm := hinv.assign.trl_lvl_mono i j (by omega) hj; rw [hiv, hjv] at hm; omega
  by_cases hl0 : ks.lvl.toNat = 0
  · rw [hl0]; exact Nat.zero_le _
  · obtain ⟨i, _, hle, _⟩ := hstep ks.lvl.toNat (Nat.le_refl _) (Nat.pos_of_ne_zero hl0); omega

private theorem k6_inv_set_lvl {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (v : BitVec 32)
    (hvl : ∀ w < ks.nv.toNat, (ks.lvlArr[w]?.getD 0#32).toNat ≤ v.toNat) :
    K6Inv L P (ks.putHdr .lvl v) :=
  ⟨hinv.shapes.putHdr .lvl v, k6ClausesOk_cast hinv.clauses,
   by dsimp only [K6State.putHdr]; exact hinv.watches,
   { hinv.assign with trl_lvl_le := hvl }, by dsimp only [K6State.putHdr]; exact hinv.reasons⟩

private theorem k6_inv_set_hdr_nc {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (f : K6HdrField) (hf : f = .tick_lim ∨ f = .qsearch) (v : BitVec 32) :
    K6Inv L P (ks.putHdr f v) := by
  rcases hf with rfl | rfl <;> exact
    ⟨hinv.shapes.putHdr _ v, k6ClausesOk_cast hinv.clauses,
     by dsimp only [K6State.putHdr]; exact hinv.watches,
     k6BaseAssignOk_cast hinv.assign, by dsimp only [K6State.putHdr]; exact hinv.reasons⟩

private theorem k6_mem_assumpLits_of_lt {ks : K6State}
    (hlen : ks.nassump.toNat ≤ ks.assump.length) {i : Nat} (hi : i < ks.nassump.toNat) :
    (ks.assump[i]?.getD 0#32).toNat ∈ k6AssumpLits ks := by
  unfold k6AssumpLits; rw [List.mem_map]; refine ⟨ks.assump[i]?.getD 0#32, ?_, rfl⟩
  rw [List.mem_take_iff_getElem]
  exact ⟨i, by omega, by simp [List.getElem?_eq_getElem (by omega : i < ks.assump.length)]⟩

private theorem k6_trl_idx_eq_of_val {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) {p q : Nat} (hp : p < ks.trl_end.toNat) (hq : q < ks.trl_end.toNat)
    (heq : (ks.trl[p]?.getD 0#32).toNat = (ks.trl[q]?.getD 0#32).toNat) : p = q := by
  by_cases hpq : p = q
  · exact hpq
  · exfalso; exact k6_trl_nodup_var_ne hinv.shapes hinv.clauses.nv_le hinv.assign hp hq hpq
      (congrArg (· / 2) heq)

private theorem k6_decide_step_preserves {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks0 ks : K6State} (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks)
    (hframe : K6SolveFrame L ks0 ks) (hlvlne : K6LvlNonempty ks) (hlate : K6FreeDecLate ks)
    {lit : BitVec 32} (hlit : lit.toNat < 2 * ks.nv.toNat) (hun : ks.vals[lit.toNat]? = some 0#32)
    (hall_ass : lit.toNat ∉ k6AssumpLits ks → ∀ a ∈ k6AssumpLits ks, ks.vals[a]? = some 1#32) :
    let ks' := k6AssignStep (ks.putHdr .lvl (ks.lvl + 1#32)) lit 0xFFFFFFFF#32
    K6Inv L P ks' ∧ K6TrailSynced ks' ∧ K6SolveFrame L ks0 ks' ∧
    K6LvlNonempty ks' ∧ K6FreeDecLate ks' := by
  intro ks'; have hmL := L.hmaxV; have hnv := hinv.clauses.nv_le
  have hle_te := k6_lvl_le_trl_end hinv hlvlne; have hte_le := hinv.assign.trl_end_le
  have hlvl1_nat : (ks.lvl + 1#32).toNat = ks.lvl.toNat + 1 := by bv_omega
  have hlvl1_ne0 : ks.lvl + 1#32 ≠ 0#32 := fun h => by
    have := congrArg BitVec.toNat h; rw [hlvl1_nat] at this; simp at this
  have hinv1 := k6_inv_set_lvl hinv (ks.lvl + 1#32) fun v hv => by
    change (ks.lvlArr[v]?.getD 0#32).toNat ≤ (ks.lvl + 1#32).toNat
    rw [hlvl1_nat]; have := hinv.assign.trl_lvl_le v hv; omega
  have hdec1 : ∀ i < ks.trl_end.toNat,
      ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 ≠ ks.lvl + 1#32 := fun i hi heq => by
    have hli := hinv.assign.trl_lt _
      (k6_mem_trailLits_of_lt hi (by rw [hinv.shapes.trl_len]; omega))
    have hle := hinv.assign.trl_lvl_le ((ks.trl[i]?.getD 0#32).toNat / 2) (by omega)
    have hcon := congrArg BitVec.toNat heq; rw [hlvl1_nat] at hcon; omega
  obtain ⟨hinv', hsync'⟩ := k6AssignStep_preserves_inv hinv1 hsync hlit hun
    (fun h => absurd h hlvl1_ne0) (fun _ _ => hdec1) (Or.inl rfl)
  have hte_lt := k6_trl_end_lt_of_unassigned hinv.shapes hnv hinv.assign hlit (by simp [hun])
  have hv_div := (k6_bv32_div2_lt hlit).1
  have e_te : ks'.trl_end.toNat = ks.trl_end.toNat + 1 := by
    dsimp only [ks', k6AssignStep, K6State.putHdr]; bv_omega
  have e_trl_lt : ∀ i < ks.trl_end.toNat, ks'.trl[i]? = ks.trl[i]? := fun i hi => by
    dsimp only [ks', k6AssignStep, K6State.putHdr]; exact List.getElem?_set_ne (by omega)
  have e_trl_end : ks'.trl[ks.trl_end.toNat]? = some lit := by
    dsimp only [ks', k6AssignStep, K6State.putHdr]
    exact List.getElem?_set_self (by rw [hinv.shapes.trl_len]; omega)
  have e_lvl_v : ks'.lvlArr[lit.toNat / 2]? = some (ks.lvl + 1#32) := by
    dsimp only [ks', k6AssignStep, K6State.putHdr]; rw [hv_div]
    exact List.getElem?_set_self (by rw [hinv.shapes.lvlArr_len]; omega)
  have hnot_trl : ∀ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 :=
    fun i hi heq => by
      have hnz := (hinv.assign.vals_nz_iff_trl lit.toNat hlit).mpr ⟨i, hi, heq⟩; simp [hun] at hnz
  have e_var_other : ∀ v, v ≠ lit.toNat / 2 →
      ks'.lvlArr[v]? = ks.lvlArr[v]? ∧ ks'.rsn[v]? = ks.rsn[v]? := fun v hne => by
    dsimp only [ks', k6AssignStep, K6State.putHdr]; rw [hv_div]
    exact ⟨List.getElem?_set_ne hne.symm, List.getElem?_set_ne hne.symm⟩
  refine ⟨hinv', hsync',
    K6SolveFrame.trans hframe ⟨rfl, k6TailEq_trans
      (k6TailEq_of_putHdr_ne_nv (L := L) (ks := ks) (f := .lvl) (by decide) (ks.lvl + 1#32))
      (k6TailEq_of_k6AssignStep lit 0xFFFFFFFF#32 hlit), rfl, rfl, rfl⟩,
    fun L0 hL0 hLle => by
      change L0 ≤ (ks.lvl + 1#32).toNat at hLle; rw [hlvl1_nat] at hLle
      by_cases htop : L0 = ks.lvl.toNat + 1
      · subst htop; refine ⟨ks.trl_end.toNat, by rw [e_te]; omega, ?_⟩
        rw [e_trl_end, Option.getD_some, e_lvl_v, Option.getD_some, hlvl1_nat]
      · obtain ⟨i, hi, hiv⟩ := hlvlne L0 hL0 (by omega)
        refine ⟨i, by rw [e_te]; omega, ?_⟩
        rw [e_trl_lt i hi, (e_var_other _ (hnot_trl i hi)).1]; exact hiv,
    by intro p hp hpos hrsn hnot a ha; rw [e_te] at hp; change a ∈ k6AssumpLits ks at ha
       by_cases hpe : p = ks.trl_end.toNat
       · subst hpe; rw [e_trl_end, Option.getD_some] at hnot
         have ha_val := hall_ass hnot a ha
         have ha_lt : a < 2 * ks.nv.toNat := by
           simp only [k6AssumpLits, List.mem_map, List.mem_take_iff_getElem] at ha
           obtain ⟨_, ⟨ia, hia, rfl⟩, rfl⟩ := ha
           have hlen : ks.nassump.toNat ≤ ks.assump.length := by
             rw [hinv.shapes.assump_len]; exact hinv.clauses.nassump_le
           simpa [List.getElem?_eq_getElem (by omega : ia < ks.assump.length)] using
             hinv.clauses.assump_ok ia (by omega)
         obtain ⟨q, hq, hqv⟩ := (hinv.assign.vals_nz_iff_trl a ha_lt).mp (by simp [ha_val])
         have hsy_q := hsync q hq
         have ha_eq : (ks.trl[q]?.getD 0#32).toNat = a := by
           rcases (litVar_eq_iff (ks.trl[q]?.getD 0#32).toNat a).mp
             (by simpa [litVar] using hqv) with heq | heq
           · exact heq
           · exfalso; have hx : (ks.trl[q]?.getD 0#32).toNat ^^^ 1 = a := by
               rw [heq, show litNeg a = a ^^^ 1 from rfl, k6_nat_xor1_xor1]
             dsimp only at hsy_q; rw [hx, ha_val] at hsy_q; cases hsy_q.2
         exact ⟨q, hq, by rw [e_trl_lt q hq]; exact ha_eq⟩
       · have hp' : p < ks.trl_end.toNat := by omega
         rw [e_trl_lt p hp', (e_var_other _ (hnot_trl p hp')).1] at hpos
         rw [e_trl_lt p hp', (e_var_other _ (hnot_trl p hp')).2] at hrsn
         rw [e_trl_lt p hp'] at hnot
         obtain ⟨q, hqp, hqa⟩ := hlate p hp' hpos hrsn hnot a ha
         exact ⟨q, hqp, by rw [e_trl_lt q (by omega)]; exact hqa⟩⟩

private theorem k6_allDecisionsInAssumps_of_late {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks : K6State} (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks)
    (hlate : K6FreeDecLate ks) {ia : Nat} (hia : ia < ks.nassump.toNat)
    (hfals : ks.vals[(ks.assump[ia]?.getD 0#32).toNat]? = some 2#32) :
    ∀ β, P β → ¬ (unitsCnf (k6AssumpLits ks)).Sat β := by
  have hlen_a : ks.nassump.toNat ≤ ks.assump.length := by
    rw [hinv.shapes.assump_len]; exact hinv.clauses.nassump_le
  have ha_mem := k6_mem_assumpLits_of_lt hlen_a hia
  refine k6_falsified_assump_unsat hinv hsync (fun d hd => ?_) hia hfals
  by_cases hd_mem : d ∈ k6AssumpLits ks
  · exact hd_mem
  · exfalso; have hmL := L.hmaxV; have hnv := hinv.clauses.nv_le
    have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
      rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; omega
    obtain ⟨p, hp, rfl, hpos, hrsn⟩ := (k6_mem_trailDecisions_iff htrl_len).mp hd
    obtain ⟨q, hq, hqa⟩ := hlate p hp hpos hrsn hd_mem _ ha_mem
    have hsy := hsync q (Nat.lt_trans hq hp); dsimp only at hsy
    rw [hqa, hfals] at hsy; cases hsy.1

private theorem k6_solveLoopInv_of_propagate {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks0 ks ks' : K6State} {confl : BitVec 32} (_hinv : K6Inv L P ks)
    (hframe : K6SolveFrame L ks0 ks) (hlvlne : K6LvlNonempty ks) (hlate : K6FreeDecLate ks)
    (hinv' : K6Inv L P ks') (hsync' : K6TrailSynced ks') (hp : K6PropPreserved ks ks')
    (htl : K6TailEq L ks ks') (hte_le : ks.trl_end.toNat ≤ ks'.trl_end.toNat)
    (htrl_kept : ∀ i < ks.trl_end.toNat, ks'.trl[i]? = ks.trl[i]? ∧
      ks'.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? =
        ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? ∧
      ks'.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]? =
        ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?)
    (hnew : ∀ i, ks.trl_end.toNat ≤ i → i < ks'.trl_end.toNat →
      ks'.lvlArr[(ks'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = ks.lvl ∧
      ks'.rsn[(ks'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 ≠ 0xFFFFFFFF#32)
    (hc_ok : confl ≠ 0xFFFFFFFF#32 → confl.toNat < ks'.nc.toNat ∧
      ∀ l ∈ k6ClauseLits ks' confl.toNat, ks'.vals[l]? = some 2#32) :
    K6SolveLoopInv L P ks0 ks' confl :=
  ⟨hinv', hsync', K6SolveFrame.trans hframe ⟨hp.nv, htl, hp.nassump, hp.assump, hp.neq⟩,
   fun L0 hL0 hLle => by
     rw [hp.lvl] at hLle; obtain ⟨i, hi, hiv⟩ := hlvlne L0 hL0 hLle
     obtain ⟨ht, hl, _⟩ := htrl_kept i hi
     exact ⟨i, Nat.lt_of_lt_of_le hi hte_le, by rw [ht, hl]; exact hiv⟩,
   fun p hp_lt hpos hrsn hnot a ha => by
     have hass_eq : k6AssumpLits ks' = k6AssumpLits ks := by
       unfold k6AssumpLits; rw [hp.nassump, hp.assump]
     rw [hass_eq] at hnot ha
     by_cases hp_old : p < ks.trl_end.toNat
     · obtain ⟨ht, hl, hr⟩ := htrl_kept p hp_old
       rw [ht, hl] at hpos; rw [ht, hr] at hrsn; rw [ht] at hnot
       obtain ⟨q, hqp, hqa⟩ := hlate p hp_old hpos hrsn hnot a ha
       exact ⟨q, hqp, by rw [(htrl_kept q (Nat.lt_trans hqp hp_old)).1]; exact hqa⟩
     · exact absurd hrsn (hnew p (by omega) hp_lt).2,
   hc_ok⟩

private theorem k6_solveLoopInv_of_analyze {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks0 ks ks' : K6State} (hinv : K6Inv L P ks) (hframe : K6SolveFrame L ks0 ks)
    (hlvlne : K6LvlNonempty ks) (hlate : K6FreeDecLate ks)
    (hinv' : K6Inv L P ks') (hsync' : K6TrailSynced ks')
    (e_nv : ks'.nv = ks.nv) (htl : K6TailEq L ks ks') (e_na : ks'.nassump = ks.nassump)
    (e_as : ks'.assump = ks.assump) (e_nq : ks'.neq = ks.neq)
    (hlvl_lt : ks'.lvl.toNat < ks.lvl.toNat)
    (hdec_sub : ∀ d ∈ k6TrailDecisions ks', ∃ i < ks.trl_end.toNat,
      (ks.trl[i]?.getD 0#32).toNat = d ∧ d ∈ k6TrailDecisions ks ∧
      (ks.lvlArr[d / 2]?.getD 0#32).toNat ≤ ks'.lvl.toNat)
    (hkept_below : ∀ i < ks.trl_end.toNat,
      (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ ks'.lvl.toNat →
      i < ks'.trl_end.toNat ∧ ks'.trl[i]? = ks.trl[i]? ∧
      ks'.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? =
        ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?) :
    K6SolveLoopInv L P ks0 ks' 0xFFFFFFFF#32 :=
  ⟨hinv', hsync', K6SolveFrame.trans hframe ⟨e_nv, htl, e_na, e_as, e_nq⟩,
   fun L0 hL0 hLle => by
     obtain ⟨i, hi, hiv⟩ := hlvlne L0 hL0 (Nat.le_trans hLle (Nat.le_of_lt hlvl_lt))
     obtain ⟨hi', ht, hl⟩ := hkept_below i hi (by rw [hiv]; exact hLle)
     exact ⟨i, hi', by rw [ht, hl]; exact hiv⟩,
   fun p hp hpos hrsn hnot a ha => by
     have hass_eq : k6AssumpLits ks' = k6AssumpLits ks := by unfold k6AssumpLits; rw [e_na, e_as]
     rw [hass_eq] at hnot ha; have hmL := L.hmaxV; have hnv' := hinv'.clauses.nv_le
     have hnv := hinv.clauses.nv_le
     have htrl_len' : ks'.trl_end.toNat ≤ ks'.trl.length := by
       rw [hinv'.shapes.trl_len]; have := hinv'.assign.trl_end_le; omega
     have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
       rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; omega
     obtain ⟨p0, hp0, hp0_eq, hp0_dec, hp0_lvl⟩ :=
       hdec_sub _ ((k6_mem_trailDecisions_iff htrl_len').mpr ⟨p, hp, rfl, hpos, hrsn⟩)
     have hle0 : (ks.lvlArr[(ks.trl[p0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
         ks'.lvl.toNat := by rw [hp0_eq]; exact hp0_lvl
     obtain ⟨hp0', hp0_trl, _⟩ := hkept_below p0 hp0 hle0
     obtain rfl : p0 = p := k6_trl_idx_eq_of_val hinv' hp0' hp (by rw [hp0_trl]; exact hp0_eq)
     obtain ⟨_, _, _, hpos0, hrsn0⟩ := (k6_mem_trailDecisions_iff htrl_len).mp hp0_dec
     obtain ⟨q, hqp, hqa⟩ := hlate p0 hp0 (by rw [← hp0_eq] at hpos0; exact hpos0)
       (by rw [← hp0_eq] at hrsn0; exact hrsn0) (by rw [← hp0_trl]; exact hnot) a ha
     have hq_lvl := Nat.le_trans (hinv.assign.trl_lvl_mono q p0 (Nat.le_of_lt hqp) hp0) hle0
     exact ⟨q, hqp, by rw [(hkept_below q (Nat.lt_trans hqp hp0) hq_lvl).2.1]; exact hqa⟩,
   fun h => absurd rfl h⟩

private theorem k6_solveLoopInv_of_lvl0 {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks0 ks : K6State} (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks)
    (hlvl0 : ks.lvl = 0#32) (hframe : K6SolveFrame L ks0 ks) :
    K6SolveLoopInv L P ks0 ks 0xFFFFFFFF#32 :=
  ⟨hinv, hsync, hframe,
   fun L0 hL0 hLle => by rw [hlvl0] at hLle; simp at hLle; omega,
   fun p hp hpos => by
     exfalso; have hmL := L.hmaxV; have hnv := hinv.clauses.nv_le
     have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
       rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; omega
     have hlp := hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hp htrl_len)
     have hle := hinv.assign.trl_lvl_le ((ks.trl[p]?.getD 0#32).toNat / 2) (by omega)
     rw [hlvl0] at hle; simp at hle; omega,
   fun h => absurd rfl h⟩

private abbrev K6SolveQ (L : K6Layout) (P : (Nat → Bool) → Prop) (c : FullCfg) (s : FullState)
    (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ (r fuel' : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
    let s' : FullState := { s with core := { s.core with fuel := fuel' }
                                   scratch := { s.scratch with scratch_buf := scr' } }
    let ks := k6StateOfScratch L s.scratch.scratch_buf; let ks' := k6StateOfScratch L scr'
    s'.LengthsOk c → fuel'.toNat ≤ s.core.fuel.toNat →
    (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
    K6Inv L P ks' → K6TrailSynced ks' → ks'.nv = ks.nv → K6TailEq L ks ks' →
    ks'.nassump = ks.nassump →
    k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf → ks'.neq = ks.neq →
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
    (r = 20#64 → ∀ β, P β → ¬ (unitsCnf (k6AssumpLitsS L scr')).Sat β) →
    (FullMem c s' ⋆ R) m' → Q (r, ()) m'

private theorem k6_solve_post_finish {c : FullCfg} {s : FullState} {P : (Nat → Bool) → Prop}
    {L : K6Layout} {scr : List (BitVec 32)} {ks0 ks' : K6State} {fuel' r : BitVec 64}
    {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hlen : s.LengthsOk c) (hL_scr : L.scrLen = c.scratch_cap)
    (hlen_L : scr.length = L.scrLen) (hof_ks0 : k6StateOfScratch L scr = ks0)
    (hinv' : K6Inv L P ks') (hsync' : K6TrailSynced ks')
    (hfuel : fuel'.toNat ≤ s.core.fuel.toNat) (hframe : K6SolveFrame L ks0 ks')
    (hr : r = 0#64 ∨ r = 10#64 ∨ r = 20#64)
    (hr20 : r = 20#64 → ∀ β, P β → ¬ (unitsCnf (k6AssumpLits ks')).Sat β)
    (hm' : (FullK6Frame c L { s with core := { s.core with fuel := fuel' } } ⋆
      K6Mem L (L.kPtr c.pScratchBuf) ks' ⋆ R) m')
    (hQ : K6SolveQ L P c s R Q) (hscr_eq : s.scratch.scratch_buf = scr) : Q (r, ()) m' := by
  let sFuel : FullState := { s with core := { s.core with fuel := fuel' } }
  let scr' := scr.take L.k6Base ++ ks'.toSlab
  have hsh' := hinv'.shapes
  have hkbase_le : L.k6Base ≤ scr.length := by rw [hlen_L]; unfold K6Layout.scrLen; omega
  have htk_len : (scr.take L.k6Base).length = L.k6Base := List.length_take_of_le hkbase_le
  have hscr'_len : scr'.length = c.scratch_cap := by
    simp only [scr', List.length_append, htk_len, K6State.toSlab_length hsh']
    rw [← hL_scr]; unfold K6Layout.scrLen; omega
  have hof' : k6StateOfScratch L scr' = ks' := by
    unfold k6StateOfScratch
    rw [show scr' = scr.take L.k6Base ++ ks'.toSlab from rfl,
      k6_slab_drop_exact _ ks'.toSlab htk_len]
    exact K6State.ofSlab_toSlab hsh'
  have hlen' := k6_fullState_lengthsOk_scratch
    (⟨{ hlen.core_ok with vals_len := hlen.core_ok.vals_len }, hlen.scratch_ok⟩ : sFuel.LengthsOk c)
    hscr'_len
  have hm_join := fullMem_join_k6 (c := c) (L := L) (s := sFuel) (ks' := ks') (R := R)
    (by change L.k6Base ≤ sFuel.scratch.scratch_buf.length; rw [hscr_eq]; exact hkbase_le) hsh' hm'
  refine hQ r fuel' scr' m' hlen' hfuel
    (fun i hi => by
      rw [hscr_eq, List.getElem?_append_left (by rw [htk_len]; exact hi),
        List.getElem?_take_of_lt hi])
    (hof' ▸ hinv') (hof' ▸ hsync')
    (by rw [hof', hscr_eq, hof_ks0]; exact hframe.nv)
    (by rw [hof', hscr_eq, hof_ks0]; exact hframe.tail)
    (by rw [hof', hscr_eq, hof_ks0]; exact hframe.nassump)
    (by
      unfold k6AssumpLitsS k6AssumpLits
      rw [hof', hscr_eq, hof_ks0, hframe.nassump, hframe.assump])
    (by rw [hof', hscr_eq, hof_ks0]; exact hframe.neq)
    hr (fun h20 => by unfold k6AssumpLitsS; rw [hof']; exact hr20 h20)
    (by simpa [sFuel, scr', hscr_eq] using hm_join)

private theorem k6_solve_setStatus_finish {c : FullCfg} {s : FullState} {P : (Nat → Bool) → Prop}
    {L : K6Layout} {ks : K6State} {fuel' r : BitVec 64} {st : BitVec 32}
    {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hlen : s.LengthsOk c) (hL_scr : L.scrLen = c.scratch_cap)
    (hlen_L : s.scratch.scratch_buf.length = L.scrLen)
    (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks) (hfuel : fuel'.toNat ≤ s.core.fuel.toNat)
    (hframe : K6SolveFrame L (k6StateOfScratch L s.scratch.scratch_buf) ks)
    (hr : r = 0#64 ∨ r = 10#64 ∨ r = 20#64)
    (hr20 : r = 20#64 → ∀ β, P β → ¬ (unitsCnf (k6AssumpLits ks)).Sat β)
    (hm' : (K6MemA L (L.kPtr c.pScratchBuf) (ks.putHdr .status st) ⋆
      (FullK6Frame c L { s with core := { s.core with fuel := fuel' } } ⋆ R)) m')
    (hQ : K6SolveQ L P c s R Q) : Q (r, ()) m' := by
  obtain ⟨_, hmFin⟩ := k6MemA_to_mem hm'
  have htl' := k6TailEq_trans hframe.tail (k6TailEq_of_putHdr_ne_nv (f := .status) (by decide) st)
  exact k6_solve_post_finish hlen hL_scr hlen_L rfl (k6SetStatus_preserves_inv hinv st)
    (k6TrailSynced_cast hsync) hfuel
    ⟨by k6_field; exact hframe.nv, htl', by k6_field; exact hframe.nassump,
      hframe.assump, by k6_field; exact hframe.neq⟩ hr hr20 (sep_ac hmFin) hQ rfl

private theorem k6_solve_decide_prep {L : K6Layout} {P : (Nat → Bool) → Prop} {ks0 km : K6State}
    (hinv : K6Inv L P km) (hsync : K6TrailSynced km) (hframe : K6SolveFrame L ks0 km)
    (hlvlne : K6LvlNonempty km) (hlate : K6FreeDecLate km) {pick3 : BitVec 32}
    (hpk_lt : pick3.toNat < km.nv.toNat) (hpk_val : km.vals[2 * pick3.toNat]?.getD 0#32 = 0#32)
    (hall_ass : ∀ a ∈ k6AssumpLits km, km.vals[a]? = some 1#32) :
    let ks_q := km.putHdr .qsearch pick3
    let ph := (ks_q.flags[pick3.toNat]?.getD 0#32 ^^^ ks_q.phase) &&& 1#32
    let lit_d := (pick3 <<< (1 : Nat)) ||| ph
    let ks' := k6AssignStep (ks_q.putHdr .lvl (ks_q.lvl + 1#32)) lit_d 0xFFFFFFFF#32
    lit_d.toNat < 2 * L.maxV ∧ km.trl_end.toNat < km.nv.toNat ∧
    K6Inv L P ks' ∧ K6TrailSynced ks' ∧ K6SolveFrame L ks0 ks' ∧
    K6LvlNonempty ks' ∧ K6FreeDecLate ks' := by
  intro ks_q ph lit_d ks'
  have hmL := L.hmaxV; have hnv_m := hinv.clauses.nv_le
  have hinv_q := k6_inv_set_hdr_nc hinv .qsearch (Or.inr rfl) pick3
  have hframe_q : K6SolveFrame L ks0 ks_q := K6SolveFrame.trans hframe
    ⟨rfl, k6TailEq_of_putHdr_ne_nv (f := .qsearch) (by decide) pick3, rfl, rfl, rfl⟩
  have hph_lt : ph.toNat < 2 := by
    dsimp only [ph]; rw [BitVec.toNat_and]; have h1 : (1#32 : BitVec 32).toNat = 1 := rfl
    rw [h1]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hlit_d := k6_bv32_shl1_or_bit hpk_lt hnv_m hmL.2 hph_lt
  have hlit_0 : ks_q.vals[lit_d.toNat]? = some 0#32 := by
    rcases (by omega : ph.toNat = 0 ∨ ph.toNat = 1) with h0 | h1
    · rw [hlit_d.1, h0, Nat.add_zero]
      exact k6_vals_some hinv_q.shapes (by unfold sz2V; omega) hpk_val
    · have hxor : 2 * pick3.toNat + 1 = (2 * pick3.toNat) ^^^ 1 := by
        rcases k6_nat_xor1_cases (2 * pick3.toNat) with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
      rw [hlit_d.1, h1, hxor]
      exact k6_vals_some hinv_q.shapes
        (by unfold sz2V; change (2 * pick3.toNat) ^^^ 1 < 2 * L.maxV; omega)
        (k6_vals_xor1_zero hinv_q (by change 2 * pick3.toNat < 2 * km.nv.toNat; omega) hpk_val)
  have hte_lt := k6_trl_end_lt_of_unassigned hinv_q.shapes hnv_m hinv_q.assign
    (by change lit_d.toNat < 2 * km.nv.toNat; exact hlit_d.2)
    (by change ks_q.vals[lit_d.toNat]?.getD 0#32 = 0#32; rw [hlit_0]; rfl)
  obtain ⟨hinv_d, hsync_d, hframe_d, hlvlne_d, hlate_d⟩ :=
    k6_decide_step_preserves hinv_q hsync hframe_q hlvlne hlate
      (by change lit_d.toNat < 2 * ks_q.nv.toNat; exact hlit_d.2) hlit_0
      (fun _ a ha => hall_ass a ha)
  exact ⟨Nat.lt_of_lt_of_le hlit_d.2 (by change 2 * km.nv.toNat ≤ 2 * L.maxV; omega),
    hte_lt, hinv_d, hsync_d, hframe_d, hlvlne_d, hlate_d⟩

private theorem k6_solve_pick_bounds {L : K6Layout} {km : K6State} (hmL : L.maxV ≤ 8192)
    (hnv_m : km.nv.toNat ≤ L.maxV) {c : BitVec 32} (hc_lt : c.toNat < km.nv.toNat) :
    (c <<< (1 : Nat)).toNat = 2 * c.toNat ∧ (c <<< (1 : Nat)).toNat < sz2V L ∧
      c.toNat < szV L := by
  have hsh : (c <<< (1 : Nat)).toNat = 2 * c.toNat := by rw [BitVec.toNat_shiftLeft]; simp; omega
  exact ⟨hsh, by unfold sz2V; omega, by unfold szV; omega⟩

private theorem k6_solve_pick_qlist_wp {L : K6Layout} {km : K6State} (hmL : L.maxV ≤ 8192)
    (hnv_m : km.nv.toNat ≤ L.maxV) {c s : BitVec 32} (hc_lt : c.toNat < km.nv.toNat)
    (hs_lt : s.toNat < km.nv.toNat) :
    (c <<< (1 : Nat)).toNat = 2 * c.toNat ∧ (c <<< (1 : Nat)).toNat < sz2V L ∧
      c.toNat < szV L ∧ (s + 1#32).toNat = s.toNat + 1 :=
  ⟨(k6_solve_pick_bounds hmL hnv_m hc_lt).1, (k6_solve_pick_bounds hmL hnv_m hc_lt).2.1,
   (k6_solve_pick_bounds hmL hnv_m hc_lt).2.2, by bv_omega⟩

open Lean Elab Tactic in
local elab "k6_solve_qlist_pick" PickInv:ident hJ:ident km:ident hmL:term:max hnv_m:ident
    initC:term:max hmInit:term:max fallbackP:term:max fallbackHP:term:max : tactic => do
  let lId := mkIdent `L; let kPtr := mkIdent `kPtr; let cId := mkIdent `c
  let sFuel1 := mkIdent `sFuel1; let rId := mkIdent `R
  evalTactic (← `(tactic| (
    refine wp_while_break_state (brkTs := [i32, i32, i32]) (lpTs := [i32, i32])
      (β := BitVec 32 × BitVec 32 × BitVec 32)
      (fun bst => (bst.1, bst.2.1, bst.2.2, ()))
      (fun bst m_v => $PickInv bst.2.1 m_v)
      (α := BitVec 32 × BitVec 32) (fun st => (st.1, st.2, ()))
      (fun st => ($km).nv.toNat - st.2.toNat)
      (fun st m_v => st.2.toNat ≤ ($km).nv.toNat ∧
        (K6MemA $lId $kPtr $km ⋆ (FullK6Frame $cId $lId $sFuel1 ⋆ $rId)) m_v) ?_ ?_ ?_
    · rintro B ⟨c_, p_, s_⟩ m_v hp_
      exact wp_jump_state (α := BitVec 32 × BitVec 32 × BitVec 32)
        (proj := fun p : BitVec 32 × BitVec 32 × BitVec 32 => (p.1, p.2.1, p.2.2, ()))
        (c_, p_, s_) rfl ($hJ (c_, p_, s_) m_v hp_)
    · rintro B L' ⟨c', s'⟩ m_v hB hL ⟨hs_le, hm_v⟩; c0_hsplit
      · c0_hsplit
        · have hc_lt : c'.toNat < ($km).nv.toNat := by bv_omega
          have hs_lt : s'.toNat < ($km).nv.toNat := by bv_omega
          obtain ⟨hc_shl, _, _, hs_1⟩ :=
            k6_solve_pick_qlist_wp $hmL $hnv_m hc_lt hs_lt
          c0_hsplit
          · c0_hsteps!; exact hB (c', c', s') m_v ⟨Or.inr ⟨hc_lt, by rwa [← hc_shl]⟩, hm_v⟩
          · c0_hsteps!
            exact hL (($km).qprev[c'.toNat]?.getD 0#32, s' + 1#32) m_v
              (by dsimp only; rw [hs_1]; omega) ⟨by dsimp only; rw [hs_1]; omega, hm_v⟩
        · c0_hsteps!; exact hB (c', $fallbackP, s') m_v ⟨($fallbackHP).1, hm_v⟩
      · c0_hsteps!; exact hB (c', $fallbackP, s') m_v ⟨($fallbackHP).1, hm_v⟩
    · intro B L' _ hL
      exact wp_jump_state (α := BitVec 32 × BitVec 32)
        (proj := fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ()))
        ($initC, 0#32) rfl (hL _ _ ⟨Nat.zero_le _, $hmInit⟩))))

/-! ## 2. Parametric `Func.wp` Theorem for `full_k6_solve` (`12/14`) -/

/-- `12/14`: Parametric `Func.wp` proof for `full_k6_solve`. -/
theorem full_k6_solve_wp (Γ : Env)
    (hMaxV : Γ.Has "full_m6_max_v" m6MaxVSpec)
    (hBt : Γ.Has "full_k6_backtrack" step13K6BacktrackSpec)
    (hAsg : Γ.Has "full_k6_assign" k6AssignSpec)
    (hProp : Γ.Has "full_k6_propagate" step13K6PropagateSpec)
    (hAna : Γ.Has "full_k6_analyze" step13K6AnalyzeSpec) :
    ∀ args m Q X, step13K6SolveSpec args m Q X → Func.wp Γ full_k6_solve_body args m Q X := by
  rintro ⟨hPtr, tick_lim, ⟨⟩⟩ m Q X ⟨c, s, P, L, R, rfl, hlen, hL_scr, hL_mv, hinv0, hm, hQ⟩
  let scr := s.scratch.scratch_buf; let ks0 := k6StateOfScratch L scr
  let kPtr := L.kPtr c.pScratchBuf
  have hmL := L.hmaxV; have hacL := L.hacap
  have hlen_L : scr.length = L.scrLen := hlen.scratch_ok.scratch_buf_len.trans hL_scr.symm
  have hsc_lt : c.scratch_cap < 2 ^ 64 := Nat.lt_trans c.hscr (by unfold dimacsBound; decide)
  have hmv32_eq : (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = L.mv32 := by
    rw [← hL_mv]; unfold K6Layout.mv32; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmF0 : (FullK6Frame c L s ⋆ K6Mem L kPtr ks0 ⋆ R) m := by
    rw [fullMem_eq_k6Frame hlen_L] at hm; exact hm
  clear hm; c0_hsteps_nogrp; refine k6_maxV_call_step hMaxV hsc_lt ?_; c0_hsplit
  · exfalso; have hmv0 : L.mv32 = 0#32 := by rw [← hmv32_eq]; exact ‹_›
    have h0 := congrArg BitVec.toNat hmv0; change (BitVec.ofNat 32 L.maxV).toNat = 0 at h0
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h0; omega
  · rw [hmv32_eq]; c0_hsteps_nogrp; rw [k6_ptr_base L c.pScratchBuf]; k6_call hBt
    refine ⟨L, P, ks0, FullK6Frame c L s ⋆ R, hinv0, Or.inl rfl, sep_ac hmF0,
      fun ks1 m1 hinv1 hsync1 hlvl1 _ hbt1 htl1 _ _ hm1 => ?_⟩
    have hframe1 : K6SolveFrame L ks0 ks1 := ⟨hbt1.nv, htl1, hbt1.nassump, hbt1.assump, hbt1.neq⟩
    have hmA1 := k6Mem_to_amem hinv1.shapes hm1; clear hm1; c0_hsplit
    · have hinc1 : ks1.incons ≠ 0#32 := ‹_›; c0_hsteps!
      exact k6_solve_setStatus_finish hlen hL_scr hlen_L hinv1 hsync1 (le_refl _) hframe1
        (Or.inr (Or.inr rfl)) (fun _ β hP _ => hinv1.clauses.incons_ok hinc1 β hP) hm hQ
    · c0_hsteps_nogrp
      refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
        (fun tlim => (tlim, ())) (fun _ => True) ?_ (fun _ hJt => by
          c0_hsplit <;> (c0_hsteps!; exact hJt _ trivial))
      rintro _ tlim _; c0_hsteps_nogrp
      let ks2 := (ks1.putHdr .tick_lim tlim).putHdr .status 0#32
      have hinv2 := k6SetStatus_preserves_inv (k6_inv_set_hdr_nc hinv1 .tick_lim (Or.inl rfl) tlim)
        0#32
      have hsync2 : K6TrailSynced ks2 := k6TrailSynced_cast hsync1
      have htl2 : K6TailEq L ks1 ks2 := k6TailEq_trans
        (k6TailEq_of_putHdr_ne_nv (L := L) (ks := ks1) (f := .tick_lim) (by decide) tlim)
        (k6TailEq_of_putHdr_ne_nv (L := L) (f := .status) (by decide) 0#32)
      have hframe2 : K6SolveFrame L ks0 ks2 := K6SolveFrame.trans hframe1 ⟨rfl, htl2, rfl, rfl, rfl⟩
      k6_call hProp
      refine ⟨L, P, ks2, FullK6Frame c L s ⋆ R, hinv2, hsync2, (k6MemA_to_mem hm).2,
        fun confl_p ks_p m_p hinv_p hsync_p hp_p htl_p hte_p hkept_p hnew_p _ hconfl_ne hm_p => ?_⟩
      have hm_p' : (K6Mem L kPtr ks_p ⋆ (FullK6Frame c L s ⋆ R)) m_p := hm_p; clear hm_p
      c0_hsplit
      · have hc_ne_ff : confl_p ≠ 0xFFFFFFFF#32 := ‹_›
        have hmA_p := k6Mem_to_amem hinv_p.shapes hm_p'; clear hm_p'; c0_hsteps!
        obtain ⟨hc_lt, hc_fals⟩ := hconfl_ne hc_ne_ff
        have huns := k6_conflict_unsat_lvl0 hinv_p (hp_p.lvl.trans hlvl1) hc_lt hc_fals
        have hframe_i := K6SolveFrame.trans hframe2
          ⟨by k6_field; exact hp_p.nv,
           k6TailEq_trans htl_p (k6TailEq_of_putHdr_ne_nv (f := .incons) (by decide) 1#32),
           by k6_field; exact hp_p.nassump, by k6_field; exact hp_p.assump,
           by k6_field; exact hp_p.neq⟩
        exact k6_solve_setStatus_finish hlen hL_scr hlen_L (k6SetIncons_preserves_inv hinv_p huns)
          (k6TrailSynced_cast hsync_p) (le_refl _) hframe_i
          (Or.inr (Or.inr rfl)) (fun _ β hP _ => huns β hP) hm hQ
      · have hc_ff : confl_p = 0xFFFFFFFF#32 := by
          first | exact ‹_› | exact Classical.not_not.mp ‹_›
        have hframe_p := K6SolveFrame.trans hframe2
          ⟨hp_p.nv, htl_p, hp_p.nassump, hp_p.assump, hp_p.neq⟩
        have hsi_p := k6_solveLoopInv_of_lvl0 hinv_p hsync_p (hp_p.lvl.trans hlvl1) hframe_p
        c0_hsteps_nogrp
        refine wp_while_state1 (t := i32) (fun st : BitVec 32 × K6State × BitVec 64 => st.1)
          (fun st => st.2.2.toNat)
          (fun st m_l => st.2.2.toNat ≤ s.core.fuel.toNat ∧
            K6SolveLoopInv L P ks0 st.2.1 st.1 ∧
            (K6MemA L kPtr st.2.1 ⋆
              (FullK6Frame c L { s with core := { s.core with fuel := st.2.2 } } ⋆ R)) m_l)
          ?_ ?_
        · intro Jm hJm; c0_hsteps!; rw [hc_ff]
          exact hJm (0xFFFFFFFF#32, ks_p, s.core.fuel) m_p
            ⟨le_refl _, hsi_p, k6Mem_to_amem hinv_p.shapes hm_p'⟩
        · rintro Jm ⟨confl_m, km, fuel_m⟩ m_l ⟨hfuel_m, hsi_m, hm_l⟩ ih_m
          dsimp only at hfuel_m hsi_m hm_l
          refine wp_join0 (fun mEx =>
            (K6MemA L kPtr km ⋆
              (FullK6Frame c L { s with core := { s.core with fuel := fuel_m } } ⋆ R)) mEx)
            ?_ ?_
          · intro _ mEx hmEx; c0_hsteps!
            exact k6_solve_setStatus_finish hlen hL_scr hlen_L hsi_m.inv hsi_m.sync hfuel_m
              hsi_m.frame (Or.inl rfl) (fun h => absurd h (by decide)) hm hQ
          · intro Jex hJex; c0_hsplit
            · c0_hsplit
              · have hfuel_pos : 0 < fuel_m.toNat := by bv_omega
                have hfuel_sub : (fuel_m - 1#64).toNat = fuel_m.toNat - 1 := by bv_omega
                let sFuel1 : FullState := { s with core := { s.core with fuel := fuel_m - 1#64 } }
                have hfuel_le1 : (fuel_m - 1#64).toNat ≤ s.core.fuel.toNat := by omega
                let PickInv := fun (p : BitVec 32) (mv : Mem 64) =>
                  (p = 0xFFFFFFFF#32 ∨
                    (p.toNat < km.nv.toNat ∧ km.vals[2 * p.toNat]?.getD 0#32 = 0#32)) ∧
                  (K6MemA L kPtr km ⋆ (FullK6Frame c L sFuel1 ⋆ R)) mv
                c0_hsplit
                · have hconfl_ne : confl_m ≠ 0xFFFFFFFF#32 := ‹_›
                  have hm_l1 : (K6MemA L kPtr km ⋆ (FullK6Frame c L sFuel1 ⋆ R)) m := by
                    simpa only [sFuel1] using sep_ac hm
                  clear hm; c0_hsplit
                  · have hlvl0_m : km.lvl = 0#32 := ‹_›; c0_hsteps!
                    obtain ⟨hc_lt, hc_fals⟩ := hsi_m.confl_ok hconfl_ne
                    have huns := k6_conflict_unsat_lvl0 hsi_m.inv hlvl0_m hc_lt hc_fals
                    have hframe_i : K6SolveFrame L ks0 (km.putHdr .incons 1#32) :=
                      K6SolveFrame.trans hsi_m.frame
                        ⟨rfl, k6TailEq_of_putHdr_ne_nv (f := .incons) (by decide) 1#32, rfl, rfl,
                        rfl⟩
                    exact k6_solve_setStatus_finish hlen hL_scr hlen_L
                      (k6SetIncons_preserves_inv hsi_m.inv huns) (k6TrailSynced_cast hsi_m.sync)
                      hfuel_le1 hframe_i (Or.inr (Or.inr rfl)) (fun _ β hP _ => huns β hP) hm hQ
                  · have hlvl_pos : 0 < km.lvl.toNat := by bv_omega
                    obtain ⟨hc_lt, hc_fals⟩ := hsi_m.confl_ok hconfl_ne
                    obtain ⟨iw, hiw, hiw_lvl⟩ := hsi_m.lvlne km.lvl.toNat hlvl_pos (le_refl _)
                    k6_call hAna
                    refine ⟨L, P, km, FullK6Frame c L sFuel1 ⋆ R, hsi_m.inv, hsi_m.sync,
                      hlvl_pos, ⟨iw, hiw, BitVec.eq_of_toNat_eq hiw_lvl⟩, hc_lt, hc_fals,
                      (k6MemA_to_mem hm_l1).2,
                      fun ok_a ks_a m_a hinv_a hsync_a e_nv htl_a e_na e_as _ _ e_nq hok_a
                        hm_a => ?_⟩
                    c0_hsplit
                    · have hok_t : ok_a = true := by cases ok_a <;> simp_all
                      obtain ⟨hlvl_lt, _, hdec_sub, hkept⟩ := hok_a hok_t
                      have hsi_a := k6_solveLoopInv_of_analyze hsi_m.inv hsi_m.frame hsi_m.lvlne
                        hsi_m.late hinv_a hsync_a e_nv htl_a e_na e_as e_nq hlvl_lt hdec_sub hkept
                      k6_call hProp
                      refine ⟨L, P, ks_a, FullK6Frame c L sFuel1 ⋆ R, hsi_a.inv, hsi_a.sync, hm_a,
                        fun confl_p2 ks_p2 m_p2 hinv_p2 hsync_p2 hp_p2 htl_p2 hte_p2 hkept_p2
                          hnew_p2 _ hc_ne2 hm_p2 => ?_⟩
                      c0_hsteps!
                      exact ih_m (confl_p2, ks_p2, fuel_m - 1#64) _ (by dsimp only; omega)
                        ⟨hfuel_le1, k6_solveLoopInv_of_propagate hsi_a.inv hsi_a.frame hsi_a.lvlne
                          hsi_a.late hinv_p2 hsync_p2 hp_p2 htl_p2 hte_p2 hkept_p2 hnew_p2 hc_ne2,
                         k6Mem_to_amem hinv_p2.shapes hm_p2⟩
                    · have hmA_a := k6Mem_to_amem hinv_a.shapes hm_a; clear hm_a; c0_hsteps!
                      exact k6_solve_setStatus_finish hlen hL_scr hlen_L hinv_a hsync_a hfuel_le1
                        (K6SolveFrame.trans hsi_m.frame ⟨e_nv, htl_a, e_na, e_as, e_nq⟩)
                        (Or.inl rfl) (fun h => absurd h (by decide)) hm hQ
                · have hconfl_ff : confl_m = 0xFFFFFFFF#32 := by
                    first | exact ‹_› | exact Classical.not_not.mp ‹_›
                  have hm_l1 : (K6MemA L kPtr km ⋆ (FullK6Frame c L sFuel1 ⋆ R)) m := by
                    simpa only [sFuel1] using sep_ac hm
                  clear hm; c0_hsteps_nogrp
                  refine wp_while_break_state (β := BitVec 32 × BitVec 32 × Bool × K6State)
                    (fun bst => ((bst.1, bst.2.1, bst.2.2.1, ()) : Tup Val [i32, i32, .bool]))
                    (fun bst m_b =>
                      (bst.2.2.1 = false → bst.1 = 0xFFFFFFFF#32 ∧ bst.2.2.2 = km ∧
                        ∀ j < km.nassump.toNat,
                          km.vals[(km.assump[j]?.getD 0#32).toNat]? = some 1#32) ∧
                      (bst.2.2.1 = true → K6SolveLoopInv L P ks0 bst.2.2.2 bst.1) ∧
                      (K6MemA L kPtr bst.2.2.2 ⋆ (FullK6Frame c L sFuel1 ⋆ R)) m_b)
                    (α := BitVec 32) (fun st => ((st, ()) : Tup Val [i32]))
                    (fun st => km.nassump.toNat - st.toNat)
                    (fun st m_b => st.toNat ≤ km.nassump.toNat ∧
                      (∀ j < st.toNat, km.vals[(km.assump[j]?.getD 0#32).toNat]? = some 1#32) ∧
                      (K6MemA L kPtr km ⋆ (FullK6Frame c L sFuel1 ⋆ R)) m_b) ?_ ?_ ?_
                  · rintro B ⟨confl_b, ad_b, did_b, ks_b⟩ m_b ⟨hf_b, ht_b, hm_b⟩
                    dsimp only at hf_b ht_b hm_b; c0_hsplit
                    · have hdid_t : did_b = true := ‹_›; c0_hsteps!
                      exact ih_m (confl_b, ks_b, fuel_m - 1#64) _ (by dsimp only; omega)
                        ⟨hfuel_le1, ht_b hdid_t, hm_b⟩
                    · have hdid_f : did_b = false := by cases did_b <;> simp_all
                      obtain ⟨_, hks_b_eq, hall_ass_j⟩ := hf_b hdid_f; subst ks_b
                      have hall_ass_mem : ∀ a ∈ k6AssumpLits km, km.vals[a]? = some 1#32 := by
                        intro a ha
                        simp only [k6AssumpLits, List.mem_map, List.mem_take_iff_getElem] at ha
                        obtain ⟨ab, ⟨ia, hia, rfl⟩, rfl⟩ := ha
                        have hlen_a : km.nassump.toNat ≤ km.assump.length := by
                          rw [hsi_m.inv.shapes.assump_len]; exact hsi_m.inv.clauses.nassump_le
                        have hget := hall_ass_j ia (by omega)
                        rwa [List.getElem?_eq_getElem (by omega : ia < km.assump.length),
                          Option.getD_some] at hget
                      c0_hsplit
                      · c0_hsteps!
                        exact k6_solve_setStatus_finish hlen hL_scr hlen_L hsi_m.inv hsi_m.sync
                          hfuel_le1 hsi_m.frame (Or.inr (Or.inl rfl))
                          (fun h => absurd h (by decide)) hm hQ
                      · have hnv_m := hsi_m.inv.clauses.nv_le; c0_hsteps_nogrp
                        refine wp_while_break_state (β := BitVec 32 × BitVec 32 × BitVec 32)
                          (fun bst => (bst.1, bst.2.1, bst.2.2, ()))
                          (fun bst m_v => PickInv bst.2.1 m_v)
                          (α := BitVec 32 × BitVec 32) (fun st => (st.1, st.2, ()))
                          (fun st => km.nv.toNat - st.2.toNat)
                          (fun st m_v => st.2.toNat ≤ km.nv.toNat ∧
                            (K6MemA L kPtr km ⋆ (FullK6Frame c L sFuel1 ⋆ R)) m_v) ?_ ?_ ?_
                        · rintro B1 ⟨_c1, pick1, _s1⟩ m_v1 hp1; dsimp only at hp1
                          refine wp_join_state
                            (proj := fun p : BitVec 32 × BitVec 32 × BitVec 32 =>
                              (p.1, p.2.1, p.2.2, ()))
                            (fun p m_v2 => PickInv p.2.1 m_v2) ?_ ?_
                          · intro J2 ⟨_c2, pick2, _s2⟩ m_v2 hp2; dsimp only at hp2
                            refine wp_join_state
                              (proj := fun p : BitVec 32 × BitVec 32 => (p.1, p.2, ()))
                              (fun p m_v3 => PickInv p.2 m_v3) ?_ ?_
                            · intro J3 ⟨_c3, pick3⟩ m_v3 ⟨hpick3, hm_v3⟩
                              dsimp only at hpick3 hm_v3; c0_hsplit
                              · c0_hsteps!
                                exact k6_solve_setStatus_finish hlen hL_scr hlen_L hsi_m.inv
                                  hsi_m.sync hfuel_le1 hsi_m.frame (Or.inr (Or.inl rfl))
                                  (fun h => absurd h (by decide)) hm hQ
                              · have hpk_ne : pick3 ≠ 0xFFFFFFFF#32 := ‹_›
                                rcases hpick3 with rfl | ⟨hpk_lt, hpk_val⟩
                                · exact absurd rfl hpk_ne
                                have hpk_mv : pick3.toNat < szV L := by unfold szV; omega
                                let ks_q := km.putHdr .qsearch pick3
                                let ph : BitVec 32 :=
                                  (ks_q.flags[pick3.toNat]?.getD 0#32 ^^^ ks_q.phase) &&& 1#32
                                let lit_d := (pick3 <<< (1 : Nat)) ||| ph
                                let ks_l := ks_q.putHdr .lvl (ks_q.lvl + 1#32)
                                obtain ⟨hlit_mv, hte_lt, hinv_d, hsync_d, hframe_d, hlvlne_d,
                                  hlate_d⟩ := k6_solve_decide_prep hsi_m.inv hsi_m.sync hsi_m.frame
                                    hsi_m.lvlne hsi_m.late hpk_lt hpk_val hall_ass_mem
                                c0_hsteps_nogrp; k6_call hAsg
                                refine ⟨L, ks_l, FullK6Frame c L sFuel1 ⋆ R,
                                  hsi_m.inv.shapes.putHdr .qsearch pick3 |>.putHdr .lvl _,
                                  by dsimp only [ks_l, ks_q, K6State.putHdr]
                                     exact hsi_m.inv.clauses.max_v_eq, hlit_mv,
                                  Nat.lt_of_lt_of_le hte_lt hnv_m, (k6MemA_to_mem hm).2,
                                  fun mA hmA => ?_⟩
                                k6_call hProp
                                refine ⟨L, P, k6AssignStep ks_l lit_d 0xFFFFFFFF#32,
                                  FullK6Frame c L sFuel1 ⋆ R, hinv_d, hsync_d, hmA,
                                  fun confl_p2 ks_p2 m_p2 hinv_p2 hsync_p2 hp_p2 htl_p2 hte_p2
                                    hkept_p2 hnew_p2 _ hc_ne2 hm_p2 => ?_⟩
                                c0_hsteps!; exact ih_m (confl_p2, ks_p2, fuel_m - 1#64) _
                                  (by dsimp only; omega)
                                  ⟨hfuel_le1, k6_solveLoopInv_of_propagate hinv_d hframe_d
                                    hlvlne_d hlate_d hinv_p2 hsync_p2 hp_p2 htl_p2 hte_p2 hkept_p2
                                    hnew_p2 hc_ne2, k6Mem_to_amem hinv_p2.shapes hm_p2⟩
                            · intro J3 hJ3; c0_hsplit
                              · c0_hsteps_nogrp
                                refine wp_while_break_state (β := BitVec 32 × BitVec 32)
                                  (fun bst => (bst.1, bst.2, ())) (fun bst m_v => PickInv bst.2 m_v)
                                  (α := BitVec 32) (fun st => (st, ()))
                                  (fun st => km.nv.toNat - st.toNat)
                                  (fun st m_v => st.toNat ≤ km.nv.toNat ∧
                                    (K6MemA L kPtr km ⋆ (FullK6Frame c L sFuel1 ⋆ R)) m_v) ?_ ?_ ?_
                                · rintro B3 ⟨c3, p3⟩ m_v3 hp3
                                  exact wp_jump_state (proj :=
                                    fun p : BitVec 32 × BitVec 32 => (p.1, p.2, ()))
                                    (c3, p3) rfl (hJ3 (c3, p3) m_v3 hp3)
                                · rintro B3 L3 c3 m_v3 hB3 hL3 ⟨hc3_le, hm_v3⟩; c0_hsplit
                                  · have hc3_lt : c3.toNat < km.nv.toNat := by bv_omega
                                    obtain ⟨hc3_shl, hc3_sz2V, _⟩ :=
                                      k6_solve_pick_bounds hmL.2 hnv_m hc3_lt
                                    have hc3_1 : (c3 + 1#32).toNat = c3.toNat + 1 := by bv_omega
                                    c0_hsplit
                                    · c0_hsteps!
                                      exact hB3 (c3, c3) m_v3 ⟨Or.inr ⟨hc3_lt, by rwa [← hc3_shl]⟩,
                                        hm_v3⟩
                                    · c0_hsteps!; exact hL3 (c3 + 1#32) m_v3 (by rw [hc3_1]; omega)
                                        ⟨by rw [hc3_1]; omega, hm_v3⟩
                                  · dsimp only [PickInv] at hp2
                                    c0_hsteps!; exact hB3 (c3, pick2) m_v3 ⟨hp2.1, hm_v3⟩
                                · intro B3 L3 _ hL3
                                  dsimp only [PickInv] at hp2
                                  exact wp_jump_state (proj := fun st : BitVec 32 => (st, ()))
                                    0#32 rfl (hL3 0#32 m_v2 ⟨by simp, hp2.2⟩)
                              · exact wp_jump_state (proj :=
                                    fun p : BitVec 32 × BitVec 32 => (p.1, p.2, ()))
                                  (_c2, pick2) rfl (hJ3 (_c2, pick2) m_v2 hp2)
                          · intro J2 hJ2; c0_hsplit
                            · dsimp only [PickInv] at hp1
                              have hmL2 := hmL.2; let ql := km.qlast; have hm_v1 := hp1.2
                              c0_hsteps_nogrp
                              k6_solve_qlist_pick PickInv hJ2 km hmL2 hnv_m ql hm_v1 pick1 hp1
                            · exact wp_jump_state (proj := fun p : BitVec 32 × BitVec 32 ×
                                  BitVec 32 => (p.1, p.2.1, p.2.2, ()))
                                (_c1, pick1, _s1) rfl (hJ2 (_c1, pick1, _s1) m_v1 hp1)
                        · rintro B1 L1 ⟨c1, s1⟩ m_v1 hB1 hL1 ⟨hs1_le, hm_v1⟩; c0_hsplit
                          · c0_hsplit
                            · have hc1_lt : c1.toNat < km.nv.toNat := by bv_omega
                              have hs1_lt : s1.toNat < km.nv.toNat := by bv_omega
                              obtain ⟨hc1_shl, _, _⟩ := k6_solve_pick_bounds hmL.2 hnv_m hc1_lt
                              have hs1_1 : (s1 + 1#32).toNat = s1.toNat + 1 := by bv_omega
                              c0_hsplit
                              · c0_hsteps!; exact hB1 (c1, c1, s1) m_v1
                                  ⟨Or.inr ⟨hc1_lt, by rwa [← hc1_shl]⟩, hm_v1⟩
                              · c0_hsteps!
                                exact hL1 (km.qprev[c1.toNat]?.getD 0#32, s1 + 1#32) m_v1
                                  (by dsimp only; rw [hs1_1]; omega)
                                  ⟨by dsimp only; rw [hs1_1]; omega, hm_v1⟩
                            · exact hB1 (c1, 0xFFFFFFFF#32, s1) m_v1 ⟨Or.inl rfl, hm_v1⟩
                          · exact hB1 (c1, 0xFFFFFFFF#32, s1) m_v1 ⟨Or.inl rfl, hm_v1⟩
                        · intro B1 L1 _ hL1
                          exact wp_jump_state
                            (proj := fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ()))
                            (km.qsearch, 0#32) rfl (hL1 _ _ ⟨by simp, hm_b⟩)
                  · rintro B0 L0 ad_a m_a hB0 hL0 ⟨had_le, hall_j, hm_a⟩; c0_hsplit
                    · have had_lt : ad_a.toNat < km.nassump.toNat := by bv_omega
                      have hna_le := hsi_m.inv.clauses.nassump_le
                      have hnv_m := hsi_m.inv.clauses.nv_le
                      have had_mv : ad_a.toNat < szV L := by unfold szV; omega
                      have had_1 : (ad_a + 1#32).toNat = ad_a.toNat + 1 := by bv_omega
                      let alit := km.assump[ad_a.toNat]?.getD 0#32
                      have halit_lt : alit.toNat < 2 * km.nv.toNat :=
                        hsi_m.inv.clauses.assump_ok ad_a.toNat had_lt
                      have halit_sz2V : alit.toNat < sz2V L := by unfold sz2V; omega
                      have hlen_a : km.nassump.toNat ≤ km.assump.length := by
                        rw [hsi_m.inv.shapes.assump_len]; exact hna_le
                      have halit_mem := k6_mem_assumpLits_of_lt hlen_a had_lt
                      c0_hsplit
                      · have hav2' := k6_vals_some hsi_m.inv.shapes halit_sz2V ‹_›
                        c0_hsteps!
                        exact k6_solve_setStatus_finish hlen hL_scr hlen_L hsi_m.inv hsi_m.sync
                          hfuel_le1 hsi_m.frame (Or.inr (Or.inr rfl))
                          (fun _ β hP hsat => k6_allDecisionsInAssumps_of_late hsi_m.inv
                            hsi_m.sync hsi_m.late had_lt hav2' β hP hsat) hm hQ
                      · c0_hsplit
                        · have hav0 : km.vals[alit.toNat]?.getD 0#32 = 0#32 := ‹_›
                          have halit_0 := k6_vals_some hsi_m.inv.shapes halit_sz2V hav0
                          have hte_lt := k6_trl_end_lt_of_unassigned hsi_m.inv.shapes hnv_m
                            hsi_m.inv.assign halit_lt hav0
                          let km_l := km.putHdr .lvl (km.lvl + 1#32)
                          c0_hsteps_nogrp; k6_call hAsg
                          refine ⟨L, km_l, FullK6Frame c L sFuel1 ⋆ R,
                            hsi_m.inv.shapes.putHdr .lvl _, hsi_m.inv.clauses.max_v_eq,
                            Nat.lt_of_lt_of_le halit_lt (Nat.mul_le_mul_left 2 hnv_m),
                            Nat.lt_of_lt_of_le hte_lt hnv_m, (k6MemA_to_mem hm).2, fun mA hmA => ?_⟩
                          obtain ⟨hinv_d, hsync_d, hframe_d, hlvlne_d, hlate_d⟩ :=
                            k6_decide_step_preserves hsi_m.inv hsi_m.sync hsi_m.frame hsi_m.lvlne
                              hsi_m.late halit_lt halit_0 (fun hnot => absurd halit_mem hnot)
                          k6_call hProp
                          refine ⟨L, P, k6AssignStep km_l alit 0xFFFFFFFF#32,
                            FullK6Frame c L sFuel1 ⋆ R, hinv_d, hsync_d, hmA,
                            fun confl_p2 ks_p2 m_p2 hinv_p2 hsync_p2 hp_p2 htl_p2 hte_p2 hkept_p2
                              hnew_p2 _ hc_ne2 hm_p2 => ?_⟩
                          c0_hsteps!
                          exact hB0 (confl_p2, ad_a, true, ks_p2) m_p2
                            ⟨(fun h => by dsimp only at h; cases h),
                             fun _ => k6_solveLoopInv_of_propagate hinv_d hframe_d hlvlne_d hlate_d
                               hinv_p2 hsync_p2 hp_p2 htl_p2 hte_p2 hkept_p2 hnew_p2 hc_ne2,
                             k6Mem_to_amem hinv_p2.shapes hm_p2⟩
                        · have hne2 : km.vals[alit.toNat]?.getD 0#32 ≠ 2#32 := ‹_›
                          have hne0 : km.vals[alit.toNat]?.getD 0#32 ≠ 0#32 := ‹_›
                          have hav1 : km.vals[alit.toNat]?.getD 0#32 = 1#32 := by
                            rcases hsi_m.inv.assign.vals_dom alit.toNat halit_lt with h0 | h1 | h2
                            · exact absurd h0 hne0
                            · exact h1
                            · exact absurd h2 hne2
                          have hav1' := k6_vals_some hsi_m.inv.shapes halit_sz2V hav1
                          c0_hsteps!
                          refine hL0 (ad_a + 1#32) m_a (by rw [had_1]; omega)
                            ⟨by rw [had_1]; exact had_lt, fun j hj => by
                              rw [had_1] at hj; by_cases hja : j = ad_a.toNat
                              · subst hja; exact hav1'
                              · exact hall_j j (by omega), hm_a⟩
                    · exact hB0 (confl_m, ad_a, false, km) m_a
                        ⟨fun _ => ⟨hconfl_ff, rfl, fun j hj => by
                          have heq : ad_a.toNat = km.nassump.toNat := by bv_omega
                          rw [← heq] at hj; exact hall_j j hj⟩,
                         (fun h => by dsimp only at h; cases h), hm_a⟩
                  · intro _ L0 _ hL0
                    exact wp_jump_state (proj := fun st : BitVec 32 => (st, ())) 0#32 rfl
                      (hL0 0#32 m ⟨by simp, fun _ hj => by simp at hj, hm_l1⟩)
              · c0_hsteps!; exact hJex _ ‹_›
            · c0_hsteps!; exact hJex _ ‹_›

end LeanQbe.T.Examples.Kissat.Proof.Kitten
end
