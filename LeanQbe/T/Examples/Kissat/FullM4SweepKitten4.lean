module

public import LeanQbe.T.Examples.Kissat.FullM4SweepKitten3

/-!
# Kissat M4b 512-Var `kitten` CDCL Solve `Func.wp` Proof (`Part 4`, `1/24`)

Proves the final `full_k512_*` parametric `(Γ : Env)` `Func.wp` contract (`12/24`),
completing all `12/12` 512-var `kitten` proofs:
- `12/24`: `full_k512_solve_wp`
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4Sweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

open scoped K512MemATactics

/-! ## 3. Solve Loop Invariants & `full_k512_solve_wp` (`12/24`) -/

/-- Every positive decision level `1 .. ks.lvl` is inhabited on `trl`. -/
def K512LvlNonempty (ks : K512State) : Prop :=
  ∀ L, 0 < L → L ≤ ks.lvl.toNat →
    ∃ i < ks.trl_end.toNat, (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = L

/-- Every positive-level non-assumption decision sits strictly after all assumptions on `trl`. -/
def K512FreeDecLate (ks : K512State) : Prop :=
  ∀ p < ks.trl_end.toNat,
    0 < (ks.lvlArr[(ks.trl[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat →
    ks.rsn[(ks.trl[p]?.getD 0#32).toNat / 2]?.getD 0#32 = 0xFFFFFFFF#32 →
    (ks.trl[p]?.getD 0#32).toNat ∉ k5AssumpLits ks →
    ∀ a ∈ k5AssumpLits ks, ∃ q < p, (ks.trl[q]?.getD 0#32).toNat = a

private structure K5SolveFrame (ks0 ks : K512State) : Prop where
  nv : ks.nv = ks0.nv
  nassump : ks.nassump = ks0.nassump
  assump : ks.assump = ks0.assump

private theorem K5SolveFrame.trans {ks0 ks1 ks2 : K512State}
    (h1 : K5SolveFrame ks0 ks1) (h2 : K5SolveFrame ks1 ks2) : K5SolveFrame ks0 ks2 :=
  ⟨h2.nv.trans h1.nv, h2.nassump.trans h1.nassump, h2.assump.trans h1.assump⟩

private structure K5SolveLoopInv (acap : Nat) (P : (Nat → Bool) → Prop)
    (ks0 ks : K512State) (confl : BitVec 32) : Prop where
  inv : K512Inv acap P ks
  sync : K512TrailSynced ks
  frame : K5SolveFrame ks0 ks
  lvlne : K512LvlNonempty ks
  late : K512FreeDecLate ks
  confl_ok : confl ≠ 0xFFFFFFFF#32 →
    confl.toNat < ks.nc.toNat ∧ ∀ l ∈ k5ClauseLits ks confl.toNat, ks.vals[l]? = some 2#32

private theorem k5_lvl_le_trl_end {acap : Nat} {P : (Nat → Bool) → Prop} {ks : K512State}
    (hinv : K512Inv acap P ks) (hne : K512LvlNonempty ks) : ks.lvl.toNat ≤ ks.trl_end.toNat := by
  have hstep : ∀ L, L ≤ ks.lvl.toNat → 0 < L →
      ∃ i < ks.trl_end.toNat, L - 1 ≤ i ∧
        (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = L := by
    intro L; induction L with
    | zero => intro _ hz; omega
    | succ L ih =>
      intro hle _
      obtain ⟨i, hi, hiv⟩ := hne (L + 1) (Nat.succ_pos L) hle
      by_cases hL0 : L = 0
      · subst hL0; exact ⟨i, hi, Nat.zero_le _, hiv⟩
      · obtain ⟨j, hj, hj_le, hjv⟩ := ih (by omega) (Nat.pos_of_ne_zero hL0)
        refine ⟨i, hi, ?_, hiv⟩
        by_cases hlt : L ≤ i
        · omega
        · exfalso; have hm := hinv.assign.trl_lvl_mono i j (by omega) hj; rw [hiv, hjv] at hm; omega
  by_cases hl0 : ks.lvl.toNat = 0
  · rw [hl0]; exact Nat.zero_le _
  · obtain ⟨i, hi, hle, _⟩ := hstep ks.lvl.toNat (Nat.le_refl _) (Nat.pos_of_ne_zero hl0); omega

private theorem k5_vals_some_zero {acap : Nat} {P : (Nat → Bool) → Prop} {ks : K512State}
    (hinv : K512Inv acap P ks) {l : Nat} (hl : l < 2 * ks.nv.toNat)
    (hz : ks.vals[l]?.getD 0#32 = 0#32) : ks.vals[l]? = some 0#32 := by
  have hnv := hinv.clauses.nv_le
  have hlen : l < ks.vals.length := by rw [hinv.shapes.vals_len]; unfold k5MaxV at hnv; omega
  rw [List.getElem?_eq_getElem hlen, Option.getD_some] at hz
  rw [List.getElem?_eq_getElem hlen, hz]

private theorem k5_inv_set_tick_lim {acap : Nat} {P : (Nat → Bool) → Prop} {ks : K512State}
    (hinv : K512Inv acap P ks) (v : BitVec 32) : K512Inv acap P (ks.putHdr .tick_lim v) :=
  ⟨hinv.shapes.putHdr .tick_lim v,
   ⟨hinv.clauses.acap_ge, hinv.clauses.acap_lt, hinv.clauses.acap_eq, hinv.clauses.nv_le,
    hinv.clauses.nc_le, hinv.clauses.alen_le, hinv.clauses.nassump_le, hinv.clauses.nkl_le,
    hinv.clauses.nana_le, hinv.clauses.cl_wf, hinv.clauses.cl_mono, hinv.clauses.incons_ok,
    hinv.clauses.assump_ok, hinv.clauses.flags_clean⟩,
   hinv.watches, k5a_baseAssign_of_eq hinv.assign, hinv.reasons⟩

private theorem k5_inv_set_qsearch {acap : Nat} {P : (Nat → Bool) → Prop} {ks : K512State}
    (hinv : K512Inv acap P ks) (v : BitVec 32) : K512Inv acap P (ks.putHdr .qsearch v) :=
  k5SetQueue_preserves_inv hinv hinv.shapes.qprev_len hinv.shapes.qnext_len
    hinv.shapes.qstampArr_len

private theorem k5_mem_assumpLits_of_lt {ks : K512State}
    (hlen : ks.nassump.toNat ≤ ks.assump.length) {i : Nat} (hi : i < ks.nassump.toNat) :
    (ks.assump[i]?.getD 0#32).toNat ∈ k5AssumpLits ks := by
  unfold k5AssumpLits; rw [List.mem_map]
  refine ⟨ks.assump[i]?.getD 0#32, ?_, rfl⟩
  rw [List.mem_take_iff_getElem]
  exact ⟨i, by omega, by simp [List.getElem?_eq_getElem (by omega : i < ks.assump.length)]⟩

private theorem k5_trl_idx_eq_of_val {acap : Nat} {P : (Nat → Bool) → Prop} {ks : K512State}
    (hinv : K512Inv acap P ks) {p q : Nat} (hp : p < ks.trl_end.toNat) (hq : q < ks.trl_end.toNat)
    (heq : (ks.trl[p]?.getD 0#32).toNat = (ks.trl[q]?.getD 0#32).toNat) : p = q := by
  by_cases hpq : p = q
  · exact hpq
  · exfalso
    exact k5_trl_nodup_var_ne hinv.shapes hinv.clauses.nv_le hinv.assign hp hq hpq
      (congrArg (· / 2) heq)

private theorem k5_decide_step_preserves {acap : Nat} {P : (Nat → Bool) → Prop}
    {ks0 ks : K512State} (hinv : K512Inv acap P ks) (hsync : K512TrailSynced ks)
    (hframe : K5SolveFrame ks0 ks) (hlvlne : K512LvlNonempty ks) (hlate : K512FreeDecLate ks)
    {lit : BitVec 32} (hlit : lit.toNat < 2 * ks.nv.toNat) (hun : ks.vals[lit.toNat]? = some 0#32)
    (hall_ass : lit.toNat ∉ k5AssumpLits ks → ∀ a ∈ k5AssumpLits ks, ks.vals[a]? = some 1#32) :
    let ks1 := ks.putHdr .lvl (ks.lvl + 1#32)
    let ks' := k5AssignStep ks1 lit 0xFFFFFFFF#32
    K512Inv acap P ks' ∧ K512TrailSynced ks' ∧ K5SolveFrame ks0 ks' ∧
    K512LvlNonempty ks' ∧ K512FreeDecLate ks' := by
  intro ks1 ks'
  have hnv := hinv.clauses.nv_le; have hle_te := k5_lvl_le_trl_end hinv hlvlne
  have hte_le := hinv.assign.trl_end_le
  have hlvl1_nat : (ks.lvl + 1#32).toNat = ks.lvl.toNat + 1 := by unfold k5MaxV at hnv; bv_omega
  have hlvl1_ne0 : ks.lvl + 1#32 ≠ 0#32 := fun h => by
    have := congrArg BitVec.toNat h; rw [hlvl1_nat] at this; simp at this
  have hinv1 : K512Inv acap P ks1 :=
    ⟨hinv.shapes.putHdr .lvl (ks.lvl + 1#32),
     ⟨hinv.clauses.acap_ge, hinv.clauses.acap_lt, hinv.clauses.acap_eq, hinv.clauses.nv_le,
      hinv.clauses.nc_le, hinv.clauses.alen_le, hinv.clauses.nassump_le, hinv.clauses.nkl_le,
      hinv.clauses.nana_le, hinv.clauses.cl_wf, hinv.clauses.cl_mono, hinv.clauses.incons_ok,
      hinv.clauses.assump_ok, hinv.clauses.flags_clean⟩,
     hinv.watches,
     { hinv.assign with
       trl_lvl_le := fun v hv => by
         change (ks.lvlArr[v]?.getD 0#32).toNat ≤ (ks.lvl + 1#32).toNat
         rw [hlvl1_nat]; have := hinv.assign.trl_lvl_le v hv; omega },
     hinv.reasons⟩
  have hdec1 : ∀ i < ks1.trl_end.toNat,
      ks1.lvlArr[(ks1.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 ≠ ks1.lvl := by
    intro i hi heq
    have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
      rw [hinv.shapes.trl_len]; unfold k5MaxV at hnv; omega
    have hli := hinv.assign.trl_lt _ (k5_mem_trailLits_of_lt hi htrl_len)
    have hle := hinv.assign.trl_lvl_le ((ks.trl[i]?.getD 0#32).toNat / 2) (by omega)
    have hcon := congrArg BitVec.toNat heq
    change (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
      (ks.lvl + 1#32).toNat at hcon
    rw [hlvl1_nat] at hcon; omega
  obtain ⟨hinv', hsync'⟩ := k5AssignStep_preserves_inv hinv1 hsync hlit hun
    (fun h => absurd h hlvl1_ne0) (fun _ _ => hdec1) (Or.inl rfl)
  have hte_lt := k5_trl_end_lt_of_unassigned hinv.shapes hnv hinv.assign hlit (by simp [hun])
  have e_te : ks'.trl_end.toNat = ks.trl_end.toNat + 1 := by
    dsimp only [ks', k5AssignStep, ks1, K512State.putHdr]; unfold k5MaxV at hnv; bv_omega
  have e_trl_lt : ∀ i < ks.trl_end.toNat, ks'.trl[i]? = ks.trl[i]? := fun i hi => by
    dsimp only [ks', k5AssignStep, ks1, K512State.putHdr]; exact List.getElem?_set_ne (by omega)
  have e_trl_end : ks'.trl[ks.trl_end.toNat]? = some lit := by
    dsimp only [ks', k5AssignStep, ks1, K512State.putHdr]
    exact List.getElem?_set_self (by rw [hinv.shapes.trl_len]; unfold k5MaxV at hnv; omega)
  have e_lvl_v : ks'.lvlArr[lit.toNat / 2]? = some (ks.lvl + 1#32) := by
    dsimp only [ks', k5AssignStep, ks1, K512State.putHdr]
    rw [(k5_bv32_div2_lt hlit).1]
    exact List.getElem?_set_self (by rw [hinv.shapes.lvlArr_len]; unfold k5MaxV at hnv; omega)
  have hnot_trl : ∀ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := by
    intro i hi heq; have hnz := (hinv.assign.vals_nz_iff_trl lit.toNat hlit).mpr ⟨i, hi, heq⟩
    simp [hun] at hnz
  have e_lvl_other : ∀ v, v ≠ lit.toNat / 2 → ks'.lvlArr[v]? = ks.lvlArr[v]? := fun v hne => by
    dsimp only [ks', k5AssignStep, ks1, K512State.putHdr]
    rw [(k5_bv32_div2_lt hlit).1]; exact List.getElem?_set_ne hne.symm
  have e_rsn_other : ∀ v, v ≠ lit.toNat / 2 → ks'.rsn[v]? = ks.rsn[v]? := fun v hne => by
    dsimp only [ks', k5AssignStep, ks1, K512State.putHdr]
    rw [(k5_bv32_div2_lt hlit).1]; exact List.getElem?_set_ne hne.symm
  have hlvlne' : K512LvlNonempty ks' := by
    intro L hL0 hLle; change L ≤ (ks.lvl + 1#32).toNat at hLle; rw [hlvl1_nat] at hLle
    by_cases htop : L = ks.lvl.toNat + 1
    · subst htop; refine ⟨ks.trl_end.toNat, by rw [e_te]; omega, ?_⟩
      rw [e_trl_end, Option.getD_some, e_lvl_v, Option.getD_some, hlvl1_nat]
    · obtain ⟨i, hi, hiv⟩ := hlvlne L hL0 (by omega)
      refine ⟨i, by rw [e_te]; omega, ?_⟩
      rw [e_trl_lt i hi, e_lvl_other _ (hnot_trl i hi)]; exact hiv
  have hlate' : K512FreeDecLate ks' := by
    intro p hp hpos hrsn hnot a ha; rw [e_te] at hp; change a ∈ k5AssumpLits ks at ha
    by_cases hpe : p = ks.trl_end.toNat
    · subst hpe; rw [e_trl_end, Option.getD_some] at hnot
      have ha_val := hall_ass hnot a ha
      have ha_lt : a < 2 * ks.nv.toNat := by
        simp only [k5AssumpLits, List.mem_map] at ha; obtain ⟨ab, hab, rfl⟩ := ha
        rw [List.mem_take_iff_getElem] at hab; obtain ⟨ia, hia, rfl⟩ := hab
        have hlen : ks.nassump.toNat ≤ ks.assump.length := by
          rw [hinv.shapes.assump_len]; exact hinv.clauses.nassump_le
        have := hinv.clauses.assump_ok ia (by omega)
        rwa [List.getElem?_eq_getElem (by omega : ia < ks.assump.length), Option.getD_some] at this
      obtain ⟨q, hq, hqv⟩ := (hinv.assign.vals_nz_iff_trl a ha_lt).mp (by simp [ha_val])
      have hsy_q := hsync q hq; let lq := (ks.trl[q]?.getD 0#32).toNat
      have ha_eq : lq = a := by
        rcases (litVar_eq_iff lq a).mp (by simpa [litVar] using hqv) with heq | heq
        · exact heq
        · exfalso; have hx : lq ^^^ 1 = a := by rw [heq, ← k5_litNeg_eq_xor1, k5_nat_xor1_xor1]
          dsimp only at hsy_q; rw [← hx] at ha_val; dsimp only [lq] at ha_val
          rw [ha_val] at hsy_q; cases hsy_q.2
      exact ⟨q, hq, by rw [e_trl_lt q hq]; exact ha_eq⟩
    · have hp' : p < ks.trl_end.toNat := by omega
      rw [e_trl_lt p hp'] at hpos hrsn hnot
      rw [e_lvl_other _ (hnot_trl p hp')] at hpos; rw [e_rsn_other _ (hnot_trl p hp')] at hrsn
      obtain ⟨q, hqp, hqa⟩ := hlate p hp' hpos hrsn hnot a ha
      exact ⟨q, hqp, by rw [e_trl_lt q (by omega)]; exact hqa⟩
  exact ⟨hinv', hsync', K5SolveFrame.trans hframe ⟨rfl, rfl, rfl⟩, hlvlne', hlate'⟩

private theorem k5_allDecisionsInAssumps_of_late {acap : Nat} {P : (Nat → Bool) → Prop}
    {ks : K512State} (hinv : K512Inv acap P ks) (hsync : K512TrailSynced ks)
    (hlate : K512FreeDecLate ks) {ia : Nat} (hia : ia < ks.nassump.toNat)
    (hfals : ks.vals[(ks.assump[ia]?.getD 0#32).toNat]? = some 2#32) :
    ∀ β, P β → ¬ (unitsCnf (k5AssumpLits ks)).Sat β := by
  have hlen_a : ks.nassump.toNat ≤ ks.assump.length := by
    rw [hinv.shapes.assump_len]; exact hinv.clauses.nassump_le
  have ha_mem := k5_mem_assumpLits_of_lt hlen_a hia
  have hdec : ∀ d ∈ k5TrailDecisions ks, d ∈ k5AssumpLits ks := by
    intro d hd; by_cases hd_mem : d ∈ k5AssumpLits ks
    · exact hd_mem
    · exfalso; have hnv := hinv.clauses.nv_le
      have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
        rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; unfold k5MaxV at hnv; omega
      obtain ⟨p, hp, rfl, hpos, hrsn⟩ := (k5_mem_trailDecisions_iff htrl_len).mp hd
      obtain ⟨q, hq, hqa⟩ := hlate p hp hpos hrsn hd_mem _ ha_mem
      have hsy := hsync q (Nat.lt_trans hq hp); dsimp only at hsy
      rw [hqa, hfals] at hsy; cases hsy.1
  exact k5_falsified_assump_unsat hinv hsync hdec hia hfals

private theorem k5_solveLoopInv_of_propagate {acap : Nat} {P : (Nat → Bool) → Prop}
    {ks0 ks ks' : K512State} {confl : BitVec 32} (_hinv : K512Inv acap P ks)
    (hframe : K5SolveFrame ks0 ks) (hlvlne : K512LvlNonempty ks) (hlate : K512FreeDecLate ks)
    (hinv' : K512Inv acap P ks') (hsync' : K512TrailSynced ks') (hp : K5PropPreserved ks ks')
    (hte_le : ks.trl_end.toNat ≤ ks'.trl_end.toNat)
    (htrl_kept : ∀ i < ks.trl_end.toNat, ks'.trl[i]? = ks.trl[i]? ∧
      ks'.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? =
        ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? ∧
      ks'.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]? =
        ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?)
    (hnew : ∀ i, ks.trl_end.toNat ≤ i → i < ks'.trl_end.toNat →
      ks'.lvlArr[(ks'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = ks.lvl ∧
      ks'.rsn[(ks'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 ≠ 0xFFFFFFFF#32)
    (hc_ok : confl ≠ 0xFFFFFFFF#32 → confl.toNat < ks'.nc.toNat ∧
      ∀ l ∈ k5ClauseLits ks' confl.toNat, ks'.vals[l]? = some 2#32) :
    K5SolveLoopInv acap P ks0 ks' confl := by
  have hframe' := K5SolveFrame.trans hframe ⟨hp.nv, hp.nassump, hp.assump⟩
  have hlvlne' : K512LvlNonempty ks' := by
    intro L hL0 hLle; rw [hp.lvl] at hLle
    obtain ⟨i, hi, hiv⟩ := hlvlne L hL0 hLle
    refine ⟨i, Nat.lt_of_lt_of_le hi hte_le, ?_⟩
    obtain ⟨ht, hl, _⟩ := htrl_kept i hi; rw [ht, hl]; exact hiv
  have hlate' : K512FreeDecLate ks' := by
    intro p hp_lt hpos hrsn hnot a ha
    have hass_eq : k5AssumpLits ks' = k5AssumpLits ks := by
      unfold k5AssumpLits; rw [hp.nassump, hp.assump]
    rw [hass_eq] at hnot ha
    by_cases hp_old : p < ks.trl_end.toNat
    · obtain ⟨ht, hl, hr⟩ := htrl_kept p hp_old
      rw [ht, hl] at hpos; rw [ht, hr] at hrsn; rw [ht] at hnot
      obtain ⟨q, hqp, hqa⟩ := hlate p hp_old hpos hrsn hnot a ha
      exact ⟨q, hqp, by rw [(htrl_kept q (Nat.lt_trans hqp hp_old)).1]; exact hqa⟩
    · exact absurd hrsn (hnew p (by omega) hp_lt).2
  exact ⟨hinv', hsync', hframe', hlvlne', hlate', hc_ok⟩

private theorem k5_solveLoopInv_of_analyze {acap : Nat} {P : (Nat → Bool) → Prop}
    {ks0 ks ks' : K512State} (hinv : K512Inv acap P ks) (hframe : K5SolveFrame ks0 ks)
    (hlvlne : K512LvlNonempty ks) (hlate : K512FreeDecLate ks)
    (hinv' : K512Inv acap P ks') (hsync' : K512TrailSynced ks')
    (e_nv : ks'.nv = ks.nv) (e_na : ks'.nassump = ks.nassump) (e_as : ks'.assump = ks.assump)
    (hlvl_lt : ks'.lvl.toNat < ks.lvl.toNat)
    (hdec_sub : ∀ d ∈ k5TrailDecisions ks', ∃ i < ks.trl_end.toNat,
      (ks.trl[i]?.getD 0#32).toNat = d ∧ d ∈ k5TrailDecisions ks ∧
      (ks.lvlArr[d / 2]?.getD 0#32).toNat ≤ ks'.lvl.toNat)
    (hkept_below : ∀ i < ks.trl_end.toNat,
      (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ ks'.lvl.toNat →
      i < ks'.trl_end.toNat ∧ ks'.trl[i]? = ks.trl[i]? ∧
      ks'.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? =
        ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?) :
    K5SolveLoopInv acap P ks0 ks' 0xFFFFFFFF#32 := by
  have hframe' := K5SolveFrame.trans hframe ⟨e_nv, e_na, e_as⟩
  have hlvlne' : K512LvlNonempty ks' := by
    intro L hL0 hLle
    obtain ⟨i, hi, hiv⟩ := hlvlne L hL0 (Nat.le_trans hLle (Nat.le_of_lt hlvl_lt))
    obtain ⟨hi', ht, hl⟩ := hkept_below i hi (by rw [hiv]; exact hLle)
    exact ⟨i, hi', by rw [ht, hl]; exact hiv⟩
  have hlate' : K512FreeDecLate ks' := by
    intro p hp hpos hrsn hnot a ha
    have hass_eq : k5AssumpLits ks' = k5AssumpLits ks := by unfold k5AssumpLits; rw [e_na, e_as]
    rw [hass_eq] at hnot ha
    have hnv' := hinv'.clauses.nv_le; have hnv := hinv.clauses.nv_le
    have htrl_len' : ks'.trl_end.toNat ≤ ks'.trl.length := by
      rw [hinv'.shapes.trl_len]; have := hinv'.assign.trl_end_le; unfold k5MaxV at hnv'; omega
    have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
      rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; unfold k5MaxV at hnv; omega
    have hd_mem' : (ks'.trl[p]?.getD 0#32).toNat ∈ k5TrailDecisions ks' :=
      (k5_mem_trailDecisions_iff htrl_len').mpr ⟨p, hp, rfl, hpos, hrsn⟩
    obtain ⟨p0, hp0, hp0_eq, hp0_dec, hp0_lvl⟩ := hdec_sub _ hd_mem'
    have hle0 : (ks.lvlArr[(ks.trl[p0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        ks'.lvl.toNat := by rw [hp0_eq]; exact hp0_lvl
    obtain ⟨hp0', hp0_trl, _⟩ := hkept_below p0 hp0 hle0
    obtain rfl : p0 = p := k5_trl_idx_eq_of_val hinv' hp0' hp (by rw [hp0_trl]; exact hp0_eq)
    obtain ⟨_, _, _, hpos0, hrsn0⟩ := (k5_mem_trailDecisions_iff htrl_len).mp hp0_dec
    have hnot0 : (ks.trl[p0]?.getD 0#32).toNat ∉ k5AssumpLits ks := by rw [← hp0_trl]; exact hnot
    obtain ⟨q, hqp, hqa⟩ := hlate p0 hp0 (by rw [← hp0_eq] at hpos0; exact hpos0)
      (by rw [← hp0_eq] at hrsn0; exact hrsn0) hnot0 a ha
    have hq_lvl := Nat.le_trans (hinv.assign.trl_lvl_mono q p0 (Nat.le_of_lt hqp) hp0) hle0
    obtain ⟨_, hq_trl, _⟩ := hkept_below q (Nat.lt_trans hqp hp0) hq_lvl
    exact ⟨q, hqp, by rw [hq_trl]; exact hqa⟩
  exact ⟨hinv', hsync', hframe', hlvlne', hlate', fun h => absurd rfl h⟩

private theorem k5_solveLoopInv_of_lvl0 {acap : Nat} {P : (Nat → Bool) → Prop}
    {ks0 ks : K512State} (hinv : K512Inv acap P ks) (hsync : K512TrailSynced ks)
    (hlvl0 : ks.lvl = 0#32) (hframe : K5SolveFrame ks0 ks) :
    K5SolveLoopInv acap P ks0 ks 0xFFFFFFFF#32 :=
  ⟨hinv, hsync, hframe,
   fun L hL0 hLle => by rw [hlvl0] at hLle; simp at hLle; omega,
   fun p hp hpos => by
     exfalso; have hnv := hinv.clauses.nv_le
     have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
       rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; unfold k5MaxV at hnv; omega
     have hlp := hinv.assign.trl_lt _ (k5_mem_trailLits_of_lt hp htrl_len)
     have hle := hinv.assign.trl_lvl_le ((ks.trl[p]?.getD 0#32).toNat / 2) (by omega)
     rw [hlvl0] at hle; simp at hle; omega,
   fun h => absurd rfl h⟩

private theorem k5_bv32_shl1_or_bit {pick ph : BitVec 32} {nv : Nat}
    (hp : pick.toNat < nv) (hnv : nv ≤ k5MaxV) (hph : ph.toNat < 2) :
    ((pick <<< (1 : Nat)) ||| ph).toNat = 2 * pick.toNat + ph.toNat ∧
    ((pick <<< (1 : Nat)) ||| ph).toNat < 2 * nv := by
  unfold k5MaxV at hnv
  have h1 : (pick <<< (1 : Nat)).toNat = 2 * pick.toNat := by
    rw [BitVec.toNat_shiftLeft]; simp; omega
  have h2 : ((pick <<< (1 : Nat)) ||| ph).toNat = 2 * pick.toNat + ph.toNat := by
    rcases (by omega : ph.toNat = 0 ∨ ph.toNat = 1) with hz | ho
    · have : ph = 0#32 := BitVec.eq_of_toNat_eq hz; subst this; simp [h1]
    · have : ph = 1#32 := BitVec.eq_of_toNat_eq ho; subst this
      rw [BitVec.toNat_or, h1]
      have heq : 2 ^ 1 * pick.toNat + 1 = (2 ^ 1 * pick.toNat) ||| 1 :=
        Nat.two_pow_add_eq_or_of_lt (by decide : 1 < 2 ^ 1) pick.toNat
      have h132 : (1#32 : BitVec 32).toNat = 1 := rfl
      rw [h132, show 2 * pick.toNat = 2 ^ 1 * pick.toNat by omega, ← heq]
  exact ⟨h2, by omega⟩

private theorem k5_solve_post_finish {c : FullCfg} {s : FullState} {P : (Nat → Bool) → Prop}
    {scr : List (BitVec 32)} {ks0 ks' : K512State} {fuel' r : BitVec 64} {R : Mem 64 → Prop}
    {m' : Mem 64} {Q : Post [i64]}
    (hlen : s.LengthsOk c) (h2304 : 2304 ≤ scr.length) (hscr_len : scr.length = c.scratch_cap)
    (hscr_ge : k5MinScr ≤ scr.length) (hof_ks0 : k5StateOfScratch scr = ks0)
    (hinv' : K512Inv (scr.length - (k5Base + k5SlabFixed)) P ks')
    (hfuel : fuel'.toNat ≤ s.core.fuel.toNat) (hframe : K5SolveFrame ks0 ks')
    (hr : r = 0#64 ∨ r = 10#64 ∨ r = 20#64)
    (hr20 : r = 20#64 → ∀ β, P β → ¬ (unitsCnf (k5AssumpLits ks')).Sat β)
    (hm' : (FullK512Frame c { s with core := { s.core with fuel := fuel' } } ⋆
      K512Mem (c.pScratchBuf + 9216#64) ks' ⋆ R) m')
    (hQ : ∀ (r fuel' : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with core := { s.core with fuel := fuel' }
                                     scratch := { s.scratch with scratch_buf := scr' } }
      let ks := k5StateOfScratch s.scratch.scratch_buf; let ks' := k5StateOfScratch scr'
      s'.LengthsOk c → fuel'.toNat ≤ s.core.fuel.toNat →
      (∀ i < k5Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K512ScratchInv P scr' → ks'.nv = ks.nv → ks'.nassump = ks.nassump →
      k5AssumpLitsS scr' = k5AssumpLitsS s.scratch.scratch_buf →
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → ∀ β, P β → ¬ (unitsCnf (k5AssumpLitsS scr')).Sat β) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hscr_eq : s.scratch.scratch_buf = scr) : Q (r, ()) m' := by
  let sFuel : FullState := { s with core := { s.core with fuel := fuel' } }
  let scr' := scr.take 2304 ++ ks'.toSlab
  have hsh' := hinv'.shapes
  have htk_len : (scr.take 2304).length = 2304 := List.length_take_of_le h2304
  have hscr'_len : scr'.length = c.scratch_cap := by
    simp only [scr', List.length_append, htk_len, K512State.toSlab_length hsh']
    unfold k5MinScr at hscr_ge; unfold k5Base k5SlabFixed; omega
  have hpre : ∀ i < k5Base, scr'[i]? = s.scratch.scratch_buf[i]? := fun i hi => by
    rw [hscr_eq, List.getElem?_append_left (by unfold k5Base at hi; omega),
      List.getElem?_take_of_lt (by unfold k5Base at hi; omega)]
  have hof' : k5StateOfScratch scr' = ks' := by
    unfold k5StateOfScratch
    rw [show scr' = scr.take 2304 ++ ks'.toSlab from rfl,
      k5_slab_drop_exact _ ks'.toSlab (by unfold k5Base; exact htk_len)]
    exact K512State.ofSlab_toSlab hsh'
  have hks_inv' : K512ScratchInv P scr' := by
    refine ⟨by rw [hscr'_len, ← hscr_len]; exact hscr_ge, by rw [hscr'_len]; exact c.hscr, ?_⟩
    rw [hof', hscr'_len, ← hscr_len]; exact hinv'
  have hlen_f : sFuel.LengthsOk c :=
    ⟨{ hlen.core_ok with vals_len := hlen.core_ok.vals_len }, hlen.scratch_ok⟩
  have hlen' : FullState.LengthsOk c
      { sFuel with scratch := { s.scratch with scratch_buf := scr' } } :=
    k5_fullState_lengthsOk_scratch hlen_f (by rw [hscr'_len])
  have hm_join := fullMem_join_k5 (c := c) (s := sFuel)
    (acap := scr.length - (k5Base + k5SlabFixed)) (ks' := ks') (R := R)
    (by change 2304 ≤ sFuel.scratch.scratch_buf.length; rw [hscr_eq]; exact h2304) hsh' hm'
  refine hQ r fuel' scr' m' hlen' hfuel hpre hks_inv'
    (by rw [hof', hscr_eq, hof_ks0]; exact hframe.nv)
    (by rw [hof', hscr_eq, hof_ks0]; exact hframe.nassump)
    (by unfold k5AssumpLitsS k5AssumpLits; rw [hof', hscr_eq, hof_ks0, hframe.nassump,
        hframe.assump])
    hr (fun h20 => by unfold k5AssumpLitsS; rw [hof']; exact hr20 h20)
    (by simpa [sFuel, scr', hscr_eq] using hm_join)

/-- `12/24`: Parametric `Func.wp` proof for `full_k512_solve`. -/
theorem full_k512_solve_wp (Γ : Env)
    (hBt : ∀ args m Q X, k5BacktrackSpec args m Q X →
      Γ "full_k512_backtrack" [i64, i32] [] args m Q X)
    (hAsg : ∀ args m Q X, k5AssignSpec args m Q X →
      Γ "full_k512_assign" [i64, i32, i32] [] args m Q X)
    (hProp : ∀ args m Q X, k5PropagateSpec args m Q X →
      Γ "full_k512_propagate" [i64] [i32] args m Q X)
    (hAna : ∀ args m Q X, k5AnalyzeSpec args m Q X →
      Γ "full_k512_analyze" [i64, i32] [.bool] args m Q X) :
    ∀ args m Q X, k5SolveSpec args m Q X →
      Func.wp Γ full_k512_solve_body args m Q X := by
  rintro ⟨hPtr, tick_lim, ⟨⟩⟩ m Q X ⟨c, s, P, R, rfl, hlen, hscr_inv, hm, hQ⟩
  rcases hscr_inv with ⟨hscr_ge, hscr_lt, hinv0⟩
  let scr := s.scratch.scratch_buf
  let acap := scr.length - (k5Base + k5SlabFixed)
  let ks0 := k5StateOfScratch scr
  have hscr_len : scr.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hscr_min : 21792 ≤ scr.length := by
    dsimp only [scr]; unfold k5MinScr at hscr_ge; omega
  have h2304 : 2304 ≤ scr.length := by omega
  have hkPtr_eq : c.pScratchBuf + BitVec.ofNat 64 2304 * 4 = c.pScratchBuf + 9216#64 :=
    k5Ptr_base_eq c.pScratchBuf
  have hmF0 : (FullK512Frame c s ⋆ K512Mem (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) ks0 ⋆ R) m :=
    by
    rw [fullMem_eq_k5Frame hscr_min] at hm; rw [hkPtr_eq]; exact sep_ac hm
  clear hm
  c0_hsteps_nogrp; c0_call hBt
  refine ⟨acap, P, ks0, FullK512Frame c s ⋆ R, hinv0, Or.inl rfl, sep_ac hmF0,
    fun ks1 m1 hinv1 hsync1 hlvl1 _ hbt1 _ _ hm1 => ?_⟩
  dsimp only [Arg.val] at hm1
  have hframe1 : K5SolveFrame ks0 ks1 := ⟨hbt1.nv, hbt1.nassump, hbt1.assump⟩
  have hmA1 : (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap ks1 ⋆
      (FullK512Frame c s ⋆ R)) m1 := k5Mem_to_amem hinv1.shapes (sep_ac hm1)
  clear hm1
  c0_hsplit
  · have hinc1 : ks1.incons ≠ 0#32 := ‹_›
    c0_hsteps!; obtain ⟨_, hmFin1⟩ := k5MemA_to_mem hmA1
    refine k5_solve_post_finish hlen h2304 hscr_len hscr_ge rfl hinv1 (le_refl _) hframe1
      (Or.inr (Or.inr rfl)) (fun _ β hP _ => hinv1.clauses.incons_ok hinc1 β hP) ?_ hQ rfl
    rw [← hkPtr_eq]; exact sep_ac hmFin1
  · c0_hsteps_nogrp
    refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
      (fun tlim => (tlim, ())) (fun _ => True) ?_ (fun _ hJt => by
        c0_hsplit <;> (c0_hsteps!; exact hJt _ trivial))
    rintro _ tlim _
    c0_hsteps_nogrp
    let ks2 := ks1.putHdr .tick_lim tlim
    have hinv2 := k5_inv_set_tick_lim hinv1 tlim
    have hsync2 : K512TrailSynced ks2 := hsync1
    have hframe2 : K5SolveFrame ks0 ks2 := K5SolveFrame.trans hframe1 ⟨rfl, rfl, rfl⟩
    obtain ⟨_, hm2_m⟩ := k5MemA_to_mem hm
    c0_call hProp
    refine ⟨acap, P, ks2, FullK512Frame c s ⋆ R, hinv2, hsync2, hm2_m,
      fun confl_p ks_p m_p hinv_p hsync_p hp_p hte_p hkept_p hnew_p _ hconfl_ne hm_p => ?_⟩
    dsimp only [Arg.val] at hm_p
    have hm_p' : (K512Mem (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) ks_p ⋆
        (FullK512Frame c s ⋆ R)) m_p := hm_p
    clear hm_p
    c0_hsplit
    · have hc_ne_ff : confl_p ≠ 0xFFFFFFFF#32 := ‹_›
      have hmA_p := k5Mem_to_amem hinv_p.shapes hm_p'; clear hm_p'
      c0_hsteps!
      obtain ⟨hc_lt, hc_fals⟩ := hconfl_ne hc_ne_ff
      have huns := k5_conflict_unsat_lvl0 hinv_p (hp_p.lvl.trans hlvl1) hc_lt hc_fals
      have hinv_i := k5SetIncons_preserves_inv hinv_p huns
      have hframe_i : K5SolveFrame ks0 (ks_p.putHdr .incons 1#32) :=
        K5SolveFrame.trans hframe2 ⟨hp_p.nv, hp_p.nassump, hp_p.assump⟩
      obtain ⟨_, hmFin_i⟩ := k5MemA_to_mem hm
      refine k5_solve_post_finish hlen h2304 hscr_len hscr_ge rfl hinv_i (le_refl _) hframe_i
        (Or.inr (Or.inr rfl)) (fun _ β hP _ => huns β hP) ?_ hQ rfl
      rw [← hkPtr_eq]; exact sep_ac hmFin_i
    · have hc_ff : confl_p = 0xFFFFFFFF#32 := by
        first | exact ‹_› | exact Classical.not_not.mp ‹_›
      have hframe_p := K5SolveFrame.trans hframe2 ⟨hp_p.nv, hp_p.nassump, hp_p.assump⟩
      have hsi_p := k5_solveLoopInv_of_lvl0 hinv_p hsync_p (hp_p.lvl.trans hlvl1) hframe_p
      refine wp_while_state1 (fun st : BitVec 32 × K512State × BitVec 64 => st.1)
        (fun st => st.2.2.toNat)
        (fun st m_l => st.2.2.toNat ≤ s.core.fuel.toNat ∧
          K5SolveLoopInv acap P ks0 st.2.1 st.1 ∧
          (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap st.2.1 ⋆
            (FullK512Frame c { s with core := { s.core with fuel := st.2.2 } } ⋆ R)) m_l) ?_ ?_
      · intro Jm hJm; c0_hsteps!; rw [hc_ff]
        exact hJm (0xFFFFFFFF#32, ks_p, s.core.fuel) m_p
          ⟨le_refl _, hsi_p, k5Mem_to_amem hinv_p.shapes hm_p'⟩
      · rintro Jm ⟨confl_m, km, fuel_m⟩ m_l ⟨hfuel_m, hsi_m, hm_l⟩ ih_m
        dsimp only at hfuel_m hsi_m hm_l
        c0_hsplit
        · c0_hsplit
          · have hfuel_pos : 0 < fuel_m.toNat := by bv_omega
            have hfuel_sub : (fuel_m - 1#64).toNat = fuel_m.toNat - 1 := by bv_omega
            let sFuel1 : FullState := { s with core := { s.core with fuel := fuel_m - 1#64 } }
            have hfuel_le1 : (fuel_m - 1#64).toNat ≤ s.core.fuel.toNat := by omega
            c0_hsplit
            · -- `confl != 0xFFFFFFFF`
              have hconfl_ne : confl_m ≠ 0xFFFFFFFF#32 := ‹_›
              have hm_l1 : (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap km ⋆
                  (FullK512Frame c sFuel1 ⋆ R)) m := by simpa only [sFuel1] using sep_ac hm
              clear hm
              c0_hsplit
              · -- `lvl == 0` -> UNSAT (20)
                have hlvl0_m : km.lvl = 0#32 := ‹_›
                c0_hsteps!
                obtain ⟨hc_lt, hc_fals⟩ := hsi_m.confl_ok hconfl_ne
                have huns := k5_conflict_unsat_lvl0 hsi_m.inv hlvl0_m hc_lt hc_fals
                have hinv_i := k5SetIncons_preserves_inv hsi_m.inv huns
                have hframe_i : K5SolveFrame ks0 (km.putHdr .incons 1#32) :=
                  K5SolveFrame.trans hsi_m.frame ⟨rfl, rfl, rfl⟩
                obtain ⟨_, hmFin_i⟩ := k5MemA_to_mem hm
                refine k5_solve_post_finish hlen h2304 hscr_len hscr_ge rfl hinv_i hfuel_le1
                  hframe_i (Or.inr (Or.inr rfl)) (fun _ β hP _ => huns β hP) ?_ hQ rfl
                rw [← hkPtr_eq]; exact sep_ac hmFin_i
              · -- `lvl > 0` -> analyze & propagate
                have hlvl_pos : 0 < km.lvl.toNat := by bv_omega
                obtain ⟨hc_lt, hc_fals⟩ := hsi_m.confl_ok hconfl_ne
                obtain ⟨iw, hiw, hiw_lvl⟩ := hsi_m.lvlne km.lvl.toNat hlvl_pos (le_refl _)
                have hiw_lvl_bv : km.lvlArr[(km.trl[iw]?.getD 0#32).toNat / 2]?.getD 0#32 =
                    km.lvl := BitVec.eq_of_toNat_eq hiw_lvl
                obtain ⟨_, hm_a0⟩ := k5MemA_to_mem hm_l1
                c0_call hAna
                refine ⟨acap, P, km, FullK512Frame c sFuel1 ⋆ R, hsi_m.inv, hsi_m.sync,
                  hlvl_pos, ⟨iw, hiw, hiw_lvl_bv⟩, hc_lt, hc_fals, hm_a0,
                  fun ok_a ks_a m_a hinv_a e_nv e_na e_as _ hok_a hm_a => ?_⟩
                dsimp only [Arg.val] at hm_a
                c0_hsplit
                · have hok_t : ok_a = true := by cases ok_a <;> simp_all
                  obtain ⟨hsync_a, hlvl_lt, _, hdec_sub, hkept⟩ := hok_a hok_t
                  have hsi_a := k5_solveLoopInv_of_analyze hsi_m.inv hsi_m.frame hsi_m.lvlne
                    hsi_m.late hinv_a hsync_a e_nv e_na e_as hlvl_lt hdec_sub hkept
                  c0_call hProp
                  refine ⟨acap, P, ks_a, FullK512Frame c sFuel1 ⋆ R, hsi_a.inv, hsi_a.sync, hm_a,
                    fun confl_p2 ks_p2 m_p2 hinv_p2 hsync_p2 hp_p2 hte_p2 hkept_p2 hnew_p2 _
                      hc_ne2 hm_p2 => ?_⟩
                  dsimp only [Arg.val] at hm_p2
                  have hsi_p2 := k5_solveLoopInv_of_propagate hsi_a.inv hsi_a.frame hsi_a.lvlne
                    hsi_a.late hinv_p2 hsync_p2 hp_p2 hte_p2 hkept_p2 hnew_p2 hc_ne2
                  c0_hsteps!
                  exact ih_m (confl_p2, ks_p2, fuel_m - 1#64) _ (by dsimp only; omega)
                    ⟨hfuel_le1, hsi_p2, k5Mem_to_amem hinv_p2.shapes hm_p2⟩
                · c0_hsteps!
                  have hframe_a := K5SolveFrame.trans hsi_m.frame ⟨e_nv, e_na, e_as⟩
                  refine k5_solve_post_finish hlen h2304 hscr_len hscr_ge rfl hinv_a hfuel_le1
                    hframe_a (Or.inl rfl) (fun h => absurd h (by decide)) ?_ hQ rfl
                  rw [← hkPtr_eq]; exact sep_ac hm_a
            · -- `confl == 0xFFFFFFFF`: check assumptions, then decide
              have hconfl_ff : confl_m = 0xFFFFFFFF#32 := by
                first | exact ‹_› | exact Classical.not_not.mp ‹_›
              have hm_l1 : (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap km ⋆
                  (FullK512Frame c sFuel1 ⋆ R)) m := by simpa only [sFuel1] using sep_ac hm
              clear hm
              c0_hsteps_nogrp
              refine wp_while_break_state
                (β := BitVec 32 × BitVec 32 × Bool × K512State)
                (fun bst => ((bst.1, bst.2.1, bst.2.2.1, ()) : Tup Val [i32, i32, .bool]))
                (fun bst m_b =>
                  (bst.2.2.1 = false → bst.1 = 0xFFFFFFFF#32 ∧ bst.2.2.2 = km ∧
                    ∀ j < km.nassump.toNat,
                      km.vals[(km.assump[j]?.getD 0#32).toNat]? = some 1#32) ∧
                  (bst.2.2.1 = true → K5SolveLoopInv acap P ks0 bst.2.2.2 bst.1) ∧
                  (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap bst.2.2.2 ⋆
                    (FullK512Frame c sFuel1 ⋆ R)) m_b)
                (α := BitVec 32) (fun st => ((st, ()) : Tup Val [i32]))
                (fun st => km.nassump.toNat - st.toNat)
                (fun st m_b => st.toNat ≤ km.nassump.toNat ∧
                  (∀ j < st.toNat, km.vals[(km.assump[j]?.getD 0#32).toNat]? = some 1#32) ∧
                  (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap km ⋆
                    (FullK512Frame c sFuel1 ⋆ R)) m_b) ?_ ?_ ?_
              · rintro B ⟨confl_b, ad_b, did_b, ks_b⟩ m_b ⟨hf_b, ht_b, hm_b⟩
                dsimp only at hf_b ht_b hm_b
                c0_hsplit
                · have hdid_t : did_b = true := ‹_›
                  c0_hsteps!
                  exact ih_m (confl_b, ks_b, fuel_m - 1#64) _ (by dsimp only; omega)
                    ⟨hfuel_le1, ht_b hdid_t, hm_b⟩
                · have hdid_f : did_b = false := by cases did_b <;> simp_all
                  obtain ⟨_, hks_b_eq, hall_ass_j⟩ := hf_b hdid_f; subst ks_b
                  have hall_ass_mem : ∀ a ∈ k5AssumpLits km, km.vals[a]? = some 1#32 := by
                    intro a ha
                    simp only [k5AssumpLits, List.mem_map, List.mem_take_iff_getElem] at ha
                    obtain ⟨ab, ⟨ia, hia, rfl⟩, rfl⟩ := ha
                    have hlen_a : km.nassump.toNat ≤ km.assump.length := by
                      rw [hsi_m.inv.shapes.assump_len]; exact hsi_m.inv.clauses.nassump_le
                    have hget := hall_ass_j ia (by omega)
                    rwa [List.getElem?_eq_getElem (by omega : ia < km.assump.length),
                      Option.getD_some] at hget
                  c0_hsplit
                  · c0_hsteps!; obtain ⟨_, hmFin_b⟩ := k5MemA_to_mem hm_b
                    refine k5_solve_post_finish hlen h2304 hscr_len hscr_ge rfl hsi_m.inv
                      hfuel_le1 hsi_m.frame (Or.inr (Or.inl rfl))
                      (fun h => absurd h (by decide)) ?_ hQ rfl
                    rw [← hkPtr_eq]; exact sep_ac hmFin_b
                  · have hnv_m := hsi_m.inv.clauses.nv_le
                    c0_hsteps_nogrp
                    refine wp_while_break_state (β := BitVec 32 × BitVec 32 × BitVec 32)
                      (fun bst => (bst.1, bst.2.1, bst.2.2, ()))
                      (fun bst m_v => (bst.2.1 = 0xFFFFFFFF#32 ∨ (bst.2.1.toNat < km.nv.toNat ∧
                          km.vals[2 * bst.2.1.toNat]?.getD 0#32 = 0#32)) ∧
                        (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap km ⋆
                          (FullK512Frame c sFuel1 ⋆ R)) m_v)
                      (α := BitVec 32 × BitVec 32) (fun st => (st.1, st.2, ()))
                      (fun st => km.nv.toNat - st.2.toNat)
                      (fun st m_v => st.2.toNat ≤ km.nv.toNat ∧
                        (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap km ⋆
                          (FullK512Frame c sFuel1 ⋆ R)) m_v) ?_ ?_ ?_
                    · rintro B1 ⟨_c1, pick1, _s1⟩ m_v1 ⟨hpick1, hm_v1⟩
                      dsimp only at hpick1 hm_v1
                      refine wp_join_state
                        (proj :=
                          fun p : BitVec 32 × BitVec 32 × BitVec 32 => (p.1, p.2.1, p.2.2, ()))
                        (fun p m_v2 => (p.2.1 = 0xFFFFFFFF#32 ∨ (p.2.1.toNat < km.nv.toNat ∧
                            km.vals[2 * p.2.1.toNat]?.getD 0#32 = 0#32)) ∧
                          (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap km ⋆
                            (FullK512Frame c sFuel1 ⋆ R)) m_v2) ?_ ?_
                      · intro J2 ⟨_c2, pick2, _s2⟩ m_v2 ⟨hpick2, hm_v2⟩
                        dsimp only at hpick2 hm_v2
                        refine wp_join_state
                          (proj := fun p : BitVec 32 × BitVec 32 => (p.1, p.2, ()))
                          (fun p m_v3 => (p.2 = 0xFFFFFFFF#32 ∨ (p.2.toNat < km.nv.toNat ∧
                              km.vals[2 * p.2.toNat]?.getD 0#32 = 0#32)) ∧
                            (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap km ⋆
                              (FullK512Frame c sFuel1 ⋆ R)) m_v3) ?_ ?_
                        · intro J3 ⟨_c3, pick3⟩ m_v3 ⟨hpick3, hm_v3⟩
                          dsimp only at hpick3 hm_v3
                          c0_hsplit
                          · c0_hsteps!; obtain ⟨_, hmFin_v⟩ := k5MemA_to_mem hm_v3
                            refine k5_solve_post_finish hlen h2304 hscr_len hscr_ge rfl hsi_m.inv
                              hfuel_le1 hsi_m.frame (Or.inr (Or.inl rfl))
                              (fun h => absurd h (by decide)) ?_ hQ rfl
                            rw [← hkPtr_eq]; exact sep_ac hmFin_v
                          · have hpk_ne : pick3 ≠ 0xFFFFFFFF#32 := ‹_›
                            rcases hpick3 with rfl | ⟨hpk_lt, hpk_val⟩
                            · exact absurd rfl hpk_ne
                            have hpk_512 : pick3.toNat < 512 := by unfold k5MaxV at hnv_m; omega
                            let ks_q := km.putHdr .qsearch pick3
                            have hinv_q := k5_inv_set_qsearch hsi_m.inv pick3
                            have hframe_q : K5SolveFrame ks0 ks_q :=
                              K5SolveFrame.trans hsi_m.frame ⟨rfl, rfl, rfl⟩
                            let ph : BitVec 32 :=
                              (ks_q.flags[pick3.toNat]?.getD 0#32 ^^^ ks_q.phase) &&& 1#32
                            have hph_lt : ph.toNat < 2 := by
                              dsimp only [ph]; rw [BitVec.toNat_and]
                              have h1 : (1#32 : BitVec 32).toNat = 1 := rfl
                              rw [h1]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
                            let lit_d := (pick3 <<< (1 : Nat)) ||| ph
                            have hlit_d := k5_bv32_shl1_or_bit hpk_lt hnv_m hph_lt
                            have hlit_0 : ks_q.vals[lit_d.toNat]? = some 0#32 := by
                              have hz0 := k5_vals_some_zero hinv_q
                                (show 2 * pick3.toNat < 2 * ks_q.nv.toNat by
                                  change 2 * pick3.toNat < 2 * km.nv.toNat; omega) hpk_val
                              rcases (by omega : ph.toNat = 0 ∨ ph.toNat = 1) with h0 | h1
                              · rwa [hlit_d.1, h0, Nat.add_zero]
                              · have hxor : 2 * pick3.toNat + 1 = (2 * pick3.toNat) ^^^ 1 := by
                                  rcases k5_nat_xor1_cases (2 * pick3.toNat) with ⟨_, _⟩ | ⟨_,
                                    _⟩ <;>
                                    omega
                                rw [hlit_d.1, h1, hxor]
                                have hpk2 : 2 * pick3.toNat < 2 * ks_q.nv.toNat := by
                                  change 2 * pick3.toNat < 2 * km.nv.toNat; omega
                                exact k5_vals_some_zero hinv_q
                                  (by change (2 * pick3.toNat) ^^^ 1 < 2 * km.nv.toNat; omega)
                                  (k5_vals_xor1_zero hinv_q hpk2 hpk_val)
                            have hte_lt := k5_trl_end_lt_of_unassigned hinv_q.shapes hnv_m
                              hinv_q.assign
                                (by change lit_d.toNat < 2 * km.nv.toNat; exact hlit_d.2)
                              (by change ks_q.vals[lit_d.toNat]?.getD 0#32 = 0#32; rw [hlit_0]; rfl)
                            let ks_l := ks_q.putHdr .lvl (ks_q.lvl + 1#32)
                            c0_hsteps_nogrp; obtain ⟨_, hm_asg⟩ := k5MemA_to_mem hm
                            c0_call hAsg
                            refine ⟨acap, ks_l, FullK512Frame c sFuel1 ⋆ R,
                              hinv_q.shapes.putHdr .lvl _, hinv_q.clauses.acap_lt, hnv_m, hlit_d.2,
                              hte_lt, hm_asg, fun mA hmA => ?_⟩
                            dsimp only [Arg.val] at hmA
                            obtain ⟨hinv_d, hsync_d, hframe_d, hlvlne_d, hlate_d⟩ :=
                              k5_decide_step_preserves hinv_q hsi_m.sync hframe_q hsi_m.lvlne
                                hsi_m.late hlit_d.2 hlit_0 (fun _ => hall_ass_mem)
                            c0_call hProp
                            refine ⟨acap, P, k5AssignStep ks_l lit_d 0xFFFFFFFF#32,
                              FullK512Frame c sFuel1 ⋆ R, hinv_d, hsync_d, hmA,
                              fun confl_p2 ks_p2 m_p2 hinv_p2 hsync_p2 hp_p2 hte_p2 hkept_p2
                                hnew_p2 _ hc_ne2 hm_p2 => ?_⟩
                            dsimp only [Arg.val] at hm_p2
                            have hsi_p2 := k5_solveLoopInv_of_propagate hinv_d hframe_d hlvlne_d
                              hlate_d hinv_p2 hsync_p2 hp_p2 hte_p2 hkept_p2 hnew_p2 hc_ne2
                            c0_hsteps!
                            exact ih_m (confl_p2, ks_p2, fuel_m - 1#64) _ (by dsimp only; omega)
                              ⟨hfuel_le1, hsi_p2, k5Mem_to_amem hinv_p2.shapes hm_p2⟩
                        · intro J3 hJ3; c0_hsplit
                          · c0_hsteps_nogrp
                            refine wp_while_break_state (β := BitVec 32 × BitVec 32)
                              (fun bst => (bst.1, bst.2, ()))
                              (fun bst m_v => (bst.2 = 0xFFFFFFFF#32 ∨ (bst.2.toNat < km.nv.toNat ∧
                                  km.vals[2 * bst.2.toNat]?.getD 0#32 = 0#32)) ∧
                                (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap km ⋆
                                  (FullK512Frame c sFuel1 ⋆ R)) m_v)
                              (α := BitVec 32) (fun st => (st, ()))
                              (fun st => km.nv.toNat - st.toNat)
                              (fun st m_v => st.toNat ≤ km.nv.toNat ∧
                                (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap km ⋆
                                  (FullK512Frame c sFuel1 ⋆ R)) m_v) ?_ ?_ ?_
                            · rintro B3 ⟨c3, p3⟩ m_v3 hp3
                              exact wp_jump_state (proj :=
                                fun p : BitVec 32 × BitVec 32 => (p.1, p.2, ()))
                                (c3, p3) rfl (hJ3 (c3, p3) m_v3 hp3)
                            · rintro B3 L3 c3 m_v3 hB3 hL3 ⟨hc3_le, hm_v3⟩
                              c0_hsplit
                              · have hc3_lt : c3.toNat < km.nv.toNat := by bv_omega
                                have hc3_shl : (c3 <<< (1 : Nat)).toNat = 2 * c3.toNat := by
                                  rw [BitVec.toNat_shiftLeft]; unfold k5MaxV at hnv_m; simp; omega
                                have hc3_1024 : (c3 <<< (1 : Nat)).toNat < 1024 := by
                                  rw [hc3_shl]; unfold k5MaxV at hnv_m; omega
                                have hc3_1 : (c3 + 1#32).toNat = c3.toNat + 1 := by
                                  unfold k5MaxV at hnv_m; bv_omega
                                c0_hsplit
                                · have hv0 : km.vals[2 * c3.toNat]?.getD 0#32 = 0#32 := by
                                    rwa [← hc3_shl]
                                  c0_hsteps!; exact hB3 (c3, c3) m_v3 ⟨Or.inr ⟨hc3_lt, hv0⟩, hm_v3⟩
                                · c0_hsteps!
                                  exact hL3 (c3 + 1#32) m_v3 (by rw [hc3_1]; omega)
                                    ⟨by rw [hc3_1]; omega, hm_v3⟩
                              · c0_hsteps!; exact hB3 (c3, pick2) m_v3 ⟨hpick2, hm_v3⟩
                            · intro B3 L3 hB3 hL3
                              exact wp_jump_state (proj := fun st : BitVec 32 => (st, ())) 0#32 rfl
                                (hL3 0#32 m_v2 ⟨by simp, hm_v2⟩)
                          · exact wp_jump_state (proj :=
                            fun p : BitVec 32 × BitVec 32 => (p.1, p.2, ()))
                              (_c2, pick2) rfl (hJ3 (_c2, pick2) m_v2 ⟨hpick2, hm_v2⟩)
                      · intro J2 hJ2; c0_hsplit
                        · c0_hsteps_nogrp
                          refine wp_while_break_state (β := BitVec 32 × BitVec 32 × BitVec 32)
                            (fun bst => (bst.1, bst.2.1, bst.2.2, ()))
                            (fun bst m_v => (bst.2.1 = 0xFFFFFFFF#32 ∨
                              (bst.2.1.toNat < km.nv.toNat ∧
                                km.vals[2 * bst.2.1.toNat]?.getD 0#32 = 0#32)) ∧
                              (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap km ⋆
                                (FullK512Frame c sFuel1 ⋆ R)) m_v)
                            (α := BitVec 32 × BitVec 32) (fun st => (st.1, st.2, ()))
                            (fun st => km.nv.toNat - st.2.toNat)
                            (fun st m_v => st.2.toNat ≤ km.nv.toNat ∧
                              (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap km ⋆
                                (FullK512Frame c sFuel1 ⋆ R)) m_v) ?_ ?_ ?_
                          · rintro B2 ⟨c2, p2, s2⟩ m_v2 hp2
                            exact wp_jump_state
                              (proj :=
                                fun p : BitVec 32 × BitVec 32 × BitVec 32 => (p.1, p.2.1, p.2.2,
                                  ()))
                              (c2, p2, s2) rfl (hJ2 (c2, p2, s2) m_v2 hp2)
                          · rintro B2 L2 ⟨c2, s2⟩ m_v2 hB2 hL2 ⟨hs2_le, hm_v2⟩
                            c0_hsplit
                            · c0_hsplit
                              · have hc2_lt : c2.toNat < km.nv.toNat := by bv_omega
                                have hs2_lt : s2.toNat < km.nv.toNat := by bv_omega
                                have hc2_512 : c2.toNat < 512 := by unfold k5MaxV at hnv_m; omega
                                have hc2_shl : (c2 <<< (1 : Nat)).toNat = 2 * c2.toNat := by
                                  rw [BitVec.toNat_shiftLeft]; unfold k5MaxV at hnv_m; simp; omega
                                have hc2_1024 : (c2 <<< (1 : Nat)).toNat < 1024 := by
                                  rw [hc2_shl]; unfold k5MaxV at hnv_m; omega
                                have hs2_1 : (s2 + 1#32).toNat = s2.toNat + 1 := by
                                  unfold k5MaxV at hnv_m; bv_omega
                                c0_hsplit
                                · have hv0 : km.vals[2 * c2.toNat]?.getD 0#32 = 0#32 := by
                                    rwa [← hc2_shl]
                                  c0_hsteps!
                                  exact hB2 (c2, c2, s2) m_v2 ⟨Or.inr ⟨hc2_lt, hv0⟩, hm_v2⟩
                                · c0_hsteps!
                                  exact hL2 (km.qprev[c2.toNat]?.getD 0#32, s2 + 1#32) m_v2
                                    (by dsimp only; rw [hs2_1]; omega)
                                    ⟨by dsimp only; rw [hs2_1]; omega, hm_v2⟩
                              · c0_hsteps!; exact hB2 (c2, pick1, s2) m_v2 ⟨hpick1, hm_v2⟩
                            · c0_hsteps!; exact hB2 (c2, pick1, s2) m_v2 ⟨hpick1, hm_v2⟩
                          · intro B2 L2 hB2 hL2
                            exact wp_jump_state
                              (proj := fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ()))
                              (km.qlast, 0#32) rfl (hL2 _ _ ⟨by simp, hm_v1⟩)
                        · exact wp_jump_state
                            (proj :=
                              fun p : BitVec 32 × BitVec 32 × BitVec 32 => (p.1, p.2.1, p.2.2, ()))
                            (_c1, pick1, _s1) rfl (hJ2 (_c1, pick1, _s1) m_v1 ⟨hpick1, hm_v1⟩)
                    · rintro B1 L1 ⟨c1, s1⟩ m_v1 hB1 hL1 ⟨hs1_le, hm_v1⟩
                      c0_hsplit
                      · c0_hsplit
                        · have hc1_lt : c1.toNat < km.nv.toNat := by bv_omega
                          have hs1_lt : s1.toNat < km.nv.toNat := by bv_omega
                          have hc1_512 : c1.toNat < 512 := by unfold k5MaxV at hnv_m; omega
                          have hc1_shl : (c1 <<< (1 : Nat)).toNat = 2 * c1.toNat := by
                            rw [BitVec.toNat_shiftLeft]; unfold k5MaxV at hnv_m; simp; omega
                          have hc1_1024 : (c1 <<< (1 : Nat)).toNat < 1024 := by
                            rw [hc1_shl]; unfold k5MaxV at hnv_m; omega
                          have hs1_1 : (s1 + 1#32).toNat = s1.toNat + 1 := by
                            unfold k5MaxV at hnv_m; bv_omega
                          c0_hsplit
                          · have hv0 : km.vals[2 * c1.toNat]?.getD 0#32 = 0#32 := by
                              rwa [← hc1_shl]
                            c0_hsteps!; exact hB1 (c1, c1, s1) m_v1 ⟨Or.inr ⟨hc1_lt, hv0⟩, hm_v1⟩
                          · c0_hsteps!
                            exact hL1 (km.qprev[c1.toNat]?.getD 0#32, s1 + 1#32) m_v1
                              (by dsimp only; rw [hs1_1]; omega)
                              ⟨by dsimp only; rw [hs1_1]; omega, hm_v1⟩
                        · exact hB1 (c1, 0xFFFFFFFF#32, s1) m_v1 ⟨Or.inl rfl, hm_v1⟩
                      · exact hB1 (c1, 0xFFFFFFFF#32, s1) m_v1 ⟨Or.inl rfl, hm_v1⟩
                    · intro B1 L1 hB1 hL1
                      exact wp_jump_state
                        (proj := fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ()))
                        (km.qsearch, 0#32) rfl (hL1 _ _ ⟨by simp, hm_b⟩)
              · -- Assumption loop body
                rintro B0 L0 ad_a m_a hB0 hL0 ⟨had_le, hall_j, hm_a⟩
                c0_hsplit
                · have had_lt : ad_a.toNat < km.nassump.toNat := by bv_omega
                  have hna_le := hsi_m.inv.clauses.nassump_le
                  have hnv_m := hsi_m.inv.clauses.nv_le
                  have had_512 : ad_a.toNat < 512 := by unfold k5MaxV at hna_le; omega
                  have had_1 : (ad_a + 1#32).toNat = ad_a.toNat + 1 := by
                    unfold k5MaxV at hna_le; bv_omega
                  let alit := km.assump[ad_a.toNat]?.getD 0#32
                  have halit_lt : alit.toNat < 2 * km.nv.toNat :=
                    hsi_m.inv.clauses.assump_ok ad_a.toNat had_lt
                  have halit_1024 : alit.toNat < 1024 := by unfold k5MaxV at hnv_m; omega
                  have hlen_a : km.nassump.toNat ≤ km.assump.length := by
                    rw [hsi_m.inv.shapes.assump_len]; exact hna_le
                  have halit_mem := k5_mem_assumpLits_of_lt hlen_a had_lt
                  c0_hsplit
                  · have hav2 : km.vals[alit.toNat]?.getD 0#32 = 2#32 := ‹_›
                    have hav2' : km.vals[alit.toNat]? = some 2#32 := by
                      have hl : alit.toNat < km.vals.length := by
                        rw [hsi_m.inv.shapes.vals_len]; exact halit_1024
                      rw [List.getElem?_eq_getElem hl, Option.getD_some] at hav2
                      rw [List.getElem?_eq_getElem hl, hav2]
                    c0_hsteps!; obtain ⟨_, hmFin_a⟩ := k5MemA_to_mem hm_a
                    refine k5_solve_post_finish hlen h2304 hscr_len hscr_ge rfl hsi_m.inv
                      hfuel_le1 hsi_m.frame (Or.inr (Or.inr rfl))
                      (fun _ => k5_allDecisionsInAssumps_of_late hsi_m.inv hsi_m.sync hsi_m.late
                        had_lt hav2') ?_ hQ rfl
                    rw [← hkPtr_eq]; exact sep_ac hmFin_a
                  · c0_hsplit
                    · have hav0 : km.vals[alit.toNat]?.getD 0#32 = 0#32 := ‹_›
                      have halit_0 := k5_vals_some_zero hsi_m.inv halit_lt hav0
                      have hte_lt := k5_trl_end_lt_of_unassigned hsi_m.inv.shapes hnv_m
                        hsi_m.inv.assign halit_lt hav0
                      let km_l := km.putHdr .lvl (km.lvl + 1#32)
                      c0_hsteps_nogrp; obtain ⟨_, hm_asg⟩ := k5MemA_to_mem hm
                      c0_call hAsg
                      refine ⟨acap, km_l, FullK512Frame c sFuel1 ⋆ R,
                        hsi_m.inv.shapes.putHdr .lvl _, hsi_m.inv.clauses.acap_lt, hnv_m, halit_lt,
                        hte_lt, hm_asg, fun mA hmA => ?_⟩
                      dsimp only [Arg.val] at hmA
                      obtain ⟨hinv_d, hsync_d, hframe_d, hlvlne_d, hlate_d⟩ :=
                        k5_decide_step_preserves hsi_m.inv hsi_m.sync hsi_m.frame hsi_m.lvlne
                          hsi_m.late halit_lt halit_0 (fun hnot => absurd halit_mem hnot)
                      c0_call hProp
                      refine ⟨acap, P, k5AssignStep km_l alit 0xFFFFFFFF#32,
                        FullK512Frame c sFuel1 ⋆ R, hinv_d, hsync_d, hmA,
                        fun confl_p2 ks_p2 m_p2 hinv_p2 hsync_p2 hp_p2 hte_p2 hkept_p2 hnew_p2 _
                          hc_ne2 hm_p2 => ?_⟩
                      dsimp only [Arg.val] at hm_p2
                      c0_hsteps!
                      exact hB0 (confl_p2, ad_a, true, ks_p2) m_p2
                        ⟨(fun h => by dsimp only at h; cases h),
                         fun _ => k5_solveLoopInv_of_propagate hinv_d hframe_d hlvlne_d hlate_d
                           hinv_p2 hsync_p2 hp_p2 hte_p2 hkept_p2 hnew_p2 hc_ne2,
                         k5Mem_to_amem hinv_p2.shapes hm_p2⟩
                    · have hne2 : km.vals[alit.toNat]?.getD 0#32 ≠ 2#32 := ‹_›
                      have hne0 : km.vals[alit.toNat]?.getD 0#32 ≠ 0#32 := ‹_›
                      have hav1 : km.vals[alit.toNat]?.getD 0#32 = 1#32 := by
                        rcases hsi_m.inv.assign.vals_dom alit.toNat halit_lt with h0 | h1 | h2
                        · exact absurd h0 hne0
                        · exact h1
                        · exact absurd h2 hne2
                      have hav1' : km.vals[alit.toNat]? = some 1#32 := by
                        have hl : alit.toNat < km.vals.length := by
                          rw [hsi_m.inv.shapes.vals_len]; exact halit_1024
                        rw [List.getElem?_eq_getElem hl, Option.getD_some] at hav1
                        rw [List.getElem?_eq_getElem hl, hav1]
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
              · intro B0 L0 hB0 hL0
                exact wp_jump_state (proj := fun st : BitVec 32 => (st, ())) 0#32 rfl
                  (hL0 0#32 m ⟨by simp, fun _ hj => by simp at hj, hm_l1⟩)
          · c0_hsteps!; obtain ⟨_, hmFin_m⟩ := k5MemA_to_mem hm_l
            refine k5_solve_post_finish hlen h2304 hscr_len hscr_ge rfl hsi_m.inv hfuel_m
              hsi_m.frame (Or.inl rfl) (fun h => absurd h (by decide)) ?_ hQ rfl
            rw [← hkPtr_eq]; exact sep_ac hmFin_m
        · c0_hsteps!; obtain ⟨_, hmFin_m⟩ := k5MemA_to_mem hm_l
          refine k5_solve_post_finish hlen h2304 hscr_len hscr_ge rfl hsi_m.inv hfuel_m
            hsi_m.frame (Or.inl rfl) (fun h => absurd h (by decide)) ?_ hQ rfl
          rw [← hkPtr_eq]; exact sep_ac hmFin_m

end LeanQbe.T.Examples.Kissat.FullM4Sweep
