module

public import LeanQbe.T.Examples.Kissat.FullKittenLemmas2

/-!
# Kissat `D-Full` Scratch `kitten` Helpers, `build_failing`, & `flip` (`Part 3`)

1. Pure bitvector, CNF resolution, pigeonhole, and 2WL watch-chain cursor (`WChainCursor`)
   preservation lemmas shared by `flip` and `propagate`.
2. `full_kitten_build_failing_wp` (`8/15`): marks failing conflict-closure `KM_CORE` clauses on the
   trail and proves `(marked_core ++ unitsCnf assumps).Unsat`.
3. `full_kitten_flip_wp` (`9/15`): relocates watched literals on `whead[lit]` and flips
   `vals[lit] := 2`, `vals[lit^1] := 1` preserving `KittenScratchInv`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

open scoped KittenMemTactics KittenMemATactics KittenProjTactics

/-! ## 6. Shared Bitvector, CNF, Trail, & 2WL Watch-Chain Helpers -/

theorem cm_or_core_and_ffff (x : BitVec 32) :
    ((x ||| kmCore) &&& 0xFFFF#32) = x &&& 0xFFFF#32 := by
  unfold kmCore
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have hk : (0x10000#32 : BitVec 32)[i] = false ∨ i = 16 := by revert i hi; decide
  have hm : (0xFFFF#32 : BitVec 32)[i] = false ∨ i < 16 := by revert i hi; decide
  simp only [BitVec.getElem_and, BitVec.getElem_or]
  rcases hk with h0 | rfl
  · simp [h0]
  · simp

theorem cm_or_core_and_lrn (x : BitVec 32) :
    ((x ||| kmCore) &&& kmLrn) = x &&& kmLrn := by
  have h16 : (0x20000#32 : BitVec 32)[16] = false := by decide
  unfold kmCore kmLrn
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have hk : (0x10000#32 : BitVec 32)[i] = false ∨ i = 16 := by revert i hi; decide
  simp only [BitVec.getElem_and, BitVec.getElem_or]
  rcases hk with h0 | rfl
  · simp [h0]
  · simp [h16]

theorem cm_or_core_and_core_nz (x : BitVec 32) :
    ((x ||| kmCore) &&& kmCore) ≠ 0#32 := by
  unfold kmCore
  intro h
  have h16 := congrArg (fun b : BitVec 32 => b[16]) h
  revert h16; simp

theorem cm_and_not_core (x : BitVec 32) :
    ((x &&& ~~~kmCore) &&& kmCore) = 0#32 := by
  unfold kmCore
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
  by_cases h16 : i = 16
  · subst h16; simp
  · have hk : (0x10000#32 : BitVec 32)[i] = false := by revert i hi h16; decide
    simp [hk]

theorem fl_or2_and2_nz (x : BitVec 32) :
    ((x ||| 2#32) &&& 2#32) ≠ 0#32 := by
  intro h
  have h1 := congrArg (fun b : BitVec 32 => b[1]) h
  revert h1; simp

theorem fl_andnot2_and2_zero (x : BitVec 32) :
    ((x &&& ~~~2#32) &&& 2#32) = 0#32 := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
  by_cases h1 : i = 1
  · subst h1; simp
  · have h2 : (2#32 : BitVec 32)[i] = false := by revert i hi h1; decide
    simp [h2]

/-- If `F` entails clause `c`, `u ∈ c`, and `F` entails `[x^1]` for every `x ∈ c` (`x ≠ u`),
then `F` entails unit `[u]`. -/
theorem cnf_entails_unit_of_falsified_others {F : CNF Nat} {c : List Nat} {u : Nat}
    (hc : F.EntailsClause (cnfClause c)) (_hu : u ∈ c)
    (hothers : ∀ x ∈ c, x ≠ u → F.EntailsClause (cnfClause [litNeg x])) :
    F.EntailsClause (cnfClause [u]) := by
  rw [CNF.entails_clause_def]
  intro α hα
  obtain ⟨x, hx_mem, hxsat⟩ := (clause_sat_cnfClause_iff α c).mp
    (CNF.entails_clause_def.mp hc α hα)
  by_cases hxu : x = u
  · rw [hxu] at hxsat; exact (sat_cnfClause_singleton α u).mpr hxsat
  · have hneg := CNF.entails_clause_def.mp (hothers x hx_mem hxu) α hα
    exact absurd ((sat_cnfClause_singleton α x).mpr hxsat)
      ((sat_cnfClause_litNeg_iff α x).mp hneg)

private theorem list_nodup_subset_length {n : Nat} :
    ∀ {xs : List Nat}, xs.Nodup → (∀ x ∈ xs, x < n) → xs.length ≤ n := by
  induction n with
  | zero =>
    intro xs _ hlt
    cases xs with
    | nil => simp
    | cons x _ => exact absurd (hlt x List.mem_cons_self) (by omega)
  | succ k ih =>
    intro xs hnd hlt
    by_cases hmem : k ∈ xs
    · have hnd' : (xs.erase k).Nodup := hnd.erase k
      have hlt' : ∀ x ∈ xs.erase k, x < k := by
        intro x hx
        have hmem_x := List.mem_of_mem_erase hx
        have hne : x ≠ k := fun h => by
          subst h; exact List.Nodup.not_mem_erase hnd hx
        have := hlt x hmem_x; omega
      have hle := ih hnd' hlt'
      have hlen := List.length_erase_of_mem hmem
      omega
    · have hle := ih hnd (fun x hx => by
        have := hlt x hx
        have hne : x ≠ k := fun heq => hmem (heq ▸ hx)
        omega)
      omega

private theorem list_nodup_mem_of_length_ge {n : Nat} {xs : List Nat}
    (hnd : xs.Nodup) (hlt : ∀ x ∈ xs, x < n) (hlen : n ≤ xs.length) {v : Nat} (hv : v < n) :
    v ∈ xs := by
  by_cases hmem : v ∈ xs
  · exact hmem
  · exfalso
    have h1 : (v :: xs).Nodup := List.nodup_cons.mpr ⟨hmem, hnd⟩
    have h2 : ∀ x ∈ (v :: xs), x < n := fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hv
      · exact hlt x hx'
    have hle := list_nodup_subset_length h1 h2
    simp at hle; omega

/-- If literal `l < 2 * nv` is unassigned (`vals[l] = 0`), then `trl_end < nv`. -/
theorem trl_end_lt_of_unassigned {acap : Nat} {ks : KittenState}
    (hsh : ks.ShapesOk acap) (hnv : ks.nv.toNat ≤ kMaxV) (hba : KittenBaseAssignOk ks)
    {l : Nat} (hl : l < 2 * ks.nv.toNat) (h0 : ks.vals[l]? = some 0#32) :
    ks.trl_end.toNat < ks.nv.toNat := by
  have hle := hba.trl_end_le
  by_cases hlt : ks.trl_end.toNat < ks.nv.toNat
  · exact hlt
  · exfalso
    have heq : ks.trl_end.toNat = ks.nv.toNat := by omega
    have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
      rw [hsh.trl_len]; unfold kMaxV at hnv; omega
    let vs := (kittenTrailLits ks).map (· / 2)
    have hvs_nd : vs.Nodup := hba.trl_nodup
    have hvs_lt : ∀ x ∈ vs, x < ks.nv.toNat := by
      intro x hx; rw [List.mem_map] at hx; obtain ⟨t, ht, rfl⟩ := hx
      have := hba.trl_lt t ht; omega
    have hvs_len : ks.nv.toNat ≤ vs.length := by
      simp only [vs, kittenTrailLits, List.length_map, List.length_take]; omega
    have hv_mem := list_nodup_mem_of_length_ge hvs_nd hvs_lt hvs_len (v := l / 2) (by omega)
    rw [List.mem_map] at hv_mem
    obtain ⟨t, ht, htv⟩ := hv_mem
    unfold kittenTrailLits at ht
    rw [List.mem_map] at ht
    obtain ⟨bv, hbv, rfl⟩ := ht
    obtain ⟨i, hi, heq_bv⟩ := List.getElem_of_mem hbv
    have hi_te : i < ks.trl_end.toNat := by simp [List.length_take] at hi; omega
    have hi_trl : i < ks.trl.length := by omega
    simp only [List.getElem_take] at heq_bv
    have hnz : ks.vals[l]?.getD 0#32 ≠ 0#32 := (hba.vals_nz_iff_trl l hl).mpr ⟨i, hi_te, by
      rw [List.getElem?_eq_getElem hi_trl, Option.getD_some, heq_bv]; exact htv⟩
    rw [h0] at hnz; exact hnz rfl

/-- Updating only `prop` (`≤ trl_end`) and `ticks` preserves `Inv` and `TrailSynced`. -/
theorem kittenBumpPropTicks_preserves_inv {acap : Nat} {ks : KittenState}
    (hinv : ks.Inv acap) (hsync : KittenTrailSynced ks) {pr' tk' : BitVec 32}
    (hpr : pr'.toNat ≤ ks.trl_end.toNat) :
    let ks' := (ks.putHdr .prop pr').putHdr .ticks tk'
    ks'.Inv acap ∧ KittenTrailSynced ks' := by
  intro ks'
  have hsh' : ks'.ShapesOk acap := (hinv.shapes.putHdr .prop pr').putHdr .ticks tk'
  have e_pr : ks'.prop = pr' := by dsimp only [ks']; kp_field
  have e_nv : ks'.nv = ks.nv := by dsimp only [ks']; kp_field
  have e_nc : ks'.nc = ks.nc := by dsimp only [ks']; kp_field
  have e_on : ks'.orig_nc = ks.orig_nc := by dsimp only [ks']; kp_field
  have e_lvl : ks'.lvl = ks.lvl := by dsimp only [ks']; kp_field
  have e_te : ks'.trl_end = ks.trl_end := by dsimp only [ks']; kp_field
  have e_un : ks'.unass = ks.unass := by dsimp only [ks']; kp_field
  have e_in : ks'.incons = ks.incons := by dsimp only [ks']; kp_field
  have e_fa : ks'.failing = ks.failing := by dsimp only [ks']; kp_field
  have e_an : ks'.ante = ks.ante := by dsimp only [ks']; kp_field
  have e_al : ks'.alen = ks.alen := by dsimp only [ks']; kp_field
  have e_ac : ks'.acap = ks.acap := by dsimp only [ks']; kp_field
  have e_na : ks'.nassump = ks.nassump := by dsimp only [ks']; kp_field
  have e_nu : ks'.nunits = ks.nunits := by dsimp only [ks']; kp_field
  have e_nr : ks'.nres = ks.nres := by dsimp only [ks']; kp_field
  have e_nk : ks'.nkl = ks.nkl := by dsimp only [ks']; kp_field
  have e_nn : ks'.nana = ks.nana := by dsimp only [ks']; kp_field
  have e_la : ks'.lvlArr = ks.lvlArr := by dsimp only [ks']; kp_field
  have e_rs : ks'.rsn = ks.rsn := by dsimp only [ks']; kp_field
  have e_tr : ks'.trl = ks.trl := by dsimp only [ks']; kp_field
  have e_fl : ks'.flags = ks.flags := by dsimp only [ks']; kp_field
  have e_va : ks'.vals = ks.vals := by dsimp only [ks']; kp_field
  have e_as : ks'.assump = ks.assump := by dsimp only [ks']; kp_field
  have e_un_a : ks'.units = ks.units := by dsimp only [ks']; kp_field
  have e_wh : ks'.whead = ks.whead := by dsimp only [ks']; kp_field
  have e_wn : ks'.wnext = ks.wnext := by dsimp only [ks']; kp_field
  have e_wb : ks'.wblit = ks.wblit := by dsimp only [ks']; kp_field
  have e_co : ks'.clOff = ks.clOff := by dsimp only [ks']; kp_field
  have e_cm : ks'.clMeta = ks.clMeta := by dsimp only [ks']; kp_field
  have e_ca : ks'.clAux = ks.clAux := by dsimp only [ks']; kp_field
  have e_ar : ks'.arena = ks.arena := by dsimp only [ks']; kp_field
  have hba : KittenBaseAssignOk ks' :=
    ⟨by rw [e_te, e_nv]; exact hinv.assign.trl_end_le,
      by rw [e_pr, e_te]; exact hpr,
      by rw [e_un, e_te, e_nv]; exact hinv.assign.unass_eq,
      by rw [e_nv, e_va]; exact hinv.assign.vals_dom,
      by rw [e_nv, e_va]; exact hinv.assign.vals_neg_iff,
      by rw [e_nv, e_va, e_te, e_tr]; exact hinv.assign.vals_nz_iff_trl,
      by unfold kittenTrailLits; rw [e_te, e_tr]; exact hinv.assign.trl_nodup,
      by unfold kittenTrailLits; rw [e_nv, e_te, e_tr]; exact hinv.assign.trl_lt,
      by rw [e_nv, e_la, e_lvl]; exact hinv.assign.trl_lvl_le,
      by rw [e_nv, e_va, e_la, e_rs]; exact hinv.assign.unass_lvl_zero,
      by rw [e_te, e_la, e_tr]; exact hinv.assign.trl_lvl_mono,
      by rw [e_te, e_la, e_tr, e_rs]; exact hinv.assign.dec_earliest,
      by unfold kittenOrigClauses kittenClauseLits kittenClauseOff kittenClauseSize kittenClauseMeta
         rw [e_te, e_tr, e_la, e_rs, e_va, e_on, e_nc, e_an, e_co, e_cm, e_ar]
         exact hinv.assign.lvl0_ok⟩
  have hcl : KittenClausesOk acap ks' := by
    have h0 := hinv.clauses
    have hcm_eq : ∀ c, kittenClauseMeta ks' c = kittenClauseMeta ks c := fun c => by
      simp [kittenClauseMeta, e_cm]
    have hsz_eq : ∀ c, kittenClauseSize ks' c = kittenClauseSize ks c := fun c => by
      simp [kittenClauseSize, hcm_eq]
    have his_eq : ∀ c, kittenClauseIsLrn ks' c = kittenClauseIsLrn ks c := fun c => by
      simp [kittenClauseIsLrn, hcm_eq]
    have hoff_eq : ∀ c, kittenClauseOff ks' c = kittenClauseOff ks c := fun c => by
      simp [kittenClauseOff, e_co]
    have hsp_eq : ∀ c, kittenClauseSpan ks' c = kittenClauseSpan ks c := fun c => by
      simp [kittenClauseSpan, hsz_eq, his_eq, kittenClauseAux, e_ca]
    have hlits_eq : ∀ c, kittenClauseLits ks' c = kittenClauseLits ks c := fun c => by
      simp [kittenClauseLits, hoff_eq, hsz_eq, e_ar]
    have hants_eq : ∀ c, kittenClauseAnts ks' c = kittenClauseAnts ks c := fun c => by
      simp [kittenClauseAnts, his_eq, hoff_eq, hsz_eq, kittenClauseAux, e_ca, e_ar]
    have horig_eq : kittenOrigClauses ks' = kittenOrigClauses ks :=
      kittenOrigClauses_eq_of e_on fun c _ => hlits_eq c
    refine ⟨h0.acap_ge, h0.acap_lt, by rw [e_ac]; exact h0.acap_eq,
      by rw [e_nv]; exact h0.nv_le, by rw [e_nc]; exact h0.nc_le,
      by rw [e_on, e_nc]; exact h0.orig_nc_le, by rw [e_on]; exact h0.orig_nc_max,
      by rw [e_al]; exact h0.alen_le, by rw [e_na]; exact h0.nassump_le,
      by rw [e_nu]; exact h0.nunits_le, by rw [e_nr]; exact h0.nres_le,
      by rw [e_nk]; exact h0.nkl_le, by rw [e_nn]; exact h0.nana_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc; rw [e_nc] at hc
      have hw := h0.cl_wf c hc
      rw [his_eq, hsz_eq, hoff_eq, hsp_eq, hlits_eq, horig_eq, hants_eq,
        List.map_congr_left (fun a _ => hlits_eq a), e_on, e_al, e_nv, e_an]
      exact hw
    · intro c1 c2 h12 h2; rw [e_nc] at h2
      rw [hoff_eq, hsp_eq, hoff_eq]; exact h0.cl_mono c1 c2 h12 h2
    · intro ui hui; rw [e_nu] at hui
      have hu := h0.units_ok ui hui
      dsimp only; rw [e_un_a, e_nc, hsz_eq]; exact hu
    · intro hi; rw [e_in] at hi
      have hinc := h0.incons_ok hi
      rw [e_in, e_nc, horig_eq, hlits_eq, e_va, e_la, e_an, e_rs]
      refine ⟨hinc.1, hinc.2.1, fun l hl => ?_⟩
      have hr := hinc.2.2 l hl
      refine ⟨hr.1, hr.2.1, fun ha => ?_⟩
      have hrr := hr.2.2 ha
      exact ⟨hrr.1, by rw [hlits_eq]; exact hrr.2⟩
    · intro hf; rw [e_fa] at hf
      have hfa := h0.failing_ok hf
      have hcm' : (fun ci => (kittenClauseMeta ks' ci &&& kmCore) != 0#32) =
          (fun ci => (kittenClauseMeta ks ci &&& kmCore) != 0#32) :=
        funext fun ci => by rw [hcm_eq]
      have hmp' : List.map (kittenClauseLits ks') = List.map (kittenClauseLits ks) :=
        congrArg List.map (funext hlits_eq)
      unfold kittenAssumpLits at hfa ⊢
      rwa [e_nc, hcm', hmp', e_na, e_as]
    · intro i hi; rw [e_na] at hi; rw [e_as, e_nv]; exact h0.assump_ok i hi
    · intro v hv; rw [e_nv] at hv; rw [e_fl]; exact h0.flags_clean v hv
  have hw : KittenWatchesOk ks' := by
    obtain ⟨ch, hc1, hc2, hc3, hc4⟩ := hinv.watches
    refine ⟨ch, by rw [e_nv]; exact hc1, hc2,
      fun l hl => by rw [e_wn, e_wh]; exact hc3 l (by rw [e_nv] at hl; exact hl),
      fun l hl w hw => by
        simpa only [e_nc, e_nv, e_wb, e_ar, kittenClauseSize, kittenClauseMeta, kittenClauseOff,
          e_cm, e_co] using hc4 l (by rw [e_nv] at hl; exact hl) w hw⟩
  have hsync' : KittenTrailSynced ks' := by
    intro i hi; rw [e_te] at hi; rw [e_tr, e_va]; exact hsync i hi
  have hrsn' : ReasonOk ks' := by
    intro i hi; rw [e_te] at hi
    simpa only [e_tr, e_rs, e_nc, kittenClauseLits, kittenClauseOff, kittenClauseSize,
      kittenClauseMeta, e_co, e_cm, e_ar] using hinv.reasons i hi
  exact ⟨⟨hsh', hcl, hw, hba, hrsn'⟩, hsync'⟩

private theorem list_flatten_set_sub_perm {α : Type} (xs : List (List α)) {l : Nat}
    (hi : l < xs.length) (done todo' : List α) (w0 : α)
    (heq : xs[l]'hi = done ++ w0 :: todo') :
    xs.flatten.Perm (w0 :: (xs.set l (done ++ todo')).flatten) := by
  induction xs generalizing l with
  | nil => simp at hi
  | cons x tl ih =>
    cases l with
    | zero =>
      simp only [List.getElem_cons_zero] at heq
      simp only [List.set_cons_zero, List.flatten_cons, heq, List.append_assoc]
      exact List.perm_middle
    | succ l' =>
      simp only [List.getElem_cons_succ] at heq
      simp only [List.set_cons_succ, List.flatten_cons]
      exact ((ih (by simp at hi; omega) heq).append_left x).trans List.perm_middle

private theorem list_flatten_nodup_getElem {α : Type} :
    ∀ {xs : List (List α)}, xs.flatten.Nodup → ∀ {i : Nat} (hi : i < xs.length),
      (xs[i]'hi).Nodup ∧ ∀ j, j ≠ i → (hj : j < xs.length) → ∀ a ∈ xs[i]'hi, a ∉ xs[j]'hj
  | [], _, i, hi => absurd hi (by simp)
  | x :: tl, hnd, 0, hi => by
    simp only [List.flatten_cons] at hnd
    have ha := List.nodup_append.mp hnd
    refine ⟨ha.1, fun j hne hj a hai haj => ?_⟩
    cases j with
    | zero => exact hne rfl
    | succ j' =>
      have hj' : j' < tl.length := by simp at hj; exact hj
      simp only [List.getElem_cons_zero] at hai
      simp only [List.getElem_cons_succ] at haj
      exact ha.2.2 a hai a (List.mem_flatten.mpr ⟨tl[j'], List.getElem_mem hj', haj⟩) rfl
  | x :: tl, hnd, i + 1, hi => by
    simp only [List.flatten_cons] at hnd
    have ha := List.nodup_append.mp hnd
    have hi' : i < tl.length := by simp at hi; exact hi
    have ihr := list_flatten_nodup_getElem ha.2.1 hi'
    refine ⟨ihr.1, fun j hne hj a hai haj => ?_⟩
    cases j with
    | zero =>
      simp only [List.getElem_cons_succ] at hai
      simp only [List.getElem_cons_zero] at haj
      exact ha.2.2 a haj a (List.mem_flatten.mpr ⟨tl[i], List.getElem_mem hi', hai⟩) rfl
    | succ j' =>
      have hj' : j' < tl.length := by simp at hj; exact hj
      exact ihr.2 j' (fun h => hne (congrArg Nat.succ h)) hj' a hai haj

private theorem trl_nodup_var_ne' {acap : Nat} {ks : KittenState} (hsh : ks.ShapesOk acap)
    (hnv : ks.nv.toNat ≤ kMaxV) (hba : KittenBaseAssignOk ks)
    {i j : Nat} (hi : i < ks.trl_end.toNat) (hj : j < ks.trl_end.toNat) (hne : i ≠ j) :
    (ks.trl[i]?.getD 0#32).toNat / 2 ≠ (ks.trl[j]?.getD 0#32).toNat / 2 := by
  have hlen : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hsh.trl_len]; have := hba.trl_end_le; unfold kMaxV at hnv; omega
  have hnd := hba.trl_nodup
  unfold kittenTrailLits at hnd
  rw [List.map_map] at hnd
  have hm_len : (List.map ((fun x => x / 2) ∘ BitVec.toNat)
      (ks.trl.take ks.trl_end.toNat)).length = ks.trl_end.toNat := by
    simp [List.length_take]; omega
  intro heq
  have hinj := list_nodup_getElem_inj hnd (by omega) (by omega)
    (show (List.map ((fun x => x / 2) ∘ BitVec.toNat) (ks.trl.take ks.trl_end.toNat))[i] =
        (List.map ((fun x => x / 2) ∘ BitVec.toNat) (ks.trl.take ks.trl_end.toNat))[j] by
      simp only [List.getElem_map, List.getElem_take, Function.comp_def]
      rw [List.getElem?_eq_getElem (by omega : i < ks.trl.length),
        List.getElem?_eq_getElem (by omega : j < ks.trl.length), Option.getD_some,
        Option.getD_some] at heq
      exact heq)
  exact hne hinj

/-- Unlinking node `w0` right after predecessor `u` in `WChain wn hd (pfx ++ u :: w0 :: todo')`
preserves `WChain` on `wn.set u wn[w0]`. -/
theorem wchain_bypass {wn : List (BitVec 32)} {hd nxt : BitVec 32}
    {pfx : List Nat} {u w0 : Nat} {todo' : List Nat}
    (hc : WChain wn hd (pfx ++ u :: w0 :: todo'))
    (hnd : (pfx ++ u :: w0 :: todo').Nodup)
    (hu : u < wn.length) (hw0 : w0 < wn.length) (hnxt : wn[w0]'hw0 = nxt) :
    WChain (wn.set u nxt) hd (pfx ++ [u] ++ todo') := by
  induction pfx generalizing hd with
  | nil =>
    simp only [List.nil_append, List.singleton_append] at hc hnd ⊢
    rcases WChain_cases hc with ⟨_, hc_nil⟩ | ⟨u', ws1, hu', hhd, hcons, htail⟩
    · cases hc_nil
    · obtain ⟨hu_eq, hws1⟩ := List.cons.inj hcons
      subst hhd hu_eq hws1
      rcases WChain_cases htail with ⟨_, hnil⟩ | ⟨w', ws2, hw', hw_eq, hcons2, htail2⟩
      · cases hnil
      · obtain ⟨hw0_eq, hws2⟩ := List.cons.inj hcons2
        subst hw0_eq hws2
        have hnd_u : u ∉ w0 :: todo' := (List.nodup_cons.mp hnd).1
        have hu_nt : u ∉ todo' := fun h => hnd_u (List.mem_cons_of_mem _ h)
        have htail_congr : WChain (wn.set u nxt) nxt todo' := by
          rw [← hnxt]
          exact htail2.congr fun y hy =>
            (List.getElem?_set_ne (fun h : u = y => hu_nt (h ▸ hy))).symm
        have hus : u < (wn.set u nxt).length := by simp [hu]
        exact WChain.cons hus (by rw [List.getElem_set_self]; exact htail_congr)
  | cons x xs ih =>
    simp only [List.cons_append] at hc hnd ⊢
    rcases WChain_cases hc with ⟨_, hc_nil⟩ | ⟨x', ws1, hx', hhd, hcons, htail⟩
    · cases hc_nil
    · obtain ⟨hx_eq, hws1⟩ := List.cons.inj hcons
      subst hhd hx_eq hws1
      have hnd_x := List.nodup_cons.mp hnd
      have hxu : x ≠ u := fun h => hnd_x.1 (h ▸ List.mem_append_right xs List.mem_cons_self)
      have hxs_s : x < (wn.set u nxt).length := by simp [hx']
      have hset_x : (wn.set u nxt)[x]'hxs_s = wn[x]'hx' := by
        rw [List.getElem_set_ne hxu.symm]
      have ih' := ih htail hnd_x.2
      rw [← hset_x] at ih'
      exact WChain.cons hxs_s ih'

/-- Cursor invariant while traversing watch list `whead[l]` (`done ++ todo = chains[l]`). -/
structure WChainCursor (ks : KittenState) (l : Nat) (chains : List (List Nat))
    (done todo : List Nat) (prev w : BitVec 32) : Prop where
  len_eq : chains.length = 2 * ks.nv.toNat
  nodup : chains.flatten.Nodup
  chain_l : chains[l]?.getD [] = done ++ todo
  chains_wc : ∀ x < 2 * ks.nv.toNat,
    WChain ks.wnext (ks.whead[x]?.getD 0xFFFFFFFF#32) (chains[x]?.getD [])
  chains_bnd : ∀ x < 2 * ks.nv.toNat, ∀ u ∈ chains[x]?.getD [],
    u < 2 * ks.nc.toNat ∧ 2 ≤ kittenClauseSize ks (u / 2) ∧
    (ks.arena[kittenClauseOff ks (u / 2) + (u % 2)]?.getD 0#32).toNat = x ∧
    (ks.wblit[u]?.getD 0#32).toNat < 2 * ks.nv.toNat
  tail_wc : WChain ks.wnext w todo
  prev_rel : (done = [] ∧ prev = 0xFFFFFFFF#32 ∧ ks.whead[l]?.getD 0xFFFFFFFF#32 = w) ∨
    (∃ pfx u, done = pfx ++ [u] ∧ prev = BitVec.ofNat 32 u ∧
      u < ks.wnext.length ∧ ks.wnext[u]?.getD 0xFFFFFFFF#32 = w)

theorem WChainCursor.watchesOk {ks : KittenState} {l : Nat} {chains : List (List Nat)}
    {done todo : List Nat} {prev w : BitVec 32}
    (wc : WChainCursor ks l chains done todo prev w) : KittenWatchesOk ks :=
  ⟨chains, wc.len_eq, wc.nodup, wc.chains_wc, wc.chains_bnd⟩

theorem WChainCursor.init {acap : Nat} {ks : KittenState} (hsh : ks.ShapesOk acap)
    (hnv : ks.nv.toNat ≤ kMaxV) (hw : KittenWatchesOk ks) {l : Nat} (hl : l < 2 * ks.nv.toNat) :
    ∃ chains, WChainCursor ks l chains [] (chains[l]?.getD []) 0xFFFFFFFF#32
      (ks.whead[l]?.getD 0#32) := by
  obtain ⟨chains, hlen, hnd, hwc, hbnd⟩ := hw
  have hwh_len : l < ks.whead.length := by rw [hsh.whead_len]; unfold kMaxV at hnv; omega
  have hwh_eq : ks.whead[l]?.getD 0#32 = ks.whead[l]?.getD 0xFFFFFFFF#32 := by
    rw [List.getElem?_eq_getElem hwh_len]; rfl
  rw [hwh_eq]
  exact ⟨chains, hlen, hnd, rfl, hwc, hbnd, hwc l hl, Or.inl ⟨rfl, rfl, rfl⟩⟩

theorem WChainCursor.step_unfold {acap : Nat} {ks : KittenState} (_hsh : ks.ShapesOk acap)
    (hnc : ks.nc.toNat ≤ kMaxCl) {l : Nat} (hl : l < 2 * ks.nv.toNat)
    {chains : List (List Nat)} {done todo : List Nat} {prev w : BitVec 32}
    (wc : WChainCursor ks l chains done todo prev w) (hne : w ≠ 0xFFFFFFFF#32) :
    ∃ w0 todo', w0 < ks.wnext.length ∧
      todo = w0 :: todo' ∧ w = BitVec.ofNat 32 w0 ∧ w0 < 2 * ks.nc.toNat ∧ w0 < 1792 ∧
      w.toNat = w0 ∧ (w >>> (1 : Nat)).toNat = w0 / 2 ∧ (w &&& 1#32).toNat = w0 % 2 ∧
      2 ≤ kittenClauseSize ks (w0 / 2) ∧
      (ks.arena[kittenClauseOff ks (w0 / 2) + (w0 % 2)]?.getD 0#32).toNat = l ∧
      (ks.wblit[w0]?.getD 0#32).toNat < 2 * ks.nv.toNat ∧
      WChain ks.wnext (ks.wnext[w0]?.getD 0#32) todo' := by
  obtain ⟨w0, todo', hw0, htd, hw_eq, htail⟩ := WChain_getElem_of_eq wc.tail_wc hne
  have hm_l : w0 ∈ chains[l]?.getD [] := by
    rw [wc.chain_l, htd]; exact List.mem_append_right _ List.mem_cons_self
  have hb := wc.chains_bnd l hl w0 hm_l
  have hw0_1792 : w0 < 1792 := by unfold kMaxCl at hnc; omega
  have hw_tn : w.toNat = w0 := by
    rw [hw_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hw_div2 : (w >>> (1 : Nat)).toNat = w0 / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one, hw_tn]
  have hw_mod2 : (w &&& 1#32).toNat = w0 % 2 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod w.toNat 1, hw_tn]
  have hnxt_eq : ks.wnext[w0]?.getD 0#32 = ks.wnext[w0]'hw0 := by
    rw [List.getElem?_eq_getElem hw0, Option.getD_some]
  refine ⟨w0, todo', hw0, htd, hw_eq, hb.1, hw0_1792, hw_tn, hw_div2, hw_mod2,
    hb.2.1, hb.2.2.1, hb.2.2.2, ?_⟩
  rw [hnxt_eq]; exact htail

/-- Updating `wblit[w0] := other` keeps node `w0` on list `l` and advances `(prev, w)` to
`(w, nxt)`. -/
theorem kittenWatchKeep_preserves {acap : Nat} {ks : KittenState}
    (hsh : ks.ShapesOk acap) (hinv : ks.Inv acap)
    {l : Nat} (hl : l < 2 * ks.nv.toNat) {chains : List (List Nat)}
    {done todo' : List Nat} {prev : BitVec 32} {w0 : Nat}
    (wc : WChainCursor ks l chains done (w0 :: todo') prev (BitVec.ofNat 32 w0))
    {other : BitVec 32} (hoth : other.toNat < 2 * ks.nv.toNat) :
    let w := BitVec.ofNat 32 w0
    let nxt := ks.wnext[w0]?.getD 0#32
    let ks' := ks.putArr .wblit w0 other
    ks'.Inv acap ∧
    WChainCursor ks' l chains (done ++ [w0]) todo' w nxt ∧
    ks'.nv = ks.nv ∧ ks'.nc = ks.nc ∧ ks'.orig_nc = ks.orig_nc ∧ ks'.lvl = ks.lvl ∧
    ks'.prop = ks.prop ∧ ks'.trl_end = ks.trl_end ∧ ks'.unass = ks.unass ∧
    ks'.incons = ks.incons ∧ ks'.failing = ks.failing ∧ ks'.ante = ks.ante ∧
    ks'.nassump = ks.nassump ∧ ks'.assump = ks.assump ∧ ks'.vals = ks.vals ∧
    ks'.lvlArr = ks.lvlArr ∧ ks'.rsn = ks.rsn ∧ ks'.trl = ks.trl ∧
    ks'.clOff = ks.clOff ∧ ks'.clMeta = ks.clMeta ∧ ks'.clAux = ks.clAux ∧
    ks'.arena = ks.arena := by
  intro w nxt ks'
  have hsh' : ks'.ShapesOk acap := hsh.putArr .wblit w0 other
  have hnc := hinv.clauses.nc_le
  have hm_l : w0 ∈ chains[l]?.getD [] := by
    rw [wc.chain_l]; exact List.mem_append_right _ List.mem_cons_self
  have hb0 := wc.chains_bnd l hl w0 hm_l
  have hw0_nc : w0 < 2 * ks.nc.toNat := hb0.1
  have hwb_len : w0 < ks.wblit.length := by rw [hsh.wblit_len]; unfold kMaxCl at hnc; omega
  have hwn_len : w0 < ks.wnext.length := by rw [hsh.wnext_len]; unfold kMaxCl at hnc; omega
  have hnxt_eq : ks.wnext[w0]?.getD 0#32 = ks.wnext[w0]?.getD 0xFFFFFFFF#32 := by
    rw [List.getElem?_eq_getElem hwn_len]; rfl
  rcases WChain_cases wc.tail_wc with ⟨_, hnil⟩ | ⟨w0', todo'', hw0', hw_eq, hcons, htail'⟩
  · cases hnil
  · obtain ⟨_, htd_eq⟩ := List.cons.inj hcons
    subst htd_eq
    have hw0_eq : w0 = w0' := by
      have ht := congrArg BitVec.toNat hw_eq
      have h1 : w0 < 2 ^ 32 := by unfold kMaxCl at hnc; omega
      have hwn' : w0' < 1792 := by rw [hsh.wnext_len] at hw0'; exact hw0'
      have h2 : w0' < 2 ^ 32 := by omega
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at ht
      exact ht
    subst hw0_eq
    have wc' : WChainCursor ks' l chains (done ++ [w0]) todo' w nxt := by
      refine ⟨wc.len_eq, wc.nodup, ?_, wc.chains_wc, ?_, ?_, Or.inr ⟨done, w0, rfl, rfl,
        hwn_len, hnxt_eq.symm⟩⟩
      · rw [wc.chain_l]; simp
      · intro x hx u hu
        have hbu := wc.chains_bnd x hx u hu
        by_cases hu0 : u = w0
        · have hxl : x = l := by
            by_cases hne : x = l
            · exact hne
            · exfalso
              have hx_len : x < chains.length := by rw [wc.len_eq]; exact hx
              have hl_len : l < chains.length := by rw [wc.len_eq]; exact hl
              have hnd := (list_flatten_nodup_getElem wc.nodup hx_len).2 l (Ne.symm hne) hl_len
                w0
              rw [List.getElem?_eq_getElem hx_len, Option.getD_some] at hu
              rw [List.getElem?_eq_getElem hl_len, Option.getD_some] at hm_l
              exact hnd (hu0 ▸ hu) hm_l
          subst hxl
          rw [hu0]; exact ⟨hb0.1, hb0.2.1, hb0.2.2.1, by
            change ((ks.wblit.set w0 other)[w0]?.getD 0#32).toNat < 2 * ks.nv.toNat
            rw [List.getElem?_set_self hwb_len, Option.getD_some]; exact hoth⟩
        · exact ⟨hbu.1, hbu.2.1, hbu.2.2.1, by
            change ((ks.wblit.set w0 other)[u]?.getD 0#32).toNat < 2 * ks.nv.toNat
            rw [List.getElem?_set_ne (Ne.symm hu0)]; exact hbu.2.2.2⟩
      · change WChain ks.wnext nxt todo'
        have hget : nxt = ks.wnext[w0]'hw0' := by
          dsimp only [nxt]; rw [List.getElem?_eq_getElem hw0', Option.getD_some]
        rw [hget]; exact htail'
    have hcl' : KittenClausesOk acap ks' := by
      have h0 := hinv.clauses
      refine ⟨h0.acap_ge, h0.acap_lt, h0.acap_eq, h0.nv_le, h0.nc_le, h0.orig_nc_le,
        h0.orig_nc_max, h0.alen_le, h0.nassump_le, h0.nunits_le, h0.nres_le, h0.nkl_le,
        h0.nana_le, h0.cl_wf, h0.cl_mono, h0.units_ok, h0.incons_ok, h0.failing_ok,
        h0.assump_ok, h0.flags_clean⟩
    have hba' : KittenBaseAssignOk ks' := by
      have h0 := hinv.assign
      refine ⟨h0.trl_end_le, h0.prop_le, h0.unass_eq, h0.vals_dom, h0.vals_neg_iff,
        h0.vals_nz_iff_trl, h0.trl_nodup, h0.trl_lt, h0.trl_lvl_le, h0.unass_lvl_zero,
        h0.trl_lvl_mono, h0.dec_earliest, h0.lvl0_ok⟩
    have hrsn' : ReasonOk ks' := hinv.reasons
    exact ⟨⟨hsh', hcl', wc'.watchesOk, hba', hrsn'⟩, wc',
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl⟩

/-- Unlinking node `w0` (`slot = w0 % 2`) from watch list `l`, swapping `arena[off+slot] ↔
arena[off+ri]` (`ri ≥ 2`), and prepending `w0` to `whead[repl]` preserves `KittenInv`,
perm-equivalent clauses, and advances the cursor to `(prev, nxt)`. -/
theorem kittenWatchReloc_preserves {acap : Nat} {ks : KittenState}
    (hsh : ks.ShapesOk acap) (hinv : ks.Inv acap)
    {l : Nat} (hl : l < 2 * ks.nv.toNat) {chains : List (List Nat)}
    {done todo' : List Nat} {prev : BitVec 32} {w0 : Nat}
    (wc : WChainCursor ks l chains done (w0 :: todo') prev (BitVec.ofNat 32 w0))
    {ri : Nat} (hri_ge : 2 ≤ ri) (hri_lt : ri < kittenClauseSize ks (w0 / 2))
    {repl other : BitVec 32} (hrepl_ne : repl.toNat ≠ l)
    (hother_eq : other = ks.arena[kittenClauseOff ks (w0 / 2) + ((w0 % 2) ^^^ 1)]?.getD 0#32)
    (hrepl_eq : repl = ks.arena[kittenClauseOff ks (w0 / 2) + ri]?.getD 0#32) :
    let w := BitVec.ofNat 32 w0
    let nxt := ks.wnext[w0]?.getD 0#32
    let cid := w0 / 2
    let slot := w0 % 2
    let off := kittenClauseOff ks cid
    let ar' := (ks.arena.set (off + slot) repl).set (off + ri) (BitVec.ofNat 32 l)
    let wh1 := if prev = 0xFFFFFFFF#32 then ks.whead.set l nxt else ks.whead
    let wn1 := if prev = 0xFFFFFFFF#32 then ks.wnext else ks.wnext.set prev.toNat nxt
    let ks1 : KittenState := { ks with arena := ar', whead := wh1, wnext := wn1 }
    let ks' := kittenWatchStep0 ks1 w repl other
    ks'.Inv acap ∧
    (∀ c < ks.nc.toNat, (kittenClauseLits ks' c).Perm (kittenClauseLits ks c)) ∧
    (∀ c < ks.nc.toNat, c ≠ cid → kittenClauseLits ks' c = kittenClauseLits ks c) ∧
    (∀ c < ks.nc.toNat, kittenClauseAnts ks' c = kittenClauseAnts ks c) ∧
    KittenCnfPermEquiv (kittenOrigClauses ks') (kittenOrigClauses ks) ∧
    (∃ chains', WChainCursor ks' l chains' done todo' prev nxt) ∧
    ks'.nv = ks.nv ∧ ks'.nc = ks.nc ∧ ks'.orig_nc = ks.orig_nc ∧ ks'.lvl = ks.lvl ∧
    ks'.prop = ks.prop ∧ ks'.trl_end = ks.trl_end ∧ ks'.unass = ks.unass ∧
    ks'.incons = ks.incons ∧ ks'.failing = ks.failing ∧ ks'.ante = ks.ante ∧
    ks'.nassump = ks.nassump ∧ ks'.assump = ks.assump ∧ ks'.vals = ks.vals ∧
    ks'.lvlArr = ks.lvlArr ∧ ks'.rsn = ks.rsn ∧ ks'.trl = ks.trl ∧
    ks'.clOff = ks.clOff ∧ ks'.clMeta = ks.clMeta ∧ ks'.clAux = ks.clAux ∧
    ks'.flags = ks.flags := by
  intro w nxt cid slot off ar' wh1 wn1 ks1 ks'
  have hnv := hinv.clauses.nv_le
  have hnc := hinv.clauses.nc_le
  have hch_l : l < chains.length := by rw [wc.len_eq]; exact hl
  have hm_l : w0 ∈ chains[l]?.getD [] := by
    rw [wc.chain_l]; exact List.mem_append_right _ List.mem_cons_self
  have hb0 := wc.chains_bnd l hl w0 hm_l
  have hcid_lt : cid < ks.nc.toNat := by dsimp only [cid]; omega
  have hwf_c := hinv.clauses.cl_wf cid hcid_lt
  have hri_lt' : ri < kittenClauseSize ks cid := hri_lt
  have hsz_ge : 2 ≤ kittenClauseSize ks cid := hb0.2.1
  have hslot_lt : slot < 2 := Nat.mod_lt w0 (by decide)
  have hother_slot_lt : (slot ^^^ 1) < 2 := by
    rcases Nat.mod_two_eq_zero_or_one w0 with h | h <;> simp [slot, h]
  have hoff_le : off + kittenClauseSpan ks cid ≤ ks.alen.toNat := hwf_c.2.2.1
  have hsp_ge : kittenClauseSize ks cid ≤ kittenClauseSpan ks cid := by
    unfold kittenClauseSpan; omega
  have har_len : ks.arena.length = acap := hsh.arena_len
  have hal_le : ks.alen.toNat ≤ acap := hinv.clauses.alen_le
  have hwn_len : w0 < ks.wnext.length := by rw [hsh.wnext_len]; unfold kMaxCl at hnc; omega
  have hwh_len : l < ks.whead.length := by rw [hsh.whead_len]; unfold kMaxV at hnv; omega
  have hnxt_eq : nxt = ks.wnext[w0]'hwn_len := by
    dsimp only [nxt]; rw [List.getElem?_eq_getElem hwn_len, Option.getD_some]
  have har_slot : ks.arena[off + slot]'(by dsimp only [off]; omega) = BitVec.ofNat 32 l := by
    have ha := hb0.2.2.1
    rw [List.getElem?_eq_getElem (by dsimp only [off]; omega : off + slot < ks.arena.length),
      Option.getD_some] at ha
    exact BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold kMaxV at hnv; omega)]; exact ha)
  have hrepl_lt_ar : off + ri < ks.arena.length := by dsimp only [off]; omega
  have hrepl_mem : repl.toNat ∈ kittenClauseLits ks cid := by
    rw [hrepl_eq]
    change (ks.arena[kittenClauseOff ks cid + ri]?.getD 0#32).toNat ∈ kittenClauseLits ks cid
    rw [List.getElem?_eq_getElem hrepl_lt_ar, Option.getD_some]
    unfold kittenClauseLits; rw [List.mem_map]
    refine ⟨ks.arena[off + ri]'hrepl_lt_ar, ?_, rfl⟩
    rw [List.mem_iff_getElem]
    exact ⟨ri, by
        dsimp only [off] at hrepl_lt_ar hoff_le
        simp [List.length_take, List.length_drop, har_len]; omega,
      by dsimp only [off]; simp [List.getElem_take, List.getElem_drop]⟩
  have hrepl_nv : repl.toNat < 2 * ks.nv.toNat := hwf_c.2.2.2.1 _ hrepl_mem
  have hother_lt_ar : off + (slot ^^^ 1) < ks.arena.length := by dsimp only [off]; omega
  have hother_mem : other.toNat ∈ kittenClauseLits ks cid := by
    rw [hother_eq]
    change (ks.arena[kittenClauseOff ks cid + (slot ^^^ 1)]?.getD 0#32).toNat ∈
      kittenClauseLits ks cid
    rw [List.getElem?_eq_getElem hother_lt_ar, Option.getD_some]
    unfold kittenClauseLits; rw [List.mem_map]
    refine ⟨ks.arena[off + (slot ^^^ 1)]'hother_lt_ar, ?_, rfl⟩
    rw [List.mem_iff_getElem]
    exact ⟨slot ^^^ 1, by
        dsimp only [off] at hother_lt_ar hoff_le
        simp [List.length_take, List.length_drop, har_len]; omega,
      by dsimp only [off]; simp [List.getElem_take, List.getElem_drop]⟩
  have hother_nv : other.toNat < 2 * ks.nv.toNat := hwf_c.2.2.2.1 _ hother_mem
  have har'_eq : ar' = (ks.arena.set (off + slot) (ks.arena[off + ri]'hrepl_lt_ar)).set
      (off + ri) (ks.arena[off + slot]'(by dsimp only [off]; omega)) := by
    dsimp only [ar']
    rw [har_slot, hrepl_eq]
    change (ks.arena.set (off + slot) (ks.arena[off + ri]?.getD 0#32)).set (off + ri) _ = _
    rw [List.getElem?_eq_getElem hrepl_lt_ar, Option.getD_some]
  have hsh1 : ks1.ShapesOk acap := by
    refine ⟨hsh.hdrTail_len, hsh.lvlArr_len, hsh.rsn_len, hsh.qprev_len, hsh.qnext_len,
      hsh.qstampArr_len, hsh.trl_len, hsh.flags_len, hsh.vals_len, hsh.assump_len, hsh.ana_len,
      hsh.kl_len, hsh.units_len, hsh.res_len, ?_, ?_, hsh.wblit_len, hsh.clOff_len,
      hsh.clMeta_len, hsh.clAux_len, ?_⟩
    · dsimp only [ks1, wh1]; split <;> simp [List.length_set, hsh.whead_len]
    · dsimp only [ks1, wn1]; split <;> simp [List.length_set, hsh.wnext_len]
    · simp [ks1, ar', List.length_set, hsh.arena_len]
  have hsh' : ks'.ShapesOk acap := kittenWatchStep0_preserves_shapes hsh1 w repl other
  have hlits_other :
      ∀ c < ks.nc.toNat, c ≠ cid → kittenClauseLits ks' c = kittenClauseLits ks c := by
    intro c hclt hcne
    change kittenClauseLits ks1 c = kittenClauseLits ks c
    unfold kittenClauseLits
    change ((ar'.drop (kittenClauseOff ks c)).take (kittenClauseSize ks c)).map BitVec.toNat =
      ((ks.arena.drop (kittenClauseOff ks c)).take (kittenClauseSize ks c)).map BitVec.toNat
    have hout : ∀ idx, idx = off + slot ∨ idx = off + ri →
        idx < kittenClauseOff ks c ∨ kittenClauseOff ks c + kittenClauseSize ks c ≤ idx := by
      intro idx hidx
      by_cases hcl : c < cid
      · right
        have hm := hinv.clauses.cl_mono c cid hcl hcid_lt
        have hsp := show kittenClauseSize ks c ≤ kittenClauseSpan ks c by
          unfold kittenClauseSpan; omega
        change kittenClauseOff ks c + kittenClauseSpan ks c ≤ off at hm
        dsimp only [off] at hm ⊢
        rcases hidx with rfl | rfl <;> omega
      · left
        have hm := hinv.clauses.cl_mono cid c (by omega) hclt
        change off + kittenClauseSpan ks cid ≤ kittenClauseOff ks c at hm
        dsimp only [off] at hm ⊢
        rcases hidx with rfl | rfl <;> omega
    dsimp only [ar']
    rw [drop_take_set_out _ _ (hout _ (Or.inr rfl)),
      drop_take_set_out _ _ (hout _ (Or.inl rfl))]
  have hlits_perm_all : ∀ c < ks.nc.toNat,
      (kittenClauseLits ks' c).Perm (kittenClauseLits ks c) := by
    intro c hclt
    by_cases hccid : c = cid
    · subst hccid
      change (kittenClauseLits ks1 cid).Perm (kittenClauseLits ks cid)
      unfold kittenClauseLits
      change (((ar'.drop off).take (kittenClauseSize ks cid)).map BitVec.toNat).Perm
        (((ks.arena.drop off).take (kittenClauseSize ks cid)).map BitVec.toNat)
      rw [har'_eq]
      exact (drop_take_set_swap ks.arena (off := off) (sz := kittenClauseSize ks cid)
        (p := slot) (q := ri) (by omega) hri_lt' (by dsimp only [off]; omega)).map _
    · rw [hlits_other c hclt hccid]
  have hants_all : ∀ c < ks.nc.toNat, kittenClauseAnts ks' c = kittenClauseAnts ks c := by
    intro c hclt
    change kittenClauseAnts ks1 c = kittenClauseAnts ks c
    unfold kittenClauseAnts
    change (if kittenClauseIsLrn ks c then
        ((ar'.drop (kittenClauseOff ks c + kittenClauseSize ks c)).take
          (kittenClauseAux ks c)).map BitVec.toNat else [c]) = _
    split
    · have hout : ∀ idx, idx = off + slot ∨ idx = off + ri →
          idx < kittenClauseOff ks c + kittenClauseSize ks c ∨
            kittenClauseOff ks c + kittenClauseSize ks c + kittenClauseAux ks c ≤ idx := by
        intro idx hidx
        by_cases hcc : c = cid
        · subst hcc; left; dsimp only [off] at hidx; rcases hidx with rfl | rfl <;> omega
        · by_cases hcl : c < cid
          · right
            have hm := hinv.clauses.cl_mono c cid hcl hcid_lt
            have : kittenClauseSize ks c + kittenClauseAux ks c ≤ kittenClauseSpan ks c := by
              unfold kittenClauseSpan; simp [*]
            change kittenClauseOff ks c + kittenClauseSpan ks c ≤ off at hm
            dsimp only [off] at hm ⊢
            rcases hidx with rfl | rfl <;> omega
          · left
            have hm := hinv.clauses.cl_mono cid c (by omega) hclt
            change off + kittenClauseSpan ks cid ≤ kittenClauseOff ks c at hm
            dsimp only [off] at hm ⊢
            rcases hidx with rfl | rfl <;> omega
      dsimp only [ar']
      rw [drop_take_set_out _ _ (hout _ (Or.inr rfl)),
        drop_take_set_out _ _ (hout _ (Or.inl rfl))]
    · rfl
  have e_on : ks'.orig_nc = ks.orig_nc := rfl
  have e_nc : ks'.nc = ks.nc := rfl
  have e_nv : ks'.nv = ks.nv := rfl
  have e_cm : ∀ c, kittenClauseMeta ks' c = kittenClauseMeta ks c := fun _ => rfl
  have horig_perm : KittenCnfPermEquiv (kittenOrigClauses ks') (kittenOrigClauses ks) := by
    refine ⟨by simp [kittenOrigClauses, e_on], fun i hi => ?_⟩
    unfold kittenOrigClauses at hi ⊢
    simp only [List.length_map, List.length_range] at hi
    rw [e_on] at hi
    rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD]
    have hl1 : i < ((List.range ks'.orig_nc.toNat).map (kittenClauseLits ks')).length := by
      simp [e_on, hi]
    have hl2 : i < ((List.range ks.orig_nc.toNat).map (kittenClauseLits ks)).length := by
      simp [hi]
    rw [List.getElem?_eq_getElem hl1, List.getElem?_eq_getElem hl2,
      Option.getD_some, Option.getD_some]
    simp only [List.getElem_map, List.getElem_range]
    exact hlits_perm_all i (Nat.lt_of_lt_of_le hi hinv.clauses.orig_nc_le)
  have horig_ent_iff : ∀ cl,
      (cnfOfClauses (kittenOrigClauses ks')).EntailsClause cl ↔
        (cnfOfClauses (kittenOrigClauses ks)).EntailsClause cl := fun cl =>
    ⟨fun h => horig_perm.entailsClause h, fun h => horig_perm.symm.entailsClause h⟩
  have hcl' : KittenClausesOk acap ks' := by
    have h0 := hinv.clauses
    refine ⟨h0.acap_ge, h0.acap_lt, h0.acap_eq, h0.nv_le, h0.nc_le, h0.orig_nc_le, h0.orig_nc_max,
      h0.alen_le, h0.nassump_le, h0.nunits_le, h0.nres_le, h0.nkl_le, h0.nana_le,
      ?_, ?_, ?_, ?_, ?_, h0.assump_ok, h0.flags_clean⟩
    · intro c hc
      have hc' : c < ks.nc.toNat := hc
      have hw := h0.cl_wf c hc'
      have hp := hlits_perm_all c hc'
      have hmem : ∀ l, l ∈ kittenClauseLits ks' c ↔ l ∈ kittenClauseLits ks c := fun l => hp.mem_iff
      refine ⟨hw.1, hw.2.1, hw.2.2.1, fun l hl => hw.2.2.2.1 l ((hmem l).mp hl), ?_, ?_⟩
      · rw [horig_ent_iff, CNF.entails_clause_def]
        intro α hα
        exact (cnfClause_sat_perm α hp).mpr (CNF.entails_clause_def.mp hw.2.2.2.2.1 α hα)
      · intro hante hge
        have ⟨ha1, ha2⟩ := hw.2.2.2.2.2 hante hge
        refine ⟨by rw [hants_all c hc']; exact ha1, ?_⟩
        rw [hants_all c hc', CNF.entails_clause_def]
        intro α hα
        have hp_cnf : KittenCnfPermEquiv ((kittenClauseAnts ks c).map (kittenClauseLits ks'))
            ((kittenClauseAnts ks c).map (kittenClauseLits ks)) := by
          refine ⟨by simp, fun i hi => ?_⟩
          simp only [List.length_map] at hi
          rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
            List.getElem?_eq_getElem (by simpa using hi),
            List.getElem?_eq_getElem (by simpa using hi), Option.getD_some, Option.getD_some]
          simp only [List.getElem_map]
          exact hlits_perm_all _ (Nat.lt_trans (ha1 _ (List.getElem_mem hi)) hc')
        exact (cnfClause_sat_perm α hp).mpr
          (CNF.entails_clause_def.mp ha2 α ((hp_cnf.sat_iff α).mp hα))
    · exact h0.cl_mono
    · intro ui hui; exact h0.units_ok ui hui
    · intro hi
      have hinc := h0.incons_ok hi
      have hp_inc := hlits_perm_all ks.incons.toNat hinc.1
      refine ⟨hinc.1, CNF.unsat_iff_not_sat.mpr (fun α hα =>
          (CNF.unsat_iff_not_sat.mp hinc.2.1) α ((horig_perm.sat_iff α).mp hα)), fun l hl => ?_⟩
      have hl' := hp_inc.mem_iff.mp hl
      have hr := hinc.2.2 l hl'
      refine ⟨hr.1, hr.2.1, fun hante => ?_⟩
      have hrr := hr.2.2 hante
      let rr := (ks.rsn[l / 2]?.getD 0xFFFFFFFF#32).toNat
      have hne_c : rr ≠ cid := by
        intro heq
        have hlen1 := congrArg List.length hrr.2
        have hbd_r : kittenClauseOff ks rr + kittenClauseSize ks rr ≤ ks.arena.length := by
          have := (h0.cl_wf _ hrr.1).2.2.1; unfold kittenClauseSpan at this
          dsimp only [rr]; rw [har_len]; omega
        have hsz1 : kittenClauseSize ks cid = 1 := by
          unfold kittenClauseLits at hlen1
          dsimp only [rr] at hbd_r heq
          rw [List.length_map, List.length_take, List.length_drop,
            Nat.min_eq_left (by omega)] at hlen1
          rw [← heq]; exact hlen1
        omega
      have hlits_rr : kittenClauseLits ks' rr = kittenClauseLits ks rr :=
        hlits_other rr hrr.1 hne_c
      exact ⟨hrr.1, by change kittenClauseLits ks' rr = [l ^^^ 1]; rw [hlits_rr]; exact hrr.2⟩
    · intro hf
      have hfa := h0.failing_ok hf
      have hp_fail : KittenCnfPermEquiv
          (((List.range ks'.nc.toNat).filter fun ci =>
            (kittenClauseMeta ks' ci &&& kmCore) != 0#32).map (kittenClauseLits ks'))
          (((List.range ks.nc.toNat).filter fun ci =>
            (kittenClauseMeta ks ci &&& kmCore) != 0#32).map (kittenClauseLits ks)) := by
        have hflt : (List.range ks'.nc.toNat).filter
              (fun ci => (kittenClauseMeta ks' ci &&& kmCore) != 0#32) =
            (List.range ks.nc.toNat).filter
              (fun ci => (kittenClauseMeta ks ci &&& kmCore) != 0#32) := by
          rw [e_nc]; exact List.filter_congr fun i _ => by rw [e_cm]
        refine ⟨by simp [hflt], fun i hi => ?_⟩
        simp only [List.length_map, hflt] at hi
        rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
          List.getElem?_eq_getElem (by simp [hflt, hi]),
          List.getElem?_eq_getElem (by simp [hi]), Option.getD_some, Option.getD_some]
        simp only [List.getElem_map, hflt]
        have hmem_f := List.mem_filter.mp (List.getElem_mem hi)
        rw [List.mem_range] at hmem_f
        exact hlits_perm_all _ hmem_f.1
      exact (hp_fail.unsat_iff (unitsCnf (kittenAssumpLits ks))).mpr hfa
  have hba' : KittenBaseAssignOk ks' := by
    have h0 := hinv.assign
    refine ⟨h0.trl_end_le, h0.prop_le, h0.unass_eq, h0.vals_dom, h0.vals_neg_iff,
      h0.vals_nz_iff_trl, h0.trl_nodup, h0.trl_lt, h0.trl_lvl_le, h0.unass_lvl_zero,
      h0.trl_lvl_mono, h0.dec_earliest, fun i hi hlv => ?_⟩
    have hl0 := h0.lvl0_ok i hi hlv
    have hnt_ent : (cnfOfClauses (kittenOrigClauses ks')).EntailsClause
        (cnfClause [(ks.trl[i]?.getD 0#32).toNat]) :=
      horig_perm.symm.entailsClause hl0.2.2.2.1
    refine ⟨hl0.1, hl0.2.1, hl0.2.2.1, hnt_ent, fun hante => ?_⟩
    have hrr := hl0.2.2.2.2 hante
    let rr := (ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat
    have hne_c : rr ≠ cid := by
      intro heq
      have hlen1 := congrArg List.length hrr.2
      have hbd_r : kittenClauseOff ks rr + kittenClauseSize ks rr ≤ ks.arena.length := by
        have := (hinv.clauses.cl_wf _ hrr.1).2.2.1; unfold kittenClauseSpan at this
        dsimp only [rr]; rw [har_len]; omega
      have hsz1 : kittenClauseSize ks cid = 1 := by
        unfold kittenClauseLits at hlen1
        dsimp only [rr] at hbd_r heq
        rw [List.length_map, List.length_take, List.length_drop,
          Nat.min_eq_left (by omega)] at hlen1
        rw [← heq]; exact hlen1
      omega
    have hlits_rr : kittenClauseLits ks' rr = kittenClauseLits ks rr :=
      hlits_other rr hrr.1 hne_c
    exact ⟨hrr.1, by
      change kittenClauseLits ks' rr = [(ks.trl[i]?.getD 0#32).toNat]
      rw [hlits_rr]; exact hrr.2⟩
  have hrsn' : ReasonOk ks' := by
    intro i hi
    have hro := hinv.reasons i hi
    dsimp only at hro ⊢
    rcases hro with hdec | ⟨hr_lt, hmem, hall⟩
    · exact Or.inl hdec
    · right
      have hp := hlits_perm_all _ hr_lt
      exact ⟨hr_lt, hp.mem_iff.mpr hmem, fun x hx => hall x (hp.mem_iff.mp hx)⟩
  let chains1 := chains.set l (done ++ todo')
  have hch1_len : chains1.length = 2 * ks1.nv.toNat := by
    rw [List.length_set]; exact wc.len_eq
  have hch_l_eq : chains[l]'hch_l = done ++ w0 :: todo' := by
    have := wc.chain_l
    rwa [List.getElem?_eq_getElem hch_l, Option.getD_some] at this
  have hperm1 : chains.flatten.Perm (w0 :: chains1.flatten) :=
    list_flatten_set_sub_perm chains hch_l done todo' w0 hch_l_eq
  have hnd_cons : (w0 :: chains1.flatten).Nodup := hperm1.nodup_iff.mp wc.nodup
  have hw0_not_in : w0 ∉ chains1.flatten := (List.nodup_cons.mp hnd_cons).1
  have hch1_nd : chains1.flatten.Nodup := (List.nodup_cons.mp hnd_cons).2
  have hch1_sub : ∀ x < 2 * ks.nv.toNat, ∀ u ∈ chains1[x]?.getD [], u ∈ chains[x]?.getD [] := by
    intro x hx u hu
    have hx1 : x < chains1.length := by rw [hch1_len]; exact hx
    have hx0 : x < chains.length := by rw [wc.len_eq]; exact hx
    rw [List.getElem?_eq_getElem hx1, Option.getD_some] at hu
    rw [List.getElem?_eq_getElem hx0, Option.getD_some]
    by_cases hxl : x = l
    · subst hxl
      simp only [chains1, List.getElem_set_self] at hu
      rw [hch_l_eq]
      rcases List.mem_append.mp hu with hd | ht
      · exact List.mem_append_left _ hd
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ ht)
    · simp only [chains1, List.getElem_set_ne (Ne.symm hxl)] at hu
      exact hu
  have hdone_elim : prev = 0xFFFFFFFF#32 → done = [] := fun hprev => by
    rcases wc.prev_rel with ⟨hd, _, _⟩ | ⟨_, u, _, hp_eq, hu_len, _⟩
    · exact hd
    · exfalso
      have h2 : u < 1792 := by rw [hsh.wnext_len] at hu_len; exact hu_len
      have h3 := congrArg BitVec.toNat (hp_eq.symm.trans hprev)
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        show (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 by decide] at h3
      omega
  have hwc1 : ∀ x < 2 * ks1.nv.toNat,
      WChain ks1.wnext (ks1.whead[x]?.getD 0xFFFFFFFF#32) (chains1[x]?.getD []) := by
    intro x hx
    have hx_nv : x < 2 * ks.nv.toNat := hx
    have hx1 : x < chains1.length := by rw [hch1_len]; exact hx_nv
    have hx0 : x < chains.length := by rw [wc.len_eq]; exact hx_nv
    by_cases hprev : prev = 0xFFFFFFFF#32
    · have hdone_nil := hdone_elim hprev
      have hwh1 : wh1 = ks.whead.set l nxt := by simp [wh1, hprev]
      have hwn1 : wn1 = ks.wnext := by simp [wn1, hprev]
      by_cases hxl : l = x
      · subst hxl
        rw [List.getElem?_eq_getElem hx1, Option.getD_some]
        simp only [chains1, List.getElem_set_self, hdone_nil, List.nil_append, ks1, hwh1, hwn1]
        rw [List.getElem?_set_self hwh_len, Option.getD_some]
        rcases WChain_cases wc.tail_wc with ⟨_, hn⟩ | ⟨w0', _, hw0', hw_eq', hcons, htail'⟩
        · cases hn
        · obtain ⟨_, htd_eq⟩ := List.cons.inj hcons
          subst htd_eq
          have hw0_eq : w0 = w0' := by
            have ht := congrArg BitVec.toNat hw_eq'
            have h1 : w0 < 2 ^ 32 := by unfold kMaxCl at hnc; omega
            have hwn' : w0' < 1792 := by rw [hsh.wnext_len] at hw0'; exact hw0'
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1,
              Nat.mod_eq_of_lt (by omega : w0' < 2 ^ 32)] at ht
            exact ht
          subst hw0_eq
          have hg : nxt = ks.wnext[w0]'hw0' := by
            dsimp only [nxt]; rw [List.getElem?_eq_getElem hw0', Option.getD_some]
          rw [hg]; exact htail'
      · have hwc0 := wc.chains_wc x hx_nv
        rw [List.getElem?_eq_getElem hx1, Option.getD_some]
        rw [List.getElem?_eq_getElem hx0, Option.getD_some] at hwc0
        simp only [chains1, List.getElem_set_ne hxl, ks1, hwh1, hwn1] at hwc0 ⊢
        rwa [List.getElem?_set_ne hxl]
    · rcases wc.prev_rel with ⟨_, hp_fff, _⟩ | ⟨pfx, u, hdone_eq, hp_eq, hu_len, _⟩
      · exact absurd hp_fff hprev
      · have hu_tn : prev.toNat = u := by
          rw [hp_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
            rw [hsh.wnext_len] at hu_len; omega)]
        have hwh1 : wh1 = ks.whead := by simp [wh1, hprev]
        have hwn1 : wn1 = ks.wnext.set u nxt := by simp [wn1, hprev, hu_tn]
        have hnd_get := list_flatten_nodup_getElem wc.nodup hch_l
        by_cases hxl : l = x
        · subst hxl
          rw [List.getElem?_eq_getElem hx1, Option.getD_some]
          simp only [chains1, List.getElem_set_self, hdone_eq, List.append_assoc, ks1, hwh1, hwn1]
          have hwc0 := wc.chains_wc l hx_nv
          rw [List.getElem?_eq_getElem hch_l, Option.getD_some, hch_l_eq, hdone_eq,
            List.append_assoc] at hwc0
          have hnd_l := hnd_get.1
          rw [hch_l_eq, hdone_eq, List.append_assoc] at hnd_l
          simpa [List.append_assoc] using wchain_bypass hwc0 hnd_l hu_len hwn_len hnxt_eq.symm
        · have hu_not_x : u ∉ chains[x]'hx0 := by
            refine hnd_get.2 x (Ne.symm hxl) hx0 u ?_
            rw [hch_l_eq, hdone_eq]; simp
          have hwc0 := wc.chains_wc x hx_nv
          rw [List.getElem?_eq_getElem hx1, Option.getD_some]
          rw [List.getElem?_eq_getElem hx0, Option.getD_some] at hwc0
          simp only [chains1, List.getElem_set_ne hxl, ks1, hwh1, hwn1]
          exact hwc0.congr fun y hy =>
            (List.getElem?_set_ne (fun h : u = y => hu_not_x (h ▸ hy))).symm
  have hbnd1 : ∀ x < 2 * ks1.nv.toNat, ∀ u ∈ chains1[x]?.getD [],
      u < 2 * ks1.nc.toNat ∧ 2 ≤ kittenClauseSize ks1 (u / 2) ∧
      (ks1.arena[kittenClauseOff ks1 (u / 2) + (u % 2)]?.getD 0#32).toNat = x ∧
      (ks1.wblit[u]?.getD 0#32).toNat < 2 * ks1.nv.toNat := by
    intro x hx u hu
    have hbu := wc.chains_bnd x hx u (hch1_sub x hx u hu)
    have hu_ne : u ≠ w0 := fun h => hw0_not_in (by
      rw [← h, List.mem_flatten]
      have hx1 : x < chains1.length := by rw [hch1_len]; exact hx
      exact ⟨chains1[x], List.getElem_mem hx1, by
        simpa [List.getElem?_eq_getElem hx1] using hu⟩)
    have har_u : ks1.arena[kittenClauseOff ks (u / 2) + u % 2]? =
        ks.arena[kittenClauseOff ks (u / 2) + u % 2]? := by
      dsimp only [ks1, ar']
      by_cases huc : u / 2 = cid
      · have hmod_ne1 : u % 2 ≠ slot := fun hm => hu_ne (by omega)
        have hmod_ne2 : u % 2 ≠ ri := by
          have : u % 2 < 2 := Nat.mod_lt u (by decide); omega
        rw [huc, List.getElem?_set_ne (by dsimp only [off]; omega),
          List.getElem?_set_ne (by dsimp only [off]; omega)]
      · have hu_lt : u / 2 < ks.nc.toNat := Nat.div_lt_of_lt_mul hbu.1
        have hne1 : off + slot ≠ kittenClauseOff ks (u / 2) + u % 2 := by
          dsimp only [off]
          by_cases hlu : u / 2 < cid
          · have hm := hinv.clauses.cl_mono (u / 2) cid hlu hcid_lt
            have hsp_u : 2 ≤ kittenClauseSpan ks (u / 2) := by
              unfold kittenClauseSpan; have := hbu.2.1; omega
            have hu_m : u % 2 < 2 := Nat.mod_lt u (by decide)
            change kittenClauseOff ks (u / 2) + kittenClauseSpan ks (u / 2) ≤
              kittenClauseOff ks cid at hm
            omega
          · have hm := hinv.clauses.cl_mono cid (u / 2) (by omega) hu_lt
            change kittenClauseOff ks cid + kittenClauseSpan ks cid ≤
              kittenClauseOff ks (u / 2) at hm
            omega
        have hne2 : off + ri ≠ kittenClauseOff ks (u / 2) + u % 2 := by
          dsimp only [off]
          by_cases hlu : u / 2 < cid
          · have hm := hinv.clauses.cl_mono (u / 2) cid hlu hcid_lt
            have hu_m : u % 2 < 2 := Nat.mod_lt u (by decide)
            have hsp_u : 2 ≤ kittenClauseSpan ks (u / 2) := by
              unfold kittenClauseSpan; have := hbu.2.1; omega
            change kittenClauseOff ks (u / 2) + kittenClauseSpan ks (u / 2) ≤
              kittenClauseOff ks cid at hm
            omega
          · have hm := hinv.clauses.cl_mono cid (u / 2) (by omega) hu_lt
            change kittenClauseOff ks cid + kittenClauseSpan ks cid ≤
              kittenClauseOff ks (u / 2) at hm
            omega
        rw [List.getElem?_set_ne hne2, List.getElem?_set_ne hne1]
    refine ⟨hbu.1, hbu.2.1, ?_, hbu.2.2.2⟩
    change (ks1.arena[kittenClauseOff ks (u / 2) + u % 2]?.getD 0#32).toNat = x
    rw [har_u]; exact hbu.2.2.1
  have hsz_ks1 : ∀ c, kittenClauseSize ks1 c = kittenClauseSize ks c := fun _ => rfl
  have hoff_ks1 : ∀ c, kittenClauseOff ks1 c = kittenClauseOff ks c := fun _ => rfl
  have hw_tn : w.toNat = w0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold kMaxCl at hnc; omega)]
  have hw_step0 := kittenWatchStep0_preserves_watches_with hsh1 hch1_len hch1_nd hwc1 hbnd1
    (w := w) (l := repl) (vo := other)
    (by change w.toNat < 2 * ks.nc.toNat; rw [hw_tn]; exact hb0.1)
    hnc hnv hrepl_nv hother_nv
    (by rw [hsz_ks1, hw_tn]; exact hsz_ge)
    (by rw [hoff_ks1, hw_tn]
        change (ar'[off + slot]?.getD 0#32).toNat = repl.toNat
        have hslot_ri : off + slot ≠ off + ri := by omega
        have hoff_len2 : off + slot < ks.arena.length := by dsimp only [off]; omega
        simp [ar', List.getElem?_set_ne hslot_ri.symm,
          List.getElem?_set_self (by simp [hoff_len2] : off + slot < ks.arena.length)])
    (by rw [hw_tn]; exact hw0_not_in)
  have hrepl_ch1 : repl.toNat < chains1.length := by
    rw [hch1_len]; change repl.toNat < 2 * ks.nv.toNat; exact hrepl_nv
  let chains' := chains1.set repl.toNat (w.toNat :: chains1[repl.toNat]'hrepl_ch1)
  have hwc_cur' : WChainCursor ks' l chains' done todo' prev nxt := by
    have hl1 : l < 2 * ks1.nv.toNat := hl
    have hch'_l : l < chains'.length := by
      simp only [chains', List.length_set]; rw [hch1_len]; exact hl1
    have hcl'_eq : chains'[l]?.getD [] = done ++ todo' := by
      rw [List.getElem?_eq_getElem hch'_l, Option.getD_some]
      simp only [chains', List.getElem_set_ne hrepl_ne]
      simp only [chains1, List.getElem_set_self]
    have htail_ks : WChain ks.wnext nxt todo' := by
      rcases WChain_cases wc.tail_wc with ⟨_, hn⟩ | ⟨w0', _, hw0', hw_eq', hcons, htail'⟩
      · cases hn
      · obtain ⟨_, htd_eq⟩ := List.cons.inj hcons
        subst htd_eq
        have hw0_eq : w0 = w0' := by
          have ht := congrArg BitVec.toNat hw_eq'
          have h1 : w0 < 2 ^ 32 := by unfold kMaxCl at hnc; omega
          have hwn' : w0' < 1792 := by rw [hsh.wnext_len] at hw0'; exact hw0'
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1,
            Nat.mod_eq_of_lt (by omega : w0' < 2 ^ 32)] at ht
          exact ht
        subst hw0_eq
        have hg : nxt = ks.wnext[w0]'hw0' := by
          dsimp only [nxt]; rw [List.getElem?_eq_getElem hw0', Option.getD_some]
        rw [hg]; exact htail'
    have hnd_l := (list_flatten_nodup_getElem wc.nodup hch_l).1
    have hw0_nt : w0 ∉ todo' := by
      rw [hch_l_eq] at hnd_l
      have hnd2 := (List.nodup_append.mp hnd_l).2.1
      exact (List.nodup_cons.mp hnd2).1
    have htail1 : WChain ks1.wnext nxt todo' := by
      by_cases hprev : prev = 0xFFFFFFFF#32
      · simp [ks1, wn1, hprev, htail_ks]
      · rcases wc.prev_rel with ⟨_, hp, _⟩ | ⟨pfx, u, hde, hp_eq, hu_len, _⟩
        · exact absurd hp hprev
        · have hu_tn : prev.toNat = u := by
            rw [hp_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
              rw [hsh.wnext_len] at hu_len; omega)]
          have hu_nt : u ∉ todo' := by
            rw [hch_l_eq, hde] at hnd_l
            have hd := (List.nodup_append.mp hnd_l).2.2 u (by simp)
            exact fun h => hd u (List.mem_cons_of_mem _ h) rfl
          simp only [ks1, wn1, hprev, ↓reduceIte, hu_tn]
          exact htail_ks.congr fun y hy =>
            (List.getElem?_set_ne (fun h : u = y => hu_nt (h ▸ hy))).symm
    have htail' : WChain ks'.wnext nxt todo' := by
      change WChain (ks1.wnext.set w.toNat _) nxt todo'
      rw [hw_tn]
      exact htail1.congr fun y hy =>
        (List.getElem?_set_ne (fun h : w0 = y => hw0_nt (h ▸ hy))).symm
    have hprev' : (done = [] ∧ prev = 0xFFFFFFFF#32 ∧
        ks'.whead[l]?.getD 0xFFFFFFFF#32 = nxt) ∨
        (∃ pfx u, done = pfx ++ [u] ∧ prev = BitVec.ofNat 32 u ∧
          u < ks'.wnext.length ∧ ks'.wnext[u]?.getD 0xFFFFFFFF#32 = nxt) := by
      by_cases hprev : prev = 0xFFFFFFFF#32
      · left
        have hdone_nil := hdone_elim hprev
        refine ⟨hdone_nil, hprev, ?_⟩
        change (ks1.whead.set repl.toNat w)[l]?.getD 0xFFFFFFFF#32 = nxt
        rw [List.getElem?_set_ne hrepl_ne]
        change (wh1)[l]?.getD 0xFFFFFFFF#32 = nxt
        dsimp only [wh1]
        simp only [hprev, ↓reduceIte]
        rw [List.getElem?_set_self hwh_len, Option.getD_some]
      · right
        rcases wc.prev_rel with ⟨_, hp, _⟩ | ⟨pfx, u, hde, hp_eq, hu_len, _⟩
        · exact absurd hp hprev
        · have hu_tn : prev.toNat = u := by
            rw [hp_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
              rw [hsh.wnext_len] at hu_len; omega)]
          have hune : w0 ≠ u := by
            intro heq
            rw [hch_l_eq, hde] at hnd_l
            have hd := (List.nodup_append.mp hnd_l).2.2 u (by simp)
            exact hd w0 List.mem_cons_self heq.symm
          refine ⟨pfx, u, hde, hp_eq, by simpa [ks', kittenWatchStep0, ks1, wn1, hprev] using
            hu_len, ?_⟩
          change (ks1.wnext.set w.toNat _)[u]?.getD 0xFFFFFFFF#32 = nxt
          rw [hw_tn, List.getElem?_set_ne hune]
          change wn1[u]?.getD 0xFFFFFFFF#32 = nxt
          dsimp only [wn1]
          simp only [hprev, ↓reduceIte]
          rw [hu_tn, List.getElem?_set_self hu_len, Option.getD_some]
    exact ⟨hw_step0.1, hw_step0.2.1, hcl'_eq, hw_step0.2.2.1, hw_step0.2.2.2.1, htail', hprev'⟩
  exact ⟨⟨hsh', hcl', hwc_cur'.watchesOk, hba', hrsn'⟩, hlits_perm_all, hlits_other,
    hants_all, horig_perm, ⟨chains', hwc_cur'⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Final literal flip in `full_kitten_flip` (`lvlArr[lit/2] ≠ 0`, `vals[lit] := 2`,
`vals[lit^1] := 1`) preserves `KittenInv`. -/
theorem kittenFlipFinish_preserves {acap : Nat} {ks : KittenState}
    (hinv : ks.Inv acap) {lit : BitVec 32} (hlit : lit.toNat < 2 * ks.nv.toNat)
    (hval1 : ks.vals[lit.toNat]? = some 1#32)
    (hlvl_nz : ks.lvlArr[(lit >>> (1 : Nat)).toNat]?.getD 0#32 ≠ 0#32) :
    let ks' := (ks.putArr .vals lit.toNat 2#32).putArr .vals (lit ^^^ 1#32).toNat 1#32
    ks'.Inv acap := by
  intro ks'
  have hsh := hinv.shapes
  have hnv := hinv.clauses.nv_le
  have hsh' : ks'.ShapesOk acap := (hsh.putArr .vals _ _).putArr .vals _ _
  obtain ⟨hv_eq, hv_lt⟩ := bv32_lit_div2_bv hlit
  obtain ⟨hn_eq, hn_lt⟩ := bv32_xor1_eq_litNeg hlit
  rw [bv32_one_eq] at hn_eq hn_lt
  have hl_ne : lit.toNat ≠ (lit ^^^ 1#32).toNat := by
    rw [hn_eq, ← litNeg_eq_xor1]
    rcases nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  have hlen_v : lit.toNat < ks.vals.length := by rw [hsh.vals_len]; unfold kMaxV at hnv; omega
  have hlen_nl : (lit ^^^ 1#32).toNat < ks.vals.length := by
    rw [hsh.vals_len]; unfold kMaxV at hnv; omega
  have hval_lit : ks'.vals[lit.toNat]? = some 2#32 := by
    change ((ks.vals.set lit.toNat 2#32).set (lit ^^^ 1#32).toNat 1#32)[lit.toNat]? = some 2#32
    rw [List.getElem?_set_ne hl_ne.symm, List.getElem?_set_self hlen_v]
  have hval_nl : ks'.vals[(lit ^^^ 1#32).toNat]? = some 1#32 := by
    change ((ks.vals.set lit.toNat 2#32).set (lit ^^^ 1#32).toNat 1#32)[(lit ^^^ 1#32).toNat]? =
      some 1#32
    rw [List.getElem?_set_self (by simp; exact hlen_nl)]
  have hval_other : ∀ x, x / 2 ≠ lit.toNat / 2 → ks'.vals[x]? = ks.vals[x]? := by
    intro x hx
    change ((ks.vals.set lit.toNat 2#32).set (lit ^^^ 1#32).toNat 1#32)[x]? = ks.vals[x]?
    have h1 : x ≠ lit.toNat := fun h => hx (h ▸ rfl)
    have h2 : x ≠ (lit ^^^ 1#32).toNat := fun h => by
      have h' : x / 2 = (lit.toNat ^^^ 1) / 2 := by rw [h, hn_eq, ← litNeg_eq_xor1]
      rcases nat_xor1_cases lit.toNat with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
    rw [List.getElem?_set_ne h2.symm, List.getElem?_set_ne h1.symm]
  have hv_div : lit.toNat / 2 ≠ (lit.toNat / 2) + 1 := by omega
  have hcl' : KittenClausesOk acap ks' := by
    have h0 := hinv.clauses
    refine ⟨h0.acap_ge, h0.acap_lt, h0.acap_eq, h0.nv_le, h0.nc_le, h0.orig_nc_le, h0.orig_nc_max,
      h0.alen_le, h0.nassump_le, h0.nunits_le, h0.nres_le, h0.nkl_le, h0.nana_le,
      h0.cl_wf, h0.cl_mono, h0.units_ok, fun hi => ?_, h0.failing_ok, h0.assump_ok, h0.flags_clean⟩
    have hinc := h0.incons_ok hi
    refine ⟨hinc.1, hinc.2.1, fun l hl => ?_⟩
    have hr := hinc.2.2 l hl
    have hne_v : l / 2 ≠ lit.toNat / 2 := fun heq => by
      have hlz := hr.2.1
      rw [heq, ← hv_eq] at hlz
      exact hlvl_nz hlz
    rw [hval_other l hne_v]
    exact hr
  have hba' : KittenBaseAssignOk ks' := by
    have h0 := hinv.assign
    refine ⟨h0.trl_end_le, h0.prop_le, h0.unass_eq, ?_, ?_, ?_, h0.trl_nodup, h0.trl_lt,
      h0.trl_lvl_le, ?_, h0.trl_lvl_mono, h0.dec_earliest, ?_⟩
    · intro l hl
      by_cases hv : l / 2 = lit.toNat / 2
      · rcases nat_xor1_cases lit.toNat with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
          · rcases nat_xor1_cases l with ⟨hc, hd⟩ | ⟨hc, hd⟩ <;>
              · have he : l = lit.toNat ∨ l = (lit ^^^ 1#32).toNat := by
                  rw [hn_eq, ← litNeg_eq_xor1]; omega
                rcases he with rfl | rfl
                · rw [hval_lit]; exact Or.inr (Or.inr rfl)
                · rw [hval_nl]; exact Or.inr (Or.inl rfl)
      · rw [hval_other l hv]; exact h0.vals_dom l hl
    · intro l hl
      by_cases hv : l / 2 = lit.toNat / 2
      · have he : l = lit.toNat ∨ l = (lit ^^^ 1#32).toNat := by
          rcases nat_xor1_cases lit.toNat with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
            rcases nat_xor1_cases l with ⟨hc, hd⟩ | ⟨hc, hd⟩ <;>
              · rw [hn_eq, ← litNeg_eq_xor1]; omega
        rcases he with rfl | rfl
        · have hx : lit.toNat ^^^ 1 = (lit ^^^ 1#32).toNat := by
            rw [hn_eq, ← litNeg_eq_xor1]
          rw [hval_lit, hx, hval_nl]; simp
        · have hx : (lit ^^^ 1#32).toNat ^^^ 1 = lit.toNat := by
            rw [hn_eq]; exact litNeg_litNeg _
          rw [hval_nl, hx, hval_lit]; simp
      · have hnv' : (l ^^^ 1) / 2 ≠ lit.toNat / 2 := by
          rcases nat_xor1_cases l with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
        rw [hval_other l hv, hval_other (l ^^^ 1) hnv']
        exact h0.vals_neg_iff l hl
    · intro l hl
      by_cases hv : l / 2 = lit.toNat / 2
      · have hnz_old : ks.vals[lit.toNat]?.getD 0#32 ≠ 0#32 := by simp [hval1]
        have hex := (h0.vals_nz_iff_trl lit.toNat hlit).mp hnz_old
        have hex' : ∃ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = l / 2 := by
          simpa [hv] using hex
        have hnz_new : ks'.vals[l]?.getD 0#32 ≠ 0#32 := by
          have he : l = lit.toNat ∨ l = (lit ^^^ 1#32).toNat := by
            rcases nat_xor1_cases lit.toNat with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
              rcases nat_xor1_cases l with ⟨hc, hd⟩ | ⟨hc, hd⟩ <;>
                · rw [hn_eq, ← litNeg_eq_xor1]; omega
          rcases he with rfl | rfl
          · rw [hval_lit]; simp
          · rw [hval_nl]; simp
        exact ⟨fun _ => hex', fun _ => hnz_new⟩
      · rw [hval_other l hv]; exact h0.vals_nz_iff_trl l hl
    · intro v hv hv0
      by_cases hvq : v = lit.toNat / 2
      · exfalso
        subst hvq
        rcases nat_xor1_cases lit.toNat with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · have : 2 * (lit.toNat / 2) = lit.toNat := by omega
          rw [this, hval_lit] at hv0; cases hv0
        · have : 2 * (lit.toNat / 2) = (lit ^^^ 1#32).toNat := by
            rw [hn_eq, ← litNeg_eq_xor1]; omega
          rw [this, hval_nl] at hv0; cases hv0
      · have hv0' : ks.vals[2 * v]?.getD 0#32 = 0#32 := by
          rwa [← hval_other (2 * v) (by omega)]
        exact h0.unass_lvl_zero v hv hv0'
    · intro i hi
      dsimp only
      intro hlv
      have hlv' : ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = 0#32 := hlv
      have h0l := h0.lvl0_ok i hi hlv'
      have hne_v : (ks.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := fun heq => by
        rw [heq, ← hv_eq] at hlv'; exact hlvl_nz hlv'
      have hne_x : ((ks.trl[i]?.getD 0#32).toNat ^^^ 1) / 2 ≠ lit.toNat / 2 := by
        rcases nat_xor1_cases (ks.trl[i]?.getD 0#32).toNat with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
      refine ⟨h0l.1, ?_, ?_, h0l.2.2.2.1, h0l.2.2.2.2⟩
      · rw [show ks'.vals[(ks'.trl[i]?.getD 0#32).toNat]? =
            ks'.vals[(ks.trl[i]?.getD 0#32).toNat]? from rfl, hval_other _ hne_v]
        exact h0l.2.1
      · rw [show ks'.vals[(ks'.trl[i]?.getD 0#32).toNat ^^^ 1]? =
            ks'.vals[(ks.trl[i]?.getD 0#32).toNat ^^^ 1]? from rfl, hval_other _ hne_x]
        exact h0l.2.2.1
  exact ⟨hsh', hcl', hinv.watches, hba', hinv.reasons⟩

/-! ## 7. `full_kitten_build_failing_wp` (`8/15`) -/

private def FailingLoopInv (ks : KittenState) (i : BitVec 32) (fls cms : List (BitVec 32)) :
    Prop :=
  i.toNat ≤ ks.trl_end.toNat ∧ fls.length = 128 ∧ cms.length = 896 ∧
  (∀ c < ks.nc.toNat, cms[c]?.getD 0#32 = ks.clMeta[c]?.getD 0#32 ∨
    cms[c]?.getD 0#32 = (ks.clMeta[c]?.getD 0#32 ||| kmCore)) ∧
  (∀ α : Nat → Bool,
    (cnfOfClauses (((List.range ks.nc.toNat).filter fun ci =>
      (cms[ci]?.getD 0#32 &&& kmCore) != 0#32).map (kittenClauseLits ks)) ++
      unitsCnf (kittenAssumpLits ks)).Sat α →
    ∃ k < i.toNat,
      ((fls[(ks.trl[k]?.getD 0#32).toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32) ∧
      (cnfClause [litNeg (ks.trl[k]?.getD 0#32).toNat]).Sat α)

private theorem failingStep_finish_inv {acap : Nat} {ks : KittenState}
    (hsh : ks.ShapesOk acap) (hinv : ks.Inv acap) {i : BitVec 32}
    {fls fls_clr fls_j cms : List (BitVec 32)}
    (hloop : FailingLoopInv ks i fls cms) (hpos : 0 < i.toNat)
    {rsn : BitVec 32} (hrsn_ne : rsn ≠ 0xFFFFFFFF#32)
    (hrsn_eq : rsn = ks.rsn[(ks.trl[i.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32)
    (hclr : ∀ w < ks.nv.toNat, w ≠ (ks.trl[i.toNat - 1]?.getD 0#32).toNat / 2 →
      fls_clr[w]? = fls[w]?)
    (hkeep : ∀ w < ks.nv.toNat,
      (fls_clr[w]?.getD 0#32 &&& 2#32) ≠ 0#32 → (fls_j[w]?.getD 0#32 &&& 2#32) ≠ 0#32)
    (hmark : ∀ q < kittenClauseSize ks rsn.toNat,
      let lv := (ks.arena[kittenClauseOff ks rsn.toNat + q]?.getD 0#32).toNat / 2
      lv ≠ (ks.trl[i.toNat - 1]?.getD 0#32).toNat / 2 →
      (fls_j[lv]?.getD 0#32 &&& 2#32) ≠ 0#32)
    (hflj_len : fls_j.length = 128) :
    let cms' := cms.set rsn.toNat (cms[rsn.toNat]?.getD 0#32 ||| kmCore)
    FailingLoopInv ks (i - 1#32) fls_j cms' := by
  intro cms'
  have hnv := hinv.clauses.nv_le
  have hnc := hinv.clauses.nc_le
  have hi_le := hloop.1
  have hi1_lt : i.toNat - 1 < ks.trl_end.toNat := by omega
  have hi_sub : (i - 1#32).toNat = i.toNat - 1 := by
    have := hinv.assign.trl_end_le; unfold kMaxV at hnv; bv_omega
  have hro := hinv.reasons (i.toNat - 1) hi1_lt
  dsimp only at hro
  let lit := (ks.trl[i.toNat - 1]?.getD 0#32).toNat
  let v := lit / 2
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hsh.trl_len]; have := hinv.assign.trl_end_le; unfold kMaxV at hnv; omega
  have hlit_lt : lit < 2 * ks.nv.toNat :=
    hinv.assign.trl_lt lit (mem_kittenTrailLits_of_lt hi1_lt htrl_len)
  have hrsn_len : v < ks.rsn.length := by
    rw [hsh.rsn_len]; unfold kMaxV at hnv; change lit / 2 < 128; omega
  have hrsn_eq2 : ks.rsn[v]?.getD 0#32 = rsn := by
    rw [hrsn_eq, List.getElem?_eq_getElem hrsn_len]; rfl
  rcases hro with hdec | ⟨hr_lt, _, hall⟩
  · exfalso; rw [hrsn_eq2] at hdec; exact hrsn_ne hdec
  · rw [hrsn_eq2] at hr_lt hall
    have hcm_len : rsn.toNat < cms.length := by
      rw [hloop.2.2.1]; unfold kMaxCl at hnc; omega
    have hcms' : ∀ c < ks.nc.toNat, cms'[c]?.getD 0#32 = ks.clMeta[c]?.getD 0#32 ∨
        cms'[c]?.getD 0#32 = (ks.clMeta[c]?.getD 0#32 ||| kmCore) := by
      intro c hc
      by_cases hcr : c = rsn.toNat
      · subst hcr
        rw [show cms'[rsn.toNat]?.getD 0#32 = (cms[rsn.toNat]?.getD 0#32 ||| kmCore) by
          simp [cms', List.getElem?_set_self hcm_len]]
        rcases hloop.2.2.2.1 rsn.toNat hc with h1 | h2
        · right; rw [h1]
        · right; rw [h2]; apply BitVec.eq_of_getElem_eq; intro b hb
          simp only [BitVec.getElem_or]; cases _ : (ks.clMeta[rsn.toNat]?.getD 0#32)[b] <;>
            cases _ : kmCore[b] <;> simp
      · have := hloop.2.2.2.1 c hc
        simpa [cms', List.getElem?_set_ne (Ne.symm hcr)] using this
    refine ⟨by rw [hi_sub]; omega, hflj_len, by simp [cms', hloop.2.2.1], hcms', ?_⟩
    intro α hα
    rw [CNF.sat_append] at hα
    have hα_old : (cnfOfClauses (((List.range ks.nc.toNat).filter fun ci =>
        (cms[ci]?.getD 0#32 &&& kmCore) != 0#32).map (kittenClauseLits ks)) ++
        unitsCnf (kittenAssumpLits ks)).Sat α := by
      rw [CNF.sat_append]; refine ⟨?_, hα.2⟩
      rw [cnf_sat_cnfOfClauses_iff] at hα ⊢
      intro c hc
      rw [List.mem_map] at hc
      obtain ⟨ci, hci, rfl⟩ := hc
      rw [List.mem_filter, List.mem_range] at hci
      apply hα.1
      rw [List.mem_map]
      refine ⟨ci, List.mem_filter.mpr ⟨List.mem_range.mpr hci.1, ?_⟩, rfl⟩
      by_cases hcr : ci = rsn.toNat
      · subst hcr
        simp only [cms', List.getElem?_set_self hcm_len, Option.getD_some,
          cm_or_core_and_core_nz, bne_iff_ne, ne_eq, not_false_eq_true]
      · simpa [cms', List.getElem?_set_ne (Ne.symm hcr)] using hci.2
    obtain ⟨k, hk_lt, hk_fl, hk_sat⟩ := hloop.2.2.2.2 α hα_old
    by_cases hkl : k < i.toNat - 1
    · have hkv : (ks.trl[k]?.getD 0#32).toNat / 2 < ks.nv.toNat := by
        have hlt_k : k < ks.trl_end.toNat := by omega
        have := hinv.assign.trl_lt _ (mem_kittenTrailLits_of_lt hlt_k htrl_len); omega
      have hne_v : (ks.trl[k]?.getD 0#32).toNat / 2 ≠ v :=
        trl_nodup_var_ne' hsh hnv hinv.assign (by omega) hi1_lt (by omega)
      refine ⟨k, by rw [hi_sub]; exact hkl, hkeep _ hkv ?_, hk_sat⟩
      rwa [hclr _ hkv hne_v]
    · have hkeq : k = i.toNat - 1 := by omega
      subst hkeq
      have hr_core : (cms'[rsn.toNat]?.getD 0#32 &&& kmCore) ≠ 0#32 := by
        rw [show cms'[rsn.toNat]?.getD 0#32 = (cms[rsn.toNat]?.getD 0#32 ||| kmCore) by
          simp [cms', List.getElem?_set_self hcm_len]]
        exact cm_or_core_and_core_nz _
      have hr_mem : kittenClauseLits ks rsn.toNat ∈ ((List.range ks.nc.toNat).filter fun ci =>
          (cms'[ci]?.getD 0#32 &&& kmCore) != 0#32).map (kittenClauseLits ks) :=
        List.mem_map.mpr ⟨rsn.toNat, List.mem_filter.mpr ⟨List.mem_range.mpr hr_lt,
          bne_iff_ne.mpr hr_core⟩, rfl⟩
      have hsat_r := (cnf_sat_cnfOfClauses_iff α _).mp hα.1 _ hr_mem
      obtain ⟨x, hx_mem, hxsat⟩ := (clause_sat_cnfClause_iff α _).mp hsat_r
      have hnot_lit : ¬ (cnfClause [lit]).Sat α :=
        (sat_cnfClause_litNeg_iff α lit).mp hk_sat
      have hxne : x ≠ lit := fun h => hnot_lit (h ▸ (sat_cnfClause_singleton α x).mpr hxsat)
      obtain ⟨q, hq_lt, hq_eq⟩ := hall x hx_mem hxne
      have hx_mem_u := hx_mem
      unfold kittenClauseLits at hx_mem_u
      rw [List.mem_map] at hx_mem_u
      obtain ⟨bx, hbx, rfl⟩ := hx_mem_u
      obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hbx
      have hr_sz : r < kittenClauseSize ks rsn.toNat := by simp [List.length_take] at hr; omega
      have har_lt_len : kittenClauseOff ks rsn.toNat + r < ks.arena.length := by
        have hwf_r := hinv.clauses.cl_wf rsn.toNat hr_lt
        have := hwf_r.2.2.1; unfold kittenClauseSpan at this
        rw [hsh.arena_len]; have := hinv.clauses.alen_le; omega
      have hbx_eq : ((ks.arena.drop (kittenClauseOff ks rsn.toNat)).take
          (kittenClauseSize ks rsn.toNat))[r] =
          ks.arena[kittenClauseOff ks rsn.toNat + r]?.getD 0#32 := by
        simp [List.getElem?_eq_getElem har_lt_len]
      have hne_qv : (ks.trl[q]?.getD 0#32).toNat / 2 ≠ v :=
        trl_nodup_var_ne' hsh hnv hinv.assign (by omega) hi1_lt (by omega)
      have hx_div : (ks.arena[kittenClauseOff ks rsn.toNat + r]?.getD 0#32).toNat / 2 =
          (ks.trl[q]?.getD 0#32).toNat / 2 := by
        rw [← hbx_eq, hq_eq]
        rcases nat_xor1_cases
          (((ks.arena.drop (kittenClauseOff ks rsn.toNat)).take
            (kittenClauseSize ks rsn.toNat))[r]).toNat with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
      have hmark_q := hmark r hr_sz (by rw [hx_div]; exact hne_qv)
      rw [hx_div] at hmark_q
      refine ⟨q, by rw [hi_sub]; exact hq_lt, hmark_q, ?_⟩
      rw [hq_eq, litNeg_eq_xor1, litNeg_litNeg]; simpa [← hbx_eq] using
        (sat_cnfClause_singleton α _).mpr hxsat

private theorem failingStep_skip_inv {acap : Nat} {ks : KittenState}
    (_hsh : ks.ShapesOk acap) (hinv : ks.Inv acap) {i : BitVec 32}
    {fls cms : List (BitVec 32)}
    (hloop : FailingLoopInv ks i fls cms) (hpos : 0 < i.toNat)
    (hzero : (fls[(ks.trl[i.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0#32 &&& 2#32) = 0#32) :
    FailingLoopInv ks (i - 1#32) fls cms := by
  have hnv := hinv.clauses.nv_le
  have hi_sub : (i - 1#32).toNat = i.toNat - 1 := by
    have := hloop.1; have := hinv.assign.trl_end_le; unfold kMaxV at hnv; bv_omega
  refine ⟨by rw [hi_sub]; have := hloop.1; omega, hloop.2.1, hloop.2.2.1, hloop.2.2.2.1, ?_⟩
  intro α hα
  obtain ⟨k, hk_lt, hk_fl, hk_sat⟩ := hloop.2.2.2.2 α hα
  refine ⟨k, ?_, hk_fl, hk_sat⟩
  rw [hi_sub]
  by_cases hkl : k < i.toNat - 1
  · exact hkl
  · exfalso
    have hkeq : k = i.toNat - 1 := by omega
    subst hkeq; exact absurd hzero hk_fl

private theorem failingStep_dec_inv {acap : Nat} {ks : KittenState}
    (hsh : ks.ShapesOk acap) (hinv : ks.Inv acap) (hdec : KittenAllDecisionsInAssumps ks)
    {i : BitVec 32} {fls fls_clr cms : List (BitVec 32)}
    (hloop : FailingLoopInv ks i fls cms) (hpos : 0 < i.toNat)
    (hrsn : ks.rsn[(ks.trl[i.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0#32 = 0xFFFFFFFF#32)
    (hclr_len : fls_clr.length = 128)
    (hclr : ∀ w < ks.nv.toNat, w ≠ (ks.trl[i.toNat - 1]?.getD 0#32).toNat / 2 →
      fls_clr[w]? = fls[w]?) :
    FailingLoopInv ks (i - 1#32) fls_clr cms := by
  have hnv := hinv.clauses.nv_le
  have hi_le := hloop.1
  have hi1_lt : i.toNat - 1 < ks.trl_end.toNat := by omega
  have hi_sub : (i - 1#32).toNat = i.toNat - 1 := by
    have := hinv.assign.trl_end_le; unfold kMaxV at hnv; bv_omega
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hsh.trl_len]; have := hinv.assign.trl_end_le; unfold kMaxV at hnv; omega
  refine ⟨by rw [hi_sub]; omega, hclr_len, hloop.2.2.1, hloop.2.2.2.1, ?_⟩
  intro α hα
  obtain ⟨k, hk_lt, hk_fl, hk_sat⟩ := hloop.2.2.2.2 α hα
  have hkne : k ≠ i.toNat - 1 := by
    intro hkeq
    have hk1 : k < ks.trl_end.toNat := by rw [hkeq]; exact hi1_lt
    have hrsn_k : ks.rsn[(ks.trl[k]?.getD 0#32).toNat / 2]?.getD 0#32 = 0xFFFFFFFF#32 := by
      rw [hkeq]; exact hrsn
    have hmem_dec : (ks.trl[k]?.getD 0#32).toNat ∈ kittenTrailDecisions ks :=
      (mem_kittenTrailDecisions_iff htrl_len).mpr ⟨k, hk1, rfl, hrsn_k⟩
    have hmem_ass := hdec _ hmem_dec
    have hsat_a := (sat_unitsCnf_iff α (kittenAssumpLits ks)).mp (CNF.sat_append.mp hα).2 _ hmem_ass
    exact ((sat_cnfClause_litNeg_iff α _).mp hk_sat) hsat_a
  have hne_v : (ks.trl[k]?.getD 0#32).toNat / 2 ≠ (ks.trl[i.toNat - 1]?.getD 0#32).toNat / 2 :=
    trl_nodup_var_ne' hsh hnv hinv.assign (by omega) hi1_lt hkne
  have hkv : (ks.trl[k]?.getD 0#32).toNat / 2 < ks.nv.toNat := by
    have hlt_k : k < ks.trl_end.toNat := by omega
    have := hinv.assign.trl_lt _ (mem_kittenTrailLits_of_lt hlt_k htrl_len); omega
  refine ⟨k, by rw [hi_sub]; omega, ?_, hk_sat⟩
  rwa [hclr _ hkv hne_v]

private theorem failingFinish_preserves {acap : Nat} {ks : KittenState}
    (hsh : ks.ShapesOk acap) (hinv : ks.Inv acap) (hsync : KittenTrailSynced ks)
    {fls_fin cms_fin : List (BitVec 32)}
    (hloop : FailingLoopInv ks 0#32 fls_fin cms_fin)
    (hclean : ∀ v < ks.nv.toNat, (fls_fin[v]?.getD 0#32 &&& 2#32) = 0#32) :
    let ks' : KittenState := { ks with failing := 1#32, flags := fls_fin, clMeta := cms_fin }
    ks'.Inv acap ∧ KittenTrailSynced ks' ∧ ks'.failing = 1#32 ∧
    KittenBuildFailingPreserved ks ks' := by
  intro ks'
  have hsh' : ks'.ShapesOk acap :=
    ⟨hsh.hdrTail_len, hsh.lvlArr_len, hsh.rsn_len, hsh.qprev_len, hsh.qnext_len,
      hsh.qstampArr_len, hsh.trl_len, hloop.2.1, hsh.vals_len, hsh.assump_len, hsh.ana_len,
      hsh.kl_len, hsh.units_len, hsh.res_len, hsh.whead_len, hsh.wnext_len, hsh.wblit_len,
      hsh.clOff_len, hloop.2.2.1, hsh.clAux_len, hsh.arena_len⟩
  have hcm_eq : ∀ c < ks.nc.toNat,
      (kittenClauseMeta ks' c &&& 0xFFFF#32) = (kittenClauseMeta ks c &&& 0xFFFF#32) ∧
      (kittenClauseMeta ks' c &&& kmLrn) = (kittenClauseMeta ks c &&& kmLrn) := by
    intro c hc
    rcases hloop.2.2.2.1 c hc with h1 | h2
    · constructor <;> simp [kittenClauseMeta, ks', h1]
    · constructor
      · change (cms_fin[c]?.getD 0#32 &&& 0xFFFF#32) = (ks.clMeta[c]?.getD 0#32 &&& 0xFFFF#32)
        rw [h2]; exact cm_or_core_and_ffff _
      · change (cms_fin[c]?.getD 0#32 &&& kmLrn) = (ks.clMeta[c]?.getD 0#32 &&& kmLrn)
        rw [h2]; exact cm_or_core_and_lrn _
  have hsz_eq : ∀ c < ks.nc.toNat, kittenClauseSize ks' c = kittenClauseSize ks c := fun c hc => by
    unfold kittenClauseSize; rw [(hcm_eq c hc).1]
  have his_eq : ∀ c < ks.nc.toNat,
      kittenClauseIsLrn ks' c = kittenClauseIsLrn ks c := fun c hc => by
    unfold kittenClauseIsLrn; rw [(hcm_eq c hc).2]
  have hsp_eq : ∀ c < ks.nc.toNat, kittenClauseSpan ks' c = kittenClauseSpan ks c := fun c hc => by
    unfold kittenClauseSpan; rw [hsz_eq c hc, his_eq c hc]; rfl
  have hlits_eq : ∀ c < ks.nc.toNat,
      kittenClauseLits ks' c = kittenClauseLits ks c := fun c hc => by
    unfold kittenClauseLits; rw [hsz_eq c hc]; rfl
  have hants_eq : ∀ c < ks.nc.toNat,
      kittenClauseAnts ks' c = kittenClauseAnts ks c := fun c hc => by
    unfold kittenClauseAnts; rw [his_eq c hc, hsz_eq c hc]; rfl
  have horig_eq : kittenOrigClauses ks' = kittenOrigClauses ks :=
    kittenOrigClauses_eq_of rfl fun c hc =>
      hlits_eq c (Nat.lt_of_lt_of_le hc hinv.clauses.orig_nc_le)
  have hcl' : KittenClausesOk acap ks' := by
    have h0 := hinv.clauses
    refine ⟨h0.acap_ge, h0.acap_lt, h0.acap_eq, h0.nv_le, h0.nc_le, h0.orig_nc_le, h0.orig_nc_max,
      h0.alen_le, h0.nassump_le, h0.nunits_le, h0.nres_le, h0.nkl_le, h0.nana_le,
      ?_, ?_, ?_, ?_, ?_, h0.assump_ok, hclean⟩
    · intro c hc
      have hw := h0.cl_wf c hc
      rw [his_eq c hc, hsz_eq c hc, hsp_eq c hc, hlits_eq c hc, horig_eq, hants_eq c hc]
      refine ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, fun ha hge => ?_⟩
      have ⟨ha1, ha2⟩ := hw.2.2.2.2.2 ha hge
      refine ⟨ha1, ?_⟩
      have hm : (kittenClauseAnts ks c).map (kittenClauseLits ks') =
          (kittenClauseAnts ks c).map (kittenClauseLits ks) :=
        List.map_congr_left fun a haa => hlits_eq a (Nat.lt_trans (ha1 a haa) hc)
      rwa [hm]
    · intro c1 c2 h12 hc2
      have hm := h0.cl_mono c1 c2 h12 hc2
      rwa [show kittenClauseOff ks' c1 = kittenClauseOff ks c1 from rfl,
        show kittenClauseOff ks' c2 = kittenClauseOff ks c2 from rfl,
        hsp_eq c1 (Nat.lt_trans h12 hc2)]
    · intro ui hui
      have hu := h0.units_ok ui hui
      refine ⟨hu.1, by rw [hsz_eq _ hu.1]; exact hu.2⟩
    · intro hi
      have hinc := h0.incons_ok hi
      refine ⟨hinc.1, by rw [horig_eq]; exact hinc.2.1, fun l hl => ?_⟩
      rw [hlits_eq _ hinc.1] at hl
      have hr := hinc.2.2 l hl
      refine ⟨hr.1, hr.2.1, fun ha => ?_⟩
      have hrr := hr.2.2 ha
      have hl_r := hlits_eq _ hrr.1
      exact ⟨hrr.1, by rw [hl_r]; exact hrr.2⟩
    · intro _
      rw [CNF.unsat_iff_not_sat]
      intro α hα
      have hsat : (cnfOfClauses (((List.range ks.nc.toNat).filter fun ci =>
          (cms_fin[ci]?.getD 0#32 &&& kmCore) != 0#32).map (kittenClauseLits ks)) ++
          unitsCnf (kittenAssumpLits ks)).Sat α := by
        rw [CNF.sat_append] at hα ⊢
        refine ⟨?_, hα.2⟩
        rw [cnf_sat_cnfOfClauses_iff] at hα ⊢
        intro cl hcl
        rw [List.mem_map] at hcl
        obtain ⟨ci, hci, rfl⟩ := hcl
        rw [List.mem_filter, List.mem_range] at hci
        rw [← hlits_eq ci hci.1]
        exact hα.1 _ (List.mem_map.mpr ⟨ci, List.mem_filter.mpr ⟨List.mem_range.mpr hci.1,
          hci.2⟩, rfl⟩)
      obtain ⟨k, hk, _⟩ := hloop.2.2.2.2 α hsat
      rw [show (0#32 : BitVec 32).toNat = 0 from rfl] at hk
      exact absurd hk (Nat.not_lt_zero _)
  have hw' : KittenWatchesOk ks' := by
    obtain ⟨ch, hc1, hc2, hc3, hc4⟩ := hinv.watches
    refine ⟨ch, hc1, hc2, hc3, fun l hl w hw => ?_⟩
    have hb := hc4 l hl w hw
    exact ⟨hb.1, by rw [hsz_eq _ (Nat.div_lt_of_lt_mul hb.1)]; exact hb.2.1, hb.2.2.1, hb.2.2.2⟩
  have hba' : KittenBaseAssignOk ks' := by
    have h0 := hinv.assign
    refine ⟨h0.trl_end_le, h0.prop_le, h0.unass_eq, h0.vals_dom, h0.vals_neg_iff,
      h0.vals_nz_iff_trl, h0.trl_nodup, h0.trl_lt, h0.trl_lvl_le, h0.unass_lvl_zero,
      h0.trl_lvl_mono, h0.dec_earliest, fun i hi hlv => ?_⟩
    have hl0 := h0.lvl0_ok i hi hlv
    refine ⟨hl0.1, hl0.2.1, hl0.2.2.1, by rw [horig_eq]; exact hl0.2.2.2.1, fun ha => ?_⟩
    have hrr := hl0.2.2.2.2 ha
    exact ⟨hrr.1, by rw [hlits_eq _ hrr.1]; exact hrr.2⟩
  have hrsn' : ReasonOk ks' := by
    intro i hi
    rcases hinv.reasons i hi with hd | ⟨hr_lt, hmem, hall⟩
    · exact Or.inl hd
    · right; rw [hlits_eq _ hr_lt]; exact ⟨hr_lt, hmem, hall⟩
  exact ⟨⟨hsh', hcl', hw', hba', hrsn'⟩, hsync, rfl,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, horig_eq,
      fun _ _ => rfl⟩⟩

/-- Parametric `Func.wp` proof for `full_kitten_build_failing`. -/
theorem full_kitten_build_failing_wp (Γ : Env) :
    ∀ args m Q X, fullKittenBuildFailingSpec args m Q X →
      Func.wp Γ full_kitten_build_failing_body args m Q X := by
  rintro ⟨kPtr, alit, ⟨⟩⟩ m Q X ⟨acap, ks, R, hinv, hsync, halit, halit_mem, hval2, hdec, hm, hQ⟩
  have hsh := hinv.shapes
  have hcl := hinv.clauses
  have hnv := hcl.nv_le
  have hnc := hcl.nc_le
  have hnv_128 : ks.nv.toNat ≤ 128 := by unfold kMaxV at hnv; exact hnv
  have hnv_28 : ks.nv.toNat < 2 ^ 28 := by omega
  obtain ⟨halit_div, halit_lt⟩ := bv32_lit_div2_bv halit
  have halit_128 : (alit >>> (1 : Nat)).toNat < 128 := by omega
  have halit_28 : (alit >>> (1 : Nat)).toNat < 2 ^ 28 := by omega
  have halit_fl_len : (alit >>> (1 : Nat)).toNat < ks.flags.length := by
    rw [hsh.flags_len]; exact halit_128
  have hmA := kittenMem_to_amem hsh hm; clear hm
  c0_hsteps_nogrp
  refine wp_while_state (proj := fun st : BitVec 32 × List (BitVec 32) => (st.1, ()))
    (fun st => ks.nv.toNat - st.1.toNat)
    (fun st m' =>
      st.1.toNat ≤ ks.nv.toNat ∧ st.2.length = 128 ∧
      (∀ v < st.1.toNat, (st.2[v]?.getD 0#32 &&& 2#32) = 0#32) ∧
      (KittenMemA kPtr acap { ks with flags := st.2 } ⋆ R) m')
    ?_ ?_
  · intro L1 hL1
    refine hL1 (0#32, ks.flags) m ⟨Nat.zero_le _, hsh.flags_len, fun _ h => by simp at h, hmA⟩
  · intro L1 ⟨i, fls⟩ m' ⟨hi_le, hfls_len, hclr, hm'⟩ ih
    dsimp only at hi_le hfls_len hclr hm' ⊢
    obtain ⟨ksF, hksF⟩ : ∃ x : KittenState, x = { ks with flags := fls } := ⟨_, rfl⟩
    rw [← hksF] at hm'
    c0_hsplit
    · have hi_lt : i.toNat < ks.nv.toNat := hc
      have hi_128 : i.toNat < 128 := by omega
      have hi_28 : i.toNat < 2 ^ 28 := by omega
      have hi1_wrap : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
      c0_hsteps!
      refine ih (i + 1#32, fls.set i.toNat (fls[i.toNat]?.getD 0#32 &&& ~~~2#32)) _
        (by dsimp only; rw [hi1_wrap]; omega) ⟨by dsimp only; rw [hi1_wrap]; omega,
          by simp [List.length_set, hfls_len], ?_, ?_⟩
      · intro v hv
        rw [hi1_wrap] at hv
        by_cases hvi : v = i.toNat
        · subst hvi
          rw [List.getElem?_set_self (by omega), Option.getD_some]
          exact fl_andnot2_and2_zero _
        · rw [List.getElem?_set_ne (Ne.symm hvi)]; exact hclr v (by omega)
      · refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hm
        rw [hksF]; kstate_ext <;> (first | rfl | kp_field)
    · have hi_eq : i.toNat = ks.nv.toNat := by
        have hhc : ¬ i.toNat < ks.nv.toNat := hc
        omega
      let fls1 := fls.set (alit >>> (1 : Nat)).toNat
        (fls[(alit >>> (1 : Nat)).toNat]?.getD 0#32 ||| 2#32)
      c0_hsteps_nogrp
      have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
        rw [hsh.trl_len]; have := hinv.assign.trl_end_le; omega
      obtain ⟨k0, hk0_lt, hk0_eq⟩ :=
        kitten_falsified_to_trail hsh hnv hinv.assign hsync halit hval2
      have hk0_div : (ks.trl[k0]?.getD 0#32).toNat / 2 = (alit >>> (1 : Nat)).toNat := by
        rw [hk0_eq, halit_div, ← litNeg_eq_xor1]
        rcases nat_xor1_cases alit.toNat with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
      have hfls1_len : fls1.length = 128 := by simp [fls1, hfls_len]
      have hinit_loop : FailingLoopInv ks ks.trl_end fls1 ks.clMeta := by
        refine ⟨Nat.le_refl _, hfls1_len, hsh.clMeta_len, fun c _ => Or.inl rfl, fun α hα => ?_⟩
        have hsat_a := (sat_unitsCnf_iff α (kittenAssumpLits ks)).mp
          (CNF.sat_append.mp hα).2 alit.toNat halit_mem
        refine ⟨k0, hk0_lt, ?_, ?_⟩
        · rw [hk0_div]
          simp only [fls1,
            List.getElem?_set_self (by omega : (alit >>> (1 : Nat)).toNat < fls.length),
            Option.getD_some]
          exact fl_or2_and2_nz _
        · rw [hk0_eq, litNeg_litNeg]; exact hsat_a
      refine wp_while_state
        (proj := fun st : BitVec 32 × List (BitVec 32) × List (BitVec 32) => (st.1, ()))
        (fun st => st.1.toNat)
        (fun st m'' => FailingLoopInv ks st.1 st.2.1 st.2.2 ∧
          (KittenMemA kPtr acap { ks with flags := st.2.1, clMeta := st.2.2 } ⋆ R) m'')
        ?_ ?_
      · intro L2 hL2
        refine wp_jump_state
          (proj := fun st : BitVec 32 × List (BitVec 32) × List (BitVec 32) => (st.1, ()))
          (ks.trl_end, fls1, ks.clMeta) (by rw [hksF]; kp_field; rfl)
          (hL2 (ks.trl_end, fls1, ks.clMeta) m ⟨hinit_loop, ?_⟩)
        refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hm
        rw [hksF]; kstate_ext <;> (first | rfl | kp_field |
          (dsimp only [fls1]; simp only [halit_div, BitVec.toNat_ushiftRight,
            Nat.shiftRight_eq_div_pow, BitVec.ofNat_eq_ofNat]; simp))
      · intro L2 ⟨i2, fls2, cms2⟩ m2 ⟨hloop2, hm2⟩ ih2
        dsimp only at hloop2 hm2 ⊢
        obtain ⟨ksC, hksC⟩ : ∃ x : KittenState,
            x = { ks with flags := fls2, clMeta := cms2 } := ⟨_, rfl⟩
        rw [← hksC] at hm2
        c0_hsplit
        · have hi2_pos : 0 < i2.toNat := hc
          have hi2_le := hloop2.1
          have hi2_sub : (i2 - 1#32).toNat = i2.toNat - 1 := by
            have := hinv.assign.trl_end_le; bv_omega
          have hi2_sub_128 : (i2 - 1#32).toNat < 128 := by
            have := hinv.assign.trl_end_le; omega
          have hi2_sub_28 : (i2 - 1#32).toNat < 2 ^ 28 := by omega
          let tlit := ks.trl[(i2 - 1#32).toNat]?.getD 0#32
          have htlit_lt : tlit.toNat < 2 * ks.nv.toNat :=
            hinv.assign.trl_lt tlit.toNat (mem_kittenTrailLits_of_lt (by rw [hi2_sub]; omega)
              htrl_len)
          obtain ⟨hv_div, hv_lt⟩ := bv32_lit_div2_bv htlit_lt
          have hbv_u1 : ∀ x : BitVec 32,
              (x >>> (1 : BitVec 32)).toNat = (x >>> (1 : Nat)).toNat := fun _ => rfl
          have hv_128 : (tlit >>> (1 : Nat)).toNat < 128 := by omega
          have hv_28 : (tlit >>> (1 : Nat)).toNat < 2 ^ 28 := by omega
          have htlit_128 :
              (ksC.trl[(i2 - 1).toNat]?.getD 0#32 >>> 1).toNat < 128 := by
            rw [hksC]; exact hv_128
          have htlit_bv28 :
              (ksC.trl[(i2 - 1).toNat]?.getD 0#32 >>> 1).toNat < 2 ^ 28 := by
            rw [hksC]; exact hv_28
          c0_hsplit
          try (refine LeanQbe.T.wp_unroll_group fun _ _ => ?_; c0_hsplit)
          · have hzero_flag : (fls2[(tlit >>> (1 : Nat)).toNat]?.getD 0#32 &&& 2#32) = 0#32 := by
              rw [hksC] at hc
              exact hc
            have hloop_skip := failingStep_skip_inv hsh hinv hloop2 hi2_pos (by
              rw [← hi2_sub]
              change (fls2[tlit.toNat / 2]?.getD 0#32 &&& 2#32) = 0#32
              rw [← hv_div]; exact hzero_flag)
            c0_hsteps!
            exact ih2 (i2 - 1#32, fls2, cms2) _ (by dsimp only; omega)
              ⟨hloop_skip, by rw [hksC] at hm2; exact hm2⟩
          · have hnz_flag : (fls2[(tlit >>> (1 : Nat)).toNat]?.getD 0#32 &&& 2#32) ≠ 0#32 := by
              rw [hksC] at hc
              exact hc
            let fls2_clr := fls2.set (tlit >>> (1 : Nat)).toNat
              (fls2[(tlit >>> (1 : Nat)).toNat]?.getD 0#32 &&& ~~~2#32)
            have hclr_len : fls2_clr.length = 128 := by simp [fls2_clr, hloop2.2.1]
            have hclr_eq : ∀ w < ks.nv.toNat,
                w ≠ (ks.trl[i2.toNat - 1]?.getD 0#32).toNat / 2 → fls2_clr[w]? = fls2[w]? := by
              intro w _ hw
              have hne_w : (tlit >>> (1 : Nat)).toNat ≠ w := by
                rw [hv_div]; dsimp only [tlit]; rw [hi2_sub]; exact hw.symm
              exact List.getElem?_set_ne hne_w
            c0_hsplit
            try (refine LeanQbe.T.wp_unroll_group fun _ _ => ?_; c0_hsplit)
            · have hi2_sub' :
                  (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + i2.toNat) % 2 ^ 32 =
                    (i2 - 1#32).toNat := by
                have := hinv.assign.trl_end_le; have := hloop2.1; bv_omega
              have hrsn_fff :
                  ks.rsn[(tlit >>> (1 : Nat)).toNat]?.getD 0#32 = 0xFFFFFFFF#32 := by
                have hc0 : ks.rsn[(ks.trl[(2 ^ 32 - BitVec.toNat (1 : BitVec 32) +
                    i2.toNat) % 2 ^ 32]?.getD 0#32).toNat / 2]?.getD 0#32 =
                    0xFFFFFFFF#32 := by
                  rw [hksC] at hc; exact hc
                rw [hi2_sub'] at hc0; rwa [hv_div]
              have hrsn_fff2 :
                  ks.rsn[(ks.trl[i2.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0#32 =
                    0xFFFFFFFF#32 := by
                rwa [← hi2_sub, ← hv_div]
              have hloop_dec := failingStep_dec_inv hsh hinv hdec hloop2 hi2_pos hrsn_fff2
                hclr_len hclr_eq
              c0_hsteps!
              refine ih2 (i2 - 1#32, fls2_clr, cms2) _ (by dsimp only; omega) ⟨hloop_dec, ?_⟩
              refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hm
              rw [hksC]; kstate_ext <;> (first | rfl | kp_field |
                (dsimp only [fls2_clr, tlit]; simp [BitVec.toNat_ushiftRight,
                  Nat.shiftRight_eq_div_pow, BitVec.ofNat_eq_ofNat]))
            · have hi2_sub' :
                  (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + i2.toNat) % 2 ^ 32 =
                    (i2 - 1#32).toNat := by
                have := hinv.assign.trl_end_le; have := hloop2.1; bv_omega
              let rsn := ks.rsn[(tlit >>> (1 : Nat)).toNat]?.getD 0#32
              have hrsn_ne : rsn ≠ 0xFFFFFFFF#32 := by
                have hc0 : ks.rsn[(ks.trl[(2 ^ 32 - BitVec.toNat (1 : BitVec 32) +
                    i2.toNat) % 2 ^ 32]?.getD 0#32).toNat / 2]?.getD 0#32 ≠
                    0xFFFFFFFF#32 := by
                  rw [hksC] at hc; exact hc
                rw [hi2_sub'] at hc0; dsimp only [rsn]; rwa [hv_div]
              have hrsn_fff_eq : rsn =
                  ks.rsn[(ks.trl[i2.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 := by
                dsimp only [rsn]; rw [← hi2_sub, ← hv_div]
                rw [List.getElem?_eq_getElem (by rw [hsh.rsn_len]; exact hv_128)]; rfl
              have hro := hinv.reasons (i2.toNat - 1) (by omega)
              dsimp only at hro
              have hrsn_lt : rsn.toNat < ks.nc.toNat := by
                have hr_get : ks.rsn[(ks.trl[i2.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0#32 =
                    rsn := by
                  dsimp only [rsn]; rw [← hi2_sub, ← hv_div]
                rw [hr_get] at hro
                rcases hro with hfff | ⟨hlt, _⟩
                · exact absurd hfff hrsn_ne
                · exact hlt
              have hrsn_896 : rsn.toNat < 896 := by unfold kMaxCl at hnc; omega
              have hrsn_28 : rsn.toNat < 2 ^ 28 := by omega
              let cms2' := cms2.set rsn.toNat (cms2[rsn.toNat]?.getD 0#32 ||| kmCore)
              let soff := ks.clOff[rsn.toNat]?.getD 0#32
              let ssz := cms2'[rsn.toNat]?.getD 0#32 &&& 0xFFFF#32
              have hssz_eq : ssz.toNat = kittenClauseSize ks rsn.toNat := by
                dsimp only [ssz, cms2']
                rw [List.getElem?_set_self (by rw [hloop2.2.2.1]; omega), Option.getD_some]
                rcases hloop2.2.2.2.1 rsn.toNat hrsn_lt with h1 | h2
                · rw [h1, cm_or_core_and_ffff]; rfl
                · rw [h2]
                  have heq_or : (ks.clMeta[rsn.toNat]?.getD 0#32 ||| kmCore) ||| kmCore =
                      ks.clMeta[rsn.toNat]?.getD 0#32 ||| kmCore := by
                    apply BitVec.eq_of_getElem_eq; intro b _
                    simp only [BitVec.getElem_or]
                    cases _ : (ks.clMeta[rsn.toNat]?.getD 0#32)[b] <;> cases _ : kmCore[b] <;> simp
                  rw [heq_or, cm_or_core_and_ffff]; rfl
              have hwf_r := hcl.cl_wf rsn.toNat hrsn_lt
              have hsoff_ssz : kittenClauseOff ks rsn.toNat + kittenClauseSize ks rsn.toNat ≤
                  ks.alen.toNat := by
                have := hwf_r.2.2.1; unfold kittenClauseSpan at this; omega
              have hm_m :
                  (KittenMemA kPtr acap { ks with flags := fls2_clr, clMeta := cms2 } ⋆ R) m := by
                refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hm
                rw [hksC]; kstate_ext <;> (first | rfl | kp_field |
                  (dsimp only [fls2_clr, tlit]; simp [BitVec.toNat_ushiftRight,
                    Nat.shiftRight_eq_div_pow, BitVec.ofNat_eq_ofNat]))
              clear hm
              obtain ⟨ksM, hksM⟩ : ∃ x : KittenState,
                  x = { ks with flags := fls2_clr, clMeta := cms2 } := ⟨_, rfl⟩
              have hm : (KittenMemA kPtr acap ksM ⋆ R) m := by rw [hksM]; exact hm_m
              have hput_flags_rsn : ∀ (idx : Nat) (v : BitVec 32),
                  (ksC.putArr .flags idx v).rsn = ks.rsn :=
                fun _ _ => by rw [hksC]; rfl
              have htrl_ksC : ksC.trl = ks.trl := by rw [hksC]
              have hrsn_c_eq :
                  ks.rsn[(ks.trl[(i2 - 1).toNat]?.getD 0#32 >>> (1 : Nat)).toNat]?.getD 0#32 =
                    rsn := by
                dsimp only [rsn, tlit]; rfl
              have hrsn_c_eq' :
                  ks.rsn[(ks.trl[(i2 - 1#32).toNat]?.getD 0#32 >>> (1 : Nat)).toNat]?.getD 0#32 =
                    rsn := by
                dsimp only [rsn, tlit]
              rw [hput_flags_rsn, htrl_ksC]
              try rw [hrsn_c_eq]
              try rw [hrsn_c_eq']
              c0_hsteps_nogrp
              have hsz_g :
                  ((ksM.putArr .clMeta rsn.toNat (ksM.clMeta[rsn.toNat]?.getD 0#32 |||
                      (65536 : BitVec 32))).clMeta[rsn.toNat]?.getD 0#32 &&&
                    (65535 : BitVec 32)) = ssz := by
                rw [hksM]; dsimp only [KittenState.putArr, ssz, cms2']
                simp only [List.getElem?_set_self (by rw [hloop2.2.2.1]; omega),
                  Option.getD_some]
                rfl
              have hoff_g :
                  (ksM.putArr .clMeta rsn.toNat (ksM.clMeta[rsn.toNat]?.getD 0#32 |||
                      (65536 : BitVec 32))).clOff[rsn.toNat]?.getD 0#32 = soff := by
                rw [hksM]; rfl
              try rw [hoff_g]
              try rw [hsz_g]
              refine wp_while_state (proj := fun st : BitVec 32 × List (BitVec 32) => (st.1, ()))
                (fun st => ssz.toNat - st.1.toNat)
                (fun st m3 =>
                  st.1.toNat ≤ ssz.toNat ∧ st.2.length = 128 ∧
                  (∀ w < ks.nv.toNat,
                    (fls2_clr[w]?.getD 0#32 &&& 2#32) ≠ 0#32 →
                    (st.2[w]?.getD 0#32 &&& 2#32) ≠ 0#32) ∧
                  (∀ q < st.1.toNat,
                    let lv := (ks.arena[kittenClauseOff ks rsn.toNat + q]?.getD 0#32).toNat / 2
                    lv ≠ (ks.trl[i2.toNat - 1]?.getD 0#32).toNat / 2 →
                    (st.2[lv]?.getD 0#32 &&& 2#32) ≠ 0#32) ∧
                  (KittenMemA kPtr acap { ks with flags := st.2, clMeta := cms2' } ⋆ R) m3)
                ?_ ?_
              · intro L3 hL3
                refine hL3 (0#32, fls2_clr) _ ⟨Nat.zero_le _, hclr_len, fun _ _ h => h,
                  fun _ h => by simp at h, ?_⟩
                refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hm
                rw [hksM]; kstate_ext <;> (first | rfl | kp_field)
              · intro L3 ⟨j, fls3⟩ m3 ⟨hj_le, hfl3_len, hkeep3, hmark3, hm3⟩ ih3
                dsimp only at hj_le hfl3_len hkeep3 hmark3 hm3 ⊢
                obtain ⟨ksJ, hksJ⟩ : ∃ x : KittenState,
                    x = { ks with flags := fls3, clMeta := cms2' } := ⟨_, rfl⟩
                rw [← hksJ] at hm3
                c0_hsplit
                · have hj_lt : j.toNat < ssz.toNat := hc
                  have hj_sz : j.toNat < kittenClauseSize ks rsn.toNat := by omega
                  have har_lt_a : kittenClauseOff ks rsn.toNat + j.toNat < ks.arena.length := by
                    rw [hsh.arena_len]; have := hcl.alen_le; omega
                  have har_28 : soff.toNat + j.toNat < 2 ^ 28 := by
                    change kittenClauseOff ks rsn.toNat + j.toNat < 2 ^ 28
                    have := hcl.alen_le; have := hcl.acap_lt; unfold dimacsBound at *; omega
                  have har_cap : soff.toNat + j.toNat < acap := by
                    change kittenClauseOff ks rsn.toNat + j.toNat < acap
                    have := hcl.alen_le; omega
                  have hlv_mem : (ks.arena[kittenClauseOff ks rsn.toNat + j.toNat]'har_lt_a).toNat ∈
                      kittenClauseLits ks rsn.toNat := by
                    unfold kittenClauseLits; rw [List.mem_map]
                    refine ⟨ks.arena[kittenClauseOff ks rsn.toNat + j.toNat]'har_lt_a, ?_, rfl⟩
                    rw [List.mem_iff_getElem]
                    exact ⟨j.toNat, by
                        simp [List.length_take, List.length_drop]
                        rw [hsh.arena_len]; have := hcl.alen_le; omega,
                      by simp [List.getElem_take, List.getElem_drop]⟩
                  have hlv_lit := hwf_r.2.2.2.1 _ hlv_mem
                  let ot := ks.arena[soff.toNat + j.toNat]?.getD 0#32
                  have hot_eq : ot = ks.arena[kittenClauseOff ks rsn.toNat + j.toNat]'har_lt_a := by
                    dsimp only [ot]
                    rw [show soff.toNat = kittenClauseOff ks rsn.toNat from rfl,
                      List.getElem?_eq_getElem har_lt_a, Option.getD_some]
                  obtain ⟨hlv_div, hlv_nv⟩ :=
                    bv32_lit_div2_bv (l := ot) (by rw [hot_eq]; exact hlv_lit)
                  have hlv_128 : (ot >>> (1 : Nat)).toNat < 128 := by omega
                  have hlv_28 : (ot >>> (1 : Nat)).toNat < 2 ^ 28 := by omega
                  have hlvJ_128 :
                      (ksJ.arena[soff.toNat + j.toNat]?.getD 0#32 >>> (1 : Nat)).toNat < 128 := by
                    rw [hksJ]; exact hlv_128
                  have hlvJ_28 :
                      (ksJ.arena[soff.toNat + j.toNat]?.getD 0#32 >>> (1 : Nat)).toNat <
                        2 ^ 28 := by
                    rw [hksJ]; exact hlv_28
                  have hj1_wrap : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
                  c0_hsplit
                  try (refine LeanQbe.T.wp_unroll_group fun _ _ => ?_; c0_hsplit)
                  · have hne_lv : (ot >>> (1 : Nat)) ≠ (tlit >>> (1 : Nat)) := by
                      have hc0 : (ot >>> (1 : BitVec 32)) ≠ (tlit >>> (1 : BitVec 32)) := by
                        rw [hksJ] at hc; exact hc
                      intro heq; apply hc0
                      exact BitVec.eq_of_toNat_eq (by
                        rw [hbv_u1, hbv_u1]; exact congrArg BitVec.toNat heq)
                    have hne_nat : (ot >>> (1 : Nat)).toNat ≠ (tlit >>> (1 : Nat)).toNat :=
                      fun h => hne_lv (BitVec.eq_of_toNat_eq h)
                    let fls3' := fls3.set (ot >>> (1 : Nat)).toNat
                      (fls3[(ot >>> (1 : Nat)).toNat]?.getD 0#32 ||| 2#32)
                    c0_hsteps!
                    refine ih3 (j + 1#32, fls3') _ (by dsimp only; rw [hj1_wrap]; omega)
                      ⟨by dsimp only; rw [hj1_wrap]; omega, by simp [fls3', hfl3_len], ?_, ?_, ?_⟩
                    · intro w hw hflw
                      by_cases hwo : w = (ot >>> (1 : Nat)).toNat
                      · subst hwo
                        simp only [fls3', List.getElem?_set_self (by rw [hfl3_len]; exact hlv_128),
                          Option.getD_some]
                        exact fl_or2_and2_nz _
                      · dsimp only [fls3']
                        rw [List.getElem?_set_ne (Ne.symm hwo)]
                        exact hkeep3 w hw hflw
                    · intro q hq lv hne_q
                      dsimp only [lv] at hne_q ⊢
                      rw [hj1_wrap] at hq
                      by_cases hqj : q = j.toNat
                      · subst hqj
                        change (fls3'[ot.toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32
                        rw [← hlv_div]
                        simp only [fls3',
                          List.getElem?_set_self (by rw [hfl3_len]; exact hlv_128),
                          Option.getD_some]
                        exact fl_or2_and2_nz _
                      · have hmk := hmark3 q (by omega) hne_q
                        by_cases hqo : (ks.arena[kittenClauseOff ks rsn.toNat + q]?.getD
                            0#32).toNat / 2 = (ot >>> (1 : Nat)).toNat
                        · rw [hqo]
                          simp only [fls3',
                            List.getElem?_set_self (by rw [hfl3_len]; exact hlv_128),
                            Option.getD_some]
                          exact fl_or2_and2_nz _
                        · dsimp only [fls3']
                          rw [List.getElem?_set_ne (Ne.symm hqo)]
                          exact hmk
                    · refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hm
                      rw [hksJ]; kstate_ext <;> (first | rfl | kp_field)
                  · have heq_lv : (ot >>> (1 : Nat)) = (tlit >>> (1 : Nat)) := by
                      have hc0 : (ot >>> (1 : BitVec 32)) = (tlit >>> (1 : BitVec 32)) := by
                        rw [hksJ] at hc; exact hc
                      exact BitVec.eq_of_toNat_eq (by
                        rw [← hbv_u1, ← hbv_u1]; exact congrArg BitVec.toNat hc0)
                    c0_hsteps!
                    refine ih3 (j + 1#32, fls3) _ (by dsimp only; rw [hj1_wrap]; omega)
                      ⟨by dsimp only; rw [hj1_wrap]; omega, hfl3_len, hkeep3, ?_,
                        by rw [← hksJ]; exact hm3⟩
                    intro q hq lv hne_q
                    dsimp only [lv] at hne_q ⊢
                    rw [hj1_wrap] at hq
                    by_cases hqj : q = j.toNat
                    · subst hqj
                      exfalso; apply hne_q
                      change (ot.toNat / 2) = _
                      rw [← hlv_div, heq_lv, hv_div]
                      dsimp only [tlit]; rw [hi2_sub]
                    · exact hmark3 q (by omega) hne_q
                · have hj_eq : j.toNat = ssz.toNat := by
                    have hhc : ¬ j.toNat < ssz.toNat := hc
                    omega
                  have hmark_all : ∀ q < kittenClauseSize ks rsn.toNat,
                      (ks.arena[kittenClauseOff ks rsn.toNat + q]?.getD 0#32).toNat / 2 ≠
                        (ks.trl[i2.toNat - 1]?.getD 0#32).toNat / 2 →
                      (fls3[(ks.arena[kittenClauseOff ks rsn.toNat + q]?.getD 0#32).toNat / 2]?.getD
                        0#32 &&& 2#32) ≠ 0#32 :=
                    fun q hq => hmark3 q (by omega)
                  have hloop_fin := failingStep_finish_inv hsh hinv hloop2 hi2_pos hrsn_ne
                    hrsn_fff_eq hclr_eq hkeep3 hmark_all hfl3_len
                  c0_hsteps!
                  exact ih2 (i2 - 1#32, fls3, cms2') _ (by dsimp only; omega)
                    ⟨hloop_fin, by rw [hksJ] at hm3; exact hm3⟩
        · have hi2_eq : i2 = 0#32 := by
            have : ¬ 0 < i2.toNat := hc
            bv_omega
          subst hi2_eq
          c0_hsteps_nogrp
          refine wp_while_state (proj := fun st : BitVec 32 × List (BitVec 32) => (st.1, ()))
            (fun st => ks.nv.toNat - st.1.toNat)
            (fun st m4 =>
              st.1.toNat ≤ ks.nv.toNat ∧ st.2.length = 128 ∧
              (∀ v < st.1.toNat, (st.2[v]?.getD 0#32 &&& 2#32) = 0#32) ∧
              (KittenMemA kPtr acap { ks with flags := st.2, clMeta := cms2 } ⋆ R) m4)
            ?_ ?_
          · intro L4 hL4
            refine hL4 (0#32, fls2) _ ⟨Nat.zero_le _, hloop2.2.1, fun _ h => by simp at h,
              by rw [hksC] at hm2; exact hm2⟩
          · intro L4 ⟨i4, fls4⟩ m4 ⟨hi4_le, hfl4_len, hclr4, hm4⟩ ih4
            dsimp only at hi4_le hfl4_len hclr4 hm4 ⊢
            obtain ⟨ks4, hks4⟩ : ∃ x : KittenState,
                x = { ks with flags := fls4, clMeta := cms2 } := ⟨_, rfl⟩
            rw [← hks4] at hm4
            c0_hsplit
            · have hi4_lt : i4.toNat < ks.nv.toNat := hc
              have hi4_128 : i4.toNat < 128 := by omega
              have hi4_28 : i4.toNat < 2 ^ 28 := by omega
              have hi4_wrap : (i4 + 1#32).toNat = i4.toNat + 1 := by bv_omega
              c0_hsteps!
              refine ih4 (i4 + 1#32, fls4.set i4.toNat (fls4[i4.toNat]?.getD 0#32 &&& ~~~2#32)) _
                (by dsimp only; rw [hi4_wrap]; omega) ⟨by dsimp only; rw [hi4_wrap]; omega,
                  by simp [hfl4_len], ?_, ?_⟩
              · intro v hv
                rw [hi4_wrap] at hv
                by_cases hvi : v = i4.toNat
                · subst hvi
                  rw [List.getElem?_set_self (by omega), Option.getD_some]
                  exact fl_andnot2_and2_zero _
                · rw [List.getElem?_set_ne (Ne.symm hvi)]; exact hclr4 v (by omega)
              · refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hm
                rw [hks4]; kstate_ext <;> (first | rfl | kp_field)
            · have hi4_eq : i4.toNat = ks.nv.toNat := by
                have hhc : ¬ i4.toNat < ks.nv.toNat := hc
                omega
              have hclean_fin : ∀ v < ks.nv.toNat, (fls4[v]?.getD 0#32 &&& 2#32) = 0#32 :=
                fun v hv => hclr4 v (by omega)
              have hloop_fin : FailingLoopInv ks 0#32 fls4 cms2 :=
                ⟨Nat.zero_le _, hfl4_len, hloop2.2.2.1, hloop2.2.2.2.1, fun α hα => by
                  obtain ⟨k, hk, _⟩ := hloop2.2.2.2.2 α hα
                  rw [show (0#32 : BitVec 32).toNat = 0 from rfl] at hk
                  exact absurd hk (Nat.not_lt_zero _)⟩
              have hfin := failingFinish_preserves hsh hinv hsync hloop_fin hclean_fin
              c0_hsteps!
              obtain ⟨_, hm_fin⟩ := kittenMemA_to_mem hm
              refine hQ _ _ hfin.1 hfin.2.1 hfin.2.2.1 hfin.2.2.2
                (Eq.mp (congrArg (fun x => (KittenMem kPtr x ⋆ R) _) ?_) hm_fin)
              rw [hks4]; kstate_ext <;> (first | rfl | kp_field)

/-! ## 8. `full_kitten_flip_wp` (`9/15`) -/

/-- Parametric `Func.wp` proof for `full_kitten_flip`. -/
theorem full_kitten_flip_wp (Γ : Env) :
    ∀ args m Q X, fullKittenFlipSpec args m Q X →
      Func.wp Γ full_kitten_flip_body args m Q X := by
  rintro ⟨hPtr, lit, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hinv_s, hlit_lt, hm, hQ⟩
  rcases hinv_s with ⟨hscr_ge, hscr_lt, hinv⟩
  let scr := s.scratch.scratch_buf
  have hscr_len : s.scratch.scratch_buf.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hscr_8864 : 8864 ≤ s.scratch.scratch_buf.length := by
    unfold kMinScratchCap at hscr_ge; omega
  have hscr_256 : 256 ≤ scr.length := by dsimp only [scr]; omega
  let acap := scr.length - 8864
  let ks := kittenStateOfScratch scr
  have hsh := hinv.shapes
  have hcl := hinv.clauses
  have hnv := hcl.nv_le
  have hnc := hcl.nc_le
  obtain ⟨hv_div, hv_lt⟩ := bv32_lit_div2_bv hlit_lt
  have hlit_256 : lit.toNat < 256 := by unfold kMaxV at hnv; omega
  have hlit_28 : lit.toNat < 2 ^ 28 := by omega
  have hv_128 : (lit >>> (1 : Nat)).toNat < 128 := by unfold kMaxV at hnv; omega
  have hv_28 : (lit >>> (1 : Nat)).toNat < 2 ^ 28 := by omega
  have hmF : (FullKittenFrame c s ⋆
      KittenMem (c.pScratchBuf + BitVec.ofNat 64 256 * 4) ks ⋆ R) m := by
    have hfull := fullMem_eq_kittenFrame (c := c) (s := s) hscr_8864
    rw [show (1024#64 : BitVec 64) = BitVec.ofNat 64 256 * 4 from by decide] at hfull
    rw [hfull] at hm; exact sep_ac hm
  clear hm
  let kPtr := c.pScratchBuf + BitVec.ofNat 64 256 * 4
  have hmA : (KittenMemA kPtr acap ks ⋆ (FullKittenFrame c s ⋆ R)) m := by
    have hm1 : (KittenMem kPtr ks ⋆ (FullKittenFrame c s ⋆ R)) m := sep_ac hmF
    exact kittenMem_to_amem hsh hm1
  clear hmF
  have hret_unchanged : ∀ m',
      (KittenMemA kPtr acap ks ⋆ (FullKittenFrame c s ⋆ R)) m' →
      Q (false, ()) m' := by
    intro m' hm'
    obtain ⟨_, hm''⟩ := kittenMemA_to_mem hm'
    have hmF' : (FullKittenFrame c s ⋆ KittenMem kPtr ks ⋆ R) m' := sep_ac hm''
    have hm_full := fullMem_join_kitten (c := c) (s := s) (acap := acap) (ks' := ks)
      (R := R) hscr_256 hsh hmF'
    have hscr_orig : scr.take 256 ++ ks.toSlab = scr := by
      unfold ks kittenStateOfScratch
      rw [KittenState.toSlab_ofSlab (by simp; dsimp only [scr]; omega), List.take_append_drop]
    rw [hscr_orig] at hm_full
    exact hQ false scr m' hlen (fun _ _ => rfl) ⟨hscr_ge, hscr_lt, hinv⟩
      rfl rfl rfl rfl rfl (KittenCnfPermEquiv.refl _) (fun _ _ => rfl) hm_full
  c0_hsplit
  · exfalso
    have hge : ks.nv.toNat ≤ (lit >>> (1 : Nat)).toNat := by
      change ks.nv.toNat ≤ (lit >>> (1 : BitVec 32)).toNat
      exact hc
    dsimp only [ks, scr] at hge
    omega
  · c0_hsplit; try (refine LeanQbe.T.wp_unroll_group fun _ _ => ?_; c0_hsteps_nogrp; c0_hsplit)
    · c0_hsteps!
      exact hret_unchanged m hmA
    · have hvals_get : ks.vals[lit.toNat]?.getD 0#32 = 1#32 := hc
      c0_hsplit
      · c0_hsteps!
        exact hret_unchanged m hmA
      · have hval1 : ks.vals[lit.toNat]? = some 1#32 := by
          rw [List.getElem?_eq_getElem (by rw [hsh.vals_len]; exact hlit_256),
            Option.getD_some] at hvals_get
          rw [List.getElem?_eq_getElem (by rw [hsh.vals_len]; exact hlit_256), hvals_get]
        have hlvl_nz : ks.lvlArr[(lit >>> (1 : Nat)).toNat]?.getD 0#32 ≠ 0#32 := by
          change ks.lvlArr[lit.toNat / 2]?.getD 0#32 ≠ 0#32
          exact hc
        obtain ⟨chains0, hwc0⟩ := WChainCursor.init hsh hnv hinv.watches hlit_lt
        c0_hsteps_nogrp
        refine wp_while_state
          (proj := fun st : BitVec 32 × BitVec 32 × List Nat × List Nat × KittenState ×
            List (List Nat) => (st.2.1, st.1, ()))
          (fun st => st.2.2.2.1.length)
          (fun st m' =>
            let prev := st.1; let w := st.2.1; let done := st.2.2.1
            let todo := st.2.2.2.1; let ksW := st.2.2.2.2.1; let ch := st.2.2.2.2.2
            WChainCursor ksW lit.toNat ch done todo prev w ∧ ksW.Inv acap ∧
            KittenCnfPermEquiv (kittenOrigClauses ksW) (kittenOrigClauses ks) ∧
            ksW.nv = ks.nv ∧ ksW.orig_nc = ks.orig_nc ∧ ksW.ante = ks.ante ∧
            ksW.nassump = ks.nassump ∧ ksW.assump = ks.assump ∧ ksW.vals = ks.vals ∧
            ksW.lvlArr = ks.lvlArr ∧ ksW.clAux = ks.clAux ∧
            (KittenMemA kPtr acap ksW ⋆ (FullKittenFrame c s ⋆ R)) m')
          ?_ ?_
        · intro L0 hL0
          exact hL0 (0xFFFFFFFF#32, ks.whead[lit.toNat]?.getD 0#32, [],
            chains0[lit.toNat]?.getD [], ks, chains0) m
            ⟨hwc0, hinv, KittenCnfPermEquiv.refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hmA⟩
        · intro L0 ⟨prev, w, done, todo, ksW, chW⟩ m'
            ⟨hwc, hinvW, hpermW, w_nv, w_on, w_an, w_na, w_as, w_va, w_la, w_ca, hmW⟩ ih
          dsimp only at hwc hinvW hpermW w_nv w_on w_an w_na w_as w_va w_la w_ca hmW ⊢
          have hshW := hinvW.shapes
          have hclW := hinvW.clauses
          have hnvW := hclW.nv_le
          have hncW := hclW.nc_le
          have hlit_ltW : lit.toNat < 2 * ksW.nv.toNat := by rw [w_nv]; exact hlit_lt
          have hfinish_ret : ∀ (ok : Bool) (ksF : KittenState) (mF : Mem 64),
              ksF.Inv acap → KittenCnfPermEquiv (kittenOrigClauses ksF) (kittenOrigClauses ks) →
              ksF.nv = ks.nv → ksF.orig_nc = ks.orig_nc → ksF.ante = ks.ante →
              ksF.nassump = ks.nassump → ksF.assump = ks.assump → ksF.clAux = ks.clAux →
              (KittenMemA kPtr acap ksF ⋆ (FullKittenFrame c s ⋆ R)) mF → Q (ok, ()) mF := by
            intro ok ksF mF hinvF hpermF f_nv f_on f_an f_na f_as f_ca hmF
            have hshF := hinvF.shapes
            obtain ⟨_, hmF'⟩ := kittenMemA_to_mem hmF
            have hm_exp : (FullKittenFrame c s ⋆ KittenMem kPtr ksF ⋆ R) mF := sep_ac hmF'
            have hm_full := fullMem_join_kitten (c := c) (s := s) (acap := acap)
              (ks' := ksF) (R := R) hscr_256 hshF hm_exp
            let scr' := scr.take 256 ++ ksF.toSlab
            have hscr'_len : scr'.length = c.scratch_cap := by
              simp only [scr', List.length_append,
                List.length_take_of_le hscr_256,
                KittenState.toSlab_length hshF]
              dsimp only [acap, scr]; omega
            have hpre : ∀ x < kBase, scr'[x]? = scr[x]? := by
              intro x hx
              have htk : x < (scr.take 256).length := by
                rw [List.length_take_of_le hscr_256]
                unfold kBase at hx; omega
              rw [List.getElem?_append_left htk, List.getElem?_take_of_lt
                (by unfold kBase at hx; omega)]
            have hof : kittenStateOfScratch scr' = ksF := by
              unfold kittenStateOfScratch
              rw [slab_drop_exact _ ksF.toSlab (by
                rw [List.length_take_of_le hscr_256])]
              exact KittenState.ofSlab_toSlab hshF
            have hks_inv : KittenScratchInv scr' := by
              refine ⟨by dsimp only [acap, scr] at *; omega, by rw [hscr'_len]; exact c.hscr, ?_⟩
              rw [hof, hscr'_len, show c.scratch_cap - 8864 = acap by dsimp only [acap, scr]; omega]
              exact hinvF
            refine hQ ok scr' mF (fullState_lengthsOk_scratch hlen hscr'_len) hpre hks_inv
              (by rw [hof]; exact f_nv) (by rw [hof]; exact f_on)
              (by rw [hof]; exact f_an) (by rw [hof]; exact f_na)
              (by unfold kittenAssumpLitsS; rw [hof]
                  exact kittenAssumpLits_eq_of
                    (by rw [hshF.assump_len]; exact hinvF.clauses.nassump_le)
                    (by rw [hsh.assump_len]; exact hcl.nassump_le) f_na
                    (fun _ _ => by rw [f_as]))
              (by unfold kittenOrigClausesS; rw [hof]; exact hpermF)
              (fun ci hci => by rw [hof, f_ca]) hm_full
          c0_hsplit
          · have hw_ne : w ≠ 0xFFFFFFFF#32 := by bv_omega
            obtain ⟨w0, todo', hw0_wn, rfl, rfl, hw0_nc, hw0_1792, hw_tn, hw_div2, hw_mod2,
              hsz_ge, har_slot_l, hwb_lt, htail_nxt⟩ :=
              hwc.step_unfold hshW hncW hlit_ltW hw_ne
            have hw_28 : (BitVec.ofNat 32 w0).toNat < 2 ^ 28 := by omega
            have hw_1792 : (BitVec.ofNat 32 w0).toNat < 1792 := by omega
            have hcid_lt : w0 / 2 < ksW.nc.toNat := by omega
            have hcid_896 : w0 / 2 < 896 := by unfold kMaxCl at hncW; omega
            have hcid_28 : w0 / 2 < 2 ^ 28 := by omega
            have hwf_c := hclW.cl_wf (w0 / 2) hcid_lt
            have hoff_ssz : kittenClauseOff ksW (w0 / 2) + kittenClauseSize ksW (w0 / 2) ≤
                ksW.alen.toNat := by
              have := hwf_c.2.2.1; unfold kittenClauseSpan at this; omega
            have hother_slot_lt : (w0 % 2 ^^^ 1) < kittenClauseSize ksW (w0 / 2) := by
              rcases Nat.mod_two_eq_zero_or_one w0 with h | h <;> simp [h] <;> omega
            have hother_lt_ar : kittenClauseOff ksW (w0 / 2) + (w0 % 2 ^^^ 1) <
                ksW.arena.length := by
              rw [hshW.arena_len]; have := hclW.alen_le; omega
            have hother_mem : (ksW.arena[kittenClauseOff ksW (w0 / 2) + (w0 % 2 ^^^ 1)]'
                hother_lt_ar).toNat ∈ kittenClauseLits ksW (w0 / 2) := by
              unfold kittenClauseLits; rw [List.mem_map]
              refine ⟨_, ?_, rfl⟩
              rw [List.mem_iff_getElem]
              exact ⟨w0 % 2 ^^^ 1, by
                  simp [List.length_take, List.length_drop, hshW.arena_len]
                  have := hclW.alen_le; omega,
                by simp [List.getElem_take, List.getElem_drop]⟩
            have hother_lt : (ksW.arena[kittenClauseOff ksW (w0 / 2) + (w0 % 2 ^^^ 1)]'
                hother_lt_ar).toNat < 2 * ksW.nv.toNat := hwf_c.2.2.2.1 _ hother_mem
            let other := ksW.arena[kittenClauseOff ksW (w0 / 2) + (w0 % 2 ^^^ 1)]?.getD 0#32
            have hother_256 : other.toNat < 256 := by
              dsimp only [other]; rw [List.getElem?_eq_getElem hother_lt_ar, Option.getD_some]
              unfold kMaxV at hnvW; omega
            have hother_28 : other.toNat < 2 ^ 28 := by omega
            have hother_nv : other.toNat < 2 * ksW.nv.toNat := by
              dsimp only [other]; rw [List.getElem?_eq_getElem hother_lt_ar, Option.getD_some]
              exact hother_lt
            have hw_sh1 : (BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat = w0 / 2 := by
              simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                Nat.mod_eq_of_lt (by omega : w0 < 2 ^ 32)]
            have hw_sh_896 : (BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat < 896 := by
              rw [hw_sh1]; exact hcid_896
            have hw_sh_28 : (BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat < 2 ^ 28 := by
              rw [hw_sh1]; exact hcid_28
            have hslot_lt2 :
                (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^ (1 : BitVec 32)).toNat < 2 := by
              have hlt : (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^ (1 : BitVec 32)).toNat =
                  w0 % 2 ^^^ 1 := by
                rw [BitVec.toNat_xor, BitVec.toNat_and, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (by omega : w0 < 2 ^ 32)]
                simp [Nat.and_one_is_mod]
              rw [hlt]; rcases Nat.mod_two_eq_zero_or_one w0 with h | h <;> simp [h]
            have hcl_off_wrap :
                (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                  (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^ (1 : BitVec 32)).toNat <
                  2 ^ 28 := by
              rw [hw_sh1]; change kittenClauseOff ksW (w0 / 2) + _ < 2 ^ 28
              have := hclW.alen_le; have := hclW.acap_lt; unfold dimacsBound at *; omega
            have hcl_off_acap :
                (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                  (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^ (1 : BitVec 32)).toNat <
                  acap := by
              rw [hw_sh1]; change kittenClauseOff ksW (w0 / 2) + _ < acap
              have := hclW.alen_le; omega
            have hother_bv_256 :
                (ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>>
                    (1 : Nat)).toNat]?.getD 0#32).toNat +
                  (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^ (1 : BitVec 32)).toNat]?.getD
                  0#32).toNat < 256 := by
              rw [hw_sh1]
              have hlt : (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^ (1 : BitVec 32)).toNat =
                  w0 % 2 ^^^ 1 := by
                rw [BitVec.toNat_xor, BitVec.toNat_and, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (by omega : w0 < 2 ^ 32)]
                simp [Nat.and_one_is_mod]
              rw [hlt]; exact hother_256
            have hother_bv_28 :
                (ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>>
                    (1 : Nat)).toNat]?.getD 0#32).toNat +
                  (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^ (1 : BitVec 32)).toNat]?.getD
                  0#32).toNat < 2 ^ 28 := by omega
            iterate 24 c0_hstep
            refine head_wp_load rfl
              (KittenMemATactics.load_ka_arena_off hcl_off_wrap hcl_off_acap hmW) ?_
            c0_hsplit
            try (refine LeanQbe.T.wp_unroll_group fun _ _ => ?_; c0_hsplit)
            · obtain ⟨hkp_inv, hkp_wc, hkp_nv, _, hkp_on, _, _, _, _, _, _, hkp_an, hkp_na,
                  hkp_as, hkp_va, hkp_la, _, _, _, _, hkp_ca, _⟩ :=
                kittenWatchKeep_preserves hshW hinvW hlit_ltW hwc hother_nv
              have hother_bv_eq :
                  (ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>>
                      (1 : Nat)).toNat]?.getD 0#32).toNat +
                    (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^ (1 : BitVec 32)).toNat]?.getD
                    0#32) = other := by
                have hlt : (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^ (1 : BitVec 32)).toNat =
                    w0 % 2 ^^^ 1 := by
                  rw [BitVec.toNat_xor, BitVec.toNat_and, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega : w0 < 2 ^ 32)]
                  simp [Nat.and_one_is_mod]
                rw [hw_sh1, hlt]; rfl
              c0_hsteps!
              rw [hw_tn]
              refine ih (BitVec.ofNat 32 w0, ksW.wnext[w0]?.getD 0#32, done ++ [w0], todo',
                  ksW.putArr .wblit w0 other, chW) _ (by simp)
                ⟨hkp_wc, hkp_inv,
                  (by change KittenCnfPermEquiv (kittenOrigClauses ksW) (kittenOrigClauses ks)
                      exact hpermW),
                  hkp_nv.trans w_nv, hkp_on.trans w_on, hkp_an.trans w_an,
                  hkp_na.trans w_na, hkp_as.trans w_as, hkp_va.trans w_va,
                  hkp_la.trans w_la, hkp_ca.trans w_ca, ?_⟩
              refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ _) _) ?_) hm
              kstate_ext <;> (first | rfl | kp_field | rw [hw_tn, hother_bv_eq])
            · c0_hsteps_nogrp
              let sz := ksW.clMeta[w0 / 2]?.getD 0#32 &&& 0xFFFF#32
              let off := ksW.clOff[w0 / 2]?.getD 0#32
              refine wp_while_break_state
                (projBrk := fun b : BitVec 32 × BitVec 32 × BitVec 32 =>
                  (b.1, b.2.1, b.2.2, ()))
                (fun b mb => mb = m' ∧
                  (b.2.1 = 0xFFFFFFFF#32 ∨
                    (2 ≤ b.2.1.toNat ∧ b.2.1.toNat < sz.toNat ∧
                      b.2.2 = ksW.arena[off.toNat + b.2.1.toNat]?.getD 0#32 ∧
                      b.2.2 ≠ lit ∧ ksW.vals[b.2.2.toNat]? = some 1#32)))
                (projLp := fun st : BitVec 32 => (st, ()))
                (fun st => sz.toNat - st.toNat)
                (fun st m'' => m'' = m' ∧ st.toNat ≤ sz.toNat ∧ 2 ≤ st.toNat)
                ?_ ?_ ?_
              · rintro B ⟨_, ri, repl⟩ mb ⟨rfl, hbrk⟩
                dsimp only at hbrk ⊢
                c0_hsplit
                · c0_hsteps!
                  exact hfinish_ret false ksW mb hinvW hpermW w_nv w_on w_an w_na w_as w_ca hmW
                · have hri_ne : ri ≠ 0xFFFFFFFF#32 := by bv_omega
                  obtain ⟨hri_ge, hri_lt, hrepl_eq, hrepl_ne, hrepl_val⟩ :=
                    hbrk.resolve_left hri_ne
                  have hri_lt' : ri.toNat < kittenClauseSize ksW (w0 / 2) := hri_lt
                  have hrepl_ne' : repl.toNat ≠ lit.toNat := fun h =>
                    hrepl_ne (BitVec.eq_of_toNat_eq h)
                  obtain ⟨hrl_inv, _, _, _, hrl_perm, ⟨chW', hwc'⟩,
                      hrl_nv, _, hrl_on, _, _, _, _, _, _, hrl_an, hrl_na, hrl_as, hrl_va,
                      hrl_la, _, _, _, _, hrl_ca, _⟩ :=
                    kittenWatchReloc_preserves hshW hinvW hlit_ltW hwc
                      hri_ge hri_lt' hrepl_ne' rfl hrepl_eq
                  have hri_wrap : off.toNat + ri.toNat < 2 ^ 28 := by
                    have := hclW.alen_le
                    have := hclW.acap_lt; unfold dimacsBound at this
                    change kittenClauseOff ksW (w0 / 2) + ri.toNat < 2 ^ 28; omega
                  have hri_cap : off.toNat + ri.toNat < acap := by
                    have := hclW.alen_le; change kittenClauseOff ksW (w0 / 2) + ri.toNat < acap
                    omega
                  have hslot_wrap : off.toNat + (w0 % 2) < 2 ^ 28 := by
                    have := hclW.alen_le
                    have := hclW.acap_lt; unfold dimacsBound at this
                    change kittenClauseOff ksW (w0 / 2) + w0 % 2 < 2 ^ 28; omega
                  have hslot_cap : off.toNat + (w0 % 2) < acap := by
                    have := hclW.alen_le; change kittenClauseOff ksW (w0 / 2) + w0 % 2 < acap
                    omega
                  have hslot_and1 :
                      (BitVec.ofNat 32 w0 &&& (1 : BitVec 32)).toNat = w0 % 2 := hw_mod2
                  have hslot_bv_wrap :
                      (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                        (BitVec.ofNat 32 w0 &&& (1 : BitVec 32)).toNat < 2 ^ 28 := by
                    rw [hw_sh1, hslot_and1]; exact hslot_wrap
                  have hslot_bv_cap :
                      (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                        (BitVec.ofNat 32 w0 &&& (1 : BitVec 32)).toNat < acap := by
                    rw [hw_sh1, hslot_and1]; exact hslot_cap
                  have hri_bv_wrap :
                      (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                        ri.toNat < 2 ^ 28 := by
                    rw [hw_sh1]; exact hri_wrap
                  have hri_bv_cap :
                      (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                        ri.toNat < acap := by
                    rw [hw_sh1]; exact hri_cap
                  have hrepl_256 : repl.toNat < 256 := by
                    rw [hrepl_eq]
                    have har_e : kittenClauseOff ksW (w0 / 2) + ri.toNat < ksW.arena.length := by
                      rw [hshW.arena_len]; exact hri_cap
                    have hm_r : (ksW.arena[kittenClauseOff ksW (w0 / 2) + ri.toNat]'har_e).toNat ∈
                        kittenClauseLits ksW (w0 / 2) := by
                      unfold kittenClauseLits; rw [List.mem_map]
                      refine ⟨_, ?_, rfl⟩
                      rw [List.mem_iff_getElem]
                      exact ⟨ri.toNat, by
                          simp [List.length_take, List.length_drop, hshW.arena_len]
                          have := hclW.alen_le; omega,
                        by simp [List.getElem_take, List.getElem_drop]⟩
                    have := hwf_c.2.2.2.1 _ hm_r
                    change (ksW.arena[kittenClauseOff ksW (w0 / 2) + ri.toNat]?.getD
                      0#32).toNat < 256
                    rw [List.getElem?_eq_getElem har_e, Option.getD_some]
                    unfold kMaxV at hnvW; omega
                  have hrepl_28 : repl.toNat < 2 ^ 28 := by omega
                  have hprv_lt : prev ≠ 0xFFFFFFFF#32 → prev.toNat < 1792 := by
                    intro hp
                    rcases hwc.prev_rel with ⟨_, hpf, _⟩ | ⟨_, u, _, hp_eq, hu_len, _⟩
                    · exact absurd hpf hp
                    · rw [hp_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
                        rw [hshW.wnext_len] at hu_len; omega)]
                      rw [hshW.wnext_len] at hu_len; exact hu_len
                  iterate 5 c0_hstep
                  refine head_wp_store rfl rfl
                    (KittenMemATactics.store_ka_arena_off repl
                      hslot_bv_wrap hslot_bv_cap hmW) ?_
                  intro m_s1 hm_s1
                  iterate 5 c0_hstep
                  refine head_wp_store rfl rfl
                    (KittenMemATactics.store_ka_arena_off lit
                      hri_bv_wrap hri_bv_cap hm_s1) ?_
                  intro m_s2 hm
                  clear hmW hm_s1
                  refine wp_unroll_group fun _ _ => ?_
                  c0_hsplit
                  · have hpeq : prev = 0xFFFFFFFF#32 := by bv_omega
                    c0_hsteps!
                    rw [hw_tn]
                    refine ih (prev, ksW.wnext[w0]?.getD 0#32, done, todo', _, chW') _
                      (by simp) ⟨hwc', hrl_inv, hrl_perm.trans hpermW,
                        hrl_nv.trans w_nv, hrl_on.trans w_on, hrl_an.trans w_an,
                        hrl_na.trans w_na, hrl_as.trans w_as, hrl_va.trans w_va,
                        hrl_la.trans w_la, hrl_ca.trans w_ca, ?_⟩
                    refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ _) _) ?_) hm
                    dsimp only [kittenWatchStep0]; simp only [hpeq, ↓reduceIte]
                    kstate_ext <;> (first | rfl | kp_field |
                      (simp [hw_tn, hw_sh1, hw_mod2, BitVec.ofNat_toNat]; try rfl))
                  · have hpne : prev ≠ 0xFFFFFFFF#32 := by bv_omega
                    have hprv_1792 := hprv_lt hpne
                    have hprv_28 : prev.toNat < 2 ^ 28 := by omega
                    c0_hsteps!
                    rw [hw_tn]
                    refine ih (prev, ksW.wnext[w0]?.getD 0#32, done, todo', _, chW') _
                      (by simp) ⟨hwc', hrl_inv, hrl_perm.trans hpermW,
                        hrl_nv.trans w_nv, hrl_on.trans w_on, hrl_an.trans w_an,
                        hrl_na.trans w_na, hrl_as.trans w_as, hrl_va.trans w_va,
                        hrl_la.trans w_la, hrl_ca.trans w_ca, ?_⟩
                    refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ _) _) ?_) hm
                    dsimp only [kittenWatchStep0]; simp only [hpne, ↓reduceIte]
                    kstate_ext <;> (first | rfl | kp_field |
                      (simp [hw_tn, hw_sh1, hw_mod2, BitVec.ofNat_toNat]; try rfl))
              · intro B L1 r m1 hB ih1 ⟨rfl, hr_le, hr2⟩
                dsimp only at hr_le hr2 ⊢
                c0_hsplit
                · have hsz_def : sz.toNat = kittenClauseSize ksW (w0 / 2) := rfl
                  have hw0_mod : w0 % 2 ^ 32 = w0 := Nat.mod_eq_of_lt (by omega)
                  have hr_lt : r.toNat < sz.toNat := by
                    have hc0 : r.toNat <
                        (ksW.clMeta[w0 % 2 ^ 32 / 2]?.getD 0#32 &&& 65535).toNat := hc
                    rw [hw0_mod] at hc0; exact hc0
                  have har_lt_r : kittenClauseOff ksW (w0 / 2) + r.toNat < ksW.arena.length := by
                    rw [hshW.arena_len]; have := hclW.alen_le; omega
                  have hr_wrap : off.toNat + r.toNat < 2 ^ 28 := by
                    have := hclW.alen_le; have hlt_d := hclW.acap_lt; unfold dimacsBound at hlt_d
                    change kittenClauseOff ksW (w0 / 2) + r.toNat < 2 ^ 28; omega
                  have hr_cap : off.toNat + r.toNat < acap := by
                    have := hclW.alen_le; change kittenClauseOff ksW (w0 / 2) + r.toNat < acap
                    omega
                  have hr_bv_wrap :
                      (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                        r.toNat < 2 ^ 28 := by
                    rw [hw_sh1]; exact hr_wrap
                  have hr_bv_cap :
                      (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                        r.toNat < acap := by
                    rw [hw_sh1]; exact hr_cap
                  have hcand_mem : (ksW.arena[kittenClauseOff ksW (w0 / 2) + r.toNat]'
                      har_lt_r).toNat ∈ kittenClauseLits ksW (w0 / 2) := by
                    unfold kittenClauseLits; rw [List.mem_map]
                    refine ⟨_, ?_, rfl⟩; rw [List.mem_iff_getElem]
                    exact ⟨r.toNat, by
                        simp [List.length_take, List.length_drop, hshW.arena_len];
                        have := hclW.alen_le; omega,
                      by simp [List.getElem_take, List.getElem_drop]⟩
                  have hcand_256 : (ksW.arena[off.toNat + r.toNat]?.getD 0#32).toNat < 256 := by
                    change (ksW.arena[kittenClauseOff ksW (w0 / 2) + r.toNat]?.getD
                      0#32).toNat < 256
                    rw [List.getElem?_eq_getElem har_lt_r, Option.getD_some]
                    have := hwf_c.2.2.2.1 _ hcand_mem; unfold kMaxV at hnvW; omega
                  have hcand_28 : (ksW.arena[off.toNat + r.toNat]?.getD 0#32).toNat < 2 ^ 28 := by
                    omega
                  have hcand_bv_256 :
                      (ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD
                        0#32).toNat + r.toNat]?.getD 0#32).toNat < 256 := by
                    rw [hw_sh1]; exact hcand_256
                  have hcand_bv_28 :
                      (ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD
                        0#32).toNat + r.toNat]?.getD 0#32).toNat < 2 ^ 28 := by
                    omega
                  have hr1_wrap : (r + 1#32).toNat = r.toNat + 1 := by
                    have : sz.toNat < 65536 := by
                      dsimp only [sz]; rw [BitVec.toNat_and]
                      exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
                    bv_omega
                  iterate 5 c0_hstep
                  refine head_wp_load rfl
                    (KittenMemATactics.load_ka_arena_off hr_bv_wrap hr_bv_cap hmW) ?_
                  refine wp_unroll_group fun _ _ => ?_
                  c0_hsplit
                  · have hne_cand : ksW.arena[off.toNat + r.toNat]?.getD 0#32 ≠ lit := by
                      have hc0 : ksW.arena[(ksW.clOff[w0 % 2 ^ 32 / 2]?.getD 0#32).toNat +
                          r.toNat]?.getD 0#32 ≠ lit := hc
                      rw [hw0_mod] at hc0; exact hc0
                    c0_hsplit
                    · have hc_val1 : ksW.vals[(ksW.arena[off.toNat + r.toNat]?.getD
                          0#32).toNat]? = some 1#32 := by
                        have hvl : (ksW.arena[off.toNat + r.toNat]?.getD 0#32).toNat <
                            ksW.vals.length := by rw [hshW.vals_len]; exact hcand_256
                        have hc' : (ksW.vals[(ksW.arena[off.toNat + r.toNat]?.getD
                            0#32).toNat]?.getD 0#32) = 1#32 := by
                          have hc0 : (ksW.vals[(ksW.arena[(ksW.clOff[w0 % 2 ^ 32 / 2]?.getD
                              0#32).toNat + r.toNat]?.getD 0#32).toNat]?.getD 0#32) = 1#32 := hc
                          rwa [hw0_mod] at hc0
                        rw [List.getElem?_eq_getElem hvl] at hc' ⊢
                        simp only [Option.getD_some] at hc'
                        exact congrArg some hc'
                      c0_hsteps!
                      rw [hw_sh1]
                      exact hB (r, r, ksW.arena[off.toNat + r.toNat]?.getD 0#32) _
                        ⟨rfl, Or.inr ⟨hr2, hr_lt, rfl, hne_cand, hc_val1⟩⟩
                    · c0_hsteps!
                      exact ih1 (r + 1#32) _ (by rw [hr1_wrap]; omega)
                        ⟨rfl, by rw [hr1_wrap]; omega, by rw [hr1_wrap]; omega⟩
                  · c0_hsteps!
                    exact ih1 (r + 1#32) _ (by rw [hr1_wrap]; omega)
                      ⟨rfl, by rw [hr1_wrap]; omega, by rw [hr1_wrap]; omega⟩
                · c0_hsteps!
                  exact hB (r, 0xFFFFFFFF#32, 0#32) _ ⟨rfl, Or.inl rfl⟩
              · intro B L1 _ hL1
                c0_hsteps!
                exact hL1 2#32 m' ⟨rfl, hsz_ge, le_refl _⟩
          · have hweq : w = 0xFFFFFFFF#32 := by bv_omega
            obtain ⟨hn_eq, hn_lt⟩ := bv32_xor1_eq_litNeg hlit_lt
            have hnl_ltW : (lit ^^^ 1#32).toNat < 2 * ksW.nv.toNat := by
              rw [show (lit ^^^ 1#32).toNat = (lit ^^^ 1).toNat from rfl, hn_eq, w_nv]
              exact hn_lt
            have hnl_256 : (lit ^^^ 1#32).toNat < 256 := by unfold kMaxV at hnvW; omega
            have hnl_28 : (lit ^^^ 1#32).toNat < 2 ^ 28 := by omega
            have hval1W : ksW.vals[lit.toNat]? = some 1#32 := by rw [w_va]; exact hval1
            have hlvlW : ksW.lvlArr[(lit >>> (1 : Nat)).toNat]?.getD 0#32 ≠ 0#32 := by
              rw [w_la]; exact hlvl_nz
            have hfin := kittenFlipFinish_preserves hinvW hlit_ltW hval1W hlvlW
            c0_hsteps!
            let ksF := (ksW.putArr .vals lit.toNat 2#32).putArr .vals (lit ^^^ 1#32).toNat 1#32
            have hksF_perm : KittenCnfPermEquiv (kittenOrigClauses ksF) (kittenOrigClauses ks) := by
              change KittenCnfPermEquiv (kittenOrigClauses ksW) (kittenOrigClauses ks)
              exact hpermW
            exact hfinish_ret true ksF _ hfin hksF_perm
              (by dsimp only [ksF]; kp_field; exact w_nv)
              (by dsimp only [ksF]; kp_field; exact w_on)
              (by dsimp only [ksF]; kp_field; exact w_an)
              (by dsimp only [ksF]; kp_field; exact w_na)
              (by dsimp only [ksF]; kp_field; exact w_as)
              (by dsimp only [ksF]; kp_field; exact w_ca)
              (by refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ _) _) ?_) hm
                  dsimp only [ksF]; rfl)

end LeanQbe.T.Examples.Kissat.Full