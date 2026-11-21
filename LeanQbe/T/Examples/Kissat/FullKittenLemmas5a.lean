module

public import LeanQbe.T.Examples.Kissat.FullKittenSpec1
public import LeanQbe.T.Examples.Kissat.FullKittenLemmas1

/-!
# Kissat `D-Full` Scratch `kitten` Verification (`Part 5a`: `core`)

Proves the parametric `(Γ : Env)` `Func.wp` contract for:
- `[13] full_kitten_core_wp` (`incons`/`failing` & `clAux` preserved, DAG-closed core UNSAT)

Re-exported alongside `[14] full_kitten_shrink_wp` from `FullKittenLemmas5.lean`.
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

/-! ## 1. Pure Helpers for `full_kitten_core` -/

/-- All core-marked clauses (both original and learned) in `0..bound`. -/
private def coreMarkedClauses (ks : KittenState) (bound : Nat) : List (List Nat) :=
  ((List.range bound).filter fun ci =>
    (kittenClauseMeta ks ci &&& kmCore) != 0#32).map (kittenClauseLits ks)

/-- `st` agrees with `ks0` everywhere except possibly the `KM_CORE` bit of `clMeta`. -/
private structure CoreMetaRel (ks0 st : KittenState) : Prop where
  eq_with : st = { ks0 with clMeta := st.clMeta }
  clMeta_len : st.clMeta.length = 896
  bits_eq : ∀ (i : Nat),
    (st.clMeta[i]?.getD 0#32 &&& 0xFFFF#32) = (ks0.clMeta[i]?.getD 0#32 &&& 0xFFFF#32) ∧
    (st.clMeta[i]?.getD 0#32 &&& kmLrn) = (ks0.clMeta[i]?.getD 0#32 &&& kmLrn)

private theorem CoreMetaRel.refl {acap : Nat} {ks0 : KittenState}
    (hsh : ks0.ShapesOk acap) : CoreMetaRel ks0 ks0 :=
  ⟨by cases ks0; rfl, hsh.clMeta_len, fun _ => ⟨rfl, rfl⟩⟩

private theorem CoreMetaRel.shapes {acap : Nat} {ks0 st : KittenState}
    (hsh : ks0.ShapesOk acap) (h : CoreMetaRel ks0 st) : st.ShapesOk acap := by
  rw [h.eq_with]
  exact ⟨hsh.hdrTail_len, hsh.lvlArr_len, hsh.rsn_len, hsh.qprev_len, hsh.qnext_len,
    hsh.qstampArr_len, hsh.trl_len, hsh.flags_len, hsh.vals_len, hsh.assump_len, hsh.ana_len,
    hsh.kl_len, hsh.units_len, hsh.res_len, hsh.whead_len, hsh.wnext_len, hsh.wblit_len,
    hsh.clOff_len, h.clMeta_len, hsh.clAux_len, hsh.arena_len⟩

private theorem CoreMetaRel.clearCore {ks0 st : KittenState} (h : CoreMetaRel ks0 st)
    (i : Nat) (hi : i < 896) :
    CoreMetaRel ks0 (st.putArr .clMeta i (st.clMeta[i]?.getD 0#32 &&& ~~~kmCore)) := by
  have hlt : i < st.clMeta.length := by rw [h.clMeta_len]; exact hi
  refine ⟨by rw [h.eq_with]; rfl, by simp [KittenState.putArr, h.clMeta_len], fun k => ?_⟩
  simp only [KittenState.putArr]
  by_cases hki : k = i
  · subst hki
    rw [List.getElem?_set_self hlt, Option.getD_some,
      bv32_and_0xffff_and_not_core, bv32_and_lrn_and_not_core]
    exact h.bits_eq k
  · rw [List.getElem?_set_ne (Ne.symm hki)]; exact h.bits_eq k

private theorem CoreMetaRel.setCore {ks0 st : KittenState} (h : CoreMetaRel ks0 st)
    (i : Nat) (hi : i < 896) :
    CoreMetaRel ks0 (st.putArr .clMeta i (st.clMeta[i]?.getD 0#32 ||| kmCore)) := by
  have hlt : i < st.clMeta.length := by rw [h.clMeta_len]; exact hi
  refine ⟨by rw [h.eq_with]; rfl, by simp [KittenState.putArr, h.clMeta_len], fun k => ?_⟩
  simp only [KittenState.putArr]
  by_cases hki : k = i
  · subst hki
    rw [List.getElem?_set_self hlt, Option.getD_some,
      bv32_and_0xffff_or_core, bv32_and_lrn_or_core]
    exact h.bits_eq k
  · rw [List.getElem?_set_ne (Ne.symm hki)]; exact h.bits_eq k

private theorem CoreMetaRel.clause_fields {ks0 st : KittenState} (h : CoreMetaRel ks0 st)
    (cid : Nat) :
    kittenClauseOff st cid = kittenClauseOff ks0 cid ∧
    kittenClauseSize st cid = kittenClauseSize ks0 cid ∧
    kittenClauseIsLrn st cid = kittenClauseIsLrn ks0 cid ∧
    kittenClauseAux st cid = kittenClauseAux ks0 cid ∧
    kittenClauseSpan st cid = kittenClauseSpan ks0 cid ∧
    kittenClauseLits st cid = kittenClauseLits ks0 cid ∧
    kittenClauseAnts st cid = kittenClauseAnts ks0 cid := by
  have hco : st.clOff = ks0.clOff := by rw [h.eq_with]
  have hca : st.clAux = ks0.clAux := by rw [h.eq_with]
  have har : st.arena = ks0.arena := by rw [h.eq_with]
  have hsz : kittenClauseSize st cid = kittenClauseSize ks0 cid := by
    simp only [kittenClauseSize, kittenClauseMeta, (h.bits_eq cid).1]
  have hlr : kittenClauseIsLrn st cid = kittenClauseIsLrn ks0 cid := by
    simp only [kittenClauseIsLrn, kittenClauseMeta, (h.bits_eq cid).2]
  have hoff : kittenClauseOff st cid = kittenClauseOff ks0 cid := by
    simp only [kittenClauseOff, hco]
  have haux : kittenClauseAux st cid = kittenClauseAux ks0 cid := by
    simp only [kittenClauseAux, hca]
  exact ⟨hoff, hsz, hlr, haux,
    by simp only [kittenClauseSpan, hsz, hlr, haux],
    by simp only [kittenClauseLits, hoff, hsz, har],
    by simp only [kittenClauseAnts, hlr, hoff, hsz, haux, har]⟩

private theorem CoreMetaRel.orig_eq {ks0 st : KittenState} (h : CoreMetaRel ks0 st) :
    kittenOrigClauses st = kittenOrigClauses ks0 :=
  kittenOrigClauses_eq_of (by rw [h.eq_with]) fun ci _ => (h.clause_fields ci).2.2.2.2.2.1

private theorem CoreMetaRel.assump_eq {ks0 st : KittenState} (h : CoreMetaRel ks0 st) :
    kittenAssumpLits st = kittenAssumpLits ks0 := by
  unfold kittenAssumpLits; rw [h.eq_with]

private theorem CoreMetaRel.toInv {acap : Nat} {ks0 st : KittenState}
    (hinv : ks0.Inv acap) (h : CoreMetaRel ks0 st)
    (hfail : st.failing ≠ 0xFFFFFFFF#32 →
      (cnfOfClauses (coreMarkedClauses st st.nc.toNat) ++
        unitsCnf (kittenAssumpLits st)).Unsat) :
    st.Inv acap := by
  have hsh := h.shapes hinv.shapes
  have e_nv : st.nv = ks0.nv := by rw [h.eq_with]
  have e_nc : st.nc = ks0.nc := by rw [h.eq_with]
  have e_on : st.orig_nc = ks0.orig_nc := by rw [h.eq_with]
  have e_al : st.alen = ks0.alen := by rw [h.eq_with]
  have e_ac : st.acap = ks0.acap := by rw [h.eq_with]
  have e_na : st.nassump = ks0.nassump := by rw [h.eq_with]
  have e_nu : st.nunits = ks0.nunits := by rw [h.eq_with]
  have e_nr : st.nres = ks0.nres := by rw [h.eq_with]
  have e_nk : st.nkl = ks0.nkl := by rw [h.eq_with]
  have e_nn : st.nana = ks0.nana := by rw [h.eq_with]
  have e_in : st.incons = ks0.incons := by rw [h.eq_with]
  have e_an : st.ante = ks0.ante := by rw [h.eq_with]
  have e_lv : st.lvl = ks0.lvl := by rw [h.eq_with]
  have e_pr : st.prop = ks0.prop := by rw [h.eq_with]
  have e_te : st.trl_end = ks0.trl_end := by rw [h.eq_with]
  have e_un : st.unass = ks0.unass := by rw [h.eq_with]
  have e_va : st.vals = ks0.vals := by rw [h.eq_with]
  have e_la : st.lvlArr = ks0.lvlArr := by rw [h.eq_with]
  have e_rs : st.rsn = ks0.rsn := by rw [h.eq_with]
  have e_tr : st.trl = ks0.trl := by rw [h.eq_with]
  have e_fl : st.flags = ks0.flags := by rw [h.eq_with]
  have e_as : st.assump = ks0.assump := by rw [h.eq_with]
  have e_ui : st.units = ks0.units := by rw [h.eq_with]
  have e_wh : st.whead = ks0.whead := by rw [h.eq_with]
  have e_wn : st.wnext = ks0.wnext := by rw [h.eq_with]
  have e_wb : st.wblit = ks0.wblit := by rw [h.eq_with]
  have e_ar : st.arena = ks0.arena := by rw [h.eq_with]
  have hcl : KittenClausesOk acap st := by
    refine ⟨hinv.clauses.acap_ge, hinv.clauses.acap_lt, by rw [e_ac]; exact hinv.clauses.acap_eq,
      by rw [e_nv]; exact hinv.clauses.nv_le, by rw [e_nc]; exact hinv.clauses.nc_le,
      by rw [e_on, e_nc]; exact hinv.clauses.orig_nc_le,
      by rw [e_on]; exact hinv.clauses.orig_nc_max, by rw [e_al]; exact hinv.clauses.alen_le,
      by rw [e_na]; exact hinv.clauses.nassump_le, by rw [e_nu]; exact hinv.clauses.nunits_le,
      by rw [e_nr]; exact hinv.clauses.nres_le, by rw [e_nk]; exact hinv.clauses.nkl_le,
      by rw [e_nn]; exact hinv.clauses.nana_le, ?_, ?_, ?_, ?_, hfail, ?_, ?_⟩
    · intro cid hcid
      have hw := hinv.clauses.cl_wf cid (e_nc ▸ hcid)
      have hf := h.clause_fields cid
      rw [hf.2.2.1, hf.2.1, hf.1, hf.2.2.2.2.1, hf.2.2.2.2.2.1, hf.2.2.2.2.2.2,
        List.map_congr_left (fun a _ => (h.clause_fields a).2.2.2.2.2.1),
        e_on, e_al, e_nv, e_an, h.orig_eq]
      exact hw
    · intro c1 c2 h12 hc2
      rw [(h.clause_fields c1).1, (h.clause_fields c1).2.2.2.2.1, (h.clause_fields c2).1]
      exact hinv.clauses.cl_mono c1 c2 h12 (e_nc ▸ hc2)
    · intro ui hui
      dsimp only
      rw [e_ui, e_nc, (h.clause_fields _).2.1]
      exact hinv.clauses.units_ok ui (e_nu ▸ hui)
    · intro hi
      have hinc := hinv.clauses.incons_ok (e_in ▸ hi)
      refine ⟨by rw [e_in, e_nc]; exact hinc.1, by rw [h.orig_eq]; exact hinc.2.1, fun l hl => ?_⟩
      rw [e_in, (h.clause_fields _).2.2.2.2.2.1] at hl
      have hr := hinc.2.2 l hl
      dsimp only at hr ⊢
      rw [e_va, e_la, e_rs, e_nc]
      refine ⟨hr.1, hr.2.1, fun ha => ?_⟩
      have hrr := hr.2.2 (e_an ▸ ha)
      rw [(h.clause_fields _).2.2.2.2.2.1]
      exact hrr
    · intro i hi; rw [e_as, e_nv]; exact hinv.clauses.assump_ok i (e_na ▸ hi)
    · intro v hv; rw [e_fl]; exact hinv.clauses.flags_clean v (e_nv ▸ hv)
  have hw : KittenWatchesOk st := by
    obtain ⟨ch, h1, h2, h3, h4⟩ := hinv.watches
    refine ⟨ch, e_nv ▸ h1, h2, fun l hl => by rw [e_wn, e_wh]; exact h3 l (e_nv ▸ hl),
      fun l hl w hw => ?_⟩
    have hb := h4 l (e_nv ▸ hl) w hw
    rw [e_nc, e_nv, e_ar, e_wb, (h.clause_fields _).2.1, (h.clause_fields _).1]; exact hb
  have hba : KittenBaseAssignOk st :=
    ⟨by rw [e_te, e_nv]; exact hinv.assign.trl_end_le,
     by rw [e_pr, e_te]; exact hinv.assign.prop_le,
     by rw [e_un, e_te, e_nv]; exact hinv.assign.unass_eq,
     by rw [e_nv, e_va]; exact hinv.assign.vals_dom,
     by rw [e_nv, e_va]; exact hinv.assign.vals_neg_iff,
     by rw [e_nv, e_va, e_te, e_tr]; exact hinv.assign.vals_nz_iff_trl,
     by unfold kittenTrailLits; rw [e_te, e_tr]; exact hinv.assign.trl_nodup,
     by unfold kittenTrailLits; rw [e_nv, e_te, e_tr]; exact hinv.assign.trl_lt,
     by rw [e_nv, e_la, e_lv]; exact hinv.assign.trl_lvl_le,
     by rw [e_nv, e_va, e_la, e_rs]; exact hinv.assign.unass_lvl_zero,
     by rw [e_te, e_la, e_tr]; exact hinv.assign.trl_lvl_mono,
     by rw [e_te, e_la, e_tr, e_rs]; exact hinv.assign.dec_earliest,
     by intro i hi l hlv
        rw [e_te] at hi
        dsimp only [l] at hlv ⊢
        rw [e_tr, e_la] at hlv
        rw [e_tr, e_rs, e_va, h.orig_eq, e_nc]
        have h0 := hinv.assign.lvl0_ok i hi hlv
        refine ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1, fun ha => ?_⟩
        have hr := h0.2.2.2.2 (e_an ▸ ha)
        dsimp only at hr ⊢
        rw [(h.clause_fields _).2.2.2.2.2.1]; exact hr⟩
  have hrsn : ReasonOk st := by
    intro i hi
    rw [e_te] at hi; dsimp only; rw [e_tr, e_rs, e_nc]
    have hr := hinv.reasons i hi; dsimp only at hr
    simpa only [(h.clause_fields _).2.2.2.2.2.1] using hr
  exact ⟨hsh, hcl, hw, hba, hrsn⟩

private theorem coreMarked_unsat_mono {ks0 st1 st2 : KittenState}
    (h1 : CoreMetaRel ks0 st1) (h2 : CoreMetaRel ks0 st2)
    (hmono : ∀ c < ks0.nc.toNat,
      (kittenClauseMeta st1 c &&& kmCore) ≠ 0#32 → (kittenClauseMeta st2 c &&& kmCore) ≠ 0#32)
    (huns : (cnfOfClauses (coreMarkedClauses st1 ks0.nc.toNat) ++
      unitsCnf (kittenAssumpLits ks0)).Unsat) :
    (cnfOfClauses (coreMarkedClauses st2 ks0.nc.toNat) ++
      unitsCnf (kittenAssumpLits ks0)).Unsat := by
  rw [CNF.unsat_iff_not_sat] at huns ⊢
  intro α hα
  apply huns α
  rw [CNF.sat_append] at hα ⊢
  refine ⟨?_, hα.2⟩
  rw [cnf_sat_cnfOfClauses_iff] at hα ⊢
  intro cl hcl
  unfold coreMarkedClauses at hcl
  rw [List.mem_map] at hcl
  obtain ⟨ci, hci, rfl⟩ := hcl
  rw [List.mem_filter, List.mem_range] at hci
  have hnz1 : (kittenClauseMeta st1 ci &&& kmCore) ≠ 0#32 := by
    simpa [bne_iff_ne] using hci.2
  have hnz2 : (kittenClauseMeta st2 ci &&& kmCore) ≠ 0#32 := hmono ci hci.1 hnz1
  have hlits : kittenClauseLits st1 ci = kittenClauseLits st2 ci :=
    (h1.clause_fields ci).2.2.2.2.2.1.trans (h2.clause_fields ci).2.2.2.2.2.1.symm
  rw [hlits]
  apply hα.1
  unfold coreMarkedClauses
  rw [List.mem_map]
  exact ⟨ci, List.mem_filter.mpr ⟨List.mem_range.mpr hci.1, by simpa [bne_iff_ne] using hnz2⟩, rfl⟩

private theorem coreMarked_setCore_unsat {ks0 st : KittenState}
    (h : CoreMetaRel ks0 st) {idx : Nat} (hi : idx < 896)
    (huns : (cnfOfClauses (coreMarkedClauses st ks0.nc.toNat) ++
      unitsCnf (kittenAssumpLits ks0)).Unsat) :
    let st' := st.putArr .clMeta idx (st.clMeta[idx]?.getD 0#32 ||| kmCore)
    (cnfOfClauses (coreMarkedClauses st' ks0.nc.toNat) ++
      unitsCnf (kittenAssumpLits ks0)).Unsat := by
  intro st'
  have h' := h.setCore idx hi
  refine coreMarked_unsat_mono h h' (fun c _ hc => ?_) huns
  by_cases hci : c = idx
  · subst hci
    have hlt : c < st.clMeta.length := by rw [h.clMeta_len]; exact hi
    change ((st.clMeta.set c (st.clMeta[c]?.getD 0#32 ||| kmCore))[c]?.getD 0#32 &&& kmCore) ≠ 0#32
    rw [List.getElem?_set_self hlt, Option.getD_some]
    exact bv32_and_core_or_core _
  · change ((st.clMeta.set idx _)[c]?.getD 0#32 &&& kmCore) ≠ 0#32
    rw [List.getElem?_set_ne (Ne.symm hci)]
    exact hc

private theorem core_incons_seeded_unsat {acap : Nat} {ks0 st : KittenState}
    (hinv : ks0.Inv acap) (hrel : CoreMetaRel ks0 st)
    (hante : ks0.ante ≠ 0#32) (hinc : ks0.incons ≠ 0xFFFFFFFF#32)
    (hmark_inc : (kittenClauseMeta st ks0.incons.toNat &&& kmCore) ≠ 0#32)
    (hmark_rsn : ∀ j < kittenClauseSize ks0 ks0.incons.toNat,
      let l := (ks0.arena[kittenClauseOff ks0 ks0.incons.toNat + j]?.getD 0#32).toNat
      let r0 := (ks0.rsn[l / 2]?.getD 0#32).toNat
      (kittenClauseMeta st r0 &&& kmCore) ≠ 0#32) :
    (cnfOfClauses (coreMarkedClauses st ks0.nc.toNat) ++
      unitsCnf (kittenAssumpLits ks0)).Unsat := by
  refine cnfOfClauses_unsat_append_left _ ?_
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have hio := hinv.clauses.incons_ok hinc
  have hinc_mem : kittenClauseLits st ks0.incons.toNat ∈ coreMarkedClauses st ks0.nc.toNat := by
    unfold coreMarkedClauses
    rw [List.mem_map]
    exact ⟨ks0.incons.toNat,
      List.mem_filter.mpr ⟨List.mem_range.mpr hio.1, by simpa [bne_iff_ne] using hmark_inc⟩, rfl⟩
  have hsat_inc := (cnf_sat_cnfOfClauses_iff α _).mp hα _ hinc_mem
  rw [(hrel.clause_fields _).2.2.2.2.2.1, clause_sat_cnfClause_iff] at hsat_inc
  obtain ⟨l, hl_mem, hlsat⟩ := hsat_inc
  have hwf := hinv.clauses.cl_wf ks0.incons.toNat hio.1
  have hl_lt : l < 2 * ks0.nv.toNat := hwf.2.2.2.1 l hl_mem
  have hspan : kittenClauseOff ks0 ks0.incons.toNat + kittenClauseSize ks0 ks0.incons.toNat ≤
      ks0.arena.length := by
    rw [hinv.shapes.arena_len]
    have h1 := hwf.2.2.1; unfold kittenClauseSpan at h1
    have h2 := hinv.clauses.alen_le; omega
  have hlen_lits : (kittenClauseLits ks0 ks0.incons.toNat).length =
      kittenClauseSize ks0 ks0.incons.toNat := by
    simp only [kittenClauseLits, List.length_map, List.length_take, List.length_drop]; omega
  obtain ⟨j, hj_len, hj_eq⟩ := List.getElem_of_mem hl_mem
  have hj_lt : j < kittenClauseSize ks0 ks0.incons.toNat := hlen_lits ▸ hj_len
  have hl_eq_ar : (ks0.arena[kittenClauseOff ks0 ks0.incons.toNat + j]?.getD 0#32).toNat = l := by
    rw [← hj_eq]
    simp only [kittenClauseLits, List.getElem_map, List.getElem_take, List.getElem_drop]
    rw [List.getElem?_eq_getElem (by omega : kittenClauseOff ks0 ks0.incons.toNat + j <
      ks0.arena.length), Option.getD_some]
  have hmr := hmark_rsn j hj_lt
  dsimp only at hmr
  rw [hl_eq_ar] at hmr
  have hr_ok := (hio.2.2 l hl_mem).2.2 hante
  dsimp only at hr_ok
  have hrs_len : l / 2 < ks0.rsn.length := by
    rw [hinv.shapes.rsn_len]; have := hinv.clauses.nv_le; unfold kMaxV at this; omega
  have hrs_eq : ks0.rsn[l / 2]?.getD 0#32 = ks0.rsn[l / 2]?.getD 0xFFFFFFFF#32 := by
    rw [List.getElem?_eq_getElem hrs_len, Option.getD_some, Option.getD_some]
  rw [hrs_eq] at hmr
  let r0 := (ks0.rsn[l / 2]?.getD 0xFFFFFFFF#32).toNat
  have hr_mem : kittenClauseLits st r0 ∈ coreMarkedClauses st ks0.nc.toNat := by
    unfold coreMarkedClauses
    rw [List.mem_map]
    exact ⟨r0, List.mem_filter.mpr ⟨List.mem_range.mpr hr_ok.1, by simpa [bne_iff_ne] using hmr⟩,
      rfl⟩
  have hsat_r := (cnf_sat_cnfOfClauses_iff α _).mp hα _ hr_mem
  rw [(hrel.clause_fields r0).2.2.2.2.2.1, hr_ok.2, litNeg_eq_xor1] at hsat_r
  exact (sat_cnfClause_litNeg_iff α l).mp hsat_r ((sat_cnfClause_singleton α l).mpr hlsat)

private theorem core_dag_entails {acap : Nat} {ks0 st : KittenState}
    (hinv : ks0.Inv acap) (hrel : CoreMetaRel ks0 st) (hante : ks0.ante ≠ 0#32)
    (hdag : ∀ c < ks0.nc.toNat, (kittenClauseMeta st c &&& kmCore) ≠ 0#32 →
      ks0.orig_nc.toNat ≤ c →
      ∀ a ∈ kittenClauseAnts ks0 c, (kittenClauseMeta st a &&& kmCore) ≠ 0#32) :
    ∀ c < ks0.nc.toNat, (kittenClauseMeta st c &&& kmCore) ≠ 0#32 →
      (cnfOfClauses (kittenCoreClauses st)).EntailsClause (cnfClause (kittenClauseLits st c)) := by
  intro c
  induction c using Nat.strongRecOn with
  | ind c ih =>
    intro hc hcm
    by_cases horig : c < ks0.orig_nc.toNat
    · apply cnfOfClauses_entailsClause_of_mem
      unfold kittenCoreClauses
      rw [List.mem_map]
      have e_on : st.orig_nc = ks0.orig_nc := by rw [hrel.eq_with]
      exact ⟨c, List.mem_filter.mpr ⟨List.mem_range.mpr (e_on ▸ horig),
        by simpa [bne_iff_ne] using hcm⟩, rfl⟩
    · have hge : ks0.orig_nc.toNat ≤ c := Nat.le_of_not_lt horig
      have hwf := (hinv.clauses.cl_wf c hc).2.2.2.2.2 hante hge
      rw [CNF.entails_clause_def]
      intro α hα
      rw [(hrel.clause_fields c).2.2.2.2.2.1]
      apply CNF.entails_clause_def.mp hwf.2 α
      rw [cnf_sat_cnfOfClauses_iff]
      intro cl hcl
      rw [List.mem_map] at hcl
      obtain ⟨a, ha, rfl⟩ := hcl
      have ha_lt : a < c := hwf.1 a ha
      have ha_mark : (kittenClauseMeta st a &&& kmCore) ≠ 0#32 := hdag c hc hcm hge a ha
      have hent := ih a ha_lt (Nat.lt_trans ha_lt hc) ha_mark
      rw [(hrel.clause_fields a).2.2.2.2.2.1] at hent
      exact CNF.entails_clause_def.mp hent α hα

private theorem core_dag_unsat {acap : Nat} {ks0 st : KittenState}
    (hinv : ks0.Inv acap) (hrel : CoreMetaRel ks0 st) (hante : ks0.ante ≠ 0#32)
    (huns : (cnfOfClauses (coreMarkedClauses st ks0.nc.toNat) ++
      unitsCnf (kittenAssumpLits ks0)).Unsat)
    (hdag : ∀ c < ks0.nc.toNat, (kittenClauseMeta st c &&& kmCore) ≠ 0#32 →
      ks0.orig_nc.toNat ≤ c →
      ∀ a ∈ kittenClauseAnts ks0 c, (kittenClauseMeta st a &&& kmCore) ≠ 0#32) :
    (cnfOfClauses (kittenCoreClauses st) ++ unitsCnf (kittenAssumpLits st)).Unsat := by
  rw [hrel.assump_eq, CNF.unsat_iff_not_sat]
  intro α hα
  rw [CNF.sat_append] at hα
  rw [CNF.unsat_iff_not_sat] at huns
  apply huns α
  rw [CNF.sat_append]
  refine ⟨?_, hα.2⟩
  rw [cnf_sat_cnfOfClauses_iff]
  intro cl hcl
  unfold coreMarkedClauses at hcl
  rw [List.mem_map] at hcl
  obtain ⟨ci, hci, rfl⟩ := hcl
  rw [List.mem_filter, List.mem_range] at hci
  have hcm : (kittenClauseMeta st ci &&& kmCore) ≠ 0#32 := by simpa [bne_iff_ne] using hci.2
  exact CNF.entails_clause_def.mp (core_dag_entails hinv hrel hante hdag ci hci.1 hcm) α hα.1

private theorem mem_kittenCoreClauses_mem_orig (ks : KittenState) :
    ∀ cl ∈ kittenCoreClauses ks, cl ∈ kittenOrigClauses ks := by
  intro cl hcl
  unfold kittenCoreClauses at hcl
  unfold kittenOrigClauses
  rw [List.mem_map] at hcl ⊢
  obtain ⟨ci, hci, rfl⟩ := hcl
  exact ⟨ci, (List.mem_filter.mp hci).1, rfl⟩

/-! ## 2. Parametric `Func.wp` Proof for `full_kitten_core` -/

/-- Parametric `Func.wp` proof for `full_kitten_core`. -/
theorem full_kitten_core_wp (Γ : Env) :
    ∀ args m Q X, fullKittenCoreSpec args m Q X → Func.wp Γ full_kitten_core_body args m Q X := by
  rintro ⟨hPtr, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hinv_s, hante, hor_if, hm, hQ⟩
  rcases hinv_s with ⟨hscr_ge, hscr_lt, hinv⟩
  let scr := s.scratch.scratch_buf
  change kMinScratchCap ≤ scr.length at hscr_ge
  change scr.length < dimacsBound at hscr_lt
  have hscr_len : scr.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hscr_8864 : 8864 ≤ scr.length := by unfold kMinScratchCap at hscr_ge; omega
  let acap := scr.length - 8864
  let ks0 := kittenStateOfScratch scr
  change ks0.Inv acap at hinv
  change ks0.ante ≠ 0#32 at hante
  change ks0.incons ≠ 0xFFFFFFFF#32 ∨ ks0.failing ≠ 0xFFFFFFFF#32 at hor_if
  have hsh0 := hinv.shapes
  have hcl0 := hinv.clauses
  have hnv := hcl0.nv_le
  have hnc := hcl0.nc_le
  have honc := hcl0.orig_nc_le
  have hal := hcl0.alen_le
  have hacap_lt : acap < 2 ^ 28 := hcl0.acap_lt
  have hmF : (FullKittenFrame c s ⋆ KittenMem (c.pScratchBuf + 1024#64) ks0 ⋆ R) m := by
    have hfull := fullMem_eq_kittenFrame (c := c) (s := s) hscr_8864
    rw [hfull] at hm; exact sep_ac hm
  clear hm
  c0_hsteps_nogrp
  let kPtr := c.pScratchBuf + BitVec.ofNat 64 256 * 4
  have hmA : (KittenMemA kPtr acap ks0 ⋆ (FullKittenFrame c s ⋆ R)) m := by
    have hm1 : (KittenMem kPtr ks0 ⋆ (FullKittenFrame c s ⋆ R)) m := by
      dsimp only [kPtr]; rw [kPtr_base_eq]; exact sep_ac hmF
    exact kittenMem_to_amem hsh0 hm1
  clear hmF
  c0_hsteps_nogrp
  refine wp_join_state0 (α := KittenState)
    (fun st m1 => CoreMetaRel ks0 st ∧
      (cnfOfClauses (coreMarkedClauses st ks0.nc.toNat) ++
        unitsCnf (kittenAssumpLits ks0)).Unsat ∧
      (KittenMemA kPtr acap st ⋆ (FullKittenFrame c s ⋆ R)) m1) ?_ ?_
  · intro J1 st1 m1 ⟨hrel1, huns1, hm1⟩
    c0_hsteps_nogrp
    have hnc_eq1 : st1.nc = ks0.nc := by rw [hrel1.eq_with]
    refine wp_while_state1 (fun p : BitVec 32 × KittenState => p.1)
      (fun p => p.1.toNat)
      (fun p m2 => p.1.toNat ≤ ks0.nc.toNat ∧ CoreMetaRel ks0 p.2 ∧
        (cnfOfClauses (coreMarkedClauses p.2 ks0.nc.toNat) ++
          unitsCnf (kittenAssumpLits ks0)).Unsat ∧
        (∀ c, p.1.toNat ≤ c → c < ks0.nc.toNat →
          (kittenClauseMeta p.2 c &&& kmCore) ≠ 0#32 → ks0.orig_nc.toNat ≤ c →
          ∀ a ∈ kittenClauseAnts ks0 c, (kittenClauseMeta p.2 a &&& kmCore) ≠ 0#32) ∧
        (KittenMemA kPtr acap p.2 ⋆ (FullKittenFrame c s ⋆ R)) m2)
      ?_ ?_
    · intro J2 hJ2
      exact wp_jump_state (proj := fun p : BitVec 32 × KittenState => (p.1, ()))
        (ks0.nc, st1) rfl
        (hJ2 _ m1 ⟨Nat.le_refl _, hrel1, huns1, fun c h1 h2 => by dsimp only at h1; omega, hm1⟩)
    · rintro J2 ⟨cid, st2⟩ m2 ⟨hcid_le, hrel2, huns2, hdag2, hm2⟩ ih2
      dsimp only at hcid_le hrel2 huns2 hdag2 hm2
      c0_hsplit
      · have hcid_pos : 0 < cid.toNat := by bv_omega
        let cid' := cid - 1#32
        have hcid'_eq : cid'.toNat = cid.toNat - 1 := by dsimp only [cid']; bv_omega
        have hcid'_lt : cid'.toNat < ks0.nc.toNat := by omega
        have hcid'_896 : cid'.toNat < 896 := by unfold kMaxCl at hnc; omega
        have hcid'_wrap : cid'.toNat < 2 ^ 28 := by omega
        c0_hsteps_nogrp
        let mval := st2.clMeta[cid'.toNat]?.getD 0#32
        have hwf_c := hcl0.cl_wf cid'.toNat hcid'_lt
        refine wp_join_state0 (α := KittenState)
          (fun st3 m3 => CoreMetaRel ks0 st3 ∧
            (cnfOfClauses (coreMarkedClauses st3 ks0.nc.toNat) ++
              unitsCnf (kittenAssumpLits ks0)).Unsat ∧
            (∀ c, cid'.toNat ≤ c → c < ks0.nc.toNat →
              (kittenClauseMeta st3 c &&& kmCore) ≠ 0#32 → ks0.orig_nc.toNat ≤ c →
              ∀ a ∈ kittenClauseAnts ks0 c, (kittenClauseMeta st3 a &&& kmCore) ≠ 0#32) ∧
            (KittenMemA kPtr acap st3 ⋆ (FullKittenFrame c s ⋆ R)) m3) ?_ ?_
        · intro J3 st3 m3 ⟨hrel3, huns3, hdag3, hm3⟩
          c0_hsteps_nogrp
          exact ih2 (cid', st3) m3 (by dsimp only; omega)
            ⟨by dsimp only; omega, hrel3, huns3, hdag3, hm3⟩
        · intro J3 hJ3
          c0_hsplit
          · c0_hsplit
            · have hcore_c : (mval &&& kmCore) ≠ 0#32 := ‹_›
              have hlrn_c : (mval &&& kmLrn) ≠ 0#32 := ‹_›
              have hlrn_true : kittenClauseIsLrn ks0 cid'.toNat = true := by
                have h1 : kittenClauseIsLrn st2 cid'.toNat = true := by
                  unfold kittenClauseIsLrn kittenClauseMeta
                  simpa [bne_iff_ne] using hlrn_c
                rw [(hrel2.clause_fields cid'.toNat).2.2.1] at h1; exact h1
              have hge_orig : ks0.orig_nc.toNat ≤ cid'.toNat := by
                have := hwf_c.1; rw [hlrn_true] at this
                exact of_decide_eq_true this.symm
              c0_hsteps_nogrp
              let off := st2.clOff[cid'.toNat]?.getD 0#32
              let sz := mval &&& 0xFFFF#32
              let na := st2.clAux[cid'.toNat]?.getD 0#32
              have hoff_eq : off.toNat = kittenClauseOff ks0 cid'.toNat := by
                have e_co : st2.clOff = ks0.clOff := by rw [hrel2.eq_with]
                simp only [off, kittenClauseOff, e_co]
              have hsz_eq : sz.toNat = kittenClauseSize ks0 cid'.toNat := by
                have h1 : (mval &&& 0xFFFF#32) = (kittenClauseMeta ks0 cid'.toNat &&& 0xFFFF#32) :=
                  (hrel2.bits_eq cid'.toNat).1
                simp only [sz, kittenClauseSize, h1]
              have hna_eq : na.toNat = kittenClauseAux ks0 cid'.toNat := by
                have e_ca : st2.clAux = ks0.clAux := by rw [hrel2.eq_with]
                simp only [na, kittenClauseAux, e_ca]
              have hspan_le : off.toNat + sz.toNat + na.toNat ≤ acap := by
                have hsp := hwf_c.2.2.1
                unfold kittenClauseSpan at hsp
                simp only [hlrn_true, ite_true] at hsp
                omega
              have hants_ok := hwf_c.2.2.2.2.2 hante hge_orig
              refine wp_while_state1 (fun p : BitVec 32 × KittenState => p.1)
                (fun p => na.toNat - p.1.toNat)
                (fun p m4 => p.1.toNat ≤ na.toNat ∧ CoreMetaRel ks0 p.2 ∧
                  (cnfOfClauses (coreMarkedClauses p.2 ks0.nc.toNat) ++
                    unitsCnf (kittenAssumpLits ks0)).Unsat ∧
                  (∀ c < ks0.nc.toNat, (kittenClauseMeta st2 c &&& kmCore) ≠ 0#32 →
                    (kittenClauseMeta p.2 c &&& kmCore) ≠ 0#32) ∧
                  (∀ c, cid'.toNat ≤ c → p.2.clMeta[c]? = st2.clMeta[c]?) ∧
                  (∀ t < p.1.toNat,
                    (kittenClauseMeta p.2
                      (ks0.arena[off.toNat + sz.toNat + t]?.getD 0#32).toNat &&& kmCore) ≠ 0#32) ∧
                  (KittenMemA kPtr acap p.2 ⋆ (FullKittenFrame c s ⋆ R)) m4)
                ?_ ?_
              · intro J4 hJ4
                exact wp_jump_state (proj := fun p : BitVec 32 × KittenState => (p.1, ()))
                  (0#32, st2) rfl
                  (hJ4 _ m2 ⟨by simp, hrel2, huns2, fun _ _ h => h, fun _ _ => rfl,
                    fun _ h => by simp at h, hm2⟩)
              · rintro J4 ⟨j, st4⟩ m4 ⟨hj_le, hrel4, huns4, hmono4, hhi4, hmarked4, hm4⟩ ih4
                dsimp only at hj_le hrel4 huns4 hmono4 hhi4 hmarked4 hm4
                have hsub_comm :
                    (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + cid.toNat) % 2 ^ 32 = cid'.toNat := by
                  dsimp only [cid']; bv_omega
                c0_hsplit
                · have hj_lt : j.toNat < na.toNat := by
                    dsimp only [na]; rwa [hsub_comm] at hc
                  have hidx_lt : off.toNat + sz.toNat + j.toNat < acap := by omega
                  have hidx_wrap : off.toNat + sz.toNat + j.toNat < 2 ^ 28 := by omega
                  c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
                  refine head_wp_load rfl
                    (KittenMemATactics.load_ka_arena_off2 hidx_wrap hidx_lt hm4) ?_
                  let ant := st4.arena[off.toNat + sz.toNat + j.toNat]?.getD 0#32
                  have hant_eq : ant = ks0.arena[off.toNat + sz.toNat + j.toNat]?.getD 0#32 := by
                    have e_ar : st4.arena = ks0.arena := by rw [hrel4.eq_with]
                    simp only [ant, e_ar]
                  have hant_mem : ant.toNat ∈ kittenClauseAnts ks0 cid'.toNat := by
                    unfold kittenClauseAnts
                    simp only [hlrn_true, ite_true, List.mem_map]
                    have har_lt : off.toNat + sz.toNat + j.toNat < ks0.arena.length := by
                      rw [hsh0.arena_len]; exact hidx_lt
                    refine ⟨ks0.arena[off.toNat + sz.toNat + j.toNat]'har_lt, ?_, ?_⟩
                    · rw [List.mem_iff_getElem]
                      refine ⟨j.toNat, ?_, ?_⟩
                      · simp only [List.length_take, List.length_drop, hsh0.arena_len,
                          ← hoff_eq, ← hsz_eq, ← hna_eq]; omega
                      · simp only [List.getElem_take, List.getElem_drop, ← hoff_eq, ← hsz_eq]
                    · rw [hant_eq, List.getElem?_eq_getElem har_lt, Option.getD_some]
                  have hant_lt_c : ant.toNat < cid'.toNat := hants_ok.1 _ hant_mem
                  have hant_lt_nc : ant.toNat < ks0.nc.toNat := Nat.lt_trans hant_lt_c hcid'_lt
                  have hant_896 : ant.toNat < 896 := by unfold kMaxCl at hnc; omega
                  have hant_wrap : ant.toNat < 2 ^ 28 := by omega
                  have hj1 : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
                  c0_hsteps!
                  · let st4' := st4.putArr .clMeta ant.toNat
                      (st4.clMeta[ant.toNat]?.getD 0#32 ||| kmCore)
                    refine ih4 (j + 1#32, st4') _ (by dsimp only; rw [hj1]; omega)
                      ⟨by dsimp only; rw [hj1]; omega, hrel4.setCore ant.toNat hant_896,
                        coreMarked_setCore_unsat hrel4 hant_896 huns4, ?_, ?_, ?_, hm⟩
                    · intro cl hcl hcm2
                      have hcm4 := hmono4 cl hcl hcm2
                      by_cases hca : cl = ant.toNat
                      · have hlt : ant.toNat < st4.clMeta.length := by
                          rw [hrel4.clMeta_len]; exact hant_896
                        change ((st4.clMeta.set ant.toNat _)[cl]?.getD 0#32 &&& kmCore) ≠ 0#32
                        rw [hca, List.getElem?_set_self hlt, Option.getD_some]
                        exact bv32_and_core_or_core _
                      · change ((st4.clMeta.set ant.toNat _)[cl]?.getD 0#32 &&& kmCore) ≠ 0#32
                        rw [List.getElem?_set_ne (Ne.symm hca)]
                        exact hcm4
                    · intro cl hcl_ge
                      change (st4.clMeta.set ant.toNat _)[cl]? = st2.clMeta[cl]?
                      rw [List.getElem?_set_ne (by omega)]
                      exact hhi4 cl hcl_ge
                    · intro t ht
                      rw [hj1] at ht
                      by_cases htj : t = j.toNat
                      · subst htj
                        have hlt : ant.toNat < st4.clMeta.length := by
                          rw [hrel4.clMeta_len]; exact hant_896
                        rw [← hant_eq]
                        change ((st4.clMeta.set ant.toNat _)[ant.toNat]?.getD 0#32 &&& kmCore) ≠
                          0#32
                        rw [List.getElem?_set_self hlt, Option.getD_some]
                        exact bv32_and_core_or_core _
                      · have hprev := hmarked4 t (by omega)
                        let idx := (ks0.arena[off.toNat + sz.toNat + t]?.getD 0#32).toNat
                        by_cases hia : idx = ant.toNat
                        · have hlt : ant.toNat < st4.clMeta.length := by
                            rw [hrel4.clMeta_len]; exact hant_896
                          change ((st4.clMeta.set ant.toNat _)[idx]?.getD 0#32 &&& kmCore) ≠ 0#32
                          rw [hia, List.getElem?_set_self hlt, Option.getD_some]
                          exact bv32_and_core_or_core _
                        · change ((st4.clMeta.set ant.toNat _)[idx]?.getD 0#32 &&& kmCore) ≠ 0#32
                          rw [List.getElem?_set_ne (Ne.symm hia)]
                          exact hprev
                  · exfalso
                    rw [hsub_comm] at hc
                    exact hc hant_lt_nc
                · have hj_eq : j.toNat = na.toNat := by
                    rw [hsub_comm] at hc; change ¬ j.toNat < na.toNat at hc; omega
                  rw [hj_eq] at hmarked4
                  c0_hsteps!
                  refine hJ3 st4 m4 ⟨hrel4, huns4, ?_, hm4⟩
                  intro c hc_ge hc_lt hcm4 hge_o a ha
                  by_cases hcc : c = cid'.toNat
                  · subst hcc
                    unfold kittenClauseAnts at ha
                    simp only [hlrn_true, ite_true, List.mem_map] at ha
                    obtain ⟨b, hb, rfl⟩ := ha
                    obtain ⟨t, ht_len, ht_eq⟩ := List.getElem_of_mem hb
                    have ht_lt : t < na.toNat := by
                      simp only [List.length_take, List.length_drop, hsh0.arena_len,
                        ← hoff_eq, ← hsz_eq, ← hna_eq] at ht_len; omega
                    have hb_eq : b = ks0.arena[off.toNat + sz.toNat + t]?.getD 0#32 := by
                      rw [← ht_eq]
                      simp only [List.getElem_take, List.getElem_drop, ← hoff_eq, ← hsz_eq]
                      rw [List.getElem?_eq_getElem (by rw [hsh0.arena_len]; omega),
                        Option.getD_some]
                    rw [hb_eq]
                    exact hmarked4 t ht_lt
                  · have hc_gt : cid.toNat ≤ c := by omega
                    have hcm2 : (kittenClauseMeta st2 c &&& kmCore) ≠ 0#32 := by
                      unfold kittenClauseMeta at hcm4 ⊢
                      rwa [hhi4 c hc_ge] at hcm4
                    exact hmono4 a
                      (Nat.lt_trans (((hcl0.cl_wf c hc_lt).2.2.2.2.2 hante hge_o).1 a ha) hc_lt)
                      (hdag2 c hc_gt hc_lt hcm2 hge_o a ha)
            · c0_hsteps!
              have hnlrn : (mval &&& kmLrn) = 0#32 := ‹_›
              refine hJ3 st2 m2 ⟨hrel2, huns2, ?_, hm2⟩
              intro c hc_ge hc_lt hcm hge_o a ha
              by_cases hcc : c = cid'.toNat
              · subst hcc
                exfalso
                have h1 : kittenClauseIsLrn st2 cid'.toNat = false := by
                  unfold kittenClauseIsLrn kittenClauseMeta
                  rw [bne_eq_false_iff_eq]; exact hnlrn
                rw [(hrel2.clause_fields cid'.toNat).2.2.1, hwf_c.1] at h1
                rw [decide_eq_true hge_o] at h1; cases h1
              · exact hdag2 c (by omega) hc_lt hcm hge_o a ha
          · c0_hsteps!
            have hncore : (mval &&& kmCore) = 0#32 := ‹_›
            refine hJ3 st2 m2 ⟨hrel2, huns2, ?_, hm2⟩
            intro c hc_ge hc_lt hcm hge_o a ha
            by_cases hcc : c = cid'.toNat
            · subst hcc; exact absurd hncore hcm
            · exact hdag2 c (by omega) hc_lt hcm hge_o a ha
      · have hcid_zero : cid.toNat = 0 := by bv_omega
        rw [hcid_zero] at hdag2
        c0_hsteps_nogrp
        have honc_eq : st2.orig_nc = ks0.orig_nc := by rw [hrel2.eq_with]
        refine wp_while_state_pure (fun p : BitVec 32 × BitVec 32 => (p.1, (p.2, ())))
          (fun p => ks0.orig_nc.toNat - p.2.toNat)
          (fun p => p.2.toNat ≤ ks0.orig_nc.toNat ∧ p.1.toNat ≤ p.2.toNat)
          ?_ ?_
        · intro J3 hJ3
          exact wp_jump_state (proj := fun p : BitVec 32 × BitVec 32 => (p.1, (p.2, ())))
            (0#32, 0#32) rfl (hJ3 _ ⟨by simp, by simp⟩)
        · rintro J3 ⟨csz, i⟩ ⟨hi_le, hcsz_le⟩ ih3
          dsimp only at hi_le hcsz_le
          c0_hsplit
          · have hi_lt : i.toNat < ks0.orig_nc.toNat := by rw [honc_eq] at *; bv_omega
            have hi_896 : i.toNat < 896 := by
              have := hcl0.orig_nc_max; unfold kMaxOrig at this; omega
            have hi_wrap : i.toNat < 2 ^ 28 := by omega
            have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
            have hcsz1 : (csz + 1#32).toNat = csz.toNat + 1 := by
              have := hcl0.orig_nc_max; unfold kMaxOrig at this; bv_omega
            c0_hsteps!
            · exact ih3 (csz + 1#32, i + 1#32) (by dsimp only; rw [hi1]; omega)
                ⟨by dsimp only; rw [hi1]; omega, by dsimp only; rw [hcsz1, hi1]; omega⟩
            · exact ih3 (csz, i + 1#32) (by dsimp only; rw [hi1]; omega)
                ⟨by dsimp only; rw [hi1]; omega, by dsimp only; rw [hi1]; omega⟩
          · have hi_eq : i.toNat = ks0.orig_nc.toNat := by rw [honc_eq] at *; bv_omega
            c0_hsteps!
            have hdag_full : ∀ c < ks0.nc.toNat, (kittenClauseMeta st2 c &&& kmCore) ≠ 0#32 →
                ks0.orig_nc.toNat ≤ c →
                ∀ a ∈ kittenClauseAnts ks0 c, (kittenClauseMeta st2 a &&& kmCore) ≠ 0#32 :=
              fun c hc => hdag2 c (Nat.zero_le c) hc
            have hsh2 := hrel2.shapes hsh0
            have hinv2 := hrel2.toInv hinv (fun _ => by
              rw [show st2.nc = ks0.nc by rw [hrel2.eq_with], hrel2.assump_eq]; exact huns2)
            have hcore_unsat := core_dag_unsat hinv hrel2 hante huns2 hdag_full
            obtain ⟨_, hm2'⟩ := kittenMemA_to_mem hm2
            have hm2'_exp :
                (FullKittenFrame c s ⋆ KittenMem (c.pScratchBuf + 1024#64) st2 ⋆ R) m2 := by
              dsimp only [kPtr] at hm2'; rw [kPtr_base_eq] at hm2'; exact sep_ac hm2'
            have hmJ := fullMem_join_kitten (c := c) (s := s) (acap := acap) (ks' := st2)
              (R := R) (by change 256 ≤ scr.length; omega) hsh2 hm2'_exp
            let scr' := s.scratch.scratch_buf.take 256 ++ st2.toSlab
            have hscr_s_eq : s.scratch.scratch_buf = scr := rfl
            have hscr'_len : scr'.length = c.scratch_cap := by
              simp only [scr', hscr_s_eq, List.length_append,
                List.length_take_of_le (by omega : 256 ≤ scr.length),
                KittenState.toSlab_length hsh2]
              dsimp only [acap]; omega
            have hpre : ∀ x < kBase, scr'[x]? = s.scratch.scratch_buf[x]? := by
              intro x hx
              have htk : x < (s.scratch.scratch_buf.take 256).length := by
                rw [hscr_s_eq, List.length_take_of_le (by omega : 256 ≤ scr.length)]
                unfold kBase at hx; omega
              rw [List.getElem?_append_left htk, List.getElem?_take_of_lt
                (by unfold kBase at hx; omega)]
            have hof : kittenStateOfScratch scr' = st2 := by
              unfold kittenStateOfScratch
              rw [slab_drop_exact _ st2.toSlab (by
                rw [hscr_s_eq, List.length_take_of_le (by omega : 256 ≤ scr.length)])]
              exact KittenState.ofSlab_toSlab hsh2
            have hks_inv : KittenScratchInv scr' := by
              refine ⟨by omega, by rw [hscr'_len]; exact c.hscr, ?_⟩
              rw [hof, show scr'.length - 8864 = acap by dsimp only [acap]; omega]
              exact hinv2
            exact hQ csz scr' m2 (fullState_lengthsOk_scratch hlen hscr'_len) hpre hks_inv
              (by rw [hof, honc_eq]; omega)
              (by rw [hof, hrel2.eq_with]) (by rw [hof, honc_eq])
              (by rw [hof, hrel2.eq_with]) (by rw [hof, hrel2.eq_with])
              (by rw [hof, hrel2.eq_with]) (by rw [hof, hrel2.eq_with])
              (by unfold kittenOrigClausesS; rw [hof]; exact hrel2.orig_eq)
              (by unfold kittenAssumpLitsS; rw [hof]; exact hrel2.assump_eq)
              (by intro ci _; rw [hof, hrel2.eq_with])
              (by unfold kittenCoreClausesS kittenOrigClausesS; rw [hof]
                  exact mem_kittenCoreClauses_mem_orig st2)
              (by unfold kittenCoreClausesS kittenAssumpLitsS; rw [hof]; exact hcore_unsat)
              hmJ
  · intro J1 hJ1
    c0_hsplit
    · have hfail_nil : ks0.failing = 0xFFFFFFFF#32 := ‹_›
      have hinc_ne : ks0.incons ≠ 0xFFFFFFFF#32 :=
        hor_if.resolve_right (fun h => h hfail_nil)
      c0_hsteps_nogrp
      refine wp_while_state1 (fun p : BitVec 32 × KittenState => p.1)
        (fun p => ks0.nc.toNat - p.1.toNat)
        (fun p m1 => p.1.toNat ≤ ks0.nc.toNat ∧ CoreMetaRel ks0 p.2 ∧
          (KittenMemA kPtr acap p.2 ⋆ (FullKittenFrame c s ⋆ R)) m1)
        ?_ ?_
      · intro J2 hJ2
        exact wp_jump_state (proj := fun p : BitVec 32 × KittenState => (p.1, ()))
          (0#32, ks0) rfl (hJ2 _ m ⟨by simp, CoreMetaRel.refl hsh0, hmA⟩)
      · rintro J2 ⟨i, st⟩ m1 ⟨hi_le, hrel, hm1⟩ ih
        dsimp only at hi_le hrel hm1
        c0_hsplit
        · have hi_lt : i.toNat < ks0.nc.toNat := by bv_omega
          have hi_896 : i.toNat < 896 := by unfold kMaxCl at hnc; omega
          have hi_wrap : i.toNat < 2 ^ 28 := by omega
          have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
          c0_hsteps!
          exact ih (i + 1#32, _) _ (by dsimp only; rw [hi1]; omega)
            ⟨by dsimp only; rw [hi1]; omega, hrel.clearCore i.toNat hi_896, hm⟩
        · c0_hsteps_nogrp
          have hinc_eq : st.incons = ks0.incons := by rw [hrel.eq_with]
          refine wp_join0 (fun m' => J1 () m') (fun _ m' h => h) fun _ hJs => ?_
          c0_hsplit
          · have hio := hcl0.incons_ok hinc_ne
            have hinc_896 : ks0.incons.toNat < 896 := by
              have := hio.1; unfold kMaxCl at hnc; omega
            have hinc_wrap : ks0.incons.toNat < 2 ^ 28 := by omega
            have hinc_st_896 : st.incons.toNat < 896 := by rw [hinc_eq]; exact hinc_896
            have hinc_st_wrap : st.incons.toNat < 2 ^ 28 := by rw [hinc_eq]; exact hinc_wrap
            c0_hsteps_nogrp
            let stI := st.putArr .clMeta st.incons.toNat
              (st.clMeta[st.incons.toNat]?.getD 0#32 ||| kmCore)
            have hrelI : CoreMetaRel ks0 stI := hrel.setCore st.incons.toNat hinc_st_896
            have hmarkI : (kittenClauseMeta stI ks0.incons.toNat &&& kmCore) ≠ 0#32 := by
              have hlt : st.incons.toNat < st.clMeta.length := by
                rw [hrel.clMeta_len]; exact hinc_st_896
              change ((st.clMeta.set st.incons.toNat _)[ks0.incons.toNat]?.getD 0#32 &&&
                kmCore) ≠ 0#32
              rw [← hinc_eq, List.getElem?_set_self hlt, Option.getD_some]
              exact bv32_and_core_or_core _
            let off := stI.clOff[st.incons.toNat]?.getD 0#32
            let sz := stI.clMeta[st.incons.toNat]?.getD 0#32 &&& 0xFFFF#32
            have hoff_eq : off.toNat = kittenClauseOff ks0 ks0.incons.toNat := by
              have e_co : stI.clOff = ks0.clOff := by rw [hrelI.eq_with]
              simp only [off, kittenClauseOff, e_co, hinc_eq]
            have hsz_eq : sz.toNat = kittenClauseSize ks0 ks0.incons.toNat := by
              have h1 := (hrelI.bits_eq ks0.incons.toNat).1
              simp only [sz, kittenClauseSize, kittenClauseMeta, hinc_eq, h1]
            have hwf_inc := hcl0.cl_wf ks0.incons.toNat hio.1
            have hspan_inc : off.toNat + sz.toNat ≤ acap := by
              have h1 := hwf_inc.2.2.1; unfold kittenClauseSpan at h1; omega
            refine wp_while_state1 (fun p : BitVec 32 × KittenState => p.1)
              (fun p => sz.toNat - p.1.toNat)
              (fun p m2 => p.1.toNat ≤ sz.toNat ∧ CoreMetaRel ks0 p.2 ∧
                (kittenClauseMeta p.2 ks0.incons.toNat &&& kmCore) ≠ 0#32 ∧
                (∀ t < p.1.toNat,
                  let l := (ks0.arena[off.toNat + t]?.getD 0#32).toNat
                  let r0 := (ks0.rsn[l / 2]?.getD 0#32).toNat
                  (kittenClauseMeta p.2 r0 &&& kmCore) ≠ 0#32) ∧
                (KittenMemA kPtr acap p.2 ⋆ (FullKittenFrame c s ⋆ R)) m2)
              ?_ ?_
            · intro J3 hJ3
              exact wp_jump_state (proj := fun p : BitVec 32 × KittenState => (p.1, ()))
                (0#32, stI) rfl
                (hJ3 _ _ ⟨by simp, hrelI, hmarkI, fun _ h => by simp at h, hm⟩)
            · rintro J3 ⟨j, stJ⟩ m2 ⟨hj_le, hrelJ, hmarkJ, hrsnJ, hm2⟩ ihJ
              dsimp only at hj_le hrelJ hmarkJ hrsnJ hm2
              c0_hsplit
              · have hj_lt : j.toNat < sz.toNat := by
                  change j.toNat < sz.toNat at hc; exact hc
                have hidx_lt : off.toNat + j.toNat < acap := by omega
                have hidx_wrap : off.toNat + j.toNat < 2 ^ 28 := by omega
                let lit := stJ.arena[off.toNat + j.toNat]?.getD 0#32
                have hlit_eq : lit = ks0.arena[off.toNat + j.toNat]?.getD 0#32 := by
                  have e_ar : stJ.arena = ks0.arena := by rw [hrelJ.eq_with]
                  simp only [lit, e_ar]
                have hlit_mem : lit.toNat ∈ kittenClauseLits ks0 ks0.incons.toNat := by
                  unfold kittenClauseLits
                  rw [List.mem_map]
                  have har_lt : off.toNat + j.toNat < ks0.arena.length := by
                    rw [hsh0.arena_len]; exact hidx_lt
                  refine ⟨ks0.arena[off.toNat + j.toNat]'har_lt, ?_, ?_⟩
                  · rw [List.mem_iff_getElem]
                    exact ⟨j.toNat,
                      by simp only [List.length_take, List.length_drop, hsh0.arena_len,
                           ← hoff_eq, ← hsz_eq]; omega,
                      by simp only [List.getElem_take, List.getElem_drop, ← hoff_eq]⟩
                  · rw [hlit_eq, List.getElem?_eq_getElem har_lt, Option.getD_some]
                have hlit_lt : lit.toNat < 2 * ks0.nv.toNat := hwf_inc.2.2.2.1 _ hlit_mem
                obtain ⟨hv_eq, hv_lt⟩ := bv32_lit_div2_bv hlit_lt
                have hv_128 : (lit >>> (1 : Nat)).toNat < 128 := by unfold kMaxV at hnv; omega
                have hv_wrap : (lit >>> (1 : Nat)).toNat < 2 ^ 28 := by omega
                c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
                refine head_wp_load rfl
                  (KittenMemATactics.load_ka_arena_off hidx_wrap hidx_lt hm2) ?_
                c0_hsteps_nogrp
                let r0 := stJ.rsn[(lit >>> (1 : Nat)).toNat]?.getD 0#32
                have hr0_eq : r0 = ks0.rsn[lit.toNat / 2]?.getD 0#32 := by
                  have e_rs : stJ.rsn = ks0.rsn := by rw [hrelJ.eq_with]
                  simp only [r0, hv_eq, e_rs]
                have hr0_ok := (hio.2.2 lit.toNat hlit_mem).2.2 hante
                dsimp only at hr0_ok
                have hrs_len : lit.toNat / 2 < ks0.rsn.length := by
                  rw [hsh0.rsn_len]; unfold kMaxV at hnv; omega
                have hr0_toNat : r0.toNat < ks0.nc.toNat := by
                  rw [hr0_eq, List.getElem?_eq_getElem hrs_len, Option.getD_some]
                  have h1 := hr0_ok.1
                  rwa [List.getElem?_eq_getElem hrs_len, Option.getD_some] at h1
                have hr0_896 : r0.toNat < 896 := by unfold kMaxCl at hnc; omega
                have hr0_wrap : r0.toNat < 2 ^ 28 := by omega
                have hj1 : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
                c0_hsteps!
                · let stJ' := stJ.putArr .clMeta r0.toNat
                    (stJ.clMeta[r0.toNat]?.getD 0#32 ||| kmCore)
                  refine ihJ (j + 1#32, stJ') _ (by dsimp only; rw [hj1]; omega)
                    ⟨by dsimp only; rw [hj1]; omega, hrelJ.setCore r0.toNat hr0_896, ?_, ?_, hm⟩
                  · by_cases hi_r : ks0.incons.toNat = r0.toNat
                    · have hlt : r0.toNat < stJ.clMeta.length := by
                        rw [hrelJ.clMeta_len]; exact hr0_896
                      change ((stJ.clMeta.set r0.toNat _)[ks0.incons.toNat]?.getD 0#32 &&&
                        kmCore) ≠ 0#32
                      rw [hi_r, List.getElem?_set_self hlt, Option.getD_some]
                      exact bv32_and_core_or_core _
                    · change ((stJ.clMeta.set r0.toNat _)[ks0.incons.toNat]?.getD 0#32 &&&
                        kmCore) ≠ 0#32
                      rw [List.getElem?_set_ne (Ne.symm hi_r)]
                      exact hmarkJ
                  · intro t ht
                    rw [hj1] at ht
                    by_cases htj : t = j.toNat
                    · subst htj
                      dsimp only
                      rw [← hlit_eq, ← hr0_eq]
                      have hlt : r0.toNat < stJ.clMeta.length := by
                        rw [hrelJ.clMeta_len]; exact hr0_896
                      change ((stJ.clMeta.set r0.toNat _)[r0.toNat]?.getD 0#32 &&& kmCore) ≠ 0#32
                      rw [List.getElem?_set_self hlt, Option.getD_some]
                      exact bv32_and_core_or_core _
                    · have hprev := hrsnJ t (by omega)
                      dsimp only at hprev ⊢
                      let idx := (ks0.rsn[(ks0.arena[off.toNat + t]?.getD 0#32).toNat / 2]?.getD
                        0#32).toNat
                      by_cases hir : idx = r0.toNat
                      · have hlt : r0.toNat < stJ.clMeta.length := by
                          rw [hrelJ.clMeta_len]; exact hr0_896
                        change ((stJ.clMeta.set r0.toNat _)[idx]?.getD 0#32 &&& kmCore) ≠ 0#32
                        rw [hir, List.getElem?_set_self hlt, Option.getD_some]
                        exact bv32_and_core_or_core _
                      · change ((stJ.clMeta.set r0.toNat _)[idx]?.getD 0#32 &&& kmCore) ≠ 0#32
                        rw [List.getElem?_set_ne (Ne.symm hir)]
                        exact hprev
                · exfalso
                  have hff : r0 = 0xFFFFFFFF#32 := by
                    dsimp only [r0]; rw [hv_eq]; exact hc
                  have : r0.toNat = 2 ^ 32 - 1 := by rw [hff]; decide
                  omega
              · have hj_eq : j.toNat = sz.toNat := by
                  change ¬ j.toNat < sz.toNat at hc; omega
                rw [hj_eq] at hrsnJ
                c0_hsteps!
                refine hJs m2 (hJ1 stJ m2 ⟨hrelJ, ?_, hm2⟩)
                refine core_incons_seeded_unsat hinv hrelJ hante hinc_ne hmarkJ fun t ht => ?_
                rw [← hoff_eq]
                exact hrsnJ t (hsz_eq ▸ ht)
          · exfalso; exact hinc_ne (hinc_eq ▸ ‹_›)
    · c0_hsteps!
      have hfail_ne : ks0.failing ≠ 0xFFFFFFFF#32 := ‹_›
      refine hJ1 ks0 m ⟨CoreMetaRel.refl hsh0, hcl0.failing_ok hfail_ne, hmA⟩

end LeanQbe.T.Examples.Kissat.Full
