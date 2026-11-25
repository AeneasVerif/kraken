/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelitySweep
public import LeanQbe.T.Examples.Kissat.FullM8SweepV2ConeProof
import LeanQbe.T.Examples.Kissat.FullM6SweepProofConeLemmas

/-!
# Kissat Full-Fidelity Sweep — Generalized Dynamic-Cone Invariants & Lemmas (`Cone0`)

Generalizes `FullM8SweepV2ConeProof` invariants (`FidConeInv`, `FidConeBase`, `FidConeSavedBase`,
`FidConeScanBase`) and pure/rollback/push/add-clause/exit lemmas over dynamic `GAP-SWP-01` limits
(`mvC ∈ [256, L.maxV]`, `mc_c ≤ L.maxOrig`, `depth_lim ∈ [2, 3]`) driven by `h->glue_used[28]`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelitySweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6Sweep LeanQbe.T.Examples.Kissat.FullM8SweepV2
open Kraken.Bedrock2.Test
open FullArenaTactics
open scoped FullArenaTactics M6SweepTactics

/-! ## 1. Dynamic Escalation Limit Arithmetic (`GAP-SWP-01`) -/

theorem fid_comp_vlim_clim {comp : BitVec 32} (hc : comp.toNat ≤ 5) :
    256 ≤ (256#32 <<< comp).toNat ∧ (256#32 <<< comp).toNat ≤ 8192 ∧
    1024 ≤ (1024#32 <<< comp).toNat ∧ (1024#32 <<< comp).toNat ≤ 32768 := by
  have hcases : comp = 0#32 ∨ comp = 1#32 ∨ comp = 2#32 ∨
      comp = 3#32 ∨ comp = 4#32 ∨ comp = 5#32 := by bv_omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem fid_gu28_lt {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c) :
    (BitVec.setWidth 64 (28 : BitVec 32)).toNat < s.scratch.glue_used.length := by
  rw [hlen.scratch_ok.glue_used_len]; decide

theorem fid_gu28_lt64 {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c) :
    (28 : BitVec 64).toNat < s.scratch.glue_used.length := by
  rw [hlen.scratch_ok.glue_used_len]; decide

theorem fid_coneLift_eq_of_getElem {ws1 ws2 : List (BitVec 32)} {l : Nat}
    (h : ws1[l / 2]? = ws2[l / 2]?) : m6ConeLift ws1 l = m6ConeLift ws2 l := by
  have hiff : ∀ α : Nat → Bool,
      (cnfClause [m6ConeLift ws1 l]).Sat α ↔ (cnfClause [m6ConeLift ws2 l]).Sat α := by
    intro α
    rw [← coneLift_sat_iff, ← coneLift_sat_iff]
    simp only [sat_cnfClause_singleton, litVar, h]
  have hsgn : litSign (m6ConeLift ws1 l) = litSign (m6ConeLift ws2 l) := by
    have h1 := hiff (fun _ => true)
    simp only [sat_cnfClause_singleton] at h1
    cases h1s : litSign (m6ConeLift ws1 l) <;> cases h2s : litSign (m6ConeLift ws2 l) <;>
      simp_all
  have hp : m6ConeLift ws1 l % 2 = m6ConeLift ws2 l % 2 := by
    unfold litSign at hsgn
    rcases Nat.mod_two_eq_zero_or_one (m6ConeLift ws1 l) with h1 | h1 <;>
      rcases Nat.mod_two_eq_zero_or_one (m6ConeLift ws2 l) with h2 | h2 <;>
      simp [h1, h2] at hsgn ⊢
  have hv : m6ConeLift ws1 l / 2 = m6ConeLift ws2 l / 2 := by
    let β : Nat → Bool := fun k =>
      xor (decide (k = m6ConeLift ws1 l / 2)) (litSign (m6ConeLift ws1 l))
    have h1 : (cnfClause [m6ConeLift ws1 l]).Sat β := by
      simp only [sat_cnfClause_singleton, litVar, β, decide_true]
      cases litSign (m6ConeLift ws1 l) <;> decide
    have h2 := (hiff β).mp h1
    simp only [sat_cnfClause_singleton, litVar, β, ← hsgn] at h2
    have hd : decide (m6ConeLift ws2 l / 2 = m6ConeLift ws1 l / 2) = true := by
      cases litSign (m6ConeLift ws1 l) <;>
        cases hcmp : decide (m6ConeLift ws2 l / 2 = m6ConeLift ws1 l / 2) <;>
        simp_all
    exact (decide_eq_true_eq.mp hd).symm
  omega


def fidConeMask (t : FullState) : FullState :=
  { core := { t.core with tmp := [] }
    scratch := { t.scratch with work_stk1 := [], tarjan_mark := [], scratch_buf := [] } }

theorem fidConeMask_core_eq {s st : FullState} (h : AgreesExcept fidConeMask s st) :
    st.core = { s.core with tmp := st.core.tmp } := by
  have hc : ({ st.core with tmp := [] } : FullCoreState) = { s.core with tmp := [] } :=
    congrArg FullState.core h
  cases h1 : st.core; cases h2 : s.core
  rw [h1, h2] at hc; cases hc; rfl

theorem fidConeMask_state_eq {s st : FullState} (h : AgreesExcept fidConeMask s st) :
    st = { s with
      core := { s.core with tmp := st.core.tmp }
      scratch := { s.scratch with
        work_stk1 := st.scratch.work_stk1
        tarjan_mark := st.scratch.tarjan_mark
        scratch_buf := st.scratch.scratch_buf } } := by
  have hc := fidConeMask_core_eq h
  have hs : (fidConeMask st).scratch = (fidConeMask s).scratch := congrArg FullState.scratch h
  cases st with | mk c1 sc1 => cases s with | mk c2 sc2 =>
  dsimp only [fidConeMask] at hc hs ⊢
  cases sc1; cases sc2; cases hs; rw [hc]

theorem fidConeMask_preserves_dense {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} (hag : AgreesExcept fidConeMask s st)
    (hlen : st.LengthsOk c) (hdw : FullDenseInvW c F0 F_cur s) :
    FullDenseInvW c F0 F_cur st := by
  have hc0 := fidConeMask_core_eq hag
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

theorem fidConeMask_upd_tmp {s st : FullState} (tmp' : List (BitVec 32))
    (h : AgreesExcept fidConeMask s st) :
    AgreesExcept fidConeMask s { st with core := { st.core with tmp := tmp' } } :=
  h.update (fun x => { x with core := { x.core with tmp := tmp' } }) fun _ => rfl

theorem fidConeMask_upd_tmk {s st : FullState} (tmk' : List (BitVec 32))
    (h : AgreesExcept fidConeMask s st) :
    AgreesExcept fidConeMask s { st with scratch := { st.scratch with tarjan_mark := tmk' } } :=
  h.update (fun x => { x with scratch := { x.scratch with tarjan_mark := tmk' } }) fun _ => rfl

theorem fidConeMask_upd_tmk_ws1 {s st : FullState} (tmk' ws1' : List (BitVec 32))
    (h : AgreesExcept fidConeMask s st) :
    AgreesExcept fidConeMask s
      { st with scratch := { st.scratch with tarjan_mark := tmk', work_stk1 := ws1' } } :=
  h.update
    (fun x => { x with scratch := { x.scratch with tarjan_mark := tmk', work_stk1 := ws1' } })
    fun _ => rfl
theorem fid_k6ShrinkNv_preserves_inv {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks : K6State} {mvC nv : BitVec 32}
    (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks)
    (hnv1 : 1 ≤ nv.toNat) (hnv_le_mvC : nv.toNat ≤ mvC.toNat)
    (hmvC_leMax : mvC.toNat ≤ L.maxV) (hks_nv : ks.nv = mvC)
    (_hlvl0 : ks.lvl = 0#32) (hna0 : ks.nassump = 0#32)
    (hbdd : K6LitsBounded nv.toNat ks)
    (htrl_bdd : ∀ l ∈ k6TrailLits ks, l < 2 * nv.toNat) :
    let ks' := ((((((ks.putHdr .nv nv).putHdr .unass (nv - ks.trl_end)).putHdr .qlast
      (nv - 1#32)).putHdr .qsearch (nv - 1#32)).putHdr .qstamp nv)).putArr .qnext
      (nv.toNat - 1) 0xFFFFFFFF#32
    K6Inv L P ks' ∧ K6TrailSynced ks' ∧ ks'.nv = nv := by
  intro ks'
  have hte_le : ks.trl_end.toNat ≤ nv.toNat := m6_trl_end_le_of_bdd hinv htrl_bdd
  have hm := L.hmaxV
  have hnv_max : nv.toNat ≤ L.maxV := by omega
  have hnv_le_old : nv.toNat ≤ ks.nv.toNat := hks_nv ▸ hnv_le_mvC
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
structure FidConeInv (F_cur : List (List Nat)) (L : K6Layout)
    (mvC : BitVec 32) (st : FullState) (nv nc : Nat) : Prop where
  nv_ge1 : 1 ≤ nv
  nv_le_mvC : nv ≤ mvC.toNat
  mvC_leMax : mvC.toNat ≤ L.maxV
  nv_le_cv : nv ≤ st.core.cur_vars
  nc_le : nc ≤ L.maxOrig
  scr_len : st.scratch.scratch_buf.length = L.scrLen
  k6_inv : K6Inv L (ConeModelSet F_cur st.scratch.work_stk1 nv)
    (k6StateOfScratch L st.scratch.scratch_buf)
  k6_sync : K6TrailSynced (k6StateOfScratch L st.scratch.scratch_buf)
  k6_nv : (k6StateOfScratch L st.scratch.scratch_buf).nv = mvC
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


theorem FidConeInv.nv_leMax {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {st : FullState} {nv nc : Nat} (h : FidConeInv F_cur L mvC st nv nc) : nv ≤ L.maxV :=
  Nat.le_trans h.nv_le_mvC h.mvC_leMax

theorem fidConeInv_tmp_irrel {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {st : FullState} {nv nc : Nat} {tmp' : List (BitVec 32)} (h : FidConeInv F_cur L mvC st nv nc) :
    FidConeInv F_cur L mvC { st with core := { st.core with tmp := tmp' } } nv nc :=
  ⟨h.nv_ge1, h.nv_le_mvC, h.mvC_leMax, h.nv_le_cv, h.nc_le, h.scr_len, h.k6_inv, h.k6_sync,
   h.k6_nv, h.k6_lvl, h.k6_na, h.k6_bdd, h.k6_trl_bdd, h.fwd, h.rev⟩

theorem fidConeInv_init {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout} {s : FullState}
    {scr0 : List (BitVec 32)} {mvC root_v : BitVec 32}
    (hlen : s.LengthsOk c) (hL_len : L.scrLen = c.scratch_cap)
    (hmvC_ge1 : 1 ≤ mvC.toNat) (hmvC_leMax : mvC.toNat ≤ L.maxV)
    (hroot : root_v.toNat < s.core.cur_vars) (htmk : M6TmkZero s)
    (hscr0 : scr0.length = c.scratch_cap)
    (hK : ∀ P, K6Inv L P (k6StateOfScratch L scr0))
    (hsy : K6TrailSynced (k6StateOfScratch L scr0))
    (hnv : (k6StateOfScratch L scr0).nv = mvC)
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
    s1.LengthsOk c ∧ AgreesExcept fidConeMask s s1 ∧ FidConeInv F_cur L mvC s1 1 0 := by
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
      nv_le_mvC := hmvC_ge1
      mvC_leMax := hmvC_leMax
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

theorem fidConeInv_push_var {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {mvC : BitVec 32} {s : FullState} {nv nc : Nat} {ov : BitVec 32}
    (hlen : s.LengthsOk c) (hc : FidConeInv F_cur L mvC s nv nc)
    (hnv_max : nv < mvC.toNat) (hov : ov.toNat < s.core.cur_vars)
    (hmiss : s.scratch.tarjan_mark[ov.toNat]?.getD 0#32 = 0#32) :
    nv < s.core.cur_vars ∧
    let s' : FullState :=
      { s with scratch :=
        { s.scratch with
          tarjan_mark := s.scratch.tarjan_mark.set ov.toNat (BitVec.ofNat 32 (nv + 1))
          work_stk1 := s.scratch.work_stk1.set nv ov } }
    FidConeInv F_cur L mvC s' (nv + 1) nc := by
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
      nv_le_mvC := by omega
      mvC_leMax := hc.mvC_leMax
      nv_le_cv := by dsimp [s']; omega
      nc_le := hc.nc_le
      scr_len := hc.scr_len
      k6_inv := hc.k6_inv.mono_P (fun β hβ => FullM6Sweep.coneModelSet_push_var β hβ)
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

theorem fid_cone_call_add_clause {Γ : Env}
    (hAddCl : M6EnvSpec Γ "full_k6_add_clause" k6AddClauseSpec)
    {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {s0 st : FullState} {nv nc sz : BitVec 32} {aSz : Arg Val i32}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    {k : Tup Val [.bool] → Expr Val Cont [i64]}
    (haSz : aSz.val = sz) (hL_len : L.scrLen = c.scratch_cap)
    (hL_mv : L.maxV = k6MaxV c.scratch_cap)
    (hlen : st.LengthsOk c) (hag : AgreesExcept fidConeMask s0 st)
    (hcone : FidConeInv F_cur L mvC st nv.toNat nc.toNat)
    (hnc : nc.toNat < L.maxOrig) (hsz28 : sz.toNat < 2 ^ 28)
    (hsz_tmp : sz.toNat ≤ st.core.tmp.length)
    (hlts : ∀ j < sz.toNat, (st.core.tmp[j]?.getD 0#32).toNat < 2 * nv.toNat)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause
      ((st.core.tmp.take sz.toNat).map (fun x => m6ConeLift st.scratch.work_stk1 x.toNat))))
    (hm : (FullMem c st ⋆ R) m)
    (hk : ∀ (ok : Bool) (st' : FullState) (m' : Mem 64),
      st'.LengthsOk c → AgreesExcept fidConeMask s0 st' →
      FidConeInv F_cur L mvC st' nv.toNat (if ok then nc + 1#32 else nc).toNat →
      (ok = false → st'.scratch.scratch_buf = st.scratch.scratch_buf) →
      st'.scratch.tarjan_mark = st.scratch.tarjan_mark →
      st'.scratch.work_stk1 = st.scratch.work_stk1 →
      (FullMem c st' ⋆ R) m' → wp Γ Q X (k (ok, ())) m') :
    wp Γ Q X (Expr.call (as := [i64, i64, i32]) (bs := [.bool])
      "full_k6_add_clause" (Arg.var c.hdr, Arg.var c.pTmp, aSz, ()) k) m := by
  have hm_L := L.hmaxV
  have hnv_le_mvC : nv.toNat ≤ mvC.toNat := hcone.nv_le_mvC
  have hlts_ks : ∀ j < sz.toNat,
      (st.core.tmp[j]?.getD 0#32).toNat <
        2 * (k6StateOfScratch L st.scratch.scratch_buf).nv.toNat := fun j hj => by
    rw [hcone.k6_nv]; have := hlts j hj; omega
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
  have hag' : AgreesExcept fidConeMask s0 st' := hag.update _ (fun _ => rfl)
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

theorem fid_cone_k_unassigned_step {c : FullCfg}
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
    {mvC : BitVec 32} (_hc_u : FidConeInv F_cur L mvC st_u nv_u.toNat nc_w) :
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
          dsimp only [st_u'] at heq_l ⊢
          rw [hel, fid_coneLift_eq_of_getElem hwk_eq_x]; exact heq_l
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

theorem fid_cone_exit_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {L : K6Layout} {mvC : BitVec 32} {s st_e : FullState} {R : Mem 64 → Prop} {Q : Post [i64]}
    {nv nc : BitVec 32} {m : Mem 64}
    (hdw : FullDenseInvW c F0 F_cur s) (hcap : k6MinScr ≤ c.scratch_cap)
    (hL_len : L.scrLen = c.scratch_cap) (hL_mv : L.maxV = k6MaxV c.scratch_cap)
    (hlen_e : st_e.LengthsOk c) (hag_e : AgreesExcept fidConeMask s st_e)
    (hcone_e : FidConeInv F_cur L mvC st_e nv.toNat nc.toNat)
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
  have hnv_le_mvC : nv.toNat ≤ mvC.toNat := hcone_e.nv_le_mvC
  have hnv_max : nv.toNat ≤ L.maxV := hcone_e.nv_leMax
  have hnc_max : nc.toNat ≤ L.maxOrig := hcone_e.nc_le
  obtain ⟨hinv_f, _, hnv_f⟩ := fid_k6ShrinkNv_preserves_inv hcone_e.k6_inv hcone_e.k6_sync hnv1
    hnv_le_mvC hcone_e.mvC_leMax hcone_e.k6_nv hcone_e.k6_lvl hcone_e.k6_na hcone_e.k6_bdd
    hcone_e.k6_trl_bdd
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
  have hag_f : AgreesExcept fidConeMask s s_f := hag_e.update _ (fun _ => rfl)
  have hdw_f := fidConeMask_preserves_dense hag_f hlen_f hdw
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
  rw [← fidConeMask_state_eq hag_f, hpk.1, hpk.2.1] at hQ'
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
theorem m6_denseSlice_step_bin {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} {w0 : BitVec 32} (hs : DenseWatchSliceOk F_cur k lit p rem)
    (hpos : 0 < rem) (hp : k.wstk[p]? = some w0)
    (hbin : (w0 &&& 0x80000000#32) ≠ 0#32) :
    w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
    DenseWatchSliceOk F_cur k lit (p + 1) (rem - 1) := by
  cases hs with
  | empty => omega
  | bin hp' _ hne hlt hent hrest =>
    rw [hp] at hp'; cases Option.some.inj hp'; exact ⟨hne, hlt, hent, hrest⟩
  | occ hp' _ hflag _ _ _ _ =>
    rw [hp] at hp'; cases Option.some.inj hp'; exact absurd hflag hbin

theorem m6_denseSlice_step_occ {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} {w0 : BitVec 32} (hs : DenseWatchSliceOk F_cur k lit p rem)
    (hpos : 0 < rem) (hp : k.wstk[p]? = some w0)
    (hocc : (w0 &&& 0x80000000#32) = 0#32) :
    2 ≤ rem ∧ 3 ≤ w0.toNat ∧
    ∃ cr, k.wstk[p + 1]? = some cr ∧ cr.toNat < 0x80000000 ∧
      cr.toNat ∈ fullArenaClauseRefsCore k ∧
      DenseWatchSliceOk F_cur k lit (p + 2) (rem - 2) := by
  cases hs with
  | empty => omega
  | bin hp' hflag _ _ _ _ =>
    rw [hp] at hp'; cases Option.some.inj hp'; exact absurd hocc hflag
  | occ hp' hp1 _ h3 hlt href hrest =>
    rw [hp] at hp'; cases Option.some.inj hp'
    exact ⟨by omega, h3, _, hp1, hlt, href, hrest⟩

theorem m6_bv32_sub1_of_eq (x y : BitVec 32) (h : x - 1#32 = y) : x = y + 1#32 := by
  bv_omega

theorem m6_bv32_sub1_lt {x : BitVec 32} (hpos : 0 < x.toNat) :
    (x - 1#32).toNat = x.toNat - 1 := by bv_omega

theorem m6_bv32_sub1_zext_toNat (x : BitVec 32) :
    ((x - 1#32).setWidth 64).toNat = (x - 1#32).toNat :=
  bv_c0_zext32_64 _

theorem m6_entails_singleton_of_dup {F : CNF Nat} {l : Nat}
    (h : F.EntailsClause (cnfClause [l, l])) : F.EntailsClause (cnfClause [l]) := by
  rw [CNF.entails_clause_def] at h ⊢
  intro α hα
  obtain ⟨x, hx, hxs⟩ := (clause_sat_cnfClause_iff α [l, l]).mp (h α hα)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hxl | hxl <;> rw [hxl] at hxs <;>
    exact (clause_sat_cnfClause_iff α [l]).mpr ⟨l, List.mem_cons_self, hxs⟩

theorem m6_entails_fst_of_snd_false {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {l0 l1 : Nat} (hl1 : l1 < 2 * k.cur_vars) (hf1 : k.vals[l1]?.getD 0#8 = 0xFF#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [l0, l1])) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l0]) := by
  rw [CNF.entails_clause_def] at hent ⊢
  intro α hα
  obtain ⟨x, hx, hxs⟩ := (clause_sat_cnfClause_iff α [l0, l1]).mp (hent α hα)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hxl0 | hxl1
  · rw [hxl0] at hxs; exact (clause_sat_cnfClause_iff α [l0]).mpr ⟨l0, List.mem_cons_self, hxs⟩
  · rw [hxl1] at hxs
    exact absurd ((sat_cnfClause_singleton α l1).mpr hxs)
      (m6_lvl0_false_not_sat hw hcl0 hl1 hf1 hα)

theorem m6_cone_cnt_le_nv {tmp : List (BitVec 32)} {cnt nv : Nat}
    (hlts : ∀ j < cnt, (tmp[j]?.getD 0#32).toNat < 2 * nv)
    (hnd : ∀ j1 j2, j1 < cnt → j2 < cnt → j1 ≠ j2 →
      (tmp[j1]?.getD 0#32).toNat / 2 ≠ (tmp[j2]?.getD 0#32).toNat / 2) :
    cnt ≤ nv := by
  let xs := (List.range cnt).map fun j => (tmp[j]?.getD 0#32).toNat / 2
  have hnd_xs : xs.Nodup := List.pairwise_iff_getElem.mpr fun i j hi hj hij => by
    simp only [xs, List.length_map, List.length_range] at hi hj
    simp only [xs, List.getElem_map, List.getElem_range]
    exact hnd i j hi hj (Nat.ne_of_lt hij)
  have hle := k6_nodup_subset_length (n := nv) hnd_xs fun v hv => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
    rw [List.mem_range] at hj; have := hlts j hj; omega
  simpa [xs] using hle

theorem m6_cone_unit_tmp_prep {c : FullCfg} {F_cur : List (List Nat)}
    {st : FullState} {nv qi0 pol u : BitVec 32} {litN : Nat}
    (hlen : st.LengthsOk c) (htmp0 : 0 < st.core.tmp.length)
    (hqi : qi0.toNat < nv.toNat) (_hnv_lt31 : nv.toNat < 2 ^ 31)
    (hpol : pol.toNat < 2) (_hwk : (st.scratch.work_stk1[qi0.toNat]?.getD 0#32).toNat * 2 +
      pol.toNat = (2 * (st.scratch.work_stk1[qi0.toNat]?.getD 0#32).toNat + pol.toNat))
    (hu_eq : u.toNat = 2 * qi0.toNat + pol.toNat)
    (hlit_eq : 2 * (st.scratch.work_stk1[qi0.toNat]?.getD 0#32).toNat + pol.toNat = litN)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [litN])) :
    let st' : FullState := { st with core := { st.core with tmp := st.core.tmp.set 0 u } }
    st'.LengthsOk c ∧
    (∀ j < 1, (st'.core.tmp[j]?.getD 0#32).toNat < 2 * nv.toNat) ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause
      ((st'.core.tmp.take 1).map (fun x => m6ConeLift st'.scratch.work_stk1 x.toNat))) := by
  intro st'
  have htm := hlen.core_ok.tmp_len_arr
  refine ⟨⟨{ hlen.core_ok with tmp_len_arr := by simp [st', htm] }, hlen.scratch_ok⟩,
    fun j hj => ?_, ?_⟩
  · have hj0 : j = 0 := by omega
    subst hj0; dsimp only [st']
    rw [List.getElem?_set_self (by omega), Option.getD_some]; omega
  · have htk : st'.core.tmp.take 1 = [u] := by
      dsimp only [st']
      cases ht : st.core.tmp with
      | nil => simp [ht] at htmp0
      | cons x tl => simp
    have hlift : m6ConeLift st.scratch.work_stk1 u.toNat = litN := by
      rw [hu_eq, show pol.toNat = litN % 2 by omega]
      exact coneLift_of_tmk_pair rfl (by omega)
    rw [htk]; simpa only [List.map_cons, List.map_nil, st', hlift] using hent

theorem m6_fullMem_tmp0_congr {c : FullCfg} {st : FullState} {a b : BitVec 32}
    {R : Mem 64 → Prop} {m : Mem 64} (h : a = b)
    (hm : (FullMem c { st with core := { st.core with tmp := st.core.tmp.set 0 a } } ⋆ R) m) :
    (FullMem c { st with core := { st.core with tmp := st.core.tmp.set 0 b } } ⋆ R) m :=
  h ▸ hm

theorem m6_fullMem_tmp01_congr {c : FullCfg} {st : FullState}
    {a0 a1 b0 b1 : BitVec 32} {R : Mem 64 → Prop} {m : Mem 64}
    (h0 : a0 = b0) (h1 : a1 = b1)
    (hm : (FullMem c { st with core :=
      { st.core with tmp := (st.core.tmp.set 0 a0).set 1 a1 } } ⋆ R) m) :
    (FullMem c { st with core :=
      { st.core with tmp := (st.core.tmp.set 0 b0).set 1 b1 } } ⋆ R) m :=
  h0 ▸ h1 ▸ hm

theorem m6_cnfClause_sat_congr {cl : List Nat} {β β' : Nat → Bool} {nv : Nat}
    (hlt : ∀ l ∈ cl, l < 2 * nv) (hag : ∀ i < nv, β i = β' i) :
    (cnfClause cl).Sat β ↔ (cnfClause cl).Sat β' := by
  simp only [clause_sat_cnfClause_iff]
  constructor
  · rintro ⟨l, hl, hs⟩
    refine ⟨l, hl, ?_⟩
    have := hlt l hl
    rw [show litVar l = l / 2 from rfl, ← hag (l / 2) (by omega)]
    exact hs
  · rintro ⟨l, hl, hs⟩
    refine ⟨l, hl, ?_⟩
    have := hlt l hl
    rw [show litVar l = l / 2 from rfl, hag (l / 2) (by omega)]
    exact hs

theorem m6_k6Inv_restrict_nv {F_cur : List (List Nat)} {L : K6Layout}
    {ws : List (BitVec 32)} {ks : K6State} {nv_r nv' : Nat}
    (hinv : K6Inv L (ConeModelSet F_cur ws nv_r) ks)
    (hbdd : K6LitsBounded nv' ks)
    (htrl : ∀ l ∈ k6TrailLits ks, l < 2 * nv') :
    K6Inv L (ConeModelSet F_cur ws nv') ks := by
  have hlift : ∀ β, ConeModelSet F_cur ws nv' β →
      ∃ β', ConeModelSet F_cur ws nv_r β' ∧ ∀ i < nv', β i = β' i := by
    rintro β ⟨α, hα, hagree⟩
    exact ⟨fun i => α (ws[i]?.getD 0#32).toNat, ⟨α, hα, fun _ _ => rfl⟩, hagree⟩
  exact
    { shapes := hinv.shapes
      clauses :=
        { hinv.clauses with
          cl_wf := fun cid hc =>
            let w := hinv.clauses.cl_wf cid hc
            ⟨w.1, w.2.1, w.2.2.1, fun β hβ =>
              let ⟨β', hβ', hag⟩ := hlift β hβ
              (m6_cnfClause_sat_congr (fun l hl => hbdd.1 cid hc l hl) hag).mpr (w.2.2.2 β' hβ')⟩
          incons_ok := fun hi β hβ =>
            let ⟨β', hβ', _⟩ := hlift β hβ
            hinv.clauses.incons_ok hi β' hβ' }
      watches := hinv.watches
      assign :=
        { hinv.assign with
          lvl0_ok := fun i hi hl0 =>
            let w := hinv.assign.lvl0_ok i hi hl0
            ⟨w.1, w.2.1, fun β hβ =>
              let ⟨β', hβ', hag⟩ := hlift β hβ
              have hte : ks.trl_end.toNat ≤ ks.trl.length := by
                rw [hinv.shapes.trl_len]
                exact Nat.le_trans hinv.assign.trl_end_le hinv.clauses.nv_le
              (m6_cnfClause_sat_congr
                (fun l hl => by
                  simp only [List.mem_singleton] at hl; subst hl
                  exact htrl _ (k6_mem_trailLits_of_lt hi hte))
                hag).mpr (w.2.2 β' hβ')⟩ }
      reasons := hinv.reasons }

theorem fidConeInv_pop_var {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {mvC : BitVec 32} {s st_r : FullState} {scr0 ws0 : List (BitVec 32)}
    {saved_nv nv_r : BitVec 32} {nc_w : Nat}
    (hl_r : st_r.LengthsOk c) (ha_r : AgreesExcept fidConeMask s st_r)
    (hc_r : FidConeInv F_cur L mvC st_r nv_r.toNat nc_w)
    (hsav_ge1 : 1 ≤ saved_nv.toNat) (hsav_lt : saved_nv.toNat < nv_r.toNat)
    (hscr_eq : st_r.scratch.scratch_buf = scr0)
    (hbdd_s : K6LitsBounded saved_nv.toNat (k6StateOfScratch L scr0))
    (htrl_s : ∀ l ∈ k6TrailLits (k6StateOfScratch L scr0), l < 2 * saved_nv.toNat)
    (hws_sav : ∀ j < saved_nv.toNat, st_r.scratch.work_stk1[j]? = ws0[j]?) :
    let nv' := nv_r - 1#32
    let vr := st_r.scratch.work_stk1[nv'.toNat]?.getD 0#32
    nv'.toNat = nv_r.toNat - 1 ∧ vr.toNat < st_r.scratch.tarjan_mark.length ∧
    let tmk' := st_r.scratch.tarjan_mark.set vr.toNat 0#32
    let st' : FullState :=
      { st_r with scratch := { st_r.scratch with tarjan_mark := tmk' } }
    st'.LengthsOk c ∧ AgreesExcept fidConeMask s st' ∧
    FidConeInv F_cur L mvC st' nv'.toNat nc_w ∧ st'.scratch.scratch_buf = scr0 ∧
    (∀ j < saved_nv.toNat, st'.scratch.work_stk1[j]? = ws0[j]?) := by
  intro nv' vr
  have hm := L.hmaxV
  have hnv1 : nv'.toNat = nv_r.toNat - 1 := m6_bv32_sub1_lt (by omega)
  have hnv_le : nv'.toNat ≤ nv_r.toNat := by rw [hnv1]; omega
  have hsav_le : saved_nv.toNat ≤ nv'.toNat := by rw [hnv1]; omega
  have hnv_le_mvC := hc_r.nv_le_mvC
  have hnv_leMax := hc_r.nv_leMax
  have hcv_le := hl_r.core_ok.cur_vars_le
  have htm_len := hl_r.scratch_ok.tarjan_mark_len
  have hfwd_last := hc_r.fwd nv'.toNat (by omega)
  have hvr_lt_cv : vr.toNat < st_r.core.cur_vars := hfwd_last.1
  have hvr_bd : vr.toNat < st_r.scratch.tarjan_mark.length := by rw [htm_len]; omega
  refine ⟨hnv1, hvr_bd, ?_⟩
  intro tmk' st'
  have hne_vr : ∀ i < nv'.toNat, (st_r.scratch.work_stk1[i]?.getD 0#32).toNat ≠ vr.toNat :=
    fun i hi heq => by
      have hti := (hc_r.fwd i (by omega)).2
      rw [heq, hfwd_last.2] at hti
      have htn := congrArg BitVec.toNat hti
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i + 1 < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : nv'.toNat + 1 < 2 ^ 32)] at htn
      omega
  refine ⟨⟨hl_r.core_ok, { hl_r.scratch_ok with
      tarjan_mark_len := by simp [st', tmk', htm_len] }⟩,
    fidConeMask_upd_tmk tmk' ha_r,
    { nv_ge1 := by omega
      nv_le_mvC := by omega
      mvC_leMax := hc_r.mvC_leMax
      nv_le_cv := by dsimp [st']; have := hc_r.nv_le_cv; omega
      nc_le := hc_r.nc_le
      scr_len := hc_r.scr_len
      k6_inv := by
        dsimp only [st']
        exact m6_k6Inv_restrict_nv hc_r.k6_inv
          (by
            rw [hscr_eq]
            exact ⟨fun cid hcid l hl => Nat.lt_of_lt_of_le (hbdd_s.1 cid hcid l hl) (by omega),
              fun w hw => Nat.lt_of_lt_of_le (hbdd_s.2 w hw) (by omega)⟩)
          (fun l hl => by
            rw [hscr_eq] at hl; exact Nat.lt_of_lt_of_le (htrl_s l hl) (by omega))
      k6_sync := hc_r.k6_sync
      k6_nv := hc_r.k6_nv
      k6_lvl := hc_r.k6_lvl
      k6_na := hc_r.k6_na
      k6_bdd := by
        rw [hscr_eq]
        exact ⟨fun cid hcid l hl => Nat.lt_of_lt_of_le (hbdd_s.1 cid hcid l hl) (by omega),
          fun w hw => Nat.lt_of_lt_of_le (hbdd_s.2 w hw) (by omega)⟩
      k6_trl_bdd := fun l hl => by
        rw [hscr_eq] at hl; exact Nat.lt_of_lt_of_le (htrl_s l hl) (by omega)
      fwd := fun i hi => by
        dsimp only [st']
        have hti := hc_r.fwd i (by omega)
        rw [List.getElem?_set_ne (Ne.symm (hne_vr i hi))]
        exact hti
      rev := fun v hv => by
        dsimp only [st']
        by_cases hvv : v = vr.toNat
        · subst hvv; left; rw [List.getElem?_set_self (by omega), Option.getD_some]
        · rw [List.getElem?_set_ne (Ne.symm hvv)]
          rcases hc_r.rev v hv with hz | ⟨i, hi, hwi, hti⟩
          · exact Or.inl hz
          · right
            have hne_i : i ≠ nv'.toNat := fun heq => by
              subst heq; exact hvv hwi.symm
            exact ⟨i, by omega, hwi, hti⟩ },
    hscr_eq, hws_sav⟩

theorem fid_cone_load_kptr_hdr {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {mvC : BitVec 32} {st : FullState} {nv nc : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hc : FidConeInv F_cur L mvC st nv nc) (hm : (FullMem c st ⋆ R) m) :
    loadVal m i32 (L.kPtr c.pScratchBuf + BitVec.ofNat 64 6 * 4) =
      some (k6StateOfScratch L st.scratch.scratch_buf).incons ∧
    loadVal m i32 (L.kPtr c.pScratchBuf + BitVec.ofNat 64 4 * 4) =
      some (k6StateOfScratch L st.scratch.scratch_buf).trl_end := by
  have hm1 := hm; rw [fullMem_eq_k6Frame hc.scr_len] at hm1
  have hm2 : (K6Mem L (L.kPtr c.pScratchBuf) (k6StateOfScratch L st.scratch.scratch_buf) ⋆
      (FullK6Frame c L st ⋆ R)) m := sep_ac hm1
  have ha := k6Mem_to_amem hc.k6_inv.shapes hm2
  exact ⟨K6MemATactics.load_k6_incons ha, K6MemATactics.load_k6_trl_end ha⟩

theorem fid_hag_cur_vars {s st : FullState} (h : AgreesExcept fidConeMask s st) :
    st.core.cur_vars = s.core.cur_vars := by rw [fidConeMask_core_eq h]

theorem fid_hag_wvec {s st : FullState} (h : AgreesExcept fidConeMask s st) :
    st.core.wvec = s.core.wvec := by rw [fidConeMask_core_eq h]

theorem fid_hag_wstk {s st : FullState} (h : AgreesExcept fidConeMask s st) :
    st.core.wstk = s.core.wstk := by rw [fidConeMask_core_eq h]

theorem fid_hag_arena {s st : FullState} (h : AgreesExcept fidConeMask s st) :
    st.core.arena = s.core.arena := by rw [fidConeMask_core_eq h]

theorem fid_hag_vals {s st : FullState} (h : AgreesExcept fidConeMask s st) :
    st.core.vals = s.core.vals := by rw [fidConeMask_core_eq h]

theorem fid_cone_rollback_step {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {mvC : BitVec 32} {s st_r : FullState} {scr0 ws0 : List (BitVec 32)}
    {saved_nv nv_r cv qi_l : BitVec 32} {nc_w : Nat}
    (hl_r : st_r.LengthsOk c) (ha_r : AgreesExcept fidConeMask s st_r)
    (hc_r : FidConeInv F_cur L mvC st_r nv_r.toNat nc_w)
    (hsav_ge1 : 1 ≤ saved_nv.toNat) (hsav_lt : saved_nv.toNat < nv_r.toNat)
    (hqi_lt_sav : qi_l.toNat < saved_nv.toNat)
    (hscr_eq : st_r.scratch.scratch_buf = scr0)
    (hbdd_s : K6LitsBounded saved_nv.toNat (k6StateOfScratch L scr0))
    (htrl_s : ∀ l ∈ k6TrailLits (k6StateOfScratch L scr0), l < 2 * saved_nv.toNat)
    (hws_sav : ∀ j < saved_nv.toNat, st_r.scratch.work_stk1[j]? = ws0[j]?)
    (htr : st_r.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 (qi_l.toNat + 1)) :
    (nv_r - 1#32).toNat = nv_r.toNat - 1 ∧
    ((nv_r - 1#32).setWidth 64).toNat < st_r.scratch.work_stk1.length ∧
    ∀ (hvr_ws : ((nv_r - 1#32).setWidth 64).toNat < st_r.scratch.work_stk1.length),
      let vr_raw := st_r.scratch.work_stk1[((nv_r - 1#32).setWidth 64).toNat]'hvr_ws
      let tmk' := st_r.scratch.tarjan_mark.set vr_raw.toNat 0#32
      let st' : FullState := { st_r with scratch := { st_r.scratch with tarjan_mark := tmk' } }
      (BitVec.setWidth 64 vr_raw).toNat < st_r.scratch.tarjan_mark.length ∧
      st'.LengthsOk c ∧ AgreesExcept fidConeMask s st' ∧
      FidConeInv F_cur L mvC st' (nv_r - 1#32).toNat nc_w ∧
      st'.scratch.scratch_buf = scr0 ∧
      (∀ j < saved_nv.toNat, st'.scratch.work_stk1[j]? = ws0[j]?) ∧
      st'.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 (qi_l.toNat + 1) := by
  have hm := L.hmaxV
  have hnv_r_mvC := hc_r.nv_le_mvC
  have hnv_r_max := hc_r.nv_leMax
  have hpop := fidConeInv_pop_var hl_r ha_r hc_r hsav_ge1 hsav_lt hscr_eq hbdd_s htrl_s hws_sav
  have htm_r := hl_r.scratch_ok.tarjan_mark_len
  have hwk_r := hl_r.scratch_ok.work_stk1_len
  have hvr_z : ((nv_r - 1#32).setWidth 64).toNat = (nv_r - 1#32).toNat := bv_c0_zext32_64 _
  have hvr_lt : ((nv_r - 1#32).setWidth 64).toNat < st_r.scratch.work_stk1.length := by
    rw [hwk_r, hvr_z, hpop.1]; have := hc_r.nv_le_cv; have := hl_r.core_ok.cur_vars_le; omega
  refine ⟨hpop.1, hvr_lt, fun hvr_ws => ?_⟩
  intro vr_raw tmk' st'
  have hvr_eq : vr_raw = st_r.scratch.work_stk1[(nv_r - 1#32).toNat]?.getD 0#32 := by
    rw [List.getElem?_eq_getElem (by rw [hwk_r]; omega), Option.getD_some]
    exact m6_list_getElem_congr hvr_z _ _
  have hne_cv_pop : vr_raw.toNat ≠ cv.toNat := fun heq => by
    have h1 := (hc_r.fwd (nv_r.toNat - 1) (by omega)).2
    rw [← hpop.1, ← hvr_eq, heq, htr] at h1
    have htn := congrArg BitVec.toNat h1
    simp only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : qi_l.toNat + 1 < 2 ^ 32)] at htn
    omega
  refine ⟨by rw [bv_c0_zext32_64, hvr_eq]; exact hpop.2.1,
    ⟨hl_r.core_ok, { hl_r.scratch_ok with
      tarjan_mark_len := by simp [st', tmk', htm_r] }⟩,
    ?_, ?_, ?_, hpop.2.2.2.2.2.2, ?_⟩
  · dsimp only [st', tmk']; rw [hvr_eq]; exact hpop.2.2.2.1
  · dsimp only [st', tmk']; rw [hvr_eq]; exact hpop.2.2.2.2.1
  · exact hscr_eq
  · dsimp only [st', tmk']; rw [List.getElem?_set_ne hne_cv_pop]; exact htr

theorem m6_tmk_set_mod64 (tmk : List (BitVec 32)) (x : BitVec 32) :
    tmk.set (x.toNat % 18446744073709551616) 0#32 = tmk.set x.toNat 0#32 := by
  rw [Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

theorem m6_tmk_set_get_congr {xs tmk : List (BitVec 32)} {i1 i2 : Nat}
    (h1 : i1 < xs.length) (h2 : i2 < xs.length) (heq : i1 = i2) :
    tmk.set (xs[i1]'h1).toNat 0#32 = tmk.set (xs[i2]'h2).toNat 0#32 := by
  rw [m6_list_getElem_congr heq h1 h2]

theorem m6_nat_sub1_lt {n x : Nat} (hlt : x < n) {x1 : Nat} (hx1 : x1 = x + 1) :
    n - x1 < n - x := by
  subst hx1; exact Nat.sub_lt_sub_left hlt (Nat.lt_succ_self x)

theorem m6_nat_sub2_lt {n x x2 : Nat} (_hlt : x < n) (hle : x2 ≤ n) (hx2 : x2 = x + 2) :
    n - x2 < n - x := by
  subst hx2; omega

theorem m6_nat_sub_lo1_lt {lo x x' : Nat} (hlt : lo < x) (hx' : x' = x - 1) :
    x' - lo < x - lo := by
  subst hx'; omega

theorem m6_le_sub1_of_lt {a b : Nat} (h : a < b) : a ≤ b - 1 := by omega

theorem fid_cone_rollback_mem_step {c : FullCfg} {st_r : FullState}
    {xs : List (BitVec 32)} {i1 i2 : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (h1 : i1 < xs.length) (h2 : i2 < xs.length) (heq : i1 = i2)
    (hm : (FullMem c { st_r with scratch := { st_r.scratch with
      tarjan_mark := st_r.scratch.tarjan_mark.set (xs[i1]'h1).toNat 0#32 } } ⋆ R) m) :
    (FullMem c { st_r with scratch := { st_r.scratch with
      tarjan_mark := st_r.scratch.tarjan_mark.set (xs[i2]'h2).toNat 0#32 } } ⋆ R) m :=
  (congrArg (fun t => (FullMem c { st_r with scratch := { st_r.scratch with
      tarjan_mark := t } } ⋆ R) m)
    (m6_tmk_set_get_congr h1 h2 heq)).mp hm

theorem fid_cone_push_var_step_ok {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {mvC : BitVec 32} {s st : FullState} {ws0 : List (BitVec 32)} {nv v_new cv qi_l : BitVec 32}
    {saved_nv nc_w : Nat}
    (hlen : st.LengthsOk c) (hag : AgreesExcept fidConeMask s st)
    (hcone : FidConeInv F_cur L mvC st nv.toNat nc_w)
    (hnv_max : nv.toNat < mvC.toNat) (hv_lt : v_new.toNat < s.core.cur_vars)
    (hmiss : st.scratch.tarjan_mark[v_new.toNat]?.getD 0#32 = 0#32)
    (hsav_le : saved_nv ≤ nv.toNat) (hqi_lt : qi_l.toNat < nv.toNat)
    (hws_sav : ∀ j < saved_nv, st.scratch.work_stk1[j]? = ws0[j]?)
    (htmk_cv : st.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 (qi_l.toNat + 1))
    (hwk_cv : (st.scratch.work_stk1[qi_l.toNat]?.getD 0#32).toNat = cv.toNat) :
    let tmk := st.scratch.tarjan_mark
    let ws1 := st.scratch.work_stk1
    let st' : FullState :=
      { st with scratch :=
        { st.scratch with tarjan_mark := tmk.set v_new.toNat (nv + 1#32),
                          work_stk1 := ws1.set nv.toNat v_new } }
    nv.toNat < s.core.cur_vars ∧ (nv + 1#32).toNat = nv.toNat + 1 ∧ nv.toNat ≠ qi_l.toNat ∧
    cv.toNat ≠ v_new.toNat ∧ st'.LengthsOk c ∧ AgreesExcept fidConeMask s st' ∧
    FidConeInv F_cur L mvC st' (nv + 1#32).toNat nc_w ∧
    (∀ j < saved_nv, st'.scratch.work_stk1[j]? = ws0[j]?) ∧
    st'.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 (qi_l.toNat + 1) ∧
    (st'.scratch.work_stk1[qi_l.toNat]?.getD 0#32).toNat = cv.toNat ∧
    st'.scratch.tarjan_mark[v_new.toNat]?.getD 0#32 ≠ 0#32 := by
  intro tmk ws1 st'
  have hmL := L.hmaxV
  have hmL_lo : 512 ≤ L.maxV := hmL.1
  have hmL_hi : L.maxV ≤ 8192 := hmL.2
  have hmvC_le := hcone.mvC_leMax
  have hcv_eq := fid_hag_cur_vars hag
  have hpush := fidConeInv_push_var hlen hcone hnv_max (hcv_eq.symm ▸ hv_lt) hmiss
  have hnv_lt : nv.toNat < s.core.cur_vars := hcv_eq ▸ hpush.1
  have hnv1 : (nv + 1#32).toNat = nv.toNat + 1 := m6_bv32_add1 (by omega)
  have hne_cv : cv.toNat ≠ v_new.toNat := fun heq => by
    rw [← heq, htmk_cv] at hmiss
    have := congrArg BitVec.toNat hmiss
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : qi_l.toNat + 1 < 2 ^ 32)] at this
  have hne_nv_qi : nv.toNat ≠ qi_l.toNat := by omega
  have htm_len := hlen.scratch_ok.tarjan_mark_len
  have hwk_len := hlen.scratch_ok.work_stk1_len
  have hcv_le := hlen.core_ok.cur_vars_le
  have htm_bd : v_new.toNat < tmk.length := by rw [htm_len]; omega
  refine ⟨hnv_lt, hnv1, hne_nv_qi, hne_cv,
    ⟨hlen.core_ok, { hlen.scratch_ok with
      tarjan_mark_len := by simp [st', tmk, htm_len]
      work_stk1_len := by simp [st', ws1, hwk_len] }⟩,
    fidConeMask_upd_tmk_ws1 _ _ hag,
    by rw [hnv1]; simpa [st', m6_bv32_ofNat_add1 nv] using hpush.2,
    fun j hj => by dsimp only [st']; rw [List.getElem?_set_ne (by omega)]; exact hws_sav j hj,
    by dsimp only [st']; rw [List.getElem?_set_ne (Ne.symm hne_cv)]; exact htmk_cv,
    by dsimp only [st']; rw [List.getElem?_set_ne hne_nv_qi]; exact hwk_cv,
    by dsimp only [st']; rw [List.getElem?_set_self htm_bd, Option.getD_some]
       intro h; have := congrArg BitVec.toNat h; simp [hnv1] at this⟩

/-! ## 2. Packed State Structures & Fast Cone Step Helpers -/

structure FidConeBase (F_cur : List (List Nat)) (L : K6Layout) (mvC : BitVec 32)
    (c : FullCfg) (s : FullState) (cv qi_l : BitVec 32) (nv nc : Nat)
    (st : FullState) : Prop where
  hlen : st.LengthsOk c
  hag : AgreesExcept fidConeMask s st
  hcone : FidConeInv F_cur L mvC st nv nc
  htmk : st.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 (qi_l.toNat + 1)
  hwk : (st.scratch.work_stk1[qi_l.toNat]?.getD 0#32).toNat = cv.toNat

structure FidConeSavedBase (F_cur : List (List Nat)) (L : K6Layout) (mvC : BitVec 32)
    (c : FullCfg) (s : FullState) (cv qi_l saved_nv : BitVec 32)
    (ws0 scr0 : List (BitVec 32)) (nv nc : Nat) (st : FullState) : Prop
    extends FidConeBase F_cur L mvC c s cv qi_l nv nc st where
  hsav_le : saved_nv.toNat ≤ nv
  hscr : st.scratch.scratch_buf = scr0
  hws : ∀ j < saved_nv.toNat, st.scratch.work_stk1[j]? = ws0[j]?

structure FidConeScanBase (F_cur : List (List Nat)) (L : K6Layout) (mvC : BitVec 32)
    (c : FullCfg) (s : FullState) (cv qi_l saved_nv : BitVec 32)
    (ws0 scr0 : List (BitVec 32)) (cr : BitVec 32)
    (nv nc cnt idx : Nat) (st : FullState) : Prop
    extends FidConeSavedBase F_cur L mvC c s cv qi_l saved_nv ws0 scr0 nv nc st where
  hlts : ∀ j < cnt, (st.core.tmp[j]?.getD 0#32).toNat < 2 * nv
  hcov : ∀ i < idx,
    let l := (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat
    s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨
    l ∈ (st.core.tmp.take cnt).map (fun x => m6ConeLift st.scratch.work_stk1 x.toNat)
  hvars : ∀ j < cnt, ∃ p < idx,
    (s.core.arena[cr.toNat + 3 + p]?.getD 0#32).toNat / 2 =
      (st.scratch.work_stk1[(st.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
  hnd : ∀ j1 j2, j1 < cnt → j2 < cnt → j1 ≠ j2 →
    (st.core.tmp[j1]?.getD 0#32).toNat / 2 ≠ (st.core.tmp[j2]?.getD 0#32).toNat / 2

theorem fid_cone_wvec_facts {c : FullCfg} {s st_x : FullState}
    {F_cur : List (List Nat)} {lit : BitVec 32}
    (hlen : s.LengthsOk c) (hlen_x : st_x.LengthsOk c)
    (hag_x : AgreesExcept fidConeMask s st_x)
    (hdw : DenseWatchesInv F_cur s.core) (hlit_lt : lit.toNat < 2 * s.core.cur_vars) :
    let wOff := (st_x.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat)).toNat]'(by
      have := hdw.layout.bounds lit.toNat hlit_lt
      have := hlen_x.core_ok.wvec_len
      have := hlen.core_ok.cur_vars_le
      have := c.hmaxv; unfold dimacsBound at this
      rw [m6_bv64_shl1]; omega)).setWidth 64
    let wSz := (st_x.core.wvec[((BitVec.setWidth 64 lit <<< (1 : Nat)) + 1#64).toNat]'(by
      have := hdw.layout.bounds lit.toNat hlit_lt
      have := hlen_x.core_ok.wvec_len
      have := hlen.core_ok.cur_vars_le
      have := c.hmaxv; unfold dimacsBound at this
      rw [m6_bv64_shl1_add1]; omega)).setWidth 64
    wOff.toNat = fullWatchOffCore s.core lit.toNat ∧
    wSz.toNat = fullWatchSizeCore s.core lit.toNat ∧
    (wOff + wSz).toNat = fullWatchOffCore s.core lit.toNat + fullWatchSizeCore s.core lit.toNat ∧
    wOff.toNat ≤ (wOff + wSz).toNat ∧
    (wOff + wSz).toNat - wOff.toNat = fullWatchSizeCore s.core lit.toNat ∧
    (wOff + wSz).toNat ≤ s.core.wstk.length ∧
    (2 * lit.toNat) % 2 ^ 64 = (BitVec.setWidth 64 lit <<< (1 : Nat)).toNat ∧
    (2 * lit.toNat + 1) % 2 ^ 64 = ((BitVec.setWidth 64 lit <<< (1 : Nat)) + 1#64).toNat := by
  have hwvec_x := hlen_x.core_ok.wvec_len
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hwvec_eq : st_x.core.wvec = s.core.wvec := fid_hag_wvec hag_x
  have hbounds := hdw.layout.bounds lit.toNat hlit_lt
  have hwlen_le := hlen.core_ok.wlen_le
  have hwcap_lt := c.hwcap; unfold dimacsBound at hwcap_lt
  have h2lit : (BitVec.setWidth 64 lit <<< (1 : Nat)).toNat = 2 * lit.toNat := m6_bv64_shl1 _
  have h2lit1 : ((BitVec.setWidth 64 lit <<< (1 : Nat)) + 1#64).toNat = 2 * lit.toNat + 1 :=
    m6_bv64_shl1_add1 _
  have hwo : ((st_x.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat)).toNat]'(by
      rw [hwvec_x, h2lit]; omega)).setWidth 64).toNat = fullWatchOffCore s.core lit.toNat := by
    unfold fullWatchOffCore
    rw [bv_c0_zext32_64, List.getElem?_eq_getElem (by rw [← hwvec_eq, hwvec_x]; omega),
      Option.getD_some]
    simp only [hwvec_eq, h2lit]
  have hws : ((st_x.core.wvec[((BitVec.setWidth 64 lit <<< (1 : Nat)) + 1#64).toNat]'(by
      rw [hwvec_x, h2lit1]; omega)).setWidth 64).toNat = fullWatchSizeCore s.core lit.toNat := by
    unfold fullWatchSizeCore
    rw [bv_c0_zext32_64, List.getElem?_eq_getElem (by rw [← hwvec_eq, hwvec_x]; omega),
      Option.getD_some]
    simp only [hwvec_eq, h2lit1]
  have hend : ((st_x.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat)).toNat]'(by
        rw [hwvec_x, h2lit]; omega)).setWidth 64 +
      (st_x.core.wvec[((BitVec.setWidth 64 lit <<< (1 : Nat)) + 1#64).toNat]'(by
        rw [hwvec_x, h2lit1]; omega)).setWidth 64).toNat =
      fullWatchOffCore s.core lit.toNat + fullWatchSizeCore s.core lit.toNat := by
    rw [BitVec.toNat_add, hwo, hws, Nat.mod_eq_of_lt (by omega)]
  refine ⟨hwo, hws, hend, by omega, by omega, by rw [hend, hlen.core_ok.wstk_len_arr]; omega,
    by rw [h2lit, Nat.mod_eq_of_lt (by omega)],
    by rw [h2lit1, Nat.mod_eq_of_lt (by omega)]⟩

theorem fid_cone_hp_wstk {s st_w : FullState} {p wEnd : BitVec 64}
    (hwstk_eq : st_w.core.wstk = s.core.wstk) (hp_lt : p.toNat < wEnd.toNat)
    (hend_le : wEnd.toNat ≤ s.core.wstk.length) :
    p.toNat < st_w.core.wstk.length := by
  rw [hwstk_eq]; exact Nat.lt_of_lt_of_le hp_lt hend_le

theorem fid_cone_wstk_p_toNat_eq (p : BitVec 64) (hp : p.toNat < 2 ^ 63) :
    (p.toNat + 1) % 2 ^ 64 = p.toNat + 1 :=
  Nat.mod_eq_of_lt (by omega)

theorem fid_cone_sub_sub_eq (a b c : Nat) : a - (b + c) = a - b - c := by omega

theorem fid_coneBase_of_rollback_step {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {mvC : BitVec 32} {s st_r : FullState} {scr0 ws0 : List (BitVec 32)}
    {saved_nv nv_r cv qi_l : BitVec 32} {nc_w : Nat}
    (hs : FidConeSavedBase F_cur L mvC c s cv qi_l saved_nv ws0 scr0 nv_r.toNat nc_w st_r)
    (hsav_ge1 : 1 ≤ saved_nv.toNat) (hsav_lt : saved_nv.toNat < nv_r.toNat)
    (hqi_lt_sav : qi_l.toNat < saved_nv.toNat)
    (hbdd_s : K6LitsBounded saved_nv.toNat (k6StateOfScratch L scr0))
    (htrl_s : ∀ l ∈ k6TrailLits (k6StateOfScratch L scr0), l < 2 * saved_nv.toNat) :
    (nv_r - 1#32).toNat = nv_r.toNat - 1 ∧
    ((nv_r - 1#32).setWidth 64).toNat < st_r.scratch.work_stk1.length ∧
    ∀ (hvr_ws : ((nv_r - 1#32).setWidth 64).toNat < st_r.scratch.work_stk1.length),
      let vr_raw := st_r.scratch.work_stk1[((nv_r - 1#32).setWidth 64).toNat]'hvr_ws
      let tmk' := st_r.scratch.tarjan_mark.set vr_raw.toNat 0#32
      let st' : FullState := { st_r with scratch := { st_r.scratch with tarjan_mark := tmk' } }
      (BitVec.setWidth 64 vr_raw).toNat < st_r.scratch.tarjan_mark.length ∧
      FidConeSavedBase F_cur L mvC c s cv qi_l saved_nv ws0 scr0 (nv_r - 1#32).toNat nc_w st' := by
  have hst := fid_cone_rollback_step hs.hlen hs.hag hs.hcone hsav_ge1 hsav_lt hqi_lt_sav hs.hscr
    hbdd_s htrl_s hs.hws hs.htmk
  refine ⟨hst.1, hst.2.1, fun hvr_ws => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hst.2.2 hvr_ws
  exact ⟨h1, ⟨⟨h2, h3, h4, h7, hs.hwk⟩, by rw [hst.1]; exact m6_le_sub1_of_lt hsav_lt, h5, h6⟩⟩

theorem fid_cone_push_var_base_ok {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {mvC : BitVec 32} {s st : FullState} {ws0 scr0 : List (BitVec 32)}
    {nv v_new cv qi_l saved_nv : BitVec 32} {nc_w : Nat}
    (hs : FidConeSavedBase F_cur L mvC c s cv qi_l saved_nv ws0 scr0 nv.toNat nc_w st)
    (hnv_max : nv.toNat < mvC.toNat) (hv_lt : v_new.toNat < s.core.cur_vars)
    (hmiss : st.scratch.tarjan_mark[v_new.toNat]?.getD 0#32 = 0#32)
    (hqi_lt : qi_l.toNat < nv.toNat) :
    let tmk := st.scratch.tarjan_mark
    let ws1 := st.scratch.work_stk1
    let st' : FullState :=
      { st with scratch :=
        { st.scratch with tarjan_mark := tmk.set v_new.toNat (nv + 1#32),
                          work_stk1 := ws1.set nv.toNat v_new } }
    nv.toNat < s.core.cur_vars ∧ (nv + 1#32).toNat = nv.toNat + 1 ∧ nv.toNat ≠ qi_l.toNat ∧
    cv.toNat ≠ v_new.toNat ∧ FidConeSavedBase F_cur L mvC c s cv qi_l saved_nv ws0 scr0
      (nv + 1#32).toNat nc_w st' ∧
    st'.scratch.tarjan_mark[v_new.toNat]?.getD 0#32 ≠ 0#32 := by
  intro tmk ws1 st'
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    fid_cone_push_var_step_ok hs.hlen hs.hag hs.hcone hnv_max hv_lt hmiss hs.hsav_le hqi_lt
      hs.hws hs.htmk hs.hwk
  exact ⟨h1, h2, h3, h4, ⟨⟨h5, h6, h7, h9, h10⟩,
    (by rw [h2]; exact Nat.le_trans hs.hsav_le (Nat.le_succ _)), hs.hscr, h8⟩, h11⟩

/-! ## 3. Call & Escalation Limit Helpers -/

theorem fid_if_false_prop {c a b : Prop} [Decidable c] (hc : ¬ c) (hb : b) :
    if c then a else b := by
  by_cases hc' : c
  · exact absurd hc' hc
  · simp only [hc', ↓reduceIte]; exact hb

theorem fid_call_max_v {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    {c : FullCfg} {aCap : Arg Val i64} {m : Mem 64}
    {k : Tup Val [i64] → Expr Val Cont rs}
    (haCap : aCap.val = BitVec.ofNat 64 c.scratch_cap)
    (hk : wp Γ Q X (k (BitVec.ofNat 64 (k6MaxV c.scratch_cap), ())) m) :
    wp Γ Q X (Expr.call (as := [i64]) (bs := [i64]) "full_m6_max_v" (aCap, ()) k) m := by
  refine wp_call_of_spec _ k ?_
  refine hMaxV (aCap.val, ()) m (fun r m' => wp Γ Q X (k r) m') X ?_
  have hlt : c.scratch_cap < 2 ^ 64 := Nat.lt_trans c.hscr (by unfold dimacsBound; decide)
  rw [haCap]; unfold m6MaxVSpec; dsimp only
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]; exact hk


end LeanQbe.T.Examples.Kissat.FullFidelitySweep

end
