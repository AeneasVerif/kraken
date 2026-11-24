/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanQbe Contributors
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8SweepV2
public import LeanQbe.T.Examples.Kissat.FullM6SweepProofConeLemmas

/-!
# Kissat M8 Sweep V2 — `full_m6_sweep_cone` (`V3t2`) `Func.wp` Proof

Proves `m8_sweep_cone_wp : m6SweepConeSpec` for `FullM8SweepV2.full_m6_sweep_cone_body`:
- Computes `mv_c = min mv 256` and `mc_c = min max_orig 1024` BEFORE `full_k6_init(h, mv_c)`.
- Seeds `k[25] = (root_v ^ 0x9E3779B9u) | 1u` (`k6Set25`), preserving `K6Inv`, `K6TrailSynced`,
  and `nv = 256#32` (`M8ConeInv`).
- Reuses `FullM6SweepProofConeLemmas` pure/BFS lemmas cleanly.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM8SweepV2

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open Kraken.Bedrock2.Test
open FullArenaTactics
open scoped FullArenaTactics M6SweepTactics

/-! ## 1. Isolated PRNG Seed Word (`k[25]`) & `M8ConeInv` (`nv ≤ 256`, `k6.nv = 256`) -/

@[expose] def k6Set25 (ks : K6State) (v : BitVec 32) : K6State :=
  { ks with hdrTail := ks.hdrTail.set 0 v }

theorem k6Set25_shapes {L : K6Layout} {ks : K6State} (h : ks.ShapesOk L) (v : BitVec 32) :
    (k6Set25 ks v).ShapesOk L :=
  { h with hdrTail_len := by simp [k6Set25, h.hdrTail_len] }

theorem k6Set25_inv {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (h : K6Inv L P ks) (v : BitVec 32) : K6Inv L P (k6Set25 ks v) := by
  refine ⟨k6Set25_shapes h.shapes v, ?_, h.watches, ?_, h.reasons⟩
  · exact k6ClausesOk_cast h.clauses rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  · exact k6BaseAssignOk_cast h.assign rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem k6Set25_sync {ks : K6State} (h : K6TrailSynced ks) (v : BitVec 32) :
    K6TrailSynced (k6Set25 ks v) := h

private theorem k6Set25_hdrWords (ks : K6State) (v : BitVec 32) :
    (k6HdrWords ks).set 25 v = k6HdrWords (k6Set25 ks v) := rfl

theorem k6Set25_store {L : K6Layout} {kPtr : BitVec 64} {ks : K6State}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 25 * 4) ∧
      (K6MemA L kPtr (k6Set25 ks v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 25 * 4) v) := by
  obtain ⟨hsh, hm'⟩ := k6MemA_to_mem hm
  have hi : 25 < (k6HdrWords ks).length := by rw [k6HdrWords_length hsh]; decide
  rw [k6_ptr_nat_mul4 kPtr 25 (by decide)]
  have heq : ((K6Tree L kPtr ks).set (k6Path 0)
      (array (t := i32) kPtr ((k6HdrWords ks).set 25 v))).eval =
      K6Mem L kPtr (k6Set25 ks v) := by
    rw [k6Set25_hdrWords]; rfl
  obtain ⟨hok, hst⟩ := sepTree_arr_put (t := K6Tree L kPtr ks) (p := k6Path 0) rfl (by decide)
    v hi heq hm'
  exact ⟨hok, k6Mem_to_amem (k6Set25_shapes hsh v) hst⟩

private theorem m8_coneLift_eq_of_getElem {ws1 ws2 : List (BitVec 32)} {l : Nat}
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
    let β : Nat → Bool := fun k => xor (decide (k = m6ConeLift ws1 l / 2)) (litSign (m6ConeLift ws1 l))
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


private def m8ConeMask (t : FullState) : FullState :=
  { core := { t.core with tmp := [] }
    scratch := { t.scratch with work_stk1 := [], tarjan_mark := [], scratch_buf := [] } }

private theorem m8ConeMask_core_eq {s st : FullState} (h : AgreesExcept m8ConeMask s st) :
    st.core = { s.core with tmp := st.core.tmp } := by
  have hc : ({ st.core with tmp := [] } : FullCoreState) = { s.core with tmp := [] } :=
    congrArg FullState.core h
  cases h1 : st.core; cases h2 : s.core
  rw [h1, h2] at hc; cases hc; rfl

private theorem m8ConeMask_state_eq {s st : FullState} (h : AgreesExcept m8ConeMask s st) :
    st = { s with
      core := { s.core with tmp := st.core.tmp }
      scratch := { s.scratch with
        work_stk1 := st.scratch.work_stk1
        tarjan_mark := st.scratch.tarjan_mark
        scratch_buf := st.scratch.scratch_buf } } := by
  have hc := m8ConeMask_core_eq h
  have hs : (m8ConeMask st).scratch = (m8ConeMask s).scratch := congrArg FullState.scratch h
  cases st with | mk c1 sc1 => cases s with | mk c2 sc2 =>
  dsimp only [m8ConeMask] at hc hs ⊢
  cases sc1; cases sc2; cases hs; rw [hc]

private theorem m8ConeMask_preserves_dense {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} (hag : AgreesExcept m8ConeMask s st)
    (hlen : st.LengthsOk c) (hdw : FullDenseInvW c F0 F_cur s) :
    FullDenseInvW c F0 F_cur st := by
  have hc0 := m8ConeMask_core_eq hag
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

private theorem m8ConeMask_upd_tmp {s st : FullState} (tmp' : List (BitVec 32))
    (h : AgreesExcept m8ConeMask s st) :
    AgreesExcept m8ConeMask s { st with core := { st.core with tmp := tmp' } } :=
  h.update (fun x => { x with core := { x.core with tmp := tmp' } }) fun _ => rfl

private theorem m8ConeMask_upd_tmk {s st : FullState} (tmk' : List (BitVec 32))
    (h : AgreesExcept m8ConeMask s st) :
    AgreesExcept m8ConeMask s { st with scratch := { st.scratch with tarjan_mark := tmk' } } :=
  h.update (fun x => { x with scratch := { x.scratch with tarjan_mark := tmk' } }) fun _ => rfl

private theorem m8ConeMask_upd_tmk_ws1 {s st : FullState} (tmk' ws1' : List (BitVec 32))
    (h : AgreesExcept m8ConeMask s st) :
    AgreesExcept m8ConeMask s
      { st with scratch := { st.scratch with tarjan_mark := tmk', work_stk1 := ws1' } } :=
  h.update
    (fun x => { x with scratch := { x.scratch with tarjan_mark := tmk', work_stk1 := ws1' } })
    fun _ => rfl
private theorem m8_k6ShrinkNv_preserves_inv {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks : K6State} {nv : BitVec 32}
    (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks)
    (hnv1 : 1 ≤ nv.toNat) (hnv_256 : nv.toNat ≤ 256) (hks_nv : ks.nv = 256#32)
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
  have hnv_le_old : nv.toNat ≤ ks.nv.toNat := by
    rw [hks_nv]; simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : 256 < 2 ^ 32)]; exact hnv_256
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
private structure M8ConeInv (F_cur : List (List Nat)) (L : K6Layout)
    (st : FullState) (nv nc : Nat) : Prop where
  nv_ge1 : 1 ≤ nv
  nv_le256 : nv ≤ 256
  nv_le_cv : nv ≤ st.core.cur_vars
  nc_le : nc ≤ L.maxOrig
  scr_len : st.scratch.scratch_buf.length = L.scrLen
  k6_inv : K6Inv L (ConeModelSet F_cur st.scratch.work_stk1 nv)
    (k6StateOfScratch L st.scratch.scratch_buf)
  k6_sync : K6TrailSynced (k6StateOfScratch L st.scratch.scratch_buf)
  k6_nv : (k6StateOfScratch L st.scratch.scratch_buf).nv = 256#32
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


private theorem M8ConeInv.nv_leMax {F_cur : List (List Nat)} {L : K6Layout} {st : FullState}
    {nv nc : Nat} (h : M8ConeInv F_cur L st nv nc) : nv ≤ L.maxV :=
  Nat.le_trans h.nv_le256 (Nat.le_trans (by decide : 256 ≤ 512) L.hmaxV.1)

private theorem m8ConeInv_tmp_irrel {F_cur : List (List Nat)} {L : K6Layout} {st : FullState}
    {nv nc : Nat} {tmp' : List (BitVec 32)} (h : M8ConeInv F_cur L st nv nc) :
    M8ConeInv F_cur L { st with core := { st.core with tmp := tmp' } } nv nc :=
  ⟨h.nv_ge1, h.nv_le256, h.nv_le_cv, h.nc_le, h.scr_len, h.k6_inv, h.k6_sync, h.k6_nv,
   h.k6_lvl, h.k6_na, h.k6_bdd, h.k6_trl_bdd, h.fwd, h.rev⟩

private theorem m8ConeInv_init {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout} {s : FullState}
    {scr0 : List (BitVec 32)} {root_v : BitVec 32}
    (hlen : s.LengthsOk c) (hL_len : L.scrLen = c.scratch_cap)
    (hroot : root_v.toNat < s.core.cur_vars) (htmk : M6TmkZero s)
    (hscr0 : scr0.length = c.scratch_cap)
    (hK : ∀ P, K6Inv L P (k6StateOfScratch L scr0))
    (hsy : K6TrailSynced (k6StateOfScratch L scr0))
    (hnv : (k6StateOfScratch L scr0).nv = 256#32)
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
    s1.LengthsOk c ∧ AgreesExcept m8ConeMask s s1 ∧ M8ConeInv F_cur L s1 1 0 := by
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
      nv_le256 := by omega
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

private theorem m8ConeInv_push_var {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {s : FullState} {nv nc : Nat} {ov : BitVec 32}
    (hlen : s.LengthsOk c) (hc : M8ConeInv F_cur L s nv nc)
    (hnv_max : nv < 256) (hov : ov.toNat < s.core.cur_vars)
    (hmiss : s.scratch.tarjan_mark[ov.toNat]?.getD 0#32 = 0#32) :
    nv < s.core.cur_vars ∧
    let s' : FullState :=
      { s with scratch :=
        { s.scratch with
          tarjan_mark := s.scratch.tarjan_mark.set ov.toNat (BitVec.ofNat 32 (nv + 1))
          work_stk1 := s.scratch.work_stk1.set nv ov } }
    M8ConeInv F_cur L s' (nv + 1) nc := by
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
      nv_le256 := by omega
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

private theorem m8_cone_call_add_clause {Γ : Env}
    (hAddCl : M6EnvSpec Γ "full_k6_add_clause" k6AddClauseSpec)
    {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout} {s0 st : FullState}
    {nv nc sz : BitVec 32} {aSz : Arg Val i32}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    {k : Tup Val [.bool] → Expr Val Cont [i64]}
    (haSz : aSz.val = sz) (hL_len : L.scrLen = c.scratch_cap)
    (hL_mv : L.maxV = k6MaxV c.scratch_cap)
    (hlen : st.LengthsOk c) (hag : AgreesExcept m8ConeMask s0 st)
    (hcone : M8ConeInv F_cur L st nv.toNat nc.toNat)
    (hnc : nc.toNat < L.maxOrig) (hsz28 : sz.toNat < 2 ^ 28)
    (hsz_tmp : sz.toNat ≤ st.core.tmp.length)
    (hlts : ∀ j < sz.toNat, (st.core.tmp[j]?.getD 0#32).toNat < 2 * nv.toNat)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause
      ((st.core.tmp.take sz.toNat).map (fun x => m6ConeLift st.scratch.work_stk1 x.toNat))))
    (hm : (FullMem c st ⋆ R) m)
    (hk : ∀ (ok : Bool) (st' : FullState) (m' : Mem 64),
      st'.LengthsOk c → AgreesExcept m8ConeMask s0 st' →
      M8ConeInv F_cur L st' nv.toNat (if ok then nc + 1#32 else nc).toNat →
      (ok = false → st'.scratch.scratch_buf = st.scratch.scratch_buf) →
      st'.scratch.tarjan_mark = st.scratch.tarjan_mark →
      st'.scratch.work_stk1 = st.scratch.work_stk1 →
      (FullMem c st' ⋆ R) m' → wp Γ Q X (k (ok, ())) m') :
    wp Γ Q X (Expr.call (as := [i64, i64, i32]) (bs := [.bool])
      "full_k6_add_clause" (Arg.var c.hdr, Arg.var c.pTmp, aSz, ()) k) m := by
  have hm_L := L.hmaxV
  have hnv_256 : nv.toNat ≤ 256 := hcone.nv_le256
  have hlts_ks : ∀ j < sz.toNat,
      (st.core.tmp[j]?.getD 0#32).toNat <
        2 * (k6StateOfScratch L st.scratch.scratch_buf).nv.toNat := fun j hj => by
    rw [hcone.k6_nv]; have := hlts j hj
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : 256 < 2 ^ 32)]; omega
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
  have hag' : AgreesExcept m8ConeMask s0 st' := hag.update _ (fun _ => rfl)
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

private theorem m8_cone_k_unassigned_step {c : FullCfg}
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
    (_hc_u : M8ConeInv F_cur L st_u nv_u.toNat nc_w) :
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
          rw [hel, m8_coneLift_eq_of_getElem hwk_eq_x]; exact heq_l
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

private theorem m8_cone_exit_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {L : K6Layout} {s st_e : FullState} {R : Mem 64 → Prop} {Q : Post [i64]}
    {nv nc : BitVec 32} {m : Mem 64}
    (hdw : FullDenseInvW c F0 F_cur s) (hcap : k6MinScr ≤ c.scratch_cap)
    (hL_len : L.scrLen = c.scratch_cap) (hL_mv : L.maxV = k6MaxV c.scratch_cap)
    (hlen_e : st_e.LengthsOk c) (hag_e : AgreesExcept m8ConeMask s st_e)
    (hcone_e : M8ConeInv F_cur L st_e nv.toNat nc.toNat)
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
  have hnv_256 : nv.toNat ≤ 256 := hcone_e.nv_le256
  have hnv_max : nv.toNat ≤ L.maxV := hcone_e.nv_leMax
  have hnc_max : nc.toNat ≤ L.maxOrig := hcone_e.nc_le
  obtain ⟨hinv_f, _, hnv_f⟩ := m8_k6ShrinkNv_preserves_inv hcone_e.k6_inv hcone_e.k6_sync hnv1
    hnv_256 hcone_e.k6_nv hcone_e.k6_lvl hcone_e.k6_na hcone_e.k6_bdd hcone_e.k6_trl_bdd
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
  have hag_f : AgreesExcept m8ConeMask s s_f := hag_e.update _ (fun _ => rfl)
  have hdw_f := m8ConeMask_preserves_dense hag_f hlen_f hdw
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
  rw [← m8ConeMask_state_eq hag_f, hpk.1, hpk.2.1] at hQ'
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
private theorem m6_denseSlice_step_bin {F_cur : List (List Nat)} {k : FullCoreState}
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

private theorem m6_denseSlice_step_occ {F_cur : List (List Nat)} {k : FullCoreState}
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

private theorem m6_bv32_sub1_of_eq (x y : BitVec 32) (h : x - 1#32 = y) : x = y + 1#32 := by
  bv_omega

private theorem m6_bv32_sub1_lt {x : BitVec 32} (hpos : 0 < x.toNat) :
    (x - 1#32).toNat = x.toNat - 1 := by bv_omega

private theorem m6_bv32_sub1_zext_toNat (x : BitVec 32) :
    ((x - 1#32).setWidth 64).toNat = (x - 1#32).toNat :=
  bv_c0_zext32_64 _

private theorem m6_entails_singleton_of_dup {F : CNF Nat} {l : Nat}
    (h : F.EntailsClause (cnfClause [l, l])) : F.EntailsClause (cnfClause [l]) := by
  rw [CNF.entails_clause_def] at h ⊢
  intro α hα
  obtain ⟨x, hx, hxs⟩ := (clause_sat_cnfClause_iff α [l, l]).mp (h α hα)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hxl | hxl <;> rw [hxl] at hxs <;>
    exact (clause_sat_cnfClause_iff α [l]).mpr ⟨l, List.mem_cons_self, hxs⟩

private theorem m6_entails_fst_of_snd_false {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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

private theorem m6_cone_cnt_le_nv {tmp : List (BitVec 32)} {cnt nv : Nat}
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

private theorem m6_cone_unit_tmp_prep {c : FullCfg} {F_cur : List (List Nat)}
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

private theorem m6_fullMem_tmp0_congr {c : FullCfg} {st : FullState} {a b : BitVec 32}
    {R : Mem 64 → Prop} {m : Mem 64} (h : a = b)
    (hm : (FullMem c { st with core := { st.core with tmp := st.core.tmp.set 0 a } } ⋆ R) m) :
    (FullMem c { st with core := { st.core with tmp := st.core.tmp.set 0 b } } ⋆ R) m :=
  h ▸ hm

private theorem m6_fullMem_tmp01_congr {c : FullCfg} {st : FullState}
    {a0 a1 b0 b1 : BitVec 32} {R : Mem 64 → Prop} {m : Mem 64}
    (h0 : a0 = b0) (h1 : a1 = b1)
    (hm : (FullMem c { st with core :=
      { st.core with tmp := (st.core.tmp.set 0 a0).set 1 a1 } } ⋆ R) m) :
    (FullMem c { st with core :=
      { st.core with tmp := (st.core.tmp.set 0 b0).set 1 b1 } } ⋆ R) m :=
  h0 ▸ h1 ▸ hm

private theorem m6_cnfClause_sat_congr {cl : List Nat} {β β' : Nat → Bool} {nv : Nat}
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

private theorem m6_k6Inv_restrict_nv {F_cur : List (List Nat)} {L : K6Layout}
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

private theorem m8ConeInv_pop_var {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {s st_r : FullState} {scr0 ws0 : List (BitVec 32)} {saved_nv nv_r : BitVec 32} {nc_w : Nat}
    (hl_r : st_r.LengthsOk c) (ha_r : AgreesExcept m8ConeMask s st_r)
    (hc_r : M8ConeInv F_cur L st_r nv_r.toNat nc_w)
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
    st'.LengthsOk c ∧ AgreesExcept m8ConeMask s st' ∧
    M8ConeInv F_cur L st' nv'.toNat nc_w ∧ st'.scratch.scratch_buf = scr0 ∧
    (∀ j < saved_nv.toNat, st'.scratch.work_stk1[j]? = ws0[j]?) := by
  intro nv' vr
  have hm := L.hmaxV
  have hnv1 : nv'.toNat = nv_r.toNat - 1 := m6_bv32_sub1_lt (by omega)
  have hnv_le : nv'.toNat ≤ nv_r.toNat := by rw [hnv1]; omega
  have hsav_le : saved_nv.toNat ≤ nv'.toNat := by rw [hnv1]; omega
  have hnv_256 := hc_r.nv_le256
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
    m8ConeMask_upd_tmk tmk' ha_r,
    { nv_ge1 := by omega
      nv_le256 := by omega
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

private theorem m8_cone_load_kptr_hdr {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {st : FullState} {nv nc : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hc : M8ConeInv F_cur L st nv nc) (hm : (FullMem c st ⋆ R) m) :
    loadVal m i32 (L.kPtr c.pScratchBuf + BitVec.ofNat 64 6 * 4) =
      some (k6StateOfScratch L st.scratch.scratch_buf).incons ∧
    loadVal m i32 (L.kPtr c.pScratchBuf + BitVec.ofNat 64 4 * 4) =
      some (k6StateOfScratch L st.scratch.scratch_buf).trl_end := by
  have hm1 := hm; rw [fullMem_eq_k6Frame hc.scr_len] at hm1
  have hm2 : (K6Mem L (L.kPtr c.pScratchBuf) (k6StateOfScratch L st.scratch.scratch_buf) ⋆
      (FullK6Frame c L st ⋆ R)) m := sep_ac hm1
  have ha := k6Mem_to_amem hc.k6_inv.shapes hm2
  exact ⟨K6MemATactics.load_k6_incons ha, K6MemATactics.load_k6_trl_end ha⟩

private theorem m8_hag_cur_vars {s st : FullState} (h : AgreesExcept m8ConeMask s st) :
    st.core.cur_vars = s.core.cur_vars := by rw [m8ConeMask_core_eq h]

private theorem m8_hag_wvec {s st : FullState} (h : AgreesExcept m8ConeMask s st) :
    st.core.wvec = s.core.wvec := by rw [m8ConeMask_core_eq h]

private theorem m8_hag_wstk {s st : FullState} (h : AgreesExcept m8ConeMask s st) :
    st.core.wstk = s.core.wstk := by rw [m8ConeMask_core_eq h]

private theorem m8_hag_arena {s st : FullState} (h : AgreesExcept m8ConeMask s st) :
    st.core.arena = s.core.arena := by rw [m8ConeMask_core_eq h]

private theorem m8_hag_vals {s st : FullState} (h : AgreesExcept m8ConeMask s st) :
    st.core.vals = s.core.vals := by rw [m8ConeMask_core_eq h]

private theorem m8_cone_rollback_step {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {s st_r : FullState} {scr0 ws0 : List (BitVec 32)} {saved_nv nv_r cv qi_l : BitVec 32}
    {nc_w : Nat}
    (hl_r : st_r.LengthsOk c) (ha_r : AgreesExcept m8ConeMask s st_r)
    (hc_r : M8ConeInv F_cur L st_r nv_r.toNat nc_w)
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
      st'.LengthsOk c ∧ AgreesExcept m8ConeMask s st' ∧
      M8ConeInv F_cur L st' (nv_r - 1#32).toNat nc_w ∧
      st'.scratch.scratch_buf = scr0 ∧
      (∀ j < saved_nv.toNat, st'.scratch.work_stk1[j]? = ws0[j]?) ∧
      st'.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 (qi_l.toNat + 1) := by
  have hm := L.hmaxV
  have hnv_r_256 := hc_r.nv_le256
  have hnv_r_max := hc_r.nv_leMax
  have hpop := m8ConeInv_pop_var hl_r ha_r hc_r hsav_ge1 hsav_lt hscr_eq hbdd_s htrl_s hws_sav
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

private theorem m6_tmk_set_mod64 (tmk : List (BitVec 32)) (x : BitVec 32) :
    tmk.set (x.toNat % 18446744073709551616) 0#32 = tmk.set x.toNat 0#32 := by
  rw [Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

private theorem m6_tmk_set_get_congr {xs tmk : List (BitVec 32)} {i1 i2 : Nat}
    (h1 : i1 < xs.length) (h2 : i2 < xs.length) (heq : i1 = i2) :
    tmk.set (xs[i1]'h1).toNat 0#32 = tmk.set (xs[i2]'h2).toNat 0#32 := by
  rw [m6_list_getElem_congr heq h1 h2]

private theorem m6_nat_sub1_lt {n x : Nat} (hlt : x < n) {x1 : Nat} (hx1 : x1 = x + 1) :
    n - x1 < n - x := by
  subst hx1; exact Nat.sub_lt_sub_left hlt (Nat.lt_succ_self x)

private theorem m6_nat_sub2_lt {n x x2 : Nat} (_hlt : x < n) (hle : x2 ≤ n) (hx2 : x2 = x + 2) :
    n - x2 < n - x := by
  subst hx2; omega

private theorem m6_nat_sub_lo1_lt {lo x x' : Nat} (hlt : lo < x) (hx' : x' = x - 1) :
    x' - lo < x - lo := by
  subst hx'; omega

private theorem m6_le_sub1_of_lt {a b : Nat} (h : a < b) : a ≤ b - 1 := by omega

private theorem m8_cone_rollback_mem_step {c : FullCfg} {st_r : FullState}
    {xs : List (BitVec 32)} {i1 i2 : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (h1 : i1 < xs.length) (h2 : i2 < xs.length) (heq : i1 = i2)
    (hm : (FullMem c { st_r with scratch := { st_r.scratch with
      tarjan_mark := st_r.scratch.tarjan_mark.set (xs[i1]'h1).toNat 0#32 } } ⋆ R) m) :
    (FullMem c { st_r with scratch := { st_r.scratch with
      tarjan_mark := st_r.scratch.tarjan_mark.set (xs[i2]'h2).toNat 0#32 } } ⋆ R) m :=
  (congrArg (fun t => (FullMem c { st_r with scratch := { st_r.scratch with
      tarjan_mark := t } } ⋆ R) m)
    (m6_tmk_set_get_congr h1 h2 heq)).mp hm

private theorem m8_cone_push_var_step_ok {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {s st : FullState} {ws0 : List (BitVec 32)} {nv v_new cv qi_l : BitVec 32}
    {saved_nv nc_w : Nat}
    (hlen : st.LengthsOk c) (hag : AgreesExcept m8ConeMask s st)
    (hcone : M8ConeInv F_cur L st nv.toNat nc_w)
    (hnv_max : nv.toNat < 256) (hv_lt : v_new.toNat < s.core.cur_vars)
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
    cv.toNat ≠ v_new.toNat ∧ st'.LengthsOk c ∧ AgreesExcept m8ConeMask s st' ∧
    M8ConeInv F_cur L st' (nv + 1#32).toNat nc_w ∧
    (∀ j < saved_nv, st'.scratch.work_stk1[j]? = ws0[j]?) ∧
    st'.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 (qi_l.toNat + 1) ∧
    (st'.scratch.work_stk1[qi_l.toNat]?.getD 0#32).toNat = cv.toNat ∧
    st'.scratch.tarjan_mark[v_new.toNat]?.getD 0#32 ≠ 0#32 := by
  intro tmk ws1 st'
  have hmL := L.hmaxV
  have hmL_lo : 512 ≤ L.maxV := hmL.1
  have hmL_hi : L.maxV ≤ 8192 := hmL.2
  have hcv_eq := m8_hag_cur_vars hag
  have hpush := m8ConeInv_push_var hlen hcone hnv_max (hcv_eq.symm ▸ hv_lt) hmiss
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
    m8ConeMask_upd_tmk_ws1 _ _ hag,
    by rw [hnv1]; simpa [st', m6_bv32_ofNat_add1 nv] using hpush.2,
    fun j hj => by dsimp only [st']; rw [List.getElem?_set_ne (by omega)]; exact hws_sav j hj,
    by dsimp only [st']; rw [List.getElem?_set_ne (Ne.symm hne_cv)]; exact htmk_cv,
    by dsimp only [st']; rw [List.getElem?_set_ne hne_nv_qi]; exact hwk_cv,
    by dsimp only [st']; rw [List.getElem?_set_self htm_bd, Option.getD_some]
       intro h; have := congrArg BitVec.toNat h; simp [hnv1] at this⟩

/-! ## 2. Packed State Structures & Fast Cone Step Helpers -/

private structure M8ConeBase (F_cur : List (List Nat)) (L : K6Layout)
    (c : FullCfg) (s : FullState) (cv qi_l : BitVec 32) (nv nc : Nat)
    (st : FullState) : Prop where
  hlen : st.LengthsOk c
  hag : AgreesExcept m8ConeMask s st
  hcone : M8ConeInv F_cur L st nv nc
  htmk : st.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 (qi_l.toNat + 1)
  hwk : (st.scratch.work_stk1[qi_l.toNat]?.getD 0#32).toNat = cv.toNat

private structure M8ConeSavedBase (F_cur : List (List Nat)) (L : K6Layout)
    (c : FullCfg) (s : FullState) (cv qi_l saved_nv : BitVec 32)
    (ws0 scr0 : List (BitVec 32)) (nv nc : Nat) (st : FullState) : Prop
    extends M8ConeBase F_cur L c s cv qi_l nv nc st where
  hsav_le : saved_nv.toNat ≤ nv
  hscr : st.scratch.scratch_buf = scr0
  hws : ∀ j < saved_nv.toNat, st.scratch.work_stk1[j]? = ws0[j]?

private structure M8ConeScanBase (F_cur : List (List Nat)) (L : K6Layout)
    (c : FullCfg) (s : FullState) (cv qi_l saved_nv : BitVec 32)
    (ws0 scr0 : List (BitVec 32)) (cr : BitVec 32)
    (nv nc cnt idx : Nat) (st : FullState) : Prop
    extends M8ConeSavedBase F_cur L c s cv qi_l saved_nv ws0 scr0 nv nc st where
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

private theorem m8_cone_wvec_facts {c : FullCfg} {s st_x : FullState}
    {F_cur : List (List Nat)} {lit : BitVec 32}
    (hlen : s.LengthsOk c) (hlen_x : st_x.LengthsOk c)
    (hag_x : AgreesExcept m8ConeMask s st_x)
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
  have hwvec_eq : st_x.core.wvec = s.core.wvec := m8_hag_wvec hag_x
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

private theorem m8_cone_hp_wstk {s st_w : FullState} {p wEnd : BitVec 64}
    (hwstk_eq : st_w.core.wstk = s.core.wstk) (hp_lt : p.toNat < wEnd.toNat)
    (hend_le : wEnd.toNat ≤ s.core.wstk.length) :
    p.toNat < st_w.core.wstk.length := by
  rw [hwstk_eq]; exact Nat.lt_of_lt_of_le hp_lt hend_le

private theorem m8_cone_wstk_p_toNat_eq (p : BitVec 64) (hp : p.toNat < 2 ^ 63) :
    (p.toNat + 1) % 2 ^ 64 = p.toNat + 1 :=
  Nat.mod_eq_of_lt (by omega)

private theorem m8_cone_sub_sub_eq (a b c : Nat) : a - (b + c) = a - b - c := by omega

private theorem m8_coneBase_of_rollback_step {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {s st_r : FullState} {scr0 ws0 : List (BitVec 32)} {saved_nv nv_r cv qi_l : BitVec 32}
    {nc_w : Nat} (hs : M8ConeSavedBase F_cur L c s cv qi_l saved_nv ws0 scr0 nv_r.toNat nc_w st_r)
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
      M8ConeSavedBase F_cur L c s cv qi_l saved_nv ws0 scr0 (nv_r - 1#32).toNat nc_w st' := by
  have hst := m8_cone_rollback_step hs.hlen hs.hag hs.hcone hsav_ge1 hsav_lt hqi_lt_sav hs.hscr
    hbdd_s htrl_s hs.hws hs.htmk
  refine ⟨hst.1, hst.2.1, fun hvr_ws => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hst.2.2 hvr_ws
  exact ⟨h1, ⟨⟨h2, h3, h4, h7, hs.hwk⟩, by rw [hst.1]; exact m6_le_sub1_of_lt hsav_lt, h5, h6⟩⟩

private theorem m8_cone_push_var_base_ok {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {s st : FullState} {ws0 scr0 : List (BitVec 32)} {nv v_new cv qi_l saved_nv : BitVec 32}
    {nc_w : Nat} (hs : M8ConeSavedBase F_cur L c s cv qi_l saved_nv ws0 scr0 nv.toNat nc_w st)
    (hnv_max : nv.toNat < 256) (hv_lt : v_new.toNat < s.core.cur_vars)
    (hmiss : st.scratch.tarjan_mark[v_new.toNat]?.getD 0#32 = 0#32)
    (hqi_lt : qi_l.toNat < nv.toNat) :
    let tmk := st.scratch.tarjan_mark
    let ws1 := st.scratch.work_stk1
    let st' : FullState :=
      { st with scratch :=
        { st.scratch with tarjan_mark := tmk.set v_new.toNat (nv + 1#32),
                          work_stk1 := ws1.set nv.toNat v_new } }
    nv.toNat < s.core.cur_vars ∧ (nv + 1#32).toNat = nv.toNat + 1 ∧ nv.toNat ≠ qi_l.toNat ∧
    cv.toNat ≠ v_new.toNat ∧ M8ConeSavedBase F_cur L c s cv qi_l saved_nv ws0 scr0
      (nv + 1#32).toNat nc_w st' ∧
    st'.scratch.tarjan_mark[v_new.toNat]?.getD 0#32 ≠ 0#32 := by
  intro tmk ws1 st'
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    m8_cone_push_var_step_ok hs.hlen hs.hag hs.hcone hnv_max hv_lt hmiss hs.hsav_le hqi_lt
      hs.hws hs.htmk hs.hwk
  exact ⟨h1, h2, h3, h4, ⟨⟨h5, h6, h7, h9, h10⟩,
    (by rw [h2]; exact Nat.le_trans hs.hsav_le (Nat.le_succ _)), hs.hscr, h8⟩, h11⟩

/-! ## 3. `full_m6_sweep_cone_wp` (`17/39`) -/

private theorem m8_if_false_prop {c a b : Prop} [Decidable c] (hc : ¬ c) (hb : b) :
    if c then a else b := by
  by_cases hc' : c
  · exact absurd hc' hc
  · simp only [hc', ↓reduceIte]; exact hb

private theorem m8_call_max_v {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
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


theorem m8_sweep_cone_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hInit : M6EnvSpec Γ "full_k6_init" k6InitSpec)
    (hAddCl : M6EnvSpec Γ "full_k6_add_clause" k6AddClauseSpec) :
    ∀ args m Q X, m6SweepConeSpec args m Q X →
      Func.wp Γ full_m6_sweep_cone_body args m Q X := by
  rintro ⟨h, root_v, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hdw, hcap, hroot, htmk, hm, hQ⟩
  have hlen := hdw.1; have hw := hdw.2.1; have hnd := hdw.2.2.2.1
  have hcl0 := hdw.2.2.2.2.2.1; have hdm := hdw.2.2.2.2.2.2
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hdwatches : DenseWatchesInv F_cur s.core := by
    have hmw := hw.watches; unfold ModeWatchesInv at hmw; rwa [ite_eq_right hdm] at hmw
  obtain ⟨L, hL_def⟩ : ∃ L : K6Layout, L = k6LayoutOfCap c.scratch_cap hcap c.hscr := ⟨_, rfl⟩
  have hL_len : L.scrLen = c.scratch_cap := by rw [hL_def]; exact k6LayoutOfCap_scrLen hcap c.hscr
  have hL_mv : L.maxV = k6MaxV c.scratch_cap := by rw [hL_def]; rfl
  clear hL_def
  have hmL := L.hmaxV
  have hmL_lo : 512 ≤ L.maxV := hmL.1
  have hmL_hi : L.maxV ≤ 8192 := hmL.2
  have hmv_bounds := k6MaxV_bounds hcap
  have hmv64_lt : k6MaxV c.scratch_cap < 2 ^ 32 := by omega
  let mv : BitVec 32 := (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32
  have hmv_eq : mv = L.mv32 := by
    apply BitVec.eq_of_toNat_eq
    simp only [mv, K6PtrTactics.k6_mv32_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), hL_mv]
  have hmv_nat : mv.toNat = L.maxV := by rw [hmv_eq, K6PtrTactics.k6_mv32_toNat]
  have hmo_nat : (mv * 3#32).toNat = L.maxOrig := by
    unfold K6Layout.maxOrig; bv_omega
  have hkptr_rw : c.pScratchBuf + (1280#32 + (mv <<< (1 : Nat))).setWidth 64 * 4 =
      L.kPtr c.pScratchBuf := by
    rw [hmv_eq, k6_ptr_base_k6Base]
  have hm_shl1 : ∀ x : BitVec 32, x <<< (1 : BitVec 32) = x <<< (1 : Nat) := fun _ => rfl
  have hkptr_c0 : c.pScratchBuf + BitVec.setWidth 64
      ((1280 : BitVec 32) + (BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) <<<
        (1 : BitVec 32))) * 4 = L.kPtr c.pScratchBuf := by
    rw [hm_shl1]; exact hkptr_rw
  have hkptr_c0_nat : c.pScratchBuf + BitVec.setWidth 64
      ((1280 : BitVec 32) + (BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) <<<
        (1 : Nat))) * 4 = L.kPtr c.pScratchBuf := hkptr_rw
  have hmv_c0 : (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = L.mv32 := hmv_eq
  have hqnext_c0 : L.kPtr c.pScratchBuf + BitVec.setWidth 64
      ((32 : BitVec 32) + (3 : BitVec 32) *
        (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32) * 4 =
      L.kPtr c.pScratchBuf + BitVec.ofNat 64 (4 * L.oQNext) := by
    rw [hmv_c0]; simpa [K6Layout.oQNext] using k6_ptr_add_mul L (L.kPtr c.pScratchBuf) 3 (by decide)
  unfold Func.wp full_m6_sweep_cone_body
  m6_steps
  refine m8_call_max_v hMaxV (c := c) rfl ?_
  m6_split
  · exfalso
    have hz : mv = 0#32 := hc
    rw [hmv_eq] at hz
    have h0 := congrArg BitVec.toNat hz
    simp only [BitVec.toNat_ofNat, K6PtrTactics.k6_mv32_toNat] at h0; omega
  c0_hsteps_nogrp
  m6_to_group
  refine wp_join_group (ts := [i32])
    (fun (mv_c, ()) mm => mv_c = 256#32 ∧ (FullMem c s ⋆ R) mm) ?_ ?_
  · rintro _ ⟨mv_c, ⟨⟩⟩ mm ⟨hmv_c, hmm⟩
    subst mv_c
    c0_hsteps_nogrp
    m6_to_group
    refine wp_join_group (ts := [i32])
      (fun (mc_c, ()) mm2 => mc_c = 1024#32 ∧ (FullMem c s ⋆ R) mm2) ?_ ?_
    · rintro _ ⟨mc_c, ⟨⟩⟩ mm2 ⟨hmc_c, hmm2⟩
      subst mc_c
      m6_steps
      m6_call hInit
      refine ⟨c, s, R, rfl, hlen, hmm2, ?_⟩
      refine m8_if_false_prop ?_ ?_
      · dsimp only [Arg.val_var, Prod.fst]
        rw [show (256#32 : BitVec 32).toNat = 256 from by decide, ← hL_mv]
        omega
      intro L0 scr0 m0 hL0_len hL0_mv
      dsimp only
      intro hlen0 _hpre0 hK0 hsy0 hnv0 hnc0 hlvl0 _hpr0 htr0 _hun0 _hin0 hna0 _hst0 _ho0 _hnq0 hm0
      have hL0_eq : L0 = L :=
        K6Layout.eq_of_scrLen_maxV (hL0_len.trans hL_len.symm) (hL0_mv.trans hL_mv.symm)
      subst L0
      let s0 : FullState := { s with scratch := { s.scratch with scratch_buf := scr0 } }
      have hscr0 : scr0.length = c.scratch_cap := hlen0.scratch_ok.scratch_buf_len
      have hscr0_L : s0.scratch.scratch_buf.length = L.scrLen := hscr0.trans hL_len.symm
      have hkb_le0 : L.k6Base ≤ s0.scratch.scratch_buf.length := by
        rw [hscr0_L]; unfold K6Layout.scrLen; omega
      let seed25 : BitVec 32 := (root_v ^^^ 0x9E3779B9#32) ||| 1#32
      let ks0 := k6StateOfScratch L scr0
      let ks0' := k6Set25 ks0 seed25
      have hm0_ka : (K6MemA L (L.kPtr c.pScratchBuf) ks0 ⋆ (FullK6Frame c L s0 ⋆ R)) m0 := by
        rw [fullMem_eq_k6Frame hscr0_L] at hm0
        exact k6Mem_to_amem (hK0 (fun _ => True)).shapes (sep_ac hm0)
      obtain ⟨hok25, hm1_ka⟩ := k6Set25_store seed25 hm0_ka
      let scr1 := s0.scratch.scratch_buf.take L.k6Base ++ ks0'.toSlab
      let s1 : FullState := { s0 with scratch := { s0.scratch with scratch_buf := scr1 } }
      have hm1 : (FullMem c s1 ⋆ R) (storeMem m0 i32 (L.kPtr c.pScratchBuf + BitVec.ofNat 64 25 * 4) seed25) := by
        obtain ⟨_, hkm1⟩ := k6MemA_to_mem hm1_ka
        exact fullMem_join_k6 (c := c) (L := L) (s := s0) hkb_le0
          (k6Set25_shapes (hK0 (fun _ => True)).shapes seed25) (sep_ac hkm1)
      have hscr1_len : scr1.length = c.scratch_cap := by
        dsimp only [scr1]
        rw [List.length_append, List.length_take_of_le hkb_le0,
          ks0'.toSlab_length (k6Set25_shapes (hK0 (fun _ => True)).shapes seed25), ← hL_len]
        unfold K6Layout.scrLen; omega
      have hof1 : k6StateOfScratch L scr1 = ks0' := by
        unfold k6StateOfScratch; dsimp only [scr1]
        rw [k6_slab_drop_exact _ _ (List.length_take_of_le hkb_le0)]
        exact K6State.ofSlab_toSlab (k6Set25_shapes (hK0 (fun _ => True)).shapes seed25)
      have hlen1_s : s1.LengthsOk c := ⟨hlen0.core_ok, { hlen0.scratch_ok with scratch_buf_len := hscr1_len }⟩
      have hK1 : ∀ P, K6Inv L P (k6StateOfScratch L scr1) := fun P =>
        hof1 ▸ k6Set25_inv (hK0 P) seed25
      have hsy1 : K6TrailSynced (k6StateOfScratch L scr1) :=
        hof1 ▸ k6Set25_sync hsy0 seed25
      have hnv1 : (k6StateOfScratch L scr1).nv = 256#32 := by rw [hof1]; exact hnv0
      have hnc1 : (k6StateOfScratch L scr1).nc = 0#32 := by rw [hof1]; exact hnc0
      have hlvl1 : (k6StateOfScratch L scr1).lvl = 0#32 := by rw [hof1]; exact hlvl0
      have htr1 : (k6StateOfScratch L scr1).trl_end = 0#32 := by rw [hof1]; exact htr0
      have hna1 : (k6StateOfScratch L scr1).nassump = 0#32 := by rw [hof1]; exact hna0
      have h0_wk0 : (BitVec.signExtend 64 (0 : BitVec 32)).toNat < s1.scratch.work_stk1.length := by
        rw [hlen1_s.scratch_ok.work_stk1_len,
          show (BitVec.signExtend 64 (0 : BitVec 32)).toNat = 0 from rfl]; omega
      let s1w : FullState :=
        { s1 with scratch := { s1.scratch with
            work_stk1 :=
              s1.scratch.work_stk1.set (BitVec.signExtend 64 (0 : BitVec 32)).toNat root_v } }
      have hrt_tm0 : (BitVec.setWidth 64 root_v).toNat < s1w.scratch.tarjan_mark.length := by
        rw [hlen1_s.scratch_ok.tarjan_mark_len, bv_c0_zext32_64]; omega
      obtain ⟨hlen1, hag1, hcone1⟩ :=
        m8ConeInv_init (F_cur := F_cur) hlen hL_len hroot htmk hscr1_len hK1 hsy1 hnv1
          hnc1 hlvl1 htr1 hna1
      clear hm
      change wp _ _ _ _ _
      c0_hsteps_nogrp
      dsimp only [Prod.fst]
      first | rw [hkptr_c0] | rw [hkptr_c0_nat]
      try rw [show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 25) : BitVec 64) = 25#64 from rfl]
      try rw [show (BitVec.signExtend 64 (25 : BitVec 32) : BitVec 64) = 25#64 from rfl]
      try rw [show (root_v ^^^ 2654435769 ||| 1 : BitVec 32) = seed25 from rfl]
      refine ⟨hok25, ?_⟩
      clear hm0 hm0_ka hm1_ka hok25
      change wp _ _ _ _ _
      dsimp only [Arg.val_var]
      have hm_s1 : (FullMem c s1 ⋆ R) _ := hm1
      m6_steps
      obtain ⟨st0, hst0_def⟩ : ∃ st0 : FullState, st0 =
        { s1w with scratch :=
          { s1w.scratch with
            tarjan_mark := s1w.scratch.tarjan_mark.set (BitVec.setWidth 64 root_v).toNat 1#32 } } :=
        ⟨_, rfl⟩
      -- Outer BFS loop: `while (qi < nv && depth < 2u && !limit_reached && nc < mc_c)`
      refine wp_loop_inv (ts := [i32, i32, i32, i32, .bool])
        (fun (nv, nc, qi, depth, _lim, ()) mo =>
          qi.toNat ≤ nv.toNat ∧ depth.toNat ≤ 2 ∧ ∃ st : FullState,
            st.LengthsOk c ∧ AgreesExcept m8ConeMask s st ∧
            M8ConeInv F_cur L st nv.toNat nc.toNat ∧ (FullMem c st ⋆ R) mo)
        (fun (_, _, _, depth, _, ()) _ => 2 - depth.toNat) ?_ ?_
      · intro _ hJ_out
        m6_steps
        refine hJ_out (1#32, 0#32, 0#32, 0#32, false, ()) _
          ⟨Nat.zero_le _, Nat.zero_le _, _, hlen1, hag1, hcone1, ?_⟩
        simpa only [hst0_def, s1w, s1, s0,
          show (BitVec.signExtend 64 (0 : BitVec 32)).toNat = 0 from rfl,
          bv_c0_zext32_64] using (by assumption : (FullMem c _ ⋆ R) _)
      rintro _ ⟨nv, nc, qi, depth, lim, ⟨⟩⟩ mo
        ⟨hqi_le, hdep_le, st, hlen_st, hag_st, hcone_st, hmo⟩ hJ_out
      clear hm hm1 hmm hmm2 hm_s1 hst0_def st0 hcone1 hag1 hlen1 hrt_tm0 s1w h0_wk0
        hK1 hsy1 hnv1 hnc1 hlvl1 htr1 hna1 hlen1_s hof1 hscr1_len s1 scr1 ks0' ks0 seed25
        hkb_le0 hscr0_L s0 hscr0 _hpre0 _hpr0 _hun0 _hin0 _hst0 _ho0 _hnq0
        hlen0 hK0 hsy0 hnv0 hnc0 hlvl0 htr0 hna0 hL0_len hL0_mv scr0
      m6_to_group
      refine wp_join_group (ts := [])
        (fun () m_ex => ∃ st_e : FullState,
          st_e.LengthsOk c ∧ AgreesExcept m8ConeMask s st_e ∧
          M8ConeInv F_cur L st_e nv.toNat nc.toNat ∧ (FullMem c st_e ⋆ R) m_ex)
        (fun _ () m_ex ⟨st_e, hlen_e, hag_e, hcone_e, hm_e⟩ => by
          clear hJ_out hmo hqi_le hdep_le hlen_st hag_st hcone_st
          have hscr_e := hcone_e.scr_len
          have hkb_le : L.k6Base ≤ st_e.scratch.scratch_buf.length := by
            rw [hscr_e]; unfold K6Layout.scrLen; omega
          let ks_e := k6StateOfScratch L st_e.scratch.scratch_buf
          have hte_le : ks_e.trl_end.toNat ≤ nv.toNat :=
            m6_trl_end_le_of_bdd hcone_e.k6_inv hcone_e.k6_trl_bdd
          have hnv_ge1 : 1 ≤ nv.toNat := hcone_e.nv_ge1
          have hnv_leMax : nv.toNat ≤ L.maxV := hcone_e.nv_leMax
          change wp _ _ _ _ _
          c0_hsteps
          obtain ⟨Rfr, hRfr⟩ : ∃ Rfr : Mem 64 → Prop, Rfr = (FullK6Frame c L st_e ⋆ R) := ⟨_, rfl⟩
          have hm_ka : (K6MemA L (L.kPtr c.pScratchBuf) ks_e ⋆ Rfr) m_ex := by
            rw [fullMem_eq_k6Frame hscr_e] at hm_e
            rw [hRfr]
            exact k6Mem_to_amem hcone_e.k6_inv.shapes (sep_ac hm_e)
          clear hm_e
          dsimp only [Prod.fst]
          try (first | rw [hkptr_c0] | rw [hkptr_c0_nat])
          try rw [hqnext_c0]
          open scoped K6MemATactics K6PtrTactics in c0_hsteps_nogrp
          m6_to_group
          refine wp_join_group (ts := [i32])
            (fun (un_v, ()) mu => un_v = nv - ks_e.trl_end ∧
              (K6MemA L (L.kPtr c.pScratchBuf) (ks_e.putHdr .nv nv) ⋆ Rfr) mu)
            (fun _ (un_v, ()) mu ⟨hun_eq, hmu⟩ => by
              subst hun_eq
              have hnv_pos : 0 < nv.toNat := by omega
              have hnv_sub_bv : (nv - (1 : BitVec 32)).toNat = nv.toNat - 1 := by bv_omega
              have hnv_subMax : (nv - (1 : BitVec 32)).toNat < K6MemATactics.szV L := by
                dsimp only [K6MemATactics.szV]; rw [hnv_sub_bv]; omega
              open scoped K6MemATactics K6PtrTactics in m6_to_group
              refine wp_join_group (ts := [])
                (fun () mf =>
                  (K6MemA L (L.kPtr c.pScratchBuf)
                    ((((((ks_e.putHdr .nv nv).putHdr .unass (nv - ks_e.trl_end)).putHdr .qlast
                      (nv - 1#32)).putHdr .qsearch (nv - 1#32)).putHdr .qstamp nv).putArr .qnext
                        (nv.toNat - 1) 0xFFFFFFFF#32) ⋆ Rfr) mf)
                (fun _ () mf hmf => by
                  m6_steps
                  rw [hRfr] at hmf
                  exact m8_cone_exit_post hdw hcap hL_len hL_mv hlen_e hag_e hcone_e hmf hQ)
                (fun _ hJ_nv0 => by
                  m6_split
                  · c0_hsteps
                    try rw [hqnext_c0]
                    open scoped K6MemATactics K6PtrTactics in c0_hsteps!
                    rw [hnv_sub_bv, show (1 : BitVec 32) = 1#32 from rfl,
                      show (4294967295 : BitVec 32) = 0xFFFFFFFF#32 from rfl] at hm
                    exact hJ_nv0 () _ hm
                  · exfalso; have : nv = 0#32 := by bv_omega
                    have h0 := congrArg BitVec.toNat this; simp at h0; omega))
            (fun _ hJ_ter => by
              m6_split
              · m6_steps; exact hJ_ter (nv - ks_e.trl_end, ()) _ ⟨rfl, by assumption⟩
              · exfalso
                have hgt : nv.toNat < ks_e.trl_end.toNat := by bv_omega
                omega))
        (fun _ hJ_ex => by
          clear hQ hInit hMaxV
          m6_split; rotate_left
          · m6_steps; exact hJ_ex () mo ⟨st, hlen_st, hag_st, hcone_st, hmo⟩
          have hqi_lt : qi.toNat < nv.toNat := hc
          m6_split; rotate_left
          · m6_steps; exact hJ_ex () mo ⟨st, hlen_st, hag_st, hcone_st, hmo⟩
          have hdep_lt : depth.toNat < 2 := hc
          m6_split
          · m6_steps; exact hJ_ex () mo ⟨st, hlen_st, hag_st, hcone_st, hmo⟩
          have hlim_f : lim = false := by cases lim <;> simp at hc ⊢
          m6_split; rotate_left
          · m6_steps; exact hJ_ex () mo ⟨st, hlen_st, hag_st, hcone_st, hmo⟩
          have hnc_lt : nc.toNat < L.maxOrig := by
            have : nc.toNat < 1024 := hc
            unfold K6Layout.maxOrig; omega
          have hdep1 : (depth + 1#32).toNat = depth.toNat + 1 :=
            m6_bv32_add1 (by omega)
          obtain ⟨layer_end, hle_def⟩ : ∃ layer_end : BitVec 32, layer_end = nv := ⟨_, rfl⟩
          -- Layer loop: `while (qi < layer_end && !limit_reached && nc < max_orig)`
          m6_to_group
          refine wp_loop_inv (ts := [i32, i32, i32, .bool])
            (fun (nv_l, nc_l, qi_l, lim_l, ()) ml =>
              qi_l.toNat ≤ layer_end.toNat ∧ layer_end.toNat ≤ nv_l.toNat ∧ ∃ st_l : FullState,
                st_l.LengthsOk c ∧ AgreesExcept m8ConeMask s st_l ∧
                M8ConeInv F_cur L st_l nv_l.toNat nc_l.toNat ∧ (FullMem c st_l ⋆ R) ml)
            (fun (_, _, qi_l, _, ()) _ => layer_end.toNat - qi_l.toNat)
            (fun _ hJ_in => by
              m6_steps
              exact hJ_in (nv, nc, qi, lim, ()) mo
                ⟨hle_def ▸ hqi_le, hle_def ▸ le_refl _, st, hlen_st, hag_st, hcone_st, hmo⟩)
            (fun _ (nv_l, nc_l, qi_l, lim_l, ()) ml
                ⟨hqi_l_le, hle_nv_l, st_l, hlen_l, hag_l, hcone_l, hml⟩ hJ_in => by
              clear hJ_ex hmo hlen_st hag_st hcone_st
              m6_split; rotate_left
              · m6_steps
                exact hJ_out (nv_l, nc_l, qi_l, depth + 1#32, lim_l, ()) ml
                  (by dsimp only; exact m6_nat_sub1_lt hdep_lt hdep1)
                  ⟨Nat.le_trans hqi_l_le hle_nv_l, by rw [hdep1]; exact hdep_lt, st_l,
                    hlen_l, hag_l, hcone_l, hml⟩
              have hqi_l_lt : qi_l.toNat < layer_end.toNat := hle_def ▸ hc
              m6_split
              · m6_steps
                exact hJ_out (nv_l, nc_l, qi_l, depth + 1#32, lim_l, ()) ml
                  (by dsimp only; exact m6_nat_sub1_lt hdep_lt hdep1)
                  ⟨Nat.le_trans hqi_l_le hle_nv_l, by rw [hdep1]; exact hdep_lt, st_l,
                    hlen_l, hag_l, hcone_l, hml⟩
              m6_split; rotate_left
              · m6_steps
                exact hJ_out (nv_l, nc_l, qi_l, depth + 1#32, lim_l, ()) ml
                  (by dsimp only; exact m6_nat_sub1_lt hdep_lt hdep1)
                  ⟨Nat.le_trans hqi_l_le hle_nv_l, by rw [hdep1]; exact hdep_lt, st_l,
                    hlen_l, hag_l, hcone_l, hml⟩
              clear hle_def
              have hwk_l := hlen_l.scratch_ok.work_stk1_len
              have htm_l := hlen_l.scratch_ok.tarjan_mark_len
              have hnv_l_max := hcone_l.nv_leMax
              have hqi_z : (BitVec.setWidth 64 qi_l).toNat = qi_l.toNat := bv_c0_zext32_64 qi_l
              have hqi_ws : (BitVec.setWidth 64 qi_l).toNat < st_l.scratch.work_stk1.length := by
                have := hcone_l.nv_le_cv; have := hlen_l.core_ok.cur_vars_le
                rw [hqi_z, hwk_l]; omega
              obtain ⟨cv, hcv_def⟩ : ∃ cv : BitVec 32,
                  cv = st_l.scratch.work_stk1[(BitVec.setWidth 64 qi_l).toNat]'hqi_ws := ⟨_, rfl⟩
              have hwk_qi : st_l.scratch.work_stk1[qi_l.toNat]?.getD 0#32 = cv := by
                rw [hcv_def, List.getElem?_eq_getElem (by rw [hwk_l]; omega), Option.getD_some]
                exact m6_list_getElem_congr hqi_z.symm _ _
              have hcv_lt_s : cv.toNat < s.core.cur_vars := by
                have hf := (hcone_l.fwd qi_l.toNat (by omega)).1
                rw [hwk_qi, m8_hag_cur_vars hag_l] at hf; exact hf
              have hcv_idx : st_l.scratch.tarjan_mark[cv.toNat]?.getD 0#32 =
                  BitVec.ofNat 32 (qi_l.toNat + 1) := by
                have hf := (hcone_l.fwd qi_l.toNat (by omega)).2
                rw [hwk_qi] at hf; exact hf
              have hcv_tmk : (BitVec.setWidth 64 cv).toNat < st_l.scratch.tarjan_mark.length := by
                rw [htm_l, bv_c0_zext32_64]; omega
              have hqi1 : (qi_l + 1#32).toNat = qi_l.toNat + 1 :=
                m6_bv32_add1 (by omega)
              m6_steps
              have hcur_tmk : st_l.scratch.tarjan_mark[(BitVec.setWidth 64 cv).toNat]'hcv_tmk =
                  BitVec.ofNat 32 (qi_l.toNat + 1) := by
                rw [← Option.getD_some (a :=
                    st_l.scratch.tarjan_mark[(BitVec.setWidth 64 cv).toNat]'hcv_tmk),
                  ← List.getElem?_eq_getElem hcv_tmk, bv_c0_zext32_64, hcv_idx]
              have hmap_c : ((st_l.scratch.tarjan_mark[(BitVec.setWidth 64 cv).toNat]'hcv_tmk) -
                  1#32) = qi_l := by
                rw [hcur_tmk]; exact m6_bv32_ofNat_add1_sub1 qi_l
              have hcv_qi : ∀ (h : qi_l.toNat < st_l.scratch.work_stk1.length),
                  st_l.scratch.work_stk1[qi_l.toNat]'h = cv := fun h => by
                rw [hcv_def]; exact m6_list_getElem_congr hqi_z.symm h hqi_ws
              have hqi_ws0 : qi_l.toNat < st_l.scratch.work_stk1.length := by
                have h1 := hcone_l.nv_le_cv
                have h2 := m8_hag_cur_vars hag_l
                rw [hwk_l]; omega
              have hcv_qi0 : st_l.scratch.work_stk1[qi_l.toNat]'hqi_ws0 = cv := hcv_qi hqi_ws0
              -- Pass 1: Binary `pol` loop `while (pol < 2u && !limit_reached && nc < max_orig)`
              m6_to_group
              refine wp_loop_inv (ts := [i32, i32, .bool, i32])
                (fun (nv_p, nc_p, _lim_p, pol, ()) mp =>
                  pol.toNat ≤ 2 ∧ layer_end.toNat ≤ nv_p.toNat ∧ ∃ st_p : FullState,
                    M8ConeBase F_cur L c s cv qi_l nv_p.toNat nc_p.toNat st_p ∧
                    (FullMem c st_p ⋆ R) mp)
                (fun (_, _, _, pol, ()) _ => 2 - pol.toNat)
                (fun _ hJ_bpol => by
                  m6_steps
                  exact hJ_bpol (nv_l, nc_l, lim_l, 0#32, ()) ml
                    ⟨Nat.zero_le _, hle_nv_l, st_l,
                     ⟨hlen_l, hag_l, hcone_l, hcv_idx, by rw [hwk_qi]⟩, hml⟩)
                (fun _ (nv_p, nc_p, lim_p, pol, ()) mp
                    ⟨hpol_le, hle_nv_p, st_p, hb_p, hmp⟩ hJ_bpol => by
                  m6_to_group
                  refine wp_join_group (ts := [])
                    (fun () mp_ex => layer_end.toNat ≤ nv_p.toNat ∧ ∃ st_p2 : FullState,
                      M8ConeBase F_cur L c s cv qi_l nv_p.toNat nc_p.toNat st_p2 ∧
                      (FullMem c st_p2 ⋆ R) mp_ex)
                    (fun _ () mp_ex ⟨hle_nv2, st_p2, hb_p2, hm2⟩ => by
                      -- Pass 2: Long `pol` loop `while (pol < 2u && !limit_reached && ...)`
                      clear hJ_bpol hmp hpol_le hle_nv_p hb_p hJ_out hm_shl1 hqnext_c0 hdw hroot
                        htmk hcur_tmk hcv_idx hle_nv_l hlen_l hag_l hcone_l hmv_c0
                        hmv_bounds hmv64_lt hdep1 hdep_lt hlim_f hqi_lt hqi_le hdep_le hnc_lt
                      m6_steps
                      refine wp_loop_inv (ts := [i32, i32, .bool, i32])
                        (fun (nv_q, nc_q, _lim_q, pol_q, ()) mq =>
                          pol_q.toNat ≤ 2 ∧ layer_end.toNat ≤ nv_q.toNat ∧ ∃ st_q : FullState,
                            M8ConeBase F_cur L c s cv qi_l nv_q.toNat nc_q.toNat st_q ∧
                            (FullMem c st_q ⋆ R) mq)
                        (fun (_, _, _, pol_q, ()) _ => 2 - pol_q.toNat)
                        (fun _ hJ_lpol => by
                          m6_steps
                          exact hJ_lpol (nv_p, nc_p, lim_p, 0#32, ()) mp_ex
                            ⟨Nat.zero_le _, hle_nv2, st_p2, hb_p2, hm2⟩)
                        (fun _ (nv_q, nc_q, lim_q, pol_q, ()) mq
                            ⟨hpolq_le, hle_nv_q, st_q, hb_q, hmq⟩ hJ_lpol => by
                          m6_split; rotate_left
                          · m6_steps
                            exact hJ_in (nv_q, nc_q, qi_l + 1#32, lim_q, ()) mq
                              (by dsimp only; rw [hqi1]; exact m6_nat_sub1_lt hqi_l_lt rfl)
                              ⟨by rw [hqi1]; exact hqi_l_lt, hle_nv_q, st_q,
                               hb_q.hlen, hb_q.hag, hb_q.hcone, hmq⟩
                          have hpolq_lt : pol_q.toNat < 2 := hc
                          m6_split
                          · m6_steps
                            exact hJ_in (nv_q, nc_q, qi_l + 1#32, lim_q, ()) mq
                              (by dsimp only; rw [hqi1]; exact m6_nat_sub1_lt hqi_l_lt rfl)
                              ⟨by rw [hqi1]; exact hqi_l_lt, hle_nv_q, st_q,
                               hb_q.hlen, hb_q.hag, hb_q.hcone, hmq⟩
                          m6_split; rotate_left
                          · m6_steps
                            exact hJ_in (nv_q, nc_q, qi_l + 1#32, lim_q, ()) mq
                              (by dsimp only; rw [hqi1]; exact m6_nat_sub1_lt hqi_l_lt rfl)
                              ⟨by rw [hqi1]; exact hqi_l_lt, hle_nv_q, st_q,
                               hb_q.hlen, hb_q.hag, hb_q.hcone, hmq⟩
                          have hncq_lt : nc_q.toNat < L.maxOrig := by
                            have : nc_q.toNat < 1024 := hc
                            unfold K6Layout.maxOrig; omega
                          obtain ⟨lit, hlit_def⟩ : ∃ lit : BitVec 32,
                              lit = ((cv <<< (1 : Nat)) ||| pol_q) := ⟨_, rfl⟩
                          have hlit_eq : lit.toNat = 2 * cv.toNat + pol_q.toNat := by
                            rw [hlit_def]
                            exact m6_bv32_shl1_or_pol cv pol_q (by omega) hpolq_lt
                          have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by omega
                          obtain ⟨hwo, hwsz, hend_eq, hwo_le, hrem_eq, hend_ws, h2l_mod, h2l1_mod⟩
                            := m8_cone_wvec_facts hlen hb_q.hlen hb_q.hag hdwatches hlit_lt
                          have hwvec_q := hb_q.hlen.core_ok.wvec_len
                          have h2l_bd : (BitVec.setWidth 64 lit <<< (1 : Nat)).toNat <
                              st_q.core.wvec.length := by
                            rw [hwvec_q, m6_bv64_shl1]; omega
                          have h2l1_bd : ((BitVec.setWidth 64 lit <<< (1 : Nat)) + 1#64).toNat <
                              st_q.core.wvec.length := by
                            rw [hwvec_q, m6_bv64_shl1_add1]; omega
                          obtain ⟨wOff, hwOff_def⟩ : ∃ wOff : BitVec 64,
                              wOff = (st_q.core.wvec[(BitVec.setWidth 64 lit <<<
                                (1 : Nat)).toNat]'h2l_bd).setWidth 64 := ⟨_, rfl⟩
                          obtain ⟨wSz, hwSz_def⟩ : ∃ wSz : BitVec 64,
                              wSz = (st_q.core.wvec[((BitVec.setWidth 64 lit <<< (1 : Nat)) +
                                1#64).toNat]'h2l1_bd).setWidth 64 := ⟨_, rfl⟩
                          obtain ⟨wEnd, hwEnd⟩ : ∃ wEnd : BitVec 64, wEnd = wOff + wSz := ⟨_, rfl⟩
                          have hend_ws : wEnd.toNat ≤ s.core.wstk.length := by
                            rw [hwEnd, hwOff_def, hwSz_def]; exact hend_ws
                          have hwOff_n : wOff.toNat = fullWatchOffCore s.core lit.toNat := by
                            rw [hwOff_def]; exact hwo
                          have hwSz_n : wSz.toNat = fullWatchSizeCore s.core lit.toNat := by
                            rw [hwSz_def]; exact hwsz
                          have hend_n : wEnd.toNat =
                              fullWatchOffCore s.core lit.toNat +
                                fullWatchSizeCore s.core lit.toNat := by
                            rw [hwEnd, hwOff_def, hwSz_def]; exact hend_eq
                          have hpol1 : (pol_q + 1#32).toNat = pol_q.toNat + 1 :=
                            m6_bv32_add1 (Nat.lt_trans hpolq_lt (by decide))
                          have hwv0_eq :
                              ∀ (h : (2 * lit.toNat) % 2 ^ 64 < st_q.core.wvec.length),
                              st_q.core.wvec[(2 * lit.toNat) % 2 ^ 64]'h =
                                st_q.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat)).toNat]'
                                  h2l_bd := fun h => m6_list_getElem_congr h2l_mod h _
                          have hwv1_eq :
                              ∀ (h : (2 * lit.toNat + (1#64).toNat) % 2 ^ 64 <
                                  st_q.core.wvec.length),
                                st_q.core.wvec[(2 * lit.toNat +
                                  (1#64).toNat) % 2 ^ 64]'h =
                                  st_q.core.wvec[((BitVec.setWidth 64 lit <<< (1 : Nat)) +
                                    1#64).toNat]'h2l1_bd := fun h =>
                            m6_list_getElem_congr
                              (by rw [show (1#64).toNat = 1 from rfl]; exact h2l1_mod) h _
                          have h2l_bd_ws :
                              (BitVec.setWidth 64 ((st_l.scratch.work_stk1[
                                (BitVec.setWidth 64 qi_l).toNat]'hqi_ws <<< (1 : Nat)) |||
                                pol_q) <<< (1 : Nat)).toNat < st_q.core.wvec.length := by
                            rw [← hcv_def, ← hlit_def]; exact h2l_bd
                          have h2l1_bd_ws :
                              ((BitVec.setWidth 64 ((st_l.scratch.work_stk1[
                                (BitVec.setWidth 64 qi_l).toNat]'hqi_ws <<< (1 : Nat)) |||
                                pol_q) <<< (1 : Nat)) + 1#64).toNat < st_q.core.wvec.length := by
                            rw [← hcv_def, ← hlit_def]; exact h2l1_bd
                          have hw0_ws :
                              ∀ (h : (BitVec.setWidth 64 ((st_l.scratch.work_stk1[
                                  (BitVec.setWidth 64 qi_l).toNat]'hqi_ws <<< (1 : Nat)) |||
                                  pol_q) <<< (1 : Nat)).toNat < st_q.core.wvec.length),
                                (st_q.core.wvec[(BitVec.setWidth 64 ((st_l.scratch.work_stk1[
                                  (BitVec.setWidth 64 qi_l).toNat]'hqi_ws <<< (1 : Nat)) |||
                                  pol_q) <<< (1 : Nat)).toNat]'h).setWidth 64 = wOff := fun h => by
                            rw [hwOff_def]; congr 1
                            exact m6_list_getElem_congr (by rw [← hcv_def, ← hlit_def]) h h2l_bd
                          have hw1_ws :
                              ∀ (h : ((BitVec.setWidth 64 ((st_l.scratch.work_stk1[
                                  (BitVec.setWidth 64 qi_l).toNat]'hqi_ws <<< (1 : Nat)) |||
                                  pol_q) <<< (1 : Nat)) + 1#64).toNat < st_q.core.wvec.length),
                                (st_q.core.wvec[((BitVec.setWidth 64 ((st_l.scratch.work_stk1[
                                  (BitVec.setWidth 64 qi_l).toNat]'hqi_ws <<< (1 : Nat)) |||
                                  pol_q) <<< (1 : Nat)) + 1#64).toNat]'h).setWidth 64 =
                                  wSz := fun h => by
                            rw [hwSz_def]; congr 1
                            exact m6_list_getElem_congr (by rw [← hcv_def, ← hlit_def]) h h2l1_bd
                          have hw0_eq_nat : ∀ (h : (BitVec.setWidth 64 lit <<< (1 : Nat)).toNat <
                                st_q.core.wvec.length),
                              (st_q.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat)).toNat]'h).toNat
                                = wOff.toNat := fun h => by rw [hwOff_def, bv_c0_zext32_64]
                          have hw1_eq_nat : ∀ (h : ((BitVec.setWidth 64 lit <<< (1 : Nat)) +
                                1#64).toNat < st_q.core.wvec.length),
                              (st_q.core.wvec[((BitVec.setWidth 64 lit <<< (1 : Nat)) +
                                1#64).toNat]'h).toNat = wSz.toNat := fun h => by
                            rw [hwSz_def, bv_c0_zext32_64]
                          -- Long watch loop join (`pol_q = pol_q + 1u`)
                          m6_to_group
                          refine wp_join_group (ts := [i32, i32, .bool, i64])
                            (fun (nv_e, nc_e, _lim_e, _, ()) m_we =>
                              layer_end.toNat ≤ nv_e.toNat ∧ ∃ st_we : FullState,
                                M8ConeBase F_cur L c s cv qi_l nv_e.toNat nc_e.toNat st_we ∧
                                (FullMem c st_we ⋆ R) m_we)
                            (fun _ (nv_e, nc_e, lim_e, _, ()) m_we ⟨hnve, st_we, hb_e, hm_e⟩ => by
                              m6_steps
                              exact hJ_lpol (nv_e, nc_e, lim_e, pol_q + 1#32, ()) m_we
                                (by dsimp only; rw [hpol1]; exact m6_nat_sub1_lt hpolq_lt rfl)
                                ⟨by rw [hpol1]; exact hpolq_lt, hnve, st_we, hb_e, hm_e⟩)
                            (fun _ hJ_we => by
                              m6_to_group
                              refine wp_loop_inv (ts := [i32, i32, .bool, i64])
                                (fun (nv_w, nc_w, _lim_w, p, ()) mw =>
                                  p.toNat ≤ wEnd.toNat ∧ layer_end.toNat ≤ nv_w.toNat ∧
                                  DenseWatchSliceOk F_cur s.core lit.toNat p.toNat
                                    (wEnd.toNat - p.toNat) ∧
                                  ∃ st_w : FullState,
                                    M8ConeBase F_cur L c s cv qi_l nv_w.toNat nc_w.toNat st_w ∧
                                    (FullMem c st_w ⋆ R) mw)
                                (fun (_, _, _, p, ()) _ => wEnd.toNat - p.toNat)
                                (fun _ hJ_w => by
                                  m6_steps
                                  refine hJ_w (nv_q, nc_q, lim_q, _, ()) mq
                                    ⟨?_, hle_nv_q, ?_, st_q, hb_q, hmq⟩
                                  · try rw [hw0_ws]
                                    rw [hwEnd, hwOff_def, hwSz_def]; exact hwo_le
                                  · try rw [hw0_ws]
                                    rw [hwEnd, hwOff_def, hwSz_def, hrem_eq, hwo]
                                    exact hdwatches.slices lit.toNat hlit_lt)
                                (fun J_w (nv_w, nc_w, lim_w, p, ()) mw
                                    ⟨hp_le, hnv_w_mono, hslice, st_w, hb_w, hmw⟩ hJ_w => by
                                  clear hJ_lpol hmq hpol1 hle_nv2 hb_p2 hm2 hpolq_le hle_nv_q
                                    hncq_lt hpolq_lt hwo hwsz hend_eq hwo_le hrem_eq
                                    hwOff_n hwSz_n
                                  m6_split; rotate_left
                                  · m6_steps; exact hJ_we (nv_w, nc_w, lim_w, p, ()) mw
                                      ⟨hnv_w_mono, st_w, hb_w, hmw⟩
                                  have hp_lt : p.toNat < wEnd.toNat := by
                                    simp only [hcv_qi0] at hc
                                    repeat rw [m6_getElem_eq_getD st_q.core.wvec (d := 0#32)] at hc
                                    rw [m8_hag_wvec hb_q.hag] at hc
                                    change p.toNat <
                                      ((s.core.wvec[2 * (cv <<< (1 : Nat) ||| pol_q).toNat %
                                          2 ^ 64]?.getD 0#32).toNat +
                                        (s.core.wvec[(2 * (cv <<< (1 : Nat) ||| pol_q).toNat +
                                            1) % 2 ^ 64]?.getD 0#32).toNat) % 2 ^ 64 at hc
                                    rw [← hlit_def,
                                      show 2 * lit.toNat % 2 ^ 64 = 2 * lit.toNat from
                                        Nat.mod_eq_of_lt (by omega),
                                      show (2 * lit.toNat + 1) % 2 ^ 64 = 2 * lit.toNat + 1 from
                                        Nat.mod_eq_of_lt (by omega)] at hc
                                    change p.toNat <
                                      (fullWatchOffCore s.core lit.toNat +
                                        fullWatchSizeCore s.core lit.toNat) % 2 ^ 64 at hc
                                    have hw_lt : wEnd.toNat < 2 ^ 64 := wEnd.isLt
                                    rw [← hend_n, Nat.mod_eq_of_lt (by omega)] at hc
                                    exact hc
                                  m6_split
                                  · m6_steps; exact hJ_we (nv_w, nc_w, lim_w, p, ()) mw
                                      ⟨hnv_w_mono, st_w, hb_w, hmw⟩
                                  m6_split; rotate_left
                                  · m6_steps; exact hJ_we (nv_w, nc_w, lim_w, p, ()) mw
                                      ⟨hnv_w_mono, st_w, hb_w, hmw⟩
                                  have hncw_lt : nc_w.toNat < L.maxOrig := by
                                    have : nc_w.toNat < 1024 := hc
                                    unfold K6Layout.maxOrig; omega
                                  have hwstk_eq : st_w.core.wstk = s.core.wstk :=
                                    m8_hag_wstk hb_w.hag
                                  have hcv_w : st_w.core.cur_vars = s.core.cur_vars :=
                                    m8_hag_cur_vars hb_w.hag
                                  have hp_wstk_w : p.toNat < st_w.core.wstk.length :=
                                    m8_cone_hp_wstk hwstk_eq hp_lt hend_ws
                                  have hp1 : (p + 1#64).toNat = p.toNat + 1 :=
                                    m6_bv64_add1 (by omega)
                                  obtain ⟨w0, hw0_def⟩ : ∃ w0 : BitVec 32,
                                      w0 = st_w.core.wstk[p.toNat]'hp_wstk_w := ⟨_, rfl⟩
                                  have hw0_s : s.core.wstk[p.toNat]? = some w0 := by
                                    rw [hw0_def, List.getElem?_eq_getElem (hwstk_eq ▸ hp_wstk_w)]
                                    exact congrArg some (by simp [hwstk_eq])
                                  m6_split
                                  · have hbin : (w0 &&& 0x80000000#32) ≠ 0#32 := by
                                      rw [hw0_def]; exact hc
                                    obtain ⟨_, _, _, hslice1⟩ :=
                                      m6_denseSlice_step_bin hslice (Nat.sub_pos_of_lt hp_lt)
                                        hw0_s hbin
                                    m6_steps
                                    exact hJ_w (nv_w, nc_w, lim_w, p + 1#64, ()) mw
                                      (by dsimp only; rw [hp1]; exact m6_nat_sub1_lt hp_lt rfl)
                                      ⟨by rw [hp1]; exact hp_lt, hnv_w_mono,
                                        by rw [hp1, m8_cone_sub_sub_eq]; exact hslice1,
                                        st_w, hb_w, hmw⟩
                                  · have hocc : (w0 &&& 0x80000000#32) = 0#32 := by
                                      rw [hw0_def]; exact hc
                                    obtain ⟨hrem2, _, cr, hcr_s, hcr_lt, hcr_ref, hslice2⟩ :=
                                      m6_denseSlice_step_occ hslice (Nat.sub_pos_of_lt hp_lt)
                                        hw0_s hocc
                                    m6_split
                                    · exfalso
                                      have hge : wEnd.toNat ≤ (p + 1#64).toNat := by
                                        simp only [hcv_qi0] at hc
                                        repeat rw [m6_getElem_eq_getD st_q.core.wvec
                                          (d := 0#32)] at hc
                                        rw [m8_hag_wvec hb_q.hag] at hc
                                        change ((s.core.wvec[2 * (cv <<< (1 : Nat) |||
                                            pol_q).toNat % 2 ^ 64]?.getD 0#32).toNat +
                                          (s.core.wvec[(2 * (cv <<< (1 : Nat) ||| pol_q).toNat +
                                              1) % 2 ^ 64]?.getD 0#32).toNat) % 2 ^ 64 ≤
                                          (p.toNat + 1) % 2 ^ 64 at hc
                                        rw [← hlit_def,
                                          show 2 * lit.toNat % 2 ^ 64 = 2 * lit.toNat from
                                            Nat.mod_eq_of_lt (by omega),
                                          show (2 * lit.toNat + 1) % 2 ^ 64 = 2 * lit.toNat + 1 from
                                            Nat.mod_eq_of_lt (by omega)] at hc
                                        change (fullWatchOffCore s.core lit.toNat +
                                          fullWatchSizeCore s.core lit.toNat) % 2 ^ 64 ≤
                                          (p.toNat + 1) % 2 ^ 64 at hc
                                        have hw_lt : wEnd.toNat < 2 ^ 64 := wEnd.isLt
                                        rw [← hend_n, Nat.mod_eq_of_lt (by omega), ← hp1,
                                          Nat.mod_eq_of_lt (p + 1#64).isLt] at hc
                                        exact hc
                                      omega
                                    have hp2 : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by
                                      rw [m6_bv64_add1 (by rw [hp1]; omega), hp1]
                                    have hp2_le : (p + 1#64 + 1#64).toNat ≤ wEnd.toNat := by
                                      rw [hp2]; omega
                                    have har_s := hlen.core_ok.arena_len_arr
                                    have hcr_wf := hw.arena.refs_wf cr.toNat hcr_ref
                                    have hacap_lt := c.harena; unfold dimacsBound at hacap_lt
                                    have hal_le := hlen.core_ok.arena_len_le
                                    have hp1_lt_end : (p + 1#64).toNat < wEnd.toNat := by
                                      rw [hp1]; omega
                                    have hp1_wstk : (p + 1#64).toNat < st_w.core.wstk.length :=
                                      m8_cone_hp_wstk hwstk_eq hp1_lt_end hend_ws
                                    have hcr_eq : st_w.core.wstk[p.toNat + 1]'(hp1 ▸ hp1_wstk) =
                                        cr := by
                                      have hcr_w : st_w.core.wstk[p.toNat + 1]? = some cr :=
                                        hwstk_eq ▸ hcr_s
                                      rw [List.getElem?_eq_getElem (hp1 ▸ hp1_wstk)] at hcr_w
                                      exact Option.some.inj hcr_w
                                    have hcr_idx :
                                        ∀ {j : Nat} (hj : j < st_w.core.wstk.length),
                                          j = p.toNat + 1 → st_w.core.wstk[j]'hj = cr :=
                                      fun _ hij => by subst hij; exact hcr_eq
                                    have hcr2_lt : (BitVec.setWidth 64 cr + 2#64).toNat =
                                        cr.toNat + 2 := by
                                      simp only [BitVec.toNat_add, bv_c0_zext32_64,
                                        show (2#64 : BitVec 64).toNat = 2 from rfl]; omega
                                    have har_eq : st_w.core.arena = s.core.arena :=
                                      m8_hag_arena hb_w.hag
                                    have har_cr_bd : cr.toNat < st_w.core.arena.length := by
                                      rw [har_eq, har_s]; omega
                                    have har_cr2_bd : (BitVec.setWidth 64 cr + 2#64).toNat <
                                        st_w.core.arena.length := by
                                      rw [har_eq, har_s, hcr2_lt]; omega
                                    obtain ⟨sz, hsz_def⟩ : ∃ sz : BitVec 32,
                                        sz = st_w.core.arena[(BitVec.setWidth 64 cr + 2#64).toNat]'
                                          har_cr2_bd := ⟨_, rfl⟩
                                    have har_cr_idx :
                                        ∀ {k : Nat} (hk : k < st_w.core.arena.length), k = cr.toNat
                                          → st_w.core.arena[k]'hk =
                                            st_w.core.arena[cr.toNat]'har_cr_bd :=
                                      fun _ hkeq => Option.some.inj (by subst hkeq; rfl)
                                    have har_sz_idx :
                                        ∀ {k : Nat} (hk : k < st_w.core.arena.length),
                                          k = (BitVec.setWidth 64 cr + 2#64).toNat →
                                          st_w.core.arena[k]'hk = sz :=
                                      fun _ hkeq => Option.some.inj (by subst hkeq; rw [hsz_def])
                                    have hsz_core : sz.toNat =
                                        fullArenaClauseSizeCore s.core cr.toNat := by
                                      unfold fullArenaClauseSizeCore; rw [hsz_def]
                                      rw [List.getElem?_eq_getElem (by rw [har_s]; omega),
                                        Option.getD_some]
                                      simp only [har_eq, hcr2_lt]
                                    have hstep_occ : ∀ (nv_x nc_x : BitVec 32) (lim_x : Bool)
                                        (st_x : FullState) (mx : Mem 64),
                                        layer_end.toNat ≤ nv_x.toNat →
                                        M8ConeBase F_cur L c s cv qi_l nv_x.toNat nc_x.toNat st_x →
                                        (FullMem c st_x ⋆ R) mx →
                                        J_w (nv_x, nc_x, lim_x, p + 1#64 + 1#64, ()) mx :=
                                      fun nv_x nc_x lim_x st_x mx hnvx hbx hmx =>
                                        hJ_w (nv_x, nc_x, lim_x, p + 1#64 + 1#64, ()) mx
                                          (by dsimp only; exact m6_nat_sub2_lt hp_lt hp2_le hp2)
                                          ⟨hp2_le, hnvx,
                                            by rw [hp2, m8_cone_sub_sub_eq]; exact hslice2,
                                            st_x, hbx, hmx⟩
                                    have hocc_done : J_w (nv_w, nc_w, lim_w, p + 1#64 + 1#64, ())
                                      mw := hstep_occ nv_w nc_w lim_w st_w mw hnv_w_mono hb_w hmw
                                    have hp_mod :
                                        (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
                                          p.toNat + 1 :=
                                      m8_cone_wstk_p_toNat_eq p (by omega)
                                    have hcr_w_p1 : st_w.core.wstk[(p + 1#64).toNat]'hp1_wstk =
                                        cr :=
                                      hcr_idx _ hp1
                                    have har_cr_bd' :
                                        (BitVec.setWidth 64
                                          (st_w.core.wstk[(p + 1#64).toNat]'hp1_wstk)).toNat <
                                          st_w.core.arena.length := by
                                      rw [hcr_w_p1, bv_c0_zext32_64]; exact har_cr_bd
                                    m6_split; · m6_steps; exact hocc_done
                                    have har_cr2_bd' :
                                        (BitVec.setWidth 64
                                          (st_w.core.wstk[(p + 1#64).toNat]'hp1_wstk) +
                                            2#64).toNat < st_w.core.arena.length := by
                                      rw [hcr_w_p1]; exact har_cr2_bd
                                    m6_split; · m6_steps; exact hocc_done
                                    have hgr0 : (st_w.core.arena[cr.toNat]'har_cr_bd &&&
                                        (0x00080000#32 ||| 0x00400000#32)) = 0#32 := by
                                      rw [har_cr_idx] at hc
                                      · exact hc
                                      · rw [hcr_idx _ hp_mod]
                                    m6_split; · m6_steps; exact hocc_done
                                    have hsz_ge3 : 3 ≤ sz.toNat := by
                                      rw [har_sz_idx] at hc
                                      · exact Nat.le_of_not_lt hc
                                      · rw [hcr_idx]
                                        · rw [hcr2_lt,
                                            show BitVec.toNat (2 : BitVec 64) =
                                                        2 from rfl,
                                            Nat.mod_eq_of_lt (by omega)]
                                        · exact hp_mod
                                    m6_split; · m6_steps; exact hocc_done
                                    obtain ⟨hng, hcr_sz_le, hsz_cv, hcr3_bd⟩ :=
                                      m6_cone_occ_hdr_ok hlen hw hnd har_eq hcr_ref hsz_core hgr0
                                    have hsz_ar :
                                        (s.core.arena[cr.toNat + 2]?.getD 0#32).toNat = sz.toNat :=
                                      hsz_core.symm
                                    have hnd_cl : ((fullArenaClauseLits s cr.toNat).map (· /
                                      2)).Nodup := hnd cr.toNat hcr_ref hng
                                    obtain ⟨saved_nv, hsav_eq⟩ : ∃ saved_nv : BitVec 32,
                                        saved_nv = nv_w := ⟨_, rfl⟩
                                    obtain ⟨scr_sav, hscr_sav_eq⟩ : ∃ scr_sav : List (BitVec 32),
                                        scr_sav = st_w.scratch.scratch_buf := ⟨_, rfl⟩
                                    have hsav_ge1 : 1 ≤ saved_nv.toNat :=
                                      hsav_eq ▸ hb_w.hcone.nv_ge1
                                    have hbdd_sav : K6LitsBounded saved_nv.toNat
                                        (k6StateOfScratch L scr_sav) :=
                                      hsav_eq ▸ hscr_sav_eq ▸ hb_w.hcone.k6_bdd
                                    have htrl_sav : ∀ l ∈ k6TrailLits (k6StateOfScratch L scr_sav),
                                        l < 2 * saved_nv.toNat :=
                                      hsav_eq ▸ hscr_sav_eq ▸ hb_w.hcone.k6_trl_bdd
                                    clear hslice hslice2 hw0_s hocc hwv0_eq hwv1_eq h2l_mod
                                      h2l1_mod hsz_def
                                    m6_to_group
                                    refine wp_join_group (ts := [i32, .bool, .bool, i32, i32])
                                      (fun (nv_e, _lim_e, drop_e, cnt_e, idx_e, ()) m_e =>
                                        ∃ st_e : FullState,
                                          M8ConeSavedBase F_cur L c s cv qi_l saved_nv
                                            st_w.scratch.work_stk1 scr_sav
                                            nv_e.toNat nc_w.toNat st_e
                                          ∧ (drop_e = false →
                                            idx_e.toNat = sz.toNat ∧ cnt_e.toNat ≤ idx_e.toNat ∧
                                            (∀ j < cnt_e.toNat,
                                              (st_e.core.tmp[j]?.getD 0#32).toNat <
                                                2 * nv_e.toNat) ∧
                                            (∀ i < idx_e.toNat,
                                              let l := (s.core.arena[cr.toNat + 3 + i]?.getD
                                                0#32).toNat
                                              s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨
                                              l ∈ (st_e.core.tmp.take cnt_e.toNat).map
                                                (fun x => m6ConeLift
                                                  st_e.scratch.work_stk1 x.toNat)) ∧
                                            (∀ j1 j2, j1 < cnt_e.toNat → j2 < cnt_e.toNat →
                                              j1 ≠ j2 →
                                              (st_e.core.tmp[j1]?.getD 0#32).toNat / 2 ≠
                                                (st_e.core.tmp[j2]?.getD 0#32).toNat / 2)) ∧
                                          (FullMem c st_e ⋆ R) m_e)
                                      (fun _ (nv_e, lim_e, drop_e, cnt_e, idx_e, ()) m_e
                                          ⟨st_e, hs_e, hndrop, hme⟩ => by
                                        m6_split
                                        · -- `drop = true`: rollback `while (nv > saved_nv)`
                                          m6_to_group
                                          refine wp_loop_inv (ts := [i32])
                                            (fun (nv_r, ()) mr =>
                                              nv_r.toNat ≤ nv_e.toNat ∧ ∃ st_r : FullState,
                                                M8ConeSavedBase F_cur L c s cv qi_l saved_nv
                                                  st_w.scratch.work_stk1 scr_sav nv_r.toNat
                                                  nc_w.toNat st_r ∧
                                                (FullMem c st_r ⋆ R) mr)
                                            (fun (nv_r, ()) _ => nv_r.toNat - saved_nv.toNat)
                                            (fun _ hJr => by
                                              m6_steps
                                              exact hJr (nv_e, ()) m_e
                                                ⟨le_refl _, st_e, hs_e, hme⟩)
                                            (fun _ (nv_r, ()) mr ⟨hle_e, st_r, hs_r, hmr⟩ hJr => by
                                              m6_split
                                              · have hsav_lt : saved_nv.toNat < nv_r.toNat := by
                                                  rw [hsav_eq]; exact hc
                                                obtain ⟨hnv1, hvr_lt, hstep⟩ :=
                                                  m8_coneBase_of_rollback_step hs_r hsav_ge1 hsav_lt
                                                    (by
                                                      rw [hsav_eq]
                                                      exact Nat.lt_of_lt_of_le
                                                        hqi_l_lt hnv_w_mono)
                                                    hbdd_sav htrl_sav
                                                obtain ⟨hvr_tmk_bd, hs'⟩ := hstep hvr_lt
                                                m6_steps
                                                refine hJr (nv_r - 1#32, ()) _
                                                  (by
                                                    dsimp only
                                                    exact m6_nat_sub_lo1_lt hsav_lt hnv1)
                                                  ⟨hnv1 ▸ le_trans (Nat.sub_le _ _) hle_e,
                                                    _, hs', ?_⟩
                                                try rw [m6_tmk_set_mod64] at hm
                                                exact m8_cone_rollback_mem_step _ hvr_lt
                                                  (m6_bv32_sub1_zext_toNat nv_r) hm
                                              · have hnv_le_sav : nv_r.toNat ≤ saved_nv.toNat := by
                                                  rw [hsav_eq]; exact Nat.le_of_not_lt hc
                                                m6_steps
                                                have hnv_eq : nv_r = saved_nv :=
                                                  BitVec.eq_of_toNat_eq
                                                    (Nat.le_antisymm hnv_le_sav hs_r.hsav_le)
                                                have hle_nv_r : layer_end.toNat ≤ nv_r.toNat := by
                                                  rw [hnv_eq, hsav_eq]; exact hnv_w_mono
                                                exact hstep_occ nv_r nc_w lim_e st_r mr
                                                  hle_nv_r (hnv_eq ▸ hs_r.toM8ConeBase) hmr)
                                        · -- `drop = false`: call `full_k6_add_clause`
                                          obtain ⟨hk_eq, hcnt_le, hlts_e, hcov_e, hnd_e⟩ :=
                                            hndrop (by cases drop_e <;> simp at hc ⊢)
                                          have hcnt_le_nv : cnt_e.toNat ≤ nv_e.toNat :=
                                            m6_cone_cnt_le_nv hlts_e hnd_e
                                          have hnv_e_max := hs_e.hcone.nv_leMax
                                          have hcnt_le28 : cnt_e.toNat < 2 ^ 28 := by omega
                                          have hcnt_tmp : cnt_e.toNat ≤ st_e.core.tmp.length := by
                                            rw [hs_e.hlen.core_ok.tmp_len_arr]
                                            exact Nat.le_trans hcnt_le_nv
                                              (Nat.le_trans hs_e.hcone.nv_le_cv (by
                                                rw [m8_hag_cur_vars hs_e.hag]; exact hcv_le))
                                          have hent_ke : (cnfOfClauses F_cur).EntailsClause
                                              (cnfClause ((st_e.core.tmp.take cnt_e.toNat).map
                                                (fun x => m6ConeLift
                                                  st_e.scratch.work_stk1 x.toNat))) := by
                                            refine m6_cone_clause_entails_filtered hw hcl0 hcr_ref
                                              hng fun l hl => ?_
                                            obtain ⟨i, hi, rfl⟩ :=
                                              (m6_arenaClauseLitsCore_mem_iff
                                                (by rw [hsz_ar]; exact hcr3_bd)).mp hl
                                            rw [hsz_ar] at hi
                                            exact hcov_e i (hk_eq.symm ▸ hi)
                                          m6_steps
                                          refine m8_cone_call_add_clause hAddCl
                                            (aSz := Arg.var cnt_e) rfl hL_len hL_mv hs_e.hlen
                                            hs_e.hag hs_e.hcone hncw_lt hcnt_le28 hcnt_tmp hlts_e
                                            hent_ke hme
                                            (fun ok st' m' hl' ha' hc' hfalse_scr ht_eq hw_eq hm'
                                              => by
                                              m6_split
                                              · have hic := (m8_cone_load_kptr_hdr hc' hm').1
                                                m6_to_group
                                                refine wp_join_group (ts := [.bool])
                                                  (fun (_lim', ()) m'' => m'' = m')
                                                  (fun _ (lim', ()) m'' hm'' => by
                                                    subst m''
                                                    m6_steps
                                                    exact hstep_occ nv_e (nc_w + 1#32) lim' st' m'
                                                      (Nat.le_trans hnv_w_mono
                                                        (hsav_eq ▸ hs_e.hsav_le))
                                                      ⟨hl', ha', by simpa only [hc, ↓reduceIte]
                                                        using hc', ht_eq ▸ hs_e.htmk,
                                                        hw_eq ▸ hs_e.hwk⟩
                                                      hm')
                                                  (fun _ hJ_inc => by
                                                    change wp _ _ _ _ _
                                                    c0_hsteps
                                                    dsimp only [Prod.fst]
                                                    try (first | rw [hkptr_c0] | rw [hkptr_c0_nat])
                                                    try rw [show (BitVec.ofNat (OfNat.ofNat 64)
                                                        (OfNat.ofNat 6) : BitVec 64) = 6#64 from rfl]
                                                    refine head_wp_load rfl hic ?_
                                                    m6_split
                                                    · m6_steps; exact hJ_inc (true, ()) m' rfl
                                                    · m6_steps; exact hJ_inc (lim_e, ()) m' rfl)
                                              · have hs'_saved : M8ConeSavedBase F_cur L c s cv qi_l
                                                    saved_nv st_w.scratch.work_stk1 scr_sav
                                                    nv_e.toNat nc_w.toNat st' :=
                                                  ⟨⟨hl', ha', by simpa only [hc, Bool.false_eq_true,
                                                      ↓reduceIte] using hc', ht_eq ▸ hs_e.htmk,
                                                      hw_eq ▸ hs_e.hwk⟩,
                                                    hs_e.hsav_le,
                                                    (hfalse_scr (by cases ok <;> simp at hc ⊢)
                                                      ).trans
                                                      hs_e.hscr,
                                                    hw_eq ▸ hs_e.hws⟩
                                                m6_to_group
                                                refine wp_loop_inv (ts := [i32])
                                                  (fun (nv_r, ()) mr =>
                                                    nv_r.toNat ≤ nv_e.toNat ∧ ∃ st_r : FullState,
                                                      M8ConeSavedBase F_cur L c s cv qi_l saved_nv
                                                        st_w.scratch.work_stk1 scr_sav nv_r.toNat
                                                        nc_w.toNat st_r ∧
                                                      (FullMem c st_r ⋆ R) mr)
                                                  (fun (nv_r, ()) _ => nv_r.toNat - saved_nv.toNat)
                                                  (fun _ hJr => by
                                                    m6_steps
                                                    exact hJr (nv_e, ()) m'
                                                      ⟨le_refl _, st', hs'_saved, hm'⟩)
                                                  (fun _ (nv_r, ()) mr ⟨hle_e, st_r, hs_r, hmr⟩
                                                      hJr => by
                                                    m6_split
                                                    · have hsav_lt :
                                                          saved_nv.toNat < nv_r.toNat := by
                                                        rw [hsav_eq]; exact hc
                                                      obtain ⟨hnv1, hvr_lt, hstep⟩ :=
                                                        m8_coneBase_of_rollback_step hs_r hsav_ge1
                                                          hsav_lt (by
                                                            rw [hsav_eq]
                                                            exact
                                                              Nat.lt_of_lt_of_le hqi_l_lt
                                                                hnv_w_mono)
                                                          hbdd_sav htrl_sav
                                                      obtain ⟨hvr_tmk_bd, hs'⟩ := hstep hvr_lt
                                                      m6_steps
                                                      refine hJr (nv_r - 1#32, ()) _
                                                        (by
                                                          dsimp only
                                                          exact m6_nat_sub_lo1_lt hsav_lt hnv1)
                                                        ⟨hnv1 ▸ le_trans (Nat.sub_le _ _) hle_e,
                                                          _, hs', ?_⟩
                                                      try rw [m6_tmk_set_mod64] at hm
                                                      exact m8_cone_rollback_mem_step _ hvr_lt
                                                        (m6_bv32_sub1_zext_toNat nv_r) hm
                                                    · have hnv_le_sav :
                                                          nv_r.toNat ≤ saved_nv.toNat := by
                                                        rw [hsav_eq]; exact Nat.le_of_not_lt hc
                                                      m6_steps
                                                      have hnv_eq : nv_r = saved_nv :=
                                                        BitVec.eq_of_toNat_eq
                                                          (Nat.le_antisymm hnv_le_sav hs_r.hsav_le)
                                                      have hle_nv_r :
                                                          layer_end.toNat ≤ nv_r.toNat := by
                                                        rw [hnv_eq, hsav_eq]; exact hnv_w_mono
                                                      exact hstep_occ nv_r nc_w true st_r mr
                                                        hle_nv_r (hnv_eq ▸ hs_r.toM8ConeBase) hmr)))
                                      (fun _ hJ_occ => by
                                        m6_to_group
                                        refine wp_loop_inv (ts := [i32, i32, i32])
                                          (fun (nv_k, cnt, idx, ()) mk =>
                                            idx.toNat ≤ sz.toNat ∧ cnt.toNat ≤ idx.toNat ∧
                                            ∃ st_k : FullState,
                                              M8ConeScanBase F_cur L c s cv qi_l saved_nv
                                                st_w.scratch.work_stk1 scr_sav cr nv_k.toNat
                                                nc_w.toNat cnt.toNat idx.toNat st_k ∧
                                              (FullMem c st_k ⋆ R) mk)
                                          (fun (_, _, idx, ()) _ => sz.toNat - idx.toNat)
                                          (fun _ hJ_k => by
                                            m6_steps
                                            exact hJ_k (nv_w, 0#32, 0#32, ()) mw
                                              ⟨Nat.zero_le _, Nat.zero_le _, st_w,
                                               ⟨⟨hb_w, hsav_eq ▸ le_refl _, hscr_sav_eq.symm,
                                                 fun _ _ => rfl⟩,
                                                fun _ hj => by simp at hj,
                                                fun _ hi => by simp at hi,
                                                fun _ hj => by simp at hj,
                                                fun _ _ h1 => by simp at h1⟩, hmw⟩)
                                          (fun _ (nv_k, cnt, idx, ()) mk
                                              ⟨hk_le, hcnt_le, st_k, hs_k, hmk⟩ hJ_k => by
                                            clear hJ_in hJ_we hJ_w hstep_occ
                                              hocc_done hsav_ge1 hbdd_sav htrl_sav
                                              hL_len hL_mv hAddCl hmo_nat
                                              hmv_eq hqi1 hcv_lt_s hmL hmx
                                            try clear hcv_qi
                                            m6_split; rotate_left
                                            · have hidx_ge : sz.toNat ≤ idx.toNat := by
                                                rw [har_sz_idx] at hc
                                                · exact Nat.le_of_not_lt hc
                                                · rw [hcr_idx]
                                                  · rw [hcr2_lt,
                                                      show BitVec.toNat (2 : BitVec 64) =
                                                        2 from rfl,
                                                      Nat.mod_eq_of_lt (by omega)]
                                                  · exact hp_mod
                                              have hk_eq : idx.toNat = sz.toNat :=
                                                Nat.le_antisymm hk_le hidx_ge
                                              m6_steps
                                              exact hJ_occ (nv_k, lim_w, false, cnt, idx, ()) mk
                                                ⟨st_k, hs_k.toM8ConeSavedBase,
                                                 fun _ => ⟨hk_eq, hcnt_le, hs_k.hlts, hs_k.hcov,
                                                   hs_k.hnd⟩, hmk⟩
                                            · -- Body of `idx < sz` loop
                                              have hk_lt : idx.toNat < sz.toNat := by
                                                rw [har_sz_idx] at hc
                                                · exact hc
                                                · rw [hcr_idx]
                                                  · rw [hcr2_lt,
                                                      show BitVec.toNat (2 : BitVec 64) =
                                                        2 from rfl,
                                                      Nat.mod_eq_of_lt (by omega)]
                                                  · exact hp_mod
                                              have hae_k := m8_hag_arena hs_k.hag
                                              have hve_k := m8_hag_vals hs_k.hag
                                              have har_k := hs_k.hlen.core_ok.arena_len_arr
                                              have hvals_k := hs_k.hlen.core_ok.vals_len
                                              have hidx_k : (BitVec.setWidth 64 cr + 3#64 +
                                                  BitVec.setWidth 64 idx).toNat =
                                                  cr.toNat + 3 + idx.toNat := by
                                                simp only [bv_c0_zext32_64, BitVec.toNat_add,
                                                  show (3#64 : BitVec 64).toNat = 3 from rfl]
                                                omega
                                              have hidx_bd : (BitVec.setWidth 64 cr + 3#64 +
                                                  BitVec.setWidth 64 idx).toNat <
                                                  st_k.core.arena.length := by
                                                rw [har_k, hidx_k]; omega
                                              have hl_in_cl :
                                                  (st_k.core.arena[cr.toNat + 3 + idx.toNat]'(by
                                                      rw [har_k]; omega)).toNat ∈
                                                    fullArenaClauseLitsCore s.core cr.toNat := by
                                                rw [m6_arenaClauseLitsCore_mem_iff
                                                  (by rw [hsz_ar]; exact hcr3_bd)]
                                                refine ⟨idx.toNat, by rw [hsz_ar]; exact hk_lt, ?_⟩
                                                rw [List.getElem?_eq_getElem
                                                    (by rw [← hae_k, har_k]; omega),
                                                  Option.getD_some]
                                                simp [hae_k]
                                              obtain ⟨lit_k, hlit_k_def⟩ : ∃ lit_k : BitVec 32,
                                                  lit_k = st_k.core.arena[(BitVec.setWidth 64 cr +
                                                    3#64 + BitVec.setWidth 64 idx).toNat]'hidx_bd
                                                := ⟨_, rfl⟩
                                              have hl_lt_s : lit_k.toNat < 2 * s.core.cur_vars := by
                                                rw [hlit_k_def]
                                                simpa only [hidx_k] using
                                                  hw.arena.lits_lt cr.toNat hcr_ref hng _ hl_in_cl
                                              have hval_bd : lit_k.toNat < st_k.core.vals.length :=
                                                by rw [hvals_k]; omega
                                              have hk1 : (idx + 1#32).toNat = idx.toNat + 1 :=
                                                m6_bv32_add1 (by omega)
                                              have hlit_ar : (s.core.arena[cr.toNat + 3 +
                                                  idx.toNat]?.getD 0#32).toNat = lit_k.toNat := by
                                                rw [List.getElem?_eq_getElem
                                                    (by rw [← hae_k, har_k]; omega),
                                                  Option.getD_some]
                                                simp only [hlit_k_def, hidx_k, hae_k]
                                              have har_hc_idx :
                                                  (cr.toNat + BitVec.toNat (3 : BitVec 64) +
                                                    BitVec.toNat idx) % 2 ^ 64 =
                                                    cr.toNat + 3 + idx.toNat := by
                                                rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                                                  Nat.mod_eq_of_lt (by omega)]
                                              have hidx_bd_w : (BitVec.setWidth 64
                                                  (st_w.core.wstk[(p + 1#64).toNat]'hp1_wstk) +
                                                    3#64 + BitVec.setWidth 64 idx).toNat <
                                                  st_k.core.arena.length := by
                                                rw [hcr_w_p1]; exact hidx_bd
                                              have h_ar_lk_w :
                                                  st_k.core.arena[(BitVec.setWidth 64
                                                      (st_w.core.wstk[(p + 1#64).toNat]'hp1_wstk) +
                                                      3#64 + BitVec.setWidth 64 idx).toNat]'
                                                      hidx_bd_w = lit_k :=
                                                hlit_k_def ▸ m6_list_getElem_congr
                                                  (by rw [hcr_w_p1])
                                                  hidx_bd_w hidx_bd
                                              have h_ar_lk_w1 : ∀ {pf1 pf2},
                                                  st_k.core.arena[(BitVec.setWidth 64
                                                      (st_w.core.wstk[(p +
                                                        (1 : BitVec 64)).toNat]'pf1) +
                                                      (3 : BitVec 64) +
                                                      BitVec.setWidth 64 idx).toNat]'pf2 = lit_k :=
                                                fun {pf1 _} =>
                                                  have hw1 :
                                                      st_w.core.wstk[(p +
                                                        (1 : BitVec 64)).toNat]'pf1 = cr :=
                                                    (m6_list_getElem_congr rfl pf1
                                                      hp1_wstk).trans hcr_w_p1
                                                  hlit_k_def ▸ m6_list_getElem_congr
                                                    (by rw [hw1]; rfl) _ hidx_bd
                                              have hval_bd_w : (BitVec.setWidth 64
                                                  (st_k.core.arena[(BitVec.setWidth 64
                                                    (st_w.core.wstk[(p + 1#64).toNat]'hp1_wstk) +
                                                    3#64 + BitVec.setWidth 64
                                                      idx).toNat]'hidx_bd_w)).toNat <
                                                  st_k.core.vals.length := by
                                                rw [bv_c0_zext32_64, h_ar_lk_w]; exact hval_bd
                                              m6_split
                                              · m6_steps
                                                exact hJ_occ (nv_k, lim_w, true, cnt, idx, ()) mk
                                                  ⟨st_k, hs_k.toM8ConeSavedBase,
                                                   (fun h => by cases h), hmk⟩
                                              have hnot_pos : s.core.vals[lit_k.toNat]?.getD
                                                  0#8 ≠ 1#8 := fun h1 => by
                                                rw [m6_getElem_eq_getD st_k.core.vals (d := 0#8),
                                                  m6_getElem_eq_getD st_k.core.arena (d := 0#32),
                                                  hcr_idx _ hp_mod, har_hc_idx, hae_k, hlit_ar,
                                                  hve_k, h1] at hc
                                                exact absurd hc (by decide)
                                              m6_to_group
                                              refine wp_join_group (ts := [i32, .bool, .bool, i32])
                                                (fun (nv_u, lim_u, drop_u, cnt_u, ()) m_u =>
                                                  lim_u = lim_w ∧ drop_u = false ∧
                                                  cnt.toNat ≤ cnt_u.toNat ∧
                                                  cnt_u.toNat ≤ idx.toNat + 1 ∧
                                                  ∃ st_u' : FullState,
                                                    M8ConeScanBase F_cur L c s cv qi_l saved_nv
                                                      st_w.scratch.work_stk1 scr_sav cr nv_u.toNat
                                                      nc_w.toNat cnt_u.toNat (idx.toNat + 1) st_u'
                                                    ∧ (FullMem c st_u' ⋆ R) m_u)
                                                (fun _ (nv_u, lim_u, drop_u, cnt_u, ()) m_u
                                                    ⟨_, _, _, hc1, st_u', hs_u', hmu'⟩ => by
                                                  m6_steps
                                                  refine hJ_k (nv_u, cnt_u, idx + 1#32, ()) m_u
                                                    (by
                                                      dsimp only; rw [hk1]
                                                      exact m6_nat_sub1_lt hk_lt rfl)
                                                    ⟨by rw [hk1]; exact hk_lt,
                                                     by rw [hk1]; exact hc1, st_u',
                                                     by rw [hk1]; exact hs_u', hmu'⟩)
                                                (fun _ hJ_lv => by
                                                  m6_split
                                                  · have hl_zero : s.core.vals[lit_k.toNat]?.getD
                                                        0#8 = 0#8 := by
                                                      rcases hw.vals_domain lit_k.toNat hl_lt_s
                                                        with h0 | h1 | hf
                                                      · exact h0
                                                      · exact absurd h1 hnot_pos
                                                      · rw [m6_getElem_eq_getD st_k.core.vals
                                                            (d := 0#8),
                                                          m6_getElem_eq_getD st_k.core.arena
                                                            (d := 0#32),
                                                          hcr_idx _ hp_mod, har_hc_idx, hae_k,
                                                          hlit_ar, hve_k, hf] at hc
                                                        exact absurd hc (by decide)
                                                    have hlv_eq : (lit_k >>> (1 : Nat)).toNat =
                                                        lit_k.toNat / 2 :=
                                                      m6_bv32_shr1_toNat lit_k
                                                    have hlv_lt : (lit_k >>> (1 : Nat)).toNat <
                                                        s.core.cur_vars := by omega
                                                    have hlv_tm_k : (BitVec.setWidth 64
                                                        (lit_k >>> (1 : Nat))).toNat <
                                                        st_k.scratch.tarjan_mark.length := by
                                                      rw [hs_k.hlen.scratch_ok.tarjan_mark_len,
                                                        bv_c0_zext32_64]; omega
                                                    have hlv_tm_k_w : (BitVec.setWidth 64
                                                        (st_k.core.arena[(BitVec.setWidth 64
                                                          (st_w.core.wstk[(p +
                                                            1#64).toNat]'hp1_wstk) + 3#64 +
                                                            BitVec.setWidth 64 idx).toNat]'
                                                            hidx_bd_w >>> (1 : Nat))).toNat <
                                                        st_k.scratch.tarjan_mark.length := by
                                                      rw [h_ar_lk_w]; exact hlv_tm_k
                                                    have hfl_k := hs_k.hlen.core_ok.flags_len
                                                    have hlv_fl_k : (BitVec.setWidth 64
                                                        (lit_k >>> (1 : Nat))).toNat <
                                                        st_k.core.flags.length := by
                                                      rw [hfl_k, bv_c0_zext32_64]; omega
                                                    have hlv_fl_k_w : (BitVec.setWidth 64
                                                        (st_k.core.arena[(BitVec.setWidth 64
                                                          (st_w.core.wstk[(p +
                                                            1#64).toNat]'hp1_wstk) + 3#64 +
                                                            BitVec.setWidth 64 idx).toNat]'
                                                            hidx_bd_w >>> (1 : Nat))).toNat <
                                                        st_k.core.flags.length := by
                                                      rw [h_ar_lk_w]; exact hlv_fl_k
                                                    m6_split
                                                    · m6_steps
                                                      exact hJ_occ (nv_k, lim_w, true, cnt, idx,
                                                        ()) mk
                                                        ⟨st_k, hs_k.toM8ConeSavedBase,
                                                         (fun h => by cases h), hmk⟩
                                                    m6_to_group
                                                    refine wp_join_group (ts := [])
                                                      (fun () m_d => m_d = mk)
                                                      (fun _ () m_d hmd => by
                                                        subst m_d
                                                        m6_to_group
                                                        refine wp_join_group (ts := [])
                                                          (fun () m_c => m_c = mk)
                                                          (fun _ () m_c hmc => by
                                                            subst m_c
                                                            m6_to_group
                                                            refine wp_join_group
                                                              (ts := [i32, .bool, .bool])
                                                              (fun (nv_u, lim_u, drop_u, ()) m_u =>
                                                                lim_u = lim_w ∧ drop_u = false ∧
                                                                nv_k.toNat ≤ nv_u.toNat ∧
                                                                ∃ st_u : FullState,
                                                                  M8ConeSavedBase F_cur L c s cv
                                                                    qi_l saved_nv
                                                                    st_w.scratch.work_stk1 scr_sav
                                                                    nv_u.toNat nc_w.toNat st_u ∧
                                                                  st_u.core.tmp = st_k.core.tmp ∧
                                                                  (∀ j < nv_k.toNat,
                                                                    st_u.scratch.work_stk1[j]? =
                                                                      st_k.scratch.work_stk1[j]?) ∧
                                                                  st_u.scratch.tarjan_mark[(lit_k
                                                                    >>> (1 : Nat)).toNat]?.getD
                                                                    0#32 ≠ 0#32 ∧
                                                                  (FullMem c st_u ⋆ R) m_u)
                                                              (fun _ (nv_u, lim_u, drop_u, ()) m_u
                                                                  ⟨hlim_u, hdrop_u, hnvku, st_u,
                                                                   hs_u, htmpu, hwku, htlv, hmu⟩ =>
                                                                     by
                                                                have htm_u :=
                                                                  hs_u.hlen.2.tarjan_mark_len
                                                                have htmp_u :=
                                                                  hs_u.hlen.core_ok.tmp_len_arr
                                                                have hcv_u :=
                                                                  m8_hag_cur_vars hs_u.hag
                                                                rcases hs_u.hcone.rev
                                                                  (lit_k >>> (1 : Nat)).toNat
                                                                    (by rw [hcv_u]; exact hlv_lt)
                                                                      with
                                                                  hz | ⟨ilv, hilv, hwlv, htlv_v⟩
                                                                · exact absurd hz htlv
                                                                have hnv_u_max :=
                                                                  hs_u.hcone.nv_leMax
                                                                obtain ⟨hcnt1, hlu', hlts_u',
                                                                    hcov_u', hvars_u', hnd_u'⟩ :=
                                                                  m8_cone_k_unassigned_step
                                                                  hs_u.hlen
                                                                    htmpu hwku hnvku hnv_u_max
                                                                    hk_lt hsz_cv hcv_le hcnt_le
                                                                    hlit_ar hilv (hlv_eq ▸ hwlv)
                                                                    (hlv_eq ▸ htlv_v) hs_k.hlts
                                                                    hs_k.hcov hs_k.hvars hs_k.hnd
                                                                    hnd_cl hcr3_bd hsz_core
                                                                    hs_u.hcone
                                                                have hcnt_tmp : (BitVec.setWidth 64
                                                                    cnt).toNat <
                                                                    st_u.core.tmp.length := by
                                                                  rw [htmp_u, bv_c0_zext32_64]
                                                                  omega
                                                                have hcnt_tmp' : cnt.toNat <
                                                                    st_u.core.tmp.length := by
                                                                  rw [← bv_c0_zext32_64 cnt]
                                                                  exact hcnt_tmp
                                                                have hlv_tm_u_w : (BitVec.setWidth
                                                                    64 (st_k.core.arena[
                                                                    (BitVec.setWidth 64
                                                                    (st_w.core.wstk[(p +
                                                                      1#64).toNat]'hp1_wstk) +
                                                                    3#64 + BitVec.setWidth 64
                                                                      idx).toNat]'hidx_bd_w >>>
                                                                    (1 : Nat))).toNat <
                                                                    List.length
                                                                      st_u.scratch.tarjan_mark
                                                                    := by
                                                                  rw [h_ar_lk_w, htm_u,
                                                                    bv_c0_zext32_64]; omega
                                                                m6_steps
                                                                have htm_u_lk : ∀ {pf1 pf2 pf3},
                                                                    st_u.scratch.tarjan_mark[
                                                                      (BitVec.setWidth 64
                                                                      (st_k.core.arena[
                                                                        (BitVec.setWidth 64
                                                                          (st_w.core.wstk[(p +
                                                                            (1 : BitVec
                                                                              64)).toNat]'pf1) +
                                                                          (3 : BitVec 64) +
                                                                          BitVec.setWidth 64
                                                                            idx).toNat]'pf2 >>>
                                                                        (OfNat.ofNat 1 :
                                                                          Nat))).toNat]'pf3 =
                                                                      st_u.scratch.tarjan_mark[
                                                                        lit_k.toNat / 2]?.getD
                                                                        0#32 :=
                                                                  fun {_ _ _} => by
                                                                  have hlen_t :
                                                                      lit_k.toNat / 2 <
                                                                        List.length
                                                                          st_u.scratch.tarjan_mark
                                                                        := by rw [htm_u]; omega
                                                                  rw [List.getElem?_eq_getElem
                                                                    hlen_t, Option.getD_some]
                                                                  exact m6_list_getElem_congr
                                                                    (by
                                                                      rw [h_ar_lk_w1,
                                                                        bv_c0_zext32_64]
                                                                      exact hlv_eq) _ _
                                                                have hcnt_n : (BitVec.setWidth 64
                                                                    cnt).toNat = cnt.toNat :=
                                                                  bv_c0_zext32_64 cnt
                                                                let nl_u :=
                                                                  ((st_u.scratch.tarjan_mark[
                                                                    lit_k.toNat / 2]?.getD
                                                                    0#32 - 1#32) <<< (1 : Nat)) |||
                                                                    (lit_k &&& 1#32)
                                                                let st_u' : FullState :=
                                                                  { st_u with core :=
                                                                    { st_u.core with
                                                                      tmp :=
                                                                        st_u.core.tmp.set
                                                                          cnt.toNat nl_u } }
                                                                have hm_u' : (FullMem c st_u' ⋆
                                                                    R) m := by
                                                                  have hm' := hm
                                                                  dsimp only [LeanQbe.T.lift2,
                                                                    Arg.val_var, Arg.val_imm,
                                                                    Prod.fst] at hm'
                                                                  rw [hcnt_n, htm_u_lk,
                                                                    h_ar_lk_w1] at hm'
                                                                  exact hm'
                                                                refine hJ_lv (nv_u, lim_u, drop_u,
                                                                  cnt + 1#32, ()) m
                                                                  ⟨hlim_u, hdrop_u, by omega,
                                                                   by rw [hcnt1]; omega, st_u',
                                                                   ⟨⟨⟨hlu',
                                                                      m8ConeMask_upd_tmp _ hs_u.hag,
                                                                      m8ConeInv_tmp_irrel
                                                                       hs_u.hcone,
                                                                      hs_u.htmk, hs_u.hwk⟩,
                                                                    hs_u.hsav_le, hs_u.hscr,
                                                                    hs_u.hws⟩,
                                                                   hlts_u',
                                                                   by simpa only [hk1] using
                                                                     hcov_u',
                                                                   by simpa only [hk1] using
                                                                     hvars_u',
                                                                   hnd_u'⟩, hm_u'⟩)
                                                              (fun _ hJ_u => by
                                                                have htm_k :=
                                                                  hs_k.hlen.2.tarjan_mark_len
                                                                have hwk_k_len :=
                                                                  hs_k.hlen.scratch_ok.work_stk1_len
                                                                m6_split
                                                                · have hmiss :
                                                                      st_k.scratch.tarjan_mark[
                                                                        (lit_k >>>
                                                                          (1 : Nat)).toNat]?.getD
                                                                        0#32 = 0#32 := by
                                                                    rw [m6_getElem_eq_getD
                                                                        st_k.scratch.tarjan_mark
                                                                        (d := 0#32),
                                                                      m6_getElem_eq_getD
                                                                        st_k.core.arena (d := 0#32),
                                                                      hcr_idx _ hp_mod, har_hc_idx,
                                                                      hae_k, hlit_ar, ← hlv_eq]
                                                                      at hc
                                                                    exact hc
                                                                  m6_split
                                                                  · m6_steps
                                                                    exact hJ_occ (nv_k, true, true,
                                                                      cnt, idx, ()) mk
                                                                      ⟨st_k, hs_k.toM8ConeSavedBase,
                                                                       (fun h => by cases h), hmk⟩
                                                                  · have hnv_k_max :
                                                                        nv_k.toNat < 256 := by
                                                                      have : ¬ 256 ≤ nv_k.toNat :=
                                                                        hc
                                                                      have := hmL_lo
                                                                      omega
                                                                    have hqi_nv_k :
                                                                        qi_l.toNat < nv_k.toNat :=
                                                                      Nat.lt_of_lt_of_le
                                                                        (hsav_eq ▸
                                                                          Nat.lt_of_lt_of_le
                                                                            hqi_l_lt hnv_w_mono)
                                                                        hs_k.hsav_le
                                                                    rcases m8_cone_push_var_base_ok
                                                                        hs_k.toM8ConeSavedBase
                                                                        hnv_k_max hlv_lt hmiss
                                                                        hqi_nv_k with
                                                                      ⟨hnv_k_lt, hnv1, hne_nv_qi,
                                                                        hne_cv, hs_u, htlvu⟩
                                                                    have hnv_ws :
                                                                        (BitVec.setWidth 64
                                                                          ((nv_k + 1#32) -
                                                                            1#32)).toNat <
                                                                          List.length
                                                                            st_k.scratch.work_stk1
                                                                          := by
                                                                      rw [hwk_k_len,
                                                                        bv_c0_zext32_64,
                                                                        m6_bv32_add1_sub1_eq nv_k]
                                                                      omega
                                                                    have hnv_ws0 : (BitVec.setWidth
                                                                        64 nv_k).toNat <
                                                                        List.length
                                                                          st_k.scratch.work_stk1
                                                                        := by
                                                                      rw [hwk_k_len,
                                                                        bv_c0_zext32_64]; omega
                                                                    have hnv_ws1 : nv_k.toNat <
                                                                        List.length
                                                                          st_k.scratch.work_stk1
                                                                        := by
                                                                      rw [hwk_k_len]; omega
                                                                    m6_steps
                                                                    let st_u : FullState :=
                                                                      { st_k with scratch :=
                                                                        { st_k.scratch with
                                                                          tarjan_mark := List.set
                                                                            st_k.scratch.tarjan_mark
                                                                            (lit_k >>>
                                                                              (1 : Nat)).toNat
                                                                            (nv_k + 1#32)
                                                                          work_stk1 := List.set
                                                                            st_k.scratch.work_stk1
                                                                            nv_k.toNat (lit_k >>>
                                                                              (1 : Nat)) } }
                                                                    have h2 :=
                                                                      m6_bv32_add1_sub1_toNat nv_k
                                                                    have htm_idx :
                                                                        (BitVec.setWidth 64
                                                                          (lit_k >>> (OfNat.ofNat 1
                                                                            : Nat))).toNat =
                                                                          (lit_k >>> (1 :
                                                                            Nat)).toNat :=
                                                                      bv_c0_zext32_64 _
                                                                    have hm_u :
                                                                        (FullMem c st_u ⋆ R) m := by
                                                                      have hm' := hm
                                                                      dsimp only [LeanQbe.T.lift2,
                                                                        Arg.val_var, Arg.val_imm,
                                                                        Prod.fst] at hm'
                                                                      rw [h_ar_lk_w1, htm_idx,
                                                                        bv_c0_zext32_64] at hm'
                                                                      try rw [h2] at hm'
                                                                      exact (congrArg (fun stx =>
                                                                        (FullMem c stx ⋆ R) m)
                                                                        rfl).mp hm'
                                                                    exact hJ_u (nv_k + 1#32, lim_w,
                                                                      false, ()) m
                                                                      ⟨rfl, rfl,
                                                                       by rw [hnv1]; exact
                                                                         Nat.le_succ _,
                                                                       st_u, hs_u, rfl,
                                                                       fun j _ => by
                                                                         dsimp only [st_u]
                                                                         exact List.getElem?_set_ne
                                                                           (by omega),
                                                                       htlvu, hm_u⟩
                                                                · have hne_ov :
                                                                      st_k.scratch.tarjan_mark[
                                                                        (lit_k >>>
                                                                          (1 : Nat)).toNat]?.getD
                                                                        0#32 ≠ 0#32 := by
                                                                    rw [m6_getElem_eq_getD
                                                                        st_k.scratch.tarjan_mark
                                                                        (d := 0#32),
                                                                      m6_getElem_eq_getD
                                                                        st_k.core.arena (d := 0#32),
                                                                      hcr_idx _ hp_mod, har_hc_idx,
                                                                      hae_k, hlit_ar, ← hlv_eq]
                                                                      at hc
                                                                    exact hc
                                                                  m6_steps
                                                                  exact hJ_u (nv_k, lim_w, false,
                                                                    ()) mk
                                                                    ⟨rfl, rfl, le_refl _, st_k,
                                                                     hs_k.toM8ConeSavedBase, rfl,
                                                                     fun _ _ => rfl, hne_ov, hmk⟩))
                                                          (fun _ hJcont => by
                                                            m6_split
                                                            · m6_split
                                                              · m6_steps
                                                                exact hJ_occ (nv_k, lim_w, true,
                                                                  cnt, idx, ()) mk
                                                                  ⟨st_k, hs_k.toM8ConeSavedBase,
                                                                   (fun h => by cases h), hmk⟩
                                                              · m6_steps; exact hJcont () mk rfl
                                                            · m6_steps; exact hJcont () mk rfl))
                                                      (fun _ hJdup => by
                                                        m6_split
                                                        · m6_split
                                                          · m6_steps
                                                            exact hJ_occ (nv_k, lim_w, true, cnt,
                                                              idx, ()) mk
                                                              ⟨st_k, hs_k.toM8ConeSavedBase,
                                                               (fun h => by cases h), hmk⟩
                                                          · m6_steps; exact hJdup () mk rfl
                                                        · m6_steps; exact hJdup () mk rfl)
                                                  · have hne0 : s.core.vals[lit_k.toNat]?.getD
                                                        0#8 ≠ 0#8 := fun h0 => by
                                                      rw [m6_getElem_eq_getD st_k.core.vals
                                                          (d := 0#8),
                                                        m6_getElem_eq_getD st_k.core.arena
                                                          (d := 0#32),
                                                        hcr_idx _ hp_mod, har_hc_idx, hae_k,
                                                        hlit_ar, hve_k, h0] at hc
                                                      exact absurd (by decide) hc
                                                    have hfals_k : s.core.vals[lit_k.toNat]?.getD
                                                        0#8 = 0xFF#8 :=
                                                      (hw.vals_domain lit_k.toNat hl_lt_s).elim
                                                        (absurd · hne0)
                                                        (·.elim (absurd · hnot_pos) id)
                                                    m6_steps
                                                    refine hJ_lv (nv_k, lim_w, false, cnt, ()) mk
                                                      ⟨rfl, rfl, le_refl _, by omega,
                                                       st_k, ⟨hs_k.toM8ConeSavedBase, hs_k.hlts,
                                                        fun i hi => ?_, fun j hj => ?_, hs_k.hnd⟩,
                                                       hmk⟩
                                                    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with
                                                        hlt | rfl
                                                      · exact hs_k.hcov i hlt
                                                      · left; rwa [hlit_ar]
                                                    · obtain ⟨p, hp, hpeq⟩ := hs_k.hvars j hj
                                                      exact ⟨p, Nat.lt_succ_of_lt hp, hpeq⟩)))))))
                    (fun _ hJ_bp => by
                      clear hJ_out hJ_in hcur_tmk hcv_idx hdw hroot htmk hm_shl1 hqnext_c0
                        hmv_c0 hmv_bounds hmv64_lt hdep1 hdep_lt hlim_f hqi_lt hqi_le hdep_le
                      m6_split; rotate_left
                      · m6_steps; exact hJ_bp () mp ⟨hle_nv_p, st_p, hb_p, hmp⟩
                      have hpol_lt : pol.toNat < 2 := hc
                      m6_split
                      · m6_steps; exact hJ_bp () mp ⟨hle_nv_p, st_p, hb_p, hmp⟩
                      m6_split; rotate_left
                      · m6_steps; exact hJ_bp () mp ⟨hle_nv_p, st_p, hb_p, hmp⟩
                      have hncp_lt : nc_p.toNat < L.maxOrig := by
                        have : nc_p.toNat < 1024 := hc
                        unfold K6Layout.maxOrig; omega
                      obtain ⟨lit, hlit_def⟩ : ∃ lit : BitVec 32,
                          lit = ((cv <<< (1 : Nat)) ||| pol) := ⟨_, rfl⟩
                      have hlit_eq : lit.toNat = 2 * cv.toNat + pol.toNat := by
                        rw [hlit_def]; exact m6_bv32_shl1_or_pol cv pol (by omega) hpol_lt
                      have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by omega
                      obtain ⟨hwo, hwsz, hend_eq, hwo_le, hrem_eq, hend_ws, h2l_mod, h2l1_mod⟩ :=
                        m8_cone_wvec_facts hlen hb_p.hlen hb_p.hag hdwatches hlit_lt
                      have hwvec_p := hb_p.hlen.core_ok.wvec_len
                      have h2l_bd : (BitVec.setWidth 64 lit <<< (1 : Nat)).toNat <
                          st_p.core.wvec.length := by
                        rw [hwvec_p, m6_bv64_shl1]; omega
                      have h2l1_bd : ((BitVec.setWidth 64 lit <<< (1 : Nat)) + 1#64).toNat <
                          st_p.core.wvec.length := by
                        rw [hwvec_p, m6_bv64_shl1_add1]; omega
                      obtain ⟨wOff, hwOff_def⟩ : ∃ wOff : BitVec 64,
                          wOff = (st_p.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat)).toNat]'
                            h2l_bd).setWidth 64 := ⟨_, rfl⟩
                      obtain ⟨wSz, hwSz_def⟩ : ∃ wSz : BitVec 64,
                          wSz = (st_p.core.wvec[((BitVec.setWidth 64 lit <<< (1 : Nat)) +
                            1#64).toNat]'h2l1_bd).setWidth 64 := ⟨_, rfl⟩
                      obtain ⟨wEnd, hwEnd⟩ : ∃ wEnd : BitVec 64, wEnd = wOff + wSz := ⟨_, rfl⟩
                      have hend_ws : wEnd.toNat ≤ s.core.wstk.length := by
                        rw [hwEnd, hwOff_def, hwSz_def]; exact hend_ws
                      have hend_n : wEnd.toNat =
                          fullWatchOffCore s.core lit.toNat +
                            fullWatchSizeCore s.core lit.toNat := by
                        rw [hwEnd, hwOff_def, hwSz_def]; exact hend_eq
                      have hpol1 : (pol + 1#32).toNat = pol.toNat + 1 :=
                        m6_bv32_add1 (Nat.lt_trans hpol_lt (by decide))
                      have hwv0_eq :
                          ∀ (h : (2 * lit.toNat) % 2 ^ 64 < st_p.core.wvec.length),
                          st_p.core.wvec[(2 * lit.toNat) % 2 ^ 64]'h =
                            st_p.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat)).toNat]'h2l_bd :=
                        fun h => m6_list_getElem_congr h2l_mod h _
                      have hwv1_eq :
                          ∀ (h : (2 * lit.toNat + (1#64).toNat) % 2 ^ 64 <
                              st_p.core.wvec.length),
                            st_p.core.wvec[(2 * lit.toNat + (1#64).toNat) % 2 ^ 64]'h =
                              st_p.core.wvec[((BitVec.setWidth 64 lit <<< (1 : Nat)) +
                                1#64).toNat]'h2l1_bd := fun h =>
                        m6_list_getElem_congr
                          (by rw [show (1#64).toNat = 1 from rfl]; exact h2l1_mod) h _
                      have h2l_bd_ws :
                          (BitVec.setWidth 64 ((st_l.scratch.work_stk1[
                            (BitVec.setWidth 64 qi_l).toNat]'hqi_ws <<< (1 : Nat)) ||| pol) <<<
                            (1 : Nat)).toNat < st_p.core.wvec.length := by
                        rw [← hcv_def, ← hlit_def]; exact h2l_bd
                      have h2l1_bd_ws :
                          ((BitVec.setWidth 64 ((st_l.scratch.work_stk1[
                            (BitVec.setWidth 64 qi_l).toNat]'hqi_ws <<< (1 : Nat)) ||| pol) <<<
                            (1 : Nat)) + 1#64).toNat < st_p.core.wvec.length := by
                        rw [← hcv_def, ← hlit_def]; exact h2l1_bd
                      have hw0_ws :
                          ∀ (h : (BitVec.setWidth 64 ((st_l.scratch.work_stk1[
                              (BitVec.setWidth 64 qi_l).toNat]'hqi_ws <<< (1 : Nat)) ||| pol) <<<
                              (1 : Nat)).toNat < st_p.core.wvec.length),
                            (st_p.core.wvec[(BitVec.setWidth 64 ((st_l.scratch.work_stk1[
                              (BitVec.setWidth 64 qi_l).toNat]'hqi_ws <<< (1 : Nat)) ||| pol) <<<
                              (1 : Nat)).toNat]'h).setWidth 64 = wOff := fun h => by
                        rw [hwOff_def]; congr 1
                        exact m6_list_getElem_congr (by rw [← hcv_def, ← hlit_def]) h h2l_bd
                      have hw1_ws :
                          ∀ (h : ((BitVec.setWidth 64 ((st_l.scratch.work_stk1[
                              (BitVec.setWidth 64 qi_l).toNat]'hqi_ws <<< (1 : Nat)) ||| pol) <<<
                              (1 : Nat)) + 1#64).toNat < st_p.core.wvec.length),
                            (st_p.core.wvec[((BitVec.setWidth 64 ((st_l.scratch.work_stk1[
                              (BitVec.setWidth 64 qi_l).toNat]'hqi_ws <<< (1 : Nat)) ||| pol) <<<
                              (1 : Nat)) + 1#64).toNat]'h).setWidth 64 = wSz := fun h => by
                        rw [hwSz_def]; congr 1
                        exact m6_list_getElem_congr (by rw [← hcv_def, ← hlit_def]) h h2l1_bd
                      have hw0_eq_nat : ∀ (h : (BitVec.setWidth 64 lit <<< (1 : Nat)).toNat <
                            st_p.core.wvec.length),
                          (st_p.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat)).toNat]'h).toNat =
                            wOff.toNat := fun h => by rw [hwOff_def, bv_c0_zext32_64]
                      have hw1_eq_nat : ∀ (h : ((BitVec.setWidth 64 lit <<< (1 : Nat)) +
                            1#64).toNat < st_p.core.wvec.length),
                          (st_p.core.wvec[((BitVec.setWidth 64 lit <<< (1 : Nat)) +
                            1#64).toNat]'h).toNat = wSz.toNat := fun h => by
                        rw [hwSz_def, bv_c0_zext32_64]
                      m6_to_group
                      refine wp_join_group (ts := [i32, i32, .bool, i64])
                        (fun (nv_e, nc_e, _lim_e, _, ()) m_we =>
                          layer_end.toNat ≤ nv_e.toNat ∧ ∃ st_we : FullState,
                            M8ConeBase F_cur L c s cv qi_l nv_e.toNat nc_e.toNat st_we ∧
                            (FullMem c st_we ⋆ R) m_we)
                        (fun _ (nv_e, nc_e, lim_e, _, ()) m_we ⟨hnve, st_we, hb_e, hm_e⟩ => by
                          m6_steps
                          exact hJ_bpol (nv_e, nc_e, lim_e, pol + 1#32, ()) m_we
                            (by dsimp only; rw [hpol1]; exact m6_nat_sub1_lt hpol_lt rfl)
                            ⟨by rw [hpol1]; exact hpol_lt, hnve, st_we, hb_e, hm_e⟩)
                        (fun _ hJ_we => by
                          m6_to_group
                          refine wp_loop_inv (ts := [i32, i32, .bool, i64])
                            (fun (nv_w, nc_w, _lim_w, p, ()) mw =>
                              p.toNat ≤ wEnd.toNat ∧ layer_end.toNat ≤ nv_w.toNat ∧
                              DenseWatchSliceOk F_cur s.core lit.toNat p.toNat
                                (wEnd.toNat - p.toNat) ∧
                              ∃ st_w : FullState,
                                M8ConeBase F_cur L c s cv qi_l nv_w.toNat nc_w.toNat st_w ∧
                                (FullMem c st_w ⋆ R) mw)
                            (fun (_, _, _, p, ()) _ => wEnd.toNat - p.toNat)
                            (fun _ hJ_w => by
                              m6_steps
                              refine hJ_w (nv_p, nc_p, lim_p, _, ()) mp
                                ⟨?_, hle_nv_p, ?_, st_p, hb_p, hmp⟩
                              · try rw [hw0_ws]
                                rw [hwEnd, hwOff_def, hwSz_def]; exact hwo_le
                              · try rw [hw0_ws]
                                rw [hwEnd, hwOff_def, hwSz_def, hrem_eq, hwo]
                                exact hdwatches.slices lit.toNat hlit_lt)
                            (fun J_w (nv_w, nc_w, lim_w, p, ()) mw
                                ⟨hp_le, hnv_w_mono, hslice, st_w, hb_w, hmw⟩ hJ_w => by
                              clear hJ_bpol hmp hpol1 hle_nv_l hlen_l hag_l hcone_l
                                hqi1 hnc_lt hncp_lt hpol_le hcv_lt_s hwo_le hrem_eq
                              m6_split; rotate_left
                              · m6_steps; exact hJ_we (nv_w, nc_w, lim_w, p, ()) mw
                                  ⟨hnv_w_mono, st_w, hb_w, hmw⟩
                              have hp_lt : p.toNat < wEnd.toNat := by
                                simp only [hcv_qi0] at hc
                                repeat rw [m6_getElem_eq_getD st_p.core.wvec (d := 0#32)] at hc
                                rw [m8_hag_wvec hb_p.hag] at hc
                                change p.toNat <
                                  ((s.core.wvec[2 * (cv <<< (1 : Nat) ||| pol).toNat %
                                      2 ^ 64]?.getD 0#32).toNat +
                                    (s.core.wvec[(2 * (cv <<< (1 : Nat) ||| pol).toNat +
                                        1) % 2 ^ 64]?.getD 0#32).toNat) % 2 ^ 64 at hc
                                rw [← hlit_def,
                                  show 2 * lit.toNat % 2 ^ 64 = 2 * lit.toNat from
                                    Nat.mod_eq_of_lt (by omega),
                                  show (2 * lit.toNat + 1) % 2 ^ 64 = 2 * lit.toNat + 1 from
                                    Nat.mod_eq_of_lt (by omega)] at hc
                                change p.toNat <
                                  (fullWatchOffCore s.core lit.toNat +
                                    fullWatchSizeCore s.core lit.toNat) % 2 ^ 64 at hc
                                have hw_lt : wEnd.toNat < 2 ^ 64 := wEnd.isLt
                                rw [← hend_n, Nat.mod_eq_of_lt (by omega)] at hc
                                exact hc
                              m6_split
                              · m6_steps; exact hJ_we (nv_w, nc_w, lim_w, p, ()) mw
                                  ⟨hnv_w_mono, st_w, hb_w, hmw⟩
                              m6_split; rotate_left
                              · m6_steps; exact hJ_we (nv_w, nc_w, lim_w, p, ()) mw
                                  ⟨hnv_w_mono, st_w, hb_w, hmw⟩
                              have hncw_lt : nc_w.toNat < L.maxOrig := by
                                have : nc_w.toNat < 1024 := hc
                                unfold K6Layout.maxOrig; omega
                              have hwstk_eq : st_w.core.wstk = s.core.wstk :=
                                m8_hag_wstk hb_w.hag
                              have hcv_w : st_w.core.cur_vars = s.core.cur_vars :=
                                m8_hag_cur_vars hb_w.hag
                              have hp_wstk_w : p.toNat < st_w.core.wstk.length :=
                                m8_cone_hp_wstk hwstk_eq hp_lt hend_ws
                              have hp1 : (p + 1#64).toNat = p.toNat + 1 := m6_bv64_add1 (by omega)
                              obtain ⟨w0, hw0_def⟩ : ∃ w0 : BitVec 32,
                                  w0 = st_w.core.wstk[p.toNat]'hp_wstk_w := ⟨_, rfl⟩
                              have hw0_s : s.core.wstk[p.toNat]? = some w0 := by
                                rw [hw0_def, List.getElem?_eq_getElem (hwstk_eq ▸ hp_wstk_w)]
                                exact congrArg some (by simp [hwstk_eq])
                              m6_split
                              · have hocc : (w0 &&& 0x80000000#32) = 0#32 := by
                                  rw [hw0_def]; exact hc
                                obtain ⟨_, _, _, _, _, _, hslice1⟩ :=
                                  m6_denseSlice_step_occ hslice (Nat.sub_pos_of_lt hp_lt) hw0_s
                                    hocc
                                have hp2 : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by
                                  rw [m6_bv64_add1 (by rw [hp1]; omega), hp1]
                                have hp2_le : (p + 1#64 + 1#64).toNat ≤ wEnd.toNat := by
                                  rw [hp2]; omega
                                m6_steps
                                exact hJ_w (nv_w, nc_w, lim_w, p + 1#64 + 1#64, ()) mw
                                  (by dsimp only; exact m6_nat_sub2_lt hp_lt hp2_le hp2)
                                  ⟨hp2_le, hnv_w_mono,
                                    by rw [hp2, m8_cone_sub_sub_eq]; exact hslice1,
                                    st_w, hb_w, hmw⟩
                              · have hbin : (w0 &&& 0x80000000#32) ≠ 0#32 := by
                                  rw [hw0_def]; exact hc
                                obtain ⟨_, hot_lt, hent_bin, hslice1⟩ :=
                                  m6_denseSlice_step_bin hslice (Nat.sub_pos_of_lt hp_lt) hw0_s
                                    hbin
                                obtain ⟨ot, hot_def⟩ : ∃ ot : BitVec 32,
                                    ot = (w0 &&& 0x7FFFFFFF#32) := ⟨_, rfl⟩
                                have hot_lt' : ot.toNat < 2 * s.core.cur_vars :=
                                  hot_def ▸ hot_lt
                                obtain ⟨ov, hov_def⟩ : ∃ ov : BitVec 32,
                                    ov = (ot >>> (1 : Nat)) := ⟨_, rfl⟩
                                have hov_eq : ov.toNat = ot.toNat / 2 := by
                                  rw [hov_def]; exact m6_bv32_shr1_toNat ot
                                have hov_lt : ov.toNat < s.core.cur_vars := by omega
                                have hvals_w := hb_w.hlen.core_ok.vals_len
                                have hfl_w := hb_w.hlen.core_ok.flags_len
                                have htm_w := hb_w.hlen.scratch_ok.tarjan_mark_len
                                have hwk_w_len := hb_w.hlen.scratch_ok.work_stk1_len
                                have hcv_w' := m8_hag_cur_vars hb_w.hag
                                have hov_fl : (BitVec.setWidth 64 ov).toNat <
                                    st_w.core.flags.length := by
                                  rw [hfl_w, bv_c0_zext32_64]; omega
                                have hov_fl_p : (BitVec.setWidth 64
                                    ((st_w.core.wstk[p.toNat]'hp_wstk_w &&&
                                      (2147483647 : BitVec 32)) >>> (1 : Nat))).toNat <
                                    st_w.core.flags.length := by
                                  rw [← hw0_def,
                                    show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl,
                                    ← hot_def, ← hov_def]
                                  exact hov_fl
                                have hot_vals : (BitVec.setWidth 64 ot).toNat <
                                    st_w.core.vals.length := by
                                  rw [hvals_w, bv_c0_zext32_64]; omega
                                have hot_vals_p : (BitVec.setWidth 64
                                    (st_w.core.wstk[p.toNat]'hp_wstk_w &&&
                                      (2147483647 : BitVec 32))).toNat < st_w.core.vals.length := by
                                  rw [← hw0_def,
                                    show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl,
                                    ← hot_def]
                                  exact hot_vals
                                have hstep_bin : ∀ nv_b nc_b lim_b st_b m_b,
                                    layer_end.toNat ≤ BitVec.toNat nv_b →
                                    M8ConeBase F_cur L c s cv qi_l nv_b.toNat nc_b.toNat st_b →
                                    (FullMem c st_b ⋆ R) m_b →
                                    J_w (nv_b, nc_b, lim_b, p + 1#64, ()) m_b :=
                                  fun nv_b nc_b lim_b st_b m_b hnvb hbb hmb =>
                                    hJ_w (nv_b, nc_b, lim_b, p + 1#64, ()) m_b
                                      (by dsimp only; rw [hp1]; exact m6_nat_sub1_lt hp_lt rfl)
                                      ⟨by rw [hp1]; exact hp_lt, hnvb,
                                        by rw [hp1, m8_cone_sub_sub_eq]; exact hslice1,
                                        st_b, hbb, hmb⟩
                                -- `if ((u64)ov >= h->cur_vars || (fl[ov] & FL_ACTIVE) == 0u)`
                                m6_split
                                · exfalso
                                  have hge_cv : st_w.core.cur_vars ≤ ov.toNat := by
                                    rw [← hov_def, ← hot_def, ← hw0_def] at *; bv_omega
                                  omega
                                m6_split
                                · m6_steps
                                  exact hstep_bin nv_w nc_w lim_w st_w mw hnv_w_mono hb_w hmw
                                -- `if (ovv > 0) continue`
                                m6_split
                                · m6_steps
                                  exact hstep_bin nv_w nc_w lim_w st_w mw hnv_w_mono hb_w hmw
                                have hnot_pos : s.core.vals[ot.toNat]?.getD 0#8 ≠ 1#8 :=
                                  fun h1 => by
                                    have h1' : s.core.vals[(st_w.core.wstk[p.toNat]'hp_wstk_w &&&
                                        (2147483647 : BitVec 32)).toNat]?.getD 0#8 = 1#8 := by
                                      rw [← hw0_def,
                                        show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl,
                                        ← hot_def]
                                      exact h1
                                    rw [m6_getElem_eq_getD st_w.core.vals (d := 0#8),
                                      m8_hag_vals hb_w.hag, h1'] at hc
                                    exact absurd hc (by decide)
                                -- `if (ov == cv)`
                                m6_split
                                · m6_to_group
                                  refine wp_join_group (ts := [i32, .bool])
                                    (fun (nc_b, _lim_b, ()) m_b => ∃ st_b : FullState,
                                      M8ConeBase F_cur L c s cv qi_l nv_w.toNat nc_b.toNat st_b ∧
                                      (FullMem c st_b ⋆ R) m_b)
                                    (fun _ (nc_b, lim_b, ()) m_b ⟨st_b, hbb, hmb⟩ => by
                                      m6_steps
                                      exact hstep_bin nv_w nc_b lim_b st_b m_b hnv_w_mono hbb hmb)
                                    (fun _ hJ_ov => by
                                      m6_split; rotate_left
                                      · m6_steps; exact hJ_ov (nc_w, lim_w, ()) mw ⟨st_w, hb_w, hmw⟩
                                      have hot_eq_lit : ot = lit := by
                                        rw [hot_def, hw0_def]
                                        simp only [hcv_qi0] at hc
                                        change (st_w.core.wstk[p.toNat]'hp_wstk_w &&&
                                          0x7FFFFFFF#32) = (cv <<< (1 : Nat) ||| pol) at hc
                                        rw [← hlit_def] at hc
                                        exact hc
                                      have hnv_w_max := hb_w.hcone.nv_leMax
                                      have htmp_w0 : 0 < st_w.core.tmp.length := by
                                        rw [hb_w.hlen.core_ok.tmp_len_arr]; omega
                                      have hent_self : (cnfOfClauses F_cur).EntailsClause
                                          (cnfClause [lit.toNat]) := by
                                        apply m6_entails_singleton_of_dup
                                        simpa only [← hot_def, ← hot_eq_lit] using hent_bin
                                      have hmap_lp : ((qi_l <<< (1 : Nat)) ||| pol).toNat =
                                          2 * qi_l.toNat + pol.toNat :=
                                        m6_bv32_shl1_or_pol qi_l pol (by omega) hpol_lt
                                      obtain ⟨hl_st, hlts_u, hent_u⟩ :=
                                        m6_cone_unit_tmp_prep (nv := nv_w) (qi0 := qi_l)
                                          (pol := pol) (u := (qi_l <<< (1 : Nat)) ||| pol) hb_w.hlen
                                          htmp_w0 (by omega) (by omega) hpol_lt (by omega)
                                          hmap_lp
                                          (by rw [hb_w.hwk, ← hlit_eq]) hent_self
                                      m6_to_group
                                      try refine wp_unroll_group fun _ _ => ?_
                                      m6_steps
                                      have hcv_q' :
                                          st_l.scratch.work_stk1[(BitVec.setWidth 64 qi_l).toNat]'
                                            hqi_ws = cv := hcv_def.symm
                                      have hm_tmk0 :
                                          st_l.scratch.tarjan_mark[(BitVec.setWidth 64
                                            (st_l.scratch.work_stk1[(BitVec.setWidth 64
                                              qi_l).toNat]'hqi_ws)).toNat]'(by
                                                rw [hcv_q']; exact hcv_tmk) - 1#32 = qi_l := by
                                        rw [m6_list_getElem_congr
                                          (congrArg (fun x => (BitVec.setWidth 64 x).toNat) hcv_q')
                                          _ hcv_tmk, hmap_c]
                                      refine m8_cone_call_add_clause hAddCl (aSz := Arg.imm 1)
                                        (sz := 1#32) rfl hL_len hL_mv hl_st
                                        (m8ConeMask_upd_tmp _ hb_w.hag)
                                        (m8ConeInv_tmp_irrel hb_w.hcone) hncw_lt (by decide)
                                        (by
                                          rw [hl_st.core_ok.tmp_len_arr,
                                            ← hb_w.hlen.core_ok.tmp_len_arr]
                                          exact htmp_w0)
                                        hlts_u hent_u
                                        (m6_fullMem_tmp0_congr
                                          (congrArg (fun x : BitVec 32 =>
                                            (x <<< (1 : Nat)) ||| pol) hm_tmk0)
                                          hm)
                                        (fun ok st' m' hl' ha' hc' _ ht' hw' hm' => by
                                          m6_split
                                          · have hic := (m8_cone_load_kptr_hdr hc' hm').1
                                            m6_to_group
                                            refine wp_join_group (ts := [.bool])
                                              (fun (_lim', ()) m'' => m'' = m')
                                              (fun _ (lim', ()) m'' hm'' => by
                                                subst m''
                                                m6_steps
                                                exact hJ_ov (nc_w + 1#32, lim', ()) m'
                                                  ⟨st', ⟨hl', ha', by simpa only [hc, ↓reduceIte]
                                                    using hc', ht' ▸ hb_w.htmk, hw' ▸ hb_w.hwk⟩,
                                                   hm'⟩)
                                              (fun _ hJ_inc => by
                                                change wp _ _ _ _ _; c0_hsteps
                                                dsimp only [Prod.fst]
                                                try (first | rw [hkptr_c0] | rw [hkptr_c0_nat])
                                                try rw [show (BitVec.ofNat (OfNat.ofNat 64)
                                                    (OfNat.ofNat 6) : BitVec 64) = 6#64 from rfl]
                                                refine head_wp_load rfl hic ?_
                                                m6_split
                                                · m6_steps; exact hJ_inc (true, ()) m' rfl
                                                · m6_steps; exact hJ_inc (lim_w, ()) m' rfl)
                                          · m6_steps
                                            exact hJ_ov (nc_w, true, ()) m'
                                              ⟨st', ⟨hl', ha', by simpa only [hc,
                                                Bool.false_eq_true,
                                                ↓reduceIte] using hc', ht' ▸ hb_w.htmk,
                                                hw' ▸ hb_w.hwk⟩, hm'⟩))
                                -- `if (ovv < 0)`
                                have hov_ne_cv : ov ≠ cv := by
                                  rw [hov_def, hot_def, hw0_def]
                                  simp only [hcv_qi0] at hc
                                  change ¬((st_w.core.wstk[p.toNat]'hp_wstk_w &&&
                                    0x7FFFFFFF#32) >>> (1 : Nat) = cv) at hc
                                  exact hc
                                m6_split
                                · have htmp_w0 : 0 < st_w.core.tmp.length := by
                                    rw [hb_w.hlen.core_ok.tmp_len_arr]; omega
                                  m6_to_group
                                  refine wp_join_group (ts := [i32, .bool])
                                    (fun (nc_b, _lim_b, ()) m_b => ∃ st_b : FullState,
                                      M8ConeBase F_cur L c s cv qi_l nv_w.toNat nc_b.toNat st_b ∧
                                      (FullMem c st_b ⋆ R) m_b)
                                    (fun _ (nc_b, lim_b, ()) m_b ⟨st_b, hbb, hmb⟩ => by
                                      m6_steps
                                      exact hstep_bin nv_w nc_b lim_b st_b m_b hnv_w_mono hbb hmb)
                                    (fun _ hJ_ov => by
                                      have hne0 : s.core.vals[ot.toNat]?.getD 0#8 ≠ 0#8 :=
                                        fun h0 => by
                                          have h0' : s.core.vals[(st_w.core.wstk[p.toNat]'hp_wstk_w
                                              &&& (2147483647 : BitVec 32)).toNat]?.getD 0#8 =
                                              0#8 := by
                                            rw [← hw0_def,
                                              show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from
                                                rfl, ← hot_def]
                                            exact h0
                                          rw [m6_getElem_eq_getD st_w.core.vals (d := 0#8),
                                            m8_hag_vals hb_w.hag, h0'] at hc
                                          exact absurd hc (by decide)
                                      have hfals_ot : s.core.vals[ot.toNat]?.getD 0#8 = 0xFF#8 :=
                                        (hw.vals_domain ot.toNat hot_lt').elim
                                          (absurd · hne0) (·.elim (absurd · hnot_pos) id)
                                      have hnv_w_max := hb_w.hcone.nv_leMax
                                      have hent_unit : (cnfOfClauses F_cur).EntailsClause
                                          (cnfClause [lit.toNat]) :=
                                        m6_entails_fst_of_snd_false hw hcl0 hot_lt' hfals_ot
                                          (hot_def ▸ hent_bin)
                                      have hmap_lp : ((qi_l <<< (1 : Nat)) ||| pol).toNat =
                                          2 * qi_l.toNat + pol.toNat :=
                                        m6_bv32_shl1_or_pol qi_l pol (by omega) hpol_lt
                                      obtain ⟨hl_st, hlts_u, hent_u⟩ :=
                                        m6_cone_unit_tmp_prep (nv := nv_w) (qi0 := qi_l)
                                          (pol := pol) (u := (qi_l <<< (1 : Nat)) ||| pol) hb_w.hlen
                                          htmp_w0 (by omega) (by omega) hpol_lt (by omega) hmap_lp
                                          (by rw [hb_w.hwk]; exact hlit_eq.symm) hent_unit
                                      m6_steps
                                      have hcv_q' :
                                          st_l.scratch.work_stk1[(BitVec.setWidth 64 qi_l).toNat]'
                                            hqi_ws = cv := hcv_def.symm
                                      have hm_tmk0 :
                                          st_l.scratch.tarjan_mark[(BitVec.setWidth 64
                                            (st_l.scratch.work_stk1[(BitVec.setWidth 64
                                              qi_l).toNat]'hqi_ws)).toNat]'(by
                                                rw [hcv_q']; exact hcv_tmk) - 1#32 = qi_l := by
                                        rw [m6_list_getElem_congr
                                          (congrArg (fun x => (BitVec.setWidth 64 x).toNat) hcv_q')
                                          _ hcv_tmk, hmap_c]
                                      refine m8_cone_call_add_clause hAddCl (aSz := Arg.imm 1)
                                        (sz := 1#32) rfl hL_len hL_mv hl_st
                                        (m8ConeMask_upd_tmp _ hb_w.hag)
                                        (m8ConeInv_tmp_irrel hb_w.hcone) hncw_lt (by decide)
                                        (by
                                          rw [hl_st.core_ok.tmp_len_arr,
                                            ← hb_w.hlen.core_ok.tmp_len_arr]
                                          exact htmp_w0)
                                        hlts_u hent_u
                                        (m6_fullMem_tmp0_congr
                                          (congrArg (fun x : BitVec 32 =>
                                            (x <<< (1 : Nat)) ||| pol) hm_tmk0) hm)
                                        (fun ok st' m' hl' ha' hc' _ ht' hw' hm' => by
                                          m6_split
                                          · have hic := (m8_cone_load_kptr_hdr hc' hm').1
                                            m6_to_group
                                            refine wp_join_group (ts := [.bool])
                                              (fun (_lim', ()) m'' => m'' = m')
                                              (fun _ (lim', ()) m'' hm'' => by
                                                subst m''
                                                m6_steps
                                                exact hJ_ov (nc_w + 1#32, lim', ()) m'
                                                  ⟨st', ⟨hl', ha', by simpa only [hc, ↓reduceIte]
                                                    using hc', ht' ▸ hb_w.htmk, hw' ▸ hb_w.hwk⟩,
                                                   hm'⟩)
                                              (fun _ hJ_inc => by
                                                change wp _ _ _ _ _; c0_hsteps
                                                dsimp only [Prod.fst]
                                                try (first | rw [hkptr_c0] | rw [hkptr_c0_nat])
                                                try rw [show (BitVec.ofNat (OfNat.ofNat 64)
                                                    (OfNat.ofNat 6) : BitVec 64) = 6#64 from rfl]
                                                refine head_wp_load rfl hic ?_
                                                m6_split
                                                · m6_steps; exact hJ_inc (true, ()) m' rfl
                                                · m6_steps; exact hJ_inc (lim_w, ()) m' rfl)
                                          · m6_steps
                                            exact hJ_ov (nc_w, true, ()) m'
                                              ⟨st', ⟨hl', ha', by simpa only [hc,
                                                Bool.false_eq_true,
                                                ↓reduceIte] using hc', ht' ▸ hb_w.htmk,
                                                hw' ▸ hb_w.hwk⟩, hm'⟩))
                                · -- Unassigned `ov`
                                  have hov_tmk : (BitVec.setWidth 64 ov).toNat <
                                      st_w.scratch.tarjan_mark.length := by
                                    rw [htm_w, bv_c0_zext32_64]; omega
                                  have htm_w_idx :
                                      ∀ {j : Nat} (hj : j < st_w.scratch.tarjan_mark.length),
                                        j = ov.toNat →
                                        st_w.scratch.tarjan_mark[j]'hj =
                                          st_w.scratch.tarjan_mark[ov.toNat]'(by omega) :=
                                    fun _ hij => Option.some.inj (by subst hij; rfl)
                                  have hov_tmk_ws :
                                      (BitVec.setWidth 64
                                        ((st_w.core.wstk[p.toNat]'hp_wstk_w &&&
                                          (2147483647 : BitVec 32)) >>> (1 : Nat))).toNat <
                                        st_w.scratch.tarjan_mark.length := by
                                    rw [← hw0_def, show (2147483647 : BitVec 32) = 0x7FFFFFFF#32
                                        from rfl, ← hot_def, ← hov_def]
                                    exact hov_tmk
                                  m6_to_group
                                  refine wp_join_group (ts := [])
                                    (fun () md => md = mw)
                                    (fun _ () md hmd => by
                                      subst md
                                      clear hslice hslice1 hwv0_eq hwv1_eq h2l_mod h2l1_mod
                                        hw0_s hbin hnot_pos
                                      obtain ⟨saved_nv, hsav_eq⟩ : ∃ saved_nv : BitVec 32,
                                          saved_nv = nv_w := ⟨_, rfl⟩
                                      obtain ⟨scr_sav, hscr_sav_eq⟩ :
                                          ∃ scr_sav : List (BitVec 32),
                                            scr_sav = st_w.scratch.scratch_buf := ⟨_, rfl⟩
                                      have hsav_ge1 : 1 ≤ saved_nv.toNat :=
                                        hsav_eq ▸ hb_w.hcone.nv_ge1
                                      have hbdd_sav : K6LitsBounded saved_nv.toNat
                                          (k6StateOfScratch L scr_sav) :=
                                        hsav_eq ▸ hscr_sav_eq ▸ hb_w.hcone.k6_bdd
                                      have htrl_sav : ∀ l ∈ k6TrailLits (k6StateOfScratch L
                                          scr_sav), l < 2 * saved_nv.toNat :=
                                        hsav_eq ▸ hscr_sav_eq ▸ hb_w.hcone.k6_trl_bdd
                                      m6_to_group
                                      refine wp_join_group (ts := [i32, .bool])
                                        (fun (nv_a, _lim_a, ()) m_a => ∃ st_a : FullState,
                                          M8ConeSavedBase F_cur L c s cv qi_l saved_nv
                                            st_w.scratch.work_stk1 scr_sav
                                            nv_a.toNat nc_w.toNat st_a
                                          ∧ st_a.scratch.tarjan_mark[ov.toNat]?.getD 0#32 ≠ 0#32 ∧
                                          (FullMem c st_a ⋆ R) m_a)
                                        (fun _ (nv_a, lim_a, ()) m_a ⟨st_a, hs_a, htoa, hma⟩ => by
                                          have htm_a := hs_a.hlen.scratch_ok.tarjan_mark_len
                                          have htmp_a := hs_a.hlen.core_ok.tmp_len_arr
                                          have hcv_a := m8_hag_cur_vars hs_a.hag
                                          rcases hs_a.hcone.rev ov.toNat
                                              (by rw [hcv_a]; exact hov_lt)
                                            with hz | ⟨iov, hiov, hwov, htov⟩
                                          · exact absurd hz htoa
                                          obtain ⟨hl0_lt, hl1_lt, hlift0, hlift1⟩ :=
                                            m6_cone_bin_lits_ok (Nat.lt_of_lt_of_le
                                              (by omega : qi_l.toNat < nv_w.toNat)
                                              (hsav_eq ▸ hs_a.hsav_le))
                                              (by have := hs_a.hcone.nv_leMax; omega)
                                              hpol_lt hlit_eq
                                              hov_eq hiov hs_a.htmk hs_a.hwk htov hwov
                                          have hcv_tm : cv.toNat <
                                              st_a.scratch.tarjan_mark.length := by omega
                                          have hov_tm : ov.toNat <
                                              st_a.scratch.tarjan_mark.length := by omega
                                          have hov_tm_a : (BitVec.setWidth 64 ov).toNat <
                                              st_a.scratch.tarjan_mark.length := by
                                            rw [htm_a, bv_c0_zext32_64]; omega
                                          rw [List.getElem?_eq_getElem hcv_tm, Option.getD_some]
                                            at hl0_lt hlift0
                                          rw [List.getElem?_eq_getElem hov_tm, Option.getD_some]
                                            at hl1_lt hlift1
                                          let l0_b := (qi_l <<< (1 : Nat)) ||| pol
                                          let l1_b := ((st_a.scratch.tarjan_mark[(BitVec.setWidth
                                            64 ov).toNat]'hov_tm_a - 1#32) <<< (1 : Nat)) |||
                                            (ot &&& 1#32)
                                          have htmp_a1 : 1 < st_a.core.tmp.length := by
                                            have := hs_a.hcone.nv_le_cv
                                            have := hs_a.hlen.core_ok.cur_vars_le
                                            have hne_cv_ov : cv.toNat ≠ ov.toNat := fun heq =>
                                              hov_ne_cv (BitVec.eq_of_toNat_eq heq.symm)
                                            omega
                                          let st_ab : FullState :=
                                            { st_a with core := { st_a.core with
                                              tmp := (st_a.core.tmp.set 0 l0_b).set 1 l1_b } }
                                          have hl0_eq : l0_b =
                                              ((st_a.scratch.tarjan_mark[cv.toNat]'hcv_tm -
                                                1#32) <<< (1 : Nat)) ||| pol := by
                                            dsimp only [l0_b]
                                            have ha : st_a.scratch.tarjan_mark[cv.toNat]'hcv_tm =
                                                BitVec.ofNat 32 (qi_l.toNat + 1) := by
                                              simpa only [List.getElem?_eq_getElem hcv_tm,
                                                Option.getD_some] using hs_a.htmk
                                            rw [ha, m6_bv32_ofNat_add1_sub1]
                                          have htm_ov_idx : st_a.scratch.tarjan_mark[
                                              (BitVec.setWidth 64 ov).toNat]'hov_tm_a =
                                              st_a.scratch.tarjan_mark[ov.toNat]'hov_tm :=
                                            m6_list_getElem_congr (bv_c0_zext32_64 ov)
                                              hov_tm_a hov_tm
                                          obtain ⟨hlen_ab, hlts_ab, hent_ab⟩ :=
                                            m6_cone_bin_tmp_prep (l1_b := l1_b) hs_a.hlen htmp_a1
                                              (hl0_eq ▸ hl0_lt)
                                              (by dsimp only [l1_b]; rw [htm_ov_idx]; exact hl1_lt)
                                              (hl0_eq ▸ hlift0)
                                              (by
                                                dsimp only [l1_b]
                                                rw [htm_ov_idx, hlift1, hot_def])
                                              hent_bin
                                          have htmp_a0 : 0 < st_a.core.tmp.length :=
                                            Nat.lt_trans Nat.zero_lt_one htmp_a1
                                          have hov_tm_a_ws :
                                              (BitVec.setWidth 64
                                                ((st_w.core.wstk[p.toNat]'hp_wstk_w &&&
                                                  (2147483647 : BitVec 32)) >>> (1 : Nat))).toNat <
                                                st_a.scratch.tarjan_mark.length := by
                                            rw [← hw0_def, show (2147483647 : BitVec 32) =
                                                0x7FFFFFFF#32 from rfl, ← hot_def, ← hov_def]
                                            exact hov_tm_a
                                          m6_to_group
                                          refine wp_join_group (ts := [i32, i32, .bool])
                                              (fun (nv_b, nc_b, _lim_b, ()) m_b =>
                                                layer_end.toNat ≤ nv_b.toNat ∧ ∃ st_b : FullState,
                                                  M8ConeBase F_cur L c s cv qi_l nv_b.toNat
                                                    nc_b.toNat st_b ∧
                                                  (FullMem c st_b ⋆ R) m_b) ?_ ?_
                                          · rintro _ ⟨nv_b, nc_b, lim_b, ⟨⟩⟩ m_b
                                              ⟨hnvb, st_b, hbb, hmb⟩
                                            m6_steps
                                            exact hstep_bin nv_b nc_b lim_b st_b m_b hnvb hbb hmb
                                          · intro _ hJ_bin
                                            m6_steps
                                            have hcv_q' :
                                                st_l.scratch.work_stk1[(BitVec.setWidth 64
                                                  qi_l).toNat]'hqi_ws = cv := hcv_def.symm
                                            have hm_tmk0 :
                                                st_l.scratch.tarjan_mark[(BitVec.setWidth 64
                                                  (st_l.scratch.work_stk1[(BitVec.setWidth 64
                                                    qi_l).toNat]'hqi_ws)).toNat]'(by
                                                      rw [hcv_q']
                                                      exact hcv_tmk) - 1#32 = qi_l := by
                                              rw [m6_list_getElem_congr
                                                (congrArg (fun x => (BitVec.setWidth 64 x).toNat)
                                                  hcv_q')
                                                _ hcv_tmk, hmap_c]
                                            have hl1_c0 : ∀ {pf1 pf2},
                                                ((st_a.scratch.tarjan_mark[(BitVec.setWidth 64
                                                  ((st_w.core.wstk[p.toNat]'pf1 &&&
                                                    2147483647#32) >>> OfNat.ofNat 1)).toNat]'pf2 -
                                                  1#32) <<< (1 : Nat)) |||
                                                  ((st_w.core.wstk[p.toNat]'pf1 &&&
                                                    2147483647#32) &&& 1#32) = l1_b := by
                                              intro pf1 pf2
                                              have hidx : (BitVec.setWidth 64
                                                  ((st_w.core.wstk[p.toNat]'pf1 &&&
                                                    2147483647#32) >>> OfNat.ofNat 1)).toNat =
                                                  (BitVec.setWidth 64 ov).toNat := by
                                                rw [← hw0_def, show (2147483647#32 : BitVec 32) =
                                                    0x7FFFFFFF#32 from rfl, ← hot_def]
                                                change (BitVec.setWidth 64 (ot >>>
                                                  (1 : Nat))).toNat = (BitVec.setWidth 64 ov).toNat
                                                rw [← hov_def]
                                              have hot1 : ((st_w.core.wstk[p.toNat]'pf1 &&&
                                                  2147483647#32) &&& 1#32) = (ot &&& 1#32) := by
                                                rw [← hw0_def, show (2147483647#32 : BitVec 32) =
                                                    0x7FFFFFFF#32 from rfl, ← hot_def]
                                              dsimp only [l1_b]
                                              rw [m6_list_getElem_congr hidx pf2 hov_tm_a, hot1]
                                            refine m8_cone_call_add_clause hAddCl
                                              (aSz := Arg.imm 2) (sz := 2#32) rfl hL_len hL_mv
                                              hlen_ab (m8ConeMask_upd_tmp _ hs_a.hag)
                                              (m8ConeInv_tmp_irrel hs_a.hcone) hncw_lt (by decide)
                                              (by
                                                rw [hlen_ab.core_ok.tmp_len_arr, ← htmp_a]
                                                exact htmp_a1)
                                              hlts_ab hent_ab
                                              (m6_fullMem_tmp01_congr
                                                (congrArg (fun x : BitVec 32 =>
                                                  (x <<< (1 : Nat)) ||| pol) hm_tmk0)
                                                hl1_c0 ‹(FullMem c _ ⋆ R) _›)
                                              (fun ok st' m' hl' ha' hc' hfalse_scr ht' hw'
                                                hm' => by
                                                m6_split
                                                · m6_steps
                                                  exact hJ_bin (nv_a, nc_w + (1 : BitVec 32),
                                                      lim_a, ())
                                                    m' ⟨Nat.le_trans hnv_w_mono
                                                        (hsav_eq ▸ hs_a.hsav_le),
                                                      st', ⟨hl', ha',
                                                        by
                                                          rw [show (1 : BitVec 32) = 1#32 from rfl]
                                                          simpa only [hc, ↓reduceIte] using hc',
                                                        ht' ▸ hs_a.htmk, hw' ▸ hs_a.hwk⟩, hm'⟩
                                                · have hs'_saved : M8ConeSavedBase F_cur L c s
                                                      cv qi_l saved_nv st_w.scratch.work_stk1
                                                      scr_sav nv_a.toNat nc_w.toNat st' :=
                                                    ⟨⟨hl', ha', by simpa only
                                                        [hc, Bool.false_eq_true, ↓reduceIte]
                                                        using hc', ht' ▸ hs_a.htmk,
                                                        hw' ▸ hs_a.hwk⟩,
                                                      hs_a.hsav_le,
                                                      (hfalse_scr (by cases ok <;> simp at hc ⊢)
                                                        ).trans hs_a.hscr,
                                                      hw' ▸ hs_a.hws⟩
                                                  m6_to_group
                                                  refine wp_loop_inv (ts := [i32])
                                                    (fun (nv_r, ()) mr =>
                                                      nv_r.toNat ≤ nv_a.toNat ∧
                                                      ∃ st_r : FullState,
                                                        M8ConeSavedBase F_cur L c s cv qi_l
                                                          saved_nv st_w.scratch.work_stk1
                                                          scr_sav nv_r.toNat nc_w.toNat st_r ∧
                                                        (FullMem c st_r ⋆ R) mr)
                                                    (fun (nv_r, ()) _ =>
                                                      nv_r.toNat - saved_nv.toNat)
                                                    (fun _ hJr => by
                                                      m6_steps
                                                      exact hJr (nv_a, ()) m'
                                                        ⟨le_refl _, st', hs'_saved, hm'⟩)
                                                    (fun _ (nv_r, ()) mr ⟨hle_a, st_r, hs_r,
                                                        hmr⟩ hJr => by
                                                      m6_split
                                                      · have hsav_lt :
                                                          saved_nv.toNat < nv_r.toNat := by
                                                          rw [hsav_eq]; exact hc
                                                        obtain ⟨hnv1, hvr_lt, hstep⟩ :=
                                                          m8_coneBase_of_rollback_step hs_r
                                                            hsav_ge1 hsav_lt
                                                            (by
                                                              rw [hsav_eq]
                                                              exact Nat.lt_of_lt_of_le hqi_l_lt
                                                                hnv_w_mono)
                                                            hbdd_sav htrl_sav
                                                        obtain ⟨hvr_tmk_bd, hs'⟩ := hstep hvr_lt
                                                        m6_steps
                                                        refine hJr (nv_r - 1#32, ()) _
                                                          (by
                                                            dsimp only
                                                            exact m6_nat_sub_lo1_lt hsav_lt
                                                              hnv1)
                                                          ⟨hnv1 ▸ le_trans (Nat.sub_le _ _)
                                                            hle_a, _, hs', ?_⟩
                                                        try rw [m6_tmk_set_mod64] at hm
                                                        exact m8_cone_rollback_mem_step _ hvr_lt
                                                          (m6_bv32_sub1_zext_toNat nv_r) hm
                                                      · have hnv_le_sav :
                                                          nv_r.toNat ≤ saved_nv.toNat := by
                                                          rw [hsav_eq]
                                                          exact Nat.le_of_not_lt hc
                                                        m6_steps
                                                        have hnv_eq : nv_r = saved_nv :=
                                                          BitVec.eq_of_toNat_eq
                                                            (Nat.le_antisymm hnv_le_sav
                                                              hs_r.hsav_le)
                                                        have hle_nv_r :
                                                            layer_end.toNat ≤ nv_r.toNat := by
                                                          rw [hnv_eq, hsav_eq]; exact hnv_w_mono
                                                        exact hJ_bin (nv_r, nc_w, true, ()) mr
                                                          ⟨hle_nv_r, st_r,
                                                           hnv_eq ▸ hs_r.toM8ConeBase, hmr⟩)))
                                        (fun _ hJ_a => by
                                          m6_split
                                          · have hmiss : st_w.scratch.tarjan_mark[ov.toNat]?.getD
                                                0#32 = 0#32 := by
                                              rw [List.getElem?_eq_getElem (by omega),
                                                Option.getD_some]
                                              rw [htm_w_idx _ (by
                                                rw [← hw0_def,
                                                  show (2147483647 : BitVec 32) = 0x7FFFFFFF#32
                                                    from rfl,
                                                  ← hot_def]
                                                change (BitVec.setWidth 64 (ot >>>
                                                  (1 : Nat))).toNat = ov.toNat
                                                rw [← hov_def, bv_c0_zext32_64])] at hc
                                              exact hc
                                            m6_split
                                            · m6_steps
                                              exact hJ_we (nv_w, nc_w, true, p + 1#64, ()) mw
                                                ⟨hnv_w_mono, st_w, hb_w, hmw⟩
                                            · have hnv_lt_max : nv_w.toNat < 256 := by
                                                have : ¬ 256 ≤ nv_w.toNat := hc
                                                omega
                                              have hqi_nv_w : qi_l.toNat < nv_w.toNat :=
                                                Nat.lt_of_lt_of_le hqi_l_lt hnv_w_mono
                                              have hs_w_sav : M8ConeSavedBase F_cur L c s cv qi_l
                                                  saved_nv st_w.scratch.work_stk1 scr_sav
                                                  nv_w.toNat nc_w.toNat st_w :=
                                                ⟨hb_w, hsav_eq ▸ le_refl _, hscr_sav_eq.symm,
                                                 fun _ _ => rfl⟩
                                              obtain ⟨hnv_w_lt, hnv1, hne_nv_qi, hne_cv, hs_a,
                                                htlva⟩ :=
                                                m8_cone_push_var_base_ok hs_w_sav hnv_lt_max
                                                  hov_lt hmiss hqi_nv_w
                                              have hnv_ws : (BitVec.setWidth 64 ((nv_w + 1#32) -
                                                  1#32)).toNat < st_w.scratch.work_stk1.length := by
                                                rw [hwk_w_len, bv_c0_zext32_64,
                                                  m6_bv32_add1_sub1_eq nv_w]; omega
                                              m6_steps
                                              let st_a : FullState :=
                                                { st_w with scratch :=
                                                  { st_w.scratch with
                                                    tarjan_mark := st_w.scratch.tarjan_mark.set
                                                      ov.toNat (nv_w + 1#32)
                                                    work_stk1 := st_w.scratch.work_stk1.set
                                                      nv_w.toNat ov } }
                                              have h2 := m6_bv32_add1_sub1_toNat nv_w
                                              have htm_idx : (BitVec.setWidth 64
                                                  ((st_w.core.wstk[p.toNat]'hp_wstk_w &&&
                                                    2147483647#32) >>> OfNat.ofNat 1)).toNat =
                                                  ov.toNat := by
                                                rw [← hw0_def, show (2147483647#32 : BitVec 32) =
                                                    0x7FFFFFFF#32 from rfl, ← hot_def]
                                                change (BitVec.setWidth 64 (ot >>>
                                                  (1 : Nat))).toNat = ov.toNat
                                                rw [← hov_def, bv_c0_zext32_64]
                                              have hws_val :
                                                  ((st_w.core.wstk[p.toNat]'hp_wstk_w &&&
                                                    2147483647#32) >>> OfNat.ofNat 1) = ov := by
                                                rw [← hw0_def, show (2147483647#32 : BitVec 32) =
                                                    0x7FFFFFFF#32 from rfl, ← hot_def]
                                                exact hov_def.symm
                                              have hm_a : (FullMem c st_a ⋆ R) m := by
                                                have hm' := hm
                                                dsimp only [LeanQbe.T.lift2, Arg.val_var,
                                                  Arg.val_imm] at hm'
                                                try rw [show (2147483647 : BitVec 32) =
                                                    2147483647#32 from rfl] at hm'
                                                try rw [hws_val] at hm'
                                                try rw [show (1 : BitVec 32) = 1#32 from rfl] at hm'
                                                try rw [htm_idx] at hm'
                                                repeat rw [bv_c0_zext32_64] at hm'
                                                try rw [h2] at hm'
                                                exact hm'
                                              exact hJ_a (nv_w + 1#32, lim_w, ()) m
                                                ⟨st_a, hnv1 ▸ hs_a, htlva, hm_a⟩
                                          · have hne_ov : st_w.scratch.tarjan_mark[ov.toNat]?.getD
                                                0#32 ≠ 0#32 := by
                                              rw [List.getElem?_eq_getElem (by omega),
                                                Option.getD_some]
                                              rw [htm_w_idx _ (by
                                                rw [← hw0_def,
                                                  show (2147483647 : BitVec 32) = 0x7FFFFFFF#32
                                                    from rfl,
                                                  ← hot_def]
                                                change (BitVec.setWidth 64 (ot >>>
                                                  (1 : Nat))).toNat = ov.toNat
                                                rw [← hov_def, bv_c0_zext32_64])] at hc
                                              exact hc
                                            m6_steps
                                            exact hJ_a (nv_w, lim_w, ()) mw
                                              ⟨st_w, ⟨hb_w, hsav_eq ▸ le_refl _, hscr_sav_eq.symm,
                                                fun _ _ => rfl⟩, hne_ov, hmw⟩))
                                    (fun _ hJ_d => by
                                      m6_split
                                      · m6_split
                                        · m6_steps
                                          exact hstep_bin nv_w nc_w lim_w st_w mw hnv_w_mono
                                            hb_w hmw
                                        · m6_steps; exact hJ_d () mw rfl
                                      · m6_steps; exact hJ_d () mw rfl)))))))

    · intro _ hJ_mc
      m6_split
      · exfalso
        have : (mv * 3#32).toNat < 1024 := hc
        rw [hmo_nat] at this
        unfold K6Layout.maxOrig at this
        omega
      · m6_steps; exact hJ_mc (1024#32, ()) _ ⟨rfl, hmm⟩
  · intro _ hJ_mv
    m6_split
    · exfalso; have : mv.toNat < 256 := hc; omega
    · m6_steps; exact hJ_mv (256#32, ()) _ ⟨rfl, hm⟩

end LeanQbe.T.Examples.Kissat.FullM8SweepV2

end
