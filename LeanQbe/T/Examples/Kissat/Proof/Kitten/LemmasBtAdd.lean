/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Kitten.LemmasWatch

/-!
# Backtrack Loop, `init`, & `add_clause` Invariant Lemmas (`Kissat.Proof.Kitten.LemmasBtAdd`)

Covers `K6BtLoopInv` (`init`/`step`/`finish`), `k6Init_finish_inv`, and `k6AddClause_ge2_preserves`.

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

/-! ## 1. Backtrack Loop Invariant (`K6BtLoopInv`) -/

structure K6BtUnchanged (ks st : K6State) : Prop where
  nv_eq : st.nv = ks.nv
  nc_eq : st.nc = ks.nc
  lvl_eq : st.lvl = ks.lvl
  prop_eq : st.prop = ks.prop
  te_hdr : st.trl_end = ks.trl_end
  inc_eq : st.incons = ks.incons
  alen_eq : st.alen = ks.alen
  acap_eq : st.acap = ks.acap
  na_eq : st.nassump = ks.nassump
  nk_eq : st.nkl = ks.nkl
  nan_eq : st.nana = ks.nana
  st_eq : st.status = ks.status
  ph_eq : st.phase = ks.phase
  op_eq : st.openCnt = ks.openCnt
  mv_eq : st.max_v = ks.max_v
  mo_eq : st.max_orig = ks.max_orig
  mc_eq : st.max_cl = ks.max_cl
  nq_eq : st.neq = ks.neq
  ht_eq : st.hdrTail = ks.hdrTail
  qs_eq : st.qstampArr = ks.qstampArr
  trl_eq : st.trl = ks.trl
  fl_eq : st.flags = ks.flags
  ass_eq : st.assump = ks.assump
  ana_eq : st.ana = ks.ana
  kl_eq : st.kl = ks.kl
  wh_eq : st.whead = ks.whead
  wn_eq : st.wnext = ks.wnext
  wb_eq : st.wblit = ks.wblit
  co_eq : st.clOff = ks.clOff
  cs_eq : st.clSz = ks.clSz
  ar_eq : st.arena = ks.arena

local macro "k6bt_unchanged " h:ident : tactic =>
  `(tactic| exact ⟨by k6_field; exact ($h).nv_eq, by k6_field; exact ($h).nc_eq,
    by k6_field; exact ($h).lvl_eq, by k6_field; exact ($h).prop_eq,
    by k6_field; exact ($h).te_hdr, by k6_field; exact ($h).inc_eq,
    by k6_field; exact ($h).alen_eq, by k6_field; exact ($h).acap_eq,
    by k6_field; exact ($h).na_eq, by k6_field; exact ($h).nk_eq,
    by k6_field; exact ($h).nan_eq, by k6_field; exact ($h).st_eq,
    by k6_field; exact ($h).ph_eq, by k6_field; exact ($h).op_eq,
    by k6_field; exact ($h).mv_eq, by k6_field; exact ($h).mo_eq,
    by k6_field; exact ($h).mc_eq, by k6_field; exact ($h).nq_eq,
    by k6_field; exact ($h).ht_eq, by k6_field; exact ($h).qs_eq,
    by k6_field; exact ($h).trl_eq, by k6_field; exact ($h).fl_eq,
    by k6_field; exact ($h).ass_eq, by k6_field; exact ($h).ana_eq,
    by k6_field; exact ($h).kl_eq, by k6_field; exact ($h).wh_eq,
    by k6_field; exact ($h).wn_eq, by k6_field; exact ($h).wb_eq,
    by k6_field; exact ($h).co_eq, by k6_field; exact ($h).cs_eq,
    by k6_field; exact ($h).ar_eq⟩)

theorem K6BtUnchanged.putHdr_bt {ks st : K6State} (h : K6BtUnchanged ks st) (f : K6HdrField)
    (hf : f = .unass ∨ f = .qsearch) (v : BitVec 32) : K6BtUnchanged ks (st.putHdr f v) := by
  rcases hf with rfl | rfl <;> k6bt_unchanged h

theorem K6BtUnchanged.putArr_bt {ks st : K6State} (h : K6BtUnchanged ks st) (f : K6ArrField)
    (hf : f = .vals ∨ f = .lvlArr ∨ f = .rsn) (i : Nat) (v : BitVec 32) :
    K6BtUnchanged ks (st.putArr f i v) := by
  rcases hf with rfl | rfl | rfl <;> k6bt_unchanged h

structure K6BtLoopInv (L : K6Layout) (ks : K6State) (target_lvl te : BitVec 32)
    (st : K6State) : Prop where
  sh : st.ShapesOk L
  te_le : te.toNat ≤ ks.trl_end.toNat
  unass_eq : st.unass.toNat + te.toNat = ks.nv.toNat
  eqs : K6BtUnchanged ks st
  kept_var : ∀ w < ks.nv.toNat, (∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = w) →
    st.lvlArr[w]? = ks.lvlArr[w]? ∧ st.rsn[w]? = ks.rsn[w]? ∧
    st.vals[2 * w]? = ks.vals[2 * w]? ∧ st.vals[2 * w + 1]? = ks.vals[2 * w + 1]?
  cleared_var : ∀ w < ks.nv.toNat, (¬ ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = w) →
    st.lvlArr[w]? = some 0#32 ∧ st.rsn[w]? = some 0xFFFFFFFF#32 ∧
    st.vals[2 * w]? = some 0#32 ∧ st.vals[2 * w + 1]? = some 0#32
  popped_gt : ∀ i, te.toNat ≤ i → i < ks.trl_end.toNat →
    target_lvl.toNat < (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat

theorem K6BtLoopInv.trl_eq {L : K6Layout} {ks : K6State} {target_lvl te : BitVec 32}
    {st : K6State} (h : K6BtLoopInv L ks target_lvl te st) : st.trl = ks.trl :=
  h.eqs.trl_eq

theorem k6BtLoopInv_init {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    {target_lvl : BitVec 32} (hinv : K6Inv L P ks) :
    K6BtLoopInv L ks target_lvl ks.trl_end ks :=
  ⟨hinv.shapes, Nat.le_refl _, hinv.assign.unass_eq,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   fun _ _ _ => ⟨rfl, rfl, rfl, rfl⟩,
   fun w hw hno => by
     have hz : ks.vals[2 * w]?.getD 0#32 = 0#32 := by
       by_cases hcz : ks.vals[2 * w]?.getD 0#32 = 0#32
       · exact hcz
       · obtain ⟨i, hi, hie⟩ := (hinv.assign.vals_nz_iff_trl (2 * w) (by omega)).mp hcz
         exact absurd ⟨i, hi, by simpa using hie⟩ hno
     have hzo := hinv.assign.unass_lvl_zero w hw hz
     have hz1 := k6_vals_xor1_zero hinv (by omega : 2 * w < 2 * ks.nv.toNat) hz
     rw [show (2 * w) ^^^ 1 = 2 * w + 1 by
       rcases k6_nat_xor1_cases (2 * w) with ⟨_, _⟩ | ⟨_, _⟩ <;> omega] at hz1
     have := hinv.clauses.nv_le
     have hv0_len : 2 * w < ks.vals.length := by rw [hinv.shapes.vals_len]; omega
     have hv1_len : 2 * w + 1 < ks.vals.length := by rw [hinv.shapes.vals_len]; omega
     have hl_len : w < ks.lvlArr.length := by rw [hinv.shapes.lvlArr_len]; omega
     have hr_len : w < ks.rsn.length := by rw [hinv.shapes.rsn_len]; omega
     rw [List.getElem?_eq_getElem hl_len, List.getElem?_eq_getElem hr_len] at hzo
     rw [List.getElem?_eq_getElem hv0_len] at hz; rw [List.getElem?_eq_getElem hv1_len] at hz1
     exact ⟨by rw [List.getElem?_eq_getElem hl_len]; simpa using hzo.1,
       by rw [List.getElem?_eq_getElem hr_len]; simpa using hzo.2,
       by rw [List.getElem?_eq_getElem hv0_len]; simpa using hz,
       by rw [List.getElem?_eq_getElem hv1_len]; simpa using hz1⟩,
   fun _ h1 h2 => absurd (Nat.lt_of_le_of_lt h1 h2) (Nat.lt_irrefl _)⟩

theorem K6BtLoopInv.put_qsearch {L : K6Layout} {ks : K6State} {target_lvl te : BitVec 32}
    {st : K6State} (h : K6BtLoopInv L ks target_lvl te st) (qs : BitVec 32) :
    K6BtLoopInv L ks target_lvl te (st.putHdr .qsearch qs) :=
  ⟨h.sh.putHdr .qsearch qs, h.te_le, by k6_field; exact h.unass_eq,
   h.eqs.putHdr_bt .qsearch (Or.inr rfl) qs,
   fun w hw hex => by k6_field; exact h.kept_var w hw hex,
   fun w hw hno => by k6_field; exact h.cleared_var w hw hno, h.popped_gt⟩

theorem k6BtLoopInv_step {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    {target_lvl te : BitVec 32} {st : K6State} (hinv : K6Inv L P ks)
    (hbt : K6BtLoopInv L ks target_lvl te st) (hpos : 0 < te.toNat)
    (hpop : target_lvl.toNat <
      (st.lvlArr[(ks.trl[te.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) :
    let lit := ks.trl[te.toNat - 1]?.getD 0#32
    let v := (lit >>> 1).toNat
    let st' := ((((st.putArr .vals lit.toNat 0#32).putArr .vals (lit ^^^ 1#32).toNat 0#32).putArr
      .lvlArr v 0#32).putArr .rsn v 0xFFFFFFFF#32).putHdr .unass (st.unass + 1#32)
    K6BtLoopInv L ks target_lvl (te - 1#32) st' ∧
    ∀ qs, K6BtLoopInv L ks target_lvl (te - 1#32) (st'.putHdr .qsearch qs) := by
  intro lit v st'; have := L.hmaxV; have hnv := hinv.clauses.nv_le
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; omega
  have hte1_lt : te.toNat - 1 < ks.trl_end.toNat := by have := hbt.te_le; omega
  have hlit_lt : lit.toNat < 2 * ks.nv.toNat :=
    hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hte1_lt htrl_len)
  have hv_eq : v = lit.toNat / 2 := (k6_bv32_div2_lt hlit_lt).1
  have hv_lt : v < ks.nv.toNat := by omega
  have hnl_eq : (lit ^^^ 1#32).toNat = lit.toNat ^^^ 1 := by simp
  have hsh' : st'.ShapesOk L :=
    ((((hbt.sh.putArr .vals _ _).putArr .vals _ _).putArr .lvlArr _ _).putArr
      .rsn _ _).putHdr .unass _
  have hun_lt : st.unass.toNat + 1 < 2 ^ 32 := by have := hbt.unass_eq; omega
  have hte_sub : (te - 1#32).toNat = te.toNat - 1 := by bv_omega
  have hun' : st'.unass.toNat + (te - 1#32).toNat = ks.nv.toNat := by
    have hun_st : st'.unass = st.unass + 1#32 := by dsimp only [st']; k6_field
    rw [hun_st, hte_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have := hbt.unass_eq; omega
  have hlvl_st : st'.lvlArr = st.lvlArr.set v 0#32 := by dsimp only [st']; k6_field
  have hrsn_st : st'.rsn = st.rsn.set v 0xFFFFFFFF#32 := by dsimp only [st']; k6_field
  have hvals_st : st'.vals = (st.vals.set lit.toNat 0#32).set (lit.toNat ^^^ 1) 0#32 := by
    dsimp only [st']; k6_field; rw [hnl_eq]
  have hl_xor := k6_nat_xor1_cases lit.toNat
  have heqs' : K6BtUnchanged ks st' :=
    ((((hbt.eqs.putArr_bt .vals (Or.inl rfl) _ _).putArr_bt .vals (Or.inl rfl) _ _).putArr_bt
      .lvlArr (Or.inr (Or.inl rfl)) _ _).putArr_bt .rsn (Or.inr (Or.inr rfl)) _ _).putHdr_bt
      .unass (Or.inl rfl) _
  have hstep : K6BtLoopInv L ks target_lvl (te - 1#32) st' := by
    refine ⟨hsh', by rw [hte_sub]; omega, hun', heqs', ?_, ?_, ?_⟩
    · intro w hw ⟨i, hi, hiw⟩
      have hi' : i < te.toNat - 1 := by rw [hte_sub] at hi; exact hi
      have hne_v : w ≠ v := by
        rw [← hiw, hv_eq]
        exact k6_trl_nodup_var_ne hinv.shapes hnv hinv.assign (Nat.lt_trans hi' (by omega)) hte1_lt
          (by omega)
      have hold := hbt.kept_var w hw ⟨i, by omega, hiw⟩
      rw [hlvl_st, hrsn_st, hvals_st, List.getElem?_set_ne (Ne.symm hne_v),
        List.getElem?_set_ne (Ne.symm hne_v)]
      rcases hl_xor with ⟨_, _⟩ | ⟨_, _⟩ <;> exact ⟨hold.1, hold.2.1,
        by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hold.2.2.1,
        by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hold.2.2.2⟩
    · intro w hw hnone; by_cases hwv : w = v
      · subst hwv
        rw [hlvl_st, hrsn_st, hvals_st, List.getElem?_set_self (by rw [hbt.sh.lvlArr_len]; omega),
          List.getElem?_set_self (by rw [hbt.sh.rsn_len]; omega)]
        have hv0_len : 2 * v < st.vals.length := by rw [hbt.sh.vals_len]; omega
        have hv1_len : 2 * v + 1 < st.vals.length := by rw [hbt.sh.vals_len]; omega
        rcases hl_xor with ⟨h0a, h1a⟩ | ⟨h0a, h1a⟩
        · exact ⟨rfl, rfl, by rw [h1a, h0a, ← hv_eq, List.getElem?_set_ne (by omega),
            List.getElem?_set_self hv0_len],
            by rw [h1a, ← hv_eq, List.getElem?_set_self (by simp [hv1_len])]⟩
        · exact ⟨rfl, rfl, by rw [h1a, ← hv_eq, List.getElem?_set_self (by simp [hv0_len])],
            by rw [h1a, h0a, ← hv_eq, List.getElem?_set_ne (by omega),
              List.getElem?_set_self hv1_len]⟩
      · have hnone_old : ¬ ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = w := by
          rintro ⟨i, hi, hiw⟩; by_cases hie : i = te.toNat - 1
          · subst hie; exact hwv (by rw [hv_eq]; exact hiw.symm)
          · exact hnone ⟨i, by rw [hte_sub]; omega, hiw⟩
        have hold := hbt.cleared_var w hw hnone_old
        rw [hlvl_st, hrsn_st, hvals_st, List.getElem?_set_ne (Ne.symm hwv),
          List.getElem?_set_ne (Ne.symm hwv)]
        rcases hl_xor with ⟨_, _⟩ | ⟨_, _⟩ <;> exact ⟨hold.1, hold.2.1,
          by rw [List.getElem?_set_ne (by omega),
            List.getElem?_set_ne (by omega)]; exact hold.2.2.1,
          by rw [List.getElem?_set_ne (by omega),
            List.getElem?_set_ne (by omega)]; exact hold.2.2.2⟩
    · intro i hlo hhi; rw [hte_sub] at hlo; by_cases hie : i = te.toNat - 1
      · subst hie
        rw [(hbt.kept_var (lit.toNat / 2) (by omega) ⟨te.toNat - 1, by omega, rfl⟩).1] at hpop
        exact hpop
      · exact hbt.popped_gt i (by omega) hhi
  exact ⟨hstep, fun qs => hstep.put_qsearch qs⟩

theorem k6BtLoopInv_finish {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    {target_lvl te : BitVec 32} {st : K6State} (hinv : K6Inv L P ks)
    (hbt : K6BtLoopInv L ks target_lvl te st) (hsync_below : target_lvl = 0#32 ∨ K6TrailSynced ks)
    (hexit : te = 0#32 ∨ ∃ i < te.toNat, i = te.toNat - 1 ∧
      (st.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat) :
    let st' := ((st.putHdr .trl_end te).putHdr .prop
      (if te.toNat < st.prop.toNat then te else st.prop)).putHdr .lvl target_lvl
    K6Inv L P st' ∧ K6TrailSynced st' ∧ st'.lvl = target_lvl ∧
    st'.trl_end.toNat ≤ ks.trl_end.toNat ∧ K6BtPreserved ks st' ∧
    (∀ i < st'.trl_end.toNat,
      st'.trl[i]? = ks.trl[i]? ∧ st'.rsn[(st'.trl[i]?.getD 0#32).toNat / 2]? =
        ks.rsn[(st'.trl[i]?.getD 0#32).toNat / 2]? ∧
      (st'.lvlArr[(st'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat) := by
  intro st'; have := L.hmaxV; have hnv := hinv.clauses.nv_le
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; omega
  have hkept_lvl : ∀ i < te.toNat,
      (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat := by
    intro i hi; rcases hexit with rfl | ⟨j, hj, _, hle⟩
    · simp at hi
    · have hj_lt := Nat.lt_of_lt_of_le hj hbt.te_le
      have hlj := hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hj_lt htrl_len)
      rw [(hbt.kept_var _ (by omega) ⟨j, hj, rfl⟩).1] at hle
      exact Nat.le_trans (hinv.assign.trl_lvl_mono i j (by omega) hj_lt) hle
  have hsh' : st'.ShapesOk L := ((hbt.sh.putHdr .trl_end _).putHdr .prop _).putHdr .lvl _
  have e := hbt.eqs
  have e_te : st'.trl_end = te := by dsimp only [st']; k6_field
  have e_trl : st'.trl = ks.trl := by dsimp only [st']; k6_field; exact e.trl_eq
  have e_la : st'.lvlArr = st.lvlArr := by dsimp only [st']; k6_field
  have hpres : K6BtPreserved ks st' :=
    ⟨by dsimp only [st']; k6_field; exact e.nv_eq, by dsimp only [st']; k6_field; exact e.nc_eq,
     by dsimp only [st']; k6_field; exact e.inc_eq, by dsimp only [st']; k6_field; exact e.alen_eq,
     by dsimp only [st']; k6_field; exact e.acap_eq, by dsimp only [st']; k6_field; exact e.na_eq,
     by dsimp only [st']; k6_field; exact e.nk_eq, by dsimp only [st']; k6_field; exact e.nan_eq,
     by dsimp only [st']; k6_field; exact e.st_eq, by dsimp only [st']; k6_field; exact e.ph_eq,
     by dsimp only [st']; k6_field; exact e.op_eq, by dsimp only [st']; k6_field; exact e.mv_eq,
     by dsimp only [st']; k6_field; exact e.mo_eq, by dsimp only [st']; k6_field; exact e.mc_eq,
     by dsimp only [st']; k6_field; exact e.nq_eq, by dsimp only [st']; k6_field; exact e.ht_eq,
     by dsimp only [st']; k6_field; exact e.ass_eq, by dsimp only [st']; k6_field; exact e.ana_eq,
     by dsimp only [st']; k6_field; exact e.kl_eq, by dsimp only [st']; k6_field; exact e.wh_eq,
     by dsimp only [st']; k6_field; exact e.wn_eq, by dsimp only [st']; k6_field; exact e.wb_eq,
     by dsimp only [st']; k6_field; exact e.co_eq, by dsimp only [st']; k6_field; exact e.cs_eq,
     by dsimp only [st']; k6_field; exact e.ar_eq,
     fun v _ => by dsimp only [st']; k6_field; rw [e.fl_eq],
     fun i hi => by
       rw [e_te] at hi
       have hli := hinv.assign.trl_lt _
         (k6_mem_trailLits_of_lt (Nat.lt_of_lt_of_le hi hbt.te_le) htrl_len)
       rw [e_la, e_trl]; exact (hbt.kept_var _ (by omega) ⟨i, hi, rfl⟩).1⟩
  have e_lvl : st'.lvl = target_lvl := by dsimp only [st']; k6_field
  have e_un : st'.unass = st.unass := by dsimp only [st']; k6_field
  have e_pr : st'.prop = if te.toNat < st.prop.toNat then te else st.prop := by
    dsimp only [st']; k6_field
  have e_rs : st'.rsn = st.rsn := by dsimp only [st']; k6_field
  have e_va : st'.vals = st.vals := by dsimp only [st']; k6_field
  have hcl' : K6ClausesOk L P st' :=
    k6ClausesOk_cast hinv.clauses hpres.acap hpres.max_v hpres.max_orig hpres.max_cl
      hpres.nv hpres.nc hpres.alen hpres.nassump (Or.inl hpres.incons) hpres.assump
      hpres.clOff hpres.clSz hpres.arena (Or.inl hpres.nkl) (Or.inl hpres.nana)
      (Or.inl (by dsimp only [st']; k6_field; exact e.fl_eq))
  have hw' : K6WatchesOk st' := by
    obtain ⟨ch, hch_len, hch_nd, hch_wc, hch_bnd⟩ := hinv.watches
    refine ⟨ch, hpres.nv ▸ hch_len, hch_nd, fun l hl => ?_, fun l hl w hw => ?_⟩
    · rw [hpres.nv] at hl; rw [hpres.wnext, hpres.whead]; exact hch_wc l hl
    · rw [hpres.nv] at hl
      simp only [k6ClauseSize, k6ClauseOff, k6ClauseLits, hpres.nv, hpres.nc, hpres.clSz,
        hpres.clOff, hpres.arena, hpres.wblit]; exact hch_bnd l hl w hw
  have hkept_vals : ∀ l, (∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = l / 2) →
      st.vals[l]? = ks.vals[l]? ∧ st.vals[l ^^^ 1]? = ks.vals[l ^^^ 1]? := fun l hex => by
    obtain ⟨i, hi, hiv⟩ := hex
    have := hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt (Nat.lt_of_lt_of_le hi hbt.te_le) htrl_len)
    have hkv := hbt.kept_var (l / 2) (by omega) ⟨i, hi, hiv⟩
    rcases k6_nat_xor1_cases l with ⟨he, hx⟩ | ⟨he, hx⟩
    · exact ⟨by rw [he]; exact hkv.2.2.1, by rw [hx]; exact hkv.2.2.2⟩
    · exact ⟨by rw [he]; exact hkv.2.2.2, by rw [hx]; exact hkv.2.2.1⟩
  have hcleared_vals : ∀ l, l / 2 < ks.nv.toNat →
      (¬ ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = l / 2) →
      st.vals[l]? = some 0#32 ∧ st.vals[l ^^^ 1]? = some 0#32 := fun l hl hno => by
    have hcv := hbt.cleared_var (l / 2) hl hno
    rcases k6_nat_xor1_cases l with ⟨he, hx⟩ | ⟨he, hx⟩
    · exact ⟨by rw [he]; exact hcv.2.2.1, by rw [hx]; exact hcv.2.2.2⟩
    · exact ⟨by rw [he]; exact hcv.2.2.2, by rw [hx]; exact hcv.2.2.1⟩
  have hsync' : K6TrailSynced st' := fun i hi => by
    rw [e_te] at hi; have hi_ks := Nat.lt_of_lt_of_le hi hbt.te_le
    let l := (ks.trl[i]?.getD 0#32).toNat; have hp := hkept_vals l ⟨i, hi, rfl⟩
    change st'.vals[(st'.trl[i]?.getD 0#32).toNat]? = some 1#32 ∧
      st'.vals[(st'.trl[i]?.getD 0#32).toNat ^^^ 1]? = some 2#32
    rw [e_trl, e_va]; change st.vals[l]? = some 1#32 ∧ st.vals[l ^^^ 1]? = some 2#32
    rw [hp.1, hp.2]
    rcases hsync_below with rfl | hsy
    · have hl_lt := hinv.assign.trl_lt l (k6_mem_trailLits_of_lt hi_ks htrl_len)
      have h0 :=
        hinv.assign.lvl0_ok i hi_ks
          (BitVec.eq_of_toNat_eq (Nat.eq_zero_of_le_zero (hkept_lvl i hi)))
      exact ⟨h0.1, h0.2.1⟩
    · exact hsy i hi_ks
  have hpf : k6TrailLits st' <+: k6TrailLits ks := by
    unfold k6TrailLits; rw [e_te, e_trl]
    exact List.IsPrefix.map BitVec.toNat (List.take_prefix_take_left hbt.te_le)
  have hba' : K6BaseAssignOk P st' := by
    refine ⟨by rw [e_te, hpres.nv]; exact Nat.le_trans hbt.te_le hinv.assign.trl_end_le,
      by rw [e_pr, e_te]; split <;> omega, by rw [e_un, e_te, hpres.nv]; exact hbt.unass_eq,
      ?_, ?_, ?_, hinv.assign.trl_nodup.sublist (hpf.map (· / 2)).sublist,
      fun l hl => hpres.nv ▸ hinv.assign.trl_lt l (hpf.subset hl), ?_, ?_, ?_, ?_, ?_⟩
    · intro l hl; rw [hpres.nv] at hl; rw [e_va]
      by_cases hex : ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = l / 2
      · rw [(hkept_vals l hex).1]; exact hinv.assign.vals_dom l hl
      · rw [(hcleared_vals l (by omega) hex).1]; left; rfl
    · intro l hl; rw [hpres.nv] at hl; rw [e_va]
      by_cases hex : ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = l / 2
      · have hp := hkept_vals l hex; rw [hp.1, hp.2]; exact hinv.assign.vals_neg_iff l hl
      · have hp := hcleared_vals l (by omega) hex; rw [hp.1, hp.2]; simp
    · intro l hl; rw [hpres.nv] at hl; rw [e_va, e_te, e_trl]
      by_cases hex : ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = l / 2
      · obtain ⟨i, hi, hiv⟩ := hex
        exact ⟨fun _ => ⟨i, hi, hiv⟩, fun _ => by
          rw [(hkept_vals l ⟨i, hi, hiv⟩).1]
          exact (hinv.assign.vals_nz_iff_trl l hl).mpr ⟨i, Nat.lt_of_lt_of_le hi hbt.te_le, hiv⟩⟩
      · have hp := hcleared_vals l (by omega) hex
        exact ⟨fun hnz => absurd (by rw [hp.1]; rfl) hnz, fun h => absurd h hex⟩
    · intro v hv; rw [hpres.nv] at hv; rw [e_la, e_lvl]
      by_cases hex : ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = v
      · obtain ⟨i, hi, rfl⟩ := hex; rw [(hbt.kept_var _ hv ⟨i, hi, rfl⟩).1]; exact hkept_lvl i hi
      · rw [(hbt.cleared_var v hv hex).1]; simp
    · intro v hv hz; rw [hpres.nv] at hv; rw [e_va] at hz; rw [e_la, e_rs]
      by_cases hex : ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = v
      · exfalso; obtain ⟨i, hi, hiv⟩ := hex; rw [(hbt.kept_var v hv ⟨i, hi, hiv⟩).2.2.1] at hz
        exact (hinv.assign.vals_nz_iff_trl (2 * v) (by omega)).mpr ⟨i,
          Nat.lt_of_lt_of_le hi hbt.te_le, by omega⟩ hz
      · have hcv := hbt.cleared_var v hv hex; rw [hcv.1, hcv.2.1]; exact ⟨rfl, rfl⟩
    · intro i j hij hj; rw [e_te] at hj; rw [e_la, e_trl]
      have hi_ks := Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hij hj) hbt.te_le
      have hj_ks := Nat.lt_of_lt_of_le hj hbt.te_le
      have hli := hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hi_ks htrl_len)
      have hlj := hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hj_ks htrl_len)
      rw [(hbt.kept_var _ (by omega) ⟨i, by omega, rfl⟩).1, (hbt.kept_var _ (by omega) ⟨j, hj,
        rfl⟩).1]
      exact hinv.assign.trl_lvl_mono i j hij hj_ks
    · intro i j hji hi hpos heq; rw [e_te] at hi; rw [e_la, e_trl] at hpos heq; rw [e_trl, e_rs]
      have hi_ks := Nat.lt_of_lt_of_le hi hbt.te_le
      have hj_ks := Nat.lt_of_lt_of_le (Nat.lt_trans hji hi) hbt.te_le
      have hli := hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hi_ks htrl_len)
      have hlj := hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hj_ks htrl_len)
      have hki := hbt.kept_var _ (by omega) ⟨i, hi, rfl⟩
      have hkj := hbt.kept_var _ (by omega) ⟨j, Nat.lt_trans hji hi, rfl⟩
      rw [hki.1] at hpos heq; rw [hkj.1] at heq; rw [hki.2.1]
      exact hinv.assign.dec_earliest i j hji hi_ks hpos heq
    · intro i hi; dsimp only; intro hl0; rw [e_te] at hi
      have hi_ks := Nat.lt_of_lt_of_le hi hbt.te_le
      let l := (ks.trl[i]?.getD 0#32).toNat
      have hl_lt := hinv.assign.trl_lt l (k6_mem_trailLits_of_lt hi_ks htrl_len)
      rw [e_la, e_trl] at hl0; change st.lvlArr[l / 2]?.getD 0#32 = 0#32 at hl0
      rw [(hbt.kept_var (l / 2) (by omega) ⟨i, hi, rfl⟩).1] at hl0
      have h0 := hinv.assign.lvl0_ok i hi_ks hl0; have hsy := hsync' i (by rw [e_te]; exact hi)
      exact ⟨hsy.1, hsy.2, by rw [e_trl]; exact h0.2.2⟩
  have hre' : K6ReasonOk st' := fun i hi => by
    rw [e_te] at hi; have hi_ks := Nat.lt_of_lt_of_le hi hbt.te_le
    let l := (ks.trl[i]?.getD 0#32).toNat
    have hl_lt := hinv.assign.trl_lt l (k6_mem_trailLits_of_lt hi_ks htrl_len)
    have hkv := hbt.kept_var (l / 2) (by omega) ⟨i, hi, rfl⟩
    change let l := (st'.trl[i]?.getD 0#32).toNat; let r := st'.rsn[l / 2]?.getD 0#32; _
    rw [e_trl, e_rs, hkv.2.1, hpres.nc]
    have hcl_eq : ∀ c, k6ClauseLits st' c = k6ClauseLits ks c := fun c => by
      unfold k6ClauseLits k6ClauseOff k6ClauseSize; rw [hpres.clOff, hpres.clSz, hpres.arena]
    rcases hinv.reasons i hi_ks with hnone | ⟨hr_lt, hmem, hoth⟩
    · exact Or.inl hnone
    · right; rw [hcl_eq]; exact ⟨hr_lt, hmem, hoth⟩
  refine ⟨⟨hsh', hcl', hw', hba', hre'⟩, hsync', e_lvl, e_te ▸ hbt.te_le, hpres, fun i hi => ?_⟩
  rw [e_te] at hi; have hi_ks := Nat.lt_of_lt_of_le hi hbt.te_le
  have hl_lt := hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hi_ks htrl_len)
  have hkv := hbt.kept_var _ (by omega) ⟨i, hi, rfl⟩
  rw [e_trl, e_rs, e_la, hkv.2.1, hkv.1]; exact ⟨rfl, rfl, hkept_lvl i hi⟩

/-! ## 2. `full_k6_init` & `full_k6_add_clause` Preservation Helpers -/

theorem k6Init_finish_inv {L : K6Layout} {nv : BitVec 32} {st : K6State}
    (hsh : st.ShapesOk L) (hnv_le : nv.toNat ≤ L.maxV)
    (e_nv : st.nv = nv) (e_nc : st.nc = 0#32) (e_lvl : st.lvl = 0#32)
    (e_prop : st.prop = 0#32) (e_te : st.trl_end = 0#32) (e_un : st.unass = nv)
    (e_ac : st.acap = BitVec.ofNat 32 L.acap) (e_mv : st.max_v = BitVec.ofNat 32 L.maxV)
    (e_mo : st.max_orig = BitVec.ofNat 32 L.maxOrig) (e_mc : st.max_cl = BitVec.ofNat 32 L.maxCl)
    (e_al : st.alen = 0#32) (e_in : st.incons = 0#32) (e_na : st.nassump = 0#32)
    (e_nk : st.nkl = 0#32) (e_nn : st.nana = 0#32)
    (hvars : ∀ v < nv.toNat, st.lvlArr[v]? = some 0#32 ∧ st.rsn[v]? = some 0xFFFFFFFF#32 ∧
      st.flags[v]? = some 0#32)
    (hlits : ∀ l < 2 * nv.toNat, st.vals[l]? = some 0#32 ∧ st.whead[l]? = some 0xFFFFFFFF#32) :
    (∀ P, K6Inv L P st) ∧ K6TrailSynced st := by
  refine ⟨fun P => ⟨hsh, ?_, ?_, ?_, fun i hi => by rw [e_te] at hi; simp at hi⟩,
    fun i hi => by rw [e_te] at hi; simp at hi⟩
  · refine ⟨e_ac, e_mv, e_mo, e_mc, e_nv ▸ hnv_le, by simp [e_nc], by simp [e_al],
      by simp [e_na], by simp [e_nk], by simp [e_nn], fun _ hc => by simp [e_nc] at hc,
      fun _ _ _ hc => by simp [e_nc] at hc, fun hi => absurd e_in hi,
      fun _ hi => by simp [e_na] at hi, fun v hv => by
        rw [e_nv] at hv; rw [(hvars v hv).2.2, Option.getD_some]; decide⟩
  · refine ⟨List.replicate (2 * nv.toNat) [], by simp [e_nv], by simp [List.flatten_replicate_nil],
      fun l hl => by
        rw [e_nv] at hl; rw [(hlits l hl).2, Option.getD_some]; simp [hl, K5WChain.nil],
      fun l hl w hw => by rw [e_nv] at hl; simp [hl] at hw⟩
  · refine ⟨by simp [e_te], by simp [e_prop, e_te], by simp [e_un, e_te, e_nv],
      fun l hl => by rw [e_nv] at hl; rw [(hlits l hl).1]; left; rfl,
      fun l hl => by
        rw [e_nv] at hl; have hnl : l ^^^ 1 < 2 * nv.toNat := by
          rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
        rw [(hlits l hl).1, (hlits (l ^^^ 1) hnl).1]; simp,
      fun l hl => by rw [e_nv] at hl; rw [(hlits l hl).1]; simp [e_te],
      by unfold k6TrailLits; simp [e_te], fun l hl => by
        unfold k6TrailLits at hl; simp [e_te] at hl,
      fun v hv => by rw [e_nv] at hv; rw [(hvars v hv).1, e_lvl]; simp,
      fun v hv _ => by rw [e_nv] at hv; rw [(hvars v hv).1, (hvars v hv).2.1]; exact ⟨rfl, rfl⟩,
      fun _ _ _ hj => by simp [e_te] at hj, fun _ _ _ hi => by simp [e_te] at hi,
      fun _ hi => by simp [e_te] at hi⟩

theorem k6AddClause_ge2_preserves {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    {ar xs : List (BitVec 32)} {sz : BitVec 32}
    (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks)
    (hnc_lt : ks.nc.toNat < L.maxCl) (hsz2 : 2 ≤ sz.toNat) (hsz_max : sz.toNat < 2 ^ 28)
    (hsz_xs : sz.toNat ≤ xs.length) (hfit : ks.alen.toNat + sz.toNat ≤ L.acap)
    (har_len : ar.length = L.acap) (har_old : ∀ j < ks.alen.toNat, ar[j]? = ks.arena[j]?)
    (har_new : ∀ j < sz.toNat, ar[ks.alen.toNat + j]? = xs[j]?)
    (hxlits : ∀ j < sz.toNat, (xs[j]?.getD 0#32).toNat < 2 * ks.nv.toNat)
    (hent : SemEntails P ((xs.take sz.toNat).map BitVec.toNat)) :
    let stM := (((({ ks with arena := ar } : K6State).putHdr .alen (ks.alen + sz)).putArr
      .clOff ks.nc.toNat ks.alen).putArr .clSz ks.nc.toNat sz).putHdr .nc (ks.nc + 1#32)
    let ks' := k6WatchStep stM ks.nc (xs[0]'(by omega)) (xs[1]'(by omega))
    K6Inv L P ks' ∧ K6TrailSynced ks' ∧ ks'.lvl = ks.lvl ∧ ks'.nv = ks.nv ∧
    ks'.nassump = ks.nassump ∧ ks'.assump = ks.assump ∧ ks'.trl_end = ks.trl_end ∧
    ks'.unass = ks.unass ∧ ks'.incons = ks.incons ∧
    (∀ M, (∀ j < sz.toNat, (xs[j]?.getD 0#32).toNat < 2 * M) →
      K6LitsBounded M ks → K6LitsBounded M ks') := by
  intro stM ks'; have := L.hmaxV; have := L.hacap
  have hnc1 : (ks.nc + 1#32).toNat = ks.nc.toNat + 1 := by unfold K6Layout.maxCl at hnc_lt; bv_omega
  have hal1 : (ks.alen + sz).toNat = ks.alen.toNat + sz.toNat := by
    unfold dimacsBound at *; bv_omega
  have hshM0 : ({ ks with arena := ar } : K6State).ShapesOk L :=
    { hinv.shapes with arena_len := har_len }
  have hshM : stM.ShapesOk L :=
    (((hshM0.putHdr .alen _).putArr .clOff _ _).putArr .clSz _ _).putHdr .nc _
  have hcl_old : ∀ c < ks.nc.toNat, k6ClauseOff stM c = k6ClauseOff ks c ∧
      k6ClauseSize stM c = k6ClauseSize ks c ∧ k6ClauseLits stM c = k6ClauseLits ks c := fun c hc =>
        by
    have hoff : k6ClauseOff stM c = k6ClauseOff ks c := by
      unfold k6ClauseOff; dsimp only [stM]; k6_field; rw [List.getElem?_set_ne (by omega)]
    have hszc : k6ClauseSize stM c = k6ClauseSize ks c := by
      unfold k6ClauseSize; dsimp only [stM]; k6_field; rw [List.getElem?_set_ne (by omega)]
    have hwf := hinv.clauses.cl_wf c hc
    refine ⟨hoff, hszc, by
      unfold k6ClauseLits
      rw [hoff, hszc, show stM.arena = ar from by dsimp only [stM]; k6_field]; congr 1
      apply List.ext_getElem (by simp [List.length_take, List.length_drop, har_len,
        hinv.shapes.arena_len])
      intro k hk1 _; have hk_sz : k < k6ClauseSize ks c := by simp [List.length_take] at hk1; omega
      have := hinv.clauses.alen_le; have := hinv.shapes.arena_len
      simp only [List.getElem_take, List.getElem_drop]
      have hg := har_old (k6ClauseOff ks c + k) (by have := hwf.2.1; omega)
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hg
      exact Option.some.inj hg⟩
  have hnew_off : k6ClauseOff stM ks.nc.toNat = ks.alen.toNat := by
    unfold k6ClauseOff; dsimp only [stM]; k6_field
    rw [List.getElem?_set_self (by rw [hinv.shapes.clOff_len]; exact hnc_lt), Option.getD_some]
  have hnew_sz : k6ClauseSize stM ks.nc.toNat = sz.toNat := by
    unfold k6ClauseSize; dsimp only [stM]; k6_field
    rw [List.getElem?_set_self (by rw [hinv.shapes.clSz_len]; exact hnc_lt), Option.getD_some]
  have hnew_lits : k6ClauseLits stM ks.nc.toNat = (xs.take sz.toNat).map BitVec.toNat := by
    unfold k6ClauseLits
    rw [hnew_off, hnew_sz, show stM.arena = ar from by dsimp only [stM]; k6_field]; congr 1
    apply List.ext_getElem (by simp [List.length_take, List.length_drop, har_len]; omega)
    intro k hk1 _; have hk_sz : k < sz.toNat := by simp [List.length_take] at hk1; omega
    simp only [List.getElem_take, List.getElem_drop]
    have hg := har_new k hk_sz
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hg
    exact Option.some.inj hg
  obtain ⟨eM_nv, eM_nc, eM_al, eM_ar, eM_te, eM_trl, eM_rsn, eM_wn, eM_wh⟩ :
      stM.nv = ks.nv ∧ stM.nc = ks.nc + 1#32 ∧ stM.alen = ks.alen + sz ∧
      stM.arena = ar ∧ stM.trl_end = ks.trl_end ∧ stM.trl = ks.trl ∧ stM.rsn = ks.rsn ∧
      stM.wnext = ks.wnext ∧ stM.whead = ks.whead := by
    dsimp only [stM]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> k6_field
  have hclM : K6ClausesOk L P stM := by
    refine ⟨?_, ?_, ?_, ?_, by rw [eM_nv]; exact hinv.clauses.nv_le, by rw [eM_nc, hnc1]; omega,
      by rw [eM_al, hal1]; exact hfit, ?_, ?_, ?_, fun cid hc => ?_, fun c1 c2 h12 h2 => ?_, ?_, ?_,
      ?_⟩
    · dsimp only [stM]; k6_field; exact hinv.clauses.acap_eq
    · dsimp only [stM]; k6_field; exact hinv.clauses.max_v_eq
    · dsimp only [stM]; k6_field; exact hinv.clauses.max_orig_eq
    · dsimp only [stM]; k6_field; exact hinv.clauses.max_cl_eq
    · dsimp only [stM]; k6_field; exact hinv.clauses.nassump_le
    · dsimp only [stM]; k6_field; exact hinv.clauses.nkl_le
    · dsimp only [stM]; k6_field; exact hinv.clauses.nana_le
    · rw [eM_nc, hnc1] at hc; rw [eM_al, hal1, eM_nv]; by_cases hcid : cid = ks.nc.toNat
      · subst hcid; rw [hnew_off, hnew_sz, hnew_lits]
        refine ⟨hsz2, Nat.le_refl _, fun l hl => ?_, hent⟩
        rw [List.mem_map] at hl; obtain ⟨b, hb, rfl⟩ := hl
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
        have hj_sz : j < sz.toNat := by simp [List.length_take] at hj; omega
        have hxj := hxlits j hj_sz; simp only [List.getElem_take]
        rwa [List.getElem?_eq_getElem (by omega : j < xs.length), Option.getD_some] at hxj
      · obtain ⟨ho, hs, hl⟩ := hcl_old cid (by omega); rw [ho, hs, hl]
        have hw := hinv.clauses.cl_wf cid (by omega); exact ⟨hw.1, by omega, hw.2.2.1, hw.2.2.2⟩
    · rw [eM_nc, hnc1] at h2; change k6ClauseOff stM c1 + k6ClauseSize stM c1 ≤ k6ClauseOff stM c2
      have ho1 := hcl_old c1 (by omega); rw [ho1.1, ho1.2.1]; by_cases h2e : c2 = ks.nc.toNat
      · subst h2e; rw [hnew_off]; exact (hinv.clauses.cl_wf c1 (by omega)).2.1
      · rw [(hcl_old c2 (by omega)).1]; exact hinv.clauses.cl_mono c1 c2 h12 (by omega)
    · dsimp only [stM]; k6_field; exact hinv.clauses.incons_ok
    · dsimp only [stM]; k6_field; exact hinv.clauses.assump_ok
    · dsimp only [stM]; k6_field; exact hinv.clauses.flags_clean
  have hwM : K6WatchesOk stM := by
    obtain ⟨chains, hlen, hnd, hwc, hbnd⟩ := hinv.watches
    refine ⟨chains, eM_nv ▸ hlen, hnd, by rw [eM_wn, eM_wh]; exact hwc, fun l hl w hw => ?_⟩
    rw [eM_nv] at hl; obtain ⟨_, hw2, hw3, hw4, hw5, hw6, hw7⟩ := hbnd l hl w hw
    have ho := hcl_old (w / 2) (by omega); have hwf := hinv.clauses.cl_wf (w / 2) (by omega)
    have har_get : ∀ off < 2, stM.arena[k6ClauseOff ks (w / 2) + off]? =
        ks.arena[k6ClauseOff ks (w / 2) + off]? := fun off hoff => by
          rw [eM_ar]; exact har_old _ (by omega)
    refine ⟨by rw [eM_nc, hnc1]; omega, by rw [ho.2.1]; exact hw2,
      by rw [ho.1, har_get (w % 2) (Nat.mod_lt _ (by decide))]; exact hw3,
      by dsimp only [stM]; k6_field; exact hw4, by
        rw [ho.2.2]; dsimp only [stM]; k6_field; exact hw5,
      by rw [ho.2.1]; dsimp only [stM]; k6_field; exact hw6, fun h2 => by
        rw [ho.2.1] at h2; rw [ho.1, har_get (w % 2 ^^^ 1) (by
          rcases Nat.mod_two_eq_zero_or_one w with h | h <;> simp [h])]
        dsimp only [stM]; k6_field; exact hw7 h2⟩
  have hl_lt : ∀ j (hj : j < 2), (xs[j]'(by omega)).toNat < 2 * stM.nv.toNat ∧
      (xs[j]'(by omega)).toNat ∈ k6ClauseLits stM ks.nc.toNat := fun j hj =>
    ⟨by
       have h0 := hxlits j (by omega)
       rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
       rw [eM_nv]; exact h0,
     by rw [hnew_lits, List.mem_map]; exact ⟨xs[j]'(by omega),
          List.mem_take_iff_getElem.mpr ⟨j, by omega, by simp⟩, rfl⟩⟩
  have hw' : K6WatchesOk ks' :=
    k6WatchStep_preserves_watches hshM hwM (by rw [eM_nc, hnc1]; omega) (by rw [eM_nc, hnc1]; omega)
      (eM_nv ▸ hinv.clauses.nv_le) (hl_lt 0 (by decide)).1 (hl_lt 1 (by decide)).1
      (by rw [hnew_sz]; exact hsz2) (hl_lt 0 (by decide)).2 (hl_lt 1 (by decide)).2
      (by rw [hnew_off, eM_ar]; have h0 := har_new 0 (by omega); rw [Nat.add_zero] at h0
          rw [h0, List.getElem?_eq_getElem (by omega), Option.getD_some])
      (by rw [hnew_off, eM_ar, har_new 1 (by omega), List.getElem?_eq_getElem (by omega),
        Option.getD_some])
      (fun chains hclen _ hwc => by
        obtain ⟨ch0, h0len, _, h0wc, h0bnd⟩ := hinv.watches
        have hcheq : chains = ch0 := List.ext_getElem (by rw [hclen, eM_nv, h0len]) fun x hx1 hx2 =>
          by
          have hc1 := hwc x (by rw [eM_nv]; omega); have hc2 := h0wc x (by omega)
          rw [eM_wn, eM_wh, List.getElem?_eq_getElem hx1, Option.getD_some] at hc1
          rw [List.getElem?_eq_getElem hx2, Option.getD_some] at hc2
          exact k6_wchain_unique (by rw [hinv.shapes.wnext_len]; unfold K6Layout.maxCl; omega) hc1
            hc2
        rw [hcheq]; constructor <;> intro hmem <;>
          (obtain ⟨ch, hch_m, hw_m⟩ := List.mem_flatten.mp hmem
           obtain ⟨x, hx, rfl⟩ := List.getElem_of_mem hch_m
           have := h0bnd x (by omega) _ (by simpa [List.getElem?_eq_getElem hx] using hw_m); omega))
  have hbaM := k6BaseAssignOk_cast hinv.assign (h1 := eM_nv) (h2 := eM_te)
    (h3 := by dsimp only [stM]; k6_field) (h4 := by dsimp only [stM]; k6_field)
    (h5 := by dsimp only [stM]; k6_field) (h6 := eM_trl) (h7 := by dsimp only [stM]; k6_field)
    (h8 := by dsimp only [stM]; k6_field) (h9 := eM_rsn)
  have hreM : K6ReasonOk stM := fun i hi => by
    rw [eM_te] at hi
    change let l := (stM.trl[i]?.getD 0#32).toNat; let r := stM.rsn[l / 2]?.getD 0xFFFFFFFF#32; _
    rw [eM_trl, eM_rsn, eM_nc]; rcases hinv.reasons i hi with hnone | ⟨hr_lt, hmem, hoth⟩
    · exact Or.inl hnone
    · right; rw [(hcl_old _ hr_lt).2.2, hnc1]; exact ⟨by omega, hmem, hoth⟩
  have hsyncM := k6TrailSynced_cast hsync (h_te := eM_te) (h_tr := eM_trl)
    (h_va := by dsimp only [stM]; k6_field)
  have hlb' : ∀ M, (∀ j < sz.toNat, (xs[j]?.getD 0#32).toNat < 2 * M) →
      K6LitsBounded M ks → K6LitsBounded M ks' := fun M hxsM hM => by
    have hnc4 : ks.nc.toNat < 4 * L.maxV := hnc_lt; have hxs1 : 1 < xs.length := by omega
    have eK_nc : ks'.nc = ks.nc + 1#32 := by
      dsimp only [ks', k6WatchStep, k6WatchStep0]; rw [← eM_nc]
    have eK_lits : ∀ c, k6ClauseLits ks' c = k6ClauseLits stM c := fun c => by
      dsimp only [ks', k6WatchStep, k6WatchStep0, k6ClauseLits, k6ClauseOff, k6ClauseSize]
    constructor
    · intro cid hcid l hl; rw [eK_nc, hnc1] at hcid; rw [eK_lits] at hl
      by_cases hc : cid = ks.nc.toNat
      · subst hc; rw [hnew_lits, List.mem_map] at hl; obtain ⟨b, hb, rfl⟩ := hl
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
        have hj' : j < sz.toNat := by simp [List.length_take] at hj; omega
        have hx := hxsM j hj'; simp only [List.getElem_take]
        rwa [List.getElem?_eq_getElem (by omega : j < xs.length), Option.getD_some] at hx
      · rw [(hcl_old cid (by omega)).2.2] at hl; exact hM.1 cid (by omega) l hl
    · intro w hw; rw [eK_nc, hnc1] at hw
      have hw0 := k6_bv32_cid_w0 hnc_lt (by unfold K6Layout.maxCl; omega)
      have hw1 := k6_bv32_cid_w1 hnc_lt (by unfold K6Layout.maxCl; omega)
      let bf : BitVec 32 :=
        if (stM.clSz[ks.nc.toNat]?.getD 0#32).toNat = 2 then 0x80000000#32 else 0#32
      have hwb_eq : ks'.wblit = (ks.wblit.set (2 * ks.nc.toNat) ((xs[1]'(by omega)) ||| bf)).set
          (2 * ks.nc.toNat + 1) ((xs[0]'(by omega)) ||| bf) := by
        dsimp only [ks', k6WatchStep, k6WatchStep0, bf]; rw [hw0.1, hw1.1]; dsimp only [stM]
        k6_field
      have hbf_m : ∀ j (hj : j < 2),
      ((xs[j]'(by omega)) ||| bf) &&& 0x7FFFFFFF#32 = xs[j]'(by omega) :=
        fun j hj => by
          have hlt31 : (xs[j]'(by omega)).toNat < 2 ^ 31 := by
            have hxj := hxlits j (by omega); have := hinv.clauses.nv_le
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hxj; omega
          dsimp only [bf]; split
          · exact (k6_bv32_or_bin_mask hlt31).1
          · rw [BitVec.or_zero]; exact (k6_bv32_lt31_and_mask hlt31).1
      rw [hwb_eq]; by_cases h1 : w = 2 * ks.nc.toNat + 1
      · subst h1
        rw [List.getElem?_set_self (by simp [hinv.shapes.wblit_len]; unfold K6Layout.maxCl; omega),
          Option.getD_some, hbf_m 0 (by decide)]
        have hx := hxsM 0 (by omega)
        rw [List.getElem?_eq_getElem (by omega : 0 < xs.length), Option.getD_some] at hx
        exact hx
      · rw [List.getElem?_set_ne (Ne.symm h1)]; by_cases h0 : w = 2 * ks.nc.toNat
        · subst h0
          rw [List.getElem?_set_self (by rw [hinv.shapes.wblit_len]; unfold K6Layout.maxCl; omega),
            Option.getD_some, hbf_m 1 (by decide)]
          have hx := hxsM 1 (by omega)
          rw [List.getElem?_eq_getElem (by omega : 1 < xs.length), Option.getD_some] at hx
          exact hx
        · rw [List.getElem?_set_ne (Ne.symm h0)]; exact hM.2 w (by omega)
  exact ⟨⟨k6WatchStep_preserves_shapes hshM ks.nc (xs[0]'(by omega)) (xs[1]'(by omega)),
    k6WatchStep_clausesOk hclM _ _ _, hw', k6WatchStep_assignOk hbaM _ _ _,
    k6WatchStep_reasonOk hreM _ _ _⟩,
    k6WatchStep_trailSynced hsyncM _ _ _, by
      dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field, eM_nv,
    by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field,
    by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field, eM_te,
    by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field,
    by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field, hlb'⟩

end LeanQbe.T.Examples.Kissat.Proof.Kitten

end
