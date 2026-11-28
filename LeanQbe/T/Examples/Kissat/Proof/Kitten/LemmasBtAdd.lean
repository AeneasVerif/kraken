/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Kitten.LemmasWatch

/-!
# Backtrack Loop, `init`, & `add_clause` Invariant Lemmas (`Kissat.Proof.Kitten.LemmasBtAdd`)

Covers `K6BtLoopInv` (`init`/`step`/`finish`), `k6Init_finish_inv`, and
`k6AddClause_ge2_preserves`.

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

structure K6BtLoopInv (L : K6Layout) (ks : K6State) (target_lvl te : BitVec 32)
    (st : K6State) : Prop where
  sh : st.ShapesOk L
  te_le : te.toNat ≤ ks.trl_end.toNat
  unass_eq : st.unass.toNat + te.toNat = ks.nv.toNat
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
  kept_var : ∀ w < ks.nv.toNat,
    (∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = w) →
    st.lvlArr[w]? = ks.lvlArr[w]? ∧ st.rsn[w]? = ks.rsn[w]? ∧
    st.vals[2 * w]? = ks.vals[2 * w]? ∧ st.vals[2 * w + 1]? = ks.vals[2 * w + 1]?
  cleared_var : ∀ w < ks.nv.toNat,
    (¬ ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = w) →
    st.lvlArr[w]? = some 0#32 ∧ st.rsn[w]? = some 0xFFFFFFFF#32 ∧
    st.vals[2 * w]? = some 0#32 ∧ st.vals[2 * w + 1]? = some 0#32
  popped_gt : ∀ i, te.toNat ≤ i → i < ks.trl_end.toNat →
    target_lvl.toNat < (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat

theorem k6BtLoopInv_init {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    {target_lvl : BitVec 32} (hinv : K6Inv L P ks) :
    K6BtLoopInv L ks target_lvl ks.trl_end ks :=
  ⟨hinv.shapes, Nat.le_refl _, hinv.assign.unass_eq, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl,
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
     have hv0_len : 2 * w < ks.vals.length := by
       rw [hinv.shapes.vals_len]; have := hinv.clauses.nv_le; omega
     have hv1_len : 2 * w + 1 < ks.vals.length := by
       rw [hinv.shapes.vals_len]; have := hinv.clauses.nv_le; omega
     have hl_len : w < ks.lvlArr.length := by
       rw [hinv.shapes.lvlArr_len]; have := hinv.clauses.nv_le; omega
     have hr_len : w < ks.rsn.length := by
       rw [hinv.shapes.rsn_len]; have := hinv.clauses.nv_le; omega
     rw [List.getElem?_eq_getElem hl_len, Option.getD_some] at hzo
     rw [List.getElem?_eq_getElem hr_len, Option.getD_some] at hzo
     rw [List.getElem?_eq_getElem hv0_len, Option.getD_some] at hz
     rw [List.getElem?_eq_getElem hv1_len, Option.getD_some] at hz1
     exact ⟨by rw [List.getElem?_eq_getElem hl_len, hzo.1],
       by rw [List.getElem?_eq_getElem hr_len, hzo.2],
       by rw [List.getElem?_eq_getElem hv0_len, hz],
       by rw [List.getElem?_eq_getElem hv1_len, hz1]⟩,
   fun _ h1 h2 => absurd (Nat.lt_of_le_of_lt h1 h2) (Nat.lt_irrefl _)⟩

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
  intro lit v st'
  have := L.hmaxV
  have hnv := hinv.clauses.nv_le
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; omega
  have hte1_lt : te.toNat - 1 < ks.trl_end.toNat := by have := hbt.te_le; omega
  have hv_lt : v < ks.nv.toNat := by
    have hm1 := k6_mem_trailLits_of_lt hte1_lt htrl_len
    have hlt := hinv.assign.trl_lt lit.toNat hm1
    have hdv := (k6_bv32_div2_lt hlt).1; omega
  have hnl_eq : (lit ^^^ 1#32).toNat = lit.toNat ^^^ 1 := by simp
  have hsh' : st'.ShapesOk L :=
    ((((hbt.sh.putArr .vals _ _).putArr .vals _ _).putArr .lvlArr _ _).putArr
      .rsn _ _).putHdr .unass _
  have hun_lt : st.unass.toNat + 1 < 2 ^ 32 := by have := hbt.unass_eq; omega
  have hmk : ∀ qOpt : Option (BitVec 32),
      K6BtLoopInv L ks target_lvl (te - 1#32)
        (match qOpt with | none => st' | some qs => st'.putHdr .qsearch qs) := by
    intro qOpt
    let finSt := match qOpt with | none => st' | some qs => st'.putHdr .qsearch qs
    have hshF : finSt.ShapesOk L := by
      cases qOpt with | none => exact hsh' | some qs => exact hsh'.putHdr .qsearch qs
    have hte_sub : (te - 1#32).toNat = te.toNat - 1 := by bv_omega
    have hunF : finSt.unass.toNat + (te - 1#32).toNat = ks.nv.toNat := by
      have hun_st : finSt.unass = st.unass + 1#32 := by
        cases qOpt <;> dsimp only [finSt, st'] <;> k6_field
      rw [hun_st, hte_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have := hbt.unass_eq; omega
    have hlvl_st : finSt.lvlArr = st.lvlArr.set v 0#32 := by
      cases qOpt <;> dsimp only [finSt, st'] <;> k6_field
    have hrsn_st : finSt.rsn = st.rsn.set v 0xFFFFFFFF#32 := by
      cases qOpt <;> dsimp only [finSt, st'] <;> k6_field
    have hvals_st : finSt.vals = (st.vals.set lit.toNat 0#32).set (lit.toNat ^^^ 1) 0#32 := by
      cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> rw [hnl_eq]
    have hv_eq : v = lit.toNat / 2 := (k6_bv32_div2_lt
      (hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hte1_lt htrl_len))).1
    have hl_xor := k6_nat_xor1_cases lit.toNat
    refine ⟨hshF, by rw [hte_sub]; omega, hunF,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.nv_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.nc_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.lvl_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.prop_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.te_hdr,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.inc_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.alen_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.acap_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.na_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.nk_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.nan_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.st_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.ph_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.op_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.mv_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.mo_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.mc_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.nq_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.ht_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.qs_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.trl_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.fl_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.ass_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.ana_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.kl_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.wh_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.wn_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.wb_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.co_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.cs_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.ar_eq,
      ?_, ?_, ?_⟩
    · intro w hw ⟨i, hi, hiw⟩
      have hi' : i < te.toNat - 1 := by rw [hte_sub] at hi; exact hi
      have hne_v : w ≠ v := by
        rw [← hiw, hv_eq]
        exact k6_trl_nodup_var_ne hinv.shapes hnv hinv.assign (Nat.lt_trans hi' (by omega)) hte1_lt
          (by omega)
      have hold := hbt.kept_var w hw ⟨i, by omega, hiw⟩
      rw [hlvl_st, hrsn_st, hvals_st, List.getElem?_set_ne (Ne.symm hne_v),
        List.getElem?_set_ne (Ne.symm hne_v)]
      rcases hl_xor with ⟨_, _⟩ | ⟨_, _⟩ <;>
        exact ⟨hold.1, hold.2.1,
          by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
             exact hold.2.2.1,
          by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
             exact hold.2.2.2⟩
    · intro w hw hnone
      by_cases hwv : w = v
      · subst hwv
        have hlv_len : v < st.lvlArr.length := by rw [hbt.sh.lvlArr_len]; omega
        have hrs_len : v < st.rsn.length := by rw [hbt.sh.rsn_len]; omega
        have hv0_len : 2 * v < st.vals.length := by rw [hbt.sh.vals_len]; omega
        have hv1_len : 2 * v + 1 < st.vals.length := by rw [hbt.sh.vals_len]; omega
        rw [hlvl_st, hrsn_st, hvals_st, List.getElem?_set_self hlv_len,
          List.getElem?_set_self hrs_len]
        refine ⟨rfl, rfl, ?_, ?_⟩
        · rcases hl_xor with ⟨h0a, h1a⟩ | ⟨h0a, h1a⟩
          · rw [h1a, h0a, ← hv_eq, List.getElem?_set_ne (by omega),
              List.getElem?_set_self hv0_len]
          · rw [h1a, ← hv_eq,
              List.getElem?_set_self (by simp only [List.length_set]; exact hv0_len)]
        · rcases hl_xor with ⟨h0a, h1a⟩ | ⟨h0a, h1a⟩
          · rw [h1a, ← hv_eq,
              List.getElem?_set_self (by simp only [List.length_set]; exact hv1_len)]
          · rw [h1a, h0a, ← hv_eq, List.getElem?_set_ne (by omega),
              List.getElem?_set_self hv1_len]
      · have hnone_old : ¬ ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = w := by
          rintro ⟨i, hi, hiw⟩
          by_cases hie : i = te.toNat - 1
          · subst hie; exact hwv (by rw [hv_eq]; exact hiw.symm)
          · exact hnone ⟨i, by rw [hte_sub]; omega, hiw⟩
        have hold := hbt.cleared_var w hw hnone_old
        rw [hlvl_st, hrsn_st, hvals_st, List.getElem?_set_ne (Ne.symm hwv),
          List.getElem?_set_ne (Ne.symm hwv)]
        rcases hl_xor with ⟨_, _⟩ | ⟨_, _⟩ <;>
          exact ⟨hold.1, hold.2.1,
            by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
               exact hold.2.2.1,
            by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
               exact hold.2.2.2⟩
    · intro i hlo hhi; rw [hte_sub] at hlo
      by_cases hie : i = te.toNat - 1
      · subst hie
        have hkept := hbt.kept_var (lit.toNat / 2) (by omega) ⟨te.toNat - 1, by omega, rfl⟩
        rw [hkept.1] at hpop; exact hpop
      · exact hbt.popped_gt i (by omega) hhi
  exact ⟨hmk none, fun qs => hmk (some qs)⟩

theorem k6BtLoopInv_finish {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    {target_lvl te : BitVec 32} {st : K6State} (hinv : K6Inv L P ks)
    (hbt : K6BtLoopInv L ks target_lvl te st)
    (hsync_below : target_lvl = 0#32 ∨ K6TrailSynced ks)
    (hexit : te = 0#32 ∨
      ∃ i < te.toNat, i = te.toNat - 1 ∧
        (st.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat) :
    let st' := ((st.putHdr .trl_end te).putHdr .prop
      (if te.toNat < st.prop.toNat then te else st.prop)).putHdr .lvl target_lvl
    K6Inv L P st' ∧ K6TrailSynced st' ∧ st'.lvl = target_lvl ∧
    st'.trl_end.toNat ≤ ks.trl_end.toNat ∧ K6BtPreserved ks st' ∧
    (∀ i < st'.trl_end.toNat,
      st'.trl[i]? = ks.trl[i]? ∧ st'.rsn[(st'.trl[i]?.getD 0#32).toNat / 2]? =
        ks.rsn[(st'.trl[i]?.getD 0#32).toNat / 2]? ∧
      (st'.lvlArr[(st'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat) := by
  intro st'
  have := L.hmaxV; have hnv := hinv.clauses.nv_le
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; omega
  have hkept_lvl : ∀ i < te.toNat,
      (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat := by
    intro i hi
    rcases hexit with rfl | ⟨j, hj, _, hle⟩
    · simp at hi
    · have hj_lt : j < ks.trl_end.toNat := Nat.lt_of_lt_of_le hj hbt.te_le
      have hlj := hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hj_lt htrl_len)
      have hkj := (hbt.kept_var _ (by omega) ⟨j, hj, rfl⟩).1
      rw [hkj] at hle
      exact Nat.le_trans (hinv.assign.trl_lvl_mono i j (by omega) hj_lt) hle
  have hsh' : st'.ShapesOk L := ((hbt.sh.putHdr .trl_end _).putHdr .prop _).putHdr .lvl _
  have e_nv : st'.nv = ks.nv := by dsimp only [st']; k6_field; exact hbt.nv_eq
  have e_nc : st'.nc = ks.nc := by dsimp only [st']; k6_field; exact hbt.nc_eq
  have e_lvl : st'.lvl = target_lvl := by dsimp only [st']; k6_field
  have e_te : st'.trl_end = te := by dsimp only [st']; k6_field
  have e_un : st'.unass = st.unass := by dsimp only [st']; k6_field
  have e_pr : st'.prop = if te.toNat < st.prop.toNat then te else st.prop := by
    dsimp only [st']; k6_field
  have e_trl : st'.trl = ks.trl := by dsimp only [st']; k6_field; exact hbt.trl_eq
  have e_la : st'.lvlArr = st.lvlArr := by dsimp only [st']; k6_field
  have e_rs : st'.rsn = st.rsn := by dsimp only [st']; k6_field
  have e_va : st'.vals = st.vals := by dsimp only [st']; k6_field
  have hpres : K6BtPreserved ks st' :=
    { nv := e_nv, nc := e_nc, incons := by dsimp only [st']; k6_field; exact hbt.inc_eq
      alen := by dsimp only [st']; k6_field; exact hbt.alen_eq
      acap := by dsimp only [st']; k6_field; exact hbt.acap_eq
      nassump := by dsimp only [st']; k6_field; exact hbt.na_eq
      nkl := by dsimp only [st']; k6_field; exact hbt.nk_eq
      nana := by dsimp only [st']; k6_field; exact hbt.nan_eq
      status := by dsimp only [st']; k6_field; exact hbt.st_eq
      phase := by dsimp only [st']; k6_field; exact hbt.ph_eq
      openCnt := by dsimp only [st']; k6_field; exact hbt.op_eq
      max_v := by dsimp only [st']; k6_field; exact hbt.mv_eq
      max_orig := by dsimp only [st']; k6_field; exact hbt.mo_eq
      max_cl := by dsimp only [st']; k6_field; exact hbt.mc_eq
      neq := by dsimp only [st']; k6_field; exact hbt.nq_eq
      hdrTail := by dsimp only [st']; k6_field; exact hbt.ht_eq
      assump := by dsimp only [st']; k6_field; exact hbt.ass_eq
      ana := by dsimp only [st']; k6_field; exact hbt.ana_eq
      kl := by dsimp only [st']; k6_field; exact hbt.kl_eq
      whead := by dsimp only [st']; k6_field; exact hbt.wh_eq
      wnext := by dsimp only [st']; k6_field; exact hbt.wn_eq
      wblit := by dsimp only [st']; k6_field; exact hbt.wb_eq
      clOff := by dsimp only [st']; k6_field; exact hbt.co_eq
      clSz := by dsimp only [st']; k6_field; exact hbt.cs_eq
      arena := by dsimp only [st']; k6_field; exact hbt.ar_eq
      flags2_eq := fun v _ => by
        have hfl : st'.flags = ks.flags := by dsimp only [st']; k6_field; exact hbt.fl_eq
        rw [hfl]
      lvlArr_kept := fun i hi => by
        rw [e_te] at hi; rw [e_trl, e_la]
        have hli :=
          hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt (Nat.lt_of_lt_of_le hi hbt.te_le) htrl_len)
        exact (hbt.kept_var _ (by omega) ⟨i, hi, rfl⟩).1 }
  have hcl' : K6ClausesOk L P st' :=
    { acap_eq := hpres.acap.trans hinv.clauses.acap_eq
      max_v_eq := hpres.max_v.trans hinv.clauses.max_v_eq
      max_orig_eq := hpres.max_orig.trans hinv.clauses.max_orig_eq
      max_cl_eq := hpres.max_cl.trans hinv.clauses.max_cl_eq
      nv_le := e_nv ▸ hinv.clauses.nv_le, nc_le := e_nc ▸ hinv.clauses.nc_le
      alen_le := hpres.alen ▸ hinv.clauses.alen_le
      nassump_le := hpres.nassump ▸ hinv.clauses.nassump_le
      nkl_le := hpres.nkl ▸ hinv.clauses.nkl_le, nana_le := hpres.nana ▸ hinv.clauses.nana_le
      cl_wf := by
        unfold k6ClauseLits k6ClauseOff k6ClauseSize
        rw [e_nc, e_nv, hpres.alen, hpres.clOff, hpres.clSz, hpres.arena]; exact hinv.clauses.cl_wf
      cl_mono := by
        unfold k6ClauseOff k6ClauseSize; rw [e_nc, hpres.clOff, hpres.clSz]
        exact hinv.clauses.cl_mono
      incons_ok := hpres.incons ▸ hinv.clauses.incons_ok
      assump_ok := by rw [e_nv, hpres.nassump, hpres.assump]; exact hinv.clauses.assump_ok
      flags_clean := fun v hv => by
        rw [e_nv] at hv; rw [hpres.flags2_eq v hv]; exact hinv.clauses.flags_clean v hv }
  have hw' : K6WatchesOk st' := by
    obtain ⟨ch, hch_len, hch_nd, hch_wc, hch_bnd⟩ := hinv.watches
    refine ⟨ch, by rw [e_nv]; exact hch_len, hch_nd, fun l hl => ?_, fun l hl w hw => ?_⟩
    · rw [e_nv] at hl; rw [hpres.wnext, hpres.whead]; exact hch_wc l hl
    · rw [e_nv] at hl
      have hcl_sz : ∀ c, k6ClauseSize st' c = k6ClauseSize ks c := fun c => by
        unfold k6ClauseSize; rw [hpres.clSz]
      have hcl_off : ∀ c, k6ClauseOff st' c = k6ClauseOff ks c := fun c => by
        unfold k6ClauseOff; rw [hpres.clOff]
      have hcl_lits : ∀ c, k6ClauseLits st' c = k6ClauseLits ks c := fun c => by
        unfold k6ClauseLits; rw [hcl_off, hcl_sz, hpres.arena]
      rw [e_nv, e_nc, hcl_sz, hcl_off, hcl_lits, hpres.arena, hpres.wblit]
      exact hch_bnd l hl w hw
  have hsync' : K6TrailSynced st' := fun i hi => by
    rw [e_te] at hi
    have hi_ks := Nat.lt_of_lt_of_le hi hbt.te_le
    let l := (ks.trl[i]?.getD 0#32).toNat
    have hl_lt : l < 2 * ks.nv.toNat := hinv.assign.trl_lt l (k6_mem_trailLits_of_lt hi_ks htrl_len)
    have hkv := hbt.kept_var (l / 2) (by omega) ⟨i, hi, rfl⟩
    have hvals_old : ks.vals[l]? = some 1#32 ∧ ks.vals[l ^^^ 1]? = some 2#32 := by
      rcases hsync_below with rfl | hsy
      · have hl0 : ks.lvlArr[l / 2]?.getD 0#32 = 0#32 :=
          BitVec.eq_of_toNat_eq (Nat.eq_zero_of_le_zero (hkept_lvl i hi))
        have h0 := hinv.assign.lvl0_ok i hi_ks hl0; exact ⟨h0.1, h0.2.1⟩
      · exact hsy i hi_ks
    change st'.vals[(st'.trl[i]?.getD 0#32).toNat]? = some 1#32 ∧
      st'.vals[(st'.trl[i]?.getD 0#32).toNat ^^^ 1]? = some 2#32
    rw [e_trl, e_va]; change st.vals[l]? = some 1#32 ∧ st.vals[l ^^^ 1]? = some 2#32
    have hpair : st.vals[l]? = ks.vals[l]? ∧ st.vals[l ^^^ 1]? = ks.vals[l ^^^ 1]? := by
      rcases k6_nat_xor1_cases l with ⟨he, hx⟩ | ⟨he, hx⟩
      · exact ⟨by rw [he]; exact hkv.2.2.1, by rw [hx]; exact hkv.2.2.2⟩
      · exact ⟨by rw [he]; exact hkv.2.2.2, by rw [hx]; exact hkv.2.2.1⟩
    rw [hpair.1, hpair.2]; exact hvals_old
  have hba' : K6BaseAssignOk P st' := by
    refine ⟨by rw [e_te, e_nv]; exact Nat.le_trans hbt.te_le hinv.assign.trl_end_le,
      by rw [e_pr, e_te]; split <;> omega,
      by rw [e_un, e_te, e_nv]; exact hbt.unass_eq,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro l hl; rw [e_nv] at hl; rw [e_va]
      by_cases hex : ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = l / 2
      · have hkv := hbt.kept_var (l / 2) (by omega) hex
        rcases k6_nat_xor1_cases l with ⟨he, _⟩ | ⟨he, _⟩
        · rw [he, hkv.2.2.1, ← he]; exact hinv.assign.vals_dom l hl
        · rw [he, hkv.2.2.2, ← he]; exact hinv.assign.vals_dom l hl
      · have hcv := hbt.cleared_var (l / 2) (by omega) hex
        rcases k6_nat_xor1_cases l with ⟨he, _⟩ | ⟨he, _⟩
        · rw [he, hcv.2.2.1]; left; rfl
        · rw [he, hcv.2.2.2]; left; rfl
    · intro l hl; rw [e_nv] at hl; rw [e_va]
      by_cases hex : ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = l / 2
      · have hkv := hbt.kept_var (l / 2) (by omega) hex
        have hpair : st.vals[l]? = ks.vals[l]? ∧ st.vals[l ^^^ 1]? = ks.vals[l ^^^ 1]? := by
          rcases k6_nat_xor1_cases l with ⟨he, hx⟩ | ⟨he, hx⟩
          · exact ⟨by rw [he]; exact hkv.2.2.1, by rw [hx]; exact hkv.2.2.2⟩
          · exact ⟨by rw [he]; exact hkv.2.2.2, by rw [hx]; exact hkv.2.2.1⟩
        rw [hpair.1, hpair.2]; exact hinv.assign.vals_neg_iff l hl
      · have hcv := hbt.cleared_var (l / 2) (by omega) hex
        have hpair : st.vals[l]? = some 0#32 ∧ st.vals[l ^^^ 1]? = some 0#32 := by
          rcases k6_nat_xor1_cases l with ⟨he, hx⟩ | ⟨he, hx⟩
          · exact ⟨by rw [he]; exact hcv.2.2.1, by rw [hx]; exact hcv.2.2.2⟩
          · exact ⟨by rw [he]; exact hcv.2.2.2, by rw [hx]; exact hcv.2.2.1⟩
        rw [hpair.1, hpair.2]; simp
    · intro l hl; rw [e_nv] at hl; rw [e_va, e_te, e_trl]
      by_cases hex : ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = l / 2
      · refine ⟨fun _ => hex, fun _ => ?_⟩
        obtain ⟨i, hi, hiv⟩ := hex
        have hkv := hbt.kept_var (l / 2) (by omega) ⟨i, hi, hiv⟩
        have hnz := (hinv.assign.vals_nz_iff_trl l hl).mpr ⟨i, Nat.lt_of_lt_of_le hi hbt.te_le, hiv⟩
        rcases k6_nat_xor1_cases l with ⟨he, _⟩ | ⟨he, _⟩
        · rw [he, hkv.2.2.1, ← he]; exact hnz
        · rw [he, hkv.2.2.2, ← he]; exact hnz
      · have hcv := hbt.cleared_var (l / 2) (by omega) hex
        refine ⟨fun hnz => absurd ?_ hnz, fun h => absurd h hex⟩
        rcases k6_nat_xor1_cases l with ⟨he, _⟩ | ⟨he, _⟩
        · rw [he, hcv.2.2.1]; rfl
        · rw [he, hcv.2.2.2]; rfl
    · have hpf : k6TrailLits st' <+: k6TrailLits ks := by
        unfold k6TrailLits; rw [e_te, e_trl]
        exact List.IsPrefix.map BitVec.toNat (List.take_prefix_take_left hbt.te_le)
      exact hinv.assign.trl_nodup.sublist (hpf.map (· / 2)).sublist
    · intro l hl; rw [e_nv]
      have hpf : k6TrailLits st' <+: k6TrailLits ks := by
        unfold k6TrailLits; rw [e_te, e_trl]
        exact List.IsPrefix.map BitVec.toNat (List.take_prefix_take_left hbt.te_le)
      exact hinv.assign.trl_lt l (hpf.subset hl)
    · intro v hv; rw [e_nv] at hv; rw [e_la, e_lvl]
      by_cases hex : ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = v
      · obtain ⟨i, hi, rfl⟩ := hex
        rw [(hbt.kept_var _ hv ⟨i, hi, rfl⟩).1]; exact hkept_lvl i hi
      · rw [(hbt.cleared_var v hv hex).1]; simp
    · intro v hv hz; rw [e_nv] at hv; rw [e_va] at hz; rw [e_la, e_rs]
      by_cases hex : ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = v
      · exfalso; obtain ⟨i, hi, hiv⟩ := hex
        have hkv := hbt.kept_var v hv ⟨i, hi, hiv⟩
        rw [hkv.2.2.1] at hz
        exact (hinv.assign.vals_nz_iff_trl (2 * v) (by omega)).mpr
          ⟨i, Nat.lt_of_lt_of_le hi hbt.te_le, by omega⟩ hz
      · have hcv := hbt.cleared_var v hv hex; rw [hcv.1, hcv.2.1]; exact ⟨rfl, rfl⟩
    · intro i j hij hj; rw [e_te] at hj; rw [e_la, e_trl]
      have hi_ks := Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hij hj) hbt.te_le
      have hj_ks := Nat.lt_of_lt_of_le hj hbt.te_le
      have hli := hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hi_ks htrl_len)
      have hlj := hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hj_ks htrl_len)
      rw [(hbt.kept_var _ (by omega) ⟨i, by omega, rfl⟩).1,
        (hbt.kept_var _ (by omega) ⟨j, hj, rfl⟩).1]
      exact hinv.assign.trl_lvl_mono i j hij hj_ks
    · intro i j hji hi hpos heq; rw [e_te] at hi
      rw [e_la, e_trl] at hpos heq; rw [e_trl, e_rs]
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
      have hkv := hbt.kept_var (l / 2) (by omega) ⟨i, hi, rfl⟩
      rw [e_la, e_trl] at hl0; change st.lvlArr[l / 2]?.getD 0#32 = 0#32 at hl0
      rw [hkv.1] at hl0
      have h0 := hinv.assign.lvl0_ok i hi_ks hl0
      have hsy := hsync' i (by rw [e_te]; exact hi)
      exact ⟨hsy.1, hsy.2, by rw [e_trl]; exact h0.2.2⟩
  have hre' : K6ReasonOk st' := fun i hi => by
    rw [e_te] at hi
    have hi_ks := Nat.lt_of_lt_of_le hi hbt.te_le
    let l := (ks.trl[i]?.getD 0#32).toNat
    have hl_lt := hinv.assign.trl_lt l (k6_mem_trailLits_of_lt hi_ks htrl_len)
    have hkv := hbt.kept_var (l / 2) (by omega) ⟨i, hi, rfl⟩
    change let l := (st'.trl[i]?.getD 0#32).toNat; let r := st'.rsn[l / 2]?.getD 0#32; _
    rw [e_trl, e_rs, hkv.2.1, e_nc]
    have hcl_eq : ∀ c, k6ClauseLits st' c = k6ClauseLits ks c := fun c => by
      unfold k6ClauseLits k6ClauseOff k6ClauseSize; rw [hpres.clOff, hpres.clSz, hpres.arena]
    rcases hinv.reasons i hi_ks with hnone | ⟨hr_lt, hmem, hoth⟩
    · exact Or.inl hnone
    · right; rw [hcl_eq]; exact ⟨hr_lt, hmem, hoth⟩
  refine ⟨⟨hsh', hcl', hw', hba', hre'⟩, hsync', e_lvl, by rw [e_te]; exact hbt.te_le, hpres, ?_⟩
  intro i hi; rw [e_te] at hi
  have hi_ks := Nat.lt_of_lt_of_le hi hbt.te_le
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
  have hsync : K6TrailSynced st := fun i hi => by rw [e_te] at hi; simp at hi
  refine ⟨fun P => ⟨hsh, ?_, ?_, ?_, fun i hi => by rw [e_te] at hi; simp at hi⟩, hsync⟩
  · refine ⟨e_ac, e_mv, e_mo, e_mc, by rw [e_nv]; exact hnv_le, by rw [e_nc]; simp,
      by simp [e_al], by rw [e_na]; simp, by rw [e_nk]; simp, by rw [e_nn]; simp,
      fun cid hc => by rw [e_nc] at hc; simp at hc,
      fun _ _ _ hc => by rw [e_nc] at hc; simp at hc,
      fun hi => absurd e_in hi,
      fun i hi => by rw [e_na] at hi; simp at hi,
      fun v hv => by rw [e_nv] at hv; rw [(hvars v hv).2.2, Option.getD_some]; decide⟩
  · refine ⟨List.replicate (2 * nv.toNat) [], by rw [e_nv]; simp,
      by rw [List.flatten_replicate_nil]; exact List.nodup_nil, ?_, ?_⟩
    · intro l hl; rw [e_nv] at hl
      rw [(hlits l hl).2, Option.getD_some]
      simp only [List.getElem?_replicate, hl, ↓reduceIte, Option.getD_some]
      exact K5WChain.nil
    · intro l hl w hw; rw [e_nv] at hl
      simp only [List.getElem?_replicate, hl, ↓reduceIte, Option.getD_some] at hw
      cases hw
  · refine ⟨by simp [e_te], by simp [e_prop, e_te], by rw [e_un, e_te, e_nv]; simp,
      fun l hl => by rw [e_nv] at hl; rw [(hlits l hl).1]; left; rfl,
      fun l hl => by
        rw [e_nv] at hl
        have hnl : l ^^^ 1 < 2 * nv.toNat := by
          rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
        rw [(hlits l hl).1, (hlits (l ^^^ 1) hnl).1]; simp,
      fun l hl => by rw [e_nv] at hl; rw [(hlits l hl).1]; simp [e_te],
      by unfold k6TrailLits; rw [e_te]; simp,
      fun l hl => by unfold k6TrailLits at hl; rw [e_te] at hl; simp at hl,
      fun v hv => by rw [e_nv] at hv; rw [(hvars v hv).1, e_lvl]; simp,
      fun v hv _ => by rw [e_nv] at hv; rw [(hvars v hv).1, (hvars v hv).2.1]; exact ⟨rfl, rfl⟩,
      fun _ _ _ hj => by rw [e_te] at hj; simp at hj,
      fun _ _ _ hi => by rw [e_te] at hi; simp at hi,
      fun _ hi => by rw [e_te] at hi; simp at hi⟩

theorem k6AddClause_ge2_preserves {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    {ar : List (BitVec 32)} {xs : List (BitVec 32)} {sz : BitVec 32}
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
  intro stM ks'
  have := L.hmaxV; have := L.hacap
  have hnc_mc : ks.nc.toNat < L.maxCl := hnc_lt
  have hnc1 : (ks.nc + 1#32).toNat = ks.nc.toNat + 1 := by
    unfold K6Layout.maxCl at hnc_lt; bv_omega
  have hal1 : (ks.alen + sz).toNat = ks.alen.toNat + sz.toNat := by
    unfold dimacsBound at *; bv_omega
  have hsh_ar : ({ ks with arena := ar } : K6State).ShapesOk L :=
    { hinv.shapes with arena_len := har_len }
  have hshM : stM.ShapesOk L :=
    (((hsh_ar.putHdr .alen _).putArr .clOff _ _).putArr .clSz _ _).putHdr .nc _
  have hcl_old : ∀ c < ks.nc.toNat,
      k6ClauseOff stM c = k6ClauseOff ks c ∧ k6ClauseSize stM c = k6ClauseSize ks c ∧
      k6ClauseLits stM c = k6ClauseLits ks c := fun c hc => by
    have hoff : k6ClauseOff stM c = k6ClauseOff ks c := by
      unfold k6ClauseOff; dsimp only [stM]; k6_field; rw [List.getElem?_set_ne (by omega)]
    have hszc : k6ClauseSize stM c = k6ClauseSize ks c := by
      unfold k6ClauseSize; dsimp only [stM]; k6_field; rw [List.getElem?_set_ne (by omega)]
    have hwf := hinv.clauses.cl_wf c hc
    have hlits : k6ClauseLits stM c = k6ClauseLits ks c := by
      unfold k6ClauseLits; rw [hoff, hszc]
      have har_eq : stM.arena = ar := by dsimp only [stM]; k6_field
      rw [har_eq]; congr 1
      apply List.ext_getElem
      · simp [List.length_take, List.length_drop, har_len, hinv.shapes.arena_len]
      · intro k hk1 _
        have hk_sz : k < k6ClauseSize ks c := by simp [List.length_take] at hk1; omega
        have hal_le := hinv.clauses.alen_le
        have har0 := hinv.shapes.arena_len
        have hbd_al : k6ClauseOff ks c + k6ClauseSize ks c ≤ ks.alen.toNat := hwf.2.1
        simp only [List.getElem_take, List.getElem_drop]
        have hg := har_old (k6ClauseOff ks c + k) (by omega)
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hg
        exact Option.some.inj hg
    exact ⟨hoff, hszc, hlits⟩
  have hnew_off : k6ClauseOff stM ks.nc.toNat = ks.alen.toNat := by
    unfold k6ClauseOff; dsimp only [stM]; k6_field
    rw [List.getElem?_set_self (by rw [hinv.shapes.clOff_len]; exact hnc_mc), Option.getD_some]
  have hnew_sz : k6ClauseSize stM ks.nc.toNat = sz.toNat := by
    unfold k6ClauseSize; dsimp only [stM]; k6_field
    rw [List.getElem?_set_self (by rw [hinv.shapes.clSz_len]; exact hnc_mc), Option.getD_some]
  have hnew_lits : k6ClauseLits stM ks.nc.toNat = (xs.take sz.toNat).map BitVec.toNat := by
    unfold k6ClauseLits; rw [hnew_off, hnew_sz]
    have har_eq : stM.arena = ar := by dsimp only [stM]; k6_field
    rw [har_eq]; congr 1
    apply List.ext_getElem
    · simp [List.length_take, List.length_drop, har_len]; omega
    · intro k hk1 _
      have hk_sz : k < sz.toNat := by simp [List.length_take] at hk1; omega
      simp only [List.getElem_take, List.getElem_drop]
      have hg := har_new k hk_sz
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hg
      exact Option.some.inj hg
  have hks'_ar : ks'.arena = ar := by
    dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
  have hks'_nc : ks'.nc = ks.nc + 1#32 := by
    dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
  have hks'_nv : ks'.nv = ks.nv := by
    dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
  have hks'_al : ks'.alen = ks.alen + sz := by
    dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
  have hcl' : K6ClausesOk L P ks' := by
    refine ⟨by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]
               k6_field; exact hinv.clauses.acap_eq,
      by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field; exact hinv.clauses.max_v_eq,
      by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field; exact hinv.clauses.max_orig_eq,
      by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field; exact hinv.clauses.max_cl_eq,
      by rw [hks'_nv]; exact hinv.clauses.nv_le, by rw [hks'_nc, hnc1]; omega,
      by rw [hks'_al, hal1]; exact hfit,
      by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field; exact hinv.clauses.nassump_le,
      by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field; exact hinv.clauses.nkl_le,
      by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field; exact hinv.clauses.nana_le,
      ?_, ?_,
      by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field; exact hinv.clauses.incons_ok,
      by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field; exact hinv.clauses.assump_ok,
      by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field; exact hinv.clauses.flags_clean⟩
    · intro cid hc; rw [hks'_nc, hnc1] at hc
      have heq_cl : k6ClauseOff ks' cid = k6ClauseOff stM cid ∧
          k6ClauseSize ks' cid = k6ClauseSize stM cid ∧
          k6ClauseLits ks' cid = k6ClauseLits stM cid := ⟨rfl, rfl, rfl⟩
      rw [heq_cl.1, heq_cl.2.1, heq_cl.2.2, hks'_al, hal1, hks'_nv]
      by_cases hcid : cid = ks.nc.toNat
      · subst hcid; rw [hnew_off, hnew_sz, hnew_lits]
        refine ⟨hsz2, Nat.le_refl _, fun l hl => ?_, hent⟩
        rw [List.mem_map] at hl; obtain ⟨b, hb, rfl⟩ := hl
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
        have hj_sz : j < sz.toNat := by simp [List.length_take] at hj; omega
        simp only [List.getElem_take]
        have hxj := hxlits j hj_sz
        rwa [List.getElem?_eq_getElem (by omega : j < xs.length), Option.getD_some] at hxj
      · have hlt : cid < ks.nc.toNat := by omega
        obtain ⟨ho, hs, hl⟩ := hcl_old cid hlt
        rw [ho, hs, hl]; have hw := hinv.clauses.cl_wf cid hlt
        exact ⟨hw.1, by omega, hw.2.2.1, hw.2.2.2⟩
    · intro c1 c2 h12 h2; rw [hks'_nc, hnc1] at h2
      change k6ClauseOff stM c1 + k6ClauseSize stM c1 ≤ k6ClauseOff stM c2
      have ho1 := hcl_old c1 (by omega)
      rw [ho1.1, ho1.2.1]
      by_cases h2e : c2 = ks.nc.toNat
      · subst h2e; rw [hnew_off]; exact (hinv.clauses.cl_wf c1 (by omega)).2.1
      · have ho2 := hcl_old c2 (by omega); rw [ho2.1]
        exact hinv.clauses.cl_mono c1 c2 h12 (by omega)
  have hwM : K6WatchesOk stM := by
    obtain ⟨chains, hlen, hnd, hwc, hbnd⟩ := hinv.watches
    refine ⟨chains, by dsimp only [stM]; k6_field; exact hlen, hnd,
      by dsimp only [stM]; k6_field; exact hwc, fun l hl w hw => ?_⟩
    have hl' : l < 2 * ks.nv.toNat := by revert hl; dsimp only [stM]; k6_field; exact id
    obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ := hbnd l hl' w hw
    have ho := hcl_old (w / 2) (by omega)
    have har_get : stM.arena[k6ClauseOff ks (w / 2) + w % 2]? =
        ks.arena[k6ClauseOff ks (w / 2) + w % 2]? := by
      have har_eq : stM.arena = ar := by dsimp only [stM]; k6_field
      rw [har_eq]; have hwf := hinv.clauses.cl_wf (w / 2) (by omega)
      exact har_old _ (by omega)
    have har_get1 : stM.arena[k6ClauseOff ks (w / 2) + (w % 2 ^^^ 1)]? =
        ks.arena[k6ClauseOff ks (w / 2) + (w % 2 ^^^ 1)]? := by
      have har_eq : stM.arena = ar := by dsimp only [stM]; k6_field
      rw [har_eq]; have hwf := hinv.clauses.cl_wf (w / 2) (by omega)
      rcases Nat.mod_two_eq_zero_or_one w with hm0 | hm1
      · rw [hm0, show (0 ^^^ 1 : Nat) = 1 from by decide]; exact har_old _ (by omega)
      · rw [hm1, show (1 ^^^ 1 : Nat) = 0 from by decide]; exact har_old _ (by omega)
    refine ⟨by dsimp only [stM]; k6_field; rw [hnc1]; omega,
      by rw [ho.2.1]; exact hw2, by rw [ho.1, har_get]; exact hw3,
      by dsimp only [stM]; k6_field; exact hw4,
      by rw [ho.2.2]; dsimp only [stM]; k6_field; exact hw5,
      by rw [ho.2.1]; dsimp only [stM]; k6_field; exact hw6,
      fun h2 => by
        rw [ho.2.1] at h2; rw [ho.1, har_get1]
        dsimp only [stM]; k6_field; exact hw7 h2⟩
  have hl0_lt : (xs[0]'(by omega)).toNat < 2 * stM.nv.toNat := by
    have h0 := hxlits 0 (by omega); rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
    dsimp only [stM]; k6_field; exact h0
  have hl1_lt : (xs[1]'(by omega)).toNat < 2 * stM.nv.toNat := by
    have h1 := hxlits 1 (by omega); rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1
    dsimp only [stM]; k6_field; exact h1
  have hl0_mem : (xs[0]'(by omega)).toNat ∈ k6ClauseLits stM ks.nc.toNat := by
    rw [hnew_lits, List.mem_map]; refine ⟨xs[0]'(by omega), ?_, rfl⟩
    rw [List.mem_take_iff_getElem]; exact ⟨0, by omega, by simp⟩
  have hl1_mem : (xs[1]'(by omega)).toNat ∈ k6ClauseLits stM ks.nc.toNat := by
    rw [hnew_lits, List.mem_map]; refine ⟨xs[1]'(by omega), ?_, rfl⟩
    rw [List.mem_take_iff_getElem]; exact ⟨1, by omega, by simp⟩
  have hw' : K6WatchesOk ks' :=
    k6WatchStep_preserves_watches hshM hwM
      (by dsimp only [stM]; k6_field; rw [hnc1]; omega)
      (by dsimp only [stM]; k6_field; rw [hnc1]; omega)
      (by dsimp only [stM]; k6_field; exact hinv.clauses.nv_le)
      hl0_lt hl1_lt (by rw [hnew_sz]; exact hsz2) hl0_mem hl1_mem
      (by rw [hnew_off]; have har_eq : stM.arena = ar := by dsimp only [stM]; k6_field
          have h0 := har_new 0 (by omega); rw [Nat.add_zero] at h0
          rw [har_eq, h0, List.getElem?_eq_getElem (by omega), Option.getD_some])
      (by rw [hnew_off]; have har_eq : stM.arena = ar := by dsimp only [stM]; k6_field
          rw [har_eq, har_new 1 (by omega), List.getElem?_eq_getElem (by omega), Option.getD_some])
      (fun chains hclen _ hwc => by
        obtain ⟨ch0, h0len, _, h0wc, h0bnd⟩ := hinv.watches
        have hwn_eq : stM.wnext = ks.wnext := by dsimp only [stM]; k6_field
        have hwh_eq : stM.whead = ks.whead := by dsimp only [stM]; k6_field
        have hnv_eq : stM.nv = ks.nv := by dsimp only [stM]; k6_field
        have hcheq : chains = ch0 := by
          apply List.ext_getElem (by rw [hclen, hnv_eq, h0len])
          intro x hx1 hx2
          have hx_nv : x < 2 * ks.nv.toNat := by omega
          have hc1 := hwc x (by rw [hnv_eq]; exact hx_nv)
          have hc2 := h0wc x hx_nv
          rw [hwn_eq, hwh_eq, List.getElem?_eq_getElem hx1, Option.getD_some] at hc1
          rw [List.getElem?_eq_getElem hx2, Option.getD_some] at hc2
          refine k6_wchain_unique (by rw [hinv.shapes.wnext_len]
                                      unfold K6Layout.maxCl; omega) hc1 hc2
        rw [hcheq]; constructor <;> intro hmem <;>
          (obtain ⟨ch, hch_m, hw_m⟩ := List.mem_flatten.mp hmem
           obtain ⟨x, hx, rfl⟩ := List.getElem_of_mem hch_m
           have hb := h0bnd x (by omega) _ (by simpa [List.getElem?_eq_getElem hx] using hw_m)
           omega))
  have hba' : K6BaseAssignOk P ks' := by
    have h1 : ks'.trl_end = ks.trl_end := by
      dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    have h2 : ks'.prop = ks.prop := by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    have h3 : ks'.unass = ks.unass := by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    have h4 : ks'.vals = ks.vals := by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    have h5 : ks'.trl = ks.trl := by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    have h6 : ks'.lvl = ks.lvl := by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    have h7 : ks'.lvlArr = ks.lvlArr := by
      dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    have h8 : ks'.rsn = ks.rsn := by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    exact ⟨by rw [h1, hks'_nv]; exact hinv.assign.trl_end_le,
      by rw [h2, h1]; exact hinv.assign.prop_le,
      by rw [h3, h1, hks'_nv]; exact hinv.assign.unass_eq,
      by rw [hks'_nv, h4]; exact hinv.assign.vals_dom,
      by rw [hks'_nv, h4]; exact hinv.assign.vals_neg_iff,
      by rw [hks'_nv, h4, h1, h5]; exact hinv.assign.vals_nz_iff_trl,
      by unfold k6TrailLits; rw [h1, h5]; exact hinv.assign.trl_nodup,
      by unfold k6TrailLits; rw [hks'_nv, h1, h5]; exact hinv.assign.trl_lt,
      by rw [hks'_nv, h7, h6]; exact hinv.assign.trl_lvl_le,
      by rw [hks'_nv, h4, h7, h8]; exact hinv.assign.unass_lvl_zero,
      by rw [h1, h7, h5]; exact hinv.assign.trl_lvl_mono,
      by rw [h1, h7, h5, h8]; exact hinv.assign.dec_earliest,
      by rw [h1, h5, h7, h4]; exact hinv.assign.lvl0_ok⟩
  have hre' : K6ReasonOk ks' := fun i hi => by
    have h1 : ks'.trl_end = ks.trl_end := by
      dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    have h5 : ks'.trl = ks.trl := by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    have h8 : ks'.rsn = ks.rsn := by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    rw [h1] at hi
    change let l := (ks'.trl[i]?.getD 0#32).toNat; let r := ks'.rsn[l / 2]?.getD 0xFFFFFFFF#32; _
    rw [h5, h8, hks'_nc]
    rcases hinv.reasons i hi with hnone | ⟨hr_lt, hmem, hoth⟩
    · exact Or.inl hnone
    · right; have ho := hcl_old _ hr_lt
      have hl_eq :
          k6ClauseLits ks' (ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat =
          k6ClauseLits ks (ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat :=
        ho.2.2
      rw [hnc1, hl_eq]; exact ⟨by omega, hmem, hoth⟩
  have hsync' : K6TrailSynced ks' := by
    have h1 : ks'.trl_end = ks.trl_end := by
      dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    have h4 : ks'.vals = ks.vals := by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    have h5 : ks'.trl = ks.trl := by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    intro i hi; rw [h1] at hi; unfold K6TrailSynced at hsync
    change ks'.vals[(ks'.trl[i]?.getD 0#32).toNat]? = some 1#32 ∧
      ks'.vals[(ks'.trl[i]?.getD 0#32).toNat ^^^ 1]? = some 2#32
    rw [h4, h5]; exact hsync i hi
  have hlb' : ∀ M, (∀ j < sz.toNat, (xs[j]?.getD 0#32).toNat < 2 * M) →
      K6LitsBounded M ks → K6LitsBounded M ks' := fun M hxsM hM => by
    have hnc4 : ks.nc.toNat < 4 * L.maxV := hnc_lt
    have hxs1 : 1 < xs.length := by omega
    constructor
    · intro cid hcid l hl
      rw [hks'_nc, hnc1] at hcid
      have heq_cl : k6ClauseLits ks' cid = k6ClauseLits stM cid := rfl
      rw [heq_cl] at hl
      by_cases hc : cid = ks.nc.toNat
      · subst hc; rw [hnew_lits] at hl
        rw [List.mem_map] at hl; obtain ⟨b, hb, rfl⟩ := hl
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
        have hj_sz : j < sz.toNat := by simp [List.length_take] at hj; omega
        simp only [List.getElem_take]
        have hx := hxsM j hj_sz
        rwa [List.getElem?_eq_getElem (by omega : j < xs.length), Option.getD_some] at hx
      · rw [(hcl_old cid (by omega)).2.2] at hl; exact hM.1 cid (by omega) l hl
    · intro w hw; rw [hks'_nc, hnc1] at hw
      have hw0 := k6_bv32_cid_w0 hnc_lt (by unfold K6Layout.maxCl; omega)
      have hw1 := k6_bv32_cid_w1 hnc_lt (by unfold K6Layout.maxCl; omega)
      let bf : BitVec 32 := if (stM.clSz[ks.nc.toNat]?.getD 0#32).toNat = 2 then 0x80000000#32
        else 0#32
      have hwb_eq : ks'.wblit =
          (ks.wblit.set (2 * ks.nc.toNat) ((xs[1]'(by omega)) ||| bf)).set
            (2 * ks.nc.toNat + 1) ((xs[0]'(by omega)) ||| bf) := by
        dsimp only [ks', k6WatchStep, k6WatchStep0, bf]
        rw [hw0.1, hw1.1]; dsimp only [stM]; k6_field
      have h0_lt31 : (xs[0]'(by omega)).toNat < 2 ^ 31 := by
        have hx0 := hxlits 0 (by omega); have := hinv.clauses.nv_le
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hx0; omega
      have h1_lt31 : (xs[1]'(by omega)).toNat < 2 ^ 31 := by
        have hx1 := hxlits 1 (by omega); have := hinv.clauses.nv_le
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hx1; omega
      have hbf_m0 : ((xs[0]'(by omega)) ||| bf) &&& 0x7FFFFFFF#32 = xs[0]'(by omega) := by
        dsimp only [bf]; split
        · exact (k6_bv32_or_bin_mask h0_lt31).1
        · rw [BitVec.or_zero]; exact (k6_bv32_lt31_and_mask h0_lt31).1
      have hbf_m1 : ((xs[1]'(by omega)) ||| bf) &&& 0x7FFFFFFF#32 = xs[1]'(by omega) := by
        dsimp only [bf]; split
        · exact (k6_bv32_or_bin_mask h1_lt31).1
        · rw [BitVec.or_zero]; exact (k6_bv32_lt31_and_mask h1_lt31).1
      rw [hwb_eq]
      by_cases h1 : w = 2 * ks.nc.toNat + 1
      · subst h1
        rw [List.getElem?_set_self (by
          simp only [List.length_set, hinv.shapes.wblit_len]; unfold K6Layout.maxCl; omega),
          Option.getD_some, hbf_m0]
        have hx := hxsM 0 (by omega)
        rwa [List.getElem?_eq_getElem (by omega : 0 < xs.length), Option.getD_some] at hx
      · rw [List.getElem?_set_ne (Ne.symm h1)]
        by_cases h0 : w = 2 * ks.nc.toNat
        · subst h0
          rw [List.getElem?_set_self (by rw [hinv.shapes.wblit_len]; unfold K6Layout.maxCl; omega),
            Option.getD_some, hbf_m1]
          have hx := hxsM 1 (by omega)
          rwa [List.getElem?_eq_getElem (by omega : 1 < xs.length), Option.getD_some] at hx
        · rw [List.getElem?_set_ne (Ne.symm h0)]; exact hM.2 w (by omega)
  exact ⟨⟨k6WatchStep_preserves_shapes hshM ks.nc (xs[0]'(by omega)) (xs[1]'(by omega)),
    hcl', hw', hba', hre'⟩, hsync',
    by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field, hks'_nv,
    by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field,
    by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field,
    by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field,
    by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field,
    by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field, hlb'⟩

end LeanQbe.T.Examples.Kissat.Proof.Kitten

end
