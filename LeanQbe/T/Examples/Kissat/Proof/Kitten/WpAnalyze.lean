/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Kitten.WpAnalyze0

/-!
# Step-13 `Func.wp` Proof for `full_k6_analyze` (`11/14`, `Kissat.Proof.Kitten.WpAnalyze`)

Certifies `full_k6_analyze_wp` (`step13K6AnalyzeSpec`) against `Src.Kitten.full_k6_analyze_body`
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

section DynKlMem
@[scoped bv_c0] private theorem k6c_sext_1 :
    BitVec.signExtend 64 1#32 = BitVec.ofNat 64 1 := rfl
@[scoped c0_load] private theorem load_k6_kl_dyn_z0 {L : K6Layout} {kPtr : BitVec 64}
    {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64} (hm : (K6MemA L kPtr ks ⋆ R) m) :
    loadVal m i32
      ((kPtr + ((32 : BitVec 32) + (8 : BitVec 32) * L.mv32).setWidth 64 * 4) +
        BitVec.ofNat 64 0 * 4) = some (ks.kl[0]?.getD 0#32) := by
  rw [k6_ptr_kl L kPtr]; exact load_k6_kl0 hm
@[scoped c0_store] private theorem store_k6_kl_dyn_z0 {L : K6Layout} {kPtr : BitVec 64}
    {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32)
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32
      ((kPtr + ((32 : BitVec 32) + (8 : BitVec 32) * L.mv32).setWidth 64 * 4) +
        BitVec.ofNat 64 0 * 4) ∧
      (K6MemA L kPtr (ks.putArr .kl 0 v) ⋆ R)
        (storeMem m i32
          ((kPtr + ((32 : BitVec 32) + (8 : BitVec 32) * L.mv32).setWidth 64 * 4) +
            BitVec.ofNat 64 0 * 4) v) := by
  rw [k6_ptr_kl L kPtr]; exact store_k6_kl0 v hm
@[scoped c0_load] private theorem load_k6_kl_dyn_z1 {L : K6Layout} {kPtr : BitVec 64}
    {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64} (hm : (K6MemA L kPtr ks ⋆ R) m) :
    loadVal m i32
      ((kPtr + ((32 : BitVec 32) + (8 : BitVec 32) * L.mv32).setWidth 64 * 4) +
        BitVec.ofNat 64 1 * 4) = some (ks.kl[1]?.getD 0#32) := by
  rw [k6_ptr_kl L kPtr]; exact load_k6_kl1 hm
@[scoped c0_store] private theorem store_k6_kl_dyn_z1 {L : K6Layout} {kPtr : BitVec 64}
    {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32)
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32
      ((kPtr + ((32 : BitVec 32) + (8 : BitVec 32) * L.mv32).setWidth 64 * 4) +
        BitVec.ofNat 64 1 * 4) ∧
      (K6MemA L kPtr (ks.putArr .kl 1 v) ⋆ R)
        (storeMem m i32
          ((kPtr + ((32 : BitVec 32) + (8 : BitVec 32) * L.mv32).setWidth 64 * 4) +
            BitVec.ofNat 64 1 * 4) v) := by
  rw [k6_ptr_kl L kPtr]; exact store_k6_kl1 v hm
end DynKlMem

private structure K6AnaBrkPost (L : K6Layout) (P : (Nat → Bool) → Prop) (ks : K6State)
    (uip : BitVec 32) (st : K6State) : Prop where
  sh : st.ShapesOk L
  pres : K6AnaPreserved ks st
  tail : K6TailEq L ks st
  nkl_pos : 1 ≤ st.nkl.toNat
  nkl_le : st.nkl.toNat ≤ st.nv.toNat
  nana_le : st.nana.toNat ≤ st.nv.toNat
  ana_lt : ∀ i < st.nana.toNat, (st.ana[i]?.getD 0#32).toNat < st.nv.toNat
  flags_seen : ∀ v < st.nv.toNat,
    ((st.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32) ↔
      ∃ i < st.nana.toNat, (st.ana[i]?.getD 0#32).toNat = v
  uip_ok : uip ≠ 0xFFFFFFFF#32 →
    uip.toNat < 2 * st.nv.toNat ∧ st.lvlArr[uip.toNat / 2]?.getD 0#32 = st.lvl ∧
    (∀ i, 1 ≤ i → i < st.nkl.toNat →
      let l := (st.kl[i]?.getD 0#32).toNat
      l < 2 * st.nv.toNat ∧ 0 < (st.lvlArr[l / 2]?.getD 0#32).toNat ∧
      (st.lvlArr[l / 2]?.getD 0#32).toNat < st.lvl.toNat ∧ st.vals[l]? = some 2#32) ∧
    SemEntails P (uip.toNat :: ((st.kl.take st.nkl.toNat).drop 1).map BitVec.toNat)

private theorem k6AnaBrkPost_of_uip_ff {L : K6Layout} {P : (Nat → Bool) → Prop} {ks st : K6State}
    {idx : Nat} (hinv : K6AnaInv L P st idx) (hp : K6AnaPreserved ks st)
    (htl : K6TailEq L ks st) : K6AnaBrkPost L P ks 0xFFFFFFFF#32 st :=
  ⟨hinv.shapes, hp, htl, hinv.nkl_pos, hinv.nkl_le, hinv.nana_le, hinv.ana_lt, hinv.flags_seen,
   fun h => absurd rfl h⟩

private theorem k6a_clear_flags_exit {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks stB : K6State} {uip : BitVec 32} {fls : List (BitVec 32)}
    (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks) (hBrk : K6AnaBrkPost L P ks uip stB)
    (hfls_len : fls.length = L.maxV)
    (hna_mv : stB.nana.toNat ≤ L.maxV) (hnk_mv : stB.nkl.toNat ≤ L.maxV)
    (hcl_done : ∀ v < stB.nv.toNat, (∃ j < stB.nana.toNat, (stB.ana[j]?.getD 0#32).toNat = v) →
      (fls[v]?.getD 0#32 &&& 2#32) = 0#32)
    (hcl_orig : ∀ v < stB.nv.toNat, (stB.flags[v]?.getD 0#32 &&& 2#32) = 0#32 →
      (fls[v]?.getD 0#32 &&& 2#32) = 0#32)
    (htl_fl : ∀ v, stB.nv.toNat ≤ v → v < L.maxV → fls[v]? = stB.flags[v]?) :
    let stF : K6State := { stB with flags := fls }
    K6Inv L P stF ∧ K6TrailSynced stF ∧ K6AnaPreserved ks stF ∧ K6TailEq L ks stF := by
  intro stF
  have hfl_clean : ∀ v < stF.nv.toNat, (stF.flags[v]?.getD 0#32 &&& 2#32) = 0#32 := by
    intro v hv; dsimp only [stF] at hv ⊢
    by_cases hnz : (stB.flags[v]?.getD 0#32 &&& 2#32) = 0#32
    · exact hcl_orig v hv hnz
    · exact hcl_done v hv ((hBrk.flags_seen v hv).mp hnz)
  have hshF : stF.ShapesOk L := { hBrk.sh with flags_len := hfls_len }
  have hpresF : K6AnaPreserved ks stF :=
    ⟨hBrk.pres.nv, hBrk.pres.nc, hBrk.pres.lvl, hBrk.pres.prop, hBrk.pres.trl_end,
     hBrk.pres.unass, hBrk.pres.incons, hBrk.pres.alen, hBrk.pres.acap, hBrk.pres.nassump,
     hBrk.pres.status, hBrk.pres.max_v, hBrk.pres.max_orig, hBrk.pres.max_cl, hBrk.pres.neq,
     hBrk.pres.lvlArr, hBrk.pres.rsn, hBrk.pres.trl, hBrk.pres.vals, hBrk.pres.assump,
     hBrk.pres.whead, hBrk.pres.wnext, hBrk.pres.wblit, hBrk.pres.clOff, hBrk.pres.clSz,
     hBrk.pres.arena⟩
  have ⟨hinvF, hsyncF⟩ := k6a_inv_of_ana_clean hinv hsync hshF hpresF hnk_mv hna_mv hfl_clean
  exact ⟨hinvF, hsyncF, hpresF, k6a_clear_flags_tail hBrk.tail htl_fl⟩

private theorem k6a_nkl1_finish {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks stSw ksBt st5 : K6State} {uip jlvl : BitVec 32} {kPtr : BitVec 64}
    {R : Mem 64 → Prop} {mFin : Mem 64} {Q : Post [.bool]}
    (hQ : ∀ (ok : Bool) (ks' : K6State) (m' : Mem 64),
      K6Inv L P ks' → K6TrailSynced ks' → ks'.nv = ks.nv → K6TailEq L ks ks' →
      ks'.nassump = ks.nassump → ks'.assump = ks.assump → ks'.incons = ks.incons →
      ks'.status = ks.status → ks'.neq = ks.neq →
      (ok = true → ks'.lvl.toNat < ks.lvl.toNat ∧
        (0 < ks'.lvl.toNat → ∃ i < ks'.trl_end.toNat,
          ks'.lvlArr[(ks'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = ks'.lvl) ∧
        (∀ d ∈ k6TrailDecisions ks', ∃ i < ks.trl_end.toNat,
          (ks.trl[i]?.getD 0#32).toNat = d ∧ d ∈ k6TrailDecisions ks ∧
          (ks.lvlArr[d / 2]?.getD 0#32).toNat ≤ ks'.lvl.toNat) ∧
        (∀ i < ks.trl_end.toNat,
          (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ ks'.lvl.toNat →
          i < ks'.trl_end.toNat ∧ ks'.trl[i]? = ks.trl[i]? ∧
          ks'.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? =
            ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?)) →
      (K6Mem L kPtr ks' ⋆ R) m' → Q (ok, ()) m')
    (hinv5 : K6Inv L P st5) (hsync5 : K6TrailSynced st5)
    (hst5_eq : ∃ qf ql qs qst qp qn qsa, st5 =
      { ksBt with qfirst := qf, qlast := ql, qsearch := qs, qstamp := qst,
                  qprev := qp, qnext := qn, qstampArr := qsa })
    (hbtPres : K6BtPreserved stSw ksBt) (hpresSw : K6AnaPreserved ks stSw)
    (htl_st5 : K6TailEq L ks st5) (hlvlBt : ksBt.lvl = jlvl) (hj0 : jlvl = 0#32)
    (hj_lt : jlvl.toNat < ks.lvl.toNat) (huip_lt_k : uip.toNat < 2 * ks.nv.toNat)
    (huip_none : ¬ ∃ i < ksBt.trl_end.toNat, (ksBt.trl[i]?.getD 0#32).toNat / 2 = uip.toNat / 2)
    (huip_v0 : ksBt.vals[uip.toNat]? = some 0#32) (hte_lt_nv : ksBt.trl_end.toNat < ksBt.nv.toNat)
    (hent_uip : SemEntails P [uip.toNat])
    (hdec_ks : ∀ d ∈ k6TrailDecisions ksBt, ∃ i < ks.trl_end.toNat,
      (ks.trl[i]?.getD 0#32).toNat = d ∧ d ∈ k6TrailDecisions ks ∧
      (ks.lvlArr[d / 2]?.getD 0#32).toNat ≤ jlvl.toNat)
    (hA2_bt : ∀ i < ks.trl_end.toNat,
      (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ jlvl.toNat →
      i < ksBt.trl_end.toNat ∧ ksBt.trl[i]? = ks.trl[i]? ∧
      ksBt.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? =
        ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?)
    (hmFin : (K6Mem L kPtr (k6AssignStep st5 uip 0xFFFFFFFF#32) ⋆ R) mFin) : Q (true, ()) mFin := by
  obtain ⟨qf, ql, qs, qst, qp, qn, qsa, hst5⟩ := hst5_eq
  have hbt_nv : ksBt.nv = ks.nv := hbtPres.nv.trans hpresSw.nv
  have hst5_lvl0 : st5.lvl = 0#32 := by rw [hst5, hlvlBt, hj0]
  have huip_lt5 : uip.toNat < 2 * st5.nv.toNat := by rw [hst5, hbt_nv]; exact huip_lt_k
  obtain ⟨hinvFin, hsyncFin⟩ := k6AssignStep_preserves_inv hinv5 hsync5 (lit := uip)
    (rsn := 0xFFFFFFFF#32) huip_lt5 (by rw [hst5]; exact huip_v0) (fun _ => hent_uip)
    (fun h => by rw [hst5_lvl0] at h; simp at h) (Or.inl rfl)
  obtain ⟨hdecFin, hlwFin, htrFin⟩ := k6a_assignStep_decisions_eq hinv5 (lit := uip)
    (rsn := 0xFFFFFFFF#32) huip_lt5 (by rw [hst5]; exact hte_lt_nv)
    (by rw [hst5]; exact huip_none) (Or.inl hst5_lvl0)
  have f_lvl : (k6AssignStep st5 uip 0xFFFFFFFF#32).lvl = jlvl := by
    change st5.lvl = jlvl; rw [hst5, hlvlBt]
  have f_dec : k6TrailDecisions (k6AssignStep st5 uip 0xFFFFFFFF#32) = k6TrailDecisions ksBt := by
    rw [hdecFin]; unfold k6TrailDecisions; rw [hst5]
  have htlFin := k6TailEq_trans htl_st5 (k6TailEq_of_k6AssignStep uip 0xFFFFFFFF#32 huip_lt5)
  exact hQ true (k6AssignStep st5 uip 0xFFFFFFFF#32) mFin hinvFin hsyncFin
    (by rw [hst5]; exact hbt_nv) htlFin (by rw [hst5]; exact hbtPres.nassump.trans hpresSw.nassump)
    (by rw [hst5]; exact hbtPres.assump.trans hpresSw.assump)
    (by rw [hst5]; exact hbtPres.incons.trans hpresSw.incons)
    (by rw [hst5]; exact hbtPres.status.trans hpresSw.status)
    (by rw [hst5]; exact hbtPres.neq.trans hpresSw.neq)
    (fun _ => ⟨by rw [f_lvl]; exact hj_lt, hlwFin,
      fun d hd => by rw [f_dec] at hd; rw [f_lvl]; exact hdec_ks d hd,
      fun i hi hlv => by
        rw [f_lvl] at hlv
        obtain ⟨hi_bt, ht_bt, hl_bt⟩ := hA2_bt i hi hlv
        obtain ⟨hi_f, ht_f, hl_f⟩ := htrFin i (by rw [hst5]; exact hi_bt)
        have ht_f' : (k6AssignStep st5 uip 0xFFFFFFFF#32).trl[i]? = ksBt.trl[i]? :=
          ht_f.trans (by rw [hst5])
        have hl_f' : (k6AssignStep st5 uip 0xFFFFFFFF#32).lvlArr[
            (ks.trl[i]?.getD 0#32).toNat / 2]? =
            ksBt.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? := by
          have h1 := hl_f; have htr_st5 : st5.trl[i]? = ks.trl[i]? := by rw [hst5]; exact ht_bt
          rw [htr_st5] at h1; exact h1.trans (by rw [hst5])
        exact ⟨hi_f, ht_f'.trans ht_bt, hl_f'.trans hl_bt⟩⟩) hmFin

private theorem k6a_nkl2_assign_finish {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks stSw ksBt st5 : K6State} {uip jlvl : BitVec 32} {ar7 : List (BitVec 32)}
    {kPtr : BitVec 64} {R : Mem 64 → Prop} {mFin : Mem 64} {Q : Post [.bool]}
    (hQ : ∀ (ok : Bool) (ks' : K6State) (m' : Mem 64),
      K6Inv L P ks' → K6TrailSynced ks' → ks'.nv = ks.nv → K6TailEq L ks ks' →
      ks'.nassump = ks.nassump → ks'.assump = ks.assump → ks'.incons = ks.incons →
      ks'.status = ks.status → ks'.neq = ks.neq →
      (ok = true → ks'.lvl.toNat < ks.lvl.toNat ∧
        (0 < ks'.lvl.toNat → ∃ i < ks'.trl_end.toNat,
          ks'.lvlArr[(ks'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = ks'.lvl) ∧
        (∀ d ∈ k6TrailDecisions ks', ∃ i < ks.trl_end.toNat,
          (ks.trl[i]?.getD 0#32).toNat = d ∧ d ∈ k6TrailDecisions ks ∧
          (ks.lvlArr[d / 2]?.getD 0#32).toNat ≤ ks'.lvl.toNat) ∧
        (∀ i < ks.trl_end.toNat,
          (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ ks'.lvl.toNat →
          i < ks'.trl_end.toNat ∧ ks'.trl[i]? = ks.trl[i]? ∧
          ks'.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? =
            ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?)) →
      (K6Mem L kPtr ks' ⋆ R) m' → Q (ok, ()) m')
    (hinv5 : K6Inv L P st5) (hsync5 : K6TrailSynced st5)
    (hst5_eq : ∃ qf ql qs qst qp qn qsa, st5 =
      { ksBt with qfirst := qf, qlast := ql, qsearch := qs, qstamp := qst,
                  qprev := qp, qnext := qn, qstampArr := qsa })
    (hbtPres : K6BtPreserved stSw ksBt) (hpresSw : K6AnaPreserved ks stSw)
    (htl_st5 : K6TailEq L ks st5) (hlvlBt : ksBt.lvl = jlvl)
    (hj_lt : jlvl.toNat < ks.lvl.toNat) (hjlvl_pos : 0 < jlvl.toNat)
    (huip_lt_k : uip.toNat < 2 * ks.nv.toNat)
    (huip_none : ¬ ∃ i < ksBt.trl_end.toNat, (ksBt.trl[i]?.getD 0#32).toNat / 2 = uip.toNat / 2)
    (huip_v0 : ksBt.vals[uip.toNat]? = some 0#32) (hte_lt_nv : ksBt.trl_end.toNat < ksBt.nv.toNat)
    (hkl_bt_trl : ∀ l < 2 * ks.nv.toNat, stSw.vals[l]? = some 2#32 →
      (ks.lvlArr[l / 2]?.getD 0#32).toNat ≤ jlvl.toNat →
      ∃ j < ksBt.trl_end.toNat, (ksBt.trl[j]?.getD 0#32).toNat = l ^^^ 1)
    (hdec_ks : ∀ d ∈ k6TrailDecisions ksBt, ∃ i < ks.trl_end.toNat,
      (ks.trl[i]?.getD 0#32).toNat = d ∧ d ∈ k6TrailDecisions ks ∧
      (ks.lvlArr[d / 2]?.getD 0#32).toNat ≤ jlvl.toNat)
    (hA2_bt : ∀ i < ks.trl_end.toNat,
      (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ jlvl.toNat →
      i < ksBt.trl_end.toNat ∧ ksBt.trl[i]? = ks.trl[i]? ∧
      ksBt.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? =
        ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?)
    (hsw0 : stSw.kl[0]? = some uip)
    (hsw_nt : ∀ k, 1 ≤ k → k < stSw.nkl.toNat →
      let l := (stSw.kl[k]?.getD 0#32).toNat
      l < 2 * stSw.nv.toNat ∧ 0 < (stSw.lvlArr[l / 2]?.getD 0#32).toNat ∧
      (stSw.lvlArr[l / 2]?.getD 0#32).toNat ≤ jlvl.toNat ∧ stSw.vals[l]? = some 2#32)
    (hnc_lt : st5.nc.toNat < L.maxCl) (hnkl5_ge2 : 2 ≤ st5.nkl.toNat)
    (hfit : st5.alen.toNat + st5.nkl.toNat ≤ L.acap) (har7_len : ar7.length = L.acap)
    (har7_old : ∀ k < st5.alen.toNat, ar7[k]? = st5.arena[k]?)
    (har7_lits : ∀ k < st5.nkl.toNat, ar7[st5.alen.toNat + k]? = st5.kl[k]?)
    (hent_kl5 : SemEntails P ((st5.kl.take st5.nkl.toNat).map BitVec.toNat))
    (hmFin : let stM := (((({ st5 with arena := ar7 } : K6State).putHdr .alen
        (st5.alen + st5.nkl)).putArr .clOff st5.nc.toNat st5.alen).putArr .clSz st5.nc.toNat
        st5.nkl).putHdr .nc (st5.nc + 1#32)
      let stW := k6WatchStep stM st5.nc (st5.kl[0]?.getD 0#32) (st5.kl[1]?.getD 0#32)
      (K6Mem L kPtr (k6AssignStep stW uip st5.nc) ⋆ R) mFin) : Q (true, ()) mFin := by
  have hm_v := L.hmaxV; have hac := L.hacap
  obtain ⟨qf, ql, qs, qst, qp, qn, qsa, hst5⟩ := hst5_eq
  have hbt_nv : ksBt.nv = ks.nv := hbtPres.nv.trans hpresSw.nv
  have hbt_na : ksBt.nassump = ks.nassump := hbtPres.nassump.trans hpresSw.nassump
  have hbt_as : ksBt.assump = ks.assump := hbtPres.assump.trans hpresSw.assump
  have hbt_in : ksBt.incons = ks.incons := hbtPres.incons.trans hpresSw.incons
  have hbt_st : ksBt.status = ks.status := hbtPres.status.trans hpresSw.status
  have hbt_nq : ksBt.neq = ks.neq := hbtPres.neq.trans hpresSw.neq
  have hsh5 := hinv5.shapes; have hkl5_len : st5.kl.length = L.maxV := hsh5.kl_len
  have hkl5_lt : ∀ k < st5.nkl.toNat, (st5.kl[k]?.getD 0#32).toNat < 2 * st5.nv.toNat := by
    intro k hk; rw [hst5, hbtPres.nkl] at hk; rw [hst5, hbtPres.kl, hbtPres.nv]
    by_cases hk0 : k = 0
    · subst hk0; rw [hsw0, Option.getD_some, hpresSw.nv]; exact huip_lt_k
    · exact (hsw_nt k (by omega) hk).1
  have hkl5_0 : st5.kl[0]?.getD 0#32 = uip := by rw [hst5, hbtPres.kl, hsw0, Option.getD_some]
  have hkl0_lt : (st5.kl[0]?.getD 0#32).toNat < 2 * st5.nv.toNat := hkl5_lt 0 (by omega)
  have hkl1_lt : (st5.kl[1]?.getD 0#32).toNat < 2 * st5.nv.toNat := hkl5_lt 1 (by omega)
  have hget0 : st5.kl[0]'(by omega) = st5.kl[0]?.getD 0#32 := by
    simp [List.getElem?_eq_getElem (by omega : 0 < st5.kl.length)]
  have hget1 : st5.kl[1]'(by omega) = st5.kl[1]?.getD 0#32 := by
    simp [List.getElem?_eq_getElem (by omega : 1 < st5.kl.length)]
  have hnkl5_le : st5.nkl.toNat ≤ L.maxV := hinv5.clauses.nkl_le
  have hnkl5_28 : st5.nkl.toNat < 2 ^ 28 := by omega
  obtain ⟨hinvW, hsyncW, w_lvl, w_nv, w_na, w_as, w_te, _, w_inc, _⟩ :=
    k6AddClause_ge2_preserves hinv5 hsync5 hnc_lt hnkl5_ge2 hnkl5_28 (by omega) hfit har7_len
      har7_old har7_lits hkl5_lt hent_kl5
  rw [hget0, hget1] at hinvW hsyncW w_lvl w_nv w_na w_as w_te w_inc
  let stM := (((({ st5 with arena := ar7 } : K6State).putHdr .alen
    (st5.alen + st5.nkl)).putArr .clOff st5.nc.toNat st5.alen).putArr .clSz st5.nc.toNat
    st5.nkl).putHdr .nc (st5.nc + 1#32)
  let stW := k6WatchStep stM st5.nc (st5.kl[0]?.getD 0#32) (st5.kl[1]?.getD 0#32)
  have hnc_ne : st5.nc ≠ 0xFFFFFFFF#32 := by unfold K6Layout.maxCl at hnc_lt; bv_omega
  have hnc1 : (st5.nc + 1#32).toNat = st5.nc.toNat + 1 := by
    unfold K6Layout.maxCl at hnc_lt; bv_omega
  have hstW_nc : stW.nc = st5.nc + 1#32 := by
    dsimp only [stW, k6WatchStep, k6WatchStep0, stM]; k6_field
  have hnc_ltW : st5.nc.toNat < stW.nc.toNat := by rw [hstW_nc, hnc1]; omega
  have hstW_lits : k6ClauseLits stW st5.nc.toNat =
      (st5.kl.take st5.nkl.toNat).map BitVec.toNat := by
    have hoffW : k6ClauseOff stW st5.nc.toNat = st5.alen.toNat := by
      unfold k6ClauseOff; dsimp only [stW, k6WatchStep, k6WatchStep0, stM]; k6_field
      rw [List.getElem?_set_self (by rw [hsh5.clOff_len]; omega), Option.getD_some]
    have hszW : k6ClauseSize stW st5.nc.toNat = st5.nkl.toNat := by
      unfold k6ClauseSize; dsimp only [stW, k6WatchStep, k6WatchStep0, stM]; k6_field
      rw [List.getElem?_set_self (by rw [hsh5.clSz_len]; omega), Option.getD_some]
    have harW : stW.arena = ar7 := by dsimp only [stW, k6WatchStep, k6WatchStep0, stM]; k6_field
    unfold k6ClauseLits; rw [hoffW, hszW, harW]; congr 1
    apply List.ext_getElem
    · simp [List.length_take, List.length_drop, har7_len, hkl5_len]; omega
    · intro k hk1 _; have hk_n : k < st5.nkl.toNat := by simp [List.length_take] at hk1; omega
      simp only [List.getElem_take, List.getElem_drop]
      have hg := har7_lits k hk_n
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hg
      exact Option.some.inj hg
  have huip_memW : uip.toNat ∈ k6ClauseLits stW st5.nc.toNat := by
    rw [hstW_lits, List.mem_map]; refine ⟨uip, ?_, rfl⟩
    rw [List.mem_take_iff_getElem]; refine ⟨0, by omega, ?_⟩
    have := hkl5_0; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at this; exact this
  have hstW_lvl_pos : 0 < stW.lvl.toNat := by rw [w_lvl, hst5, hlvlBt]; exact hjlvl_pos
  have hstW_trl : stW.trl = ksBt.trl := by
    dsimp only [stW, k6WatchStep, k6WatchStep0, stM]; k6_field; rw [hst5]
  have hstW_vals : stW.vals = ksBt.vals := by
    dsimp only [stW, k6WatchStep, k6WatchStep0, stM]; k6_field; rw [hst5]
  have hstW_rsn : stW.rsn = ksBt.rsn := by
    dsimp only [stW, k6WatchStep, k6WatchStep0, stM]; k6_field; rw [hst5]
  have hstW_lvlArr : stW.lvlArr = ksBt.lvlArr := by
    dsimp only [stW, k6WatchStep, k6WatchStep0, stM]; k6_field; rw [hst5]
  have hstW_st : stW.status = ks.status := by
    have h1 : stW.status = st5.status := by
      dsimp only [stW, k6WatchStep, k6WatchStep0, stM]; k6_field
    rw [h1, hst5]; exact hbt_st
  have hstW_nq : stW.neq = ks.neq := by
    have h1 : stW.neq = st5.neq := by dsimp only [stW, k6WatchStep, k6WatchStep0, stM]; k6_field
    rw [h1, hst5]; exact hbt_nq
  have hothersW : ∀ x ∈ k6ClauseLits stW st5.nc.toNat, x ≠ uip.toNat →
      ∃ j < stW.trl_end.toNat, (stW.trl[j]?.getD 0#32).toNat = x ^^^ 1 := by
    intro x hx hne; rw [hstW_lits, List.mem_map] at hx; obtain ⟨b, hb, rfl⟩ := hx
    rw [List.mem_take_iff_getElem] at hb; obtain ⟨k, hk, rfl⟩ := hb
    have hk_n : k < st5.nkl.toNat := by omega
    have hk_pos : 1 ≤ k := by
      by_cases hk0 : k = 0
      · exfalso; subst hk0; apply hne; have := hkl5_0
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at this; rw [this]
      · omega
    have hswk := hsw_nt k hk_pos (by rw [hst5, hbtPres.nkl] at hk_n; exact hk_n)
    dsimp only at hswk
    have hgetk : (stSw.kl[k]?.getD 0#32).toNat = (st5.kl[k]'(by omega)).toNat := by
      rw [← hbtPres.kl, ← show st5.kl = ksBt.kl by rw [hst5],
        List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [hgetk] at hswk; rw [w_te, show st5.trl_end = ksBt.trl_end by rw [hst5], hstW_trl]
    exact hkl_bt_trl _ (by rw [← hpresSw.nv]; exact hswk.1) hswk.2.2.2
      (by rw [← hpresSw.lvlArr]; exact hswk.2.2.1)
  have huip_ltW : uip.toNat < 2 * stW.nv.toNat := by rw [w_nv, hst5, hbt_nv]; exact huip_lt_k
  obtain ⟨hinvFin, hsyncFin⟩ := k6AssignStep_preserves_inv hinvW hsyncW (lit := uip) (rsn := st5.nc)
    huip_ltW (by rw [hstW_vals]; exact huip_v0)
    (fun h => by rw [h] at hstW_lvl_pos; simp at hstW_lvl_pos)
    (fun _ h => absurd h hnc_ne) (Or.inr ⟨hnc_ltW, huip_memW, hothersW⟩)
  obtain ⟨hdecFin, hlwFin, htrFin⟩ := k6a_assignStep_decisions_eq hinvW (lit := uip)
    (rsn := st5.nc) huip_ltW (by rw [w_te, w_nv, hst5]; exact hte_lt_nv)
    (by rw [hstW_trl, w_te, hst5]; exact huip_none) (Or.inr hnc_ne)
  have f_lvl : (k6AssignStep stW uip st5.nc).lvl = jlvl := by
    change stW.lvl = jlvl; rw [w_lvl, hst5, hlvlBt]
  have f_dec : k6TrailDecisions (k6AssignStep stW uip st5.nc) = k6TrailDecisions ksBt := by
    rw [hdecFin]; unfold k6TrailDecisions; rw [hstW_trl, hstW_lvlArr, hstW_rsn, w_te, hst5]
  have htl_stM : K6TailEq L st5 stM := by
    dsimp only [stM]; exact ⟨rfl, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  have hstM_nv : stM.nv = st5.nv := by dsimp only [stM]; k6_field
  have htl_stW := k6TailEq_trans htl_st5 (k6TailEq_trans htl_stM
    (k6TailEq_of_k6WatchStep st5.nc (st5.kl[0]?.getD 0#32) (st5.kl[1]?.getD 0#32)
      (hstM_nv ▸ hkl0_lt) (hstM_nv ▸ hkl1_lt)))
  have htlFin := k6TailEq_trans htl_stW (k6TailEq_of_k6AssignStep uip st5.nc huip_ltW)
  exact hQ true (k6AssignStep stW uip st5.nc) mFin hinvFin hsyncFin
    (w_nv.trans (by rw [hst5]; exact hbt_nv)) htlFin
    (w_na.trans (by rw [hst5]; exact hbt_na)) (w_as.trans (by rw [hst5]; exact hbt_as))
    (w_inc.trans (by rw [hst5]; exact hbt_in)) hstW_st hstW_nq
    (fun _ => ⟨by rw [f_lvl]; exact hj_lt, hlwFin,
      fun d hd => by rw [f_dec] at hd; rw [f_lvl]; exact hdec_ks d hd,
      fun i hi hlv => by
        rw [f_lvl] at hlv
        obtain ⟨hi_bt, ht_bt, hl_bt⟩ := hA2_bt i hi hlv
        obtain ⟨hi_f, ht_f, hl_f⟩ := htrFin i (by rw [w_te, hst5]; exact hi_bt)
        rw [hstW_trl] at ht_f hl_f; rw [hstW_lvlArr, ht_bt] at hl_f
        exact ⟨hi_f, ht_f.trans ht_bt, hl_f.trans hl_bt⟩⟩) hmFin

private theorem k6a_clear_flags_step_inv {stB : K6State} {ai : BitVec 32} {fls : List (BitVec 32)}
    {L : K6Layout} (hfls_len : fls.length = L.maxV) (hnvB : stB.nv.toNat ≤ L.maxV)
    (hai_lt : ai.toNat < stB.nana.toNat)
    (hav_lt : (stB.ana[ai.toNat]?.getD 0#32).toNat < stB.nv.toNat)
    (hai1 : (ai + 1#32).toNat = ai.toNat + 1)
    (hcl_done : ∀ v < stB.nv.toNat, (∃ j < ai.toNat, (stB.ana[j]?.getD 0#32).toNat = v) →
      (fls[v]?.getD 0#32 &&& 2#32) = 0#32)
    (hcl_orig : ∀ v < stB.nv.toNat, (stB.flags[v]?.getD 0#32 &&& 2#32) = 0#32 →
      (fls[v]?.getD 0#32 &&& 2#32) = 0#32)
    (htl_fl : ∀ v, stB.nv.toNat ≤ v → v < L.maxV → fls[v]? = stB.flags[v]?) :
    let av := (stB.ana[ai.toNat]?.getD 0#32).toNat
    let fls' := fls.set av (fls[av]?.getD 0#32 &&& ~~~2#32)
    (ai + 1#32).toNat ≤ stB.nana.toNat ∧ fls'.length = L.maxV ∧
    (∀ v < stB.nv.toNat, (∃ j < (ai + 1#32).toNat, (stB.ana[j]?.getD 0#32).toNat = v) →
      (fls'[v]?.getD 0#32 &&& 2#32) = 0#32) ∧
    (∀ v < stB.nv.toNat, (stB.flags[v]?.getD 0#32 &&& 2#32) = 0#32 →
      (fls'[v]?.getD 0#32 &&& 2#32) = 0#32) ∧
    (∀ v, stB.nv.toNat ≤ v → v < L.maxV → fls'[v]? = stB.flags[v]?) := by
  intro av fls'
  have hav_len : av < fls.length := by rw [hfls_len]; omega
  refine ⟨by rw [hai1]; omega, by simp [fls', hfls_len], ?_, ?_, ?_⟩
  · intro v hv ⟨j, hj, hjeq⟩; rw [hai1] at hj
    by_cases hvv : v = av
    · subst hvv; simp only [fls', List.getElem?_set_self hav_len, Option.getD_some]
      exact k6a_fl_andnot2_and2_zero _
    · simp only [fls', List.getElem?_set_ne (Ne.symm hvv)]
      by_cases hja : j = ai.toNat
      · subst hja; exact absurd hjeq.symm hvv
      · exact hcl_done v hv ⟨j, by omega, hjeq⟩
  · intro v hv h0; by_cases hvv : v = av
    · subst hvv; simp only [fls', List.getElem?_set_self hav_len, Option.getD_some]
      exact k6a_fl_andnot2_and2_zero _
    · simp only [fls', List.getElem?_set_ne (Ne.symm hvv)]; exact hcl_orig v hv h0
  · intro v hv hvm; simp only [fls', List.getElem?_set_ne (by omega : av ≠ v)]
    exact htl_fl v hv hvm

private theorem k6a_jlvl_step_inv {stF : K6State} {ks_lvl jlvl wi i il : BitVec 32}
    (hi1 : 1 ≤ i.toNat) (hi_lt : i.toNat < stF.nkl.toNat) (hj_lt : jlvl.toNat < ks_lvl.toNat)
    (hi_eq1 : i.toNat = 1 → jlvl = 0#32 ∧ wi = 1#32)
    (hi_ge2 : 2 ≤ i.toNat → 1 ≤ wi.toNat ∧ wi.toNat < i.toNat ∧ 0 < jlvl.toNat ∧
      stF.lvlArr[(stF.kl[wi.toNat]?.getD 0#32).toNat / 2]?.getD 0#32 = jlvl)
    (hall_le : ∀ k, 1 ≤ k → k < i.toNat →
      (stF.lvlArr[(stF.kl[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ jlvl.toNat)
    (hi1_add : (i + 1#32).toNat = i.toNat + 1)
    (hil_eq : il = stF.lvlArr[(stF.kl[i.toNat]?.getD 0#32).toNat / 2]?.getD 0#32)
    (hil_pos : 0 < il.toNat) (hil_lt : il.toNat < ks_lvl.toNat) :
    (jlvl.toNat < il.toNat →
      1 ≤ (i + 1#32).toNat ∧ (i + 1#32).toNat ≤ stF.nkl.toNat ∧ il.toNat < ks_lvl.toNat ∧
      ((i + 1#32).toNat = 1 → il = 0#32 ∧ i = 1#32) ∧
      (2 ≤ (i + 1#32).toNat → 1 ≤ i.toNat ∧ i.toNat < (i + 1#32).toNat ∧ 0 < il.toNat ∧
        stF.lvlArr[(stF.kl[i.toNat]?.getD 0#32).toNat / 2]?.getD 0#32 = il) ∧
      (∀ k, 1 ≤ k → k < (i + 1#32).toNat →
        (stF.lvlArr[(stF.kl[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ il.toNat)) ∧
    (il.toNat ≤ jlvl.toNat →
      1 ≤ (i + 1#32).toNat ∧ (i + 1#32).toNat ≤ stF.nkl.toNat ∧ jlvl.toNat < ks_lvl.toNat ∧
      ((i + 1#32).toNat = 1 → jlvl = 0#32 ∧ wi = 1#32) ∧
      (2 ≤ (i + 1#32).toNat → 1 ≤ wi.toNat ∧ wi.toNat < (i + 1#32).toNat ∧ 0 < jlvl.toNat ∧
        stF.lvlArr[(stF.kl[wi.toNat]?.getD 0#32).toNat / 2]?.getD 0#32 = jlvl) ∧
      (∀ k, 1 ≤ k → k < (i + 1#32).toNat →
        (stF.lvlArr[(stF.kl[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ jlvl.toNat)) := by
  refine ⟨fun hgt => ⟨by rw [hi1_add]; omega, by rw [hi1_add]; omega, hil_lt,
      fun h => by rw [hi1_add] at h; omega,
      fun _ => ⟨hi1, by rw [hi1_add]; omega, hil_pos, hil_eq.symm⟩,
      fun k hk1 hk_lt => by
        rw [hi1_add] at hk_lt
        by_cases hki : k = i.toNat
        · subst hki; rw [← hil_eq]; exact le_refl _
        · have := hall_le k hk1 (by omega); omega⟩,
    fun hle => by
      have hi_ge2_cur : 2 ≤ i.toNat := by
        by_cases h1 : i.toNat = 1
        · have hj0 := (hi_eq1 h1).1; rw [hj0] at hle; simp at hle; omega
        · omega
      obtain ⟨hw1, hw_lt, hj_pos, hw_lvl⟩ := hi_ge2 hi_ge2_cur
      refine ⟨by rw [hi1_add]; omega, by rw [hi1_add]; omega, hj_lt,
        fun h => by rw [hi1_add] at h; omega,
        fun _ => ⟨hw1, by rw [hi1_add]; omega, hj_pos, hw_lvl⟩,
        fun k hk1 hk_lt => by
          rw [hi1_add] at hk_lt
          by_cases hki : k = i.toNat
          · subst hki; rw [← hil_eq]; exact hle
          · exact hall_le k hk1 (by omega)⟩⟩

private theorem k6a_arena_copy_step {st5 : K6State} {i7 : BitVec 32} {ar7 : List (BitVec 32)}
    {L : K6Layout} (har7_len : ar7.length = L.acap) (hkl_len : st5.kl.length = L.maxV)
    (hi7_lt : i7.toNat < st5.nkl.toNat) (hnkl_le : st5.nkl.toNat ≤ L.maxV)
    (hfit : st5.alen.toNat + st5.nkl.toNat ≤ L.acap)
    (hi7_1 : (i7 + 1#32).toNat = i7.toNat + 1)
    (har7_old : ∀ k < st5.alen.toNat, ar7[k]? = st5.arena[k]?)
    (har7_lits : ∀ k < i7.toNat, ar7[st5.alen.toNat + k]? = st5.kl[k]?) :
    let ar7' := ar7.set (st5.alen.toNat + i7.toNat) (st5.kl[i7.toNat]?.getD 0#32)
    (i7 + 1#32).toNat ≤ st5.nkl.toNat ∧ ar7'.length = L.acap ∧
    (∀ k < st5.alen.toNat, ar7'[k]? = st5.arena[k]?) ∧
    (∀ k < (i7 + 1#32).toNat, ar7'[st5.alen.toNat + k]? = st5.kl[k]?) := by
  intro ar7'
  refine ⟨by rw [hi7_1]; omega, by simp [ar7', har7_len],
    fun k hk => by rw [List.getElem?_set_ne (by omega)]; exact har7_old k hk,
    fun k hk => by
      rw [hi7_1] at hk; by_cases hki : k = i7.toNat
      · subst hki; rw [List.getElem?_set_self (by omega),
          List.getElem?_eq_getElem (by rw [hkl_len]; omega), Option.getD_some]
      · rw [List.getElem?_set_ne (by omega)]; exact har7_lits k (by omega)⟩

private theorem k6a_ana_uip_exit_post {L : K6Layout} {P : (Nat → Bool) → Prop} {ks st st1 : K6State}
    {p : BitVec 32} {idx' : Nat}
    (hinv1 : K6AnaInv L P { st with openCnt := st.openCnt - 1#32 } idx')
    (hpresL : K6AnaPreserved ks st)
    (hpres1 : K6AnaPreserved st { st with openCnt := st.openCnt - 1#32 })
    (htlL : K6TailEq L ks st) (htl1' : K6TailEq L st { st with openCnt := st.openCnt - 1#32 })
    (hst1_eq : st1 = { st with openCnt := st.openCnt - 1#32 })
    (hop0 : st1.openCnt = 0#32) (hp_lt : p.toNat < 2 * st.nv.toNat)
    (hlvl_hit : st.lvlArr[p.toNat / 2]?.getD 0#32 = st.lvl)
    (hent_hit : SemEntails P ((p.toNat ^^^ 1) ::
      k6ResolventLits { st with openCnt := st.openCnt - 1#32 } idx')) :
    K6AnaBrkPost L P ks (p ^^^ 1#32) st1 := by
  subst hst1_eq
  have hkl_eq := k6a_uip_exit hinv1 hop0
  rw [hkl_eq] at hent_hit
  have huip_eq : (p ^^^ 1#32).toNat = p.toNat ^^^ 1 := by simp
  have huip_lt : (p ^^^ 1#32).toNat < 2 * st.nv.toNat := by
    rw [huip_eq]; rcases k6_nat_xor1_cases p.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  have huip_lvl : st.lvlArr[(p ^^^ 1#32).toNat / 2]?.getD 0#32 = st.lvl := by
    rw [huip_eq, k6a_xor1_div2]; exact hlvl_hit
  exact ⟨hinv1.shapes, k6AnaPreserved_trans hpresL hpres1, k6TailEq_trans htlL htl1',
    hinv1.nkl_pos, hinv1.nkl_le, hinv1.nana_le, hinv1.ana_lt, hinv1.flags_seen,
    fun _ => ⟨huip_lt, huip_lvl, fun i hi1 hi2 =>
      let hk := hinv1.kl_nonTop i hi1 hi2; ⟨hk.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2⟩,
      by rw [huip_eq]; exact hent_hit⟩⟩

private theorem k6a_lvl_loop_prep {L : K6Layout} {P : (Nat → Bool) → Prop} {stF : K6State}
    {ks_lvl jlvl wi i : BitVec 32} (hinvF : K6Inv L P stF) (hstF_lvl : stF.lvl = ks_lvl)
    (hi1 : 1 ≤ i.toNat) (hi_lt : i.toNat < stF.nkl.toNat) (hj_lt : jlvl.toNat < ks_lvl.toNat)
    (hi_eq1 : i.toNat = 1 → jlvl = 0#32 ∧ wi = 1#32)
    (hi_ge2 : 2 ≤ i.toNat → 1 ≤ wi.toNat ∧ wi.toNat < i.toNat ∧ 0 < jlvl.toNat ∧
      stF.lvlArr[(stF.kl[wi.toNat]?.getD 0#32).toNat / 2]?.getD 0#32 = jlvl)
    (hall_le : ∀ k, 1 ≤ k → k < i.toNat →
      (stF.lvlArr[(stF.kl[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ jlvl.toNat)
    (hkl_ntF : ∀ k, 1 ≤ k → k < stF.nkl.toNat →
      let l := (stF.kl[k]?.getD 0#32).toNat
      l < 2 * stF.nv.toNat ∧ 0 < (stF.lvlArr[l / 2]?.getD 0#32).toNat ∧
      (stF.lvlArr[l / 2]?.getD 0#32).toNat < stF.lvl.toNat ∧ stF.vals[l]? = some 2#32)
    {uip : BitVec 32} :
    let stKl0 := stF.putArr .kl 0 uip
    let il := stF.lvlArr[(stF.kl[i.toNat]?.getD 0#32).toNat / 2]?.getD 0#32
    i.toNat < szV L ∧ (stKl0.kl[i.toNat]?.getD 0#32 >>> 1).toNat =
      (stF.kl[i.toNat]?.getD 0#32).toNat / 2 ∧
    (stKl0.kl[i.toNat]?.getD 0#32 >>> 1).toNat < szV L ∧ (i + 1#32).toNat = i.toNat + 1 ∧
    stKl0.lvlArr = stF.lvlArr ∧
    ((jlvl.toNat < il.toNat →
      1 ≤ (i + 1#32).toNat ∧ (i + 1#32).toNat ≤ stF.nkl.toNat ∧ il.toNat < ks_lvl.toNat ∧
      ((i + 1#32).toNat = 1 → il = 0#32 ∧ i = 1#32) ∧
      (2 ≤ (i + 1#32).toNat → 1 ≤ i.toNat ∧ i.toNat < (i + 1#32).toNat ∧ 0 < il.toNat ∧
        stF.lvlArr[(stF.kl[i.toNat]?.getD 0#32).toNat / 2]?.getD 0#32 = il) ∧
      (∀ k, 1 ≤ k → k < (i + 1#32).toNat →
        (stF.lvlArr[(stF.kl[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ il.toNat)) ∧
     (il.toNat ≤ jlvl.toNat →
      1 ≤ (i + 1#32).toNat ∧ (i + 1#32).toNat ≤ stF.nkl.toNat ∧ jlvl.toNat < ks_lvl.toNat ∧
      ((i + 1#32).toNat = 1 → jlvl = 0#32 ∧ wi = 1#32) ∧
      (2 ≤ (i + 1#32).toNat → 1 ≤ wi.toNat ∧ wi.toNat < (i + 1#32).toNat ∧ 0 < jlvl.toNat ∧
        stF.lvlArr[(stF.kl[wi.toNat]?.getD 0#32).toNat / 2]?.getD 0#32 = jlvl) ∧
      (∀ k, 1 ≤ k → k < (i + 1#32).toNat →
        (stF.lvlArr[(stF.kl[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ jlvl.toNat))) := by
  intro stKl0 il
  have hm_v := L.hmaxV; have hnv := hinvF.clauses.nv_le; have hnkl := hinvF.clauses.nkl_le
  have hnt := hkl_ntF i.toNat hi1 hi_lt; dsimp only at hnt
  have hkl0_i : stKl0.kl[i.toNat]? = stF.kl[i.toNat]? := by
    dsimp only [stKl0]; k6_field; exact List.getElem?_set_ne (by omega)
  have hlv_div : (stKl0.kl[i.toNat]?.getD 0#32 >>> 1).toNat =
      (stF.kl[i.toNat]?.getD 0#32).toNat / 2 := by rw [hkl0_i]; exact (k6_bv32_div2_lt hnt.1).1
  have hi1_add : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
  have hstep := k6a_jlvl_step_inv (ks_lvl := ks_lvl) hi1 hi_lt hj_lt hi_eq1 hi_ge2 hall_le
    hi1_add rfl hnt.2.1 (by rw [← hstF_lvl]; exact hnt.2.2.1)
  exact ⟨by unfold szV; omega, hlv_div, by unfold szV; rw [hlv_div]; omega, hi1_add,
    by dsimp only [stKl0]; k6_field, hstep⟩

private theorem k6a_ret5_post {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks st5 stSw ksBt : K6State} {kPtr : BitVec 64} {R : Mem 64 → Prop} {Q : Post [Ty.bool]}
    (hret_false : ∀ (ks' : K6State) (m' : Mem 64), K6Inv L P ks' → K6TrailSynced ks' →
      ks'.nv = ks.nv → K6TailEq L ks ks' → ks'.nassump = ks.nassump →
      ks'.assump = ks.assump → ks'.incons = ks.incons → ks'.status = ks.status →
      ks'.neq = ks.neq → (K6Mem L kPtr ks' ⋆ R) m' → Q (false, ()) m')
    (hinv5 : K6Inv L P st5) (hsync5 : K6TrailSynced st5) (htl_st5 : K6TailEq L ks st5)
    (hbtPres : K6BtPreserved stSw ksBt) (hpresSw : K6AnaPreserved ks stSw)
    (hbt_nv : ksBt.nv = ks.nv)
    (hst5_eq : ∃ qf ql qs qst qp qn qsa, st5 =
      { ksBt with qfirst := qf, qlast := ql, qsearch := qs, qstamp := qst,
                  qprev := qp, qnext := qn, qstampArr := qsa })
    {m' : Mem 64} (hm' : (K6Mem L kPtr st5 ⋆ R) m') : Q (false, ()) m' := by
  obtain ⟨qf, ql, qs, qst, qp, qn, qsa, hst5⟩ := hst5_eq
  exact hret_false st5 m' hinv5 hsync5 (by rw [hst5]; exact hbt_nv) htl_st5
    (by rw [hst5]; exact hbtPres.nassump.trans hpresSw.nassump)
    (by rw [hst5]; exact hbtPres.assump.trans hpresSw.assump)
    (by rw [hst5]; exact hbtPres.incons.trans hpresSw.incons)
    (by rw [hst5]; exact hbtPres.status.trans hpresSw.status)
    (by rw [hst5]; exact hbtPres.neq.trans hpresSw.neq) hm'

private theorem k6a_init_clause_res {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    {confl_cid : BitVec 32} (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks)
    (hconfl_lt : confl_cid.toNat < ks.nc.toNat)
    (hconfl_fals : ∀ l ∈ k6ClauseLits ks confl_cid.toNat, ks.vals[l]? = some 2#32) :
    let ks0 : K6State := { ks with nkl := 1#32, nana := 0#32, openCnt := 0#32 }
    ∀ l ∈ k6ClauseLits ks0 confl_cid.toNat, l / 2 ≠ (0xFFFFFFFF#32 : BitVec 32).toNat →
      ks0.vals[l]? = some 2#32 ∧ (ks0.lvlArr[l / 2]?.getD 0#32 = ks0.lvl →
        ∃ j < ks.trl_end.toNat, (ks0.trl[j]?.getD 0#32).toNat = l ^^^ 1) := by
  intro ks0 l hl _; have hwf := hinv.clauses.cl_wf confl_cid.toNat hconfl_lt
  exact ⟨hconfl_fals l hl, fun _ =>
    k6_falsified_to_trail hinv.assign hsync (hwf.2.2.1 l hl) (hconfl_fals l hl)⟩

private theorem k6a_kl_take1_eq {st5 ksBt stSw : K6State} {nkl uip : BitVec 32}
    (hst5 : st5.kl = ksBt.kl ∧ st5.nkl = ksBt.nkl) (hkl : ksBt.kl = stSw.kl)
    (hnkl : ksBt.nkl = nkl) (hnkl1 : nkl = 1#32) (hsw0 : stSw.kl[0]? = some uip) :
    (st5.kl.take st5.nkl.toNat).map BitVec.toNat = [uip.toNat] := by
  rw [hst5.1, hst5.2, hkl, hnkl, hnkl1]
  change (stSw.kl.take 1).map BitVec.toNat = [uip.toNat]
  rw [List.take_add_one, List.take_zero, List.nil_append, hsw0, Option.toList_some]; rfl

/-! ## 2. Parametric `Func.wp` Theorem for `full_k6_analyze` (`11/14`) -/

@[scoped c0_load] private theorem load_k6_lvl_8 {L : K6Layout} {kPtr : BitVec 64}
    {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64} (hm : (K6MemA L kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + 8#64) = some ks.lvl := by
  rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 2 * 4 from rfl]; exact load_k6_lvl hm

/-- `11/14`: Parametric `Func.wp` proof for `full_k6_analyze`. -/
theorem full_k6_analyze_wp (Γ : Env)
    (hAnaCl : Γ.Has "full_k6_ana_clause" step13K6AnaClauseSpec)
    (hBt : Γ.Has "full_k6_backtrack" step13K6BacktrackSpec)
    (hMtf : Γ.Has "full_k6_mtf" k6MtfSpec)
    (hWatch : Γ.Has "full_k6_watch" k6WatchSpec)
    (hAssign : Γ.Has "full_k6_assign" k6AssignSpec) :
    ∀ args m Q X, step13K6AnalyzeSpec args m Q X →
      Func.wp Γ full_k6_analyze_body args m Q X := by
  rintro ⟨kPtr, confl_cid, ⟨⟩⟩ m Q X ⟨L, P, ks, R, hinv, hsync, hlvl_pos, hlvl_wit,
    hconfl_lt, hconfl_fals, hm, hQ⟩
  have hm_v := L.hmaxV; have hac := L.hacap; have hsh := hinv.shapes; have hnv := hinv.clauses.nv_le
  have hmv : ks.max_v = L.mv32 := hinv.clauses.max_v_eq
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hsh.trl_len]; have := hinv.assign.trl_end_le; omega
  have hvdec : ∃ v < ks.nv.toNat, ks.lvlArr[v]?.getD 0#32 = ks.lvl := by
    obtain ⟨i0, hi0, hl0⟩ := hlvl_wit
    have hlt := hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hi0 htrl_len)
    exact ⟨(ks.trl[i0]?.getD 0#32).toNat / 2, by omega, hl0⟩
  have hret_false : ∀ (ks' : K6State) (m' : Mem 64),
      K6Inv L P ks' → K6TrailSynced ks' → ks'.nv = ks.nv → K6TailEq L ks ks' →
      ks'.nassump = ks.nassump → ks'.assump = ks.assump → ks'.incons = ks.incons →
      ks'.status = ks.status → ks'.neq = ks.neq → (K6Mem L kPtr ks' ⋆ R) m' →
      Q (false, ()) m' :=
    fun ks' m' hi hsy h1 htl h2 h3 h4 h5 h6 hm' =>
      hQ false ks' m' hi hsy h1 htl h2 h3 h4 h5 h6 (fun h => by cases h) hm'
  have hmA := k6Mem_to_amem hsh hm; clear hm; c0_hsteps_nogrp; rw [hmv]; c0_hsteps_nogrp
  let ks0 : K6State := { ks with nkl := 1#32, nana := 0#32, openCnt := 0#32 }
  obtain ⟨hinv0, hpres0, htl0⟩ := k6a_init_anaInv hinv hsync hlvl_pos hvdec
  have hm0 : (K6Mem L kPtr ks0 ⋆ R) m := by
    obtain ⟨_, hm0'⟩ := k6MemA_to_mem hm
    exact Eq.mp (congrArg (fun x => (K6Mem L kPtr x ⋆ R) _) (by k6_ext)) hm0'
  c0_call hAnaCl
  refine ⟨L, P, ks0, ks.trl_end.toNat, R, hinv0, hconfl_lt, hvdec,
    k6a_init_clause_res hinv hsync hconfl_lt hconfl_fals,
    fun h => absurd rfl h, hm0, fun ks1 m1 hinv1 hpres1 htl1 hent1 _ hm1 => ?_⟩
  · have hpres_k1 := k6AnaPreserved_trans hpres0 hpres1
    have htl_k1 := k6TailEq_trans htl0 htl1
    have hm1A := k6Mem_to_amem hinv1.shapes hm1; clear hm1 hm hm0
    c0_hsteps_nogrp
    refine wp_while_break_state
      (brkTs := [i32, i32]) (lpTs := [i32]) (β := BitVec 32 × BitVec 32 × K6State)
      (fun b => (b.1, b.2.1, ()))
      (fun b mb => K6AnaBrkPost L P ks b.2.1 b.2.2 ∧ (K6MemA L kPtr b.2.2 ⋆ R) mb)
      (α := BitVec 32 × K6State) (fun p => (p.1, ())) (fun p => p.1.toNat)
      (fun p ml => K6AnaInv L P p.2 p.1.toNat ∧ K6AnaPreserved ks p.2 ∧
        K6TailEq L ks p.2 ∧ SemEntails P (k6ResolventLits p.2 p.1.toNat) ∧
        (K6MemA L kPtr p.2 ⋆ R) ml) ?_ ?_ ?_
    · rintro B ⟨_, uip, stB⟩ mB ⟨hBrk, hmB⟩; dsimp only at hBrk hmB ⊢
      have hnvB : stB.nv = ks.nv := hBrk.pres.nv
      have hna_mv : stB.nana.toNat ≤ L.maxV := by have := hBrk.nana_le; rw [hnvB] at this; omega
      have hnk_mv : stB.nkl.toNat ≤ L.maxV := by have := hBrk.nkl_le; rw [hnvB] at this; omega
      c0_hsteps_nogrp
      refine wp_while_state1 (fun p : BitVec 32 × List (BitVec 32) => p.1)
        (fun p => stB.nana.toNat - p.1.toNat)
        (fun p mf => p.1.toNat ≤ stB.nana.toNat ∧ p.2.length = L.maxV ∧
          (∀ v < stB.nv.toNat, (∃ j < p.1.toNat, (stB.ana[j]?.getD 0#32).toNat = v) →
            (p.2[v]?.getD 0#32 &&& 2#32) = 0#32) ∧
          (∀ v < stB.nv.toNat, (stB.flags[v]?.getD 0#32 &&& 2#32) = 0#32 →
            (p.2[v]?.getD 0#32 &&& 2#32) = 0#32) ∧
          (∀ v, stB.nv.toNat ≤ v → v < L.maxV → p.2[v]? = stB.flags[v]?) ∧
          (K6MemA L kPtr { stB with flags := p.2 } ⋆ R) mf)
        (fun Lf hLf => hLf (0#32, stB.flags) mB ⟨Nat.zero_le _, hBrk.sh.flags_len,
          fun _ _ ⟨_, hj, _⟩ => by simp at hj, fun _ _ h => h, fun _ _ _ => rfl,
          by simpa using hmB⟩) ?_
      · rintro Lf ⟨ai, fls⟩ mf ⟨hai_le, hfls_len, hcl_done, hcl_orig, htl_fl, hmf⟩ ihf
        dsimp only at hai_le hfls_len hcl_done hcl_orig htl_fl hmf ⊢
        obtain ⟨stF, hstF⟩ : ∃ x : K6State, x = { stB with flags := fls } := ⟨_, rfl⟩
        rw [← hstF] at hmf
        c0_hsplit
        · have hai_lt : ai.toNat < stB.nana.toNat := by rw [hstF] at hc; exact hc
          have hai_mv : ai.toNat < szV L := by unfold szV; omega
          have hav_lt : (stB.ana[ai.toNat]?.getD 0#32).toNat < stB.nv.toNat :=
            hBrk.ana_lt ai.toNat hai_lt
          have hav_mv : (stF.ana[ai.toNat]?.getD 0#32).toNat < szV L := by
            unfold szV; rw [hstF]; change (stB.ana[ai.toNat]?.getD 0#32).toNat < L.maxV
            rw [hnvB] at hav_lt; omega
          have hai1 : (ai + 1#32).toNat = ai.toNat + 1 := by bv_omega
          c0_hsteps!
          have hcf := k6a_clear_flags_step_inv hfls_len (hnvB ▸ hnv) hai_lt hav_lt hai1
            hcl_done hcl_orig htl_fl
          refine ihf (ai + 1#32, fls.set (stB.ana[ai.toNat]?.getD 0#32).toNat
              (fls[(stB.ana[ai.toNat]?.getD 0#32).toNat]?.getD 0#32 &&& ~~~2#32)) _
            (by dsimp only; rw [hai1]; omega) ⟨hcf.1, hcf.2.1, hcf.2.2.1, hcf.2.2.2.1,
              hcf.2.2.2.2, Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _)
                (by rw [hstF]; k6_ext)) hm⟩
        · have hai_eq : ai.toNat = stB.nana.toNat := by
            have h1 : ¬ ai.toNat < stF.nana.toNat := hc
            rw [hstF] at h1; dsimp only at h1; omega
          obtain ⟨hinvF, hsyncF, hpresF, htlF⟩ := k6a_clear_flags_exit hinv hsync hBrk hfls_len
            hna_mv hnk_mv (by rw [← hai_eq]; exact hcl_done) hcl_orig htl_fl
          rw [← hstF] at hinvF hsyncF hpresF htlF
          c0_hsplit
          · c0_hsteps!; obtain ⟨_, hmF⟩ := k6MemA_to_mem hmf
            exact hret_false stF mf hinvF hsyncF hpresF.nv htlF hpresF.nassump hpresF.assump
              hpresF.incons hpresF.status hpresF.neq hmF
          · have huip_ne : uip ≠ 0xFFFFFFFF#32 := ‹_›
            obtain ⟨huip_lt, huip_lvl, hkl_ntB, hent_uip⟩ := hBrk.uip_ok huip_ne
            have huip_lt_k : uip.toNat < 2 * ks.nv.toNat := by rwa [hnvB] at huip_lt
            have huip_lvl_k : ks.lvlArr[uip.toNat / 2]?.getD 0#32 = ks.lvl := by
              rwa [hBrk.pres.lvlArr, hBrk.pres.lvl] at huip_lvl
            have hkl_ntF : ∀ i, 1 ≤ i → i < stF.nkl.toNat →
                let l := (stF.kl[i]?.getD 0#32).toNat
                l < 2 * stF.nv.toNat ∧ 0 < (stF.lvlArr[l / 2]?.getD 0#32).toNat ∧
                (stF.lvlArr[l / 2]?.getD 0#32).toNat < stF.lvl.toNat ∧
                stF.vals[l]? = some 2#32 := by rw [hstF]; exact hkl_ntB
            let stKl0 := stF.putArr .kl 0 uip
            c0_hsteps_nogrp
            refine wp_while_state_pure (ts := [i32, i32, i32])
              (α := BitVec 32 × BitVec 32 × BitVec 32) (fun t => (t.1, t.2.1, t.2.2, ()))
              (fun t => stF.nkl.toNat - t.2.2.toNat)
              (fun t => 1 ≤ t.2.2.toNat ∧ t.2.2.toNat ≤ stF.nkl.toNat ∧
                t.1.toNat < ks.lvl.toNat ∧
                (t.2.2.toNat = 1 → t.1 = 0#32 ∧ t.2.1 = 1#32) ∧
                (2 ≤ t.2.2.toNat → 1 ≤ t.2.1.toNat ∧ t.2.1.toNat < t.2.2.toNat ∧
                  0 < t.1.toNat ∧
                  stF.lvlArr[(stF.kl[t.2.1.toNat]?.getD 0#32).toNat / 2]?.getD 0#32 = t.1) ∧
                (∀ k, 1 ≤ k → k < t.2.2.toNat →
                  (stF.lvlArr[(stF.kl[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ t.1.toNat))
              ?_ ?_
            · intro L3 hL3; exact wp_jump_state
                (proj := fun t : BitVec 32 × BitVec 32 × BitVec 32 => (t.1, t.2.1, t.2.2, ()))
                (0#32, 1#32, 1#32) rfl (hL3 (0#32, 1#32, 1#32) ⟨by decide,
                  by rw [hstF]; exact hBrk.nkl_pos, hlvl_pos, fun _ => ⟨rfl, rfl⟩,
                  fun h => by simp at h, fun k h1 h2 => by simp at h2; omega⟩)
            · rintro L3 ⟨jlvl, wi, i⟩ ⟨hi1, hi_le, hj_lt, hi_eq1, hi_ge2, hall_le⟩ ih3
              dsimp only at hi1 hi_le hj_lt hi_eq1 hi_ge2 hall_le ⊢
              have hkl0_nkl : stKl0.nkl = stF.nkl := by dsimp only [stKl0]; k6_field
              c0_hsplit
              · have hi_lt : i.toNat < stF.nkl.toNat := by rw [← hkl0_nkl]; exact hc
                obtain ⟨hi_mv, hlv_div, hlv_mv, hi1_add, hkl0_lv, hjl_step⟩ :=
                  k6a_lvl_loop_prep hinvF hpresF.lvl hi1 hi_lt hj_lt hi_eq1 hi_ge2 hall_le hkl_ntF
                let il := stF.lvlArr[(stF.kl[i.toNat]?.getD 0#32).toNat / 2]?.getD 0#32
                c0_hsteps!
                · have hgt : jlvl.toNat < il.toNat := by
                    dsimp only [il]; rw [← hlv_div, ← hkl0_lv]; exact hc
                  rw [hkl0_lv, hlv_div]
                  exact ih3 (il, i, i + 1#32) (by dsimp only; rw [hi1_add]; omega) (hjl_step.1 hgt)
                · have hle : il.toNat ≤ jlvl.toNat := by
                    have h1 : ¬ jlvl.toNat < (stKl0.lvlArr[(stKl0.kl[i.toNat]?.getD 0#32 >>>
                        1).toNat]?.getD 0#32).toNat := hc
                    rw [hkl0_lv, hlv_div] at h1; dsimp only [il]; omega
                  exact ih3 (jlvl, wi, i + 1#32) (by dsimp only; rw [hi1_add]; omega)
                    (hjl_step.2 hle)
              · have hi_eq : i.toNat = stF.nkl.toNat := by
                  have h1 : ¬ i.toNat < stKl0.nkl.toNat := hc; rw [hkl0_nkl] at h1; omega
                rw [hi_eq] at hi_eq1 hi_ge2 hall_le
                let stSw := if 2 ≤ stF.nkl.toNat ∧ wi ≠ 1#32 then
                  (stKl0.putArr .kl 1 (stKl0.kl[wi.toNat]?.getD 0#32)).putArr .kl wi.toNat
                    (stKl0.kl[1]?.getD 0#32)
                  else stKl0
                obtain ⟨hinvSw, hsyncSw, hpresSwF, htlSwF, hsw_nkl, hsw_nana, hsw_ana, hsw0,
                  hsw_mem, hsw_nt⟩ := k6a_swap_kl_preserves hinvF hsyncF
                    (by rw [hstF]; exact hBrk.nkl_pos) (by rw [hstF]; exact hBrk.nkl_le)
                    (fun h2 => ⟨(hi_ge2 h2).1, (hi_ge2 h2).2.1⟩)
                    (fun k hk1 hk_lt => let h := hkl_ntF k hk1 hk_lt
                      ⟨h.1, h.2.1, hall_le k hk1 hk_lt, h.2.2.2⟩)
                have hpresSw := k6AnaPreserved_trans hpresF hpresSwF
                have htlSw := k6TailEq_trans htlF htlSwF
                c0_hsteps_nogrp
                refine wp_join0 (fun m4 => (K6MemA L kPtr stSw ⋆ R) m4) ?_ ?_
                · intro J4 m4 hm4; obtain ⟨_, hm4_bt⟩ := k6MemA_to_mem hm4
                  c0_hsteps_nogrp; c0_call hBt
                  refine ⟨L, P, stSw, R, hinvSw, Or.inr hsyncSw, hm4_bt,
                    fun ksBt mBt hinvBt hsyncBt hlvlBt hte_le hbtPres htlBt hbtKept hB1 hmBt => ?_⟩
                  obtain ⟨huip_none, huip_v0, hte_lt_nv, hkl_bt_trl, hdec_ks, hA2_bt⟩ :=
                    k6a_after_bt_facts hinvSw hsyncSw hpresSw huip_lt_k huip_lvl_k hj_lt
                      hinvBt hlvlBt hte_le hbtPres hbtKept hB1
                  have hbt_nv := hbtPres.nv.trans hpresSw.nv
                  have htl_bt := k6TailEq_trans htlSw htlBt
                  have hbt_nkl : ksBt.nkl = stF.nkl := hbtPres.nkl.trans hsw_nkl
                  have hmBtA := k6Mem_to_amem hinvBt.shapes hmBt; clear hmBt hm4 hm4_bt
                  c0_hsteps_nogrp
                  refine wp_while_state1 (fun p : BitVec 32 × K6State => p.1)
                    (fun p => ksBt.nana.toNat - p.1.toNat)
                    (fun p m5 => p.1.toNat ≤ ksBt.nana.toNat ∧
                      (∃ qf ql qs qst qp qn qsa, p.2 =
                        { ksBt with qfirst := qf, qlast := ql, qsearch := qs, qstamp := qst,
                                    qprev := qp, qnext := qn, qstampArr := qsa }) ∧
                      p.2.ShapesOk L ∧ (K6MemA L kPtr p.2 ⋆ R) m5)
                    (fun L5 hL5 => wp_jump_state (proj := fun p : BitVec 32 × K6State => (p.1, ()))
                      (0#32, ksBt) rfl (hL5 (0#32, ksBt) mBt ⟨Nat.zero_le _, ⟨ksBt.qfirst,
                        ksBt.qlast, ksBt.qsearch, ksBt.qstamp, ksBt.qprev, ksBt.qnext,
                        ksBt.qstampArr, rfl⟩, hinvBt.shapes, hmBtA⟩)) ?_
                  · rintro L5 ⟨ai5, st5⟩ m5 ⟨hai5_le, hq5, hsh5, hm5⟩ ih5
                    dsimp only at hai5_le hq5 hsh5 hm5 ⊢
                    obtain ⟨qf, ql, qs, qst, qp, qn, qsa, hst5_eq⟩ := hq5
                    c0_hsplit
                    · have hai5_lt : ai5.toNat < ksBt.nana.toNat := by rw [hst5_eq] at hc; exact hc
                      have hai5_mv : ai5.toNat < szV L := by
                        unfold szV; have := hinvBt.clauses.nana_le; omega
                      have hai5_1 : (ai5 + 1#32).toNat = ai5.toNat + 1 := by bv_omega
                      c0_hsteps_nogrp; obtain ⟨_, hm5_m⟩ := k6MemA_to_mem hm5
                      c0_call hMtf
                      refine ⟨L, st5, R, hsh5, by rw [hst5_eq]; exact hinvBt.clauses.max_v_eq,
                        by rw [hst5_eq]; exact hinvBt.clauses.nv_le, hm5_m,
                        fun qf' ql' qs' qst' qp' qn' qsa' m5' hsh5' hm5' => ?_⟩
                      c0_hsteps!
                      let st5' : K6State :=
                        { st5 with qfirst := qf', qlast := ql', qsearch := qs', qstamp := qst',
                                   qprev := qp', qnext := qn', qstampArr := qsa' }
                      refine ih5 (ai5 + 1#32, st5') m5' (by dsimp only; rw [hai5_1]; omega)
                        ⟨by dsimp only; rw [hai5_1]; omega,
                         ⟨qf', ql', qs', qst', qp', qn', qsa', by dsimp only [st5']; rw [hst5_eq]⟩,
                         hsh5', k6Mem_to_amem hsh5' hm5'⟩
                    · obtain ⟨hinv5, hsync5, htl_st5, hent_kl5, hca5, hmc5⟩ :=
                        k6a_ana_mtf_exit_inv hinvBt hsyncBt htl_bt hbtPres hsw_nkl
                          (fun x hx => by
                            dsimp only [stSw, stKl0]; rw [hsw_nkl]; exact hsw_mem x hx)
                          (by rw [hstF]; exact hent_uip) hsh5
                          ⟨qf, ql, qs, qst, qp, qn, qsa, hst5_eq⟩
                      c0_hsplit
                      · have hnkl1 : stF.nkl = 1#32 := by rw [← hkl0_nkl]; exact hc
                        rw [k6a_kl_take1_eq (by rw [hst5_eq]; exact ⟨rfl, rfl⟩)
                          hbtPres.kl hbt_nkl hnkl1 hsw0] at hent_kl5
                        obtain ⟨_, hm5_a⟩ := k6MemA_to_mem hm5; c0_hsteps_nogrp; c0_call hAssign
                        refine ⟨L, st5, R, hsh5, hinv5.clauses.max_v_eq,
                          Nat.lt_of_lt_of_le huip_lt_k (by omega), by
                            rw [hst5_eq]
                            exact Nat.lt_of_lt_of_le hte_lt_nv (by rw [hbt_nv]; omega),
                          hm5_a, fun mFin hmFin => ?_⟩
                        c0_hsteps!
                        exact k6a_nkl1_finish hQ hinv5 hsync5 ⟨qf, ql, qs, qst, qp, qn, qsa,
                          hst5_eq⟩ hbtPres hpresSw htl_st5 hlvlBt
                          (hi_eq1 (by rw [hnkl1]; decide)).1 hj_lt huip_lt_k huip_none huip_v0
                          hte_lt_nv hent_kl5 hdec_ks hA2_bt hmFin
                      · have hnkl_ne1 : stF.nkl ≠ 1#32 := by rw [← hkl0_nkl]; exact hc
                        have hnkl_ge2 : 2 ≤ stF.nkl.toNat := by
                          have h1 : 1 ≤ stF.nkl.toNat := by rw [hstF]; exact hBrk.nkl_pos
                          have hne : stF.nkl.toNat ≠ 1 := fun h =>
                            hnkl_ne1 (BitVec.eq_of_toNat_eq h)
                          omega
                        have hret5 : ∀ m', (K6Mem L kPtr st5 ⋆ R) m' → Q (false, ()) m' :=
                          fun _ hm' => k6a_ret5_post hret_false hinv5 hsync5 htl_st5 hbtPres hpresSw
                            hbt_nv ⟨qf, ql, qs, qst, qp, qn, qsa, hst5_eq⟩ hm'
                        try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                        c0_hsplit
                        · c0_hsteps!; exact hret5 _ (k6MemA_to_mem hm5).2
                        · have hnc_lt : st5.nc.toNat < L.maxCl := by
                            have hnl : ¬ st5.max_cl.toNat ≤ st5.nc.toNat := hc
                            rw [hmc5] at hnl; omega
                          c0_hsplit
                          · c0_hsteps!; exact hret5 _ (k6MemA_to_mem hm5).2
                          · have hfit : st5.alen.toNat + st5.nkl.toNat ≤ L.acap := by
                              have hnk5 : st5.nkl = stF.nkl := by rw [hst5_eq]; exact hbt_nkl
                              have h1 : ¬ st5.acap.toNat < (st5.alen + stKl0.nkl).toNat := hc
                              rw [hca5, hkl0_nkl, ← hnk5] at h1
                              have := hinv5.clauses.alen_le; have := hinv5.clauses.nkl_le
                              unfold dimacsBound at hac; bv_omega
                            c0_hsteps_nogrp
                            refine wp_while_state1 (fun p : BitVec 32 × List (BitVec 32) => p.1)
                              (fun p => st5.nkl.toNat - p.1.toNat)
                              (fun p m7 => p.1.toNat ≤ st5.nkl.toNat ∧ p.2.length = L.acap ∧
                                (∀ k < st5.alen.toNat, p.2[k]? = st5.arena[k]?) ∧
                                (∀ k < p.1.toNat, p.2[st5.alen.toNat + k]? = st5.kl[k]?) ∧
                                (K6MemA L kPtr { st5 with arena := p.2 } ⋆ R) m7)
                              (fun L7 hL7 => wp_jump_state
                                (proj := fun p : BitVec 32 × List (BitVec 32) => (p.1, ()))
                                (0#32, st5.arena) rfl
                                (hL7 (0#32, st5.arena) m5 ⟨Nat.zero_le _, hsh5.arena_len,
                                  fun _ _ => rfl, fun _ h => by simp at h, by simpa using hm5⟩))
                              ?_
                            · rintro L7 ⟨i7, ar7⟩ m7
                                ⟨hi7_le, har7_len, har7_old, har7_lits, hm7⟩ ih7
                              dsimp only at hi7_le har7_len har7_old har7_lits hm7 ⊢
                              obtain ⟨st7, hst7⟩ : ∃ x : K6State, x = { st5 with arena := ar7 } :=
                                ⟨_, rfl⟩
                              rw [← hst7] at hm7
                              have hnkl_st5 : st5.nkl = stKl0.nkl := by
                                rw [hst5_eq, hbt_nkl, hkl0_nkl]
                              c0_hsplit
                              · have hi7_lt : i7.toNat < st5.nkl.toNat := by rw [hnkl_st5]; exact hc
                                have hi7_mv : i7.toNat < szV L := by
                                  unfold szV; have := hinv5.clauses.nkl_le; omega
                                have hoff7_eq : (st5.alen + i7).toNat =
                                    st5.alen.toNat + i7.toNat := by
                                  unfold dimacsBound at hac; bv_omega
                                have hoff7_ar : (st5.alen + i7).toNat < szAr L := by
                                  unfold szAr; rw [hoff7_eq]; omega
                                have hi7_1 : (i7 + 1#32).toNat = i7.toNat + 1 := by bv_omega
                                c0_hsteps!
                                have hcp := k6a_arena_copy_step har7_len hsh5.kl_len hi7_lt
                                  hinv5.clauses.nkl_le hfit hi7_1 har7_old har7_lits
                                refine ih7 (i7 + 1#32, ar7.set (st5.alen.toNat + i7.toNat)
                                    (st5.kl[i7.toNat]?.getD 0#32)) _
                                  (by dsimp only; rw [hi7_1]; omega) ⟨hcp.1, hcp.2.1, hcp.2.2.1,
                                    hcp.2.2.2, Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _)
                                      (by rw [hst7]; k6_ext; try simp only [hoff7_eq])) hm⟩
                              · have hi7_eq : i7.toNat = st5.nkl.toNat := by
                                  have h1 : ¬ i7.toNat < stKl0.nkl.toNat := hc
                                  rw [← hnkl_st5] at h1; omega
                                rw [hi7_eq] at har7_lits
                                have hnc_len : st5.nc.toNat < szCl L := by unfold szCl; exact hnc_lt
                                have hnkl5_ge2 : 2 ≤ st5.nkl.toNat := by
                                  rw [hst5_eq, hbt_nkl]; exact hnkl_ge2
                                have hnkl5_mv : st5.nkl.toNat ≤ L.maxV := hinv5.clauses.nkl_le
                                c0_hsteps_nogrp
                                let stM := (((({ st5 with arena := ar7 } : K6State).putHdr .alen
                                    (st5.alen + st5.nkl)).putArr .clOff st5.nc.toNat
                                    st5.alen).putArr .clSz st5.nc.toNat st5.nkl).putHdr .nc
                                    (st5.nc + 1#32)
                                have hsw1 := hsw_nt 1 (le_refl _) (by rw [hsw_nkl]; exact hnkl_ge2)
                                obtain ⟨hshM, hmvM, hk0, hk1, hshW, hmvW, hW_eq, hteW⟩ :=
                                  k6a_nkl2_watch_prep hinv5 ⟨qf, ql, qs, qst, qp, qn, qsa, hst5_eq⟩
                                    hbtPres hpresSw hsw0 huip_lt_k hsw1.1 hte_lt_nv har7_len
                                obtain ⟨_, hmM⟩ := k6MemA_to_mem hm
                                rw [hst7, ← hnkl_st5] at hmM
                                have hstM_eq' : (((((st7.putHdr .alen (st5.alen +
                                    (stF.putArr K6ArrField.kl 0 uip).nkl)).putArr .clOff
                                    st5.nc.toNat st5.alen).putArr .clSz st5.nc.toNat
                                    (stF.putArr K6ArrField.kl 0 uip).nkl).putHdr .nc
                                    (st5.nc + 1))) = stM := by rw [hst7, ← hnkl_st5]; rfl
                                have hnv5 := hinv5.clauses.nv_le
                                have hstM_nv : stM.nv.toNat ≤ L.maxV := by
                                  dsimp only [stM]; k6_field; exact hnv5
                                c0_call hWatch
                                refine ⟨L, stM, R, hshM, hmvM, hnc_lt,
                                  by rw [hstM_eq']
                                     exact Nat.lt_of_lt_of_le hk0 (Nat.mul_le_mul_left 2 hstM_nv),
                                  by rw [hstM_eq']
                                     exact Nat.lt_of_lt_of_le hk1 (Nat.mul_le_mul_left 2 hstM_nv),
                                  hmM, fun mW hmW => ?_⟩
                                let stW := k6WatchStep stM st5.nc (st5.kl[0]?.getD 0#32)
                                  (st5.kl[1]?.getD 0#32)
                                have hstW_eq : k6WatchStep stM st5.nc (stM.kl[0]?.getD 0#32)
                                    (stM.kl[1]?.getD 0#32) = stW := by
                                  dsimp only [stW, stM]; k6_field
                                rw [hstM_eq', hstW_eq] at hmW
                                c0_hsteps_nogrp; c0_call hAssign
                                refine ⟨L, stW, R, hshW, hmvW, by omega,
                                  Nat.lt_of_lt_of_le hteW (by
                                    dsimp only [stW, k6WatchStep, k6WatchStep0, stM]; k6_field
                                    exact hinv5.clauses.nv_le),
                                  hmW, fun mFin hmFin => ?_⟩
                                c0_hsteps!
                                exact k6a_nkl2_assign_finish hQ hinv5 hsync5
                                  ⟨qf, ql, qs, qst, qp, qn, qsa, hst5_eq⟩ hbtPres hpresSw htl_st5
                                  hlvlBt hj_lt (hi_ge2 hnkl_ge2).2.2.1 huip_lt_k huip_none huip_v0
                                  hte_lt_nv hkl_bt_trl hdec_ks hA2_bt hsw0 hsw_nt hnc_lt hnkl5_ge2
                                  hfit har7_len har7_old har7_lits hent_kl5 hmFin
                · intro J4 hJ4; try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                  c0_hsplit
                  · have hnkl_ge2 : 2 ≤ stF.nkl.toNat := by rw [← hkl0_nkl]; bv_omega
                    c0_hsplit
                    · have hwi_ne1 : wi ≠ 1#32 := ‹_›
                      have hwi_mv : wi.toNat < szV L := by
                        have h1 := (hi_ge2 hnkl_ge2).2.1; unfold szV; rw [hstF] at h1
                        dsimp only at h1; omega
                      c0_hsteps!; exact hJ4 _ (Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _)
                        (by dsimp only [stSw]; rw [k6a_ite_t ⟨hnkl_ge2, hwi_ne1⟩])) hm)
                    · have hwi_eq1 : wi = 1#32 := by
                        first | exact ‹_› | exact Classical.not_not.mp ‹_›
                      c0_hsteps!; exact hJ4 _ (Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _)
                        (by dsimp only [stSw]; rw [k6a_ite_f (fun h => h.2 hwi_eq1)])) hm)
                  · have hnkl_lt2 : ¬ 2 ≤ stF.nkl.toNat := by rw [← hkl0_nkl]; bv_omega
                    c0_hsteps!; exact hJ4 _ (Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _)
                      (by dsimp only [stSw]; rw [k6a_ite_f (fun h => hnkl_lt2 h.1)])) hm)
    · rintro B L' ⟨idx_bv, st⟩ mL hB hL ⟨hinvL, hpresL, htlL, hentL, hmL⟩
      dsimp only at hinvL hpresL htlL hentL hmL
      c0_hsplit
      · have hop_pos : 0 < st.openCnt.toNat := by bv_omega
        c0_hsplit
        · c0_hsteps!
          exact hB (idx_bv, 0xFFFFFFFF#32, st) mL ⟨k6AnaBrkPost_of_uip_ff hinvL hpresL htlL, hmL⟩
        · have hidx_pos : 0 < idx_bv.toNat := by bv_omega
          have hidx_sub : (idx_bv - 1#32).toNat = idx_bv.toNat - 1 := by bv_omega
          let p := st.trl[idx_bv.toNat - 1]?.getD 0#32
          obtain ⟨hidx'_lt, hidx'_mv, hp_lt, hpv_eq, _, hidx_succ, hp_eq, hpv_mv'⟩ :=
            k6a_ana_loop_p_facts hinvL hidx_pos hidx_sub
          have hinvL' : K6AnaInv L P st ((idx_bv.toNat - 1) + 1) := by rwa [← hidx_succ]
          have hentL' : SemEntails P (k6ResolventLits st ((idx_bv.toNat - 1) + 1)) := by
            rwa [← hidx_succ]
          c0_hsteps_nogrp; try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
          try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
          c0_hsplit
          · have hfl_hit : (st.flags[p.toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32 := by
              rw [← hpv_eq, ← hp_eq]; exact ‹_›
            c0_hsplit
            · have hlvl_hit : st.lvlArr[p.toNat / 2]?.getD 0#32 = st.lvl := by
                rw [← hpv_eq, ← hp_eq, hpresL.lvl, ← hpres_k1.lvl]; exact ‹_›
              obtain ⟨_, hinv1, hpres1, htl1', hres_hit⟩ :=
                k6a_resolvent_step_hit hinvL' ⟨hfl_hit, hlvl_hit⟩
              have hent_hit : SemEntails P ((p.toNat ^^^ 1) ::
                  k6ResolventLits { st with openCnt := st.openCnt - 1#32 } (idx_bv.toNat - 1)) :=
                k6a_semEntails_subset hres_hit hentL'
              let st1 := st.putHdr .openCnt (st.openCnt - 1#32)
              have hst1_eq : st1 = { st with openCnt := st.openCnt - 1#32 } := by k6_ext
              c0_hsplit
              · have hop0 : st1.openCnt = 0#32 := by dsimp only [st1]; k6_field; exact ‹_›
                c0_hsteps!; rw [show st.trl[(idx_bv - 1).toNat]?.getD 0#32 = p from hp_eq]
                exact hB (idx_bv - 1#32, p ^^^ 1#32, st1) _
                  ⟨k6a_ana_uip_exit_post hinv1 hpresL hpres1 htlL htl1' hst1_eq hop0 hp_lt
                    hlvl_hit hent_hit, hm⟩
              · have hst1_pos : 0 < ({ st with openCnt := st.openCnt - 1#32 } :
                    K6State).openCnt.toNat := by
                  have hne : (st.putHdr .openCnt (st.openCnt - 1#32)).openCnt ≠ 0#32 := ‹_›
                  dsimp only [K6State.putHdr] at hne ⊢; bv_omega
                obtain ⟨_, _, _, hrsn_ne, hrsn_lt, hp_mem, hp_uniq, hoth⟩ :=
                  k6a_rsn_pre hinv1 hidx'_lt hst1_pos hlvl_hit
                c0_hsplit
                · exfalso; have heq : st.rsn[(st.trl[(idx_bv - 1#32).toNat]?.getD 0#32 >>>
                      1).toNat]?.getD 0#32 = 0xFFFFFFFF#32 := ‹_›
                  rw [hp_eq] at heq; exact hrsn_ne heq
                · obtain ⟨_, hm1_m⟩ := k6MemA_to_mem hm
                  change (K6Mem L kPtr st1 ⋆ R) _ at hm1_m; rw [hst1_eq] at hm1_m
                  have hp_eq' : st.trl[(idx_bv - 1).toNat]?.getD 0#32 = p := hp_eq
                  c0_call hAnaCl
                  refine ⟨L, P, { st with openCnt := st.openCnt - 1#32 }, idx_bv.toNat - 1, R,
                    hinv1, by dsimp only [Arg.val, K6State.putHdr]; rw [hp_eq']; exact hrsn_lt,
                    ⟨p.toNat / 2, Nat.div_lt_of_lt_mul (by exact hp_lt), hlvl_hit⟩,
                    fun l hl hne => ?_, fun _ => ?_, hm1_m,
                    fun ks2 m2 hinv2 hpres2 htl2 hent2 _ hm2 => ?_⟩
                  · dsimp only [Arg.val, K6State.putHdr] at hl hne; rw [hp_eq'] at hl hne
                    have h1 := hoth l hl (by rw [hpv_eq] at hne; exact hne)
                    exact ⟨h1.1, fun _ => h1.2⟩
                  · dsimp only [Arg.val, K6State.putHdr]; rw [hp_eq']
                    refine ⟨p.toNat, hp_mem, hpv_eq.symm, hp_uniq, by rw [hpv_eq]; exact hfl_hit,
                      by rw [hpv_eq]; exact hlvl_hit, hent_hit⟩
                  · c0_hsteps!
                    refine hL (idx_bv - 1#32, ks2) m2 (by dsimp only; rw [hidx_sub]; omega)
                      ⟨by dsimp only; rw [hidx_sub]; exact hinv2,
                       k6AnaPreserved_trans hpresL (k6AnaPreserved_trans hpres1 hpres2),
                       k6TailEq_trans (k6TailEq_trans htlL htl1') htl2,
                       by dsimp only; rw [hidx_sub]; exact hent2, k6Mem_to_amem hinv2.shapes hm2⟩
            · have hnlv : st.lvlArr[p.toNat / 2]?.getD 0#32 ≠ st.lvl := by
                rw [← hpv_eq, ← hp_eq, hpresL.lvl, ← hpres_k1.lvl]; exact ‹_›
              obtain ⟨hinvS, hresS⟩ := k6a_resolvent_step_skip hinvL' fun h => hnlv h.2
              c0_hsteps!
              refine hL (idx_bv - 1#32, st) mL (by dsimp only; rw [hidx_sub]; omega)
                ⟨by dsimp only; rw [hidx_sub]; exact hinvS, hpresL, htlL,
                 by dsimp only; rw [hidx_sub, ← hresS]; exact hentL', hmL⟩
          · have hfl0 : (st.flags[p.toNat / 2]?.getD 0#32 &&& 2#32) = 0#32 := by
              rw [← hpv_eq, ← hp_eq]; exact ‹_›
            obtain ⟨hinvS, hresS⟩ := k6a_resolvent_step_skip hinvL' fun h => h.1 hfl0
            c0_hsteps!
            refine hL (idx_bv - 1#32, st) mL (by dsimp only; rw [hidx_sub]; omega)
              ⟨by dsimp only; rw [hidx_sub]; exact hinvS, hpresL, htlL,
               by dsimp only; rw [hidx_sub, ← hresS]; exact hentL', hmL⟩
      · c0_hsteps!
        exact hB (idx_bv, 0xFFFFFFFF#32, st) mL ⟨k6AnaBrkPost_of_uip_ff hinvL hpresL htlL, hmL⟩
    · intro B L' hB hL; exact wp_jump_state (proj := fun p : BitVec 32 × K6State => (p.1, ()))
        (ks1.trl_end, ks1) rfl (hL (ks1.trl_end, ks1) m1
          ⟨by rw [hpres_k1.trl_end]; exact hinv1, hpres_k1, htl_k1,
           by rw [hpres_k1.trl_end]; exact hent1, hm1A⟩)

end LeanQbe.T.Examples.Kissat.Proof.Kitten
end
