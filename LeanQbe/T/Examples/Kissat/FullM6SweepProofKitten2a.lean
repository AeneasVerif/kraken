module

public import LeanQbe.T.Examples.Kissat.FullM6SweepProofKitten1

/-!
# Kissat `D-Full` M6 — Scaled `K6` Sub-Solver Proofs (`Part 2a`, `11/39` cumulative)

Parametric `(Γ : Env)` `Func.wp` contract for `full_k6_propagate` (`11/39` cumulative),
supporting scaled `512 ≤ max_v ≤ 8192`, inline binary `K6_BIN_FLAG` fast-paths, and `u64`
clause-scan/visit tick accounting via `full_k6_add_ticks`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Sweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Sweep
open Kraken.Bedrock2.Test

open K6MemATactics K6PtrTactics
open scoped K6MemATactics K6PtrTactics

/-! ## 1. Propagation Frame & Unlinked-Clause Falsification Helpers -/

private structure K6PropFrame (ks0 ks : K6State) : Prop where
  pres : K6PropPreserved ks0 ks
  te_ge : ks0.trl_end.toNat ≤ ks.trl_end.toNat
  old_trl : ∀ i < ks0.trl_end.toNat,
    ks.trl[i]? = ks0.trl[i]? ∧
    ks.lvlArr[(ks0.trl[i]?.getD 0#32).toNat / 2]? =
      ks0.lvlArr[(ks0.trl[i]?.getD 0#32).toNat / 2]? ∧
    ks.rsn[(ks0.trl[i]?.getD 0#32).toNat / 2]? =
      ks0.rsn[(ks0.trl[i]?.getD 0#32).toNat / 2]?
  new_trl : ∀ i, ks0.trl_end.toNat ≤ i → i < ks.trl_end.toNat →
    ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = ks0.lvl ∧
    ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 ≠ 0xFFFFFFFF#32

private theorem K6PropFrame.refl (ks : K6State) : K6PropFrame ks ks :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   le_refl _, fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ h1 h2 => by omega⟩

private theorem K6PropFrame.cast {ks0 ks ks' : K6State} (h : K6PropFrame ks0 ks)
    (h1 : ks'.nv = ks.nv) (h2 : ks'.nc = ks.nc) (h3 : ks'.lvl = ks.lvl)
    (h4 : ks'.incons = ks.incons) (h5 : ks'.alen = ks.alen) (h6 : ks'.acap = ks.acap)
    (h7 : ks'.nassump = ks.nassump) (h8 : ks'.status = ks.status)
    (h9 : ks'.openCnt = ks.openCnt) (h10 : ks'.max_v = ks.max_v)
    (h11 : ks'.max_orig = ks.max_orig) (h12 : ks'.max_cl = ks.max_cl)
    (h13 : ks'.neq = ks.neq) (h14 : ks'.assump = ks.assump)
    (h15 : ks'.trl_end = ks.trl_end) (h16 : ks'.trl = ks.trl)
    (h17 : ks'.lvlArr = ks.lvlArr) (h18 : ks'.rsn = ks.rsn) : K6PropFrame ks0 ks' :=
  ⟨⟨h1.trans h.pres.nv, h2.trans h.pres.nc, h3.trans h.pres.lvl, h4.trans h.pres.incons,
    h5.trans h.pres.alen, h6.trans h.pres.acap, h7.trans h.pres.nassump, h8.trans h.pres.status,
    h9.trans h.pres.openCnt, h10.trans h.pres.max_v, h11.trans h.pres.max_orig,
    h12.trans h.pres.max_cl, h13.trans h.pres.neq, h14.trans h.pres.assump⟩,
   h15 ▸ h.te_ge,
   fun i hi => by rw [h16, h17, h18]; exact h.old_trl i hi,
   fun i hlo hhi => by rw [h15] at hhi; rw [h16, h17, h18]; exact h.new_trl i hlo hhi⟩

private theorem K6PropFrame.trans {ks0 ks1 ks2 : K6State}
    (h12 : K6PropFrame ks0 ks1) (h23 : K6PropFrame ks1 ks2) : K6PropFrame ks0 ks2 :=
  ⟨⟨h23.pres.nv.trans h12.pres.nv, h23.pres.nc.trans h12.pres.nc, h23.pres.lvl.trans h12.pres.lvl,
    h23.pres.incons.trans h12.pres.incons, h23.pres.alen.trans h12.pres.alen,
    h23.pres.acap.trans h12.pres.acap, h23.pres.nassump.trans h12.pres.nassump,
    h23.pres.status.trans h12.pres.status, h23.pres.openCnt.trans h12.pres.openCnt,
    h23.pres.max_v.trans h12.pres.max_v, h23.pres.max_orig.trans h12.pres.max_orig,
    h23.pres.max_cl.trans h12.pres.max_cl, h23.pres.neq.trans h12.pres.neq,
    h23.pres.assump.trans h12.pres.assump⟩,
   Nat.le_trans h12.te_ge h23.te_ge,
   fun i hi => by
     have h1 := h12.old_trl i hi
     have h2 := h23.old_trl i (Nat.lt_of_lt_of_le hi h12.te_ge)
     rw [h1.1] at h2
     exact ⟨h2.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩,
   fun i hlo hhi => by
     by_cases h1 : i < ks1.trl_end.toNat
     · have hn := h12.new_trl i hlo h1
       have ho := h23.old_trl i h1
       rw [ho.1, ho.2.1, ho.2.2]; exact hn
     · have hn := h23.new_trl i (by omega) hhi; rw [h12.pres.lvl] at hn; exact hn⟩

private theorem k6PropAssign_frame {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) {lit rsn : BitVec 32} (hlit : lit.toNat < 2 * ks.nv.toNat)
    (hun : ks.vals[lit.toNat]? = some 0#32) (hrsn_ne : rsn ≠ 0xFFFFFFFF#32) :
    K6PropFrame ks (k6AssignStep ks lit rsn) := by
  have hm := L.hmaxV; have hnv := hinv.clauses.nv_le
  have hte_lt := k6_trl_end_lt_of_unassigned hinv.shapes hnv hinv.assign hlit (by simp [hun])
  have hv_eq := (k6_bv32_div2_lt hlit).1
  have hte1 : (ks.trl_end + 1#32).toNat = ks.trl_end.toNat + 1 := by bv_omega
  have hnot_trl : ∀ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := by
    intro i hi heq; have hnz := (hinv.assign.vals_nz_iff_trl lit.toNat hlit).mpr ⟨i, hi, heq⟩
    simp [hun] at hnz
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    by change ks.trl_end.toNat ≤ (ks.trl_end + 1#32).toNat; omega,
    fun i hi => by
      have hne := hnot_trl i hi
      exact ⟨List.getElem?_set_ne (by omega),
        by dsimp only [k6AssignStep]; rw [hv_eq]; exact List.getElem?_set_ne (Ne.symm hne),
        by dsimp only [k6AssignStep]; rw [hv_eq]; exact List.getElem?_set_ne (Ne.symm hne)⟩,
    fun i hlo hhi => by
      change i < (ks.trl_end + 1#32).toNat at hhi; rw [hte1] at hhi
      have hie : i = ks.trl_end.toNat := by omega
      subst hie; dsimp only [k6AssignStep]
      rw [List.getElem?_set_self (by rw [hinv.shapes.trl_len]; omega),
        Option.getD_some, hv_eq,
        List.getElem?_set_self (by rw [hinv.shapes.lvlArr_len]; omega),
        List.getElem?_set_self (by rw [hinv.shapes.rsn_len]; omega),
        Option.getD_some, Option.getD_some]
      exact ⟨rfl, hrsn_ne⟩⟩

private theorem k6BumpProp_preserves_inv {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks) {p' : BitVec 32}
    (hp_le : p'.toNat ≤ ks.trl_end.toNat) :
    K6Inv L P (ks.putHdr .prop p') ∧ K6TrailSynced (ks.putHdr .prop p') :=
  ⟨⟨hinv.shapes.putHdr .prop p',
    k6ClausesOk_cast hinv.clauses (by k6_field) (by k6_field) (by k6_field) (by k6_field)
      (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field)
      (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field),
    by dsimp only [K6State.putHdr]; exact hinv.watches,
    { hinv.assign with prop_le := by dsimp only [K6State.putHdr]; exact hp_le },
    by dsimp only [K6State.putHdr]; exact hinv.reasons⟩,
   by dsimp only [K6State.putHdr]; exact hsync⟩

private theorem k6_unlinked_clause_falsified {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks : K6State} (hinv : K6Inv L P ks) {cid slot : Nat} (hcid : cid < ks.nc.toNat)
    (hslot : slot < 2) {nl other : BitVec 32}
    (hnl_f : ks.vals[nl.toNat]? = some 2#32)
    (hslot_eq : (ks.arena[k6ClauseOff ks cid + slot]?.getD 0#32).toNat = nl.toNat)
    (hoth_eq : other.toNat = (ks.arena[k6ClauseOff ks cid + (slot ^^^ 1)]?.getD 0#32).toNat)
    (hrest : ∀ q, 2 ≤ q → q < k6ClauseSize ks cid →
      ks.vals[(ks.arena[k6ClauseOff ks cid + q]?.getD 0#32).toNat]? = some 2#32) :
    ∀ x ∈ k6ClauseLits ks cid, x ≠ other.toNat → ks.vals[x]? = some 2#32 := by
  intro x hx hne
  have hbd : k6ClauseOff ks cid + k6ClauseSize ks cid ≤ ks.arena.length := by
    rw [hinv.shapes.arena_len]; have := (hinv.clauses.cl_wf cid hcid).2.1
    have := hinv.clauses.alen_le; omega
  obtain ⟨q, hq, rfl⟩ := (k6_mem_clauseLits_iff hbd).mp hx
  by_cases hq2 : q < 2
  · by_cases hqs : q = slot
    · subst hqs; rw [hslot_eq]; exact hnl_f
    · have hqo : q = slot ^^^ 1 := by
        rcases (show slot = 0 ∨ slot = 1 by omega) with rfl | rfl
        · change q = 1; omega
        · change q = 0; omega
      subst hqo; exact absurd hoth_eq.symm hne
  · exact hrest q (by omega) hq

private theorem k6_unit_of_falsified {P : (Nat → Bool) → Prop} {l : Nat} {cl : List Nat}
    (h : SemEntails P cl) (hf : ∀ x ∈ cl, x ≠ l → SemEntails P [x ^^^ 1]) :
    SemEntails P [l] := fun β hβ => by
  obtain ⟨x, hx, hxs⟩ := (clause_sat_cnfClause_iff β cl).mp (h β hβ)
  by_cases hxl : x = l
  · rw [← hxl]; exact (sat_cnfClause_singleton β x).mpr hxs
  · exact absurd ((sat_cnfClause_singleton β x).mpr hxs)
      ((sat_cnfClause_litNeg_iff β x).mp (hf x hx hxl β hβ))

/-! ## 2. `11/39`: `full_k6_propagate_wp` -/

/-- `11/39`: Parametric `Func.wp` proof for `full_k6_propagate`. -/
theorem full_k6_propagate_wp (Γ : Env)
    (hAddTicks : M6EnvSpec Γ "full_k6_add_ticks" k6AddTicksSpec)
    (hAssign : M6EnvSpec Γ "full_k6_assign" k6AssignSpec) :
    ∀ args m Q X, k6PropagateSpec args m Q X → Func.wp Γ full_k6_propagate_body args m Q X := by
  rintro ⟨kPtr, ⟨⟩⟩ m Q X ⟨L, P, ks0, R, hinv0, hsync0, hm0, hQ⟩
  have hm_b := L.hmaxV; have hac_b := L.hacap
  have hmv0 : ks0.max_v = L.mv32 := hinv0.clauses.max_v_eq
  have hmA0 := k6Mem_to_amem hinv0.shapes hm0; clear hm0
  have hret : ∀ (confl : BitVec 32) (ksF : K6State) (mF : Mem 64),
      K6Inv L P ksF → K6TrailSynced ksF → K6PropFrame ks0 ksF →
      (confl = 0xFFFFFFFF#32 → ksF.prop = ksF.trl_end) →
      (confl ≠ 0xFFFFFFFF#32 → confl.toNat < ksF.nc.toNat ∧
        ∀ l ∈ k6ClauseLits ksF confl.toNat, ksF.vals[l]? = some 2#32) →
      (K6Mem L kPtr ksF ⋆ R) mF → Q (confl, ()) mF := fun confl ksF mF hi hs hf h1 h2 hmF =>
    hQ confl ksF mF hi hs hf.pres hf.te_ge hf.old_trl hf.new_trl h1 h2 hmF
  c0_hsteps_nogrp
  rw [hmv0]
  refine wp_while_state (α := BitVec 64 × K6State) (fun st => (st.1, ()))
    (fun st => ks0.nv.toNat - st.2.prop.toNat)
    (fun st mO => K6Inv L P st.2 ∧ K6TrailSynced st.2 ∧ K6PropFrame ks0 st.2 ∧
      (K6MemA L kPtr st.2 ⋆ R) mO) ?_ ?_
  · intro J hJ
    exact wp_jump_state (proj := fun st : BitVec 64 × K6State => (st.1, ())) (0#64, ks0) rfl
      (hJ (0#64, ks0) m ⟨hinv0, hsync0, K6PropFrame.refl ks0, hmA0⟩)
  · rintro J ⟨ticksO, ksO⟩ mO ⟨hinvO, hsyncO, hfrO, hmO⟩ ihO
    dsimp only at hinvO hsyncO hfrO hmO ⊢
    have hnvO := hinvO.clauses.nv_le
    c0_hsplit
    · -- ksO.prop < ksO.trl_end
      have hp_lt : ksO.prop.toNat < ksO.trl_end.toNat := by bv_omega
      have hp_mv : ksO.prop.toNat < szV L := by
        have := hinvO.assign.trl_end_le; unfold szV; omega
      let pO := ksO.prop
      let lit := ksO.trl[pO.toNat]?.getD 0#32
      have hlit_def : ksO.trl[ksO.prop.toNat]?.getD 0#32 = lit := rfl
      have hnl_bn : BitVec.ofNat 32 (lit ^^^ 1#32).toNat = lit ^^^ 1#32 := by simp
      have hlit_lt : lit.toNat < 2 * ksO.nv.toNat :=
        hinvO.assign.trl_lt lit.toNat (k6_mem_trailLits_of_lt hp_lt
          (by rw [hinvO.shapes.trl_len]; have := hinvO.assign.trl_end_le; omega))
      obtain ⟨hnl_eq, hnl_lt⟩ := k6_bv32_xor1_lt hlit_lt
      have hnl_mv2 : (lit ^^^ 1#32).toNat < sz2V L := by unfold sz2V; omega
      have hnl_val2O : ksO.vals[(lit ^^^ 1#32).toNat]? = some 2#32 := by
        rw [hnl_eq, show litNeg lit.toNat = lit.toNat ^^^ 1 from rfl]
        exact (hsyncO pO.toNat hp_lt).2
      have hp1_eq : (pO + 1#32).toNat = pO.toNat + 1 := by dsimp only [pO]; bv_omega
      obtain ⟨hinv1, hsync1⟩ := k6BumpProp_preserves_inv hinvO hsyncO (by rw [hp1_eq]; exact hp_lt)
      let ks1 := ksO.putHdr .prop (pO + 1#32)
      have hfr1 : K6PropFrame ks0 ks1 :=
        hfrO.cast rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      obtain ⟨ch1, hwc1⟩ :=
        K6WChainCursor.init hinv1.shapes hinv1.clauses.nv_le hinv1.watches hnl_lt
      c0_hsteps_nogrp
      refine wp_while_state
        (α :=
          BitVec 64 × BitVec 64 × BitVec 32 × BitVec 32 × List Nat × List Nat ×
            K6State × List (List Nat))
        (fun st => (st.1, st.2.1, st.2.2.1, st.2.2.2.1, ()))
        (fun st => st.2.2.2.2.2.1.length)
        (fun st mW =>
          K6WChainCursor st.2.2.2.2.2.2.1 (lit ^^^ 1#32).toNat st.2.2.2.2.2.2.2
            st.2.2.2.2.1 st.2.2.2.2.2.1 st.2.2.1 st.2.2.2.1 ∧
          K6Inv L P st.2.2.2.2.2.2.1 ∧ K6TrailSynced st.2.2.2.2.2.2.1 ∧
          K6PropFrame ks0 st.2.2.2.2.2.2.1 ∧ st.2.2.2.2.2.2.1.prop.toNat = pO.toNat + 1 ∧
          pO.toNat < st.2.2.2.2.2.2.1.trl_end.toNat ∧
          st.2.2.2.2.2.2.1.trl[pO.toNat]? = some lit ∧
          st.2.2.2.2.2.2.1.max_v = L.mv32 ∧
          (K6MemA L kPtr st.2.2.2.2.2.2.1 ⋆ R) mW) ?_ ?_
      · intro Jw hJw
        have htr_lit : ks1.trl[pO.toNat]? = some lit := by
          change ksO.trl[pO.toNat]? = some (ksO.trl[pO.toNat]?.getD 0#32)
          rw [List.getElem?_eq_getElem
            (by rw [hinvO.shapes.trl_len]; unfold szV at hp_mv; exact hp_mv),
            Option.getD_some]
        exact wp_jump_state
          (proj :=
            fun st : BitVec 64 × BitVec 64 × BitVec 32 × BitVec 32 × List Nat × List Nat ×
              K6State × List (List Nat) =>
            (st.1, st.2.1, st.2.2.1, st.2.2.2.1, ()))
          (ticksO, 0#64, 0xFFFFFFFF#32, ks1.whead[(lit ^^^ 1#32).toNat]?.getD 0#32, [],
            ch1[(lit ^^^ 1#32).toNat]?.getD [], ks1, ch1)
          rfl (hJw _ _ ⟨hwc1, hinv1, hsync1, hfr1, by change (pO + 1#32).toNat = _; exact hp1_eq,
            hp_lt, htr_lit, hinv1.clauses.max_v_eq, hm⟩)
      · rintro Jw ⟨ticks, visits, prev, w, done, todo, ksW, chW⟩ mW
          ⟨hwc, hinvW, hsyncW, hfrW, hw_pr, hw_te, hw_lit, hw_mv, hmW⟩ ihW
        dsimp only at hwc hinvW hsyncW hfrW hw_pr hw_te hw_lit hw_mv hmW ⊢
        have hshW := hinvW.shapes; have hclW := hinvW.clauses
        have hnvW := hclW.nv_le; have hncW := hclW.nc_le
        have hw_nl_lt : (lit ^^^ 1#32).toNat < 2 * ksW.nv.toNat := by
          rw [hfrW.pres.nv, ← hfrO.pres.nv]; exact hnl_lt
        have hnl_val2W : ksW.vals[(lit ^^^ 1#32).toNat]? = some 2#32 := by
          have hs := hsyncW pO.toNat hw_te
          rw [hw_lit, Option.getD_some] at hs
          rw [hnl_eq, show litNeg lit.toNat = lit.toNat ^^^ 1 from rfl]; exact hs.2
        c0_hsplit
        · have hw_ne : w ≠ 0xFFFFFFFF#32 := by bv_omega
          obtain ⟨w0, todo', hw0_len, rfl, rfl, hw0_nc, hw0_mc2, hw_tn, hw_div2, hw_mod2,
              hsz_ge, har_slot_l, hbv_nv, hbv_mem, hbin_iff, hbin_eq, _⟩ :=
            hwc.step_unfold hncW hw_nl_lt hw_ne
          have hw_mod32 : w0 % 2 ^ 32 = w0 := by
            unfold K6Layout.maxCl at hw0_mc2; omega
          have hw0_2cl : w0 < sz2Cl L := by unfold sz2Cl; exact hw0_mc2
          have hw0_bv2 : (BitVec.ofNat 32 w0).toNat < sz2Cl L := by rw [hw_tn]; exact hw0_2cl
          have hcid_lt : w0 / 2 < ksW.nc.toNat := by omega
          have hcid_cl : w0 / 2 < szCl L := by unfold szCl K6Layout.maxCl at *; omega
          have hcid_ne_ff : BitVec.ofNat 32 w0 >>> (1 : Nat) ≠ 0xFFFFFFFF#32 := fun h => by
            have := congrArg BitVec.toNat h; rw [hw_div2] at this
            change w0 / 2 = 4294967295 at this; unfold K6Layout.maxCl at *; omega
          have hwf_c := hclW.cl_wf (w0 / 2) hcid_lt
          let bv_bv := ksW.wblit[w0]?.getD 0#32 &&& 0x7FFFFFFF#32
          have hbv_mv2 : bv_bv.toNat < sz2V L := by dsimp only [bv_bv]; unfold sz2V; omega
          have hbv_mv2' : (ksW.wblit[(BitVec.ofNat 32 w0).toNat]?.getD 0#32 &&&
              0x7FFFFFFF#32).toNat < sz2V L := by
            rw [hw_tn]; exact hbv_mv2
          c0_hsplit
          · -- vals[bv] == 1 => keep watch & continue
            have hwc_next := k6WatchSkip_cursor hshW hwc hw0_len
            c0_hsteps!; rw [hw_tn]
            exact ihW (ticks, visits + 1#64, BitVec.ofNat 32 w0, ksW.wnext[w0]?.getD 0#32,
                done ++ [w0], todo', ksW, chW) mW (by simp)
              ⟨hwc_next, hinvW, hsyncW, hfrW, hw_pr, hw_te, hw_lit, hw_mv, hmW⟩
          · have hbv_ne1 : ksW.vals[bv_bv.toNat]? ≠ some 1#32 := fun h1 => by
              have hhc : ¬ksW.vals[(ksW.wblit[w0 % 2 ^ 32]?.getD 0#32 &&&
                  2147483647).toNat]?.getD 0#32 = 1#32 := ‹_›
              rw [hw_mod32] at hhc
              exact hhc (by
                change ksW.vals[bv_bv.toNat]?.getD 0#32 = 1#32
                rw [h1]; rfl)
            c0_hsplit
            · -- Inline binary fast-path `(wb & K6_BIN_FLAG) != 0`
              have hbin_nz : (ksW.wblit[w0]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := by
                rw [← hw_tn]; exact ‹_›
              have hsz2 : k6ClauseSize ksW (w0 / 2) = 2 := hbin_iff.mp hbin_nz
              have hbv_slot : bv_bv.toNat =
                  (ksW.arena[k6ClauseOff ksW (w0 / 2) + (w0 % 2 ^^^ 1)]?.getD 0#32).toNat :=
                hbin_eq hsz2
              have hbin_fals := k6_unlinked_clause_falsified hinvW hcid_lt
                (Nat.mod_lt w0 (by decide)) hnl_val2W har_slot_l hbv_slot
                (fun q hq2 hqlt => by rw [hsz2] at hqlt; omega)
              c0_hsplit
              · -- bvv == 2 => conflict return cid
                have hbv2 : ksW.vals[bv_bv.toNat]? = some 2#32 := by
                  have h0 : ksW.vals[bv_bv.toNat]?.getD 0#32 = 2#32 := by
                    dsimp only [bv_bv]; rw [← hw_tn]; exact ‹_›
                  have hvl : bv_bv.toNat < ksW.vals.length := by
                    rw [hshW.vals_len]; exact hbv_mv2
                  rw [List.getElem?_eq_getElem hvl, Option.getD_some] at h0
                  rw [List.getElem?_eq_getElem hvl, h0]
                c0_hsteps_nogrp
                k6_call hAddTicks
                refine ⟨L, ksW, R, hshW, (k6MemA_to_mem hmW).2, fun tk' m' hm' => ?_⟩
                have hinvT := k6AddTicks_preserves_inv hinvW tk'
                have hsyncT : K6TrailSynced (ksW.putHdr .ticks tk') := hsyncW
                have hfrT : K6PropFrame ks0 (ksW.putHdr .ticks tk') :=
                  hfrW.cast rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                c0_hsteps!
                refine hret (BitVec.ofNat 32 w0 >>> (1 : Nat)) (ksW.putHdr .ticks tk') m' hinvT
                  hsyncT hfrT (fun h => absurd h hcid_ne_ff) (fun _ => ?_) hm'
                rw [hw_div2]
                refine ⟨by change w0 / 2 < ksW.nc.toNat; exact hcid_lt, fun x hx => ?_⟩
                change x ∈ k6ClauseLits ksW (w0 / 2) at hx
                by_cases hxb : x = bv_bv.toNat
                · rw [hxb]; exact hbv2
                · exact hbin_fals x hx hxb
              · -- bvv != 2 => if bvv == 0 assign & continue
                have hbv_ne2 : ksW.vals[bv_bv.toNat]? ≠ some 2#32 := fun h2 => by
                  have hhc : ¬ksW.vals[(ksW.wblit[w0 % 2 ^ 32]?.getD 0#32 &&&
                      2147483647).toNat]?.getD 0#32 = 2#32 := ‹_›
                  rw [hw_mod32] at hhc
                  exact hhc (by
                    change ksW.vals[bv_bv.toNat]?.getD 0#32 = 2#32
                    rw [h2]; rfl)
                have hbv0 : ksW.vals[bv_bv.toNat]? = some 0#32 := by
                  rcases hinvW.assign.vals_dom bv_bv.toNat hbv_nv with h0 | h1 | h2
                  · have hvl : bv_bv.toNat < ksW.vals.length := by
                      rw [hshW.vals_len]; exact hbv_mv2
                    rw [List.getElem?_eq_getElem hvl, Option.getD_some] at h0
                    rw [List.getElem?_eq_getElem hvl, h0]
                  · exact absurd (by
                      have hvl : bv_bv.toNat < ksW.vals.length := by
                        rw [hshW.vals_len]; exact hbv_mv2
                      rw [List.getElem?_eq_getElem hvl, Option.getD_some] at h1
                      rw [List.getElem?_eq_getElem hvl, h1]) hbv_ne1
                  · exact absurd (by
                      have hvl : bv_bv.toNat < ksW.vals.length := by
                        rw [hshW.vals_len]; exact hbv_mv2
                      rw [List.getElem?_eq_getElem hvl, Option.getD_some] at h2
                      rw [List.getElem?_eq_getElem hvl, h2]) hbv_ne2
                have hte_ltW := k6_trl_end_lt_of_unassigned hshW hnvW hinvW.assign hbv_nv
                  (by dsimp only [bv_bv] at hbv0; rw [hbv0]; rfl)
                obtain ⟨hinvB, hsyncB⟩ := k6AssignStep_preserves_inv hinvW hsyncW hbv_nv hbv0
                  (fun hl0 => k6_unit_of_falsified hwf_c.2.2.2 fun x hx hne =>
                    (k6_falsified_lvl0_entails hinvW hl0 (hwf_c.2.2.1 x hx)
                      (hbin_fals x hx hne)).2)
                  (fun _ hrs => absurd hrs hcid_ne_ff)
                  (Or.inr ⟨by rw [hw_div2]; exact hcid_lt, by rw [hw_div2]; exact hbv_mem,
                    fun x hx hne => by
                      rw [hw_div2] at hx
                      exact k6_falsified_to_trail hinvW.assign hsyncW (hwf_c.2.2.1 x hx)
                        (hbin_fals x hx hne)⟩)
                have hfr_kb := k6PropAssign_frame hinvW hbv_nv hbv0 hcid_ne_ff
                let ksB := k6AssignStep ksW bv_bv (BitVec.ofNat 32 w0 >>> (1 : Nat))
                refine wp_join0 (fun mB => (K6MemA L kPtr ksB ⋆ R) mB) ?_ ?_
                · intro Jb mB hmB
                  have hwcB : K6WChainCursor ksB (lit ^^^ 1#32).toNat chW done (w0 :: todo') prev
                      (BitVec.ofNat 32 w0) :=
                    ⟨hwc.len_eq, hwc.nodup, hwc.chain_l, hwc.chains_wc, hwc.chains_bnd,
                     hwc.tail_wc, hwc.prev_rel⟩
                  have hskipB := k6WatchSkip_cursor hinvB.shapes hwcB hw0_len
                  c0_hsteps!; rw [hw_tn]
                  refine ihW (ticks, visits + 1#64, BitVec.ofNat 32 w0, ksB.wnext[w0]?.getD 0#32,
                      done ++ [w0], todo', ksB, chW) mB (by simp)
                    ⟨hskipB, hinvB, hsyncB, hfrW.trans hfr_kb, hw_pr,
                     Nat.lt_of_lt_of_le hw_te hfr_kb.te_ge,
                     (hfr_kb.old_trl pO.toNat hw_te).1.trans hw_lit, hw_mv, hmB⟩
                · intro Jb hJb
                  c0_hsplit
                  · c0_hsteps_nogrp
                    k6_call hAssign
                    refine ⟨L, ksW, R, hshW, hw_mv, by omega, Nat.lt_of_lt_of_le hte_ltW hnvW,
                      (k6MemA_to_mem hmW).2, fun mB hmB => ?_⟩
                    rw [hw_tn] at hmB
                    exact hJb mB (k6Mem_to_amem hinvB.shapes hmB)
                  · exfalso
                    have hhc : ¬ksW.vals[(ksW.wblit[w0 % 2 ^ 32]?.getD 0#32 &&&
                        2147483647).toNat]?.getD 0#32 = 0#32 := ‹_›
                    rw [hw_mod32] at hhc
                    exact hhc (by
                      change ksW.vals[bv_bv.toNat]?.getD 0#32 = 0#32
                      rw [hbv0]; rfl)
            · -- Non-binary `(wb & K6_BIN_FLAG) == 0`
              have hnonbin : (ksW.wblit[w0]?.getD 0#32 &&& 0x80000000#32) = 0#32 := by
                rw [← hw_tn]; bv_omega
              have hsz_ne2 : k6ClauseSize ksW (w0 / 2) ≠ 2 := fun h2 =>
                absurd (hbin_iff.mpr h2) (by rw [hnonbin]; simp)
              have har_ok : ∀ idx < k6ClauseSize ksW (w0 / 2),
                  k6ClauseOff ksW (w0 / 2) + idx < L.acap ∧
                  (ksW.arena[k6ClauseOff ksW (w0 / 2) + idx]?.getD 0#32).toNat <
                    2 * ksW.nv.toNat := by
                intro idx hidx
                have hcap : k6ClauseOff ksW (w0 / 2) + idx < L.acap := by
                  have := hclW.alen_le; omega
                have hmem : (ksW.arena[k6ClauseOff ksW (w0 / 2) + idx]?.getD 0#32).toNat ∈
                    k6ClauseLits ksW (w0 / 2) := by
                  rw [k6_mem_clauseLits_iff
                    (by rw [hshW.arena_len]; have := hclW.alen_le; omega)]
                  exact ⟨idx, hidx, rfl⟩
                exact ⟨hcap, hwf_c.2.2.1 _ hmem⟩
              have hother_slot_lt : w0 % 2 ^^^ 1 < 2 := by
                rcases Nat.mod_two_eq_zero_or_one w0 with h | h <;> simp [h]
              let other := ksW.arena[k6ClauseOff ksW (w0 / 2) + (w0 % 2 ^^^ 1)]?.getD 0#32
              have hother_nv : other.toNat < 2 * ksW.nv.toNat := (har_ok _ (by omega)).2
              have hot_mem : other.toNat ∈ k6ClauseLits ksW (w0 / 2) := by
                rw [k6_mem_clauseLits_iff
                  (by rw [hshW.arena_len]; have := hclW.alen_le; omega)]
                exact ⟨w0 % 2 ^^^ 1, by omega, rfl⟩
              have hw_sh1 : (BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat = w0 / 2 := hw_div2
              have hw_m2_lt : w0 % 2 < 2 ^ 32 :=
                Nat.lt_trans (Nat.mod_lt w0 (by decide)) (by decide)
              have hm2_xor_lt : w0 % 2 ^^^ 1 < 2 ^ 32 := by
                rcases Nat.mod_two_eq_zero_or_one w0 with h | h <;> simp [h]
              have hslot_bv :
                  (BitVec.ofNat 32 w0 &&& (1 : BitVec 32)) = BitVec.ofNat 32 (w0 % 2) := by
                apply BitVec.eq_of_toNat_eq
                change (BitVec.ofNat 32 w0 &&& 1#32).toNat = (BitVec.ofNat 32 (w0 % 2)).toNat
                rw [hw_mod2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_m2_lt]
              have hslot_other_bv :
                  (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^ (1 : BitVec 32)) =
                    BitVec.ofNat 32 (w0 % 2 ^^^ 1) := by
                apply BitVec.eq_of_toNat_eq
                rw [BitVec.toNat_xor,
                  show (BitVec.ofNat 32 w0 &&& (1 : BitVec 32)).toNat =
                    (BitVec.ofNat 32 w0 &&& 1#32).toNat from rfl,
                  hw_mod2, show (1 : BitVec 32).toNat = 1 from rfl, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt hm2_xor_lt]
              have hcl_off_add :
                  (ksW.clOff[w0 / 2]?.getD 0#32 +
                    (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^ (1 : BitVec 32))).toNat =
                  k6ClauseOff ksW (w0 / 2) + (w0 % 2 ^^^ 1) := by
                have hcap' : k6ClauseOff ksW (w0 / 2) + (w0 % 2 ^^^ 1) < L.acap :=
                  (har_ok (w0 % 2 ^^^ 1) (by omega)).1
                unfold k6ClauseOff at hcap' ⊢; unfold dimacsBound at hac_b
                rw [hslot_other_bv]; have := hm2_xor_lt; bv_omega
              have hcl_off_ar :
                  ((ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32) +
                    (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^ (1 : BitVec 32))).toNat <
                    szAr L := by
                unfold szAr; rw [hw_sh1, hcl_off_add]; exact (har_ok (w0 % 2 ^^^ 1) (by omega)).1
              have hother_mv2 : other.toNat < sz2V L := by unfold sz2V; omega
              have hoth_arr_lt :
                  (ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32 +
                    (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^ (1 : BitVec 32))).toNat]?.getD
                      0#32).toNat < sz2V L := by
                rw [hw_sh1, hcl_off_add]; exact hother_mv2
              have hslot_other_nat :
                  (BitVec.ofNat 32 w0 &&& 1#32 ^^^ 1#32).toNat = w0 % 2 ^^^ 1 := by
                have := congrArg BitVec.toNat hslot_other_bv
                rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm2_xor_lt] at this
              have hother_hc_eq :
                  ksW.arena[((ksW.clOff[w0 % 2 ^ 32 / 2]?.getD 0#32).toNat +
                    (BitVec.ofNat 32 w0 &&& 1#32 ^^^ 1#32).toNat) % 2 ^ 32]?.getD 0#32 =
                  other := by
                have hcap' : k6ClauseOff ksW (w0 / 2) + (w0 % 2 ^^^ 1) < L.acap :=
                  (har_ok (w0 % 2 ^^^ 1) (by omega)).1
                have hac_lt : L.acap < 2 ^ 32 := by unfold dimacsBound at hac_b; omega
                dsimp only [other, k6ClauseOff] at hcap' ⊢
                rw [hw_mod32, hslot_other_nat, Nat.mod_eq_of_lt (by omega)]
              c0_hsplit
              · -- vals[other] == 1 => wblit[w] = other, keep watch & continue
                obtain ⟨hkp_inv, hkp_wc⟩ :=
                  k6WatchKeep_preserves hinvW hw_nl_lt hwc hother_nv hot_mem hsz_ne2
                c0_hsteps!; rw [hw_tn]
                refine ihW (ticks, visits + 1#64, BitVec.ofNat 32 w0, ksW.wnext[w0]?.getD 0#32,
                    done ++ [w0], todo', ksW.putArr .wblit w0 other, chW) _ (by simp)
                  ⟨hkp_wc, hkp_inv, hsyncW,
                    hfrW.cast rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                      rfl,
                    hw_pr, hw_te, hw_lit, hw_mv, ?_⟩
                refine Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _) ?_) ‹_›
                k6_ext <;> (first | rfl | {
                  dsimp only [other]
                  try rw [hw_tn]
                  try rw [hw_sh1]
                  try rw [hcl_off_add]
                  try dsimp only [k6ClauseOff]
                  try rfl })
              · -- vals[other] != 1 => bump ticks, scan r = 2..sz-1
                have hoth_ne1 : ksW.vals[other.toNat]? ≠ some 1#32 := fun h1 => by
                  have hhc : ¬ksW.vals[(ksW.arena[((ksW.clOff[w0 % 2 ^ 32 / 2]?.getD 0#32).toNat +
                      (BitVec.ofNat 32 w0 &&& 1#32 ^^^ 1#32).toNat) % 2 ^ 32]?.getD
                        0#32).toNat]?.getD 0#32 = 1#32 := ‹_›
                  rw [hother_hc_eq] at hhc
                  exact hhc (by rw [h1]; rfl)
                c0_hsteps_nogrp
                let sz := ksW.clSz[w0 / 2]?.getD 0#32
                let off := ksW.clOff[w0 / 2]?.getD 0#32
                refine wp_while_break_state
                  (projBrk :=
                    fun b : BitVec 32 × BitVec 32 × BitVec 32 => (b.1, b.2.1, b.2.2, ()))
                  (fun b mb => mW = mb ∧
                    ((b.2.1 = 0xFFFFFFFF#32 ∧ ∀ q, 2 ≤ q → q < sz.toNat →
                      ksW.vals[(ksW.arena[off.toNat + q]?.getD 0#32).toNat]? = some 2#32) ∨
                     (2 ≤ b.2.1.toNat ∧ b.2.1.toNat < sz.toNat ∧
                      b.2.2 = ksW.arena[off.toNat + b.2.1.toNat]?.getD 0#32 ∧
                      ksW.vals[b.2.2.toNat]? ≠ some 2#32)))
                  (projLp := fun st : BitVec 32 => (st, ())) (fun st => sz.toNat - st.toNat)
                  (fun r m'' => mW = m'' ∧ r.toNat ≤ sz.toNat ∧ 2 ≤ r.toNat ∧
                    ∀ q, 2 ≤ q → q < r.toNat →
                      ksW.vals[(ksW.arena[off.toNat + q]?.getD 0#32).toNat]? = some 2#32)
                  ?_ ?_ ?_
                · rintro B ⟨_, ri, repl⟩ mb ⟨hmb, hbrk⟩
                  subst mb
                  dsimp only at hbrk ⊢
                  c0_hsplit
                  · -- ri != 0xFFFFFFFF => relocate watch
                    have hri_ne : ri ≠ 0xFFFFFFFF#32 := by bv_omega
                    obtain ⟨hri_ge, hri_lt, hrepl_eq, hrepl_ne2⟩ :=
                      hbrk.resolve_left (fun h => hri_ne h.1)
                    have hrepl_ne : repl.toNat ≠ (lit ^^^ 1#32).toNat := fun h =>
                      hrepl_ne2 (by rw [h]; exact hnl_val2W)
                    obtain ⟨hrl_inv, ⟨chR, hwcR⟩⟩ :=
                      k6WatchReloc_preserves hinvW hw_nl_lt hwc hri_ge hri_lt hrepl_ne rfl hrepl_eq
                    obtain ⟨hri_cap, hri_lit⟩ := har_ok ri.toNat hri_lt
                    obtain ⟨hslot_cap, _⟩ :=
                      har_ok (w0 % 2) (by have := Nat.mod_lt w0 (by decide : 0 < 2); omega)
                    have hslot_off_eq :
                        (ksW.clOff[w0 / 2]?.getD 0#32 +
                          (BitVec.ofNat 32 w0 &&& (1 : BitVec 32))).toNat =
                        (ksW.clOff[w0 / 2]?.getD 0#32).toNat + w0 % 2 := by
                      rw [hslot_bv]; unfold dimacsBound at hac_b
                      change (ksW.clOff[w0 / 2]?.getD 0#32 + BitVec.ofNat 32 (w0 % 2)).toNat = _
                      change k6ClauseOff ksW (w0 / 2) + w0 % 2 < L.acap at hslot_cap
                      unfold k6ClauseOff at hslot_cap; bv_omega
                    have hslot_ar :
                        (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32 +
                          (BitVec.ofNat 32 w0 &&& (1 : BitVec 32))).toNat < szAr L := by
                      unfold szAr; rw [hw_sh1, hslot_off_eq]; exact hslot_cap
                    have hri_off_eq :
                        (ksW.clOff[w0 / 2]?.getD 0#32 + ri).toNat =
                        (ksW.clOff[w0 / 2]?.getD 0#32).toNat + ri.toNat := by
                      unfold dimacsBound at hac_b
                      change k6ClauseOff ksW (w0 / 2) + ri.toNat < L.acap at hri_cap
                      unfold k6ClauseOff at hri_cap; bv_omega
                    have hri_ar :
                        (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32 +
                          ri).toNat < szAr L := by
                      unfold szAr; rw [hw_sh1, hri_off_eq]; exact hri_cap
                    have hrepl_mv2 : repl.toNat < sz2V L := by
                      change repl = ksW.arena[k6ClauseOff ksW (w0 / 2) +
                        ri.toNat]?.getD 0#32 at hrepl_eq
                      rw [hrepl_eq]; unfold sz2V; omega
                    have hprv_lt : prev ≠ 0xFFFFFFFF#32 → prev.toNat < sz2Cl L := fun hp => by
                      rcases hwc.prev_rel with ⟨_, hpf, _⟩ | ⟨_, u, _, hp_eq, hu_len, _⟩
                      · exact absurd hpf hp
                      · rw [hshW.wnext_len] at hu_len
                        have hu32 : u < 2 ^ 32 := by unfold K6Layout.maxCl at hu_len; omega
                        rw [hp_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu32]
                        unfold sz2Cl; exact hu_len
                    let nxt := ksW.wnext[w0]?.getD 0#32
                    let ar1 := (ksW.arena.set (k6ClauseOff ksW (w0 / 2) + w0 % 2) repl).set
                      (k6ClauseOff ksW (w0 / 2) + ri.toNat) (BitVec.ofNat 32 (lit ^^^ 1#32).toNat)
                    let wh1 := if prev = 0xFFFFFFFF#32 then ksW.whead.set (lit ^^^ 1#32).toNat nxt
                      else ksW.whead
                    let wn1 := if prev = 0xFFFFFFFF#32 then ksW.wnext
                      else ksW.wnext.set prev.toNat nxt
                    let ks1r : K6State := { ksW with arena := ar1, whead := wh1, wnext := wn1 }
                    c0_hsteps_nogrp
                    refine wp_join0 (fun mr => (K6MemA L kPtr ks1r ⋆ R) mr) ?_ ?_
                    · intro Jr mr hmr
                      c0_hsteps!; rw [hw_tn]
                      refine ihW (ticks + 1#64, visits + 1#64, prev, nxt, done, todo', _, chR)
                        _ (by simp)
                        ⟨hwcR, hrl_inv, hsyncW,
                          hfrW.cast rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                            rfl rfl rfl,
                          hw_pr, hw_te, hw_lit,
                          (by exact hw_mv), ?_⟩
                      refine Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _) ?_) ‹_›
                      dsimp only [k6WatchStep0, ks1r, wh1, wn1, ar1, nxt]
                      k6_ext <;> (first | rfl | {
                        try rw [hw_tn]
                        try rw [hw_sh1]
                        try rw [hcl_off_add]
                        try dsimp only [k6ClauseOff]
                        try rfl })
                    · intro Jr hJr
                      c0_hsplit
                      · have hpeq : prev = 0xFFFFFFFF#32 := by bv_omega
                        c0_hsteps!
                        refine hJr _ (Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _) ?_) ‹_›)
                        dsimp only [ks1r, wh1, wn1, ar1, nxt]; simp only [hpeq, ↓reduceIte]
                        k6_ext <;> (first | rfl | {
                          try rw [hw_tn]
                          try rw [hw_sh1]
                          try rw [hslot_off_eq]
                          try rw [hri_off_eq]
                          try rw [hlit_def]
                          try rw [hnl_bn]
                          try dsimp only [k6ClauseOff]
                          try rfl })
                      · have hpne : prev ≠ 0xFFFFFFFF#32 := by bv_omega
                        have hprv_bd := hprv_lt hpne
                        c0_hsteps!
                        refine hJr _ (Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _) ?_) ‹_›)
                        dsimp only [ks1r, wh1, wn1, ar1, nxt]; simp only [hpne, ↓reduceIte]
                        k6_ext <;> (first | rfl | {
                          try rw [hw_tn]
                          try rw [hw_sh1]
                          try rw [hslot_off_eq]
                          try rw [hri_off_eq]
                          try rw [hlit_def]
                          try rw [hnl_bn]
                          try dsimp only [k6ClauseOff]
                          try rfl })
                  · -- ri == 0xFFFFFFFF => conflict or unit propagation
                    have hri_eq : ri = 0xFFFFFFFF#32 := by bv_omega
                    have h_all2 : ∀ q, 2 ≤ q → q < sz.toNat →
                        ksW.vals[(ksW.arena[off.toNat + q]?.getD 0#32).toNat]? = some 2#32 :=
                      (hbrk.resolve_right fun h => by
                        have hlt := h.2.1
                        have hsz_bd : sz.toNat < 2 ^ 28 := by
                          have := hclW.alen_le; unfold dimacsBound at hac_b
                          change k6ClauseSize ksW (w0 / 2) < 2 ^ 28; omega
                        rw [hri_eq,
                          show (0xFFFFFFFF#32 : BitVec 32).toNat = 4294967295 from rfl] at hlt
                        omega).2
                    obtain ⟨hinvK, hwcK⟩ :=
                      k6WatchKeep_preserves hinvW hw_nl_lt hwc hother_nv hot_mem hsz_ne2
                    let ksK := ksW.putArr .wblit w0 other
                    have hfrK : K6PropFrame ks0 ksK :=
                      hfrW.cast rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                        rfl rfl
                    have hcl_fals := k6_unlinked_clause_falsified hinvK hcid_lt
                      (Nat.mod_lt w0 (by decide)) hnl_val2W har_slot_l rfl h_all2
                    have hother_bv_eq :
                        ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD
                          0#32 + (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^
                          (1 : BitVec 32))).toNat]?.getD 0#32 = other := by
                      rw [hw_sh1, hcl_off_add]
                    have hmvK : ksK.max_v = L.mv32 := by dsimp only [ksK]; k6_field; exact hw_mv
                    c0_hsteps_nogrp
                    c0_hsplit
                    · -- ov == 2 => add_ticks & return cid
                      have hov2 : ksK.vals[other.toNat]? = some 2#32 := by
                        have hc0 : ksW.vals[other.toNat]?.getD 0#32 = 2#32 := by
                          rw [← hother_hc_eq]; exact ‹_›
                        have hvl : other.toNat < ksW.vals.length := by
                          rw [hshW.vals_len]; exact hother_mv2
                        dsimp only [ksK, K6State.putArr]
                        rw [List.getElem?_eq_getElem hvl, Option.getD_some] at hc0
                        rw [List.getElem?_eq_getElem hvl, hc0]
                      have hmK : (K6MemA L kPtr ksK ⋆ R) m := by
                        refine Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) m) ?_) ‹_›
                        dsimp only [ksK]; k6_ext <;> (first | rfl | {
                          try rw [hw_tn]
                          rw [hother_bv_eq] })
                      k6_call hAddTicks
                      refine ⟨L, ksK, R, hinvK.shapes, (k6MemA_to_mem hmK).2,
                        fun tk' m' hm' => ?_⟩
                      have hinvT := k6AddTicks_preserves_inv hinvK tk'
                      have hsyncT : K6TrailSynced (ksK.putHdr .ticks tk') := hsyncW
                      have hfrT : K6PropFrame ks0 (ksK.putHdr .ticks tk') :=
                        hfrK.cast rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                          rfl rfl
                      c0_hsteps!
                      refine hret (BitVec.ofNat 32 w0 >>> (1 : Nat)) (ksK.putHdr .ticks tk') m'
                        hinvT hsyncT hfrT (fun h => absurd h hcid_ne_ff) (fun _ => ?_) hm'
                      rw [hw_div2]
                      refine ⟨by change w0 / 2 < ksK.nc.toNat; exact hcid_lt, fun x hx => ?_⟩
                      change x ∈ k6ClauseLits ksK (w0 / 2) at hx
                      by_cases hxo : x = other.toNat
                      · rw [hxo]; exact hov2
                      · exact hcl_fals x hx hxo
                    · -- ov != 2 => if ov == 0 assign & continue
                      have hov_ne2 : ksW.vals[other.toNat]? ≠ some 2#32 := fun h2 => by
                        have hhc : ¬ksW.vals[(ksW.arena[((ksW.clOff[w0 % 2 ^ 32 / 2]?.getD
                            0#32).toNat + (BitVec.ofNat 32 w0 &&& 1#32 ^^^ 1#32).toNat) %
                            2 ^ 32]?.getD 0#32).toNat]?.getD 0#32 = 2#32 := ‹_›
                        rw [hother_hc_eq] at hhc
                        exact hhc (by rw [h2]; rfl)
                      have hov0 : ksK.vals[other.toNat]? = some 0#32 := by
                        dsimp only [ksK, K6State.putArr]
                        rcases hinvW.assign.vals_dom other.toNat hother_nv with h0 | h1 | h2
                        · have hvl : other.toNat < ksW.vals.length := by
                            rw [hshW.vals_len]; exact hother_mv2
                          rw [List.getElem?_eq_getElem hvl, Option.getD_some] at h0
                          rw [List.getElem?_eq_getElem hvl, h0]
                        · exact absurd (by
                            have hvl : other.toNat < ksW.vals.length := by
                              rw [hshW.vals_len]; exact hother_mv2
                            rw [List.getElem?_eq_getElem hvl, Option.getD_some] at h1
                            rw [List.getElem?_eq_getElem hvl, h1]) hoth_ne1
                        · exact absurd (by
                            have hvl : other.toNat < ksW.vals.length := by
                              rw [hshW.vals_len]; exact hother_mv2
                            rw [List.getElem?_eq_getElem hvl, Option.getD_some] at h2
                            rw [List.getElem?_eq_getElem hvl, h2]) hov_ne2
                      have hoth_memK : other.toNat ∈ k6ClauseLits ksK (w0 / 2) := by
                        dsimp only [ksK]; exact hot_mem
                      have hte_ltK := k6_trl_end_lt_of_unassigned hinvK.shapes hnvW hinvK.assign
                        hother_nv (by dsimp only [K6State.putArr]
                                      dsimp only [ksK, K6State.putArr] at hov0; rw [hov0]; rfl)
                      obtain ⟨hinvF, hsyncF⟩ := k6AssignStep_preserves_inv hinvK hsyncW hother_nv
                        hov0
                        (fun hl0 => k6_unit_of_falsified hwf_c.2.2.2 fun x hx hne =>
                          (k6_falsified_lvl0_entails hinvK hl0 (hwf_c.2.2.1 x hx)
                            (hcl_fals x hx hne)).2)
                        (fun _ hrs => absurd hrs hcid_ne_ff)
                        (Or.inr ⟨by rw [hw_div2]; exact hcid_lt,
                          by rw [hw_div2]; exact hoth_memK,
                          fun x hx hne => by
                            rw [hw_div2] at hx
                            exact k6_falsified_to_trail hinvK.assign hsyncW (hwf_c.2.2.1 x hx)
                              (hcl_fals x hx hne)⟩)
                      have hfr_kf := k6PropAssign_frame hinvK hother_nv hov0 hcid_ne_ff
                      let ksF := k6AssignStep ksK other (BitVec.ofNat 32 w0 >>> (1 : Nat))
                      have hmK : (K6MemA L kPtr ksK ⋆ R) m := by
                        refine Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) m) ?_) ‹_›
                        dsimp only [ksK]; k6_ext <;> (first | rfl | {
                          try rw [hw_tn]
                          rw [hother_bv_eq] })
                      refine wp_join0 (fun mF => (K6MemA L kPtr ksF ⋆ R) mF) ?_ ?_
                      · intro Jf mF hmF
                        have hskipF : K6WChainCursor ksF (lit ^^^ 1#32).toNat chW (done ++ [w0])
                            todo' (BitVec.ofNat 32 w0) (ksW.wnext[w0]?.getD 0#32) :=
                          ⟨hwcK.len_eq, hwcK.nodup, hwcK.chain_l, hwcK.chains_wc, hwcK.chains_bnd,
                           hwcK.tail_wc, hwcK.prev_rel⟩
                        c0_hsteps!; rw [hw_tn]
                        refine ihW (ticks + 1#64, visits + 1#64, BitVec.ofNat 32 w0,
                            ksF.wnext[w0]?.getD 0#32, done ++ [w0], todo', ksF, chW) mF (by simp)
                          ⟨hskipF, hinvF, hsyncF, hfrK.trans hfr_kf, hw_pr,
                           Nat.lt_of_lt_of_le hw_te hfr_kf.te_ge,
                           (hfr_kf.old_trl pO.toNat hw_te).1.trans hw_lit, hw_mv, hmF⟩
                      · intro Jf hJf
                        c0_hsplit
                        · c0_hsteps_nogrp
                          k6_call hAssign
                          refine ⟨L, ksK, R, hinvK.shapes, hmvK, by omega,
                            Nat.lt_of_lt_of_le hte_ltK hnvW, (k6MemA_to_mem hmK).2,
                            fun mF hmF => ?_⟩
                          rw [hother_bv_eq] at hmF
                          exact hJf mF (k6Mem_to_amem hinvF.shapes hmF)
                        · exfalso
                          have hhc : ¬ksW.vals[(ksW.arena[((ksW.clOff[w0 % 2 ^ 32 / 2]?.getD
                              0#32).toNat + (BitVec.ofNat 32 w0 &&& 1#32 ^^^ 1#32).toNat) %
                              2 ^ 32]?.getD 0#32).toNat]?.getD 0#32 = 0#32 := ‹_›
                          rw [hother_hc_eq] at hhc
                          dsimp only [ksK, K6State.putArr] at hov0
                          exact hhc (by rw [hov0]; rfl)
                · intro B L2 r m2 hB ih2 ⟨hm2, hr_le, hr2, hr_fals⟩
                  subst m2
                  dsimp only at hr_le hr2 hr_fals ⊢
                  c0_hsplit
                  · have hr_lt : r.toNat < sz.toNat := by
                      have hc0 : r.toNat < (ksW.clSz[w0 % 2 ^ 32 / 2]?.getD 0#32).toNat := ‹_›
                      rw [hw_mod32] at hc0; exact hc0
                    obtain ⟨hr_cap, hr_lit⟩ := har_ok r.toNat hr_lt
                    have hr_off_eq :
                        (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32 +
                          r).toNat = off.toNat + r.toNat := by
                      rw [hw_sh1]; unfold off; unfold dimacsBound at hac_b
                      change k6ClauseOff ksW (w0 / 2) + r.toNat < L.acap at hr_cap
                      unfold k6ClauseOff at hr_cap; bv_omega
                    have hr_ar :
                        (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32 +
                          r).toNat < szAr L := by
                      unfold szAr; rw [hr_off_eq]; exact hr_cap
                    have hcand_mv2 :
                        (ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD
                          0#32 + r).toNat]?.getD 0#32).toNat < sz2V L := by
                      rw [hr_off_eq]; dsimp only [off]
                      change (ksW.arena[k6ClauseOff ksW (w0 / 2) + r.toNat]?.getD 0#32).toNat <
                        sz2V L
                      unfold sz2V; omega
                    have hr1_wrap : (r + 1#32).toNat = r.toNat + 1 := by
                      have hsz_bd : sz.toNat < 2 ^ 28 := by
                        have := hclW.alen_le; unfold dimacsBound at hac_b
                        change k6ClauseSize ksW (w0 / 2) < 2 ^ 28; omega
                      bv_omega
                    c0_hsteps_nogrp
                    c0_hsplit
                    · have hc_ne2 :
                          ksW.vals[(ksW.arena[off.toNat + r.toNat]?.getD 0#32).toNat]? ≠
                          some 2#32 := fun heq => by
                        have hc0 : ksW.vals[(ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>>
                            (1 : Nat)).toNat]?.getD 0#32 + r).toNat]?.getD 0#32).toNat]?.getD
                            0#32 ≠ 2#32 := ‹_›
                        rw [hr_off_eq, heq, Option.getD_some] at hc0; exact hc0 rfl
                      c0_hsteps!
                      rw [hr_off_eq]
                      exact hB (r, r, ksW.arena[off.toNat + r.toNat]?.getD 0#32) mW
                        ⟨rfl, Or.inr ⟨hr2, hr_lt, rfl, hc_ne2⟩⟩
                    · have hc_eq2 :
                          ksW.vals[(ksW.arena[off.toNat + r.toNat]?.getD 0#32).toNat]? =
                          some 2#32 := by
                        have hc0 : ksW.vals[(ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>>
                            (1 : Nat)).toNat]?.getD 0#32 + r).toNat]?.getD 0#32).toNat]?.getD
                            0#32 = 2#32 := ‹_›
                        rw [hr_off_eq] at hc0
                        have hvl :
                            (ksW.arena[off.toNat + r.toNat]?.getD 0#32).toNat <
                            ksW.vals.length := by
                          rw [hshW.vals_len]; change (ksW.arena[k6ClauseOff ksW (w0 / 2) +
                            r.toNat]?.getD 0#32).toNat < 2 * L.maxV; omega
                        rw [List.getElem?_eq_getElem hvl, Option.getD_some] at hc0
                        rw [List.getElem?_eq_getElem hvl, hc0]
                      c0_hsteps!
                      refine ih2 (r + 1#32) mW (by rw [hr1_wrap]; omega)
                        ⟨rfl, by rw [hr1_wrap]; omega, by rw [hr1_wrap]; omega,
                          fun q hq2 hqr => ?_⟩
                      rw [hr1_wrap] at hqr
                      by_cases hqe : q = r.toNat
                      · subst hqe; exact hc_eq2
                      · exact hr_fals q hq2 (by omega)
                  · have hr_eq : r.toNat = sz.toNat := by
                      have hge : ¬ r.toNat < (ksW.clSz[(BitVec.ofNat 32 w0 >>>
                          (1 : Nat)).toNat]?.getD 0#32).toNat := ‹_›
                      rw [hw_sh1] at hge; dsimp only [sz] at hr_le ⊢; omega
                    c0_hsteps!
                    exact hB (r, 0xFFFFFFFF#32, 0#32) mW
                      ⟨rfl, Or.inl ⟨rfl, fun q hq2 hqsz => hr_fals q hq2 (by omega)⟩⟩
                · intro B L2 _ hL2
                  c0_hsteps!
                  exact hL2 2#32 mW ⟨rfl, hsz_ge, le_refl _, fun _ _ hq => by
                    rw [show (2#32 : BitVec 32).toNat = 2 from rfl] at hq; omega⟩
        · -- inner loop done => next outer iteration
          c0_hsteps!
          exact ihO (ticks + (visits >>> 7#64) + 1#64, ksW) mW (by
            have h1 := hinvO.assign.trl_end_le
            have h2 : ksO.nv.toNat = ks0.nv.toNat := congrArg BitVec.toNat hfrO.pres.nv
            dsimp only; dsimp only [pO] at hw_pr; omega) ⟨hinvW, hsyncW, hfrW, hmW⟩
    · -- outer loop done => add_ticks & return 0xFFFFFFFF
      have hpr_eq : ksO.prop = ksO.trl_end :=
        BitVec.eq_of_toNat_eq (by have := hinvO.assign.prop_le; bv_omega)
      c0_hsteps_nogrp
      k6_call hAddTicks
      refine ⟨L, ksO, R, hinvO.shapes, (k6MemA_to_mem hmO).2, fun tk' m' hm' => ?_⟩
      have hinvF := k6AddTicks_preserves_inv hinvO tk'
      have hsyncF : K6TrailSynced (ksO.putHdr .ticks tk') := hsyncO
      have hfrF : K6PropFrame ks0 (ksO.putHdr .ticks tk') :=
        hfrO.cast rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      c0_hsteps!
      exact hret 0xFFFFFFFF#32 (ksO.putHdr .ticks tk') m' hinvF hsyncF hfrF (fun _ => hpr_eq)
        (fun h => absurd rfl h) hm'

end LeanQbe.T.Examples.Kissat.FullM6Sweep
