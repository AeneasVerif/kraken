/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Kitten.WpBtFlip

/-!
# Step-13 `Func.wp` Proof for `full_k512_add_live_m6` (`14/14`, `Kissat.Proof.Kitten.WpAddLive`)

Certifies `full_k512_add_live_m6_wp` (`step13K6AddLiveSpec`) (`K6TailEq`-preserving).
Zero legacy `Full*` imports; zero `@[expose]` on theorems/lemmas; every decl `<= 450` LOC.
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

/-! ## 1. Add-Live Frame Bundle & Binary-Clause Facts -/

private structure K6LiveInv (L : K6Layout) (P : (Nat → Bool) → Prop)
    (ks0 ks : K6State) : Prop where
  inv : K6Inv L P ks
  sync : K6TrailSynced ks
  nv : ks.nv = ks0.nv
  tail : K6TailEq L ks0 ks
  nassump : ks.nassump = ks0.nassump
  assump : ks.assump = ks0.assump
  neq : ks.neq = ks0.neq

private theorem K6LiveInv.setStatus {L : K6Layout} {P : (Nat → Bool) → Prop} {ks0 ks : K6State}
    (h : K6LiveInv L P ks0 ks) (st : BitVec 32) : K6LiveInv L P ks0 (ks.putHdr .status st) :=
  ⟨k6SetStatus_preserves_inv h.inv st, k6TrailSynced_cast h.sync,
   by k6_field; exact h.nv,
   k6TailEq_trans h.tail (k6TailEq_of_putHdr_ne_nv (f := .status) (by decide) st),
   by k6_field; exact h.nassump, by k6_field; exact h.assump, by k6_field; exact h.neq⟩

private theorem K6LiveInv.setInconsStatus {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks0 ks : K6State} (h : K6LiveInv L P ks0 ks) (hunsat : ∀ β, ¬ P β) :
    K6LiveInv L P ks0 ((ks.putHdr .incons 1#32).putHdr .status 20#32) :=
  (K6LiveInv.mk (k6SetIncons_preserves_inv h.inv hunsat) (k6TrailSynced_cast h.sync) h.nv
    (k6TailEq_trans h.tail (k6TailEq_of_putHdr_ne_nv (f := .incons) (by decide) 1#32))
    h.nassump h.assump h.neq).setStatus 20#32

private theorem K6LiveInv.ofProp {L : K6Layout} {P : (Nat → Bool) → Prop} {ks0 ksW ksP : K6State}
    (hW : K6LiveInv L P ks0 ksW) (hinvP : K6Inv L P ksP) (hsyncP : K6TrailSynced ksP)
    (hpp : K6PropPreserved ksW ksP) (htlP : K6TailEq L ksW ksP) : K6LiveInv L P ks0 ksP :=
  ⟨hinvP, hsyncP, hpp.nv.trans hW.nv, k6TailEq_trans hW.tail htlP,
   hpp.nassump.trans hW.nassump, hpp.assump.trans hW.assump, hpp.neq.trans hW.neq⟩

private theorem k6_add_live_finish_post {c : FullCfg} {s : FullState} {P : (Nat → Bool) → Prop}
    {L : K6Layout} {R : Mem 64 → Prop} {Q : Post []} (hlen : s.LengthsOk c)
    (hL_len : L.scrLen = c.scratch_cap) (hkb_le : L.k6Base ≤ s.scratch.scratch_buf.length)
    (hQ : ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      let ks0 := k6StateOfScratch L s.scratch.scratch_buf; let ks' := k6StateOfScratch L scr'
      s'.LengthsOk c → (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K6Inv L P ks' → K6TrailSynced ks' → ks'.nv = ks0.nv → K6TailEq L ks0 ks' →
      ks'.nassump = ks0.nassump → k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf →
      ks'.neq = ks0.neq → (FullMem c s' ⋆ R) m' → Q () m') :
    ∀ {ks' : K6State} {m' : Mem 64},
      K6LiveInv L P (k6StateOfScratch L s.scratch.scratch_buf) ks' →
      (K6Mem L (L.kPtr c.pScratchBuf) ks' ⋆ (FullK6Frame c L s ⋆ R)) m' → Q () m' := by
  intro ks' m' h hm'
  have hmJ := fullMem_join_k6 (c := c) (L := L) (s := s) (ks' := ks') (R := R) (m' := m')
    hkb_le h.inv.shapes (sep_ac hm')
  let scr' := s.scratch.scratch_buf.take L.k6Base ++ ks'.toSlab
  have htk : (s.scratch.scratch_buf.take L.k6Base).length = L.k6Base :=
    List.length_take_of_le hkb_le
  have hscr'_len : scr'.length = c.scratch_cap := by
    simp only [scr', List.length_append, htk, K6State.toSlab_length h.inv.shapes, ← hL_len]
    unfold K6Layout.scrLen K6Layout.k6Base K6Layout.k6Fixed; omega
  have hpre : ∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]? := fun i hi => by
    rw [List.getElem?_append_left (by rw [htk]; exact hi), List.getElem?_take_of_lt hi]
  have hof : k6StateOfScratch L scr' = ks' := by
    unfold k6StateOfScratch; rw [k6_slab_drop_exact _ ks'.toSlab htk]
    exact K6State.ofSlab_toSlab h.inv.shapes
  exact hQ scr' m' (k6_fullState_lengthsOk_scratch hlen hscr'_len) hpre
    (hof ▸ h.inv) (hof ▸ h.sync) (hof ▸ h.nv) (hof ▸ h.tail) (hof ▸ h.nassump)
    (by unfold k6AssumpLitsS k6AssumpLits; rw [hof, h.nassump, h.assump])
    (hof ▸ h.neq) hmJ

private theorem k6_add_live_bin_facts {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks0 ks1 stM ks2 : K6State} {a b : BitVec 32}
    (hstM : stM = (((({ ks1 with
        arena := (ks1.arena.set ks1.alen.toNat a).set (ks1.alen.toNat + 1) b } :
      K6State).putHdr .alen (ks1.alen + 2#32)).putArr .clOff ks1.nc.toNat ks1.alen).putArr
      .clSz ks1.nc.toNat 2#32).putHdr .nc (ks1.nc + 1#32))
    (hks2 : ks2 = k6WatchStep stM ks1.nc a b) (hL1 : K6LiveInv L P ks0 ks1) (hlvl1 : ks1.lvl = 0#32)
    (ha_lt1 : a.toNat < 2 * ks1.nv.toNat) (hb_lt1 : b.toNat < 2 * ks1.nv.toNat)
    (hnc_lt : ks1.nc.toNat < L.maxCl) (hoff_fit : ks1.alen.toNat + 2 ≤ L.acap)
    (har_len : ((ks1.arena.set ks1.alen.toNat a).set (ks1.alen.toNat + 1) b).length = L.acap)
    (hent_ab : SemEntails P [a.toNat, b.toNat])
    (hsub : ∀ j < 2, ([a, b][j]?.getD 0#32).toNat < 2 * ks1.nv.toNat) :
    stM.ShapesOk L ∧ stM.max_v = L.mv32 ∧ K6LiveInv L P ks0 ks2 ∧ ks2.lvl = 0#32 ∧
    ks2.nv.toNat ≤ L.maxV ∧ ks2.max_v = L.mv32 ∧ a.toNat < 2 * ks2.nv.toNat ∧
    b.toNat < 2 * ks2.nv.toNat ∧ k6ClauseLits ks2 ks1.nc.toNat = [a.toNat, b.toNat] ∧
    ks1.nc.toNat < ks2.nc.toNat := by
  have hac_b := L.hacap; have hm_b := L.hmaxV
  have hsh_stM : stM.ShapesOk L := by
    have h1 : ({ ks1 with
        arena := (ks1.arena.set ks1.alen.toNat a).set (ks1.alen.toNat + 1) b } :
      K6State).ShapesOk L := { hL1.inv.shapes with arena_len := har_len }
    rw [hstM]; exact (((h1.putHdr .alen _).putArr .clOff _ _).putArr .clSz _ _).putHdr .nc _
  have hpres := k6AddClause_ge2_preserves (xs := [a, b]) (sz := 2#32)
    (ar := (ks1.arena.set ks1.alen.toNat a).set (ks1.alen.toNat + 1) b) hL1.inv hL1.sync
    hnc_lt (by decide) (by decide) (by simp) hoff_fit har_len
    (fun j hj => by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
    (fun j hj => by
      have hj2 : j < 2 := by change j < (2#32 : BitVec 32).toNat at hj; simp at hj; exact hj
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · rw [List.getElem?_set_ne (by omega), Nat.add_zero,
          List.getElem?_set_self (by rw [hL1.inv.shapes.arena_len]; omega)]; rfl
      · rw [List.getElem?_set_self (by simp [hL1.inv.shapes.arena_len]; omega)]; rfl)
    hsub (by simpa using hent_ab)
  dsimp only at hpres
  rw [← hstM, show ([a, b][0]'(by simp)) = a from rfl,
    show ([a, b][1]'(by simp)) = b from rfl, ← hks2] at hpres
  have hstM_nv : stM.nv = ks1.nv := by rw [hstM]; k6_field
  have hstM_mv : stM.max_v = L.mv32 := by rw [hstM]; k6_field; exact hL1.inv.clauses.max_v_eq
  have hneq2 : ks2.neq = ks0.neq := by
    have : ks2.neq = stM.neq := by rw [hks2]; dsimp only [k6WatchStep, k6WatchStep0]
    rw [this, hstM]; k6_field; exact hL1.neq
  have htl2 : K6TailEq L ks0 ks2 := by
    rw [hks2]
    exact k6TailEq_trans (k6TailEq_trans hL1.tail
        (by rw [hstM]; exact ⟨rfl, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩))
      (k6TailEq_of_k6WatchStep ks1.nc a b (by rw [hstM_nv]; exact ha_lt1)
        (by rw [hstM_nv]; exact hb_lt1))
  have hcl_nc : k6ClauseLits ks2 ks1.nc.toNat = [a.toNat, b.toNat] := by
    have hoff : k6ClauseOff ks2 ks1.nc.toNat = ks1.alen.toNat := by
      unfold k6ClauseOff; rw [hks2]; dsimp only [k6WatchStep, k6WatchStep0]; rw [hstM]; k6_field
      rw [List.getElem?_set_self (by rw [hL1.inv.shapes.clOff_len]; exact hnc_lt), Option.getD_some]
    have hsz : k6ClauseSize ks2 ks1.nc.toNat = 2 := by
      unfold k6ClauseSize; rw [hks2]; dsimp only [k6WatchStep, k6WatchStep0]; rw [hstM]; k6_field
      rw [List.getElem?_set_self (by rw [hL1.inv.shapes.clSz_len]; exact hnc_lt), Option.getD_some]
      rfl
    have har_eq : ks2.arena = (ks1.arena.set ks1.alen.toNat a).set (ks1.alen.toNat + 1) b := by
      rw [hks2]; dsimp only [k6WatchStep, k6WatchStep0]; rw [hstM]; k6_field
    unfold k6ClauseLits; rw [hoff, hsz, har_eq]
    exact k6_arena_take2 hL1.inv.shapes.arena_len (by omega)
  have hnc_lt2 : ks1.nc.toNat < ks2.nc.toNat := by
    have : ks2.nc = ks1.nc + 1#32 := by
      rw [hks2]; dsimp only [k6WatchStep, k6WatchStep0]; rw [hstM]; k6_field
    rw [this]; unfold K6Layout.maxCl at hnc_lt; bv_omega
  exact ⟨hsh_stM, hstM_mv,
    ⟨hpres.1, hpres.2.1, hpres.2.2.2.1.trans hL1.nv, htl2,
     hpres.2.2.2.2.1.trans hL1.nassump, hpres.2.2.2.2.2.1.trans hL1.assump, hneq2⟩,
    hpres.2.2.1.trans hlvl1, hpres.1.clauses.nv_le, hpres.1.clauses.max_v_eq,
    by rw [hpres.2.2.2.1]; exact ha_lt1, by rw [hpres.2.2.2.1]; exact hb_lt1, hcl_nc, hnc_lt2⟩

/-! ## 2. `full_k512_add_live_m6_wp` (`14/14`) -/

open Lean Elab Tactic in
local elab "live_prop " ksW:term:max hlW:term:max hmAW:term:max : tactic => do
  let runLiveProp := mkIdent `runLiveProp
  let finishR := mkIdent `finishR
  let hProp := mkIdent `hProp
  evalTactic (← `(tactic| (
    refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
    k6_call $hProp
    exact $runLiveProp
      (fun hLP hmAP => by c0_hsteps!; exact $finishR hLP (k6MemA_to_mem hmAP).2)
      (fun hLP hlP _ h1 h2 hmAP => by
        c0_hsteps!
        exact $finishR (hLP.setInconsStatus (k6_conflict_unsat_lvl0 hLP.inv hlP h1 h2))
          (k6MemA_to_mem ‹_›).2)
      $ksW $hlW $hmAW)))

/-- `14/14`: Parametric `Func.wp` proof for `full_k512_add_live_m6` (`step13K6AddLiveSpec`). -/
theorem full_k512_add_live_m6_wp (Γ : Env)
    (hMaxV : Γ.Has "full_m6_max_v" m6MaxVSpec)
    (hBt : Γ.Has "full_k6_backtrack" step13K6BacktrackSpec)
    (hAssign : Γ.Has "full_k6_assign" k6AssignSpec)
    (hWatch : Γ.Has "full_k6_watch" k6WatchSpec)
    (hProp : Γ.Has "full_k6_propagate" step13K6PropagateSpec) :
    ∀ args m Q X, step13K6AddLiveSpec args m Q X →
      Func.wp Γ full_k512_add_live_m6_body args m Q X := by
  rintro ⟨hPtr, a, b, ⟨⟩⟩ m Q X ⟨c, s, P, L, R, rfl, hlen, hL_len, hL_mv, hinv0, ha_lt,
    hb_unit, hb_bin, hm, hQ⟩
  let scr := s.scratch.scratch_buf; let ks0 := k6StateOfScratch L scr
  have hm_b := L.hmaxV; have hac_b := L.hacap
  have hscr_len : scr.length = L.scrLen := hlen.scratch_ok.scratch_buf_len.trans hL_len.symm
  have hkb_le : L.k6Base ≤ scr.length := by rw [hscr_len]; unfold K6Layout.scrLen; omega
  let kPtr := L.kPtr c.pScratchBuf
  have hmF0 : (K6Mem L kPtr ks0 ⋆ (FullK6Frame c L s ⋆ R)) m := by
    rw [fullMem_eq_k6Frame hscr_len] at hm; exact sep_ac hm
  clear hm
  have hsc_lt : c.scratch_cap < 2 ^ 64 := Nat.lt_trans c.hscr (by unfold dimacsBound; decide)
  c0_hsteps_nogrp; refine k6_maxV_call_step hMaxV hsc_lt ?_
  have hmv32_eq := k6_flip_mv32_eq hL_mv
  c0_hsplit
  · exfalso; have hmv0 : L.mv32 = 0#32 := by rw [← hmv32_eq]; exact ‹_›
    have h0 := congrArg BitVec.toNat hmv0; change (BitVec.ofNat 32 L.maxV).toNat = 0 at h0
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h0; omega
  · rw [hmv32_eq]
    c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
    rw [k6_ptr_base L c.pScratchBuf]
    obtain ⟨Rfr, hRfr⟩ : ∃ Rfr : Mem 64 → Prop, Rfr = (FullK6Frame c L s ⋆ R) := ⟨_, rfl⟩
    have hmA0 : (K6MemA L kPtr ks0 ⋆ Rfr) m := by rw [hRfr]; exact k6Mem_to_amem hinv0.shapes hmF0
    have finishR : ∀ {ks' : K6State} {m' : Mem 64},
        K6LiveInv L P ks0 ks' → (K6Mem L kPtr ks' ⋆ Rfr) m' → Q () m' :=
      fun h hm' => k6_add_live_finish_post hlen hL_len hkb_le hQ h (hRfr ▸ hm')
    clear hmF0
    refine wp_join_state0 (α := K6State)
      (fun ks1 m1 => K6LiveInv L P ks0 ks1 ∧ ks1.lvl = 0#32 ∧ (K6MemA L kPtr ks1 ⋆ Rfr) m1)
      ?_ ?_
    · intro J0 ks1 m1 ⟨hL1, hlvl1, hmA1⟩
      let runLiveProp :
          ∀ {ksW : K6State} {mW : Mem 64} {k : Tup Val [i32] → Expr Val Cont []},
          (∀ {ksP : K6State} {mP : Mem 64}, K6LiveInv L P ks0 ksP → (K6MemA L kPtr ksP ⋆ Rfr) mP →
            wp Γ Q X (k (0xFFFFFFFF#32, ())) mP) →
          (∀ {confl : BitVec 32} {ksP : K6State} {mP : Mem 64},
            K6LiveInv L P ks0 ksP → ksP.lvl = 0#32 → confl ≠ 0xFFFFFFFF#32 →
            confl.toNat < ksP.nc.toNat → (∀ l ∈ k6ClauseLits ksP confl.toNat,
              ksP.vals[l]? = some 2#32) →
            (K6MemA L kPtr ksP ⋆ Rfr) mP → wp Γ Q X (k (confl, ())) mP) →
          K6LiveInv L P ks0 ksW → ksW.lvl = 0#32 → (K6MemA L kPtr ksW ⋆ Rfr) mW →
          step13K6PropagateSpec (kPtr, ()) mW (fun r mP => wp Γ Q X (k r) mP) X :=
        fun hOk hBad hLW hlW hmAW =>
          ⟨L, P, _, Rfr, hLW.inv, hLW.sync, (k6MemA_to_mem hmAW).2,
            fun confl ksP mP hiP hsP hpp htlP _ _ _ _ hconfl hmP => by
              have hLP := hLW.ofProp hiP hsP hpp htlP
              have hmAP := k6Mem_to_amem hiP.shapes hmP
              by_cases hcf : confl = 0xFFFFFFFF#32
              · subst hcf; exact hOk hLP hmAP
              · exact hBad hLP (hpp.lvl.trans hlW) hcf (hconfl hcf).1 (hconfl hcf).2 hmAP⟩
      let runLiveAssign :
          ∀ {ksW : K6State} {mW : Mem 64} {lit rsn : BitVec 32}
            {k1 : Tup Val [] → Expr Val Cont []},
          (∀ {ksN : K6State} {mN : Mem 64}, K6LiveInv L P ks0 ksN → ksN.lvl = 0#32 →
            (K6MemA L kPtr ksN ⋆ Rfr) mN → wp Γ Q X (k1 ()) mN) →
          K6LiveInv L P ks0 ksW → ksW.lvl = 0#32 →
          lit.toNat < 2 * ksW.nv.toNat → ksW.vals[lit.toNat]? = some 0#32 →
          SemEntails P [lit.toNat] →
          (rsn = 0xFFFFFFFF#32 ∨ (rsn.toNat < ksW.nc.toNat ∧
            lit.toNat ∈ k6ClauseLits ksW rsn.toNat ∧
            ∀ x ∈ k6ClauseLits ksW rsn.toNat, x ≠ lit.toNat →
              ∃ j < ksW.trl_end.toNat, (ksW.trl[j]?.getD 0#32).toNat = x ^^^ 1)) →
          (K6MemA L kPtr ksW ⋆ Rfr) mW →
          k6AssignSpec (kPtr, lit, rsn, ()) mW (fun r mN => wp Γ Q X (k1 r) mN) X := by
        intro ksW mW lit rsn k1 hk1 hLW hlW hlit hun hent hrsn hmAW
        have hnvW_le := hLW.inv.clauses.nv_le
        have hte_lt := k6_trl_end_lt_of_unassigned hLW.inv.shapes hnvW_le hLW.inv.assign hlit
          (by simp [hun])
        obtain ⟨hinvN, hsyncN⟩ := k6AssignStep_preserves_inv hLW.inv hLW.sync hlit hun
          (fun _ => hent) (fun hpos => by rw [hlW] at hpos; simp at hpos) hrsn
        have hLN : K6LiveInv L P ks0 (k6AssignStep ksW lit rsn) :=
          ⟨hinvN, hsyncN, hLW.nv,
           k6TailEq_trans hLW.tail (k6TailEq_of_k6AssignStep (L := L) lit rsn hlit),
           hLW.nassump, hLW.assump, hLW.neq⟩
        exact ⟨L, ksW, Rfr, hLW.inv.shapes, hLW.inv.clauses.max_v_eq, (by omega),
          Nat.lt_of_lt_of_le hte_lt hnvW_le, (k6MemA_to_mem hmAW).2,
          fun mN hmN => hk1 hLN hlW (k6Mem_to_amem hinvN.shapes hmN)⟩
      have hnv1 := hL1.inv.clauses.nv_le; have hmv1 : ks1.max_v = L.mv32 := hL1.inv.clauses.max_v_eq
      have ha_lt1 : a.toNat < 2 * ks1.nv.toNat := by rw [hL1.nv]; exact ha_lt
      have ha_mv2 : a.toNat < sz2V L := by unfold sz2V; omega
      c0_hsplit
      · c0_hsteps!; exact finishR (hL1.setStatus 20#32) (k6MemA_to_mem hm).2
      · c0_hsplit
        · have hent_a := hb_unit ‹_›
          try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
          c0_hsplit
          · have hfals := k6_vals_some hL1.inv.shapes ha_mv2 ‹_›
            have hunsat : ∀ β, ¬ P β := SemEntails.unsat_of_falsified hent_a fun x hx => by
              simp at hx; subst hx; exact (k6_falsified_lvl0_entails hL1.inv hlvl1 ha_lt1 hfals).2
            c0_hsteps!; exact finishR (hL1.setInconsStatus hunsat) (k6MemA_to_mem hm).2
          · refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
            c0_hsplit
            · have hun0 := k6_vals_some hL1.inv.shapes ha_mv2 ‹_›
              k6_call hAssign
              refine runLiveAssign (fun hLN hlN hmAN => ?_) hL1 hlvl1 ha_lt1 hun0 hent_a
                (Or.inl rfl) hmA1
              c0_hsteps_nogrp; live_prop hLN hlN hmAN
            · c0_hsteps_nogrp; live_prop hL1 hlvl1 hmA1
        · obtain ⟨hb_lt0, hent_ab⟩ := hb_bin ‹_›
          have hb_lt1 : b.toNat < 2 * ks1.nv.toNat := by rw [hL1.nv]; exact hb_lt0
          have hb_mv2 : b.toNat < sz2V L := by unfold sz2V; omega
          have hca1 : ks1.acap.toNat = L.acap := by
            unfold dimacsBound at hac_b
            rw [hL1.inv.clauses.acap_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have hmc1 : ks1.max_cl.toNat = L.maxCl := by
            rw [hL1.inv.clauses.max_cl_eq]; unfold K6Layout.maxCl
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          c0_hsplit
          · c0_hsteps!; exact finishR hL1 (k6MemA_to_mem hmA1).2
          · c0_hsplit
            · c0_hsteps!; exact finishR hL1 (k6MemA_to_mem hmA1).2
            · have hnc_lt : ks1.nc.toNat < L.maxCl := by rw [← hmc1]; bv_omega
              have hal_ks : ks1.alen.toNat ≤ ks1.acap.toNat := by
                rw [hca1]; exact hL1.inv.clauses.alen_le
              have hcap_lt : ks1.acap.toNat < 2 ^ 28 := by
                rw [hca1]; unfold dimacsBound at hac_b; omega
              have hoff_fit : ks1.alen.toNat + 2 ≤ L.acap := by rw [← hca1]; bv_omega
              have hoff0_ar : ks1.alen.toNat < szAr L := by unfold szAr; omega
              have hoff1_ar : (ks1.alen + 1#32).toNat < szAr L := by
                unfold szAr dimacsBound at *; bv_omega
              have h1_eq : (ks1.alen + (1 : BitVec 32)).toNat = ks1.alen.toNat + 1 := by
                unfold dimacsBound at hac_b; bv_omega
              have har_len :
                  ((ks1.arena.set ks1.alen.toNat a).set (ks1.alen.toNat + 1) b).length = L.acap :=
                by simp [hL1.inv.shapes.arena_len]
              obtain ⟨stM, hstM⟩ : ∃ x : K6State, x = (((({ ks1 with
                  arena := (ks1.arena.set ks1.alen.toNat a).set (ks1.alen.toNat + 1) b } :
                K6State).putHdr .alen (ks1.alen + 2#32)).putArr .clOff ks1.nc.toNat ks1.alen).putArr
                .clSz ks1.nc.toNat 2#32).putHdr .nc (ks1.nc + 1#32) := ⟨_, rfl⟩
              obtain ⟨ks2, hks2⟩ : ∃ x : K6State, x = k6WatchStep stM ks1.nc a b := ⟨_, rfl⟩
              obtain ⟨hsh_stM, hmv_stM, hL2, hlvl2, hnv2, hmv2, ha_lt2, hb_lt2, hcl_nc, hnc_lt2⟩ :=
                k6_add_live_bin_facts hstM hks2 hL1 hlvl1 ha_lt1 hb_lt1 hnc_lt hoff_fit
                  har_len hent_ab (fun j hj => by
                    have hj2 : j < 2 := by
                      change j < (2#32 : BitVec 32).toNat at hj; simp at hj; exact hj
                    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> simpa)
              c0_hsteps_nogrp; obtain ⟨_, hmM⟩ := k6MemA_to_mem hm
              have hmM_eq : (K6Mem L kPtr stM ⋆ Rfr) m := by
                refine Eq.mp (congrArg (fun x => (K6Mem L kPtr x ⋆ Rfr) _) ?_) hmM
                rw [hstM]; k6_ext <;> (try rfl) <;> rw [h1_eq]
              k6_call hWatch
              refine ⟨L, stM, Rfr, hsh_stM, hmv_stM, hnc_lt, (by omega), (by omega), hmM_eq,
                fun m2 hm2 => ?_⟩
              rw [← hks2] at hm2
              have hmA2 : (K6MemA L kPtr ks2 ⋆ Rfr) m2 := k6Mem_to_amem hL2.inv.shapes hm2
              clear hm2 hmM_eq hstM hks2
              c0_hsteps_nogrp; refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
              c0_hsplit
              · have hfals_a := k6_vals_some hL2.inv.shapes ha_mv2 ‹_›
                obtain ⟨⟨ja, hja, hja_eq⟩, hent_na⟩ :=
                  k6_falsified_lvl0_entails hL2.inv hlvl2 ha_lt2 hfals_a
                c0_hsplit
                · have hfals_b := k6_vals_some hL2.inv.shapes hb_mv2 ‹_›
                  have hent_nb := (k6_falsified_lvl0_entails hL2.inv hlvl2 hb_lt2 hfals_b).2
                  have hunsat : ∀ β, ¬ P β := SemEntails.unsat_of_falsified hent_ab fun x hx => by
                    simp at hx; rcases hx with rfl | rfl <;> assumption
                  c0_hsteps!
                  exact finishR (hL2.setInconsStatus hunsat)
                    (k6MemA_to_mem ‹(K6MemA L kPtr _ ⋆ Rfr) _›).2
                · refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                  c0_hsplit
                  · have hun_b := k6_vals_some hL2.inv.shapes hb_mv2 ‹_›
                    have hent_b : SemEntails P [b.toNat] :=
                      SemEntails.unit_of_falsified hent_ab fun x hx hne => by
                        simp at hx; rcases hx with rfl | rfl
                        · exact hent_na
                        · exact absurd rfl hne
                    k6_call hAssign
                    refine runLiveAssign (fun hLN hlN hmAN => ?_) hL2 hlvl2 hb_lt2 hun_b hent_b
                      (Or.inr ⟨hnc_lt2, by rw [hcl_nc]; simp, fun x hx hne => by
                        rw [hcl_nc] at hx; simp at hx; rcases hx with rfl | rfl
                        · exact ⟨ja, hja, hja_eq⟩
                        · exact absurd rfl hne⟩) hmA2
                    c0_hsteps_nogrp; live_prop hLN hlN hmAN
                  · c0_hsteps_nogrp; live_prop hL2 hlvl2 hmA2
              · refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                c0_hsplit
                · c0_hsplit
                  · have hfals_b := k6_vals_some hL2.inv.shapes hb_mv2 ‹_›
                    have hun_a := k6_vals_some hL2.inv.shapes ha_mv2 ‹_›
                    obtain ⟨⟨jb, hjb, hjb_eq⟩, hent_nb⟩ :=
                      k6_falsified_lvl0_entails hL2.inv hlvl2 hb_lt2 hfals_b
                    have hent_a : SemEntails P [a.toNat] :=
                      SemEntails.unit_of_falsified hent_ab fun x hx hne => by
                        simp at hx; rcases hx with rfl | rfl
                        · exact absurd rfl hne
                        · exact hent_nb
                    k6_call hAssign
                    refine runLiveAssign (fun hLN hlN hmAN => ?_) hL2 hlvl2 ha_lt2 hun_a hent_a
                      (Or.inr ⟨hnc_lt2, by rw [hcl_nc]; simp, fun x hx hne => by
                        rw [hcl_nc] at hx; simp at hx; rcases hx with rfl | rfl
                        · exact absurd rfl hne
                        · exact ⟨jb, hjb, hjb_eq⟩⟩) hmA2
                    c0_hsteps_nogrp; live_prop hLN hlN hmAN
                  · c0_hsteps_nogrp; live_prop hL2 hlvl2 hmA2
                · c0_hsteps_nogrp; live_prop hL2 hlvl2 hmA2
    · intro J0 hJ0
      refine LeanQbe.T.wp_unroll_group fun J1 hJ1 => ?_
      have hBt_ok : J1 () m := by
        refine hJ1 () m ?_
        k6_call hBt
        refine ⟨L, P, ks0, Rfr, hinv0, Or.inl rfl, (k6MemA_to_mem hmA0).2,
          fun ks1 m1 hinv1 hsync1 hlvl1 _ hbtp htl1 _ _ hm1 => ?_⟩
        have hmA1 := k6Mem_to_amem hinv1.shapes hm1; c0_hsteps!
        have hL1 : K6LiveInv L P ks0 (ks1.putHdr .status 0#32) :=
          (K6LiveInv.mk hinv1 hsync1 hbtp.nv htl1 hbtp.nassump hbtp.assump hbtp.neq).setStatus 0#32
        exact hJ0 _ _ ⟨hL1, by k6_field; exact hlvl1, ‹_›⟩
      c0_hsplit
      · refine head_wp_jump rfl rfl hBt_ok
      · c0_hsplit
        · refine head_wp_jump rfl rfl hBt_ok
        · have hlvl0 : ks0.lvl = 0#32 := by bv_omega
          c0_hsteps!
          exact hJ0 _ m ⟨⟨hinv0, k6_trailSynced_of_lvl0 hinv0 hlvl0, rfl,
            k6TailEq_refl L ks0, rfl, rfl, rfl⟩, hlvl0, hmA0⟩

end LeanQbe.T.Examples.Kissat.Proof.Kitten
end
