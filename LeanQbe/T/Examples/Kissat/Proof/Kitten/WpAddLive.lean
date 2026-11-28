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

/-! ## 1. Add-Live Finish & Binary-Clause Facts -/

private theorem k6_add_live_finish_post {c : FullCfg} {s : FullState} {P : (Nat → Bool) → Prop}
    {L : K6Layout} {R : Mem 64 → Prop} {Q : Post []} (hlen : s.LengthsOk c)
    (hL_len : L.scrLen = c.scratch_cap)
    (hkb_le : L.k6Base ≤ s.scratch.scratch_buf.length)
    (hQ : ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      let ks0 := k6StateOfScratch L s.scratch.scratch_buf; let ks' := k6StateOfScratch L scr'
      s'.LengthsOk c → (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K6Inv L P ks' → K6TrailSynced ks' → ks'.nv = ks0.nv → K6TailEq L ks0 ks' →
      ks'.nassump = ks0.nassump → k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf →
      ks'.neq = ks0.neq → (FullMem c s' ⋆ R) m' → Q () m') :
    let ks0 := k6StateOfScratch L s.scratch.scratch_buf
    ∀ {ks' : K6State} {m' : Mem 64},
      K6Inv L P ks' → K6TrailSynced ks' → ks'.nv = ks0.nv → K6TailEq L ks0 ks' →
      ks'.nassump = ks0.nassump → ks'.assump = ks0.assump → ks'.neq = ks0.neq →
      (K6Mem L (L.kPtr c.pScratchBuf) ks' ⋆ (FullK6Frame c L s ⋆ R)) m' → Q () m' := by
  intro ks0 ks' m' hinv' hsync' hnv' htail' hna' hass' hneq' hm'
  have hmJ := fullMem_join_k6 (c := c) (L := L) (s := s) (ks' := ks') (R := R) (m' := m')
    hkb_le hinv'.shapes (sep_ac hm')
  let scr' := s.scratch.scratch_buf.take L.k6Base ++ ks'.toSlab
  have htk_len : (s.scratch.scratch_buf.take L.k6Base).length = L.k6Base :=
    List.length_take_of_le hkb_le
  have hscr'_len : scr'.length = c.scratch_cap := by
    simp only [scr', List.length_append, htk_len, K6State.toSlab_length hinv'.shapes, ← hL_len]
    unfold K6Layout.scrLen K6Layout.k6Base K6Layout.k6Fixed; omega
  have hpre : ∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]? := fun i hi => by
    rw [List.getElem?_append_left (by rw [htk_len]; exact hi), List.getElem?_take_of_lt hi]
  have hof : k6StateOfScratch L scr' = ks' := by
    unfold k6StateOfScratch
    rw [k6_slab_drop_exact _ ks'.toSlab htk_len]
    exact K6State.ofSlab_toSlab hinv'.shapes
  exact hQ scr' m' (k6_fullState_lengthsOk_scratch hlen hscr'_len) hpre
    (by rw [hof]; exact hinv') (by rw [hof]; exact hsync') (by rw [hof]; exact hnv')
    (by rw [hof]; exact htail') (by rw [hof]; exact hna')
    (by unfold k6AssumpLitsS k6AssumpLits; rw [hof, hna', hass'])
    (by rw [hof]; exact hneq') hmJ

private theorem k6_add_live_vals_some {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    {l : Nat} {v : BitVec 32} (hinv : K6Inv L P ks) (hl : l < sz2V L)
    (hv : ks.vals[l]?.getD 0#32 = v) : ks.vals[l]? = some v := by
  have hvl : l < ks.vals.length := by rw [hinv.shapes.vals_len]; exact hl
  rw [List.getElem?_eq_getElem hvl, Option.getD_some] at hv
  rw [List.getElem?_eq_getElem hvl, hv]

private theorem k6_add_live_setStatus_pres {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks0 ks : K6State} (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks)
    (hnv : ks.nv = ks0.nv) (htl : K6TailEq L ks0 ks) (hna : ks.nassump = ks0.nassump)
    (hass : ks.assump = ks0.assump) (hneq : ks.neq = ks0.neq) (st : BitVec 32) :
    let ks' := ks.putHdr .status st
    K6Inv L P ks' ∧ K6TrailSynced ks' ∧ ks'.nv = ks0.nv ∧ K6TailEq L ks0 ks' ∧
    ks'.nassump = ks0.nassump ∧ ks'.assump = ks0.assump ∧ ks'.neq = ks0.neq :=
  ⟨k6SetStatus_preserves_inv hinv st, by unfold K6TrailSynced at *; k6_field; exact hsync,
   by k6_field; exact hnv,
   k6TailEq_trans htl (k6TailEq_of_putHdr_ne_nv (f := .status) (by decide) st),
   by k6_field; exact hna, by k6_field; exact hass, by k6_field; exact hneq⟩

private theorem k6_add_live_confl_finish {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks0 : K6State} {kPtr : BitVec 64} {Rfr : Mem 64 → Prop} {Q : Post []}
    (finishR : ∀ {ks' : K6State} {m' : Mem 64},
      K6Inv L P ks' → K6TrailSynced ks' → ks'.nv = ks0.nv → K6TailEq L ks0 ks' →
      ks'.nassump = ks0.nassump → ks'.assump = ks0.assump → ks'.neq = ks0.neq →
      (K6Mem L kPtr ks' ⋆ Rfr) m' → Q () m')
    {ksW ksP : K6State} {confl : BitVec 32} {mFin : Mem 64}
    (hlW : ksW.lvl = 0#32) (hnvW : ksW.nv = ks0.nv) (htlW : K6TailEq L ks0 ksW)
    (hnaW : ksW.nassump = ks0.nassump) (hassW : ksW.assump = ks0.assump) (hneqW : ksW.neq = ks0.neq)
    (hinvP : K6Inv L P ksP) (hsyncP : K6TrailSynced ksP) (hpp : K6PropPreserved ksW ksP)
    (htlP : K6TailEq L ksW ksP)
    (hcf : confl.toNat < ksP.nc.toNat ∧ ∀ l ∈ k6ClauseLits ksP confl.toNat,
      ksP.vals[l]? = some 2#32)
    (hmFin : (K6MemA L kPtr ((ksP.putHdr .incons 1#32).putHdr .status 20#32) ⋆ Rfr) mFin) :
    Q () mFin := by
  have hunsat := k6_conflict_unsat_lvl0 hinvP (hpp.lvl.trans hlW) hcf.1 hcf.2
  have htlI := k6TailEq_trans (k6TailEq_trans htlW htlP)
    (k6TailEq_of_putHdr_ne_nv (f := .incons) (by decide) 1#32)
  obtain ⟨hiS, hsS, hnS, htlS, hnaS, hasS, hnqS⟩ :=
    k6_add_live_setStatus_pres (k6SetIncons_preserves_inv hinvP hunsat)
      (by unfold K6TrailSynced at *; k6_field; exact hsyncP)
      (hpp.nv.trans hnvW) htlI (hpp.nassump.trans hnaW)
      (hpp.assump.trans hassW) (hpp.neq.trans hneqW) 20#32
  exact finishR hiS hsS hnS htlS hnaS hasS hnqS (k6MemA_to_mem hmFin).2

private theorem k6_add_live_bin_facts {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks0 ks1 stM ks2 : K6State} {a b : BitVec 32}
    (hstM : stM = (((({ ks1 with
        arena := (ks1.arena.set ks1.alen.toNat a).set (ks1.alen.toNat + 1) b } :
      K6State).putHdr .alen (ks1.alen + 2#32)).putArr .clOff ks1.nc.toNat ks1.alen).putArr
      .clSz ks1.nc.toNat 2#32).putHdr .nc (ks1.nc + 1#32))
    (hks2 : ks2 = k6WatchStep stM ks1.nc a b)
    (hinv1 : K6Inv L P ks1) (hlvl1 : ks1.lvl = 0#32) (hnv1_0 : ks1.nv = ks0.nv)
    (htl1_0 : K6TailEq L ks0 ks1) (hna1_0 : ks1.nassump = ks0.nassump)
    (hass1_0 : ks1.assump = ks0.assump) (hneq1_0 : ks1.neq = ks0.neq)
    (ha_lt1 : a.toNat < 2 * ks1.nv.toNat) (hb_lt1 : b.toNat < 2 * ks1.nv.toNat)
    (hnc_lt : ks1.nc.toNat < L.maxCl) (hoff_fit : ks1.alen.toNat + 2 ≤ L.acap)
    (har_len : ((ks1.arena.set ks1.alen.toNat a).set (ks1.alen.toNat + 1) b).length = L.acap)
    (hent_ab : SemEntails P [a.toNat, b.toNat])
    (hsub : ∀ j < 2, ([a, b][j]?.getD 0#32).toNat < 2 * ks1.nv.toNat)
    (hsync1 : K6TrailSynced ks1) :
    stM.ShapesOk L ∧ stM.max_v = L.mv32 ∧
    K6Inv L P ks2 ∧ K6TrailSynced ks2 ∧ ks2.lvl = 0#32 ∧ ks2.nv = ks0.nv ∧
    K6TailEq L ks0 ks2 ∧ ks2.nassump = ks0.nassump ∧ ks2.assump = ks0.assump ∧
    ks2.neq = ks0.neq ∧ ks2.nv.toNat ≤ L.maxV ∧ ks2.max_v = L.mv32 ∧
    a.toNat < 2 * ks2.nv.toNat ∧ b.toNat < 2 * ks2.nv.toNat ∧
    k6ClauseLits ks2 ks1.nc.toNat = [a.toNat, b.toNat] ∧ ks1.nc.toNat < ks2.nc.toNat := by
  have hac_b := L.hacap; have hm_b := L.hmaxV
  have hsh_stM : stM.ShapesOk L := by
    have h1 : ({ ks1 with
        arena := (ks1.arena.set ks1.alen.toNat a).set (ks1.alen.toNat + 1) b } :
      K6State).ShapesOk L := { hinv1.shapes with arena_len := har_len }
    rw [hstM]
    exact (((h1.putHdr .alen _).putArr .clOff _ _).putArr .clSz _ _).putHdr .nc _
  have htl_stM : K6TailEq L ks1 stM := by
    rw [hstM]; exact ⟨rfl, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  have hpres := k6AddClause_ge2_preserves (xs := [a, b]) (sz := 2#32)
    (ar := (ks1.arena.set ks1.alen.toNat a).set (ks1.alen.toNat + 1) b) hinv1 hsync1
    hnc_lt (by decide) (by decide) (by simp) hoff_fit har_len
    (fun j hj => by
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
    (fun j hj => by
      have hj2 : j < 2 := by change j < (2#32 : BitVec 32).toNat at hj; simp at hj; exact hj
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · rw [List.getElem?_set_ne (by omega), Nat.add_zero,
          List.getElem?_set_self (by rw [hinv1.shapes.arena_len]; omega)]; rfl
      · rw [List.getElem?_set_self (by simp [hinv1.shapes.arena_len]; omega)]; rfl)
    hsub (by simpa using hent_ab)
  dsimp only at hpres
  rw [← hstM] at hpres
  rw [show ([a, b][0]'(by simp)) = a from rfl,
    show ([a, b][1]'(by simp)) = b from rfl, ← hks2] at hpres
  have hinv2 := hpres.1; have hsync2 := hpres.2.1
  have hstM_nv : stM.nv = ks1.nv := by rw [hstM]; k6_field
  have hstM_mv : stM.max_v = L.mv32 := by rw [hstM]; k6_field; exact hinv1.clauses.max_v_eq
  have hneq2 : ks2.neq = ks0.neq := by
    have : ks2.neq = stM.neq := by rw [hks2]; dsimp only [k6WatchStep, k6WatchStep0]
    rw [this, hstM]; k6_field; exact hneq1_0
  have htl2 : K6TailEq L ks0 ks2 := by
    rw [hks2]
    exact k6TailEq_trans (k6TailEq_trans htl1_0 htl_stM)
      (k6TailEq_of_k6WatchStep ks1.nc a b (by rw [hstM_nv]; exact ha_lt1)
        (by rw [hstM_nv]; exact hb_lt1))
  have hcl_nc : k6ClauseLits ks2 ks1.nc.toNat = [a.toNat, b.toNat] := by
    have hoff : k6ClauseOff ks2 ks1.nc.toNat = ks1.alen.toNat := by
      unfold k6ClauseOff; rw [hks2]; dsimp only [k6WatchStep, k6WatchStep0]
      rw [hstM]; k6_field
      rw [List.getElem?_set_self (by rw [hinv1.shapes.clOff_len]; exact hnc_lt), Option.getD_some]
    have hsz : k6ClauseSize ks2 ks1.nc.toNat = 2 := by
      unfold k6ClauseSize; rw [hks2]; dsimp only [k6WatchStep, k6WatchStep0]
      rw [hstM]; k6_field
      rw [List.getElem?_set_self (by rw [hinv1.shapes.clSz_len]; exact hnc_lt), Option.getD_some]
      rfl
    unfold k6ClauseLits; rw [hoff, hsz]
    have har_eq : ks2.arena = (ks1.arena.set ks1.alen.toNat a).set (ks1.alen.toNat + 1) b := by
      rw [hks2]; dsimp only [k6WatchStep, k6WatchStep0]; rw [hstM]; k6_field
    rw [har_eq]; exact k6_arena_take2 hinv1.shapes.arena_len (by omega)
  have hnc_lt2 : ks1.nc.toNat < ks2.nc.toNat := by
    have : ks2.nc = ks1.nc + 1#32 := by
      rw [hks2]; dsimp only [k6WatchStep, k6WatchStep0]; rw [hstM]; k6_field
    rw [this]; unfold K6Layout.maxCl at hnc_lt; bv_omega
  exact ⟨hsh_stM, hstM_mv,
    hinv2, hsync2, hpres.2.2.1.trans hlvl1, hpres.2.2.2.1.trans hnv1_0, htl2,
    hpres.2.2.2.2.1.trans hna1_0, hpres.2.2.2.2.2.1.trans hass1_0, hneq2,
    hinv2.clauses.nv_le, hinv2.clauses.max_v_eq, by rw [hpres.2.2.2.1]; exact ha_lt1,
    by rw [hpres.2.2.2.1]; exact hb_lt1, hcl_nc, hnc_lt2⟩

/-! ## 2. `full_k512_add_live_m6_wp` (`14/14`) -/

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
    have h0 := congrArg BitVec.toNat hmv0
    change (BitVec.ofNat 32 L.maxV).toNat = 0 at h0
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h0; omega
  · rw [hmv32_eq]
    c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
    rw [k6_ptr_base L c.pScratchBuf]
    obtain ⟨Rfr, hRfr⟩ : ∃ Rfr : Mem 64 → Prop, Rfr = (FullK6Frame c L s ⋆ R) := ⟨_, rfl⟩
    have hmA0 : (K6MemA L kPtr ks0 ⋆ Rfr) m := by
      rw [hRfr]; exact k6Mem_to_amem hinv0.shapes hmF0
    have finishR : ∀ {ks' : K6State} {m' : Mem 64},
        K6Inv L P ks' → K6TrailSynced ks' → ks'.nv = ks0.nv → K6TailEq L ks0 ks' →
        ks'.nassump = ks0.nassump → ks'.assump = ks0.assump → ks'.neq = ks0.neq →
        (K6Mem L kPtr ks' ⋆ Rfr) m' → Q () m' :=
      fun hi hs h1 htl h2 h3 h4 hm' =>
        k6_add_live_finish_post hlen hL_len hkb_le hQ hi hs h1 htl h2 h3 h4 (hRfr ▸ hm')
    clear hmF0
    refine wp_join_state0 (α := K6State)
      (fun ks1 m1 => K6Inv L P ks1 ∧ K6TrailSynced ks1 ∧ ks1.lvl = 0#32 ∧
        ks1.nv = ks0.nv ∧ K6TailEq L ks0 ks1 ∧ ks1.nassump = ks0.nassump ∧
        ks1.assump = ks0.assump ∧ ks1.neq = ks0.neq ∧ (K6MemA L kPtr ks1 ⋆ Rfr) m1) ?_ ?_
    · intro J0 ks1 m1 ⟨hinv1, hsync1, hlvl1, hnv1_0, htl1_0, hna1_0, hass1_0, hneq1_0, hmA1⟩
      let runLiveProp :
          ∀ {ksW : K6State} {mW : Mem 64} {k : Tup Val [i32] → Expr Val Cont []},
          K6Inv L P ksW → K6TrailSynced ksW → ksW.lvl = 0#32 →
          ksW.nv = ks0.nv → K6TailEq L ks0 ksW → ksW.nassump = ks0.nassump →
          ksW.assump = ks0.assump → ksW.neq = ks0.neq → (K6MemA L kPtr ksW ⋆ Rfr) mW →
          (∀ confl ksP mP, K6Inv L P ksP → K6TrailSynced ksP → K6PropPreserved ksW ksP →
            K6TailEq L ksW ksP → confl ≠ 0xFFFFFFFF#32 →
            (confl.toNat < ksP.nc.toNat ∧ ∀ l ∈ k6ClauseLits ksP confl.toNat,
              ksP.vals[l]? = some 2#32) →
            (K6Mem L kPtr ksP ⋆ Rfr) mP → wp Γ Q X (k (confl, ())) mP) →
          (∀ ksP mP, K6Inv L P ksP → K6TrailSynced ksP → K6PropPreserved ksW ksP →
            K6TailEq L ksW ksP → (K6Mem L kPtr ksP ⋆ Rfr) mP →
            wp Γ Q X (k (0xFFFFFFFF#32, ())) mP) →
          step13K6PropagateSpec (kPtr, ()) mW (fun r mP => wp Γ Q X (k r) mP) X :=
        fun hinvW hsyncW _ _ _ _ _ _ hmAW hC hN =>
          ⟨L, P, _, Rfr, hinvW, hsyncW, (k6MemA_to_mem hmAW).2,
            fun confl ksP mP hiP hsP hpp htlP _ _ _ _ hconfl hmP => by
              by_cases hcf : confl = 0xFFFFFFFF#32
              · subst hcf; exact hN ksP mP hiP hsP hpp htlP hmP
              · exact hC confl ksP mP hiP hsP hpp htlP hcf (hconfl hcf) hmP⟩
      have hnv1 := hinv1.clauses.nv_le; have hmv1 : ks1.max_v = L.mv32 := hinv1.clauses.max_v_eq
      have ha_lt1 : a.toNat < 2 * ks1.nv.toNat := by rw [hnv1_0]; exact ha_lt
      have ha_mv2 : a.toNat < sz2V L := by unfold sz2V; omega
      c0_hsplit
      · c0_hsteps!
        obtain ⟨hiS, hsS, hnS, htlS, hnaS, hasS, hnqS⟩ :=
          k6_add_live_setStatus_pres hinv1 hsync1 hnv1_0 htl1_0 hna1_0 hass1_0 hneq1_0 20#32
        exact finishR hiS hsS hnS htlS hnaS hasS hnqS (k6MemA_to_mem hm).2
      · c0_hsplit
        · have hent_a := hb_unit ‹_›
          try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
          c0_hsplit
          · have hfals := k6_add_live_vals_some hinv1 ha_mv2 ‹_›
            have hunsat : ∀ β, ¬ P β := SemEntails.unsat_of_falsified hent_a fun x hx => by
              simp at hx; subst hx; exact (k6_falsified_lvl0_entails hinv1 hlvl1 ha_lt1 hfals).2
            c0_hsteps!
            have htlI := k6TailEq_trans htl1_0
              (k6TailEq_of_putHdr_ne_nv (f := .incons) (by decide) 1#32)
            obtain ⟨hiS, hsS, hnS, htlS, hnaS, hasS, hnqS⟩ :=
              k6_add_live_setStatus_pres (k6SetIncons_preserves_inv hinv1 hunsat)
                (by unfold K6TrailSynced at *; k6_field; exact hsync1) hnv1_0 htlI hna1_0
                hass1_0 hneq1_0 20#32
            exact finishR hiS hsS hnS htlS hnaS hasS hnqS (k6MemA_to_mem hm).2
          · refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
            c0_hsplit
            · have hun0 := k6_add_live_vals_some hinv1 ha_mv2 ‹_›
              have hte_lt := k6_trl_end_lt_of_unassigned hinv1.shapes hnv1 hinv1.assign ha_lt1
                (by simp [hun0])
              obtain ⟨hinv2, hsync2⟩ := k6AssignStep_preserves_inv hinv1 hsync1 ha_lt1 hun0
                (fun _ => hent_a) (fun hpos => by rw [hlvl1] at hpos; simp at hpos) (Or.inl rfl)
              have htl2_0 := k6TailEq_trans htl1_0
                (k6TailEq_of_k6AssignStep (L := L) a 0xFFFFFFFF#32 ha_lt1)
              k6_call hAssign
              refine ⟨L, ks1, Rfr, hinv1.shapes, hmv1, (by have := hinv1.clauses.nv_le; omega),
                Nat.lt_of_lt_of_le hte_lt hnv1, (k6MemA_to_mem hmA1).2, fun m2 hm2 => ?_⟩
              c0_hsteps_nogrp; have hmA2 := k6Mem_to_amem hinv2.shapes hm2
              have hlvl2 : (k6AssignStep ks1 a 0xFFFFFFFF#32).lvl = 0#32 := hlvl1
              refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
              k6_call hProp
              refine runLiveProp hinv2 hsync2 hlvl2 hnv1_0 htl2_0 hna1_0 hass1_0 hneq1_0 hmA2
                ?_ ?_
              · intro confl ksP mP hinvP hsyncP hpp htlP hc_ne ⟨hconfl_lt, hfals⟩ hmP
                have hunsat := k6_conflict_unsat_lvl0 hinvP (hpp.lvl.trans hlvl2) hconfl_lt hfals
                have hmAP := k6Mem_to_amem hinvP.shapes hmP; c0_hsteps!
                have htlI := k6TailEq_trans (k6TailEq_trans htl2_0 htlP)
                  (k6TailEq_of_putHdr_ne_nv (f := .incons) (by decide) 1#32)
                obtain ⟨hiS, hsS, hnS, htlS, hnaS, hasS, hnqS⟩ :=
                  k6_add_live_setStatus_pres (k6SetIncons_preserves_inv hinvP hunsat)
                    (by unfold K6TrailSynced at *; k6_field; exact hsyncP)
                    (hpp.nv.trans hnv1_0) htlI (hpp.nassump.trans hna1_0)
                    (hpp.assump.trans hass1_0) (hpp.neq.trans hneq1_0) 20#32
                exact finishR hiS hsS hnS htlS hnaS hasS hnqS (k6MemA_to_mem hm).2
              · intro ksP mP hinvP hsyncP hpp htlP hmP; c0_hsteps!
                exact finishR hinvP hsyncP (hpp.nv.trans hnv1_0) (k6TailEq_trans htl2_0 htlP)
                  (hpp.nassump.trans hna1_0) (hpp.assump.trans hass1_0) (hpp.neq.trans hneq1_0)
                  hmP
            · c0_hsteps_nogrp; refine LeanQbe.T.wp_unroll_group fun _ _ => ?_; k6_call hProp
              refine runLiveProp hinv1 hsync1 hlvl1 hnv1_0 htl1_0 hna1_0 hass1_0 hneq1_0 hmA1
                ?_ ?_
              · intro confl ksP mP hinvP hsyncP hpp htlP hc_ne ⟨hconfl_lt, hfals⟩ hmP
                have hunsat := k6_conflict_unsat_lvl0 hinvP (hpp.lvl.trans hlvl1) hconfl_lt hfals
                have hmAP := k6Mem_to_amem hinvP.shapes hmP; c0_hsteps!
                have htlI := k6TailEq_trans (k6TailEq_trans htl1_0 htlP)
                  (k6TailEq_of_putHdr_ne_nv (f := .incons) (by decide) 1#32)
                obtain ⟨hiS, hsS, hnS, htlS, hnaS, hasS, hnqS⟩ :=
                  k6_add_live_setStatus_pres (k6SetIncons_preserves_inv hinvP hunsat)
                    (by unfold K6TrailSynced at *; k6_field; exact hsyncP)
                    (hpp.nv.trans hnv1_0) htlI (hpp.nassump.trans hna1_0)
                    (hpp.assump.trans hass1_0) (hpp.neq.trans hneq1_0) 20#32
                exact finishR hiS hsS hnS htlS hnaS hasS hnqS (k6MemA_to_mem hm).2
              · intro ksP mP hinvP hsyncP hpp htlP hmP; c0_hsteps!
                exact finishR hinvP hsyncP (hpp.nv.trans hnv1_0) (k6TailEq_trans htl1_0 htlP)
                  (hpp.nassump.trans hna1_0) (hpp.assump.trans hass1_0) (hpp.neq.trans hneq1_0)
                  hmP
        · obtain ⟨hb_lt0, hent_ab⟩ := hb_bin ‹_›
          have hb_lt1 : b.toNat < 2 * ks1.nv.toNat := by rw [hnv1_0]; exact hb_lt0
          have hb_mv2 : b.toNat < sz2V L := by unfold sz2V; omega
          have hca1 : ks1.acap.toNat = L.acap := by
            unfold dimacsBound at hac_b
            rw [hinv1.clauses.acap_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have hmc1 : ks1.max_cl.toNat = L.maxCl := by
            rw [hinv1.clauses.max_cl_eq]; unfold K6Layout.maxCl
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          c0_hsplit
          · c0_hsteps!
            exact finishR hinv1 hsync1 hnv1_0 htl1_0 hna1_0 hass1_0 hneq1_0 (k6MemA_to_mem hmA1).2
          · c0_hsplit
            · c0_hsteps!
              exact finishR hinv1 hsync1 hnv1_0 htl1_0 hna1_0 hass1_0 hneq1_0
                (k6MemA_to_mem hmA1).2
            · have hnc_lt : ks1.nc.toNat < L.maxCl := by rw [← hmc1]; bv_omega
              have hal_ks : ks1.alen.toNat ≤ ks1.acap.toNat := by
                rw [hca1]; exact hinv1.clauses.alen_le
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
                by simp [hinv1.shapes.arena_len]
              obtain ⟨stM, hstM⟩ : ∃ x : K6State, x = (((({ ks1 with
                  arena := (ks1.arena.set ks1.alen.toNat a).set (ks1.alen.toNat + 1) b } :
                K6State).putHdr .alen (ks1.alen + 2#32)).putArr .clOff ks1.nc.toNat ks1.alen).putArr
                .clSz ks1.nc.toNat 2#32).putHdr .nc (ks1.nc + 1#32) := ⟨_, rfl⟩
              obtain ⟨ks2, hks2⟩ : ∃ x : K6State, x = k6WatchStep stM ks1.nc a b := ⟨_, rfl⟩
              obtain ⟨hsh_stM, hmv_stM, hinv2, hsync2, hlvl2, hnv2_eq, htl2_0,
                hna2_eq, hass2_eq, hneq2_eq, hnv2, hmv2, ha_lt2, hb_lt2, hcl_nc, hnc_lt2⟩ :=
                k6_add_live_bin_facts hstM hks2 hinv1 hlvl1 hnv1_0 htl1_0 hna1_0 hass1_0 hneq1_0
                  ha_lt1 hb_lt1 hnc_lt hoff_fit har_len hent_ab
                  (fun j hj => by
                    have hj2 : j < 2 := by
                      change j < (2#32 : BitVec 32).toNat at hj; simp at hj; exact hj
                    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> simpa)
                  hsync1
              c0_hsteps_nogrp; obtain ⟨hshM, hmM⟩ := k6MemA_to_mem hm
              have hmM_eq : (K6Mem L kPtr stM ⋆ Rfr) m := by
                refine Eq.mp (congrArg (fun x => (K6Mem L kPtr x ⋆ Rfr) _) ?_) hmM
                rw [hstM]; k6_ext <;> (try rfl) <;> rw [h1_eq]
              k6_call hWatch
              refine ⟨L, stM, Rfr, hsh_stM, hmv_stM, hnc_lt, (by omega), (by omega), hmM_eq,
                fun m2 hm2 => ?_⟩
              rw [← hks2] at hm2
              have hmA2 : (K6MemA L kPtr ks2 ⋆ Rfr) m2 := k6Mem_to_amem hinv2.shapes hm2
              clear hm2 hmM_eq hstM hks2
              c0_hsteps_nogrp; refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
              c0_hsplit
              · have hfals_a := k6_add_live_vals_some hinv2 ha_mv2 ‹_›
                obtain ⟨⟨ja, hja, hja_eq⟩, hent_na⟩ :=
                  k6_falsified_lvl0_entails hinv2 hlvl2 ha_lt2 hfals_a
                c0_hsplit
                · have hfals_b := k6_add_live_vals_some hinv2 hb_mv2 ‹_›
                  have hent_nb := (k6_falsified_lvl0_entails hinv2 hlvl2 hb_lt2 hfals_b).2
                  have hunsat : ∀ β, ¬ P β := SemEntails.unsat_of_falsified hent_ab fun x hx => by
                    simp at hx; rcases hx with rfl | rfl <;> assumption
                  c0_hsteps!
                  have htlI := k6TailEq_trans htl2_0
                    (k6TailEq_of_putHdr_ne_nv (f := .incons) (by decide) 1#32)
                  obtain ⟨hiS, hsS, hnS, htlS, hnaS, hasS, hnqS⟩ :=
                    k6_add_live_setStatus_pres (k6SetIncons_preserves_inv hinv2 hunsat)
                      (by unfold K6TrailSynced at *; k6_field; exact hsync2)
                      hnv2_eq htlI hna2_eq hass2_eq hneq2_eq 20#32
                  exact finishR hiS hsS hnS htlS hnaS hasS hnqS
                    (k6MemA_to_mem ‹(K6MemA L kPtr _ ⋆ Rfr) _›).2
                · refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                  c0_hsplit
                  · have hun_b := k6_add_live_vals_some hinv2 hb_mv2 ‹_›
                    have hte_lt := k6_trl_end_lt_of_unassigned hinv2.shapes hnv2 hinv2.assign hb_lt2
                      (by simp [hun_b])
                    have hent_b : SemEntails P [b.toNat] :=
                      SemEntails.unit_of_falsified hent_ab fun x hx hne => by
                        simp at hx; rcases hx with rfl | rfl
                        · exact hent_na
                        · exact absurd rfl hne
                    obtain ⟨hinv3, hsync3⟩ := k6AssignStep_preserves_inv hinv2 hsync2 hb_lt2 hun_b
                      (fun _ => hent_b) (fun hpos => by rw [hlvl2] at hpos; simp at hpos)
                      (Or.inr ⟨hnc_lt2, by rw [hcl_nc]; simp, fun x hx hne => by
                        rw [hcl_nc] at hx; simp at hx; rcases hx with rfl | rfl
                        · exact ⟨ja, hja, hja_eq⟩
                        · exact absurd rfl hne⟩)
                    have htl3_0 := k6TailEq_trans htl2_0
                      (k6TailEq_of_k6AssignStep (L := L) b ks1.nc hb_lt2)
                    k6_call hAssign
                    refine ⟨L, ks2, Rfr, hinv2.shapes, hmv2,
                      (by have := hinv2.clauses.nv_le; omega),
                      Nat.lt_of_lt_of_le hte_lt hnv2, (k6MemA_to_mem hmA2).2, fun m3 hm3 => ?_⟩
                    c0_hsteps_nogrp; have hmA3 := k6Mem_to_amem hinv3.shapes hm3
                    refine LeanQbe.T.wp_unroll_group fun _ _ => ?_; k6_call hProp
                    refine runLiveProp hinv3 hsync3 hlvl2 hnv2_eq htl3_0 hna2_eq hass2_eq hneq2_eq
                      hmA3 (fun cP ksP mP hiP hsP hpp htlP hc_ne hcf hmP => ?_)
                      (fun ksP mP hiP hsP hpp htlP hmP => by
                        c0_hsteps!; exact finishR hiP hsP (hpp.nv.trans hnv2_eq)
                          (k6TailEq_trans htl3_0 htlP) (hpp.nassump.trans hna2_eq)
                          (hpp.assump.trans hass2_eq) (hpp.neq.trans hneq2_eq) hmP)
                    · have hmAP := k6Mem_to_amem hiP.shapes hmP; c0_hsteps!
                      exact k6_add_live_confl_finish (ksW := k6AssignStep ks2 b ks1.nc)
                        finishR hlvl2 hnv2_eq htl3_0 hna2_eq hass2_eq hneq2_eq hiP hsP hpp htlP
                        hcf ‹_›
                  · c0_hsteps_nogrp; refine LeanQbe.T.wp_unroll_group fun _ _ => ?_; k6_call hProp
                    refine runLiveProp hinv2 hsync2 hlvl2 hnv2_eq htl2_0 hna2_eq hass2_eq hneq2_eq
                      hmA2 (fun cP ksP mP hiP hsP hpp htlP hc_ne hcf hmP => ?_)
                      (fun ksP mP hiP hsP hpp htlP hmP => by
                        c0_hsteps!; exact finishR hiP hsP (hpp.nv.trans hnv2_eq)
                          (k6TailEq_trans htl2_0 htlP) (hpp.nassump.trans hna2_eq)
                          (hpp.assump.trans hass2_eq) (hpp.neq.trans hneq2_eq) hmP)
                    · have hmAP := k6Mem_to_amem hiP.shapes hmP; c0_hsteps!
                      exact k6_add_live_confl_finish finishR hlvl2 hnv2_eq htl2_0 hna2_eq hass2_eq
                        hneq2_eq hiP hsP hpp htlP hcf ‹_›
              · refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                c0_hsplit
                · c0_hsplit
                  · have hfals_b := k6_add_live_vals_some hinv2 hb_mv2 ‹_›
                    have hun_a := k6_add_live_vals_some hinv2 ha_mv2 ‹_›
                    obtain ⟨⟨jb, hjb, hjb_eq⟩, hent_nb⟩ :=
                      k6_falsified_lvl0_entails hinv2 hlvl2 hb_lt2 hfals_b
                    have hte_lt := k6_trl_end_lt_of_unassigned hinv2.shapes hnv2 hinv2.assign ha_lt2
                      (by simp [hun_a])
                    have hent_a : SemEntails P [a.toNat] :=
                      SemEntails.unit_of_falsified hent_ab fun x hx hne => by
                        simp at hx; rcases hx with rfl | rfl
                        · exact absurd rfl hne
                        · exact hent_nb
                    obtain ⟨hinv3, hsync3⟩ := k6AssignStep_preserves_inv hinv2 hsync2 ha_lt2 hun_a
                      (fun _ => hent_a) (fun hpos => by rw [hlvl2] at hpos; simp at hpos)
                      (Or.inr ⟨hnc_lt2, by rw [hcl_nc]; simp, fun x hx hne => by
                        rw [hcl_nc] at hx; simp at hx; rcases hx with rfl | rfl
                        · exact absurd rfl hne
                        · exact ⟨jb, hjb, hjb_eq⟩⟩)
                    have htl3_0 := k6TailEq_trans htl2_0
                      (k6TailEq_of_k6AssignStep (L := L) a ks1.nc ha_lt2)
                    k6_call hAssign
                    refine ⟨L, ks2, Rfr, hinv2.shapes, hmv2,
                      (by have := hinv2.clauses.nv_le; omega),
                      Nat.lt_of_lt_of_le hte_lt hnv2, (k6MemA_to_mem hmA2).2, fun m3 hm3 => ?_⟩
                    c0_hsteps_nogrp; have hmA3 := k6Mem_to_amem hinv3.shapes hm3
                    refine LeanQbe.T.wp_unroll_group fun _ _ => ?_; k6_call hProp
                    refine runLiveProp hinv3 hsync3 hlvl2 hnv2_eq htl3_0 hna2_eq hass2_eq hneq2_eq
                      hmA3 (fun cP ksP mP hiP hsP hpp htlP hc_ne hcf hmP => ?_)
                      (fun ksP mP hiP hsP hpp htlP hmP => by
                        c0_hsteps!; exact finishR hiP hsP (hpp.nv.trans hnv2_eq)
                          (k6TailEq_trans htl3_0 htlP) (hpp.nassump.trans hna2_eq)
                          (hpp.assump.trans hass2_eq) (hpp.neq.trans hneq2_eq) hmP)
                    · have hmAP := k6Mem_to_amem hiP.shapes hmP; c0_hsteps!
                      exact k6_add_live_confl_finish (ksW := k6AssignStep ks2 a ks1.nc)
                        finishR hlvl2 hnv2_eq htl3_0 hna2_eq hass2_eq hneq2_eq hiP hsP hpp htlP
                        hcf ‹_›
                  · c0_hsteps_nogrp; refine LeanQbe.T.wp_unroll_group fun _ _ => ?_; k6_call hProp
                    refine runLiveProp hinv2 hsync2 hlvl2 hnv2_eq htl2_0 hna2_eq hass2_eq hneq2_eq
                      hmA2 (fun cP ksP mP hiP hsP hpp htlP hc_ne hcf hmP => ?_)
                      (fun ksP mP hiP hsP hpp htlP hmP => by
                        c0_hsteps!; exact finishR hiP hsP (hpp.nv.trans hnv2_eq)
                          (k6TailEq_trans htl2_0 htlP) (hpp.nassump.trans hna2_eq)
                          (hpp.assump.trans hass2_eq) (hpp.neq.trans hneq2_eq) hmP)
                    · have hmAP := k6Mem_to_amem hiP.shapes hmP; c0_hsteps!
                      exact k6_add_live_confl_finish finishR hlvl2 hnv2_eq htl2_0 hna2_eq hass2_eq
                        hneq2_eq hiP hsP hpp htlP hcf ‹_›
                · c0_hsteps_nogrp; refine LeanQbe.T.wp_unroll_group fun _ _ => ?_; k6_call hProp
                  refine runLiveProp hinv2 hsync2 hlvl2 hnv2_eq htl2_0 hna2_eq hass2_eq hneq2_eq
                    hmA2 (fun cP ksP mP hiP hsP hpp htlP hc_ne hcf hmP => ?_)
                    (fun ksP mP hiP hsP hpp htlP hmP => by
                      c0_hsteps!; exact finishR hiP hsP (hpp.nv.trans hnv2_eq)
                        (k6TailEq_trans htl2_0 htlP) (hpp.nassump.trans hna2_eq)
                        (hpp.assump.trans hass2_eq) (hpp.neq.trans hneq2_eq) hmP)
                  · have hmAP := k6Mem_to_amem hiP.shapes hmP; c0_hsteps!
                    exact k6_add_live_confl_finish finishR hlvl2 hnv2_eq htl2_0 hna2_eq hass2_eq
                      hneq2_eq hiP hsP hpp htlP hcf ‹_›
    · intro J0 hJ0
      refine LeanQbe.T.wp_unroll_group fun J1 hJ1 => ?_
      have hBt_ok : J1 () m := by
        refine hJ1 () m ?_
        k6_call hBt
        refine ⟨L, P, ks0, Rfr, hinv0, Or.inl rfl, (k6MemA_to_mem hmA0).2,
          fun ks1 m1 hinv1 hsync1 hlvl1 _ hbtp htl1 _ _ hm1 => ?_⟩
        have hmA1 := k6Mem_to_amem hinv1.shapes hm1; c0_hsteps!
        obtain ⟨hinv1', hsync1', hnv1', htl1', hna1', hass1', hneq1'⟩ :=
          k6_add_live_setStatus_pres hinv1 hsync1 hbtp.nv htl1 hbtp.nassump hbtp.assump
            hbtp.neq 0#32
        exact hJ0 _ _ ⟨hinv1', hsync1', by k6_field; exact hlvl1, hnv1', htl1', hna1', hass1',
          hneq1', ‹_›⟩
      c0_hsplit
      · refine head_wp_jump rfl rfl hBt_ok
      · c0_hsplit
        · refine head_wp_jump rfl rfl hBt_ok
        · have hlvl0 : ks0.lvl = 0#32 := by bv_omega
          c0_hsteps!
          exact hJ0 _ m ⟨hinv0, k6_trailSynced_of_lvl0 hinv0 hlvl0, hlvl0, rfl,
            k6TailEq_refl L ks0, rfl, rfl, rfl, hmA0⟩

end LeanQbe.T.Examples.Kissat.Proof.Kitten

end
