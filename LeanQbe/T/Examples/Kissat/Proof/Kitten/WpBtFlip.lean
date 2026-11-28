/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Kitten.LemmasBtAdd

/-!
# Step-13 `Func.wp` Proofs for `full_k6_backtrack` & `full_k6_flip` (`8, 13/14`, `WpBtFlip`)

Certifies:
- `full_k6_backtrack_wp` (`step13K6BacktrackSpec`)
- `full_k6_flip_wp` (`step13K6FlipSpec`)

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

/-! ## 1. `K6TailEq` Preservation Helpers -/

private theorem k6TailEq_of_k6BtStep {L : K6Layout} {ks st : K6State} (lit : BitVec 32)
    (hlit : lit.toNat < 2 * ks.nv.toNat) (ht : K6TailEq L ks st) :
    let v := (lit >>> 1).toNat
    let st' := ((((st.putArr .vals lit.toNat 0#32).putArr .vals (lit ^^^ 1#32).toNat 0#32).putArr
      .lvlArr v 0#32).putArr .rsn v 0xFFFFFFFF#32).putHdr .unass (st.unass + 1#32)
    K6TailEq L ks st' ∧ ∀ qs, K6TailEq L ks (st'.putHdr .qsearch qs) := by
  intro v st'
  have hlt1 : lit.toNat < 2 * st.nv.toNat := ht.1 ▸ hlit
  have hx_lt1 : (lit ^^^ 1#32).toNat < 2 * st.nv.toNat := by
    rw [ht.1, (k6_bv32_xor1_lt hlit).1]; exact (k6_bv32_xor1_lt hlit).2
  have hv_lt : v < st.nv.toNat := by
    dsimp only [v]; rw [ht.1, (k6_bv32_div2_lt hlit).1]; omega
  have hst' : K6TailEq L ks st' := by
    have hnv' : st'.nv = st.nv := by dsimp only [st']; k6_field
    refine k6TailEq_trans ht ⟨hnv', fun w hw _ => ?_⟩
    have hne : lit.toNat ≠ 2 * w ∧ lit.toNat ≠ 2 * w + 1 ∧
        (lit ^^^ 1#32).toNat ≠ 2 * w ∧ (lit ^^^ 1#32).toNat ≠ 2 * w + 1 ∧ v ≠ w := by omega
    dsimp only [st', K6State.putArr, K6State.putHdr]
    exact ⟨List.getElem?_set_ne hne.2.2.2.2, List.getElem?_set_ne hne.2.2.2.2, rfl,
      (List.getElem?_set_ne hne.2.2.1).trans (List.getElem?_set_ne hne.1),
      (List.getElem?_set_ne hne.2.2.2.1).trans (List.getElem?_set_ne hne.2.1), rfl, rfl⟩
  exact ⟨hst', fun qs => k6TailEq_trans hst' (k6TailEq_of_putHdr_ne_nv (f := .qsearch)
    (by decide) qs)⟩

private theorem k6TailEq_of_k6FlipFinish {L : K6Layout} {ks : K6State} (lit : BitVec 32)
    (hlit : lit.toNat < 2 * ks.nv.toNat) :
    K6TailEq L ks ((ks.putArr .vals lit.toNat 2#32).putArr .vals (lit ^^^ 1#32).toNat 1#32) := by
  have hx_lt : (lit ^^^ 1#32).toNat < 2 * ks.nv.toNat := by
    rw [(k6_bv32_xor1_lt hlit).1]; exact (k6_bv32_xor1_lt hlit).2
  exact k6TailEq_trans (k6TailEq_putArr_lit (Or.inl rfl) hlit 2#32)
    (k6TailEq_putArr_lit (ks := ks.putArr .vals lit.toNat 2#32) (Or.inl rfl) hx_lt 1#32)

theorem k6_flip_mv32_eq {L : K6Layout} {cap : Nat} (hL_mv : L.maxV = k6MaxV cap) :
    (BitVec.ofNat 64 (k6MaxV cap)).setWidth 32 = L.mv32 := by
  have hm := L.hmaxV
  rw [← hL_mv]; unfold K6Layout.mv32; apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-! ## 2. `full_k6_backtrack_wp` (`8/14`) -/

/-- `8/14`: Parametric `Func.wp` proof for `full_k6_backtrack` (`step13K6BacktrackSpec`). -/
theorem full_k6_backtrack_wp (Γ : Env) :
    ∀ args m Q X, step13K6BacktrackSpec args m Q X →
      Func.wp Γ full_k6_backtrack_body args m Q X := by
  rintro ⟨kPtr, target_lvl, ⟨⟩⟩ m Q X ⟨L, P, ks, R, hinv, hsync_below, hm, hQ⟩
  have hm_b := L.hmaxV; have hnv := hinv.clauses.nv_le; have hsh := hinv.shapes
  have hmv : ks.max_v = L.mv32 := hinv.clauses.max_v_eq
  have hmA := k6Mem_to_amem hsh hm; clear hm
  c0_hsteps_nogrp
  rw [hmv]
  refine wp_join_state1 (fun st : BitVec 32 => st)
    (fun _ m' => (K6MemA L kPtr ks ⋆ R) m') ?_ ?_
  · intro J0 best_st m0 hm0
    refine wp_while_break_state (β := BitVec 32 × BitVec 32 × K6State)
      (fun bst => (bst.1, bst.2.1, ()))
      (fun bst m' => K6BtLoopInv L ks target_lvl bst.1 bst.2.2 ∧ K6TailEq L ks bst.2.2 ∧
        (bst.1 = 0#32 ∨ ∃ i < bst.1.toNat, i = bst.1.toNat - 1 ∧
          (bst.2.2.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
            target_lvl.toNat) ∧
        (K6MemA L kPtr bst.2.2 ⋆ R) m')
      (α := BitVec 32 × BitVec 32 × K6State)
      (fun st => (st.1, st.2.1, ())) (fun st => st.1.toNat)
      (fun st m' => K6BtLoopInv L ks target_lvl st.1 st.2.2 ∧ K6TailEq L ks st.2.2 ∧
        (K6MemA L kPtr st.2.2 ⋆ R) m')
      ?_ ?_ ?_
    · rintro B ⟨te, _best_st, st⟩ m' ⟨hbt, htail, hexit, hm'⟩
      dsimp only at hbt htail hexit hm'
      c0_hsteps_nogrp
      let stProp := if te.toNat < st.prop.toNat then (st.putHdr .trl_end te).putHdr .prop te
        else st.putHdr .trl_end te
      refine wp_join0 (fun m'' => (K6MemA L kPtr stProp ⋆ R) m'') ?_ ?_
      · intro Jf m'' hm''
        c0_hsteps!
        obtain ⟨_, hmFin⟩ := k6MemA_to_mem hm
        have hfin := k6BtLoopInv_finish hinv hbt hsync_below hexit
        let ksFin := ((st.putHdr .trl_end te).putHdr .prop
          (if te.toNat < st.prop.toNat then te else st.prop)).putHdr .lvl target_lvl
        have heq_st : stProp.putHdr .lvl target_lvl = ksFin := by
          dsimp only [stProp, ksFin]
          by_cases hp : te.toNat < st.prop.toNat <;> simp only [hp, ite_true, ite_false] <;> k6_ext
        rw [heq_st] at hmFin
        have htail_fin : K6TailEq L ks ksFin :=
          k6TailEq_trans htail (k6TailEq_trans (k6TailEq_of_putHdr_ne_nv (by decide) te)
            (k6TailEq_trans (k6TailEq_of_putHdr_ne_nv (by decide) _)
              (k6TailEq_of_putHdr_ne_nv (by decide) target_lvl)))
        rcases hfin with ⟨h1, h2, h3, h4, h5, h6⟩
        have h7 : ∀ i < ks.trl_end.toNat,
            (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat →
            i < ksFin.trl_end.toNat := by
          intro i hi hle
          have hte_eq : ksFin.trl_end = te := by dsimp only [ksFin]; k6_field
          rw [hte_eq]
          rcases Nat.lt_or_ge i te.toNat with hlt | hge
          · exact hlt
          · exfalso; have := hbt.popped_gt i hge hi; omega
        exact hQ _ _ h1 h2 h3 h4 h5 htail_fin h6 h7 hmFin
      · intro Jf hJf
        have hpr_eq : (st.putHdr .trl_end te).prop = st.prop := by k6_field
        c0_hsteps!
        · apply hJf _; have hp : te.toNat < st.prop.toNat := by rw [← hpr_eq]; bv_omega
          simpa [stProp, hp] using hm
        · apply hJf _; have hp : ¬ te.toNat < st.prop.toNat := by rw [← hpr_eq]; bv_omega
          simpa [stProp, hp] using hm
    · rintro B L1 ⟨te, bst, st⟩ m' hB hL ⟨hbt, htail, hm'⟩
      dsimp only at hbt htail hm'
      c0_hsplit
      · have hpos : 0 < te.toNat := by bv_omega
        have hte1_lt : te.toNat - 1 < ks.trl_end.toNat := by have := hbt.te_le; omega
        have hte1_mv : (te - 1#32).toNat < szV L := by
          have := hinv.assign.trl_end_le; have := hbt.te_le; unfold szV; bv_omega
        have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
          rw [hsh.trl_len]; have := hinv.assign.trl_end_le; omega
        let lit := ks.trl[te.toNat - 1]'(by omega)
        have hte_sub1 : (te - (1 : BitVec 32)).toNat = te.toNat - 1 := by bv_omega
        have hlit_get : st.trl[(te - (1 : BitVec 32)).toNat]?.getD 0#32 = lit := by
          rw [hte_sub1, hbt.trl_eq,
            List.getElem?_eq_getElem (by omega : te.toNat - 1 < ks.trl.length), Option.getD_some]
        have hlit_lt : lit.toNat < 2 * ks.nv.toNat := by
          have hm1 := k6_mem_trailLits_of_lt hte1_lt htrl_len
          rw [List.getElem?_eq_getElem (by omega : te.toNat - 1 < ks.trl.length),
            Option.getD_some] at hm1
          exact hinv.assign.trl_lt lit.toNat hm1
        obtain ⟨hv_eq, _⟩ := k6_bv32_div2_lt hlit_lt
        obtain ⟨hn_eq, _⟩ := k6_bv32_xor1_lt hlit_lt
        have hv_st_mv : ((st.trl[(te - (1 : BitVec 32)).toNat]?.getD 0#32) >>> (1 : Nat)).toNat <
            szV L := by
          rw [hlit_get, hv_eq]; unfold szV; omega
        have hl_mv2 : lit.toNat < sz2V L := by unfold sz2V; omega
        have hnl_st_mv2 :
            (st.trl[(te - (1 : BitVec 32)).toNat]?.getD 0#32 ^^^ (1 : BitVec 32)).toNat <
            sz2V L := by
          rw [hlit_get, K6PtrTactics.k6_bv32_one, hn_eq]; unfold sz2V litNeg
          rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
        c0_hsplit
        · refine hB (te, bst, st) m' ⟨hbt, htail,
            Or.inr ⟨te.toNat - 1, Nat.sub_lt hpos Nat.one_pos, rfl, ?_⟩, hm'⟩
          rw [List.getElem?_eq_getElem (by omega : te.toNat - 1 < ks.trl.length), Option.getD_some]
          have hle_raw :
              (st.lvlArr[(st.trl[(te - (1 : BitVec 32)).toNat]?.getD 0#32).toNat / 2]?.getD
                0#32).toNat ≤ target_lvl.toNat := by c0_bound
          rwa [hlit_get] at hle_raw
        · have hstep := k6BtLoopInv_step hinv hbt hpos (by
            have hle_raw :
                ¬ (st.lvlArr[(st.trl[(te - (1 : BitVec 32)).toNat]?.getD 0#32).toNat / 2]?.getD
                    0#32).toNat ≤ target_lvl.toNat := by c0_bound
            rw [hte_sub1, hbt.trl_eq] at hle_raw; exact Nat.lt_of_not_le hle_raw)
          have hlit_tail : (ks.trl[te.toNat - 1]?.getD 0#32).toNat < 2 * ks.nv.toNat := by
            rw [List.getElem?_eq_getElem (by omega : te.toNat - 1 < ks.trl.length),
              Option.getD_some]
            exact hlit_lt
          have htail_step := k6TailEq_of_k6BtStep (L := L) (ks.trl[te.toNat - 1]?.getD 0#32)
            hlit_tail htail
          c0_hsteps!
          · have hs2 := hstep.2 (st.trl[(te - (1 : BitVec 32)).toNat]?.getD 0#32 >>> (1 : Nat))
            have hex1 : (te - 1#32).toNat = te.toNat - 1 := by bv_omega
            refine hL (te - 1#32, _, _) _ (by dsimp only; rw [hex1]; omega)
              ⟨hs2, ?_, ?_⟩
            · simpa only [K6State.putHdr, hbt.trl_eq, K6PtrTactics.k6_bv32_zero,
                K6PtrTactics.k6_bv32_one, hex1] using
                htail_step.2 (st.trl[(te - (1 : BitVec 32)).toNat]?.getD 0#32 >>> (1 : Nat))
            · refine Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _) ?_) hm
              k6_ext <;> (first | rfl | (simp only [hbt.trl_eq,
                K6PtrTactics.k6_bv32_one, hex1]; try rfl))
          · have hex1 : (te - 1#32).toNat = te.toNat - 1 := by bv_omega
            refine hL (te - 1#32, bst, _) _ (by dsimp only; rw [hex1]; omega)
              ⟨hstep.1, ?_, ?_⟩
            · simpa only [K6State.putHdr, hbt.trl_eq, K6PtrTactics.k6_bv32_zero,
                K6PtrTactics.k6_bv32_one, hex1] using htail_step.1
            · refine Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _) ?_) hm
              k6_ext <;> (first | rfl | (simp only [hbt.trl_eq,
                K6PtrTactics.k6_bv32_one, hex1]; try rfl))
      · exact hB (te, bst, st) m' ⟨hbt, htail, Or.inl (by bv_omega), hm'⟩
    · intro B L1 hB hL
      exact wp_jump_state (proj := fun st : BitVec 32 × BitVec 32 × K6State => (st.1, st.2.1, ()))
        (ks.trl_end, best_st, ks) rfl
        (hL (ks.trl_end, best_st, ks) m0 ⟨k6BtLoopInv_init hinv, k6TailEq_refl L ks, hm0⟩)
  · intro J0 hJ0
    c0_hsplit
    · have hqs_mv : ks.qsearch.toNat < szV L := by
        have : ks.qsearch.toNat < ks.nv.toNat := by bv_omega
        unfold szV; omega
      c0_hsteps!; exact hJ0 _ m hmA
    · c0_hsteps!; exact hJ0 _ m hmA

/-! ## 3. `full_k6_flip_wp` (`13/14`) -/

private theorem k6_flip_finish_post {c : FullCfg} {s : FullState} {P : (Nat → Bool) → Prop}
    {L : K6Layout} {R : Mem 64 → Prop} {Q : Post [.bool]} (hlen : s.LengthsOk c)
    (hL_len : L.scrLen = c.scratch_cap)
    (hkb_le : L.k6Base ≤ s.scratch.scratch_buf.length)
    (hQ : ∀ (ok : Bool) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      let ks := k6StateOfScratch L s.scratch.scratch_buf; let ks' := k6StateOfScratch L scr'
      s'.LengthsOk c → (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K6Inv L P ks' → ks'.nv = ks.nv → K6TailEq L ks ks' → ks'.nassump = ks.nassump →
      k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf → ks'.neq = ks.neq →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    let ks := k6StateOfScratch L s.scratch.scratch_buf
    ∀ (ok : Bool) (ks' : K6State) (m' : Mem 64),
      K6Inv L P ks' → ks'.nv = ks.nv → K6TailEq L ks ks' → ks'.nassump = ks.nassump →
      ks'.assump = ks.assump → ks'.neq = ks.neq →
      (K6MemA L (L.kPtr c.pScratchBuf) ks' ⋆ (FullK6Frame c L s ⋆ R)) m' → Q (ok, ()) m' := by
  intro ks ok ks' m' hinv' hnv' htail' hna' hass' hneq' hm'
  obtain ⟨_, hm0⟩ := k6MemA_to_mem hm'
  have hmJ := fullMem_join_k6 (c := c) (L := L) (s := s) (ks' := ks') (R := R)
    hkb_le hinv'.shapes (sep_ac hm0)
  let scr' := s.scratch.scratch_buf.take L.k6Base ++ ks'.toSlab
  have htk_len : (s.scratch.scratch_buf.take L.k6Base).length = L.k6Base :=
    List.length_take_of_le hkb_le
  have hscr'_len : scr'.length = c.scratch_cap := by
    dsimp only [scr']
    rw [List.length_append, htk_len, K6State.toSlab_length hinv'.shapes, ← hL_len]
    unfold K6Layout.scrLen K6Layout.k6Base K6Layout.k6Fixed; omega
  have hpre : ∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]? := fun i hi => by
    rw [List.getElem?_append_left (by rw [htk_len]; exact hi), List.getElem?_take_of_lt hi]
  have hof : k6StateOfScratch L scr' = ks' := by
    unfold k6StateOfScratch
    rw [k6_slab_drop_exact _ ks'.toSlab htk_len]
    exact K6State.ofSlab_toSlab hinv'.shapes
  exact hQ ok scr' m' (k6_fullState_lengthsOk_scratch hlen hscr'_len) hpre
    (by rw [hof]; exact hinv') (by rw [hof]; exact hnv') (by rw [hof]; exact htail')
    (by rw [hof]; exact hna') (by unfold k6AssumpLitsS k6AssumpLits; rw [hof, hna', hass'])
    (by rw [hof]; exact hneq') hmJ

private theorem k6_flip_wblit_eq {ksW : K6State} {w0 idx : Nat} {s1 : BitVec 32}
    (hidx : idx = w0 / 2)
    (hs : (ksW.clOff[w0 / 2]?.getD 0#32 + s1).toNat =
      (ksW.clOff[w0 / 2]?.getD 0#32).toNat + (w0 % 2 ^^^ 1)) :
    ksW.wblit.set w0 (ksW.arena[(ksW.clOff[idx]?.getD 0#32 + s1).toNat]?.getD 0#32) =
      ksW.wblit.set w0 (ksW.arena[(ksW.clOff[w0 / 2]?.getD 0#32).toNat +
        (w0 % 2 ^^^ 1)]?.getD 0#32) := by
  subst hidx; rw [hs]

/-- `13/14`: Parametric `Func.wp` proof for `full_k6_flip` (`step13K6FlipSpec`). -/
theorem full_k6_flip_wp (Γ : Env)
    (hMaxV : Γ.Has "full_m6_max_v" m6MaxVSpec)
    (hAddTicks : Γ.Has "full_k6_add_ticks" k6AddTicksSpec) :
    ∀ args m Q X, step13K6FlipSpec args m Q X → Func.wp Γ full_k6_flip_body args m Q X := by
  rintro ⟨hPtr, lit, ⟨⟩⟩ m Q X ⟨c, s, P, L, R, rfl, hlen, hL_len, hL_mv, hinv, hlit_lt, hm, hQ⟩
  let scr := s.scratch.scratch_buf; let ks := k6StateOfScratch L scr
  have hm_b := L.hmaxV; have hac_b := L.hacap
  have hsh := hinv.shapes; have hnv := hinv.clauses.nv_le
  have hmv_eq_ks : ks.max_v = L.mv32 := hinv.clauses.max_v_eq
  have hscr_len : scr.length = L.scrLen := hlen.scratch_ok.scratch_buf_len.trans hL_len.symm
  have hkb_le : L.k6Base ≤ scr.length := by rw [hscr_len]; unfold K6Layout.scrLen; omega
  let kPtr := L.kPtr c.pScratchBuf
  have hmA0 : (K6MemA L kPtr ks ⋆ (FullK6Frame c L s ⋆ R)) m := by
    rw [fullMem_eq_k6Frame hscr_len] at hm; exact k6Mem_to_amem hsh (sep_ac hm)
  clear hm
  obtain ⟨Rfr, hRfr⟩ : ∃ Rfr : Mem 64 → Prop, Rfr = (FullK6Frame c L s ⋆ R) := ⟨_, rfl⟩
  have hfinish : ∀ (ok : Bool) (ks' : K6State) (m' : Mem 64),
      K6Inv L P ks' → ks'.nv = ks.nv → K6TailEq L ks ks' → ks'.nassump = ks.nassump →
      ks'.assump = ks.assump → ks'.neq = ks.neq → (K6MemA L kPtr ks' ⋆ Rfr) m' →
      Q (ok, ()) m' := fun ok ks' m' hinv' hnv' htail' hna' hass' hneq' hm' =>
    k6_flip_finish_post hlen hL_len hkb_le hQ ok ks' m' hinv' hnv' htail' hna' hass' hneq'
      (hRfr ▸ hm')
  obtain ⟨hv_eq, hv_lt⟩ := k6_bv32_div2_lt hlit_lt
  have hlit_mv2 : lit.toNat < sz2V L := by unfold sz2V; omega
  have hv_mv : (lit >>> (1 : Nat)).toNat < szV L := by unfold szV; omega
  have hsc_lt : c.scratch_cap < 2 ^ 64 := Nat.lt_trans c.hscr (by unfold dimacsBound; decide)
  c0_hsteps_nogrp
  refine k6_maxV_call_step hMaxV hsc_lt ?_
  have hmv32_eq := k6_flip_mv32_eq hL_mv
  c0_hsplit
  · exfalso; have hmv0 : L.mv32 = 0#32 := by rw [← hmv32_eq]; exact ‹_›
    have h0 := congrArg BitVec.toNat hmv0
    change (BitVec.ofNat 32 L.maxV).toNat = 0 at h0
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h0; omega
  · rw [hmv32_eq]
    c0_hsteps_nogrp; rw [k6_ptr_base L c.pScratchBuf]
    have hmA : (K6MemA L kPtr ks ⋆ Rfr) m := by rw [hRfr]; exact hmA0
    clear hmA0
    have hret_f : (K6MemA L kPtr ks ⋆ Rfr) m → Q (false, ()) m :=
      hfinish false ks m hinv rfl (k6TailEq_refl L ks) rfl rfl rfl
    c0_hsplit
    · c0_hsteps!; exact hret_f hmA
    · c0_hsplit
      · c0_hsteps!; exact hret_f hmA
      · c0_hsplit
        · c0_hsteps!; exact hret_f hmA
        · c0_hsplit
          · c0_hsteps!; exact hret_f hmA
          · have hval1 : ks.vals[lit.toNat]? = some 1#32 := by
              have hc : ks.vals[lit.toNat]?.getD 0#32 = 1#32 := ‹_›
              rw [List.getElem?_eq_getElem (by rw [hsh.vals_len]; exact hlit_mv2),
                Option.getD_some] at hc
              rw [List.getElem?_eq_getElem (by rw [hsh.vals_len]; exact hlit_mv2), hc]
            have hlvl_nz : ks.lvlArr[(lit >>> (1 : Nat)).toNat]?.getD 0#32 ≠ 0#32 := ‹_›
            obtain ⟨ch0, hwc0⟩ := K6WChainCursor.init hsh hnv hinv.watches hlit_lt
            c0_hsteps_nogrp
            refine wp_while_break_state
              (projBrk :=
                fun bst : BitVec 32 × BitVec 32 × BitVec 64 × BitVec 64 × Bool × K6State =>
                (bst.2.1, bst.1, bst.2.2.1, bst.2.2.2.1, bst.2.2.2.2.1, ()))
              (fun bst m' => K6Inv L P bst.2.2.2.2.2 ∧
                bst.2.2.2.2.2.nv = ks.nv ∧ K6TailEq L ks bst.2.2.2.2.2 ∧
                bst.2.2.2.2.2.nassump = ks.nassump ∧ bst.2.2.2.2.2.assump = ks.assump ∧
                bst.2.2.2.2.2.vals = ks.vals ∧ bst.2.2.2.2.2.lvlArr = ks.lvlArr ∧
                bst.2.2.2.2.2.neq = ks.neq ∧ bst.2.2.2.2.2.max_v = L.mv32 ∧
                (K6MemA L kPtr bst.2.2.2.2.2 ⋆ Rfr) m')
              (α := BitVec 32 × BitVec 32 × BitVec 64 × BitVec 64 × List Nat × List Nat ×
                K6State × List (List Nat))
              (fun st => (st.2.1, st.1, st.2.2.1, st.2.2.2.1, ()))
              (fun st => st.2.2.2.2.2.1.length)
              (fun st m' => K6WChainCursor st.2.2.2.2.2.2.1 lit.toNat st.2.2.2.2.2.2.2
                  st.2.2.2.2.1 st.2.2.2.2.2.1 st.1 st.2.1 ∧
                K6Inv L P st.2.2.2.2.2.2.1 ∧ st.2.2.2.2.2.2.1.nv = ks.nv ∧
                K6TailEq L ks st.2.2.2.2.2.2.1 ∧ st.2.2.2.2.2.2.1.nassump = ks.nassump ∧
                st.2.2.2.2.2.2.1.assump = ks.assump ∧ st.2.2.2.2.2.2.1.vals = ks.vals ∧
                st.2.2.2.2.2.2.1.lvlArr = ks.lvlArr ∧ st.2.2.2.2.2.2.1.neq = ks.neq ∧
                st.2.2.2.2.2.2.1.max_v = L.mv32 ∧
                (K6MemA L kPtr st.2.2.2.2.2.2.1 ⋆ Rfr) m') ?_ ?_ ?_
            · rintro B ⟨_, _, visits, ticks, ok, ksB⟩ m'
                ⟨hinvB, b_nv, b_tl, b_na, b_as, b_va, b_la, b_nq, _b_mv, hmB⟩
              dsimp only at hinvB b_nv b_tl b_na b_as b_va b_la b_nq hmB
              c0_hsteps_nogrp; k6_call hAddTicks
              refine ⟨L, ksB, Rfr, hinvB.shapes, (k6MemA_to_mem hmB).2, fun tk' m2 hm2 => ?_⟩
              have hinvT := k6AddTicks_preserves_inv hinvB tk'
              have hmAT := k6Mem_to_amem hinvT.shapes hm2
              have htlT := k6TailEq_trans b_tl (k6TailEq_of_putHdr_ne_nv (f := .ticks)
                (by decide) tk')
              c0_hsplit
              · obtain ⟨_, hn_lt⟩ := k6_bv32_xor1_lt hlit_lt
                have hnl_mv2 : (lit ^^^ 1#32).toNat < sz2V L := by unfold sz2V; omega
                have hlit_ltT : lit.toNat < 2 * (ksB.putHdr .ticks tk').nv.toNat := by
                  k6_field; rw [b_nv]; exact hlit_lt
                have hvalT : (ksB.putHdr .ticks tk').vals[lit.toNat]? = some 1#32 := by
                  k6_field; rw [b_va]; exact hval1
                have hlvlT : (ksB.putHdr .ticks tk').lvlArr[(lit >>> (1 : Nat)).toNat]?.getD 0#32 ≠
                    0#32 := by k6_field; rw [b_la]; exact hlvl_nz
                have hfin := k6FlipFinish_preserves hinvT hlit_ltT hvalT hlvlT
                have htlF := k6TailEq_trans htlT (k6TailEq_of_k6FlipFinish lit hlit_ltT)
                c0_hsteps!
                exact hfinish true _ _ hfin (by k6_field; exact b_nv) htlF
                  (by k6_field; exact b_na) (by k6_field; exact b_as) (by k6_field; exact b_nq)
                  ‹_›
              · c0_hsteps!
                exact hfinish false _ m2 hinvT (by k6_field; exact b_nv) htlT
                  (by k6_field; exact b_na) (by k6_field; exact b_as) (by k6_field; exact b_nq)
                  hmAT
            · rintro B L1 ⟨prev, w, visits, ticks, done, todo, ksW, chW⟩ m'
                hB ih ⟨hwc, hinvW, w_nv, w_tl, w_na, w_as, w_va, w_la, w_nq, w_mv, hmW⟩
              dsimp only at hwc hinvW w_nv w_tl w_na w_as w_va w_la w_nq w_mv hmW ⊢
              have hshW := hinvW.shapes; have hclW := hinvW.clauses
              have hnvW := hclW.nv_le; have hncW := hclW.nc_le
              have hlit_ltW : lit.toNat < 2 * ksW.nv.toNat := w_nv ▸ hlit_lt
              c0_hsplit
              · have hw_ne : w ≠ 0xFFFFFFFF#32 := by bv_omega
                obtain ⟨w0, todo', hw0_len, rfl, rfl, hw0_nc, hw0_mc2, hw_tn, hw_div2, hw_mod2,
                    hsz_ge, har_slot, hbv_nv, hbv_mem, hbin_iff, hbin_eq, _⟩ :=
                  hwc.step_unfold hncW hlit_ltW hw_ne
                have hw0_2cl : w0 < sz2Cl L := by unfold sz2Cl; exact hw0_mc2
                have hw0_bv2 : (BitVec.ofNat 32 w0).toNat < sz2Cl L := by rw [hw_tn]; exact hw0_2cl
                have hcid_lt : w0 / 2 < ksW.nc.toNat := by omega
                have hcid_cl : w0 / 2 < szCl L := by unfold szCl K6Layout.maxCl at *; omega
                have hbv_mv2 : ((ksW.wblit[w0]?.getD 0#32) &&& 0x7FFFFFFF#32).toNat < sz2V L := by
                  unfold sz2V; omega
                have hbv_mv2' : ((ksW.wblit[(BitVec.ofNat 32 w0).toNat]?.getD 0#32) &&&
                    0x7FFFFFFF#32).toNat < sz2V L := by rw [hw_tn]; exact hbv_mv2
                c0_hsplit
                · c0_hsplit
                  · c0_hsteps!
                    exact hB (prev, BitVec.ofNat 32 w0, visits + 1#64, ticks, false, ksW) m'
                      ⟨hinvW, w_nv, w_tl, w_na, w_as, w_va, w_la, w_nq, w_mv, hmW⟩
                  · c0_hsplit
                    · c0_hsteps!
                      exact hB (prev, BitVec.ofNat 32 w0, visits + 1#64, ticks, false, ksW) m'
                        ⟨hinvW, w_nv, w_tl, w_na, w_as, w_va, w_la, w_nq, w_mv, hmW⟩
                    · have hskip := k6WatchSkip_cursor hshW hwc hw0_len
                      c0_hsteps!; rw [hw_tn]
                      exact ih (BitVec.ofNat 32 w0, ksW.wnext[w0]?.getD 0#32, visits + 1#64,
                          ticks, done ++ [w0], todo', ksW, chW) _ (by simp)
                        ⟨hskip, hinvW, w_nv, w_tl, w_na, w_as, w_va, w_la, w_nq, w_mv, hmW⟩
                · have hnonbin : (ksW.wblit[w0]?.getD 0#32 &&& 0x80000000#32) = 0#32 := by
                    rw [← hw_tn]; bv_omega
                  have hsz_ne2 : k6ClauseSize ksW (w0 / 2) ≠ 2 := fun h2 =>
                    absurd (hbin_iff.mpr h2) (by rw [hnonbin]; simp)
                  refine LeanQbe.T.wp_unroll_group fun Jnk hJnk => ?_
                  have hnk : Jnk () m' := by
                    refine hJnk () m' ?_
                    obtain ⟨har_ok, hother_nv, hot_mem, hslot_bv, hslot_other_bv, hcl_off_add,
                      hcl_off_ar, hother_mv2, _⟩ :=
                      k6_nonbin_setup hinvW hcid_lt hw_div2 hw_mod2
                    let other := ksW.arena[k6ClauseOff ksW (w0 / 2) + (w0 % 2 ^^^ 1)]?.getD 0#32
                    have hw_sh1 : (BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat = w0 / 2 := hw_div2
                    have hoth_arr_lt :
                        (ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD
                          0#32 + (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^
                          (1 : BitVec 32))).toNat]?.getD 0#32).toNat < sz2V L := by
                      rw [hw_sh1, hcl_off_add]; exact hother_mv2
                    c0_hsteps_nogrp
                    refine LeanQbe.T.wp_unroll_group fun Jsc hJsc => ?_
                    have hsc : Jsc () m' := by
                      refine hJsc () m' ?_
                      let sz := ksW.clSz[w0 / 2]?.getD 0#32
                      let off := ksW.clOff[w0 / 2]?.getD 0#32
                      refine wp_while_break_state
                        (projBrk := fun b : BitVec 32 × BitVec 32 × BitVec 32 =>
                          (b.1, b.2.1, b.2.2, ()))
                        (fun b mb => mb = m' ∧ (b.2.1 = 0xFFFFFFFF#32 ∨
                          (2 ≤ b.2.1.toNat ∧ b.2.1.toNat < sz.toNat ∧
                            b.2.2 = ksW.arena[off.toNat + b.2.1.toNat]?.getD 0#32 ∧
                            b.2.2 ≠ lit ∧ ksW.vals[b.2.2.toNat]? = some 1#32)))
                        (projLp := fun st : BitVec 32 => (st, ())) (fun st => sz.toNat - st.toNat)
                        (fun st m'' => m'' = m' ∧ st.toNat ≤ sz.toNat ∧ 2 ≤ st.toNat) ?_ ?_ ?_
                      · rintro B2 ⟨_, ri, repl⟩ mb ⟨rfl, hbrk⟩; dsimp only at hbrk ⊢
                        c0_hsplit
                        · c0_hsteps!
                          exact hB (prev, BitVec.ofNat 32 w0, visits + 1#64, ticks + 1#64,
                            false, ksW) mb ⟨hinvW, w_nv, w_tl, w_na, w_as, w_va, w_la, w_nq,
                              w_mv, hmW⟩
                        · have hri_ne : ri ≠ 0xFFFFFFFF#32 := by bv_omega
                          obtain ⟨hri_ge, hri_lt, hrepl_eq, hrepl_ne, _⟩ :=
                            hbrk.resolve_left hri_ne
                          obtain ⟨hrl_inv, ⟨chW', hwc'⟩⟩ :=
                            k6WatchReloc_preserves hinvW hlit_ltW hwc hri_ge hri_lt
                              (fun h => hrepl_ne (BitVec.eq_of_toNat_eq h)) rfl hrepl_eq
                          obtain ⟨hri_cap, hri_lit⟩ := har_ok ri.toNat hri_lt
                          obtain ⟨hslot_cap, _⟩ :=
                            har_ok (w0 % 2) (by have := Nat.mod_lt w0 (by decide : 0 < 2); omega)
                          obtain ⟨hslot_off_eq, hslot_ar, hri_off_eq, hri_ar⟩ :=
                            k6_reloc_addrs hw_div2 hslot_bv hslot_cap hri_cap
                          have hsw_lit : BitVec.setWidth 32 lit = lit := by
                            apply BitVec.eq_of_toNat_eq; simp
                          have hlit_bn : BitVec.ofNat 32 lit.toNat = lit := by simp
                          have hw_sh_bv : (BitVec.ofNat 32 w0 >>> 1#32).toNat = w0 / 2 := by
                            change (BitVec.ofNat 32 w0 >>> (1#32 : BitVec 32).toNat).toNat = w0 / 2
                            exact hw_div2
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
                          have htlR := k6_reloc_tailEq
                            (w := BitVec.ofNat 32 w0) (repl := repl)
                            (other := ksW.arena[k6ClauseOff ksW (w0 / 2) +
                              (w0 % 2 ^^^ 1)]?.getD 0#32)
                            (nxt := ksW.wnext[w0]?.getD 0#32) (prev := prev)
                            (arOff := k6ClauseOff ksW (w0 / 2)) (slot := w0 % 2) (ri := ri.toNat)
                            w_tl hlit_ltW (by rw [hrepl_eq]; exact hri_lit)
                          have hcl_bv_eq : (ksW.clOff[w0 / 2]?.getD 0#32 +
                              (BitVec.ofNat 32 w0 &&& 1#32 ^^^ 1#32)).toNat =
                              (ksW.clOff[w0 / 2]?.getD 0#32).toNat + (w0 % 2 ^^^ 1) := hcl_off_add
                          let nxt := ksW.wnext[w0]?.getD 0#32
                          let ks1r : K6State := {
                            ksW with
                            arena := (ksW.arena.set (k6ClauseOff ksW (w0 / 2) + w0 % 2) repl).set
                              (k6ClauseOff ksW (w0 / 2) + ri.toNat) (BitVec.ofNat 32 lit.toNat),
                            whead := if prev = 0xFFFFFFFF#32 then ksW.whead.set lit.toNat nxt
                              else ksW.whead,
                            wnext := if prev = 0xFFFFFFFF#32 then ksW.wnext
                              else ksW.wnext.set prev.toNat nxt }
                          let other :=
                            ksW.arena[k6ClauseOff ksW (w0 / 2) + (w0 % 2 ^^^ 1)]?.getD 0#32
                          c0_hsteps_nogrp
                          try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                          c0_hsplit <;> (
                            first
                            | have hpeq : prev = 0xFFFFFFFF#32 := by bv_omega
                            | (have hpne : prev ≠ 0xFFFFFFFF#32 := by bv_omega
                               have hprv_bd := hprv_lt hpne)
                            c0_hsteps!; try rw [hw_tn]
                            refine ih (prev, nxt, visits + 1#64, ticks + 1#64,
                                done, todo', k6WatchStep0 ks1r (BitVec.ofNat 32 w0) repl other,
                                chW') _ (by simp) ⟨hwc', hrl_inv, w_nv, htlR, w_na, w_as, w_va,
                                w_la, w_nq, w_mv, Eq.mp (congrArg (fun x =>
                                  (K6MemA L kPtr x ⋆ Rfr) _)
                                  ?_) hm⟩
                            dsimp only [k6WatchStep0, ks1r, nxt, other, k6ClauseOff]
                            first | simp only [hpeq, ↓reduceIte] | simp only [hpne, ↓reduceIte]
                            k6_ext <;> (first
                              | rfl
                              | { rw [hlit_bn]
                                  exact k6_reloc_arena_slot hw_div2 hw_sh_bv rfl hslot_bv hslot_cap
                                    hri_cap }
                              | { try rw [K6PtrTactics.k6_bv32_one]
                                  rw [show (BitVec.ofNat 32 w0 >>> OfNat.ofNat 1).toNat = w0 / 2
                                    from hw_div2, hcl_bv_eq] }
                              | { try rw [hw_tn]; try rw [K6PtrTactics.k6_bv32_one]
                                  try rw [show (BitVec.ofNat 32 w0 >>> OfNat.ofNat 1).toNat =
                                    w0 / 2 from hw_div2]
                                  try rw [hw_sh_bv]; try rw [hcl_bv_eq]; try rfl }))
                      · intro B2 L2 r m1 hB2 ih1 ⟨rfl, hr_le, hr2⟩
                        dsimp only at hr_le hr2 ⊢
                        have hw_md : w0 % 2 ^ 32 / 2 = w0 / 2 := by
                          rw [Nat.mod_eq_of_lt (by unfold K6Layout.maxCl at hw0_mc2; omega)]
                        c0_hsplit
                        · have hr_lt : r.toNat < sz.toNat := by
                            have hc0 : r.toNat < (ksW.clSz[w0 % 2 ^ 32 / 2]?.getD 0#32).toNat := by
                              bv_omega
                            rwa [hw_md] at hc0
                          obtain ⟨hr_cap, hr_lit⟩ := har_ok r.toNat hr_lt
                          have hco : (ksW.clOff[w0 / 2]?.getD 0#32 + r).toNat =
                              k6ClauseOff ksW (w0 / 2) + r.toNat := by
                            unfold k6ClauseOff at hr_cap ⊢; unfold dimacsBound at hac_b; bv_omega
                          have hr_ar : (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD
                              0#32 + r).toNat < szAr L := by
                                unfold szAr; rw [hw_sh1, hco]; exact hr_cap
                          have hcand_mv2 : (ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>>
                              (1 : Nat)).toNat]?.getD 0#32 + r).toNat]?.getD 0#32).toNat <
                              sz2V L := by rw [hw_sh1, hco]; unfold sz2V; omega
                          have hr1_wrap : (r + 1#32).toNat = r.toNat + 1 := by
                            have := (hclW.cl_wf (w0 / 2) (Nat.div_lt_of_lt_mul hw0_nc)).2.1
                            have := hclW.alen_le; unfold dimacsBound at hac_b
                            have : sz.toNat < 2 ^ 28 := by
                              change k6ClauseSize ksW (w0 / 2) < 2 ^ 28; omega
                            bv_omega
                          c0_hsteps_nogrp
                          refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                          c0_hsplit
                          · have hco' : (ksW.clOff[w0 % 2 ^ 32 / 2]?.getD 0#32 + r).toNat =
                                off.toNat + r.toNat := by rw [hw_md]; exact hco
                            have hne_cand : ksW.arena[off.toNat + r.toNat]?.getD 0#32 ≠ lit := by
                              have hc0 : ksW.arena[(ksW.clOff[w0 % 2 ^ 32 / 2]?.getD 0#32 +
                                  r).toNat]?.getD 0#32 ≠ lit := by bv_omega
                              rwa [hco'] at hc0
                            c0_hsplit
                            · have hc_val1 : ksW.vals[(ksW.arena[off.toNat +
                              r.toNat]?.getD 0#32).toNat]? =
                                  some 1#32 := by
                                have hvl : (ksW.arena[off.toNat +
                                  r.toNat]?.getD 0#32).toNat < ksW.vals.length := by
                                  rw [hshW.vals_len]; change (ksW.arena[k6ClauseOff ksW (w0 / 2) +
                                    r.toNat]?.getD 0#32).toNat < 2 * L.maxV; omega
                                have hc0 : ksW.vals[(ksW.arena[(ksW.clOff[w0 % 2 ^ 32 / 2]?.getD
                                    0#32 + r).toNat]?.getD 0#32).toNat]?.getD 0#32 = 1#32 := by
                                      bv_omega
                                rw [hco'] at hc0
                                exact k6_vals_some hshW
                                  (by unfold sz2V; rw [hshW.vals_len] at hvl; exact hvl) hc0
                              c0_hsteps!; rw [hw_sh1, hco]
                              exact hB2 (r, r, ksW.arena[off.toNat + r.toNat]?.getD 0#32) _
                                ⟨rfl, Or.inr ⟨hr2, hr_lt, rfl, hne_cand, hc_val1⟩⟩
                            · c0_hsteps!
                              exact ih1 (r + 1#32) _ (by rw [hr1_wrap]; omega)
                                ⟨rfl, by rw [hr1_wrap]; omega, by rw [hr1_wrap]; omega⟩
                          · c0_hsteps!
                            exact ih1 (r + 1#32) _ (by rw [hr1_wrap]; omega)
                              ⟨rfl, by rw [hr1_wrap]; omega, by rw [hr1_wrap]; omega⟩
                        · c0_hsteps!; exact hB2 (r, 0xFFFFFFFF#32, 0#32) _ ⟨rfl, Or.inl rfl⟩
                      · intro B2 L2 _ hL2; c0_hsteps!; exact hL2 2#32 m' ⟨rfl, hsz_ge, le_refl _⟩
                    c0_hsplit
                    · c0_hsplit
                      · obtain ⟨hkp_inv, hkp_wc⟩ :=
                          k6WatchKeep_preserves hinvW hlit_ltW hwc hother_nv hot_mem hsz_ne2
                        have htlK := k6TailEq_trans w_tl
                          (k6TailEq_putArr_nonTail (L := L) (ks := ksW) (f := .wblit)
                            (by decide) w0 other)
                        c0_hsteps!; rw [hw_tn]
                        refine ih (BitVec.ofNat 32 w0, ksW.wnext[w0]?.getD 0#32, visits + 1#64,
                            ticks + 1#64, done ++ [w0], todo', ksW.putArr .wblit w0 other, chW)
                          _ (by simp) ⟨hkp_wc, hkp_inv, by k6_field; exact w_nv, htlK,
                            by k6_field; exact w_na, by k6_field; exact w_as,
                            by k6_field; exact w_va, by k6_field; exact w_la,
                            by k6_field; exact w_nq, by k6_field; exact w_mv, ?_⟩
                        refine Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ Rfr) _) ?_) ‹_›
                        k6_ext <;> (first | rfl | {
                          dsimp only [other]; try rw [hw_tn, hw_sh1]; try rw [hcl_off_add]
                          try dsimp only [k6ClauseOff]; try rfl })
                      · refine head_wp_jump rfl rfl hsc
                    · refine head_wp_jump rfl rfl hsc
                  c0_hsplit
                  · c0_hsplit
                    · have hskip := k6WatchSkip_cursor hshW hwc hw0_len
                      c0_hsteps!; rw [hw_tn]
                      exact ih (BitVec.ofNat 32 w0, ksW.wnext[w0]?.getD 0#32, visits + 1#64,
                          ticks, done ++ [w0], todo', ksW, chW) _ (by simp)
                        ⟨hskip, hinvW, w_nv, w_tl, w_na, w_as, w_va, w_la, w_nq, w_mv, hmW⟩
                    · refine head_wp_jump rfl rfl hnk
                  · refine head_wp_jump rfl rfl hnk
              · c0_hsteps!
                exact hB (prev, w, visits, ticks, true, ksW) m'
                  ⟨hinvW, w_nv, w_tl, w_na, w_as, w_va, w_la, w_nq, w_mv, hmW⟩
            · intro B L1 hB hL
              exact wp_jump_state (proj :=
                  fun st : BitVec 32 × BitVec 32 × BitVec 64 × BitVec 64 × List Nat ×
                    List Nat × K6State × List (List Nat) =>
                  (st.2.1, st.1, st.2.2.1, st.2.2.2.1, ()))
                (0xFFFFFFFF#32, ks.whead[lit.toNat]?.getD 0#32, 0#64, 1#64,
                  [], ch0[lit.toNat]?.getD [], ks, ch0) rfl
                (hL _ m ⟨hwc0, hinv, rfl, k6TailEq_refl L ks, rfl, rfl, rfl, rfl, rfl,
                  hmv_eq_ks, hmA⟩)

end LeanQbe.T.Examples.Kissat.Proof.Kitten

end
