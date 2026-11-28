/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Kitten.LemmasBtAdd

/-!
# Step-13 `Func.wp` Proof for `full_k6_add_clause` (`6/14`, `Kissat.Proof.Kitten.WpAddClause`)

Certifies `full_k6_add_clause_wp` (`step13K6AddClauseSpec`) with `glue_used[33]` HWM tracking,
preserving `K6HwmClean`, `K6Inv`, `K6TrailSynced`, and `K6LitsBounded`.
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
open LeanQbe.T.Examples.Kissat.Proof.Kitten.Spec
open LeanQbe.T.Examples.Kissat.Src.Kitten

open K6MemATactics K6PtrTactics
open scoped K6MemATactics K6PtrTactics

/-! ## 1. Step-13 HWM Helpers -/

private theorem s13_hwm_clean_of_range {L : K6Layout} {hw0 hw' : BitVec 32} {ks ks' : K6State}
    (hhwm : K6HwmClean L hw0 ks) (hfin : hw0 = 0xFFFFFFFF#32 ∧ hw' = 0xFFFFFFFF#32 ∨
      (hw0 ≠ 0xFFFFFFFF#32 ∧ hw0.toNat ≤ hw'.toNat ∧ hw'.toNat ≤ L.maxV ∧
        ∀ v, hw'.toNat ≤ v → v < L.maxV →
          ks'.lvlArr[v]? = ks.lvlArr[v]? ∧ ks'.rsn[v]? = ks.rsn[v]? ∧
          ks'.flags[v]? = ks.flags[v]? ∧ ks'.vals[2 * v]? = ks.vals[2 * v]? ∧
          ks'.vals[2 * v + 1]? = ks.vals[2 * v + 1]? ∧
          ks'.whead[2 * v]? = ks.whead[2 * v]? ∧
          ks'.whead[2 * v + 1]? = ks.whead[2 * v + 1]?)) :
    K6HwmClean L hw' ks' := by
  rcases hfin with ⟨rfl, rfl⟩ | ⟨hne, hle1, hle2, heq⟩
  · exact Or.inl rfl
  · rcases hhwm with rfl | ⟨_, hcl⟩
    · exact absurd rfl hne
    · refine Or.inr ⟨hle2, fun v hvw hvm => ?_⟩
      have ha := heq v hvw hvm; have hc := hcl v (Nat.le_trans hle1 hvw) hvm
      rw [ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2.1, ha.2.2.2.2.2.1, ha.2.2.2.2.2.2]
      exact hc

private theorem s13_hwm_eq_of_ticks_watch {L : K6Layout} {ks : K6State} (tk cid l0 l1 : BitVec 32)
    {hw : Nat} (hl0 : l0.toNat / 2 < hw) (hl1 : l1.toNat / 2 < hw) :
    let st := k6WatchStep (ks.putHdr .ticks tk) cid l0 l1
    ∀ v, hw ≤ v → v < L.maxV →
      st.lvlArr[v]? = ks.lvlArr[v]? ∧ st.rsn[v]? = ks.rsn[v]? ∧
      st.flags[v]? = ks.flags[v]? ∧ st.vals[2 * v]? = ks.vals[2 * v]? ∧
      st.vals[2 * v + 1]? = ks.vals[2 * v + 1]? ∧ st.whead[2 * v]? = ks.whead[2 * v]? ∧
      st.whead[2 * v + 1]? = ks.whead[2 * v + 1]? := fun v hv _ => by
  dsimp only [k6WatchStep, k6WatchStep0, K6State.putHdr]
  exact ⟨rfl, rfl, rfl, rfl, rfl,
    by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)],
    by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]⟩

private theorem s13_hwm_eq_of_assign {L : K6Layout} {ks : K6State} {lit rsn : BitVec 32}
    {hw : Nat} (hlit : lit.toNat / 2 < hw) :
    let st := k6AssignStep ks lit rsn
    ∀ v, hw ≤ v → v < L.maxV →
      st.lvlArr[v]? = ks.lvlArr[v]? ∧ st.rsn[v]? = ks.rsn[v]? ∧
      st.flags[v]? = ks.flags[v]? ∧ st.vals[2 * v]? = ks.vals[2 * v]? ∧
      st.vals[2 * v + 1]? = ks.vals[2 * v + 1]? ∧ st.whead[2 * v]? = ks.whead[2 * v]? ∧
      st.whead[2 * v + 1]? = ks.whead[2 * v + 1]? := fun v hv _ => by
  have hdiv : (lit >>> 1).toNat = lit.toNat / 2 := by
    rw [show (lit >>> 1) = lit >>> (1 : Nat) from rfl, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, Nat.pow_one]
  dsimp only [k6AssignStep]; rw [hdiv, show (lit ^^^ 1#32).toNat = lit.toNat ^^^ 1 from by simp]
  rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;>
    exact ⟨List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega),
      by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)],
      by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)], rfl, rfl⟩

private theorem s13_add_clause_hwm_id {L : K6Layout} {ks : K6State} {hw0 hw' : BitVec 32}
    {gu' : List (BitVec 32)} {sz : BitVec 32} {xs : List (BitVec 32)}
    (hgu'_33 : gu'[33]? = some hw') (hhwm0' : K6HwmClean L hw0 ks)
    (hhwm_rel : hw0 = 0xFFFFFFFF#32 ∧ hw' = 0xFFFFFFFF#32 ∨
      hw0 ≠ 0xFFFFFFFF#32 ∧ hw0.toNat ≤ hw'.toNat ∧ hw'.toNat ≤ L.maxV ∧
        ∀ i < sz.toNat, (xs[i]?.getD 0#32).toNat / 2 + 1 ≤ hw'.toNat) :
    K6HwmClean L (gu'[33]?.getD 0#32) ks := by
  rw [hgu'_33, Option.getD_some]; refine s13_hwm_clean_of_range hhwm0' ?_
  rcases hhwm_rel with ⟨h0, h1⟩ | ⟨h0, h1, h2, _⟩
  · exact Or.inl ⟨h0, h1⟩
  · exact Or.inr ⟨h0, h1, h2, fun v _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem s13_add_clause_sz1_bnd {L : K6Layout} {ks : K6State} {xs : List (BitVec 32)}
    {sz : BitVec 32} (h0_xs : 0 < xs.length) (h0_sz : 0 < sz.toNat)
    (htrl_len : ks.trl.length = L.maxV) (hte_lt : ks.trl_end.toNat < ks.nv.toNat)
    (hnv_le : ks.nv.toNat ≤ L.maxV) :
    ∀ M, (∀ i < sz.toNat, (xs[i]?.getD 0#32).toNat < 2 * M) →
      K6LitsBounded M ks → (∀ l ∈ k6TrailLits ks, l < 2 * M) →
      K6LitsBounded M (k6AssignStep ks xs[0] 0xFFFFFFFF#32) ∧
        (∀ l ∈ k6TrailLits (k6AssignStep ks xs[0] 0xFFFFFFFF#32), l < 2 * M) := by
  intro M hM hBM hTM; refine ⟨⟨hBM.1, hBM.2⟩, fun l hl => ?_⟩
  unfold k6TrailLits at hl; rw [List.mem_map] at hl; obtain ⟨b, hb, rfl⟩ := hl
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  have hi' : i < (ks.trl_end + 1#32).toNat :=
    Nat.lt_of_lt_of_le hi (by dsimp only [k6AssignStep]; exact List.length_take_le _ _)
  have hte1 : (ks.trl_end + 1#32).toNat = ks.trl_end.toNat + 1 := by bv_omega
  simp only [List.getElem_take, k6AssignStep]
  have htrl_lt : ks.trl_end.toNat < ks.trl.length := by rw [htrl_len]; omega
  by_cases hie : i = ks.trl_end.toNat
  · subst hie; rw [List.getElem_set_self (by rw [List.length_set]; exact htrl_lt)]
    have := hM 0 h0_sz; rwa [List.getElem?_eq_getElem h0_xs, Option.getD_some] at this
  · have hte1_lt : i < ks.trl_end.toNat := by rw [hte1] at hi'; omega
    rw [List.getElem_set_ne (by omega)]
    refine hTM _ (List.mem_map.mpr ⟨ks.trl[i]'(by omega), ?_, rfl⟩)
    rw [List.mem_iff_getElem]
    exact ⟨i, by rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt htrl_lt)]; exact hte1_lt,
      by simp⟩

private theorem s13_add_clause_ge2_post {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks st stM : K6State} {sz tk' hw0 hw' : BitVec 32} {xs gu' : List (BitVec 32)}
    (hlvl0 : ks.lvl = 0#32) (hsz2 : 2 ≤ sz.toNat) (hxs0 : 0 < xs.length) (hxs1 : 1 < xs.length)
    (hstM_eq : stM = (((({ ks with arena := st.arena } : K6State).putHdr .alen
      (ks.alen + sz)).putArr .clOff ks.nc.toNat ks.alen).putArr .clSz ks.nc.toNat sz).putHdr
      .nc (ks.nc + 1#32))
    (hgu'_33 : gu'[33]? = some hw') (hhwm0' : K6HwmClean L hw0 ks)
    (hhwm_rel : hw0 = 0xFFFFFFFF#32 ∧ hw' = 0xFFFFFFFF#32 ∨
      hw0 ≠ 0xFFFFFFFF#32 ∧ hw0.toNat ≤ hw'.toNat ∧ hw'.toNat ≤ L.maxV ∧
        ∀ i < sz.toNat, (xs[i]?.getD 0#32).toNat / 2 + 1 ≤ hw'.toNat)
    (hpres2 : K6Inv L P (k6WatchStep stM ks.nc xs[0] xs[1]) ∧
      K6TrailSynced (k6WatchStep stM ks.nc xs[0] xs[1]) ∧
      (k6WatchStep stM ks.nc xs[0] xs[1]).lvl = ks.lvl ∧
      (k6WatchStep stM ks.nc xs[0] xs[1]).nv = ks.nv ∧
      (k6WatchStep stM ks.nc xs[0] xs[1]).nassump = ks.nassump ∧
      (k6WatchStep stM ks.nc xs[0] xs[1]).assump = ks.assump ∧
      (k6WatchStep stM ks.nc xs[0] xs[1]).trl_end = ks.trl_end ∧
      (k6WatchStep stM ks.nc xs[0] xs[1]).unass = ks.unass ∧
      (k6WatchStep stM ks.nc xs[0] xs[1]).incons = ks.incons ∧
      (∀ M, (∀ j < sz.toNat, (xs[j]?.getD 0#32).toNat < 2 * M) →
        K6LitsBounded M ks → K6LitsBounded M (k6WatchStep stM ks.nc xs[0] xs[1]))) :
    let ksF := k6WatchStep (stM.putHdr .ticks tk') ks.nc xs[0] xs[1]
    K6HwmClean L (gu'[33]?.getD 0#32) ksF ∧ K6Inv L P ksF ∧ K6TrailSynced ksF ∧
      ksF.lvl = 0#32 ∧ ksF.nv = ks.nv ∧ ksF.nassump = ks.nassump ∧ ksF.assump = ks.assump ∧
      (2 ≤ sz.toNat → ksF.trl_end = ks.trl_end ∧ ksF.prop = ks.prop ∧
        ksF.unass = ks.unass ∧ ksF.incons = ks.incons) ∧
      (∀ M, (∀ i < sz.toNat, (xs[i]?.getD 0#32).toNat < 2 * M) →
        K6LitsBounded M ks → (∀ l ∈ k6TrailLits ks, l < 2 * M) →
        K6LitsBounded M ksF ∧ (∀ l ∈ k6TrailLits ksF, l < 2 * M)) := by
  let ksW := k6WatchStep stM ks.nc xs[0] xs[1]
  let ksF := k6WatchStep (stM.putHdr .ticks tk') ks.nc xs[0] xs[1]
  have hksF_eq : ksF = ksW.putHdr .ticks tk' := by
    dsimp only [ksF, ksW, k6WatchStep, k6WatchStep0]; k6_ext
  have hhwmF : K6HwmClean L (gu'[33]?.getD 0#32) ksF := by
    rw [hgu'_33, Option.getD_some]; refine s13_hwm_clean_of_range hhwm0' ?_
    rcases hhwm_rel with ⟨h0, h1⟩ | ⟨h0, h1, h2, hlt⟩
    · exact Or.inl ⟨h0, h1⟩
    · have hx0 := hlt 0 (by omega); have hx1 := hlt 1 (by omega)
      rw [List.getElem?_eq_getElem hxs0, Option.getD_some] at hx0
      rw [List.getElem?_eq_getElem hxs1, Option.getD_some] at hx1
      refine Or.inr ⟨h0, h1, h2, fun v hvw hvm => ?_⟩
      have hsub : ksF.lvlArr = ks.lvlArr ∧ ksF.rsn = ks.rsn ∧ ksF.flags = ks.flags ∧
          ksF.vals = ks.vals ∧
          ksF.whead = (k6WatchStep (ks.putHdr .ticks tk') ks.nc xs[0] xs[1]).whead := by
        dsimp only [ksF, k6WatchStep, k6WatchStep0]; rw [hstM_eq]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> k6_field
      have heq := s13_hwm_eq_of_ticks_watch (L := L) (ks := ks) tk' ks.nc xs[0] xs[1]
        (by omega) (by omega) v hvw hvm
      dsimp only [k6WatchStep, k6WatchStep0, K6State.putHdr] at heq
      rw [hsub.1, hsub.2.1, hsub.2.2.1, hsub.2.2.2.1]
      dsimp only [k6WatchStep, k6WatchStep0] at hsub; rw [hsub.2.2.2.2]; exact heq
  have hge2F : 2 ≤ sz.toNat → ksF.trl_end = ks.trl_end ∧
      ksF.prop = ks.prop ∧ ksF.unass = ks.unass ∧ ksF.incons = ks.incons := fun _ => by
    have hprF : ksW.prop = ks.prop := by
      dsimp only [ksW, k6WatchStep, k6WatchStep0]; rw [hstM_eq]; k6_field
    rw [hksF_eq]
    exact ⟨hpres2.2.2.2.2.2.2.1, hprF, hpres2.2.2.2.2.2.2.2.1, hpres2.2.2.2.2.2.2.2.2.1⟩
  refine ⟨hhwmF,
    (by change K6Inv L P ksF; rw [hksF_eq]; exact k6AddTicks_preserves_inv hpres2.1 tk'),
    (by change K6TrailSynced ksF; rw [hksF_eq]; exact hpres2.2.1),
    by change ksF.lvl = 0#32; rw [hksF_eq]; k6_field; rw [hpres2.2.2.1]; exact hlvl0,
    by change ksF.nv = ks.nv; rw [hksF_eq]; k6_field; exact hpres2.2.2.2.1,
    by change ksF.nassump = ks.nassump; rw [hksF_eq]; k6_field; exact hpres2.2.2.2.2.1,
    by change ksF.assump = ks.assump; rw [hksF_eq]; k6_field; exact hpres2.2.2.2.2.2.1,
    hge2F, fun M hM hBM hTM =>
      ⟨by change K6LitsBounded M ksF; rw [hksF_eq]; exact hpres2.2.2.2.2.2.2.2.2.2 M hM hBM, by
        have hteF : ksF.trl_end = ks.trl_end := (hge2F hsz2).1
        have htrF : ksF.trl = ks.trl := by
          rw [hksF_eq]; dsimp only [ksW, k6WatchStep, k6WatchStep0]; rw [hstM_eq]; k6_field
        change ∀ l ∈ k6TrailLits ksF, l < 2 * M; simpa [k6TrailLits, hteF, htrF] using hTM⟩⟩

private theorem s13_hwm_step_bounds {L : K6Layout} {ks : K6State} {xs : List (BitVec 32)}
    {sz : BitVec 32} {xi : Nat} (hxi_lt : xi < sz.toNat) (hsz_le : sz.toNat ≤ xs.length)
    (hnv_le : ks.nv.toNat ≤ L.maxV) (hm_le : L.maxV ≤ 8192)
    (hxl : (xs[xi]?.getD 0#32).toNat < 2 * ks.nv.toNat) :
    (BitVec.ofNat 32 xi).toNat < xs.length ∧ (BitVec.ofNat 32 xi).toNat = xi ∧
      ((xs[xi]?.getD 0#32 >>> (1 : Nat)) + 1#32).toNat =
        (xs[xi]?.getD 0#32).toNat / 2 + 1 ∧
      ((xs[xi]?.getD 0#32 >>> (1 : Nat)) + 1#32).toNat ≤ L.maxV ∧
      (xs[xi % 2 ^ 32 % 2 ^ 64].toNat / 2 + 1) % 2 ^ 32 = (xs[xi]?.getD 0#32).toNat / 2 + 1 ∧
      BitVec.ofNat 32 xi + 1 = BitVec.ofNat 32 (xi + 1) := by
  have hxi_xs : xi < xs.length := by omega
  have hxi_eq : (BitVec.ofNat 32 xi).toNat = xi := by bv_omega
  rw [List.getElem?_eq_getElem hxi_xs, Option.getD_some] at hxl
  have hxv_eq : ((xs[xi]?.getD 0#32 >>> (1 : Nat)) + 1#32).toNat =
      (xs[xi]?.getD 0#32).toNat / 2 + 1 := by
    rw [List.getElem?_eq_getElem hxi_xs, Option.getD_some]; bv_omega
  have hxv_lt : ((xs[xi]?.getD 0#32 >>> (1 : Nat)) + 1#32).toNat ≤ L.maxV := by
    rw [hxv_eq, List.getElem?_eq_getElem hxi_xs, Option.getD_some]; omega
  have hhc_mod_eq : (xs[xi % 2 ^ 32 % 2 ^ 64].toNat / 2 + 1) % 2 ^ 32 =
      (xs[xi]?.getD 0#32).toNat / 2 + 1 := by
    have hmod : xi % 2 ^ 32 % 2 ^ 64 = xi := by omega
    simp only [hmod, List.getElem?_eq_getElem hxi_xs, Option.getD_some]
    exact Nat.mod_eq_of_lt (by omega)
  exact ⟨by bv_omega, hxi_eq, hxv_eq, hxv_lt, hhc_mod_eq,
    BitVec.eq_of_toNat_eq (by bv_omega)⟩

/-! ## 2. Parametric `Func.wp` Theorem for `full_k6_add_clause` (`6/14`) -/

/-- `6/14`: Parametric `Func.wp` proof for `full_k6_add_clause`. -/
theorem full_k6_add_clause_wp (Γ : Env) (hMaxV : Γ.Has "full_m6_max_v" m6MaxVSpec)
    (hAssign : Γ.Has "full_k6_assign" k6AssignSpec)
    (hAddTicks : Γ.Has "full_k6_add_ticks" k6AddTicksSpec)
    (hWatch : Γ.Has "full_k6_watch" k6WatchSpec) :
    ∀ args m Q X, step13K6AddClauseSpec args m Q X →
      Func.wp Γ full_k6_add_clause_body args m Q X := by
  rintro ⟨h, lits_ptr, sz, ⟨⟩⟩ m Q X ⟨c, s, P, L, scr, gu, xs, R, rfl, hlen, hscr_s, hgu_s,
    hL_scr, hL_mv, hinv, hsync, hlvl0, hsz_le, hsz_max, hxlits, hent, hhwm0, hm, hcont⟩
  subst hscr_s; subst hgu_s
  let ks := k6StateOfScratch L s.scratch.scratch_buf
  have hmL := L.hmaxV; have hnv_le := hinv.clauses.nv_le
  have hgu_len : 33 < s.scratch.glue_used.length := by rw [hlen.scratch_ok.glue_used_len]; omega
  let hw0 := s.scratch.glue_used[33]
  have hhwm0' : K6HwmClean L hw0 ks := by
    simpa [hw0, List.getElem?_eq_getElem hgu_len] using hhwm0
  have hscr_len : s.scratch.scratch_buf.length = L.scrLen :=
    hlen.scratch_ok.scratch_buf_len.trans hL_scr.symm
  have hkbase : L.k6Base ≤ s.scratch.scratch_buf.length := by
    rw [hscr_len]; unfold K6Layout.scrLen; omega
  have htk_len : (s.scratch.scratch_buf.take L.k6Base).length = L.k6Base :=
    List.length_take_of_le hkbase
  have hscr_c := c.hscr
  have hcap64 : c.scratch_cap < 2 ^ 64 := by unfold dimacsBound at hscr_c; omega
  have hmv32 : ((BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32) = L.mv32 := by
    unfold K6Layout.mv32; rw [← hL_mv]; apply BitVec.eq_of_toNat_eq; bv_omega
  c0_hsteps_nogrp
  refine wp_join_state1 (α := List (BitVec 32) × BitVec 32) Prod.snd
    (fun st m' => st.1.length = 64 ∧
      (∀ i < 64, i ≠ 33 → st.1[i]? = s.scratch.glue_used[i]?) ∧ st.1[33]? = some st.2 ∧
      (hw0 = 0xFFFFFFFF#32 ∧ st.2 = 0xFFFFFFFF#32 ∨
        hw0 ≠ 0xFFFFFFFF#32 ∧ hw0.toNat ≤ st.2.toNat ∧ st.2.toNat ≤ L.maxV ∧
          ∀ i < sz.toNat, (xs[i]?.getD 0#32).toNat / 2 + 1 ≤ st.2.toNat) ∧
      (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
        array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
        array (t := i32) c.pGlueUsed st.1 ⋆ array (t := i32) lits_ptr xs ⋆ R) m') ?_ ?_
  · rintro Jgu ⟨gu', hw'⟩ m1 ⟨hgu'_len, hgu_other, hgu'_33, hhwm_rel, hm1⟩
    c0_hsteps_nogrp; refine k6_maxV_call_step hMaxV hcap64 ?_
    have hm1' := hm1; rw [array_scratch_eq_k6 hscr_len] at hm1'
    have hmA : (K6MemA L (L.kPtr c.pScratchBuf) ks ⋆
        (array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take L.k6Base) ⋆
          array64 (c.hdr + 32) (hdrTailWords c s) ⋆
          array (t := i32) c.pGlueUsed gu' ⋆ array (t := i32) lits_ptr xs ⋆ R)) m1 :=
      k6Mem_to_amem hinv.shapes (sep_ac hm1')
    have finish_with := fun (ok : Bool) (ks' : K6State) {m' : Mem 64}
        (hm' : (K6MemA L (L.kPtr c.pScratchBuf) ks' ⋆
          (array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take L.k6Base) ⋆
            array64 (c.hdr + 32) (hdrTailWords c s) ⋆
            array (t := i32) c.pGlueUsed gu' ⋆ array (t := i32) lits_ptr xs ⋆ R)) m')
        (hinv' : K6Inv L P ks') (hsync' : K6TrailSynced ks') (hlvl' : ks'.lvl = 0#32)
        (hnv' : ks'.nv = ks.nv) (hna' : ks'.nassump = ks.nassump) (hass' : ks'.assump = ks.assump)
        (hne' : ok = false → ks' = ks)
        (hge2' : 2 ≤ sz.toNat → ks'.trl_end = ks.trl_end ∧ ks'.prop = ks.prop ∧
          ks'.unass = ks.unass ∧ ks'.incons = ks.incons)
        (hhwm_st : K6HwmClean L (gu'[33]?.getD 0#32) ks')
        (hbnd : ∀ M, (∀ i < sz.toNat, (xs[i]?.getD 0#32).toNat < 2 * M) →
          K6LitsBounded M ks → (∀ l ∈ k6TrailLits ks, l < 2 * M) →
          K6LitsBounded M ks' ∧ (∀ l ∈ k6TrailLits ks', l < 2 * M)) => by
      obtain ⟨hsh', hm''⟩ := k6MemA_to_mem hm'
      let scr' := s.scratch.scratch_buf.take L.k6Base ++ ks'.toSlab
      let s' : FullState :=
        { s with scratch := { s.scratch with scratch_buf := scr', glue_used := gu' } }
      have hm_arr : (array (t := i32) c.pScratchBuf scr' ⋆
          (array64 (c.hdr + 32) (hdrTailWords c s') ⋆
            array (t := i32) c.pGlueUsed gu' ⋆ array (t := i32) lits_ptr xs ⋆ R)) m' := by
        change (array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take L.k6Base ++ ks'.toSlab) ⋆
          _) m'
        rw [← k6_append_eq_array_scratch htk_len hsh']; exact sep_ac hm''
      have hscr'_len : scr'.length = c.scratch_cap := by
        dsimp only [scr']
        rw [List.length_append, htk_len, ks'.toSlab_length hsh', ← hL_scr]
        unfold K6Layout.scrLen; omega
      have hks'_eq : k6StateOfScratch L scr' = ks' := by
        unfold k6StateOfScratch; rw [k6_slab_drop_exact _ _ htk_len, K6State.ofSlab_toSlab hsh']
      have hlen' : s'.LengthsOk c :=
        ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hscr'_len, glue_used_len :=
          hgu'_len }⟩
      have hpref : ∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]? := fun i hi => by
        dsimp only [scr']
        rw [List.getElem?_append_left (by rw [htk_len]; omega), List.getElem?_take_of_lt hi]
      have hassS : k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf := by
        unfold k6AssumpLitsS; rw [hks'_eq]; unfold k6AssumpLits; rw [hna', hass']
      exact hcont ok scr' gu' m' hlen' hpref hgu_other (hks'_eq ▸ hhwm_st)
        (hks'_eq ▸ hinv') (hks'_eq ▸ hsync') (hks'_eq ▸ hlvl') (hks'_eq ▸ hnv')
        (hks'_eq ▸ hna') hassS (fun hok => by rw [hks'_eq, hne' hok])
        (fun h2 => by rw [hks'_eq]; exact hge2' h2)
        (fun M hm1' hm2' hm3' => by rw [hks'_eq]; exact hbnd M hm1' hm2' hm3')
        (sep_ac hm_arr)
    have hhwm_id := s13_add_clause_hwm_id hgu'_33 hhwm0' hhwm_rel
    c0_hsteps_nogrp
    · have hsz0 : sz.toNat = 0 := by bv_omega
      rw [hmv32, k6_ptr_base L c.pScratchBuf]; c0_hsteps!
      have hunsat : ∀ β, ¬ P β := SemEntails.unsat_of_nil (by simpa [hsz0] using hent)
      exact finish_with true (ks.putHdr .incons 1#32) hm (k6SetIncons_preserves_inv hinv hunsat)
        hsync hlvl0 rfl rfl rfl (fun h => absurd h (by decide)) (fun h2 => by omega) hhwm_id
        (fun _ _ hB hT => ⟨hB, hT⟩)
    · have h0_xs : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat < xs.length := by
        have hnz : 0 < sz.toNat := by bv_omega
        rw [BitVec.toNat_ofNat]; simp only [Nat.zero_mod]; omega
      have hsz1 : sz.toNat = 1 := by bv_omega
      have h0_xs : 0 < xs.length := by omega
      have hxl0 : (xs[0]).toNat < 2 * ks.nv.toNat := by
        have := hxlits 0 (by omega); rwa [List.getElem?_eq_getElem h0_xs, Option.getD_some] at this
      have hxl0_sz : (xs[0]).toNat < sz2V L := by unfold sz2V; dsimp only [ks] at hxl0; omega
      have ht1 : xs.take sz.toNat = [xs[0]] := by
        rw [hsz1]; cases xs with | nil => simp at h0_xs | cons x t => simp
      rw [hmv32, k6_ptr_base L c.pScratchBuf]
      c0_hsteps_nogrp; try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
      c0_hsplit
      · have hsome2 : ks.vals[(xs[0]).toNat]? = some 2#32 :=
          k6_vals_some hinv.shapes hxl0_sz (by simpa using
            ‹ks.vals[(xs[(BitVec.ofNat 64 0).toNat]).toNat]?.getD 0#32 = 2#32›)
        have hunsat : ∀ β, ¬ P β := fun β hβ =>
          (sat_cnfClause_litNeg_iff β (xs[0]).toNat).mp
            ((k6_falsified_lvl0_entails hinv hlvl0 hxl0 hsome2).2 β hβ)
            (by simpa [ht1] using hent β hβ)
        c0_hsteps!
        exact finish_with true (ks.putHdr .incons 1#32) hm (k6SetIncons_preserves_inv hinv hunsat)
          hsync hlvl0 rfl rfl rfl (fun h => absurd h (by decide)) (fun h2 => by omega) hhwm_id
          (fun _ _ hB hT => ⟨hB, hT⟩)
      · try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
        c0_hsplit
        · have huv0 : ks.vals[(xs[0]).toNat]?.getD 0#32 = 0#32 := by bv_omega
          have hsome0 : ks.vals[(xs[0]).toNat]? = some 0#32 := k6_vals_some hinv.shapes hxl0_sz huv0
          have hte_lt := k6_trl_end_lt_of_unassigned hinv.shapes hnv_le hinv.assign hxl0 huv0
          have ⟨hinv1, hsync1⟩ := k6AssignStep_preserves_inv hinv hsync hxl0 hsome0
            (fun _ => by simpa [ht1] using hent) (fun hp => by rw [hlvl0] at hp; simp at hp)
            (Or.inl rfl)
          k6_call hAssign
          · refine ⟨L, ks, _, hinv.shapes, hinv.clauses.max_v_eq,
              by dsimp only [ks] at hxl0 hnv_le; simpa using Nat.lt_of_lt_of_le hxl0 (by omega),
              Nat.lt_of_lt_of_le hte_lt hnv_le, (k6MemA_to_mem hmA).2, fun m' hm' => ?_⟩
            have hmA' := k6Mem_to_amem hinv1.shapes hm'
            have hhwm1 :
                K6HwmClean L (gu'[33]?.getD 0#32) (k6AssignStep ks xs[0] 0xFFFFFFFF#32) := by
              rw [hgu'_33, Option.getD_some]; refine s13_hwm_clean_of_range hhwm0' ?_
              rcases hhwm_rel with ⟨h0, h1⟩ | ⟨h0, h1, h2, hlt⟩
              · exact Or.inl ⟨h0, h1⟩
              · have hx0 := hlt 0 (by omega)
                rw [List.getElem?_eq_getElem h0_xs, Option.getD_some] at hx0
                exact Or.inr ⟨h0, h1, h2, s13_hwm_eq_of_assign (by omega)⟩
            c0_hsteps!
            exact finish_with true (k6AssignStep ks xs[0] 0xFFFFFFFF#32) hmA' hinv1 hsync1 hlvl0
              rfl rfl rfl (fun h => absurd h (by decide)) (fun h2 => by omega) hhwm1
              (s13_add_clause_sz1_bnd (xs := xs) (sz := sz) h0_xs (by bv_omega)
                hinv.shapes.trl_len hte_lt hnv_le)
        · c0_hsteps!
          exact finish_with true ks hmA hinv hsync hlvl0 rfl rfl rfl
            (fun h => absurd h (by decide)) (fun h2 => by omega) hhwm_id
            (fun _ _ hB hT => ⟨hB, hT⟩)
    · have hsz2 : 2 ≤ sz.toNat := by bv_omega
      rw [hmv32, k6_ptr_base L c.pScratchBuf]
      have ret_false : Q (false, ()) m1 :=
        finish_with false ks hmA hinv hsync hlvl0 rfl rfl rfl (fun _ => rfl)
          (fun _ => ⟨rfl, rfl, rfl, rfl⟩) hhwm_id (fun _ _ hB hT => ⟨hB, hT⟩)
      c0_hsteps_nogrp
      · c0_hsteps!; exact ret_false
      · c0_hsteps!; exact ret_false
      · have hnc_lt : ks.nc.toNat < L.maxCl := by
          have hlt : ks.nc.toNat < ks.max_cl.toNat := by bv_omega
          rw [hinv.clauses.max_cl_eq, BitVec.toNat_ofNat] at hlt
          exact Nat.lt_of_lt_of_le hlt (Nat.mod_le _ _)
        have hfit : ks.alen.toNat + sz.toNat ≤ L.acap := by
          have h_acap : ks.acap.toNat = L.acap := by
            rw [hinv.clauses.acap_eq, BitVec.toNat_ofNat]
            exact Nat.mod_eq_of_lt (by have := L.hacap; unfold dimacsBound at *; omega)
          have := hinv.clauses.alen_le; have := L.hacap; unfold dimacsBound at *
          dsimp only [ks] at *; bv_omega
        have hxs0 : 0 < xs.length := by omega
        have hxs1 : 1 < xs.length := by omega
        refine wp_while_state (ts := [i32]) (α := Nat × K6State)
          (fun p => (BitVec.ofNat 32 p.1, ())) (fun p => sz.toNat - p.1)
          (fun p m'' => p.1 ≤ sz.toNat ∧ p.2.ShapesOk L ∧ p.2 = { ks with arena := p.2.arena } ∧
            (∀ j < ks.alen.toNat, p.2.arena[j]? = ks.arena[j]?) ∧
            (∀ j < p.1, p.2.arena[ks.alen.toNat + j]? = xs[j]?) ∧
            (K6MemA L (L.kPtr c.pScratchBuf) p.2 ⋆
              (array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take L.k6Base) ⋆
                array64 (c.hdr + 32) (hdrTailWords c s) ⋆
                array (t := i32) c.pGlueUsed gu' ⋆ array (t := i32) lits_ptr xs ⋆ R)) m'') ?_ ?_
        · intro Ji hJi; c0_hsteps!
          exact hJi (0, ks) _ ⟨Nat.zero_le _, hinv.shapes, by cases ks; rfl,
            fun _ _ => rfl, fun _ hj => absurd hj (Nat.not_lt_zero _), hmA⟩
        · rintro Ji ⟨i, st⟩ m2 ⟨hi_le, hsh_st, hst_eq, hold, hnew, hm2⟩ ih
          dsimp only at hst_eq
          have hst_mv : st.max_v = L.mv32 := by rw [hst_eq]; exact hinv.clauses.max_v_eq
          c0_hsteps_nogrp
          · have hi_lt : i < sz.toNat := by bv_omega
            have hi_xs : (BitVec.ofNat 32 i).toNat < xs.length := by bv_omega
            have hi_ar : (ks.alen + BitVec.ofNat 32 i).toNat < szAr L := by unfold szAr; bv_omega
            have hidx : (ks.alen + BitVec.ofNat 32 i).toNat = ks.alen.toNat + i := by
              have := L.hacap; unfold dimacsBound at *; bv_omega
            c0_hsteps!
            rw [show (BitVec.ofNat 32 (i, st).fst + 1 : BitVec 32) = BitVec.ofNat 32 (i + 1) by
              have := L.hacap; unfold dimacsBound at *
              apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt (by omega : i + 1 < 2 ^ 32)]]
            refine ih (i + 1, st.putArr .arena (ks.alen + BitVec.ofNat 32 i).toNat
                xs[(BitVec.ofNat 32 i).toNat]) _ (by omega)
              ⟨by omega, hsh_st.putArr .arena _ _, by rw [hst_eq]; k6_field,
                fun j hj => by
                  k6_field; rw [hidx, List.getElem?_set_ne (by omega)]; exact hold j hj,
                fun j hj => by
                  k6_field; by_cases hji : j = i
                  · subst hji; rw [hidx, List.getElem?_set_self (by rw [hsh_st.arena_len]; omega),
                      List.getElem?_eq_getElem (by omega)]
                    congr 2; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
                  · rw [hidx, List.getElem?_set_ne (by omega)]; exact hnew j (by omega), hm⟩
          · have hi_eq : i = sz.toNat := by bv_omega
            subst hi_eq
            let stM := ((((st.putHdr .alen (ks.alen + sz)).putArr .clOff ks.nc.toNat
              ks.alen).putArr .clSz ks.nc.toNat sz).putHdr .nc (ks.nc + 1#32))
            have hpres2 := k6AddClause_ge2_preserves hinv hsync hnc_lt hsz2 hsz_max hsz_le hfit
              hsh_st.arena_len hold hnew hxlits hent
            have hstM_eq : stM = (((({ ks with arena := st.arena } : K6State).putHdr .alen
                (ks.alen + sz)).putArr .clOff ks.nc.toNat ks.alen).putArr .clSz ks.nc.toNat
                sz).putHdr .nc (ks.nc + 1#32) := by dsimp only [stM]; rw [hst_eq]
            have hstM_sh : stM.ShapesOk L :=
              (((hsh_st.putHdr .alen _).putArr .clOff _ _).putArr .clSz _ _).putHdr .nc _
            have hnc_cl : ks.nc.toNat < szCl L := by unfold szCl; exact hnc_lt
            c0_hsteps_nogrp; k6_call hAddTicks
            · let rest : Mem 64 → Prop :=
                array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take L.k6Base) ⋆
                  array64 (c.hdr + 32) (hdrTailWords c s) ⋆
                  array (t := i32) c.pGlueUsed gu' ⋆ array (t := i32) lits_ptr xs ⋆ R
              refine ⟨L, stM, rest, hstM_sh, ?_, fun tk' m3 hm3 => ?_⟩
              · exact Eq.mp (congrArg (fun x => (K6Mem L (L.kPtr c.pScratchBuf) x ⋆ rest) _)
                  (by dsimp only [stM]; k6_ext)) (k6MemA_to_mem hm).2
              · have hxl0 : (xs[0]).toNat < 2 * L.maxV := by
                  have h0 := hxlits 0 (by omega)
                  rw [List.getElem?_eq_getElem hxs0, Option.getD_some] at h0; omega
                have hxl1 : (xs[1]).toNat < 2 * L.maxV := by
                  have h1 := hxlits 1 (by omega)
                  rw [List.getElem?_eq_getElem hxs1, Option.getD_some] at h1; omega
                dsimp only [rest] at hm3; c0_hsteps!; k6_call hWatch
                · refine ⟨L, stM.putHdr .ticks tk', _, hstM_sh.putHdr .ticks tk',
                    by dsimp only [K6State.putHdr, stM]; k6_field; exact hst_mv,
                    hnc_lt, hxl0, hxl1, hm3, fun m4 hm4 => ?_⟩
                  c0_hsteps!; dsimp only [ks] at hstM_eq; rw [← hstM_eq] at hpres2
                  have hpost := s13_add_clause_ge2_post (L := L) (P := P) (tk' := tk')
                    hlvl0 hsz2 hxs0 hxs1 hstM_eq hgu'_33 hhwm0' hhwm_rel hpres2
                  exact finish_with true _ (k6Mem_to_amem hpost.2.1.shapes hm4)
                    hpost.2.1 hpost.2.2.1 hpost.2.2.2.1 hpost.2.2.2.2.1 hpost.2.2.2.2.2.1
                    hpost.2.2.2.2.2.2.1 (fun h => absurd h (by decide))
                    hpost.2.2.2.2.2.2.2.1 hpost.1 hpost.2.2.2.2.2.2.2.2
  · intro Jgu hJgu; c0_hsteps_nogrp
    · have hne : hw0 ≠ 0xFFFFFFFF#32 := by
        simpa [hw0, show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 33)).toNat = 33 by decide]
          using ‹_›
      have hhw0_le : hw0.toNat ≤ L.maxV := by
        rcases hhwm0 with hff | ⟨hle, _⟩
        · exact absurd (by simpa [hw0, List.getElem?_eq_getElem hgu_len] using hff) hne
        · simpa [hw0, List.getElem?_eq_getElem hgu_len] using hle
      have hgu33 : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 33)).toNat <
          s.scratch.glue_used.length := by rw [hlen.scratch_ok.glue_used_len]; decide
      refine wp_while_state (ts := [i32, i32]) (α := Nat × BitVec 32)
        (fun p => (p.2, BitVec.ofNat 32 p.1, ())) (fun p => sz.toNat - p.1)
        (fun p m' => p.1 ≤ sz.toNat ∧ hw0.toNat ≤ p.2.toNat ∧ p.2.toNat ≤ L.maxV ∧
          (∀ i < p.1, (xs[i]?.getD 0#32).toNat / 2 + 1 ≤ p.2.toNat) ∧ m' = m) ?_ ?_
      · intro Jlp hJlp; c0_hsteps!
        exact hJlp (0, s.scratch.glue_used[(BitVec.ofNat 64 33).toNat]) _
          ⟨Nat.zero_le _, by simp [hw0], by simp [hw0, hhw0_le],
            fun _ h => absurd h (Nat.not_lt_zero _), rfl⟩
      · rintro Jlp ⟨xi, hw⟩ m' ⟨hxi, hlo, hhi, halt, rfl⟩ ih
        c0_hsteps_nogrp
        · have hxi_lt : xi < sz.toNat := by bv_omega
          obtain ⟨hxi_xs, hxi_eq, hxv_eq, hxv_lt, hhc_mod_eq, hadd_bv⟩ :=
            s13_hwm_step_bounds hxi_lt hsz_le hnv_le hmL.2 (hxlits xi hxi_lt)
          have hx_get : xs[(BitVec.ofNat 32 xi).toNat] = xs[xi]?.getD 0#32 := by
            simp [hxi_eq, List.getElem?_eq_getElem (by omega : xi < xs.length)]
          c0_hsteps!
          · have hhw' : hw.toNat ≤ ((xs[(BitVec.ofNat 32 xi).toNat] >>> (1 : Nat)) +
                1#32).toNat := by
              have hlt : hw.toNat < (xs[xi % 2 ^ 32 % 2 ^ 64].toNat / 2 + 1) % 2 ^ 32 := ‹_›
              rw [hx_get]; rw [hhc_mod_eq] at hlt; rw [hxv_eq]; omega
            rw [hadd_bv]
            refine ih (xi + 1, (xs[(BitVec.ofNat 32 xi).toNat] >>> (1 : Nat)) + 1#32) _
              (by omega) ⟨by omega, Nat.le_trans hlo hhw', by rw [hx_get]; exact hxv_lt,
                fun i hi => by
                  by_cases hii : i = xi
                  · dsimp only; rw [hii, hx_get, hxv_eq]; exact Nat.le_refl _
                  · exact Nat.le_trans (halt i (by omega)) hhw', rfl⟩
          · have hhc : hw.toNat ≥ (xs[xi]?.getD 0#32).toNat / 2 + 1 := by
              have hnot : ¬ hw.toNat < (xs[xi % 2 ^ 32 % 2 ^ 64].toNat / 2 + 1) % 2 ^ 32 := ‹_›
              rw [hhc_mod_eq] at hnot; omega
            rw [hadd_bv]
            refine ih (xi + 1, hw) _ (by omega) ⟨by omega, hlo, hhi, fun i hi => by
              by_cases hii : i = xi
              · dsimp only; rw [hii]; exact hhc
              · exact halt i (by omega), rfl⟩
        · have hxi_eq : xi = sz.toNat := by bv_omega
          subst hxi_eq; c0_hsteps!
          let gu' := s.scratch.glue_used.set (BitVec.ofNat 64 33).toNat hw
          exact hJgu (gu', hw) _
            ⟨by simp [gu', hlen.scratch_ok.glue_used_len],
              fun i _ hni => by
                dsimp only [gu']; rw [List.getElem?_set_ne (by simpa using hni.symm)],
              by dsimp only [gu']
                 rw [show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 33)).toNat = 33 by decide,
                   List.getElem?_set_self hgu_len],
              Or.inr ⟨hne, hlo, hhi, halt⟩, by exact sep_ac hm⟩
    · have heq : hw0 = 0xFFFFFFFF#32 := by
        simpa [hw0, show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 33)).toNat = 33 by decide]
          using ‹_›
      c0_hsteps!
      exact hJgu (s.scratch.glue_used, s.scratch.glue_used[(BitVec.ofNat 64 33).toNat]) _
        ⟨hlen.scratch_ok.glue_used_len, fun _ _ _ => rfl,
          by dsimp only; rw [List.getElem?_eq_getElem hgu_len]; rfl,
          Or.inl ⟨heq, by change s.scratch.glue_used[33] = 0xFFFFFFFF#32; exact heq⟩, sep_ac hm⟩

end LeanQbe.T.Examples.Kissat.Proof.Kitten
end
