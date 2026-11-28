/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Sweep.LemmasCommon
public import LeanQbe.T.Examples.Kissat.Proof.Sweep.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Kitten.Spec

/-!
# Backward Sweep Partition & Hash Table WP Proofs (`Kissat.Proof.Sweep.WpPart0`)
Proves `Func.wp` for `full_m6_sweep_rearm`, `full_m6_sweep_build_pht`,
and `full_m6_extract_pht` using `Proof.Sweep.Spec`.
-/

set_option autoImplicit false
public section
namespace LeanQbe.T.Examples.Kissat.Proof.Sweep

open Std Std.Sat Kraken.Bedrock2.Test LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Src.Sweep LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec LeanQbe.T.Examples.Kissat.Proof.Sweep.Spec
open LeanQbe.T.Examples.Kissat.Proof.Kitten LeanQbe.T.Examples.Kissat.Proof.Kitten.Spec
open K6MemATactics K6PtrTactics
open scoped FullArenaTactics M6SweepTactics M6PhtMem FullK6DynMem M6ElsBv

/-! ## 0. Pure BitVec & Layout Helpers -/

private theorem m6_zext32 (x : BitVec 32) : (BitVec.setWidth 64 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (lt_trans (BitVec.isLt x) (by decide))]

private theorem m6_bv32_add1_ofNat {n : Nat} (h : n + 1 < 2 ^ 32) :
    BitVec.ofNat 32 n + 1 = BitVec.ofNat 32 (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1
    from rfl, Nat.mod_eq_of_lt (by omega : n < 2 ^ 32), Nat.mod_eq_of_lt h]

private theorem m6_bv32_sub1_ofNat {n : Nat} (hp : 0 < n) (h : n < 2 ^ 32) :
    BitVec.ofNat 32 n - 1 = BitVec.ofNat 32 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]; exact hp)), BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, show (1 : BitVec 32).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega)]

private theorem m6_bv64_add1_ofNat {n : Nat} (h : n + 1 < 2 ^ 64) :
    BitVec.ofNat 64 n + 1 = BitVec.ofNat 64 (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1
    from rfl, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64), Nat.mod_eq_of_lt h]

private theorem m6_zext32_ofNat {n : Nat} (h : n < 2 ^ 32) :
    (BitVec.setWidth 64 (BitVec.ofNat 32 n)).toNat = n := by
  rw [m6_zext32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem m6_bv32_shl1_toNat {v : BitVec 32} (hv : v.toNat < 2 ^ 31) :
    (v <<< (1#32 : BitVec 32)).toNat = 2 * v.toNat := by
  have h1 : (v <<< (1#32 : BitVec 32)) = v <<< (1 : Nat) := rfl
  rw [h1, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]; omega

private theorem m6_bv64_shl1_toNat {x : BitVec 64} (hx : x.toNat < 2 ^ 63) :
    (x <<< (1#64 : BitVec 64)).toNat = 2 * x.toNat := by
  have h1 : (x <<< (1#64 : BitVec 64)) = x <<< (1 : Nat) := rfl
  rw [h1, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]; omega

private theorem m6_lit_shl1_or_toNat {v : BitVec 32} {pol : Nat}
    (hv : v.toNat < 2 ^ 30) (hpol : pol < 2) :
    ((v <<< (1#32 : BitVec 32)) ||| BitVec.ofNat 32 pol).toNat = 2 * v.toNat + pol := by
  have h1 := m6_bv32_shl1_toNat (v := v) (by omega)
  rcases (show pol = 0 ∨ pol = 1 by omega) with rfl | rfl
  · simp only [BitVec.toNat_or, h1, show (BitVec.ofNat 32 0).toNat = 0 from rfl, Nat.or_zero]
    omega
  · simp only [BitVec.toNat_or, h1, show (BitVec.ofNat 32 1).toNat = 1 from rfl]
    apply Nat.eq_of_testBit_eq; intro k; rw [Nat.testBit_or]
    rcases k with rfl | k
    · simp [Nat.testBit_zero]
    · simp [Nat.testBit_succ, show (1 : Nat) / 2 = 0 by decide,
        show (2 * v.toNat + 1) / 2 = v.toNat by omega]

private theorem m6_set_scr_pref_other {scr0 scr : List (BitVec 32)} {cap b : Nat}
    {P : Nat → Prop} (v : BitVec 32)
    (hpref : ∀ i < cap, P i → scr[i]? = scr0[i]?) (hnP : ¬ P b) :
    ∀ i < cap, P i → (scr.set b v)[i]? = scr0[i]? := fun i hi hPi => by
  rw [List.getElem?_set_ne (fun heq => hnP (by rw [heq]; exact hPi))]; exact hpref i hi hPi

private theorem m6_scr_nx_lt {scr : List (BitVec 32)} {L : K6Layout} {cap k : Nat}
    (hL : L.scrLen = cap) (hscr : scr.length = cap) (hk : k < L.maxV) :
    k6PhtNext + k < scr.length := by
  rw [hscr.trans hL.symm]; unfold K6Layout.scrLen K6Layout.k6Base k6PhtNext; omega

private theorem m6_scr_hd_lt {scr : List (BitVec 32)} {L : K6Layout} {cap b : Nat}
    (hL : L.scrLen = cap) (hscr : scr.length = cap) (hb : b < k6PhtSz) :
    k6PhtHead + b < scr.length := by
  rw [hscr.trans hL.symm]; unfold K6Layout.scrLen K6Layout.k6Base k6PhtHead k6PhtSz at *; omega

/-! ## 1. `full_m6_sweep_rearm` -/

private structure M6RearmIn where
  pIdx : Nat
  steps : Nat
  flags : List (BitVec 32)

private abbrev M6RearmStInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (flags : List (BitVec 32)) (m' : Mem 64) : Prop :=
  flags.length = c.max_vars ∧
  let s' : FullState := { s with core := { s.core with flags := flags } }
  FullDenseInvW c F0 F_cur s' ∧ (FullMem c s' ⋆ R) m'

private theorem m6_rearm_wvec_facts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {v : BitVec 32} {pol : Nat}
    (hinv : FullDenseInvW c F0 F_cur s) (hwlen_db : WatchStackLayout s.core)
    (hv_cur : v.toNat < s.core.cur_vars) (hpol : pol < 2) :
    let shl := BitVec.setWidth 64 (v <<< (1#32 : BitVec 32) ||| BitVec.ofNat 32 pol) <<<
      (1#64 : BitVec 64)
    let wOff := (s.core.wvec[2 * (2 * v.toNat + pol)]?.getD 0#32).toNat
    let wSz := (s.core.wvec[2 * (2 * v.toNat + pol) + 1]?.getD 0#32).toNat
    (shl.toNat < s.core.wvec.length) ∧ ((shl + 1#64).toNat < s.core.wvec.length) ∧
    (wOff + wSz ≤ s.core.wlen) ∧
    DenseWatchSliceOk F_cur s.core (2 * v.toNat + pol) wOff wSz ∧
    shl.toNat = 2 * (2 * v.toNat + pol) ∧
    (∀ h0 h1, (s.core.wvec[(v <<< OfNat.ofNat 1 ||| BitVec.ofNat 32 pol).toNat *
        2 ^ OfNat.ofNat 1 % 2 ^ 64]'h0).toNat +
        (s.core.wvec[((v <<< OfNat.ofNat 1 ||| BitVec.ofNat 32 pol).toNat *
          2 ^ OfNat.ofNat 1 + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'h1).toNat < 2 ^ 64 ∧
      ((s.core.wvec[(v <<< OfNat.ofNat 1 ||| BitVec.ofNat 32 pol).toNat *
          2 ^ OfNat.ofNat 1 % 2 ^ 64]'h0).toNat +
        (s.core.wvec[((v <<< OfNat.ofNat 1 ||| BitVec.ofNat 32 pol).toNat *
          2 ^ OfNat.ofNat 1 + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'h1).toNat) % 2 ^ 64 =
        wOff + wSz) := by
  have hcur_le := hinv.1.core_ok.cur_vars_le; have hmv_db := c.hmaxv
  unfold dimacsBound at hmv_db
  have hv30 : v.toNat < 2 ^ 30 := by omega
  have hlit_eq : ((v <<< (1#32 : BitVec 32)) ||| BitVec.ofNat 32 pol).toNat =
      2 * v.toNat + pol := m6_lit_shl1_or_toNat hv30 hpol
  have h64 : (BitVec.setWidth 64
      (v <<< (1#32 : BitVec 32) ||| BitVec.ofNat 32 pol)).toNat < 2 ^ 63 := by
    rw [m6_zext32]; omega
  have hw0_eq : (BitVec.setWidth 64 (v <<< (1#32 : BitVec 32) ||| BitVec.ofNat 32 pol) <<<
      (1#64 : BitVec 64)).toNat = 2 * (2 * v.toNat + pol) := by
    rw [m6_bv64_shl1_toNat h64, m6_zext32, hlit_eq]
  have hwv_len := hinv.1.core_ok.wvec_len
  have hlit_cur : 2 * v.toNat + pol < 2 * s.core.cur_vars := by omega
  have hw0_lt : 2 * (2 * v.toNat + pol) < s.core.wvec.length := by rw [hwv_len]; omega
  have hw1_lt : 2 * (2 * v.toNat + pol) + 1 < s.core.wvec.length := by rw [hwv_len]; omega
  refine ⟨by rw [hw0_eq]; exact hw0_lt, by
    rw [BitVec.toNat_add, hw0_eq, show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega)]; exact hw1_lt,
    hwlen_db.bounds (2 * v.toNat + pol) hlit_cur, ?_, hw0_eq, fun h0' h1' => ?_⟩
  · have hw := hinv.2.1.watches; unfold ModeWatchesInv at hw
    simp only [hinv.2.2.2.2.2.2, ↓reduceIte] at hw; exact hw.slices _ hlit_cur
  · have hc0 : (v <<< OfNat.ofNat 1 ||| BitVec.ofNat 32 pol).toNat *
        2 ^ OfNat.ofNat 1 % 2 ^ 64 = 2 * (2 * v.toNat + pol) := by
      change (v <<< (1#32 : BitVec 32) ||| BitVec.ofNat 32 pol).toNat * 2 ^ 1 % 2 ^ 64 = _
      rw [hlit_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]; omega
    have hc1 : ((v <<< OfNat.ofNat 1 ||| BitVec.ofNat 32 pol).toNat *
        2 ^ OfNat.ofNat 1 + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
        2 * (2 * v.toNat + pol) + 1 := by
      change ((v <<< (1#32 : BitVec 32) ||| BitVec.ofNat 32 pol).toNat * 2 ^ 1 + 1) % 2 ^ 64 = _
      rw [hlit_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]; omega
    have h0 : s.core.wvec[(v <<< OfNat.ofNat 1 ||| BitVec.ofNat 32 pol).toNat *
        2 ^ OfNat.ofNat 1 % 2 ^ 64]'h0' = s.core.wvec[2 * (2 * v.toNat + pol)]?.getD 0#32 :=
      Option.some.inj (by
        rw [← List.getElem?_eq_getElem h0', hc0, List.getElem?_eq_getElem hw0_lt]; rfl)
    have h1 : s.core.wvec[((v <<< OfNat.ofNat 1 ||| BitVec.ofNat 32 pol).toNat *
        2 ^ OfNat.ofNat 1 + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'h1' =
        s.core.wvec[2 * (2 * v.toNat + pol) + 1]?.getD 0#32 :=
      Option.some.inj (by
        rw [← List.getElem?_eq_getElem h1', hc1, List.getElem?_eq_getElem hw1_lt]; rfl)
    have := (s.core.wvec[2 * (2 * v.toNat + pol)]?.getD 0#32).isLt
    have := (s.core.wvec[2 * (2 * v.toNat + pol) + 1]?.getD 0#32).isLt
    rw [h0, h1]; exact ⟨by omega, Nat.mod_eq_of_lt (by omega)⟩

private theorem m6_rearm_occ_ar2_eq {c : FullCfg} {s : FullState} {pi : Nat} {cref : BitVec 32}
    (hlen : s.LengthsOk c) (hcref1 : cref.toNat + 3 ≤ s.core.arena_len)
    (hpi64 : pi + 1 < 2 ^ 64) (hw1_p : s.core.wstk[pi + 1]? = some cref) :
    ∀ (hbd1 : (pi + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < s.core.wstk.length)
      (hcr : ((s.core.wstk[(pi + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'hbd1).toNat +
        BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 < s.core.arena.length),
      s.core.arena[((s.core.wstk[(pi + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'hbd1).toNat +
        BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'hcr =
        s.core.arena[(BitVec.setWidth 64 cref + 2#64).toNat]?.getD 0#32 := by
  intro hbd1 hcr
  have hpi1 : (pi + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = pi + 1 := by
    change (pi + 1) % 2 ^ 64 = pi + 1; exact Nat.mod_eq_of_lt hpi64
  have hww : s.core.wstk[(pi + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'hbd1 = cref :=
    Option.some.inj (by rw [← List.getElem?_eq_getElem hbd1, hpi1, hw1_p])
  unfold dimacsBound at *; have ha := c.harena
  have hidx : (BitVec.setWidth 64 cref + 2#64).toNat = cref.toNat + 2 := by
    rw [BitVec.toNat_add, m6_zext32, show (2#64 : BitVec 64).toNat = 2 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have hlt : (BitVec.setWidth 64 cref + 2#64).toNat < s.core.arena.length := by
    have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr; omega
  rw [List.getElem?_eq_getElem hlt, Option.getD_some]; congr 1
  rw [hidx, hww, show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; exact Nat.mod_eq_of_lt (by omega)

private theorem m6_rearm_occ_ari_lt {c : FullCfg} {s : FullState} {pi i : Nat} {cref : BitVec 32}
    (hlen : s.LengthsOk c) (_hcref1 : cref.toNat + 3 ≤ s.core.arena_len)
    (hcref_sz : cref.toNat + 3 + fullArenaClauseSizeCore s.core cref.toNat ≤ s.core.arena_len)
    {hpi1_bv : (BitVec.ofNat 64 pi + 1#64).toNat < s.core.wstk.length}
    (hwstk_cref : s.core.wstk[(BitVec.ofNat 64 pi + 1#64).toNat]'hpi1_bv = cref)
    (hi_lt : i < (s.core.arena[(BitVec.setWidth 64 cref + 2#64).toNat]?.getD 0#32).toNat) :
    (BitVec.setWidth 64 (s.core.wstk[(BitVec.ofNat 64 pi + 1#64).toNat]'hpi1_bv) + 3#64 +
      BitVec.setWidth 64 (BitVec.ofNat 32 i)).toNat < s.core.arena.length := by
  rw [hwstk_cref]; have h1 := hlen.core_ok.arena_len_le; have h2 := hlen.core_ok.arena_len_arr
  unfold dimacsBound at *; have ha := c.harena
  have h_eq : (BitVec.setWidth 64 cref + 2#64).toNat = cref.toNat + 2 := by
    rw [BitVec.toNat_add, m6_zext32, show (2#64 : BitVec 64).toNat = 2 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have hi_sz : i < fullArenaClauseSizeCore s.core cref.toNat := by
    unfold fullArenaClauseSizeCore; rw [← h_eq]; exact hi_lt
  have hi_64 : i < 2 ^ 32 := by omega
  simp only [BitVec.toNat_add, m6_zext32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi_64,
    show (3#64 : BitVec 64).toNat = 3 from rfl,
    Nat.mod_eq_of_lt (by omega : cref.toNat + 3 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : cref.toNat + 3 + i < 2 ^ 64)]
  omega

theorem full_m6_sweep_rearm_wp (Γ : Env) :
    ∀ args m Q X, fullM6SweepRearmSpec args m Q X →
      Func.wp Γ full_m6_sweep_rearm_body args m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hinv, hm, hQ⟩
  dsimp only [Func.wp]; unfold full_m6_sweep_rearm_body
  have hlen : s.LengthsOk c := hinv.1
  have hcur_le : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
  have hmv_db : c.max_vars < 2 * dimacsBound := c.hmaxv
  c0_hsteps_nogrp
  · exact hQ s.core.flags m hlen.core_ok.flags_len hinv hm
  · have hc := ‹¬ s.core.cur_vars % 2 ^ 64 ≤ v.toNat›
    have h64 : s.core.cur_vars < 2 ^ 64 := by unfold dimacsBound at hmv_db; omega
    have hv_cur : v.toNat < s.core.cur_vars := by rw [Nat.mod_eq_of_lt h64] at hc; omega
    refine wp_while_state (ts := [i32]) (α := Nat × List (BitVec 32))
      (fun st => (BitVec.ofNat 32 st.1, ())) (fun st => 2 - st.1)
      (fun st m' => st.1 ≤ 2 ∧ M6RearmStInv c F0 F_cur s R st.2 m') ?_ ?_
    · intro J0 hJ0; c0_hsteps_nogrp
      exact hJ0 (0, s.core.flags) _ ⟨Nat.zero_le 2, hlen.core_ok.flags_len, hinv, hm⟩
    · rintro J0 ⟨pol, flags_lp⟩ m_lp ⟨hpol_le, hfl_len, hinv_lp, hm_lp⟩ ih
      dsimp only at hpol_le hfl_len hinv_lp hm_lp ih; have hlen_lp := hinv_lp.1
      c0_hsteps_nogrp
      · have hpol_lt : pol < 2 := by bv_omega
        have hwf := m6_rearm_wvec_facts hinv (m6_watchLayout_of_denseInvW hinv) hv_cur hpol_lt
        have hw0_lt : (BitVec.setWidth 64 (v <<< (1#32 : BitVec 32) |||
            BitVec.ofNat 32 pol) <<< (1#64 : BitVec 64)).toNat <
            ({ s with core := { s.core with flags := flags_lp } } :
              FullState).core.wvec.length := hwf.1
        have hw1_lt : (BitVec.setWidth 64 (v <<< (1#32 : BitVec 32) |||
            BitVec.ofNat 32 pol) <<< (1#64 : BitVec 64) + 1#64).toNat <
            ({ s with core := { s.core with flags := flags_lp } } :
              FullState).core.wvec.length := hwf.2.1
        c0_hsteps_nogrp
        have hslice0 := hwf.2.2.2.1; have hw0_at := hwf.2.2.2.2.1; have hwEnd_c := hwf.2.2.2.2.2
        let wOff := (s.core.wvec[2 * (2 * v.toNat + pol)]?.getD 0#32).toNat
        let wEnd := wOff + (s.core.wvec[2 * (2 * v.toNat + pol) + 1]?.getD 0#32).toNat
        have hwEnd_le : wEnd ≤ s.core.wlen := hwf.2.2.1
        have hwEnd_33 : wEnd < 2 ^ 33 := by
          have := (s.core.wvec[2 * (2 * v.toNat + pol)]?.getD 0#32).isLt
          have := (s.core.wvec[2 * (2 * v.toNat + pol) + 1]?.getD 0#32).isLt
          dsimp [wOff, wEnd]; omega
        refine wp_join_group (fun _ m1 => ∃ flags1, M6RearmStInv c F0 F_cur s R flags1 m1) ?_ ?_
        · rintro J_out _ m1 ⟨flags1, hinv1⟩; c0_hsteps_nogrp
          rw [m6_bv32_add1_ofNat (n := pol) (by omega)]
          exact ih (pol + 1, flags1) m1 (by omega) ⟨by omega, hinv1⟩
        · intro J_out hJ_out; clear hm
          refine wp_while_state (ts := [i64, i64]) (α := M6RearmIn)
            (fun st => (BitVec.ofNat 64 st.pIdx, BitVec.ofNat 64 st.steps, ()))
            (fun st => wEnd - st.pIdx)
            (fun st m1 => wOff ≤ st.pIdx ∧ st.pIdx ≤ wEnd ∧ st.steps ≤ 128 ∧
              DenseWatchSliceOk F_cur s.core (2 * v.toNat + pol) st.pIdx (wEnd - st.pIdx) ∧
              M6RearmStInv c F0 F_cur s R st.flags m1) ?_ ?_
          · intro J1 hJ1; c0_hsteps_nogrp
            have hget0 : s.core.wvec[(BitVec.setWidth 64 (v <<< (1#32 : BitVec 32) |||
                BitVec.ofNat 32 pol) <<< (1#64 : BitVec 64)).toNat]'hw0_lt =
                s.core.wvec[2 * (2 * v.toNat + pol)]?.getD 0#32 := by
              have h0' : s.core.wvec[2 * (2 * v.toNat + pol)]?.getD 0#32 =
                  s.core.wvec[(BitVec.setWidth 64 (v <<< (1#32 : BitVec 32) |||
                    BitVec.ofNat 32 pol) <<< (1#64 : BitVec 64)).toNat]?.getD 0#32 := by
                rw [hw0_at]
              rw [h0', List.getElem?_eq_getElem hw0_lt]; rfl
            have hw0_64 : (BitVec.setWidth 64
                (s.core.wvec[2 * (2 * v.toNat + pol)]?.getD 0#32)).toNat = wOff := m6_zext32 _
            erw [hget0]
            rw [show BitVec.setWidth 64 (s.core.wvec[2 * (2 * v.toNat + pol)]?.getD 0#32) =
              BitVec.ofNat 64 wOff by apply BitVec.eq_of_toNat_eq; simp [hw0_64]]
            exact hJ1 ⟨wOff, 0, flags_lp⟩ m_lp ⟨Nat.le_refl _, by dsimp [wOff, wEnd]; omega,
              Nat.zero_le _, by simpa [wOff, wEnd] using hslice0, hfl_len, hinv_lp, hm_lp⟩
          · rintro J1 ⟨pi, steps, flags1⟩ m1
              ⟨hpi_lo, hpi_hi, hst_le, hslice, hfl1_len, hinv1, hm1⟩ ih1
            dsimp only at hpi_lo hpi_hi hst_le hslice hfl1_len hinv1 hm1 ih1
            have hlen1 := hinv1.1; have hwEnd_v : wEnd < 2 ^ 33 := hwEnd_33
            have hpi_33 : pi < 2 ^ 33 := by dsimp only [wEnd, wOff] at hpi_hi hwEnd_v; omega
            have hpi_64 : pi < 2 ^ 64 := by omega
            have hst_64 : steps < 2 ^ 64 := by omega
            c0_hsteps_nogrp
            · have hpi_lt : pi < wEnd := by
                have hc_pi := ‹pi % 2 ^ 64 < _›
                rw [(hwEnd_c _ _).2, Nat.mod_eq_of_lt hpi_64] at hc_pi; exact hc_pi
              generalize hrem : wEnd - pi = rem at hslice
              have hpi_bv : (BitVec.ofNat 64 pi).toNat <
                  ({ s with core := { s.core with flags := flags1 } } :
                    FullState).core.wstk.length := by
                have hwl := hlen1.core_ok.wlen_le; have hwa := hlen1.core_ok.wstk_len_arr
                dsimp only at hwa ⊢; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpi_64, hwa]
                exact Nat.lt_of_lt_of_le hpi_lt (Nat.le_trans hwEnd_le hwl)
              cases hslice with
              | empty => exfalso; omega
              | @bin _ rem w0 hw0_p hw0_nz _ hw0_lt2v _ hrest =>
              · have hst_lt : steps < 128 := by
                  have h1 := ‹steps % 2 ^ 64 < BitVec.toNat 128›
                  rw [show BitVec.toNat (128 : BitVec 64) = 128 from rfl,
                    Nat.mod_eq_of_lt hst_64] at h1; exact h1
                c0_hsteps_nogrp
                · refine wp_join0 (fun m2 => ∃ flags2, M6RearmStInv c F0 F_cur s R flags2 m2) ?_ ?_
                  · rintro Js m2 ⟨flags2, hinv2⟩; c0_hsteps_nogrp
                    rw [m6_bv64_add1_ofNat (n := pi) (by omega),
                      m6_bv64_add1_ofNat (n := steps) (by omega)]
                    exact ih1 ⟨pi + 1, steps + 1, flags2⟩ m2 (by dsimp only; omega)
                      ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
                       by dsimp only; rw [show wEnd - (pi + 1) = rem by omega]; exact hrest, hinv2⟩
                  · intro Js hJs
                    have hu_fl : (BitVec.setWidth 64
                        (((s.core.wstk[(BitVec.ofNat 64 pi).toNat]'hpi_bv &&& 2147483647) >>>
                          OfNat.ofNat 1 : BitVec 32))).toNat < flags1.length := by
                      have hget : s.core.wstk[(BitVec.ofNat 64 pi).toNat]'hpi_bv = w0 :=
                        Option.some.inj (by
                          rw [← List.getElem?_eq_getElem hpi_bv, BitVec.toNat_ofNat,
                            Nat.mod_eq_of_lt hpi_64]; exact hw0_p)
                      rw [hget, m6_zext32, m6_bv32_shr1_toNat, hfl1_len,
                        show (2147483647 : BitVec 32) = 2147483647#32 from rfl]
                      have := hw0_lt2v; omega
                    c0_hsteps_nogrp
                    · dsimp only at hm
                      exact hJs _ ⟨_, by simp [hfl1_len],
                        m6_fullDenseInvW_with_flags hinv1 (by simp [hfl1_len]), hm⟩
                    all_goals exact hJs _ ⟨flags1, hfl1_len, hinv1, hm1⟩
                all_goals
                  exfalso; have h1 := ‹s.core.wstk[pi % 2 ^ 64] &&& 2147483648#32 = 0#32›
                  have hw0_at_h1 : ∀ h, s.core.wstk[pi % 2 ^ 64]'h = w0 := fun h =>
                    Option.some.inj ((List.getElem?_eq_getElem h).symm.trans
                      (by rw [Nat.mod_eq_of_lt hpi_64]; exact hw0_p))
                  rw [hw0_at_h1 _] at h1; exact hw0_nz h1
              | @occ _ rem w0 cref hw0_p hw1_p hw0_z _ _ hcref hrest =>
                have hpi1_64 : pi + 1 < 2 ^ 64 := by omega
                have hpi1_lt : pi + 1 < wEnd := by dsimp only [wEnd, wOff] at hrem hpi_hi; omega
                have hpi1_bv : (BitVec.ofNat 64 pi + 1#64).toNat <
                    ({ s with core := { s.core with flags := flags1 } } :
                      FullState).core.wstk.length := by
                  have hwl := hlen1.core_ok.wlen_le; have hwa := hlen1.core_ok.wstk_len_arr
                  dsimp only at hwa ⊢
                  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpi_64,
                    show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt hpi1_64, hwa]
                  exact Nat.lt_of_lt_of_le hpi1_lt (Nat.le_trans hwEnd_le hwl)
                c0_hsteps_nogrp
                · exfalso; have h1 := ‹¬ s.core.wstk[pi % 2 ^ 64] &&& 2147483648#32 = 0#32›
                  have hw0_at_h1 : ∀ h, s.core.wstk[pi % 2 ^ 64]'h = w0 := fun h =>
                    Option.some.inj ((List.getElem?_eq_getElem h).symm.trans
                      (by rw [Nat.mod_eq_of_lt hpi_64]; exact hw0_p))
                  rw [hw0_at_h1 _] at h1; exact h1 hw0_z
                · exfalso; have h1 := ‹_ ≤ (pi + BitVec.toNat 1) % 2 ^ 64›
                  rw [(hwEnd_c _ _).2, show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
                    Nat.mod_eq_of_lt hpi1_64] at h1; dsimp only [wEnd, wOff] at hpi1_lt h1; omega
                · have hcref_wf := hinv.2.1.arena.refs_wf _ hcref
                  have hcref_sz : cref.toNat + 3 + fullArenaClauseSizeCore s.core cref.toNat ≤
                      s.core.arena_len := Nat.le_trans hcref_wf.2.2.1 hcref_wf.2.2.2.1
                  have hst_lt : steps < 128 := by
                    have h1 := ‹steps % 2 ^ 64 < BitVec.toNat 128›
                    rw [show BitVec.toNat (128 : BitVec 64) = 128 from rfl,
                      Nat.mod_eq_of_lt hst_64] at h1; exact h1
                  have hwstk_cref : s.core.wstk[(BitVec.ofNat 64 pi + 1#64).toNat]'hpi1_bv = cref :=
                    Option.some.inj (by
                      rw [← List.getElem?_eq_getElem hpi1_bv, BitVec.toNat_add, BitVec.toNat_ofNat,
                        Nat.mod_eq_of_lt hpi_64, show (1#64 : BitVec 64).toNat = 1 from rfl,
                        Nat.mod_eq_of_lt hpi1_64]; exact hw1_p)
                  have har := hcref_wf.1; unfold dimacsBound at har; have ha := c.harena
                  have hcr2 : (BitVec.setWidth 64 (s.core.wstk[(BitVec.ofNat 64 pi +
                      1#64).toNat]'hpi1_bv) + 2#64).toNat < s.core.arena.length := by
                    rw [hwstk_cref, BitVec.toNat_add, m6_zext32,
                      show (2#64 : BitVec 64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
                    have h1 := hlen1.core_ok.arena_len_le; have h2 := hlen1.core_ok.arena_len_arr
                    dsimp only at h1 h2; omega
                  have hcr0 : (BitVec.setWidth 64 (s.core.wstk[(BitVec.ofNat 64 pi +
                      1#64).toNat]'hpi1_bv)).toNat < s.core.arena.length := by
                    rw [hwstk_cref, m6_zext32]
                    have h1 := hlen1.core_ok.arena_len_le; have h2 := hlen1.core_ok.arena_len_arr
                    dsimp only at h1 h2; omega
                  have hstep2 : ∀ flags2 m2, M6RearmStInv c F0 F_cur s R flags2 m2 →
                      J1 (BitVec.ofNat 64 pi + 1 + 1, BitVec.ofNat 64 steps + 1, ()) m2 := by
                    intro flags2 m2 hinv2
                    rw [m6_bv64_add1_ofNat (n := pi) (by omega),
                      m6_bv64_add1_ofNat (n := pi + 1) (by omega),
                      m6_bv64_add1_ofNat (n := steps) (by omega)]
                    exact ih1 ⟨pi + 2, steps + 1, flags2⟩ m2 (by dsimp only; omega)
                      ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
                       by dsimp only; rw [show wEnd - (pi + 2) = rem by omega]; exact hrest, hinv2⟩
                  c0_hsteps_nogrp
                  · exact hstep2 flags1 m1 ⟨hfl1_len, hinv1, hm1⟩
                  · exact hstep2 flags1 m1 ⟨hfl1_len, hinv1, hm1⟩
                  · have har2 := m6_rearm_occ_ar2_eq hlen hcref_wf.1 hpi1_64 hw1_p
                    clear hpol_lt hpol_le hfl_len hinv_lp hm_lp hlen_lp ih
                    try clear hpi_lo hpi_hi hst_le hpi_33 hst_64 hwEnd_v hst_lt hpi1_lt hpi_lt
                    try clear hw0_lt hw1_lt hslice0 hw0_at hwEnd_c hwEnd_le hwEnd_33 hwf hrem hrest
                    refine wp_while_state (ts := [i32]) (α := Nat × List (BitVec 32))
                      (fun st => (BitVec.ofNat 32 st.1, ()))
                      (fun st => (s.core.arena[(BitVec.setWidth 64 cref +
                        2#64).toNat]?.getD 0#32).toNat - st.1)
                      (fun st m2 => st.1 ≤ (s.core.arena[(BitVec.setWidth 64 cref +
                        2#64).toNat]?.getD 0#32).toNat ∧
                        M6RearmStInv c F0 F_cur s R st.2 m2) ?_ ?_
                    · intro J_c hJ_c; c0_hsteps_nogrp
                      exact hJ_c (0, flags1) m1 ⟨Nat.zero_le _, hfl1_len, hinv1, hm1⟩
                    · rintro J_c ⟨i, flags2⟩ m2 ⟨hi_le, hfl2_len, hinv2, hm2⟩ ih_c
                      dsimp only at hi_le hfl2_len hinv2 hm2 ih_c
                      clear hm1 hinv1 hfl1_len hlen1
                      c0_hsteps_nogrp
                      · have hsz_le16 : (s.core.arena[(BitVec.setWidth 64 cref +
                            2#64).toNat]?.getD 0#32).toNat ≤ 16 := by
                          have h1 := ‹¬ BitVec.toNat (16 : BitVec 32) < _›
                          have h16 : BitVec.toNat (16 : BitVec 32) = 16 := rfl
                          rw [har2 _ _, h16] at h1; omega
                        have hi_lt_sz : i < (s.core.arena[(BitVec.setWidth 64 cref +
                            2#64).toNat]?.getD 0#32).toNat := by
                          have hc_i := ‹i % 2 ^ 32 < _›
                          rw [har2 _ _, Nat.mod_eq_of_lt (by omega)] at hc_i; exact hc_i
                        have hari_lt := m6_rearm_occ_ari_lt hlen hcref_wf.1 hcref_sz
                          hwstk_cref hi_lt_sz
                        c0_hsteps_nogrp
                        refine wp_join0 (fun m3 =>
                            ∃ flags3, M6RearmStInv c F0 F_cur s R flags3 m3) ?_ ?_
                        · rintro Js m3 ⟨flags3, hinv3⟩; c0_hsteps_nogrp
                          rw [m6_bv32_add1_ofNat (n := i) (by omega)]
                          exact ih_c (i + 1, flags3) m3 (by dsimp only; omega)
                            ⟨by dsimp only; omega, hinv3⟩
                        · intro Js hJs; c0_hsteps_nogrp
                          · rename_i hlt _
                            have hu_fl2 : (BitVec.setWidth 64
                                (s.core.arena[(BitVec.setWidth 64 (s.core.wstk[(BitVec.ofNat 64 pi +
                                    1#64).toNat]'hpi1_bv) + 3#64 + BitVec.setWidth 64
                                    (BitVec.ofNat 32 i)).toNat]'hari_lt >>>
                                  OfNat.ofNat 1 : BitVec 32)).toNat < flags2.length := by
                              have hw1_idx : (BitVec.ofNat 64 pi + 1#64).toNat =
                                  (pi + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 := by
                                rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp [Nat.add_mod]
                              have hws : s.core.wstk[(BitVec.ofNat 64 pi + 1#64).toNat]'hpi1_bv =
                                  s.core.wstk[(pi + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(
                                    hw1_idx ▸ hpi1_bv) := by congr 1
                              have har_idx : (BitVec.setWidth 64 (s.core.wstk[(BitVec.ofNat 64 pi +
                                  1#64).toNat]'hpi1_bv) + 3#64 + BitVec.setWidth 64
                                  (BitVec.ofNat 32 i)).toNat =
                                  ((s.core.wstk[(pi + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(
                                    hw1_idx ▸ hpi1_bv)).toNat +
                                    BitVec.toNat (3 : BitVec 64) + i % 2 ^ 32) % 2 ^ 64 := by
                                rw [hws, BitVec.toNat_add, BitVec.toNat_add, m6_zext32, m6_zext32,
                                  BitVec.toNat_ofNat]; simp [Nat.add_mod]
                              have ha_eq : s.core.arena[(BitVec.setWidth 64 (s.core.wstk[(
                                  BitVec.ofNat 64 pi + 1#64).toNat]'hpi1_bv) + 3#64 +
                                  BitVec.setWidth 64 (BitVec.ofNat 32 i)).toNat]'hari_lt =
                                  s.core.arena[((s.core.wstk[(pi +
                                    BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(hw1_idx ▸
                                      hpi1_bv)).toNat + BitVec.toNat (3 : BitVec 64) +
                                      i % 2 ^ 32) % 2 ^ 64]'(har_idx ▸ hari_lt) := by congr 1
                              rw [m6_zext32, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                ha_eq, hfl2_len]
                              rw [Nat.mod_eq_of_lt h64] at hlt; omega
                            c0_hsteps_nogrp
                            · dsimp only at hm
                              exact hJs _ ⟨_, by simp [hfl2_len],
                                m6_fullDenseInvW_with_flags hinv2 (by simp [hfl2_len]), hm⟩
                            all_goals exact hJs _ ⟨flags2, hfl2_len, hinv2, hm2⟩
                          all_goals exact hJs _ ⟨flags2, hfl2_len, hinv2, hm2⟩
                      · exact hstep2 flags2 m2 ⟨hfl2_len, hinv2, hm2⟩
            all_goals
              exact hJ_out (BitVec.ofNat 64 pi, BitVec.ofNat 64 steps, ()) m1
                ⟨flags1, hfl1_len, hinv1, hm1⟩
      · have hpol2 : pol = 2 := by bv_omega
        subst hpol2; c0_hsteps_nogrp; exact hQ flags_lp m_lp hfl_len hinv_lp hm_lp

/-! ## 1b. PHT & Partition Invariant Helpers -/

private theorem m6_bvt32_and_1023_lt (x : BitVec 64) :
    (BitVec.truncate 32 (x &&& 1023#64)).toNat < k6PhtSz := by
  have h1 := M6SweepTactics.m6_bv64_and_1023 x; unfold k6PhtSz
  change (BitVec.setWidth 32 (x &&& 1023#64)).toNat < 1024
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by rw [h1]; omega), h1]
  exact Nat.mod_lt _ (by decide)

private theorem m6_phtHead_add_toNat {b : BitVec 32} (hb : b.toNat < k6PhtSz) :
    (BitVec.setWidth 64 (256#32 + b)).toNat = k6PhtHead + b.toNat := by
  unfold k6PhtSz k6PhtHead at *
  rw [m6_zext32, BitVec.toNat_add, show (256#32 : BitVec 32).toNat = 256 from rfl,
    Nat.mod_eq_of_lt (by omega)]

private theorem m6_phtHead_idx_lt {b : BitVec 32} {len : Nat}
    (hb : b.toNat < k6PhtSz) (hlen : 1280 ≤ len) :
    (BitVec.setWidth 64 (256#32 + b)).toNat < len := by
  rw [m6_phtHead_add_toNat hb]; unfold k6PhtHead k6PhtSz at *; omega

private theorem m6_pht_insert_ok {scr0 scr1 : List (BitVec 32)}
    {cap nv k : Nat} {L : K6Layout} {b : BitVec 32}
    (hL : L.scrLen = cap) (hscr1 : scr1.length = cap)
    (hk_lt : k < nv) (hnv_le : nv ≤ L.maxV) (hb : b.toNat < k6PhtSz)
    (hpref : ∀ j < cap, j < k6PhtHead ∨ L.phtMerged ≤ j → scr1[j]? = scr0[j]?)
    (hpht : M6PhtOk k scr1) :
    let old := scr1[k6PhtHead + b.toNat]?.getD 0xFFFFFFFF#32
    let scr2 := (scr1.set (k6PhtNext + k) old).set (k6PhtHead + b.toNat) (BitVec.ofNat 32 k)
    scr2.length = cap ∧ (∀ j < cap, j < k6PhtHead ∨ L.phtMerged ≤ j → scr2[j]? = scr0[j]?) ∧
    M6PhtOk (k + 1) scr2 := by
  intro old scr2
  have hmaxv := L.hmaxV; have hnx_bd := m6_scr_nx_lt hL hscr1 (by omega : k < L.maxV)
  have hhd_bd := m6_scr_hd_lt hL hscr1 hb
  have hpref1 : ∀ j < cap, j < k6PhtHead ∨ L.phtMerged ≤ j →
      (scr1.set (k6PhtNext + k) old)[j]? = scr0[j]? := by
    refine m6_set_scr_pref_other old hpref ?_
    unfold K6Layout.phtMerged k6PhtHead k6PhtNext; omega
  have hpref2 : ∀ j < cap, j < k6PhtHead ∨ L.phtMerged ≤ j → scr2[j]? = scr0[j]? := by
    refine m6_set_scr_pref_other (BitVec.ofNat 32 k) hpref1 ?_
    unfold K6Layout.phtMerged k6PhtHead k6PhtSz at *; omega
  refine ⟨by simp [scr2, hscr1], hpref2, fun b' hb' => ?_, fun j hj => ?_⟩
  · by_cases hbe : b' = b.toNat
    · subst hbe; rw [List.getElem?_set_self (by simpa [scr2] using hhd_bd), Option.getD_some]
      exact Or.inr (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by
        unfold k6PhtNext k6PhtHead k6PhtSz at *; omega)]
      rcases hpht.1 b' hb' with h | h; exact Or.inl h; exact Or.inr (by omega)
  · rw [List.getElem?_set_ne (by unfold k6PhtHead k6PhtNext k6PhtSz at *; omega)]
    by_cases hjk : j = k
    · subst hjk; rw [List.getElem?_set_self hnx_bd, Option.getD_some]; exact hpht.1 b.toNat hb
    · rw [List.getElem?_set_ne (by omega)]
      rcases hpht.2 j (by omega) with h | h; exact Or.inl h; exact Or.inr h

private theorem m6_pht_set_next_ok {scr0 scr : List (BitVec 32)}
    {cap nv idx : Nat} {L : K6Layout} (v : BitVec 32)
    (hL : L.scrLen = cap) (hscr : scr.length = cap) (hidx : idx < nv) (hnv_le : nv ≤ L.maxV)
    (hv : v = 0xFFFFFFFF#32 ∨ v.toNat < idx)
    (hpref : ∀ j < cap, j < k6PhtHead ∨ L.phtMerged ≤ j → scr[j]? = scr0[j]?)
    (hpht : M6PhtOk nv scr) :
    let scr' := scr.set (k6PhtNext + idx) v
    scr'.length = cap ∧ (∀ j < cap, j < k6PhtHead ∨ L.phtMerged ≤ j → scr'[j]? = scr0[j]?) ∧
    M6PhtOk nv scr' := by
  intro scr'
  have hnx_bd := m6_scr_nx_lt hL hscr (by omega : idx < L.maxV)
  have hpref' : ∀ j < cap, j < k6PhtHead ∨ L.phtMerged ≤ j → scr'[j]? = scr0[j]? := by
    refine m6_set_scr_pref_other v hpref ?_; unfold K6Layout.phtMerged k6PhtHead k6PhtNext; omega
  refine ⟨by simp [scr', hscr], hpref', fun b' hb' => ?_, fun j hj => ?_⟩
  · rw [List.getElem?_set_ne (by unfold k6PhtHead k6PhtNext k6PhtSz at *; omega)]
    exact hpht.1 b' hb'
  · by_cases hje : j = idx
    · subst hje; rw [List.getElem?_set_self hnx_bd, Option.getD_some]; exact hv
    · rw [List.getElem?_set_ne (by omega)]; exact hpht.2 j hj

private theorem m6_pht_set_head_ok {scr0 scr : List (BitVec 32)}
    {cap nv b : Nat} {L : K6Layout} (v : BitVec 32)
    (hL : L.scrLen = cap) (hscr : scr.length = cap) (hb : b < k6PhtSz)
    (hv : v = 0xFFFFFFFF#32 ∨ v.toNat < nv)
    (hpref : ∀ j < cap, j < k6PhtHead ∨ L.phtMerged ≤ j → scr[j]? = scr0[j]?)
    (hpht : M6PhtOk nv scr) :
    let scr' := scr.set (k6PhtHead + b) v
    scr'.length = cap ∧ (∀ j < cap, j < k6PhtHead ∨ L.phtMerged ≤ j → scr'[j]? = scr0[j]?) ∧
    M6PhtOk nv scr' := by
  intro scr'; have hhd_bd := m6_scr_hd_lt hL hscr hb
  have hpref' : ∀ j < cap, j < k6PhtHead ∨ L.phtMerged ≤ j → scr'[j]? = scr0[j]? := by
    refine m6_set_scr_pref_other v hpref ?_; unfold K6Layout.phtMerged k6PhtHead k6PhtSz at *; omega
  refine ⟨by simp [scr', hscr], hpref', fun b' hb' => ?_, fun j hj => ?_⟩
  · by_cases hbe : b' = b
    · subst hbe; rw [List.getElem?_set_self hhd_bd, Option.getD_some]; exact hv
    · rw [List.getElem?_set_ne (by omega)]; exact hpht.1 b' hb'
  · rw [List.getElem?_set_ne (by unfold k6PhtHead k6PhtNext k6PhtSz at *; omega)]; exact hpht.2 j hj

/-! ## 2. `full_m6_sweep_build_pht` -/

theorem full_m6_sweep_build_pht_wp (Γ : Env)
    (hMaxV : Γ.Has "full_m6_max_v" m6MaxVSpec) :
    ∀ args m Q X, fullM6SweepBuildPhtSpec args m Q X →
      Func.wp Γ full_m6_sweep_build_pht_body args m Q X := by
  rintro ⟨h, nv, smask, ⟨⟩⟩ m Q X
    ⟨c, s, L, R, rfl, hlen, hscrLen, hmaxV, hnv_le, hnv_mv, hstk, hm, hQ⟩
  have hcap64 : c.scratch_cap < 2 ^ 64 := by have := c.hscr; unfold dimacsBound at this; omega
  have hL_max := L.hmaxV
  dsimp only [Func.wp]; unfold full_m6_sweep_build_pht_body
  c0_hsteps_nogrp; refine k6_maxV_call_step hMaxV hcap64 ?_; c0_hsteps_nogrp
  have hmv32 : BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) = L.mv32 := by
    apply BitVec.eq_of_toNat_eq; have := hL_max.2; simp [K6Layout.mv32, ← hmaxV]
  rw [hmv32]
  refine wp_while_state (ts := [i32]) (α := Nat × List (BitVec 32))
    (fun st => (BitVec.ofNat 32 st.1, ())) (fun st => 1024 - st.1)
    (fun st m' => st.1 ≤ 1024 ∧ st.2.length = c.scratch_cap ∧
      (∀ i < c.scratch_cap, i < k6PhtHead ∨ L.phtMerged ≤ i →
        st.2[i]? = s.scratch.scratch_buf[i]?) ∧
      (∀ b < st.1, st.2[k6PhtHead + b]? = some 0xFFFFFFFF#32) ∧
      (FullMem c { s with scratch := { s.scratch with scratch_buf := st.2 } } ⋆ R) m') ?_ ?_
  · intro J0 hJ0; c0_hsteps_nogrp
    exact hJ0 (0, s.scratch.scratch_buf) _ ⟨Nat.zero_le 1024, hlen.scratch_ok.scratch_buf_len,
      fun _ _ _ => rfl, fun _ hb => absurd hb (Nat.not_lt_zero _), hm⟩
  · rintro J0 ⟨i, scr⟩ m' ⟨hi_le, hscr_len, hpref, hinit, hm'⟩ ih
    dsimp only at hi_le hscr_len hpref hinit hm' ih
    c0_hsteps_nogrp
    · have hi_lt : i < 1024 := by bv_omega
      have hbi : (BitVec.ofNat 32 i).toNat = i := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hidx : (BitVec.setWidth 64 (256#32 + BitVec.ofNat 32 i)).toNat = k6PhtHead + i := by
        unfold k6PhtHead; rw [m6_zext32]; bv_omega
      have hbd : (256#32 + BitVec.ofNat 32 i).toNat < scr.length := by
        have := m6_scr_hd_lt hscrLen hscr_len (show i < k6PhtSz by unfold k6PhtSz; exact hi_lt)
        unfold k6PhtHead at this; bv_omega
      c0_hsteps_nogrp
      have hpref' : ∀ j < c.scratch_cap, j < k6PhtHead ∨ L.phtMerged ≤ j →
          (scr.set (k6PhtHead + i) 0xFFFFFFFF#32)[j]? = s.scratch.scratch_buf[j]? := by
        refine m6_set_scr_pref_other 0xFFFFFFFF#32 hpref ?_
        unfold K6Layout.phtMerged k6PhtHead; omega
      have hinit' : ∀ b < i + 1,
          (scr.set (k6PhtHead + i) 0xFFFFFFFF#32)[k6PhtHead + b]? = some 0xFFFFFFFF#32 := by
        intro b hb; by_cases hbi_eq : b = i
        · subst hbi_eq
          rw [List.getElem?_set_self (m6_scr_hd_lt hscrLen hscr_len
            (by unfold k6PhtSz; exact hi_lt))]
        · rw [List.getElem?_set_ne (by omega)]; exact hinit b (by omega)
      dsimp only at hm
      have hm_st : (FullMem c { s with scratch := { s.scratch with
          scratch_buf := scr.set (k6PhtHead + i) 0xFFFFFFFF#32 } } ⋆ R) m := by
        rw [← hidx]; exact hm
      change J0 (BitVec.ofNat 32 i + 1, ()) m
      rw [m6_bv32_add1_ofNat (n := i) (by omega)]
      exact ih (i + 1, scr.set (k6PhtHead + i) 0xFFFFFFFF#32) m (by omega)
        ⟨by omega, by simp [hscr_len], hpref', hinit', hm_st⟩
    · have hi_eq : i = 1024 := by bv_omega
      subst hi_eq; clear hm
      refine wp_while_state (ts := [i32]) (α := Nat × List (BitVec 32))
        (fun st => (BitVec.ofNat 32 st.1, ())) (fun st => nv.toNat - st.1)
        (fun st m'' => st.1 ≤ nv.toNat ∧ st.2.length = c.scratch_cap ∧
          (∀ j < c.scratch_cap, j < k6PhtHead ∨ L.phtMerged ≤ j →
            st.2[j]? = s.scratch.scratch_buf[j]?) ∧
          M6PhtOk st.1 st.2 ∧
          (FullMem c { s with scratch := { s.scratch with scratch_buf := st.2 } } ⋆ R) m'') ?_ ?_
      · intro J1 hJ1; c0_hsteps_nogrp
        refine hJ1 (0, scr) m' ⟨Nat.zero_le _, hscr_len, hpref, ?_, hm'⟩
        exact ⟨fun b hb => Or.inl (by rw [hinit b hb, Option.getD_some]),
          fun _ hk => absurd hk (Nat.not_lt_zero _)⟩
      · rintro J1 ⟨k, scr1⟩ m1 ⟨hk_le, hscr1_len, hpref1, hpht1, hm1⟩ ih1
        dsimp only at hk_le hscr1_len hpref1 hpht1 hm1 ih1
        have hlen1 : ({ s with scratch := { s.scratch with scratch_buf := scr1 } } :
            FullState).LengthsOk c :=
          ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hscr1_len }⟩
        c0_hsteps_nogrp
        · have hk_lt : k < nv.toNat := by bv_omega
          have hk_mv : k < L.maxV := by omega
          have hwk1 : (BitVec.ofNat 32 k).toNat < ({ s with scratch := { s.scratch with
              scratch_buf := scr1 } } : FullState).scratch.work_stk1.length := by
            rw [hlen1.scratch_ok.work_stk1_len]; bv_omega
          c0_hsteps_nogrp
          refine wp_join0 (fun m2 => ∃ scr2, scr2.length = c.scratch_cap ∧
              (∀ j < c.scratch_cap, j < k6PhtHead ∨ L.phtMerged ≤ j →
                scr2[j]? = s.scratch.scratch_buf[j]?) ∧
              M6PhtOk (k + 1) scr2 ∧ (FullMem c { s with scratch :=
                { s.scratch with scratch_buf := scr2 } } ⋆ R) m2) ?_ ?_
          · rintro J_k m2 ⟨scr2, hscr2_len, hpref2, hpht2, hm2⟩
            c0_hsteps_nogrp; rw [m6_bv32_add1_ofNat (n := k) (by omega)]
            exact ih1 (k + 1, scr2) m2 (by omega) ⟨by omega, hscr2_len, hpref2, hpht2, hm2⟩
          · intro J_k hJ_k
            have hk_bi_mv : (BitVec.ofNat 32 k).toNat < L.maxV := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hk_mv
            c0_hsteps_nogrp
            refine wp_join0 (fun m_sk => (FullMem c { s with scratch :=
                { s.scratch with scratch_buf := scr1 } } ⋆ R) m_sk) ?_ ?_
            · rintro Js m_sk hm_sk; c0_hsteps_nogrp
              have hpref2 : ∀ j < c.scratch_cap, j < k6PhtHead ∨ L.phtMerged ≤ j →
                  (scr1.set (k6PhtNext + k) 0xFFFFFFFF#32)[j]? = s.scratch.scratch_buf[j]? := by
                refine m6_set_scr_pref_other 0xFFFFFFFF#32 hpref1 ?_
                unfold K6Layout.phtMerged k6PhtHead k6PhtNext; omega
              have hpht2 : M6PhtOk (k + 1) (scr1.set (k6PhtNext + k) 0xFFFFFFFF#32) := by
                refine ⟨fun b hb => ?_, fun j hj => ?_⟩
                · rw [List.getElem?_set_ne (by unfold k6PhtHead k6PhtNext k6PhtSz at *; omega)]
                  rcases hpht1.1 b hb with h | h; exact Or.inl h; exact Or.inr (by omega)
                · by_cases hjk : j = k
                  · subst hjk
                    rw [List.getElem?_set_self (m6_scr_nx_lt hscrLen hscr1_len hk_mv)]
                    exact Or.inl rfl
                  · rw [List.getElem?_set_ne (by omega)]; exact hpht1.2 j (by omega)
              have hbi : (BitVec.ofNat 32 k).toNat = k := by
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
              dsimp only [k6PhtNext] at hm ⊢; rw [hbi] at hm
              exact hJ_k _ ⟨_, by simp [hscr1_len], hpref2, hpht2, hm⟩
            · intro Js hJs; dsimp only at hlen1
              have hwk1_v := hstk k hk_lt
              have hk_wk : k < s.scratch.work_stk1.length := by
                rw [hlen1.scratch_ok.work_stk1_len]; bv_omega
              have hbi : (BitVec.ofNat 32 k).toNat = k := by
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
              have hbi64 : (BitVec.setWidth 64 (BitVec.ofNat 32 k)).toNat = k := by
                rw [m6_zext32, hbi]
              have hv_val : (BitVec.setWidth 64
                  (s.scratch.work_stk1[(BitVec.setWidth 64 (BitVec.ofNat 32 k)).toNat]'hwk1 <<<
                    (1#32 : BitVec 32))).toNat < s.core.vals.length := by
                have h1 := hlen1.core_ok.vals_len; have h2 := hlen1.core_ok.cur_vars_le
                have h3 := c.hmaxv; dsimp only [dimacsBound] at h1 h2 h3
                have hget : s.scratch.work_stk1[
                    (BitVec.setWidth 64 (BitVec.ofNat 32 k)).toNat]'hwk1 =
                    s.scratch.work_stk1[k]'hk_wk := by congr 1
                rw [List.getElem?_eq_getElem hk_wk, Option.getD_some] at hwk1_v
                rw [m6_zext32, hget,
                  m6_bv32_shl1_toNat (by omega : s.scratch.work_stk1[k].toNat < 2 ^ 31)]; omega
              have hsig_lt : (BitVec.setWidth 64 (s.scratch.work_stk1[
                  (BitVec.setWidth 64 (BitVec.ofNat 32 k)).toNat]'hwk1)).toNat <
                  s.scratch.sim_sig.length := by
                have h1 := hlen1.scratch_ok.sim_sig_len
                have h2 := hlen1.core_ok.cur_vars_le; dsimp only at h1 h2
                have hget : s.scratch.work_stk1[
                    (BitVec.setWidth 64 (BitVec.ofNat 32 k)).toNat]'hwk1 =
                    s.scratch.work_stk1[k]'hk_wk := by congr 1
                rw [hget, m6_zext32]
                rw [List.getElem?_eq_getElem hk_wk, Option.getD_some] at hwk1_v; omega
              dsimp only; c0_hsteps_nogrp
              · refine wp_join_group (ts := [i64]) (fun _ m2 => m2 = m1) ?_ ?_
                · rintro Js' ⟨hval, ⟨⟩⟩ m2 rfl; c0_hsteps_nogrp
                  have hscr1_ge : 1280 ≤ scr1.length := by
                    rw [hscr1_len.trans hscrLen.symm]; unfold K6Layout.scrLen K6Layout.k6Base
                    have := L.hmaxV.1; omega
                  let b32 := BitVec.truncate 32
                    ((((hval ^^^ hval >>> (BitVec.signExtend 64 17#32)) ^^^
                      hval >>> (BitVec.signExtend 64 34#32)) ^^^
                      hval >>> (BitVec.signExtend 64 51#32)) &&& 1023#64)
                  have hb_lt : b32.toNat < k6PhtSz := m6_bvt32_and_1023_lt _
                  have hscr_b : (BitVec.setWidth 64 (256#32 + b32)).toNat < scr1.length :=
                    m6_phtHead_idx_lt hb_lt hscr1_ge
                  c0_hsteps_nogrp
                  have hscr_b2 : (BitVec.setWidth 64 (256#32 + b32)).toNat <
                      (scr1.set (k6PhtNext + (BitVec.ofNat 32 k).toNat)
                        (scr1[(BitVec.setWidth 64 (256#32 + b32)).toNat]'hscr_b)).length := by
                    rw [List.length_set]; exact hscr_b
                  c0_hsteps_nogrp
                  have hok := m6_pht_insert_ok hscrLen hscr1_len hk_lt hnv_le hb_lt hpref1 hpht1
                  dsimp only at hok
                  have hbi_eq : (BitVec.setWidth 64 (256 + BitVec.setWidth 32
                      ((hval ^^^ hval >>> (17 : BitVec 64) ^^^ hval >>> (34 : BitVec 64) ^^^
                        hval >>> (51 : BitVec 64)) &&& BitVec.ofNat 64 1023))).toNat =
                      k6PhtHead + b32.toNat := m6_phtHead_add_toNat hb_lt
                  have hget_hd : ∀ h_p, scr1[(BitVec.setWidth 64 (256 + BitVec.setWidth 32
                      ((hval ^^^ hval >>> (17 : BitVec 64) ^^^ hval >>> (34 : BitVec 64) ^^^
                        hval >>> (51 : BitVec 64)) &&& BitVec.ofNat 64 1023))).toNat]'h_p =
                      scr1[k6PhtHead + b32.toNat]'(m6_scr_hd_lt hscrLen hscr1_len hb_lt) :=
                    fun _ => by congr 1
                  have hk32 : (BitVec.ofNat 32 k).toNat = k := by
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                  dsimp only [k6PhtNext] at hm ⊢
                  try rw [hbi64] at hm ⊢
                  try rw [hbi] at hm ⊢
                  erw [hget_hd] at hm
                  erw [hbi_eq] at hm
                  rw [hk32] at hm
                  rw [← m6_getElem_eq_getD scr1
                    (m6_scr_hd_lt hscrLen hscr1_len hb_lt) 0xFFFFFFFF#32] at hok
                  exact hJ_k _ ⟨_, hok.1, hok.2.1, hok.2.2, hm⟩
                · intro Js' hJs'; c0_hsteps_nogrp <;> exact hJs' _ m1 rfl
              · exact hJs _ hm1
              · exact hJs _ hm1
        · have hk_eq : k = nv.toNat := by bv_omega
          subst hk_eq; c0_hsteps_nogrp; exact hQ scr1 m1 hscr1_len hpref1 hpht1 hm1

/-! ## 3. `full_m6_extract_pht` -/

private structure M6ExtSt where
  ncls : Nat
  b : Nat
  scr : List (BitVec 32)
  sstk : List (BitVec 32)
  mclr : List (BitVec 32)

private structure M6ExtCh where
  prev : BitVec 32
  tail : BitVec 32
  cnt : Nat
  k : BitVec 32
  rem : Nat
  scr : List (BitVec 32)
  mclr : List (BitVec 32)

private abbrev M6ExtStOf (s : FullState) (scr sstk mclr : List (BitVec 32)) : FullState :=
  { s with
    core := { s.core with min_clr := mclr }
    scratch := { s.scratch with scratch_buf := scr, shrink_stk := sstk } }

private abbrev M6ExtScrInv (c : FullCfg) (L : K6Layout) (nv : BitVec 32) (s : FullState)
    (scr : List (BitVec 32)) : Prop :=
  scr.length = c.scratch_cap ∧
  (∀ i < c.scratch_cap, i < k6PhtHead ∨ L.phtMerged ≤ i → scr[i]? = s.scratch.scratch_buf[i]?) ∧
  M6PhtOk nv.toNat scr

private abbrev M6ExtStInv (c : FullCfg) (L : K6Layout) (nv : BitVec 32) (s : FullState)
    (R : Mem 64 → Prop) (st : M6ExtSt) (m' : Mem 64) : Prop :=
  st.b ≤ 1024 ∧ st.ncls ≤ c.max_vars ∧ st.sstk.length = c.max_vars ∧ st.mclr.length = c.max_vars ∧
  (∀ ci < st.ncls, (st.sstk[ci]?.getD 0xFFFFFFFF#32).toNat < nv.toNat) ∧
  M6ExtScrInv c L nv s st.scr ∧ (FullMem c (M6ExtStOf s st.scr st.sstk st.mclr) ⋆ R) m'

private abbrev M6ExtChInv (c : FullCfg) (L : K6Layout) (nv : BitVec 32) (s : FullState)
    (R : Mem 64 → Prop) (sstk : List (BitVec 32)) (st : M6ExtCh) (m' : Mem 64) : Prop :=
  st.rem ≤ nv.toNat ∧ st.rem + st.cnt ≤ nv.toNat + 1 ∧ st.tail.toNat < nv.toNat ∧
  (st.k = 0xFFFFFFFF#32 ∨ (st.k.toNat < nv.toNat ∧ st.k.toNat < st.tail.toNat)) ∧
  (st.prev = 0xFFFFFFFF#32 ∨
    (st.prev.toNat < nv.toNat ∧ (st.k = 0xFFFFFFFF#32 ∨ st.k.toNat < st.prev.toNat))) ∧
  st.mclr.length = c.max_vars ∧ M6ExtScrInv c L nv s st.scr ∧
  (FullMem c (M6ExtStOf s st.scr sstk st.mclr) ⋆ R) m'

theorem full_m6_extract_pht_wp (Γ : Env)
    (hMaxV : Γ.Has "full_m6_max_v" m6MaxVSpec) :
    ∀ args m Q X, fullM6ExtractPhtSpec args m Q X →
      Func.wp Γ full_m6_extract_pht_body args m Q X := by
  rintro ⟨h, nv, smask, ⟨⟩⟩ m Q X
    ⟨c, s, L, R, rfl, hlen, hscrLen, hmaxV, hnv_le, hnv_mv, hstk, hpht, hm, hQ⟩
  have hcap64 : c.scratch_cap < 2 ^ 64 := by have := c.hscr; unfold dimacsBound at this; omega
  have hmv_db := c.hmaxv; unfold dimacsBound at hmv_db; have hL_max := L.hmaxV
  dsimp only [Func.wp]; unfold full_m6_extract_pht_body
  c0_hsteps_nogrp; refine k6_maxV_call_step hMaxV hcap64 ?_; c0_hsteps_nogrp
  refine wp_while_state (ts := [i32, i32]) (α := M6ExtSt)
    (fun st => (BitVec.ofNat 32 st.ncls, BitVec.ofNat 32 st.b, ()))
    (fun st => 1024 - st.b) (M6ExtStInv c L nv s R) ?_ ?_
  · intro J0 hJ0; c0_hsteps_nogrp
    exact hJ0 ⟨0, 0, s.scratch.scratch_buf, s.scratch.shrink_stk, s.core.min_clr⟩ _
      ⟨Nat.zero_le 1024, Nat.zero_le _, hlen.scratch_ok.shrink_stk_len,
       hlen.core_ok.min_clr_len_arr, fun _ hci => absurd hci (Nat.not_lt_zero _),
       ⟨hlen.scratch_ok.scratch_buf_len, fun _ _ _ => rfl, hpht⟩, hm⟩
  · rintro J0 ⟨ncls, b, scr, sstk, mclr⟩ m'
      ⟨hb_le, hnc_mv, hsstk_len, hmclr_len, hs_hd, hscr_inv, hm'⟩ ih
    obtain ⟨hscr_len, hpref, hpht_lp⟩ := hscr_inv
    dsimp only at hb_le hnc_mv hsstk_len hmclr_len hs_hd hscr_len hpref hpht_lp hm' ih
    c0_hsteps_nogrp
    · have hb_lt : b < 1024 := by
        have h1 := ‹(BitVec.ofNat 32 b).toNat < BitVec.toNat 1024›
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1; exact h1
      clear hm
      refine wp_while_state (ts := [i32, i32]) (α := Nat × M6ExtSt)
        (fun st => (BitVec.ofNat 32 st.2.ncls, BitVec.ofNat 32 st.1, ())) (fun st => st.1)
        (fun st m1 => st.1 ≤ nv.toNat ∧ st.2.b = b ∧ M6ExtStInv c L nv s R st.2 m1) ?_ ?_
      · intro J_lim hJ_lim; c0_hsteps_nogrp
        have hnv_eq := hJ_lim (nv.toNat, ⟨ncls, b, scr, sstk, mclr⟩) m'
          ⟨Nat.le_refl _, rfl, hb_le, hnc_mv, hsstk_len, hmclr_len, hs_hd,
           ⟨hscr_len, hpref, hpht_lp⟩, hm'⟩
        simpa [BitVec.ofNat_toNat] using hnv_eq
      · rintro J_lim ⟨lim, ncls1, b1, scr1, sstk1, mclr1⟩ m1
          ⟨hlim_le, hb_b1, _, hnc1, hsstk1, hmclr1, hs_hd1, hscr1_inv, hm1⟩ ih1
        obtain ⟨hscr1, hpref1, hpht1⟩ := hscr1_inv
        dsimp only at hlim_le hb_b1 hnc1 hsstk1 hmclr1 hs_hd1 hscr1 hpref1 hpht1 hm1 ih ih1
        subst b1
        refine wp_join0 (fun m2 => ∃ scr2 sstk2 mclr2,
            sstk2.length = c.max_vars ∧ mclr2.length = c.max_vars ∧
            (∀ ci < ncls1, (sstk2[ci]?.getD 0xFFFFFFFF#32).toNat < nv.toNat) ∧
            M6ExtScrInv c L nv s scr2 ∧ (FullMem c (M6ExtStOf s scr2 sstk2 mclr2) ⋆ R) m2) ?_ ?_
        · rintro J_b m2 ⟨scr2, sstk2, mclr2, hsstk2, hmclr2, hs_hd2, hscr2, hm2⟩; c0_hsteps_nogrp
          change J0 (BitVec.ofNat 32 ncls1, BitVec.ofNat 32 b + 1, ()) m2
          rw [m6_bv32_add1_ofNat (n := b) (by omega)]
          exact ih ⟨ncls1, b + 1, scr2, sstk2, mclr2⟩ m2 (by dsimp only; omega)
            ⟨by dsimp only; omega, hnc1, hsstk2, hmclr2, hs_hd2, hscr2, hm2⟩
        · intro J_b hJ_b
          have hscr_b : (BitVec.setWidth 64 (256#32 + BitVec.ofNat 32 b)).toNat < scr1.length := by
            rw [hscr1.trans hscrLen.symm]; unfold K6Layout.scrLen K6Layout.k6Base; bv_omega
          have hb_idx_nat :
              (BitVec.setWidth 64 (256#32 + BitVec.ofNat 32 b)).toNat = k6PhtHead + b := by
            have hb32 : (BitVec.ofNat 32 b).toNat = b := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
            have := m6_phtHead_add_toNat (b := BitVec.ofNat 32 b)
              (by unfold k6PhtSz; rw [hb32]; exact hb_lt)
            rw [hb32] at this; exact this
          dsimp only; c0_hsteps_nogrp
          · have hhd_lt : (scr1[(BitVec.setWidth 64
                (256#32 + BitVec.ofNat 32 b)).toNat]'hscr_b).toNat < nv.toNat := by
              have hc1 := hpht1.1 b hb_lt
              rw [← hb_idx_nat, List.getElem?_eq_getElem hscr_b, Option.getD_some] at hc1
              rcases hc1 with hff | hlt
              · rename_i hcond
                have hidx_eq : (BitVec.setWidth 64 (256#32 + BitVec.ofNat 32 b)).toNat =
                    (BitVec.toNat (256 : BitVec 32) + (BitVec.ofNat 32 b).toNat) % 2 ^ 32 := by
                  rw [m6_zext32, BitVec.toNat_add]; rfl
                have hpt_eq :
                    scr1[(BitVec.setWidth 64 (256#32 + BitVec.ofNat 32 b)).toNat]'hscr_b =
                      scr1[(BitVec.toNat (256 : BitVec 32) +
                        (BitVec.ofNat 32 b).toNat) % 2 ^ 32]'(hidx_eq ▸ hscr_b) := by congr 1
                rw [hpt_eq]; simpa [BitVec.toNat_ofNat] using hcond
              · exact hlt
            let head0_r := scr1[(BitVec.setWidth 64 (256#32 + BitVec.ofNat 32 b)).toNat]'hscr_b
            have hhead_r_nv : head0_r.toNat < nv.toNat := hhd_lt
            have hmclr_h0 : (BitVec.setWidth 64 head0_r).toNat < mclr1.length := by
              rw [m6_zext32, hmclr1]; exact Nat.lt_of_lt_of_le hhead_r_nv hnv_mv
            have hwk_h0 : (BitVec.setWidth 64 head0_r).toNat < s.scratch.work_stk1.length := by
              rw [m6_zext32, hlen.scratch_ok.work_stk1_len]; omega
            have hsig_h0 : (BitVec.setWidth 64
                (s.scratch.work_stk1[(BitVec.setWidth 64 head0_r).toNat]'hwk_h0)).toNat <
                s.scratch.sim_sig.length := by
              have hget : s.scratch.work_stk1[(BitVec.setWidth 64 head0_r).toNat]'hwk_h0 =
                  s.scratch.work_stk1[head0_r.toNat]?.getD 0#32 := by
                rw [m6_getElem_eq_getD _ hwk_h0 0#32, m6_zext32]
              rw [hget, m6_zext32, hlen.scratch_ok.sim_sig_len]
              have := hstk head0_r.toNat hhead_r_nv; have := hlen.core_ok.cur_vars_le; omega
            c0_hsteps_nogrp
            · have hlim_pos : 0 < lim := by bv_omega
              let head0 := scr1[k6PhtHead + b]'(m6_scr_hd_lt hscrLen hscr1 hb_lt)
              have hhd_eq : ∀ h_p, scr1[(BitVec.setWidth 64
                  ((256 : BitVec 32) + BitVec.ofNat 32 b)).toNat]'h_p = head0 :=
                fun _ => by dsimp only [head0]; congr 1
              have hhead_nv : head0.toNat < nv.toNat := hhd_eq hscr_b ▸ hhd_lt
              have hhead_mv : head0.toNat < L.maxV := Nat.lt_of_lt_of_le hhead_nv hnv_le
              have hok_hd := m6_pht_set_head_ok 0xFFFFFFFF#32 hscrLen hscr1 hb_lt
                (Or.inl rfl) hpref1 hpht1
              dsimp only at hok_hd
              let scr_e0 := scr1.set (k6PhtHead + b) 0xFFFFFFFF#32
              let mclr_e0 := mclr1.set head0.toNat 0#32
              let nxt0 := scr_e0[k6PhtNext + head0.toNat]'(m6_scr_nx_lt hscrLen hok_hd.1 hhead_mv)
              refine wp_while_state (ts := [i32, i32, i32, i32, i32]) (α := M6ExtCh)
                (fun st => (st.prev, st.tail, BitVec.ofNat 32 st.cnt,
                  st.k, BitVec.ofNat 32 st.rem, ()))
                (fun st => st.rem) (M6ExtChInv c L nv s R sstk1) ?_ ?_
              · intro J_ch hJ_ch; c0_hsteps_nogrp
                have hnxt0_ok : nxt0 = 0xFFFFFFFF#32 ∨
                    (nxt0.toNat < nv.toNat ∧ nxt0.toNat < head0.toNat) := by
                  have hn := hok_hd.2.2.2 head0.toNat hhead_nv
                  dsimp only [scr_e0] at hn ⊢
                  rw [← m6_getElem_eq_getD _ (m6_scr_nx_lt hscrLen hok_hd.1 hhead_mv)
                    0xFFFFFFFF#32] at hn
                  rcases hn with h | h; exact Or.inl h; exact Or.inr ⟨Nat.lt_trans h hhead_nv, h⟩
                have hm_e0 : (FullMem c (M6ExtStOf s scr_e0 sstk1 mclr_e0) ⋆ R) m := by
                  dsimp only [M6ExtStOf, scr_e0, mclr_e0] at hm ⊢
                  erw [hhd_eq] at hm
                  erw [hb_idx_nat, m6_zext32 head0] at hm; exact hm
                simpa [head0, scr_e0, nxt0, k6PhtHead, BitVec.ofNat_toNat] using hJ_ch
                  ⟨0xFFFFFFFF#32, head0, 1, nxt0, nv.toNat, scr_e0, mclr_e0⟩ m
                  ⟨Nat.le_refl _, by dsimp only; omega, hhead_nv, hnxt0_ok, Or.inl rfl,
                   by simp [mclr_e0, hmclr1], ⟨hok_hd.1, hok_hd.2.1, hok_hd.2.2⟩, hm_e0⟩
              · rintro J_ch ⟨prev, tail, cnt, k, rem, scr_ch, mclr_ch⟩ m2
                  ⟨hrem_le, hcnt_le, htail_lt, hk_ok, hprev_ok, hmclr_ch, hscr_ch_inv, hm2⟩ ih_ch
                obtain ⟨hscr_ch, hpref_ch, hpht_ch⟩ := hscr_ch_inv
                dsimp only at hrem_le hcnt_le htail_lt hk_ok hprev_ok hmclr_ch hm2 ih_ch
                dsimp only at hscr_ch hpref_ch hpht_ch
                clear hm
                have htail_mv : tail.toNat < L.maxV := by omega
                refine wp_join0 (fun m3 => ∃ scr3, M6ExtScrInv c L nv s scr3 ∧
                    (FullMem c (M6ExtStOf s scr3 sstk1 mclr_ch) ⋆ R) m3) ?_ ?_
                · rintro J_ex m3 ⟨scr3, hscr3_inv, hm3⟩; c0_hsteps_nogrp
                  have hok_t := m6_pht_set_next_ok 0xFFFFFFFF#32 hscrLen hscr3_inv.1 htail_lt
                    hnv_le (Or.inl rfl) hscr3_inv.2.1 hscr3_inv.2.2
                  dsimp only at hok_t
                  let scr3' := scr3.set (k6PhtNext + tail.toNat) 0xFFFFFFFF#32
                  have hscr3'_inv : M6ExtScrInv c L nv s scr3' := ⟨hok_t.1, hok_t.2.1, hok_t.2.2⟩
                  have hm3' : (FullMem c (M6ExtStOf s scr3' sstk1 mclr_ch) ⋆ R) m := by
                    dsimp only [M6ExtStOf, scr3', k6PhtNext] at hm ⊢; exact hm
                  clear hm
                  refine wp_join0 (fun m4 => ∃ scr4, M6ExtScrInv c L nv s scr4 ∧
                      (FullMem c (M6ExtStOf s scr4 sstk1 mclr_ch) ⋆ R) m4) ?_ ?_
                  · rintro J_p m4 ⟨scr4, hscr4_inv, hm4⟩
                    refine wp_join_group (ts := [i32]) (fun ⟨res, _⟩ m5 =>
                        ∃ ncls2 sstk2, res = BitVec.ofNat 32 ncls2 ∧ ncls2 ≤ c.max_vars ∧
                          sstk2.length = c.max_vars ∧
                          (∀ ci < ncls2, (sstk2[ci]?.getD 0xFFFFFFFF#32).toNat < nv.toNat) ∧
                          (FullMem c (M6ExtStOf s scr4 sstk2 mclr_ch) ⋆ R) m5) ?_ ?_
                    · rintro J_ncls ⟨ncls_res, ⟨⟩⟩ m5 ⟨ncls2, sstk2, rfl, hnc2, hsstk2, hs_hd2, hm5⟩
                      c0_hsteps_nogrp
                      rw [m6_bv32_sub1_ofNat hlim_pos (by have := nv.isLt; omega)]
                      exact ih1 (lim - 1, ⟨ncls2, b, scr4, sstk2, mclr_ch⟩) m5 (by omega)
                        ⟨by omega, rfl, hb_le, hnc2, hsstk2, hmclr_ch, hs_hd2, hscr4_inv, hm5⟩
                    · intro J_ncls hJ_ncls; c0_hsteps_nogrp
                      · have hlt := ‹(BitVec.ofNat 32 ncls1).toNat < c.max_vars % 2 ^ 64›
                        rw [Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
                          Nat.mod_eq_of_lt (by omega)] at hlt
                        have hnc_bd64 :
                            (BitVec.setWidth 64 (BitVec.ofNat 32 ncls1)).toNat = ncls1 :=
                          m6_zext32_ofNat (by omega)
                        have hnc_lt : (BitVec.setWidth 64 (BitVec.ofNat 32 ncls1)).toNat <
                            sstk1.length := by rw [hnc_bd64, hsstk1]; exact hlt
                        c0_hsteps_nogrp
                        dsimp only [M6ExtStOf] at hm ⊢
                        refine hJ_ncls _ _
                          ⟨ncls1 + 1, _, m6_bv32_add1_ofNat (n := ncls1) (by omega),
                           by omega, by simp [hsstk1], ?_, hm⟩
                        intro ci hci; rw [hnc_bd64]; by_cases hcn : ci = ncls1
                        · subst hcn; rw [List.getElem?_set_self (by rw [hsstk1]; omega),
                            Option.getD_some]; erw [hhd_eq]; exact hhead_nv
                        · rw [List.getElem?_set_ne (by omega)]; exact hs_hd1 ci (by omega)
                      all_goals exact hJ_ncls _ m4 ⟨ncls1, sstk1, rfl, hnc1, hsstk1, hs_hd1, hm4⟩
                  · intro J_p hJ_p; c0_hsteps_nogrp
                    · have hp_lt : prev.toNat < nv.toNat := by bv_omega
                      have hok_p := m6_pht_set_next_ok 0xFFFFFFFF#32 hscrLen hscr3'_inv.1 hp_lt
                        hnv_le (Or.inl rfl) hscr3'_inv.2.1 hscr3'_inv.2.2
                      c0_hsteps_nogrp; dsimp only [M6ExtStOf, k6PhtNext] at hm ⊢
                      exact hJ_p _ ⟨_, ⟨hok_p.1, hok_p.2.1, hok_p.2.2⟩, hm⟩
                    · exact hJ_p _ ⟨scr3', hscr3'_inv, hm3'⟩
                · intro J_ex hJ_ex; c0_hsteps_nogrp
                  · have hrem_pos : 0 < rem := by bv_omega
                    have hk_lt_nv : k.toNat < nv.toNat := by bv_omega
                    have hk_mv : k.toNat < L.maxV := by omega
                    have hk_tail : k.toNat < tail.toNat := by
                      rcases hk_ok with rfl | h
                      · exact absurd hk_lt_nv (by bv_omega)
                      · exact h.2
                    have hwk_k : (BitVec.setWidth 64 k).toNat < s.scratch.work_stk1.length := by
                      rw [hlen.scratch_ok.work_stk1_len, m6_zext32]; omega
                    have hsig_k : (BitVec.setWidth 64
                        (s.scratch.work_stk1[(BitVec.setWidth 64 k).toNat]'hwk_k)).toNat <
                        s.scratch.sim_sig.length := by
                      have hget : s.scratch.work_stk1[(BitVec.setWidth 64 k).toNat]'hwk_k =
                          s.scratch.work_stk1[k.toNat]?.getD 0#32 := by
                        rw [m6_getElem_eq_getD _ hwk_k 0#32, m6_zext32]
                      rw [hget, m6_zext32, hlen.scratch_ok.sim_sig_len]
                      have := hstk k.toNat hk_lt_nv; have := hlen.core_ok.cur_vars_le; omega
                    c0_hsteps_nogrp
                    let nxt := scr_ch[k6PhtNext + k.toNat]'(m6_scr_nx_lt hscrLen hscr_ch hk_mv)
                    have hnxt_ok : nxt = 0xFFFFFFFF#32 ∨
                        (nxt.toNat < nv.toNat ∧ nxt.toNat < k.toNat) := by
                      have hn := hpht_ch.2 k.toNat hk_lt_nv
                      rw [← m6_getElem_eq_getD scr_ch (m6_scr_nx_lt hscrLen hscr_ch hk_mv)
                        0xFFFFFFFF#32] at hn
                      rcases hn with h | h
                      · exact Or.inl h
                      · exact Or.inr ⟨Nat.lt_trans h hk_lt_nv, h⟩
                    refine wp_join_group (ts := [i32, i32, i32]) (fun xs m3 =>
                        ∃ prev' tail' : BitVec 32, ∃ cnt' : Nat, ∃ scr3 mclr3 : List (BitVec 32),
                          xs = (prev', tail', BitVec.ofNat 32 cnt', ()) ∧ cnt' ≤ cnt + 1 ∧
                          tail'.toNat < nv.toNat ∧
                          (nxt = 0xFFFFFFFF#32 ∨ (nxt.toNat < nv.toNat ∧ nxt.toNat < tail'.toNat)) ∧
                          (prev' = 0xFFFFFFFF#32 ∨ (prev'.toNat < nv.toNat ∧
                            (nxt = 0xFFFFFFFF#32 ∨ nxt.toNat < prev'.toNat))) ∧
                          mclr3.length = c.max_vars ∧ M6ExtScrInv c L nv s scr3 ∧
                          (FullMem c (M6ExtStOf s scr3 sstk1 mclr3) ⋆ R) m3) ?_ ?_
                    · rintro J_nx ⟨prev', tail', cnt'', ⟨⟩⟩ m3
                        ⟨prev_, tail_, cnt', scr3, mclr3, hxs, hcnt', htail', hnxt_t, hprev',
                         hmclr3, hscr3_inv, hm3⟩
                      rcases hxs with ⟨rfl, rfl, rfl, _⟩
                      rw [m6_bv32_sub1_ofNat (n := rem) hrem_pos (by omega)]
                      exact ih_ch ⟨prev', tail', cnt', nxt, rem - 1, scr3, mclr3⟩ m3
                        (by dsimp only; omega)
                        ⟨by dsimp only; omega, by dsimp only; omega, htail', hnxt_t, hprev',
                         hmclr3, hscr3_inv, hm3⟩
                    · intro J_nx hJ_nx
                      have hmclr_k : (BitVec.setWidth 64 k).toNat < mclr_ch.length := by
                        rw [hmclr_ch, m6_zext32]; omega
                      refine wp_join0 (fun m3 => m3 = m2) ?_ ?_
                      · rintro J_m m3 hm3_eq; subst m3; c0_hsteps_nogrp
                        refine wp_join_group (ts := [i32]) (fun ⟨col, _⟩ m3 =>
                            m3 = m2 ∧ (col = 0#32 ∨ col = 1#32)) ?_ ?_
                        · rintro J_c ⟨col, ⟨⟩⟩ m3 ⟨rfl, _⟩; c0_hsteps_nogrp
                          have hok := m6_pht_set_next_ok k hscrLen hscr_ch htail_lt hnv_le
                            (Or.inr hk_tail) hpref_ch hpht_ch
                          have hpr_ok : prev = 0xFFFFFFFF#32 ∨ (prev.toNat < nv.toNat ∧
                              (nxt = 0xFFFFFFFF#32 ∨ nxt.toNat < prev.toNat)) := by
                            rcases hprev_ok with rfl | ⟨hp1, hp2⟩
                            · exact Or.inl rfl
                            · refine Or.inr ⟨hp1, ?_⟩
                              rcases hnxt_ok with h1 | ⟨_, h2⟩; exact Or.inl h1
                              refine Or.inr (lt_trans h2 ?_)
                              rcases hp2 with h3 | h3
                              · exact absurd hk_lt_nv (by subst h3; bv_omega)
                              · exact h3
                          dsimp only [M6ExtStOf, k6PhtNext] at hm ⊢; rw [m6_zext32] at hm
                          rw [m6_bv32_add1_ofNat (n := cnt) (by have := nv.isLt; omega)]
                          exact hJ_nx (prev, k, BitVec.ofNat 32 (cnt + 1), ()) _
                            ⟨prev, k, cnt + 1, _, _, rfl, by omega, hk_lt_nv,
                             hnxt_ok, hpr_ok, by simp [hmclr_ch], ⟨hok.1, hok.2.1, hok.2.2⟩, hm⟩
                        · intro J_c hJ_c; c0_hsteps_nogrp
                          · exact hJ_c _ m2 ⟨rfl, Or.inl rfl⟩
                          · exact hJ_c _ m2 ⟨rfl, Or.inr rfl⟩
                      · intro J_m hJ_m; c0_hsteps_nogrp
                        · exact hJ_m _ rfl
                        · exact hJ_m _ rfl
                        · refine wp_join0 (fun m3 => ∃ scr3, M6ExtScrInv c L nv s scr3 ∧
                              (FullMem c (M6ExtStOf s scr3 sstk1 mclr_ch) ⋆ R) m3) ?_ ?_
                          · rintro J_mm m3 ⟨scr3, hscr3_inv, hm3⟩; c0_hsteps_nogrp
                            have hnx_t : nxt = 0xFFFFFFFF#32 ∨
                                (nxt.toNat < nv.toNat ∧ nxt.toNat < tail.toNat) := by
                              rcases hnxt_ok with h1 | ⟨h1, h2⟩
                              · exact Or.inl h1
                              · exact Or.inr ⟨h1, lt_trans h2 hk_tail⟩
                            exact hJ_nx (k, tail, BitVec.ofNat 32 cnt, ()) m3
                              ⟨k, tail, cnt, scr3, mclr_ch, rfl, by omega, htail_lt, hnx_t,
                               Or.inr ⟨hk_lt_nv, hnxt_ok.imp_right And.right⟩, hmclr_ch,
                               hscr3_inv, hm3⟩
                          · intro J_mm hJ_mm
                            have hscr_b_ch :
                                (BitVec.setWidth 64 (256#32 + BitVec.ofNat 32 b)).toNat <
                                  scr_ch.length := by rw [hscr_ch, ← hscr1]; exact hscr_b
                            c0_hsteps_nogrp
                            · have hok := m6_pht_set_head_ok k hscrLen hscr_ch hb_lt
                                (Or.inr hk_lt_nv) hpref_ch hpht_ch
                              dsimp only [M6ExtStOf] at hm ⊢; erw [hb_idx_nat] at hm
                              exact hJ_mm _ ⟨_, ⟨hok.1, hok.2.1, hok.2.2⟩, hm⟩
                            · have hne : prev ≠ 0xFFFFFFFF#32 := by bv_omega
                              have hprev_nv : prev.toNat < nv.toNat := by
                                rcases hprev_ok with rfl | hp
                                · exact absurd rfl hne
                                · exact hp.1
                              have hk_prev : k.toNat < prev.toNat := by
                                rcases hprev_ok with rfl | hp
                                · exact absurd rfl hne
                                · rcases hp.2 with h1 | h1
                                  · exact absurd hk_lt_nv (by subst h1; bv_omega)
                                  · exact h1
                              c0_hsteps_nogrp
                              have hok := m6_pht_set_next_ok k hscrLen hscr_ch hprev_nv hnv_le
                                (Or.inr hk_prev) hpref_ch hpht_ch
                              dsimp only [M6ExtStOf, k6PhtNext] at hm ⊢
                              exact hJ_mm _ ⟨_, ⟨hok.1, hok.2.1, hok.2.2⟩, hm⟩
                  all_goals exact hJ_ex m2 ⟨scr_ch, ⟨hscr_ch, hpref_ch, hpht_ch⟩, hm2⟩
            all_goals
              exact hJ_b _ ⟨scr1, sstk1, mclr1, hsstk1, hmclr1, hs_hd1,
                ⟨hscr1, hpref1, hpht1⟩, hm1⟩
          all_goals exact hJ_b _ ⟨scr1, sstk1, mclr1, hsstk1, hmclr1, hs_hd1,
              ⟨hscr1, hpref1, hpht1⟩, hm1⟩
    · have hb_eq : b = 1024 := by bv_omega
      subst hb_eq; c0_hsteps_nogrp
      have hc_mv : (BitVec.ofNat 32 ncls).toNat = ncls := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      dsimp only [M6ExtStOf] at hm'
      exact hQ (BitVec.ofNat 32 ncls) scr sstk mclr m' hscr_len hsstk_len hmclr_len
        hpref (by rw [hc_mv]; exact hnc_mv)
        ⟨by rw [hc_mv, hsstk_len]; exact hnc_mv, hpht_lp.2,
          fun ci hci => hs_hd ci (by rw [hc_mv] at hci; exact hci)⟩ hm'

end LeanQbe.T.Examples.Kissat.Proof.Sweep

end
