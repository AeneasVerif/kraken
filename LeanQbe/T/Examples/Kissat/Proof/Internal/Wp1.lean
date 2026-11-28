/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Internal.Spec
import LeanQbe.T.Examples.Kissat.Proof.Internal.Wp0
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Internal Arena Split & Table Zeroing WP Proofs (`Proof.Internal.Wp1`)

Parametric `(Γ : Env)` `Func.wp` proofs (`0` legacy `Full*` imports, `0` `@[expose]` theorems):
1. `full_init_arenas_wp` (against `fullInitArenasSpec`, calling `full_init_ptrs`)
2. `full_zero_tables1_wp` (against `fullZeroTables1Spec`)
3. `full_zero_tables2_wp` (against `fullZeroTables2Spec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Internal

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Internal

local elab "in_steps" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := true, splitJnz := false } 10000

local elab "in_steps_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 10000

/-! ## 1. Arithmetic & List Helpers -/

@[expose] def fullInitAp (avail_dyn : Nat) : Nat :=
  min ((avail_dyn / 8 * 3) / 5) 134217727

@[expose] def fullInitRp (avail_dyn : Nat) : Nat :=
  (fullInitAp avail_dyn + 5) / 6

@[expose] def fullInitWp (avail_dyn : Nat) : Nat :=
  min (avail_dyn / 8 - fullInitAp avail_dyn - fullInitRp avail_dyn) 134217727

theorem fullInitAp_add_rp_le (avail_dyn : Nat) :
    fullInitAp avail_dyn + fullInitRp avail_dyn ≤ avail_dyn / 8 := by
  have h1 : fullInitAp avail_dyn ≤ (avail_dyn / 8 * 3) / 5 := Nat.min_le_left _ _
  unfold fullInitRp; omega

theorem fullInitAp_lt {avail_dyn : Nat} : 2 * fullInitAp avail_dyn < 2 * dimacsBound := by
  unfold fullInitAp dimacsBound; omega

theorem fullInitWp_lt {avail_dyn : Nat} : 2 * fullInitWp avail_dyn < 2 * dimacsBound := by
  unfold fullInitWp dimacsBound; omega

theorem fullInitRp_lt {avail_dyn : Nat} : 2 * fullInitRp avail_dyn < 2 * dimacsBound := by
  unfold fullInitRp fullInitAp dimacsBound; omega

private theorem bv64_ushr3_eq (x : BitVec 64) :
    x >>> (3 : Nat) = BitVec.ofNat 64 (x.toNat / 8) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by omega : x.toNat / 8 < 2 ^ 64)]

private theorem bv64_mul_nat' (x : BitVec 64) (k : Nat) :
    x * BitVec.ofNat 64 k = BitVec.ofNat 64 (x.toNat * k) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_mod]

private theorem bv64_shl1_eq (n : Nat) :
    BitVec.ofNat 64 n <<< (1 : Nat) = BitVec.ofNat 64 (2 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_mod, Nat.mul_comm]

private theorem bv64_shl2_eq (n : Nat) :
    BitVec.ofNat 64 n <<< (2 : Nat) = BitVec.ofNat 64 (4 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_mod, Nat.mul_comm]

private theorem bv64_shl3_eq (n : Nat) :
    BitVec.ofNat 64 n <<< (3 : Nat) = BitVec.ofNat 64 (8 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat, Nat.mul_mod, Nat.mul_comm]

private theorem bv64_add_ofNat (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

private theorem bv64_sub_ofNat {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  have hb' : b < 2 ^ 64 := Nat.lt_of_le_of_lt hb ha
  rw [BitVec.toNat_sub_of_le
      (by simp [BitVec.le_def, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb', hb]),
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb', Nat.mod_eq_of_lt (by omega)]

private theorem bv64_add1_toNat {v : BitVec 64} {n : Nat} (hv : v.toNat < n) (hn : n < 2 ^ 64) :
    (v + 1#64).toNat = v.toNat + 1 := by
  simp only [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl]; omega

private theorem list_eq_replicate_of_forall {α : Type} {xs : List α} {n : Nat} {x : α}
    (hlen : xs.length = n) (h : ∀ j < n, xs[j]? = some x) : xs = List.replicate n x := by
  refine List.ext_getElem (by simp [hlen]) fun j hj1 hj2 => ?_
  have hg := h j (by simpa using hj2)
  rw [List.getElem?_eq_getElem hj1, Option.some.injEq] at hg
  simpa using hg

private theorem wvec_eq_replicate_of_pairs {xs : List (BitVec 32)} {n : Nat}
    (hlen : xs.length = 2 * n)
    (h : ∀ j < n, xs[2 * j]? = some 0#32 ∧ xs[2 * j + 1]? = some 0#32) :
    xs = List.replicate (2 * n) 0#32 := by
  refine list_eq_replicate_of_forall hlen fun i hi => ?_
  have hq := h (i / 2) (by omega)
  have hdm := Nat.div_add_mod i 2
  rcases Nat.mod_two_eq_zero_or_one i with hm0 | hm1
  · rw [hm0, Nat.add_zero] at hdm; simpa [hdm] using hq.1
  · rw [hm1] at hdm; simpa [hdm] using hq.2

private theorem last_learned_getD_eq {xs : List (BitVec 32)}
    (h : ∀ j < 16, xs[j]? = some 0xFFFFFFFF#32) :
    ∀ k < 16, xs.getD k 0 = 0xFFFFFFFF#32 := fun k hk => by
  rw [List.getD_eq_getElem?_getD, h k hk]; rfl

/-! ## 2. `full_init_arenas_wp` -/

private def ptrsDummyCfg {hdr_addr : BitVec 64} {max_v : Nat}
    (hmx : max_v < 2 * dimacsBound) (hfit : hdr_addr.toNat + fullFixedBytes max_v < 2 ^ 64) :
    FullCfg :=
  { hdr := hdr_addr, avail := fullFixedBytes max_v, mv := 0, max_vars := max_v, bva_cap := max_v
    nc := 0, arena_cap := 0, wcap := 0, delayed_cap := 0, red_cap := 0, extend_cap := 0
    scratch_cap := 0, hbva := by omega, hmv := by unfold dimacsBound; omega, hmaxv := hmx
    hnc := by unfold dimacsBound; omega, harena := by unfold dimacsBound; omega
    hwcap := by unfold dimacsBound; omega, hdel := by unfold dimacsBound; omega
    hred := by unfold dimacsBound; omega, hext := by unfold dimacsBound; omega
    hscr := by unfold dimacsBound; omega, havail_fit := hfit, hsize := Nat.le_refl _ }

private theorem aw0_pres (w0 : List (BitVec 64)) (v11 v12 v0 v1 : BitVec 64)
    {i : Nat} (h : i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 11 ∧ i ≠ 12) :
    ((((w0.set 11 v11).set 12 v12).set 0 v0).set 1 v1)[i]? = w0[i]? := by
  simp only [List.getElem?_set_ne (Ne.symm h.2.1), List.getElem?_set_ne (Ne.symm h.1),
    List.getElem?_set_ne (Ne.symm h.2.2.2), List.getElem?_set_ne (Ne.symm h.2.2.1)]

private theorem aw1_pres (w1 : List (BitVec 64)) (v14 v16 : BitVec 64)
    {i : Nat} (h : i ≠ 14 ∧ i ≠ 16) :
    ((w1.set 14 v14).set 16 v16)[i]? = w1[i]? := by
  simp only [List.getElem?_set_ne (Ne.symm h.2), List.getElem?_set_ne (Ne.symm h.1)]

private theorem aw3_pres (w3 : List (BitVec 64)) (v3 v6 : BitVec 64)
    {i : Nat} (h : i ≠ 3 ∧ i ≠ 6) :
    ((w3.set 3 v3).set 6 v6)[i]? = w3[i]? := by
  simp only [List.getElem?_set_ne (Ne.symm h.2), List.getElem?_set_ne (Ne.symm h.1)]

section InitArenas
open scoped InHdrTactics

theorem full_init_arenas_wp (Γ : Env) (hPtrs : Γ.Has "full_init_ptrs" fullInitPtrsSpec) :
    ∀ a m Q X, fullInitArenasSpec a m Q X → Func.wp Γ full_init_arenas_body a m Q X := by
  rintro ⟨h, hdr_addr, max_v, adyn, ⟨⟩⟩ m Q X
    ⟨ws, dcap, ecap, scap, R, rfl, hw, hmx, hdel, hext, hscr, h52, h109, h112, hfit, hm, hQ⟩
  have hmx' := hmx; have hdel' := hdel; have hext' := hext; have hscr' := hscr
  unfold dimacsBound at hmx' hdel' hext' hscr'
  have hadyn := adyn.isLt
  have htp_lt : adyn.toNat / 8 < 2 ^ 61 := by omega
  have hap3_lt : ((adyn.toNat / 8) * 3) < 2 ^ 64 := by omega
  let ap := fullInitAp adyn.toNat
  let rp := fullInitRp adyn.toNat
  let wp_c := fullInitWp adyn.toNat
  have hap_lt : ap ≤ 134217727 := by dsimp [ap]; unfold fullInitAp; omega
  have hrp_lt : rp ≤ 22369622 := by dsimp [rp]; unfold fullInitRp; omega
  have hwp_lt : wp_c ≤ 134217727 := by dsimp [wp_c]; unfold fullInitWp; omega
  have hap_rp := fullInitAp_add_rp_le adyn.toNat
  let w0 := ws.take 35; let w1 := (ws.drop 35).take 35
  let w2 := (ws.drop 70).take 35; let w3 := (ws.drop 105).take 35
  have h0l : w0.length = 35 := by simp [w0, hw]
  have h1l : w1.length = 35 := by simp [w1, hw]
  have h2l : w2.length = 35 := by simp [w2, hw]
  have h3l : w3.length = 35 := by simp [w3, hw]
  have hm4 : (hdrTail4 h w0 w1 w2 w3 ⋆ R) m := array64_to_hdrTail4 hw hm
  have hdel_at : w1[17]?.getD 0#64 = BitVec.ofNat 64 dcap := by
    dsimp only [w1]; rw [drop_take_getElem? ws 35 35 17 (by decide), h52]; rfl
  have hext_at : w3[4]?.getD 0#64 = BitVec.ofNat 64 ecap := by
    dsimp only [w3]; rw [drop_take_getElem? ws 105 35 4 (by decide), h109]; rfl
  unfold Func.wp full_init_arenas_body
  in_steps_nogrp
  clear hm4
  rw [hdel_at, hext_at, bv64_ushr3_eq adyn]
  have hap3 : BitVec.ofNat 64 (adyn.toNat / 8) * (3 : BitVec 64) =
      BitVec.ofNat 64 ((adyn.toNat / 8) * 3) := by
    rw [show (3 : BitVec 64) = BitVec.ofNat 64 3 from rfl, bv64_mul_nat',
      bv64_ofNat_toNat (by omega)]
  have hap_div : BitVec.ofNat 64 ((adyn.toNat / 8) * 3) / (5 : BitVec 64) =
      BitVec.ofNat 64 (((adyn.toNat / 8) * 3) / 5) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_udiv, Nat.mod_eq_of_lt hap3_lt,
      Nat.mod_eq_of_lt (show ((adyn.toNat / 8) * 3) / 5 < 2 ^ 64 by omega)]
  rw [hap3, hap_div]
  refine wp_join_group
    (fun (ap_v, ()) ma => ap_v = BitVec.ofNat 64 ap ∧ ma = m) ?_ ?_
  · rintro _ ⟨ap_v, ⟨⟩⟩ ma ⟨rfl, hma⟩
    rw [hma]; clear hma ma
    in_steps_nogrp
    have hap5 : BitVec.ofNat 64 ap + (5 : BitVec 64) = BitVec.ofNat 64 (ap + 5) := by
      rw [show (5 : BitVec 64) = BitVec.ofNat 64 5 from rfl, bv64_add_ofNat]
    have hrp_div : BitVec.ofNat 64 (ap + 5) / (6 : BitVec 64) = BitVec.ofNat 64 rp := by
      apply BitVec.eq_of_toNat_eq
      simp [rp, fullInitRp, ap, BitVec.toNat_udiv,
        Nat.mod_eq_of_lt (show ap + 5 < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show (ap + 5) / 6 < 2 ^ 64 by omega)]
    have hsub_wp : BitVec.ofNat 64 (adyn.toNat / 8) -
        BitVec.ofNat 64 ap - BitVec.ofNat 64 rp =
        BitVec.ofNat 64 (adyn.toNat / 8 - ap - rp) := by
      rw [bv64_sub_ofNat (by omega) (by omega), bv64_sub_ofNat (by omega) (by omega)]
    rw [hap5, hrp_div, hsub_wp]
    refine wp_join_group
      (fun (wp_v, ()) mw => wp_v = BitVec.ofNat 64 wp_c ∧ mw = m) ?_ ?_
    · rintro _ ⟨wp_v, ⟨⟩⟩ mw ⟨rfl, hmw⟩
      rw [hmw]; clear hmw mw
      in_steps_nogrp
      refine LeanQbe.T.wp_call_of_spec _ _ (hPtrs _ _ _ _ ?_)
      dsimp only [vals, Arg.val]
      refine ⟨ws, R, rfl, hw, hmx, by omega, hm, fun ws' m0 hw' hptrs hpres hm0 => ?_⟩
      let c0 := ptrsDummyCfg (hdr_addr := h) hmx (by omega)
      have h0c := hptrs c0 rfl rfl
      have har_ws' : ws'[10]? = some c0.pArena := h0c.2.2.2.2.2.2.1
      let w0' := ws'.take 35; let w1' := (ws'.drop 35).take 35
      let w2' := (ws'.drop 70).take 35; let w3' := (ws'.drop 105).take 35
      have hm0' := array64_to_hdrTail4 hw' hm0
      change (hdrTail4 h w0' w1' w2' w3' ⋆ R) m0 at hm0'
      clear hm hm0
      have h0l' : w0'.length = 35 := by simp [w0', hw']
      have h1l' : w1'.length = 35 := by simp [w1', hw']
      have h2l' : w2'.length = 35 := by simp [w2', hw']
      have h3l' : w3'.length = 35 := by simp [w3', hw']
      have har_get : w0'[10]?.getD 0#64 = c0.pArena := by
        dsimp only [w0']; rw [List.getElem?_take_of_lt (by decide), har_ws']; rfl
      in_steps
      have hdel_mul : BitVec.ofNat 64 dcap * (12 : BitVec 64) =
          BitVec.ofNat 64 (12 * dcap) := by
        rw [show (12 : BitVec 64) = BitVec.ofNat 64 12 from rfl, bv64_mul_nat',
          bv64_ofNat_toNat (by omega), Nat.mul_comm]
      have hshl3_a : BitVec.ofNat 64 ap <<< (3 : Nat) = BitVec.ofNat 64 (8 * ap) :=
        bv64_shl3_eq ap
      have hshl3_w : BitVec.ofNat 64 wp_c <<< (3 : Nat) = BitVec.ofNat 64 (8 * wp_c) :=
        bv64_shl3_eq wp_c
      have hshl3_r : BitVec.ofNat 64 rp <<< (3 : Nat) = BitVec.ofNat 64 (8 * rp) :=
        bv64_shl3_eq rp
      have hshl2_e : BitVec.ofNat 64 ecap <<< (2 : Nat) = BitVec.ofNat 64 (4 * ecap) :=
        bv64_shl2_eq ecap
      have hshl1_a : BitVec.ofNat 64 ap <<< (1 : Nat) = BitVec.ofNat 64 (2 * ap) :=
        bv64_shl1_eq ap
      have hshl1_w : BitVec.ofNat 64 wp_c <<< (1 : Nat) = BitVec.ofNat 64 (2 * wp_c) :=
        bv64_shl1_eq wp_c
      have hshl1_r : BitVec.ofNat 64 rp <<< (1 : Nat) = BitVec.ofNat 64 (2 * rp) :=
        bv64_shl1_eq rp
      rw [har_get, hdel_mul, hshl3_a, hshl3_w, hshl3_r, hshl2_e,
        hshl1_a, hshl1_w, hshl1_r] at hm
      have h52' : ws'[52]? = some (BitVec.ofNat 64 dcap) := (hpres 52 (by decide)).trans h52
      have h109' : ws'[109]? = some (BitVec.ofNat 64 ecap) := (hpres 109 (by decide)).trans h109
      have h112' : ws'[112]? = some (BitVec.ofNat 64 scap) := (hpres 112 (by decide)).trans h112
      let pWstk_v := c0.pArena + BitVec.ofNat 64 (8 * ap)
      let pDel_v := pWstk_v + BitVec.ofNat 64 (8 * wp_c)
      let pRed_v := pDel_v + BitVec.ofNat 64 (12 * dcap)
      let pExt_v := pRed_v + BitVec.ofNat 64 (8 * rp)
      let pScr_v := pExt_v + BitVec.ofNat 64 (4 * ecap)
      let aw0 := (((w0'.set 11 pWstk_v).set 12 pDel_v).set 0 (BitVec.ofNat 64 (2 * ap))).set 1
        (BitVec.ofNat 64 (2 * wp_c))
      let aw1 := (w1'.set 14 pRed_v).set 16 (BitVec.ofNat 64 (2 * rp))
      let aw3 := (w3'.set 3 pExt_v).set 6 pScr_v
      have haw0_len : aw0.length = 35 := by simp [aw0, h0l']
      have haw1_len : aw1.length = 35 := by simp [aw1, h1l']
      have haw3_len : aw3.length = 35 := by simp [aw3, h3l']
      let ws'' := aw0 ++ aw1 ++ w2' ++ aw3
      have hws''_len : ws''.length = 140 := by simp [ws'', haw0_len, haw1_len, h2l', haw3_len]
      have hm_arr : (array64 (h + 32) ws'' ⋆ R) m := by
        rwa [← hdrTail4_eq_array64 haw0_len haw1_len h2l']
      have hbd_a : 2 * ap < 2 * dimacsBound := fullInitAp_lt
      have hbd_w : 2 * wp_c < 2 * dimacsBound := fullInitWp_lt
      have hbd_r : 2 * rp < 2 * dimacsBound := fullInitRp_lt
      have hsum : 4 * (2 * ap) + 4 * (2 * wp_c) + 4 * (2 * rp) ≤ adyn.toNat := by
        dsimp [ap, rp, wp_c]; unfold fullInitWp; omega
      have hwpos : 40 ≤ adyn.toNat → 1 ≤ 2 * wp_c := fun h40 => by
        dsimp [wp_c]; unfold fullInitWp fullInitRp fullInitAp; omega
      refine hQ (2 * ap) (2 * wp_c) (2 * rp) ws'' m hws''_len hbd_a hbd_w hbd_r hsum hwpos
        (fun c hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 => ?_) hm_arr
      have hcpt := hptrs c hc1 hc2
      have ga0 := fun i (hi : i < 35) =>
        append4_getElem?_0 (w1 := aw1) (w2 := w2') (w3 := aw3) haw0_len hi
      have ga1 := fun i (hi0 : 35 ≤ i) (hi1 : i < 70) =>
        append4_getElem?_1 (w2 := w2') (w3 := aw3) haw0_len haw1_len hi0 hi1
      have ga2 := fun i (hi0 : 70 ≤ i) (hi1 : i < 105) =>
        append4_getElem?_2 (w3 := aw3) haw0_len haw1_len h2l' hi0 hi1
      have ga3 := fun i (hi0 : 105 ≤ i) =>
        append4_getElem?_3 (w3 := aw3) haw0_len haw1_len h2l' hi0
      have pr0 : ∀ i, i < 35 → i ≠ 0 → i ≠ 1 → i ≠ 11 → i ≠ 12 → ws''[i]? = ws'[i]? :=
        fun i hi h0n h1n h11n h12n => by
          rw [ga0 i hi, aw0_pres w0' _ _ _ _ ⟨h0n, h1n, h11n, h12n⟩]
          dsimp only [w0']; rw [List.getElem?_take_of_lt hi]
      have pr1 : ∀ i, 35 ≤ i → i < 70 → i ≠ 49 → i ≠ 51 → ws''[i]? = ws'[i]? :=
        fun i hi0 hi1 _ _ => by
          rw [ga1 i hi0 hi1, aw1_pres w1' _ _ ⟨by omega, by omega⟩,
            drop_take_getElem? ws' 35 35 (i - 35) (by omega), show 35 + (i - 35) = i by omega]
      have pr2 : ∀ i, 70 ≤ i → i < 105 → ws''[i]? = ws'[i]? := fun i hi0 hi1 => by
        rw [ga2 i hi0 hi1, drop_take_getElem? ws' 70 35 (i - 70) (by omega),
          show 70 + (i - 70) = i by omega]
      have pr3 : ∀ i, 105 ≤ i → i < 140 → i ≠ 108 → i ≠ 111 → ws''[i]? = ws'[i]? :=
        fun i hi0 hi1 _ _ => by
          rw [ga3 i hi0, aw3_pres w3' _ _ ⟨by omega, by omega⟩,
            drop_take_getElem? ws' 105 35 (i - 105) (by omega), show 105 + (i - 105) = i by omega]
      have hp_a : c.pArena = c0.pArena :=
        Option.some.inj (hcpt.2.2.2.2.2.2.1.symm.trans har_ws')
      have hp_w : c.pWstk = pWstk_v := by
        unfold FullCfg.pWstk; rw [hp_a, hc3, show 4 * (2 * ap) = 8 * ap by omega]
      have hp_d : c.pDelayed = pDel_v := by
        unfold FullCfg.pDelayed; rw [hp_w, hc4, show 4 * (2 * wp_c) = 8 * wp_c by omega]
      have hp_r : c.pRedRefs = pRed_v := by
        unfold FullCfg.pRedRefs; rw [hp_d, hc5]
      have hp_e : c.pExtendStk = pExt_v := by
        unfold FullCfg.pExtendStk; rw [hp_r, hc6, show 4 * (2 * rp) = 8 * rp by omega]
      have hp_s : c.pScratchBuf = pScr_v := by
        unfold FullCfg.pScratchBuf; rw [hp_e, hc7]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [ga0 0 (by decide)]; dsimp [aw0]
        rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by simp [h0l']), hc3]
      · rw [ga0 1 (by decide)]; dsimp [aw0]
        rw [List.getElem?_set_self (by simp [h0l']), hc4]
      · rw [pr0 4 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hcpt.1
      · rw [pr0 5 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hcpt.2.1
      · rw [pr0 6 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hcpt.2.2.1
      · rw [pr0 7 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hcpt.2.2.2.1
      · rw [pr0 8 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hcpt.2.2.2.2.1
      · rw [pr0 9 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.1
      · rw [pr0 10 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.1
      · rw [ga0 11 (by decide)]; dsimp [aw0]
        rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
          List.getElem?_set_ne (by decide), List.getElem?_set_self (by simp [h0l']), hp_w]
      · rw [ga0 12 (by decide)]; dsimp [aw0]
        rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
          List.getElem?_set_self (by simp [h0l']), hp_d]
      · rw [pr0 13 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.1
      · rw [pr0 21 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.1
      · rw [pr0 22 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.1
      · rw [pr0 23 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.1
      · rw [pr0 24 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.2.1
      · rw [pr0 25 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.1
      · rw [pr0 26 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · rw [pr0 29 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · rw [pr1 41 (by decide) (by decide) (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · rw [pr1 42 (by decide) (by decide) (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · rw [pr1 43 (by decide) (by decide) (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · rw [pr1 44 (by decide) (by decide) (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · rw [pr1 45 (by decide) (by decide) (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · rw [pr1 46 (by decide) (by decide) (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · rw [pr1 47 (by decide) (by decide) (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · rw [pr1 48 (by decide) (by decide) (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · rw [ga1 49 (by decide) (by decide)]; dsimp [aw1]
        rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by simp [h1l']), hp_r]
      · rw [pr1 50 (by decide) (by decide) (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · rw [ga1 51 (by decide) (by decide)]; dsimp [aw1]
        rw [List.getElem?_set_self (by simp [h1l']), hc6]
      · rw [pr1 52 (by decide) (by decide) (by decide) (by decide), h52', hc5]
      · rw [pr2 96 (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · rw [pr2 97 (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · rw [pr2 98 (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · rw [pr2 99 (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · rw [pr2 100 (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · rw [pr2 101 (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · rw [pr2 102 (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · rw [pr2 103 (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · rw [pr2 104 (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · rw [pr3 105 (by decide) (by decide) (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · rw [pr3 106 (by decide) (by decide) (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · rw [pr3 107 (by decide) (by decide) (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · rw [ga3 108 (by decide)]; dsimp [aw3]
        rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by simp [h3l']), hp_e]
      · rw [pr3 109 (by decide) (by decide) (by decide) (by decide), h109', hc7]
      · rw [ga3 111 (by decide)]; dsimp [aw3]
        rw [List.getElem?_set_self (by simp [h3l']), hp_s]
      · rw [pr3 112 (by decide) (by decide) (by decide) (by decide), h112', hc8]
      · rw [pr3 113 (by decide) (by decide) (by decide) (by decide)]
        exact hcpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    · intro Jw hJw; in_steps_nogrp; c0_hsplit
      · in_steps
        have hgt : 134217727 < adyn.toNat / 8 - ap - rp := by
          rw [Nat.mod_eq_of_lt (by omega : adyn.toNat / 8 - ap - rp < 2 ^ 64)] at hc
          exact hc
        refine hJw _ _ ⟨?_, rfl⟩
        dsimp [wp_c]; unfold fullInitWp; rw [Nat.min_eq_right (by omega)] <;> rfl
      · in_steps
        have hle : adyn.toNat / 8 - ap - rp ≤ 134217727 := by
          rw [show (134217727 : BitVec 64).toNat = 134217727 from rfl,
            Nat.mod_eq_of_lt (by omega : adyn.toNat / 8 - ap - rp < 2 ^ 64)] at hc
          omega
        refine hJw _ _ ⟨?_, rfl⟩
        dsimp [wp_c]; unfold fullInitWp; rw [Nat.min_eq_left hle]
  · intro Ja hJa; in_steps_nogrp; c0_hsplit
    · in_steps
      have hgt : 134217727 < (adyn.toNat / 8 * 3) / 5 := by
        rw [Nat.mod_eq_of_lt (by omega : (adyn.toNat / 8 * 3) / 5 < 2 ^ 64)] at hc
        exact hc
      refine hJa _ _ ⟨?_, rfl⟩
      dsimp [ap]; unfold fullInitAp; rw [Nat.min_eq_right (by omega)] <;> rfl
    · in_steps
      have hle : (adyn.toNat / 8 * 3) / 5 ≤ 134217727 := by
        rw [show (134217727 : BitVec 64).toNat = 134217727 from rfl,
          Nat.mod_eq_of_lt (by omega : (adyn.toNat / 8 * 3) / 5 < 2 ^ 64)] at hc
        omega
      refine hJa _ _ ⟨?_, rfl⟩
      dsimp [ap]; unfold fullInitAp; rw [Nat.min_eq_left hle]

end InitArenas

/-! ## 3. `full_zero_tables1_wp` and `full_zero_tables2_wp` -/

section ZeroTables
open scoped FullArenaTactics

theorem full_zero_tables1_wp (Γ : Env) :
    ∀ a m Q X, fullZeroTables1Spec a m Q X → Func.wp Γ full_zero_tables1_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hcl := hlen.core_ok; have hs := hlen.scratch_ok
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hmd : c.minDepth ≤ 1000 := fullMinDepthOf_le c.max_vars
  unfold dimacsBound at hmx
  unfold Func.wp full_zero_tables1_body
  in_steps_nogrp
  refine wp_loop_inv
    (fun (i_v, ()) ml => ∃ st : FullState, i_v.toNat ≤ 2 * c.max_vars ∧
      st = { s with
        core := { s.core with
          vals := st.core.vals, lit_mark := st.core.lit_mark,
          wvec := st.core.wvec, repr := st.core.repr },
        scratch := { s.scratch with
          walk_vals := st.scratch.walk_vals, tarjan_mark := st.scratch.tarjan_mark,
          tarjan_reach := st.scratch.tarjan_reach } } ∧
      st.core.vals.length = 2 * c.max_vars ∧ st.core.lit_mark.length = 2 * c.max_vars ∧
      st.core.wvec.length = 4 * c.max_vars ∧ st.core.repr.length = 2 * c.max_vars ∧
      st.scratch.walk_vals.length = 2 * c.max_vars ∧
      st.scratch.tarjan_mark.length = 2 * c.max_vars ∧
      st.scratch.tarjan_reach.length = 2 * c.max_vars ∧
      (∀ j < i_v.toNat, st.core.vals[j]? = some 0#8 ∧ st.core.lit_mark[j]? = some 0#8 ∧
        st.core.wvec[2 * j]? = some 0#32 ∧ st.core.wvec[2 * j + 1]? = some 0#32) ∧
      (FullMem c st ⋆ R) ml)
    (fun (i_v, ()) _ => 2 * c.max_vars - i_v.toNat) ?_ ?_
  · intro L1 hL1; in_steps
    exact hL1 (0#64, ()) m ⟨s, Nat.zero_le _, rfl, hcl.vals_len, hcl.lit_mark_len, hcl.wvec_len,
      hcl.repr_len, hs.walk_vals_len, hs.tarjan_mark_len, hs.tarjan_reach_len,
      (fun _ h0 => by cases h0), hm⟩
  · intro L1 ⟨i_v, ⟨⟩⟩ ml ⟨st, hle, hag, hvl, hlm, hwv, hrp, hwv_s, htm, htr, hall, hm1⟩ hL1
    in_steps_nogrp
    c0_hsplit
    · rw [Nat.mod_eq_of_lt (by omega : c.max_vars < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 2 * c.max_vars < 2 ^ 64)] at hc
      have hilt' : i_v.toNat < 2 * c.max_vars := hc
      have hi1 : (i_v + 1#64).toNat = i_v.toNat + 1 := bv64_add1_toNat hilt' (by omega)
      have hshl : (i_v <<< (1 : Nat)).toNat = 2 * i_v.toNat := by
        simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
        rw [Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]
      have hshl1 : (i_v <<< (1 : Nat) + (1 : BitVec 64)).toNat = 2 * i_v.toNat + 1 := by
        simp only [BitVec.toNat_add, hshl, show (1 : BitVec 64).toNat = 1 from rfl]; omega
      in_steps
      refine hL1 (i_v + 1#64, ()) m (by dsimp only; rw [hi1]; omega)
        ⟨_, by rw [hi1]; omega, congrArg (fun x =>
          { x with
            core := { x.core with
              vals := st.core.vals.set i_v.toNat 0#8,
              lit_mark := st.core.lit_mark.set i_v.toNat 0#8,
              wvec := (st.core.wvec.set (2 * i_v.toNat) 0#32).set (2 * i_v.toNat + 1) 0#32,
              repr := st.core.repr.set i_v.toNat (i_v.setWidth 32) },
            scratch := { x.scratch with
              walk_vals := st.scratch.walk_vals.set i_v.toNat 0#8,
              tarjan_mark := st.scratch.tarjan_mark.set i_v.toNat 0#32,
              tarjan_reach := st.scratch.tarjan_reach.set i_v.toNat 0#32 } }) hag,
          by simp [hvl], by simp [hlm], by simp [hwv], by simp [hrp], by simp [hwv_s],
          by simp [htm], by simp [htr], fun j hj => ?_, ?_⟩
      · rw [hi1] at hj
        by_cases hje : j = i_v.toNat
        · subst hje
          exact ⟨List.getElem?_set_self (by omega), List.getElem?_set_self (by omega),
            by rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)],
            List.getElem?_set_self (by rw [List.length_set, hwv]; omega)⟩
        · obtain ⟨ha1, ha2, ha3, ha4⟩ := hall j (by omega)
          rw [List.getElem?_set_ne (Ne.symm hje), List.getElem?_set_ne (Ne.symm hje),
            List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
          exact ⟨ha1, ha2, ha3, ha4⟩
      · rw [hshl, hshl1] at hm; exact hm
    · rw [Nat.mod_eq_of_lt (by omega : c.max_vars < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 2 * c.max_vars < 2 ^ 64)] at hc
      have hieq : i_v.toNat = 2 * c.max_vars := by omega
      rw [hieq] at hall
      let s1 : FullState :=
        { s with
          core := { s.core with
            vals := List.replicate (2 * c.max_vars) 0#8,
            lit_mark := List.replicate (2 * c.max_vars) 0#8,
            wvec := List.replicate (4 * c.max_vars) 0#32,
            repr := st.core.repr },
          scratch := { s.scratch with
            walk_vals := st.scratch.walk_vals, tarjan_mark := st.scratch.tarjan_mark,
            tarjan_reach := st.scratch.tarjan_reach } }
      have hwv_eq : st.core.wvec = List.replicate (4 * c.max_vars) 0#32 := by
        simpa [show 2 * (2 * c.max_vars) = 4 * c.max_vars by omega] using
          wvec_eq_replicate_of_pairs (n := 2 * c.max_vars) (by omega)
            (fun j hj => (hall j hj).2.2)
      have hs1_eq : st = s1 := by
        rw [hag, list_eq_replicate_of_forall hvl (fun j hj => (hall j hj).1),
          list_eq_replicate_of_forall hlm (fun j hj => (hall j hj).2.1), hwv_eq]
      rw [hs1_eq] at hm1
      in_steps_nogrp
      refine wp_join_group
        (fun _ mw => ∃ wstk' : List (BitVec 32), wstk'.length = c.wcap ∧
          (FullMem c { s1 with core := { s1.core with wstk := wstk' } } ⋆ R) mw) ?_ ?_
      · rintro _ ⟨⟩ mw ⟨wstk', hwstk', hmw⟩
        let s2 : FullState := { s1 with core := { s1.core with wstk := wstk' } }
        in_steps_nogrp
        refine wp_loop_inv
          (fun (k_v, ()) ml2 => ∃ mstk' : List (BitVec 32),
            k_v.toNat ≤ 2 * c.minDepth ∧ mstk'.length = 2 * c.minDepth ∧
            (FullMem c { s2 with core := { s2.core with min_stk := mstk' } } ⋆ R) ml2)
          (fun (k_v, ()) _ => 2 * c.minDepth - k_v.toNat) ?_ ?_
        · intro L2 hL2; in_steps
          exact hL2 (0#64, ()) mw ⟨s2.core.min_stk, Nat.zero_le _, hcl.min_stk_len, hmw⟩
        · intro L2 ⟨k_v, ⟨⟩⟩ ml2 ⟨mstk', hk_le, hmstl, hm2⟩ hL2
          in_steps_nogrp
          c0_hsplit
          · rw [Nat.mod_eq_of_lt (by omega : c.minDepth < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : 2 * c.minDepth < 2 ^ 64)] at hc
            have hklt' : k_v.toNat < 2 * c.minDepth := hc
            have hk1 : (k_v + 1#64).toNat = k_v.toNat + 1 := bv64_add1_toNat hklt' (by omega)
            in_steps
            exact hL2 (k_v + 1#64, ()) m (by dsimp only; rw [hk1]; omega)
              ⟨mstk'.set k_v.toNat 0#32, by rw [hk1]; omega, by simp [hmstl], hm⟩
          · in_steps_nogrp
            refine wp_loop_inv
              (fun (k3, ()) ml3 => ∃ gu' : List (BitVec 32),
                k3.toNat ≤ 64 ∧ gu'.length = 64 ∧
                (FullMem c { s2 with
                  core := { s2.core with min_stk := mstk' },
                  scratch := { s2.scratch with glue_used := gu' } } ⋆ R) ml3)
              (fun (k3, ()) _ => 64 - k3.toNat) ?_ ?_
            · intro L3 hL3; in_steps
              exact hL3 (0#64, ()) ml2 ⟨s2.scratch.glue_used, Nat.zero_le _, hs.glue_used_len, hm2⟩
            · intro L3 ⟨k3, ⟨⟩⟩ ml3 ⟨gu', hk3_le, hgul, hm3⟩ hL3
              in_steps_nogrp
              c0_hsplit
              · have hk3lt' : k3.toNat < 64 := by simpa using hc
                have hk31 : (k3 + 1#64).toNat = k3.toNat + 1 := bv64_add1_toNat hk3lt' (by omega)
                in_steps
                exact hL3 (k3 + 1#64, ()) m (by dsimp only; rw [hk31]; omega)
                  ⟨gu'.set k3.toNat 0#32, by rw [hk31]; omega, by simp [hgul], hm⟩
              · in_steps_nogrp
                refine wp_loop_inv
                  (fun (k4, ()) ml4 => ∃ ll' : List (BitVec 32),
                    k4.toNat ≤ 16 ∧ ll'.length = 16 ∧
                    (∀ j < k4.toNat, ll'[j]? = some 0xFFFFFFFF#32) ∧
                    (FullMem c { s2 with
                      core := { s2.core with min_stk := mstk' },
                      scratch := { s2.scratch with glue_used := gu', last_learned := ll' } } ⋆ R)
                      ml4)
                  (fun (k4, ()) _ => 16 - k4.toNat) ?_ ?_
                · intro L4 hL4; in_steps
                  exact hL4 (0#64, ()) ml3
                    ⟨s2.scratch.last_learned, Nat.zero_le _, hs.last_learned_len,
                      (fun _ h0 => by cases h0), hm3⟩
                · intro L4 ⟨k4, ⟨⟩⟩ ml4 ⟨ll', hk4_le, hlll, hall4, hm4⟩ hL4
                  in_steps_nogrp
                  c0_hsplit
                  · have hk4lt' : k4.toNat < 16 := by simpa using hc
                    have hk41 : (k4 + 1#64).toNat = k4.toNat + 1 :=
                      bv64_add1_toNat hk4lt' (by omega)
                    in_steps
                    refine hL4 (k4 + 1#64, ()) m (by dsimp only; rw [hk41]; omega)
                      ⟨ll'.set k4.toNat 0xFFFFFFFF#32, by rw [hk41]; omega,
                        by simp [hlll], fun j hj => ?_, hm⟩
                    rw [hk41] at hj
                    by_cases hje : j = k4.toNat
                    · subst hje; exact List.getElem?_set_self (by omega)
                    · rw [List.getElem?_set_ne (Ne.symm hje)]; exact hall4 j (by omega)
                  · have hk4eq : k4.toNat = 16 := by simp at hc; omega
                    rw [hk4eq] at hall4
                    in_steps
                    let sc' : FullScratch := { s1.scratch with
                      glue_used := gu', last_learned := ll' }
                    have hsc' : sc'.LengthsOk c :=
                      { hs with
                        walk_vals_len := hwv_s, tarjan_mark_len := htm,
                        tarjan_reach_len := htr, glue_used_len := hgul,
                        last_learned_len := hlll }
                    exact hQ wstk' mstk' st.core.repr sc' ml4 hwstk' hmstl hrp hsc' rfl
                      (last_learned_getD_eq hall4) hm4
      · intro Jw hJw; in_steps_nogrp; c0_hsplit
        · have hwc : c.wcap < 2 * 2 ^ 28 := c.hwcap
          have hwpos' : 0 < s1.core.wstk.length := by
            dsimp only [s1]; rw [hcl.wstk_len_arr]
            rw [Nat.mod_eq_of_lt (by omega : c.wcap < 2 ^ 64)] at hc
            exact hc
          in_steps
          exact hJw () m ⟨_, by rw [List.length_set]; exact hcl.wstk_len_arr, hm⟩
        · in_steps
          exact hJw () ml ⟨s1.core.wstk, hcl.wstk_len_arr, hm1⟩

local elab "in_steps_h5" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 15

local elab "in_steps_18" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 18

@[irreducible] private def Zt2CorePres (s st : FullState) : Prop :=
  st.core = { s.core with
    mrk := st.core.mrk, flags := st.core.flags, lvl := st.core.lvl, rsns := st.core.rsns,
    frame_trail := st.core.frame_trail, frame_dec := st.core.frame_dec }

private def Zt2LoopInv (c : FullCfg) (s st : FullState) (n : Nat) : Prop :=
  n ≤ c.max_vars ∧
  Zt2CorePres s st ∧
  st.LengthsOk c ∧
  FullExtScratchPres s st ∧
  ∀ j < n, st.core.mrk[j]? = some 0#8 ∧ st.core.lvl[j]? = some 0#32 ∧
    st.core.rsns[j]? = some 0xFFFFFFFF#32 ∧ st.core.frame_trail[j]? = some 0#32

private def Zt2Mid5Inv (c : FullCfg) (s st : FullState) (v : Nat) : Prop :=
  v < c.max_vars ∧
  Zt2CorePres s st ∧
  st.LengthsOk c ∧
  FullExtScratchPres s st ∧
  st.core.mrk[v]? = some 0#8 ∧
  ∀ j < v, st.core.mrk[j]? = some 0#8 ∧ st.core.lvl[j]? = some 0#32 ∧
    st.core.rsns[j]? = some 0xFFFFFFFF#32 ∧ st.core.frame_trail[j]? = some 0#32

private theorem zt2_mid5_ok {c : FullCfg} {s st : FullState} {v : Nat}
    (hv : v < c.max_vars) (hinv : Zt2LoopInv c s st v) :
    let st1 : FullState :=
      { core := { st.core with mrk := st.core.mrk.set v 0#8 },
        scratch := { st.scratch with
          phases := st.scratch.phases.set v 0#8,
          phases_target := st.scratch.phases_target.set v 0#8,
          phases_best := st.scratch.phases_best.set v 0#8,
          walk_best := st.scratch.walk_best.set v 1#8 } }
    Zt2Mid5Inv c s st1 v := by
  intro st1
  obtain ⟨_, hag, hlok, hpres, hall⟩ := hinv
  unfold Zt2CorePres at hag
  have hc := hlok.core_ok; have hs := hlok.scratch_ok
  refine ⟨hv, ?_,
    ⟨{ hc with mrk_len := by simp [st1, hc.mrk_len] },
     { hs with
        phases_len := by simp [st1, hs.phases_len],
        phases_target_len := by simp [st1, hs.phases_target_len],
        phases_best_len := by simp [st1, hs.phases_best_len],
        walk_best_len := by simp [st1, hs.walk_best_len] }⟩,
    hpres, List.getElem?_set_self (by rw [hc.mrk_len]; exact hv), fun j hj => ?_⟩
  · unfold Zt2CorePres
    exact congrArg (fun x => { x with mrk := st1.core.mrk }) hag
  · obtain ⟨h1, h2, h3, h4⟩ := hall j hj
    simp only [st1, List.getElem?_set_ne (by omega : v ≠ j)]
    exact ⟨h1, h2, h3, h4⟩

private theorem zt2_mid11_ok {c : FullCfg} {s st1 : FullState} {v : Nat}
    (hmid : Zt2Mid5Inv c s st1 v) :
    let st2 : FullState :=
      { core := { st1.core with
          lvl := st1.core.lvl.set v 0#32,
          rsns := st1.core.rsns.set v 0xFFFFFFFF#32,
          frame_trail := st1.core.frame_trail.set v 0#32,
          frame_dec := st1.core.frame_dec.set v 0xFFFFFFFF#32 },
        scratch := { st1.scratch with
          score := st1.scratch.score.set v 0#64,
          sim_sig := st1.scratch.sim_sig.set v 0#64 } }
    Zt2LoopInv c s st2 (v + 1) := by
  intro st2
  obtain ⟨hv, hag, hlok, hpres, hmrk_v, hall⟩ := hmid
  unfold Zt2CorePres at hag
  have hc := hlok.core_ok; have hs := hlok.scratch_ok
  refine ⟨by omega, ?_,
    ⟨{ hc with
        lvl_len := by simp [st2, hc.lvl_len], rsns_len := by simp [st2, hc.rsns_len],
        frame_trail_len := by simp [st2, hc.frame_trail_len],
        frame_dec_len := by simp [st2, hc.frame_dec_len] },
     { hs with
        score_len := by simp [st2, hs.score_len],
        sim_sig_len := by simp [st2, hs.sim_sig_len] }⟩,
    hpres, fun j hj => ?_⟩
  · unfold Zt2CorePres
    exact congrArg (fun x =>
      { x with
        lvl := st2.core.lvl, rsns := st2.core.rsns,
        frame_trail := st2.core.frame_trail, frame_dec := st2.core.frame_dec }) hag
  by_cases hje : j = v
  · subst hje
    exact ⟨hmrk_v,
      List.getElem?_set_self (by rw [hc.lvl_len]; exact hv),
      List.getElem?_set_self (by rw [hc.rsns_len]; exact hv),
      List.getElem?_set_self (by rw [hc.frame_trail_len]; omega)⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hall j (by omega)
    simp only [st2, List.getElem?_set_ne (Ne.symm hje)]
    exact ⟨h1, h2, h3, h4⟩

private theorem zt2_tail_inv {c : FullCfg} {s st2 : FullState} {n : Nat}
    (hinv : Zt2LoopInv c s st2 n)
    {flags' heap' pos' qp' qn' qs' : List (BitVec 32)}
    (hfl : flags'.length = c.max_vars) (hhp : heap'.length = c.max_vars)
    (hps : pos'.length = c.max_vars) (hqp : qp'.length = c.max_vars)
    (hqn : qn'.length = c.max_vars) (hqs : qs'.length = c.max_vars) :
    Zt2LoopInv c s
      { core := { st2.core with flags := flags' },
        scratch := { st2.scratch with
          heap := heap', pos := pos', q_prev := qp', q_next := qn', q_stamp := qs' } } n := by
  obtain ⟨hv_le, hag, hlok, hpres, hall⟩ := hinv
  unfold Zt2CorePres at hag
  have hc := hlok.core_ok; have hs := hlok.scratch_ok
  refine ⟨hv_le, ?_,
    ⟨{ hc with flags_len := hfl },
     { hs with
        heap_len_arr := hhp, pos_len := hps,
        q_prev_len := hqp, q_next_len := hqn, q_stamp_len := hqs }⟩,
    hpres, hall⟩
  unfold Zt2CorePres
  exact congrArg (fun x => { x with flags := flags' }) hag

private theorem zt2_tail6_wp (Γ : Env) {c : FullCfg} {st2 : FullState}
    {v_v : Val i64} {m : Mem 64} {Q : Post []} {X : XPost} {R : Mem 64 → Prop}
    {k : Expr Val Cont []}
    (hfl2 : st2.core.flags.length = c.max_vars)
    (hhp2 : st2.scratch.heap.length = c.max_vars)
    (hps2 : st2.scratch.pos.length = c.max_vars)
    (hqp2 : st2.scratch.q_prev.length = c.max_vars)
    (hqn2 : st2.scratch.q_next.length = c.max_vars)
    (hqs2 : st2.scratch.q_stamp.length = c.max_vars)
    (hvv : v_v.toNat < c.max_vars) (hm2 : (FullMem c st2 ⋆ R) m)
    (hk : ∀ (flags' heap' pos' qp' qn' qs' : List (BitVec 32)) m',
      flags'.length = c.max_vars → heap'.length = c.max_vars → pos'.length = c.max_vars →
      qp'.length = c.max_vars → qn'.length = c.max_vars → qs'.length = c.max_vars →
      (FullMem c
        ({ core := { st2.core with flags := flags' },
           scratch := { st2.scratch with
             heap := heap', pos := pos', q_prev := qp', q_next := qn', q_stamp := qs' } } :
          FullState) ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X
      (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
       Expr.let_ (Op.mk (.add i64) (Arg.var c.pFlags, Arg.var p.1, ())) fun p =>
       Expr.store (Arg.imm (t := i32) 0) (Arg.var p.1)
         (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
          Expr.let_ (Op.mk (.add i64) (Arg.var c.pHeap, Arg.var p.1, ())) fun p =>
          Expr.store (Arg.imm (t := i32) 0) (Arg.var p.1)
            (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
             Expr.let_ (Op.mk (.add i64) (Arg.var c.pPos, Arg.var p.1, ())) fun p =>
             Expr.store (Arg.imm (t := i32) 4294967295) (Arg.var p.1)
               (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
                Expr.let_ (Op.mk (.add i64) (Arg.var c.pQPrev, Arg.var p.1, ())) fun p =>
                Expr.store (Arg.imm (t := i32) 4294967295) (Arg.var p.1)
                  (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
                   Expr.let_ (Op.mk (.add i64) (Arg.var c.pQNext, Arg.var p.1, ())) fun p =>
                   Expr.store (Arg.imm (t := i32) 4294967295) (Arg.var p.1)
                     (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
                      Expr.let_ (Op.mk (.add i64) (Arg.var c.pQStamp, Arg.var p.1, ())) fun p =>
                      Expr.store (Arg.imm (t := i32) 0) (Arg.var p.1) k))))))
      m := by
  c0_hstraight
  exact hk _ _ _ _ _ _ m (by rw [List.length_set]; exact hfl2)
    (by rw [List.length_set]; exact hhp2) (by rw [List.length_set]; exact hps2)
    (by rw [List.length_set]; exact hqp2) (by rw [List.length_set]; exact hqn2)
    (by rw [List.length_set]; exact hqs2) hm

@[irreducible] private def Zt2LoopCont (c : FullCfg) (s : FullState) (v : Nat)
    (L : Cont [i64]) (R : Mem 64 → Prop) : Prop :=
  ∀ (a : Val i64) (m : Mem 64),
    (c.max_vars - a.toNat) < (c.max_vars - v) →
    (∃ st_n, Zt2LoopInv c s st_n a.toNat ∧ (FullMem c st_n ⋆ R) m) → L (a, ()) m

theorem full_zero_tables2_wp (Γ : Env) :
    ∀ a m Q X, fullZeroTables2Spec a m Q X → Func.wp Γ full_zero_tables2_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hlen, hm0, hQ⟩
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  have hmx64 : c.max_vars < 2 ^ 64 := by omega
  have hmx_to : (BitVec.ofNat 64 c.max_vars).toNat = c.max_vars := bv64_ofNat_toNat (by omega)
  unfold Func.wp full_zero_tables2_body
  c0_hstraight
  refine wp_loop_inv
    (fun (v_v, ()) ml => ∃ st : FullState, Zt2LoopInv c s st v_v.toNat ∧
      (FullMem c st ⋆ R) ml)
    (fun (v_v, ()) _ => c.max_vars - v_v.toNat) ?_ ?_
  · intro L hL; c0_hstraight
    refine hL (0#64, ()) m0 ⟨s, ⟨Nat.zero_le _, ?_, hlen, ⟨rfl, rfl⟩, fun _ h0 => by cases h0⟩, hm0⟩
    unfold Zt2CorePres; rfl
  · intro L ⟨v_v, ⟨⟩⟩ m ⟨st, hinv, hm⟩ hL
    clear hm0
    obtain ⟨hv_le, hag, hlok, hpres, hall⟩ := hinv
    have hcl := hlok.core_ok; have hs := hlok.scratch_ok
    have hmrk_l : st.core.mrk.length = c.max_vars := hcl.mrk_len
    have hlvl_l : st.core.lvl.length = c.max_vars := hcl.lvl_len
    have hrsns_l : st.core.rsns.length = c.max_vars := hcl.rsns_len
    have hft_l : st.core.frame_trail.length = c.max_vars + 1 := hcl.frame_trail_len
    have hfd_l : st.core.frame_dec.length = c.max_vars + 1 := hcl.frame_dec_len
    c0_hsplit_nobound
    · rw [Nat.mod_eq_of_lt hmx64] at hc
      have hvlt' : v_v.toNat < c.max_vars := hc
      have hv1 := bv64_add1_toNat hvlt' hmx64
      have hph_l : st.scratch.phases.length = c.max_vars := hs.phases_len
      have hpt_l : st.scratch.phases_target.length = c.max_vars := hs.phases_target_len
      have hpb_l : st.scratch.phases_best.length = c.max_vars := hs.phases_best_len
      have hwb_l : st.scratch.walk_best.length = c.max_vars := hs.walk_best_len
      have hcont : Zt2LoopCont c s v_v.toNat L R := by
        unfold Zt2LoopCont; exact fun a ma hma hst => hL (a, ()) ma hma hst
      clear hlvl_l hrsns_l hft_l hfd_l hL hQ hc hmx hmx64 hmx_to
      in_steps_h5
      obtain ⟨st1, hinv1, hm1⟩ : ∃ st1 : FullState,
          Zt2Mid5Inv c s st1 v_v.toNat ∧ (FullMem c st1 ⋆ R) m :=
        ⟨_, zt2_mid5_ok hvlt' ⟨hv_le, hag, hlok, hpres, hall⟩, hm⟩
      clear hm hv_le hag hlok hcl hs hpres hall hmrk_l hph_l hpt_l hpb_l hwb_l
      have hm := hm1; clear hm1
      have hl1 := hinv1.2.2.1.core_ok; have hs1 := hinv1.2.2.1.scratch_ok
      have hlvl_l : st1.core.lvl.length = c.max_vars := hl1.lvl_len
      have hrsns_l : st1.core.rsns.length = c.max_vars := hl1.rsns_len
      have hft_l : st1.core.frame_trail.length = c.max_vars + 1 := hl1.frame_trail_len
      have hfd_l : st1.core.frame_dec.length = c.max_vars + 1 := hl1.frame_dec_len
      have hsc_l : st1.scratch.score.length = c.max_vars := hs1.score_len
      have hsg_l : st1.scratch.sim_sig.length = c.max_vars := hs1.sim_sig_len
      in_steps_18
      obtain ⟨st2, hinv2, hm2⟩ : ∃ st2 : FullState,
          Zt2LoopInv c s st2 (v_v.toNat + 1) ∧ (FullMem c st2 ⋆ R) m :=
        ⟨_, zt2_mid11_ok hinv1, hm⟩
      clear hm hinv1 hl1 hs1 hlvl_l hrsns_l hft_l hfd_l hsc_l hsg_l
      have hl2 := hinv2.2.2.1.core_ok; have hs2 := hinv2.2.2.1.scratch_ok
      refine zt2_tail6_wp Γ hl2.flags_len hs2.heap_len_arr hs2.pos_len
        hs2.q_prev_len hs2.q_next_len hs2.q_stamp_len hvlt' hm2 ?_
      intro fl' hp' ps' qp' qn' qs' m' hfl hhp hps hqp hqn hqs hm'
      c0_hstraight
      unfold Zt2LoopCont at hcont
      exact hcont (v_v + 1#64) m'
        (by rw [hv1]; exact Nat.sub_lt_sub_left hvlt' (Nat.lt_succ_self _))
        ⟨_, by rw [hv1]; exact zt2_tail_inv hinv2 hfl hhp hps hqp hqn hqs, hm'⟩
    · rw [Nat.mod_eq_of_lt hmx64] at hc
      have hveq : v_v.toNat = c.max_vars := Nat.le_antisymm hv_le (Nat.not_lt.mp hc)
      rw [hveq] at hall
      c0_hstraight
      have hmrk : st.core.mrk = List.replicate c.max_vars 0#8 :=
        list_eq_replicate_of_forall hmrk_l fun j hj => (hall j hj).1
      have hlvl : st.core.lvl = List.replicate c.max_vars 0#32 :=
        list_eq_replicate_of_forall hlvl_l fun j hj => (hall j hj).2.1
      have hrsns : st.core.rsns = List.replicate c.max_vars 0xFFFFFFFF#32 :=
        list_eq_replicate_of_forall hrsns_l fun j hj => (hall j hj).2.2.1
      let ftrl' := st.core.frame_trail.set c.max_vars 0#32
      let fdec' := st.core.frame_dec.set c.max_vars 0xFFFFFFFF#32
      have hftrl_len : ftrl'.length = c.max_vars + 1 := by
        dsimp only [ftrl']; rw [List.length_set, hft_l]
      have hfdec_len : fdec'.length = c.max_vars + 1 := by
        dsimp only [fdec']; rw [List.length_set, hfd_l]
      have hftrl : ftrl' = List.replicate (c.max_vars + 1) 0#32 := by
        refine list_eq_replicate_of_forall hftrl_len fun j hj => ?_
        by_cases hje : j = c.max_vars
        · subst hje; exact List.getElem?_set_self (by rw [hft_l]; exact Nat.lt_succ_self _)
        · rw [List.getElem?_set_ne (Ne.symm hje)]
          exact (hall j (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hj) hje)).2.2.2
      have hcore_eq :
          { s.core with
            mrk := List.replicate c.max_vars 0#8, flags := st.core.flags,
            lvl := List.replicate c.max_vars 0#32,
            rsns := List.replicate c.max_vars 0xFFFFFFFF#32,
            frame_trail := List.replicate (c.max_vars + 1) 0#32, frame_dec := fdec' } =
          { st.core with
            frame_trail := st.core.frame_trail.set c.max_vars 0#32,
            frame_dec := st.core.frame_dec.set c.max_vars 0xFFFFFFFF#32 } := by
        unfold Zt2CorePres at hag
        rw [hag, hmrk, hlvl, hrsns, ← hftrl]
      have hm_out : (FullMem c { s with
          core := { s.core with
            mrk := List.replicate c.max_vars 0#8, flags := st.core.flags,
            lvl := List.replicate c.max_vars 0#32, rsns := List.replicate c.max_vars 0xFFFFFFFF#32,
            frame_trail := List.replicate (c.max_vars + 1) 0#32, frame_dec := fdec' },
          scratch := st.scratch } ⋆ R) m := by
        rw [hcore_eq]; dsimp only [ftrl', fdec']; rw [hmx_to] at hm; exact hm
      exact hQ st.core.flags fdec' st.scratch m hcl.flags_len hfdec_len hs hpres hm_out

end ZeroTables

end LeanQbe.T.Examples.Kissat.Proof.Internal
