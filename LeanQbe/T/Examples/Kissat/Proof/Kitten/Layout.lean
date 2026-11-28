/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb
public import LeanQbe.T.Logic.SepTree

/-!
# Dynamic `K6Layout` and `K6State` Slab Serialization (`Kissat.Proof.Kitten.Layout`)

Zero legacy `Full*` imports; zero `@[expose]` on theorems/lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Kitten

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-! ## 1. Dynamic `K6Layout` & Pure Bitvector / Offset Helpers -/

@[expose] def k6PhtHead : Nat := 256
@[expose] def k6PhtSz : Nat := 1024
@[expose] def k6PhtNext : Nat := 1280
@[expose] def k6MinScr : Nat := 24576
@[expose] def k6MaxVCap : Nat := 8192

@[expose] def k6MaxV (cap : Nat) : Nat :=
  if cap < k6MinScr then 0
  else if 524288 ≤ cap then k6MaxVCap
  else
    let raw := ((cap - 1312) / 45) / 64 * 64
    max 512 (min k6MaxVCap raw)

theorem k6MaxV_eq_zero {cap : Nat} (h : cap < k6MinScr) : k6MaxV cap = 0 := by
  simp [k6MaxV, h]

theorem k6MaxV_bounds {cap : Nat} (hge : k6MinScr ≤ cap) :
    512 ≤ k6MaxV cap ∧ k6MaxV cap ≤ 8192 ∧
    1280 + 2 * k6MaxV cap + 32 + 38 * k6MaxV cap + 2560 ≤ cap ∧
    2560 ≤ cap - (1280 + 2 * k6MaxV cap + 32 + 38 * k6MaxV cap) := by
  have h1 : ¬ cap < k6MinScr := Nat.not_lt.mpr hge
  unfold k6MaxV k6MaxVCap; simp only [h1, ↓reduceIte]; split
  · next h2 =>
    refine ⟨by decide, by decide, ?_, ?_⟩ <;> (unfold k6MinScr at hge; omega)
  · next h2 =>
    unfold k6MinScr at hge
    have hdiv : ((cap - 1312) / 45) / 64 * 64 ≤ (cap - 1312) / 45 :=
      Nat.div_mul_le_self ((cap - 1312) / 45) 64
    have h45 : (cap - 1312) / 45 * 45 ≤ cap - 1312 := Nat.div_mul_le_self (cap - 1312) 45
    omega

theorem k6MaxV_512 : k6MaxV 24576 = 512 := by decide

private theorem bv64_and_not63 (x : BitVec 64) :
    (x &&& 0xFFFFFFFFFFFFFFC0#64).toNat = x.toNat / 64 * 64 := by
  have heq : x &&& 0xFFFFFFFFFFFFFFC0#64 = (x >>> (6 : Nat)) <<< (6 : Nat) := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, hi,
      decide_true, Bool.true_and]
    by_cases h6 : i < 6
    · have hf : (0xFFFFFFFFFFFFFFC0#64).getLsbD i = false := by revert i hi h6; decide
      simp [h6, hf]
    · have ht : (0xFFFFFFFFFFFFFFC0#64).getLsbD i = true := by
        have hge : 6 ≤ i := by omega
        revert i hi h6 hge; decide
      simp [h6, ht]; rw [Nat.add_sub_cancel' (by omega)]
  rw [heq]; simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  have := x.isLt; rw [Nat.mod_eq_of_lt (by omega)]

theorem k6MaxV_bv64_eq {cap : Nat} (hlt : cap < 2 ^ 64) :
    let cap64 := BitVec.ofNat 64 cap
    let r64 : BitVec 64 :=
      if cap64 < 24576#64 then 0#64
      else if 524288#64 ≤ cap64 then 8192#64
      else
        let raw := ((cap64 - 1312#64) / 45#64) &&& 0xFFFFFFFFFFFFFFC0#64
        if raw < 512#64 then 512#64 else if 8192#64 < raw then 8192#64 else raw
    r64 = BitVec.ofNat 64 (k6MaxV cap) := by
  dsimp only; unfold k6MaxV k6MinScr k6MaxVCap
  by_cases h1 : cap < 24576
  · have hb1 : BitVec.ofNat 64 cap < 24576#64 := by
      change (BitVec.ofNat 64 cap).toNat < (24576#64).toNat; bv_omega
    simp [h1, hb1]
  · have hb1 : ¬ BitVec.ofNat 64 cap < 24576#64 := by
      change ¬ (BitVec.ofNat 64 cap).toNat < (24576#64).toNat; bv_omega
    simp only [h1, hb1, ↓reduceIte]
    by_cases h2 : 524288 ≤ cap
    · have hb2 : 524288#64 ≤ BitVec.ofNat 64 cap := by
        change (524288#64).toNat ≤ (BitVec.ofNat 64 cap).toNat; bv_omega
      simp [h2, hb2]
    · have hb2 : ¬ 524288#64 ≤ BitVec.ofNat 64 cap := by
        change ¬ (524288#64).toNat ≤ (BitVec.ofNat 64 cap).toNat; bv_omega
      simp only [h2, hb2, ↓reduceIte]
      have hsub : (BitVec.ofNat 64 cap - 1312#64).toNat = cap - 1312 := by bv_omega
      have hdiv : ((BitVec.ofNat 64 cap - 1312#64) / 45#64).toNat = (cap - 1312) / 45 := by
        rw [BitVec.toNat_udiv, hsub]; rfl
      have hraw :
          (((BitVec.ofNat 64 cap - 1312#64) / 45#64) &&& 0xFFFFFFFFFFFFFFC0#64).toNat =
            ((cap - 1312) / 45) / 64 * 64 := by
        rw [bv64_and_not63, hdiv]
      apply BitVec.eq_of_toNat_eq
      by_cases hr1 : ((cap - 1312) / 45) / 64 * 64 < 512
      · have hb :
            (((BitVec.ofNat 64 cap - 1312#64) / 45#64) &&& 0xFFFFFFFFFFFFFFC0#64) < 512#64 := by
          change
            (((BitVec.ofNat 64 cap - 1312#64) / 45#64) &&& 0xFFFFFFFFFFFFFFC0#64).toNat < 512
          rw [hraw]; exact hr1
        simp only [hb, ↓reduceIte]
        rw [show max 512 (min 8192 (((cap - 1312) / 45) / 64 * 64)) = 512 by omega]
      · have hb :
            ¬ (((BitVec.ofNat 64 cap - 1312#64) / 45#64) &&& 0xFFFFFFFFFFFFFFC0#64) < 512#64 := by
          change
            ¬ (((BitVec.ofNat 64 cap - 1312#64) / 45#64) &&& 0xFFFFFFFFFFFFFFC0#64).toNat < 512
          rw [hraw]; exact hr1
        simp only [hb, ↓reduceIte]
        by_cases hr2 : 8192 < ((cap - 1312) / 45) / 64 * 64
        · have hb2 : (8192#64 : BitVec 64) <
              (((BitVec.ofNat 64 cap - 1312#64) / 45#64) &&& 0xFFFFFFFFFFFFFFC0#64) := by
            change 8192 < (((BitVec.ofNat 64 cap - 1312#64) / 45#64) &&&
              0xFFFFFFFFFFFFFFC0#64).toNat
            rw [hraw]; exact hr2
          simp only [hb2, ↓reduceIte]
          rw [show max 512 (min 8192 (((cap - 1312) / 45) / 64 * 64)) = 8192 by omega]
        · have hb2 : ¬ (8192#64 : BitVec 64) <
              (((BitVec.ofNat 64 cap - 1312#64) / 45#64) &&& 0xFFFFFFFFFFFFFFC0#64) := by
            change ¬ 8192 < (((BitVec.ofNat 64 cap - 1312#64) / 45#64) &&&
              0xFFFFFFFFFFFFFFC0#64).toNat
            rw [hraw]; exact hr2
          simp only [hb2, ↓reduceIte, hraw, BitVec.toNat_ofNat]
          rw [Nat.mod_eq_of_lt (by omega)]; omega

structure K6Layout where
  maxV : Nat
  acap : Nat
  hmaxV : 512 ≤ maxV ∧ maxV ≤ 8192
  hacap : 2560 ≤ acap ∧ acap < dimacsBound

@[expose] def K6Layout.maxOrig (L : K6Layout) : Nat := 3 * L.maxV
@[expose] def K6Layout.maxCl (L : K6Layout) : Nat := 4 * L.maxV
@[expose] def K6Layout.phtMerged (L : K6Layout) : Nat := 1280 + L.maxV
@[expose] def K6Layout.k6Base (L : K6Layout) : Nat := 1280 + 2 * L.maxV
@[expose] def K6Layout.k6Fixed (L : K6Layout) : Nat := 32 + 38 * L.maxV
@[expose] def K6Layout.scrLen (L : K6Layout) : Nat := L.k6Base + L.k6Fixed + L.acap
@[expose] def K6Layout.oLvl (_L : K6Layout) : Nat := 32
@[expose] def K6Layout.oRsn (L : K6Layout) : Nat := 32 + L.maxV
@[expose] def K6Layout.oQPrev (L : K6Layout) : Nat := 32 + 2 * L.maxV
@[expose] def K6Layout.oQNext (L : K6Layout) : Nat := 32 + 3 * L.maxV
@[expose] def K6Layout.oQStamp (L : K6Layout) : Nat := 32 + 4 * L.maxV
@[expose] def K6Layout.oTrl (L : K6Layout) : Nat := 32 + 5 * L.maxV
@[expose] def K6Layout.oFlags (L : K6Layout) : Nat := 32 + 6 * L.maxV
@[expose] def K6Layout.oAna (L : K6Layout) : Nat := 32 + 7 * L.maxV
@[expose] def K6Layout.oKl (L : K6Layout) : Nat := 32 + 8 * L.maxV
@[expose] def K6Layout.oAssump (L : K6Layout) : Nat := 32 + 9 * L.maxV
@[expose] def K6Layout.oVals (L : K6Layout) : Nat := 32 + 10 * L.maxV
@[expose] def K6Layout.oWHead (L : K6Layout) : Nat := 32 + 12 * L.maxV
@[expose] def K6Layout.oWNext (L : K6Layout) : Nat := 32 + 14 * L.maxV
@[expose] def K6Layout.oWBlit (L : K6Layout) : Nat := 32 + 22 * L.maxV
@[expose] def K6Layout.oClOff (L : K6Layout) : Nat := 32 + 30 * L.maxV
@[expose] def K6Layout.oClSz (L : K6Layout) : Nat := 32 + 34 * L.maxV
@[expose] def K6Layout.oArena (L : K6Layout) : Nat := 32 + 38 * L.maxV
@[expose] def K6Layout.mv32 (L : K6Layout) : BitVec 32 := BitVec.ofNat 32 L.maxV
@[expose] def K6Layout.kPtr (L : K6Layout) (pScr : BitVec 64) : BitVec 64 :=
  pScr + BitVec.ofNat 64 (4 * L.k6Base)

@[expose]
def k6LayoutOfCap (cap : Nat) (hge : k6MinScr ≤ cap) (hlt : cap < dimacsBound) : K6Layout :=
  let mv := k6MaxV cap
  { maxV := mv
    acap := cap - (1280 + 2 * mv + 32 + 38 * mv)
    hmaxV := ⟨(k6MaxV_bounds hge).1, (k6MaxV_bounds hge).2.1⟩
    hacap := ⟨(k6MaxV_bounds hge).2.2.2, by
      have := (k6MaxV_bounds hge).2.2.1; unfold dimacsBound at *; omega⟩ }

theorem k6LayoutOfCap_scrLen {cap : Nat} (hge : k6MinScr ≤ cap) (hlt : cap < dimacsBound) :
    (k6LayoutOfCap cap hge hlt).scrLen = cap := by
  unfold K6Layout.scrLen K6Layout.k6Base K6Layout.k6Fixed k6LayoutOfCap
  have := (k6MaxV_bounds hge).2.2.1; dsimp only; omega

theorem K6Layout.eq_of_scrLen_maxV {L1 L2 : K6Layout} (hlen : L1.scrLen = L2.scrLen)
    (hmv : L1.maxV = L2.maxV) : L1 = L2 := by
  cases L1; cases L2
  dsimp only [K6Layout.scrLen, K6Layout.k6Base, K6Layout.k6Fixed] at hlen hmv
  subst hmv; congr 1; omega

theorem k6LayoutOfCap_eq {L : K6Layout} {cap : Nat} (hlen : L.scrLen = cap)
    (hmv : L.maxV = k6MaxV cap) (hge : k6MinScr ≤ cap) (hlt : cap < dimacsBound) :
    k6LayoutOfCap cap hge hlt = L :=
  K6Layout.eq_of_scrLen_maxV ((k6LayoutOfCap_scrLen hge hlt).trans hlen.symm) hmv.symm

theorem k6_bv32_div2_lt {nv : Nat} {l : BitVec 32} (hl : l.toNat < 2 * nv) :
    (l >>> (1 : Nat)).toNat = l.toNat / 2 ∧ (l >>> (1 : Nat)).toNat < nv := by
  have hd : (l >>> (1 : Nat)).toNat = l.toNat / 2 := bv32_lshr_1 l
  exact ⟨hd, by omega⟩

theorem k6_bv32_xor1_lt {nv : Nat} {l : BitVec 32} (hl : l.toNat < 2 * nv) :
    (l ^^^ 1#32).toNat = litNeg l.toNat ∧ (l ^^^ 1#32).toNat < 2 * nv := by
  have hx : (l ^^^ 1#32).toNat = litNeg l.toNat := bv32_xor_1 l
  have hlt : litNeg l.toNat < 2 * nv := by
    have h := litNeg_eq l.toNat; split at h <;> omega
  exact ⟨hx, by rw [hx]; exact hlt⟩

theorem k6_bv32_cid_w0 {nc : Nat} {cid : BitVec 32} (hc : cid.toNat < nc) (_hnc : nc ≤ 32768) :
    (cid <<< 1).toNat = 2 * cid.toNat ∧ (cid <<< 1).toNat < 2 * nc := by
  have h1 : (cid <<< 1).toNat = 2 * cid.toNat := by bv_omega
  exact ⟨h1, by omega⟩

theorem k6_bv32_cid_w1 {nc : Nat} {cid : BitVec 32} (hc : cid.toNat < nc) (_hnc : nc ≤ 32768) :
    ((cid <<< 1) ||| 1#32).toNat = 2 * cid.toNat + 1 ∧ ((cid <<< 1) ||| 1#32).toNat < 2 * nc := by
  have h0 : (cid <<< 1).toNat = 2 * cid.toNat := by bv_omega
  have h1 : ((cid <<< 1) ||| 1#32).toNat = 2 * cid.toNat + 1 := by
    rw [BitVec.toNat_or, show (1#32 : BitVec 32).toNat = 1 from rfl, h0]
    apply Nat.eq_of_testBit_eq; intro i
    cases i with
    | zero => simp [Nat.testBit_zero]
    | succ j =>
      rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
      simp [show (2 * cid.toNat + 1) / 2 = cid.toNat by omega]
  exact ⟨h1, by omega⟩

theorem k6_ptr_nat_mul4 (p : BitVec 64) (idx : Nat) (_h : idx < 2 ^ 28) :
    p + BitVec.ofNat 64 idx * 4 = p + BitVec.ofNat 64 (4 * idx) := by
  congr 1; bv_omega

theorem k6_ptr_base_k6Base (L : K6Layout) (pScr : BitVec 64) :
    pScr + BitVec.ofNat 64 (4 * L.k6Base) = L.kPtr pScr := rfl

theorem k6_ptr_add_mul (L : K6Layout) (kPtr : BitVec 64) (c : Nat) (_hc : c ≤ 38) :
    kPtr + BitVec.ofNat 64 (4 * (32 + c * L.maxV)) =
      (kPtr + BitVec.ofNat 64 (4 * (32 + c * L.maxV))) := rfl

theorem k6_ptr_add_off (base : BitVec 64) (k1 k2 : Nat) :
    (base + BitVec.ofNat 64 (4 * k1)) + BitVec.ofNat 64 (4 * k2) =
      base + BitVec.ofNat 64 (4 * (k1 + k2)) := by
  rw [ptr_add_ofNat]; congr 1; apply BitVec.eq_of_toNat_eq; bv_omega

theorem k6_ptr_add_1 (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + BitVec.ofNat 64 (4 * (32 + L.maxV)) =
      kPtr + BitVec.ofNat 64 (4 * L.oRsn) := rfl

theorem k6_ptr_lvl (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + BitVec.ofNat 64 (4 * 32) = kPtr + BitVec.ofNat 64 (4 * L.oLvl) := rfl

/-! ## 2. `K6State`, `ShapesOk`, and Slab Serialization -/

structure K6State where
  nv : BitVec 32
  nc : BitVec 32
  lvl : BitVec 32
  prop : BitVec 32
  trl_end : BitVec 32
  unass : BitVec 32
  incons : BitVec 32
  qfirst : BitVec 32
  qlast : BitVec 32
  qsearch : BitVec 32
  qstamp : BitVec 32
  ticks : BitVec 32
  tick_lim : BitVec 32
  alen : BitVec 32
  acap : BitVec 32
  nassump : BitVec 32
  nkl : BitVec 32
  nana : BitVec 32
  status : BitVec 32
  phase : BitVec 32
  openCnt : BitVec 32
  max_v : BitVec 32
  max_orig : BitVec 32
  max_cl : BitVec 32
  neq : BitVec 32
  hdrTail : List (BitVec 32)
  lvlArr : List (BitVec 32)
  rsn : List (BitVec 32)
  qprev : List (BitVec 32)
  qnext : List (BitVec 32)
  qstampArr : List (BitVec 32)
  trl : List (BitVec 32)
  flags : List (BitVec 32)
  ana : List (BitVec 32)
  kl : List (BitVec 32)
  assump : List (BitVec 32)
  vals : List (BitVec 32)
  whead : List (BitVec 32)
  wnext : List (BitVec 32)
  wblit : List (BitVec 32)
  clOff : List (BitVec 32)
  clSz : List (BitVec 32)
  arena : List (BitVec 32)

@[expose] def k6HdrWords (ks : K6State) : List (BitVec 32) :=
  [ks.nv, ks.nc, ks.lvl, ks.prop, ks.trl_end, ks.unass, ks.incons, ks.qfirst, ks.qlast,
   ks.qsearch, ks.qstamp, ks.ticks, ks.tick_lim, ks.alen, ks.acap, ks.nassump, ks.nkl,
   ks.nana, ks.status, ks.phase, ks.openCnt, ks.max_v, ks.max_orig, ks.max_cl, ks.neq] ++
  ks.hdrTail

structure K6State.ShapesOk (L : K6Layout) (ks : K6State) : Prop where
  hdrTail_len : ks.hdrTail.length = 7
  lvlArr_len : ks.lvlArr.length = L.maxV
  rsn_len : ks.rsn.length = L.maxV
  qprev_len : ks.qprev.length = L.maxV
  qnext_len : ks.qnext.length = L.maxV
  qstampArr_len : ks.qstampArr.length = L.maxV
  trl_len : ks.trl.length = L.maxV
  flags_len : ks.flags.length = L.maxV
  ana_len : ks.ana.length = L.maxV
  kl_len : ks.kl.length = L.maxV
  assump_len : ks.assump.length = L.maxV
  vals_len : ks.vals.length = 2 * L.maxV
  whead_len : ks.whead.length = 2 * L.maxV
  wnext_len : ks.wnext.length = 2 * L.maxCl
  wblit_len : ks.wblit.length = 2 * L.maxCl
  clOff_len : ks.clOff.length = L.maxCl
  clSz_len : ks.clSz.length = L.maxCl
  arena_len : ks.arena.length = L.acap

theorem k6HdrWords_length {L : K6Layout} {ks : K6State} (h : ks.ShapesOk L) :
    (k6HdrWords ks).length = 32 := by
  simp [k6HdrWords, h.hdrTail_len]

@[expose] def K6State.toSlab (ks : K6State) : List (BitVec 32) :=
  k6HdrWords ks ++ (ks.lvlArr ++ (ks.rsn ++ (ks.qprev ++ (ks.qnext ++ (ks.qstampArr ++
  (ks.trl ++ (ks.flags ++ (ks.ana ++ (ks.kl ++ (ks.assump ++ (ks.vals ++ (ks.whead ++
  (ks.wnext ++ (ks.wblit ++ (ks.clOff ++ (ks.clSz ++ ks.arena))))))))))))))))

private theorem k6_toSlab_len_arith (v a : Nat) :
    32 + (v + (v + (v + (v + (v + (v + (v + (v + (v + (v + (2 * v + (2 * v +
      (2 * (4 * v) + (2 * (4 * v) + (4 * v + (4 * v + a)))))))))))))))) =
    (32 + 38 * v) + a := by omega

theorem K6State.toSlab_length {L : K6Layout} {ks : K6State} (h : ks.ShapesOk L) :
    ks.toSlab.length = L.k6Fixed + L.acap := by
  have hh := k6HdrWords_length h
  rcases h with ⟨_, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
  dsimp only [K6State.toSlab]
  simp only [List.length_append, hh, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17]
  unfold K6Layout.maxCl K6Layout.k6Fixed
  exact k6_toSlab_len_arith L.maxV L.acap

@[expose] def K6State.ofSlab (L : K6Layout) (xs : List (BitVec 32)) : K6State where
  nv := xs[0]?.getD 0#32
  nc := xs[1]?.getD 0#32
  lvl := xs[2]?.getD 0#32
  prop := xs[3]?.getD 0#32
  trl_end := xs[4]?.getD 0#32
  unass := xs[5]?.getD 0#32
  incons := xs[6]?.getD 0#32
  qfirst := xs[7]?.getD 0#32
  qlast := xs[8]?.getD 0#32
  qsearch := xs[9]?.getD 0#32
  qstamp := xs[10]?.getD 0#32
  ticks := xs[11]?.getD 0#32
  tick_lim := xs[12]?.getD 0#32
  alen := xs[13]?.getD 0#32
  acap := xs[14]?.getD 0#32
  nassump := xs[15]?.getD 0#32
  nkl := xs[16]?.getD 0#32
  nana := xs[17]?.getD 0#32
  status := xs[18]?.getD 0#32
  phase := xs[19]?.getD 0#32
  openCnt := xs[20]?.getD 0#32
  max_v := xs[21]?.getD 0#32
  max_orig := xs[22]?.getD 0#32
  max_cl := xs[23]?.getD 0#32
  neq := xs[24]?.getD 0#32
  hdrTail := (xs.drop 25).take 7
  lvlArr := (xs.drop L.oLvl).take L.maxV
  rsn := (xs.drop L.oRsn).take L.maxV
  qprev := (xs.drop L.oQPrev).take L.maxV
  qnext := (xs.drop L.oQNext).take L.maxV
  qstampArr := (xs.drop L.oQStamp).take L.maxV
  trl := (xs.drop L.oTrl).take L.maxV
  flags := (xs.drop L.oFlags).take L.maxV
  ana := (xs.drop L.oAna).take L.maxV
  kl := (xs.drop L.oKl).take L.maxV
  assump := (xs.drop L.oAssump).take L.maxV
  vals := (xs.drop L.oVals).take (2 * L.maxV)
  whead := (xs.drop L.oWHead).take (2 * L.maxV)
  wnext := (xs.drop L.oWNext).take (2 * L.maxCl)
  wblit := (xs.drop L.oWBlit).take (2 * L.maxCl)
  clOff := (xs.drop L.oClOff).take L.maxCl
  clSz := (xs.drop L.oClSz).take L.maxCl
  arena := xs.drop L.oArena

theorem K6State.shapesOk_ofSlab_eq {L : K6Layout} {xs : List (BitVec 32)}
    (h : xs.length = L.k6Fixed + L.acap) :
    (K6State.ofSlab L xs).ShapesOk L := by
  unfold K6Layout.k6Fixed at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [K6State.ofSlab, List.length_take, List.length_drop,
    K6Layout.oLvl, K6Layout.oRsn, K6Layout.oQPrev, K6Layout.oQNext, K6Layout.oQStamp,
    K6Layout.oTrl, K6Layout.oFlags, K6Layout.oAna, K6Layout.oKl, K6Layout.oAssump,
    K6Layout.oVals, K6Layout.oWHead, K6Layout.oWNext, K6Layout.oWBlit, K6Layout.oClOff,
    K6Layout.oClSz, K6Layout.oArena, K6Layout.maxCl]
  all_goals omega

private theorem k6_slice_append {α : Type _} (xs : List α) (a b : Nat) :
    (xs.drop a).take b ++ xs.drop (a + b) = xs.drop a := by
  rw [← @List.drop_drop _ b a xs, List.take_append_drop]

private theorem k6_drop_exact {α : Type _} (p s : List α) {k : Nat} (hk : p.length = k) :
    (p ++ s).drop k = s := by
  rw [List.drop_append_of_le_length (by omega), ← hk, List.drop_length, List.nil_append]

private theorem k6_drop_step {α : Type _} {xs p rest : List α} {k0 : Nat} (k1 : Nat) {n : Nat}
    (hd : xs.drop k0 = p ++ rest) (hp : p.length = n) (hsum : k1 = k0 + n) :
    xs.drop k1 = rest := by
  rw [hsum, ← List.drop_drop, hd]; exact k6_drop_exact p rest hp

private theorem k6_take_prefix {α : Type _} {xs p rest : List α} {k n : Nat}
    (hd : xs.drop k = p ++ rest) (hp : p.length = n) :
    (xs.drop k).take n = p := by
  rw [hd, List.take_append_of_le_length (by omega), ← hp, List.take_length]

private theorem k6_slice_append_eq {α : Type _} (xs : List α) {a b c : Nat}
    (h : c = a + b) : (xs.drop a).take b ++ xs.drop c = xs.drop a := by
  subst h; exact k6_slice_append xs a b

theorem K6State.toSlab_ofSlab {L : K6Layout} {xs : List (BitVec 32)}
    (h : L.k6Fixed ≤ xs.length) :
    (K6State.ofSlab L xs).toSlab = xs := by
  have hxs : 32 ≤ xs.length := by unfold K6Layout.k6Fixed at h; omega
  have hht : (K6State.ofSlab L xs).hdrTail.length = 7 := by
    simp only [K6State.ofSlab, List.length_take, List.length_drop]; omega
  have hkh : (k6HdrWords (K6State.ofSlab L xs)).length = 32 := by
    simp [k6HdrWords, hht]
  have h0 : k6HdrWords (K6State.ofSlab L xs) = xs.take 32 := by
    apply List.ext_getElem
    · rw [hkh, List.length_take_of_le hxs]
    · intro i hi1 _hi2
      have hi32 : i < 32 := by rw [hkh] at hi1; exact hi1
      simp only [k6HdrWords, K6State.ofSlab]
      by_cases h25 : i < 25
      · have hix : i < xs.length := by omega
        rw [List.getElem_take]
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨
          i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨
          i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [List.getElem?_eq_getElem hix]
      · rw [List.getElem_take, List.getElem_append_right (by simp; omega)]
        simp [List.getElem_take, List.getElem_drop, show 25 + (i - 25) = i by omega]
  have t16 := k6_slice_append_eq xs (a := L.oClSz) (b := L.maxCl) (c := L.oArena)
    (by unfold K6Layout.oArena K6Layout.oClSz K6Layout.maxCl; omega)
  have t15 := k6_slice_append_eq xs (a := L.oClOff) (b := L.maxCl) (c := L.oClSz)
    (by unfold K6Layout.oClSz K6Layout.oClOff K6Layout.maxCl; omega)
  have t14 := k6_slice_append_eq xs (a := L.oWBlit) (b := 2 * L.maxCl) (c := L.oClOff)
    (by unfold K6Layout.oClOff K6Layout.oWBlit K6Layout.maxCl; omega)
  have t13 := k6_slice_append_eq xs (a := L.oWNext) (b := 2 * L.maxCl) (c := L.oWBlit)
    (by unfold K6Layout.oWBlit K6Layout.oWNext K6Layout.maxCl; omega)
  have t12 := k6_slice_append_eq xs (a := L.oWHead) (b := 2 * L.maxV) (c := L.oWNext)
    (by unfold K6Layout.oWNext K6Layout.oWHead; omega)
  have t11 := k6_slice_append_eq xs (a := L.oVals) (b := 2 * L.maxV) (c := L.oWHead)
    (by unfold K6Layout.oWHead K6Layout.oVals; omega)
  have t10 := k6_slice_append_eq xs (a := L.oAssump) (b := L.maxV) (c := L.oVals)
    (by unfold K6Layout.oVals K6Layout.oAssump; omega)
  have t9 := k6_slice_append_eq xs (a := L.oKl) (b := L.maxV) (c := L.oAssump)
    (by unfold K6Layout.oAssump K6Layout.oKl; omega)
  have t8 := k6_slice_append_eq xs (a := L.oAna) (b := L.maxV) (c := L.oKl)
    (by unfold K6Layout.oKl K6Layout.oAna; omega)
  have t7 := k6_slice_append_eq xs (a := L.oFlags) (b := L.maxV) (c := L.oAna)
    (by unfold K6Layout.oAna K6Layout.oFlags; omega)
  have t6 := k6_slice_append_eq xs (a := L.oTrl) (b := L.maxV) (c := L.oFlags)
    (by unfold K6Layout.oFlags K6Layout.oTrl; omega)
  have t5 := k6_slice_append_eq xs (a := L.oQStamp) (b := L.maxV) (c := L.oTrl)
    (by unfold K6Layout.oTrl K6Layout.oQStamp; omega)
  have t4 := k6_slice_append_eq xs (a := L.oQNext) (b := L.maxV) (c := L.oQStamp)
    (by unfold K6Layout.oQStamp K6Layout.oQNext; omega)
  have t3 := k6_slice_append_eq xs (a := L.oQPrev) (b := L.maxV) (c := L.oQNext)
    (by unfold K6Layout.oQNext K6Layout.oQPrev; omega)
  have t2 := k6_slice_append_eq xs (a := L.oRsn) (b := L.maxV) (c := L.oQPrev)
    (by unfold K6Layout.oQPrev K6Layout.oRsn; omega)
  have t1 := k6_slice_append_eq xs (a := L.oLvl) (b := L.maxV) (c := L.oRsn)
    (by unfold K6Layout.oRsn K6Layout.oLvl; omega)
  unfold K6State.toSlab
  conv =>
    lhs; rhs
    simp only [K6State.ofSlab]
  rw [h0, t16, t15, t14, t13, t12, t11, t10, t9, t8, t7, t6, t5, t4, t3, t2, t1]
  unfold K6Layout.oLvl
  exact List.take_append_drop 32 xs

theorem K6State.ofSlab_toSlab {L : K6Layout} {ks : K6State} (h : ks.ShapesOk L) :
    K6State.ofSlab L ks.toSlab = ks := by
  have hkh : (k6HdrWords ks).length = 32 := k6HdrWords_length h
  rcases h with ⟨hht, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
  let xs := ks.toSlab
  have hd0 : xs.drop 0 = k6HdrWords ks ++ (ks.lvlArr ++ (ks.rsn ++ (ks.qprev ++ (ks.qnext ++
    (ks.qstampArr ++ (ks.trl ++ (ks.flags ++ (ks.ana ++ (ks.kl ++ (ks.assump ++ (ks.vals ++
    (ks.whead ++ (ks.wnext ++ (ks.wblit ++ (ks.clOff ++ (ks.clSz ++ ks.arena)))))))))))))))) := rfl
  have hd1 := k6_drop_step L.oLvl hd0 hkh rfl
  have hd2 := k6_drop_step L.oRsn hd1 h1 (by unfold K6Layout.oRsn K6Layout.oLvl; omega)
  have hd3 := k6_drop_step L.oQPrev hd2 h2 (by unfold K6Layout.oQPrev K6Layout.oRsn; omega)
  have hd4 := k6_drop_step L.oQNext hd3 h3 (by unfold K6Layout.oQNext K6Layout.oQPrev; omega)
  have hd5 := k6_drop_step L.oQStamp hd4 h4 (by unfold K6Layout.oQStamp K6Layout.oQNext; omega)
  have hd6 := k6_drop_step L.oTrl hd5 h5 (by unfold K6Layout.oTrl K6Layout.oQStamp; omega)
  have hd7 := k6_drop_step L.oFlags hd6 h6 (by unfold K6Layout.oFlags K6Layout.oTrl; omega)
  have hd8 := k6_drop_step L.oAna hd7 h7 (by unfold K6Layout.oAna K6Layout.oFlags; omega)
  have hd9 := k6_drop_step L.oKl hd8 h8 (by unfold K6Layout.oKl K6Layout.oAna; omega)
  have hd10 := k6_drop_step L.oAssump hd9 h9 (by unfold K6Layout.oAssump K6Layout.oKl; omega)
  have hd11 := k6_drop_step L.oVals hd10 h10 (by unfold K6Layout.oVals K6Layout.oAssump; omega)
  have hd12 := k6_drop_step L.oWHead hd11 h11 (by unfold K6Layout.oWHead K6Layout.oVals; omega)
  have hd13 := k6_drop_step L.oWNext hd12 h12 (by unfold K6Layout.oWNext K6Layout.oWHead; omega)
  have hd14 := k6_drop_step L.oWBlit hd13 h13
    (by unfold K6Layout.oWBlit K6Layout.oWNext K6Layout.maxCl; omega)
  have hd15 := k6_drop_step L.oClOff hd14 h14
    (by unfold K6Layout.oClOff K6Layout.oWBlit K6Layout.maxCl; omega)
  have hd16 := k6_drop_step L.oClSz hd15 h15
    (by unfold K6Layout.oClSz K6Layout.oClOff K6Layout.maxCl; omega)
  have hd17 := k6_drop_step L.oArena hd16 h16
    (by unfold K6Layout.oArena K6Layout.oClSz K6Layout.maxCl; omega)
  have hpfx : (xs.drop 0).take 32 = k6HdrWords ks := k6_take_prefix hd0 hkh
  have hht' : (xs.drop 25).take 7 = ks.hdrTail := by
    have htk : xs.take 32 = k6HdrWords ks := by simpa using hpfx
    rw [List.take_drop, show 25 + 7 = 32 from rfl, htk, k6HdrWords,
      List.drop_append_of_le_length (by simp)]
    simp
  cases ks; unfold K6State.ofSlab; congr 1
  all_goals first
    | exact hht'
    | exact k6_take_prefix hd1 h1
    | exact k6_take_prefix hd2 h2
    | exact k6_take_prefix hd3 h3
    | exact k6_take_prefix hd4 h4
    | exact k6_take_prefix hd5 h5
    | exact k6_take_prefix hd6 h6
    | exact k6_take_prefix hd7 h7
    | exact k6_take_prefix hd8 h8
    | exact k6_take_prefix hd9 h9
    | exact k6_take_prefix hd10 h10
    | exact k6_take_prefix hd11 h11
    | exact k6_take_prefix hd12 h12
    | exact k6_take_prefix hd13 h13
    | exact k6_take_prefix hd14 h14
    | exact k6_take_prefix hd15 h15
    | exact k6_take_prefix hd16 h16
    | exact hd17
    | (dsimp only [xs, K6State.toSlab, k6HdrWords]
       simp only [List.append_assoc, List.cons_append, List.nil_append]
       simp)

end LeanQbe.T.Examples.Kissat.Proof.Kitten

end
