module

public import LeanQbe.T.Examples.Kissat.FullM6Sweep
public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.FullSpec3
public import LeanQbe.T.Examples.Kissat.FullM4SweepSpec
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb
public import LeanQbe.T.Logic.SepTree

/-!
# Kissat `D-Full` M6 Sweep — Specs, Dynamic `K6Layout`, `K6Tree`, & Invariants

1. `k6MaxV`, `K6Layout`, `k6LayoutOfCap` (dynamic scaling inside `scratch_buf`, `24576 ≤ cap`),
   and pointer-base normalization lemmas.
2. `K6State`, `K6State.ShapesOk L`, slab round-trip (`toSlab_ofSlab`, `ofSlab_toSlab`), balanced
   `18`-leaf `K6Tree L kPtr ks`, `K6Mem`, `K6MemA`, `FullK6Frame`, and strictly scoped
   `K6MemATactics`.
3. Semantic invariants: `K6Inv L P ks`, `K6WatchesOk` (with inline `K6_BIN_FLAG` invariant),
   `K6ScratchInv P scr`, `M6TmkZero`, `M6SweepConeOk`, `M6PhtOk`, `M6PartitionOk`,
   `M6EqBufOk`, and `M6ReprFlatInv`.
4. All `51` UNSAT-only `Spec` contracts (`39` owned + `12` canonical `Full` externs),
   `m6SweepSpecTable`, and `m6SweepEnv`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Sweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Sweep
open Kraken.Bedrock2.Test

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
  unfold k6MaxV; simp [h]

theorem k6MaxV_bounds {cap : Nat} (hge : k6MinScr ≤ cap) :
    512 ≤ k6MaxV cap ∧ k6MaxV cap ≤ 8192 ∧ 1312 + 45 * k6MaxV cap ≤ cap := by
  unfold k6MaxV k6MinScr k6MaxVCap at *
  have hnot : ¬ cap < 24576 := by omega
  simp only [hnot, ↓reduceIte]
  split
  · exact ⟨by decide, by decide, by omega⟩
  · have hq : 516 ≤ (cap - 1312) / 45 := by omega
    have h45 : 45 * ((cap - 1312) / 45) ≤ cap - 1312 := Nat.mul_div_le (cap - 1312) 45
    have hmod : ((cap - 1312) / 45) / 64 * 64 ≤ (cap - 1312) / 45 := by omega
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
      have hraw : (((BitVec.ofNat 64 cap - 1312#64) / 45#64) &&& 0xFFFFFFFFFFFFFFC0#64).toNat =
          ((cap - 1312) / 45) / 64 * 64 := by
        rw [bv64_and_not63, hdiv]
      apply BitVec.eq_of_toNat_eq
      by_cases hr1 : ((cap - 1312) / 45) / 64 * 64 < 512
      · have hb :
            (((BitVec.ofNat 64 cap - 1312#64) / 45#64) &&& 0xFFFFFFFFFFFFFFC0#64) < 512#64 := by
          change (((BitVec.ofNat 64 cap - 1312#64) / 45#64) &&& 0xFFFFFFFFFFFFFFC0#64).toNat < 512
          rw [hraw]; exact hr1
        simp only [hb, ↓reduceIte]
        rw [show max 512 (min 8192 (((cap - 1312) / 45) / 64 * 64)) = 512 by omega]
      · have hb :
            ¬ (((BitVec.ofNat 64 cap - 1312#64) / 45#64) &&& 0xFFFFFFFFFFFFFFC0#64) < 512#64 := by
          change ¬ (((BitVec.ofNat 64 cap - 1312#64) / 45#64) &&& 0xFFFFFFFFFFFFFFC0#64).toNat < 512
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
  have hb := k6MaxV_bounds hge
  { maxV := mv
    acap := cap - (1312 + 40 * mv)
    hmaxV := ⟨hb.1, hb.2.1⟩
    hacap := ⟨by omega, by omega⟩ }

theorem k6LayoutOfCap_scrLen {cap : Nat} (hge : k6MinScr ≤ cap) (hlt : cap < dimacsBound) :
    (k6LayoutOfCap cap hge hlt).scrLen = cap := by
  have hb := k6MaxV_bounds hge
  unfold K6Layout.scrLen K6Layout.k6Base K6Layout.k6Fixed k6LayoutOfCap; dsimp only; omega

theorem k6_bv32_div2_lt {nv : Nat} {l : BitVec 32} (hl : l.toNat < 2 * nv) :
    (l >>> (1 : Nat)).toNat = l.toNat / 2 ∧ (l >>> (1 : Nat)).toNat < nv := by
  have h1 : (l >>> (1 : Nat)).toNat = l.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact ⟨h1, by omega⟩

theorem k6_bv32_xor1_lt {nv : Nat} {l : BitVec 32} (hl : l.toNat < 2 * nv) :
    (l ^^^ 1#32).toNat = litNeg l.toNat ∧ (l ^^^ 1#32).toNat < 2 * nv := by
  have h1 : (l ^^^ 1#32).toNat = l.toNat ^^^ 1 := by simp
  have h2 : l.toNat ^^^ 1 = litNeg l.toNat := rfl
  refine ⟨h1.trans h2, ?_⟩; rw [h1, h2, litNeg_eq]; split <;> omega

theorem k6_bv32_cid_w0 {nc : Nat} {cid : BitVec 32} (hc : cid.toNat < nc) (hnc : nc ≤ 32768) :
    (cid <<< (1 : Nat)).toNat = 2 * cid.toNat ∧ (cid <<< (1 : Nat)).toNat < 2 * nc := by
  have hshl : (cid <<< (1 : Nat)).toNat = 2 * cid.toNat := by bv_omega
  exact ⟨hshl, by omega⟩

theorem k6_bv32_cid_w1 {nc : Nat} {cid : BitVec 32} (hc : cid.toNat < nc) (hnc : nc ≤ 32768) :
    ((cid <<< (1 : Nat)) ||| 1#32).toNat = 2 * cid.toNat + 1 ∧
      ((cid <<< (1 : Nat)) ||| 1#32).toNat < 2 * nc := by
  have hsh : cid <<< (1 : Nat) = BitVec.ofNat 32 (2 * cid.toNat) := by bv_omega
  have h1 : BitVec.ofNat 32 (2 * cid.toNat) ||| 1#32 = BitVec.ofNat 32 (2 * cid.toNat + 1) := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and,
      show (1#32).getLsbD i = decide (i = 0) by cases i <;> simp]
    cases i with
    | zero => simp [Nat.testBit_zero]
    | succ k => simp [Nat.testBit_succ, show (2 * cid.toNat + 1) / 2 = cid.toNat by omega]
  have hor : ((cid <<< (1 : Nat)) ||| 1#32).toNat = 2 * cid.toNat + 1 := by
    rw [hsh, h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact ⟨hor, by omega⟩

theorem k6_ptr_nat_mul4 (p : BitVec 64) (idx : Nat) (h : idx < 2 ^ 28) :
    p + BitVec.ofNat 64 idx * 4 = p + BitVec.ofNat 64 (4 * idx) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
  congr 1; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), show 4 % 2 ^ 64 = 4 from by decide,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mul_comm]

theorem k6_ptr_base_k6Base (L : K6Layout) (pScr : BitVec 64) :
    pScr + (1280#32 + (L.mv32 <<< (1 : Nat))).setWidth 64 * 4 = L.kPtr pScr := by
  have hm := L.hmaxV
  have heq : (1280#32 + (L.mv32 <<< (1 : Nat))).setWidth 64 * 4 =
      BitVec.ofNat 64 (4 * L.k6Base) := by
    unfold K6Layout.k6Base K6Layout.mv32
    rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_shiftLeft,
      BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), show 4 % 2 ^ 64 = 4 from by decide,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  rw [heq]; rfl

theorem k6_ptr_add_mul (L : K6Layout) (kPtr : BitVec 64) (c : Nat) (hc : c ≤ 38) :
    kPtr + (32#32 + BitVec.ofNat 32 c * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * (32 + c * L.maxV)) := by
  have hm := L.hmaxV
  have hcl : c * L.maxV ≤ 38 * 8192 := Nat.mul_le_mul hc hm.2
  have heq : (32#32 + BitVec.ofNat 32 c * L.mv32).setWidth 64 * 4 =
      BitVec.ofNat 64 (4 * (32 + c * L.maxV)) := by
    unfold K6Layout.mv32
    rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : c < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : L.maxV < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : c * L.maxV < 2 ^ 32),
      show (32 % 2 ^ 32 : Nat) = 32 from by decide,
      Nat.mod_eq_of_lt (by omega : 32 + c * L.maxV < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : 32 + c * L.maxV < 2 ^ 64),
      show (4 % 2 ^ 64 : Nat) = 4 from by decide,
      Nat.mod_eq_of_lt (by omega : (32 + c * L.maxV) * 4 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 4 * (32 + c * L.maxV) < 2 ^ 64)]
    omega
  rw [heq]

theorem k6_ptr_add_1 (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + (32#32 + L.mv32).setWidth 64 * 4 = kPtr + BitVec.ofNat 64 (4 * L.oRsn) := by
  simpa [K6Layout.oRsn, Nat.one_mul] using k6_ptr_add_mul L kPtr 1 (by decide)

theorem k6_ptr_lvl (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + (32#32).setWidth 64 * 4 = kPtr + BitVec.ofNat 64 (4 * L.oLvl) := by
  rw [show (32#32 : BitVec 32).setWidth 64 = BitVec.ofNat 64 32 from rfl]
  exact k6_ptr_nat_mul4 kPtr 32 (by decide)

/-! ## 2. `K6State`, `ShapesOk`, Slab Serialization, & Balanced `K6Tree` -/

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
  [ ks.nv, ks.nc, ks.lvl, ks.prop, ks.trl_end, ks.unass, ks.incons, ks.qfirst, ks.qlast,
    ks.qsearch, ks.qstamp, ks.ticks, ks.tick_lim, ks.alen, ks.acap, ks.nassump, ks.nkl,
    ks.nana, ks.status, ks.phase, ks.openCnt, ks.max_v, ks.max_orig, ks.max_cl, ks.neq ] ++
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
  nv := xs[0]?.getD 0#32; nc := xs[1]?.getD 0#32; lvl := xs[2]?.getD 0#32
  prop := xs[3]?.getD 0#32; trl_end := xs[4]?.getD 0#32; unass := xs[5]?.getD 0#32
  incons := xs[6]?.getD 0#32; qfirst := xs[7]?.getD 0#32; qlast := xs[8]?.getD 0#32
  qsearch := xs[9]?.getD 0#32; qstamp := xs[10]?.getD 0#32; ticks := xs[11]?.getD 0#32
  tick_lim := xs[12]?.getD 0#32; alen := xs[13]?.getD 0#32; acap := xs[14]?.getD 0#32
  nassump := xs[15]?.getD 0#32; nkl := xs[16]?.getD 0#32; nana := xs[17]?.getD 0#32
  status := xs[18]?.getD 0#32; phase := xs[19]?.getD 0#32; openCnt := xs[20]?.getD 0#32
  max_v := xs[21]?.getD 0#32; max_orig := xs[22]?.getD 0#32; max_cl := xs[23]?.getD 0#32
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
      rw [hkh] at hi1
      have hge : i < xs.length := by omega
      simp only [List.getElem_take]
      by_cases h25 : i < 25
      · have hfn : ∀ k : Fin 25,
            (k6HdrWords (K6State.ofSlab L xs))[k.1]'(by rw [hkh]; omega) =
              xs[k.1]'(by have hk := k.isLt; omega) := by
          intro ⟨k, hk⟩
          have hget (j : Nat) (hj : j < 25) : xs[j]?.getD 0#32 = xs[j]'(by omega) := by
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          match k, hk with
          | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _
          | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _
          | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ => exact hget _ (by omega)
          | _ + 25, hk => omega
        exact hfn ⟨i, h25⟩
      · have hlo : 25 ≤ i := by omega
        have hi_lt : i - 25 < 7 := by omega
        simp only [k6HdrWords, K6State.ofSlab]
        rw [List.getElem_append_right (by simp; omega)]
        simp only [List.length_cons, List.length_nil, List.getElem_take, List.getElem_drop]
        congr 1; omega
  have heq : ∀ {a b c : Nat}, c = a + b →
      (xs.drop a).take b ++ xs.drop c = xs.drop a :=
    fun {a b _} hc => by subst hc; exact k6_slice_append xs a b
  have ha1 : L.oArena = L.oClSz + L.maxCl := by
    unfold K6Layout.oArena K6Layout.oClSz K6Layout.maxCl; omega
  have ha2 : L.oClSz = L.oClOff + L.maxCl := by
    unfold K6Layout.oClSz K6Layout.oClOff K6Layout.maxCl; omega
  have ha3 : L.oClOff = L.oWBlit + 2 * L.maxCl := by
    unfold K6Layout.oClOff K6Layout.oWBlit K6Layout.maxCl; omega
  have ha4 : L.oWBlit = L.oWNext + 2 * L.maxCl := by
    unfold K6Layout.oWBlit K6Layout.oWNext K6Layout.maxCl; omega
  simp only [K6State.toSlab, K6State.ofSlab] at h0 ⊢
  rw [h0, heq ha1, heq ha2, heq ha3, heq ha4,
    heq (show L.oWNext = L.oWHead + 2 * L.maxV by unfold K6Layout.oWNext K6Layout.oWHead; omega),
    heq (show L.oWHead = L.oVals + 2 * L.maxV by unfold K6Layout.oWHead K6Layout.oVals; omega),
    heq (show L.oVals = L.oAssump + L.maxV by unfold K6Layout.oVals K6Layout.oAssump; omega),
    heq (show L.oAssump = L.oKl + L.maxV by unfold K6Layout.oAssump K6Layout.oKl; omega),
    heq (show L.oKl = L.oAna + L.maxV by unfold K6Layout.oKl K6Layout.oAna; omega),
    heq (show L.oAna = L.oFlags + L.maxV by unfold K6Layout.oAna K6Layout.oFlags; omega),
    heq (show L.oFlags = L.oTrl + L.maxV by unfold K6Layout.oFlags K6Layout.oTrl; omega),
    heq (show L.oTrl = L.oQStamp + L.maxV by unfold K6Layout.oTrl K6Layout.oQStamp; omega),
    heq (show L.oQStamp = L.oQNext + L.maxV by unfold K6Layout.oQStamp K6Layout.oQNext; omega),
    heq (show L.oQNext = L.oQPrev + L.maxV by unfold K6Layout.oQNext K6Layout.oQPrev; omega),
    heq (show L.oQPrev = L.oRsn + L.maxV by unfold K6Layout.oQPrev K6Layout.oRsn; omega),
    heq (show L.oRsn = L.oLvl + L.maxV by unfold K6Layout.oRsn K6Layout.oLvl; omega),
    show L.oLvl = 32 from rfl, List.take_append_drop]

theorem K6State.ofSlab_toSlab {L : K6Layout} {ks : K6State} (h : ks.ShapesOk L) :
    K6State.ofSlab L ks.toSlab = ks := by
  rcases ks with ⟨nv, nc, lvl, prop, trl_end, unass, incons, qfirst, qlast, qsearch, qstamp,
    ticks, tick_lim, alen, acapF, nassump, nkl, nana, status, phase, openCnt, max_v, max_orig,
    max_cl, neq, hdrTail, lvlArr, rsn, qprev, qnext, qstampArr, trl, flags, ana, kl, assump,
    vals, whead, wnext, wblit, clOff, clSz, arena⟩
  rcases h with ⟨htl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, _⟩
  let L0 := [nv, nc, lvl, prop, trl_end, unass, incons, qfirst, qlast, qsearch, qstamp, ticks,
    tick_lim, alen, acapF, nassump, nkl, nana, status, phase, openCnt, max_v, max_orig, max_cl,
    neq]
  let ts : List (BitVec 32) :=
    (L0 ++ hdrTail) ++ (lvlArr ++ (rsn ++ (qprev ++ (qnext ++ (qstampArr ++ (trl ++ (flags ++
    (ana ++ (kl ++ (assump ++ (vals ++ (whead ++ (wnext ++ (wblit ++ (clOff ++ (clSz ++
    arena))))))))))))))))
  have hd0 : ts.drop L.oLvl = lvlArr ++ (rsn ++ (qprev ++ (qnext ++ (qstampArr ++ (trl ++ (flags ++
      (ana ++ (kl ++ (assump ++ (vals ++ (whead ++ (wnext ++ (wblit ++ (clOff ++ (clSz ++
      arena))))))))))))))) :=
    k6_drop_exact (L0 ++ hdrTail) _
      (by unfold K6Layout.oLvl; simpa [L0, List.length_append] using htl)
  have hd1 := k6_drop_step L.oRsn hd0 h1 (by unfold K6Layout.oRsn K6Layout.oLvl; omega)
  have hd2 := k6_drop_step L.oQPrev hd1 h2 (by unfold K6Layout.oQPrev K6Layout.oRsn; omega)
  have hd3 := k6_drop_step L.oQNext hd2 h3 (by unfold K6Layout.oQNext K6Layout.oQPrev; omega)
  have hd4 := k6_drop_step L.oQStamp hd3 h4 (by unfold K6Layout.oQStamp K6Layout.oQNext; omega)
  have hd5 := k6_drop_step L.oTrl hd4 h5 (by unfold K6Layout.oTrl K6Layout.oQStamp; omega)
  have hd6 := k6_drop_step L.oFlags hd5 h6 (by unfold K6Layout.oFlags K6Layout.oTrl; omega)
  have hd7 := k6_drop_step L.oAna hd6 h7 (by unfold K6Layout.oAna K6Layout.oFlags; omega)
  have hd8 := k6_drop_step L.oKl hd7 h8 (by unfold K6Layout.oKl K6Layout.oAna; omega)
  have hd9 := k6_drop_step L.oAssump hd8 h9 (by unfold K6Layout.oAssump K6Layout.oKl; omega)
  have hd10 := k6_drop_step L.oVals hd9 h10 (by unfold K6Layout.oVals K6Layout.oAssump; omega)
  have hd11 := k6_drop_step L.oWHead hd10 h11 (by unfold K6Layout.oWHead K6Layout.oVals; omega)
  have hd12 := k6_drop_step L.oWNext hd11 h12 (by unfold K6Layout.oWNext K6Layout.oWHead; omega)
  have hd13 := k6_drop_step L.oWBlit hd12 h13
    (by unfold K6Layout.oWBlit K6Layout.oWNext K6Layout.maxCl; omega)
  have hd14 := k6_drop_step L.oClOff hd13 h14
    (by unfold K6Layout.oClOff K6Layout.oWBlit K6Layout.maxCl; omega)
  have hd15 := k6_drop_step L.oClSz hd14 h15
    (by unfold K6Layout.oClSz K6Layout.oClOff K6Layout.maxCl; omega)
  have hd16 := k6_drop_step L.oArena hd15 h16
    (by unfold K6Layout.oArena K6Layout.oClSz K6Layout.maxCl; omega)
  have hht : (ts.drop 25).take 7 = hdrTail := by
    simp only [ts, List.append_assoc]
    rw [List.drop_append_of_le_length (by simp [L0])]
    have hnil : L0.drop 25 = [] := by simp [L0]
    rw [hnil, List.nil_append, List.take_append_of_le_length (by rw [htl]; decide),
      ← htl, List.take_length]
  change K6State.ofSlab L ts = _
  simp only [K6State.ofSlab]
  rw [hht, k6_take_prefix hd0 h1, k6_take_prefix hd1 h2, k6_take_prefix hd2 h3,
    k6_take_prefix hd3 h4, k6_take_prefix hd4 h5, k6_take_prefix hd5 h6, k6_take_prefix hd6 h7,
    k6_take_prefix hd7 h8, k6_take_prefix hd8 h9, k6_take_prefix hd9 h10, k6_take_prefix hd10 h11,
    k6_take_prefix hd11 h12, k6_take_prefix hd12 h13, k6_take_prefix hd13 h14,
    k6_take_prefix hd14 h15, k6_take_prefix hd15 h16, hd16]
  rfl

@[expose] def k6Path (n : Nat) : List Bool :=
  Nat.casesOn n [false, false, false, false] fun n =>
  Nat.casesOn n [false, false, false, true] fun n =>
  Nat.casesOn n [false, false, true, false] fun n =>
  Nat.casesOn n [false, false, true, true] fun n =>
  Nat.casesOn n [false, true, false, false] fun n =>
  Nat.casesOn n [false, true, false, true] fun n =>
  Nat.casesOn n [false, true, true, false] fun n =>
  Nat.casesOn n [false, true, true, true, false] fun n =>
  Nat.casesOn n [false, true, true, true, true] fun n =>
  Nat.casesOn n [true, false, false, false] fun n =>
  Nat.casesOn n [true, false, false, true] fun n =>
  Nat.casesOn n [true, false, true, false] fun n =>
  Nat.casesOn n [true, false, true, true] fun n =>
  Nat.casesOn n [true, true, false, false] fun n =>
  Nat.casesOn n [true, true, false, true] fun n =>
  Nat.casesOn n [true, true, true, false] fun n =>
  Nat.casesOn n [true, true, true, true, false] fun _ =>
    [true, true, true, true, true]

/-- Balanced `18`-leaf `SepTree` over `K6`'s dynamically scaled `u32` slab at `kPtr`. -/
@[expose] def K6Tree (L : K6Layout) (kPtr : BitVec 64) (ks : K6State) : SepTree :=
  let t01 := SepTree.node (.leaf (array (t := i32) kPtr (k6HdrWords ks)))
    (.leaf (array (t := i32) (kPtr + BitVec.ofNat 64 (4 * L.oLvl)) ks.lvlArr))
  let t23 := SepTree.node
    (.leaf (array (t := i32) (kPtr + BitVec.ofNat 64 (4 * L.oRsn)) ks.rsn))
    (.leaf (array (t := i32) (kPtr + BitVec.ofNat 64 (4 * L.oQPrev)) ks.qprev))
  let t45 := SepTree.node
    (.leaf (array (t := i32) (kPtr + BitVec.ofNat 64 (4 * L.oQNext)) ks.qnext))
    (.leaf (array (t := i32) (kPtr + BitVec.ofNat 64 (4 * L.oQStamp)) ks.qstampArr))
  let t78 := SepTree.node
    (.leaf (array (t := i32) (kPtr + BitVec.ofNat 64 (4 * L.oFlags)) ks.flags))
    (.leaf (array (t := i32) (kPtr + BitVec.ofNat 64 (4 * L.oAna)) ks.ana))
  let t68 := SepTree.node
    (.leaf (array (t := i32) (kPtr + BitVec.ofNat 64 (4 * L.oTrl)) ks.trl)) t78
  let t910 := SepTree.node
    (.leaf (array (t := i32) (kPtr + BitVec.ofNat 64 (4 * L.oKl)) ks.kl))
    (.leaf (array (t := i32) (kPtr + BitVec.ofNat 64 (4 * L.oAssump)) ks.assump))
  let t1112 := SepTree.node
    (.leaf (array (t := i32) (kPtr + BitVec.ofNat 64 (4 * L.oVals)) ks.vals))
    (.leaf (array (t := i32) (kPtr + BitVec.ofNat 64 (4 * L.oWHead)) ks.whead))
  let t1314 := SepTree.node
    (.leaf (array (t := i32) (kPtr + BitVec.ofNat 64 (4 * L.oWNext)) ks.wnext))
    (.leaf (array (t := i32) (kPtr + BitVec.ofNat 64 (4 * L.oWBlit)) ks.wblit))
  let t1617 := SepTree.node
    (.leaf (array (t := i32) (kPtr + BitVec.ofNat 64 (4 * L.oClSz)) ks.clSz))
    (.leaf (array (t := i32) (kPtr + BitVec.ofNat 64 (4 * L.oArena)) ks.arena))
  let t1517 := SepTree.node
    (.leaf (array (t := i32) (kPtr + BitVec.ofNat 64 (4 * L.oClOff)) ks.clOff)) t1617
  .node (.node (.node t01 t23) (.node t45 t68)) (.node (.node t910 t1112) (.node t1314 t1517))

@[expose] def K6Mem (L : K6Layout) (kPtr : BitVec 64) (ks : K6State) : Mem 64 → Prop :=
  (K6Tree L kPtr ks).eval

private theorem k6_arr32_append (a off : BitVec 64) (xs ys : List (BitVec 32))
    (hs : a + BitVec.ofNat 64 (4 * xs.length) = off) :
    array (t := i32) a (xs ++ ys) = (array (t := i32) a xs ⋆ array (t := i32) off ys) := by
  rw [array_append, show (i32 : Ty).bytes = 4 from rfl, hs]

theorem k6Mem_eq_array {L : K6Layout} (kPtr : BitVec 64) {ks : K6State} (h : ks.ShapesOk L) :
    K6Mem L kPtr ks = array (t := i32) kPtr ks.toSlab := by
  have hh := k6HdrWords_length h
  rcases h with ⟨_, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, _⟩
  dsimp only [K6Mem, K6Tree, SepTree.eval, K6State.toSlab]
  rw [k6_arr32_append kPtr (kPtr + BitVec.ofNat 64 (4 * L.oLvl)) (k6HdrWords ks) _
    (by rw [hh]; rfl)]
  rw [k6_arr32_append _ (kPtr + BitVec.ofNat 64 (4 * L.oRsn)) ks.lvlArr _
    (by rw [h1, ptr_add_ofNat]; unfold K6Layout.oLvl K6Layout.oRsn; congr 2; omega)]
  rw [k6_arr32_append _ (kPtr + BitVec.ofNat 64 (4 * L.oQPrev)) ks.rsn _
    (by rw [h2, ptr_add_ofNat]; unfold K6Layout.oRsn K6Layout.oQPrev; congr 2; omega)]
  rw [k6_arr32_append _ (kPtr + BitVec.ofNat 64 (4 * L.oQNext)) ks.qprev _
    (by rw [h3, ptr_add_ofNat]; unfold K6Layout.oQPrev K6Layout.oQNext; congr 2; omega)]
  rw [k6_arr32_append _ (kPtr + BitVec.ofNat 64 (4 * L.oQStamp)) ks.qnext _
    (by rw [h4, ptr_add_ofNat]; unfold K6Layout.oQNext K6Layout.oQStamp; congr 2; omega)]
  rw [k6_arr32_append _ (kPtr + BitVec.ofNat 64 (4 * L.oTrl)) ks.qstampArr _
    (by rw [h5, ptr_add_ofNat]; unfold K6Layout.oQStamp K6Layout.oTrl; congr 2; omega)]
  rw [k6_arr32_append _ (kPtr + BitVec.ofNat 64 (4 * L.oFlags)) ks.trl _
    (by rw [h6, ptr_add_ofNat]; unfold K6Layout.oTrl K6Layout.oFlags; congr 2; omega)]
  rw [k6_arr32_append _ (kPtr + BitVec.ofNat 64 (4 * L.oAna)) ks.flags _
    (by rw [h7, ptr_add_ofNat]; unfold K6Layout.oFlags K6Layout.oAna; congr 2; omega)]
  rw [k6_arr32_append _ (kPtr + BitVec.ofNat 64 (4 * L.oKl)) ks.ana _
    (by rw [h8, ptr_add_ofNat]; unfold K6Layout.oAna K6Layout.oKl; congr 2; omega)]
  rw [k6_arr32_append _ (kPtr + BitVec.ofNat 64 (4 * L.oAssump)) ks.kl _
    (by rw [h9, ptr_add_ofNat]; unfold K6Layout.oKl K6Layout.oAssump; congr 2; omega)]
  rw [k6_arr32_append _ (kPtr + BitVec.ofNat 64 (4 * L.oVals)) ks.assump _
    (by rw [h10, ptr_add_ofNat]; unfold K6Layout.oAssump K6Layout.oVals; congr 2; omega)]
  rw [k6_arr32_append _ (kPtr + BitVec.ofNat 64 (4 * L.oWHead)) ks.vals _
    (by rw [h11, ptr_add_ofNat]; unfold K6Layout.oVals K6Layout.oWHead; congr 2; omega)]
  rw [k6_arr32_append _ (kPtr + BitVec.ofNat 64 (4 * L.oWNext)) ks.whead _
    (by rw [h12, ptr_add_ofNat]; unfold K6Layout.oWHead K6Layout.oWNext; congr 2; omega)]
  rw [k6_arr32_append _ (kPtr + BitVec.ofNat 64 (4 * L.oWBlit)) ks.wnext _
    (by rw [h13, ptr_add_ofNat]; unfold K6Layout.oWNext K6Layout.oWBlit K6Layout.maxCl
        congr 2; omega)]
  rw [k6_arr32_append _ (kPtr + BitVec.ofNat 64 (4 * L.oClOff)) ks.wblit _
    (by rw [h14, ptr_add_ofNat]; unfold K6Layout.oWBlit K6Layout.oClOff K6Layout.maxCl
        congr 2; omega)]
  rw [k6_arr32_append _ (kPtr + BitVec.ofNat 64 (4 * L.oClSz)) ks.clOff _
    (by rw [h15, ptr_add_ofNat]; unfold K6Layout.oClOff K6Layout.oClSz K6Layout.maxCl
        congr 2; omega)]
  rw [k6_arr32_append _ (kPtr + BitVec.ofNat 64 (4 * L.oArena)) ks.clSz _
    (by rw [h16, ptr_add_ofNat]; unfold K6Layout.oClSz K6Layout.oArena K6Layout.maxCl
        congr 2; omega)]
  ac_rfl

theorem array_scratch_eq_k6 {L : K6Layout} {p : BitVec 64} {scr : List (BitVec 32)}
    (hlen : scr.length = L.scrLen) :
    array (t := i32) p scr =
      (array (t := i32) p (scr.take L.k6Base) ⋆
        K6Mem L (L.kPtr p) (K6State.ofSlab L (scr.drop L.k6Base))) := by
  have hle : L.k6Fixed ≤ (scr.drop L.k6Base).length := by
    rw [List.length_drop, hlen]; unfold K6Layout.scrLen; omega
  have hsh := K6State.shapesOk_ofSlab_eq (L := L) (xs := scr.drop L.k6Base) (by
    rw [List.length_drop, hlen]; unfold K6Layout.scrLen; omega)
  rw [k6Mem_eq_array (L.kPtr p) hsh, K6State.toSlab_ofSlab hle]
  have htk : (scr.take L.k6Base).length = L.k6Base :=
    List.length_take_of_le (by rw [hlen]; unfold K6Layout.scrLen; omega)
  have happ := k6_arr32_append p (L.kPtr p) (scr.take L.k6Base) (scr.drop L.k6Base)
    (by rw [htk]; rfl)
  rwa [List.take_append_drop] at happ

theorem k6_append_eq_array_scratch {L : K6Layout} {p : BitVec 64} {scrHead : List (BitVec 32)}
    {ks : K6State} (hh : scrHead.length = L.k6Base) (hsh : ks.ShapesOk L) :
    (array (t := i32) p scrHead ⋆ K6Mem L (L.kPtr p) ks) =
      array (t := i32) p (scrHead ++ ks.toSlab) := by
  rw [k6Mem_eq_array (L.kPtr p) hsh]
  exact (k6_arr32_append p (L.kPtr p) scrHead ks.toSlab (by rw [hh]; rfl)).symm

@[expose] def FullK6Frame (c : FullCfg) (L : K6Layout) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
  FullScrMetaArrs c s.scratch ⋆ array (t := i32) c.pDelayed s.scratch.delayed ⋆
  array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
  array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
  array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take L.k6Base) ⋆ c.pad

theorem fullMem_eq_k6Frame {c : FullCfg} {L : K6Layout} {s : FullState}
    (hlen : s.scratch.scratch_buf.length = L.scrLen) :
    FullMem c s = (FullK6Frame c L s ⋆
      K6Mem L (L.kPtr c.pScratchBuf)
        (K6State.ofSlab L (s.scratch.scratch_buf.drop L.k6Base))) := by
  unfold FullMem FullScratchArrays FullScrDynArrs FullK6Frame
  rw [array_scratch_eq_k6 hlen]; ac_rfl

theorem fullMem_join_k6 {c : FullCfg} {L : K6Layout} {s : FullState} {ks' : K6State}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hkbase : L.k6Base ≤ s.scratch.scratch_buf.length) (hsh : ks'.ShapesOk L)
    (hm : (FullK6Frame c L s ⋆ K6Mem L (L.kPtr c.pScratchBuf) ks' ⋆ R) m) :
    let scr' := s.scratch.scratch_buf.take L.k6Base ++ ks'.toSlab
    let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
    (FullMem c s' ⋆ R) m := by
  intro scr' s'
  have htk : (s.scratch.scratch_buf.take L.k6Base).length = L.k6Base :=
    List.length_take_of_le hkbase
  have h1 : (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆
      array64 (c.hdr + 32) (Full.hdrTailWords c s') ⋆ FullCoreArrays c s.core ⋆
      FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
      FullScrMetaArrs c s.scratch ⋆ array (t := i32) c.pDelayed s.scratch.delayed ⋆
      array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
      array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
      (array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take L.k6Base) ⋆
        K6Mem L (L.kPtr c.pScratchBuf) ks') ⋆ c.pad ⋆ R) m := by
    have hhdr : Full.hdrTailWords c s' = Full.hdrTailWords c s := rfl
    rw [hhdr]; unfold FullK6Frame at hm; exact sep_ac hm
  rw [k6_append_eq_array_scratch htk hsh] at h1
  unfold FullMem FullScratchArrays FullScrDynArrs; exact sep_ac h1

private theorem fullK6Frame_hdrGet {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (i : Nat) (hi : i < 140)
    (hm : (FullK6Frame c L s ⋆ R) m) :
    loadVal m i64 (c.hdr + BitVec.ofNat 64 (32 + 8 * i)) =
      some ((Full.hdrTailWords c s)[i]'(by rw [Full.hdrTailWords_length]; exact hi)) := by
  have h1 : (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
       FullCoreArrays c s.core ⋆ FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
       FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
       array (t := i32) c.pDelayed s.scratch.delayed ⋆
       array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
       array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
       array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take L.k6Base) ⋆ c.pad ⋆ R)) m := by
    unfold FullK6Frame at hm; exact sep_ac hm
  have hl := loadVal_array64 (i := i) (by rw [Full.hdrTailWords_length]; exact hi) h1
  rwa [show c.hdr + (32 : BitVec 64) + BitVec.ofNat 64 (8 * i) =
    c.hdr + BitVec.ofNat 64 (32 + 8 * i) from ptr_add_ofNat c.hdr 32 (8 * i)] at hl

theorem fullK6Frame_fuel_store {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64) (hm : (FullK6Frame c L s ⋆ R) m) :
    storeOk m i64 (c.hdr + 168) ∧
      (FullK6Frame c L { s with core := { s.core with fuel := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 168) v) := by
  have h1 : (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
       FullCoreArrays c s.core ⋆ FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
       FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
       array (t := i32) c.pDelayed s.scratch.delayed ⋆
       array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
       array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
       array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take L.k6Base) ⋆ c.pad ⋆ R)) m := by
    unfold FullK6Frame at hm; exact sep_ac hm
  obtain ⟨hok, hst⟩ := store_array64 (i := 17) v (by rw [Full.hdrTailWords_length]; decide) h1
  rw [show c.hdr + 32 + BitVec.ofNat 64 (8 * 17) = c.hdr + 168 from
    ptr_add_ofNat c.hdr 32 136] at hok hst
  have hset : (Full.hdrTailWords c s).set 17 v =
      Full.hdrTailWords c { s with core := { s.core with fuel := v } } := by
    simp [Full.hdrTailWords, hdrTailWords0, hdrTailWords1, hdrTailWords2, hdrTailWords3, List.set]
  rw [hset] at hst; unfold FullK6Frame; exact ⟨hok, sep_ac hst⟩

/-! ## 3. Non-Expanding `putHdr`/`putArr`, `K6MemA`, & Scoped Tactics -/

inductive K6HdrField where
  | nv | nc | lvl | prop | trl_end | unass | incons | qfirst | qlast | qsearch | qstamp
  | ticks | tick_lim | alen | acap | nassump | nkl | nana | status | phase
  | openCnt | max_v | max_orig | max_cl | neq
  deriving DecidableEq

inductive K6ArrField where
  | lvlArr | rsn | qprev | qnext | qstampArr | trl | flags | ana | kl | assump
  | vals | whead | wnext | wblit | clOff | clSz | arena
  deriving DecidableEq

@[expose] def K6State.putHdr (ks : K6State) (f : K6HdrField) (v : BitVec 32) : K6State :=
  K6HdrField.casesOn (motive := fun _ => K6State) f
    { ks with nv := v } { ks with nc := v } { ks with lvl := v }
    { ks with prop := v } { ks with trl_end := v } { ks with unass := v }
    { ks with incons := v } { ks with qfirst := v } { ks with qlast := v }
    { ks with qsearch := v } { ks with qstamp := v } { ks with ticks := v }
    { ks with tick_lim := v } { ks with alen := v } { ks with acap := v }
    { ks with nassump := v } { ks with nkl := v } { ks with nana := v }
    { ks with status := v } { ks with phase := v } { ks with openCnt := v }
    { ks with max_v := v } { ks with max_orig := v } { ks with max_cl := v }
    { ks with neq := v }

@[expose] def K6State.putArr (ks : K6State) (f : K6ArrField) (i : Nat) (v : BitVec 32) : K6State :=
  K6ArrField.casesOn (motive := fun _ => K6State) f
    { ks with lvlArr := ks.lvlArr.set i v }
    { ks with rsn := ks.rsn.set i v }
    { ks with qprev := ks.qprev.set i v }
    { ks with qnext := ks.qnext.set i v }
    { ks with qstampArr := ks.qstampArr.set i v }
    { ks with trl := ks.trl.set i v }
    { ks with flags := ks.flags.set i v }
    { ks with ana := ks.ana.set i v }
    { ks with kl := ks.kl.set i v }
    { ks with assump := ks.assump.set i v }
    { ks with vals := ks.vals.set i v }
    { ks with whead := ks.whead.set i v }
    { ks with wnext := ks.wnext.set i v }
    { ks with wblit := ks.wblit.set i v }
    { ks with clOff := ks.clOff.set i v }
    { ks with clSz := ks.clSz.set i v }
    { ks with arena := ks.arena.set i v }

theorem K6State.ShapesOk.putHdr {L : K6Layout} {ks : K6State}
    (h : ks.ShapesOk L) (f : K6HdrField) (v : BitVec 32) :
    (ks.putHdr f v).ShapesOk L := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
  cases f <;> exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

theorem K6State.ShapesOk.putArr {L : K6Layout} {ks : K6State}
    (h : ks.ShapesOk L) (f : K6ArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).ShapesOk L := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
  cases f <;> refine ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simpa [K6State.putArr]

theorem k6State_ext {a b : K6State}
    (h1 : a.nv = b.nv) (h2 : a.nc = b.nc) (h3 : a.lvl = b.lvl) (h4 : a.prop = b.prop)
    (h5 : a.trl_end = b.trl_end) (h6 : a.unass = b.unass) (h7 : a.incons = b.incons)
    (h8 : a.qfirst = b.qfirst) (h9 : a.qlast = b.qlast) (h10 : a.qsearch = b.qsearch)
    (h11 : a.qstamp = b.qstamp) (h12 : a.ticks = b.ticks) (h13 : a.tick_lim = b.tick_lim)
    (h14 : a.alen = b.alen) (h15 : a.acap = b.acap) (h16 : a.nassump = b.nassump)
    (h17 : a.nkl = b.nkl) (h18 : a.nana = b.nana) (h19 : a.status = b.status)
    (h20 : a.phase = b.phase) (h21 : a.openCnt = b.openCnt) (h22 : a.max_v = b.max_v)
    (h23 : a.max_orig = b.max_orig) (h24 : a.max_cl = b.max_cl) (h25 : a.neq = b.neq)
    (h26 : a.hdrTail = b.hdrTail) (h27 : a.lvlArr = b.lvlArr) (h28 : a.rsn = b.rsn)
    (h29 : a.qprev = b.qprev) (h30 : a.qnext = b.qnext) (h31 : a.qstampArr = b.qstampArr)
    (h32 : a.trl = b.trl) (h33 : a.flags = b.flags) (h34 : a.ana = b.ana) (h35 : a.kl = b.kl)
    (h36 : a.assump = b.assump) (h37 : a.vals = b.vals) (h38 : a.whead = b.whead)
    (h39 : a.wnext = b.wnext) (h40 : a.wblit = b.wblit) (h41 : a.clOff = b.clOff)
    (h42 : a.clSz = b.clSz) (h43 : a.arena = b.arena) : a = b := by
  cases a; cases b; simp only [K6State.mk.injEq]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38,
    h39, h40, h41, h42, h43⟩

@[expose] def K6MemA (L : K6Layout) (kPtr : BitVec 64) (ks : K6State) : Mem 64 → Prop :=
  fun m => K6Mem L kPtr ks m ∧ ks.ShapesOk L

theorem k6Mem_to_amem {L : K6Layout} {kPtr : BitVec 64} {ks : K6State} {R : Mem 64 → Prop}
    {m : Mem 64} (hsh : ks.ShapesOk L) (hm : (K6Mem L kPtr ks ⋆ R) m) :
    (K6MemA L kPtr ks ⋆ R) m :=
  sep_mono (fun _ h => ⟨h, hsh⟩) hm

theorem k6MemA_to_mem {L : K6Layout} {kPtr : BitVec 64} {ks : K6State} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (K6MemA L kPtr ks ⋆ R) m) :
    ks.ShapesOk L ∧ (K6Mem L kPtr ks ⋆ R) m :=
  sep_pure_l.mp (sep_mono (fun _ ⟨h1, h2⟩ => ⟨h2, h1⟩) hm)

private theorem k6HdrGet {L : K6Layout} {kPtr : BitVec 64} {ks : K6State} {R : Mem 64 → Prop}
    {m : Mem 64} (idx : Nat) (hlt : idx < 32) (v : BitVec 32)
    (heq : ∀ hsh : ks.ShapesOk L,
      (k6HdrWords ks)[idx]'(by rw [k6HdrWords_length hsh]; exact hlt) = v)
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 idx * 4) = some v := by
  obtain ⟨hsh, hm'⟩ := k6MemA_to_mem hm
  have hi : idx < (k6HdrWords ks).length := by rw [k6HdrWords_length hsh]; exact hlt
  rw [k6_ptr_nat_mul4 kPtr idx (by omega), ← heq hsh]
  exact sepTree_arr_get (t := K6Tree L kPtr ks) (p := k6Path 0) rfl (by decide) hi hm'

private theorem k6HdrPut {L : K6Layout} {kPtr : BitVec 64} {ks : K6State} {R : Mem 64 → Prop}
    {m : Mem 64} (f : K6HdrField) (idx : Nat) (v : BitVec 32) (hlt : idx < 32)
    (hset : (k6HdrWords ks).set idx v = k6HdrWords (ks.putHdr f v))
    (heq : ((K6Tree L kPtr ks).set (k6Path 0)
      (array (t := i32) kPtr (k6HdrWords (ks.putHdr f v)))).eval = K6Mem L kPtr (ks.putHdr f v))
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 idx * 4) ∧
      (K6MemA L kPtr (ks.putHdr f v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 idx * 4) v) := by
  obtain ⟨hsh, hm'⟩ := k6MemA_to_mem hm
  have hi : idx < (k6HdrWords ks).length := by rw [k6HdrWords_length hsh]; exact hlt
  rw [k6_ptr_nat_mul4 kPtr idx (by omega)]
  obtain ⟨hok, hst⟩ := sepTree_arr_put (t := K6Tree L kPtr ks) (p := k6Path 0) rfl (by decide) v hi
    (hset ▸ heq) hm'
  exact ⟨hok, k6Mem_to_amem (hsh.putHdr f v) hst⟩

private theorem k6ArrGetBase {L : K6Layout} {kPtr : BitVec 64} {ks : K6State} (p : List Bool)
    (kOff n : Nat) (xs : List (BitVec 32)) {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : ks.ShapesOk L → xs.length = n)
    (hget : (K6Tree L kPtr ks).get p = array (t := i32) (kPtr + BitVec.ofNat 64 (4 * kOff)) xs)
    {i : BitVec 32} (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < n)
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    loadVal m i32 ((kPtr + BitVec.ofNat 64 (4 * kOff)) + i.setWidth 64 * 4) =
      some (xs[i.toNat]?.getD 0#32) := by
  obtain ⟨hsh, hm'⟩ := k6MemA_to_mem hm
  have hi' : i.toNat < xs.length := by rw [hlen hsh]; exact hi
  rw [List.getElem?_eq_getElem hi', Option.getD_some,
    show i.setWidth 64 = BitVec.ofNat 64 i.toNat from by apply BitVec.eq_of_toNat_eq; simp,
    k6_ptr_nat_mul4 _ i.toNat hlt]
  exact sepTree_arr_get (t := K6Tree L kPtr ks) (p := p) hget (by decide) hi' hm'

private theorem k6ArrPutBase {L : K6Layout} {kPtr : BitVec 64} {ks : K6State} (p : List Bool)
    (f : K6ArrField) (kOff n : Nat) (xs : List (BitVec 32)) {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : ks.ShapesOk L → xs.length = n)
    (hget : (K6Tree L kPtr ks).get p = array (t := i32) (kPtr + BitVec.ofNat 64 (4 * kOff)) xs)
    (v : BitVec 32) {i : BitVec 32} (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < n)
    (heq : ((K6Tree L kPtr ks).set p
      (array (t := i32) (kPtr + BitVec.ofNat 64 (4 * kOff)) (xs.set i.toNat v))).eval =
      K6Mem L kPtr (ks.putArr f i.toNat v))
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 ((kPtr + BitVec.ofNat 64 (4 * kOff)) + i.setWidth 64 * 4) ∧
      (K6MemA L kPtr (ks.putArr f i.toNat v) ⋆ R)
        (storeMem m i32 ((kPtr + BitVec.ofNat 64 (4 * kOff)) + i.setWidth 64 * 4) v) := by
  obtain ⟨hsh, hm'⟩ := k6MemA_to_mem hm
  have hi' : i.toNat < xs.length := by rw [hlen hsh]; exact hi
  rw [show i.setWidth 64 = BitVec.ofNat 64 i.toNat from by apply BitVec.eq_of_toNat_eq; simp,
    k6_ptr_nat_mul4 _ i.toNat hlt]
  obtain ⟨hok, hst⟩ := sepTree_arr_put (t := K6Tree L kPtr ks) (p := p) hget (by decide) v hi'
    heq hm'
  exact ⟨hok, k6Mem_to_amem (hsh.putArr f i.toNat v) hst⟩

theorem fullAddClause6_mem_to_ka {c : FullCfg} {L : K6Layout} {s : FullState}
    {scr xs : List (BitVec 32)} {litsPtr : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    {ks : K6State} (hlen : scr.length = L.scrLen) (hsh : ks.ShapesOk L)
    (hof : K6State.ofSlab L (scr.drop L.k6Base) = ks)
    (hm : (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
      array (t := i32) c.pScratchBuf scr ⋆ array (t := i32) litsPtr xs ⋆ R) m) :
    (K6MemA L (L.kPtr c.pScratchBuf) ks ⋆
      (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
        (array (t := i32) litsPtr xs ⋆
          (array (t := i32) c.pScratchBuf (scr.take L.k6Base) ⋆ R)))) m := by
  rw [array_scratch_eq_k6 hlen, hof] at hm
  exact k6Mem_to_amem hsh (sep_ac hm)

theorem fullAddClause6_ka_to_mem {c : FullCfg} {L : K6Layout} {s : FullState}
    {scr xs : List (BitVec 32)} {litsPtr : BitVec 64} {R : Mem 64 → Prop} {m' : Mem 64}
    {ks' : K6State} (hkbase : L.k6Base ≤ scr.length) (hsh' : ks'.ShapesOk L)
    (hm' : (K6MemA L (L.kPtr c.pScratchBuf) ks' ⋆
      (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
        (array (t := i32) litsPtr xs ⋆
          (array (t := i32) c.pScratchBuf (scr.take L.k6Base) ⋆ R)))) m') :
    let scr' := scr.take L.k6Base ++ ks'.toSlab
    let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
    (array64 (c.hdr + 32) (Full.hdrTailWords c s') ⋆
      array (t := i32) c.pScratchBuf scr' ⋆ array (t := i32) litsPtr xs ⋆ R) m' := by
  intro scr' s'
  obtain ⟨_, hm0⟩ := k6MemA_to_mem hm'
  have htk : (scr.take L.k6Base).length = L.k6Base := List.length_take_of_le hkbase
  have hm1 : (array64 (c.hdr + 32) (Full.hdrTailWords c s') ⋆
      ((array (t := i32) c.pScratchBuf (scr.take L.k6Base) ⋆
        K6Mem L (L.kPtr c.pScratchBuf) ks') ⋆
      (array (t := i32) litsPtr xs ⋆ R))) m' := by
    have hhdr : Full.hdrTailWords c s' = Full.hdrTailWords c s := rfl
    rw [hhdr]; exact sep_ac hm0
  rw [k6_append_eq_array_scratch htk hsh'] at hm1; exact sep_ac hm1

namespace K6MemATactics

attribute [scoped bv_c0] bv32_lshr_1 bv32_and_1 bv32_xor_1 List.length_set Bool.false_eq_true

section FrameAccess
variable {c : FullCfg} {L : K6Layout} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}

@[scoped c0_load] theorem load_k6f_scratch_cap (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 928) = some (BitVec.ofNat 64 c.scratch_cap) :=
  FullArenaTactics.load_full_scratch_cap hm
@[scoped c0_load] theorem load_k6fr_scratch_cap (hm : (FullK6Frame c L s ⋆ R) m) :
    loadVal m i64 (c.hdr + 928) = some (BitVec.ofNat 64 c.scratch_cap) := by
  simpa [Full.hdrTailWords, hdrTailWords0, hdrTailWords1, hdrTailWords2, hdrTailWords3] using
    fullK6Frame_hdrGet 112 (by decide) hm
@[scoped c0_load] theorem load_k6f_scratch_buf (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 920) = some c.pScratchBuf :=
  FullArenaTactics.load_full_scratch_buf_ptr hm
@[scoped c0_load] theorem load_k6fr_scratch_buf (hm : (FullK6Frame c L s ⋆ R) m) :
    loadVal m i64 (c.hdr + 920) = some c.pScratchBuf := by
  simpa [Full.hdrTailWords, hdrTailWords0, hdrTailWords1, hdrTailWords2, hdrTailWords3] using
    fullK6Frame_hdrGet 111 (by decide) hm
@[scoped c0_load] theorem load_k6fr_fuel (hm : (FullK6Frame c L s ⋆ R) m) :
    loadVal m i64 (c.hdr + 168) = some s.core.fuel := by
  simpa [Full.hdrTailWords, hdrTailWords0, hdrTailWords1, hdrTailWords2, hdrTailWords3] using
    fullK6Frame_hdrGet 17 (by decide) hm
@[scoped c0_store] theorem store_k6fr_fuel (v : BitVec 64) (hm : (FullK6Frame c L s ⋆ R) m) :
    storeOk m i64 (c.hdr + 168) ∧
      (FullK6Frame c L { s with core := { s.core with fuel := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 168) v) := fullK6Frame_fuel_store v hm
@[scoped c0_load] theorem load_k6hdrTail_scratch_cap
    (hm : (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ R) m) :
    loadVal m i64 (c.hdr + 928) = some (BitVec.ofNat 64 c.scratch_cap) := by
  have hl := loadVal_array64 (i := 112) (by rw [Full.hdrTailWords_length]; decide) hm
  rw [show c.hdr + 32 + BitVec.ofNat 64 (8 * 112) = c.hdr + 928 from
    ptr_add_ofNat c.hdr 32 896] at hl
  simpa [Full.hdrTailWords, hdrTailWords0, hdrTailWords1, hdrTailWords2, hdrTailWords3] using hl
@[scoped c0_load] theorem load_k6hdrTail_scratch_buf
    (hm : (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ R) m) :
    loadVal m i64 (c.hdr + 920) = some c.pScratchBuf := by
  have hl := loadVal_array64 (i := 111) (by rw [Full.hdrTailWords_length]; decide) hm
  rw [show c.hdr + 32 + BitVec.ofNat 64 (8 * 111) = c.hdr + 920 from
    ptr_add_ofNat c.hdr 32 888] at hl
  simpa [Full.hdrTailWords, hdrTailWords0, hdrTailWords1, hdrTailWords2, hdrTailWords3] using hl
@[scoped c0_load] theorem load_k6arr32_z0 {a : BitVec 64} {xs : List (BitVec 32)}
    (h : (array (t := i32) a xs ⋆ R) m) (hi : 0 < xs.length) :
    loadVal m i32 (a + BitVec.ofNat 64 0 * 4) = some (xs[0]'hi) := by
  rw [k6_ptr_nat_mul4 a 0 (by decide)]; exact loadVal_array (t := i32) (by decide) hi h
@[scoped c0_load] theorem load_k6arr32_u32 {a : BitVec 64} {i : BitVec 32} {xs : List (BitVec 32)}
    (h : (array (t := i32) a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i32 (a + i.setWidth 64 * 4) = some (xs[i.toNat]'hi) := by
  rw [show (4 : BitVec 64) = 4#64 from rfl]; exact c0_load_array32_u32 h hi
@[scoped c0_store] theorem store_k6arr32_u32 {a : BitVec 64} {i : BitVec 32}
    {xs : List (BitVec 32)} (v : BitVec 32) (h : (array (t := i32) a xs ⋆ R) m)
    (hi : i.toNat < xs.length) :
    storeOk m i32 (a + i.setWidth 64 * 4) ∧
      (array (t := i32) a (xs.set i.toNat v) ⋆ R) (storeMem m i32 (a + i.setWidth 64 * 4) v) := by
  rw [show (4 : BitVec 64) = 4#64 from rfl]; exact c0_store_array32_u32 v h hi
end FrameAccess

local syntax "def_k6_hdr " ident num : command
local macro_rules
  | `(def_k6_hdr $fld $idx) => do
    let lnm := Lean.mkIdent (Lean.Name.mkSimple s!"load_k6_{fld.getId}")
    let snm := Lean.mkIdent (Lean.Name.mkSimple s!"store_k6_{fld.getId}")
    let pnm := Lean.mkIdent (Lean.Name.mkSimple s!"putArr_{fld.getId}")
    let hnm := Lean.mkIdent (Lean.Name.mkSimple s!"putHdr_{fld.getId}")
    let tag := Lean.mkIdent (`K6HdrField ++ fld.getId)
    `(
      @[scoped bv_c0] theorem $pnm (ks : K6State) (f : K6ArrField) (i : Nat) (v : BitVec 32) :
          (ks.putArr f i v).$fld = ks.$fld := by cases f <;> rfl
      theorem $hnm (ks : K6State) (f : K6HdrField) (v : BitVec 32) :
          (ks.putHdr f v).$fld = if f = $tag then v else ks.$fld := by cases f <;> rfl
      @[scoped c0_load] theorem $lnm {L : K6Layout} {kPtr : BitVec 64} {ks : K6State}
          {R : Mem 64 → Prop} {m : Mem 64} (hm : (K6MemA L kPtr ks ⋆ R) m) :
          loadVal m i32 (kPtr + BitVec.ofNat 64 ($idx) * 4) = some ks.$fld :=
        k6HdrGet ($idx) (by decide) ks.$fld (fun _ => rfl) hm
      @[scoped c0_store] theorem $snm {L : K6Layout} {kPtr : BitVec 64} {ks : K6State}
          {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hm : (K6MemA L kPtr ks ⋆ R) m) :
          storeOk m i32 (kPtr + BitVec.ofNat 64 ($idx) * 4) ∧
            (K6MemA L kPtr (ks.putHdr $tag v) ⋆ R)
              (storeMem m i32 (kPtr + BitVec.ofNat 64 ($idx) * 4) v) :=
        k6HdrPut $tag ($idx) v (by decide) rfl (by rfl) hm
    )

def_k6_hdr nv 0
def_k6_hdr nc 1
def_k6_hdr lvl 2
def_k6_hdr prop 3
def_k6_hdr trl_end 4
def_k6_hdr unass 5
def_k6_hdr incons 6
def_k6_hdr qfirst 7
def_k6_hdr qlast 8
def_k6_hdr qsearch 9
def_k6_hdr qstamp 10
def_k6_hdr ticks 11
def_k6_hdr tick_lim 12
def_k6_hdr alen 13
def_k6_hdr acap 14
def_k6_hdr nassump 15
def_k6_hdr nkl 16
def_k6_hdr nana 17
def_k6_hdr status 18
def_k6_hdr phase 19
def_k6_hdr openCnt 20
def_k6_hdr max_v 21
def_k6_hdr max_orig 22
def_k6_hdr max_cl 23
def_k6_hdr neq 24

theorem putHdr_hdrTail (ks : K6State) (f : K6HdrField) (v : BitVec 32) :
    (ks.putHdr f v).hdrTail = ks.hdrTail := by cases f <;> rfl
theorem putArr_hdrTail (ks : K6State) (f : K6ArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).hdrTail = ks.hdrTail := by cases f <;> rfl

local syntax "def_k6_arr " ident num ident ident ident : command
local macro_rules
  | `(def_k6_arr $fld $pidx $offfn $szfn $lenfld) => do
    let lnm := Lean.mkIdent (Lean.Name.mkSimple s!"load_k6_{fld.getId}")
    let snm := Lean.mkIdent (Lean.Name.mkSimple s!"store_k6_{fld.getId}")
    let hnm := Lean.mkIdent (Lean.Name.mkSimple s!"putHdr_{fld.getId}")
    let pnm := Lean.mkIdent (Lean.Name.mkSimple s!"putArr_{fld.getId}")
    let ltnm := Lean.mkIdent (Lean.Name.mkSimple s!"{szfn.getId}_lt28")
    let ii := Lean.mkIdent (Lean.Name.mkSimple "i")
    let tag := Lean.mkIdent (`K6ArrField ++ fld.getId)
    `(
      @[scoped bv_c0] theorem $hnm (ks : K6State) (f : K6HdrField) (v : BitVec 32) :
          (ks.putHdr f v).$fld = ks.$fld := by cases f <;> rfl
      theorem $pnm (ks : K6State) (f : K6ArrField) (i : Nat) (v : BitVec 32) :
          (ks.putArr f i v).$fld = if f = $tag then (ks.$fld).set i v else ks.$fld := by
        cases f <;> rfl
      @[scoped c0_load] theorem $lnm {L : K6Layout} {kPtr : BitVec 64} {ks : K6State}
          {R : Mem 64 → Prop} {m : Mem 64} {$ii : BitVec 32} (hi : ($ii).toNat < ($szfn L))
          (hm : (K6MemA L kPtr ks ⋆ R) m) :
          loadVal m i32 ((kPtr + BitVec.ofNat 64 (4 * ($offfn L))) + ($ii).setWidth 64 * 4) =
            some ((ks.$fld)[($ii).toNat]?.getD 0#32) :=
        k6ArrGetBase (k6Path $pidx) ($offfn L) ($szfn L) ks.$fld (fun h => h.$lenfld)
          (by rfl) (Nat.lt_trans hi ($ltnm L)) hi hm
      @[scoped c0_store] theorem $snm {L : K6Layout} {kPtr : BitVec 64} {ks : K6State}
          {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) {$ii : BitVec 32}
          (hi : ($ii).toNat < ($szfn L))
          (hm : (K6MemA L kPtr ks ⋆ R) m) :
          storeOk m i32 ((kPtr + BitVec.ofNat 64 (4 * ($offfn L))) + ($ii).setWidth 64 * 4) ∧
            (K6MemA L kPtr (ks.putArr $tag ($ii).toNat v) ⋆ R)
              (storeMem m i32 ((kPtr + BitVec.ofNat 64 (4 * ($offfn L))) +
                ($ii).setWidth 64 * 4) v) :=
        k6ArrPutBase (k6Path $pidx) $tag ($offfn L) ($szfn L) ks.$fld (fun h => h.$lenfld)
          (by rfl) v (Nat.lt_trans hi ($ltnm L)) hi (by rfl) hm
    )

abbrev szV (L : K6Layout) : Nat := L.maxV
abbrev sz2V (L : K6Layout) : Nat := 2 * L.maxV
abbrev szCl (L : K6Layout) : Nat := L.maxCl
abbrev sz2Cl (L : K6Layout) : Nat := 2 * L.maxCl
abbrev szAr (L : K6Layout) : Nat := L.acap

theorem szV_lt28 (L : K6Layout) : szV L < 2 ^ 28 := by have := L.hmaxV; unfold szV; omega
theorem sz2V_lt28 (L : K6Layout) : sz2V L < 2 ^ 28 := by have := L.hmaxV; unfold sz2V; omega
theorem szCl_lt28 (L : K6Layout) : szCl L < 2 ^ 28 := by
  have := L.hmaxV; unfold szCl K6Layout.maxCl; omega
theorem sz2Cl_lt28 (L : K6Layout) : sz2Cl L < 2 ^ 28 := by
  have := L.hmaxV; unfold sz2Cl K6Layout.maxCl; omega
theorem szAr_lt28 (L : K6Layout) : szAr L < 2 ^ 28 := by
  have := L.hacap; unfold szAr dimacsBound at *; omega

def_k6_arr lvlArr 1 K6Layout.oLvl szV lvlArr_len
def_k6_arr rsn 2 K6Layout.oRsn szV rsn_len
def_k6_arr qprev 3 K6Layout.oQPrev szV qprev_len
def_k6_arr qnext 4 K6Layout.oQNext szV qnext_len
def_k6_arr qstampArr 5 K6Layout.oQStamp szV qstampArr_len
def_k6_arr trl 6 K6Layout.oTrl szV trl_len
def_k6_arr flags 7 K6Layout.oFlags szV flags_len
def_k6_arr ana 8 K6Layout.oAna szV ana_len
def_k6_arr kl 9 K6Layout.oKl szV kl_len
def_k6_arr assump 10 K6Layout.oAssump szV assump_len
def_k6_arr vals 11 K6Layout.oVals sz2V vals_len
def_k6_arr whead 12 K6Layout.oWHead sz2V whead_len
def_k6_arr wnext 13 K6Layout.oWNext sz2Cl wnext_len
def_k6_arr wblit 14 K6Layout.oWBlit sz2Cl wblit_len
def_k6_arr clOff 15 K6Layout.oClOff szCl clOff_len
def_k6_arr clSz 16 K6Layout.oClSz szCl clSz_len
def_k6_arr arena 17 K6Layout.oArena szAr arena_len

section ExtraK6Access
variable {L : K6Layout} {kPtr : BitVec 64} {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64}

@[scoped c0_load] theorem load_k6_kl0 (hm : (K6MemA L kPtr ks ⋆ R) m) :
    loadVal m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oKl)) + (0#32).setWidth 64 * 4) =
      some (ks.kl[0]?.getD 0#32) :=
  load_k6_kl (i := 0#32) (by unfold szV; have := L.hmaxV; bv_omega) hm

@[scoped c0_store] theorem store_k6_kl0 (v : BitVec 32) (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oKl)) + (0#32).setWidth 64 * 4) ∧
      (K6MemA L kPtr (ks.putArr .kl 0 v) ⋆ R)
        (storeMem m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oKl)) + (0#32).setWidth 64 * 4) v) :=
  store_k6_kl v (i := 0#32) (by unfold szV; have := L.hmaxV; bv_omega) hm

@[scoped c0_load] theorem load_k6_kl1 (hm : (K6MemA L kPtr ks ⋆ R) m) :
    loadVal m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oKl)) + (1#32).setWidth 64 * 4) =
      some (ks.kl[1]?.getD 0#32) :=
  load_k6_kl (i := 1#32) (by unfold szV; have := L.hmaxV; bv_omega) hm

@[scoped c0_store] theorem store_k6_kl1 (v : BitVec 32) (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oKl)) + (1#32).setWidth 64 * 4) ∧
      (K6MemA L kPtr (ks.putArr .kl 1 v) ⋆ R)
        (storeMem m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oKl)) + (1#32).setWidth 64 * 4) v) :=
  store_k6_kl v (i := 1#32) (by unfold szV; have := L.hmaxV; bv_omega) hm

@[scoped c0_load] theorem load_k6_assump0 (hm : (K6MemA L kPtr ks ⋆ R) m) :
    loadVal m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oAssump)) + (0#32).setWidth 64 * 4) =
      some (ks.assump[0]?.getD 0#32) :=
  load_k6_assump (i := 0#32) (by unfold szV; have := L.hmaxV; bv_omega) hm

@[scoped c0_store] theorem store_k6_assump0 (v : BitVec 32) (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oAssump)) + (0#32).setWidth 64 * 4) ∧
      (K6MemA L kPtr (ks.putArr .assump 0 v) ⋆ R)
        (storeMem m i32
          ((kPtr + BitVec.ofNat 64 (4 * L.oAssump)) + (0#32).setWidth 64 * 4) v) :=
  store_k6_assump v (i := 0#32) (by unfold szV; have := L.hmaxV; bv_omega) hm

@[scoped c0_load] theorem load_k6_trl_sub1 {te : BitVec 32} (hpos : 0 < te.toNat)
    (hi : te.toNat - 1 < L.maxV) (hm : (K6MemA L kPtr ks ⋆ R) m) :
    loadVal m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oTrl)) + (te - 1#32).setWidth 64 * 4) =
      some (ks.trl[te.toNat - 1]?.getD 0#32) := by
  have hsub : (te - 1#32).toNat = te.toNat - 1 := by bv_omega
  simpa [hsub] using load_k6_trl (i := te - 1#32) (by unfold szV; rw [hsub]; exact hi) hm

@[scoped c0_store] theorem store_k6_qnext_sub1 (v : BitVec 32) {nv : BitVec 32}
    (hpos : 0 < nv.toNat) (hi : nv.toNat - 1 < L.maxV) (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oQNext)) + (nv - 1#32).setWidth 64 * 4) ∧
      (K6MemA L kPtr (ks.putArr .qnext (nv.toNat - 1) v) ⋆ R)
        (storeMem m i32
          ((kPtr + BitVec.ofNat 64 (4 * L.oQNext)) + (nv - 1#32).setWidth 64 * 4) v) := by
  have hsub : (nv - 1#32).toNat = nv.toNat - 1 := by bv_omega
  simpa [hsub] using store_k6_qnext v (i := nv - 1#32) (by unfold szV; rw [hsub]; exact hi) hm

@[scoped c0_load] theorem load_k6_arena_off {off j : BitVec 32}
    (hwrap : off.toNat + j.toNat < 2 ^ 32) (hi : off.toNat + j.toNat < L.acap)
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    loadVal m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oArena)) + (off + j).setWidth 64 * 4) =
      some (ks.arena[off.toNat + j.toNat]?.getD 0#32) := by
  have hoj : (off + j).toNat = off.toNat + j.toNat := by bv_omega
  simpa [hoj] using load_k6_arena (i := off + j) (by unfold szAr; rw [hoj]; exact hi) hm

@[scoped c0_store] theorem store_k6_arena_off (v : BitVec 32) {off j : BitVec 32}
    (hwrap : off.toNat + j.toNat < 2 ^ 32) (hi : off.toNat + j.toNat < L.acap)
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oArena)) + (off + j).setWidth 64 * 4) ∧
      (K6MemA L kPtr (ks.putArr .arena (off.toNat + j.toNat) v) ⋆ R)
        (storeMem m i32
          ((kPtr + BitVec.ofNat 64 (4 * L.oArena)) + (off + j).setWidth 64 * 4) v) := by
  have hoj : (off + j).toNat = off.toNat + j.toNat := by bv_omega
  simpa [hoj] using store_k6_arena v (i := off + j) (by unfold szAr; rw [hoj]; exact hi) hm
end ExtraK6Access

scoped macro "c0_call " h:ident : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

scoped macro "k6_field" : tactic => `(tactic|
  simp only [
    putHdr_nv, putHdr_nc, putHdr_lvl, putHdr_prop, putHdr_trl_end, putHdr_unass, putHdr_incons,
    putHdr_qfirst, putHdr_qlast, putHdr_qsearch, putHdr_qstamp, putHdr_ticks, putHdr_tick_lim,
    putHdr_alen, putHdr_acap, putHdr_nassump, putHdr_nkl, putHdr_nana, putHdr_status, putHdr_phase,
    putHdr_openCnt, putHdr_max_v, putHdr_max_orig, putHdr_max_cl, putHdr_neq, putHdr_hdrTail,
    putArr_hdrTail, putArr_nv, putArr_nc, putArr_lvl, putArr_prop, putArr_trl_end,
    putArr_unass, putArr_incons, putArr_qfirst, putArr_qlast, putArr_qsearch, putArr_qstamp,
    putArr_ticks, putArr_tick_lim, putArr_alen, putArr_acap, putArr_nassump, putArr_nkl,
    putArr_nana, putArr_status, putArr_phase, putArr_openCnt, putArr_max_v, putArr_max_orig,
    putArr_max_cl, putArr_neq,
    putHdr_lvlArr, putHdr_rsn, putHdr_qprev, putHdr_qnext, putHdr_qstampArr, putHdr_trl,
    putHdr_flags, putHdr_ana, putHdr_kl, putHdr_assump, putHdr_vals, putHdr_whead, putHdr_wnext,
    putHdr_wblit, putHdr_clOff, putHdr_clSz, putHdr_arena,
    putArr_lvlArr, putArr_rsn, putArr_qprev, putArr_qnext, putArr_qstampArr, putArr_trl,
    putArr_flags, putArr_ana, putArr_kl, putArr_assump, putArr_vals, putArr_whead, putArr_wnext,
    putArr_wblit, putArr_clOff, putArr_clSz, putArr_arena,
    reduceCtorEq, ite_true, ite_false])

scoped macro "k6_ext" : tactic => `(tactic|
  (apply k6State_ext <;> (k6_field; try rfl)))

end K6MemATactics

/-! ## 4. Semantic Model-Set & Structural Invariants -/

@[expose] def k6WatchStep0 (ks : K6State) (w l valOther : BitVec 32) : K6State :=
  let wi := w.toNat; let li := l.toNat
  { ks with
    wblit := ks.wblit.set wi valOther
    wnext := ks.wnext.set wi (ks.whead[li]?.getD 0#32)
    whead := ks.whead.set li w }

@[expose] def k6WatchStep (ks : K6State) (cid l0 l1 : BitVec 32) : K6State :=
  let w0 := cid <<< 1; let w1 := w0 ||| 1#32
  let sz := (ks.clSz[cid.toNat]?.getD 0#32).toNat
  let bf := if sz = 2 then 0x80000000#32 else 0#32
  k6WatchStep0 (k6WatchStep0 ks w0 l0 (l1 ||| bf)) w1 l1 (l0 ||| bf)

@[expose] def k6AssignStep (ks : K6State) (lit rsn : BitVec 32) : K6State :=
  let v := (lit >>> 1).toNat; let li := lit.toNat; let nli := (lit ^^^ 1#32).toNat
  let te := ks.trl_end.toNat
  let unass' := if ks.unass.toNat > 0 then ks.unass - 1#32 else ks.unass
  let fl := ks.flags[v]?.getD 0#32
  let fl' := if (lit &&& 1#32) ≠ 0#32 then fl ||| 1#32 else fl &&& ~~~1#32
  { ks with
    vals := (ks.vals.set li 1#32).set nli 2#32
    lvlArr := ks.lvlArr.set v ks.lvl
    rsn := ks.rsn.set v rsn
    trl := ks.trl.set te lit
    trl_end := ks.trl_end + 1#32
    unass := unass'
    flags := ks.flags.set v fl' }

@[expose] def k6ClauseOff (ks : K6State) (cid : Nat) : Nat := (ks.clOff[cid]?.getD 0#32).toNat
@[expose] def k6ClauseSize (ks : K6State) (cid : Nat) : Nat := (ks.clSz[cid]?.getD 0#32).toNat
@[expose] def k6ClauseLits (ks : K6State) (cid : Nat) : List Nat :=
  ((ks.arena.drop (k6ClauseOff ks cid)).take (k6ClauseSize ks cid)).map BitVec.toNat
@[expose] def k6AssumpLits (ks : K6State) : List Nat :=
  (ks.assump.take ks.nassump.toNat).map BitVec.toNat
@[expose] def k6TrailLits (ks : K6State) : List Nat :=
  (ks.trl.take ks.trl_end.toNat).map BitVec.toNat

@[expose] def k6TrailDecisions (ks : K6State) : List Nat :=
  (ks.trl.take ks.trl_end.toNat).filterMap fun l =>
    if 0 < (ks.lvlArr[l.toNat / 2]?.getD 0#32).toNat ∧
       ks.rsn[l.toNat / 2]?.getD 0#32 = 0xFFFFFFFF#32
    then some l.toNat else none

/-- `K6` 2WL invariant with exact inline binary `K6_BIN_FLAG` (`0x80000000#32`) tracking. -/
@[expose] def K6WatchesOk (ks : K6State) : Prop :=
  ∃ chains : List (List Nat),
    chains.length = 2 * ks.nv.toNat ∧ chains.flatten.Nodup ∧
    (∀ l < 2 * ks.nv.toNat,
      K5WChain ks.wnext (ks.whead[l]?.getD 0xFFFFFFFF#32) (chains[l]?.getD [])) ∧
    (∀ l < 2 * ks.nv.toNat, ∀ w ∈ chains[l]?.getD [],
      w < 2 * ks.nc.toNat ∧ 2 ≤ k6ClauseSize ks (w / 2) ∧
      (ks.arena[k6ClauseOff ks (w / 2) + (w % 2)]?.getD 0#32).toNat = l ∧
      let wb := ks.wblit[w]?.getD 0#32
      let bv := (wb &&& 0x7FFFFFFF#32).toNat
      bv < 2 * ks.nv.toNat ∧ bv ∈ k6ClauseLits ks (w / 2) ∧
      ((wb &&& 0x80000000#32) ≠ 0#32 ↔ k6ClauseSize ks (w / 2) = 2) ∧
      (k6ClauseSize ks (w / 2) = 2 →
        bv = (ks.arena[k6ClauseOff ks (w / 2) + (w % 2 ^^^ 1)]?.getD 0#32).toNat))

structure K6ClausesOk (L : K6Layout) (P : (Nat → Bool) → Prop) (ks : K6State) : Prop where
  acap_eq : ks.acap = BitVec.ofNat 32 L.acap
  max_v_eq : ks.max_v = BitVec.ofNat 32 L.maxV
  max_orig_eq : ks.max_orig = BitVec.ofNat 32 L.maxOrig
  max_cl_eq : ks.max_cl = BitVec.ofNat 32 L.maxCl
  nv_le : ks.nv.toNat ≤ L.maxV
  nc_le : ks.nc.toNat ≤ L.maxCl
  alen_le : ks.alen.toNat ≤ L.acap
  nassump_le : ks.nassump.toNat ≤ L.maxV
  nkl_le : ks.nkl.toNat ≤ L.maxV
  nana_le : ks.nana.toNat ≤ L.maxV
  cl_wf : ∀ cid < ks.nc.toNat,
    2 ≤ k6ClauseSize ks cid ∧
    k6ClauseOff ks cid + k6ClauseSize ks cid ≤ ks.alen.toNat ∧
    (∀ l ∈ k6ClauseLits ks cid, l < 2 * ks.nv.toNat) ∧
    SemEntails P (k6ClauseLits ks cid)
  cl_mono : ∀ c1 c2, c1 < c2 → c2 < ks.nc.toNat →
    k6ClauseOff ks c1 + k6ClauseSize ks c1 ≤ k6ClauseOff ks c2
  incons_ok : ks.incons ≠ 0#32 → ∀ β, ¬ P β
  assump_ok : ∀ i < ks.nassump.toNat, (ks.assump[i]?.getD 0#32).toNat < 2 * ks.nv.toNat
  flags_clean : ∀ v < ks.nv.toNat, (ks.flags[v]?.getD 0#32 &&& 2#32) = 0#32

structure K6BaseAssignOk (P : (Nat → Bool) → Prop) (ks : K6State) : Prop where
  trl_end_le : ks.trl_end.toNat ≤ ks.nv.toNat
  prop_le : ks.prop.toNat ≤ ks.trl_end.toNat
  unass_eq : ks.unass.toNat + ks.trl_end.toNat = ks.nv.toNat
  vals_dom : ∀ l < 2 * ks.nv.toNat,
    let v := ks.vals[l]?.getD 0#32; v = 0#32 ∨ v = 1#32 ∨ v = 2#32
  vals_neg_iff : ∀ l < 2 * ks.nv.toNat,
    ks.vals[l]?.getD 0#32 = 1#32 ↔ ks.vals[l ^^^ 1]?.getD 0#32 = 2#32
  vals_nz_iff_trl : ∀ l < 2 * ks.nv.toNat,
    ks.vals[l]?.getD 0#32 ≠ 0#32 ↔
      ∃ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = l / 2
  trl_nodup : (k6TrailLits ks |>.map (· / 2)).Nodup
  trl_lt : ∀ l ∈ k6TrailLits ks, l < 2 * ks.nv.toNat
  trl_lvl_le : ∀ v < ks.nv.toNat, (ks.lvlArr[v]?.getD 0#32).toNat ≤ ks.lvl.toNat
  unass_lvl_zero : ∀ v < ks.nv.toNat, ks.vals[2 * v]?.getD 0#32 = 0#32 →
    ks.lvlArr[v]?.getD 0#32 = 0#32 ∧ ks.rsn[v]?.getD 0#32 = 0xFFFFFFFF#32
  trl_lvl_mono : ∀ i j, i ≤ j → j < ks.trl_end.toNat →
    (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
    (ks.lvlArr[(ks.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
  dec_earliest : ∀ i j, j < i → i < ks.trl_end.toNat →
    0 < (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat →
    ks.lvlArr[(ks.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32 =
      ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 →
    ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 ≠ 0xFFFFFFFF#32
  lvl0_ok : ∀ i < ks.trl_end.toNat,
    let l := (ks.trl[i]?.getD 0#32).toNat
    ks.lvlArr[l / 2]?.getD 0#32 = 0#32 →
    ks.vals[l]? = some 1#32 ∧ ks.vals[l ^^^ 1]? = some 2#32 ∧ SemEntails P [l]

@[expose] def K6TrailSynced (ks : K6State) : Prop :=
  ∀ i < ks.trl_end.toNat,
    let l := (ks.trl[i]?.getD 0#32).toNat
    ks.vals[l]? = some 1#32 ∧ ks.vals[l ^^^ 1]? = some 2#32

@[expose] def K6ReasonOk (ks : K6State) : Prop :=
  ∀ i < ks.trl_end.toNat,
    let l := (ks.trl[i]?.getD 0#32).toNat
    let r := ks.rsn[l / 2]?.getD 0xFFFFFFFF#32
    r = 0xFFFFFFFF#32 ∨
    (r.toNat < ks.nc.toNat ∧ l ∈ k6ClauseLits ks r.toNat ∧
     ∀ x ∈ k6ClauseLits ks r.toNat, x ≠ l → ∃ j < i, (ks.trl[j]?.getD 0#32).toNat = x ^^^ 1)

structure K6Inv (L : K6Layout) (P : (Nat → Bool) → Prop) (ks : K6State) : Prop where
  shapes : ks.ShapesOk L
  clauses : K6ClausesOk L P ks
  watches : K6WatchesOk ks
  assign : K6BaseAssignOk P ks
  reasons : K6ReasonOk ks

@[expose] def k6StateOfScratch (L : K6Layout) (scr : List (BitVec 32)) : K6State :=
  K6State.ofSlab L (scr.drop L.k6Base)

@[expose] def k6AssumpLitsS (L : K6Layout) (scr : List (BitVec 32)) : List Nat :=
  k6AssumpLits (k6StateOfScratch L scr)

@[expose] def K6ScratchInv (P : (Nat → Bool) → Prop) (scr : List (BitVec 32)) : Prop :=
  ∃ (hge : k6MinScr ≤ scr.length) (hlt : scr.length < dimacsBound),
    K6Inv (k6LayoutOfCap scr.length hge hlt) P
      (k6StateOfScratch (k6LayoutOfCap scr.length hge hlt) scr)

@[expose] def K6LitsBounded (M : Nat) (ks : K6State) : Prop :=
  (∀ cid < ks.nc.toNat, ∀ l ∈ k6ClauseLits ks cid, l < 2 * M) ∧
  (∀ w < 2 * ks.nc.toNat, (ks.wblit[w]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat < 2 * M)

@[expose] def k6ResolventLits (ks : K6State) (idx : Nat) : List Nat :=
  let seenTop := ((List.range idx).filterMap fun j =>
    let l := (ks.trl[j]?.getD 0#32).toNat
    if ks.lvlArr[l / 2]?.getD 0#32 = ks.lvl ∧ (ks.flags[l / 2]?.getD 0#32 &&& 2#32) ≠ 0#32
    then some (l ^^^ 1) else none)
  let klLits := ((ks.kl.take ks.nkl.toNat).drop 1).map BitVec.toNat
  seenTop ++ klLits

structure K6AnaInv (L : K6Layout) (P : (Nat → Bool) → Prop) (ks : K6State) (idx : Nat) :
    Prop where
  shapes : ks.ShapesOk L
  acap_eq : ks.acap = BitVec.ofNat 32 L.acap
  max_v_eq : ks.max_v = BitVec.ofNat 32 L.maxV
  max_orig_eq : ks.max_orig = BitVec.ofNat 32 L.maxOrig
  max_cl_eq : ks.max_cl = BitVec.ofNat 32 L.maxCl
  nv_le : ks.nv.toNat ≤ L.maxV
  nc_le : ks.nc.toNat ≤ L.maxCl
  alen_le : ks.alen.toNat ≤ L.acap
  nassump_le : ks.nassump.toNat ≤ L.maxV
  lvl_pos : 0 < ks.lvl.toNat
  idx_le : idx ≤ ks.trl_end.toNat
  cl_wf : ∀ cid < ks.nc.toNat,
    2 ≤ k6ClauseSize ks cid ∧ k6ClauseOff ks cid + k6ClauseSize ks cid ≤ ks.alen.toNat ∧
    (∀ l ∈ k6ClauseLits ks cid, l < 2 * ks.nv.toNat) ∧ SemEntails P (k6ClauseLits ks cid)
  cl_mono : ∀ c1 c2, c1 < c2 → c2 < ks.nc.toNat →
    k6ClauseOff ks c1 + k6ClauseSize ks c1 ≤ k6ClauseOff ks c2
  incons_ok : ks.incons ≠ 0#32 → ∀ β, ¬ P β
  assump_ok : ∀ i < ks.nassump.toNat, (ks.assump[i]?.getD 0#32).toNat < 2 * ks.nv.toNat
  watches : K6WatchesOk ks
  assign : K6BaseAssignOk P ks
  synced : K6TrailSynced ks
  reasons : K6ReasonOk ks
  nkl_pos : 1 ≤ ks.nkl.toNat
  nkl_le : ks.nkl.toNat ≤ ks.nv.toNat
  nana_le : ks.nana.toNat ≤ ks.nv.toNat
  ana_nodup : ((ks.ana.take ks.nana.toNat).map BitVec.toNat).Nodup
  ana_lt : ∀ i < ks.nana.toNat, (ks.ana[i]?.getD 0#32).toNat < ks.nv.toNat
  flags_seen : ∀ v < ks.nv.toNat,
    ((ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32) ↔
      ∃ i < ks.nana.toNat, (ks.ana[i]?.getD 0#32).toNat = v
  kl_nonTop : ∀ i, 1 ≤ i → i < ks.nkl.toNat →
    let l := (ks.kl[i]?.getD 0#32).toNat
    l < 2 * ks.nv.toNat ∧ (ks.flags[l / 2]?.getD 0#32 &&& 2#32) ≠ 0#32 ∧
    0 < (ks.lvlArr[l / 2]?.getD 0#32).toNat ∧ (ks.lvlArr[l / 2]?.getD 0#32).toNat < ks.lvl.toNat ∧
    ks.vals[l]? = some 2#32
  kl_injective : ∀ v < ks.nv.toNat, (ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32 →
    (ks.lvlArr[v]?.getD 0#32).toNat < ks.lvl.toNat →
    ∃ i, 1 ≤ i ∧ i < ks.nkl.toNat ∧ (ks.kl[i]?.getD 0#32).toNat / 2 = v
  nkl_count : ∀ v < ks.nv.toNat, (ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32 →
    0 < (ks.lvlArr[v]?.getD 0#32).toNat
  kl_nodup : (((ks.kl.take ks.nkl.toNat).drop 1).map (fun l => l.toNat / 2)).Nodup
  open_eq : ks.openCnt.toNat =
    ((List.range idx).filter fun j =>
      let v := (ks.trl[j]?.getD 0#32).toNat / 2
      decide (ks.lvlArr[v]?.getD 0#32 = ks.lvl ∧ (ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32)).length
  seen_in_trl : ∀ v < ks.nv.toNat, (ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32 →
    ks.lvlArr[v]?.getD 0#32 = ks.lvl →
    ∃ j < ks.trl_end.toNat, (ks.trl[j]?.getD 0#32).toNat / 2 = v

@[expose] def M6PhtOk (nv : Nat) (scr : List (BitVec 32)) : Prop :=
  (∀ b < k6PhtSz,
    let h := scr[k6PhtHead + b]?.getD 0xFFFFFFFF#32
    h = 0xFFFFFFFF#32 ∨ h.toNat < nv) ∧
  (∀ i < nv,
    let nx := scr[k6PhtNext + i]?.getD 0xFFFFFFFF#32
    nx = 0xFFFFFFFF#32 ∨ nx.toNat < i)

@[expose] def M6PartitionOk (nv ncls : Nat) (scr heads : List (BitVec 32)) : Prop :=
  ncls ≤ heads.length ∧
  (∀ i < nv,
    let nx := scr[k6PhtNext + i]?.getD 0xFFFFFFFF#32
    nx = 0xFFFFFFFF#32 ∨ nx.toNat < i) ∧
  (∀ ci < ncls, (heads[ci]?.getD 0xFFFFFFFF#32).toNat < nv)

@[expose] def M6TmkZero (s : FullState) : Prop :=
  ∀ v < s.core.cur_vars, s.scratch.tarjan_mark[v]?.getD 0#32 = 0#32

@[expose] def M6SweepConeOk (F_cur : List (List Nat)) (s : FullState) (nv : Nat) : Prop :=
  1 ≤ nv ∧ nv ≤ k6MaxV s.scratch.scratch_buf.length ∧ nv ≤ s.core.cur_vars ∧
  (∀ i < nv, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
  K6ScratchInv (ConeModelSet F_cur s.scratch.work_stk1 nv) s.scratch.scratch_buf ∧
  ∃ hge hlt,
    (k6StateOfScratch (k6LayoutOfCap s.scratch.scratch_buf.length hge hlt)
      s.scratch.scratch_buf).nv = BitVec.ofNat 32 nv

@[expose] def M6EqBufOk (F_cur : List (List Nat)) (s : FullState) (neq : Nat) : Prop :=
  neq ≤ s.core.cur_vars ∧
  ∀ i < neq,
    let la := (s.scratch.work_stk2[2 * i]?.getD 0#32).toNat
    let lc := (s.scratch.work_stk2[2 * i + 1]?.getD 0#32).toNat
    la < 2 * s.core.cur_vars ∧ lc < 2 * s.core.cur_vars ∧
    LitEquiv (cnfOfClauses F_cur) la lc

@[expose]
def M6ReprFlatInv (F_cur : List (List Nat)) (nlits : Nat) (repr : List (BitVec 32)) : Prop :=
  FullCongReprInv F_cur nlits repr ∧
  (∀ l < nlits, repr[(repr[l]?.getD 0#32).toNat]? = repr[l]?) ∧
  (∀ l < nlits, (repr[l ^^^ 1]?.getD 0#32).toNat = (repr[l]?.getD 0#32).toNat ^^^ 1)

structure K6BtPreserved (ks ks' : K6State) : Prop where
  nv : ks'.nv = ks.nv
  nc : ks'.nc = ks.nc
  incons : ks'.incons = ks.incons
  alen : ks'.alen = ks.alen
  acap : ks'.acap = ks.acap
  nassump : ks'.nassump = ks.nassump
  nkl : ks'.nkl = ks.nkl
  nana : ks'.nana = ks.nana
  status : ks'.status = ks.status
  phase : ks'.phase = ks.phase
  openCnt : ks'.openCnt = ks.openCnt
  max_v : ks'.max_v = ks.max_v
  max_orig : ks'.max_orig = ks.max_orig
  max_cl : ks'.max_cl = ks.max_cl
  neq : ks'.neq = ks.neq
  hdrTail : ks'.hdrTail = ks.hdrTail
  assump : ks'.assump = ks.assump
  ana : ks'.ana = ks.ana
  kl : ks'.kl = ks.kl
  whead : ks'.whead = ks.whead
  wnext : ks'.wnext = ks.wnext
  wblit : ks'.wblit = ks.wblit
  clOff : ks'.clOff = ks.clOff
  clSz : ks'.clSz = ks.clSz
  arena : ks'.arena = ks.arena
  flags2_eq : ∀ v < ks.nv.toNat,
    (ks'.flags[v]?.getD 0#32 &&& 2#32) = (ks.flags[v]?.getD 0#32 &&& 2#32)
  lvlArr_kept : ∀ i < ks'.trl_end.toNat,
    ks'.lvlArr[(ks'.trl[i]?.getD 0#32).toNat / 2]? =
      ks.lvlArr[(ks'.trl[i]?.getD 0#32).toNat / 2]?

structure K6AnaPreserved (ks ks' : K6State) : Prop where
  nv : ks'.nv = ks.nv
  nc : ks'.nc = ks.nc
  lvl : ks'.lvl = ks.lvl
  prop : ks'.prop = ks.prop
  trl_end : ks'.trl_end = ks.trl_end
  unass : ks'.unass = ks.unass
  incons : ks'.incons = ks.incons
  alen : ks'.alen = ks.alen
  acap : ks'.acap = ks.acap
  nassump : ks'.nassump = ks.nassump
  status : ks'.status = ks.status
  max_v : ks'.max_v = ks.max_v
  max_orig : ks'.max_orig = ks.max_orig
  max_cl : ks'.max_cl = ks.max_cl
  neq : ks'.neq = ks.neq
  lvlArr : ks'.lvlArr = ks.lvlArr
  rsn : ks'.rsn = ks.rsn
  trl : ks'.trl = ks.trl
  vals : ks'.vals = ks.vals
  assump : ks'.assump = ks.assump
  whead : ks'.whead = ks.whead
  wnext : ks'.wnext = ks.wnext
  wblit : ks'.wblit = ks.wblit
  clOff : ks'.clOff = ks.clOff
  clSz : ks'.clSz = ks.clSz
  arena : ks'.arena = ks.arena

structure K6PropPreserved (ks ks' : K6State) : Prop where
  nv : ks'.nv = ks.nv
  nc : ks'.nc = ks.nc
  lvl : ks'.lvl = ks.lvl
  incons : ks'.incons = ks.incons
  alen : ks'.alen = ks.alen
  acap : ks'.acap = ks.acap
  nassump : ks'.nassump = ks.nassump
  status : ks'.status = ks.status
  openCnt : ks'.openCnt = ks.openCnt
  max_v : ks'.max_v = ks.max_v
  max_orig : ks'.max_orig = ks.max_orig
  max_cl : ks'.max_cl = ks.max_cl
  neq : ks'.neq = ks.neq
  assump : ks'.assump = ks.assump

theorem K6Layout.eq_of_scrLen_maxV {L1 L2 : K6Layout} (hlen : L1.scrLen = L2.scrLen)
    (hmv : L1.maxV = L2.maxV) : L1 = L2 := by
  rcases L1 with ⟨mv1, ac1, _, _⟩
  rcases L2 with ⟨mv2, ac2, _, _⟩
  dsimp only at hmv; subst hmv
  unfold K6Layout.scrLen K6Layout.k6Base K6Layout.k6Fixed at hlen
  dsimp only at hlen
  obtain rfl : ac1 = ac2 := by omega
  rfl

theorem k6LayoutOfCap_eq {L : K6Layout} {cap : Nat} (hlen : L.scrLen = cap)
    (hmv : L.maxV = k6MaxV cap) (hge : k6MinScr ≤ cap) (hlt : cap < dimacsBound) :
    k6LayoutOfCap cap hge hlt = L :=
  K6Layout.eq_of_scrLen_maxV ((k6LayoutOfCap_scrLen hge hlt).trans hlen.symm) hmv.symm

theorem k6ScratchInv_to_inv {P : (Nat → Bool) → Prop} {scr : List (BitVec 32)} {L : K6Layout}
    (hlen : L.scrLen = scr.length) (hmv : L.maxV = k6MaxV scr.length)
    (h : K6ScratchInv P scr) : K6Inv L P (k6StateOfScratch L scr) := by
  rcases h with ⟨hge, hlt, hinv⟩
  rwa [k6LayoutOfCap_eq hlen hmv hge hlt] at hinv

theorem K6Inv.to_scratchInv {P : (Nat → Bool) → Prop} {scr : List (BitVec 32)} {L : K6Layout}
    (hlen : scr.length = L.scrLen) (hmv : L.maxV = k6MaxV scr.length)
    (hge : k6MinScr ≤ scr.length) (hlt : scr.length < dimacsBound)
    (h : K6Inv L P (k6StateOfScratch L scr)) : K6ScratchInv P scr := by
  refine ⟨hge, hlt, ?_⟩
  rwa [k6LayoutOfCap_eq hlen.symm hmv hge hlt]

/-! ## 5. All `39` Owned + `12` External `Spec` Contracts (`51` Total) -/

@[expose] def m6MaxVSpec : Spec [i64] [i64] := fun (cap, ()) m Q _ =>
  Q (BitVec.ofNat 64 (k6MaxV cap.toNat), ()) m

@[expose] def k6AddTicksSpec : Spec [i64, i64] [] := fun (kPtr, _delta, ()) m Q _ =>
  ∃ (L : K6Layout) (ks : K6State) (R : Mem 64 → Prop),
    ks.ShapesOk L ∧ (K6Mem L kPtr ks ⋆ R) m ∧
    ∀ tk' m', (K6Mem L kPtr (ks.putHdr .ticks tk') ⋆ R) m' → Q () m'

@[expose] def k6InitSpec : Spec [i64, i32] [] := fun (h, nv, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    if c.scratch_cap < k6MinScr ∨ k6MaxV c.scratch_cap < nv.toNat then Q () m
    else ∀ (L : K6Layout) (scr' : List (BitVec 32)) (m' : Mem 64),
      L.scrLen = c.scratch_cap → L.maxV = k6MaxV c.scratch_cap →
      let ks' := k6StateOfScratch L scr'
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      s'.LengthsOk c → (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      (∀ P, K6Inv L P ks') → K6TrailSynced ks' →
      ks'.nv = nv → ks'.nc = 0#32 → ks'.lvl = 0#32 → ks'.prop = 0#32 →
      ks'.trl_end = 0#32 → ks'.unass = nv → ks'.incons = 0#32 → ks'.nassump = 0#32 →
      ks'.status = 0#32 → ks'.openCnt = 0#32 → ks'.neq = 0#32 →
      (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def k6WatchSpec : Spec [i64, i32, i32, i32] [] := fun (kPtr, cid, l0, l1, ()) m Q _ =>
  ∃ (L : K6Layout) (ks : K6State) (R : Mem 64 → Prop),
    ks.ShapesOk L ∧ ks.max_v = L.mv32 ∧ cid.toNat < L.maxCl ∧
    l0.toNat < 2 * L.maxV ∧ l1.toNat < 2 * L.maxV ∧ (K6Mem L kPtr ks ⋆ R) m ∧
    ∀ m', (K6Mem L kPtr (k6WatchStep ks cid l0 l1) ⋆ R) m' → Q () m'

@[expose] def k6AssignSpec : Spec [i64, i32, i32] [] := fun (kPtr, lit, rsn, ()) m Q _ =>
  ∃ (L : K6Layout) (ks : K6State) (R : Mem 64 → Prop),
    ks.ShapesOk L ∧ ks.max_v = L.mv32 ∧ lit.toNat < 2 * L.maxV ∧
    ks.trl_end.toNat < L.maxV ∧ (K6Mem L kPtr ks ⋆ R) m ∧
    ∀ m', (K6Mem L kPtr (k6AssignStep ks lit rsn) ⋆ R) m' → Q () m'

@[expose] def k6AddClauseSpec : Spec [i64, i64, i32] [.bool] := fun (h, lits_ptr, sz, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (P : (Nat → Bool) → Prop) (L : K6Layout)
    (scr xs : List (BitVec 32)) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.scratch.scratch_buf = scr ∧
    L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
    K6Inv L P (k6StateOfScratch L scr) ∧ K6TrailSynced (k6StateOfScratch L scr) ∧
    (k6StateOfScratch L scr).lvl = 0#32 ∧ sz.toNat ≤ xs.length ∧ sz.toNat < 2 ^ 28 ∧
    (∀ i < sz.toNat, (xs[i]?.getD 0#32).toNat < 2 * (k6StateOfScratch L scr).nv.toNat) ∧
    SemEntails P ((xs.take sz.toNat).map BitVec.toNat) ∧
    (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
      array (t := i32) c.pScratchBuf scr ⋆ array (t := i32) lits_ptr xs ⋆ R) m ∧
    ∀ (ok : Bool) (scr' : List (BitVec 32)) (m' : Mem 64),
      let ks := k6StateOfScratch L scr; let ks' := k6StateOfScratch L scr'
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap → (∀ i < L.k6Base, scr'[i]? = scr[i]?) →
      K6Inv L P ks' → K6TrailSynced ks' → ks'.lvl = 0#32 → ks'.nv = ks.nv →
      ks'.nassump = ks.nassump → k6AssumpLitsS L scr' = k6AssumpLitsS L scr →
      (ok = false → ks' = ks) →
      (2 ≤ sz.toNat → ks'.trl_end = ks.trl_end ∧ ks'.prop = ks.prop ∧
        ks'.unass = ks.unass ∧ ks'.incons = ks.incons) →
      (∀ M, (∀ i < sz.toNat, (xs[i]?.getD 0#32).toNat < 2 * M) →
        K6LitsBounded M ks → (∀ l ∈ k6TrailLits ks, l < 2 * M) →
        K6LitsBounded M ks' ∧ (∀ l ∈ k6TrailLits ks', l < 2 * M)) →
      (array64 (c.hdr + 32) (Full.hdrTailWords c s') ⋆
        array (t := i32) c.pScratchBuf scr' ⋆ array (t := i32) lits_ptr xs ⋆ R) m' →
      Q (ok, ()) m'

@[expose] def k6MtfSpec : Spec [i64, i32] [] := fun (kPtr, _v, ()) m Q _ =>
  ∃ (L : K6Layout) (ks : K6State) (R : Mem 64 → Prop),
    ks.ShapesOk L ∧ ks.max_v = L.mv32 ∧ ks.nv.toNat ≤ L.maxV ∧ (K6Mem L kPtr ks ⋆ R) m ∧
    ∀ qf' ql' qs' qst' qp' qn' qsa' m',
      let ks' : K6State := { ks with qfirst := qf', qlast := ql', qsearch := qs', qstamp := qst',
                                     qprev := qp', qnext := qn', qstampArr := qsa' }
      ks'.ShapesOk L → (K6Mem L kPtr ks' ⋆ R) m' → Q () m'

@[expose] def k6BacktrackSpec : Spec [i64, i32] [] := fun (kPtr, target_lvl, ()) m Q _ =>
  ∃ (L : K6Layout) (P : (Nat → Bool) → Prop) (ks : K6State) (R : Mem 64 → Prop),
    K6Inv L P ks ∧ (target_lvl = 0#32 ∨ K6TrailSynced ks) ∧ (K6Mem L kPtr ks ⋆ R) m ∧
    ∀ (ks' : K6State) (m' : Mem 64),
      K6Inv L P ks' → K6TrailSynced ks' → ks'.lvl = target_lvl →
      ks'.trl_end.toNat ≤ ks.trl_end.toNat → K6BtPreserved ks ks' →
      (∀ i < ks'.trl_end.toNat,
        ks'.trl[i]? = ks.trl[i]? ∧ ks'.rsn[(ks'.trl[i]?.getD 0#32).toNat / 2]? =
          ks.rsn[(ks'.trl[i]?.getD 0#32).toNat / 2]? ∧
        (ks'.lvlArr[(ks'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat) →
      (∀ i < ks.trl_end.toNat,
        (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat →
        i < ks'.trl_end.toNat) →
      (K6Mem L kPtr ks' ⋆ R) m' → Q () m'

@[expose] def k6PropagateSpec : Spec [i64] [i32] := fun (kPtr, ()) m Q _ =>
  ∃ (L : K6Layout) (P : (Nat → Bool) → Prop) (ks : K6State) (R : Mem 64 → Prop),
    K6Inv L P ks ∧ K6TrailSynced ks ∧ (K6Mem L kPtr ks ⋆ R) m ∧
    ∀ (confl : BitVec 32) (ks' : K6State) (m' : Mem 64),
      K6Inv L P ks' → K6TrailSynced ks' → K6PropPreserved ks ks' →
      ks.trl_end.toNat ≤ ks'.trl_end.toNat →
      (∀ i < ks.trl_end.toNat, ks'.trl[i]? = ks.trl[i]? ∧
        ks'.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? =
          ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? ∧
        ks'.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]? =
          ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?) →
      (∀ i, ks.trl_end.toNat ≤ i → i < ks'.trl_end.toNat →
        ks'.lvlArr[(ks'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = ks.lvl ∧
        ks'.rsn[(ks'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 ≠ 0xFFFFFFFF#32) →
      (confl = 0xFFFFFFFF#32 → ks'.prop = ks'.trl_end) →
      (confl ≠ 0xFFFFFFFF#32 →
        confl.toNat < ks'.nc.toNat ∧ ∀ l ∈ k6ClauseLits ks' confl.toNat, ks'.vals[l]? = some 2#32) →
      (K6Mem L kPtr ks' ⋆ R) m' → Q (confl, ()) m'

@[expose] def k6AnaClauseSpec : Spec [i64, i32, i32] [] := fun (kPtr, cid, skip_v, ()) m Q _ =>
  ∃ (L : K6Layout) (P : (Nat → Bool) → Prop) (ks : K6State) (idx : Nat) (R : Mem 64 → Prop),
    K6AnaInv L P ks idx ∧ cid.toNat < ks.nc.toNat ∧
    (∃ v_dec < ks.nv.toNat, ks.lvlArr[v_dec]?.getD 0#32 = ks.lvl) ∧
    (∀ l ∈ k6ClauseLits ks cid.toNat, l / 2 ≠ skip_v.toNat →
      ks.vals[l]? = some 2#32 ∧
      (ks.lvlArr[l / 2]?.getD 0#32 = ks.lvl →
        ∃ j < idx, (ks.trl[j]?.getD 0#32).toNat = l ^^^ 1)) ∧
    (skip_v ≠ 0xFFFFFFFF#32 →
      ∃ l ∈ k6ClauseLits ks cid.toNat, l / 2 = skip_v.toNat ∧
        (∀ l' ∈ k6ClauseLits ks cid.toNat, l' / 2 = skip_v.toNat → l' = l) ∧
        (ks.flags[skip_v.toNat]?.getD 0#32 &&& 2#32) ≠ 0#32 ∧
        ks.lvlArr[skip_v.toNat]?.getD 0#32 = ks.lvl ∧
        SemEntails P ((l ^^^ 1) :: k6ResolventLits ks idx)) ∧
    (K6Mem L kPtr ks ⋆ R) m ∧
    ∀ (ks' : K6State) (m' : Mem 64),
      K6AnaInv L P ks' idx → K6AnaPreserved ks ks' →
      SemEntails P (k6ResolventLits ks' idx) →
      (∀ v < ks.nv.toNat, (ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32 →
        (ks'.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32) →
      (K6Mem L kPtr ks' ⋆ R) m' → Q () m'

@[expose] def k6AnalyzeSpec : Spec [i64, i32] [.bool] := fun (kPtr, confl_cid, ()) m Q _ =>
  ∃ (L : K6Layout) (P : (Nat → Bool) → Prop) (ks : K6State) (R : Mem 64 → Prop),
    K6Inv L P ks ∧ K6TrailSynced ks ∧ 0 < ks.lvl.toNat ∧
    (∃ i < ks.trl_end.toNat,
      ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = ks.lvl) ∧
    confl_cid.toNat < ks.nc.toNat ∧
    (∀ l ∈ k6ClauseLits ks confl_cid.toNat, ks.vals[l]? = some 2#32) ∧
    (K6Mem L kPtr ks ⋆ R) m ∧
    ∀ (ok : Bool) (ks' : K6State) (m' : Mem 64),
      K6Inv L P ks' → K6TrailSynced ks' → ks'.nv = ks.nv → ks'.nassump = ks.nassump →
      ks'.assump = ks.assump → ks'.incons = ks.incons → ks'.status = ks.status →
      ks'.neq = ks.neq →
      (ok = true →
        ks'.lvl.toNat < ks.lvl.toNat ∧
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
      (K6Mem L kPtr ks' ⋆ R) m' → Q (ok, ()) m'

@[expose] def k6SolveSpec : Spec [i64, i64] [i64] := fun (h, _tick_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (P : (Nat → Bool) → Prop) (L : K6Layout)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
    K6Inv L P (k6StateOfScratch L s.scratch.scratch_buf) ∧ (FullMem c s ⋆ R) m ∧
    ∀ (r fuel' : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with core := { s.core with fuel := fuel' }
                                     scratch := { s.scratch with scratch_buf := scr' } }
      let ks := k6StateOfScratch L s.scratch.scratch_buf; let ks' := k6StateOfScratch L scr'
      s'.LengthsOk c → fuel'.toNat ≤ s.core.fuel.toNat →
      (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K6Inv L P ks' → K6TrailSynced ks' → ks'.nv = ks.nv → ks'.nassump = ks.nassump →
      k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf → ks'.neq = ks.neq →
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → ∀ β, P β → ¬ (unitsCnf (k6AssumpLitsS L scr')).Sat β) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def k6FlipSpec : Spec [i64, i32] [.bool] := fun (h, lit, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (P : (Nat → Bool) → Prop) (L : K6Layout)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
    K6Inv L P (k6StateOfScratch L s.scratch.scratch_buf) ∧
    lit.toNat < 2 * (k6StateOfScratch L s.scratch.scratch_buf).nv.toNat ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      let ks := k6StateOfScratch L s.scratch.scratch_buf; let ks' := k6StateOfScratch L scr'
      s'.LengthsOk c → (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K6Inv L P ks' → ks'.nv = ks.nv → ks'.nassump = ks.nassump →
      k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf → ks'.neq = ks.neq →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def k6AddLiveSpec : Spec [i64, i32, i32] [] := fun (h, a, b, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (P : (Nat → Bool) → Prop) (L : K6Layout)
    (R : Mem 64 → Prop),
    let ks0 := k6StateOfScratch L s.scratch.scratch_buf
    h = c.hdr ∧ s.LengthsOk c ∧ L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
    K6Inv L P ks0 ∧ a.toNat < 2 * ks0.nv.toNat ∧
    (b = 0xFFFFFFFF#32 → SemEntails P [a.toNat]) ∧
    (b ≠ 0xFFFFFFFF#32 → b.toNat < 2 * ks0.nv.toNat ∧ SemEntails P [a.toNat, b.toNat]) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      let ks' := k6StateOfScratch L scr'
      s'.LengthsOk c → (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K6Inv L P ks' → K6TrailSynced ks' → ks'.nv = ks0.nv →
      ks'.nassump = ks0.nassump → k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf →
      ks'.neq = ks0.neq → (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def m6DensePropLitSpec : Spec [i64, i32] [.bool] := fun (h, _lit, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.core.propagated = s.core.propagated →
      s.core.trail_end ≤ s'.core.trail_end → s'.core.repr = s.core.repr →
      s'.core.arena_len = s.core.arena_len →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (ok = true → s'.core.inconsistent = s.core.inconsistent) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def m6DensePropSpec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.core.repr = s.core.repr →
      s'.core.arena_len = s.core.arena_len →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (ok = true ↔ s'.core.inconsistent = 0#64) →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def m6SweepConeSpec : Spec [i64, i32] [i64] := fun (h, root_v, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ k6MinScr ≤ c.scratch_cap ∧
    root_v.toNat < s.core.cur_vars ∧ M6TmkZero s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r tmp' ws1' tmk' scr' m',
      let s' : FullState := { s with core := { s.core with tmp := tmp' }
                                     scratch := { s.scratch with work_stk1 := ws1',
                                                                 tarjan_mark := tmk',
                                                                 scratch_buf := scr' } }
      let nv := (r &&& 0xFFFF#64).toNat
      let nc := (r >>> 16).toNat
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.core.vals = s.core.vals →
      s'.core.inconsistent = s.core.inconsistent → M6SweepConeOk F_cur s' nv →
      nc ≤ 3 * k6MaxV c.scratch_cap → r.toNat = nv + nc * 2 ^ 16 →
      (∀ v < s.core.cur_vars, tmk'[v]?.getD 0#32 ≠ 0#32 →
        ∃ i < nv, (ws1'[i]?.getD 0#32).toNat = v) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def m6SweepRefineSigSpec : Spec [i64, i32, i32] [] := fun (h, nv, _bit_idx, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ k6MinScr ≤ c.scratch_cap ∧
    nv.toNat ≤ k6MaxV c.scratch_cap ∧ nv.toNat ≤ 2 * c.max_vars ∧
    (∀ i < nv.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ sig' m', sig'.length = c.max_vars →
      (FullMem c { s with scratch := { s.scratch with sim_sig := sig' } } ⋆ R) m' → Q () m'

@[expose] def m6SweepRandPhasesSpec : Spec [i64, i32] [] := fun (h, nv, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (P : (Nat → Bool) → Prop) (L : K6Layout)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
    K6Inv L P (k6StateOfScratch L s.scratch.scratch_buf) ∧
    (k6StateOfScratch L s.scratch.scratch_buf).nv = nv ∧ (FullMem c s ⋆ R) m ∧
    ∀ rng' scr' m',
      let s' : FullState := { s with scratch := { s.scratch with rng_state := rng',
                                                                 scratch_buf := scr' } }
      s'.LengthsOk c → (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K6Inv L P (k6StateOfScratch L scr') → (k6StateOfScratch L scr').nv = nv →
      (k6StateOfScratch L scr').nassump =
        (k6StateOfScratch L s.scratch.scratch_buf).nassump →
      k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf →
      (k6StateOfScratch L scr').neq = (k6StateOfScratch L s.scratch.scratch_buf).neq →
      (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def m6SweepSolveSpec : Spec [i64, i32, i64] [i64] := fun (h, nv, _tick_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (P : (Nat → Bool) → Prop) (L : K6Layout)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
    K6Inv L P (k6StateOfScratch L s.scratch.scratch_buf) ∧
    (k6StateOfScratch L s.scratch.scratch_buf).nv = nv ∧ (FullMem c s ⋆ R) m ∧
    ∀ r fuel' rng' scr' m',
      let s' : FullState :=
        { s with core := { s.core with fuel := fuel' }
                 scratch := { s.scratch with rng_state := rng', scratch_buf := scr' } }
      let ks := k6StateOfScratch L s.scratch.scratch_buf; let ks' := k6StateOfScratch L scr'
      s'.LengthsOk c → fuel'.toNat ≤ s.core.fuel.toNat →
      (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K6Inv L P ks' → K6TrailSynced ks' → ks'.nv = nv → ks'.nassump = ks.nassump →
      k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf → ks'.neq = ks.neq →
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → ∀ β, P β → ¬ (unitsCnf (k6AssumpLitsS L scr')).Sat β) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def m6SweepFlipRoundSpec : Spec [i64, i32] [i32] := fun (h, nv, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (P : (Nat → Bool) → Prop) (L : K6Layout)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
    K6Inv L P (k6StateOfScratch L s.scratch.scratch_buf) ∧
    (k6StateOfScratch L s.scratch.scratch_buf).nv = nv ∧ (FullMem c s ⋆ R) m ∧
    ∀ ret rng' scr' m',
      let s' : FullState := { s with scratch := { s.scratch with rng_state := rng',
                                                                 scratch_buf := scr' } }
      let ks := k6StateOfScratch L s.scratch.scratch_buf; let ks' := k6StateOfScratch L scr'
      s'.LengthsOk c → (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K6Inv L P ks' → ks'.nv = nv → ks'.nassump = ks.nassump →
      k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf → ks'.neq = ks.neq →
      (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

@[expose] def m6SweepSimSpec : Spec [i64, i32, i64] [i32] := fun (h, nv, _tick_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ M6SweepConeOk F_cur s nv.toNat ∧ (FullMem c s ⋆ R) m ∧
    ∀ r fuel' rng' sig' scr' m',
      let s' : FullState := { s with core := { s.core with fuel := fuel' }
                                     scratch := { s.scratch with rng_state := rng',
                                                                 sim_sig := sig',
                                                                 scratch_buf := scr' } }
      FullDenseInvW c F0 F_cur s' → fuel'.toNat ≤ s.core.fuel.toNat →
      M6SweepConeOk F_cur s' nv.toNat →
      (r = 0xFFFFFFFF#32 → (cnfOfClauses F_cur).Unsat) →
      (r ≠ 0xFFFFFFFF#32 → r.toNat ≤ 64) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def m6SweepRearmSpec : Spec [i64, i32] [] := fun (h, _v, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ flags' m',
      let s' : FullState := { s with core := { s.core with flags := flags' } }
      flags'.length = c.max_vars → FullDenseInvW c F0 F_cur s' →
      (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def m6SweepBuildPhtSpec : Spec [i64, i32, i64] [] := fun (h, nv, _smask, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (L : K6Layout) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
    nv.toNat ≤ L.maxV ∧ nv.toNat ≤ 2 * c.max_vars ∧
    (∀ i < nv.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, i < k6PhtHead ∨ L.phtMerged ≤ i →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      M6PhtOk nv.toNat scr' → (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def m6ExtractPhtSpec : Spec [i64, i32, i64] [i32] := fun (h, nv, _smask, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (L : K6Layout) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
    nv.toNat ≤ L.maxV ∧ nv.toNat ≤ c.max_vars ∧
    (∀ i < nv.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
    M6PhtOk nv.toNat s.scratch.scratch_buf ∧ (FullMem c s ⋆ R) m ∧
    ∀ ncls scr' sstk' mclr' m',
      let s' : FullState :=
        { s with core := { s.core with min_clr := mclr' }
                 scratch := { s.scratch with scratch_buf := scr', shrink_stk := sstk' } }
      scr'.length = c.scratch_cap → sstk'.length = c.max_vars → mclr'.length = c.max_vars →
      (∀ i < c.scratch_cap, i < k6PhtHead ∨ L.phtMerged ≤ i →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      ncls.toNat ≤ c.max_vars → M6PartitionOk nv.toNat ncls.toNat scr' sstk' →
      (FullMem c s' ⋆ R) m' → Q (ncls, ()) m'

@[expose] def m6RefinePartitionSpec : Spec [i64, i32, i32] [i32] := fun (h, nv, ncls, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (L : K6Layout) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
    nv.toNat ≤ L.maxV ∧ nv.toNat ≤ c.max_vars ∧ ncls.toNat ≤ c.max_vars ∧
    (∀ i < nv.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
    M6PartitionOk nv.toNat ncls.toNat s.scratch.scratch_buf s.scratch.shrink_stk ∧
    (FullMem c s ⋆ R) m ∧
    ∀ new_n scr' sstk' wsort' m',
      let sc' : FullScratch :=
        { s.scratch with scratch_buf := scr', shrink_stk := sstk', wsort := wsort' }
      let s' : FullState := { s with scratch := sc' }
      scr'.length = c.scratch_cap → sstk'.length = c.max_vars → wsort'.length = 2 * c.max_vars →
      (∀ i < c.scratch_cap, i < k6PhtNext ∨ L.phtMerged ≤ i →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      new_n.toNat ≤ c.max_vars → M6PartitionOk nv.toNat new_n.toNat scr' sstk' →
      (FullMem c s' ⋆ R) m' → Q (new_n, ()) m'

@[expose]
def m6SweepUnitsSpec : Spec [i64, i32, i32, i64] [i64] := fun (h, nv, rbit_in, _tlim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ M6SweepConeOk F_cur s nv.toNat ∧
    rbit_in.toNat ≤ 64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      M6SweepConeOk F_cur s' nv.toNat →
      (r = 0xFFFFFFFFFFFFFFFF#64 → F0.Unsat) →
      (r ≠ 0xFFFFFFFFFFFFFFFF#64 → r.toNat ≤ 64) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def m6SweepClassesSpec : Spec [i64, i32, i32, i64] [i64] :=
  fun (h, nv, rbit_in, _tlim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ M6SweepConeOk F_cur s nv.toNat ∧
      rbit_in.toNat ≤ 64 ∧ (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        s'.scratch.work_stk1 = s.scratch.work_stk1 →
        s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
        s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (r = 1#64 → ∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
          M6EqBufOk F_cur s' (k6StateOfScratch L s'.scratch.scratch_buf).neq.toNat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def m6ElsArSpec : Spec [i64, i32, i32] [.bool] := fun (h, cr, rl, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ cr.toNat ∈ fullArenaClauseRefs s ∧
    rl.toNat < 2 * s.core.cur_vars ∧ M6ReprFlatInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.core.repr = s.core.repr →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def m6ElsLitSpec : Spec [i64, i32, i32] [.bool] := fun (h, l, rl, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ l.toNat < 2 * s.core.cur_vars ∧
    rl.toNat < 2 * s.core.cur_vars ∧ LitEquiv (cnfOfClauses F_cur) l.toNat rl.toNat ∧
    M6ReprFlatInv F_cur (2 * s.core.cur_vars) s.core.repr ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.core.repr = s.core.repr →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def m6ElsFoldSpec : Spec [i64, i32] [.bool] := fun (h, neq, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ M6EqBufOk F_cur s neq.toNat ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      (ok = true → M6ReprFlatInv F_cur (2 * s'.core.cur_vars) s'.core.repr) →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def m6DenseElsSpec : Spec [i64, i32] [.bool] := fun (h, neq, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ M6EqBufOk F_cur s neq.toNat ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      (ok = true ↔ s'.core.inconsistent = 0#64) →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def m6SweepVarSpec : Spec [i64, i32, i64] [i64] := fun (h, root_v, _tlim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ k6MinScr ≤ c.scratch_cap ∧
    root_v.toNat < s.core.cur_vars ∧ M6TmkZero s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → M6TmkZero s' →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose]
def m6CandSiftSpec : Spec [i64, i64, i32, i32] [] := fun (cands_ptr, deg_ptr, start, n, ()) m Q _ =>
  ∃ (cands deg : List (BitVec 32)) (bound : Nat) (R : Mem 64 → Prop),
    start.toNat < n.toNat ∧ n.toNat ≤ cands.length ∧ n.toNat < 2 ^ 31 ∧
    bound ≤ deg.length ∧ (∀ i < n.toNat, (cands[i]?.getD 0#32).toNat < bound) ∧
    (array (t := i32) cands_ptr cands ⋆ array (t := i32) deg_ptr deg ⋆ R) m ∧
    ∀ cands' m',
      cands'.length = cands.length → (∀ i < n.toNat, (cands'[i]?.getD 0#32).toNat < bound) →
      (array (t := i32) cands_ptr cands' ⋆ array (t := i32) deg_ptr deg ⋆ R) m' → Q () m'

@[expose] def m6CollectCandsSpec : Spec [i64] [i32] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ nc trc' ws2' m',
      let s' : FullState :=
        { s with scratch := { s.scratch with tarjan_reach := trc', work_stk2 := ws2' } }
      s'.LengthsOk c → nc.toNat ≤ s.core.cur_vars →
      (∀ i < nc.toNat, (trc'[i]?.getD 0#32).toNat < s.core.cur_vars) →
      (FullMem c s' ⋆ R) m' → Q (nc, ()) m'

@[expose] def m6SweepVarsSpec : Spec [i64, i64, i64] [i64] := fun (h, _budget, _tlim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ M6TmkZero s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInv c F0 s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → M6TmkZero s' →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def m6ExtendPush2Spec : Spec [i64, i32, i32] [.bool] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _blk, _ot, ()) s => h = c.hdr ∧ s.scratch.extend_len ≤ c.extend_cap)
    (fun c _ _ s s' =>
      s'.scratch.last_learned = s.scratch.last_learned ∧ s'.scratch.extend_len ≤ c.extend_cap ∧
      s'.scratch.scratch_buf = s.scratch.scratch_buf ∧
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
      s'.scratch.work_stk1 = s.scratch.work_stk1)

/-! ### `51`-Row Specification Table & Environment (`39` owned + `12` canonical `Full` externs) -/

@[expose] def m6SweepSpecTable : List SpecEntry :=
  [ ⟨"full_m6_max_v", [i64], [i64], m6MaxVSpec, true⟩
  , ⟨"full_k6_add_ticks", [i64, i64], [], k6AddTicksSpec, true⟩
  , ⟨"full_k6_init", [i64, i32], [], k6InitSpec, true⟩
  , ⟨"full_k6_watch", [i64, i32, i32, i32], [], k6WatchSpec, true⟩
  , ⟨"full_k6_assign", [i64, i32, i32], [], k6AssignSpec, true⟩
  , ⟨"full_k6_add_clause", [i64, i64, i32], [.bool], k6AddClauseSpec, true⟩
  , ⟨"full_k6_mtf", [i64, i32], [], k6MtfSpec, true⟩
  , ⟨"full_k6_backtrack", [i64, i32], [], k6BacktrackSpec, true⟩
  , ⟨"full_k6_propagate", [i64], [i32], k6PropagateSpec, true⟩
  , ⟨"full_k6_ana_clause", [i64, i32, i32], [], k6AnaClauseSpec, true⟩
  , ⟨"full_k6_analyze", [i64, i32], [.bool], k6AnalyzeSpec, true⟩
  , ⟨"full_k6_solve", [i64, i64], [i64], k6SolveSpec, true⟩
  , ⟨"full_k6_flip", [i64, i32], [.bool], k6FlipSpec, true⟩
  , ⟨"full_k512_add_live_m6", [i64, i32, i32], [], k6AddLiveSpec, true⟩
  , ⟨"full_m6_dense_prop_lit", [i64, i32], [.bool], m6DensePropLitSpec, true⟩
  , ⟨"full_m6_dense_prop", [i64], [.bool], m6DensePropSpec, true⟩
  , ⟨"full_m6_sweep_cone", [i64, i32], [i64], m6SweepConeSpec, true⟩
  , ⟨"full_m6_sweep_refine_sig", [i64, i32, i32], [], m6SweepRefineSigSpec, true⟩
  , ⟨"full_m6_sweep_rand_phases", [i64, i32], [], m6SweepRandPhasesSpec, true⟩
  , ⟨"full_m6_sweep_solve", [i64, i32, i64], [i64], m6SweepSolveSpec, true⟩
  , ⟨"full_m6_sweep_flip_round", [i64, i32], [i32], m6SweepFlipRoundSpec, true⟩
  , ⟨"full_m6_sweep_sim", [i64, i32, i64], [i32], m6SweepSimSpec, true⟩
  , ⟨"full_m6_sweep_rearm", [i64, i32], [], m6SweepRearmSpec, true⟩
  , ⟨"full_m6_sweep_build_pht", [i64, i32, i64], [], m6SweepBuildPhtSpec, true⟩
  , ⟨"full_m6_extract_pht", [i64, i32, i64], [i32], m6ExtractPhtSpec, true⟩
  , ⟨"full_m6_refine_partition", [i64, i32, i32], [i32], m6RefinePartitionSpec, true⟩
  , ⟨"full_m6_sweep_units", [i64, i32, i32, i64], [i64], m6SweepUnitsSpec, true⟩
  , ⟨"full_m6_sweep_classes", [i64, i32, i32, i64], [i64], m6SweepClassesSpec, true⟩
  , ⟨"full_m6_els_ar", [i64, i32, i32], [.bool], m6ElsArSpec, true⟩
  , ⟨"full_m6_els_lit", [i64, i32, i32], [.bool], m6ElsLitSpec, true⟩
  , ⟨"full_m6_els_fold", [i64, i32], [.bool], m6ElsFoldSpec, true⟩
  , ⟨"full_m6_dense_els", [i64, i32], [.bool], m6DenseElsSpec, true⟩
  , ⟨"full_m6_sweep_var", [i64, i32, i64], [i64], m6SweepVarSpec, true⟩
  , ⟨"full_m6_cand_sift", [i64, i64, i32, i32], [], m6CandSiftSpec, true⟩
  , ⟨"full_m6_collect_cands", [i64], [i32], m6CollectCandsSpec, true⟩
  , ⟨"full_m6_sweep_vars", [i64, i64, i64], [i64], m6SweepVarsSpec, true⟩
  , ⟨"full_m6_sweep_dense", [i64, i64, i64], [i64], m4SweepDenseSpec, true⟩
  , ⟨"full_m6_sweep_sat", [i64, i64, i64], [i64], m4SweepSatSpec, true⟩
  , ⟨"full_sweep_sat_m6", [i64], [i64], Full.fullSweepSatSpec, true⟩
  , ⟨"full_rng_next", [i64], [i64], Full.fullRngNextSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩
  , ⟨"full_assign_lvl", [i64, i32, i32, i32], [], Full.fullAssignLvlSpec, true⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  , ⟨"full_set_inactive", [i64, i32, i32], [], Full.fullSetInactiveSpec, true⟩
  , ⟨"full_extend_push2", [i64, i32, i32], [.bool], m6ExtendPush2Spec, true⟩
  , ⟨"full_add_unit", [i64, i32], [.bool], Full.fullAddUnitSpec, true⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64], Full.fullAddBinSpec, true⟩
  , ⟨"full_enter_dense", [i64], [.bool], Full.fullEnterDenseSpec, true⟩
  , ⟨"full_rebuild_watches", [i64], [i64], Full.fullRebuildWatchesSpec, true⟩
  , ⟨"full_substitute", [i64], [i64], Full.fullSubstituteSpec, true⟩ ]

@[expose] def m6SweepEnv : Env := Env.ofTable m6SweepSpecTable

theorem m6SweepSpecTable_nodup : (m6SweepSpecTable.map SpecEntry.name).Nodup := by decide

theorem m6SweepSpecTable_noExit : ∀ e ∈ m6SweepSpecTable, e.noExit = true := by
  intro e he
  have hall : m6SweepSpecTable.all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem m6SweepSpecTable_sigs :
    (m6SweepSpecTable.take 39).map (fun e => (e.name, e.as, e.rs)) =
      m6Sweep_fns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl

theorem m6SweepSpecTable_ext_sigs :
    (m6SweepSpecTable.drop 39).map (fun e => ⟨e.name, e.as, e.rs⟩) = m6SweepExterns := by
  t_kernel_rfl

theorem m6SweepEnv_noExit :
    ∀ f as bs xs m Q X X',
      m6SweepEnv f as bs xs m Q X → m6SweepEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m6SweepSpecTable_noExit

@[expose] def M6EnvSpec (Γ : Env) (nm : String) {as bs : List Ty} (sp : Spec as bs) : Prop :=
  ∀ args m Q X, sp args m Q X → Γ nm as bs args m Q X

theorem m6SweepEnv_row {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m6SweepSpecTable)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    M6EnvSpec m6SweepEnv nm sp :=
  fun xs m Q X hs =>
    Env.ofTable_of_mem (e := ⟨nm, as, bs, sp, true⟩) hmem m6SweepSpecTable_nodup
      (hno xs m Q X hs)

end LeanQbe.T.Examples.Kissat.FullM6Sweep
