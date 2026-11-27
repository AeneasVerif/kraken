/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.OpsCoreHelpers
public import LeanQbe.T.Examples.Bitblast.Src.OpsCore
import LeanQbe.T.Examples.Bitblast.Proof.DriverHelpers
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0HeadStepGuard
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas

/-!
# Arithmetic & Comparison WP Proofs (`Bitblast.Proof.OpsCore2`)

Proves canonical `Γ`-parametric `Func.wp` theorems for:
- `bv_blast_add_wp`
- `bv_blast_eq_wp`
- `bv_blast_ult_wp`
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open LeanQbe.T
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Src.OpsCore

/-! ## Local Array32 Load/Store Rules -/

@[local c0_load] private theorem oc2_load_lits_add {R : Mem 64 → Prop} {m : Mem 64}
    {a : BitVec 64} {off k : BitVec 32} {xs : List (BitVec 32)}
    (h : (array (t := i32) a xs ⋆ R) m)
    (hwrap : off.toNat + k.toNat < 2 ^ 32) (hi : off.toNat + k.toNat < xs.length) :
    loadVal m i32 (a + BitVec.setWidth 64 (off + k) * 4) =
      some (xs[off.toNat + k.toNat]'hi) :=
  ops_load_array32_u32_add_mul4 h hwrap hi

@[local c0_store] private theorem oc2_store_lits_add {R : Mem 64 → Prop} {m : Mem 64}
    {a : BitVec 64} {off k : BitVec 32} {xs : List (BitVec 32)} (v : BitVec 32)
    (h : (array (t := i32) a xs ⋆ R) m)
    (hwrap : off.toNat + k.toNat < 2 ^ 32) (hi : off.toNat + k.toNat < xs.length) :
    storeOk m i32 (a + BitVec.setWidth 64 (off + k) * 4) ∧
      (array (t := i32) a (xs.set (off.toNat + k.toNat) v) ⋆ R)
        (storeMem m i32 (a + BitVec.setWidth 64 (off + k) * 4) v) :=
  ops_store_array32_u32_add_mul4 v h hwrap hi

/-! ## Local Frame, Separation & BitVec Helpers -/

private theorem oc2_aig_le_refl (g : Ref.Aig) : g ≤ g :=
  ⟨rfl, Nat.le_refl _, fun _ hi => Array.getElem?_eq_getElem hi⟩

private theorem oc2_aigFrame_refl (h : BVHdrState) : h.AigFrame h :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl⟩

private theorem oc2_sep5_emp_all {A B C D R : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ (C ⋆ (D ⋆ (R ⋆ Std.ExtHashMap.emp))))) m) : (A ⋆ B ⋆ C ⋆ D ⋆ R) m :=
  (by simp only [Std.ExtHashMap.sep_emp]; ac_rfl :
    (A ⋆ (B ⋆ (C ⋆ (D ⋆ (R ⋆ Std.ExtHashMap.emp))))) = (A ⋆ B ⋆ C ⋆ D ⋆ R)) ▸ h

private theorem oc2_bv_carry_zero {w : Nat} (a b : BitVec w) (c : Bool) :
    BitVec.carry 0 a b c = c := by
  cases c <;> simp [BitVec.carry, Nat.mod_one]

private theorem oc2_xor1_rshift1 (x : BitVec 32) :
    ((x ^^^ 1#32) >>> 1).toNat = (x >>> 1).toNat := by
  have heq : (x ^^^ 1#32) >>> 1 = x >>> 1 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    have hbit : (1#32 : BitVec 32).getLsbD (1 + i) = false := by
      simp only [BitVec.getLsbD, BitVec.toNat_ofNat, Nat.testBit, Nat.shiftRight_eq_div_pow]
      rw [Nat.mod_eq_of_lt (by decide),
        Nat.div_eq_of_lt (Nat.one_lt_two_pow (by omega))]
      decide
    rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor, hbit,
      Bool.xor_false]
  rw [heq]

private theorem oc2_decide_forall_lt_succ {j : Nat} {P : Nat → Prop}
    [∀ i, Decidable (P i)] :
    decide (∀ i < j + 1, P i) = (decide (∀ i < j, P i) && decide (P j)) := by
  by_cases h1 : ∀ i < j, P i
  · by_cases h2 : P j
    · have h3 : ∀ i < j + 1, P i := fun i hi => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · exact h1 i hlt
        · exact h2
      rw [decide_eq_true h1, decide_eq_true h2, decide_eq_true h3]; rfl
    · have h3 : ¬ ∀ i < j + 1, P i := fun hall => h2 (hall j (Nat.lt_succ_self j))
      rw [decide_eq_true h1, decide_eq_false h2, decide_eq_false h3]; rfl
  · have h3 : ¬ ∀ i < j + 1, P i := fun hall =>
      h1 fun i hi => hall i (Nat.lt_trans hi (Nat.lt_succ_self j))
    rw [decide_eq_false h1, decide_eq_false h3]; rfl

private theorem oc2_sliceDenotes_bit {g : Ref.Aig} {ρ : Nat → Bool}
    {xs : List (BitVec 32)} {off w i : Nat} {v : BitVec w}
    (hle : off + w ≤ xs.length) (hi : i < w)
    (hden : SliceDenotes g ρ (litsSlice xs off w) v) :
    g.evalLit ρ (UInt32.ofBitVec (xs.getD (off + i) 0#32)) = v.getLsbD i :=
  (sliceDenotes_iff hle).mp hden i hi

/-! ## 1. `bv_blast_add` Helpers & WP Proof -/

private structure AddSt where
  cin : BitVec 32
  j : BitVec 32
  hdr : BVHdrState
  g : Ref.Aig
  aigW : List (BitVec 64)
  htS : List (BitVec 32)
  xs : List (BitVec 32)

private def AddInv (a_off b_off w : BitVec 32) (hdr0 : BVHdrState) (g0 : Ref.Aig)
    (lits0 : List (BitVec 32)) (st : AddSt) : Prop :=
  st.j.toNat ≤ w.toNat ∧
  hdr0.BlastFrame st.hdr ∧
  st.hdr.lits_len = hdr0.lits_len + w ∧
  st.hdr.oom = 0#32 ∧
  g0 ≤ st.g ∧
  st.g.nodes.size ≤ g0.nodes.size + 12 * st.j.toNat ∧
  AigInv st.hdr st.g st.aigW st.htS ∧
  st.xs.length = lits0.length ∧
  (∀ i < hdr0.lits_len.toNat, st.xs.getD i 0#32 = lits0.getD i 0#32) ∧
  (st.cin >>> 1).toNat < st.hdr.aig_len.toNat ∧
  (st.j.toNat < w.toNat → ∀ (ρ : Nat → Bool) (vA vB : BitVec w.toNat),
    SliceDenotes g0 ρ (litsSlice lits0 a_off.toNat w.toNat) vA →
    SliceDenotes g0 ρ (litsSlice lits0 b_off.toNat w.toNat) vB →
    st.g.evalLit ρ (UInt32.ofBitVec st.cin) = BitVec.carry st.j.toNat vA vB false) ∧
  SliceAigWf st.hdr.aig_len.toNat st.xs hdr0.lits_len.toNat st.j.toNat ∧
  ∀ i < st.j.toNat, ∀ (ρ : Nat → Bool) (vA vB : BitVec w.toNat),
    SliceDenotes g0 ρ (litsSlice lits0 a_off.toNat w.toNat) vA →
    SliceDenotes g0 ρ (litsSlice lits0 b_off.toNat w.toNat) vB →
    st.g.evalLit ρ (UInt32.ofBitVec (st.xs.getD (hdr0.lits_len.toNat + i) 0#32)) =
      (vA + vB).getLsbD i

private theorem add_oom_exit {h : BitVec 64} {a_off b_off w : BitVec 32}
    {hdr hdr1 hdr2 : BVHdrState} {g g1 g2 : Ref.Aig}
    {aig2 : List (BitVec 64)} {ht2 xs lits0 : List (BitVec 32)}
    {m2 : Mem 64} {R : Mem 64 → Prop} {Q : (BitVec 32 × PUnit) → Mem 64 → Prop}
    {j k : Nat}
    (hjlt : j < w.toNat) (hk12 : k ≤ 12)
    (hroom : w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat)
    (hfr0 : hdr.BlastFrame hdr2) (hlen2 : hdr2.lits_len = hdr.lits_len + w)
    (hgg01 : g ≤ g1) (hfr01 : hdr.BlastFrame hdr1) (ho1 : hdr1.oom = 0#32)
    (hsz1 : g1.nodes.size ≤ g.nodes.size + 12 * j)
    (hgg12 : g1 ≤ g2) (hsz2 : g2.nodes.size ≤ g1.nodes.size + k)
    (hinv2 : AigInv hdr2 g2 aig2 ht2)
    (hxlen : xs.length = lits0.length)
    (hpref : ∀ i < hdr.lits_len.toNat, xs.getD i 0#32 = lits0.getD i 0#32)
    (hne : hdr2.oom ≠ 0#32)
    (hok : hdr1.oom = 0#32 → g1.A + 1 + g1.nodes.size + k ≤ hdr1.aig_cap.toNat →
      g1.nodes.size + k ≤ bvMaxGates → hdr2.oom = 0#32)
    (hm2 : (bvHdrMem h hdr2 ⋆ array64 hdr2.aig_ptr aig2 ⋆
      array (t := i32) hdr2.ht_ptr ht2 ⋆ array (t := i32) hdr2.lits_ptr xs ⋆ R) m2)
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Ref.Aig)
      (aig' : List (BitVec 64)) (ht' lits' : List (BitVec 32)) (m' : Mem 64),
      hdr.BlastFrame hdr' → g ≤ g' → g'.nodes.size ≤ g.nodes.size + 12 * w.toNat →
      AigInv hdr' g' aig' ht' → lits'.length = lits0.length →
      (∀ i < hdr.lits_len.toNat, lits'.getD i 0#32 = lits0.getD i 0#32) →
      hdr.lits_len.toNat ≤ hdr'.lits_len.toNat →
      hdr'.lits_len.toNat ≤ hdr.lits_len.toNat + w.toNat →
      (hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
        hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat) →
      (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
      (hdr.oom = 0#32 → sliceBoundsOk hdr a_off w = true →
        sliceBoundsOk hdr b_off w = true →
        w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat →
        g.A + 1 + g.nodes.size + 12 * w.toNat ≤ hdr.aig_cap.toNat →
        g.nodes.size + 12 * w.toNat ≤ bvMaxGates → hdr'.oom = 0#32) →
      (hdr'.oom = 0#32 → hdr.oom = 0#32 ∧ sliceBoundsOk hdr a_off w = true ∧
        sliceBoundsOk hdr b_off w = true ∧
        w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat ∧
        ret = hdr.lits_len ∧ hdr'.lits_len = hdr.lits_len + w ∧
        SliceAigWf hdr'.aig_len.toNat lits' ret.toNat w.toNat ∧
        ∀ (ρ : Nat → Bool) (vA vB : BitVec w.toNat),
          SliceDenotes g ρ (litsSlice lits0 a_off.toNat w.toNat) vA →
          SliceDenotes g ρ (litsSlice lits0 b_off.toNat w.toNat) vB →
          SliceDenotes g' ρ (litsSlice lits' ret.toNat w.toNat) (vA + vB)) →
      (hdr'.oom ≠ 0#32 → ret = 0xFFFFFFFF#32) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aig' ⋆
        array (t := i32) hdr'.ht_ptr ht' ⋆ array (t := i32) hdr'.lits_ptr lits' ⋆ R) m' →
      Q (ret, ⟨⟩) m') :
    Q (0xFFFFFFFF#32, ⟨⟩) m2 := by
  have hmul : 12 * (j + 1) ≤ 12 * w.toNat := Nat.mul_le_mul_left 12 (by omega)
  rw [Nat.mul_succ] at hmul
  have hlen_le : hdr.lits_len.toNat ≤ hdr2.lits_len.toNat := by
    have := hdr.lits_cap.isLt
    rw [hlen2, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    omega
  have hlen_sum : hdr2.lits_len.toNat ≤ hdr.lits_len.toNat + w.toNat := by
    rw [hlen2, BitVec.toNat_add]; exact Nat.mod_le _ _
  refine hQ 0xFFFFFFFF#32 hdr2 g2 aig2 ht2 xs m2 hfr0 (Ref.Aig.extends_trans hgg01 hgg12)
    (by omega) hinv2 hxlen hpref hlen_le hlen_sum
    (fun _ => by rw [hfr0.lits_cap]; omega) (fun _ => hne) ?_
    (fun h0' => absurd h0' hne) (fun _ => rfl) hm2
  intro _ _ _ _ haig_cap hmaxg
  apply hok ho1
  · rw [← hgg01.1, hfr01.aig_cap]; omega
  · omega

private def AddCarryJoinPred (h : BitVec 64) (a_off b_off w : BitVec 32)
    (hdr0 : BVHdrState) (g0 : Ref.Aig) (lits0 : List (BitVec 32))
    (j : BitVec 32) (xs' : List (BitVec 32))
    (st_g g2 : Ref.Aig) (R : Mem 64 → Prop) : Tup Val [i32] → Mem 64 → Prop :=
  fun (nc, ⟨⟩) ml =>
    ∃ hdr3 g3 aig3 ht3,
      hdr0.BlastFrame hdr3 ∧
      hdr3.lits_len = hdr0.lits_len + w ∧
      hdr3.oom = 0#32 ∧
      g2 ≤ g3 ∧
      g3.nodes.size ≤ st_g.nodes.size + 12 ∧
      AigInv hdr3 g3 aig3 ht3 ∧
      (nc >>> 1).toNat < hdr3.aig_len.toNat ∧
      (j.toNat + 1 < w.toNat → ∀ (ρ : Nat → Bool) (vA vB : BitVec w.toNat),
        SliceDenotes g0 ρ (litsSlice lits0 a_off.toNat w.toNat) vA →
        SliceDenotes g0 ρ (litsSlice lits0 b_off.toNat w.toNat) vB →
        g3.evalLit ρ (UInt32.ofBitVec nc) = BitVec.carry (j.toNat + 1) vA vB false) ∧
      (bvHdrMem h hdr3 ⋆ array64 hdr3.aig_ptr aig3 ⋆
        array (t := i32) hdr3.ht_ptr ht3 ⋆ array (t := i32) hdr3.lits_ptr xs' ⋆ R) ml

private theorem addInv_step {a_off b_off w : BitVec 32}
    {hdr0 : BVHdrState} {g0 : Ref.Aig} {lits0 : List (BitVec 32)} {st : AddSt}
    {hdr2 hdr3 : BVHdrState} {g2 g3 : Ref.Aig}
    {aig2 aig3 : List (BitVec 64)} {ht2 ht3 : List (BitVec 32)} {sum2 nc : BitVec 32}
    (_hle_a : a_off.toNat + w.toNat ≤ lits0.length)
    (_hle_b : b_off.toNat + w.toNat ≤ lits0.length)
    (hinv : AddInv a_off b_off w hdr0 g0 lits0 st)
    (_hlt : st.j.toNat < w.toNat) (hi_out : hdr0.lits_len.toNat + st.j.toNat < st.xs.length)
    (hgg2 : st.g ≤ g2) (hinv2 : AigInv hdr2 g2 aig2 ht2)
    (hsum_lt : (sum2 >>> 1).toNat < hdr2.aig_len.toNat)
    (hsum_ev : ∀ (ρ : Nat → Bool) (vA vB : BitVec w.toNat),
      SliceDenotes g0 ρ (litsSlice lits0 a_off.toNat w.toNat) vA →
      SliceDenotes g0 ρ (litsSlice lits0 b_off.toNat w.toNat) vB →
      g2.evalLit ρ (UInt32.ofBitVec sum2) = (vA + vB).getLsbD st.j.toNat)
    (hfr3 : hdr0.BlastFrame hdr3) (hlen3 : hdr3.lits_len = hdr0.lits_len + w)
    (ho3 : hdr3.oom = 0#32) (hgg23 : g2 ≤ g3)
    (_hsz3 : g3.nodes.size ≤ st.g.nodes.size + 12) (hinv3 : AigInv hdr3 g3 aig3 ht3)
    (hnc_lt : (nc >>> 1).toNat < hdr3.aig_len.toNat)
    (hnc_ev : st.j.toNat + 1 < w.toNat → ∀ (ρ : Nat → Bool) (vA vB : BitVec w.toNat),
      SliceDenotes g0 ρ (litsSlice lits0 a_off.toNat w.toNat) vA →
      SliceDenotes g0 ρ (litsSlice lits0 b_off.toNat w.toNat) vB →
      g3.evalLit ρ (UInt32.ofBitVec nc) = BitVec.carry (st.j.toNat + 1) vA vB false) :
    (st.j + 1#32).toNat = st.j.toNat + 1 ∧
      AddInv a_off b_off w hdr0 g0 lits0
        { cin := nc, j := st.j + 1#32, hdr := hdr3, g := g3, aigW := aig3, htS := ht3,
          xs := st.xs.set (hdr0.lits_len.toNat + st.j.toNat) sum2 } := by
  have hj1 : (st.j + 1#32).toNat = st.j.toNat + 1 := by
    have := w.isLt
    rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hlen23 := aigInv_aigLen_mono hinv2 hinv3 hgg23
  have hgg_s3 := Ref.Aig.extends_trans hgg2 hgg23
  have hlen_s3 := aigInv_aigLen_mono hinv.2.2.2.2.2.2.1 hinv3 hgg_s3
  refine ⟨hj1, by dsimp only; omega, hfr3, hlen3, ho3,
    Ref.Aig.extends_trans hinv.2.2.2.2.1 hgg_s3,
    by dsimp only; have := hinv.2.2.2.2.2.1; rw [hj1, Nat.mul_succ]; omega,
    hinv3, by simp [hinv.2.2.2.2.2.2.2.1], ?_, hnc_lt, ?_, ?_, ?_⟩
  · intro i hi; rw [list_getD_set_ne st.xs 0#32 _ (by omega)]
    exact hinv.2.2.2.2.2.2.2.2.1 i hi
  · intro hj1lt ρ vA vB hdA hdB
    dsimp only at hj1lt ⊢; rw [hj1] at hj1lt ⊢
    exact hnc_ev hj1lt ρ vA vB hdA hdB
  · intro i hi
    by_cases hie : i = st.j.toNat
    · subst hie; rw [list_getD_set_self st.xs 0#32 _ hi_out]
      exact Nat.lt_of_lt_of_le hsum_lt hlen23
    · rw [list_getD_set_ne st.xs 0#32 _ (by omega)]
      exact Nat.lt_of_lt_of_le (hinv.2.2.2.2.2.2.2.2.2.2.2.1 i (by dsimp only at hi; omega))
        hlen_s3
  · intro i hi ρ vA vB hdA hdB
    by_cases hie : i = st.j.toNat
    · subst hie
      rw [list_getD_set_self st.xs 0#32 _ hi_out,
        evalLit_extend_of_lt hinv2 hgg23 hsum_lt ρ, hsum_ev ρ vA vB hdA hdB]
    · rw [list_getD_set_ne st.xs 0#32 _ (by omega)]
      have hlt_i : i < st.j.toNat := by dsimp only at hi; omega
      have hext := sliceAigWf_evalLit_extend hinv.2.2.2.2.2.2.1 hgg_s3
        hinv.2.2.2.2.2.2.2.2.2.2.2.1 (off := hdr0.lits_len.toNat) ρ hlt_i
      rw [hext]
      exact hinv.2.2.2.2.2.2.2.2.2.2.2.2 i hlt_i ρ vA vB hdA hdB

public section

theorem bv_blast_add_wp (Γ : Env)
    (hSliceOk : ∀ xs m Q X, bvSliceOkSpec xs m Q X →
      Γ "bv_slice_ok" [i64, i32, i32] [.bool] xs m Q X)
    (hLitsAlloc : ∀ xs m Q X, bvLitsAllocSpec xs m Q X →
      Γ "bv_lits_alloc" [i64, i32] [i32] xs m Q X)
    (hAigXor : ∀ xs m Q X, bvAigXorSpec xs m Q X →
      Γ "bv_aig_xor" [i64, i32, i32] [i32] xs m Q X)
    (hFac : ∀ xs m Q X, bvFullAdderCarrySpec xs m Q X →
      Γ "bv_full_adder_carry" [i64, i32, i32, i32] [i32] xs m Q X) :
    ∀ xs m Q X, bvBlastAddSpec xs m Q X →
      Func.wp Γ bv_blast_add_body xs m Q X := by
  rintro ⟨h, a_off, b_off, w, ⟨⟩⟩ m Q X
    ⟨hdr, g, aigW, htS, lits0, R, hinv0, hlits_cap, hwf, hm, hQ⟩
  refine wp_join_group (ts := [])
    (fun _ ml => ml = m ∧ ¬ (hdr.oom = 0#32 ∧
      sliceBoundsOk hdr a_off w = true ∧ sliceBoundsOk hdr b_off w = true))
    (fun _ _ ml ⟨hml, hfail⟩ => by
      subst hml
      c0_hstraight
      let hdr' : BVHdrState := { hdr with oom := (1 : BitVec 32) }
      have hfr : hdr.BlastFrame hdr' :=
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact hQ 0xFFFFFFFF#32 hdr' g aigW htS lits0 _ hfr (oc2_aig_le_refl g)
        (Nat.le_add_right _ _) (aigInv_set_oom (1 : BitVec 32) hinv0) rfl (fun _ _ => rfl)
        (Nat.le_refl _) (Nat.le_add_right _ _) id (fun _ => by simp [hdr'])
        (fun h0 h1 h2 _ _ _ => False.elim (hfail ⟨h0, h1, h2⟩))
        (fun h0 => False.elim (by simp [hdr'] at h0)) (fun _ => rfl) (oc2_sep5_emp_all hm))
    (fun J hJ => by
      c0_hstraight
      c0_hsplit
      · exact hJ () m ⟨rfl, fun ⟨h0, _⟩ => hc h0⟩
      · have h0 : hdr.oom = 0#32 := by bv_omega
        clear hc
        c0_hcall hSliceOk
        · refine ⟨hdr, array64 hdr.aig_ptr aigW ⋆ array (t := i32) hdr.ht_ptr htS ⋆
              array (t := i32) hdr.lits_ptr lits0 ⋆ R, ops_sep5_hdr_focus hm, ?_⟩
          dsimp only [Arg.val]
          c0_hsplit
          · have hsA : sliceBoundsOk hdr a_off w = true := hc
            obtain ⟨hsA_cap, _, hsA_sum⟩ := sliceBoundsOk_sum hsA
            clear hc
            c0_hcall hSliceOk
            · refine ⟨hdr, array64 hdr.aig_ptr aigW ⋆ array (t := i32) hdr.ht_ptr htS ⋆
                  array (t := i32) hdr.lits_ptr lits0 ⋆ R, ops_sep5_hdr_focus hm, ?_⟩
              dsimp only [Arg.val]
              c0_hsplit
              · have hsB : sliceBoundsOk hdr b_off w = true := hc
                obtain ⟨_, _, hsB_sum⟩ := sliceBoundsOk_sum hsB
                clear hc
                obtain ⟨hwfA, hwfB⟩ := hwf h0 hsA hsB
                c0_hcall hLitsAlloc
                · refine ⟨hdr, array64 hdr.aig_ptr aigW ⋆ array (t := i32) hdr.ht_ptr htS ⋆
                      array (t := i32) hdr.lits_ptr lits0 ⋆ R, ops_sep5_hdr_focus hm, ?_⟩
                  dsimp only [Arg.val]
                  split
                  · next hroom =>
                    intro m1 hm1
                    obtain ⟨_, _, hroom'⟩ := hroom
                    let hdr1 : BVHdrState := { hdr with lits_len := hdr.lits_len + w }
                    have hm1' : (bvHdrMem h hdr1 ⋆ array64 hdr1.aig_ptr aigW ⋆
                        array (t := i32) hdr1.ht_ptr htS ⋆
                        array (t := i32) hdr1.lits_ptr lits0 ⋆ R) m1 :=
                      ops_sep5_hdr_unfocus hm1
                    c0_hstraight
                    c0_hsplit
                    · exfalso; exact hc h0
                    · c0_hstraight
                      have hfr1 : hdr.BlastFrame hdr1 :=
                        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                          rfl, rfl, rfl, rfl, rfl, rfl⟩
                      have hinv1 := aigInv_set_litsLen (hdr.lits_len + w) hinv0
                      refine wp_while_record
                        (proj := fun st : AddSt => (st.cin, st.j, ⟨⟩))
                        (μ := fun st => w.toNat - st.j.toNat)
                        (Inv := AddInv a_off b_off w hdr g lits0)
                        (MemPred := fun st => bvHdrMem h st.hdr ⋆
                          array64 st.hdr.aig_ptr st.aigW ⋆
                          array (t := i32) st.hdr.ht_ptr st.htS ⋆
                          array (t := i32) st.hdr.lits_ptr st.xs)
                        (R := R)
                        (fun Jw hJw => by
                          c0_hstraight
                          have hz : (0#32 : BitVec 32).toNat = 0 := rfl
                          refine hJw ⟨0#32, 0#32, hdr1, g, aigW, htS, lits0⟩ m1 ?_ hm1'
                          refine ⟨by dsimp only; rw [hz]; omega, hfr1, rfl, h0,
                            oc2_aig_le_refl g, by dsimp only; rw [hz]; omega, hinv1, rfl,
                            fun _ _ => rfl, by dsimp only; exact aigInv_false_lit_bound hinv1,
                            ?_, fun i hi => by dsimp only at hi; rw [hz] at hi; omega,
                            fun i hi => by dsimp only at hi; rw [hz] at hi; omega⟩
                          intro _ ρ vA vB _ _
                          dsimp only
                          rw [hz, evalLit_zero, oc2_bv_carry_zero])
                        (fun Jw st ml2 hinv hml2 hrec => by
                          dsimp only [Blocks.get_here] at *
                          c0_hstraight
                          c0_hsplit
                          · have hlt : st.j.toNat < w.toNat := hc
                            clear hc
                            have hwa : a_off.toNat + st.j.toNat < 2 ^ 32 := by
                              have := hdr.lits_len.isLt; omega
                            have hia : a_off.toNat + st.j.toNat < st.xs.length := by
                              have := hinv.2.2.2.2.2.2.2.1; omega
                            have hwb : b_off.toNat + st.j.toNat < 2 ^ 32 := by
                              have := hdr.lits_len.isLt; omega
                            have hib : b_off.toNat + st.j.toNat < st.xs.length := by
                              have := hinv.2.2.2.2.2.2.2.1; omega
                            have hwo : hdr.lits_len.toNat + st.j.toNat < 2 ^ 32 := by
                              have := hdr.lits_cap.isLt; omega
                            have hio : hdr.lits_len.toNat + st.j.toNat < st.xs.length := by
                              have := hinv.2.2.2.2.2.2.2.1; omega
                            have hml2_l : (array (t := i32) hdr.lits_ptr st.xs ⋆
                                (bvHdrMem h st.hdr ⋆ array64 st.hdr.aig_ptr st.aigW ⋆
                                  array (t := i32) st.hdr.ht_ptr st.htS ⋆ R)) ml2 := by
                              have h0l := ops_sep5_lits_focus hml2
                              rwa [hinv.2.1.lits_ptr] at h0l
                            c0_hstraight
                            have hml2_r : (bvHdrMem h st.hdr ⋆ array64 st.hdr.aig_ptr st.aigW ⋆
                                array (t := i32) st.hdr.ht_ptr st.htS ⋆
                                array (t := i32) st.hdr.lits_ptr st.xs ⋆ R) ml2 := by
                              rw [← hinv.2.1.lits_ptr] at hml2_l
                              exact ops_sep5_lits_unfocus hml2_l
                            rw [ops_list_getElem_eq_getD st.xs 0#32 _
                                (ops_setWidth64_add_u32 hwa),
                              ops_list_getElem_eq_getD st.xs 0#32 _
                                (ops_setWidth64_add_u32 hwb)]
                            have hlen0 := aigInv_aigLen_mono hinv0 hinv.2.2.2.2.2.2.1
                              hinv.2.2.2.2.1
                            have ha_lt : (st.xs.getD (a_off.toNat + st.j.toNat) 0#32 >>> 1).toNat <
                                st.hdr.aig_len.toNat := by
                              rw [hinv.2.2.2.2.2.2.2.2.1 _ (by omega)]
                              exact Nat.lt_of_lt_of_le (hwfA _ hlt) hlen0
                            have hb_lt : (st.xs.getD (b_off.toNat + st.j.toNat) 0#32 >>> 1).toNat <
                                st.hdr.aig_len.toNat := by
                              rw [hinv.2.2.2.2.2.2.2.2.1 _ (by omega)]
                              exact Nat.lt_of_lt_of_le (hwfB _ hlt) hlen0
                            c0_hcall hAigXor
                            · refine ⟨st.hdr, st.g, st.aigW, st.htS,
                                  array (t := i32) st.hdr.lits_ptr st.xs ⋆ R,
                                  hinv.2.2.2.2.2.2.1, fun _ => ⟨ha_lt, hb_lt⟩,
                                  ops_sep5_aig_focus hml2_r, ?_⟩
                              intro s1 hdr_x g_x aig_x ht_x m_x hfr_x hgg_x hsz_x hinv_x _
                                hok_x hpost_x hm_x
                              dsimp only [Arg.val]
                              have hm_x' := ops_sep5_aig_unfocus hm_x
                              rw [← hfr_x.lits_ptr] at hm_x'
                              c0_hstraight
                              c0_hsplit
                              · c0_hstraight
                                exact add_oom_exit (k := 3) hlt (by decide) hroom'
                                  (hinv.2.1.trans hfr_x.toBlastFrame)
                                  (hfr_x.lits_len.trans hinv.2.2.1) hinv.2.2.2.2.1 hinv.2.1
                                  hinv.2.2.2.1 hinv.2.2.2.2.2.1 hgg_x hsz_x hinv_x
                                  hinv.2.2.2.2.2.2.2.1 hinv.2.2.2.2.2.2.2.2.1 hc
                                  (fun ho hcap hmg => hok_x ho hcap hmg) hm_x' hQ
                              · have ho_x : hdr_x.oom = 0#32 := by bv_omega
                                clear hc
                                obtain ⟨hs1_lt, hs1_ev⟩ := hpost_x ho_x
                                have hlen_sx := aigInv_aigLen_mono hinv.2.2.2.2.2.2.1 hinv_x hgg_x
                                c0_hcall hAigXor
                                · refine ⟨hdr_x, g_x, aig_x, ht_x,
                                      array (t := i32) hdr_x.lits_ptr st.xs ⋆ R, hinv_x,
                                      fun _ => ⟨hs1_lt, Nat.lt_of_lt_of_le
                                        hinv.2.2.2.2.2.2.2.2.2.1 hlen_sx⟩,
                                      ops_sep5_aig_focus hm_x', ?_⟩
                                  intro s2 hdr2 g2 aig2 ht2 m2 hfr2 hgg2 hsz2 hinv2 _ hok2
                                    hpost2 hm2
                                  dsimp only [Arg.val]
                                  have hm2' := ops_sep5_aig_unfocus hm2
                                  rw [← hfr2.lits_ptr] at hm2'
                                  c0_hstraight
                                  c0_hsplit
                                  · c0_hstraight
                                    exact add_oom_exit (k := 6) hlt (by decide) hroom'
                                      ((hinv.2.1.trans hfr_x.toBlastFrame).trans
                                        hfr2.toBlastFrame)
                                      (hfr2.lits_len.trans (hfr_x.lits_len.trans hinv.2.2.1))
                                      hinv.2.2.2.2.1 hinv.2.1 hinv.2.2.2.1 hinv.2.2.2.2.2.1
                                      (Ref.Aig.extends_trans hgg_x hgg2) (by omega) hinv2
                                      hinv.2.2.2.2.2.2.2.1 hinv.2.2.2.2.2.2.2.2.1 hc
                                      (fun _ _ _ => by
                                        apply hok2 ho_x
                                        · rw [← hgg_x.1, hfr_x.aig_cap]; omega
                                        · omega)
                                      hm2' hQ
                                  · have ho2 : hdr2.oom = 0#32 := by bv_omega
                                    clear hc
                                    obtain ⟨hs2_lt, hs2_ev⟩ := hpost2 ho2
                                    have hfr02 := (hinv.2.1.trans hfr_x.toBlastFrame).trans
                                      hfr2.toBlastFrame
                                    have hlen02 : hdr2.lits_len = hdr.lits_len + w :=
                                      hfr2.lits_len.trans (hfr_x.lits_len.trans hinv.2.2.1)
                                    have hgg_s2 := Ref.Aig.extends_trans hgg_x hgg2
                                    have hm2_l : (array (t := i32) hdr.lits_ptr st.xs ⋆
                                        (bvHdrMem h hdr2 ⋆ array64 hdr2.aig_ptr aig2 ⋆
                                          array (t := i32) hdr2.ht_ptr ht2 ⋆ R)) m2 := by
                                      have h0l := ops_sep5_lits_focus hm2'
                                      rwa [hfr02.lits_ptr] at h0l
                                    c0_hstraight
                                    let xs' := st.xs.set (hdr.lits_len.toNat + st.j.toNat) s2
                                    have hml3 : (bvHdrMem h hdr2 ⋆ array64 hdr2.aig_ptr aig2 ⋆
                                        array (t := i32) hdr2.ht_ptr ht2 ⋆
                                        array (t := i32) hdr2.lits_ptr xs' ⋆ R) m := by
                                      rw [← hfr02.lits_ptr] at hm
                                      rw [ops_setWidth64_add_u32 hwo] at hm
                                      exact ops_sep5_lits_unfocus hm
                                    have hsum_ev : ∀ (ρ : Nat → Bool) (vA vB : BitVec w.toNat),
                                        SliceDenotes g ρ (litsSlice lits0 a_off.toNat w.toNat)
                                          vA →
                                        SliceDenotes g ρ (litsSlice lits0 b_off.toNat w.toNat)
                                          vB →
                                        g2.evalLit ρ (UInt32.ofBitVec s2) =
                                          (vA + vB).getLsbD st.j.toNat := by
                                      intro ρ vA vB hdA hdB
                                      have hla_eq :
                                          st.g.evalLit ρ (UInt32.ofBitVec
                                            (st.xs.getD (a_off.toNat + st.j.toNat) 0#32)) =
                                          vA.getLsbD st.j.toNat := by
                                        rw [hinv.2.2.2.2.2.2.2.2.1 _ (by omega),
                                          sliceAigWf_evalLit_extend hinv0 hinv.2.2.2.2.1 hwfA ρ hlt,
                                          oc2_sliceDenotes_bit (by omega) hlt hdA]
                                      have hlb_eq :
                                          st.g.evalLit ρ (UInt32.ofBitVec
                                            (st.xs.getD (b_off.toNat + st.j.toNat) 0#32)) =
                                          vB.getLsbD st.j.toNat := by
                                        rw [hinv.2.2.2.2.2.2.2.2.1 _ (by omega),
                                          sliceAigWf_evalLit_extend hinv0 hinv.2.2.2.2.1 hwfB ρ hlt,
                                          oc2_sliceDenotes_bit (by omega) hlt hdB]
                                      rw [hs2_ev ρ, hs1_ev ρ,
                                        evalLit_extend_of_lt hinv.2.2.2.2.2.2.1 hgg_x
                                          hinv.2.2.2.2.2.2.2.2.2.1 ρ,
                                        hla_eq, hlb_eq,
                                        hinv.2.2.2.2.2.2.2.2.2.2.1 hlt ρ vA vB hdA hdB]
                                      dsimp only
                                      rw [Bool.xor_assoc, ← BitVec.getLsbD_add hlt]
                                    refine wp_join_group (ts := [i32])
                                      (AddCarryJoinPred h a_off b_off w hdr g lits0 st.j xs'
                                        st.g g2 R)
                                      (fun Jc ⟨nc, ⟨⟩⟩ mlc ⟨hdr3, g3, aig3, ht3, hfr3, hlen3,
                                          ho3, hgg23, hsz3, hinv3, hnc_lt, hnc_ev, hmlc⟩ => by
                                        dsimp only [Blocks.get_here]
                                        c0_hstraight
                                        obtain ⟨hj1, hinv'⟩ := addInv_step (by omega) (by omega)
                                          hinv hlt hio hgg_s2 hinv2 hs2_lt hsum_ev hfr3 hlen3 ho3
                                          hgg23 hsz3 hinv3 hnc_lt hnc_ev
                                        exact hrec ⟨nc, st.j + 1#32, hdr3, g3, aig3, ht3, xs'⟩ mlc
                                          (by dsimp only; omega) hinv' hmlc)
                                      (fun Jc hJc => by
                                        c0_hstraight
                                        c0_hsplit
                                        · have hj1_lt : st.j.toNat + 1 < w.toNat := by
                                            have := w.isLt
                                            have h1 : (st.j + 1#32).toNat = st.j.toNat + 1 := by
                                              rw [BitVec.toNat_add,
                                                show (1#32 : BitVec 32).toNat = 1 from rfl,
                                                Nat.mod_eq_of_lt (by omega)]
                                            rw [← h1]; exact hc
                                          clear hc
                                          have hlen_s2 := aigInv_aigLen_mono hinv.2.2.2.2.2.2.1
                                            hinv2 hgg_s2
                                          c0_hcall hFac
                                          · refine ⟨hdr2, g2, aig2, ht2,
                                                array (t := i32) hdr2.lits_ptr xs' ⋆ R, hinv2,
                                                fun _ => ⟨Nat.lt_of_lt_of_le ha_lt hlen_s2,
                                                  Nat.lt_of_lt_of_le hb_lt hlen_s2,
                                                  Nat.lt_of_lt_of_le hinv.2.2.2.2.2.2.2.2.2.1
                                                    hlen_s2⟩,
                                                ops_sep5_aig_focus hml3, ?_⟩
                                            intro nc hdr3 g3 aig3 ht3 mlc hfr3 hgg23 hsz3 hinv3
                                              _ hok3 hpost3 _ hmlc
                                            dsimp only [Arg.val]
                                            have hmlc' := ops_sep5_aig_unfocus hmlc
                                            rw [← hfr3.lits_ptr] at hmlc'
                                            c0_hstraight
                                            c0_hsplit
                                            · c0_hstraight
                                              refine add_oom_exit (k := 12) hlt (by decide) hroom'
                                                (hfr02.trans hfr3.toBlastFrame)
                                                (hfr3.lits_len.trans hlen02) hinv.2.2.2.2.1
                                                hinv.2.1 hinv.2.2.2.1 hinv.2.2.2.2.2.1
                                                (Ref.Aig.extends_trans hgg_s2 hgg23) (by omega)
                                                hinv3 (by simp [xs', hinv.2.2.2.2.2.2.2.1])
                                                (fun i hi => by
                                                  simp only [xs']
                                                  rw [list_getD_set_ne _ 0#32 _ (by omega)]
                                                  exact hinv.2.2.2.2.2.2.2.2.1 i hi)
                                                hc (fun _ _ _ => by
                                                  apply hok3 ho2
                                                  · rw [← hgg_s2.1, hfr02.aig_cap,
                                                      ← hinv.2.1.aig_cap]
                                                    omega
                                                  · omega)
                                                hmlc' hQ
                                            · have ho3 : hdr3.oom = 0#32 := by bv_omega
                                              clear hc
                                              c0_hstraight
                                              obtain ⟨_, hnc_lt, hnc_ev⟩ := hpost3 ho3
                                              refine hJc (nc, ⟨⟩) mlc ⟨hdr3, g3, aig3, ht3,
                                                hfr02.trans hfr3.toBlastFrame,
                                                hfr3.lits_len.trans hlen02, ho3, hgg23,
                                                by omega, hinv3, hnc_lt, ?_, hmlc'⟩
                                              intro _ ρ vA vB hdA hdB
                                              have hla_eq :
                                                  g2.evalLit ρ (UInt32.ofBitVec
                                                    (st.xs.getD (a_off.toNat + st.j.toNat) 0#32)) =
                                                  vA.getLsbD st.j.toNat := by
                                                rw [evalLit_extend_of_lt hinv.2.2.2.2.2.2.1 hgg_s2
                                                  ha_lt ρ,
                                                  hinv.2.2.2.2.2.2.2.2.1 _ (by omega),
                                                  sliceAigWf_evalLit_extend hinv0 hinv.2.2.2.2.1
                                                    hwfA ρ hlt,
                                                  oc2_sliceDenotes_bit (by omega) hlt hdA]
                                              have hlb_eq :
                                                  g2.evalLit ρ (UInt32.ofBitVec
                                                    (st.xs.getD (b_off.toNat + st.j.toNat) 0#32)) =
                                                  vB.getLsbD st.j.toNat := by
                                                rw [evalLit_extend_of_lt hinv.2.2.2.2.2.2.1 hgg_s2
                                                  hb_lt ρ,
                                                  hinv.2.2.2.2.2.2.2.2.1 _ (by omega),
                                                  sliceAigWf_evalLit_extend hinv0 hinv.2.2.2.2.1
                                                    hwfB ρ hlt,
                                                  oc2_sliceDenotes_bit (by omega) hlt hdB]
                                              have hcin_eq :
                                                  g2.evalLit ρ (UInt32.ofBitVec st.cin) =
                                                  BitVec.carry st.j.toNat vA vB false := by
                                                rw [evalLit_extend_of_lt hinv.2.2.2.2.2.2.1 hgg_s2
                                                  hinv.2.2.2.2.2.2.2.2.2.1 ρ,
                                                  hinv.2.2.2.2.2.2.2.2.2.2.1 hlt ρ vA vB hdA hdB]
                                              rw [hnc_ev ρ, hla_eq, hlb_eq, hcin_eq,
                                                ← BitVec.carry_succ]
                                        · have hj1_ge : ¬ st.j.toNat + 1 < w.toNat := by
                                            have := w.isLt
                                            have h1 : (st.j + 1#32).toNat = st.j.toNat + 1 := by
                                              rw [BitVec.toNat_add,
                                                show (1#32 : BitVec 32).toNat = 1 from rfl,
                                                Nat.mod_eq_of_lt (by omega)]
                                            rw [← h1]; exact hc
                                          c0_hstraight
                                          have hlen_s2 := aigInv_aigLen_mono hinv.2.2.2.2.2.2.1
                                            hinv2 hgg_s2
                                          exact hJc (st.cin, ⟨⟩) m ⟨hdr2, g2, aig2, ht2,
                                            hfr02, hlen02, ho2, oc2_aig_le_refl g2,
                                            by omega, hinv2,
                                            Nat.lt_of_lt_of_le hinv.2.2.2.2.2.2.2.2.2.1 hlen_s2,
                                            fun hlt1 => False.elim (hj1_ge hlt1), hml3⟩)
                          · have hge : w.toNat ≤ st.j.toNat := by bv_omega
                            have heq : st.j.toNat = w.toNat := by have := hinv.1; omega
                            c0_hstraight
                            have hlen_le : hdr.lits_len.toNat ≤ st.hdr.lits_len.toNat := by
                              have := hdr.lits_cap.isLt
                              rw [hinv.2.2.1, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
                              omega
                            have hlen_sum :
                                st.hdr.lits_len.toNat ≤ hdr.lits_len.toNat + w.toNat := by
                              rw [hinv.2.2.1, BitVec.toNat_add]; exact Nat.mod_le _ _
                            refine hQ hdr.lits_len st.hdr st.g st.aigW st.htS st.xs ml2
                              hinv.2.1 hinv.2.2.2.2.1 (heq ▸ hinv.2.2.2.2.2.1)
                              hinv.2.2.2.2.2.2.1 hinv.2.2.2.2.2.2.2.1
                              hinv.2.2.2.2.2.2.2.2.1 hlen_le hlen_sum
                              (fun _ => by rw [hinv.2.1.lits_cap]; omega)
                              (fun hne => absurd h0 hne) (fun _ _ _ _ _ _ => hinv.2.2.2.1)
                              ?_ (fun hne => absurd hinv.2.2.2.1 hne) hml2
                            intro _
                            refine ⟨h0, hsA, hsB, hroom', rfl, hinv.2.2.1,
                              heq ▸ hinv.2.2.2.2.2.2.2.2.2.2.2.1, ?_⟩
                            intro ρ vA vB hdA hdB
                            rw [sliceDenotes_iff (by have := hinv.2.2.2.2.2.2.2.1; omega)]
                            intro i hi
                            exact hinv.2.2.2.2.2.2.2.2.2.2.2.2 i (heq ▸ hi) ρ vA vB hdA hdB)
                  · next hnroom =>
                    intro m1 hm1
                    let hdr1 : BVHdrState :=
                      { hdr with oom := if hdr.oom ≠ 0#32 then hdr.oom else 1#32 }
                    have hoom1 : hdr1.oom = 1#32 := by simp [hdr1, h0]
                    have hfr1 : hdr.BlastFrame hdr1 :=
                      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                        rfl, rfl, rfl, rfl, rfl, rfl⟩
                    c0_hstraight
                    c0_hsplit
                    · c0_hstraight
                      exact hQ 0xFFFFFFFF#32 hdr1 g aigW htS lits0 m1 hfr1
                        (oc2_aig_le_refl g) (Nat.le_add_right _ _) (aigInv_set_oom _ hinv0)
                        rfl (fun _ _ => rfl) (Nat.le_refl _) (Nat.le_add_right _ _) id
                        (fun hne => absurd h0 hne)
                        (fun _ _ _ hr _ _ => False.elim (hnroom ⟨h0, hsA_cap, hr⟩))
                        (fun h0' => absurd h0' (by rw [hoom1]; decide)) (fun _ => rfl)
                        (ops_sep5_hdr_unfocus hm1)
                    · exfalso; simp [h0] at hc
              · exact hJ () m ⟨rfl, fun ⟨_, _, hs⟩ => by simp [hs] at hc⟩
          · exact hJ () m ⟨rfl, fun ⟨_, hs, _⟩ => by simp [hs] at hc⟩)

end

/-! ## 2. `bv_blast_eq` Helpers & WP Proof -/

private structure EqSt where
  acc : BitVec 32
  j : BitVec 32
  hdr : BVHdrState
  g : Ref.Aig
  aigW : List (BitVec 64)
  htS : List (BitVec 32)

private def EqInv (a_off b_off w : BitVec 32) (hdr0 : BVHdrState) (g0 : Ref.Aig)
    (lits0 : List (BitVec 32)) (st : EqSt) : Prop :=
  st.j.toNat ≤ w.toNat ∧
  hdr0.AigFrame st.hdr ∧
  st.hdr.oom = 0#32 ∧
  g0 ≤ st.g ∧
  st.g.nodes.size ≤ g0.nodes.size + 4 * st.j.toNat ∧
  AigInv st.hdr st.g st.aigW st.htS ∧
  (st.acc >>> 1).toNat < st.hdr.aig_len.toNat ∧
  ∀ ρ : Nat → Bool,
    st.g.evalLit ρ (UInt32.ofBitVec st.acc) =
      decide (∀ i < st.j.toNat,
        g0.evalLit ρ (UInt32.ofBitVec (lits0.getD (a_off.toNat + i) 0#32)) =
          g0.evalLit ρ (UInt32.ofBitVec (lits0.getD (b_off.toNat + i) 0#32)))

private theorem eq_oom_exit {h : BitVec 64} {a_off b_off w : BitVec 32}
    {hdr hdr1 hdr2 : BVHdrState} {g g1 g2 : Ref.Aig}
    {aig2 : List (BitVec 64)} {ht2 lits0 : List (BitVec 32)}
    {m2 : Mem 64} {R : Mem 64 → Prop} {Q : (BitVec 32 × PUnit) → Mem 64 → Prop}
    {j k : Nat}
    (hjlt : j < w.toNat) (hk4 : k ≤ 4)
    (hfr0 : hdr.AigFrame hdr2)
    (hgg01 : g ≤ g1) (hfr01 : hdr.AigFrame hdr1) (ho1 : hdr1.oom = 0#32)
    (hsz1 : g1.nodes.size ≤ g.nodes.size + 4 * j)
    (hgg12 : g1 ≤ g2) (hsz2 : g2.nodes.size ≤ g1.nodes.size + k)
    (hinv2 : AigInv hdr2 g2 aig2 ht2)
    (hne : hdr2.oom ≠ 0#32)
    (hok : hdr1.oom = 0#32 → g1.A + 1 + g1.nodes.size + k ≤ hdr1.aig_cap.toNat →
      g1.nodes.size + k ≤ bvMaxGates → hdr2.oom = 0#32)
    (hm2 : (bvHdrMem h hdr2 ⋆ array64 hdr2.aig_ptr aig2 ⋆
      array (t := i32) hdr2.ht_ptr ht2 ⋆ array (t := i32) hdr2.lits_ptr lits0 ⋆ R) m2)
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Ref.Aig)
      (aig' : List (BitVec 64)) (ht' : List (BitVec 32)) (m' : Mem 64),
      hdr.AigFrame hdr' → g ≤ g' → g'.nodes.size ≤ g.nodes.size + 4 * w.toNat →
      AigInv hdr' g' aig' ht' → (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
      (hdr.oom = 0#32 → sliceBoundsOk hdr a_off w = true →
        sliceBoundsOk hdr b_off w = true →
        g.A + 1 + g.nodes.size + 4 * w.toNat ≤ hdr.aig_cap.toNat →
        g.nodes.size + 4 * w.toNat ≤ bvMaxGates → hdr'.oom = 0#32) →
      (hdr'.oom = 0#32 → hdr.oom = 0#32 ∧ sliceBoundsOk hdr a_off w = true ∧
        sliceBoundsOk hdr b_off w = true ∧ (ret >>> 1).toNat < hdr'.aig_len.toNat ∧
        ∀ ρ : Nat → Bool, g'.evalLit ρ (UInt32.ofBitVec ret) =
          decide (∀ j < w.toNat,
            g.evalLit ρ (UInt32.ofBitVec (lits0.getD (a_off.toNat + j) 0#32)) =
              g.evalLit ρ (UInt32.ofBitVec (lits0.getD (b_off.toNat + j) 0#32)))) →
      (hdr'.oom ≠ 0#32 → ret = 0#32) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aig' ⋆
        array (t := i32) hdr'.ht_ptr ht' ⋆ array (t := i32) hdr'.lits_ptr lits0 ⋆ R) m' →
      Q (ret, ⟨⟩) m') :
    Q (0#32, ⟨⟩) m2 := by
  have hmul : 4 * (j + 1) ≤ 4 * w.toNat := Nat.mul_le_mul_left 4 (by omega)
  rw [Nat.mul_succ] at hmul
  refine hQ 0#32 hdr2 g2 aig2 ht2 m2 hfr0 (Ref.Aig.extends_trans hgg01 hgg12) (by omega) hinv2
    (fun _ => hne) ?_ (fun h0' => absurd h0' hne) (fun _ => rfl) hm2
  intro _ _ _ haig_cap hmaxg
  apply hok ho1
  · rw [← hgg01.1, hfr01.aig_cap]; omega
  · omega

private theorem eqInv_step {a_off b_off w : BitVec 32}
    {hdr0 : BVHdrState} {g0 : Ref.Aig} {aig0 : List (BitVec 64)} {ht0 : List (BitVec 32)}
    {lits0 : List (BitVec 32)} {st : EqSt} {hdr1 hdr2 : BVHdrState} {g1 g2 : Ref.Aig}
    {aig1 aig2 : List (BitVec 64)} {ht1 ht2 : List (BitVec 32)} {eqb acc2 : BitVec 32}
    (hwfA : SliceAigWf hdr0.aig_len.toNat lits0 a_off.toNat w.toNat)
    (hwfB : SliceAigWf hdr0.aig_len.toNat lits0 b_off.toNat w.toNat)
    (hinv0 : AigInv hdr0 g0 aig0 ht0)
    (hinv : EqInv a_off b_off w hdr0 g0 lits0 st)
    (hlt : st.j.toNat < w.toNat)
    (_hinv1 : AigInv hdr1 g1 aig1 ht1) (hgg1 : st.g ≤ g1)
    (_heqb_lt : (eqb >>> 1).toNat < hdr1.aig_len.toNat)
    (heqb_ev : ∀ ρ : Nat → Bool, g1.evalLit ρ (UInt32.ofBitVec eqb) =
      (st.g.evalLit ρ (UInt32.ofBitVec (lits0.getD (a_off.toNat + st.j.toNat) 0#32)) ==
        st.g.evalLit ρ (UInt32.ofBitVec (lits0.getD (b_off.toNat + st.j.toNat) 0#32))))
    (hfr2 : hdr0.AigFrame hdr2) (ho2 : hdr2.oom = 0#32)
    (hgg12 : g1 ≤ g2) (hsz2 : g2.nodes.size ≤ st.g.nodes.size + 4)
    (hinv2 : AigInv hdr2 g2 aig2 ht2)
    (hacc_lt : (acc2 >>> 1).toNat < hdr2.aig_len.toNat)
    (hacc_ev : ∀ ρ : Nat → Bool, g2.evalLit ρ (UInt32.ofBitVec acc2) =
      (g1.evalLit ρ (UInt32.ofBitVec st.acc) && g1.evalLit ρ (UInt32.ofBitVec eqb))) :
    (st.j + 1#32).toNat = st.j.toNat + 1 ∧
      EqInv a_off b_off w hdr0 g0 lits0
        { acc := acc2, j := st.j + 1#32, hdr := hdr2, g := g2, aigW := aig2, htS := ht2 } := by
  have hj1 : (st.j + 1#32).toNat = st.j.toNat + 1 := by
    have := w.isLt
    rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hgg_s2 := Ref.Aig.extends_trans hgg1 hgg12
  refine ⟨hj1, by dsimp only; omega, hfr2, ho2,
    Ref.Aig.extends_trans hinv.2.2.2.1 hgg_s2,
    by dsimp only; have := hinv.2.2.2.2.1; rw [hj1, Nat.mul_succ]; omega,
    hinv2, hacc_lt, ?_⟩
  intro ρ
  dsimp only
  rw [hj1, hacc_ev ρ, evalLit_extend_of_lt hinv.2.2.2.2.2.1 hgg1 hinv.2.2.2.2.2.2.1 ρ,
    hinv.2.2.2.2.2.2.2 ρ, heqb_ev ρ,
    sliceAigWf_evalLit_extend hinv0 hinv.2.2.2.1 hwfA ρ hlt,
    sliceAigWf_evalLit_extend hinv0 hinv.2.2.2.1 hwfB ρ hlt,
    Bool.beq_eq_decide_eq, ← oc2_decide_forall_lt_succ]

public section

theorem bv_blast_eq_wp (Γ : Env)
    (hSliceOk : ∀ xs m Q X, bvSliceOkSpec xs m Q X →
      Γ "bv_slice_ok" [i64, i32, i32] [.bool] xs m Q X)
    (hMkAnd : ∀ xs m Q X, bvMkAndSpec xs m Q X →
      Γ "bv_mk_and" [i64, i32, i32] [i32] xs m Q X)
    (hAigBeq : ∀ xs m Q X, bvAigBeqSpec xs m Q X →
      Γ "bv_aig_beq" [i64, i32, i32] [i32] xs m Q X) :
    ∀ xs m Q X, bvBlastEqSpec xs m Q X →
      Func.wp Γ bv_blast_eq_body xs m Q X := by
  rintro ⟨h, a_off, b_off, w, ⟨⟩⟩ m Q X
    ⟨hdr, g, aigW, htS, lits0, R, hinv0, hlits_len, hwf, hm, hQ⟩
  refine wp_join_group (ts := [])
    (fun _ ml => ml = m ∧ ¬ (hdr.oom = 0#32 ∧
      sliceBoundsOk hdr a_off w = true ∧ sliceBoundsOk hdr b_off w = true))
    (fun _ _ ml ⟨hml, hfail⟩ => by
      subst hml
      c0_hstraight
      let hdr' : BVHdrState := { hdr with oom := (1 : BitVec 32) }
      have hfr : hdr.AigFrame hdr' :=
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact hQ 0#32 hdr' g aigW htS _ hfr (oc2_aig_le_refl g) (Nat.le_add_right _ _)
        (aigInv_set_oom (1 : BitVec 32) hinv0) (fun _ => by simp [hdr'])
        (fun h0 h1 h2 _ _ => False.elim (hfail ⟨h0, h1, h2⟩))
        (fun h0 => False.elim (by simp [hdr'] at h0)) (fun _ => rfl) (oc2_sep5_emp_all hm))
    (fun J hJ => by
      c0_hstraight
      c0_hsplit
      · exact hJ () m ⟨rfl, fun ⟨h0, _⟩ => hc h0⟩
      · have h0 : hdr.oom = 0#32 := by bv_omega
        clear hc
        c0_hcall hSliceOk
        · refine ⟨hdr, array64 hdr.aig_ptr aigW ⋆ array (t := i32) hdr.ht_ptr htS ⋆
              array (t := i32) hdr.lits_ptr lits0 ⋆ R, ops_sep5_hdr_focus hm, ?_⟩
          dsimp only [Arg.val]
          c0_hsplit
          · have hsA : sliceBoundsOk hdr a_off w = true := hc
            obtain ⟨_, _, hsA_sum⟩ := sliceBoundsOk_sum hsA
            clear hc
            c0_hcall hSliceOk
            · refine ⟨hdr, array64 hdr.aig_ptr aigW ⋆ array (t := i32) hdr.ht_ptr htS ⋆
                  array (t := i32) hdr.lits_ptr lits0 ⋆ R, ops_sep5_hdr_focus hm, ?_⟩
              dsimp only [Arg.val]
              c0_hsplit
              · have hsB : sliceBoundsOk hdr b_off w = true := hc
                obtain ⟨_, _, hsB_sum⟩ := sliceBoundsOk_sum hsB
                clear hc
                obtain ⟨hwfA, hwfB⟩ := hwf h0 hsA hsB
                c0_hstraight
                refine wp_while_record
                  (proj := fun st : EqSt => (st.acc, st.j, ⟨⟩))
                  (μ := fun st => w.toNat - st.j.toNat)
                  (Inv := EqInv a_off b_off w hdr g lits0)
                  (MemPred := fun st => bvHdrMem h st.hdr ⋆
                    array64 st.hdr.aig_ptr st.aigW ⋆ array (t := i32) st.hdr.ht_ptr st.htS ⋆
                    array (t := i32) st.hdr.lits_ptr lits0)
                  (R := R)
                  (fun Jw hJw => by
                    c0_hstraight
                    have hz : (0#32 : BitVec 32).toNat = 0 := rfl
                    refine hJw ⟨1#32, 0#32, hdr, g, aigW, htS⟩ m ?_ hm
                    refine ⟨by dsimp only; rw [hz]; omega, oc2_aigFrame_refl hdr, h0,
                      oc2_aig_le_refl g, by dsimp only; rw [hz]; omega, hinv0,
                      by dsimp only; exact aigInv_true_lit_bound hinv0, ?_⟩
                    intro ρ; dsimp only; rw [hz, evalLit_one]; simp)
                  (fun Jw st ml hinv hml hrec => by
                    dsimp only [Blocks.get_here] at *
                    c0_hstraight
                    c0_hsplit
                    · have hlt : st.j.toNat < w.toNat := hc
                      clear hc
                      have hwa : a_off.toNat + st.j.toNat < 2 ^ 32 := by
                        have := hdr.lits_len.isLt; omega
                      have hia : a_off.toNat + st.j.toNat < lits0.length := by omega
                      have hwb : b_off.toNat + st.j.toNat < 2 ^ 32 := by
                        have := hdr.lits_len.isLt; omega
                      have hib : b_off.toNat + st.j.toNat < lits0.length := by omega
                      have hml_l : (array (t := i32) hdr.lits_ptr lits0 ⋆
                          (bvHdrMem h st.hdr ⋆ array64 st.hdr.aig_ptr st.aigW ⋆
                            array (t := i32) st.hdr.ht_ptr st.htS ⋆ R)) ml := by
                        have h0l := ops_sep5_lits_focus hml
                        rwa [hinv.2.1.lits_ptr] at h0l
                      c0_hstraight
                      have hml_r : (bvHdrMem h st.hdr ⋆ array64 st.hdr.aig_ptr st.aigW ⋆
                          array (t := i32) st.hdr.ht_ptr st.htS ⋆
                          array (t := i32) st.hdr.lits_ptr lits0 ⋆ R) ml := by
                        rw [← hinv.2.1.lits_ptr] at hml_l
                        exact ops_sep5_lits_unfocus hml_l
                      rw [ops_list_getElem_eq_getD lits0 0#32 _ (ops_setWidth64_add_u32 hwa),
                        ops_list_getElem_eq_getD lits0 0#32 _ (ops_setWidth64_add_u32 hwb)]
                      have hlen0 := aigInv_aigLen_mono hinv0 hinv.2.2.2.2.2.1 hinv.2.2.2.1
                      have ha_lt : (lits0.getD (a_off.toNat + st.j.toNat) 0#32 >>> 1).toNat <
                          st.hdr.aig_len.toNat := Nat.lt_of_lt_of_le (hwfA _ hlt) hlen0
                      have hb_lt : (lits0.getD (b_off.toNat + st.j.toNat) 0#32 >>> 1).toNat <
                          st.hdr.aig_len.toNat := Nat.lt_of_lt_of_le (hwfB _ hlt) hlen0
                      c0_hcall hAigBeq
                      · refine ⟨st.hdr, st.g, st.aigW, st.htS,
                            array (t := i32) st.hdr.lits_ptr lits0 ⋆ R,
                            hinv.2.2.2.2.2.1, fun _ => ⟨ha_lt, hb_lt⟩,
                            ops_sep5_aig_focus hml_r, ?_⟩
                        intro eqb hdr1 g1 aig1 ht1 m1 hfr1 hgg1 hsz1 hinv1 _ hok1 hpost1 hm1
                        dsimp only [Arg.val]
                        have hm1' := ops_sep5_aig_unfocus hm1
                        rw [← hfr1.lits_ptr] at hm1'
                        c0_hstraight
                        c0_hsplit
                        · c0_hstraight
                          exact eq_oom_exit (k := 3) hlt (by decide) (hinv.2.1.trans hfr1)
                            hinv.2.2.2.1 hinv.2.1 hinv.2.2.1 hinv.2.2.2.2.1 hgg1 hsz1 hinv1 hc
                            hok1 hm1' hQ
                        · have ho1 : hdr1.oom = 0#32 := by bv_omega
                          clear hc
                          obtain ⟨heqb_lt, heqb_ev⟩ := hpost1 ho1
                          have hlen1 := aigInv_aigLen_mono hinv.2.2.2.2.2.1 hinv1 hgg1
                          c0_hcall hMkAnd
                          · refine ⟨hdr1, g1, aig1, ht1, array (t := i32) hdr1.lits_ptr lits0 ⋆ R,
                                hinv1, fun _ => ⟨Nat.lt_of_lt_of_le hinv.2.2.2.2.2.2.1 hlen1,
                                  heqb_lt⟩, ops_sep5_aig_focus hm1', ?_⟩
                            intro acc2 hdr2 g2 aig2 ht2 m2 hfr2 hgg2 hsz2 hinv2 _ hok2 hpost2 hm2
                            dsimp only [Arg.val]
                            have hm2' := ops_sep5_aig_unfocus hm2
                            rw [← hfr2.lits_ptr] at hm2'
                            c0_hstraight
                            c0_hsplit
                            · c0_hstraight
                              exact eq_oom_exit (k := 4) hlt (by decide)
                                ((hinv.2.1.trans hfr1).trans hfr2)
                                hinv.2.2.2.1 hinv.2.1 hinv.2.2.1 hinv.2.2.2.2.1
                                (Ref.Aig.extends_trans hgg1 hgg2) (by omega) hinv2 hc
                                (fun _ _ _ => by
                                  apply hok2 ho1
                                  · rw [← hgg1.1, hfr1.aig_cap]; omega
                                  · omega)
                                hm2' hQ
                            · have ho2 : hdr2.oom = 0#32 := by bv_omega
                              clear hc
                              c0_hstraight
                              obtain ⟨hacc_lt, hacc_ev⟩ := hpost2 ho2
                              obtain ⟨hj1, hinv'⟩ := eqInv_step hwfA hwfB hinv0 hinv hlt hinv1
                                hgg1 heqb_lt heqb_ev ((hinv.2.1.trans hfr1).trans hfr2) ho2 hgg2
                                (by omega) hinv2 hacc_lt hacc_ev
                              exact hrec ⟨acc2, st.j + 1#32, hdr2, g2, aig2, ht2⟩ m2
                                (by dsimp only; omega) hinv' hm2'
                    · have hge : w.toNat ≤ st.j.toNat := by bv_omega
                      have heq : st.j.toNat = w.toNat := by have := hinv.1; omega
                      c0_hstraight
                      refine hQ st.acc st.hdr st.g st.aigW st.htS ml hinv.2.1 hinv.2.2.2.1
                        (heq ▸ hinv.2.2.2.2.1) hinv.2.2.2.2.2.1 (fun hne => absurd h0 hne)
                        (fun _ _ _ _ _ => hinv.2.2.1) ?_ (fun hne => absurd hinv.2.2.1 hne) hml
                      intro _
                      exact ⟨h0, hsA, hsB, hinv.2.2.2.2.2.2.1,
                        fun ρ => by rw [← heq]; exact hinv.2.2.2.2.2.2.2 ρ⟩)
              · exact hJ () m ⟨rfl, fun ⟨_, _, hs⟩ => by simp [hs] at hc⟩
          · exact hJ () m ⟨rfl, fun ⟨_, hs, _⟩ => by simp [hs] at hc⟩)

end

/-! ## 3. `bv_blast_ult` Helpers & WP Proof -/

private structure UltSt where
  cin : BitVec 32
  j : BitVec 32
  hdr : BVHdrState
  g : Ref.Aig
  aigW : List (BitVec 64)
  htS : List (BitVec 32)

private def UltInv (a_off b_off w : BitVec 32) (hdr0 : BVHdrState) (g0 : Ref.Aig)
    (lits0 : List (BitVec 32)) (st : UltSt) : Prop :=
  st.j.toNat ≤ w.toNat ∧
  hdr0.AigFrame st.hdr ∧
  st.hdr.oom = 0#32 ∧
  g0 ≤ st.g ∧
  st.g.nodes.size ≤ g0.nodes.size + 6 * st.j.toNat ∧
  AigInv st.hdr st.g st.aigW st.htS ∧
  (st.cin >>> 1).toNat < st.hdr.aig_len.toNat ∧
  ∀ (ρ : Nat → Bool) (vA vB : BitVec w.toNat),
    SliceDenotes g0 ρ (litsSlice lits0 a_off.toNat w.toNat) vA →
    SliceDenotes g0 ρ (litsSlice lits0 b_off.toNat w.toNat) vB →
    st.g.evalLit ρ (UInt32.ofBitVec st.cin) = BitVec.carry st.j.toNat vA (~~~vB) true

private theorem ult_oom_exit {h : BitVec 64} {a_off b_off w : BitVec 32}
    {hdr hdr1 hdr2 : BVHdrState} {g g1 g2 : Ref.Aig}
    {aig2 : List (BitVec 64)} {ht2 lits0 : List (BitVec 32)}
    {m2 : Mem 64} {R : Mem 64 → Prop} {Q : (BitVec 32 × PUnit) → Mem 64 → Prop}
    {j : Nat}
    (hjlt : j < w.toNat)
    (hfr0 : hdr.AigFrame hdr2)
    (hgg01 : g ≤ g1) (hfr01 : hdr.AigFrame hdr1) (ho1 : hdr1.oom = 0#32)
    (hsz1 : g1.nodes.size ≤ g.nodes.size + 6 * j)
    (hgg12 : g1 ≤ g2) (hsz2 : g2.nodes.size ≤ g1.nodes.size + 6)
    (hinv2 : AigInv hdr2 g2 aig2 ht2)
    (hne : hdr2.oom ≠ 0#32)
    (hok : hdr1.oom = 0#32 → g1.A + 1 + g1.nodes.size + 6 ≤ hdr1.aig_cap.toNat →
      g1.nodes.size + 6 ≤ bvMaxGates → hdr2.oom = 0#32)
    (hm2 : (bvHdrMem h hdr2 ⋆ array64 hdr2.aig_ptr aig2 ⋆
      array (t := i32) hdr2.ht_ptr ht2 ⋆ array (t := i32) hdr2.lits_ptr lits0 ⋆ R) m2)
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Ref.Aig)
      (aig' : List (BitVec 64)) (ht' : List (BitVec 32)) (m' : Mem 64),
      hdr.AigFrame hdr' → g ≤ g' → g'.nodes.size ≤ g.nodes.size + 6 * w.toNat →
      AigInv hdr' g' aig' ht' → (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
      (hdr.oom = 0#32 → sliceBoundsOk hdr a_off w = true →
        sliceBoundsOk hdr b_off w = true →
        g.A + 1 + g.nodes.size + 6 * w.toNat ≤ hdr.aig_cap.toNat →
        g.nodes.size + 6 * w.toNat ≤ bvMaxGates → hdr'.oom = 0#32) →
      (hdr'.oom = 0#32 → hdr.oom = 0#32 ∧ sliceBoundsOk hdr a_off w = true ∧
        sliceBoundsOk hdr b_off w = true ∧ (ret >>> 1).toNat < hdr'.aig_len.toNat ∧
        ∀ (ρ : Nat → Bool) (vA vB : BitVec w.toNat),
          SliceDenotes g ρ (litsSlice lits0 a_off.toNat w.toNat) vA →
          SliceDenotes g ρ (litsSlice lits0 b_off.toNat w.toNat) vB →
          g'.evalLit ρ (UInt32.ofBitVec ret) = vA.ult vB) →
      (hdr'.oom ≠ 0#32 → ret = 0#32) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aig' ⋆
        array (t := i32) hdr'.ht_ptr ht' ⋆ array (t := i32) hdr'.lits_ptr lits0 ⋆ R) m' →
      Q (ret, ⟨⟩) m') :
    Q (0#32, ⟨⟩) m2 := by
  have hmul : 6 * (j + 1) ≤ 6 * w.toNat := Nat.mul_le_mul_left 6 (by omega)
  rw [Nat.mul_succ] at hmul
  refine hQ 0#32 hdr2 g2 aig2 ht2 m2 hfr0 (Ref.Aig.extends_trans hgg01 hgg12) (by omega) hinv2
    (fun _ => hne) ?_ (fun h0' => absurd h0' hne) (fun _ => rfl) hm2
  intro _ _ _ haig_cap hmaxg
  apply hok ho1
  · rw [← hgg01.1, hfr01.aig_cap]; omega
  · omega

private theorem ultInv_step {a_off b_off w : BitVec 32}
    {hdr0 : BVHdrState} {g0 : Ref.Aig} {aig0 : List (BitVec 64)} {ht0 : List (BitVec 32)}
    {lits0 : List (BitVec 32)} {st : UltSt} {hdr1 : BVHdrState} {g1 : Ref.Aig}
    {aig1 : List (BitVec 64)} {ht1 : List (BitVec 32)} {nc : BitVec 32}
    (hle_a : a_off.toNat + w.toNat ≤ lits0.length)
    (hle_b : b_off.toNat + w.toNat ≤ lits0.length)
    (hwfA : SliceAigWf hdr0.aig_len.toNat lits0 a_off.toNat w.toNat)
    (hwfB : SliceAigWf hdr0.aig_len.toNat lits0 b_off.toNat w.toNat)
    (hinv0 : AigInv hdr0 g0 aig0 ht0)
    (hinv : UltInv a_off b_off w hdr0 g0 lits0 st)
    (hlt : st.j.toNat < w.toNat)
    (hfr1 : hdr0.AigFrame hdr1) (ho1 : hdr1.oom = 0#32)
    (hgg1 : st.g ≤ g1) (hsz1 : g1.nodes.size ≤ st.g.nodes.size + 6)
    (hinv1 : AigInv hdr1 g1 aig1 ht1)
    (hnc_lt : (nc >>> 1).toNat < hdr1.aig_len.toNat)
    (hnc_ev : ∀ ρ : Nat → Bool, g1.evalLit ρ (UInt32.ofBitVec nc) =
      (st.g.evalLit ρ (UInt32.ofBitVec (lits0.getD (a_off.toNat + st.j.toNat) 0#32))).atLeastTwo
        (st.g.evalLit ρ (UInt32.ofBitVec (lits0.getD (b_off.toNat + st.j.toNat) 0#32 ^^^ 1#32)))
        (st.g.evalLit ρ (UInt32.ofBitVec st.cin))) :
    (st.j + 1#32).toNat = st.j.toNat + 1 ∧
      UltInv a_off b_off w hdr0 g0 lits0
        { cin := nc, j := st.j + 1#32, hdr := hdr1, g := g1, aigW := aig1, htS := ht1 } := by
  have hj1 : (st.j + 1#32).toNat = st.j.toNat + 1 := by
    have := w.isLt
    rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  refine ⟨hj1, by dsimp only; omega, hfr1, ho1,
    Ref.Aig.extends_trans hinv.2.2.2.1 hgg1,
    by dsimp only; have := hinv.2.2.2.2.1; rw [hj1, Nat.mul_succ]; omega,
    hinv1, hnc_lt, ?_⟩
  intro ρ vA vB hdA hdB
  dsimp only
  rw [hj1, hnc_ev ρ, evalLit_xor1,
    sliceAigWf_evalLit_extend hinv0 hinv.2.2.2.1 hwfA ρ hlt,
    sliceAigWf_evalLit_extend hinv0 hinv.2.2.2.1 hwfB ρ hlt,
    oc2_sliceDenotes_bit hle_a hlt hdA, oc2_sliceDenotes_bit hle_b hlt hdB,
    hinv.2.2.2.2.2.2.2 ρ vA vB hdA hdB, BitVec.carry_succ, BitVec.getLsbD_not,
    decide_eq_true hlt, Bool.true_and]

public section

theorem bv_blast_ult_wp (Γ : Env)
    (hSliceOk : ∀ xs m Q X, bvSliceOkSpec xs m Q X →
      Γ "bv_slice_ok" [i64, i32, i32] [.bool] xs m Q X)
    (hAigNot : ∀ xs m Q X, bvAigNotSpec xs m Q X →
      Γ "bv_aig_not" [i32] [i32] xs m Q X)
    (hFac : ∀ xs m Q X, bvFullAdderCarrySpec xs m Q X →
      Γ "bv_full_adder_carry" [i64, i32, i32, i32] [i32] xs m Q X) :
    ∀ xs m Q X, bvBlastUltSpec xs m Q X →
      Func.wp Γ bv_blast_ult_body xs m Q X := by
  rintro ⟨h, a_off, b_off, w, ⟨⟩⟩ m Q X
    ⟨hdr, g, aigW, htS, lits0, R, hinv0, hlits_len, hwf, hm, hQ⟩
  refine wp_join_group (ts := [])
    (fun _ ml => ml = m ∧ ¬ (hdr.oom = 0#32 ∧
      sliceBoundsOk hdr a_off w = true ∧ sliceBoundsOk hdr b_off w = true))
    (fun _ _ ml ⟨hml, hfail⟩ => by
      subst hml
      c0_hstraight
      let hdr' : BVHdrState := { hdr with oom := (1 : BitVec 32) }
      have hfr : hdr.AigFrame hdr' :=
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact hQ 0#32 hdr' g aigW htS _ hfr (oc2_aig_le_refl g) (Nat.le_add_right _ _)
        (aigInv_set_oom (1 : BitVec 32) hinv0) (fun _ => by simp [hdr'])
        (fun h0 h1 h2 _ _ => False.elim (hfail ⟨h0, h1, h2⟩))
        (fun h0 => False.elim (by simp [hdr'] at h0)) (fun _ => rfl) (oc2_sep5_emp_all hm))
    (fun J hJ => by
      c0_hstraight
      c0_hsplit
      · exact hJ () m ⟨rfl, fun ⟨h0, _⟩ => hc h0⟩
      · have h0 : hdr.oom = 0#32 := by bv_omega
        clear hc
        c0_hcall hSliceOk
        · refine ⟨hdr, array64 hdr.aig_ptr aigW ⋆ array (t := i32) hdr.ht_ptr htS ⋆
              array (t := i32) hdr.lits_ptr lits0 ⋆ R, ops_sep5_hdr_focus hm, ?_⟩
          dsimp only [Arg.val]
          c0_hsplit
          · have hsA : sliceBoundsOk hdr a_off w = true := hc
            obtain ⟨_, _, hsA_sum⟩ := sliceBoundsOk_sum hsA
            clear hc
            c0_hcall hSliceOk
            · refine ⟨hdr, array64 hdr.aig_ptr aigW ⋆ array (t := i32) hdr.ht_ptr htS ⋆
                  array (t := i32) hdr.lits_ptr lits0 ⋆ R, ops_sep5_hdr_focus hm, ?_⟩
              dsimp only [Arg.val]
              c0_hsplit
              · have hsB : sliceBoundsOk hdr b_off w = true := hc
                obtain ⟨_, _, hsB_sum⟩ := sliceBoundsOk_sum hsB
                clear hc
                obtain ⟨hwfA, hwfB⟩ := hwf h0 hsA hsB
                c0_hstraight
                refine wp_while_record
                  (proj := fun st : UltSt => (st.cin, st.j, ⟨⟩))
                  (μ := fun st => w.toNat - st.j.toNat)
                  (Inv := UltInv a_off b_off w hdr g lits0)
                  (MemPred := fun st => bvHdrMem h st.hdr ⋆
                    array64 st.hdr.aig_ptr st.aigW ⋆ array (t := i32) st.hdr.ht_ptr st.htS ⋆
                    array (t := i32) st.hdr.lits_ptr lits0)
                  (R := R)
                  (fun Jw hJw => by
                    c0_hstraight
                    have hz : (0#32 : BitVec 32).toNat = 0 := rfl
                    refine hJw ⟨1#32, 0#32, hdr, g, aigW, htS⟩ m ?_ hm
                    refine ⟨by dsimp only; rw [hz]; omega, oc2_aigFrame_refl hdr, h0,
                      oc2_aig_le_refl g, by dsimp only; rw [hz]; omega, hinv0,
                      by dsimp only; exact aigInv_true_lit_bound hinv0, ?_⟩
                    intro ρ vA vB _ _; dsimp only; rw [hz, evalLit_one, oc2_bv_carry_zero])
                  (fun Jw st ml hinv hml hrec => by
                    dsimp only [Blocks.get_here] at *
                    c0_hstraight
                    c0_hsplit
                    · have hlt : st.j.toNat < w.toNat := hc
                      clear hc
                      have hwb : b_off.toNat + st.j.toNat < 2 ^ 32 := by
                        have := hdr.lits_len.isLt; omega
                      have hib : b_off.toNat + st.j.toNat < lits0.length := by omega
                      have hwa : a_off.toNat + st.j.toNat < 2 ^ 32 := by
                        have := hdr.lits_len.isLt; omega
                      have hia : a_off.toNat + st.j.toNat < lits0.length := by omega
                      have hml_l : (array (t := i32) hdr.lits_ptr lits0 ⋆
                          (bvHdrMem h st.hdr ⋆ array64 st.hdr.aig_ptr st.aigW ⋆
                            array (t := i32) st.hdr.ht_ptr st.htS ⋆ R)) ml := by
                        have h0l := ops_sep5_lits_focus hml
                        rwa [hinv.2.1.lits_ptr] at h0l
                      c0_hstraight
                      rw [ops_list_getElem_eq_getD lits0 0#32 _ (ops_setWidth64_add_u32 hwb)]
                      c0_hcall hAigNot
                      dsimp only [bvAigNotSpec, Arg.val]
                      c0_hstraight
                      have hml_r : (bvHdrMem h st.hdr ⋆ array64 st.hdr.aig_ptr st.aigW ⋆
                          array (t := i32) st.hdr.ht_ptr st.htS ⋆
                          array (t := i32) st.hdr.lits_ptr lits0 ⋆ R) ml := by
                        rw [← hinv.2.1.lits_ptr] at hml_l
                        exact ops_sep5_lits_unfocus hml_l
                      rw [ops_list_getElem_eq_getD lits0 0#32 _ (ops_setWidth64_add_u32 hwa)]
                      have hlen0 := aigInv_aigLen_mono hinv0 hinv.2.2.2.2.2.1 hinv.2.2.2.1
                      have ha_lt : (lits0.getD (a_off.toNat + st.j.toNat) 0#32 >>> 1).toNat <
                          st.hdr.aig_len.toNat := Nat.lt_of_lt_of_le (hwfA _ hlt) hlen0
                      have hb_lt : (lits0.getD (b_off.toNat + st.j.toNat) 0#32 >>> 1).toNat <
                          st.hdr.aig_len.toNat := Nat.lt_of_lt_of_le (hwfB _ hlt) hlen0
                      have hbn_lt :
                          ((lits0.getD (b_off.toNat + st.j.toNat) 0#32 ^^^ 1#32) >>> 1).toNat <
                          st.hdr.aig_len.toNat := by
                        rw [oc2_xor1_rshift1]; exact hb_lt
                      c0_hcall hFac
                      · refine ⟨st.hdr, st.g, st.aigW, st.htS,
                            array (t := i32) st.hdr.lits_ptr lits0 ⋆ R, hinv.2.2.2.2.2.1,
                            fun _ => ⟨ha_lt, hbn_lt, hinv.2.2.2.2.2.2.1⟩,
                            ops_sep5_aig_focus hml_r, ?_⟩
                        intro nc hdr1 g1 aig1 ht1 m1 hfr1 hgg1 hsz1 hinv1 _ hok1 hpost1 _ hm1
                        dsimp only [Arg.val]
                        have hm1' := ops_sep5_aig_unfocus hm1
                        rw [← hfr1.lits_ptr] at hm1'
                        c0_hstraight
                        c0_hsplit
                        · c0_hstraight
                          exact ult_oom_exit hlt (hinv.2.1.trans hfr1) hinv.2.2.2.1 hinv.2.1
                            hinv.2.2.1 hinv.2.2.2.2.1 hgg1 hsz1 hinv1 hc hok1 hm1' hQ
                        · have ho1 : hdr1.oom = 0#32 := by bv_omega
                          clear hc
                          c0_hstraight
                          obtain ⟨_, hnc_lt, hnc_ev⟩ := hpost1 ho1
                          obtain ⟨hj1, hinv'⟩ := ultInv_step (by omega) (by omega) hwfA hwfB
                            hinv0 hinv hlt (hinv.2.1.trans hfr1) ho1 hgg1 hsz1 hinv1 hnc_lt hnc_ev
                          exact hrec ⟨nc, st.j + 1#32, hdr1, g1, aig1, ht1⟩ m1
                            (by dsimp only; omega) hinv' hm1'
                    · have hge : w.toNat ≤ st.j.toNat := by bv_omega
                      have heq : st.j.toNat = w.toNat := by have := hinv.1; omega
                      c0_hstraight
                      c0_hcall hAigNot
                      dsimp only [bvAigNotSpec, Arg.val]
                      c0_hstraight
                      refine hQ (st.cin ^^^ 1#32) st.hdr st.g st.aigW st.htS ml
                        hinv.2.1 hinv.2.2.2.1 (heq ▸ hinv.2.2.2.2.1) hinv.2.2.2.2.2.1
                        (fun hne => absurd h0 hne) (fun _ _ _ _ _ => hinv.2.2.1) ?_
                        (fun hne => absurd hinv.2.2.1 hne) hml
                      intro _
                      refine ⟨h0, hsA, hsB,
                        by rw [oc2_xor1_rshift1]; exact hinv.2.2.2.2.2.2.1, ?_⟩
                      intro ρ vA vB hdA hdB
                      rw [evalLit_xor1, hinv.2.2.2.2.2.2.2 ρ vA vB hdA hdB,
                        BitVec.ult_eq_not_carry, show st.j.toNat = w.toNat from heq])
              · exact hJ () m ⟨rfl, fun ⟨_, _, hs⟩ => by simp [hs] at hc⟩
          · exact hJ () m ⟨rfl, fun ⟨_, hs, _⟩ => by simp [hs] at hc⟩)

end

end LeanQbe.T.Examples.Bitblast.Proof
