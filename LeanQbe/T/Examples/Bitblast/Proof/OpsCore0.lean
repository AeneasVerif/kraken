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
# Core Pure-Slice WP Proofs (`Bitblast.Proof.OpsCore0`)

Proves canonical `Γ`-parametric `Func.wp` theorems for the non-AIG-allocating
core operations in `Bitblast/Src/OpsCore.lean`:
- `bv_slice_ok_wp`
- `bv_blast_get_lsb_d_wp`
- `bv_blast_not_wp`
- `bv_blast_extract_wp`
- `bv_blast_append_wp`
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open LeanQbe.T
open LeanQbe.T.Examples.Bitblast.Src.OpsCore

/-! ## Local Array32 Load/Store Rules -/

@[local c0_load] private theorem oc0_load_lits_add {R : Mem 64 → Prop} {m : Mem 64}
    {a : BitVec 64} {off k : BitVec 32} {xs : List (BitVec 32)}
    (h : (array (t := i32) a xs ⋆ R) m)
    (hwrap : off.toNat + k.toNat < 2 ^ 32) (hi : off.toNat + k.toNat < xs.length) :
    loadVal m i32 (a + BitVec.setWidth 64 (off + k) * 4) =
      some (xs[off.toNat + k.toNat]'hi) :=
  ops_load_array32_u32_add_mul4 h hwrap hi

@[local c0_store] private theorem oc0_store_lits_add {R : Mem 64 → Prop} {m : Mem 64}
    {a : BitVec 64} {off k : BitVec 32} {xs : List (BitVec 32)} (v : BitVec 32)
    (h : (array (t := i32) a xs ⋆ R) m)
    (hwrap : off.toNat + k.toNat < 2 ^ 32) (hi : off.toNat + k.toNat < xs.length) :
    storeOk m i32 (a + BitVec.setWidth 64 (off + k) * 4) ∧
      (array (t := i32) a (xs.set (off.toNat + k.toNat) v) ⋆ R)
        (storeMem m i32 (a + BitVec.setWidth 64 (off + k) * 4) v) :=
  ops_store_array32_u32_add_mul4 v h hwrap hi

@[local c0_load] private theorem oc0_load_lits_ext {R : Mem 64 → Prop} {m : Mem 64}
    {a : BitVec 64} {off : BitVec 32} {pos : BitVec 64} {xs : List (BitVec 32)}
    (h : (array (t := i32) a xs ⋆ R) m)
    (hpos : pos.toNat < 2 ^ 32) (hwrap : off.toNat + pos.toNat < 2 ^ 32)
    (hi : off.toNat + pos.toNat < xs.length) :
    loadVal m i32 (a + BitVec.setWidth 64 (off + BitVec.setWidth 32 pos) * 4) =
      some (xs[off.toNat + pos.toNat]'hi) :=
  ops_load_array32_u32_ext_mul4 h hpos hwrap hi

@[local c0_store] private theorem oc0_store_lits_add2 {R : Mem 64 → Prop} {m : Mem 64}
    {a : BitVec 64} {out rw j : BitVec 32} {xs : List (BitVec 32)} (v : BitVec 32)
    (h : (array (t := i32) a xs ⋆ R) m)
    (hwrap1 : out.toNat + rw.toNat < 2 ^ 32)
    (hwrap2 : out.toNat + rw.toNat + j.toNat < 2 ^ 32)
    (hi : out.toNat + rw.toNat + j.toNat < xs.length) :
    storeOk m i32 (a + BitVec.setWidth 64 (out + rw + j) * 4) ∧
      (array (t := i32) a (xs.set (out.toNat + rw.toNat + j.toNat) v) ⋆ R)
        (storeMem m i32 (a + BitVec.setWidth 64 (out + rw + j) * 4) v) :=
  ops_store_array32_u32_add_add_mul4 v h hwrap1 hwrap2 hi

/-! ## Pure Loop Invariants & Step Helpers -/

private def notLoopInv (a_off w : BitVec 32) (hdr0 : BVHdrState)
    (litsPool0 : List (BitVec 32)) : (BitVec 32 × List (BitVec 32)) → Prop :=
  fun (j, xs) =>
    j.toNat ≤ w.toNat ∧
    xs.length = litsPool0.length ∧
    (∀ i < hdr0.lits_len.toNat, xs.getD i 0#32 = litsPool0.getD i 0#32) ∧
    (∀ i < j.toNat, xs.getD (hdr0.lits_len.toNat + i) 0#32 =
      litsPool0.getD (a_off.toNat + i) 0#32 ^^^ 1#32)

private theorem notLoopInv_step {a_off w j : BitVec 32} {hdr0 : BVHdrState}
    {litsPool0 xs : List (BitVec 32)}
    (hsok : a_off.toNat + w.toNat ≤ hdr0.lits_len.toNat)
    (hinv : notLoopInv a_off w hdr0 litsPool0 (j, xs)) (hj : j.toNat < w.toNat)
    (hi_out : hdr0.lits_len.toNat + j.toNat < xs.length) :
    (j + 1#32).toNat = j.toNat + 1 ∧
      notLoopInv a_off w hdr0 litsPool0
        (j + 1#32, xs.set (hdr0.lits_len.toNat + j.toNat)
          (xs.getD (a_off.toNat + j.toNat) 0#32 ^^^ 1#32)) := by
  have hj1 : (j + 1#32).toNat = j.toNat + 1 := by
    have := w.isLt
    rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  refine ⟨hj1, by omega, by simp [hinv.2.1], ?_, ?_⟩
  · intro i hi; rw [list_getD_set_ne xs 0#32 _ (by omega)]; exact hinv.2.2.1 i hi
  · intro i hi
    by_cases hie : i = j.toNat
    · subst hie
      rw [list_getD_set_self xs 0#32 _ hi_out, hinv.2.2.1 (a_off.toNat + j.toNat) (by omega)]
    · rw [list_getD_set_ne xs 0#32 _ (by omega)]
      exact hinv.2.2.2 i (by rw [hj1] at hi; omega)

private def extractLoopInv (a_off aw start len : BitVec 32) (hdr0 : BVHdrState)
    (litsPool0 : List (BitVec 32)) : (BitVec 32 × List (BitVec 32)) → Prop :=
  fun (j, xs) =>
    j.toNat ≤ len.toNat ∧
    xs.length = litsPool0.length ∧
    (∀ i < hdr0.lits_len.toNat, xs.getD i 0#32 = litsPool0.getD i 0#32) ∧
    (∀ i < j.toNat, xs.getD (hdr0.lits_len.toNat + i) 0#32 =
      if start.toNat + i < aw.toNat then
        litsPool0.getD (a_off.toNat + (start.toNat + i)) 0#32
      else 0#32)

private theorem extractLoopInv_step {a_off aw start len j : BitVec 32} {hdr0 : BVHdrState}
    {litsPool0 xs : List (BitVec 32)}
    (hinv : extractLoopInv a_off aw start len hdr0 litsPool0 (j, xs)) (hj : j.toNat < len.toNat)
    (hi_out : hdr0.lits_len.toNat + j.toNat < xs.length) :
    let v := if start.toNat + j.toNat < aw.toNat then
        litsPool0.getD (a_off.toNat + (start.toNat + j.toNat)) 0#32 else 0#32
    (j + 1#32).toNat = j.toNat + 1 ∧
      extractLoopInv a_off aw start len hdr0 litsPool0
        (j + 1#32, xs.set (hdr0.lits_len.toNat + j.toNat) v) := by
  have hj1 : (j + 1#32).toNat = j.toNat + 1 := by
    have := len.isLt
    rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  refine ⟨hj1, by omega, by simp [hinv.2.1], ?_, ?_⟩
  · intro i hi; rw [list_getD_set_ne xs 0#32 _ (by omega)]; exact hinv.2.2.1 i hi
  · intro i hi
    by_cases hie : i = j.toNat
    · subst hie; rw [list_getD_set_self xs 0#32 _ hi_out]
    · rw [list_getD_set_ne xs 0#32 _ (by omega)]
      exact hinv.2.2.2 i (by rw [hj1] at hi; omega)

private def appendLoopRInv (rhs_off rw : BitVec 32) (hdr0 : BVHdrState)
    (litsPool0 : List (BitVec 32)) : (BitVec 32 × List (BitVec 32)) → Prop :=
  fun (j, xs) =>
    j.toNat ≤ rw.toNat ∧
    xs.length = litsPool0.length ∧
    (∀ i < hdr0.lits_len.toNat, xs.getD i 0#32 = litsPool0.getD i 0#32) ∧
    (∀ i < j.toNat,
      xs.getD (hdr0.lits_len.toNat + i) 0#32 = litsPool0.getD (rhs_off.toNat + i) 0#32)

private theorem appendLoopRInv_step {rhs_off rw j : BitVec 32} {hdr0 : BVHdrState}
    {litsPool0 xs : List (BitVec 32)}
    (hsR : rhs_off.toNat + rw.toNat ≤ hdr0.lits_len.toNat)
    (hinv : appendLoopRInv rhs_off rw hdr0 litsPool0 (j, xs)) (hj : j.toNat < rw.toNat)
    (hi_out : hdr0.lits_len.toNat + j.toNat < xs.length) :
    (j + 1#32).toNat = j.toNat + 1 ∧
      appendLoopRInv rhs_off rw hdr0 litsPool0
        (j + 1#32, xs.set (hdr0.lits_len.toNat + j.toNat)
          (xs.getD (rhs_off.toNat + j.toNat) 0#32)) := by
  have hj1 : (j + 1#32).toNat = j.toNat + 1 := by
    have := rw.isLt
    rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  refine ⟨hj1, by omega, by simp [hinv.2.1], ?_, ?_⟩
  · intro i hi; rw [list_getD_set_ne xs 0#32 _ (by omega)]; exact hinv.2.2.1 i hi
  · intro i hi
    by_cases hie : i = j.toNat
    · subst hie
      rw [list_getD_set_self xs 0#32 _ hi_out, hinv.2.2.1 (rhs_off.toNat + j.toNat) (by omega)]
    · rw [list_getD_set_ne xs 0#32 _ (by omega)]
      exact hinv.2.2.2 i (by rw [hj1] at hi; omega)

private def appendLoopLInv (lhs_off rhs_off lw rw : BitVec 32) (hdr0 : BVHdrState)
    (litsPool0 : List (BitVec 32)) : (BitVec 32 × List (BitVec 32)) → Prop :=
  fun (j, xs) =>
    j.toNat ≤ lw.toNat ∧
    xs.length = litsPool0.length ∧
    (∀ i < hdr0.lits_len.toNat, xs.getD i 0#32 = litsPool0.getD i 0#32) ∧
    (∀ i < rw.toNat, xs.getD (hdr0.lits_len.toNat + i) 0#32 =
      litsPool0.getD (rhs_off.toNat + i) 0#32) ∧
    (∀ i < j.toNat, xs.getD (hdr0.lits_len.toNat + rw.toNat + i) 0#32 =
      litsPool0.getD (lhs_off.toNat + i) 0#32)

private theorem appendLoopLInv_step {lhs_off rhs_off lw rw j : BitVec 32} {hdr0 : BVHdrState}
    {litsPool0 xs : List (BitVec 32)}
    (hsL : lhs_off.toNat + lw.toNat ≤ hdr0.lits_len.toNat)
    (hinv : appendLoopLInv lhs_off rhs_off lw rw hdr0 litsPool0 (j, xs)) (hj : j.toNat < lw.toNat)
    (hi_out : hdr0.lits_len.toNat + rw.toNat + j.toNat < xs.length) :
    (j + 1#32).toNat = j.toNat + 1 ∧
      appendLoopLInv lhs_off rhs_off lw rw hdr0 litsPool0
        (j + 1#32, xs.set (hdr0.lits_len.toNat + rw.toNat + j.toNat)
          (xs.getD (lhs_off.toNat + j.toNat) 0#32)) := by
  have hj1 : (j + 1#32).toNat = j.toNat + 1 := by
    have := lw.isLt
    rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  refine ⟨hj1, by omega, by simp [hinv.2.1], ?_, ?_, ?_⟩
  · intro i hi; rw [list_getD_set_ne xs 0#32 _ (by omega)]; exact hinv.2.2.1 i hi
  · intro i hi; rw [list_getD_set_ne xs 0#32 _ (by omega)]; exact hinv.2.2.2.1 i hi
  · intro i hi
    by_cases hie : i = j.toNat
    · subst hie
      rw [list_getD_set_self xs 0#32 _ hi_out, hinv.2.2.1 (lhs_off.toNat + j.toNat) (by omega)]
    · rw [list_getD_set_ne xs 0#32 _ (by omega)]
      exact hinv.2.2.2.2 i (by rw [hj1] at hi; omega)

/-! ## 1. `bv_slice_ok_wp` and `bv_blast_get_lsb_d_wp` -/

public section

theorem bv_slice_ok_wp (Γ : Env) :
    ∀ xs m Q X, bvSliceOkSpec xs m Q X → Func.wp Γ bv_slice_ok_body xs m Q X := by
  rintro ⟨h, off, w, ⟨⟩⟩ m Q X ⟨hdr, R, hm, hQ⟩
  c0_hstraight
  c0_hsplit
  · c0_hstraight
    have hgt : hdr.lits_cap.toNat < hdr.lits_len.toNat := by
      simpa [BitVec.ult, BitVec.toNat_setWidth] using hc
    have hsf : sliceBoundsOk hdr off w = false := by
      simp only [sliceBoundsOk, decide_eq_false_iff_not]; omega
    rwa [← hsf]
  · have hle : hdr.lits_len.toNat ≤ hdr.lits_cap.toNat := by
      simpa [BitVec.ult, BitVec.toNat_setWidth] using hc
    clear hc
    refine wp_join_group (fun _ ml => ml = m ∧ (0 < w.toNat → hdr.lits_ptr ≠ 0#64))
      (fun _ ⟨⟩ ml ⟨hml, hptr⟩ => by
        subst hml
        dsimp only [Blocks.get_here]
        c0_hstraight
        refine wp_join_group (fun (b, ⟨⟩) ml2 => ml2 = ml ∧
            (b = true ↔ off.toNat ≤ hdr.lits_len.toNat ∧
              w.toNat ≤ hdr.lits_len.toNat - off.toNat))
          (fun _ ⟨b, ⟨⟩⟩ ml2 ⟨hml2, hb⟩ => by
            subst hml2
            dsimp only [Blocks.get_here]
            c0_hstraight
            have hsb : sliceBoundsOk hdr off w = b := by
              by_cases hb1 : b = true
              · subst hb1; simp only [sliceBoundsOk, decide_eq_true_eq]
                exact ⟨hle, hptr, hb.mp rfl⟩
              · have hbf : b = false := Bool.eq_false_iff.mpr hb1
                subst hbf; simp only [sliceBoundsOk, decide_eq_false_iff_not]
                intro hcon; exact Bool.noConfusion (hb.mpr ⟨hcon.2.2.1, hcon.2.2.2⟩)
            rwa [← hsb])
          (fun J' hJ' => by
            c0_hstraight
            c0_hsplit
            · have hof_le : off.toNat ≤ hdr.lits_len.toNat := hc
              clear hc
              c0_hstraight
              c0_hsplit
              · have hmod : (2 ^ 64 - off.toNat + hdr.lits_len.toNat) % 2 ^ 64 =
                    hdr.lits_len.toNat - off.toNat := by
                  have h1 := hdr.lits_len.isLt; have h2 := off.isLt
                  rw [show 2 ^ 64 - off.toNat + hdr.lits_len.toNat =
                      2 ^ 64 + (hdr.lits_len.toNat - off.toNat) by omega,
                    Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
                have hw_le : w.toNat ≤ hdr.lits_len.toNat - off.toNat := by rw [← hmod]; exact hc
                c0_hstraight
                exact hJ' (true, ⟨⟩) ml ⟨rfl, ⟨fun _ => ⟨hof_le, hw_le⟩, fun _ => rfl⟩⟩
              · c0_hstraight
                apply hJ' (false, ⟨⟩) ml
                refine ⟨rfl, ⟨fun hf => Bool.noConfusion hf, fun ⟨_, hw_le⟩ => ?_⟩⟩
                have h1 := hdr.lits_len.isLt; have h2 := off.isLt
                have hmod : (2 ^ 64 - off.toNat + hdr.lits_len.toNat) % 2 ^ 64 =
                    hdr.lits_len.toNat - off.toNat := by
                  rw [show 2 ^ 64 - off.toNat + hdr.lits_len.toNat =
                      2 ^ 64 + (hdr.lits_len.toNat - off.toNat) by omega,
                    Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
                exact False.elim (hc (hmod ▸ hw_le))
            · c0_hstraight
              apply hJ' (false, ⟨⟩) ml
              refine ⟨rfl, ⟨fun hf => Bool.noConfusion hf, fun ⟨hof_le, _⟩ =>
                False.elim (hc hof_le)⟩⟩))
      (fun J hJ => by
        c0_hstraight
        c0_hsplit
        · have hwpos : 0 < w.toNat := by bv_omega
          clear hc
          c0_hstraight
          c0_hsplit
          · c0_hstraight
            have hsf : sliceBoundsOk hdr off w = false := by
              simp only [sliceBoundsOk, decide_eq_false_iff_not]
              intro hcon; exact hcon.2.1 hwpos hc
            rwa [← hsf]
          · c0_hstraight; exact hJ () m ⟨rfl, fun _ => hc⟩
        · c0_hstraight; exact hJ () m ⟨rfl, fun hw => False.elim (hc (by bv_omega))⟩)

theorem bv_blast_get_lsb_d_wp (Γ : Env)
    (hSliceOk : ∀ xs m Q X, bvSliceOkSpec xs m Q X →
      Γ "bv_slice_ok" [i64, i32, i32] [.bool] xs m Q X) :
    ∀ xs m Q X, bvBlastGetLsbDSpec xs m Q X →
      Func.wp Γ bv_blast_get_lsb_d_body xs m Q X := by
  rintro ⟨h, a_off, aw, idx, ⟨⟩⟩ m Q X ⟨hdr, litsPool, R, hm, hlen, hQ⟩
  refine wp_join_group
    (fun _ ml => ml = m ∧ ¬ (hdr.oom = 0#32 ∧ sliceBoundsOk hdr a_off aw = true))
    (fun _ ⟨⟩ ml ⟨hml, hfail⟩ => by
      subst hml
      dsimp only [Blocks.get_here]
      c0_hstraight
      let hdr' : BVHdrState := { hdr with oom := 1#32 }
      have hfr : hdr.AigFrame hdr' :=
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact hQ 0#32 hdr' _ hfr rfl (fun _ => by simp [hdr'])
        (fun h0 hs => False.elim (hfail ⟨h0, hs⟩))
        (fun h0 => False.elim (by simp [hdr'] at h0)) (fun _ => rfl) (ops_sep_emp3 hm))
    (fun J hJ => by
      c0_hstraight
      c0_hsplit
      · exact hJ () m ⟨rfl, fun ⟨h0, _⟩ => hc h0⟩
      · have h0 : hdr.oom = 0#32 := by bv_omega
        clear hc
        c0_hcall hSliceOk
        · refine ⟨hdr, array (t := i32) hdr.lits_ptr litsPool ⋆ R, ops_sep_assoc_r hm, ?_⟩
          dsimp only [Arg.val]
          c0_hsplit
          · obtain ⟨hs_cap, hs_ptr, hs_sum⟩ := sliceBoundsOk_sum hc
            clear hc
            c0_hstraight
            c0_hsplit
            · have hidx : idx < aw := hc
              clear hc
              have hwrap : a_off.toNat + idx.toNat < 2 ^ 32 := by
                have := hdr.lits_len.isLt; bv_omega
              have hlt_len : a_off.toNat + idx.toNat < litsPool.length := by bv_omega
              have hm_arr : (array (t := i32) hdr.lits_ptr litsPool ⋆ (bvHdrMem h hdr ⋆ R)) m :=
                ops_sep_swap12_r hm
              c0_hstraight
              have hfr : hdr.AigFrame hdr :=
                ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                  rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
              have hget : litsPool[a_off.toNat + idx.toNat]'hlt_len =
                  litsPool.getD (a_off.toNat + idx.toNat) 0#32 :=
                list_getD_eq_getElem litsPool 0#32 hlt_len
              refine hQ _ hdr m hfr rfl (fun hne => absurd h0 hne) (fun _ _ => h0) ?_
                (fun hne => absurd h0 hne) hm
              intro _
              refine ⟨h0, sliceBoundsOk_of_parts hs_cap hs_ptr hs_sum, ?_⟩
              simp [hidx, hget]
            · have hge : ¬ idx < aw := hc
              clear hc
              c0_hstraight
              have hfr : hdr.AigFrame hdr :=
                ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                  rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
              refine hQ 0#32 hdr m hfr rfl (fun hne => absurd h0 hne) (fun _ _ => h0) ?_
                (fun hne => absurd h0 hne) hm
              intro _
              refine ⟨h0, sliceBoundsOk_of_parts hs_cap hs_ptr hs_sum, ?_⟩
              simp [hge]
          · exact hJ () m ⟨rfl, fun ⟨_, hs⟩ => by simp [hs] at hc⟩)

/-! ## 2. `bv_blast_not_wp` -/

theorem bv_blast_not_wp (Γ : Env)
    (hSliceOk : ∀ xs m Q X, bvSliceOkSpec xs m Q X →
      Γ "bv_slice_ok" [i64, i32, i32] [.bool] xs m Q X)
    (hLitsAlloc : ∀ xs m Q X, bvLitsAllocSpec xs m Q X →
      Γ "bv_lits_alloc" [i64, i32] [i32] xs m Q X)
    (hAigNot : ∀ xs m Q X, bvAigNotSpec xs m Q X →
      Γ "bv_aig_not" [i32] [i32] xs m Q X) :
    ∀ xs m Q X, bvBlastNotSpec xs m Q X → Func.wp Γ bv_blast_not_body xs m Q X := by
  rintro ⟨h, a_off, w, ⟨⟩⟩ m Q X ⟨hdr, litsPool, R, hm, hcap, hQ⟩
  refine wp_join_group
    (fun _ ml => ml = m ∧ ¬ (hdr.oom = 0#32 ∧ sliceBoundsOk hdr a_off w = true))
    (fun _ ⟨⟩ ml ⟨hml, hfail⟩ => by
      subst hml
      dsimp only [Blocks.get_here]
      c0_hstraight
      let hdr' : BVHdrState := { hdr with oom := 1#32 }
      have hfr : hdr.BlastFrame hdr' :=
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact hQ 0xFFFFFFFF#32 hdr' litsPool _ hfr rfl rfl (fun _ _ => rfl)
        (fun _ => by simp [hdr']) (fun h0 hs _ => False.elim (hfail ⟨h0, hs⟩))
        (fun h0 => False.elim (by simp [hdr'] at h0)) (fun _ => ⟨rfl, rfl, rfl⟩) (ops_sep_emp3 hm))
    (fun J hJ => by
      c0_hstraight
      c0_hsplit
      · exact hJ () m ⟨rfl, fun ⟨h0, _⟩ => hc h0⟩
      · have h0 : hdr.oom = 0#32 := by bv_omega
        clear hc
        c0_hcall hSliceOk
        · refine ⟨hdr, array (t := i32) hdr.lits_ptr litsPool ⋆ R, ops_sep_assoc_r hm, ?_⟩
          dsimp only [Arg.val]
          c0_hsplit
          · have hsok : sliceBoundsOk hdr a_off w = true := hc
            obtain ⟨hs_cap, _, hs_sum⟩ := sliceBoundsOk_sum hsok
            clear hc
            c0_hcall hLitsAlloc
            · refine ⟨hdr, array (t := i32) hdr.lits_ptr litsPool ⋆ R, ops_sep_assoc_r hm, ?_⟩
              dsimp only [Arg.val]
              split
              · next hroom =>
                intro m1 hm1
                obtain ⟨_, _, hroom'⟩ := hroom
                let hdr1 : BVHdrState := { hdr with lits_len := hdr.lits_len + w }
                have hm1' : (bvHdrMem h hdr1 ⋆
                    array (t := i32) hdr1.lits_ptr litsPool ⋆ R) m1 := ops_sep_assoc_l hm1
                c0_hstraight
                c0_hsplit
                · exfalso; exact hc h0
                · c0_hstraight
                  have hfr : hdr.BlastFrame hdr1 :=
                    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                      rfl, rfl, rfl, rfl, rfl, rfl⟩
                  refine wp_while_record
                    (proj := fun st : BitVec 32 × List (BitVec 32) => (st.1, ⟨⟩))
                    (μ := fun st => w.toNat - st.1.toNat)
                    (Inv := notLoopInv a_off w hdr litsPool)
                    (MemPred := fun st =>
                      bvHdrMem h hdr1 ⋆ array (t := i32) hdr1.lits_ptr st.2)
                    (R := R)
                    (fun Jw hJw => by
                      c0_hstraight
                      have hz : (0#32 : BitVec 32).toNat = 0 := rfl
                      exact hJw (0#32, litsPool) m1
                        ⟨by omega, rfl, fun _ _ => rfl, fun i hi => by omega⟩ hm1')
                    (fun Jw ⟨j, xs⟩ ml hinv hml hrec => by
                      dsimp only [Blocks.get_here] at *
                      c0_hstraight
                      c0_hsplit
                      · have hlt : j.toNat < w.toNat := hc
                        have hwrap_a : a_off.toNat + j.toNat < 2 ^ 32 := by
                          have := hdr.lits_len.isLt; omega
                        have hi_a : a_off.toNat + j.toNat < xs.length := by
                          have := hinv.2.1; omega
                        have hwrap_o : hdr.lits_len.toNat + j.toNat < 2 ^ 32 := by
                          have := hdr.lits_cap.isLt; omega
                        have hi_o : hdr.lits_len.toNat + j.toNat < xs.length := by
                          have := hinv.2.1; omega
                        have hml' : (array (t := i32) hdr1.lits_ptr xs ⋆
                            (bvHdrMem h hdr1 ⋆ R)) ml := ops_sep_swap12_r hml
                        c0_hstraight
                        c0_hcall hAigNot
                        dsimp only [bvAigNotSpec, Arg.val]
                        c0_hstraight
                        rw [ops_list_getElem_eq_getD xs 0#32 _ (ops_setWidth64_add_u32 hwrap_a),
                          ops_setWidth64_add_u32 hwrap_o] at hm
                        obtain ⟨hj1, hinv'⟩ := notLoopInv_step hs_sum hinv hlt hi_o
                        exact hrec (j + 1#32, _) _ (by rw [hj1]; omega) hinv'
                          (ops_sep_swap12_l hm)
                      · have hge : w.toNat ≤ j.toNat := by bv_omega
                        have heq : j.toNat = w.toNat := by have := hinv.1; omega
                        c0_hstraight
                        refine hQ hdr.lits_len hdr1 xs ml hfr rfl hinv.2.1 hinv.2.2.1
                          (fun hne => absurd h0 hne) (fun _ _ _ => h0) ?_
                          (fun hne => absurd h0 hne) hml
                        intro _
                        refine ⟨h0, hsok, hroom', rfl, rfl, fun k hk => ?_⟩
                        exact hinv.2.2.2 k (heq ▸ hk))
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
                  exact hQ 0xFFFFFFFF#32 hdr1 litsPool m1 hfr1 rfl rfl (fun _ _ => rfl)
                    (fun hne => absurd h0 hne)
                    (fun _ _ hr => False.elim (hnroom ⟨h0, hs_cap, hr⟩))
                    (fun h0' => absurd h0' (by rw [hoom1]; decide))
                    (fun _ => ⟨rfl, rfl, rfl⟩) (ops_sep_assoc_l hm1)
                · exfalso; simp [h0] at hc
          · exact hJ () m ⟨rfl, fun ⟨_, hs⟩ => by simp [hs] at hc⟩)

/-! ## 3. `bv_blast_extract_wp` -/

theorem bv_blast_extract_wp (Γ : Env)
    (hSliceOk : ∀ xs m Q X, bvSliceOkSpec xs m Q X →
      Γ "bv_slice_ok" [i64, i32, i32] [.bool] xs m Q X)
    (hLitsAlloc : ∀ xs m Q X, bvLitsAllocSpec xs m Q X →
      Γ "bv_lits_alloc" [i64, i32] [i32] xs m Q X) :
    ∀ xs m Q X, bvBlastExtractSpec xs m Q X →
      Func.wp Γ bv_blast_extract_body xs m Q X := by
  rintro ⟨h, a_off, aw, start, len, ⟨⟩⟩ m Q X ⟨hdr, litsPool, R, hm, hcap, hQ⟩
  refine wp_join_group
    (fun _ ml => ml = m ∧ ¬ (hdr.oom = 0#32 ∧ sliceBoundsOk hdr a_off aw = true))
    (fun _ ⟨⟩ ml ⟨hml, hfail⟩ => by
      subst hml
      dsimp only [Blocks.get_here]
      c0_hstraight
      let hdr' : BVHdrState := { hdr with oom := 1#32 }
      have hfr : hdr.BlastFrame hdr' :=
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact hQ 0xFFFFFFFF#32 hdr' litsPool _ hfr rfl rfl (fun _ _ => rfl)
        (fun _ => by simp [hdr'])
        (fun h0 hex _ => False.elim (hfail ⟨h0, (Bool.and_eq_true _ _ ▸ hex).1⟩))
        (fun h0 => False.elim (by simp [hdr'] at h0)) (fun _ => ⟨rfl, rfl, rfl⟩) (ops_sep_emp3 hm))
    (fun J hJ => by
      c0_hstraight
      c0_hsplit
      · exact hJ () m ⟨rfl, fun ⟨h0, _⟩ => hc h0⟩
      · have h0 : hdr.oom = 0#32 := by bv_omega
        clear hc
        c0_hcall hSliceOk
        · refine ⟨hdr, array (t := i32) hdr.lits_ptr litsPool ⋆ R, ops_sep_assoc_r hm, ?_⟩
          dsimp only [Arg.val]
          c0_hsplit
          · have hsok : sliceBoundsOk hdr a_off aw = true := hc
            obtain ⟨hs_cap, _, hs_sum⟩ := sliceBoundsOk_sum hsok
            clear hc
            refine wp_join_group
              (fun _ ml => ml = m ∧ extractValidOk hdr a_off aw len = true)
              (fun _ ⟨⟩ ml ⟨hml, hext⟩ => by
                subst hml
                dsimp only [Blocks.get_here]
                c0_hcall hLitsAlloc
                · refine ⟨hdr, array (t := i32) hdr.lits_ptr litsPool ⋆ R,
                      ops_sep_assoc_r hm, ?_⟩
                  dsimp only [Arg.val]
                  split
                  · next hroom =>
                    intro m1 hm1
                    obtain ⟨_, _, hroom'⟩ := hroom
                    let hdr1 : BVHdrState := { hdr with lits_len := hdr.lits_len + len }
                    have hm1' : (bvHdrMem h hdr1 ⋆
                        array (t := i32) hdr1.lits_ptr litsPool ⋆ R) m1 := ops_sep_assoc_l hm1
                    c0_hstraight
                    c0_hsplit
                    · exfalso; exact hc h0
                    · c0_hstraight
                      have hfr : hdr.BlastFrame hdr1 :=
                        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                          rfl, rfl, rfl, rfl, rfl, rfl⟩
                      refine wp_while_record
                        (proj := fun st : BitVec 32 × List (BitVec 32) => (st.1, ⟨⟩))
                        (μ := fun st => len.toNat - st.1.toNat)
                        (Inv := extractLoopInv a_off aw start len hdr litsPool)
                        (MemPred := fun st =>
                          bvHdrMem h hdr1 ⋆ array (t := i32) hdr1.lits_ptr st.2)
                        (R := R)
                        (fun Jw hJw => by
                          c0_hstraight
                          have hz : (0#32 : BitVec 32).toNat = 0 := rfl
                          exact hJw (0#32, litsPool) m1
                            ⟨by omega, rfl, fun _ _ => rfl, fun i hi => by omega⟩ hm1')
                        (fun Jw ⟨j, xs⟩ ml2 hinv hml hrec => by
                          dsimp only [Blocks.get_here] at *
                          c0_hstraight
                          c0_hsplit
                          · have hlt : j.toNat < len.toNat := hc
                            clear hc
                            have hwrap_o : hdr.lits_len.toNat + j.toNat < 2 ^ 32 := by
                              have := hdr.lits_cap.isLt; omega
                            have hi_o : hdr.lits_len.toNat + j.toNat < xs.length := by
                              have := hinv.2.1; omega
                            have hpos_v :
                                (BitVec.setWidth 64 start + BitVec.setWidth 64 j).toNat =
                                start.toNat + j.toNat := by
                              have h1 := start.isLt; have h2 := j.isLt
                              simp only [BitVec.toNat_add, BitVec.toNat_setWidth,
                                Nat.mod_eq_of_lt (by omega : start.toNat < 2 ^ 64),
                                Nat.mod_eq_of_lt (by omega : j.toNat < 2 ^ 64),
                                Nat.mod_eq_of_lt (by omega : start.toNat + j.toNat < 2 ^ 64)]
                            c0_hstraight
                            let vj : BitVec 32 := if start.toNat + j.toNat < aw.toNat then
                                litsPool.getD (a_off.toNat + (start.toNat + j.toNat)) 0#32
                              else 0#32
                            let xs' := xs.set (hdr.lits_len.toNat + j.toNat) vj
                            refine wp_join_group (fun _ ml' =>
                                (bvHdrMem h hdr1 ⋆ array (t := i32) hdr1.lits_ptr xs' ⋆ R) ml')
                              (fun _ ⟨⟩ ml' hm' => by
                                dsimp only [Blocks.get_here]
                                c0_hstraight
                                obtain ⟨hj1, hinv'⟩ := extractLoopInv_step hinv hlt hi_o
                                exact hrec (j + 1#32, xs') ml' (by rw [hj1]; omega) hinv' hm')
                              (fun Js1 hJs1 => by
                                c0_hstraight
                                c0_hsplit
                                · have hlt_aw : start.toNat + j.toNat < aw.toNat := by
                                    rw [← hpos_v]; exact hc
                                  have hpos32 : (BitVec.setWidth 64 start +
                                      BitVec.setWidth 64 j).toNat < 2 ^ 32 := by
                                    have := aw.isLt; omega
                                  have hwa : a_off.toNat + (BitVec.setWidth 64 start +
                                      BitVec.setWidth 64 j).toNat < 2 ^ 32 := by
                                    have := hdr.lits_len.isLt; omega
                                  have hia : a_off.toNat + (BitVec.setWidth 64 start +
                                      BitVec.setWidth 64 j).toNat < xs.length := by
                                    have := hinv.2.1; omega
                                  have hml' : (array (t := i32) hdr1.lits_ptr xs ⋆
                                      (bvHdrMem h hdr1 ⋆ R)) ml2 := ops_sep_swap12_r hml
                                  c0_hstraight
                                  rw [ops_setWidth64_add_u32 hwrap_o,
                                    ops_list_getElem_eq_getD xs 0#32 _
                                      (by rw [ops_setWidth64_ext_u32 hpos32 hwa, hpos_v])] at hm
                                  have hget_vj : xs.getD (a_off.toNat +
                                      (start.toNat + j.toNat)) 0#32 = vj := by
                                    have hidx_lt : a_off.toNat + (start.toNat + j.toNat) <
                                        hdr.lits_len.toNat := by omega
                                    rw [hinv.2.2.1 _ hidx_lt]
                                    simp [vj, hlt_aw]
                                  rw [hget_vj] at hm
                                  exact hJs1 () _ (ops_sep_swap12_l hm)
                                · have hge_aw : ¬ start.toNat + j.toNat < aw.toNat := by
                                    rw [← hpos_v]; exact hc
                                  have hml' : (array (t := i32) hdr1.lits_ptr xs ⋆
                                      (bvHdrMem h hdr1 ⋆ R)) ml2 := ops_sep_swap12_r hml
                                  c0_hstraight
                                  have hveq : (0 : BitVec 32) = vj := by simp [vj, hge_aw]
                                  rw [ops_setWidth64_add_u32 hwrap_o, hveq] at hm
                                  exact hJs1 () _ (ops_sep_swap12_l hm))
                          · have hge : len.toNat ≤ j.toNat := by bv_omega
                            have heq : j.toNat = len.toNat := by have := hinv.1; omega
                            c0_hstraight
                            refine hQ hdr.lits_len hdr1 xs ml2 hfr rfl hinv.2.1 hinv.2.2.1
                              (fun hne => absurd h0 hne) (fun _ _ _ => h0) ?_
                              (fun hne => absurd h0 hne) hml
                            intro _
                            refine ⟨h0, hext, hroom', rfl, rfl, fun k hk => ?_⟩
                            exact hinv.2.2.2 k (heq ▸ hk))
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
                      exact hQ 0xFFFFFFFF#32 hdr1 litsPool m1 hfr1 rfl rfl (fun _ _ => rfl)
                        (fun hne => absurd h0 hne)
                        (fun _ _ hr => False.elim (hnroom ⟨h0, hs_cap, hr⟩))
                        (fun h0' => absurd h0' (by rw [hoom1]; decide))
                        (fun _ => ⟨rfl, rfl, rfl⟩) (ops_sep_assoc_l hm1)
                    · exfalso; simp [h0] at hc)
              (fun J2 hJ2 => by
                c0_hstraight
                c0_hsplit
                · have hlen_pos : 0 < len.toNat := by bv_omega
                  clear hc
                  c0_hstraight
                  c0_hsplit
                  · c0_hstraight
                    let hdr' : BVHdrState := { hdr with oom := 1#32 }
                    have hfr : hdr.BlastFrame hdr' :=
                      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                        rfl, rfl, rfl, rfl, rfl, rfl⟩
                    have hne_ex : extractValidOk hdr a_off aw len = false := by
                      simp only [extractValidOk, hsok, Bool.true_and, decide_eq_false_iff_not]
                      intro hcon; exact hcon hlen_pos hc
                    exact hQ 0xFFFFFFFF#32 hdr' litsPool _ hfr rfl rfl (fun _ _ => rfl)
                      (fun hne => absurd h0 hne) (fun _ hex _ => by rw [hne_ex] at hex; cases hex)
                      (fun h0' => False.elim (by simp [hdr'] at h0'))
                      (fun _ => ⟨rfl, rfl, rfl⟩) (ops_sep_emp3 hm)
                  · c0_hstraight
                    have hext : extractValidOk hdr a_off aw len = true := by
                      simp only [extractValidOk, hsok, Bool.true_and, decide_eq_true_eq]
                      exact fun _ => hc
                    exact hJ2 () m ⟨rfl, hext⟩
                · c0_hstraight
                  have hext : extractValidOk hdr a_off aw len = true := by
                    simp only [extractValidOk, hsok, Bool.true_and, decide_eq_true_eq]
                    intro hpos; exfalso; exact hc (by bv_omega)
                  exact hJ2 () m ⟨rfl, hext⟩)
          · exact hJ () m ⟨rfl, fun ⟨_, hs⟩ => by simp [hs] at hc⟩)

/-! ## 4. `bv_blast_append_wp` -/

theorem bv_blast_append_wp (Γ : Env)
    (hSliceOk : ∀ xs m Q X, bvSliceOkSpec xs m Q X →
      Γ "bv_slice_ok" [i64, i32, i32] [.bool] xs m Q X)
    (hLitsAlloc : ∀ xs m Q X, bvLitsAllocSpec xs m Q X →
      Γ "bv_lits_alloc" [i64, i32] [i32] xs m Q X) :
    ∀ xs m Q X, bvBlastAppendSpec xs m Q X →
      Func.wp Γ bv_blast_append_body xs m Q X := by
  rintro ⟨h, lhs_off, lw, rhs_off, rw, ⟨⟩⟩ m Q X ⟨hdr, litsPool, R, hm, hcap, hQ⟩
  refine wp_join_group
    (fun _ ml => ml = m ∧ ¬ (hdr.oom = 0#32 ∧
      sliceBoundsOk hdr lhs_off lw = true ∧ sliceBoundsOk hdr rhs_off rw = true))
    (fun _ ⟨⟩ ml ⟨hml, hfail⟩ => by
      subst hml
      dsimp only [Blocks.get_here]
      c0_hstraight
      let hdr' : BVHdrState := { hdr with oom := 1#32 }
      have hfr : hdr.BlastFrame hdr' :=
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact hQ 0xFFFFFFFF#32 hdr' litsPool _ hfr rfl rfl (fun _ _ => rfl)
        (fun _ => by simp [hdr']) (fun h0 h1 h2 _ => False.elim (hfail ⟨h0, h1, h2⟩))
        (fun h0 => False.elim (by simp [hdr'] at h0)) (fun _ => ⟨rfl, rfl, rfl⟩) (ops_sep_emp3 hm))
    (fun J hJ => by
      c0_hstraight
      c0_hsplit
      · exact hJ () m ⟨rfl, fun ⟨h0, _⟩ => hc h0⟩
      · have h0 : hdr.oom = 0#32 := by bv_omega
        clear hc
        c0_hcall hSliceOk
        · refine ⟨hdr, array (t := i32) hdr.lits_ptr litsPool ⋆ R, ops_sep_assoc_r hm, ?_⟩
          dsimp only [Arg.val]
          c0_hsplit
          · have hsL : sliceBoundsOk hdr lhs_off lw = true := hc
            obtain ⟨hsL_cap, _, hsL_sum⟩ := sliceBoundsOk_sum hsL
            clear hc
            c0_hcall hSliceOk
            · refine ⟨hdr, array (t := i32) hdr.lits_ptr litsPool ⋆ R, ops_sep_assoc_r hm, ?_⟩
              dsimp only [Arg.val]
              c0_hsplit
              · have hsR : sliceBoundsOk hdr rhs_off rw = true := hc
                obtain ⟨_, _, hsR_sum⟩ := sliceBoundsOk_sum hsR
                clear hc
                c0_hstraight
                have htot64 : (BitVec.setWidth 64 lw + BitVec.setWidth 64 rw).toNat =
                    lw.toNat + rw.toNat := by
                  have h1 := lw.isLt; have h2 := rw.isLt
                  simp only [BitVec.toNat_add, BitVec.toNat_setWidth,
                    Nat.mod_eq_of_lt (by omega : lw.toNat < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega : rw.toNat < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega : lw.toNat + rw.toNat < 2 ^ 64)]
                c0_hsplit
                · have hov : 4294967295 < lw.toNat + rw.toNat := by
                    simpa [BitVec.ult, htot64] using hc
                  c0_hstraight
                  let hdr' : BVHdrState := { hdr with oom := 1#32 }
                  have hfr : hdr.BlastFrame hdr' :=
                    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                      rfl, rfl, rfl, rfl, rfl, rfl⟩
                  exact hQ 0xFFFFFFFF#32 hdr' litsPool _ hfr rfl rfl (fun _ _ => rfl)
                    (fun hne => absurd h0 hne)
                    (fun _ _ _ hroom => False.elim (by have := hdr.lits_cap.isLt; omega))
                    (fun h0' => False.elim (by simp [hdr'] at h0'))
                    (fun _ => ⟨rfl, rfl, rfl⟩) (ops_sep_emp3 hm)
                · have hfit : lw.toNat + rw.toNat < 2 ^ 32 := by
                    have h1 := lw.isLt; have h2 := rw.isLt
                    have hle := hc
                    rw [Nat.mod_eq_of_lt (by omega : lw.toNat + rw.toNat < 2 ^ 64)] at hle
                    have hmax : BitVec.toNat (4294967295 : BitVec 64) = 4294967295 := rfl
                    omega
                  clear hc
                  have htr : BitVec.setWidth 32 (BitVec.setWidth 64 lw + BitVec.setWidth 64 rw) =
                      lw + rw := by
                    apply BitVec.eq_of_toNat_eq
                    simp only [BitVec.toNat_setWidth, htot64, BitVec.toNat_add,
                      Nat.mod_eq_of_lt hfit]
                  c0_hstraight
                  rw [htr]
                  c0_hcall hLitsAlloc
                  · refine ⟨hdr, array (t := i32) hdr.lits_ptr litsPool ⋆ R,
                        ops_sep_assoc_r hm, ?_⟩
                    dsimp only [Arg.val]
                    have hsum32 : (lw + rw).toNat = lw.toNat + rw.toNat := by
                      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hfit]
                    split
                    · next hroom =>
                      intro m1 hm1
                      obtain ⟨_, _, hroom_le⟩ := hroom
                      let hdr1 : BVHdrState := { hdr with lits_len := hdr.lits_len + (lw + rw) }
                      have hroom' : lw.toNat + rw.toNat ≤
                          hdr.lits_cap.toNat - hdr.lits_len.toNat := by
                        simpa [hsum32] using hroom_le
                      have hm1' : (bvHdrMem h hdr1 ⋆
                          array (t := i32) hdr1.lits_ptr litsPool ⋆ R) m1 := ops_sep_assoc_l hm1
                      c0_hstraight
                      c0_hsplit
                      · exfalso; exact hc h0
                      · c0_hstraight
                        have hfr : hdr.BlastFrame hdr1 :=
                          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                            rfl, rfl, rfl, rfl, rfl, rfl⟩
                        refine wp_while_record
                          (proj := fun st : BitVec 32 × List (BitVec 32) => (st.1, ⟨⟩))
                          (μ := fun st => rw.toNat - st.1.toNat)
                          (Inv := appendLoopRInv rhs_off rw hdr litsPool)
                          (MemPred := fun st =>
                            bvHdrMem h hdr1 ⋆ array (t := i32) hdr1.lits_ptr st.2)
                          (R := R)
                          (fun J1 hJ1 => by
                            c0_hstraight
                            have hz : (0#32 : BitVec 32).toNat = 0 := rfl
                            exact hJ1 (0#32, litsPool) m1
                              ⟨by omega, rfl, fun _ _ => rfl, fun i hi => by omega⟩ hm1')
                          (fun J1 ⟨j, xs⟩ ml hinv1 hml1 hrec1 => by
                            dsimp only [Blocks.get_here] at *
                            c0_hstraight
                            c0_hsplit
                            · have hlt : j.toNat < rw.toNat := hc
                              have hwr : rhs_off.toNat + j.toNat < 2 ^ 32 := by
                                have := hdr.lits_len.isLt; omega
                              have hir : rhs_off.toNat + j.toNat < xs.length := by
                                have := hinv1.2.1; omega
                              have hwo : hdr.lits_len.toNat + j.toNat < 2 ^ 32 := by
                                have := hdr.lits_cap.isLt; omega
                              have hio : hdr.lits_len.toNat + j.toNat < xs.length := by
                                have := hinv1.2.1; omega
                              have hml1' : (array (t := i32) hdr1.lits_ptr xs ⋆
                                  (bvHdrMem h hdr1 ⋆ R)) ml := ops_sep_swap12_r hml1
                              c0_hstraight
                              rw [ops_setWidth64_add_u32 hwo, ops_list_getElem_eq_getD xs 0#32 _
                                (ops_setWidth64_add_u32 hwr)] at hm
                              obtain ⟨hj1, hinv1'⟩ :=
                                appendLoopRInv_step hsR_sum hinv1 hlt hio
                              exact hrec1 (j + 1#32, _) _ (by rw [hj1]; omega) hinv1'
                                (ops_sep_swap12_l hm)
                            · have hge : rw.toNat ≤ j.toNat := by bv_omega
                              have heq : j.toNat = rw.toNat := by have := hinv1.1; omega
                              clear hc
                              refine wp_while_record
                                (proj := fun st : BitVec 32 × List (BitVec 32) => (st.1, ⟨⟩))
                                (μ := fun st => lw.toNat - st.1.toNat)
                                (Inv := appendLoopLInv lhs_off rhs_off lw rw hdr litsPool)
                                (MemPred := fun st =>
                                  bvHdrMem h hdr1 ⋆ array (t := i32) hdr1.lits_ptr st.2)
                                (R := R)
                                (fun J2 hJ2 => by
                                  c0_hstraight
                                  have hz : (0#32 : BitVec 32).toNat = 0 := rfl
                                  refine hJ2 (0#32, xs) ml
                                    ⟨by omega, hinv1.2.1, hinv1.2.2.1, ?_, fun i hi => by omega⟩
                                    hml1
                                  intro i hi; exact hinv1.2.2.2 i (heq ▸ hi))
                                (fun J2 ⟨k, xs2⟩ ml2 hinv2 hml2 hrec2 => by
                                  dsimp only [Blocks.get_here] at *
                                  c0_hstraight
                                  c0_hsplit
                                  · have hlt2 : k.toNat < lw.toNat := hc
                                    have hwl : lhs_off.toNat + k.toNat < 2 ^ 32 := by
                                      have := hdr.lits_len.isLt; omega
                                    have hil : lhs_off.toNat + k.toNat < xs2.length := by
                                      have := hinv2.2.1; omega
                                    have hwrw : hdr.lits_len.toNat + rw.toNat < 2 ^ 32 := by
                                      have := hdr.lits_cap.isLt; omega
                                    have hwo2 :
                                        hdr.lits_len.toNat + rw.toNat + k.toNat < 2 ^ 32 := by
                                      have := hdr.lits_cap.isLt; omega
                                    have hio2 :
                                        hdr.lits_len.toNat + rw.toNat + k.toNat < xs2.length := by
                                      have := hinv2.2.1; omega
                                    have hml2' : (array (t := i32) hdr1.lits_ptr xs2 ⋆
                                        (bvHdrMem h hdr1 ⋆ R)) ml2 :=
                                      ops_sep_swap12_r hml2
                                    c0_hstraight
                                    rw [ops_setWidth64_add3_u32 hwrw hwo2,
                                      ops_list_getElem_eq_getD xs2 0#32 _
                                        (ops_setWidth64_add_u32 hwl)] at hm
                                    obtain ⟨hk1, hinv2'⟩ :=
                                      appendLoopLInv_step hsL_sum hinv2 hlt2 hio2
                                    exact hrec2 (k + 1#32, _) _ (by rw [hk1]; omega) hinv2'
                                      (ops_sep_swap12_l hm)
                                  · have hge2 : lw.toNat ≤ k.toNat := by bv_omega
                                    have heq2 : k.toNat = lw.toNat := by have := hinv2.1; omega
                                    c0_hstraight
                                    refine hQ hdr.lits_len hdr1 xs2 ml2 hfr rfl hinv2.2.1
                                      hinv2.2.2.1 (fun hne => absurd h0 hne) (fun _ _ _ _ => h0) ?_
                                      (fun hne => absurd h0 hne) hml2
                                    intro _
                                    refine ⟨h0, hsL, hsR, hroom', rfl, rfl, hsum32,
                                      hinv2.2.2.2.1, fun i hi => ?_⟩
                                    exact hinv2.2.2.2.2 i (heq2 ▸ hi)))
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
                        exact hQ 0xFFFFFFFF#32 hdr1 litsPool m1 hfr1 rfl rfl (fun _ _ => rfl)
                          (fun hne => absurd h0 hne)
                          (fun _ _ _ hr => False.elim (hnroom ⟨h0, hsL_cap, by omega⟩))
                          (fun h0' => absurd h0' (by rw [hoom1]; decide))
                          (fun _ => ⟨rfl, rfl, rfl⟩) (ops_sep_assoc_l hm1)
                      · exfalso; simp [h0] at hc
              · exact hJ () m ⟨rfl, fun ⟨_, _, hs⟩ => by simp [hs] at hc⟩
          · exact hJ () m ⟨rfl, fun ⟨_, hs, _⟩ => by simp [hs] at hc⟩)

end

end LeanQbe.T.Examples.Bitblast.Proof
