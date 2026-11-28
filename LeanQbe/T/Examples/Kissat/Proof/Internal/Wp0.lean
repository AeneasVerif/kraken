/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Internal.Spec
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation
meta import Lean.Elab.Command

/-!
# Kissat Internal Sizing, Header & Pointer WP Proofs (`Proof.Internal.Wp0`)

Shared `hdrTail4` / region-peeling helpers (zero `import all`, zero `@[expose]` on theorems)
and parametric `(Γ : Env)` `Func.wp` proofs for `6` functions:
1. `full_fixed_bytes_wp`
2. `full_calc_ext_cap_m5_wp`
3. `full_calc_scr_cap_m5_wp`
4. `full_calc_max_v_wp`
5. `full_init_ptrs_wp`
6. `full_init_hdr_wp`
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

/-! ## 1. Shared `hdrTail4`, Region-Peeling & Pointer Layout Helpers -/

@[expose] def hdrTail4 (hdr : BitVec 64) (w0 w1 w2 w3 : List (BitVec 64)) : Mem 64 → Prop :=
  array64 (hdr + 32) w0 ⋆ array64 (hdr + 312) w1 ⋆
  array64 (hdr + 592) w2 ⋆ array64 (hdr + 872) w3

@[expose] def hdrSet (w : List (BitVec 64)) (i : Nat) (v : BitVec 64) : List (BitVec 64) :=
  w.set i v

theorem hdrSet_eq (w : List (BitVec 64)) (i : Nat) (v : BitVec 64) :
    hdrSet w i v = w.set i v := rfl

theorem hdrSet_len (w : List (BitVec 64)) (i : Nat) (v : BitVec 64) :
    (hdrSet w i v).length = w.length := List.length_set

@[expose] def hdrTail4Len (hdr : BitVec 64) (w0 w1 w2 w3 : List (BitVec 64)) :
    Mem 64 → Prop :=
  fun m => (w0.length = 35 ∧ w1.length = 35 ∧ w2.length = 35 ∧ w3.length = 35) ∧
    hdrTail4 hdr w0 w1 w2 w3 m

theorem array64_append_eq (a : BitVec 64) (xs ys : List (BitVec 64)) :
    array64 a (xs ++ ys) =
      (array64 a xs ⋆ array64 (a + BitVec.ofNat 64 (8 * xs.length)) ys) := by
  rw [array64_eq_array, array64_eq_array, array64_eq_array, array_append]
  simp [Ty.bytes, Ty.size, i64]

theorem hdrTail4_eq_array64 {hdr : BitVec 64} {w0 w1 w2 w3 : List (BitVec 64)}
    (h0 : w0.length = 35) (h1 : w1.length = 35) (h2 : w2.length = 35) :
    hdrTail4 hdr w0 w1 w2 w3 = array64 (hdr + 32) (w0 ++ w1 ++ w2 ++ w3) := by
  unfold hdrTail4
  rw [array64_append_eq, array64_append_eq, array64_append_eq]
  simp only [List.length_append, h0, h1, h2]
  rw [show hdr + 32 + BitVec.ofNat 64 (8 * 35) = hdr + 312 from by rw [BitVec.add_assoc]; rfl,
      show hdr + 32 + BitVec.ofNat 64 (8 * (35 + 35)) = hdr + 592 from by
        rw [BitVec.add_assoc]; rfl,
      show hdr + 32 + BitVec.ofNat 64 (8 * (35 + 35 + 35)) = hdr + 872 from by
        rw [BitVec.add_assoc]; rfl]

theorem array64_to_hdrTail4 {hdr : BitVec 64} {ws : List (BitVec 64)} {R : Mem 64 → Prop}
    {m : Mem 64} (hw : ws.length = 140) (hm : (array64 (hdr + 32) ws ⋆ R) m) :
    (hdrTail4 hdr (ws.take 35) ((ws.drop 35).take 35) ((ws.drop 70).take 35)
      ((ws.drop 105).take 35) ⋆ R) m := by
  have h1 : (ws.take 35).length = 35 := by simp [hw]
  have h2 : ((ws.drop 35).take 35).length = 35 := by simp [hw]
  have h3 : ((ws.drop 70).take 35).length = 35 := by simp [hw]
  have hsp : ws.take 35 ++ (ws.drop 35).take 35 ++ (ws.drop 70).take 35 ++
      (ws.drop 105).take 35 = ws := by
    have hd1 : (ws.drop 35).drop 35 = ws.drop 70 := by rw [List.drop_drop]
    have hd2 : (ws.drop 70).drop 35 = ws.drop 105 := by rw [List.drop_drop]
    have ht4 : (ws.drop 105).take 35 = ws.drop 105 := List.take_of_length_le (by simp [hw])
    rw [ht4]; simp only [List.append_assoc]
    rw [← hd2, List.take_append_drop, ← hd1, List.take_append_drop, List.take_append_drop]
  rw [hdrTail4_eq_array64 h1 h2 h3, hsp]; exact hm

theorem append4_getElem?_0 {α : Type} {w0 w1 w2 w3 : List α} (h0 : w0.length = 35)
    {i : Nat} (hi : i < 35) : (w0 ++ w1 ++ w2 ++ w3)[i]? = w0[i]? := by
  simp only [List.append_assoc]; exact List.getElem?_append_left (by omega)

theorem append4_getElem?_1 {α : Type} {w0 w1 w2 w3 : List α} (h0 : w0.length = 35)
    (h1 : w1.length = 35) {i : Nat} (hi0 : 35 ≤ i) (hi1 : i < 70) :
    (w0 ++ w1 ++ w2 ++ w3)[i]? = w1[i - 35]? := by
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by omega), h0, List.getElem?_append_left (by omega)]

theorem append4_getElem?_2 {α : Type} {w0 w1 w2 w3 : List α} (h0 : w0.length = 35)
    (h1 : w1.length = 35) (h2 : w2.length = 35) {i : Nat} (hi0 : 70 ≤ i) (hi1 : i < 105) :
    (w0 ++ w1 ++ w2 ++ w3)[i]? = w2[i - 70]? := by
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by omega), h0, List.getElem?_append_right (by omega), h1,
    List.getElem?_append_left (by omega), show i - 35 - 35 = i - 70 by omega]

theorem append4_getElem?_3 {α : Type} {w0 w1 w2 w3 : List α} (h0 : w0.length = 35)
    (h1 : w1.length = 35) (h2 : w2.length = 35) {i : Nat} (hi0 : 105 ≤ i) :
    (w0 ++ w1 ++ w2 ++ w3)[i]? = w3[i - 105]? := by
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by omega), h0, List.getElem?_append_right (by omega), h1,
    List.getElem?_append_right (by omega), h2, show i - 35 - 35 - 35 = i - 105 by omega]

theorem drop_take_getElem? {α : Type} (xs : List α) (off n i : Nat) (hi : i < n) :
    ((xs.drop off).take n)[i]? = xs[off + i]? := by
  rw [List.getElem?_take_of_lt hi, List.getElem?_drop]

theorem reg_peel {a b : BitVec 64} {n1 n2 n : Nat} {m : Mem 64} (hm : region a n m)
    (hb : a + BitVec.ofNat 64 n1 = b := by rfl) (hn : n = n1 + n2 := by omega)
    (hle : n1 + n2 ≤ 2 ^ 64 := by omega) : (region a n1 ⋆ region b n2) m := by
  subst hb hn
  rwa [← region_merge_eq (a := a) (n1 := n1) (n2 := n2) (n := n1 + n2) rfl hle] at hm

theorem reg_pad_i8 {a : BitVec 64} (k : Nat) {n : Nat} {m : Mem 64} (hm : region a n m)
    (hk : k ≤ n := by omega) (hle : n ≤ 2 ^ 64 := by omega) :
    ∃ xs : List (BitVec 8), xs.length = k ∧
      (array (t := i8) a xs ⋆ region (a + BitVec.ofNat 64 k) (n - k)) m := by
  have h1 := sep_mono (fun _ hr => region_to_array_i8 k (by omega) hr)
    (reg_peel (n1 := k) (n2 := n - k) hm)
  simp only [sep_ex_l, sep_pure_l] at h1
  exact h1

theorem reg_pad_i32 {a : BitVec 64} (k : Nat) {n : Nat} {m : Mem 64} (hm : region a n m)
    (hk : 4 * k ≤ n := by omega) (hle : n ≤ 2 ^ 64 := by omega) :
    ∃ xs : List (BitVec 32), xs.length = k ∧
      (array (t := i32) a xs ⋆ region (a + BitVec.ofNat 64 (4 * k)) (n - 4 * k)) m := by
  have h1 := sep_mono (fun _ hr => region_to_array_i32 k (by omega) hr)
    (reg_peel (n1 := 4 * k) (n2 := n - 4 * k) hm)
  simp only [sep_ex_l, sep_pure_l] at h1
  exact h1

theorem peel_step_i8 {A Q : Mem 64 → Prop} {a b : BitVec 64} (k n1 n2 n : Nat)
    {m : Mem 64} (hm : ((A ⋆ Q) ⋆ region a n) m)
    (hb : a + BitVec.ofNat 64 n1 = b := by rfl) (hn : n = n1 + n2 := by omega)
    (hk : k ≤ n1 := by omega) (hle : n1 + n2 ≤ 2 ^ 64 := by omega) :
    ∃ xs : List (BitVec 8), xs.length = k ∧
      (((A ⋆ array (t := i8) a xs) ⋆ (Q ⋆ region (a + BitVec.ofNat 64 k) (n1 - k))) ⋆
        region b n2) m := by
  have hm1 := sep_mono_r (fun _ hr =>
    sep_mono (fun _ h1 => reg_pad_i8 k h1 hk (by omega)) (reg_peel hr hb hn hle)) hm
  simp only [sep_ex_l, sep_ex_r, sep_pure_l, sep_pure_r] at hm1
  obtain ⟨xs, hl, hm2⟩ := hm1
  exact ⟨xs, hl, sep_ac hm2⟩

theorem peel_step_i32 {A Q : Mem 64 → Prop} {a b : BitVec 64} (k n1 n2 n : Nat)
    {m : Mem 64} (hm : ((A ⋆ Q) ⋆ region a n) m)
    (hb : a + BitVec.ofNat 64 n1 = b := by rfl) (hn : n = n1 + n2 := by omega)
    (hk : 4 * k ≤ n1 := by omega) (hle : n1 + n2 ≤ 2 ^ 64 := by omega) :
    ∃ xs : List (BitVec 32), xs.length = k ∧
      (((A ⋆ array (t := i32) a xs) ⋆ (Q ⋆ region (a + BitVec.ofNat 64 (4 * k)) (n1 - 4 * k))) ⋆
        region b n2) m := by
  have hm1 := sep_mono_r (fun _ hr =>
    sep_mono (fun _ h1 => reg_pad_i32 k h1 hk (by omega)) (reg_peel hr hb hn hle)) hm
  simp only [sep_ex_l, sep_ex_r, sep_pure_l, sep_pure_r] at hm1
  obtain ⟨xs, hl, hm2⟩ := hm1
  exact ⟨xs, hl, sep_ac hm2⟩

theorem peel_step_exact_i32 {A : Mem 64 → Prop} {a b : BitVec 64} (k n2 n : Nat)
    {m : Mem 64} (hm : (A ⋆ region a n) m)
    (hb : a + BitVec.ofNat 64 (4 * k) = b := by rfl) (hn : n = 4 * k + n2 := by omega)
    (hle : 4 * k + n2 ≤ 2 ^ 64 := by omega) :
    ∃ xs : List (BitVec 32), xs.length = k ∧ ((A ⋆ array (t := i32) a xs) ⋆ region b n2) m := by
  have hm1 := sep_mono_r (fun _ hr =>
    sep_mono (fun _ h1 => region_to_array_i32 k (by omega) h1) (reg_peel hr hb hn hle)) hm
  simp only [sep_ex_l, sep_ex_r, sep_pure_l, sep_pure_r] at hm1
  obtain ⟨xs, hl, hm2⟩ := hm1
  exact ⟨xs, hl, sep_ac hm2⟩

theorem peel_step_exact_i64 {A : Mem 64 → Prop} {a b : BitVec 64} (k n2 n : Nat)
    {m : Mem 64} (hm : (A ⋆ region a n) m)
    (hb : a + BitVec.ofNat 64 (8 * k) = b := by rfl) (hn : n = 8 * k + n2 := by omega)
    (hle : 8 * k + n2 ≤ 2 ^ 64 := by omega) :
    ∃ xs : List (BitVec 64), xs.length = k ∧ ((A ⋆ array64 a xs) ⋆ region b n2) m := by
  have hm1 := sep_mono_r (fun _ hr =>
    sep_mono (fun _ h1 => region_to_array64 k (by omega) h1) (reg_peel hr hb hn hle)) hm
  simp only [sep_ex_l, sep_ex_r, sep_pure_l, sep_pure_r] at hm1
  obtain ⟨xs, hl, hm2⟩ := hm1
  exact ⟨xs, hl, sep_ac hm2⟩

/-! ### Pure `FullCfg` pointer sequence matching `full_init_ptrs` -/

@[expose] def fullPVals (hdr : BitVec 64) (_mx : Nat) : BitVec 64 := hdr + BitVec.ofNat 64 1152
@[expose] def fullPWalkVals (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPVals hdr mx + BitVec.ofNat 64 (valsBytes mx)
@[expose] def fullPLitMark (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPWalkVals hdr mx + BitVec.ofNat 64 (valsBytes mx)
@[expose] def fullPMark (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPLitMark hdr mx + BitVec.ofNat 64 (valsBytes mx)
@[expose] def fullPPhases (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPMark hdr mx + BitVec.ofNat 64 (markBytes mx)
@[expose] def fullPPhasesTarget (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPPhases hdr mx + BitVec.ofNat 64 (markBytes mx)
@[expose] def fullPPhasesBest (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPPhasesTarget hdr mx + BitVec.ofNat 64 (markBytes mx)
@[expose] def fullPWalkBest (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPPhasesBest hdr mx + BitVec.ofNat 64 (markBytes mx)
@[expose] def fullPFlags (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPWalkBest hdr mx + BitVec.ofNat 64 (markBytes mx)
@[expose] def fullPLevel (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPFlags hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
@[expose] def fullPReason (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPLevel hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
@[expose] def fullPTrail (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPReason hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
@[expose] def fullPTrailPos (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPTrail hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
@[expose] def fullPTmp (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPTrailPos hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
@[expose] def fullPHeap (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPTmp hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
@[expose] def fullPPos (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPHeap hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
@[expose] def fullPMinClr (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPPos hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
@[expose] def fullPShrinkStk (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPMinClr hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
@[expose] def fullPQPrev (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPShrinkStk hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
@[expose] def fullPQNext (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPQPrev hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
@[expose] def fullPQStamp (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPQNext hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
@[expose] def fullPFrameTrail (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPQStamp hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
@[expose] def fullPFrameDec (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPFrameTrail hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
@[expose] def fullPWvec (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPFrameDec hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
@[expose] def fullPRepr (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPWvec hdr mx + BitVec.ofNat 64 (16 * mx)
@[expose] def fullPWsort (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPRepr hdr mx + BitVec.ofNat 64 (8 * mx)
@[expose] def fullPWorkStk1 (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPWsort hdr mx + BitVec.ofNat 64 (8 * mx)
@[expose] def fullPWorkStk2 (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPWorkStk1 hdr mx + BitVec.ofNat 64 (8 * mx)
@[expose] def fullPTarjanMark (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPWorkStk2 hdr mx + BitVec.ofNat 64 (8 * mx)
@[expose] def fullPTarjanReach (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPTarjanMark hdr mx + BitVec.ofNat 64 (8 * mx)
@[expose] def fullPScore (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPTarjanReach hdr mx + BitVec.ofNat 64 (8 * mx)
@[expose] def fullPSimSig (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPScore hdr mx + BitVec.ofNat 64 (8 * mx)
@[expose] def fullPMinStk (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPSimSig hdr mx + BitVec.ofNat 64 (8 * mx)
@[expose] def fullPGlueUsed (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPMinStk hdr mx + BitVec.ofNat 64 (8 * fullMinDepthOf mx)
@[expose] def fullPLastLearned (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPGlueUsed hdr mx + BitVec.ofNat 64 256
@[expose] def fullPArena (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPLastLearned hdr mx + BitVec.ofNat 64 64

private theorem bv64_mul_nat (x : BitVec 64) (k : Nat) :
    x * BitVec.ofNat 64 k = BitVec.ofNat 64 (x.toNat * k) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_mod]

private theorem bv64_shl3_nat {n : Nat} :
    BitVec.ofNat 64 n <<< (((3 : BitVec 32).signExtend 64).toNat % 64) =
      BitVec.ofNat 64 (8 * n) := by
  have hs : ((3 : BitVec 32).signExtend 64).toNat % 64 = 3 := rfl
  rw [hs]; apply BitVec.eq_of_toNat_eq; simp [Nat.mul_comm]

private theorem bv64_shl6_nat {n : Nat} :
    BitVec.ofNat 64 n <<< (((6 : BitVec 32).signExtend 64).toNat % 64) =
      BitVec.ofNat 64 (64 * n) := by
  have hs : ((6 : BitVec 32).signExtend 64).toNat % 64 = 6 := rfl
  rw [hs]; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

private theorem bv64_shl1_nat {n : Nat} (hn : 2 * n < 2 ^ 64) :
    (BitVec.ofNat 64 n <<< (((1 : BitVec 32).signExtend 64).toNat % 64)).toNat = 2 * n := by
  rw [bv_shl_sext1, bv64_ofNat_toNat hn]

theorem ptr_add_nat (p : BitVec 64) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## 2. Scoped `hdrTail4` Load/Store Automation (`InHdrTactics`) -/

namespace InHdrTactics

attribute [scoped bv_c0] List.length_set

private theorem load_hdr4_0 {hdr off : BitVec 64} (idx : Nat) {w0 w1 w2 w3 : List (BitVec 64)}
    {F : Mem 64 → Prop} {m : Mem 64} (hi : idx < w0.length)
    (hoff : hdr + off = hdr + 32 + BitVec.ofNat 64 (8 * idx))
    (hm : (hdrTail4 hdr w0 w1 w2 w3 ⋆ F) m) :
    loadVal m i64 (hdr + off) = some (w0[idx]?.getD 0#64) := by
  unfold hdrTail4 at hm
  have hm' : (array64 (hdr + 32) w0 ⋆
      (array64 (hdr + 312) w1 ⋆ array64 (hdr + 592) w2 ⋆ array64 (hdr + 872) w3 ⋆ F)) m :=
    sep_ac hm
  have hl := loadVal_array64 (i := idx) hi hm'
  rw [← hoff] at hl; rwa [List.getElem?_eq_getElem hi, Option.getD_some]

private theorem load_hdr4_1 {hdr off : BitVec 64} (idx : Nat) {w0 w1 w2 w3 : List (BitVec 64)}
    {F : Mem 64 → Prop} {m : Mem 64} (hi : idx < w1.length)
    (hoff : hdr + off = hdr + 312 + BitVec.ofNat 64 (8 * idx))
    (hm : (hdrTail4 hdr w0 w1 w2 w3 ⋆ F) m) :
    loadVal m i64 (hdr + off) = some (w1[idx]?.getD 0#64) := by
  unfold hdrTail4 at hm
  have hm' : (array64 (hdr + 312) w1 ⋆
      (array64 (hdr + 32) w0 ⋆ array64 (hdr + 592) w2 ⋆ array64 (hdr + 872) w3 ⋆ F)) m :=
    sep_ac hm
  have hl := loadVal_array64 (i := idx) hi hm'
  rw [← hoff] at hl; rwa [List.getElem?_eq_getElem hi, Option.getD_some]

private theorem load_hdr4_2 {hdr off : BitVec 64} (idx : Nat) {w0 w1 w2 w3 : List (BitVec 64)}
    {F : Mem 64 → Prop} {m : Mem 64} (hi : idx < w2.length)
    (hoff : hdr + off = hdr + 592 + BitVec.ofNat 64 (8 * idx))
    (hm : (hdrTail4 hdr w0 w1 w2 w3 ⋆ F) m) :
    loadVal m i64 (hdr + off) = some (w2[idx]?.getD 0#64) := by
  unfold hdrTail4 at hm
  have hm' : (array64 (hdr + 592) w2 ⋆
      (array64 (hdr + 32) w0 ⋆ array64 (hdr + 312) w1 ⋆ array64 (hdr + 872) w3 ⋆ F)) m :=
    sep_ac hm
  have hl := loadVal_array64 (i := idx) hi hm'
  rw [← hoff] at hl; rwa [List.getElem?_eq_getElem hi, Option.getD_some]

private theorem load_hdr4_3 {hdr off : BitVec 64} (idx : Nat) {w0 w1 w2 w3 : List (BitVec 64)}
    {F : Mem 64 → Prop} {m : Mem 64} (hi : idx < w3.length)
    (hoff : hdr + off = hdr + 872 + BitVec.ofNat 64 (8 * idx))
    (hm : (hdrTail4 hdr w0 w1 w2 w3 ⋆ F) m) :
    loadVal m i64 (hdr + off) = some (w3[idx]?.getD 0#64) := by
  unfold hdrTail4 at hm
  have hm' : (array64 (hdr + 872) w3 ⋆
      (array64 (hdr + 32) w0 ⋆ array64 (hdr + 312) w1 ⋆ array64 (hdr + 592) w2 ⋆ F)) m :=
    sep_ac hm
  have hl := loadVal_array64 (i := idx) hi hm'
  rw [← hoff] at hl; rwa [List.getElem?_eq_getElem hi, Option.getD_some]

private theorem store_hdr4_0 (off v hdr : BitVec 64) (idx : Nat) (w0 w1 w2 w3 : List (BitVec 64))
    {F : Mem 64 → Prop} {m : Mem 64} (hi : idx < w0.length)
    (hoff : hdr + off = hdr + 32 + BitVec.ofNat 64 (8 * idx))
    (hm : (hdrTail4 hdr w0 w1 w2 w3 ⋆ F) m) :
    storeOk m i64 (hdr + off) ∧
      (hdrTail4 hdr (w0.set idx v) w1 w2 w3 ⋆ F) (storeMem m i64 (hdr + off) v) := by
  unfold hdrTail4 at hm ⊢
  have hm' : (array64 (hdr + 32) w0 ⋆
      (array64 (hdr + 312) w1 ⋆ array64 (hdr + 592) w2 ⋆ array64 (hdr + 872) w3 ⋆ F)) m :=
    sep_ac hm
  obtain ⟨hok, hst⟩ := store_array64 (i := idx) v hi hm'
  rw [← hoff] at hok hst; exact ⟨hok, sep_ac hst⟩

private theorem store_hdr4_1 (off v hdr : BitVec 64) (idx : Nat) (w0 w1 w2 w3 : List (BitVec 64))
    {F : Mem 64 → Prop} {m : Mem 64} (hi : idx < w1.length)
    (hoff : hdr + off = hdr + 312 + BitVec.ofNat 64 (8 * idx))
    (hm : (hdrTail4 hdr w0 w1 w2 w3 ⋆ F) m) :
    storeOk m i64 (hdr + off) ∧
      (hdrTail4 hdr w0 (w1.set idx v) w2 w3 ⋆ F) (storeMem m i64 (hdr + off) v) := by
  unfold hdrTail4 at hm ⊢
  have hm' : (array64 (hdr + 312) w1 ⋆
      (array64 (hdr + 32) w0 ⋆ array64 (hdr + 592) w2 ⋆ array64 (hdr + 872) w3 ⋆ F)) m :=
    sep_ac hm
  obtain ⟨hok, hst⟩ := store_array64 (i := idx) v hi hm'
  rw [← hoff] at hok hst; exact ⟨hok, sep_ac hst⟩

private theorem store_hdr4_2 (off v hdr : BitVec 64) (idx : Nat) (w0 w1 w2 w3 : List (BitVec 64))
    {F : Mem 64 → Prop} {m : Mem 64} (hi : idx < w2.length)
    (hoff : hdr + off = hdr + 592 + BitVec.ofNat 64 (8 * idx))
    (hm : (hdrTail4 hdr w0 w1 w2 w3 ⋆ F) m) :
    storeOk m i64 (hdr + off) ∧
      (hdrTail4 hdr w0 w1 (w2.set idx v) w3 ⋆ F) (storeMem m i64 (hdr + off) v) := by
  unfold hdrTail4 at hm ⊢
  have hm' : (array64 (hdr + 592) w2 ⋆
      (array64 (hdr + 32) w0 ⋆ array64 (hdr + 312) w1 ⋆ array64 (hdr + 872) w3 ⋆ F)) m :=
    sep_ac hm
  obtain ⟨hok, hst⟩ := store_array64 (i := idx) v hi hm'
  rw [← hoff] at hok hst; exact ⟨hok, sep_ac hst⟩

private theorem store_hdr4_3 (off v hdr : BitVec 64) (idx : Nat) (w0 w1 w2 w3 : List (BitVec 64))
    {F : Mem 64 → Prop} {m : Mem 64} (hi : idx < w3.length)
    (hoff : hdr + off = hdr + 872 + BitVec.ofNat 64 (8 * idx))
    (hm : (hdrTail4 hdr w0 w1 w2 w3 ⋆ F) m) :
    storeOk m i64 (hdr + off) ∧
      (hdrTail4 hdr w0 w1 w2 (w3.set idx v) ⋆ F) (storeMem m i64 (hdr + off) v) := by
  unfold hdrTail4 at hm ⊢
  have hm' : (array64 (hdr + 872) w3 ⋆
      (array64 (hdr + 32) w0 ⋆ array64 (hdr + 312) w1 ⋆ array64 (hdr + 592) w2 ⋆ F)) m :=
    sep_ac hm
  obtain ⟨hok, hst⟩ := store_array64 (i := idx) v hi hm'
  rw [← hoff] at hok hst; exact ⟨hok, sep_ac hst⟩

private meta def elabCmdStr (tag src : String) : Lean.Elab.Command.CommandElabM Unit := do
  match Lean.Parser.runParserCategory (← Lean.getEnv) `command src tag with
  | .ok stx => Lean.Elab.Command.elabCommand stx
  | .error err => throwError "{tag}: {err}"

local elab "gen_hdr4_rules!" : command => do
  for chunk in [:4] do
    for idx in [:35] do
      let off := 32 + 280 * chunk + 8 * idx
      let ws := ["w0", "w1", "w2", "w3"]
      let wSel := ws[chunk]!
      let wUpds := (List.range 4).map fun c =>
        if c == chunk then s!"({ws[c]!}.set {idx} v)" else ws[c]!
      let wUpdStr := String.intercalate " " wUpds
      elabCmdStr s!"ld_{chunk}_{idx}" <|
        s!"@[scoped c0_load] theorem c0_load_hdr4_{chunk}_{idx} " ++
        "{hdr : BitVec 64} {w0 w1 w2 w3 : List (BitVec 64)} {F : Mem 64 → Prop} {m : Mem 64} " ++
        s!"(hi : {idx} < {wSel}.length) (hm : (hdrTail4 hdr w0 w1 w2 w3 ⋆ F) m) : " ++
        s!"loadVal m i64 (hdr + {off}) = some ({wSel}[{idx}]?.getD 0#64) := " ++
        s!"load_hdr4_{chunk} {idx} hi (by rw [BitVec.add_assoc]; rfl) hm"
      elabCmdStr s!"st_{chunk}_{idx}" <|
        s!"@[scoped c0_store] theorem c0_store_hdr4_{chunk}_{idx} " ++
        "(v hdr : BitVec 64) (w0 w1 w2 w3 : List (BitVec 64)) {F : Mem 64 → Prop} {m : Mem 64} " ++
        s!"(hi : {idx} < {wSel}.length) (hm : (hdrTail4 hdr w0 w1 w2 w3 ⋆ F) m) : " ++
        s!"storeOk m i64 (hdr + {off}) ∧ " ++
        s!"(hdrTail4 hdr {wUpdStr} ⋆ F) (storeMem m i64 (hdr + {off}) v) := " ++
        s!"store_hdr4_{chunk} {off} v hdr {idx} w0 w1 w2 w3 hi " ++
        "(by rw [BitVec.add_assoc]; rfl) hm"

gen_hdr4_rules!

end InHdrTactics

namespace InHdrCfgTactics

private theorem wrap_cfg_store {hdr off v : BitVec 64}
    {w0 w1 w2 w3 w0' w1' w2' w3' : List (BitVec 64)} {F : Mem 64 → Prop} {m : Mem 64}
    (hm : (hdrTail4Len hdr w0 w1 w2 w3 ⋆ F) m)
    (hstep : w0.length = 35 → w1.length = 35 → w2.length = 35 → w3.length = 35 →
      (hdrTail4 hdr w0 w1 w2 w3 ⋆ F) m →
      storeOk m i64 (hdr + off) ∧
        (w0'.length = 35 ∧ w1'.length = 35 ∧ w2'.length = 35 ∧ w3'.length = 35) ∧
        (hdrTail4 hdr w0' w1' w2' w3' ⋆ F) (storeMem m i64 (hdr + off) v)) :
    storeOk m i64 (hdr + off) ∧
      (hdrTail4Len hdr w0' w1' w2' w3' ⋆ F) (storeMem m i64 (hdr + off) v) := by
  obtain ⟨⟨h0, h1, h2, h3⟩, hm'⟩ := sep_pure_l.mp hm
  obtain ⟨hok, hlen, hst⟩ := hstep h0 h1 h2 h3 hm'
  exact ⟨hok, sep_pure_l.mpr ⟨hlen, hst⟩⟩

private meta def elabCfgCmdStr (tag src : String) : Lean.Elab.Command.CommandElabM Unit := do
  match Lean.Parser.runParserCategory (← Lean.getEnv) `command src tag with
  | .ok stx => Lean.Elab.Command.elabCommand stx
  | .error err => throwError "{tag}: {err}"

local elab "gen_hdr4_cfg_rules!" : command => do
  for chunk in [:4] do
    for idx in [:35] do
      let off := 32 + 280 * chunk + 8 * idx
      let ws := ["w0", "w1", "w2", "w3"]
      let wUpds := (List.range 4).map fun c =>
        if c == chunk then s!"(hdrSet {ws[c]!} {idx} v)" else ws[c]!
      let wUpdStr := String.intercalate " " wUpds
      let lenPfs := String.intercalate ", " <| (List.range 4).map fun c =>
        if c == chunk then s!"(hdrSet_len {ws[c]!} {idx} v).trans h{c}" else s!"h{c}"
      elabCfgCmdStr s!"stcfg_{chunk}_{idx}" <|
        s!"@[scoped c0_store] theorem c0_store_hdr4_cfg_{chunk}_{idx} " ++
        "(c : FullCfg) (v : BitVec 64) (w0 w1 w2 w3 : List (BitVec 64)) " ++
        "{F : Mem 64 → Prop} {m : Mem 64} " ++
        s!"(hm : (hdrTail4Len c.hdr w0 w1 w2 w3 ⋆ F) m) : " ++
        s!"storeOk m i64 (c.hdr + {off}) ∧ " ++
        s!"(hdrTail4Len c.hdr {wUpdStr} ⋆ F) (storeMem m i64 (c.hdr + {off}) v) := " ++
        "wrap_cfg_store hm fun h0 h1 h2 h3 hm' => " ++
        s!"let h := InHdrTactics.c0_store_hdr4_{chunk}_{idx} " ++
        "v c.hdr w0 w1 w2 w3 (by omega) hm'; " ++
        s!"⟨h.1, ⟨{lenPfs}⟩, by rw [hdrSet_eq]; exact h.2⟩"

gen_hdr4_cfg_rules!

end InHdrCfgTactics

local elab "in_steps" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := true, splitJnz := false } 10000

local elab "in_steps_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 10000

/-! ## 3. `full_fixed_bytes`, `full_calc_{ext,scr}_cap_m5`, and `full_calc_max_v` -/

theorem full_fixed_bytes_wp (Γ : Env) :
    ∀ a m Q X, fullFixedBytesSpec a m Q X → Func.wp Γ full_fixed_bytes_body a m Q X := by
  rintro ⟨max_v, ⟨⟩⟩ m Q X ⟨hmax, hQ⟩
  have hmx : max_v.toNat < 2 * dimacsBound := hmax
  unfold dimacsBound at hmx
  unfold Func.wp full_fixed_bytes_body
  in_steps_nogrp
  have hshl1 : max_v <<< (1 : Nat) = BitVec.ofNat 64 (2 * max_v.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm,
      Nat.mod_eq_of_lt (by omega : 2 * max_v.toNat < 2 ^ 64)]
  have hvb : max_v <<< (1 : Nat) + 7 &&& ~~~7 = BitVec.ofNat 64 (valsBytes max_v.toNat) := by
    rw [hshl1]; exact bv64_align8 (by omega)
  have hmb : max_v + 7 &&& ~~~7 = BitVec.ofNat 64 (markBytes max_v.toNat) := by
    simpa [markBytes, bv_ofNat_toNat_eq max_v] using bv64_align8 (n := max_v.toNat) (by omega)
  have hub_eq : (max_v + 1) <<< (2 : Nat) = BitVec.ofNat 64 (4 * (max_v.toNat + 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl,
      Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : max_v.toNat + 1 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : (max_v.toNat + 1) * 4 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 4 * (max_v.toNat + 1) < 2 ^ 64), Nat.mul_comm]
  have hub : (max_v + 1) <<< (2 : Nat) + 7 &&& ~~~7 =
      BitVec.ofNat 64 (u32FullBytes max_v.toNat) := by
    rw [hub_eq]; simpa [u32FullBytes] using bv64_align8 (n := 4 * (max_v.toNat + 1)) (by omega)
  have hshl3 : BitVec.ofNat 64 (2 * max_v.toNat) <<< (3 : Nat) =
      BitVec.ofNat 64 (16 * max_v.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega : 2 * max_v.toNat < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 16 * max_v.toNat < 2 ^ 64)]
    omega
  have hshl6 : max_v <<< (6 : Nat) = BitVec.ofNat 64 (64 * max_v.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega : 64 * max_v.toNat < 2 ^ 64), Nat.mul_comm]
  refine wp_join_group (ts := [i64])
    (fun (md, ()) m0 => m0 = m ∧ md = BitVec.ofNat 64 (fullMinDepthOf max_v.toNat)) ?_ ?_
  · rintro _ ⟨md, ⟨⟩⟩ m0 ⟨rfl, rfl⟩
    in_steps
    have hmd3 : BitVec.ofNat 64 (fullMinDepthOf max_v.toNat) <<< (3 : Nat) =
        BitVec.ofNat 64 (8 * fullMinDepthOf max_v.toNat) := by
      have hmdl := fullMinDepthOf_le max_v.toNat
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        Nat.mod_eq_of_lt (by omega : fullMinDepthOf max_v.toNat < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 8 * fullMinDepthOf max_v.toNat < 2 ^ 64)]
      omega
    have heq_ret : ((1152 : BitVec 64) + 320 +
        (max_v <<< (1 : Nat) + 7 &&& ~~~7) * 3 + (max_v + 7 &&& ~~~7) * 5 +
        ((max_v + 1) <<< (2 : Nat) + 7 &&& ~~~7) * 15 +
        max_v <<< (1 : Nat) <<< (3 : Nat) + max_v <<< (6 : Nat) +
        BitVec.ofNat 64 (fullMinDepthOf max_v.toNat) <<< (3 : Nat)) =
        BitVec.ofNat 64 (fullFixedBytes max_v.toNat) := by
      rw [hvb, hmb, hub, hshl1, hshl3, hshl6, hmd3]
      apply BitVec.eq_of_toNat_eq
      have hv_lt : valsBytes max_v.toNat < 2 ^ 64 := by unfold valsBytes; omega
      have hm_lt : markBytes max_v.toNat < 2 ^ 64 := by unfold markBytes; omega
      have hu_lt : u32FullBytes max_v.toNat < 2 ^ 64 := by unfold u32FullBytes; omega
      simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
        show (1152 : BitVec 64).toNat = 1152 from rfl,
        show (320 : BitVec 64).toNat = 320 from rfl,
        show (3 : BitVec 64).toNat = 3 from rfl, show (5 : BitVec 64).toNat = 5 from rfl,
        show (15 : BitVec 64).toNat = 15 from rfl,
        Nat.mod_eq_of_lt hv_lt, Nat.mod_eq_of_lt hm_lt, Nat.mod_eq_of_lt hu_lt]
      unfold fullFixedBytes; omega
    rw [heq_ret]; exact hQ
  · intro _ hJ; c0_hsplit
    · in_steps
      have h1 : max_v.toNat + 1 < 1000 := by
        simpa [Nat.mod_eq_of_lt (by omega : max_v.toNat + 1 < 2 ^ 64),
          show (1 : BitVec 64).toNat = 1 from rfl,
          show (1000 : BitVec 64).toNat = 1000 from rfl] using hc
      exact hJ _ _ ⟨rfl, by
        unfold fullMinDepthOf; simp only [h1, ↓reduceIte]
        have hm1 : max_v.toNat + 1 < 2 ^ 64 := by omega
        exact BitVec.eq_of_toNat_eq (by simp [Nat.mod_eq_of_lt hm1])⟩
    · in_steps
      have h1 : ¬ max_v.toNat + 1 < 1000 := by
        simpa [Nat.mod_eq_of_lt (by omega : max_v.toNat + 1 < 2 ^ 64),
          show (1 : BitVec 64).toNat = 1 from rfl,
          show (1000 : BitVec 64).toNat = 1000 from rfl] using hc
      exact hJ _ _ ⟨rfl, by unfold fullMinDepthOf; simp only [h1, ↓reduceIte]; rfl⟩

theorem full_calc_ext_cap_m5_wp (Γ : Env) :
    ∀ a m Q X, Spec.fullCalcExtCapM5Spec a m Q X →
      Func.wp Γ full_calc_ext_cap_m5_body a m Q X := by
  rintro ⟨rem, ⟨⟩⟩ m Q X hQ
  unfold Func.wp full_calc_ext_cap_m5_body
  in_steps_nogrp
  c0_hsplit
  · in_steps
    have hlt : rem.toNat < 8192 := by simpa [show (8192 : BitVec 64).toNat = 8192 from rfl] using hc
    exact hQ 0#64 (by decide) (fun _ => rfl) (by simp)
  · in_steps_nogrp
    have hge : 8192 ≤ rem.toNat := by
      have h1 : ¬ rem.toNat < 8192 := by
        simpa [show (8192 : BitVec 64).toNat = 8192 from rfl] using hc
      omega
    refine wp_join_group (ts := [i64])
      (fun (cand, ()) m0 => m0 = m ∧ cand.toNat ≤ 4194304 ∧ 4 * cand.toNat ≤ rem.toNat / 8) ?_ ?_
    · rintro _ ⟨cand, ⟨⟩⟩ m0 ⟨rfl, hle, h4⟩
      in_steps
      have hsub_le : (cand &&& ~~~1).toNat ≤ cand.toNat := by
        simp only [BitVec.toNat_and, BitVec.toNat_not, show (1 : BitVec 64).toNat = 1 from rfl]
        exact Nat.and_le_left
      exact hQ (cand &&& ~~~1) (by omega) (fun h => absurd h (by omega)) (by omega)
    · intro _ hJ
      have hs5 : (rem >>> (5 : Nat)).toNat = rem.toNat / 32 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      c0_hsplit
      · in_steps
        have hgt : 4194304 < rem.toNat / 32 := by
          rw [← hs5]; simpa [show (4194304 : BitVec 64).toNat = 4194304 from rfl] using hc
        have h4 : 4 * 4194304 ≤ rem.toNat / 8 := by omega
        exact hJ _ _ ⟨rfl, by decide, h4⟩
      · in_steps
        have hle : (rem >>> (5 : Nat)).toNat ≤ 4194304 := by
          have h1 : ¬ 4194304 < (rem >>> (5 : Nat)).toNat := by
            simpa [show (4194304 : BitVec 64).toNat = 4194304 from rfl] using hc
          omega
        exact hJ _ _ ⟨rfl, hle, by rw [hs5] at hle ⊢; omega⟩

theorem full_calc_scr_cap_m5_wp (Γ : Env) :
    ∀ a m Q X, Spec.fullCalcScrCapM5Spec a m Q X →
      Func.wp Γ full_calc_scr_cap_m5_body a m Q X := by
  rintro ⟨rem, ⟨⟩⟩ m Q X hQ
  unfold Func.wp full_calc_scr_cap_m5_body
  in_steps_nogrp
  c0_hsplit
  · in_steps
    have hlt : rem.toNat < 8192 := by simpa [show (8192 : BitVec 64).toNat = 8192 from rfl] using hc
    exact hQ 0#64 (by decide) (fun _ => rfl) (by simp)
  · in_steps_nogrp
    have hge : 8192 ≤ rem.toNat := by
      have h1 : ¬ rem.toNat < 8192 := by
        simpa [show (8192 : BitVec 64).toNat = 8192 from rfl] using hc
      omega
    refine wp_join_group (ts := [i64])
      (fun (cand, ()) m0 => m0 = m ∧ 4 * cand.toNat ≤ rem.toNat / 4) ?_ ?_
    · rintro _ ⟨cand, ⟨⟩⟩ m0 ⟨rfl, h4⟩
      in_steps_nogrp
      refine wp_join_group (ts := [i64])
        (fun (cand', ()) m1 => m1 = m0 ∧ cand'.toNat ≤ 8388608 ∧ 4 * cand'.toNat ≤ rem.toNat / 4)
        ?_ ?_
      · rintro _ ⟨cand', ⟨⟩⟩ m1 ⟨rfl, hle, h4'⟩
        in_steps
        have hsub_le : (cand' &&& ~~~1).toNat ≤ cand'.toNat := by
          simp only [BitVec.toNat_and, BitVec.toNat_not, show (1 : BitVec 64).toNat = 1 from rfl]
          exact Nat.and_le_left
        exact hQ (cand' &&& ~~~1) (by omega) (fun h => absurd h (by omega)) (by omega)
      · intro _ hJc
        c0_hsplit
        · in_steps
          have hgt : 8388608 < cand.toNat := by
            simpa [show (8388608 : BitVec 64).toNat = 8388608 from rfl] using hc
          exact hJc _ _ ⟨rfl, by decide, by omega⟩
        · in_steps
          have hle : cand.toNat ≤ 8388608 := by
            have h1 : ¬ 8388608 < cand.toNat := by
              simpa [show (8388608 : BitVec 64).toNat = 8388608 from rfl] using hc
            omega
          exact hJc _ _ ⟨rfl, hle, h4⟩
    · intro _ hJb
      have hs4 : (rem >>> (4 : Nat)).toNat = rem.toNat / 16 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      have hs5 : (rem >>> (5 : Nat)).toNat = rem.toNat / 32 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      c0_hsplit
      · in_steps
        have _ := hc; exact hJb _ _ ⟨rfl, by rw [hs4]; omega⟩
      · in_steps
        have _ := hc; exact hJb _ _ ⟨rfl, by rw [hs5]; omega⟩

theorem full_calc_max_v_wp (Γ : Env) (hFixed : Γ.Has "full_fixed_bytes" fullFixedBytesSpec) :
    ∀ a m Q X, fullCalcMaxVSpec a m Q X → Func.wp Γ full_calc_max_v_body a m Q X := by
  rintro ⟨avail, mv, nc, f0, ⟨⟩⟩ m Q X ⟨hmv, hnc, hf0, hfit, hQ⟩
  have hmv' := hmv; have hnc' := hnc; unfold dimacsBound at hmv' hnc'
  unfold Func.wp full_calc_max_v_body
  in_steps_nogrp
  refine wp_join_group (ts := [i64])
    (fun (bva_cap, ()) m0 => m0 = m ∧ bva_cap.toNat ≤ 32768) ?_ ?_
  · rintro _ ⟨bva_cap, ⟨⟩⟩ m0 ⟨rfl, hbva⟩
    in_steps_nogrp
    have hmv_sum : mv.toNat + bva_cap.toNat < 2 * dimacsBound := by
      unfold dimacsBound; omega
    have hmaxv_eq : (mv + bva_cap).toNat = mv.toNat + bva_cap.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by unfold dimacsBound at hmv_sum; omega)]
    refine LeanQbe.T.wp_call_of_spec _ _ (hFixed _ _ _ _ ?_)
    dsimp only [vals, Arg.val, fullFixedBytesSpec]
    rw [hmaxv_eq]
    refine ⟨hmv_sum, ?_⟩
    have hfx_lt := fullFixedBytes_lt hmv_sum
    in_steps_nogrp
    c0_hsplit
    · in_steps
      exact hQ mv (Nat.le_refl _) (by unfold dimacsBound; omega)
        (by rw [← hf0]; exact hfit)
    · have hfx_mod : fullFixedBytes (mv.toNat + bva_cap.toNat) % 2 ^ 64 =
          fullFixedBytes (mv.toNat + bva_cap.toNat) := Nat.mod_eq_of_lt (by omega)
      have hle_fx : fullFixedBytes (mv.toNat + bva_cap.toNat) ≤ avail.toNat := by
        rw [hfx_mod] at hc; omega
      in_steps_nogrp
      c0_hsplit
      · in_steps
        exact hQ mv (Nat.le_refl _) (by unfold dimacsBound; omega)
          (by rw [← hf0]; exact hfit)
      · in_steps
        have h40 : BitVec.toNat (40 : BitVec 64) = 40 := rfl
        have h136 : BitVec.toNat (136 : BitVec 64) = 136 := rfl
        have h136_mod : (nc.toNat * 40 + 136) % 2 ^ 64 = nc.toNat * 40 + 136 :=
          Nat.mod_eq_of_lt (by omega)
        rw [hfx_mod, h40, h136, h136_mod] at hc
        have hfits :
            fullFixedBytes (mv + bva_cap).toNat + nc.toNat * 40 + 136 ≤ avail.toNat := by
          rw [hmaxv_eq]; omega
        exact hQ (mv + bva_cap) (by rw [hmaxv_eq]; omega) (by rw [hmaxv_eq]; exact hmv_sum) hfits
  · intro _ hJ
    c0_hsplit
    · in_steps_nogrp
      c0_hsplit
      · in_steps_nogrp
        refine wp_join_group (ts := [i64])
          (fun (bc, ()) m1 => m1 = m ∧ bc.toNat ≤ 32768) ?_ ?_
        · rintro _ ⟨bc, ⟨⟩⟩ m1 ⟨rfl, hbc⟩; in_steps; exact hJ _ _ ⟨rfl, hbc⟩
        · intro _ hJb; c0_hsplit
          · in_steps; exact hJb _ _ ⟨rfl, by decide⟩
          · in_steps
            have hle : (((avail - f0) - nc * 48 - 4096) / 2688).toNat ≤ 32768 := by
              have h1 : ¬ (32768 : BitVec 64).toNat <
                  (((avail - f0) - nc * 48 - 4096) / 2688).toNat := hc
              rw [show (32768 : BitVec 64).toNat = 32768 from rfl] at h1; omega
            exact hJb _ _ ⟨rfl, hle⟩
      · in_steps; exact hJ _ _ ⟨rfl, by simp⟩
    · in_steps; exact hJ _ _ ⟨rfl, by simp⟩

/-! ## 4. `full_init_ptrs` and `full_init_hdr` -/

private def ptrsW0 (hdr : BitVec 64) (mx : Nat) (w0 : List (BitVec 64)) : List (BitVec 64) :=
  ((((((((((((((w0.set 4 (fullPVals hdr mx)).set 5 (fullPMark hdr mx)).set
    24 (fullPPhases hdr mx)).set 6 (fullPLevel hdr mx)).set 7 (fullPReason hdr mx)).set
    8 (fullPTrail hdr mx)).set 13 (fullPTmp hdr mx)).set 21 (fullPHeap hdr mx)).set
    22 (fullPPos hdr mx)).set 26 (fullPMinClr hdr mx)).set 9 (fullPWvec hdr mx)).set
    23 (fullPScore hdr mx)).set 25 (fullPMinStk hdr mx)).set 10 (fullPArena hdr mx)).set
    29 (BitVec.ofNat 64 (fullMinDepthOf mx))

private def ptrsW1 (hdr : BitVec 64) (mx : Nat) (w1 : List (BitVec 64)) : List (BitVec 64) :=
  ((((((((w1.set 10 (fullPPhasesTarget hdr mx)).set 11 (fullPPhasesBest hdr mx)).set
    6 (fullPTrailPos hdr mx)).set 13 (fullPShrinkStk hdr mx)).set 7 (fullPQPrev hdr mx)).set
    8 (fullPQNext hdr mx)).set 9 (fullPQStamp hdr mx)).set 12 (fullPWsort hdr mx)).set
    15 (fullPGlueUsed hdr mx)

private def ptrsW2 (hdr : BitVec 64) (mx : Nat) (w2 : List (BitVec 64)) : List (BitVec 64) :=
  ((((((((w2.set 27 (fullPLitMark hdr mx)).set 26 (fullPFlags hdr mx)).set
    30 (fullPFrameTrail hdr mx)).set 31 (fullPFrameDec hdr mx)).set 28 (fullPRepr hdr mx)).set
    32 (fullPWorkStk1 hdr mx)).set 33 (fullPWorkStk2 hdr mx)).set 34 (fullPTarjanMark hdr mx)).set
    29 (fullPSimSig hdr mx)

private def ptrsW3 (hdr : BitVec 64) (mx : Nat) (w3 : List (BitVec 64)) : List (BitVec 64) :=
  (((w3.set 1 (fullPWalkVals hdr mx)).set 2 (fullPWalkBest hdr mx)).set
    0 (fullPTarjanReach hdr mx)).set 8 (fullPLastLearned hdr mx)

private theorem fp_vals (c : FullCfg) : c.pVals = fullPVals c.hdr c.max_vars := rfl
private theorem fp_walkVals (c : FullCfg) : c.pWalkVals = fullPWalkVals c.hdr c.max_vars := by
  unfold FullCfg.pWalkVals fullPWalkVals; rw [fp_vals]
private theorem fp_litMark (c : FullCfg) : c.pLitMark = fullPLitMark c.hdr c.max_vars := by
  unfold FullCfg.pLitMark fullPLitMark; rw [fp_walkVals]
private theorem fp_mark (c : FullCfg) : c.pMark = fullPMark c.hdr c.max_vars := by
  unfold FullCfg.pMark fullPMark; rw [fp_litMark]
private theorem fp_phases (c : FullCfg) : c.pPhases = fullPPhases c.hdr c.max_vars := by
  unfold FullCfg.pPhases fullPPhases; rw [fp_mark]
private theorem fp_phasesTgt (c : FullCfg) :
    c.pPhasesTarget = fullPPhasesTarget c.hdr c.max_vars := by
  unfold FullCfg.pPhasesTarget fullPPhasesTarget; rw [fp_phases]
private theorem fp_phasesBest (c : FullCfg) :
    c.pPhasesBest = fullPPhasesBest c.hdr c.max_vars := by
  unfold FullCfg.pPhasesBest fullPPhasesBest; rw [fp_phasesTgt]
private theorem fp_walkBest (c : FullCfg) : c.pWalkBest = fullPWalkBest c.hdr c.max_vars := by
  unfold FullCfg.pWalkBest fullPWalkBest; rw [fp_phasesBest]
private theorem fp_flags (c : FullCfg) : c.pFlags = fullPFlags c.hdr c.max_vars := by
  unfold FullCfg.pFlags fullPFlags; rw [fp_walkBest]
private theorem fp_level (c : FullCfg) : c.pLevel = fullPLevel c.hdr c.max_vars := by
  unfold FullCfg.pLevel fullPLevel; rw [fp_flags]
private theorem fp_reason (c : FullCfg) : c.pReason = fullPReason c.hdr c.max_vars := by
  unfold FullCfg.pReason fullPReason; rw [fp_level]
private theorem fp_trail (c : FullCfg) : c.pTrail = fullPTrail c.hdr c.max_vars := by
  unfold FullCfg.pTrail fullPTrail; rw [fp_reason]
private theorem fp_trailPos (c : FullCfg) : c.pTrailPos = fullPTrailPos c.hdr c.max_vars := by
  unfold FullCfg.pTrailPos fullPTrailPos; rw [fp_trail]
private theorem fp_tmp (c : FullCfg) : c.pTmp = fullPTmp c.hdr c.max_vars := by
  unfold FullCfg.pTmp fullPTmp; rw [fp_trailPos]
private theorem fp_heap (c : FullCfg) : c.pHeap = fullPHeap c.hdr c.max_vars := by
  unfold FullCfg.pHeap fullPHeap; rw [fp_tmp]
private theorem fp_pos (c : FullCfg) : c.pPos = fullPPos c.hdr c.max_vars := by
  unfold FullCfg.pPos fullPPos; rw [fp_heap]
private theorem fp_minClr (c : FullCfg) : c.pMinClr = fullPMinClr c.hdr c.max_vars := by
  unfold FullCfg.pMinClr fullPMinClr; rw [fp_pos]
private theorem fp_shrinkStk (c : FullCfg) : c.pShrinkStk = fullPShrinkStk c.hdr c.max_vars := by
  unfold FullCfg.pShrinkStk fullPShrinkStk; rw [fp_minClr]
private theorem fp_qPrev (c : FullCfg) : c.pQPrev = fullPQPrev c.hdr c.max_vars := by
  unfold FullCfg.pQPrev fullPQPrev; rw [fp_shrinkStk]
private theorem fp_qNext (c : FullCfg) : c.pQNext = fullPQNext c.hdr c.max_vars := by
  unfold FullCfg.pQNext fullPQNext; rw [fp_qPrev]
private theorem fp_qStamp (c : FullCfg) : c.pQStamp = fullPQStamp c.hdr c.max_vars := by
  unfold FullCfg.pQStamp fullPQStamp; rw [fp_qNext]
private theorem fp_frameTrail (c : FullCfg) :
    c.pFrameTrail = fullPFrameTrail c.hdr c.max_vars := by
  unfold FullCfg.pFrameTrail fullPFrameTrail; rw [fp_qStamp]
private theorem fp_frameDec (c : FullCfg) : c.pFrameDec = fullPFrameDec c.hdr c.max_vars := by
  unfold FullCfg.pFrameDec fullPFrameDec; rw [fp_frameTrail]
private theorem fp_wvec (c : FullCfg) : c.pWvec = fullPWvec c.hdr c.max_vars := by
  unfold FullCfg.pWvec fullPWvec; rw [fp_frameDec]
private theorem fp_repr (c : FullCfg) : c.pRepr = fullPRepr c.hdr c.max_vars := by
  unfold FullCfg.pRepr fullPRepr; rw [fp_wvec]
private theorem fp_wsort (c : FullCfg) : c.pWsort = fullPWsort c.hdr c.max_vars := by
  unfold FullCfg.pWsort fullPWsort; rw [fp_repr]
private theorem fp_workStk1 (c : FullCfg) : c.pWorkStk1 = fullPWorkStk1 c.hdr c.max_vars := by
  unfold FullCfg.pWorkStk1 fullPWorkStk1; rw [fp_wsort]
private theorem fp_workStk2 (c : FullCfg) : c.pWorkStk2 = fullPWorkStk2 c.hdr c.max_vars := by
  unfold FullCfg.pWorkStk2 fullPWorkStk2; rw [fp_workStk1]
private theorem fp_tarjanMark (c : FullCfg) :
    c.pTarjanMark = fullPTarjanMark c.hdr c.max_vars := by
  unfold FullCfg.pTarjanMark fullPTarjanMark; rw [fp_workStk2]
private theorem fp_tarjanReach (c : FullCfg) :
    c.pTarjanReach = fullPTarjanReach c.hdr c.max_vars := by
  unfold FullCfg.pTarjanReach fullPTarjanReach; rw [fp_tarjanMark]
private theorem fp_score (c : FullCfg) : c.pScore = fullPScore c.hdr c.max_vars := by
  unfold FullCfg.pScore fullPScore; rw [fp_tarjanReach]
private theorem fp_simSig (c : FullCfg) : c.pSimSig = fullPSimSig c.hdr c.max_vars := by
  unfold FullCfg.pSimSig fullPSimSig; rw [fp_score]
private theorem fp_minStk (c : FullCfg) : c.pMinStk = fullPMinStk c.hdr c.max_vars := by
  unfold FullCfg.pMinStk fullPMinStk; rw [fp_simSig]
private theorem fp_glueUsed (c : FullCfg) : c.pGlueUsed = fullPGlueUsed c.hdr c.max_vars := by
  unfold FullCfg.pGlueUsed fullPGlueUsed; rw [fp_minStk, FullCfg.minDepth]
private theorem fp_lastLearned (c : FullCfg) :
    c.pLastLearned = fullPLastLearned c.hdr c.max_vars := by
  unfold FullCfg.pLastLearned fullPLastLearned; rw [fp_glueUsed]
private theorem fp_arena (c : FullCfg) : c.pArena = fullPArena c.hdr c.max_vars := by
  unfold FullCfg.pArena fullPArena; rw [fp_lastLearned]

private theorem len_cons10 {α : Type} (xs : List α) (n : Nat) (h : xs.length = n + 10) :
    ∃ a b c d e f g h1 i j ys, ys.length = n ∧
      xs = a :: b :: c :: d :: e :: f :: g :: h1 :: i :: j :: ys := by
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨h1, _ | ⟨i, _ |
    ⟨j, ys⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at h
  exact ⟨a, b, c, d, e, f, g, h1, i, j, ys, h, rfl⟩

private theorem decompose35 {α : Type} (xs : List α) (h : xs.length = 35) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
      c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 d0 d1 d2 d3 d4,
      xs = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
        c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4] := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, xs1, h1, rfl⟩ := len_cons10 xs 25 h
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, xs2, h2, rfl⟩ := len_cons10 xs1 15 h1
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, xs3, h3, rfl⟩ := len_cons10 xs2 5 h2
  rcases xs3 with _ | ⟨d0, _ | ⟨d1, _ | ⟨d2, _ | ⟨d3, _ | ⟨d4, _ | _⟩⟩⟩⟩⟩ <;> simp at h3
  exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩

private theorem ptrsW0_ok (hdr : BitVec 64) (mx : Nat) (w0 : List (BitVec 64))
    (h0 : w0.length = 35) :
    ((ptrsW0 hdr mx w0)[4]? = some (fullPVals hdr mx) ∧
      (ptrsW0 hdr mx w0)[5]? = some (fullPMark hdr mx) ∧
      (ptrsW0 hdr mx w0)[6]? = some (fullPLevel hdr mx) ∧
      (ptrsW0 hdr mx w0)[7]? = some (fullPReason hdr mx) ∧
      (ptrsW0 hdr mx w0)[8]? = some (fullPTrail hdr mx) ∧
      (ptrsW0 hdr mx w0)[9]? = some (fullPWvec hdr mx) ∧
      (ptrsW0 hdr mx w0)[10]? = some (fullPArena hdr mx) ∧
      (ptrsW0 hdr mx w0)[13]? = some (fullPTmp hdr mx) ∧
      (ptrsW0 hdr mx w0)[21]? = some (fullPHeap hdr mx) ∧
      (ptrsW0 hdr mx w0)[22]? = some (fullPPos hdr mx) ∧
      (ptrsW0 hdr mx w0)[23]? = some (fullPScore hdr mx) ∧
      (ptrsW0 hdr mx w0)[24]? = some (fullPPhases hdr mx) ∧
      (ptrsW0 hdr mx w0)[25]? = some (fullPMinStk hdr mx) ∧
      (ptrsW0 hdr mx w0)[26]? = some (fullPMinClr hdr mx) ∧
      (ptrsW0 hdr mx w0)[29]? = some (BitVec.ofNat 64 (fullMinDepthOf mx))) ∧
      (∀ i ∈ [0, 1, 11, 12], (ptrsW0 hdr mx w0)[i]? = w0[i]?) := by
  refine ⟨?_, fun i hi => ?_⟩
  · repeat' apply And.intro
    all_goals
      dsimp only [ptrsW0]
      repeat' (first
        | rw [List.getElem?_set_self (by (repeat rw [List.length_set]); rw [h0]; decide)]
        | rw [List.getElem?_set_ne (by decide)])
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> (
      dsimp only [ptrsW0]
      repeat' rw [List.getElem?_set_ne (by decide)])

private theorem ptrsW1_ok (hdr : BitVec 64) (mx : Nat) (w1 : List (BitVec 64))
    (h1 : w1.length = 35) :
    ((ptrsW1 hdr mx w1)[6]? = some (fullPTrailPos hdr mx) ∧
      (ptrsW1 hdr mx w1)[7]? = some (fullPQPrev hdr mx) ∧
      (ptrsW1 hdr mx w1)[8]? = some (fullPQNext hdr mx) ∧
      (ptrsW1 hdr mx w1)[9]? = some (fullPQStamp hdr mx) ∧
      (ptrsW1 hdr mx w1)[10]? = some (fullPPhasesTarget hdr mx) ∧
      (ptrsW1 hdr mx w1)[11]? = some (fullPPhasesBest hdr mx) ∧
      (ptrsW1 hdr mx w1)[12]? = some (fullPWsort hdr mx) ∧
      (ptrsW1 hdr mx w1)[13]? = some (fullPShrinkStk hdr mx) ∧
      (ptrsW1 hdr mx w1)[15]? = some (fullPGlueUsed hdr mx)) ∧
      (∀ i ∈ [14, 16, 17], (ptrsW1 hdr mx w1)[i]? = w1[i]?) := by
  refine ⟨?_, fun i hi => ?_⟩
  · repeat' apply And.intro
    all_goals
      dsimp only [ptrsW1]
      repeat' (first
        | rw [List.getElem?_set_self (by (repeat rw [List.length_set]); rw [h1]; decide)]
        | rw [List.getElem?_set_ne (by decide)])
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> (
      dsimp only [ptrsW1]
      repeat' rw [List.getElem?_set_ne (by decide)])

private theorem ptrsW2_ok (hdr : BitVec 64) (mx : Nat) (w2 : List (BitVec 64))
    (h2 : w2.length = 35) :
    (ptrsW2 hdr mx w2)[26]? = some (fullPFlags hdr mx) ∧
      (ptrsW2 hdr mx w2)[27]? = some (fullPLitMark hdr mx) ∧
      (ptrsW2 hdr mx w2)[28]? = some (fullPRepr hdr mx) ∧
      (ptrsW2 hdr mx w2)[29]? = some (fullPSimSig hdr mx) ∧
      (ptrsW2 hdr mx w2)[30]? = some (fullPFrameTrail hdr mx) ∧
      (ptrsW2 hdr mx w2)[31]? = some (fullPFrameDec hdr mx) ∧
      (ptrsW2 hdr mx w2)[32]? = some (fullPWorkStk1 hdr mx) ∧
      (ptrsW2 hdr mx w2)[33]? = some (fullPWorkStk2 hdr mx) ∧
      (ptrsW2 hdr mx w2)[34]? = some (fullPTarjanMark hdr mx) := by
  repeat' apply And.intro
  all_goals
    dsimp only [ptrsW2]
    repeat' (first
      | rw [List.getElem?_set_self (by (repeat rw [List.length_set]); rw [h2]; decide)]
      | rw [List.getElem?_set_ne (by decide)])

private theorem ptrsW3_ok (hdr : BitVec 64) (mx : Nat) (w3 : List (BitVec 64))
    (h3 : w3.length = 35) :
    ((ptrsW3 hdr mx w3)[0]? = some (fullPTarjanReach hdr mx) ∧
      (ptrsW3 hdr mx w3)[1]? = some (fullPWalkVals hdr mx) ∧
      (ptrsW3 hdr mx w3)[2]? = some (fullPWalkBest hdr mx) ∧
      (ptrsW3 hdr mx w3)[8]? = some (fullPLastLearned hdr mx)) ∧
      (∀ i ∈ [3, 4, 6, 7], (ptrsW3 hdr mx w3)[i]? = w3[i]?) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := decompose35 w3 h3
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, fun i hi => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> rfl

section InitPtrs
open scoped InHdrTactics

theorem full_init_ptrs_wp (Γ : Env) :
    ∀ a m Q X, fullInitPtrsSpec a m Q X → Func.wp Γ full_init_ptrs_body a m Q X := by
  rintro ⟨h, hdr_addr, max_v, ⟨⟩⟩ m Q X ⟨ws, R, rfl, hws, hmax, _hfit, hm, hQ⟩
  have hmx : max_v.toNat < 2 * dimacsBound := hmax
  unfold dimacsBound at hmx
  have hshl1 : max_v <<< (1 : Nat) = BitVec.ofNat 64 (2 * max_v.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm,
      Nat.mod_eq_of_lt (by omega : 2 * max_v.toNat < 2 ^ 64)]
  have hvb : max_v <<< (1 : Nat) + 7 &&& ~~~7 = BitVec.ofNat 64 (valsBytes max_v.toNat) := by
    rw [hshl1]; exact bv64_align8 (by omega)
  have hmb : max_v + 7 &&& ~~~7 = BitVec.ofNat 64 (markBytes max_v.toNat) := by
    simpa [markBytes, bv_ofNat_toNat_eq max_v] using bv64_align8 (n := max_v.toNat) (by omega)
  have hub_eq : (max_v + 1) <<< (2 : Nat) = BitVec.ofNat 64 (4 * (max_v.toNat + 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl,
      Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : max_v.toNat + 1 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : (max_v.toNat + 1) * 4 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 4 * (max_v.toNat + 1) < 2 ^ 64), Nat.mul_comm]
  have hub : (max_v + 1) <<< (2 : Nat) + 7 &&& ~~~7 =
      BitVec.ofNat 64 (u32FullBytes max_v.toNat) := by
    rw [hub_eq]; simpa [u32FullBytes] using bv64_align8 (n := 4 * (max_v.toNat + 1)) (by omega)
  have hu64b : max_v <<< (3 : Nat) = BitVec.ofNat 64 (8 * max_v.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega : max_v.toNat * 2 ^ 3 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 8 * max_v.toNat < 2 ^ 64)]
    omega
  have hnl3 : max_v <<< (1 : Nat) <<< (3 : Nat) = BitVec.ofNat 64 (16 * max_v.toNat) := by
    rw [hshl1]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega : 2 * max_v.toNat < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 16 * max_v.toNat < 2 ^ 64)]
    omega
  let w0 := ws.take 35; let w1 := (ws.drop 35).take 35
  let w2 := (ws.drop 70).take 35; let w3 := (ws.drop 105).take 35
  have h0l : w0.length = 35 := by simp [w0, hws]
  have h1l : w1.length = 35 := by simp [w1, hws]
  have h2l : w2.length = 35 := by simp [w2, hws]
  have h3l : w3.length = 35 := by simp [w3, hws]
  have hm4 := array64_to_hdrTail4 hws hm
  change (hdrTail4 h w0 w1 w2 w3 ⋆ R) m at hm4
  clear hm
  unfold Func.wp full_init_ptrs_body
  in_steps_nogrp
  refine wp_join_group (ts := [i64])
    (fun (md, ()) m0 => m0 = m ∧ md = BitVec.ofNat 64 (fullMinDepthOf max_v.toNat)) ?_ ?_
  · rintro _ ⟨md, ⟨⟩⟩ m0 ⟨rfl, rfl⟩
    in_steps
    rw [hvb, hmb, hub, hu64b, hnl3] at hm
    have hmd3 : BitVec.ofNat 64 (fullMinDepthOf max_v.toNat) <<< (3 : Nat) =
        BitVec.ofNat 64 (8 * fullMinDepthOf max_v.toNat) := by
      have hmdl := fullMinDepthOf_le max_v.toNat
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        Nat.mod_eq_of_lt (by omega : fullMinDepthOf max_v.toNat < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 8 * fullMinDepthOf max_v.toNat < 2 ^ 64)]
      omega
    rw [hmd3] at hm
    change (hdrTail4 h (ptrsW0 h max_v.toNat w0) (ptrsW1 h max_v.toNat w1)
      (ptrsW2 h max_v.toNat w2) (ptrsW3 h max_v.toNat w3) ⋆ R) m at hm
    have h0' : (ptrsW0 h max_v.toNat w0).length = 35 := by simp [ptrsW0, h0l]
    have h1' : (ptrsW1 h max_v.toNat w1).length = 35 := by simp [ptrsW1, h1l]
    have h2' : (ptrsW2 h max_v.toNat w2).length = 35 := by simp [ptrsW2, h2l]
    have h3' : (ptrsW3 h max_v.toNat w3).length = 35 := by simp [ptrsW3, h3l]
    rw [hdrTail4_eq_array64 h0' h1' h2'] at hm
    let ws' := ptrsW0 h max_v.toNat w0 ++ ptrsW1 h max_v.toNat w1 ++
      ptrsW2 h max_v.toNat w2 ++ ptrsW3 h max_v.toNat w3
    obtain ⟨⟨p0_4, p0_5, p0_6, p0_7, p0_8, p0_9, p0_10, p0_13, p0_21, p0_22, p0_23, p0_24, p0_25,
      p0_26, p0_29⟩, u0⟩ := ptrsW0_ok h max_v.toNat w0 h0l
    obtain ⟨⟨p1_6, p1_7, p1_8, p1_9, p1_10, p1_11, p1_12, p1_13, p1_15⟩, u1⟩ :=
      ptrsW1_ok h max_v.toNat w1 h1l
    obtain ⟨p2_26, p2_27, p2_28, p2_29, p2_30, p2_31, p2_32, p2_33, p2_34⟩ :=
      ptrsW2_ok h max_v.toNat w2 h2l
    obtain ⟨⟨p3_0, p3_1, p3_2, p3_8⟩, u3⟩ := ptrsW3_ok h max_v.toNat w3 h3l
    refine hQ ws' m (by simp [ws', h0', h1', h2', h3']) (fun c hc1 hc2 => ?_)
      (fun i hi => ?_) hm
    · rw [fp_vals, fp_mark, fp_level, fp_reason, fp_trail, fp_wvec, fp_arena, fp_tmp,
        fp_heap, fp_pos, fp_score, fp_phases, fp_minStk, fp_minClr, FullCfg.minDepth,
        fp_trailPos, fp_qPrev, fp_qNext, fp_qStamp, fp_phasesTgt, fp_phasesBest, fp_wsort,
        fp_shrinkStk, fp_glueUsed, fp_flags, fp_litMark, fp_repr, fp_simSig, fp_frameTrail,
        fp_frameDec, fp_workStk1, fp_workStk2, fp_tarjanMark, fp_tarjanReach, fp_walkVals,
        fp_walkBest, fp_lastLearned, hc1, hc2]
      dsimp only [ws']
      refine ⟨append4_getElem?_0 h0' (by decide) |>.trans p0_4,
        append4_getElem?_0 h0' (by decide) |>.trans p0_5,
        append4_getElem?_0 h0' (by decide) |>.trans p0_6,
        append4_getElem?_0 h0' (by decide) |>.trans p0_7,
        append4_getElem?_0 h0' (by decide) |>.trans p0_8,
        append4_getElem?_0 h0' (by decide) |>.trans p0_9,
        append4_getElem?_0 h0' (by decide) |>.trans p0_10,
        append4_getElem?_0 h0' (by decide) |>.trans p0_13,
        append4_getElem?_0 h0' (by decide) |>.trans p0_21,
        append4_getElem?_0 h0' (by decide) |>.trans p0_22,
        append4_getElem?_0 h0' (by decide) |>.trans p0_23,
        append4_getElem?_0 h0' (by decide) |>.trans p0_24,
        append4_getElem?_0 h0' (by decide) |>.trans p0_25,
        append4_getElem?_0 h0' (by decide) |>.trans p0_26,
        append4_getElem?_0 h0' (by decide) |>.trans p0_29,
        append4_getElem?_1 h0' h1' (by decide) (by decide) |>.trans p1_6,
        append4_getElem?_1 h0' h1' (by decide) (by decide) |>.trans p1_7,
        append4_getElem?_1 h0' h1' (by decide) (by decide) |>.trans p1_8,
        append4_getElem?_1 h0' h1' (by decide) (by decide) |>.trans p1_9,
        append4_getElem?_1 h0' h1' (by decide) (by decide) |>.trans p1_10,
        append4_getElem?_1 h0' h1' (by decide) (by decide) |>.trans p1_11,
        append4_getElem?_1 h0' h1' (by decide) (by decide) |>.trans p1_12,
        append4_getElem?_1 h0' h1' (by decide) (by decide) |>.trans p1_13,
        append4_getElem?_1 h0' h1' (by decide) (by decide) |>.trans p1_15,
        append4_getElem?_2 h0' h1' h2' (by decide) (by decide) |>.trans p2_26,
        append4_getElem?_2 h0' h1' h2' (by decide) (by decide) |>.trans p2_27,
        append4_getElem?_2 h0' h1' h2' (by decide) (by decide) |>.trans p2_28,
        append4_getElem?_2 h0' h1' h2' (by decide) (by decide) |>.trans p2_29,
        append4_getElem?_2 h0' h1' h2' (by decide) (by decide) |>.trans p2_30,
        append4_getElem?_2 h0' h1' h2' (by decide) (by decide) |>.trans p2_31,
        append4_getElem?_2 h0' h1' h2' (by decide) (by decide) |>.trans p2_32,
        append4_getElem?_2 h0' h1' h2' (by decide) (by decide) |>.trans p2_33,
        append4_getElem?_2 h0' h1' h2' (by decide) (by decide) |>.trans p2_34,
        append4_getElem?_3 h0' h1' h2' (by decide) |>.trans p3_0,
        append4_getElem?_3 h0' h1' h2' (by decide) |>.trans p3_1,
        append4_getElem?_3 h0' h1' h2' (by decide) |>.trans p3_2,
        append4_getElem?_3 h0' h1' h2' (by decide) |>.trans p3_8⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        dsimp only [ws']
        first
        | (rw [append4_getElem?_0 h0' (by decide), u0 _ (by decide)]
           exact List.getElem?_take_of_lt (by decide))
        | (rw [append4_getElem?_1 h0' h1' (by decide) (by decide), u1 _ (by decide)]
           exact drop_take_getElem? ws 35 35 _ (by decide))
        | (rw [append4_getElem?_3 h0' h1' h2' (by decide), u3 _ (by decide)]
           exact drop_take_getElem? ws 105 35 _ (by decide))
  · intro _ hJ; c0_hsplit
    · in_steps
      have h1 : max_v.toNat + 1 < 1000 := by
        simpa [Nat.mod_eq_of_lt (by omega : max_v.toNat + 1 < 2 ^ 64),
          show (1 : BitVec 64).toNat = 1 from rfl,
          show (1000 : BitVec 64).toNat = 1000 from rfl] using hc
      exact hJ _ _ ⟨rfl, by
        unfold fullMinDepthOf; simp only [h1, ↓reduceIte]
        have hm1 : max_v.toNat + 1 < 2 ^ 64 := by omega
        exact BitVec.eq_of_toNat_eq (by simp [Nat.mod_eq_of_lt hm1])⟩
    · in_steps
      have h1 : ¬ max_v.toNat + 1 < 1000 := by
        simpa [Nat.mod_eq_of_lt (by omega : max_v.toNat + 1 < 2 ^ 64),
          show (1 : BitVec 64).toNat = 1 from rfl,
          show (1000 : BitVec 64).toNat = 1000 from rfl] using hc
      exact hJ _ _ ⟨rfl, by unfold fullMinDepthOf; simp only [h1, ↓reduceIte]; rfl⟩

end InitPtrs

private def s13HdrW0 (fuel : BitVec 64) (w0 : List (BitVec 64)) : List (BitVec 64) :=
  hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet
    (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet w0 2 0#64) 3 1#64) 14 0#64) 15 0#64) 16 0#64)
    17 fuel) 18 0xFFFFFFFF#64) 19 0#64) 20 0#64) 27 0#64) 28 0x3FF0000000000000#64)
    30 0#64) 31 0#64) 32 1024#64) 33 1048576#64) 34 1024#64

private def s13HdrW1 (w1 : List (BitVec 64)) : List (BitVec 64) :=
  hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet
    (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet
    (hdrSet (hdrSet w1 18 0#64) 19 0#64) 20 0#64) 21 0xFFFFFFFF#64) 22 0#64) 23 0#64)
    24 0#64) 25 0#64) 26 0#64) 27 0#64) 28 0#64) 29 0#64) 0 1#64) 1 1#64) 2 0#64) 3 0#64)
    4 0#64) 5 0#64) 30 0#64) 31 0#64) 32 0#64) 33 1000#64) 34 0#64

private def s13HdrW2 (mv max_v : Nat) (w2 : List (BitVec 64)) : List (BitVec 64) :=
  hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet
    (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet
    (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet w2 22 (BitVec.ofNat 64 max_v))
    23 (BitVec.ofNat 64 mv)) 24 (BitVec.ofNat 64 (max_v - mv))) 25 0#64) 0 0#64) 1 0#64)
    2 0xFFFFFFFF#64) 3 0xFFFFFFFF#64) 4 0xFFFFFFFF#64) 5 0#64) 6 0#64) 7 0#64) 8 0#64)
    9 1000#64) 10 0#64) 11 1000#64) 12 0#64) 13 2#64) 14 6#64) 15 0#64) 16 1#64) 17 0#64)
    18 0x3FF0000000000000#64) 19 0#64) 20 0x3FF0000000000000#64) 21 0#64

private def s13HdrW3 (mv : Nat) (w3 : List (BitVec 64)) : List (BitVec 64) :=
  let rng := 0x9E3779B97F4A7C15#64 ^^^ (BitVec.ofNat 64 mv + 1#64)
  hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet
    (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet
    (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet (hdrSet w3 5 0#64) 9 rng) 10 100#64) 11 0#64)
    12 0#64) 13 2000#64) 14 0#64) 15 5000#64) 16 0#64) 17 0#64) 18 0#64) 19 0#64) 20 0#64)
    21 0#64) 22 0#64) 23 0#64) 24 0#64) 25 0#64) 26 0#64) 27 0#64) 28 0#64) 29 0#64)
    30 0#64) 31 0#64) 32 0#64) 33 0#64) 34 0#64

@[local simp] private theorem s13HdrW0_len {fu : BitVec 64} {w : List (BitVec 64)} :
    (s13HdrW0 fu w).length = w.length := by simp [s13HdrW0, hdrSet_len]
@[local simp] private theorem s13HdrW1_len {w : List (BitVec 64)} :
    (s13HdrW1 w).length = w.length := by simp [s13HdrW1, hdrSet_len]
@[local simp] private theorem s13HdrW2_len {mv mx : Nat} {w : List (BitVec 64)} :
    (s13HdrW2 mv mx w).length = w.length := by simp [s13HdrW2, hdrSet_len]
@[local simp] private theorem s13HdrW3_len {mv : Nat} {w : List (BitVec 64)} :
    (s13HdrW3 mv w).length = w.length := by simp [s13HdrW3, hdrSet_len]

private def s13InitHdrWitness (c : FullCfg) (fuel : BitVec 64) : FullState :=
  { core :=
      { d_cur := 0#64, d_val := 0#64, cur_vars := c.mv, unassigned := 0#64
        arena_len := 0, wlen := 1, wusable := 0#64, arena_garbage := 0#64
        first_reducible := 0xFFFFFFFF#64, num_irred := 0#64, num_redundant := 0#64
        num_binary := 0#64
        unflushed := 0#64, probing := 0#64, trail_end := 0, propagated := 0, cur_level := 0
        fuel := fuel, confl_ref := 0xFFFFFFFF#64, confl_type := 0#64, confl_lit0 := 0#64
        confl_lit1 := 0#64, tmp_cnt := 0, tmp_len := 0, min_clr_len := 0, min_clr_full := 0#64
        oom := 0#64, dense_mode := 0#64, inconsistent := 0#64
        vals := [], lit_mark := [], mrk := [], flags := [], lvl := [], rsns := [], trl := []
        trail_pos := [], tmp := [], min_clr := [], frame_trail := [], frame_dec := [], wvec := []
        repr := [], min_stk := [], arena := [], wstk := [] }
    scratch :=
      { heap_len := 0, scinc := 0x3FF0000000000000#64, rel_period := 1024#64
        rel_limit := 1048576#64, rel_wait := 1024#64, rel_u := 1#64, rel_v := 1#64
        rel_trigger := 0#64, conflicts := 0#64, learned_lits := 0#64, min_removed := 0#64
        delayed_len := 0, stable := 0#64, switched := 0#64, mode_count := 0#64
        mode_confl_lim := 1000#64, mode_tick_lim := 0#64, mode_saved_ticks := 0#64
        search_ticks := 0#64, q_first := 0xFFFFFFFF#64, q_last := 0xFFFFFFFF#64
        q_search_idx := 0xFFFFFFFF#64, q_search_stamp := 0#64, q_cur_stamp := 0#64
        target_assigned := 0#64, best_assigned := 0#64, rephase_limit := 1000#64
        rephased := 0#64, reduce_limit := 1000#64, reductions := 0#64, tier1 := 2#64
        tier2 := 6#64, restarts := 0#64, restart_limit := 1#64, ema_fast_biased := 0#64
        ema_fast_exp := 0x3FF0000000000000#64, ema_slow_biased := 0#64
        ema_slow_exp := 0x3FF0000000000000#64, extend_len := 0
        rng_state := 0x9E3779B97F4A7C15#64 ^^^ (BitVec.ofNat 64 c.mv + 1#64)
        chrono_levels := 100#64, otfs_cnt := 0#64, eager_sub_cnt := 0#64, probe_limit := 2000#64
        probings := 0#64, elim_limit := 5000#64, eliminations := 0#64, elim_bound := 0#64
        iterating := 0#64, hbr_cnt := 0#64, trans_cnt := 0#64, viv_cnt := 0#64, subst_cnt := 0#64
        cong_cnt := 0#64, sweep_cnt := 0#64, bve_cnt := 0#64, bce_cnt := 0#64, bva_cnt := 0#64
        walk_cnt_stat := 0#64, fwd_sub_cnt := 0#64, fwd_str_cnt := 0#64, ant_sz := 0#64
        res_sz := 0#64, walk_vals := [], phases := [], phases_target := [], phases_best := []
        walk_best := [], heap := [], pos := [], shrink_stk := [], q_prev := [], q_next := []
        q_stamp := [], wsort := [], work_stk1 := [], work_stk2 := [], tarjan_mark := []
        tarjan_reach := [], score := [], sim_sig := [], glue_used := [], last_learned := []
        delayed := [], red_refs := [], extend_stk := [], scratch_buf := [] } }

private theorem s13HdrW0_eq (c : FullCfg) (fuel : BitVec 64) (w0 : List (BitVec 64))
    (h0 : w0.length = 35)
    (hw : ∀ i ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29],
      w0[i]? = (HdrWordField.tailChunk0 c (s13InitHdrWitness c fuel))[i]?) :
    s13HdrW0 fuel w0 = HdrWordField.tailChunk0 c (s13InitHdrWitness c fuel) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := decompose35 w0 h0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have e0 := hw 0 (by simp); have e1 := hw 1 (by simp); have e4 := hw 4 (by simp)
  have e5 := hw 5 (by simp); have e6 := hw 6 (by simp); have e7 := hw 7 (by simp)
  have e8 := hw 8 (by simp); have e9 := hw 9 (by simp); have e10 := hw 10 (by simp)
  have e11 := hw 11 (by simp); have e12 := hw 12 (by simp); have e13 := hw 13 (by simp)
  have e21 := hw 21 (by simp); have e22 := hw 22 (by simp); have e23 := hw 23 (by simp)
  have e24 := hw 24 (by simp); have e25 := hw 25 (by simp); have e26 := hw 26 (by simp)
  have e29 := hw 29 (by simp)
  simp only [HdrWordField.tailChunk0, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq] at e0 e1 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e21 e22 e23 e24 e25 e26 e29
  simp [s13HdrW0, hdrSet_eq, HdrWordField.tailChunk0, s13InitHdrWitness, e0, e1, e4, e5, e6, e7,
    e8, e9, e10, e11, e12, e13, e21, e22, e23, e24, e25, e26, e29]

private theorem s13HdrW1_eq (c : FullCfg) (fuel : BitVec 64) (w1 : List (BitVec 64))
    (h1 : w1.length = 35)
    (hw : ∀ i ∈ [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17],
      w1[i]? = (HdrWordField.tailChunk1 c (s13InitHdrWitness c fuel))[i]?) :
    s13HdrW1 w1 = HdrWordField.tailChunk1 c (s13InitHdrWitness c fuel) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := decompose35 w1 h1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have e6 := hw 6 (by simp); have e7 := hw 7 (by simp); have e8 := hw 8 (by simp)
  have e9 := hw 9 (by simp); have e10 := hw 10 (by simp); have e11 := hw 11 (by simp)
  have e12 := hw 12 (by simp); have e13 := hw 13 (by simp); have e14 := hw 14 (by simp)
  have e15 := hw 15 (by simp); have e16 := hw 16 (by simp); have e17 := hw 17 (by simp)
  simp only [HdrWordField.tailChunk1, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq] at e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
  simp [s13HdrW1, hdrSet_eq, HdrWordField.tailChunk1, s13InitHdrWitness, e6, e7, e8, e9, e10, e11,
    e12, e13, e14, e15, e16, e17]

private theorem s13HdrW2_eq (c : FullCfg) (fuel : BitVec 64) (w2 : List (BitVec 64))
    (h2 : w2.length = 35)
    (hw : ∀ i ∈ [26, 27, 28, 29, 30, 31, 32, 33, 34],
      w2[i]? = (HdrWordField.tailChunk2 c (s13InitHdrWitness c fuel))[i]?) :
    s13HdrW2 c.mv c.max_vars w2 = HdrWordField.tailChunk2 c (s13InitHdrWitness c fuel) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := decompose35 w2 h2
  have hbva : c.max_vars - c.mv = c.bva_cap := by have := c.hbva; omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have e26 := hw 26 (by simp); have e27 := hw 27 (by simp); have e28 := hw 28 (by simp)
  have e29 := hw 29 (by simp); have e30 := hw 30 (by simp); have e31 := hw 31 (by simp)
  have e32 := hw 32 (by simp); have e33 := hw 33 (by simp); have e34 := hw 34 (by simp)
  simp only [HdrWordField.tailChunk2, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq] at e26 e27 e28 e29 e30 e31 e32 e33 e34
  simp [s13HdrW2, hdrSet_eq, HdrWordField.tailChunk2, s13InitHdrWitness, hbva, e26, e27, e28, e29,
    e30, e31, e32, e33, e34]

private theorem s13HdrW3_eq (c : FullCfg) (fuel : BitVec 64) (w3 : List (BitVec 64))
    (h3 : w3.length = 35)
    (hw : ∀ i ∈ [0, 1, 2, 3, 4, 6, 7, 8],
      w3[i]? = (HdrWordField.tailChunk3 c (s13InitHdrWitness c fuel))[i]?) :
    s13HdrW3 c.mv w3 = HdrWordField.tailChunk3 c (s13InitHdrWitness c fuel) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, d0, d1, d2, d3, d4, rfl⟩ := decompose35 w3 h3
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have e0 := hw 0 (by simp); have e1 := hw 1 (by simp); have e2 := hw 2 (by simp)
  have e3 := hw 3 (by simp); have e4 := hw 4 (by simp); have e6 := hw 6 (by simp)
  have e7 := hw 7 (by simp); have e8 := hw 8 (by simp)
  simp only [HdrWordField.tailChunk3, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq] at e0 e1 e2 e3 e4 e6 e7 e8
  simp [s13HdrW3, hdrSet_eq, HdrWordField.tailChunk3, s13InitHdrWitness, e0, e1, e2, e3, e4, e6, e7,
    e8]

section InitHdr
open scoped InHdrCfgTactics

theorem full_init_hdr_wp (Γ : Env) :
    ∀ a m Q X, fullInitHdrSpec a m Q X → Func.wp Γ full_init_hdr_body a m Q X := by
  rintro ⟨h, mv, max_v, fuel, ⟨⟩⟩ m Q X ⟨c, ws, R, rfl, rfl, rfl, hw, hws, hm, hQ⟩
  let s0 := s13InitHdrWitness c fuel
  have hws0 := hws s0
  have hmv' := c.hmv; have hmx' := c.hmaxv; unfold dimacsBound at hmv' hmx'
  have hmv_to : (BitVec.ofNat 64 c.mv).toNat = c.mv := bv64_ofNat_toNat (by omega)
  have hmx_to : (BitVec.ofNat 64 c.max_vars).toNat = c.max_vars := bv64_ofNat_toNat (by omega)
  let w0 := ws.take 35; let w1 := (ws.drop 35).take 35
  let w2 := (ws.drop 70).take 35; let w3 := (ws.drop 105).take 35
  have h0l : w0.length = 35 := by simp [w0, hw]
  have h1l : w1.length = 35 := by simp [w1, hw]
  have h2l : w2.length = 35 := by simp [w2, hw]
  have h3l : w3.length = 35 := by simp [w3, hw]
  have hw_len0 : (HdrWordField.tailChunk0 c s0).length = 35 := by simp [HdrWordField.tailChunk0]
  have hw_len1 : (HdrWordField.tailChunk1 c s0).length = 35 := by simp [HdrWordField.tailChunk1]
  have hw_len2 : (HdrWordField.tailChunk2 c s0).length = 35 := by simp [HdrWordField.tailChunk2]
  have hm4 : (hdrTail4Len c.hdr w0 w1 w2 w3 ⋆ R) m :=
    sep_pure_l.mpr ⟨⟨h0l, h1l, h2l, h3l⟩, array64_to_hdrTail4 hw hm⟩
  clear hm
  have hsub_bva : BitVec.ofNat 64 c.max_vars - BitVec.ofNat 64 c.mv =
      BitVec.ofNat 64 (c.max_vars - c.mv) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, hmv_to, hmx_to, BitVec.toNat_ofNat]
    have := c.hbva; omega
  unfold Func.wp full_init_hdr_body
  in_steps
  obtain ⟨_, hm_raw⟩ := sep_pure_l.mp hm
  have hm_arr : (array64 (c.hdr + 32) (s13HdrW0 fuel w0 ++ s13HdrW1 w1 ++
      s13HdrW2 c.mv c.max_vars w2 ++ s13HdrW3 c.mv w3) ⋆ R) m := by
    rw [← hdrTail4_eq_array64 (by simp [h0l]) (by simp [h1l]) (by simp [h2l])]
    rw [hsub_bva] at hm_raw
    exact hm_raw
  have hi0 : ∀ j ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29],
      j < 35 ∧ j ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
        41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
        102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113] := by decide
  have hi1 : ∀ j ∈ [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17],
      j < 35 ∧ (35 + j) ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
        41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
        102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113] := by decide
  have hi2 : ∀ j ∈ [26, 27, 28, 29, 30, 31, 32, 33, 34],
      j < 35 ∧ (70 + j) ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
        41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
        102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113] := by decide
  have hi3 : ∀ j ∈ [0, 1, 2, 3, 4, 6, 7, 8],
      j < 35 ∧ (105 + j) ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
        41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
        102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113] := by decide
  have heq0 : s13HdrW0 fuel w0 = HdrWordField.tailChunk0 c s0 :=
    s13HdrW0_eq c fuel w0 h0l fun i hi => by
      have ⟨hi', hm'⟩ := hi0 i hi; have hgi := hws0 i hm'
      dsimp only [w0]; rw [List.getElem?_take_of_lt hi', hgi]
      unfold hdrTailWords; exact append4_getElem?_0 hw_len0 hi'
  have heq1 : s13HdrW1 w1 = HdrWordField.tailChunk1 c s0 :=
    s13HdrW1_eq c fuel w1 h1l fun i hi => by
      have ⟨hi35, hm'⟩ := hi1 i hi; have hgi := hws0 (35 + i) hm'
      dsimp only [w1]; rw [drop_take_getElem? ws 35 35 i hi35, hgi]
      unfold hdrTailWords
      rw [append4_getElem?_1 hw_len0 hw_len1 (by omega) (by omega), show 35 + i - 35 = i by omega]
  have heq2 : s13HdrW2 c.mv c.max_vars w2 = HdrWordField.tailChunk2 c s0 :=
    s13HdrW2_eq c fuel w2 h2l fun i hi => by
      have ⟨hi35, hm'⟩ := hi2 i hi; have hgi := hws0 (70 + i) hm'
      dsimp only [w2]; rw [drop_take_getElem? ws 70 35 i hi35, hgi]
      unfold hdrTailWords
      rw [append4_getElem?_2 hw_len0 hw_len1 hw_len2 (by omega) (by omega),
        show 70 + i - 70 = i by omega]
  have heq3 : s13HdrW3 c.mv w3 = HdrWordField.tailChunk3 c s0 :=
    s13HdrW3_eq c fuel w3 h3l fun i hi => by
      have ⟨hi35, hm'⟩ := hi3 i hi; have hgi := hws0 (105 + i) hm'
      dsimp only [w3]; rw [drop_take_getElem? ws 105 35 i hi35, hgi]
      unfold hdrTailWords
      rw [append4_getElem?_3 hw_len0 hw_len1 hw_len2 (by omega), show 105 + i - 105 = i by omega]
  rw [heq0, heq1, heq2, heq3] at hm_arr
  have htail_eq : HdrWordField.tailChunk0 c s0 ++ HdrWordField.tailChunk1 c s0 ++
      HdrWordField.tailChunk2 c s0 ++ HdrWordField.tailChunk3 c s0 = hdrTailWords c s0 := rfl
  rw [htail_eq] at hm_arr
  exact hQ s0 m rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hm_arr

end InitHdr

end LeanQbe.T.Examples.Kissat.Proof.Internal
