/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.ParseBase
public import LeanQbe.T.Examples.Arisca.Proof.ParseMid
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0StepAttr
meta import LeanQbe.T.Logic.C0StepAttr
import LeanQbe.T.Logic.Arith

/-!
# ARiSCA ART Table Parser WP Proof (`Arisca.Proof.Parse`)

WP proof for `ar_parse_art_header_and_tables` (`ar_parse_art_header_and_tables_wp`), re-exporting
all parser specs and WP proofs from `ParseBase` and `ParseMid`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Proof

open Std Std.ExtHashMap LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Arisca LeanQbe.T.Examples.Arisca.Src
open LeanQbe.T.Examples.Arisca.Src.Header LeanQbe.T.Examples.Arisca.Src.Parse

public section

private theorem arrayPad_u32_eq (a : BitVec 64) (xs : List (BitVec 32)) :
    arrayPad i32 a xs = (array (t := i32) a xs ⋆
      region (a + BitVec.ofNat 64 (4 * xs.length))
        (align8 (4 * xs.length) - 4 * xs.length)) := by
  simp only [arrayPad, SlabSeg.ofArrayAlign8, SlabSeg.ofArray, Ty.bytes, Ty.size]

private theorem bv32_add1_toNat {j n : BitVec 32} (h : j.toNat < n.toNat) :
    (j + 1#32).toNat = j.toNat + 1 := by c0_bv_omega [h]

private theorem u64_and3_shr2 {x : BitVec 64} (h : (x &&& 3#64) = 0#64) :
    4 * (x >>> 2).toNat = x.toNat := by
  have hx : x.toNat % 4 = 0 := by
    have h1 : (x &&& 3#64).toNat = 0 := by rw [h]; rfl
    rwa [BitVec.toNat_and, show (3#64 : BitVec 64).toNat = 2 ^ 2 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod] at h1
  rw [bv_c0_toNat_ushiftRight_nat]; omega

private theorem u32_and1_even {x : BitVec 32} (h : (x &&& 1#32) = 0#32) : x.toNat % 2 = 0 := by
  have h1 : (x &&& 1#32).toNat = 0 := by rw [h]; rfl
  rwa [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 2 ^ 1 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod] at h1

private theorem ar_nw_step (Γ : LeanQbe.T.Env)
    (hNW : ∀ xs m Q X, arNextWordSpec xs m Q X →
      Γ "ar_next_word" [i64] [.bool, i32] xs m Q X)
    {cx art : BitVec 64} {s : ArCtxState} {artBytes : List UInt8} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [.bool, i32]} {X : XPost} {k : Nat} (sNext : ArCtxState)
    (hm : (arCtxMem cx s ⋆ (bytes art artBytes ⋆ R)) m) (hs_art : s.art = art)
    (hart : art.toNat + artBytes.length < 2 ^ 64) (hnw : 4 * s.nw.toNat ≤ artBytes.length)
    (hk_pos : s.pos = BitVec.ofNat 64 k) (hk_lt : k + 1 < 2 ^ 64)
    (hsNext : sNext = { s with pos := BitVec.ofNat 64 (k + 1) })
    (hk : ∀ (ok : Bool) (v : BitVec 32) (m' : Mem 64),
      (ok = true → k < s.nw.toNat ∧ v = BitVec.ofNat 32 (wordAt artBytes k) ∧
        (arCtxMem cx sNext ⋆ (bytes art artBytes ⋆ R)) m') →
      (ok = false → ∃ s' : ArCtxState, s'.w = s.w ∧ s'.wlen = s.wlen ∧
        (arCtxMem cx s' ⋆ (bytes art artBytes ⋆ R)) m') → Q (ok, v, ⟨⟩) m') :
    Γ "ar_next_word" [i64] [.bool, i32] (cx, ⟨⟩) m Q X := by
  rw [← hs_art] at hm hart
  refine hNW (cx, ⟨⟩) m Q X ⟨s, artBytes, R, hart, hnw, by simpa only [← sep_assoc] using hm, ?_⟩
  intro ok v s' m' hif hm'; rw [hs_art] at hm'
  have hm'' : (arCtxMem cx s' ⋆ (bytes art artBytes ⋆ R)) m' := by simpa only [sep_assoc] using hm'
  refine hk ok v m' (fun hok => ?_) (fun hok => ?_)
  · by_cases hlt : s.pos.toNat < s.nw.toNat
    · simp only [hlt, ↓reduceIte] at hif; rcases hif with ⟨_, hv, hs'⟩
      have hkp : s.pos.toNat = k := by
        rw [hk_pos, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hpos1 : s.pos + 1 = BitVec.ofNat 64 (k + 1) := by
        rw [hk_pos]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, Nat.mod_eq_of_lt hk_lt]
      refine ⟨hkp ▸ hlt, hkp ▸ hv, ?_⟩; rwa [hs', hpos1, ← hsNext] at hm''
    · simp only [hlt, ↓reduceIte] at hif; exact absurd hok (by rw [hif.1]; decide)
  · by_cases hlt : s.pos.toNat < s.nw.toNat <;> simp only [hlt, ↓reduceIte] at hif <;>
      rcases hif with ⟨_, _, hs'⟩ <;> exact ⟨s', by rw [hs'], by rw [hs'], hm''⟩

private theorem bv32_eq_0_or_1 {x : BitVec 32} (h : ¬ (1#32 : BitVec 32).toNat < x.toNat) :
    x = 0#32 ∨ x = 1#32 := by
  have hx : x.toNat = 0 ∨ x.toNat = 1 := by
    rw [show (1#32 : BitVec 32).toNat = 1 from rfl] at h; omega
  rcases hx with h0 | h1
  · exact Or.inl (BitVec.eq_of_toNat_eq (by simpa using h0))
  · exact Or.inr (BitVec.eq_of_toNat_eq (by simpa using h1))

private theorem bv32_eq_0_1_2 {x : BitVec 32} (h : ¬ (2#32 : BitVec 32).toNat < x.toNat) :
    x = 0#32 ∨ x = 1#32 ∨ x = 2#32 := by
  have hx : x.toNat = 0 ∨ x.toNat = 1 ∨ x.toNat = 2 := by
    rw [show (2#32 : BitVec 32).toNat = 2 from rfl] at h; omega
  rcases hx with h0 | h1 | h2
  · exact Or.inl (BitVec.eq_of_toNat_eq (by simpa using h0))
  · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq (by simpa using h1)))
  · exact Or.inr (Or.inr (BitVec.eq_of_toNat_eq (by simpa using h2)))

private theorem bv32_ge_of_not_ult {x : BitVec 32} {k : Nat}
    (h : ¬ x.toNat < (BitVec.ofNat 32 k).toNat) (hk : k < 2 ^ 32) : k ≤ x.toNat := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at h; omega

private theorem bv32_le_of_not_ugt {x : BitVec 32} {k : Nat}
    (h : ¬ (BitVec.ofNat 32 k).toNat < x.toNat) (hk : k < 2 ^ 32) : x.toNat ≤ k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at h; omega

private theorem sep_pull5r {A B C D E F : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ (C ⋆ (D ⋆ (E ⋆ F))))) m) : (E ⋆ (A ⋆ (B ⋆ (C ⋆ (D ⋆ F))))) m :=
  sep_swap2r (sep_mono_r (fun _ => sep_pull4r) h)

private theorem sep_push4r {A B C D E F : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ (C ⋆ (D ⋆ (E ⋆ F))))) m) : (B ⋆ (C ⋆ (D ⋆ (E ⋆ (A ⋆ F))))) m :=
  sep_mono_r (fun _ => sep_mono_r (fun _ => sep_mono_r (fun _ => sep_swap2r)))
    (sep_mono_r (fun _ => sep_mono_r (fun _ => sep_swap2r))
      (sep_mono_r (fun _ => sep_swap2r) (sep_swap2r h)))

private theorem sep_push3r {A B C D E : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ (C ⋆ (D ⋆ E)))) m) : (B ⋆ (C ⋆ (D ⋆ (A ⋆ E)))) m :=
  sep_mono_r (fun _ => sep_mono_r (fun _ => sep_swap2r))
    (sep_mono_r (fun _ => sep_swap2r) (sep_swap2r h))

private theorem art_pre_collapse {cx art w top rhs0Ptr rhs1Ptr olitPtr : BitVec 64}
    {s' : ArCtxState} {rhs0 rhs1 olit : List (BitVec 32)} {artBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64} (hfit : w.toNat + wlen < 2 ^ 64)
    (htop : top.toNat =
      776 + align8 (4 * rhs0.length) + align8 (4 * rhs1.length) + 4 * olit.length)
    (hle : top.toNat ≤ wlen) (hr0 : rhs0Ptr = w + 776#64)
    (hr1 : rhs1Ptr = w + BitVec.ofNat 64 (776 + align8 (4 * rhs0.length)))
    (hol : olitPtr =
      w + BitVec.ofNat 64 (776 + align8 (4 * rhs0.length) + align8 (4 * rhs1.length)))
    (hm : (arCtxMem cx s' ⋆ (bytes art artBytes ⋆ (arrayPad i32 rhs0Ptr rhs0 ⋆
      (arrayPad i32 rhs1Ptr rhs1 ⋆ (array (t := i32) olitPtr olit ⋆
       (region (w + top) (wlen - top.toNat) ⋆ R)))))) m) :
    (arCtxMem cx s' ⋆ region (w + 776#64) (wlen - 776) ⋆ bytes art artBytes ⋆ R) m := by
  have h3 : (arrayPad i32 rhs0Ptr rhs0 ⋆ arrayPad i32 rhs1Ptr rhs1 ⋆
      array (t := i32) olitPtr olit ⋆ region (w + top) (wlen - top.toNat) ⋆
      (arCtxMem cx s' ⋆ (bytes art artBytes ⋆ R))) m := by
    simpa only [sep_assoc] using sep_push4r (sep_mono_r (fun _ => sep_push4r) hm)
  simpa only [sep_assoc] using sep_swap2r (aigArraysPre_collapse hfit htop hle hr0 hr1 hol h3)

private theorem bv64_shl_setWidth_lt64 {x : BitVec 32} (hx : x.toNat < 64) :
    ((1 : BitVec 64) <<< ((x.setWidth 64).toNat % 64)) = 1#64 <<< x.setWidth 64 := by
  have h2 : (x.setWidth 64).toNat = x.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  rw [h2, Nat.mod_eq_of_lt hx]; exact congrArg (1#64 <<< ·) h2.symm

private theorem bv64_shl_sub64_lt128 {x : BitVec 32} (h1 : 64 ≤ x.toNat) (h2 : x.toNat ≤ 128)
    (hne : x ≠ 128#32) : ((1 : BitVec 64) <<< (((x - (64 : BitVec 32)).setWidth 64).toNat % 64)) =
      1#64 <<< (x - 64#32).setWidth 64 := by
  have hlt : x.toNat < 128 := by
    rcases Nat.lt_or_eq_of_le h2 with h | heq
    · exact h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using heq)) hne
  have hs : ((x - 64#32).setWidth 64).toNat = x.toNat - 64 := by
    have h64 : (64#32 : BitVec 32).toNat ≤ x.toNat := by simpa using h1
    rw [BitVec.toNat_setWidth, BitVec.toNat_sub_of_le (BitVec.le_def.mpr h64),
      show (64#32 : BitVec 32).toNat = 64 from rfl, Nat.mod_eq_of_lt (by omega)]
  rw [show (64 : BitVec 32) = 64#32 from rfl, hs, Nat.mod_eq_of_lt (by omega)]
  exact congrArg (1#64 <<< ·) hs.symm

private theorem u64_mul4_toNat {x : BitVec 32} (hx : x.toNat ≤ 0x3FFFFFFF) :
    (4#64 * x.setWidth 64).toNat = 4 * x.toNat := by
  rw [BitVec.toNat_mul, BitVec.toNat_setWidth, show (4#64 : BitVec 64).toNat = 4 from rfl,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem u64_setWidth_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  have := x.isLt; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]

private theorem art_pos_sum_le {nw : BitVec 64} {nNets nIn nOut : BitVec 32}
    (hnw10 : 10 ≤ nw.toNat) (hn : nNets.toNat ≤ 0x3FFFFFFF) (hi : nIn.toNat ≤ 0x3FFFFFFF)
    (ho : nOut.toNat ≤ 256) (hc : ¬ (2 ^ 64 - 10 + nw.toNat) % 2 ^ 64 <
      (nNets.toNat + nIn.toNat + nOut.toNat) % 2 ^ 64) :
    10 + nNets.toNat + nIn.toNat + nOut.toNat ≤ nw.toNat := by
  have := nw.isLt
  rw [show 2 ^ 64 - 10 + nw.toNat = 2 ^ 64 + (nw.toNat - 10) by omega,
    Nat.add_mod_left, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc
  omega

private theorem art_mid_collapse {cx art w top0 top' rhs0Ptr rhs1Ptr olitPtr : BitVec 64}
    {s' : ArCtxState} {rhs0 rhs1 olit : List (BitVec 32)} {artBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64} (hfit : w.toNat + wlen < 2 ^ 64)
    (htop : top0.toNat =
      776 + align8 (4 * rhs0.length) + align8 (4 * rhs1.length) + 4 * olit.length)
    (hbt : top0.toNat ≤ top'.toNat) (hle : top'.toNat ≤ wlen) (hr0 : rhs0Ptr = w + 776#64)
    (hr1 : rhs1Ptr = w + BitVec.ofNat 64 (776 + align8 (4 * rhs0.length)))
    (hol : olitPtr =
      w + BitVec.ofNat 64 (776 + align8 (4 * rhs0.length) + align8 (4 * rhs1.length)))
    (hm : (arCtxMem cx s' ⋆ (region (w + BitVec.ofNat 64 top0.toNat) (top'.toNat - top0.toNat) ⋆
      (region (w + top') (wlen - top'.toNat) ⋆ (bytes art artBytes ⋆ (arrayPad i32 rhs0Ptr rhs0 ⋆
       (arrayPad i32 rhs1Ptr rhs1 ⋆ (array (t := i32) olitPtr olit ⋆ R))))))) m) :
    (arCtxMem cx s' ⋆ region (w + 776#64) (wlen - 776) ⋆ bytes art artBytes ⋆ R) m := by
  rw [← addr_add_toNat w top', ← sep_assoc (region (w + BitVec.ofNat 64 top0.toNat) _),
    region_merge_offset w hbt hle hfit, addr_add_toNat] at hm
  exact art_pre_collapse hfit htop (Nat.le_trans hbt hle) hr0 hr1 hol
    (sep_mono_r (fun _ => sep_push4r) hm)

private theorem arrayPad_u8_eq (a : BitVec 64) (xs : List (BitVec 8)) :
    arrayPad i8 a xs = (array (t := i8) a xs ⋆
      region (a + BitVec.ofNat 64 xs.length) (align8 xs.length - xs.length)) := by
  simp only [arrayPad, SlabSeg.ofArrayAlign8, SlabSeg.ofArray, Ty.bytes, Ty.size,
    Nat.reduceDiv, Nat.reduceAdd, Nat.one_mul]

private theorem art_pre_pop_shuffle {C A_top R_rem B_art R0 R1 Ol R : Mem 64 → Prop} {m : Mem 64}
    (h : (C ⋆ (A_top ⋆ (R_rem ⋆ (B_art ⋆ (R0 ⋆ (R1 ⋆ (Ol ⋆ R))))))) m) :
    (R0 ⋆ (R1 ⋆ (Ol ⋆ (A_top ⋆ (C ⋆ (R_rem ⋆ (B_art ⋆ R))))))) m := by
  have h1 := sep_mono_r (fun _ => sep_mono_r (fun _ => sep_mono_r (fun _ => sep_push3r)))
    (sep_push3r h)
  have h2 := sep_mono_r (fun _ => sep_mono_r (fun _ => sep_pull4r))
    (sep_mono_r (fun _ => sep_pull4r) (sep_pull4r h1))
  exact sep_mono_r (fun _ => sep_mono_r (fun _ => sep_mono_r (fun _ => sep_mono_r
    (fun _ => sep_pull3r)))) h2

private theorem align8_add_right {a b : Nat} (ha : a % 8 = 0) : align8 (a + b) = a + align8 b := by
  unfold align8; omega

private theorem art_build_geom {w top0 top1 top2 top3 top4 top5 top6 top7 top8 top9 top10
    top11 top12 top13 top14 top15 : BitVec 64} {s : ArCtxState}
    {A O nNets nIn nOut nB nRo nRn nP nF nInB nOuB nSn nSp nMn nMv nD nGy nCl nCh : Nat}
    (htop0 : top0.toNat = 776 + align8 (4 * A) + align8 (4 * A) + 4 * O) (hs_w : s.w = w)
    (hsB : s.bind = w + BitVec.ofNat 64 (align8 top0.toNat))
    (htB : top1.toNat = align8 top0.toNat + nB)
    (hsRo : s.rule_off = w + BitVec.ofNat 64 (align8 top1.toNat))
    (htRo : top2.toNat = align8 top1.toNat + nRo)
    (hsRn : s.rule_n = w + BitVec.ofNat 64 (align8 top2.toNat))
    (htRn : top3.toNat = align8 top2.toNat + nRn)
    (hsP : s.partner = w + BitVec.ofNat 64 (align8 top3.toNat))
    (htP : top4.toNat = align8 top3.toNat + nP)
    (hsF : s.flipped = w + BitVec.ofNat 64 (align8 top4.toNat))
    (htF : top5.toNat = align8 top4.toNat + nF)
    (hsIn : s.in_net = w + BitVec.ofNat 64 (align8 top5.toNat))
    (htIn : top6.toNat = align8 top5.toNat + nInB)
    (hsOu : s.out_ref = w + BitVec.ofNat 64 (align8 top6.toNat))
    (htOu : top7.toNat = align8 top6.toNat + nOuB)
    (hsSn : s.stk_n = w + BitVec.ofNat 64 (align8 top7.toNat))
    (htSn : top8.toNat = align8 top7.toNat + nSn)
    (hsSp : s.stk_p = w + BitVec.ofNat 64 (align8 top8.toNat))
    (htSp : top9.toNat = align8 top8.toNat + nSp)
    (hsMn : s.memo_n = w + BitVec.ofNat 64 (align8 top9.toNat))
    (htMn : top10.toNat = align8 top9.toNat + nMn)
    (hsMv : s.memo_v = w + BitVec.ofNat 64 (align8 top10.toNat))
    (htMv : top11.toNat = align8 top10.toNat + nMv)
    (hsD : s.dense = w + BitVec.ofNat 64 (align8 top11.toNat))
    (htD : top12.toNat = align8 top11.toNat + nD)
    (hsGy : s.gsy = w + BitVec.ofNat 64 (align8 top12.toNat))
    (htGy : top13.toNat = align8 top12.toNat + nGy)
    (hsCl : s.gcl = w + BitVec.ofNat 64 (align8 top13.toNat))
    (htCl : top14.toNat = align8 top13.toNat + nCl)
    (hsCh : s.gch = w + BitVec.ofNat 64 (align8 top14.toNat))
    (htCh : top15.toNat = align8 top14.toNat + nCh)
    (hr0 : s.rhs0 = w + 776#64) (hr1 : s.rhs1 = w + BitVec.ofNat 64 (776 + align8 (4 * A)))
    (hol : s.olit = w + BitVec.ofNat 64 (776 + align8 (4 * A) + align8 (4 * A)))
    (hnB : nB = 4 * nNets) (hnRo : nRo = 4 * nNets) (hnRn : nRn = 4 * nNets)
    (hnP : nP = 4 * nNets) (hnF : nF = nNets) (hnIn : nInB = 4 * nIn) (hnOu : nOuB = 4 * nOut)
    (hnSn : nSn = 4 * arTTStk) (hnSp : nSp = 4 * arTTStk) (hnMn : nMn = 4 * arTTMaxAnd)
    (hnMv : nMv = 8 * arTTMaxAnd) (hnD : nD = 8 * 128) (hnGy : nGy = 4 * 85)
    (hnCl : nCl = 8 * 16) (hnCh : nCh = 8 * 16) :
    TablesGeom s A O nNets nIn nOut top15.toNat := by
  have h776 : 776 % 8 = 0 := by decide
  have hmA := align8_mod (4 * A)
  have hmO := align8_mod (4 * O)
  let t0 := 776 + align8 (4 * A) + align8 (4 * A) + align8 (4 * O)
  have ht0m : t0 % 8 = 0 := by dsimp only [t0]; omega
  have ha0 : align8 top0.toNat = t0 := by
    rw [htop0, Nat.add_assoc, Nat.add_assoc, align8_add_right h776, align8_add_right hmA,
      align8_add_right hmA]
    dsimp only [t0]; omega
  have hstep : ∀ {p nxt sz off : Nat}, nxt = align8 p + sz → align8 p = off → off % 8 = 0 →
      align8 nxt = off + align8 sz := fun hnxt hp hoff => by rw [hnxt, hp, align8_add_right hoff]
  have ha1 : align8 top1.toNat = t0 + align8 (4 * nNets) := hstep (hnB ▸ htB) ha0 ht0m
  have ha2 : align8 top2.toNat = t0 + align8 (4 * nNets) + align8 (4 * nNets) :=
    hstep (hnRo ▸ htRo) ha1 (by have := align8_mod (4 * nNets); omega)
  have ha3 : align8 top3.toNat =
      t0 + align8 (4 * nNets) + align8 (4 * nNets) + align8 (4 * nNets) :=
    hstep (hnRn ▸ htRn) ha2 (by have := align8_mod (4 * nNets); omega)
  have ha4 : align8 top4.toNat =
      t0 + align8 (4 * nNets) + align8 (4 * nNets) + align8 (4 * nNets) + align8 (4 * nNets) :=
    hstep (hnP ▸ htP) ha3 (by have := align8_mod (4 * nNets); omega)
  have ha5 : align8 top5.toNat = t0 + align8 (4 * nNets) + align8 (4 * nNets) +
      align8 (4 * nNets) + align8 (4 * nNets) + align8 nNets :=
    hstep (hnF ▸ htF) ha4 (by have := align8_mod (4 * nNets); omega)
  have ha6 : align8 top6.toNat = t0 + align8 (4 * nNets) + align8 (4 * nNets) +
      align8 (4 * nNets) + align8 (4 * nNets) + align8 nNets + align8 (4 * nIn) :=
    hstep (hnIn ▸ htIn) ha5
      (by have := align8_mod (4 * nNets); have := align8_mod nNets; omega)
  have ha7 : align8 top7.toNat = t0 + align8 (4 * nNets) + align8 (4 * nNets) +
      align8 (4 * nNets) + align8 (4 * nNets) + align8 nNets + align8 (4 * nIn) +
      align8 (4 * nOut) :=
    hstep (hnOu ▸ htOu) ha6 (by
      have := align8_mod (4 * nNets); have := align8_mod nNets
      have := align8_mod (4 * nIn); omega)
  have ha8 : align8 top8.toNat = align8 top7.toNat + 4 * arTTStk := by
    rw [htSn, hnSn, align8_add_right (align8_mod _),
      show align8 (4 * arTTStk) = 4 * arTTStk by simp [arTTStk]; decide]
  have ha9 : align8 top9.toNat = align8 top8.toNat + 4 * arTTStk := by
    rw [htSp, hnSp, align8_add_right (align8_mod _),
      show align8 (4 * arTTStk) = 4 * arTTStk by simp [arTTStk]; decide]
  have ha10 : align8 top10.toNat = align8 top9.toNat + 4 * arTTMaxAnd := by
    rw [htMn, hnMn, align8_add_right (align8_mod _),
      show align8 (4 * arTTMaxAnd) = 4 * arTTMaxAnd by simp [arTTMaxAnd]; decide]
  have ha11 : align8 top11.toNat = align8 top10.toNat + 8 * arTTMaxAnd := by
    rw [htMv, hnMv, align8_add_right (align8_mod _),
      show align8 (8 * arTTMaxAnd) = 8 * arTTMaxAnd by simp [arTTMaxAnd]; decide]
  have ha12 : align8 top12.toNat = align8 top11.toNat + 8 * 128 := by
    rw [htD, hnD, align8_add_right (align8_mod _), show align8 (8 * 128) = 8 * 128 by decide]
  have ha13 : align8 top13.toNat = align8 top12.toNat + align8 (4 * 85) := by
    rw [htGy, hnGy, align8_add_right (align8_mod _)]
  have ha14 : align8 top14.toNat = align8 top13.toNat + 8 * 16 := by
    rw [htCl, hnCl, align8_add_right (align8_mod _), show align8 (8 * 16) = 8 * 16 by decide]
  refine ⟨?_, hs_w ▸ hr0, hs_w ▸ hr1, hs_w ▸ hol, by rw [hs_w, hsB, ha0],
    by rw [hsRo, hsB, ha1, ha0, addr_add_ofNat],
    by rw [hsRn, hsRo, ha2, ha1, addr_add_ofNat, Nat.add_assoc],
    by rw [hsP, hsRn, ha3, ha2, addr_add_ofNat, Nat.add_assoc],
    by rw [hsF, hsP, ha4, ha3, addr_add_ofNat, Nat.add_assoc],
    by rw [hsIn, hsF, ha5, ha4, addr_add_ofNat, Nat.add_assoc],
    by rw [hsOu, hsIn, ha6, ha5, addr_add_ofNat, Nat.add_assoc],
    by rw [hsSn, hsOu, ha7, ha6, addr_add_ofNat, Nat.add_assoc],
    by rw [hsSp, hsSn, ha8, addr_add_ofNat], by rw [hsMn, hsSp, ha9, addr_add_ofNat],
    by rw [hsMv, hsMn, ha10, addr_add_ofNat], by rw [hsD, hsMv, ha11, addr_add_ofNat],
    by rw [hsGy, hsD, ha12, addr_add_ofNat], by rw [hsCl, hsGy, ha13, addr_add_ofNat],
    by rw [hsCh, hsCl, ha14, addr_add_ofNat]⟩
  rw [htCh, hnCh, ha14, ha13, ha12, ha11, ha10, ha9, ha8, ha7, tablesEndTop]

private def artPadRest (s : ArCtxState) (rhs0 rhs1 : List (BitVec 32))
    (O nNets nIn nOut top0 : Nat) (stkN stkP memoN : List (BitVec 32))
    (memoV dense : List (BitVec 64)) (gsy : List (BitVec 32)) (gcl gch : List (BitVec 64))
    (R : Mem 64 → Prop) : Mem 64 → Prop :=
  arrayPad i32 s.rhs0 rhs0 ⋆ region (s.olit + BitVec.ofNat 64 (4 * O)) (align8 (4 * O) - 4 * O) ⋆
  arrayPad i32 s.rhs1 rhs1 ⋆
  region (s.bind + BitVec.ofNat 64 (4 * nNets)) (align8 (4 * nNets) - 4 * nNets) ⋆
  region (s.rule_off + BitVec.ofNat 64 (4 * nNets)) (align8 (4 * nNets) - 4 * nNets) ⋆
  region (s.rule_n + BitVec.ofNat 64 (4 * nNets)) (align8 (4 * nNets) - 4 * nNets) ⋆
  region (s.partner + BitVec.ofNat 64 (4 * nNets)) (align8 (4 * nNets) - 4 * nNets) ⋆
  region (s.flipped + BitVec.ofNat 64 nNets) (align8 nNets - nNets) ⋆
  region (s.in_net + BitVec.ofNat 64 (4 * nIn)) (align8 (4 * nIn) - 4 * nIn) ⋆
  region (s.out_ref + BitVec.ofNat 64 (4 * nOut)) (align8 (4 * nOut) - 4 * nOut) ⋆
  gateScratchMem s stkN stkP memoN memoV dense gsy gcl gch ⋆
  region (s.w + BitVec.ofNat 64 top0) (s.wlen.toNat - top0) ⋆ R

private abbrev ArtLoopMem (cx art : BitVec 64) (s2 sCur : ArCtxState)
    (bC roC rnC pC : List (BitVec 32)) (fC : List (BitVec 8))
    (inC ouC olit rhs0 rhs1 : List (BitVec 32)) (O nNets nIn nOut top0 : Nat)
    (stkN stkP memoN : List (BitVec 32)) (memoV dense : List (BitVec 64))
    (gsy : List (BitVec 32)) (gcl gch : List (BitVec 64))
    (artBytes : List UInt8) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  arCtxMem cx sCur ⋆ (bytes art artBytes ⋆ (array (t := i32) s2.bind bC ⋆
    array (t := i32) s2.rule_off roC ⋆ array (t := i32) s2.rule_n rnC ⋆
    array (t := i32) s2.partner pC ⋆ array (t := i8) s2.flipped fC ⋆
    array (t := i32) s2.in_net inC ⋆ array (t := i32) s2.out_ref ouC ⋆
    array (t := i32) s2.olit olit ⋆
    artPadRest s2 rhs0 rhs1 O nNets nIn nOut top0 stkN stkP memoN memoV dense gsy gcl gch R))

private theorem art_unpack_tables {cx art : BitVec 64} {s : ArCtxState}
    {O nNets nIn nOut top0 : Nat}
    {rhs0 rhs1 olit bindArr ruleOff ruleN partnerArr : List (BitVec 32)}
    {flippedArr : List (BitVec 8)} {inNetArr outRefArr stkN stkP memoN : List (BitVec 32)}
    {memoV dense : List (BitVec 64)} {gsy : List (BitVec 32)} {gcl gch : List (BitVec 64)}
    {artBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (hol : olit.length = O) (hb : bindArr.length = nNets) (hro : ruleOff.length = nNets)
    (hrn : ruleN.length = nNets) (hp : partnerArr.length = nNets) (hf : flippedArr.length = nNets)
    (hin : inNetArr.length = nIn) (hout : outRefArr.length = nOut) (htop : s.top.toNat = top0)
    (hm : (aigArraysMem s rhs0 rhs1 olit ⋆
      netTablesMem s bindArr ruleOff ruleN partnerArr flippedArr inNetArr outRefArr ⋆
      gateScratchMem s stkN stkP memoN memoV dense gsy gcl gch ⋆
      (arCtxMem cx s ⋆ (region (s.w + s.top) (s.wlen.toNat - s.top.toNat) ⋆
       (bytes art artBytes ⋆ R)))) m) :
    ArtLoopMem cx art s s bindArr ruleOff ruleN partnerArr flippedArr inNetArr outRefArr olit
      rhs0 rhs1 O nNets nIn nOut top0 stkN stkP memoN memoV dense gsy gcl gch artBytes R m := by
  simp only [ArtLoopMem, aigArraysMem, netTablesMem, artPadRest, arrayPad_u32_eq, arrayPad_u8_eq]
    at hm ⊢
  rw [hol, hb, hro, hrn, hp, hf, hin, hout, ← addr_add_toNat s.w s.top, htop] at hm
  exact sep_cast hm (by ac_rfl)

private theorem art_pack_pos {cx art pos' : BitVec 64} (s : ArCtxState)
    {O nNets nIn nOut top0 : Nat}
    {rhs0 rhs1 olit bC roC rnC pC : List (BitVec 32)} {fC : List (BitVec 8)}
    {inC ouC stkN stkP memoN : List (BitVec 32)} {memoV dense : List (BitVec 64)}
    {gsy : List (BitVec 32)} {gcl gch : List (BitVec 64)} {artBytes : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hol : olit.length = O) (hb : bC.length = nNets) (hro : roC.length = nNets)
    (hrn : rnC.length = nNets) (hp : pC.length = nNets) (hf : fC.length = nNets)
    (hin : inC.length = nIn) (hout : ouC.length = nOut) (htop : s.top.toNat = top0)
    (hm : ArtLoopMem cx art s { s with pos := pos' } bC roC rnC pC fC inC ouC
      olit rhs0 rhs1 O nNets nIn nOut top0 stkN stkP memoN memoV dense gsy gcl gch artBytes R m) :
    let s' := { s with pos := pos' }
    (arCtxMem cx s' ⋆ aigArraysMem s' rhs0 rhs1 olit ⋆
      netTablesMem s' bC roC rnC pC fC inC ouC ⋆
      gateScratchMem s' stkN stkP memoN memoV dense gsy gcl gch ⋆
      region (s'.w + s'.top) (s'.wlen.toNat - s'.top.toNat) ⋆ bytes art artBytes ⋆ R) m := by
  simp only [ArtLoopMem, aigArraysMem, netTablesMem, gateScratchMem, artPadRest, arrayPad_u32_eq,
    arrayPad_u8_eq] at hm ⊢
  rw [← addr_add_toNat s.w s.top, htop, hol, hb, hro, hrn, hp, hf, hin, hout]
  exact sep_cast hm (by ac_rfl)

private abbrev ArtTruePost (cx art : BitVec 64) (s : ArCtxState) (g : Aig)
    (rhs0 rhs1 olit : List (BitVec 32)) (artBytes : List UInt8) (R : Mem 64 → Prop)
    (ok : Bool) (m' : Mem 64) : Prop :=
  ok = true ∧ ∃ (s' : ArCtxState)
    (bindArr ruleOff ruleN partnerArr : List (BitVec 32)) (flippedArr : List (BitVec 8))
    (inNetArr outRefArr stkN stkP memoN : List (BitVec 32))
    (memoV dense : List (BitVec 64)) (gsy : List (BitVec 32)) (gcl gch : List (BitVec 64)),
    s'.w = s.w ∧ s'.wlen = s.wlen ∧ s'.art = art ∧ 4 * s'.nw.toNat = artBytes.length ∧
    s'.pos.toNat = 10 + s'.n_nets.toNat + s'.n_in.toNat + s'.n_out.toNat ∧
    s'.pos.toNat ≤ s'.nw.toNat ∧ s'.M = s.M ∧ s'.I = s.I ∧ s'.A = s.A ∧ s'.O = s.O ∧
    s'.n_nets.toNat ≤ 0x3FFFFFFF ∧
    s'.spec = BitVec.ofNat 32 (wordAt artBytes 2) ∧
    (s'.spec = 0#32 ∨ s'.spec = 1#32 ∨ s'.spec = 2#32) ∧
    s'.rs_n = 0#32 ∧ s'.rs_ptop = 0#64 ∧ s'.rs_cap = 0#32 ∧ s'.rs_pcap = 0#64 ∧
    s'.ptop = s.ptop ∧ s'.tn = s.tn ∧ s'.qn = s.qn ∧
    s'.pc = s.pc ∧ s'.tc = s.tc ∧ s'.cur_nr = s.cur_nr ∧
    s'.top.toNat =
      tablesEndTop g.ands.length g.outs.length s'.n_nets.toNat s'.n_in.toNat s'.n_out.toNat ∧
    s'.top.toNat ≤ s'.wlen.toNat ∧ TablesGeom s' g.ands.length g.outs.length
      s'.n_nets.toNat s'.n_in.toNat s'.n_out.toNat s'.top.toNat ∧
    MasksOk s'.modW s'.mlo s'.mhi ∧ BindRep s' g bindArr inNetArr outRefArr ∧
    bindArr.length = s'.n_nets.toNat ∧ ruleOff.length = s'.n_nets.toNat ∧
    ruleN.length = s'.n_nets.toNat ∧ partnerArr.length = s'.n_nets.toNat ∧
    flippedArr.length = s'.n_nets.toNat ∧ inNetArr.length = s'.n_in.toNat ∧
    outRefArr.length = s'.n_out.toNat ∧ stkN.length = arTTStk ∧ stkP.length = arTTStk ∧
    memoN.length = arTTMaxAnd ∧ memoV.length = arTTMaxAnd ∧ dense.length = 128 ∧
    gsy.length = 85 ∧ gcl.length = 16 ∧ gch.length = 16 ∧
    (∀ i < s'.n_nets.toNat, flippedArr.getD i 0#8 = 0#8) ∧
    (∀ σ : Nat → Bool, PartnerRep σ s'.n_nets.toNat partnerArr ∧
      RulesRep s'.modW σ s' ruleOff ruleN [] [] [] []) ∧
    (arCtxMem cx s' ⋆ aigArraysMem s' rhs0 rhs1 olit ⋆
      netTablesMem s' bindArr ruleOff ruleN partnerArr flippedArr inNetArr outRefArr ⋆
      gateScratchMem s' stkN stkP memoN memoV dense gsy gcl gch ⋆
      region (s'.w + s'.top) (s'.wlen.toNat - s'.top.toNat) ⋆ bytes art artBytes ⋆ R) m'

private abbrev ArtQSpec (cx art : BitVec 64) (s : ArCtxState) (g : Aig)
    (rhs0 rhs1 olit : List (BitVec 32)) (artBytes : List UInt8) (R : Mem 64 → Prop)
    (Q : Post [.bool]) : Prop :=
  ∀ (ok : Bool) (m' : Mem 64),
    ((ok = false ∧ ∃ s'' : ArCtxState, s''.w = s.w ∧ s''.wlen = s.wlen ∧
        (arCtxMem cx s'' ⋆ region (s.w + 776#64) (s.wlen.toNat - 776) ⋆
          bytes art artBytes ⋆ R) m') ∨
      ArtTruePost cx art s g rhs0 rhs1 olit artBytes R ok m') → Q (ok, ⟨⟩) m'

private structure ArtLoopCtx where
  cx : BitVec 64
  art : BitVec 64
  top15 : BitVec 64
  s : ArCtxState
  s2 : ArCtxState
  g : Aig
  rhs0 : List (BitVec 32)
  rhs1 : List (BitVec 32)
  olit : List (BitVec 32)
  stkN : List (BitVec 32)
  stkP : List (BitVec 32)
  memoN : List (BitVec 32)
  memoV : List (BitVec 64)
  dense : List (BitVec 64)
  gsy : List (BitVec 32)
  gcl : List (BitVec 64)
  gch : List (BitVec 64)
  artBytes : List UInt8
  R : Mem 64 → Prop
  Q : Post [.bool]
  h2 : BitVec 32
  h3 : BitVec 32
  h4 : BitVec 32
  h5 : BitVec 32
  hQ : ArtQSpec cx art s g rhs0 rhs1 olit artBytes R Q
  hrep : AigRep g rhs0 rhs1 olit
  hgeom : TablesGeom s2 g.ands.length g.outs.length h5.toNat h3.toNat h4.toNat top15.toNat
  hbounds : 776 ≤ top15.toNat ∧ top15.toNat ≤ s.wlen.toNat ∧ s.w.toNat + s.wlen.toNat < 2 ^ 64 ∧
    art.toNat + artBytes.length < 2 ^ 64 ∧ s.M.toNat ≤ 0x3FFFFFF0 ∧ s.M.toNat = g.M ∧
    s.I.toNat = g.I ∧ s.A.toNat = g.ands.length ∧ s.O.toNat = g.outs.length
  hs2_eqs : s2.w = s.w ∧ s2.wlen = s.wlen ∧ s2.art = art ∧ 4 * s2.nw.toNat = artBytes.length ∧
    4 * s2.nw.toNat ≤ artBytes.length ∧ 10 + h5.toNat + h3.toNat + h4.toNat ≤ s2.nw.toNat ∧
    s2.M = s.M ∧ s2.I = s.I ∧ s2.A = s.A ∧ s2.O = s.O ∧ s2.spec = h2 ∧ s2.n_in = h3 ∧
    s2.n_out = h4 ∧ s2.n_nets = h5 ∧ s2.rs_n = 0#32 ∧ s2.rs_ptop = 0#64 ∧
    s2.rs_cap = 0#32 ∧ s2.rs_pcap = 0#64 ∧ s2.ptop = s.ptop ∧ s2.tn = s.tn ∧
    s2.qn = s.qn ∧ s2.pc = s.pc ∧ s2.tc = s.tc ∧ s2.cur_nr = s.cur_nr ∧
    s2.top.toNat = top15.toNat ∧ MasksOk s2.modW s2.mlo s2.mhi
  hh_ok : h2 = BitVec.ofNat 32 (wordAt artBytes 2) ∧
    (h2 = 0#32 ∨ h2 = 1#32 ∨ h2 = 2#32) ∧
    (h2 ≠ 2#32 → h3.toNat % 2 = 0 ∧ 2 ≤ h3.toNat) ∧ h3 = s.I ∧
    h3.toNat ≤ 0x3FFFFFFF ∧
    (if h2 = 2#32 then h4.toNat % 2 = 0 ∧ 2 ≤ h4.toNat ∧ h4.toNat / 2 ≤ 128
     else 1 ≤ h4.toNat ∧ h4.toNat ≤ 128) ∧
    h4 = s.O ∧ h5.toNat ≤ 0x3FFFFFFF
  hslens : stkN.length = arTTStk ∧ stkP.length = arTTStk ∧ memoN.length = arTTMaxAnd ∧
    memoV.length = arTTMaxAnd ∧ dense.length = 128 ∧ gsy.length = 85 ∧ gcl.length = 16 ∧
    gch.length = 16

private theorem art_fail_ctx (C : ArtLoopCtx) (s' : ArCtxState)
    {bC roC rnC pC inC ouC : List (BitVec 32)} {fC : List (BitVec 8)} {m : Mem 64}
    (lb : bC.length = C.h5.toNat) (lro : roC.length = C.h5.toNat) (lrn : rnC.length = C.h5.toNat)
    (lp : pC.length = C.h5.toNat) (lf : fC.length = C.h5.toNat) (lin : inC.length = C.h3.toNat)
    (lou : ouC.length = C.h4.toNat) (hw' : s'.w = C.s.w) (hwl' : s'.wlen = C.s.wlen)
    (hm : ArtLoopMem C.cx C.art C.s2 s' bC roC rnC pC fC inC ouC C.olit C.rhs0 C.rhs1
      C.g.outs.length C.h5.toNat C.h3.toNat C.h4.toNat C.top15.toNat C.stkN C.stkP C.memoN C.memoV
      C.dense C.gsy C.gcl C.gch C.artBytes C.R m) : C.Q (false, ⟨⟩) m := by
  obtain ⟨h776, ht15, hfit, _⟩ := C.hbounds
  obtain ⟨hs2_w, hs2_wl, _⟩ := C.hs2_eqs
  obtain ⟨hsn, hsp, hmn, hmv, hd, hgy, hcl, hch⟩ := C.hslens
  have hm2 : (aigArraysMem C.s2 C.rhs0 C.rhs1 C.olit ⋆ netTablesMem C.s2 bC roC rnC pC fC inC ouC ⋆
      gateScratchMem C.s2 C.stkN C.stkP C.memoN C.memoV C.dense C.gsy C.gcl C.gch ⋆
      region (C.s2.w + BitVec.ofNat 64 C.top15.toNat) (C.s2.wlen.toNat - C.top15.toNat) ⋆
      (arCtxMem C.cx s' ⋆ bytes C.art C.artBytes ⋆ C.R)) m := by
    simp only [ArtLoopMem, aigArraysMem, netTablesMem, artPadRest, arrayPad_u32_eq,
      arrayPad_u8_eq] at hm ⊢
    rw [C.hrep.olit_len, lb, lro, lrn, lp, lf, lin, lou]; exact sep_cast hm (by ac_rfl)
  have hm3 := tables_collapse_avail C.hgeom h776 (by rw [hs2_wl]; exact ht15)
    (by rw [hs2_w, hs2_wl]; exact hfit) C.hrep.rhs0_len C.hrep.rhs1_len C.hrep.olit_len
    lb lro lrn lp lf lin lou hsn hsp hmn hmv hd hgy hcl hch hm2
  exact C.hQ false m (Or.inl ⟨rfl, s', hw', hwl',
    by rw [hs2_w, hs2_wl] at hm3; exact sep_cast hm3 (by ac_rfl)⟩)

private theorem art_build_true_post (C : ArtLoopCtx)
    {bC roC rnC pC inC ouC : List (BitVec 32)} {fC : List (BitVec 8)} {mC : Mem 64}
    {idx : BitVec 32}
    (lb : bC.length = C.h5.toNat) (lro : roC.length = C.h5.toNat) (lrn : rnC.length = C.h5.toNat)
    (lp : pC.length = C.h5.toNat) (lf : fC.length = C.h5.toNat) (linC : inC.length = C.h3.toNat)
    (louC : ouC.length = C.h4.toNat)
    (hinvA : ∀ k < C.h5.toNat, (bC.getD k 0#32 ≠ cNone32 → (bC.getD k 0#32).toNat ≤ 2 * C.g.M + 1) ∧
      rnC.getD k 0#32 = cNone32 ∧ pC.getD k 0#32 = cNone32 ∧ fC.getD k 0#8 = 0#8)
    (hinvB : ∀ k < C.h3.toNat,
      (C.h2 = 2#32 ∧ inC.getD k 0#32 = cNone32) ∨
      ((inC.getD k 0#32).toNat < C.h5.toNat ∧
       (bC.getD (inC.getD k 0#32).toNat 0#32).toNat = 2 * (k + 1)))
    (hinvC : ∀ k < C.h4.toNat,
      (C.h2 = 2#32 ∧ ouC.getD k 0#32 = cNone32 ∧ C.g.outs.getD k 0 ≤ 1) ∨
      (((ouC.getD k 0#32) >>> 1).toNat < C.h5.toNat ∧
       let bk := bC.getD ((ouC.getD k 0#32) >>> 1).toNat 0#32
       bk ≠ cNone32 ∧ (bk ^^^ ((ouC.getD k 0#32) &&& 1#32)).toNat = C.g.outs.getD k 0))
    (hjC_eq : idx.toNat = C.h4.toNat)
    (hmC : ArtLoopMem C.cx C.art C.s2
      { C.s2 with pos := BitVec.ofNat 64 (10 + C.h5.toNat + C.h3.toNat + idx.toNat) }
      bC roC rnC pC fC inC ouC C.olit C.rhs0 C.rhs1 C.g.outs.length C.h5.toNat C.h3.toNat
      C.h4.toNat C.top15.toNat C.stkN C.stkP C.memoN C.memoV C.dense C.gsy C.gcl C.gch
      C.artBytes C.R mC) : C.Q (true, ⟨⟩) mC := by
  obtain ⟨_, ht15, _, _, _, _, hI_eq, _, hO_eq⟩ := C.hbounds
  obtain ⟨hs2_w, hs2_wl, hs2_art, hs2_nw4, _, hs2_pos_lt, hs2_M, hs2_I, hs2_A, hs2_O,
    hs2_spec, hs2_nin, hs2_nout, hs2_nnets, hs2_rn, hs2_rpt, hs2_rc, hs2_rpc,
    hs2_ptop, hs2_tn, hs2_qn, hs2_pc, hs2_tc, hs2_cnr, hs2_top, hmasks2⟩ :=
    C.hs2_eqs
  obtain ⟨hh2_word, hspec, hh3_ev, hh3_I, _, hh4_bd, hh4_O, hh5_le⟩ := C.hh_ok
  obtain ⟨hsn, hsp, hmn, hmv, hd, hgy, hcl, hch⟩ := C.hslens
  let sFin : ArCtxState :=
    { C.s2 with pos := BitVec.ofNat 64 (10 + C.h5.toNat + C.h3.toNat + C.h4.toNat) }
  have hpos_eq : BitVec.ofNat 64 (10 + C.h5.toNat + C.h3.toNat + C.h4.toNat) =
      BitVec.ofNat 64 (10 + C.h5.toNat + C.h3.toNat + idx.toNat) := by rw [hjC_eq]
  have hm_fin := art_pack_pos
    (pos' := BitVec.ofNat 64 (10 + C.h5.toNat + C.h3.toNat + C.h4.toNat))
    C.s2 C.hrep.olit_len lb lro lrn lp lf linC louC hs2_top (by rwa [hpos_eq])
  have h10_lt : 10 + C.h5.toNat + C.h3.toNat + C.h4.toNat < 2 ^ 64 := by
    have := C.h5.isLt; have := C.h3.isLt; have := C.h4.isLt; omega
  have hsFin_pos :
      sFin.pos.toNat = 10 + sFin.n_nets.toNat + sFin.n_in.toNat + sFin.n_out.toNat := by
    change (BitVec.ofNat 64 (10 + C.h5.toNat + C.h3.toNat + C.h4.toNat)).toNat =
      10 + C.s2.n_nets.toNat + C.s2.n_in.toNat + C.s2.n_out.toNat
    rw [hs2_nnets, hs2_nin, hs2_nout, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h10_lt]
  have hsFin_top : sFin.top.toNat = tablesEndTop C.g.ands.length C.g.outs.length
      sFin.n_nets.toNat sFin.n_in.toNat sFin.n_out.toNat := by
    change C.s2.top.toNat = _; rw [hs2_top, hs2_nnets, hs2_nin, hs2_nout]; exact C.hgeom.top_eq
  have hsFin_geom : TablesGeom sFin C.g.ands.length C.g.outs.length
      sFin.n_nets.toNat sFin.n_in.toNat sFin.n_out.toNat sFin.top.toNat := by
    rw [show sFin.n_nets = C.h5 from hs2_nnets, show sFin.n_in = C.h3 from hs2_nin,
      show sFin.n_out = C.h4 from hs2_nout, show sFin.top.toNat = C.top15.toNat from hs2_top]
    exact ⟨C.hgeom.top_eq, C.hgeom.rhs0_eq, C.hgeom.rhs1_eq, C.hgeom.olit_eq, C.hgeom.bind_eq,
      C.hgeom.rule_off_eq, C.hgeom.rule_n_eq, C.hgeom.partner_eq, C.hgeom.flipped_eq,
      C.hgeom.in_net_eq, C.hgeom.out_ref_eq, C.hgeom.stk_n_eq, C.hgeom.stk_p_eq,
      C.hgeom.memo_n_eq, C.hgeom.memo_v_eq, C.hgeom.dense_eq, C.hgeom.gsy_eq, C.hgeom.gcl_eq,
      C.hgeom.gch_eq⟩
  have hI3 : C.h3.toNat = C.g.I := by rw [← hI_eq, hh3_I]
  have hO4 : C.h4.toNat = C.g.outs.length := by rw [← hO_eq, hh4_O]
  have hsFin_spec : sFin.spec = C.h2 := hs2_spec
  have hsFin_modW : sFin.modW = C.s2.modW := rfl
  have hbindRep : BindRep sFin C.g bC inC ouC :=
    ⟨by change C.s2.n_nets.toNat ≤ 0x3FFFFFFF; rw [hs2_nnets]; exact hh5_le,
     by change C.s2.n_nets.toNat ≤ bC.length; rw [hs2_nnets]; omega,
     fun v hv hne => (hinvA v (by rw [← hs2_nnets]; exact hv)).1 hne,
     by rw [hsFin_spec]; exact hspec,
     by change C.s2.n_in.toNat ≤ inC.length; rw [hs2_nin]; omega,
     by change C.s2.n_in.toNat = C.g.I; rw [hs2_nin]; exact hI3,
     fun hns => by rw [hsFin_spec] at hns; rw [← hI3]; exact hh3_ev hns,
     fun i hi => by
       rw [hs2_nin] at hi; rw [hsFin_spec, hs2_nnets]; exact hinvB i hi,
     by change C.s2.n_out.toNat ≤ ouC.length; rw [hs2_nout]; omega,
     by change C.s2.n_out.toNat = C.g.outs.length; exact hs2_nout ▸ hO4,
     fun hs2 => by
       rw [hsFin_spec] at hs2
       simp only [hs2, ↓reduceIte] at hh4_bd
       rw [← hO4]; exact hh4_bd.1,
     by
       have hmw_bd : 1 ≤ sFin.modW ∧ sFin.modW ≤ 128 := by
         dsimp only [ArCtxState.modW]
         rw [hsFin_spec]
         change 1 ≤ (if C.h2 = 2#32 then C.s2.n_out.toNat / 2 else C.s2.n_out.toNat) ∧
           (if C.h2 = 2#32 then C.s2.n_out.toNat / 2 else C.s2.n_out.toNat) ≤ 128
         rw [hs2_nout]
         by_cases hc2 : C.h2 = 2#32
         · simp only [hc2, ↓reduceIte] at hh4_bd ⊢; omega
         · simp only [hc2, ↓reduceIte] at hh4_bd ⊢; omega
       exact hmw_bd,
     fun j hj => by
       rw [hs2_nout] at hj; rw [hsFin_spec, hs2_nnets]; exact hinvC j hj⟩
  refine C.hQ true mC (Or.inr ⟨rfl, sFin, bC, roC, rnC, pC, fC, inC, ouC,
    C.stkN, C.stkP, C.memoN, C.memoV, C.dense, C.gsy, C.gcl, C.gch,
    hs2_w, hs2_wl, hs2_art, hs2_nw4, hsFin_pos,
    by rw [hsFin_pos, show sFin.n_nets = C.h5 from hs2_nnets, show sFin.n_in = C.h3 from hs2_nin,
      show sFin.n_out = C.h4 from hs2_nout]; exact hs2_pos_lt,
    hs2_M, hs2_I, hs2_A, hs2_O, by change C.s2.n_nets.toNat ≤ _; rw [hs2_nnets]; exact hh5_le,
    by rw [hsFin_spec]; exact hh2_word,
    by rw [hsFin_spec]; exact hspec,
    hs2_rn, hs2_rpt, hs2_rc, hs2_rpc, hs2_ptop, hs2_tn, hs2_qn, hs2_pc, hs2_tc, hs2_cnr, hsFin_top,
    by change C.s2.top.toNat ≤ C.s2.wlen.toNat; rw [hs2_top, hs2_wl]; exact ht15,
    hsFin_geom, hsFin_modW ▸ hmasks2, hbindRep,
    by rw [← hs2_nnets] at lb; exact lb, by rw [← hs2_nnets] at lro; exact lro,
    by rw [← hs2_nnets] at lrn; exact lrn, by rw [← hs2_nnets] at lp; exact lp,
    by rw [← hs2_nnets] at lf; exact lf, by rw [← hs2_nin] at linC; exact linC,
    by rw [← hs2_nout] at louC; exact louC, hsn, hsp, hmn, hmv, hd, hgy, hcl, hch,
    fun i hi => (hinvA i (by rw [← hs2_nnets]; exact hi)).2.2.2,
    fun σ => ⟨⟨by change C.s2.n_nets.toNat ≤ pC.length; rw [hs2_nnets]; omega,
      fun v hv hne => absurd (hinvA v (by rw [← hs2_nnets]; exact hv)).2.2.1 hne⟩,
      ⟨by change C.s2.n_nets.toNat ≤ roC.length; rw [hs2_nnets]; omega,
       by change C.s2.n_nets.toNat ≤ rnC.length; rw [hs2_nnets]; omega,
       by change C.s2.rs_n.toNat ≤ C.s2.rs_cap.toNat; simp [hs2_rn, hs2_rc],
       by change C.s2.rs_ptop.toNat ≤ C.s2.rs_pcap.toNat; simp [hs2_rpt, hs2_rpc],
       by change C.s2.rs_cap.toNat ≤ 0; simp [hs2_rc],
       by change C.s2.rs_cap.toNat ≤ 0; simp [hs2_rc],
       by change C.s2.rs_cap.toNat ≤ 0; simp [hs2_rc],
       by change C.s2.rs_pcap.toNat ≤ 0; simp [hs2_rpc],
       fun i hi => by change i < C.s2.rs_n.toNat at hi; simp [hs2_rn] at hi,
       fun v hv hne => absurd (hinvA v (by rw [← hs2_nnets]; exact hv)).2.1 hne⟩⟩, hm_fin⟩)

private theorem bv32_mul2_add1_i {i nIn : BitVec 32} (hn : nIn.toNat ≤ 0x3FFFFFFF)
    (hi : i.toNat < nIn.toNat) : (2#32 * (i + 1#32)).toNat = 2 * (i.toNat + 1) := by
  rw [BitVec.toNat_mul, bv32_add1_toNat hi, show (2#32 : BitVec 32).toNat = 2 from rfl,
    Nat.mod_eq_of_lt (by omega)]

private theorem bv32_shr1_toNat (r : BitVec 32) : (r >>> 1#32).toNat = r.toNat / 2 := by c0_bv_omega

private theorem art_aalloc_step (Γ : LeanQbe.T.Env)
    (hAlloc : ∀ xs m Q X, arAallocSpec xs m Q X → Γ "ar_aalloc" [i64, i64] [i64] xs m Q X)
    {cx nbytes : BitVec 64} {s : ArCtxState} {baseTop : Nat} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} (mkS : BitVec 64 → ArCtxState)
    (hmk : ∀ t, mkS t = { s with top := t })
    (hm : (arCtxMem cx s ⋆ (region (s.w + BitVec.ofNat 64 baseTop) (s.top.toNat - baseTop) ⋆
      (region (s.w + s.top) (s.wlen.toNat - s.top.toNat) ⋆ R))) m)
    (hwpos : 0 < s.w.toNat) (hfit : s.w.toNat + s.wlen.toNat < 2 ^ 64)
    (hbase : baseTop ≤ s.top.toNat) (htop : s.top.toNat ≤ s.wlen.toNat)
    (hk : ∀ (ret newTop : BitVec 64) (m' : Mem 64), baseTop ≤ newTop.toNat →
      newTop.toNat ≤ s.wlen.toNat → ((ret = 0#64 ∧ newTop = s.top) ∨ (ret ≠ 0#64 ∧
        ret = s.w + BitVec.ofNat 64 (align8 s.top.toNat) ∧
        newTop.toNat = align8 s.top.toNat + nbytes.toNat)) →
      (arCtxMem cx (mkS newTop) ⋆ (region (s.w + BitVec.ofNat 64 baseTop) (newTop.toNat - baseTop) ⋆
        (region (s.w + newTop) (s.wlen.toNat - newTop.toNat) ⋆ R))) m' → Q (ret, ⟨⟩) m') :
    Γ "ar_aalloc" [i64, i64] [i64] (cx, nbytes, ⟨⟩) m Q X :=
  ar_aalloc_seq_step Γ hAlloc hwpos hfit hbase htop hm fun ret newTop m' hb ht hdisj hm' => by
    rw [← hmk] at hm'; exact hk ret newTop m' hb ht hdisj hm'

private structure ArtLoopSt where
  ok : Bool
  idx : BitVec 32

private def artDv : (t : Ty) → Val t
  | .bool => false | .bits _ => 0 | .float _ => 0 | .pair a b => (artDv a, artDv b)
private def artDt : (rs : List Ty) → Tup Val rs
  | [] => ⟨⟩ | r :: rs => (artDv r, artDt rs)
private def artDc : (sig : List (List Ty)) → Tup Cont sig
  | [] => ⟨⟩ | _ :: ss => (fun _ _ => False, artDc ss)
private def artIsRet : {rs : List Ty} → Expr Val Cont rs → Bool
  | _, .ret _ => true | _, _ => false

private def artLoopWalk (stopAt : Nat) (exitNext : Bool) (ok0 : Val .bool) (idx0 : Val (.bits 32)) :
    Nat → Nat → Expr Val Cont [.bool] → Expr Val Cont [.bool]
  | 0, _, _ => .hlt
  | f + 1, nCalls, e => match e with
    | .let_ _ k => artLoopWalk stopAt exitNext ok0 idx0 f nCalls (k (artDt _))
    | .load _ _ k => artLoopWalk stopAt exitNext ok0 idx0 f nCalls (k (artDv _))
    | .store _ _ k => artLoopWalk stopAt exitNext ok0 idx0 f nCalls k
    | @Expr.call _ _ _ _ _ [.bool, .bits 32] _ k =>
      let res : Tup Val [.bool, .bits 32] := if nCalls == 9 then (ok0, 0#32, ⟨⟩) else artDt _
      artLoopWalk stopAt exitNext ok0 idx0 f (nCalls + 1) (k res)
    | .call _ _ k => artLoopWalk stopAt exitNext ok0 idx0 f (nCalls + 1) (k (artDt _))
    | .jnz _ t f' => if exitNext then artLoopWalk stopAt false ok0 idx0 f nCalls f'
      else if artIsRet t then artLoopWalk stopAt false ok0 idx0 f nCalls f'
      else artLoopWalk stopAt false ok0 idx0 f nCalls t
    | .group (sig := [[]]) bs _ => match bs (artDc _) with
      | .cons b _ => artLoopWalk stopAt exitNext ok0 idx0 f nCalls (b ⟨⟩)
    | .group (sig := [[.bits 32]]) bs _ => match bs (artDc _) with
      | .cons b _ => artLoopWalk stopAt exitNext ok0 idx0 f nCalls (b (0#32, ⟨⟩))
    | .group (sig := [[.bool, .bits 32]]) bs k => if stopAt == 0 then .group bs k
      else match bs (artDc _) with
        | .cons b _ => artLoopWalk (stopAt - 1) true ok0 idx0 f nCalls (b (ok0, idx0, ⟨⟩))
    | _ => .hlt

private abbrev artLoopExpr (stopAt : Nat) (cx : Val i64) (ok0 : Val .bool)
    (idx0 : Val (.bits 32)) : Expr Val Cont [.bool] :=
  artLoopWalk stopAt false ok0 idx0 500 0
    (ar_parse_art_header_and_tables_body Val Cont (cx, 0#64, 0#64, ⟨⟩))

set_option maxRecDepth 2048 in
private theorem art_loopC_wp (Γ : LeanQbe.T.Env)
    (hNW : ∀ xs m Q X, arNextWordSpec xs m Q X → Γ "ar_next_word" [i64] [.bool, i32] xs m Q X)
    (C : ArtLoopCtx) {X : XPost} {bC roC rnC pC inC outRefArr : List (BitVec 32)}
    {fC : List (BitVec 8)} {m : Mem 64} (okB : Bool) (idxB : BitVec 32)
    (lb : bC.length = C.h5.toNat) (lro : roC.length = C.h5.toNat) (lrn : rnC.length = C.h5.toNat)
    (lp : pC.length = C.h5.toNat) (lf : fC.length = C.h5.toNat)
    (linC : inC.length = C.h3.toNat) (lou0 : outRefArr.length = C.h4.toNat)
    (hinvA : ∀ k < C.h5.toNat, (bC.getD k 0#32 ≠ cNone32 → (bC.getD k 0#32).toNat ≤ 2 * C.g.M + 1) ∧
      rnC.getD k 0#32 = cNone32 ∧ pC.getD k 0#32 = cNone32 ∧ fC.getD k 0#8 = 0#8)
    (hinvB : ∀ k < C.h3.toNat,
      (C.h2 = 2#32 ∧ inC.getD k 0#32 = cNone32) ∨
      ((inC.getD k 0#32).toNat < C.h5.toNat ∧
       (bC.getD (inC.getD k 0#32).toNat 0#32).toNat = 2 * (k + 1)))
    (hm0 : ArtLoopMem C.cx C.art C.s2
      { C.s2 with pos := BitVec.ofNat 64 (10 + C.h5.toNat + C.h3.toNat) }
      bC roC rnC pC fC inC outRefArr C.olit C.rhs0 C.rhs1 C.g.outs.length C.h5.toNat C.h3.toNat
      C.h4.toNat C.top15.toNat C.stkN C.stkP C.memoN C.memoV C.dense C.gsy C.gcl C.gch
      C.artBytes C.R m) : wp Γ C.Q X (artLoopExpr 2 C.cx okB idxB) m := by
  obtain ⟨_, _, _, hart_fit, _, _, _, _, hO_eq⟩ := C.hbounds
  obtain ⟨hs2_w, hs2_wl, hs2_art, _, hs2_nw_le, _, _, _, _, _, hs2_spec, _, hs2_nout,
      hs2_nnets, _⟩ :=
    C.hs2_eqs
  obtain ⟨_, _, _, _, _, _, hh4_O, _⟩ := C.hh_ok
  have hltC : ∀ k < C.h4.toNat, 10 + C.h5.toNat + C.h3.toNat + k + 1 < 2 ^ 64 :=
    fun k hk => by omega
  refine c0_while_state (α := ArtLoopSt) (fun st => (st.ok, st.idx, ()))
    (fun st => C.h4.toNat - st.idx.toNat)
    (fun st mC => ∃ ouC : List (BitVec 32), st.idx.toNat ≤ C.h4.toNat ∧ ouC.length = C.h4.toNat ∧
      ArtLoopMem C.cx C.art C.s2
        { C.s2 with pos := BitVec.ofNat 64 (10 + C.h5.toNat + C.h3.toNat + st.idx.toNat) }
        bC roC rnC pC fC inC ouC C.olit C.rhs0 C.rhs1 C.g.outs.length C.h5.toNat C.h3.toNat
        C.h4.toNat C.top15.toNat C.stkN C.stkP C.memoN C.memoV C.dense C.gsy C.gcl C.gch
        C.artBytes C.R mC ∧
      (∀ k < st.idx.toNat,
        (C.h2 = 2#32 ∧ ouC.getD k 0#32 = cNone32 ∧ C.g.outs.getD k 0 ≤ 1) ∨
        (((ouC.getD k 0#32) >>> 1).toNat < C.h5.toNat ∧
         let bk := bC.getD ((ouC.getD k 0#32) >>> 1).toNat 0#32
         bk ≠ cNone32 ∧ (bk ^^^ ((ouC.getD k 0#32) &&& 1#32)).toNat = C.g.outs.getD k 0)))
    (fun JC hJC => by
      c0_hsteps_nogrp
      exact hJC ⟨okB, 0#32⟩ m
        ⟨outRefArr, by simp, lou0, by simpa using hm0, fun k hk => by simp at hk⟩)
    (fun JC stC mC ⟨ouC, hjC, louC, hmC, hinvC⟩ hJC => by
      dsimp only [ArtLoopMem] at hmC
      c0_hsplit
      · have hjC_lt : stC.idx.toNat < C.h4.toNat := by rw [hs2_nout] at hc; exact hc
        clear hc; c0_hsteps_nogrp
        c0_hcall (ar_nw_step Γ hNW { C.s2 with pos := BitVec.ofNat 64 (10 + C.h5.toNat +
          C.h3.toNat + stC.idx.toNat + 1) } hmC hs2_art hart_fit hs2_nw_le rfl
          (hltC _ hjC_lt) rfl)
        intro okC r mC' hokC_t hokC_f; c0_hsplit; rotate_left
        · c0_hstraight; obtain ⟨s', hw', hwl', hm'⟩ := hokC_f (by simp [hc])
          exact art_fail_ctx C s' lb lro lrn lp lf linC louC (hs2_w ▸ hw') (hs2_wl ▸ hwl') hm'
        obtain ⟨_, _, hmC_ok⟩ := hokC_t hc; clear hc
        let sC1 :=
          { C.s2 with pos := BitVec.ofNat 64 (10 + C.h5.toNat + C.h3.toNat + stC.idx.toNat + 1) }
        have hj64 : (stC.idx.setWidth 64).toNat = stC.idx.toNat := u64_setWidth_toNat stC.idx
        have holj : stC.idx.toNat < C.olit.length := by
          rw [C.hrep.olit_len, ← hO_eq, ← congrArg BitVec.toNat hh4_O]; exact hjC_lt
        have holj64 : (stC.idx.setWidth 64).toNat < C.olit.length := by rw [hj64]; exact holj
        have houj : stC.idx.toNat < ouC.length := by rw [louC]; exact hjC_lt
        have houj64 : (stC.idx.setWidth 64).toNat < ouC.length := by rw [hj64]; exact houj
        have hjC1 : (stC.idx + 1#32).toNat = stC.idx.toNat + 1 := bv32_add1_toNat hjC_lt
        refine wp_unroll_group fun _ _ => ?_
        c0_hsplit
        · have hr_none : r = cNone32 := hc; clear hc
          c0_hsplit
          · c0_hstraight
            exact art_fail_ctx C sC1 lb lro lrn lp lf linC louC hs2_w hs2_wl hmC_ok
          · have hspec2 : C.h2 = 2#32 := by rw [← hs2_spec]; exact hc
            clear hc; try dsimp only [ArCtxState.olit]
            c0_hsplit_nobound
            · c0_hstraight
              exact art_fail_ctx C sC1 lb lro lrn lp lf linC louC hs2_w hs2_wl hmC_ok
            · have hol_le1 : C.g.outs.getD stC.idx.toNat 0 ≤ 1 := by
                have hnot :
                    ¬ (1#32 : BitVec 32).toNat < (C.olit.getD stC.idx.toNat 0#32).toNat := by
                  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem holj, Option.getD_some]
                  exact hc
                have hle1 : (C.olit.getD stC.idx.toNat 0#32).toNat ≤ 1 := by
                  rw [show (1#32 : BitVec 32).toNat = 1 from rfl] at hnot; omega
                rw [← C.hrep.olit_eq stC.idx.toNat
                  (by rw [← hO_eq, ← congrArg BitVec.toNat hh4_O]; exact hjC_lt)]
                exact hle1
              clear hc; c0_hsteps_nogrp
              dsimp only [ArCtxState.out_ref] at hm; rw [hj64] at hm
              refine hJC ⟨okC, stC.idx + 1#32⟩ m
                (by dsimp only; rw [hjC1]; exact Nat.sub_lt_sub_left hjC_lt (Nat.lt_succ_self _))
                ⟨ouC.set stC.idx.toNat cNone32, by dsimp only; rw [hjC1]; exact hjC_lt,
                 by simp [louC],
                 by dsimp only [ArtLoopMem]; rw [hjC1]; simp only [Nat.add_assoc] at hm ⊢
                    exact sep_cast hm (by ac_rfl),
                 fun k hk => ?_⟩
              dsimp only at hk; rw [hjC1] at hk
              rw [getD_set_nat 0#32 ouC stC.idx.toNat cNone32 (by omega)]
              by_cases hlt : k < stC.idx.toNat
              · have hne : k ≠ stC.idx.toNat := by omega
                simp only [hne, ↓reduceIte]; exact hinvC k hlt
              · have heq : k = stC.idx.toNat := by omega
                simp only [heq, ↓reduceIte]; exact Or.inl ⟨hspec2, trivial, hol_le1⟩
        · clear hc
          c0_hsplit
          · c0_hstraight; exact art_fail_ctx C sC1 lb lro lrn lp lf linC louC hs2_w hs2_wl hmC_ok
          · have hr_lt : (r >>> 1#32).toNat < C.h5.toNat := by
              rw [hs2_nnets] at hc; rw [bv32_shr1_toNat]; try rw [Nat.shiftRight_eq_div_pow] at hc
              exact Nat.lt_of_not_le hc
            clear hc
            have hr64 : ((r >>> 1#32).setWidth 64).toNat = (r >>> 1#32).toNat :=
              u64_setWidth_toNat (r >>> 1#32)
            have hbr_len : (r >>> 1#32).toNat < bC.length := by rw [lb]; exact hr_lt
            have hbr_len2 : r.toNat / 2 < bC.length := by rw [← bv32_shr1_toNat]; exact hbr_len
            have hbr64 : ((r >>> 1#32).setWidth 64).toNat < bC.length := by rw [hr64]; exact hbr_len
            c0_hsplit_nobound
            · c0_hstraight; exact art_fail_ctx C sC1 lb lro lrn lp lf linC louC hs2_w hs2_wl hmC_ok
            have hb_ne : bC.getD (r >>> 1#32).toNat 0#32 ≠ cNone32 := by
              rw [bv32_shr1_toNat, List.getD_eq_getElem?_getD,
                List.getElem?_eq_getElem hbr_len2, Option.getD_some]; exact hc
            clear hc
            try dsimp only [ArCtxState.olit]
            c0_hsplit_nobound
            · c0_hstraight; exact art_fail_ctx C sC1 lb lro lrn lp lf linC louC hs2_w hs2_wl hmC_ok
            have hxor_eq : (bC.getD (r >>> 1#32).toNat 0#32 ^^^ (r &&& 1#32)) =
                C.olit.getD stC.idx.toNat 0#32 := by
              rw [bv32_shr1_toNat, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbr_len2,
                Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem holj,
                Option.getD_some]; exact hc
            clear hc
            c0_hsteps_nogrp
            dsimp only [ArCtxState.out_ref] at hm; rw [hj64] at hm
            refine hJC ⟨okC, stC.idx + 1#32⟩ m
              (by dsimp only; rw [hjC1]; exact Nat.sub_lt_sub_left hjC_lt (Nat.lt_succ_self _))
              ⟨ouC.set stC.idx.toNat r, by dsimp only; rw [hjC1]; exact hjC_lt, by simp [louC],
               by dsimp only [ArtLoopMem]; rw [hjC1]; simp only [Nat.add_assoc] at hm ⊢
                  exact sep_cast hm (by ac_rfl),
               fun k hk => ?_⟩
            dsimp only at hk; rw [hjC1] at hk; rw [getD_set_nat 0#32 ouC stC.idx.toNat r (by omega)]
            by_cases hlt : k < stC.idx.toNat
            · have hne : k ≠ stC.idx.toNat := by omega
              simp only [hne, ↓reduceIte]; exact hinvC k hlt
            · have heq : k = stC.idx.toNat := by omega
              simp only [heq, ↓reduceIte]; refine Or.inr ⟨hr_lt, hb_ne, ?_⟩
              rw [show (r >>> 1 : BitVec 32).toNat = (r >>> 1#32).toNat from rfl, hxor_eq]
              exact C.hrep.olit_eq stC.idx.toNat
                (by rw [← hO_eq, ← congrArg BitVec.toNat hh4_O]; exact hjC_lt)
      · have hjC_eq : stC.idx.toNat = C.h4.toNat := by
          rw [hs2_nout] at hc; exact Nat.le_antisymm hjC (Nat.le_of_not_lt hc)
        clear hc; c0_hsteps
        exact art_build_true_post C lb lro lrn lp lf linC louC hinvA hinvB
          (fun k hk => hinvC k (hjC_eq ▸ hk)) hjC_eq hmC)

set_option maxRecDepth 2048 in
private theorem art_loopB_wp (Γ : LeanQbe.T.Env)
    (hNW : ∀ xs m Q X, arNextWordSpec xs m Q X → Γ "ar_next_word" [i64] [.bool, i32] xs m Q X)
    (C : ArtLoopCtx) {X : XPost} {bC roC rnC pC inNetArr outRefArr : List (BitVec 32)}
    {fC : List (BitVec 8)} {m : Mem 64} (okA : Bool) (idxA : BitVec 32)
    (lb : bC.length = C.h5.toNat) (lro : roC.length = C.h5.toNat) (lrn : rnC.length = C.h5.toNat)
    (lp : pC.length = C.h5.toNat) (lf : fC.length = C.h5.toNat)
    (lin0 : inNetArr.length = C.h3.toNat) (lou0 : outRefArr.length = C.h4.toNat)
    (hinvA : ∀ k < C.h5.toNat, (bC.getD k 0#32 ≠ cNone32 → (bC.getD k 0#32).toNat ≤ 2 * C.g.M + 1) ∧
      rnC.getD k 0#32 = cNone32 ∧ pC.getD k 0#32 = cNone32 ∧ fC.getD k 0#8 = 0#8)
    (hm0 : ArtLoopMem C.cx C.art C.s2 { C.s2 with pos := BitVec.ofNat 64 (10 + C.h5.toNat) }
      bC roC rnC pC fC inNetArr outRefArr C.olit C.rhs0 C.rhs1 C.g.outs.length C.h5.toNat C.h3.toNat
      C.h4.toNat C.top15.toNat C.stkN C.stkP C.memoN C.memoV C.dense C.gsy C.gcl C.gch
      C.artBytes C.R m) : wp Γ C.Q X (artLoopExpr 1 C.cx okA idxA) m := by
  obtain ⟨_, _, _, hart_fit, _⟩ := C.hbounds
  obtain ⟨hs2_w, hs2_wl, hs2_art, _, hs2_nw_le, _, _, _, _, _, hs2_spec, hs2_nin, _,
      hs2_nnets, _⟩ :=
    C.hs2_eqs
  obtain ⟨_, _, _, _, hh3_le, _⟩ := C.hh_ok
  have hltB : ∀ k < C.h3.toNat, 10 + C.h5.toNat + k + 1 < 2 ^ 64 := fun k hk => by omega
  refine c0_while_state (α := ArtLoopSt) (fun st => (st.ok, st.idx, ()))
    (fun st => C.h3.toNat - st.idx.toNat)
    (fun st mB => ∃ inC : List (BitVec 32), st.idx.toNat ≤ C.h3.toNat ∧ inC.length = C.h3.toNat ∧
      ArtLoopMem C.cx C.art C.s2
        { C.s2 with pos := BitVec.ofNat 64 (10 + C.h5.toNat + st.idx.toNat) }
        bC roC rnC pC fC inC outRefArr C.olit C.rhs0 C.rhs1 C.g.outs.length C.h5.toNat C.h3.toNat
        C.h4.toNat C.top15.toNat C.stkN C.stkP C.memoN C.memoV C.dense C.gsy C.gcl C.gch
        C.artBytes C.R mB ∧
      (∀ k < st.idx.toNat,
        (C.h2 = 2#32 ∧ inC.getD k 0#32 = cNone32) ∨
        ((inC.getD k 0#32).toNat < C.h5.toNat ∧
         (bC.getD (inC.getD k 0#32).toNat 0#32).toNat = 2 * (k + 1))))
    (fun JB hJB => by
      c0_hsteps_nogrp
      exact hJB ⟨okA, 0#32⟩ m
        ⟨inNetArr, by simp, lin0, by simpa using hm0, fun k hk => by simp at hk⟩)
    (fun JB stB mB ⟨inC, hiB, linC, hmB, hinvB⟩ hJB => by
      dsimp only [ArtLoopMem] at hmB
      c0_hsplit
      · have hiB_lt : stB.idx.toNat < C.h3.toNat := by rw [hs2_nin] at hc; exact hc
        clear hc; c0_hsteps_nogrp
        c0_hcall (ar_nw_step Γ hNW
          { C.s2 with pos := BitVec.ofNat 64 (10 + C.h5.toNat + stB.idx.toNat + 1) }
          hmB hs2_art hart_fit hs2_nw_le rfl (hltB _ hiB_lt) rfl)
        intro okB v mB' hokB_t hokB_f; c0_hsplit; rotate_left
        · c0_hstraight; obtain ⟨s', hw', hwl', hm'⟩ := hokB_f (by simp [hc])
          exact art_fail_ctx C s' lb lro lrn lp lf linC lou0 (hs2_w ▸ hw') (hs2_wl ▸ hwl') hm'
        obtain ⟨_, _, hmB_ok⟩ := hokB_t hc; clear hc
        let sB1 := { C.s2 with pos := BitVec.ofNat 64 (10 + C.h5.toNat + stB.idx.toNat + 1) }
        have hini : stB.idx.toNat < inC.length := by rw [linC]; exact hiB_lt
        have hini64 : (stB.idx.setWidth 64).toNat < inC.length := by
          rw [u64_setWidth_toNat]; exact hini
        have hiB1 : (stB.idx + 1#32).toNat = stB.idx.toNat + 1 := bv32_add1_toNat hiB_lt
        refine wp_unroll_group fun _ _ => ?_
        c0_hsplit
        · have hv_none : v = cNone32 := hc; clear hc
          c0_hsteps_nogrp
          c0_hsplit
          · c0_hstraight; exact art_fail_ctx C sB1 lb lro lrn lp lf linC lou0 hs2_w hs2_wl hmB_ok
          · have hspec2 : C.h2 = 2#32 := by rw [← hs2_spec]; exact hc
            clear hc; c0_hstraight; try dsimp only; c0_hfast_nobound
            dsimp only [ArCtxState.in_net] at hm
            rw [u64_setWidth_toNat stB.idx] at hm
            refine hJB ⟨okB, stB.idx + 1#32⟩ m
              (by dsimp only; rw [hiB1]; exact Nat.sub_lt_sub_left hiB_lt (Nat.lt_succ_self _))
              ⟨inC.set stB.idx.toNat cNone32, by dsimp only; rw [hiB1]; exact hiB_lt,
               by simp [linC],
               by dsimp only [ArtLoopMem]; rw [hiB1, ← Nat.add_assoc]
                  exact sep_cast hm (by ac_rfl),
               fun k hk => ?_⟩
            dsimp only at hk; rw [hiB1] at hk
            rw [getD_set_nat 0#32 inC stB.idx.toNat cNone32 (by omega)]
            by_cases hlt : k < stB.idx.toNat
            · have hne : k ≠ stB.idx.toNat := by omega
              simp only [hne, ↓reduceIte]; exact hinvB k hlt
            · have heq : k = stB.idx.toNat := by omega
              simp only [heq, ↓reduceIte]; exact Or.inl ⟨hspec2, trivial⟩
        · clear hc
          c0_hsplit
          · c0_hstraight; exact art_fail_ctx C sB1 lb lro lrn lp lf linC lou0 hs2_w hs2_wl hmB_ok
          · have hv_lt : v.toNat < C.h5.toNat := by rw [hs2_nnets] at hc; exact Nat.lt_of_not_le hc
            clear hc; have hv64 : (v.setWidth 64).toNat = v.toNat := u64_setWidth_toNat v
            have hbv_len : v.toNat < bC.length := by rw [lb]; exact hv_lt
            have hbv64 : (v.setWidth 64).toNat < bC.length := by rw [hv64]; exact hbv_len
            c0_hstraight; try dsimp only; c0_hsplit_nobound
            · c0_hstraight; exact art_fail_ctx C sB1 lb lro lrn lp lf linC lou0 hs2_w hs2_wl hmB_ok
            have hbv_eq : bC.getD v.toNat 0#32 = 2#32 * (stB.idx + 1#32) := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbv_len, Option.getD_some]
              exact hc
            clear hc
            c0_hstraight; try dsimp only; c0_hfast_nobound
            dsimp only [ArCtxState.in_net] at hm
            rw [u64_setWidth_toNat stB.idx] at hm
            refine hJB ⟨okB, stB.idx + 1#32⟩ m
              (by dsimp only; rw [hiB1]; exact Nat.sub_lt_sub_left hiB_lt (Nat.lt_succ_self _))
              ⟨inC.set stB.idx.toNat v, by dsimp only; rw [hiB1]; exact hiB_lt, by simp [linC],
               by dsimp only [ArtLoopMem]; rw [hiB1, ← Nat.add_assoc]
                  exact sep_cast hm (by ac_rfl),
               fun k hk => ?_⟩
            dsimp only at hk; rw [hiB1] at hk; rw [getD_set_nat 0#32 inC stB.idx.toNat v (by omega)]
            by_cases hlt : k < stB.idx.toNat
            · have hne : k ≠ stB.idx.toNat := by omega
              simp only [hne, ↓reduceIte]; exact hinvB k hlt
            · have heq : k = stB.idx.toNat := by omega
              simp only [heq, ↓reduceIte]
              exact Or.inr ⟨hv_lt, by rw [hbv_eq, bv32_mul2_add1_i hh3_le hiB_lt]⟩
      · have hiB_eq : stB.idx.toNat = C.h3.toNat := by
          rw [hs2_nin] at hc; exact Nat.le_antisymm hiB (Nat.le_of_not_lt hc)
        clear hc; c0_hstraight; change wp Γ C.Q X (artLoopExpr 2 C.cx stB.ok stB.idx) mB
        exact art_loopC_wp Γ hNW C stB.ok stB.idx lb lro lrn lp lf linC lou0 hinvA
          (fun k hk => hinvB k (hiB_eq ▸ hk)) (by rw [hiB_eq] at hmB; simpa using hmB))

set_option maxRecDepth 2048 in
private theorem art_loopA_wp (Γ : LeanQbe.T.Env)
    (hNW : ∀ xs m Q X, arNextWordSpec xs m Q X → Γ "ar_next_word" [i64] [.bool, i32] xs m Q X)
    (C : ArtLoopCtx) {X : XPost}
    {bindArr ruleOff ruleN partnerArr inNetArr outRefArr : List (BitVec 32)}
    {flippedArr : List (BitVec 8)} {m : Mem 64} (ok9 : Bool)
    (hb0 : bindArr.length = C.h5.toNat) (hro0 : ruleOff.length = C.h5.toNat)
    (hrn0 : ruleN.length = C.h5.toNat) (hp0 : partnerArr.length = C.h5.toNat)
    (hf0 : flippedArr.length = C.h5.toNat) (lin0 : inNetArr.length = C.h3.toNat)
    (lou0 : outRefArr.length = C.h4.toNat)
    (hm0 : ArtLoopMem C.cx C.art C.s2 { C.s2 with pos := BitVec.ofNat 64 (10 + 0) }
      bindArr ruleOff ruleN partnerArr flippedArr inNetArr outRefArr C.olit C.rhs0 C.rhs1
      C.g.outs.length C.h5.toNat C.h3.toNat C.h4.toNat C.top15.toNat C.stkN C.stkP C.memoN C.memoV
      C.dense C.gsy C.gcl C.gch C.artBytes C.R m) :
    wp Γ C.Q X (artLoopExpr 0 C.cx ok9 0#32) m := by
  obtain ⟨_, _, _, hart_fit, hM_le, hM_eq, _⟩ := C.hbounds
  obtain ⟨hs2_w, hs2_wl, hs2_art, _, hs2_nw_le, _, hs2_M, _, _, _, _, _, _, hs2_nnets, _⟩ :=
    C.hs2_eqs
  have hltA : ∀ k < C.h5.toNat, 10 + k + 1 < 2 ^ 64 := fun k hk => by omega
  refine c0_while_state (α := ArtLoopSt) (fun st => (st.ok, st.idx, ()))
    (fun st => C.h5.toNat - st.idx.toNat)
    (fun st mA => ∃ (bC roC rnC pC : List (BitVec 32)) (fC : List (BitVec 8)),
      st.idx.toNat ≤ C.h5.toNat ∧ bC.length = C.h5.toNat ∧ roC.length = C.h5.toNat ∧
      rnC.length = C.h5.toNat ∧ pC.length = C.h5.toNat ∧ fC.length = C.h5.toNat ∧
      ArtLoopMem C.cx C.art C.s2 { C.s2 with pos := BitVec.ofNat 64 (10 + st.idx.toNat) }
        bC roC rnC pC fC inNetArr outRefArr C.olit C.rhs0 C.rhs1 C.g.outs.length C.h5.toNat
        C.h3.toNat C.h4.toNat C.top15.toNat C.stkN C.stkP C.memoN C.memoV C.dense C.gsy C.gcl
        C.gch C.artBytes C.R mA ∧
      (∀ k < st.idx.toNat, (bC.getD k 0#32 ≠ cNone32 → (bC.getD k 0#32).toNat ≤ 2 * C.g.M + 1) ∧
        rnC.getD k 0#32 = cNone32 ∧ pC.getD k 0#32 = cNone32 ∧ fC.getD k 0#8 = 0#8))
    (fun JA hJA => by
      c0_hsteps_nogrp
      exact hJA ⟨ok9, 0#32⟩ m ⟨bindArr, ruleOff, ruleN, partnerArr, flippedArr,
        by simp, hb0, hro0, hrn0, hp0, hf0, hm0, fun k hk => by simp at hk⟩)
    (fun JA stA mA ⟨bC, roC, rnC, pC, fC, hiA, lb, lro, lrn, lp, lf, hmA, hinvA⟩ hJA => by
      dsimp only [ArtLoopMem] at hmA
      c0_hsplit
      · have hiA_lt : stA.idx.toNat < C.h5.toNat := by rw [hs2_nnets] at hc; exact hc
        clear hc; c0_hsteps_nogrp
        c0_hcall (ar_nw_step Γ hNW { C.s2 with pos := BitVec.ofNat 64 (10 + stA.idx.toNat + 1) }
          hmA hs2_art hart_fit hs2_nw_le rfl (hltA _ hiA_lt) rfl)
        intro okA b mA' hokA_t hokA_f; c0_hsplit; rotate_left
        · c0_hsteps; obtain ⟨s', hw', hwl', hm'⟩ := hokA_f (by simp [hc])
          exact art_fail_ctx C s' lb lro lrn lp lf lin0 lou0 (hs2_w ▸ hw') (hs2_wl ▸ hwl') hm'
        obtain ⟨_, _, hmA_ok⟩ := hokA_t hc; clear hc; c0_hsteps_nogrp
        refine wp_join_group (fun _ mJ1 => (b ≠ cNone32 → b.toNat ≤ 2 * C.g.M + 1) ∧ mJ1 = mA' ∧
          ArtLoopMem C.cx C.art C.s2 { C.s2 with pos := BitVec.ofNat 64 (10 + stA.idx.toNat + 1) }
            bC roC rnC pC fC inNetArr outRefArr C.olit C.rhs0 C.rhs1 C.g.outs.length C.h5.toNat
            C.h3.toNat C.h4.toNat C.top15.toNat C.stkN C.stkP C.memoN C.memoV C.dense C.gsy C.gcl
            C.gch C.artBytes C.R mJ1) ?_ ?_
        · intro J1 _ mJ1 ⟨hb_ok, rfl, hmJ1⟩
          dsimp only [ArtLoopMem] at hmJ1
          have hbi : stA.idx.toNat < bC.length := by rw [lb]; exact hiA_lt
          have hrni : stA.idx.toNat < rnC.length := by rw [lrn]; exact hiA_lt
          have hroi : stA.idx.toNat < roC.length := by rw [lro]; exact hiA_lt
          have hpi : stA.idx.toNat < pC.length := by rw [lp]; exact hiA_lt
          have hfi : stA.idx.toNat < fC.length := by rw [lf]; exact hiA_lt
          have hfi64 : (stA.idx.setWidth 64).toNat < fC.length := by
            rw [u64_setWidth_toNat]; exact hfi
          c0_hfast_nobound; try dsimp only; c0_hfast_nobound; try dsimp only; c0_hfast_nobound
          try dsimp only; c0_hfast_nobound; try dsimp only; c0_hfast_nobound
          try dsimp only; c0_hfast_nobound
          have hiA1 : (stA.idx + 1#32).toNat = stA.idx.toNat + 1 := bv32_add1_toNat hiA_lt
          rw [u64_setWidth_toNat stA.idx] at hm
          dsimp only [ArCtxState.bind, ArCtxState.rule_off, ArCtxState.rule_n,
            ArCtxState.partner, ArCtxState.flipped] at hm
          refine hJA ⟨okA, stA.idx + 1#32⟩ m
            (by dsimp only; rw [hiA1]; exact Nat.sub_lt_sub_left hiA_lt (Nat.lt_succ_self _))
            ⟨bC.set stA.idx.toNat b, roC.set stA.idx.toNat 0#32, rnC.set stA.idx.toNat cNone32,
             pC.set stA.idx.toNat cNone32, fC.set stA.idx.toNat 0#8,
             by dsimp only; rw [hiA1]; exact hiA_lt,
             by simp [lb], by simp [lro], by simp [lrn], by simp [lp], by simp [lf],
             by
               dsimp only [ArtLoopMem]; rw [hiA1, ← Nat.add_assoc]
               exact sep_cast hm (by ac_rfl),
             fun k hk => ?_⟩
          dsimp only at hk; rw [hiA1] at hk
          rw [getD_set_nat 0#32 bC stA.idx.toNat b (by omega),
            getD_set_nat 0#32 rnC stA.idx.toNat cNone32 (by omega),
            getD_set_nat 0#32 pC stA.idx.toNat cNone32 (by omega),
            getD_set_nat 0#8 fC stA.idx.toNat 0#8 (by omega)]
          by_cases hlt : k < stA.idx.toNat
          · have hne : k ≠ stA.idx.toNat := by omega
            simp only [hne, ↓reduceIte]; exact hinvA k hlt
          · have heq : k = stA.idx.toNat := by omega
            simp only [heq, ↓reduceIte]; exact ⟨hb_ok, trivial, trivial, trivial⟩
        · intro J1 hJ1; c0_hsplit
          · have hb_ne : b ≠ cNone32 := hc; clear hc; c0_hsplit
            · c0_hstraight
              exact art_fail_ctx C
                { C.s2 with pos := BitVec.ofNat 64 (10 + stA.idx.toNat + 1) }
                lb lro lrn lp lf lin0 lou0 hs2_w hs2_wl hmA_ok
            · have hb_le : b.toNat ≤ 2 * C.g.M + 1 := by
                rw [hs2_M] at hc; rw [show (2 : BitVec 32).toNat = 2 from rfl,
                  show (1 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt
                    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hM_le) 1) (by decide))] at hc
                rw [← hM_eq]; exact Nat.le_of_not_lt hc
              c0_hstraight; exact hJ1 () mA' ⟨fun _ => hb_le, rfl, hmA_ok⟩
          · have hb_eq : b = cNone32 := hc; clear hc
            c0_hstraight; exact hJ1 () mA' ⟨fun h => absurd hb_eq h, rfl, hmA_ok⟩
      · have hiA_eq : stA.idx.toNat = C.h5.toNat := by
          rw [hs2_nnets] at hc; exact Nat.le_antisymm hiA (Nat.le_of_not_lt hc)
        clear hc; c0_hstraight; change wp Γ C.Q X (artLoopExpr 1 C.cx stA.ok stA.idx) mA
        exact art_loopB_wp Γ hNW C stA.ok stA.idx lb lro lrn lp lf lin0 lou0
          (fun k hk => hinvA k (hiA_eq ▸ hk)) (by rw [hiA_eq] at hmA; simpa using hmA))

local macro "art_nw_word" k:num knext:num Γ:ident hNW:ident s0:ident hart_fit:ident
    hnw_le:ident hm_pre_fail:ident okX:ident hX:ident mX:ident hm:ident hc:ident
    hmCur:ident : tactic =>
  `(tactic| (
    c0_hsteps_nogrp
    c0_hcall (ar_nw_step $Γ $hNW ($s0 $knext) $hmCur rfl $hart_fit ($hnw_le $k) rfl (by decide) rfl)
    intro $okX $hX $mX h_t h_f; c0_hsplit; rotate_left
    · c0_hsteps; obtain ⟨s', hw', hwl', hm'⟩ := h_f (by have h_eq := $hc; simp [h_eq])
      exact $hm_pre_fail s' hw' hwl' $mX hm'
    obtain ⟨_, _, $hm⟩ := h_t $hc; clear $hc))

local macro "art_hdr_chk" hm_pre_fail:ident s0:ident m9:ident hm:ident hc:ident p:tactic : tactic =>
  `(tactic| (c0_hsplit
             · c0_hsteps; exact $hm_pre_fail ($s0 10) rfl rfl $m9 $hm
             $p; clear $hc))

local macro "art_alloc" Γ:ident hAlloc:ident hm:ident hwpos:ident hfit:ident hbP:ident htP:ident
    pX:ident topX:ident hbX:ident htX:ident hX:ident mkS:term : tactic =>
  `(tactic| (
    c0_hsteps_nogrp
    c0_hcall (art_aalloc_step $Γ $hAlloc $mkS (fun _ => rfl) $hm $hwpos $hfit $hbP $htP)
    intro $pX $topX _ $hbX $htX $hX _))

local macro "art_alloc_ok" pX:ident hpX:ident htX:ident hX:ident s2Raw:ident top15:ident
    m:ident hm:ident hc:ident hb15:ident ht15:ident hm_mid_fail:ident : tactic =>
  `(tactic| (
    c0_hsplit
    · c0_hsteps; exact $hm_mid_fail $s2Raw $top15 $m rfl rfl $hb15 $ht15 $hm
    have hne : $pX ≠ 0#64 := (by have h_eq := $hc; simpa using h_eq); clear $hc
    have h_x := $hX; rcases h_x with ⟨rfl, _⟩ | ⟨_, $hpX, $htX⟩; · exact absurd rfl hne))

set_option maxRecDepth 2048 in
theorem ar_parse_art_header_and_tables_wp (Γ : LeanQbe.T.Env)
    (hNW : ∀ xs m Q X, arNextWordSpec xs m Q X → Γ "ar_next_word" [i64] [.bool, i32] xs m Q X)
    (hAlloc : ∀ xs m Q X, arAallocSpec xs m Q X → Γ "ar_aalloc" [i64, i64] [i64] xs m Q X) :
    ∀ xs m Q X, arParseArtHeaderAndTablesSpec xs m Q X →
      Func.wp Γ ar_parse_art_header_and_tables_body xs m Q X := by
  rintro ⟨cx, art, art_len, ⟨⟩⟩ m Q X ⟨s, g, rhs0, rhs1, olit, artBytes, R, hwpos, hfit, htop_pre,
    htop_le, hr0_ptr, hr1_ptr, hol_ptr, hrep, hM_le, hM_eq, hI_eq, hA_eq, hO_eq, hrn0, hrpt0, hrc0,
    hrpc0, hart_len, hart_fit, hm, hQ⟩
  have htop_fn : s.top.toNat =
      776 + align8 (4 * rhs0.length) + align8 (4 * rhs1.length) + 4 * olit.length := by
    rw [htop_pre, hrep.rhs0_len, hrep.rhs1_len, hrep.olit_len]
  have hr1_fn : s.rhs1 = s.w + BitVec.ofNat 64 (776 + align8 (4 * rhs0.length)) := by
    rw [hr1_ptr, hrep.rhs0_len]
  have hol_fn : s.olit =
      s.w + BitVec.ofNat 64 (776 + align8 (4 * rhs0.length) + align8 (4 * rhs1.length)) := by
    rw [hol_ptr, hrep.rhs0_len, hrep.rhs1_len]
  have hm_pre_fail : ∀ (s' : ArCtxState), s'.w = s.w → s'.wlen = s.wlen → ∀ m', (arCtxMem cx s' ⋆
      (bytes art artBytes ⋆ (arrayPad i32 s.rhs0 rhs0 ⋆ (arrayPad i32 s.rhs1 rhs1 ⋆
       (array (t := i32) s.olit olit ⋆ (region (s.w + s.top) (s.wlen.toNat - s.top.toNat) ⋆ R))))))
      m' → Q (false, ⟨⟩) m' := fun s' hw' hwl' m' hm' =>
    hQ false m' (Or.inl ⟨rfl, s', hw', hwl',
      art_pre_collapse hfit htop_fn htop_le hr0_ptr hr1_fn hol_fn hm'⟩)
  c0_hsplit
  · c0_hsteps; simp only [sep_assoc] at hm
    exact hm_pre_fail s rfl rfl m (sep_mono_r (fun _ => sep_pull5r) hm)
  · have h4nw : 4 * (art_len >>> 2).toNat = artBytes.length := by
      rw [← hart_len]; exact u64_and3_shr2 hc
    clear hc
    let s0 : Nat → ArCtxState :=
      fun k => { s with art := art, nw := art_len >>> 2, pos := BitVec.ofNat 64 k }
    c0_hsteps_nogrp; dsimp only at hm; simp only [sep_emp] at hm
    have hnw_le : ∀ k, 4 * (s0 k).nw.toNat ≤ artBytes.length := fun _ => by dsimp only [s0]; omega
    have hm0 : (arCtxMem cx (s0 0) ⋆ (bytes art artBytes ⋆ (arrayPad i32 s.rhs0 rhs0 ⋆
        (arrayPad i32 s.rhs1 rhs1 ⋆ (array (t := i32) s.olit olit ⋆
         (region (s.w + s.top) (s.wlen.toNat - s.top.toNat) ⋆ R)))))) m :=
      sep_mono_r (fun _ => sep_pull5r) hm
    art_nw_word 0 1 Γ hNW s0 hart_fit hnw_le hm_pre_fail ok0 h0 m0 hm hc hm0
    art_nw_word 1 2 Γ hNW s0 hart_fit hnw_le hm_pre_fail ok1 h1 m1 hm hc hm
    c0_hsteps_nogrp
    c0_hcall (ar_nw_step Γ hNW (s0 3) hm rfl hart_fit (hnw_le 2) rfl (by decide) rfl)
    intro ok2 h2 m2 h_t2 h_f2; c0_hsplit; rotate_left
    · c0_hsteps; obtain ⟨s', hw', hwl', hm'⟩ := h_f2 (by have h_eq := hc; simp [h_eq])
      exact hm_pre_fail s' hw' hwl' m2 hm'
    obtain ⟨_, hh2_word, hm⟩ := h_t2 hc; clear hc
    art_nw_word 3 4 Γ hNW s0 hart_fit hnw_le hm_pre_fail ok3 h3 m3 hm hc hm
    art_nw_word 4 5 Γ hNW s0 hart_fit hnw_le hm_pre_fail ok4 h4 m4 hm hc hm
    art_nw_word 5 6 Γ hNW s0 hart_fit hnw_le hm_pre_fail ok5 h5 m5 hm hc hm
    art_nw_word 6 7 Γ hNW s0 hart_fit hnw_le hm_pre_fail ok6 h6 m6 hm hc hm
    art_nw_word 7 8 Γ hNW s0 hart_fit hnw_le hm_pre_fail ok7 h7 m7 hm hc hm
    art_nw_word 8 9 Γ hNW s0 hart_fit hnw_le hm_pre_fail ok8 h8 m8 hm hc hm
    c0_hsteps_nogrp
    c0_hcall (ar_nw_step Γ hNW (s0 10) hm rfl hart_fit (hnw_le 9) rfl (by decide) rfl)
    intro ok9 h9 m9 hok9_t hok9_f; c0_hsplit; rotate_left
    · c0_hsteps; obtain ⟨s', hw', hwl', hm'⟩ := hok9_f (by simp [hc])
      exact hm_pre_fail s' hw' hwl' m9 hm'
    obtain ⟨hnw_gt9, _, hm⟩ := hok9_t hc; clear hc
    art_hdr_chk hm_pre_fail s0 m9 hm hc (skip)
    art_hdr_chk hm_pre_fail s0 m9 hm hc (skip)
    art_hdr_chk hm_pre_fail s0 m9 hm hc
      (have hspec : h2 = 0#32 ∨ h2 = 1#32 ∨ h2 = 2#32 := bv32_eq_0_1_2 hc)
    c0_hsteps_nogrp
    refine wp_join_group (fun (v : Tup Val [i32]) mW => mW = m9 ∧
      (h2 ≠ 2#32 → h3.toNat % 2 = 0 ∧ 2 ≤ h3.toNat) ∧ h3 = s.I ∧
      (if h2 = 2#32 then h4.toNat % 2 = 0 ∧ 2 ≤ h4.toNat ∧ h4.toNat / 2 ≤ 128
       else 1 ≤ h4.toNat ∧ h4.toNat ≤ 128) ∧ h4 = s.O ∧
      v.1.toNat = (if h2 = 2#32 then h4.toNat / 2 else h4.toNat)) ?_ ?_
    · rintro Jmw ⟨mw, ⟨⟩⟩ mW ⟨rfl, hh3_ev, hh3_I, hh4_bd, hh4_O, hmw_eq⟩
      have hmw_ge1 : 1 ≤ mw.toNat := by
        rw [hmw_eq]; by_cases hc2 : h2 = 2#32
        · simp only [hc2, ↓reduceIte] at hh4_bd ⊢; omega
        · simp only [hc2, ↓reduceIte] at hh4_bd ⊢; omega
      have hmw_le128 : mw.toNat ≤ 128 := by
        rw [hmw_eq]; by_cases hc2 : h2 = 2#32
        · simp only [hc2, ↓reduceIte] at hh4_bd ⊢; omega
        · simp only [hc2, ↓reduceIte] at hh4_bd ⊢; omega
      art_hdr_chk hm_pre_fail s0 mW hm hc (skip)
      art_hdr_chk hm_pre_fail s0 mW hm hc
        (have hh5_le : h5.toNat ≤ 0x3FFFFFFF := bv32_le_of_not_ugt hc (by decide))
      let mlo : BitVec 64 :=
        if mw.toNat ≥ 64 then ~~~0#64 else (1#64 <<< mw.setWidth 64) - 1#64
      let mhi : BitVec 64 := if mw.toNat ≥ 64 then
          if mw = 128#32 then ~~~0#64 else (1#64 <<< (mw - 64#32).setWidth 64) - 1#64
        else 0#64
      have hmasks : MasksOk mw.toNat mlo mhi := MasksOk.of_set_masks mw hmw_ge1 hmw_le128
      let s1 : ArCtxState :=
        { s with
          art := art, nw := art_len >>> 2, pos := 10#64, spec := h2, n_in := h3, n_out := h4,
          n_nets := h5, n_gates := h6, n_cones := h7, n_main := h8, mlo := mlo, mhi := mhi }
      have hmasks_s1 : MasksOk s1.modW s1.mlo s1.mhi := by
        have hmod : s1.modW = mw.toNat := by
          dsimp only [s1, ArCtxState.modW]; exact hmw_eq.symm
        rw [hmod]; exact hmasks
      c0_hsteps_nogrp
      refine wp_join_group (fun _ mJ => (arCtxMem cx s1 ⋆ (bytes art artBytes ⋆
        (arrayPad i32 s.rhs0 rhs0 ⋆ (arrayPad i32 s.rhs1 rhs1 ⋆ (array (t := i32) s.olit olit ⋆
         (region (s.w + s.top) (s.wlen.toNat - s.top.toNat) ⋆ R)))))) mJ) ?_ ?_
      · intro J _ mJ hmJ; c0_hsplit
        · c0_hsteps; exact hm_pre_fail s1 rfl rfl mJ hmJ
        · have hh3_le : h3.toNat ≤ 0x3FFFFFFF := by
            rw [hh3_I, hI_eq]; exact Nat.le_trans hrep.i_le_m (by omega)
          have hh4_le256 : h4.toNat ≤ 256 := by
            by_cases hc2 : h2 = 2#32
            · simp only [hc2, ↓reduceIte] at hh4_bd; omega
            · simp only [hc2, ↓reduceIte] at hh4_bd; omega
          have hnw10 : 10 ≤ s1.nw.toNat := by
            dsimp only [s1]; dsimp only [s0] at hnw_gt9; exact hnw_gt9
          have hpos_le : 10 + h5.toNat + h3.toNat + h4.toNat ≤ s1.nw.toNat := by
            dsimp only [s1] at hc; exact art_pos_sum_le hnw10 hh5_le hh3_le hh4_le256 hc
          clear hc
          have hmJ0 : (arCtxMem cx s1 ⋆
              (region (s.w + BitVec.ofNat 64 s.top.toNat) (s1.top.toNat - s.top.toNat) ⋆
               (region (s.w + s1.top) (s.wlen.toNat - s1.top.toNat) ⋆ (bytes art artBytes ⋆
                (arrayPad i32 s.rhs0 rhs0 ⋆ (arrayPad i32 s.rhs1 rhs1 ⋆
                 (array (t := i32) s.olit olit ⋆ R))))))) mJ := by
            have h1 : (arCtxMem cx s1 ⋆ (region (s.w + s1.top) (s.wlen.toNat - s1.top.toNat) ⋆
                (bytes art artBytes ⋆ (arrayPad i32 s.rhs0 rhs0 ⋆ (arrayPad i32 s.rhs1 rhs1 ⋆
                 (array (t := i32) s.olit olit ⋆ R)))))) mJ := by
              simpa only [sep_assoc] using sep_mono_r (fun _ => sep_pull5r) hmJ
            rwa [Nat.sub_self, region_zero, emp_sep]
          have hm_mid_fail : ∀ (s' : ArCtxState) (top' : BitVec 64) (m' : Mem 64), s'.w = s.w →
              s'.wlen = s.wlen → s.top.toNat ≤ top'.toNat → top'.toNat ≤ s.wlen.toNat →
              (arCtxMem cx s' ⋆
                (region (s.w + BitVec.ofNat 64 s.top.toNat) (top'.toNat - s.top.toNat) ⋆
                 (region (s.w + top') (s.wlen.toNat - top'.toNat) ⋆ (bytes art artBytes ⋆
                  (arrayPad i32 s.rhs0 rhs0 ⋆ (arrayPad i32 s.rhs1 rhs1 ⋆
                   (array (t := i32) s.olit olit ⋆ R))))))) m' → Q (false, ⟨⟩) m' :=
            fun s' top' m' hw' hwl' hbt hle hm' => hQ false m' (Or.inl ⟨rfl, s', hw', hwl',
              art_mid_collapse hfit htop_fn hbt hle hr0_ptr hr1_fn hol_fn hm'⟩)
          have htop_self : s.top.toNat ≤ s1.top.toNat := Nat.le_refl _
          art_alloc Γ hAlloc hmJ0 hwpos hfit htop_self htop_le pBind top1 hb1 ht1 hB
            (fun t => { s1 with top := t })
          art_alloc Γ hAlloc hm hwpos hfit hb1 ht1 pRoff top2 hb2 ht2 hRo
            (fun t => { s1 with top := t, bind := pBind })
          art_alloc Γ hAlloc hm hwpos hfit hb2 ht2 pRn top3 hb3 ht3 hRn
            (fun t => { s1 with top := t, bind := pBind, rule_off := pRoff })
          art_alloc Γ hAlloc hm hwpos hfit hb3 ht3 pPart top4 hb4 ht4 hP
            (fun t => { s1 with top := t, bind := pBind, rule_off := pRoff, rule_n := pRn })
          art_alloc Γ hAlloc hm hwpos hfit hb4 ht4 pFlip top5 hb5 ht5 hF (fun t =>
            { s1 with
              top := t, bind := pBind, rule_off := pRoff, rule_n := pRn, partner := pPart })
          art_alloc Γ hAlloc hm hwpos hfit hb5 ht5 pIn top6 hb6 ht6 hIn (fun t =>
            { s1 with
              top := t, bind := pBind, rule_off := pRoff, rule_n := pRn, partner := pPart,
              flipped := pFlip })
          art_alloc Γ hAlloc hm hwpos hfit hb6 ht6 pOut top7 hb7 ht7 hOu (fun t =>
            { s1 with
              top := t, bind := pBind, rule_off := pRoff, rule_n := pRn, partner := pPart,
              flipped := pFlip, in_net := pIn })
          art_alloc Γ hAlloc hm hwpos hfit hb7 ht7 pStkN top8 hb8 ht8 hSn (fun t =>
            { s1 with
              top := t, bind := pBind, rule_off := pRoff, rule_n := pRn, partner := pPart,
              flipped := pFlip, in_net := pIn, out_ref := pOut })
          art_alloc Γ hAlloc hm hwpos hfit hb8 ht8 pStkP top9 hb9 ht9 hSp (fun t =>
            { s1 with
              top := t, bind := pBind, rule_off := pRoff, rule_n := pRn, partner := pPart,
              flipped := pFlip, in_net := pIn, out_ref := pOut, stk_n := pStkN })
          art_alloc Γ hAlloc hm hwpos hfit hb9 ht9 pMemN top10 hb10 ht10 hMn (fun t =>
            { s1 with
              top := t, bind := pBind, rule_off := pRoff, rule_n := pRn, partner := pPart,
              flipped := pFlip, in_net := pIn, out_ref := pOut, stk_n := pStkN, stk_p := pStkP })
          art_alloc Γ hAlloc hm hwpos hfit hb10 ht10 pMemV top11 hb11 ht11 hMv (fun t =>
            { s1 with
              top := t, bind := pBind, rule_off := pRoff, rule_n := pRn, partner := pPart,
              flipped := pFlip, in_net := pIn, out_ref := pOut, stk_n := pStkN, stk_p := pStkP,
              memo_n := pMemN })
          art_alloc Γ hAlloc hm hwpos hfit hb11 ht11 pDense top12 hb12 ht12 hD (fun t =>
            { s1 with
              top := t, bind := pBind, rule_off := pRoff, rule_n := pRn, partner := pPart,
              flipped := pFlip, in_net := pIn, out_ref := pOut, stk_n := pStkN, stk_p := pStkP,
              memo_n := pMemN, memo_v := pMemV })
          art_alloc Γ hAlloc hm hwpos hfit hb12 ht12 pGsy top13 hb13 ht13 hGy (fun t =>
            { s1 with
              top := t, bind := pBind, rule_off := pRoff, rule_n := pRn, partner := pPart,
              flipped := pFlip, in_net := pIn, out_ref := pOut, stk_n := pStkN, stk_p := pStkP,
              memo_n := pMemN, memo_v := pMemV, dense := pDense })
          art_alloc Γ hAlloc hm hwpos hfit hb13 ht13 pGcl top14 hb14 ht14 hCl (fun t =>
            { s1 with
              top := t, bind := pBind, rule_off := pRoff, rule_n := pRn, partner := pPart,
              flipped := pFlip, in_net := pIn, out_ref := pOut, stk_n := pStkN, stk_p := pStkP,
              memo_n := pMemN, memo_v := pMemV, dense := pDense, gsy := pGsy })
          art_alloc Γ hAlloc hm hwpos hfit hb14 ht14 pGch top15 hb15 ht15 hCh (fun t =>
            { s1 with
              top := t, bind := pBind, rule_off := pRoff, rule_n := pRn, partner := pPart,
              flipped := pFlip, in_net := pIn, out_ref := pOut, stk_n := pStkN, stk_p := pStkP,
              memo_n := pMemN, memo_v := pMemV, dense := pDense, gsy := pGsy, gcl := pGcl })
          let s2Raw : ArCtxState :=
            { s1 with
              top := top15, bind := pBind, rule_off := pRoff, rule_n := pRn, partner := pPart,
              flipped := pFlip, in_net := pIn, out_ref := pOut, stk_n := pStkN, stk_p := pStkP,
              memo_n := pMemN, memo_v := pMemV, dense := pDense, gsy := pGsy, gcl := pGcl,
              gch := pGch }
          c0_hstraight; dsimp only at hm; change (arCtxMem cx s2Raw ⋆ _) m at hm
          art_alloc_ok pBind hpB_eq htB_eq hB s2Raw top15 m hm hc hb15 ht15 hm_mid_fail
          art_alloc_ok pRoff hpRo_eq htRo_eq hRo s2Raw top15 m hm hc hb15 ht15 hm_mid_fail
          art_alloc_ok pRn hpRn_eq htRn_eq hRn s2Raw top15 m hm hc hb15 ht15 hm_mid_fail
          art_alloc_ok pPart hpP_eq htP_eq hP s2Raw top15 m hm hc hb15 ht15 hm_mid_fail
          art_alloc_ok pFlip hpF_eq htF_eq hF s2Raw top15 m hm hc hb15 ht15 hm_mid_fail
          art_alloc_ok pIn hpIn_eq htIn_eq hIn s2Raw top15 m hm hc hb15 ht15 hm_mid_fail
          art_alloc_ok pOut hpOu_eq htOu_eq hOu s2Raw top15 m hm hc hb15 ht15 hm_mid_fail
          art_alloc_ok pStkN hpSn_eq htSn_eq hSn s2Raw top15 m hm hc hb15 ht15 hm_mid_fail
          art_alloc_ok pStkP hpSp_eq htSp_eq hSp s2Raw top15 m hm hc hb15 ht15 hm_mid_fail
          art_alloc_ok pMemN hpMn_eq htMn_eq hMn s2Raw top15 m hm hc hb15 ht15 hm_mid_fail
          art_alloc_ok pMemV hpMv_eq htMv_eq hMv s2Raw top15 m hm hc hb15 ht15 hm_mid_fail
          art_alloc_ok pDense hpD_eq htD_eq hD s2Raw top15 m hm hc hb15 ht15 hm_mid_fail
          art_alloc_ok pGsy hpGy_eq htGy_eq hGy s2Raw top15 m hm hc hb15 ht15 hm_mid_fail
          art_alloc_ok pGcl hpCl_eq htCl_eq hCl s2Raw top15 m hm hc hb15 ht15 hm_mid_fail
          art_alloc_ok pGch hpCh_eq htCh_eq hCh s2Raw top15 m hm hc hb15 ht15 hm_mid_fail
          have hh4_le3f : h4.toNat ≤ 0x3FFFFFFF := by omega
          have hgeomRaw : TablesGeom s2Raw g.ands.length g.outs.length
              h5.toNat h3.toNat h4.toNat top15.toNat := by
            refine art_build_geom htop_pre rfl hpB_eq htB_eq hpRo_eq htRo_eq hpRn_eq htRn_eq
              hpP_eq htP_eq hpF_eq htF_eq hpIn_eq htIn_eq hpOu_eq htOu_eq hpSn_eq htSn_eq
              hpSp_eq htSp_eq hpMn_eq htMn_eq hpMv_eq htMv_eq hpD_eq htD_eq hpGy_eq htGy_eq
              hpCl_eq htCl_eq hpCh_eq htCh_eq hr0_ptr hr1_ptr hol_ptr
              (u64_mul4_toNat hh5_le) (u64_mul4_toNat hh5_le) (u64_mul4_toNat hh5_le)
              (u64_mul4_toNat hh5_le) (u64_setWidth_toNat h5) (u64_mul4_toNat hh3_le)
              (u64_mul4_toNat hh4_le3f) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
              (try simp only [arTTStk, arTTMaxAnd]) <;> decide
          change (arCtxMem cx s2Raw ⋆ (region (s.w + BitVec.ofNat 64 s.top.toNat)
            (top15.toNat - s.top.toNat) ⋆ (region (s.w + top15) (s.wlen.toNat - top15.toNat) ⋆
            (bytes art artBytes ⋆ (arrayPad i32 s.rhs0 rhs0 ⋆ (arrayPad i32 s.rhs1 rhs1 ⋆
            (array (t := i32) s.olit olit ⋆ R))))))) m at hm
          rw [addr_add_toNat s.w s.top] at hm
          obtain ⟨bindArr, ruleOff, ruleN, partnerArr, flippedArr, inNetArr, outRefArr, stkN, stkP,
              memoN, memoV, dense, gsy, gcl, gch, hb_len, hro_len, hrn_len, hp_len, hf_len, hin_len,
              hout_len, hsn_len, hsp_len, hmn_len, hmv_len, hd_len, hgy_len, hcl_len, hch_len,
              hm_pop⟩ :=
            art_tables_pop_alloc (s0 := s) (s := s2Raw) hgeomRaw (by omega) htop_pre rfl rfl rfl rfl
              hol_ptr hrep.olit_len (art_pre_pop_shuffle hm)
          have hm_unpRaw := art_unpack_tables hrep.olit_len hb_len hro_len hrn_len hp_len hf_len
            hin_len hout_len (rfl : s2Raw.top.toNat = top15.toNat)
            (by simpa only [sep_assoc] using hm_pop)
          obtain ⟨s2, hs2_eq⟩ : ∃ x : ArCtxState, x = s2Raw := ⟨s2Raw, rfl⟩
          have hm_unp0 : ArtLoopMem cx art s2 { s2 with pos := BitVec.ofNat 64 (10 + 0) }
              bindArr ruleOff ruleN partnerArr flippedArr inNetArr outRefArr olit rhs0 rhs1
              g.outs.length h5.toNat h3.toNat h4.toNat top15.toNat stkN stkP memoN memoV dense gsy
              gcl gch artBytes R m := by
            rw [show { s2 with pos := BitVec.ofNat 64 (10 + 0) } = s2 by rw [hs2_eq],
              show top15.toNat = s2.top.toNat by rw [hs2_eq]]; exact hs2_eq ▸ hm_unpRaw
          let C : ArtLoopCtx :=
            ⟨cx, art, top15, s, s2, g, rhs0, rhs1, olit, stkN, stkP, memoN, memoV, dense, gsy, gcl,
              gch, artBytes, R, Q, h2, h3, h4, h5, hQ, hrep, hs2_eq ▸ hgeomRaw,
              ⟨by omega, ht15, hfit, hart_fit, by omega, hM_eq, hI_eq, hA_eq, hO_eq⟩,
              ⟨by rw [hs2_eq], by rw [hs2_eq], by rw [hs2_eq], by rw [hs2_eq]; exact h4nw,
               by rw [hs2_eq]; exact Nat.le_of_eq h4nw, by rw [hs2_eq]; exact hpos_le,
               by rw [hs2_eq], by rw [hs2_eq], by rw [hs2_eq], by rw [hs2_eq], by rw [hs2_eq],
               by rw [hs2_eq], by rw [hs2_eq], by rw [hs2_eq], by rw [hs2_eq]; exact hrn0,
               by rw [hs2_eq]; exact hrpt0, by rw [hs2_eq]; exact hrc0, by rw [hs2_eq]; exact hrpc0,
               by rw [hs2_eq], by rw [hs2_eq], by rw [hs2_eq],
               by rw [hs2_eq], by rw [hs2_eq], by rw [hs2_eq],
               by rw [hs2_eq], by rw [hs2_eq]; exact hmasks_s1⟩,
              ⟨hh2_word, hspec, hh3_ev, hh3_I, hh3_le, hh4_bd, hh4_O, hh5_le⟩,
              ⟨hsn_len, hsp_len, hmn_len, hmv_len, hd_len, hgy_len, hcl_len, hch_len⟩⟩
          c0_hstraight; change wp Γ C.Q X (artLoopExpr 0 C.cx ok9 0#32) m
          exact art_loopA_wp Γ hNW C ok9 hb_len hro_len hrn_len hp_len hf_len hin_len hout_len
            hm_unp0
      · intro J hJ; c0_hsteps_nogrp
        c0_hsplit
        · have h128 : mw = 128#32 := hc; clear hc; c0_hsteps; dsimp only [s0] at hm
          exact hJ () m (by
            dsimp only [s1, mlo, mhi]
            simp only [h128, show (128#32 : BitVec 32).toNat ≥ 64 from by decide, ↓reduceIte]
            exact hm)
        · have hne128 : mw ≠ 128#32 := hc; clear hc
          refine wp_unroll_group fun _ _ => ?_
          c0_hsplit
          · have hgt64 : 64 < mw.toNat := hc; clear hc
            have hge64 : mw.toNat ≥ 64 := by omega
            c0_hsteps; dsimp only [s0] at hm
            rw [bv64_shl_sub64_lt128 hge64 hmw_le128 hne128] at hm
            exact hJ () m (by
              dsimp only [s1, mlo, mhi]
              simp only [hge64, ↓reduceIte, hne128]; exact hm)
          · have hle64 : mw.toNat ≤ 64 := Nat.not_lt.mp hc; clear hc
            refine wp_unroll_group fun _ _ => ?_
            c0_hsplit
            · have heq64 : mw = 64#32 := hc; clear hc
              have hge64 : mw.toNat ≥ 64 := by rw [heq64]; decide
              c0_hsteps; dsimp only [s0] at hm
              exact hJ () m (by
                dsimp only [s1, mlo, mhi]
                simp only [hge64, ↓reduceIte, show mw ≠ 128#32 by rw [heq64]; decide]
                rw [heq64]; simpa using hm)
            · have hne64 : mw ≠ 64#32 := hc; clear hc
              have hlt64 : mw.toNat < 64 := by
                have hne' : mw.toNat ≠ 64 := fun h =>
                  hne64 (BitVec.eq_of_toNat_eq (by simpa using h))
                omega
              have hnot64 : ¬ mw.toNat ≥ 64 := by omega
              c0_hsteps; dsimp only [s0] at hm
              rw [bv64_shl_setWidth_lt64 hlt64] at hm
              exact hJ () m (by
                dsimp only [s1, mlo, mhi]; simp only [hnot64, ↓reduceIte]; exact hm)
    · intro Jmw hJmw
      c0_hsplit
      · have h2eq : h2 = 2#32 := hc; clear hc
        art_hdr_chk hm_pre_fail s0 m9 hm hc (have hh3_I : h3 = s.I := hc)
        art_hdr_chk hm_pre_fail s0 m9 hm hc (have hh4_O : h4 = s.O := hc)
        art_hdr_chk hm_pre_fail s0 m9 hm hc
          (have hh4_ge2 : 2 ≤ h4.toNat := bv32_ge_of_not_ult hc (by decide))
        art_hdr_chk hm_pre_fail s0 m9 hm hc (have hh4_even : h4.toNat % 2 = 0 := u32_and1_even hc)
        art_hdr_chk hm_pre_fail s0 m9 hm hc
          (have hh4_half_le : h4.toNat / 2 ≤ 128 := by
            simp only [Nat.pow_one] at hc
            change ¬ (128 : Nat) < h4.toNat / 2 at hc
            omega)
        c0_hsteps; refine hJmw (h4 >>> 1#32, ⟨⟩) m9 ⟨rfl, ?_⟩
        refine ⟨fun h => absurd h2eq h, hh3_I, by simp [h2eq, hh4_even, hh4_ge2, hh4_half_le],
          hh4_O, ?_⟩
        simp only [h2eq, ↓reduceIte]; exact bv32_shr1_toNat h4
      · have h2ne : h2 ≠ 2#32 := hc; clear hc
        art_hdr_chk hm_pre_fail s0 m9 hm hc (have hh3_I : h3 = s.I := hc)
        art_hdr_chk hm_pre_fail s0 m9 hm hc (have hh3_even : h3.toNat % 2 = 0 := u32_and1_even hc)
        art_hdr_chk hm_pre_fail s0 m9 hm hc
          (have hh3_ge2 : 2 ≤ h3.toNat := bv32_ge_of_not_ult hc (by decide))
        art_hdr_chk hm_pre_fail s0 m9 hm hc (have hh4_O : h4 = s.O := hc)
        art_hdr_chk hm_pre_fail s0 m9 hm hc
          (have hh4_ge1 : 1 ≤ h4.toNat := bv32_ge_of_not_ult hc (by decide))
        art_hdr_chk hm_pre_fail s0 m9 hm hc
          (have hh4_le128 : h4.toNat ≤ 128 := bv32_le_of_not_ugt hc (by decide))
        c0_hsteps; refine hJmw (h4, ⟨⟩) m9 ⟨rfl, ?_⟩
        exact ⟨fun _ => ⟨hh3_even, hh3_ge2⟩, hh3_I, by simp [h2ne, hh4_ge1, hh4_le128],
          hh4_O, by simp [h2ne]⟩

end

end LeanQbe.T.Examples.Arisca.Proof
