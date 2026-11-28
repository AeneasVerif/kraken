/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Compact.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts4
public import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1

/-!
# Compaction Invariance & Heap Framing Helpers (`Proof.Compact.Inv`)

Pure Layer-A + `FullWitnessInv` + `FullMem` helpers for `Kissat.Proof.Compact`:
1. BitVec & pure list arithmetic bridges (`cmp_*` / `Spec.CompactBijOk`).
2. Binary watch slice compaction (`WatchSliceOk_step`, `Spec.CompactPreBinSliceOk`,
   `Spec.CompactUnmapBinSliceOk`, `Spec.CompactUnmapBinsOk`, loop-2/3 `wvec` pack helpers).
3. Contiguous arena prefix compaction (`CompactArenaPrefix`, `Spec.CompactArenaOk`).
4. Post-compaction `stateClausesCore` builder (`fullWitnessInv_compact_build`,
   `fullWitnessInv_compact_unsat`).
5. `FullMem` / `FullM6HdrMem` focus & unfocus primitives (`focus_vmtf_arrays`,
   `focus_heap_arrays`, `FullM6HdrCfgOk_of_compat`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Compact

open Std Std.Sat
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Compact.Spec
open Kraken.Bedrock2.Test

public section

/-! ## 1. BitVec, Pure Clause & `CompactBijOk` Helpers -/

theorem cmp_bv8_sext32_eq0 {x : BitVec 8} (h : x.signExtend 32 = 0#32) : x = 0#8 := by
  have h0 : (x.signExtend 32).toInt = (0#32 : BitVec 32).toInt := congrArg BitVec.toInt h
  rw [BitVec.toInt_signExtend_of_le (by decide)] at h0
  exact BitVec.eq_of_toInt_eq h0

theorem cmp_bv32_add1 {x : BitVec 32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + (1 : BitVec 32)).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

theorem cmp_bv64_add1 {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + (1 : BitVec 64)).toNat = x.toNat + 1 :=
  bv64_add_small_eq (by simp; omega)

theorem cmp_bv64_add2 {x : BitVec 64} (h : x.toNat + 2 < 2 ^ 64) :
    (x + (2 : BitVec 64)).toNat = x.toNat + 2 :=
  bv64_add_small_eq (by simp; omega)

theorem cmp_bv64_add3 {x : BitVec 64} (h : x.toNat + 3 < 2 ^ 64) :
    (x + (3 : BitVec 64)).toNat = x.toNat + 3 :=
  bv64_add_small_eq (by simp; omega)

theorem cmp_bv64_add4 {x : BitVec 64} (h : x.toNat + 4 < 2 ^ 64) :
    (x + (4 : BitVec 64)).toNat = x.toNat + 4 :=
  bv64_add_small_eq (by simp; omega)

theorem cmp_bv64_shl2_toNat {x : BitVec 64} (h : 4 * x.toNat < 2 ^ 64) :
    (x <<< (2 : Nat)).toNat = 4 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show 2 ^ 2 = 4 from rfl, Nat.mul_comm,
    Nat.mod_eq_of_lt h]

theorem cmp_bv64_add3_zext_toNat {x : BitVec 64} {k : BitVec 32}
    (h : x.toNat + 3 + k.toNat < 2 ^ 64) :
    (x + (3 : BitVec 64) + k.setWidth 64).toNat = x.toNat + 3 + k.toNat := by
  have hk : (k.setWidth 64).toNat = k.toNat := zext_toNat _ (by decide)
  have h3 : (x + (3 : BitVec 64)).toNat = x.toNat + 3 := cmp_bv64_add3 (by omega)
  rw [BitVec.toNat_add, h3, hk, Nat.mod_eq_of_lt h]

theorem cmp_bv_sub_ofNat {a b : Nat} (hle : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  have ha' : (BitVec.ofNat 64 a).toNat = a := bv64_ofNat_toNat ha
  have hb' : (BitVec.ofNat 64 b).toNat = b := bv64_ofNat_toNat (by omega)
  rw [bv64_sub_small_eq (by rw [ha', hb']; exact hle), ha', hb',
    bv64_ofNat_toNat (by omega)]

theorem cmp_bv32_two_mul_or_one (nv : Nat) :
    (BitVec.ofNat 32 (2 * nv) ||| 1#32) = BitVec.ofNat 32 (2 * nv + 1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_ofNat, Nat.testBit]
  cases i with
  | zero => simp [hi]
  | succ j =>
    have h1 : 1 >>> (j + 1) % 2 = 0 := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (Nat.one_lt_two_pow (by omega)),
        Nat.zero_mod]
    have h2 : (2 * nv + 1) >>> (j + 1) = (2 * nv) >>> (j + 1) := by
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.pow_succ',
        ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
        show (2 * nv + 1) / 2 = (2 * nv) / 2 by omega]
    simp [h1, h2]

theorem cmp_bv32_lit_pack {nv : Nat} (hnv : nv < 2 ^ 30) (ot : BitVec 32) :
    ((BitVec.ofNat 32 nv <<< 1#32) ||| (ot &&& 1#32)).toNat = 2 * nv + ot.toNat % 2 := by
  have ha : (ot &&& 1#32) = if ot.toNat % 2 = 0 then 0#32 else 1#32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (1#32).toNat = 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod ot.toNat 1]
    rcases Nat.mod_two_eq_zero_or_one ot.toNat with hm | hm <;> simp [hm]
  have hs : (BitVec.ofNat 32 nv <<< 1#32) = BitVec.ofNat 32 (2 * nv) := by
    apply BitVec.eq_of_toNat_eq
    change (BitVec.ofNat 32 nv <<< (1 : Nat)).toNat = (BitVec.ofNat 32 (2 * nv)).toNat
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, bv32_ofNat_toNat (n := nv) (by omega),
      bv32_ofNat_toNat (n := 2 * nv) (by omega), show 2 ^ 1 = 2 from rfl, Nat.mul_comm nv 2,
      Nat.mod_eq_of_lt (by omega : 2 * nv < 2 ^ 32)]
  rw [ha, hs]
  rcases Nat.mod_two_eq_zero_or_one ot.toNat with hm | hm
  · simp only [hm, ↓reduceIte, BitVec.or_zero]
    exact bv32_ofNat_toNat (n := 2 * nv) (by omega)
  · simp only [hm, Nat.one_ne_zero, ↓reduceIte, cmp_bv32_two_mul_or_one]
    exact bv32_ofNat_toNat (n := 2 * nv + 1) (by omega)

theorem cmp_bv32_bin_word_props {l : BitVec 32} (hl : l.toNat < 0x7FFFFFFF) :
    ((l &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&& 0x80000000#32 ≠ 0#32 ∧
    ((l &&& 0x7FFFFFFF#32) ||| 0x80000000#32) ≠ 0xFFFFFFFF#32 ∧
    (((l &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&& 0x7FFFFFFF#32).toNat = l.toNat := by
  have hm : (l &&& 0x7FFFFFFF#32) = l := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  rw [hm]
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    have hbit := congrArg (fun x : BitVec 32 => x.getLsbD 31) hz
    have h31 : (0x80000000#32).getLsbD 31 = true := rfl
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_zero, h31, Bool.or_true,
      Bool.and_true] at hbit
    exact absurd hbit (by decide)
  · intro heq
    have hmask := congrArg (· &&& 0x7FFFFFFF#32) heq
    rw [BitVec.and_or_distrib_right, hm,
      show (0x80000000#32 &&& 0x7FFFFFFF#32 : BitVec 32) = 0#32 from rfl, BitVec.or_zero,
      show (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32 : BitVec 32) = 0x7FFFFFFF#32 from rfl] at hmask
    subst hmask; revert hl; decide
  · rw [BitVec.and_or_distrib_right, hm,
      show (0x80000000#32 &&& 0x7FFFFFFF#32 : BitVec 32) = 0#32 from rfl, BitVec.or_zero]

theorem cmp_bv32_clear_shrk_rsn (hdr : BitVec 32) (hng : (hdr &&& 0x00080000#32) = 0#32) :
    let h' := hdr &&& ~~~(0x00800000#32 ||| 0x00200000#32)
    (h' &&& 0x00800000#32) = 0#32 ∧ (h' &&& 0x00080000#32) = 0#32 := by
  intro h'
  dsimp only [h']
  constructor
  · rw [BitVec.and_assoc,
      show (~~~(0x00800000#32 ||| 0x00200000#32) &&& 0x00800000#32 : BitVec 32) = 0#32 from rfl,
      BitVec.and_zero]
  · rw [BitVec.and_assoc,
      show (~~~(0x00800000#32 ||| 0x00200000#32) &&& 0x00080000#32 : BitVec 32) =
        0x00080000#32 from rfl]
    exact hng

theorem cmp_drop_take_succ {α : Type} {xs : List α} {off n : Nat}
    (hlt : off + n < xs.length) :
    (xs.drop off).take (n + 1) = (xs.drop off).take n ++ [xs[off + n]'hlt] := by
  rw [List.take_add_one, List.getElem?_drop]
  simp [List.getElem?_eq_getElem hlt]

theorem cmp_entails_of_mem_or_false {F : CNF Nat} {xs ys : List Nat}
    (hx : F.EntailsClause (cnfClause xs))
    (hmem : ∀ x ∈ xs, x ∈ ys ∨ F.EntailsClause (cnfClause [x ^^^ 1])) :
    F.EntailsClause (cnfClause ys) := by
  rw [CNF.entails_clause_def] at *
  intro α hα
  rw [clause_sat_cnfClause_iff]
  have hxs := (clause_sat_cnfClause_iff α xs).mp (hx α hα)
  obtain ⟨l, hl, hsat_l⟩ := hxs
  rcases hmem l hl with hiny | hfals
  · exact ⟨l, hiny, hsat_l⟩
  · have hns := (sat_cnfClause_singleton α (l ^^^ 1)).mp (CNF.entails_clause_def.mp hfals α hα)
    have hsat_s : (cnfClause [l]).Sat α := (sat_cnfClause_singleton α l).mpr hsat_l
    have hneg : (cnfClause [litNeg l]).Sat α := by simpa [litNeg] using hns
    exact absurd hsat_s ((sat_cnfClause_litNeg_iff α l).mp hneg)

theorem cmp_unsat_of_entails_nil {F : CNF Nat} (h : F.EntailsClause (cnfClause [])) :
    F.Unsat :=
  unsat_of_entails_nil h

theorem compactUnmapLit_pair {inv : List (BitVec 32)} {nv ov p : Nat}
    (h : (inv[nv]?.getD 0#32).toNat = ov) (hp : p < 2) :
    compactUnmapLit inv (2 * nv + p) = 2 * ov + p := by
  unfold compactUnmapLit
  rw [show (2 * nv + p) / 2 = nv by omega, show (2 * nv + p) % 2 = p by omega, h]

theorem compactUnmapLit_div2 {inv : List (BitVec 32)} (l : Nat) :
    compactUnmapLit inv l / 2 = (inv[l / 2]?.getD 0#32).toNat := by
  unfold compactUnmapLit; have := Nat.mod_lt l (by decide : 0 < 2); omega

theorem compactUnmapLit_mod2 {inv : List (BitVec 32)} (l : Nat) :
    compactUnmapLit inv l % 2 = l % 2 := by
  unfold compactUnmapLit; have := Nat.mod_lt l (by decide : 0 < 2); omega

theorem compactUnmapLit_xor1 {inv : List (BitVec 32)} (l : Nat) :
    compactUnmapLit inv (l ^^^ 1) = compactUnmapLit inv l ^^^ 1 := by
  unfold compactUnmapLit
  rw [nat_xor1_div2, nat_xor1_mod2, nat_xor1_eq]
  rcases Nat.mod_two_eq_zero_or_one l with h0 | h1
  · simp [h0]
  · simp [h1]

theorem Spec.CompactBijOk.inv_inj {old_cv ncv : Nat} {vals : List (BitVec 8)}
    {map inv : List (BitVec 32)} (h : CompactBijOk old_cv ncv vals map inv)
    {nv1 nv2 : Nat} (h1 : nv1 < ncv) (h2 : nv2 < ncv)
    (heq : (inv[nv1]?.getD 0#32).toNat = (inv[nv2]?.getD 0#32).toNat) : nv1 = nv2 := by
  obtain ⟨ov1, hov1, _, _, hi1, hm1⟩ := h.inv_ok nv1 h1
  obtain ⟨ov2, hov2, _, _, hi2, hm2⟩ := h.inv_ok nv2 h2
  have hlt1 : ov1 < 2 ^ 32 := by have := h.old_cv_lt; omega
  have hlt2 : ov2 < 2 ^ 32 := by have := h.old_cv_lt; omega
  rw [hi1, hi2, Option.getD_some, Option.getD_some, bv32_ofNat_toNat hlt1,
    bv32_ofNat_toNat hlt2] at heq
  subst heq
  rw [hm1] at hm2
  have htn := congrArg BitVec.toNat (Option.some.inj hm2)
  have hnl1 : nv1 < 2 ^ 32 := by have := h.ncv_le; have := h.old_cv_lt; omega
  have hnl2 : nv2 < 2 ^ 32 := by have := h.ncv_le; have := h.old_cv_lt; omega
  rwa [bv32_ofNat_toNat hnl1, bv32_ofNat_toNat hnl2] at htn

theorem compactUnmapLit_inj {old_cv ncv : Nat} {vals : List (BitVec 8)}
    {map inv : List (BitVec 32)} (h : CompactBijOk old_cv ncv vals map inv)
    {l1 l2 : Nat} (hl1 : l1 < 2 * ncv) (hl2 : l2 < 2 * ncv)
    (heq : compactUnmapLit inv l1 = compactUnmapLit inv l2) : l1 = l2 := by
  have hd : l1 / 2 = l2 / 2 := h.inv_inj (by omega) (by omega) (by
    rw [← compactUnmapLit_div2 l1, ← compactUnmapLit_div2 l2, heq])
  have hm : l1 % 2 = l2 % 2 := by
    rw [← compactUnmapLit_mod2 l1, ← compactUnmapLit_mod2 l2, heq]
  omega

theorem level0_vals_false_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl : k.cur_level = 0)
    {l : Nat} (hl : l < 2 * k.cur_vars) (hf : k.vals[l]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1]) := by
  obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp hf
  have h0 : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le i hi; omega
  simpa [heq] using hw.level0_sound i hi h0

theorem compactArena_entails_kept {F_cur : List (List Nat)} {inv : List (BitVec 32)}
    {olits kept : List Nat} (hold : (cnfOfClauses F_cur).EntailsClause (cnfClause olits))
    (hsub : ∀ l ∈ olits, l ∈ kept.map (compactUnmapLit inv) ∨
      (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1])) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause (kept.map (compactUnmapLit inv))) :=
  cmp_entails_of_mem_or_false hold hsub

/-! ## 2. Binary Watch Slice Compaction & Remap Helpers -/

theorem watchSliceOk_step {F_cur : List (List Nat)} {k : FullCoreState} {lit p rem : Nat}
    {w0 : BitVec 32} (h : WatchSliceOk F_cur k lit p rem) (hpos : 0 < rem)
    (hw0 : k.wstk[p]? = some w0) :
    ((w0 &&& 0x80000000#32) ≠ 0#32 →
      w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
      WatchSliceOk F_cur k lit (p + 1) (rem - 1)) ∧
    ((w0 &&& 0x80000000#32) = 0#32 →
      2 ≤ rem ∧ WatchSliceOk F_cur k lit (p + 2) (rem - 2)) := by
  cases h with
  | empty => omega
  | @bin _ rem1 w1 hp hfl hne hlt hent htail =>
    rw [hw0] at hp; cases hp
    exact ⟨fun _ => ⟨hne, hlt, hent, htail⟩, fun hz => absurd hz hfl⟩
  | @large _ rem1 w1 cref hp hp1 hfl hlt href htail =>
    rw [hw0] at hp; cases hp
    exact ⟨fun hne => absurd hfl hne, fun _ => ⟨by omega, htail⟩⟩

theorem watchSliceOk_relocate_cmp {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} (hcv : k'.cur_vars = k.cur_vars)
    (har : k'.arena = k.arena) (hal : k'.arena_len = k.arena_len)
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F_cur k lit p rem) : WatchSliceOk F_cur k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hf hne hlt hent _ ih =>
    exact .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hne (hcv ▸ hlt) hent
      (ih (p' := p' + 1) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega))
  | @large p rem w0 w1 hp h1 hf hn hlt _ ih =>
    have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k := by
      simp only [fullArenaClauseRefsCore, har, hal]
    exact .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa [Nat.add_assoc] using (hwstk 1 (by omega)).trans h1) hf hn (hrefs ▸ hlt)
      (ih (p' := p' + 2) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 2) (by omega))

theorem Spec.CompactPreBinSliceOk.relocate {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {k k' : FullCoreState} {olit p p' rem : Nat}
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : CompactPreBinSliceOk ncv inv F_cur k olit p rem) :
    CompactPreBinSliceOk ncv inv F_cur k' olit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hfl hne hlt hent _ ih =>
    exact .bin (by simpa using (hwstk 0 (by omega)).trans hp) hfl hne hlt hent
      (ih (p' := p' + 1) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega))

theorem Spec.CompactPreBinSliceOk.toUnmap {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {k : FullCoreState} {nlit olit p rem : Nat}
    (hum : compactUnmapLit inv nlit = olit)
    (h : CompactPreBinSliceOk ncv inv F_cur k olit p rem) :
    CompactUnmapBinSliceOk ncv inv F_cur k nlit p rem := by
  induction h with
  | empty => exact .empty
  | @bin p rem w0 hp hfl hne hlt hent _ ih => exact .bin hp hfl hne hlt (hum ▸ hent) ih

theorem Spec.CompactUnmapBinSliceOk.relocate {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {k k' : FullCoreState} {nlit p p' rem : Nat}
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : CompactUnmapBinSliceOk ncv inv F_cur k nlit p rem) :
    CompactUnmapBinSliceOk ncv inv F_cur k' nlit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hfl hne hlt hent _ ih =>
    exact .bin (by simpa using (hwstk 0 (by omega)).trans hp) hfl hne hlt hent
      (ih (p' := p' + 1) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega))

theorem Spec.CompactUnmapBinSliceOk.append_bin {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {k k' : FullCoreState} {nlit off off' rem : Nat}
    {w0 : BitVec 32} (h : CompactUnmapBinSliceOk ncv inv F_cur k nlit off rem)
    (hpre : ∀ idx < rem, k'.wstk[off' + idx]? = k.wstk[off + idx]?)
    (hw0 : k'.wstk[off' + rem]? = some w0)
    (hfl : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * ncv)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause
      [compactUnmapLit inv nlit, compactUnmapLit inv (w0 &&& 0x7FFFFFFF#32).toNat])) :
    CompactUnmapBinSliceOk ncv inv F_cur k' nlit off' (rem + 1) := by
  induction h generalizing off' with
  | empty =>
    rw [Nat.add_zero] at hw0
    exact .bin hw0 hfl hne hlt hent .empty
  | @bin p rem0 w1 hp hfl1 hne1 hlt1 hent1 _ ih =>
    have hp0 : k'.wstk[off']? = some w1 := by simpa using (hpre 0 (by omega)).trans hp
    have hw0' : k'.wstk[(off' + 1) + rem0]? = some w0 := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0
    have hpre' : ∀ idx < rem0, k'.wstk[(off' + 1) + idx]? = k.wstk[(p + 1) + idx]? := by
      intro idx hi
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpre (idx + 1) (by omega)
    exact .bin hp0 hfl1 hne1 hlt1 hent1 (ih hpre' hw0')

theorem Spec.CompactUnmapBinsOk.with_vars {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {k k' : FullCoreState}
    (h : CompactUnmapBinsOk ncv inv F_cur k) (_hncv : ncv ≤ k'.cur_vars)
    (hcv_le : k'.cur_vars ≤ k.cur_vars) (hw : k'.wvec = k.wvec)
    (hs : k'.wstk = k.wstk) (hl : k'.wlen = k.wlen) :
    CompactUnmapBinsOk ncv inv F_cur k' := by
  refine ⟨⟨fun l hl' => by
      unfold fullWatchOffCore fullWatchSizeCore; rw [hw, hl]
      exact h.layout.bounds l (by omega),
    fun l hl' hp => by
      unfold fullWatchSizeCore at hp; unfold fullWatchOffCore
      rw [hw] at hp ⊢; exact h.layout.pos_off l (by omega) hp,
    fun l1 l2 h1 h2 hne hp1 hp2 => by
      unfold fullWatchSizeCore at hp1 hp2; unfold fullWatchOffCore fullWatchSizeCore
      rw [hw] at hp1 hp2 ⊢; exact h.layout.disjoint l1 l2 (by omega) (by omega) hne hp1 hp2,
    fun l hl' idx hidx => by
      unfold fullWatchSizeCore at hidx; unfold fullWatchOffCore; rw [hw] at hidx ⊢; rw [hs]
      exact h.layout.no_sentinel l (by omega) idx hidx⟩,
    fun l h1 h2 => by
      unfold fullWatchSizeCore; rw [hw]
      exact h.empty_hi l h1 (by omega),
    fun l hl' => by
      have hs0 := h.slices l hl'
      unfold fullWatchOffCore fullWatchSizeCore at hs0 ⊢
      rw [hw]; exact hs0.relocate fun idx _ => by simp [hs]⟩

theorem compactBins_zero_slice_layout {c : FullCfg} {kL : FullCoreState}
    {wvecL : List (BitVec 32)} {l : Nat} (hwvec : kL.wvec = wvecL)
    (hwvL : wvecL.length = 4 * c.max_vars) (hcv : kL.cur_vars ≤ c.max_vars)
    (hl : l < 2 * kL.cur_vars) (hsz0 : fullWatchSizeCore kL l = 0)
    (hlayL : WatchStackLayout kL) :
    let wvec' := wvecL.set (2 * l) 0#32
    let k' : FullCoreState := { kL with wvec := wvec' }
    fullWatchOffCore k' l = 0 ∧ fullWatchSizeCore k' l = 0 ∧
    (∀ j, j ≠ l →
      fullWatchOffCore k' j = fullWatchOffCore kL j ∧
      fullWatchSizeCore k' j = fullWatchSizeCore kL j) ∧
    WatchStackLayout k' := by
  intro wvec' k'
  have h2l_lt : 2 * l < wvecL.length := by omega
  have hoff'_l : fullWatchOffCore k' l = 0 := by
    unfold fullWatchOffCore k' wvec'
    rw [List.getElem?_set_self h2l_lt, Option.getD_some]; rfl
  have hsz'_l : fullWatchSizeCore k' l = 0 := by
    unfold fullWatchSizeCore k' wvec'
    rw [List.getElem?_set_ne (by omega), ← hwvec]; exact hsz0
  have hne_eq : ∀ j, j ≠ l →
      fullWatchOffCore k' j = fullWatchOffCore kL j ∧
      fullWatchSizeCore k' j = fullWatchSizeCore kL j := fun j hj => by
    unfold fullWatchOffCore fullWatchSizeCore k' wvec'
    rw [← hwvec]; constructor <;> rw [List.getElem?_set_ne (by omega)]
  refine ⟨hoff'_l, hsz'_l, hne_eq,
    ⟨fun j hj => by
       by_cases hjl : j = l
       · subst hjl; rw [hoff'_l, hsz'_l]; exact Nat.zero_le _
       · obtain ⟨ho, hs⟩ := hne_eq j hjl; rw [ho, hs]; exact hlayL.bounds j hj,
     fun j hj hp => by
       by_cases hjl : j = l
       · subst hjl; rw [hsz'_l] at hp; omega
       · obtain ⟨ho, hs⟩ := hne_eq j hjl; rw [ho]; rw [hs] at hp; exact hlayL.pos_off j hj hp,
     fun j1 j2 h1 h2 hne hp1 hp2 => by
       by_cases hj1 : j1 = l
       · subst hj1; rw [hsz'_l] at hp1; omega
       · by_cases hj2 : j2 = l
         · subst hj2; rw [hsz'_l] at hp2; omega
         · obtain ⟨ho1, hs1⟩ := hne_eq j1 hj1; obtain ⟨ho2, hs2⟩ := hne_eq j2 hj2
           rw [ho1, hs1, ho2, hs2]; rw [hs1] at hp1; rw [hs2] at hp2
           exact hlayL.disjoint j1 j2 h1 h2 hne hp1 hp2,
     fun j hj idx hi => by
       by_cases hjl : j = l
       · subst hjl; rw [hsz'_l] at hi; omega
       · obtain ⟨ho, hs⟩ := hne_eq j hjl; rw [ho]; rw [hs] at hi
         exact hlayL.no_sentinel j hj idx hi⟩⟩

private theorem compactPreBinSliceOk_ne_sentinel {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {k : FullCoreState} {l p rem : Nat}
    (hp : CompactPreBinSliceOk ncv inv F_cur k l p rem) :
    ∀ i < rem, k.wstk[p + i]? ≠ some 0xFFFFFFFF#32 := by
  induction hp with
  | empty => intro _ h; omega
  | @bin p rem0 w0 hw _ hne _ _ _ ih =>
    intro i hi; cases i with
    | zero => rw [Nat.add_zero, hw]; exact fun hs => hne (Option.some.inj hs)
    | succ j => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih j (by omega)

theorem compactBins_finish_lit {c : FullCfg} {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {kL : FullCoreState} {l q : Nat}
    {wstkK : List (BitVec 32)} (hckL : FullCoreState.LengthsOk c kL)
    (hlayL : WatchStackLayout kL) (hl : l < 2 * kL.cur_vars)
    (hq_ge : fullWatchOffCore kL l ≤ q)
    (hq_le : q ≤ fullWatchOffCore kL l + fullWatchSizeCore kL l)
    (hwsK : wstkK.length = c.wcap)
    (hout : ∀ i, i < fullWatchOffCore kL l ∨
      fullWatchOffCore kL l + fullWatchSizeCore kL l ≤ i → wstkK[i]? = kL.wstk[i]?)
    (hpreK : CompactPreBinSliceOk ncv inv F_cur { kL with wstk := wstkK } l
      (fullWatchOffCore kL l) (q - fullWatchOffCore kL l))
    (wu' nb' : BitVec 64) :
    let off0 := fullWatchOffCore kL l
    let wvecG := if q = off0 then (kL.wvec.set (2 * l) 0#32).set (2 * l + 1) 0#32
                 else kL.wvec.set (2 * l + 1) (BitVec.ofNat 32 (q - off0))
    let kG : FullCoreState :=
      { kL with wvec := wvecG, wstk := wstkK, wusable := wu', num_binary := nb' }
    FullCoreState.LengthsOk c kG ∧ WatchStackLayout kG ∧
    (∀ ol < 2 * kL.cur_vars, ol ≠ l →
      (fullWatchOffCore kG ol = fullWatchOffCore kL ol ∧
        fullWatchSizeCore kG ol = fullWatchSizeCore kL ol) ∧
      ∀ idx < fullWatchSizeCore kL ol,
        kG.wstk[fullWatchOffCore kL ol + idx]? = kL.wstk[fullWatchOffCore kL ol + idx]?) ∧
    CompactPreBinSliceOk ncv inv F_cur kG l (fullWatchOffCore kG l) (fullWatchSizeCore kG l) := by
  intro off0 wvecG kG
  have hcv_le := hckL.cur_vars_le
  have hwvL := hckL.wvec_len
  have hwl_le := hckL.wlen_le
  have hbd_l := hlayL.bounds l hl
  have hwc_lt : c.wcap < 2 * 2 ^ 28 := c.hwcap
  have hlenG : kG.wvec.length = 4 * c.max_vars := by
    dsimp only [kG, wvecG]; split <;> simp [hwvL]
  have hckG : FullCoreState.LengthsOk c kG :=
    { hckL with wvec_len := hlenG, wstk_len_arr := hwsK }
  have hdiff_lt32 : q - off0 < 2 ^ 32 := by omega
  have hoff_l : fullWatchOffCore kG l = if q = off0 then 0 else off0 := by
    unfold fullWatchOffCore; dsimp only [kG, wvecG]
    by_cases hq0 : q = off0
    · simp only [hq0, ↓reduceIte]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
      rfl
    · simp only [hq0, ↓reduceIte]
      rw [List.getElem?_set_ne (by omega)]; rfl
  have hsz_l : fullWatchSizeCore kG l = q - off0 := by
    unfold fullWatchSizeCore; dsimp only [kG, wvecG]
    by_cases hq0 : q = off0
    · simp only [hq0, ↓reduceIte, Nat.sub_self]
      rw [List.getElem?_set_self (by simp [hwvL]; omega), Option.getD_some]; rfl
    · simp only [hq0, ↓reduceIte]
      rw [List.getElem?_set_self (by omega), Option.getD_some, bv32_ofNat_toNat hdiff_lt32]
  have hoth_off : ∀ ol, ol ≠ l →
      fullWatchOffCore kG ol = fullWatchOffCore kL ol ∧
      fullWatchSizeCore kG ol = fullWatchSizeCore kL ol := fun ol hne => by
    unfold fullWatchOffCore fullWatchSizeCore; dsimp only [kG, wvecG]
    by_cases hq0 : q = off0
    · simp only [hq0, ↓reduceIte]
      constructor <;> rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    · simp only [hq0, ↓reduceIte]
      constructor <;> rw [List.getElem?_set_ne (by omega)]
  have hws_oth : ∀ ol < 2 * kL.cur_vars, ol ≠ l → ∀ idx < fullWatchSizeCore kL ol,
      kG.wstk[fullWatchOffCore kL ol + idx]? = kL.wstk[fullWatchOffCore kL ol + idx]? := by
    intro ol hol hne idx hidx
    dsimp only [kG]
    by_cases hsz0_l : fullWatchSizeCore kL l = 0
    · exact hout _ (by omega)
    · have hdj := hlayL.disjoint ol l hol hl hne (by omega) (by omega)
      rcases hdj with h1 | h2
      · exact hout _ (Or.inl (by omega))
      · exact hout _ (Or.inr (by omega))
  have hpreK_G : CompactPreBinSliceOk ncv inv F_cur kG l off0 (q - off0) :=
    Spec.CompactPreBinSliceOk.relocate (k := { kL with wstk := wstkK }) (k' := kG)
      (fun _ _ => rfl) hpreK
  have hpreG : CompactPreBinSliceOk ncv inv F_cur kG l
      (fullWatchOffCore kG l) (fullWatchSizeCore kG l) := by
    rw [hoff_l, hsz_l]
    by_cases hq0 : q = off0
    · simp only [hq0, ↓reduceIte, Nat.sub_self]; exact .empty
    · rw [ite_eq_right hq0]; exact hpreK_G
  have hno_l : ∀ idx < fullWatchSizeCore kG l,
      kG.wstk[fullWatchOffCore kG l + idx]? ≠ some 0xFFFFFFFF#32 := by
    rw [hoff_l, hsz_l]
    by_cases hq0 : q = off0
    · simp [hq0]
    · rw [ite_eq_right hq0]
      exact compactPreBinSliceOk_ne_sentinel hpreK_G
  have hlayG : WatchStackLayout kG := by
    refine ⟨fun j hj => ?_, fun j hj hp => ?_, fun j1 j2 h1 h2 hne hp1 hp2 => ?_,
      fun j hj idx hidx => ?_⟩
    · by_cases hjl : j = l
      · subst hjl; rw [hoff_l, hsz_l]
        by_cases hq0 : q = off0
        · simp [hq0]
        · rw [ite_eq_right hq0]; exact Nat.le_trans (by omega) hbd_l
      · obtain ⟨ho, hs⟩ := hoth_off j hjl; rw [ho, hs]; exact hlayL.bounds j hj
    · by_cases hjl : j = l
      · subst hjl; rw [hoff_l]; rw [hsz_l] at hp
        have hq0 : q ≠ off0 := by omega
        rw [ite_eq_right hq0]; exact hlayL.pos_off j hj (by omega)
      · obtain ⟨ho, hs⟩ := hoth_off j hjl; rw [ho]; rw [hs] at hp; exact hlayL.pos_off j hj hp
    · by_cases hj1 : j1 = l
      · rw [hj1, hoff_l, hsz_l]; rw [hj1, hsz_l] at hp1
        have hq0 : q ≠ off0 := by omega
        rw [ite_eq_right hq0]
        obtain ⟨ho2, hs2⟩ := hoth_off j2 (by rw [← hj1]; exact Ne.symm hne)
        rw [ho2, hs2]; rw [hs2] at hp2
        rcases hlayL.disjoint j1 j2 h1 h2 hne (by rw [hj1]; omega) hp2 with ha | hb
        · rw [hj1] at ha; exact Or.inl (by dsimp only [off0] at *; omega)
        · exact Or.inr (by dsimp only [off0]; rw [← hj1]; exact hb)
      · by_cases hj2 : j2 = l
        · rw [hj2, hoff_l, hsz_l]; rw [hj2, hsz_l] at hp2
          have hq0 : q ≠ off0 := by omega
          rw [ite_eq_right hq0]
          obtain ⟨ho1, hs1⟩ := hoth_off j1 hj1; rw [ho1, hs1]; rw [hs1] at hp1
          rcases hlayL.disjoint j1 j2 h1 h2 hne hp1 (by rw [hj2]; omega) with ha | hb
          · exact Or.inl (by dsimp only [off0]; rw [← hj2]; exact ha)
          · rw [hj2] at hb; exact Or.inr (by dsimp only [off0] at *; omega)
        · obtain ⟨ho1, hs1⟩ := hoth_off j1 hj1; obtain ⟨ho2, hs2⟩ := hoth_off j2 hj2
          rw [ho1, hs1, ho2, hs2]; rw [hs1] at hp1; rw [hs2] at hp2
          exact hlayL.disjoint j1 j2 h1 h2 hne hp1 hp2
    · by_cases hjl : j = l
      · subst hjl; exact hno_l idx hidx
      · obtain ⟨ho, hs⟩ := hoth_off j hjl; rw [ho]; rw [hs] at hidx
        rw [hws_oth j hj hjl idx hidx]; exact hlayL.no_sentinel j hj idx hidx
  exact ⟨hckG, hlayG, fun ol hol hne => ⟨hoth_off ol hne, hws_oth ol hol hne⟩, hpreG⟩

theorem compactBins_loop2_step {old_cv ncv v nv cmax : Nat}
    {vals : List (BitVec 8)} {map inv : List (BitVec 32)}
    {wvecL wvec2 : List (BitVec 32)} (hbij : CompactBijOk old_cv ncv vals map inv)
    (hwv2 : wvec2.length = 4 * cmax) (hv_lt : v < old_cv) (hcv_le : old_cv ≤ cmax)
    (hncv_le : ncv ≤ old_cv) (hnv_lt : nv < ncv) (hnv_lt_v : nv < v)
    (hi_v : inv[nv]? = some (BitVec.ofNat 32 v))
    (hhi2 : ∀ w, v ≤ w → w < old_cv → ∀ d < 4, wvec2[4 * w + d]? = wvecL[4 * w + d]?)
    (hmap2 : ∀ nv' < ncv, ∀ ov, (inv[nv']?.getD 0#32).toNat = ov → ov < v →
      ∀ d < 4, wvec2[4 * nv' + d]? = wvecL[4 * ov + d]?)
    (hb0 : 4 * v < wvec2.length) (hb1 : 4 * v + 1 < wvec2.length)
    (hb2 : 4 * v + 2 < wvec2.length) (hb3 : 4 * v + 3 < wvec2.length) :
    let wvec2' := (((wvec2.set (4 * nv) (wvec2[4 * v]'hb0)).set (4 * nv + 1)
      (wvec2[4 * v + 1]'hb1)).set (4 * nv + 2) (wvec2[4 * v + 2]'hb2)).set
      (4 * nv + 3) (wvec2[4 * v + 3]'hb3)
    wvec2'.length = 4 * cmax ∧
    (∀ w, v + 1 ≤ w → w < old_cv → ∀ d < 4, wvec2'[4 * w + d]? = wvecL[4 * w + d]?) ∧
    (∀ nv' < ncv, ∀ ov, (inv[nv']?.getD 0#32).toNat = ov → ov < v + 1 →
      ∀ d < 4, wvec2'[4 * nv' + d]? = wvecL[4 * ov + d]?) := by
  intro wvec2'
  have hov_lt32 : old_cv < 2 ^ 32 := by have := hbij.old_cv_lt; omega
  refine ⟨by simp [wvec2', hwv2], fun w hw1 hw2 d hd => ?_, fun nv' hnv' ov hov1 hov2 d hd => ?_⟩
  · dsimp only [wvec2']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hhi2 w (by omega) hw2 d hd
  · by_cases heq : ov = v
    · have hnv_eq : nv' = nv := hbij.inv_inj (nv1 := nv') (nv2 := nv) hnv' hnv_lt
        (by rw [hov1, heq, hi_v, Option.getD_some, bv32_ofNat_toNat (by omega)])
      subst hnv_eq; rw [heq]
      rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3) with rfl | rfl | rfl | rfl <;>
        dsimp only [wvec2']
      · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega), Nat.add_zero,
          List.getElem?_set_self (by rw [hwv2]; omega)]
        simpa [List.getElem?_eq_getElem hb0] using hhi2 v (Nat.le_refl _) hv_lt 0 (by omega)
      · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_self (by simp [hwv2]; omega)]
        simpa [List.getElem?_eq_getElem hb1] using hhi2 v (Nat.le_refl _) hv_lt 1 (by omega)
      · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hwv2]; omega)]
        simpa [List.getElem?_eq_getElem hb2] using hhi2 v (Nat.le_refl _) hv_lt 2 (by omega)
      · rw [List.getElem?_set_self (by simp [hwv2]; omega)]
        simpa [List.getElem?_eq_getElem hb3] using hhi2 v (Nat.le_refl _) hv_lt 3 (by omega)
    · have hnv'_ne : nv' ≠ nv := fun hsame => by
        subst hsame
        have : ov = v := by rw [hi_v, Option.getD_some, bv32_ofNat_toNat (by omega)] at hov1; omega
        exact heq this
      dsimp only [wvec2']
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hmap2 nv' hnv' ov hov1 (by omega) d hd

theorem compactBins_loop3_step {ncv old_cv v3 cmax : Nat}
    {wvec2 wvec3 : List (BitVec 32)} (hwv3 : wvec3.length = 4 * cmax) (hncv_v3 : ncv ≤ v3)
    (hv3_lt : v3 < old_cv) (hcv_le : old_cv ≤ cmax)
    (hzero3 : ∀ w, ncv ≤ w → w < v3 → ∀ d < 4, wvec3[4 * w + d]? = some 0#32)
    (hpres3 : ∀ nv < ncv, ∀ d < 4, wvec3[4 * nv + d]? = wvec2[4 * nv + d]?) :
    let wvec3' := (((wvec3.set (4 * v3) 0#32).set (4 * v3 + 1) 0#32).set
      (4 * v3 + 2) 0#32).set (4 * v3 + 3) 0#32
    wvec3'.length = 4 * cmax ∧
    (∀ w, ncv ≤ w → w < v3 + 1 → ∀ d < 4, wvec3'[4 * w + d]? = some 0#32) ∧
    (∀ nv < ncv, ∀ d < 4, wvec3'[4 * nv + d]? = wvec2[4 * nv + d]?) := by
  intro wvec3'
  refine ⟨by simp [wvec3', hwv3], fun w hw1 hw2 d hd => ?_, fun nv hnv d hd => ?_⟩
  · by_cases hwv : w = v3
    · subst hwv
      rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3) with rfl | rfl | rfl | rfl <;>
        dsimp only [wvec3']
      · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega), Nat.add_zero,
          List.getElem?_set_self (by rw [hwv3]; omega)]
      · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_self (by simp [hwv3]; omega)]
      · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hwv3]; omega)]
      · rw [List.getElem?_set_self (by simp [hwv3]; omega)]
    · dsimp only [wvec3']
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hzero3 w hw1 (by omega) d hd
  · dsimp only [wvec3']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hpres3 nv hnv d hd

theorem compactBins_loop3_done {ncv old_cv : Nat} {inv : List (BitVec 32)}
    {kL k3 : FullCoreState} {wvecL wvec2 wvec3 : List (BitVec 32)}
    (hk3 : k3.wvec = wvec3) (hkL : kL.wvec = wvecL)
    (hzero3 : ∀ w, ncv ≤ w → w < old_cv → ∀ d < 4, wvec3[4 * w + d]? = some 0#32)
    (hpres3 : ∀ nv < ncv, ∀ d < 4, wvec3[4 * nv + d]? = wvec2[4 * nv + d]?)
    (hmap2 : ∀ nv < ncv, ∀ ov, (inv[nv]?.getD 0#32).toNat = ov → ov < old_cv →
      ∀ d < 4, wvec2[4 * nv + d]? = wvecL[4 * ov + d]?) :
    (∀ l, 2 * ncv ≤ l → l < 2 * old_cv →
      fullWatchOffCore k3 l = 0 ∧ fullWatchSizeCore k3 l = 0) ∧
    (∀ nv < ncv, ∀ ov, (inv[nv]?.getD 0#32).toNat = ov → ov < old_cv →
      k3.wvec[4 * nv]? = kL.wvec[4 * ov]? ∧ k3.wvec[4 * nv + 1]? = kL.wvec[4 * ov + 1]? ∧
      k3.wvec[4 * nv + 2]? = kL.wvec[4 * ov + 2]? ∧
      k3.wvec[4 * nv + 3]? = kL.wvec[4 * ov + 3]?) := by
  refine ⟨fun l h1 h2 => ?_, fun nv hnv ov hov1 hov2 => ?_⟩
  · have hz0 := hzero3 (l / 2) (by omega) (by omega)
    unfold fullWatchOffCore fullWatchSizeCore; rw [hk3]
    rcases Nat.mod_two_eq_zero_or_one l with hm2 | hm2
    · rw [show 2 * l + 1 = 4 * (l / 2) + 1 by omega, show 2 * l = 4 * (l / 2) + 0 by omega,
        hz0 0 (by omega), hz0 1 (by omega)]; exact ⟨rfl, rfl⟩
    · rw [show 2 * l + 1 = 4 * (l / 2) + 3 by omega, show 2 * l = 4 * (l / 2) + 2 by omega,
        hz0 2 (by omega), hz0 3 (by omega)]; exact ⟨rfl, rfl⟩
  · have hp := hpres3 nv hnv; have hm := hmap2 nv hnv ov hov1 hov2
    rw [hk3, hkL]
    exact ⟨(hp 0 (by omega)).trans (hm 0 (by omega)), (hp 1 (by omega)).trans (hm 1 (by omega)),
      (hp 2 (by omega)).trans (hm 2 (by omega)), (hp 3 (by omega)).trans (hm 3 (by omega))⟩

theorem compactBins_finalize {c : FullCfg} {old_cv ncv : Nat} {vals : List (BitVec 8)}
    {map inv : List (BitVec 32)} {F_cur : List (List Nat)} {k1 k2 : FullCoreState}
    (hcv1 : k1.cur_vars = old_cv) (hcv2 : k2.cur_vars = old_cv)
    (hbij : CompactBijOk old_cv ncv vals map inv) (hlay1 : WatchStackLayout k1)
    (_hwv2 : k2.wvec.length = 4 * c.max_vars) (hs : k2.wstk = k1.wstk) (hl : k2.wlen = k1.wlen)
    (hhi : ∀ l, 2 * ncv ≤ l → l < 2 * old_cv →
      fullWatchOffCore k2 l = 0 ∧ fullWatchSizeCore k2 l = 0)
    (hmap : ∀ nv < ncv, ∀ ov, (inv[nv]?.getD 0#32).toNat = ov → ov < old_cv →
      k2.wvec[4 * nv]? = k1.wvec[4 * ov]? ∧ k2.wvec[4 * nv + 1]? = k1.wvec[4 * ov + 1]? ∧
      k2.wvec[4 * nv + 2]? = k1.wvec[4 * ov + 2]? ∧
      k2.wvec[4 * nv + 3]? = k1.wvec[4 * ov + 3]?)
    (hpre : ∀ ol < 2 * old_cv,
      CompactPreBinSliceOk ncv inv F_cur k1 ol (fullWatchOffCore k1 ol) (fullWatchSizeCore k1 ol)) :
    CompactUnmapBinsOk ncv inv F_cur k2 := by
  have hov_of : ∀ l < 2 * ncv, ∃ ov < old_cv,
      inv[l / 2]? = some (BitVec.ofNat 32 ov) ∧
      fullWatchOffCore k2 l = fullWatchOffCore k1 (2 * ov + l % 2) ∧
      fullWatchSizeCore k2 l = fullWatchSizeCore k1 (2 * ov + l % 2) := by
    intro l hl_lt
    obtain ⟨ov, hov_lt, _, _, hinv, _⟩ := hbij.inv_ok (l / 2) (by omega)
    have hm := hmap (l / 2) (by omega) ov (by
      have := hbij.old_cv_lt; rw [hinv, Option.getD_some, bv32_ofNat_toNat (by omega)]) hov_lt
    refine ⟨ov, hov_lt, hinv, ?_, ?_⟩
    · unfold fullWatchOffCore
      rcases Nat.mod_two_eq_zero_or_one l with hp | hp
      · rw [hp, show 2 * l = 4 * (l / 2) by omega, show 2 * (2 * ov + 0) = 4 * ov by omega, hm.1]
      · rw [hp, show 2 * l = 4 * (l / 2) + 2 by omega,
          show 2 * (2 * ov + 1) = 4 * ov + 2 by omega, hm.2.2.1]
    · unfold fullWatchSizeCore
      rcases Nat.mod_two_eq_zero_or_one l with hp | hp
      · rw [hp, show 2 * l + 1 = 4 * (l / 2) + 1 by omega,
          show 2 * (2 * ov + 0) + 1 = 4 * ov + 1 by omega, hm.2.1]
      · rw [hp, show 2 * l + 1 = 4 * (l / 2) + 3 by omega,
          show 2 * (2 * ov + 1) + 1 = 4 * ov + 3 by omega, hm.2.2.2]
  have hlay2 : WatchStackLayout k2 := by
    refine ⟨fun l hl' => ?_, fun l hl' hp => ?_, fun l1 l2 h1 h2 hne hp1 hp2 => ?_,
      fun l hl' idx hi => ?_⟩
    · by_cases hlt : l < 2 * ncv
      · obtain ⟨ov, hov, _, ho, hsz⟩ := hov_of l hlt; rw [ho, hsz, hl]
        exact hlay1.bounds _ (by omega)
      · obtain ⟨ho, hsz⟩ := hhi l (by omega) (hcv2 ▸ hl'); rw [ho, hsz]; exact Nat.zero_le _
    · by_cases hlt : l < 2 * ncv
      · obtain ⟨ov, hov, _, ho, hsz⟩ := hov_of l hlt; rw [ho]; rw [hsz] at hp
        exact hlay1.pos_off _ (by omega) hp
      · obtain ⟨_, hsz⟩ := hhi l (by omega) (hcv2 ▸ hl'); omega
    · by_cases hlt1 : l1 < 2 * ncv
      · by_cases hlt2 : l2 < 2 * ncv
        · obtain ⟨ov1, hov1, hinv1, ho1, hs1⟩ := hov_of l1 hlt1
          obtain ⟨ov2, hov2, hinv2, ho2, hs2⟩ := hov_of l2 hlt2
          have hne_ov : 2 * ov1 + l1 % 2 ≠ 2 * ov2 + l2 % 2 := fun heq => by
            apply hne
            have hv1 : l1 / 2 = l2 / 2 := hbij.inv_inj (by omega) (by omega) (by
              have := hbij.old_cv_lt
              rw [hinv1, hinv2, Option.getD_some, Option.getD_some,
                bv32_ofNat_toNat (by omega), bv32_ofNat_toNat (by omega)]
              omega)
            omega
          rw [ho1, hs1, ho2, hs2]; rw [hs1] at hp1; rw [hs2] at hp2
          exact hlay1.disjoint _ _ (by omega) (by omega) hne_ov hp1 hp2
        · obtain ⟨_, hsz2⟩ := hhi l2 (by omega) (hcv2 ▸ h2); omega
      · obtain ⟨_, hsz1⟩ := hhi l1 (by omega) (hcv2 ▸ h1); omega
    · by_cases hlt : l < 2 * ncv
      · obtain ⟨ov, hov, _, ho, hsz⟩ := hov_of l hlt; rw [ho, hs]; rw [hsz] at hi
        exact hlay1.no_sentinel _ (by omega) idx hi
      · obtain ⟨_, hsz⟩ := hhi l (by omega) (hcv2 ▸ hl'); omega
  refine ⟨hlay2, fun l h1 h2 => (hhi l h1 (hcv2 ▸ h2)).2, fun l hl' => ?_⟩
  obtain ⟨ov, hov, hinv, ho, hsz⟩ := hov_of l hl'
  rw [ho, hsz]
  have hov32 : ov < 2 ^ 32 := by have := hbij.old_cv_lt; omega
  have hum : compactUnmapLit inv l = 2 * ov + l % 2 := by
    unfold compactUnmapLit
    rw [hinv, Option.getD_some, bv32_ofNat_toNat hov32]
  have hpre1 : CompactPreBinSliceOk ncv inv F_cur k2 (2 * ov + l % 2)
      (fullWatchOffCore k1 (2 * ov + l % 2)) (fullWatchSizeCore k1 (2 * ov + l % 2)) :=
    (hpre (2 * ov + l % 2) (by omega)).relocate fun idx _ => by simp [hs]
  exact hpre1.toUnmap hum

/-! ## 3. Compacted Arena Prefix & `CompactArenaOk` Helpers -/

/-- Valid contiguous compacted arena prefix `[0 ..< dst)` without shrink or garbage markers. -/
structure CompactArenaPrefix (c : FullCfg) (ncv : Nat) (inv : List (BitVec 32))
    (F_cur : List (List Nat)) (ar : List (BitVec 32)) (dst : Nat) : Prop where
  dst_ok : dst = 0 ∨ 3 ≤ dst
  dst_le : dst ≤ ar.length
  refs_wf : ∀ r ∈ fullArenaScanRefs ar dst 0 dst,
    r + 3 ≤ dst ∧ 3 ≤ (ar[r + 2]?.getD 0#32).toNat ∧
    r + 3 + (ar[r + 2]?.getD 0#32).toNat = fullArenaNextOff ar dst r ∧
    fullArenaNextOff ar dst r ≤ dst ∧
    (fullArenaNextOff ar dst r = dst ∨ fullArenaNextOff ar dst r + 3 ≤ dst)
  no_shrk : ∀ r ∈ fullArenaScanRefs ar dst 0 dst, (ar[r]?.getD 0#32 &&& 0x00800000#32) = 0#32
  no_garb : ∀ r ∈ fullArenaScanRefs ar dst 0 dst, (ar[r]?.getD 0#32 &&& 0x00080000#32) = 0#32
  lits_lt : ∀ r ∈ fullArenaScanRefs ar dst 0 dst,
    ∀ j < (ar[r + 2]?.getD 0#32).toNat, (ar[r + 3 + j]?.getD 0#32).toNat < 2 * ncv
  nodup : ∀ r ∈ fullArenaScanRefs ar dst 0 dst,
    ((((ar.drop (r + 3)).take (ar[r + 2]?.getD 0#32).toNat).map BitVec.toNat).map (· / 2)).Nodup
  entails : ∀ r ∈ fullArenaScanRefs ar dst 0 dst,
    (cnfOfClauses F_cur).EntailsClause (cnfClause
      ((((ar.drop (r + 3)).take (ar[r + 2]?.getD 0#32).toNat).map BitVec.toNat).map
        (compactUnmapLit inv)))

theorem compactArenaPrefix_empty (c : FullCfg) (ncv : Nat) (inv : List (BitVec 32))
    (F_cur : List (List Nat)) (ar : List (BitVec 32)) :
    CompactArenaPrefix c ncv inv F_cur ar 0 :=
  ⟨Or.inl rfl, Nat.zero_le _, fun _ h => by simp [fullArenaScanRefs] at h,
   fun _ h => by simp [fullArenaScanRefs] at h, fun _ h => by simp [fullArenaScanRefs] at h,
   fun _ h => by simp [fullArenaScanRefs] at h, fun _ h => by simp [fullArenaScanRefs] at h,
   fun _ h => by simp [fullArenaScanRefs] at h⟩

theorem compactArenaPrefix_congr {c : FullCfg} {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {ar1 ar2 : List (BitVec 32)} {dst : Nat}
    (h : CompactArenaPrefix c ncv inv F_cur ar1 dst) (hle : dst ≤ ar2.length)
    (hpre : ∀ i < dst, ar2[i]? = ar1[i]?) :
    CompactArenaPrefix c ncv inv F_cur ar2 dst := by
  have hle1 := h.dst_le
  have hnxt : ∀ r ∈ fullArenaScanRefs ar1 dst 0 dst,
      fullArenaNextOff ar2 dst r = fullArenaNextOff ar1 dst r := by
    intro r hr
    have hwf := h.refs_wf r hr
    have hns := h.no_shrk r hr
    have ha0 := hpre r (by omega)
    have ha2 := hpre (r + 2) (by omega)
    have h1 : ¬ (r + 3 > dst) := by omega
    have h2 : ¬ (r + 3 + (ar1[r + 2]?.getD 0#32).toNat > dst) := by omega
    unfold fullArenaNextOff
    simp [h1, ha0, ha2, h2, hns]
  have hrefs : fullArenaScanRefs ar2 dst 0 dst = fullArenaScanRefs ar1 dst 0 dst :=
    fullArenaScanRefs_congr hnxt
  have hsl : ∀ r ∈ fullArenaScanRefs ar1 dst 0 dst,
      (ar2.drop (r + 3)).take (ar2[r + 2]?.getD 0#32).toNat =
        (ar1.drop (r + 3)).take (ar1[r + 2]?.getD 0#32).toNat := by
    intro r hr
    have hwf := h.refs_wf r hr
    have ha2 := hpre (r + 2) (by omega)
    rw [ha2]
    have hlen_eq : ((ar2.drop (r + 3)).take (ar1[r + 2]?.getD 0#32).toNat).length =
        ((ar1.drop (r + 3)).take (ar1[r + 2]?.getD 0#32).toNat).length := by
      simp only [List.length_take, List.length_drop]
      rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
    refine List.ext_getElem hlen_eq fun j hj1 hj2 => ?_
    simp only [List.length_take, List.length_drop] at hj1 hj2
    rw [List.getElem_take, List.getElem_drop, List.getElem_take, List.getElem_drop]
    apply Option.some.inj
    rw [← List.getElem?_eq_getElem (by omega), ← List.getElem?_eq_getElem (by omega)]
    exact hpre (r + 3 + j) (by omega)
  refine ⟨h.dst_ok, hle, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_,
    fun r hr j hj => ?_, fun r hr => ?_, fun r hr => ?_⟩
  · rw [hrefs] at hr
    have hwf := h.refs_wf r hr
    rw [hpre (r + 2) (by omega), hnxt r hr]
    exact hwf
  · rw [hrefs] at hr; have hwf := h.refs_wf r hr; rw [hpre r (by omega)]; exact h.no_shrk r hr
  · rw [hrefs] at hr; have hwf := h.refs_wf r hr; rw [hpre r (by omega)]; exact h.no_garb r hr
  · rw [hrefs] at hr; have hwf := h.refs_wf r hr
    rw [hpre (r + 2) (by omega)] at hj
    rw [hpre (r + 3 + j) (by omega)]
    exact h.lits_lt r hr j hj
  · rw [hrefs] at hr; rw [hsl r hr]; exact h.nodup r hr
  · rw [hrefs] at hr; rw [hsl r hr]; exact h.entails r hr

theorem compactArenaPrefix_append {c : FullCfg} {ncv nsz dst : Nat}
    {inv : List (BitVec 32)} {F_cur : List (List Nat)} {ar ar' : List (BitVec 32)}
    (h : CompactArenaPrefix c ncv inv F_cur ar dst) (hnsz : 3 ≤ nsz)
    (hle : dst + 3 + nsz ≤ ar'.length) (hhold : ∀ i < dst, ar'[i]? = ar[i]?)
    (hns : (ar'[dst]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hng : (ar'[dst]?.getD 0#32 &&& 0x00080000#32) = 0#32)
    (hsz : (ar'[dst + 2]?.getD 0#32).toNat = nsz)
    (hlts : ∀ j < nsz, (ar'[dst + 3 + j]?.getD 0#32).toNat < 2 * ncv)
    (hnd : ((((ar'.drop (dst + 3)).take nsz).map BitVec.toNat).map (· / 2)).Nodup)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause
      ((((ar'.drop (dst + 3)).take nsz).map BitVec.toNat).map (compactUnmapLit inv)))) :
    CompactArenaPrefix c ncv inv F_cur ar' (dst + 3 + nsz) := by
  have hpre : CompactArenaPrefix c ncv inv F_cur ar' dst :=
    compactArenaPrefix_congr h (by omega) hhold
  have hlast : dst = 0 ∨ ∃ r ∈ fullArenaScanRefs ar' dst 0 dst,
      fullArenaNextOff ar' dst r = dst := by
    rcases hpre.dst_ok with rfl | h3
    · exact Or.inl rfl
    · right
      exact fullArenaScanRefs_last (by omega) h3 fun r hr => (hpre.refs_wf r hr).2.2.2.2
  have hnxts : ∀ r ∈ fullArenaScanRefs ar' dst 0 dst,
      fullArenaNextOff ar' (dst + 3 + nsz) r = fullArenaNextOff ar' dst r := by
    intro r hr
    have hwf := hpre.refs_wf r hr
    have hnsr := hpre.no_shrk r hr
    have h1 : ¬ (r + 3 > dst) := by omega
    have h1' : ¬ (r + 3 > dst + 3 + nsz) := by omega
    have h2 : ¬ (r + 3 + (ar'[r + 2]?.getD 0#32).toNat > dst) := by omega
    have h2' : ¬ (r + 3 + (ar'[r + 2]?.getD 0#32).toNat > dst + 3 + nsz) := by omega
    unfold fullArenaNextOff
    simp [h1, h1', h2, h2', hnsr]
  have hrefs : fullArenaScanRefs ar' (dst + 3 + nsz) 0 (dst + 3 + nsz) =
      fullArenaScanRefs ar' dst 0 dst ++ [dst] :=
    fullArenaScanRefs_eq_of_prefix hnsz hns hsz
      (fun r hr => (hpre.refs_wf r hr).2.2.2.2) hlast hnxts
  have hnxt_new : fullArenaNextOff ar' (dst + 3 + nsz) dst = dst + 3 + nsz := by
    have h1 : ¬ (dst + 3 > dst + 3 + nsz) := by omega
    unfold fullArenaNextOff; simp [h1, hsz, hns]
  refine ⟨Or.inr (by omega), hle, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_,
    fun r hr j hj => ?_, fun r hr => ?_, fun r hr => ?_⟩
  all_goals rw [hrefs, List.mem_append, List.mem_singleton] at hr
  · rcases hr with hr | rfl
    · have hwf := hpre.refs_wf r hr
      rw [hnxts r hr]
      exact ⟨by omega, hwf.2.1, hwf.2.2.1, by omega, Or.inr (by omega)⟩
    · rw [hsz, hnxt_new]; exact ⟨by omega, hnsz, rfl, Nat.le_refl _, Or.inl rfl⟩
  · rcases hr with hr | rfl
    · exact hpre.no_shrk r hr
    · exact hns
  · rcases hr with hr | rfl
    · exact hpre.no_garb r hr
    · exact hng
  · rcases hr with hr | rfl
    · exact hpre.lits_lt r hr j hj
    · rw [hsz] at hj; exact hlts j hj
  · rcases hr with hr | rfl
    · exact hpre.nodup r hr
    · rw [hsz]; exact hnd
  · rcases hr with hr | rfl
    · exact hpre.entails r hr
    · rw [hsz]; exact hent

theorem compactArenaPrefix_to_ok {c : FullCfg} {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {k : FullCoreState}
    (h : CompactArenaPrefix c ncv inv F_cur k.arena k.arena_len)
    (_hlen : k.arena.length = c.arena_cap) :
    CompactArenaOk c ncv inv F_cur k := by
  have hle := h.dst_le
  refine ⟨h.dst_ok, fun r hr => ?_, fun r hr => h.no_shrk r hr, fun r hr => h.no_garb r hr,
    fun r hr l hl => ?_, fun r hr => h.nodup r hr, fun r hr => h.entails r hr⟩
  · have hwf := h.refs_wf r hr
    exact ⟨hwf.1, hwf.2.1, by unfold fullArenaClauseSizeCore; exact le_of_eq hwf.2.2.1,
      hwf.2.2.2.1, hwf.2.2.2.2⟩
  · have hwf := h.refs_wf r hr
    have hbd : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length := by
      unfold fullArenaClauseSizeCore; omega
    obtain ⟨j, hj, rfl⟩ := (mem_fullArenaClauseLitsCore_iff hbd).mp hl
    unfold fullArenaClauseSizeCore at hj
    have hlt := h.lits_lt r hr j hj
    have hj_lt : r + 3 + j < k.arena.length := by omega
    rw [List.getElem?_eq_getElem hj_lt, Option.getD_some] at hlt
    exact hlt

theorem Spec.CompactArenaOk.with_core {c c' : FullCfg} {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {k k' : FullCoreState}
    (h : CompactArenaOk c ncv inv F_cur k) (har : k'.arena = k.arena)
    (hal : k'.arena_len = k.arena_len) : CompactArenaOk c' ncv inv F_cur k' := by
  have href : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k := by
    simp only [fullArenaClauseRefsCore, har, hal]
  refine ⟨hal ▸ h.len_ok, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr; rw [href] at hr
    simpa [hal, fullArenaClauseSizeCore, har] using h.refs_wf r hr
  · intro r hr; rw [href] at hr
    simpa [fullArenaHdrCore, har] using h.no_shrk r hr
  · intro r hr; rw [href] at hr
    simpa [fullArenaHdrCore, har] using h.no_garb r hr
  · intro r hr l hl; rw [href] at hr
    simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, har] using
      h.lits_lt r hr l (by simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, har] using hl)
  · intro r hr; rw [href] at hr
    simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, har] using h.nodup r hr
  · intro r hr; rw [href] at hr
    simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, har] using h.entails r hr

/-! ## 4. Post-Compaction Clause Database & `FullWitnessInv` Builder -/

/-- Extracts binary clauses `[lit, partner]` from slice `[p ..< p + rem)` of `k.wstk`. -/
@[expose] def binSliceClauses (k : FullCoreState) (lit : Nat) : Nat → Nat → List (List Nat)
  | _, 0 => []
  | p, rem + 1 =>
    let w0 := k.wstk[p]?.getD 0#32
    [lit, (w0 &&& 0x7FFFFFFF#32).toNat] :: binSliceClauses k lit (p + 1) rem

/-- All binary watch clauses stored across `0 ..< 2 * k.cur_vars`. -/
@[expose] def binClausesCore (k : FullCoreState) : List (List Nat) :=
  (List.range (2 * k.cur_vars)).flatMap fun l =>
    binSliceClauses k l (fullWatchOffCore k l) (fullWatchSizeCore k l)

/-- All non-garbage arena clauses stored in `k.arena`. -/
@[expose] def arenaClausesCore (k : FullCoreState) : List (List Nat) :=
  (fullArenaClauseRefsCore k).map fun r => fullArenaClauseLitsCore k r

/-- Complete compacted CNF clause list reconstructed from `k.wstk` and `k.arena`. -/
@[expose] def stateClausesCore (k : FullCoreState) : List (List Nat) :=
  binClausesCore k ++ arenaClausesCore k

private theorem entails_clause_of_cnfOfClauses_mem {F : List (List Nat)} {cl : List Nat}
    (hcl : cl ∈ F) : (cnfOfClauses F).EntailsClause (cnfClause cl) := by
  rw [CNF.entails_clause_def]
  intro α hα
  exact (cnf_sat_cnfOfClauses_iff α F).mp hα cl hcl

private theorem unsat_nil_clauses : (cnfOfClauses ([[]] : List (List Nat))).Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h := (cnf_sat_cnfOfClauses_iff α [[]]).mp hα [] (by simp)
  obtain ⟨_, hm, _⟩ := (clause_sat_cnfClause_iff α []).mp h
  cases hm

private theorem entails_of_unsat {F : CNF Nat} (hu : F.Unsat) (cl : CNF.Clause Nat) :
    F.EntailsClause cl := by
  rw [CNF.entails_clause_def]
  intro α hα
  exact absurd ((CNF.unsat_iff_not_sat.mp hu) α hα) False.elim

private theorem binSliceClauses_props {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {k : FullCoreState} {lit p rem : Nat}
    (hlit : lit < 2 * ncv) (h : CompactUnmapBinSliceOk ncv inv F_cur k lit p rem) :
    ∀ cl ∈ binSliceClauses k lit p rem,
      (∀ x ∈ cl, x / 2 < ncv) ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause (cl.map (compactUnmapLit inv))) := by
  induction h with
  | empty => intro _ hm; simp [binSliceClauses] at hm
  | @bin p rem w0 hp _ _ hlt hent _ ih =>
    intro cl hmem
    unfold binSliceClauses at hmem
    rw [hp, Option.getD_some] at hmem
    rcases List.mem_cons.mp hmem with rfl | htail
    · refine ⟨fun x hx => ?_, by simpa using hent⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> omega
    · exact ih cl htail

private theorem compactUnmapBinSliceOk_to_watch {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur F' : List (List Nat)} {k : FullCoreState} {lit p rem : Nat}
    (hcv : k.cur_vars = ncv) (h : CompactUnmapBinSliceOk ncv inv F_cur k lit p rem)
    (hent : ∀ cl ∈ binSliceClauses k lit p rem, (cnfOfClauses F').EntailsClause (cnfClause cl)) :
    WatchSliceOk F' k lit p rem := by
  induction h with
  | empty => exact .empty
  | @bin p rem w0 hp hfl hne hlt _ _ ih =>
    have hmem0 : [lit, (w0 &&& 0x7FFFFFFF#32).toNat] ∈ binSliceClauses k lit p (rem + 1) := by
      unfold binSliceClauses; rw [hp, Option.getD_some]; exact List.mem_cons_self
    exact .bin hp hfl hne (hcv ▸ hlt) (hent _ hmem0)
      (ih fun cl hc => hent cl (by
        unfold binSliceClauses; rw [hp, Option.getD_some]; exact .tail _ hc))

private theorem compactArena_to_fullArena {c : FullCfg} {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur F' : List (List Nat)} {k : FullCoreState}
    (har : CompactArenaOk c ncv inv F_cur k) (hcv : k.cur_vars = ncv)
    (hent : ∀ r ∈ fullArenaClauseRefsCore k,
      (cnfOfClauses F').EntailsClause (cnfClause (fullArenaClauseLitsCore k r))) :
    FullArenaClausesInv c F' k := by
  refine ⟨har.len_ok, har.refs_wf, ?_, ?_, ?_⟩
  · intro r hr hsh; exact absurd (har.no_shrk r hr) hsh
  · intro r hr _ l hl; exact hcv ▸ har.lits_lt r hr l hl
  · intro r hr _; exact hent r hr

/-- Builds a full post-compaction `FullWitnessInv` for `stateClausesCore k` from
`CompactUnmapBinsOk` and `CompactArenaOk` at root level (`trail_end = 0`, `cur_level = 0`,
all `vals = 0#8`). -/
theorem fullWitnessInv_compact_build {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {old_cv ncv : Nat} {inv : List (BitVec 32)} {k : FullCoreState}
    (hext : ExtUnsatSound F0 old_cv F_cur)
    (hbin : CompactUnmapBinsOk ncv inv F_cur k) (har : CompactArenaOk c ncv inv F_cur k)
    (hcv : k.cur_vars = ncv) (hinc : k.inconsistent = 0#64) (hdm : k.dense_mode = 0#64)
    (hte : k.trail_end = 0) (hcl : k.cur_level = 0)
    (hft0 : (k.frame_trail[0]?.getD 0#32).toNat = 0)
    (hvals : ∀ l < 2 * ncv, k.vals[l]?.getD 0#8 = 0#8) :
    FullWitnessInv c F0 (stateClausesCore k) k := by
  let F' := stateClausesCore k
  have hbin_ent : ∀ cl ∈ binClausesCore k,
      (∀ x ∈ cl, x / 2 < ncv) ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause (cl.map (compactUnmapLit inv))) := by
    intro cl hcl
    unfold binClausesCore at hcl
    rw [List.mem_flatMap] at hcl
    obtain ⟨l, hl_rng, hcl_sl⟩ := hcl
    rw [List.mem_range] at hl_rng
    have hl_lt : l < 2 * ncv := hcv ▸ hl_rng
    exact binSliceClauses_props hl_lt (hbin.slices l hl_lt) cl hcl_sl
  have har_ent : ∀ cl ∈ arenaClausesCore k,
      (∀ x ∈ cl, x / 2 < ncv) ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause (cl.map (compactUnmapLit inv))) := by
    intro cl hcl
    unfold arenaClausesCore at hcl
    rw [List.mem_map] at hcl
    obtain ⟨r, hr, rfl⟩ := hcl
    exact ⟨fun x hx => Nat.div_lt_of_lt_mul (har.lits_lt r hr x hx), har.entails r hr⟩
  have hvars_b : VarsBounded k.cur_vars F' := by
    intro cl hcl l hl
    unfold F' stateClausesCore at hcl
    rcases List.mem_append.mp hcl with hb | ha
    · exact hcv ▸ (hbin_ent cl hb).1 l hl
    · exact hcv ▸ (har_ent cl ha).1 l hl
  have hunsat : (cnfOfClauses F').Unsat → F0.Unsat := by
    intro hu
    apply hext.2
    rw [CNF.unsat_iff_not_sat]
    intro α hα
    apply (CNF.unsat_iff_not_sat.mp hu) (fun v => α (inv[v]?.getD 0#32).toNat)
    rw [cnf_sat_cnfOfClauses_iff]
    intro cl hcl
    have hent_un : (cnfOfClauses F_cur).EntailsClause (cnfClause (cl.map (compactUnmapLit inv))) :=
      by
        unfold F' stateClausesCore at hcl
        rcases List.mem_append.mp hcl with hb | ha
        · exact (hbin_ent cl hb).2
        · exact (har_ent cl ha).2
    have hsat_un := CNF.entails_clause_def.mp hent_un α hα
    rw [clause_sat_cnfClause_iff] at hsat_un ⊢
    obtain ⟨l', hl', hev⟩ := hsat_un
    rw [List.mem_map] at hl'
    obtain ⟨l, hl, rfl⟩ := hl'
    refine ⟨l, hl, ?_⟩
    simpa [litVar, litSign, compactUnmapLit_div2, compactUnmapLit_mod2] using hev
  have hwat : ModeWatchesInv F' k := by
    simp only [ModeWatchesInv, hdm, ↓reduceIte]
    refine ⟨hbin.layout, fun l hl => ?_⟩
    have hl' : l < 2 * ncv := hcv ▸ hl
    refine compactUnmapBinSliceOk_to_watch hcv (hbin.slices l hl') fun cl hcl => ?_
    refine entails_clause_of_cnfOfClauses_mem (List.mem_append_left _ ?_)
    unfold binClausesCore; rw [List.mem_flatMap]
    exact ⟨l, List.mem_range.mpr hl, hcl⟩
  have hfa : FullArenaClausesInv c F' k :=
    compactArena_to_fullArena har hcv fun r hr =>
      entails_clause_of_cnfOfClauses_mem
        (List.mem_append_right _ (by unfold arenaClausesCore; exact List.mem_map.mpr ⟨r, hr, rfl⟩))
  exact ⟨⟨hvars_b, hunsat⟩, fun hne => absurd hinc hne, hfa, hwat, by omega,
    fun _ h => by omega, fun _ _ h => by omega, fun l hl => Or.inl (hvals l (hcv ▸ hl)),
    fun l hl =>
      ⟨(fun h1 => by rw [hvals l (hcv ▸ hl)] at h1; cases h1),
       (fun hex => by obtain ⟨_, hi, _⟩ := hex; omega)⟩,
    fun l hl =>
      ⟨(fun h1 => by rw [hvals l (hcv ▸ hl)] at h1; cases h1),
       (fun hex => by obtain ⟨_, hi, _⟩ := hex; omega)⟩,
    fun _ h => by omega, fun _ _ _ h => by omega, fun _ _ h2 => by omega,
    fun _ h => by omega, fun _ h => by omega, fun _ h => by omega,
    fun L hL => by
      have : L = 0 := by omega
      subst this; rw [hft0]; omega,
    fun L1 L2 _ hL2 => by
      have : L1 = 0 := by omega
      have : L2 = 0 := by omega
      subst L1; subst L2; exact Nat.le_refl _,
    fun L hL1 hL2 _ _ => by omega,
    fun L hL1 hL2 => by omega,
    fun _ h => by omega,
    fun _ h => by omega⟩

/-- Builds a post-compaction `FullWitnessInv` for `[[]]` when `F0.Unsat` (e.g. root empty clause
discovered during arena compaction). -/
theorem fullWitnessInv_compact_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ncv : Nat} {inv : List (BitVec 32)} {k : FullCoreState}
    (hu : F0.Unsat) (hbin : CompactUnmapBinsOk ncv inv F_cur k)
    (har : CompactArenaOk c ncv inv F_cur k) (hcv : k.cur_vars = ncv)
    (hdm : k.dense_mode = 0#64) (hte : k.trail_end = 0) (hcl : k.cur_level = 0)
    (hft0 : (k.frame_trail[0]?.getD 0#32).toNat = 0)
    (hvals : ∀ l < 2 * ncv, k.vals[l]?.getD 0#8 = 0#8) :
    FullWitnessInv c F0 [[]] k := by
  have hwat : ModeWatchesInv [[]] k := by
    simp only [ModeWatchesInv, hdm, ↓reduceIte]
    refine ⟨hbin.layout, fun l hl => ?_⟩
    exact compactUnmapBinSliceOk_to_watch hcv (hbin.slices l (hcv ▸ hl)) fun cl _ =>
      entails_of_unsat unsat_nil_clauses _
  have hfa : FullArenaClausesInv c [[]] k :=
    compactArena_to_fullArena har hcv fun _ _ => entails_of_unsat unsat_nil_clauses _
  exact ⟨⟨fun _ hc => by simp at hc; subst hc; exact fun _ h => by simp at h, fun _ => hu⟩,
    fun _ => unsat_nil_clauses, hfa, hwat, by omega,
    fun _ h => by omega, fun _ _ h => by omega, fun l hl => Or.inl (hvals l (hcv ▸ hl)),
    fun l hl =>
      ⟨(fun h1 => by rw [hvals l (hcv ▸ hl)] at h1; cases h1),
       (fun hex => by obtain ⟨_, hi, _⟩ := hex; omega)⟩,
    fun l hl =>
      ⟨(fun h1 => by rw [hvals l (hcv ▸ hl)] at h1; cases h1),
       (fun hex => by obtain ⟨_, hi, _⟩ := hex; omega)⟩,
    fun _ h => by omega, fun _ _ _ h => by omega, fun _ _ h2 => by omega,
    fun _ h => by omega, fun _ h => by omega, fun _ h => by omega,
    fun L hL => by
      have : L = 0 := by omega
      subst this; rw [hft0]; omega,
    fun L1 L2 _ hL2 => by
      have : L1 = 0 := by omega
      have : L2 = 0 := by omega
      subst L1; subst L2; exact Nat.le_refl _,
    fun L hL1 hL2 _ _ => by omega,
    fun L hL1 hL2 => by omega,
    fun _ h => by omega,
    fun _ h => by omega⟩

/-! ## 5. `FullMem` / `FullM6HdrMem` Focus & Config Compatibility Helpers -/

theorem compactMem_cast {c : FullCfg} {s s' : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) (heq : s = s') : (FullMem c s' ⋆ R) m :=
  heq ▸ hm

theorem FullM6HdrCfgOk_of_compat {c c' : FullCfg} (hcmp : FullCfgCompat c c')
    (hcfg : FullM6HdrCfgOk c) : FullM6HdrCfgOk c' := by
  unfold FullM6HdrCfgOk at hcfg ⊢
  rwa [hcmp.hdr]

/-- Non-`q_stamp`/non-`wsort` remainder of `FullMem` for `full_compact_vmtf` array focusing. -/
@[expose] def CompactVmtfRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
  FullScrByteArrs c s.scratch ⋆
  (array (t := i32) c.pHeap s.scratch.heap ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
    array (t := i32) c.pShrinkStk s.scratch.shrink_stk ⋆
    array (t := i32) c.pQPrev s.scratch.q_prev ⋆ array (t := i32) c.pQNext s.scratch.q_next) ⋆
  (array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
    array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
    array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
    array (t := i32) c.pTarjanReach s.scratch.tarjan_reach) ⋆
  FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch ⋆ c.pad

theorem focus_vmtf_arrays {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
      array (t := i32) c.pWsort s.scratch.wsort ⋆ (CompactVmtfRest c s ⋆ R)) m := by
  unfold FullMem FullScratchArrays FullScrU32A FullScrWksArrs at hm
  unfold CompactVmtfRest
  exact sep_ac hm

theorem unfocus_vmtf_arrays {c : FullCfg} {s : FullState} {ws' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
      array (t := i32) c.pWsort ws' ⋆ (CompactVmtfRest c s ⋆ R)) m) :
    (FullMem c { s with scratch := { s.scratch with wsort := ws' } } ⋆ R) m := by
  have hhdr : hdrTailWords c { s with scratch := { s.scratch with wsort := ws' } } =
      hdrTailWords c s := rfl
  unfold FullMem FullScratchArrays FullScrU32A FullScrWksArrs
  rw [hhdr]
  unfold CompactVmtfRest at hm
  exact sep_ac hm

/-- Non-`score`/`heap`/`pos` remainder of `FullMem` for `full_compact_heap` array focusing. -/
@[expose] def CompactHeapRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
  FullScrByteArrs c s.scratch ⋆
  (array (t := i32) c.pShrinkStk s.scratch.shrink_stk ⋆
    array (t := i32) c.pQPrev s.scratch.q_prev ⋆
    array (t := i32) c.pQNext s.scratch.q_next ⋆
    array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
  FullScrWksArrs c s.scratch ⋆
  (array64 c.pSimSig s.scratch.sim_sig ⋆
    array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
    array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
  FullScrDynArrs c s.scratch ⋆ c.pad

theorem focus_heap_arrays {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array64 c.pScore s.scratch.score ⋆ array (t := i32) c.pHeap s.scratch.heap ⋆
      array (t := i32) c.pPos s.scratch.pos ⋆ (CompactHeapRest c s ⋆ R)) m := by
  unfold FullMem FullScratchArrays FullScrU32A FullScrMetaArrs at hm
  unfold CompactHeapRest
  exact sep_ac hm

theorem unfocus_heap_arrays {c : FullCfg} {s : FullState} {hp' ps' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array64 c.pScore s.scratch.score ⋆ array (t := i32) c.pHeap hp' ⋆
      array (t := i32) c.pPos ps' ⋆ (CompactHeapRest c s ⋆ R)) m) :
    (FullMem c { s with scratch := { s.scratch with heap := hp', pos := ps' } } ⋆ R) m := by
  have hhdr : hdrTailWords c { s with scratch := { s.scratch with heap := hp', pos := ps' } } =
      hdrTailWords c s := rfl
  unfold FullMem FullScratchArrays FullScrU32A FullScrMetaArrs
  rw [hhdr]
  unfold CompactHeapRest at hm
  exact sep_ac hm

end

end LeanQbe.T.Examples.Kissat.Proof.Compact
