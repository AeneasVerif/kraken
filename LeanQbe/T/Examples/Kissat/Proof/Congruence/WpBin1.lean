module

public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Inv

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Src.Congruence

/-! ## 14. `full_cong_find_units_equivs_wp` (`Spec.fullCongFindUnitsEquivsSpec`) -/

private theorem bv32_and_msb_zero {x : BitVec 32} (h : x.toNat < 2147483648) :
    x &&& 0x80000000#32 = 0#32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, Nat.zero_testBit,
    show (2147483648 : Nat) % 4294967296 = 2 ^ 31 from rfl, Nat.testBit_two_pow]
  by_cases hj : 31 = j
  · subst hj; rw [Nat.testBit_lt_two_pow h]; rfl
  · simp [hj]

private theorem two_mul_or_bit (x b : Nat) (hb : b < 2) : (2 * x) ||| b = 2 * x + b := by
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
  · simp
  · apply Nat.eq_of_testBit_eq; intro j
    cases j with
    | zero =>
      rw [Nat.testBit_or, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
      simp [Nat.mul_mod_right]
    | succ k =>
      have h0 : Nat.testBit 1 (k + 1) = false := by simp [Nat.testBit_succ]
      rw [Nat.testBit_or, h0, Bool.or_false, Nat.testBit_succ, Nat.testBit_succ,
        show (2 * x + 1) / 2 = x by omega, show (2 * x) / 2 = x by omega]

private theorem two_mul_xor_one (x : Nat) : (2 * x) ^^^ 1 = 2 * x + 1 := by
  apply Nat.eq_of_testBit_eq; intro j
  cases j with
  | zero =>
    rw [Nat.testBit_xor, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
    simp [Nat.mul_mod_right]
  | succ k =>
    have h0 : Nat.testBit 1 (k + 1) = false := by simp [Nat.testBit_succ]
    rw [Nat.testBit_xor, h0, Bool.xor_false, Nat.testBit_succ, Nat.testBit_succ,
      show (2 * x + 1) / 2 = x by omega, show (2 * x) / 2 = x by omega]

private theorem nat_xor_one_lt {a n : Nat} (h : a < 2 * n) : a ^^^ 1 < 2 * n := by
  have hm := Nat.div_add_mod a 2
  rcases (by omega : a % 2 = 0 ∨ a % 2 = 1) with h0 | h1
  · rw [show a = 2 * (a / 2) by omega, two_mul_xor_one]; omega
  · have ha : a = (2 * (a / 2)) ^^^ 1 := by rw [two_mul_xor_one]; omega
    rw [ha, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]; omega

private theorem denseWatches_slice {c : FullCfg} {F0 : Std.Sat.CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hinv : FullDenseInvW c F0 F_cur s) {l : Nat} (hl : l < 2 * s.core.cur_vars) :
    fullWatchOffCore s.core l + fullWatchSizeCore s.core l ≤ c.wcap ∧
    DenseWatchSliceOk F_cur s.core l
      (fullWatchOffCore s.core l) (fullWatchSizeCore s.core l) := by
  have hb := fullWatchBounds_of_dense hinv l hl
  have hw := hinv.2.1.watches
  unfold ModeWatchesInv at hw
  have hdm := hinv.2.2.2.2.2.2
  simp only [hdm, ↓reduceIte] at hw
  exact ⟨hb, hw.slices l hl⟩

private theorem wvec_off_eq {k : FullCoreState} {l i : Nat}
    (hi : i = 2 * l) (hb : i < k.wvec.length) :
    (k.wvec[i]'hb).toNat = fullWatchOffCore k l := by
  subst hi; rw [fullWatchOffCore, List.getElem?_eq_getElem hb, Option.getD_some]

private theorem wvec_zext_off_eq {k : FullCoreState} {l i : Nat}
    (hi : i = 2 * l) (hb : i < k.wvec.length) :
    (BitVec.setWidth 64 (k.wvec[i]'hb)).toNat = fullWatchOffCore k l := by
  rw [bv_zext32_toNat]; exact wvec_off_eq hi hb

private theorem wvec_sz_eq {k : FullCoreState} {l i : Nat}
    (hi : i = 2 * l + 1) (hb : i < k.wvec.length) :
    (k.wvec[i]'hb).toNat = fullWatchSizeCore k l := by
  subst hi; rw [fullWatchSizeCore, List.getElem?_eq_getElem hb, Option.getD_some]

private theorem denseSlice_step_aux {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} {lit i end_ n : Nat}
    (hn : n = end_ - i) (hi : i < end_) (hb : end_ ≤ c.wcap) (hwl : k.wstk.length = c.wcap)
    (hslice : DenseWatchSliceOk F_cur k lit i n) :
    i < k.wstk.length ∧
    ((k.wstk[i]'(by omega) &&& 0x80000000#32) ≠ 0#32 →
      let ot := k.wstk[i]'(by omega) &&& 0x7FFFFFFF#32
      ot.toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, ot.toNat]) ∧
      DenseWatchSliceOk F_cur k lit (i + 1) (end_ - (i + 1))) ∧
    ((k.wstk[i]'(by omega) &&& 0x80000000#32) = 0#32 →
      i + 2 ≤ end_ ∧
      ((k.wstk[i + 1]?.getD 0#32 &&& 0x80000000#32) = 0#32) ∧
      DenseWatchSliceOk F_cur k lit (i + 2) (end_ - (i + 2))) := by
  have hi_len : i < k.wstk.length := by omega
  have hw0_eq : ∀ {w : BitVec 32}, k.wstk[i]? = some w → w = k.wstk[i]'hi_len := fun hw =>
    Option.some.inj (hw.symm.trans (List.getElem?_eq_getElem hi_len))
  refine ⟨hi_len, ?_, ?_⟩
  · intro hmsb
    cases hslice with
    | empty => omega
    | bin hw0 _ _ hlt hent hrest =>
      rw [hw0_eq hw0] at hlt hent
      exact ⟨hlt, hent, (fun {r} hh (hr : r = end_ - (i + 1)) => hr ▸ hh) hrest (by omega)⟩
    | occ hw0 _ hf =>
      rw [hw0_eq hw0] at hf; exact absurd hf hmsb
  · intro hz
    cases hslice with
    | empty => omega
    | bin hw0 hf =>
      rw [hw0_eq hw0] at hf; exact absurd hz hf
    | occ hw0 hcref _ _ hlt _ hrest =>
      have hcr_z : k.wstk[i + 1]?.getD 0#32 &&& 0x80000000#32 = 0#32 := by
        rw [hcref, Option.getD_some]; exact bv32_and_msb_zero hlt
      exact ⟨by omega, hcr_z,
        (fun {r} hh (hr : r = end_ - (i + 2)) => hr ▸ hh) hrest (by omega)⟩

private theorem denseSlice_step {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} {lit i end_ : Nat}
    (hi : i < end_) (hb : end_ ≤ c.wcap) (hwl : k.wstk.length = c.wcap)
    (hslice : DenseWatchSliceOk F_cur k lit i (end_ - i)) :
    i < k.wstk.length ∧
    ((k.wstk[i]'(by omega) &&& 0x80000000#32) ≠ 0#32 →
      let ot := k.wstk[i]'(by omega) &&& 0x7FFFFFFF#32
      ot.toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, ot.toNat]) ∧
      DenseWatchSliceOk F_cur k lit (i + 1) (end_ - (i + 1))) ∧
    ((k.wstk[i]'(by omega) &&& 0x80000000#32) = 0#32 →
      i + 2 ≤ end_ ∧
      ((k.wstk[i + 1]?.getD 0#32 &&& 0x80000000#32) = 0#32) ∧
      DenseWatchSliceOk F_cur k lit (i + 2) (end_ - (i + 2))) :=
  denseSlice_step_aux rfl hi hb hwl hslice

private theorem fue_resolve_unit {F : Std.Sat.CNF Nat} {a b : Nat}
    (h1 : F.EntailsClause (cnfClause [a, b]))
    (h2 : F.EntailsClause (cnfClause [a, litNeg b])) :
    F.EntailsClause (cnfClause [a]) := by
  refine entails_of_eval_mem fun α hα => ?_
  have hs1 : clauseEvalVal α [a, b] = true :=
    (clauseEvalVal_iff α [a, b]).mpr (Std.Sat.CNF.entails_clause_def.mp h1 α hα)
  have hs2 : clauseEvalVal α [a, litNeg b] = true :=
    (clauseEvalVal_iff α [a, litNeg b]).mpr (Std.Sat.CNF.entails_clause_def.mp h2 α hα)
  have hm1 : evalLitVal α a = true ∨ evalLitVal α b = true := by
    simpa [clauseEvalVal] using hs1
  have hm2 : evalLitVal α a = true ∨ evalLitVal α (litNeg b) = true := by
    simpa [clauseEvalVal] using hs2
  rcases hm1 with ha | hb
  · exact ⟨a, by simp, ha⟩
  · rcases hm2 with ha | hnb
    · exact ⟨a, by simp, ha⟩
    · rw [evalLitVal_litNeg, hb] at hnb; exact Bool.noConfusion hnb

private theorem fue_self_unit {F : Std.Sat.CNF Nat} {a : Nat}
    (h1 : F.EntailsClause (cnfClause [a, a])) : F.EntailsClause (cnfClause [a]) := by
  refine entails_of_eval_mem fun α hα => ?_
  have hs1 : clauseEvalVal α [a, a] = true :=
    (clauseEvalVal_iff α [a, a]).mpr (Std.Sat.CNF.entails_clause_def.mp h1 α hα)
  have hm1 : evalLitVal α a = true := by simpa [clauseEvalVal] using hs1
  exact ⟨a, by simp, hm1⟩

/-! ### Mark-prefix invariant and transitions -/

private def FueMarkPrefix (wstk : List (BitVec 32)) (lo hi maxv cv lit : Nat)
    (P : Nat → Prop) (F_cur : List (List Nat)) (lm : List (BitVec 8)) : Prop :=
  lm.length = 2 * maxv ∧
  ∀ l < 2 * maxv, lm[l]?.getD 0#8 ≠ 0#8 →
    l < 2 * cv ∧ P l ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, l]) ∧
    ∃ pos, lo ≤ pos ∧ pos < hi ∧
      ∃ w : BitVec 32, wstk[pos]? = some w ∧
        w &&& 0x80000000#32 ≠ 0#32 ∧ (w &&& 0x7FFFFFFF#32).toNat = l

private theorem fueMarkPrefix_init {wstk : List (BitVec 32)} {lo maxv cv lit : Nat}
    {P : Nat → Prop} {F_cur : List (List Nat)} {lm : List (BitVec 8)}
    (hlen : lm.length = 2 * maxv) (hzero : ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8) :
    FueMarkPrefix wstk lo lo maxv cv lit P F_cur lm :=
  ⟨hlen, fun l hl hnz => absurd (hzero l hl) hnz⟩

private theorem fueMarkPrefix_mono {wstk : List (BitVec 32)} {lo hi hi' maxv cv lit : Nat}
    {P : Nat → Prop} {F_cur : List (List Nat)} {lm : List (BitVec 8)}
    (hle : hi ≤ hi') (h : FueMarkPrefix wstk lo hi maxv cv lit P F_cur lm) :
    FueMarkPrefix wstk lo hi' maxv cv lit P F_cur lm :=
  ⟨h.1, fun l hl hnz =>
    let ⟨hcv, hp, hent, pos, h1, h2, w, hw, hm, hot⟩ := h.2 l hl hnz
    ⟨hcv, hp, hent, pos, h1, Nat.lt_of_lt_of_le h2 hle, w, hw, hm, hot⟩⟩

private theorem fueMarkPrefix_set {wstk : List (BitVec 32)} {lo hi maxv cv lit : Nat}
    {P : Nat → Prop} {F_cur : List (List Nat)} {lm : List (BitVec 8)}
    (h : FueMarkPrefix wstk lo hi maxv cv lit P F_cur lm)
    (hle : lo ≤ hi) {w : BitVec 32} (hw : wstk[hi]? = some w) (hmsb : w &&& 0x80000000#32 ≠ 0#32)
    (hot_lt : (w &&& 0x7FFFFFFF#32).toNat < 2 * cv) (_hcv : cv ≤ maxv)
    (hp : P (w &&& 0x7FFFFFFF#32).toNat)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [lit, (w &&& 0x7FFFFFFF#32).toNat])) (v8 : BitVec 8) :
    FueMarkPrefix wstk lo (hi + 1) maxv cv lit P F_cur
      (lm.set (w &&& 0x7FFFFFFF#32).toNat v8) := by
  refine ⟨by rw [List.length_set, h.1], fun l hl hnz => ?_⟩
  by_cases heq : l = (w &&& 0x7FFFFFFF#32).toNat
  · subst heq; exact ⟨hot_lt, hp, hent, hi, hle, by omega, w, hw, hmsb, rfl⟩
  · have hget : (lm.set (w &&& 0x7FFFFFFF#32).toNat v8)[l]? = lm[l]? :=
      List.getElem?_set_ne (Ne.symm heq)
    rw [hget] at hnz
    exact (fueMarkPrefix_mono (by omega) h).2 l hl hnz

private theorem fueMarkPrefix_set_nz {wstk : List (BitVec 32)} {lo end_ maxv cv lit : Nat}
    {P : Nat → Prop} {F_cur : List (List Nat)} {lm : List (BitVec 8)}
    (h : FueMarkPrefix wstk lo end_ maxv cv lit P F_cur lm) {idx : Nat}
    (hidx : idx < 2 * maxv) (hnz_old : lm[idx]?.getD 0#8 ≠ 0#8) (v8 : BitVec 8) :
    FueMarkPrefix wstk lo end_ maxv cv lit P F_cur (lm.set idx v8) := by
  refine ⟨by rw [List.length_set, h.1], fun l hl hnz => ?_⟩
  by_cases heq : l = idx
  · subst heq; exact h.2 l hl hnz_old
  · have hget : (lm.set idx v8)[l]? = lm[l]? := List.getElem?_set_ne (Ne.symm heq)
    rw [hget] at hnz; exact h.2 l hl hnz

private theorem fueClear_step_occ {wstk : List (BitVec 32)} {i end_ maxv cv lit : Nat}
    {P : Nat → Prop} {F_cur : List (List Nat)} {lm : List (BitVec 8)}
    (h : FueMarkPrefix wstk i end_ maxv cv lit P F_cur lm)
    (hmsb0 : (wstk[i]?.getD 0#32 &&& 0x80000000#32) = 0#32)
    (hmsb1 : (wstk[i + 1]?.getD 0#32 &&& 0x80000000#32) = 0#32) :
    FueMarkPrefix wstk (i + 2) end_ maxv cv lit P F_cur lm := by
  refine ⟨h.1, fun l hl hnz => ?_⟩
  obtain ⟨hcv, hp, hent, pos, h1, h2, w, hw, hm, hot⟩ := h.2 l hl hnz
  refine ⟨hcv, hp, hent, pos, ?_, h2, w, hw, hm, hot⟩
  rcases (by omega : pos = i ∨ pos = i + 1 ∨ i + 2 ≤ pos) with rfl | rfl | hge
  · rw [hw, Option.getD_some] at hmsb0; exact absurd hmsb0 hm
  · rw [hw, Option.getD_some] at hmsb1; exact absurd hmsb1 hm
  · exact hge

private theorem fueClear_step_bin_set0 {wstk : List (BitVec 32)} {i end_ maxv cv lit : Nat}
    {P : Nat → Prop} {F_cur : List (List Nat)} {lm : List (BitVec 8)}
    (h : FueMarkPrefix wstk i end_ maxv cv lit P F_cur lm)
    {w : BitVec 32} (hw : wstk[i]? = some w) :
    FueMarkPrefix wstk (i + 1) end_ maxv cv lit P F_cur
      (lm.set (w &&& 0x7FFFFFFF#32).toNat 0#8) := by
  refine ⟨by rw [List.length_set, h.1], fun l hl hnz => ?_⟩
  by_cases heq : l = (w &&& 0x7FFFFFFF#32).toNat
  · subst heq
    by_cases hbd : (w &&& 0x7FFFFFFF#32).toNat < lm.length
    · rw [List.getElem?_set_self hbd, Option.getD_some] at hnz; exact absurd rfl hnz
    · rw [h.1] at hbd; omega
  · rw [List.getElem?_set_ne (Ne.symm heq)] at hnz
    obtain ⟨hcv, hp, hent, pos, h1, h2, w', hw', hm', hot'⟩ := h.2 l hl hnz
    refine ⟨hcv, hp, hent, pos, ?_, h2, w', hw', hm', hot'⟩
    rcases (by omega : pos = i ∨ i + 1 ≤ pos) with rfl | hge
    · rw [hw] at hw'; cases Option.some.inj hw'; exact absurd hot' (Ne.symm heq)
    · exact hge

private theorem fueClear_step_bin_skip {wstk : List (BitVec 32)} {i end_ maxv cv lit : Nat}
    {P : Nat → Prop} {F_cur : List (List Nat)} {lm : List (BitVec 8)}
    (h : FueMarkPrefix wstk i end_ maxv cv lit P F_cur lm)
    {w : BitVec 32} (hw : wstk[i]? = some w)
    (hnot : ¬ P (w &&& 0x7FFFFFFF#32).toNat) :
    FueMarkPrefix wstk (i + 1) end_ maxv cv lit P F_cur lm := by
  refine ⟨h.1, fun l hl hnz => ?_⟩
  obtain ⟨hcv, hp, hent, pos, h1, h2, w', hw', hm', hot'⟩ := h.2 l hl hnz
  refine ⟨hcv, hp, hent, pos, ?_, h2, w', hw', hm', hot'⟩
  rcases (by omega : pos = i ∨ i + 1 ≤ pos) with rfl | hge
  · rw [hw] at hw'; cases Option.some.inj hw'; subst hot'; exact absurd hp hnot
  · exact hge

private theorem fueClear_done {wstk : List (BitVec 32)} {end_ maxv cv lit : Nat}
    {P : Nat → Prop} {F_cur : List (List Nat)} {lm : List (BitVec 8)}
    (h : FueMarkPrefix wstk end_ end_ maxv cv lit P F_cur lm) :
    ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8 := by
  intro l hl
  by_cases hnz : lm[l]?.getD 0#8 = 0#8
  · exact hnz
  · obtain ⟨_, _, _, pos, h1, h2, _⟩ := h.2 l hl hnz
    omega

private theorem fue_dense_with_tmp_lm {c : FullCfg} {F0 : Std.Sat.CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hinv : FullDenseInvW c F0 F_cur s)
    {tmp' : List (BitVec 32)} {lm' : List (BitVec 8)}
    (htl : tmp'.length = c.max_vars) (hlml : lm'.length = 2 * c.max_vars)
    (hclr : ∀ l < 2 * c.max_vars, lm'[l]?.getD 0#8 = 0#8) :
    FullDenseInvW c F0 F_cur
      { core := { s.core with lit_mark := lm', tmp := tmp' }, scratch := s.scratch } :=
  ⟨⟨{ hinv.1.core_ok with lit_mark_len := hlml, tmp_len_arr := htl }, hinv.1.scratch_ok⟩,
    fullWitnessInv_with_tmp_lm hinv.2.1 tmp' lm',
    ⟨hinv.2.2.1.1, hclr⟩, hinv.2.2.2.1, hinv.2.2.2.2.1,
    hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

/-! ### Memory framing for watch loops (`wstk`, `lit_mark`, `tmp`, `wvec`) -/

private def FueFrame (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
    array64 (c.hdr + 32) (hdrTailWords c s)) ⋆
  (array (t := i8) c.pVals s.core.vals ⋆ array (t := i8) c.pMark s.core.mrk) ⋆
  (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
    array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
    array (t := i32) c.pTrailPos s.core.trail_pos ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
  (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
    array (t := i32) c.pFrameDec s.core.frame_dec ⋆
    array (t := i32) c.pRepr s.core.repr ⋆ array (t := i32) c.pMinStk s.core.min_stk) ⋆
  array (t := i32) c.pArena s.core.arena ⋆ FullScratchArrays c s.scratch ⋆ c.pad

private def FueMem (c : FullCfg) (s : FullState)
    (lm : List (BitVec 8)) (tmp : List (BitVec 32)) : Mem 64 → Prop :=
  array (t := i32) c.pWstk s.core.wstk ⋆ array (t := i8) c.pLitMark lm ⋆
    array (t := i32) c.pTmp tmp ⋆ array (t := i32) c.pWvec s.core.wvec ⋆ FueFrame c s

private theorem fullMem_eq_fue (c : FullCfg) (s : FullState) (lm : List (BitVec 8))
    (tmp : List (BitVec 32)) :
    FullMem c { core := { s.core with lit_mark := lm, tmp := tmp }, scratch := s.scratch } =
      FueMem c s lm tmp := by
  let s' : FullState :=
    { core := { s.core with lit_mark := lm, tmp := tmp }, scratch := s.scratch }
  have hhdr : hdrTailWords c s' = hdrTailWords c s := rfl
  unfold FullMem FullCoreArrays FullCoreByteArrs FullCoreU32A FullCoreU32B FullCoreDynArrs
    FueMem FueFrame
  rw [hhdr]; ac_rfl

private theorem fullMem_split_fue {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (FullMem c s ⋆ R) m) : (FueMem c s s.core.lit_mark s.core.tmp ⋆ R) m := by
  rwa [← fullMem_eq_fue c s s.core.lit_mark s.core.tmp]

private theorem fullMem_join_fue {c : FullCfg} {s : FullState} {lm' : List (BitVec 8)}
    {tmp' : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (FueMem c s lm' tmp' ⋆ R) m) :
    (FullMem c { core := { s.core with lit_mark := lm', tmp := tmp' }, scratch := s.scratch } ⋆ R)
      m := by
  rwa [fullMem_eq_fue]

@[local c0_load] private theorem c0_load_fue_wstk {c : FullCfg} {s : FullState}
    {lm : List (BitVec 8)} {tmp : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} (hi : i.toNat < s.core.wstk.length) (hm : (FueMem c s lm tmp ⋆ R) m) :
    loadVal m i32 (c.pWstk + i * 4) = some s.core.wstk[i.toNat] :=
  c0_load_full_wstk (s := { s with core := { s.core with lit_mark := lm, tmp := tmp } })
    hi (fullMem_join_fue hm)

@[local c0_load] private theorem c0_load_fue_wvec {c : FullCfg} {s : FullState}
    {lm : List (BitVec 8)} {tmp : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} (hi : i.toNat < s.core.wvec.length) (hm : (FueMem c s lm tmp ⋆ R) m) :
    loadVal m i32 (c.pWvec + i * 4) = some s.core.wvec[i.toNat] :=
  c0_load_full_wvec (s := { s with core := { s.core with lit_mark := lm, tmp := tmp } })
    hi (fullMem_join_fue hm)

@[local c0_load] private theorem c0_load_fue_lm {c : FullCfg} {s : FullState}
    {lm : List (BitVec 8)} {tmp : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} (hi : i.toNat < lm.length) (hm : (FueMem c s lm tmp ⋆ R) m) :
    loadVal m i8 (c.pLitMark + i) = some lm[i.toNat] :=
  c0_load_full_lit_mark (s := { s with core := { s.core with lit_mark := lm, tmp := tmp } })
    hi (fullMem_join_fue hm)

@[local c0_store] private theorem c0_store_fue_lm {c : FullCfg} {s : FullState}
    {lm : List (BitVec 8)} {tmp : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} (v : BitVec 8) (hi : i.toNat < lm.length) (hm : (FueMem c s lm tmp ⋆ R) m) :
    storeOk m i8 (c.pLitMark + i) ∧
      (FueMem c s (lm.set i.toNat v) tmp ⋆ R) (storeMem m i8 (c.pLitMark + i) v) := by
  have ⟨h1, h2⟩ := c0_store_full_lit_mark
    (s := { s with core := { s.core with lit_mark := lm, tmp := tmp } })
    v hi (fullMem_join_fue hm)
  exact ⟨h1, by rwa [← fullMem_eq_fue c s (lm.set i.toNat v) tmp]⟩

@[local c0_store] private theorem c0_store_fue_tmp {c : FullCfg} {s : FullState}
    {lm : List (BitVec 8)} {tmp : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} (v : BitVec 32) (hi : i.toNat < tmp.length)
    (hm : (FueMem c s lm tmp ⋆ R) m) :
    storeOk m i32 (c.pTmp + i * 4) ∧
      (FueMem c s lm (tmp.set i.toNat v) ⋆ R) (storeMem m i32 (c.pTmp + i * 4) v) := by
  have ⟨h1, h2⟩ := c0_store_full_tmp
    (s := { s with core := { s.core with lit_mark := lm, tmp := tmp } })
    v hi (fullMem_join_fue hm)
  exact ⟨h1, by rwa [← fullMem_eq_fue c s lm (tmp.set i.toNat v)]⟩

/-! ### Lifted loop invariants and pure transition lemmas -/

private def FueStateInv (c : FullCfg) (F0 : Std.Sat.CNF Nat) (F_cur : List (List Nat))
    (s0 s' : FullState) : Prop :=
  FullDenseInvW c F0 F_cur s' ∧
  FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr ∧
  s'.core.cur_vars = s0.core.cur_vars ∧
  s'.core.fuel = s0.core.fuel

private def FueM2Inv (c : FullCfg) (F_cur : List (List Nat)) (sp2 : FullState)
    (v2 : Val i64) (off0 sz0 : Nat) (R : Mem 64 → Prop) :
    Tup Val [i64, .bool] → Mem 64 → Prop := fun (i, mkd, ⟨⟩) mm =>
  ∃ lm', lm'.length = 2 * c.max_vars ∧
    off0 ≤ i.toNat ∧ i.toNat ≤ off0 + sz0 ∧
    DenseWatchSliceOk F_cur sp2.core (2 * v2.toNat) i.toNat (off0 + sz0 - i.toNat) ∧
    FueMarkPrefix sp2.core.wstk off0 i.toNat c.max_vars sp2.core.cur_vars
      (2 * v2.toNat) (fun l => v2.toNat < l / 2) F_cur lm' ∧
    (mkd = false → ∀ l < 2 * c.max_vars, lm'[l]?.getD 0#8 = 0#8) ∧
    (FueMem c sp2 lm' sp2.core.tmp ⋆ R) mm

private def FueS2Inv (c : FullCfg) (F_cur : List (List Nat)) (sp2 : FullState)
    (v2 : Val i64) (lit2 : BitVec 32) (off0 sz0 off1 sz1 : Nat) (R : Mem 64 → Prop) :
    Tup Val [i64, i64] → Mem 64 → Prop := fun (is2, mcnt, ⟨⟩) ms =>
  ∃ lm' tmp', lm'.length = 2 * c.max_vars ∧ tmp'.length = c.max_vars ∧
    off1 ≤ is2.toNat ∧ is2.toNat ≤ off1 + sz1 ∧
    mcnt.toNat ≤ sp2.core.cur_vars ∧
    DenseWatchSliceOk F_cur sp2.core (lit2 ^^^ 1#32).toNat is2.toNat (off1 + sz1 - is2.toNat) ∧
    FueMarkPrefix sp2.core.wstk off0 (off0 + sz0) c.max_vars sp2.core.cur_vars
      (2 * v2.toNat) (fun l => v2.toNat < l / 2) F_cur lm' ∧
    (∀ k < mcnt.toNat, (tmp'[k]?.getD 0#32).toNat < 2 * sp2.core.cur_vars ∧
      LitEquiv (cnfOfClauses F_cur) (2 * v2.toNat) (tmp'[k]?.getD 0#32).toNat) ∧
    (FueMem c sp2 lm' tmp' ⋆ R) ms

private def FueC2Inv (c : FullCfg) (F_cur : List (List Nat)) (sp2 : FullState)
    (v2 : Val i64) (off0 sz0 : Nat) (tmp_s : List (BitVec 32)) (R : Mem 64 → Prop) :
    Tup Val [i64] → Mem 64 → Prop := fun (ic2, ⟨⟩) mc2 =>
  ∃ lm_c, lm_c.length = 2 * c.max_vars ∧
    off0 ≤ ic2.toNat ∧ ic2.toNat ≤ off0 + sz0 ∧
    DenseWatchSliceOk F_cur sp2.core (2 * v2.toNat) ic2.toNat (off0 + sz0 - ic2.toNat) ∧
    FueMarkPrefix sp2.core.wstk ic2.toNat (off0 + sz0) c.max_vars sp2.core.cur_vars
      (2 * v2.toNat) (fun l => v2.toNat < l / 2) F_cur lm_c ∧
    (FueMem c sp2 lm_c tmp_s ⋆ R) mc2

private def FueC1Inv (c : FullCfg) (F_cur : List (List Nat)) (ss : FullState)
    (lit : BitVec 32) (off sz : Nat) (R : Mem 64 → Prop) :
    Tup Val [i64] → Mem 64 → Prop := fun (ic1, ⟨⟩) mc1 =>
  ∃ lm_c, lm_c.length = 2 * c.max_vars ∧
    off ≤ ic1.toNat ∧ ic1.toNat ≤ off + sz ∧
    DenseWatchSliceOk F_cur ss.core lit.toNat ic1.toNat (off + sz - ic1.toNat) ∧
    FueMarkPrefix ss.core.wstk ic1.toNat (off + sz) c.max_vars ss.core.cur_vars
      lit.toNat (fun _ => True) F_cur lm_c ∧
    (FueMem c ss lm_c ss.core.tmp ⋆ R) mc1

private def FueM1Inv (c : FullCfg) (F_cur : List (List Nat)) (ss : FullState)
    (lit : BitVec 32) (off sz : Nat) (R : Mem 64 → Prop) :
    Tup Val [i64] → Mem 64 → Prop := fun (im1, ⟨⟩) mm =>
  ∃ lm', lm'.length = 2 * c.max_vars ∧
    off ≤ im1.toNat ∧ im1.toNat ≤ off + sz ∧
    DenseWatchSliceOk F_cur ss.core lit.toNat im1.toNat (off + sz - im1.toNat) ∧
    FueMarkPrefix ss.core.wstk off im1.toNat c.max_vars ss.core.cur_vars
      lit.toNat (fun _ => True) F_cur lm' ∧
    (FueMem c ss lm' ss.core.tmp ⋆ R) mm

private theorem fue_s2_mark_nz {lm : List (BitVec 8)} {w : BitVec 32}
    (hb : ((w &&& 0x7FFFFFFF#32) ^^^ 1#32).toNat < lm.length)
    (hb' : w.toNat &&& 2147483647 ^^^ 1 < lm.length)
    (hc : BitVec.setWidth 32 (lm[w.toNat &&& 2147483647 ^^^ 1]'hb') = 1#32) :
    lm[((w &&& 0x7FFFFFFF#32) ^^^ 1#32).toNat]?.getD 0#8 ≠ 0#8 := by
  have hidx : w.toNat &&& 2147483647 ^^^ 1 = ((w &&& 0x7FFFFFFF#32) ^^^ 1#32).toNat := by
    rw [BitVec.toNat_xor, BitVec.toNat_and]; rfl
  rw [List.getElem?_eq_getElem hb, Option.getD_some]
  intro h0
  have hc' : BitVec.setWidth 32 (lm[((w &&& 0x7FFFFFFF#32) ^^^ 1#32).toNat]'hb) = 1#32 := by
    simpa only [hidx] using hc
  rw [h0] at hc'; exact absurd hc' (by decide)

private theorem fue_m1_mark_nz {lm : List (BitVec 8)} {w : BitVec 32}
    (hb : ((w &&& 0x7FFFFFFF#32) ^^^ 1#32).toNat < lm.length)
    (hb' : (w &&& 0x7FFFFFFF#32).toNat ^^^ 1 < lm.length)
    (hc : ¬ BitVec.setWidth 32 (lm[(w &&& 0x7FFFFFFF#32).toNat ^^^ 1]'hb') = 0#32) :
    lm[((w &&& 0x7FFFFFFF#32) ^^^ 1#32).toNat]?.getD 0#8 ≠ 0#8 := by
  have hidx : (w &&& 0x7FFFFFFF#32).toNat ^^^ 1 = ((w &&& 0x7FFFFFFF#32) ^^^ 1#32).toNat := by
    rw [BitVec.toNat_xor]; rfl
  rw [List.getElem?_eq_getElem hb, Option.getD_some]
  intro h0; apply hc
  have hc0 : lm[(w &&& 0x7FFFFFFF#32).toNat ^^^ 1]'hb' = 0#8 := by simpa only [hidx] using h0
  rw [hc0]; rfl

private theorem fue_s2_tmp_set {F_cur : List (List Nat)} {cv v2 mcnt : Nat}
    {tmp : List (BitVec 32)} {ot : BitVec 32}
    (hmc_lt : mcnt < tmp.length) (hot_lt : ot.toNat < 2 * cv)
    (hle : LitEquiv (cnfOfClauses F_cur) (2 * v2) ot.toNat)
    (hold : ∀ k < mcnt, (tmp[k]?.getD 0#32).toNat < 2 * cv ∧
      LitEquiv (cnfOfClauses F_cur) (2 * v2) (tmp[k]?.getD 0#32).toNat) :
    ∀ k < mcnt + 1, ((tmp.set mcnt ot)[k]?.getD 0#32).toNat < 2 * cv ∧
      LitEquiv (cnfOfClauses F_cur) (2 * v2) ((tmp.set mcnt ot)[k]?.getD 0#32).toNat := by
  intro k hk
  by_cases hkm : k = mcnt
  · subst hkm
    rw [List.getElem?_eq_getElem (by rw [List.length_set]; exact hmc_lt),
      Option.getD_some, List.getElem_set_self]
    exact ⟨hot_lt, hle⟩
  · rw [List.getElem?_set_ne (Ne.symm hkm)]; exact hold k (by omega)

/-! ### AST projections for Pass 2 and Pass 1 body -/

private def unLet64 (v : Val i64) : Expr Val Cont [i64] → Expr Val Cont [i64]
  | .let_ (ts := [.bits 64]) _ k => k (v, ())
  | e => e

private def unLoad64 (v : Val i64) : Expr Val Cont [i64] → Expr Val Cont [i64]
  | .load (.bits 64) _ k => k v
  | e => e

private def fueAfterPrologue (h cv nl pWvec pWstk pLm pVals pTmp pFlags : Val i64) :
    Expr Val Cont [i64] :=
  unLoad64 pFlags <| unLet64 (h + 800) <|
  unLoad64 pTmp <| unLet64 (h + 136) <|
  unLoad64 pVals <| unLet64 (h + 64) <|
  unLoad64 pLm <| unLet64 (h + 808) <|
  unLoad64 pWstk <| unLet64 (h + 120) <|
  unLoad64 pWvec <| unLet64 (h + 104) <|
  unLet64 nl <| unLet64 1 <|
  unLoad64 cv <| unLet64 (h + 776) <|
  full_cong_find_units_equivs_body Val Cont (h, ())

private def fuePass2Expr (h cv nl pWvec pWstk pLm pVals pTmp pFlags : Val i64) :
    Expr Val Cont [i64] :=
  match fueAfterPrologue h cv nl pWvec pWstk pLm pVals pTmp pFlags with
  | .group (sig := [[.bits 64]]) blks _ =>
    match blks ((fun _ _ => True), ()) with
    | .cons b1 .nil =>
      match b1 (0, ()) with
      | .group (sig := [[]]) blks2 _ =>
        match blks2 ((fun _ _ => True), ()) with
        | .cons b2 .nil => b2 ()
      | _ => .ret (.imm 0, ())
  | _ => .ret (.imm 0, ())

private def fuePass1BodyExpr (h cv nl pWvec pWstk pLm pVals pTmp pFlags : Val i64)
    (Jp1 : Cont [i64]) (Jp2 : Cont []) (v1 : Val i64) : Expr Val Cont [i64] :=
  match fueAfterPrologue h cv nl pWvec pWstk pLm pVals pTmp pFlags with
  | .group (sig := [[.bits 64]]) blks _ =>
    match blks (Jp1, ()) with
    | .cons b1 .nil =>
      match b1 (v1, ()) with
      | .group (sig := [[]]) _ body => body (Jp2, ())
      | _ => .ret (.imm 0, ())
  | _ => .ret (.imm 0, ())

private theorem fue_pass2_wp (Γ : Env)
    (hEquiv : Γ.Has "full_cong_equiv_fold" Spec.fullCongEquivFoldSpec)
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {cv nl : Val i64}
    (hmax32 : 2 * c.max_vars < 4294967296) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hcv64 : cv.toNat = s.core.cur_vars) (hnl64 : nl.toNat = 2 * s.core.cur_vars)
    (hwcap32 : c.wcap < 4294967296)
    {sp2_0 : FullState} {mp2_0 : Mem 64}
    (hsp2_0 : FueStateInv c F0 F_cur s sp2_0) (hmp2_0 : (FullMem c sp2_0 ⋆ R) mp2_0)
    (hQ : ∀ r s' m', FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (fuePass2Expr c.hdr cv nl c.pWvec c.pWstk c.pLitMark c.pVals c.pTmp c.pFlags)
      mp2_0 := by
  unfold fuePass2Expr fueAfterPrologue unLoad64 unLet64
  let P_st : Tup Val [] → Mem 64 → Prop := fun _ mst =>
    ∃ sst, FueStateInv c F0 F_cur s sst ∧ (FullMem c sst ⋆ R) mst
  let I_p2 : Tup Val [i64] → Mem 64 → Prop := fun (v2, ⟨⟩) mp2 =>
    ∃ sp2, FueStateInv c F0 F_cur s sp2 ∧ v2.toNat ≤ sp2.core.cur_vars ∧
      (FullMem c sp2 ⋆ R) mp2
  refine wp_loop_inv I_p2 (fun (v2, ⟨⟩) _ => s.core.cur_vars - v2.toNat) ?_ ?_
  · intro Jp2_l hJp2_l; c0_hsteps!
    exact hJp2_l (0#64, ()) mp2_0 ⟨sp2_0, hsp2_0, Nat.zero_le _, hmp2_0⟩
  · rintro Jp2_l ⟨v2, ⟨⟩⟩ mp2 ⟨sp2, ⟨hsp2, hrsp2, hcv2, hfu2⟩, hv2_le, hmp2⟩ ihp2
    refine wp_join_group (ts := []) P_st ?_ ?_
    · rintro Jex ⟨⟩ me ⟨se, ⟨hse, hrse, hcv_e, hfu_e⟩, hme⟩
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (fun (r, ()) mf =>
        ∃ sf, FueStateInv c F0 F_cur s sf ∧ (r = 1#64 ∨ r = 20#64) ∧
          (r = 20#64 → F0.Unsat) ∧ (FullMem c sf ⋆ R) mf) ?_ ?_
      · rintro _ ⟨r, ⟨⟩⟩ mf ⟨sf, ⟨hsf, hrsf, hcvs, hfus⟩, hr, huns, hmf⟩
        c0_hsteps!; exact hQ r sf mf hsf hcvs hfus hrsf hr huns hmf
      · intro Jret hJret; c0_hsteps!
        · exact hJret (20#64, ()) me ⟨se, ⟨hse, hrse, hcv_e, hfu_e⟩, Or.inr rfl,
            fun _ => unsat_of_inconsistent_w hse.2.1 hc, hme⟩
        · exact hJret (1#64, ()) me ⟨se, ⟨hse, hrse, hcv_e, hfu_e⟩, Or.inl rfl,
            fun h => absurd h (by decide), hme⟩
    · intro Jex hJex; c0_hsteps_nogrp
      · have hv2_lt : v2.toNat < sp2.core.cur_vars := by omega
        have hv2_1 : (v2 + 1#64).toNat = v2.toNat + 1 := by bv_omega
        have hfl2 : v2.toNat < sp2.core.flags.length := by
          rw [hsp2.1.core_ok.flags_len]; omega
        have hv2s : (v2 <<< (BitVec.signExtend 64 1#32)).toNat = 2 * v2.toNat := by
          change (v2 <<< 1#64).toNat = 2 * v2.toNat; exact bv64_shl1_lt (by omega)
        have hval2 : (v2 <<< (BitVec.signExtend 64 1#32)).toNat < sp2.core.vals.length := by
          rw [hv2s, hsp2.1.core_ok.vals_len]; omega
        refine wp_join_group (ts := []) P_st ?_ ?_
        · rintro _ ⟨⟩ m_c ⟨sc, hsc, hmc⟩; c0_hsteps!
          exact ihp2 (v2 + 1#64, ()) m_c (by dsimp only; omega)
            ⟨sc, hsc, by rw [hv2_1, hsc.2.2.1, ← hcv2]; omega, hmc⟩
        · intro Jc2 hJc2; c0_hsteps_nogrp
          · exact hJc2 () mp2 ⟨sp2, ⟨hsp2, hrsp2, hcv2, hfu2⟩, hmp2⟩
          · exact hJc2 () mp2 ⟨sp2, ⟨hsp2, hrsp2, hcv2, hfu2⟩, hmp2⟩
          · clear hc
            have hlit2_lt : 2 * v2.toNat < 2 * sp2.core.cur_vars := by omega
            let lit2 := (v2 <<< 1#64).setWidth 32
            have hlit2_nat : lit2.toNat = 2 * v2.toNat := by
              dsimp only [lit2]; change (v2 <<< 1#64).toNat % 4294967296 = _
              rw [bv64_shl1_lt (by omega)]; exact Nat.mod_eq_of_lt (by omega)
            have hlit2_shl : ((lit2.setWidth 64 <<< 1#64)).toNat = 2 * lit2.toNat := by
              rw [bv64_shl1_lt (by rw [bv_zext32_toNat]; omega), bv_zext32_toNat]
            have hwv2_0 : ((lit2.setWidth 64 <<< 1#64)).toNat < sp2.core.wvec.length := by
              rw [hlit2_shl, hlit2_nat, hsp2.1.core_ok.wvec_len]; omega
            have hwv2_1 : (((lit2.setWidth 64 <<< 1#64) + 1#64)).toNat <
                sp2.core.wvec.length := by
              rw [bv64_add1_lt (by rw [hlit2_shl]; omega), hlit2_shl, hlit2_nat,
                hsp2.1.core_ok.wvec_len]; omega
            have hnlit2_nat : (lit2 ^^^ 1#32).toNat = 2 * v2.toNat + 1 := by
              rw [bv32_xor1_eq_litNeg]; change lit2.toNat ^^^ 1 = _
              rw [hlit2_nat, two_mul_xor_one]
            have hnlit2_lt : (lit2 ^^^ 1#32).toNat < 2 * sp2.core.cur_vars := by
              rw [hnlit2_nat]; omega
            have hnlit2_shl : (((lit2 ^^^ 1#32).setWidth 64 <<< 1#64)).toNat =
                2 * (lit2 ^^^ 1#32).toNat := by
              rw [bv64_shl1_lt (by rw [bv_zext32_toNat]; omega), bv_zext32_toNat]
            have hwv2_2 : (((lit2 ^^^ 1#32).setWidth 64 <<< 1#64)).toNat <
                sp2.core.wvec.length := by
              rw [hnlit2_shl, hsp2.1.core_ok.wvec_len]; omega
            have hwv2_3 : ((((lit2 ^^^ 1#32).setWidth 64 <<< 1#64) + 1#64)).toNat <
                sp2.core.wvec.length := by
              rw [bv64_add1_lt (by rw [hnlit2_shl]; omega), hnlit2_shl,
                hsp2.1.core_ok.wvec_len]; omega
            obtain ⟨hb2_0, hsl2_0⟩ := denseWatches_slice hsp2 hlit2_lt
            obtain ⟨hb2_1, hsl2_1⟩ := denseWatches_slice hsp2 hnlit2_lt
            let off0 := fullWatchOffCore sp2.core (2 * v2.toNat)
            let sz0 := fullWatchSizeCore sp2.core (2 * v2.toNat)
            let off1 := fullWatchOffCore sp2.core (lit2 ^^^ 1#32).toNat
            let sz1 := fullWatchSizeCore sp2.core (lit2 ^^^ 1#32).toNat
            have hi0_eq : (lit2.setWidth 64 <<< 1#64).toNat = 2 * (2 * v2.toNat) := by
              rw [hlit2_shl, hlit2_nat]
            have hmp2_f := fullMem_split_fue hmp2
            c0_hsteps_nogrp
            -- Pass 2 Mark (`lit2` watches)
            refine wp_loop_inv (FueM2Inv c F_cur sp2 v2 off0 sz0 R)
              (fun (i, _, ⟨⟩) _ => off0 + sz0 - i.toNat) ?_ ?_
            · intro Jm2 hJm2; c0_hsteps!
              refine hJm2 _ mp2 ⟨sp2.core.lit_mark, hsp2.1.core_ok.lit_mark_len,
                ?_, ?_, ?_, ?_, fun _ => hsp2.2.2.1.2, hmp2_f⟩
              · rw [wvec_zext_off_eq (l := 2 * v2.toNat) ?_]; exact Nat.le_refl _; exact hi0_eq
              · rw [wvec_zext_off_eq (l := 2 * v2.toNat) ?_]; omega; exact hi0_eq
              · rw [wvec_zext_off_eq (l := 2 * v2.toNat) ?_]
                · have : off0 + sz0 - off0 = sz0 := by omega
                  rw [this]; exact hsl2_0
                · exact hi0_eq
              · rw [wvec_zext_off_eq (l := 2 * v2.toNat) ?_]
                · exact fueMarkPrefix_init hsp2.1.core_ok.lit_mark_len hsp2.2.2.1.2
                · exact hi0_eq
            · rintro Jm2 ⟨im2, mkd, ⟨⟩⟩ mm
                ⟨lm', hlml, him_lo, him_hi, hslm, hpref, hmkf, hmm⟩ ihm2
              c0_hsteps_nogrp
              · have him_lt : im2.toNat < off0 + sz0 := by
                  rw [wvec_off_eq (l := 2 * v2.toNat) (by omega),
                    wvec_sz_eq (l := 2 * v2.toNat)
                      (by rw [show (1 : BitVec 64).toNat = 1 from rfl]; omega)] at hc
                  omega
                have him2_1 : (im2 + 1#64).toNat = im2.toNat + 1 := by bv_omega
                have him2_2 : (im2 + 2#64).toNat = im2.toNat + 2 := by bv_omega
                have ⟨hi_len, hstep_b, hstep_o⟩ :=
                  denseSlice_step him_lt hb2_0 hsp2.1.core_ok.wstk_len_arr hslm
                c0_hsteps_nogrp
                · have ⟨hi2, _, hsl_r⟩ := hstep_o (by assumption)
                  exact ihm2 (im2 + 2#64, mkd, ()) mm (by dsimp only; omega)
                    ⟨lm', hlml, by rw [him2_2]; omega, by rw [him2_2]; omega,
                      by rw [him2_2]; exact hsl_r,
                      fueMarkPrefix_mono (by rw [him2_2]; omega) hpref, hmkf, hmm⟩
                · have ⟨hot_lt, hent_b, hsl_r⟩ := hstep_b (by assumption)
                  refine wp_join_group (ts := [.bool]) (fun (nmk, ⟨⟩) mm' =>
                    ∃ lm'', lm''.length = 2 * c.max_vars ∧
                      FueMarkPrefix sp2.core.wstk off0 (im2.toNat + 1) c.max_vars
                        sp2.core.cur_vars (2 * v2.toNat) (fun l => v2.toNat < l / 2)
                        F_cur lm'' ∧
                      (nmk = false → ∀ l < 2 * c.max_vars, lm''[l]?.getD 0#8 = 0#8) ∧
                      (FueMem c sp2 lm'' sp2.core.tmp ⋆ R) mm') ?_ ?_
                  · rintro _ ⟨nmk, ⟨⟩⟩ mm' ⟨lm'', hlml'', hpref'', hmkf'', hmm'⟩
                    c0_hsteps!
                    exact ihm2 (im2 + 1#64, nmk, ()) mm' (by dsimp only; omega)
                      ⟨lm'', hlml'', by rw [him2_1]; omega, by rw [him2_1]; omega,
                        by rw [him2_1]; exact hsl_r,
                        by rw [him2_1]; exact hpref'', hmkf'', hmm'⟩
                  · intro Jm2c hJm2c
                    have hot_lm : (sp2.core.wstk[im2.toNat]'hi_len &&& 0x7FFFFFFF#32).toNat <
                        lm'.length := by rw [hlml]; omega
                    c0_hsteps_nogrp
                    · let ot := sp2.core.wstk[im2.toNat]'hi_len &&& 0x7FFFFFFF#32
                      have hot_div : v2.toNat < ot.toNat / 2 := hc
                      clear hc; c0_hsteps_nogrp
                      exact hJm2c (true, ()) _ ⟨_, by rw [List.length_set, hlml],
                        fueMarkPrefix_set hpref him_lo (List.getElem?_eq_getElem hi_len)
                          (by assumption) hot_lt (hcv2 ▸ hcv_le) hot_div hent_b 1#8,
                        fun hf => Bool.noConfusion hf, ‹_›⟩
                    · exact hJm2c (mkd, ()) mm
                        ⟨lm', hlml, fueMarkPrefix_mono (by omega) hpref, hmkf, hmm⟩
              · -- Mark exited (`im2 = off0 + sz0`)
                have him_eq : im2.toNat = off0 + sz0 := by
                  rw [wvec_off_eq (l := 2 * v2.toNat) (by omega),
                    wvec_sz_eq (l := 2 * v2.toNat)
                      (by rw [show (1 : BitVec 64).toNat = 1 from rfl]; omega)] at hc
                  omega
                rw [him_eq] at hpref
                refine wp_join_group (ts := [i64, i64]) (fun _ mc' =>
                  ∃ sc, FueStateInv c F0 F_cur s sc ∧ (FullMem c sc ⋆ R) mc') ?_ ?_
                · rintro _ ⟨_, _, ⟨⟩⟩ mc' ⟨sc, hsc, hmc'⟩; c0_hsteps!
                  exact ihp2 (v2 + 1#64, ()) mc' (by dsimp only; omega)
                    ⟨sc, hsc, by rw [hv2_1, hsc.2.2.1, ← hcv2]; omega, hmc'⟩
                · intro Jc_p2 hJc_p2; c0_hsteps_nogrp
                  · clear hc -- `marked = true`: Scan -> Clear -> Equiv
                    refine wp_loop_inv (FueS2Inv c F_cur sp2 v2 lit2 off0 sz0 off1 sz1 R)
                      (fun (is2, _, ⟨⟩) _ => off1 + sz1 - is2.toNat) ?_ ?_
                    · intro Js2 hJs2; c0_hsteps!
                      refine hJs2 _ mm ⟨lm', sp2.core.tmp, hlml, hsp2.1.core_ok.tmp_len_arr,
                        ?_, ?_, Nat.zero_le _, ?_, hpref,
                        fun _ hk => absurd hk (Nat.not_lt_zero _), hmm⟩
                      · rw [wvec_zext_off_eq (l := (lit2 ^^^ 1#32).toNat) ?_]
                        exact Nat.le_refl _; exact hnlit2_shl
                      · rw [wvec_zext_off_eq (l := (lit2 ^^^ 1#32).toNat) ?_]
                        omega; exact hnlit2_shl
                      · rw [wvec_zext_off_eq (l := (lit2 ^^^ 1#32).toNat) ?_]
                        · have : off1 + sz1 - off1 = sz1 := by omega
                          rw [this]; exact hsl2_1
                        · exact hnlit2_shl
                    · rintro Js2 ⟨is2, mcnt, ⟨⟩⟩ ms
                        ⟨lm_s, tmp_s, hlms, htmps, his_lo, his_hi, hmc_le, hsl_s,
                         hpref_s, htmp_eq, hms⟩ ihs2
                      c0_hsteps_nogrp
                      · have his_lt : is2.toNat < off1 + sz1 := by
                          have hx : (2 * v2.toNat % 2^64 % 2^32) ^^^ 1 = 2 * v2.toNat + 1 := by
                            rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
                              two_mul_xor_one]
                          rw [wvec_off_eq (l := (lit2 ^^^ 1#32).toNat)
                              (by rw [hnlit2_nat, hx]; omega),
                            wvec_sz_eq (l := (lit2 ^^^ 1#32).toNat) (by
                              rw [hnlit2_nat, hx, show (1 : BitVec 64).toNat = 1 from rfl]
                              omega)] at hc
                          omega
                        have his2_1 : (is2 + 1#64).toNat = is2.toNat + 1 := by bv_omega
                        have his2_2 : (is2 + 2#64).toNat = is2.toNat + 2 := by bv_omega
                        have ⟨his_len, hstep_b, hstep_o⟩ :=
                          denseSlice_step his_lt hb2_1 hsp2.1.core_ok.wstk_len_arr hsl_s
                        c0_hsteps_nogrp
                        · have ⟨_, _, hsl_r⟩ := hstep_o (by assumption)
                          exact ihs2 (is2 + 2#64, mcnt, ()) ms (by dsimp only; omega)
                            ⟨lm_s, tmp_s, hlms, htmps, by rw [his2_2]; omega,
                              by rw [his2_2]; omega, hmc_le, by rw [his2_2]; exact hsl_r,
                              hpref_s, htmp_eq, hms⟩
                        · have ⟨hot_lt, hent_b, hsl_r⟩ := hstep_b (by assumption)
                          refine wp_join_group (ts := [i64]) (fun (nmc, ⟨⟩) ms' =>
                            ∃ lm_n tmp_n, lm_n.length = 2 * c.max_vars ∧
                              tmp_n.length = c.max_vars ∧ nmc.toNat ≤ sp2.core.cur_vars ∧
                              FueMarkPrefix sp2.core.wstk off0 (off0 + sz0) c.max_vars
                                sp2.core.cur_vars (2 * v2.toNat) (fun l => v2.toNat < l / 2)
                                F_cur lm_n ∧
                              (∀ k < nmc.toNat,
                                (tmp_n[k]?.getD 0#32).toNat < 2 * sp2.core.cur_vars ∧
                                LitEquiv (cnfOfClauses F_cur) (2 * v2.toNat)
                                  (tmp_n[k]?.getD 0#32).toNat) ∧
                              (FueMem c sp2 lm_n tmp_n ⋆ R) ms') ?_ ?_
                          · rintro _ ⟨nmc, ⟨⟩⟩ ms'
                              ⟨lm_n, tmp_n, hlmn, htmpn, hnmc_le, hpref_n, htmp_n, hms'⟩
                            c0_hsteps!
                            exact ihs2 (is2 + 1#64, nmc, ()) ms' (by dsimp only; omega)
                              ⟨lm_n, tmp_n, hlmn, htmpn, by rw [his2_1]; omega,
                                by rw [his2_1]; omega, hnmc_le, by rw [his2_1]; exact hsl_r,
                                hpref_n, htmp_n, hms'⟩
                          · intro Js2c hJs2c
                            let ot := sp2.core.wstk[is2.toNat]'his_len &&& 0x7FFFFFFF#32
                            have hot_x_lt : (ot ^^^ 1#32).toNat < 2 * sp2.core.cur_vars := by
                              rw [bv32_xor1_eq_litNeg]; exact nat_xor_one_lt hot_lt
                            have hot_x_lm : (ot ^^^ 1#32).toNat < lm_s.length := by
                              rw [hlms]; omega
                            c0_hsteps_nogrp
                            · have hnz_old := fue_s2_mark_nz hot_x_lm (by
                                rw [show (sp2.core.wstk[is2.toNat]'his_len).toNat &&&
                                  2147483647 ^^^ 1 = (ot ^^^ 1#32).toNat by
                                    dsimp only [ot]; rw [BitVec.toNat_xor, BitVec.toNat_and]
                                    rfl]
                                exact hot_x_lm) hc
                              have ⟨_, _, hent_mark, _⟩ := hpref_s.2 (ot ^^^ 1#32).toNat
                                (by omega) hnz_old
                              have hle_eq : LitEquiv (cnfOfClauses F_cur) (2 * v2.toNat)
                                  ot.toNat := by
                                rw [bv32_xor1_eq_litNeg] at hent_mark
                                rw [bv32_xor1_eq_litNeg, hlit2_nat] at hent_b
                                exact ⟨hent_b, hent_mark⟩
                              have hpref3 := fueMarkPrefix_set_nz hpref_s
                                (by rw [← hlms]; exact hot_x_lm) hnz_old 3#8
                              clear hc; c0_hsteps_nogrp
                              refine wp_join_group (ts := [i64]) (fun (nmc, ⟨⟩) ms' =>
                                ∃ tmp_n, tmp_n.length = c.max_vars ∧
                                  nmc.toNat ≤ sp2.core.cur_vars ∧
                                  (∀ k < nmc.toNat,
                                    (tmp_n[k]?.getD 0#32).toNat < 2 * sp2.core.cur_vars ∧
                                    LitEquiv (cnfOfClauses F_cur) (2 * v2.toNat)
                                      (tmp_n[k]?.getD 0#32).toNat) ∧
                                  (FueMem c sp2 (lm_s.set (ot ^^^ 1#32).toNat 3#8) tmp_n ⋆ R)
                                    ms') ?_ ?_
                              · rintro _ ⟨nmc, ⟨⟩⟩ ms' ⟨tmp_n, htmpn, hnmc_le, htmp_n, hms'⟩
                                c0_hsteps!
                                exact hJs2c (nmc, ()) ms' ⟨_, tmp_n,
                                  by rw [List.length_set, hlms], htmpn, hnmc_le,
                                  hpref3, htmp_n, hms'⟩
                              · intro Jmc hJmc; c0_hsteps_nogrp
                                · have hmc_lt : mcnt.toNat < tmp_s.length := by
                                    rw [htmps]; omega
                                  have hmc1 : (mcnt + 1#64).toNat = mcnt.toNat + 1 := by
                                    bv_omega
                                  c0_hsteps_nogrp
                                  exact hJmc (mcnt + 1#64, ()) _
                                    ⟨tmp_s.set mcnt.toNat ot, by rw [List.length_set, htmps],
                                      by rw [hmc1]; omega,
                                      fun k hk => fue_s2_tmp_set hmc_lt hot_lt hle_eq htmp_eq
                                        k (by rwa [hmc1] at hk), ‹_›⟩
                                · exact hJmc (mcnt, ()) _ ⟨tmp_s, htmps, hmc_le, htmp_eq, ‹_›⟩
                            · exact hJs2c (mcnt, ()) ms
                                ⟨lm_s, tmp_s, hlms, htmps, hmc_le, hpref_s, htmp_eq, hms⟩
                            · exact hJs2c (mcnt, ()) ms
                                ⟨lm_s, tmp_s, hlms, htmps, hmc_le, hpref_s, htmp_eq, hms⟩
                      · -- Scan exited -> Clear `lit2` watches
                        refine wp_loop_inv (FueC2Inv c F_cur sp2 v2 off0 sz0 tmp_s R)
                          (fun (ic2, ⟨⟩) _ => off0 + sz0 - ic2.toNat) ?_ ?_
                        · intro Jc2_l hJc2_l; c0_hsteps!
                          refine hJc2_l _ ms ⟨lm_s, hlms, ?_, ?_, ?_, ?_, hms⟩
                          · rw [wvec_zext_off_eq (l := 2 * v2.toNat) ?_]
                            exact Nat.le_refl _; exact hi0_eq
                          · rw [wvec_zext_off_eq (l := 2 * v2.toNat) ?_]; omega; exact hi0_eq
                          · rw [wvec_zext_off_eq (l := 2 * v2.toNat) ?_]
                            · have : off0 + sz0 - off0 = sz0 := by omega
                              rw [this]; exact hsl2_0
                            · exact hi0_eq
                          · rw [wvec_zext_off_eq (l := 2 * v2.toNat) ?_]
                            exact hpref_s; exact hi0_eq
                        · rintro Jc2_l ⟨ic2, ⟨⟩⟩ mc2
                            ⟨lm_c, hlmc, hic_lo, hic_hi, hsl_c, hpref_c, hmc2⟩ ihc2
                          c0_hsteps_nogrp
                          · have hic_lt : ic2.toNat < off0 + sz0 := by
                              rw [wvec_off_eq (l := 2 * v2.toNat) (by omega),
                                wvec_sz_eq (l := 2 * v2.toNat)
                                  (by rw [show (1 : BitVec 64).toNat = 1 from rfl]; omega)]
                                at hc
                              omega
                            have hic2_1 : (ic2 + 1#64).toNat = ic2.toNat + 1 := by bv_omega
                            have hic2_2 : (ic2 + 2#64).toNat = ic2.toNat + 2 := by bv_omega
                            have ⟨hic_len, hstep_b, hstep_o⟩ :=
                              denseSlice_step hic_lt hb2_0 hsp2.1.core_ok.wstk_len_arr hsl_c
                            c0_hsteps_nogrp
                            · have ⟨_, hms1, hsl_r⟩ := hstep_o (by assumption)
                              have hpref_r := fueClear_step_occ hpref_c
                                (by rw [List.getElem?_eq_getElem hic_len, Option.getD_some]
                                    assumption) hms1
                              exact ihc2 (ic2 + 2#64, ()) mc2 (by dsimp only; omega)
                                ⟨lm_c, hlmc, by rw [hic2_2]; omega, by rw [hic2_2]; omega,
                                  by rw [hic2_2]; exact hsl_r,
                                  by rw [hic2_2]; exact hpref_r, hmc2⟩
                            · have ⟨hot_lt, _, hsl_r⟩ := hstep_b (by assumption)
                              refine wp_join_group (ts := []) (fun _ mc2' =>
                                ∃ lm_c', lm_c'.length = 2 * c.max_vars ∧
                                  FueMarkPrefix sp2.core.wstk (ic2.toNat + 1) (off0 + sz0)
                                    c.max_vars sp2.core.cur_vars (2 * v2.toNat)
                                    (fun l => v2.toNat < l / 2) F_cur lm_c' ∧
                                  (FueMem c sp2 lm_c' tmp_s ⋆ R) mc2') ?_ ?_
                              · rintro _ ⟨⟩ mc2' ⟨lm_c', hlmc', hpref_c', hmc2'⟩
                                c0_hsteps!
                                exact ihc2 (ic2 + 1#64, ()) mc2' (by dsimp only; omega)
                                  ⟨lm_c', hlmc', by rw [hic2_1]; omega, by rw [hic2_1]; omega,
                                    by rw [hic2_1]; exact hsl_r,
                                    by rw [hic2_1]; exact hpref_c', hmc2'⟩
                              · intro Jcc hJcc
                                let ot := sp2.core.wstk[ic2.toNat]'hic_len &&& 0x7FFFFFFF#32
                                have hot_lm : ot.toNat < lm_c.length := by
                                  dsimp only [ot]; rw [hlmc]; omega
                                c0_hsteps_nogrp
                                · exact hJcc () _ ⟨_, by rw [List.length_set, hlmc],
                                    fueClear_step_bin_set0 hpref_c
                                      (List.getElem?_eq_getElem hic_len), ‹_›⟩
                                · exact hJcc () mc2 ⟨lm_c, hlmc,
                                    fueClear_step_bin_skip hpref_c
                                      (List.getElem?_eq_getElem hic_len)
                                      (by intro hgt; exact hc hgt), hmc2⟩
                          · -- Clear done -> join FullMem -> Equiv loop `k < mcnt`
                            have hic_eq : ic2.toNat = off0 + sz0 := by
                              rw [wvec_off_eq (l := 2 * v2.toNat) (by omega),
                                wvec_sz_eq (l := 2 * v2.toNat)
                                  (by rw [show (1 : BitVec 64).toNat = 1 from rfl]; omega)]
                                at hc
                              omega
                            rw [hic_eq] at hpref_c
                            have hsp2_clean := fue_dense_with_tmp_lm hsp2 htmps hlmc
                              (fueClear_done hpref_c)
                            let sp2_c : FullState :=
                              { core := { sp2.core with lit_mark := lm_c, tmp := tmp_s }
                                scratch := sp2.scratch }
                            have hmc2_full := fullMem_join_fue hmc2
                            let I_eq : Tup Val [i64] → Mem 64 → Prop := fun (k, ⟨⟩) meq =>
                              ∃ seq, FueStateInv c F0 F_cur s seq ∧
                                seq.core.tmp = tmp_s ∧ k.toNat ≤ mcnt.toNat ∧
                                (FullMem c seq ⋆ R) meq
                            refine wp_loop_inv I_eq (fun (k, ⟨⟩) _ => mcnt.toNat - k.toNat)
                              ?_ ?_
                            · intro Jeq hJeq; c0_hsteps!
                              exact hJeq (0#64, ()) mc2 ⟨sp2_c,
                                ⟨hsp2_clean, hrsp2, hcv2, hfu2⟩, rfl, Nat.zero_le _, hmc2_full⟩
                            · rintro Jeq ⟨k, ⟨⟩⟩ meq
                                ⟨seq, ⟨hseq, hrseq, hcvq, hfuq⟩, htmpq, hk_le, hmeq⟩ iheq
                              c0_hsteps_nogrp
                              · have hk_lt : k.toNat < mcnt.toNat := by assumption
                                have hktmp : k.toNat < seq.core.tmp.length := by
                                  rw [hseq.1.core_ok.tmp_len_arr]; omega
                                clear hc; c0_hsteps_nogrp
                                let ek := seq.core.tmp[k.toNat]'hktmp
                                have hek_eq : ek = tmp_s[k.toNat]'(by rw [htmps]; omega) := by
                                  dsimp only [ek]; simp only [htmpq]
                                have ⟨hek_lt, hek_eqv⟩ := htmp_eq k.toNat hk_lt
                                rw [List.getElem?_eq_getElem (by rw [htmps]; omega),
                                  Option.getD_some, ← hek_eq] at hek_lt hek_eqv
                                have hlit_lt_q : lit2.toNat < 2 * seq.core.cur_vars := by
                                  rw [hlit2_nat, hcvq, ← hcv2]; exact hlit2_lt
                                rw [← hlit2_nat] at hek_eqv
                                refine wp_call_of_spec _ _ ?_
                                exact hEquiv _ _ _ _
                                  ⟨c, F0, F_cur, seq, R, rfl, hseq.1, hseq.2.1, hseq.2.2.1,
                                    hseq.2.2.2.1, hseq.2.2.2.2.1, hseq.2.2.2.2.2.1,
                                    hseq.2.2.2.2.2.2, hrseq, hlit_lt_q,
                                    by rw [hcvq, ← hcv2]; exact hek_lt, hek_eqv, hmeq,
                                    fun r seq' meq' hlq' hwq' hlmq' hnvq' hextq' hclq' hdmq'
                                      hcvq' hfuq' _ _ htmpq' _ hrseq' hr2 h20 hmeq' => by
                                  have hseq' : FullDenseInvW c F0 F_cur seq' :=
                                    ⟨hlq', hwq', hlmq', hnvq', hextq', hclq', hdmq'⟩
                                  c0_hsteps_nogrp
                                  · exact hQ 20#64 seq' meq' hseq' (hcvq'.trans hcvq)
                                      (hfuq'.trans hfuq) hrseq' (Or.inr rfl)
                                      (fun _ => h20 (by assumption)) hmeq'
                                  · have hk1 : (k + 1#64).toNat = k.toNat + 1 := by bv_omega
                                    exact iheq (k + 1#64, ()) meq' (by dsimp only; omega)
                                      ⟨seq', ⟨hseq', hrseq', hcvq'.trans hcvq,
                                        hfuq'.trans hfuq⟩, htmpq'.trans htmpq,
                                        by rw [hk1]; omega, hmeq'⟩⟩
                              · exact hJc_p2 _ meq ⟨seq, ⟨hseq, hrseq, hcvq, hfuq⟩, hmeq⟩
                              · exact hJc_p2 _ meq ⟨seq, ⟨hseq, hrseq, hcvq, hfuq⟩, hmeq⟩
                  · -- `marked = false`
                    have hsp2_m := fue_dense_with_tmp_lm hsp2 hsp2.1.core_ok.tmp_len_arr
                      hlml (hmkf hc)
                    exact hJc_p2 _ mm ⟨_, ⟨hsp2_m, hrsp2, hcv2, hfu2⟩, fullMem_join_fue hmm⟩
      · exact hJex () mp2 ⟨sp2, ⟨hsp2, hrsp2, hcv2, hfu2⟩, hmp2⟩
      · exact hJex () mp2 ⟨sp2, ⟨hsp2, hrsp2, hcv2, hfu2⟩, hmp2⟩

private theorem fue_pass1_body_wp (Γ : Env)
    (hAddUnit : Γ.Has "full_add_unit" fullAddUnitSpec)
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {cv nl : Val i64}
    (hmax32 : 2 * c.max_vars < 4294967296) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hcv64 : cv.toNat = s.core.cur_vars) (hnl64 : nl.toNat = 2 * s.core.cur_vars)
    (hwcap32 : c.wcap < 4294967296)
    {Jp1 : Cont [i64]} {Jp2 : Cont []} {v1 : Val i64} {sp1 : FullState} {mp1 : Mem 64}
    (hsp1 : FueStateInv c F0 F_cur s sp1) (_hv1_le : v1.toNat ≤ sp1.core.cur_vars)
    (hmp1 : (FullMem c sp1 ⋆ R) mp1)
    (ihp1 : ∀ ys m', s.core.cur_vars - ys.1.toNat < s.core.cur_vars - v1.toNat →
      (∃ sp', FueStateInv c F0 F_cur s sp' ∧ ys.1.toNat ≤ sp'.core.cur_vars ∧
        (FullMem c sp' ⋆ R) m') → Jp1 ys m')
    (hJp2 : ∀ xs m', (∃ sst, FueStateInv c F0 F_cur s sst ∧ (FullMem c sst ⋆ R) m') → Jp2 xs m')
    (hQ : ∀ r s' m', FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X
      (fuePass1BodyExpr c.hdr cv nl c.pWvec c.pWstk c.pLitMark c.pVals c.pTmp c.pFlags Jp1 Jp2 v1)
      mp1 := by
  unfold fuePass1BodyExpr fueAfterPrologue unLoad64 unLet64
  let P_st : Tup Val [] → Mem 64 → Prop := fun _ mst =>
    ∃ sst, FueStateInv c F0 F_cur s sst ∧ (FullMem c sst ⋆ R) mst
  c0_hsteps_nogrp
  · have hv1_lt : v1.toNat < sp1.core.cur_vars := by rw [hsp1.2.2.1]; omega
    have hv1_1 : (v1 + 1#64).toNat = v1.toNat + 1 := by bv_omega
    have hfl1 : v1.toNat < sp1.core.flags.length := by
      rw [hsp1.1.1.core_ok.flags_len]; omega
    have hv1s : (v1 <<< (BitVec.signExtend 64 1#32)).toNat = 2 * v1.toNat := by
      change (v1 <<< 1#64).toNat = 2 * v1.toNat; exact bv64_shl1_lt (by omega)
    have hval1 : (v1 <<< (BitVec.signExtend 64 1#32)).toNat < sp1.core.vals.length := by
      rw [hv1s, hsp1.1.1.core_ok.vals_len]; omega
    refine wp_join_group (ts := []) P_st ?_ ?_
    · rintro _ ⟨⟩ m_c ⟨sc, hsc, hmc⟩; c0_hsteps!
      exact ihp1 (v1 + 1#64, ()) m_c (by dsimp only; omega)
        ⟨sc, hsc, by rw [hv1_1, hsc.2.2.1, ← hsp1.2.2.1]; omega, hmc⟩
    · intro Jc1 hJc1; c0_hsteps_nogrp
      · exact hJc1 () mp1 ⟨sp1, hsp1, hmp1⟩
      · exact hJc1 () mp1 ⟨sp1, hsp1, hmp1⟩
      · clear hc
        let I_sgn : Tup Val [i64] → Mem 64 → Prop := fun (sgn, ⟨⟩) ms =>
          ∃ ss, FueStateInv c F0 F_cur s ss ∧ sgn.toNat ≤ 2 ∧ (FullMem c ss ⋆ R) ms
        refine wp_loop_inv I_sgn (fun (sgn, ⟨⟩) _ => 2 - sgn.toNat) ?_ ?_
        · intro Jsgn hJsgn; c0_hsteps!
          exact hJsgn (0#64, ()) mp1 ⟨sp1, hsp1, Nat.zero_le _, hmp1⟩
        · rintro Jsgn ⟨sgn, ⟨⟩⟩ ms ⟨ss, ⟨hss, hrss, hcvs, hfus⟩, hsgn_le, hms⟩ ihsgn
          refine wp_join_group (ts := []) P_st ?_ ?_
          · rintro _ ⟨⟩ msb ⟨ssb, hssb, hmsb⟩; c0_hsteps!
            exact ihp1 (v1 + 1#64, ()) msb (by dsimp only; omega)
              ⟨ssb, hssb, by rw [hv1_1, hssb.2.2.1, ← hsp1.2.2.1]; omega, hmsb⟩
          · intro Jsbrk hJsbrk
            have hv1s' : (v1 <<< (BitVec.signExtend 64 1#32)).toNat = 2 * v1.toNat := hv1s
            have hval1' : (v1 <<< (BitVec.signExtend 64 1#32)).toNat < ss.core.vals.length := by
              rw [hv1s', hss.1.core_ok.vals_len]; omega
            c0_hsteps_nogrp
            · have hsgn_lt : sgn.toNat < 2 := by
                have h : sgn.toNat < (2 : BitVec 64).toNat := by assumption
                simpa using h
              clear hc
              have hsgn_1 : (sgn + 1#64).toNat = sgn.toNat + 1 := by bv_omega
              have hlit_or : ((v1 <<< (1 : BitVec 64)) ||| sgn).toNat =
                  2 * v1.toNat + sgn.toNat := by
                rw [BitVec.toNat_or, show (v1 <<< (1 : BitVec 64)).toNat = 2 * v1.toNat from
                  bv64_shl1_lt (by omega)]
                exact two_mul_or_bit v1.toNat sgn.toNat hsgn_lt
              let lit := ((v1 <<< (1 : BitVec 64)) ||| sgn).setWidth 32
              have hlit_nat : lit.toNat = 2 * v1.toNat + sgn.toNat := by
                dsimp only [lit]
                change ((v1 <<< (1 : BitVec 64)) ||| sgn).toNat % 4294967296 = _
                rw [hlit_or]; exact Nat.mod_eq_of_lt (by omega)
              have hlit_lt : lit.toNat < 2 * ss.core.cur_vars := by rw [hlit_nat]; omega
              have hlit_shl : ((lit.setWidth 64 <<< 1#64)).toNat = 2 * lit.toNat := by
                rw [bv64_shl1_lt (by rw [bv_zext32_toNat]; omega), bv_zext32_toNat]
              have hwv_0 : ((lit.setWidth 64 <<< 1#64)).toNat < ss.core.wvec.length := by
                rw [hlit_shl, hss.1.core_ok.wvec_len]; omega
              have hwv_1 : (((lit.setWidth 64 <<< 1#64) + 1#64)).toNat <
                  ss.core.wvec.length := by
                rw [bv64_add1_lt (by rw [hlit_shl]; omega), hlit_shl,
                  hss.1.core_ok.wvec_len]; omega
              obtain ⟨hb_s, hsl_s⟩ := denseWatches_slice hss hlit_lt
              let off := fullWatchOffCore ss.core lit.toNat
              let sz := fullWatchSizeCore ss.core lit.toNat
              have hms_f := fullMem_split_fue hms
              c0_hsteps_nogrp
              -- Group for Cleanup -> add_unit (`ts := [.bool, i64]`)
              let P_postMk : Tup Val [.bool, i64] → Mem 64 → Prop :=
                fun (fu, _istop, ⟨⟩) mpm =>
                  ∃ lm', lm'.length = 2 * c.max_vars ∧
                    FueMarkPrefix ss.core.wstk off (off + sz) c.max_vars ss.core.cur_vars
                      lit.toNat (fun _ => True) F_cur lm' ∧
                    (fu = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat])) ∧
                    (FueMem c ss lm' ss.core.tmp ⋆ R) mpm
              refine wp_join_group (ts := [.bool, i64]) P_postMk ?_ ?_
              · -- Cleanup loop + `if fu then full_add_unit`
                rintro Jpm ⟨fu, _ist, ⟨⟩⟩ mpm ⟨lm_m, hlmm, hpref_m, hfu_ent, hmpm⟩
                refine wp_loop_inv (FueC1Inv c F_cur ss lit off sz R)
                  (fun (ic1, ⟨⟩) _ => off + sz - ic1.toNat) ?_ ?_
                · intro Jc1_l hJc1_l; c0_hsteps!
                  refine hJc1_l _ mpm ⟨lm_m, hlmm, ?_, ?_, ?_, ?_, hmpm⟩
                  · rw [wvec_zext_off_eq (l := lit.toNat) ?_]
                    exact Nat.le_refl _; exact hlit_shl
                  · rw [wvec_zext_off_eq (l := lit.toNat) ?_]; omega; exact hlit_shl
                  · rw [wvec_zext_off_eq (l := lit.toNat) ?_]
                    · have : off + sz - off = sz := by omega
                      rw [this]; exact hsl_s
                    · exact hlit_shl
                  · rw [wvec_zext_off_eq (l := lit.toNat) ?_]; exact hpref_m; exact hlit_shl
                · rintro Jc1_l ⟨ic1, ⟨⟩⟩ mc1
                    ⟨lm_c, hlmc, hic_lo, hic_hi, hsl_c, hpref_c, hmc1⟩ ihc1
                  c0_hsteps_nogrp
                  · have hic_lt : ic1.toNat < off + sz := by
                      rw [wvec_off_eq (l := lit.toNat) ?_,
                        wvec_sz_eq (l := lit.toNat) ?_] at hc
                      · omega
                      · change (2 * ((v1 <<< (1 : BitVec 64) ||| sgn).toNat % 2^32) +
                          (1 : BitVec 64).toNat) % 2^64 = _
                        rw [hlit_or, hlit_nat, show (1 : BitVec 64).toNat = 1 from rfl]; omega
                      · change 2 * ((v1 <<< (1 : BitVec 64) ||| sgn).toNat % 2^32) % 2^64 = _
                        rw [hlit_or, hlit_nat]; omega
                    have hic1_1 : (ic1 + 1#64).toNat = ic1.toNat + 1 := by bv_omega
                    have hic1_2 : (ic1 + 2#64).toNat = ic1.toNat + 2 := by bv_omega
                    have ⟨hic_len, hstep_b, hstep_o⟩ :=
                      denseSlice_step hic_lt hb_s hss.1.core_ok.wstk_len_arr hsl_c
                    c0_hsteps_nogrp
                    · have ⟨_, hms1, hsl_r⟩ := hstep_o (by assumption)
                      have hpref_r := fueClear_step_occ hpref_c
                        (by rw [List.getElem?_eq_getElem hic_len, Option.getD_some]
                            assumption) hms1
                      exact ihc1 (ic1 + 2#64, ()) mc1 (by dsimp only; omega)
                        ⟨lm_c, hlmc, by rw [hic1_2]; omega, by rw [hic1_2]; omega,
                          by rw [hic1_2]; exact hsl_r,
                          by rw [hic1_2]; exact hpref_r, hmc1⟩
                    · have ⟨hot_lt, _, hsl_r⟩ := hstep_b (by assumption)
                      refine wp_join_group (ts := []) (fun _ mc1' =>
                        ∃ lm_c', lm_c'.length = 2 * c.max_vars ∧
                          FueMarkPrefix ss.core.wstk (ic1.toNat + 1) (off + sz)
                            c.max_vars ss.core.cur_vars lit.toNat (fun _ => True)
                            F_cur lm_c' ∧
                          (FueMem c ss lm_c' ss.core.tmp ⋆ R) mc1') ?_ ?_
                      · rintro _ ⟨⟩ mc1' ⟨lm_c', hlmc', hpref_c', hmc1'⟩; c0_hsteps!
                        exact ihc1 (ic1 + 1#64, ()) mc1' (by dsimp only; omega)
                          ⟨lm_c', hlmc', by rw [hic1_1]; omega, by rw [hic1_1]; omega,
                            by rw [hic1_1]; exact hsl_r,
                            by rw [hic1_1]; exact hpref_c', hmc1'⟩
                      · intro Jcc1 hJcc1
                        let ot := ss.core.wstk[ic1.toNat]'hic_len &&& 0x7FFFFFFF#32
                        have hot_lm : ot.toNat < lm_c.length := by
                          dsimp only [ot]; rw [hlmc]; omega
                        c0_hsteps_nogrp
                        exact hJcc1 () _ ⟨_, by rw [List.length_set, hlmc],
                          fueClear_step_bin_set0 hpref_c (List.getElem?_eq_getElem hic_len),
                          ‹_›⟩
                  · -- Cleanup exited -> join FullMem -> `if fu then full_add_unit`
                    have hic_eq : ic1.toNat = off + sz := by
                      rw [wvec_off_eq (l := lit.toNat) ?_,
                        wvec_sz_eq (l := lit.toNat) ?_] at hc
                      · omega
                      · change (2 * ((v1 <<< (1 : BitVec 64) ||| sgn).toNat % 2^32) +
                          (1 : BitVec 64).toNat) % 2^64 = _
                        rw [hlit_or, hlit_nat, show (1 : BitVec 64).toNat = 1 from rfl]; omega
                      · change 2 * ((v1 <<< (1 : BitVec 64) ||| sgn).toNat % 2^32) % 2^64 = _
                        rw [hlit_or, hlit_nat]; omega
                    rw [hic_eq] at hpref_c
                    have hss_clean := fue_dense_with_tmp_lm hss hss.1.core_ok.tmp_len_arr
                      hlmc (fueClear_done hpref_c)
                    let ss_c : FullState :=
                      { core := { ss.core with lit_mark := lm_c }, scratch := ss.scratch }
                    have hmc1_full := fullMem_join_fue hmc1
                    refine wp_join_group (ts := []) P_st ?_ ?_
                    · rintro _ ⟨⟩ m_n ⟨sn, hsn, hmn⟩; c0_hsteps!
                      exact ihsgn (sgn + 1#64, ()) m_n (by dsimp only; omega)
                        ⟨sn, hsn, by rw [hsgn_1]; omega, hmn⟩
                    · intro Jsn hJsn; c0_hsteps_nogrp
                      · have hfu_t : fu = true := by
                          cases fu
                          · exact absurd hc (by decide)
                          · rfl
                        have hent_u := hfu_ent hfu_t
                        refine wp_call_of_spec _ _ ?_
                        exact hAddUnit _ _ _ _
                          ⟨c, F0, F_cur, ss_c, R, rfl, hss_clean.1, hss_clean.2.1,
                            fun _ => hent_u, hmc1_full,
                            fun ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass'
                              unfl' inc' phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m2
                              hl2 hw2 hcl0 h20 _ hm2 => by
                          let s2 : FullState := {
                            core := { ss_c.core with
                              vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              propagated := prop', cur_level := cl', unassigned := unass',
                              unflushed := unfl', inconsistent := inc' }
                            scratch := { ss_c.scratch with
                              phases := phases', target_assigned := ta', best_assigned := ba',
                              phases_target := pt', phases_best := pb', heap := hp', pos := ps',
                              heap_len := hl', q_search_idx := qsi', q_search_stamp := qss' } }
                          have hs2_dense : FullDenseInvW c F0 F_cur s2 :=
                            ⟨hl2, hw2, fullAddUnitSpec_fullDenseInvW hss_clean.2.2.1
                              hss_clean.2.2.2.1 hss_clean.2.2.2.2.1 hss_clean.2.2.2.2.2.2
                              hcl0 rfl rfl rfl rfl rfl rfl rfl⟩
                          c0_hsteps_nogrp
                          · clear hc; c0_hsteps_nogrp
                            let s2c : FullState :=
                              { s2 with scratch :=
                                { s2.scratch with cong_cnt := s2.scratch.cong_cnt + 1#64 } }
                            exact hJsn () _ ⟨s2c,
                              ⟨fullDenseInvW_with_cong_cnt hs2_dense _, hrss, hcvs, hfus⟩, ‹_›⟩
                          · exact hQ 20#64 s2 m2 hs2_dense hcvs hfus hrss (Or.inr rfl)
                              (fun _ => (h20 hlit_lt (by assumption)).1) hm2⟩
                      · exact hJsn () mc1 ⟨ss_c, ⟨hss_clean, hrss, hcvs, hfus⟩, hmc1_full⟩
              · -- Mark loop (`i` from `off` to `off + sz`)
                intro Jpm hJpm
                refine wp_loop_inv (FueM1Inv c F_cur ss lit off sz R)
                  (fun (im1, ⟨⟩) _ => off + sz - im1.toNat) ?_ ?_
                · intro Jm1 hJm1; c0_hsteps!
                  refine hJm1 _ ms ⟨ss.core.lit_mark, hss.1.core_ok.lit_mark_len,
                    ?_, ?_, ?_, ?_, hms_f⟩
                  · rw [wvec_zext_off_eq (l := lit.toNat) ?_]
                    exact Nat.le_refl _; exact hlit_shl
                  · rw [wvec_zext_off_eq (l := lit.toNat) ?_]; omega; exact hlit_shl
                  · rw [wvec_zext_off_eq (l := lit.toNat) ?_]
                    · have : off + sz - off = sz := by omega
                      rw [this]; exact hsl_s
                    · exact hlit_shl
                  · rw [wvec_zext_off_eq (l := lit.toNat) ?_]
                    · exact fueMarkPrefix_init hss.1.core_ok.lit_mark_len hss.2.2.1.2
                    · exact hlit_shl
                · rintro Jm1 ⟨im1, ⟨⟩⟩ mm ⟨lm', hlml, him_lo, him_hi, hslm, hpref, hmm⟩ ihm1
                  c0_hsteps_nogrp
                  · have him_lt : im1.toNat < off + sz := by
                      rw [wvec_off_eq (l := lit.toNat) ?_,
                        wvec_sz_eq (l := lit.toNat) ?_] at hc
                      · omega
                      · change (2 * ((v1 <<< (1 : BitVec 64) ||| sgn).toNat % 2^32) +
                          (1 : BitVec 64).toNat) % 2^64 = _
                        rw [hlit_or, hlit_nat, show (1 : BitVec 64).toNat = 1 from rfl]; omega
                      · change 2 * ((v1 <<< (1 : BitVec 64) ||| sgn).toNat % 2^32) % 2^64 = _
                        rw [hlit_or, hlit_nat]; omega
                    have him1_1 : (im1 + 1#64).toNat = im1.toNat + 1 := by bv_omega
                    have him1_2 : (im1 + 2#64).toNat = im1.toNat + 2 := by bv_omega
                    have ⟨hi_len, hstep_b, hstep_o⟩ :=
                      denseSlice_step him_lt hb_s hss.1.core_ok.wstk_len_arr hslm
                    c0_hsteps_nogrp
                    · have ⟨_, _, hsl_r⟩ := hstep_o (by assumption)
                      exact ihm1 (im1 + 2#64, ()) mm (by dsimp only; omega)
                        ⟨lm', hlml, by rw [him1_2]; omega, by rw [him1_2]; omega,
                          by rw [him1_2]; exact hsl_r,
                          fueMarkPrefix_mono (by rw [him1_2]; omega) hpref, hmm⟩
                    · have ⟨hot_lt, hent_b, hsl_r⟩ := hstep_b (by assumption)
                      refine wp_join_group (ts := [.bool]) (fun (_stp, ⟨⟩) mm' =>
                        ∃ lm'', lm''.length = 2 * c.max_vars ∧
                          FueMarkPrefix ss.core.wstk off (im1.toNat + 1) c.max_vars
                            ss.core.cur_vars lit.toNat (fun _ => True) F_cur lm'' ∧
                          (FueMem c ss lm'' ss.core.tmp ⋆ R) mm') ?_ ?_
                      · rintro _ ⟨_stp, ⟨⟩⟩ mm' ⟨lm'', hlml'', hpref'', hmm'⟩; c0_hsteps!
                        exact ihm1 (im1 + 1#64, ()) mm' (by dsimp only; omega)
                          ⟨lm'', hlml'', by rw [him1_1]; omega, by rw [him1_1]; omega,
                            by rw [him1_1]; exact hsl_r, by rw [him1_1]; exact hpref'', hmm'⟩
                      · intro Jm1c hJm1c
                        let ot := ss.core.wstk[im1.toNat]'hi_len &&& 0x7FFFFFFF#32
                        have hot_lm : ot.toNat < lm'.length := by
                          dsimp only [ot]; rw [hlml]; omega
                        have hot_x_lt : (ot ^^^ 1#32).toNat < 2 * ss.core.cur_vars := by
                          rw [bv32_xor1_eq_litNeg]; exact nat_xor_one_lt hot_lt
                        have hot_x_lm : (ot ^^^ 1#32).toNat < lm'.length := by
                          rw [hlml]; omega
                        c0_hsteps_nogrp
                        · have heq_l : ot.toNat = lit.toNat :=
                            congrArg BitVec.toNat (by assumption : ot = lit)
                          rw [heq_l] at hent_b
                          exact hJpm (true, _, ()) mm
                            ⟨lm', hlml, fueMarkPrefix_mono (by omega) hpref,
                              fun _ => fue_self_unit hent_b, hmm⟩
                        · have hnz_o := fue_m1_mark_nz hot_x_lm (by
                            rw [show (ss.core.wstk[im1.toNat]'hi_len &&& 0x7FFFFFFF#32).toNat ^^^
                              1 = (ot ^^^ 1#32).toNat by
                                dsimp only [ot]; rw [BitVec.toNat_xor]; rfl]
                            exact hot_x_lm) hc
                          have ⟨_, _, hent_mark, _⟩ := hpref.2 (ot ^^^ 1#32).toNat
                            (by omega) hnz_o
                          rw [bv32_xor1_eq_litNeg] at hent_mark
                          exact hJpm (true, _, ()) mm
                            ⟨lm', hlml, fueMarkPrefix_mono (by omega) hpref,
                              fun _ => fue_resolve_unit hent_b hent_mark, hmm⟩
                        · exact hJm1c (false, ()) _ ⟨_, by rw [List.length_set, hlml],
                            fueMarkPrefix_set hpref him_lo (List.getElem?_eq_getElem hi_len)
                              (by assumption) hot_lt (by rw [hcvs]; exact hcv_le) trivial
                              hent_b 1#8, ‹_›⟩
                  · exact hJpm (false, _, ()) mm
                      ⟨lm', hlml, fueMarkPrefix_mono (by omega) hpref,
                        fun hf => Bool.noConfusion hf, hmm⟩
            · exact hJsbrk () ms ⟨ss, ⟨hss, hrss, hcvs, hfus⟩, hms⟩
            · exact hJsbrk () ms ⟨ss, ⟨hss, hrss, hcvs, hfus⟩, hms⟩
            · exact hJsbrk () ms ⟨ss, ⟨hss, hrss, hcvs, hfus⟩, hms⟩
  · exact hJp2 () mp1 ⟨sp1, hsp1, hmp1⟩
  · exact hJp2 () mp1 ⟨sp1, hsp1, hmp1⟩

/-- Canonical `Func.wp` proof for `full_cong_find_units_equivs`. -/
theorem full_cong_find_units_equivs_wp (Γ : Env)
    (hAddUnit : Γ.Has "full_add_unit" fullAddUnitSpec)
    (hEquiv : Γ.Has "full_cong_equiv_fold" Spec.fullCongEquivFoldSpec) :
    ∀ a m Q X, Spec.fullCongFindUnitsEquivsSpec a m Q X →
      Func.wp Γ full_cong_find_units_equivs_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hinv, hrepr, hm, hQ⟩
  have hmax32 : 2 * c.max_vars < 4294967296 := by
    have := c.hmaxv; unfold dimacsBound at this; omega
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hinv.1.core_ok.cur_vars_le
  have hcv64 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars :=
    bv64_ofNat_toNat_lt (by omega)
  have hnl64 : (BitVec.ofNat 64 s.core.cur_vars <<< 1#64).toNat = 2 * s.core.cur_vars := by
    rw [bv64_shl1_lt (by rw [hcv64]; omega), hcv64]
  have hwcap32 : c.wcap < 4294967296 := by
    have := c.hwcap; unfold dimacsBound at this; omega
  c0_hsteps_nogrp
  let I_p1 : Tup Val [i64] → Mem 64 → Prop := fun (v, ⟨⟩) mp1 =>
    ∃ sp1, FueStateInv c F0 F_cur s sp1 ∧ v.toNat ≤ sp1.core.cur_vars ∧ (FullMem c sp1 ⋆ R) mp1
  let P_st : Tup Val [] → Mem 64 → Prop := fun _ mst =>
    ∃ sst, FueStateInv c F0 F_cur s sst ∧ (FullMem c sst ⋆ R) mst
  refine wp_loop_inv I_p1 (fun (v, ⟨⟩) _ => s.core.cur_vars - v.toNat) ?_ ?_
  · intro Jp1 hJp1; c0_hsteps!
    exact hJp1 (0#64, ()) m ⟨s, ⟨hinv, hrepr, rfl, rfl⟩, Nat.zero_le _, hm⟩
  · rintro Jp1 ⟨v1, ⟨⟩⟩ mp1 ⟨sp1, hsp1, hv1_le, hmp1⟩ ihp1
    refine wp_join_group (ts := []) P_st ?_ ?_
    · rintro _ ⟨⟩ mp2_0 ⟨sp2_0, hsp2_0, hmp2_0⟩
      exact fue_pass2_wp Γ hEquiv hmax32 hcv_le hcv64 hnl64 hwcap32 hsp2_0 hmp2_0 hQ
    · intro Jp2 hJp2
      exact fue_pass1_body_wp Γ hAddUnit hmax32 hcv_le hcv64 hnl64 hwcap32 hsp1 hv1_le hmp1
        (fun ys m' hd hy => ihp1 ys m' hd hy) hJp2 hQ

end LeanQbe.T.Examples.Kissat.Proof.Congruence

end
