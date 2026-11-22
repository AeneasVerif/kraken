module

public import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof1a
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat M6 Congruence Closure & 2-Round Substitute Proofs — Part 1b

Proves parametric `(Γ : Env)` `Func.wp` contracts for the next 5 congruence extraction / binary /
equivalence functions (`FullM6CongSubst.lean` #11–#15):
1. `full_cong_count_bins` (`full_cong_count_bins_wp`, `m6CongCountBinsSpec`)
2. `full_cong_eb_match` (`full_cong_eb_match_wp`, `m6CongEbMatchSpec`)
3. `full_cong_extract_binaries` (`full_cong_extract_binaries_wp`, `m6CongExtractBinariesSpec`)
4. `full_cong_find_units_equivs` (`full_cong_find_units_equivs_wp`, `m6CongFindUnitsEquivsSpec`)
5. `full_cong_extract` (`full_cong_extract_wp`, `m6CongExtractSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6CongSubst

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open scoped LeanQbe.T.Examples.Kissat.FullM3CongBva.M3HeadTactics
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open scoped FullArenaTactics Full.FullCongTactics

/-! ## 1. Framing, Watch-Bound, Slice-Clearing & Pure Helpers (`Proof1b`) -/

section Helpers

private def FullWs1Rest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  (array (t := i32) c.pWsort s.scratch.wsort ⋆
   array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
   array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
   array (t := i32) c.pTarjanReach s.scratch.tarjan_reach) ⋆
  (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
   FullScrDynArrs c s.scratch ⋆ fullScrOuter c s)

private theorem focus_full_ws1 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆ (FullWs1Rest c s ⋆ R)) m := by
  rw [fullMem_eq_scrWks] at hm; unfold FullScrWksArrs at hm; unfold FullWs1Rest; ecancel

private theorem unfocus_full_ws1 {c : FullCfg} {s : FullState} {ws1' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pWorkStk1 ws1' ⋆ (FullWs1Rest c s ⋆ R)) m) :
    (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m := by
  rw [fullMem_eq_scrWks]; unfold FullScrWksArrs; unfold FullWs1Rest at hm
  change ((array (t := i32) c.pWsort s.scratch.wsort ⋆
    array (t := i32) c.pWorkStk1 ws1' ⋆
    array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
    array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
    array (t := i32) c.pTarjanReach s.scratch.tarjan_reach) ⋆
    (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
     FullScrDynArrs c s.scratch ⋆ fullScrOuter c s) ⋆ R) m
  ecancel

private def FullWs2Rest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  (array (t := i32) c.pWsort s.scratch.wsort ⋆
   array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
   array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
   array (t := i32) c.pTarjanReach s.scratch.tarjan_reach) ⋆
  (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
   FullScrDynArrs c s.scratch ⋆ fullScrOuter c s)

private theorem focus_full_ws2 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆ (FullWs2Rest c s ⋆ R)) m := by
  rw [fullMem_eq_scrWks] at hm; unfold FullScrWksArrs at hm; unfold FullWs2Rest; ecancel

private theorem unfocus_full_ws2 {c : FullCfg} {s : FullState} {ws2' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pWorkStk2 ws2' ⋆ (FullWs2Rest c s ⋆ R)) m) :
    (FullMem c { s with scratch := { s.scratch with work_stk2 := ws2' } } ⋆ R) m := by
  rw [fullMem_eq_scrWks]; unfold FullScrWksArrs; unfold FullWs2Rest at hm
  change ((array (t := i32) c.pWsort s.scratch.wsort ⋆
    array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
    array (t := i32) c.pWorkStk2 ws2' ⋆
    array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
    array (t := i32) c.pTarjanReach s.scratch.tarjan_reach) ⋆
    (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
     FullScrDynArrs c s.scratch ⋆ fullScrOuter c s) ⋆ R) m
  ecancel

private def FullLmRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  (array (t := i8) c.pVals s.core.vals ⋆ array (t := i8) c.pMark s.core.mrk) ⋆
  (FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆ fullCoreOuter c s)

private theorem focus_full_lm {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i8) c.pLitMark s.core.lit_mark ⋆ (FullLmRest c s ⋆ R)) m := by
  rw [fullMem_eq_coreByte] at hm; unfold FullCoreByteArrs at hm; unfold FullLmRest; ecancel

private theorem unfocus_full_lm {c : FullCfg} {s : FullState} {lm' : List (BitVec 8)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i8) c.pLitMark lm' ⋆ (FullLmRest c s ⋆ R)) m) :
    (FullMem c { s with core := { s.core with lit_mark := lm' } } ⋆ R) m := by
  rw [fullMem_eq_coreByte]; unfold FullCoreByteArrs; unfold FullLmRest at hm
  change ((array (t := i8) c.pVals s.core.vals ⋆ array (t := i8) c.pLitMark lm' ⋆
    array (t := i8) c.pMark s.core.mrk) ⋆
    (FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
     fullCoreOuter c s) ⋆ R) m
  ecancel

private theorem fullWatchBounds_of_dense {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s) :
    ∀ l < 2 * s.core.cur_vars,
      fullWatchOffCore s.core l + fullWatchSizeCore s.core l ≤ c.wcap := by
  intro l hl
  have hw_le := hd.1.core_ok.wlen_le
  have hwt := hd.2.1.watches
  unfold ModeWatchesInv at hwt
  split at hwt
  · exact Nat.le_trans (hwt.layout.bounds l hl) hw_le
  · exact Nat.le_trans (hwt.layout.bounds l hl) hw_le

private theorem fullDenseInvW_with_ws1 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {ws1' : List (BitVec 32)} (hl1 : ws1'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with work_stk1 := ws1' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with work_stk1_len := hl1 }⟩,
   hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem fullDenseInvW_with_oom_antsz {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    (oom' ant' : BitVec 64) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with oom := oom' }
        scratch := { s.scratch with ant_sz := ant' } } := by
  have hw' : FullWitnessInv c F0 F_cur { s.core with oom := oom' } :=
    { hd.2.1 with
      arena := { hd.2.1.arena with len_ok := hd.2.1.arena.len_ok }
      watches := hd.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
  exact ⟨⟨{ hd.1.core_ok with }, { hd.1.scratch_ok with }⟩, hw',
    fullLitMarksClear_of_eq hd.2.2.1 rfl rfl,
    fullArenaVarsNodup_of_eq hd.2.2.2.1 rfl rfl,
    fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl,
    hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem fullAddBin_fullDenseInvW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hd : FullDenseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hcl' : s'.core.cur_level = 0) (hdm' : s'.core.dense_mode = s.core.dense_mode)
    (hmrk' : s'.core.mrk = s.core.mrk) (hlm' : s'.core.lit_mark = s.core.lit_mark)
    (har' : s'.core.arena = s.core.arena) (hal' : s'.core.arena_len = s.core.arena_len)
    (hll' : s'.scratch.last_learned = s.scratch.last_learned)
    (hext' : s'.scratch.extend_len = s.scratch.extend_len) :
    FullDenseInvW c F0 F_cur s' :=
  ⟨hlen', hw', fullLitMarksClear_of_eq hd.2.2.1 hmrk' hlm',
   fullArenaVarsNodup_of_eq hd.2.2.2.1 har' hal',
   fullExtScratchOk_of_eq hd.2.2.2.2.1 har' hal' hll' hext',
   hcl', hdm' ▸ hd.2.2.2.2.2.2⟩

private theorem bv64_shl1_xor1_lt {l : BitVec 64} {n : Nat} (hl : l.toNat < 2 * n) :
    (l ^^^ 1#64).toNat < 2 * n := by
  have h : (l ^^^ 1#64).toNat = l.toNat ^^^ 1 := by simp [BitVec.toNat_xor]
  rw [h]; exact litNeg_lt_two_mul hl

private theorem bv64_mul2_lt {x : Nat} (hx : x < 2 ^ 63) :
    (BitVec.ofNat 64 x <<< (1 : Nat)).toNat = 2 * x := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm,
    Nat.mod_eq_of_lt (by omega : x < 2 ^ 64)]; omega

private theorem bv64_shl1_add1_lt {l : BitVec 64} (hl : 2 * l.toNat + 1 < 2 ^ 64) :
    (l <<< (1 : Nat)).toNat = 2 * l.toNat ∧
    (l <<< (1 : Nat) + 1#64).toNat = 2 * l.toNat + 1 := by
  have h1 : (l <<< (1 : Nat)).toNat = 2 * l.toNat := by
    rw [bv64_shl1_toNat]; exact Nat.mod_eq_of_lt (by omega)
  have h2 : (l <<< (1 : Nat) + 1#64).toNat = 2 * l.toNat + 1 := by
    rw [BitVec.toNat_add, h1, show (1#64 : BitVec 64).toNat = 1 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  exact ⟨h1, h2⟩

/-- Inductive membership of binary-watch literals in `wstk[p ..< endp)`. -/
private inductive InSliceBins (wstk : List (BitVec 32)) (endp nlits q : Nat) : Nat → Prop where
  | here {p w0} (hp : p < endp) (hw : wstk[p]? = some w0)
      (hb : (w0 &&& 0x80000000#32) ≠ 0#32) (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < nlits)
      (hq : q = (w0 &&& 0x7FFFFFFF#32).toNat) : InSliceBins wstk endp nlits q p
  | step_bin {p w0} (hp : p < endp) (hw : wstk[p]? = some w0)
      (hb : (w0 &&& 0x80000000#32) ≠ 0#32)
      (hnext : InSliceBins wstk endp nlits q (p + 1)) : InSliceBins wstk endp nlits q p
  | step_occ {p w0} (hp : p < endp) (hw : wstk[p]? = some w0)
      (hb : (w0 &&& 0x80000000#32) = 0#32)
      (hnext : InSliceBins wstk endp nlits q (p + 2)) : InSliceBins wstk endp nlits q p

private abbrev inSliceBins (wstk : List (BitVec 32)) (p endp nlits q : Nat) : Prop :=
  InSliceBins wstk endp nlits q p

private theorem inSliceBins_false_of_ge {wstk : List (BitVec 32)} {p endp nlits q : Nat}
    (hge : endp ≤ p) : inSliceBins wstk p endp nlits q ↔ False :=
  ⟨fun h => by cases h <;> omega, False.elim⟩

private inductive SliceChain (wstk : List (BitVec 32)) (off : Nat) : Nat → Prop where
  | here : SliceChain wstk off off
  | bin {p w0} : SliceChain wstk off p → wstk[p]? = some w0 →
      (w0 &&& 0x80000000#32) ≠ 0#32 → SliceChain wstk off (p + 1)
  | occ {p w0} : SliceChain wstk off p → wstk[p]? = some w0 →
      (w0 &&& 0x80000000#32) = 0#32 → SliceChain wstk off (p + 2)

private theorem inSliceBins_of_chain {wstk : List (BitVec 32)} {off endp nlits q : Nat}
    {p : Nat} (h : SliceChain wstk off p) :
    p < endp → inSliceBins wstk p endp nlits q → inSliceBins wstk off endp nlits q := by
  induction h with
  | here => exact fun _ hin => hin
  | @bin p w0 _ hp hne ih =>
    intro hp1 hin
    exact ih (by omega) (.step_bin (by omega) hp hne hin)
  | @occ p w0 _ hp heq ih =>
    intro hp2 hin
    exact ih (by omega) (.step_occ (by omega) hp heq hin)

private theorem inSliceBins_here {wstk : List (BitVec 32)} {off p endp nlits : Nat}
    {w0 : BitVec 32} (ch : SliceChain wstk off p) (hp_lt : p < endp)
    (hp : wstk[p]? = some w0) (hne : (w0 &&& 0x80000000#32) ≠ 0#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < nlits) :
    inSliceBins wstk off endp nlits (w0 &&& 0x7FFFFFFF#32).toNat :=
  inSliceBins_of_chain ch hp_lt (.here hp_lt hp hne hlt rfl)

private theorem inSliceBins_clear_bin {wstk : List (BitVec 32)} {p endp nlits q : Nat}
    {w0 : BitVec 32} (_hp_lt : p < endp) (hp : wstk[p]? = some w0)
    (hne : (w0 &&& 0x80000000#32) ≠ 0#32) (hq_ne : q ≠ (w0 &&& 0x7FFFFFFF#32).toNat)
    (hin : inSliceBins wstk p endp nlits q) :
    inSliceBins wstk (p + 1) endp nlits q := by
  cases hin with
  | here _ hw _ _ hq => rw [hp] at hw; cases hw; exact absurd hq hq_ne
  | step_bin _ _ _ hnext => exact hnext
  | step_occ _ hw hb _ => rw [hp] at hw; cases hw; exact absurd hb hne

private theorem inSliceBins_clear_occ {wstk : List (BitVec 32)} {p endp nlits q : Nat}
    {w0 : BitVec 32} (_hp_lt : p < endp) (hp : wstk[p]? = some w0)
    (heq : (w0 &&& 0x80000000#32) = 0#32) (hin : inSliceBins wstk p endp nlits q) :
    inSliceBins wstk (p + 2) endp nlits q := by
  cases hin with
  | here _ hw hb => rw [hp] at hw; cases hw; exact absurd heq hb
  | step_bin _ hw hb => rw [hp] at hw; cases hw; exact absurd heq hb
  | step_occ _ _ _ hnext => exact hnext

private theorem inSliceBins_clear_bin_of_ge {wstk : List (BitVec 32)} {p endp nlits q : Nat}
    {w0 : BitVec 32} (_hp_lt : p < endp) (hp : wstk[p]? = some w0)
    (hne : (w0 &&& 0x80000000#32) ≠ 0#32)
    (hge : nlits ≤ (w0 &&& 0x7FFFFFFF#32).toNat) (hin : inSliceBins wstk p endp nlits q) :
    inSliceBins wstk (p + 1) endp nlits q := by
  cases hin with
  | here _ hw _ hlt => rw [hp] at hw; cases hw; omega
  | step_bin _ _ _ hnext => exact hnext
  | step_occ _ hw hb _ => rw [hp] at hw; cases hw; exact absurd hb hne

private theorem dense_slice_pop_step {F_cur : List (List Nat)} {k : FullCoreState}
    {a p rem : Nat} (hslice : DenseWatchSliceOk F_cur k a p rem) (hpos : 0 < rem) :
    ∃ w0 : BitVec 32, k.wstk[p]? = some w0 ∧
      (((w0 &&& 0x80000000#32) ≠ 0#32 ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [a, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
        DenseWatchSliceOk F_cur k a (p + 1) (rem - 1)) ∨
       ((w0 &&& 0x80000000#32) = 0#32 ∧ 2 ≤ rem ∧
        DenseWatchSliceOk F_cur k a (p + 2) (rem - 2))) := by
  cases hslice with
  | empty => omega
  | bin hp hf _ _ hent hrest => exact ⟨_, hp, Or.inl ⟨hf, hent, hrest⟩⟩
  | occ hp _ hf _ _ _ hrest => exact ⟨_, hp, Or.inr ⟨hf, by omega, hrest⟩⟩

private theorem dense_slice_of_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hd : FullDenseInvW c F0 F_cur s) {l : Nat} (hl : l < 2 * s.core.cur_vars) :
    DenseWatchSliceOk F_cur s.core l (fullWatchOffCore s.core l) (fullWatchSizeCore s.core l) := by
  have hwt := hd.2.1.watches
  unfold ModeWatchesInv at hwt
  simp only [hd.2.2.2.2.2.2, ↓reduceIte] at hwt
  exact hwt.slices l hl

private theorem entails_unit_of_pair_dup {f : CNF Nat} {a : Nat}
    (h : f.EntailsClause (cnfClause [a, a])) : f.EntailsClause (cnfClause [a]) := by
  refine entails_of_eval_mem fun α hα => ?_
  have hs := (clauseEvalVal_iff α _).mpr ((CNF.entails_clause_def.mp h) α hα)
  rw [clauseEvalVal] at hs
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_self] at hs
  exact ⟨a, List.mem_singleton.mpr rfl, hs⟩

private theorem entails_unit_of_pair_and_neg {f : CNF Nat} {a q : Nat}
    (h1 : f.EntailsClause (cnfClause [a, q]))
    (h2 : f.EntailsClause (cnfClause [a, q ^^^ 1])) :
    f.EntailsClause (cnfClause [a]) := by
  refine entails_of_eval_mem fun α hα => ?_
  have hs1 := (clauseEvalVal_iff α _).mpr ((CNF.entails_clause_def.mp h1) α hα)
  have hs2 := (clauseEvalVal_iff α _).mpr ((CNF.entails_clause_def.mp h2) α hα)
  rw [clauseEvalVal] at hs1 hs2
  simp only [List.any_cons, List.any_nil, Bool.or_false,
    show q ^^^ 1 = litNeg q from rfl, evalLitVal_litNeg] at hs1 hs2
  cases ha : evalLitVal α a <;> cases hq : evalLitVal α q <;> simp_all

private theorem litEquiv_of_clauses {f : CNF Nat} {a b : Nat}
    (h1 : f.EntailsClause (cnfClause [a ^^^ 1, b]))
    (h2 : f.EntailsClause (cnfClause [a, b ^^^ 1])) : LitEquiv f a b := by
  refine litEquiv_of_eval_eq fun α hα => ?_
  have hs1 := (clauseEvalVal_iff α _).mpr ((CNF.entails_clause_def.mp h1) α hα)
  have hs2 := (clauseEvalVal_iff α _).mpr ((CNF.entails_clause_def.mp h2) α hα)
  rw [clauseEvalVal] at hs1 hs2
  simp only [List.any_cons, List.any_nil, Bool.or_false,
    show a ^^^ 1 = litNeg a from rfl, show b ^^^ 1 = litNeg b from rfl,
    evalLitVal_litNeg] at hs1 hs2
  cases ha : evalLitVal α a <;> cases hb : evalLitVal α b <;> simp_all

private theorem fullDenseInvW_with_cong_cnt {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    (cnt' : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with cong_cnt := cnt' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with }⟩, hd.2.1, hd.2.2.1, hd.2.2.2.1,
   fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl,
   hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem fullDenseInvW_with_lm_clear {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {lm' : List (BitVec 8)} (hll : lm'.length = 2 * c.max_vars)
    (hclr : ∀ q < 2 * c.max_vars, lm'[q]?.getD 0#8 = 0#8) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with lit_mark := lm' } } := by
  have hw' : FullWitnessInv c F0 F_cur { s.core with lit_mark := lm' } :=
    { hd.2.1 with
      arena := { hd.2.1.arena with len_ok := hd.2.1.arena.len_ok }
      watches := hd.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
  exact ⟨⟨{ hd.1.core_ok with lit_mark_len := hll }, hd.1.scratch_ok⟩, hw',
    ⟨hd.2.2.1.1, hclr⟩, fullArenaVarsNodup_of_eq hd.2.2.2.1 rfl rfl,
    fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl,
    hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem core_fields_of_tmp_lm {a b : FullCoreState}
    (h : { a with tmp := b.tmp, lit_mark := b.lit_mark } = b) :
    a.inconsistent = b.inconsistent ∧ a.arena = b.arena ∧ a.arena_len = b.arena_len ∧
    a.cur_vars = b.cur_vars ∧ a.cur_level = b.cur_level ∧ a.dense_mode = b.dense_mode ∧
    a.fuel = b.fuel ∧ a.repr = b.repr ∧
    ({ b with tmp := a.tmp, lit_mark := a.lit_mark } : FullCoreState) = a := by
  cases a; cases b; cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem scr_fields_of_buf {a b : FullScratch}
    (h : { a with scratch_buf := b.scratch_buf } = b) :
    a.last_learned = b.last_learned ∧ a.extend_len = b.extend_len := by
  cases a; cases b; cases h; exact ⟨rfl, rfl⟩

private theorem fullDenseInvW_of_xorK {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hd : FullDenseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c)
    (hce : { s'.core with tmp := s.core.tmp, lit_mark := s.core.lit_mark } = s.core)
    (hse : { s'.scratch with scratch_buf := s.scratch.scratch_buf } = s.scratch)
    (hmk' : FullLitMarksClear c s') :
    FullDenseInvW c F0 F_cur s' := by
  obtain ⟨_, har, hal, _, hcl, hdm, _, _, hkeq⟩ := core_fields_of_tmp_lm hce
  obtain ⟨hll, hext⟩ := scr_fields_of_buf hse
  have hnd' := fullArenaVarsNodup_of_eq hd.2.2.2.1 har hal
  have hext' := fullExtScratchOk_of_eq hd.2.2.2.2.1 har hal hll hext
  have hw_tm : FullWitnessInv c F0 F_cur
      { s.core with tmp := s'.core.tmp, lit_mark := s'.core.lit_mark } :=
    { hd.2.1 with
      arena := { hd.2.1.arena with len_ok := hd.2.1.arena.len_ok }
      watches := hd.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
  have hw' : FullWitnessInv c F0 F_cur s'.core := hkeq ▸ hw_tm
  exact ⟨hlen', hw', hmk', hnd', hext', hcl.trans hd.2.2.2.2.2.1, hdm ▸ hd.2.2.2.2.2.2⟩

private theorem fullDenseInvW_with_scr {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {scr' : List (BitVec 32)} (hl : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with scratch_buf := scr' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with scratch_buf_len := hl }⟩,
   hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem fullDenseInvW_with_ws2 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {ws2' : List (BitVec 32)} (hl : ws2'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with work_stk2 := ws2' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with work_stk2_len := hl }⟩,
   hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem bv64_shl1_or01_toNat {v sign : BitVec 64} (hv : v.toNat < 2 ^ 30)
    (hs : sign.toNat < 2) :
    (((v <<< (1 : Nat)) ||| sign).setWidth 32).toNat = 2 * v.toNat + sign.toNat := by
  have hshl : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
    rw [bv64_shl1_toNat]; exact Nat.mod_eq_of_lt (by omega)
  have hor : ((v <<< (1 : Nat)) ||| sign).toNat = 2 * v.toNat + sign.toNat := by
    rw [BitVec.toNat_or, hshl]
    rcases (by omega : sign.toNat = 0 ∨ sign.toNat = 1) with hs0 | hs1
    · rw [hs0, Nat.or_zero, Nat.add_zero]
    · rw [hs1]
      apply Nat.eq_of_testBit_eq
      intro k; cases k with
      | zero => simp
      | succ k =>
        rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
        simp [show (1 : Nat) / 2 = 0 from rfl,
          show (2 * v.toNat + 1) / 2 = v.toNat from by omega,
          show (2 * v.toNat) / 2 = v.toNat from by omega]
  rw [BitVec.toNat_setWidth, hor, Nat.mod_eq_of_lt (by omega)]

private theorem bv32_xor1_shr1 {ot : BitVec 32} :
    ((ot ^^^ 1#32) >>> (1 : Nat)).toNat = ot.toNat / 2 := by
  have h1 : ((ot ^^^ 1#32) >>> (1 : Nat)).toNat = (ot.toNat ^^^ 1) / 2 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_xor, show (1#32 : BitVec 32).toNat = 1 from rfl,
      Nat.shiftRight_eq_div_pow, Nat.pow_one]
  rw [h1]; exact litVar_litNeg ot.toNat

private theorem nodup_getElem_inj {α : Type _} :
    ∀ {l : List α}, l.Nodup → ∀ i j : Nat, (hi : i < l.length) → (hj : j < l.length) →
      l[i]'hi = l[j]'hj → i = j
  | [], _, i, _, hi, _, _ => absurd hi (Nat.not_lt_zero i)
  | _ :: _, _, 0, 0, _, _, _ => rfl
  | x :: xs, hnd, 0, j + 1, _, hj, heq => by
    have hcons := List.nodup_cons.mp hnd
    have hmem : xs[j]'(by simp at hj; omega) ∈ xs := List.getElem_mem _
    have hx : x = xs[j]'(by simp at hj; omega) := by simpa using heq
    exact absurd (hx ▸ hmem) hcons.1
  | x :: xs, hnd, i + 1, 0, hi, _, heq => by
    have hcons := List.nodup_cons.mp hnd
    have hmem : xs[i]'(by simp at hi; omega) ∈ xs := List.getElem_mem _
    have hx : x = xs[i]'(by simp at hi; omega) := by simpa using heq.symm
    exact absurd (hx ▸ hmem) hcons.1
  | _ :: xs, hnd, i + 1, j + 1, hi, hj, heq => by
    have hcons := List.nodup_cons.mp hnd
    exact congrArg Nat.succ (nodup_getElem_inj hcons.2 i j (by simp at hi; omega)
      (by simp at hj; omega) heq)

private theorem nodup_map_on {α β : Type _} {f : α → β} :
    ∀ {l : List α}, l.Nodup → (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → (l.map f).Nodup
  | [], _, _ => .nil
  | a :: xs, hnd, hinj => by
    have hcons := List.nodup_cons.mp hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, nodup_map_on hcons.2 fun x hx y hy hxy =>
      hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy⟩
    rw [List.mem_map] at hmem; obtain ⟨b, hb, hfb⟩ := hmem
    have hba := hinj b (List.mem_cons_of_mem _ hb) a List.mem_cons_self hfb
    exact hcons.1 (hba ▸ hb)

private theorem list_nodup_filter_map (f : Nat → Nat) {idxs : List Nat}
    {ar : List (BitVec 32)} {sz p : Nat}
    (hnd : ((List.range sz).map fun q => (ar[p + 3 + q]?.getD 0#32).toNat / 2).Nodup)
    (hid_nd : idxs.Nodup) (hid_lt : ∀ q ∈ idxs, q < sz)
    (hf : ∀ q, f q = (ar[p + 3 + q]?.getD 0#32).toNat / 2) :
    (idxs.map f).Nodup := by
  refine nodup_map_on hid_nd fun a ha b hb hab => ?_
  rw [hf a, hf b] at hab
  have ha_s := hid_lt a ha; have hb_s := hid_lt b hb
  exact nodup_getElem_inj hnd a b (by simp; omega) (by simp; omega)
    (by simpa [List.getElem_map] using hab)

end Helpers

/-! ## 2. `full_cong_count_bins_wp` (`m6CongCountBinsSpec`) -/

theorem full_cong_count_bins_wp (Γ : Env) :
    ∀ args m Q X, m6CongCountBinsSpec args m Q X →
      Func.wp Γ full_cong_count_bins_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hlen, hws_bd, hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; unfold dimacsBound at hmx hwc
  have hcl := hlen.core_ok; have hsl := hlen.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hwvl := hcl.wvec_len; have hwsl := hcl.wstk_len_arr
  have hws1l := hsl.work_stk1_len
  have hnl_bd : 2 * s.core.cur_vars < 2 ^ 64 := by omega
  have hfs := focus_full_ws1 hm0
  generalize hR_ws1 : FullWs1Rest c s ⋆ R = R_ws1 at hfs
  fc_steps
  have hnl_eq : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat = 2 * s.core.cur_vars :=
    bv64_mul2_lt (by omega)
  refine wp_loop_inv (ts := [i64])
    (fun (l, ()) ml => ∃ ws1 : List (BitVec 32),
      l.toNat ≤ 2 * s.core.cur_vars ∧ ws1.length = 2 * c.max_vars ∧
      (array (t := i32) c.pWorkStk1 ws1 ⋆ R_ws1) ml)
    (fun (l, ()) _ => 2 * s.core.cur_vars - l.toNat)
    (fun J1 hJ1 => by
      fc_let; exact hJ1 (0#64, ()) m0 ⟨s.scratch.work_stk1, Nat.zero_le _, hws1l, hfs⟩)
    (fun J1 (l, ()) ml ⟨ws1, hl_le, hwl1, hml⟩ ih1 => ?_)
  fc_split_fast
  · have hl_lt : l.toNat < 2 * s.core.cur_vars := by
      simp only [BitVec.ult, decide_eq_true_eq] at hc; rwa [hnl_eq] at hc
    have hl1_n : (l + 1#64).toNat = l.toNat + 1 := by bv_omega
    have hl_lt1 : l.toNat < ws1.length := by omega
    fc_steps
    refine ih1 (l + 1#64, ()) m (by dsimp only; omega)
      ⟨ws1.set l.toNat 0#32, by omega, by simp [hwl1], hm⟩
  · clear hc; subst hR_ws1
    have hm_ws1 := unfocus_full_ws1 hml
    refine wp_loop_inv (ts := [i64])
      (fun (l, ()) ml2 => ∃ ws1 : List (BitVec 32),
        l.toNat ≤ 2 * s.core.cur_vars ∧ ws1.length = 2 * c.max_vars ∧
        (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1 } } ⋆ R) ml2)
      (fun (l, ()) _ => 2 * s.core.cur_vars - l.toNat)
      (fun J2 hJ2 => by fc_let; exact hJ2 (0#64, ()) ml ⟨ws1, Nat.zero_le _, hwl1, hm_ws1⟩)
      (fun J2 (l, ()) ml2 ⟨ws1_2, hl_le2, hwl2, hml2⟩ ih2 => ?_)
    fc_split_fast
    · have hl_lt : l.toNat < 2 * s.core.cur_vars := by
        simp only [BitVec.ult, decide_eq_true_eq] at hc; rwa [hnl_eq] at hc
      have hl1_n : (l + 1#64).toNat = l.toNat + 1 := by bv_omega
      obtain ⟨hshl, hshl1⟩ := bv64_shl1_add1_lt (l := l) (by omega)
      have hbd_l := hws_bd l.toNat hl_lt
      unfold fullWatchOffCore fullWatchSizeCore at hbd_l
      have hw0_lt : (l <<< (1 : Nat)).toNat < s.core.wvec.length := by omega
      have hw1_lt : (l <<< (1 : Nat) + 1#64).toNat < s.core.wvec.length := by omega
      have hshl_wv : s.core.wvec[(l <<< (1 : Nat)).toNat]'hw0_lt =
          s.core.wvec[2 * l.toNat]'(by omega) :=
        list_getElem_congr hshl hw0_lt (by omega)
      have hshl1_wv : s.core.wvec[(l <<< (1 : Nat) + 1#64).toNat]'hw1_lt =
          s.core.wvec[2 * l.toNat + 1]'(by omega) :=
        list_getElem_congr hshl1 hw1_lt (by omega)
      have hoff_eq :
          (s.core.wvec[(l <<< (1 : Nat)).toNat]'hw0_lt).setWidth 64 =
            BitVec.ofNat 64 (s.core.wvec[2 * l.toNat]?.getD 0#32).toNat := by
        rw [hshl_wv, List.getElem?_eq_getElem (by omega), Option.getD_some]
        apply BitVec.eq_of_toNat_eq; simp
      have hwsz_eq :
          (s.core.wvec[(l <<< (1 : Nat) + 1#64).toNat]'hw1_lt).setWidth 64 =
            BitVec.ofNat 64 (s.core.wvec[2 * l.toNat + 1]?.getD 0#32).toNat := by
        rw [hshl1_wv, List.getElem?_eq_getElem (by omega), Option.getD_some]
        apply BitVec.eq_of_toNat_eq; simp
      let off := (s.core.wvec[(l <<< (1 : Nat)).toNat]'hw0_lt).setWidth 64
      let wsz := (s.core.wvec[(l <<< (1 : Nat) + 1#64).toNat]'hw1_lt).setWidth 64
      have hoff_n : off.toNat = (s.core.wvec[2 * l.toNat]?.getD 0#32).toNat := by
        dsimp only [off]; rw [hoff_eq, BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))
      have hwsz_n : wsz.toNat = (s.core.wvec[2 * l.toNat + 1]?.getD 0#32).toNat := by
        dsimp only [wsz]; rw [hwsz_eq, BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))
      have hend_n : (off + wsz).toNat = off.toNat + wsz.toNat := by
        rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
      have hend_bd : (off + wsz).toNat ≤ c.wcap := by omega
      fc_steps
      refine wp_loop_inv (ts := [i64, i32])
        (fun (p, bc, ()) mp => mp = ml2 ∧ off.toNat ≤ p.toNat ∧
          p.toNat ≤ (off + wsz).toNat + 1)
        (fun (p, _, ()) _ => (off + wsz).toNat + 1 - p.toNat)
        (fun Jp hJp => by
          fc_steps; exact hJp (off, 0#32, ()) ml2 ⟨rfl, Nat.le_refl _, by omega⟩)
        (fun Jp (p, bc, ()) mp ⟨hmp, hp_lo, hp_hi⟩ ihp => ?_)
      subst mp; fc_split_fast
      · have hp_lt : p.toNat < (off + wsz).toNat := by
          simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
        have hp_w : p.toNat < s.core.wstk.length := by omega
        have hp1_n : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
        have hp2_n : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
        fc_split_fast
        · fc_steps
          exact ihp (p + 1#64, bc + 1#32, ()) ml2 (by dsimp only; omega)
            ⟨rfl, by omega, by omega⟩
        · fc_steps
          exact ihp (p + 2#64, bc, ()) ml2 (by dsimp only; omega)
            ⟨rfl, by omega, by omega⟩
      · have hlx_lt : (l ^^^ 1#64).toNat < ws1_2.length := by
          rw [hwl2]; exact Nat.lt_of_lt_of_le (bv64_shl1_xor1_lt hl_lt) (by omega)
        clear hc; fc_steps
        exact ih2 (l + 1#64, ()) m (by dsimp only; omega)
          ⟨ws1_2.set (l ^^^ 1#64).toNat bc, by omega, by simp [hwl2], hm⟩
    · fc_steps; exact hQ ws1_2 ml2 hwl2 hml2

/-! ## 3. `full_cong_eb_match_wp` (`m6CongEbMatchSpec`) -/

theorem full_cong_eb_match_wp (Γ : Env)
    (hHasBin : ∀ args m Q X, FullCongSpecs.fullHasBinSpec args m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, m6CongEbMatchSpec args m Q X →
      Func.wp Γ full_cong_eb_match_body args m Q X := by
  rintro ⟨h, x, l, k, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hx_lt, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hlen.core_ok.cur_vars_le; have hws1l := hlen.scratch_ok.work_stk1_len
  have hx_ws1 : (x.setWidth 64).toNat < s.scratch.work_stk1.length := by
    rw [hws1l, bv_zext32_toNat]; omega
  fc_split_fast
  · fc_steps; exact hQ false fun hf => by cases hf
  · clear hc; fc_steps; c0_call hHasBin
    refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm0, fun ok1 hok1 => ?_⟩
    fc_split_fast
    · fc_steps; exact hQ true fun _ => Or.inl (by
        have h1 := (hok1 hc).2.2.2.2; rw [BitVec.toNat_xor] at h1; exact h1)
    · fc_steps; c0_call hHasBin
      refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm0, fun ok2 hok2 => ?_⟩
      fc_split_fast
      · fc_steps; exact hQ true fun _ => Or.inr (by
          have h1 := (hok2 hc).2.2.2.2; rw [BitVec.toNat_xor] at h1; exact h1)
      · fc_steps; exact hQ false fun hf => by cases hf

/-! ## 4. `full_cong_extract_binaries_wp` (`m6CongExtractBinariesSpec`) -/

theorem full_cong_extract_binaries_wp (Γ : Env)
    (hNext : ∀ args m Q X, FullCongSpecs.fullArenaNextSpec args m Q X →
      Γ "full_arena_next" [i64, i32] [i32] args m Q X)
    (hHasBin : ∀ args m Q X, FullCongSpecs.fullHasBinSpec args m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] args m Q X)
    (hAddBin : ∀ args m Q X, FullCongSpecs.fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X)
    (hCountBins : ∀ args m Q X, m6CongCountBinsSpec args m Q X →
      Γ "full_cong_count_bins" [i64] [] args m Q X)
    (hEbMatch : ∀ args m Q X, m6CongEbMatchSpec args m Q X →
      Γ "full_cong_eb_match" [i64, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, m6CongExtractBinariesSpec args m Q X →
      Func.wp Γ full_cong_extract_binaries_body args m Q X := by
  rintro ⟨h, tick_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hd, hm0, hQ⟩
  have hmx := c.hmaxv; have hac := c.harena; unfold dimacsBound at hmx hac
  have hale0 := hd.1.core_ok.arena_len_le
  fc_split_fast
  · have huns := FullM3CongBva.unsat_of_inconsistent_w hd.2.1 (bne_iff_ne.mp hc)
    fc_steps; exact hQ 20#64 s m0 hd rfl rfl (Or.inr rfl) (fun _ => huns) hm0
  · clear hc; fc_steps; c0_call hCountBins
    refine ⟨c, s, R, rfl, hd.1, fullWatchBounds_of_dense hd, hm0, fun ws1' m1 hws1_l hm1 => ?_⟩
    let s1 : FullState := { s with scratch := { s.scratch with work_stk1 := ws1' } }
    have hd1 : FullDenseInvW c F0 F_cur s1 := fullDenseInvW_with_ws1 hd hws1_l
    fc_to_group
    refine wp_loop_break_group (brkTs := [i64, i64]) (lpTs := [i64, i64])
      (fun (_, _, ()) mb => ∃ sb : FullState,
        FullDenseInvW c F0 F_cur sb ∧ sb.core.cur_vars = s.core.cur_vars ∧
        sb.core.fuel = s.core.fuel ∧ (FullMem c sb ⋆ R) mb)
      (fun rem (p, ticks, ()) ml => ∃ sl : FullState,
        FullDenseInvW c F0 F_cur sl ∧ sl.core.cur_vars = s.core.cur_vars ∧
        sl.core.fuel = s.core.fuel ∧ sl.core.arena = s1.core.arena ∧
        sl.core.arena_len = s1.core.arena_len ∧ p.toNat ≤ s1.core.arena_len ∧
        (p.toNat = s1.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefsCore s1.core) ∧
        rem = s1.core.arena_len - p.toNat ∧ (FullMem c sl ⋆ R) ml)
      ?_ ?_ ?_
    · rintro _ ⟨_, _, ⟨⟩⟩ mb ⟨sb, hdb, hcv_b, hfl_b, hmb⟩
      fc_split_fast
      · have huns := FullM3CongBva.unsat_of_inconsistent_w hdb.2.1 (bne_iff_ne.mp hc)
        fc_steps; exact hQ 20#64 sb mb hdb hcv_b hfl_b (Or.inr rfl) (fun _ => huns) hmb
      · fc_steps; exact hQ 1#64 sb mb hdb hcv_b hfl_b (Or.inl rfl) (fun h => by cases h) hmb
    · rintro B L rem ⟨p, ticks, ⟨⟩⟩ ml hB hL
        ⟨sl, hdl, hcv_l, hfl_l, har_l, hal_l, hp_le, hp_mem, rfl, hml⟩
      fc_split_fast
      · have hp_lt : p.toNat < sl.core.arena_len := by
          simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64)] at hc
          rw [hal_l]; exact hc
        clear hc; fc_split_fast
        · have hp_ref : p.toNat ∈ fullArenaClauseRefsCore sl.core := by
            have hmem := hp_mem.resolve_left (by omega)
            unfold fullArenaClauseRefsCore; rw [har_l, hal_l]; exact hmem
          have hp_wf := hdl.2.1.arena.refs_wf p.toNat hp_ref
          have hlen_l := hdl.1; have harl_l := hlen_l.core_ok.arena_len_arr
          have hale_l := hlen_l.core_ok.arena_len_le
          have hp_arr : p.toNat < sl.core.arena.length := by omega
          have hp2_n : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
          have hp2_arr : (p + 2#64).toNat < sl.core.arena.length := by omega
          fc_steps; c0_call hNext
          refine ⟨c, sl, R, rfl, hlen_l, hml, ?_⟩
          have hp_tr : (p.setWidth 32).toNat = p.toNat := by
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
          have hnp_bd := fullArenaNextOff_bounds (ar := sl.core.arena) (alen := sl.core.arena_len)
            (cref := p.toNat) hp_wf.1
          let np_bv := (BitVec.ofNat 32 (fullArenaNextOff sl.core.arena sl.core.arena_len
            (p.setWidth 32).toNat)).setWidth 64
          have hnp_n : np_bv.toNat = fullArenaNextOff sl.core.arena sl.core.arena_len p.toNat := by
            dsimp only [np_bv]; rw [hp_tr, bv_zext32_toNat, bv32_ofNat_toNat (by omega)]
          have hnp_mem : np_bv.toNat = s1.core.arena_len ∨
              np_bv.toNat ∈ fullArenaClauseRefsCore s1.core := by
            rw [hnp_n]
            rw [show fullArenaNextOff sl.core.arena sl.core.arena_len p.toNat =
              fullArenaNextOff s1.core.arena s1.core.arena_len p.toNat by rw [har_l, hal_l]]
            exact fullArenaClauseRefs_next_or_end hd1.2.1 (hp_mem.resolve_left (by omega))
          have hnp_gt : p.toNat < np_bv.toNat := by
            rw [hnp_n]; have := hp_wf.2.1; have := hp_wf.2.2.1; omega
          fc_to_group; refine wp_join_group (ts := [i64])
            (fun (t', ()) mj => ∃ sj : FullState,
              FullDenseInvW c F0 F_cur sj ∧ sj.core.cur_vars = s.core.cur_vars ∧
              sj.core.fuel = s.core.fuel ∧ sj.core.arena = s1.core.arena ∧
              sj.core.arena_len = s1.core.arena_len ∧ (FullMem c sj ⋆ R) mj)
            (fun _ ⟨t', ⟨⟩⟩ mj ⟨sj, hdj, hcv_j, hfl_j, har_j, hal_j, hmj⟩ => by
              fc_let
              refine hL (s1.core.arena_len - np_bv.toNat) (np_bv, t', ()) mj
                (by omega) ⟨sj, hdj, hcv_j, hfl_j, har_j, hal_j, by omega, hnp_mem, rfl, hmj⟩)
            ?_
          intro Jnext hJnext
          have hjnext_same : Jnext (ticks + 1#64, ()) ml :=
            hJnext (ticks + 1#64, ()) ml ⟨sl, hdl, hcv_l, hfl_l, har_l, hal_l, hml⟩
          fc_split_fast
          · have hng_red := beq_iff_eq.mp hc; clear hc; fc_split_fast
            · have hsz3_bv := beq_iff_eq.mp hc; clear hc
              have hsz_p2 : sl.core.arena[(p + 2#64).toNat]'hp2_arr =
                  sl.core.arena[p.toNat + 2]'(by omega) :=
                list_getElem_congr hp2_n hp2_arr (by omega)
              have hsz3_n : fullArenaClauseSizeCore sl.core p.toNat = 3 := by
                unfold fullArenaClauseSizeCore
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← hsz_p2]
                exact congrArg BitVec.toNat hsz3_bv
              have hng : fullArenaClauseGarb sl p.toNat = false := by
                unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                rw [List.getElem?_eq_getElem hp_arr, Option.getD_some]
                exact garb_false_of_and_480000 hng_red
              have hp3_n : (p + 3#64).toNat = p.toNat + 3 := by bv_omega
              have hp4_n : (p + 4#64).toNat = p.toNat + 4 := by bv_omega
              have hp5_n : (p + 5#64).toNat = p.toNat + 5 := by bv_omega
              have hbd6 : p.toNat + 6 ≤ sl.core.arena.length := by omega
              have hlits3 := arena_clause3_lits (k := sl.core) (cr := p.toNat) hsz3_n (by omega)
              have hcl3 := hdl.2.1.arena.entails p.toNat hp_ref hng
              have hlt3 := hdl.2.1.arena.lits_lt p.toNat hp_ref hng
              rw [hlits3] at hcl3 hlt3
              have hp3_arr : (p + 3#64).toNat < sl.core.arena.length := by omega
              have hp4_arr : (p + 4#64).toNat < sl.core.arena.length := by omega
              have hp5_arr : (p + 5#64).toNat < sl.core.arena.length := by omega
              have ha_eq : sl.core.arena[(p + 3#64).toNat]'hp3_arr =
                  sl.core.arena[p.toNat + 3]'(by omega) :=
                list_getElem_congr hp3_n hp3_arr (by omega)
              have hb_eq : sl.core.arena[(p + 4#64).toNat]'hp4_arr =
                  sl.core.arena[p.toNat + 4]'(by omega) :=
                list_getElem_congr hp4_n hp4_arr (by omega)
              have hc_eq : sl.core.arena[(p + 5#64).toNat]'hp5_arr =
                  sl.core.arena[p.toNat + 5]'(by omega) :=
                list_getElem_congr hp5_n hp5_arr (by omega)
              let la := sl.core.arena[(p + 3#64).toNat]'hp3_arr
              let lb := sl.core.arena[(p + 4#64).toNat]'hp4_arr
              let lc := sl.core.arena[(p + 5#64).toNat]'hp5_arr
              have hla_lt : la.toNat < 2 * sl.core.cur_vars := by
                dsimp only [la]; rw [ha_eq]; exact hlt3 _ (by simp)
              have hlb_lt : lb.toNat < 2 * sl.core.cur_vars := by
                dsimp only [lb]; rw [hb_eq]; exact hlt3 _ (by simp)
              have hlc_lt : lc.toNat < 2 * sl.core.cur_vars := by
                dsimp only [lc]; rw [hc_eq]; exact hlt3 _ (by simp)
              have hcl_abc : (cnfOfClauses F_cur).EntailsClause
                  (cnfClause [la.toNat, lb.toNat, lc.toNat]) := by
                dsimp only [la, lb, lc]; rw [ha_eq, hb_eq, hc_eq]; exact hcl3
              have hcv_le_l := hlen_l.core_ok.cur_vars_le
              have hvals_l := hlen_l.core_ok.vals_len
              have hla_v : (la.setWidth 64).toNat < sl.core.vals.length := by
                rw [bv_zext32_toNat]; omega
              have hlb_v : (lb.setWidth 64).toNat < sl.core.vals.length := by
                rw [bv_zext32_toNat]; omega
              have hlc_v : (lc.setWidth 64).toNat < sl.core.vals.length := by
                rw [bv_zext32_toNat]; omega
              fc_to_group; refine wp_join_group (ts := [i64])
                (fun (t', ()) mj => ∃ sj : FullState,
                  FullDenseInvW c F0 F_cur sj ∧ sj.core.cur_vars = s.core.cur_vars ∧
                  sj.core.fuel = s.core.fuel ∧ sj.core.arena = s1.core.arena ∧
                  sj.core.arena_len = s1.core.arena_len ∧ (FullMem c sj ⋆ R) mj)
                (fun _ ⟨t', ⟨⟩⟩ mj hj => by fc_let; exact hJnext (t', ()) mj hj)
                ?_
              intro Jm hJm
              have hjm_same : Jm (ticks + 1#64, ()) ml :=
                hJm (ticks + 1#64, ()) ml ⟨sl, hdl, hcv_l, hfl_l, har_l, hal_l, hml⟩
              fc_split_fast
              · fc_split_fast
                · fc_split_fast
                  · clear hc; fc_to_group
                    refine wp_join_group (ts := [i32, i32, .bool])
                      (fun (rl, rk, rfound, ()) mf => mf = ml ∧
                        (rfound = true → rl.toNat < 2 * sl.core.cur_vars ∧
                          rk.toNat < 2 * sl.core.cur_vars ∧
                          (cnfOfClauses F_cur).EntailsClause (cnfClause [rl.toNat, rk.toNat])))
                      ?_ ?_
                    · rintro _ ⟨rl, rk, rfound, ⟨⟩⟩ mf ⟨hmf, hok⟩
                      subst mf; fc_split_fast
                      · have hrl_lt := (hok hc).1; have hrk_lt := (hok hc).2.1
                        have hent_rk := (hok hc).2.2
                        clear hc hok; fc_steps; c0_call hHasBin
                        refine ⟨c, F0, F_cur, sl, R, rfl, hlen_l, hdl.2.1, hml, fun hb1 _ => ?_⟩
                        fc_split_fast
                        · fc_steps; exact hjm_same
                        · fc_steps; c0_call hAddBin
                          refine ⟨c, F0, F_cur, sl, R, rfl, hlen_l, hdl.2.1, hdl.2.2.2.2.2.1,
                            hrl_lt, hrk_lt, hent_rk, hml, fun st2 s2 m2 hlen2 hw2 hcl2 hdm2
                              hcv2 hfl2 hmrk2 hlm2 har2 hal2 _ _ _ hll2 hext2 hinc2 hm2 => ?_⟩
                          have hd2 := fullAddBin_fullDenseInvW hdl hlen2 hw2 hcl2 hdm2 hmrk2 hlm2
                            har2 hal2 hll2 hext2
                          have hcv2s : s2.core.cur_vars = s.core.cur_vars := hcv2.trans hcv_l
                          have hfl2s : s2.core.fuel = s.core.fuel := hfl2.trans hfl_l
                          fc_split_fast
                          · have huns2 :=
                              FullM3CongBva.unsat_of_inconsistent_w hw2 (hinc2 (beq_iff_eq.mp hc))
                            fc_steps
                            exact hQ 20#64 s2 m2 hd2 hcv2s hfl2s (Or.inr rfl) (fun _ => huns2) hm2
                          · clear hc; fc_split_fast
                            · fc_steps
                              let s2b : FullState :=
                                { s2 with
                                  core := { s2.core with oom := 0#64 }
                                  scratch := { s2.scratch with ant_sz := 1#64 } }
                              have hd2b := fullDenseInvW_with_oom_antsz hd2 0#64 1#64
                              exact hB (p, ticks + 1#64 + 2#64, ()) m ⟨s2b, hd2b, hcv2s, hfl2s, hm⟩
                            · clear hc; fc_steps
                              exact hJm (ticks + 1#64 + 2#64, ()) m2
                                ⟨s2, hd2, hcv2s, hfl2s, har2.trans har_l, hal2.trans hal_l, hm2⟩
                      · fc_steps; exact hjm_same
                    · intro Jf hJf; fc_steps; c0_call hEbMatch
                      refine ⟨c, F0, F_cur, sl, R, rfl, hlen_l, hdl.2.1, hla_lt, hml,
                        fun ok1 hok1 => ?_⟩
                      fc_split_fast
                      · fc_steps; refine hJf (lb, lc, true, ()) ml ⟨rfl, fun _ =>
                          ⟨hlb_lt, hlc_lt, resolve_ternary_with_either_bin hcl_abc (hok1 hc)⟩⟩
                      · clear hc; fc_steps; c0_call hEbMatch
                        refine ⟨c, F0, F_cur, sl, R, rfl, hlen_l, hdl.2.1, hlb_lt, hml,
                          fun ok2 hok2 => ?_⟩
                        fc_split_fast
                        · have hcl_bac : (cnfOfClauses F_cur).EntailsClause
                              (cnfClause [lb.toNat, la.toNat, lc.toNat]) :=
                            entails_perm_clause (fun x hx => by
                              simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
                              rcases hx with rfl | rfl | rfl <;> simp) hcl_abc
                          fc_steps; refine hJf (la, lc, true, ()) ml ⟨rfl, fun _ =>
                            ⟨hla_lt, hlc_lt,
                             resolve_ternary_with_either_bin hcl_bac (hok2 hc)⟩⟩
                        · clear hc; fc_steps; c0_call hEbMatch
                          refine ⟨c, F0, F_cur, sl, R, rfl, hlen_l, hdl.2.1, hlc_lt, hml,
                            fun ok3 hok3 => ?_⟩
                          fc_split_fast
                          · have hcl_cab : (cnfOfClauses F_cur).EntailsClause
                                (cnfClause [lc.toNat, la.toNat, lb.toNat]) :=
                              entails_perm_clause (fun x hx => by
                                simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
                                rcases hx with rfl | rfl | rfl <;> simp) hcl_abc
                            fc_steps; refine hJf (la, lb, true, ()) ml ⟨rfl, fun _ =>
                              ⟨hla_lt, hlb_lt,
                               resolve_ternary_with_either_bin hcl_cab (hok3 hc)⟩⟩
                          · fc_steps
                            exact hJf (0#32, 0#32, false, ()) ml ⟨rfl, fun h => by cases h⟩
                  · fc_steps; exact hjm_same
                · fc_steps; exact hjm_same
              · fc_steps; exact hjm_same
            · fc_steps; exact hjnext_same
          · fc_steps; exact hjnext_same
        · clear hc; fc_steps; exact hB (p, ticks, ()) ml ⟨sl, hdl, hcv_l, hfl_l, hml⟩
      · clear hc; fc_steps; exact hB (p, ticks, ()) ml ⟨sl, hdl, hcv_l, hfl_l, hml⟩
    · intro B L _ hL; fc_let
      have hmem0 : (0#64 : BitVec 64).toNat = s1.core.arena_len ∨
          (0#64 : BitVec 64).toNat ∈ fullArenaClauseRefsCore s1.core := by
        rcases Nat.eq_zero_or_pos s1.core.arena_len with hz | hpos
        · exact Or.inl hz.symm
        · exact Or.inr (fullArenaClauseRefs_zero_mem hd1.2.1 hpos)
      exact hL (s1.core.arena_len - 0) (0#64, 0#64, ()) m1
        ⟨s1, hd1, rfl, rfl, rfl, rfl, Nat.zero_le _, hmem0, rfl, hm1⟩

/-! ## 5. `full_cong_find_units_equivs_wp` (`m6CongFindUnitsEquivsSpec`) -/

section M6LocalTactics
open Lean Meta Elab Tactic

/-- Fast `O(1)` head splitter that unrolls 1-block `Expr.group` join wrappers like
`fc_split_fast`, then splits `Expr.jnz` without `c0_bound`. -/
scoped elab "m6_split_fast" : tactic => do
  focus do
    LeanQbe.T.C0HeadStep.headSteps
      { unrollGroup := true, splitJnz := false, strictMem := false } 2000
    let g ← getMainGoal
    let ty ← instantiateMVars (← g.getType)
    if ty.isAppOfArity ``LeanQbe.T.wp 6 then
      let e := (ty.getArg! 4).consumeMData
      if e.isAppOfArity ``LeanQbe.T.Expr.jnz 6 then
        let c0 := (e.getArg! 3).consumeMData
        if c0.isAppOf ``LeanQbe.T.Arg.var && c0.getAppNumArgs ≥ 2 then
          let inner0 := c0.appArg!
          let inner := FullM3CongBva.M3HeadTactics.m3PeelBlocks inner0
          if inner != inner0 then
            let cArg := Lean.mkAppN c0.getAppFn
              (c0.getAppArgs.set! (c0.getAppNumArgs - 1) inner)
            let e' := Lean.mkAppN e.getAppFn (e.getAppArgs.set! 3 cArg)
            let g' ← g.change (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e'))
              (checkDefEq := false)
            setGoals [g']
        else
          let cArg ← whnf c0
          let e' := Lean.mkAppN e.getAppFn (e.getAppArgs.set! 3 cArg)
          let g' ← g.change (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e'))
            (checkDefEq := false)
          setGoals [g']
    let hcId := Lean.mkIdent `hc
    let tac1 ← `(tactic| refine Full.FullCongTactics.wp_jnz_var (fun $hcId => ?_)
      (fun $hcId => ?_))
    let tac2 ← `(tactic| refine C0HeadStep.head_wp_jnz rfl (fun $hcId => ?_)
      (fun $hcId => ?_))
    evalTactic tac1 <|> evalTactic tac2

end M6LocalTactics

private theorem nat_two_mul_xor1 (k : Nat) : (2 * k) ^^^ 1 = 2 * k + 1 := by
  apply Nat.eq_of_testBit_eq; intro t; cases t with
  | zero => simp [Nat.add_comm]
  | succ t' =>
    rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    simp [show (1 / 2 : Nat) = 0 from rfl, show (2 * k + 1) / 2 = k by omega]

private theorem bv64_add1_lt_of {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem bv64_add2_lt_of {x : BitVec 64} (h : x.toNat + 2 < 2 ^ 64) :
    (x + 2#64).toNat = x.toNat + 2 := by
  rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl, Nat.mod_eq_of_lt h]

theorem full_cong_find_units_equivs_wp (Γ : Env)
    (hAddUnit : ∀ args m Q X, fullAddUnitSpec args m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] args m Q X)
    (hEquivFold : ∀ args m Q X, FullM3CongBva.m3CongEquivFoldSpec args m Q X →
      Γ "full_cong_equiv_fold" [i64, i32, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, m6CongFindUnitsEquivsSpec args m Q X →
      Func.wp Γ full_cong_find_units_equivs_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hd, hrepr, hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; unfold dimacsBound at hmx hwc
  have hcv0 := hd.1.core_ok.cur_vars_le
  have hnl_eq : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat = 2 * s.core.cur_vars :=
    bv64_mul2_lt (by omega)
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i64])
    (fun (v, ()) mv => ∃ sv : FullState,
      FullDenseInvW c F0 F_cur sv ∧ sv.core.cur_vars = s.core.cur_vars ∧
      sv.core.fuel = s.core.fuel ∧ FullCongReprInv F_cur (2 * sv.core.cur_vars) sv.core.repr ∧
      v.toNat ≤ s.core.cur_vars ∧ (FullMem c sv ⋆ R) mv)
    (fun (v, ()) _ => s.core.cur_vars - v.toNat)
    (fun Jv1 hJv1 => by
      m3_let; exact hJv1 (0#64, ()) m0 ⟨s, hd, rfl, rfl, hrepr, Nat.zero_le _, hm0⟩)
    (fun Jv1 (v, ()) mv ⟨sv, hdv, hcv_v, hfl_v, hrepr_v, hv_le, hmv⟩ ihv1 => ?_)
  have hcv_vle := hdv.1.core_ok.cur_vars_le
  have hfll := hdv.1.core_ok.flags_len; have hvll := hdv.1.core_ok.vals_len
  m6_split_fast
  · have hv_lt : v.toNat < s.core.cur_vars := by
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
      exact hc
    clear hc; m6_split_fast
    · clear hc
      have hv1_n : (v + 1#64).toNat = v.toNat + 1 := bv64_add1_lt_of (by omega)
      have hv2_n : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
        rw [bv64_shl1_toNat]; exact Nat.mod_eq_of_lt (by omega)
      c0_hsteps_nogrp
      refine wp_join_group (ts := [])
        (fun () mc => ∃ sc : FullState,
          FullDenseInvW c F0 F_cur sc ∧ sc.core.cur_vars = s.core.cur_vars ∧
          sc.core.fuel = s.core.fuel ∧
          FullCongReprInv F_cur (2 * sc.core.cur_vars) sc.core.repr ∧
          (FullMem c sc ⋆ R) mc)
        (fun _ ⟨⟩ mc ⟨sc, hdc, hcv_c, hfl_c, hrepr_c, hmc⟩ => by
          c0_hsteps!; exact ihv1 (v + 1#64, ()) mc (by dsimp only; omega)
            ⟨sc, hdc, hcv_c, hfl_c, hrepr_c, by omega, hmc⟩)
        ?_
      intro Jcont1 hJcont1
      have hskip1 : Jcont1 () mv := hJcont1 () mv ⟨sv, hdv, hcv_v, hfl_v, hrepr_v, hmv⟩
      m6_split_fast
      · c0_hsteps!; exact hskip1
      · clear hc; m6_split_fast
        · c0_hsteps!; exact hskip1
        · clear hc; m3_let
          refine wp_loop_inv (ts := [i64])
            (fun (sign, ()) ms => ∃ ss : FullState,
              FullDenseInvW c F0 F_cur ss ∧ ss.core.cur_vars = s.core.cur_vars ∧
              ss.core.fuel = s.core.fuel ∧
              FullCongReprInv F_cur (2 * ss.core.cur_vars) ss.core.repr ∧
              sign.toNat ≤ 2 ∧ (FullMem c ss ⋆ R) ms)
            (fun (sign, ()) _ => 2 - sign.toNat)
            (fun Js hJs => by c0_hsteps!; exact hJs (0#64, ()) mv ⟨sv, hdv, hcv_v, hfl_v, hrepr_v,
              Nat.zero_le _, hmv⟩)
            (fun Js (sign, ()) ms ⟨ss, hds, hcv_s, hfl_s, hrepr_s, hsn_le, hms⟩ ihs => ?_)
          have hcv_sle := hds.1.core_ok.cur_vars_le
          have hvll_s := hds.1.core_ok.vals_len
          m6_split_fast
          · have hsn_lt : sign.toNat < 2 := by
              rw [BitVec.ult, decide_eq_true_eq] at hc; exact hc
            clear hc; m6_split_fast
            · clear hc; m6_split_fast
              · clear hc
                let lit := ((v <<< (1 : Nat)) ||| sign).setWidth 32
                have hlit_n : lit.toNat = 2 * v.toNat + sign.toNat :=
                  bv64_shl1_or01_toNat (by omega) hsn_lt
                have hlit_lt : lit.toNat < 2 * ss.core.cur_vars := by omega
                have hwbd := fullWatchBounds_of_dense hds lit.toNat hlit_lt
                have hwvl := hds.1.core_ok.wvec_len; have hwsl := hds.1.core_ok.wstk_len_arr
                obtain ⟨hshl, hshl1⟩ := bv64_shl1_add1_lt (l := lit.setWidth 64)
                  (by rw [bv_zext32_toNat]; omega)
                have hw0_lt : (lit.setWidth 64 <<< (1 : Nat)).toNat < ss.core.wvec.length := by
                  rw [hshl, bv_zext32_toNat]; omega
                have hw1_lt :
                    (lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat < ss.core.wvec.length := by
                  rw [hshl1, bv_zext32_toNat]; omega
                have hshl_wv : ss.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hw0_lt =
                    ss.core.wvec[2 * lit.toNat]'(by omega) :=
                  list_getElem_congr (by rw [hshl, bv_zext32_toNat]) hw0_lt (by omega)
                have hshl1_wv :
                    ss.core.wvec[(lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat]'hw1_lt =
                      ss.core.wvec[2 * lit.toNat + 1]'(by omega) :=
                  list_getElem_congr (by rw [hshl1, bv_zext32_toNat]) hw1_lt (by omega)
                let off := (ss.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hw0_lt).setWidth 64
                let wsz :=
                  (ss.core.wvec[(lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat]'hw1_lt).setWidth 64
                have hoff_n : off.toNat = fullWatchOffCore ss.core lit.toNat := by
                  dsimp only [off]; unfold fullWatchOffCore
                  rw [hshl_wv, List.getElem?_eq_getElem (by omega), Option.getD_some,
                    bv_zext32_toNat]
                have hwsz_n : wsz.toNat = fullWatchSizeCore ss.core lit.toNat := by
                  dsimp only [wsz]; unfold fullWatchSizeCore
                  rw [hshl1_wv, List.getElem?_eq_getElem (by omega), Option.getD_some,
                    bv_zext32_toNat]
                have hend_n : (off + wsz).toNat = off.toNat + wsz.toNat := by
                  rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
                have hslice0 := dense_slice_of_inv hds hlit_lt
                rw [← hoff_n, ← hwsz_n] at hslice0
                c0_hsteps_nogrp
                refine wp_loop_break_group (brkTs := [.bool, i64]) (lpTs := [i64])
                  (fun (found_u, _, ()) mb => ∃ lmb : List (BitVec 8),
                    lmb.length = 2 * c.max_vars ∧
                    (∀ q < 2 * c.max_vars, lmb[q]?.getD 0#8 ≠ 0#8 →
                      inSliceBins ss.core.wstk off.toNat (off + wsz).toNat
                        (2 * ss.core.cur_vars) q) ∧
                    (found_u = true →
                      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat])) ∧
                    (FullMem c { ss with core := { ss.core with lit_mark := lmb } } ⋆ R) mb)
                  (fun rem (p, ()) mp => ∃ lmp : List (BitVec 8),
                    lmp.length = 2 * c.max_vars ∧ off.toNat ≤ p.toNat ∧
                    p.toNat ≤ (off + wsz).toNat ∧ rem = (off + wsz).toNat - p.toNat ∧
                    SliceChain ss.core.wstk off.toNat p.toNat ∧
                    DenseWatchSliceOk F_cur ss.core lit.toNat p.toNat
                      ((off + wsz).toNat - p.toNat) ∧
                    (∀ q < 2 * c.max_vars, lmp[q]?.getD 0#8 ≠ 0#8 →
                      inSliceBins ss.core.wstk off.toNat (off + wsz).toNat
                        (2 * ss.core.cur_vars) q ∧
                      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, q])) ∧
                    (FullMem c { ss with core := { ss.core with lit_mark := lmp } } ⋆ R) mp)
                  ?_ ?_ ?_
                · rintro _ ⟨found_u, _, ⟨⟩⟩ mb ⟨lmb, hlmb_l, hlmb_in, hfu_ent, hmb⟩
                  c0_hsteps_nogrp
                  refine wp_loop_inv (ts := [i64])
                    (fun (pc, ()) mc => ∃ lmc : List (BitVec 8),
                      lmc.length = 2 * c.max_vars ∧ off.toNat ≤ pc.toNat ∧
                      pc.toNat ≤ (off + wsz).toNat ∧
                      DenseWatchSliceOk F_cur ss.core lit.toNat pc.toNat
                        ((off + wsz).toNat - pc.toNat) ∧
                      (∀ q < 2 * c.max_vars, lmc[q]?.getD 0#8 ≠ 0#8 →
                        inSliceBins ss.core.wstk pc.toNat (off + wsz).toNat
                          (2 * ss.core.cur_vars) q) ∧
                      (FullMem c { ss with core := { ss.core with lit_mark := lmc } } ⋆ R) mc)
                    (fun (pc, ()) _ => (off + wsz).toNat - pc.toNat)
                    (fun Jc hJc => by
                      c0_hsteps!
                      exact hJc (off, ()) mb ⟨lmb, hlmb_l, Nat.le_refl _, by omega,
                        (by rwa [hend_n, Nat.add_sub_cancel_left]), hlmb_in, hmb⟩)
                    (fun Jc (pc, ()) mc ⟨lmc, hlmc_l, hpc_lo, hpc_hi, hsc, hlmc_in, hmc⟩ ihc => ?_)
                  m6_split_fast
                  · have hpc_lt : pc.toNat < (off + wsz).toNat := by
                      simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                    clear hc
                    obtain ⟨w0, hw0_get, hpop⟩ := dense_slice_pop_step hsc (by omega)
                    have hpc_w : pc.toNat < ss.core.wstk.length := by omega
                    have hw0_eq : ss.core.wstk[pc.toNat]'hpc_w = w0 := by
                      rw [List.getElem?_eq_getElem hpc_w] at hw0_get
                      exact Option.some.inj hw0_get
                    subst w0
                    rcases hpop with ⟨hbf, hent_w, hsc_next⟩ | ⟨hbf, hrem2, hsc_next⟩
                    · have hpc1_n : (pc + 1#64).toNat = pc.toNat + 1 :=
                        bv64_add1_lt_of (by omega)
                      m6_split_fast
                      · exfalso; exact hbf (beq_iff_eq.mp hc)
                      · clear hc; m6_split_fast
                        · have hot_lt :
                              ((ss.core.wstk[pc.toNat]'hpc_w) &&& 0x7FFFFFFF#32).toNat <
                                2 * ss.core.cur_vars := by
                            rw [hcv_s]; simp only [BitVec.ult, decide_eq_true_eq,
                              bv_zext32_toNat] at hc
                            rwa [hnl_eq] at hc
                          have hot_lm :
                              (BitVec.setWidth 64
                                ((ss.core.wstk[pc.toNat]'hpc_w) &&& 0x7FFFFFFF#32)).toNat <
                                ({ ss with core := { ss.core with lit_mark := lmc } } :
                                  FullState).core.lit_mark.length := by
                            dsimp only; rw [bv_zext32_toNat]; omega
                          c0_hsteps!
                          refine ihc (pc + 1#64, ()) m (by dsimp only; omega)
                            ⟨lmc.set ((ss.core.wstk[pc.toNat]'hpc_w) &&& 0x7FFFFFFF#32).toNat 0#8,
                             by simp [hlmc_l], by omega, by omega, by rwa [hpc1_n],
                             fun q hq hnz => ?_, hm⟩
                          by_cases hqe : q =
                              ((ss.core.wstk[pc.toNat]'hpc_w) &&& 0x7FFFFFFF#32).toNat
                          · subst hqe
                            rw [List.getElem?_set_self (by
                              dsimp only at hot_lm; rw [bv_zext32_toNat] at hot_lm; omega),
                              Option.getD_some] at hnz
                            exact absurd rfl hnz
                          · rw [List.getElem?_set_ne (Ne.symm hqe)] at hnz
                            rw [hpc1_n]
                            exact inSliceBins_clear_bin hpc_lt hw0_get hbf hqe (hlmc_in q hq hnz)
                        · have hge_ot :
                              2 * ss.core.cur_vars ≤
                                ((ss.core.wstk[pc.toNat]'hpc_w) &&& 0x7FFFFFFF#32).toNat := by
                            rw [hcv_s]; simp only [BitVec.ult, decide_eq_false_iff_not,
                              bv_zext32_toNat, hnl_eq] at hc
                            exact Nat.not_lt.mp hc
                          clear hc; c0_hsteps!
                          exact ihc (pc + 1#64, ()) mc (by dsimp only; omega)
                            ⟨lmc, hlmc_l, by omega, by omega, by rwa [hpc1_n], fun q hq hnz => by
                              rw [hpc1_n]; exact inSliceBins_clear_bin_of_ge hpc_lt hw0_get hbf
                                hge_ot (hlmc_in q hq hnz), hmc⟩
                    · have hpc2_n : (pc + 2#64).toNat = pc.toNat + 2 :=
                        bv64_add2_lt_of (by omega)
                      m6_split_fast
                      · clear hc; c0_hsteps!
                        refine ihc (pc + 2#64, ()) mc (by dsimp only; omega)
                          ⟨lmc, hlmc_l, by omega, by omega, by rwa [hpc2_n], fun q hq hnz => by
                            rw [hpc2_n]; exact inSliceBins_clear_occ hpc_lt hw0_get hbf
                              (hlmc_in q hq hnz), hmc⟩
                      · exfalso; exact (beq_eq_false_iff_ne.mp hc) hbf
                  · have hpc_e : (off + wsz).toNat ≤ pc.toNat := by
                      simp only [BitVec.ult, decide_eq_false_iff_not] at hc; exact Nat.not_lt.mp hc
                    have hclr_mc : ∀ q < 2 * c.max_vars, lmc[q]?.getD 0#8 = 0#8 := fun q hq =>
                      Classical.byContradiction fun hnz =>
                        (inSliceBins_false_of_ge hpc_e).mp (hlmc_in q hq hnz)
                    let s_clr : FullState := { ss with core := { ss.core with lit_mark := lmc } }
                    have hd_clr : FullDenseInvW c F0 F_cur s_clr :=
                      fullDenseInvW_with_lm_clear hds hlmc_l hclr_mc
                    have hsn1_n : (sign + 1#64).toNat = sign.toNat + 1 :=
                      bv64_add1_lt_of (by omega)
                    clear hc; m6_split_fast
                    · have hent_u := hfu_ent (by cases hc; rfl)
                      c0_hsteps!; m3_call hAddUnit
                      refine ⟨c, F0, F_cur, s_clr, R, rfl, hd_clr.1, hd_clr.2.1,
                        (fun _ => hent_u), hmc, ?_⟩
                      dsimp only
                      intro ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
                        ph' ta' ba' pt' pb' hp' ps' hlen_hp qsi' qss' mu hlen_u hw_u hcl_u
                        hu_ok hu_fail hmu
                      let s_u : FullState :=
                        { s_clr with
                          core := { s_clr.core with
                            vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                            cur_level := cl', unassigned := unass', unflushed := unfl',
                            inconsistent := inc' }
                          scratch := { s_clr.scratch with
                            phases := ph', target_assigned := ta', best_assigned := ba',
                            phases_target := pt', phases_best := pb', heap := hp', pos := ps',
                            heap_len := hlen_hp, q_search_idx := qsi', q_search_stamp := qss' } }
                      obtain ⟨hmk_u, hnd_u, hext_u, _, hdm_u⟩ :=
                        FullM3CongBva.fullAddUnitSpec_fullDenseInvW (s' := s_u)
                          hd_clr.2.2.1 hd_clr.2.2.2.1 hd_clr.2.2.2.2.1 hd_clr.2.2.2.2.2.2
                          hcl_u rfl rfl rfl rfl rfl rfl rfl
                      have hdu : FullDenseInvW c F0 F_cur s_u :=
                        ⟨hlen_u, hw_u, hmk_u, hnd_u, hext_u, hcl_u, hdm_u⟩
                      have hcv_us : s_u.core.cur_vars = s.core.cur_vars := hcv_s
                      have hfl_us : s_u.core.fuel = s.core.fuel := hfl_s
                      have hrepr_u' :
                          FullCongReprInv F_cur (2 * s_u.core.cur_vars) s_u.core.repr := hrepr_s
                      m6_split_fast
                      · clear hc; c0_hsteps!
                        let s_uc : FullState :=
                          { s_u with scratch :=
                            { s_u.scratch with cong_cnt := s_u.scratch.cong_cnt + 1#64 } }
                        exact ihs (sign + 1#64, ()) m (by dsimp only; rw [hsn1_n]; omega)
                          ⟨s_uc, fullDenseInvW_with_cong_cnt hdu _, hcv_us, hfl_us,
                           hrepr_u', by rw [hsn1_n]; omega, hm⟩
                      · obtain ⟨huns_u, _⟩ := hu_ok (by dsimp only [s_clr]; exact hlit_lt)
                          (by cases hc; rfl)
                        c0_hsteps!; exact hQ 20#64 s_u mu hdu hcv_us hfl_us hrepr_u'
                          (Or.inr rfl) (fun _ => huns_u) hmu
                    · c0_hsteps!
                      exact ihs (sign + 1#64, ()) mc (by dsimp only; rw [hsn1_n]; omega)
                        ⟨s_clr, hd_clr, hcv_s, hfl_s, hrepr_s, by rw [hsn1_n]; omega, hmc⟩
                · rintro B1 L1 rem ⟨p, ⟨⟩⟩ mp hB1 hL1
                    ⟨lmp, hlmp_l, hp_lo, hp_hi, rfl, hch, hsp, hmp_in, hmp⟩
                  m6_split_fast
                  · have hp_lt : p.toNat < (off + wsz).toNat := by
                      simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                    clear hc
                    obtain ⟨w0, hw0_get, hpop⟩ := dense_slice_pop_step hsp (by omega)
                    have hp_w : p.toNat < ss.core.wstk.length := by omega
                    have hw0_eq : ss.core.wstk[p.toNat]'hp_w = w0 := by
                      rw [List.getElem?_eq_getElem hp_w] at hw0_get; exact Option.some.inj hw0_get
                    subst w0
                    rcases hpop with ⟨hbf, hent_w, hsp_next⟩ | ⟨hbf, hrem2, hsp_next⟩
                    · have hp1_n : (p + 1#64).toNat = p.toNat + 1 :=
                        bv64_add1_lt_of (by omega)
                      m6_split_fast
                      · exfalso; exact hbf (beq_iff_eq.mp hc)
                      · clear hc; m6_split_fast
                        · have hot_lt :
                              ((ss.core.wstk[p.toNat]'hp_w) &&& 0x7FFFFFFF#32).toNat <
                                2 * ss.core.cur_vars := by
                            rw [hcv_s]; simp only [BitVec.ult, decide_eq_true_eq,
                              bv_zext32_toNat] at hc
                            rwa [hnl_eq] at hc
                          have hot_x :
                              (BitVec.setWidth 64
                                (((ss.core.wstk[p.toNat]'hp_w) &&& 0x7FFFFFFF#32) ^^^ 1#32)).toNat <
                                lmp.length := by
                            rw [bv_zext32_toNat, hlmp_l, bv32_xor1_eq_litNeg]
                            exact Nat.lt_of_lt_of_le (litNeg_lt_two_mul hot_lt) (by omega)
                          have hot_lm :
                              (BitVec.setWidth 64
                                ((ss.core.wstk[p.toNat]'hp_w) &&& 0x7FFFFFFF#32)).toNat <
                                ({ ss with core := { ss.core with lit_mark := lmp } } :
                                  FullState).core.lit_mark.length := by
                            dsimp only; rw [bv_zext32_toNat]; omega
                          m6_split_fast
                          · have heq_lit :
                                (ss.core.wstk[p.toNat]'hp_w) &&& 0x7FFFFFFF#32 = lit :=
                              beq_iff_eq.mp hc
                            rw [congrArg BitVec.toNat heq_lit] at hent_w
                            have hent_dup : (cnfOfClauses F_cur).EntailsClause
                                (cnfClause [lit.toNat]) :=
                              entails_unit_of_pair_dup hent_w
                            c0_hsteps!
                            exact hB1 (true, p + 1#64, ()) mp
                              ⟨lmp, hlmp_l, fun q hq hnz => (hmp_in q hq hnz).1,
                               fun _ => hent_dup, hmp⟩
                          · clear hc; m6_split_fast
                            · have hnz_neg :
                                  lmp[(((ss.core.wstk[p.toNat]'hp_w) &&& 0x7FFFFFFF#32) ^^^
                                      1#32).toNat]?.getD 0#8 ≠ 0#8 := by
                                intro heq
                                have hzx : (BitVec.setWidth 64
                                    (((ss.core.wstk[p.toNat]'hp_w) &&& 0x7FFFFFFF#32) ^^^
                                      1#32)).toNat =
                                    (((ss.core.wstk[p.toNat]'hp_w) &&& 0x7FFFFFFF#32) ^^^
                                      1#32).toNat := bv_zext32_toNat _
                                rw [← hzx, List.getElem?_eq_getElem (by
                                    rw [hzx]; rw [bv_zext32_toNat] at hot_x; exact hot_x),
                                  Option.getD_some] at heq
                                exact (bne_iff_ne.mp hc)
                                  (by dsimp only
                                      exact (congrArg (BitVec.setWidth 32) heq).trans (by decide))
                              have hent_other := (hmp_in _ (by
                                rw [bv_zext32_toNat] at hot_x; omega) hnz_neg).2
                              rw [BitVec.toNat_xor] at hent_other
                              have hent_u := entails_unit_of_pair_and_neg hent_w hent_other
                              c0_hsteps!
                              exact hB1 (true, p + 1#64, ()) mp
                                ⟨lmp, hlmp_l, fun q hq hnz => (hmp_in q hq hnz).1,
                                 fun _ => hent_u, hmp⟩
                            · clear hc; c0_hsteps!
                              refine hL1 ((off + wsz).toNat - (p + 1#64).toNat) (p + 1#64, ()) m
                                (by omega)
                                ⟨lmp.set ((ss.core.wstk[p.toNat]'hp_w) &&& 0x7FFFFFFF#32).toNat 1#8,
                                 by simp [hlmp_l], by omega, by omega, rfl,
                                 hp1_n ▸ .bin hch hw0_get hbf, by rwa [hp1_n],
                                 fun q hq hnz => ?_, hm⟩
                              by_cases hqe :
                                  q = ((ss.core.wstk[p.toNat]'hp_w) &&& 0x7FFFFFFF#32).toNat
                              · subst hqe
                                exact ⟨inSliceBins_here hch hp_lt hw0_get hbf (by omega), hent_w⟩
                              · rw [List.getElem?_set_ne (Ne.symm hqe)] at hnz
                                exact hmp_in q hq hnz
                        · clear hc; c0_hsteps!
                          exact hL1 ((off + wsz).toNat - (p + 1#64).toNat) (p + 1#64, ()) mp
                            (by omega) ⟨lmp, hlmp_l, by omega, by omega, rfl,
                              hp1_n ▸ .bin hch hw0_get hbf, by rwa [hp1_n], hmp_in, hmp⟩
                    · have hp2_n : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
                      m6_split_fast
                      · clear hc; c0_hsteps!
                        exact hL1 ((off + wsz).toNat - (p + 2#64).toNat) (p + 2#64, ()) mp
                          (by omega) ⟨lmp, hlmp_l, by omega, by omega, rfl,
                            hp2_n ▸ .occ hch hw0_get hbf, by rwa [hp2_n], hmp_in, hmp⟩
                      · exfalso; exact (beq_eq_false_iff_ne.mp hc) hbf
                  · clear hc; c0_hsteps!
                    exact hB1 (false, p, ()) mp
                      ⟨lmp, hlmp_l, fun q hq hnz => (hmp_in q hq hnz).1,
                       (fun hf => by cases hf), hmp⟩
                · intro B1 L1 _ hL1; c0_hsteps!
                  exact hL1 ((off + wsz).toNat - off.toNat) (off, ()) ms
                    ⟨ss.core.lit_mark, hds.1.core_ok.lit_mark_len, Nat.le_refl _, by omega, rfl,
                     .here, (by rwa [hend_n, Nat.add_sub_cancel_left]),
                     fun q hq hnz => absurd (hds.2.2.1.2 q hq) hnz, hms⟩
              · clear hc; c0_hsteps!
                exact ihv1 (v + 1#64, ()) ms (by dsimp only; omega)
                  ⟨ss, hds, hcv_s, hfl_s, hrepr_s, by omega, hms⟩
            · clear hc; c0_hsteps!
              exact ihv1 (v + 1#64, ()) ms (by dsimp only; omega)
                ⟨ss, hds, hcv_s, hfl_s, hrepr_s, by omega, hms⟩
          · clear hc; c0_hsteps!
            exact ihv1 (v + 1#64, ()) ms (by dsimp only; omega)
              ⟨ss, hds, hcv_s, hfl_s, hrepr_s, by omega, hms⟩
    · have hinc_ne : sv.core.inconsistent ≠ 0#64 := fun h => by rw [h] at hc; simp at hc
      clear hc; c0_hsteps_nogrp
      refine wp_loop_inv (ts := [i64])
        (fun (v2, ()) mv2 => ∃ sv2 : FullState,
          FullDenseInvW c F0 F_cur sv2 ∧ sv2.core.cur_vars = s.core.cur_vars ∧
          sv2.core.fuel = s.core.fuel ∧
          FullCongReprInv F_cur (2 * sv2.core.cur_vars) sv2.core.repr ∧
          sv2.core.inconsistent ≠ 0#64 ∧ v2.toNat ≤ s.core.cur_vars ∧ (FullMem c sv2 ⋆ R) mv2)
        (fun (v2, ()) _ => s.core.cur_vars - v2.toNat)
        (fun _ hJ => by c0_hsteps!; exact hJ (0#64, ()) mv ⟨sv, hdv, hcv_v, hfl_v, hrepr_v,
          hinc_ne, Nat.zero_le _, hmv⟩)
        (fun _ (v2, ()) mv2 ⟨sv2, hdv2, hcv2, hfl2, hrepr2, hinc2, hv2_le, hmv2⟩ _ => by
          m6_split_fast
          · clear hc; m6_split_fast
            · have : False := hinc2 (beq_iff_eq.mp hc)
              cases this
            · c0_hsteps!
              exact hQ 20#64 sv2 mv2 hdv2 hcv2 hfl2 hrepr2 (Or.inr rfl)
                (fun _ => FullM3CongBva.unsat_of_inconsistent_w hdv2.2.1 hinc2) hmv2
          · c0_hsteps!
            exact hQ 20#64 sv2 mv2 hdv2 hcv2 hfl2 hrepr2 (Or.inr rfl)
              (fun _ => FullM3CongBva.unsat_of_inconsistent_w hdv2.2.1 hinc2) hmv2)
  · clear hc; c0_hsteps_nogrp
    refine wp_loop_inv (ts := [i64])
      (fun (v, ()) mv => ∃ sv : FullState,
        FullDenseInvW c F0 F_cur sv ∧ sv.core.cur_vars = s.core.cur_vars ∧
        sv.core.fuel = s.core.fuel ∧ FullCongReprInv F_cur (2 * sv.core.cur_vars) sv.core.repr ∧
        v.toNat ≤ s.core.cur_vars ∧ (FullMem c sv ⋆ R) mv)
      (fun (v, ()) _ => s.core.cur_vars - v.toNat)
      (fun _ hJv2 => by
        c0_hsteps!; exact hJv2 (0#64, ()) mv ⟨sv, hdv, hcv_v, hfl_v, hrepr_v, Nat.zero_le _, hmv⟩)
      (fun Jv2 (v, ()) mv ⟨sv2, hdv2, hcv2, hfl2, hrepr2, hv2_le, hmv2⟩ ihv2 => ?_)
    clear hcv_vle hfll hvll hdv hcv_v hfl_v hrepr_v hv_le hmv ihv1
    clear sv
    have hcv2_le := hdv2.1.core_ok.cur_vars_le
    have hfll2 := hdv2.1.core_ok.flags_len; have hvll2 := hdv2.1.core_ok.vals_len
    m6_split_fast
    · have hv2_lt : v.toNat < s.core.cur_vars := by
        simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
        exact hc
      clear hc; m6_split_fast
      · clear hc
        have hv1_n : (v + 1#64).toNat = v.toNat + 1 := bv64_add1_lt_of (by omega)
        have hv2_n : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
          rw [bv64_shl1_toNat]; exact Nat.mod_eq_of_lt (by omega)
        c0_hsteps_nogrp
        refine wp_join_group (ts := [])
          (fun () mc => ∃ sc : FullState,
            FullDenseInvW c F0 F_cur sc ∧ sc.core.cur_vars = s.core.cur_vars ∧
            sc.core.fuel = s.core.fuel ∧
            FullCongReprInv F_cur (2 * sc.core.cur_vars) sc.core.repr ∧
            (FullMem c sc ⋆ R) mc)
          (fun _ ⟨⟩ mc ⟨sc, hdc, hcv_c, hfl_c, hrepr_c, hmc⟩ => by
            c0_hsteps!; exact ihv2 (v + 1#64, ()) mc (by dsimp only; omega)
              ⟨sc, hdc, hcv_c, hfl_c, hrepr_c, by omega, hmc⟩)
          ?_
        intro Jcont2 hJcont2
        have hskip2 : Jcont2 () mv := hJcont2 () mv ⟨sv2, hdv2, hcv2, hfl2, hrepr2, hmv2⟩
        m6_split_fast
        · c0_hsteps!; exact hskip2
        · clear hc; m6_split_fast
          · c0_hsteps!; exact hskip2
          · clear hc
            let lit := (v <<< (1 : Nat)).setWidth 32
            have hlit_n : lit.toNat = 2 * v.toNat := by dsimp only [lit]; bv_omega
            have hlit_lt : lit.toNat < 2 * sv2.core.cur_vars := by omega
            have hwbd := fullWatchBounds_of_dense hdv2 lit.toNat hlit_lt
            have hwvl := hdv2.1.core_ok.wvec_len; have hwsl := hdv2.1.core_ok.wstk_len_arr
            obtain ⟨hshl, hshl1⟩ := bv64_shl1_add1_lt (l := lit.setWidth 64)
              (by rw [bv_zext32_toNat]; omega)
            have hw0_lt : (lit.setWidth 64 <<< (1 : Nat)).toNat < sv2.core.wvec.length := by
              rw [hshl, bv_zext32_toNat]; omega
            have hw1_lt :
                (lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat < sv2.core.wvec.length := by
              rw [hshl1, bv_zext32_toNat]; omega
            have hshl_wv : sv2.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hw0_lt =
                sv2.core.wvec[2 * lit.toNat]'(by omega) :=
              list_getElem_congr (by rw [hshl, bv_zext32_toNat]) hw0_lt (by omega)
            have hshl1_wv :
                sv2.core.wvec[(lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat]'hw1_lt =
                  sv2.core.wvec[2 * lit.toNat + 1]'(by omega) :=
              list_getElem_congr (by rw [hshl1, bv_zext32_toNat]) hw1_lt (by omega)
            let off := (sv2.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hw0_lt).setWidth 64
            let wsz :=
              (sv2.core.wvec[(lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat]'hw1_lt).setWidth 64
            have hoff_n : off.toNat = fullWatchOffCore sv2.core lit.toNat := by
              dsimp only [off]; unfold fullWatchOffCore
              rw [hshl_wv, List.getElem?_eq_getElem (by omega), Option.getD_some, bv_zext32_toNat]
            have hwsz_n : wsz.toNat = fullWatchSizeCore sv2.core lit.toNat := by
              dsimp only [wsz]; unfold fullWatchSizeCore
              rw [hshl1_wv, List.getElem?_eq_getElem (by omega), Option.getD_some, bv_zext32_toNat]
            have hend_n : (off + wsz).toNat = off.toNat + wsz.toNat := by
              rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
            have hslice_pos := dense_slice_of_inv hdv2 hlit_lt
            rw [← hoff_n, ← hwsz_n] at hslice_pos
            c0_hsteps_nogrp
            refine wp_loop_inv (ts := [i64, .bool])
              (fun (p, any, ()) ma => ∃ lma : List (BitVec 8),
                lma.length = 2 * c.max_vars ∧ off.toNat ≤ p.toNat ∧
                p.toNat ≤ (off + wsz).toNat ∧ SliceChain sv2.core.wstk off.toNat p.toNat ∧
                DenseWatchSliceOk F_cur sv2.core lit.toNat p.toNat
                  ((off + wsz).toNat - p.toNat) ∧
                  (any = false → ∀ q < 2 * c.max_vars, lma[q]?.getD 0#8 = 0#8) ∧
                  (∀ q < 2 * c.max_vars, lma[q]?.getD 0#8 ≠ 0#8 →
                  v.toNat < q / 2 ∧
                  inSliceBins sv2.core.wstk off.toNat (off + wsz).toNat
                    (2 * sv2.core.cur_vars) q ∧
                  (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, q])) ∧
                (FullMem c { sv2 with core := { sv2.core with lit_mark := lma } } ⋆ R) ma)
              (fun (p, _, ()) _ => (off + wsz).toNat - p.toNat)
              (fun Ja hJa => by
                c0_hsteps!
                exact hJa (off, false, ()) mv
                  ⟨sv2.core.lit_mark, hdv2.1.core_ok.lit_mark_len, Nat.le_refl _, by omega,
                   .here, (by rwa [hend_n, Nat.add_sub_cancel_left]),
                   fun _ q hq => hdv2.2.2.1.2 q hq,
                   fun q hq hnz => absurd (hdv2.2.2.1.2 q hq) hnz, hmv2⟩)
              (fun Ja (p, any, ()) ma ⟨lma, hlma_l, hp_lo, hp_hi, hch, hsp, hany_f, hlma_in, hma⟩
                iha => ?_)
            m6_split_fast
            · have hp_lt : p.toNat < (off + wsz).toNat := by
                simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
              clear hc
              obtain ⟨w0, hw0_get, hpop⟩ := dense_slice_pop_step hsp (by omega)
              have hp_w : p.toNat < sv2.core.wstk.length := by omega
              have hw0_eq : sv2.core.wstk[p.toNat]'hp_w = w0 := by
                rw [List.getElem?_eq_getElem hp_w] at hw0_get; exact Option.some.inj hw0_get
              subst w0
              rcases hpop with ⟨hbf, hent_w, hsp_next⟩ | ⟨hbf, hrem2, hsp_next⟩
              · have hp1_n : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
                m6_split_fast
                · exfalso; exact hbf (beq_iff_eq.mp hc)
                · clear hc; m6_split_fast
                  · have hot_lt :
                        ((sv2.core.wstk[p.toNat]'hp_w) &&& 0x7FFFFFFF#32).toNat <
                          2 * sv2.core.cur_vars := by
                      rw [hcv2]; simp only [BitVec.ult, decide_eq_true_eq, bv_zext32_toNat] at hc
                      rwa [hnl_eq] at hc
                    clear hc; m6_split_fast
                    · have hot_gt :
                          v.toNat <
                            ((sv2.core.wstk[p.toNat]'hp_w) &&& 0x7FFFFFFF#32).toNat / 2 := by
                        simp only [BitVec.ult, decide_eq_true_eq, bv_zext32_toNat,
                          BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hc
                        simpa using hc
                      have hot_lm :
                          (BitVec.setWidth 64
                            ((sv2.core.wstk[p.toNat]'hp_w) &&& 0x7FFFFFFF#32)).toNat <
                            ({ sv2 with core := { sv2.core with lit_mark := lma } } :
                              FullState).core.lit_mark.length := by
                        dsimp only; rw [bv_zext32_toNat]; omega
                      c0_hsteps!
                      refine iha (p + 1#64, true, ()) m (by dsimp only; omega)
                        ⟨lma.set ((sv2.core.wstk[p.toNat]'hp_w) &&& 0x7FFFFFFF#32).toNat 1#8,
                         by rw [List.length_set]; exact hlma_l,
                         by omega, by omega, hp1_n ▸ .bin hch hw0_get hbf,
                         by rwa [hp1_n], (fun hf => by cases hf), fun q hq hnz => ?_, hm⟩
                      by_cases hqe :
                          q = ((sv2.core.wstk[p.toNat]'hp_w) &&& 0x7FFFFFFF#32).toNat
                      · subst hqe
                        exact ⟨hot_gt, inSliceBins_here hch hp_lt hw0_get hbf (by omega), hent_w⟩
                      · rw [List.getElem?_set_ne (Ne.symm hqe)] at hnz; exact hlma_in q hq hnz
                    · clear hc; c0_hsteps!
                      exact iha (p + 1#64, any, ()) ma (by dsimp only; omega)
                        ⟨lma, hlma_l, by omega, by omega, hp1_n ▸ .bin hch hw0_get hbf,
                         by rwa [hp1_n], hany_f, hlma_in, hma⟩
                  · clear hc; c0_hsteps!
                    exact iha (p + 1#64, any, ()) ma (by dsimp only; omega)
                      ⟨lma, hlma_l, by omega, by omega, hp1_n ▸ .bin hch hw0_get hbf,
                       by rwa [hp1_n], hany_f, hlma_in, hma⟩
              · have hp2_n : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
                m6_split_fast
                · clear hc; c0_hsteps!
                  exact iha (p + 2#64, any, ()) ma (by dsimp only; omega)
                    ⟨lma, hlma_l, by omega, by omega, hp2_n ▸ .occ hch hw0_get hbf,
                     by rwa [hp2_n], hany_f, hlma_in, hma⟩
                · exfalso; exact (beq_eq_false_iff_ne.mp hc) hbf
            · clear hc
              let nlit := lit ^^^ 1#32
              have hnlit_n : nlit.toNat = 2 * v.toNat + 1 := by
                dsimp only [nlit]; rw [bv32_xor1_eq_litNeg, hlit_n]; exact nat_two_mul_xor1 v.toNat
              have hnlit_lt : nlit.toNat < 2 * sv2.core.cur_vars := by omega
              m6_split_fast
              · have hwbd_n := fullWatchBounds_of_dense hdv2 nlit.toNat hnlit_lt
                obtain ⟨hnshl, hnshl1⟩ := bv64_shl1_add1_lt (l := nlit.setWidth 64)
                  (by rw [bv_zext32_toNat]; omega)
                have hnw0_lt :
                    (nlit.setWidth 64 <<< (1 : Nat)).toNat < sv2.core.wvec.length := by
                  rw [hnshl, bv_zext32_toNat]; omega
                have hnw1_lt :
                    (nlit.setWidth 64 <<< (1 : Nat) + 1#64).toNat < sv2.core.wvec.length := by
                  rw [hnshl1, bv_zext32_toNat]; omega
                have hnshl_wv : sv2.core.wvec[(nlit.setWidth 64 <<< (1 : Nat)).toNat]'hnw0_lt =
                    sv2.core.wvec[2 * nlit.toNat]'(by omega) :=
                  list_getElem_congr (by rw [hnshl, bv_zext32_toNat]) hnw0_lt (by omega)
                have hnshl1_wv :
                    sv2.core.wvec[(nlit.setWidth 64 <<< (1 : Nat) + 1#64).toNat]'hnw1_lt =
                      sv2.core.wvec[2 * nlit.toNat + 1]'(by omega) :=
                  list_getElem_congr (by rw [hnshl1, bv_zext32_toNat]) hnw1_lt (by omega)
                let noff :=
                  (sv2.core.wvec[(nlit.setWidth 64 <<< (1 : Nat)).toNat]'hnw0_lt).setWidth 64
                let nwsz :=
                  (sv2.core.wvec[(nlit.setWidth 64 <<< (1 : Nat) + 1#64).toNat]'hnw1_lt).setWidth
                    64
                have hnoff_n : noff.toNat = fullWatchOffCore sv2.core nlit.toNat := by
                  dsimp only [noff]; unfold fullWatchOffCore
                  rw [hnshl_wv, List.getElem?_eq_getElem (by omega), Option.getD_some,
                    bv_zext32_toNat]
                have hnwsz_n : nwsz.toNat = fullWatchSizeCore sv2.core nlit.toNat := by
                  dsimp only [nwsz]; unfold fullWatchSizeCore
                  rw [hnshl1_wv, List.getElem?_eq_getElem (by omega), Option.getD_some,
                    bv_zext32_toNat]
                have hnend_n : (noff + nwsz).toNat = noff.toNat + nwsz.toNat := by
                  rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
                have hslice_neg := dense_slice_of_inv hdv2 hnlit_lt
                rw [← hnoff_n, ← hnwsz_n] at hslice_neg
                have htmpl := hdv2.1.core_ok.tmp_len_arr
                c0_hsteps_nogrp
                refine wp_loop_inv (ts := [i64, i64])
                  (fun (pn, mcnt, ()) mb => ∃ (lmb : List (BitVec 8)) (tmpb : List (BitVec 32)),
                    lmb.length = 2 * c.max_vars ∧ tmpb.length = c.max_vars ∧
                    noff.toNat ≤ pn.toNat ∧ pn.toNat ≤ (noff + nwsz).toNat ∧
                    mcnt.toNat ≤ sv2.core.cur_vars ∧
                    DenseWatchSliceOk F_cur sv2.core nlit.toNat pn.toNat
                      ((noff + nwsz).toNat - pn.toNat) ∧
                    (∀ q < 2 * c.max_vars, lmb[q]?.getD 0#8 ≠ 0#8 →
                      v.toNat < q / 2 ∧
                      inSliceBins sv2.core.wstk off.toNat (off + wsz).toNat
                        (2 * sv2.core.cur_vars) q ∧
                      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, q])) ∧
                    (∀ i < mcnt.toNat, (tmpb[i]?.getD 0#32).toNat < 2 * sv2.core.cur_vars ∧
                      LitEquiv (cnfOfClauses F_cur) lit.toNat (tmpb[i]?.getD 0#32).toNat) ∧
                    (FullMem c { sv2 with core :=
                      { sv2.core with lit_mark := lmb, tmp := tmpb } } ⋆ R) mb)
                  (fun (pn, _, ()) _ => (noff + nwsz).toNat - pn.toNat)
                  (fun Jb hJb => by
                    c0_hsteps!
                    exact hJb (noff, 0#64, ()) ma ⟨lma, sv2.core.tmp, hlma_l, htmpl,
                      Nat.le_refl _, by omega, Nat.zero_le _,
                      (by rwa [hnend_n, Nat.add_sub_cancel_left]), hlma_in,
                      (fun _ h => by cases h), hma⟩)
                  (fun Jb (pn, mcnt, ()) mb
                    ⟨lmb, tmpb, hlmb_l, htmpb_l, hpn_lo, hpn_hi, hmc_le, hsn, hlmb_in, htmp_ok,
                     hmb⟩ ihb => ?_)
                m6_split_fast
                · have hpn_lt : pn.toNat < (noff + nwsz).toNat := by
                    simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                  clear hc
                  obtain ⟨w0, hw0_get, hpop⟩ := dense_slice_pop_step hsn (by omega)
                  have hpn_w : pn.toNat < sv2.core.wstk.length := by omega
                  have hw0_eq : sv2.core.wstk[pn.toNat]'hpn_w = w0 := by
                    rw [List.getElem?_eq_getElem hpn_w] at hw0_get; exact Option.some.inj hw0_get
                  subst w0
                  rcases hpop with ⟨hbf, hent_wn, hsn_next⟩ | ⟨hbf, hrem2, hsn_next⟩
                  · have hpn1_n : (pn + 1#64).toNat = pn.toNat + 1 := by
                      rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
                        Nat.mod_eq_of_lt (by omega)]
                    m6_split_fast
                    · exfalso; exact hbf (beq_iff_eq.mp hc)
                    · clear hc; m6_split_fast
                      · have hot_lt :
                            ((sv2.core.wstk[pn.toNat]'hpn_w) &&& 0x7FFFFFFF#32).toNat <
                              2 * sv2.core.cur_vars := by
                          rw [hcv2]; simp only [BitVec.ult, decide_eq_true_eq,
                            bv_zext32_toNat] at hc
                          rwa [hnl_eq] at hc
                        have hot_x :
                            (BitVec.setWidth 64
                              (((sv2.core.wstk[pn.toNat]'hpn_w) &&& 0x7FFFFFFF#32) ^^^
                                1#32)).toNat < lmb.length := by
                          rw [bv_zext32_toNat, hlmb_l, bv32_xor1_eq_litNeg]
                          exact Nat.lt_of_lt_of_le (litNeg_lt_two_mul hot_lt) (by omega)
                        clear hc; m6_split_fast
                        · clear hc; m6_split_fast
                          · let ot := (sv2.core.wstk[pn.toNat]'hpn_w) &&& 0x7FFFFFFF#32
                            have hot_x' : (ot ^^^ 1#32).toNat < lmb.length := by
                              rw [bv_zext32_toNat] at hot_x; exact hot_x
                            have heq1 : lmb[(ot ^^^ 1#32).toNat]?.getD 0#8 = 1#8 := by
                              have h1 : (BitVec.setWidth 32
                                  (({ sv2 with core :=
                                    { sv2.core with lit_mark := lmb, tmp := tmpb } } :
                                    FullState).core.lit_mark[(BitVec.setWidth 64
                                      (ot ^^^ 1#32)).toNat]'(by
                                    dsimp only; rw [bv_zext32_toNat]; exact hot_x'))) = 1#32 :=
                                beq_iff_eq.mp hc
                              dsimp only at h1
                              have hzx : (BitVec.setWidth 64 (ot ^^^ 1#32)).toNat =
                                  (ot ^^^ 1#32).toNat := bv_zext32_toNat _
                              have h1' : (lmb[(ot ^^^ 1#32).toNat]'hot_x').setWidth 32 = 1#32 := by
                                rw [← list_getElem_congr hzx (by rw [hzx]; exact hot_x') hot_x']
                                exact h1
                              have hto := congrArg BitVec.toNat h1'
                              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans
                                (BitVec.isLt _) (by decide))] at hto
                              rw [List.getElem?_eq_getElem hot_x', Option.getD_some]
                              exact BitVec.eq_of_toNat_eq hto
                            have hnz_neg : lmb[(ot ^^^ 1#32).toNat]?.getD 0#8 ≠ 0#8 := by
                              rw [heq1]; decide
                            have hlm_x3 :
                                (BitVec.setWidth 64 (ot ^^^ 1#32)).toNat <
                                  ({ sv2 with core :=
                                    { sv2.core with lit_mark := lmb, tmp := tmpb } } :
                                    FullState).core.lit_mark.length := by
                              dsimp only; rw [bv_zext32_toNat]; exact hot_x'
                            have hlt_x : (ot ^^^ 1#32).toNat < 2 * c.max_vars :=
                              hlmb_l ▸ hot_x'
                            have hent_pos := (hlmb_in (ot ^^^ 1#32).toNat hlt_x hnz_neg).2.2
                            rw [BitVec.toNat_xor] at hent_pos
                            have hlit_xor : lit.toNat ^^^ 1 = nlit.toNat := by
                              dsimp only [nlit]; rw [BitVec.toNat_xor]; rfl
                            have hent_wn' : (cnfOfClauses F_cur).EntailsClause
                                (cnfClause [lit.toNat ^^^ 1, ot.toNat]) := by
                              rwa [hlit_xor]
                            have heqv_ot := litEquiv_of_clauses hent_wn' hent_pos
                            have hlmb_new : ∀ q < 2 * c.max_vars,
                                (lmb.set (ot ^^^ 1#32).toNat 3#8)[q]?.getD 0#8 ≠ 0#8 →
                                v.toNat < q / 2 ∧
                                inSliceBins sv2.core.wstk off.toNat (off + wsz).toNat
                                  (2 * sv2.core.cur_vars) q ∧
                                (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, q]) := by
                              intro q hq hnz
                              by_cases hqe : q = (ot ^^^ 1#32).toNat
                              · subst hqe; exact hlmb_in _ hq hnz_neg
                              · rw [List.getElem?_set_ne (Ne.symm hqe)] at hnz
                                exact hlmb_in q hq hnz
                            clear hc; m6_split_fast
                            · have hm_lt : mcnt.toNat < sv2.core.cur_vars := by
                                rw [hcv2]; simp only [BitVec.ult, decide_eq_true_eq,
                                  BitVec.toNat_ofNat,
                                  Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
                                exact hc
                              have hmc1_n : (mcnt + 1#64).toNat = mcnt.toNat + 1 :=
                                bv64_add1_lt_of (by omega)
                              have hm_tmp : mcnt.toNat <
                                  ({ sv2 with core :=
                                    { sv2.core with lit_mark := lmb, tmp := tmpb } } :
                                    FullState).core.tmp.length := by
                                dsimp only; omega
                              c0_hsteps!
                              refine ihb (pn + 1#64, mcnt + 1#64, ()) m (by dsimp only; omega)
                                ⟨lmb.set (ot ^^^ 1#32).toNat 3#8, tmpb.set mcnt.toNat ot,
                                 by rw [List.length_set]; exact hlmb_l,
                                 by rw [List.length_set]; exact htmpb_l,
                                 by omega, by omega, by omega,
                                 by rwa [hpn1_n], hlmb_new, fun i hi => ?_, hm⟩
                              by_cases hie : i = mcnt.toNat
                              · subst hie
                                rw [List.getElem?_set_self (by dsimp only at hm_tmp; omega),
                                  Option.getD_some]
                                exact ⟨hot_lt, heqv_ot⟩
                              · rw [List.getElem?_set_ne (Ne.symm hie)]
                                exact htmp_ok i (by omega)
                            · clear hc; c0_hsteps!
                              exact ihb (pn + 1#64, mcnt, ()) m (by dsimp only; omega)
                                ⟨lmb.set (ot ^^^ 1#32).toNat 3#8, tmpb,
                                 by rw [List.length_set]; exact hlmb_l, htmpb_l,
                                 by omega, by omega, hmc_le,
                                 by rwa [hpn1_n], hlmb_new, htmp_ok, hm⟩
                          · clear hc; c0_hsteps!
                            exact ihb (pn + 1#64, mcnt, ()) mb (by dsimp only; omega)
                              ⟨lmb, tmpb, hlmb_l, htmpb_l, by omega, by omega, hmc_le,
                               by rwa [hpn1_n], hlmb_in, htmp_ok, hmb⟩
                        · clear hc; c0_hsteps!
                          exact ihb (pn + 1#64, mcnt, ()) mb (by dsimp only; omega)
                            ⟨lmb, tmpb, hlmb_l, htmpb_l, by omega, by omega, hmc_le,
                             by rwa [hpn1_n], hlmb_in, htmp_ok, hmb⟩
                      · clear hc; c0_hsteps!
                        exact ihb (pn + 1#64, mcnt, ()) mb (by dsimp only; omega)
                          ⟨lmb, tmpb, hlmb_l, htmpb_l, by omega, by omega, hmc_le,
                           by rwa [hpn1_n], hlmb_in, htmp_ok, hmb⟩
                  · have hpn2_n : (pn + 2#64).toNat = pn.toNat + 2 := by
                      rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl,
                        Nat.mod_eq_of_lt (by omega)]
                    m6_split_fast
                    · clear hc; c0_hsteps!
                      exact ihb (pn + 2#64, mcnt, ()) mb (by dsimp only; omega)
                        ⟨lmb, tmpb, hlmb_l, htmpb_l, by omega, by omega, hmc_le,
                         by rwa [hpn2_n], hlmb_in, htmp_ok, hmb⟩
                    · exfalso; exact (beq_eq_false_iff_ne.mp hc) hbf
                · clear hc; c0_hsteps_nogrp
                  refine wp_loop_inv (ts := [i64])
                    (fun (pc, ()) mc => ∃ lmc : List (BitVec 8),
                      lmc.length = 2 * c.max_vars ∧ off.toNat ≤ pc.toNat ∧
                      pc.toNat ≤ (off + wsz).toNat ∧
                      DenseWatchSliceOk F_cur sv2.core lit.toNat pc.toNat
                        ((off + wsz).toNat - pc.toNat) ∧
                      (∀ q < 2 * c.max_vars, lmc[q]?.getD 0#8 ≠ 0#8 →
                        v.toNat < q / 2 ∧
                        inSliceBins sv2.core.wstk pc.toNat (off + wsz).toNat
                          (2 * sv2.core.cur_vars) q) ∧
                      (FullMem c { sv2 with core :=
                        { sv2.core with lit_mark := lmc, tmp := tmpb } } ⋆ R) mc)
                    (fun (pc, ()) _ => (off + wsz).toNat - pc.toNat)
                    (fun Jc hJc => by
                      c0_hsteps!
                      exact hJc (off, ()) mb ⟨lmb, hlmb_l, Nat.le_refl _, by omega,
                        (by rwa [hend_n, Nat.add_sub_cancel_left]),
                        fun q hq hnz => ⟨(hlmb_in q hq hnz).1, (hlmb_in q hq hnz).2.1⟩, hmb⟩)
                    (fun Jc (pc, ()) mc ⟨lmc, hlmc_l, hpc_lo, hpc_hi, hsc, hlmc_in, hmc⟩ ihc => ?_)
                  m6_split_fast
                  · have hpc_lt : pc.toNat < (off + wsz).toNat := by
                      simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                    clear hc
                    obtain ⟨w0, hw0_get, hpop⟩ := dense_slice_pop_step hsc (by omega)
                    have hpc_w : pc.toNat < sv2.core.wstk.length := by omega
                    have hw0_eq : sv2.core.wstk[pc.toNat]'hpc_w = w0 := by
                      rw [List.getElem?_eq_getElem hpc_w] at hw0_get; exact Option.some.inj hw0_get
                    subst w0
                    rcases hpop with ⟨hbf, _, hsc_next⟩ | ⟨hbf, _, hsc_next⟩
                    · have hpc1_n : (pc + 1#64).toNat = pc.toNat + 1 :=
                        bv64_add1_lt_of (by omega)
                      m6_split_fast
                      · exfalso; exact hbf (beq_iff_eq.mp hc)
                      · clear hc; m6_split_fast
                        · have hot_lt :
                              ((sv2.core.wstk[pc.toNat]'hpc_w) &&& 0x7FFFFFFF#32).toNat <
                                2 * sv2.core.cur_vars := by
                            rw [hcv2]; simp only [BitVec.ult, decide_eq_true_eq,
                              bv_zext32_toNat] at hc
                            rwa [hnl_eq] at hc
                          clear hc; m6_split_fast
                          · have hot_gt : v.toNat <
                                ((sv2.core.wstk[pc.toNat]'hpc_w) &&&
                                  0x7FFFFFFF#32).toNat / 2 := by
                              simp only [BitVec.ult, decide_eq_true_eq, bv_zext32_toNat,
                                BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hc
                              simpa using hc
                            have hot_lm :
                                (BitVec.setWidth 64
                                  ((sv2.core.wstk[pc.toNat]'hpc_w) &&& 0x7FFFFFFF#32)).toNat <
                                  ({ sv2 with core :=
                                    { sv2.core with lit_mark := lmc, tmp := tmpb } } :
                                    FullState).core.lit_mark.length := by
                              dsimp only; rw [bv_zext32_toNat]; omega
                            c0_hsteps!
                            refine ihc (pc + 1#64, ()) m (by dsimp only; omega)
                              ⟨lmc.set ((sv2.core.wstk[pc.toNat]'hpc_w) &&& 0x7FFFFFFF#32).toNat
                                  0#8,
                               by rw [List.length_set]; exact hlmc_l,
                               by omega, by omega, by rwa [hpc1_n],
                               fun q hq hnz => ?_, hm⟩
                            by_cases hqe :
                                q = ((sv2.core.wstk[pc.toNat]'hpc_w) &&& 0x7FFFFFFF#32).toNat
                            · subst hqe
                              rw [List.getElem?_set_self (by
                                dsimp only at hot_lm; rw [bv_zext32_toNat] at hot_lm; omega),
                                Option.getD_some] at hnz
                              exact absurd rfl hnz
                            · rw [List.getElem?_set_ne (Ne.symm hqe)] at hnz
                              have hprev := hlmc_in q hq hnz
                              exact ⟨hprev.1, by
                                rw [hpc1_n]
                                exact inSliceBins_clear_bin hpc_lt hw0_get hbf hqe hprev.2⟩
                          · have hle_v :
                                ((sv2.core.wstk[pc.toNat]'hpc_w) &&& 0x7FFFFFFF#32).toNat / 2 ≤
                                  v.toNat := by
                              have hlt_hc : ¬ (v.toNat <
                                  ((sv2.core.wstk[pc.toNat]'hpc_w) &&&
                                    0x7FFFFFFF#32).toNat / 2) := by
                                simp only [BitVec.ult, decide_eq_false_iff_not, bv_zext32_toNat,
                                  BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                  Nat.pow_one] at hc
                                rwa [show (0x7FFFFFFF#32 : BitVec 32) = 2147483647 from rfl]
                              omega
                            clear hc; c0_hsteps!
                            refine ihc (pc + 1#64, ()) mc (by dsimp only; omega)
                              ⟨lmc, hlmc_l, by omega, by omega, by rwa [hpc1_n],
                               fun q hq hnz => ?_, hmc⟩
                            have hprev := hlmc_in q hq hnz
                            refine ⟨hprev.1, by
                              rw [hpc1_n]
                              exact inSliceBins_clear_bin hpc_lt hw0_get hbf (by omega) hprev.2⟩
                        · have hge_ot :
                              2 * sv2.core.cur_vars ≤
                                ((sv2.core.wstk[pc.toNat]'hpc_w) &&& 0x7FFFFFFF#32).toNat := by
                            rw [hcv2]; simp only [BitVec.ult, decide_eq_false_iff_not,
                              bv_zext32_toNat, hnl_eq] at hc
                            exact Nat.not_lt.mp hc
                          clear hc; c0_hsteps!
                          refine ihc (pc + 1#64, ()) mc (by dsimp only; omega)
                            ⟨lmc, hlmc_l, by omega, by omega, by rwa [hpc1_n],
                             fun q hq hnz => ?_, hmc⟩
                          have hprev := hlmc_in q hq hnz
                          refine ⟨hprev.1, by
                            rw [hpc1_n]
                            exact inSliceBins_clear_bin_of_ge hpc_lt hw0_get hbf hge_ot hprev.2⟩
                    · have hpc2_n : (pc + 2#64).toNat = pc.toNat + 2 :=
                        bv64_add2_lt_of (by omega)
                      m6_split_fast
                      · clear hc; c0_hsteps!
                        exact ihc (pc + 2#64, ()) mc (by dsimp only; omega)
                          ⟨lmc, hlmc_l, by omega, by omega, by rwa [hpc2_n], fun q hq hnz => by
                            have hprev := hlmc_in q hq hnz
                            exact ⟨hprev.1, by
                              rw [hpc2_n]; exact inSliceBins_clear_occ hpc_lt hw0_get hbf hprev.2⟩,
                           hmc⟩
                      · exfalso; exact (beq_eq_false_iff_ne.mp hc) hbf
                  · have hpc_e : (off + wsz).toNat ≤ pc.toNat := by
                      simp only [BitVec.ult, decide_eq_false_iff_not] at hc; exact Nat.not_lt.mp hc
                    have hclr_mc : ∀ q < 2 * c.max_vars, lmc[q]?.getD 0#8 = 0#8 := fun q hq =>
                      Classical.byContradiction fun hnz =>
                        (inSliceBins_false_of_ge hpc_e).mp (hlmc_in q hq hnz).2
                    let s_clr : FullState :=
                      { sv2 with core := { sv2.core with lit_mark := lmc, tmp := tmpb } }
                    have hwt_clr : FullWitnessInv c F0 F_cur s_clr.core :=
                      { hdv2.2.1 with
                        arena := { hdv2.2.1.arena with len_ok := hdv2.2.1.arena.len_ok }
                        watches := hdv2.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
                    have hd_clr : FullDenseInvW c F0 F_cur s_clr :=
                      ⟨⟨{ hdv2.1.core_ok with tmp_len_arr := htmpb_l, lit_mark_len := hlmc_l },
                        hdv2.1.scratch_ok⟩, hwt_clr, ⟨hdv2.2.2.1.1, hclr_mc⟩,
                       fullArenaVarsNodup_of_eq hdv2.2.2.2.1 rfl rfl,
                       fullExtScratchOk_of_eq hdv2.2.2.2.2.1 rfl rfl rfl rfl,
                       hdv2.2.2.2.2.2.1, hdv2.2.2.2.2.2.2⟩
                    have hrepr_clr : FullCongReprInv F_cur (2 * s_clr.core.cur_vars)
                        s_clr.core.repr := hrepr2
                    clear hc; c0_hsteps_nogrp
                    refine wp_loop_inv (ts := [i64])
                      (fun (k, ()) mk => ∃ sk : FullState,
                        FullDenseInvW c F0 F_cur sk ∧ sk.core.cur_vars = s.core.cur_vars ∧
                        sk.core.fuel = s.core.fuel ∧
                        FullCongReprInv F_cur (2 * sk.core.cur_vars) sk.core.repr ∧
                        sk.core.tmp = tmpb ∧ k.toNat ≤ mcnt.toNat ∧ (FullMem c sk ⋆ R) mk)
                      (fun (k, ()) _ => mcnt.toNat - k.toNat)
                      (fun Jk hJk => by
                        c0_hsteps!; exact hJk (0#64, ()) mc
                          ⟨s_clr, hd_clr, hcv2, hfl2, hrepr_clr, rfl, Nat.zero_le _, hmc⟩)
                      (fun Jk (k, ()) mk
                        ⟨sk, hdk, hcv_k, hfl_k, hrepr_k, htmp_k, hk_le, hmk⟩ ihk => ?_)
                    m6_split_fast
                    · have hk_lt : k.toNat < mcnt.toNat := by
                        simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                      clear hc; m6_split_fast
                      · have hinc_k : sk.core.inconsistent = 0#64 := beq_iff_eq.mp hc
                        clear hc
                        have hk1_n : (k + 1#64).toNat = k.toNat + 1 :=
                          bv64_add1_lt_of (by omega)
                        have hk_tmp : k.toNat < sk.core.tmp.length := by
                          rw [htmp_k, htmpb_l]; omega
                        have hot_ok := htmp_ok k.toNat hk_lt
                        rw [← htmp_k, List.getElem?_eq_getElem hk_tmp, Option.getD_some] at hot_ok
                        c0_hsteps!; m3_call hEquivFold
                        refine ⟨c, F0, F_cur, sk, R, rfl, hdk.1, hdk.2.1, hdk.2.2.1, hdk.2.2.2.1,
                          hdk.2.2.2.2.1, hdk.2.2.2.2.2.1, hdk.2.2.2.2.2.2, hrepr_k,
                          (by rw [hcv_k, ← hcv2]; exact hlit_lt),
                          (by rw [hcv_k, ← hcv2]; exact hot_ok.1), hot_ok.2, hmk,
                          fun r sf mf hlen_f hw_f hmk_f hnd_f hext_f hcl_f hdm_f hcv_f hfl_f _ _
                            htmp_f _ hrepr_f _ h2u hmf => ?_⟩
                        have hdf : FullDenseInvW c F0 F_cur sf :=
                          ⟨hlen_f, hw_f, hmk_f, hnd_f, hext_f, hcl_f, hdm_f⟩
                        m6_split_fast
                        · c0_hsteps!
                          exact hQ 20#64 sf mf hdf (hcv_f.trans hcv_k) (hfl_f.trans hfl_k)
                            hrepr_f (Or.inr rfl) (fun _ => h2u (beq_iff_eq.mp hc)) hmf
                        · c0_hsteps!
                          exact ihk (k + 1#64, ()) mf (by dsimp only; omega)
                            ⟨sf, hdf, hcv_f.trans hcv_k, hfl_f.trans hfl_k, hrepr_f,
                             htmp_f.trans htmp_k, by omega, hmf⟩
                      · clear hc; c0_hsteps!
                        exact ihv2 (v + 1#64, ()) mk (by dsimp only; omega)
                          ⟨sk, hdk, hcv_k, hfl_k, hrepr_k, by omega, hmk⟩
                    · clear hc; c0_hsteps!
                      exact ihv2 (v + 1#64, ()) mk (by dsimp only; omega)
                        ⟨sk, hdk, hcv_k, hfl_k, hrepr_k, by omega, hmk⟩
              · have hclr_ma : ∀ q < 2 * c.max_vars, lma[q]?.getD 0#8 = 0#8 :=
                  hany_f (by cases hc; rfl)
                let s_clr : FullState := { sv2 with core := { sv2.core with lit_mark := lma } }
                have hd_clr : FullDenseInvW c F0 F_cur s_clr :=
                  fullDenseInvW_with_lm_clear hdv2 hlma_l hclr_ma
                c0_hsteps!
                exact ihv2 (v + 1#64, ()) ma (by dsimp only; omega)
                  ⟨s_clr, hd_clr, hcv2, hfl2, hrepr2, by omega, hma⟩
      · have hinc2_ne : sv2.core.inconsistent ≠ 0#64 := fun h => by rw [h] at hc; simp at hc
        have huns2 := FullM3CongBva.unsat_of_inconsistent_w hdv2.2.1 hinc2_ne
        clear hc; m6_split_fast
        · c0_hsteps!; exact hQ 20#64 sv2 mv hdv2 hcv2 hfl2 hrepr2 (Or.inr rfl) (fun _ => huns2) hmv2
        · exfalso; exact hinc2_ne (bne_eq_false_iff_eq.mp hc)
    · clear hc; m6_split_fast
      · have huns2 := FullM3CongBva.unsat_of_inconsistent_w hdv2.2.1 (bne_iff_ne.mp hc)
        c0_hsteps!; exact hQ 20#64 sv2 mv hdv2 hcv2 hfl2 hrepr2 (Or.inr rfl) (fun _ => huns2) hmv2
      · c0_hsteps!
        exact hQ 1#64 sv2 mv hdv2 hcv2 hfl2 hrepr2 (Or.inl rfl) (fun h => by cases h) hmv2

/-! ## 6. `full_cong_extract_wp` (`m6CongExtractSpec`) -/

private theorem nat_xor1_mod2 (n : Nat) : (n ^^^ 1) % 2 = (n % 2) ^^^ 1 := by
  rw [← Nat.and_one_is_mod, ← Nat.and_one_is_mod]
  apply Nat.eq_of_testBit_eq; intro k; cases k with
  | zero => simp
  | succ k =>
    have hlt : (n % 2 ^^^ 1) < 2 := by
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]
    simp [Nat.testBit_succ, Nat.div_eq_of_lt hlt]

private theorem bv32_bit1_ne0_mod2 {l neg_p : BitVec 32} :
    ((if (l &&& 1#32) != 0#32 then neg_p ^^^ 1#32 else neg_p) &&& 1#32).toNat =
      (neg_p &&& 1#32).toNat ^^^ (l.toNat % 2) := by
  have hl1 : (l &&& 1#32).toNat = l.toNat % 2 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl]
    exact Nat.and_one_is_mod l.toNat
  rcases Nat.mod_two_eq_zero_or_one l.toNat with hm | hm
  · have hb : (l &&& 1#32) = 0#32 := BitVec.eq_of_toNat_eq (by rw [hl1, hm]; rfl)
    simp [hb, hm]
  · have hb : (l &&& 1#32) = 1#32 := BitVec.eq_of_toNat_eq (by rw [hl1, hm]; rfl)
    have hne1 : ((1#32 : BitVec 32) != 0#32) = true := rfl
    simp only [hb, hne1, ↓reduceIte]
    rw [BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_xor,
      show (1#32 : BitVec 32).toNat = 1 from rfl]
    rw [Nat.and_one_is_mod, Nat.and_one_is_mod, hm, nat_xor1_mod2]

theorem full_cong_extract_wp (Γ : Env)
    (hNext : ∀ args m Q X, FullCongSpecs.fullArenaNextSpec args m Q X →
      Γ "full_arena_next" [i64, i32] [i32] args m Q X)
    (hHasBin : ∀ args m Q X, FullCongSpecs.fullHasBinSpec args m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] args m Q X)
    (hCountBins : ∀ args m Q X, m6CongCountBinsSpec args m Q X →
      Γ "full_cong_count_bins" [i64] [] args m Q X)
    (hTryXorIte : ∀ args m Q X, m6CongTryXorIteSpec args m Q X →
      Γ "full_cong_try_xor_ite" [i64, i32, i32, i32, i64, i64] [i64] args m Q X)
    (hExtractXorK : ∀ args m Q X, m6CongExtractXorKSpec args m Q X →
      Γ "full_cong_extract_xor_k" [i64, i32, i32, i64, i64] [i64] args m Q X) :
    ∀ args m Q X, m6CongExtractSpec args m Q X →
      Func.wp Γ full_cong_extract_body args m Q X := by
  rintro ⟨h, g_cap, tick_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hd, hg_cap, hm0, hQ⟩
  have hmx := c.hmaxv; have hac := c.harena; have hsc := c.hscr
  unfold dimacsBound at hmx hac hsc
  c0_hsteps!; m3_call hCountBins
  refine ⟨c, s, R, rfl, hd.1, fullWatchBounds_of_dense hd, hm0, fun ws1' m1 hws1_l hm1 => ?_⟩
  let s1 : FullState := { s with scratch := { s.scratch with work_stk1 := ws1' } }
  have hd1 : FullDenseInvW c F0 F_cur s1 := fullDenseInvW_with_ws1 hd hws1_l
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i64, i64, i64])
    (fun (p, g_len, ticks, ()) mp => ∃ sp : FullState,
      FullDenseInvW c F0 F_cur sp ∧ sp.core.cur_vars = s.core.cur_vars ∧
      sp.core.fuel = s.core.fuel ∧ sp.core.repr = s.core.repr ∧
      sp.core.inconsistent = s.core.inconsistent ∧ sp.core.arena = s1.core.arena ∧
      sp.core.arena_len = s1.core.arena_len ∧ p.toNat ≤ s1.core.arena_len ∧
      (p.toNat = s1.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefsCore s1.core) ∧
      g_len.toNat ≤ g_cap.toNat ∧
      M6GateSeqOk F_cur s.core.cur_vars sp.scratch.scratch_buf g_len.toNat 0 ∧
      (FullMem c sp ⋆ R) mp)
    (fun (p, _, _, ()) _ => s1.core.arena_len - p.toNat)
    (fun J hJ => by
      c0_hsteps!
      have hmem0 : (0#64 : BitVec 64).toNat = s1.core.arena_len ∨
          (0#64 : BitVec 64).toNat ∈ fullArenaClauseRefsCore s1.core := by
        rcases Nat.eq_zero_or_pos s1.core.arena_len with hz | hpos
        · exact Or.inl hz.symm
        · exact Or.inr (fullArenaClauseRefs_zero_mem hd1.2.1 hpos)
      exact hJ (0#64, 0#64, 0#64, ()) m1 ⟨s1, hd1, rfl, rfl, rfl, rfl, rfl, rfl, Nat.zero_le _,
        hmem0, Nat.zero_le _, .done, hm1⟩)
    (fun J (p, g_len, ticks, ()) mp
      ⟨sp, hdp, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, hp_le, hp_mem, hgl_le, hseq_p,
       hmp⟩ ihp => ?_)
  have hq_done : Q (g_len, ()) mp :=
    hQ g_len sp mp hdp hcv_p hfl_p hrep_p hinc_p hgl_le hseq_p hmp
  have hlen_p := hdp.1
  have harl_p := hlen_p.core_ok.arena_len_arr; have hale_p := hlen_p.core_ok.arena_len_le
  have hcv_ple := hlen_p.core_ok.cur_vars_le; have hvals_pl := hlen_p.core_ok.vals_len
  have hws1_pl := hlen_p.scratch_ok.work_stk1_len; have hws2_pl := hlen_p.scratch_ok.work_stk2_len
  have hscrl_p := hlen_p.scratch_ok.scratch_buf_len
  m6_split_fast
  · have hp_lt : p.toNat < sp.core.arena_len := by
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat] at hc
      rw [Nat.mod_eq_of_lt (by omega)] at hc
      exact hc
    clear hc; m6_split_fast
    · have hgl34_le : g_len.toNat + 34 ≤ g_cap.toNat := by
        simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
      clear hc; m6_split_fast
      · clear hc
        have hp_ref : p.toNat ∈ fullArenaClauseRefsCore sp.core := by
          have hmem := hp_mem.resolve_left (by omega)
          unfold fullArenaClauseRefsCore; rw [har_p, hal_p]; exact hmem
        have hp_wf := hdp.2.1.arena.refs_wf p.toNat hp_ref
        have hp_arr : p.toNat < sp.core.arena.length := by omega
        have hp2_n : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
        have hp2_arr : (p + 2#64).toNat < sp.core.arena.length := by omega
        c0_hsteps!; m3_call hNext
        refine ⟨c, sp, R, rfl, hlen_p, hmp, ?_⟩
        have hp_tr : (p.setWidth 32).toNat = p.toNat := by
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
        have hnp_bd := fullArenaNextOff_bounds (ar := sp.core.arena) (alen := sp.core.arena_len)
          (cref := p.toNat) hp_wf.1
        let np_bv := (BitVec.ofNat 32 (fullArenaNextOff sp.core.arena sp.core.arena_len
          (p.setWidth 32).toNat)).setWidth 64
        have hnp_n : np_bv.toNat = fullArenaNextOff sp.core.arena sp.core.arena_len p.toNat := by
          dsimp only [np_bv]; rw [hp_tr, bv_zext32_toNat, bv32_ofNat_toNat (by omega)]
        have hnp_le : np_bv.toNat ≤ s1.core.arena_len := by
          rw [hnp_n, ← hal_p]; exact hnp_bd.2
        have hnp_mem : np_bv.toNat = s1.core.arena_len ∨
            np_bv.toNat ∈ fullArenaClauseRefsCore s1.core := by
          rw [hnp_n]
          rw [show fullArenaNextOff sp.core.arena sp.core.arena_len p.toNat =
            fullArenaNextOff s1.core.arena s1.core.arena_len p.toNat by rw [har_p, hal_p]]
          exact fullArenaClauseRefs_next_or_end hd1.2.1 (hp_mem.resolve_left (by omega))
        have hnp_gt : p.toNat < np_bv.toNat := by
          rw [hnp_n]; have := hp_wf.2.1; have := hp_wf.2.2.1; omega
        c0_hsteps_nogrp; refine wp_join_group (ts := [i64, i64])
          (fun (gl', tk', ()) mj => ∃ sj : FullState,
            FullDenseInvW c F0 F_cur sj ∧ sj.core.cur_vars = s.core.cur_vars ∧
            sj.core.fuel = s.core.fuel ∧ sj.core.repr = s.core.repr ∧
            sj.core.inconsistent = s.core.inconsistent ∧ sj.core.arena = s1.core.arena ∧
            sj.core.arena_len = s1.core.arena_len ∧ gl'.toNat ≤ g_cap.toNat ∧
            M6GateSeqOk F_cur s.core.cur_vars sj.scratch.scratch_buf gl'.toNat 0 ∧
            (FullMem c sj ⋆ R) mj)
          (fun _ ⟨gl', tk', ⟨⟩⟩ mj
            ⟨sj, hdj, hcv_j, hfl_j, hrep_j, hinc_j, har_j, hal_j, hgl_j, hseq_j, hmj⟩ => by
            m3_let
            exact ihp (np_bv, gl', tk', ()) mj (by dsimp only; omega)
              ⟨sj, hdj, hcv_j, hfl_j, hrep_j, hinc_j, har_j, hal_j, by omega, hnp_mem, hgl_j,
               hseq_j, hmj⟩)
          ?_
        intro Jnext hJnext
        have hjnext_same : Jnext (g_len, ticks + 1#64, ()) mp :=
          hJnext (g_len, ticks + 1#64, ()) mp
            ⟨sp, hdp, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, hgl_le, hseq_p, hmp⟩
        m6_split_fast
        · have hng_red := beq_iff_eq.mp hc; clear hc
          have hng : fullArenaClauseGarb sp p.toNat = false := by
            unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
            rw [List.getElem?_eq_getElem hp_arr, Option.getD_some]
            exact garb_false_of_and_480000 hng_red
          m6_split_fast
          · clear hc; m6_split_fast
            · have hsz_p2 : sp.core.arena[(p + 2#64).toNat]'hp2_arr =
                  sp.core.arena[p.toNat + 2]'(by omega) :=
                list_getElem_congr hp2_n hp2_arr (by omega)
              have hsz_eq : fullArenaClauseSizeCore sp.core p.toNat =
                  (sp.core.arena[(p + 2#64).toNat]'hp2_arr).toNat := by
                unfold fullArenaClauseSizeCore
                rw [hsz_p2, List.getElem?_eq_getElem (by omega), Option.getD_some]
              have hsz3 : 3 ≤ (sp.core.arena[(p + 2#64).toNat]'hp2_arr).toNat := by
                rw [← hsz_eq]; exact hp_wf.2.1
              have hsz32 : (sp.core.arena[(p + 2#64).toNat]'hp2_arr).toNat ≤ 32 := by
                simp only [BitVec.ule, decide_eq_true_eq] at hc; exact hc
              clear hc
              let sz_bv := sp.core.arena[(p + 2#64).toNat]'hp2_arr
              have hbd_sz : p.toNat + 3 + sz_bv.toNat ≤ sp.core.arena.length := by
                have h1 := hp_wf.2.2.1; have h2 := hp_wf.2.2.2.1
                have hsz_d : fullArenaClauseSizeCore sp.core p.toNat = sz_bv.toNat := hsz_eq
                omega
              c0_hsteps_nogrp
              refine wp_loop_break_group
                (brkTs := [i32, i32, i32, .bool, i32]) (lpTs := [i32, i32, i32, i32])
                (fun (usz, _, neg_p, sat, _, ()) mb => ∃ ws2 : List (BitVec 32),
                  ws2.length = 2 * c.max_vars ∧
                  (sat = false →
                    3 ≤ sz_bv.toNat ∧
                    usz.toNat ≤ sz_bv.toNat ∧ usz.toNat ≤ sp.core.cur_vars ∧
                    (∀ j < usz.toNat, (ws2[j]?.getD 0#32).toNat < 2 * sp.core.cur_vars) ∧
                    ((neg_p &&& 1#32).toNat = (List.range usz.toNat).foldl
                      (fun acc i => acc ^^^ ((ws2[i]?.getD 0#32).toNat % 2)) 0) ∧
                    (∃ idxs : List Nat, idxs.length = usz.toNat ∧ idxs.Nodup ∧
                      (∀ q ∈ idxs, q < sz_bv.toNat) ∧
                      (∀ j < usz.toNat,
                        idxs[j]? = some (idxs[j]?.getD 0) →
                        ws2[j]? = sp.core.arena[p.toNat + 3 + (idxs[j]?.getD 0)]?) ∧
                      (∀ q < sz_bv.toNat, q ∈ idxs ∨
                        sp.core.vals[(sp.core.arena[p.toNat + 3 + q]?.getD 0#32).toNat]?.getD 0#8 =
                          0xFF#8)) ∧
                    (∀ j < usz.toNat, ∀ j2 < usz.toNat, j ≠ j2 →
                      (ws2[j]?.getD 0#32).toNat / 2 ≠ (ws2[j2]?.getD 0#32).toNat / 2) ∧
                    (cnfOfClauses F_cur).EntailsClause (cnfClause
                      ((List.range usz.toNat).map fun j => (ws2[j]?.getD 0#32).toNat))) ∧
                  (FullMem c { sp with scratch := { sp.scratch with work_stk2 := ws2 } } ⋆ R) mb)
                (fun rem (usz, max_nbc, neg_p, k, ()) mk => ∃ ws2 : List (BitVec 32),
                  ws2.length = 2 * c.max_vars ∧ k.toNat ≤ sz_bv.toNat ∧
                  rem = sz_bv.toNat - k.toNat ∧
                  usz.toNat ≤ k.toNat ∧ usz.toNat ≤ sp.core.cur_vars ∧
                  (∀ j < usz.toNat, (ws2[j]?.getD 0#32).toNat < 2 * sp.core.cur_vars) ∧
                  ((neg_p &&& 1#32).toNat = (List.range usz.toNat).foldl
                    (fun acc i => acc ^^^ ((ws2[i]?.getD 0#32).toNat % 2)) 0) ∧
                  (∃ idxs : List Nat, idxs.length = usz.toNat ∧ idxs.Nodup ∧
                    (∀ q ∈ idxs, q < k.toNat) ∧
                    (∀ j < usz.toNat,
                      ws2[j]? = sp.core.arena[p.toNat + 3 + (idxs[j]?.getD 0)]?) ∧
                    (∀ q < k.toNat, q ∈ idxs ∨
                      sp.core.vals[(sp.core.arena[p.toNat + 3 + q]?.getD 0#32).toNat]?.getD 0#8 =
                        0xFF#8)) ∧
                  (FullMem c { sp with scratch := { sp.scratch with work_stk2 := ws2 } } ⋆ R) mk)
                ?_ ?_ ?_
              · rintro _ ⟨usz, _, neg_p, sat, _, ⟨⟩⟩ mb ⟨ws2, hws2_l, hnsat, hmb⟩
                let sb : FullState := { sp with scratch := { sp.scratch with work_stk2 := ws2 } }
                have hdb : FullDenseInvW c F0 F_cur sb := fullDenseInvW_with_ws2 hdp hws2_l
                have hnd_b : FullArenaVarsNodup sb := hdb.2.2.2.1
                m6_split_fast
                · clear hc; c0_hsteps!
                  exact hJnext (g_len, ticks + 1#64, ()) mb
                    ⟨sb, hdb, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, hgl_le, hseq_p, hmb⟩
                · have hsat_f : sat = false := hc; clear hc
                  m6_split_fast
                  · have hu_lt3 : 3 ≤ usz.toNat := by
                      simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                    clear hc; m6_split_fast
                    · have hu_le32 : usz.toNat ≤ 32 := by
                        simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                      clear hc; m6_split_fast
                      · have hu_cv : usz.toNat ≤ sb.core.cur_vars := by
                          simp only [BitVec.ule, decide_eq_true_eq, bv_zext32_toNat,
                            BitVec.toNat_ofNat] at hc
                          rw [Nat.mod_eq_of_lt (by omega)] at hc
                          dsimp only [sb]; rw [hcv_p]; exact hc
                        clear hc
                        obtain ⟨_, _, _, hlt_u, hneg_u, _, hdiff_u, hent_u⟩ := hnsat hsat_f
                        let arity := usz - 1#32
                        have har_n : arity.toNat = usz.toNat - 1 := by
                          dsimp only [arity]; bv_omega
                        c0_hsteps_nogrp; refine wp_join_group (ts := [i64])
                          (fun (gl', ()) mg => ∃ sg : FullState,
                            FullDenseInvW c F0 F_cur sg ∧ sg.core.cur_vars = s.core.cur_vars ∧
                            sg.core.fuel = s.core.fuel ∧ sg.core.repr = s.core.repr ∧
                            sg.core.inconsistent = s.core.inconsistent ∧
                            sg.core.arena = s1.core.arena ∧ sg.core.arena_len = s1.core.arena_len ∧
                            sg.scratch.work_stk2 = ws2 ∧
                            g_len.toNat ≤ gl'.toNat ∧ gl'.toNat ≤ g_cap.toNat ∧
                            M6GateSeqOk F_cur s.core.cur_vars sg.scratch.scratch_buf gl'.toNat 0 ∧
                            (FullMem c sg ⋆ R) mg)
                          ?_ ?_
                        · rintro _ ⟨gl', ⟨⟩⟩ mg
                            ⟨sg, hdg, hcv_g, hfl_g, hrep_g, hinc_g, har_g, hal_g, hws2_g,
                             hgl_lo, hgl_hi, hseq_g, hmg⟩
                          have hlen_g := hdg.1; have hscrl_g := hlen_g.scratch_ok.scratch_buf_len
                          m6_split_fast
                          · have hu3 : usz = 3#32 := beq_iff_eq.mp hc; clear hc
                            have hu3_n : usz.toNat = 3 := congrArg BitVec.toNat hu3
                            m6_split_fast
                            · have hgl14_le : gl'.toNat + 14 ≤ g_cap.toNat := by
                                simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                              have hlt3' := hlt_u
                              rw [hu3_n] at hlt3'
                              have hl0_lt := hlt3' 0 (by omega)
                              have hl1_lt := hlt3' 1 (by omega)
                              have hl2_lt := hlt3' 2 (by omega)
                              have hdiff01 := hdiff_u 0 (by omega) 1 (by omega) (by decide)
                              have hdiff02 := hdiff_u 0 (by omega) 2 (by omega) (by decide)
                              have hdiff12 := hdiff_u 1 (by omega) 2 (by omega) (by decide)
                              have hent3 : (cnfOfClauses F_cur).EntailsClause (cnfClause
                                  [(ws2[0]?.getD 0#32).toNat, (ws2[1]?.getD 0#32).toNat,
                                   (ws2[2]?.getD 0#32).toNat]) := by
                                simpa [hu3_n, List.range_succ] using hent_u
                              have hws2_0 : 0 < sg.scratch.work_stk2.length := by
                                rw [hws2_g, hws2_l]; omega
                              have hws2_1 : 1 < sg.scratch.work_stk2.length := by
                                rw [hws2_g, hws2_l]; omega
                              have hws2_2 : 2 < sg.scratch.work_stk2.length := by
                                rw [hws2_g, hws2_l]; omega
                              have hget0 : sg.scratch.work_stk2[0]'hws2_0 =
                                  ws2[0]?.getD 0#32 := by
                                rw [List.getElem?_eq_getElem (by rw [hws2_l]; omega),
                                  Option.getD_some]
                                simp [hws2_g]
                              have hget1 : sg.scratch.work_stk2[1]'hws2_1 =
                                  ws2[1]?.getD 0#32 := by
                                rw [List.getElem?_eq_getElem (by rw [hws2_l]; omega),
                                  Option.getD_some]
                                simp [hws2_g]
                              have hget2 : sg.scratch.work_stk2[2]'hws2_2 =
                                  ws2[2]?.getD 0#32 := by
                                rw [List.getElem?_eq_getElem (by rw [hws2_l]; omega),
                                  Option.getD_some]
                                simp [hws2_g]
                              have hload0 : loadVal mg i32 (c.pWorkStk2 + 0#64) =
                                  some (sg.scratch.work_stk2[0]'hws2_0) := by
                                simpa using FullArenaTactics.load_full_work_stk2 (i := 0) hws2_0 hmg
                              have hload1 : loadVal mg i32 (c.pWorkStk2 + 4#64) =
                                  some (sg.scratch.work_stk2[1]'hws2_1) := by
                                simpa using FullArenaTactics.load_full_work_stk2 (i := 1) hws2_1 hmg
                              have hload2 : loadVal mg i32 (c.pWorkStk2 + 8#64) =
                                  some (sg.scratch.work_stk2[2]'hws2_2) := by
                                simpa using FullArenaTactics.load_full_work_stk2 (i := 2) hws2_2 hmg
                              m3_let
                              refine wp_load_of (v := sg.scratch.work_stk2[0]'hws2_0) hload0 ?_
                              m3_let
                              refine wp_load_of (v := sg.scratch.work_stk2[1]'hws2_1) hload1 ?_
                              m3_let
                              refine wp_load_of (v := sg.scratch.work_stk2[2]'hws2_2) hload2 ?_
                              c0_hsteps!; m3_call hTryXorIte
                              refine ⟨c, F0, F_cur, sg, R, rfl, hlen_g, hdg.2.1, hdg.2.2.2.1,
                                hdg.2.2.2.2.2.1, ?_, ?_, ?_,
                                (by rw [hget0, hget1]; exact hdiff01),
                                (by rw [hget0, hget2]; exact hdiff02),
                                (by rw [hget1, hget2]; exact hdiff12), ?_,
                                by omega, hg_cap, by rw [hcv_g]; exact hseq_g, hmg,
                                fun ret scr' mg' hscrl' hret_lo hret_hi _ hseq' hmg' => ?_⟩
                              · rw [hget0, hcv_g, ← hcv_p]; exact hl0_lt
                              · rw [hget1, hcv_g, ← hcv_p]; exact hl1_lt
                              · rw [hget2, hcv_g, ← hcv_p]; exact hl2_lt
                              · rw [hget0, hget1, hget2]; exact hent3
                              · c0_hsteps!
                                exact hJnext (ret, ticks + 1#64 + 4#64, ()) mg'
                                  ⟨{ sg with scratch := { sg.scratch with scratch_buf := scr' } },
                                   fullDenseInvW_with_scr hdg hscrl', hcv_g, hfl_g, hrep_g, hinc_g,
                                   har_g, hal_g, hret_hi, by rw [← hcv_g]; exact hseq', hmg'⟩
                            · clear hc; c0_hsteps!
                              exact hJnext (gl', ticks + 1#64, ()) mg
                                ⟨sg, hdg, hcv_g, hfl_g, hrep_g, hinc_g, har_g, hal_g, hgl_hi,
                                 hseq_g, hmg⟩
                          · clear hc; m6_split_fast
                            · have hu4 : 4 ≤ usz.toNat := by
                                simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                              clear hc; m6_split_fast
                              · have hu5 : usz.toNat ≤ 5 := by
                                  simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                                clear hc; m6_split_fast
                                · have hgl25_le : gl'.toNat + 25 ≤ g_cap.toNat := by
                                    simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                                  clear hc; c0_hsteps!; m3_call hExtractXorK
                                  refine ⟨c, F0, F_cur, sg, R, rfl, hlen_g, hdg.2.1, hdg.2.2.1,
                                    hdg.2.2.2.1, hdg.2.2.2.2.2.1, by omega, by omega,
                                    by rw [hcv_g]; omega, by omega, hg_cap,
                                    by rw [hcv_g]; exact hseq_g,
                                    by rw [hws2_g]; intro j hj; rw [hcv_g, ← hcv_p]
                                       exact hlt_u j hj,
                                    by rw [hws2_g]; exact hneg_u,
                                    by rw [hws2_g]; exact hent_u, hmg,
                                    fun ret sx mx hlen_x hce hse hmk_x hret_lo hret_hi _ hseq_x
                                      hmx => ?_⟩
                                  have hdx := fullDenseInvW_of_xorK hdg hlen_x hce hse hmk_x
                                  obtain ⟨hinc_ce, har_ce, hal_ce, hcv_ce, _, _, hfu_ce, hrep_ce,
                                    _⟩ := core_fields_of_tmp_lm hce
                                  have hcv_x : sx.core.cur_vars = s.core.cur_vars :=
                                    hcv_ce.trans hcv_g
                                  have hfl_x : sx.core.fuel = s.core.fuel :=
                                    hfu_ce.trans hfl_g
                                  have hrep_x : sx.core.repr = s.core.repr :=
                                    hrep_ce.trans hrep_g
                                  have hinc_x : sx.core.inconsistent = s.core.inconsistent :=
                                    hinc_ce.trans hinc_g
                                  have har_x : sx.core.arena = s1.core.arena :=
                                    har_ce.trans har_g
                                  have hal_x : sx.core.arena_len = s1.core.arena_len :=
                                    hal_ce.trans hal_g
                                  c0_hsteps!
                                  exact hJnext (ret, ticks + 1#64 + 8#64, ()) mx
                                    ⟨sx, hdx, hcv_x, hfl_x, hrep_x, hinc_x, har_x, hal_x, hret_hi,
                                     by rw [← hcv_g]; exact hseq_x, hmx⟩
                                · clear hc; c0_hsteps!
                                  exact hJnext (gl', ticks + 1#64, ()) mg
                                    ⟨sg, hdg, hcv_g, hfl_g, hrep_g, hinc_g, har_g, hal_g, hgl_hi,
                                     hseq_g, hmg⟩
                              · clear hc; c0_hsteps!
                                exact hJnext (gl', ticks + 1#64, ()) mg
                                  ⟨sg, hdg, hcv_g, hfl_g, hrep_g, hinc_g, har_g, hal_g, hgl_hi,
                                   hseq_g, hmg⟩
                            · clear hc; c0_hsteps!
                              exact hJnext (gl', ticks + 1#64, ()) mg
                                ⟨sg, hdg, hcv_g, hfl_g, hrep_g, hinc_g, har_g, hal_g, hgl_hi,
                                 hseq_g, hmg⟩
                        · intro Jg hJg
                          have hjg0 : Jg (g_len, ()) mb :=
                            hJg (g_len, ()) mb ⟨sb, hdb, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p,
                              rfl, Nat.le_refl _, hgl_le, hseq_p, hmb⟩
                          m6_split_fast
                          · clear hc; c0_hsteps!
                            refine wp_loop_inv (ts := [i64, i32])
                              (fun (gc, i, ()) mi => ∃ scrc : List (BitVec 32),
                                scrc.length = c.scratch_cap ∧ g_len.toNat ≤ gc.toNat ∧
                                gc.toNat ≤ g_cap.toNat ∧ i.toNat ≤ usz.toNat ∧
                                M6GateSeqOk F_cur s.core.cur_vars scrc gc.toNat 0 ∧
                                (FullMem c { sb with scratch :=
                                  { sb.scratch with scratch_buf := scrc } } ⋆ R) mi)
                              (fun (_, i, ()) _ => usz.toNat - i.toNat)
                              (fun Ji hJi => by
                                c0_hsteps!
                                exact hJi (g_len, 0#32, ()) mb
                                  ⟨sb.scratch.scratch_buf, hscrl_p, Nat.le_refl _, hgl_le,
                                   Nat.zero_le _, hseq_p, hmb⟩)
                              (fun Ji (gc, i, ()) mi
                                ⟨scrc, hscrl_c, hgc_lo, hgc_hi, hi_le, hseq_c, hmi⟩ ihi => ?_)
                            m6_split_fast
                            · have hi_lt : i.toNat < usz.toNat := by
                                simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                              clear hc; m6_split_fast
                              · have hgc_ar : gc.toNat + 2 + arity.toNat ≤ g_cap.toNat := by
                                  simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                                clear hc
                                have hi_ws2 : i.toNat < ws2.length := by omega
                                let lhs := ws2[i.toNat]'hi_ws2
                                have hlhs_eq : ws2[i.toNat]?.getD 0#32 = lhs := by
                                  rw [List.getElem?_eq_getElem hi_ws2, Option.getD_some]
                                have hlhs_ws1 : (BitVec.setWidth 64 lhs).toNat <
                                    sb.scratch.work_stk1.length := by
                                  rw [bv_zext32_toNat]
                                  dsimp only [sb]
                                  rw [hws1_pl]
                                  have hlt_lhs := hlt_u i.toNat hi_lt
                                  rw [hlhs_eq] at hlt_lhs
                                  have := hcv_ple
                                  omega
                                have hi1_n : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
                                m6_split_fast
                                · clear hc
                                  let sc_c : FullState :=
                                    { sb with scratch := { sb.scratch with scratch_buf := scrc } }
                                  have hlen_c : sc_c.LengthsOk c :=
                                    ⟨hlen_p.core_ok,
                                     { hdb.1.scratch_ok with scratch_buf_len := hscrl_c }⟩
                                  have hwc_c : FullWitnessInv c F0 F_cur sc_c.core := hdb.2.1
                                  c0_hsteps_nogrp
                                  refine wp_loop_break_group (brkTs := [.bool, i32]) (lpTs := [i32])
                                    (fun (ok, _, ()) mj => mj = mi ∧
                                      (ok = true → ∀ k < usz.toNat, k ≠ i.toNat →
                                        (cnfOfClauses F_cur).EntailsClause (cnfClause
                                          [litNeg lhs.toNat,
                                           litNeg (ws2[k]?.getD 0#32).toNat])))
                                    (fun rem2 (j, ()) mj => mj = mi ∧ j.toNat ≤ usz.toNat ∧
                                      rem2 = usz.toNat - j.toNat ∧
                                      ∀ k < j.toNat, k ≠ i.toNat →
                                        (cnfOfClauses F_cur).EntailsClause (cnfClause
                                          [litNeg lhs.toNat,
                                           litNeg (ws2[k]?.getD 0#32).toNat]))
                                    ?_ ?_ ?_
                                  · rintro _ ⟨ok, _, ⟨⟩⟩ mj ⟨hmj_eq, hbins⟩
                                    subst mj
                                    m6_split_fast
                                    · have hbins' := hbins (by cases hc; rfl)
                                      have hgc0 : gc.toNat < scrc.length := by omega
                                      have hgc1_n : (gc + 1#64).toNat = gc.toNat + 1 := by bv_omega
                                      have hgc1 : (gc + 1#64).toNat < scrc.length := by omega
                                      c0_hsteps!
                                      let scrc0 := scrc.set gc.toNat lhs
                                      let scrc1 := scrc0.set (gc + 1#64).toNat arity
                                      refine wp_loop_inv (ts := [i32, i32])
                                        (fun (j2, rk, ()) mj2 => ∃ scrw : List (BitVec 32),
                                          scrw.length = c.scratch_cap ∧
                                          j2.toNat ≤ usz.toNat ∧
                                          rk.toNat = (if j2.toNat ≤ i.toNat then j2.toNat
                                            else j2.toNat - 1) ∧
                                          (∀ idx < gc.toNat, scrw[idx]? = scrc[idx]?) ∧
                                          scrw[gc.toNat]? = some lhs ∧
                                          scrw[gc.toNat + 1]? = some arity ∧
                                          (∀ k < j2.toNat, k ≠ i.toNat →
                                            scrw[gc.toNat + 2 + (if k < i.toNat then k else k - 1)]?
                                              = some ((ws2[k]?.getD 0#32) ^^^ 1#32)) ∧
                                          (FullMem c { sb with scratch :=
                                            { sb.scratch with scratch_buf := scrw } } ⋆ R) mj2)
                                        (fun (j2, _, ()) _ => usz.toNat - j2.toNat)
                                        (fun Jw hJw => by
                                          c0_hsteps!
                                          refine hJw (0#32, 0#32, ()) m
                                            ⟨scrc1, by simp [scrc1, scrc0, hscrl_c], Nat.zero_le _,
                                             by simp, fun idx hidx => ?_, ?_, ?_,
                                             (fun k hk => by cases hk), hm⟩
                                          · dsimp only [scrc1, scrc0]
                                            rw [List.getElem?_set_ne (by omega),
                                              List.getElem?_set_ne (by omega)]
                                          · dsimp only [scrc1, scrc0]
                                            rw [List.getElem?_set_ne (by omega),
                                              List.getElem?_set_self hgc0]
                                          · dsimp only [scrc1, scrc0]; rw [← hgc1_n]
                                            exact List.getElem?_set_self
                                              (by rw [List.length_set]; exact hgc1))
                                        (fun Jw (j2, rk, ()) mj2
                                          ⟨scrw, hscrlw, hj2_le, hrk_e, hprefw, hw0, hw1, hwrhs,
                                           hmj2⟩ ihw => ?_)
                                      m6_split_fast
                                      · have hj2_lt : j2.toNat < usz.toNat := by
                                          simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                                        have hj21_n : (j2 + 1#32).toNat = j2.toNat + 1 := by
                                          bv_omega
                                        clear hc; m6_split_fast
                                        · have hji : j2.toNat ≠ i.toNat := fun h =>
                                            (bne_iff_ne.mp hc) (BitVec.eq_of_toNat_eq h)
                                          have hj2_ws2 : j2.toNat < ws2.length := by omega
                                          have hrk1_n : (rk + 1#32).toNat = rk.toNat + 1 := by
                                            have hrk_lt : rk.toNat < arity.toNat := by
                                              rw [hrk_e, har_n]; split <;> omega
                                            bv_omega
                                          have hwr_n :
                                              (gc + 2#64 + rk.setWidth 64).toNat =
                                                gc.toNat + 2 + rk.toNat :=
                                            bv64_add_zext32 (k := 2) (by
                                              have hrk_lt : rk.toNat < arity.toNat := by
                                                rw [hrk_e, har_n]; split <;> omega
                                              have := hgc_ar; have := hg_cap; omega)
                                          have hwr_sc :
                                              (gc + 2#64 + rk.setWidth 64).toNat < scrw.length := by
                                            have hrk_lt : rk.toNat < arity.toNat := by
                                              rw [hrk_e, har_n]; split <;> omega
                                            have := hgc_ar; have := hg_cap
                                            rw [hwr_n, hscrlw]; omega
                                          c0_hsteps!
                                          refine ihw (j2 + 1#32, rk + 1#32, ()) m
                                            (by dsimp only; omega)
                                            ⟨scrw.set (gc + 2#64 + rk.setWidth 64).toNat
                                              (ws2[j2.toNat]'hj2_ws2 ^^^ 1#32),
                                             by simp [hscrlw], by omega,
                                             by rw [hj21_n, hrk1_n, hrk_e]
                                                split <;> split <;> omega,
                                             fun idx hidx => by
                                               rw [List.getElem?_set_ne (by omega)]
                                               exact hprefw idx hidx,
                                             by rw [List.getElem?_set_ne (by omega)]; exact hw0,
                                             by rw [List.getElem?_set_ne (by omega)]; exact hw1,
                                             fun k hk hkne => ?_, hm⟩
                                          by_cases hkj : k = j2.toNat
                                          · subst hkj
                                            have hset_lt :
                                                gc.toNat + 2 + (if j2.toNat < i.toNat then j2.toNat
                                                  else j2.toNat - 1) < scrw.length := by
                                              rw [hscrlw]; have := hgc_ar; have := hg_cap
                                              split <;> omega
                                            rw [hwr_n, hrk_e]
                                            rw [show (if j2.toNat ≤ i.toNat then j2.toNat
                                                  else j2.toNat - 1) =
                                                if j2.toNat < i.toNat then j2.toNat
                                                else j2.toNat - 1 by split <;> split <;> omega]
                                            rw [List.getElem?_set_self hset_lt]
                                            rw [List.getElem?_eq_getElem hj2_ws2, Option.getD_some]
                                          · rw [List.getElem?_set_ne (by
                                              rw [hwr_n, hrk_e]; split <;> split <;> omega)]
                                            exact hwrhs k (by omega) hkne
                                        · have hji : j2.toNat = i.toNat :=
                                            congrArg BitVec.toNat (by simpa using hc)
                                          c0_hsteps!
                                          refine ihw (j2 + 1#32, rk, ()) mj2 (by dsimp only; omega)
                                            ⟨scrw, hscrlw, by omega,
                                             by rw [hj21_n, hrk_e]; split <;> split <;> omega,
                                             hprefw, hw0, hw1,
                                             fun k hk hkne => hwrhs k (by omega) hkne, hmj2⟩
                                      · have hj2_e : j2.toNat = usz.toNat := by
                                          simp only [BitVec.ult, decide_eq_false_iff_not] at hc
                                          omega
                                        rw [hj2_e] at hwrhs
                                        have har_bv : arity = BitVec.ofNat 32 (usz.toNat - 1) := by
                                          apply BitVec.eq_of_toNat_eq
                                          rw [har_n, bv32_ofNat_toNat (by omega)]
                                        have hgat := m6_andGate_of_emitted hu_lt3 hu_le32
                                          hu_cv hi_lt hlt_u hent_u (hlhs_eq ▸ hbins') (by omega)
                                          (hlhs_eq ▸ hw0) (har_bv ▸ hw1) hwrhs
                                        have hgl_next : (gc + 2#64 + arity.setWidth 64).toNat =
                                            gc.toNat + 2 + (usz.toNat - 1) := by
                                          rw [bv64_add_zext32 (k := 2)
                                            (by have := hgc_ar; have := hg_cap; omega), har_n]
                                        have hseq_new : M6GateSeqOk F_cur s.core.cur_vars scrw
                                            (gc + 2#64 + arity.setWidth 64).toNat 0 := by
                                          rw [hgl_next]
                                          refine m6GateSeqOk_append (by omega) hprefw ?_ hseq_c
                                          refine .step ((show sb.core.cur_vars = s.core.cur_vars
                                            from hcv_p) ▸ hgat) ?_
                                          have hmword_ar :
                                              (arity &&& 0xFF#32).toNat = usz.toNat - 1 := by
                                            rw [BitVec.toNat_and, har_n,
                                              show (0xFF#32 : BitVec 32).toNat = 255 from rfl]
                                            simpa [Nat.mod_eq_of_lt
                                              (show usz.toNat - 1 < 256 by omega)]
                                              using Nat.and_two_pow_sub_one_eq_mod (usz.toNat - 1) 8
                                          simpa [hw1, hmword_ar] using M6GateSeqOk.done
                                        c0_hsteps!
                                        exact ihi (gc + 2#64 + arity.setWidth 64, i + 1#32, ()) mj2
                                          (by dsimp only; omega)
                                          ⟨scrw, hscrlw, by omega, by omega, by omega, hseq_new,
                                           hmj2⟩
                                    · clear hc; c0_hsteps!
                                      exact ihi (gc, i + 1#32, ()) mi (by dsimp only; omega)
                                        ⟨scrc, hscrl_c, hgc_lo, hgc_hi, by omega, hseq_c, hmi⟩
                                  · rintro B2 L2 rem2 ⟨j, ⟨⟩⟩ mj hB2 hL2 ⟨hmj_eq, hj_le, rfl, hseen⟩
                                    subst mj
                                    m6_split_fast
                                    · have hj_lt : j.toNat < usz.toNat := by
                                        simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                                      have hj1 : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
                                      clear hc; c0_hsteps_nogrp; refine wp_join_group (ts := [])
                                        (fun () m_j => m_j = mi ∧
                                          ∀ k < (j + 1#32).toNat, k ≠ i.toNat →
                                            (cnfOfClauses F_cur).EntailsClause (cnfClause
                                              [litNeg lhs.toNat,
                                               litNeg (ws2[k]?.getD 0#32).toNat]))
                                        ?_ ?_
                                      · rintro _ ⟨⟩ m_j ⟨hmj2_eq, hseen'⟩; subst m_j; c0_hsteps!
                                        exact hL2 (usz.toNat - (j + 1#32).toNat) (j + 1#32, ()) mi
                                          (by omega) ⟨rfl, by omega, rfl, hseen'⟩
                                      · intro Jj hJj; m6_split_fast
                                        · have hji : j.toNat ≠ i.toNat := fun h =>
                                            (bne_iff_ne.mp hc) (BitVec.eq_of_toNat_eq h)
                                          have hj_ws2 : j.toNat < ws2.length := by omega
                                          c0_hsteps!; m3_call hHasBin
                                          refine ⟨c, F0, F_cur, sc_c, R, rfl, hlen_c, hwc_c, hmi,
                                            fun hb hhb => ?_⟩
                                          m6_split_fast
                                          · have hnew :
                                                (cnfOfClauses F_cur).EntailsClause (cnfClause
                                                  [litNeg lhs.toNat,
                                                   litNeg (ws2[j.toNat]?.getD 0#32).toNat]) := by
                                              have h0 := (hhb (by cases hc; rfl)).2.2.2.2
                                              simp only [sb, bv_zext32_toNat] at h0
                                              have h1 : (cnfOfClauses F_cur).EntailsClause
                                                  (cnfClause [(lhs ^^^ 1#32).toNat,
                                                    ((ws2[j.toNat]?.getD 0#32) ^^^ 1#32).toNat]) :=
                                                by
                                                dsimp only [lhs]
                                                rw [List.getElem?_eq_getElem hj_ws2,
                                                  Option.getD_some]
                                                exact h0
                                              rw [bv32_xor1_eq_litNeg, bv32_xor1_eq_litNeg] at h1
                                              exact h1
                                            c0_hsteps!
                                            exact hJj () mi ⟨rfl, fun k hk hkne => by
                                              rw [hj1] at hk
                                              by_cases hkj : k = j.toNat
                                              · subst hkj; exact hnew
                                              · exact hseen k (by omega) hkne⟩
                                          · c0_hsteps!
                                            exact hB2 (false, j, ()) mi ⟨rfl, fun hf => by cases hf⟩
                                        · have hji : j.toNat = i.toNat :=
                                            congrArg BitVec.toNat (by simpa using hc)
                                          c0_hsteps!
                                          exact hJj () mi ⟨rfl, fun k hk hkne =>
                                            hseen k (by omega) hkne⟩
                                    · have hj_e : j.toNat = usz.toNat := by
                                        simp only [BitVec.ult, decide_eq_false_iff_not] at hc; omega
                                      rw [hj_e] at hseen; c0_hsteps!
                                      exact hB2 (true, j, ()) mi ⟨rfl, fun _ => hseen⟩
                                  · intro _ L2 _ hL2; c0_hsteps!
                                    exact hL2 (usz.toNat - 0) (0#32, ()) mi
                                      ⟨rfl, Nat.zero_le _, rfl, fun _ h => by simp at h⟩
                                · clear hc; c0_hsteps!
                                  exact ihi (gc, i + 1#32, ()) mi (by dsimp only; omega)
                                    ⟨scrc, hscrl_c, hgc_lo, hgc_hi, by omega, hseq_c, hmi⟩
                              · clear hc; c0_hsteps!
                                exact hJg (gc, ()) mi
                                  ⟨{ sb with scratch := { sb.scratch with scratch_buf := scrc } },
                                   fullDenseInvW_with_scr hdb hscrl_c, hcv_p, hfl_p, hrep_p, hinc_p,
                                   har_p, hal_p, rfl, hgc_lo, hgc_hi, hseq_c, hmi⟩
                            · clear hc; c0_hsteps!
                              exact hJg (gc, ()) mi
                                ⟨{ sb with scratch := { sb.scratch with scratch_buf := scrc } },
                                 fullDenseInvW_with_scr hdb hscrl_c, hcv_p, hfl_p, hrep_p, hinc_p,
                                 har_p, hal_p, rfl, hgc_lo, hgc_hi, hseq_c, hmi⟩
                          · clear hc; c0_hsteps!; exact hjg0
                      · clear hc; c0_hsteps!
                        exact hJnext (g_len, ticks + 1#64, ()) mb
                          ⟨sb, hdb, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, hgl_le, hseq_p, hmb⟩
                    · clear hc; c0_hsteps!
                      exact hJnext (g_len, ticks + 1#64, ()) mb
                        ⟨sb, hdb, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, hgl_le, hseq_p, hmb⟩
                  · clear hc; c0_hsteps!
                    exact hJnext (g_len, ticks + 1#64, ()) mb
                      ⟨sb, hdb, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, hgl_le, hseq_p, hmb⟩
              · rintro B3 L3 rem3 ⟨usz, max_nbc, neg_p, k, ⟨⟩⟩ mk hB3 hL3
                  ⟨ws2, hws2_l, hk_le, rfl, hu_k, hu_cv, hlt_u, hneg_u,
                   ⟨idxs, hid_len, hid_nd, hid_lt, hws2_map, hcov_k⟩, hmk⟩
                m6_split_fast
                · have hk_lt : k.toNat < sz_bv.toNat := by
                    simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                  have hk1_n : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
                  have hp3k_n : (p + 3#64 + k.setWidth 64).toNat = p.toNat + 3 + k.toNat :=
                    bv64_add_zext32 (k := 3) (by omega)
                  have hp3k_arr : (p + 3#64 + k.setWidth 64).toNat < sp.core.arena.length := by
                    omega
                  let lk := sp.core.arena[(p + 3#64 + k.setWidth 64).toNat]'hp3k_arr
                  have hlk_eq : lk = sp.core.arena[p.toNat + 3 + k.toNat]'(by omega) :=
                    list_getElem_congr hp3k_n hp3k_arr (by omega)
                  have hlk_lt : lk.toNat < 2 * sp.core.cur_vars := by
                    have hmem_lk : lk.toNat ∈ fullArenaClauseLits sp p.toNat := by
                      unfold fullArenaClauseLits fullArenaClauseLitsCore
                      have hsz_szbv :
                          fullArenaClauseSizeCore sp.core p.toNat = sz_bv.toNat := hsz_eq
                      have : p.toNat + 3 + fullArenaClauseSizeCore sp.core p.toNat ≤
                          sp.core.arena.length := by
                        rw [hsz_szbv]; exact hbd_sz
                      simp only [List.mem_map]
                      refine ⟨lk, ?_, rfl⟩
                      have hk_s : k.toNat < fullArenaClauseSizeCore sp.core p.toNat := by
                        rw [hsz_szbv]; exact hk_lt
                      have hget : ((sp.core.arena.drop (p.toNat + 3)).take
                          (fullArenaClauseSizeCore sp.core p.toNat))[k.toNat]'(by
                            simp [List.length_take, List.length_drop]; omega) = lk := by
                        simp [List.getElem_take, List.getElem_drop, hlk_eq]
                      rw [← hget]; exact List.getElem_mem _
                    exact hdp.2.1.arena.lits_lt p.toNat hp_ref hng lk.toNat hmem_lk
                  have hlk_v : (lk.setWidth 64).toNat < sp.core.vals.length := by
                    rw [bv_zext32_toNat]; omega
                  have hlk_v' : lk.toNat < sp.core.vals.length := by
                    rw [bv_zext32_toNat] at hlk_v; exact hlk_v
                  clear hc; m6_split_fast
                  · c0_hsteps!
                    exact hB3 (usz, max_nbc, neg_p, true, k, ()) mk
                      ⟨ws2, hws2_l, (fun hf => by cases hf), hmk⟩
                  · have hdom_lk : sp.core.vals[(lk.setWidth 64).toNat]'hlk_v = 0#8 ∨
                        sp.core.vals[(lk.setWidth 64).toNat]'hlk_v = 1#8 ∨
                        sp.core.vals[(lk.setWidth 64).toNat]'hlk_v = 0xFF#8 := by
                      have hdom_lk0 := hdp.2.1.vals_domain lk.toNat hlk_lt
                      rw [List.getElem?_eq_getElem hlk_v', Option.getD_some] at hdom_lk0
                      rw [list_getElem_congr (bv_zext32_toNat lk) hlk_v hlk_v']
                      exact hdom_lk0
                    have hnsgt : ¬ (0#32 : BitVec 32).slt
                        ((sp.core.vals[(lk.setWidth 64).toNat]'hlk_v).signExtend 32) = true := by
                      have hc0 : (0#32 : BitVec 32).slt
                          ((sp.core.vals[(lk.setWidth 64).toNat]'hlk_v).signExtend 32) = false :=
                        hc
                      rw [hc0]; decide
                    clear hc; m6_split_fast
                    · have heq0 : sp.core.vals[(lk.setWidth 64).toNat]'hlk_v = 0#8 :=
                        FullM3CongBva.bv8_eq0_of_signExtend32 hdom_lk (beq_iff_eq.mp hc)
                      clear hc; m6_split_fast
                      · have hu_lt_cv : usz.toNat < sp.core.cur_vars := by
                          rw [hcv_p]
                          simp only [BitVec.ult, decide_eq_true_eq, bv_zext32_toNat,
                            BitVec.toNat_ofNat] at hc
                          rwa [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
                        have hu1_n : (usz + 1#32).toNat = usz.toNat + 1 := by bv_omega
                        have hu_ws2 : usz.toNat < ws2.length := by omega
                        have hu_ws2_64 : (usz.setWidth 64).toNat < ws2.length := by
                          rw [bv_zext32_toNat]; exact hu_ws2
                        let ws2' := ws2.set usz.toNat lk
                        have hlk_ws1 : (lk.setWidth 64).toNat < sp.scratch.work_stk1.length := by
                          rw [bv_zext32_toNat, hws1_pl]; exact Nat.lt_of_lt_of_le hlk_lt (by omega)
                        clear hc; m3_let
                        refine wp_store_sep
                          (FullArenaTactics.c0_store_full_work_stk2 lk hu_ws2_64 hmk) ?_
                        intro m_st hm_st
                        let sp2 : FullState :=
                          { sp with scratch := { sp.scratch with work_stk2 := ws2' } }
                        have hm2 : (FullMem c sp2 ⋆ R) m_st := by
                          simpa only [sp2, ws2', bv_zext32_toNat] using hm_st
                        have hlk_ws1' : (lk.setWidth 64).toNat < sp2.scratch.work_stk1.length :=
                          hlk_ws1
                        c0_hsteps_nogrp
                        refine wp_join_group (ts := [i32])
                          (fun (_mn, ()) mmn => mmn = m_st) ?_ ?_
                        · rintro _ ⟨mn', ⟨⟩⟩ mmn hmmn; rw [hmmn]
                          c0_hsteps_nogrp
                          refine wp_join_group (ts := [i32])
                            (fun (np', ()) mnp => mnp = m_st ∧
                              np' = (if (lk &&& 1#32) != 0#32 then neg_p ^^^ 1#32 else neg_p))
                            ?_ ?_
                          · rintro _ ⟨neg_p', ⟨⟩⟩ mnp ⟨hmnp, hnp'⟩; rw [hmnp, hnp']
                            c0_hsteps!
                            refine hL3 (sz_bv.toNat - (k + 1#32).toNat)
                              (usz + 1#32, _,
                               (if (lk &&& 1#32) != 0#32 then neg_p ^^^ 1#32 else neg_p),
                               k + 1#32, ()) m_st (by omega)
                              ⟨ws2', by simp [ws2', hws2_l], by omega, rfl, by omega, by omega,
                               fun j hj => ?_, ?_, ?_, hm2⟩
                            · dsimp only [ws2']; by_cases hju : j = usz.toNat
                              · subst hju; rw [List.getElem?_set_self hu_ws2, Option.getD_some]
                                exact hlk_lt
                              · rw [List.getElem?_set_ne (Ne.symm hju)]; exact hlt_u j (by omega)
                            · rw [hu1_n, List.range_succ, List.foldl_append, List.foldl_cons,
                                List.foldl_nil]
                              have hfold_eq : ∀ n ≤ usz.toNat,
                                  List.foldl (fun acc i =>
                                    acc ^^^ ((ws2'[i]?.getD 0#32).toNat % 2)) 0 (List.range n) =
                                  List.foldl (fun acc i =>
                                    acc ^^^ ((ws2[i]?.getD 0#32).toNat % 2)) 0 (List.range n) := by
                                intro n hn
                                induction n with
                                | zero => rfl
                                | succ n ih =>
                                  simp only [List.range_succ, List.foldl_append, List.foldl_cons,
                                    List.foldl_nil, ih (by omega)]
                                  congr 2; dsimp only [ws2']
                                  rw [List.getElem?_set_ne (by omega)]
                              rw [hfold_eq usz.toNat (Nat.le_refl _), ← hneg_u]
                              have hlast : ws2'[usz.toNat]?.getD 0#32 = lk := by
                                dsimp only [ws2']
                                rw [List.getElem?_set_self hu_ws2, Option.getD_some]
                              rw [hlast]; exact bv32_bit1_ne0_mod2
                            · refine ⟨idxs ++ [k.toNat], by simp [hid_len, hu1_n], ?_,
                                fun q hq => ?_, fun j hj => ?_, fun q hq => ?_⟩
                              · rw [List.nodup_append]
                                refine ⟨hid_nd, by simp, fun q hq b hb _ => ?_⟩
                                cases hb with
                                | head => have := hid_lt q hq; omega
                                | tail _ ht => cases ht
                              · simp only [List.mem_append, List.mem_singleton] at hq
                                rcases hq with hq | rfl
                                · have := hid_lt q hq; omega
                                · omega
                              · dsimp only [ws2']; rw [hu1_n] at hj
                                by_cases hju : j = usz.toNat
                                · subst hju
                                  rw [List.getElem?_set_self hu_ws2]
                                  have hid_e : (idxs ++ [k.toNat])[usz.toNat]? = some k.toNat := by
                                    rw [List.getElem?_append_right (by omega), hid_len,
                                      Nat.sub_self]
                                    simp
                                  rw [hid_e, Option.getD_some,
                                    List.getElem?_eq_getElem (by omega), hlk_eq]
                                · rw [List.getElem?_set_ne (Ne.symm hju)]
                                  have hid_l : (idxs ++ [k.toNat])[j]? = idxs[j]? :=
                                    List.getElem?_append_left (by omega)
                                  rw [hid_l]; exact hws2_map j (by omega)
                              · simp only [List.mem_append, List.mem_singleton]
                                by_cases hqk : q = k.toNat
                                · subst hqk; exact Or.inl (Or.inr rfl)
                                · rcases hcov_k q (by omega) with hin | hff
                                  · exact Or.inl (Or.inl hin)
                                  · exact Or.inr hff
                          · intro Jnp hJnp; m6_split_fast
                            · have hbnz : ((lk &&& 1#32) != 0#32) = true := hc
                              m3_let
                              exact hJnp (neg_p ^^^ 1#32, ()) m_st ⟨rfl, by rw [hbnz]; rfl⟩
                            · have hbnz : ((lk &&& 1#32) != 0#32) = false := hc
                              have hbz : ¬ ((lk &&& 1#32) != 0#32) = true := by
                                rw [hbnz]; decide
                              m3_let
                              exact hJnp (neg_p, ()) m_st ⟨rfl, by rw [ite_eq_right hbz]⟩
                        · intro Jmn hJmn; m6_split_fast
                          · m3_let; exact hJmn (_, ()) m_st rfl
                          · m3_let; exact hJmn (_, ()) m_st rfl
                      · c0_hsteps!
                        exact hB3 (usz, max_nbc, neg_p, true, k, ()) mk
                          ⟨ws2, hws2_l, (fun hf => by cases hf), hmk⟩
                    · have hne0 : sp.core.vals[(lk.setWidth 64).toNat]'hlk_v ≠ 0#8 := by
                        apply FullM3CongBva.bv8_ne0_of_signExtend32 hdom_lk
                        exact beq_eq_false_iff_ne.mp hc
                      have hff_lk : sp.core.vals[(lk.setWidth 64).toNat]?.getD 0#8 = 0xFF#8 := by
                        rw [List.getElem?_eq_getElem hlk_v, Option.getD_some]
                        exact FullM3CongBva.bv8_ne0_not_signExtend32_sgt0_eqff hdom_lk hne0 hnsgt
                      c0_hsteps!
                      refine hL3 (sz_bv.toNat - (k + 1#32).toNat)
                        (usz, max_nbc, neg_p, k + 1#32, ()) mk (by omega)
                        ⟨ws2, hws2_l, by omega, rfl, by omega, hu_cv, hlt_u, hneg_u,
                         ⟨idxs, hid_len, hid_nd, fun q hq => by have := hid_lt q hq; omega,
                          hws2_map, fun q hq => ?_⟩, hmk⟩
                      by_cases hqk : q = k.toNat
                      · subst hqk; right
                        have hk_ar : sp.core.arena[p.toNat + 3 + k.toNat]?.getD 0#32 = lk := by
                          rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hlk_eq]
                        rw [hk_ar]; rw [bv_zext32_toNat] at hff_lk; exact hff_lk
                      · exact hcov_k q (by omega)
                · have hk_e : k.toNat = sz_bv.toNat := by
                    simp only [BitVec.ult, decide_eq_false_iff_not] at hc
                    change ¬ k.toNat < sz_bv.toNat at hc; omega
                  have hsz_bv : fullArenaClauseSizeCore sp.core p.toNat = sz_bv.toNat := hsz_eq
                  have hcov_all : ∀ l ∈ fullArenaClauseLits sp p.toNat,
                      sp.core.vals[l]?.getD 0#8 = 0xFF#8 ∨ l ∈
                        ((List.range usz.toNat).map fun j => (ws2[j]?.getD 0#32).toNat) := by
                    intro l hl
                    unfold fullArenaClauseLits fullArenaClauseLitsCore at hl
                    rw [hsz_bv] at hl
                    rw [List.mem_map] at hl; obtain ⟨bv, hbv, rfl⟩ := hl
                    obtain ⟨q, hq, hget⟩ := List.mem_iff_getElem.mp hbv
                    rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)] at hq
                    have hq_lt : q < sz_bv.toNat := hq
                    have hbd_q : p.toNat + 3 + q < sp.core.arena.length := by
                      have := hbd_sz; omega
                    rw [List.getElem_take, List.getElem_drop] at hget
                    rcases hcov_k q (hk_e ▸ hq_lt) with hin | hff
                    · right; obtain ⟨j, hj, hgetj⟩ := List.mem_iff_getElem.mp hin
                      have hj_u : j < usz.toNat := by omega
                      have hm_j := hws2_map j hj_u
                      have hid_j : (idxs[j]?.getD 0) = q := by
                        rw [List.getElem?_eq_getElem hj, Option.getD_some, hgetj]
                      rw [hid_j, List.getElem?_eq_getElem (by omega),
                        List.getElem?_eq_getElem hbd_q, hget] at hm_j
                      rw [List.mem_map]; refine ⟨j, List.mem_range.mpr hj_u, ?_⟩
                      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                      exact congrArg BitVec.toNat (Option.some.inj hm_j)
                    · left; rw [List.getElem?_eq_getElem hbd_q, Option.getD_some, hget] at hff
                      exact hff
                  have hent_u :=
                    unassigned_clause_entails hdp.2.1 hdp.2.2.2.2.2.1 hp_ref hng hcov_all
                  have hnd_u : (idxs.map fun q =>
                      (sp.core.arena[p.toNat + 3 + q]?.getD 0#32).toNat / 2).Nodup := by
                    have hnd_sp := hdp.2.2.2.1 p.toNat hp_ref hng
                    have har_lits : fullArenaClauseLits sp p.toNat =
                        ((List.range sz_bv.toNat).map fun q =>
                          (sp.core.arena[p.toNat + 3 + q]?.getD 0#32).toNat) := by
                      unfold fullArenaClauseLits fullArenaClauseLitsCore; rw [hsz_bv]
                      apply List.ext_getElem
                      · simp only [List.length_map, List.length_take, List.length_drop,
                          List.length_range]
                        exact Nat.min_eq_left (by omega)
                      · intro q hq _
                        simp only [List.length_map, List.length_take, List.length_drop] at hq
                        rw [Nat.min_eq_left (by omega)] at hq
                        have hbd_q : p.toNat + 3 + q < sp.core.arena.length := by
                          have := hbd_sz; omega
                        simp only [List.getElem_map, List.getElem_take, List.getElem_drop,
                          List.getElem_range]
                        rw [List.getElem?_eq_getElem hbd_q, Option.getD_some]
                    rw [har_lits, List.map_map] at hnd_sp
                    exact list_nodup_filter_map
                      (fun q => (sp.core.arena[p.toNat + 3 + q]?.getD 0#32).toNat / 2)
                      hnd_sp hid_nd (fun q hq => by rw [← hk_e]; exact hid_lt q hq) (fun _ => rfl)
                  have hdiff_u : ∀ j < usz.toNat, ∀ j2 < usz.toNat, j ≠ j2 →
                      (ws2[j]?.getD 0#32).toNat / 2 ≠ (ws2[j2]?.getD 0#32).toNat / 2 := by
                    intro j hj j2 hj2 hne
                    have hm1 := hws2_map j hj; have hm2 := hws2_map j2 hj2
                    rw [hm1, hm2]
                    have hind := nodup_getElem_inj hnd_u j j2 (by simp [hid_len, hj])
                      (by simp [hid_len, hj2])
                    intro heq
                    have hij1 : idxs[j]?.getD 0 = idxs[j]'(by simp [hid_len, hj]) := by
                      rw [List.getElem?_eq_getElem (by simp [hid_len, hj]), Option.getD_some]
                    have hij2 : idxs[j2]?.getD 0 = idxs[j2]'(by simp [hid_len, hj2]) := by
                      rw [List.getElem?_eq_getElem (by simp [hid_len, hj2]), Option.getD_some]
                    rw [hij1, hij2] at heq
                    exact hne (hind (by simp only [List.getElem_map]; exact heq))
                  c0_hsteps!
                  exact hB3 (usz, max_nbc, neg_p, false, k, ()) mk
                    ⟨ws2, hws2_l, fun _ => ⟨hsz3, by omega, hu_cv, hlt_u, hneg_u,
                      ⟨idxs, hid_len, hid_nd, fun q hq => by rw [← hk_e]; exact hid_lt q hq,
                       fun j hj _ => hws2_map j hj,
                       fun q hq => by rw [← hk_e] at hq; exact hcov_k q hq⟩,
                      hdiff_u, hent_u⟩, hmk⟩
              · intro _ L3 _ hL3; c0_hsteps!
                exact hL3 (sz_bv.toNat - 0) (0#32, 0#32, 0#32, 0#32, ()) mp
                  ⟨sp.scratch.work_stk2, hws2_pl, Nat.zero_le _, rfl, Nat.zero_le _, Nat.zero_le _,
                   (fun _ h => by cases h), (by simp),
                   ⟨[], rfl, .nil, (fun _ h => by cases h), (fun _ h => by cases h),
                    (fun _ h => by cases h)⟩, hmp⟩
            · clear hc; c0_hsteps!; exact hjnext_same
          · clear hc; c0_hsteps!; exact hjnext_same
        · clear hc; c0_hsteps!; exact hjnext_same
      · clear hc; c0_hsteps!; exact hq_done
    · clear hc; c0_hsteps!; exact hq_done
  · clear hc; c0_hsteps!; exact hq_done

end LeanQbe.T.Examples.Kissat.FullM6CongSubst
