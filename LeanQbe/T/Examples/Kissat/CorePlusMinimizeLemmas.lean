module

public import LeanQbe.T.Examples.Kissat.CorePlusMinimizeLemmas1

/-!
# Kissat `CorePlus` Iterative Literal and Clause Minimization Proofs (`Wave 1b`)

Proves the remaining two minimization functions in `CorePlus.lean` on top of
`CorePlusMinimizeLemmas1`:
1. `kissat_minimize_lit` (`corePlusMinimizeLitSpec`, `kissat_minimize_lit_wp`).
2. `kissat_minimize_clause` (`corePlusMinimizeClauseSpec`, `kissat_min_clause_wp`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.CorePlus

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat

section
open scoped MinTactics

/-! ## 1. `kissat_minimize_lit` (`corePlusMinimizeLitSpec`) -/

private structure MinLitBrkFacts (c : CorePlusCfg) (s : CorePlusState)
    (keepSet : List Nat) (root_lit : Nat) (r : Tup Val [i64, .bool, i64])
    (m : Mem 64) (R : Mem 64 → Prop) (mrk' : List (BitVec 8))
    (mstk' mclr' : List (BitVec 32)) (mcl' : Nat) (mcf' : BitVec 64) : Prop where
  sp_lt : r.1.toNat < c.minDepth
  mrk_len : mrk'.length = c.mv
  stk_len : mstk'.length = 2 * c.minDepth
  clr_len : mclr'.length = c.mv
  clr_le : mcl' ≤ c.mv
  pres2 : ∀ w < c.mv, s.mrk[w]?.getD 0#8 = 2#8 → mrk'[w]?.getD 0#8 = 2#8
  hmin : MinMarkInv c (withMinFields s mrk' mstk' mclr' mcl' mcf') keepSet
  hok : r.2.1 = true → ∀ keep' : List Nat,
    (∀ l ∈ keepSet, l = root_lit ∨ l ∈ keep') →
    MinMarkInv c (withMinFields s mrk' mstk' mclr' mcl' mcf') keep'
  hm : (CorePlusMem c (withMinFields s mrk' mstk' mclr' mcl' mcf') ⋆ R) m

private def MinLitBrk (c : CorePlusCfg) (s : CorePlusState)
    (keepSet : List Nat) (root_lit : Nat) (r : Tup Val [i64, .bool, i64])
    (m : Mem 64) (R : Mem 64 → Prop) : Prop :=
  ∃ mrk' mstk' mclr' mcl' mcf',
    MinLitBrkFacts c s keepSet root_lit r m R mrk' mstk' mclr' mcl' mcf'

private structure MinLitInvFacts (c : CorePlusCfg) (s : CorePlusState)
    (keepSet : List Nat) (root_lit idx0 maxSteps : Nat) (v : Tup Val [i64, i64])
    (m : Mem 64) (R : Mem 64 → Prop) (mrk' : List (BitVec 8))
    (mstk' mclr' : List (BitVec 32)) (mcl' : Nat) (mcf' : BitVec 64) : Prop where
  steps_le : v.2.1.toNat ≤ maxSteps
  mrk_len : mrk'.length = c.mv
  stk_len : mstk'.length = 2 * c.minDepth
  clr_len : mclr'.length = c.mv
  clr_le : mcl' ≤ c.mv
  pres2 : ∀ w < c.mv, s.mrk[w]?.getD 0#8 = 2#8 → mrk'[w]?.getD 0#8 = 2#8
  hmin : MinMarkInv c (withMinFields s mrk' mstk' mclr' mcl' mcf') keepSet
  frames : MinFrameOk c s mrk' mstk' root_lit idx0 v.1.toNat
  hm : (CorePlusMem c (withMinFields s mrk' mstk' mclr' mcl' mcf') ⋆ R) m

private def MinLitInv (c : CorePlusCfg) (s : CorePlusState)
    (keepSet : List Nat) (root_lit idx0 maxSteps : Nat) (v : Tup Val [i64, i64])
    (m : Mem 64) (R : Mem 64 → Prop) : Prop :=
  ∃ mrk' mstk' mclr' mcl' mcf',
    MinLitInvFacts c s keepSet root_lit idx0 maxSteps v m R mrk' mstk' mclr' mcl' mcf'

private theorem MinLitInv.to_brk_false {c : CorePlusCfg} {s : CorePlusState}
    {keepSet : List Nat} {root_lit idx0 maxSteps : Nat} {sp steps steps' : BitVec 64}
    {m : Mem 64} {R : Mem 64 → Prop}
    (inv : MinLitInv c s keepSet root_lit idx0 maxSteps (sp, steps, ()) m R) :
    MinLitBrk c s keepSet root_lit (sp, false, steps', ()) m R := by
  obtain ⟨mrk, mstk, mclr, mcl, mcf, _, hml, hsl, hcl, hcle, hp2, hmin, hf, hm⟩ := inv
  exact ⟨mrk, mstk, mclr, mcl, mcf, hf.sp_lt, hml, hsl, hcl, hcle, hp2, hmin,
    (fun h => by cases h), hm⟩

private theorem MinLitInv.to_brk_false_pos {c : CorePlusCfg} {s : CorePlusState}
    {keepSet : List Nat} {root_lit : Nat}
    {mrk : List (BitVec 8)} {mstk mclr : List (BitVec 32)} {mcl : Nat} {mcf sp steps' : BitVec 64}
    {pos' : BitVec 32} {m : Mem 64} {R : Mem 64 → Prop}
    (hsp : sp.toNat < c.minDepth) (hml : mrk.length = c.mv)
    (hsl : mstk.length = 2 * c.minDepth) (hcl : mclr.length = c.mv) (hcle : mcl ≤ c.mv)
    (hp2 : ∀ w < c.mv, s.mrk[w]?.getD 0#8 = 2#8 → mrk[w]?.getD 0#8 = 2#8)
    (hmin : MinMarkInv c (withMinFields s mrk mstk mclr mcl mcf) keepSet)
    (hm : (CorePlusMem c (withMinFields s mrk (mstk.set (2 * sp.toNat + 1) pos') mclr mcl mcf)
      ⋆ R) m) :
    MinLitBrk c s keepSet root_lit (sp, false, steps', ()) m R :=
  ⟨mrk, mstk.set (2 * sp.toNat + 1) pos', mclr, mcl, mcf, hsp, hml, by simp [hsl], hcl, hcle,
    hp2, minMarkInv_set_stk hmin _, (fun h => by cases h), hm⟩

private theorem min_lit_skip_cont {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    {keepSet : List Nat} {root_lit idx0 maxSteps : Nat}
    {mrk : List (BitVec 8)} {mstk mclr : List (BitVec 32)} {mcl : Nat} {mcf : BitVec 64}
    {sp steps' : BitVec 64} {pos' : BitVec 32} {m' : Mem 64} {R : Mem 64 → Prop}
    (hcore : CorePlusCoreInv c F0 s) (hst : steps'.toNat ≤ maxSteps)
    (hmrkl : mrk.length = c.mv) (hmstkl : mstk.length = 2 * c.minDepth)
    (hmcl : mclr.length = c.mv) (hmcl_le : mcl ≤ c.mv)
    (hp2 : ∀ w < c.mv, s.mrk[w]?.getD 0#8 = 2#8 → mrk[w]?.getD 0#8 = 2#8)
    (hmin : MinMarkInv c (withMinFields s mrk mstk mclr mcl mcf) keepSet)
    (hf : MinFrameOk c s mrk mstk root_lit idx0 sp.toNat)
    {rcid : BitVec 32}
    (hrsn : s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 = rcid)
    (hrne : rcid ≠ 0xFFFFFFFF#32)
    (hpos_lt : (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat < clauseSize s rcid.toNat)
    (hpos_eq : (mstk[2 * sp.toNat + 1]?.getD 0#32) = pos')
    (hcond : let q := (s.lpool[clauseOff s rcid.toNat + pos'.toNat]?.getD 0#32).toNat
      q / 2 = (mstk[2 * sp.toNat]?.getD 0#32).toNat ∨
      (s.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ mrk[q / 2]?.getD 0#8 = 2#8)
    (hm' : (CorePlusMem c (withMinFields s mrk
      (mstk.set (2 * sp.toNat + 1) (pos' + 1#32)) mclr mcl mcf) ⋆ R) m') :
    MinLitInv c s keepSet root_lit idx0 maxSteps (sp, steps', ()) m' R := by
  have hu32 : pos'.toNat + 1 < 2 ^ 32 := by
    obtain ⟨_, _, _, _, _, _, _, hrc2, _⟩ := hf.idx sp.toNat (le_refl _)
    rw [hrsn] at hrc2; rw [← hpos_eq]
    have := hcore.lengths.lit_len_le; have := hcore.clauses.bounds rcid.toNat hrc2
    have := c.hlcap; unfold dimacsBound at *; omega
  have hset : mstk.set (2 * sp.toNat + 1) (pos' + 1#32) =
      mstk.set (2 * sp.toNat + 1) (BitVec.ofNat 32 (pos'.toNat + 1)) := by congr 1
  refine ⟨mrk, mstk.set (2 * sp.toNat + 1) (pos' + 1#32), mclr, mcl, mcf, hst, hmrkl,
    by simp [hmstkl], hmcl, hmcl_le, hp2, minMarkInv_set_stk hmin _, ?_, hm'⟩
  rw [hset]
  refine minFrameOk_skip hf (congrArg BitVec.toNat hpos_eq) hu32 fun idx_sp hi htr => ?_
  dsimp only; rw [hrsn]
  have hrel := min_lit_child_rel hcore hi (by rw [htr]; exact hrsn) hrne (hpos_eq ▸ hpos_lt)
  rcases hrel with ⟨hd, heq⟩ | ⟨hne, k, hk, hkeq⟩
  · exact Or.inl heq
  · rcases hcond with hq | hl0 | hm2
    · exact absurd hq (by rwa [htr] at hne)
    · exact Or.inr ⟨k, hk, hkeq, Or.inl hl0⟩
    · exact Or.inr ⟨k, hk, hkeq, Or.inr hm2⟩

private theorem min_lit_push_cont {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    {keepSet : List Nat} {root_lit idx0 maxSteps : Nat}
    {mrk : List (BitVec 8)} {mstk mclr : List (BitVec 32)} {mcl : Nat} {mcf : BitVec 64}
    {sp steps' : BitVec 64} {pos' u ur : BitVec 32} {m' : Mem 64} {R : Mem 64 → Prop}
    (hcore : CorePlusCoreInv c F0 s) (hst : steps'.toNat ≤ maxSteps)
    (hmrkl : mrk.length = c.mv) (hmstkl : mstk.length = 2 * c.minDepth)
    (hmcl : mclr.length = c.mv) (hmcl_le : mcl ≤ c.mv)
    (hp2 : ∀ w < c.mv, s.mrk[w]?.getD 0#8 = 2#8 → mrk[w]?.getD 0#8 = 2#8)
    (hmin : MinMarkInv c (withMinFields s mrk mstk mclr mcl mcf) keepSet)
    (hf : MinFrameOk c s mrk mstk root_lit idx0 sp.toNat)
    (hsp1 : sp.toNat + 1 < c.minDepth) {rcid : BitVec 32}
    (hrsn : s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 = rcid)
    (hrne : rcid ≠ 0xFFFFFFFF#32)
    (hpos_eq : (mstk[2 * sp.toNat + 1]?.getD 0#32) = pos')
    (hpos_lt : pos'.toNat < clauseSize s rcid.toNat)
    (hu_eq : u = s.lpool[clauseOff s rcid.toNat + pos'.toNat]?.getD 0#32 >>> 1)
    (hu_lt : u.toNat < c.mv) (hne_v : u ≠ mstk[2 * sp.toNat]?.getD 0#32)
    (hn2 : (mrk[u.toNat]?.getD 0#8 &&& 2#8) = 0#8)
    (hn4 : (mrk[u.toNat]?.getD 0#8 &&& 4#8) = 0#8)
    (hur_eq : s.rsns[u.toNat]?.getD 0xFFFFFFFF#32 = ur)
    (hur1 : ur ≠ 0xFFFFFFFF#32) (hur2 : ur.toNat < s.num_clauses)
    (hm' : (CorePlusMem c (withMinFields s mrk
      (pushMinStk mstk sp.toNat pos'.toNat u) mclr mcl mcf) ⋆ R) m') :
    MinLitInv c s keepSet root_lit idx0 maxSteps (sp + 1#64, steps', ()) m' R := by
  have hm_z : mrk[u.toNat]?.getD 0#8 = 0#8 :=
    (mrk_dom_cases (hmin.mrk_dom u.toNat hu_lt)).2.2 hn2 hn4
  have hsp_eq : (sp + 1#64).toNat = sp.toNat + 1 := by
    have := hf.sp_lt; have := minDepthOf_le c.mv
    dsimp only [CorePlusCfg.minDepth] at *; simp [BitVec.toNat_add]; omega
  have hu32 : pos'.toNat + 1 < 2 ^ 32 := by
    obtain ⟨_, _, _, _, _, _, _, hrc2, _⟩ := hf.idx sp.toNat (le_refl _)
    rw [hrsn] at hrc2
    have := hcore.lengths.lit_len_le; have := hcore.clauses.bounds rcid.toNat hrc2
    have := c.hlcap; unfold dimacsBound at *; omega
  refine ⟨mrk, pushMinStk mstk sp.toNat pos'.toNat u, mclr, mcl, mcf, hst, hmrkl,
    pushMinStk_len hmstkl, hmcl, hmcl_le, hp2, minMarkInv_set_stk hmin _, ?_, hm'⟩
  rw [hsp_eq]
  refine minFrameOk_push hf hsp1 (congrArg BitVec.toNat hpos_eq) hu32 hu_lt (by rw [hm_z]; decide)
    hur_eq hur1 hur2 fun idx_sp hi htr => ?_
  dsimp only; rw [hrsn]
  have hrel := min_lit_child_rel hcore hi (by rw [htr]; exact hrsn) hrne hpos_lt
  rcases hrel with ⟨hd, _⟩ | ⟨_, k, hk, hkeq⟩
  · exfalso; apply hne_v; apply BitVec.eq_of_toNat_eq; rw [hu_eq, bv32_lshr_1, hd, htr]
  · exact ⟨by rw [hu_eq, bv32_lshr_1], k, hk, hkeq⟩

private theorem min_lit_poison_brk {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    {keepSet : List Nat} {root_lit : Nat}
    {mrk : List (BitVec 8)} {mstk mclr : List (BitVec 32)} {mcl : Nat} {mcf : BitVec 64}
    {mrk3 : List (BitVec 8)} {mclr3 : List (BitVec 32)} {mcl3 : Nat} {mcf3 : BitVec 64}
    {sp steps' : BitVec 64} {u : BitVec 32} {m3 : Mem 64} {R : Mem 64 → Prop}
    (hcore : CorePlusCoreInv c F0 (withMinFields s mrk mstk mclr mcl mcf))
    (hmin : MinMarkInv c (withMinFields s mrk mstk mclr mcl mcf) keepSet)
    (hsp : sp.toNat < c.minDepth) (hsl : mstk.length = 2 * c.minDepth)
    (hp2 : ∀ w < c.mv, s.mrk[w]?.getD 0#8 = 2#8 → mrk[w]?.getD 0#8 = 2#8)
    (hbr : if c.mv ≤ u.toNat ∨ mrk[u.toNat]?.getD 0#8 ≠ 0#8 then
        mrk3 = mrk ∧ mclr3 = mclr ∧ mcl3 = mcl ∧ mcf3 = mcf
      else let st' := minMarkState c (withMinFields s mrk mstk mclr mcl mcf) u.toNat 4#8
        mrk3 = st'.mrk ∧ mclr3 = st'.min_clr ∧ mcl3 = st'.min_clr_len ∧ mcf3 = st'.min_clr_full)
    (hm3 : (CorePlusMem c (withMinFields s mrk3 mstk mclr3 mcl3 mcf3) ⋆ R) m3) :
    MinLitBrk c s keepSet root_lit (sp, false, steps', ()) m3 R := by
  obtain ⟨hm3l, hc3l, hcl3, hp3, hmin3⟩ := minMark_poison_post hcore hmin u hbr
  exact ⟨mrk3, mstk, mclr3, mcl3, mcf3, hsp, hm3l, hsl, hc3l, hcl3,
    fun w hw h2 => hp3 w hw (hp2 w hw h2), hmin3, (fun h => by cases h), hm3⟩

private theorem min_lit_done_brk {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    {keepSet : List Nat} {root_lit idx0 : Nat}
    {mrk : List (BitVec 8)} {mstk mclr : List (BitVec 32)} {mcl : Nat} {mcf steps' : BitVec 64}
    {m' : Mem 64} {R : Mem 64 → Prop}
    (hcore : CorePlusCoreInv c F0 s) (hmrkl : mrk.length = c.mv)
    (hmstkl : mstk.length = 2 * c.minDepth) (hmcl : mclr.length = c.mv) (hmcl_le : mcl ≤ c.mv)
    (hp2 : ∀ w < c.mv, s.mrk[w]?.getD 0#8 = 2#8 → mrk[w]?.getD 0#8 = 2#8)
    (hmin : MinMarkInv c (withMinFields s mrk mstk mclr mcl mcf) keepSet)
    (hf : MinFrameOk c s mrk mstk root_lit idx0 0)
    (hroot : (s.trl[idx0]?.getD 0#32).toNat = root_lit ^^^ 1)
    (hdone : clauseSize s (s.rsns[(mstk[0]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat ≤
      (mstk[1]?.getD 0#32).toNat)
    (hm' : (CorePlusMem c (withMinFields s mrk mstk mclr mcl mcf) ⋆ R) m') :
    MinLitBrk c s keepSet root_lit (0#64, true, steps', ()) m' R := by
  have hcore' := hcore.of_minFields (mcf' := mcf) hmrkl hmstkl hmcl hmcl_le
  obtain ⟨idx_0, hidx_0, htr, hj0, _, hrc1, hrc2, hslots⟩ :=
    minFrameOk_top_done hcore hf (by simpa only [Nat.mul_zero, Nat.zero_add] using hdone)
  have hieq := hj0 rfl; subst idx0
  have hrsn : let p0 := root_lit ^^^ 1
      let rsn := s.rsns[p0 / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 ∧ rsn.toNat < s.num_clauses ∧
      ∀ q ∈ clauseLits s rsn.toNat, q = p0 ∨ ∃ k < idx_0, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 ∧
        ((s.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ mrk[q / 2]?.getD 0#8 = 2#8) := by
    dsimp only; rw [← hroot]; exact ⟨hrc1, hrc2, hslots⟩
  exact ⟨mrk, mstk, mclr, mcl, mcf, hf.sp_lt, hmrkl, hmstkl, hmcl, hmcl_le, hp2, hmin,
    fun _ keep' hsub => minMarkInv_drop hcore' hmin hsub hidx_0 hroot hrsn, hm'⟩

private theorem min_lit_pop_cont {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    {keepSet : List Nat} {root_lit idx0 maxSteps : Nat}
    {mrk : List (BitVec 8)} {mstk mclr : List (BitVec 32)} {mcl : Nat} {mcf : BitVec 64}
    {mrk3 : List (BitVec 8)} {mclr3 : List (BitVec 32)} {mcl3 : Nat} {mcf3 : BitVec 64}
    {sp steps' : BitVec 64} {m3 : Mem 64} {R : Mem 64 → Prop}
    (hcore : CorePlusCoreInv c F0 s) (hst : steps'.toNat ≤ maxSteps)
    (hmrkl : mrk.length = c.mv) (hmstkl : mstk.length = 2 * c.minDepth)
    (hmcl : mclr.length = c.mv) (hmcl_le : mcl ≤ c.mv)
    (hp2 : ∀ w < c.mv, s.mrk[w]?.getD 0#8 = 2#8 → mrk[w]?.getD 0#8 = 2#8)
    (hmin : MinMarkInv c (withMinFields s mrk mstk mclr mcl mcf) keepSet)
    (hf : MinFrameOk c s mrk mstk root_lit idx0 sp.toNat) (hsp : 0 < sp.toNat)
    (hdone : clauseSize s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat
      ≤ (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat)
    (hbr : if c.mv ≤ (mstk[2 * sp.toNat]?.getD 0#32).toNat ∨
          mrk[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD 0#8 ≠ 0#8 then
        mrk3 = mrk ∧ mclr3 = mclr ∧ mcl3 = mcl ∧ mcf3 = mcf
      else let st' := minMarkState c (withMinFields s mrk mstk mclr mcl mcf)
            ((mstk[2 * sp.toNat]?.getD 0#32).toNat) 2#8
        mrk3 = st'.mrk ∧ mclr3 = st'.min_clr ∧ mcl3 = st'.min_clr_len ∧ mcf3 = st'.min_clr_full)
    (hm3 : (CorePlusMem c (withMinFields s mrk3 mstk mclr3 mcl3 mcf3) ⋆ R) m3) :
    MinLitInv c s keepSet root_lit idx0 maxSteps (sp - 1#64, steps', ()) m3 R := by
  have hcore' := hcore.of_minFields (mcf' := mcf) hmrkl hmstkl hmcl hmcl_le
  obtain ⟨idx_sp, hidx_sp, htr, _, hn4, hrc1, hrc2, hslots⟩ := minFrameOk_top_done hcore hf hdone
  obtain ⟨hm3l, hc3l, hcl3, hm3_v, hp3, hp34, hmin3⟩ :=
    minMark_pop_post hcore' hmin hidx_sp _ htr hn4 ⟨hrc1, hrc2, hslots⟩ hbr
  have hsp_sub : (sp - 1#64).toNat = sp.toNat - 1 := by simp [BitVec.toNat_sub]; omega
  refine ⟨mrk3, mstk, mclr3, mcl3, mcf3, hst, hm3l, hmstkl, hc3l, hcl3,
    fun w hw h2 => hp3 w hw (hp2 w hw h2), hmin3, ?_, hm3⟩
  rw [hsp_sub]; exact minFrameOk_pop hcore hf hsp hm3l hp3 hp34 hm3_v

private theorem min_stk_rsn_cls_eq {s : CorePlusState} {mstk : List (BitVec 32)} {sp : BitVec 64}
    {i0 i1 : Nat} (hi0 : i0 = 2 * sp.toNat) (hi1 : i1 = 2 * sp.toNat + 1) (off : Nat)
    {hp hv hr hc} :
    mstk[i1]'hp = mstk[2 * sp.toNat + 1]?.getD 0#32 ∧
    s.cls[4 * ((s.rsns[(mstk[i0]'hv).toNat % 2 ^ 64]'hr).toNat % 2 ^ 64) + off]'hc =
      s.cls[4 * (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD
        0xFFFFFFFF#32).toNat + off]?.getD 0#32 := by
  have h1 : mstk[i1]'hp = mstk[2 * sp.toNat + 1]?.getD 0#32 := bv_get_eq hp hi1
  have h2 : (mstk[i0]'hv).toNat % 2 ^ 64 = (mstk[2 * sp.toNat]?.getD 0#32).toNat := by
    rw [bv_get_eq hv hi0, min_bv32_mod64]
  have h3 : s.rsns[(mstk[i0]'hv).toNat % 2 ^ 64]'hr =
      s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 := bv_get_eq hr h2
  exact ⟨h1, bv_get_eq hc (by rw [h3, min_bv32_mod64])⟩

private theorem min_pos_lt_clauseSize {s : CorePlusState} {mstk : List (BitVec 32)} {sp : BitVec 64}
    {i0 i1 : Nat} {hp hv hr hc}
    (hlt : (mstk[i1]'hp).toNat % 2 ^ 64 <
      (s.cls[4 * ((s.rsns[(mstk[i0]'hv).toNat % 2 ^ 64]'hr).toNat % 2 ^ 64) +
        1]'hc).toNat % 2 ^ 64)
    (hi0 : i0 = 2 * sp.toNat) (hi1 : i1 = 2 * sp.toNat + 1) :
    (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat <
      clauseSize s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat := by
  obtain ⟨h1, h4⟩ := min_stk_rsn_cls_eq hi0 hi1 1 (hr := hr) (hc := hc)
  rw [h1, min_bv32_mod64, h4, min_bv32_mod64] at hlt; exact hlt

private theorem min_pos_ge_clauseSize {s : CorePlusState} {mstk : List (BitVec 32)} {sp : BitVec 64}
    {i0 i1 : Nat} {hp hv hr hc}
    (hnlt : ¬ (mstk[i1]'hp).toNat % 2 ^ 64 <
      (s.cls[4 * ((s.rsns[(mstk[i0]'hv).toNat % 2 ^ 64]'hr).toNat % 2 ^ 64) +
        1]'hc).toNat % 2 ^ 64)
    (hi0 : i0 = 2 * sp.toNat) (hi1 : i1 = 2 * sp.toNat + 1) :
    clauseSize s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat ≤
      (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat := by
  obtain ⟨h1, h4⟩ := min_stk_rsn_cls_eq hi0 hi1 1 (hr := hr) (hc := hc)
  rw [h1, min_bv32_mod64, h4, min_bv32_mod64] at hnlt; exact Nat.le_of_not_lt hnlt

private theorem min_lpool_q_eq {s : CorePlusState} {mstk : List (BitVec 32)} {sp : BitVec 64}
    {i0 i1 : Nat} (hi0 : i0 = 2 * sp.toNat) (hi1 : i1 = 2 * sp.toNat + 1) {hv hr hco hp hlp}
    (hlp_lt : clauseOff s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD
        0xFFFFFFFF#32).toNat + (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat < 2 ^ 64) :
    s.lpool[((s.cls[4 * ((s.rsns[(mstk[i0]'hv).toNat % 2 ^ 64]'hr).toNat % 2 ^ 64)]'hco).toNat +
      (mstk[i1]'hp).toNat) % 2 ^ 64]'hlp =
    s.lpool[clauseOff s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat
      + (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat]?.getD 0#32 := by
  obtain ⟨h1, h4⟩ := min_stk_rsn_cls_eq hi0 hi1 0 (hr := hr) (hc := hco)
  simp only [Nat.add_zero] at h4
  exact bv_get_eq hlp (by rw [h1, h4]; exact Nat.mod_eq_of_lt hlp_lt)

private theorem min_lpool_q_hm {s : CorePlusState} {mstk : List (BitVec 32)} {sp : BitVec 64}
    (hs0 : (sp <<< 1).toNat = 2 * sp.toNat) (hs1 : (sp <<< 1 + 1).toNat = 2 * sp.toNat + 1)
    {hv hr hco hp hlp}
    (hlp_lt : clauseOff s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD
        0xFFFFFFFF#32).toNat + (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat < 2 ^ 64) :
    s.lpool[(BitVec.setWidth 64 (s.cls[4 * (BitVec.setWidth 64
        (s.rsns[(BitVec.setWidth 64 (mstk[(sp <<< 1).toNat]'hv)).toNat]'hr)).toNat]'hco) +
      BitVec.setWidth 64 (mstk[(sp <<< 1 + 1).toNat]'hp)).toNat]'hlp =
    s.lpool[clauseOff s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat
      + (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat]?.getD 0#32 := by
  have h1 : mstk[(sp <<< 1 + 1).toNat]'hp = mstk[2 * sp.toNat + 1]?.getD 0#32 := bv_get_eq hp hs1
  have h2 : (BitVec.setWidth 64 (mstk[(sp <<< 1).toNat]'hv)).toNat =
      (mstk[2 * sp.toNat]?.getD 0#32).toNat := by
    rw [bv32_zext64_eq, BitVec.toNat_ofNat, min_bv32_mod64, bv_get_eq hv hs0]
  have h3 : s.rsns[(BitVec.setWidth 64 (mstk[(sp <<< 1).toNat]'hv)).toNat]'hr =
      s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 := bv_get_eq hr h2
  have h4 : (BitVec.setWidth 64 (s.cls[4 * (BitVec.setWidth 64
      (s.rsns[(BitVec.setWidth 64 (mstk[(sp <<< 1).toNat]'hv)).toNat]'hr)).toNat]'hco)).toNat =
      clauseOff s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD
        0xFFFFFFFF#32).toNat := by
    rw [bv32_zext64_eq, BitVec.toNat_ofNat, min_bv32_mod64]
    have hi : 4 * (BitVec.setWidth 64 (s.rsns[(BitVec.setWidth 64
        (mstk[(sp <<< 1).toNat]'hv)).toNat]'hr)).toNat =
        4 * (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat := by
      rw [bv32_zext64_eq, BitVec.toNat_ofNat, min_bv32_mod64, h3]
    exact congrArg BitVec.toNat (bv_get_eq hco hi)
  refine bv_get_eq hlp ?_
  rw [BitVec.toNat_add, h1, h4]; exact Nat.mod_eq_of_lt hlp_lt

private theorem min_lpool_u_eq {s : CorePlusState} {mstk : List (BitVec 32)} {sp : BitVec 64}
    {i0 i1 : Nat} (hi0 : i0 = 2 * sp.toNat) (hi1 : i1 = 2 * sp.toNat + 1) {hv hr hco hp hlp}
    (hlp_lt : clauseOff s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD
        0xFFFFFFFF#32).toNat + (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat < 2 ^ 64) :
    (s.lpool[((s.cls[4 * ((s.rsns[(mstk[i0]'hv).toNat % 2 ^ 64]'hr).toNat % 2 ^ 64)]'hco).toNat +
      (mstk[i1]'hp).toNat) % 2 ^ 64]'hlp).toNat / 2 % 2 ^ 64 =
    (s.lpool[clauseOff s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat
      + (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat]?.getD 0#32).toNat / 2 := by
  rw [min_lpool_q_eq hi0 hi1 hlp_lt]
  exact Nat.mod_eq_of_lt
    (Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.div_le_self _ 2) (BitVec.isLt _)) (by decide))

private theorem min_mrk_u_eq {s : CorePlusState} {mrk : List (BitVec 8)}
    {mstk : List (BitVec 32)} {sp : BitVec 64} {i0 i1 : Nat}
    (hi0 : i0 = 2 * sp.toNat) (hi1 : i1 = 2 * sp.toNat + 1) {hv hr hco hp hlp hm}
    (hlp_lt : clauseOff s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD
        0xFFFFFFFF#32).toNat + (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat < 2 ^ 64) :
    mrk[(s.lpool[((s.cls[4 * ((s.rsns[(mstk[i0]'hv).toNat % 2 ^ 64]'hr).toNat %
        2 ^ 64)]'hco).toNat + (mstk[i1]'hp).toNat) % 2 ^ 64]'hlp).toNat / 2 % 2 ^ 64]'hm =
    mrk[(s.lpool[clauseOff s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD
        0xFFFFFFFF#32).toNat + (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat]?.getD
        0#32).toNat / 2]?.getD 0#8 :=
  bv_get_eq hm (min_lpool_u_eq hi0 hi1 hlp_lt)

private theorem min_u_lt_mv_of {c : CorePlusCfg} {s : CorePlusState} {mstk : List (BitVec 32)}
    {sp : BitVec 64} {i0 i1 : Nat} {hv hr hco hp hlp}
    (hi0 : i0 = 2 * sp.toNat) (hi1 : i1 = 2 * sp.toNat + 1)
    (hlp_lt : clauseOff s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD
        0xFFFFFFFF#32).toNat + (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat < 2 ^ 64)
    (hmv : c.mv < 2 ^ 64)
    (hn : ¬c.mv % 2 ^ 64 ≤ (s.lpool[((s.cls[4 * ((s.rsns[(mstk[i0]'hv).toNat %
        2 ^ 64]'hr).toNat % 2 ^ 64)]'hco).toNat + (mstk[i1]'hp).toNat) %
        2 ^ 64]'hlp).toNat / 2 % 2 ^ 64) :
    (s.lpool[clauseOff s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD
        0xFFFFFFFF#32).toNat + (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat]?.getD
        0#32).toNat / 2 < c.mv := by
  rw [min_lpool_u_eq hi0 hi1 hlp_lt, Nat.mod_eq_of_lt hmv] at hn; omega

private theorem min_ur_ne_of {s : CorePlusState} {mstk : List (BitVec 32)} {sp : BitVec 64}
    {i0 i1 : Nat} {hv hr hco hp hlp hrs}
    (hi0 : i0 = 2 * sp.toNat) (hi1 : i1 = 2 * sp.toNat + 1)
    (hlp_lt : clauseOff s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD
        0xFFFFFFFF#32).toNat + (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat < 2 ^ 64)
    (hn : ¬s.rsns[(s.lpool[((s.cls[4 * ((s.rsns[(mstk[i0]'hv).toNat % 2 ^ 64]'hr).toNat %
        2 ^ 64)]'hco).toNat + (mstk[i1]'hp).toNat) % 2 ^ 64]'hlp).toNat / 2 % 2 ^ 64]'hrs =
        0xFFFFFFFF#32) :
    s.rsns[(s.lpool[clauseOff s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD
        0xFFFFFFFF#32).toNat + (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat]?.getD
        0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
  rwa [bv_get_eq (d := 0xFFFFFFFF#32) hrs (min_lpool_u_eq hi0 hi1 hlp_lt)] at hn

private theorem min_ur_lt_of {s : CorePlusState} {mstk : List (BitVec 32)} {sp : BitVec 64}
    {i0 i1 : Nat} {hv hr hco hp hlp hrs}
    (hi0 : i0 = 2 * sp.toNat) (hi1 : i1 = 2 * sp.toNat + 1)
    (hlp_lt : clauseOff s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD
        0xFFFFFFFF#32).toNat + (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat < 2 ^ 64)
    (hnc : s.num_clauses < 2 ^ 64)
    (hn : ¬s.num_clauses % 2 ^ 64 ≤ (s.rsns[(s.lpool[((s.cls[4 * ((s.rsns[(mstk[i0]'hv).toNat %
        2 ^ 64]'hr).toNat % 2 ^ 64)]'hco).toNat + (mstk[i1]'hp).toNat) %
        2 ^ 64]'hlp).toNat / 2 % 2 ^ 64]'hrs).toNat % 2 ^ 64) :
    (s.rsns[(s.lpool[clauseOff s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD
        0xFFFFFFFF#32).toNat + (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat]?.getD
        0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat < s.num_clauses := by
  rw [bv_get_eq (d := 0xFFFFFFFF#32) hrs (min_lpool_u_eq hi0 hi1 hlp_lt),
    min_bv32_mod64, Nat.mod_eq_of_lt hnc] at hn
  omega

private theorem min_steps_lt {lit_len mv maxSteps : Nat} {steps : BitVec 64}
    (hmax : maxSteps = (lit_len + mv) * 4 + 64) (hlt : maxSteps < 2 ^ 64)
    (hsum : lit_len + mv < 2 ^ 64)
    (hc : steps.toNat < ((lit_len + mv) % 2 ^ 64 * 4 + 64) % 2 ^ 64) :
    (steps + 1).toNat ≤ maxSteps ∧ maxSteps - (steps + 1).toNat < maxSteps - steps.toNat := by
  rw [Nat.mod_eq_of_lt hsum, ← hmax, Nat.mod_eq_of_lt hlt] at hc
  have h1 : (steps + 1).toNat = steps.toNat + 1 := by
    rw [BitVec.toNat_add, bv64_toNat_one, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem min_lit_skip_leaf {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    {keepSet : List Nat} {root_lit idx0 maxSteps i0 i1 : Nat}
    {mrk : List (BitVec 8)} {mstk mclr : List (BitVec 32)} {mcl : Nat} {mcf : BitVec 64}
    {sp steps steps' : BitVec 64} {m' : Mem 64} {R : Mem 64 → Prop} {L : Cont [i64, i64]}
    (hcore : CorePlusCoreInv c F0 s) (hmax : maxSteps = (s.lit_len + c.mv) * 4 + 64)
    (hlt : maxSteps < 2 ^ 64) (hsum : s.lit_len + c.mv < 2 ^ 64)
    (hc_st : steps.toNat < ((s.lit_len + c.mv) % 2 ^ 64 * 4 + 64) % 2 ^ 64)
    (hmrkl : mrk.length = c.mv) (hmstkl : mstk.length = 2 * c.minDepth)
    (hmcl : mclr.length = c.mv) (hmcl_le : mcl ≤ c.mv)
    (hp2 : ∀ w < c.mv, s.mrk[w]?.getD 0#8 = 2#8 → mrk[w]?.getD 0#8 = 2#8)
    (hmin : MinMarkInv c (withMinFields s mrk mstk mclr mcl mcf) keepSet)
    (hf : MinFrameOk c s mrk mstk root_lit idx0 sp.toNat)
    (hshl1 : ((sp <<< 1) + 1).toNat = 2 * sp.toNat + 1)
    (ih : ∀ ys m', maxSteps - ys.2.1.toNat < maxSteps - steps.toNat →
      MinLitInv c s keepSet root_lit idx0 maxSteps ys m' R → L ys m')
    (hrc1 : s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (_hrc2 : (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat <
      s.num_clauses)
    {hp hv hr hc_s hp'}
    (hc_pos : (mstk[i1]'hp).toNat % 2 ^ 64 <
      (s.cls[4 * ((s.rsns[(mstk[i0]'hv).toNat % 2 ^ 64]'hr).toNat % 2 ^ 64) +
        1]'hc_s).toNat % 2 ^ 64)
    (hi0 : i0 = 2 * sp.toNat) (hi1 : i1 = 2 * sp.toNat + 1) (hsteps_eq : steps' = steps + 1)
    (hcond : let rcid := s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32
      let q := (s.lpool[clauseOff s rcid.toNat + (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat]?.getD
        0#32).toNat
      q / 2 = (mstk[2 * sp.toNat]?.getD 0#32).toNat ∨
      (s.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ mrk[q / 2]?.getD 0#8 = 2#8)
    (hm' : (CorePlusMem c (withMinFields s mrk
      (mstk.set (sp <<< 1 + 1).toNat (mstk[(sp <<< 1 + 1).toNat]'hp' + 1#32)) mclr mcl mcf)
      ⋆ R) m') :
    L (sp, steps', ()) m' := by
  have hpos_lt := min_pos_lt_clauseSize hc_pos hi0 hi1
  have ⟨hst1, hst2⟩ := min_steps_lt hmax hlt hsum hc_st
  subst hsteps_eq
  refine ih _ _ hst2 (min_lit_skip_cont hcore hst1 hmrkl hmstkl hmcl hmcl_le
    hp2 hmin hf rfl hrc1 hpos_lt (pos' := mstk[2 * sp.toNat + 1]?.getD 0#32) rfl hcond ?_)
  rwa [bv_get_eq hp' hshl1, hshl1] at hm'

private theorem min_lit_ur_poison {Γ : Env}
    (hMm : ∀ a m Q X, corePlusMinMarkSpec a m Q X →
      Γ "kissat_min_mark" [i64, i32, i8] [] a m Q X)
    {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState} {keepSet : List Nat}
    {root_lit : Nat} {Q : Post [Ty.bool]} {X : XPost} {R : Mem 64 → Prop}
    {mrk : List (BitVec 8)} {mstk mclr : List (BitVec 32)} {mcl : Nat} {mcf sp steps : BitVec 64}
    {m : Mem 64} {J' : Cont [i64, .bool, i64]}
    (hcore : CorePlusCoreInv c F0 (withMinFields s mrk mstk mclr mcl mcf))
    (hmin : MinMarkInv c (withMinFields s mrk mstk mclr mcl mcf) keepSet)
    (hsp : sp.toNat < c.minDepth) (hsl : mstk.length = 2 * c.minDepth)
    (hp2 : ∀ w < c.mv, s.mrk[w]?.getD 0#8 = 2#8 → mrk[w]?.getD 0#8 = 2#8)
    (hBrk : ∀ r mr, MinLitBrk c s keepSet root_lit r mr R → J' r mr)
    (u : BitVec 32)
    (hm : (CorePlusMem c (withMinFields s mrk mstk mclr mcl mcf) ⋆ R) m) :
    wp Γ Q X
      (Expr.call (as := [i64, i32, i8]) (bs := []) "kissat_min_mark"
        (Arg.var c.hdr, Arg.var u, Arg.var 4#8, ())
        fun _ => Expr.jump J' (Arg.var sp, Arg.imm false, Arg.var (steps + 1), ())) m :=
  LeanQbe.T.wp_call_of_spec _ _
    (minMark_wp_of_spec hMm u 4#8 hcore.lengths hm fun mrk3 mclr3 mcl3 mcf3 m3 hbr hm3 => by
      simp only [LeanQbe.T.wp_jump, LeanQbe.T.vals_cons, LeanQbe.T.vals_nil,
        LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]
      exact hBrk _ _ (min_lit_poison_brk hcore hmin hsp hsl hp2 hbr hm3))

private theorem pushMinStk_eq_bv {mstk : List (BitVec 32)} {sp : BitVec 64}
    {hp_idx : (sp <<< 1 + 1).toNat < mstk.length} {u : BitVec 32}
    (hs1 : (sp <<< 1 + 1).toNat = 2 * sp.toNat + 1)
    (hpush0 : ((sp + 1) <<< 1).toNat = 2 * (sp.toNat + 1))
    (hpush1 : (((sp + 1) <<< 1) + 1).toNat = 2 * (sp.toNat + 1) + 1)
    (hu32 : (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat + 1 < 2 ^ 32) :
    (((mstk.set (sp <<< 1 + 1).toNat (mstk[(sp <<< 1 + 1).toNat]'hp_idx + 1)).set
        ((sp + 1) <<< 1).toNat u).set (((sp + 1) <<< 1) + 1).toNat 0) =
      pushMinStk mstk sp.toNat (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat u := by
  unfold pushMinStk
  rw [bv_get_eq hp_idx hs1, hs1, hpush0, hpush1]
  have hinc : (mstk[2 * sp.toNat + 1]?.getD 0#32) + 1 =
      BitVec.ofNat 32 ((mstk[2 * sp.toNat + 1]?.getD 0#32).toNat + 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, bv32_toNat_one, bv32_ofNat_toNat hu32, Nat.mod_eq_of_lt hu32]
  rw [hinc]; rfl

private theorem min_lit_step_push {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    {keepSet : List Nat} {root_lit idx0 maxSteps : Nat}
    {mrk : List (BitVec 8)} {mstk mclr : List (BitVec 32)} {mcl : Nat} {mcf sp steps : BitVec 64}
    {m : Mem 64} {R : Mem 64 → Prop} {L : Cont [i64, i64]}
    (hcore : CorePlusCoreInv c F0 s) (hmax_lt : maxSteps < 2 ^ 64)
    (hmax_sum : s.lit_len + c.mv < 2 ^ 64)
    (hmax : maxSteps = (s.lit_len + c.mv) * 4 + 64)
    (hst_c : steps.toNat < ((s.lit_len + c.mv) % 2 ^ 64 * 4 + 64) % 2 ^ 64)
    (hmrkl : mrk.length = c.mv) (hmstkl' : mstk.length = 2 * c.minDepth)
    (hmcl : mclr.length = c.mv) (hmcl_le : mcl ≤ c.mv)
    (hp2 : ∀ w < c.mv, s.mrk[w]?.getD 0#8 = 2#8 → mrk[w]?.getD 0#8 = 2#8)
    (hmin_cur : MinMarkInv c (withMinFields s mrk mstk mclr mcl mcf) keepSet)
    (hf : MinFrameOk c s mrk mstk root_lit idx0 sp.toNat)
    (hshl0 : (sp <<< 1).toNat = 2 * sp.toNat)
    (hshl1 : (sp <<< 1 + 1).toNat = 2 * sp.toNat + 1)
    {hv hr hco hp hlp}
    (hrc1_c : s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hpos_lt : (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat <
      clauseSize s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat)
    (hlp_p : clauseOff s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD
        0xFFFFFFFF#32).toNat + (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat < 2 ^ 64)
    (hu_lt : (s.lpool[clauseOff s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD
        0xFFFFFFFF#32).toNat + (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat]?.getD
        0#32).toNat / 2 < c.mv)
    (hm_z : mrk[(s.lpool[clauseOff s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD
        0xFFFFFFFF#32).toNat + (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat]?.getD
        0#32).toNat / 2]?.getD 0#8 = 0#8)
    (hne_v : s.lpool[clauseOff s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD
        0xFFFFFFFF#32).toNat + (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat]?.getD 0#32 >>> 1 ≠
      mstk[2 * sp.toNat]?.getD 0#32)
    (hsp1_lt : sp.toNat + 1 < c.minDepth)
    (hur_ne : s.rsns[(s.lpool[clauseOff s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD
        0xFFFFFFFF#32).toNat + (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat]?.getD
        0#32 >>> 1).toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hur_lt : (s.rsns[(s.lpool[clauseOff s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD
        0xFFFFFFFF#32).toNat + (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat]?.getD
        0#32 >>> 1).toNat]?.getD 0xFFFFFFFF#32).toNat < s.num_clauses)
    (ih : ∀ ys m', maxSteps - ys.2.1.toNat < maxSteps - steps.toNat →
      MinLitInv c s keepSet root_lit idx0 maxSteps ys m' R → L ys m')
    (hu32 : (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat + 1 < 2 ^ 32)
    (hm : (CorePlusMem c (withMinFields s mrk
      (((mstk.set (sp <<< 1 + 1).toNat (mstk[(sp <<< 1 + 1).toNat]'hp + 1)).set
        ((sp + 1) <<< 1).toNat
        (s.lpool[(BitVec.setWidth 64 (s.cls[4 * (BitVec.setWidth 64
          (s.rsns[(BitVec.setWidth 64 (mstk[(sp <<< 1).toNat]'hv)).toNat]'hr)).toNat]'hco) +
          BitVec.setWidth 64 (mstk[(sp <<< 1 + 1).toNat]'hp)).toNat]'hlp >>> 1)).set
        ((sp + 1) <<< 1 + 1).toNat 0)
      mclr mcl mcf) ⋆ R) m) :
    L (sp + 1, steps + 1, ()) m := by
  have hsp1_bd : sp.toNat + 1 < 1000 := lt_of_lt_of_le hsp1_lt (minDepthOf_le c.mv)
  have hpush0_eq : ((sp + 1) <<< 1).toNat = 2 * (sp.toNat + 1) := by
    have hsp_lt_bd : sp.toNat + 1 < 2 ^ 64 := lt_trans hsp1_bd (by decide)
    have h1 : (sp + 1).toNat = sp.toNat + 1 := by
      rw [BitVec.toNat_add, bv64_toNat_one, Nat.mod_eq_of_lt hsp_lt_bd]
    rw [bv64_shl_nat1, h1, Nat.mod_eq_of_lt (lt_trans (Nat.mul_lt_mul_of_pos_left hsp1_bd
      (by decide)) (by decide))]
  have hpush1_eq : (((sp + 1) <<< 1) + 1).toNat = 2 * (sp.toNat + 1) + 1 := by
    rw [BitVec.toNat_add, bv64_toNat_one, hpush0_eq,
      Nat.mod_eq_of_lt (lt_trans (Nat.succ_lt_succ (Nat.mul_lt_mul_of_pos_left hsp1_bd
        (by decide))) (by decide))]
  have ⟨hst1, hst2⟩ := min_steps_lt hmax hmax_lt hmax_sum hst_c
  rw [min_lpool_q_hm hshl0 hshl1 hlp_p] at hm
  have hpush_stk := pushMinStk_eq_bv (hp_idx := hp) (u := s.lpool[clauseOff s
    (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat +
    (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat]?.getD 0#32 >>> 1)
    hshl1 hpush0_eq hpush1_eq hu32
  rw [hpush_stk] at hm
  exact ih _ _ hst2 (min_lit_push_cont hcore hst1 hmrkl hmstkl' hmcl hmcl_le hp2
    hmin_cur hf hsp1_lt rfl hrc1_c rfl hpos_lt rfl (by rwa [bv32_lshr_1]) hne_v
    (by rw [bv32_lshr_1, hm_z]; decide) (by rw [bv32_lshr_1, hm_z]; decide) rfl hur_ne hur_lt hm)

private theorem min_lp_lt {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    {mstk : List (BitVec 32)} {sp : BitVec 64}
    (hcore : CorePlusCoreInv c F0 s)
    (hrc2 : (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat <
      s.num_clauses)
    (hpos : (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat <
      clauseSize s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat) :
    clauseOff s (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat +
      (mstk[2 * sp.toNat + 1]?.getD 0#32).toNat < 2 ^ 64 := by
  have := hcore.lengths.lit_len_le
  have := hcore.clauses.bounds _ hrc2
  have := c.hlcap; unfold dimacsBound at *; omega

private theorem min_lit_ur_step {Γ : Env}
    (hMm : ∀ a m Q X, corePlusMinMarkSpec a m Q X →
      Γ "kissat_min_mark" [i64, i32, i8] [] a m Q X)
    {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState} {keepSet : List Nat}
    {root_lit idx0 i0 i1 : Nat} {Q : Post [Ty.bool]} {X : XPost} {R : Mem 64 → Prop}
    {mrk : List (BitVec 8)} {mstk mclr : List (BitVec 32)} {mcl : Nat} {mcf sp steps : BitVec 64}
    {m : Mem 64} {J' : Cont [i64, .bool, i64]}
    (hcore : CorePlusCoreInv c F0 s)
    (hmrkl : mrk.length = c.mv) (hmstkl' : mstk.length = 2 * c.minDepth)
    (hmcl : mclr.length = c.mv) (hmcl_le : mcl ≤ c.mv)
    (hp2 : ∀ w < c.mv, s.mrk[w]?.getD 0#8 = 2#8 → mrk[w]?.getD 0#8 = 2#8)
    (hmin_cur : MinMarkInv c (withMinFields s mrk mstk mclr mcl mcf) keepSet)
    (hf : MinFrameOk c s mrk mstk root_lit idx0 sp.toNat)
    (hshl0 : (sp <<< 1).toNat = 2 * sp.toNat)
    (hshl1 : (sp <<< 1 + 1).toNat = 2 * sp.toNat + 1)
    {hp hv hr hco hp' hv2 hr2 hco2 hp2' hlp}
    (hc_pos : (mstk[i1]'hp).toNat % 2 ^ 64 <
      (s.cls[4 * ((s.rsns[(mstk[i0]'hv).toNat % 2 ^ 64]'hr).toNat % 2 ^ 64) +
        1]'hco).toNat % 2 ^ 64)
    (hrc2 : (s.rsns[(mstk[2 * sp.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat <
      s.num_clauses)
    (hi0 : i0 = 2 * sp.toNat) (hi1 : i1 = 2 * sp.toNat + 1)
    (hBrk : ∀ r mr, MinLitBrk c s keepSet root_lit r mr R → J' r mr)
    (hm : (CorePlusMem c (withMinFields s mrk
      (mstk.set (sp <<< 1 + 1).toNat (mstk[(sp <<< 1 + 1).toNat]'hp' + 1)) mclr mcl mcf)
      ⋆ R) m) :
    wp Γ Q X
      (Expr.call (as := [i64, i32, i8]) (bs := []) "kissat_min_mark"
        (Arg.var c.hdr,
         Arg.var (s.lpool[(BitVec.setWidth 64 (s.cls[4 * (BitVec.setWidth 64
           (s.rsns[(BitVec.setWidth 64 (mstk[(sp <<< 1).toNat]'hv2)).toNat]'hr2)).toNat]'hco2) +
           BitVec.setWidth 64 (mstk[(sp <<< 1 + 1).toNat]'hp2')).toNat]'hlp >>> 1),
         Arg.var 4#8, ())
        fun _ => Expr.jump J' (Arg.var sp, Arg.imm false, Arg.var (steps + 1), ())) m := by
  have hm_len1 : (mstk.set (sp <<< 1 + 1).toNat
      (mstk[(sp <<< 1 + 1).toNat] + 1)).length = 2 * c.minDepth := by simp [hmstkl']
  have hpos_lt := min_pos_lt_clauseSize hc_pos hi0 hi1
  have hlp_p := min_lp_lt hcore hrc2 hpos_lt
  cp_let_simp; rw [min_lpool_q_hm hshl0 hshl1 hlp_p]
  exact min_lit_ur_poison hMm (hcore.of_minFields (mcf' := mcf) hmrkl hm_len1 hmcl hmcl_le)
    (minMarkInv_set_stk hmin_cur _) hf.sp_lt hm_len1 hp2 hBrk _ hm

private theorem min_lit_entry_rsn {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    {root_lit : BitVec 32} {hr1 hr2} (hcore : CorePlusCoreInv c F0 s)
    (hrl_lt : root_lit.toNat / 2 < c.mv)
    (h1 : s.rsns[root_lit.toNat / 2 % 2 ^ 64]'hr1 ≠ 0xFFFFFFFF#32)
    (h2 : ¬s.num_clauses % 2 ^ 64 ≤ (s.rsns[root_lit.toNat / 2 % 2 ^ 64]'hr2).toNat % 2 ^ 64) :
    s.rsns[root_lit.toNat / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
      (s.rsns[root_lit.toNat / 2]?.getD 0xFFFFFFFF#32).toNat < s.num_clauses := by
  have hmv := c.hmv; have hmaxc := c.hmax_c; have hnc := hcore.lengths.num_clauses_le
  unfold dimacsBound at *
  have hidx : root_lit.toNat / 2 < s.rsns.length := by rw [hcore.lengths.rsns_len]; exact hrl_lt
  have hmod : root_lit.toNat / 2 % 2 ^ 64 = root_lit.toNat / 2 := Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, ?_⟩
  · rw [List.getElem?_eq_getElem hidx, Option.getD_some]; simpa only [hmod] using h1
  · rw [List.getElem?_eq_getElem hidx, Option.getD_some]
    simp only [hmod] at h2; have := (s.rsns[root_lit.toNat / 2]'hidx).isLt; omega

private theorem min_lit_brk_pos {c : CorePlusCfg} {s : CorePlusState} {keepSet : List Nat}
    {root_lit : Nat} {mrk : List (BitVec 8)} {mstk mclr : List (BitVec 32)}
    {mcl : Nat} {mcf sp steps' : BitVec 64} {pos' : BitVec 32}
    {m : Mem 64} {R : Mem 64 → Prop} {J : Cont [i64, .bool, i64]}
    (hBrk : ∀ r mr, MinLitBrk c s keepSet root_lit r mr R → J r mr)
    (hsp : sp.toNat < c.minDepth) (hml : mrk.length = c.mv)
    (hsl : mstk.length = 2 * c.minDepth) (hcl : mclr.length = c.mv) (hcle : mcl ≤ c.mv)
    (hp2 : ∀ w < c.mv, s.mrk[w]?.getD 0#8 = 2#8 → mrk[w]?.getD 0#8 = 2#8)
    (hmin : MinMarkInv c (withMinFields s mrk mstk mclr mcl mcf) keepSet)
    (hshl1 : (sp <<< 1 + 1).toNat = 2 * sp.toNat + 1)
    (hm : (CorePlusMem c (withMinFields s mrk
      (mstk.set (sp <<< 1 + 1).toNat pos') mclr mcl mcf) ⋆ R) m) :
    J (sp, false, steps', ()) m :=
  hBrk _ _ (MinLitInv.to_brk_false_pos hsp hml hsl hcl hcle hp2 hmin (by rwa [← hshl1]))

private theorem min_lit_post_wp {Γ : Env}
    (hMm : ∀ a m Q X, corePlusMinMarkSpec a m Q X →
      Γ "kissat_min_mark" [i64, i32, i8] [] a m Q X)
    {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState} {keepSet : List Nat}
    {root_lit : Val i32} {R : Mem 64 → Prop} {Q : Post [Ty.bool]} {X : XPost}
    (hcore : CorePlusCoreInv c F0 s)
    (hQ : ∀ ok mrk' mstk' mclr' mcl' mcf' m',
      let s' : CorePlusState := withMinFields s mrk' mstk' mclr' mcl' mcf'
      s'.LengthsOk c → (∀ v < c.mv, s.mrk[v]?.getD 0#8 = 2#8 → mrk'[v]?.getD 0#8 = 2#8) →
      MinMarkInv c s' keepSet →
      (ok = true → ∀ keep' : List Nat,
        (∀ l ∈ keepSet, l = root_lit.toNat ∨ l ∈ keep') → MinMarkInv c s' keep') →
      (CorePlusMem c s' ⋆ R) m' → Q (ok, ()) m')
    {sp : BitVec 64} {ok : Bool} {steps : BitVec 64} {mr : Mem 64}
    (hbrk : MinLitBrk c s keepSet root_lit.toNat (sp, ok, steps, ()) mr R) :
    wp Γ Q X
      (Expr.jnz (Arg.imm ok)
        (Expr.ret (Arg.imm true, ()))
        (Expr.group (sig := [[i64]])
          (fun Js =>
            Blocks.cons
              (fun p =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.cmp CmpOp.ule i64 Ty.bool (by decide),
                    args := (Arg.var p.1, Arg.var sp, ()) }
                  fun p_1 =>
                  Expr.jnz (Arg.var p_1.1)
                    (Expr.let_
                      { sig := [i32], code := OpCode.sext 32 64,
                        args := (Arg.imm 1, ()) } fun p_2 =>
                      Expr.let_
                        { sig := [i64, i64], code := OpCode.shl i64,
                          args := (Arg.var p.1, Arg.var p_2.1, ()) } fun p_3 =>
                        Expr.let_
                          { sig := [i64, i64], code := OpCode.mul i64,
                            args := (Arg.var p_3.1, Arg.imm 4, ()) } fun p_4 =>
                          Expr.let_
                            { sig := [i64, i64], code := OpCode.add i64,
                              args := (Arg.var c.pMinStk, Arg.var p_4.1, ()) } fun p_5 =>
                            Expr.load i32 (Arg.var p_5.1) fun ld =>
                              Expr.let_
                                { sig := [i32], code := OpCode.trunc 32 8,
                                  args := (Arg.imm 4, ()) } fun p_6 =>
                                Expr.call (as := [i64, i32, i8]) (bs := []) "kissat_min_mark"
                                  (Arg.var c.hdr, Arg.var ld, Arg.var p_6.1, ()) fun _ =>
                                  Expr.let_
                                    { sig := [i64, i64], code := OpCode.add i64,
                                      args := (Arg.var p.1, Arg.imm 1, ()) } fun p =>
                                    Expr.jump Js.1 (Arg.var p.1, ()))
                    (Expr.ret (Arg.imm false, ())))
              Blocks.nil)
          fun Js => Expr.jump Js.1 (Arg.imm 1#64, ()))) mr := by
  obtain ⟨brk_mrk, brk_mstk, brk_mclr, brk_mcl, brk_mcf, bf⟩ := hbrk
  have hm_r := bf.mrk_len; have hs_r := bf.stk_len; have hc_r := bf.clr_len
  have hcl_r := bf.clr_le; have hsp_lt : sp.toNat < c.minDepth := bf.sp_lt; have hm_b := bf.hm
  have hlen_r := (hcore.of_minFields (mcf' := brk_mcf) hm_r hs_r hc_r hcl_r).lengths
  have hmd_le : c.minDepth ≤ 1000 := minDepthOf_le c.mv
  cp_steps!
  · exact hQ true brk_mrk brk_mstk brk_mclr brk_mcl brk_mcf mr
      hlen_r bf.pres2 bf.hmin (fun _ => bf.hok ‹ok = true›) hm_b
  · refine wp_loop_inv (fun j mj => ∃ mrk2 mclr2 mcl2 mcf2,
        1 ≤ j.1.toNat ∧ j.1.toNat ≤ sp.toNat + 1 ∧ mrk2.length = c.mv ∧
        mclr2.length = c.mv ∧ mcl2 ≤ c.mv ∧
        (∀ w < c.mv, s.mrk[w]?.getD 0#8 = 2#8 → mrk2[w]?.getD 0#8 = 2#8) ∧
        MinMarkInv c (withMinFields s mrk2 brk_mstk mclr2 mcl2 mcf2) keepSet ∧
        (CorePlusMem c (withMinFields s mrk2 brk_mstk mclr2 mcl2 mcf2) ⋆ R) mj)
      (fun j _ => sp.toNat + 1 - j.1.toNat)
      (fun L2 ih2 => by
        cp_steps
        exact ih2 _ _ ⟨brk_mrk, brk_mclr, brk_mcl, brk_mcf, by simp only [bv_c0]; omega,
          by simp only [bv_c0]; omega, hm_r, hc_r, hcl_r, bf.pres2, bf.hmin, hm_b⟩)
      (fun L2 j mj ⟨mrk2, mclr2, mcl2, mcf2, hj1, hjle, hm2, hc2, hcl2, hp2, hmin2, hm2_mem⟩
          ih2 => ?_)
    cp_steps
    · have hj_le_sp : j.1.toNat ≤ sp.toNat := by c0_bound
      have hcore2 := hcore.of_minFields (mcf' := mcf2) hm2 hs_r hc2 hcl2
      refine LeanQbe.T.wp_call_of_spec _ _
        (minMark_wp_of_spec hMm _ 4#8 hcore2.lengths hm2_mem
          fun mrk3 mclr3 mcl3 mcf3 m3 hbr hm3 => ?_)
      cp_let_simp; cp_steps
      obtain ⟨hm3_len, hc3_len, hcl3, hp3, hmin3⟩ := minMark_poison_post hcore2 hmin2 _ hbr
      exact ih2 _ _ (by c0_bound) ⟨mrk3, mclr3, mcl3, mcf3, by c0_bound, by c0_bound,
        hm3_len, hc3_len, hcl3, fun w hw h2 => hp3 w hw (hp2 w hw h2), hmin3, hm3⟩
    · exact hQ false mrk2 brk_mstk mclr2 mcl2 mcf2 mj
        (hcore.of_minFields (mcf' := mcf2) hm2 hs_r hc2 hcl2).lengths
        hp2 hmin2 (fun hf => by cases hf) hm2_mem

private theorem min_lit_entry_inv {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    {keepSet : List Nat} {root_lit : BitVec 32} {idx0 maxSteps : Nat}
    {m : Mem 64} {R : Mem 64 → Prop}
    (hcore : CorePlusCoreInv c F0 s) (hmin : MinMarkInv c s keepSet)
    (hmd_pos : 1 ≤ c.minDepth) (hrl_lt : root_lit.toNat / 2 < c.mv)
    (hidx0 : idx0 < s.trail_end)
    (hroot_trv : (s.trl[idx0]?.getD 0#32).toNat / 2 = root_lit.toNat / 2)
    (hrm : s.mrk[root_lit.toNat / 2]?.getD 0#8 = 2#8)
    (hrc_ne : s.rsns[root_lit.toNat / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hrc_lt : (s.rsns[root_lit.toNat / 2]?.getD 0xFFFFFFFF#32).toNat < s.num_clauses)
    (hm : (CorePlusMem c
      { s with min_stk := (s.min_stk.set 0 (root_lit >>> 1)).set 1 0#32 } ⋆ R) m) :
    MinLitInv c s keepSet root_lit.toNat idx0 maxSteps (0#64, 0#64, ()) m R := by
  have hmstkl := hcore.lengths.min_stk_len
  have hmstk_set : ((s.min_stk.set 0 (root_lit >>> 1)).set 1 0#32).length = 2 * c.minDepth := by
    simp [hmstkl]
  have hstk0 : (((s.min_stk.set 0 (root_lit >>> 1)).set 1 0#32)[0]?.getD 0#32).toNat =
      root_lit.toNat / 2 := by
    rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by simp [hmstkl]; omega),
      Option.getD_some, bv32_lshr_1]
  have hstk1 : (((s.min_stk.set 0 (root_lit >>> 1)).set 1 0#32)[1]?.getD 0#32).toNat = 0 := by
    rw [List.getElem?_set_self (by simp [hmstkl]; omega), Option.getD_some]; rfl
  refine ⟨s.mrk, (s.min_stk.set 0 (root_lit >>> 1)).set 1 0#32, s.min_clr,
    s.min_clr_len, s.min_clr_full, by simp [bv_c0], hcore.lengths.mrk_len, hmstk_set,
    hcore.lengths.min_clr_len_arr, hcore.lengths.min_clr_len_le, fun _ _ hw => hw,
    minMarkInv_set_stk hmin _, ⟨hmd_pos, hcore.lengths.mrk_len, hmstk_set, fun j hj => ?_⟩, hm⟩
  have hj0 : j = 0 := by dsimp only at hj; simp only [bv_c0] at hj; omega
  subst hj0
  refine ⟨idx0, hidx0, by rw [hstk0]; exact hrl_lt, by rw [hstk0, hroot_trv], fun _ => rfl,
    by rw [hstk0, hrm]; decide, by rw [hstk0]; exact hrc_ne, by rw [hstk0]; exact hrc_lt,
    fun t ht => by simp only [Nat.mul_zero, Nat.zero_add, hstk1, Nat.zero_min] at ht; omega⟩

/-- Specification proof for `kissat_minimize_lit(h, root_lit)`. -/
theorem kissat_minimize_lit_wp (Γ : Env)
    (hMm : ∀ a m Q X, corePlusMinMarkSpec a m Q X →
      Γ "kissat_min_mark" [i64, i32, i8] [] a m Q X) :
    ∀ a m Q X, corePlusMinimizeLitSpec a m Q X →
      Func.wp Γ kissat_minimize_lit_body a m Q X := by
  rintro ⟨h, root_lit, ⟨⟩⟩ m Q X ⟨c, F0, s, keepSet, R, rfl, hcore, hmin, hrl, hrv, hrm, hm, hQ⟩
  unfold Func.wp kissat_minimize_lit_body
  have hmv := c.hmv; have hlcap := c.hlcap; have hmaxc := c.hmax_c
  unfold dimacsBound at hmv hlcap hmaxc
  have hmd_pos : 1 ≤ c.minDepth := minDepthOf_pos c.mv
  have hmd_le : c.minDepth ≤ 1000 := minDepthOf_le c.mv
  have hrl_lt : root_lit.toNat / 2 < c.mv := by omega
  have hml := hcore.lengths.mrk_len; have hll := hcore.lengths.lvl_len
  have hrsnl := hcore.lengths.rsns_len; have hclsl := hcore.lengths.cls_len
  have hlpl := hcore.lengths.lpool_len; have hmstkl := hcore.lengths.min_stk_len
  have hmclrl := hcore.lengths.min_clr_len_arr; have hmcl_le := hcore.lengths.min_clr_len_le
  have hlit_le := hcore.lengths.lit_len_le; have hnc_le := hcore.lengths.num_clauses_le
  have hmax_sum : s.lit_len + c.mv < 2 ^ 64 := by omega
  obtain ⟨idx0, hidx0, hroot_tr⟩ := (hcore.vals_false_iff root_lit.toNat hrl).mp hrv
  have hroot_trv : (s.trl[idx0]?.getD 0#32).toNat / 2 = root_lit.toNat / 2 := by
    rw [hroot_tr]; exact litVar_litNeg _
  let maxSteps := (s.lit_len + c.mv) * 4 + 64
  have hmax_lt : maxSteps < 2 ^ 64 := by unfold maxSteps; omega
  let hfalse : Q (false, ()) m := hQ false s.mrk s.min_stk s.min_clr s.min_clr_len s.min_clr_full
    m hcore.lengths (fun _ _ hw => hw) hmin (fun hf => by cases hf) hm
  cp_steps
  · exfalso; simp only [bv_c0, Nat.reducePow] at hc
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc; omega
  · exfalso; have h0 := congrArg BitVec.toNat hc
    simp only [BitVec.toNat_ofNat, bv64_toNat_zero] at h0; omega
  · exact hfalse
  · exact hfalse
  · exact hfalse
  · exact hfalse
  · have hPost := hJ; clear hJ
    obtain ⟨hrc_ne, hrc_lt⟩ := min_lit_entry_rsn hcore hrl_lt (by assumption) (by assumption)
    suffices hBrk : ∀ r mr, MinLitBrk c s keepSet root_lit.toNat r mr R → J r mr by
      refine wp_loop_inv (fun v ml => MinLitInv c s keepSet root_lit.toNat idx0 maxSteps v ml R)
        (fun v _ => maxSteps - v.2.1.toNat) (fun L ih => by
          cp_steps; exact ih _ _ (min_lit_entry_inv hcore hmin hmd_pos hrl_lt hidx0 hroot_trv hrm
            hrc_ne hrc_lt hm)) (fun L v ml inv ih => ?_)
      have hbrk0 : ∀ s', MinLitBrk c s keepSet root_lit.toNat (v.1, false, s', ()) ml R :=
        fun _ => inv.to_brk_false
      obtain ⟨mrk, mstk, mclr, mcl, mcf, hst_le, hmrkl, hmstkl', hmcl, hmcl_le,
        hp2, hmin_cur, hf, hm_cur⟩ := inv
      have hsp_lt := hf.sp_lt
      have hshl0 : (v.1 <<< 1).toNat = 2 * v.1.toNat := by simp [bv_c0]; omega
      have hshl1 : ((v.1 <<< 1) + 1).toNat = 2 * v.1.toNat + 1 := by simp [bv_c0]; omega
      obtain ⟨idx_cur, -, hv_lt_c, -, -, -, hrc1_c, hrc2_c, -⟩ := hf.idx v.1.toNat (le_refl _)
      have hpos_idx : 2 * v.1.toNat + 1 < mstk.length := by omega
      have hv_idx : 2 * v.1.toNat < mstk.length := by omega
      have hcls_b := hcore.clauses.bounds _ hrc2_c
      have h2m : 2 * v.1.toNat % 2 ^ 64 = 2 * v.1.toNat := Nat.mod_eq_of_lt (by omega)
      have h2p1m : (2 * v.1.toNat + 1) % 2 ^ 64 = 2 * v.1.toNat + 1 := Nat.mod_eq_of_lt (by omega)
      clear hPost hfalse hQ hmin hrv hrm hrc_ne hrc_lt idx_cur
      cp_steps
      · exact hBrk _ _ (hbrk0 _)
      · exact hBrk _ _ (hbrk0 _)
      · exact hBrk _ _ (hbrk0 _)
      · exact hBrk _ _ (hbrk0 _)
      · exact hBrk _ _ (hbrk0 _)
      · exact min_lit_brk_pos hBrk hsp_lt hmrkl hmstkl' hmcl hmcl_le hp2 hmin_cur hshl1 hm
      · refine min_lit_skip_leaf hcore rfl hmax_lt hmax_sum (by assumption) hmrkl hmstkl' hmcl
          hmcl_le hp2 hmin_cur hf hshl1 ih hrc1_c hrc2_c (by assumption) h2m h2p1m rfl (Or.inl ?_)
          hm
        have hlp_p := min_lp_lt hcore hrc2_c (min_pos_lt_clauseSize (by assumption) h2m h2p1m)
        have hc' := congrArg BitVec.toNat hc
        rwa [min_lpool_q_eq h2m h2p1m hlp_p, bv32_lshr_1, bv_get_eq _ h2m] at hc'
      · refine min_lit_skip_leaf hcore rfl hmax_lt hmax_sum (by assumption) hmrkl hmstkl' hmcl
          hmcl_le hp2 hmin_cur hf hshl1 ih hrc1_c hrc2_c (by assumption) h2m h2p1m rfl
          (Or.inr (Or.inl ?_)) hm
        have hlp_p := min_lp_lt hcore hrc2_c (min_pos_lt_clauseSize (by assumption) h2m h2p1m)
        have hc' := congrArg BitVec.toNat hc
        rwa [bv_get_eq _ (min_lpool_u_eq h2m h2p1m hlp_p)] at hc'
      · have hpos_lt := min_pos_lt_clauseSize (by assumption) h2m h2p1m
        have hlp_p := min_lp_lt hcore hrc2_c hpos_lt
        have hu_lt := min_u_lt_mv_of h2m h2p1m hlp_p (by omega) ‹¬c.mv % 2 ^ 64 ≤ _›
        refine min_lit_skip_leaf hcore rfl hmax_lt hmax_sum (by assumption) hmrkl hmstkl' hmcl
          hmcl_le hp2 hmin_cur hf hshl1 ih hrc1_c hrc2_c (by assumption) h2m h2p1m rfl
          (Or.inr (Or.inr ?_)) hm
        rw [min_mrk_u_eq h2m h2p1m hlp_p] at hc
        rcases hmin_cur.mrk_dom _ hu_lt with h0 | h2 | h4
        · exfalso; apply hc; rw [h0]; decide
        · exact h2
        · exfalso; apply hc; rw [h4]; decide
      · exact min_lit_brk_pos hBrk hsp_lt hmrkl hmstkl' hmcl hmcl_le hp2 hmin_cur hshl1 hm
      · exact min_lit_ur_step hMm hcore hmrkl hmstkl' hmcl hmcl_le hp2 hmin_cur hf hshl0 hshl1
          (by assumption) hrc2_c h2m h2p1m hBrk hm
      · exact min_lit_ur_step hMm hcore hmrkl hmstkl' hmcl hmcl_le hp2 hmin_cur hf hshl0 hshl1
          (by assumption) hrc2_c h2m h2p1m hBrk hm
      · exact min_lit_brk_pos hBrk hsp_lt hmrkl hmstkl' hmcl hmcl_le hp2 hmin_cur hshl1 hm
      · exact min_lit_brk_pos hBrk hsp_lt hmrkl hmstkl' hmcl hmcl_le hp2 hmin_cur hshl1 hm
      · exact min_lit_brk_pos hBrk hsp_lt hmrkl hmstkl' hmcl hmcl_le hp2 hmin_cur hshl1 hm
      · rename_i hmrk2 hmrk4 hur1 hur2 _ _
        have hpos_lt := min_pos_lt_clauseSize (by assumption) h2m h2p1m
        have hlp_p := min_lp_lt hcore hrc2_c hpos_lt
        have hu_lt := min_u_lt_mv_of h2m h2p1m hlp_p (by omega) ‹¬c.mv % 2 ^ 64 ≤ _›
        have hm_z : mrk[(s.lpool[clauseOff s (s.rsns[(mstk[2 * v.1.toNat]?.getD
            0#32).toNat]?.getD 0xFFFFFFFF#32).toNat + (mstk[2 * v.1.toNat + 1]?.getD
            0#32).toNat]?.getD 0#32).toNat / 2]?.getD 0#8 = 0#8 := by
          rw [min_mrk_u_eq h2m h2p1m hlp_p] at hmrk2 hmrk4
          rcases hmin_cur.mrk_dom _ hu_lt with h0 | h2 | h4
          · exact h0
          · exfalso; rw [h2] at hmrk2; revert hmrk2; decide
          · exfalso; rw [h4] at hmrk4; revert hmrk4; decide
        have hne_v : s.lpool[clauseOff s (s.rsns[(mstk[2 * v.1.toNat]?.getD
            0#32).toNat]?.getD 0xFFFFFFFF#32).toNat + (mstk[2 * v.1.toNat + 1]?.getD
            0#32).toNat]?.getD 0#32 >>> 1 ≠ mstk[2 * v.1.toNat]?.getD 0#32 := by
          rw [← min_lpool_q_eq h2m h2p1m hlp_p, ← bv_get_eq (by rw [h2m]; exact hv_idx) h2m]
          assumption
        have hsp1_lt : v.1.toNat + 1 < c.minDepth := by
          have := Nat.mod_eq_of_lt (by omega : c.minDepth < 2 ^ 64)
          have := Nat.mod_eq_of_lt (by omega : v.1.toNat + 1 < 2 ^ 64); omega
        have hur_lt := min_ur_lt_of h2m h2p1m hlp_p (by omega) hur2
        have hur_ne := min_ur_ne_of h2m h2p1m hlp_p hur1
        rw [← bv32_lshr_1] at hur_lt hur_ne
        exact min_lit_step_push hcore hmax_lt hmax_sum rfl (by assumption) hmrkl hmstkl' hmcl
          hmcl_le hp2 hmin_cur hf hshl0 hshl1 hrc1_c hpos_lt hlp_p hu_lt hm_z hne_v hsp1_lt
          hur_ne hur_lt ih (by omega) hm
      · have hv0 : v.1 = 0#64 := by assumption
        rw [hv0]; have hv0n : v.1.toNat = 0 := by rw [hv0]; rfl
        have hpos_ge : clauseSize s (s.rsns[(mstk[0]?.getD 0#32).toNat]?.getD
            0xFFFFFFFF#32).toNat ≤ (mstk[1]?.getD 0#32).toNat := by
          simpa only [hv0n] using min_pos_ge_clauseSize (by assumption) h2m h2p1m
        exact hBrk _ _ (min_lit_done_brk hcore hmrkl hmstkl' hmcl hmcl_le hp2 hmin_cur
          (hv0n ▸ hf) hroot_tr hpos_ge hm_cur)
      · have hsp_pos : 0 < v.1.toNat :=
          Nat.pos_of_ne_zero fun h0 => ‹v.1 ≠ 0#64› (BitVec.eq_of_toNat_eq (by simpa using h0))
        have hpos_ge := min_pos_ge_clauseSize (by assumption) h2m h2p1m
        have hcore_cur := hcore.of_minFields (mcf' := mcf) hmrkl hmstkl' hmcl hmcl_le
        have hmstk0 : (withMinFields s mrk mstk mclr mcl mcf).min_stk[(v.1 <<< 1).toNat] =
            mstk[2 * v.1.toNat]?.getD 0#32 := by
          dsimp only [withMinFields]; exact bv_get_eq _ hshl0
        have hst_c : v.2.1.toNat < ((s.lit_len + c.mv) % 2 ^ 64 * 4 + 64) % 2 ^ 64 := by assumption
        cp_let_simp; rw [hmstk0]
        refine LeanQbe.T.wp_call_of_spec _ _
          (minMark_wp_of_spec hMm (mstk[2 * v.1.toNat]?.getD 0#32) 2#8 hcore_cur.lengths hm_cur
            fun mrk3 mclr3 mcl3 mcf3 m3 hbr hm3 => ?_)
        rw [withMinFields_upd] at hm3; cp_let_simp
        have ⟨hst1, hst2⟩ := min_steps_lt rfl hmax_lt hmax_sum hst_c
        exact ih _ _ hst2 (min_lit_pop_cont hcore hst1 hmrkl hmstkl' hmcl hmcl_le hp2 hmin_cur
          hf hsp_pos hpos_ge hbr hm3)
      · exact hBrk _ _ (hbrk0 _)
    rintro ⟨sp, ok, steps, ⟨⟩⟩ mr hbrk
    exact hPost _ _ (min_lit_post_wp hMm hcore hQ hbrk)

/-! ## 2. `kissat_minimize_clause` (`corePlusMinimizeClauseSpec`) -/

private theorem min_clause_finish {c : CorePlusCfg} {F0 : CNF Nat} {s s0 : CorePlusState}
    {R : Mem 64 → Prop} {Q : Post []} {tmp_f : List (BitVec 32)} {mrk_f mrk_c : List (BitVec 8)}
    {mstk_f mclr_f : List (BitVec 32)} {mcl_f : Nat} {mcf_f keep_f : BitVec 64} {m' : Mem 64}
    (hs0 : s0 = { s with heur := { s.heur with conflicts := s.heur.conflicts + 1 } })
    (hQ : ∀ tmp' tl' mrk' mstk' mclr' mcl' mcf' heur' m',
      let s' : CorePlusState := { s with
        tmp := tmp', tmp_len := tl', mrk := mrk', min_stk := mstk', min_clr := mclr',
        min_clr_len := mcl', min_clr_full := mcf', heur := heur' }
      CorePlusInv c F0 s' → 1 ≤ tl' → tl' ≤ s.tmp_len → tmp'[0]? = s.tmp[0]? →
      (∀ j, 1 ≤ j → j < tl' → ∃ i, 1 ≤ i ∧ i < s.tmp_len ∧ tmp'[j]? = s.tmp[i]?) →
      F0.EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat)) →
      (CorePlusMem c s' ⋆ R) m' → Q () m')
    (hcore_f : CorePlusCoreInv c F0 (withMinTmp s0 tmp_f mrk_f mstk_f mclr_f mcl_f mcf_f))
    (hmclen : mrk_c.length = c.mv) (hmc_c : ∀ w < c.mv, mrk_c[w]?.getD 0#8 = 0#8)
    (inv : FilterInv c s0 keep_f.toNat s0.tmp_len tmp_f mrk_f mstk_f mclr_f mcl_f mcf_f)
    (hent : F0.EntailsClause (cnfClause ((tmp_f.take keep_f.toNat).map BitVec.toNat)))
    (hm : (CorePlusMem c { s0 with
      tmp := tmp_f, tmp_len := keep_f.toNat, mrk := mrk_c, min_stk := mstk_f, min_clr := mclr_f,
      min_clr_len := 0, min_clr_full := 0#64,
      heur := { s0.heur with
        learned_lits := s0.heur.learned_lits + keep_f,
        min_removed := s0.heur.min_removed + (BitVec.ofNat 64 s.tmp_len - keep_f) } } ⋆ R) m') :
    Q () m' := by
  subst hs0; dsimp only at hm hcore_f inv
  have hkeep_lt : keep_f.toNat < 2 ^ 64 := keep_f.isLt
  have hk_le : keep_f.toNat ≤ s.tmp_len := by
    have := inv.hkle; have := inv.hk_le; omega
  have hcore_end : CorePlusCoreInv c F0 { s with
      tmp := tmp_f, tmp_len := keep_f.toNat, mrk := mrk_c, min_stk := mstk_f, min_clr := mclr_f,
      min_clr_len := 0, min_clr_full := 0#64,
      heur := { s.heur with
        conflicts := s.heur.conflicts + 1,
        learned_lits := s.heur.learned_lits + keep_f,
        min_removed := s.heur.min_removed + (BitVec.ofNat 64 s.tmp_len - keep_f) } } :=
    { hcore_f with
      lengths := { hcore_f.lengths with
        tmp_len_lt := hkeep_lt, mrk_len := hmclen, min_clr_len_le := Nat.zero_le _,
        heur_ok := hcore_f.lengths.heur_ok.with_stats _ _ _ }
      clauses := { hcore_f.clauses with bounds := hcore_f.clauses.bounds } }
  exact hQ tmp_f keep_f.toNat mrk_c mstk_f mclr_f 0 0#64 _ _ ⟨hcore_end, hmc_c⟩ inv.hk1
    hk_le inv.tmp0 inv.kept hent hm

private theorem bv64_add1_toNat {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + 1).toNat = x.toNat + 1 := by simp [bv_c0]; omega

private theorem min_clause_post_ent {c : CorePlusCfg} {F0 : CNF Nat} {s0 : CorePlusState}
    {keep k : Nat} {tmp : List (BitVec 32)} {mrk : List (BitVec 8)}
    {mstk mclr : List (BitVec 32)} {mcl : Nat} {mcf : BitVec 64}
    (hcore0 : CorePlusCoreInv c F0 s0) (hs0_arr : s0.tmp_len ≤ s0.tmp.length)
    (horig : F0.EntailsClause (cnfClause ((s0.tmp.take s0.tmp_len).map BitVec.toNat)))
    (htmp_all : ∀ k < s0.tmp_len, (s0.tmp[k]?.getD 0#32).toNat < 2 * c.mv ∧
      s0.vals[(s0.tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8)
    (inv : FilterInv c s0 keep k tmp mrk mstk mclr mcl mcf) (hkeq : k = s0.tmp_len) :
    FilterInv c s0 keep s0.tmp_len tmp mrk mstk mclr mcl mcf ∧
    CorePlusCoreInv c F0 (withMinTmp s0 tmp mrk mstk mclr mcl mcf) ∧
    F0.EntailsClause (cnfClause ((tmp.take keep).map BitVec.toNat)) := by
  rw [hkeq] at inv
  have hcore_f := hcore0.of_minTmp (mcf' := mcf) inv.tmp_len inv.mrk_len inv.stk_len
    inv.clr_len inv.clr_le
  exact ⟨inv, hcore_f, min_clause_entails hcore_f hs0_arr horig htmp_all inv⟩

/-- Specification proof for `kissat_minimize_clause(h)`. -/
theorem kissat_min_clause_wp (Γ : Env)
    (hMm : ∀ a m Q X, corePlusMinMarkSpec a m Q X →
      Γ "kissat_min_mark" [i64, i32, i8] [] a m Q X)
    (hMl : ∀ a m Q X, corePlusMinimizeLitSpec a m Q X →
      Γ "kissat_minimize_lit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, corePlusMinimizeClauseSpec a m Q X →
      Func.wp Γ kissat_minimize_clause_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, htl1, htlmv, horig, htmp, hm, hQ⟩
  unfold Func.wp kissat_minimize_clause_body
  have hcore := hinv.core; have hmc := hinv.marks
  have hmv : c.mv < 2 ^ 28 := c.hmv
  have hml := hcore.lengths.mrk_len; have htmparr := hcore.lengths.tmp_len_arr
  have hmstkl := hcore.lengths.min_stk_len; have hmclrl := hcore.lengths.min_clr_len_arr
  have hmcl_le := hcore.lengths.min_clr_len_le
  let s0 : CorePlusState := { s with heur := { s.heur with conflicts := s.heur.conflicts + 1 } }
  have hcore0 : CorePlusCoreInv c F0 s0 :=
    hcore.with_heur (hcore.lengths.heur_ok.with_stats _ _ _)
  have hmc0 : MarksClear c s0 := hmc
  have hs0_arr : s0.tmp_len ≤ s0.tmp.length := by change s.tmp_len ≤ s.tmp.length; omega
  cp_steps
  · exact hQ s.tmp s.tmp_len s.mrk s.min_stk s.min_clr s.min_clr_len s.min_clr_full
      { s.heur with
        conflicts := s.heur.conflicts + 1,
        learned_lits := s.heur.learned_lits + BitVec.ofNat 64 s.tmp_len } _
      ⟨hcore.with_heur (hcore.lengths.heur_ok.with_stats _ _ _), hmc⟩ htl1 (le_refl _) rfl
      (fun j hj1 hjlt => by c0_bound) horig hm
  · exfalso; c0_bound
  · clear hJ
    have htlt1 : 1 < s.tmp_len := by c0_bound
    have htlt264 : s0.tmp_len < 2 ^ 64 := by change s.tmp_len < 2 ^ 64; omega
    have hs0_tl : s0.tmp_len = s.tmp_len := rfl
    have hs0_len : s0.tmp.length = c.mv := htmparr; have hs0_mv : s0.tmp_len ≤ c.mv := htlmv
    let orig := (s0.tmp.take s0.tmp_len).map BitVec.toNat
    refine wp_loop_inv (fun i mi => ∃ mrk1 mclr1 mcl1 mcf1,
        SeedInv c s0 orig i.1.toNat mrk1 mclr1 mcl1 mcf1 ∧
        (CorePlusMem c (withMinFields s0 mrk1 s0.min_stk mclr1 mcl1 mcf1) ⋆ R) mi)
      (fun i _ => s0.tmp_len - i.1.toNat) (fun L1 ih1 => by
        cp_steps; exact ih1 _ _ ⟨s0.mrk, s0.min_clr, 0, 0#64,
          ⟨by c0_bound, hml, hmclrl, Nat.zero_le _,
            fun w hw => by rw [hmc0 w hw]; decide, fun _ hk => by c0_bound,
            minMarkInv_init (hcore0.of_minFields hml hmstkl hmclrl (Nat.zero_le _)) hmc0 orig⟩, hm⟩)
      (fun L1 i mi ⟨mrk1, mclr1, mcl1, mcf1, inv1, hm1⟩ ih1 => ?_)
    have hile1 := inv1.ile
    cp_steps
    · have hilt : i.1.toNat < s0.tmp_len := by rw [hs0_tl]; c0_bound
      have hi_arr : i.1.toNat < s0.tmp.length := by change i.1.toNat < s.tmp.length; omega
      have hcore1 := hcore0.of_minFields (mcf' := mcf1) inv1.mrk_len hmstkl inv1.clr_len inv1.clr_le
      cp_let_simp
      refine LeanQbe.T.wp_call_of_spec _ _ (minMark_wp_of_spec hMm (s0.tmp[i.1.toNat]'hi_arr >>> 1)
        2#8 hcore1.lengths hm1 fun mrk2 mclr2 mcl2 mcf2 m2 hbr hm2 => ?_)
      rw [withMinFields_upd] at hm2; cp_let_simp
      refine ih1 _ _ (by c0_bound) ⟨mrk2, mclr2, mcl2, mcf2, ?_, hm2⟩
      rw [show (i.1 + 1, ()).1.toNat = i.1.toNat + 1 from bv64_add1_toNat (by omega)]
      exact min_clause_seed_step hcore0 hilt hi_arr rfl
        (fun j hj => (htmp j hj).1) (htmp i.1.toNat hilt).2 inv1 hbr
    · refine wp_loop_inv (fun v mv => ∃ tmp2 mrk2 mstk2 mclr2 mcl2 mcf2,
          FilterInv c s0 v.1.toNat v.2.1.toNat tmp2 mrk2 mstk2 mclr2 mcl2 mcf2 ∧
          (CorePlusMem c (withMinTmp s0 tmp2 mrk2 mstk2 mclr2 mcl2 mcf2) ⋆ R) mv)
        (fun v _ => s0.tmp_len - v.2.1.toNat) (fun L2 ih2 => by
          cp_steps
          have hieq : i.1.toNat = s0.tmp_len := by have := inv1.ile; rw [hs0_tl] at this ⊢; c0_bound
          refine ih2 _ _ ⟨s0.tmp, mrk1, s0.min_stk, mclr1, mcl1, mcf1, ?_, hm1⟩
          rw [show BitVec.toNat ((1, 1, ()) : Tup Val [i64, i64]).1 = 1 from by simp [bv_c0]]
          exact ⟨le_refl _, le_refl _, htl1, htmparr, inv1.mrk_len, hmstkl, inv1.clr_len,
            inv1.clr_le, rfl, fun j hj1 hjl => by omega, fun _ _ _ => rfl,
            fun j hj => inv1.marked j (by omega),
            by have hinit := inv1.hmin; dsimp only [withMinFields] at hinit
               rwa [mcKeepSet_init htl1 hs0_arr]⟩)
        (fun L2 v mv ⟨tmp2, mrk2, mstk2, mclr2, mcl2, mcf2, inv2, hm2⟩ ih2 => ?_)
      have htmp2l := inv2.tmp_len; have hk_le2 := inv2.hk_le; have hkle2 := inv2.hkle
      cp_steps
      · have hk_lt : v.2.1.toNat < s0.tmp_len := by rw [hs0_tl]; c0_bound
        have hk_arr : v.2.1.toNat < tmp2.length := by rw [inv2.tmp_len]; omega
        have hcore2 := hcore0.of_minTmp (mcf' := mcf2) inv2.tmp_len inv2.mrk_len inv2.stk_len
          inv2.clr_len inv2.clr_le
        have hlit_eq : tmp2[v.2.1.toNat]'hk_arr = s0.tmp[v.2.1.toNat]?.getD 0#32 := by
          rw [← inv2.tail v.2.1.toNat (le_refl _) hk_lt, List.getElem?_eq_getElem hk_arr,
            Option.getD_some]
        have hlt_v := htmp v.2.1.toNat hk_lt
        have hm2_v : mrk2[(tmp2[v.2.1.toNat]'hk_arr).toNat / 2]?.getD 0#8 = 2#8 := by
          rw [hlit_eq]; exact inv2.mrk2 v.2.1.toNat hk_lt
        cp_let_simp
        refine LeanQbe.T.wp_call_of_spec _ _ (hMl _ _ _ _ ⟨c, F0,
          withMinTmp s0 tmp2 mrk2 mstk2 mclr2 mcl2 mcf2,
          mcKeepSet s0.tmp s0.tmp_len tmp2 v.1.toNat v.2.1.toNat, R, rfl, hcore2, inv2.hmin,
          by rw [hlit_eq]; exact hlt_v.1, by rw [hlit_eq]; exact hlt_v.2, hm2_v, hm2,
          fun ok mrk3 mstk3 mclr3 mcl3 mcf3 m3 hlen3 hp3 hmin3 hok3 hm3 => ?_⟩)
        rw [withMinTmp_upd] at hm3; cp_let_simp; cp_steps
        · refine ih2 _ _ (by c0_bound) ⟨tmp2, mrk3, mstk3, mclr3, mcl3, mcf3, ?_, hm3⟩
          rw [show (v.1, v.2.1 + 1, ()).1.toNat = v.1.toNat from rfl,
              show (v.1, v.2.1 + 1, ()).2.1.toNat = v.2.1.toNat + 1 from bv64_add1_toNat (by omega)]
          simp only [LeanQbe.T.Arg.val_var] at hok3
          exact min_clause_filter_drop inv2 hk_lt hs0_arr (fun j hj => (htmp j hj).1)
            hlen3.mrk_len hlen3.min_stk_len hlen3.min_clr_len_arr hlen3.min_clr_len_le hp3
            fun kp hsub => hok3 ‹ok = true› kp fun l hl =>
              (hsub l hl).imp_left fun h1 => by rw [h1, hlit_eq]
        · refine ih2 _ _ (by c0_bound) ⟨tmp2.set v.1.toNat (tmp2[v.2.1.toNat]'hk_arr),
            mrk3, mstk3, mclr3, mcl3, mcf3, ?_, by simpa only [hlit_eq] using hm⟩
          rw [show (v.1 + 1, v.2.1 + 1, ()).1.toNat = v.1.toNat + 1 from
                bv64_add1_toNat (by omega),
              show (v.1 + 1, v.2.1 + 1, ()).2.1.toNat = v.2.1.toNat + 1 from
                bv64_add1_toNat (by omega)]
          exact min_clause_filter_keep inv2 hk_lt hs0_arr htlmv (fun j hj => (htmp j hj).1)
            hlen3.mrk_len hlen3.min_stk_len hlen3.min_clr_len_arr hlen3.min_clr_len_le
            hp3 hmin3 hlit_eq
      · obtain ⟨inv2, hcore_f, hent⟩ := min_clause_post_ent hcore0 hs0_arr horig htmp inv2
          (by have := inv2.hk_le; rw [hs0_tl] at this ⊢; c0_bound)
        refine wp_loop_inv (fun w mw => ∃ mrk3, w.1.toNat ≤ c.mv ∧ mrk3.length = c.mv ∧
            (∀ u < w.1.toNat, mrk3[u]?.getD 0#8 = 0#8) ∧
            (CorePlusMem c (withMinTmp s0 tmp2 mrk3 mstk2 mclr2 mcl2 mcf2) ⋆ R) mw)
          (fun w _ => c.mv - w.1.toNat) (fun L3 ih3 => by
            cp_steps; exact ih3 _ _ ⟨mrk2, by c0_bound, inv2.mrk_len,
              fun u hu => by simp [bv_c0] at hu, hm2⟩)
          (fun L3 w mw ⟨mrk3, hwle, hm3l, hzr3, hm3⟩ ih3 => ?_)
        cp_steps
        · exact ih3 _ _ (by c0_bound) ⟨mrk3.set w.1.toNat 0#8, by c0_bound, by simp [hm3l],
            fun u hu => by
              by_cases hue : u = w.1.toNat
              · subst hue; rw [List.getElem?_set_self (by c0_bound)]; rfl
              · rw [List.getElem?_set_ne (Ne.symm hue)]; exact hzr3 u (by c0_bound), hm⟩
        · exact min_clause_finish rfl hQ hcore_f hm3l (fun u hu => hzr3 u (by c0_bound)) inv2
            hent hm
      · obtain ⟨inv2, hcore_f, hent⟩ := min_clause_post_ent hcore0 hs0_arr horig htmp inv2
          (by have := inv2.hk_le; rw [hs0_tl] at this ⊢; c0_bound)
        refine wp_loop_inv (fun z mz => ∃ mrk3, ClearListInv c mrk2 mrk3 mclr2 z.1.toNat mcl2 ∧
            (CorePlusMem c (withMinTmp s0 tmp2 mrk3 mstk2 mclr2 mcl2 mcf2) ⋆ R) mz)
          (fun z _ => mcl2 - z.1.toNat) (fun L3 ih3 => by
            cp_steps; exact ih3 _ _ ⟨mrk2, ⟨Nat.zero_le _, inv2.mrk_len,
              fun _ _ hw => hw, fun _ hj => by simp [bv_c0] at hj⟩, hm2⟩)
          (fun L3 z mz ⟨mrk3, inv3, hm3⟩ ih3 => ?_)
        have hzle := inv3.zle; have hm3l := inv3.len; have hcl2 := inv2.clr_le
        have hmclr_l := inv2.clr_len
        cp_steps
        · have hzi : z.1.toNat < mclr2.length := by c0_bound
          have hlt32 := (mclr2[z.1.toNat]'hzi).isLt
          refine ih3 _ _ (by c0_bound) ⟨_, ?_, by rwa [bv_c0_zext32_64] at hm⟩
          rw [show (z.1 + 1, ()).1.toNat = z.1.toNat + 1 from bv64_add1_toNat (by omega)]
          exact inv3.step_clr (by c0_bound) hzi (by simp only [bv_c0, Nat.reducePow] at hc; omega)
        · have hzi : z.1.toNat < mclr2.length := by c0_bound
          have hlt32 := (mclr2[z.1.toNat]'hzi).isLt
          refine ih3 _ _ (by c0_bound) ⟨mrk3, ?_, hm3⟩
          rw [show (z.1 + 1, ()).1.toNat = z.1.toNat + 1 from bv64_add1_toNat (by omega)]
          exact inv3.step_skip (by c0_bound) hzi (by simp only [bv_c0, Nat.reducePow] at hc; omega)
        · have hzeq : z.1.toNat = mcl2 := by c0_bound
          rw [hzeq] at inv3
          exact min_clause_finish rfl hQ hcore_f hm3l
            (min_clause_clr_clear inv3 (inv2.hmin.clr_cov ‹mcf2 = 0#64›)) inv2 hent hm

end

end LeanQbe.T.Examples.Kissat.CorePlus
