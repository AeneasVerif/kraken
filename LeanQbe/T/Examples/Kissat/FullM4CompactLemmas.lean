/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM4Compact
public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Examples.Kissat.FullSpec2
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0Agrees
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` M4a Compaction Lemmas & Contracts (`FullM4CompactLemmas`)

Shared tactics, `CompactVmtfRest`/`CompactHeapRest` array-focus helpers, `FullCfgCompat` /
`FullCfg.shrinkMv` dimacs-header shrink helpers, `CompactBijOk` bijection theory,
`CompactUnmapBinsOk` / `CompactArenaOk` transition lemmas, canonical `20`-row `compactSpecTable`
/ `compactEnv` (reusing `FullSpec2.full*Spec`), and `nvCompact*` heap helpers.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4Compact

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. Strictly scoped tactics & arithmetic / index-0 / focus helpers (`FullCompactTactics`) -/

namespace FullCompactTactics

open scoped FullArenaTactics

theorem strip_le_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

scoped macro "cm_strip" : tactic =>
  `(tactic| first | apply strip_le_32_64 | apply strip_le_8_32 | apply strip_le_8_64)
scoped macro "cm_unmdata" : tactic =>
  `(tactic| first | change LeanQbe.T.Func.wp _ _ _ _ _ _ | change LeanQbe.T.wp _ _ _ _ _)
scoped macro "cm_steps" : tactic =>
  `(tactic| (
      (try cm_unmdata)
      (repeat cm_strip)
      c0_steps
      repeat (any_goals (cm_strip; repeat cm_strip); c0_steps)))

open Lean Elab Tactic in
scoped elab "cm_to_group" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let ty ← Lean.instantiateMVars (← g.getType)
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.group then
        out := out.push g
      else if ty.isAppOf ``And && ty.getAppNumArgs == 2 then
        try
          evalTactic (← `(tactic| cm_strip))
          go (fuel - 1); out := out ++ (← getUnsolvedGoals)
        catch _ => out := out.push g
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out.push g
    setGoals out.toList
  evalTactic (← `(tactic| try cm_unmdata))
  go 500

open Lean Elab Tactic in
scoped elab "cm_split" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let ty ← Lean.instantiateMVars (← (← getMainGoal).getType)
    if ty.isAppOf ``And && ty.getAppNumArgs == 2 then
      try evalTactic (← `(tactic| cm_strip)); go (fuel - 1); return catch _ => return
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
      let _ ← LeanQbe.T.C0Step.stepOnce; return
    if ← LeanQbe.T.C0Step.stepOnce then go (fuel - 1)
  evalTactic (← `(tactic| try cm_unmdata))
  go 100

@[scoped c0_store] theorem store_full_frame_trail0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.core.frame_trail.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pFrameTrail ∧
      (FullMem c { s with core := { s.core with frame_trail := s.core.frame_trail.set 0 v } } ⋆ R)
        (storeMem m i32 c.pFrameTrail v) := by
  simpa using FullArenaTactics.store_full_frame_trail (i := 0) v hi hm

@[scoped c0_store] theorem store_full_frame_dec0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.core.frame_dec.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pFrameDec ∧
      (FullMem c { s with core := { s.core with frame_dec := s.core.frame_dec.set 0 v } } ⋆ R)
        (storeMem m i32 c.pFrameDec v) := by
  simpa using FullArenaTactics.store_full_frame_dec (i := 0) v hi hm

end FullCompactTactics

open FullArenaTactics FullCompactTactics
open scoped FullArenaTactics FullCompactTactics

theorem compactMem_cast {c : FullCfg} {s1 s2 : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMem c s1 ⋆ R) m) (heq : s1 = s2) : (FullMem c s2 ⋆ R) m :=
  heq ▸ hm

theorem bv64_add_nat {x : BitVec 64} (n : Nat) (hn : n < 2 ^ 64)
    (h : x.toNat + n < 2 ^ 64) : (x + BitVec.ofNat 64 n).toNat = x.toNat + n := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt h]

theorem bv64_add1 {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + (1 : BitVec 64)).toNat = x.toNat + 1 := bv64_add_nat 1 (by decide) h

theorem bv64_add2 {x : BitVec 64} (h : x.toNat + 2 < 2 ^ 64) :
    (x + (2 : BitVec 64)).toNat = x.toNat + 2 := bv64_add_nat 2 (by decide) h

theorem bv64_add3 {x : BitVec 64} (h : x.toNat + 3 < 2 ^ 64) :
    (x + (3 : BitVec 64)).toNat = x.toNat + 3 := bv64_add_nat 3 (by decide) h

theorem bv64_add4 {x : BitVec 64} (h : x.toNat + 4 < 2 ^ 64) :
    (x + (4 : BitVec 64)).toNat = x.toNat + 4 := bv64_add_nat 4 (by decide) h

theorem bv32_add1 {x : BitVec 32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + (1 : BitVec 32)).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

theorem bv64_shl1_toNat {x : BitVec 64} (h : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm, Nat.mod_eq_of_lt h]

theorem bv64_shl2_toNat {x : BitVec 64} (h : 4 * x.toNat < 2 ^ 64) :
    (x <<< (2 : Nat)).toNat = 4 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show 2 ^ 2 = 4 from rfl, Nat.mul_comm,
    Nat.mod_eq_of_lt h]

theorem bv64_shr1_toNat (x : BitVec 64) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv32_shr1_toNat (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv64_add3_zext_toNat {x : BitVec 64} {y : BitVec 32}
    (h : x.toNat + 3 + y.toNat < 2 ^ 64) :
    (x + (3 : BitVec 64) + y.setWidth 64).toNat = x.toNat + 3 + y.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat y (by decide),
    show (3 : BitVec 64).toNat = 3 from rfl,
    Nat.mod_eq_of_lt (by omega : x.toNat + 3 < 2 ^ 64), Nat.mod_eq_of_lt h]

theorem bv8_sext32_eq0_of_dom {x : BitVec 8}
    (hd : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) : x.signExtend 32 = 0#32 ↔ x = 0#8 := by
  rcases hd with rfl | rfl | rfl <;> decide

theorem bv8_gt0_of_dom {x : BitVec 8} (hdom : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    ((0#32).slt (x.signExtend 32) = true ↔ x = 1#8) ∧
    ((x.signExtend 32).slt 0#32 = true ↔ x = 0xFF#8) := by
  rcases hdom with rfl | rfl | rfl <;> decide

theorem bv32_bin_word_props {l : BitVec 32} (hl : l.toNat < 0x7FFFFFFF) :
    let w := (l &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    (w &&& 0x80000000#32) ≠ 0#32 ∧ w ≠ 0xFFFFFFFF#32 ∧ (w &&& 0x7FFFFFFF#32) = l := by
  intro w
  have hl_eq : l &&& 0x7FFFFFFF#32 = l := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have hw7 : w &&& 0x7FFFFFFF#32 = l := by
    have h1 : w &&& 0x7FFFFFFF#32 = l &&& 0x7FFFFFFF#32 := by
      ext i hi
      have h0 : ((0x80000000#32)[i] && (0x7FFFFFFF#32)[i]) = false := by
        rw [← BitVec.getElem_and]; exact BitVec.getElem_zero hi
      simp [w, BitVec.getElem_and, BitVec.getElem_or, Bool.and_or_distrib_right, h0]
    rw [h1, hl_eq]
  have hw8 : (w &&& 0x80000000#32) ≠ 0#32 := by
    intro h; have h31 := congrArg (·[31]) h
    have hb : (0x80000000#32)[31]'(by decide) = true := by decide
    simp only [w, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_zero, hb,
      Bool.or_true, Bool.true_and] at h31
    exact Bool.noConfusion h31
  exact ⟨hw8, binWatchWord_ne_sentinel (by rw [hw7]; exact hl), hw7⟩

theorem bv32_clear_shrk_rsn (x : BitVec 32) (hng : (x &&& 0x00080000#32) = 0#32) :
    ((x &&& ~~~(0x00800000#32 ||| 0x00200000#32)) &&& 0x00800000#32) = 0#32 ∧
    ((x &&& ~~~(0x00800000#32 ||| 0x00200000#32)) &&& 0x00080000#32) = 0#32 :=
  ⟨by rw [BitVec.and_assoc]; exact BitVec.and_zero, by rw [BitVec.and_assoc]; exact hng⟩

theorem entails_of_unsat_cnf {F : CNF Nat} (hu : F.Unsat) (c : CNF.Clause Nat) :
    F.EntailsClause c :=
  CNF.entails_clause_def.mpr fun α hα => False.elim ((CNF.unsat_iff_not_sat.mp hu) α hα)

theorem drop_take_succ_cm {α : Type} {xs : List α} {off n : Nat} (hlt : off + n < xs.length) :
    (xs.drop off).take (n + 1) = (xs.drop off).take n ++ [xs[off + n]'hlt] := by
  have h1 : n < (xs.drop off).length := by simp; omega
  rw [List.take_add_one, List.getElem?_eq_getElem h1, List.getElem_drop]; simp

theorem fullLastLearnedWf_of_cleared {s : FullState}
    (hclear : ∀ i < 8, s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    FullLastLearnedWf s := fun i hi => Or.inl (hclear i hi)

theorem WatchSliceOk_step {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} {w0 : BitVec 32} (h : WatchSliceOk F_cur k lit p rem)
    (hpos : 0 < rem) (hw0 : k.wstk[p]? = some w0) :
    ((w0 &&& 0x80000000#32) ≠ 0#32 →
      w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
      WatchSliceOk F_cur k lit (p + 1) (rem - 1)) ∧
    ((w0 &&& 0x80000000#32) = 0#32 →
      2 ≤ rem ∧ WatchSliceOk F_cur k lit (p + 2) (rem - 2)) := by
  cases h with
  | empty => omega
  | bin hp hf hne hlt hent hrest =>
    rw [hp] at hw0; cases hw0
    exact ⟨fun _ => ⟨hne, hlt, hent, by simpa using hrest⟩, fun h0 => absurd h0 hf⟩
  | large hp _ hf _ _ hrest =>
    rw [hp] at hw0; cases hw0
    exact ⟨fun hne => absurd hf hne, fun _ => ⟨by omega, by simpa using hrest⟩⟩

/-! ### Focus / unfocus helpers for `q_stamp`/`wsort` (`vmtf`) and `score`/`heap`/`pos` (`heap`) -/

def CompactVmtfRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
  FullScrByteArrs c s.scratch ⋆
  array (t := i32) c.pHeap s.scratch.heap ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
  array (t := i32) c.pShrinkStk s.scratch.shrink_stk ⋆
  array (t := i32) c.pQPrev s.scratch.q_prev ⋆ array (t := i32) c.pQNext s.scratch.q_next ⋆
  array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
  array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
  array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
  array (t := i32) c.pTarjanReach s.scratch.tarjan_reach ⋆
  FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch ⋆ c.pad

theorem focus_vmtf_arrays {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆ array (t := i32) c.pWsort s.scratch.wsort ⋆
      (CompactVmtfRest c s ⋆ R)) m := by
  unfold FullMem FullScratchArrays FullScrU32A FullScrWksArrs at hm
  unfold CompactVmtfRest; ecancel

theorem unfocus_vmtf_arrays {c : FullCfg} {s : FullState} {ws' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m' : Mem 64}
    (hm : (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆ array (t := i32) c.pWsort ws' ⋆
      (CompactVmtfRest c s ⋆ R)) m') :
    (FullMem c { s with scratch := { s.scratch with wsort := ws' } } ⋆ R) m' := by
  let sc' : FullScratch := { s.scratch with wsort := ws' }
  change (FullMem c { s with scratch := sc' } ⋆ R) m'
  unfold FullMem FullScratchArrays FullScrU32A FullScrWksArrs
  rw [show Full.hdrTailWords c { s with scratch := sc' } = Full.hdrTailWords c s from rfl,
    show FullScrByteArrs c sc' = FullScrByteArrs c s.scratch from rfl,
    show FullScrMetaArrs c sc' = FullScrMetaArrs c s.scratch from rfl,
    show FullScrDynArrs c sc' = FullScrDynArrs c s.scratch from rfl]
  unfold CompactVmtfRest at hm; dsimp only [sc']; ecancel

def CompactHeapRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
  FullScrByteArrs c s.scratch ⋆
  array (t := i32) c.pShrinkStk s.scratch.shrink_stk ⋆
  array (t := i32) c.pQPrev s.scratch.q_prev ⋆ array (t := i32) c.pQNext s.scratch.q_next ⋆
  array (t := i32) c.pQStamp s.scratch.q_stamp ⋆ FullScrWksArrs c s.scratch ⋆
  array64 c.pSimSig s.scratch.sim_sig ⋆ array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
  array (t := i32) c.pLastLearned s.scratch.last_learned ⋆ FullScrDynArrs c s.scratch ⋆ c.pad

theorem focus_heap_arrays {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array64 c.pScore s.scratch.score ⋆ array (t := i32) c.pHeap s.scratch.heap ⋆
      array (t := i32) c.pPos s.scratch.pos ⋆ (CompactHeapRest c s ⋆ R)) m := by
  unfold FullMem FullScratchArrays FullScrU32A FullScrMetaArrs at hm
  unfold CompactHeapRest; ecancel

theorem unfocus_heap_arrays {c : FullCfg} {s : FullState} {hp' ps' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m' : Mem 64}
    (hm : (array64 c.pScore s.scratch.score ⋆ array (t := i32) c.pHeap hp' ⋆
      array (t := i32) c.pPos ps' ⋆ (CompactHeapRest c s ⋆ R)) m') :
    (FullMem c { s with scratch := { s.scratch with heap := hp', pos := ps' } } ⋆ R) m' := by
  let sc' : FullScratch := { s.scratch with heap := hp', pos := ps' }
  change (FullMem c { s with scratch := sc' } ⋆ R) m'
  unfold FullMem FullScratchArrays FullScrU32A FullScrMetaArrs
  rw [show Full.hdrTailWords c { s with scratch := sc' } = Full.hdrTailWords c s from rfl,
    show FullScrByteArrs c sc' = FullScrByteArrs c s.scratch from rfl,
    show FullScrWksArrs c sc' = FullScrWksArrs c s.scratch from rfl,
    show FullScrDynArrs c sc' = FullScrDynArrs c s.scratch from rfl]
  unfold CompactHeapRest at hm; dsimp only [sc']; ecancel

/-! ## 2. `FullCfgCompat`, `FullCfg.shrinkMv`, & header shrink stores -/

/-- Configuration compatibility after dead-variable compaction shrinks `d.mv` (`#1991`):
preserves `hdr`, `avail`, `max_vars`, and all buffer capacities, keeping pointers and `pad` equal
while allowing `mv` to decrease (`bva_cap := max_vars - mv`). -/
structure FullCfgCompat (c c' : FullCfg) : Prop where
  hdr : c'.hdr = c.hdr
  avail : c'.avail = c.avail
  mv_le : c'.mv ≤ c.mv
  max_vars : c'.max_vars = c.max_vars
  nc : c'.nc = c.nc
  arena_cap : c'.arena_cap = c.arena_cap
  wcap : c'.wcap = c.wcap
  delayed_cap : c'.delayed_cap = c.delayed_cap
  red_cap : c'.red_cap = c.red_cap
  extend_cap : c'.extend_cap = c.extend_cap
  scratch_cap : c'.scratch_cap = c.scratch_cap

theorem FullCfgCompat.refl (c : FullCfg) : FullCfgCompat c c :=
  ⟨rfl, rfl, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem FullCfgCompat.trans {c1 c2 c3 : FullCfg}
    (h12 : FullCfgCompat c1 c2) (h23 : FullCfgCompat c2 c3) : FullCfgCompat c1 c3 :=
  ⟨h23.hdr.trans h12.hdr, h23.avail.trans h12.avail, Nat.le_trans h23.mv_le h12.mv_le,
   h23.max_vars.trans h12.max_vars, h23.nc.trans h12.nc, h23.arena_cap.trans h12.arena_cap,
   h23.wcap.trans h12.wcap, h23.delayed_cap.trans h12.delayed_cap,
   h23.red_cap.trans h12.red_cap, h23.extend_cap.trans h12.extend_cap,
   h23.scratch_cap.trans h12.scratch_cap⟩

/-- Shrink `mv` to `mv' ≤ c.mv` and grow `bva_cap` to `c.max_vars - mv'`. -/
def fullCfgShrinkMv (c : FullCfg) (mv' : Nat) (hle : mv' ≤ c.mv) : FullCfg where
  hdr := c.hdr
  avail := c.avail
  mv := mv'
  max_vars := c.max_vars
  bva_cap := c.max_vars - mv'
  nc := c.nc
  arena_cap := c.arena_cap
  wcap := c.wcap
  delayed_cap := c.delayed_cap
  red_cap := c.red_cap
  extend_cap := c.extend_cap
  scratch_cap := c.scratch_cap
  hbva := by have := c.hbva; omega
  hmv := Nat.lt_of_le_of_lt hle c.hmv
  hmaxv := c.hmaxv
  hnc := c.hnc
  harena := c.harena
  hwcap := c.hwcap
  hdel := c.hdel
  hred := c.hred
  hext := c.hext
  hscr := c.hscr
  havail_fit := c.havail_fit
  hsize := c.hsize

theorem FullCfgCompat.shrinkMv (c : FullCfg) (mv' : Nat) (hle : mv' ≤ c.mv) :
    FullCfgCompat c (fullCfgShrinkMv c mv' hle) :=
  ⟨rfl, rfl, hle, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem FullLitMarksClear.of_compat {c c' : FullCfg} {s : FullState}
    (hc : FullCfgCompat c c') (h : FullLitMarksClear c s) : FullLitMarksClear c' s :=
  ⟨fun v hv => h.1 v (hc.max_vars ▸ hv), fun l hl => h.2 l (hc.max_vars ▸ hl)⟩

theorem FullExtScratchOk.of_compat {c c' : FullCfg} {s s' : FullState}
    (hc : FullCfgCompat c c') (h : FullExtScratchOk c s) (hpres : FullExtScratchPres s s')
    (hsub : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s') :
    FullExtScratchOk c' s' := by
  refine ⟨FullLastLearnedWf.of_refs_subset h.1 hpres.1 hsub, ?_⟩
  rw [hc.extend_cap, hpres.2]; exact h.2

/-- Intermediate heap predicate between `h->d.mv = ncv` and `h->bva_cap = h->max_vars - ncv`. -/
def FullMemShrinkMid (c : FullCfg) (mv' : BitVec 64) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr mv' (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
  FullScratchArrays c s.scratch ⋆ c.pad

private theorem hdrTailWords_set94 (c : FullCfg) (s : FullState) (mv' : Nat) (hle : mv' ≤ c.mv) :
    (Full.hdrTailWords c s).set 94 (BitVec.ofNat 64 (c.max_vars - mv')) =
      Full.hdrTailWords (fullCfgShrinkMv c mv' hle) s := by
  simp only [Full.hdrTailWords, Full.hdrTailWords0, Full.hdrTailWords1, Full.hdrTailWords2,
    Full.hdrTailWords3, List.cons_append, List.nil_append, List.set_cons_succ, List.set_cons_zero]
  rfl

private theorem fullRest_shrinkMv (c : FullCfg) (s : FullState) (mv' : Nat) (hle : mv' ≤ c.mv) :
    FullCoreArrays (fullCfgShrinkMv c mv' hle) s.core = FullCoreArrays c s.core ∧
    FullScratchArrays (fullCfgShrinkMv c mv' hle) s.scratch = FullScratchArrays c s.scratch ∧
    (fullCfgShrinkMv c mv' hle).pad = c.pad :=
  ⟨rfl, rfl, rfl⟩

theorem full_store_mv_mid {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (mv' : BitVec 64) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 c.hdr ∧
      (FullMemShrinkMid c mv' s ⋆ R) (storeMem m i64 c.hdr mv') := by
  have h1 : (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
      s.core.d_cur s.core.d_val ⋆
      (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
        FullScratchArrays c s.scratch ⋆ c.pad ⋆ R)) m := by
    unfold FullMem at hm; ecancel
  obtain ⟨hok, hst⟩ := store_dimacs_mv mv' h1
  refine ⟨hok, ?_⟩
  unfold FullMemShrinkMid; ecancel

theorem full_load_max_vars_mid {c : FullCfg} {mv' : BitVec 64} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMemShrinkMid c mv' s ⋆ R) m) :
    loadVal m i64 (c.hdr + 768) = some (BitVec.ofNat 64 c.max_vars) := by
  have h1 : (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
      (dimacsState c.hdr mv' (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
        FullCoreArrays c s.core ⋆ FullScratchArrays c s.scratch ⋆ c.pad ⋆ R)) m := by
    unfold FullMemShrinkMid at hm; ecancel
  have hget := loadVal_array64 (i := 92) (by rw [Full.hdrTailWords_length]; decide) h1
  rw [BitVec.add_assoc, show (32 : BitVec 64) + BitVec.ofNat 64 (8 * 92) = 768 by decide] at hget
  have helem : (Full.hdrTailWords c s)[92]'(by rw [Full.hdrTailWords_length]; decide) =
      BitVec.ofNat 64 c.max_vars := rfl
  simpa only [helem] using hget

theorem full_store_bva_mid {c : FullCfg} {mv' : Nat} (hle : mv' ≤ c.mv) {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMemShrinkMid c (BitVec.ofNat 64 mv') s ⋆ R) m) :
    storeOk m i64 (c.hdr + 784) ∧
      (FullMem (fullCfgShrinkMv c mv' hle) s ⋆ R)
        (storeMem m i64 (c.hdr + 784) (BitVec.ofNat 64 (c.max_vars - mv'))) := by
  have h1 : (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 mv') (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
        FullCoreArrays c s.core ⋆ FullScratchArrays c s.scratch ⋆ c.pad ⋆ R)) m := by
    unfold FullMemShrinkMid at hm; ecancel
  obtain ⟨hok, hst⟩ := store_array64 (i := 94) (BitVec.ofNat 64 (c.max_vars - mv'))
    (by rw [Full.hdrTailWords_length]; decide) h1
  have hptr : c.hdr + 32 + BitVec.ofNat 64 (8 * 94) = c.hdr + 784 := by
    rw [BitVec.add_assoc, show (32 : BitVec 64) + BitVec.ofNat 64 (8 * 94) = 784 by decide]
  rw [hptr] at hok hst
  rw [hdrTailWords_set94 c s mv' hle] at hst
  have ⟨hc1, hc2, hc3⟩ := fullRest_shrinkMv c s mv' hle
  refine ⟨hok, ?_⟩
  unfold FullMem
  rw [hc1, hc2, hc3]
  change (dimacsState (fullCfgShrinkMv c mv' hle).hdr
      (BitVec.ofNat 64 (fullCfgShrinkMv c mv' hle).mv)
      (BitVec.ofNat 64 (fullCfgShrinkMv c mv' hle).nc) s.core.d_cur s.core.d_val ⋆
    array64 ((fullCfgShrinkMv c mv' hle).hdr + 32)
      (Full.hdrTailWords (fullCfgShrinkMv c mv' hle) s) ⋆
    FullCoreArrays c s.core ⋆ FullScratchArrays c s.scratch ⋆ c.pad ⋆ R) _
  ecancel

/-! ### Binary-only watch slices parameterized by explicit active variable count `nvars` -/

inductive CompactBinSliceOk (nvars : Nat) (F_cur : List (List Nat)) (k : FullCoreState)
    (lit : Nat) : Nat → Nat → Prop where
  | empty {p} : CompactBinSliceOk nvars F_cur k lit p 0
  | bin {p rem w0} :
      k.wstk[p]? = some w0 → (w0 &&& 0x80000000#32) ≠ 0#32 → w0 ≠ 0xFFFFFFFF#32 →
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * nvars →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) →
      CompactBinSliceOk nvars F_cur k lit (p + 1) rem →
      CompactBinSliceOk nvars F_cur k lit p (rem + 1)

theorem CompactBinSliceOk.toWatchSliceOk {nvars : Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {lit p rem : Nat} (hnv : nvars ≤ k.cur_vars)
    (h : CompactBinSliceOk nvars F_cur k lit p rem) :
    WatchSliceOk F_cur k lit p rem := by
  induction h with
  | empty => exact .empty
  | @bin p rem w0 hp hf hne hlt hent _ ih =>
    exact .bin hp hf hne (by omega) hent ih

/-! ## 3. Pure remapping bijection, CNF projection, & UNSAT soundness reconstruction -/

/-- Reverse-map a compacted literal `l'` back to original variable space via `inv`. -/
def compactUnmapLit (inv : List (BitVec 32)) (l' : Nat) : Nat :=
  2 * (inv[l' / 2]?.getD 0#32).toNat + l' % 2

theorem compactUnmapLit_pair (inv : List (BitVec 32)) {v' : Nat} (l : Nat)
    (hv' : (inv[v']?.getD 0#32).toNat = l / 2) :
    compactUnmapLit inv (2 * v' + l % 2) = l := by
  unfold compactUnmapLit
  have hd : (2 * v' + l % 2) / 2 = v' := by omega
  have hm : (2 * v' + l % 2) % 2 = l % 2 := by omega
  rw [hd, hm, hv']; omega

theorem compactUnmapLit_div2 (inv : List (BitVec 32)) (l' : Nat) :
    compactUnmapLit inv l' / 2 = (inv[l' / 2]?.getD 0#32).toNat := by
  unfold compactUnmapLit; omega

theorem compactUnmapLit_mod2 (inv : List (BitVec 32)) (l' : Nat) :
    compactUnmapLit inv l' % 2 = l' % 2 := by
  unfold compactUnmapLit; omega

/-- Bijection invariants established on `map` (`work_stk1`) and `inv` (`work_stk2`) by
`full_compact_assign_map`. -/
structure CompactBijOk (old_cv ncv : Nat) (vals : List (BitVec 8))
    (map inv : List (BitVec 32)) : Prop where
  old_cv_lt : old_cv < 0x7FFFFFFF
  ncv_le : ncv ≤ old_cv
  map_ok : ∀ v < old_cv,
    map[v]? = some 0xFFFFFFFF#32 ∨
    ∃ nv < ncv, nv ≤ v ∧ vals[2 * v]?.getD 0#8 = 0#8 ∧
      map[v]? = some (BitVec.ofNat 32 nv) ∧ inv[nv]? = some (BitVec.ofNat 32 v)
  inv_ok : ∀ nv < ncv,
    ∃ ov < old_cv, nv ≤ ov ∧ vals[2 * ov]?.getD 0#8 = 0#8 ∧
      inv[nv]? = some (BitVec.ofNat 32 ov) ∧ map[ov]? = some (BitVec.ofNat 32 nv)

theorem CompactBijOk.map_inj {old_cv ncv : Nat} {vals : List (BitVec 8)}
    {map inv : List (BitVec 32)} (h : CompactBijOk old_cv ncv vals map inv)
    {v1 v2 : Nat} (hv1 : v1 < old_cv) (hv2 : v2 < old_cv)
    {nv1 nv2 : BitVec 32} (hm1 : map[v1]? = some nv1) (hm2 : map[v2]? = some nv2)
    (hne : nv1 ≠ 0xFFFFFFFF#32) (heq : nv1 = nv2) : v1 = v2 := by
  have hb1 : ∃ n1 < ncv, n1 ≤ v1 ∧ vals[2 * v1]?.getD 0#8 = 0#8 ∧
      map[v1]? = some (BitVec.ofNat 32 n1) ∧ inv[n1]? = some (BitVec.ofNat 32 v1) := by
    rcases h.map_ok v1 hv1 with hff | hex
    · exact absurd (Option.some.inj (hm1.symm.trans hff)) hne
    · exact hex
  have hne2 : nv2 ≠ 0xFFFFFFFF#32 := heq ▸ hne
  have hb2 : ∃ n2 < ncv, n2 ≤ v2 ∧ vals[2 * v2]?.getD 0#8 = 0#8 ∧
      map[v2]? = some (BitVec.ofNat 32 n2) ∧ inv[n2]? = some (BitVec.ofNat 32 v2) := by
    rcases h.map_ok v2 hv2 with hff | hex
    · exact absurd (Option.some.inj (hm2.symm.trans hff)) hne2
    · exact hex
  obtain ⟨n1, hn1, _, _, hmv1, hinv1⟩ := hb1
  obtain ⟨n2, hn2, _, _, hmv2, hinv2⟩ := hb2
  have hncv_lt : ncv < 2 ^ 32 := Nat.lt_of_le_of_lt h.ncv_le (by have := h.old_cv_lt; omega)
  have hov_lt : old_cv < 2 ^ 32 := by have := h.old_cv_lt; omega
  have hbv : BitVec.ofNat 32 n1 = BitVec.ofNat 32 n2 := by
    have ha := Option.some.inj (hm1.symm.trans hmv1)
    have hb := Option.some.inj (hm2.symm.trans hmv2)
    exact ha.symm.trans (heq.trans hb)
  have hn12 : n1 = n2 := by
    have hto := congrArg BitVec.toNat hbv
    rwa [bv32_ofNat_toNat (by omega), bv32_ofNat_toNat (by omega)] at hto
  subst hn12
  have hvt := congrArg BitVec.toNat (Option.some.inj (hinv1.symm.trans hinv2))
  rwa [bv32_ofNat_toNat (by omega), bv32_ofNat_toNat (by omega)] at hvt

theorem CompactBijOk.inv_inj {old_cv ncv : Nat} {vals : List (BitVec 8)}
    {map inv : List (BitVec 32)} (h : CompactBijOk old_cv ncv vals map inv)
    {nv1 nv2 : Nat} (hn1 : nv1 < ncv) (hn2 : nv2 < ncv)
    (heq : (inv[nv1]?.getD 0#32).toNat = (inv[nv2]?.getD 0#32).toNat) : nv1 = nv2 := by
  obtain ⟨ov1, hov1, _, _, hi1, hm1⟩ := h.inv_ok nv1 hn1
  obtain ⟨ov2, hov2, _, _, hi2, hm2⟩ := h.inv_ok nv2 hn2
  have hov_lt : old_cv < 2 ^ 32 := by have := h.old_cv_lt; omega
  have hncv_lt : ncv < 2 ^ 32 := Nat.lt_of_le_of_lt h.ncv_le (by omega)
  rw [hi1, hi2, Option.getD_some, Option.getD_some, bv32_ofNat_toNat (by omega),
    bv32_ofNat_toNat (by omega)] at heq
  subst heq
  have hbv := Option.some.inj (hm1.symm.trans hm2)
  have hto := congrArg BitVec.toNat hbv
  rwa [bv32_ofNat_toNat (by omega), bv32_ofNat_toNat (by omega)] at hto

/-- Pre-remapped binary watch slice at old literal `old_lit` with compacted partners `< 2 * ncv`. -/
inductive CompactPreBinSliceOk (ncv : Nat) (inv : List (BitVec 32)) (F_cur : List (List Nat))
    (k : FullCoreState) (old_lit : Nat) : Nat → Nat → Prop where
  | empty {p} : CompactPreBinSliceOk ncv inv F_cur k old_lit p 0
  | bin {p rem w0} :
      k.wstk[p]? = some w0 → (w0 &&& 0x80000000#32) ≠ 0#32 → w0 ≠ 0xFFFFFFFF#32 →
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * ncv →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [old_lit, compactUnmapLit inv (w0 &&& 0x7FFFFFFF#32).toNat]) →
      CompactPreBinSliceOk ncv inv F_cur k old_lit (p + 1) rem →
      CompactPreBinSliceOk ncv inv F_cur k old_lit p (rem + 1)

theorem CompactPreBinSliceOk.relocate {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {k k' : FullCoreState} {old_lit p p' rem : Nat}
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : CompactPreBinSliceOk ncv inv F_cur k old_lit p rem) :
    CompactPreBinSliceOk ncv inv F_cur k' old_lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hf hne hlt hent _ ih =>
    exact .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hne hlt hent
      (ih (p' := p' + 1) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega))

theorem CompactPreBinSliceOk.append_bin {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {k k' : FullCoreState} {old_lit p p' rem : Nat} {w0 : BitVec 32}
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : CompactPreBinSliceOk ncv inv F_cur k old_lit p rem)
    (hw0 : k'.wstk[p' + rem]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * ncv)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [old_lit, compactUnmapLit inv (w0 &&& 0x7FFFFFFF#32).toNat])) :
    CompactPreBinSliceOk ncv inv F_cur k' old_lit p' (rem + 1) := by
  induction h generalizing p' with
  | empty => exact .bin (by simpa using hw0) hflag hne hlt hent .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    exact .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn hl he
      (ih (p' := p' + 1) (fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0))

theorem CompactPreBinSliceOk.ne_sentinel {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {k : FullCoreState} {old_lit p rem : Nat}
    (h : CompactPreBinSliceOk ncv inv F_cur k old_lit p rem) :
    ∀ idx < rem, k.wstk[p + idx]? ≠ some 0xFFFFFFFF#32 := by
  induction h with
  | empty => intro _ hk; omega
  | @bin p rem w0 hp _ hne _ _ _ ih =>
    intro idx hk; cases idx with
    | zero => rw [Nat.add_zero, hp]; exact fun heq => hne (Option.some.inj heq)
    | succ k' => simpa [Nat.add_assoc, Nat.add_comm 1 k'] using ih k' (by omega)

/-- Binary watch slice whose entries all fall strictly inside `< 2 * ncv` and whose unmapped
clauses `[compactUnmapLit inv l, compactUnmapLit inv ot]` are entailed by `F_cur`. -/
inductive CompactUnmapBinSliceOk (ncv : Nat) (inv : List (BitVec 32)) (F_cur : List (List Nat))
    (k : FullCoreState) (lit : Nat) : Nat → Nat → Prop where
  | empty {p} : CompactUnmapBinSliceOk ncv inv F_cur k lit p 0
  | bin {p rem w0} :
      k.wstk[p]? = some w0 → (w0 &&& 0x80000000#32) ≠ 0#32 → w0 ≠ 0xFFFFFFFF#32 →
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * ncv →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [compactUnmapLit inv lit,
          compactUnmapLit inv (w0 &&& 0x7FFFFFFF#32).toNat]) →
      CompactUnmapBinSliceOk ncv inv F_cur k lit (p + 1) rem →
      CompactUnmapBinSliceOk ncv inv F_cur k lit p (rem + 1)

theorem CompactUnmapBinSliceOk.of_pre {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {k : FullCoreState} {lit old_lit p rem : Nat}
    (hun : compactUnmapLit inv lit = old_lit)
    (h : CompactPreBinSliceOk ncv inv F_cur k old_lit p rem) :
    CompactUnmapBinSliceOk ncv inv F_cur k lit p rem := by
  induction h with
  | empty => exact .empty
  | @bin p rem w0 hp hf hne hlt hent _ ih =>
    exact .bin hp hf hne hlt (hun ▸ hent) ih

theorem CompactUnmapBinSliceOk.relocate {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {k k' : FullCoreState} {lit p p' rem : Nat}
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : CompactUnmapBinSliceOk ncv inv F_cur k lit p rem) :
    CompactUnmapBinSliceOk ncv inv F_cur k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hf hne hlt hent _ ih =>
    exact .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hne hlt hent
      (ih (p' := p' + 1) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega))

theorem CompactUnmapBinSliceOk.append_bin {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {k k' : FullCoreState} {lit p p' rem : Nat} {w0 : BitVec 32}
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : CompactUnmapBinSliceOk ncv inv F_cur k lit p rem)
    (hw0 : k'.wstk[p' + rem]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * ncv)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [compactUnmapLit inv lit,
        compactUnmapLit inv (w0 &&& 0x7FFFFFFF#32).toNat])) :
    CompactUnmapBinSliceOk ncv inv F_cur k' lit p' (rem + 1) := by
  induction h generalizing p' with
  | empty => exact .bin (by simpa using hw0) hflag hne hlt hent .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    exact .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn hl he
      (ih (p' := p' + 1) (fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0))

theorem CompactUnmapBinSliceOk.ne_sentinel {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {k : FullCoreState} {lit p rem : Nat}
    (h : CompactUnmapBinSliceOk ncv inv F_cur k lit p rem) :
    ∀ idx < rem, k.wstk[p + idx]? ≠ some 0xFFFFFFFF#32 := by
  induction h with
  | empty => intro _ hk; omega
  | @bin p rem w0 hp _ hne _ _ _ ih =>
    intro idx hk; cases idx with
    | zero => rw [Nat.add_zero, hp]; exact fun heq => hne (Option.some.inj heq)
    | succ k' => simpa [Nat.add_assoc, Nat.add_comm 1 k'] using ih k' (by omega)

structure CompactUnmapBinsOk (ncv : Nat) (inv : List (BitVec 32)) (F_cur : List (List Nat))
    (k : FullCoreState) : Prop where
  layout : WatchStackLayout k
  empty_hi : ∀ l, 2 * ncv ≤ l → l < 2 * k.cur_vars → fullWatchSizeCore k l = 0
  slices : ∀ l < 2 * ncv,
    CompactUnmapBinSliceOk ncv inv F_cur k l (fullWatchOffCore k l) (fullWatchSizeCore k l)

theorem CompactUnmapBinsOk.with_vars {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {k k' : FullCoreState} (h : CompactUnmapBinsOk ncv inv F_cur k)
    (hcv : k'.cur_vars = ncv) (hle : ncv ≤ k.cur_vars)
    (hwvec : k'.wvec = k.wvec) (hwstk : k'.wstk = k.wstk) (hwlen : k'.wlen = k.wlen) :
    CompactUnmapBinsOk ncv inv F_cur k' := by
  have hlay : WatchStackLayout k' :=
    ⟨fun l hl => by
       unfold fullWatchOffCore fullWatchSizeCore; rw [hwvec, hwlen]
       exact h.layout.bounds l (by omega),
     fun l hl hpos => by
       unfold fullWatchSizeCore at hpos; unfold fullWatchOffCore
       rw [hwvec] at hpos ⊢; exact h.layout.pos_off l (by omega) hpos,
     fun l1 l2 h1 h2 hne hp1 hp2 => by
       unfold fullWatchSizeCore at hp1 hp2; unfold fullWatchOffCore fullWatchSizeCore
       rw [hwvec] at hp1 hp2 ⊢
       exact h.layout.disjoint l1 l2 (by omega) (by omega) hne hp1 hp2,
     fun l hl idx hi => by
       unfold fullWatchSizeCore at hi; unfold fullWatchOffCore
       rw [hwvec] at hi ⊢; rw [hwstk]
       exact h.layout.no_sentinel l (by omega) idx hi⟩
  refine ⟨hlay, fun l hl1 hl2 => by omega, fun l hl => ?_⟩
  have hls := (h.slices l hl).relocate (k' := k') (p' := fullWatchOffCore k' l)
    (fun idx _ => by simp only [fullWatchOffCore, hwvec, hwstk])
  simpa [fullWatchSizeCore, hwvec] using hls

/-- Clean compacted arena invariant before/after `cur_vars := ncv`: contiguous valid clauses
with `PH_GARB` and `PH_SHRK` cleared, literals `< 2 * ncv`, and unmapped entailment in `F_cur`. -/
structure CompactArenaOk (c : FullCfg) (ncv : Nat) (inv : List (BitVec 32))
    (F_cur : List (List Nat)) (k : FullCoreState) : Prop where
  len_ok : k.arena_len = 0 ∨ 3 ≤ k.arena_len
  refs_wf : ∀ r ∈ fullArenaClauseRefsCore k,
    r + 3 ≤ k.arena_len ∧ 3 ≤ fullArenaClauseSizeCore k r ∧
    r + 3 + fullArenaClauseSizeCore k r ≤ fullArenaNextOff k.arena k.arena_len r ∧
    fullArenaNextOff k.arena k.arena_len r ≤ k.arena_len ∧
    (fullArenaNextOff k.arena k.arena_len r = k.arena_len ∨
     fullArenaNextOff k.arena k.arena_len r + 3 ≤ k.arena_len)
  no_shrk : ∀ r ∈ fullArenaClauseRefsCore k, (fullArenaHdrCore k r &&& 0x00800000#32) = 0#32
  no_garb : ∀ r ∈ fullArenaClauseRefsCore k, fullArenaClauseGarbCore k r = false
  lits_lt : ∀ r ∈ fullArenaClauseRefsCore k,
    ∀ l ∈ fullArenaClauseLitsCore k r, l < 2 * ncv
  nodup : ∀ r ∈ fullArenaClauseRefsCore k,
    ((fullArenaClauseLitsCore k r).map (· / 2)).Nodup
  entails : ∀ r ∈ fullArenaClauseRefsCore k,
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((fullArenaClauseLitsCore k r).map (compactUnmapLit inv)))

theorem CompactArenaOk.with_core {c : FullCfg} {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {k k' : FullCoreState} (h : CompactArenaOk c ncv inv F_cur k)
    (har : k'.arena = k.arena) (hal : k'.arena_len = k.arena_len) :
    CompactArenaOk c ncv inv F_cur k' := by
  have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k := by
    simp [fullArenaClauseRefsCore, har, hal]
  refine ⟨hal ▸ h.len_ok, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr; rw [hrefs] at hr; simpa [hal, har, fullArenaClauseSizeCore] using h.refs_wf r hr
  · intro r hr; rw [hrefs] at hr; simpa [fullArenaHdrCore, har] using h.no_shrk r hr
  · intro r hr; rw [hrefs] at hr
    simpa [fullArenaClauseGarbCore, fullArenaHdrCore, har] using h.no_garb r hr
  · intro r hr; rw [hrefs] at hr
    simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, har] using h.lits_lt r hr
  · intro r hr; rw [hrefs] at hr
    simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, har] using h.nodup r hr
  · intro r hr; rw [hrefs] at hr
    simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, har] using h.entails r hr

/-- Canonical CNF clause extraction from a binary-only-watched compacted `FullCoreState`. -/
def binSliceClauses (wstk : List (BitVec 32)) (lit p : Nat) : Nat → List (List Nat)
  | 0 => []
  | rem + 1 =>
    match wstk[p]? with
    | some w0 =>
      if (w0 &&& 0x80000000#32) ≠ 0#32 then
        [lit, (w0 &&& 0x7FFFFFFF#32).toNat] :: binSliceClauses wstk lit (p + 1) rem
      else binSliceClauses wstk lit (p + 1) rem
    | none => []

def arenaClausesCore (k : FullCoreState) : List (List Nat) :=
  (fullArenaClauseRefsCore k).filterMap fun r =>
    if fullArenaClauseGarbCore k r = false then some (fullArenaClauseLitsCore k r)
    else none

def stateClausesCore (k : FullCoreState) : List (List Nat) :=
  ((List.range (2 * k.cur_vars)).flatMap fun l =>
    binSliceClauses k.wstk l (fullWatchOffCore k l) (fullWatchSizeCore k l)) ++
  arenaClausesCore k

private theorem lit_eval_iff_unmap (inv : List (BitVec 32)) (α : Nat → Bool) (l' : Nat) :
    (α (inv[litVar l']?.getD 0#32).toNat = !litSign l') ↔
      (α (litVar (compactUnmapLit inv l')) = !litSign (compactUnmapLit inv l')) := by
  have hvar : litVar (compactUnmapLit inv l') = (inv[litVar l']?.getD 0#32).toNat :=
    compactUnmapLit_div2 inv l'
  have hsign : litSign (compactUnmapLit inv l') = litSign l' := by
    unfold litSign compactUnmapLit
    have hm : (2 * (inv[l' / 2]?.getD 0#32).toNat + l' % 2) % 2 = l' % 2 := by omega
    rw [hm]
  rw [hvar, hsign]

private theorem sat_cnfClause_unmap (inv : List (BitVec 32)) (α : Nat → Bool) (c : List Nat) :
    (cnfClause c).Sat (fun nv => α (inv[nv]?.getD 0#32).toNat) ↔
      (cnfClause (c.map (compactUnmapLit inv))).Sat α := by
  simp only [clause_sat_cnfClause_iff, List.mem_map]
  constructor
  · rintro ⟨l, hl, hev⟩
    exact ⟨compactUnmapLit inv l, ⟨l, hl, rfl⟩, (lit_eval_iff_unmap inv α l).mp hev⟩
  · rintro ⟨_, ⟨l, hl, rfl⟩, hev⟩
    exact ⟨l, hl, (lit_eval_iff_unmap inv α l).mpr hev⟩

private theorem binSliceClauses_props {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {k : FullCoreState} {lit p rem : Nat} (hl : lit < 2 * ncv)
    (h : CompactUnmapBinSliceOk ncv inv F_cur k lit p rem) :
    ∀ cl ∈ binSliceClauses k.wstk lit p rem,
      (∀ l ∈ cl, l < 2 * ncv) ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause (cl.map (compactUnmapLit inv))) := by
  induction h with
  | empty => intro cl hmem; simp [binSliceClauses] at hmem
  | @bin p rem w0 hp hf hne hlt hent _ ih =>
    intro cl hmem
    simp only [binSliceClauses, hp, hf, ne_eq, not_false_eq_true, ↓reduceIte,
      List.mem_cons] at hmem
    rcases hmem with rfl | hrest
    · refine ⟨fun l hl' => ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
        rcases hl' with rfl | rfl <;> assumption
      · simpa only [List.map_cons, List.map_nil] using hent
    · exact ih cl hrest

private theorem binSliceClauses_entails {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {k : FullCoreState} {lit p rem : Nat} (F_next : List (List Nat))
    (hsub : ∀ cl ∈ binSliceClauses k.wstk lit p rem, cl ∈ F_next)
    (h : CompactUnmapBinSliceOk ncv inv F_cur k lit p rem) :
    CompactBinSliceOk ncv F_next k lit p rem := by
  induction h with
  | empty => exact .empty
  | @bin p rem w0 hp hf hne hlt _ _ ih =>
    have hmem : [lit, (w0 &&& 0x7FFFFFFF#32).toNat] ∈ binSliceClauses k.wstk lit p (rem + 1) := by
      simp [binSliceClauses, hp, hf]
    exact .bin hp hf hne hlt (entails_mem_cnfOfClauses (hsub _ hmem))
      (ih fun cl hcl => hsub cl (by simp [binSliceClauses, hp, hf, hcl]))

theorem fullWitnessInv_compact_build {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {old_cv ncv : Nat} {inv : List (BitVec 32)} {k : FullCoreState}
    (hsound : ExtUnsatSound F0 old_cv F_cur)
    (hbin : CompactUnmapBinsOk ncv inv F_cur k)
    (har : CompactArenaOk c ncv inv F_cur k)
    (hcv : k.cur_vars = ncv)
    (hinc : k.inconsistent = 0#64) (hdm : k.dense_mode = 0#64)
    (hte : k.trail_end = 0) (hcl : k.cur_level = 0)
    (hft0 : (k.frame_trail[0]?.getD 0#32).toNat = 0)
    (hvals : ∀ l < 2 * k.cur_vars, k.vals[l]?.getD 0#8 = 0#8) :
    FullWitnessInv c F0 (stateClausesCore k) k ∧
    ExtUnsatSound F0 k.cur_vars (stateClausesCore k) := by
  let F_next := stateClausesCore k
  have hcl_props : ∀ cl ∈ F_next,
      (∀ l ∈ cl, l < 2 * ncv) ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause (cl.map (compactUnmapLit inv))) := by
    intro cl hcl_mem
    unfold F_next stateClausesCore at hcl_mem
    rcases List.mem_append.mp hcl_mem with hbin_m | har_m
    · rw [List.mem_flatMap] at hbin_m
      obtain ⟨l, hl, hmem⟩ := hbin_m
      rw [List.mem_range, hcv] at hl
      exact binSliceClauses_props hl (hbin.slices l hl) cl hmem
    · unfold arenaClausesCore at har_m
      rw [List.mem_filterMap] at har_m
      obtain ⟨r, hr, heq⟩ := har_m
      split at heq
      · cases heq; exact ⟨har.lits_lt r hr, har.entails r hr⟩
      · cases heq
  have hext : ExtUnsatSound F0 k.cur_vars F_next := by
    refine ⟨fun cl hcl_m l hl => ?_, fun hu => ?_⟩
    · have := (hcl_props cl hcl_m).1 l hl; unfold litVar; omega
    · apply hsound.2
      rw [CNF.unsat_iff_not_sat] at hu ⊢
      intro α hα
      apply hu (fun nv => α (inv[nv]?.getD 0#32).toNat)
      rw [cnf_sat_cnfOfClauses_iff]
      intro cl hcl_m
      exact (sat_cnfClause_unmap inv α cl).mpr
        (CNF.entails_clause_def.mp (hcl_props cl hcl_m).2 α hα)
  have hwat : ModeWatchesInv F_next k := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine ⟨hbin.layout, fun l hl => ?_⟩
    have hln : l < 2 * ncv := hcv ▸ hl
    have hbin_l : CompactBinSliceOk ncv F_next k l (fullWatchOffCore k l) (fullWatchSizeCore k l) :=
      binSliceClauses_entails F_next (fun cl hcl_m => by
        unfold F_next stateClausesCore
        exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨l, List.mem_range.mpr hl, hcl_m⟩))
        (hbin.slices l hln)
    exact hbin_l.toWatchSliceOk (by omega)
  have harena : FullArenaClausesInv c F_next k := by
    refine ⟨har.len_ok, har.refs_wf, ?_, ?_, ?_⟩
    · intro r hr hsh; exact absurd (har.no_shrk r hr) hsh
    · intro r hr hng l hl; have := har.lits_lt r hr l hl; omega
    · intro r hr hng
      refine entails_mem_cnfOfClauses ?_
      unfold F_next stateClausesCore arenaClausesCore
      refine List.mem_append_right _ (List.mem_filterMap.mpr ⟨r, hr, ?_⟩)
      simp only [hng, ↓reduceIte]
  refine ⟨⟨hext, fun hne => absurd hinc hne, harena, hwat, by rw [hte, hcl]; omega,
    fun _ h => by omega, fun _ _ h => by omega, fun l hl => Or.inl (hvals l hl),
    fun l hl => ⟨(by intro h1; rw [hvals l hl] at h1; cases h1), (by rintro ⟨_, hi, _⟩; omega)⟩,
    fun l hl => ⟨(by intro h1; rw [hvals l hl] at h1; cases h1), (by rintro ⟨_, hi, _⟩; omega)⟩,
    fun _ h => by omega, fun _ _ _ h => by omega, fun _ _ h2 => by omega,
    fun _ h => by omega, fun _ h => by omega, fun _ h => by omega,
    (fun L hL => by rw [show L = 0 by omega, hft0, hte]; omega),
    (fun L1 L2 _ hL2 => by rw [show L1 = L2 by omega]; omega),
    fun _ h => by omega, fun _ h => by omega, fun _ h => by omega, fun _ h => by omega⟩, hext⟩

private theorem compactBinSlice_to_unsat {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {k : FullCoreState} {l p rem : Nat}
    (hunsat : (cnfOfClauses [[]]).Unsat)
    (hs : CompactUnmapBinSliceOk ncv inv F_cur k l p rem) :
    CompactBinSliceOk ncv [[]] k l p rem := by
  induction hs with
  | empty => exact .empty
  | @bin p rem w0 hp hf hne hlt _ _ ih =>
    exact .bin hp hf hne hlt (entails_of_unsat_cnf hunsat _) ih

theorem fullWitnessInv_compact_unsat {c : FullCfg} {F0 : CNF Nat} {ncv : Nat}
    {inv : List (BitVec 32)} {F_cur : List (List Nat)} {k : FullCoreState}
    (hF0 : F0.Unsat) (hbin : CompactUnmapBinsOk ncv inv F_cur k)
    (har : CompactArenaOk c ncv inv F_cur k) (hcv : k.cur_vars = ncv) (hdm : k.dense_mode = 0#64)
    (hte : k.trail_end = 0) (hcl : k.cur_level = 0)
    (hft0 : (k.frame_trail[0]?.getD 0#32).toNat = 0)
    (hvals : ∀ l < 2 * k.cur_vars, k.vals[l]?.getD 0#8 = 0#8) :
    FullWitnessInv c F0 [[]] k := by
  have hunsat : (cnfOfClauses [[]]).Unsat :=
    unsat_of_entails_nil (entails_mem_cnfOfClauses List.mem_cons_self)
  have hext : ExtUnsatSound F0 k.cur_vars [[]] :=
    ⟨(fun cl hcl_m l hl => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl_m; subst cl; cases hl),
     (fun _ => hF0)⟩
  have hwat : ModeWatchesInv [[]] k := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine ⟨hbin.layout, fun l hl => ?_⟩
    exact (compactBinSlice_to_unsat hunsat (hbin.slices l (hcv ▸ hl))).toWatchSliceOk (by omega)
  have harena : FullArenaClausesInv c [[]] k :=
    ⟨har.len_ok, har.refs_wf, fun r hr hsh => absurd (har.no_shrk r hr) hsh,
     fun r hr _ l hl => by have := har.lits_lt r hr l hl; omega,
     fun _ _ _ => entails_of_unsat_cnf hunsat _⟩
  exact ⟨hext, fun _ => hunsat, harena, hwat, by rw [hte, hcl]; omega,
    fun _ h => by omega, fun _ _ h => by omega, fun l hl => Or.inl (hvals l hl),
    fun l hl => ⟨(by intro h1; rw [hvals l hl] at h1; cases h1), (by rintro ⟨_, hi, _⟩; omega)⟩,
    fun l hl => ⟨(by intro h1; rw [hvals l hl] at h1; cases h1), (by rintro ⟨_, hi, _⟩; omega)⟩,
    fun _ h => by omega, fun _ _ _ h => by omega, fun _ _ h2 => by omega,
    fun _ h => by omega, fun _ h => by omega, fun _ h => by omega,
    (fun L hL => by rw [show L = 0 by omega, hft0, hte]; omega),
    (fun L1 L2 _ hL2 => by rw [show L1 = L2 by omega]; omega),
    fun _ h => by omega, fun _ h => by omega, fun _ h => by omega, fun _ h => by omega⟩

/-! ### `FullState.LengthsOk`, watch-compaction, & arena-compaction transition helpers -/

theorem fullArenaNextOff_mem_of_mem {ar : List (BitVec 32)} {alen r : Nat}
    (hr : r ∈ fullArenaScanRefs ar alen 0 alen)
    (hnext3 : fullArenaNextOff ar alen r + 3 ≤ alen) :
    fullArenaNextOff ar alen r ∈ fullArenaScanRefs ar alen 0 alen := by
  have go : ∀ (fuel pos : Nat), alen - pos ≤ fuel →
      r ∈ fullArenaScanRefs ar alen pos fuel →
      fullArenaNextOff ar alen r ∈ fullArenaScanRefs ar alen pos fuel := by
    intro fuel; induction fuel with
    | zero => intro pos _ hmem; simp [fullArenaScanRefs] at hmem
    | succ f ih =>
      intro pos hfl hmem
      unfold fullArenaScanRefs at hmem ⊢; split at hmem
      · rename_i hle
        simp only [hle, ↓reduceIte, List.mem_cons] at hmem ⊢
        rcases hmem with rfl | hrest
        · right
          have hb := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := r) hle
          have hf1 : 1 ≤ f := by omega
          obtain ⟨f', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
          unfold fullArenaScanRefs; simp [hnext3]
        · exact Or.inr (ih (fullArenaNextOff ar alen pos)
            (by have := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hle; omega)
            hrest)
      · simp at hmem
  exact go alen 0 (by omega) hr

theorem FullSparseInv_with_work_stk1 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {ws1' : List (BitVec 32)} (hlen1 : ws1'.length = 2 * c.max_vars) :
    FullSparseInv c F0 { s with scratch := { s.scratch with work_stk1 := ws1' } } := by
  obtain ⟨Fc, hw⟩ := h.1.witness
  exact ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with work_stk1_len := hlen1 }⟩,
    Fc, hw⟩, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem FullSparseInvW_with_work_stk1 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) {ws1' : List (BitVec 32)}
    (hlen1 : ws1'.length = 2 * c.max_vars) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with work_stk1 := ws1' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with work_stk1_len := hlen1 }⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem compactBins_finish_lit {c : FullCfg} {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {k : FullCoreState} (hck : FullCoreState.LengthsOk c k)
    (hlay : WatchStackLayout k) {l q : Nat} (hl : l < 2 * k.cur_vars)
    (hq0 : fullWatchOffCore k l ≤ q)
    (hqend : q ≤ fullWatchOffCore k l + fullWatchSizeCore k l)
    {wstk' : List (BitVec 32)} (hwslen : wstk'.length = c.wcap)
    (hout1 : ∀ i, i < fullWatchOffCore k l ∨ fullWatchOffCore k l + fullWatchSizeCore k l ≤ i →
      wstk'[i]? = k.wstk[i]?)
    (hpre : CompactPreBinSliceOk ncv inv F_cur { k with wstk := wstk' } l
      (fullWatchOffCore k l) (q - fullWatchOffCore k l))
    {wu' nb' : BitVec 64} :
    let off0 := fullWatchOffCore k l
    let wvec' :=
      if q = off0 then (k.wvec.set (2 * l) 0#32).set (2 * l + 1) 0#32
      else k.wvec.set (2 * l + 1) (BitVec.ofNat 32 (q - off0))
    let k' : FullCoreState :=
      { k with wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' }
    FullCoreState.LengthsOk c k' ∧ WatchStackLayout k' ∧
    (∀ j < 2 * k.cur_vars, j ≠ l →
      fullWatchSizeCore k' j = fullWatchSizeCore k j ∧
      ∀ idx < fullWatchSizeCore k j,
        k'.wstk[fullWatchOffCore k' j + idx]? = k.wstk[fullWatchOffCore k j + idx]?) ∧
    fullWatchOffCore k' l = (if q = off0 then 0 else off0) ∧
    fullWatchSizeCore k' l = q - off0 ∧
    CompactPreBinSliceOk ncv inv F_cur k' l (fullWatchOffCore k' l) (fullWatchSizeCore k' l) := by
  intro off0 wvec' k'
  have hcv_le := hck.cur_vars_le
  have hwlen_le := hck.wlen_le
  have hwc_lt : c.wcap < 2 * 2 ^ 28 := c.hwcap
  have hbd_l := hlay.bounds l hl
  have hdiff_lt : q - off0 < 2 ^ 32 := by
    have : off0 = fullWatchOffCore k l := rfl
    omega
  have hwvec'_len : wvec'.length = 4 * c.max_vars := by
    dsimp only [wvec']; split <;> simp [hck.wvec_len]
  have hoff_self : fullWatchOffCore k' l = (if q = off0 then 0 else off0) := by
    unfold fullWatchOffCore; dsimp only [k', wvec']
    split
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by rw [hck.wvec_len]; omega)]
      rfl
    · rw [List.getElem?_set_ne (by omega)]; rfl
  have hsz_self : fullWatchSizeCore k' l = q - off0 := by
    unfold fullWatchSizeCore; dsimp only [k', wvec']
    split
    · rename_i hqe; rw [List.getElem?_set_self (by simp [hck.wvec_len]; omega), Option.getD_some,
        hqe, Nat.sub_self]; rfl
    · rw [List.getElem?_set_self (by rw [hck.wvec_len]; omega), Option.getD_some]
      exact bv32_ofNat_toNat hdiff_lt
  have hwvec'_ne : ∀ j < 2 * k.cur_vars, j ≠ l →
      fullWatchOffCore k' j = fullWatchOffCore k j ∧
      fullWatchSizeCore k' j = fullWatchSizeCore k j := by
    intro j _ hne; unfold fullWatchOffCore fullWatchSizeCore; dsimp only [k', wvec']
    split <;> constructor
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    · rw [List.getElem?_set_ne (by omega)]
    · rw [List.getElem?_set_ne (by omega)]
  have hother : ∀ j < 2 * k.cur_vars, j ≠ l →
      fullWatchSizeCore k' j = fullWatchSizeCore k j ∧
      ∀ idx < fullWatchSizeCore k j,
        k'.wstk[fullWatchOffCore k' j + idx]? = k.wstk[fullWatchOffCore k j + idx]? := by
    intro j hj hne
    obtain ⟨ho, hs⟩ := hwvec'_ne j hj hne
    refine ⟨hs, fun idx hidx => ?_⟩
    rw [ho]; dsimp only [k']; apply hout1
    by_cases hzl : fullWatchSizeCore k l = 0
    · rw [hzl, Nat.add_zero]; omega
    · rcases hlay.disjoint j l hj hl hne (by omega) (Nat.pos_of_ne_zero hzl) with ha | hb
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
  have hlay' : WatchStackLayout k' := by
    refine ⟨fun j hj => ?_, fun j hj hp => ?_, fun j1 j2 h1 h2 hne hp1 hp2 => ?_,
      fun j hj idx hi => ?_⟩
    · by_cases hjl : j = l
      · subst j; rw [hoff_self, hsz_self]; split <;> dsimp only [k', off0] <;> omega
      · obtain ⟨ho, hs⟩ := hwvec'_ne j hj hjl; rw [ho, hs]; exact hlay.bounds j hj
    · by_cases hjl : j = l
      · subst j; rw [hsz_self] at hp; rw [hoff_self]
        split
        · exfalso; dsimp only [off0] at *; omega
        · exact hlay.pos_off l hl (by dsimp only [off0] at *; omega)
      · obtain ⟨ho, hs⟩ := hwvec'_ne j hj hjl; rw [ho]; rw [hs] at hp; exact hlay.pos_off j hj hp
    · by_cases hj1 : j1 = l
      · subst j1; rw [hsz_self] at hp1 ⊢; rw [hoff_self]
        obtain ⟨ho2, hs2⟩ := hwvec'_ne j2 h2 (Ne.symm hne)
        rw [ho2]; rw [hs2] at hp2
        split
        · exfalso; omega
        · rcases hlay.disjoint l j2 hl h2 hne (by dsimp only [off0] at *; omega) hp2 with ha | hb
          · exact Or.inl (by dsimp only [off0] at *; omega)
          · exact Or.inr (by dsimp only [off0] at *; omega)
      · obtain ⟨ho1, hs1⟩ := hwvec'_ne j1 h1 hj1
        rw [ho1]; rw [hs1] at hp1
        by_cases hj2 : j2 = l
        · subst j2; rw [hsz_self] at hp2 ⊢; rw [hoff_self]
          split
          · exfalso; omega
          · rcases hlay.disjoint j1 l h1 hl hj1 hp1 (by dsimp only [off0] at *; omega) with ha | hb
            · exact Or.inl (by dsimp only [off0] at *; omega)
            · exact Or.inr (by dsimp only [off0] at *; omega)
        · obtain ⟨ho2, hs2⟩ := hwvec'_ne j2 h2 hj2
          rw [ho2, hs1, hs2]; rw [hs2] at hp2; exact hlay.disjoint j1 j2 h1 h2 hne hp1 hp2
    · by_cases hjl : j = l
      · subst j; rw [hsz_self] at hi; rw [hoff_self]
        split
        · exfalso; omega
        · exact hpre.ne_sentinel idx hi
      · obtain ⟨_, hs⟩ := hother j hj hjl
        rw [hs idx (by rw [← (hwvec'_ne j hj hjl).2]; exact hi)]
        exact hlay.no_sentinel j hj idx (by rw [← (hwvec'_ne j hj hjl).2]; exact hi)
  refine ⟨{ hck with wvec_len := hwvec'_len, wstk_len_arr := hwslen }, hlay', hother,
    hoff_self, hsz_self, ?_⟩
  rw [hoff_self, hsz_self]; split
  · rename_i hqe; rw [hqe, Nat.sub_self]; exact .empty
  · exact CompactPreBinSliceOk.relocate (k := { k with wstk := wstk' }) (k' := k')
      (p := fullWatchOffCore k l) (p' := off0) (fun _ _ => rfl) hpre

theorem compactBins_finalize {c : FullCfg} {old_cv ncv : Nat}
    {vals : List (BitVec 8)} {map inv : List (BitVec 32)} {F_cur : List (List Nat)}
    {k1 k2 : FullCoreState} (_hcv1 : k1.cur_vars = old_cv) (hcv2 : k2.cur_vars = old_cv)
    (hbij : CompactBijOk old_cv ncv vals map inv)
    (hlay1 : WatchStackLayout k1)
    (_hwvec2 : k2.wvec.length = 4 * c.max_vars)
    (hwstk2 : k2.wstk = k1.wstk) (hwlen2 : k2.wlen = k1.wlen)
    (hhi : ∀ l, 2 * ncv ≤ l → l < 2 * old_cv →
      fullWatchOffCore k2 l = 0 ∧ fullWatchSizeCore k2 l = 0)
    (hmap : ∀ nv < ncv, ∀ ov,
      (inv[nv]?.getD 0#32).toNat = ov → ov < old_cv →
      k2.wvec[4 * nv]? = k1.wvec[4 * ov]? ∧
      k2.wvec[4 * nv + 1]? = k1.wvec[4 * ov + 1]? ∧
      k2.wvec[4 * nv + 2]? = k1.wvec[4 * ov + 2]? ∧
      k2.wvec[4 * nv + 3]? = k1.wvec[4 * ov + 3]?)
    (hpre : ∀ ol < 2 * old_cv,
      CompactPreBinSliceOk ncv inv F_cur k1 ol (fullWatchOffCore k1 ol) (fullWatchSizeCore k1 ol)) :
    CompactUnmapBinsOk ncv inv F_cur k2 := by
  have hpair : ∀ l < 2 * ncv, ∃ ov < old_cv,
      (inv[l / 2]?.getD 0#32).toNat = ov ∧
      fullWatchOffCore k2 l = fullWatchOffCore k1 (2 * ov + l % 2) ∧
      fullWatchSizeCore k2 l = fullWatchSizeCore k1 (2 * ov + l % 2) := by
    intro l hl
    obtain ⟨ov, hov, _, _, hinv, _⟩ := hbij.inv_ok (l / 2) (by omega)
    have hov_lt : ov < 2 ^ 32 := by have := hbij.old_cv_lt; omega
    have hinv_nat : (inv[l / 2]?.getD 0#32).toNat = ov := by
      rw [hinv, Option.getD_some, bv32_ofNat_toNat hov_lt]
    obtain ⟨hw0, hw1, hw2, hw3⟩ := hmap (l / 2) (by omega) ov hinv_nat hov
    refine ⟨ov, hov, hinv_nat, ?_, ?_⟩
    · unfold fullWatchOffCore
      rcases Nat.mod_two_eq_zero_or_one l with hm | hm
      · rw [hm, Nat.add_zero, show 2 * l = 4 * (l / 2) by omega,
          show 2 * (2 * ov) = 4 * ov by omega, hw0]
      · rw [hm, show 2 * l = 4 * (l / 2) + 2 by omega,
          show 2 * (2 * ov + 1) = 4 * ov + 2 by omega, hw2]
    · unfold fullWatchSizeCore
      rcases Nat.mod_two_eq_zero_or_one l with hm | hm
      · rw [hm, show 2 * l + 1 = 4 * (l / 2) + 1 by omega,
          show 2 * (2 * ov + 0) + 1 = 4 * ov + 1 by omega, hw1]
      · rw [hm, show 2 * l + 1 = 4 * (l / 2) + 3 by omega,
          show 2 * (2 * ov + 1) + 1 = 4 * ov + 3 by omega, hw3]
  have hncv_le := hbij.ncv_le
  have hlay2 : WatchStackLayout k2 := by
    refine ⟨fun l hl => ?_, fun l hl hp => ?_, fun l1 l2 h1 h2 hne hp1 hp2 => ?_,
      fun l hl idx hi => ?_⟩
    · by_cases hln : l < 2 * ncv
      · obtain ⟨ov, hov, _, ho, hs⟩ := hpair l hln
        rw [ho, hs, hwlen2]; exact hlay1.bounds (2 * ov + l % 2) (by omega)
      · obtain ⟨ho, hs⟩ := hhi l (by omega) (by omega)
        rw [ho, hs]; exact Nat.zero_le _
    · by_cases hln : l < 2 * ncv
      · obtain ⟨ov, hov, _, ho, hs⟩ := hpair l hln
        rw [hs] at hp; rw [ho]; exact hlay1.pos_off (2 * ov + l % 2) (by omega) hp
      · rw [(hhi l (by omega) (by omega)).2] at hp; omega
    · by_cases hl1 : l1 < 2 * ncv
      · by_cases hl2 : l2 < 2 * ncv
        · obtain ⟨ov1, hov1, hin1, ho1, hs1⟩ := hpair l1 hl1
          obtain ⟨ov2, hov2, hin2, ho2, hs2⟩ := hpair l2 hl2
          rw [hs1] at hp1; rw [hs2] at hp2; rw [ho1, hs1, ho2, hs2]
          have hol_ne : 2 * ov1 + l1 % 2 ≠ 2 * ov2 + l2 % 2 := by
            intro heq
            have hd : ov1 = ov2 := by omega
            have hm : l1 % 2 = l2 % 2 := by omega
            have hlv := hbij.inv_inj (nv1 := l1 / 2) (nv2 := l2 / 2)
              (by omega) (by omega) (by rw [hin1, hin2, hd])
            omega
          exact hlay1.disjoint _ _ (by omega) (by omega) hol_ne hp1 hp2
        · rw [(hhi l2 (by omega) (by omega)).2] at hp2; omega
      · rw [(hhi l1 (by omega) (by omega)).2] at hp1; omega
    · by_cases hln : l < 2 * ncv
      · obtain ⟨ov, hov, _, ho, hs⟩ := hpair l hln
        rw [ho, hwstk2]; rw [hs] at hi
        exact hlay1.no_sentinel (2 * ov + l % 2) (by omega) idx hi
      · rw [(hhi l (by omega) (by omega)).2] at hi; omega
  refine ⟨hlay2, fun l h1 h2 => (hhi l h1 (hcv2 ▸ h2)).2, fun l hl => ?_⟩
  obtain ⟨ov, hov, hin, ho, hs⟩ := hpair l hl
  rw [ho, hs]
  have hun : compactUnmapLit inv l = 2 * ov + l % 2 := by
    unfold compactUnmapLit; rw [hin]
  exact CompactUnmapBinSliceOk.of_pre hun
    (CompactPreBinSliceOk.relocate (k := k1) (k' := k2)
      (fun _ _ => by rw [hwstk2]) (hpre (2 * ov + l % 2) (by omega)))

/-- Prefix compaction invariant on `ar[0 ..< dst)` for `full_compact_arena`. -/
structure CompactArenaPrefix (c : FullCfg) (ncv : Nat) (inv : List (BitVec 32))
    (F_cur : List (List Nat)) (ar : List (BitVec 32)) (dst : Nat) : Prop where
  len_ok : dst = 0 ∨ 3 ≤ dst
  dst_le : dst ≤ ar.length
  refs_wf : ∀ r ∈ fullArenaScanRefs ar dst 0 dst,
    r + 3 ≤ dst ∧ 3 ≤ (ar[r + 2]?.getD 0#32).toNat ∧
    r + 3 + (ar[r + 2]?.getD 0#32).toNat ≤ fullArenaNextOff ar dst r ∧
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

theorem compactArenaPrefix_zero {c : FullCfg} {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {ar : List (BitVec 32)} :
    CompactArenaPrefix c ncv inv F_cur ar 0 :=
  ⟨Or.inl rfl, Nat.zero_le _,
   fun _ hr => by simp [fullArenaScanRefs] at hr,
   fun _ hr => by simp [fullArenaScanRefs] at hr,
   fun _ hr => by simp [fullArenaScanRefs] at hr,
   fun _ hr => by simp [fullArenaScanRefs] at hr,
   fun _ hr => by simp [fullArenaScanRefs] at hr,
   fun _ hr => by simp [fullArenaScanRefs] at hr⟩

theorem compactArenaPrefix_congr {c : FullCfg} {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {ar ar' : List (BitVec 32)} {dst : Nat}
    (h : CompactArenaPrefix c ncv inv F_cur ar dst) (hlen' : dst ≤ ar'.length)
    (hpre : ∀ i < dst, ar'[i]? = ar[i]?) : CompactArenaPrefix c ncv inv F_cur ar' dst := by
  have hnxt : ∀ r ∈ fullArenaScanRefs ar dst 0 dst,
      fullArenaNextOff ar' dst r = fullArenaNextOff ar dst r := fun r hr => by
    have hwf := h.refs_wf r hr
    have hsh := h.no_shrk r hr
    have hbd : r + 3 + (ar[r + 2]?.getD 0#32).toNat ≤ dst := by omega
    have ha0 := hpre r (by omega)
    have ha2 := hpre (r + 2) (by omega)
    unfold fullArenaNextOff
    simp only [show ¬ (r + 3 > dst) by omega, ↓reduceIte, ha0, ha2,
      show ¬ (r + 3 + (ar[r + 2]?.getD 0#32).toNat > dst) by omega, hsh, ne_eq,
      not_true_eq_false]
  have hrefs : fullArenaScanRefs ar' dst 0 dst = fullArenaScanRefs ar dst 0 dst :=
    fullArenaScanRefs_congr hnxt
  have hlits_eq : ∀ r ∈ fullArenaScanRefs ar dst 0 dst,
      ((ar'.drop (r + 3)).take (ar'[r + 2]?.getD 0#32).toNat).map BitVec.toNat =
      ((ar.drop (r + 3)).take (ar[r + 2]?.getD 0#32).toNat).map BitVec.toNat := fun r hr => by
    have hwf := h.refs_wf r hr
    rw [hpre (r + 2) (by omega)]
    congr 1
    refine List.ext_getElem (by simp; have := h.dst_le; omega) fun j hj1 _ => ?_
    have hj : j < (ar[r + 2]?.getD 0#32).toNat := by simp at hj1; omega
    simp only [List.getElem_take, List.getElem_drop]
    have hp := hpre (r + 3 + j) (by omega)
    rw [List.getElem?_eq_getElem (by omega : r + 3 + j < ar'.length),
      List.getElem?_eq_getElem (by have := h.dst_le; omega : r + 3 + j < ar.length)] at hp
    exact Option.some.inj hp
  refine ⟨h.len_ok, hlen', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr; rw [hrefs] at hr; have hwf := h.refs_wf r hr
    rwa [hnxt r hr, hpre (r + 2) (by omega)]
  · intro r hr; rw [hrefs] at hr; have hr3 := (h.refs_wf r hr).1
    rw [hpre r (by omega)]; exact h.no_shrk r hr
  · intro r hr; rw [hrefs] at hr; have hr3 := (h.refs_wf r hr).1
    rw [hpre r (by omega)]; exact h.no_garb r hr
  · intro r hr j hj; rw [hrefs] at hr; have hwf := h.refs_wf r hr
    rw [hpre (r + 2) (by omega)] at hj
    rw [hpre (r + 3 + j) (by omega)]; exact h.lits_lt r hr j hj
  · intro r hr; rw [hrefs] at hr; rw [hlits_eq r hr]; exact h.nodup r hr
  · intro r hr; rw [hrefs] at hr; rw [hlits_eq r hr]; exact h.entails r hr

theorem compactArenaPrefix_append {c : FullCfg} {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {ar ar' : List (BitVec 32)} {dst sz : Nat}
    (h : CompactArenaPrefix c ncv inv F_cur ar dst) (hsz3 : 3 ≤ sz)
    (hlen' : dst + 3 + sz ≤ ar'.length) (hpre : ∀ i < dst, ar'[i]? = ar[i]?)
    (hnoshrk : (ar'[dst]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hnogarb : (ar'[dst]?.getD 0#32 &&& 0x00080000#32) = 0#32)
    (hsz_eq : (ar'[dst + 2]?.getD 0#32).toNat = sz)
    (hlits_lt : ∀ j < sz, (ar'[dst + 3 + j]?.getD 0#32).toNat < 2 * ncv)
    (hnodup : ((((ar'.drop (dst + 3)).take sz).map BitVec.toNat).map (· / 2)).Nodup)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause
      ((((ar'.drop (dst + 3)).take sz).map BitVec.toNat).map (compactUnmapLit inv)))) :
    CompactArenaPrefix c ncv inv F_cur ar' (dst + 3 + sz) := by
  have hc := compactArenaPrefix_congr h (by omega) hpre
  have hlast : dst = 0 ∨
      ∃ r ∈ fullArenaScanRefs ar' dst 0 dst, fullArenaNextOff ar' dst r = dst := by
    rcases hc.len_ok with hz | h3
    · exact Or.inl hz
    · exact Or.inr (fullArenaScanRefs_last (by omega) h3 fun r hr => (hc.refs_wf r hr).2.2.2.2)
  have hnxt_ext : ∀ r ∈ fullArenaScanRefs ar' dst 0 dst,
      fullArenaNextOff ar' (dst + 3 + sz) r = fullArenaNextOff ar' dst r := fun r hr => by
    have hwf := hc.refs_wf r hr
    have hsh := hc.no_shrk r hr
    unfold fullArenaNextOff
    simp only [show ¬ (r + 3 > dst) by omega, show ¬ (r + 3 > dst + 3 + sz) by omega, ↓reduceIte,
      show ¬ (r + 3 + (ar'[r + 2]?.getD 0#32).toNat > dst) by omega,
      show ¬ (r + 3 + (ar'[r + 2]?.getD 0#32).toNat > dst + 3 + sz) by omega,
      hsh, ne_eq, not_true_eq_false]
  have hrefs : fullArenaScanRefs ar' (dst + 3 + sz) 0 (dst + 3 + sz) =
      fullArenaScanRefs ar' dst 0 dst ++ [dst] :=
    fullArenaScanRefs_eq_of_prefix hsz3 hnoshrk hsz_eq
      (fun r hr => (hc.refs_wf r hr).2.2.2.2) hlast hnxt_ext
  refine ⟨Or.inr (by omega), hlen', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | hreq
    · have hwf := hc.refs_wf r hr; rw [hnxt_ext r hr]
      exact ⟨by omega, hwf.2.1, hwf.2.2.1, by omega,
        Or.inr (by rcases hwf.2.2.2.2 with h1 | h1 <;> omega)⟩
    · subst r
      have hnxt_d : fullArenaNextOff ar' (dst + 3 + sz) dst = dst + 3 + sz := by
        unfold fullArenaNextOff
        simp only [show ¬ (dst + 3 > dst + 3 + sz) by omega, ↓reduceIte, hsz_eq,
          show ¬ (dst + 3 + sz > dst + 3 + sz) by omega, hnoshrk, ne_eq, not_true_eq_false]
      rw [hsz_eq, hnxt_d]
      exact ⟨by omega, hsz3, by omega, Nat.le_refl _, Or.inl rfl⟩
  · intro r hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact hc.no_shrk r hr
    · exact hnoshrk
  · intro r hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact hc.no_garb r hr
    · exact hnogarb
  · intro r hr j hj; rw [hrefs, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact hc.lits_lt r hr j hj
    · rw [hsz_eq] at hj; exact hlits_lt j hj
  · intro r hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact hc.nodup r hr
    · rw [hsz_eq]; exact hnodup
  · intro r hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact hc.entails r hr
    · rw [hsz_eq]; exact hent

theorem compactArenaPrefix_to_ok {c : FullCfg} {ncv : Nat} {inv : List (BitVec 32)}
    {F_cur : List (List Nat)} {k : FullCoreState}
    (h : CompactArenaPrefix c ncv inv F_cur k.arena k.arena_len)
    (hlen_ar : k.arena.length = c.arena_cap) : CompactArenaOk c ncv inv F_cur k := by
  refine ⟨h.len_ok, h.refs_wf, h.no_shrk, ?_, ?_, h.nodup, h.entails⟩
  · intro r hr; unfold fullArenaClauseGarbCore fullArenaHdrCore
    simp [h.no_garb r hr]
  · intro r hr l hl
    have hwf := h.refs_wf r hr
    have hbd : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length := by
      have := h.dst_le; unfold fullArenaClauseSizeCore; omega
    obtain ⟨j, hj, rfl⟩ := (mem_fullArenaClauseLitsCore_iff hbd).mp hl
    have hj' : j < (k.arena[r + 2]?.getD 0#32).toNat := hj
    have h1 := h.lits_lt r hr j hj'
    rwa [List.getElem?_eq_getElem (by omega : r + 3 + j < k.arena.length), Option.getD_some] at h1

theorem level0_vals_false_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {l : Nat} (hlt : l < 2 * k.cur_vars) (hfals : k.vals[l]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1]) := by
  obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hlt).mp hfals
  have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
  rwa [heq] at hs

theorem compactArena_entails_kept {F_cur : List (List Nat)} {olits kept : List Nat} {old_cv : Nat}
    (horig : (cnfOfClauses F_cur).EntailsClause (cnfClause olits))
    (hsub : ∀ l ∈ olits, l ∈ kept ∨
      (l < 2 * old_cv ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1]))) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause kept) := by
  refine CNF.entails_clause_def.mpr fun α hα => ?_
  have h1 := CNF.entails_clause_def.mp horig α hα
  rw [clause_sat_cnfClause_iff] at h1 ⊢
  obtain ⟨l, hl, hev⟩ := h1
  rcases hsub l hl with hin | ⟨_, hunit⟩
  · exact ⟨l, hin, hev⟩
  · have hu := CNF.entails_clause_def.mp hunit α hα
    rw [clause_sat_cnfClause_iff] at hu
    obtain ⟨l', hm', hv'⟩ := hu
    rw [List.mem_singleton] at hm'; subst hm'
    have hvar : litVar (l ^^^ 1) = litVar l := fullInv_var_xor1 l
    have hsign : litSign (l ^^^ 1) = !litSign l := litSign_litNeg l
    rw [hvar, hsign] at hv'
    rw [hev] at hv'; cases hls : litSign l <;> simp_all

/-! ## 4. `20`-row `compactSpecTable`, `compactEnv`, & `Spec` contracts -/

/-! ### Owned `13` `FullM4Compact` `Spec` contracts -/

def fullCompactNeededSpec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.cur_level < 2 ^ 64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ res : Bool,
      (res = true → s.core.cur_level = 0 ∧ s.core.dense_mode = 0#64 ∧ 128 ≤ s.core.cur_vars) →
      Q (res, ()) m

def fullCompactFlushSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → s'.core.cur_level = 0 ∧ s'.core.propagated = s'.core.trail_end ∧
        s'.core.oom = 0#64 ∧ s'.core.unflushed = 0#64 ∧ s'.core.inconsistent = 0#64) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullCompactMarkLiveSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ ws1' m',
      let s' : FullState := { s with scratch := { s.scratch with work_stk1 := ws1' } }
      FullSparseInvW c F0 F_cur s' → (FullMem c s' ⋆ R) m' → Q () m'

def fullCompactAssignMapSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ ncv ws1' ws2' m',
      let s' : FullState :=
        { s with scratch := { s.scratch with work_stk1 := ws1', work_stk2 := ws2' } }
      s'.LengthsOk c →
      CompactBijOk s.core.cur_vars ncv.toNat s.core.vals ws1' ws2' →
      (FullMem c s' ⋆ R) m' → Q (ncv, ()) m'

def fullCompactRecordExtSpec : Spec [i64, i64, i64] [] := fun (h, old_cv, ncv, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧
    old_cv.toNat = s.core.cur_vars ∧ ncv.toNat ≤ old_cv.toNat ∧
    s.scratch.extend_len ≤ c.extend_cap ∧ (FullMem c s ⋆ R) m ∧
    ∀ ext' elen' m',
      let s' : FullState :=
        { s with scratch := { s.scratch with extend_stk := ext', extend_len := elen' } }
      s'.LengthsOk c → elen' ≤ c.extend_cap → (FullMem c s' ⋆ R) m' → Q () m'

def fullCompactBinsSpec : Spec [i64, i64, i64] [] := fun (h, old_cv, ncv, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧
    old_cv.toNat = s.core.cur_vars ∧ ncv.toNat ≤ old_cv.toNat ∧
    CompactBijOk old_cv.toNat ncv.toNat s.core.vals s.scratch.work_stk1 s.scratch.work_stk2 ∧
    (FullMem c s ⋆ R) m ∧
    ∀ wvec' wstk' wu' nb' m',
      let s' : FullState :=
        { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu',
                                       num_binary := nb' } }
      s'.LengthsOk c →
      CompactUnmapBinsOk ncv.toNat s.scratch.work_stk2 F_cur s'.core →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullCompactArenaSpec : Spec [i64, i64] [i64] := fun (h, old_cv, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ncv : Nat) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ ExtUnsatSound F0 old_cv.toNat F_cur ∧
    FullArenaClausesInv c F_cur s.core ∧ FullArenaVarsNodup s ∧
    s.core.dense_mode = 0#64 ∧ s.core.cur_level = 0 ∧
    old_cv.toNat = s.core.cur_vars ∧ ncv ≤ old_cv.toNat ∧
    CompactBijOk old_cv.toNat ncv s.core.vals s.scratch.work_stk1 s.scratch.work_stk2 ∧
    (∀ l < 2 * old_cv.toNat, s.core.vals[l]?.getD 0#8 = 0#8 ∨
      s.core.vals[l]?.getD 0#8 = 1#8 ∨ s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
    (∀ l < 2 * old_cv.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8 →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1])) ∧
    CompactUnmapBinsOk ncv s.scratch.work_stk2 F_cur s.core ∧
    (FullMem c s ⋆ R) m ∧
    ∀ st ar' al' fred' ni' nr' wvec' wstk' wlen' wu' nb' oom' ll' ws' m',
      let s' : FullState :=
        { core := { s.core with arena := ar', arena_len := al', arena_garbage := 0#64,
                                first_reducible := fred', num_irred := ni',
                                num_redundant := nr', wvec := wvec', wstk := wstk',
                                wlen := wlen', wusable := wu', num_binary := nb', oom := oom' }
          scratch := { s.scratch with last_learned := ll', wsort := ws' } }
      s'.LengthsOk c →
      (st = 0#64 ∨ st = 2#64 ∨ st = 3#64) →
      (st = 2#64 → F0.Unsat) →
      (st = 3#64 → oom' = 1#64) →
      CompactUnmapBinsOk ncv s.scratch.work_stk2 F_cur s'.core →
      CompactArenaOk c ncv s.scratch.work_stk2 F_cur s'.core →
      FullLastLearnedWf s' → (FullMem c s' ⋆ R) m' → Q (st, ()) m'

def fullCompactVarsSpec : Spec [i64, i64, i64] [] := fun (h, old_cv, ncv, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ old_cv.toNat = s.core.cur_vars ∧
    ncv.toNat ≤ old_cv.toNat ∧
    (∀ nv < ncv.toNat, (s.scratch.work_stk2[nv]?.getD 0#32).toNat < old_cv.toNat) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ c' vals' fl' lvl' rsns' ft0' fd0' sc' m',
      let s' : FullState :=
        { core := { s.core with vals := vals', flags := fl', lvl := lvl', rsns := rsns',
                                frame_trail := s.core.frame_trail.set 0 ft0',
                                frame_dec := s.core.frame_dec.set 0 fd0',
                                trail_end := 0, propagated := 0, cur_level := 0,
                                unflushed := 0#64, confl_ref := 0xFFFFFFFF#64, confl_type := 0#64,
                                cur_vars := ncv.toNat, unassigned := ncv }
          scratch := sc' }
      FullCfgCompat c c' → s'.LengthsOk c' → ft0' = 0#32 →
      (∀ l < 2 * c'.max_vars, l < 2 * old_cv.toNat → vals'[l]? = some 0#8) →
      FullExtScratchPres s s' →
      sc'.work_stk1 = s.scratch.work_stk1 → sc'.work_stk2 = s.scratch.work_stk2 →
      (FullMem c' s' ⋆ R) m' → Q () m'

def fullCompactSiftQSpec : Spec [i64, i64, i64, i64] [] :=
  fun (qs_ptr, ws_ptr, start, n, ()) m Q _ =>
  ∃ (qs ws : List (BitVec 32)) (R : Mem 64 → Prop),
    start.toNat ≤ n.toNat ∧ n.toNat ≤ ws.length ∧ n.toNat < 2 ^ 62 ∧
    (∀ k < n.toNat, (ws[k]?.getD 0#32).toNat < qs.length) ∧
    (array (t := i32) qs_ptr qs ⋆ array (t := i32) ws_ptr ws ⋆ R) m ∧
    ∀ ws' m', ws'.length = ws.length →
      (∀ k, n.toNat ≤ k → ws'[k]? = ws[k]?) →
      (∀ k < n.toNat, ∃ j < n.toNat, ws'[k]? = ws[j]?) →
      (array (t := i32) qs_ptr qs ⋆ array (t := i32) ws_ptr ws' ⋆ R) m' → Q () m'

def fullCompactVmtfSpec : Spec [i64, i64] [] := fun (h, ncv, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ ncv.toNat ≤ c.max_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ sc' m',
      let s' : FullState := { s with scratch := sc' }
      s'.LengthsOk c → FullExtScratchPres s s' →
      sc'.work_stk1 = s.scratch.work_stk1 → sc'.work_stk2 = s.scratch.work_stk2 →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullCompactSiftHSpec : Spec [i64, i64, i64, i64, i64] [] :=
  fun (sc_ptr, hp_ptr, ps_ptr, start, n, ()) m Q _ =>
    ∃ (sc : List (BitVec 64)) (hp ps : List (BitVec 32)) (R : Mem 64 → Prop),
      start.toNat < n.toNat ∧ n.toNat ≤ hp.length ∧ n.toNat ≤ ps.length ∧ n.toNat < 2 ^ 32 ∧
      (∀ k < n.toNat, (hp[k]?.getD 0#32).toNat < sc.length ∧
        (hp[k]?.getD 0#32).toNat < ps.length) ∧
      (array64 sc_ptr sc ⋆ array (t := i32) hp_ptr hp ⋆ array (t := i32) ps_ptr ps ⋆ R) m ∧
      ∀ hp' ps' m', hp'.length = hp.length → ps'.length = ps.length →
        (∀ k, n.toNat ≤ k → hp'[k]? = hp[k]?) →
        (∀ k < n.toNat, ∃ j < n.toNat, hp'[k]? = hp[j]?) →
        (array64 sc_ptr sc ⋆ array (t := i32) hp_ptr hp' ⋆ array (t := i32) ps_ptr ps' ⋆ R) m' →
        Q () m'

def fullCompactHeapSpec : Spec [i64, i64] [] := fun (h, ncv, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ ncv.toNat ≤ c.max_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ sc' m',
      let s' : FullState := { s with scratch := sc' }
      s'.LengthsOk c → FullExtScratchPres s s' →
      sc'.work_stk1 = s.scratch.work_stk1 → sc'.work_stk2 = s.scratch.work_stk2 →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullCompactSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r c' s' m',
      FullCfgCompat c c' → FullSparseInv c' F0 s' → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars ≤ s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → s'.core.cur_level = 0) →
      (FullMem c' s' ⋆ R) m' → Q (r, ()) m'

/-- Canonical `20`-row spec table: `13` owned `FullM4Compact` fns + `7` `FullSpec2` externs. -/
def compactSpecTable : List SpecEntry :=
  [ ⟨"full_compact_needed", [i64], [.bool], fullCompactNeededSpec, true⟩
  , ⟨"full_compact_flush", [i64], [i64], fullCompactFlushSpec, true⟩
  , ⟨"full_compact_mark_live", [i64], [], fullCompactMarkLiveSpec, true⟩
  , ⟨"full_compact_assign_map", [i64], [i64], fullCompactAssignMapSpec, true⟩
  , ⟨"full_compact_record_ext", [i64, i64, i64], [], fullCompactRecordExtSpec, true⟩
  , ⟨"full_compact_bins", [i64, i64, i64], [], fullCompactBinsSpec, true⟩
  , ⟨"full_compact_arena", [i64, i64], [i64], fullCompactArenaSpec, true⟩
  , ⟨"full_compact_vars", [i64, i64, i64], [], fullCompactVarsSpec, true⟩
  , ⟨"full_compact_sift_q", [i64, i64, i64, i64], [], fullCompactSiftQSpec, true⟩
  , ⟨"full_compact_vmtf", [i64, i64], [], fullCompactVmtfSpec, true⟩
  , ⟨"full_compact_sift_h", [i64, i64, i64, i64, i64], [], fullCompactSiftHSpec, true⟩
  , ⟨"full_compact_heap", [i64, i64], [], fullCompactHeapSpec, true⟩
  , ⟨"full_compact", [i64], [i64], fullCompactSpec, true⟩
  , ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  , ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  , ⟨"full_rewatch_arena", [i64, i64], [.bool], fullRewatchArenaSpec, true⟩
  , ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
  ]

def compactEnv : Env := Env.ofTable compactSpecTable

theorem compactSpecTable_nodup : (compactSpecTable.map SpecEntry.name).Nodup := by decide

theorem compactSpecTable_noExit : ∀ e ∈ compactSpecTable, e.noExit = true := by
  intro e he
  have hall : compactSpecTable.all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem compactSpecTable_sigs :
    (compactSpecTable.take 13).map (fun e => (e.name, e.as, e.rs)) =
      compact_fns.map (fun f => (f.name, f.as, f.rs)) :=
  rfl

theorem compactSpecTable_ext_sigs :
    (compactSpecTable.drop 13).map (fun e => ⟨e.name, e.as, e.rs⟩) = fullM4CompactExterns :=
  rfl

theorem compactEnv_noExit :
    ∀ f as bs xs m Q X X',
      compactEnv f as bs xs m Q X → compactEnv f as bs xs m Q X' :=
  Env.ofTable_noExit compactSpecTable_noExit

theorem compactEnv_row {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ compactSpecTable)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ xs m Q X, sp xs m Q X → compactEnv nm as bs xs m Q X :=
  fun xs m Q X hs =>
    Env.ofTable_of_mem (e := ⟨nm, as, bs, sp, true⟩) hmem compactSpecTable_nodup
      (hno xs m Q X hs)

/-! ## 5. Concrete `Mem 64` non-vacuity heap-building helpers -/

theorem cm_sep_append {P Q : Mem 64 → Prop} {a b : BitVec 64} {bs1 bs2 : List UInt8}
    (hb : b = a + BitVec.ofNat 64 bs1.length) (hlen : bs1.length + bs2.length ≤ 2 ^ 64)
    (h1 : P (bs1.At a)) (h2 : Q (bs2.At b)) : (P ⋆ Q) ((bs1 ++ bs2).At a) := by
  have heq := congrFun (Mem.At_append_sep bs1 bs2 a hlen) ((bs1 ++ bs2).At a)
  rw [← hb] at heq
  exact sep_mono2 (fun _ h => h ▸ h1) (fun _ h => h ▸ h2) _ (heq.mp rfl)

theorem cm_arr_pad_p {t : Ty} {a : BitVec 64} {xs : List (Val t)} (n pad : Nat)
    (hn : t.bytes * xs.length = n) (hbd : n + pad ≤ 2 ^ 64) :
    (bytesOf xs ++ List.replicate pad 0).length = n + pad ∧
    (array (t := t) a xs ⋆ region (a + BitVec.ofNat 64 n) pad)
      ((bytesOf xs ++ List.replicate pad 0).At a) :=
  ⟨by rw [List.length_append, bytesOf_length, List.length_replicate, hn],
    cm_sep_append (by rw [bytesOf_length, hn])
      (by rw [bytesOf_length, List.length_replicate]; omega)
      (array_bytes a xs (by omega)) ⟨List.replicate pad 0, List.length_replicate, rfl⟩⟩

theorem cm_arr_p {t : Ty} {a : BitVec 64} {xs : List (Val t)} (n : Nat)
    (hn : t.bytes * xs.length = n) (hbd : n ≤ 2 ^ 64) :
    (bytesOf xs).length = n ∧ array (t := t) a xs ((bytesOf xs).At a) :=
  ⟨by rw [bytesOf_length, hn], array_bytes a xs (by omega)⟩

theorem cm_arr64_p {a : BitVec 64} {xs : List (BitVec 64)} (n : Nat)
    (hn : 8 * xs.length = n) (hbd : n ≤ 2 ^ 64) :
    (bytes64 xs).length = n ∧ array64 a xs ((bytes64 xs).At a) :=
  ⟨by rw [bytes64_length, hn], array64_bytes a xs (by omega)⟩

theorem cm_join_pair {P Q : Mem 64 → Prop} {a b : BitVec 64} {bs1 bs2 : List UInt8}
    {n1 n2 : Nat} (h1 : bs1.length = n1 ∧ P (bs1.At a))
    (h2 : bs2.length = n2 ∧ Q (bs2.At b))
    (hb : b = a + BitVec.ofNat 64 n1) (hbd : n1 + n2 ≤ 2 ^ 64) :
    (bs1 ++ bs2).length = n1 + n2 ∧ (P ⋆ Q) ((bs1 ++ bs2).At a) :=
  ⟨by rw [List.length_append, h1.1, h2.1], cm_sep_append (h1.1 ▸ hb) (by omega) h1.2 h2.2⟩

theorem cm_sep_reorg {P Q : Mem 64 → Prop} {bs : List UInt8} {a : BitVec 64} {n : Nat}
    (h : bs.length = n ∧ P (bs.At a)) (himp : ∀ m, P m → Q m) : bs.length = n ∧ Q (bs.At a) :=
  ⟨h.1, himp _ h.2⟩

theorem cm_zip4 {A1 B1 A2 B2 A3 B3 A4 B4 : Mem 64 → Prop} {m : Mem 64}
    (h : ((((A1 ⋆ B1) ⋆ (A2 ⋆ B2)) ⋆ (A3 ⋆ B3)) ⋆ (A4 ⋆ B4)) m) :
    (((A1 ⋆ A3 ⋆ A4) ⋆ A2) ⋆ (B1 ⋆ B2 ⋆ B3 ⋆ B4)) m := sep_ac h

theorem cm_zip4_tail {C A2 P1 A5 B5 A6 B6 A7 B7 A8 B8 : Mem 64 → Prop} {m : Mem 64}
    (h : ((((((C ⋆ A2) ⋆ P1) ⋆ (A5 ⋆ B5)) ⋆ (A6 ⋆ B6)) ⋆ (A7 ⋆ B7)) ⋆ (A8 ⋆ B8)) m) :
    (C ⋆ (A2 ⋆ A5 ⋆ A6 ⋆ A7 ⋆ A8) ⋆ (P1 ⋆ B5 ⋆ B6 ⋆ B7 ⋆ B8)) m := sep_ac h

end LeanQbe.T.Examples.Kissat.FullM4Compact
