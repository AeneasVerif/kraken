/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Collect
public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersArena
public import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersMoveEnd
public import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersMoveSweep
public import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersSweep0
public import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersSweep1
public import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersWatch
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
public import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Examples.Kissat.Proof.Collect.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Arena Sweep Helpers & Inner-Loop WP (`Proof.Collect.WpSweep0`)

Shared invariants, pure compaction/reason-map lemmas, and the inner `PH_RSN` loop WP proof for
`LeanQbe.T.Examples.Kissat.Proof.Collect.WpSweep`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Collect

open Classical
open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Collect
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullKissatMath
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
open Kraken.Bedrock2.Test
open scoped FullArenaTactics M6Tactics1 M6Tactics2a

public section

theorem collect_fwd1_sweep {t : Ty} {Q : Post [t]} :
    (fun (r : Tup Val [t]) m' => Q (r.fst, ()) m') = Q := funext fun ⟨_, ⟨⟩⟩ => rfl

theorem full_mem_cast {c : FullCfg} {s1 s2 : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMem c s1 ⋆ R) m) (heq : s1 = s2) : (FullMem c s2 ⋆ R) m :=
  heq ▸ hm

abbrev swOp1 {t r : Ty} (code : OpCode [t] [r]) (a : Arg Val t) : Op Val [r] :=
  Op.mk code (a, ())

abbrev swOp2 {t r : Ty} (code : OpCode [t, t] [r]) (a b : Arg Val t) : Op Val [r] :=
  Op.mk code (a, b, ())

/-! ## 1. Loop & Join Invariants and Bundles -/

structure M6PreEqs (s sPre : FullState) : Prop where
  cv : sPre.core.cur_vars = s.core.cur_vars
  cl : sPre.core.cur_level = s.core.cur_level
  ft : sPre.core.frame_trail = s.core.frame_trail
  fd : sPre.core.frame_dec = s.core.frame_dec
  inc : sPre.core.inconsistent = s.core.inconsistent
  vals : sPre.core.vals = s.core.vals
  lvl : sPre.core.lvl = s.core.lvl
  trl : sPre.core.trl = s.core.trl
  tp : sPre.core.trail_pos = s.core.trail_pos
  te : sPre.core.trail_end = s.core.trail_end

abbrev M6SweepPostQ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen' wlen'
    wu' fred' ni' nr' nb' oom' sc' m'',
    let s' : FullState :=
      { core := { s.core with
          unassigned := unass', arena_len := alen', wlen := wlen', wusable := wu',
          arena_garbage := 0#64, first_reducible := fred', num_irred := ni', num_redundant := nr',
          num_binary := nb', unflushed := unfl', trail_end := te', oom := oom', vals := vals',
          flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp', wvec := wvec',
          arena := arena', wstk := wstk' }
        scratch := sc' }
    s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 3#64) →
    sc'.extend_len = s.scratch.extend_len → sc'.work_stk1 = s.scratch.work_stk1 →
    sc'.work_stk2 = s.scratch.work_stk2 → FullLastLearnedWf s' →
    FullWitnessInv c F0 F_cur s'.core → FullArenaVarsNodup s' →
    (r = 0#64 ∨ r = 1#64 → oom' = 0#64) →
    (0 < s.core.cur_level → r ≠ 1#64 ∧ r ≠ 2#64 ∧ vals' = s.core.vals ∧ lvl' = s.core.lvl ∧
      trl' = s.core.trl ∧ tp' = s.core.trail_pos ∧ te' = s.core.trail_end) →
    (r = 1#64 → s.core.cur_level = 0 ∧ s.core.trail_end < te') →
    (r = 2#64 → s.core.cur_level = 0 ∧ F0.Unsat) →
    (r = 3#64 → oom' ≠ 0#64) → (FullMem c s' ⋆ R) m'' → Q (r, ()) m''

def PreSweepValBrkInv (s : FullState) (fp : Nat) (m0 : Mem 64)
    (arg : Tup Val [i64, i64, .bool]) (mB : Mem 64) : Prop :=
  let (p, _cnt, pre_ok, ()) := arg
  mB = m0 ∧ p.toNat ≤ fp ∧ (pre_ok = true → CleanIrredChain s.core.arena 0 p.toNat)

def PreSweepValInv (s : FullState) (fp : Nat) (m0 : Mem 64)
    (arg : Tup Val [i64, i64]) (mL : Mem 64) : Prop :=
  let (p, _cnt, ()) := arg
  mL = m0 ∧ p.toNat ≤ fp ∧ CleanIrredChain s.core.arena 0 p.toNat

def PreSweepInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (arg : Tup Val [i64, i64]) (mP : Mem 64) : Prop :=
  let (start, _pre_irred, ()) := arg
  start.toNat ≤ s.core.arena_len ∧
  (0 < start.toNat → 0 < s.core.cur_level ∧ start.toNat < s.core.arena_len) ∧
  ∃ arPre : List (BitVec 32),
    let sPre : FullState := { s with core := { s.core with arena := arPre } }
    sPre.LengthsOk c ∧ FullWitnessInv c F0 F_cur sPre.core ∧ FullArenaVarsNodup sPre ∧
    (start.toNat < s.core.arena_len → start.toNat ∈ fullArenaClauseRefs sPre) ∧
    CompactPrefixOk c F_cur s sPre.core start.toNat ∧
    SweepReasonMapInv sPre.core sPre.core start.toNat start.toNat ∧
    (0 < s.core.cur_level →
      ∀ idx < sPre.core.trail_end,
        let v := (sPre.core.trl[idx]?.getD 0#32).toNat / 2
        let rsn := sPre.core.rsns[v]?.getD 0xFFFFFFFF#32
        0 < (sPre.core.lvl[v]?.getD 0#32).toNat →
        (rsn &&& 0x80000000#32) = 0#32 → start.toNat ≤ rsn.toNat →
        (fullArenaHdr sPre rsn.toNat &&& 0x00200000#32) ≠ 0#32) ∧
    (FullMem c sPre ⋆ R) mP

def M6SweepExitInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s sPre : FullState) (R : Mem 64 → Prop) (start : Nat)
    (arg : Tup Val [i64, i64, i64, i64, i64, .bool, .bool, .bool]) (mE : Mem 64) : Prop :=
  let (_src, dst, first_red, _ir, _rd, has_iar, unsat, new_unit, ()) := arg
  start ≤ dst.toNat ∧ dst.toNat ≤ s.core.arena_len ∧
  (has_iar = true → first_red ≠ 0xFFFFFFFF#64) ∧
  ∃ (sE : FullState) (rwE : Nat), M6SweepLike s sE ∧ sE.LengthsOk c ∧
    CompactPrefixOk c F_cur s sE.core dst.toNat ∧
    CompactPrefixOk c F_cur s sE.core start ∧ WatchStackLayout sE.core ∧
    (∀ l < 2 * sE.core.cur_vars,
      WatchSliceLtOk start F_cur sE.core l (fullWatchOff sE l) (fullWatchSize sE l)) ∧
    (start < dst.toNat →
      start ∈ fullArenaClauseRefsCore { sE.core with arena_len := dst.toNat }) ∧
    FullWitnessInv c F0 F_cur { sE.core with arena_len := dst.toNat } ∧
    M6FirstRedOk c F_cur s sPre sE start dst.toNat rwE first_red ∧
    (0 < s.core.cur_level →
      SweepReasonMapInv sPre.core sE.core sPre.core.arena_len dst.toNat) ∧
    (unsat = true → s.core.cur_level = 0 ∧ F0.Unsat) ∧
    (new_unit = true → s.core.cur_level = 0 ∧ s.core.trail_end < sE.core.trail_end) ∧
    (0 < s.core.cur_level → unsat = false ∧ new_unit = false ∧ sE.core.vals = s.core.vals ∧
      sE.core.lvl = s.core.lvl ∧ sE.core.trl = s.core.trl ∧ sE.core.trail_pos = s.core.trail_pos ∧
      sE.core.trail_end = s.core.trail_end) ∧
    (FullMem c sE ⋆ R) mE

def M6LastLearnedLoopInv (c : FullCfg) (sM : FullState) (R : Mem 64 → Prop)
    (dst irred redd : BitVec 64) (arg : Tup Val [i64]) (mL : Mem 64) : Prop :=
  let (li, ()) := arg
  li.toNat ≤ 16 ∧
  ∃ llL : List (BitVec 32), llL.length = 16 ∧
    (∀ j < li.toNat, llL[j]? = some 0xFFFFFFFF#32) ∧
    (FullMem c
      { core := { sM.core with arena_len := dst.toNat, arena_garbage := 0#64,
                               num_irred := irred, num_redundant := redd }
        scratch := { sM.scratch with last_learned := llL } } ⋆ R) mL

def M6RsnLoopInv (s sC : FullState) (arH : List (BitVec 32))
    (src dst st : Nat) (m0 : Mem 64) (arg : Tup Val [i32]) (mI : Mem 64) : Prop :=
  let (i, ()) := arg
  m0 = mI ∧ i.toNat ≤ st ∧
  (0 < s.core.cur_level → ∀ j < i.toNat,
    let lit := arH[dst + 3 + j]?.getD 0#32
    ¬ (lit.toNat / 2 < s.core.cur_vars ∧
       (0#32).slt ((sC.core.vals[lit.toNat]?.getD 0#8).signExtend 32) = true ∧
       sC.core.rsns[lit.toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src))

def M6RsnNextInv (s sC : FullState) (litI : BitVec 32) (src : Nat) (m0 : Mem 64)
    (_ : Tup Val []) (mN : Mem 64) : Prop :=
  m0 = mN ∧
  (0 < s.core.cur_level →
    ¬ (litI.toNat / 2 < s.core.cur_vars ∧
       (0#32).slt ((sC.core.vals[litI.toNat]?.getD 0#8).signExtend 32) = true ∧
       sC.core.rsns[litI.toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src))

/-! ## 2. Pure Pre-Sweep, Reason-Loop & Compaction Helpers -/

theorem sweep_pos_lits_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sL sC : FullState} {arH : List (BitVec 32)} {src dst st : BitVec 64}
    {old_sz : BitVec 32} {at_root : Bool}
    (hout : fullSweepCopyOutcome c F0 F_cur sL sC src dst old_sz at_root st)
    (hdec : at_root = false) (harL_len : sL.core.arena.length = c.arena_cap)
    (harC_len : sC.core.arena.length = c.arena_cap)
    (hsrc_fit : src.toNat + 3 + old_sz.toNat ≤ c.arena_cap) (hdst_src : dst.toNat ≤ src.toNat)
    (hsrc_lits : ((sL.core.arena.drop (src.toNat + 3)).take old_sz.toNat).map BitVec.toNat =
      fullArenaClauseLitsCore s0.core src.toNat)
    (hszH : (arH[dst.toNat + 2]?.getD 0#32).toNat = st.toNat)
    (hdropH : ((arH.drop (dst.toNat + 3)).take st.toNat).map BitVec.toNat =
      ((sC.core.arena.drop (dst.toNat + 3)).take st.toNat).map BitVec.toNat) :
    st.toNat = old_sz.toNat ∧
    sC.core.vals = sL.core.vals ∧ sC.core.lvl = sL.core.lvl ∧ sC.core.rsns = sL.core.rsns ∧
    sC.core.trl = sL.core.trl ∧ sC.core.trail_pos = sL.core.trail_pos ∧
    sC.core.trail_end = sL.core.trail_end ∧
    fullArenaClauseLitsCore { sC.core with arena := arH, arena_len := dst.toNat + 3 + st.toNat }
      dst.toNat = fullArenaClauseLitsCore s0.core src.toNat := by
  obtain ⟨hst_eq, hvC, _, hlC, hrC, htC, htpC, hteC, _, _, _, _, _, _, _, _, _, _, hcp⟩ :=
    hout.1 hdec
  have hst_n : st.toNat = old_sz.toNat := by rw [hst_eq, zext_toNat _ (by decide)]
  refine ⟨hst_n, hvC, hlC, hrC, htC, htpC, hteC, ?_⟩
  rw [show fullArenaClauseLitsCore
        { sC.core with arena := arH, arena_len := dst.toNat + 3 + st.toNat } dst.toNat =
        ((arH.drop (dst.toNat + 3)).take st.toNat).map BitVec.toNat by
      unfold fullArenaClauseLitsCore
      rw [show fullArenaClauseSizeCore
          { sC.core with arena := arH, arena_len := dst.toNat + 3 + st.toNat } dst.toNat =
          st.toNat from hszH],
    hdropH, ← hsrc_lits, hst_n]
  congr 1; apply List.ext_getElem (by simp [harL_len, harC_len]; omega)
  intro j hj1 _; have hj : j < old_sz.toNat := by simp [harC_len] at hj1; omega
  simp only [List.getElem_take, List.getElem_drop]
  have h1 := hcp j hj
  rw [List.getElem?_eq_getElem (by omega : dst.toNat + 3 + j < sC.core.arena.length),
    List.getElem?_eq_getElem (by omega : src.toNat + 3 + j < sL.core.arena.length)] at h1
  exact Option.some.inj h1

theorem sweep_rsn_hit_false_at_root {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sC : FullState} {litI : BitVec 32} {src dst : Nat}
    (hwC : FullWitnessInv c F0 F_cur { sC.core with arena_len := dst })
    (hcl0 : sC.core.cur_level = 0) (hsrc_lt : src < 0xFFFFFFFF)
    (hlitI_lt : litI.toNat < 2 * sC.core.cur_vars)
    (hlitI_v : litI.toNat < sC.core.vals.length)
    (hval_gt0 : (0#32).slt ((sC.core.vals[litI.toNat]'hlitI_v).signExtend 32) = true)
    (hrsn_eq : (sC.core.rsns[litI.toNat / 2]?.getD 0xFFFFFFFF#32).toNat = src) : False := by
  have hv1 : sC.core.vals[litI.toNat]?.getD 0#8 = 1#8 := by
    have hdom := hwC.vals_domain litI.toNat hlitI_lt
    have hg : sC.core.vals[litI.toNat]?.getD 0#8 = sC.core.vals[litI.toNat]'hlitI_v := by
      rw [List.getElem?_eq_getElem hlitI_v, Option.getD_some]
    rw [hg] at hdom ⊢; exact (bv8_gt0_of_dom hdom).1.mp hval_gt0
  obtain ⟨idx, hidx, hieq⟩ := (hwC.vals_true_iff litI.toNat hlitI_lt).mp hv1
  have hlv := hwC.lvl_le idx hidx
  dsimp only at hlv; rw [hcl0] at hlv
  have hr_ff := hwC.level0_rsn_none idx hidx (Nat.eq_zero_of_le_zero hlv)
  dsimp only at hr_ff; rw [hieq] at hr_ff; rw [hr_ff] at hrsn_eq; simp at hrsn_eq; omega

theorem m6_pre_val_all_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sPre : FullState} {fp : Nat} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) (hnd : FullArenaVarsNodup s)
    (hrmk : 0 < s.core.cur_level → FullReasonsMarked s)
    (hfp_pos : 0 < fp) (hfp_lt : fp < s.core.arena_len) (hc0 : CleanIrredChain s.core.arena 0 fp)
    {ar' : List (BitVec 32)} (har' : ar'.length = c.arena_cap)
    (htail : ∀ i, fp ≤ i → i < s.core.arena_len → ar'[i]? = s.core.arena[i]?)
    (hmatch : ∀ r ∈ fullArenaClauseRefsCore { s.core with arena_len := fp },
      (ar'[r]?.getD 0#32 &&& 0x00C80000#32) = 0#32 ∧ ar'[r + 2]? = s.core.arena[r + 2]? ∧
      ∀ j < (s.core.arena[r + 2]?.getD 0#32).toNat, ar'[r + 3 + j]? = s.core.arena[r + 3 + j]?)
    (hsPre : sPre = { s with core := { s.core with arena := ar' } }) :
    sPre.LengthsOk c ∧ FullWitnessInv c F0 F_cur sPre.core ∧ FullArenaVarsNodup sPre ∧
    (fp < s.core.arena_len → fp ∈ fullArenaClauseRefs sPre) ∧
    CompactPrefixOk c F_cur s sPre.core fp ∧ SweepReasonMapInv sPre.core sPre.core fp fp ∧
    (0 < s.core.cur_level → ∀ idx < sPre.core.trail_end,
      let v := (sPre.core.trl[idx]?.getD 0#32).toNat / 2
      let rsn := sPre.core.rsns[v]?.getD 0xFFFFFFFF#32
      0 < (sPre.core.lvl[v]?.getD 0#32).toNat →
      (rsn &&& 0x80000000#32) = 0#32 → fp ≤ rsn.toNat →
      (fullArenaHdr sPre rsn.toNat &&& 0x00200000#32) ≠ 0#32) := by
  subst hsPre
  obtain ⟨hfp_mem, hcmp', hrm', hw', hnd', _⟩ := prefix_cleared_ok hlen.core_ok hw hnd
    hfp_pos hfp_lt hc0 har' htail hmatch
  have hrm_self : SweepReasonMapInv { s.core with arena := ar' }
      { s.core with arena := ar' } fp fp := by
    intro idx hidx; have h1 := hrm' idx hidx; dsimp only at h1 ⊢
    split at h1
    · split; exact h1; contradiction
    · split
      · contradiction
      · split at h1
        · obtain ⟨ha, hb, hc, hd, he, hf, _⟩ := h1
          split; exact ⟨ha, hb, hc, hd, he, hf, rfl⟩; contradiction
        · split; contradiction; exact h1
  refine ⟨⟨{ hlen.core_ok with arena_len_arr := har' }, hlen.scratch_ok⟩, hw', hnd',
    fun _ => hfp_mem, hcmp', hrm_self, fun hpos idx hidx hlvl hlg hge => ?_⟩
  have hmk := hrmk hpos idx hidx hlvl hlg
  have hri := hw.reason_inv idx hidx (fun hff => by rw [hff] at hlg; simp at hlg)
  rw [ite_eq_right (fun h => h hlg)] at hri
  have hr_eq : ({ s.core with arena := ar' }).arena[
      (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat]? =
      s.core.arena[
        (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat]? :=
    htail _ hge (by have := (hw.arena.refs_wf _ hri.1).1; omega)
  unfold fullArenaHdr fullArenaHdrCore at hmk ⊢; dsimp only; rw [hr_eq]; exact hmk

theorem m6_sweep_rsn_hit_pos {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sL sC : FullState} {arH rsnsR : List (BitVec 32)} {litI : BitVec 32}
    {src nsrc st : Nat} {dst : BitVec 64}
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hsrc_ref : src ∈ fullArenaClauseRefs s0)
    (hnsrc64 : nsrc = fullArenaNextOff s0.core.arena s0.core.arena_len src)
    (hdst_src : dst.toNat ≤ src) (hsrc_lt8 : src < 0x80000000)
    (hrmL : SweepReasonMapInv s0.core sL.core src dst.toNat)
    (hhapp : SweepHappenedCore s0.core sL.core
      { sL.core with arena := arH, rsns := rsnsR, arena_len := dst.toNat + 3 + st }
      dst.toNat src)
    (hrs_eq : rsnsR = sC.core.rsns.set (litI.toNat / 2) (dst.setWidth 32))
    (hvC : sC.core.vals = s0.core.vals) (hrC : sC.core.rsns = sL.core.rsns)
    (hrsns_len : sC.core.rsns.length = c.max_vars) (hcv_le : s0.core.cur_vars ≤ c.max_vars)
    (hlitI_lt : litI.toNat < 2 * s0.core.cur_vars) (hlitI_v : litI.toNat < sC.core.vals.length)
    (hvg : (0#32).slt ((sC.core.vals[litI.toNat]'hlitI_v).signExtend 32) = true)
    (hrsn_eq : (sC.core.rsns[litI.toNat / 2]?.getD 0xFFFFFFFF#32).toNat = src) :
    SweepReasonMapInv s0.core { sC.core with arena := arH, rsns := rsnsR }
      nsrc (dst.toNat + 3 + st) := by
  have hv1 : s0.core.vals[litI.toNat]?.getD 0#8 = 1#8 := by
    have hdom := hw0.vals_domain litI.toNat hlitI_lt
    have hg : sC.core.vals[litI.toNat]?.getD 0#8 = sC.core.vals[litI.toNat]'hlitI_v := by
      rw [List.getElem?_eq_getElem hlitI_v, Option.getD_some]
    have h1 : (0#32).slt ((sC.core.vals[litI.toNat]?.getD 0#8).signExtend 32) = true := by rwa [hg]
    rw [hvC] at h1; exact (bv8_gt0_of_dom hdom).1.mp h1
  obtain ⟨idx0, hidx0, hieq0⟩ := (hw0.vals_true_iff litI.toNat hlitI_lt).mp hv1
  have hr_src_L : sL.core.rsns[(s0.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
      BitVec.ofNat 32 src := by
    apply BitVec.eq_of_toNat_eq; rw [bv32_ofNat_toNat (by omega), hieq0, ← hrC]; exact hrsn_eq
  have hr0_src : s0.core.rsns[(s0.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
      BitVec.ofNat 32 src := by
    have hm0' := hrmL idx0 hidx0; dsimp only at hm0'
    split at hm0'
    · rename_i hc1; rw [hr_src_L] at hm0'
      rcases hc1 with hff | hhi
      · rw [hff] at hm0'; have := congrArg BitVec.toNat hm0'
        rw [bv32_ofNat_toNat (by omega)] at this; simp at this; omega
      · rw [← hm0'] at hhi
        exact absurd ((bv32_lt_highbit_iff _).mp
          (by rw [bv32_ofNat_toNat (by omega)]; exact hsrc_lt8)) hhi
    · split at hm0'
      · rw [hr_src_L] at hm0'; have := hm0'.1; rw [bv32_ofNat_toNat (by omega)] at this; omega
      · rw [hr_src_L] at hm0'; exact hm0'.symm
  have hdst_sw : dst.setWidth 32 = BitVec.ofNat 32 dst.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, bv32_ofNat_toNat (by omega), Nat.mod_eq_of_lt (by omega)]
  refine SweepReasonMapInv.congr_rsns_arena rfl rfl
    (SweepReasonMapInv.keep_step (kL := sL.core) hw0 hsrc_ref hnsrc64 hdst_src hsrc_lt8 hrmL hhapp
      (fun idx hidx hne => ?_) (fun idx hidx heq_s => ?_))
  · have hne_idx : idx ≠ idx0 := fun heq => hne (heq ▸ hr0_src)
    have hve_ne : (s0.core.trl[idx]?.getD 0#32).toNat / 2 ≠ litI.toNat / 2 := fun hveq =>
      hne_idx (hw0.trail_vars_nodup idx idx0 hidx hidx0 (by rw [hveq, hieq0]))
    rw [hrs_eq, List.getElem?_set_ne (Ne.symm hve_ne), hrC]
  · have hid_eq := fullWitness_reason_unique hw0 hidx hidx0 hsrc_lt8 heq_s hr0_src
    subst hid_eq; rw [hrs_eq, hieq0, List.getElem?_set_self (by omega), Option.getD_some, hdst_sw]

theorem m6_hit_rsn_step {c : FullCfg} {_F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sPre _sL sC : FullState} {R : Mem 64 → Prop} {arH arR : List (BitVec 32)}
    {litI : BitVec 32} {dst nsrc st : BitVec 64}
    {mark_allowed : Bool} {mS : Mem 64}
    (hlenC0 : sC.LengthsOk c) (harR_len : arR.length = c.arena_cap)
    (hpreR : ∀ i < dst.toNat, arR[i]? = arH[i]?)
    (hbodyR : ∀ j, dst.toNat + 3 ≤ j → arR[j]? = arH[j]?)
    (hszR : (arR[dst.toNat + 2]?.getD 0#32).toNat = st.toNat)
    (hflR : (arR[dst.toNat]?.getD 0#32 &&& 0x00880000#32) = 0#32)
    (hredR : (arR[dst.toNat]?.getD 0#32 &&& 0x00400000#32) =
      (arH[dst.toNat]?.getD 0#32 &&& 0x00400000#32))
    (hdst_lt8 : dst.toNat < 0x80000000) (hvI_r' : litI.toNat / 2 < sC.core.rsns.length)
    (hcmpR : CompactPrefixOk c F_cur s
      { sC.core with arena := arR, rsns := sC.core.rsns.set (litI.toNat / 2) (dst.setWidth 32) }
      (dst.toNat + 3 + st.toNat))
    (hdst_inR : dst.toNat ∈ fullArenaClauseRefsCore
      { sC.core with
        arena := arR, rsns := sC.core.rsns.set (litI.toNat / 2) (dst.setWidth 32),
        arena_len := dst.toNat + 3 + st.toNat })
    (hr0_ok : s.core.cur_level = 0 → False)
    (hrmR : 0 < s.core.cur_level → SweepReasonMapInv sPre.core
      { sC.core with arena := arR, rsns := sC.core.rsns.set (litI.toNat / 2) (dst.setWidth 32) }
      nsrc.toNat (dst.toNat + 3 + st.toNat))
    (hmkR : 0 < s.core.cur_level → mark_allowed = true →
      ∀ idx < sPre.core.trail_end,
        ((sC.core.rsns.set (litI.toNat / 2) (dst.setWidth 32))[(sPre.core.trl[idx]?.getD
          0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat = dst.toNat →
        (arR[dst.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
        ∃ j < (arR[dst.toNat + 2]?.getD 0#32).toNat,
          let lit := (arR[dst.toNat + 3 + j]?.getD 0#32).toNat
          lit / 2 = (sPre.core.trl[idx]?.getD 0#32).toNat / 2 ∧ sC.core.vals[lit]?.getD 0#8 = 1#8)
    (hmS : (FullMem c { sC with
      core := { sC.core with
        arena := arR, rsns := sC.core.rsns.set (litI.toNat / 2) (dst.setWidth 32) } } ⋆ R) mS) :
    M6RsnBranchInv c F_cur s sPre sC R arH nsrc.toNat dst.toNat st.toNat mark_allowed () mS :=
  ⟨arR, _, harR_len, by rw [List.length_set, hlenC0.core_ok.rsns_len], hpreR, hbodyR, hszR, hflR,
   hredR, hcmpR, hdst_inR, fun idx _ hlt => by
      by_cases hve : (sPre.core.trl[idx]?.getD 0#32).toNat / 2 = litI.toNat / 2
      · rw [hve, List.getElem?_set_self hvI_r', Option.getD_some, BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt (by omega)] at hlt; omega
      · rw [List.getElem?_set_ne (Ne.symm hve)],
   fun hcl0 => absurd hcl0 hr0_ok, hrmR, hmkR, hmS⟩

theorem m6_watchSliceLtOk_congr {keep : Nat} {F_cur : List (List Nat)}
    {k1 k2 : FullCoreState} {l p rem : Nat}
    (hcv : k2.cur_vars = k1.cur_vars) (hwstk : k2.wstk = k1.wstk)
    (hrefs : ∀ r < keep, r ∈ fullArenaClauseRefsCore k1 → r ∈ fullArenaClauseRefsCore k2)
    (h : WatchSliceLtOk keep F_cur k1 l p rem) : WatchSliceLtOk keep F_cur k2 l p rem := by
  induction h with
  | empty => exact .empty
  | bin hw0 hbin hne hlt hent _ ih =>
    exact .bin (hwstk ▸ hw0) hbin hne (hcv ▸ hlt) hent ih
  | large hw0 hw1 hn hb hlt hmem _ ih =>
    exact .large (hwstk ▸ hw0) (hwstk ▸ hw1) hn hb hlt (hrefs _ hlt hmem) ih

theorem m6_binOnlyWatchesInv_congr {F_cur : List (List Nat)} {k1 k2 : FullCoreState}
    (hlay : WatchStackLayout k2) (hwv : k2.wvec = k1.wvec) (hwst : k2.wstk = k1.wstk)
    (hcv : k2.cur_vars = k1.cur_vars)
    (hlt : ∀ l < 2 * k1.cur_vars,
      WatchSliceLtOk 0 F_cur k1 l (fullWatchOffCore k1 l) (fullWatchSizeCore k1 l)) :
    BinOnlyWatchesInv F_cur k2 := by
  refine ⟨hlay, fun l hl => ?_⟩
  have h2 := m6_watchSliceLtOk_congr (k2 := k2) hcv hwst
    (fun _ hr => absurd hr (Nat.not_lt_zero _)) (hlt l (hcv ▸ hl))
  have hoff : fullWatchOffCore k2 l = fullWatchOffCore k1 l := by unfold fullWatchOffCore; rw [hwv]
  have hsz : fullWatchSizeCore k2 l = fullWatchSizeCore k1 l := by
    unfold fullWatchSizeCore; rw [hwv]
  rw [hoff, hsz]
  exact (WatchSliceLtOk.toBinOnly h2).relocate
    (by rw [CNF.entails_def]; exact fun _ h => h) (Nat.le_refl _) (fun _ _ => rfl)

theorem m6_rsn_post_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sPre sL sC : FullState} {R : Mem 64 → Prop} {arH arR rsnsR : List (BitVec 32)}
    {hdr0 : BitVec 32} {start dst nsrc src st fr' first_red : BitVec 64}
    {old_sz : BitVec 32} {rwL : Nat} {hcl_beq hia' new_unit mark_allowed : Bool}
    {mR : Mem 64}
    (hst_dst : start.toNat ≤ dst.toNat) (hal_le : s.core.arena_len ≤ c.arena_cap)
    (hdst_next_eq :
      (dst + (3 : BitVec 64) + (st.setWidth 32).setWidth 64).toNat = dst.toNat + 3 + st.toNat)
    (hnew3 : 3 ≤ st.toNat) (hfit_next : dst.toNat + 3 + st.toNat ≤ nsrc.toNat)
    (hnxt_le_al : nsrc.toNat ≤ s.core.arena_len)
    (hnxt_mem : nsrc.toNat = s.core.arena_len ∨ nsrc.toNat ∈ fullArenaClauseRefs sPre)
    (hlikeC : M6SweepLike s sC) (hlenC0 : sC.LengthsOk c) (hpre : M6PreEqs s sPre)
    (harC_len : sC.core.arena.length = c.arena_cap)
    (hcmpC : CompactPrefixOk c F_cur s sC.core dst.toNat)
    (hcmpC_st : CompactPrefixOk c F_cur s sC.core start.toNat) (hlayC : WatchStackLayout sC.core)
    (hltC : ∀ l < 2 * sC.core.cur_vars,
      WatchSliceLtOk start.toNat F_cur sC.core l (fullWatchOff sC l) (fullWatchSize sC l))
    (hstC_in : start.toNat < dst.toNat →
      start.toNat ∈ fullArenaClauseRefsCore { sC.core with arena_len := dst.toNat })
    (hfr_to_C : M6FirstRedOk c F_cur s sPre sC start.toNat dst.toNat rwL first_red)
    (htailC : ∀ i, nsrc.toNat ≤ i → i < s.core.arena_len →
      sC.core.arena[i]? = sPre.core.arena[i]?)
    (hrootL : M6SweepLoopRootOk c F0 F_cur s sL start.toNat dst.toNat new_unit)
    (hposL : M6SweepLoopPosOk s sPre sL src.toNat dst.toNat new_unit)
    (hdec_cl0 : ∀ b : Bool,
      hcl_beq = b ↔ (if b then s.core.cur_level = 0 else 0 < s.core.cur_level))
    (hout_ok0 : fullSweepCopyOutcome c F0 F_cur sL sC src dst old_sz hcl_beq st)
    (hpreH : ∀ i < dst.toNat, arH[i]? = sC.core.arena[i]?)
    (hbodyH : ∀ j, dst.toNat + 3 ≤ j → arH[j]? = sC.core.arena[j]?)
    (harH_0 : arH[dst.toNat]? = some (hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)))
    (hhdr_orig : hdr0 = fullArenaHdrCore sPre.core src.toNat)
    (hng_src : fullArenaClauseGarbCore sPre.core src.toNat = false)
    (harR_len : arR.length = c.arena_cap) (hrsnsR_len : rsnsR.length = c.max_vars)
    (hpreR : ∀ i < dst.toNat, arR[i]? = arH[i]?)
    (hbodyR : ∀ j, dst.toNat + 3 ≤ j → arR[j]? = arH[j]?)
    (hszR : (arR[dst.toNat + 2]?.getD 0#32).toNat = st.toNat)
    (hflR : (arR[dst.toNat]?.getD 0#32 &&& 0x00880000#32) = 0#32)
    (hredR : (arR[dst.toNat]?.getD 0#32 &&& 0x00400000#32) =
      (arH[dst.toNat]?.getD 0#32 &&& 0x00400000#32))
    (hcmpR : CompactPrefixOk c F_cur s { sC.core with arena := arR, rsns := rsnsR }
      (dst.toNat + 3 + st.toNat))
    (hdst_inR : dst.toNat ∈ fullArenaClauseRefsCore
      { sC.core with arena := arR, rsns := rsnsR, arena_len := dst.toNat + 3 + st.toNat })
    (hrsns_lt_dst : ∀ idx < sPre.core.trail_end,
      (rsnsR[(sPre.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat < dst.toNat →
      rsnsR[(sPre.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
        sC.core.rsns[(sPre.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32)
    (hrsns_r0 : s.core.cur_level = 0 → rsnsR = sC.core.rsns)
    (hrmR : 0 < s.core.cur_level → SweepReasonMapInv sPre.core
      { sC.core with arena := arR, rsns := rsnsR } nsrc.toNat (dst.toNat + 3 + st.toNat))
    (hmkR : 0 < s.core.cur_level → mark_allowed = true →
      ∀ idx < sPre.core.trail_end,
        (rsnsR[(sPre.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat = dst.toNat →
        (arR[dst.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
        ∃ j < (arR[dst.toNat + 2]?.getD 0#32).toNat,
          let lit := (arR[dst.toNat + 3 + j]?.getD 0#32).toNat
          lit / 2 = (sPre.core.trl[idx]?.getD 0#32).toNat / 2 ∧ sC.core.vals[lit]?.getD 0#8 = 1#8)
    (hmR : (FullMem c { sC with core := { sC.core with arena := arR, rsns := rsnsR } } ⋆ R) mR)
    (hmark_eq : mark_allowed = (!(decide (s.core.cur_level = 0)) &&
      (decide (first_red ≠ 0xFFFFFFFF#64) || decide ((hdr0 &&& 0x00400000#32) ≠ 0#32))))
    (hfr_some : fr' ≠ 0xFFFFFFFF#64 →
      (first_red = 0xFFFFFFFF#64 → fr' = dst ∧ (hdr0 &&& 0x00400000#32) ≠ 0#32) ∧
      (first_red ≠ 0xFFFFFFFF#64 → fr' = first_red))
    (hhia : hia' = true → fr' ≠ 0xFFFFFFFF#64) :
    M6SweepLoopInv c F0 F_cur s sPre R start.toNat
      nsrc (dst + (3 : BitVec 64) + (st.setWidth 32).setWidth 64) fr' hia' new_unit mR := by
  let sNext : FullState := { sC with core := { sC.core with arena := arR, rsns := rsnsR } }
  have hlenNext : sNext.LengthsOk c :=
    ⟨{ hlenC0.core_ok with arena_len_arr := harR_len, rsns_len := hrsnsR_len }, hlenC0.scratch_ok⟩
  have halC : sC.core.arena_len = s.core.arena_len := hlikeC.unchanged.2.1
  have hdst_cap : dst.toNat ≤ c.arena_cap := Nat.le_trans (by omega) hal_le
  have hst_al : start.toNat ≤ s.core.arena_len := by omega
  have hpre_CR : PrefixAgrees dst.toNat sC.core.arena arR := fun i hi =>
    (hpreR i hi).trans (hpreH i hi)
  obtain ⟨hcmpR_st, hkeepR_st⟩ := m6_refs_lt_prefix_transfer hcmpC_st (k' := sNext.core) rfl
    harC_len harR_len (by change start.toNat ≤ sC.core.arena_len; rw [halC]; exact hst_al)
    (by change start.toNat ≤ sNext.core.arena_len; rw [halC]; exact hst_al)
    (Nat.le_trans hst_al hal_le) (fun i hi => hpre_CR i (Nat.lt_of_lt_of_le hi hst_dst))
  have htr_C := arenaPrefix_preserves_compact (k := sC.core) (k' := sNext.core) hcmpC rfl
    harC_len harR_len hdst_cap hpre_CR
  have hlayNext : WatchStackLayout sNext.core := hlayC.with_wstk rfl rfl rfl rfl
  have hltNext : ∀ l < 2 * sNext.core.cur_vars,
      WatchSliceLtOk start.toNat F_cur sNext.core l (fullWatchOff sNext l)
        (fullWatchSize sNext l) := fun l hl =>
    m6_watchSliceLtOk_congr (k1 := sC.core) (k2 := sNext.core) rfl rfl
      (fun r hr hlt => hkeepR_st r hlt hr) (hltC l hl)
  have hstNext_in : start.toNat < dst.toNat + 3 + st.toNat →
      start.toNat ∈ fullArenaClauseRefsCore
        { sNext.core with arena_len := dst.toNat + 3 + st.toNat } := fun _ => by
    rcases Nat.eq_or_lt_of_le hst_dst with heq | hlt
    · rw [heq]; exact hdst_inR
    · have h1 := hstC_in hlt; rw [← htr_C.2.1] at h1
      exact (fullArenaClauseRefsCore_mono_prefix (by omega) htr_C.1.1 _ h1).1
  have hfr_next : ∃ rwN, M6FirstRedOk c F_cur s sPre sNext start.toNat
      (dst.toNat + 3 + st.toNat) rwN fr' := by
    by_cases hfe : fr' = 0xFFFFFFFF#64
    · exact ⟨0, .inl hfe⟩
    · obtain ⟨h_first, h_keep⟩ := hfr_some hfe
      by_cases hfr0_e : first_red = 0xFFFFFFFF#64
      · obtain ⟨hfr_eq, hred_ne⟩ := h_first hfr0_e; rw [hfr_eq]
        have hredR_ne : (arR[dst.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 := by
          rw [hredR, harH_0, Option.getD_some,
            (m6_bv32_nhdr_bits hdr0 (by
              unfold fullArenaClauseGarbCore at hng_src
              simpa [hhdr_orig, bne_iff_ne] using hng_src)).2.2.2.2.1]; exact hred_ne
        have hmv1 : MoveRangeChain arR dst.toNat (dst.toNat + 3 + st.toNat) (3 + st.toNat) := by
          have h1 := moveRangeChain_snoc (ar := arR) (a := dst.toNat) (p := dst.toNat)
            (p' := dst.toNat + 3 + st.toNat) .empty (by omega) hflR (by rw [hszR]; exact hnew3)
            (by rw [hszR])
          rwa [ite_eq_left hredR_ne, hszR, Nat.zero_add] at h1
        refine ⟨3 + st.toNat, .inr ⟨hst_dst, by omega, htr_C.1, by omega, hmv1, hdst_inR,
          ⟨fun hp r hr idx hidx heq => ?_⟩⟩⟩
        have hps : 0 < s.core.cur_level := hpre.cl ▸ hp
        have hmk_t : mark_allowed = true := by
          simp [hmark_eq, hred_ne, show s.core.cur_level ≠ 0 by omega]
        cases hr with
        | head => exact hmkR hps hmk_t idx hidx heq
        | tail _ _ _ _ hr_tl => exfalso; have := hr_tl.bounds; rw [hszR] at this; omega
      · rw [h_keep hfr0_e]
        rcases hfr_to_C with hbad | ⟨h1, h2, hcmpC_fr, hrw0, hmvC, hfr_inC, hmkC⟩
        · exact absurd hbad hfr0_e
        · have hmvR_pre : MoveRangeChain arR first_red.toNat dst.toNat rwL :=
            hmvC.congr (fun i _ hi => hpre_CR i hi)
          have hmvR_nxt := moveRangeChain_snoc hmvR_pre (p' := dst.toNat + 3 + st.toNat) (by omega)
            hflR (by rw [hszR]; exact hnew3) (by rw [hszR])
          rw [hszR] at hmvR_nxt
          have hcmpR_fr := (arenaPrefix_preserves_compact (k := sC.core) (k' := sNext.core)
            hcmpC_fr rfl harC_len harR_len (Nat.le_trans (Nat.le_of_lt h2) hdst_cap)
            (fun i hi => hpre_CR i (Nat.lt_trans hi h2))).1
          have hfr_inR : first_red.toNat ∈ fullArenaClauseRefsCore
              { sNext.core with arena_len := dst.toNat } := by rw [htr_C.2.1]; exact hfr_inC
          refine ⟨rwL + if (arR[dst.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 then
              3 + st.toNat else 0,
            .inr ⟨h1, by omega, hcmpR_fr, by omega, hmvR_nxt,
            (fullArenaClauseRefsCore_mono_prefix (by omega) htr_C.1.1 _ hfr_inR).1,
            ⟨fun hp r hr idx hidx heq => ?_⟩⟩⟩
          rcases refInChain_split hmvR_pre hr with hprev | hcur
          · have hprevC := hprev.congr (fun i _ hi => (hpre_CR i hi).symm)
            have hpb := hprevC.bounds
            have hrsn_ne := (hrsns_lt_dst idx hidx (by
              change (rsnsR[(sPre.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
                0xFFFFFFFF#32).toNat < dst.toNat
              rw [heq]; have := hpb.2; omega)).symm
            obtain ⟨ha, j, hj, hlv, hval⟩ :=
              hmkC.get hp r hprevC idx hidx (by rw [hrsn_ne]; exact heq)
            exact ⟨by rw [hpre_CR r (by omega)]; exact ha, j,
              by rw [hpre_CR (r + 2) (by omega)]; exact hj,
              by rw [hpre_CR (r + 3 + j) (by omega)]; exact hlv,
              by rw [hpre_CR (r + 3 + j) (by omega)]; exact hval⟩
          · cases hcur with
            | head =>
              have hps : 0 < s.core.cur_level := hpre.cl ▸ hp
              have hmk_t : mark_allowed = true := by
                simp [hmark_eq, hfr0_e, show s.core.cur_level ≠ 0 by omega]
              exact hmkR hps hmk_t idx hidx heq
            | tail _ _ _ _ hr_tl => exfalso; have := hr_tl.bounds; rw [hszR] at this; omega
  rcases hfr_next with ⟨rwN, hfrN⟩
  refine ⟨by rw [hdst_next_eq]; omega, by rw [hdst_next_eq]; exact hfit_next, hnxt_le_al,
    fun hlt => hnxt_mem.resolve_left (Nat.ne_of_lt hlt), hhia, sNext, rwN, hlikeC.of_ar_rsns,
    hlenNext, by rw [hdst_next_eq]; exact hcmpR, hcmpR_st, hlayNext, hltNext,
    fun hlt => by rw [hdst_next_eq] at hlt ⊢; exact hstNext_in hlt,
    by rw [hdst_next_eq]; exact hfrN,
    fun i hi1 hi2 => by
      have hi_g : dst.toNat + 3 ≤ i := by omega
      rw [hbodyR i hi_g, hbodyH i hi_g]; exact htailC i hi1 hi2,
    ⟨fun hcl0 => ?_⟩, ⟨fun hpos => ?_⟩, full_mem_cast hmR rfl⟩
  · obtain ⟨hwC, hbinC_f, hteC, _⟩ := hout_ok0.2 ((hdec_cl0 true).mpr hcl0)
    have hcl0C : sC.core.cur_level = 0 := hlikeC.unchanged.2.2.1.trans hcl0
    have hbinC : BinOnlyWatchesInv F_cur sC.core := m6_binOnly_of_full
      (by have := hlenC0.core_ok.wlen_le; have := hlenC0.core_ok.wstk_len_arr; omega) hbinC_f
    have hwC_dst : FullWitnessInv c F0 F_cur { sC.core with arena_len := dst.toNat } :=
      { hwC with
        arena := hcmpC.1
        watches := (hbinC.with_core (k' := { sC.core with arena_len := dst.toNat })
          rfl rfl rfl rfl).toModeWatchesInv
        reason_inv := fun i hi h => absurd (hwC.level0_rsn_none i hi (by
          have := hwC.lvl_le i hi; rw [hcl0C] at this; omega)) h
        reason_lit_mem := fun i hi h => absurd (hwC.level0_rsn_none i hi (by
          have := hwC.lvl_le i hi; rw [hcl0C] at this; omega)) h }
    rw [hdst_next_eq]
    have hwN := fullWitnessInv_append_root hwC_dst hbinC hcl0C
      (by simpa [sNext, hrsns_r0 hcl0] using hcmpR.1)
    have hkn : ({ sNext.core with arena_len := dst.toNat + 3 + st.toNat } : FullCoreState) =
        { { sC.core with arena := arR } with arena_len := dst.toNat + 3 + st.toNat } := by
      dsimp [sNext]; rw [hrsns_r0 hcl0]
    exact ⟨(hrootL.get hcl0).1, by rw [hkn]; exact hwN,
      Nat.le_trans (hrootL.get hcl0).2.2.1 hteC,
      fun hnu => Nat.lt_of_lt_of_le ((hrootL.get hcl0).2.2.2 hnu) hteC⟩
  · obtain ⟨_, hvC, _, hlC, _, htC, htpC, hteC, _⟩ := hout_ok0.1 ((hdec_cl0 false).mpr hpos)
    obtain ⟨hnu0, hv0, hl0, ht0, htp0, hte0, _⟩ := hposL.get hpos
    exact ⟨hnu0, hvC.trans hv0, hlC.trans hl0, htC.trans ht0, htpC.trans htp0,
      hteC.trans hte0, by rw [hdst_next_eq]; exact hrmR hpos⟩

/-! ## 3. Post-Loop, Move-Red & Exit Helpers -/

theorem m6_clear_fall_step {c : FullCfg} {F_cur : List (List Nat)} {s sPre sE : FullState}
    {R : Mem 64 → Prop} {first_red dst : Nat} {cp : BitVec 64} {m' : Mem 64}
    (hfr_cp : first_red ≤ cp.toNat) (hcp_lt : cp.toNat < dst) (hdst_cap : dst ≤ c.arena_cap)
    (hcap_lt : c.arena_cap < 2 * dimacsBound)
    {arL : List (BitVec 32)} {rwRem : Nat} (harL_l : arL.length = c.arena_cap)
    (hpreL : ∀ i, i < first_red → arL[i]? = sE.core.arena[i]?)
    (htailL : ∀ i, cp.toNat ≤ i → i < dst → arL[i]? = sE.core.arena[i]?)
    (hmvRem : MoveRangeChain sE.core.arena cp.toNat dst rwRem)
    (hcmpL : CompactPrefixOk c F_cur s { sE.core with arena := arL } dst)
    (hrmL : 0 < s.core.cur_level →
      SweepReasonMapInv sPre.core { sE.core with arena := arL } sPre.core.arena_len dst)
    (hrefsL : fullArenaClauseRefsCore { sE.core with arena := arL, arena_len := dst } =
      fullArenaClauseRefsCore { sE.core with arena_len := dst })
    (hcp_in : cp.toNat ∈ fullArenaClauseRefsCore { sE.core with arena := arL, arena_len := dst })
    {hdr sz : BitVec 32}
    (hhdr : hdr = arL[cp.toNat]'(by rw [harL_l]; omega))
    (hsz : sz = arL[cp.toNat + 2]'(by
      cases hmvRem with | empty => omega | step h3 => rw [harL_l]; omega))
    (hm' : (FullMem c { sE with core :=
      { sE.core with arena := arL.set cp.toNat (hdr &&& ~~~0x00200000#32) } } ⋆ R) m') :
    3 ≤ sz.toNat ∧ cp.toNat + 3 + sz.toNat ≤ dst ∧
    M6ClearFallInv c F_cur s sPre sE R first_red dst (cp + (3#64 + sz.setWidth 64)) m' := by
  have hdb : dimacsBound = 2 ^ 28 := rfl
  cases hmvRem with
  | empty => omega
  | @step _ _ _ h3 hfl hsz3 hfit hmv_nxt =>
    have hcp_ar := htailL cp.toNat (Nat.le_refl _) hcp_lt
    have hcp2_ar := htailL (cp.toNat + 2) (by omega) (by omega)
    have hhdr_s : sE.core.arena[cp.toNat]? = some hdr := by
      rw [← hcp_ar, hhdr]; exact List.getElem?_eq_getElem _
    have hsz_s : sE.core.arena[cp.toNat + 2]? = some sz := by
      rw [← hcp2_ar, hsz]; exact List.getElem?_eq_getElem _
    have hsz_eq : (sE.core.arena[cp.toNat + 2]?.getD 0#32).toNat = sz.toNat := by
      rw [hsz_s, Option.getD_some]
    rw [hsz_eq] at hfit hmv_nxt hsz3
    have hcp'_eq : (cp + (3#64 + sz.setWidth 64)).toNat = cp.toNat + 3 + sz.toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_add, show (3#64).toNat = 3 from rfl,
        zext_toNat (n := 64) sz (by decide),
        Nat.mod_eq_of_lt (by omega : 3 + sz.toNat < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : cp.toNat + (3 + sz.toNat) < 2 ^ 64), Nat.add_assoc]
    have hclr_bits := bv32_bit21_clear_pres hdr
    have hfl_hdr : (hdr &&& 0x00880000#32) = 0#32 := by rwa [hhdr_s, Option.getD_some] at hfl
    have hsh_hdr : (hdr &&& 0x00800000#32) = 0#32 := by
      have h1 : (hdr &&& (0x00880000#32 &&& 0x00800000#32)) = 0#32 := by
        rw [← BitVec.and_assoc, hfl_hdr, BitVec.zero_and]
      rwa [show (0x00880000#32 &&& 0x00800000#32) = 0x00800000#32 from rfl] at h1
    have hgb_hdr : (hdr &&& 0x00080000#32) = 0#32 := by
      have h1 : (hdr &&& (0x00880000#32 &&& 0x00080000#32)) = 0#32 := by
        rw [← BitVec.and_assoc, hfl_hdr, BitVec.zero_and]
      rwa [show (0x00880000#32 &&& 0x00080000#32) = 0x00080000#32 from rfl] at h1
    obtain ⟨hcmp', hrefs', hcl'⟩ := m6_set_hdr_at_ref_preserves hcmpL harL_l hdst_cap hcp_in
      (hclr_bits.2.trans hsh_hdr) (hclr_bits.1.trans hgb_hdr)
    refine ⟨hsz3, hfit, by rw [hcp'_eq]; omega, by rw [hcp'_eq]; exact hfit, _, _, by simp [harL_l],
      fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact hpreL i hi,
      fun i hi1 hi2 => by
        rw [hcp'_eq] at hi1; rw [List.getElem?_set_ne (by omega)]; exact htailL i (by omega) hi2,
      by rw [hcp'_eq]; exact hmv_nxt, hcmp',
      fun hpos => m6_set_hdr_preserves_srm hrefs' hcl' (hrmL hpos),
      hrefs'.trans hrefsL, fun hlt' => ?_, hm'⟩
    rw [hcp'_eq] at hlt' ⊢
    have hnx_new : fullArenaNextOff (arL.set cp.toNat (hdr &&& ~~~0x00200000#32)) dst cp.toNat =
        cp.toNat + 3 + sz.toNat := by
      have hsh' : ((arL.set cp.toNat (hdr &&& ~~~0x00200000#32))[cp.toNat]?.getD 0#32 &&&
          0x00800000#32) = 0#32 := by
        rw [List.getElem?_set_self (by rw [harL_l]; omega), Option.getD_some]
        exact hclr_bits.2.trans hsh_hdr
      have hsz' : ((arL.set cp.toNat (hdr &&& ~~~0x00200000#32))[cp.toNat + 2]?.getD 0#32).toNat =
          sz.toNat := by
        rw [List.getElem?_set_ne (by omega), hsz, List.getElem?_eq_getElem, Option.getD_some]
      dsimp only [fullArenaNextOff]; rw [hsz']
      simp only [show ¬ (cp.toNat + 3 > dst) by omega,
        show ¬ (cp.toNat + 3 + sz.toNat > dst) by omega, hsh', ↓reduceIte, ne_eq,
        not_true_eq_false]
    have hmem := fullArenaClauseRefs_next_or_end hcmp'.1 (hrefs' ▸ hcp_in)
    dsimp only at hmem; rw [hnx_new] at hmem; exact hmem.resolve_left (by omega)

theorem m6_first_red_mem_prefix {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {k1 k2 : FullCoreState} {fr dst : Nat}
    (hcmp1_fr : CompactPrefixOk c F_cur s k1 fr) (hcmp2 : CompactPrefixOk c F_cur s k2 dst)
    (har1 : k1.arena.length = c.arena_cap) (har2 : k2.arena.length = c.arena_cap)
    (hfr_dst : fr < dst) (hdst_cap : dst ≤ c.arena_cap)
    (hpre : ∀ i < fr, k2.arena[i]? = k1.arena[i]?)
    (hfr1 : fr ∈ fullArenaClauseRefsCore { k1 with arena_len := dst }) :
    fr ∈ fullArenaClauseRefsCore { k2 with arena_len := dst } := by
  by_cases hfr0 : fr = 0
  · rw [hfr0]; exact fullArenaClauseRefs_zero_mem hcmp2.1 (by dsimp; omega)
  · have hfr_pos : 0 < fr := Nat.pos_of_ne_zero hfr0
    have hcmp1_dst : CompactPrefixOk c F_cur s { k1 with arena_len := dst } fr :=
      (arenaPrefix_preserves_compact (k' := { k1 with arena_len := dst }) hcmp1_fr rfl
        har1 har1 (by omega) (fun _ _ => rfl)).1
    have hgo : ∀ fuel pos, pos ≤ fr → pos ∈ fullArenaClauseRefsCore { k1 with arena_len := dst } →
        pos ∈ fullArenaClauseRefsCore { k2 with arena_len := dst } →
        fr ∈ fullArenaScanRefs k1.arena dst pos fuel →
        fr ∈ fullArenaClauseRefsCore { k2 with arena_len := dst } := by
      intro fuel; induction fuel with
      | zero => intro _ _ _ _ h; simp [fullArenaScanRefs] at h
      | succ f ih =>
        intro pos hle hp1 hp2 hr
        unfold fullArenaScanRefs at hr; split at hr
        · simp only [List.mem_cons] at hr; rcases hr with rfl | hrest
          · exact hp2
          · rcases Nat.eq_or_lt_of_le hle with rfl | hlt
            · exact hp2
            · have hp1_fr := m6_refs_lt_compactPrefix hcmp1_dst (by dsimp only; omega) pos hp1 hlt
              have hwf := hcmp1_fr.1.refs_wf pos hp1_fr
              simp only [fullArenaClauseSizeCore] at hwf
              have hsh := (hcmp1_fr.2.1 pos hp1_fr).1; dsimp only [fullArenaHdrCore] at hsh
              have hnf : fullArenaNextOff k1.arena fr pos =
                  pos + 3 + (k1.arena[pos + 2]?.getD 0#32).toNat := by
                dsimp only [fullArenaNextOff]
                simp [show ¬ (pos + 3 > fr) by omega,
                  show ¬ (pos + 3 + (k1.arena[pos + 2]?.getD 0#32).toNat > fr) by omega, hsh]
              have hn_dst : fullArenaNextOff k1.arena dst pos =
                  pos + 3 + (k1.arena[pos + 2]?.getD 0#32).toNat := by
                dsimp only [fullArenaNextOff]
                simp [show ¬ (pos + 3 > dst) by omega,
                  show ¬ (pos + 3 + (k1.arena[pos + 2]?.getD 0#32).toNat > dst) by omega, hsh]
              have hnx_le : fullArenaNextOff k1.arena dst pos ≤ fr := by
                rw [hn_dst, ← hnf]; exact hwf.2.2.2.1
              have hnx_eq := fullArenaNextOff_congr_block (hpre pos hlt)
                (hpre (pos + 2) (by omega))
                fun k hk1 hk2 => hpre k (by rw [hn_dst] at hk2; rw [hnf] at hwf; omega)
              have hmem1_fr := fullArenaClauseRefs_next_or_end hcmp1_fr.1 hp1_fr
              dsimp only at hmem1_fr
              have hmem1 : fullArenaNextOff k1.arena dst pos ∈
                  fullArenaClauseRefsCore { k1 with arena_len := dst } := by
                rw [hn_dst, ← hnf]
                rcases hmem1_fr with he | hr'
                · rw [he]; exact hfr1
                · exact (fullArenaClauseRefsCore_mono_prefix (Nat.le_of_lt hfr_dst)
                    hcmp1_fr.1 _ hr').1
              have hmem2 := fullArenaClauseRefs_next_or_end hcmp2.1 hp2
              dsimp only at hmem2; rw [hnx_eq] at hmem2
              exact ih _ hnx_le hmem1 (hmem2.resolve_left (by omega)) hrest
        · simp at hr
    exact hgo dst 0 (Nat.zero_le _) ((fullArenaClauseRefsCore_mono_prefix (Nat.le_of_lt hfr_dst)
      hcmp1_fr.1 0 (fullArenaClauseRefs_zero_mem hcmp1_fr.1 (by dsimp only; omega))).1)
      (fullArenaClauseRefs_zero_mem hcmp2.1 (by dsimp; omega)) hfr1

theorem m6_post_move_shared {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sPre sL : FullState} {R : Mem 64 → Prop} {start : Nat} {dst first_red : BitVec 64}
    {new_unit unsat : Bool} {arM rsnsM : List (BitVec 32)} {scM : FullScratch} {mM : Mem 64}
    (hwPre : FullWitnessInv c F0 F_cur sPre.core) (hdk : 0 < start → sL.core.dense_mode = 0#64)
    (hlikeL : M6SweepLike s sL) (hlenL : sL.LengthsOk c)
    (hst_dst : start ≤ dst.toNat) (hst_al : start ≤ s.core.arena_len)
    (hdst_cap : dst.toNat ≤ c.arena_cap) (hpre : M6PreEqs s sPre)
    (harM_len : arM.length = c.arena_cap) (hrsM_len : rsnsM.length = c.max_vars)
    (hscM_len : scM.LengthsOk c) (hscM_el : scM.extend_len = sL.scratch.extend_len)
    (hscM_ws1 : scM.work_stk1 = sL.scratch.work_stk1)
    (hscM_ws2 : scM.work_stk2 = sL.scratch.work_stk2)
    (hpre_st : ∀ i < start, arM[i]? = sL.core.arena[i]?)
    (hcmpL_st : CompactPrefixOk c F_cur s sL.core start)
    (hcmpM : CompactPrefixOk c F_cur s { sL.core with arena := arM, rsns := rsnsM } dst.toNat)
    (hlayL : WatchStackLayout sL.core)
    (hltL : ∀ l < 2 * sL.core.cur_vars,
      WatchSliceLtOk start F_cur sL.core l (fullWatchOff sL l) (fullWatchSize sL l))
    (hstart0 : s.core.cur_level = 0 → start = 0)
    (hwE : FullWitnessInv c F0 F_cur { sL.core with arena_len := dst.toNat })
    (hunit : new_unit = true → s.core.cur_level = 0 ∧ s.core.trail_end < sL.core.trail_end)
    (hpos_eqs : 0 < s.core.cur_level → new_unit = false ∧ sL.core.vals = s.core.vals ∧
      sL.core.lvl = s.core.lvl ∧ sL.core.trl = s.core.trl ∧
      sL.core.trail_pos = s.core.trail_pos ∧ sL.core.trail_end = s.core.trail_end)
    (hrmM : 0 < s.core.cur_level →
      SweepReasonMapInv sPre.core { sL.core with arena := arM, rsns := rsnsM }
        sPre.core.arena_len dst.toNat)
    (hrsn_r0 : s.core.cur_level = 0 → ∀ idx < sL.core.trail_end,
      rsnsM[(sL.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32)
    (hstM_in : start < dst.toNat →
      start ∈ fullArenaClauseRefsCore
        { sL.core with
          arena := arM, rsns := rsnsM, first_reducible := first_red, arena_len := dst.toNat })
    (huns : unsat = true → s.core.cur_level = 0 ∧ F0.Unsat)
    (hmM : (FullMem c
      { core := { sL.core with arena := arM, rsns := rsnsM, first_reducible := first_red },
        scratch := scM } ⋆ R) mM) :
    M6PostMoveInv c F0 F_cur s R start dst unsat new_unit () mM := by
  let sM0 : FullState := { sL with core := { sL.core with arena := arM, rsns := rsnsM } }
  let sM : FullState :=
    { core := { sL.core with arena := arM, rsns := rsnsM, first_reducible := first_red },
      scratch := scM }
  have hu := hlikeL.unchanged
  have hpostM : M6PostLike s sM := by
    rcases hlikeL with ⟨v, f, l, _, t, tp, te, u, uf, wv, ws, _, wl, wu, nb, o, _, _, rfl⟩
    exact ⟨v, f, l, rsnsM, t, tp, te, u, uf, wv, ws, arM, wl, wu, first_red, nb, o, rfl⟩
  have hlenM : sM.LengthsOk c :=
    ⟨{ m6_core_lengths_upd hlenL.core_ok hlenL.core_ok.arena_len_le sL.core.arena_garbage
         first_red sL.core.num_irred sL.core.num_redundant with
       arena_len_arr := harM_len, rsns_len := hrsM_len }, hscM_len⟩
  have hcmpM_st : CompactPrefixOk c F_cur s sM0.core start :=
    (arenaPrefix_preserves_compact (k := sL.core) (k' := sM0.core) hcmpL_st rfl
      hlenL.core_ok.arena_len_arr harM_len (by omega) hpre_st).1
  have hcmpM' : CompactPrefixOk c F_cur s sM.core dst.toNat :=
    ⟨{ len_ok := hcmpM.1.len_ok, refs_wf := hcmpM.1.refs_wf, shrk_term := hcmpM.1.shrk_term,
       lits_lt := hcmpM.1.lits_lt, entails := hcmpM.1.entails }, hcmpM.2.1, hcmpM.2.2⟩
  have hlikeM : M6SweepLike s sM0 := hlikeL.of_ar_rsns
  have hw_end : FullWitnessInv c F0 F_cur { sM.core with arena_len := dst.toNat } := by
    by_cases hcl0 : s.core.cur_level = 0
    · have hbw := m6_binOnlyWatchesInv_congr (k1 := sL.core)
        (k2 := { sM.core with arena_len := dst.toNat })
        (hlayL.with_wstk rfl rfl rfl rfl) rfl rfl rfl (fun l hl => hstart0 hcl0 ▸ hltL l hl)
      exact m6_trivial_post_witness (m6_root_post_move_witness hwE hcmpM'.1 hbw.toModeWatchesInv
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (hu.2.2.1.trans hcl0) (hrsn_r0 hcl0))
    · have hpos : 0 < s.core.cur_level := Nat.pos_of_ne_zero hcl0
      have hlt_M : ∀ l < 2 * sM0.core.cur_vars,
          WatchSliceLtOk start F_cur sM0.core l (fullWatchOff sM0 l) (fullWatchSize sM0 l) :=
        fun l hl => m6_watchSliceLtOk_congr (k1 := sL.core) rfl rfl (fun r hr_lt hr_mem =>
          have h1 := m6_refs_lt_compactPrefix hcmpL_st (by rw [hu.2.1]; exact hst_al) r hr_mem hr_lt
          have h2 : r ∈ fullArenaClauseRefsCore { sM0.core with arena_len := start } :=
            (arenaPrefix_preserves_compact (k := sL.core) (k' := sM0.core) hcmpL_st rfl
              hlenL.core_ok.arena_len_arr harM_len (by omega) hpre_st).2.1 ▸ h1
          (fullArenaClauseRefsCore_mono_prefix
            (by change start ≤ sL.core.arena_len; rw [hu.2.1]; exact hst_al)
            hcmpM_st.1 r h2).1) (hltL l hl)
      have hsw := m6_sweep_end_witness (sPre := sPre) (sL := sM0)
        hwPre (fun hs => hdk hs)
        ⟨{ hlenL.core_ok with arena_len_arr := harM_len, rsns_len := hrsM_len }, hlenL.scratch_ok⟩
        hlikeM hpre.cv hpre.cl hpre.ft hpre.fd hpre.inc hpre.vals hpre.lvl hpre.trl hpre.tp
        hpre.te hst_dst (by change start ≤ sL.core.arena_len; rw [hu.2.1]; exact hst_al) hcmpM
        hcmpM_st (hlayL.with_wstk rfl rfl rfl rfl) hlt_M ⟨fun h0 => absurd h0 hcl0⟩
        ⟨fun hp => ⟨(hpos_eqs hp).1, (hpos_eqs hp).2.1, (hpos_eqs hp).2.2.1,
          (hpos_eqs hp).2.2.2.1, (hpos_eqs hp).2.2.2.2.1, (hpos_eqs hp).2.2.2.2.2, hrmM hp⟩⟩
      exact m6_trivial_post_witness hsw
  refine ⟨sM, hpostM, hlenM, hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2.1,
    hu.2.2.2.2.2.1, hu.2.2.2.2.2.2.1, hscM_el.trans hu.2.2.2.2.2.2.2.1,
    hscM_ws1.trans hu.2.2.2.2.2.2.2.2.1, hscM_ws2.trans hu.2.2.2.2.2.2.2.2.2,
    hw_end, hcmpM'.2.1, hcmpM'.2.2, hstM_in, huns, fun hnu => ?_, fun hpos => ?_, hmM⟩
  · by_cases hcl0 : s.core.cur_level = 0
    · exact ⟨hcl0, (hunit hnu).2⟩
    · exact absurd (hpos_eqs (Nat.pos_of_ne_zero hcl0)).1 (by simp [hnu])
  · have huns_f : unsat = false := by cases hu' : unsat; rfl; exact absurd (huns hu').1 (by omega)
    exact ⟨huns_f, hpos_eqs hpos⟩

theorem m6_move_red_post_cf {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sPre sL : FullState} {R : Mem 64 → Prop} {start : Nat}
    {dst first_red : BitVec 64} {new_unit unsat : Bool} {arM : List (BitVec 32)} {mM : Mem 64}
    (hwPre : FullWitnessInv c F0 F_cur sPre.core) (hdk : 0 < start → sL.core.dense_mode = 0#64)
    (hlikeL : M6SweepLike s sL) (hlenL : sL.LengthsOk c)
    (hst_dst : start ≤ dst.toNat) (hst_al : start ≤ s.core.arena_len)
    (hdst_cap : dst.toNat ≤ c.arena_cap) (hpre : M6PreEqs s sPre)
    (harM_len : arM.length = c.arena_cap) (hpre_st : ∀ i < start, arM[i]? = sL.core.arena[i]?)
    (hcmpL_st : CompactPrefixOk c F_cur s sL.core start)
    (hcmpM : CompactPrefixOk c F_cur s { sL.core with arena := arM } dst.toNat)
    (hlayL : WatchStackLayout sL.core)
    (hltL : ∀ l < 2 * sL.core.cur_vars,
      WatchSliceLtOk start F_cur sL.core l (fullWatchOff sL l) (fullWatchSize sL l))
    (hstL_in : start < dst.toNat →
      start ∈ fullArenaClauseRefsCore { sL.core with arena_len := dst.toNat })
    (hrefsM : fullArenaClauseRefsCore { sL.core with arena := arM, arena_len := dst.toNat } =
      fullArenaClauseRefsCore { sL.core with arena_len := dst.toNat })
    (hstart0 : s.core.cur_level = 0 → start = 0)
    (hwE : FullWitnessInv c F0 F_cur { sL.core with arena_len := dst.toNat })
    (hunit : new_unit = true → s.core.cur_level = 0 ∧ s.core.trail_end < sL.core.trail_end)
    (hpos_eqs : 0 < s.core.cur_level → new_unit = false ∧ sL.core.vals = s.core.vals ∧
      sL.core.lvl = s.core.lvl ∧ sL.core.trl = s.core.trl ∧
      sL.core.trail_pos = s.core.trail_pos ∧ sL.core.trail_end = s.core.trail_end)
    (hrmM : 0 < s.core.cur_level →
      SweepReasonMapInv sPre.core { sL.core with arena := arM } sPre.core.arena_len dst.toNat)
    (huns : unsat = true → s.core.cur_level = 0 ∧ F0.Unsat)
    (hmM : (FullMem c { sL with
      core := { sL.core with arena := arM, first_reducible := first_red } } ⋆ R) mM) :
    M6PostMoveInv c F0 F_cur s R start dst unsat new_unit () mM :=
  m6_post_move_shared hwPre hdk hlikeL hlenL hst_dst hst_al hdst_cap hpre harM_len
    hlenL.core_ok.rsns_len hlenL.scratch_ok rfl rfl rfl hpre_st hcmpL_st hcmpM hlayL hltL
    hstart0 hwE hunit hpos_eqs hrmM
    (fun hcl0 idx hidx => hwE.level0_rsn_none idx hidx (by
      have hlv := hwE.lvl_le idx hidx
      exact Nat.eq_zero_of_le_zero (by
        rwa [show ({ sL.core with arena_len := dst.toNat } : FullCoreState).cur_level = 0 from
          hlikeL.unchanged.2.2.1.trans hcl0] at hlv)))
    (fun hst => by
      have h1 : start ∈ fullArenaClauseRefsCore
          { sL.core with arena := arM, arena_len := dst.toNat } := hrefsM ▸ hstL_in hst
      exact (congrArg (start ∈ ·) (fullArenaClauseRefsCore_congr
        (k1 := { sL.core with arena := arM, arena_len := dst.toNat })
        (k2 := { sL.core with
          arena := arM, first_reducible := first_red, arena_len := dst.toNat })
        rfl (fun _ _ => rfl))).mp h1)
    huns hmM

theorem m6_move_red_post_end {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sPre sL : FullState} {R : Mem 64 → Prop} {start rwL rwOut : Nat}
    {dst first_red fred' : BitVec 64} {new_unit : Bool}
    {ar' rsns' : List (BitVec 32)} {sc' : FullScratch} {mM : Mem 64}
    (hwPre : FullWitnessInv c F0 F_cur sPre.core) (hdk : 0 < start → sL.core.dense_mode = 0#64)
    (hlikeL : M6SweepLike s sL) (hlenL : sL.LengthsOk c) (hcap_bd : c.arena_cap < 2 * dimacsBound)
    (hst_dst : start ≤ dst.toNat) (hdst_al : dst.toNat ≤ s.core.arena_len)
    (hdst_cap : dst.toNat ≤ c.arena_cap)
    (hfr_st : start ≤ first_red.toNat) (hfr_lt : first_red.toNat < dst.toNat)
    (hpre : M6PreEqs s sPre) (hcmpL : CompactPrefixOk c F_cur s sL.core dst.toNat)
    (hcmpL_st : CompactPrefixOk c F_cur s sL.core start)
    (hcmpL_fr : CompactPrefixOk c F_cur s sL.core first_red.toNat)
    (hlayL : WatchStackLayout sL.core)
    (hltL : ∀ l < 2 * sL.core.cur_vars,
      WatchSliceLtOk start F_cur sL.core l (fullWatchOff sL l) (fullWatchSize sL l))
    (hstL_in : start < dst.toNat →
      start ∈ fullArenaClauseRefsCore { sL.core with arena_len := dst.toNat })
    (hmvE : MoveRangeChain sL.core.arena first_red.toNat dst.toNat rwL)
    (hfr_in : first_red.toNat ∈ fullArenaClauseRefsCore { sL.core with arena_len := dst.toNat })
    (hrmk : M6ReasonMarkRange sPre sL first_red.toNat dst.toNat)
    (hstart0 : s.core.cur_level = 0 → start = 0)
    (hwE : FullWitnessInv c F0 F_cur { sL.core with arena_len := dst.toNat })
    (hunit : new_unit = true → s.core.cur_level = 0 ∧ s.core.trail_end < sL.core.trail_end)
    (hpos_eqs : 0 < s.core.cur_level → new_unit = false ∧ sL.core.vals = s.core.vals ∧
      sL.core.lvl = s.core.lvl ∧ sL.core.trl = s.core.trl ∧
      sL.core.trail_pos = s.core.trail_pos ∧ sL.core.trail_end = s.core.trail_end)
    (hrmE : 0 < s.core.cur_level →
      SweepReasonMapInv sPre.core sL.core sPre.core.arena_len dst.toNat)
    (har' : ar'.length = c.arena_cap) (hrs' : rsns'.length = c.max_vars)
    (hsc'_len : sc'.LengthsOk c) (hsc'_el : sc'.extend_len = sL.scratch.extend_len)
    (hsc'_ws1 : sc'.work_stk1 = sL.scratch.work_stk1)
    (hsc'_ws2 : sc'.work_stk2 = sL.scratch.work_stk2)
    (hpre' : ∀ i < first_red.toNat, ar'[i]? = sL.core.arena[i]?)
    (hmv' : MoveRangeChain ar' first_red.toNat dst.toNat rwOut)
    (hblk' : ∀ r, RefInChain ar' first_red.toNat dst.toNat r →
      (ar'[r]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧ ∃ src,
        RefInChain sL.core.arena first_red.toNat dst.toNat src ∧
        (ar'[r + 2]?.getD 0#32).toNat = (sL.core.arena[src + 2]?.getD 0#32).toNat ∧
        ∀ j < (sL.core.arena[src + 2]?.getD 0#32).toNat,
          ar'[r + 3 + j]? = sL.core.arena[src + 3 + j]?)
    (hrsns' : ∀ v < sL.core.cur_vars,
      let r0 := sL.core.rsns[v]?.getD 0xFFFFFFFF#32
      if first_red.toNat ≤ r0.toNat ∧ r0.toNat < dst.toNat ∧
          RefInChain sL.core.arena first_red.toNat dst.toNat r0.toNat ∧
          (sL.core.arena[r0.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
          ∃ j < (sL.core.arena[r0.toNat + 2]?.getD 0#32).toNat,
            let lit := (sL.core.arena[r0.toNat + 3 + j]?.getD 0#32).toNat
            lit / 2 = v ∧ sL.core.vals[lit]?.getD 0#8 = 1#8
      then
        let r' := (rsns'[v]?.getD 0xFFFFFFFF#32).toNat
        first_red.toNat ≤ r' ∧ r' < dst.toNat ∧ r' < 2147483648 ∧
        RefInChain ar' first_red.toNat dst.toNat r' ∧
        (ar'[r' + 2]?.getD 0#32).toNat = (sL.core.arena[r0.toNat + 2]?.getD 0#32).toNat ∧
        ∀ j < (sL.core.arena[r0.toNat + 2]?.getD 0#32).toNat,
          ar'[r' + 3 + j]? = sL.core.arena[r0.toNat + 3 + j]?
      else rsns'[v]?.getD 0xFFFFFFFF#32 = r0)
    (hmM : (FullMem c
      { core := { sL.core with arena := ar', rsns := rsns', first_reducible := fred' },
        scratch := sc' } ⋆ R) mM) :
    M6PostMoveInv c F0 F_cur s R start dst false new_unit () mM := by
  have hdb : dimacsBound = 2 ^ 28 := rfl
  have hu := hlikeL.unchanged
  have hcr := move_red_end_compact_and_rsn hwPre hcmpL hcmpL_fr hlenL.core_ok.arena_len_arr har'
    hrs' hfr_lt hdst_cap hfr_in hmvE hmv' hpre' hblk' hrmE (fun hp => hrmk.get (hpre.cl.symm ▸ hp))
    (hu.1.trans hpre.cv.symm) hwPre.trail_lits_lt hrsns'
  have hcmp_cr : CompactPrefixOk c F_cur s
      { sL.core with arena := ar', rsns := rsns', first_reducible := fred' } dst.toNat :=
    ⟨{ len_ok := hcr.1.1.len_ok, refs_wf := hcr.1.1.refs_wf, shrk_term := hcr.1.1.shrk_term,
       lits_lt := hcr.1.1.lits_lt, entails := hcr.1.1.entails }, hcr.1.2.1, hcr.1.2.2⟩
  have hfrM := m6_first_red_mem_prefix hcmpL_fr hcmp_cr hlenL.core_ok.arena_len_arr har'
    hfr_lt hdst_cap hpre' hfr_in
  have hstM_in := m6_start_in_post_move
    (kM := { sL.core with arena := ar', rsns := rsns', first_reducible := fred' })
    hcmpL_fr hlenL.core_ok.arena_len_arr har' rfl hdst_cap hfr_lt hfr_st hpre' hstL_in hfrM
  exact m6_post_move_shared hwPre hdk hlikeL hlenL hst_dst (by rw [← hu.2.1]; omega) hdst_cap
    hpre har' hrs' hsc'_len hsc'_el hsc'_ws1 hsc'_ws2
    (fun i hi => hpre' i (Nat.lt_of_lt_of_le hi hfr_st)) hcmpL_st hcr.1 hlayL hltL
    hstart0 hwE hunit hpos_eqs hcr.2
    (fun hcl0 idx hidx => by
      have htl := hwE.trail_lits_lt idx hidx; dsimp only at htl
      have hv : (sL.core.trl[idx]?.getD 0#32).toNat / 2 < sL.core.cur_vars :=
        Nat.div_lt_of_lt_mul htl
      have hff := hwE.level0_rsn_none idx hidx (by
        have hlv := hwE.lvl_le idx hidx
        exact Nat.eq_zero_of_le_zero (by
          rwa [show ({ sL.core with arena_len := dst.toNat } : FullCoreState).cur_level = 0 from
            hu.2.2.1.trans hcl0] at hlv))
      dsimp only at hff
      have hsp := hrsns' _ hv; dsimp only at hsp; rw [hff] at hsp
      split at hsp
      · rename_i hcond; exfalso; have h29 : dst.toNat < 2 ^ 32 - 1 := by omega
        have := hcond.2.1; change (0xFFFFFFFF#32).toNat < dst.toNat at this; simp at this; omega
      · exact hsp)
    (fun hst => by
      let k1 : FullCoreState := { sL.core with
        arena := ar', rsns := rsns', first_reducible := fred', arena_len := dst.toNat }
      let k2 : FullCoreState := { sL.core with
        arena := ar', rsns := rsns', first_reducible := first_red, arena_len := dst.toNat }
      exact (congrArg (start ∈ ·)
        (fullArenaClauseRefsCore_congr (k1 := k1) (k2 := k2) rfl (fun _ _ => rfl))).mp
        (hstM_in hst))
    (fun h => by cases h) hmM

abbrev m6PostState (sM : FullState) (dst ni nr : BitVec 64)
    (ll' : List (BitVec 32)) : FullState :=
  { core := { sM.core with arena_len := dst.toNat, arena_garbage := 0#64,
                           num_irred := ni, num_redundant := nr },
    scratch := { sM.scratch with last_learned := ll' } }

theorem m6_sweep_early_exit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sM : FullState} {R : Mem 64 → Prop} {dst ni nr ret : BitVec 64}
    {ll' : List (BitVec 32)} {m' : Mem 64} {Q : Post [i64]}
    (hpostM : M6PostLike s sM)
    (hlenP : (m6PostState sM dst ni nr ll').LengthsOk c)
    (hllP : FullLastLearnedWf (m6PostState sM dst ni nr ll'))
    (hwP : FullWitnessInv c F0 F_cur (m6PostState sM dst ni nr ll').core)
    (hndP : FullArenaVarsNodup (m6PostState sM dst ni nr ll'))
    (helM : sM.scratch.extend_len = s.scratch.extend_len)
    (hws1M : sM.scratch.work_stk1 = s.scratch.work_stk1)
    (hws2M : sM.scratch.work_stk2 = s.scratch.work_stk2)
    (hm' : (FullMem c (m6PostState sM dst ni nr ll') ⋆ R) m')
    (hret : (ret = 2#64 ∧ s.core.cur_level = 0 ∧ F0.Unsat) ∨ (ret = 3#64 ∧ sM.core.oom ≠ 0#64))
    (hQ : M6SweepPostQ c F0 F_cur s R Q)
    (hpos : 0 < s.core.cur_level → sM.core.vals = s.core.vals ∧ sM.core.lvl = s.core.lvl ∧
      sM.core.trl = s.core.trl ∧ sM.core.trail_pos = s.core.trail_pos ∧
      sM.core.trail_end = s.core.trail_end) : Q (ret, ()) m' := by
  rcases hpostM with ⟨v, f, l, r, t, tp, te, u, uf, wv, ws, ar, wl, wu, fr, nb, o, hEq⟩
  dsimp only [m6PostState] at hlenP hllP hwP hndP hm'
  rw [hEq] at hlenP hllP hwP hndP hm' hpos hret
  rcases hret with ⟨rfl, hcl0, huns⟩ | ⟨rfl, hoom⟩
  · exact hQ 2#64 v f l r t tp te u uf wv ws ar dst.toNat wl wu fr ni nr nb o
      { sM.scratch with last_learned := ll' } m' hlenP (by simp) helM hws1M hws2M hllP hwP hndP
      (fun h => by simp at h) (fun h => by omega) (fun h => by simp at h)
      (fun _ => ⟨hcl0, huns⟩) (fun h => by simp at h) hm'
  · exact hQ 3#64 v f l r t tp te u uf wv ws ar dst.toNat wl wu fr ni nr nb o
      { sM.scratch with last_learned := ll' } m' hlenP (by simp) helM hws1M hws2M hllP hwP hndP
      (fun h => by simp at h) (fun hp => ⟨by simp, by simp, hpos hp⟩)
      (fun h => by simp at h) (fun h => by simp at h) (fun _ => hoom) hm'

theorem m6_sweep_rewatch_exit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sM : FullState} {R : Mem 64 → Prop} {dst ni nr : BitVec 64} {ll' : List (BitVec 32)}
    (hpostM : M6PostLike s sM) (hoom0 : sM.core.oom = 0#64)
    (hll_ff : ∀ i < 16, ll'[i]? = some 0xFFFFFFFF#32)
    (hndP : FullArenaVarsNodup
      { core := { sM.core with
          arena_len := dst.toNat, arena_garbage := 0#64, num_irred := ni, num_redundant := nr },
        scratch := { sM.scratch with last_learned := ll' } })
    (helM : sM.scratch.extend_len = s.scratch.extend_len)
    (hws1M : sM.scratch.work_stk1 = s.scratch.work_stk1)
    (hws2M : sM.scratch.work_stk2 = s.scratch.work_stk2) (new_unit : Bool)
    (hunit : new_unit = true → s.core.cur_level = 0 ∧ s.core.trail_end < sM.core.trail_end)
    (hnu_pos : 0 < s.core.cur_level → new_unit = false)
    (hpos : 0 < s.core.cur_level → sM.core.vals = s.core.vals ∧ sM.core.lvl = s.core.lvl ∧
      sM.core.trl = s.core.trl ∧ sM.core.trail_pos = s.core.trail_pos ∧
      sM.core.trail_end = s.core.trail_end) (Q : Post [i64]) (hQ : M6SweepPostQ c F0 F_cur s R Q) :
    let sPost : FullState :=
      { core := { sM.core with arena_len := dst.toNat, arena_garbage := 0#64,
                               num_irred := ni, num_redundant := nr },
        scratch := { sM.scratch with last_learned := ll' } }
    fullRewatchArenaPost c F0 F_cur sPost R fun (ok, ()) m' =>
      if ok = true then Q (if new_unit = true then 1#64 else 0#64, ()) m' else Q (3#64, ()) m' := by
  dsimp only
  intro ok arena' wvec' wstk' wlen' wu' oom' wsort' m'
  dsimp only
  intro hlen' hw' hnd_fn _ hoomF hoomT hm'
  have hnd' := hnd_fn hndP
  rcases hpostM with ⟨v, f, l, r, t, tp, te, u, uf, wv, ws, ar, wl, wu, fr, nb, o, hEq⟩
  rw [hEq] at hlen' hw' hnd' hoomT hm' hoom0 hpos hunit
  dsimp only at hoom0 hpos hunit
  let sOut : FullState :=
    { core := { s.core with
        vals := v, flags := f, lvl := l, rsns := r, trl := t, trail_pos := tp, trail_end := te,
        unassigned := u, unflushed := uf, wvec := wvec', wstk := wstk', arena := arena',
        arena_len := dst.toNat, wlen := wlen', wusable := wu', arena_garbage := 0#64,
        first_reducible := fr, num_irred := ni, num_redundant := nr, num_binary := nb, oom := oom' }
      scratch := { sM.scratch with last_learned := ll', wsort := wsort' } }
  have hll' : FullLastLearnedWf sOut := fullLastLearnedWf_of_all_sentinel hll_ff
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact hQ 3#64 v f l r t tp te u uf wvec' wstk' arena' dst.toNat wlen' wu' fr ni nr nb oom'
      { sM.scratch with last_learned := ll', wsort := wsort' } m' hlen' (by simp) helM hws1M hws2M
      hll' hw' hnd' (fun h => by simp at h) (fun hp => ⟨by simp, by simp, hpos hp⟩)
      (fun h => by simp at h) (fun h => by simp at h) (fun _ => by simp [hoomF rfl]) hm'
  · simp only [↓reduceIte]
    cases new_unit
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact hQ 0#64 v f l r t tp te u uf wvec' wstk' arena' dst.toNat wlen' wu' fr ni nr nb oom'
        { sM.scratch with last_learned := ll', wsort := wsort' } m' hlen' (by simp) helM hws1M hws2M
        hll' hw' hnd' (fun _ => (hoomT rfl).trans hoom0) (fun hp => ⟨by simp, by simp, hpos hp⟩)
        (fun h => by simp at h) (fun h => by simp at h) (fun h => by simp at h) hm'
    · simp only [↓reduceIte]
      exact hQ 1#64 v f l r t tp te u uf wvec' wstk' arena' dst.toNat wlen' wu' fr ni nr nb oom'
        { sM.scratch with last_learned := ll', wsort := wsort' } m' hlen' (by simp) helM hws1M hws2M
        hll' hw' hnd' (fun _ => (hoomT rfl).trans hoom0) (fun hp => absurd (hnu_pos hp) (by simp))
        (fun _ => hunit rfl) (fun h => by simp at h) (fun h => by simp at h) hm'

theorem m6_rsn_miss_exit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sPre sL sC : FullState} {R : Mem 64 → Prop} {arH : List (BitVec 32)}
    {hdr0 : BitVec 32} {src dst nsrc st : BitVec 64} {old_sz : BitVec 32}
    {hcl_beq mark_allowed new_unit : Bool} {m : Mem 64}
    (hwPre : FullWitnessInv c F0 F_cur sPre.core) (hpre : M6PreEqs s sPre) (hlenC0 : sC.LengthsOk c)
    (harL_len : sL.core.arena.length = c.arena_cap) (harC_len : sC.core.arena.length = c.arena_cap)
    (harH_len : arH.length = c.arena_cap) (hszH : (arH[dst.toNat + 2]?.getD 0#32).toNat = st.toNat)
    (harH_0 : arH[dst.toNat]? = some (hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)))
    (hdropH : ((arH.drop (dst.toNat + 3)).take st.toNat).map BitVec.toNat =
      ((sC.core.arena.drop (dst.toNat + 3)).take st.toNat).map BitVec.toNat)
    (hcmpH : CompactPrefixOk c F_cur s { sC.core with arena := arH } (dst.toNat + 3 + st.toNat))
    (hdst_inH : dst.toNat ∈ fullArenaClauseRefsCore
      { sC.core with arena := arH, arena_len := dst.toNat + 3 + st.toNat })
    (hdst_src : dst.toNat ≤ src.toNat) (hsrc_lt8 : src.toNat < 0x80000000)
    (hdst_fit_arH : dst.toNat + 3 + st.toNat ≤ arH.length)
    (hsrc_ref : src.toNat ∈ fullArenaClauseRefs sPre)
    (hnsrc64 : nsrc.toNat = fullArenaNextOff sPre.core.arena sPre.core.arena_len src.toNat)
    (hsrc_fit_cap : src.toNat + 3 + old_sz.toNat ≤ c.arena_cap)
    (hsrc_lits_eq : ((sL.core.arena.drop (src.toNat + 3)).take old_sz.toNat).map BitVec.toNat =
      fullArenaClauseLitsCore sPre.core src.toNat)
    (hout_ok0 : fullSweepCopyOutcome c F0 F_cur sL sC src dst old_sz hcl_beq st)
    (hdec_cl0 : ∀ b : Bool,
      hcl_beq = b ↔ (if b then s.core.cur_level = 0 else 0 < s.core.cur_level))
    (hposL : M6SweepLoopPosOk s sPre sL src.toNat dst.toNat new_unit)
    (happend_mk : ∀ rsns' : List (BitVec 32),
      fullArenaClauseLitsCore
          { sC.core with arena := arH, arena_len := dst.toNat + 3 + st.toNat } dst.toNat =
        fullArenaClauseLitsCore sPre.core src.toNat →
      SweepHappenedCore sPre.core sL.core
        { sL.core with arena := arH, rsns := rsns', arena_len := dst.toNat + 3 + st.toNat }
        dst.toNat src.toNat)
    (hflH : ((hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)) &&& 0x00880000#32) = 0#32)
    (hmiss : 0 < s.core.cur_level → ∀ j < st.toNat,
      let lit := arH[dst.toNat + 3 + j]?.getD 0#32
      ¬ (lit.toNat / 2 < s.core.cur_vars ∧
         (0#32).slt ((sC.core.vals[lit.toNat]?.getD 0#8).signExtend 32) = true ∧
         sC.core.rsns[lit.toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src.toNat))
    (hm_arH : (FullMem c { sC with core := { sC.core with arena := arH } } ⋆ R) m) :
    M6RsnBranchInv c F_cur s sPre sC R arH nsrc.toNat dst.toNat st.toNat mark_allowed () m := by
  have hrm_miss : ∀ hpos : 0 < s.core.cur_level,
      SweepReasonMapInv sPre.core { sC.core with arena := arH } nsrc.toNat
        (dst.toNat + 3 + st.toNat) := fun hpos => by
    obtain ⟨_, hvC, _, hrC, _, _, _, hlits_eq⟩ :=
      sweep_pos_lits_eq hout_ok0 ((hdec_cl0 false).mpr hpos) harL_len harC_len hsrc_fit_cap
        hdst_src hsrc_lits_eq hszH hdropH
    exact SweepReasonMapInv.congr_rsns_arena rfl rfl
      (SweepReasonMapInv.keep_step (kL := sL.core) hwPre hsrc_ref hnsrc64 hdst_src hsrc_lt8
        (hposL.get hpos).2.2.2.2.2.2 (happend_mk sC.core.rsns hlits_eq) (fun _ _ _ => by rw [hrC])
        (fun idx hidx heq => absurd heq (m6_rsn_not_src_of_miss hwPre (hposL.get hpos).2.2.2.2.2.2
          (hvC.trans ((hposL.get hpos).2.1.trans hpre.vals.symm)) hrC hszH hdst_fit_arH hsrc_lt8
          hlits_eq (fun j hj => by rw [hpre.cv]; exact hmiss hpos j hj) hidx)))
  refine ⟨arH, sC.core.rsns, harH_len, hlenC0.core_ok.rsns_len, fun _ _ => rfl, fun _ _ => rfl,
    hszH, by rw [harH_0, Option.getD_some]; exact hflH, rfl, hcmpH.with_rsns, hdst_inH,
    fun _ _ _ => rfl, fun _ => rfl, hrm_miss, fun hp _ idx hidx heq => by
      obtain ⟨_, hvC, _, hrC, _, _, _, hlits_eq⟩ :=
        sweep_pos_lits_eq hout_ok0 ((hdec_cl0 false).mpr hp) harL_len harC_len hsrc_fit_cap
          hdst_src hsrc_lits_eq hszH hdropH
      have hnot := m6_rsn_not_src_of_miss hwPre (hposL.get hp).2.2.2.2.2.2
        (hvC.trans ((hposL.get hp).2.1.trans hpre.vals.symm)) hrC hszH hdst_fit_arH hsrc_lt8
        hlits_eq (fun j hj => by rw [hpre.cv]; exact hmiss hp j hj) hidx
      exact absurd (hrC ▸ heq) (m6_rsn_ne_dst_of_not_src_val hwPre hdst_src (by omega)
        (hposL.get hp).2.2.2.2.2.2 hnot hsrc_lt8 hidx),
    full_mem_cast hm_arH rfl⟩

/-! ## 4. Factored `PH_RSN` Inner Loop WP -/

abbrev m6RsnLoopExpr {rs : List Ty} (JR : Cont []) (pArena pVals pRsns pCv src dst : Val i64)
    (st : Val i32) (nhdr : Val i32) (at_root : Val Ty.bool) (first_red : Val i64)
    (hdr32 : Val i32) : Expr Val Cont rs :=
  Expr.group (fun _ => Blocks.cons (ts := [i32]) (fun _ => Expr.jump JR ()) .nil) fun Jbrk =>
    Expr.group (fun Ji => Blocks.cons (ts := [i32]) (fun p46 =>
      Expr.let_ (swOp2 (.cmp .ult i32 .bool (by decide)) (Arg.var p46.1) (Arg.var st)) fun p =>
      Expr.jnz (Arg.var p.1)
        (Expr.let_ (swOp2 (.add i64) (Arg.var dst) (Arg.imm 3)) fun p =>
         Expr.let_ (swOp1 (.zext 32 64) (Arg.var p46.1)) fun p47 =>
         Expr.let_ (swOp2 (.add i64) (Arg.var p.1) (Arg.var p47.1)) fun p =>
         Expr.let_ (swOp2 (.mul i64) (Arg.var p.1) (Arg.imm 4)) fun p =>
         Expr.let_ (swOp2 (.add i64) (Arg.var pArena) (Arg.var p.1)) fun p =>
         Expr.load i32 (Arg.var p.1) fun ld8 =>
         Expr.let_ (swOp2 (.lshr i32) (Arg.var ld8) (Arg.imm 1)) fun p =>
         Expr.group (fun _ => Blocks.cons (ts := []) (fun _ =>
           Expr.let_ (swOp2 (.add i32) (Arg.var p46.1) (Arg.imm 1)) fun p =>
           Expr.jump Ji.1 (Arg.var p.1, ())) .nil) fun Jni =>
         Expr.let_ (swOp1 (.zext 32 64) (Arg.var p.1)) fun p48 =>
         Expr.let_ (swOp2 (.cmp .ult i64 .bool (by decide)) (Arg.var p48.1) (Arg.var pCv))
           fun p49 =>
         Expr.jnz (Arg.var p49.1)
           (Expr.let_ (swOp1 (.zext 32 64) (Arg.var ld8)) fun p50 =>
            Expr.let_ (swOp2 (.add i64) (Arg.var pVals) (Arg.var p50.1)) fun p51 =>
            Expr.load i8 (Arg.var p51.1) fun ld9 =>
            Expr.let_ (swOp1 (.trunc 32 8) (Arg.imm 0)) fun p52 =>
            Expr.let_ (swOp1 (.sext 8 32) (Arg.var ld9)) fun p53 =>
            Expr.let_ (swOp1 (.sext 8 32) (Arg.var p52.1)) fun p54 =>
            Expr.let_ (swOp2 (.cmp .sgt i32 .bool (by decide)) (Arg.var p53.1) (Arg.var p54.1))
              fun p55 =>
            Expr.jnz (Arg.var p55.1)
              (Expr.let_ (swOp1 (.zext 32 64) (Arg.var p.1)) fun p56 =>
               Expr.let_ (swOp2 (.mul i64) (Arg.var p56.1) (Arg.imm 4)) fun p57 =>
               Expr.let_ (swOp2 (.add i64) (Arg.var pRsns) (Arg.var p57.1)) fun p58 =>
               Expr.load i32 (Arg.var p58.1) fun ld10 =>
               Expr.let_ (swOp1 (.zext 32 64) (Arg.var ld10)) fun p59 =>
               Expr.let_ (swOp2 (.cmp .eq i64 .bool (by decide)) (Arg.var p59.1) (Arg.var src))
                 fun p60 =>
               Expr.jnz (Arg.var p60.1)
                 (Expr.let_ (swOp1 (.zext 32 64) (Arg.var p.1)) fun p =>
                  Expr.let_ (swOp2 (.mul i64) (Arg.var p.1) (Arg.imm 4)) fun p =>
                  Expr.let_ (swOp2 (.add i64) (Arg.var pRsns) (Arg.var p.1)) fun p =>
                  Expr.let_ (swOp1 (.trunc 64 32) (Arg.var dst)) fun p61 =>
                  Expr.store (Arg.var p61.1) (Arg.var p.1)
                    (Expr.group (fun _ => Blocks.cons (ts := []) (fun _ =>
                      Expr.jump Jbrk.1 (Arg.var p46.1, ())) .nil) fun Jm =>
                     Expr.jnz (Arg.var at_root) (Expr.jump Jm.1 ())
                       (Expr.group (fun _ => Blocks.cons (ts := []) (fun _ =>
                          Expr.let_ (swOp2 (.mul i64) (Arg.var dst) (Arg.imm 4)) fun p =>
                          Expr.let_ (swOp2 (.add i64) (Arg.var pArena) (Arg.var p.1)) fun p =>
                          Expr.let_ (swOp2 (.or i32) (Arg.var nhdr) (Arg.imm 2097152)) fun p62 =>
                          Expr.store (Arg.var p62.1) (Arg.var p.1) (Expr.jump Jm.1 ())) .nil)
                        fun Jmk =>
                        Expr.let_ (swOp2 (.cmp .ne i64 .bool (by decide))
                          (Arg.var first_red) (Arg.imm 4294967295)) fun p =>
                        Expr.jnz (Arg.var p.1) (Expr.jump Jmk.1 ())
                          (Expr.let_ (swOp2 (.and i32) (Arg.var hdr32) (Arg.imm 4194304)) fun p =>
                           Expr.let_ (swOp2 (.cmp .ne i32 .bool (by decide)) (Arg.var p.1)
                             (Arg.imm 0)) fun p =>
                           Expr.jnz (Arg.var p.1) (Expr.jump Jmk.1 ()) (Expr.jump Jm.1 ())))))
                 (Expr.jump Jni.1 ()))
              (Expr.jump Jni.1 ()))
           (Expr.jump Jni.1 ()))
        (Expr.jump Jbrk.1 (Arg.var p46.1, ()))) .nil)
    fun Ji => Expr.jump Ji.1 (Arg.imm (t := i32) 0, ())

theorem m6_sweep_rsn_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sPre sL sC : FullState} {R : Mem 64 → Prop} {arH : List (BitVec 32)}
    {hdr0 : BitVec 32} {src dst nsrc st first_red : BitVec 64} {old_sz : BitVec 32}
    {new_unit : Bool} {m : Mem 64}
    (JR : Cont [])
    (hwPre : FullWitnessInv c F0 F_cur sPre.core) (hpre : M6PreEqs s sPre)
    (hlikeC : M6SweepLike s sC) (hlenC0 : sC.LengthsOk c)
    (hcap_lt : c.arena_cap < 2 * dimacsBound) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hcl_lt : s.core.cur_level < 2 ^ 64)
    (harL_len : sL.core.arena.length = c.arena_cap) (harC_len : sC.core.arena.length = c.arena_cap)
    (harH_len : arH.length = c.arena_cap) (hszH : (arH[dst.toNat + 2]?.getD 0#32).toNat = st.toNat)
    (harH_0 : arH[dst.toNat]? = some (hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)))
    (hbodyH : ∀ j, dst.toNat + 3 ≤ j → arH[j]? = sC.core.arena[j]?)
    (hdropH : ((arH.drop (dst.toNat + 3)).take st.toNat).map BitVec.toNat =
      ((sC.core.arena.drop (dst.toNat + 3)).take st.toNat).map BitVec.toNat)
    (hcmpH : CompactPrefixOk c F_cur s { sC.core with arena := arH } (dst.toNat + 3 + st.toNat))
    (hdst_inH : dst.toNat ∈ fullArenaClauseRefsCore
      { sC.core with arena := arH, arena_len := dst.toNat + 3 + st.toNat })
    (hdst_src : dst.toNat ≤ src.toNat) (hdst_lt8 : dst.toNat < 0x80000000)
    (hsrc_lt8 : src.toNat < 0x80000000) (hsrc_ref : src.toNat ∈ fullArenaClauseRefs sPre)
    (hnsrc64 : nsrc.toNat = fullArenaNextOff sPre.core.arena sPre.core.arena_len src.toNat)
    (hsrc_fit_cap : src.toNat + 3 + old_sz.toNat ≤ c.arena_cap)
    (hdst_fit_arH : dst.toNat + 3 + st.toNat ≤ arH.length)
    (hsrc_lits_eq : ((sL.core.arena.drop (src.toNat + 3)).take old_sz.toNat).map BitVec.toNat =
      fullArenaClauseLitsCore sPre.core src.toNat)
    (hout_ok0 : fullSweepCopyOutcome c F0 F_cur sL sC src dst old_sz
      (BitVec.ofNat 64 s.core.cur_level == 0) st)
    (hdec_cl0 : ∀ b : Bool, (BitVec.ofNat 64 s.core.cur_level == 0) = b ↔
      (if b then s.core.cur_level = 0 else 0 < s.core.cur_level))
    (hposL : M6SweepLoopPosOk s sPre sL src.toNat dst.toNat new_unit)
    (happend_mk : ∀ rsns' : List (BitVec 32),
      fullArenaClauseLitsCore
          { sC.core with arena := arH, arena_len := dst.toNat + 3 + st.toNat } dst.toNat =
        fullArenaClauseLitsCore sPre.core src.toNat →
      SweepHappenedCore sPre.core sL.core
        { sL.core with arena := arH, rsns := rsns', arena_len := dst.toNat + 3 + st.toNat }
        dst.toNat src.toNat)
    (hnew_lt : ∀ j < st.toNat,
      (sC.core.arena[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * sC.core.cur_vars)
    (hbits : let nh := hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)
      ((nh ||| 0x00200000#32) &&& 0x00800000#32) = 0#32 ∧
      ((nh ||| 0x00200000#32) &&& 0x00080000#32) = 0#32 ∧
      (nh &&& 0x00880000#32) = 0#32 ∧ ((nh ||| 0x00200000#32) &&& 0x00880000#32) = 0#32 ∧
      (nh &&& 0x00400000#32) = (hdr0 &&& 0x00400000#32) ∧
      ((nh ||| 0x00200000#32) &&& 0x00400000#32) = (hdr0 &&& 0x00400000#32))
    (hm_arH : (FullMem c { sC with core := { sC.core with arena := arH } } ⋆ R) m)
    (hJR : ∀ mR, M6RsnBranchInv c F_cur s sPre sC R arH nsrc.toNat dst.toNat st.toNat
      (!(decide (s.core.cur_level = 0)) &&
       (decide (first_red ≠ 0xFFFFFFFF#64) || decide ((hdr0 &&& 0x00400000#32) ≠ 0#32)))
      () mR → wp Γ Q X (Expr.jump JR ()) mR) :
    wp Γ Q X
      (m6RsnLoopExpr JR c.pArena c.pVals c.pReason (BitVec.ofNat 64 s.core.cur_vars)
        src dst (st.setWidth 32) (hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32))
        (BitVec.ofNat 64 s.core.cur_level == 0) first_red hdr0) m := by
  have hdb : dimacsBound = 2 ^ 28 := rfl
  have hmax_lt : c.max_vars < 2 * dimacsBound := c.hmaxv
  let mark_allowed : Bool := !(decide (s.core.cur_level = 0)) &&
    (decide (first_red ≠ 0xFFFFFFFF#64) || decide ((hdr0 &&& 0x00400000#32) ≠ 0#32))
  let sH : FullState := { sC with core := { sC.core with arena := arH } }
  m6_to_group
  refine wp_join_group (fun (_ : Tup Val [i32]) =>
      M6RsnBranchInv c F_cur s sPre sC R arH nsrc.toNat dst.toNat st.toNat mark_allowed ())
    (fun _ ⟨_iB, ⟨⟩⟩ mB hB => by
      dsimp only [Blocks.get_here, Blocks.get_there]; rw [wp_jump]; exact hJR mB hB) ?_
  intro Jbrk hJbrk
  refine wp_loop_inv (M6RsnLoopInv s sC arH src.toNat dst.toNat st.toNat m)
    (fun (i, ()) _ => st.toNat - i.toNat) (fun Ji hLoopI => ?_) ?_
  · m6_c0_steps; exact hLoopI (0#32, ()) m ⟨rfl, Nat.zero_le _, fun _ _ hj => absurd hj (by simp)⟩
  · rintro Ji ⟨i, ⟨⟩⟩ mI ⟨hmI, hi_le, hmissI⟩ hLoopI; subst mI
    m6_jnz
    · have hi_lt : i.toNat < st.toNat := by
        have : i.toNat < (st.setWidth 32).toNat := by c0_bound
        omega
      have hi1_eq : (i + 1#32).toNat = i.toNat + 1 := bv32_add1 (by omega)
      have hdi_eq : (dst + 3 + i.setWidth 64).toNat = dst.toNat + 3 + i.toNat := by
        rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat i (by decide)]; simp; omega
      have hdi_lt : (dst + 3 + i.setWidth 64).toNat < arH.length := by omega
      let litI := arH[(dst + 3 + i.setWidth 64).toNat]'hdi_lt
      have hlitI_eq : arH[dst.toNat + 3 + i.toNat]?.getD 0#32 = litI := by
        rw [List.getElem?_eq_getElem (by omega : dst.toNat + 3 + i.toNat < arH.length),
          Option.getD_some]; simp only [litI, hdi_eq]
      have hlitI_lt : litI.toNat < 2 * s.core.cur_vars := by
        have h1 := hnew_lt i.toNat hi_lt
        rwa [hlikeC.unchanged.1, ← hbodyH (dst.toNat + 3 + i.toNat) (by omega), hlitI_eq] at h1
      have hvI_eq : (litI >>> (1 : BitVec 32)).toNat = litI.toNat / 2 := bv32_shr1_toNat litI
      have hlitI_v : litI.toNat < sC.core.vals.length := by
        rw [hlenC0.core_ok.vals_len]
        exact Nat.lt_of_lt_of_le hlitI_lt (Nat.mul_le_mul_left 2 hcv_le)
      have hvI_r' : litI.toNat / 2 < sC.core.rsns.length := by
        rw [hlenC0.core_ok.rsns_len]
        exact Nat.lt_of_lt_of_le (Nat.div_lt_of_lt_mul (by omega)) hcv_le
      m6_to_group_strip
      refine wp_join_group (M6RsnNextInv s sC litI src.toNat m) ?_ ?_
      · rintro _ ⟨⟩ _ ⟨rfl, hmiss_cur⟩; m6_c0_steps
        refine hLoopI (i + 1#32, ()) m (by dsimp only; rw [hi1_eq]; omega)
          ⟨rfl, by rw [hi1_eq]; omega, fun hpos j hj => ?_⟩
        rw [hi1_eq] at hj
        rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hj) with rfl | hlt
        · simpa [hlitI_eq] using hmiss_cur hpos
        · exact hmissI hpos j hlt
      · intro Jni hJni
        m6_tiny_lets; apply wp_jnz_of
        · intro _
          m6_tiny_lets; rw [wp_load]
          refine ⟨_, by
            have hl_vals := @c0_load_full_vals c sH R m (litI.setWidth 64)
              (by change (litI.setWidth 64).toNat < sC.core.vals.length
                  rw [bv_c0_zext32_64]; exact hlitI_v) hm_arH
            simp only [Arg.val_var]; exact hl_vals, ?_⟩
          m6_tiny_lets; apply wp_jnz_of
          · intro hval_gt0; simp only [Arg.val_var] at hval_gt0
            m6_tiny_lets; rw [wp_load]
            refine ⟨_, by
              have hl_rsns := @c0_load_full_rsns c sH R m (BitVec.setWidth 64 (litI >>> 1))
                (by change (BitVec.setWidth 64 (litI >>> 1)).toNat < sC.core.rsns.length
                    rw [bv_c0_zext32_64, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                      Nat.pow_one]; exact hvI_r') hm_arH
              simp only [Arg.val_var]; exact hl_rsns, ?_⟩
            m6_tiny_lets; apply wp_jnz_of
            · intro hc; simp only [Arg.val_var, beq_iff_eq] at hc
              m6_tiny_lets
              apply wp_store_sep (by
                have hs_rsns := @c0_store_full_rsns c sH R m
                  (BitVec.setWidth 64 (litI >>> 1)) (dst.setWidth 32)
                  (by change (BitVec.setWidth 64 (litI >>> 1)).toNat < sC.core.rsns.length
                      rw [bv_c0_zext32_64, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                        Nat.pow_one]; exact hvI_r') hm_arH
                simp only [Arg.val_var]; exact hs_rsns)
              intro mS hmS
              have hrsn_eq : (sC.core.rsns[litI.toNat / 2]?.getD 0xFFFFFFFF#32).toNat =
                  src.toNat := by
                have h1 := congrArg BitVec.toNat hc; simp only [bv_c0_zext32_64] at h1
                rw [List.getElem?_eq_getElem hvI_r', Option.getD_some]
                simpa only [sH, litI, BitVec.toNat_ushiftRight,
                  Nat.shiftRight_eq_div_pow, Nat.pow_one] using h1
              have hvg : (0#32).slt ((sC.core.vals[litI.toNat]'hlitI_v).signExtend 32) = true := by
                simpa only [sH, litI, bv_c0_zext32_64] using hval_gt0
              have hidx_eq : (BitVec.setWidth 64 (litI >>> 1)).toNat = litI.toNat / 2 := by
                rw [bv_c0_zext32_64, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                  Nat.pow_one]
              rw [hidx_eq] at hmS
              have hr0_no : s.core.cur_level = 0 → False := fun hcl0 =>
                sweep_rsn_hit_false_at_root (hout_ok0.2 ((hdec_cl0 true).mpr hcl0)).1
                  (hlikeC.unchanged.2.2.1.trans hcl0) (by omega) (hlikeC.unchanged.1 ▸ hlitI_lt)
                  hlitI_v hvg hrsn_eq
              let rsnsR := sC.core.rsns.set (litI.toNat / 2) (dst.setWidth 32)
              have hrm_hit : 0 < s.core.cur_level → SweepReasonMapInv sPre.core
                  { sC.core with arena := arH, rsns := rsnsR } nsrc.toNat
                  (dst.toNat + 3 + st.toNat) := fun hp => by
                obtain ⟨_, hvC, _, hrC, _, _, _, hlits_eq⟩ := sweep_pos_lits_eq hout_ok0
                  ((hdec_cl0 false).mpr hp) harL_len harC_len hsrc_fit_cap hdst_src
                  hsrc_lits_eq hszH hdropH
                exact m6_sweep_rsn_hit_pos hwPre hsrc_ref hnsrc64 hdst_src hsrc_lt8
                  (hposL.get hp).2.2.2.2.2.2 (happend_mk rsnsR hlits_eq) rfl
                  (hvC.trans ((hposL.get hp).2.1.trans hpre.vals.symm)) hrC
                  hlenC0.core_ok.rsns_len (hpre.cv ▸ hcv_le) (hpre.cv ▸ hlitI_lt)
                  hlitI_v hvg hrsn_eq
              m6_to_group
              refine wp_join_group (fun (_ : Tup Val []) mK => M6RsnBranchInv c F_cur s sPre sC R
                arH nsrc.toNat dst.toNat st.toNat mark_allowed () mK) ?_ ?_
              · rintro _ ⟨⟩ mK hK; (first | rw [wp_jump] | m6_c0_steps); exact hJbrk (i, ()) mK hK
              · intro Jm hJm; m6_jnz
                · have hcl0 : s.core.cur_level = 0 := by
                    have h1 := congrArg BitVec.toNat hc
                    rw [bv64_ofNat_toNat_id hcl_lt] at h1; exact h1
                  exact absurd hcl0 hr0_no
                · have hpos : 0 < s.core.cur_level := by
                    by_cases h0 : s.core.cur_level = 0
                    · exfalso; apply hc; rw [h0]; rfl
                    · exact Nat.pos_of_ne_zero h0
                  m6_to_group
                  refine wp_join_group (fun (_ : Tup Val []) mR => mR = mS) ?_ ?_
                  · rintro _ ⟨⟩ mR hmR_eq; subst mR
                    have hdst_lt_arH : dst.toNat < arH.length := by omega
                    m6_tiny_lets
                    let nhdr := hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32)
                    let arR := arH.set dst.toNat (nhdr ||| 0x00200000#32)
                    let sS_ar : FullState :=
                      { sC with core := { sC.core with arena := arH, rsns := rsnsR } }
                    apply wp_store_sep (by
                      have hs_ar := @c0_store_full_arena c sS_ar R mS dst (nhdr ||| 0x00200000#32)
                        hdst_lt_arH hmS
                      simpa [Arg.val_var, lift2, nhdr, sS_ar, rsnsR] using hs_ar)
                    intro mR2 hmR2; rw [wp_jump]
                    obtain ⟨hcmpR, hrefsR, hclR⟩ := m6_set_hdr_at_ref_preserves
                      (k := { sC.core with arena := arH, rsns := rsnsR })
                      hcmpH.with_rsns harH_len (by omega) hdst_inH hbits.1 hbits.2.1
                    have hmR_cast : (FullMem c { sC with core := { sC.core with
                        arena := arR, rsns := rsnsR } } ⋆ R) mR2 := hmR2
                    exact hJm () _ (m6_hit_rsn_step (_F0 := F0) (_sL := sL)
                      hlenC0 (by simp [harH_len])
                      (fun _ hi => List.getElem?_set_ne (by omega))
                      (fun _ hj => List.getElem?_set_ne (by omega))
                      (by dsimp [arR]; rw [List.getElem?_set_ne (by omega)]; exact hszH)
                      (by dsimp [arR]; rw [List.getElem?_set_self hdst_lt_arH, Option.getD_some]
                          exact hbits.2.2.2.1)
                      (by dsimp [arR]; rw [List.getElem?_set_self hdst_lt_arH, harH_0,
                            Option.getD_some, Option.getD_some]
                          exact hbits.2.2.2.2.2.trans hbits.2.2.2.2.1.symm)
                      hdst_lt8 hvI_r' hcmpR (hrefsR ▸ hdst_inH) hr0_no
                      (fun hp => m6_set_hdr_preserves_srm hrefsR hclR (hrm_hit hp))
                      (fun hp _ idx hidx heq => by
                        obtain ⟨hvC, hrC⟩ := by
                          have h1 := hout_ok0.1 ((hdec_cl0 false).mpr hp)
                          exact And.intro h1.2.1 h1.2.2.2.2.1
                        have hdst_sw64 : dst.setWidth 32 =
                            (BitVec.ofNat 64 dst.toNat).setWidth 32 := by
                          apply BitVec.eq_of_toNat_eq
                          rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
                            bv64_ofNat_toNat_id (by omega)]
                        rw [hdst_sw64] at heq
                        have hve_lit := m6_rsn_eq_lit_of_hit hwPre hdst_src hsrc_lt8
                          (hposL.get hp).2.2.2.2.2.2 hrC
                          (hvC.trans ((hposL.get hp).2.1.trans hpre.vals.symm))
                          hlenC0.core_ok.rsns_len (hpre.cv ▸ hcv_le) (hpre.cv ▸ hlitI_lt)
                          hlitI_v hvg hrsn_eq hidx heq
                        refine ⟨by
                            dsimp [arR]; rw [List.getElem?_set_self hdst_lt_arH, Option.getD_some,
                              BitVec.and_or_distrib_right,
                              show (0x00200000#32 &&& 0x00200000#32) = 0x00200000#32 from rfl]
                            intro h0; have := congrArg (·[21]) h0; simp at this,
                          i.toNat, by rw [List.getElem?_set_ne (by omega), hszH]; exact hi_lt, ?_⟩
                        have hl_eq : arR[dst.toNat + 3 + i.toNat]?.getD 0#32 = litI := by
                          dsimp [arR]; rw [List.getElem?_set_ne (by omega)]; exact hlitI_eq
                        rw [hl_eq]; exact ⟨hve_lit.1.symm, hve_lit.2⟩)
                      hmR_cast)
                  · intro Js hJs; m6_jnz
                    · exact hJs () mS rfl
                    · have hfr_nil : first_red = 0xFFFFFFFF#64 := by
                        simpa [Arg.val_var] using hc
                      m6_jnz
                      · exact hJs () mS rfl
                      · have hred0 : (hdr0 &&& 0x00400000#32) = 0#32 := by
                          simpa [Arg.val_var] using hc
                        exact hJm () _ (m6_hit_rsn_step (_F0 := F0) (_sL := sL)
                          hlenC0 harH_len
                          (fun _ _ => rfl) (fun _ _ => rfl) hszH
                          (by rw [harH_0, Option.getD_some]; exact hbits.2.2.1) rfl
                          hdst_lt8 hvI_r' hcmpH.with_rsns hdst_inH hr0_no hrm_hit (fun _ hma => by
                            exfalso
                            simp only [mark_allowed,
                              decide_eq_false (by omega : s.core.cur_level ≠ 0),
                              Bool.not_false, Bool.true_and, Bool.or_eq_true, decide_eq_true_eq]
                              at hma
                            rcases hma with hfr_ne | hred_ne
                            · exact hfr_ne hfr_nil
                            · exact hred_ne hred0)
                          hmS)
            · intro hc; simp only [Arg.val_var, beq_eq_false_iff_ne, ne_eq] at hc
              rw [wp_jump]; refine hJni () m ⟨rfl, fun _ ⟨_, _, hrs⟩ => ?_⟩
              apply hc; apply BitVec.eq_of_toNat_eq; rw [bv_c0_zext32_64]
              have h1 := congrArg BitVec.toNat hrs
              rw [bv32_ofNat_toNat (by omega), List.getElem?_eq_getElem hvI_r',
                Option.getD_some] at h1
              simpa only [sH, litI, bv_c0_zext32_64, BitVec.toNat_ushiftRight,
                Nat.shiftRight_eq_div_pow, Nat.pow_one] using h1
          · intro hc; simp only [Arg.val_var] at hc
            rw [wp_jump]; refine hJni () m ⟨rfl, fun _ ⟨_, hvg, _⟩ => ?_⟩
            rw [List.getElem?_eq_getElem hlitI_v, Option.getD_some] at hvg
            exact Bool.false_ne_true (hc.symm.trans (by
              simpa only [sH, litI, bv_c0_zext32_64] using hvg))
        · intro hc
          simp only [Arg.val_var, BitVec.ult, decide_eq_false_iff_not, bv_c0_zext32_64,
            BitVec.toNat_ofNat] at hc
          rw [Nat.mod_eq_of_lt (by omega)] at hc
          change ¬ (litI.toNat / 2 < s.core.cur_vars) at hc; omega
    · have hi_eq : i.toNat = st.toNat := by omega
      try rw [wp_jump]
      exact hJbrk (i, ()) m (m6_rsn_miss_exit hwPre hpre hlenC0 harL_len harC_len harH_len hszH
        harH_0 hdropH hcmpH hdst_inH hdst_src hsrc_lt8 hdst_fit_arH hsrc_ref hnsrc64 hsrc_fit_cap
        hsrc_lits_eq hout_ok0 hdec_cl0 hposL happend_mk hbits.2.2.1
        (fun hpos j hj => hmissI hpos j (by omega)) hm_arH)

end

end LeanQbe.T.Examples.Kissat.Proof.Collect
