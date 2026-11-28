/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersWatch
public import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersArena
public import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersMoveSweep
public import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersSweep0
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1

/-!
# Arena Sweep State Framing & Invariants (`Proof.Collect.HelpersSweep1`)

`M6SweepLike`, `PreSweepClrInv`, `M6SweepLoopInv`, `M6PostMoveInv`, `M6RsnBranchInv`,
`M6ClearFallInv`, and pre-sweep / end-of-loop witness helpers for `full_arena_sweep_m6_wp`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Collect

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullKissatMath
open LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
open Kraken.Bedrock2.Test

public section

/-! ## 1. Sweep State Framing & Bin-Only Helpers -/

inductive M6SweepLike (s s' : FullState) : Prop where
  | mk (vals' : List (BitVec 8)) (flags' lvl' rsns' trl' tp' : List (BitVec 32))
      (te' : Nat) (unass' unfl' : BitVec 64) (wvec' wstk' arena' : List (BitVec 32))
      (wlen' : Nat) (wu' nb' oom' : BitVec 64) (ph' : List (BitVec 8)) (ws' : List (BitVec 32))
      (hEq : s' =
        { core :=
            { s.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
              trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
              wvec := wvec', wstk := wstk', arena := arena', wlen := wlen', wusable := wu',
              num_binary := nb', oom := oom' }
          scratch := { s.scratch with phases := ph', wsort := ws' } }) :
      M6SweepLike s s'

theorem M6SweepLike.of_copy {s sL : FullState} (h : M6SweepLike s sL)
    {arC : List (BitVec 32)} {valsC : List (BitVec 8)}
    {flagsC lvlC rsnsC trlC tpC : List (BitVec 32)} {teC : Nat} {unassC unflC : BitVec 64}
    {wvecC wstkC : List (BitVec 32)} {wlenC : Nat} {wuC nbC oomC : BitVec 64}
    {phC : List (BitVec 8)} {wsC : List (BitVec 32)} :
    M6SweepLike s
      { core := { sL.core with arena := arC, vals := valsC, flags := flagsC, lvl := lvlC,
                               rsns := rsnsC, trl := trlC, trail_pos := tpC, trail_end := teC,
                               unassigned := unassC, unflushed := unflC, wvec := wvecC,
                               wstk := wstkC, wlen := wlenC, wusable := wuC, num_binary := nbC,
                               oom := oomC }
        scratch := { sL.scratch with phases := phC, wsort := wsC } } := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  exact ⟨valsC, flagsC, lvlC, rsnsC, trlC, tpC, teC, unassC, unflC, wvecC, wstkC, arC, wlenC,
    wuC, nbC, oomC, phC, wsC, rfl⟩

theorem m6_binOnlySlice_of_full {F_cur : List (List Nat)} {k : FullCoreState}
    (hwlen : k.wlen ≤ k.wstk.length) (hbin : FullBinOnlyWatchesInv F_cur k)
    {l : Nat} (hl : l < 2 * k.cur_vars) :
    BinOnlyWatchSliceOk F_cur k l (fullWatchOffCore k l) (fullWatchSizeCore k l) := by
  have hb := Nat.le_trans (hbin.1.bounds l hl) hwlen
  suffices h : ∀ rem idx, idx + rem = fullWatchSizeCore k l →
      BinOnlyWatchSliceOk F_cur k l (fullWatchOffCore k l + idx) rem from
    by simpa using h (fullWatchSizeCore k l) 0 (Nat.zero_add _)
  intro rem; induction rem with
  | zero => intro _ _; exact .empty
  | succ rem ih =>
    intro idx heq
    have hlt_sz : idx < fullWatchSizeCore k l := by omega
    have hlt_len : fullWatchOffCore k l + idx < k.wstk.length := by omega
    obtain ⟨hf, hltv, hent⟩ := hbin.2 l hl idx hlt_sz
    have hget : k.wstk[fullWatchOffCore k l + idx]? =
        some (k.wstk[fullWatchOffCore k l + idx]'hlt_len) := List.getElem?_eq_getElem hlt_len
    simp only [hget, Option.getD_some] at hf hltv hent
    have hne : k.wstk[fullWatchOffCore k l + idx]'hlt_len ≠ 0xFFFFFFFF#32 := fun hsq =>
      hbin.1.no_sentinel l hl idx hlt_sz (by rw [hget, hsq])
    exact .bin hget hf hne hltv hent
      (by rw [Nat.add_assoc]; exact ih (idx + 1) (by omega))

theorem m6_binOnly_of_full {F_cur : List (List Nat)} {k : FullCoreState}
    (hwlen : k.wlen ≤ k.wstk.length) (hbin : FullBinOnlyWatchesInv F_cur k) :
    BinOnlyWatchesInv F_cur k :=
  ⟨hbin.1, fun _ hl => m6_binOnlySlice_of_full hwlen hbin hl⟩

theorem M6SweepLike.of_ar_rsns {s sC : FullState} (h : M6SweepLike s sC)
    {arH rsnsR : List (BitVec 32)} :
    M6SweepLike s { sC with core := { sC.core with arena := arH, rsns := rsnsR } } := by
  rcases h with ⟨valsC, flagsC, lvlC, _, trlC, tpC, teC, unassC, unflC, wvecC, wstkC, _,
    wlenC, wuC, nbC, oomC, phC, wsC, rfl⟩
  exact ⟨valsC, flagsC, lvlC, rsnsR, trlC, tpC, teC, unassC, unflC, wvecC, wstkC, arH, wlenC,
    wuC, nbC, oomC, phC, wsC, rfl⟩

theorem M6SweepLike.unchanged {s s' : FullState} (h : M6SweepLike s s') :
    s'.core.cur_vars = s.core.cur_vars ∧ s'.core.arena_len = s.core.arena_len ∧
    s'.core.cur_level = s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode ∧
    s'.core.frame_trail = s.core.frame_trail ∧ s'.core.frame_dec = s.core.frame_dec ∧
    s'.core.inconsistent = s.core.inconsistent ∧
    s'.scratch.extend_len = s.scratch.extend_len ∧
    s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
    s'.scratch.work_stk2 = s.scratch.work_stk2 := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

structure M6SweepLoopRootOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s sL : FullState) (start dst : Nat) (new_unit : Bool) : Prop where
  get : s.core.cur_level = 0 →
    start = 0 ∧
    FullWitnessInv c F0 F_cur { sL.core with arena_len := dst } ∧
    s.core.trail_end ≤ sL.core.trail_end ∧
    (new_unit = true → s.core.trail_end < sL.core.trail_end)

structure M6SweepLoopPosOk (s sPre sL : FullState) (src dst : Nat) (new_unit : Bool) :
    Prop where
  get : 0 < s.core.cur_level →
    new_unit = false ∧ sL.core.vals = s.core.vals ∧ sL.core.lvl = s.core.lvl ∧
    sL.core.trl = s.core.trl ∧ sL.core.trail_pos = s.core.trail_pos ∧
    sL.core.trail_end = s.core.trail_end ∧
    SweepReasonMapInv sPre.core sL.core src dst

/-! ## 2. Join & Loop Invariants for `full_arena_sweep_m6_wp` -/

inductive PreSweepClrInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) (fp : Nat)
    (cp : BitVec 64) (mL : Mem 64) : Prop where
  | mk
      (hcp_le : cp.toNat ≤ fp)
      (hdone : CleanIrredChain s.core.arena 0 cp.toNat)
      (hrem : CleanIrredChain s.core.arena cp.toNat fp)
      (hcp_in : cp.toNat < fp →
        cp.toNat ∈ fullArenaClauseRefsCore { s.core with arena_len := fp })
      (arL : List (BitVec 32))
      (harL_l : arL.length = c.arena_cap)
      (htailL : ∀ i, cp.toNat ≤ i → i < s.core.arena_len → arL[i]? = s.core.arena[i]?)
      (hmatchL : ∀ r ∈ fullArenaClauseRefsCore { s.core with arena_len := fp },
        r < cp.toNat →
        (arL[r]?.getD 0#32 &&& 0x00C80000#32) = 0#32 ∧ arL[r + 2]? = s.core.arena[r + 2]? ∧
        ∀ j < (s.core.arena[r + 2]?.getD 0#32).toNat, arL[r + 3 + j]? = s.core.arena[r + 3 + j]?)
      (hmL : (FullMem c { s with core := { s.core with arena := arL } } ⋆ R) mL) :
      PreSweepClrInv c s R fp cp mL

structure M6ReasonMarkRange (sPre sL : FullState) (first_red dst : Nat) : Prop where
  get : 0 < sPre.core.cur_level → ∀ r, RefInChain sL.core.arena first_red dst r →
    ∀ idx < sPre.core.trail_end,
      (sL.core.rsns[(sPre.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32).toNat = r →
      (sL.core.arena[r]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
      ∃ j < (sL.core.arena[r + 2]?.getD 0#32).toNat,
        let lit := (sL.core.arena[r + 3 + j]?.getD 0#32).toNat
        lit / 2 = (sPre.core.trl[idx]?.getD 0#32).toNat / 2 ∧
        sL.core.vals[lit]?.getD 0#8 = 1#8

inductive M6FirstRedOk (c : FullCfg) (F_cur : List (List Nat)) (s sPre sL : FullState)
    (start dst rwL : Nat) (first_red : BitVec 64) : Prop where
  | inl (heq : first_red = 0xFFFFFFFF#64) :
      M6FirstRedOk c F_cur s sPre sL start dst rwL first_red
  | inr (h : start ≤ first_red.toNat ∧ first_red.toNat < dst ∧
      CompactPrefixOk c F_cur s sL.core first_red.toNat ∧
      0 < rwL ∧ MoveRangeChain sL.core.arena first_red.toNat dst rwL ∧
      first_red.toNat ∈ fullArenaClauseRefsCore { sL.core with arena_len := dst } ∧
      M6ReasonMarkRange sPre sL first_red.toNat dst) :
      M6FirstRedOk c F_cur s sPre sL start dst rwL first_red

inductive M6SweepLoopInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s sPre : FullState) (R : Mem 64 → Prop) (start : Nat)
    (src dst first_red : BitVec 64) (has_iar new_unit : Bool) (mL : Mem 64) : Prop where
  | mk
      (hst_dst : start ≤ dst.toNat)
      (hdst_src : dst.toNat ≤ src.toNat)
      (hsrc_le : src.toNat ≤ s.core.arena_len)
      (hsrc_mem : src.toNat < s.core.arena_len → src.toNat ∈ fullArenaClauseRefs sPre)
      (hhas_iar : has_iar = true → first_red ≠ 0xFFFFFFFF#64)
      (sL : FullState)
      (rwL : Nat)
      (hlikeL : M6SweepLike s sL)
      (hlenL : sL.LengthsOk c)
      (hcmpL : CompactPrefixOk c F_cur s sL.core dst.toNat)
      (hcmpL_st : CompactPrefixOk c F_cur s sL.core start)
      (hlayL : WatchStackLayout sL.core)
      (hltL : ∀ l < 2 * sL.core.cur_vars,
        WatchSliceLtOk start F_cur sL.core l (fullWatchOff sL l) (fullWatchSize sL l))
      (hstL_in : start < dst.toNat →
        start ∈ fullArenaClauseRefsCore { sL.core with arena_len := dst.toNat })
      (hfrL : M6FirstRedOk c F_cur s sPre sL start dst.toNat rwL first_red)
      (htailL : ∀ i, src.toNat ≤ i → i < s.core.arena_len →
        sL.core.arena[i]? = sPre.core.arena[i]?)
      (hrootL : M6SweepLoopRootOk c F0 F_cur s sL start dst.toNat new_unit)
      (hposL : M6SweepLoopPosOk s sPre sL src.toNat dst.toNat new_unit)
      (hmL : (FullMem c sL ⋆ R) mL) :
      M6SweepLoopInv c F0 F_cur s sPre R start src dst first_red has_iar new_unit mL

theorem m6_trivial_post_witness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {dst : Nat} {fr : BitVec 64}
    (hw : FullWitnessInv c F0 F_cur { k with arena_len := dst }) :
    FullWitnessInv c F0 F_cur { { k with first_reducible := fr } with arena_len := dst } :=
  { hw with
    arena :=
      { len_ok := hw.arena.len_ok, refs_wf := hw.arena.refs_wf, shrk_term := hw.arena.shrk_term,
        lits_lt := hw.arena.lits_lt, entails := hw.arena.entails }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

inductive M6PostLike (s sM : FullState) : Prop where
  | mk (v : List (BitVec 8)) (f l r t tp : List (BitVec 32)) (te : Nat) (u uf : BitVec 64)
      (wv ws ar : List (BitVec 32)) (wl : Nat) (wu fr nb o : BitVec 64)
      (hEq : sM.core =
        { s.core with
          vals := v, flags := f, lvl := l, rsns := r, trl := t, trail_pos := tp, trail_end := te,
          unassigned := u, unflushed := uf, wvec := wv, wstk := ws, arena := ar, wlen := wl,
          wusable := wu, first_reducible := fr, num_binary := nb, oom := o }) :
      M6PostLike s sM

theorem m6_core_lengths_upd {c : FullCfg} {k : FullCoreState} (h : k.LengthsOk c)
    {al : Nat} (hal : al ≤ c.arena_cap) (ag fr ni nr : BitVec 64) :
    FullCoreState.LengthsOk c
      { k with
        arena_len := al, arena_garbage := ag, first_reducible := fr, num_irred := ni,
        num_redundant := nr } := by
  cases h; constructor <;> (try exact hal) <;> assumption

theorem m6_witness_upd_stats {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (ag ni nr : BitVec 64) :
    FullWitnessInv c F0 F_cur
      { k with arena_garbage := ag, num_irred := ni, num_redundant := nr } :=
  { hw with
    arena :=
      { len_ok := hw.arena.len_ok, refs_wf := hw.arena.refs_wf, shrk_term := hw.arena.shrk_term,
        lits_lt := hw.arena.lits_lt, entails := hw.arena.entails }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem m6_start_in_post_move {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {kE kM : FullCoreState} {start fr dst : Nat}
    (hcmpE_fr : CompactPrefixOk c F_cur s kE fr) (harE : kE.arena.length = c.arena_cap)
    (harM : kM.arena.length = c.arena_cap) (hcv : kM.cur_vars = kE.cur_vars)
    (hdst_cap : dst ≤ c.arena_cap) (hfr_lt : fr < dst) (hfr_st : start ≤ fr)
    (hpre : PrefixAgrees fr kE.arena kM.arena)
    (hstE : start < dst → start ∈ fullArenaClauseRefsCore { kE with arena_len := dst })
    (hfrM : fr ∈ fullArenaClauseRefsCore { kM with arena_len := dst }) :
    start < dst → start ∈ fullArenaClauseRefsCore { kM with arena_len := dst } := fun hst_lt => by
  have hcmp' : CompactPrefixOk c F_cur s { kE with arena_len := dst } fr :=
    (arenaPrefix_preserves_compact (k := kE) (k' := { kE with arena_len := dst }) hcmpE_fr rfl
      harE harE (by omega) (fun _ _ => rfl)).1
  rcases Nat.eq_or_lt_of_le hfr_st with heq | hlt
  · rw [heq]; exact hfrM
  · have hst_e := m6_refs_lt_compactPrefix hcmp' (by dsimp only; omega) start (hstE hst_lt) hlt
    have htr := arenaPrefix_preserves_compact (k' := { kM with arena_len := dst }) hcmp' hcv harE
      harM (by omega) hpre
    rw [← htr.2.1] at hst_e
    exact (fullArenaClauseRefsCore_mono_prefix (Nat.le_of_lt hfr_lt) htr.1.1 _ hst_e).1

inductive M6PostMoveInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (start : Nat) (dst : BitVec 64)
    (unsat new_unit : Bool) (_ : Tup Val []) (mM : Mem 64) : Prop where
  | mk (sM : FullState)
      (hpostM : M6PostLike s sM)
      (hlenM : sM.LengthsOk c)
      (hcvM : sM.core.cur_vars = s.core.cur_vars)
      (halM : sM.core.arena_len = s.core.arena_len)
      (hclM : sM.core.cur_level = s.core.cur_level)
      (hdmM : sM.core.dense_mode = s.core.dense_mode)
      (hftM : sM.core.frame_trail = s.core.frame_trail)
      (hfdM : sM.core.frame_dec = s.core.frame_dec)
      (hincM : sM.core.inconsistent = s.core.inconsistent)
      (helM : sM.scratch.extend_len = s.scratch.extend_len)
      (hws1M : sM.scratch.work_stk1 = s.scratch.work_stk1)
      (hws2M : sM.scratch.work_stk2 = s.scratch.work_stk2)
      (hwM : FullWitnessInv c F0 F_cur { sM.core with arena_len := dst.toNat })
      (hnoM : ∀ r ∈ fullArenaClauseRefsCore { sM.core with arena_len := dst.toNat },
        (fullArenaHdrCore { sM.core with arena_len := dst.toNat } r &&& 0x00800000#32) = 0#32 ∧
        fullArenaClauseGarbCore { sM.core with arena_len := dst.toNat } r = false)
      (hndM : FullArenaVarsNodup s →
        ∀ r ∈ fullArenaClauseRefsCore { sM.core with arena_len := dst.toNat },
          ((fullArenaClauseLitsCore { sM.core with arena_len := dst.toNat } r).map (· / 2)).Nodup)
      (hstM_in : start < dst.toNat →
        start ∈ fullArenaClauseRefsCore { sM.core with arena_len := dst.toNat })
      (hunsM : unsat = true → s.core.cur_level = 0 ∧ F0.Unsat)
      (hunitM : new_unit = true → s.core.cur_level = 0 ∧ s.core.trail_end < sM.core.trail_end)
      (hposM : 0 < s.core.cur_level → unsat = false ∧ new_unit = false ∧
        sM.core.vals = s.core.vals ∧ sM.core.lvl = s.core.lvl ∧ sM.core.trl = s.core.trl ∧
        sM.core.trail_pos = s.core.trail_pos ∧ sM.core.trail_end = s.core.trail_end)
      (hmM : (FullMem c sM ⋆ R) mM) :
      M6PostMoveInv c F0 F_cur s R start dst unsat new_unit () mM

inductive M6RsnBranchInv (c : FullCfg) (F_cur : List (List Nat)) (s sPre sC : FullState)
    (R : Mem 64 → Prop) (arH : List (BitVec 32)) (nsrc dst st : Nat) (mark_allowed : Bool)
    (_ : Tup Val []) (mR : Mem 64) : Prop where
  | mk (arR rsnsR : List (BitVec 32))
      (harR_len : arR.length = c.arena_cap)
      (hrsnsR_len : rsnsR.length = c.max_vars)
      (hpreR : ∀ i < dst, arR[i]? = arH[i]?)
      (hbodyR : ∀ j, dst + 3 ≤ j → arR[j]? = arH[j]?)
      (hszR : (arR[dst + 2]?.getD 0#32).toNat = st)
      (hflR : (arR[dst]?.getD 0#32 &&& 0x00880000#32) = 0#32)
      (hredR : (arR[dst]?.getD 0#32 &&& 0x00400000#32) =
        (arH[dst]?.getD 0#32 &&& 0x00400000#32))
      (hcmpR : CompactPrefixOk c F_cur s { sC.core with arena := arR, rsns := rsnsR }
        (dst + 3 + st))
      (hdst_inR : dst ∈ fullArenaClauseRefsCore
        { sC.core with arena := arR, rsns := rsnsR, arena_len := dst + 3 + st })
      (hrsns_lt_dst : ∀ idx < sPre.core.trail_end,
        (rsnsR[(sPre.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat < dst →
        rsnsR[(sPre.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
          sC.core.rsns[(sPre.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32)
      (hrsns_r0 : s.core.cur_level = 0 → rsnsR = sC.core.rsns)
      (hrmR : 0 < s.core.cur_level →
        SweepReasonMapInv sPre.core { sC.core with arena := arR, rsns := rsnsR } nsrc
          (dst + 3 + st))
      (hmkR : 0 < s.core.cur_level → mark_allowed = true →
        ∀ idx < sPre.core.trail_end,
          (rsnsR[(sPre.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat = dst →
          (arR[dst]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
          ∃ j < (arR[dst + 2]?.getD 0#32).toNat,
            let lit := (arR[dst + 3 + j]?.getD 0#32).toNat
            lit / 2 = (sPre.core.trl[idx]?.getD 0#32).toNat / 2 ∧
            sC.core.vals[lit]?.getD 0#8 = 1#8)
      (hmR : (FullMem c { sC with core := { sC.core with arena := arR, rsns := rsnsR } } ⋆ R) mR) :
      M6RsnBranchInv c F_cur s sPre sC R arH nsrc dst st mark_allowed () mR

inductive M6ClearFallInv (c : FullCfg) (F_cur : List (List Nat)) (s sPre sE : FullState)
    (R : Mem 64 → Prop) (first_red dst : Nat) (cp : BitVec 64) (mF : Mem 64) : Prop where
  | mk
      (hfr_cp : first_red ≤ cp.toNat)
      (hcp_le : cp.toNat ≤ dst)
      (arL : List (BitVec 32))
      (rwRem : Nat)
      (harL_l : arL.length = c.arena_cap)
      (hpreL : ∀ i, i < first_red → arL[i]? = sE.core.arena[i]?)
      (htailL : ∀ i, cp.toNat ≤ i → i < dst → arL[i]? = sE.core.arena[i]?)
      (hmvRem : MoveRangeChain sE.core.arena cp.toNat dst rwRem)
      (hcmpL : CompactPrefixOk c F_cur s { sE.core with arena := arL } dst)
      (hrmL : 0 < s.core.cur_level →
        SweepReasonMapInv sPre.core { sE.core with arena := arL } sPre.core.arena_len dst)
      (hrefsL : fullArenaClauseRefsCore { sE.core with arena := arL, arena_len := dst } =
        fullArenaClauseRefsCore { sE.core with arena_len := dst })
      (hcp_in : cp.toNat < dst →
        cp.toNat ∈ fullArenaClauseRefsCore { sE.core with arena := arL, arena_len := dst })
      (hmF : (FullMem c { sE with core := { sE.core with arena := arL } } ⋆ R) mF) :
      M6ClearFallInv c F_cur s sPre sE R first_red dst cp mF

/-! ## 3. Post-Loop & Pre-Sweep Helpers -/

theorem m6_root_post_move_witness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {kE kM : FullCoreState} {dst : Nat}
    (hwEnd : FullWitnessInv c F0 F_cur { kE with arena_len := dst })
    (haM : FullArenaClausesInv c F_cur { kM with arena_len := dst })
    (hwatM : ModeWatchesInv F_cur { kM with arena_len := dst })
    (hvals : kM.vals = kE.vals) (hlvl : kM.lvl = kE.lvl) (htrl : kM.trl = kE.trl)
    (htp : kM.trail_pos = kE.trail_pos) (hte : kM.trail_end = kE.trail_end)
    (hcl : kM.cur_level = kE.cur_level) (hcv : kM.cur_vars = kE.cur_vars)
    (hft : kM.frame_trail = kE.frame_trail) (hfd : kM.frame_dec = kE.frame_dec)
    (hinc : kM.inconsistent = kE.inconsistent) (_hcl0 : kE.cur_level = 0)
    (hrsn_ff : ∀ idx < kE.trail_end,
      kM.rsns[(kE.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    FullWitnessInv c F0 F_cur { kM with arena_len := dst } :=
  { ext_sound := by dsimp only; rw [hcv]; exact hwEnd.ext_sound
    inconsistent_sound := by dsimp only; rw [hinc]; exact hwEnd.inconsistent_sound
    arena := haM
    watches := hwatM
    cur_level_le := by dsimp only; rw [hcl, hte]; exact hwEnd.cur_level_le
    trail_lits_lt := fun i hi => by
      dsimp only at hi ⊢; rw [htrl, hcv]; exact hwEnd.trail_lits_lt i (hte ▸ hi)
    trail_vars_nodup := fun i j hi hj h => by
      dsimp only at hi hj h; rw [htrl] at h
      exact hwEnd.trail_vars_nodup i j (hte ▸ hi) (hte ▸ hj) h
    vals_domain := fun l hl => by
      dsimp only at hl ⊢; rw [hvals]; exact hwEnd.vals_domain l (hcv ▸ hl)
    vals_true_iff := fun l hl => by
      dsimp only at hl ⊢; rw [hvals, hte, htrl]; exact hwEnd.vals_true_iff l (hcv ▸ hl)
    vals_false_iff := fun l hl => by
      dsimp only at hl ⊢; rw [hvals, hte, htrl]; exact hwEnd.vals_false_iff l (hcv ▸ hl)
    lvl_le := fun i hi => by
      dsimp only at hi ⊢; rw [hlvl, htrl, hcl]; exact hwEnd.lvl_le i (hte ▸ hi)
    dec_earliest := fun i j hi hj hlt hdec => by
      dsimp only at hi hj hlt hdec; rw [hlvl, htrl] at hlt hdec
      exact hwEnd.dec_earliest i j (hte ▸ hi) (hte ▸ hj) hlt
        ⟨hdec.1, hwEnd.level0_rsn_none j (hte ▸ hj)
          (by have := hwEnd.lvl_le j (hte ▸ hj); change _ ≤ kE.cur_level at this; omega)⟩
    levels_inhabited := fun L h1 h2 => by
      dsimp only at h2 ⊢; rw [hte, hlvl, htrl]; exact hwEnd.levels_inhabited L h1 (hcl ▸ h2)
    level0_sound := fun i hi h0 => by
      dsimp only at hi h0 ⊢; rw [hlvl, htrl] at h0; rw [htrl]
      exact hwEnd.level0_sound i (hte ▸ hi) h0
    trail_pos_inv := fun i hi => by
      dsimp only at hi ⊢; rw [htp, htrl]; exact hwEnd.trail_pos_inv i (hte ▸ hi)
    level0_rsn_none := fun idx hidx _ => by
      dsimp only at hidx ⊢; rw [htrl]; exact hrsn_ff idx (hte ▸ hidx)
    frame_trail_lt := fun L hL => by
      dsimp only at hL ⊢; rw [hft, hte]; exact hwEnd.frame_trail_lt L (hcl ▸ hL)
    frame_trail_mono := fun L1 L2 h1 h2 => by
      dsimp only at h2 ⊢; rw [hft]; exact hwEnd.frame_trail_mono L1 L2 h1 (hcl ▸ h2)
    frame_trail_before_lt := fun L h1 h2 i hi => by
      dsimp only at h2 hi ⊢; rw [hft] at hi; rw [hlvl, htrl]
      exact hwEnd.frame_trail_before_lt L h1 (hcl ▸ h2) i hi
    frame_dec_lt := fun L h1 h2 => by
      dsimp only at h2 ⊢; rw [hfd, hcv]; exact hwEnd.frame_dec_lt L h1 (hcl ▸ h2)
    reason_inv := fun idx hidx hne => by
      dsimp only at hidx hne; rw [htrl] at hne
      exact absurd (hrsn_ff idx (hte ▸ hidx)) hne
    reason_lit_mem := fun idx hidx hne => by
      dsimp only at hidx hne; rw [htrl] at hne
      exact absurd (hrsn_ff idx (hte ▸ hidx)) hne }

theorem cleanIrredChain_three_le {ar : List (BitVec 32)} {lo hi : Nat}
    (h : CleanIrredChain ar lo hi) (hlt : lo < hi) : lo + 3 ≤ hi := by
  cases h with
  | empty => omega
  | step h3 => exact h3

theorem m6_sweep_end_witness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sPre sL : FullState} {start dst : Nat} {new_unit : Bool}
    (hwPre : FullWitnessInv c F0 F_cur sPre.core)
    (hdk : 0 < start → sL.core.dense_mode = 0#64)
    (hlenL : sL.LengthsOk c) (hlikeL : M6SweepLike s sL)
    (hcv_pre : sPre.core.cur_vars = s.core.cur_vars)
    (hcl_pre : sPre.core.cur_level = s.core.cur_level)
    (hft_pre : sPre.core.frame_trail = s.core.frame_trail)
    (hfd_pre : sPre.core.frame_dec = s.core.frame_dec)
    (hinc_pre : sPre.core.inconsistent = s.core.inconsistent)
    (hvals_pre : sPre.core.vals = s.core.vals)
    (hlvl_pre : sPre.core.lvl = s.core.lvl)
    (htrl_pre : sPre.core.trl = s.core.trl)
    (htp_pre : sPre.core.trail_pos = s.core.trail_pos)
    (hte_pre : sPre.core.trail_end = s.core.trail_end)
    (hst_dst : start ≤ dst) (hst_al : start ≤ sL.core.arena_len)
    (hcmpL : CompactPrefixOk c F_cur s sL.core dst)
    (hcmpL_st : CompactPrefixOk c F_cur s sL.core start)
    (hlayL : WatchStackLayout sL.core)
    (hltL : ∀ l < 2 * sL.core.cur_vars,
      WatchSliceLtOk start F_cur sL.core l (fullWatchOff sL l) (fullWatchSize sL l))
    (hrootL : M6SweepLoopRootOk c F0 F_cur s sL start dst new_unit)
    (hposL : M6SweepLoopPosOk s sPre sL sPre.core.arena_len dst new_unit) :
    FullWitnessInv c F0 F_cur { sL.core with arena_len := dst } := by
  by_cases hcl0 : s.core.cur_level = 0
  · exact (hrootL.get hcl0).2.1
  · have hpos : 0 < s.core.cur_level := Nat.pos_of_ne_zero hcl0
    obtain ⟨_, hvals, hlvl, htrl, htp, hte, hrm⟩ := hposL.get hpos
    have hu := hlikeL.unchanged
    have hdk' : 0 < start → sL.core.dense_mode = 0#64 := fun hs => hdk hs
    have hlay_dst : WatchStackLayout { sL.core with arena_len := dst } :=
      hlayL.with_wstk rfl rfl rfl rfl
    have hkeep : ∀ r ∈ fullArenaClauseRefsCore sL.core, r < start →
        r ∈ fullArenaClauseRefsCore { sL.core with arena_len := dst } := fun r hr hlt =>
      (fullArenaClauseRefsCore_mono_prefix hst_dst hcmpL_st.1 r
        (m6_refs_lt_compactPrefix hcmpL_st hst_al r hr hlt)).1
    exact SweepReasonMapInv.toFullWitnessInvLt hlenL.core_ok hwPre hcmpL.1 hdk' hlay_dst hltL
      hkeep (hvals.trans hvals_pre.symm) (hlvl.trans hlvl_pre.symm) (htrl.trans htrl_pre.symm)
      (htp.trans htp_pre.symm) (hte.trans hte_pre.symm) (hu.2.2.1.trans hcl_pre.symm)
      (hu.1.trans hcv_pre.symm) (hu.2.2.2.2.1.trans hft_pre.symm)
      (hu.2.2.2.2.2.1.trans hfd_pre.symm) (hu.2.2.2.2.2.2.1.trans hinc_pre.symm) hrm

theorem m6_pre_clr_step {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {fp : Nat} {cp : BitVec 64} {m' : Mem 64}
    (hcp_lt : cp.toNat < fp) (hcp3 : cp.toNat + 3 ≤ fp) (hfp_le : fp ≤ s.core.arena_len)
    (hal_le : s.core.arena_len ≤ c.arena_cap) (hcap_bd : c.arena_cap < 2 * dimacsBound)
    (hdone : CleanIrredChain s.core.arena 0 cp.toNat)
    (hrem : CleanIrredChain s.core.arena cp.toNat fp)
    (hcp_in : cp.toNat < fp →
      cp.toNat ∈ fullArenaClauseRefsCore { s.core with arena_len := fp })
    {arL : List (BitVec 32)} (harL_l : arL.length = c.arena_cap)
    (htailL : ∀ i, cp.toNat ≤ i → i < s.core.arena_len → arL[i]? = s.core.arena[i]?)
    (hmatchL : ∀ r ∈ fullArenaClauseRefsCore { s.core with arena_len := fp }, r < cp.toNat →
      (arL[r]?.getD 0#32 &&& 0x00C80000#32) = 0#32 ∧ arL[r + 2]? = s.core.arena[r + 2]? ∧
      ∀ j < (s.core.arena[r + 2]?.getD 0#32).toNat, arL[r + 3 + j]? = s.core.arena[r + 3 + j]?)
    {hdr sz : BitVec 32} (hhdr : hdr = arL[cp.toNat]'(by rw [harL_l]; omega))
    (hsz : sz = arL[cp.toNat + 2]'(by rw [harL_l]; omega))
    {ar' : List (BitVec 32)}
    (har'_eq : ar' = arL.set cp.toNat (hdr &&& ~~~0x00200000#32) ∨
      ((hdr &&& 0x00200000#32) = 0#32 ∧ ar' = arL))
    (hm' : (FullMem c { s with core := { s.core with arena := ar' } } ⋆ R) m') :
    3 ≤ sz.toNat ∧ cp.toNat + 3 + sz.toNat ≤ fp ∧
    PreSweepClrInv c s R fp (cp + (3#64 + sz.setWidth 64)) m' := by
  have hdb : dimacsBound = 2 ^ 28 := rfl
  cases hrem with
  | empty => omega
  | @step _ _ h3 hfl_cp hsz3 hfit hrem_nxt =>
    have hcp_ar : arL[cp.toNat]? = s.core.arena[cp.toNat]? :=
      htailL cp.toNat (Nat.le_refl _) (by omega)
    have hcp2_ar : arL[cp.toNat + 2]? = s.core.arena[cp.toNat + 2]? :=
      htailL (cp.toNat + 2) (by omega) (by omega)
    have hhdr_s : s.core.arena[cp.toNat]? = some hdr := by
      rw [← hcp_ar, hhdr]; exact List.getElem?_eq_getElem _
    have hsz_s : s.core.arena[cp.toNat + 2]? = some sz := by
      rw [← hcp2_ar, hsz]; exact List.getElem?_eq_getElem _
    have hfl_hdr : (hdr &&& 0x00C80000#32) = 0#32 := by rwa [hhdr_s, Option.getD_some] at hfl_cp
    have hsz_eq : (s.core.arena[cp.toNat + 2]?.getD 0#32).toNat = sz.toNat := by
      rw [hsz_s, Option.getD_some]
    rw [hsz_eq] at hfit hrem_nxt hsz3
    have hcp'_eq : (cp + (3#64 + sz.setWidth 64)).toNat = cp.toNat + 3 + sz.toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_add, show (3#64).toNat = 3 from rfl,
        zext_toNat (n := 64) sz (by decide),
        Nat.mod_eq_of_lt (by omega : 3 + sz.toNat < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : cp.toNat + (3 + sz.toNat) < 2 ^ 64), Nat.add_assoc]
    have hnx_fp : fullArenaNextOff s.core.arena fp cp.toNat = cp.toNat + 3 + sz.toNat := by
      have hsh := (bv32_mask_00C80000_props _ hfl_cp).1
      unfold fullArenaNextOff
      simp [show ¬ (cp.toNat + 3 > fp) by omega, hsz_s,
        show ¬ (cp.toNat + 3 + sz.toNat > fp) by omega, hsh]
    refine ⟨hsz3, hfit, ?_⟩
    refine ⟨hcp'_eq ▸ hfit, ?_, ?_, fun hlt' => ?_, ar', ?_, fun i hi1 hi2 => ?_,
      fun r hr hr_lt => ?_, hm'⟩
    · rw [hcp'_eq]
      exact hdone.snoc (by omega) hfl_cp (by rw [hsz_eq]; exact hsz3) (by rw [hsz_eq])
    · rw [hcp'_eq]; exact hrem_nxt
    · rw [hcp'_eq] at hlt' ⊢
      have h3_n := cleanIrredChain_three_le hrem_nxt hlt'
      have hmem := fullArenaScanRefs_mem_next (ar := s.core.arena) (alen := fp)
        (Nat.le_refl fp) (hcp_in hcp_lt) (by rw [hnx_fp]; exact h3_n)
      rwa [hnx_fp] at hmem
    · rcases har'_eq with rfl | ⟨_, rfl⟩ <;> simp [harL_l]
    · rw [hcp'_eq] at hi1
      rcases har'_eq with rfl | ⟨_, rfl⟩
      · rw [List.getElem?_set_ne (by omega)]; exact htailL i (by omega) hi2
      · exact htailL i (by omega) hi2
    · rw [hcp'_eq] at hr_lt
      have har'_ag : ∀ q, q ≠ cp.toNat → ar'[q]? = arL[q]? := fun q hq => by
        rcases har'_eq with rfl | ⟨_, rfl⟩
        · exact List.getElem?_set_ne hq.symm
        · rfl
      by_cases hrc : r < cp.toNat
      · have hdisj := cleanIrredChain_disjoint_lt hdone
          (CleanIrredChain.step h3 hfl_cp (by rw [hsz_eq]; exact hsz3)
            (by rw [hsz_eq]; exact hfit) (by rw [hsz_eq]; exact hrem_nxt))
          r hr hrc
        obtain ⟨h1, h2, h3m⟩ := hmatchL r hr hrc
        exact ⟨by rwa [har'_ag r (by omega)], by rwa [har'_ag (r + 2) (by omega)], fun j hj => by
          rw [har'_ag (r + 3 + j) (by omega)]; exact h3m j hj⟩
      · have hreq : r = cp.toNat := by
          rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt hrc) with rfl | hgt
          · rfl
          · have hd := fullArenaScanRefs_disjoint (hcp_in hcp_lt) hr hgt
            rw [hnx_fp] at hd; omega
        subst r
        refine ⟨?_, ?_, fun j hj => ?_⟩
        · rcases har'_eq with rfl | ⟨_, rfl⟩
          · rw [List.getElem?_set_self (by rw [harL_l]; omega), Option.getD_some,
              bv32_clear_rsn_keeps_clean, hfl_hdr]
          · rw [hcp_ar]; exact hfl_cp
        · rw [har'_ag (cp.toNat + 2) (by omega)]; exact hcp2_ar
        · rw [har'_ag (cp.toNat + 3 + j) (by omega)]
          exact htailL (cp.toNat + 3 + j) (by omega) (by rw [hsz_eq] at hj; omega)

end

end LeanQbe.T.Examples.Kissat.Proof.Collect
