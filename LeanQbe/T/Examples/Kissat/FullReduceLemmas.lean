/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullReduceLemmas4
import all Kraken.Mem
import all Kraken.Separation

/-!
# Stage-4 (`D-Full`) GC / Sweep `Func.wp` Proofs — Part 5 (`full_arena_sweep`)

Main arena compaction loop, reason-remapping loop, `last_learned` sentinel reset, and final:
10. `full_arena_sweep` (`Full2.lean:149-200`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat.Full.FullReduceSpecs
open LeanQbe.T.Examples.Kissat.Full.FullReduceHelpers
open scoped FullArenaTactics FullReduceTactics

/-! ## 1. Sweep state framing & header-write helpers -/





private def SweepLike (s s' : FullState) : Prop :=
  ∃ vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' wlen' wu' nb' oom' ph' ws',
    s' =
      { core :=
          { s.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
            wvec := wvec', wstk := wstk', arena := arena', wlen := wlen', wusable := wu',
            num_binary := nb', oom := oom' }
        scratch := { s.scratch with phases := ph', wsort := ws' } }

private theorem SweepLike.of_copy {s sL : FullState} (h : SweepLike s sL)
    {arC : List (BitVec 32)} {valsC : List (BitVec 8)}
    {flagsC lvlC rsnsC trlC tpC : List (BitVec 32)} {teC : Nat} {unassC unflC : BitVec 64}
    {wvecC wstkC : List (BitVec 32)} {wlenC : Nat} {wuC nbC oomC : BitVec 64}
    {phC : List (BitVec 8)} {wsC : List (BitVec 32)} :
    SweepLike s
      { core := { sL.core with arena := arC, vals := valsC, flags := flagsC, lvl := lvlC,
                               rsns := rsnsC, trl := trlC, trail_pos := tpC, trail_end := teC,
                               unassigned := unassC, unflushed := unflC, wvec := wvecC,
                               wstk := wstkC, wlen := wlenC, wusable := wuC, num_binary := nbC,
                               oom := oomC }
        scratch := { sL.scratch with phases := phC, wsort := wsC } } := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  exact ⟨valsC, flagsC, lvlC, rsnsC, trlC, tpC, teC, unassC, unflC, wvecC, wstkC, arC, wlenC,
    wuC, nbC, oomC, phC, wsC, rfl⟩

private theorem SweepLike.of_ar_rsns {s sC : FullState} (h : SweepLike s sC)
    {arH rsnsR : List (BitVec 32)} :
    SweepLike s { sC with core := { sC.core with arena := arH, rsns := rsnsR } } := by
  rcases h with ⟨valsC, flagsC, lvlC, _, trlC, tpC, teC, unassC, unflC, wvecC, wstkC, _,
    wlenC, wuC, nbC, oomC, phC, wsC, rfl⟩
  exact ⟨valsC, flagsC, lvlC, rsnsR, trlC, tpC, teC, unassC, unflC, wvecC, wstkC, arH, wlenC,
    wuC, nbC, oomC, phC, wsC, rfl⟩

private theorem SweepLike.unchanged {s s' : FullState} (h : SweepLike s s') :
    s'.core.cur_vars = s.core.cur_vars ∧ s'.core.arena_len = s.core.arena_len ∧
    s'.core.cur_level = s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode ∧
    s'.core.frame_trail = s.core.frame_trail ∧ s'.core.frame_dec = s.core.frame_dec ∧
    s'.core.inconsistent = s.core.inconsistent := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private def SweepLoopRootOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s sL : FullState) (dst : Nat) (new_unit : Bool) : Prop :=
  s.core.cur_level = 0 →
  FullWitnessInv c F0 F_cur { sL.core with arena_len := dst } ∧
  s.core.trail_end ≤ sL.core.trail_end ∧
  (new_unit = true → s.core.trail_end < sL.core.trail_end)

private def SweepLoopPosOk (s s0 sL : FullState) (src dst : Nat) (new_unit : Bool) : Prop :=
  0 < s.core.cur_level →
  new_unit = false ∧ sL.core.vals = s.core.vals ∧ sL.core.lvl = s.core.lvl ∧
  sL.core.trl = s.core.trl ∧ sL.core.trail_pos = s.core.trail_pos ∧
  sL.core.trail_end = s.core.trail_end ∧
  SweepReasonMapInv s0.core sL.core src dst

private def SweepHappendCore (k0 kL kH : FullCoreState) (dst src : Nat) : Prop :=
  fullArenaClauseRefsCore kH = fullArenaClauseRefsCore { kL with arena_len := dst } ++ [dst] ∧
  (∀ r ∈ fullArenaClauseRefsCore { kL with arena_len := dst },
    fullArenaClauseGarbCore kH r =
      fullArenaClauseGarbCore { kL with arena_len := dst } r ∧
    fullArenaClauseLitsCore kH r =
      fullArenaClauseLitsCore { kL with arena_len := dst } r) ∧
  fullArenaClauseGarbCore kH dst = false ∧
  fullArenaClauseLitsCore kH dst = fullArenaClauseLitsCore k0 src

private def ArenaSweepExitInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop)
    (arg : Tup Val [i64, i64, i64, i64, i64, .bool, .bool]) (mE : Mem 64) : Prop :=
  let (_src, dst, _first_red, _irred, _redd, unsat, new_unit, ()) := arg
  dst.toNat ≤ s.core.arena_len ∧
  ∃ sE : FullState, SweepLike s sE ∧
    let kEnd : FullCoreState := { sE.core with arena_len := dst.toNat }
    sE.LengthsOk c ∧ FullWitnessInv c F0 F_cur kEnd ∧
    (∀ r ∈ fullArenaClauseRefsCore kEnd,
      (fullArenaHdrCore kEnd r &&& 0x00800000#32) = 0#32 ∧
      fullArenaClauseGarbCore kEnd r = false) ∧
    (FullArenaVarsNodup s →
      ∀ r ∈ fullArenaClauseRefsCore kEnd, ((fullArenaClauseLitsCore kEnd r).map (· / 2)).Nodup) ∧
    (unsat = true → s.core.cur_level = 0 ∧ F0.Unsat) ∧
    (new_unit = true → s.core.cur_level = 0 ∧ s.core.trail_end < sE.core.trail_end) ∧
    (0 < s.core.cur_level → unsat = false ∧ new_unit = false ∧ sE.core.vals = s.core.vals ∧
      sE.core.lvl = s.core.lvl ∧ sE.core.trl = s.core.trl ∧ sE.core.trail_pos = s.core.trail_pos ∧
      sE.core.trail_end = s.core.trail_end) ∧
    (FullMem c sE ⋆ R) mE

private def ArenaSweepLoopInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s0 : FullState) (R : Mem 64 → Prop)
    (arg : Tup Val [i64, i64, i64, i64, i64, .bool]) (mL : Mem 64) : Prop :=
  let (src, dst, _fr, _ir, _rd, new_unit, ()) := arg
  dst.toNat ≤ src.toNat ∧ src.toNat ≤ s.core.arena_len ∧
  (src.toNat < s.core.arena_len → src.toNat ∈ fullArenaClauseRefs s0) ∧
  ∃ sL : FullState, SweepLike s sL ∧
    sL.LengthsOk c ∧ CompactPrefixOk c F_cur s sL.core dst.toNat ∧ BinOnlyWatchesInv F_cur sL.core ∧
    (∀ i, src.toNat ≤ i → i < s.core.arena_len → sL.core.arena[i]? = s.core.arena[i]?) ∧
    SweepLoopRootOk c F0 F_cur s sL dst.toNat new_unit ∧
    SweepLoopPosOk s s0 sL src.toNat dst.toNat new_unit ∧
    (FullMem c sL ⋆ R) mL

private def LastLearnedLoopInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (valsE : List (BitVec 8)) (flagsE lvlE rsnsE trlE tpE wvecE wstkE arenaE : List (BitVec 32))
    (teE wlenE : Nat) (unassE unflE wuE nbE oomE dst first_red irred redd : BitVec 64)
    (phE : List (BitVec 8)) (wsE : List (BitVec 32)) (arg : Tup Val [i64]) (mL : Mem 64) : Prop :=
  let (li, ()) := arg
  li.toNat ≤ 16 ∧
  ∃ llL : List (BitVec 32), llL.length = 16 ∧
    (∀ j < li.toNat, llL[j]? = some 0xFFFFFFFF#32) ∧
    (FullMem c
      { core :=
          { s.core with
            vals := valsE, flags := flagsE, lvl := lvlE, rsns := rsnsE, trl := trlE,
            trail_pos := tpE, trail_end := teE, unassigned := unassE, unflushed := unflE,
            wvec := wvecE, wstk := wstkE, arena := arenaE, arena_len := dst.toNat,
            wlen := wlenE, wusable := wuE, arena_garbage := 0#64, first_reducible := first_red,
            num_irred := irred, num_redundant := redd, num_binary := nbE, oom := oomE }
        scratch := { s.scratch with phases := phE, wsort := wsE, last_learned := llL } } ⋆ R) mL

private theorem sweep_write_hdr_wrap {c : FullCfg} {F_cur : List (List Nat)}
    {s s0 sL sC : FullState} {R : Mem 64 → Prop} {m : Mem 64} {dst : BitVec 64} {src st : Nat}
    {hdr0 : BitVec 32} (hcmpC : CompactPrefixOk c F_cur s sC.core dst.toNat)
    (hcongrC : CompactPrefixCongr sL.core sC.core dst.toNat)
    (hcv_eq : sC.core.cur_vars = s.core.cur_vars)
    (hnew3 : 3 ≤ st) (harC_len : sC.core.arena.length = c.arena_cap)
    (hfit : dst.toNat + 3 + st ≤ c.arena_cap)
    (hd1_eq : (dst + (1 : BitVec 64)).toNat = dst.toNat + 1)
    (hd2_eq : (dst + (2 : BitVec 64)).toNat = dst.toNat + 2)
    (hnsz32_eq : (BitVec.ofNat 32 st).toNat = st)
    (hsrc_ref : src ∈ fullArenaClauseRefs s0)
    (hng_src : fullArenaClauseGarbCore s0.core src = false)
    (hhdr_orig : hdr0 = fullArenaHdrCore s0.core src)
    (hs0_eq : s0.core.arena = s.core.arena ∧ s0.core.arena_len = s.core.arena_len)
    (hnew_lt : ∀ j < st, (sC.core.arena[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hnew_sub : List.Sublist (((sC.core.arena.drop (dst.toNat + 3)).take st).map BitVec.toNat)
      (fullArenaClauseLitsCore s0.core src))
    (hnew_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (((sC.core.arena.drop (dst.toNat + 3)).take st).map BitVec.toNat)))
    (hm_raw : (FullMem c
      { sC with core := { sC.core with arena := (((sC.core.arena.set dst.toNat
          (hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32))).set
          (dst + (1 : BitVec 64)).toNat 2#32).set (dst + (2 : BitVec 64)).toNat
          (BitVec.ofNat 32 st)) } } ⋆ R) m) :
    ∃ arH : List (BitVec 32), arH.length = c.arena_cap ∧
      (∀ j, dst.toNat + 3 ≤ j → arH[j]? = sC.core.arena[j]?) ∧
      (arH[dst.toNat + 2]?.getD 0#32).toNat = st ∧
      ((arH.drop (dst.toNat + 3)).take st).map BitVec.toNat =
        ((sC.core.arena.drop (dst.toNat + 3)).take st).map BitVec.toNat ∧
      CompactPrefixOk c F_cur s { sC.core with arena := arH } (dst.toNat + 3 + st) ∧
      (∀ rsns' : List (BitVec 32),
        fullArenaClauseLitsCore { sC.core with arena := arH, arena_len := dst.toNat + 3 + st }
          dst.toNat = fullArenaClauseLitsCore s0.core src →
        SweepHappendCore s0.core sL.core
          { sL.core with arena := arH, rsns := rsns', arena_len := dst.toNat + 3 + st }
          dst.toNat src) ∧
      (FullMem c { sC with core := { sC.core with arena := arH } } ⋆ R) m := by
  let arH := ((sC.core.arena.set dst.toNat
    (hdr0 &&& ~~~(0x00800000#32 ||| 0x00200000#32))).set
    (dst + (1 : BitVec 64)).toNat 2#32).set (dst + (2 : BitVec 64)).toNat (BitVec.ofNat 32 st)
  obtain ⟨haCmp_C, hnoC, hndC⟩ := hcmpC
  have harH_len : arH.length = c.arena_cap := by simp [arH, harC_len]
  have hpreH : PrefixAgrees dst.toNat sC.core.arena arH := fun idx hidx => by
    dsimp only [arH]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have hbodyH : ∀ j, dst.toNat + 3 ≤ j → arH[j]? = sC.core.arena[j]? := fun j hj => by
    dsimp only [arH]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have hcl_bits := bv32_clear_shrk_rsn hdr0 (by
    have hng0 : (fullArenaHdrCore s0.core src &&& 0x00080000#32) = 0#32 := by
      unfold fullArenaClauseGarbCore at hng_src; simpa [bne_iff_ne] using hng_src
    rwa [hhdr_orig])
  have hnoshrkH : (arH[dst.toNat]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
    dsimp only [arH]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by omega), Option.getD_some]; exact hcl_bits.1
  have hnogarbH : (arH[dst.toNat]?.getD 0#32 &&& 0x00080000#32) = 0#32 := by
    dsimp only [arH]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by omega), Option.getD_some]; exact hcl_bits.2
  have hszH : (arH[dst.toNat + 2]?.getD 0#32).toNat = st := by
    dsimp only [arH]; rw [← hd2_eq, List.getElem?_set_self (by simp; omega), Option.getD_some,
      hnsz32_eq]
  have hdropH : ((arH.drop (dst.toNat + 3)).take st).map BitVec.toNat =
      ((sC.core.arena.drop (dst.toNat + 3)).take st).map BitVec.toNat := by
    congr 1; refine List.ext_getElem (by simp [harH_len, harC_len]) fun j hj1 _ => ?_
    have hj : j < st := by simp [harH_len] at hj1; omega
    simp only [List.getElem_take, List.getElem_drop]
    have h1 := hbodyH (dst.toNat + 3 + j) (by omega)
    rw [List.getElem?_eq_getElem (by omega : dst.toNat + 3 + j < arH.length),
      List.getElem?_eq_getElem (by omega : dst.toNat + 3 + j < sC.core.arena.length)] at h1
    exact Option.some.inj h1
  obtain ⟨hrefsN, haN, holdN, hnoN⟩ := compactArena_append_block (k := sC.core)
    (k' := { sC.core with arena := arH }) (dst := dst.toNat) (new_sz := st) haCmp_C hnoC rfl hnew3
    harC_len harH_len hfit hpreH hnoshrkH hnogarbH hszH
    (fun j hj => by rw [hbodyH (dst.toNat + 3 + j) (by omega)]; rw [hcv_eq]; exact hnew_lt j hj)
    (by rw [hdropH]; exact hnew_ent)
  have hgarb_dst : fullArenaClauseGarbCore
      { sC.core with arena := arH, arena_len := dst.toNat + 3 + st } dst.toNat = false := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore; simp [hnogarbH]
  refine ⟨arH, harH_len, hbodyH, hszH, hdropH, ⟨haN, hnoN, fun hnd r hr => ?_⟩,
    fun rsns' hlits_eq => ?_, hm_raw⟩
  · rw [hrefsN, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · rw [(holdN r hr).2.2]; exact hndC hnd r hr
    · unfold fullArenaClauseLitsCore
      rw [show fullArenaClauseSizeCore
            { sC.core with arena := arH, arena_len := dst.toNat + 3 + st } dst.toNat = st from
          hszH,
        hdropH]
      have hsrc_s : src ∈ fullArenaClauseRefs s := by
        unfold fullArenaClauseRefs fullArenaClauseRefsCore at hsrc_ref ⊢
        rw [← hs0_eq.1, ← hs0_eq.2]; exact hsrc_ref
      have hng_s : fullArenaClauseGarb s src = false := by
        unfold fullArenaClauseGarb; unfold fullArenaClauseGarbCore fullArenaHdrCore at hng_src ⊢
        rw [← hs0_eq.1]; exact hng_src
      have hlits_s : fullArenaClauseLitsCore s0.core src = fullArenaClauseLits s src := by
        unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [hs0_eq.1]
      rw [hlits_s] at hnew_sub; exact (hnew_sub.map (· / 2)).nodup (hnd src hsrc_s hng_s)
  · refine ⟨?_, fun r hr => ?_, hgarb_dst, hlits_eq⟩
    · change fullArenaClauseRefsCore
        { sC.core with arena := arH, arena_len := dst.toNat + 3 + st } = _
      rw [hrefsN, hcongrC.1]
    · exact ⟨(holdN r (hcongrC.1.symm ▸ hr)).2.1.trans (hcongrC.2 r hr).1,
        (holdN r (hcongrC.1.symm ▸ hr)).2.2.trans (hcongrC.2 r hr).2⟩

private def ArenaSweepRsnInv (c : FullCfg) (s s0 sC : FullState) (R : Mem 64 → Prop)
    (arH : List (BitVec 32)) (nsrc dst st : Nat) (_ : Tup Val []) (mR : Mem 64) : Prop :=
  ∃ rsnsR : List (BitVec 32), rsnsR.length = c.max_vars ∧
    (s.core.cur_level = 0 → rsnsR = sC.core.rsns) ∧
    (0 < s.core.cur_level →
      SweepReasonMapInv s0.core { sC.core with arena := arH, rsns := rsnsR } nsrc (dst + 3 + st)) ∧
    (FullMem c { sC with core := { sC.core with arena := arH, rsns := rsnsR } } ⋆ R) mR

private def ArenaSweepRsnLoopInv (s sC : FullState) (arH : List (BitVec 32))
    (src dst st : Nat) (m0 : Mem 64) (arg : Tup Val [i32]) (mI : Mem 64) : Prop :=
  let (i, ()) := arg
  m0 = mI ∧ i.toNat ≤ st ∧
  (0 < s.core.cur_level → ∀ j < i.toNat,
    let lit := arH[dst + 3 + j]?.getD 0#32
    ¬ (lit.toNat / 2 < s.core.cur_vars ∧
       (0#32).slt ((sC.core.vals[lit.toNat]?.getD 0#8).signExtend 32) = true ∧
       sC.core.rsns[lit.toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src))

private def ArenaSweepRsnNextInv (s sC : FullState) (litI : BitVec 32) (src : Nat) (m0 : Mem 64)
    (_ : Tup Val []) (mN : Mem 64) : Prop :=
  m0 = mN ∧
  (0 < s.core.cur_level →
    ¬ (litI.toNat / 2 < s.core.cur_vars ∧
       (0#32).slt ((sC.core.vals[litI.toNat]?.getD 0#8).signExtend 32) = true ∧
       sC.core.rsns[litI.toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src))

private theorem sweep_rsn_hit_pos {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sL sC : FullState} {arH : List (BitVec 32)} {litI : BitVec 32}
    {src dst : BitVec 64} {nsrc st : Nat}
    (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hsrc_ref : src.toNat ∈ fullArenaClauseRefs s0)
    (hnsrc64 : nsrc = fullArenaNextOff s0.core.arena s0.core.arena_len src.toNat)
    (hdst_src : dst.toNat ≤ src.toNat) (hsrc_lt8 : src.toNat < 0x80000000)
    (hrmL : SweepReasonMapInv s0.core sL.core src.toNat dst.toNat)
    (hhapp : SweepHappendCore s0.core sL.core
      { sL.core with arena := arH, rsns := sC.core.rsns.set (litI.toNat / 2) (dst.setWidth 32),
                     arena_len := dst.toNat + 3 + st }
      dst.toNat src.toNat)
    (hvC : sC.core.vals = s0.core.vals) (hrC : sC.core.rsns = sL.core.rsns)
    (hrsns_len : sC.core.rsns.length = c.max_vars) (hcv_le : s0.core.cur_vars ≤ c.max_vars)
    (hlitI_lt : litI.toNat < 2 * s0.core.cur_vars) (hlitI_v : litI.toNat < sC.core.vals.length)
    (hval_gt0 : (0#32).slt ((sC.core.vals[litI.toNat]'hlitI_v).signExtend 32) = true)
    (hrsn_eq : (sC.core.rsns[litI.toNat / 2]?.getD 0xFFFFFFFF#32).toNat = src.toNat) :
    SweepReasonMapInv s0.core
      { sC.core with arena := arH, rsns := sC.core.rsns.set (litI.toNat / 2) (dst.setWidth 32) }
      nsrc (dst.toNat + 3 + st) := by
  have hv1 : s0.core.vals[litI.toNat]?.getD 0#8 = 1#8 := by
    have hdom := hw0.vals_domain litI.toNat hlitI_lt
    have hg : sC.core.vals[litI.toNat]?.getD 0#8 = sC.core.vals[litI.toNat]'hlitI_v := by
      rw [List.getElem?_eq_getElem hlitI_v, Option.getD_some]
    have h1 : (0#32).slt ((sC.core.vals[litI.toNat]?.getD 0#8).signExtend 32) = true := by
      rwa [hg]
    rw [hvC] at h1; exact (bv8_gt0_of_dom hdom).1.mp h1
  obtain ⟨idx0, hidx0, hieq0⟩ := (hw0.vals_true_iff litI.toNat hlitI_lt).mp hv1
  have hr_src_L : sL.core.rsns[(s0.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
      BitVec.ofNat 32 src.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [bv32_ofNat_toNat (by omega), hieq0, ← hrC]; exact hrsn_eq
  have hr0_src : s0.core.rsns[(s0.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
      BitVec.ofNat 32 src.toNat := by
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
      · rw [hr_src_L] at hm0'; have := hm0'.1
        rw [bv32_ofNat_toNat (by omega)] at this; omega
      · rw [hr_src_L] at hm0'; exact hm0'.symm
  have hdst_sw : dst.setWidth 32 = BitVec.ofNat 32 dst.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, bv32_ofNat_toNat (by omega), Nat.mod_eq_of_lt (by omega)]
  refine SweepReasonMapInv.congr_rsns_arena rfl rfl
    (SweepReasonMapInv.keep_step (kL := sL.core) hw0 hsrc_ref hnsrc64 hdst_src hsrc_lt8 hrmL
      hhapp ?_ ?_)
  · intro idx hidx hne_s
    have hv_ne : (s0.core.trl[idx]?.getD 0#32).toNat / 2 ≠ litI.toNat / 2 := fun hveq => by
      have := hw0.trail_vars_nodup idx idx0 hidx hidx0 (by rw [hieq0]; exact hveq)
      subst this; exact hne_s hr0_src
    rw [List.getElem?_set_ne (Ne.symm hv_ne), hrC]
  · intro idx hidx heq_s
    have hidx_eq := fullWitness_reason_unique hw0 hidx hidx0 hsrc_lt8 heq_s hr0_src
    subst hidx_eq
    rw [hieq0, List.getElem?_set_self (by rw [hrsns_len]; omega), Option.getD_some, hdst_sw]

private theorem sweep_rsn_miss_pos {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sL sC : FullState} {arH : List (BitVec 32)} {src dst nsrc st : Nat}
    (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hsrc_ref : src ∈ fullArenaClauseRefs s0)
    (hnsrc64 : nsrc = fullArenaNextOff s0.core.arena s0.core.arena_len src)
    (hdst_src : dst ≤ src) (hsrc_lt8 : src < 0x80000000)
    (hrmL : SweepReasonMapInv s0.core sL.core src dst)
    (hhapp : SweepHappendCore s0.core sL.core
      { sL.core with arena := arH, rsns := sC.core.rsns, arena_len := dst + 3 + st } dst src)
    (hvC : sC.core.vals = s0.core.vals) (hrC : sC.core.rsns = sL.core.rsns)
    (hszH : (arH[dst + 2]?.getD 0#32).toNat = st) (hfit : dst + 3 + st ≤ arH.length)
    (hlits_eq : fullArenaClauseLitsCore { sC.core with arena := arH, arena_len := dst + 3 + st }
      dst = fullArenaClauseLitsCore s0.core src)
    (hmiss : ∀ j < st,
      let lit := arH[dst + 3 + j]?.getD 0#32
      ¬ (lit.toNat / 2 < s0.core.cur_vars ∧
         (0#32).slt ((sC.core.vals[lit.toNat]?.getD 0#8).signExtend 32) = true ∧
         sC.core.rsns[lit.toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src)) :
    SweepReasonMapInv s0.core { sC.core with arena := arH, rsns := sC.core.rsns }
      nsrc (dst + 3 + st) := by
  refine SweepReasonMapInv.congr_rsns_arena rfl rfl
    (SweepReasonMapInv.keep_step (kL := sL.core) hw0 hsrc_ref hnsrc64 hdst_src hsrc_lt8 hrmL hhapp
      (fun _ _ _ => by rw [hrC]) (fun idx hidx heq_s => ?_))
  exfalso
  have hne_s : BitVec.ofNat 32 src ≠ 0xFFFFFFFF#32 := fun h => by
    have := congrArg BitVec.toNat h; rw [bv32_ofNat_toNat (by omega)] at this; simp at this; omega
  have hlg_s : (BitVec.ofNat 32 src &&& 0x80000000#32) = 0#32 :=
    (bv32_lt_highbit_iff _).mp (by rw [bv32_ofNat_toNat (by omega)]; exact hsrc_lt8)
  have hmem := hw0.reason_lit_mem idx hidx (heq_s ▸ hne_s) (heq_s ▸ hlg_s)
  rw [heq_s, bv32_ofNat_toNat (by omega), ← hlits_eq] at hmem
  have hbd : dst + 3 + fullArenaClauseSizeCore
      { sC.core with arena := arH, arena_len := dst + 3 + st } dst ≤ arH.length := by
    rw [show fullArenaClauseSizeCore { sC.core with arena := arH, arena_len := dst + 3 + st } dst =
      st from hszH]; omega
  obtain ⟨j, hj, hjeq⟩ := (mem_fullArenaClauseLitsCore_iff hbd).mp hmem
  rw [show fullArenaClauseSizeCore { sC.core with arena := arH, arena_len := dst + 3 + st } dst =
    st from hszH] at hj
  have hlt_tl := hw0.trail_lits_lt idx hidx
  have hval1 : s0.core.vals[(s0.core.trl[idx]?.getD 0#32).toNat]?.getD 0#8 = 1#8 :=
    (hw0.vals_true_iff _ hlt_tl).mpr ⟨idx, hidx, rfl⟩
  have hlit_j : (arH[dst + 3 + j]?.getD 0#32).toNat = (s0.core.trl[idx]?.getD 0#32).toNat := by
    rw [List.getElem?_eq_getElem (by omega : dst + 3 + j < arH.length), Option.getD_some]
    exact hjeq
  have hrsn_j : sC.core.rsns[(s0.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
      BitVec.ofNat 32 src := by
    have hrm_i := hrmL idx hidx; dsimp only at hrm_i; rw [heq_s] at hrm_i
    split at hrm_i
    · rename_i hbad; exact absurd hbad (fun hc => hc.elim hne_s (fun h => h hlg_s))
    · split at hrm_i
      · rename_i hlt; rw [bv32_ofNat_toNat (by omega)] at hlt; omega
      · rw [hrC, hrm_i]
  exact hmiss j hj
    ⟨by rw [hlit_j]; omega, by rw [hlit_j, hvC, hval1]; decide, by rw [hlit_j]; exact hrsn_j⟩

private theorem sweep_rsn_unmarked_pos {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sL sC : FullState} {arH : List (BitVec 32)} {src dst nsrc st : Nat}
    (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hrmk0 : FullReasonsMarked s0)
    (hsrc_ref : src ∈ fullArenaClauseRefs s0)
    (hnsrc64 : nsrc = fullArenaNextOff s0.core.arena s0.core.arena_len src)
    (hdst_src : dst ≤ src) (hsrc_lt8 : src < 0x80000000)
    (hrmL : SweepReasonMapInv s0.core sL.core src dst)
    (hhapp : SweepHappendCore s0.core sL.core
      { sL.core with arena := arH, rsns := sC.core.rsns, arena_len := dst + 3 + st } dst src)
    (hrC : sC.core.rsns = sL.core.rsns)
    (h0 : (fullArenaHdrCore s0.core src &&& 0x00200000#32) = 0#32) :
    SweepReasonMapInv s0.core { sC.core with arena := arH, rsns := sC.core.rsns }
      nsrc (dst + 3 + st) := by
  refine SweepReasonMapInv.congr_rsns_arena rfl rfl
    (SweepReasonMapInv.keep_step (kL := sL.core) hw0 hsrc_ref hnsrc64 hdst_src hsrc_lt8 hrmL hhapp
      (fun _ _ _ => by rw [hrC]) (fun idx hidx heq_s => ?_))
  exfalso
  have hne_s : BitVec.ofNat 32 src ≠ 0xFFFFFFFF#32 := fun h => by
    have := congrArg BitVec.toNat h; rw [bv32_ofNat_toNat (by omega)] at this; simp at this; omega
  have hlg_s : (BitVec.ofNat 32 src &&& 0x80000000#32) = 0#32 :=
    (bv32_lt_highbit_iff _).mp (by rw [bv32_ofNat_toNat (by omega)]; exact hsrc_lt8)
  have hlvl_pos : 0 < (s0.core.lvl[(s0.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat :=
    Classical.byContradiction fun h0' => by
      have := hw0.level0_rsn_none idx hidx (by omega); rw [heq_s] at this; exact hne_s this
  have hmk := hrmk0 idx hidx hlvl_pos (heq_s ▸ hlg_s)
  rw [heq_s, bv32_ofNat_toNat (by omega)] at hmk; exact hmk h0

private theorem sweep_bins_wrap {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {wvec0 wstk0 ws0 : List (BitVec 32)}
    {wlen0 : Nat} {nb0 : BitVec 64} {m0 : Mem 64}
    (hrmk : 0 < s.core.cur_level → FullReasonsMarked s)
    (hlen0 : ({ core := { s.core with wvec := wvec0, wstk := wstk0, wlen := wlen0,
                                        wusable := 0#64, num_binary := nb0 }
                scratch := { s.scratch with wsort := ws0 } } : FullState).LengthsOk c)
    (hbin0 : BinOnlyWatchesInv F_cur
      { s.core with wvec := wvec0, wstk := wstk0, wlen := wlen0, wusable := 0#64,
                    num_binary := nb0 })
    (hw0 : FullWitnessInv c F0 F_cur
      { s.core with wvec := wvec0, wstk := wstk0, wlen := wlen0, wusable := 0#64,
                    num_binary := nb0 })
    (hm0 : (FullMem c { core := { s.core with wvec := wvec0, wstk := wstk0, wlen := wlen0,
                                              wusable := 0#64, num_binary := nb0 }
                        scratch := { s.scratch with wsort := ws0 } } ⋆ R) m0) :
    ∃ s0 : FullState, SweepLike s s0 ∧ s0.LengthsOk c ∧ BinOnlyWatchesInv F_cur s0.core ∧
      FullWitnessInv c F0 F_cur s0.core ∧
      (s0.core.arena = s.core.arena ∧ s0.core.arena_len = s.core.arena_len ∧
       s0.core.cur_vars = s.core.cur_vars ∧ s0.core.cur_level = s.core.cur_level ∧
       s0.core.vals = s.core.vals ∧ s0.core.lvl = s.core.lvl ∧ s0.core.trl = s.core.trl ∧
       s0.core.trail_pos = s.core.trail_pos ∧ s0.core.trail_end = s.core.trail_end) ∧
      (0 < s0.core.cur_level → FullReasonsMarked s0) ∧ (FullMem c s0 ⋆ R) m0 :=
  ⟨_, ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩,
    hlen0, hbin0, hw0, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hrmk, hm0⟩

private theorem sweep_copy_wrap {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} {R : Mem 64 → Prop} {src dst st : BitVec 64} {old_sz : BitVec 32}
    {at_root : Bool} {arC flagsC lvlC rsnsC trlC tpC wvecC wstkC wsC : List (BitVec 32)}
    {valsC phC : List (BitVec 8)} {teC wlenC : Nat} {unassC unflC wuC nbC oomC : BitVec 64}
    {mC : Mem 64} (hlikeL : SweepLike s sL)
    (hlenC : ({ core := { sL.core with arena := arC, vals := valsC, flags := flagsC,
                                       lvl := lvlC, rsns := rsnsC, trl := trlC,
                                       trail_pos := tpC, trail_end := teC,
                                       unassigned := unassC, unflushed := unflC,
                                       wvec := wvecC, wstk := wstkC, wlen := wlenC,
                                       wusable := wuC, num_binary := nbC, oom := oomC }
                scratch := { sL.scratch with phases := phC, wsort := wsC } } :
              FullState).LengthsOk c)
    (houtC : OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + old_sz.toNat)
      sL.core.arena arC)
    (hout_ok : fullSweepCopyOutcome c F0 F_cur sL
      { core := { sL.core with arena := arC, vals := valsC, flags := flagsC,
                               lvl := lvlC, rsns := rsnsC, trl := trlC,
                               trail_pos := tpC, trail_end := teC,
                               unassigned := unassC, unflushed := unflC,
                               wvec := wvecC, wstk := wstkC, wlen := wlenC,
                               wusable := wuC, num_binary := nbC, oom := oomC }
        scratch := { sL.scratch with phases := phC, wsort := wsC } }
      src dst old_sz at_root st)
    (hmC : (FullMem c
      { core := { sL.core with arena := arC, vals := valsC, flags := flagsC, lvl := lvlC,
                               rsns := rsnsC, trl := trlC, trail_pos := tpC, trail_end := teC,
                               unassigned := unassC, unflushed := unflC, wvec := wvecC,
                               wstk := wstkC, wlen := wlenC, wusable := wuC,
                               num_binary := nbC, oom := oomC }
        scratch := { sL.scratch with phases := phC, wsort := wsC } } ⋆ R) mC) :
    ∃ sC : FullState, SweepLike s sC ∧ sC.LengthsOk c ∧
      (sC.core.arena = arC ∧ sC.core.vals = valsC ∧ sC.core.rsns = rsnsC ∧
       sC.core.trail_end = teC ∧ sC.core.oom = oomC) ∧
      OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + old_sz.toNat)
        sL.core.arena sC.core.arena ∧
      fullSweepCopyOutcome c F0 F_cur sL sC src dst old_sz at_root st ∧
      (FullMem c sC ⋆ R) mC :=
  ⟨_, hlikeL.of_copy, hlenC, ⟨rfl, rfl, rfl, rfl, rfl⟩, houtC, hout_ok, hmC⟩

local macro "fr_tiny_simp" : tactic =>
  `(tactic| simp only [
      LeanQbe.T.op1_eq_mk, LeanQbe.T.op2_eq_mk,
      LeanQbe.T.wp_let_add_eq, LeanQbe.T.wp_let_mul_eq, LeanQbe.T.wp_let_and_eq,
      LeanQbe.T.wp_let_cmp_eq, LeanQbe.T.wp_let_zext_eq, LeanQbe.T.wp_let_sext_eq,
      LeanQbe.T.wp_let_trunc_eq,
      LeanQbe.T.OpCode.eq, LeanQbe.T.OpCode.ne, LeanQbe.T.OpCode.ult, LeanQbe.T.OpCode.sgt,
      LeanQbe.T.vals_nil, LeanQbe.T.vals_cons, LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm,
      LeanQbe.T.Ty.hasFloat_vec, LeanQbe.T.Ty.hasFloat, LeanQbe.T.Ty.isFloatTree,
      LeanQbe.T.evalBits_eq_beq, LeanQbe.T.evalBits_ne_bne,
      LeanQbe.T.evalBits_ult_eq, LeanQbe.T.evalBits_sgt_eq,
      LeanQbe.T.lift1, LeanQbe.T.lift2, LeanQbe.T.liftCmp,
      cast_eq, Bool.false_eq_true, ite_false, ite_true,
      BitVec.reduceSignExtend, BitVec.reduceSetWidth, BitVec.reduceAdd, BitVec.reduceMul])

local macro "fr_tiny_lets" : tactic =>
  `(tactic| try repeat (first | (fr_strip; try fr_tiny_simp) | fr_tiny_simp))

theorem full_arena_sweep_wp (Γ : Env)
    (hsweep_bins : ∀ a m Q X, fullSweepBinsSpec a m Q X →
      Γ "full_sweep_bins" [i64] [] a m Q X)
    (hnext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hcopy : ∀ a m Q X, fullSweepCopySpec a m Q X →
      Γ "full_sweep_copy" [i64, i64, i64, i32, .bool] [i64] a m Q X)
    (hrewatch : ∀ a m Q X, fullRewatchArenaSpec a m Q X →
      Γ "full_rewatch_arena" [i64, i64] [.bool] a m Q X) :
    ∀ a m Q X, fullArenaSweepSpec a m Q X → Func.wp Γ full_arena_sweep_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd0, hdm0, hrmk, hm, hQ⟩
  change fullArenaSweepPost c F0 F_cur s R Q at hQ
  have hcap_lt : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  -- Step 1: `full_sweep_bins(h)`
  fr_steps; c0_call hsweep_bins
  refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm,
    fun wvec0 wstk0 wlen0 nb0 ws0 m0 hlen0R hbin0R hfbin0R hdn0R hw0R hm0R => ?_⟩
  obtain ⟨s0, hlike0, hlen0, hbin0, hw0, h0_same, hrmk0, hm0⟩ :=
    sweep_bins_wrap hrmk hlen0R hbin0R hw0R hm0R
  clear hsweep_bins hrmk hw hlen hm hlen0R hbin0R hfbin0R hdn0R hw0R hm0R
    wvec0 wstk0 wlen0 nb0 ws0
  obtain ⟨h0_ar, h0_al, h0_cv, h0_cl, h0_va, h0_lv, h0_tr, h0_tp, h0_te⟩ := h0_same
  have hal_le : s.core.arena_len ≤ c.arena_cap := h0_al ▸ hlen0.core_ok.arena_len_le
  have hcv_le : s.core.cur_vars ≤ c.max_vars := h0_cv ▸ hlen0.core_ok.cur_vars_le
  have hdec_cl0 : ∀ (b : Bool), (BitVec.ofNat 64 s.core.cur_level == 0) = b ↔
      (if b then s.core.cur_level = 0 else 0 < s.core.cur_level) := by
    have hcl_lt : s.core.cur_level < 2 ^ 64 := by
      have h1 : s0.core.cur_level ≤ s0.core.trail_end := hw0.cur_level_le
      have h2 : s0.core.trail_end ≤ s0.core.cur_vars := hlen0.core_ok.trail_end_le
      omega
    intro b; cases b
    · simp only [beq_eq_false_iff_ne, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro hne
        rcases Nat.eq_zero_or_pos s.core.cur_level with h0 | hpos
        · exact absurd (by simp [h0]) hne
        · exact hpos
      · intro hpos h0; have := congrArg BitVec.toNat h0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_lt] at this; simp at this; omega
    · simp only [beq_iff_eq, ↓reduceIte]
      constructor
      · intro h0; have := congrArg BitVec.toNat h0
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_lt] at this
      · intro h0; simp [h0]
  have hcl_beq : (BitVec.ofNat 64 s.core.cur_level == 0) = decide (s.core.cur_level = 0) := by
    by_cases hcl0 : s.core.cur_level = 0
    · rw [(hdec_cl0 true).mpr hcl0]; simp [hcl0]
    · rw [(hdec_cl0 false).mpr (Nat.pos_of_ne_zero hcl0)]; simp [hcl0]
  -- Step 2: main compaction loop `(src, dst, first_red, irred, redd, new_unit)`
  -- Join point after loop exit (handles both normal exit `src = alen` and early `break`).
  fr_to_group
  refine wp_join_group (ArenaSweepExitInv c F0 F_cur s R) ?_ ?_
  · -- Continuation after loop exit: write header scalars, zero `last_learned[0..15]`, check returns
    rintro _ ⟨_srcE, dst, first_red, irred, redd, unsat, new_unit, ⟨⟩⟩ mE
      ⟨hdst_le, sE, hlikeE, hlenE, hwEnd, hnoEnd, hndEnd, hunsatE, hunitE, hposE, hmE⟩
    rcases hlikeE with ⟨valsE, flagsE, lvlE, rsnsE, trlE, tpE, teE, unassE, unflE, wvecE, wstkE,
      arenaE, wlenE, wuE, nbE, oomE, phE, wsE, rfl⟩
    clear hnext hcopy hrmk0 hbin0 hlen0 h0_ar h0_al h0_cv h0_cl
      h0_va h0_lv h0_tr h0_tp h0_te hcl_beq
    have hll_len : s.scratch.last_learned.length = 16 := hlenE.scratch_ok.last_learned_len
    fr_steps
    -- Zero `last_learned[0..15] = 0xFFFFFFFFu`
    refine wp_loop_inv (LastLearnedLoopInv c s R valsE flagsE lvlE rsnsE trlE tpE wvecE wstkE
        arenaE teE wlenE unassE unflE wuE nbE oomE dst first_red irred redd phE wsE)
      (fun (li, ()) _ => 16 - li.toNat) (fun Jli hLoopLi => ?_) ?_
    · fr_steps
      exact hLoopLi (0#64, ()) m ⟨Nat.zero_le _, s.scratch.last_learned, hll_len,
        fun _ hj => absurd hj (Nat.not_lt_zero _), fullMem_cast hm rfl⟩
    · rintro Jli ⟨li, ⟨⟩⟩ mL ⟨hli_le, llL, hllL, hallL, hmL⟩ hLoopLi
      fr_split
      · have hli_lt : li.toNat < 16 := by c0_bound
        have hli1_eq : (li + (1 : BitVec 64)).toNat = li.toNat + 1 := bv64_add1 (by omega)
        fr_steps
        refine hLoopLi (li + (1 : BitVec 64), ()) m (by dsimp only; rw [hli1_eq]; omega)
          ⟨by rw [hli1_eq]; omega, llL.set li.toNat 0xFFFFFFFF#32, List.length_set.trans hllL,
           fun j hj => ?_, fullMem_cast hm rfl⟩
        rw [hli1_eq] at hj
        by_cases hje : j = li.toNat
        · subst j; exact List.getElem?_set_self (by omega)
        · rw [List.getElem?_set_ne (Ne.symm hje)]; exact hallL j (by omega)
      · have hli_16 : li.toNat = 16 := by c0_bound
        let scLL : FullScratch :=
          { s.scratch with phases := phE, wsort := wsE, last_learned := llL }
        let sLL : FullState :=
          { core :=
              { s.core with
                vals := valsE, flags := flagsE, lvl := lvlE, rsns := rsnsE, trl := trlE,
                trail_pos := tpE, trail_end := teE, unassigned := unassE, unflushed := unflE,
                wvec := wvecE, wstk := wstkE, arena := arenaE, arena_len := dst.toNat,
                wlen := wlenE, wusable := wuE, arena_garbage := 0#64,
                first_reducible := first_red, num_irred := irred, num_redundant := redd,
                num_binary := nbE, oom := oomE }
            scratch := scLL }
        have hlenLL : sLL.LengthsOk c :=
          ⟨{ hlenE.core_ok with arena_len_le := by change dst.toNat ≤ c.arena_cap; omega },
           { hlenE.scratch_ok with last_learned_len := hllL }⟩
        have hll_wf : FullLastLearnedWf sLL :=
          fullLastLearnedWf_of_all_sentinel (fun j hj => hallL j (by omega))
        have hwLL : FullWitnessInv c F0 F_cur sLL.core :=
          { hwEnd with arena := { hwEnd.arena with len_ok := hwEnd.arena.len_ok }
                       watches := hwEnd.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
        have hndLL : FullArenaVarsNodup sLL := fun r hr _ => hndEnd hnd0 r hr
        fr_split
        · -- `unsat = true`: return `2#64`
          have hu_t : unsat = true := by simpa using hc
          fr_steps
          exact hQ 2#64 valsE flagsE lvlE rsnsE trlE tpE teE unassE unflE wvecE wstkE arenaE
            dst.toNat wlenE wuE first_red irred redd nbE oomE scLL mL hlenLL hwLL hndLL
            hll_wf rfl rfl (Or.inr (Or.inr (Or.inl rfl)))
            (fun h => by rcases h with h | h <;> cases h)
            (fun hpos => absurd (hposE hpos).1 (by simp [hu_t]))
            (fun h => by cases h) (fun _ => hunsatE hu_t) (fun h => by cases h) hmL
        · fr_split
          · -- `h->oom != 0`: return `3#64`
            have hoom_ne : oomE ≠ 0#64 := fun h0 => by
              have hne : oomE.toNat ≠ 0 := by c0_bound
              exact hne (by simp [h0])
            fr_steps
            exact hQ 3#64 valsE flagsE lvlE rsnsE trlE tpE teE unassE unflE wvecE wstkE arenaE
              dst.toNat wlenE wuE first_red irred redd nbE oomE scLL mL hlenLL hwLL hndLL
              hll_wf rfl rfl (Or.inr (Or.inr (Or.inr rfl)))
              (fun h => by rcases h with h | h <;> cases h)
              (fun hpos => by
                obtain ⟨_, _, hv, hl, ht, htp, hte⟩ := hposE hpos
                exact ⟨by decide, by decide, hv, hl, ht, htp, hte⟩)
              (fun h => by cases h) (fun h => by cases h) (fun _ => hoom_ne) hmL
          · -- `h->oom == 0`: call `full_rewatch_arena(h, dst)`
            have hoom0 : oomE = 0#64 :=
              BitVec.eq_of_toNat_eq (by change oomE.toNat = 0; c0_bound)
            fr_steps; c0_call hrewatch
            refine ⟨c, F0, F_cur, sLL, R, rfl, hlenLL, rfl, hwLL, hdm0, hnoEnd, hmL,
              fun ok arR wvecR wstkR wlenR wuR oomR wsR mR hlenR hwR _ hndR hokt hokf hmR => ?_⟩
            let scR : FullScratch :=
              { s.scratch with phases := phE, wsort := wsR, last_learned := llL }
            have hll_wfR : FullLastLearnedWf
                { core := { sLL.core with arena := arR, wvec := wvecR, wstk := wstkR,
                                          wlen := wlenR, wusable := wuR, oom := oomR }
                  scratch := scR } :=
              fullLastLearnedWf_of_all_sentinel (fun j hj => hallL j (by omega))
            fr_split
            · -- `ok = true`: return `new_unit ? 1#64 : 0#64`
              have hok_t : ok = true := by simpa using hc
              have hoomR0 : oomR = 0#64 := (hokt hok_t).trans hoom0
              fr_to_group
              refine wp_join_group (fun (r, ()) m' =>
                mR = m' ∧ ((r = 1#64 ∧ new_unit = true) ∨ (r = 0#64 ∧ new_unit = false))) ?_ ?_
              · rintro _ ⟨r, ⟨⟩⟩ _ ⟨rfl, hr⟩
                fr_steps
                rcases hr with ⟨rfl, hnu_t⟩ | ⟨rfl, hnu_f⟩
                · exact hQ 1#64 valsE flagsE lvlE rsnsE trlE tpE teE unassE unflE wvecR wstkR arR
                    dst.toNat wlenR wuR first_red irred redd nbE oomR scR mR hlenR hwR
                    (hndR hndLL) hll_wfR rfl rfl (Or.inr (Or.inl rfl)) (fun _ => hoomR0)
                    (fun hpos => absurd (hposE hpos).2.1 (by simp [hnu_t]))
                    (fun _ => hunitE hnu_t) (fun h => by cases h) (fun h => by cases h)
                    (fullMem_cast hmR rfl)
                · exact hQ 0#64 valsE flagsE lvlE rsnsE trlE tpE teE unassE unflE wvecR wstkR arR
                    dst.toNat wlenR wuR first_red irred redd nbE oomR scR mR hlenR hwR
                    (hndR hndLL) hll_wfR rfl rfl (Or.inl rfl) (fun _ => hoomR0)
                    (fun hpos => by
                      obtain ⟨_, _, hv, hl, ht, htp, hte⟩ := hposE hpos
                      exact ⟨by decide, by decide, hv, hl, ht, htp, hte⟩)
                    (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
                    (fullMem_cast hmR rfl)
              · intro Jret hJret
                fr_split
                · fr_steps; exact hJret (1#64, ()) mR ⟨rfl, Or.inl ⟨rfl, by simpa using hc⟩⟩
                · fr_steps; exact hJret (0#64, ()) mR ⟨rfl, Or.inr ⟨rfl, by simpa using hc⟩⟩
            · -- `!ok`: return `3#64`
              have hoomR1 : oomR = 1#64 := hokf (by cases ok <;> simp at hc ⊢)
              fr_steps
              exact hQ 3#64 valsE flagsE lvlE rsnsE trlE tpE teE unassE unflE wvecR wstkR arR
                dst.toNat wlenR wuR first_red irred redd nbE oomR scR mR hlenR hwR
                (hndR hndLL) hll_wfR rfl rfl (Or.inr (Or.inr (Or.inr rfl)))
                (fun h => by rcases h with h | h <;> cases h)
                (fun hpos => by
                  obtain ⟨_, _, hv, hl, ht, htp, hte⟩ := hposE hpos
                  exact ⟨by decide, by decide, hv, hl, ht, htp, hte⟩)
                (fun h => by cases h) (fun h => by cases h) (fun _ => by simp [hoomR1])
                (fullMem_cast hmR rfl)
  · -- Entry to main compaction loop (`while (src < alen)`)
    intro JE hJE
    clear hrewatch hQ
    refine wp_loop_inv (ArenaSweepLoopInv c F0 F_cur s s0 R)
      (fun (src, _, _, _, _, _, ()) _ => s.core.arena_len - src.toNat) (fun JL hLoopL => ?_) ?_
    · fr_steps
      refine hLoopL (0#64, 0#64, 0xFFFFFFFF#64, 0#64, 0#64, false, ()) m0
        ⟨Nat.le_refl _, Nat.zero_le _,
         fun hpos => fullArenaClauseRefs_zero_mem hw0.arena (h0_al ▸ hpos),
         s0, hlike0, hlen0, ⟨fullArenaClausesInv_zero,
           fun r hr => by simp [fullArenaClauseRefsCore, fullArenaScanRefs] at hr,
           fun _ r hr => by simp [fullArenaClauseRefsCore, fullArenaScanRefs] at hr⟩,
         hbin0,
         fun i _ _ => congrArg (·[i]?) h0_ar,
         fun hcl0 => ⟨fullWitnessInv_arena_len_zero hw0 hbin0 (h0_cl.trans hcl0),
           h0_te ▸ Nat.le_refl _, fun h => Bool.noConfusion h⟩,
         fun _ => ⟨rfl, h0_va, h0_lv, h0_tr, h0_tp, h0_te, SweepReasonMapInv.init⟩, hm0⟩
    · rintro JL ⟨src, dst, first_red, irred, redd, new_unit, ⟨⟩⟩ mL
        ⟨hdst_src, hsrc_le, hsrc_mem, sL, hlikeL, hlenL, hcmpL, hbinL,
         htailL, hrootL, hposL, hmL⟩ hLoopL
      obtain ⟨hcvL, halL, hclL, hdmL, hftL, hfdL, hincL⟩ := hlikeL.unchanged
      have harL_len : sL.core.arena.length = c.arena_cap := hlenL.core_ok.arena_len_arr
      fr_split
      · -- `src < alen`
        have hsrc_lt : src.toNat < s.core.arena_len := by c0_bound
        have hsrc_ref : src.toNat ∈ fullArenaClauseRefs s0 := hsrc_mem hsrc_lt
        have hwf0 := hw0.arena.refs_wf src.toNat hsrc_ref
        have hsrc3_le : src.toNat + 3 ≤ s.core.arena_len := by rw [← h0_al]; exact hwf0.1
        have hsrc_lt8 : src.toNat < 0x80000000 := by omega
        -- `src + 3 > alen` is auto-discharged false by `fr_split`; read `hdr`, `old_sz`
        fr_split
        · have hs2_eq : (src + (2 : BitVec 64)).toNat = src.toNat + 2 := by
            rw [BitVec.toNat_add, show (2 : BitVec 64).toNat = 2 from rfl,
              Nat.mod_eq_of_lt (by omega)]
          have hs0_lt : src.toNat < sL.core.arena.length := by omega
          have hs2_lt : (src + (2 : BitVec 64)).toNat < sL.core.arena.length := by omega
          have hhdr_orig :
              sL.core.arena[src.toNat]'hs0_lt = fullArenaHdrCore s0.core src.toNat := by
            have h1 := (htailL src.toNat (Nat.le_refl _) hsrc_lt).trans
              (congrArg (·[src.toNat]?) h0_ar.symm)
            unfold fullArenaHdrCore
            rw [← h1, List.getElem?_eq_getElem hs0_lt, Option.getD_some]
          have hsz_orig : (sL.core.arena[(src + (2 : BitVec 64)).toNat]'hs2_lt).toNat =
              fullArenaClauseSizeCore s0.core src.toNat := by
            have h1 := (htailL (src.toNat + 2) (by omega) (by omega)).trans
              (congrArg (·[src.toNat + 2]?) h0_ar.symm)
            unfold fullArenaClauseSizeCore
            rw [← h1, List.getElem?_eq_getElem (by omega : src.toNat + 2 < sL.core.arena.length),
              Option.getD_some]
            simp only [hs2_eq]
          have hsrc32 : (src.setWidth 32).toNat = src.toNat := by
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
          have hnxt_eq : fullArenaNextOff sL.core.arena s.core.arena_len src.toNat =
              fullArenaNextOff s0.core.arena s0.core.arena_len src.toNat := by
            rw [h0_al]
            refine fullArenaNextOff_congr_block
              ((htailL src.toNat (Nat.le_refl _) hsrc_lt).trans
                (congrArg (·[src.toNat]?) h0_ar.symm))
              ((htailL (src.toNat + 2) (by omega) (by omega)).trans
                (congrArg (·[src.toNat + 2]?) h0_ar.symm))
              (fun k hk1 hk2 =>
                (htailL k (by omega)
                  (by have h : fullArenaNextOff s0.core.arena s0.core.arena_len src.toNat ≤
                        s0.core.arena_len := hwf0.2.2.2.1
                      rw [h0_al] at h; omega)).trans (congrArg (·[k]?) h0_ar.symm))
          have hnxt_bd := fullArenaNextOff_bounds hwf0.1 (ar := s0.core.arena)
          have hnxt_le_al : fullArenaNextOff s0.core.arena s0.core.arena_len src.toNat ≤
              s.core.arena_len := by rw [← h0_al]; exact hwf0.2.2.2.1
          have hnxt_mem : fullArenaNextOff s0.core.arena s0.core.arena_len src.toNat =
              s.core.arena_len ∨
              fullArenaNextOff s0.core.arena s0.core.arena_len src.toNat ∈
                fullArenaClauseRefs s0 := by
            rw [← h0_al]; exact fullArenaClauseRefs_next_or_end hw0.arena hsrc_ref
          fr_steps; c0_call hnext
          refine ⟨c, sL, R, rfl, hlenL, hmL, ?_⟩
          let nsrc32 := BitVec.ofNat 32 (fullArenaNextOff sL.core.arena sL.core.arena_len
            (src.setWidth 32).toNat)
          have hnsrc64 : (nsrc32.setWidth 64).toNat =
              fullArenaNextOff s0.core.arena s0.core.arena_len src.toNat := by
            rw [zext_toNat nsrc32 (by decide)]
            dsimp only [nsrc32]; rw [halL, hsrc32, hnxt_eq]
            exact bv32_ofNat_toNat (by omega)
          have hnsrc_gt : src.toNat < (nsrc32.setWidth 64).toNat := by
            have h1 : src.toNat < fullArenaNextOff s0.core.arena s0.core.arena_len src.toNat :=
              hnxt_bd.1
            rw [hnsrc64]; omega
          have hdec_m :
              s.core.arena_len - (nsrc32.setWidth 64).toNat < s.core.arena_len - src.toNat := by
            omega
          have hskip_go : (fullArenaClauseGarbCore s0.core src.toNat = true ∨
              fullArenaClauseSizeCore s0.core src.toNat < 3 ∨
              s0.core.arena_len < src.toNat + 3 + fullArenaClauseSizeCore s0.core src.toNat) →
              JL (nsrc32.setWidth 64, dst, first_red, irred, redd, new_unit, ()) mL := by
            intro hsk
            refine hLoopL (nsrc32.setWidth 64, dst, first_red, irred, redd, new_unit, ()) mL
              hdec_m
              ⟨by omega, by rw [hnsrc64]; exact hnxt_le_al, fun hlt => ?_,
               sL, hlikeL, hlenL, hcmpL, hbinL,
               fun i hi1 hi2 => htailL i (by omega) hi2, hrootL, fun hpos => ?_, hmL⟩
            · rw [hnsrc64] at hlt ⊢; exact hnxt_mem.resolve_left (by omega)
            · obtain ⟨hnu, hv, hl, ht, htp, hte, hrmL⟩ := hposL hpos
              exact ⟨hnu, hv, hl, ht, htp, hte,
                hrmL.skip hw0 hsrc_ref hnsrc64 hsk⟩
          -- Check skip conditions: `PH_GARB != 0`, `old_sz < 3`, `src + 3 + old_sz > alen`
          fr_split
          · -- `(hdr & PH_GARB) != 0`: skip
            fr_steps; exact hskip_go (Or.inl (by
              unfold fullArenaClauseGarbCore; rw [← hhdr_orig]; simpa [bne_iff_ne] using hc))
          · have hng_src : fullArenaClauseGarbCore s0.core src.toNat = false := by
              unfold fullArenaClauseGarbCore; rw [← hhdr_orig]; simpa [bne_iff_ne] using hc
            have hsz3_pre : 3 ≤ (sL.core.arena[(src + (2 : BitVec 64)).toNat]'hs2_lt).toNat := by
              rw [hsz_orig]; exact hwf0.2.1
            have hfit_pre : src.toNat + 3 +
                (sL.core.arena[(src + (2 : BitVec 64)).toNat]'hs2_lt).toNat ≤
                s0.core.arena_len := by
              rw [hsz_orig]
              have h1 : src.toNat + 3 + fullArenaClauseSizeCore s0.core src.toNat ≤
                  fullArenaNextOff s0.core.arena s0.core.arena_len src.toNat := hwf0.2.2.1
              have h2 : fullArenaNextOff s0.core.arena s0.core.arena_len src.toNat ≤
                  s0.core.arena_len := hwf0.2.2.2.1
              omega
            -- `old_sz < 3` and `src + 3 + old_sz > alen` are auto-closed false
            clear hskip_go
            have har_s_len : s.core.arena.length = c.arena_cap :=
              h0_ar ▸ hlen0.core_ok.arena_len_arr
            have hsz3 : 3 ≤ (sL.core.arena[(src + (2 : BitVec 64)).toNat]'hs2_lt).toNat := hsz3_pre
            have hsrc_fit : src.toNat + 3 +
                (sL.core.arena[(src + (2 : BitVec 64)).toNat]'hs2_lt).toNat ≤
                s.core.arena_len := h0_al ▸ hfit_pre
            have hsrc_lits_eq :
                ((sL.core.arena.drop (src.toNat + 3)).take
                  (sL.core.arena[(src + (2 : BitVec 64)).toNat]'hs2_lt).toNat).map
                  BitVec.toNat = fullArenaClauseLitsCore s0.core src.toNat := by
              have har0_len : s0.core.arena.length = c.arena_cap := hlen0.core_ok.arena_len_arr
              rw [hsz_orig]; unfold fullArenaClauseLitsCore; congr 1
              apply List.ext_getElem (by simp [harL_len, har0_len])
              intro j hj1 _
              have hj : j < fullArenaClauseSizeCore s0.core src.toNat := by simp at hj1; omega
              simp only [List.getElem_take, List.getElem_drop]
              have h1 := (htailL (src.toNat + 3 + j) (by omega) (by omega)).trans
                (congrArg (·[src.toNat + 3 + j]?) h0_ar.symm)
              rw [List.getElem?_eq_getElem (by omega : src.toNat + 3 + j < sL.core.arena.length),
                List.getElem?_eq_getElem (by omega : src.toNat + 3 + j < s0.core.arena.length)]
                at h1
              exact Option.some.inj h1
            have hlits_lt_src : ∀ j < (sL.core.arena[(src + (2 : BitVec 64)).toNat]'hs2_lt).toNat,
                (sL.core.arena[src.toNat + 3 + j]?.getD 0#32).toNat < 2 * sL.core.cur_vars := by
              intro j hj
              rw [hcvL, htailL (src.toNat + 3 + j) (by omega) (by omega), ← h0_ar]
              have hbd : src.toNat + 3 + fullArenaClauseSizeCore s0.core src.toNat ≤
                  s0.core.arena.length := by
                have := hlen0.core_ok.arena_len_arr; omega
              have hj' : j < fullArenaClauseSizeCore s0.core src.toNat := by omega
              have hmem : (s0.core.arena[src.toNat + 3 + j]'(by omega)).toNat ∈
                  fullArenaClauseLitsCore s0.core src.toNat :=
                (mem_fullArenaClauseLitsCore_iff hbd).mpr ⟨j, hj', rfl⟩
              have hlt_j := hw0.arena.lits_lt src.toNat hsrc_ref hng_src _ hmem
              rw [h0_cv] at hlt_j
              rwa [List.getElem?_eq_getElem (by omega : src.toNat + 3 + j < s0.core.arena.length),
                Option.getD_some]
            -- Call `full_sweep_copy(h, src, dst, old_sz, at_root)`
            fr_steps; c0_call hcopy
            refine ⟨c, F0, F_cur, sL, R, rfl, hlenL, hdst_src, hsz3, by omega, ?_, hlits_lt_src,
              fun hrt => ?_, hmL,
              fun st arC valsC flagsC lvlC rsnsC trlC tpC teC unassC unflC wvecC wstkC wlenC wuC
                nbC oomC phC wsC mC hlenC0 houtC0 hout_ok0 hmC0 => ?_⟩
            · rw [hclL, h0_cl, hcl_beq]
            · have hcl0 : s.core.cur_level = 0 := (hdec_cl0 true).mp (h0_cl ▸ hrt)
              exact ⟨(hrootL hcl0).1, hbinL,
                by rw [hsrc_lits_eq]; exact hw0.arena.entails src.toNat hsrc_ref hng_src⟩
            -- Wrap `full_sweep_copy` output into opaque `sC : FullState`
            rw [h0_cl] at hout_ok0
            obtain ⟨sC, hlikeC, hlenC, -, houtC, hresC, hmC⟩ :=
              sweep_copy_wrap hlikeL hlenC0 houtC0 hout_ok0 hmC0
            clear hlenC0 houtC0 hout_ok0 hmC0
              arC valsC flagsC lvlC rsnsC trlC tpC teC unassC unflC
              wvecC wstkC wlenC wuC nbC oomC phC wsC
            have harC_len : sC.core.arena.length = c.arena_cap := hlenC.core_ok.arena_len_arr
            have hpreC : PrefixAgrees dst.toNat sL.core.arena sC.core.arena := fun idx hidx =>
              houtC.getElem?_lt (by omega)
            have htailC : ∀ i, (nsrc32.setWidth 64).toNat ≤ i → i < s.core.arena_len →
                sC.core.arena[i]? = s.core.arena[i]? := fun i hi1 hi2 => by
              have hfit_n : src.toNat + 3 +
                  (sL.core.arena[(src + (2 : BitVec 64)).toNat]'hs2_lt).toNat ≤
                  (nsrc32.setWidth 64).toNat := by
                rw [hnsrc64, hsz_orig]; exact hwf0.2.2.1
              rw [houtC.getElem?_ge (by omega)]
              exact htailL i (by omega) hi2
            obtain ⟨hcmpC, hcongrC⟩ := arenaPrefix_preserves_compact
              (s := s) (k := sL.core) (k' := sC.core) hcmpL
              (by rw [hlikeC.unchanged.1, hcvL]) harL_len harC_len (by omega) hpreC
            clear hpreC houtC
            have hcl0_of_special :
                st = 0xFFFFFFFE#64 ∨ st = 0xFFFFFFFD#64 ∨ st = 1#64 ∨ st = 0xFFFFFFFF#64 →
                s.core.cur_level = 0 := by
              intro hsp
              exact Classical.byContradiction fun hne => by
                have hst_old := (hresC.1 ((hdec_cl0 false).mpr (Nat.pos_of_ne_zero hne))).1
                have hst_lt : st.toNat < 2 * 2 ^ 28 := by
                  rw [hst_old, zext_toNat _ (by decide)]; omega
                rcases hsp with rfl | rfl | rfl | rfl
                · revert hst_lt; decide
                · revert hst_lt; decide
                · have h1 := congrArg BitVec.toNat hst_old
                  rw [zext_toNat _ (by decide), show (1#64).toNat = 1 from rfl] at h1; omega
                · revert hst_lt; decide
            fr_tiny_lets; apply wp_jnz_of
            · -- `st == 0xFFFFFFFE`: UNSAT -> `unsat = true; break`
              intro hc; simp only [LeanQbe.T.Arg.val_var, beq_iff_eq] at hc
              have hcl0 := hcl0_of_special (Or.inl hc)
              obtain ⟨hwC, _, hteC, _, hunsC, _, _, _, _⟩ := hresC.2 ((hdec_cl0 true).mpr hcl0)
              have hteC' : sL.core.trail_end ≤ sC.core.trail_end := hteC
              (first | rw [wp_jump] | fr_steps)
              exact hJE (src, dst, first_red, irred, redd, true, new_unit, ()) mC
                ⟨by omega, sC, hlikeC, hlenC, hwC, hcmpC.2.1, hcmpC.2.2,
                 fun _ => ⟨hcl0, hunsC hc⟩,
                 fun hnu => ⟨hcl0, by have := (hrootL hcl0).2.2 hnu; omega⟩,
                 fun hpos => by omega, hmC⟩
            · intro hc; simp only [LeanQbe.T.Arg.val_var, beq_eq_false_iff_ne, ne_eq] at hc
              fr_tiny_lets; apply wp_jnz_of
              · -- `st == 0xFFFFFFFD`: OOM -> `break`
                intro hc1; simp only [LeanQbe.T.Arg.val_var, beq_iff_eq] at hc1
                have hcl0 := hcl0_of_special (Or.inr (Or.inl hc1))
                obtain ⟨hwC, _, hteC, _, _, _, _, _, _⟩ := hresC.2 ((hdec_cl0 true).mpr hcl0)
                have hteC' : sL.core.trail_end ≤ sC.core.trail_end := hteC
                (first | rw [wp_jump] | fr_steps)
                exact hJE (src, dst, first_red, irred, redd, false, new_unit, ()) mC
                  ⟨by omega, sC, hlikeC, hlenC, hwC, hcmpC.2.1, hcmpC.2.2,
                   fun h => Bool.noConfusion h,
                   fun hnu => ⟨hcl0, by have := (hrootL hcl0).2.2 hnu; omega⟩,
                   fun hpos => by omega, hmC⟩
              · intro hc1; simp only [LeanQbe.T.Arg.val_var, beq_eq_false_iff_ne, ne_eq] at hc1
                fr_tiny_lets; apply wp_jnz_of
                · -- `st == 1`: new level-0 unit -> `new_unit = true; src = nsrc; continue`
                  intro hc2; simp only [LeanQbe.T.Arg.val_var, beq_iff_eq] at hc2
                  have hcl0 := hcl0_of_special (Or.inr (Or.inr (Or.inl hc2)))
                  obtain ⟨hwC, hbinC, hteC, _, _, _, _, hunitC, _⟩ :=
                    hresC.2 ((hdec_cl0 true).mpr hcl0)
                  (first | rw [wp_jump] | fr_steps)
                  refine hLoopL (nsrc32.setWidth 64, dst, first_red, irred, redd, true, ())
                    mC hdec_m
                    ⟨by omega, by rw [hnsrc64]; exact hnxt_le_al, fun hlt => ?_,
                     sC, hlikeC, hlenC, hcmpC, hbinC,
                     htailC, fun _ => ⟨hwC, by have := (hrootL hcl0).2.1; omega,
                       fun _ => by have := (hrootL hcl0).2.1; have := hunitC hc2; omega⟩,
                     fun hpos => by omega, hmC⟩
                  rw [hnsrc64] at hlt ⊢; exact hnxt_mem.resolve_left (by omega)
                · intro hc2; simp only [LeanQbe.T.Arg.val_var, beq_eq_false_iff_ne, ne_eq] at hc2
                  fr_tiny_lets; apply wp_jnz_of
                  · -- `st == 0xFFFFFFFF`: sat or binary -> `src = nsrc; continue`
                    intro hc3; simp only [LeanQbe.T.Arg.val_var, beq_iff_eq] at hc3
                    have hcl0 := hcl0_of_special (Or.inr (Or.inr (Or.inr hc3)))
                    obtain ⟨hwC, hbinC, hteC, _, _, _, _, _, _⟩ :=
                      hresC.2 ((hdec_cl0 true).mpr hcl0)
                    (first | rw [wp_jump] | fr_steps)
                    refine hLoopL (nsrc32.setWidth 64, dst, first_red, irred, redd, new_unit, ())
                      mC hdec_m
                      ⟨by omega, by rw [hnsrc64]; exact hnxt_le_al, fun hlt => ?_,
                       sC, hlikeC, hlenC, hcmpC, hbinC,
                       htailC, fun _ => ⟨hwC, by have := (hrootL hcl0).2.1; omega,
                         fun hnu => by have := (hrootL hcl0).2.2 hnu; omega⟩,
                       fun hpos => by omega, hmC⟩
                    rw [hnsrc64] at hlt ⊢; exact hnxt_mem.resolve_left (by omega)
                  · intro hc3; simp only [LeanQbe.T.Arg.val_var, beq_eq_false_iff_ne, ne_eq] at hc3
                    -- Live compacted block: `3 ≤ new_sz ≤ old_sz`!
                    clear hcl0_of_special hJE JE hcmpL htailL
                    obtain ⟨hnew3, hnew_le, hnew_lt, hnew_sub, hnew_ent, hbinC⟩ :=
                      sweep_copy_new_props hw0 hbinL hresC hdec_cl0 hcvL
                        (by rw [hlikeC.unchanged.1, hcvL]) hsz3 harL_len
                        harC_len (by omega) hdst_src hsrc_ref hng_src hsrc_lits_eq
                        (fun j hj => hcvL ▸ hlits_lt_src j hj)
                        (by assumption) (by assumption) (by assumption) (by assumption)
                    clear hbinL hsz3 hsrc_fit hlits_lt_src hnext hcopy hcl_beq hlike0 hbin0 hlen0
                      h0_lv h0_tr h0_tp h0_te
                    have hnsz32_eq : (st.setWidth 32).toNat = st.toNat := by
                      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                    have hd1_eq : (dst + (1 : BitVec 64)).toNat = dst.toNat + 1 :=
                      bv64_add1 (by omega)
                    have hd2_eq : (dst + (2 : BitVec 64)).toNat = dst.toNat + 2 := by
                      rw [BitVec.toNat_add, show (2 : BitVec 64).toNat = 2 from rfl,
                        Nat.mod_eq_of_lt (by omega)]
                    -- Write compacted header `ar[dst..dst+2]`
                    fr_unmdata
                    try c0_let_simp
                    apply wp_store_sep
                    · simp only [LeanQbe.T.Arg.val_var]
                      exact FullArenaTactics.c0_store_full_arena _ (by omega) hmC
                    intro m1 hm1
                    clear hmC
                    try c0_let_simp
                    apply wp_store_sep
                    · simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]
                      exact FullArenaTactics.c0_store_full_arena _
                        (by simp only [List.length_set, hd1_eq]; omega) hm1
                    intro m2 hm2
                    clear hm1
                    try c0_let_simp
                    apply wp_store_sep
                    · simp only [LeanQbe.T.Arg.val_var]
                      exact FullArenaTactics.c0_store_full_arena _
                        (by simp only [List.length_set, hd2_eq]; omega) hm2
                    intro m hm
                    clear hm2
                    try c0_let_simp
                    let hdr0 := sL.core.arena[src.toNat]'hs0_lt
                    have hst32_of : st.setWidth 32 = BitVec.ofNat 32 st.toNat := by
                      apply BitVec.eq_of_toNat_eq
                      rw [hnsz32_eq, bv32_ofNat_toNat (by omega)]
                    obtain ⟨arH, harH_len, hbodyH, hszH, hdropH, hcmpH, happend_mk, hm_arH⟩ :=
                      sweep_write_hdr_wrap hcmpC hcongrC
                        (by rw [hlikeC.unchanged.1]) hnew3 harC_len
                        (by omega) hd1_eq hd2_eq (bv32_ofNat_toNat (by omega)) hsrc_ref hng_src
                        hhdr_orig ⟨h0_ar, h0_al⟩ hnew_lt hnew_sub hnew_ent
                        (fullMem_cast hm (by simp only [hst32_of]; congr 1))
                    clear hm hcongrC
                    have hdst_next_eq :
                        (dst + (3 : BitVec 64) + (st.setWidth 32).setWidth 64).toNat =
                        dst.toNat + 3 + st.toNat := by
                      rw [BitVec.toNat_add, BitVec.toNat_add,
                        zext_toNat (st.setWidth 32) (by decide), hnsz32_eq]
                      simp; omega
                    -- Join point after optional `if ((hdr & PH_RSN) != 0)` reason-remapping loop
                    fr_to_group
                    refine wp_join_group (ArenaSweepRsnInv c s s0 sC R arH
                      (nsrc32.setWidth 64).toNat dst.toNat st.toNat) ?_ ?_
                    · -- Continuation after reason-remapping: update `first_red`/`redd`/`irred`
                      rintro _ ⟨⟩ mR ⟨rsnsR, hrsnsR_len, hrsns_r0, hrmR, hmR⟩
                      let sNext : FullState :=
                        { sC with core := { sC.core with arena := arH, rsns := rsnsR } }
                      have hlenNext : sNext.LengthsOk c :=
                        ⟨{ hlenC.core_ok with arena_len_arr := harH_len,
                                              rsns_len := hrsnsR_len }, hlenC.scratch_ok⟩
                      have hstep_next : ∀ fr' ir' rd',
                          JL (nsrc32.setWidth 64,
                              dst + (3 : BitVec 64) + (st.setWidth 32).setWidth 64,
                              fr', ir', rd', new_unit, ()) mR := fun fr' ir' rd' => by
                        refine hLoopL _ mR hdec_m
                          ⟨by rw [hdst_next_eq, hnsrc64]; have := hwf0.2.2.1; omega,
                           by rw [hnsrc64]; exact hnxt_le_al, fun hlt => ?_,
                           sNext, hlikeC.of_ar_rsns, hlenNext,
                           by rw [hdst_next_eq]; exact hcmpH.with_rsns,
                           hbinC.with_core rfl rfl rfl rfl,
                           fun i hi1 hi2 => by
                             rw [hbodyH i (by have := hwf0.2.2.1; rw [hnsrc64] at hi1; omega)]
                             exact htailC i hi1 hi2,
                           fun hcl0 => ?_, fun hpos => ?_, fullMem_cast hmR rfl⟩
                        · rw [hnsrc64] at hlt ⊢; exact hnxt_mem.resolve_left (by omega)
                        · obtain ⟨hwC, _, hteC, _, _, _, _, _, _⟩ :=
                            hresC.2 ((hdec_cl0 true).mpr hcl0)
                          rw [hdst_next_eq]
                          have hhr := hrsns_r0 hcl0
                          have hkn : ({ sNext.core with arena_len := dst.toNat + 3 + st.toNat } :
                              FullCoreState) =
                              { { sC.core with arena := arH } with
                                arena_len := dst.toNat + 3 + st.toNat } :=
                            by dsimp [sNext]; rw [hhr]
                          rw [hkn]
                          have hte_nxt : sNext.core.trail_end = sC.core.trail_end := rfl
                          exact ⟨fullWitnessInv_append_root hwC hbinC
                              (hlikeC.unchanged.2.2.1.trans hcl0) hcmpH.1,
                            by have := (hrootL hcl0).2.1; rw [hte_nxt]; omega,
                            fun hnu => by have := (hrootL hcl0).2.2 hnu; rw [hte_nxt]; omega⟩
                        · obtain ⟨_, hvC, _, hlC, _, htC, htpC, hteC, _, _, _, _, _, _, _, _, _,
                            _, _⟩ := hresC.1 ((hdec_cl0 false).mpr hpos)
                          obtain ⟨hnu0, hv0, hl0, ht0, htp0, hte0, _⟩ := hposL hpos
                          exact ⟨hnu0, hvC.trans hv0, hlC.trans hl0, htC.trans ht0,
                            htpC.trans htp0, hteC.trans hte0,
                            by rw [hdst_next_eq]; exact hrmR hpos⟩
                      refine wp_unroll_group fun Js hJs => ?_
                      try c0_let_simp
                      apply wp_jnz_of
                      · intro _; try c0_let_simp
                        refine wp_unroll_group fun Js1 hJs1 => ?_
                        try c0_let_simp
                        apply wp_jnz_of <;>
                          (intro _; (try c0_let_simp); apply hJs1; (try c0_let_simp);
                           apply hJs; (try c0_let_simp); exact hstep_next _ _ _)
                      · intro _; try c0_let_simp
                        apply hJs; try c0_let_simp; exact hstep_next _ _ _
                    · -- Entry to `if ((hdr & PH_RSN) != 0)`
                      intro JR hJR
                      clear hLoopL JL hcmpC hcmpH htailC hbinC hrootL hnxt_le_al hnxt_mem
                        hdst_next_eq hdec_m hnxt_bd hsz3_pre hfit_pre
                      fr_tiny_lets
                      apply wp_jnz_of
                      · -- `(hdr & PH_RSN) != 0`: scan `i < new_sz` for matching trail reason
                        intro _
                        fr_to_group
                        refine wp_join_group (fun (_ : Tup Val [i32]) =>
                            ArenaSweepRsnInv c s s0 sC R arH
                              (nsrc32.setWidth 64).toNat dst.toNat st.toNat ()) ?_ ?_
                        · rintro _ ⟨_iB, ⟨⟩⟩ mB hB; (first | rw [wp_jump] | fr_steps)
                          exact hJR () mB hB
                        · intro Jbrk hJbrk
                          refine wp_loop_inv
                            (ArenaSweepRsnLoopInv s sC arH src.toNat dst.toNat st.toNat m)
                            (fun (i, ()) _ => st.toNat - i.toNat) (fun Ji hLoopI => ?_) ?_
                          · fr_steps
                            exact hLoopI (0#32, ()) m ⟨rfl, Nat.zero_le _,
                              fun _ _ hj => absurd hj (Nat.not_lt_zero _)⟩
                          · rintro Ji ⟨i, ⟨⟩⟩ mI ⟨hmI, hi_le, hmissI⟩ hLoopI
                            subst mI
                            fr_split
                            · have hi_lt : i.toNat < st.toNat := by
                                have : i.toNat < (st.setWidth 32).toNat := by c0_bound
                                omega
                              have hi1_eq : (i + (1 : BitVec 32)).toNat = i.toNat + 1 :=
                                bv32_add1 (by omega)
                              have hdi_eq : (dst + (3 : BitVec 64) + i.setWidth 64).toNat =
                                  dst.toNat + 3 + i.toNat := by
                                rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat i (by decide)]
                                simp; omega
                              have hdi_lt : (dst + (3 : BitVec 64) + i.setWidth 64).toNat <
                                  arH.length := by omega
                              let litI := arH[(dst + (3 : BitVec 64) + i.setWidth 64).toNat]'hdi_lt
                              have hlitI_lt : litI.toNat < 2 * s.core.cur_vars := by
                                have h1' : arH[dst.toNat + 3 + i.toNat]?.getD 0#32 = litI := by
                                  rw [List.getElem?_eq_getElem
                                      (by omega : dst.toNat + 3 + i.toNat < arH.length),
                                    Option.getD_some]
                                  simp only [litI, hdi_eq]
                                have h1 := hnew_lt i.toNat hi_lt
                                rw [← hbodyH (dst.toNat + 3 + i.toNat) (by omega), h1'] at h1
                                exact h1
                              have hvI_eq : (litI >>> (1 : BitVec 32)).toNat = litI.toNat / 2 :=
                                bv32_shr1_toNat litI
                              have hlitI_v : litI.toNat < sC.core.vals.length := by
                                have := hlenC.core_ok.vals_len; omega
                              have hvI_r : (litI >>> (1 : BitVec 32)).toNat <
                                  sC.core.rsns.length := by
                                have := hlenC.core_ok.rsns_len; omega
                              have hlitI_v64 :
                                  (litI.setWidth 64).toNat < sC.core.vals.length := by
                                rw [zext_toNat _ (by decide)]; exact hlitI_v
                              have hvI_r64 :
                                  ((litI >>> (1 : BitVec 32)).setWidth 64).toNat <
                                    sC.core.rsns.length := by
                                rw [zext_toNat _ (by decide), hvI_eq]; exact hvI_r
                              fr_to_group
                              refine wp_join_group
                                (ArenaSweepRsnNextInv s sC litI src.toNat m) ?_ ?_
                              · rintro _ ⟨⟩ _ ⟨rfl, hmiss_cur⟩
                                fr_steps
                                refine hLoopI (i + (1 : BitVec 32), ()) m
                                  (by dsimp only; rw [hi1_eq]; omega)
                                  ⟨rfl, by rw [hi1_eq]; omega, fun hpos j hj => ?_⟩
                                rw [hi1_eq] at hj
                                by_cases hje : j = i.toNat
                                · subst j
                                  have hlit_eq :
                                      arH[dst.toNat + 3 + i.toNat]?.getD 0#32 = litI := by
                                    rw [List.getElem?_eq_getElem (by omega : dst.toNat + 3 +
                                      i.toNat < arH.length), Option.getD_some]
                                    simp only [litI, hdi_eq]
                                  simpa [hlit_eq] using hmiss_cur hpos
                                · exact hmissI hpos j (by omega)
                              · intro Jni hJni
                                let sH : FullState :=
                                  { sC with core := { sC.core with arena := arH } }
                                have hvI_r' : litI.toNat / 2 < sC.core.rsns.length :=
                                  hvI_eq ▸ hvI_r
                                fr_tiny_lets
                                apply wp_jnz_of
                                · intro _; fr_tiny_lets
                                  apply wp_load_of
                                  · simp only [LeanQbe.T.Arg.val_var]
                                    apply FullArenaTactics.c0_load_full_vals
                                      (s := sH) (hm := hm_arH)
                                    change _ < sC.core.vals.length
                                    simp only [LeanQbe.T.bv_c0_zext32_64]
                                    exact hlitI_v
                                  fr_tiny_lets
                                  apply wp_jnz_of
                                  · intro hval_gt0
                                    simp only [LeanQbe.T.Arg.val_var] at hval_gt0
                                    fr_tiny_lets
                                    apply wp_load_of
                                    · simp only [LeanQbe.T.Arg.val_var]
                                      apply FullArenaTactics.c0_load_full_rsns
                                        (s := sH) (hm := hm_arH)
                                      change _ < sC.core.rsns.length
                                      simp only [LeanQbe.T.bv_c0_zext32_64,
                                        BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                        Nat.pow_one]
                                      exact hvI_r'
                                    fr_tiny_lets
                                    apply wp_jnz_of
                                    · -- HIT! `rsns[v] = (u32)dst; break`
                                      intro hc
                                      simp only [LeanQbe.T.Arg.val_var, beq_iff_eq] at hc
                                      fr_tiny_lets
                                      apply wp_store_sep
                                      · simp only [LeanQbe.T.Arg.val_var]
                                        apply FullArenaTactics.c0_store_full_rsns
                                          (s := sH) (hm := hm_arH)
                                        change _ < sC.core.rsns.length
                                        simp only [LeanQbe.T.bv_c0_zext32_64,
                                          BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                          Nat.pow_one]
                                        exact hvI_r'
                                      intro m hm; clear hm_arH
                                      rw [wp_jump]
                                      have hrsn_eq :
                                          (sC.core.rsns[litI.toNat / 2]?.getD 0xFFFFFFFF#32).toNat =
                                          src.toNat := by
                                        have h1 := congrArg BitVec.toNat hc
                                        simp only [LeanQbe.T.bv_c0_zext32_64] at h1
                                        rw [List.getElem?_eq_getElem hvI_r', Option.getD_some]
                                        simpa only [sH, litI, BitVec.toNat_ushiftRight,
                                          Nat.shiftRight_eq_div_pow, Nat.pow_one] using h1
                                      have hvg : (0#32).slt
                                          ((sC.core.vals[litI.toNat]'hlitI_v).signExtend 32) =
                                          true := by
                                        simpa only [sH, litI, LeanQbe.T.bv_c0_zext32_64]
                                          using hval_gt0
                                      have hidx_eq :
                                          (BitVec.setWidth 64
                                            (arH[(dst + 3 + i.setWidth 64).toNat] >>>
                                              (1 : Nat))).toNat =
                                          litI.toNat / 2 := by
                                        simp only [LeanQbe.T.bv_c0_zext32_64,
                                          BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                          Nat.pow_one]
                                        rfl
                                      rw [hidx_eq] at hm
                                      refine hJbrk (i, ()) m
                                        ⟨sC.core.rsns.set (litI.toNat / 2) (dst.setWidth 32),
                                         by simp [hlenC.core_ok.rsns_len], fun hcl0 => ?_,
                                         fun hpos => ?_, hm⟩
                                      · exact False.elim (sweep_rsn_hit_false_at_root
                                          (hresC.2 ((hdec_cl0 true).mpr hcl0)).1
                                          (hlikeC.unchanged.2.2.1.trans hcl0)
                                          (by rw [hlikeC.unchanged.1]; exact hlitI_lt)
                                          hlitI_v hlenC.core_ok.rsns_len
                                          (by rw [hlikeC.unchanged.1]; exact hcv_le)
                                          hsrc_lt8 hvg hrsn_eq)
                                      · obtain ⟨_, hvC, _, hrC, _, _, _, hlits_eq⟩ :=
                                          sweep_pos_lits_eq hresC ((hdec_cl0 false).mpr hpos)
                                            harL_len harC_len (by omega) hdst_src hsrc_lits_eq
                                            hszH hdropH
                                        obtain ⟨_, hv0, _, _, _, _, hrmL⟩ := hposL hpos
                                        exact sweep_rsn_hit_pos hw0 hsrc_ref hnsrc64 hdst_src
                                          hsrc_lt8 hrmL
                                          (happend_mk (sC.core.rsns.set (litI.toNat / 2)
                                            (dst.setWidth 32)) hlits_eq)
                                          (hvC.trans (hv0.trans h0_va.symm))
                                          hrC hlenC.core_ok.rsns_len (h0_cv ▸ hcv_le)
                                          (h0_cv ▸ hlitI_lt) hlitI_v hvg hrsn_eq
                                    · intro hc
                                      simp only [LeanQbe.T.Arg.val_var, beq_eq_false_iff_ne,
                                        ne_eq] at hc
                                      rw [wp_jump]
                                      refine hJni () m ⟨rfl, fun _ ⟨_, _, hrs⟩ => ?_⟩
                                      apply hc; apply BitVec.eq_of_toNat_eq
                                      rw [LeanQbe.T.bv_c0_zext32_64]
                                      have h1 := congrArg BitVec.toNat hrs
                                      rw [bv32_ofNat_toNat (by omega),
                                        List.getElem?_eq_getElem hvI_r', Option.getD_some] at h1
                                      simpa only [sH, litI, LeanQbe.T.bv_c0_zext32_64,
                                        BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                        Nat.pow_one] using h1
                                  · intro hc
                                    simp only [LeanQbe.T.Arg.val_var] at hc
                                    rw [wp_jump]
                                    refine hJni () m ⟨rfl, fun _ ⟨_, hvg, _⟩ => ?_⟩
                                    rw [List.getElem?_eq_getElem hlitI_v, Option.getD_some] at hvg
                                    exact Bool.false_ne_true (hc.symm.trans
                                      (by simpa only [sH, litI, LeanQbe.T.bv_c0_zext32_64]
                                            using hvg))
                                · intro hc
                                  simp only [LeanQbe.T.Arg.val_var, BitVec.ult,
                                    decide_eq_false_iff_not, LeanQbe.T.bv_c0_zext32_64,
                                    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                    Nat.pow_one, BitVec.toNat_ofNat] at hc
                                  rw [Nat.mod_eq_of_lt (by omega)] at hc
                                  change ¬ (litI.toNat / 2 < s0.core.cur_vars) at hc
                                  omega
                            · -- Loop finished (`i = new_sz`) without match -> NO var had `r0 = src`
                              have hi_eq : i.toNat = st.toNat := by
                                have : (st.setWidth 32).toNat ≤ i.toNat := by c0_bound
                                omega
                              (first | rw [wp_jump] | fr_steps)
                              refine hJbrk (i, ()) m
                                ⟨sC.core.rsns, hlenC.core_ok.rsns_len, fun _ => rfl,
                                fun hpos => ?_, fullMem_cast hm_arH rfl⟩
                              obtain ⟨_, hvC, _, hrC, _, _, _, hlits_eq⟩ :=
                                sweep_pos_lits_eq hresC ((hdec_cl0 false).mpr hpos) harL_len
                                  harC_len (by omega) hdst_src hsrc_lits_eq hszH hdropH
                              obtain ⟨_, hv0, _, _, _, _, hrmL⟩ := hposL hpos
                              exact sweep_rsn_miss_pos hw0 hsrc_ref hnsrc64 hdst_src hsrc_lt8
                                hrmL (happend_mk sC.core.rsns hlits_eq)
                                (hvC.trans (hv0.trans h0_va.symm))
                                hrC hszH (by omega) hlits_eq
                                (fun j hj => h0_cv ▸ hmissI hpos j (by omega))
                      · -- `(hdr & PH_RSN) == 0`: by `FullReasonsMarked s0`, no var has `r0 = src`
                        intro hc
                        simp only [LeanQbe.T.Arg.val_var, bne_eq_false_iff_eq] at hc
                        (first | rw [wp_jump] | fr_steps)
                        refine hJR () m ⟨sC.core.rsns, hlenC.core_ok.rsns_len, fun _ => rfl,
                          fun hpos => ?_, fullMem_cast hm_arH rfl⟩
                        obtain ⟨_, _, _, hrC, _, _, _, hlits_eq⟩ :=
                          sweep_pos_lits_eq hresC ((hdec_cl0 false).mpr hpos) harL_len harC_len
                            (by omega) hdst_src hsrc_lits_eq hszH hdropH
                        obtain ⟨_, _, _, _, _, _, hrmL⟩ := hposL hpos
                        exact sweep_rsn_unmarked_pos hw0 (hrmk0 (h0_cl ▸ hpos)) hsrc_ref hnsrc64
                          hdst_src hsrc_lt8 hrmL (happend_mk sC.core.rsns hlits_eq) hrC
                          (by rw [← hhdr_orig]; exact hc)
      · -- Exit compaction loop (`src = alen`): jump to `JE`
        have hsrc_end : src.toNat = s.core.arena_len := by c0_bound
        fr_steps
        refine hJE (src, dst, first_red, irred, redd, false, new_unit, ()) mL
          ⟨by omega, sL, hlikeL, hlenL, ?_, hcmpL.2.1, hcmpL.2.2,
           fun h => Bool.noConfusion h, fun hnu => ?_, fun hpos => ?_, hmL⟩
        · by_cases hcl0 : s.core.cur_level = 0
          · exact (hrootL hcl0).1
          · obtain ⟨_, hv, hl, ht, htp, hte, hrmL⟩ := hposL (by omega)
            exact SweepReasonMapInv.toFullWitnessInv hw0 hcmpL.1 hbinL (hv.trans h0_va.symm)
              (hl.trans h0_lv.symm) (ht.trans h0_tr.symm) (htp.trans h0_tp.symm)
              (hte.trans h0_te.symm) (hclL.trans h0_cl.symm) (hcvL.trans h0_cv.symm)
              (hftL.trans hlike0.unchanged.2.2.2.2.1.symm)
              (hfdL.trans hlike0.unchanged.2.2.2.2.2.1.symm)
              (hincL.trans hlike0.unchanged.2.2.2.2.2.2.symm)
              ((hsrc_end.trans h0_al.symm) ▸ hrmL)
        · by_cases hcl0 : s.core.cur_level = 0
          · exact ⟨hcl0, (hrootL hcl0).2.2 hnu⟩
          · exact absurd (hposL (by omega)).1 (by simp [hnu])
        · obtain ⟨hnu, hv, hl, ht, htp, hte, _⟩ := hposL hpos
          exact ⟨rfl, hnu, hv, hl, ht, htp, hte⟩

end LeanQbe.T.Examples.Kissat.Full
