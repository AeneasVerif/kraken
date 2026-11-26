/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7V2Robust
public import LeanQbe.T.Examples.Kissat.FullM7V2RobustProof0
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Examples.Kissat.FullAssignAddLemmas1
import LeanQbe.T.Examples.Kissat.FullReduceLemmas1
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Examples.Kissat.FullLearnAnaLemmas1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Step-12 `S1.5` Del-Spec Bridge for `full_reduce_purge_c0`
(`FullFidelityStep12ProofPurgeDel`)

Purely additive `Full.fullPropagateDelSpec` proof of `FullM7V2Robust.full_reduce_purge_c0_body`
(`full_reduce_purge_c0_del_wp`) against `Full.fullReduceSpec (h, true, ())`, bridging
`FullM6S15Bridge.s15_to_propagateDel` without modifying `FullM7V2RobustProof0.lean`
(`0` `@[expose]` thms, `0` new `import all`, `<= std3`, `XPost`-polymorphic).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM7V2Robust
open Full.FullReduceTactics
open scoped Full.FullArenaTactics Full.FullReduceTactics
open Kraken.Bedrock2.Test

private def Fid12PurgeStateOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s' : FullState) : Prop :=
  FullSparseInv c F0 s' ∧
  FullWitnessInv c F0 F_cur s'.core ∧
  s'.core.cur_level ≤ s.core.cur_level ∧
  s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
  s'.core.cur_vars = s.core.cur_vars ∧
  s'.core.tmp = s.core.tmp ∧
  s'.core.tmp_len = s.core.tmp_len ∧
  s'.core.frame_trail = s.core.frame_trail ∧
  s'.core.frame_dec = s.core.frame_dec ∧
  s'.core.inconsistent = s.core.inconsistent ∧
  s'.core.d_cur = s.core.d_cur ∧
  s'.core.d_val = s.core.d_val ∧
  s'.scratch.extend_len = s.scratch.extend_len ∧
  s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
  (0 < s'.core.cur_level →
    s'.core.cur_level = s.core.cur_level ∧ s'.core.vals = s.core.vals ∧
    s'.core.lvl = s.core.lvl ∧ s'.core.trl = s.core.trl ∧
    s'.core.trail_pos = s.core.trail_pos ∧ s'.core.trail_end = s.core.trail_end)

private theorem fid12_purgeStateOk_refl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInv c F0 s) (hw : FullWitnessInv c F0 F_cur s.core) :
    Fid12PurgeStateOk c F0 F_cur s s :=
  ⟨hsp, hw, Nat.le_refl _, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem fid12_purgeStateOk_trans {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s1 s2 : FullState} (h1 : Fid12PurgeStateOk c F0 F_cur s s1)
    (h2 : Fid12PurgeStateOk c F0 F_cur s1 s2) : Fid12PurgeStateOk c F0 F_cur s s2 :=
  ⟨h2.1, h2.2.1, Nat.le_trans h2.2.2.1 h1.2.2.1, Nat.le_trans h2.2.2.2.1 h1.2.2.2.1,
    h2.2.2.2.2.1.trans h1.2.2.2.2.1, h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun hpos => by
      have hpos1 : 0 < s1.core.cur_level := Nat.lt_of_lt_of_le hpos h2.2.2.1
      have ha := h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hpos
      have hb := h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hpos1
      exact ⟨ha.1.trans hb.1, ha.2.1.trans hb.2.1, ha.2.2.1.trans hb.2.2.1,
        ha.2.2.2.1.trans hb.2.2.2.1, ha.2.2.2.2.1.trans hb.2.2.2.2.1,
        ha.2.2.2.2.2.trans hb.2.2.2.2.2⟩⟩

private theorem fid12_purgeStateOk_with_unflushed {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s1 : FullState} (h1 : Fid12PurgeStateOk c F0 F_cur s s1)
    (u' : BitVec 64) :
    Fid12PurgeStateOk c F0 F_cur s { s1 with core := { s1.core with unflushed := u' } } := by
  have hsp1 := h1.1
  have hw' := FullDenseWatchHelpers.fullWitnessInv_with_unflushed h1.2.1 u'
  have hlen' : ({ s1 with core := { s1.core with unflushed := u' } } : FullState).LengthsOk c :=
    ⟨{ hsp1.1.lengths.core_ok with vals_len := hsp1.1.lengths.core_ok.vals_len },
      hsp1.1.lengths.scratch_ok⟩
  have hsp' : FullSparseInv c F0 { s1 with core := { s1.core with unflushed := u' } } :=
    ⟨⟨hlen', ⟨F_cur, hw'⟩⟩, hsp1.2.1, hsp1.2.2.1, hsp1.2.2.2.1, hsp1.2.2.2.2⟩
  exact fid12_purgeStateOk_trans h1 ⟨hsp', hw', Nat.le_refl _, Nat.le_refl _, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem fid12_purgeStateOk_mark_reasons {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s2 : FullState} {ar' : List (BitVec 32)}
    (h2 : Fid12PurgeStateOk c F0 F_cur s s2)
    (hlen' : ({ s2 with core := { s2.core with arena := ar' } } : FullState).LengthsOk c)
    (hrefs : fullArenaClauseRefs { s2 with core := { s2.core with arena := ar' } } =
      fullArenaClauseRefs s2)
    (hper : ∀ r ∈ fullArenaClauseRefs s2,
      fullArenaClauseSize { s2 with core := { s2.core with arena := ar' } } r =
        fullArenaClauseSize s2 r ∧
      fullArenaClauseGarb { s2 with core := { s2.core with arena := ar' } } r =
        fullArenaClauseGarb s2 r ∧
      fullArenaClauseLits { s2 with core := { s2.core with arena := ar' } } r =
        fullArenaClauseLits s2 r)
    (hw' : FullWitnessInv c F0 F_cur { s2.core with arena := ar' }) :
    Fid12PurgeStateOk c F0 F_cur s { s2 with core := { s2.core with arena := ar' } } := by
  let s3 : FullState := { s2 with core := { s2.core with arena := ar' } }
  have hnd : FullArenaVarsNodup s3 := fun r hr hng => by
    rw [hrefs] at hr; rw [(hper r hr).2.1] at hng; rw [(hper r hr).2.2]
    exact h2.1.2.2.1 r hr hng
  have hll : FullLastLearnedWf s3 := fun i hi => by
    change s2.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
      (s2.scratch.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs s3
    rw [hrefs]; exact h2.1.2.2.2.1.1 i hi
  exact fid12_purgeStateOk_trans h2 ⟨⟨⟨hlen', ⟨F_cur, hw'⟩⟩, h2.1.2.1, hnd,
    ⟨hll, h2.1.2.2.2.1.2⟩, h2.1.2.2.2.2⟩, hw', Nat.le_refl _, Nat.le_refl _,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem fid12_purgeStateOk_backtrack0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s0 : FullState} (h0 : Fid12PurgeStateOk c F0 F_cur s s0)
    {vals' : List (BitVec 8)} {lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' : BitVec 64} {sc' : FullScratch} :
    let sB : FullState := { s0 with
      core := { s0.core with
        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', cur_level := 0, unassigned := unass' }
      scratch := sc' }
    sB.LengthsOk c → FullWitnessInv c F0 F_cur sB.core →
    sc'.last_learned = s0.scratch.last_learned →
    sc'.extend_len = s0.scratch.extend_len →
    sc'.work_stk2 = s0.scratch.work_stk2 →
    Fid12PurgeStateOk c F0 F_cur s sB := by
  intro sB hlen' hw' hll' hext' hws2'
  have hllB : FullLastLearnedWf sB := fun i hi => by
    change sc'.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
      (sc'.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs s0
    rw [hll']; exact h0.1.2.2.2.1.1 i hi
  exact fid12_purgeStateOk_trans h0 ⟨⟨⟨hlen', ⟨F_cur, hw'⟩⟩, h0.1.2.1, h0.1.2.2.1,
    ⟨hllB, hext' ▸ h0.1.2.2.2.1.2⟩, h0.1.2.2.2.2⟩, hw', Nat.zero_le _, Nat.le_refl _,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hext', hws2', fun hpos => by cases hpos⟩

private theorem fid12_purgeStateOk_propagate0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sA : FullState} (hA : Fid12PurgeStateOk c F0 F_cur s sA)
    (hcl0 : sA.core.cur_level = 0)
    {valsB : List (BitVec 8)}
    {flagsB lvlB rsnsB trlB tpB wvecB arenaB wstkB : List (BitVec 32)}
    {teB propB wlenB : Nat} {unassB unflB wuB fuelB ctypeB crefB c0B c1B oomB : BitVec 64}
    {scB : FullScratch} :
    let sB : FullState :=
      { sA with
        core := { sA.core with
          vals := valsB, flags := flagsB, lvl := lvlB, rsns := rsnsB, trl := trlB,
          trail_pos := tpB, trail_end := teB, propagated := propB, unassigned := unassB,
          unflushed := unflB, wvec := wvecB, arena := arenaB, wstk := wstkB, wlen := wlenB,
          wusable := wuB, fuel := fuelB, confl_type := ctypeB, confl_ref := crefB,
          confl_lit0 := c0B, confl_lit1 := c1B, oom := oomB }
        scratch := scB }
    sB.LengthsOk c → FullWitnessInv c F0 F_cur sB.core →
    FullArenaVarsNodup sB → (∀ ref ∈ fullArenaClauseRefs sA, ref ∈ fullArenaClauseRefs sB) →
    scB.last_learned = sA.scratch.last_learned →
    scB.extend_len = sA.scratch.extend_len →
    scB.work_stk2 = sA.scratch.work_stk2 →
    fuelB.toNat ≤ sA.core.fuel.toNat →
    Fid12PurgeStateOk c F0 F_cur s sB := by
  intro sB hlenB hwB hndB hrefsB hllB hextB hws2B hfuelB
  have hll' : FullLastLearnedWf sB := fun i hi => by
    change scB.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
      (scB.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs sB
    rw [hllB]; exact (hA.1.2.2.2.1.1 i hi).imp id (hrefsB _)
  exact fid12_purgeStateOk_trans hA ⟨⟨⟨hlenB, ⟨F_cur, hwB⟩⟩, hA.1.2.1, hndB,
    ⟨hll', hextB ▸ hA.1.2.2.2.1.2⟩, hA.1.2.2.2.2⟩, hwB, Nat.le_refl _, hfuelB,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hextB, hws2B,
    fun hpos => by change 0 < sA.core.cur_level at hpos; omega⟩

private theorem fid12_purgeStateOk_arena_sweep {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s st : FullState} (hst : Fid12PurgeStateOk c F0 F_cur s st)
    {vals' : List (BitVec 8)}
    {flags' lvl' rsns' trl' tp' wvec' wstk' arena' : List (BitVec 32)}
    {te' alen' wlen' : Nat} {unass' unfl' wu' fred' ni' nr' nb' oom' : BitVec 64}
    {sc' : FullScratch} :
    let sA : FullState :=
      { st with
        core := { st.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
          wvec := wvec', wstk := wstk', arena := arena', arena_len := alen', wlen := wlen',
          wusable := wu', arena_garbage := 0#64, first_reducible := fred', num_irred := ni',
          num_redundant := nr', num_binary := nb', oom := oom' }
        scratch := sc' }
    sA.LengthsOk c → FullWitnessInv c F0 F_cur sA.core →
    FullArenaVarsNodup sA → FullLastLearnedWf sA →
    sc'.extend_len = st.scratch.extend_len →
    sc'.work_stk2 = st.scratch.work_stk2 →
    (0 < st.core.cur_level →
      vals' = st.core.vals ∧ lvl' = st.core.lvl ∧ trl' = st.core.trl ∧
      tp' = st.core.trail_pos ∧ te' = st.core.trail_end) →
    Fid12PurgeStateOk c F0 F_cur s sA := by
  intro sA hlenA hwA hndA hllA hextA hws2A hposA
  exact fid12_purgeStateOk_trans hst ⟨⟨⟨hlenA, ⟨F_cur, hwA⟩⟩, hst.1.2.1, hndA,
    ⟨hllA, hextA ▸ hst.1.2.2.2.1.2⟩, hst.1.2.2.2.2⟩, hwA, Nat.le_refl _, Nat.le_refl _,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hextA, hws2A,
    fun hpos => by
      obtain ⟨hv, hl, ht, htp, hte⟩ := hposA hpos
      exact ⟨rfl, hv, hl, ht, htp, hte⟩⟩

private theorem fid12_purgeStateOk_mark_garb {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sL : FullState} {cr : Nat} {agN : BitVec 64}
    (hokL : Fid12PurgeStateOk c F0 F_cur s sL) (hrmL : FullDenseWatchSpecs.FullReasonsMarked sL)
    (hcr_mem : cr ∈ fullArenaClauseRefs sL)
    (hcr_norsn : (fullArenaHdr sL cr &&& 0x00200000#32) = 0#32)
    (hcr_ar : cr < sL.core.arena.length) :
    let sM : FullState :=
      { sL with core := { sL.core with
        arena := sL.core.arena.set cr (sL.core.arena[cr]'hcr_ar ||| 0x00080000#32)
        arena_garbage := agN } }
    Fid12PurgeStateOk c F0 F_cur s sM ∧ FullDenseWatchSpecs.FullReasonsMarked sM ∧
    fullArenaClauseRefs sM = fullArenaClauseRefs sL := by
  intro sM
  have hhdr_eq : sL.core.arena[cr]'hcr_ar = fullArenaHdr sL cr := by
    unfold fullArenaHdr fullArenaHdrCore
    rw [List.getElem?_eq_getElem hcr_ar, Option.getD_some]
  have hnonact := FullDenseWatchHelpers.markGarb_nonact_of_reasonsMarked hokL.2.1 hrmL hcr_norsn
  have hmg := FullDenseWatchHelpers.markGarb_preserves_fullWitnessInv
    hokL.1.1.lengths hokL.2.1 hcr_mem agN hnonact
  rw [← hhdr_eq] at hmg
  obtain ⟨hlenM, hrefsM, hwM, hrsnM, hndM⟩ := hmg
  have hndM' : FullArenaVarsNodup sM := hndM fun r hr hng => hokL.1.2.2.1 r hr hng
  have hllM : FullLastLearnedWf sM := fun j hj => by
    change sL.scratch.last_learned[j]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
      (sL.scratch.last_learned[j]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs sM
    rw [hrefsM]; exact hokL.1.2.2.2.1.1 j hj
  have hrmM : FullDenseWatchSpecs.FullReasonsMarked sM := fun idx hidx hlp hlg => by
    have hne0 : sL.core.rsns[(sL.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
      intro heq; rw [heq] at hlg; revert hlg; decide
    have hrs := hokL.2.1.reason_inv idx hidx hne0
    have hbf : ¬ (sL.core.rsns[(sL.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
    rw [ite_eq_right hbf] at hrs
    rw [hrsnM _ hrs.1]; exact hrmL idx hidx hlp hlg
  have hokM : Fid12PurgeStateOk c F0 F_cur s sM :=
    fid12_purgeStateOk_trans hokL ⟨⟨⟨hlenM, ⟨F_cur, hwM⟩⟩, hokL.1.2.1, hndM',
      ⟨hllM, hokL.1.2.2.2.1.2⟩, hokL.1.2.2.2.2⟩, hwM,
      Nat.le_refl _, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  exact ⟨hokM, hrmM, hrefsM⟩

private theorem fid12_purge_bv32_norsn_of_mask {x : BitVec 32}
    (hx : (x &&& 0x00280000#32) = 0#32) :
    (x &&& 0x00200000#32) = 0#32 := by
  have h21 : (x &&& 0x00280000#32)[21] = false := by rw [hx]; decide
  have hb : (0x00280000#32 : BitVec 32)[21] = true := by decide
  simp only [BitVec.getElem_and, hb, Bool.and_true] at h21
  ext i hi
  by_cases hi21 : i = 21
  · subst hi21; simp [h21]
  · have hz : (0x00200000#32 : BitVec 32)[i] = false := by revert i hi hi21; decide
    simp [BitVec.getElem_and, hz]

/-- Emergency purge `full_reduce_purge_c0` under `Full.fullPropagateDelSpec` (`S1.5` delayed
watch propagation). -/
theorem full_reduce_purge_c0_del_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateDelSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hMarkRsn : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X) :
    ∀ h m Q X, Full.fullReduceSpec (h, true, ()) m Q X →
      Func.wp Γ full_reduce_purge_c0_body (h, ()) m Q X := by
  intro h m Q X hsp
  rcases hsp with ⟨c, F0, F_cur, s, R, rfl, ⟨hlen, hw, hlm, hnd, hext, hdm⟩, hm, hQ⟩
  have har_cap : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hsp0 : FullSparseInv c F0 s := ⟨⟨hlen, ⟨F_cur, hw⟩⟩, hlm, hnd, hext, hdm⟩
  have hok0 : Fid12PurgeStateOk c F0 F_cur s s := fid12_purgeStateOk_refl hsp0 hw
  have hret : ∀ (r : BitVec 64) (st : FullState) (ml : Mem 64),
      Fid12PurgeStateOk c F0 F_cur s st → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → s.core.oom = 0#64 → st.core.oom = 0#64) →
      (FullMem c st ⋆ R) ml → Q (r, ()) ml := fun r st ml hok hr hu hoom hml =>
    hQ r st ml ⟨hok.1.1.lengths, hok.2.1, hok.1.2.1, hok.1.2.2.1, hok.1.2.2.2.1, hok.1.2.2.2.2⟩
      hr hok.2.2.1 hok.2.2.2.1 hok.2.2.2.2.1 hok.2.2.2.2.2.1
      hok.2.2.2.2.2.2.1 hok.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hu hoom
      (fun _ => hok.2.2.2.2.2.2.2.2.2.2.2.2.2.2) hml
  unfold Func.wp full_reduce_purge_c0_body
  fr_to_group
  refine wp_join_group
    (fun _ m1 => ∃ s1 : FullState, Fid12PurgeStateOk c F0 F_cur s s1 ∧
      (s.core.oom = 0#64 → s1.core.oom = 0#64) ∧ (FullMem c s1 ⋆ R) m1)
    ?_ ?_
  · rintro _ _ m1 ⟨s1, hok1, hoom1, hm1⟩
    clear hsp0 hm
    fr_to_group; c0_call hMarkRsn
    refine ⟨c, F0, F_cur, s1, R, rfl, hok1.1.1.lengths, hok1.2.1, hm1,
      fun ar2 m3 hlen3 hrefs3 hper3 hrm3 hw3 hm3 => ?_⟩
    obtain ⟨s3, hok3, hoom3, hrm3', hm3'⟩ :
        ∃ s3 : FullState, Fid12PurgeStateOk c F0 F_cur s s3 ∧
          (s.core.oom = 0#64 → s3.core.oom = 0#64) ∧ FullDenseWatchSpecs.FullReasonsMarked s3 ∧
          (FullMem c s3 ⋆ R) m3 :=
      ⟨{ s1 with core := { s1.core with arena := ar2 } },
        fid12_purgeStateOk_mark_reasons hok1 hlen3 hrefs3 hper3 hw3, hoom1,
        fun idx hidx hp hg => hrm3 rfl idx hidx hp hg, hm3⟩
    clear hm3 s1 hok1 hoom1 hm1 ar2 hlen3 hrefs3 hper3 hrm3 hw3
    fr_to_group
    refine wp_join_group
      (fun _ m4 =>
        ∃ s4 : FullState, Fid12PurgeStateOk c F0 F_cur s s4 ∧
          (s.core.oom = 0#64 → s4.core.oom = 0#64) ∧ FullDenseWatchSpecs.FullReasonsMarked s4 ∧
          (FullMem c s4 ⋆ R) m4)
      ?_ ?_
    · rintro _ _ m4 ⟨s4, hok4, hoom4, hrm4, hm4⟩
      clear s3 hok3 hoom3 hrm3' hm3' m3
      fr_to_group
      refine wp_join_group
        (fun _ mK => ∃ sK : FullState, Fid12PurgeStateOk c F0 F_cur s sK ∧
          (s.core.oom = 0#64 → sK.core.oom = 0#64) ∧ (FullMem c sK ⋆ R) mK)
        (fun _ _ mK ⟨sK, hokK, hoomK, hmK⟩ => by
          fr_steps
          exact hret 1#64 sK mK hokK (Or.inr (Or.inl rfl)) (fun h => by cases h)
            (fun _ => hoomK) hmK)
        (fun Jbrk hJbrk => by
          fr_to_group
          refine wp_loop_group
            (fun rem () ml => ∃ st : FullState, rem = c.max_vars - st.core.trail_end ∧
              Fid12PurgeStateOk c F0 F_cur s st ∧
              (s.core.oom = 0#64 → st.core.oom = 0#64) ∧
              (0 < st.core.cur_level → FullDenseWatchSpecs.FullReasonsMarked st) ∧
              (FullMem c st ⋆ R) ml) ?_ ?_
          · rintro L rem ⟨⟩ ml ih ⟨st, rfl, hok_st, hoom_st, hrm_st, hm_st⟩
            dsimp only [Blocks.get]
            refine wp_jnz_of (fun _ => ?_) (fun hc => by cases hc)
            c0_call hSweep
            refine ⟨c, F0, F_cur, st, R, rfl, hok_st.1.1.lengths, hok_st.2.1,
              hok_st.1.2.2.1, hok_st.1.2.2.2.2,
              fun hpos => fun idx hidx hp hg => hrm_st hpos idx hidx hp hg, hm_st,
              fun sr vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena'
                alen' wlen' wu' fred' ni' nr' nb' oom' sc' mA
                hlenA hdomA hextA hws2A hllA hwA hndA hoomA hposA hsr1 hsr2 hsr3 hmA => ?_⟩
            obtain ⟨sA, hokA, hclA_eq, hteA, hoomA', hmA'⟩ :
                ∃ sA : FullState, Fid12PurgeStateOk c F0 F_cur s sA ∧
                  sA.core.cur_level = st.core.cur_level ∧ sA.core.trail_end = te' ∧
                  (sr = 0#64 ∨ sr = 1#64 → sA.core.oom = 0#64) ∧ (FullMem c sA ⋆ R) mA :=
              ⟨_, fid12_purgeStateOk_arena_sweep hok_st hlenA hwA hndA hllA hextA hws2A
                (fun hpos => by
                  obtain ⟨_, _, hv, hl, ht, htp, hte⟩ := hposA hpos
                  exact ⟨hv, hl, ht, htp, hte⟩),
                rfl, rfl, hoomA, hmA⟩
            clear hmA vals' flags' lvl' rsns' trl' tp' unass' unfl' wvec' wstk' arena' alen'
              wlen' wu' fred' ni' nr' nb' oom' sc' hlenA hwA hndA hllA hextA hws2A hoomA
              hposA hsr3
            fr_steps
            · exact hret 20#64 sA mA hokA (Or.inr (Or.inr rfl)) (fun _ => (hsr2 hc).2)
                (fun h => by cases h) hmA'
            · exact hret 0#64 sA mA hokA (Or.inl rfl) (fun h => by cases h)
                (fun h => by cases h) hmA'
            · exact hJbrk () mA ⟨sA, hokA, fun _ => hoomA' (Or.inl hc), hmA'⟩
            · have hsr_eq1 : sr = 1#64 := by
                rcases hdomA with rfl | rfl | rfl | rfl <;> first | rfl | contradiction
              obtain ⟨hcl0, hst_te_lt⟩ := hsr1 hsr_eq1
              have hoomA0 : sA.core.oom = 0#64 := hoomA' (Or.inr hsr_eq1)
              have hclA0 : sA.core.cur_level = 0 := by omega
              c0_call hProp
              refine ⟨c, F0, F_cur, sA, R, rfl, hokA.1.1.lengths, hokA.2.1, hokA.1.2.2.2.2, hmA',
                fun pr valsB flagsB lvlB rsnsB trlB tpB teB propB unassB unflB wvecB arenaB
                  wstkB wlenB wuB fuelB ctypeB crefB c0B c1B oomB ticksB wsortB phasesB
                  delayedB mB hlenB hwB hteB hpermB hfuelB hdomB hpr0 hpr1 hpr2 hidleB hmB => ?_⟩
              have hndB : FullArenaVarsNodup
                  { sA with
                    core := { sA.core with
                      vals := valsB, flags := flagsB, lvl := lvlB, rsns := rsnsB, trl := trlB,
                      trail_pos := tpB, trail_end := teB, propagated := propB, unassigned := unassB,
                      unflushed := unflB, wvec := wvecB, arena := arenaB, wstk := wstkB,
                      wlen := wlenB, wusable := wuB, fuel := fuelB, confl_type := ctypeB,
                      confl_ref := crefB, confl_lit0 := c0B, confl_lit1 := c1B, oom := oomB }
                    scratch := { sA.scratch with
                      search_ticks := ticksB, wsort := wsortB, phases := phasesB,
                      delayed := delayedB } } := by
                intro ref href hng
                have href0 : ref ∈ fullArenaClauseRefsCore sA.core := hpermB.2.1 ▸ href
                obtain ⟨_, hgb, hp⟩ := hpermB.2.2 ref href0
                exact (hp.map (· / 2)).nodup_iff.mpr (hokA.1.2.2.1 ref href0 (hgb.symm.trans hng))
              obtain ⟨sB, hokB, hteB_eq, hclB0, hoomB', hconflB', hmB'⟩ :
                  ∃ sB : FullState, Fid12PurgeStateOk c F0 F_cur s sB ∧
                    sB.core.trail_end = teB ∧ sB.core.cur_level = 0 ∧
                    (pr = 0#64 → sB.core.oom = 0#64) ∧ (pr = 1#64 → F0.Unsat) ∧
                    (FullMem c sB ⋆ R) mB := by
                refine ⟨_, fid12_purgeStateOk_propagate0 hokA hclA0 hlenB hwB hndB
                  (fun ref href => by
                    change ref ∈ fullArenaClauseRefsCore _; rw [hpermB.2.1]; exact href)
                  rfl rfl rfl hfuelB, rfl, hclA0, fun h0 => (hpr0 h0).2.1 hoomA0, ?_, hmB⟩
                intro h1
                refine FullDenseWatchHelpers.fullConflictInv_level0_unsat hwB hclA0 ?_
                rcases (hpr1 h1).2.2 with ⟨ht, h0, h1', hf0, hf1, hent⟩ | hlg
                · exact Or.inl ⟨ht, h0, h1', hent, hf0, hf1⟩
                · exact Or.inr hlg
              have hteA_le_B : te' ≤ teB := by rw [← hteA]; exact hteB.1
              clear hmB hteB valsB flagsB lvlB rsnsB trlB tpB propB unassB unflB wvecB arenaB
                wstkB wlenB wuB fuelB ctypeB crefB c0B c1B oomB ticksB wsortB phasesB delayedB
                hlenB hwB hndB hpermB hfuelB hdomB hpr0 hpr1 hpr2 hidleB
              fr_steps
              · exact hret 20#64 sB mB hokB (Or.inr (Or.inr rfl))
                  (fun _ => hconflB' hc) (fun h => by cases h) hmB'
              · exact hret 0#64 sB mB hokB (Or.inl rfl) (fun h => by cases h)
                  (fun h => by cases h) hmB'
              · have hte_bd : sB.core.trail_end ≤ c.max_vars :=
                  Nat.le_trans hokB.1.1.lengths.core_ok.trail_end_le
                    hokB.1.1.lengths.core_ok.cur_vars_le
                exact ih (c.max_vars - sB.core.trail_end) () _ (by omega)
                  ⟨{ sB with core := { sB.core with unflushed := 0#64 } }, rfl,
                    fid12_purgeStateOk_with_unflushed hokB 0#64, fun _ => hoomB' hc,
                    fun hpos => by change 0 < sB.core.cur_level at hpos; omega, hm⟩
          · intro L hL; fr_steps
            exact hL (c.max_vars - s4.core.trail_end) () m4
              ⟨s4, rfl, hok4, hoom4, fun _ => hrm4, hm4⟩)
    · intro J4 hJ4
      fr_to_group
      refine wp_loop_inv
        (fun (p, ()) mL =>
          p.toNat ≤ s3.core.arena_len ∧
          (p.toNat = s3.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s3) ∧
          ∃ sL : FullState,
            sL.core.arena_len = s3.core.arena_len ∧
            Fid12PurgeStateOk c F0 F_cur s sL ∧ (s.core.oom = 0#64 → sL.core.oom = 0#64) ∧
            FullDenseWatchSpecs.FullReasonsMarked sL ∧
            fullArenaClauseRefs sL = fullArenaClauseRefs s3 ∧ (FullMem c sL ⋆ R) mL)
        (fun (p, ()) _ => s3.core.arena_len - p.toNat)
        (fun JL hLoopL => by
          fr_to_group
          refine hLoopL (0#64, ()) m3 ⟨Nat.zero_le _, ?_, s3, rfl,
            hok3, hoom3, hrm3', rfl, hm3'⟩
          by_cases hz : s3.core.arena_len = 0
          · exact Or.inl hz.symm
          · exact Or.inr (FullDenseWatchHelpers.fullArenaClauseRefs_zero_mem hok3.2.1.arena
              (Nat.pos_of_ne_zero hz)))
        (fun JL (p, ()) mL ⟨hp_le, hp_mem, sL, halenL, hokL, hoomL, hrmL, hrefsL, hmL⟩ hLoopL => ?_)
      have hlenL := hokL.1.1.lengths
      have halL := hlenL.core_ok.arena_len_le
      have haarL := hlenL.core_ok.arena_len_arr
      fr_to_group
      · have hp_lt : p.toNat < sL.core.arena_len := by c0_bound
        have hp_in : p.toNat ∈ fullArenaClauseRefs sL := by
          rw [hrefsL]; exact hp_mem.resolve_left (by omega)
        have hp_wf := hokL.2.1.arena.refs_wf p.toNat hp_in
        have hp_lt32 : p.toNat < 2 ^ 32 := by omega
        have hp_trunc : (p.setWidth 32).toNat = p.toNat := by
          rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt hp_lt32
        have hnb := fullArenaNextOff_bounds (ar := sL.core.arena) (alen := sL.core.arena_len)
          (cref := p.toNat) hp_wf.1
        have hnxt_mem := FullDenseWatchHelpers.fullArenaClauseRefs_next_mem hokL.2.1.arena hp_in
        let n32 :=
          BitVec.ofNat 32 (fullArenaNextOff sL.core.arena sL.core.arena_len (p.setWidth 32).toNat)
        have hn_eq : (n32.setWidth 64).toNat =
            fullArenaNextOff sL.core.arena sL.core.arena_len p.toNat := by
          dsimp only [n32]; rw [hp_trunc, BitVec.toNat_setWidth, bv32_ofNat_toNat (by omega)]
          exact Nat.mod_eq_of_lt (by omega)
        fr_to_group; c0_call hArenaNext
        refine ⟨c, sL, R, rfl, hlenL, hmL, ?_⟩
        fr_to_group
        refine wp_join_group
          (fun _ mM =>
            ∃ sM : FullState,
              sM.core.arena_len = s3.core.arena_len ∧
              Fid12PurgeStateOk c F0 F_cur s sM ∧ (s.core.oom = 0#64 → sM.core.oom = 0#64) ∧
              FullDenseWatchSpecs.FullReasonsMarked sM ∧
              fullArenaClauseRefs sM = fullArenaClauseRefs s3 ∧ (FullMem c sM ⋆ R) mM)
          (fun _ _ mM ⟨sM, halenM, hokM, hoomM, hrmM, hrefsM, hmM⟩ => by
            fr_to_group
            · exfalso
              have hle_np : (n32.setWidth 64).toNat ≤ p.toNat := by c0_bound
              omega
            · fr_steps
              exact hLoopL (n32.setWidth 64, ()) mM (by dsimp only; rw [hn_eq]; omega)
                ⟨by rw [hn_eq]; omega,
                  by rw [hn_eq]
                     rcases hnxt_mem with hend | hmem
                     · exact Or.inl (hend.trans halenL)
                     · exact Or.inr (hrefsL ▸ hmem),
                  sM, halenM, hokM, hoomM, hrmM, hrefsM, hmM⟩)
          (fun JM hJM => ?_)
        fr_to_group
        · have hp3_le : p.toNat + 3 ≤ sL.core.arena_len := hp_wf.1
          have hmask :
              (sL.core.arena[p.toNat]'(by omega) &&& (0x00080000#32 ||| 0x00200000#32)) = 0#32 := by
            simpa [bv_c0] using hc
          have hmask2 : (sL.core.arena[p.toNat]'(by omega) &&& 0x00280000#32) = 0#32 := by
            simpa [show (0x00080000#32 ||| 0x00200000#32) = 0x00280000#32 by decide] using hmask
          have hp_ar : p.toNat < sL.core.arena.length := by omega
          have hp2_ar : p.toNat + 2 < sL.core.arena.length := by omega
          have hp2_eq : (p + 2#64).toNat = p.toNat + 2 := by
            rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl,
              Nat.mod_eq_of_lt (by omega)]
          have hp2_ar64 : (p + 2#64).toNat < sL.core.arena.length := by rw [hp2_eq]; exact hp2_ar
          have hhdr_eq : sL.core.arena[p.toNat]'(by omega) = fullArenaHdr sL p.toNat := by
            unfold fullArenaHdr fullArenaHdrCore
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have hnorsn : (fullArenaHdr sL p.toNat &&& 0x00200000#32) = 0#32 := by
            rw [← hhdr_eq]; exact fid12_purge_bv32_norsn_of_mask hmask2
          fr_steps
          let agN := sL.core.arena_garbage + 3#64 +
            ((sL.core.arena.set p.toNat
              (sL.core.arena[p.toNat]'hp_ar ||| 0x00080000#32))[p.toNat + 2]'(by
                simp [hp2_ar])).setWidth 64
          obtain ⟨hokM, hrmM, hrefsM⟩ :=
            fid12_purgeStateOk_mark_garb (agN := agN) hokL hrmL hp_in hnorsn hp_ar
          let sM : FullState :=
            { sL with core := { sL.core with
              arena := sL.core.arena.set p.toNat (sL.core.arena[p.toNat]'hp_ar ||| 0x00080000#32)
              arena_garbage := agN } }
          exact hJM () m ⟨sM, halenL, hokM, hoomL, hrmM, hrefsM.trans hrefsL, by
            refine cast (congrArg (fun st' => (FullMem c st' ⋆ R) m) ?_) hm
            dsimp only [sM, agN]
            have h5 : (524288 : BitVec 32) = 0x00080000#32 := rfl
            have h3 : (3 : BitVec 64) = 3#64 := rfl
            have h2 : (p + (2 : BitVec 64)).toNat = p.toNat + 2 := hp2_eq
            simp only [h5, h3]
            congr 2; congr 1
            simp only [h2]⟩
        all_goals exact hJM () mL ⟨sL, halenL, hokL, hoomL, hrmL, hrefsL, hmL⟩
      · exact hJ4 (p, ()) mL ⟨sL, hokL, hoomL, hrmL, hmL⟩
  · intro J1 hJ1
    fr_to_group
    · refine wp_join_group
        (fun _ mB => ∃ sB : FullState, Fid12PurgeStateOk c F0 F_cur s sB ∧ sB.core.cur_level = 0 ∧
          (s.core.oom = 0#64 → sB.core.oom = 0#64) ∧ (FullMem c sB ⋆ R) mB)
        (fun _ _ mB ⟨sB, hokB, hclB, hoomB0, hmB⟩ => by
          clear hc hsp0 hm
          fr_to_group; c0_call hProp
          refine ⟨c, F0, F_cur, sB, R, rfl, hokB.1.1.lengths, hokB.2.1, hokB.1.2.2.2.2, hmB,
            fun pr valsP flagsP lvlP rsnsP trlP tpP teP propP unassP unflP wvecP arenaP wstkP
              wlenP wuP fuelP ctypeP crefP c0P c1P oomP ticksP wsortP phasesP delayedP mP
              hlenP hwP hteP hpermP hfuelP hdomP hpr0 hpr1 hpr2 hidleP hmP => ?_⟩
          have hndP : FullArenaVarsNodup
              { sB with
                core := { sB.core with
                  vals := valsP, flags := flagsP, lvl := lvlP, rsns := rsnsP, trl := trlP,
                  trail_pos := tpP, trail_end := teP, propagated := propP, unassigned := unassP,
                  unflushed := unflP, wvec := wvecP, arena := arenaP, wstk := wstkP,
                  wlen := wlenP, wusable := wuP, fuel := fuelP, confl_type := ctypeP,
                  confl_ref := crefP, confl_lit0 := c0P, confl_lit1 := c1P, oom := oomP }
                scratch := { sB.scratch with
                  search_ticks := ticksP, wsort := wsortP, phases := phasesP,
                  delayed := delayedP } } := by
            intro ref href hng
            have href0 : ref ∈ fullArenaClauseRefsCore sB.core := hpermP.2.1 ▸ href
            obtain ⟨_, hgb, hp⟩ := hpermP.2.2 ref href0
            exact (hp.map (· / 2)).nodup_iff.mpr (hokB.1.2.2.1 ref href0 (hgb.symm.trans hng))
          obtain ⟨sP, hokP, hoomP', hconflP', hmP'⟩ :
              ∃ sP : FullState, Fid12PurgeStateOk c F0 F_cur s sP ∧
                (pr = 0#64 → s.core.oom = 0#64 → sP.core.oom = 0#64) ∧
                (pr = 1#64 → F0.Unsat) ∧ (FullMem c sP ⋆ R) mP := by
            refine ⟨_, fid12_purgeStateOk_propagate0 hokB hclB hlenP hwP hndP
              (fun ref href => by
                change ref ∈ fullArenaClauseRefsCore _; rw [hpermP.2.1]; exact href)
              rfl rfl rfl hfuelP, fun h0 hso => (hpr0 h0).2.1 (hoomB0 hso), ?_, hmP⟩
            intro h1
            refine FullDenseWatchHelpers.fullConflictInv_level0_unsat hwP hclB ?_
            rcases (hpr1 h1).2.2 with ⟨ht, h0, h1', hf0, hf1, hent⟩ | hlg
            · exact Or.inl ⟨ht, h0, h1', hent, hf0, hf1⟩
            · exact Or.inr hlg
          clear hmP hteP valsP flagsP lvlP rsnsP trlP tpP teP propP unassP unflP wvecP arenaP wstkP
            wlenP wuP fuelP ctypeP crefP c0P c1P oomP ticksP wsortP phasesP delayedP
            hlenP hwP hndP hpermP hfuelP hdomP hpr0 hpr1 hpr2 hidleP
          fr_steps
          · exact hret 20#64 sP mP hokP (Or.inr (Or.inr rfl)) (fun _ => hconflP' hc)
              (fun h => by cases h) hmP'
          · exact hret 0#64 sP mP hokP (Or.inl rfl) (fun h => by cases h)
              (fun h => by cases h) hmP'
          · exact hJ1 () _ ⟨{ sP with core := { sP.core with unflushed := 0#64 } },
              fid12_purgeStateOk_with_unflushed hokP 0#64, hoomP' hc, hm⟩)
        (fun JB hJB => by
          fr_to_group
          fr_to_group
          · c0_call hBacktrack
            have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
            have hcl_bd : s.core.cur_level < 2 ^ 64 := by
              have := hw.cur_level_le; have := hlen.core_ok.trail_end_le
              have := hlen.core_ok.cur_vars_le; omega
            refine ⟨c, s, R, rfl, hlen, hcl_bd,
              fun _ => by
                have := hlen.core_ok.trail_end_le
                have := hlen.core_ok.cur_vars_le
                have := hw.cur_level_le
                omega,
              hw.trail_lits_lt, hm,
              fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
                hlen' _ _ hcl' hps _ _ _ hwt _ hm' => ?_⟩
            have hmin : cl' = 0 := hcl'.trans (Nat.min_zero _)
            subst hmin
            fr_steps
            exact hJB () m' ⟨_, fid12_purgeStateOk_backtrack0 hok0 hlen'
              (hwt F0 F_cur hw (Nat.zero_le _)) hps.1.1 hps.1.2 hps.2.2.1, rfl, id, hm'⟩
          · have hcl0 : s.core.cur_level = 0 := by
              have hle := hlen.core_ok.trail_end_le
              have hcv := hlen.core_ok.cur_vars_le
              have hcl := hw.cur_level_le
              c0_bound
            exact hJB () _ ⟨s, hok0, hcl0, id, hm⟩)
    · exact hJ1 () _ ⟨s, hok0, id, hm⟩

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep12

end
