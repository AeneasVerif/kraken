/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5ReduceProbeProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5ReduceProbeProof1b0
public import LeanQbe.T.Examples.Kissat.FullM6CompactFlushProof1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullArena1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Step 13 S5 `full_reduce_m6` Proof (`FullFidelityStep13S5ReduceProbeProof2`)

Proves UNSAT-sound `Func.wp` (`XPost := False`, `<= 100` cols, `0` `@[expose]` on proofs) for
`full_reduce_m6` against:
1. `step13ReduceM6Spec` (`Proof0`, compaction-aware for `S3` callers at `force = false`).
2. `FullM6Orch.m6ReduceSpec` at `force = true` (`full_reduce_m6_force_s5_wp`, for `S2`/`S6a`).
-/

set_option autoImplicit false

local elab "c0_hfast_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

local macro "c0_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Compact
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6CompactFlush
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open FullArenaTactics
open scoped FullArenaTactics FullM6Hdr.M6HdrTactics FullM6ProofUtil.M6ProofUtilTactics

/-! ## 1. Reduction State & Step Helpers -/

private theorem s5_level0_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hl0 : s.core.cur_level = 0)
    (hc : FullConflictOkW F_cur s) : F0.Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨_, href, hng, hfals⟩
  · refine hw.ext_sound.2
      (unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => Or.inr ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h0lt).mp hf0
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h1lt).mp hf1
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
  · refine hw.ext_sound.2 (unsat_of_entails_nil
      (entails_of_mem_or_false (hw.arena.entails _ href hng) fun l hl => Or.inr ?_))
    obtain ⟨i, hi, hieq⟩ :=
      (hw.vals_false_iff l (hw.arena.lits_lt _ href hng l hl)).mp (hfals l hl)
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs

private theorem s5_arenaVarsNodup_perm {s s' : FullState}
    (hap : FullArenaPermEq s.core s'.core) (hnd : FullArenaVarsNodup s) :
    FullArenaVarsNodup s' := by
  intro r hr hgb; change r ∈ fullArenaClauseRefs s' at hr
  have hmem : r ∈ fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs at hr ⊢; rw [hap.2.1] at hr; exact hr
  have hperm := hap.2.2 r hmem; unfold fullArenaClauseGarb at hgb; rw [hperm.2.1] at hgb
  exact (List.Perm.map (fun x => x / 2) hperm.2.2).nodup_iff.mpr (hnd r hmem hgb)

private structure S5RedSt (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (ext : List (BitVec 64))
    (st : FullState) (ml : Mem 64) : Prop where
  inv : FullM6HdrInvW c F0 F_cur ext st
  cl : st.core.cur_level ≤ s.core.cur_level
  fu : st.core.fuel.toNat ≤ s.core.fuel.toNat
  cv : st.core.cur_vars = s.core.cur_vars
  tmp : st.core.tmp = s.core.tmp
  tl : st.core.tmp_len = s.core.tmp_len
  ws2 : st.scratch.work_stk2 = s.scratch.work_stk2
  pos : 0 < st.core.cur_level →
    st.core.cur_level = s.core.cur_level ∧ st.core.vals = s.core.vals ∧
    st.core.lvl = s.core.lvl ∧ st.core.trl = s.core.trl ∧
    st.core.trail_pos = s.core.trail_pos ∧ st.core.trail_end = s.core.trail_end
  mem : (FullM6HdrMem c ext st ⋆ R) ml

private theorem s5RedSt_refl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    S5RedSt c F0 F_cur s R ext s m :=
  ⟨hinv, Nat.le_refl _, Nat.le_refl _, rfl, rfl, rfl, rfl,
    fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, hm⟩

private theorem s5RedSt_with_scratch {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    (hst : S5RedSt c F0 F_cur s R ext st ml) {sc' : FullScratch}
    (hsc : sc'.LengthsOk c) (hll : sc'.last_learned = st.scratch.last_learned)
    (hext : sc'.extend_len = st.scratch.extend_len) (hws2 : sc'.work_stk2 = st.scratch.work_stk2)
    {ml' : Mem 64} (hm' : (FullM6HdrMem c ext { st with scratch := sc' } ⋆ R) ml') :
    S5RedSt c F0 F_cur s R ext { st with scratch := sc' } ml' :=
  have hsp := hst.inv.sparseW
  ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk ⟨⟨hsp.1.core_ok, hsc⟩, hsp.2.1, hsp.2.2.1,
      hsp.2.2.2.1, FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨hll, hext⟩ (fun _ hr => hr),
      hsp.2.2.2.2.2⟩, hst.cl, hst.fu, hst.cv, hst.tmp, hst.tl, hws2.trans hst.ws2, hst.pos, hm'⟩

private theorem s5RedSt_w2a {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st s' : FullState} {R : Mem 64 → Prop} {ext ext' : List (BitVec 64)} {ml ml' : Mem 64}
    (hst : S5RedSt c F0 F_cur s R ext st ml) (hc : s'.core = st.core) (hl : s'.LengthsOk c)
    (hms : M6HdrScratchPres st s') (hext : M6HdrExtOk ext')
    (hm' : (FullM6HdrMem c ext' s' ⋆ R) ml') : S5RedSt c F0 F_cur s R ext' s' ml' := by
  have hsp := hst.inv.sparseW
  have hlm' : FullLitMarksClear c s' :=
    ⟨fun v hv => by rw [hc]; exact hsp.2.2.1.1 v hv, by simpa only [hc] using hsp.2.2.1.2⟩
  have hsp' : FullSparseInvW c F0 F_cur s' :=
    ⟨hl, hc ▸ hsp.2.1, hlm',
      fun r hr hng => by
        change r ∈ fullArenaClauseRefs s' at hr; unfold fullArenaClauseRefs at hr
        unfold fullArenaClauseGarb at hng; unfold fullArenaClauseLits
        rw [hc] at hr hng ⊢; exact hsp.2.2.2.1 r hr hng,
      FullExtScratchOk.of_pres hsp.2.2.2.2.1 hms.extPres
        fun _ hr => by unfold fullArenaClauseRefs at hr ⊢; rwa [hc],
      hc ▸ hsp.2.2.2.2.2⟩
  exact ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hext hsp', hc ▸ hst.cl, hc ▸ hst.fu, hc ▸ hst.cv,
    hc ▸ hst.tmp, hc ▸ hst.tl, hms.ws2.trans hst.ws2,
    fun hpos => by rw [hc] at hpos ⊢; exact hst.pos hpos, hm'⟩

private theorem s5RedSt_with_unflushed {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml ml' : Mem 64}
    (hst : S5RedSt c F0 F_cur s R ext st ml) (u' : BitVec 64)
    (hm' : (FullM6HdrMem c ext { st with core := { st.core with unflushed := u' } } ⋆ R) ml') :
    S5RedSt c F0 F_cur s R ext { st with core := { st.core with unflushed := u' } } ml' :=
  have hsp := hst.inv.sparseW
  ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk
    ⟨⟨{ hsp.1.core_ok with vals_len := hsp.1.core_ok.vals_len }, hsp.1.scratch_ok⟩,
      Full.FullDenseWatchHelpers.fullWitnessInv_with_unflushed hsp.2.1 u', hsp.2.2.1,
      hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩,
    hst.cl, hst.fu, hst.cv, hst.tmp, hst.tl, hst.ws2, hst.pos, hm'⟩

private theorem s5RedSt_mark_reasons {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml ml' : Mem 64}
    {ar' : List (BitVec 32)} (hst : S5RedSt c F0 F_cur s R ext st ml)
    (hlen' : ({ st with core := { st.core with arena := ar' } } : FullState).LengthsOk c)
    (hrefs : fullArenaClauseRefs { st with core := { st.core with arena := ar' } } =
      fullArenaClauseRefs st)
    (hper : ∀ r ∈ fullArenaClauseRefs st,
      fullArenaClauseSize { st with core := { st.core with arena := ar' } } r =
        fullArenaClauseSize st r ∧
      fullArenaClauseGarb { st with core := { st.core with arena := ar' } } r =
        fullArenaClauseGarb st r ∧
      fullArenaClauseLits { st with core := { st.core with arena := ar' } } r =
        fullArenaClauseLits st r)
    (hw' : FullWitnessInv c F0 F_cur { st.core with arena := ar' })
    (hm' : (FullM6HdrMem c ext { st with core := { st.core with arena := ar' } } ⋆ R) ml') :
    S5RedSt c F0 F_cur s R ext { st with core := { st.core with arena := ar' } } ml' :=
  have hsp := hst.inv.sparseW
  ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk ⟨hlen', hw', hsp.2.2.1, fun r hr hng => by
      rw [hrefs] at hr; rw [(hper r hr).2.1] at hng; rw [(hper r hr).2.2]
      exact hsp.2.2.2.1 r hr hng,
      FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ hr => by rwa [hrefs]),
      hsp.2.2.2.2.2⟩, hst.cl, hst.fu, hst.cv, hst.tmp, hst.tl, hst.ws2, hst.pos, hm'⟩

private theorem s5RedSt_backtrack0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    (hst : S5RedSt c F0 F_cur s R ext st ml)
    {vals' : List (BitVec 8)} {lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' : BitVec 64} {sc' : FullScratch} {m' : Mem 64} :
    let sB : FullState :=
      { core := { st.core with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', propagated := prop', cur_level := 0, unassigned := unass' }
        scratch := sc' }
    sB.LengthsOk c → FullWitnessInv c F0 F_cur sB.core →
    sc'.last_learned = st.scratch.last_learned → sc'.extend_len = st.scratch.extend_len →
    sc'.work_stk2 = st.scratch.work_stk2 →
    (FullM6HdrMem c ext sB ⋆ R) m' → S5RedSt c F0 F_cur s R ext sB m' :=
  fun hlen' hw' hll' hext' hws2' hm' => have hsp := hst.inv.sparseW
  ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk ⟨hlen', hw', hsp.2.2.1, hsp.2.2.2.1,
      FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨hll', hext'⟩ (fun _ hr => hr), hsp.2.2.2.2.2⟩,
    Nat.zero_le _, hst.fu, hst.cv, hst.tmp, hst.tl, hws2'.trans hst.ws2,
    (fun h => by cases h), hm'⟩

private theorem s5_call_step13Bcp_red {Γ : Env} {f : Sym} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s st : FullState} {R : Mem 64 → Prop} {ml : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ a m' Q' X', step13BcpM6Spec a m' Q' X' → Γ f [i64] [i64] a m' Q' X')
    (hst : S5RedSt c F0 F_cur s R ext st ml) (hcl0 : st.core.cur_level = 0)
    (hk : ∀ r ext' s' m', S5RedSt c F0 F_cur s R ext' s' m' → s'.core.cur_level = 0 →
      st.core.trail_end ≤ s'.core.trail_end → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → st.core.oom = 0#64 → s'.core.oom = 0#64) →
      (r = 1#64 → F0.Unsat) → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call f (as := [i64]) (bs := [i64]) args k) ml := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  have hsp := hst.inv.sparseW
  refine hΓ _ _ _ X ⟨c, F0, F_cur, ext, st, R, rfl, hst.inv.cfgOk, hst.inv.extOk,
    hsp.1, hsp.2.1, hsp.2.2.2.2.2, hst.mem, ?_⟩
  intro r ext' vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen'
    wu' fuel' ctype' cref' c0' c1' oom' sc' m' s'
    hext' _ hexti' hw' htr hap hps _ _ _ _ hfu hr h0 h1 _ _ hm'
  have hextSt : FullExtScratchPres st s' := ⟨hps.1.1, hps.1.2⟩
  have hsp' : FullSparseInvW c F0 F_cur s' :=
    ⟨hexti', hw', hsp.2.2.1, s5_arenaVarsNodup_perm hap hsp.2.2.2.1,
      FullExtScratchOk.of_pres hsp.2.2.2.2.1 hextSt fun _ hr =>
        by unfold fullArenaClauseRefs at hr ⊢; rwa [hap.2.1],
      hsp.2.2.2.2.2⟩
  have hst' : S5RedSt c F0 F_cur s R ext' s' m' :=
    ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hext' hsp', hst.cl,
      Nat.le_trans hfu hst.fu, hst.cv, hst.tmp, hst.tl, hps.2.2.1.trans hst.ws2,
      fun hpos => by change 0 < st.core.cur_level at hpos; omega, hm'⟩
  exact hk r ext' s' m' hst' hcl0 htr.1 hr (fun h0eq hso => (h0 h0eq).2.1 hso)
    (fun h1eq => s5_level0_unsat hw' hcl0 (h1 h1eq).2.2)

private theorem s5RedSt_arena_sweep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    (hst : S5RedSt c F0 F_cur s R ext st ml)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' wvec' wstk' arena' : List (BitVec 32)}
    {te' alen' wlen' : Nat} {unass' unfl' wu' fred' ni' nr' nb' oom' : BitVec 64}
    {sc' : FullScratch} {m' : Mem 64} :
    let sA : FullState :=
      { core :=
          { st.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
            wvec := wvec', wstk := wstk', arena := arena', arena_len := alen', wlen := wlen',
            wusable := wu', arena_garbage := 0#64, first_reducible := fred', num_irred := ni',
            num_redundant := nr', num_binary := nb', oom := oom' }
        scratch := sc' }
    sA.LengthsOk c → FullWitnessInv c F0 F_cur sA.core → FullArenaVarsNodup sA →
    FullLastLearnedWf sA → sc'.extend_len = st.scratch.extend_len →
    sc'.work_stk2 = st.scratch.work_stk2 →
    (0 < st.core.cur_level → vals' = st.core.vals ∧ lvl' = st.core.lvl ∧ trl' = st.core.trl ∧
      tp' = st.core.trail_pos ∧ te' = st.core.trail_end) →
    (FullM6HdrMem c ext sA ⋆ R) m' → S5RedSt c F0 F_cur s R ext sA m' := by
  intro sA hlenA hwA hndA hllA hextA hws2A hposA hm'
  have hsp := hst.inv.sparseW
  refine ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk
      ⟨hlenA, hwA, hsp.2.2.1, hndA, ⟨hllA, hextA ▸ hsp.2.2.2.2.1.2⟩, hsp.2.2.2.2.2⟩,
    hst.cl, hst.fu, hst.cv, hst.tmp, hst.tl, hws2A.trans hst.ws2, fun hpos => ?_, hm'⟩
  obtain ⟨hv, hl, ht, htp, hte⟩ := hposA hpos
  obtain ⟨hcl, hv0, hl0, ht0, htp0, hte0⟩ := hst.pos hpos
  exact ⟨hcl, hv.trans hv0, hl.trans hl0, ht.trans ht0, htp.trans htp0, hte.trans hte0⟩

private def S5RedRefsOk (s : FullState) (rc : Nat) : Prop :=
  ∀ j < rc,
    let r := (s.scratch.red_refs[j]?.getD 0#32).toNat
    r ∈ fullArenaClauseRefs s ∧ (fullArenaHdr s r &&& 0x00200000#32) = 0#32

private theorem s5RedRefsOk_push {c : FullCfg} {s : FullState} {rc p : Nat}
    (hrr_len : s.scratch.red_refs.length = c.red_cap) (hrc_lt : rc < c.red_cap)
    (hp_lt32 : p < 2 ^ 32) (hp_mem : p ∈ fullArenaClauseRefs s)
    (hp_norsn : (fullArenaHdr s p &&& 0x00200000#32) = 0#32)
    (hprev : S5RedRefsOk s rc) :
    S5RedRefsOk { s with scratch :=
      { s.scratch with red_refs := s.scratch.red_refs.set rc (BitVec.ofNat 32 p) } } (rc + 1) := by
  intro j hj
  by_cases hje : j = rc
  · subst j
    have hget : (s.scratch.red_refs.set rc (BitVec.ofNat 32 p))[rc]? = some (BitVec.ofNat 32 p) :=
      List.getElem?_set_self (by omega)
    simpa [hget, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp_lt32] using And.intro hp_mem hp_norsn
  · have hget : (s.scratch.red_refs.set rc (BitVec.ofNat 32 p))[j]? = s.scratch.red_refs[j]? :=
      List.getElem?_set_ne (Ne.symm hje)
    simpa [hget] using hprev j (by omega)

private theorem s5RedSt_update_used {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml ml' : Mem 64}
    {p rc : Nat} {u : BitVec 32}
    (hst : S5RedSt c F0 F_cur s R ext st ml) (hrmL : FullReasonsMarked st)
    (hrrL : S5RedRefsOk st rc) (hp_in : p ∈ fullArenaClauseRefs st)
    (hp_ar : p < st.core.arena.length)
    (hm' : (FullM6HdrMem c ext
      { core := { st.core with
          arena := st.core.arena.set p
            ((st.core.arena[p]'hp_ar &&& 0x07FFFFFF#32) ||| (u <<< (27 : Nat))) }
        scratch := st.scratch } ⋆ R) ml') :
    let v' := (st.core.arena[p]'hp_ar &&& 0x07FFFFFF#32) ||| (u <<< (27 : Nat))
    let sU : FullState := { st with core := { st.core with arena := st.core.arena.set p v' } }
    S5RedSt c F0 F_cur s R ext sU ml' ∧ FullReasonsMarked sU ∧
    fullArenaClauseRefs sU = fullArenaClauseRefs st ∧ S5RedRefsOk sU rc ∧
    (fullArenaHdr sU p &&& 0x00200000#32) = (st.core.arena[p]'hp_ar &&& 0x00200000#32) := by
  intro v' sU
  have hsp := hst.inv.sparseW
  have hhdr_eq : st.core.arena[p]'hp_ar = fullArenaHdr st p := by
    unfold fullArenaHdr fullArenaHdrCore; rw [List.getElem?_eq_getElem hp_ar, Option.getD_some]
  have hup := Full.FullDenseWatchHelpers.updateUsed_preserves_fullWitnessInv hsp.1 hsp.2.1 hp_in u
  rw [← hhdr_eq] at hup
  obtain ⟨hlenU, hrefsU, hperU, hwU⟩ := hup
  have hndU : FullArenaVarsNodup sU := fun r hr hng => by
    rw [hrefsU] at hr; rw [(hperU r hr).2.1] at hng; rw [(hperU r hr).2.2.1]
    exact hsp.2.2.2.1 r hr hng
  have hspU : FullSparseInvW c F0 F_cur sU :=
    ⟨hlenU, hwU, hsp.2.2.1, hndU, FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨rfl, rfl⟩
      (fun _ hr => by rwa [hrefsU]), hsp.2.2.2.2.2⟩
  have hrmU : FullReasonsMarked sU := fun idx hidx hlp hlg => by
    have hne0 : st.core.rsns[(st.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := fun heq => by rw [heq] at hlg; revert hlg; decide
    have hrs := hsp.2.1.reason_inv idx hidx hne0
    rw [ite_eq_right (fun h => absurd hlg h)] at hrs
    rw [(hperU _ hrs.1).2.2.2]; exact hrmL idx hidx hlp hlg
  have hrrU : S5RedRefsOk sU rc := fun j hj => by
    obtain ⟨hjm, hjr⟩ := hrrL j hj; exact ⟨hrefsU ▸ hjm, (hperU _ hjm).2.2.2.trans hjr⟩
  exact ⟨⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk hspU, hst.cl, hst.fu,
    hst.cv, hst.tmp, hst.tl, hst.ws2, hst.pos, hm'⟩, hrmU, hrefsU, hrrU,
    by rw [(hperU p hp_in).2.2.2, ← hhdr_eq]⟩

private theorem s5RedSt_mark_garb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml ml' : Mem 64}
    {cr rc : Nat} {agN : BitVec 64}
    (hst : S5RedSt c F0 F_cur s R ext st ml) (hrmI : FullReasonsMarked st)
    (hrrI : S5RedRefsOk st rc) (hcr_mem : cr ∈ fullArenaClauseRefs st)
    (hcr_norsn : (fullArenaHdr st cr &&& 0x00200000#32) = 0#32)
    (hcr_ar : cr < st.core.arena.length)
    (hm' : (FullM6HdrMem c ext
      { core := { st.core with
          arena := st.core.arena.set cr (st.core.arena[cr]'hcr_ar ||| 0x00080000#32)
          arena_garbage := agN }
        scratch := st.scratch } ⋆ R) ml') :
    let sN : FullState :=
      { core := { st.core with
          arena := st.core.arena.set cr (st.core.arena[cr]'hcr_ar ||| 0x00080000#32)
          arena_garbage := agN }
        scratch := st.scratch }
    S5RedSt c F0 F_cur s R ext sN ml' ∧ FullReasonsMarked sN ∧
    fullArenaClauseRefs sN = fullArenaClauseRefs st ∧ S5RedRefsOk sN rc := by
  intro sN
  have hsp := hst.inv.sparseW
  have hhdr_eq : st.core.arena[cr]'hcr_ar = fullArenaHdr st cr := by
    unfold fullArenaHdr fullArenaHdrCore; rw [List.getElem?_eq_getElem hcr_ar, Option.getD_some]
  have hnonact := Full.FullDenseWatchHelpers.markGarb_nonact_of_reasonsMarked hsp.2.1 hrmI hcr_norsn
  have hmg := Full.FullDenseWatchHelpers.markGarb_preserves_fullWitnessInv
    hsp.1 hsp.2.1 hcr_mem agN hnonact
  rw [← hhdr_eq] at hmg
  obtain ⟨hlenN, hrefsN, hwN, hrsnN, hndN⟩ := hmg
  have hspN : FullSparseInvW c F0 F_cur sN :=
    ⟨hlenN, hwN, hsp.2.2.1, hndN hsp.2.2.2.1, FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨rfl, rfl⟩
      (fun _ hr => by rwa [hrefsN]), hsp.2.2.2.2.2⟩
  have hrmN : FullReasonsMarked sN := fun idx hidx hlp hlg => by
    have hne0 : st.core.rsns[(st.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := fun heq => by rw [heq] at hlg; revert hlg; decide
    have hrs := hsp.2.1.reason_inv idx hidx hne0
    rw [ite_eq_right (fun h => absurd hlg h)] at hrs
    rw [hrsnN _ hrs.1]; exact hrmI idx hidx hlp hlg
  have hrrN : S5RedRefsOk sN rc := fun j hj => by
    obtain ⟨hjm, hjr⟩ := hrrI j hj; exact ⟨hrefsN ▸ hjm, (hrsnN _ hjm).trans hjr⟩
  exact ⟨⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk hspN, hst.cl, hst.fu,
    hst.cv, hst.tmp, hst.tl, hst.ws2, hst.pos, hm'⟩, hrmN, hrefsN, hrrN⟩

/-! ## 2. Post-Compaction End State & Trailing Watermarks -/

private structure S5RedEndSt (force : Bool) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (c' : FullCfg) (ext' : List (BitVec 64))
    (st : FullState) (ml : Mem 64) (ret : Val i64) : Prop where
  compat : FullCfgCompat c c'
  inv : FullM6HdrInv c' F0 ext' st
  ret_dom : ret = 0#64 ∨ ret = 1#64 ∨ ret = 20#64
  cl1 : ret = 1#64 → st.core.cur_level ≤ s.core.cur_level
  fu : st.core.fuel.toNat ≤ s.core.fuel.toNat
  cv : st.core.cur_vars ≤ s.core.cur_vars
  unsat : ret = 20#64 → F0.Unsat
  force_ok : force = true → c' = c ∧ FullM6HdrInvW c F0 F_cur ext' st ∧
    st.core.cur_level ≤ s.core.cur_level ∧
    st.core.cur_vars = s.core.cur_vars ∧ st.core.tmp = s.core.tmp ∧
    st.core.tmp_len = s.core.tmp_len ∧ st.scratch.work_stk2 = s.scratch.work_stk2 ∧
    (ret = 1#64 → s.core.oom = 0#64 → st.core.oom = 0#64) ∧
    (ret = 1#64 → 0 < st.core.cur_level →
      st.core.cur_level = s.core.cur_level ∧ st.core.vals = s.core.vals ∧
      st.core.lvl = s.core.lvl ∧ st.core.trl = s.core.trl ∧
      st.core.trail_pos = s.core.trail_pos ∧ st.core.trail_end = s.core.trail_end)
  mem : (FullM6HdrMem c' ext' st ⋆ R) ml

private abbrev S5RedPost (force : Bool) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ r c' ext' s' m', FullCfgCompat c c' → FullM6HdrInv c' F0 ext' s' →
    (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → s'.core.cur_vars ≤ s.core.cur_vars →
    s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 20#64 → F0.Unsat) →
    (r = 1#64 → s'.core.cur_level ≤ s.core.cur_level) →
    (force = true → c' = c ∧ FullM6HdrInvW c F0 F_cur ext' s' ∧
      s'.core.cur_level ≤ s.core.cur_level ∧
      s'.core.cur_vars = s.core.cur_vars ∧ s'.core.tmp = s.core.tmp ∧
      s'.core.tmp_len = s.core.tmp_len ∧ s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
      (r = 1#64 → s.core.oom = 0#64 → s'.core.oom = 0#64) ∧
      (r = 1#64 → 0 < s'.core.cur_level →
        s'.core.cur_level = s.core.cur_level ∧ s'.core.vals = s.core.vals ∧
        s'.core.lvl = s.core.lvl ∧ s'.core.trl = s.core.trl ∧
        s'.core.trail_pos = s.core.trail_pos ∧ s'.core.trail_end = s.core.trail_end)) →
    (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m'

private theorem s5RedEndSt_of_redSt {force : Bool} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s st : FullState} {R : Mem 64 → Prop}
    {ext : List (BitVec 64)} {ml : Mem 64} {ret : Val i64}
    (hst : S5RedSt c F0 F_cur s R ext st ml)
    (hdom : ret = 0#64 ∨ ret = 1#64 ∨ ret = 20#64) (hu : ret = 20#64 → F0.Unsat)
    (ho : ret = 1#64 → s.core.oom = 0#64 → st.core.oom = 0#64) :
    S5RedEndSt force c F0 F_cur s R c ext st ml ret :=
  ⟨FullCfgCompat.refl c, hst.inv.toInv, hdom, fun _ => hst.cl, hst.fu,
    hst.cv ▸ Nat.le_refl _, hu,
    fun _ => ⟨rfl, hst.inv, hst.cl, hst.cv, hst.tmp, hst.tl, hst.ws2, ho, fun _ => hst.pos⟩,
    hst.mem⟩

private theorem s5RedEndSt_w2a {force : Bool} {c c' : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s st s' : FullState} {R : Mem 64 → Prop}
    {ext ext' : List (BitVec 64)} {ml ml' : Mem 64} {ret : Val i64}
    (hend : S5RedEndSt force c F0 F_cur s R c' ext st ml ret)
    (hc : s'.core = st.core) (hl : s'.LengthsOk c') (hms : M6HdrScratchPres st s')
    (hext : M6HdrExtOk ext') (hm' : (FullM6HdrMem c' ext' s' ⋆ R) ml') :
    S5RedEndSt force c F0 F_cur s R c' ext' s' ml' ret := by
  have hinv' := fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres hend.inv hl hc hms) hext
  refine ⟨hend.compat, hinv', hend.ret_dom, fun h1 => hc ▸ hend.cl1 h1, hc ▸ hend.fu,
    hc ▸ hend.cv, hend.unsat, fun hf => ?_, hm'⟩
  obtain ⟨hcc, hinvW, hcl, hcv, htmp, htl, hws2, ho, hpos⟩ := hend.force_ok hf
  subst hcc
  have hsp := hinvW.sparseW
  have hsp' : FullSparseInvW c' F0 F_cur s' :=
    fullSparseInvW_of_core_eq hsp hl hc hms.extPres
  exact ⟨rfl, FullM6HdrInvW.mk_inv hinvW.cfgOk hext hsp', hc ▸ hcl, hc ▸ hcv,
    hc ▸ htmp, hc ▸ htl, hms.ws2.trans hws2,
    fun h1 hso => by rw [hc]; exact ho h1 hso,
    fun h1 hgt => by rw [hc] at hgt ⊢; exact hpos h1 hgt⟩

private theorem s5_reduce_ret_wm {Γ : Env} {force : Val .bool} {rret : Val i64}
    {c c' : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {extR : List (BitVec 64)}
    {s sR : FullState} {R : Mem 64 → Prop} {mr : Mem 64} {Q : Post [i64]} {X : XPost}
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hUpdCls : ∀ a m Q X, step13UpdateClassifyM6Spec a m Q X →
      Γ "full_update_classify_fid" [i64] [] a m Q X)
    (hQ : S5RedPost force c F0 F_cur s R Q)
    (hend : S5RedEndSt force c F0 F_cur s R c' extR sR mr rret) :
    wp Γ Q X (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 336, ())) fun p_12 =>
      Expr.load i64 (Arg.var p_12.fst) fun ld =>
        Expr.call (as := [i64, i64, i64]) (bs := []) "m6_hdr_set_watermark"
            (Arg.var c.hdr, Arg.imm 2, Arg.var ld, ()) fun _ =>
          Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 600, ())) fun p_14 =>
            Expr.load i64 (Arg.var p_14.fst) fun ld =>
              Expr.call (as := [i64, i64, i64]) (bs := []) "m6_hdr_set_watermark"
                  (Arg.var c.hdr, Arg.imm 3, Arg.var ld, ()) fun _ =>
                Expr.call (as := [i64]) (bs := []) "full_update_classify_fid"
                    (Arg.var c.hdr, ()) fun _ =>
                  Expr.ret (Arg.var rret, ())) mr := by
  have hhdr : c.hdr = c'.hdr := hend.compat.hdr.symm
  rw [hhdr]
  refine wp_m6Hdr_focus_frame hend.mem fun hmRf => ?_
  c0_hfast_nogrp
  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hSetWm _ _ _ _ h) hend.inv.cfgOk
    hend.inv.extOk hend.inv.sparse.lengths (fullM6HdrMem_unfocus hmRf)
    fun _ extR1 sR1 mR1 hcR1 hlR1 hmsR1 hextR1 _ hmR1 => ?_
  have hend1 := s5RedEndSt_w2a hend hcR1 hlR1 hmsR1 hextR1 hmR1
  refine wp_m6Hdr_focus_frame hend1.mem fun hmR1f => ?_
  c0_hfast_nogrp
  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hSetWm _ _ _ _ h) hend1.inv.cfgOk
    hend1.inv.extOk hend1.inv.sparse.lengths (fullM6HdrMem_unfocus hmR1f)
    fun _ extR2 sR2 mR2 hcR2 hlR2 hmsR2 hextR2 _ hmR2 => ?_
  have hend2 := s5RedEndSt_w2a hend1 hcR2 hlR2 hmsR2 hextR2 hmR2
  c0_hfast_nogrp
  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hUpdCls _ _ _ _ h) hend2.inv.cfgOk
    hend2.inv.extOk hend2.inv.sparse.lengths hend2.mem
    fun _ extR3 sR3 mR3 hcR3 hlR3 hmsR3 hextR3 _ hmR3 => ?_
  have hend3 := s5RedEndSt_w2a hend2 hcR3 hlR3 hmsR3 hextR3 hmR3
  c0_hfast_nogrp
  exact hQ rret c' extR3 sR3 mR3 hend3.compat hend3.inv hend3.ret_dom hend3.cv hend3.fu
    hend3.unsat hend3.cl1 hend3.force_ok hend3.mem

/-! ## 3. Sweep, Mark-Garbage, Collect & Unflushed Helpers -/

private theorem s5_reduce_jt_loop {Γ : Env} {ret : Val i64} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext2 : List (BitVec 64)} {s sT : FullState}
    {R : Mem 64 → Prop} {mT : Mem 64} {Q : Post [i64]} {X : XPost} {Jt : Cont [i64]}
    {e_else : Expr Val Cont [i64]} (hret : ret = 1#64)
    (hProp : ∀ a m Q X, step13BcpM6Spec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hJt : ∀ (xs : Tup Val [i64]) (m : Mem 64), (match xs with
      | (rret, ()) => ∃ extR st,
        S5RedSt c F0 F_cur s R extR st m ∧ (rret = 0#64 ∨ rret = 1#64 ∨ rret = 20#64) ∧
        (rret = 20#64 → F0.Unsat) ∧ (rret = 1#64 → s.core.oom = 0#64 → st.core.oom = 0#64)) →
      Jt xs m)
    (hstT : S5RedSt c F0 F_cur s R ext2 sT mT)
    (hoomT : s.core.oom = 0#64 → sT.core.oom = 0#64) (hrmT : FullReasonsMarked sT) :
    wp Γ Q X (Expr.group (sig := [[]]) (fun L => Blocks.cons (fun _ => Expr.jnz (Arg.imm true)
      (Expr.call (as := [i64]) (bs := [i64]) "full_arena_sweep" (Arg.var c.hdr, ()) fun p =>
        Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p.fst, Arg.imm 2, ())) fun p_1 =>
        Expr.jnz (Arg.var p_1.fst) (Expr.jump Jt (Arg.imm 20, ()))
        (Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p.fst, Arg.imm 3, ())) fun p_2 =>
        Expr.jnz (Arg.var p_2.fst) (Expr.jump Jt (Arg.imm 0, ()))
        (Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p.fst, Arg.imm 0, ())) fun p_3 =>
        Expr.jnz (Arg.var p_3.fst) (Expr.jump Jt (Arg.var ret, ()))
        (Expr.call (as := [i64]) (bs := [i64]) "full_propagate" (Arg.var c.hdr, ()) fun p_4 =>
          Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_4.fst, Arg.imm 1, ())) fun p_5 =>
          Expr.jnz (Arg.var p_5.fst) (Expr.jump Jt (Arg.imm 20, ()))
          (Expr.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl) (Arg.var p_4.fst, Arg.imm 0, ())) fun p_6 =>
          Expr.jnz (Arg.var p_6.fst) (Expr.jump Jt (Arg.imm 0, ()))
          (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun p_7 =>
          Expr.store (t := i64) (Arg.imm 0) (Arg.var p_7.fst) (Expr.jump L.fst ())))))))
      e_else) .nil) (fun L => Expr.jump L.fst ())) mT := by
  refine wp_loop_group (ts := [])
    (fun rem () ml => ∃ extL st,
      rem = c.max_vars - st.core.trail_end ∧
      S5RedSt c F0 F_cur s R extL st ml ∧
      (s.core.oom = 0#64 → st.core.oom = 0#64) ∧
      (0 < st.core.cur_level → FullReasonsMarked st))
    ?_ ?_
  · rintro L rem ⟨⟩ ml ih ⟨extL, st, rfl, hst_st, hoom_st, hrm_st⟩
    refine wp_jnz_of (fun _ => ?_) (fun hc => by cases hc)
    refine wp_m6Hdr_focus_frame hst_st.mem fun hmf => ?_
    c0_call hSweep
    refine ⟨c, F0, F_cur, st, m6ExtMem (m6ExtAddr c.hdr) extL ⋆ R,
      rfl, hst_st.inv.sparseW.1, hst_st.inv.sparseW.2.1,
      hst_st.inv.sparseW.2.2.2.1, hst_st.inv.sparseW.2.2.2.2.2,
      hrm_st, hmf,
      fun sr vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec'
        wstk' arena' alen' wlen' wu' fred' ni' nr' nb' oom' sc' mA
        hlenA hsr_dom hextA hws2A hllA hwA hndA hoomA hposA hsr1 hsr2 _hsr3 hmA => ?_⟩
    have hstA := s5RedSt_arena_sweep hst_st hlenA hwA hndA hllA hextA
      hws2A (fun hpos => by
        obtain ⟨_, _, hv, hl, ht, htp, hte⟩ := hposA hpos
        exact ⟨hv, hl, ht, htp, hte⟩) (fullM6HdrMem_unfocus_full hmA)
    c0_hfast_nogrp
    · exact hJt (20#64, ()) mA ⟨extL, _, hstA, Or.inr (Or.inr rfl),
        fun _ => (hsr2 hc).2, fun h => by cases h⟩
    · exact hJt (0#64, ()) mA ⟨extL, _, hstA, Or.inl rfl,
        (fun h => by cases h), fun h => by cases h⟩
    · simpa only [← hret] using hJt (1#64, ()) mA ⟨extL, _, hstA, Or.inr (Or.inl rfl),
        (fun h => by cases h), fun _ _ => hoomA (Or.inl hc)⟩
    · have hsr_eq1 : sr = 1#64 := by
        rcases hsr_dom with rfl | rfl | rfl | rfl <;> first | rfl | contradiction
      obtain ⟨hcl0, hteA⟩ := hsr1 hsr_eq1
      have hoomA0 : oom' = 0#64 := hoomA (Or.inr hsr_eq1)
      refine s5_call_step13Bcp_red rfl
        (fun _ _ _ _ h => hProp _ _ _ _ h) hstA hcl0
        fun pr extB sB mB hstB _hclB hteB hrB h0B h1B => ?_
      c0_hfast_nogrp
      · exact hJt (20#64, ()) mB ⟨extB, sB, hstB, Or.inr (Or.inr rfl),
          fun _ => h1B hc, fun h => by cases h⟩
      · exact hJt (0#64, ()) mB ⟨extB, sB, hstB, Or.inl rfl,
          (fun h => by cases h), fun h => by cases h⟩
      · refine wp_m6Hdr_focus_frame hstB.mem fun hmBf => ?_
        c0_hfast_nogrp
        have hte_bd : sB.core.trail_end ≤ c.max_vars :=
          Nat.le_trans hstB.inv.sparseW.1.core_ok.trail_end_le
            hstB.inv.sparseW.1.core_ok.cur_vars_le
        dsimp only at hteB
        exact ih (c.max_vars - sB.core.trail_end) () _ (by omega)
          ⟨extB, { sB with core := { sB.core with unflushed := 0#64 } }, rfl,
            s5RedSt_with_unflushed hstB 0#64 (fullM6HdrMem_unfocus (by assumption)),
            fun _ => h0B hc hoomA0,
            fun hpos => by change 0 < sB.core.cur_level at hpos; omega⟩
  · intro L hL
    c0_hfast_nogrp
    exact hL (c.max_vars - sT.core.trail_end) () mT ⟨ext2, sT, rfl, hstT, hoomT, fun _ => hrmT⟩

private theorem s5_reduce_j4_post {Γ : Env} {ret : Val i64} {force do_compact : Val .bool}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext2 : List (BitVec 64)}
    {s s4 : FullState} {R : Mem 64 → Prop} {m4 : Mem 64} {Q : Post [i64]} {X : XPost}
    {Jret : Cont [i64]} (hret : ret = 1#64)
    (hMarkRsn : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hProp : ∀ a m Q X, step13BcpM6Spec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hJret : ∀ (xs : Tup Val [i64]) (m : Mem 64), (match xs with
      | (rret, ()) => ∃ extR sR,
        S5RedSt c F0 F_cur s R extR sR m ∧ (rret = 0#64 ∨ rret = 1#64 ∨ rret = 20#64) ∧
        (rret = 20#64 → F0.Unsat) ∧ (rret = 1#64 → s.core.oom = 0#64 → sR.core.oom = 0#64)) →
      Jret xs m)
    (hst4 : S5RedSt c F0 F_cur s R ext2 s4 m4)
    (hoom4 : s.core.oom = 0#64 → s4.core.oom = 0#64) (hrm4 : FullReasonsMarked s4) :
    wp Γ Q X (Expr.group (sig := [[]]) (fun _Js_1 => Blocks.cons (fun _ =>
      Expr.group (sig := [[i64]])
        (fun _Js_2 => Blocks.cons (fun p => Expr.jump Jret (Arg.var p.fst, ())) Blocks.nil)
        fun Js => Expr.group (sig := [[]]) (fun Js_2 => Blocks.cons (fun _ =>
          Expr.jnz (Arg.imm true)
            (Expr.call (as := [i64]) (bs := [i64]) "full_arena_sweep" (Arg.var c.hdr, ()) fun p =>
              Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p.fst, Arg.imm 2, ()))
                fun p_1 =>
              Expr.jnz (Arg.var p_1.fst) (Expr.jump Js.fst (Arg.imm 20, ()))
              (Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p.fst, Arg.imm 3, ()))
                fun p_2 =>
              Expr.jnz (Arg.var p_2.fst) (Expr.jump Js.fst (Arg.imm 0, ()))
              (Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p.fst, Arg.imm 0, ()))
                fun p =>
              Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.var ret, ()))
              (Expr.call (as := [i64]) (bs := [i64]) "full_propagate" (Arg.var c.hdr, ()) fun p =>
                Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p.fst, Arg.imm 1, ()))
                  fun p_3 =>
                Expr.jnz (Arg.var p_3.fst) (Expr.jump Js.fst (Arg.imm 20, ()))
                (Expr.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl) (Arg.var p.fst, Arg.imm 0, ()))
                  fun p =>
                Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.imm 0, ()))
                (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun p =>
                Expr.store (t := i64) (Arg.imm 0) (Arg.var p.fst) (Expr.jump Js_2.fst ())))))))
            (Expr.jump Js.fst (Arg.var ret, ()))) Blocks.nil)
        fun Js => Expr.jump Js.fst ()) Blocks.nil)
    fun Js_1 => Expr.jnz (Arg.var force) (Expr.jump Js_1.fst ())
      (Expr.jnz (Arg.var do_compact) (Expr.jump Js_1.fst ())
        (Expr.group (sig := [[]]) (fun _Js_2 => Blocks.cons (fun _ =>
          Expr.call (as := [i64, .bool]) (bs := []) "full_mark_reasons"
            (Arg.var c.hdr, Arg.imm false, ()) fun _ =>
          Expr.jump Jret (Arg.var ret, ())) Blocks.nil) fun Jm =>
        Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun p =>
        Expr.load i64 (Arg.var p.fst) fun ld =>
        Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p =>
        Expr.jnz (Arg.var p.fst)
          (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 472, ())) fun p =>
          Expr.load i64 (Arg.var p.fst) fun ld =>
          Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p =>
          Expr.jnz (Arg.var p.fst) (Expr.jump Js_1.fst ())
            (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 160, ())) fun p =>
            Expr.load i64 (Arg.var p.fst) fun ld =>
            Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p =>
            Expr.jnz (Arg.var p.fst) (Expr.jump Js_1.fst ()) (Expr.jump Jm.fst ())))
          (Expr.jump Jm.fst ())))) m4 := by
  refine wp_join_group (fun _ mT => ∃ sT : FullState,
      S5RedSt c F0 F_cur s R ext2 sT mT ∧
      (s.core.oom = 0#64 → sT.core.oom = 0#64) ∧ FullReasonsMarked sT)
    (fun _ _ mT ⟨sT, hstT, hoomT, hrmT⟩ => by
      refine wp_join_group (fun ((rret : Val i64), ()) mt => ∃ extR st,
          S5RedSt c F0 F_cur s R extR st mt ∧
          (rret = 0#64 ∨ rret = 1#64 ∨ rret = 20#64) ∧
          (rret = 20#64 → F0.Unsat) ∧
          (rret = 1#64 → s.core.oom = 0#64 → st.core.oom = 0#64))
        (fun _ (rret, ()) mt h => hJret (rret, ()) mt h)
        (fun Jt hJt => @s5_reduce_jt_loop Γ ret c F0 F_cur ext2 s sT R mT Q X Jt
          (Expr.jump Jt (Arg.var ret, ())) hret hProp hSweep hJt hstT hoomT hrmT))
    (fun JT hJT => by
      refine wp_m6Hdr_focus_frame hst4.mem fun hm4f => ?_
      c0_hfast_nogrp
      · exact hJT () m4 ⟨s4, hst4, hoom4, hrm4⟩
      · exact hJT () m4 ⟨s4, hst4, hoom4, hrm4⟩
      · refine wp_join_group (ts := []) (fun _ mM => mM = m4)
          (fun _ _ mM hmM => by
            subst hmM
            refine wp_m6Hdr_focus_frame hst4.mem fun hm4f' => ?_
            c0_hfast_nogrp
            c0_call hMarkRsn
            refine ⟨c, F0, F_cur, s4, m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R,
              rfl, hst4.inv.sparseW.1, hst4.inv.sparseW.2.1, hm4f',
              fun ar5 m5 hl5 hrefs5 hper5 _ hw5 hm5 => ?_⟩
            c0_hfast_nogrp
            simpa only [← hret] using hJret (1#64, ()) _
              ⟨ext2, _, s5RedSt_mark_reasons hst4 hl5 hrefs5 hper5 hw5
                (fullM6HdrMem_unfocus_full hm5), Or.inr (Or.inl rfl),
                (fun h => absurd h (by decide)), fun _ => hoom4⟩)
          (fun Jm hJm => by
            c0_hfast_nogrp <;> first
              | exact hJT () m4 ⟨s4, hst4, hoom4, hrm4⟩
              | exact hJm () m4 rfl))

private abbrev s5MarkGarbExpr (c : FullCfg) (rc target : Val i64) (J4 : Cont []) :
    Expr Val Cont [i64] :=
  Expr.group (sig := [[i64]]) (fun Js_2 => Blocks.cons (fun p_30 =>
    Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.var p_30.fst, Arg.var target, ())) fun p_31 =>
    Expr.jnz (Arg.var p_31.fst)
      (Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.var p_30.fst, Arg.var rc, ())) fun p_32 =>
      Expr.jnz (Arg.var p_32.fst)
        (Expr.let_ (Op.mk (.mul i64) (Arg.var p_30.fst, Arg.imm 4, ())) fun p_33 =>
        Expr.let_ (Op.mk (.add i64) (Arg.var c.pRedRefs, Arg.var p_33.fst, ())) fun p_34 =>
        Expr.load i32 (Arg.var p_34.fst) fun ld_7 =>
        Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld_7, ())) fun p_35 =>
        Expr.let_ (Op.mk (.mul i64) (Arg.var p_35.fst, Arg.imm 4, ())) fun p_36 =>
        Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p_36.fst, ())) fun p_37 =>
        Expr.load i32 (Arg.var p_37.fst) fun ld_8 =>
        Expr.group (sig := [[]]) (fun _Js => Blocks.cons (fun _p =>
          Expr.let_ (Op.mk (.add i64) (Arg.var p_30.fst, Arg.imm 1, ())) fun p =>
          Expr.jump Js_2.fst (Arg.var p.fst, ())) Blocks.nil) fun Js =>
        Expr.let_ (Op.mk (.and i32) (Arg.var ld_8, Arg.imm 524288, ())) fun p_38 =>
        Expr.let_ (Op.mk (.cmp .eq i32 Ty.bool rfl) (Arg.var p_38.fst, Arg.imm 0, ())) fun p_39 =>
        Expr.jnz (Arg.var p_39.fst)
          (Expr.let_ (Op.mk (.mul i64) (Arg.var p_35.fst, Arg.imm 4, ())) fun p_40 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p_40.fst, ())) fun p_41 =>
          Expr.let_ (Op.mk (.or i32) (Arg.var ld_8, Arg.imm 524288, ())) fun p_42 =>
          Expr.store (t := i32) (Arg.var p_42.fst) (Arg.var p_41.fst)
            (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 472, ())) fun p_43 =>
            Expr.load i64 (Arg.var p_43.fst) fun ld_9 =>
            Expr.let_ (Op.mk (.add i64) (Arg.var ld_9, Arg.imm 3, ())) fun p_44 =>
            Expr.let_ (Op.mk (.add i64) (Arg.var p_35.fst, Arg.imm 2, ())) fun p_45 =>
            Expr.let_ (Op.mk (.mul i64) (Arg.var p_45.fst, Arg.imm 4, ())) fun p_46 =>
            Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p_46.fst, ())) fun p_47 =>
            Expr.load i32 (Arg.var p_47.fst) fun ld =>
            Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun p_48 =>
            Expr.let_ (Op.mk (.add i64) (Arg.var p_44.fst, Arg.var p_48.fst, ())) fun p_49 =>
            Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 472, ())) fun p =>
            Expr.store (t := i64) (Arg.var p_49.fst) (Arg.var p.fst) (Expr.jump Js.fst ())))
          (Expr.jump Js.fst ()))
        (Expr.jump J4 ()))
      (Expr.jump J4 ())) Blocks.nil) (fun Js => Expr.jump Js.fst (Arg.imm 0, ()))

private theorem s5_reduce_mark_garb_loop {Γ : Env} {rc target : Val i64} {c : FullCfg}
    {F0 : CNF Nat} {F_cur : List (List Nat)} {ext2 : List (BitVec 64)} {s sS : FullState}
    {R : Mem 64 → Prop} {mS : Mem 64} {Q : Post [i64]} {X : XPost} {J4 : Cont []}
    (hJ4 : ∀ (xs : Tup Val []) (m : Mem 64), (∃ s4 : FullState,
      S5RedSt c F0 F_cur s R ext2 s4 m ∧ (s.core.oom = 0#64 → s4.core.oom = 0#64) ∧
      FullReasonsMarked s4) → J4 xs m)
    (hstS : S5RedSt c F0 F_cur s R ext2 sS mS)
    (hoomS : s.core.oom = 0#64 → sS.core.oom = 0#64) (hrmS : FullReasonsMarked sS)
    (hrc_le : rc.toNat ≤ c.red_cap) (hrrS : S5RedRefsOk sS rc.toNat) :
    wp Γ Q X (s5MarkGarbExpr c rc target J4) mS := by
  refine wp_loop_inv
    (fun (i, ()) mI => i.toNat ≤ rc.toNat ∧ ∃ sI : FullState,
      S5RedSt c F0 F_cur s R ext2 sI mI ∧ (s.core.oom = 0#64 → sI.core.oom = 0#64) ∧
      FullReasonsMarked sI ∧ S5RedRefsOk sI rc.toNat)
    (fun (i, ()) _ => rc.toNat - i.toNat)
    (fun JI hLoopI => by
      c0_hfast_nogrp
      exact hLoopI (0#64, ()) _ ⟨Nat.zero_le _, sS, hstS, hoomS, hrmS, hrrS⟩)
    (fun JI (i, ()) mI ⟨hi_le, sI, hstI, hoomI, hrmI, hrrI⟩ hLoopI => ?_)
  have hlenI := hstI.inv.sparseW.1
  have hrrlI := hlenI.scratch_ok.red_refs_len
  have halI := hlenI.core_ok.arena_len_le
  have haarI := hlenI.core_ok.arena_len_arr
  refine wp_m6Hdr_focus_frame hstI.mem fun hmIf => ?_
  c0_hfast_nogrp
  · have hi_lt : i.toNat < rc.toNat := by c0_bound
    have hi_rr : i.toNat < sI.scratch.red_refs.length := by omega
    have hcr_ok := hrrI i.toNat hi_lt
    have hcr_get : (sI.scratch.red_refs[i.toNat]'hi_rr).toNat =
        (sI.scratch.red_refs[i.toNat]?.getD 0#32).toNat := by
      rw [List.getElem?_eq_getElem hi_rr, Option.getD_some]
    have hcr_mem : (sI.scratch.red_refs[i.toNat]'hi_rr).toNat ∈ fullArenaClauseRefs sI := by
      rw [hcr_get]; exact hcr_ok.1
    have hcr_norsn : (fullArenaHdr sI
        (sI.scratch.red_refs[i.toNat]'hi_rr).toNat &&& 0x00200000#32) = 0#32 := by
      rw [hcr_get]; exact hcr_ok.2
    have hcr_wf := hstI.inv.sparseW.2.1.arena.refs_wf _ hcr_mem
    have hcr_lt : (sI.scratch.red_refs[i.toNat]'hi_rr).toNat < sI.core.arena.length := by
      have := hcr_wf.1; omega
    have hi1 : (i + 1#64).toNat = i.toNat + 1 := by c0_bound
    have hcr_idx : ((sI.scratch.red_refs[i.toNat]'hi_rr).setWidth 64).toNat =
        (sI.scratch.red_refs[i.toNat]'hi_rr).toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
        (Nat.lt_trans (sI.scratch.red_refs[i.toNat]'hi_rr).isLt (by decide))]
    have hcr_z_lt : ((sI.scratch.red_refs[i.toNat]'hi_rr).setWidth 64).toNat <
        sI.core.arena.length := by rw [hcr_idx]; exact hcr_lt
    c0_hfast_nogrp
    refine wp_join_group (ts := []) (fun _ mN => ∃ sN : FullState,
        S5RedSt c F0 F_cur s R ext2 sN mN ∧ (s.core.oom = 0#64 → sN.core.oom = 0#64) ∧
        FullReasonsMarked sN ∧ S5RedRefsOk sN rc.toNat) ?_ ?_
    · rintro _ _ mN ⟨sN, hstN, hoomN, hrmN, hrrN⟩
      c0_hfast_nogrp
      exact hLoopI (i + 1#64, ()) mN (by dsimp only; omega) ⟨by omega, sN, hstN, hoomN, hrmN, hrrN⟩
    · intro _Js hJs
      c0_hfast_nogrp
      · simp only [hcr_idx] at hc hm
        obtain ⟨hstN, hrmN, _, hrrN⟩ := s5RedSt_mark_garb (agN := _)
          hstI hrmI hrrI hcr_mem hcr_norsn (by omega) (fullM6HdrMem_unfocus hm)
        exact hJs () _ ⟨_, hstN, hoomI, hrmN, hrrN⟩
      · exact hJs () mI ⟨sI, hstI, hoomI, hrmI, hrrI⟩
  · exact hJ4 () mI ⟨sI, hstI, hoomI, hrmI⟩
  · exact hJ4 () mI ⟨sI, hstI, hoomI, hrmI⟩

private theorem s5_reduce_unflushed {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext : List (BitVec 64)} {s s0 : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost} {J1 : Cont [i64]}
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, step13BcpM6Spec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hJ1 : ∀ (xs : Tup Val [i64]) (m : Mem 64), (match xs with
      | (ret, ()) => ∃ ext1 s1,
        S5RedSt c F0 F_cur s R ext1 s1 m ∧ (ret = 0#64 ∨ ret = 1#64 ∨ ret = 20#64) ∧
        (ret = 20#64 → F0.Unsat) ∧ (ret = 1#64 → s.core.oom = 0#64 → s1.core.oom = 0#64)) →
      J1 xs m)
    (hst0 : S5RedSt c F0 F_cur s R ext s0 m) (hlen0 : s0.LengthsOk c)
    (hs0_core : s0.core = s.core) :
    wp Γ Q X (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun p_10 =>
      Expr.load i64 (Arg.var p_10.fst) fun ld =>
      Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p_11 =>
      Expr.jnz (Arg.var p_11.fst)
        (Expr.group (sig := [[]]) (fun _Js_1 => Blocks.cons (fun _p_12 =>
          Expr.call (as := [i64]) (bs := [i64]) "full_propagate" (Arg.var c.hdr, ()) fun p_13 =>
            Expr.group (sig := [[i64]])
              (fun _Js_2 => Blocks.cons (fun p => Expr.jump J1 (Arg.var p.fst, ())) Blocks.nil)
              fun Js =>
            Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_13.fst, Arg.imm 1, ()))
              fun p_14 =>
            Expr.jnz (Arg.var p_14.fst) (Expr.jump Js.fst (Arg.imm 20, ()))
              (Expr.group (sig := [[i64]])
                (fun _Js_2 => Blocks.cons (fun p => Expr.jump Js.fst (Arg.var p.fst, ()))
                  Blocks.nil) fun Js =>
              Expr.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl) (Arg.var p_13.fst, Arg.imm 0, ()))
                fun p_15 =>
              Expr.jnz (Arg.var p_15.fst) (Expr.jump Js.fst (Arg.imm 0, ()))
                (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun p =>
                Expr.store (t := i64) (Arg.imm 0) (Arg.var p.fst)
                  (Expr.jump Js.fst (Arg.imm 1, ())))))
          Blocks.nil) fun Js =>
          Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 160, ())) fun p_12 =>
          Expr.load i64 (Arg.var p_12.fst) fun ld =>
          Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p_13 =>
          Expr.jnz (Arg.var p_13.fst)
            (Expr.call (as := [i64, i64]) (bs := []) "full_backtrack"
              (Arg.var c.hdr, Arg.imm 0, ()) fun _p => Expr.jump Js.fst ())
            (Expr.jump Js.fst ()))
        (Expr.jump J1 (Arg.imm 1, ()))) m := by
  refine wp_m6Hdr_focus_frame hst0.mem fun hm0f => ?_
  c0_hfast_nogrp
  · refine wp_join_group (fun _ mB => ∃ sB : FullState,
        S5RedSt c F0 F_cur s R ext sB mB ∧ sB.core.cur_level = 0 ∧
        (s.core.oom = 0#64 → sB.core.oom = 0#64))
      (fun _ _ mB ⟨sB, hstB, hclB, hoomB⟩ => by
        c0_hfast_nogrp
        refine s5_call_step13Bcp_red rfl (fun _ _ _ _ h => hProp _ _ _ _ h) hstB hclB
          fun pr extP sP mP hstP _hclP _hteP hrP h0P h1P => ?_
        c0_hfast_nogrp
        refine wp_join_group (ts := [i64]) (fun ((ret : Val i64), ()) mJ => ∃ sJ : FullState,
            S5RedSt c F0 F_cur s R extP sJ mJ ∧ (ret = 0#64 ∨ ret = 1#64 ∨ ret = 20#64) ∧
            (ret = 20#64 → F0.Unsat) ∧ (ret = 1#64 → s.core.oom = 0#64 → sJ.core.oom = 0#64))
          ?_ ?_
        · rintro _ ⟨ret, ⟨⟩⟩ mJ ⟨sJ, hstJ, hrJ, huJ, hoJ⟩
          c0_hfast_nogrp; exact hJ1 (ret, ()) mJ ⟨extP, sJ, hstJ, hrJ, huJ, hoJ⟩
        · intro Jp1 hJp1
          c0_hfast_nogrp
          · exact hJp1 (20#64, ()) mP ⟨sP, hstP, Or.inr (Or.inr rfl),
              fun _ => h1P (by assumption), fun h => by cases h⟩
          · refine wp_join_group (ts := [i64]) (fun ((ret : Val i64), ()) mJ => ∃ sJ : FullState,
                S5RedSt c F0 F_cur s R extP sJ mJ ∧
                (ret = 0#64 ∨ ret = 1#64 ∨ ret = 20#64) ∧
                (ret = 20#64 → F0.Unsat) ∧
                (ret = 1#64 → s.core.oom = 0#64 → sJ.core.oom = 0#64)) ?_ ?_
            · rintro _ ⟨ret, ⟨⟩⟩ mJ hJ
              c0_hfast_nogrp; exact hJp1 (ret, ()) mJ hJ
            · intro Jp2 hJp2
              c0_hfast_nogrp
              · exact hJp2 (0#64, ()) mP ⟨sP, hstP, Or.inl rfl,
                  fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
              · refine wp_m6Hdr_focus_frame hstP.mem fun hmPf => ?_
                c0_hfast_nogrp
                exact hJp2 (1#64, ()) _ ⟨_, s5RedSt_with_unflushed hstP 0#64
                    (fullM6HdrMem_unfocus (by assumption)),
                  Or.inr (Or.inl rfl), fun h => absurd h (by decide),
                  fun _ hso => h0P (by assumption) (hoomB hso)⟩)
      (fun JB hJB => by
        c0_hfast_nogrp
        · c0_call hBacktrack
          refine ⟨c, s0, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hlen0,
            by have hmax := c.hmaxv; unfold dimacsBound at hmax
               have := hst0.inv.sparseW.2.1.cur_level_le
               have := hlen0.core_ok.trail_end_le
               have := hlen0.core_ok.cur_vars_le; omega,
            fun _ => by
              have hmax := c.hmaxv; unfold dimacsBound at hmax
              have := hst0.inv.sparseW.2.1.cur_level_le
              have := hlen0.core_ok.trail_end_le
              have := hlen0.core_ok.cur_vars_le; omega,
            hst0.inv.sparseW.2.1.trail_lits_lt, hm0f,
            fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
              hlen' _ _ hcl' _ hsc' _ _ hw' _ hm' => ?_⟩
          have hcl'0 : cl' = 0 := by simpa using hcl'
          subst hcl'0
          obtain ⟨ta', ba', pt', pb', hp', ps', hl', qsi', qss', hsc_eq⟩ := hsc'
          c0_hfast_nogrp
          exact hJB () _
            ⟨_, s5RedSt_backtrack0 hst0 hlen'
              (hw' F0 F_cur hst0.inv.sparseW.2.1 (Nat.zero_le _))
              (by rw [hsc_eq]) (by rw [hsc_eq]) (by rw [hsc_eq])
              (fullM6HdrMem_unfocus_full hm'),
              rfl, fun h => by dsimp only; rwa [hs0_core]⟩
        · have hcl0 : s0.core.cur_level = 0 := by
            have hmax := c.hmaxv; unfold dimacsBound at hmax
            have hle := hlen0.core_ok.trail_end_le
            have hcv := hlen0.core_ok.cur_vars_le
            have hcl := hst0.inv.sparseW.2.1.cur_level_le
            c0_bound
          exact hJB () m ⟨s0, hst0, hcl0, fun h => hs0_core ▸ h⟩)
  · exact hJ1 (1#64, ()) m
      ⟨ext, s0, hst0, Or.inr (Or.inl rfl), fun h => absurd h (by decide),
        fun _ hso => by rwa [hs0_core]⟩

private def S5RedLoopInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s3 : FullState) (R : Mem 64 → Prop) (ext2 : List (BitVec 64))
    (rc : Val i64) (sL : FullState) (mL : Mem 64) : Prop :=
  rc.toNat ≤ c.red_cap ∧ sL.core.arena_len = s3.core.arena_len ∧
  S5RedSt c F0 F_cur s R ext2 sL mL ∧ (s.core.oom = 0#64 → sL.core.oom = 0#64) ∧
  FullReasonsMarked sL ∧ fullArenaClauseRefs sL = fullArenaClauseRefs s3 ∧
  S5RedRefsOk sL rc.toNat ∧ (FullMem c sL ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) mL

private abbrev s5PushRcExpr (c : FullCfg) (rc p : Val i64) (keep : Val .bool)
    (Jrc2 : Cont [i64]) : Expr Val Cont [i64] :=
  Expr.jnz (Arg.var keep) (Expr.jump Jrc2 (Arg.var rc, ()))
    (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 440, ())) fun p_1 =>
      Expr.load i64 (Arg.var p_1.fst) fun ld =>
        Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.var rc, Arg.var ld, ())) fun p_2 =>
          Expr.jnz (Arg.var p_2.fst)
            (Expr.let_ (Op.mk (.mul i64) (Arg.var rc, Arg.imm 4, ())) fun p_3 =>
              Expr.let_ (Op.mk (.add i64) (Arg.var c.pRedRefs, Arg.var p_3.fst, ())) fun p_4 =>
                Expr.let_ (Op.mk (.trunc 64 32) (Arg.var p, ())) fun p_37 =>
                  Expr.store (t := i32) (Arg.var p_37.fst) (Arg.var p_4.fst)
                    (Expr.let_ (Op.mk (.add i64) (Arg.var rc, Arg.imm 1, ())) fun p_5 =>
                      Expr.jump Jrc2 (Arg.var p_5.fst, ())))
            (Expr.jump Jrc2 (Arg.var rc, ())))

private abbrev s5KeepBoolExpr (glue t1 t2 : Val i64) (old_u : Val i32)
    (JK : Cont [.bool]) : Expr Val Cont [i64] :=
  Expr.group (sig := [[]])
    (fun _Js_3 => Blocks.cons (fun _ =>
      Expr.let_ (Op.mk (.cmp .ule i64 Ty.bool rfl) (Arg.var glue, Arg.var t2, ())) fun p_1 =>
        Expr.jnz (Arg.var p_1.fst)
          (Expr.let_ (Op.mk (.cmp .uge i32 Ty.bool rfl) (Arg.var old_u, Arg.imm 30, ())) fun p_2 =>
            Expr.jnz (Arg.var p_2.fst) (Expr.jump JK (Arg.imm true, ()))
              (Expr.jump JK (Arg.imm false, ())))
          (Expr.jump JK (Arg.imm false, ()))) Blocks.nil)
    fun Js_3 =>
      Expr.let_ (Op.mk (.cmp .ule i64 Ty.bool rfl) (Arg.var glue, Arg.var t1, ())) fun p_1 =>
        Expr.jnz (Arg.var p_1.fst)
          (Expr.let_ (Op.mk (.cmp .ugt i32 Ty.bool rfl) (Arg.var old_u, Arg.imm 0, ())) fun p_2 =>
            Expr.jnz (Arg.var p_2.fst) (Expr.jump JK (Arg.imm true, ()))
              (Expr.jump Js_3.fst ()))
          (Expr.jump Js_3.fst ())

private theorem s5_reduce_push_rc {Γ : Env} {rc p : Val i64} {keep : Val .bool}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext2 : List (BitVec 64)}
    {s s3 sU : FullState} {R : Mem 64 → Prop} {mU : Mem 64} {Q : Post [i64]} {X : XPost}
    {Jrc2 : Cont [i64]}
    (hJrc2 : ∀ (xs : Tup Val [i64]) mR,
      (∃ sR, S5RedLoopInv c F0 F_cur s s3 R ext2 xs.1 sR mR) → Jrc2 xs mR)
    (hrc_le : rc.toNat ≤ c.red_cap) (hred_cap : c.red_cap < 2 * 2 ^ 28)
    (hp_lt32 : p.toNat < 2 ^ 32) (hp_trunc : (p.setWidth 32).toNat = p.toNat)
    (hp_inU : p.toNat ∈ fullArenaClauseRefs sU)
    (hno_rsn : (fullArenaHdr sU p.toNat &&& 0x00200000#32) = 0#32)
    (hlenU : sU.LengthsOk c) (halenU : sU.core.arena_len = s3.core.arena_len)
    (hstU : S5RedSt c F0 F_cur s R ext2 sU mU) (hoomU : s.core.oom = 0#64 → sU.core.oom = 0#64)
    (hrmU : FullReasonsMarked sU) (hrefsU : fullArenaClauseRefs sU = fullArenaClauseRefs s3)
    (hrrU : S5RedRefsOk sU rc.toNat)
    (hmU : (FullMem c sU ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) mU) :
    wp Γ Q X (s5PushRcExpr c rc p keep Jrc2) mU := by
  have hrrlU := hlenU.scratch_ok.red_refs_len; dsimp only [s5PushRcExpr]; c0_hfast_nogrp
  · exact hJrc2 (rc, ()) mU ⟨sU, hrc_le, halenU, hstU, hoomU, hrmU, hrefsU, hrrU, hmU⟩
  · have hrc_lt : rc.toNat < c.red_cap := by
      have := BitVec.lt_def.mp (by assumption : rc < BitVec.ofNat 64 c.red_cap)
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this; exact this
    have hrc1 : (rc + 1#64).toNat = rc.toNat + 1 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    c0_hfast_nogrp
    let scU' : FullScratch :=
      { sU.scratch with red_refs := sU.scratch.red_refs.set rc.toNat (p.setWidth 32) }
    let sU' : FullState := { sU with scratch := scU' }
    have hmU' : (FullMem c sU' ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) m := hm
    have hstU' := s5RedSt_with_scratch hstU (sc' := scU')
      { hlenU.scratch_ok with red_refs_len := by simp [scU', hrrlU] }
      rfl rfl rfl (fullM6HdrMem_unfocus hmU')
    have hp_sw : p.setWidth 32 = BitVec.ofNat 32 p.toNat := BitVec.eq_of_toNat_eq
      (by rw [hp_trunc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp_lt32])
    have hrrU' : S5RedRefsOk sU' (rc + 1#64).toNat := by
      dsimp only [sU', scU']; rw [hrc1, hp_sw]
      exact s5RedRefsOk_push hrrlU hrc_lt hp_lt32 hp_inU hno_rsn hrrU
    exact hJrc2 (rc + 1#64, ()) _
      ⟨sU', by dsimp only; omega, halenU, hstU', hoomU, hrmU, hrefsU, hrrU', hmU'⟩
  · exact hJrc2 (rc, ()) mU ⟨sU, hrc_le, halenU, hstU, hoomU, hrmU, hrefsU, hrrU, hmU⟩

private theorem s5_reduce_keep_bool {Γ : Env} {glue t1 t2 : Val i64} {old_u : Val i32}
    {mU : Mem 64} {Q : Post [i64]} {X : XPost} {JK : Cont [.bool]}
    (hJK : ∀ b, JK (b, ()) mU) : wp Γ Q X (s5KeepBoolExpr glue t1 t2 old_u JK) mU := by
  dsimp only [s5KeepBoolExpr]; c0_hfast_nogrp
  refine wp_join_group (fun (_ : Tup Val []) mS => mS = mU)
    (fun _ _ _ hmS => by cases hmS; c0_hfast_nogrp <;> exact hJK _)
    (fun _ hJs => by c0_hfast_nogrp <;> first | exact hJK true | exact hJs () mU rfl)

private theorem s5_reduce_collect_jr {Γ : Env} {hdr : Val i32} {rc p t1 t2 : Val i64}
    {old_u : Val i32} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext2 : List (BitVec 64)} {s s3 sU : FullState} {R : Mem 64 → Prop} {mU : Mem 64}
    {Q : Post [i64]} {X : XPost} {JR : Cont [i64]}
    (hJR : ∀ (xs : Tup Val [i64]) mR,
      (∃ sR, S5RedLoopInv c F0 F_cur s s3 R ext2 xs.1 sR mR) → JR xs mR)
    (hrc_le : rc.toNat ≤ c.red_cap) (hred_cap : c.red_cap < 2 * 2 ^ 28)
    (hp_lt : p.toNat < s3.core.arena_len) (hp_lt32 : p.toNat < 2 ^ 32)
    (hp_trunc : (p.setWidth 32).toNat = p.toNat)
    (hp_mem : p.toNat = s3.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s3)
    (hhdrU : (fullArenaHdr sU p.toNat &&& 0x00200000#32) = (hdr &&& 0x00200000#32))
    (halenU : sU.core.arena_len = s3.core.arena_len)
    (hstU : S5RedSt c F0 F_cur s R ext2 sU mU) (hoomU : s.core.oom = 0#64 → sU.core.oom = 0#64)
    (hrmU : FullReasonsMarked sU) (hrefsU : fullArenaClauseRefs sU = fullArenaClauseRefs s3)
    (hrrU : S5RedRefsOk sU rc.toNat)
    (hmU : (FullMem c sU ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) mU) :
    wp Γ Q X (Expr.let_ (Op.mk (.and i32) (Arg.var hdr, Arg.imm 2097152, ())) fun p_32 =>
      Expr.let_ (Op.mk (.cmp .eq i32 Ty.bool rfl) (Arg.var p_32.fst, Arg.imm 0, ())) fun p_33 =>
        Expr.jnz (Arg.var p_33.fst)
          (Expr.let_ (Op.mk (.and i32) (Arg.var hdr, Arg.imm 524287, ())) fun p_34 =>
            Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_34.fst, ())) fun p_35 =>
              Expr.group (sig := [[.bool]]) (fun _Js_3 => Blocks.cons (fun p_36 =>
                Expr.group (sig := [[i64]]) (fun _Js_4 => Blocks.cons (fun q =>
                  Expr.jump JR (Arg.var q.fst, ())) Blocks.nil)
                  (fun Js => s5PushRcExpr c rc p p_36.fst Js.fst)) Blocks.nil)
                (fun Js => s5KeepBoolExpr p_35.fst t1 t2 old_u Js.fst))
          (Expr.jump JR (Arg.var rc, ()))) mU := by
  have hlenU := hstU.inv.sparseW.1
  c0_hfast_nogrp
  · have hno_rsn : (fullArenaHdr sU p.toNat &&& 0x00200000#32) = 0#32 := hhdrU ▸ hc
    have hp_inU : p.toNat ∈ fullArenaClauseRefs sU :=
      hrefsU ▸ hp_mem.resolve_left (by omega)
    refine wp_join_group (fun (_ : Tup Val [.bool]) mK => mK = mU) (by
      rintro _ ⟨keep, ⟨⟩⟩ mK rfl
      refine wp_join_group
        (fun (rc', ()) mR => ∃ sR, S5RedLoopInv c F0 F_cur s s3 R ext2 rc' sR mR)
        (fun _ (rc', ()) mR hR => by c0_hfast_nogrp; exact hJR (rc', ()) mR hR)
        (fun _ hJrc2 => s5_reduce_push_rc hJrc2 hrc_le hred_cap hp_lt32 hp_trunc hp_inU
          hno_rsn hlenU halenU hstU hoomU hrmU hrefsU hrrU hmU))
      (fun _ hJK => by c0_hfast_nogrp; exact s5_reduce_keep_bool fun b => hJK (b, ()) mU rfl)
  · exact hJR (rc, ()) mU ⟨sU, hrc_le, halenU, hstU, hoomU, hrmU, hrefsU, hrrU, hmU⟩

/-! ## 4. Main `full_reduce_m6` Theorems -/

private theorem full_reduce_m6_s5_core (Γ : Env)
    (hIsqrt : ∀ a m Q X, fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hLog10 : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_log10_u64" [i64] [i64] a m Q X)
    (hSub : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_sub" [i64, i64] [i64] a m Q X)
    (hDiv : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_div" [i64, i64] [i64] a m Q X)
    (hFromU64 : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_from_u64" [i64] [i64] a m Q X)
    (hMul : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_mul" [i64, i64] [i64] a m Q X)
    (hToU64 : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_to_u64" [i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hRecomp : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_recompute_tiers" [i64] [] a m Q X)
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hUpdCls : ∀ a m Q X, step13UpdateClassifyM6Spec a m Q X →
      Γ "full_update_classify_fid" [i64] [] a m Q X)
    (hMarkRsn : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hSortReds : ∀ a m Q X, step13SortRedsSpec a m Q X →
      Γ "full_sort_reds" [i64, i64] [] a m Q X)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, step13BcpM6Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hCompNeed : ∀ a m Q X, fullCompactNeededM6Spec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, step13CompactM6Spec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {force : Bool} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hm0 : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : S5RedPost force c F0 F_cur s R Q) :
    Func.wp Γ FullFidelityStep13S5ReduceProbe.full_reduce_m6_body (c.hdr, force, ()) m Q X := by
  have har_cap : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hred_cap : c.red_cap < 2 * 2 ^ 28 := c.hred
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  unfold Func.wp FullFidelityStep13S5ReduceProbe.full_reduce_m6_body
  have hst_init := s5RedSt_refl hinv hm0
  refine wp_m6Hdr_focus_frame hm0 fun hmf => ?_
  c0_hfast_nogrp; c0_call hIsqrt; intro r_isq hsq1 hsq2 hsq3; clear hsq1 hsq2 hsq3
  dsimp only; c0_hfast_nogrp
  let s0 : FullState := { s with scratch :=
    { s.scratch with
      reductions := s.scratch.reductions + 1#64
      reduce_limit := s.scratch.conflicts + r_isq } }
  have hlen0 : s0.LengthsOk c :=
    ⟨hinv.sparseW.1.core_ok, { hinv.sparseW.1.scratch_ok with
      walk_vals_len := hinv.sparseW.1.scratch_ok.walk_vals_len }⟩
  have hmf0 : (FullMem c s0 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m := by
    simpa only [s0, BitVec.ofNat_eq_ofNat] using hm
  have hst0 : S5RedSt c F0 F_cur s R ext s0 m :=
    s5RedSt_with_scratch hst_init hlen0.scratch_ok rfl rfl rfl (fullM6HdrMem_unfocus hmf0)
  refine wp_join_group (fun ((ret : Val i64), ()) m1 => ∃ ext1 s1,
      S5RedSt c F0 F_cur s R ext1 s1 m1 ∧ (ret = 0#64 ∨ ret = 1#64 ∨ ret = 20#64) ∧
      (ret = 20#64 → F0.Unsat) ∧ (ret = 1#64 → s.core.oom = 0#64 → s1.core.oom = 0#64)) ?_ ?_
  · rintro J1 ⟨ret, ⟨⟩⟩ m1 ⟨ext1, s1, hst1, hr1, hu1, ho1⟩
    c0_hfast_nogrp
    refine wp_join_group (ts := [i64, .bool]) (fun (rret, _dc, ()) mr =>
        ∃ c' extR sR, S5RedEndSt force c F0 F_cur s R c' extR sR mr rret) ?_ ?_
    · rintro _ ⟨rret, _dc, ⟨⟩⟩ mr ⟨c', extR, sR, hendR⟩
      dsimp only [Blocks.get_here]
      exact s5_reduce_ret_wm hSetWm hUpdCls hQ hendR
    · intro Jret hJret
      c0_hfast_nogrp
      · have hc_ret : ret = 1#64 := hc
        have hoom1 : s.core.oom = 0#64 → s1.core.oom = 0#64 := ho1 hc_ret
        refine wp_join_group (ts := [.bool]) (fun ((dc : Val .bool), ()) mdc =>
            mdc = m1 ∧ (dc = true → force = false)) ?_ ?_
        · rintro _ ⟨do_compact, ⟨⟩⟩ mdc ⟨rfl, hdc_f⟩
          c0_hfast_nogrp
          refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hRecomp _ _ _ _ h) hst1.inv.cfgOk
            hst1.inv.extOk hst1.inv.sparseW.1 hst1.mem
            fun _ ext2 s2 m2 hc2 hl2 hms2 hext2 _ hm2 => ?_
          have hst2 := s5RedSt_w2a hst1 hc2 hl2 hms2 hext2 hm2
          have hoom2 : s.core.oom = 0#64 → s2.core.oom = 0#64 := fun h => hc2 ▸ hoom1 h
          c0_hfast_nogrp; c0_call hMarkRsn
          refine ⟨c, F0, F_cur, s2, m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R, rfl,
            hst2.inv.sparseW.1, hst2.inv.sparseW.2.1, fullM6HdrMem_focus_full hst2.mem,
            fun ar3 m3 hl3 hrefs3 hper3 hrm3 hw3 hm3 => ?_⟩
          have hst3 :=
            s5RedSt_mark_reasons hst2 hl3 hrefs3 hper3 hw3 (fullM6HdrMem_unfocus_full hm3)
          let s3 : FullState := { s2 with core := { s2.core with arena := ar3 } }
          have hrm3' : FullReasonsMarked s3 := hrm3 rfl
          have hoom3 : s.core.oom = 0#64 → s3.core.oom = 0#64 := hoom2
          refine wp_m6Hdr_focus_frame hst3.mem fun hm3f => ?_
          c0_hfast_nogrp
          refine wp_loop_inv
            (fun (rc, p, ()) mL => p.toNat ≤ s3.core.arena_len ∧
              (p.toNat = s3.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s3) ∧
              ∃ sL : FullState, S5RedLoopInv c F0 F_cur s s3 R ext2 rc sL mL)
            (fun (_, p, ()) _ => s3.core.arena_len - p.toNat)
            (fun JL hLoopL => by
              c0_hfast_nogrp
              refine hLoopL (0#64, 0#64, ()) m3 ⟨Nat.zero_le _, ?_, s3,
                Nat.zero_le _, rfl, hst3, hoom3, hrm3', rfl, fun _ h => by simp at h, hm3f⟩
              by_cases hz : s3.core.arena_len = 0
              · exact Or.inl hz.symm
              · exact Or.inr (Full.FullDenseWatchHelpers.fullArenaClauseRefs_zero_mem
                  hst3.inv.sparseW.2.1.arena (Nat.pos_of_ne_zero hz)))
            (fun JL (rc, p, ()) mL ⟨hp_le, hp_mem, sL, hL⟩ hLoopL => ?_)
          · have ⟨hrc_le, halenL, hstL, hoomL, hrmL, hrefsL, hrrL, hmL⟩ := hL
            have hlenL := hstL.inv.sparseW.1; have halL := hlenL.core_ok.arena_len_le
            have haarL := hlenL.core_ok.arena_len_arr; have hrrlL := hlenL.scratch_ok.red_refs_len
            c0_hfast_nogrp
            · have hp_lt : p.toNat < sL.core.arena_len := by
                dsimp only [s3] at halenL
                have hmod : s2.core.arena_len % 2 ^ 64 ≤ s2.core.arena_len := Nat.mod_le _ _
                omega
              have hp_in : p.toNat ∈ fullArenaClauseRefs sL := by
                rw [hrefsL]; exact hp_mem.resolve_left (by omega)
              have hp_wf := hstL.inv.sparseW.2.1.arena.refs_wf p.toNat hp_in
              have hp_lt32 : p.toNat < 2 ^ 32 := by omega
              have hp_trunc : (p.setWidth 32).toNat = p.toNat := by
                rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt hp_lt32
              c0_hfast_nogrp
              c0_call hArenaNext
              refine ⟨c, sL, m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R, rfl, hlenL, hmL, ?_⟩
              have hnb := fullArenaNextOff_bounds (ar := sL.core.arena) (alen := sL.core.arena_len)
                (cref := p.toNat) hp_wf.1
              have hnxt_mem :=
                FullDenseWatchHelpers.fullArenaClauseRefs_next_mem hstL.inv.sparseW.2.1.arena hp_in
              have hn_eq : ((BitVec.ofNat 32 (fullArenaNextOff sL.core.arena sL.core.arena_len
                  (p.setWidth 32).toNat)).setWidth 64).toNat =
                  fullArenaNextOff sL.core.arena sL.core.arena_len p.toNat := by
                rw [hp_trunc, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
              refine wp_join_group
                (fun (rc', ()) mN =>
                  ∃ sN : FullState, S5RedLoopInv c F0 F_cur s s3 R ext2 rc' sN mN)
                (fun _ (rc', ()) mN ⟨sN, hN⟩ => by
                  c0_hfast_nogrp
                  refine hLoopL (rc', _, ()) mN (by dsimp only [Arg.val]; rw [hn_eq]; omega)
                    ⟨by dsimp only [Arg.val]; rw [hn_eq]; omega, ?_, sN, hN⟩
                  dsimp only [Arg.val]; rw [hn_eq]; rcases hnxt_mem with hend | hmem
                  · exact Or.inl (hend.trans halenL)
                  · exact Or.inr (hrefsL ▸ hmem))
                (fun JN hJN => ?_)
              c0_hfast_nogrp
              · refine wp_join_group
                  (fun _ mU => ∃ sU : FullState, sU.core.arena_len = s3.core.arena_len ∧
                    S5RedSt c F0 F_cur s R ext2 sU mU ∧ (s.core.oom = 0#64 → sU.core.oom = 0#64) ∧
                    FullReasonsMarked sU ∧ fullArenaClauseRefs sU = fullArenaClauseRefs s3 ∧
                    S5RedRefsOk sU rc.toNat ∧ (fullArenaHdr sU p.toNat &&& 0x00200000#32) =
                      (sL.core.arena[p.toNat]'(by omega) &&& 0x00200000#32) ∧
                    (FullMem c sU ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) mU)
                  (fun _ _ mU ⟨sU, halenU, hstU, hoomU, hrmU, hrefsU, hrrU, hhdrU, hmU⟩ => by
                    c0_hfast_nogrp
                    refine wp_join_group
                      (fun (rc', ()) mR => ∃ sR, S5RedLoopInv c F0 F_cur s s3 R ext2 rc' sR mR)
                      (fun _ (rc', ()) mR hR => by c0_hfast_nogrp; exact hJN (rc', ()) mR hR)
                      (fun _ hJR => s5_reduce_collect_jr hJR hrc_le hred_cap
                        (halenL ▸ hp_lt) hp_lt32 hp_trunc hp_mem (by rw [hhdrU]) halenU hstU
                        hoomU hrmU hrefsU hrrU hmU))
                  (fun JU hJU => by
                    c0_hfast_nogrp
                    · let sU : FullState :=
                        { core := { sL.core with
                            arena := sL.core.arena.set p.toNat
                              ((sL.core.arena[p.toNat]'(by omega) &&& 0x07FFFFFF#32) |||
                                ((((sL.core.arena[p.toNat]'(by omega) >>> (27 : Nat)) &&&
                                  31#32) - 1#32) <<< (27 : Nat))) }
                          scratch := sL.scratch }
                      have hmUf : (FullMem c sU ⋆
                          (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) m := hm
                      obtain ⟨hstU, hrmU, hrefsU, hrrU, hhdrU⟩ := s5RedSt_update_used
                        (u := (((sL.core.arena[p.toNat]'(by omega) >>> (27 : Nat))
                        &&& 31#32) - 1#32)) hstL hrmL hrrL hp_in (by omega)
                        (fullM6HdrMem_unfocus hmUf)
                      exact hJU () m ⟨sU, halenL, hstU, hoomL, hrmU, hrefsU.trans hrefsL, hrrU,
                        hhdrU, hmUf⟩
                    · have hhdr_eq :
                          fullArenaHdr sL p.toNat = sL.core.arena[p.toNat]'(by omega) := by
                        unfold fullArenaHdr fullArenaHdrCore
                        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                      exact hJU () mL ⟨sL, halenL, hstL, hoomL, hrmL, hrefsL, hrrL,
                        by rw [hhdr_eq], hmL⟩)
              all_goals exact hJN (rc, ()) mL ⟨sL, hL⟩
            · refine wp_join_group
                (fun _ m4 => ∃ s4 : FullState, S5RedSt c F0 F_cur s R ext2 s4 m4 ∧
                  (s.core.oom = 0#64 → s4.core.oom = 0#64) ∧ FullReasonsMarked s4)
                (fun _ _ m4 ⟨s4, hst4, hoom4, hrm4⟩ => by
                  refine wp_join_group (ts := [i64]) (fun ((rret : Val i64), ()) m5 => ∃ ext5 s5,
                      S5RedSt c F0 F_cur s R ext5 s5 m5 ∧
                      (rret = 0#64 ∨ rret = 1#64 ∨ rret = 20#64) ∧
                      (rret = 20#64 → F0.Unsat) ∧
                      (rret = 1#64 → s.core.oom = 0#64 → s5.core.oom = 0#64))
                    (fun _ (rret, ()) m5 ⟨ext5, s5, hst5, hr5, hu5, ho5⟩ => by
                      refine wp_join_group (ts := [i64])
                        (fun (rret', ()) mr => ∃ c' extR sR,
                          S5RedEndSt force c F0 F_cur s R c' extR sR mr rret')
                        (fun _ (rret', _) mr hend => by
                          c0_hfast_nogrp
                          exact hJret (rret', _, ()) mr hend)
                        (fun Jc hJc => by
                          c0_hfast_nogrp
                          · have hcf : force = false := hdc_f ‹do_compact = true›
                            c0_call hCompact
                            refine ⟨c, F0, ext5, s5, R, rfl, hst5.inv.toInv, hst5.mem,
                              fun r' c' ext' s' m' hcmp' hinv' hr' hcv' hfu' hu' hcl' hm' => ?_⟩
                            refine wp_join_group (ts := [i64])
                              (fun (rret', ()) mr => ∃ c' extR sR,
                                S5RedEndSt force c F0 F_cur s R c' extR sR mr rret')
                              (fun _ (rret', _) mr hend => by
                                c0_hfast_nogrp; exact hJc (rret', ()) mr hend)
                              (fun Jc1 hJc1 => by
                                c0_hfast_nogrp
                                · exact hJc1 (20#64, ()) m' ⟨c', ext', s', hcmp', hinv',
                                    Or.inr (Or.inr rfl), fun h => absurd h (by decide),
                                    le_trans hfu' hst5.fu, le_trans hcv' (le_of_eq hst5.cv),
                                    fun _ => hu' ‹r' = 20#64›,
                                    fun hf => absurd (hf.symm.trans hcf) (by decide), hm'⟩
                                · refine wp_join_group (ts := [i64])
                                    (fun (rret', ()) mr => ∃ c' extR sR,
                                      S5RedEndSt force c F0 F_cur s R c' extR sR mr rret')
                                    (fun _ (rret', _) mr hend => by
                                      c0_hfast_nogrp; exact hJc1 (rret', ()) mr hend)
                                    (fun Jc2 hJc2 => by
                                      c0_hfast_nogrp
                                      · exact hJc2 (0#64, ()) m' ⟨c', ext', s', hcmp', hinv',
                                          Or.inl rfl, fun h => absurd h (by decide),
                                          le_trans hfu' hst5.fu, le_trans hcv' (le_of_eq hst5.cv),
                                          fun h => absurd h (by decide),
                                          fun hf => absurd (hf.symm.trans hcf) (by decide), hm'⟩
                                      · have hr1' : r' = 1#64 := by
                                          rcases hr' with rfl | rfl | rfl <;>
                                            first | rfl | contradiction
                                        rw [‹rret = 1#64›]
                                        exact hJc2 (1#64, ()) m'
                                          ⟨c', ext', s', hcmp', hinv', Or.inr (Or.inl rfl),
                                            fun _ => by rw [hcl' hr1']; exact Nat.zero_le _,
                                            le_trans hfu' hst5.fu, le_trans hcv' (le_of_eq hst5.cv),
                                            fun h => absurd h (by decide),
                                            fun hf => absurd (hf.symm.trans hcf) (by decide), hm'⟩))
                          · exact hJc (rret, ()) m5
                              ⟨c, ext5, s5, s5RedEndSt_of_redSt hst5 hr5 hu5 ho5⟩
                          · exact hJc (rret, ()) m5
                              ⟨c, ext5, s5, s5RedEndSt_of_redSt hst5 hr5 hu5 ho5⟩))
                    (fun J5 hJ5 =>
                      s5_reduce_j4_post hc_ret hMarkRsn hProp hSweep hJ5 hst4 hoom4 hrm4))
                fun J4 hJ4 => by
                  c0_hfast_nogrp
                  · have hrr_bd : ∀ k < rc.toNat,
                        (sL.scratch.red_refs[k]?.getD 0#32).toNat + 2 < c.arena_cap :=
                      fun k hk => by
                        have hwf := (hstL.inv.sparseW.2.1.arena.refs_wf _ (hrrL k hk).1).1
                        omega
                    c0_call hSortReds
                    refine ⟨c, sL, m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R, rfl, hlenL, hrc_le,
                      hrr_bd, hmL, fun rr' sb' mS hrr_len hsb_len hpermS hmS => ?_⟩
                    let scS : FullScratch :=
                      { sL.scratch with red_refs := rr', scratch_buf := sb' }
                    have hstS := s5RedSt_with_scratch hstL (sc' := scS)
                      { hlenL.scratch_ok with red_refs_len := hrr_len, scratch_buf_len := hsb_len }
                      rfl rfl rfl (fullM6HdrMem_unfocus_full hmS)
                    have hrrS : S5RedRefsOk { sL with scratch := scS } rc.toNat :=
                      fun k hk => by
                        obtain ⟨j, hj, heq⟩ := hpermS k hk
                        change (scS.red_refs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs sL ∧
                          (fullArenaHdr sL (scS.red_refs[k]?.getD 0#32).toNat &&& 0x00200000#32) =
                            0#32
                        rw [heq]; exact hrrL j hj
                    let sS : FullState := { sL with scratch := scS }
                    c0_hfast_nogrp
                    refine wp_join_group (ts := [i64]) (fun (_ : Tup Val [i64]) ma => ma = mS)
                      (fun _ ⟨_arg, ⟨⟩⟩ ma hma => by
                        subst ma; c0_hfast_nogrp; c0_call hLog10; intro lg
                        dsimp only; c0_hfast_nogrp
                        refine wp_join_group (ts := [i64])
                          (fun (_ : Tup Val [i64]) mb => mb = mS)
                          (fun _ ⟨_qv, ⟨⟩⟩ mb hmb => by
                            subst mb
                            c0_hfast_nogrp; c0_call hDiv; intro d1
                            dsimp only; c0_hfast_nogrp; c0_call hSub; intro pct
                            dsimp only; c0_hfast_nogrp; c0_call hDiv; intro frac
                            dsimp only; c0_hfast_nogrp; c0_call hFromU64; intro frc
                            dsimp only; c0_hfast_nogrp; c0_call hMul; intro fprod
                            dsimp only; c0_hfast_nogrp; c0_call hToU64; intro target
                            dsimp only; c0_hfast_nogrp
                            exact s5_reduce_mark_garb_loop (sS := sS) hJ4 hstS hoomL hrmL hrc_le
                              hrrS)
                          (fun Jq hJq => by
                            dsimp only; c0_hfast_nogrp
                            · exact hJq (_, ()) mS rfl
                            · exact hJq (_, ()) mS rfl))
                      (fun Jarg hJarg => by
                        dsimp only; c0_hfast_nogrp <;> exact hJarg (_, ()) mS rfl)
                  · exact hJ4 () mL ⟨sL, hstL, hoomL, hrmL⟩
        · intro Jdc hJdc
          refine wp_m6Hdr_focus_frame hst1.mem fun hm1f => ?_
          c0_hfast_nogrp
          · exact hJdc (false, ()) m1 ⟨rfl, fun h => by cases h⟩
          · c0_call hCompNeed
            have hcl_lt : s1.core.cur_level < 2 ^ 64 :=
              Nat.lt_of_le_of_lt
                (Nat.le_trans hst1.inv.sparseW.2.1.cur_level_le
                  (Nat.le_trans hst1.inv.sparseW.1.core_ok.trail_end_le
                    hst1.inv.sparseW.1.core_ok.cur_vars_le))
                (Nat.lt_trans hmaxv (by decide))
            refine ⟨c, s1, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hst1.inv.sparseW.1,
              hcl_lt, hm1f, fun res hres => ?_⟩
            c0_hfast_nogrp <;> first
              | exact hJdc (true, ()) m1 ⟨rfl, fun _ => ‹force = false›⟩
              | exact hJdc (false, ()) m1 ⟨rfl, fun h => absurd h (by decide)⟩
          · exact hJdc (false, ()) m1 ⟨rfl, fun h => by cases h⟩
      · exact hJret (ret, _, ()) m1 ⟨c, ext1, s1, s5RedEndSt_of_redSt hst1 hr1 hu1 ho1⟩
  · intro J1 hJ1; exact s5_reduce_unflushed hBacktrack hProp hJ1 hst0 hlen0 rfl

theorem full_reduce_m6_s5_wp (Γ : Env)
    (hIsqrt : ∀ a m Q X, fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hLog10 : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_log10_u64" [i64] [i64] a m Q X)
    (hSub : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_sub" [i64, i64] [i64] a m Q X)
    (hDiv : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_div" [i64, i64] [i64] a m Q X)
    (hFromU64 : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_from_u64" [i64] [i64] a m Q X)
    (hMul : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_mul" [i64, i64] [i64] a m Q X)
    (hToU64 : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_to_u64" [i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hRecomp : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_recompute_tiers" [i64] [] a m Q X)
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hUpdCls : ∀ a m Q X, step13UpdateClassifyM6Spec a m Q X →
      Γ "full_update_classify_fid" [i64] [] a m Q X)
    (hMarkRsn : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hSortReds : ∀ a m Q X, step13SortRedsSpec a m Q X →
      Γ "full_sort_reds" [i64, i64] [] a m Q X)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, step13BcpM6Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hCompNeed : ∀ a m Q X, fullCompactNeededM6Spec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, step13CompactM6Spec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X) :
    ∀ a m Q X, step13ReduceM6Spec a m Q X →
      Func.wp Γ FullFidelityStep13S5ReduceProbe.full_reduce_m6_body a m Q X := by
  rintro ⟨h, force, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, ext, s, R, rfl, hinv, hm0, hQ⟩
  exact full_reduce_m6_s5_core Γ hIsqrt hLog10 hSub hDiv hFromU64 hMul hToU64 hArenaNext
    hRecomp hSetWm hUpdCls hMarkRsn hSortReds hBacktrack hProp hSweep hCompNeed hCompact hinv hm0
    fun r c' ext' s' m' hcmp hinv' hr hcv hfu hu hcl hf hm' =>
      hQ r c' ext' s' m' hcmp hinv' hr hcv hfu hu hcl
        (fun hft => let ⟨hc, hinvW, _, hv, htmp, htl, hws2, ho, hp⟩ := hf hft
          ⟨hc, hinvW, hv, htmp, htl, hws2, ho, hp⟩) hm'

theorem full_reduce_m6_force_s5_wp (Γ : Env)
    (hIsqrt : ∀ a m Q X, fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hLog10 : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_log10_u64" [i64] [i64] a m Q X)
    (hSub : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_sub" [i64, i64] [i64] a m Q X)
    (hDiv : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_div" [i64, i64] [i64] a m Q X)
    (hFromU64 : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_from_u64" [i64] [i64] a m Q X)
    (hMul : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_mul" [i64, i64] [i64] a m Q X)
    (hToU64 : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_to_u64" [i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hRecomp : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_recompute_tiers" [i64] [] a m Q X)
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hUpdCls : ∀ a m Q X, step13UpdateClassifyM6Spec a m Q X →
      Γ "full_update_classify_fid" [i64] [] a m Q X)
    (hMarkRsn : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hSortReds : ∀ a m Q X, step13SortRedsSpec a m Q X →
      Γ "full_sort_reds" [i64, i64] [] a m Q X)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, step13BcpM6Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hCompNeed : ∀ a m Q X, fullCompactNeededM6Spec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, step13CompactM6Spec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X) :
    ∀ h m Q X, m6ReduceSpec (h, true, ()) m Q X →
      Func.wp Γ FullFidelityStep13S5ReduceProbe.full_reduce_m6_body (h, true, ()) m Q X := by
  intro h m Q X hs
  rcases m6ReduceSpec_elim hs with ⟨c, F0, F_cur, ext, s, R, rfl, hinv, hm0, hQ⟩
  exact full_reduce_m6_s5_core Γ hIsqrt hLog10 hSub hDiv hFromU64 hMul hToU64 hArenaNext
    hRecomp hSetWm hUpdCls hMarkRsn hSortReds hBacktrack hProp hSweep hCompNeed hCompact hinv hm0
    fun r c' ext' s' m' _ _ hr _ hfu hu _ hf hm' =>
      let ⟨rfl, hinvW, hcl, hv, htmp, htl, hws2, ho, hp⟩ := hf rfl
      hQ r ext' s' m' hinvW hr hcl hfu hv htmp htl hws2 hu ho hp hm'

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S5
