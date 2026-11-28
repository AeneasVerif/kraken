/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Reduce.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Reduce.WpReduceHelpers
public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Shared Reduction State & Sub-Proof Helpers (`Proof.Reduce.WpReduceShared`)

Provides the common invariant state `RedSt` (with `RedRefsOk`), pure transition lemmas,
and shared `Func.wp` call wrappers (`backtrack0`, `propagate0`, `markReasons`, `sweep13`,
`arenaNext`) reused by `WpPurge` and `WpReduce*` with zero legacy imports.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Reduce

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open scoped FullArenaTactics

/-! ## 1. Pure Arena, `FullWitnessInv`, and `RedRefsOk` Helpers -/

@[expose] def RedRefsOk (s : FullState) (rc : Nat) : Prop :=
  ∀ j < rc,
    let r := (s.scratch.red_refs[j]?.getD 0#32).toNat
    r ∈ fullArenaClauseRefs s ∧ (fullArenaHdr s r &&& 0x00200000#32) = 0#32

theorem redRefsOk_push {c : FullCfg} {s : FullState} {rc p : Nat}
    (hrr_len : s.scratch.red_refs.length = c.red_cap) (hrc_lt : rc < c.red_cap)
    (hp_lt32 : p < 2 ^ 32) (hp_mem : p ∈ fullArenaClauseRefs s)
    (hp_norsn : (fullArenaHdr s p &&& 0x00200000#32) = 0#32)
    (hprev : RedRefsOk s rc) :
    RedRefsOk { s with scratch :=
      { s.scratch with red_refs := s.scratch.red_refs.set rc (BitVec.ofNat 32 p) } }
      (rc + 1) := by
  intro j hj
  by_cases hje : j = rc
  · subst j
    have hget :
        (s.scratch.red_refs.set rc (BitVec.ofNat 32 p))[rc]? = some (BitVec.ofNat 32 p) :=
      List.getElem?_set_self (by omega)
    simpa [hget, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp_lt32] using
      And.intro hp_mem hp_norsn
  · have hget : (s.scratch.red_refs.set rc (BitVec.ofNat 32 p))[j]? = s.scratch.red_refs[j]? :=
      List.getElem?_set_ne (Ne.symm hje)
    simpa [hget] using hprev j (by omega)

private theorem fullArenaScanRefs_mem_self {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos : Nat}, alen - pos ≤ fuel → pos + 3 ≤ alen →
      pos ∈ fullArenaScanRefs ar alen pos fuel
  | 0, _, _, _ => by omega
  | _ + 1, _, _, hp => by simp [fullArenaScanRefs, hp]

theorem fullArenaClauseRefs_zero_mem {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (ha : FullArenaClausesInv c F_cur k) (hpos : 0 < k.arena_len) :
    0 ∈ fullArenaClauseRefsCore k := by
  have h3 : 0 + 3 ≤ k.arena_len := by
    rcases ha.len_ok with h0 | hle
    · omega
    · omega
  exact fullArenaScanRefs_mem_self (by omega) h3

private theorem fullArenaScanRefs_next_mem_aux {ar : List (BitVec 32)} {alen : Nat}
    (hchain : ∀ q ∈ fullArenaScanRefs ar alen 0 alen,
      fullArenaNextOff ar alen q = alen ∨ fullArenaNextOff ar alen q + 3 ≤ alen) :
    ∀ {fuel pos r : Nat},
      (∀ q ∈ fullArenaScanRefs ar alen pos fuel,
        fullArenaNextOff ar alen q = alen ∨ fullArenaNextOff ar alen q + 3 ≤ alen) →
      alen - pos ≤ fuel → r ∈ fullArenaScanRefs ar alen pos fuel →
      fullArenaNextOff ar alen r = alen ∨
        fullArenaNextOff ar alen r ∈ fullArenaScanRefs ar alen pos fuel
  | 0, _, _, _, _, hr => by simp [fullArenaScanRefs] at hr
  | fuel + 1, pos, r, hloc, hfl, hr => by
    unfold fullArenaScanRefs at hloc hr ⊢
    split at hr
    · rename_i hpos
      simp only [hpos, ↓reduceIte] at hloc ⊢
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr_tail
      · rcases hloc r List.mem_cons_self with heq | h3
        · exact Or.inl heq
        · right; apply List.mem_cons_of_mem
          have hnb := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := r) hpos
          exact fullArenaScanRefs_mem_self (by omega) h3
      · have hnb := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hpos
        rcases fullArenaScanRefs_next_mem_aux hchain
            (fun q hq => hloc q (List.mem_cons_of_mem _ hq)) (by omega) hr_tail with
          heq | hin
        · exact Or.inl heq
        · exact Or.inr (List.mem_cons_of_mem _ hin)
    · simp at hr

theorem fullArenaClauseRefs_next_mem {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (ha : FullArenaClausesInv c F_cur k) {r : Nat}
    (hr : r ∈ fullArenaClauseRefsCore k) :
    fullArenaNextOff k.arena k.arena_len r = k.arena_len ∨
      fullArenaNextOff k.arena k.arena_len r ∈ fullArenaClauseRefsCore k :=
  fullArenaScanRefs_next_mem_aux
    (fun q hq => (ha.refs_wf q hq).2.2.2.2)
    (fun q hq => (ha.refs_wf q hq).2.2.2.2)
    (Nat.sub_le _ _) hr

private theorem watchSliceOk_with_unflushed {F_cur : List (List Nat)} {k : FullCoreState}
    (u' : BitVec 64) : ∀ {lit p rem : Nat},
    WatchSliceOk F_cur k lit p rem →
    WatchSliceOk F_cur { k with unflushed := u' } lit p rem
  | _, _, _, .empty => .empty
  | _, _, _, .bin h1 h2 h3 h4 h5 hrest =>
    .bin h1 h2 h3 h4 h5 (watchSliceOk_with_unflushed u' hrest)
  | _, _, _, .large h1 h2 h3 h4 h5 hrest =>
    .large h1 h2 h3 h4 h5 (watchSliceOk_with_unflushed u' hrest)

private theorem denseWatchSliceOk_with_unflushed {F_cur : List (List Nat)} {k : FullCoreState}
    (u' : BitVec 64) : ∀ {lit p rem : Nat},
    DenseWatchSliceOk F_cur k lit p rem →
    DenseWatchSliceOk F_cur { k with unflushed := u' } lit p rem
  | _, _, _, .empty => .empty
  | _, _, _, .bin h1 h2 h3 h4 h5 hrest =>
    .bin h1 h2 h3 h4 h5 (denseWatchSliceOk_with_unflushed u' hrest)
  | _, _, _, .occ h1 h2 h3 h4 h5 h6 hrest =>
    .occ h1 h2 h3 h4 h5 h6 (denseWatchSliceOk_with_unflushed u' hrest)

theorem fullWitnessInv_with_unflushed {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (u' : BitVec 64) :
    FullWitnessInv c F0 F_cur { k with unflushed := u' } := by
  have harena : FullArenaClausesInv c F_cur { k with unflushed := u' } :=
    ⟨hw.arena.len_ok, hw.arena.refs_wf, hw.arena.shrk_term, hw.arena.lits_lt, hw.arena.entails⟩
  have hlay : WatchStackLayout { k with unflushed := u' } :=
    ⟨hw.watches.layout.bounds, hw.watches.layout.pos_off, hw.watches.layout.disjoint,
      hw.watches.layout.no_sentinel⟩
  have hwat : ModeWatchesInv F_cur { k with unflushed := u' } := by
    have hmw := hw.watches
    unfold ModeWatchesInv at hmw ⊢
    by_cases hdm : k.dense_mode = 0#64
    · rw [ite_eq_left hdm] at hmw
      rw [ite_eq_left hdm]
      exact ⟨hlay, fun l hl => watchSliceOk_with_unflushed u' (hmw.slices l hl)⟩
    · rw [ite_eq_right hdm] at hmw
      rw [ite_eq_right hdm]
      exact ⟨hlay, fun l hl => denseWatchSliceOk_with_unflushed u' (hmw.slices l hl)⟩
  exact ⟨hw.ext_sound, hw.inconsistent_sound, harena, hwat, hw.cur_level_le,
    hw.trail_lits_lt, hw.trail_vars_nodup, hw.vals_domain, hw.vals_true_iff, hw.vals_false_iff,
    hw.lvl_le, hw.dec_earliest, hw.levels_inhabited, hw.level0_sound, hw.trail_pos_inv,
    hw.level0_rsn_none, hw.frame_trail_lt, hw.frame_trail_mono, hw.frame_trail_before_lt,
    hw.frame_dec_lt, hw.reason_inv, hw.reason_lit_mem⟩

theorem lengthsOk_with_unflushed {c : FullCfg} {s : FullState}
    (hl : s.LengthsOk c) (u' : BitVec 64) :
    ({ s with core := { s.core with unflushed := u' } } : FullState).LengthsOk c :=
  ⟨{ hl.core_ok with vals_len := hl.core_ok.vals_len }, hl.scratch_ok⟩

theorem bv32_norsn_of_and_280000 {x : BitVec 32} (hx : (x &&& 0x00280000#32) = 0#32) :
    (x &&& 0x00200000#32) = 0#32 := by
  have h21 : (x &&& 0x00280000#32)[21] = false := by rw [hx]; decide
  have hb : (0x00280000#32 : BitVec 32)[21] = true := by decide
  simp only [BitVec.getElem_and, hb, Bool.and_true] at h21
  ext i hi
  by_cases hi21 : i = 21
  · subst hi21; simp [h21]
  · have hz : (0x00200000#32 : BitVec 32)[i] = false := by revert i hi hi21; decide
    simp [BitVec.getElem_and, hz]

private theorem bv32_shl27_and_07FFFFFF (y : BitVec 32) :
    (y <<< (27 : Nat)) &&& 0x07FFFFFF#32 = 0#32 := by
  ext i hi
  by_cases hlt : i < 27
  · simp [BitVec.getElem_and, BitVec.getElem_shiftLeft, hlt]
  · have hm0 : (0x07FFFFFF#32 : BitVec 32)[i] = false := by
      revert i hi hlt; decide
    simp [BitVec.getElem_and, hm0]

theorem bv32_mask_bit21_pres {x y : BitVec 32} :
    ((x &&& 0x07FFFFFF#32) ||| (y <<< (27 : Nat))) &&& 0x00200000#32 =
      x &&& 0x00200000#32 := by
  have h_eq : (~~~(0xF8000000#32 : BitVec 32)) = 0x07FFFFFF#32 := by decide
  refine bv32_mask_pres_of_disj (w := x) (m := 0xF8000000#32) (bits := 0x00200000#32)
    (by decide) ?_ |> fun h => by simpa only [h_eq] using h
  simpa only [h_eq] using bv32_shl27_and_07FFFFFF y

theorem bv32_usage_keep_bits {x y : BitVec 32} :
    let w' := (x &&& 0x07FFFFFF#32) ||| (y <<< (27 : Nat))
    w' &&& 524288#32 = x &&& 524288#32 ∧ w' &&& 8388608#32 = x &&& 8388608#32 := by
  have h_eq : (~~~(0xF8000000#32 : BitVec 32)) = 0x07FFFFFF#32 := by decide
  have hu : (y <<< (27 : Nat)) &&& ~~~(0xF8000000#32 : BitVec 32) = 0#32 := by
    simpa only [h_eq] using bv32_shl27_and_07FFFFFF y
  refine ⟨?_, ?_⟩
  · simpa only [h_eq] using bv32_mask_pres_of_disj (w := x) (m := 0xF8000000#32) (by decide) hu
  · simpa only [h_eq] using bv32_mask_pres_of_disj (w := x) (m := 0xF8000000#32) (by decide) hu

theorem fullSparseInvW_with_unflushed {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (u' : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with unflushed := u' } } :=
  ⟨lengthsOk_with_unflushed hsp.1 u', fullWitnessInv_with_unflushed hsp.2.1 u',
    hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

theorem arenaVarsNodup_of_permEq {s s' : FullState}
    (hap : FullArenaPermEq s.core s'.core) (hnd : FullArenaVarsNodup s) :
    FullArenaVarsNodup s' := by
  intro r hr hgb
  change r ∈ fullArenaClauseRefs s' at hr
  have hmem : r ∈ fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs at hr ⊢; rw [hap.2.1] at hr; exact hr
  have hperm := hap.2.2 r hmem
  unfold fullArenaClauseGarb at hgb
  rw [hperm.2.1] at hgb
  exact (List.Perm.map (fun x => x / 2) hperm.2.2).nodup_iff.mpr (hnd r hmem hgb)

theorem lastLearnedWf_of_permEq {s s' : FullState}
    (hap : FullArenaPermEq s.core s'.core) (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hprev : FullLastLearnedWf s) : FullLastLearnedWf s' := fun i hi => by
  change s'.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
    (s'.scratch.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs s'
  rw [hll]
  change _ ∨ _ ∈ fullArenaClauseRefsCore s'.core
  rw [hap.2.1]
  exact hprev i hi

/-! ## 2. Shared Reduction Invariant State `RedSt` & Transitions -/

structure RedSt (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (ext : List (BitVec 64))
    (st : FullState) (ml : Mem 64) : Prop where
  inv : FullM6HdrInvW c F0 F_cur ext st
  cl : st.core.cur_level ≤ s.core.cur_level
  fu : st.core.fuel.toNat ≤ s.core.fuel.toNat
  cv : st.core.cur_vars = s.core.cur_vars
  tmp : st.core.tmp = s.core.tmp
  tl : st.core.tmp_len = s.core.tmp_len
  prb : st.core.probing = s.core.probing
  mcl : st.core.min_clr_len = s.core.min_clr_len
  ws1 : st.scratch.work_stk1 = s.scratch.work_stk1
  ws2 : st.scratch.work_stk2 = s.scratch.work_stk2
  pos : 0 < st.core.cur_level →
    st.core.cur_level = s.core.cur_level ∧ st.core.vals = s.core.vals ∧
    st.core.lvl = s.core.lvl ∧ st.core.trl = s.core.trl ∧
    st.core.trail_pos = s.core.trail_pos ∧ st.core.trail_end = s.core.trail_end
  mem : (FullM6HdrMem c ext st ⋆ R) ml

theorem redSt_refl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    RedSt c F0 F_cur s R ext s m :=
  ⟨hinv, Nat.le_refl _, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, hm⟩

theorem redSt_with_scratch {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml ml' : Mem 64}
    (hst : RedSt c F0 F_cur s R ext st ml) {sc' : FullScratch}
    (hsc : sc'.LengthsOk c) (hll : sc'.last_learned = st.scratch.last_learned)
    (hext : sc'.extend_len = st.scratch.extend_len)
    (hws1 : sc'.work_stk1 = st.scratch.work_stk1) (hws2 : sc'.work_stk2 = st.scratch.work_stk2)
    (hm' : (FullM6HdrMem c ext { st with scratch := sc' } ⋆ R) ml') :
    RedSt c F0 F_cur s R ext { st with scratch := sc' } ml' :=
  have hsp := hst.inv.sparseW
  ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk
      (fullSparseInvW_of_core_eq hsp ⟨hsp.1.core_ok, hsc⟩ rfl ⟨hll, hext⟩),
    hst.cl, hst.fu, hst.cv, hst.tmp, hst.tl, hst.prb, hst.mcl,
    hws1.trans hst.ws1, hws2.trans hst.ws2, hst.pos, hm'⟩

theorem redSt_w2a {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st s' : FullState} {R : Mem 64 → Prop} {ext ext' : List (BitVec 64)} {ml ml' : Mem 64}
    (hst : RedSt c F0 F_cur s R ext st ml) (hc : s'.core = st.core) (hl : s'.LengthsOk c)
    (hms : M6HdrScratchPres st s') (hext : M6HdrExtOk ext')
    (hm' : (FullM6HdrMem c ext' s' ⋆ R) ml') : RedSt c F0 F_cur s R ext' s' ml' :=
  ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hext
      (fullSparseInvW_of_core_eq hst.inv.sparseW hl hc hms.extPres),
    hc ▸ hst.cl, hc ▸ hst.fu, hc ▸ hst.cv, hc ▸ hst.tmp, hc ▸ hst.tl, hc ▸ hst.prb,
    hc ▸ hst.mcl, hms.ws1.trans hst.ws1, hms.ws2.trans hst.ws2,
    fun hpos => by rw [hc] at hpos ⊢; exact hst.pos hpos, hm'⟩

theorem redSt_with_unflushed {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml ml' : Mem 64}
    (hst : RedSt c F0 F_cur s R ext st ml) (u' : BitVec 64)
    (hm' : (FullM6HdrMem c ext { st with core := { st.core with unflushed := u' } } ⋆ R) ml') :
    RedSt c F0 F_cur s R ext { st with core := { st.core with unflushed := u' } } ml' :=
  ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk
      (fullSparseInvW_with_unflushed hst.inv.sparseW u'),
    hst.cl, hst.fu, hst.cv, hst.tmp, hst.tl, hst.prb, hst.mcl, hst.ws1, hst.ws2,
    hst.pos, hm'⟩

theorem redSt_backtrack0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml m' : Mem 64}
    (hst : RedSt c F0 F_cur s R ext st ml)
    {vals' : List (BitVec 8)} {lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' : BitVec 64} {sc' : FullScratch} :
    let sB : FullState :=
      { core := { st.core with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', propagated := prop', cur_level := 0, unassigned := unass' }
        scratch := sc' }
    sB.LengthsOk c → FullWitnessInv c F0 F_cur sB.core →
    sc'.last_learned = st.scratch.last_learned → sc'.extend_len = st.scratch.extend_len →
    sc'.work_stk1 = st.scratch.work_stk1 → sc'.work_stk2 = st.scratch.work_stk2 →
    (FullM6HdrMem c ext sB ⋆ R) m' → RedSt c F0 F_cur s R ext sB m' :=
  fun hlen' hw' hll' hext' hws1' hws2' hm' =>
  have hsp := hst.inv.sparseW
  ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk
      ⟨hlen', hw', hsp.2.2.1, hsp.2.2.2.1,
        FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨hll', hext'⟩ (fun _ hr => hr),
        hsp.2.2.2.2.2⟩,
    Nat.zero_le _, hst.fu, hst.cv, hst.tmp, hst.tl, hst.prb, hst.mcl,
    hws1'.trans hst.ws1, hws2'.trans hst.ws2, (fun h => by cases h), hm'⟩

theorem redSt_mark_reasons {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml ml' : Mem 64}
    {ar' : List (BitVec 32)} (hst : RedSt c F0 F_cur s R ext st ml)
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
    RedSt c F0 F_cur s R ext { st with core := { st.core with arena := ar' } } ml' :=
  have hsp := hst.inv.sparseW
  ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk
      ⟨hlen', hw', hsp.2.2.1,
        fun r hr hng => by
          rw [hrefs] at hr; rw [(hper r hr).2.1] at hng; rw [(hper r hr).2.2]
          exact hsp.2.2.2.1 r hr hng,
        FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ hr => by rwa [hrefs]),
        hsp.2.2.2.2.2⟩,
    hst.cl, hst.fu, hst.cv, hst.tmp, hst.tl, hst.prb, hst.mcl, hst.ws1, hst.ws2,
    hst.pos, hm'⟩

theorem redSt_mark_garb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml ml' : Mem 64}
    {cr rc : Nat} {agN : BitVec 64}
    (hst : RedSt c F0 F_cur s R ext st ml) (hrmI : FullReasonsMarked st)
    (hrrI : RedRefsOk st rc) (hcr_mem : cr ∈ fullArenaClauseRefs st)
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
    RedSt c F0 F_cur s R ext sN ml' ∧ FullReasonsMarked sN ∧
    fullArenaClauseRefs sN = fullArenaClauseRefs st ∧ RedRefsOk sN rc := by
  intro sN
  have hsp := hst.inv.sparseW
  have hhdr_eq : st.core.arena[cr]'hcr_ar = fullArenaHdr st cr := by
    unfold fullArenaHdr fullArenaHdrCore; rw [List.getElem?_eq_getElem hcr_ar, Option.getD_some]
  have hmg := markGarb_sparseInvW hsp hrmI hcr_mem hcr_norsn agN
  rw [← hhdr_eq] at hmg
  have hrefs : fullArenaClauseRefs sN = fullArenaClauseRefs st := by
    have hnon := markGarb_nonact_of_reasonsMarked hsp.2.1 hrmI hcr_norsn
    have hw := markGarb_preserves_witness hsp.1.core_ok hsp.2.1 hcr_mem agN hnon
    simpa only [sN, fullArenaClauseRefs, ← hhdr_eq] using hw.1
  have hspN : FullSparseInvW c F0 F_cur sN := hmg.1
  have hrmN : FullReasonsMarked sN := by simpa only [sN, ← hhdr_eq] using hmg.2
  have hrrN : RedRefsOk sN rc := fun j hj => by
    obtain ⟨hjm, hjr⟩ := hrrI j hj
    refine ⟨hrefs ▸ hjm, ?_⟩
    by_cases heq : cr = (st.scratch.red_refs[j]?.getD 0#32).toNat
    · have hg : (st.core.arena.set cr (st.core.arena[cr]'hcr_ar ||| 0x00080000#32))[
          (st.scratch.red_refs[j]?.getD 0#32).toNat]? =
          some (st.core.arena[cr]'hcr_ar ||| 0x00080000#32) := by
        rw [← heq]; exact List.getElem?_set_self hcr_ar
      rw [← heq] at hjr
      change ((st.core.arena.set cr (st.core.arena[cr]'hcr_ar ||| 0x00080000#32))[
        (st.scratch.red_refs[j]?.getD 0#32).toNat]?.getD 0#32 &&& 0x00200000#32) = 0#32
      rw [hg, Option.getD_some, hhdr_eq]
      exact ((bv32_bit19_or_pres (fullArenaHdr st cr)).2.2.1).trans hjr
    · have hg : (st.core.arena.set cr (st.core.arena[cr]'hcr_ar ||| 0x00080000#32))[
          (st.scratch.red_refs[j]?.getD 0#32).toNat]? =
          st.core.arena[(st.scratch.red_refs[j]?.getD 0#32).toNat]? := List.getElem?_set_ne heq
      change ((st.core.arena.set cr (st.core.arena[cr]'hcr_ar ||| 0x00080000#32))[
        (st.scratch.red_refs[j]?.getD 0#32).toNat]?.getD 0#32 &&& 0x00200000#32) = 0#32
      rw [hg]
      exact hjr
  exact ⟨⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk hspN,
      hst.cl, hst.fu, hst.cv, hst.tmp, hst.tl, hst.prb, hst.mcl, hst.ws1, hst.ws2,
      hst.pos, hm'⟩,
    hrmN, hrefs, hrrN⟩

theorem redSt_update_used {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml ml' : Mem 64}
    {p rc : Nat} {u : BitVec 32}
    (hst : RedSt c F0 F_cur s R ext st ml) (hrmL : FullReasonsMarked st)
    (hrrL : RedRefsOk st rc) (hp_in : p ∈ fullArenaClauseRefs st)
    (hp_ar : p < st.core.arena.length)
    (hm' : (FullM6HdrMem c ext
      { core := { st.core with
          arena := st.core.arena.set p
            ((st.core.arena[p]'hp_ar &&& 0x07FFFFFF#32) ||| (u <<< (27 : Nat))) }
        scratch := st.scratch } ⋆ R) ml') :
    let v' := (st.core.arena[p]'hp_ar &&& 0x07FFFFFF#32) ||| (u <<< (27 : Nat))
    let sU : FullState := { st with core := { st.core with arena := st.core.arena.set p v' } }
    RedSt c F0 F_cur s R ext sU ml' ∧ FullReasonsMarked sU ∧
    fullArenaClauseRefs sU = fullArenaClauseRefs st ∧ RedRefsOk sU rc ∧
    (fullArenaHdr sU p &&& 0x00200000#32) = (st.core.arena[p]'hp_ar &&& 0x00200000#32) := by
  intro v' sU
  have hsp := hst.inv.sparseW
  have hhdr_eq : st.core.arena[p]'hp_ar = fullArenaHdrCore st.core p := by
    unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem hp_ar, Option.getD_some]
  have hbits := bv32_usage_keep_bits (x := st.core.arena[p]'hp_ar) (y := u)
  have h19 : v' &&& 524288#32 = fullArenaHdrCore st.core p &&& 524288#32 := by
    rw [← hhdr_eq]; exact hbits.1
  have h23 : v' &&& 8388608#32 = fullArenaHdrCore st.core p &&& 8388608#32 := by
    rw [← hhdr_eq]; exact hbits.2
  have hpw := setHdrKeep_preserves_witness hsp.1.core_ok hsp.2.1 hp_in v' h19 h23
  have hspU := setHdrKeep_sparseInvW hsp hp_in v' h19 h23
  have hrefs : fullArenaClauseRefs sU = fullArenaClauseRefs st := hpw.1
  have hset_self : (fullArenaHdr sU p &&& 0x00200000#32) =
      (st.core.arena[p]'hp_ar &&& 0x00200000#32) := by
    have hg : (st.core.arena.set p v')[p]? = some v' := List.getElem?_set_self hp_ar
    unfold fullArenaHdr fullArenaHdrCore
    rw [hg, Option.getD_some]
    exact bv32_mask_bit21_pres
  have hbit21_any : ∀ r, (fullArenaHdr sU r &&& 0x00200000#32) =
      (fullArenaHdr st r &&& 0x00200000#32) := fun r => by
    by_cases heq : p = r
    · subst heq; rw [hset_self]; exact congrArg (· &&& 0x00200000#32) hhdr_eq
    · have hg : (st.core.arena.set p v')[r]? = st.core.arena[r]? := List.getElem?_set_ne heq
      unfold fullArenaHdr fullArenaHdrCore
      simp only [sU, hg]
  have hrmU : FullReasonsMarked sU := fun idx hidx hpos hlg => by
    rw [hbit21_any _]; exact hrmL idx hidx hpos hlg
  have hrrU : RedRefsOk sU rc := fun j hj => by
    obtain ⟨hjm, hjr⟩ := hrrL j hj
    exact ⟨hrefs ▸ hjm, (hbit21_any _).trans hjr⟩
  exact ⟨⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk hspU,
      hst.cl, hst.fu, hst.cv, hst.tmp, hst.tl, hst.prb, hst.mcl, hst.ws1, hst.ws2,
      hst.pos, hm'⟩,
    hrmU, hrefs, hrrU, hset_self⟩

theorem redSt_arena_sweep13 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml m' : Mem 64}
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' wvec' wstk' arena' : List (BitVec 32)}
    {te' alen' wlen' : Nat} {unass' unfl' wu' fred' ni' nr' nb' oom' : BitVec 64}
    {sc' : FullScratch} (hst : RedSt c F0 F_cur s R ext st ml) :
    let sA : FullState :=
      { core := { st.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
          wvec := wvec', wstk := wstk', arena := arena', arena_len := alen', wlen := wlen',
          wusable := wu', arena_garbage := 0#64, first_reducible := fred', num_irred := ni',
          num_redundant := nr', num_binary := nb', oom := oom' }
        scratch := sc' }
    sA.LengthsOk c → FullWitnessInv c F0 F_cur sA.core → FullArenaVarsNodup sA →
    FullLastLearnedWf sA → sc'.extend_len = st.scratch.extend_len →
    sc'.work_stk1 = st.scratch.work_stk1 → sc'.work_stk2 = st.scratch.work_stk2 →
    (0 < st.core.cur_level → vals' = st.core.vals ∧ lvl' = st.core.lvl ∧ trl' = st.core.trl ∧
      tp' = st.core.trail_pos ∧ te' = st.core.trail_end) →
    (FullM6HdrMem c ext sA ⋆ R) m' → RedSt c F0 F_cur s R ext sA m' := by
  intro sA hlenA hwA hndA hllA hextA hws1A hws2A hposA hm'
  have hspA := fullSparseInvW_of_sweep13 hst.inv.sparseW hlenA hwA hndA hllA rfl rfl rfl hextA
  refine ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk hspA,
    hst.cl, hst.fu, hst.cv, hst.tmp, hst.tl, hst.prb, hst.mcl,
    hws1A.trans hst.ws1, hws2A.trans hst.ws2, fun hpos => ?_, hm'⟩
  obtain ⟨hv, hl, ht, htp, hte⟩ := hposA hpos
  obtain ⟨hcl, hv0, hl0, ht0, htp0, hte0⟩ := hst.pos hpos
  exact ⟨hcl, hv.trans hv0, hl.trans hl0, ht.trans ht0, htp.trans htp0, hte.trans hte0⟩

/-! ## 3. Shared WP Callee Wrappers (`backtrack0`, `propagate0`, `markReasons`, `sweep13`) -/

theorem red_call_backtrack0 {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64, i64]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s st : FullState} {R : Mem 64 → Prop} {ml : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, 0#64, ()))
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    (hst : RedSt c F0 F_cur s R ext st ml)
    (hk : ∀ sB mB, RedSt c F0 F_cur s R ext sB mB →
      sB.core.cur_level = 0 → sB.core.oom = st.core.oom → wp Γ Q X (k ()) mB) :
    wp Γ Q X (.call "full_backtrack" (as := [i64, i64]) (bs := []) args k) ml := by
  refine wp_m6Hdr_focus_frame hst.mem fun hmf => ?_
  refine wp_call_of_spec args k ?_
  rw [hargs]
  have hsp := hst.inv.sparseW
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcl_bd : st.core.cur_level < 2 ^ 64 := by
    have := hsp.2.1.cur_level_le; have := hsp.1.core_ok.trail_end_le
    have := hsp.1.core_ok.cur_vars_le; omega
  refine hBt _ _ _ X ⟨c, st, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hsp.1, hcl_bd,
    fun _ => by
      have := hsp.1.core_ok.trail_end_le; have := hsp.1.core_ok.cur_vars_le
      have := hsp.2.1.cur_level_le; omega,
    hsp.2.1.trail_lits_lt, hmf,
    fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m' hlen' _ _ hcl' hps hsc_ex _ _ hw' _
      hm' => ?_⟩
  have hcl'0 : cl' = 0 := hcl'.trans (Nat.min_zero _)
  subst hcl'0
  obtain ⟨_, _, _, _, _, _, _, _, _, hsc_eq⟩ := hsc_ex
  have hll' : sc'.last_learned = st.scratch.last_learned := by rw [hsc_eq]
  have hext' : sc'.extend_len = st.scratch.extend_len := by rw [hsc_eq]
  have hws1' : sc'.work_stk1 = st.scratch.work_stk1 := by rw [hsc_eq]
  have hws2' : sc'.work_stk2 = st.scratch.work_stk2 := by rw [hsc_eq]
  exact hk _ m'
    (redSt_backtrack0 hst hlen' (hw' F0 F_cur hsp.2.1 (Nat.zero_le _)) hll' hext' hws1' hws2'
      (fullM6HdrMem_unfocus_full hm')) rfl rfl

theorem red_call_propagate0 {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s st : FullState} {R : Mem 64 → Prop} {ml : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hProp : Γ.Has "full_propagate" PropSearch.Spec.propagateM6Spec)
    (hst : RedSt c F0 F_cur s R ext st ml) (hcl0 : st.core.cur_level = 0)
    (hk : ∀ r ext' s' m', RedSt c F0 F_cur s R ext' s' m' → s'.core.cur_level = 0 →
      st.core.trail_end ≤ s'.core.trail_end → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → st.core.oom = 0#64 → s'.core.oom = 0#64) →
      (r = 1#64 → F0.Unsat) → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_propagate" (as := [i64]) (bs := [i64]) args k) ml := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  have hsp := hst.inv.sparseW
  refine hProp _ _ _ X ⟨c, F0, F_cur, ext, st, R, rfl, hst.inv.cfgOk, hst.inv.extOk,
    hsp.1, hsp.2.1, hsp.2.2.2.2.2, hst.mem, ?_⟩
  intro r ext' vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen'
    wu' fuel' ctype' cref' c0' c1' oom' sc' m' s' hext' _ hlen' hw' htr _ hap hps hrr _ hnprb _ hfu
    hr h0 h1 _ _ hm'
  have hextSt : FullExtScratchPres st s' := hps.1
  have hsp' : FullSparseInvW c F0 F_cur s' :=
    fullSparseInvW_of_bcp13 hsp hlen' hw' hap rfl rfl rfl hextSt.1 hextSt.2
  have hst' : RedSt c F0 F_cur s R ext' s' m' :=
    ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hext' hsp', hst.cl, Nat.le_trans hfu hst.fu,
      hst.cv, hst.tmp, hst.tl, hst.prb, hst.mcl, hps.2.1.trans hst.ws1,
      hps.2.2.1.trans hst.ws2,
      fun hpos => by change 0 < st.core.cur_level at hpos; omega, hm'⟩
  exact hk r ext' s' m' hst' hcl0 htr.1 hr (fun h0eq hso => (h0 h0eq).2.1 hso)
    (fun h1eq => level0_unsat_of_conflict_okW hw' hcl0 (h1 h1eq).2.2)

theorem red_call_mark_reasons {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64, .bool]} {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s st : FullState} {R : Mem 64 → Prop} {ml : Mem 64} {Q : Post ret} {X : XPost}
    {set_flag : Bool} (hargs : vals args = (c.hdr, set_flag, ()))
    (hMark : Γ.Has "full_mark_reasons" fullMarkReasonsSpec)
    (hst : RedSt c F0 F_cur s R ext st ml)
    (hk : ∀ s' m', RedSt c F0 F_cur s R ext s' m' →
      (set_flag = true → FullReasonsMarked s') → s'.core.oom = st.core.oom →
      wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_mark_reasons" (as := [i64, .bool]) (bs := []) args k) ml := by
  refine wp_m6Hdr_focus_frame hst.mem fun hmf => ?_
  refine wp_call_of_spec args k ?_
  rw [hargs]
  have hsp := hst.inv.sparseW
  refine hMark _ _ _ X ⟨c, F0, F_cur, st, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R,
    rfl, hsp.1, hsp.2.1, hmf, fun ar' m' hl' hrefs' hper' hrm' hw' hm' => ?_⟩
  exact hk _ m' (redSt_mark_reasons hst hl' hrefs' hper' hw' (fullM6HdrMem_unfocus_full hm'))
    (fun hsf => fun idx hidx hpos hlg => hrm' hsf idx hidx hpos hlg) rfl

theorem red_call_sweep13 {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s st : FullState} {R : Mem 64 → Prop} {ml : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hSweep : Γ.Has "full_arena_sweep" Collect.Spec.step13ArenaSweepSpec)
    (hst : RedSt c F0 F_cur s R ext st ml)
    (hrm : 0 < st.core.cur_level → FullReasonsMarked st)
    (hk : ∀ sr sA mA, RedSt c F0 F_cur s R ext sA mA →
      sr = 0#64 ∨ sr = 1#64 ∨ sr = 2#64 ∨ sr = 3#64 →
      (sr = 0#64 ∨ sr = 1#64 → sA.core.oom = 0#64) →
      (0 < st.core.cur_level → sr ≠ 1#64 ∧ sr ≠ 2#64) →
      (sr = 1#64 → sA.core.cur_level = 0 ∧ st.core.trail_end < sA.core.trail_end) →
      (sr = 2#64 → sA.core.cur_level = 0 ∧ F0.Unsat) →
      wp Γ Q X (k (sr, ())) mA) :
    wp Γ Q X (.call "full_arena_sweep" (as := [i64]) (bs := [i64]) args k) ml := by
  refine wp_m6Hdr_focus_frame hst.mem fun hmf => ?_
  refine wp_call_of_spec args k ?_
  rw [hargs]
  have hsp := hst.inv.sparseW
  refine hSweep _ _ _ X ⟨c, F0, F_cur, st, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R,
    rfl, hsp.1, hsp.2.1, hsp.2.2.2.1, hsp.2.2.2.2.2,
    fun hpos => fun idx hidx hp hl => hrm hpos idx hidx hp hl, hmf,
    fun sr vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen' wlen' wu'
      fred' ni' nr' nb' oom' sc' mA hlenA hdomA hextA hws1A hws2A hllA hwA hndA hoomA hposA
      hsr1 hsr2 _ hmA => ?_⟩
  have hstA := redSt_arena_sweep13 hst hlenA hwA hndA hllA hextA hws1A hws2A
    (fun hpos => by
      obtain ⟨_, _, hv, hl, ht, htp, hte⟩ := hposA hpos
      exact ⟨hv, hl, ht, htp, hte⟩)
    (fullM6HdrMem_unfocus_full hmA)
  exact hk sr _ mA hstA hdomA hoomA
    (fun hpos => ⟨(hposA hpos).1, (hposA hpos).2.1⟩)
    hsr1 hsr2

end LeanQbe.T.Examples.Kissat.Proof.Reduce
