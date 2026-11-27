/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5VivifyBackboneProof0a
import LeanQbe.T.Examples.Kissat.FullVivifyLemmas2
import LeanQbe.T.Examples.Kissat.FullVivifyLemmas3
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat Fidelity Step 13 Shard S5-B — Vivify Deduce Clear & Large Reason (`Proof1a`)

Exports `S13DeduceHelpers` (`S13ArPres`, `s13_deduce_clear_wp`, `s13_deduce_large_rsn_wp`)
for `full_viv_deduce_m6` (calling `full_viv_recompute_promote_fid` on redundant reasons)
while keeping every file `< 1,400` LOC and every theorem `<= 420` lines.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open FullVivTopTactics FullM6VivBackbone FullVivifyHelpers
open scoped FullArenaTactics FullVivTopTactics

/-! ## 1. `c0_store` / Framing & Arena-Promotion Preservation Helpers -/

section S13DeduceHelpers

private theorem c0_store_ws1_z_s13a {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pWorkStk1 + 0#64) ∧
    (FullMem c { s with scratch := { s.scratch with work_stk1 := s.scratch.work_stk1.set 0 v } }
      ⋆ R) (storeMem m i32 (c.pWorkStk1 + 0#64) v) := by
  simpa using FullArenaTactics.store_full_work_stk1 v hi hm

private theorem c0_store_ws1_b_s13a {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pWorkStk1 ∧
    (FullMem c { s with scratch := { s.scratch with work_stk1 := s.scratch.work_stk1.set 0 v } }
      ⋆ R) (storeMem m i32 c.pWorkStk1 v) := by
  simpa using FullArenaTactics.store_full_work_stk1 v hi hm

private theorem c0_store_ws2_z_s13a {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pWorkStk2 + 0#64) ∧
    (FullMem c { s with scratch := { s.scratch with work_stk2 := s.scratch.work_stk2.set 0 v } }
      ⋆ R) (storeMem m i32 (c.pWorkStk2 + 0#64) v) := by
  simpa using FullArenaTactics.store_full_work_stk2 v hi hm

private theorem c0_store_ws2_b_s13a {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pWorkStk2 ∧
    (FullMem c { s with scratch := { s.scratch with work_stk2 := s.scratch.work_stk2.set 0 v } }
      ⋆ R) (storeMem m i32 c.pWorkStk2 v) := by
  simpa using FullArenaTactics.store_full_work_stk2 v hi hm

attribute [local c0_store] c0_store_ws1_z_s13a c0_store_ws1_b_s13a
  c0_store_ws2_z_s13a c0_store_ws2_b_s13a

/-- Arena-promotion preservation invariant across `full_viv_recompute_promote_fid` calls
inside `full_viv_deduce_m6`. -/
@[expose] def S13ArPres (s0 s : FullState) : Prop :=
  fullArenaClauseRefs s = fullArenaClauseRefs s0 ∧
  (∀ r ∈ fullArenaClauseRefs s0,
    fullArenaClauseGarb s r = fullArenaClauseGarb s0 r ∧
    fullArenaClauseSize s r = fullArenaClauseSize s0 r ∧
    fullArenaClauseLits s r = fullArenaClauseLits s0 r)

theorem s13ArPres_refl (s : FullState) : S13ArPres s s :=
  ⟨rfl, fun _ _ => ⟨rfl, rfl, rfl⟩⟩

theorem s13ArPres_trans {s0 s1 s2 : FullState} (h1 : S13ArPres s0 s1) (h2 : S13ArPres s1 s2) :
    S13ArPres s0 s2 :=
  ⟨h2.1.trans h1.1, fun r hr =>
    let ⟨hg1, hs1, hl1⟩ := h1.2 r hr
    let ⟨hg2, hs2, hl2⟩ := h2.2 r (h1.1.symm ▸ hr)
    ⟨hg2.trans hg1, hs2.trans hs1, hl2.trans hl1⟩⟩

theorem s13ArPres_of_fields {s0 : FullState} {ar' mclr' : List (BitVec 32)}
    (hrefs : fullArenaClauseRefs
      { s0 with core := { s0.core with arena := ar', min_clr := mclr' } } =
      fullArenaClauseRefs s0)
    (hpres : ∀ r ∈ fullArenaClauseRefs s0,
      fullArenaClauseGarb { s0 with core := { s0.core with arena := ar', min_clr := mclr' } } r =
        fullArenaClauseGarb s0 r ∧
      fullArenaClauseSize { s0 with core := { s0.core with arena := ar', min_clr := mclr' } } r =
        fullArenaClauseSize s0 r ∧
      fullArenaClauseLits { s0 with core := { s0.core with arena := ar', min_clr := mclr' } } r =
        fullArenaClauseLits s0 r) :
    S13ArPres s0 { s0 with core := { s0.core with arena := ar', min_clr := mclr' } } :=
  ⟨hrefs, hpres⟩

theorem s13ArPres_with_fields {s0 s1 : FullState} (h : S13ArPres s0 s1)
    {mrk1 lm1 : List (BitVec 8)} {ws1 ws2 : List (BitVec 32)} {asz rsz : BitVec 64} :
    S13ArPres s0
      { s1 with
        core := { s1.core with mrk := mrk1, lit_mark := lm1 }
        scratch := { s1.scratch with
          work_stk1 := ws1, work_stk2 := ws2, ant_sz := asz, res_sz := rsz } } := by
  rcases h with ⟨hrefs, hpres⟩
  refine ⟨?_, fun r hr => ?_⟩
  · unfold fullArenaClauseRefs fullArenaClauseRefsCore at hrefs ⊢; exact hrefs
  · exact hpres r hr

theorem s13_vivClosed_taut_true {s : FullState} {implied : BitVec 32}
    {ws1 ws2 ws2' : List (BitVec 32)} {qi qlen olen olen' : Nat} {taut : Bool}
    (hcb : VivClosedOk s implied ws1 ws2 qi qlen olen taut)
    (hrsn : s.core.rsns[(ws1[qi]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    VivClosedOk s implied ws1 ws2' (qi + 1) qlen olen' true := by
  intro k hk idx hidx ht
  rcases (by omega : k < qi ∨ k = qi) with hk' | rfl
  · have h := hcb k hk' idx hidx ht
    by_cases hr : s.core.rsns[(ws1[k]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32
    · simp only [hr, ↓reduceIte]; intro h1; cases h1
    · simp only [hr, ↓reduceIte] at h ⊢; exact h
  · simp only [hrsn, ↓reduceIte]; intro h1; cases h1

theorem s13_vivSeed_mono_ws2 {s : FullState} {cref implied : BitVec 32}
    {ws1 ws2 ws2' : List (BitVec 32)} {qlen olen olen' : Nat}
    (hsd : VivSeedOk s cref implied ws1 ws2 qlen olen false)
    (hle : olen ≤ olen') (hlen : olen ≤ ws2.length) (hlen' : olen' ≤ ws2'.length)
    (hpre : ∀ j < olen, ws2'[j]? = ws2[j]?) :
    VivSeedOk s cref implied ws1 ws2' qlen olen' false := by
  intro _
  have h := hsd rfl
  by_cases hi : implied = 0xFFFFFFFF#32
  · simp only [hi, ne_eq, not_true_eq_false, ↓reduceIte] at h ⊢; exact h
  · simp only [hi, ne_eq, not_false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨j, hj, hjeq⟩ := (mem_map_take_iff hlen).mp h
    exact (mem_map_take_iff hlen').mpr ⟨j, by omega, by rw [hpre j hj, hjeq]⟩

theorem s13_vivClosed_ar_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} {mrk : List (BitVec 8)} {implied : BitVec 32} {ws1 ws2 : List (BitVec 32)}
    {qi qlen olen : Nat} {taut : Bool}
    (hw : FullWitnessInv c F0 F_cur s.core) (_hq : VivQueueOk c s mrk ws1 qlen) (_hqi : qi ≤ qlen)
    (_hcore : s'.core.cur_vars = s.core.cur_vars) (hlvl : s'.core.lvl = s.core.lvl)
    (hrsns : s'.core.rsns = s.core.rsns) (htrl : s'.core.trl = s.core.trl)
    (hte : s'.core.trail_end = s.core.trail_end) (hpres : S13ArPres s s')
    (hcb : VivClosedOk s implied ws1 ws2 qi qlen olen taut) :
    VivClosedOk s' implied ws1 ws2 qi qlen olen taut := by
  intro k hk idx hidx htrk
  rw [hte] at hidx; rw [htrl] at htrk
  have hcbk := hcb k hk idx hidx htrk
  rw [hrsns, hlvl]
  by_cases hdec : s.core.rsns[(ws1[k]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32
  · simp only [hdec, ↓reduceIte] at hcbk ⊢; rwa [htrl]
  · simp only [hdec, ↓reduceIte] at hcbk ⊢
    by_cases hbin : (s.core.rsns[(ws1[k]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 &&&
        0x80000000#32) ≠ 0#32
    · rw [ite_eq_left hbin] at hcbk ⊢; exact hcbk
    · rw [ite_eq_right hbin] at hcbk ⊢
      let r := (s.core.rsns[(ws1[k]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat
      have href_r : r ∈ fullArenaClauseRefs s := by
        have hri := hw.reason_inv idx hidx (by rwa [htrk])
        rw [htrk, ite_eq_right hbin] at hri; exact hri.1
      have hlits_eq : fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r :=
        (hpres.2 r href_r).2.2
      dsimp only [r] at hlits_eq
      rw [hlits_eq, htrl]; exact hcbk

theorem s13_vivOut_ar_eq {s s' : FullState} {implied : BitVec 32} {ws1 ws2 : List (BitVec 32)}
    {qi olen : Nat} {taut : Bool}
    (hcv : s'.core.cur_vars = s.core.cur_vars) (hrsns : s'.core.rsns = s.core.rsns)
    (ho : VivOutOk s implied ws1 ws2 qi olen taut) :
    VivOutOk s' implied ws1 ws2 qi olen taut := by
  intro ht; have h := ho ht; rwa [hcv, hrsns]

theorem s13_vivSeed_ar_eq {_c : FullCfg} {_F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} {cref implied : BitVec 32} {ws1 ws2 : List (BitVec 32)}
    {qlen olen : Nat} {taut : Bool}
    (hconfl : implied = 0xFFFFFFFF#32 →
      FullVivifySpecs.FullVivConflictOk F_cur s ∨
      (s.core.confl_type = 0#64 ∧
        ∀ l ∈ fullArenaClauseLits s cref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8))
    (href : cref.toNat ∈ fullArenaClauseRefs s)
    (hlvl : s'.core.lvl = s.core.lvl) (hct : s'.core.confl_type = s.core.confl_type)
    (hcr : s'.core.confl_ref = s.core.confl_ref)
    (hcl0 : s'.core.confl_lit0 = s.core.confl_lit0)
    (hcl1 : s'.core.confl_lit1 = s.core.confl_lit1) (hpres : S13ArPres s s')
    (hsd : VivSeedOk s cref implied ws1 ws2 qlen olen taut) :
    VivSeedOk s' cref implied ws1 ws2 qlen olen taut := by
  intro ht; have h := hsd ht
  by_cases hi : implied ≠ 0xFFFFFFFF#32
  · dsimp only [VivSeedOk] at h ⊢; rw [ite_eq_left hi] at h ⊢; exact h
  · have hieq : implied = 0xFFFFFFFF#32 := by
      cases Classical.em (implied = 0xFFFFFFFF#32) with
      | inl he => exact he
      | inr hne => exact absurd hne hi
    simp only [hi, ↓reduceIte] at h ⊢
    rw [hct, hlvl]
    by_cases hct1 : s.core.confl_type = 1#64
    · simp only [hct1, ↓reduceIte] at h ⊢; rwa [hcl0, hcl1]
    · simp only [hct1, ↓reduceIte] at h ⊢; rw [hcr]
      have href_src : (if s.core.confl_type = 2#64 then s.core.confl_ref.toNat else cref.toNat) ∈
          fullArenaClauseRefs s := by
        by_cases hct2 : s.core.confl_type = 2#64
        · simp only [hct2, ↓reduceIte]
          rcases hconfl hieq with (⟨h1, _⟩ | ⟨_, hr2, _⟩) | ⟨h0, _⟩
          · exact absurd h1 hct1
          · exact hr2
          · rw [h0] at hct2; cases hct2
        · simp only [hct2, ↓reduceIte]; exact href
      have hlits := (hpres.2 _ href_src).2.2
      intro l hl; exact h l (by rwa [hlits] at hl)

theorem s13_vivQueue_ar_eq {c : FullCfg} {s s' : FullState} {mrk : List (BitVec 8)}
    {ws1 : List (BitVec 32)} {qlen : Nat}
    (hcv : s'.core.cur_vars = s.core.cur_vars) (hlvl : s'.core.lvl = s.core.lvl)
    (hte : s'.core.trail_end = s.core.trail_end) (htrl : s'.core.trl = s.core.trl)
    (hq : VivQueueOk c s mrk ws1 qlen) : VivQueueOk c s' mrk ws1 qlen := by
  simpa only [VivQueueOk, hcv, hlvl, hte, htrl] using hq

@[expose] def S13SubRefOk (s : FullState) (asz : BitVec 64) : Prop :=
  M6SubRefOk s asz ∧
  (asz ≠ 0xFFFFFFFFFFFFFFFF#64 → asz ≠ 0xFFFFFFFFFFFFFFFE#64 →
    asz.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s asz.toNat = false)

theorem s13_subRef_set_ref {s : FullState} {r : BitVec 32}
    (hr : r.toNat ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s r.toNat = false) :
    S13SubRefOk s (r.setWidth 64) :=
  ⟨Or.inr (Or.inr (by
    simpa [BitVec.toNat_setWidth,
      (Nat.mod_eq_of_lt (Nat.lt_trans r.isLt (by decide : 2 ^ 32 < 2 ^ 64)))] using hr)),
   fun _ _ => by
     have h : (r.setWidth 64).toNat = r.toNat := by
       rw [BitVec.toNat_setWidth,
         Nat.mod_eq_of_lt (Nat.lt_trans r.isLt (by decide : 2 ^ 32 < 2 ^ 64))]
     rw [h]; exact ⟨hr, hng⟩⟩

theorem s13_subRef_of_pres {s0 s : FullState} {asz : BitVec 64}
    (hpres : S13ArPres s0 s) (h : S13SubRefOk s0 asz) : S13SubRefOk s asz :=
  ⟨by rcases h.1 with rfl | rfl | hr
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (hpres.1.symm ▸ hr)),
   fun h1 h2 =>
     let ⟨hr, hng⟩ := h.2 h1 h2
     ⟨hpres.1.symm ▸ hr, (hpres.2 _ hr).1.symm ▸ hng⟩⟩

theorem s13_subRef_of_refs_eq {s s' : FullState} {asz : BitVec 64}
    (hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s) (h : M6SubRefOk s asz) :
    M6SubRefOk s' asz := by
  rcases h with rfl | rfl | hr
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (hrefs ▸ hr))

theorem s13_noMark_of_sparseW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) : S13SparseInvNoMark c F0 F_cur s :=
  ⟨hsp.1, hsp.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

theorem s13_deduce_finish_sparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : S13SparseInvNoMark c F0 F_cur s)
    {mrk' lm' : List (BitVec 8)} {ws1' ws2' : List (BitVec 32)} {asz' rsz' : BitVec 64}
    (hmrk : mrk'.length = c.max_vars) (hlm : lm'.length = 2 * c.max_vars)
    (hws1 : ws1'.length = 2 * c.max_vars) (hws2 : ws2'.length = 2 * c.max_vars)
    (hmrk_clr : ∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8)
    (hlm_clr : ∀ l < 2 * c.max_vars, lm'[l]?.getD 0#8 = 0#8) :
    FullSparseInvW c F0 F_cur
      { s with
        core := { s.core with mrk := mrk', lit_mark := lm' }
        scratch := { s.scratch with
          work_stk1 := ws1', work_stk2 := ws2', ant_sz := asz', res_sz := rsz' } } :=
  ⟨⟨{ hsp.1.core_ok with mrk_len := hmrk, lit_mark_len := hlm },
    { hsp.1.scratch_ok with work_stk1_len := hws1, work_stk2_len := hws2 }⟩,
   { hsp.2.1 with
     arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok }
     watches := hsp.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   ⟨hmrk_clr, hlm_clr⟩, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2⟩

theorem s13_deduce_state_len {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c)
    {mrk' lm' : List (BitVec 8)} {ws1' ws2' : List (BitVec 32)} {asz' rsz' : BitVec 64}
    (hmrk : mrk'.length = c.max_vars) (hlm : lm'.length = 2 * c.max_vars)
    (hws1 : ws1'.length = 2 * c.max_vars) (hws2 : ws2'.length = 2 * c.max_vars) :
    ({ s with
      core := { s.core with mrk := mrk', lit_mark := lm' }
      scratch := { s.scratch with
        work_stk1 := ws1', work_stk2 := ws2', ant_sz := asz', res_sz := rsz' } } :
      FullState).LengthsOk c :=
  ⟨{ hlen.core_ok with mrk_len := hmrk, lit_mark_len := hlm },
   { hlen.scratch_ok with work_stk1_len := hws1, work_stk2_len := hws2 }⟩

theorem s13_deduce_state_witness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core)
    {mrk' lm' : List (BitVec 8)} :
    FullWitnessInv c F0 F_cur { s.core with mrk := mrk', lit_mark := lm' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

theorem s13_deduce_state_noMark {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : S13SparseInvNoMark c F0 F_cur s)
    {mrk' lm' : List (BitVec 8)} {ws1' ws2' : List (BitVec 32)} {asz' rsz' : BitVec 64}
    (hmrk : mrk'.length = c.max_vars) (hlm : lm'.length = 2 * c.max_vars)
    (hws1 : ws1'.length = 2 * c.max_vars) (hws2 : ws2'.length = 2 * c.max_vars) :
    S13SparseInvNoMark c F0 F_cur
      { s with
        core := { s.core with mrk := mrk', lit_mark := lm' }
        scratch := { s.scratch with
          work_stk1 := ws1', work_stk2 := ws2', ant_sz := asz', res_sz := rsz' } } :=
  ⟨s13_deduce_state_len hsp.1 hmrk hlm hws1 hws2, s13_deduce_state_witness hsp.2.1,
    hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2⟩

theorem s13_push_branch_step {c : FullCfg}
    {s : FullState} {mrk_c lm1 : List (BitVec 8)} {ws1_c ws2_c : List (BitVec 32)}
    {asz_c rsz_c : BitVec 64} {qlen : Val i64} {ov : Val i32} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i32]} {X : XPost} {J : Cont [i64]} {Γ : Env}
    (hlen : s.LengthsOk c) (hq : VivQueueOk c s mrk_c ws1_c qlen.toNat)
    (hov_lt : ov.toNat < s.core.cur_vars)
    (hov_trl : ∃ idx < s.core.trail_end, (s.core.trl[idx]?.getD 0#32).toNat / 2 = ov.toNat)
    (hm : (FullMem c { s with
      core := { s.core with mrk := mrk_c, lit_mark := lm1 }
      scratch := { s.scratch with
        work_stk1 := ws1_c, work_stk2 := ws2_c, ant_sz := asz_c, res_sz := rsz_c } } ⋆ R) m)
    (hJ : ∀ (qlen' : Val i64) (mrk_n : List (BitVec 8)) (ws1_n : List (BitVec 32)) mn,
      qlen.toNat ≤ qlen'.toNat → qlen'.toNat ≤ s.core.cur_vars →
      (∀ j < qlen.toNat, ws1_n[j]? = ws1_c[j]?) →
      VivQueueOk c s mrk_n ws1_n qlen'.toNat →
      ((s.core.lvl[ov.toNat]?.getD 0#32).toNat = 0 ∨
        ov.toNat ∈ (ws1_n.take qlen'.toNat).map BitVec.toNat) →
      (FullMem c { s with
        core := { s.core with mrk := mrk_n, lit_mark := lm1 }
        scratch := { s.scratch with
          work_stk1 := ws1_n, work_stk2 := ws2_c, ant_sz := asz_c, res_sz := rsz_c } } ⋆ R) mn →
      J (qlen', ()) mn) :
    wp Γ Q X (deducePushExpr (BitVec.ofNat 64 s.core.cur_vars)
      c.pMark c.pLevel c.pWorkStk1 ov qlen J) m := by
  have hcl := hlen.core_ok; have hcv_le := hcl.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hov_lvl : ov.toNat < s.core.lvl.length := by rw [hcl.lvl_len]; omega
  have hov_mrk : ov.toNat < mrk_c.length := by rw [hq.1]; omega
  have hql_le := hq.2.2.1; have hcv_64 : s.core.cur_vars < 2 ^ 64 := by omega
  dsimp only [deducePushExpr, fvOp32]
  fvt_steps
  · have hlvl_pos : 0 < (s.core.lvl[ov.toNat]'hov_lvl).toNat := by c0_bound
    have hm0 : mrk_c[ov.toNat]'hov_mrk = 0#8 := by
      have hm032 : (mrk_c[ov.toNat]'hov_mrk).setWidth 32 = 0#32 := by assumption
      exact (bv8_zext32_eq0_iff _).mp hm032
    have hlvl_pos' : 0 < (s.core.lvl[ov.toNat]?.getD 0#32).toNat := by
      rwa [List.getElem?_eq_getElem hov_lvl, Option.getD_some]
    have hm0' : mrk_c[ov.toNat]?.getD 0#8 = 0#8 := by
      rwa [List.getElem?_eq_getElem hov_mrk, Option.getD_some]
    have hql_lt := push_queue_lt hq hcv_le hov_lt hm0'
    have hql_ws1 : qlen.toNat < ws1_c.length := by have := hq.2.1; omega
    have hql1 : (qlen + 1#64).toNat = qlen.toNat + 1 := by bv_omega
    obtain ⟨_, hq_next, hpre_next, _⟩ :=
      push_queue_step hq hcv_le hov_lt hlvl_pos' hm0' hov_trl
    fvt_steps
    have hov_mod : ov.toNat % 2 ^ 64 = ov.toNat := Nat.mod_eq_of_lt (by omega)
    refine hJ (qlen + 1#64) _ _ _ (by omega) (by omega) hpre_next ?_ (Or.inr ?_) hm
    · simpa [hql1, hov_mod] using hq_next
    · rw [hql1]
      exact (mem_map_take_iff (by simp [hq.2.1]; omega)).mpr
        ⟨qlen.toNat, by omega, by rw [List.getElem?_set_self hql_ws1]; rfl⟩
  · have hm0 : mrk_c[ov.toNat]'hov_mrk = 0#8 := by
      have hm032 : (mrk_c[ov.toNat]'hov_mrk).setWidth 32 = 0#32 := by assumption
      exact (bv8_zext32_eq0_iff _).mp hm032
    have hm0' : mrk_c[ov.toNat]?.getD 0#8 = 0#8 := by
      rwa [List.getElem?_eq_getElem hov_mrk, Option.getD_some]
    have hql_lt := push_queue_lt hq hcv_le hov_lt hm0'
    have hcv_le_q : s.core.cur_vars % 2 ^ 64 ≤ qlen.toNat := by c0_bound
    rw [Nat.mod_eq_of_lt hcv_64] at hcv_le_q; omega
  · have hm_ne0 : mrk_c[ov.toNat]'hov_mrk ≠ 0#8 := fun h => by
      have hne32 : (mrk_c[ov.toNat]'hov_mrk).setWidth 32 ≠ 0#32 := by assumption
      exact hne32 ((bv8_zext32_eq0_iff _).mpr h)
    have hm1 : mrk_c[ov.toNat]?.getD 0#8 = 1#8 := by
      rcases hq.2.2.2.2.2.2.2.1 ov.toNat hov_lt with h0 | h1
      · rw [List.getElem?_eq_getElem hov_mrk, Option.getD_some] at h0; exact absurd h0 hm_ne0
      · exact h1
    exact hJ qlen mrk_c ws1_c m (Nat.le_refl _) hql_le (fun _ _ => rfl) hq
      (Or.inr ((hq.2.2.2.2.2.2.1 ov.toNat hov_lt).mp hm1)) hm
  · have hlvl0 : (s.core.lvl[ov.toNat]'hov_lvl).toNat = 0 := by c0_bound
    exact hJ qlen mrk_c ws1_c m (Nat.le_refl _) hql_le (fun _ _ => rfl) hq
      (Or.inl (by rwa [List.getElem?_eq_getElem hov_lvl, Option.getD_some])) hm

/-! ## 2. `s13_deduce_clear_wp` -/

abbrev s13DeduceClearExpr (h pMark pLitMark pTmp pWs1 : Val i64)
    (sz : Val i32) (qlen : Val i64) (olen : Val i32) (taut : Val .bool) : Expr Val Cont [i32] :=
  Expr.group (sig := [[i64]]) (fun Js => Blocks.cons (fun p19 =>
    fvOp32 (OpCode.cmp .ult i64 .bool (by decide)) (Arg.var p19.fst, Arg.var qlen, ()) fun p =>
    Expr.jnz (Arg.var p.fst)
      (fvOp32 (OpCode.mul i64) (Arg.var p19.fst, Arg.imm 4, ()) fun p =>
       fvOp32 (OpCode.add i64) (Arg.var pWs1, Arg.var p.fst, ()) fun p =>
       Expr.load i32 (Arg.var p.fst) fun ld =>
       fvOp32 (OpCode.zext 32 64) (Arg.var ld, ()) fun p =>
       fvOp32 (OpCode.add i64) (Arg.var pMark, Arg.var p.fst, ()) fun p =>
       fvOp32 (OpCode.trunc 32 8) (Arg.imm 0, ()) fun p0 =>
       Expr.store (Arg.var p0.fst) (Arg.var p.fst)
         (fvOp32 (OpCode.add i64) (Arg.var p19.fst, Arg.imm 1, ()) fun p =>
          Expr.jump Js.fst (Arg.var p.fst, ())))
      (Expr.group (sig := [[i32]]) (fun Js2 => Blocks.cons (fun p21 =>
        fvOp32 (OpCode.cmp .ult i32 .bool (by decide)) (Arg.var p21.fst, Arg.var sz, ()) fun p =>
        Expr.jnz (Arg.var p.fst)
          (fvOp32 (OpCode.zext 32 64) (Arg.var p21.fst, ()) fun p =>
           fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
           fvOp32 (OpCode.add i64) (Arg.var pTmp, Arg.var p.fst, ()) fun p =>
           Expr.load i32 (Arg.var p.fst) fun ld =>
           fvOp32 (OpCode.zext 32 64) (Arg.var ld, ()) fun p =>
           fvOp32 (OpCode.add i64) (Arg.var pLitMark, Arg.var p.fst, ()) fun p =>
           fvOp32 (OpCode.trunc 32 8) (Arg.imm 0, ()) fun p0 =>
           Expr.store (Arg.var p0.fst) (Arg.var p.fst)
             (fvOp32 (OpCode.add i32) (Arg.var p21.fst, Arg.imm 1, ()) fun p =>
              Expr.jump Js2.fst (Arg.var p.fst, ())))
          (Expr.jnz (Arg.var taut)
            (fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 1136, ()) fun p =>
             Expr.store (Arg.imm (t := i64) 18446744073709551615) (Arg.var p.fst)
               (Expr.ret (Arg.imm 4294967295, ())))
            (Expr.ret (Arg.var olen, ())))) Blocks.nil)
        fun Js2 => Expr.jump Js2.fst (Arg.imm 0, ()))) Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.imm 0, ())

theorem s13_deduce_clear_wp (Γ : Env) {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {mrk_b lm1 : List (BitVec 8)} {ws1_b ws2_b : List (BitVec 32)} {asz_b rsz_b : BitVec 64}
    {sz : Val i32} {qlen_c : Val i64} {olen_c : Val i32} {taut_c : Val .bool}
    {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hspW : S13SparseInvNoMark c F0 F_cur s)
    (hsz_le : sz.toNat ≤ c.max_vars)
    (htmp_lt : ∀ k < sz.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hqb : VivQueueOk c s mrk_b ws1_b qlen_c.toNat)
    (hlm1_len : lm1.length = 2 * c.max_vars)
    (hlm1_dom : ∀ l < 2 * c.max_vars, lm1[l]?.getD 0#8 ≠ 0#8 →
      ∃ t < sz.toNat, (s.core.tmp[t]?.getD 0#32).toNat = l)
    (hws2_b : ws2_b.length = 2 * c.max_vars)
    (hsub_b : S13SubRefOk s asz_b)
    (hm : (FullMem c { s with
      core := { s.core with mrk := mrk_b, lit_mark := lm1 }
      scratch := { s.scratch with
        work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_b } } ⋆ R) m)
    (hQ : ∀ (ret : Val i32) mrk' lm' asz' mf,
      let s' : FullState := { s with
        core := { s.core with mrk := mrk', lit_mark := lm' }
        scratch := { s.scratch with
          work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz', res_sz := rsz_b } }
      FullSparseInvW c F0 F_cur s' → S13SubRefOk s' asz' →
      (taut_c = true → ret = 0xFFFFFFFF#32) → (taut_c = false → ret = olen_c) →
      (taut_c = false → asz' = asz_b) →
      (FullMem c s' ⋆ R) mf → Q (ret, ()) mf) :
    wp Γ Q X (s13DeduceClearExpr c.hdr c.pMark c.pLitMark c.pTmp c.pWorkStk1
      sz qlen_c olen_c taut_c) m := by
  have hcl := hspW.1.core_ok; have hcv_le := hcl.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  dsimp only [s13DeduceClearExpr, fvOp32]
  refine wp_loop_inv (ts := [i64])
    (fun (qi2, ()) mc => ∃ mrk_c : List (BitVec 8),
      qi2.toNat ≤ qlen_c.toNat ∧ mrk_c.length = c.max_vars ∧
      (∀ v < c.max_vars, mrk_c[v]?.getD 0#8 = 0#8 ∨
        ∃ k, qi2.toNat ≤ k ∧ k < qlen_c.toNat ∧ (ws1_b[k]?.getD 0#32).toNat = v) ∧
      (FullMem c { s with
        core := { s.core with mrk := mrk_c, lit_mark := lm1 }
        scratch := { s.scratch with
          work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_b } } ⋆ R) mc)
    (fun (qi2, ()) _ => qlen_c.toNat - qi2.toNat) ?_ ?_
  · intro Jc hJc; fvt_steps
    exact hJc (0#64, ()) m ⟨mrk_b, by simp, hqb.1, viv_clear_mrk_init hqb hcv_le, hm⟩
  · rintro Jc ⟨qi2, ⟨⟩⟩ mc ⟨mrk_c, hq2_le, hmrkc_len, hinv_c, hmc⟩ ihc
    fvt_step; fvt_step
    · have hqi2_lt : qi2.toNat < qlen_c.toNat := by c0_bound
      have hqi2_ws1 : qi2.toNat < ws1_b.length := by have := hqb.2.1; have := hqb.2.2.1; omega
      have hqi2_1 : (qi2 + 1#64).toNat = qi2.toNat + 1 := by bv_omega
      obtain ⟨hv_mrk, hinv_next⟩ := viv_clear_mrk_step hmrkc_len hqb.2.2.2.1 hcv_le hqi2_lt hinv_c
      have hidx_mrk : (ws1_b[qi2.toNat]'hqi2_ws1).toNat < mrk_c.length := by
        rwa [List.getElem?_eq_getElem hqi2_ws1, Option.getD_some] at hv_mrk
      have hidx_set64 : ((ws1_b[qi2.toNat]'hqi2_ws1).setWidth 64).toNat =
          (ws1_b[qi2.toNat]'hqi2_ws1).toNat := by bv_omega
      have hidx_mrk64 : ((ws1_b[qi2.toNat]'hqi2_ws1).setWidth 64).toNat < mrk_c.length := by
        rw [hidx_set64]; exact hidx_mrk
      have hidx_mod : (ws1_b[qi2.toNat]'hqi2_ws1).toNat % 2 ^ 64 =
          (ws1_b[qi2.toNat]'hqi2_ws1).toNat :=
        Nat.mod_eq_of_lt (Nat.lt_trans (ws1_b[qi2.toNat]'hqi2_ws1).isLt (by decide))
      fvt_steps; simp only [hidx_mod] at *
      exact ihc (qi2 + 1#64, ()) _ (by dsimp only; omega)
        ⟨mrk_c.set (ws1_b[qi2.toNat]'hqi2_ws1).toNat 0#8, by dsimp only; omega, by simp [hmrkc_len],
         fun u hu => by
           have h := hinv_next u hu
           rwa [List.getElem?_eq_getElem hqi2_ws1, Option.getD_some, ← hqi2_1] at h, by assumption⟩
    · have hqi2_eq : qi2.toNat = qlen_c.toNat := by c0_bound
      have hmrkc_clr : ∀ v < c.max_vars, mrk_c[v]?.getD 0#8 = 0#8 := fun v hv => by
        rcases hinv_c v hv with h0 | ⟨k, hk1, hk2, _⟩
        · exact h0
        · omega
      clear hc ihc Jc
      refine wp_loop_inv (ts := [i32])
        (fun (mi2, ()) mlm =>
          mi2.toNat ≤ sz.toNat ∧ ∃ lm2 : List (BitVec 8), lm2.length = 2 * c.max_vars ∧
            (∀ l < 2 * c.max_vars, lm2[l]?.getD 0#8 ≠ 0#8 →
              ∃ t, mi2.toNat ≤ t ∧ t < sz.toNat ∧ (s.core.tmp[t]?.getD 0#32).toNat = l) ∧
            (FullMem c { s with
              core := { s.core with mrk := mrk_c, lit_mark := lm2 }
              scratch := { s.scratch with
                work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_b } }
              ⋆ R) mlm)
        (fun (mi2, _) _ => sz.toNat - mi2.toNat) ?_ ?_
      · intro Jl hJl; fvt_steps
        exact hJl (0#32, ()) mc ⟨Nat.zero_le _, lm1, hlm1_len, fun l hl hnz => by
          obtain ⟨t, ht, hteq⟩ := hlm1_dom l hl hnz
          exact ⟨t, Nat.zero_le _, by omega, hteq⟩, hmc⟩
      · rintro Jl ⟨mi2, ⟨⟩⟩ mlm ⟨hmi2_le, lm2, hlm2_len, hlm2_dom, hmlm⟩ ihl
        fvt_step; fvt_step
        · have hmi2_lt : mi2.toNat < sz.toNat := by c0_bound
          have hmi2_1 : (mi2 + 1#32).toNat = mi2.toNat + 1 := by bv_omega
          have hmi2_tmp : mi2.toNat < s.core.tmp.length := by rw [hcl.tmp_len_arr]; omega
          let lt2 := s.core.tmp[mi2.toNat]'hmi2_tmp
          have hlt2_lm : lt2.toNat < lm2.length := by
            have := htmp_lt mi2.toNat hmi2_lt
            rw [List.getElem?_eq_getElem hmi2_tmp, Option.getD_some] at this
            dsimp only [lt2]; omega
          fvt_steps
          let lm2' := lm2.set lt2.toNat 0#8
          refine ihl (mi2 + 1#32, ()) _ (by dsimp only; omega)
            ⟨by omega, lm2', by simp [lm2', hlm2_len], fun q hq hnz => ?_, by assumption⟩
          by_cases hql : q = lt2.toNat
          · subst hql; dsimp only [lm2'] at hnz
            rw [List.getElem?_set_self hlt2_lm, Option.getD_some] at hnz; exact absurd rfl hnz
          · dsimp only [lm2'] at hnz; rw [List.getElem?_set_ne (Ne.symm hql)] at hnz
            obtain ⟨t, ht1, ht2, hteq⟩ := hlm2_dom q hq hnz
            have hne_t : t ≠ mi2.toNat := fun he => by
              subst he; rw [List.getElem?_eq_getElem hmi2_tmp, Option.getD_some] at hteq
              exact hql hteq.symm
            exact ⟨t, by omega, ht2, hteq⟩
        · have hmi2_eq : mi2.toNat = sz.toNat := by c0_bound
          have hlm2_clr : ∀ l < 2 * c.max_vars, lm2[l]?.getD 0#8 = 0#8 := fun l hl =>
            Classical.byContradiction fun hnz => by
              obtain ⟨t, ht1, ht2, _⟩ := hlm2_dom l hl hnz; omega
          fvt_steps
          · exact hQ 0xFFFFFFFF#32 mrk_c lm2 0xFFFFFFFFFFFFFFFF#64 _
              (s13_deduce_finish_sparse hspW hmrkc_len hlm2_len hqb.2.1 hws2_b hmrkc_clr hlm2_clr)
              ⟨Or.inl rfl, fun h => absurd rfl h⟩ (fun _ => rfl)
              (fun h => by cases h.symm.trans hc) (fun h => by cases h.symm.trans hc)
              (by assumption)
          · exact hQ olen_c mrk_c lm2 asz_b mlm
              (s13_deduce_finish_sparse hspW hmrkc_len hlm2_len hqb.2.1 hws2_b hmrkc_clr hlm2_clr)
              (s13_subRef_of_pres (s13ArPres_refl _) hsub_b)
              (fun h => by cases h.symm.trans hc) (fun _ => rfl) (fun _ => rfl) hmlm

/-! ## 3. `s13_deduce_large_rsn_wp` -/

abbrev s13DeduceLargeRsnExpr (h pVars pMark pLevel pArena pWs1 : Val i64)
    (cref sz rsn_bv v_bv : Val i32) (qlen qi1 : Val i64) (olen : Val i32) (taut : Val .bool)
    (J_brk : Cont [i64, i64, i32, .bool]) (J : Cont [i64]) : Expr Val Cont [i32] :=
  fvOp32 (OpCode.zext 32 64) (Arg.var rsn_bv, ()) fun p =>
  fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p3 =>
  fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 48, ()) fun p48 =>
  Expr.load i64 (Arg.var p48.fst) fun ld_13 =>
  fvOp32 (OpCode.cmp .ule i64 .bool (by decide)) (Arg.var p3.fst, Arg.var ld_13, ()) fun pb =>
  Expr.jnz (Arg.var pb.fst)
    (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
      Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
        fvOp32 (OpCode.zext 32 64) (Arg.var rsn_bv, ()) fun p =>
        fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.imm 2, ()) fun p =>
        fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
        fvOp32 (OpCode.add i64) (Arg.var pArena, Arg.var p.fst, ()) fun p =>
        Expr.load i32 (Arg.var p.fst) fun ld_14 =>
        Expr.group (sig := [[i64, i32]]) (fun Js_2 => Blocks.cons (fun p_38 =>
          fvOp32 (OpCode.cmp .ult i32 .bool (by decide))
            (Arg.var p_38.snd.fst, Arg.var ld_14, ()) fun p =>
          Expr.jnz (Arg.var p.fst)
            (fvOp32 (OpCode.zext 32 64) (Arg.var rsn_bv, ()) fun p =>
             fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p =>
             fvOp32 (OpCode.zext 32 64) (Arg.var ld_14, ()) fun pz =>
             fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.var pz.fst, ()) fun p =>
             fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 48, ()) fun p48 =>
             Expr.load i64 (Arg.var p48.fst) fun ld_15 =>
             fvOp32 (OpCode.cmp .ule i64 .bool (by decide))
               (Arg.var p.fst, Arg.var ld_15, ()) fun p =>
             Expr.jnz (Arg.var p.fst)
               (fvOp32 (OpCode.zext 32 64) (Arg.var rsn_bv, ()) fun p =>
                fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p =>
                fvOp32 (OpCode.zext 32 64) (Arg.var p_38.snd.fst, ()) fun pz =>
                fvOp32 (OpCode.add i64) (Arg.var p.fst, Arg.var pz.fst, ()) fun p =>
                fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
                fvOp32 (OpCode.add i64) (Arg.var pArena, Arg.var p.fst, ()) fun p =>
                Expr.load i32 (Arg.var p.fst) fun ld =>
                fvOp32 (OpCode.lshr i32) (Arg.var ld, Arg.imm 1, ()) fun p_ov =>
                Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p =>
                  fvOp32 (OpCode.add i32) (Arg.var p_38.snd.fst, Arg.imm 1, ()) fun pj =>
                  Expr.jump Js_2.fst (Arg.var p.fst, Arg.var pj.fst, ())) Blocks.nil) fun Js_n =>
                fvOp32 (OpCode.cmp .ne i32 .bool (by decide))
                  (Arg.var p_ov.fst, Arg.var v_bv, ()) fun p =>
                Expr.jnz (Arg.var p.fst)
                  (deducePushExpr pVars pMark pLevel pWs1 p_ov.fst p_38.fst Js_n.fst)
                  (Expr.jump Js_n.fst (Arg.var p_38.fst, ())))
               (Expr.jump J (Arg.var p_38.fst, ())))
            (Expr.jump J (Arg.var p_38.fst, ()))) Blocks.nil)
          fun Js_init => Expr.jump Js_init.fst (Arg.var qlen, Arg.imm 0, ())) Blocks.nil)
        fun Js_as =>
        fvOp32 (OpCode.cmp .ne i32 .bool (by decide)) (Arg.var rsn_bv, Arg.var cref, ()) fun p =>
        Expr.jnz (Arg.var p.fst)
          (Expr.call "full_viv_subsumes_cl_m6" (as := [i64, i32, i32]) (bs := [.bool])
             (Arg.var h, Arg.var rsn_bv, Arg.var sz, ()) fun ok =>
           Expr.jnz (Arg.var ok.fst)
             (fvOp32 (OpCode.zext 32 64) (Arg.var rsn_bv, ()) fun pr =>
              fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 1136, ()) fun p =>
              Expr.store (Arg.var pr.fst) (Arg.var p.fst)
                (Expr.jump J_brk (Arg.var qlen, Arg.var qi1, Arg.var olen, Arg.var taut, ())))
             (Expr.jump Js_as.fst ()))
          (Expr.jump Js_as.fst ())) Blocks.nil)
      fun Js_rs =>
      fvOp32 (OpCode.zext 32 64) (Arg.var rsn_bv, ()) fun p =>
      fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
      fvOp32 (OpCode.add i64) (Arg.var pArena, Arg.var p.fst, ()) fun p =>
      Expr.load i32 (Arg.var p.fst) fun ld =>
      fvOp32 (OpCode.and i32) (Arg.var ld, Arg.imm 4194304, ()) fun p =>
      fvOp32 (OpCode.cmp .ne i32 .bool (by decide)) (Arg.var p.fst, Arg.imm 0, ()) fun p =>
      Expr.jnz (Arg.var p.fst)
        (fvOp32 (OpCode.add i64) (Arg.var h, Arg.imm 1144, ()) fun p =>
         Expr.store (Arg.imm (t := i64) 1) (Arg.var p.fst)
           (Expr.call "full_viv_recompute_promote_fid" (as := [i64, i32]) (bs := [])
              (Arg.var h, Arg.var rsn_bv, ()) fun _ => Expr.jump Js_rs.fst ()))
        (Expr.jump Js_rs.fst ()))
    (Expr.jump J (Arg.var qlen, ()))

theorem s13_deduce_large_rsn_wp (Γ : Env)
    (hPromote : ∀ a m Q X, step13VivRecomputePromoteSpec a m Q X →
      Γ "full_viv_recompute_promote_fid" [i64, i32] [] a m Q X)
    (hSubCl : ∀ a m Q X, fullVivSubsumesClM6Spec a m Q X →
      Γ "full_viv_subsumes_cl_m6" [i64, i32, i32] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {mrk_b lm1 : List (BitVec 8)} {ws1_b ws2_b : List (BitVec 32)} {asz_b rsz_b : BitVec 64}
    {qlen_c qi1 : Val i64} {cref sz rsn_bv v_bv olen : Val i32} {taut : Val .bool}
    {idx0 : Nat} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    {J_brk : Cont [i64, i64, i32, .bool]} {J : Cont [i64]}
    (hspW : S13SparseInvNoMark c F0 F_cur s)
    (hqb : VivQueueOk c s mrk_b ws1_b qlen_c.toNat)
    (hlm1_len : lm1.length = 2 * c.max_vars) (hws2_b : ws2_b.length = 2 * c.max_vars)
    (hsub_b : S13SubRefOk s asz_b)
    (href_r : rsn_bv.toNat ∈ fullArenaClauseRefs s)
    (hng_r : fullArenaClauseGarb s rsn_bv.toNat = false)
    (hidx0 : idx0 < s.core.trail_end) (htrl0 : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = v_bv.toNat)
    (hlits_r : ∀ q ∈ fullArenaClauseLitsCore s.core rsn_bv.toNat,
      q = (s.core.trl[idx0]?.getD 0#32).toNat ∨
      ∃ m < idx0, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
        (s.core.lvl[q / 2]?.getD 0#32).toNat ≤
          (s.core.lvl[(s.core.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hm : (FullMem c { s with
      core := { s.core with mrk := mrk_b, lit_mark := lm1 }
      scratch := { s.scratch with
        work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_b } } ⋆ R) m)
    (hJ : ∀ (qlen' : Val i64) (ar_n mclr_n : List (BitVec 32)) (mrk_n : List (BitVec 8))
        (ws1_n : List (BitVec 32)) (asz_n rsz_n : BitVec 64) mlg,
      let s_n : FullState := { s with
        core := { s.core with arena := ar_n, min_clr := mclr_n, mrk := mrk_n, lit_mark := lm1 }
        scratch := { s.scratch with
          work_stk1 := ws1_n, work_stk2 := ws2_b, ant_sz := asz_n, res_sz := rsz_n } }
      S13SparseInvNoMark c F0 F_cur s_n →
      S13ArPres s { s with core := { s.core with arena := ar_n, min_clr := mclr_n } } →
      qlen_c.toNat ≤ qlen'.toNat → qlen'.toNat ≤ s.core.cur_vars →
      (∀ j < qlen_c.toNat, ws1_n[j]? = ws1_b[j]?) →
      VivQueueOk c s mrk_n ws1_n qlen'.toNat → S13SubRefOk s_n asz_n →
      (∀ q ∈ fullArenaClauseLitsCore s.core rsn_bv.toNat, q / 2 ≠ v_bv.toNat →
        (s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨
        q / 2 ∈ (ws1_n.take qlen'.toNat).map BitVec.toNat) →
      (FullMem c s_n ⋆ R) mlg → J (qlen', ()) mlg)
    (hJ_brk : ∀ (ar_n mclr_n : List (BitVec 32)) (rsz_n : BitVec 64) mb,
      let s_n : FullState := { s with
        core := { s.core with arena := ar_n, min_clr := mclr_n, mrk := mrk_b, lit_mark := lm1 }
        scratch := { s.scratch with
          work_stk1 := ws1_b, work_stk2 := ws2_b,
          ant_sz := rsn_bv.setWidth 64, res_sz := rsz_n } }
      S13SparseInvNoMark c F0 F_cur s_n →
      S13ArPres s { s with core := { s.core with arena := ar_n, min_clr := mclr_n } } →
      S13SubRefOk s_n (rsn_bv.setWidth 64) → (FullMem c s_n ⋆ R) mb →
      J_brk (qlen_c, qi1, olen, taut, ()) mb) :
    wp Γ Q X (s13DeduceLargeRsnExpr c.hdr (BitVec.ofNat 64 s.core.cur_vars)
      c.pMark c.pLevel c.pArena c.pWorkStk1 cref sz rsn_bv v_bv qlen_c qi1 olen taut
      J_brk J) m := by
  have hw := hspW.2.1; have hcl := hspW.1.core_ok
  have hcap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hcap hmx
  have hcv_le := hcl.cur_vars_le; have hte_le := hcl.trail_end_le
  have har_len := hcl.arena_len_arr; have halen_le := hcl.arena_len_le
  have hwf_r := hw.arena.refs_wf rsn_bv.toNat href_r
  have hbd_r :
      rsn_bv.toNat + 3 + fullArenaClauseSizeCore s.core rsn_bv.toNat ≤ s.core.arena.length := by
    omega
  dsimp only [s13DeduceLargeRsnExpr, fvOp32]
  fvt_to_group
  refine wp_join_group (ts := [])
      (fun _ m_rs => ∃ (ar_1 mclr_1 : List (BitVec 32)) (rsz_1 : BitVec 64),
        let s1 : FullState := { s with core := { s.core with arena := ar_1, min_clr := mclr_1 } }
        S13SparseInvNoMark c F0 F_cur
          { s1 with
            core := { s1.core with mrk := mrk_b, lit_mark := lm1 }
            scratch := { s1.scratch with
              work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_1 } } ∧
        S13ArPres s s1 ∧
        (FullMem c { s1 with
          core := { s1.core with mrk := mrk_b, lit_mark := lm1 }
          scratch := { s1.scratch with
            work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_b, res_sz := rsz_1 } } ⋆ R) m_rs)
      (fun _ _ m_rs ⟨ar_1, mclr_1, rsz_1, hsp_1, hpres_1, hm_rs⟩ => by
        let s1 : FullState := { s with core := { s.core with arena := ar_1, min_clr := mclr_1 } }
        have hw1 := hsp_1.2.1; have hcl1 := hsp_1.1.core_ok
        have href_1 : rsn_bv.toNat ∈ fullArenaClauseRefs s1 := hpres_1.1.symm ▸ href_r
        have hng_1 : fullArenaClauseGarb s1 rsn_bv.toNat = false := by
          change fullArenaClauseGarb s1 rsn_bv.toNat = false
          rw [(hpres_1.2 rsn_bv.toNat href_r).1]; exact hng_r
        have hwf_1 := hw1.arena.refs_wf rsn_bv.toNat href_1
        have har1_len : ar_1.length = c.arena_cap := hcl1.arena_len_arr
        have hs1_len : s1.core.arena_len = s.core.arena_len := rfl
        have hs1_ar : s1.core.arena = ar_1 := rfl
        have hbd_1 :
            rsn_bv.toNat + 3 + fullArenaClauseSizeCore s1.core rsn_bv.toNat ≤ ar_1.length := by
          have h1 := hwf_1.2.2.1; have hnext := hwf_1.2.2.2.1; have h2 := hcl1.arena_len_le
          have hsz_same : fullArenaClauseSizeCore { s1.core with mrk := mrk_b, lit_mark := lm1 }
              rsn_bv.toNat = fullArenaClauseSizeCore s1.core rsn_bv.toNat := rfl
          dsimp only [s1] at *; omega
        have hrsn_ar : rsn_bv.toNat < ar_1.length := by
          have := hwf_1.2.1; omega
        have hrsn_2 : (rsn_bv.setWidth 64 + 2#64).toNat < ar_1.length := by
          have := hwf_1.1; have := hcl1.arena_len_le; bv_omega
        have hrsn_2_mod : (rsn_bv.toNat + 2) % 18446744073709551616 = rsn_bv.toNat + 2 :=
          Nat.mod_eq_of_lt (by have := hwf_1.1; omega)
        have hrsn_2_eq : (rsn_bv.setWidth 64 + 2#64).toNat = rsn_bv.toNat + 2 := by
          have := hwf_1.1; bv_omega
        let rsz_bv := ar_1[(rsn_bv.setWidth 64 + 2#64).toNat]'hrsn_2
        have hrsz_raw : ar_1[rsn_bv.toNat + 2]'(by omega) = rsz_bv := by
          dsimp only [rsz_bv]; simp only [hrsn_2_eq]
        have hrsz_eq : rsz_bv.toNat = fullArenaClauseSizeCore s1.core rsn_bv.toNat := by
          unfold fullArenaClauseSizeCore
          have h2_lt : rsn_bv.toNat + 2 < s1.core.arena.length := by rw [hs1_ar]; omega
          rw [List.getElem?_eq_getElem h2_lt, Option.getD_some]
          dsimp only [s1]; exact congrArg BitVec.toNat hrsz_raw.symm
        have hrsz_s : rsz_bv.toNat = fullArenaClauseSizeCore s.core rsn_bv.toNat := by
          rw [hrsz_eq]; exact (hpres_1.2 rsn_bv.toNat href_r).2.1
        have hlits_1_s : fullArenaClauseLitsCore s1.core rsn_bv.toNat =
            fullArenaClauseLitsCore s.core rsn_bv.toNat := (hpres_1.2 rsn_bv.toNat href_r).2.2
        have hsub_10 : S13SubRefOk s1 asz_b := s13_subRef_of_pres hpres_1 hsub_b
        refine wp_join_group (ts := [])
          (fun _ m_as => ∃ asz_1 : BitVec 64, S13SubRefOk s1 asz_1 ∧
            (FullMem c { s1 with
              core := { s1.core with mrk := mrk_b, lit_mark := lm1 }
              scratch := { s1.scratch with
                work_stk1 := ws1_b, work_stk2 := ws2_b, ant_sz := asz_1, res_sz := rsz_1 } }
              ⋆ R) m_as)
          (fun _ _ m_as ⟨asz_1, hsub_1, hm_as⟩ => by
            fvt_to_group
            refine wp_loop_inv (ts := [i64, i32])
              (fun (qlen_j, j_c, ()) mj => ∃ (mrk_j : List (BitVec 8)) (ws1_j : List (BitVec 32)),
                j_c.toNat ≤ rsz_bv.toNat ∧ qlen_c.toNat ≤ qlen_j.toNat ∧
                qlen_j.toNat ≤ s.core.cur_vars ∧ (∀ k < qlen_c.toNat, ws1_j[k]? = ws1_b[k]?) ∧
                VivQueueOk c s mrk_j ws1_j qlen_j.toNat ∧
                (∀ t < j_c.toNat,
                  (ar_1[rsn_bv.toNat + 3 + t]?.getD 0#32).toNat / 2 ≠ v_bv.toNat →
                  (s.core.lvl[(ar_1[rsn_bv.toNat + 3 + t]?.getD 0#32).toNat / 2]?.getD
                    0#32).toNat = 0 ∨
                  (ar_1[rsn_bv.toNat + 3 + t]?.getD 0#32).toNat / 2 ∈
                    (ws1_j.take qlen_j.toNat).map BitVec.toNat) ∧
                (FullMem c { s1 with
                  core := { s1.core with mrk := mrk_j, lit_mark := lm1 }
                  scratch := { s1.scratch with
                    work_stk1 := ws1_j, work_stk2 := ws2_b,
                    ant_sz := asz_1, res_sz := rsz_1 } } ⋆ R) mj)
              (fun (_, j_c, ()) _ => rsz_bv.toNat - j_c.toNat) ?_ ?_
            · intro Jj hJj; fvt_steps
              exact hJj (qlen_c, 0#32, ()) m_as ⟨mrk_b, ws1_b, by simp, Nat.le_refl _, hqb.2.2.1,
                fun _ _ => rfl, hqb, fun _ h => absurd h (Nat.not_lt_zero _), hm_as⟩
            · rintro Jj ⟨qlen_j, j_c, ⟨⟩⟩ mj
                ⟨mrk_j, ws1_j, hj_le, hq_le_j, hql_j, heq_j, hqj, hcov_j, hmj⟩ ihj
              fvt_step; fvt_step
              · have hj_lt : j_c.toNat < rsz_bv.toNat := by
                  dsimp only [rsz_bv]
                  simpa only [s1, hrsn_2_mod, hrsn_2_eq,
                    show BitVec.toNat (2 : BitVec 64) = 2 from rfl] using hc
                have hj1 : (j_c + 1#32).toNat = j_c.toNat + 1 := by bv_omega
                have hlit_idx : (rsn_bv.setWidth 64 + 3#64 + j_c.setWidth 64).toNat =
                    rsn_bv.toNat + 3 + j_c.toNat := by bv_omega
                have hlit_ar :
                    (rsn_bv.setWidth 64 + 3#64 + j_c.setWidth 64).toNat < ar_1.length := by
                  omega
                fvt_to_group
                · let ol_bv := ar_1[(rsn_bv.setWidth 64 + 3#64 + j_c.setWidth 64).toNat]'hlit_ar
                  let ov_bv := ol_bv >>> 1#32
                  have hol_raw : ar_1[rsn_bv.toNat + 3 + j_c.toNat]'(by omega) = ol_bv := by
                    dsimp only [ol_bv]; simp only [hlit_idx]
                  have hol_mem : ol_bv.toNat ∈ fullArenaClauseLitsCore s1.core rsn_bv.toNat :=
                    (mem_fullArenaClauseLitsCore_iff hbd_1).mpr
                      ⟨j_c.toNat, by rw [← hrsz_eq]; exact hj_lt, congrArg BitVec.toNat hol_raw⟩
                  have hol_mem_s : ol_bv.toNat ∈ fullArenaClauseLitsCore s.core rsn_bv.toNat :=
                    hlits_1_s ▸ hol_mem
                  have hol_lt : ol_bv.toNat < 2 * s.core.cur_vars :=
                    hw.arena.lits_lt rsn_bv.toNat href_r hng_r ol_bv.toNat hol_mem_s
                  have hov_val : ov_bv.toNat = ol_bv.toNat / 2 := bv32_lshr1_toNat _
                  have hov_cv : ov_bv.toNat < s.core.cur_vars := by rw [hov_val]; omega
                  refine wp_join_group (ts := [i64])
                    (fun (qlen', ()) ml => ∃ (mrk_l : List (BitVec 8)) (ws1_l : List (BitVec 32)),
                      qlen_j.toNat ≤ qlen'.toNat ∧ qlen'.toNat ≤ s.core.cur_vars ∧
                      (∀ k < qlen_j.toNat, ws1_l[k]? = ws1_j[k]?) ∧
                      VivQueueOk c s mrk_l ws1_l qlen'.toNat ∧
                      (ov_bv.toNat ≠ v_bv.toNat →
                        (s.core.lvl[ov_bv.toNat]?.getD 0#32).toNat = 0 ∨
                        ov_bv.toNat ∈ (ws1_l.take qlen'.toNat).map BitVec.toNat) ∧
                      (FullMem c { s1 with
                        core := { s1.core with mrk := mrk_l, lit_mark := lm1 }
                        scratch := { s1.scratch with
                          work_stk1 := ws1_l, work_stk2 := ws2_b,
                          ant_sz := asz_1, res_sz := rsz_1 } } ⋆ R) ml)
                    (fun _ ⟨qlen', ⟨⟩⟩ ml
                        ⟨mrk_l, ws1_l, hq_jl, hql_l, heq_l, hql_ok, hcov_ov, hml⟩ => by
                      fvt_steps
                      have hws1_l_len : ws1_l.length = 2 * c.max_vars := hql_ok.2.1
                      refine ihj (qlen', j_c + 1#32, ()) ml (by dsimp only; omega)
                        ⟨mrk_l, ws1_l, by omega, by omega, hql_l,
                         fun k hk => (heq_l k (by omega)).trans (heq_j k hk), hql_ok,
                         fun t ht hne => ?_, hml⟩
                      rcases (by omega : t < j_c.toNat ∨ t = j_c.toNat) with ht' | rfl
                      · refine (hcov_j t ht' hne).elim Or.inl fun hm' => Or.inr ?_
                        obtain ⟨k, hk, hkeq⟩ :=
                          (mem_map_take_iff (by have := hqj.2.1; omega)).mp hm'
                        exact (mem_map_take_iff (by omega)).mpr
                          ⟨k, by omega, by rw [heq_l k hk, hkeq]⟩
                      · have hleq :
                            (ar_1[rsn_bv.toNat + 3 + j_c.toNat]?.getD 0#32).toNat / 2 =
                            ov_bv.toNat := by
                          rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
                            hol_raw, hov_val]
                        rw [hleq] at hne ⊢; exact hcov_ov hne)
                    (fun Jl hJl => by
                      fvt_step; rw [wp_jnz]; constructor <;> intro hc
                      · have hne_bv : ov_bv ≠ v_bv := by
                          simp only [Arg.val_var, bne_iff_ne] at hc; exact hc
                        have hov_ne : ov_bv.toNat ≠ v_bv.toNat :=
                          fun he => hne_bv (BitVec.eq_of_toNat_eq he)
                        have hov_trl : ∃ m < s.core.trail_end,
                            (s.core.trl[m]?.getD 0#32).toNat / 2 = ov_bv.toNat := by
                          rcases hlits_r ol_bv.toNat hol_mem_s with hsame | ⟨m, hm_lt, hmeq, _⟩
                          · exfalso; exact hov_ne (by rw [hov_val, hsame, htrl0])
                          · exact ⟨m, by omega, by rw [hmeq, fullInv_var_xor1, hov_val]⟩
                        have hscl := hspW.1.scratch_ok
                        have hlen_l : s1.LengthsOk c :=
                          s13_deduce_state_len hsp_1.1 hcl.mrk_len hcl.lit_mark_len
                            hscl.work_stk1_len hscl.work_stk2_len
                        have hqj_s1 : VivQueueOk c s1 mrk_j ws1_j qlen_j.toNat :=
                          s13_vivQueue_ar_eq rfl rfl rfl rfl hqj
                        exact s13_push_branch_step (s := s1) hlen_l hqj_s1
                          hov_cv hov_trl hmj
                          fun qlen' mrk_l ws1_l ml hq_jl hql_l heq_l hql_ok hcov_ov hml =>
                            hJl (qlen', ()) ml ⟨mrk_l, ws1_l, hq_jl, hql_l, heq_l,
                              s13_vivQueue_ar_eq rfl rfl rfl rfl hql_ok,
                              fun _ => hcov_ov, hml⟩
                      · have heq_bv : ov_bv = v_bv := by
                          simp only [Arg.val_var, bne_eq_false_iff_eq] at hc; exact hc
                        fvt_steps
                        exact hJl (qlen_j, ()) mj ⟨mrk_j, ws1_j, Nat.le_refl _, hql_j,
                          fun _ _ => rfl, hqj,
                          fun hne => absurd (congrArg BitVec.toNat heq_bv) hne, hmj⟩)
                · have hlt : s.core.arena_len < rsn_bv.toNat + 3 + rsz_bv.toNat := by
                    have hc' := Nat.lt_of_not_ge hc
                    have hlen_m : s.core.arena_len % 2 ^ 64 = s.core.arena_len :=
                      Nat.mod_eq_of_lt (by omega)
                    have hsum_m : (rsn_bv.toNat + 3 + rsz_bv.toNat) % 2 ^ 64 =
                        rsn_bv.toNat + 3 + rsz_bv.toNat := Nat.mod_eq_of_lt (by omega)
                    have hc'' : s.core.arena_len < (rsn_bv.toNat + 3 + rsz_bv.toNat) % 2 ^ 64 := by
                      dsimp only [rsz_bv]
                      simpa only [s1, hrsn_2_mod, hrsn_2_eq, hlen_m,
                        show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
                        show BitVec.toNat (3 : BitVec 64) = 3 from rfl] using hc'
                    omega
                  have : rsn_bv.toNat + 3 + rsz_bv.toNat ≤ s.core.arena_len := by omega
                  omega
              · have hj_eq : j_c.toNat = rsz_bv.toNat := by
                  have hge : rsz_bv.toNat ≤ j_c.toNat := Nat.not_lt.mp (by
                    dsimp only [rsz_bv] at *
                    simpa only [s1, hrsn_2_mod, hrsn_2_eq,
                      show BitVec.toNat (2 : BitVec 64) = 2 from rfl] using hc)
                  exact Nat.le_antisymm hj_le hge
                have hcov_l : ∀ q ∈ fullArenaClauseLitsCore s.core rsn_bv.toNat,
                    q / 2 ≠ v_bv.toNat →
                    (s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨
                    q / 2 ∈ (ws1_j.take qlen_j.toNat).map BitVec.toNat := by
                  intro q hq hne
                  rw [← hlits_1_s] at hq
                  obtain ⟨t, ht, hqt⟩ := (mem_fullArenaClauseLitsCore_iff hbd_1).mp hq
                  have ht_lt : rsn_bv.toNat + 3 + t < ar_1.length := by omega
                  rw [← hrsz_eq] at ht
                  have hc' := hcov_j t (by omega)
                    (by rw [List.getElem?_eq_getElem ht_lt, Option.getD_some, hqt]; exact hne)
                  rwa [List.getElem?_eq_getElem ht_lt, Option.getD_some, hqt] at hc'
                let s_out : FullState := { s with
                  core := { s.core with
                    arena := ar_1, min_clr := mclr_1, mrk := mrk_j, lit_mark := lm1 }
                  scratch := { s.scratch with
                    work_stk1 := ws1_j, work_stk2 := ws2_b, ant_sz := asz_1, res_sz := rsz_1 } }
                have hsp_out : S13SparseInvNoMark c F0 F_cur s_out :=
                  ⟨s13_deduce_state_len hsp_1.1 hqj.1 hlm1_len hqj.2.1 hws2_b,
                   { hsp_1.2.1 with
                     arena := { hsp_1.2.1.arena with len_ok := hsp_1.2.1.arena.len_ok }
                     watches := hsp_1.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
                   hsp_1.2.2.1, hsp_1.2.2.2.1, hsp_1.2.2.2.2⟩
                exact hJ qlen_j ar_1 mclr_1 mrk_j ws1_j asz_1 rsz_1 mj hsp_out hpres_1
                  hq_le_j hql_j heq_j hqj hsub_1 hcov_l hmj)
          (fun Jas hJas => by
            fvt_steps
            · c0_call hSubCl
              refine ⟨c, F0, F_cur, _, R, rfl,
                s13_deduce_state_len hsp_1.1 hqb.1 hlm1_len hqb.2.1 hws2_b,
                s13_deduce_state_witness hw1, href_1, hng_1, hm_rs, fun ok => ?_⟩
              fvt_steps
              · exact hJ_brk ar_1 mclr_1 rsz_1 _
                  (s13_deduce_state_noMark hsp_1 hqb.1 hlm1_len hqb.2.1 hws2_b)
                  hpres_1 (s13_subRef_set_ref href_1 hng_1) (by assumption)
              · exact hJas () m_rs ⟨asz_b, hsub_10, hm_rs⟩
            · exact hJas () m_rs ⟨asz_b, hsub_10, hm_rs⟩))
      (fun Jrs hJrs => by
        fvt_steps
        · c0_call hPromote
          refine ⟨c, F0, F_cur, _, R, rfl,
            s13_deduce_state_noMark hspW hqb.1 hlm1_len hqb.2.1 hws2_b,
            href_r, hng_r, hm, fun ar' mclr' mp hsp' hrefs' hpres' hmp => ?_⟩
          exact hJrs () mp ⟨ar', mclr', 1#64, hsp', s13ArPres_of_fields hrefs' hpres', hmp⟩
        · exact hJrs () m ⟨s.core.arena, s.core.min_clr, rsz_b,
            s13_deduce_state_noMark hspW hqb.1 hlm1_len hqb.2.1 hws2_b,
            s13ArPres_refl s, hm⟩)

/-! ## 4. `s13_deduce_phase2_dec_wp` -/

theorem s13_deduce_phase2_dec_wp (Γ : Env) {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s1 sb : FullState} {R : Mem 64 → Prop}
    {mrk_b : List (BitVec 8)} {ws1_b ws2_b : List (BitVec 32)}
    {cref implied olen_c : Val i32} {qi_c qlen_c : Val i64} {taut_c : Val .bool}
    {idx0 : Nat} {m : Mem 64} {Q : Post [i32]} {X : XPost} {J : Cont [i32, .bool]}
    (hw1 : FullWitnessInv c F0 F_cur s1.core) (hcv_le : s1.core.cur_vars ≤ c.max_vars)
    (hws2_b : ws2_b.length = 2 * c.max_vars)
    (hqb : VivQueueOk c s1 mrk_b ws1_b qlen_c.toNat)
    (hcb : VivClosedOk s1 implied ws1_b ws2_b qi_c.toNat qlen_c.toNat olen_c.toNat taut_c)
    (hob : VivOutOk s1 implied ws1_b ws2_b qi_c.toNat olen_c.toNat taut_c)
    (hsdb : VivSeedOk s1 cref implied ws1_b ws2_b qlen_c.toNat olen_c.toNat taut_c)
    (himp : implied ≠ 0xFFFFFFFF#32 →
      implied.toNat < 2 * s1.core.cur_vars ∧ s1.core.vals[implied.toNat]?.getD 0#8 = 1#8)
    (hqi_lt : qi_c.toNat < qlen_c.toNat) (hidx0 : idx0 < s1.core.trail_end)
    (htrl0 : (s1.core.trl[idx0]?.getD 0#32).toNat / 2 = (ws1_b[qi_c.toNat]?.getD 0#32).toNat)
    (hrsn_ff : s1.core.rsns[(ws1_b[qi_c.toNat]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 =
      0xFFFFFFFF#32)
    (hsb_ws2 : sb.scratch.work_stk2 = ws2_b) (hm : (FullMem c sb ⋆ R) m)
    (hJ : ∀ (olen' : Val i32) (taut' : Val .bool) md ws2_d, ws2_d.length = 2 * c.max_vars →
      VivClosedOk s1 implied ws1_b ws2_d (qi_c.toNat + 1) qlen_c.toNat olen'.toNat taut' →
      VivOutOk s1 implied ws1_b ws2_d (qi_c.toNat + 1) olen'.toNat taut' →
      VivSeedOk s1 cref implied ws1_b ws2_d qlen_c.toNat olen'.toNat taut' →
      (FullMem c { sb with scratch := { sb.scratch with work_stk2 := ws2_d } } ⋆ R) md →
      J (olen', taut', ()) md) :
    let tl_bv := s1.core.trl[idx0]?.getD 0#32
    wp Γ Q X
      (fvOp32 (OpCode.cmp .eq i32 .bool (by decide)) (Arg.var tl_bv, Arg.var implied, ()) fun p =>
       Expr.jnz (Arg.var p.fst) (Expr.jump J (Arg.var olen_c, Arg.imm (t := .bool) true, ()))
         (Expr.group (sig := [[i32]]) (fun _ => Blocks.cons (fun p =>
            Expr.jump J (Arg.var p.fst, Arg.var taut_c, ())) Blocks.nil) fun Js_o =>
          fvOp32 (OpCode.zext 32 64) (Arg.var olen_c, ()) fun po =>
          fvOp32 (OpCode.cmp .ult i64 .bool (by decide))
            (Arg.var po.fst, Arg.var (BitVec.ofNat 64 s1.core.cur_vars), ()) fun p =>
          Expr.jnz (Arg.var p.fst)
            (fvOp32 (OpCode.zext 32 64) (Arg.var olen_c, ()) fun p =>
             fvOp32 (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
             fvOp32 (OpCode.add i64) (Arg.var c.pWorkStk2, Arg.var p.fst, ()) fun p =>
             fvOp32 (OpCode.xor i32) (Arg.var tl_bv, Arg.imm 1, ()) fun px =>
             Expr.store (Arg.var px.fst) (Arg.var p.fst)
               (fvOp32 (OpCode.add i32) (Arg.var olen_c, Arg.imm 1, ()) fun p =>
                Expr.jump Js_o.fst (Arg.var p.fst, ())))
            (Expr.jump Js_o.fst (Arg.var olen_c, ())))) m := by
  intro tl_bv
  have hm' : (FullMem c { sb with scratch := { sb.scratch with work_stk2 := ws2_b } } ⋆ R) m := by
    simpa only [← hsb_ws2] using hm
  clear hm
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have htl_lt : tl_bv.toNat < 2 * s1.core.cur_vars := hw1.trail_lits_lt idx0 hidx0
  dsimp only [fvOp32]
  fvt_step; fvt_step
  · fvt_steps
    exact hJ olen_c true m ws2_b hws2_b (s13_vivClosed_taut_true hcb hrsn_ff)
      (fun h => by cases h) (fun h => by cases h) hm'
  · have htl_ne : tl_bv ≠ implied := by c0_bound
    refine wp_join_group (ts := [i32])
      (fun (olen', ()) mo => ∃ ws2_o : List (BitVec 32), ws2_o.length = 2 * c.max_vars ∧
        VivClosedOk s1 implied ws1_b ws2_o (qi_c.toNat + 1) qlen_c.toNat olen'.toNat taut_c ∧
        VivOutOk s1 implied ws1_b ws2_o (qi_c.toNat + 1) olen'.toNat taut_c ∧
        VivSeedOk s1 cref implied ws1_b ws2_o qlen_c.toNat olen'.toNat taut_c ∧
        (FullMem c { sb with scratch := { sb.scratch with work_stk2 := ws2_o } } ⋆ R) mo)
      (fun _ ⟨olen', ⟨⟩⟩ mo ⟨ws2_o, hws2_o, hco, hoo, hsdo, hmo⟩ => by
        rw [Blocks.get_here]; fvt_steps
        exact hJ olen' taut_c mo ws2_o hws2_o hco hoo hsdo hmo)
      (fun Jo hJo => by
        c0_hstraight; c0_hsplit
        · have hol_lt : olen_c.toNat < s1.core.cur_vars := by
            have h1 : (olen_c.setWidth 64).toNat < (BitVec.ofNat 64 s1.core.cur_vars).toNat := by
              c0_bound
            rwa [bv32_setWidth64_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
          have hol_ws2 : olen_c.toNat < ws2_b.length := by rw [hws2_b]; omega
          have hol_ws2_64 : (olen_c.setWidth 64).toNat < ws2_b.length := by
            rw [bv32_setWidth64_toNat]; exact hol_ws2
          have hol1 : (olen_c + 1#32).toNat = olen_c.toNat + 1 := by bv_omega
          fvt_steps
          let ws2_o := ws2_b.set olen_c.toNat (tl_bv ^^^ 1#32)
          have hws2_o_len : ws2_o.length = 2 * c.max_vars := by simp [ws2_o, hws2_b]
          cases taut_c with
          | true =>
            refine hJo (olen_c + 1#32, ()) _ ⟨ws2_o, hws2_o_len,
              s13_vivClosed_taut_true hcb hrsn_ff, (fun h => by cases h),
              (fun h => by cases h), ?_⟩
            dsimp only [ws2_o]; rw [← bv32_setWidth64_toNat]; assumption
          | false =>
            have hpush := vivOut_push_step hw1 hqb hqi_lt hob hcb himp
              hidx0 htrl0 hrsn_ff (fun _ => htl_ne) hws2_b hcv_le
            have hco : VivClosedOk s1 implied ws1_b ws2_o (qi_c.toNat + 1) qlen_c.toNat
                (olen_c + 1#32).toNat false := by rw [hol1]; exact hpush.2.2.2.1
            have hoo : VivOutOk s1 implied ws1_b ws2_o (qi_c.toNat + 1)
                (olen_c + 1#32).toNat false := by rw [hol1]; exact hpush.2.2.1
            have hsdo : VivSeedOk s1 cref implied ws1_b ws2_o qlen_c.toNat
                (olen_c + 1#32).toNat false := by
              rw [hol1]
              exact s13_vivSeed_mono_ws2 hsdb (by omega) (by omega) (by omega)
                (fun j hj => hpush.2.2.2.2 j hj)
            refine hJo (olen_c + 1#32, ()) _ ⟨ws2_o, hws2_o_len, hco, hoo, hsdo, ?_⟩
            dsimp only [ws2_o]; rw [← bv32_setWidth64_toNat]; assumption
        · have hol_ge : s1.core.cur_vars ≤ olen_c.toNat := by
            have h1 :
                ¬((olen_c.setWidth 64).toNat < (BitVec.ofNat 64 s1.core.cur_vars).toNat) := by
              c0_bound
            rw [bv32_setWidth64_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
            omega
          fvt_steps
          cases taut_c with
          | true =>
            exact hJo (olen_c, ()) m ⟨ws2_b, hws2_b, s13_vivClosed_taut_true hcb hrsn_ff,
              (fun h => by cases h), (fun h => by cases h), hm'⟩
          | false =>
            have hol_lt := (vivOut_push_lt hw1 hqb hcv_le hqi_lt hob himp hidx0 htrl0
              (fun _ => htl_ne) (by have := (hob rfl).1; omega)).1
            omega)

end S13DeduceHelpers

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

end
