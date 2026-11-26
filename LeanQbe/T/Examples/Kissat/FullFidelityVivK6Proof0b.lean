/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityVivK6
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof3b
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof0
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
import LeanQbe.T.Examples.Kissat.FullM7ParityVivTiersProof0
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Dynamic Vivification Proofs (`FullFidelityVivK6Proof0b`)

UNSAT-only `Func.wp` proofs (`public section`, `0 @[expose]`, `0 import all`, `std3`) for
`GAP-VIV-01/02`: `full_viv_collect_fid_wp`, `full_viv_count_fid_wp`, `full_viv_sort_fid_wp`,
`full_vivify_tier_m6_hdr_fid_wp`, and `full_vivify_m6_hdr_fid_wp`.
-/

set_option autoImplicit false

local elab "fvt_steps_np" : tactic => LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

local elab "fvt_to_group_np" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityVivK6

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
/-! ## 3. Dynamic Vivification Specs & `Func.wp` Proofs (`GAP-VIV-01/02`) -/

section VivFidSpecs

/-- Stride-1 `full_viv_collect_fid(h, tier_mode)` collecting up to `h->red_cap` clause refs. -/
def fullVivCollectFidSpec : Spec [i64, i64] [i64] := fun (h, _tier_mode, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ bn rr' m',
      bn.toNat ≤ c.red_cap → rr'.length = c.red_cap →
      (∀ k < bn.toNat, (rr'[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) →
      (FullMem c { s with scratch := { s.scratch with red_refs := rr' } } ⋆ R) m' → Q (bn, ()) m'

/-- Stride-1 `full_viv_count_fid(h, bn)` accumulating literal counts in `tarjan_reach`. -/
def fullVivCountFidSpec : Spec [i64, i64] [] := fun (h, bn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ bn.toNat ≤ c.red_cap ∧
    (∀ k < bn.toNat, (s.scratch.red_refs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ tr' m',
      tr'.length = 2 * c.max_vars →
      (FullMem c { s with scratch := { s.scratch with tarjan_reach := tr' } } ⋆ R) m' → Q () m'

/-- 2-key Shell sort `full_viv_sort2_fid(h, bn, mode)` for modes 1 (`3*bn <= red_cap`) and
2 (`2*bn <= scratch_cap`). -/
def fullVivSort2FidSpec : Spec [i64, i64, i64] [] := fun (h, bn, mode, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ bn.toNat ≤ c.red_cap ∧
    ((mode = 1#64 ∧ 3 * bn.toNat ≤ c.red_cap) ∨ (mode = 2#64 ∧ 2 * bn.toNat ≤ c.scratch_cap)) ∧
    (∀ k < bn.toNat, (s.scratch.red_refs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ rr' scr' m',
      rr'.length = c.red_cap → scr'.length = c.scratch_cap →
      (∀ k < bn.toNat, (rr'[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) →
      (FullMem c { s with scratch := { s.scratch with red_refs := rr', scratch_buf := scr' } } ⋆ R)
        m' → Q () m'

/-- Dynamic key-storage `full_viv_sort_fid(h, bn)` sorting `red_refs[0 ..< bn)`. -/
def fullVivSortFidSpec : Spec [i64, i64] [] := fun (h, bn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ bn.toNat ≤ c.red_cap ∧
    (∀ k < bn.toNat, (s.scratch.red_refs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ rr' scr' m',
      rr'.length = c.red_cap → scr'.length = c.scratch_cap →
      (∀ k < bn.toNat, (rr'[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) →
      (FullMem c { s with scratch := { s.scratch with red_refs := rr', scratch_buf := scr' } } ⋆ R)
        m' → Q () m'

theorem fullVivCollectFidSpec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost} (h : fullVivCollectFidSpec xs m Q X) :
    fullVivCollectFidSpec xs m Q X' := by rcases xs with ⟨_, _, ⟨⟩⟩; exact h

theorem fullVivCountFidSpec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post []} {X X' : XPost} (h : fullVivCountFidSpec xs m Q X) :
    fullVivCountFidSpec xs m Q X' := by rcases xs with ⟨_, _, ⟨⟩⟩; exact h

theorem fullVivSort2FidSpec_monoX {xs : Tup Val [i64, i64, i64]} {m : Mem 64}
    {Q : Post []} {X X' : XPost} (h : fullVivSort2FidSpec xs m Q X) :
    fullVivSort2FidSpec xs m Q X' := by rcases xs with ⟨_, _, _, ⟨⟩⟩; exact h

theorem fullVivSortFidSpec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post []} {X X' : XPost} (h : fullVivSortFidSpec xs m Q X) :
    fullVivSortFidSpec xs m Q X' := by rcases xs with ⟨_, _, ⟨⟩⟩; exact h

theorem fullVivCollectFidSpec_intro {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {R : Mem 64 → Prop} {h tier_mode : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hh : h = c.hdr) (hsp : FullSparseInv c F0 s) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ bn rr' m',
      bn.toNat ≤ c.red_cap → rr'.length = c.red_cap →
      (∀ k < bn.toNat, (rr'[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) →
      (FullMem c { s with scratch := { s.scratch with red_refs := rr' } } ⋆ R) m' → Q (bn, ()) m') :
    fullVivCollectFidSpec (h, tier_mode, ()) m Q X :=
  ⟨c, F0, s, R, hh, hsp, hm, hQ⟩

theorem fullVivCountFidSpec_intro {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {R : Mem 64 → Prop} {h bn : BitVec 64} {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hsp : FullSparseInv c F0 s) (hbn : bn.toNat ≤ c.red_cap)
    (hrr : ∀ k < bn.toNat, (s.scratch.red_refs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ tr' m', tr'.length = 2 * c.max_vars →
      (FullMem c { s with scratch := { s.scratch with tarjan_reach := tr' } } ⋆ R) m' → Q () m') :
    fullVivCountFidSpec (h, bn, ()) m Q X :=
  ⟨c, F0, s, R, hh, hsp, hbn, hrr, hm, hQ⟩

theorem fullVivSortFidSpec_intro {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {R : Mem 64 → Prop} {h bn : BitVec 64} {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hsp : FullSparseInv c F0 s) (hbn : bn.toNat ≤ c.red_cap)
    (hrr : ∀ k < bn.toNat, (s.scratch.red_refs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ rr' scr' m', rr'.length = c.red_cap → scr'.length = c.scratch_cap →
      (∀ k < bn.toNat, (rr'[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) →
      (FullMem c { s with scratch := { s.scratch with red_refs := rr', scratch_buf := scr' } } ⋆ R)
        m' → Q () m') :
    fullVivSortFidSpec (h, bn, ()) m Q X :=
  ⟨c, F0, s, R, hh, hsp, hbn, hrr, hm, hQ⟩

end VivFidSpecs

section VivFidProofs

open FullVivTopTactics FullVivTop FullM6VivBackbone FullM6OrchAdapters FullM6Hdr
open scoped FullArenaTactics FullVivTopTactics

private theorem fid_sparse_with_rr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {rr' : List (BitVec 32)} (hrr : rr'.length = c.red_cap) :
    FullSparseInv c F0 { s with scratch := { s.scratch with red_refs := rr' } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with red_refs_len := hrr }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem fid_sparse_with_tr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {tr' : List (BitVec 32)} (htr : tr'.length = 2 * c.max_vars) :
    FullSparseInv c F0 { s with scratch := { s.scratch with tarjan_reach := tr' } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with tarjan_reach_len := htr }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem fid_sparse_with_rr_scr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {rr' scr' : List (BitVec 32)} (hrr : rr'.length = c.red_cap)
    (hscr : scr'.length = c.scratch_cap) :
    FullSparseInv c F0
      { s with scratch := { s.scratch with red_refs := rr', scratch_buf := scr' } } :=
  ⟨⟨⟨h.1.lengths.core_ok,
      { h.1.lengths.scratch_ok with red_refs_len := hrr, scratch_buf_len := hscr }⟩,
    h.1.witness⟩, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem fid_sparse_with_res_sz {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (rsz : BitVec 64) :
    FullSparseInv c F0 { s with scratch := { s.scratch with res_sz := rsz } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem fid_sparse_with_ticks {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (st : BitVec 64) :
    FullSparseInv c F0 { s with scratch := { s.scratch with search_ticks := st } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem fid_sparseInv_of_core_eq {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullSparseInv c F0 s) (hlen' : s'.LengthsOk c) (hcore : s'.core = s.core)
    (hpres : FullM6Hdr.M6HdrScratchPres s s') : FullSparseInv c F0 s' := by
  obtain ⟨hcore_inv, hmc, hvn, hsc, hdm⟩ := h
  refine ⟨⟨hlen', ?_⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨F_cur, hw⟩ := hcore_inv.2
    exact ⟨F_cur, by rw [hcore]; exact hw⟩
  · unfold FullLitMarksClear FullMrkZero; rw [hcore]; exact hmc
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    rw [hcore]; exact hvn
  · exact ⟨fun i hi => by
      have hll : s'.scratch.last_learned[i]? = s.scratch.last_learned[i]? := by
        rw [hpres.extPres.1]
      dsimp only [FullLastLearnedWf] at hsc ⊢
      rw [hll]
      rcases hsc.1 i hi with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (by unfold fullArenaClauseRefs; rw [hcore]; exact h2),
      by rw [hpres.extPres.2]; exact hsc.2⟩
  · rw [hcore]; exact hdm

private theorem fid_sparseInvW_of_prop_canon {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' unfl' : BitVec 64} {wvec' arena' wstk' : List (BitVec 32)}
    {wlen' : Nat} {wu' fuel' ctype' cref' c0' c1' oom' ticks' : BitVec 64}
    {wsort' : List (BitVec 32)} {phases' : List (BitVec 8)} {delayed' : List (BitVec 32)}
    (hlen' : ({ s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                            fuel := fuel', confl_type := ctype', confl_ref := cref',
                            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort',
                                  phases := phases', delayed := delayed' } } :
      FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                    trail_pos := tp', trail_end := te', propagated := prop',
                    unassigned := unass', unflushed := unfl', wvec := wvec', arena := arena',
                    wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                    confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                    confl_lit1 := c1', oom := oom' })
    (hperm : FullArenaPermEq s.core
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                    trail_pos := tp', trail_end := te', propagated := prop',
                    unassigned := unass', unflushed := unfl', wvec := wvec', arena := arena',
                    wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                    confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                    confl_lit1 := c1', oom := oom' }) :
    FullSparseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                              unassigned := unass', unflushed := unfl', wvec := wvec',
                              arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                              fuel := fuel', confl_type := ctype', confl_ref := cref',
                              confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := { s.scratch with
          search_ticks := ticks', wsort := wsort', phases := phases', delayed := delayed' } } := by
  let s' : FullState :=
    { s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                            fuel := fuel', confl_type := ctype', confl_ref := cref',
                            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort',
                                  phases := phases', delayed := delayed' } }
  have hnd' : FullArenaVarsNodup s' := fun ref href hng => by
    have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 ref href0 (hgb.symm.trans hng))
  have hrefs : ∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s' := fun ref hr => by
    change ref ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact hr
  exact FullVivTop.fullSparseInvW_of_prop_state hsp hlen' hw' hnd'
    ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hrefs

private theorem fid_ext_pres_compose {ext ext1 ext2 : List (BitVec 64)}
    (h1 : M6HdrExtInitOk ext → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext ext1)
    (h2 : M6HdrExtInitOk ext1 → M6HdrExtInitOk ext2 ∧ M6ExtW2bPres ext1 ext2) :
    M6HdrExtInitOk ext → M6HdrExtInitOk ext2 ∧ M6ExtW2bPres ext ext2 := fun hi =>
  ⟨(h2 (h1 hi).1).1, (h1 hi).2.trans (h2 (h1 hi).1).2⟩

theorem full_viv_collect_fid_wp (Γ : Env)
    (hNext : ∀ a m Q X, Full.fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hTierMatch : ∀ a m Q X, fullVivTierMatchM6Spec a m Q X →
      Γ "full_viv_tier_match_m6" [i64, i32, i64] [.bool] a m Q X) :
    ∀ a m Q X, fullVivCollectFidSpec a m Q X →
      Func.wp Γ full_viv_collect_fid_body a m Q X := by
  rintro ⟨h, tier_mode, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp0, hm0, hQ⟩
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred
  unfold dimacsBound at har_cap hmx hrc
  obtain ⟨F_cur0, hsw0⟩ := hsp0.exists_witness
  have hal0 : s.core.arena_len ≤ c.arena_cap := hsp0.1.lengths.core_ok.arena_len_le
  have har0_len : s.core.arena.length = c.arena_cap := hsp0.1.lengths.core_ok.arena_len_arr
  have hrr0_len : s.scratch.red_refs.length = c.red_cap := hsp0.1.lengths.scratch_ok.red_refs_len
  have h0_mem : 0 = s.core.arena_len ∨ 0 ∈ fullArenaClauseRefs s := by
    rcases Nat.eq_zero_or_pos s.core.arena_len with h0 | hpos
    · exact Or.inl h0.symm
    · exact Or.inr (fullArenaClauseRefs_zero_mem hsw0.2.1.arena hpos)
  unfold Func.wp full_viv_collect_fid_body
  fvt_steps
  refine wp_loop_inv (ts := [i64, i64])
    (fun (bn, pass, ()) mo => ∃ rro : List (BitVec 32),
      pass.toNat ≤ 2 ∧ bn.toNat ≤ c.red_cap ∧ rro.length = c.red_cap ∧
      (∀ k < bn.toNat, (rro[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
      (FullMem c { s with scratch := { s.scratch with red_refs := rro } } ⋆ R) mo)
    (fun (_, pass, ()) _ => 2 - pass.toNat)
    (fun Jo hJo => by
      fvt_steps
      exact hJo (0#64, 0#64, ()) m0 ⟨s.scratch.red_refs, Nat.zero_le _, Nat.zero_le _,
        hrr0_len, fun _ hk => by simp at hk, hm0⟩)
    (fun Jo ⟨bn0, pass, ⟨⟩⟩ mo ⟨rro, hpass_le, hbn0_le, hrro_len, hoko, hmo⟩ iho => ?_)
  fvt_steps
  · have hpass_lt : pass.toNat < 2 := by c0_bound
    have hpass1 : (pass + 1#64).toNat = pass.toNat + 1 := by bv_omega
    refine wp_loop_inv (ts := [i64, i64])
      (fun (bn, p, ()) mp => ∃ rrp : List (BitVec 32),
        p.toNat ≤ s.core.arena_len ∧
        (p.toNat = s.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s) ∧
        bn.toNat ≤ c.red_cap ∧ rrp.length = c.red_cap ∧
        (∀ k < bn.toNat, (rrp[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
        (FullMem c { s with scratch := { s.scratch with red_refs := rrp } } ⋆ R) mp)
      (fun (_, p, ()) _ => s.core.arena_len - p.toNat)
      (fun J1 hJ1 => by
        fvt_steps
        exact hJ1 (bn0, 0#64, ()) mo ⟨rro, Nat.zero_le _, h0_mem, hbn0_le, hrro_len, hoko, hmo⟩)
      (fun J1 ⟨bn, p, ⟨⟩⟩ mp ⟨rrp, hp_le, hp_mem, hbn_le, hrrp_len, hokp, hmp⟩ ih1 => ?_)
    fvt_steps
    · have hp_lt : p.toNat < s.core.arena_len := by c0_bound
      have hp_ref : p.toNat ∈ fullArenaClauseRefs s := hp_mem.resolve_left (by omega)
      have hwfp := hsw0.2.1.arena.refs_wf p.toNat hp_ref
      have hp_lt_ar : p.toNat < s.core.arena.length := by omega
      have hp32 : (p.setWidth 32).toNat = p.toNat := by bv_omega
      fvt_steps
      c0_call hNext
      refine ⟨c, { s with scratch := { s.scratch with red_refs := rrp } },
        R, rfl, ⟨hsp0.1.lengths.core_ok,
          { hsp0.1.lengths.scratch_ok with red_refs_len := hrrp_len }⟩,
        hmp, ?_⟩
      let np_nat := fullArenaNextOff s.core.arena s.core.arena_len (p.setWidth 32).toNat
      have hnb : p.toNat < np_nat ∧ np_nat ≤ s.core.arena_len := by
        dsimp only [np_nat]; rw [hp32]; exact fullArenaNextOff_bounds hwfp.1
      have hnp_mem : np_nat = s.core.arena_len ∨ np_nat ∈ fullArenaClauseRefs s := by
        dsimp only [np_nat]; rw [hp32]
        exact fullArenaClauseRefs_next_mem_or_end hsw0.2.1.arena hp_ref
      have hnp_bv : ((BitVec.ofNat 32 np_nat).setWidth 64).toNat = np_nat := by
        rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)]
      dsimp only; fvt_to_group
      refine wp_join_group (ts := [i64])
        (fun (bn', ()) mn => ∃ rrn : List (BitVec 32),
          bn'.toNat ≤ c.red_cap ∧ rrn.length = c.red_cap ∧
          (∀ k < bn'.toNat, (rrn[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
          (FullMem c { s with scratch := { s.scratch with red_refs := rrn } } ⋆ R) mn) ?_ ?_
      · rintro _ ⟨bn', ⟨⟩⟩ mn ⟨rrn, hbn'_le, hrrn_len, hokn, hmn⟩
        fvt_steps
        exact ih1 (bn', (BitVec.ofNat 32 np_nat).setWidth 64, ()) mn
          (by dsimp only; rw [hnp_bv]; omega)
          ⟨rrn, by rw [hnp_bv]; exact hnb.2, by rw [hnp_bv]; exact hnp_mem,
            hbn'_le, hrrn_len, hokn, hmn⟩
      · intro Jn hJn
        c0_hsplit
        · fvt_to_group
          refine wp_join_group (ts := [i32]) (fun _ mw => mp = mw) ?_
            (fun Jw hJw => by fvt_steps <;> exact hJw _ mp rfl)
          rintro _ ⟨want, ⟨⟩⟩ _ rfl
          fvt_to_group
          refine wp_join_group (ts := [i64])
            (fun (bn', ()) mn => ∃ rrn : List (BitVec 32),
              bn'.toNat ≤ c.red_cap ∧ rrn.length = c.red_cap ∧
              (∀ k < bn'.toNat, (rrn[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
              (FullMem c { s with scratch := { s.scratch with red_refs := rrn } } ⋆ R) mn)
            (fun _ x mn hx => hJn x mn hx)
            (fun Jt hJt => by
              c0_hsplit
              · c0_call hTierMatch
                refine ⟨c, { s with scratch := { s.scratch with red_refs := rrp } }, R, rfl, hmp,
                  fun matched => ?_⟩
                fvt_steps
                · have hbn_lt : bn.toNat < c.red_cap := by c0_bound
                  have hbn1 : (bn + 1#64).toNat = bn.toNat + 1 := by bv_omega
                  fvt_steps
                  refine hJt (bn + 1#64, ()) _ ⟨_, by rw [hbn1]; omega, by simp [hrrp_len], ?_, hm⟩
                  intro k hk
                  rw [hbn1] at hk
                  by_cases hke : k = bn.toNat
                  · subst hke; rw [List.getElem?_set_self (by omega), Option.getD_some, hp32]
                    exact hp_ref
                  · rw [List.getElem?_set_ne (by omega)]; exact hokp k (by omega)
                · exact hJt (bn, ()) mp ⟨rrp, hbn_le, hrrp_len, hokp, hmp⟩
                · exact hJt (bn, ()) mp ⟨rrp, hbn_le, hrrp_len, hokp, hmp⟩
              · fvt_steps; exact hJt (bn, ()) mp ⟨rrp, hbn_le, hrrp_len, hokp, hmp⟩)
        · fvt_steps; exact hJn (bn, ()) mp ⟨rrp, hbn_le, hrrp_len, hokp, hmp⟩
    · fvt_steps
      exact iho (bn, pass + 1#64, ()) mp (by dsimp only; rw [hpass1]; omega)
        ⟨rrp, by rw [hpass1]; omega, hbn_le, hrrp_len, hokp, hmp⟩
  · fvt_steps; exact hQ bn0 rro mo hbn0_le hrro_len hoko hmo
  · fvt_steps; exact hQ bn0 rro mo hbn0_le hrro_len hoko hmo

theorem full_viv_count_fid_wp (Γ : Env) :
    ∀ a m Q X, fullVivCountFidSpec a m Q X →
      Func.wp Γ full_viv_count_fid_body a m Q X := by
  rintro ⟨h, bn, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp0, hbn_le, hok0, hm0, hQ⟩
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred
  unfold dimacsBound at har_cap hmx hrc
  obtain ⟨F_cur0, hsw0⟩ := hsp0.exists_witness
  have hcv_le := hsp0.1.lengths.core_ok.cur_vars_le
  have har_le := hsp0.1.lengths.core_ok.arena_len_le
  have har_len := hsp0.1.lengths.core_ok.arena_len_arr
  have hrr_len := hsp0.1.lengths.scratch_ok.red_refs_len
  have htr_len := hsp0.1.lengths.scratch_ok.tarjan_reach_len
  have hnlits : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]; omega
  unfold Func.wp full_viv_count_fid_body
  fvt_steps
  -- Zero loop `while (l < nlits)`
  refine wp_loop_inv (ts := [i64])
    (fun (l, ()) ml => ∃ trl : List (BitVec 32),
      l.toNat ≤ 2 * s.core.cur_vars ∧ trl.length = 2 * c.max_vars ∧
      (FullMem c { s with scratch := { s.scratch with tarjan_reach := trl } } ⋆ R) ml)
    (fun (l, ()) _ => 2 * s.core.cur_vars - l.toNat)
    (fun Jl hJl => by fvt_steps; exact hJl (0#64, ()) m0 ⟨s.scratch.tarjan_reach, Nat.zero_le _,
      htr_len, hm0⟩)
    (fun Jl ⟨l, ⟨⟩⟩ ml ⟨trl, hl_le, htrl_len, hml⟩ ihl => ?_)
  fvt_steps
  · have hl_lt : l.toNat < 2 * s.core.cur_vars := by
      have hc' : l.toNat < (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat := by c0_bound
      rwa [hnlits] at hc'
    have hl1 : (l + 1#64).toNat = l.toNat + 1 := by bv_omega
    fvt_steps
    exact ihl (l + 1#64, ()) _ (by dsimp only; rw [hl1]; omega)
      ⟨_, by rw [hl1]; omega, by simp [htrl_len], hm⟩
  · -- Clause count loop `while (bi < bn)`
    refine wp_loop_inv (ts := [i64])
      (fun (bi, ()) mbi => ∃ trb : List (BitVec 32),
        bi.toNat ≤ bn.toNat ∧ trb.length = 2 * c.max_vars ∧
        (FullMem c { s with scratch := { s.scratch with tarjan_reach := trb } } ⋆ R) mbi)
      (fun (bi, ()) _ => bn.toNat - bi.toNat)
      (fun Jb hJb => by fvt_steps; exact hJb (0#64, ()) ml ⟨trl, Nat.zero_le _, htrl_len, hml⟩)
      (fun Jb ⟨bi, ⟨⟩⟩ mbi ⟨trb, hbi_le, htrb_len, hmbi⟩ ihb => ?_)
    fvt_steps
    · have hbi_lt : bi.toNat < bn.toNat := by c0_bound
      have hbi1 : (bi + 1#64).toNat = bi.toNat + 1 := by bv_omega
      have hbi_rr : bi.toNat < s.scratch.red_refs.length := by omega
      let cr := s.scratch.red_refs[bi.toNat]'hbi_rr
      have hcr_ref : cr.toNat ∈ fullArenaClauseRefs s := by
        have h := hok0 bi.toNat hbi_lt
        rwa [List.getElem?_eq_getElem hbi_rr, Option.getD_some] at h
      have hwfc := hsw0.2.1.arena.refs_wf cr.toNat hcr_ref
      have hcr2_nat : (cr.setWidth 64 + 2#64).toNat = cr.toNat + 2 := by
        rw [BitVec.toNat_add, zext_toNat cr (by decide), show (2#64).toNat = 2 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      have hcr2_lt : (cr.setWidth 64 + 2#64).toNat < s.core.arena.length := by rw [hcr2_nat]; omega
      let sz := s.core.arena[(cr.setWidth 64 + 2#64).toNat]'hcr2_lt
      have hsz_eq : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat := by
        dsimp only [sz]; unfold fullArenaClauseSizeCore
        rw [List.getElem?_eq_getElem (by omega : cr.toNat + 2 < s.core.arena.length),
          Option.getD_some]
        exact congrArg BitVec.toNat (by simp only [hcr2_nat])
      have hsz_bd : cr.toNat + 3 + sz.toNat ≤ s.core.arena_len := by
        rw [hsz_eq]; exact Nat.le_trans hwfc.2.2.1 hwfc.2.2.2.1
      fvt_steps
      refine wp_loop_inv (ts := [i32])
        (fun (k, ()) mk => ∃ trk : List (BitVec 32),
          k.toNat ≤ sz.toNat ∧ trk.length = 2 * c.max_vars ∧
          (FullMem c { s with scratch := { s.scratch with tarjan_reach := trk } } ⋆ R) mk)
        (fun (k, ()) _ => sz.toNat - k.toNat)
        (fun Jk hJk => by fvt_steps; exact hJk (0#32, ()) mbi ⟨trb, Nat.zero_le _, htrb_len, hmbi⟩)
        (fun Jk ⟨k, ⟨⟩⟩ mk ⟨trk, hk_le, htrk_len, hmk⟩ ihk => ?_)
      fvt_steps
      · have hk_lt : k.toNat < sz.toNat := by c0_bound
        have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
        have hk_idx : (cr.setWidth 64 + 3#64 + k.setWidth 64).toNat =
            cr.toNat + 3 + k.toNat := by
          rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat cr (by decide),
            zext_toNat k (by decide), show (3#64).toNat = 3 from rfl,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        have hk_ar : (cr.setWidth 64 + 3#64 + k.setWidth 64).toNat < s.core.arena.length := by
          rw [hk_idx]; omega
        let lit := s.core.arena[(cr.setWidth 64 + 3#64 + k.setWidth 64).toNat]'hk_ar
        fvt_to_group
        refine wp_join_group (ts := [])
          (fun () m1 => ∃ tr1 : List (BitVec 32), tr1.length = 2 * c.max_vars ∧
            (FullMem c { s with scratch := { s.scratch with tarjan_reach := tr1 } } ⋆ R) m1)
          (fun _ () m1 ⟨tr1, htr1, hm1⟩ => by
            fvt_steps
            exact ihk (k + 1#32, ()) m1 (by dsimp only; rw [hk1]; omega)
              ⟨tr1, by rw [hk1]; omega, htr1, hm1⟩)
          (fun Jif hJif => by
            c0_hsplit
            · have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by
                have h3 : BitVec.toNat (3 : BitVec 64) = 3 := rfl
                have hmod : (cr.toNat + BitVec.toNat (3 : BitVec 64) + k.toNat) % 2 ^ 64 =
                    cr.toNat + 3 + k.toNat := by rw [h3]; omega
                have h2cv : 2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 = 2 * s.core.cur_vars := by
                  omega
                have hlt1 : (s.core.arena[cr.toNat + 3 + k.toNat]'(by omega)).toNat <
                    2 * s.core.cur_vars := by
                  simpa only [cr, hmod, h2cv] using hc
                simpa only [lit, hk_idx] using hlt1
              have hlit_tr : (lit.setWidth 64).toNat < trk.length := by
                rw [zext_toNat lit (by decide), htrk_len]; omega
              fvt_steps
              · exact hJif () _ ⟨_, by simp [htrk_len], hm⟩
              · exact hJif () mk ⟨trk, htrk_len, hmk⟩
            · fvt_steps; exact hJif () mk ⟨trk, htrk_len, hmk⟩)
      · exact ihb (bi + 1#64, ()) mk (by dsimp only; rw [hbi1]; omega)
          ⟨trk, by rw [hbi1]; omega, htrk_len, hmk⟩
    · exact hQ trb mbi htrb_len hmbi

private theorem fid_sort_set_rr_ok {rr : List (BitVec 32)} {cap bn idx : Nat}
    {v : BitVec 32} {refs : List Nat}
    (hlen : rr.length = cap) (_hbn : bn ≤ cap) (hidx : idx < cap)
    (hok : ∀ k < bn, (rr[k]?.getD 0#32).toNat ∈ refs)
    (hv : idx < bn → v.toNat ∈ refs) :
    (rr.set idx v).length = cap ∧
    ∀ k < bn, ((rr.set idx v)[k]?.getD 0#32).toNat ∈ refs := by
  refine ⟨by simp [hlen], fun k hk => ?_⟩
  by_cases hke : k = idx
  · subst hke; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hv hk
  · rw [List.getElem?_set_ne (by omega)]; exact hok k hk

private theorem fid_bv64_shl1 {x : BitVec 64} (hx : x.toNat < 2 ^ 60) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm,
    Nat.mod_eq_of_lt (by omega)]

private theorem fid_bv64_shl1_add1 {x : BitVec 64} (hx : x.toNat < 2 ^ 60) :
    ((x <<< (1 : Nat)) + 1#64).toNat = 2 * x.toNat + 1 := by
  rw [BitVec.toNat_add, fid_bv64_shl1 hx, show (1#64 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega)]

theorem full_viv_sort2_fid_wp (Γ : Env) :
    ∀ a m Q X, fullVivSort2FidSpec a m Q X →
      Func.wp Γ full_viv_sort2_fid_body a m Q X := by
  rintro ⟨h, bn, md, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp0, hbn_le, hmd12, hok0, hm0, hQ⟩
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred; have hsc := c.hscr
  unfold dimacsBound at har_cap hmx hrc hsc
  obtain ⟨F_cur0, hsw0⟩ := hsp0.exists_witness
  have hcv_le := hsp0.1.lengths.core_ok.cur_vars_le
  have har_le := hsp0.1.lengths.core_ok.arena_len_le
  have har_len := hsp0.1.lengths.core_ok.arena_len_arr
  have hrr_len := hsp0.1.lengths.scratch_ok.red_refs_len
  have htr_len := hsp0.1.lengths.scratch_ok.tarjan_reach_len
  have hscr_len := hsp0.1.lengths.scratch_ok.scratch_buf_len
  have hnlits : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]; omega
  let KeysState (rr scr : List (BitVec 32)) : Prop :=
    rr.length = c.red_cap ∧ scr.length = c.scratch_cap ∧
    ∀ k < bn.toNat, (rr[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s
  let KeyPtr (kp : BitVec 64) : Prop :=
    (md = 1#64 ∧ kp = c.pRedRefs + bn * 4 ∧ 3 * bn.toNat ≤ c.red_cap) ∨
    (md = 2#64 ∧ kp = c.pScratchBuf ∧ 2 * bn.toNat ≤ c.scratch_cap)
  have hkey_load : ∀ {kp idx : BitVec 64} {rr scr : List (BitVec 32)} {mk : Mem 64},
      KeyPtr kp → KeysState rr scr → idx.toNat < 2 * bn.toNat →
      (FullMem c { s with scratch := { s.scratch with red_refs := rr, scratch_buf := scr } }
        ⋆ R) mk →
      ∃ v, loadVal mk i32 (kp + idx * 4) = some v := by
    intro kp idx rr scr mk hkp hks hidx hmk
    rcases hkp with ⟨_, rfl, h3⟩ | ⟨_, rfl, h2⟩
    · have haddr : c.pRedRefs + bn * 4 + idx * 4 =
          c.pRedRefs + BitVec.ofNat 64 (4 * (bn.toNat + idx.toNat)) := by
        apply BitVec.eq_of_toNat_eq
        have h4 : (4 : BitVec 64).toNat = 4 := rfl
        simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h4]
        rw [Nat.mul_add]; omega
      have hlt : bn.toNat + idx.toNat < rr.length := by rw [hks.1]; omega
      refine ⟨rr[bn.toNat + idx.toNat]'hlt, ?_⟩
      rw [haddr]
      have hF : (array (t := i32) c.pRedRefs rr ⋆
          (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur
            s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
            FullCoreArrays c s.core ⋆
            (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
             FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
             (array (t := i32) c.pDelayed s.scratch.delayed ⋆
              array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
              array (t := i32) c.pScratchBuf scr)) ⋆ c.pad ⋆ R)) mk := by
        unfold FullMem FullScratchArrays FullScrDynArrs at hmk; exact sep_cast hmk (by ac_rfl)
      exact loadVal_array (t := i32) (by decide) hlt hF
    · have haddr : c.pScratchBuf + idx * 4 = c.pScratchBuf + BitVec.ofNat 64 (4 * idx.toNat) := by
        rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
      have hlt : idx.toNat < scr.length := by rw [hks.2.1]; omega
      refine ⟨scr[idx.toNat]'hlt, ?_⟩
      rw [haddr]
      have hF : (array (t := i32) c.pScratchBuf scr ⋆
          (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur
            s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
            FullCoreArrays c s.core ⋆
            (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
             FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
             (array (t := i32) c.pDelayed s.scratch.delayed ⋆
              array (t := i32) c.pRedRefs rr ⋆
              array (t := i32) c.pExtendStk s.scratch.extend_stk)) ⋆ c.pad ⋆ R)) mk := by
        unfold FullMem FullScratchArrays FullScrDynArrs at hmk; exact sep_cast hmk (by ac_rfl)
      exact loadVal_array (t := i32) (by decide) hlt hF
  have hkey_store : ∀ {kp idx : BitVec 64} (v : BitVec 32) {rr scr : List (BitVec 32)}
      {mk : Mem 64}, KeyPtr kp → KeysState rr scr → idx.toNat < 2 * bn.toNat →
      (FullMem c { s with scratch := { s.scratch with red_refs := rr, scratch_buf := scr } }
        ⋆ R) mk →
      storeOk mk i32 (kp + idx * 4) ∧
      ∃ rr' scr', KeysState rr' scr' ∧
        (FullMem c { s with scratch := { s.scratch with red_refs := rr', scratch_buf := scr' } }
          ⋆ R) (storeMem mk i32 (kp + idx * 4) v) := by
    intro kp idx v rr scr mk hkp hks hidx hmk
    rcases hkp with ⟨_, rfl, h3⟩ | ⟨_, rfl, h2⟩
    · have haddr : c.pRedRefs + bn * 4 + idx * 4 =
          c.pRedRefs + BitVec.ofNat 64 (4 * (bn.toNat + idx.toNat)) := by
        apply BitVec.eq_of_toNat_eq
        have h4 : (4 : BitVec 64).toNat = 4 := rfl
        simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h4]
        rw [Nat.mul_add]; omega
      have hlt : bn.toNat + idx.toNat < rr.length := by rw [hks.1]; omega
      have hF : (array (t := i32) c.pRedRefs rr ⋆
          (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur
            s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
            FullCoreArrays c s.core ⋆
            (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
             FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
             (array (t := i32) c.pDelayed s.scratch.delayed ⋆
              array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
              array (t := i32) c.pScratchBuf scr)) ⋆ c.pad ⋆ R)) mk := by
        unfold FullMem FullScratchArrays FullScrDynArrs at hmk; exact sep_cast hmk (by ac_rfl)
      obtain ⟨hok, hst⟩ := store_array (t := i32) v (by decide) hlt hF
      rw [show (i32 : Ty).bytes = 4 from rfl, ← haddr] at hok hst
      refine ⟨hok, rr.set (bn.toNat + idx.toNat) v, scr,
        ⟨by simp [hks.1], hks.2.1, fun k hk => by
          rw [List.getElem?_set_ne (by omega)]; exact hks.2.2 k hk⟩, ?_⟩
      unfold FullMem FullScratchArrays FullScrDynArrs; exact sep_cast hst (by ac_rfl)
    · have haddr : c.pScratchBuf + idx * 4 = c.pScratchBuf + BitVec.ofNat 64 (4 * idx.toNat) := by
        rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
      have hlt : idx.toNat < scr.length := by rw [hks.2.1]; omega
      have hF : (array (t := i32) c.pScratchBuf scr ⋆
          (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur
            s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
            FullCoreArrays c s.core ⋆
            (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
             FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
             (array (t := i32) c.pDelayed s.scratch.delayed ⋆
              array (t := i32) c.pRedRefs rr ⋆
              array (t := i32) c.pExtendStk s.scratch.extend_stk)) ⋆ c.pad ⋆ R)) mk := by
        unfold FullMem FullScratchArrays FullScrDynArrs at hmk; exact sep_cast hmk (by ac_rfl)
      obtain ⟨hok, hst⟩ := store_array (t := i32) v (by decide) hlt hF
      rw [show (i32 : Ty).bytes = 4 from rfl, ← haddr] at hok hst
      refine ⟨hok, rr, scr.set idx.toNat v,
        ⟨hks.1, by simp [hks.2.1], hks.2.2⟩, ?_⟩
      unfold FullMem FullScratchArrays FullScrDynArrs; exact sep_cast hst (by ac_rfl)
  unfold Func.wp full_viv_sort2_fid_body
  fvt_to_group_np
  refine wp_join_group (ts := [i64]) (fun (kp, ()) mk => m0 = mk ∧ KeyPtr kp) ?_
    (fun Jk hJk => by
      c0_hsplit
      · fvt_steps_np
        have h1 : md = 1#64 := by c0_bound
        rcases hmd12 with ⟨_, h3⟩ | ⟨h2, _⟩
        · exact hJk _ m0 ⟨rfl, Or.inl ⟨h1, rfl, h3⟩⟩
        · exact absurd (h1.symm.trans h2) (by decide)
      · fvt_steps_np
        have hne1 : md ≠ 1#64 := by c0_bound
        rcases hmd12 with ⟨h1, _⟩ | ⟨h2, h2b⟩
        · exact absurd h1 hne1
        · exact hJk _ m0 ⟨rfl, Or.inr ⟨h2, rfl, h2b⟩⟩)
  rintro _ ⟨kp, ⟨⟩⟩ _ ⟨rfl, hkp⟩
  -- Key computation loop `while (bi < bn)`
  refine wp_loop_inv (ts := [i64])
    (fun (bi, ()) mbi => ∃ rr scr, bi.toNat ≤ bn.toNat ∧ KeysState rr scr ∧
      (FullMem c { s with scratch := { s.scratch with red_refs := rr, scratch_buf := scr } }
        ⋆ R) mbi)
    (fun (bi, ()) _ => bn.toNat - bi.toNat)
    (fun Jb hJb => by
      fvt_steps_np
      exact hJb (0#64, ()) m0 ⟨s.scratch.red_refs, s.scratch.scratch_buf, Nat.zero_le _,
        ⟨hrr_len, hscr_len, hok0⟩, hm0⟩)
    (fun Jb ⟨bi, ⟨⟩⟩ mbi ⟨rr, scr, hbi_le, hks, hmbi⟩ ihb => ?_)
  c0_hsplit
  · have hbi_lt : bi.toNat < bn.toNat := by c0_bound
    have hbi1 : (bi + 1#64).toNat = bi.toNat + 1 := by bv_omega
    have hbi_rr : bi.toNat < rr.length := by rw [hks.1]; omega
    let cr := rr[bi.toNat]'hbi_rr
    have hcr_ref : cr.toNat ∈ fullArenaClauseRefs s := by
      have h := hks.2.2 bi.toNat hbi_lt
      rwa [List.getElem?_eq_getElem hbi_rr, Option.getD_some] at h
    have hwfc := hsw0.2.1.arena.refs_wf cr.toNat hcr_ref
    have hcr2_nat : (cr.setWidth 64 + 2#64).toNat = cr.toNat + 2 := by
      rw [BitVec.toNat_add, zext_toNat cr (by decide), show (2#64).toNat = 2 from rfl,
        Nat.mod_eq_of_lt (by omega)]
    have hcr2_lt : (cr.setWidth 64 + 2#64).toNat < s.core.arena.length := by
      rw [hcr2_nat]; omega
    let sz := s.core.arena[(cr.setWidth 64 + 2#64).toNat]'hcr2_lt
    have hsz_eq : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat := by
      dsimp only [sz]; unfold fullArenaClauseSizeCore
      rw [List.getElem?_eq_getElem (by omega : cr.toNat + 2 < s.core.arena.length),
        Option.getD_some]
      exact congrArg BitVec.toNat (by simp only [hcr2_nat])
    have hsz_bd : cr.toNat + 3 + sz.toNat ≤ s.core.arena_len := by
      rw [hsz_eq]; exact Nat.le_trans hwfc.2.2.1 hwfc.2.2.2.1
    fvt_steps_np
    refine wp_loop_inv (ts := [i32, i32, i32, i32, i32])
      (fun (_k0, _d0, _k1, _d1, j, ()) mj => mbi = mj ∧ j.toNat ≤ sz.toNat)
      (fun (_, _, _, _, j, ()) _ => sz.toNat - j.toNat)
      (fun Jj hJj => by fvt_steps_np; exact hJj _ mbi ⟨rfl, Nat.zero_le _⟩)
      (fun Jj ⟨k0, d0, k1, d1, j, ⟨⟩⟩ mj ⟨rfl, hj_le⟩ ihj => ?_)
    c0_hsplit
    · have hj_lt : j.toNat < sz.toNat := by c0_bound
      have hj1 : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
      have hj_idx : (cr.setWidth 64 + 3#64 + j.setWidth 64).toNat =
          cr.toNat + 3 + j.toNat := by
        rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat cr (by decide),
          zext_toNat j (by decide), show (3#64).toNat = 3 from rfl,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have hj_ar : (cr.setWidth 64 + 3#64 + j.setWidth 64).toNat < s.core.arena.length := by
        rw [hj_idx]; omega
      fvt_to_group_np
      refine wp_join_group (ts := [i32]) (fun _ md => mbi = md) ?_
        (fun Jd hJd => by
          c0_hsplit
          · have hl_lt : (s.core.arena[(cr.setWidth 64 + 3#64 + j.setWidth 64).toNat]'hj_ar).toNat
                < 2 * s.core.cur_vars := by
              have hc' : ((s.core.arena[(cr.setWidth 64 + 3#64 +
                  j.setWidth 64).toNat]'hj_ar).setWidth 64).toNat <
                  (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat := by c0_bound
              rwa [zext_toNat _ (by decide), hnlits] at hc'
            fvt_steps_np; exact hJd _ mbi rfl
          · try fvt_steps_np; exact hJd _ mbi rfl)
      rintro _ ⟨dl, ⟨⟩⟩ _ rfl
      fvt_to_group_np
      refine wp_join_group (ts := [i32, i32, i32, i32]) (fun _ mu => mbi = mu)
        (fun _ ⟨k0', d0', k1', d1', ⟨⟩⟩ mu hmu => by
          subst hmu; fvt_steps_np
          exact ihj (k0', d0', k1', d1', j + 1#32, ()) mbi
            (by dsimp only; rw [hj1]; omega) ⟨rfl, by rw [hj1]; omega⟩)
        (fun Ju hJu => by fvt_steps_np <;> exact hJu _ mbi rfl)
    · -- Store `keys[bi << 1] = k0; keys[(bi << 1) + 1] = k1;`
      have hbi2 : (bi <<< (1 : Nat)).toNat = 2 * bi.toNat := fid_bv64_shl1 (by omega)
      have hbi21 : ((bi <<< (1 : Nat)) + 1#64).toNat = 2 * bi.toNat + 1 :=
        fid_bv64_shl1_add1 (by omega)
      fvt_to_group_np
      obtain ⟨hok_k0, rr1, scr1, hks1, hm1⟩ := hkey_store (idx := bi <<< (1 : Nat)) k0
        hkp hks (by rw [hbi2]; omega) hmbi
      refine wp_store_sep ⟨hok_k0, hm1⟩ fun mbi1 hmbi1 => ?_
      obtain ⟨hok_k1, rr2, scr2, hks2, hm2⟩ := hkey_store (idx := (bi <<< (1 : Nat)) + 1#64) k1
        hkp hks1 (by rw [hbi21]; omega) hmbi1
      try fvt_to_group_np
      refine wp_store_sep ⟨hok_k1, hm2⟩ fun mbi2 hmbi2 => ?_
      fvt_steps_np
      exact ihb (bi + 1#64, ()) mbi2 (by dsimp only; rw [hbi1]; omega)
        ⟨rr2, scr2, by rw [hbi1]; omega, hks2, hmbi2⟩
  · -- Shell sort loop `while (gap > 0)` (mode 1/2)
    fvt_to_group_np
    refine wp_loop_inv (ts := [i64])
      (fun (gap, ()) mg => ∃ rrg scrg, gap.toNat ≤ bn.toNat ∧ KeysState rrg scrg ∧
        (FullMem c { s with scratch := { s.scratch with red_refs := rrg, scratch_buf := scrg } }
          ⋆ R) mg)
      (fun (gap, ()) _ => gap.toNat)
      (fun Jg hJg => by
        fvt_steps_np
        have hbn2 : (bn >>> (1 : Nat)).toNat = bn.toNat / 2 := by
          rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
        exact hJg (bn >>> (1 : Nat), ()) mbi ⟨rr, scr, by rw [hbn2]; omega, hks, hmbi⟩)
      (fun Jg ⟨gap, ⟨⟩⟩ mg ⟨rrg, scrg, hgap_le, hksg, hmg⟩ ihg => ?_)
    c0_hsplit
    · have hgap_pos : 0 < gap.toNat := by c0_bound
      have hgap_half : (gap >>> (1 : Nat)).toNat = gap.toNat / 2 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
      fvt_to_group_np
      refine wp_loop_inv (ts := [i64])
        (fun (si, ()) msi => ∃ rrs scrs, gap.toNat ≤ si.toNat ∧ si.toNat ≤ bn.toNat ∧
          KeysState rrs scrs ∧
          (FullMem c { s with scratch := { s.scratch with red_refs := rrs, scratch_buf := scrs } }
            ⋆ R) msi)
        (fun (si, ()) _ => bn.toNat - si.toNat)
        (fun Js hJs => by fvt_steps_np; exact hJs (gap, ()) mg ⟨rrg, scrg, Nat.le_refl _,
          hgap_le, hksg, hmg⟩)
        (fun Js ⟨si, ⟨⟩⟩ msi ⟨rrs, scrs, hsi_lo, hsi_le, hkss, hmsi⟩ ihs => ?_)
      c0_hsplit
      · have hsi_lt : si.toNat < bn.toNat := by c0_bound
        have hsi1 : (si + 1#64).toNat = si.toNat + 1 := by bv_omega
        have hsi_rr : si.toNat < rrs.length := by rw [hkss.1]; omega
        let cr := rrs[si.toNat]'hsi_rr
        have hcr_ref : cr.toNat ∈ fullArenaClauseRefs s := by
          have h := hkss.2.2 si.toNat hsi_lt
          rwa [List.getElem?_eq_getElem hsi_rr, Option.getD_some] at h
        have hwfc := hsw0.2.1.arena.refs_wf cr.toNat hcr_ref
        have hsi2 : (si <<< (1 : Nat)).toNat = 2 * si.toNat := fid_bv64_shl1 (by omega)
        have hsi21 : ((si <<< (1 : Nat)) + 1#64).toNat = 2 * si.toNat + 1 :=
          fid_bv64_shl1_add1 (by omega)
        fvt_to_group_np
        obtain ⟨k0, hlk0⟩ := hkey_load (idx := si <<< (1 : Nat)) hkp hkss
          (by rw [hsi2]; omega) hmsi
        obtain ⟨k1, hlk1⟩ := hkey_load (idx := (si <<< (1 : Nat)) + 1#64) hkp hkss
          (by rw [hsi21]; omega) hmsi
        refine wp_load_of (by dsimp only [Arg.val]; exact hlk0) ?_
        try fvt_to_group_np
        refine wp_load_of (by dsimp only [Arg.val]; exact hlk1) ?_
        have hcr_ar : (cr.setWidth 64).toNat < s.core.arena.length := by
          rw [zext_toNat cr (by decide)]; omega
        fvt_to_group_np
        refine wp_join_group (ts := [i32]) (fun _ m1 => msi = m1) ?_
          (fun Jd0 hJd0 => by
            c0_hsplit
            · have hlt : (k0.setWidth 64).toNat < s.scratch.tarjan_reach.length := by
                have hc' : (k0.setWidth 64).toNat <
                    (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat := by c0_bound
                rw [hnlits] at hc'; omega
              fvt_steps_np; exact hJd0 _ msi rfl
            · try fvt_steps_np; exact hJd0 _ msi rfl)
        rintro _ ⟨dk0, ⟨⟩⟩ _ rfl
        fvt_to_group_np
        refine wp_join_group (ts := [i32]) (fun _ m2 => msi = m2) ?_
          (fun Jd1 hJd1 => by
            c0_hsplit
            · have hlt : (k1.setWidth 64).toNat < s.scratch.tarjan_reach.length := by
                have hc' : (k1.setWidth 64).toNat <
                    (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat := by c0_bound
                rw [hnlits] at hc'; omega
              fvt_steps_np; exact hJd1 _ msi rfl
            · try fvt_steps_np; exact hJd1 _ msi rfl)
        rintro _ ⟨dk1, ⟨⟩⟩ _ rfl
        -- Inner Shell shift loop `while (sj >= gap)`
        refine wp_loop_break_group (brkTs := [i64]) (lpTs := [i64])
          (fun (sj_f, ()) msf => ∃ rrf scrf, sj_f.toNat < bn.toNat ∧ KeysState rrf scrf ∧
            (FullMem c { s with scratch := { s.scratch with red_refs := rrf, scratch_buf := scrf } }
              ⋆ R) msf)
          (fun rem (sj, ()) msj => ∃ rrj scrj, sj.toNat < bn.toNat ∧ rem = sj.toNat ∧
            KeysState rrj scrj ∧
            (FullMem c { s with scratch := { s.scratch with red_refs := rrj, scratch_buf := scrj } }
              ⋆ R) msj) ?_ ?_ ?_
        · rintro _ ⟨sj_f, ⟨⟩⟩ msf ⟨rrf, scrf, hsjf_lt, hksf, hmsf⟩
          have hsjf_rr : sj_f.toNat < rrf.length := by rw [hksf.1]; omega
          have hsjf2 : (sj_f <<< (1 : Nat)).toNat = 2 * sj_f.toNat := fid_bv64_shl1 (by omega)
          have hsjf21 : ((sj_f <<< (1 : Nat)) + 1#64).toNat = 2 * sj_f.toNat + 1 :=
            fid_bv64_shl1_add1 (by omega)
          fvt_to_group_np
          have hksf0 : KeysState (rrf.set sj_f.toNat cr) scrf :=
            ⟨by simp [hksf.1], hksf.2.1,
              (fid_sort_set_rr_ok hksf.1 hbn_le (by omega) hksf.2.2 (fun _ => hcr_ref)).2⟩
          obtain ⟨hok_f0, rrf1, scrf1, hksf1, hmf1⟩ := hkey_store
            (idx := sj_f <<< (1 : Nat)) k0 hkp hksf0 (by rw [hsjf2]; omega) hm
          refine wp_store_sep ⟨hok_f0, hmf1⟩ fun mf1 hmf1' => ?_
          obtain ⟨hok_f1, rrf2, scrf2, hksf2, hmf2⟩ := hkey_store
            (idx := (sj_f <<< (1 : Nat)) + 1#64) k1 hkp hksf1 (by rw [hsjf21]; omega) hmf1'
          try fvt_to_group_np
          refine wp_store_sep ⟨hok_f1, hmf2⟩ fun mf2 hmf2' => ?_
          fvt_steps_np
          exact ihs (si + 1#64, ()) mf2 (by dsimp only; rw [hsi1]; omega)
            ⟨rrf2, scrf2, by rw [hsi1]; omega, by rw [hsi1]; omega, hksf2, hmf2'⟩
        · intro B L rem ⟨sj, ⟨⟩⟩ msj hB hL ⟨rrj, scrj, hsj_lt, hrem, hksj, hmsj⟩
          subst hrem
          c0_hsplit
          · have hge : gap.toNat ≤ sj.toNat := by c0_bound
            have hpj_nat : (sj - gap).toNat = sj.toNat - gap.toNat := by
              rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hge)]
            have hpj_lt : (sj - gap).toNat < bn.toNat := by omega
            have hpj_rr : (sj - gap).toNat < rrj.length := by rw [hksj.1]; omega
            let pcr := rrj[(sj - gap).toNat]'hpj_rr
            have hpcr_ref : pcr.toNat ∈ fullArenaClauseRefs s := by
              have h := hksj.2.2 (sj - gap).toNat hpj_lt
              rwa [List.getElem?_eq_getElem hpj_rr, Option.getD_some] at h
            have hwfp := hsw0.2.1.arena.refs_wf pcr.toNat hpcr_ref
            have hpj2 : ((sj - gap) <<< (1 : Nat)).toNat = 2 * (sj - gap).toNat :=
              fid_bv64_shl1 (by have := hrc; have := hsc; have := hbn_le; omega)
            have hpj21 : (((sj - gap) <<< (1 : Nat)) + 1#64).toNat =
                2 * (sj - gap).toNat + 1 :=
              fid_bv64_shl1_add1 (by have := hrc; have := hsc; have := hbn_le; omega)
            fvt_to_group_np
            obtain ⟨pk0, hlpk0⟩ := hkey_load (idx := (sj - gap) <<< (1 : Nat)) hkp hksj
              (by rw [hpj2]; omega) hmsj
            obtain ⟨pk1, hlpk1⟩ := hkey_load (idx := ((sj - gap) <<< (1 : Nat)) + 1#64)
              hkp hksj (by rw [hpj21]; omega) hmsj
            try fvt_to_group_np
            refine wp_load_of (by dsimp only [Arg.val]; exact hlpk0) ?_
            try fvt_to_group_np
            refine wp_load_of (by dsimp only [Arg.val]; exact hlpk1) ?_
            have hpcr_ar : (pcr.setWidth 64).toNat < s.core.arena.length := by
              rw [zext_toNat pcr (by decide)]; omega
            fvt_to_group_np
            refine wp_join_group (ts := [i32]) (fun _ m3 => msj = m3) ?_
              (fun Jdp0 hJdp0 => by
                c0_hsplit
                · have hlt : (pk0.setWidth 64).toNat < s.scratch.tarjan_reach.length := by
                    have hc' : (pk0.setWidth 64).toNat <
                        (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat := hc
                    rw [hnlits] at hc'; omega
                  fvt_steps_np; exact hJdp0 _ msj rfl
                · try fvt_steps_np; exact hJdp0 _ msj rfl)
            rintro _ ⟨dpk0, ⟨⟩⟩ _ rfl
            fvt_to_group_np
            refine wp_join_group (ts := [i32]) (fun _ m4 => msj = m4) ?_
              (fun Jdp1 hJdp1 => by
                c0_hsplit
                · have hlt : (pk1.setWidth 64).toNat < s.scratch.tarjan_reach.length := by
                    have hc' : (pk1.setWidth 64).toNat <
                        (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat := hc
                    rw [hnlits] at hc'; omega
                  fvt_steps_np; exact hJdp1 _ msj rfl
                · try fvt_steps_np; exact hJdp1 _ msj rfl)
            rintro _ ⟨dpk1, ⟨⟩⟩ _ rfl
            refine wp_join_group (ts := []) (fun () mc => msj = mc)
              (fun _ () mc hmc => by
                subst hmc
                refine wp_join_group (ts := []) (fun () mc2 => msj = mc2)
                  (fun _ () mc2 hmc2 => by
                    subst hmc2
                    have hsj_rr : sj.toNat < rrj.length := by rw [hksj.1]; omega
                    have hsj2 : (sj <<< (1 : Nat)).toNat = 2 * sj.toNat := fid_bv64_shl1 (by omega)
                    have hsj21 : ((sj <<< (1 : Nat)) + 1#64).toNat = 2 * sj.toNat + 1 :=
                      fid_bv64_shl1_add1 (by omega)
                    fvt_to_group_np
                    have hksj0 : KeysState (rrj.set sj.toNat pcr) scrj :=
                      ⟨by simp [hksj.1], hksj.2.1,
                        (fid_sort_set_rr_ok hksj.1 hbn_le (by omega) hksj.2.2
                          (fun _ => hpcr_ref)).2⟩
                    obtain ⟨hok_s0, rrj1, scrj1, hksj1, hms1⟩ := hkey_store
                      (idx := sj <<< (1 : Nat)) pk0 hkp hksj0 (by rw [hsj2]; omega) hm
                    refine wp_store_sep ⟨hok_s0, hms1⟩ fun ms1 hms1' => ?_
                    obtain ⟨hok_s1, rrj2, scrj2, hksj2, hms2⟩ := hkey_store
                      (idx := (sj <<< (1 : Nat)) + 1#64) pk1 hkp hksj1 (by rw [hsj21]; omega)
                      hms1'
                    try fvt_to_group_np
                    refine wp_store_sep ⟨hok_s1, hms2⟩ fun ms2 hms2' => ?_
                    fvt_steps_np
                    exact hL (sj - gap).toNat (sj - gap, ()) ms2 (by rw [hpj_nat]; omega)
                      ⟨rrj2, scrj2, hpj_lt, rfl, hksj2, hms2'⟩)
                  (fun Jc2 hJc2 => by
                    c0_hsplit
                    · c0_hsplit
                      · try fvt_to_group_np
                        exact hB (sj, ()) msj ⟨rrj, scrj, hsj_lt, hksj, hmsj⟩
                      · refine wp_join_group (ts := []) (fun () m1 => msj = m1)
                          (fun _ () m1 hm1 => by subst hm1; exact hJc2 () msj rfl)
                          fun J1 hJ1 => by
                            c0_hsplit
                            · c0_hsplit
                              · try fvt_to_group_np
                                exact hB (sj, ()) msj ⟨rrj, scrj, hsj_lt, hksj, hmsj⟩
                              · refine wp_join_group (ts := []) (fun () m2 => msj = m2)
                                  (fun _ () m2 hm2 => by subst hm2; exact hJ1 () msj rfl)
                                  fun J2 hJ2 => by
                                    c0_hsplit
                                    · c0_hsplit
                                      · try fvt_to_group_np
                                        exact hB (sj, ()) msj ⟨rrj, scrj, hsj_lt, hksj, hmsj⟩
                                      · fvt_steps_np <;> first
                                          | exact hB (sj, ()) msj ⟨rrj, scrj, hsj_lt, hksj, hmsj⟩
                                          | exact hJ2 () msj rfl
                                    · try fvt_to_group_np
                                      exact hJ2 () msj rfl
                            · try fvt_to_group_np
                              exact hJ1 () msj rfl
                    · try fvt_to_group_np
                      exact hJc2 () msj rfl))
              (fun Jc hJc => by
                fvt_steps_np
                all_goals first
                  | exact hB (sj, ()) msj ⟨rrj, scrj, hsj_lt, hksj, hmsj⟩
                  | exact hJc () msj rfl)
          · try fvt_steps_np
            exact hB (sj, ()) msj ⟨rrj, scrj, hsj_lt, hksj, hmsj⟩
        · intro B L _ hL; fvt_steps_np
          exact hL si.toNat (si, ()) msi ⟨rrs, scrs, hsi_lt, rfl, hkss, hmsi⟩
      · fvt_steps_np
        exact ihg (gap >>> (1 : Nat), ()) msi (by dsimp only; rw [hgap_half]; omega)
          ⟨rrs, scrs, by rw [hgap_half]; omega, hkss, hmsi⟩
    · fvt_steps_np
      exact hQ rrg scrg mg hksg.1 hksg.2.1 hksg.2.2 hmg

theorem full_viv_sort_fid_wp (Γ : Env)
    (hSort2 : ∀ a m Q X, fullVivSort2FidSpec a m Q X →
      Γ "full_viv_sort2_fid" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullVivSortFidSpec a m Q X →
      Func.wp Γ full_viv_sort_fid_body a m Q X := by
  rintro ⟨h, bn, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp0, hbn_le, hok0, hm0, hQ⟩
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred; have hsc := c.hscr
  unfold dimacsBound at har_cap hmx hrc hsc
  obtain ⟨F_cur0, hsw0⟩ := hsp0.exists_witness
  have hcv_le := hsp0.1.lengths.core_ok.cur_vars_le
  have har_le := hsp0.1.lengths.core_ok.arena_len_le
  have har_len := hsp0.1.lengths.core_ok.arena_len_arr
  have hrr_len := hsp0.1.lengths.scratch_ok.red_refs_len
  have htr_len := hsp0.1.lengths.scratch_ok.tarjan_reach_len
  have hscr_len := hsp0.1.lengths.scratch_ok.scratch_buf_len
  have hnlits : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]; omega
  have hret0 : Q () m0 := hQ s.scratch.red_refs s.scratch.scratch_buf m0 hrr_len hscr_len hok0 hm0
  have hmode_rcap3 : (BitVec.ofNat 64 c.red_cap / 3#64).toNat = c.red_cap / 3 := by
    rw [BitVec.toNat_udiv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      show (3#64 : BitVec 64).toNat = 3 from rfl]
  have hmode_scap2 : (BitVec.ofNat 64 c.scratch_cap >>> (1 : Nat)).toNat = c.scratch_cap / 2 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have hmode_rcap2 : (BitVec.ofNat 64 c.red_cap >>> (1 : Nat)).toNat = c.red_cap / 2 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftRight_eq_div_pow, Nat.pow_one]
  unfold Func.wp full_viv_sort_fid_body
  fvt_steps
  · exact hret0
  · have hle : bn.toNat ≤ c.red_cap / 3 := by
      have hc' : bn.toNat ≤ (BitVec.ofNat 64 c.red_cap / 3#64).toNat := by c0_bound
      rwa [hmode_rcap3] at hc'
    c0_call hSort2
    exact ⟨c, F0, s, R, rfl, hsp0, hbn_le, Or.inl ⟨rfl, by omega⟩, hok0, hm0, hQ⟩
  · have hle : bn.toNat ≤ c.scratch_cap / 2 := by
      have hc' : bn.toNat ≤ (BitVec.ofNat 64 c.scratch_cap >>> (1 : Nat)).toNat := by c0_bound
      rwa [hmode_scap2] at hc'
    c0_call hSort2
    exact ⟨c, F0, s, R, rfl, hsp0, hbn_le, Or.inr ⟨rfl, by omega⟩, hok0, hm0, hQ⟩
  · exact hret0
  · -- Mode 3: 1-key sort (`keys1 = rr + bn`, `2 * bn <= c.red_cap`)
    have h2bn : 2 * bn.toNat ≤ c.red_cap := by
      have hc' : ¬ (BitVec.ofNat 64 c.red_cap >>> (1 : Nat)).toNat < bn.toNat := by c0_bound
      rw [hmode_rcap2] at hc'; omega
    have hrr_load1 : ∀ {idx : BitVec 64} {rr : List (BitVec 32)} {mk : Mem 64},
        rr.length = c.red_cap → idx.toNat < bn.toNat →
        (FullMem c { s with scratch := { s.scratch with red_refs := rr } } ⋆ R) mk →
        ∃ v, loadVal mk i32 (c.pRedRefs + bn * 4 + idx * 4) = some v := by
      intro idx rr mk hlen hidx hmk
      have haddr : c.pRedRefs + bn * 4 + idx * 4 =
          c.pRedRefs + BitVec.ofNat 64 (4 * (bn.toNat + idx.toNat)) := by
        apply BitVec.eq_of_toNat_eq
        have h4 : (4 : BitVec 64).toNat = 4 := rfl
        simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h4]
        rw [Nat.mul_add]; omega
      have hlt : bn.toNat + idx.toNat < rr.length := by rw [hlen]; omega
      refine ⟨rr[bn.toNat + idx.toNat]'hlt, ?_⟩
      rw [haddr]
      have hF : (array (t := i32) c.pRedRefs rr ⋆
          (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur
            s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
            FullCoreArrays c s.core ⋆
            (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
             FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
             (array (t := i32) c.pDelayed s.scratch.delayed ⋆
              array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
              array (t := i32) c.pScratchBuf s.scratch.scratch_buf)) ⋆ c.pad ⋆ R)) mk := by
        unfold FullMem FullScratchArrays FullScrDynArrs at hmk; exact sep_cast hmk (by ac_rfl)
      exact loadVal_array (t := i32) (by decide) hlt hF
    have hrr_store1 : ∀ {idx : BitVec 64} (v : BitVec 32) {rr : List (BitVec 32)}
        {mk : Mem 64}, rr.length = c.red_cap →
        (∀ k < bn.toNat, (rr[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) →
        idx.toNat < bn.toNat →
        (FullMem c { s with scratch := { s.scratch with red_refs := rr } } ⋆ R) mk →
        storeOk mk i32 (c.pRedRefs + bn * 4 + idx * 4) ∧
        ∃ rr', rr'.length = c.red_cap ∧
          (∀ k < bn.toNat, (rr'[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
          (FullMem c { s with scratch := { s.scratch with red_refs := rr' } } ⋆ R)
            (storeMem mk i32 (c.pRedRefs + bn * 4 + idx * 4) v) := by
      intro idx v rr mk hlen hok hidx hmk
      have haddr : c.pRedRefs + bn * 4 + idx * 4 =
          c.pRedRefs + BitVec.ofNat 64 (4 * (bn.toNat + idx.toNat)) := by
        apply BitVec.eq_of_toNat_eq
        have h4 : (4 : BitVec 64).toNat = 4 := rfl
        simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h4]
        rw [Nat.mul_add]; omega
      have hlt : bn.toNat + idx.toNat < rr.length := by rw [hlen]; omega
      have hF : (array (t := i32) c.pRedRefs rr ⋆
          (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur
            s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
            FullCoreArrays c s.core ⋆
            (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
             FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
             (array (t := i32) c.pDelayed s.scratch.delayed ⋆
              array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
              array (t := i32) c.pScratchBuf s.scratch.scratch_buf)) ⋆ c.pad ⋆ R)) mk := by
        unfold FullMem FullScratchArrays FullScrDynArrs at hmk; exact sep_cast hmk (by ac_rfl)
      obtain ⟨hso, hst⟩ := store_array (t := i32) v (by decide) hlt hF
      rw [show (i32 : Ty).bytes = 4 from rfl, ← haddr] at hso hst
      refine ⟨hso, rr.set (bn.toNat + idx.toNat) v, by simp [hlen],
        fun k hk => by rw [List.getElem?_set_ne (by omega)]; exact hok k hk, ?_⟩
      unfold FullMem FullScratchArrays FullScrDynArrs; exact sep_cast hst (by ac_rfl)
    -- Key computation loop `while (bi < bn)` (1 key `k0`)
    refine wp_loop_inv (ts := [i64])
      (fun (bi, ()) mbi => ∃ rr, bi.toNat ≤ bn.toNat ∧ rr.length = c.red_cap ∧
        (∀ k < bn.toNat, (rr[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
        (FullMem c { s with scratch := { s.scratch with red_refs := rr } } ⋆ R) mbi)
      (fun (bi, ()) _ => bn.toNat - bi.toNat)
      (fun Jb hJb => by fvt_steps; exact hJb (0#64, ()) m0 ⟨s.scratch.red_refs, Nat.zero_le _,
        hrr_len, hok0, hm0⟩)
      (fun Jb ⟨bi, ⟨⟩⟩ mbi ⟨rr, hbi_le, hlen_r, hok_r, hmbi⟩ ihb => ?_)
    fvt_steps
    · have hbi_lt : bi.toNat < bn.toNat := by c0_bound
      have hbi1 : (bi + 1#64).toNat = bi.toNat + 1 := by bv_omega
      have hbi_rr : bi.toNat < rr.length := by rw [hlen_r]; omega
      let cr := rr[bi.toNat]'hbi_rr
      have hcr_ref : cr.toNat ∈ fullArenaClauseRefs s := by
        have h := hok_r bi.toNat hbi_lt
        rwa [List.getElem?_eq_getElem hbi_rr, Option.getD_some] at h
      have hwfc := hsw0.2.1.arena.refs_wf cr.toNat hcr_ref
      have hcr2_nat : (cr.setWidth 64 + 2#64).toNat = cr.toNat + 2 := by
        rw [BitVec.toNat_add, zext_toNat cr (by decide), show (2#64).toNat = 2 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      have hcr2_lt : (cr.setWidth 64 + 2#64).toNat < s.core.arena.length := by
        rw [hcr2_nat]; omega
      let sz := s.core.arena[(cr.setWidth 64 + 2#64).toNat]'hcr2_lt
      have hsz_eq : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat := by
        dsimp only [sz]; unfold fullArenaClauseSizeCore
        rw [List.getElem?_eq_getElem (by omega : cr.toNat + 2 < s.core.arena.length),
          Option.getD_some]
        exact congrArg BitVec.toNat (by simp only [hcr2_nat])
      have hsz_bd : cr.toNat + 3 + sz.toNat ≤ s.core.arena_len := by
        rw [hsz_eq]; exact Nat.le_trans hwfc.2.2.1 hwfc.2.2.2.1
      fvt_steps
      refine wp_loop_inv (ts := [i32, i32, i32])
        (fun (_k0, _d0, j, ()) mj => mbi = mj ∧ j.toNat ≤ sz.toNat)
        (fun (_, _, j, ()) _ => sz.toNat - j.toNat)
        (fun Jj hJj => by fvt_steps; exact hJj _ mbi ⟨rfl, Nat.zero_le _⟩)
        (fun Jj ⟨k0, d0, j, ⟨⟩⟩ mj ⟨rfl, hj_le⟩ ihj => ?_)
      fvt_steps
      · have hj_lt : j.toNat < sz.toNat := by c0_bound
        have hj1 : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
        have hj_idx : (cr.setWidth 64 + 3#64 + j.setWidth 64).toNat =
            cr.toNat + 3 + j.toNat := by
          rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat cr (by decide),
            zext_toNat j (by decide), show (3#64).toNat = 3 from rfl,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        have hj_ar : (cr.setWidth 64 + 3#64 + j.setWidth 64).toNat < s.core.arena.length := by
          rw [hj_idx]; omega
        fvt_to_group
        refine wp_join_group (ts := [i32]) (fun _ md => mbi = md) ?_
          (fun Jd hJd => by
            fvt_steps
            · have hl_lt : (s.core.arena[(cr.setWidth 64 + 3#64 + j.setWidth 64).toNat]'hj_ar).toNat
                  < 2 * s.core.cur_vars := by
                have hc' : ((s.core.arena[(cr.setWidth 64 + 3#64 +
                    j.setWidth 64).toNat]'hj_ar).setWidth 64).toNat <
                    (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat := by c0_bound
                rwa [zext_toNat _ (by decide), hnlits] at hc'
              fvt_steps; exact hJd _ mbi rfl
            · exact hJd _ mbi rfl)
        rintro _ ⟨dl, ⟨⟩⟩ _ rfl
        fvt_to_group
        refine wp_join_group (ts := [i32, i32]) (fun _ mu => mbi = mu)
          (fun _ ⟨k0', d0', ⟨⟩⟩ mu hmu => by
            subst hmu; fvt_steps
            exact ihj (k0', d0', j + 1#32, ()) mbi
              (by dsimp only; rw [hj1]; omega) ⟨rfl, by rw [hj1]; omega⟩)
          (fun Ju hJu => by fvt_steps_np <;> exact hJu _ mbi rfl)
      · obtain ⟨hok_k, rr1, hlen1, hok1, hm1⟩ := hrr_store1 (idx := bi) k0 hlen_r hok_r
          hbi_lt hmbi
        refine wp_store_sep ⟨hok_k, hm1⟩ fun mbi1 hmbi1 => ?_
        fvt_steps
        exact ihb (bi + 1#64, ()) mbi1 (by dsimp only; rw [hbi1]; omega)
          ⟨rr1, by rw [hbi1]; omega, hlen1, hok1, hmbi1⟩
    · -- 1-key Shell sort `while (gap > 0)`
      refine wp_loop_inv (ts := [i64])
        (fun (gap, ()) mg => ∃ rrg, gap.toNat ≤ bn.toNat ∧ rrg.length = c.red_cap ∧
          (∀ k < bn.toNat, (rrg[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
          (FullMem c { s with scratch := { s.scratch with red_refs := rrg } } ⋆ R) mg)
        (fun (gap, ()) _ => gap.toNat)
        (fun Jg hJg => by
          fvt_steps
          have hbn2 : (bn >>> (1 : Nat)).toNat = bn.toNat / 2 := by
            rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
          exact hJg (bn >>> (1 : Nat), ()) mbi ⟨rr, by rw [hbn2]; omega, hlen_r, hok_r, hmbi⟩)
        (fun Jg ⟨gap, ⟨⟩⟩ mg ⟨rrg, hgap_le, hlen_g, hok_g, hmg⟩ ihg => ?_)
      fvt_steps
      · have hgap_pos : 0 < gap.toNat := by c0_bound
        have hgap_half : (gap >>> (1 : Nat)).toNat = gap.toNat / 2 := by
          rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
        refine wp_loop_inv (ts := [i64])
          (fun (si, ()) msi => ∃ rrs, gap.toNat ≤ si.toNat ∧ si.toNat ≤ bn.toNat ∧
            rrs.length = c.red_cap ∧
            (∀ k < bn.toNat, (rrs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
            (FullMem c { s with scratch := { s.scratch with red_refs := rrs } } ⋆ R) msi)
          (fun (si, ()) _ => bn.toNat - si.toNat)
          (fun Js hJs => by fvt_steps; exact hJs (gap, ()) mg ⟨rrg, Nat.le_refl _, hgap_le,
            hlen_g, hok_g, hmg⟩)
          (fun Js ⟨si, ⟨⟩⟩ msi ⟨rrs, hsi_lo, hsi_le, hlen_s, hok_s, hmsi⟩ ihs => ?_)
        fvt_steps
        · have hsi_lt : si.toNat < bn.toNat := by c0_bound
          have hsi1 : (si + 1#64).toNat = si.toNat + 1 := by bv_omega
          have hsi_rr : si.toNat < rrs.length := by rw [hlen_s]; omega
          let cr := rrs[si.toNat]'hsi_rr
          have hcr_ref : cr.toNat ∈ fullArenaClauseRefs s := by
            have h := hok_s si.toNat hsi_lt
            rwa [List.getElem?_eq_getElem hsi_rr, Option.getD_some] at h
          have hwfc := hsw0.2.1.arena.refs_wf cr.toNat hcr_ref
          obtain ⟨k0, hlk0⟩ := hrr_load1 (idx := si) hlen_s hsi_lt hmsi
          refine wp_load_of (by dsimp only [Arg.val]; exact hlk0) ?_
          have hcr_ar : (cr.setWidth 64).toNat < s.core.arena.length := by
            rw [zext_toNat cr (by decide)]; omega
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i32]) (fun _ m1 => msi = m1) ?_
            (fun Jd0 hJd0 => by
              fvt_steps
              · have hlt : (k0.setWidth 64).toNat < s.scratch.tarjan_reach.length := by
                  have hc' : (k0.setWidth 64).toNat <
                      (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat := by c0_bound
                  rw [hnlits] at hc'; omega
                fvt_steps; exact hJd0 _ msi rfl
              · exact hJd0 _ msi rfl)
          rintro _ ⟨dk0, ⟨⟩⟩ _ rfl
          refine wp_loop_break_group (brkTs := [i64]) (lpTs := [i64])
            (fun (sj_f, ()) msf => ∃ rrf, sj_f.toNat < bn.toNat ∧ rrf.length = c.red_cap ∧
              (∀ k < bn.toNat, (rrf[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
              (FullMem c { s with scratch := { s.scratch with red_refs := rrf } } ⋆ R) msf)
            (fun rem (sj, ()) msj => ∃ rrj, sj.toNat < bn.toNat ∧ rem = sj.toNat ∧
              rrj.length = c.red_cap ∧
              (∀ k < bn.toNat, (rrj[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
              (FullMem c { s with scratch := { s.scratch with red_refs := rrj } } ⋆ R) msj)
            ?_ ?_ ?_
          · rintro _ ⟨sj_f, ⟨⟩⟩ msf ⟨rrf, hsjf_lt, hlen_f, hok_f, hmsf⟩
            have hsjf_rr : sj_f.toNat < rrf.length := by rw [hlen_f]; omega
            c0_hsteps_nogrp
            have hok_f0 := fid_sort_set_rr_ok (idx := sj_f.toNat) hlen_f hbn_le (by omega) hok_f
              (fun _ => hcr_ref)
            obtain ⟨hok_fk, rrf1, hlen_f1, hok_f1, hmf1⟩ := hrr_store1 (idx := sj_f) k0
              hok_f0.1 hok_f0.2 hsjf_lt hm
            refine wp_store_sep ⟨hok_fk, hmf1⟩ fun mf1 hmf1' => ?_
            fvt_steps
            exact ihs (si + 1#64, ()) mf1 (by dsimp only; rw [hsi1]; omega)
              ⟨rrf1, by rw [hsi1]; omega, by rw [hsi1]; omega, hlen_f1, hok_f1, hmf1'⟩
          · intro B L rem ⟨sj, ⟨⟩⟩ msj hB hL ⟨rrj, hsj_lt, hrem, hlen_j, hok_j, hmsj⟩
            subst hrem
            c0_hsplit
            · have hge : gap.toNat ≤ sj.toNat := by c0_bound
              have hpj_nat : (sj - gap).toNat = sj.toNat - gap.toNat := by
                rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hge)]
              have hpj_lt : (sj - gap).toNat < bn.toNat := by omega
              have hpj_rr : (sj - gap).toNat < rrj.length := by rw [hlen_j]; omega
              let pcr := rrj[(sj - gap).toNat]'hpj_rr
              have hpcr_ref : pcr.toNat ∈ fullArenaClauseRefs s := by
                have h := hok_j (sj - gap).toNat hpj_lt
                rwa [List.getElem?_eq_getElem hpj_rr, Option.getD_some] at h
              have hwfp := hsw0.2.1.arena.refs_wf pcr.toNat hpcr_ref
              obtain ⟨pk0, hlpk0⟩ := hrr_load1 (idx := sj - gap) hlen_j hpj_lt hmsj
              c0_hsteps_nogrp
              refine wp_load_of (by dsimp only [Arg.val]; exact hlpk0) ?_
              have hpcr_ar : (pcr.setWidth 64).toNat < s.core.arena.length := by
                rw [zext_toNat pcr (by decide)]; omega
              c0_hsteps_nogrp
              refine wp_join_group (ts := [i32]) (fun _ m3 => msj = m3) ?_
                (fun Jdp0 hJdp0 => by
                  c0_hsplit
                  · have hlt : (pk0.setWidth 64).toNat < s.scratch.tarjan_reach.length := by
                      have hc' : (pk0.setWidth 64).toNat <
                          (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat := hc
                      rw [hnlits] at hc'; omega
                    c0_hsteps!; exact hJdp0 _ msj rfl
                  · c0_hsteps!; exact hJdp0 _ msj rfl)
              rintro _ ⟨dpk0, ⟨⟩⟩ _ rfl
              refine wp_join_group (ts := []) (fun () mc => msj = mc)
                (fun _ () mc hmc => by
                  subst hmc
                  refine wp_join_group (ts := []) (fun () mc2 => msj = mc2)
                    (fun _ () mc2 hmc2 => by
                      subst hmc2
                      have hsj_rr : sj.toNat < rrj.length := by rw [hlen_j]; omega
                      c0_hsteps_nogrp
                      have hok_j0 := fid_sort_set_rr_ok (idx := sj.toNat) hlen_j hbn_le (by omega)
                        hok_j (fun _ => hpcr_ref)
                      obtain ⟨hok_jk, rrj1, hlen_j1, hok_j1, hmj1⟩ := hrr_store1 (idx := sj) pk0
                        hok_j0.1 hok_j0.2 hsj_lt hm
                      refine wp_store_sep ⟨hok_jk, hmj1⟩ fun mj1 hmj1' => ?_
                      fvt_steps_np
                      exact hL (sj - gap).toNat (sj - gap, ()) mj1 (by rw [hpj_nat]; omega)
                        ⟨rrj1, hpj_lt, rfl, hlen_j1, hok_j1, hmj1'⟩)
                    (fun Jc2 hJc2 => by
                      fvt_steps_np
                      all_goals first
                        | exact hB (sj, ()) msj ⟨rrj, hsj_lt, hlen_j, hok_j, hmsj⟩
                        | exact hJc2 () msj rfl))
                (fun Jc hJc => by
                  fvt_steps_np
                  all_goals first
                    | exact hB (sj, ()) msj ⟨rrj, hsj_lt, hlen_j, hok_j, hmsj⟩
                    | exact hJc () msj rfl)
            · exact hB (sj, ()) msj ⟨rrj, hsj_lt, hlen_j, hok_j, hmsj⟩
          · intro B L _ hL; fvt_steps
            exact hL si.toNat (si, ()) msi ⟨rrs, hsi_lt, rfl, hlen_s, hok_s, hmsi⟩
        · exact ihg (gap >>> (1 : Nat), ()) msi (by dsimp only; rw [hgap_half]; omega)
            ⟨rrs, by rw [hgap_half]; omega, hlen_s, hok_s, hmsi⟩
      · exact hQ rrg s.scratch.scratch_buf mg hlen_g hscr_len hok_g hmg

/-- `full_vivify_tier_m6_hdr_fid` (`GAP-VIV-01` dynamic `bmax = red_cap`, `D-01` sort guard,
and `h->res_sz = bi`) satisfies exact `FullM6OrchAdapters.m6aVivifyTierSpec`. -/
theorem full_vivify_tier_m6_hdr_fid_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hCollect : ∀ a m Q X, fullVivCollectFidSpec a m Q X →
      Γ "full_viv_collect_fid" [i64, i64] [i64] a m Q X)
    (hCount : ∀ a m Q X, fullVivCountFidSpec a m Q X →
      Γ "full_viv_count_fid" [i64, i64] [] a m Q X)
    (hSort : ∀ a m Q X, fullVivSortFidSpec a m Q X →
      Γ "full_viv_sort_fid" [i64, i64] [] a m Q X)
    (hVivClause : ∀ a m Q X, FullM6VivBackbone.fullVivClauseM6Spec a m Q X →
      Γ "full_viv_clause_m6" [i64, i32] [i64] a m Q X)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hClearTier : ∀ a m Q X, FullM6VivBackbone.fullVivClearTierM6Spec a m Q X →
      Γ "full_viv_clear_tier_m6" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullM6OrchAdapters.m6aVivifyTierSpec a m Q X →
      Func.wp Γ full_vivify_tier_m6_hdr_fid_body a m Q X := by
  rintro ⟨h, tier_mode, budget0, tick_lim, ⟨⟩⟩ m0 Q X hs
  obtain ⟨c, F0, s, R, rfl, hsp0, hm0, hQ⟩ := FullM6OrchAdapters.m6aVivifyTierSpec_elim hs
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred
  unfold LratBytes.dimacsBound at har_cap hmx hrc
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := hmx
  unfold Func.wp full_vivify_tier_m6_hdr_fid_body; fvt_to_group
  · fvt_steps
    exact hQ 1#64 s m0 hsp0 (fun h => h) (fun h => h) (fun hb => absurd (by c0_bound) hb)
      (Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm0
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ s1 : FullState, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1) ?_ ?_
  · rintro _ ⟨⟩ m ⟨s1, hsp1, hcl1, hfl1, hm⟩
    fvt_steps
    let s2 : FullState := { s1 with core := { s1.core with probing := 1#64 } }
    have hsp2 : FullSparseInv c F0 s2 := FullVivTop.FullSparseInv.with_probing hsp1 1#64
    have hm2 : (FullMem c s2 ⋆ R) m := hm
    have hfl2 : s2.core.fuel.toNat ≤ s.core.fuel.toNat := hfl1
    clear_value s2
    clear hsp1 hcl1 hfl1
    c0_call hCollect
    refine ⟨c, F0, s2, R, rfl, hsp2, hm2, fun bn rr3 m3 hbn_le hrr3 hok3 hm3 => ?_⟩
    let s3 : FullState := { s2 with scratch := { s2.scratch with red_refs := rr3 } }
    have hsp3 : FullSparseInv c F0 s3 := fid_sparse_with_rr hsp2 hrr3
    let SortJoin : Tup Val [] → Mem 64 → Prop := fun () ms =>
      ∃ (s5 : FullState) (rr5 : List (BitVec 32)),
        FullSparseInv c F0 s5 ∧ s5.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        fullArenaClauseRefs s5 = fullArenaClauseRefs s2 ∧
        s5.scratch.red_refs = rr5 ∧ rr5.length = c.red_cap ∧
        (∀ k < bn.toNat, (rr5[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s2) ∧
        (FullMem c s5 ⋆ R) ms
    fvt_to_group
    refine wp_join_group (ts := []) SortJoin ?_ ?_
    · rintro _ ⟨⟩ m5 ⟨s5, rr5, hsp5, hfl5, hrefs5, hrr5, hrr5_len, hok5', hm5'⟩
      c0_hsteps_nogrp
      refine wp_loop_break_group (brkTs := [i64, i64, i64]) (lpTs := [i64, i64])
        (fun (_budget_b, res_b, bi_b, ()) mb => ∃ sb : FullState,
          FullSparseInv c F0 sb ∧ sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          (res_b = 1#64 ∨ res_b = 20#64) ∧ (res_b = 20#64 → F0.Unsat) ∧
          (FullMem c sb ⋆ R) mb)
        (fun rem (budget, bi, ()) mvi => ∃ svi : FullState,
          bi.toNat ≤ bn.toNat ∧ rem = bn.toNat - bi.toNat ∧
          FullSparseInv c F0 svi ∧ svi.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          fullArenaClauseRefs svi = fullArenaClauseRefs s2 ∧
          svi.scratch.red_refs = rr5 ∧ (FullMem c svi ⋆ R) mvi)
        ?_ ?_ ?_
      · rintro _ ⟨_, res_b, bi_b, ⟨⟩⟩ mb ⟨sb, hspb, hflb, hresb, h20b, hmb⟩
        refine wp_join_group (ts := [])
          (fun () m_bt => ∃ sbt : FullState,
            FullSparseInv c F0 sbt ∧ sbt.core.cur_level = 0 ∧
            sbt.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sbt ⋆ R) m_bt) ?_ ?_
        · rintro _ ⟨⟩ m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
          refine wp_join_group (ts := [])
            (fun () m_w => ∃ sw : FullState,
              FullSparseInv c F0 sw ∧ sw.core.cur_level = 0 ∧
              sw.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sw ⋆ R) m_w) ?_ ?_
          · rintro _ ⟨⟩ m_w ⟨sw, hspw, hclw, hflw, hm_w⟩
            fvt_steps
            let sf1 : FullState := { sw with scratch := { sw.scratch with res_sz := bi_b } }
            let sf : FullState := { sf1 with core := { sf1.core with probing := 0#64 } }
            have hspf : FullSparseInv c F0 sf :=
              FullVivTop.FullSparseInv.with_probing (fid_sparse_with_res_sz hspw bi_b) 0#64
            exact hQ res_b sf _ hspf (fun _ => hclw) (fun _ => rfl)
              (fun _ => ⟨hclw, rfl⟩) hflw hresb h20b hm
          · intro Jw hJw
            fvt_steps
            · c0_call hClearTier
              refine ⟨c, F0, sbt, R, rfl, hspbt, hclbt, hm_bt,
                fun sw m_w hspw hclw hflw hm_w =>
                  hJw () m_w ⟨sw, hspw, hclw, by rw [hflw]; exact hflbt, hm_w⟩⟩
            · exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
            · exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
            · exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
        · intro Jbt hJbt
          obtain ⟨F_curb, hswb⟩ := hspb.exists_witness
          have hclb_lt : sb.core.cur_level < 2 ^ 64 := by
            have := hswb.2.1.cur_level_le; have := hspb.1.lengths.core_ok.trail_end_le
            have := hspb.1.lengths.core_ok.cur_vars_le; omega
          fvt_steps
          · c0_call hBacktrack
            refine ⟨c, sb, R, rfl, hspb.1.lengths, hclb_lt,
              (by intro _
                  have := hswb.2.1.cur_level_le; have := hspb.1.lengths.core_ok.trail_end_le
                  have := hspb.1.lengths.core_ok.cur_vars_le; omega),
              hswb.2.1.trail_lits_lt, hmb,
              fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
                hlen_bt _ _ hcl_bt hpres_bt _ _ _ hw_bt _ hm_bt => ?_⟩
            have hsp_bt : FullSparseInv c F0 _ :=
              FullVivTop.FullSparseInv.of_backtrack hspb (Nat.zero_le _) hlen_bt hpres_bt
                (by simpa using hw_bt F0)
            exact hJbt () m_bt ⟨_, hsp_bt, by rw [hcl_bt]; simp, hflb, hm_bt⟩
          · have hclb0 : sb.core.cur_level = 0 := by
              have h0 : (BitVec.ofNat 64 sb.core.cur_level).toNat = 0 := by rw [hc]; rfl
              rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclb_lt] at h0
            exact hJbt () mb ⟨sb, hspb, hclb0, hflb, hmb⟩
      · intro B L rem ⟨budget, bi, ⟨⟩⟩ mvi hB hL
          ⟨svi, hbi_le, hrem, hspv, hflv, hrefsv, hrrv, hmvi⟩
        subst hrem
        fvt_steps
        · have hbi_lt : bi.toNat < bn.toNat := by c0_bound
          have hbi_rr : bi.toNat < svi.scratch.red_refs.length := by rw [hrrv, hrr5_len]; omega
          let cr := svi.scratch.red_refs[bi.toNat]'hbi_rr
          have hcr_ref : cr.toNat ∈ fullArenaClauseRefs svi := by
            rw [hrefsv]
            have h := hok5' bi.toNat hbi_lt
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
            have heq : cr = rr5[bi.toNat]'(by omega) := Option.some.inj (by
              rw [← List.getElem?_eq_getElem hbi_rr, hrrv, List.getElem?_eq_getElem (by omega)])
            rwa [heq]
          obtain ⟨F_curv, hswv⟩ := hspv.exists_witness
          have hbi1 : (bi + 1#64).toNat = bi.toNat + 1 := by bv_omega
          fvt_steps
          c0_call hVivClause
          refine ⟨c, F0, F_curv, svi, R, rfl, hswv, hcr_ref, hmvi,
            fun vc s_vc m_vc hsw_vc hfl_vc _ hrefs_vc hrr_vc hvc h20_vc hm_vc => ?_⟩
          have hrefs_vc2 : fullArenaClauseRefs s_vc = fullArenaClauseRefs s2 :=
            hrefs_vc.trans hrefsv
          have hrr_vc5 : s_vc.scratch.red_refs = rr5 := hrr_vc.trans hrrv
          have hfl_vc' : s_vc.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl_vc hflv
          fvt_steps
          · exact hB (budget - 1#64, 20#64, bi, ()) m_vc
              ⟨s_vc, hsw_vc.toSparse, hfl_vc', Or.inr rfl, fun _ => h20_vc (by c0_bound), hm_vc⟩
          · exact hB (budget - 1#64, 1#64, bi, ()) m_vc
              ⟨s_vc, hsw_vc.toSparse, hfl_vc', Or.inl rfl, (fun h => by cases h), hm_vc⟩
          · have hcl_vc_lt : s_vc.core.cur_level < 2 ^ 64 := by
              have := hsw_vc.2.1.cur_level_le; have := hsw_vc.1.core_ok.trail_end_le
              have := hsw_vc.1.core_ok.cur_vars_le; omega
            have hcl_vc0 : s_vc.core.cur_level = 0 := by
              have h0 : (BitVec.ofNat 64 s_vc.core.cur_level).toNat = 0 := by
                have hc0 : BitVec.ofNat 64 s_vc.core.cur_level = 0#64 := by c0_bound
                rw [hc0]; rfl
              rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_vc_lt] at h0
            c0_call hProp
            refine ⟨c, F0, F_curv, s_vc, R, rfl, hsw_vc.1, hsw_vc.2.1, hsw_vc.2.2.2.2.2, hm_vc,
              fun pr vals_p flags_p lvl_p rsns_p trl_p tp_p te_p prop_p unass_p unfl_p
                wvec_p arena_p wstk_p wlen_p wu_p fuel_p ctype_p cref_p c0_p c1_p oom_p
                ticks_p wsort_p phases_p delayed_p m_p hlen_p hw_p _ hperm_p _ hfl_p _ _ hpr1 _ _
                hm_p => ?_⟩
            let s_p : FullState :=
              { s_vc with
                core := { s_vc.core with
                  vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p,
                  trl := trl_p, trail_pos := tp_p, trail_end := te_p, propagated := prop_p,
                  unassigned := unass_p, unflushed := unfl_p, wvec := wvec_p,
                  arena := arena_p, wstk := wstk_p, wlen := wlen_p, wusable := wu_p,
                  fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
                  confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
                scratch := { s_vc.scratch with
                  search_ticks := ticks_p, wsort := wsort_p, phases := phases_p,
                  delayed := delayed_p } }
            have hsw_p : FullSparseInvW c F0 F_curv s_p :=
              fid_sparseInvW_of_prop_canon hsw_vc hlen_p hw_p hperm_p
            have hrefs_p : fullArenaClauseRefs s_p = fullArenaClauseRefs s_vc := hperm_p.2.1
            have hfl_p' : s_p.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl_p hfl_vc'
            fvt_steps
            · have hpr_eq1 : pr = 1#64 := by c0_bound
              have hunsat : F0.Unsat :=
                FullVivTopSpecs.level0_unsat_of_conflict_okW hw_p hcl_vc0 (hpr1 hpr_eq1).2.2
              exact hB (budget - 1#64, 20#64, bi, ()) m_p
                ⟨s_p, hsw_p.toSparse, hfl_p', Or.inr rfl, fun _ => hunsat, hm_p⟩
            · exact hL (bn.toNat - (bi + 1#64).toNat) (budget - 1#64, bi + 1#64, ()) m_p
                (by rw [hbi1]; omega)
                ⟨s_p, by rw [hbi1]; omega, rfl, hsw_p.toSparse, hfl_p',
                  hrefs_p.trans hrefs_vc2, hrr_vc5, hm_p⟩
          · exact hL (bn.toNat - (bi + 1#64).toNat) (budget - 1#64, bi + 1#64, ()) m_vc
              (by rw [hbi1]; omega)
              ⟨s_vc, by rw [hbi1]; omega, rfl, hsw_vc.toSparse, hfl_vc', hrefs_vc2, hrr_vc5, hm_vc⟩
        · exact hB (budget, 1#64, bi, ()) mvi
            ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
        · exact hB (budget, 1#64, bi, ()) mvi
            ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
        · exact hB (budget, 1#64, bi, ()) mvi
            ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
        · exact hB (budget, 1#64, bi, ()) mvi
            ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
        · exact hB (budget, 1#64, bi, ()) mvi
            ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
      · intro B L _ hL; fvt_steps
        exact hL bn.toNat (budget0, 0#64, ()) m5
          ⟨s5, Nat.zero_le _, by simp, hsp5, hfl5, hrefs5, hrr5, hm5'⟩
    · intro Js hJs
      have hSortBranch : wp Γ Q X
          (Expr.call (as := [i64, i64]) (bs := []) "full_viv_count_fid"
            (Arg.var c.hdr, Arg.var bn, ()) fun _ =>
            Expr.call (as := [i64, i64]) (bs := []) "full_viv_sort_fid"
              (Arg.var c.hdr, Arg.var bn, ()) fun _ =>
              Expr.jump Js ()) m3 := by
        c0_call hCount
        refine ⟨c, F0, s3, R, rfl, hsp3, hbn_le, hok3, hm3, fun tr3 m3c htr3 hm3c => ?_⟩
        let s3c : FullState := { s3 with scratch := { s3.scratch with tarjan_reach := tr3 } }
        have hsp3c : FullSparseInv c F0 s3c := fid_sparse_with_tr hsp3 htr3
        c0_call hSort
        refine ⟨c, F0, s3c, R, rfl, hsp3c, hbn_le, hok3, hm3c,
          fun rr4 scr4 m4 hrr4 hscr4 hok4 hm4 => ?_⟩
        let s4 : FullState :=
          { s3c with scratch := { s3c.scratch with red_refs := rr4, scratch_buf := scr4 } }
        have hsp4 : FullSparseInv c F0 s4 := fid_sparse_with_rr_scr hsp3c hrr4 hscr4
        exact hJs () m4 ⟨s4, rr4, hsp4, hfl2, rfl, rfl, hrr4, hok4, hm4⟩
      fvt_steps
      · exact hSortBranch
      · exact hSortBranch
      · exact hJs () m3 ⟨s3, rr3, hsp3, hfl2, rfl, rfl, hrr3, hok3, hm3⟩
  · intro Jc hJc
    obtain ⟨F_cur0, hsw0⟩ := hsp0.exists_witness
    have hcl0_lt : s.core.cur_level < 2 ^ 64 := by
      have := hsw0.2.1.cur_level_le; have := hsp0.1.lengths.core_ok.trail_end_le
      have := hsp0.1.lengths.core_ok.cur_vars_le; omega
    fvt_steps
    · c0_call hBacktrack
      refine ⟨c, s, R, rfl, hsp0.1.lengths, hcl0_lt,
        (by intro _
            have := hsw0.2.1.cur_level_le; have := hsp0.1.lengths.core_ok.trail_end_le
            have := hsp0.1.lengths.core_ok.cur_vars_le; omega),
        hsw0.2.1.trail_lits_lt, hm0,
        fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m1
          hlen1 _ _ hcl1 hpres1 _ _ _ hw_bt _ hm1 => ?_⟩
      have hsp1 : FullSparseInv c F0 _ :=
        FullVivTop.FullSparseInv.of_backtrack hsp0 (Nat.zero_le _) hlen1 hpres1
          (by simpa using hw_bt F0)
      exact hJc () m1 ⟨_, hsp1, by rw [hcl1]; simp, Nat.le_refl _, hm1⟩
    · have hcl0 : s.core.cur_level = 0 := by
        have h0 : (BitVec.ofNat 64 s.core.cur_level).toNat = 0 := by rw [hc]; rfl
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl0_lt] at h0
      exact hJc () m0 ⟨s, hsp0, hcl0, Nat.le_refl _, hm0⟩

private def FidVivStepInv (c : FullCfg) (F0 : CNF Nat) (ext0 : List (BitVec 64))
    (s0 : FullState) (R : Mem 64 → Prop) (didRun : Prop) :
    Tup Val [i64, i64] → Mem 64 → Prop := fun (r, _lim, ()) mk =>
  ∃ (extk : List (BitVec 64)) (sk : FullState),
    M6HdrExtOk extk ∧ (M6HdrExtInitOk ext0 → M6HdrExtInitOk extk ∧ M6ExtW2bPres ext0 extk) ∧
    FullSparseInv c F0 sk ∧ sk.core.cur_level = 0 ∧
    (didRun → sk.core.probing = 0#64) ∧ (r = 20#64 → sk.core.probing = 0#64) ∧
    sk.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
    (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat) ∧
    (FullMem c sk ⋆ (array64 (c.hdr - 2304) extk ⋆ R)) mk

/-- `full_vivify_m6_hdr_fid` (`GAP-VIV-02` dynamic active-tier `/ sum` normalization using
existing `M6_DELAY_VIVIFYIRR = 3ULL`) satisfies exact `FullM6OrchAdapters.m6aVivifySpec`. -/
theorem full_vivify_m6_hdr_fid_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hSync : ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_sync_legacy_tiers" [i64] [] a m Q X)
    (hDelaying : ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hGetWm : ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [i64] [i64] a m Q X →
      Γ "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X)
    (hVivTier : ∀ a m Q X, FullM6OrchAdapters.m6aVivifyTierSpec a m Q X →
      Γ "full_vivify_tier_m6_hdr" [i64, i64, i64, i64] [i64] a m Q X)
    (hBumpDelay : ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hReduceDelay : ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullM6OrchAdapters.m6aVivifySpec a m Q X →
      Func.wp Γ full_vivify_m6_hdr_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, F0, ext, s, R, rfl, hcfg, hext, hsp, hm, hQ⟩ :=
    FullM6OrchAdapters.m6aVivifySpec_elim hs
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred
  unfold LratBytes.dimacsBound at har_cap hmx hrc
  obtain ⟨F_cur, hw0⟩ := hsp.1.witness
  have hco0 := hsp.1.lengths.core_ok
  have hclv_lt : s.core.cur_level < 2 ^ 64 := by
    have := hw0.cur_level_le; have := hco0.trail_end_le; have := hco0.cur_vars_le; omega
  have hmax_vars_pos : 0 < s.core.cur_level → 0 < c.max_vars := by
    intro _; have := hw0.cur_level_le; have := hco0.trail_end_le
    have := hco0.cur_vars_le; omega
  rw [FullM6Hdr.fullM6HdrMem_iff] at hm
  unfold Func.wp full_vivify_m6_hdr_fid_body; dsimp only; fvt_to_group
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ s1, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      (FullMem c s1 ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) m1)
    (fun _ () m1 ⟨s1, hsp1, hcl01, hfu1, hm1⟩ => ?_) (fun _ hJ => ?_)
  · clear hm
    c0_call hSync
    refine FullM6Hdr.m6HdrW2aSpec_of rfl hcfg hext hsp1.1.lengths
      ((FullM6Hdr.fullM6HdrMem_iff ..).mpr hm1)
      fun () ext2 s2 m2 hcore2 hlen2 hsc2 hext2 hw2 hm2 => ?_
    have hsp2 : FullSparseInv c F0 s2 := fid_sparseInv_of_core_eq hsp1 hlen2 hcore2 hsc2
    have hcl02 : s2.core.cur_level = 0 := by rw [hcore2]; exact hcl01
    refine wp_join_group (ts := [i64])
      (fun (_w0, ()) m3 => ∃ ext3 s3, M6HdrExtOk ext3 ∧
        (M6HdrExtInitOk ext → M6HdrExtInitOk ext3 ∧ M6ExtW2bPres ext ext3) ∧
        FullSparseInv c F0 s3 ∧ s3.core.cur_level = 0 ∧
        s3.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullMem c s3 ⋆ (array64 (c.hdr - 2304) ext3 ⋆ R)) m3) ?_
      (fun Jw0 hJw0 => by
        c0_call hDelaying
        refine FullM6Hdr.m6HdrW2aSpec_of rfl hcfg hext2 hsp2.1.lengths hm2
          fun ⟨del0, ⟨⟩⟩ ext3 s3 m3 hcore3 hlen3 hsc3 hext3 hw3 hm3 => ?_
        have hsp3 : FullSparseInv c F0 s3 := fid_sparseInv_of_core_eq hsp2 hlen3 hcore3 hsc3
        have hcl03 : s3.core.cur_level = 0 := by rw [hcore3]; exact hcl02
        have hpres3 := fid_ext_pres_compose hw2 hw3
        have hfl3_le : s3.core.fuel.toNat ≤ s.core.fuel.toNat := by
          rw [hcore3, hcore2]; exact hfu1
        rw [FullM6Hdr.fullM6HdrMem_iff] at hm3
        fvt_steps <;> exact hJw0 _ m3 ⟨ext3, s3, hext3, hpres3, hsp3, hcl03, hfl3_le, hm3⟩)
    rintro _ ⟨w0, ⟨⟩⟩ m3 ⟨ext3, s3, hext3, hpres3, hsp3, hcl03, hfl3_le, hm3⟩
    fvt_to_group
    refine wp_join_group (ts := [i64]) (fun _ mw1 => m3 = mw1) ?_
      (fun Jw1 hJw1 => by fvt_steps <;> exact hJw1 _ m3 rfl)
    rintro _ ⟨w1_0, ⟨⟩⟩ _ rfl; fvt_to_group
    refine wp_join_group (ts := [i64]) (fun _ mw2 => m3 = mw2) ?_
      (fun Jw2 hJw2 => by fvt_steps <;> exact hJw2 _ m3 rfl)
    rintro _ ⟨w2_0, ⟨⟩⟩ _ rfl; fvt_to_group
    refine wp_join_group (ts := [i64]) (fun _ mw3 => m3 = mw3) ?_
      (fun Jw3 hJw3 => by fvt_steps <;> exact hJw3 _ m3 rfl)
    rintro _ ⟨w3, ⟨⟩⟩ _ rfl; fvt_to_group
    · -- `sum == 0`: set `h->probing = 0` and return `1ULL`
      fvt_steps
      let s3p : FullState := { s3 with core := { s3.core with probing := 0#64 } }
      have hsp3p : FullSparseInv c F0 s3p := FullVivTop.FullSparseInv.with_probing hsp3 0#64
      exact hQ 1#64 ext3 s3p _ ⟨hext3, hpres3⟩ hsp3p ⟨hcl03, rfl⟩ hfl3_le
        (Or.inl rfl) (fun h => by cases h) ((FullM6Hdr.fullM6HdrMem_iff ..).mpr hm)
    · -- `sum != 0`: compute `total`, merge `tier1 >= tier2`, run active tiers `1, 2, 3, 0`
      have hsum_nz : w0 + w1_0 + w2_0 + w3 ≠ 0#64 := by c0_bound
      fvt_steps
      c0_call hGetWm
      refine FullM6Hdr.m6HdrW2aSpec_of rfl hcfg hext3 hsp3.1.lengths
        ((FullM6Hdr.fullM6HdrMem_iff ..).mpr hm3)
        fun ⟨last_p, ⟨⟩⟩ ext4 s4 m4 hcore4 hlen4 hsc4 hext4 hw4 hm4 => ?_
      have hsp4 : FullSparseInv c F0 s4 := fid_sparseInv_of_core_eq hsp3 hlen4 hcore4 hsc4
      have hcl04 : s4.core.cur_level = 0 := by rw [hcore4]; exact hcl03
      have hpres4 := fid_ext_pres_compose hpres3 hw4
      have hfl4_le : s4.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hcore4]; exact hfl3_le
      rw [FullM6Hdr.fullM6HdrMem_iff] at hm4
      let start := s3.scratch.search_ticks
      have hbud : (0xFFFFFFFF#64 : BitVec 64) ≠ 0#64 := by decide
      fvt_to_group
      refine wp_join_group (ts := [i64]) (fun _ md => m4 = md) ?_
        (fun Jd hJd => by fvt_steps <;> exact hJd _ m4 rfl)
      rintro _ ⟨delta, ⟨⟩⟩ _ rfl; fvt_to_group
      refine wp_join_group (ts := [i64]) (fun _ me => m4 = me) ?_
        (fun Je hJe => by fvt_steps <;> exact hJe _ m4 rfl)
      rintro _ ⟨eff_ref, ⟨⟩⟩ _ rfl; fvt_to_group
      refine wp_join_group (ts := [i64, i64])
        (fun (w1, w2, ()) mwg => m4 = mwg ∧ w1 + w2 = w1_0 + w2_0) ?_
        (fun Jwg hJwg => by fvt_steps <;> exact hJwg _ m4 ⟨rfl, by bv_omega⟩)
      rintro _ ⟨w1, w2, ⟨⟩⟩ _ ⟨rfl, hw12⟩
      let StepInv (didRun : Prop) := FidVivStepInv c F0 ext s R didRun
      have hTierCall : ∀ (extk : List (BitVec 64)) (sk : FullState) (mk : Mem 64)
          (tm limk : BitVec 64) (didNext : Prop),
          M6HdrExtOk extk → (M6HdrExtInitOk ext → M6HdrExtInitOk extk ∧ M6ExtW2bPres ext extk) →
          FullSparseInv c F0 sk → sk.core.fuel.toNat ≤ s.core.fuel.toNat →
          (FullMem c sk ⋆ (array64 (c.hdr - 2304) extk ⋆ R)) mk →
          ∀ (K : Tup Val [i64] → Mem 64 → Prop),
          (∀ rk mk', StepInv didNext (rk, limk, ()) mk' → K (rk, ()) mk') →
          Γ "full_vivify_tier_m6_hdr" [i64, i64, i64, i64] [i64]
            (c.hdr, tm, 0xFFFFFFFF#64, limk, ()) mk K X := by
        intro extk sk mk tm limk _ hek hpk hspk hfk hmk K hK
        apply hVivTier
        refine FullM6OrchAdapters.m6aVivifyTierSpec_of hspk hmk
          fun rk s' m' hsp' _ _ hbp' hfu' hres' huns' hm' => ?_
        obtain ⟨hcl', hpr'⟩ := hbp' hbud
        exact hK rk m' ⟨extk, s', hek, hpk, hsp', hcl', fun _ => hpr', fun _ => hpr',
          Nat.le_trans hfu' hfk, hres', huns', hm'⟩
      fvt_to_group_np
      refine wp_join_group (ts := [i64, i64]) (StepInv (w1 ≠ 0#64)) ?_ ?_
      · rintro _ ⟨r1, lim1, ⟨⟩⟩ m1 ⟨ext1, s1', he1, hp1, hsp1', hcl1, hpr1, hpr1r,
          hfu1', hr1, hu1, hm1'⟩
        fvt_to_group_np
        refine wp_join_group (ts := [i64, i64]) (StepInv (w1 ≠ 0#64 ∨ w2 ≠ 0#64)) ?_ ?_
        · rintro _ ⟨r2, lim2, ⟨⟩⟩ m2 ⟨ext2, s2', he2, hp2, hsp2', hcl2, hpr2, hpr2r,
            hfu2', hr2, hu2, hm2'⟩
          fvt_to_group_np
          refine wp_join_group (ts := [i64, i64])
            (StepInv (w1 ≠ 0#64 ∨ w2 ≠ 0#64 ∨ w3 ≠ 0#64)) ?_ ?_
          · rintro _ ⟨r3, lim3, ⟨⟩⟩ m3' ⟨ext3', s3', he3', hp3', hsp3', hcl3, hpr3, hpr3r,
              hfu3', hr3, hu3, hm3'⟩
            fvt_to_group_np
            refine wp_join_group (ts := [i64, i64])
              (StepInv (w1 ≠ 0#64 ∨ w2 ≠ 0#64 ∨ w3 ≠ 0#64 ∨ w0 ≠ 0#64)) ?_ ?_
            · rintro _ ⟨r4, _lim4, ⟨⟩⟩ m4' ⟨ext4', s4', he4', hp4', hsp4', hcl4, hpr4, _,
                hfu4', hr4, hu4, hm4'⟩
              have hsome : w1 ≠ 0#64 ∨ w2 ≠ 0#64 ∨ w3 ≠ 0#64 ∨ w0 ≠ 0#64 :=
                Classical.byContradiction fun hno => by
                  have h1 : w1 = 0#64 := Classical.byContradiction fun h => hno (Or.inl h)
                  have h2 : w2 = 0#64 := Classical.byContradiction fun h => hno (Or.inr (Or.inl h))
                  have h3 : w3 = 0#64 :=
                    Classical.byContradiction fun h => hno (Or.inr (Or.inr (Or.inl h)))
                  have h0 : w0 = 0#64 :=
                    Classical.byContradiction fun h => hno (Or.inr (Or.inr (Or.inr h)))
                  apply hsum_nz; bv_omega
              have hpr4' : s4'.core.probing = 0#64 := hpr4 hsome
              fvt_steps_np
              let sfin : FullState :=
                { s4' with scratch := { s4'.scratch with search_ticks := start } }
              have hsp_fin : FullSparseInv c F0 sfin :=
                fid_sparse_with_ticks hsp4' start
              exact hQ r4 ext4' sfin _ ⟨he4', hp4'⟩ hsp_fin ⟨hcl4, hpr4'⟩ hfu4' hr4 hu4
                ((FullM6Hdr.fullM6HdrMem_iff ..).mpr hm)
            · intro J0 hJ0
              have hskip0 : (r3 = 20#64 ∨ w0 = 0#64) →
                  StepInv (w1 ≠ 0#64 ∨ w2 ≠ 0#64 ∨ w3 ≠ 0#64 ∨ w0 ≠ 0#64) (r3, lim3, ()) m3' := by
                intro hsk
                refine ⟨ext3', s3', he3', hp3', hsp3', hcl3, ?_, hpr3r, hfu3', hr3, hu3, hm3'⟩
                intro hd
                rcases hsk with rfl | h0
                · exact hpr3r rfl
                · rcases hd with h | h | h | h
                  · exact hpr3 (Or.inl h)
                  · exact hpr3 (Or.inr (Or.inl h))
                  · exact hpr3 (Or.inr (Or.inr h))
                  · exact absurd h0 h
              fvt_to_group_np
              · -- `r3 != 20 && w0 > 0`
                fvt_to_group_np
                refine wp_join_group (ts := [i64]) (fun _ ml => m3' = ml) ?_
                  (fun Jl hJl => by fvt_steps_np <;> exact hJl _ m3' rfl)
                rintro _ ⟨lim4, ⟨⟩⟩ _ rfl
                fvt_to_group_np
                refine wp_call_of_spec _ _ (hTierCall ext3' s3' m3' 0#64 lim4
                  (w1 ≠ 0#64 ∨ w2 ≠ 0#64 ∨ w3 ≠ 0#64 ∨ w0 ≠ 0#64) he3' hp3' hsp3' hfu3' hm3' _ ?_)
                rintro (r4 : Val i64) m4a ⟨ext4a, s4a, he4a, hp4a, hsp4a, hcl4a, hpr4a, hpr4ar,
                  hfu4a, hr4a, hu4a, hm4a⟩
                c0_hsteps_nogrp
                refine wp_join_group (ts := [])
                  (fun () m4b => StepInv (w1 ≠ 0#64 ∨ w2 ≠ 0#64 ∨ w3 ≠ 0#64 ∨ w0 ≠ 0#64)
                    (r4, lim4, ()) m4b)
                  (fun _ () m4b hm4b => hJ0 (r4, lim4, ()) m4b hm4b)
                  (fun Jif hJif => by
                    c0_hsplit
                    · -- `r4 != 20`: compute `y` and call `bump_delay` or `reduce_delay`
                      fvt_to_group_np
                      refine wp_join_group (ts := [i64]) (fun _ my => m4a = my) ?_
                        (fun Jy hJy => by fvt_steps_np <;> exact hJy _ m4a rfl)
                      rintro _ ⟨_du, ⟨⟩⟩ _ rfl
                      fvt_to_group_np
                      refine wp_join_group (ts := [])
                        (fun () md' => StepInv (w1 ≠ 0#64 ∨ w2 ≠ 0#64 ∨ w3 ≠ 0#64 ∨ w0 ≠ 0#64)
                          (r4, lim4, ()) md')
                        (fun _ () md' hmd' => hJif () md' hmd')
                        (fun Jd hJd => by
                          have hBump : wp Γ Q X
                              (Expr.call (as := [i64, i64]) (bs := []) "m6_hdr_bump_delay"
                                (Arg.var c.hdr, Arg.imm 3, ()) fun _ => Expr.jump Jd ()) m4a := by
                            c0_call hBumpDelay
                            refine FullM6Hdr.m6HdrW2aSpec_of rfl hcfg he4a hsp4a.1.lengths
                              ((FullM6Hdr.fullM6HdrMem_iff ..).mpr hm4a)
                              fun () ext4b s4b m4b hcore4b hlen4b hsc4b he4b hw4b hm4b => ?_
                            have hsp4b := fid_sparseInv_of_core_eq hsp4a hlen4b hcore4b hsc4b
                            exact hJd () m4b ⟨ext4b, s4b, he4b, fid_ext_pres_compose hp4a hw4b,
                              hsp4b, by rw [hcore4b]; exact hcl4a,
                              fun hd => by rw [hcore4b]; exact hpr4a hd,
                              fun hr => by rw [hcore4b]; exact hpr4ar hr,
                              by rw [hcore4b]; exact hfu4a, hr4a, hu4a,
                              (FullM6Hdr.fullM6HdrMem_iff ..).mp hm4b⟩
                          have hRed : wp Γ Q X
                              (Expr.call (as := [i64, i64]) (bs := []) "m6_hdr_reduce_delay"
                                (Arg.var c.hdr, Arg.imm 3, ()) fun _ => Expr.jump Jd ()) m4a := by
                            c0_call hReduceDelay
                            refine FullM6Hdr.m6HdrW2aSpec_of rfl hcfg he4a hsp4a.1.lengths
                              ((FullM6Hdr.fullM6HdrMem_iff ..).mpr hm4a)
                              fun () ext4b s4b m4b hcore4b hlen4b hsc4b he4b hw4b hm4b => ?_
                            have hsp4b := fid_sparseInv_of_core_eq hsp4a hlen4b hcore4b hsc4b
                            exact hJd () m4b ⟨ext4b, s4b, he4b, fid_ext_pres_compose hp4a hw4b,
                              hsp4b, by rw [hcore4b]; exact hcl4a,
                              fun hd => by rw [hcore4b]; exact hpr4a hd,
                              fun hr => by rw [hcore4b]; exact hpr4ar hr,
                              by rw [hcore4b]; exact hfu4a, hr4a, hu4a,
                              (FullM6Hdr.fullM6HdrMem_iff ..).mp hm4b⟩
                          fvt_steps_np <;> first | exact hBump | exact hRed)
                    · exact hJif () m4a
                        ⟨ext4a, s4a, he4a, hp4a, hsp4a, hcl4a, hpr4a, hpr4ar, hfu4a, hr4a, hu4a,
                          hm4a⟩)
              · exact hJ0 (r3, lim3, ()) m3' (hskip0 (Or.inr (by c0_bound)))
              · exact hJ0 (r3, lim3, ()) m3' (hskip0 (Or.inl (by c0_bound)))
          · intro J3 hJ3
            have hskip3 : (r2 = 20#64 ∨ w3 = 0#64) →
                StepInv (w1 ≠ 0#64 ∨ w2 ≠ 0#64 ∨ w3 ≠ 0#64) (r2, lim2, ()) m2 := by
              intro hsk
              refine ⟨ext2, s2', he2, hp2, hsp2', hcl2, ?_, hpr2r, hfu2', hr2, hu2, hm2'⟩
              intro hd
              rcases hsk with rfl | h3
              · exact hpr2r rfl
              · rcases hd with h | h | h
                · exact hpr2 (Or.inl h)
                · exact hpr2 (Or.inr h)
                · exact absurd h3 h
            fvt_to_group_np
            · fvt_to_group_np
              refine wp_join_group (ts := [i64]) (fun _ ml => m2 = ml) ?_
                (fun Jl hJl => by fvt_steps_np <;> exact hJl _ m2 rfl)
              rintro _ ⟨lim3, ⟨⟩⟩ _ rfl
              refine wp_call_of_spec _ _ (hTierCall ext2 s2' m2 3#64 lim3
                (w1 ≠ 0#64 ∨ w2 ≠ 0#64 ∨ w3 ≠ 0#64) he2 hp2 hsp2' hfu2' hm2' _ ?_)
              intro r3 m3' h3; exact hJ3 (r3, lim3, ()) m3' h3
            · exact hJ3 (r2, lim2, ()) m2 (hskip3 (Or.inr (by c0_bound)))
            · exact hJ3 (r2, lim2, ()) m2 (hskip3 (Or.inl (by c0_bound)))
        · intro J2 hJ2
          have hskip2 : (r1 = 20#64 ∨ w2 = 0#64) →
              StepInv (w1 ≠ 0#64 ∨ w2 ≠ 0#64) (r1, lim1, ()) m1 := by
            intro hsk
            refine ⟨ext1, s1', he1, hp1, hsp1', hcl1, ?_, hpr1r, hfu1', hr1, hu1, hm1'⟩
            intro hd
            rcases hsk with rfl | h2
            · exact hpr1r rfl
            · rcases hd with h | h
              · exact hpr1 h
              · exact absurd h2 h
          fvt_to_group_np
          · fvt_to_group_np
            refine wp_join_group (ts := [i64]) (fun _ ml => m1 = ml) ?_
              (fun Jl hJl => by fvt_steps_np <;> exact hJl _ m1 rfl)
            rintro _ ⟨lim2, ⟨⟩⟩ _ rfl
            refine wp_call_of_spec _ _ (hTierCall ext1 s1' m1 2#64 lim2
              (w1 ≠ 0#64 ∨ w2 ≠ 0#64) he1 hp1 hsp1' hfu1' hm1' _ ?_)
            intro r2 m2 h2; exact hJ2 (r2, lim2, ()) m2 h2
          · exact hJ2 (r1, lim1, ()) m1 (hskip2 (Or.inr (by c0_bound)))
          · exact hJ2 (r1, lim1, ()) m1 (hskip2 (Or.inl (by c0_bound)))
      · intro J1 hJ1
        fvt_to_group_np
        · fvt_to_group_np
          refine wp_join_group (ts := [i64]) (fun _ ml => m4 = ml) ?_
            (fun Jl hJl => by fvt_steps_np <;> exact hJl _ m4 rfl)
          rintro _ ⟨lim1, ⟨⟩⟩ _ rfl
          refine wp_call_of_spec _ _ (hTierCall ext4 s4 m4 1#64 lim1 (w1 ≠ 0#64)
            hext4 hpres4 hsp4 hfl4_le hm4 _ ?_)
          intro r1 m1 h1; exact hJ1 (r1, lim1, ()) m1 h1
        · have hw1_0 : w1 = 0#64 := by c0_bound
          exact hJ1 (1#64, start, ()) m4
            ⟨ext4, s4, hext4, hpres4, hsp4, hcl04, fun h => absurd hw1_0 h,
             fun h => absurd h (by decide), hfl4_le, Or.inl rfl,
             fun h => absurd h (by decide), hm4⟩
  · fvt_steps
    · c0_call hBacktrack
      refine ⟨c, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hsp.1.lengths, hclv_lt, hmax_vars_pos,
        hw0.trail_lits_lt, hm, fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m1
          hlen1 _ _ hcl1 hpres1 _ _ _ hw_bt _ hm1 => ?_⟩
      have hsp1 : FullSparseInv c F0 _ :=
        FullVivTop.FullSparseInv.of_backtrack hsp (Nat.zero_le _) hlen1 hpres1
          (by simpa using hw_bt F0)
      exact hJ () m1 ⟨_, hsp1, by rw [hcl1]; simp, Nat.le_refl _, hm1⟩
    · have hcl0 : s.core.cur_level = 0 := by
        have h0 : (BitVec.ofNat 64 s.core.cur_level).toNat = 0 := by rw [hc]; rfl
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclv_lt] at h0
      exact hJ () m ⟨s, hsp, hcl0, Nat.le_refl _, hm⟩

end VivFidProofs

end LeanQbe.T.Examples.Kissat.FullFidelityVivK6
