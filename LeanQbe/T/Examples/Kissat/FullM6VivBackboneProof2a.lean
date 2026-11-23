module

public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof1
import LeanQbe.T.Examples.Kissat.FullVivifyLemmas2
import LeanQbe.T.Examples.Kissat.FullVivifyLemmas3
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat M6 Vivification — Simplify, Commit, & Deduce (`Proof2a`)

Certifies UNSAT-sound `Func.wp` (`XPost := False`, `0` SAT model proofs) for the `3` heavy
vivification engine functions in `FullM6VivBackbone.lean`:
1. `full_viv_simplify_m6_wp` (`fullVivSimplifyM6Spec`, glue lowering, `full_add_bin_m6`, OOM `2ULL`)
2. `full_viv_commit_m6_wp` (`fullVivCommitM6Spec`, prefix-preserving `target = olen - 2` commit at
   arbitrary `cur_level` via `NonActiveReason` + `full_viv_unreason_m6` + `full_viv_best_watch_m6`)
3. `full_viv_deduce_m6_wp` (`fullVivDeduceM6Spec`, `lit_mark` marking/clearing, binary/large
   subsumption `M6SubRefOk` in `h->ant_sz`, backward BFS entailment for all `olen ≠ 0xFFFFFFFF#32`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6VivBackbone

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open FullVivTopTactics
open scoped FullArenaTactics FullVivTopTactics

/-! ## 1. Cross-File Specifications (`Simplify`, `Commit`, `Deduce`) -/

section Specs

/-- Specification for `full_viv_simplify_m6(h, cref)`: level-0 simplification of a non-garbage
arena clause with glue lowering, `full_add_bin_m6`, and OOM `2#64` propagation, preserving
`red_refs` and `tarjan_reach`. -/
@[expose] def fullVivSimplifyM6Spec : Spec [i64, i32] [i64] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ s.core.cur_level = 0 ∧
    cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena_len = s.core.arena_len →
      s'.core.probing = s.core.probing → s'.core.fuel = s.core.fuel →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 0#64 →
        cref.toNat ∈ fullArenaClauseRefs s' ∧ fullArenaClauseGarb s' cref.toNat = false) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Specification for `full_viv_commit_m6(h, cref, olen, implied)`: prefix-preserving commit of
`work_stk2[0 ..< olen)` entailed by `F_cur` at ANY `cur_level`, preserving `fullArenaClauseRefs`,
`red_refs`, and `tarjan_reach`. -/
@[expose] def fullVivCommitM6Spec : Spec [i64, i32, i32, i32] [i64] :=
  fun (h, cref, olen, _implied, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧
      cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
      olen.toNat ≤ c.max_vars ∧
      (olen.toNat < fullArenaClauseSize s cref.toNat →
        (∀ i < olen.toNat, (s.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
        ((s.scratch.work_stk2.take olen.toNat).map fun x => x.toNat / 2).Nodup ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.work_stk2.take olen.toNat).map BitVec.toNat))) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        FullSparseInvW c F0 F_cur s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.arena_len = s.core.arena_len →
        s'.core.probing = s.core.probing → s'.core.fuel = s.core.fuel →
        fullArenaClauseRefs s' = fullArenaClauseRefs s →
        s'.scratch.red_refs = s.scratch.red_refs →
        s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'


end Specs

/-! ## 2. Shared Local Helpers & Pure Packs -/

section Helpers

open FullVivifyHelpers

private theorem c0_load_ws1_z_m6 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pWorkStk1 + 0#64) = some s.scratch.work_stk1[0] :=
  FullArenaTactics.load_full_work_stk1 hi hm

private theorem c0_load_ws1_b_m6 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pWorkStk1 = some s.scratch.work_stk1[0] := by
  simpa using FullArenaTactics.load_full_work_stk1 hi hm

private theorem c0_store_ws1_z_m6 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pWorkStk1 + 0#64) ∧
    (FullMem c { s with scratch := { s.scratch with work_stk1 := s.scratch.work_stk1.set 0 v } }
      ⋆ R) (storeMem m i32 (c.pWorkStk1 + 0#64) v) := by
  simpa using FullArenaTactics.store_full_work_stk1 v hi hm

private theorem c0_store_ws1_b_m6 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pWorkStk1 ∧
    (FullMem c { s with scratch := { s.scratch with work_stk1 := s.scratch.work_stk1.set 0 v } }
      ⋆ R) (storeMem m i32 c.pWorkStk1 v) := by
  simpa using FullArenaTactics.store_full_work_stk1 v hi hm

private theorem c0_load_ws2_z_m6 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pWorkStk2 + 0#64) = some s.scratch.work_stk2[0] :=
  FullArenaTactics.load_full_work_stk2 hi hm

private theorem c0_load_ws2_b_m6 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pWorkStk2 = some s.scratch.work_stk2[0] := by
  simpa using FullArenaTactics.load_full_work_stk2 hi hm

private theorem c0_load_ws2_4_m6 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 1 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pWorkStk2 + 4#64) = some s.scratch.work_stk2[1] :=
  FullArenaTactics.load_full_work_stk2 hi hm

private theorem c0_store_ws2_z_m6 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pWorkStk2 + 0#64) ∧
    (FullMem c { s with scratch := { s.scratch with work_stk2 := s.scratch.work_stk2.set 0 v } }
      ⋆ R) (storeMem m i32 (c.pWorkStk2 + 0#64) v) := by
  simpa using FullArenaTactics.store_full_work_stk2 v hi hm

private theorem c0_store_ws2_b_m6 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pWorkStk2 ∧
    (FullMem c { s with scratch := { s.scratch with work_stk2 := s.scratch.work_stk2.set 0 v } }
      ⋆ R) (storeMem m i32 c.pWorkStk2 v) := by
  simpa using FullArenaTactics.store_full_work_stk2 v hi hm

attribute [local c0_load] c0_load_ws1_z_m6 c0_load_ws1_b_m6 c0_load_ws2_z_m6 c0_load_ws2_b_m6
  c0_load_ws2_4_m6
attribute [local c0_store] c0_store_ws1_z_m6 c0_store_ws1_b_m6 c0_store_ws2_z_m6 c0_store_ws2_b_m6

private theorem m6_sparseW_with_counts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (ni' nr' : BitVec 64) :
    FullSparseInvW c F0 F_cur
      { s with core := { s.core with num_irred := ni', num_redundant := nr' } } :=
  ⟨⟨{ hsp.1.core_ok with }, hsp.1.scratch_ok⟩,
   { hsp.2.1 with
     arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok }
     watches := hsp.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

private theorem m6_sparseW_with_inc {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (hu : (cnfOfClauses F_cur).Unsat) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with inconsistent := 1#64 } } :=
  ⟨⟨{ hsp.1.core_ok with }, hsp.1.scratch_ok⟩,
   { hsp.2.1 with
     inconsistent_sound := fun _ => hu
     arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok }
     watches := hsp.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

private theorem m6_sparseW_with_vivcnt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (vc' : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with viv_cnt := vc' } } :=
  ⟨⟨hsp.1.core_ok, { hsp.1.scratch_ok with }⟩, hsp.2.1, hsp.2.2.1, hsp.2.2.2.1,
   hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

private theorem m6_sparseW_with_ws2 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) {ws2' : List (BitVec 32)}
    (hlen : ws2'.length = 2 * c.max_vars) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with work_stk2 := ws2' } } :=
  ⟨⟨hsp.1.core_ok, { hsp.1.scratch_ok with work_stk2_len := hlen }⟩, hsp.2.1, hsp.2.2.1,
   hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

private theorem m6_sparseW_with_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (oom' : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with oom := oom' } } :=
  fv_with_oomW hsp oom'

private theorem m6_watchLayout {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) : WatchStackLayout s.core := by
  have hmw := hsp.2.1.watches; unfold ModeWatchesInv at hmw
  simp only [hsp.2.2.2.2.2, ↓reduceIte] at hmw; exact hmw.layout

private theorem m6_unwatch_sparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {wvec' wstk' : List (BitVec 32)} {wu' : BitVec 64}
    (hlen' : ({ s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } } :
      FullState).LengthsOk c)
    (hmode' : ∀ Fc, ModeWatchesInv Fc s.core →
      ModeWatchesInv Fc { s.core with wvec := wvec', wstk := wstk', wusable := wu' }) :
    FullSparseInvW c F0 F_cur
      { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } } :=
  ⟨hlen',
   { hsp.2.1 with
     arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok }
     watches := hmode' F_cur hsp.2.1.watches },
   hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

private theorem m6_ws2_perm_props {F_cur : List (List Nat)} {ws2 ws2' : List (BitVec 32)}
    {n cv : Nat} (hws2 : n ≤ ws2.length) (hws2' : n ≤ ws2'.length)
    (hperm : (ws2'.take n).Perm (ws2.take n))
    (hlt : ∀ i < n, (ws2[i]?.getD 0#32).toNat < 2 * cv)
    (hnd : ((ws2.take n).map fun x => x.toNat / 2).Nodup)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause ((ws2.take n).map BitVec.toNat))) :
    (∀ i < n, (ws2'[i]?.getD 0#32).toNat < 2 * cv) ∧
    (((ws2'.take n).map BitVec.toNat).map (· / 2)).Nodup ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause ((ws2'.take n).map BitVec.toNat)) := by
  refine ⟨fun i hi => ?_, ?_, ?_⟩
  · have hm : ws2'[i]'(by omega) ∈ ws2.take n := hperm.mem_iff.mp (by
      rw [List.mem_iff_getElem]
      exact ⟨i, by rw [List.length_take]; omega, by simp [List.getElem_take]⟩)
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hm
    have hj_n : j < n := by rw [List.length_take] at hj; omega
    rw [List.getElem_take] at heq
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← heq]
    have := hlt j hj_n
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
  · have hp2 : (((ws2'.take n).map BitVec.toNat).map (· / 2)).Perm
        (((ws2.take n).map BitVec.toNat).map (· / 2)) :=
      (hperm.map BitVec.toNat).map (· / 2)
    exact hp2.nodup_iff.mpr (by simpa only [List.map_map, Function.comp_def] using hnd)
  · rw [CNF.entails_clause_def] at hent ⊢
    intro α hα
    obtain ⟨l, hl, hsat⟩ := (clause_sat_cnfClause_iff α _).mp (hent α hα)
    exact (clause_sat_cnfClause_iff α _).mpr ⟨l, (hperm.map BitVec.toNat).mem_iff.mpr hl, hsat⟩

private theorem m6_commit_shrk_hnonact {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s3 : FullState} (hsp3 : FullSparseInvW c F0 F_cur s3)
    {cref olen : Nat} (href3 : cref ∈ fullArenaClauseRefs s3)
    (hnonact : NonActiveReason s3.core cref) (hng3 : fullArenaClauseGarb s3 cref = false)
    (holen3 : 3 ≤ olen) (holen_lt : olen < fullArenaClauseSize s3 cref)
    (holen_le : olen ≤ s3.scratch.work_stk2.length)
    (hout_lt : ∀ j < olen, (s3.scratch.work_stk2[j]?.getD 0#32).toNat < 2 * s3.core.cur_vars)
    (hout_nd : (((s3.scratch.work_stk2.take olen).map BitVec.toNat).map (· / 2)).Nodup)
    (hout_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s3.scratch.work_stk2.take olen).map BitVec.toNat)))
    {nhdr2 : BitVec 32} {ar_p : List (BitVec 32)}
    (harp_len : ar_p.length = c.arena_cap)
    (hng2 : (nhdr2 &&& 0x00080000#32) = 0#32) (hsh2 : (nhdr2 &&& 0x00800000#32) ≠ 0#32)
    (hout_p : ∀ k, (k < cref ∨ cref + 3 + fullArenaClauseSize s3 cref ≤ k) →
      ar_p[k]? = s3.core.arena[k]?)
    (hsz_p : (ar_p[cref + 2]?.getD 0#32).toNat = olen)
    (hpay_p : ∀ j < olen, ar_p[cref + 3 + j]? = s3.scratch.work_stk2[j]?)
    (hpad_p : M6ShrkPad ar_p s3.core.arena cref (fullArenaClauseSize s3 cref) olen) :
    let ar_f := ar_p.set cref nhdr2
    let s_f : FullState := { s3 with core := { s3.core with arena := ar_f } }
    FullSparseInvW c F0 F_cur s_f ∧ fullArenaClauseRefs s_f = fullArenaClauseRefs s3 := by
  intro ar_f s_f
  have hw3 := hsp3.2.1; have hcl := hsp3.1.core_ok
  have hwf := hw3.arena.refs_wf cref href3; have halen_le := hcl.arena_len_le
  have hsz_def : fullArenaClauseSize s3 cref = fullArenaClauseSizeCore s3.core cref := rfl
  have harf_len : ar_f.length = c.arena_cap := by simp [ar_f, harp_len]
  have hsz_f : (ar_f[cref + 2]?.getD 0#32).toNat = olen := by
    dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hsz_p
  have hpay_f : ∀ j < olen, ar_f[cref + 3 + j]? = s3.scratch.work_stk2[j]? := fun j hj => by
    dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hpay_p j hj
  have hlits_eq : fullArenaClauseLitsCore { s3.core with arena := ar_f } cref =
      (s3.scratch.work_stk2.take olen).map BitVec.toNat := by
    have hbd' : cref + 3 + fullArenaClauseSizeCore { s3.core with arena := ar_f } cref ≤
        ar_f.length := by change cref + 3 + (ar_f[cref + 2]?.getD 0#32).toNat ≤ ar_f.length; omega
    have hlen_l : (fullArenaClauseLitsCore { s3.core with arena := ar_f } cref).length = olen := by
      unfold fullArenaClauseLitsCore fullArenaClauseSizeCore
      simp only [List.length_map, List.length_take, List.length_drop, hsz_f]; omega
    refine List.ext_getElem
      (by rw [hlen_l, List.length_map, List.length_take]; omega)
      fun t ht1 _ => ?_
    rw [hlen_l] at ht1
    have hgt : (fullArenaClauseLitsCore { s3.core with arena := ar_f } cref)[t]'(by
        rw [hlen_l]; exact ht1) =
        (ar_f[cref + 3 + t]'(by omega)).toNat := by
      unfold fullArenaClauseLitsCore; simp [List.getElem_map, List.getElem_take, List.getElem_drop]
    rw [hgt, List.getElem_map, List.getElem_take]
    have hg := hpay_f t ht1
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hg
    exact congrArg BitVec.toNat (Option.some.inj hg)
  have hpad_f : M6ShrkPad ar_f s3.core.arena cref (fullArenaClauseSize s3 cref) olen := by
    unfold M6ShrkPad at hpad_p ⊢; split
    · rename_i h0; rw [ite_eq_left h0] at hpad_p
      exact ⟨fun k hk1 hk2 => by
        dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hpad_p.1 k hk1 hk2,
        by dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hpad_p.2⟩
    · rename_i hne; rw [ite_eq_right hne] at hpad_p
      exact fun k hk1 hk2 => by
        dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hpad_p k hk1 hk2
  obtain ⟨hsp_f, hrefs_f, _, _⟩ := fullSparseInvW_of_inPlaceShrink_hnonact hsp3 href3 hnonact hng3
    holen3 holen_lt harf_len
    (fun k hk => by dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hout_p k hk)
    (by dsimp only [ar_f]; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hng2)
    (by dsimp only [ar_f]; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hsh2)
    hsz_f hpad_f (fun j hj => by rw [hpay_f j hj]; exact hout_lt j hj)
    (by rw [hlits_eq]; exact hout_nd) (by rw [hlits_eq]; exact hout_ent)
  exact ⟨hsp_f, hrefs_f⟩

private theorem m6_simplify_shrk_sparseInv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s2 : FullState} (hsp2 : FullSparseInvW c F0 F_cur s2) (hl0 : s2.core.cur_level = 0)
    {cref nsz : Nat} (href2 : cref ∈ fullArenaClauseRefs s2)
    (hng2 : fullArenaClauseGarb s2 cref = false) (hnsz3 : 3 ≤ nsz)
    (hnsz_lt : nsz < fullArenaClauseSize s2 cref) {ar3 ar_p : List (BitVec 32)} {idxs : List Nat}
    {nhdr2 : BitVec 32} (harp_len : ar_p.length = c.arena_cap) (hid_len : idxs.length = nsz)
    (hid_pw : idxs.Pairwise (· < ·)) (hid_lt : ∀ q ∈ idxs, q < fullArenaClauseSize s2 cref)
    (hsub3 : ∀ t < nsz, ar3[cref + 3 + t]? = s2.core.arena[cref + 3 + idxs[t]?.getD 0]?)
    (hnew_lt : ∀ t < nsz, (ar3[cref + 3 + t]?.getD 0#32).toNat < 2 * s2.core.cur_vars)
    (hent_new : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((List.range nsz).map fun t => (ar3[cref + 3 + t]?.getD 0#32).toNat)))
    (hng_nh : (nhdr2 &&& 0x00080000#32) = 0#32) (hsh_nh : (nhdr2 &&& 0x00800000#32) ≠ 0#32)
    (hout_p : ∀ k, (k < cref ∨ cref + 3 + fullArenaClauseSize s2 cref ≤ k) →
      ar_p[k]? = s2.core.arena[k]?)
    (hsz_p : (ar_p[cref + 2]?.getD 0#32).toNat = nsz)
    (hpay_p : ∀ t < nsz, ar_p[cref + 3 + t]? = ar3[cref + 3 + t]?)
    (hpad_p : ShrkPad ar_p s2.core.arena cref (fullArenaClauseSize s2 cref) nsz) :
    let ar_f := ar_p.set cref nhdr2
    let s_f : FullState := { s2 with core := { s2.core with arena := ar_f } }
    FullSparseInvW c F0 F_cur s_f ∧ fullArenaClauseGarb s_f cref = false ∧
    fullArenaClauseRefs s_f = fullArenaClauseRefs s2 := by
  intro ar_f s_f
  have hw2 := hsp2.2.1; have hcl := hsp2.1.core_ok
  have hwf := hw2.arena.refs_wf cref href2; have halen_le := hcl.arena_len_le
  have hsz_def : fullArenaClauseSize s2 cref = fullArenaClauseSizeCore s2.core cref := rfl
  have harf_len : ar_f.length = c.arena_cap := by simp [ar_f, harp_len]
  have hpad_f : ShrkPad ar_f s2.core.arena cref (fullArenaClauseSize s2 cref) nsz := by
    unfold ShrkPad at hpad_p ⊢; split
    · rename_i h0; rw [ite_eq_left h0] at hpad_p
      exact ⟨fun k hk1 hk2 => by
        dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hpad_p.1 k hk1 hk2,
        by dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hpad_p.2⟩
    · rename_i hne; rw [ite_eq_right hne] at hpad_p
      exact fun k hk1 hk2 => by
        dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hpad_p k hk1 hk2
  obtain ⟨hsp_f, hgb_f, ha_f⟩ := simplify_shrk_sparseInv hsp2 hl0 href2 hng2 hnsz3 hnsz_lt
    harf_len hid_len hid_pw hid_lt hsub3 hnew_lt hent_new
    (fun k hk => by dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hout_p k hk)
    (by dsimp only [ar_f]; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hng_nh)
    (by dsimp only [ar_f]; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hsh_nh)
    (by dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hsz_p)
    (fun t ht => by dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hpay_p t ht)
    hpad_f
  exact ⟨hsp_f, hgb_f, ha_f.1⟩

private theorem m6_watchPush_pre {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {blk cref : BitVec 32} (hsp : FullSparseInvW c F0 F_cur s)
    (hcref : cref.toNat < 0x80000000) :
    s.LengthsOk c ∧ WatchStackLayout s.core ∧
    ((2#32 : BitVec 32).toNat = 1 → (blk &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32) ∧
    ((2#32 : BitVec 32).toNat = 2 →
      (blk &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 ∧ cref ≠ 0xFFFFFFFF#32) :=
  ⟨hsp.1, m6_watchLayout hsp, fun h => absurd h (by decide),
   fun _ => ⟨(FullVivifyTactics.bv32_mask_lo31_props _).2, bv32_ne_sentinel_of_lt hcref⟩⟩

end Helpers

attribute [local c0_load] c0_load_ws1_z_m6 c0_load_ws1_b_m6 c0_load_ws2_z_m6 c0_load_ws2_b_m6
  c0_load_ws2_4_m6
attribute [local c0_store] c0_store_ws1_z_m6 c0_store_ws1_b_m6 c0_store_ws2_z_m6 c0_store_ws2_b_m6

/-! ## 3. Shared Factored Sub-Expressions (`DecrCount`, `GlueShrk`) -/

section SharedBlocks

open FullVivifyHelpers

private abbrev m6DecrCountExpr (h : Val i64) (hdr : Val i32) (k : Expr Val Cont [i64]) :
    Expr Val Cont [i64] :=
  Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) => k) Blocks.nil) fun Js =>
  fvOp (OpCode.and i32) (Arg.var hdr, Arg.imm 4194304, ()) fun p =>
  fvOp (OpCode.cmp .ne i32 .bool rfl) (Arg.var p.fst, Arg.imm 0, ()) fun p =>
  Expr.jnz (Arg.var p.fst)
    (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ => Expr.jump Js.fst ()) Blocks.nil)
       fun Js1 =>
     fvOp (OpCode.add i64) (Arg.var h, Arg.imm 496, ()) fun p =>
     Expr.load i64 (Arg.var p.fst) fun ld =>
     fvOp (OpCode.cmp .ugt i64 .bool rfl) (Arg.var ld, Arg.imm 0, ()) fun p =>
     Expr.jnz (Arg.var p.fst)
       (fvOp (OpCode.add i64) (Arg.var h, Arg.imm 496, ()) fun p =>
        Expr.load i64 (Arg.var p.fst) fun ld =>
        fvOp (OpCode.sub i64) (Arg.var ld, Arg.imm 1, ()) fun p1 =>
        fvOp (OpCode.add i64) (Arg.var h, Arg.imm 496, ()) fun p =>
        Expr.store (Arg.var p1.fst) (Arg.var p.fst) (Expr.jump Js1.fst ()))
       (Expr.jump Js1.fst ()))
    (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ => Expr.jump Js.fst ()) Blocks.nil)
       fun Js2 =>
     fvOp (OpCode.add i64) (Arg.var h, Arg.imm 488, ()) fun p =>
     Expr.load i64 (Arg.var p.fst) fun ld =>
     fvOp (OpCode.cmp .ugt i64 .bool rfl) (Arg.var ld, Arg.imm 0, ()) fun p =>
     Expr.jnz (Arg.var p.fst)
       (fvOp (OpCode.add i64) (Arg.var h, Arg.imm 488, ()) fun p =>
        Expr.load i64 (Arg.var p.fst) fun ld =>
        fvOp (OpCode.sub i64) (Arg.var ld, Arg.imm 1, ()) fun p1 =>
        fvOp (OpCode.add i64) (Arg.var h, Arg.imm 488, ()) fun p =>
        Expr.store (Arg.var p1.fst) (Arg.var p.fst) (Expr.jump Js2.fst ()))
       (Expr.jump Js2.fst ()))

private theorem m6_decr_count_wp (Γ : Env) {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {hdr : Val i32} {k : Expr Val Cont [i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (ni' nr' : BitVec 64) mg,
      (FullMem c { s with core := { s.core with num_irred := ni', num_redundant := nr' } } ⋆ R) mg →
      wp Γ Q X k mg) :
    wp Γ Q X (m6DecrCountExpr c.hdr hdr k) m := by
  dsimp only [m6DecrCountExpr, fvOp]
  refine wp_join_group (ts := [])
    (fun _ mg => ∃ ni' nr' : BitVec 64,
      (FullMem c { s with core := { s.core with num_irred := ni', num_redundant := nr' } } ⋆ R) mg)
    (fun _ _ mg ⟨ni', nr', hmg⟩ => hk ni' nr' mg hmg)
    (fun Jg hJg => by
      fvt_to_group
      · refine wp_join_group (ts := [])
          (fun _ mg => ∃ ni' nr' : BitVec 64,
            (FullMem c { s with core := { s.core with num_irred := ni', num_redundant := nr' } }
              ⋆ R) mg)
          (fun _ _ mg h => hJg () mg h)
          (fun J1 hJ1 => by
            fvt_steps
            · exact hJ1 () _ ⟨_, _, by assumption⟩
            · exact hJ1 () _ ⟨_, _, by assumption⟩)
      · refine wp_join_group (ts := [])
          (fun _ mg => ∃ ni' nr' : BitVec 64,
            (FullMem c { s with core := { s.core with num_irred := ni', num_redundant := nr' } }
              ⋆ R) mg)
          (fun _ _ mg h => hJg () mg h)
          (fun J2 hJ2 => by
            fvt_steps
            · exact hJ2 () _ ⟨_, _, by assumption⟩
            · exact hJ2 () _ ⟨_, _, by assumption⟩))

private abbrev m6TermPtr (pArena : Val i64) (cref old_sz : Val i32)
    (k : Val i64 → Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  fvOp (OpCode.zext 32 64) (Arg.var cref, ()) fun p =>
  fvOp (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p =>
  fvOp (OpCode.zext 32 64) (Arg.var old_sz, ()) fun pz =>
  fvOp (OpCode.add i64) (Arg.var p.fst, Arg.var pz.fst, ()) fun p =>
  fvOp (OpCode.sub i64) (Arg.var p.fst, Arg.imm 1, ()) fun p =>
  fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
  fvOp (OpCode.add i64) (Arg.var pArena, Arg.var p.fst, ()) fun p => k p.fst

private theorem m6_bv32_or_shrk_garb (x : BitVec 32) :
    ((x ||| 0x00800000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) := by
  rw [BitVec.and_or_distrib_right, show (0x00800000#32 &&& 0x00080000#32) = 0#32 by decide,
    BitVec.or_zero]

private theorem m6_bv32_or_shrk_ne0 (x : BitVec 32) :
    ((x ||| 0x00800000#32) &&& 0x00800000#32) ≠ 0#32 := fun h => by
  have := congrArg (BitVec.getLsbD · 23) h
  simp at this

private abbrev m6GlueShrkExpr (pArena : Val i64) (cref hdr old_sz nsz : Val i32)
    (k : Val i32 → Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.group (sig := [[i32]]) (fun _ => Blocks.cons (fun (p_g : Tup Val [i32]) =>
    Expr.group (sig := [[i32]]) (fun _ => Blocks.cons (fun (p_s : Tup Val [i32]) =>
      arBasePtr pArena cref fun p =>
      Expr.store (Arg.var p_s.fst) (Arg.var p) (k p_s.fst)) Blocks.nil) fun Js_s =>
    fvOp (OpCode.and i32) (Arg.var p_g.fst, Arg.imm 8388608, ()) fun p =>
    fvOp (OpCode.cmp .eq i32 .bool rfl) (Arg.var p.fst, Arg.imm 0, ()) fun p =>
    Expr.jnz (Arg.var p.fst)
      (m6TermPtr pArena cref old_sz fun pt =>
       Expr.store (Arg.imm (t := i32) 4294967295) (Arg.var pt)
         (fvOp (OpCode.or i32) (Arg.var p_g.fst, Arg.imm 8388608, ()) fun p =>
          Expr.jump Js_s.fst (Arg.var p.fst, ())))
      (Expr.jump Js_s.fst (Arg.var p_g.fst, ()))) Blocks.nil) fun Js_g =>
  fvOp (OpCode.and i32) (Arg.var hdr, Arg.imm 4194304, ()) fun p =>
  fvOp (OpCode.cmp .ne i32 .bool rfl) (Arg.var p.fst, Arg.imm 0, ()) fun p =>
  Expr.jnz (Arg.var p.fst)
    (fvOp (OpCode.and i32) (Arg.var hdr, Arg.imm 524287, ()) fun pg =>
     Expr.group (sig := [[i32]]) (fun _ => Blocks.cons (fun (p : Tup Val [i32]) =>
       Expr.jump Js_g.fst (Arg.var p.fst, ())) Blocks.nil) fun Js_i =>
     fvOp (OpCode.cmp .uge i32 .bool rfl) (Arg.var pg.fst, Arg.var nsz, ()) fun p =>
     Expr.jnz (Arg.var p.fst)
       (fvOp (OpCode.not i32) (Arg.imm 524287, ()) fun pm =>
        fvOp (OpCode.and i32) (Arg.var hdr, Arg.var pm.fst, ()) fun pa =>
        fvOp (OpCode.sub i32) (Arg.var nsz, Arg.imm 1, ()) fun ps =>
        fvOp (OpCode.and i32) (Arg.var ps.fst, Arg.imm 524287, ()) fun pb =>
        fvOp (OpCode.or i32) (Arg.var pa.fst, Arg.var pb.fst, ()) fun pr =>
        Expr.jump Js_i.fst (Arg.var pr.fst, ()))
       (Expr.jump Js_i.fst (Arg.var hdr, ())))
    (Expr.jump Js_g.fst (Arg.var hdr, ()))

private theorem m6_glue_shrk_wp (Γ : Env) {c : FullCfg} {s3 : FullState} {R : Mem 64 → Prop}
    {cref hdr old_sz nsz : Val i32} {ar_sz : List (BitVec 32)}
    {k : Val i32 → Expr Val Cont [i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hhdr_eq : fullArenaHdr s3 cref.toNat = hdr) (hhdr_ng : (hdr &&& 0x00080000#32) = 0#32)
    (hold_sz_3 : 3 ≤ old_sz.toNat) (hnsz3 : 3 ≤ nsz.toNat) (hnsz_lt : nsz.toNat < old_sz.toNat)
    (hcap : c.arena_cap < 2 * 2 ^ 28) (hbd : cref.toNat + 3 + old_sz.toNat ≤ c.arena_cap)
    (hasz_cap : ar_sz.length = c.arena_cap) (hcref0_eq : (cref.setWidth 64).toNat = cref.toNat)
    (hcref3_eq : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3)
    (hasz_out : ∀ p, (p < cref.toNat ∨ cref.toNat + 3 + old_sz.toNat ≤ p) →
      ar_sz[p]? = s3.core.arena[p]?)
    (hasz_sz : (ar_sz[cref.toNat + 2]?.getD 0#32).toNat = nsz.toNat)
    (hasz_pad : ∀ p, cref.toNat + 3 + nsz.toNat ≤ p → p < cref.toNat + 3 + old_sz.toNat →
      ar_sz[p]? = s3.core.arena[p]?)
    (hm : (FullMem c { s3 with core := { s3.core with arena := ar_sz } } ⋆ R) m)
    (hk : ∀ (nhdr2 : Val i32) (ar_p : List (BitVec 32)) mf,
      ar_p.length = c.arena_cap →
      (nhdr2 &&& 0x00080000#32) = 0#32 → (nhdr2 &&& 0x00800000#32) ≠ 0#32 →
      (∀ p, (p < cref.toNat ∨ cref.toNat + 3 + old_sz.toNat ≤ p) → ar_p[p]? = s3.core.arena[p]?) →
      (ar_p[cref.toNat + 2]?.getD 0#32).toNat = nsz.toNat →
      (∀ j < nsz.toNat, ar_p[cref.toNat + 3 + j]? = ar_sz[cref.toNat + 3 + j]?) →
      M6ShrkPad ar_p s3.core.arena cref.toNat old_sz.toNat nsz.toNat →
      ShrkPad ar_p s3.core.arena cref.toNat old_sz.toNat nsz.toNat →
      (FullMem c { s3 with core := { s3.core with arena := ar_p.set cref.toNat nhdr2 } } ⋆ R) mf →
      wp Γ Q X (k nhdr2) mf) :
    wp Γ Q X (m6GlueShrkExpr c.pArena cref hdr old_sz nsz k) m := by
  have hterm_eq : (cref.setWidth 64 + 3#64 + old_sz.setWidth 64 - 1#64).toNat =
      cref.toNat + 3 + old_sz.toNat - 1 := by
    have hos64 : (old_sz.setWidth 64).toNat = old_sz.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
        (Nat.lt_trans old_sz.isLt (by decide : 2 ^ 32 < 2 ^ 64))]
    have hadd : (cref.setWidth 64 + 3#64 + old_sz.setWidth 64).toNat =
        cref.toNat + 3 + old_sz.toNat := by
      rw [BitVec.toNat_add, hcref3_eq, hos64, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hadd]; show 1 ≤ _; omega), hadd]; rfl
  have hterm_lt : (cref.setWidth 64 + 3#64 + old_sz.setWidth 64 - 1#64).toNat < ar_sz.length := by
    rw [hterm_eq, hasz_cap]; omega
  dsimp only [m6GlueShrkExpr, m6TermPtr, arBasePtr, fvOp]
  refine wp_join_group (ts := [i32])
    (fun (nhdr, ()) m_g => m = m_g ∧ (nhdr &&& 0x00080000#32) = 0#32 ∧
      (nhdr &&& 0x00800000#32) = (hdr &&& 0x00800000#32))
    (fun _ ⟨nhdr, ⟨⟩⟩ m_g ⟨hm_g, hng_nh, hsh_nh⟩ => by
      subst hm_g
      refine wp_join_group (ts := [i32])
        (fun (nhdr2, ()) m_p => ∃ ar_p : List (BitVec 32), ar_p.length = c.arena_cap ∧
          (nhdr2 &&& 0x00080000#32) = 0#32 ∧ (nhdr2 &&& 0x00800000#32) ≠ 0#32 ∧
          (∀ p, (p < cref.toNat ∨ cref.toNat + 3 + old_sz.toNat ≤ p) →
            ar_p[p]? = s3.core.arena[p]?) ∧
          (ar_p[cref.toNat + 2]?.getD 0#32).toNat = nsz.toNat ∧
          (∀ j < nsz.toNat, ar_p[cref.toNat + 3 + j]? = ar_sz[cref.toNat + 3 + j]?) ∧
          M6ShrkPad ar_p s3.core.arena cref.toNat old_sz.toNat nsz.toNat ∧
          ShrkPad ar_p s3.core.arena cref.toNat old_sz.toNat nsz.toNat ∧
          (FullMem c { s3 with core := { s3.core with arena := ar_p } } ⋆ R) m_p)
        (fun _ ⟨nhdr2, ⟨⟩⟩ m_p
            ⟨ar_p, harp_len, hng2, hsh2, hout_p, hsz_p, hpay_p, hmpad, hspad, hmp⟩ => by
          have hcref_ltp : (cref.setWidth 64).toNat < ar_p.length := by
            rw [hcref0_eq, harp_len]; omega
          fvt_steps
          have hmf := fullMem_eq_of_arena_eq
            (show ar_p.set (cref.setWidth 64).toNat nhdr2 = ar_p.set cref.toNat nhdr2 by
              rw [hcref0_eq]) hm
          exact hk nhdr2 ar_p _ harp_len hng2 hsh2 hout_p hsz_p hpay_p hmpad hspad hmf)
        (fun Jp hJp => by
          fvt_steps
          · have hsh0 : (nhdr &&& 0x00800000#32) = 0#32 := by c0_bound
            let term := (cref.setWidth 64 + 3#64 + old_sz.setWidth 64 - 1#64).toNat
            have hraw0 : (s3.core.arena[cref.toNat]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
              have : fullArenaHdr s3 cref.toNat = s3.core.arena[cref.toNat]?.getD 0#32 := rfl
              rw [← this, hhdr_eq, ← hsh_nh, hsh0]
            have hpad_pr : (∀ p, cref.toNat + 3 + nsz.toNat ≤ p →
                p < cref.toNat + 3 + old_sz.toNat - 1 →
                (ar_sz.set term 0xFFFFFFFF#32)[p]? = s3.core.arena[p]?) ∧
                (ar_sz.set term 0xFFFFFFFF#32)[cref.toNat + 3 + old_sz.toNat - 1]? =
                  some 0xFFFFFFFF#32 :=
              ⟨fun p hp1 hp2 => by
                 rw [List.getElem?_set_ne (by omega)]; exact hasz_pad p hp1 (by omega),
               by rw [show cref.toNat + 3 + old_sz.toNat - 1 = term by omega]
                  exact List.getElem?_set_self (by omega)⟩
            refine hJp (nhdr ||| 0x00800000#32, ()) _
              ⟨ar_sz.set term 0xFFFFFFFF#32, by simp [hasz_cap],
               by rw [m6_bv32_or_shrk_garb, hng_nh], m6_bv32_or_shrk_ne0 nhdr,
               fun p hp => by rw [List.getElem?_set_ne (by omega)]; exact hasz_out p hp,
               by rw [List.getElem?_set_ne (by omega)]; exact hasz_sz,
               fun j hj => List.getElem?_set_ne (by omega),
               by unfold M6ShrkPad; rw [ite_eq_left hraw0]; exact hpad_pr,
               by unfold ShrkPad; rw [ite_eq_left hraw0]; exact hpad_pr, hm⟩
          · have hsh_ne : (nhdr &&& 0x00800000#32) ≠ 0#32 := by c0_bound
            have hraw_ne : (s3.core.arena[cref.toNat]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := by
              have : fullArenaHdr s3 cref.toNat = s3.core.arena[cref.toNat]?.getD 0#32 := rfl
              rw [← this, hhdr_eq, ← hsh_nh]; exact hsh_ne
            refine hJp (nhdr, ()) _ ⟨ar_sz, hasz_cap, hng_nh, hsh_ne, hasz_out, hasz_sz,
              fun _ _ => rfl,
              by unfold M6ShrkPad; rw [ite_eq_right hraw_ne]; exact hasz_pad,
              by unfold ShrkPad; rw [ite_eq_right hraw_ne]; exact hasz_pad, hm⟩))
    (fun Jg hJg => by
      fvt_to_group
      · refine wp_join_group (ts := [i32])
          (fun (nhdr, ()) m_i => m = m_i ∧ (nhdr &&& 0x00080000#32) = 0#32 ∧
            (nhdr &&& 0x00800000#32) = (hdr &&& 0x00800000#32))
          (fun _ ⟨nhdr, ⟨⟩⟩ m_i h => hJg (nhdr, ()) m_i h)
          (fun Ji hJi => by
            fvt_steps
            · exact hJi ((hdr &&& ~~~0x7FFFF#32) ||| ((nsz - 1#32) &&& 0x7FFFF#32), ()) _
                ⟨rfl, by rw [bv32_set_glue_garb hdr _ (bv32_glue_mask_garb _), hhdr_ng],
                 bv32_set_glue_shrk hdr _ (bv32_glue_mask_shrk _)⟩
            · exact hJi (hdr, ()) _ ⟨rfl, hhdr_ng, rfl⟩)
      · exact hJg (hdr, ()) _ ⟨rfl, hhdr_ng, rfl⟩)

end SharedBlocks

/-! ## 4. `full_viv_simplify_m6_wp` (Factored: ShrkTail, PostLoop2, Loop2, Main) -/

section SimplifyProof

open FullVivifyHelpers

private abbrev m6SimplifyShrkTailExpr (c : FullCfg) (cref hdr old_sz nsz : Val i32) :
    Expr Val Cont [i64] :=
  arOffPtr c.pArena cref 2 fun p => Expr.store (Arg.var nsz) (Arg.var p)
  (arOffPtr c.pArena cref 1 fun p => Expr.store (Arg.imm (t := i32) 2) (Arg.var p)
    (m6GlueShrkExpr c.pArena cref hdr old_sz nsz fun _ =>
      arOffPtr c.pArena cref 3 fun p => Expr.load i32 (Arg.var p) fun l0 =>
      arOffPtr c.pArena cref 4 fun p => Expr.load i32 (Arg.var p) fun l1 =>
      Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
        fvOp (OpCode.add i64) (Arg.var c.hdr, Arg.imm 760, ()) fun p =>
        Expr.store (Arg.imm (t := i64) 1) (Arg.var p.fst) (Expr.ret (Arg.imm 2, ()))) Blocks.nil)
        fun Jo =>
      fvOp (OpCode.and i32) (Arg.var l1, Arg.imm 2147483647, ()) fun b1 =>
      Expr.call "full_watch_push" (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
        (Arg.var c.hdr, Arg.var l0, Arg.var b1.fst, Arg.var cref, Arg.imm 2, ()) fun ok1 =>
      Expr.jnz (Arg.var ok1.fst)
        (fvOp (OpCode.and i32) (Arg.var l0, Arg.imm 2147483647, ()) fun b0 =>
         Expr.call "full_watch_push" (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
           (Arg.var c.hdr, Arg.var l1, Arg.var b0.fst, Arg.var cref, Arg.imm 2, ()) fun ok2 =>
         Expr.jnz (Arg.var ok2.fst) (Expr.ret (Arg.imm 0, ())) (Expr.jump Jo.fst ()))
        (Expr.jump Jo.fst ())))

private theorem m6_simplify_shrk_tail_wp (Γ : Env)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s2 : FullState}
    {R : Mem 64 → Prop} {cref hdr old_sz nsz : Val i32} {ar3 : List (BitVec 32)}
    {idxs : List Nat} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hsp2 : FullSparseInvW c F0 F_cur s2) (hl0 : s2.core.cur_level = 0)
    (href : cref.toNat ∈ fullArenaClauseRefs s2)
    (hrefs2 : fullArenaClauseRefs s2 = fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s2 cref.toNat = false)
    (hhdr_eq : fullArenaHdr s2 cref.toNat = hdr) (hhdr_ng : (hdr &&& 0x00080000#32) = 0#32)
    (hsz2 : fullArenaClauseSize s2 cref.toNat = old_sz.toNat)
    (hold_sz_3 : 3 ≤ old_sz.toNat) (hnsz3 : 3 ≤ nsz.toNat) (hnsz_lt : nsz.toNat < old_sz.toNat)
    (hcv2 : s2.core.cur_vars = s.core.cur_vars) (hal2 : s2.core.arena_len = s.core.arena_len)
    (hpr2 : s2.core.probing = s.core.probing) (hfu2 : s2.core.fuel = s.core.fuel)
    (hrr2 : s2.scratch.red_refs = s.scratch.red_refs)
    (htr2 : s2.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (har3_len : ar3.length = c.arena_cap) (hid_len : idxs.length = nsz.toNat)
    (hid_pw : idxs.Pairwise (· < ·)) (hid_lt : ∀ q ∈ idxs, q < old_sz.toNat)
    (hout3 : ∀ p, (p < cref.toNat + 3 ∨ cref.toNat + 3 + nsz.toNat ≤ p) →
      ar3[p]? = s2.core.arena[p]?)
    (hsub3 : ∀ t < nsz.toNat,
      ar3[cref.toNat + 3 + t]? = s2.core.arena[cref.toNat + 3 + idxs[t]?.getD 0]?)
    (hnew_lt : ∀ t < nsz.toNat, (ar3[cref.toNat + 3 + t]?.getD 0#32).toNat < 2 * s2.core.cur_vars)
    (hent_new : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((List.range nsz.toNat).map fun t => (ar3[cref.toNat + 3 + t]?.getD 0#32).toNat)))
    (hm : (FullMem c { s2 with core := { s2.core with arena := ar3 } } ⋆ R) m)
    (hQ : ∀ r s' m', FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena_len = s.core.arena_len →
      s'.core.probing = s.core.probing → s'.core.fuel = s.core.fuel →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs → s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 0#64 → cref.toNat ∈ fullArenaClauseRefs s' ∧ fullArenaClauseGarb s' cref.toNat = false) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (m6SimplifyShrkTailExpr c cref hdr old_sz nsz) m := by
  have hw2 := hsp2.2.1; have hcl2 := hsp2.1.core_ok
  have hcap := c.harena; unfold dimacsBound at hcap
  have hwf := hw2.arena.refs_wf cref.toNat href
  have hbd : cref.toNat + 3 + old_sz.toNat ≤ c.arena_cap := by
    have := hcl2.arena_len_le
    have : fullArenaClauseSizeCore s2.core cref.toNat = old_sz.toNat := hsz2
    omega
  have hcref0_eq : (cref.setWidth 64).toNat = cref.toNat := by bv_omega
  have hcref1_eq : (cref.setWidth 64 + 1#64).toNat = cref.toNat + 1 := by bv_omega
  have hcref2_eq : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2 := by bv_omega
  have hcref3_eq : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3 := by bv_omega
  have hcref4_eq : (cref.setWidth 64 + 4#64).toNat = cref.toNat + 4 := by bv_omega
  have har3_lt2 : (cref.setWidth 64 + 2#64).toNat < ar3.length := by omega
  have har3_lt1 : (cref.setWidth 64 + 1#64).toNat < ar3.length := by omega
  let ar_sz :=
    (ar3.set (cref.setWidth 64 + 2#64).toNat nsz).set (cref.setWidth 64 + 1#64).toNat 2#32
  obtain ⟨hasz_len, hasz_out, hasz_sz, hasz_pay, hasz_pad, _⟩ :=
    ar_set_sz_props (ar0 := ar3) (ar_orig := s2.core.arena)
      (by rw [hcl2.arena_len_arr]; exact har3_len)
      hnsz3 hnsz_lt (by rw [har3_len]; omega) rfl hcref2_eq hcref1_eq hout3
  have hasz_cap : ar_sz.length = c.arena_cap := by rw [hasz_len, hcl2.arena_len_arr]
  dsimp only [m6SimplifyShrkTailExpr, arOffPtr, fvOp]
  fvt_to_group
  refine m6_glue_shrk_wp Γ hhdr_eq hhdr_ng hold_sz_3 hnsz3 hnsz_lt hcap hbd hasz_cap
    hcref0_eq hcref3_eq hasz_out hasz_sz hasz_pad hm
    fun nhdr2 ar_p mf harp_len hng2 hsh2 hout_p hsz_p hpay_p _ hspad hmf => ?_
  have hpay_ar3 : ∀ t < nsz.toNat, ar_p[cref.toNat + 3 + t]? = ar3[cref.toNat + 3 + t]? :=
    fun t ht => (hpay_p t ht).trans (hasz_pay t ht)
  have hcref_lt8 : cref.toNat < 0x80000000 := by omega
  obtain ⟨hsp_f, hgb_f, hrefs_f0⟩ :=
    m6_simplify_shrk_sparseInv hsp2 hl0 href hng hnsz3 (by rw [hsz2]; exact hnsz_lt) harp_len
      hid_len hid_pw (fun q hq => by rw [hsz2]; exact hid_lt q hq) hsub3 hnew_lt hent_new
      hng2 hsh2 (by rw [hsz2]; exact hout_p) hsz_p hpay_ar3 (by rw [hsz2]; exact hspad)
  have hrefs_f : fullArenaClauseRefs { s2 with core := { s2.core with
      arena := ar_p.set cref.toNat nhdr2 } } = fullArenaClauseRefs s := hrefs_f0.trans hrefs2
  let ar_f := ar_p.set cref.toNat nhdr2
  let s_f : FullState := { s2 with core := { s2.core with arena := ar_f } }
  have harf_lt3 : (cref.setWidth 64 + 3#64).toNat < s_f.core.arena.length := by
    change _ < ar_f.length; simp [ar_f, harp_len]; omega
  have harf_lt4 : (cref.setWidth 64 + 4#64).toNat < s_f.core.arena.length := by
    change _ < ar_f.length; simp [ar_f, harp_len]; omega
  fvt_to_group
  refine wp_join_group (ts := [])
    (fun _ m_oom => ∃ s_o : FullState, FullSparseInvW c F0 F_cur s_o ∧ s_o.core.cur_level = 0 ∧
      s_o.core.cur_vars = s.core.cur_vars ∧ s_o.core.arena_len = s.core.arena_len ∧
      s_o.core.probing = s.core.probing ∧ s_o.core.fuel = s.core.fuel ∧
      fullArenaClauseRefs s_o = fullArenaClauseRefs s ∧
      s_o.scratch.red_refs = s.scratch.red_refs ∧
      s_o.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ (FullMem c s_o ⋆ R) m_oom)
    (fun _ _ m_oom ⟨s_o, hsp_o, hl_o, hcv_o, hal_o, hpr_o, hfu_o, href_o, hrr_o, htr_o, hm_o⟩ => by
      fvt_steps
      exact hQ 2#64 _ _ (m6_sparseW_with_oom hsp_o 1#64) hl_o hcv_o hal_o hpr_o hfu_o href_o
        hrr_o htr_o (Or.inr (Or.inr (Or.inl rfl))) (fun h => by cases h) (fun h => by cases h) hm)
    (fun Jo hJo => by
      fvt_steps; c0_call hWatchPush
      let l0 := ar_f[(cref.setWidth 64 + 3#64).toNat]'harf_lt3
      let l1 := ar_f[(cref.setWidth 64 + 4#64).toNat]'harf_lt4
      obtain ⟨hl1, lay1, hp1_1, hp1_2⟩ := m6_watchPush_pre (blk := l1) hsp_f hcref_lt8
      refine ⟨c, s_f, R, rfl, hl1, lay1, hp1_1, hp1_2, hmf,
        fun ok1 wvec3 wstk3 wlen3 wu3 wsort3 m4 hlen4 hlay4 hoth4 hok1_t hok1_f hm4 => ?_⟩
      have hsp4 := fullWatchPush_large_preserves_sparseInvW hsp_f
        (FullVivifyTactics.bv32_mask_lo31_props l1).1 hcref_lt8 (hrefs_f0 ▸ href) hlen4 hlay4
        hoth4 (fun h => let t := hok1_t h;
          ⟨t.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2 rfl⟩) (fun h => (hok1_f h).1)
      fvt_steps
      · c0_call hWatchPush
        obtain ⟨hl2, lay2, hp2_1, hp2_2⟩ := m6_watchPush_pre (blk := l0) hsp4 hcref_lt8
        refine ⟨c, _, R, rfl, hl2, lay2, hp2_1, hp2_2, hm4,
          fun ok2 wvec4 wstk4 wlen4 wu4 wsort4 m5 hlen5 hlay5 hoth5 hok2_t hok2_f hm5 => ?_⟩
        have hsp5 := fullWatchPush_large_preserves_sparseInvW hsp4
          (FullVivifyTactics.bv32_mask_lo31_props l0).1 hcref_lt8
          (by change cref.toNat ∈ fullArenaClauseRefs s_f; exact hrefs_f0 ▸ href)
          hlen5 hlay5 hoth5 (fun h => let t := hok2_t h;
            ⟨t.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2 rfl⟩) (fun h => (hok2_f h).1)
        fvt_steps
        · exact hQ 0#64 _ m5 hsp5 hl0 hcv2 hal2 hpr2 hfu2 hrefs_f hrr2 htr2 (Or.inl rfl)
            (fun h => by cases h) (fun _ => ⟨hrefs_f0 ▸ href, hgb_f⟩) hm5
        · exact hJo () m5 ⟨_, hsp5, hl0, hcv2, hal2, hpr2, hfu2, hrefs_f, hrr2, htr2, hm5⟩
      · exact hJo () m4 ⟨_, hsp4, hl0, hcv2, hal2, hpr2, hfu2, hrefs_f, hrr2, htr2, hm4⟩)

private abbrev m6SimplifyPostLoop2Expr (c : FullCfg) (cref hdr old_sz nsz : Val i32) :
    Expr Val Cont [i64] :=
  fvOp (OpCode.cmp .eq i32 .bool rfl) (Arg.var nsz, Arg.imm 0, ()) fun p =>
  Expr.jnz (Arg.var p.fst)
    (fvOp (OpCode.add i64) (Arg.var c.hdr, Arg.imm 1024, ()) fun p =>
     Expr.store (Arg.imm (t := i64) 1) (Arg.var p.fst) (Expr.ret (Arg.imm 20, ())))
    (fvOp (OpCode.cmp .eq i32 .bool rfl) (Arg.var nsz, Arg.imm 1, ()) fun p =>
     Expr.jnz (Arg.var p.fst)
      (arBasePtr c.pArena cref fun p =>
       fvOp (OpCode.or i32) (Arg.var hdr, Arg.imm 524288, ()) fun p1 =>
       Expr.store (Arg.var p1.fst) (Arg.var p)
         (addArenaGarbageExpr c.hdr old_sz
           (m6DecrCountExpr c.hdr hdr
             (Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun (p : Tup Val [i64]) =>
                Expr.ret (Arg.var p.fst, ())) Blocks.nil) fun Js =>
              arOffPtr c.pArena cref 3 fun p => Expr.load i32 (Arg.var p) fun ld =>
              Expr.call "full_add_unit" (as := [i64, i32]) (bs := [.bool])
                (Arg.var c.hdr, Arg.var ld, ()) fun p => Expr.jnz (Arg.var p.fst)
                (Expr.jump Js.fst (Arg.imm 1, ())) (Expr.jump Js.fst (Arg.imm 20, ()))))))
      (fvOp (OpCode.cmp .eq i32 .bool rfl) (Arg.var nsz, Arg.imm 2, ()) fun p =>
       Expr.jnz (Arg.var p.fst)
        (arOffPtr c.pArena cref 3 fun p => Expr.load i32 (Arg.var p) fun l0 =>
         arOffPtr c.pArena cref 4 fun p => Expr.load i32 (Arg.var p) fun l1 =>
         Expr.call "full_add_bin_m6" (as := [i64, i32, i32]) (bs := [i64])
           (Arg.var c.hdr, Arg.var l0, Arg.var l1, ()) fun br =>
         arBasePtr c.pArena cref fun p =>
         fvOp (OpCode.or i32) (Arg.var hdr, Arg.imm 524288, ()) fun p1 =>
         Expr.store (Arg.var p1.fst) (Arg.var p)
           (addArenaGarbageExpr c.hdr old_sz
             (m6DecrCountExpr c.hdr hdr
               (fvOp (OpCode.cmp .eq i64 .bool rfl) (Arg.var br.fst, Arg.imm 20, ()) fun p =>
                Expr.jnz (Arg.var p.fst) (Expr.ret (Arg.imm 20, ()))
                  (fvOp (OpCode.cmp .eq i64 .bool rfl) (Arg.var br.fst, Arg.imm 2, ()) fun p =>
                   Expr.jnz (Arg.var p.fst) (Expr.ret (Arg.imm 2, ()))
                     (Expr.ret (Arg.imm 1, ())))))))
        (m6SimplifyShrkTailExpr c cref hdr old_sz nsz)))

private theorem m6_simplify_post_loop2_wp (Γ : Env)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBinM6 : ∀ a m Q X, fullAddBinM6Spec a m Q X →
      Γ "full_add_bin_m6" [i64, i32, i32] [i64] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s2 : FullState}
    {R : Mem 64 → Prop} {cref hdr old_sz nsz : Val i32} {ar3 : List (BitVec 32)}
    {idxs : List Nat} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hsp2 : FullSparseInvW c F0 F_cur s2) (hl0 : s2.core.cur_level = 0)
    (href : cref.toNat ∈ fullArenaClauseRefs s2)
    (hrefs2 : fullArenaClauseRefs s2 = fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s2 cref.toNat = false)
    (hhdr_eq : fullArenaHdr s2 cref.toNat = hdr) (hhdr_ng : (hdr &&& 0x00080000#32) = 0#32)
    (hsz2 : fullArenaClauseSize s2 cref.toNat = old_sz.toNat)
    (hold_sz_3 : 3 ≤ old_sz.toNat) (hnsz_lt : nsz.toNat < old_sz.toNat)
    (hcv2 : s2.core.cur_vars = s.core.cur_vars) (hal2 : s2.core.arena_len = s.core.arena_len)
    (hpr2 : s2.core.probing = s.core.probing) (hfu2 : s2.core.fuel = s.core.fuel)
    (hrr2 : s2.scratch.red_refs = s.scratch.red_refs)
    (htr2 : s2.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (har3_len : ar3.length = c.arena_cap) (hid_len : idxs.length = nsz.toNat)
    (hid_pw : idxs.Pairwise (· < ·)) (hid_lt : ∀ q ∈ idxs, q < old_sz.toNat)
    (hout3 : ∀ p, (p < cref.toNat + 3 ∨ cref.toNat + 3 + nsz.toNat ≤ p) →
      ar3[p]? = s2.core.arena[p]?)
    (hsub3 : ∀ t < nsz.toNat,
      ar3[cref.toNat + 3 + t]? = s2.core.arena[cref.toNat + 3 + idxs[t]?.getD 0]?)
    (hcov3 : ∀ j < old_sz.toNat,
      s2.core.vals[(s2.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat]?.getD 0#8 = 0#8 →
      ∃ t < nsz.toNat, ar3[cref.toNat + 3 + t]? = s2.core.arena[cref.toNat + 3 + j]?)
    (hno1_2 : ∀ j < old_sz.toNat,
      s2.core.vals[(s2.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat]?.getD 0#8 ≠ 1#8)
    (hm : (FullMem c { s2 with core := { s2.core with arena := ar3 } } ⋆ R) m)
    (hQ : ∀ r s' m', FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena_len = s.core.arena_len →
      s'.core.probing = s.core.probing → s'.core.fuel = s.core.fuel →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs → s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 0#64 → cref.toNat ∈ fullArenaClauseRefs s' ∧ fullArenaClauseGarb s' cref.toNat = false) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (m6SimplifyPostLoop2Expr c cref hdr old_sz nsz) m := by
  have hw2 := hsp2.2.1; have hcl2 := hsp2.1.core_ok
  have hcap := c.harena; unfold dimacsBound at hcap
  have hwf := hw2.arena.refs_wf cref.toNat href
  have hbd : cref.toNat + 3 + old_sz.toNat ≤ c.arena_cap := by
    have := hcl2.arena_len_le
    have : fullArenaClauseSizeCore s2.core cref.toNat = old_sz.toNat := hsz2
    omega
  have hcref0_eq : (cref.setWidth 64).toNat = cref.toNat := by bv_omega
  have hcref3_eq : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3 := by bv_omega
  have hcref4_eq : (cref.setWidth 64 + 4#64).toNat = cref.toNat + 4 := by bv_omega
  have har3_lt0 : (cref.setWidth 64).toNat < ar3.length := by omega
  have har3_lt3 : (cref.setWidth 64 + 3#64).toNat < ar3.length := by omega
  have har3_lt4 : (cref.setWidth 64 + 4#64).toNat < ar3.length := by omega
  obtain ⟨hnew_lt, hent_new, hupd_w, hnd_other_ar3⟩ :=
    simplify_compact_facts hsp2 hl0 href hng (by rw [hsz2]; exact hnsz_lt) har3_len
      hid_len hout3 (fun q hq => by rw [hsz2]; exact hid_lt q hq) hsub3
      (fun j hj => hcov3 j (by rw [hsz2] at hj; exact hj))
      (fun j hj => hno1_2 j (by rw [hsz2] at hj; exact hj))
  dsimp only [m6SimplifyPostLoop2Expr, arBasePtr, arOffPtr, addArenaGarbageExpr, fvOp]
  fvt_step; fvt_step
  · -- `nsz == 0`: UNSAT
    have hnsz0 : nsz.toNat = 0 := by c0_bound
    have har3_eq : ar3 = s2.core.arena :=
      List.ext_getElem (by rw [har3_len, hcl2.arena_len_arr]) fun i hi _ => by
        have h := hout3 i (by omega)
        rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (by omega)] at h
        exact Option.some.inj h
    have hu : (cnfOfClauses F_cur).Unsat :=
      unsat_of_entails_nil (by simpa [hnsz0] using hent_new)
    have hm_s2 : (FullMem c s2 ⋆ R) m := fullMem_eq_of_arena_eq har3_eq hm
    clear hm; fvt_steps
    exact hQ 20#64 _ _ (m6_sparseW_with_inc hsp2 hu) hl0 hcv2 hal2 hpr2 hfu2 hrefs2 hrr2 htr2
      (Or.inr (Or.inr (Or.inr rfl))) (fun _ => hw2.ext_sound.2 hu) (fun h => by cases h) hm
  · have hnsz_ne0 : nsz ≠ 0#32 := by c0_bound
    rw [wp_jnz]; constructor <;> intro hc
    · -- `nsz == 1`: mark `PH_GARB`, decr counts, `full_add_unit`
      have hnsz1 : nsz.toNat = 1 := by
        simp only [Arg.val_var, beq_iff_eq] at hc; rw [hc]; rfl
      fvt_to_group
      obtain ⟨hlen_u, hw_u, hrefs_u, _⟩ := hupd_w (by omega)
      let s_upd : FullState := { s2 with core := { s2.core with arena := ar3 } }
      have hhdr_u : fullArenaHdr s_upd cref.toNat = hdr := by
        unfold fullArenaHdr fullArenaHdrCore; dsimp only [s_upd]
        rw [hout3 cref.toNat (Or.inl (by omega))]; exact hhdr_eq
      have hext_u : FullExtScratchOk c s_upd := ⟨fun i hi => by
        dsimp only [FullLastLearnedWf, s_upd]; rw [hrefs_u]
        exact hsp2.2.2.2.2.1.1 i hi, hsp2.2.2.2.2.1.2⟩
      have hm_u := fullMem_eq_of_arena_ag_eq
        (a2 := ar3.set cref.toNat (hdr ||| 0x00080000#32)) (by rw [hcref0_eq]; rfl) hm
      clear hm
      obtain ⟨s_g, har_g0, hmeta_g, hsc_g, hsp_g, ha_g, hm_g⟩ :=
        fullArena_markGarb_pack hlen_u hw_u hsp2.2.2.1 hext_u hsp2.2.2.2.2.2 hl0
          (by rw [hrefs_u]; exact href) hhdr_u
          (fun r hr hne hngr => hnd_other_ar3 s_upd rfl rfl r (hrefs_u ▸ hr) hne hngr) hm_u
      clear hm_u
      have hrefs_g : fullArenaClauseRefs s_g = fullArenaClauseRefs s :=
        (ha_g.1.trans hrefs_u).trans hrefs2
      have hcv_g : s_g.core.cur_vars = s.core.cur_vars := hmeta_g.2.1.trans hcv2
      have hal_g : s_g.core.arena_len = s.core.arena_len := hmeta_g.1.trans hal2
      have hpr_g : s_g.core.probing = s.core.probing := hmeta_g.2.2.2.1.trans hpr2
      have hfu_g : s_g.core.fuel = s.core.fuel := hmeta_g.2.2.2.2.trans hfu2
      have hrr_g : s_g.scratch.red_refs = s.scratch.red_refs :=
        (congrArg FullScratch.red_refs hsc_g).trans hrr2
      have htr_g : s_g.scratch.tarjan_reach = s.scratch.tarjan_reach :=
        (congrArg FullScratch.tarjan_reach hsc_g).trans htr2
      refine m6_decr_count_wp Γ hm_g fun ni' nr' mg hmg => ?_
      let sg1 : FullState :=
        { s_g with core := { s_g.core with num_irred := ni', num_redundant := nr' } }
      have hmg' : (FullMem c sg1 ⋆ R) mg := hmg
      clear hmg
      have hsp_g1 := m6_sparseW_with_counts hsp_g ni' nr'
      have har_g : s_g.core.arena = ar3.set cref.toNat (hdr ||| 0x00080000#32) := by
        rw [har_g0, hhdr_u]
      have hu0_eq : sg1.core.arena[(cref.setWidth 64 + 3).toNat]'(by
          change _ < s_g.core.arena.length
          rw [hsp_g.1.core_ok.arena_len_arr, show (cref.setWidth 64 + 3 : BitVec 64).toNat =
            cref.toNat + 3 from hcref3_eq]; omega) =
          ar3[cref.toNat + 3]'(by omega) := by
        change s_g.core.arena[(cref.setWidth 64 + 3).toNat]'_ = _
        simp only [har_g, show (cref.setWidth 64 + 3 : BitVec 64).toNat =
          cref.toNat + 3 from hcref3_eq]
        exact List.getElem_set_ne (by omega : cref.toNat ≠ cref.toNat + 3) _
      have hu0_lt : (ar3[cref.toNat + 3]'(by omega)).toNat < 2 * sg1.core.cur_vars := by
        have := hnew_lt 0 (by omega)
        rwa [List.getElem?_eq_getElem (by omega), Option.getD_some,
          ← show sg1.core.cur_vars = s2.core.cur_vars from hmeta_g.2.1] at this
      have hu0_ent : (cnfOfClauses F_cur).EntailsClause
          (cnfClause [(ar3[cref.toNat + 3]'(by omega)).toNat]) :=
        range_entails_1 hnsz1 (by omega) hent_new
      have hsg_ar3 : (cref.setWidth 64 + 3#64).toNat < sg1.core.arena.length := by
        change _ < s_g.core.arena.length; rw [hsp_g.1.core_ok.arena_len_arr, hcref3_eq]; omega
      fvt_to_group
      refine wp_join_group (ts := [i64])
        (fun (r, ()) m4 => ∃ sf : FullState, FullSparseInvW c F0 F_cur sf ∧ sf.core.cur_level = 0 ∧
          sf.core.cur_vars = s.core.cur_vars ∧ sf.core.arena_len = s.core.arena_len ∧
          sf.core.probing = s.core.probing ∧ sf.core.fuel = s.core.fuel ∧
          fullArenaClauseRefs sf = fullArenaClauseRefs s ∧
          sf.scratch.red_refs = s.scratch.red_refs ∧
          sf.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
          (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat) ∧ (FullMem c sf ⋆ R) m4)
        (fun _ ⟨r, ⟨⟩⟩ m4 ⟨sf, h1, h2, h3, h4, h5, h6, h7, h8, h9, hdom, h20, hm4⟩ => by
          fvt_steps
          exact hQ r sf m4 h1 h2 h3 h4 h5 h6 h7 h8 h9
            (hdom.elim (fun e => Or.inr (Or.inl e)) (fun e => Or.inr (Or.inr (Or.inr e))))
            h20 (fun h0 => by rcases hdom with e | e <;> rw [e] at h0 <;> cases h0) hm4)
        (fun Jr hJr => by
          fvt_steps; c0_call hAddUnit
          refine ⟨c, F0, F_cur, sg1, R, rfl, hsp_g1.1, hsp_g1.2.1,
            fun _ => by rw [hu0_eq]; exact hu0_ent, hmg',
            fun ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
              ph' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m4 hlen4 hw4 hcl0_4 hltf _ hm4 => ?_⟩
          have hsp4 : FullSparseInvW c F0 F_cur _ :=
            ⟨hlen4, hw4, hsp_g1.2.2.1, hsp_g1.2.2.2.1, hsp_g1.2.2.2.2.1, hsp_g1.2.2.2.2.2⟩
          fvt_steps
          · exact hJr (1#64, ()) m4 ⟨_, hsp4, hcl0_4, hcv_g, hal_g, hpr_g, hfu_g, hrefs_g, hrr_g,
              htr_g, Or.inl rfl, (fun h => by cases h), hm4⟩
          · exact hJr (20#64, ()) m4 ⟨_, hsp4, hcl0_4, hcv_g, hal_g, hpr_g, hfu_g, hrefs_g, hrr_g,
              htr_g, Or.inr rfl, fun _ => (hltf (by rw [hu0_eq]; exact hu0_lt) hc).1, hm4⟩)
    · have hnsz_ne1 : nsz ≠ 1#32 := by
        simp only [Arg.val_var, beq_eq_false_iff_ne] at hc; exact hc
      fvt_step; rw [wp_jnz]; constructor <;> intro hc
      · -- `nsz == 2`: `full_add_bin_m6`, mark `PH_GARB`, decr counts, ret `20`/`2`/`1`
        have hnsz2 : nsz.toNat = 2 := by
          simp only [Arg.val_var, beq_iff_eq] at hc; rw [hc]; rfl
        obtain ⟨hlen_u, hw_u, hrefs_u, _⟩ := hupd_w (by omega)
        let s_upd : FullState := { s2 with core := { s2.core with arena := ar3 } }
        have hu0_lt : (ar3[(cref.setWidth 64 + 3#64).toNat]'har3_lt3).toNat <
            2 * s_upd.core.cur_vars := by
          simp only [hcref3_eq]; have := hnew_lt 0 (by omega)
          rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
        have hu1_lt : (ar3[(cref.setWidth 64 + 4#64).toNat]'har3_lt4).toNat <
            2 * s_upd.core.cur_vars := by
          simp only [hcref4_eq]; have := hnew_lt 1 (by omega)
          rwa [show cref.toNat + 3 + 1 = cref.toNat + 4 by omega,
            List.getElem?_eq_getElem (by omega), Option.getD_some] at this
        have hbin_ent : (cnfOfClauses F_cur).EntailsClause
            (cnfClause [(ar3[(cref.setWidth 64 + 3#64).toNat]'har3_lt3).toNat,
                        (ar3[(cref.setWidth 64 + 4#64).toNat]'har3_lt4).toNat]) := by
          simp only [hcref3_eq, hcref4_eq]
          simpa [show cref.toNat + 3 + 1 = cref.toNat + 4 by omega] using
            range_entails_2 hnsz2 (by omega) hent_new
        have hext_u : FullExtScratchOk c s_upd := ⟨fun i hi => by
          dsimp only [FullLastLearnedWf, s_upd]; rw [hrefs_u]
          exact hsp2.2.2.2.2.1.1 i hi, hsp2.2.2.2.2.1.2⟩
        fvt_steps; c0_call hAddBinM6
        refine ⟨c, F0, F_cur, s_upd, R, rfl, hlen_u, hw_u, hl0, fun _ _ => hbin_ent, hm,
          fun br vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu'
            nb' oom' inc' ph' wso' m4 hlen4 hw4 _ h20 _ hm4 => ?_⟩
        let s4 : FullState :=
          { s_upd with
            core := { s_upd.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
              trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
              wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
              oom := oom', inconsistent := inc' }
            scratch := { s_upd.scratch with phases := ph', wsort := wso' } }
        have hhdr4 : fullArenaHdr s4 cref.toNat = hdr := by
          unfold fullArenaHdr fullArenaHdrCore; dsimp only [s4, s_upd]
          rw [hout3 cref.toNat (Or.inl (by omega))]; exact hhdr_eq
        have hrefs4 : fullArenaClauseRefs s4 = fullArenaClauseRefs s2 := hrefs_u
        have hm4' : (FullMem c s4 ⋆ R) m4 := hm4
        clear hm4; fvt_to_group
        have hm4_g := fullMem_eq_of_arena_ag_eq
          (a2 := s4.core.arena.set cref.toNat (hdr ||| 0x00080000#32))
          (by rw [hcref0_eq]; rfl) hm
        clear hm
        obtain ⟨s5, _, hmeta5, hsc5, hsp5, ha5, hm5⟩ :=
          fullArena_markGarb_pack hlen4 hw4 hsp2.2.2.1 hext_u hsp2.2.2.2.2.2 hl0
            (by rw [hrefs4]; exact href) hhdr4
            (fun r hr hne hngr => hnd_other_ar3 s4 rfl rfl r (hrefs4 ▸ hr) hne hngr) hm4_g
        clear hm4_g
        have hrefs5 : fullArenaClauseRefs s5 = fullArenaClauseRefs s :=
          (ha5.1.trans hrefs4).trans hrefs2
        have hcv5 : s5.core.cur_vars = s.core.cur_vars := hmeta5.2.1.trans hcv2
        have hal5 : s5.core.arena_len = s.core.arena_len := hmeta5.1.trans hal2
        have hpr5 : s5.core.probing = s.core.probing := hmeta5.2.2.2.1.trans hpr2
        have hfu5 : s5.core.fuel = s.core.fuel := hmeta5.2.2.2.2.trans hfu2
        have hrr5 : s5.scratch.red_refs = s.scratch.red_refs :=
          (congrArg FullScratch.red_refs hsc5).trans hrr2
        have htr5 : s5.scratch.tarjan_reach = s.scratch.tarjan_reach :=
          (congrArg FullScratch.tarjan_reach hsc5).trans htr2
        refine m6_decr_count_wp Γ hm5 fun ni' nr' mg hmg => ?_
        fvt_steps
        · exact hQ 20#64 _ mg (m6_sparseW_with_counts hsp5 ni' nr') hmeta5.2.2.1 hcv5 hal5 hpr5 hfu5
            hrefs5 hrr5 htr5 (Or.inr (Or.inr (Or.inr rfl))) (fun _ => (h20 hc).1)
            (fun h => by cases h) hmg
        · exact hQ 2#64 _ mg (m6_sparseW_with_counts hsp5 ni' nr') hmeta5.2.2.1 hcv5 hal5 hpr5 hfu5
            hrefs5 hrr5 htr5 (Or.inr (Or.inr (Or.inl rfl))) (fun h => by cases h)
            (fun h => by cases h) hmg
        · exact hQ 1#64 _ mg (m6_sparseW_with_counts hsp5 ni' nr') hmeta5.2.2.1 hcv5 hal5 hpr5 hfu5
            hrefs5 hrr5 htr5 (Or.inr (Or.inl rfl)) (fun h => by cases h)
            (fun h => by cases h) hmg
      · -- `nsz >= 3`
        have hnsz_ne2 : nsz ≠ 2#32 := by
          simp only [Arg.val_var, beq_eq_false_iff_ne] at hc; exact hc
        have hnsz3 : 3 ≤ nsz.toNat := bv32_ge3_of_ne nsz hnsz_ne0 hnsz_ne1 hnsz_ne2
        exact m6_simplify_shrk_tail_wp Γ hWatchPush hsp2 hl0 href hrefs2 hng hhdr_eq hhdr_ng
          hsz2 hold_sz_3 hnsz3 hnsz_lt hcv2 hal2 hpr2 hfu2 hrr2 htr2 har3_len hid_len hid_pw
          hid_lt hout3 hsub3 hnew_lt hent_new hm hQ

private abbrev m6SimplifyLoop2Expr (c : FullCfg) (cref hdr old_sz : Val i32) :
    Expr Val Cont [i64] :=
  Expr.group (sig := [[i32, i32]]) (fun Js => Blocks.cons (fun (p : Tup Val [i32, i32]) =>
    fvOp (OpCode.cmp .ult i32 .bool rfl) (Arg.var p.fst, Arg.var old_sz, ()) fun pb =>
    Expr.jnz (Arg.var pb.fst)
      (arLitPtr c.pArena cref p.fst fun pa => Expr.load i32 (Arg.var pa) fun ld =>
       Expr.group (sig := [[i32]]) (fun _ => Blocks.cons (fun (pn : Tup Val [i32]) =>
         fvOp (OpCode.add i32) (Arg.var p.fst, Arg.imm 1, ()) fun pi =>
         Expr.jump Js.fst (Arg.var pi.fst, Arg.var pn.fst, ())) Blocks.nil) fun Js1 =>
       fvOp (OpCode.zext 32 64) (Arg.var ld, ()) fun pl =>
       fvOp (OpCode.add i64) (Arg.var c.pVals, Arg.var pl.fst, ()) fun pv =>
       Expr.load i8 (Arg.var pv.fst) fun lv =>
       fvOp (OpCode.trunc 32 8) (Arg.imm 0, ()) fun pz =>
       fvOp (OpCode.sext 8 32) (Arg.var lv, ()) fun plv =>
       fvOp (OpCode.sext 8 32) (Arg.var pz.fst, ()) fun pz32 =>
       fvOp (OpCode.cmp .eq i32 .bool rfl) (Arg.var plv.fst, Arg.var pz32.fst, ()) fun pc =>
       Expr.jnz (Arg.var pc.fst)
         (arLitPtr c.pArena cref p.snd.fst fun pn => Expr.store (Arg.var ld) (Arg.var pn)
            (fvOp (OpCode.add i32) (Arg.var p.snd.fst, Arg.imm 1, ())
              fun pnsz => Expr.jump Js1.fst (Arg.var pnsz.fst, ())))
         (Expr.jump Js1.fst (Arg.var p.snd.fst, ())))
      (m6SimplifyPostLoop2Expr c cref hdr old_sz p.snd.fst)) Blocks.nil)
  fun Js => Expr.jump Js.fst (Arg.imm 0, Arg.imm 0, ())

private theorem m6_simplify_loop2_wp (Γ : Env)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBinM6 : ∀ a m Q X, fullAddBinM6Spec a m Q X →
      Γ "full_add_bin_m6" [i64, i32, i32] [i64] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s2 : FullState}
    {R : Mem 64 → Prop} {cref hdr old_sz : Val i32} {j0 : Nat} {m2 : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hsp2 : FullSparseInvW c F0 F_cur s2) (hl0 : s2.core.cur_level = 0)
    (href : cref.toNat ∈ fullArenaClauseRefs s2)
    (hrefs2 : fullArenaClauseRefs s2 = fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s2 cref.toNat = false)
    (hhdr_eq : fullArenaHdr s2 cref.toNat = hdr) (hhdr_ng : (hdr &&& 0x00080000#32) = 0#32)
    (hsz2 : fullArenaClauseSize s2 cref.toNat = old_sz.toNat) (hold_sz_3 : 3 ≤ old_sz.toNat)
    (hcv2 : s2.core.cur_vars = s.core.cur_vars) (hal2 : s2.core.arena_len = s.core.arena_len)
    (hpr2 : s2.core.probing = s.core.probing) (hfu2 : s2.core.fuel = s.core.fuel)
    (hrr2 : s2.scratch.red_refs = s.scratch.red_refs)
    (htr2 : s2.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (hno1_2 : ∀ j < old_sz.toNat,
      s2.core.vals[(s2.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat]?.getD 0#8 ≠ 1#8)
    (hj0_lt : j0 < old_sz.toNat)
    (hj0_ff :
      s2.core.vals[(s2.core.arena[cref.toNat + 3 + j0]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8)
    (hm2 : (FullMem c s2 ⋆ R) m2)
    (hQ : ∀ r s' m', FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena_len = s.core.arena_len →
      s'.core.probing = s.core.probing → s'.core.fuel = s.core.fuel →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs → s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 0#64 → cref.toNat ∈ fullArenaClauseRefs s' ∧ fullArenaClauseGarb s' cref.toNat = false) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (m6SimplifyLoop2Expr c cref hdr old_sz) m2 := by
  have hw2 := hsp2.2.1; have hcl2 := hsp2.1.core_ok
  have hcap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hcap hmx
  have har_len := hcl2.arena_len_arr; have hv_len := hcl2.vals_len; have hcv_le := hcl2.cur_vars_le
  have hwf := hw2.arena.refs_wf cref.toNat href
  have hold_sz_bd : cref.toNat + 3 + old_sz.toNat ≤ s2.core.arena.length := by
    have := hcl2.arena_len_le
    have : fullArenaClauseSizeCore s2.core cref.toNat = old_sz.toNat := hsz2
    omega
  have hlit_lt : ∀ (j : Nat) (_hj : j < old_sz.toNat),
      (s2.core.arena[cref.toNat + 3 + j]'(by omega)).toNat < 2 * s2.core.cur_vars := fun j hj =>
    hw2.arena.lits_lt cref.toNat href hng _
      ((mem_fullArenaClauseLitsCore_iff (by
        have : fullArenaClauseSizeCore s2.core cref.toNat = old_sz.toNat := hsz2; omega)).mpr
        ⟨j, by
          have : fullArenaClauseSizeCore s2.core cref.toNat = old_sz.toNat := hsz2; omega, rfl⟩)
  dsimp only [m6SimplifyLoop2Expr, arLitPtr, fvOp]
  refine wp_loop_inv (ts := [i32, i32])
    (fun (i2, nsz, ()) m3 => ∃ (ar3 : List (BitVec 32)) (idxs : List Nat),
      i2.toNat ≤ old_sz.toNat ∧ nsz.toNat ≤ i2.toNat ∧
      (j0 < i2.toNat → nsz.toNat < i2.toNat) ∧ ar3.length = c.arena_cap ∧
      (∀ p, (p < cref.toNat + 3 ∨ cref.toNat + 3 + nsz.toNat ≤ p) → ar3[p]? = s2.core.arena[p]?) ∧
      idxs.length = nsz.toNat ∧ idxs.Pairwise (· < ·) ∧ (∀ q ∈ idxs, q < i2.toNat) ∧
      (∀ t < nsz.toNat,
        ar3[cref.toNat + 3 + t]? = s2.core.arena[cref.toNat + 3 + idxs[t]?.getD 0]?) ∧
      (∀ j < i2.toNat,
        s2.core.vals[(s2.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat]?.getD 0#8 = 0#8 →
        ∃ t < nsz.toNat, ar3[cref.toNat + 3 + t]? = s2.core.arena[cref.toNat + 3 + j]?) ∧
      (FullMem c { s2 with core := { s2.core with arena := ar3 } } ⋆ R) m3)
    (fun (i2, _, ()) _ => old_sz.toNat - i2.toNat) ?_ ?_
  · intro J2 hJ2; fvt_steps
    exact hJ2 (0#32, 0#32, ()) m2 ⟨s2.core.arena, [], by simp, by simp, fun h => by simp at h,
      har_len, fun _ _ => rfl, rfl, .nil, fun _ h => by simp at h, fun _ h => by simp at h,
      fun _ h => by simp at h, hm2⟩
  · rintro J2 ⟨i2, nsz, ⟨⟩⟩ m3
      ⟨ar3, idxs, hi2_le, hnsz_le, hlt_j0, har3_len, hout3, hid_len, hid_pw, hid_lt,
       hsub3, hcov3, hm3⟩ ih2
    fvt_step; fvt_step
    · have hi2_lt : i2.toNat < old_sz.toNat := by c0_bound
      have hi2_idx :
          (cref.setWidth 64 + 3#64 + i2.setWidth 64).toNat = cref.toNat + 3 + i2.toNat := by
        bv_omega
      have hmod3i2 : (cref.toNat + BitVec.toNat (3 : BitVec 64) + i2.toNat) % 2 ^ 64 =
          cref.toNat + 3 + i2.toNat := by
        rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; exact Nat.mod_eq_of_lt (by omega)
      have har3_i2_lt : cref.toNat + 3 + i2.toNat < ar3.length := by omega
      have hs2_i2_lt : cref.toNat + 3 + i2.toNat < s2.core.arena.length := by omega
      have hi2_lt_ar : (cref.setWidth 64 + 3#64 + i2.setWidth 64).toNat < ar3.length := by omega
      have hnsz_idx : (cref.setWidth 64 + 3#64 + nsz.setWidth 64).toNat =
          cref.toNat + 3 + nsz.toNat := by bv_omega
      have hnsz_lt_ar : (cref.setWidth 64 + 3#64 + nsz.setWidth 64).toNat < ar3.length := by omega
      have hlit2_eq : ar3[cref.toNat + 3 + i2.toNat]'har3_i2_lt =
          s2.core.arena[cref.toNat + 3 + i2.toNat]'hs2_i2_lt := by
        have := hout3 (cref.toNat + 3 + i2.toNat) (Or.inr (by omega))
        rw [List.getElem?_eq_getElem har3_i2_lt, List.getElem?_eq_getElem hs2_i2_lt] at this
        exact Option.some.inj this
      have hlit2_v : (ar3[cref.toNat + 3 + i2.toNat]'har3_i2_lt).toNat < 2 * s2.core.cur_vars := by
        rw [hlit2_eq]; exact hlit_lt i2.toNat hi2_lt
      have hlit2_vlt : (ar3[(cref.setWidth 64 + 3#64 + i2.setWidth 64).toNat]'hi2_lt_ar).toNat <
          s2.core.vals.length := by
        rw [show ar3[(cref.setWidth 64 + 3#64 + i2.setWidth 64).toNat]'hi2_lt_ar =
          ar3[cref.toNat + 3 + i2.toNat]'har3_i2_lt by simp only [hi2_idx]]; omega
      have hi2_1 : (i2 + 1#32).toNat = i2.toNat + 1 := by bv_omega
      fvt_to_group
      refine wp_join_group (ts := [i32])
        (fun (nsz', ()) m4 => ∃ (ar4 : List (BitVec 32)) (idxs' : List Nat),
          nsz'.toNat ≤ i2.toNat + 1 ∧ (j0 < i2.toNat + 1 → nsz'.toNat < i2.toNat + 1) ∧
          ar4.length = c.arena_cap ∧
          (∀ p, (p < cref.toNat + 3 ∨ cref.toNat + 3 + nsz'.toNat ≤ p) →
            ar4[p]? = s2.core.arena[p]?) ∧
          idxs'.length = nsz'.toNat ∧ idxs'.Pairwise (· < ·) ∧ (∀ q ∈ idxs', q < i2.toNat + 1) ∧
          (∀ t < nsz'.toNat,
            ar4[cref.toNat + 3 + t]? = s2.core.arena[cref.toNat + 3 + idxs'[t]?.getD 0]?) ∧
          (∀ j < i2.toNat + 1,
            s2.core.vals[(s2.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat]?.getD 0#8 = 0#8 →
            ∃ t < nsz'.toNat, ar4[cref.toNat + 3 + t]? = s2.core.arena[cref.toNat + 3 + j]?) ∧
          (FullMem c { s2 with core := { s2.core with arena := ar4 } } ⋆ R) m4)
        (fun _ ⟨nsz', ⟨⟩⟩ m4
            ⟨ar4, idxs', hle', hlt', har4_len, hout4, hid', hpw', hlt_id', hsub', hcov', hm4⟩ => by
          fvt_steps
          exact ih2 (i2 + 1#32, nsz', ()) m4 (by dsimp only; omega)
            ⟨ar4, idxs', by omega, by omega, by omega, har4_len, hout4, hid', hpw',
             fun q hq => by have := hlt_id' q hq; omega, hsub',
             fun j hj => hcov' j (by omega), hm4⟩)
        (fun Jn hJn => by
          fvt_steps
          · have hv0 : s2.core.vals[(s2.core.arena[cref.toNat + 3 + i2.toNat]?.getD
                0#32).toNat]?.getD 0#8 = 0#8 := by
              rw [List.getElem?_eq_getElem hs2_i2_lt, Option.getD_some, ← hlit2_eq,
                List.getElem?_eq_getElem (by omega), Option.getD_some]
              simp only [hmod3i2] at hc; exact (bv8_sext32_eq0_iff _).mp hc
            have hi2_ne_j0 : i2.toNat ≠ j0 := fun h => by subst h; rw [hv0] at hj0_ff; cases hj0_ff
            have hnsz1 : (nsz + 1#32).toNat = nsz.toNat + 1 := by bv_omega
            let lit2 := ar3[cref.toNat + 3 + i2.toNat]'har3_i2_lt
            let ar4 := ar3.set (cref.toNat + 3 + nsz.toNat) lit2
            have har4_eq : ar3.set (cref.setWidth 64 + 3#64 + nsz.setWidth 64).toNat
                (ar3[(cref.setWidth 64 + 3#64 + i2.setWidth 64).toNat]'hi2_lt_ar) = ar4 := by
              simp only [ar4, lit2, hnsz_idx, hi2_idx]
            refine hJn (nsz + 1#32, ()) _
              ⟨ar4, idxs ++ [i2.toNat], by omega, fun hj => by omega,
               by simp [ar4, har3_len], fun p hp => ?_, by simp [hid_len, hnsz1], ?_, ?_, ?_,
               ?_, fullMem_eq_of_arena_eq har4_eq hm⟩
            · dsimp only [ar4]; rw [List.getElem?_set_ne (by omega)]; exact hout3 p (by omega)
            · exact List.pairwise_append.mpr ⟨hid_pw, List.pairwise_singleton _ _,
                fun a ha b hb => by simp at hb; subst hb; exact hid_lt a ha⟩
            · intro q hq; simp at hq
              exact hq.elim (fun h => Nat.lt_trans (hid_lt q h) (by omega))
                (fun h => by omega)
            · intro t ht; by_cases htn : t = nsz.toNat
              · subst htn; dsimp only [ar4]; rw [List.getElem?_set_self (by omega)]
                have hget_id : (idxs ++ [i2.toNat])[nsz.toNat]?.getD 0 = i2.toNat := by
                  rw [List.getElem?_append_right (by omega),
                    show nsz.toNat - idxs.length = 0 by omega]; rfl
                rw [hget_id, List.getElem?_eq_getElem hs2_i2_lt]; dsimp only [lit2]; rw [hlit2_eq]
              · dsimp only [ar4]; rw [List.getElem?_set_ne (by omega),
                  List.getElem?_append_left (by omega)]; exact hsub3 t (by omega)
            · intro j hj hvj; rcases (by omega : j < i2.toNat ∨ j = i2.toNat) with hj' | rfl
              · obtain ⟨t, ht, hteq⟩ := hcov3 j hj' hvj
                exact ⟨t, by omega, by dsimp only [ar4]; rw [List.getElem?_set_ne (by omega)]
                                       exact hteq⟩
              · refine ⟨nsz.toNat, by omega, ?_⟩; dsimp only [ar4]
                rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem hs2_i2_lt]
                dsimp only [lit2]; rw [hlit2_eq]
          · have hvne0 : s2.core.vals[(s2.core.arena[cref.toNat + 3 + i2.toNat]?.getD
                0#32).toNat]?.getD 0#8 ≠ 0#8 := fun h0 => by
              rw [List.getElem?_eq_getElem hs2_i2_lt, Option.getD_some, ← hlit2_eq,
                List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
              simp only [hmod3i2] at hc; exact hc ((bv8_sext32_eq0_iff _).mpr h0)
            exact hJn (nsz, ()) m3
              ⟨ar3, idxs, by omega, fun hj => by omega, har3_len, hout3, hid_len, hid_pw,
               fun q hq => Nat.lt_trans (hid_lt q hq) (by omega), hsub3,
               fun j hj hvj => (by omega : j < i2.toNat ∨ j = i2.toNat).elim
                 (fun h => hcov3 j h hvj) (fun h => absurd (h ▸ hvj) hvne0), hm3⟩)
    · have hi2_eq : i2.toNat = old_sz.toNat := by c0_bound
      have hnsz_lt : nsz.toNat < old_sz.toNat := by have := hlt_j0 (by omega); omega
      exact m6_simplify_post_loop2_wp Γ hAddUnit hAddBinM6 hWatchPush hsp2 hl0 href hrefs2 hng
        hhdr_eq hhdr_ng hsz2 hold_sz_3 hnsz_lt hcv2 hal2 hpr2 hfu2 hrr2 htr2 har3_len hid_len
        hid_pw (fun q hq => by have := hid_lt q hq; omega) hout3 hsub3
        (fun j hj => hcov3 j (by omega)) hno1_2 hm3 hQ

/-- `full_viv_simplify_m6` satisfies `fullVivSimplifyM6Spec` parametrically in `Γ`. -/
theorem full_viv_simplify_m6_wp (Γ : Env)
    (hUnwatch : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBinM6 : ∀ a m Q X, fullAddBinM6Spec a m Q X →
      Γ "full_add_bin_m6" [i64, i32, i32] [i64] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullVivSimplifyM6Spec a m Q X →
      Func.wp Γ full_viv_simplify_m6_body a m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hl0, href, hng, hm0, hQ⟩
  have hw0 := hsp.2.1; have hcl := hsp.1.core_ok
  have hcap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hcap hmx
  have har_len := hcl.arena_len_arr; have halen_le := hcl.arena_len_le
  have hcv_le := hcl.cur_vars_le; have hv_len := hcl.vals_len
  have hcref_wf := hw0.arena.refs_wf cref.toNat href
  obtain ⟨hcref_lt, _, hcref0_eq, _, hcref2_eq, hcref3_eq, hcref4_eq, hhdr_ng_raw⟩ :=
    cref_hdr_facts (fv_sparseW_to_sparse hsp) hw0 href hng
  let hdr := s.core.arena[(cref.setWidth 64).toNat]'(by rw [hcref0_eq]; exact hcref_lt)
  let old_sz := s.core.arena[(cref.setWidth 64 + 2#64).toNat]'(by rw [hcref2_eq]; omega)
  have hhdr_eq : hdr = fullArenaHdr s cref.toNat := ar_get_eq_getD hcref0_eq _
  have hold_sz_eq : old_sz.toNat = fullArenaClauseSizeCore s.core cref.toNat :=
    congrArg BitVec.toNat (ar_get_eq_getD hcref2_eq _)
  have hold_sz_3 : 3 ≤ old_sz.toNat := by rw [hold_sz_eq]; exact hcref_wf.2.1
  have hold_sz_bd : cref.toNat + 3 + old_sz.toNat ≤ s.core.arena.length := by
    rw [hold_sz_eq]; omega
  have hhdr_ng : (hdr &&& 0x00080000#32) = 0#32 := by
    simpa [hhdr_eq, fullArenaHdr, fullArenaHdrCore] using hhdr_ng_raw
  have hcref3_lt : (cref.setWidth 64 + 3#64).toNat < s.core.arena.length := by omega
  have hcref4_lt : (cref.setWidth 64 + 4#64).toNat < s.core.arena.length := by omega
  have hsz_s_eq : fullArenaClauseSize s cref.toNat = old_sz.toNat := hold_sz_eq.symm
  have hlit_lt : ∀ (j : Nat) (_hj : j < old_sz.toNat),
      (s.core.arena[cref.toNat + 3 + j]'(by omega)).toNat < 2 * s.core.cur_vars := fun j hj =>
    hw0.arena.lits_lt cref.toNat href hng _
      ((mem_fullArenaClauseLitsCore_iff (by omega)).mpr ⟨j, by rw [← hold_sz_eq]; exact hj, rfl⟩)
  unfold Func.wp full_viv_simplify_m6_body
  fvt_to_group
  refine wp_loop_inv (ts := [i32, i32])
    (fun (k, i, ()) m1 => m0 = m1 ∧ i.toNat ≤ old_sz.toNat ∧ k.toNat ≤ i.toNat ∧
      (∀ j < i.toNat,
        s.core.vals[(s.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat]?.getD 0#8 ≠ 1#8) ∧
      (k.toNat < i.toNat → ∃ j0 < i.toNat,
        s.core.vals[(s.core.arena[cref.toNat + 3 + j0]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8))
    (fun (_, i, ()) _ => old_sz.toNat - i.toNat) ?_ ?_
  · intro J1 hJ1; fvt_steps
    exact hJ1 (0#32, 0#32, ()) m0 ⟨rfl, by simp, by simp,
      fun _ hj => by simp at hj, fun hlt => by simp at hlt⟩
  · rintro J1 ⟨k, i, ⟨⟩⟩ m1 ⟨rfl, hi_le, hk_le, hno1, hhasf⟩ ih1
    fvt_step; fvt_step
    · have hi_lt : i.toNat < old_sz.toNat := by dsimp only [old_sz]; c0_bound
      have hidx_eq : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat =
          cref.toNat + 3 + i.toNat := by bv_omega
      have hmod3i : (cref.toNat + BitVec.toNat (3 : BitVec 64) + i.toNat) % 2 ^ 64 =
          cref.toNat + 3 + i.toNat := by
        rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; exact Nat.mod_eq_of_lt (by omega)
      have hidx_lt : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat < s.core.arena.length := by
        omega
      let lit := s.core.arena[cref.toNat + 3 + i.toNat]'(by omega)
      have hlit_getD : s.core.arena[cref.toNat + 3 + i.toNat]?.getD 0#32 = lit := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hlit_v : lit.toNat < 2 * s.core.cur_vars := hlit_lt i.toNat hi_lt
      have hlit_vlt :
          (s.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hidx_lt).toNat <
            s.core.vals.length := by
        rw [show s.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hidx_lt = lit by
          simp only [lit, hidx_eq]]; omega
      have hdom := hw0.vals_domain lit.toNat hlit_v
      have hv_get : s.core.vals[lit.toNat]'(by omega) = s.core.vals[lit.toNat]?.getD 0#8 := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hi1_eq : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
      fvt_steps
      · -- `vals[lit] > 0`
        c0_call hUnwatch
        refine ⟨c, s, R, rfl, hsp.1, m6_watchLayout hsp, hm0,
          fun wvec1 wstk1 wu1 m2 hlen1 _ hmode1 hm2 => ?_⟩
        have hsp1 := m6_unwatch_sparse hsp hlen1 hmode1
        have hcref4_lt1 : (cref.setWidth 64 + 4#64).toNat < ({ s with core :=
            { s.core with wvec := wvec1, wstk := wstk1, wusable := wu1 } } :
            FullState).core.arena.length := hcref4_lt
        fvt_steps; c0_call hUnwatch
        refine ⟨c, _, R, rfl, hsp1.1, m6_watchLayout hsp1, hm2,
          fun wvec2 wstk2 wu2 m3 hlen2 _ hmode2 hm3 => ?_⟩
        let s2 : FullState := { s with core :=
          { s.core with wvec := wvec2, wstk := wstk2, wusable := wu2 } }
        have hsp2 : FullSparseInvW c F0 F_cur s2 := m6_unwatch_sparse hsp1 hlen2 hmode2
        have hm3' : (FullMem c s2 ⋆ R) m3 := hm3
        clear hm3; fvt_to_group
        obtain ⟨hsp3, hrefs3, _⟩ :=
          fv_markGarbW hsp2 hl0 href (s.core.arena_garbage + 3#64 + old_sz.setWidth 64)
        let s3 : FullState := { s2 with core := { s2.core with
          arena := s.core.arena.set cref.toNat (fullArenaHdr s cref.toNat ||| 0x00080000#32)
          arena_garbage := s.core.arena_garbage + 3#64 + old_sz.setWidth 64 } }
        have hm3_g : (FullMem c s3 ⋆ R) m := by
          have har_eq : s.core.arena.set (cref.setWidth 64).toNat (hdr ||| 0x00080000#32) =
              s.core.arena.set cref.toNat (fullArenaHdr s cref.toNat ||| 0x00080000#32) := by
            rw [hcref0_eq, hhdr_eq]
          exact fullMem_eq_of_arena_ag_eq har_eq hm
        clear hm
        refine m6_decr_count_wp Γ hm3_g fun ni' nr' mg hmg => ?_
        fvt_steps
        exact hQ 1#64 _ mg (m6_sparseW_with_counts hsp3 ni' nr') hl0 rfl rfl rfl rfl
          hrefs3 rfl rfl (Or.inr (Or.inl rfl)) (fun h => by cases h) (fun h => by cases h) hmg
      · -- `vals[lit] == 0`
        have hne1 : s.core.vals[lit.toNat]?.getD 0#8 ≠ 1#8 := by
          simp only [hmod3i] at hc; rw [← hv_get, (bv8_sext32_eq0_iff _).mp hc]; decide
        have hk1_eq : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
        refine ih1 (k + 1#32, i + 1#32, ()) m0 (by dsimp only; omega)
          ⟨rfl, by omega, by omega, fun j hj => (by omega : j < i.toNat ∨ j = i.toNat).elim
            (hno1 j) (fun h => by rw [h, hlit_getD]; exact hne1),
           fun hlt => by obtain ⟨j0, hj0, hf0⟩ := hhasf (by omega); exact ⟨j0, by omega, hf0⟩⟩
      · -- `vals[lit] < 0`
        rename_i hc_slt
        have hne1 : s.core.vals[lit.toNat]?.getD 0#8 ≠ 1#8 := fun heq => by
          have h1 : s.core.vals[lit.toNat]'(by omega) = 1#8 := hv_get.trans heq
          simp only [hmod3i] at hc_slt; rw [h1] at hc_slt; revert hc_slt; decide
        have hff : s.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8 := by
          rcases hdom with h0 | h1 | hff
          · exfalso; have h0' : s.core.vals[lit.toNat]'(by omega) = 0#8 := hv_get.trans h0
            simp only [hmod3i] at hc; exact hc ((bv8_sext32_eq0_iff _).mpr h0')
          · exact absurd h1 hne1
          · exact hff
        refine ih1 (k, i + 1#32, ()) m0 (by dsimp only; omega)
          ⟨rfl, by omega, by omega, fun j hj => (by omega : j < i.toNat ∨ j = i.toNat).elim
            (hno1 j) (fun h => by rw [h, hlit_getD]; exact hne1),
           fun _ => ⟨i.toNat, by omega, by rwa [hlit_getD]⟩⟩
    · -- Loop 1 exit: `i == old_sz`
      have hi_eq : i.toNat = old_sz.toNat := by dsimp only [old_sz] at hi_le ⊢; c0_bound
      clear hc ih1 J1
      fvt_steps
      · exact hQ 0#64 s m0 hsp hl0 rfl rfl rfl rfl rfl rfl rfl (Or.inl rfl)
          (fun h => by cases h) (fun _ => ⟨href, hng⟩) hm0
      · have hk_lt : k.toNat < old_sz.toNat := by
          have hne : k.toNat ≠ old_sz.toNat :=
            fun h => (by dsimp only [old_sz]; c0_bound : k ≠ old_sz) (BitVec.eq_of_toNat_eq h)
          omega
        obtain ⟨j0, hj0_lt, hj0_ff⟩ := hhasf (by omega)
        c0_call hUnwatch
        refine ⟨c, s, R, rfl, hsp.1, m6_watchLayout hsp, hm0,
          fun wvec1 wstk1 wu1 m1' hlen1 _ hmode1 hm1' => ?_⟩
        have hsp1 := m6_unwatch_sparse hsp hlen1 hmode1
        have hcref4_lt1 : (cref.setWidth 64 + 4#64).toNat < ({ s with core :=
            { s.core with wvec := wvec1, wstk := wstk1, wusable := wu1 } } :
            FullState).core.arena.length := hcref4_lt
        fvt_steps; c0_call hUnwatch
        refine ⟨c, _, R, rfl, hsp1.1, m6_watchLayout hsp1, hm1',
          fun wvec2 wstk2 wu2 m2 hlen2 _ hmode2 hm2 => ?_⟩
        let s2 : FullState := { s with core :=
          { s.core with wvec := wvec2, wstk := wstk2, wusable := wu2 } }
        have hsp2 : FullSparseInvW c F0 F_cur s2 := m6_unwatch_sparse hsp1 hlen2 hmode2
        have hm2' : (FullMem c s2 ⋆ R) m2 := hm2
        exact m6_simplify_loop2_wp Γ hAddUnit hAddBinM6 hWatchPush hsp2 hl0 href rfl hng
          hhdr_eq.symm hhdr_ng hsz_s_eq hold_sz_3 rfl rfl rfl rfl rfl rfl
          (j0 := j0) (fun j hj => hno1 j (by rw [hi_eq]; exact hj))
          (by change j0 < old_sz.toNat; rw [← hi_eq]; exact hj0_lt) hj0_ff hm2' hQ

end SimplifyProof

/-! ## 5. `full_viv_commit_m6_wp` (Factored: ShrkTail, Main) -/

section CommitProof

open FullVivifyHelpers

private abbrev m6CommitShrkTailExpr (c : FullCfg) (cref hdr old_sz olen : Val i32) :
    Expr Val Cont [i64] :=
  Expr.store (Arg.var olen) (Arg.var (c.pArena + (cref.setWidth 64 + 2) * 4))
  (arOffPtr c.pArena cref 1 fun p => Expr.store (Arg.imm (t := i32) 2) (Arg.var p)
    (m6GlueShrkExpr c.pArena cref hdr old_sz olen fun _ =>
      fvOp (OpCode.sext 32 64) (Arg.imm 0, ()) fun p =>
      fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
      fvOp (OpCode.add i64) (Arg.var c.pWorkStk2, Arg.var p.fst, ()) fun p =>
      Expr.load i32 (Arg.var p.fst) fun l0 =>
      fvOp (OpCode.sext 32 64) (Arg.imm 1, ()) fun p =>
      fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
      fvOp (OpCode.add i64) (Arg.var c.pWorkStk2, Arg.var p.fst, ()) fun p =>
      Expr.load i32 (Arg.var p.fst) fun l1 =>
      Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
        fvOp (OpCode.add i64) (Arg.var c.hdr, Arg.imm 760, ()) fun p =>
        Expr.store (Arg.imm (t := i64) 1) (Arg.var p.fst)
          (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
             Expr.ret (Arg.imm 2, ())) Blocks.nil) fun Jbo =>
           fvOp (OpCode.add i64) (Arg.var c.hdr, Arg.imm 160, ()) fun p =>
           Expr.load i64 (Arg.var p.fst) fun ld =>
           fvOp (OpCode.cmp .ne i64 .bool rfl) (Arg.var ld, Arg.imm 0, ()) fun p =>
           Expr.jnz (Arg.var p.fst)
             (Expr.call "full_backtrack" (as := [i64, i64]) (bs := [])
                (Arg.var c.hdr, Arg.imm 0, ()) fun _ => Expr.jump Jbo.fst ())
             (Expr.jump Jbo.fst ()))) Blocks.nil) fun Jo =>
      fvOp (OpCode.and i32) (Arg.var l1, Arg.imm 2147483647, ()) fun b1 =>
      Expr.call "full_watch_push" (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
        (Arg.var c.hdr, Arg.var l0, Arg.var b1.fst, Arg.var cref, Arg.imm 2, ()) fun ok1 =>
      Expr.jnz (Arg.var ok1.fst)
        (fvOp (OpCode.and i32) (Arg.var l0, Arg.imm 2147483647, ()) fun b0 =>
         Expr.call "full_watch_push" (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
           (Arg.var c.hdr, Arg.var l1, Arg.var b0.fst, Arg.var cref, Arg.imm 2, ()) fun ok2 =>
         Expr.jnz (Arg.var ok2.fst) (Expr.ret (Arg.imm 1, ())) (Expr.jump Jo.fst ()))
        (Expr.jump Jo.fst ())))

private theorem m6_commit_shrk_tail_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s3 : FullState}
    {R : Mem 64 → Prop} {cref hdr old_sz olen : Val i32} {ar4 : List (BitVec 32)}
    {m4 : Mem 64} {Q : Post [i64]} {X : XPost}
    (hsp3 : FullSparseInvW c F0 F_cur s3)
    (href : cref.toNat ∈ fullArenaClauseRefs s3)
    (hrefs3 : fullArenaClauseRefs s3 = fullArenaClauseRefs s)
    (hnonact3 : NonActiveReason s3.core cref.toNat)
    (hng3 : fullArenaClauseGarb s3 cref.toNat = false)
    (hhdr3 : fullArenaHdr s3 cref.toNat = hdr) (hhdr_ng : (hdr &&& 0x00080000#32) = 0#32)
    (hsz3 : fullArenaClauseSize s3 cref.toNat = old_sz.toNat)
    (hold_sz_3 : 3 ≤ old_sz.toNat) (holen3 : 3 ≤ olen.toNat) (holen_lt : olen.toNat < old_sz.toNat)
    (hcv3 : s3.core.cur_vars = s.core.cur_vars) (hal3 : s3.core.arena_len = s.core.arena_len)
    (hpr3 : s3.core.probing = s.core.probing) (hfu3 : s3.core.fuel = s.core.fuel)
    (hrr3 : s3.scratch.red_refs = s.scratch.red_refs)
    (htr3 : s3.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (holen_le : olen.toNat ≤ s3.scratch.work_stk2.length)
    (hout_lt : ∀ j < olen.toNat,
      (s3.scratch.work_stk2[j]?.getD 0#32).toNat < 2 * s3.core.cur_vars)
    (hout_nd : (((s3.scratch.work_stk2.take olen.toNat).map BitVec.toNat).map (· / 2)).Nodup)
    (hout_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s3.scratch.work_stk2.take olen.toNat).map BitVec.toNat)))
    (har4_len : ar4.length = c.arena_cap)
    (hcp4 : ∀ k < olen.toNat, ar4[cref.toNat + 3 + k]? = s3.scratch.work_stk2[k]?)
    (hout4 : ∀ p, (p < cref.toNat + 3 ∨ cref.toNat + 3 + olen.toNat ≤ p) →
      ar4[p]? = s3.core.arena[p]?)
    (hm4 : (FullMem c { s3 with core := { s3.core with arena := ar4 } } ⋆ R) m4)
    (hQ : ∀ r s' m', FullSparseInvW c F0 F_cur s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena_len = s.core.arena_len →
      s'.core.probing = s.core.probing → s'.core.fuel = s.core.fuel →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs → s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (m6CommitShrkTailExpr c cref hdr old_sz olen) m4 := by
  have hw3 := hsp3.2.1; have hcl3 := hsp3.1.core_ok
  have hcap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hcap hmx
  have hwf := hw3.arena.refs_wf cref.toNat href
  have hbd : cref.toNat + 3 + old_sz.toNat ≤ c.arena_cap := by
    have := hcl3.arena_len_le
    have : fullArenaClauseSizeCore s3.core cref.toNat = old_sz.toNat := hsz3
    omega
  have hcref0_eq : (cref.setWidth 64).toNat = cref.toNat := by bv_omega
  have hcref1_eq : (cref.setWidth 64 + 1#64).toNat = cref.toNat + 1 := by bv_omega
  have hcref2_eq : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2 := by bv_omega
  have hcref3_eq : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3 := by bv_omega
  have har4_lt2 : (cref.setWidth 64 + 2).toNat < ar4.length := by
    change (cref.setWidth 64 + 2#64).toNat < ar4.length; omega
  have har4_lt1 : (cref.setWidth 64 + 1#64).toNat < ar4.length := by omega
  let ar_sz :=
    (ar4.set (cref.setWidth 64 + 2).toNat olen).set (cref.setWidth 64 + 1#64).toNat 2#32
  obtain ⟨hasz_len, hasz_out, hasz_sz, hasz_pay, hasz_pad, _⟩ :=
    ar_set_sz_props (ar0 := ar4) (ar_orig := s3.core.arena)
      (by rw [hcl3.arena_len_arr]; exact har4_len)
      holen3 holen_lt (by rw [har4_len]; omega) rfl hcref2_eq hcref1_eq hout4
  have hasz_cap : ar_sz.length = c.arena_cap := by simp [ar_sz, har4_len]
  dsimp only [m6CommitShrkTailExpr, arOffPtr, fvOp]
  fvt_to_group
  refine m6_glue_shrk_wp Γ hhdr3 hhdr_ng hold_sz_3 holen3 holen_lt hcap hbd hasz_cap
    hcref0_eq hcref3_eq hasz_out hasz_sz hasz_pad hm
    fun nhdr2 ar_p mf harp_len hng2 hsh2 hout_p hsz_p hpay_p hmpad _ hmf => ?_
  have hpay_ws2 : ∀ j < olen.toNat, ar_p[cref.toNat + 3 + j]? = s3.scratch.work_stk2[j]? :=
    fun j hj => (hpay_p j hj).trans ((hasz_pay j hj).trans (hcp4 j hj))
  have hcref_lt8 : cref.toNat < 0x80000000 := by omega
  have h0_ws2 : 0 < s3.scratch.work_stk2.length := by omega
  have h1_ws2 : 1 < s3.scratch.work_stk2.length := by omega
  obtain ⟨hsp_f, hrefs_f0⟩ := m6_commit_shrk_hnonact hsp3 href hnonact3 hng3 holen3
    (by rw [hsz3]; exact holen_lt) holen_le hout_lt hout_nd hout_ent harp_len hng2 hsh2
    (by rw [hsz3]; exact hout_p) hsz_p hpay_ws2 (by rw [hsz3]; exact hmpad)
  let s_f : FullState := { s3 with core := { s3.core with arena := ar_p.set cref.toNat nhdr2 } }
  have hrefs_fs : fullArenaClauseRefs s_f = fullArenaClauseRefs s := hrefs_f0.trans hrefs3
  have h0_sf : 0 < s_f.scratch.work_stk2.length := h0_ws2
  have h1_sf : 1 < s_f.scratch.work_stk2.length := h1_ws2
  fvt_to_group
  refine wp_join_group (ts := [])
    (fun _ m_oom => ∃ s_o : FullState, FullSparseInvW c F0 F_cur s_o ∧
      s_o.core.cur_vars = s.core.cur_vars ∧ s_o.core.arena_len = s.core.arena_len ∧
      s_o.core.probing = s.core.probing ∧ s_o.core.fuel = s.core.fuel ∧
      fullArenaClauseRefs s_o = fullArenaClauseRefs s ∧
      s_o.scratch.red_refs = s.scratch.red_refs ∧
      s_o.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ (FullMem c s_o ⋆ R) m_oom)
    (fun _ _ m_oom ⟨s_o, hsp_o, hcv_o, hal_o, hpr_o, hfu_o, href_o, hrr_o, htr_o, hm_o⟩ => by
      let s_o1 := { s_o with core := { s_o.core with oom := 1#64 } }
      have hsp_o1 := m6_sparseW_with_oom hsp_o 1#64
      have hcl_o64 : s_o1.core.cur_level < 2 ^ 64 := by
        change s_o.core.cur_level < 2 ^ 64
        have := hsp_o.2.1.cur_level_le; have := hsp_o.1.core_ok.trail_end_le
        have := hsp_o.1.core_ok.cur_vars_le; omega
      have hbt_o : (0#64 : BitVec 64).toNat < s_o1.core.cur_level →
          (0#64 : BitVec 64).toNat < c.max_vars := fun h => by
        change (0#64 : BitVec 64).toNat < s_o.core.cur_level at h
        have := hsp_o.2.1.cur_level_le; have := hsp_o.1.core_ok.trail_end_le
        have := hsp_o.1.core_ok.cur_vars_le; omega
      fvt_to_group
      refine wp_join_group (ts := [])
        (fun _ mf2 => ∃ sf : FullState, FullSparseInvW c F0 F_cur sf ∧
          sf.core.cur_vars = s.core.cur_vars ∧ sf.core.arena_len = s.core.arena_len ∧
          sf.core.probing = s.core.probing ∧ sf.core.fuel = s.core.fuel ∧
          fullArenaClauseRefs sf = fullArenaClauseRefs s ∧
          sf.scratch.red_refs = s.scratch.red_refs ∧
          sf.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ (FullMem c sf ⋆ R) mf2)
        (fun _ _ mf2 ⟨sf, hspf, hcvf, half, hprf, hfuf, hreff, hrrf, htrf, hmf2⟩ => by
          fvt_steps
          exact hQ 2#64 sf mf2 hspf hcvf half hprf hfuf hreff hrrf htrf
            (Or.inr (Or.inl rfl)) (fun h => by cases h) hmf2)
        (fun Jbo hJbo => by
          fvt_steps
          · c0_call hBacktrack
            refine ⟨c, s_o1, R, rfl, hsp_o1.1, hcl_o64, hbt_o, hsp_o1.2.1.trail_lits_lt, hm,
              fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
                hlen_bt _ _ _ hpres_bt hsc_bt _ _ hw_bt _ hm_bt => ?_⟩
            have hsp_bt := FullVivTop.FullSparseInvW.of_backtrack hsp_o1 (Nat.zero_le _) hlen_bt
              hpres_bt (hw_bt F0 F_cur hsp_o1.2.1 (Nat.zero_le _))
            rcases hsc_bt with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
            fvt_steps
            exact hJbo () m_bt ⟨_, hsp_bt, hcv_o, hal_o, hpr_o, hfu_o, href_o, hrr_o, htr_o, hm_bt⟩
          · exact hJbo () _ ⟨s_o1, hsp_o1, hcv_o, hal_o, hpr_o, hfu_o, href_o, hrr_o, htr_o, hm⟩))
    (fun Jo hJo => by
      fvt_steps; c0_call hWatchPush
      let l0 := s_f.scratch.work_stk2[0]'h0_sf
      let l1 := s_f.scratch.work_stk2[1]'h1_sf
      obtain ⟨hl1, lay1, hp1_1, hp1_2⟩ := m6_watchPush_pre (blk := l1) hsp_f hcref_lt8
      refine ⟨c, s_f, R, rfl, hl1, lay1, hp1_1, hp1_2, hmf,
        fun ok1 wvec3 wstk3 wlen3 wu3 wsort3 m5 hlen5 hlay5 hoth5 hok1_t hok1_f hm5 => ?_⟩
      have hsp5 := fullWatchPush_large_preserves_sparseInvW hsp_f
        (FullVivifyTactics.bv32_mask_lo31_props l1).1 hcref_lt8 (hrefs_f0 ▸ href) hlen5 hlay5
        hoth5 (fun h => let t := hok1_t h;
          ⟨t.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2 rfl⟩) (fun h => (hok1_f h).1)
      fvt_steps
      · c0_call hWatchPush
        obtain ⟨hl2, lay2, hp2_1, hp2_2⟩ := m6_watchPush_pre (blk := l0) hsp5 hcref_lt8
        refine ⟨c, _, R, rfl, hl2, lay2, hp2_1, hp2_2, hm5,
          fun ok2 wvec4 wstk4 wlen4 wu4 wsort4 m6 hlen6 hlay6 hoth6 hok2_t hok2_f hm6 => ?_⟩
        have hsp6 := fullWatchPush_large_preserves_sparseInvW hsp5
          (FullVivifyTactics.bv32_mask_lo31_props l0).1 hcref_lt8
          (by change cref.toNat ∈ fullArenaClauseRefs s_f; exact hrefs_f0 ▸ href)
          hlen6 hlay6 hoth6 (fun h => let t := hok2_t h;
            ⟨t.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2 rfl⟩) (fun h => (hok2_f h).1)
        fvt_steps
        · exact hQ 1#64 _ m6 hsp6 hcv3 hal3 hpr3 hfu3 hrefs_fs hrr3 htr3 (Or.inl rfl)
            (fun h => by cases h) hm6
        · exact hJo () m6 ⟨_, hsp6, hcv3, hal3, hpr3, hfu3, hrefs_fs, hrr3, htr3, hm6⟩
      · exact hJo () m5 ⟨_, hsp5, hcv3, hal3, hpr3, hfu3, hrefs_fs, hrr3, htr3, hm5⟩)

/-- `full_viv_commit_m6` satisfies `fullVivCommitM6Spec` parametrically in `Γ`. -/
theorem full_viv_commit_m6_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hUnwatch : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBinM6 : ∀ a m Q X, fullAddBinM6Spec a m Q X →
      Γ "full_add_bin_m6" [i64, i32, i32] [i64] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hUnreason : ∀ a m Q X, fullVivUnreasonM6Spec a m Q X →
      Γ "full_viv_unreason_m6" [i64, i32] [] a m Q X)
    (hBestWatch : ∀ a m Q X, fullVivBestWatchM6Spec a m Q X →
      Γ "full_viv_best_watch_m6" [i64, i32] [] a m Q X) :
    ∀ a m Q X, fullVivCommitM6Spec a m Q X →
      Func.wp Γ full_viv_commit_m6_body a m Q X := by
  rintro ⟨h, cref, olen, implied, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hsp, href, hng, holen_le_mv, hout_ok, hm0, hQ⟩
  have hw := hsp.2.1; have hcl := hsp.1.core_ok; have hscl := hsp.1.scratch_ok
  have hcap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hcap hmx
  have har_len := hcl.arena_len_arr; have halen_le := hcl.arena_len_le
  have hws2_len := hscl.work_stk2_len; have hcref_wf := hw.arena.refs_wf cref.toNat href
  have holen_le : olen.toNat ≤ 2 * c.max_vars := by omega
  have hcl_lt64 : s.core.cur_level < 2 ^ 64 := by
    have := hw.cur_level_le; have := hcl.trail_end_le; have := hcl.cur_vars_le; omega
  obtain ⟨hcref_lt, _, hcref0_eq, _, hcref2_eq, hcref3_eq, hcref4_eq, hhdr_ng_raw⟩ :=
    cref_hdr_facts (fv_sparseW_to_sparse hsp) hw href hng
  let hdr := s.core.arena[(cref.setWidth 64).toNat]'(by rw [hcref0_eq]; exact hcref_lt)
  let old_sz := s.core.arena[(cref.setWidth 64 + 2#64).toNat]'(by rw [hcref2_eq]; omega)
  have hhdr_eq : hdr = fullArenaHdr s cref.toNat := ar_get_eq_getD hcref0_eq _
  have hold_sz_eq : old_sz.toNat = fullArenaClauseSizeCore s.core cref.toNat :=
    congrArg BitVec.toNat (ar_get_eq_getD hcref2_eq _)
  have hold_sz_3 : 3 ≤ old_sz.toNat := by rw [hold_sz_eq]; exact hcref_wf.2.1
  have hold_sz_bd : cref.toNat + 3 + old_sz.toNat ≤ s.core.arena.length := by
    rw [hold_sz_eq]; omega
  have hhdr_ng : (hdr &&& 0x00080000#32) = 0#32 := by
    simpa [hhdr_eq, fullArenaHdr, fullArenaHdrCore] using hhdr_ng_raw
  have hcref3_lt : (cref.setWidth 64 + 3#64).toNat < s.core.arena.length := by omega
  have hcref4_lt : (cref.setWidth 64 + 4#64).toNat < s.core.arena.length := by omega
  have hsz_s_eq : fullArenaClauseSize s cref.toNat = old_sz.toNat := hold_sz_eq.symm
  let s1 : FullState :=
    { s with scratch := { s.scratch with viv_cnt := s.scratch.viv_cnt + 1#64 } }
  have hsp1 : FullSparseInvW c F0 F_cur s1 := m6_sparseW_with_vivcnt hsp _
  have hbt_lt_mv : ∀ t : BitVec 64, t.toNat < s1.core.cur_level → t.toNat < c.max_vars :=
    fun t h => by
      have := hw.cur_level_le; have := hcl.trail_end_le; have := hcl.cur_vars_le
      change t.toNat < s.core.cur_level at h; omega
  unfold Func.wp full_viv_commit_m6_body
  fvt_to_group
  · -- `olen >= old_sz`: no-op return `1ULL`
    exact hQ 1#64 s m0 hsp rfl rfl rfl rfl rfl rfl rfl (Or.inl rfl) (fun h => by cases h) hm0
  · -- `olen == 0` (`olen < old_sz`): backtrack to 0, set `inconsistent = 1`, ret `20ULL`
    have holen_lt : olen.toNat < old_sz.toNat := by dsimp only [old_sz]; c0_bound
    obtain ⟨_, _, hout_ent⟩ := hout_ok (by rw [hsz_s_eq]; exact holen_lt)
    have holen0 : olen.toNat = 0 := by c0_bound
    have hu : (cnfOfClauses F_cur).Unsat :=
      unsat_of_entails_nil (by simpa [holen0] using hout_ent)
    refine wp_join_group (ts := [])
      (fun _ mb => ∃ sb : FullState, FullSparseInvW c F0 F_cur sb ∧
        sb.core.cur_vars = s.core.cur_vars ∧ sb.core.arena_len = s.core.arena_len ∧
        sb.core.probing = s.core.probing ∧ sb.core.fuel = s.core.fuel ∧
        fullArenaClauseRefs sb = fullArenaClauseRefs s ∧
        sb.scratch.red_refs = s.scratch.red_refs ∧
        sb.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ (FullMem c sb ⋆ R) mb)
      (fun _ _ mb ⟨sb, hspb, hcvb, halb, hprb, hfub, hrefb, hrrb, htrb, hmb⟩ => by
        fvt_steps
        exact hQ 20#64 _ _ (m6_sparseW_with_inc hspb hu) hcvb halb hprb hfub hrefb hrrb htrb
          (Or.inr (Or.inr rfl)) (fun _ => hw.ext_sound.2 hu) hm)
      (fun Jb hJb => by
        fvt_steps
        · c0_call hBacktrack
          refine ⟨c, s1, R, rfl, hsp1.1, hcl_lt64, hbt_lt_mv 0#64, hw.trail_lits_lt, hm,
            fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
              hlen_bt _ _ _ hpres_bt hsc_bt _ _ hw_bt _ hm_bt => ?_⟩
          have hsp_bt := FullVivTop.FullSparseInvW.of_backtrack hsp1 (Nat.zero_le _) hlen_bt
            hpres_bt (hw_bt F0 F_cur hw (Nat.zero_le _))
          rcases hsc_bt with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
          fvt_steps
          exact hJb () m_bt ⟨_, hsp_bt, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm_bt⟩
        · exact hJb () _ ⟨s1, hsp1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm⟩)
  · -- `olen <= 2` (`olen ∈ {1, 2}`, `olen < old_sz`)
    have holen_lt : olen.toNat < old_sz.toNat := by dsimp only [old_sz]; c0_bound
    obtain ⟨hout_lt, _, hout_ent⟩ := hout_ok (by rw [hsz_s_eq]; exact holen_lt)
    have holen_ne0 : olen.toNat ≠ 0 := fun h =>
      (by c0_bound : olen ≠ 0#32) (BitVec.eq_of_toNat_eq h)
    have holen_le2 : olen.toNat ≤ 2 := by c0_bound
    refine wp_join_group (ts := [])
      (fun _ mb => ∃ sb : FullState, FullSparseInvW c F0 F_cur sb ∧ sb.core.cur_level = 0 ∧
        sb.core.arena = s.core.arena ∧ sb.core.cur_vars = s.core.cur_vars ∧
        sb.core.arena_len = s.core.arena_len ∧ sb.core.probing = s.core.probing ∧
        sb.core.fuel = s.core.fuel ∧ sb.scratch.work_stk2 = s.scratch.work_stk2 ∧
        sb.scratch.red_refs = s.scratch.red_refs ∧
        sb.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ (FullMem c sb ⋆ R) mb)
      (fun _ _ mb ⟨sb, hspb, hl0b, harb, hcvb, halb, hprb, hfub, hws2b, hrrb, htrb, hmb⟩ => by
        have hrefb : fullArenaClauseRefs sb = fullArenaClauseRefs s := by
          unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [harb, halb]
        have hhdrb : fullArenaHdr sb cref.toNat = hdr := by
          unfold fullArenaHdr fullArenaHdrCore; rw [harb]; exact hhdr_eq.symm
        have hcref3_b : (cref.setWidth 64 + 3#64).toNat < sb.core.arena.length := by
          rw [harb]; exact hcref3_lt
        have hcref4_b : (cref.setWidth 64 + 4#64).toNat < sb.core.arena.length := by
          rw [harb]; exact hcref4_lt
        fvt_steps; c0_call hUnwatch
        refine ⟨c, sb, R, rfl, hspb.1, m6_watchLayout hspb, hmb,
          fun wvec1 wstk1 wu1 m2 hlen1 hlay1 hmode1 hm2 => ?_⟩
        have hsp_w1 := m6_unwatch_sparse hspb hlen1 hmode1
        fvt_steps; c0_call hUnwatch
        refine ⟨c, _, R, rfl, hsp_w1.1, m6_watchLayout hsp_w1, hm2,
          fun wvec2 wstk2 wu2 m3 hlen2 hlay2 hmode2 hm3 => ?_⟩
        let s3 : FullState := { sb with core :=
          { sb.core with wvec := wvec2, wstk := wstk2, wusable := wu2 } }
        have hsp3 : FullSparseInvW c F0 F_cur s3 := m6_unwatch_sparse hsp_w1 hlen2 hmode2
        have hm3' : (FullMem c s3 ⋆ R) m3 := hm3
        clear hsp_w1 hlen1 hlay1 hmode1 hm2 hm3 wvec1 wstk1 wu1 m2 hlen2 hlay2 hmode2
        have hcref_lt3 : cref.toNat < s3.core.arena.length := by
          change cref.toNat < sb.core.arena.length; rw [harb]; exact hcref_lt
        fvt_to_group
        obtain ⟨hsp_g, hrefs_g0, _⟩ :=
          fv_markGarbW hsp3 hl0b (hrefb ▸ href)
            (sb.core.arena_garbage + 3#64 + old_sz.setWidth 64)
        let s_g : FullState := { s3 with core := { s3.core with
          arena := s3.core.arena.set cref.toNat (fullArenaHdr s3 cref.toNat ||| 0x00080000#32)
          arena_garbage := sb.core.arena_garbage + 3#64 + old_sz.setWidth 64 } }
        have hm_g : (FullMem c s_g ⋆ R) m := by
          have har_eq :
              s3.core.arena.set (cref.setWidth 64).toNat (hdr ||| 0x00080000#32) =
              s3.core.arena.set cref.toNat (fullArenaHdr s3 cref.toNat ||| 0x00080000#32) := by
            rw [hcref0_eq, show fullArenaHdr s3 cref.toNat = hdr from hhdrb]
          exact fullMem_eq_of_arena_ag_eq har_eq hm
        clear hm
        have hrefs_g : fullArenaClauseRefs s_g = fullArenaClauseRefs s := hrefs_g0.trans hrefb
        have hws2_g : s_g.scratch.work_stk2 = s.scratch.work_stk2 := hws2b
        refine m6_decr_count_wp Γ hm_g fun ni' nr' mg hmg => ?_
        let sg1 : FullState :=
          { s_g with core := { s_g.core with num_irred := ni', num_redundant := nr' } }
        have hmg' : (FullMem c sg1 ⋆ R) mg := hmg
        clear hmg
        have hsp_g1 := m6_sparseW_with_counts hsp_g ni' nr'
        have h0_ws2 : 0 < sg1.scratch.work_stk2.length := by
          change 0 < sb.scratch.work_stk2.length; rw [hws2b, hws2_len]; omega
        fvt_steps
        · -- `olen == 1`
          have holen1 : olen.toNat = 1 := by c0_bound
          have hu0_lt : (sg1.scratch.work_stk2[0]'h0_ws2).toNat < 2 * sg1.core.cur_vars := by
            have h := hout_lt 0 (by omega)
            rwa [← hws2_g, List.getElem?_eq_getElem h0_ws2, Option.getD_some, ← hcvb] at h
          have hu0_ent : (cnfOfClauses F_cur).EntailsClause
              (cnfClause [(sg1.scratch.work_stk2[0]'h0_ws2).toNat]) := by
            simpa only [← hws2_g] using take_entails_1 holen1 (by rw [hws2_len]; omega) hout_ent
          c0_call hAddUnit
          refine ⟨c, F0, F_cur, sg1, R, rfl, hsp_g1.1, hsp_g1.2.1, fun _ => hu0_ent, hmg',
            fun ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
              ph' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m4 hlen4 hw4 _ hltf _ hm4 => ?_⟩
          have hsp4 : FullSparseInvW c F0 F_cur _ :=
            ⟨hlen4, hw4, hsp_g1.2.2.1, hsp_g1.2.2.2.1, hsp_g1.2.2.2.2.1, hsp_g1.2.2.2.2.2⟩
          fvt_steps
          · exact hQ 1#64 _ m4 hsp4 hcvb halb hprb hfub hrefs_g hrrb htrb
              (Or.inl rfl) (fun h => by cases h) hm4
          · exact hQ 20#64 _ m4 hsp4 hcvb halb hprb hfub hrefs_g hrrb htrb
              (Or.inr (Or.inr rfl)) (fun _ => (hltf hu0_lt hc).1) hm4
        · -- `olen == 2`
          have holen2 : olen.toNat = 2 := by
            have : olen ≠ 1#32 := by c0_bound
            have : olen.toNat ≠ 1 := fun h => this (BitVec.eq_of_toNat_eq h)
            omega
          have h1_ws2 : 1 < sg1.scratch.work_stk2.length := by
            change 1 < sb.scratch.work_stk2.length; rw [hws2b, hws2_len]; omega
          have hu0_lt : (sg1.scratch.work_stk2[0]'h0_ws2).toNat < 2 * sg1.core.cur_vars := by
            have h := hout_lt 0 (by omega)
            rwa [← hws2_g, List.getElem?_eq_getElem h0_ws2, Option.getD_some, ← hcvb] at h
          have hu1_lt : (sg1.scratch.work_stk2[1]'h1_ws2).toNat < 2 * sg1.core.cur_vars := by
            have h := hout_lt 1 (by omega)
            rwa [← hws2_g, List.getElem?_eq_getElem h1_ws2, Option.getD_some, ← hcvb] at h
          have hbin_ent : (cnfOfClauses F_cur).EntailsClause
              (cnfClause [(sg1.scratch.work_stk2[0]'h0_ws2).toNat,
                          (sg1.scratch.work_stk2[1]'h1_ws2).toNat]) := by
            simpa only [← hws2_g] using take_entails_2 holen2 (by rw [hws2_len]; omega) hout_ent
          fvt_steps; c0_call hAddBinM6
          refine ⟨c, F0, F_cur, sg1, R, rfl, hsp_g1.1, hsp_g1.2.1, hl0b, fun _ _ => hbin_ent, hmg',
            fun br vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu'
              nb' oom' inc' ph' wso' m4 hlen4 hw4 _ h20 _ hm4 => ?_⟩
          have hsp4 : FullSparseInvW c F0 F_cur _ :=
            ⟨hlen4, hw4, hsp_g1.2.2.1, hsp_g1.2.2.2.1, hsp_g1.2.2.2.2.1, hsp_g1.2.2.2.2.2⟩
          fvt_steps
          · exact hQ 20#64 _ m4 hsp4 hcvb halb hprb hfub hrefs_g hrrb htrb
              (Or.inr (Or.inr rfl)) (fun _ => (h20 hc).1) hm4
          · exact hQ 2#64 _ m4 hsp4 hcvb halb hprb hfub hrefs_g hrrb htrb
              (Or.inr (Or.inl rfl)) (fun h => by cases h) hm4
          · exact hQ 1#64 _ m4 hsp4 hcvb halb hprb hfub hrefs_g hrrb htrb
              (Or.inl rfl) (fun h => by cases h) hm4)
      (fun Jb hJb => by
        fvt_steps
        · c0_call hBacktrack
          refine ⟨c, s1, R, rfl, hsp1.1, hcl_lt64, hbt_lt_mv 0#64, hw.trail_lits_lt, hm,
            fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
              hlen_bt _ _ hcl_bt hpres_bt hsc_bt _ _ hw_bt _ hm_bt => ?_⟩
          have hsp_bt := FullVivTop.FullSparseInvW.of_backtrack hsp1 (Nat.zero_le _) hlen_bt
            hpres_bt (hw_bt F0 F_cur hw (Nat.zero_le _))
          rcases hsc_bt with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
          fvt_steps
          exact hJb () m_bt ⟨_, hsp_bt, by simpa using hcl_bt, rfl, rfl, rfl, rfl, rfl, rfl,
            rfl, rfl, hm_bt⟩
        · have hcl0 : s1.core.cur_level = 0 := by
            have h0 : BitVec.ofNat 64 s.core.cur_level = 0#64 := by assumption
            have := congrArg BitVec.toNat h0
            rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_lt64] at this
          exact hJb () _ ⟨s1, hsp1, hcl0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm⟩)
  · -- `3 <= olen < old_sz`
    have holen_lt : olen.toNat < old_sz.toNat := by dsimp only [old_sz]; c0_bound
    obtain ⟨hout_lt, hout_nd, hout_ent⟩ := hout_ok (by rw [hsz_s_eq]; exact holen_lt)
    have holen3 : 3 ≤ olen.toNat := by
      have hgt2 : 2 < olen.toNat := by c0_bound
      omega
    refine wp_join_group (ts := [])
      (fun _ mp => ∃ sp : FullState, FullSparseInvW c F0 F_cur sp ∧
        sp.core.arena = s.core.arena ∧ sp.core.cur_vars = s.core.cur_vars ∧
        sp.core.arena_len = s.core.arena_len ∧ sp.core.probing = s.core.probing ∧
        sp.core.fuel = s.core.fuel ∧ sp.scratch.work_stk2 = s.scratch.work_stk2 ∧
        sp.scratch.red_refs = s.scratch.red_refs ∧
        sp.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ (FullMem c sp ⋆ R) mp)
      (fun _ _ mp ⟨sp, hspp, harp, hcvp, halp, hprp, hfup, hws2p, hrrp, htrp, hmp⟩ => by
        fvt_steps; c0_call hUnreason
        refine ⟨c, F0, F_cur, sp, R, rfl, hspp, hmp,
          fun su mu hspu hnonact hcvu haru halu hpru hfuu _ hws2u hrru htru hmu => ?_⟩
        have hlt_u : ∀ i < olen.toNat,
            (su.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * su.core.cur_vars := by
          rw [hws2u, hws2p, hcvu, hcvp]; exact hout_lt
        fvt_steps; c0_call hBestWatch
        refine ⟨c, su, R, rfl, hspu.1, holen_le_mv, hlt_u, hmu,
          fun ws2' mw hws2'_len hperm hmw => ?_⟩
        let sbw : FullState := { su with scratch := { su.scratch with work_stk2 := ws2' } }
        have hsp_bw : FullSparseInvW c F0 F_cur sbw := m6_sparseW_with_ws2 hspu hws2'_len
        obtain ⟨hout_lt', hout_nd', hout_ent'⟩ := m6_ws2_perm_props
          (by rw [hws2_len]; omega) (by rw [hws2'_len]; omega)
          (by rw [hws2u, hws2p] at hperm; exact hperm) hout_lt hout_nd hout_ent
        have hcref3_bw : (cref.setWidth 64 + 3#64).toNat < sbw.core.arena.length := by
          change _ < su.core.arena.length; rw [haru, harp]; exact hcref3_lt
        have hcref4_bw : (cref.setWidth 64 + 4#64).toNat < sbw.core.arena.length := by
          change _ < su.core.arena.length; rw [haru, harp]; exact hcref4_lt
        fvt_steps; c0_call hUnwatch
        refine ⟨c, sbw, R, rfl, hsp_bw.1, m6_watchLayout hsp_bw, hmw,
          fun wvec1 wstk1 wu1 m2 hlen1 hlay1 hmode1 hm2 => ?_⟩
        have hsp_w1 := m6_unwatch_sparse hsp_bw hlen1 hmode1
        fvt_steps; c0_call hUnwatch
        refine ⟨c, _, R, rfl, hsp_w1.1, m6_watchLayout hsp_w1, hm2,
          fun wvec2 wstk2 wu2 m3 hlen2 hlay2 hmode2 hm3 => ?_⟩
        let s3 : FullState := { sbw with core :=
          { sbw.core with wvec := wvec2, wstk := wstk2, wusable := wu2 } }
        have hsp3 : FullSparseInvW c F0 F_cur s3 := m6_unwatch_sparse hsp_w1 hlen2 hmode2
        have har3_eq : s3.core.arena = s.core.arena := haru.trans harp
        have hcv3 : s3.core.cur_vars = s.core.cur_vars := hcvu.trans hcvp
        have hal3 : s3.core.arena_len = s.core.arena_len := halu.trans halp
        have hpr3 : s3.core.probing = s.core.probing := hpru.trans hprp
        have hfu3 : s3.core.fuel = s.core.fuel := hfuu.trans hfup
        have hrr3 : s3.scratch.red_refs = s.scratch.red_refs := hrru.trans hrrp
        have htr3 : s3.scratch.tarjan_reach = s.scratch.tarjan_reach := htru.trans htrp
        have hrefs3 : fullArenaClauseRefs s3 = fullArenaClauseRefs s := by
          unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har3_eq, hal3]
        have hng3 : fullArenaClauseGarb s3 cref.toNat = false := by
          unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
          rw [har3_eq]; exact hng
        have hsz3 : fullArenaClauseSize s3 cref.toNat = old_sz.toNat := by
          unfold fullArenaClauseSize fullArenaClauseSizeCore; rw [har3_eq]; exact hsz_s_eq
        have hhdr3 : fullArenaHdr s3 cref.toNat = hdr := by
          unfold fullArenaHdr fullArenaHdrCore; rw [har3_eq]; exact hhdr_eq.symm
        have hnonact3 : NonActiveReason s3.core cref.toNat := hnonact
        have hm3' : (FullMem c s3 ⋆ R) m3 := hm3
        clear hsp_w1 hlen1 hlay1 hmode1 hm2 hm3 wvec1 wstk1 wu1 m2 hlen2 hlay2 hmode2 hsp_bw hmw
          hspu hmu hspp hmp
        fvt_to_group
        refine wp_loop_inv (ts := [i32])
          (fun (i, ()) m4 => ∃ ar4 : List (BitVec 32), i.toNat ≤ olen.toNat ∧
            ar4.length = c.arena_cap ∧
            (∀ k < i.toNat, ar4[cref.toNat + 3 + k]? = ws2'[k]?) ∧
            (∀ p, (p < cref.toNat + 3 ∨ cref.toNat + 3 + i.toNat ≤ p) →
              ar4[p]? = s3.core.arena[p]?) ∧
            (FullMem c { s3 with core := { s3.core with arena := ar4 } } ⋆ R) m4)
          (fun (i, ()) _ => olen.toNat - i.toNat) ?_ ?_
        · intro Jc hJc; fvt_steps
          exact hJc (0#32, ()) m3 ⟨s3.core.arena, by simp, by rw [har3_eq]; exact har_len,
            fun _ hk => by simp at hk, fun _ _ => rfl, hm3'⟩
        · rintro Jc ⟨i, ⟨⟩⟩ m4 ⟨ar4, hi_le, har4_len, hcp4, hout4, hm4⟩ ihc
          fvt_step; fvt_step
          · have hi_lt : i.toNat < olen.toNat := by c0_bound
            have hi_idx : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat =
                cref.toNat + 3 + i.toNat := by bv_omega
            have hi_lt_ar : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat < ar4.length := by
              omega
            have hi_lt_ws2 : i.toNat < ws2'.length := by omega
            have hi1_eq : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
            fvt_steps
            let ar5 := ar4.set (cref.toNat + 3 + i.toNat) (ws2'[i.toNat]'hi_lt_ws2)
            have har5_eq : ar4.set (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat
                (ws2'[i.toNat]'hi_lt_ws2) = ar5 := by simp only [ar5, hi_idx]
            refine ihc (i + 1#32, ()) _ (by dsimp only; omega)
              ⟨ar5, by omega, by simp [ar5, har4_len], fun k hk => ?_, fun p hp => ?_,
                fullMem_eq_of_arena_eq har5_eq hm⟩
            · rcases (by omega : k < i.toNat ∨ k = i.toNat) with hk' | rfl
              · dsimp only [ar5]; rw [List.getElem?_set_ne (by omega)]; exact hcp4 k hk'
              · dsimp only [ar5]
                rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem hi_lt_ws2]
            · dsimp only [ar5]; rw [List.getElem?_set_ne (by omega)]; exact hout4 p (by omega)
          · have hi_eq : i.toNat = olen.toNat := by c0_bound
            exact m6_commit_shrk_tail_wp Γ hBacktrack hWatchPush hsp3 (hrefs3 ▸ href) hrefs3
              hnonact3 hng3 hhdr3 hhdr_ng hsz3 hold_sz_3 holen3 holen_lt hcv3 hal3 hpr3 hfu3
              hrr3 htr3 (by change olen.toNat ≤ ws2'.length; omega)
              (by change ∀ j < olen.toNat, (ws2'[j]?.getD 0#32).toNat < 2 * s3.core.cur_vars
                  rw [hcv3]; exact hout_lt')
              hout_nd' hout_ent' har4_len (fun k hk => hcp4 k (by omega))
              (fun p hp => hout4 p (by omega)) hm4 hQ)
      (fun Jp hJp => by
        fvt_to_group
        · refine wp_join_group (ts := [])
            (fun _ mp => ∃ sp : FullState, FullSparseInvW c F0 F_cur sp ∧
              sp.core.arena = s.core.arena ∧ sp.core.cur_vars = s.core.cur_vars ∧
              sp.core.arena_len = s.core.arena_len ∧ sp.core.probing = s.core.probing ∧
              sp.core.fuel = s.core.fuel ∧ sp.scratch.work_stk2 = s.scratch.work_stk2 ∧
              sp.scratch.red_refs = s.scratch.red_refs ∧
              sp.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ (FullMem c sp ⋆ R) mp)
            (fun _ _ mp h => hJp () mp h)
            (fun Ji hJi => by
              fvt_steps
              · have htgt_lt : ((olen - 2#32).setWidth 64).toNat < s1.core.cur_level := by
                  have h1 : ((olen - 2#32).setWidth 64).toNat <
                      (BitVec.ofNat 64 s.core.cur_level).toNat := by c0_bound
                  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_lt64] at h1
                c0_call hBacktrack
                refine ⟨c, s1, R, rfl, hsp1.1, hcl_lt64,
                  hbt_lt_mv ((olen - 2#32).setWidth 64), hw.trail_lits_lt, hm,
                  fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
                    hlen_bt _ _ _ hpres_bt hsc_bt _ _ hw_bt _ hm_bt => ?_⟩
                have hsp_bt := FullVivTop.FullSparseInvW.of_backtrack hsp1 (Nat.le_of_lt htgt_lt)
                  hlen_bt hpres_bt (hw_bt F0 F_cur hw (Nat.le_of_lt htgt_lt))
                rcases hsc_bt with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
                fvt_steps
                exact hJi () m_bt ⟨_, hsp_bt, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm_bt⟩
              · exact hJi () _ ⟨s1, hsp1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm⟩)
        · exact hJp () _ ⟨s1, hsp1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm⟩)

end CommitProof

end LeanQbe.T.Examples.Kissat.FullM6VivBackbone
