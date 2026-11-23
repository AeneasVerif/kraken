module

public import LeanQbe.T.Examples.Kissat.FullM6VivBackbone
public import LeanQbe.T.Examples.Kissat.FullSpec3
public import LeanQbe.T.Examples.Kissat.FullBvaHeapSpec
public import LeanQbe.T.Examples.Kissat.FullVivifyLemmas1
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
public import LeanQbe.T.Examples.Kissat.FullM3BackboneLemmas1
import LeanQbe.T.Examples.Kissat.FullBinLuckyLemmas1
import LeanQbe.T.Examples.Kissat.FullBvaFwdLemmas1
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
import LeanQbe.T.Examples.Kissat.FullTransLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat M6 Vivification & Backbone Shared Proof Foundations & Base Overrides (`Proof0`)

Provides M1-clean (`public section`, `0` `import all`, `private` helpers) foundational lemmas
shared by `FullM6VivBackboneProof{1,2,3,}` plus parametric `Func.wp` proofs for:
1. Shared invariants & arena/watch/resolution lemmas:
   - `fullWitnessInv_set_hdr_non_gs` / `fullSparseInvW_set_hdr_non_gs`: arbitrary header edits
     preserving `PH_GARB` (bit 19) & `PH_SHRK` (bit 23) at any `cur_level`.
   - `inPlaceShrink_hnonact_preserves_fullWitness` / `fullSparseInvW_of_inPlaceShrink_hnonact`:
     prefix-preserving in-place clause shrinking at any `cur_level` under `NonActiveReason`.
   - `markGarb_hnonact_preserves_fullSparseW`: clause deletion at any `cur_level` under
     `NonActiveReason`.
   - `watchSliceOk_append` & `largeWatchBuf_to_slice`: binary-first watch-slice partitioning.
   - `inst_resolve_entails`: 1-step resolution for vivification instantiation strengthening.
   - `BackboneTrailInv` & 2-literal resolution lemmas for multi-level backbone 1UIP.
2. `full_add_bin_m6_ext_wp` & canonical `full_add_bin_m6_wp` (`Full.fullAddBinSpec`).
3. `full_init_fresh_var_m6_heap_wp` (`FullBvaHeap.fullInitFreshVarHeapSpec`) & canonical
   `full_init_fresh_var_m6_wp` (`Full.fullInitFreshVarSpec`).
4. `full_prioritize_binaries_m6_wp` (`fullPrioritizeBinariesM6Spec`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6VivBackbone

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. Shared Predicates & Cross-File Specs -/

/-- No trail literal in `0 ..< k.trail_end` currently uses large arena clause `cref` as its
reason. -/
@[expose] def NonActiveReason (k : FullCoreState) (cref : Nat) : Prop :=
  ∀ idx < k.trail_end,
    let rsn := k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
    rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ cref

/-- `ShrkPad` compatibility predicate for in-place clause shrinking. -/
@[expose] def M6ShrkPad (ar_p ar0 : List (BitVec 32)) (cref old_sz nsz : Nat) : Prop :=
  if (ar0[cref]?.getD 0#32 &&& 0x00800000#32) = 0#32 then
    (∀ k, cref + 3 + nsz ≤ k → k < cref + 3 + old_sz - 1 → ar_p[k]? = ar0[k]?) ∧
    ar_p[cref + 3 + old_sz - 1]? = some 0xFFFFFFFF#32
  else
    ∀ k, cref + 3 + nsz ≤ k → k < cref + 3 + old_sz → ar_p[k]? = ar0[k]?

/-- Extended `full_add_bin_m6` spec preserving `red_refs` and `tarjan_reach` (needed by vivify
callers) while refining canonical `Full.fullAddBinSpec`. -/
@[expose] def fullAddBinM6Spec : Spec [i64, i32, i32] [i64] := fun (h, a, b, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ s.core.cur_level = 0 ∧
    (a.toNat < 2 * s.core.cur_vars → b.toNat < 2 * s.core.cur_vars →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat])) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb' oom' inc'
      phases' wsort' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                unassigned := unass', unflushed := unfl', wvec := wvec',
                                wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                                oom := oom', inconsistent := inc' }
          scratch := { s.scratch with phases := phases', wsort := wsort' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat ∧ inc' ≠ 0#64) →
      (r = 2#64 → oom' ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Contract for `full_prioritize_binaries_m6(h)`: partitions binary watches ahead of large
watches in place using `scratch_buf`, preserving `FullSparseInvW` and all non-watch core fields. -/
@[expose] def fullPrioritizeBinariesM6Spec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) wstk' scr' m',
      let s' : FullState :=
        { s with
          core := { s.core with wstk := wstk' }
          scratch := { s.scratch with scratch_buf := scr' } }
      FullSparseInvW c F0 F_cur s' → (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Lightweight multi-level trail invariant used during one `full_backbone_round_m6` sweep.
Keeps the initial level-0 prefix `0 ..< saved0` untouched (including its `lvl` and `rsns`),
tracks valid level-0 entailed units (`lvl = 0`), and maintains binary-reason DAG edges on the
active probe decision level (`saved ..< trail_end`). -/
structure BackboneTrailInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 st : FullState) (saved0 : Nat) : Prop where
  len_ok : st.LengthsOk c
  s0_l0 : s0.core.cur_level = 0
  same_core : st.core =
    { s0.core with
      vals := st.core.vals, lvl := st.core.lvl, rsns := st.core.rsns,
      trl := st.core.trl, trail_end := st.core.trail_end, cur_level := st.core.cur_level,
      confl_lit0 := st.core.confl_lit0, confl_lit1 := st.core.confl_lit1 }
  same_scratch : st.scratch =
    { s0.scratch with
      ant_sz := st.scratch.ant_sz, res_sz := st.scratch.res_sz,
      work_stk1 := st.scratch.work_stk1, work_stk2 := st.scratch.work_stk2 }
  saved0_eq : saved0 = s0.core.trail_end
  saved0_le : saved0 ≤ st.core.trail_end
  trl_prefix : ∀ i < saved0, st.core.trl[i]? = s0.core.trl[i]?
  vals_prefix : ∀ l < 2 * s0.core.cur_vars,
    s0.core.vals[l]?.getD 0#8 ≠ 0#8 → st.core.vals[l]?.getD 0#8 = s0.core.vals[l]?.getD 0#8
  vals_hi : ∀ l, 2 * s0.core.cur_vars ≤ l → st.core.vals[l]? = s0.core.vals[l]?
  lvl_prefix : ∀ i < saved0,
    let v := (s0.core.trl[i]?.getD 0#32).toNat / 2
    st.core.lvl[v]? = s0.core.lvl[v]? ∧ st.core.rsns[v]? = s0.core.rsns[v]?
  trl_lits_lt : ∀ i < st.core.trail_end, (st.core.trl[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars
  trl_vars_nodup : ∀ i j, i < st.core.trail_end → j < st.core.trail_end →
    (st.core.trl[i]?.getD 0#32).toNat / 2 = (st.core.trl[j]?.getD 0#32).toNat / 2 → i = j
  trl_vals_ok : ∀ i < st.core.trail_end,
    let l := (st.core.trl[i]?.getD 0#32).toNat
    st.core.vals[l]?.getD 0#8 = 1#8 ∧ st.core.vals[l ^^^ 1]?.getD 0#8 = 0xFF#8
  vals_dom : ∀ l < 2 * s0.core.cur_vars,
    st.core.vals[l]?.getD 0#8 = 0#8 ∨ st.core.vals[l]?.getD 0#8 = 1#8 ∨
    st.core.vals[l]?.getD 0#8 = 0xFF#8
  vals_true_trl : ∀ l < 2 * s0.core.cur_vars,
    st.core.vals[l]?.getD 0#8 = 1#8 →
    ∃ i < st.core.trail_end, (st.core.trl[i]?.getD 0#32).toNat = l
  vals_false_trl : ∀ l < 2 * s0.core.cur_vars,
    st.core.vals[l]?.getD 0#8 = 0xFF#8 →
    ∃ i < st.core.trail_end, (st.core.trl[i]?.getD 0#32).toNat = l ^^^ 1
  lvl_le_cur : ∀ i < st.core.trail_end,
    (st.core.lvl[(st.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ st.core.cur_level
  l0_entails : ∀ i < st.core.trail_end,
    (st.core.lvl[(st.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 →
    (cnfOfClauses F_cur).EntailsClause (cnfClause [(st.core.trl[i]?.getD 0#32).toNat])

/-- Active probe-level binary-reason DAG invariant on `trl[saved ..< st.core.trail_end)`. -/
@[expose] def BackboneProbeSeg (F_cur : List (List Nat)) (st : FullState)
    (saved target_lvl : Nat) : Prop :=
  saved < st.core.trail_end ∧
  (∀ i < saved,
    (st.core.lvl[(st.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < target_lvl) ∧
  (∀ i, saved ≤ i → i < st.core.trail_end →
    let p := (st.core.trl[i]?.getD 0#32).toNat
    (st.core.lvl[p / 2]?.getD 0#32).toNat = target_lvl ∧
    (saved < i →
      let rsn := st.core.rsns[p / 2]?.getD 0xFFFFFFFF#32
      (rsn &&& 0x80000000#32) ≠ 0#32 ∧
      let not_q := (rsn &&& 0x7FFFFFFF#32).toNat
      not_q < 2 * st.core.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [p, not_q]) ∧
      ∃ m, saved ≤ m ∧ m < i ∧ (st.core.trl[m]?.getD 0#32).toNat = not_q ^^^ 1))

/-! ## 2. Pure Bitvector, Arena Header, Shrink, & Mark-Garbage Lemmas -/

section ArenaCoreLemmas

theorem bv32_and_not_red_garb (x : BitVec 32) :
    ((x &&& ~~~0x00400000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) := by
  rw [BitVec.and_assoc, show (~~~0x00400000#32 &&& 0x00080000#32) = 0x00080000#32 from rfl]

theorem bv32_and_not_red_shrk (x : BitVec 32) :
    ((x &&& ~~~0x00400000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) := by
  rw [BitVec.and_assoc, show (~~~0x00400000#32 &&& 0x00800000#32) = 0x00800000#32 from rfl]

theorem bv32_set_glue_garb (x g : BitVec 32) (hg : (g &&& 0x00080000#32) = 0#32) :
    (((x &&& ~~~0x7FFFF#32) ||| g) &&& 0x00080000#32) = (x &&& 0x00080000#32) := by
  rw [BitVec.and_or_distrib_right, hg, BitVec.or_zero, BitVec.and_assoc,
    show (~~~0x7FFFF#32 &&& 0x00080000#32) = 0x00080000#32 from rfl]

theorem bv32_set_glue_shrk (x g : BitVec 32) (hg : (g &&& 0x00800000#32) = 0#32) :
    (((x &&& ~~~0x7FFFF#32) ||| g) &&& 0x00800000#32) = (x &&& 0x00800000#32) := by
  rw [BitVec.and_or_distrib_right, hg, BitVec.or_zero, BitVec.and_assoc,
    show (~~~0x7FFFF#32 &&& 0x00800000#32) = 0x00800000#32 from rfl]

theorem bv32_glue_mask_garb (y : BitVec 32) :
    ((y &&& 0x7FFFF#32) &&& 0x00080000#32) = 0#32 := by
  rw [BitVec.and_assoc, show (0x7FFFF#32 &&& 0x00080000#32) = 0#32 from rfl, BitVec.and_zero]

theorem bv32_glue_mask_shrk (y : BitVec 32) :
    ((y &&& 0x7FFFF#32) &&& 0x00800000#32) = 0#32 := by
  rw [BitVec.and_assoc, show (0x7FFFF#32 &&& 0x00800000#32) = 0#32 from rfl, BitVec.and_zero]

/-- Arbitrary header update on `cref ∈ fullArenaClauseRefsCore k` preserving `PH_GARB` (bit 19)
and `PH_SHRK` (bit 23) preserves `FullWitnessInv`, `fullArenaClauseRefsCore`, and all clause
sizes/garbage/literals at ANY `cur_level` (covers `PH_VIV`, `PH_RED` promotion, glue update). -/
theorem fullWitnessInv_set_hdr_non_gs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c) (hw : FullWitnessInv c F0 F_cur k)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefsCore k) (v : BitVec 32)
    (h19 : (v &&& 0x00080000#32) = (fullArenaHdrCore k cref &&& 0x00080000#32))
    (h23 : (v &&& 0x00800000#32) = (fullArenaHdrCore k cref &&& 0x00800000#32)) :
    let k' : FullCoreState := { k with arena := k.arena.set cref v }
    k'.LengthsOk c ∧ fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    FullWitnessInv c F0 F_cur k' ∧
    (∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) := by
  intro k'
  have hcref_wf := hw.arena.refs_wf cref href
  have har_len : cref < k.arena.length := by
    have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
  have ha_cref : k'.arena[cref]? = some v := List.getElem?_set_self har_len
  have hne_out : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore k r ≤ cref ∧
        fullArenaNextOff k.arena k.arena_len r ≤ cref) ∨
      (cref + 3 ≤ fullArenaNextOff k.arena k.arena_len cref ∧
        fullArenaNextOff k.arena k.arena_len cref ≤ r) := fun r hr hne => by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨by have := fullArenaScanRefs_disjoint hr href hlt
                       have := (hw.arena.refs_wf r hr).2.2.1; omega,
        fullArenaScanRefs_disjoint hr href hlt⟩
    · exact Or.inr ⟨by omega, fullArenaScanRefs_disjoint href hr hgt⟩
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaNextOff k'.arena k.arena_len r = fullArenaNextOff k.arena k.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst r
      have h2eq : k'.arena[cref + 2]? = k.arena[cref + 2]? := List.getElem?_set_ne (by omega)
      have h1 : ¬ (cref + 3 > k.arena_len) := by omega
      have h2 : ¬ (cref + 3 + (k.arena[cref + 2]?.getD 0#32).toNat > k.arena_len) := by
        unfold fullArenaClauseSizeCore at hcref_wf; omega
      unfold fullArenaNextOff
      simp only [h1, ↓reduceIte, h2eq, h2, ha_cref, Option.getD_some]
      rw [h23, show fullArenaHdrCore k cref = k.arena[cref]?.getD 0#32 from rfl]
      split
      · exact fullArenaSkipShrk_congr fun i hi _ => List.getElem?_set_ne (by omega)
      · rfl
    · refine fullArenaNextOff_congr_block (List.getElem?_set_ne (Ne.symm hrc)) ?_ ?_
      · rcases hne_out r hr hrc with ⟨hlt, _⟩ | ⟨_, hgt⟩
        · have := (hw.arena.refs_wf r hr).2.1; exact List.getElem?_set_ne (by omega)
        · exact List.getElem?_set_ne (by omega)
      · intro i hi1 _
        rcases hne_out r hr hrc with ⟨_, hle⟩ | ⟨_, hgt⟩
        · exact List.getElem?_set_ne (by omega)
        · have := (hw.arena.refs_wf r hr).2.2.1; exact List.getElem?_set_ne (by omega)
  have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hsz_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r := fun r hr => by
    unfold fullArenaClauseSizeCore; dsimp only [k']
    by_cases hrc : r = cref
    · subst r; rw [List.getElem?_set_ne (by omega)]
    · rcases hne_out r hr hrc with ⟨hlt, _⟩ | ⟨_, hgt⟩
      · have := (hw.arena.refs_wf r hr).2.1; rw [List.getElem?_set_ne (by omega)]
      · rw [List.getElem?_set_ne (by omega)]
  have hgarb_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := fun r hr => by
    unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [k']
    by_cases hrc : r = cref
    · subst r; rw [List.getElem?_set_self har_len, Option.getD_some, h19]; rfl
    · rw [List.getElem?_set_ne (Ne.symm hrc)]
  have hlits_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := fun r hr => by
    have hwf := hw.arena.refs_wf r hr
    have hk_bd : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length := by
      have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
    refine fullArenaClauseLitsCore_eq_of_hold hk_bd (by simpa [k'] using hk_bd) (hsz_eq r hr) ?_
    intro j hj; dsimp only [k']; apply List.getElem?_set_ne
    by_cases hrc : r = cref
    · subst r; omega
    · rcases hne_out r hr hrc with ⟨h1, _⟩ | ⟨_, h2⟩ <;> omega
  have harena' : FullArenaClausesInv c F_cur k' := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; dsimp only [k'] at hnxt ⊢
      rw [hnxt r hr, hsz_eq r hr]; exact hw.arena.refs_wf r hr
    · intro r hr hsh; rw [hrefs] at hr
      have hsh0 : (fullArenaHdrCore k r &&& 0x00800000#32) ≠ 0#32 := by
        by_cases hrc : r = cref
        · subst r; unfold fullArenaHdrCore at hsh h23 ⊢; simpa [ha_cref, h23] using hsh
        · unfold fullArenaHdrCore at hsh ⊢
          simpa [k', List.getElem?_set_ne (Ne.symm hrc)] using hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
      have hget_r : k.arena[r]? = some (fullArenaHdrCore k r) := by
        have hr3 := (hw.arena.refs_wf r hr).1
        have : r < k.arena.length := by
          have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
      obtain ⟨t0, ht0_lo, _, _, ht0_sent⟩ :=
        fullArenaNextOff_hits_sentinel (hw.arena.refs_wf r hr).1
          (by rw [hget_r, Option.getD_some]; exact hsh0) ht1 ht2 hsent
      have ht0_ne : t0 ≠ cref := by
        by_cases hrc : r = cref
        · subst r; have := (hw.arena.refs_wf cref hr).2.1; omega
        · rcases hne_out r hr hrc with ⟨_, _⟩ | ⟨_, _⟩
          · omega
          · have := (hw.arena.refs_wf r hr).2.1; omega
      have hnxt_le : fullArenaNextOff k.arena k.arena_len r ≤ k.arena_len :=
        (hw.arena.refs_wf r hr).2.2.2.1
      refine ⟨t0, by rw [hsz_eq r hr]; exact ht0_lo, by dsimp only [k']; omega, ?_⟩
      dsimp only [k']; rw [List.getElem?_set_ne ht0_ne.symm]; exact ht0_sent
    · intro r hr hng l hl; rw [hrefs] at hr
      rw [hgarb_eq r hr] at hng; rw [hlits_eq r hr] at hl
      exact hw.arena.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      rw [hgarb_eq r hr] at hng; rw [hlits_eq r hr]
      exact hw.arena.entails r hr hng
  refine ⟨{ hlen with arena_len_arr := by simp [k', hlen.arena_len_arr] }, hrefs,
    { hw with
      arena := harena'
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hrefs ▸ hr)
      reason_inv := fun idx hidx hne => by
        have hrs := hw.reason_inv idx hidx hne
        dsimp only [k'] at hrs ⊢
        by_cases hbin : (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
        · rw [ite_eq_left hbin] at hrs ⊢; exact hrs
        · rw [ite_eq_right hbin] at hrs ⊢
          let r := (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat
          exact ⟨hrefs ▸ hrs.1, (hgarb_eq r hrs.1).trans hrs.2.1,
            fun q hq => hrs.2.2 q ((hlits_eq r hrs.1) ▸ hq)⟩
      reason_lit_mem := fun idx hidx hne hlg => by
        have hrs := hw.reason_inv idx hidx hne
        have hbf : ¬ (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
        rw [ite_eq_right hbf] at hrs
        dsimp only [k']
        rw [hlits_eq _ hrs.1]
        exact hw.reason_lit_mem idx hidx hne hlg },
    fun r hr => ⟨hgarb_eq r hr, hsz_eq r hr, hlits_eq r hr⟩⟩

/-- `FullSparseInvW` wrapper for `fullWitnessInv_set_hdr_non_gs` (with optional `num_irred` /
`num_redundant` updates). -/
theorem fullSparseInvW_set_hdr_non_gs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (v : BitVec 32)
    (ni' nr' : BitVec 64)
    (h19 : (v &&& 0x00080000#32) = (fullArenaHdr s cref &&& 0x00080000#32))
    (h23 : (v &&& 0x00800000#32) = (fullArenaHdr s cref &&& 0x00800000#32)) :
    let s' : FullState :=
      { s with core :=
        { s.core with arena := s.core.arena.set cref v,
                      num_irred := ni', num_redundant := nr' } }
    FullSparseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
      fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
      fullArenaClauseLits s' r = fullArenaClauseLits s r) := by
  intro s'
  obtain ⟨hlen_c, hrefs, hw', hall⟩ :=
    fullWitnessInv_set_hdr_non_gs hsp.1.core_ok hsp.2.1 href v h19 h23
  have hlen' : s'.LengthsOk c := ⟨{ hlen_c with }, hsp.1.scratch_ok⟩
  have hw_s' : FullWitnessInv c F0 F_cur s'.core :=
    { hw' with
      arena := { hw'.arena with len_ok := hw'.arena.len_ok }
      watches := hw'.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
  have hrefs' : fullArenaClauseRefs s' = fullArenaClauseRefs s := hrefs
  have hnd' : FullArenaVarsNodup s' := fun r hr hng => by
    have hr0 : r ∈ fullArenaClauseRefs s := hrefs' ▸ hr
    obtain ⟨hg, _, hl⟩ := hall r hr0
    have hl' : fullArenaClauseLits s' r = fullArenaClauseLits s r := hl
    have hg' : fullArenaClauseGarb s' r = fullArenaClauseGarb s r := hg
    rw [hl']; exact hsp.2.2.2.1 r hr0 (hg'.symm.trans hng)
  have hext' : FullExtScratchOk c s' :=
    ⟨fun i hi => (hsp.2.2.2.2.1.1 i hi).imp id (fun h => hrefs' ▸ h), hsp.2.2.2.2.1.2⟩
  exact ⟨⟨hlen', hw_s', hsp.2.2.1, hnd', hext', hsp.2.2.2.2.2⟩, hrefs', hall⟩

private theorem fullArenaSkipShrk_step_range_m6 {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {p q : Nat}, p ≤ q → q ≤ alen →
      (∀ k, p ≤ k → k < q → ar[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) →
      fullArenaSkipShrk ar alen p (alen - p) = fullArenaSkipShrk ar alen q (alen - q) := by
  suffices h : ∀ d p q, p + d = q → q ≤ alen →
      (∀ k, p ≤ k → k < q → ar[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) →
      fullArenaSkipShrk ar alen p (alen - p) = fullArenaSkipShrk ar alen q (alen - q) from
    fun {p q} hle hqa hne => h (q - p) p q (by omega) hqa hne
  intro d; induction d with
  | zero => intro p q hpq _ _; rw [show p = q by omega]
  | succ d ih =>
    intro p q hpq hqa hne
    have hpa : p < alen := by omega
    have hf : alen - p = (alen - (p + 1)) + 1 := by omega
    have hnep : ar[p]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := hne p (Nat.le_refl p) (by omega)
    have hstep1 : ∀ f, fullArenaSkipShrk ar alen p (f + 1) =
        fullArenaSkipShrk ar alen (p + 1) f := fun f => by simp [fullArenaSkipShrk, hpa, hnep]
    rw [hf, hstep1]
    exact ih (p + 1) q (by omega) hqa fun k hk1 hk2 => hne k (by omega) hk2

/-- Prefix-preserving in-place clause shrinking at ANY `cur_level` under `NonActiveReason`:
generalizes `inPlaceShrink_preserves_fullWitness` (`FullVivifyLemmas1`) from `cur_level = 0` to
`NonActiveReason s.core cref`. -/
theorem inPlaceShrink_hnonact_preserves_fullWitness {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    {cref nsz : Nat} (href : cref ∈ fullArenaClauseRefs s)
    (hnonact : NonActiveReason s.core cref)
    (hng : fullArenaClauseGarb s cref = false)
    (hnsz3 : 3 ≤ nsz) (hnsz_lt : nsz < fullArenaClauseSize s cref)
    {arena' : List (BitVec 32)} {ni' nr' : BitVec 64} {sc' : FullScratch}
    (hal' : arena'.length = c.arena_cap) (hsc' : sc'.LengthsOk c)
    (hout : ∀ k, (k < cref ∨ cref + 3 + fullArenaClauseSize s cref ≤ k) →
      arena'[k]? = s.core.arena[k]?)
    (hnhdr_garb : (arena'[cref]?.getD 0#32 &&& 0x00080000#32) = 0#32)
    (hnhdr_shrk : (arena'[cref]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32)
    (hnsz_eq : (arena'[cref + 2]?.getD 0#32).toNat = nsz)
    (hpad_old : M6ShrkPad arena' s.core.arena cref (fullArenaClauseSize s cref) nsz)
    (hlits_lt : ∀ j < nsz, (arena'[cref + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore { s.core with arena := arena' } cref))) :
    let s' : FullState :=
      { s with
        core := { s.core with arena := arena', num_irred := ni', num_redundant := nr' }
        scratch := sc' }
    s'.LengthsOk c ∧ FullWitnessInv c F0 F_cur s'.core ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    fullArenaClauseGarb s' cref = false ∧ fullArenaClauseSize s' cref = nsz ∧
    (∀ r ∈ fullArenaClauseRefs s,
      fullArenaNextOff s'.core.arena s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r) := by
  intro s'
  dsimp only [fullArenaClauseRefs, fullArenaClauseSize, fullArenaClauseGarb,
    fullArenaClauseLits, fullArenaHdr, M6ShrkPad] at *
  have hcl := hlen.core_ok
  have hcref_wf := hw.arena.refs_wf cref href
  have hold_bd : cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena.length := by
    have := hcl.arena_len_arr; have := hcl.arena_len_le; omega
  have hold_ne_ff : ∀ k, cref + 3 ≤ k → k < cref + 3 + fullArenaClauseSizeCore s.core cref →
      s.core.arena[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
    intro k hk1 hk2
    let j := k - (cref + 3)
    have hj : j < fullArenaClauseSizeCore s.core cref := by omega
    have hmem : (s.core.arena[cref + 3 + j]'(by omega)).toNat ∈
        fullArenaClauseLitsCore s.core cref :=
      (mem_fullArenaClauseLitsCore_iff hold_bd).mpr ⟨j, hj, rfl⟩
    have hlt := hw.arena.lits_lt cref href hng _ hmem
    have hcv := hcl.cur_vars_le; have hmax := c.hmaxv; unfold dimacsBound at hmax
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    intro heq
    have h1 : (s.core.arena[cref + 3 + j]'(by omega)).toNat = 0xFFFFFFFF := by
      have hidx_eq : cref + 3 + j = k := by omega
      simp only [hidx_eq, heq]; rfl
    omega
  have hnxt_cref : fullArenaNextOff arena' s.core.arena_len cref =
      fullArenaNextOff s.core.arena s.core.arena_len cref := by
    have h1 : ¬ (cref + 3 > s.core.arena_len) := by omega
    have h2 : ¬ (cref + 3 + (s.core.arena[cref + 2]?.getD 0#32).toNat > s.core.arena_len) := by
      unfold fullArenaClauseSizeCore at hcref_wf; omega
    have h2n : ¬ (cref + 3 + nsz > s.core.arena_len) := by omega
    unfold fullArenaNextOff
    simp only [h1, h2, hnhdr_shrk, hnsz_eq, h2n, ↓reduceIte, ne_eq, not_false_eq_true]
    by_cases hsh0 : (s.core.arena[cref]?.getD 0#32 &&& 0x00800000#32) = 0#32
    · rw [ite_eq_left hsh0] at hpad_old
      obtain ⟨hkeep, hterm⟩ := hpad_old
      have hsh0' : ¬ ((s.core.arena[cref]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32) := by
        simpa using hsh0
      rw [ite_eq_right hsh0']
      have hstep := fullArenaSkipShrk_step_range_m6 (ar := arena') (alen := s.core.arena_len)
        (p := cref + 3 + nsz) (q := cref + 3 + fullArenaClauseSizeCore s.core cref - 1)
        (by omega) (by omega) fun k hk1 hk2 => by
          rw [hkeep k hk1 hk2]; exact hold_ne_ff k (by omega) (by omega)
      rw [hstep]
      have hfl : s.core.arena_len - (cref + 3 + fullArenaClauseSizeCore s.core cref - 1) =
          (s.core.arena_len - (cref + 3 + fullArenaClauseSizeCore s.core cref)) + 1 := by omega
      have hlt_a : cref + 3 + fullArenaClauseSizeCore s.core cref - 1 < s.core.arena_len := by
        omega
      rw [hfl]; unfold fullArenaSkipShrk
      simp only [hlt_a, hterm, Option.getD_some, ↓reduceIte, ne_eq, not_true_eq_false]
      have hsz_def : fullArenaClauseSizeCore s.core cref =
          (s.core.arena[cref + 2]?.getD 0#32).toNat := rfl
      omega
    · rw [ite_eq_right hsh0] at hpad_old
      rw [ite_eq_left hsh0]
      have hstep := fullArenaSkipShrk_step_range_m6 (ar := arena') (alen := s.core.arena_len)
        (p := cref + 3 + nsz) (q := cref + 3 + fullArenaClauseSizeCore s.core cref)
        (by omega) (by omega) fun k hk1 hk2 => by
          rw [hpad_old k hk1 hk2]; exact hold_ne_ff k (by omega) hk2
      rw [hstep]
      exact fullArenaSkipShrk_congr fun k hk1 _ => hout k (Or.inr hk1)
  have hne_out : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∧
        fullArenaNextOff s.core.arena s.core.arena_len r ≤ cref) ∨
      (cref + 3 + fullArenaClauseSizeCore s.core cref ≤ r) := fun r hr hne => by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨by have := fullArenaScanRefs_disjoint hr href hlt
                       have := (hw.arena.refs_wf r hr).2.2.1; omega,
        fullArenaScanRefs_disjoint hr href hlt⟩
    · exact Or.inr (by have := fullArenaScanRefs_disjoint href hr hgt; omega)
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff arena' s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst r; exact hnxt_cref
    · rcases hne_out r hr hrc with ⟨_, hle⟩ | hge
      · refine fullArenaNextOff_congr_block (hout r (Or.inl (by omega)))
          (hout (r + 2) (Or.inl (by have := (hw.arena.refs_wf r hr).2.1; omega)))
          fun k _ hk2 => hout k (Or.inl (by omega))
      · refine fullArenaNextOff_congr_block (hout r (Or.inr hge))
          (hout (r + 2) (Or.inr (by omega)))
          fun k hk1 _ => hout k (Or.inr (by omega))
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hoth_eq : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r ∧
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := by
    intro r hr hne
    have hr_wf := hw.arena.refs_wf r hr
    have hr_bd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
      have := hcl.arena_len_arr; have := hcl.arena_len_le; omega
    have hout_r : ∀ p, r ≤ p → p < r + 3 + fullArenaClauseSizeCore s.core r →
        arena'[p]? = s.core.arena[p]? := fun p _ _ => by
      rcases hne_out r hr hne with ⟨hlt, _⟩ | hge
      · exact hout p (Or.inl (by omega))
      · exact hout p (Or.inr (by omega))
    have hgb : fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := by
      unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']
      rw [hout_r r (by omega) (by omega)]
    have hsz : fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := by
      unfold fullArenaClauseSizeCore; dsimp only [s']
      rw [hout_r (r + 2) (by omega) (by omega)]
    have hlits := fullArenaClauseLitsCore_eq_of_hold hr_bd
      (by rw [hal', ← hcl.arena_len_arr]; exact hr_bd) hsz
      fun j hj => hout_r (r + 3 + j) (by omega) (by omega)
    exact ⟨hgb, hsz, hlits⟩
  have hgarb_c : fullArenaClauseGarbCore s'.core cref = false := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']; simp [hnhdr_garb]
  have hsz_c : fullArenaClauseSizeCore s'.core cref = nsz := hnsz_eq
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; dsimp only [s'] at hnxt ⊢
      rw [hnxt r hr]
      by_cases hrc : r = cref
      · subst r; rw [hsz_c]; exact ⟨hcref_wf.1, hnsz3, by omega, hcref_wf.2.2.2.1, hcref_wf.2.2.2.2⟩
      · rw [(hoth_eq r hr hrc).2.1]; exact hw.arena.refs_wf r hr
    · intro r hr hsh; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r
        by_cases hsh0 : (s.core.arena[cref]?.getD 0#32 &&& 0x00800000#32) = 0#32
        · rw [ite_eq_left hsh0] at hpad_old
          have := hcref_wf.2.2.1; have := hcref_wf.2.2.2.1
          exact ⟨cref + 3 + fullArenaClauseSizeCore s.core cref - 1,
            by rw [hsz_c]; omega, by dsimp only [s']; omega, hpad_old.2⟩
        · have hsh0' : (fullArenaHdrCore s.core cref &&& 0x00800000#32) ≠ 0#32 := hsh0
          obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term cref hr hsh0'
          refine ⟨t, by rw [hsz_c]; omega, ht2, ?_⟩
          dsimp only [s']; rw [hout t (Or.inr ht1)]; exact hsent
      · have hr_wf := hw.arena.refs_wf r hr
        have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore at hsh ⊢; dsimp only [s'] at hsh
          rcases hne_out r hr hrc with ⟨hlt, _⟩ | hge
          · rwa [hout r (Or.inl (by omega))] at hsh
          · rwa [hout r (Or.inr hge)] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
        have hget_r : s.core.arena[r]? = some (fullArenaHdrCore s.core r) := by
          have : r < s.core.arena.length := by
            have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
          unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
        obtain ⟨t0, ht0_lo, _, ht0_nxt, ht0_sent⟩ :=
          fullArenaNextOff_hits_sentinel hr_wf.1
            (by rw [hget_r, Option.getD_some]; exact hsh0) ht1 ht2 hsent
        have hr_nxt_le := hr_wf.2.2.2.1
        refine ⟨t0, by rw [(hoth_eq r hr hrc).2.1]; exact ht0_lo, by dsimp only [s']; omega, ?_⟩
        dsimp only [s']
        rcases hne_out r hr hrc with ⟨_, hle⟩ | hge
        · rw [hout t0 (Or.inl (by omega))]; exact ht0_sent
        · rw [hout t0 (Or.inr (by omega))]; exact ht0_sent
    · intro r hr hngr l hl; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r
        have hbd' : cref + 3 + fullArenaClauseSizeCore s'.core cref ≤ s'.core.arena.length := by
          rw [hsz_c]; dsimp only [s']; rw [hal']; have := hcl.arena_len_le
          have := hcref_wf.2.2.1; have := hcref_wf.2.2.2.1; omega
        obtain ⟨j, hj, hjl⟩ := (mem_fullArenaClauseLitsCore_iff hbd').mp hl
        rw [hsz_c] at hj
        have hlt := hlits_lt j hj
        have hjl_bd : cref + 3 + j < arena'.length := by
          rw [hsz_c] at hbd'; dsimp only [s'] at hbd'; omega
        rw [List.getElem?_eq_getElem hjl_bd, Option.getD_some] at hlt
        exact hjl ▸ hlt
      · obtain ⟨hg, _, hli⟩ := hoth_eq r hr hrc
        exact hw.arena.lits_lt r hr (hg ▸ hngr) l (hli ▸ hl)
    · intro r hr hngr; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; exact hent
      · obtain ⟨hg, _, hli⟩ := hoth_eq r hr hrc
        rw [hli]; exact hw.arena.entails r hr (hg ▸ hngr)
  have hlen' : s'.LengthsOk c := ⟨{ hcl with arena_len_arr := by simp [s', hal'] }, hsc'⟩
  refine ⟨hlen', { hw with
    arena := harena'
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hrefs ▸ hr)
    reason_inv := fun idx hidx hne => by
      have hrs := hw.reason_inv idx hidx hne
      dsimp only [s'] at hrs ⊢
      by_cases hbin : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
      · rw [ite_eq_left hbin] at hrs ⊢; exact hrs
      · have hlg' : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32 :=
          Classical.byContradiction fun hn => hbin hn
        rw [ite_eq_right hbin] at hrs ⊢
        let r := (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat
        have hne_c := hnonact idx hidx hne hlg'
        obtain ⟨hg, _, hl⟩ := hoth_eq r hrs.1 hne_c
        exact ⟨hrefs ▸ hrs.1, hg.trans hrs.2.1, fun q hq => hrs.2.2 q (hl ▸ hq)⟩
    reason_lit_mem := fun idx hidx hne hlg => by
      have hrs := hw.reason_inv idx hidx hne
      have hbf : ¬ (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
      rw [ite_eq_right hbf] at hrs
      have hne_c := hnonact idx hidx hne hlg
      dsimp only [s']
      rw [(hoth_eq _ hrs.1 hne_c).2.2]
      exact hw.reason_lit_mem idx hidx hne hlg },
    hrefs, hgarb_c, hsz_c, hnxt⟩

/-- `FullSparseInvW` wrapper for `inPlaceShrink_hnonact_preserves_fullWitness`. -/
theorem fullSparseInvW_of_inPlaceShrink_hnonact {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {cref nsz : Nat} (href : cref ∈ fullArenaClauseRefs s)
    (hnonact : NonActiveReason s.core cref) (hng : fullArenaClauseGarb s cref = false)
    (hnsz3 : 3 ≤ nsz) (hnsz_lt : nsz < fullArenaClauseSize s cref)
    {arena' : List (BitVec 32)} {ni' nr' : BitVec 64} (hal' : arena'.length = c.arena_cap)
    (hout : ∀ k, (k < cref ∨ cref + 3 + fullArenaClauseSize s cref ≤ k) →
      arena'[k]? = s.core.arena[k]?)
    (hnhdr_garb : (arena'[cref]?.getD 0#32 &&& 0x00080000#32) = 0#32)
    (hnhdr_shrk : (arena'[cref]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32)
    (hnsz_eq : (arena'[cref + 2]?.getD 0#32).toNat = nsz)
    (hpad_old : M6ShrkPad arena' s.core.arena cref (fullArenaClauseSize s cref) nsz)
    (hlits_lt : ∀ j < nsz, (arena'[cref + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hnd_cref : ((fullArenaClauseLitsCore { s.core with arena := arena' } cref).map (· / 2)).Nodup)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore { s.core with arena := arena' } cref))) :
    let s' : FullState :=
      { s with core := { s.core with arena := arena', num_irred := ni', num_redundant := nr' } }
    FullSparseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    fullArenaClauseGarb s' cref = false ∧ fullArenaClauseSize s' cref = nsz := by
  intro s'
  have hw := hsp.2.1; have hcl := hsp.1.core_ok
  obtain ⟨hlen', hw', hrefs', hgb', hsz', _⟩ :=
    inPlaceShrink_hnonact_preserves_fullWitness hsp.1 hw href hnonact hng hnsz3 hnsz_lt hal'
      hsp.1.scratch_ok hout hnhdr_garb hnhdr_shrk hnsz_eq hpad_old hlits_lt hent
  have hnd' : FullArenaVarsNodup s' := fun r hr hngr => by
    rw [hrefs'] at hr
    dsimp only [fullArenaClauseRefs, fullArenaClauseGarb, fullArenaClauseLits] at hr hngr ⊢
    by_cases hrc : r = cref
    · subst r; exact hnd_cref
    · have hr_wf := hw.arena.refs_wf r hr
      have hdisj := (Nat.lt_or_gt_of_ne hrc).elim
        (fun h => Or.inl (hw.arena.disjoint hr href h))
        (fun h => Or.inr (hw.arena.disjoint href hr h))
      have hbd1 : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
        have := hr_wf.2.2.1; have := hr_wf.2.2.2.1
        have := hcl.arena_len_arr; have := hcl.arena_len_le; omega
      have hout' : ∀ p, r ≤ p → p < r + 3 + fullArenaClauseSizeCore s.core r →
          arena'[p]? = s.core.arena[p]? := fun p _ _ => by
        dsimp only [fullArenaClauseSize] at hout
        exact hdisj.elim
          (fun h1 => hout p (Or.inl (by omega)))
          (fun h2 => hout p (Or.inr (by omega)))
      have hszr : fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := by
        unfold fullArenaClauseSizeCore; dsimp only [s']; rw [hout' (r + 2) (by omega) (by omega)]
      have hgbr : fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']
        rw [hout' r (by omega) (by omega)]
      have hlitsr := fullArenaClauseLitsCore_eq_of_hold hbd1
        (by rw [hal', ← hcl.arena_len_arr]; exact hbd1)
        hszr fun j hj => hout' (r + 3 + j) (by omega) (by omega)
      rw [hgbr] at hngr; rw [hlitsr]; exact hsp.2.2.2.1 r hr hngr
  have hext' : FullExtScratchOk c s' :=
    ⟨fun i hi => by dsimp only [s']; rw [hrefs']; exact hsp.2.2.2.2.1.1 i hi, hsp.2.2.2.2.1.2⟩
  exact ⟨⟨hlen', hw', hsp.2.2.1, hnd', hext', hsp.2.2.2.2.2⟩, hrefs', hgb', hsz'⟩

/-- Clause garbage marking (`PH_GARB`) at ANY `cur_level` under `NonActiveReason`, preserving
`FullSparseInvW` and `fullArenaClauseRefs`. -/
theorem markGarb_hnonact_preserves_fullSparseW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (hnonact : NonActiveReason s.core cref)
    (ag' ni' nr' vc' : BitVec 64) :
    let s' : FullState :=
      { s with
        core := { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag', num_irred := ni', num_redundant := nr' }
        scratch := { s.scratch with viv_cnt := vc' } }
    FullSparseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro s'
  have hw := hsp.2.1; have hcl := hsp.1.core_ok
  have hmg := hw.arena.markGarb hcl href ag'
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core := hmg.1
  have hdisj_lits : ∀ {r : Nat}, r ∈ fullArenaClauseRefsCore s.core → r ≠ cref →
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun {r} hr hne => by
    have hdisj : r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∨ cref + 3 ≤ r := by
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl (hw.arena.disjoint hr href hlt)
      · exact Or.inr (by have := hw.arena.disjoint href hr hgt; omega)
    have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
      have := (hw.arena.refs_wf r hr).2.2.1; have := (hw.arena.refs_wf r hr).2.2.2.1
      have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
    exact (fullArenaClauseLitsCore_set_outside hbd hdisj).2
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with arena_len_arr := by simp [s', hcl.arena_len_arr] }, { hsp.1.scratch_ok with }⟩
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := { hmg.2 with len_ok := hmg.2.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hrefs ▸ hr)
      reason_inv := fun idx hidx hne => by
        have hrs := hw.reason_inv idx hidx hne
        dsimp only [s'] at hrs ⊢
        by_cases hbin : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
        · rw [ite_eq_left hbin] at hrs ⊢; exact hrs
        · have hlg' : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
              0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32 :=
            Classical.byContradiction fun hn => hbin hn
          rw [ite_eq_right hbin] at hrs ⊢
          let r := (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat
          have hne_c := hnonact idx hidx hne hlg'
          have hgb : fullArenaClauseGarbCore s'.core r = false := by
            unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']
            rw [List.getElem?_set_ne hne_c.symm]; exact hrs.2.1
          have hl := hdisj_lits hrs.1 hne_c
          exact ⟨hrefs ▸ hrs.1, hgb, fun q hq => hrs.2.2 q (hl ▸ hq)⟩
      reason_lit_mem := fun idx hidx hne hlg => by
        have hrs := hw.reason_inv idx hidx hne
        have hbf : ¬ (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
        rw [ite_eq_right hbf] at hrs
        dsimp only [s']
        exact hdisj_lits hrs.1 (hnonact idx hidx hne hlg) ▸ hw.reason_lit_mem idx hidx hne hlg }
  have hrefs' : fullArenaClauseRefs s' = fullArenaClauseRefs s := hrefs
  have hnd' : FullArenaVarsNodup s' := fun r hr hngr => by
    rw [hrefs'] at hr
    by_cases hrc : r = cref
    · subst r
      exfalso
      have hgb : fullArenaClauseGarb s' cref = true := by
        unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']
        have hlt : cref < s.core.arena.length := by
          have := (hw.arena.refs_wf cref href).1; have := hcl.arena_len_le
          have := hcl.arena_len_arr; omega
        rw [List.getElem?_set_self hlt, Option.getD_some, BitVec.and_or_distrib_right,
          show (0x00080000#32 &&& 0x00080000#32) = 0x00080000#32 from rfl]
        have hne : (fullArenaHdr s cref &&& 0x00080000#32) ||| 0x00080000#32 ≠ 0#32 := by
          intro hz
          have := congrArg (· &&& 0x00080000#32) hz
          rw [BitVec.and_or_distrib_right,
            show (0x00080000#32 &&& 0x00080000#32) = 0x00080000#32 from rfl,
            BitVec.zero_and] at this
          have hbit := congrArg (fun x : BitVec 32 => x[19]) this
          simp at hbit
        simp [hne]
      rw [hgb] at hngr; cases hngr
    · have hgb0 : fullArenaClauseGarb s r = false := by
        unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hngr ⊢
        dsimp only [s'] at hngr; rwa [List.getElem?_set_ne (Ne.symm hrc)] at hngr
      rw [show fullArenaClauseLits s' r = fullArenaClauseLits s r from hdisj_lits hr hrc]
      exact hsp.2.2.2.1 r hr hgb0
  have hext' : FullExtScratchOk c s' :=
    ⟨fun i hi => (hsp.2.2.2.2.1.1 i hi).imp id (fun h => hrefs' ▸ h), hsp.2.2.2.2.1.2⟩
  exact ⟨⟨hlen', hw', hsp.2.2.1, hnd', hext', hsp.2.2.2.2.2⟩, hrefs'⟩

end ArenaCoreLemmas

/-! ## 3. Resolution, Watch-Slice Partition, & Backbone Trail Lemmas -/

section SemanticHelpers

/-- 1-step resolution soundness for vivification instantiation strengthening:
if `F ⊨ out`, `F ⊨ rest ++ [lit]`, and every literal in `out` is either `lit ^^^ 1` or in `rest`,
then `F ⊨ rest`. -/
theorem inst_resolve_entails {F : CNF Nat} {out rest : List Nat} {lit : Nat}
    (hout : F.EntailsClause (cnfClause out))
    (hfull : F.EntailsClause (cnfClause (rest ++ [lit])))
    (hsub : ∀ x ∈ out, x = lit ^^^ 1 ∨ x ∈ rest) :
    F.EntailsClause (cnfClause rest) := by
  rw [CNF.entails_clause_def] at hout hfull ⊢
  intro α hα
  obtain ⟨x, hx_mem, hx_sat⟩ := (clause_sat_cnfClause_iff α _).mp (hout α hα)
  rcases hsub x hx_mem with hx_eq | hx_rest
  · obtain ⟨y, hy_mem, hy_sat⟩ := (clause_sat_cnfClause_iff α _).mp (hfull α hα)
    rw [List.mem_append, List.mem_singleton] at hy_mem
    rcases hy_mem with hy_rest | hy_eq
    · exact (clause_sat_cnfClause_iff α _).mpr ⟨y, hy_rest, hy_sat⟩
    · exfalso
      rw [hx_eq] at hx_sat; rw [hy_eq] at hy_sat
      have hx_neg : (cnfClause [lit ^^^ 1]).Sat α := (sat_cnfClause_singleton α _).mpr hx_sat
      have hy_pos : (cnfClause [lit]).Sat α := (sat_cnfClause_singleton α _).mpr hy_sat
      exact ((sat_cnfClause_litNeg_iff α lit).mp hx_neg) hy_pos
  · exact (clause_sat_cnfClause_iff α _).mpr ⟨x, hx_rest, hx_sat⟩

/-- 2-literal resolution for multi-level backbone 1UIP:
resolving `[x ^^^ 1, y ^^^ 1]` with `[x, p ^^^ 1]` gives `[p ^^^ 1, y ^^^ 1]`. -/
theorem backbone_resolve2 {F : CNF Nat} {x y p : Nat}
    (h1 : F.EntailsClause (cnfClause [x ^^^ 1, y ^^^ 1]))
    (h2 : F.EntailsClause (cnfClause [x, p ^^^ 1])) :
    F.EntailsClause (cnfClause [p ^^^ 1, y ^^^ 1]) := by
  rw [CNF.entails_clause_def] at h1 h2 ⊢
  intro α hα
  obtain ⟨l1, hm1, hs1⟩ := (clause_sat_cnfClause_iff α _).mp (h1 α hα)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm1
  rcases hm1 with hl1 | hl1
  · obtain ⟨l2, hm2, hs2⟩ := (clause_sat_cnfClause_iff α _).mp (h2 α hα)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with hl2 | hl2
    · exfalso
      rw [hl1] at hs1; rw [hl2] at hs2
      exact ((sat_cnfClause_litNeg_iff α x).mp ((sat_cnfClause_singleton α _).mpr hs1))
        ((sat_cnfClause_singleton α _).mpr hs2)
    · rw [hl2] at hs2; exact (clause_sat_cnfClause_iff α _).mpr ⟨p ^^^ 1, by simp, hs2⟩
  · rw [hl1] at hs1; exact (clause_sat_cnfClause_iff α _).mpr ⟨y ^^^ 1, by simp, hs1⟩

/-- Duplicate-literal collapse `[a, a] -> [a]`. -/
theorem backbone_collapse_eq {F : CNF Nat} {a : Nat}
    (h : F.EntailsClause (cnfClause [a, a])) : F.EntailsClause (cnfClause [a]) := by
  rw [CNF.entails_clause_def] at h ⊢; intro α hα
  obtain ⟨l, hm, hs⟩ := (clause_sat_cnfClause_iff α _).mp (h α hα)
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hm
  exact (clause_sat_cnfClause_iff α _).mpr ⟨l, by simp [hm], hs⟩

/-- Level-0 unit resolution `[c0, c1]` with `[c1 ^^^ 1]` gives `[c0]`. -/
theorem backbone_resolve_l0 {F : CNF Nat} {c0 c1 : Nat}
    (h1 : F.EntailsClause (cnfClause [c0, c1]))
    (h2 : F.EntailsClause (cnfClause [c1 ^^^ 1])) :
    F.EntailsClause (cnfClause [c0]) := by
  rw [CNF.entails_clause_def] at h1 h2 ⊢; intro α hα
  obtain ⟨l, hm, hs⟩ := (clause_sat_cnfClause_iff α _).mp (h1 α hα)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with hl | hl
  · rw [hl] at hs; exact (clause_sat_cnfClause_iff α _).mpr ⟨c0, by simp, hs⟩
  · exfalso
    rw [hl] at hs
    exact ((sat_cnfClause_litNeg_iff α c1).mp (h2 α hα)) ((sat_cnfClause_singleton α _).mpr hs)

/-- Concatenation of adjacent valid `WatchSliceOk` slices. -/
theorem watchSliceOk_append {F_cur : List (List Nat)} {k : FullCoreState} {lit p n1 n2 : Nat}
    (h1 : WatchSliceOk F_cur k lit p n1) (h2 : WatchSliceOk F_cur k lit (p + n1) n2) :
    WatchSliceOk F_cur k lit p (n1 + n2) := by
  induction h1 with
  | empty => simpa using h2
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    have h2' : WatchSliceOk F_cur k lit (p + 1 + rem) n2 := by
      simpa [Nat.add_assoc, Nat.add_comm 1 rem] using h2
    simpa [Nat.add_assoc, Nat.add_comm 1 n2] using
      WatchSliceOk.bin hp hflag hne hlt hent (ih h2')
  | @large p rem w0 cref hp hp1 hflag hlt href _ ih =>
    have h2' : WatchSliceOk F_cur k lit (p + 2 + rem) n2 := by
      simpa [Nat.add_assoc, Nat.add_comm 2 rem] using h2
    simpa [Nat.add_assoc, Nat.add_comm 2 n2] using
      WatchSliceOk.large hp hp1 hflag hlt href (ih h2')

/-- Appending a single valid binary watch word onto the end of a `WatchSliceOk` slice. -/
theorem watchSliceOk_snoc_bin {F_cur : List (List Nat)} {k : FullCoreState} {lit p n : Nat}
    {w0 : BitVec 32} (h1 : WatchSliceOk F_cur k lit p n)
    (hp : k.wstk[p + n]? = some w0) (hflag : (w0 &&& 0x80000000#32) ≠ 0#32)
    (hne : w0 ≠ 0xFFFFFFFF#32) (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    WatchSliceOk F_cur k lit p (n + 1) :=
  watchSliceOk_append h1 (WatchSliceOk.bin hp hflag hne hlt hent .empty)

/-- Large-watch pair buffer invariant in `scr[0 ..< ln)` for `full_prioritize_binaries_m6`. -/
@[expose] def LargeWatchBufOk (k : FullCoreState) (scr : List (BitVec 32)) (ln : Nat) : Prop :=
  ln % 2 = 0 ∧
  ∀ i, 2 * i + 1 < ln →
    ∃ w0 cr, scr[2 * i]? = some w0 ∧ scr[2 * i + 1]? = some cr ∧
      (w0 &&& 0x80000000#32) = 0#32 ∧ cr.toNat < 0x80000000 ∧
      cr.toNat ∈ fullArenaClauseRefsCore k

/-- Copying a valid `LargeWatchBufOk` buffer into `k.wstk[q ..< q + ln)` yields `WatchSliceOk`. -/
theorem largeWatchBuf_to_slice {F_cur : List (List Nat)} {k : FullCoreState} {lit q ln : Nat}
    {scr : List (BitVec 32)} (hbuf : LargeWatchBufOk k scr ln)
    (hcopy : ∀ j < ln, k.wstk[q + j]? = scr[j]?) :
    WatchSliceOk F_cur k lit q ln := by
  suffices h : ∀ m q0 off, off + 2 * m = ln →
      (∀ j < 2 * m, k.wstk[q0 + j]? = scr[off + j]?) →
      (∀ i, off ≤ 2 * i → 2 * i + 1 < ln →
        ∃ w0 cr, scr[2 * i]? = some w0 ∧ scr[2 * i + 1]? = some cr ∧
          (w0 &&& 0x80000000#32) = 0#32 ∧ cr.toNat < 0x80000000 ∧
          cr.toNat ∈ fullArenaClauseRefsCore k) →
      off % 2 = 0 →
      WatchSliceOk F_cur k lit q0 (2 * m) by
    have hln : ln = 2 * (ln / 2) := by have := hbuf.1; omega
    rw [hln]
    exact h (ln / 2) q 0 (by omega) (fun j hj => by simpa using hcopy j (by omega))
      (fun i _ hi => hbuf.2 i hi) rfl
  intro m; induction m with
  | zero => intro _ _ _ _ _ _; exact .empty
  | succ m ih =>
    intro q0 off hoff hcp hall heven
    have hi : 2 * (off / 2) = off := by omega
    obtain ⟨w0, cr, hw0, hcr, hfl, hlt, href⟩ := hall (off / 2) (by omega) (by omega)
    rw [hi] at hw0 hcr
    have hq0 : k.wstk[q0]? = some w0 := by
      have := hcp 0 (by omega); simpa [hw0] using this
    have hq1 : k.wstk[q0 + 1]? = some cr := by
      have := hcp 1 (by omega); simpa [hcr] using this
    have htail := ih (q0 + 2) (off + 2) (by omega)
      (fun j hj => by
        have := hcp (j + 2) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm 2 j] using this)
      (fun i hi1 hi2 => hall i (by omega) hi2) (by omega)
    simpa [Nat.mul_succ] using WatchSliceOk.large hq0 hq1 hfl hlt href htail

/-- Restoring `FullWitnessInv` once `BackboneTrailInv` unwinds to `saved0` (`cur_level = 0`). -/
theorem BackboneTrailInv.to_fullWitnessInv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 : Nat} (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hbt : BackboneTrailInv c F0 F_cur s0 st saved0)
    (hte : st.core.trail_end = saved0) (hcl0 : st.core.cur_level = 0) :
    FullWitnessInv c F0 F_cur st.core := by
  have hsc := hbt.same_core; have hs0l0 := hbt.s0_l0
  have hcv : st.core.cur_vars = s0.core.cur_vars := by rw [hsc]
  have hte0 : st.core.trail_end = s0.core.trail_end := hte.trans hbt.saved0_eq
  have hvals_eq : ∀ l < 2 * s0.core.cur_vars,
      st.core.vals[l]?.getD 0#8 = s0.core.vals[l]?.getD 0#8 := by
    intro l hl
    rcases hw0.vals_domain l hl with h0 | h1 | hff
    · by_cases hcur : st.core.vals[l]?.getD 0#8 = 0#8
      · exact hcur.trans h0.symm
      · exfalso
        rcases hbt.vals_dom l hl with hz | hp | hn
        · exact hcur hz
        · obtain ⟨i, hi, heq⟩ := hbt.vals_true_trl l hl hp
          rw [hte] at hi; rw [hbt.trl_prefix i hi] at heq
          have := (hw0.vals_true_iff l hl).mpr ⟨i, hbt.saved0_eq ▸ hi, heq⟩
          rw [h0] at this; cases this
        · obtain ⟨i, hi, heq⟩ := hbt.vals_false_trl l hl hn
          rw [hte] at hi; rw [hbt.trl_prefix i hi] at heq
          have := (hw0.vals_false_iff l hl).mpr ⟨i, hbt.saved0_eq ▸ hi, heq⟩
          rw [h0] at this; cases this
    · exact hbt.vals_prefix l hl (by rw [h1]; decide)
    · exact hbt.vals_prefix l hl (by rw [hff]; decide)
  have htrl_eq : ∀ i < st.core.trail_end, st.core.trl[i]? = s0.core.trl[i]? :=
    fun i hi => hbt.trl_prefix i (hte ▸ hi)
  have hlvl_eq : ∀ i < st.core.trail_end,
      let v := (st.core.trl[i]?.getD 0#32).toNat / 2
      st.core.lvl[v]? = s0.core.lvl[v]? ∧ st.core.rsns[v]? = s0.core.rsns[v]? := by
    intro i hi; rw [htrl_eq i hi]; exact hbt.lvl_prefix i (hte ▸ hi)
  have harena_eq : st.core.arena = s0.core.arena ∧ st.core.arena_len = s0.core.arena_len :=
    ⟨by rw [hsc], by rw [hsc]⟩
  have hwat_eq : st.core.wvec = s0.core.wvec ∧ st.core.wstk = s0.core.wstk ∧
      st.core.wlen = s0.core.wlen ∧ st.core.dense_mode = s0.core.dense_mode :=
    ⟨by rw [hsc], by rw [hsc], by rw [hsc], by rw [hsc]⟩
  refine
    { ext_sound := hcv ▸ hw0.ext_sound
      inconsistent_sound := by rw [show st.core.inconsistent = s0.core.inconsistent by rw [hsc]]
                               exact hw0.inconsistent_sound
      arena := by
        have har := hw0.arena
        exact
          ⟨by rw [harena_eq.2]; exact har.len_ok,
           fun r hr => by
             rw [fullArenaClauseRefsCore, harena_eq.1, harena_eq.2] at hr
             simpa [fullArenaClauseSizeCore, fullArenaNextOff, harena_eq.1, harena_eq.2] using
               har.refs_wf r hr,
           fun r hr hsh => by
             rw [fullArenaClauseRefsCore, harena_eq.1, harena_eq.2] at hr
             simpa [fullArenaClauseSizeCore, fullArenaHdrCore, harena_eq.1, harena_eq.2] using
               har.shrk_term r hr (by simpa [fullArenaHdrCore, harena_eq.1] using hsh),
           fun r hr hng l hl => by
             rw [fullArenaClauseRefsCore, harena_eq.1, harena_eq.2] at hr
             rw [hcv]
             exact har.lits_lt r hr
               (by simpa [fullArenaClauseGarbCore, fullArenaHdrCore, harena_eq.1] using hng) l
               (by simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, harena_eq.1] using hl),
           fun r hr hng => by
             rw [fullArenaClauseRefsCore, harena_eq.1, harena_eq.2] at hr
             simpa [fullArenaClauseLitsCore, fullArenaClauseSizeCore, harena_eq.1] using
               har.entails r hr (by simpa [fullArenaClauseGarbCore, fullArenaHdrCore,
               harena_eq.1] using hng)⟩
      watches := hw0.watches.with_wstk hwat_eq.2.2.2 hcv hwat_eq.1 hwat_eq.2.1 hwat_eq.2.2.1
        (fun r hr => by simpa [fullArenaClauseRefsCore, harena_eq.1, harena_eq.2] using hr)
      cur_level_le := by omega
      trail_lits_lt := fun i hi => by rw [hcv]; exact hbt.trl_lits_lt i hi
      trail_vars_nodup := hbt.trl_vars_nodup
      vals_domain := fun l hl => hbt.vals_dom l (hcv ▸ hl)
      vals_true_iff := fun l hl => by
        rw [hvals_eq l (hcv ▸ hl), hw0.vals_true_iff l (hcv ▸ hl)]
        constructor
        · rintro ⟨i, hi, heq⟩; exact ⟨i, hte0 ▸ hi, by rw [htrl_eq i (hte0 ▸ hi), heq]⟩
        · rintro ⟨i, hi, heq⟩; rw [htrl_eq i hi] at heq; exact ⟨i, hte0 ▸ hi, heq⟩
      vals_false_iff := fun l hl => by
        rw [hvals_eq l (hcv ▸ hl), hw0.vals_false_iff l (hcv ▸ hl)]
        constructor
        · rintro ⟨i, hi, heq⟩; exact ⟨i, hte0 ▸ hi, by rw [htrl_eq i (hte0 ▸ hi), heq]⟩
        · rintro ⟨i, hi, heq⟩; rw [htrl_eq i hi] at heq; exact ⟨i, hte0 ▸ hi, heq⟩
      lvl_le := fun i hi => by
        rw [(hlvl_eq i hi).1, htrl_eq i hi, hcl0]
        have := hw0.lvl_le i (hte0 ▸ hi); rw [hs0l0] at this; exact this
      dec_earliest := fun i j hi hj _ hdec => by
        have hlv := hw0.lvl_le j (hte0 ▸ hj)
        rw [hs0l0] at hlv
        rw [(hlvl_eq j hj).1, htrl_eq j hj] at hdec; omega
      levels_inhabited := fun L h1 hle => by omega
      level0_sound := fun i hi _ => by
        rw [htrl_eq i hi]
        exact hw0.level0_sound i (hte0 ▸ hi)
          (by have := hw0.lvl_le i (hte0 ▸ hi); rw [hs0l0] at this; omega)
      trail_pos_inv := fun i hi => by
        rw [show st.core.trail_pos = s0.core.trail_pos by rw [hsc], htrl_eq i hi]
        exact hw0.trail_pos_inv i (hte0 ▸ hi)
      level0_rsn_none := fun idx hidx _ => by
        rw [(hlvl_eq idx hidx).2, htrl_eq idx hidx]
        exact hw0.level0_rsn_none idx (hte0 ▸ hidx)
          (by have := hw0.lvl_le idx (hte0 ▸ hidx); rw [hs0l0] at this; omega)
      frame_trail_lt := fun L hL => by
        obtain rfl : L = 0 := by omega
        rw [show st.core.frame_trail = s0.core.frame_trail by rw [hsc], hte0]
        exact hw0.frame_trail_lt 0 (Nat.zero_le _)
      frame_trail_mono := fun L1 L2 h12 h2 => by
        obtain rfl : L2 = 0 := by omega
        obtain rfl : L1 = 0 := by omega
        exact Nat.le_refl _
      frame_trail_before_lt := fun L h1 h2 => by omega
      frame_dec_lt := fun L h1 h2 => by omega
      reason_inv := fun idx hidx hne => by
        have hr0 := hw0.level0_rsn_none idx (hte0 ▸ hidx)
          (by have := hw0.lvl_le idx (hte0 ▸ hidx); rw [hs0l0] at this; omega)
        rw [(hlvl_eq idx hidx).2, htrl_eq idx hidx] at hne; exact absurd hr0 hne
      reason_lit_mem := fun idx hidx hne _ => by
        have hr0 := hw0.level0_rsn_none idx (hte0 ▸ hidx)
          (by have := hw0.lvl_le idx (hte0 ▸ hidx); rw [hs0l0] at this; omega)
        rw [(hlvl_eq idx hidx).2, htrl_eq idx hidx] at hne; exact absurd hr0 hne }

end SemanticHelpers

/-! ## 4. `FullSparseInvW` Field-Update Helpers -/

section SparseUpdates

theorem fullSparseInvW_with_tarjan_reach {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) {tr' : List (BitVec 32)}
    (htr : tr'.length = 2 * c.max_vars) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with tarjan_reach := tr' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with tarjan_reach_len := htr }⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem fullSparseInvW_with_red_refs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) {rr' : List (BitVec 32)}
    (hrr : rr'.length = c.red_cap) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with red_refs := rr' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with red_refs_len := hrr }⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem fullSparseInvW_with_flags {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) {fl' : List (BitVec 32)}
    (hfl : fl'.length = c.max_vars) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with flags := fl' } } :=
  ⟨⟨{ h.1.core_ok with flags_len := hfl }, h.1.scratch_ok⟩,
    { h.2.1 with
      arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
      watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem fullSparseInvW_with_work_stk1 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) {ws1' : List (BitVec 32)}
    (hws : ws1'.length = 2 * c.max_vars) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with work_stk1 := ws1' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with work_stk1_len := hws }⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem fullSparseInvW_with_work_stk2 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) {ws2' : List (BitVec 32)}
    (hws : ws2'.length = 2 * c.max_vars) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with work_stk2 := ws2' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with work_stk2_len := hws }⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem fullSparseInvW_with_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) {tmp' : List (BitVec 32)}
    (htmp : tmp'.length = c.max_vars) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with tmp := tmp' } } :=
  ⟨⟨{ h.1.core_ok with tmp_len_arr := htmp }, h.1.scratch_ok⟩,
    { h.2.1 with
      arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
      watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem fullSparseInvW_with_ant_res {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) (a' r' : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with ant_sz := a', res_sz := r' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with }⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem fullSparseInvW_with_probing {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) (p' : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with probing := p' } } :=
  ⟨⟨{ h.1.core_ok with }, h.1.scratch_ok⟩,
    { h.2.1 with
      arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
      watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem fullSparseInvW_with_delayed_len {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) (dl' : Nat) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with delayed_len := dl' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with }⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem fullSparseInvW_with_confl_clear {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) (ct' cr' : BitVec 64) :
    FullSparseInvW c F0 F_cur
      { s with core := { s.core with confl_type := ct', confl_ref := cr' } } :=
  ⟨⟨{ h.1.core_ok with }, h.1.scratch_ok⟩,
    { h.2.1 with
      arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
      watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem fullSparseInvW_to_sparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) : FullSparseInv c F0 s :=
  ⟨⟨h.1, F_cur, h.2.1⟩, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

end SparseUpdates

/-! ## 5. `full_add_bin_m6` `Func.wp` Proof (Canonical `Full.fullAddBinSpec`) -/

section AddBinM6Proof

open FullBinLuckySpecs
open scoped FullArenaTactics FullBinLuckyTactics

private theorem addBin_adapt_alvl (Γ : Env)
    (h : ∀ a m Q X, Full.fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X) :
    EnvSpec Γ "full_assign_lvl" FullBinLuckySpecs.fullAssignLvlSpec :=
  fun a m Q X hs => h a m Q X hs

private theorem addBin_adapt_wpush (Γ : Env)
    (h : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    EnvSpec Γ "full_watch_push" FullBinLuckySpecs.fullWatchPushSpec :=
  fun a m Q X hs => h a m Q X hs

/-- `full_add_bin_m6` satisfies `fullAddBinM6Spec` (preserves `red_refs`, `tarjan_reach`, and all
other scratch arrays outside `phases`/`wsort`, setting `FL_TRANS | FL_BONE0 | FL_BONE1` on both
endpoints). -/
theorem full_add_bin_m6_ext_wp (Γ : Env)
    (hhas : ∀ a m Q X, Full.fullHasBinSpec a m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] a m Q X)
    (halvl : ∀ a m Q X, Full.fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hwpush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ args m Q X, fullAddBinM6Spec args m Q X →
      Func.wp Γ full_add_bin_m6_body args m Q X := by
  have halvl' := addBin_adapt_alvl Γ halvl
  have hwpush' := addBin_adapt_wpush Γ hwpush
  rintro ⟨h, a, b, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hcl0, hent, hm, hQ⟩
  have hcl := hlen.core_ok
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hcl.cur_vars_le; have hvl := hcl.vals_len; have hfll0 := hcl.flags_len
  have hret0 : Q (0#64, ()) m :=
    hQ 0#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
      s.core.trail_end s.core.unassigned s.core.unflushed s.core.wvec s.core.wstk s.core.wlen
      s.core.wusable s.core.num_binary s.core.oom s.core.inconsistent s.scratch.phases
      s.scratch.wsort m hlen hw (Or.inl rfl) (fun h2 => by cases h2) (fun h2 => by cases h2) hm
  unfold Func.wp full_add_bin_m6_body
  fbl_group
  · exact hret0
  · exact hret0
  · exact hret0
  · exact hret0
  · exact hret0
  · have ha_lt : a.toNat < 2 * s.core.cur_vars := by c0_bound
    have hb_lt : b.toNat < 2 * s.core.cur_vars := by c0_bound
    have hne_neg : a ≠ b ^^^ 1#32 := by c0_bound
    have hent_ab := hent ha_lt hb_lt
    have hdom_a := hw.vals_domain a.toNat ha_lt
    have hdom_b := hw.vals_domain b.toNat hb_lt
    refine wp_join_group
      (fun () mJ => mJ = m ∧
        ¬ (s.core.vals[a.toNat]?.getD 0#8 = 0xFF#8 ∧
           s.core.vals[b.toNat]?.getD 0#8 = 0xFF#8) ∧
        s.core.vals[a.toNat]?.getD 0#8 ≠ 1#8 ∧
        s.core.vals[b.toNat]?.getD 0#8 ≠ 1#8)
      ?_ (fun J hJ => by
        have ha_pos : s.core.vals[a.toNat]?.getD 0#8 ≠ 1#8 := by
          have h0 : BitVec.slt 0#32
              (BitVec.signExtend 32 (s.core.vals[a.toNat]'(by omega))) = false := by assumption
          intro heq; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
          rw [heq] at h0; revert h0; decide
        have hb_pos : s.core.vals[b.toNat]?.getD 0#8 ≠ 1#8 := by
          have h0 : BitVec.slt 0#32
              (BitVec.signExtend 32 (s.core.vals[b.toNat]'(by omega))) = false := by assumption
          intro heq; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
          rw [heq] at h0; revert h0; decide
        fbl_group
        · have hva_neg : s.core.vals[a.toNat]?.getD 0#8 = 0xFF#8 := by
            have hlt : BitVec.slt (BitVec.signExtend 32
                (s.core.vals[a.toNat]'(by omega))) 0#32 = true := by assumption
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdom_a ⊢
            rcases hdom_a with h | h | h <;> rw [h] at hlt
            · exact absurd hlt (by decide)
            · exact absurd hlt (by decide)
            · exact h
          have hvb_neg : s.core.vals[b.toNat]?.getD 0#8 = 0xFF#8 := by
            have hlt : BitVec.slt (BitVec.signExtend 32
                (s.core.vals[b.toNat]'(by omega))) 0#32 = true := by assumption
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdom_b ⊢
            rcases hdom_b with h | h | h <;> rw [h] at hlt
            · exact absurd hlt (by decide)
            · exact absurd hlt (by decide)
            · exact h
          have hFcur_unsat : (cnfOfClauses F_cur).Unsat := by
            refine unsat_of_entails_nil (entails_of_mem_or_false hent_ab fun l hl => Or.inr ?_)
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
            rcases hl with rfl | rfl
            · obtain ⟨ia, hia, haeq⟩ := (hw.vals_false_iff _ ha_lt).mp hva_neg
              have hs := hw.level0_sound ia hia (by have := hw.lvl_le ia hia; omega)
              rwa [haeq] at hs
            · obtain ⟨ib, hib, hbeq⟩ := (hw.vals_false_iff _ hb_lt).mp hvb_neg
              have hs := hw.level0_sound ib hib (by have := hw.lvl_le ib hib; omega)
              rwa [hbeq] at hs
          have hlen_inc : ({ s with core := { s.core with inconsistent := 1#64 } } :
              FullState).LengthsOk c := ⟨{ hcl with }, hlen.scratch_ok⟩
          have hw' : FullWitnessInv c F0 F_cur { s.core with inconsistent := 1#64 } :=
            { hw with
              inconsistent_sound := fun _ => hFcur_unsat
              arena := { hw.arena with len_ok := hw.arena.len_ok }
              watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
          exact hQ 20#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl
            s.core.trail_pos s.core.trail_end s.core.unassigned s.core.unflushed s.core.wvec
            s.core.wstk s.core.wlen s.core.wusable s.core.num_binary s.core.oom 1#64
            s.scratch.phases s.scratch.wsort _ hlen_inc hw'
            (Or.inr (Or.inr (Or.inr rfl))) (fun _ => ⟨hw.ext_sound.2 hFcur_unsat, by decide⟩)
            (fun h2 => by cases h2) (by assumption)
        · have hnb : s.core.vals[b.toNat]?.getD 0#8 ≠ 0xFF#8 := by
            have h0 : BitVec.slt (BitVec.signExtend 32
                (s.core.vals[b.toNat]'(by omega))) 0#32 = false := by assumption
            intro heq; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
            rw [heq] at h0; revert h0; decide
          exact hJ () _ ⟨rfl, fun ⟨_, hb⟩ => hnb hb, ha_pos, hb_pos⟩
        · have hna : s.core.vals[a.toNat]?.getD 0#8 ≠ 0xFF#8 := by
            have h0 : BitVec.slt (BitVec.signExtend 32
                (s.core.vals[a.toNat]'(by omega))) 0#32 = false := by assumption
            intro heq; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
            rw [heq] at h0; revert h0; decide
          exact hJ () _ ⟨rfl, fun ⟨ha, _⟩ => hna ha, ha_pos, hb_pos⟩)
    rintro _ _ mJ ⟨rfl, hnot_both, ha_pos, hb_pos⟩
    have hassign_lit : ∀ (lit : BitVec 32), lit.toNat < 2 * s.core.cur_vars →
        s.core.vals[lit.toNat]?.getD 0#8 = 0#8 →
        (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]) →
        wp Γ Q X (Expr.call (as := [i64, i32, i32, i32]) (bs := []) "full_assign_lvl"
          (Arg.var c.hdr, Arg.var lit, Arg.imm (4294967295#32 : Val i32),
            Arg.imm (0#32 : Val i32), ())
          fun _ => Expr.ret (Arg.imm (1#64 : Val i64), ())) mJ := by
      intro lit hlit hun hunit
      c0_call halvl'
      refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
      have hte_lt : s.core.trail_end < c.max_vars := by
        have := hw.trail_end_lt_of_unassigned hlit hun; omega
      have hnot_cond : ¬ (s.core.cur_vars ≤ lit.toNat / 2 ∨
          c.max_vars ≤ s.core.trail_end ∨ s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
        intro h; rcases h with h1 | h2 | h3 <;> first | omega | exact h3 hun
      rw [ite_eq_right hnot_cond]; dsimp only
      intro flags' unassigned' phases' m' hfll hphl hm'
      obtain ⟨hlen', hw'⟩ :=
        fbl_assignLevel0_preserves_fullWitness hlen hw hcl0 hfll hphl hlit hun hunit
      fbl_group
      exact hQ 1#64 _ flags' _ _ _ _ _ unassigned' _ s.core.wvec s.core.wstk s.core.wlen
        s.core.wusable s.core.num_binary s.core.oom s.core.inconsistent phases' s.scratch.wsort
        m' hlen' hw' (Or.inr (Or.inl rfl)) (fun h2 => by cases h2) (fun h2 => by cases h2) hm'
    fbl_group
    refine wp_join_group (fun _ mK => mK = mJ ∧
      (s.core.vals[a.toNat]?.getD 0#8 = 0xFF#8 ∨ a = b))
      ?_ (fun J hJ => by
        fbl_group
        · have hva_neg : s.core.vals[a.toNat]?.getD 0#8 = 0xFF#8 := by
            have hlt : BitVec.slt (BitVec.signExtend 32
                (s.core.vals[a.toNat]'(by omega))) 0#32 = true := by assumption
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdom_a ⊢
            rcases hdom_a with h | h | h <;> rw [h] at hlt
            · exact absurd hlt (by decide)
            · exact absurd hlt (by decide)
            · exact h
          exact hJ () _ ⟨rfl, Or.inl hva_neg⟩
        · exact hJ () _ ⟨rfl, Or.inr (by assumption)⟩
        · have hna_neg : s.core.vals[a.toNat]?.getD 0#8 ≠ 0xFF#8 := by
            have h0 : BitVec.slt (BitVec.signExtend 32
                (s.core.vals[a.toNat]'(by omega))) 0#32 = false := by assumption
            intro heq; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
            rw [heq] at h0; revert h0; decide
          have hva0 : s.core.vals[a.toNat]?.getD 0#8 = 0#8 := by
            rcases hdom_a with h | h | h <;> first | exact h | contradiction
          have hvb_neg : s.core.vals[b.toNat]?.getD 0#8 = 0xFF#8 := by
            have hlt : BitVec.slt (BitVec.signExtend 32
                (s.core.vals[b.toNat]'(by omega))) 0#32 = true := by assumption
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdom_b ⊢
            rcases hdom_b with h | h | h <;> rw [h] at hlt
            · exact absurd hlt (by decide)
            · exact absurd hlt (by decide)
            · exact h
          have hunit_a : (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat]) := by
            refine entails_of_mem_or_false hent_ab fun l hl => ?_
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
            rcases hl with rfl | rfl
            · exact Or.inl (by simp)
            · obtain ⟨ib, hib, hbeq⟩ := (hw.vals_false_iff _ hb_lt).mp hvb_neg
              have hs := hw.level0_sound ib hib (by have := hw.lvl_le ib hib; omega)
              right; rwa [hbeq] at hs
          exact hassign_lit a ha_lt hva0 hunit_a
        · have hna_neg : s.core.vals[a.toNat]?.getD 0#8 ≠ 0xFF#8 := by
            have h0 : BitVec.slt (BitVec.signExtend 32
                (s.core.vals[a.toNat]'(by omega))) 0#32 = false := by assumption
            intro heq; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
            rw [heq] at h0; revert h0; decide
          have hva0 : s.core.vals[a.toNat]?.getD 0#8 = 0#8 := by
            rcases hdom_a with h | h | h <;> first | exact h | contradiction
          c0_call hhas
          refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm, ?_⟩
          intro r _
          fbl_group
          · exact hret0
          · have hwpc := fbl_bv32_mask_bin b (by omega)
            have hwpc1 := fbl_bv32_mask_bin a (by omega)
            refine wp_join_group
              (fun _ mO => ∃ wvecO wstkO wlenO wuO wsortO,
                let sO : FullState :=
                  { s with
                    core := { s.core with wvec := wvecO, wstk := wstkO,
                                          wlen := wlenO, wusable := wuO }
                    scratch := { s.scratch with wsort := wsortO } }
                sO.LengthsOk c ∧ ModeWatchesInv F_cur sO.core ∧ (FullMem c sO ⋆ R) mO)
              ?_ (fun J hJ => by
                c0_call hwpush'
                refine ⟨c, s, R, rfl, hlen, hw.watches.layout, fun _ => hwpc.1,
                  fun h2 => absurd h2 (by decide), hm, ?_⟩
                dsimp only
                intro ok1 wvec1 wstk1 wlen1 wu1 wsort1 m1 hlen1 hlay1 hother1 hok1t hok1f hm1
                let s1 : FullState :=
                  { s with
                    core := { s.core with wvec := wvec1, wstk := wstk1,
                                          wlen := wlen1, wusable := wu1 }
                    scratch := { s.scratch with wsort := wsort1 } }
                fbl_group
                · obtain ⟨_, _, hsz1, hpref1, hw0_1, _⟩ := hok1t (by assumption)
                  have hok1 : ok1 = true := by assumption
                  have hw1_ok : ModeWatchesInv F_cur s1.core :=
                    fbl_watchPush_bin_preserves_modeWatches (ok := ok1) hw.watches hlay1 rfl rfl
                      (fun _ r => r) ⟨hwpc.2.1, hwpc.1, hwpc.2.2 ▸ hb_lt, hwpc.2.2 ▸ hent_ab⟩
                      hother1 (fun _ => ⟨ha_lt, hsz1, hpref1, hw0_1⟩)
                      (fun hf => by rw [hok1] at hf; cases hf)
                  c0_call hwpush'
                  refine ⟨c, s1, R, rfl, hlen1, hlay1, fun _ => hwpc1.1,
                    fun h2 => absurd h2 (by decide), hm1, ?_⟩
                  dsimp only
                  intro ok2 wvec2 wstk2 wlen2 wu2 wsort2 m2 hlen2 hlay2 hother2 hok2t hok2f hm2
                  let s2 : FullState :=
                    { s1 with
                      core := { s1.core with wvec := wvec2, wstk := wstk2, wlen := wlen2,
                                             wusable := wu2 }
                      scratch := { s.scratch with wsort := wsort2 } }
                  have hva_lt : (BitVec.setWidth 64 (a >>> (1 : Nat))).toNat <
                      s2.core.flags.length := by
                    dsimp only [s2, s1]; rw [hfll0]; c0_bound
                  have hvb_lt : (BitVec.setWidth 64 (b >>> (1 : Nat))).toNat <
                      s2.core.flags.length := by
                    dsimp only [s2, s1]; rw [hfll0]; c0_bound
                  fbl_group
                  · obtain ⟨_, _, hsz2, hpref2, hw0_2, _⟩ := hok2t (by assumption)
                    have hok2 : ok2 = true := by assumption
                    have hw2_ok : ModeWatchesInv F_cur s2.core :=
                      fbl_watchPush_bin_preserves_modeWatches (ok := ok2) hw1_ok hlay2 rfl rfl
                        (fun _ r => r) ⟨hwpc1.2.1, hwpc1.1, hwpc1.2.2 ▸ ha_lt,
                          hwpc1.2.2 ▸ fbl_entailsClause_swap2 hent_ab⟩
                        hother2 (fun _ => ⟨hb_lt, hsz2, hpref2, hw0_2⟩)
                        (fun hf => by rw [hok2] at hf; cases hf)
                    have hfl2_len : ∀ fl', fl'.length = c.max_vars →
                        ({ s2 with core := { s2.core with
                          flags := fl', num_binary := s.core.num_binary + 1#64 } } :
                          FullState).LengthsOk c ∧
                        FullWitnessInv c F0 F_cur
                          { s2.core with
                            flags := fl', num_binary := s.core.num_binary + 1#64 } := by
                      intro fl' hfl'
                      exact ⟨⟨{ hlen2.core_ok with flags_len := hfl' }, hlen2.scratch_ok⟩,
                        { hw with
                          arena := { hw.arena with len_ok := hw.arena.len_ok }
                          watches := hw2_ok.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }⟩
                    refine hQ 1#64 s.core.vals _ s.core.lvl s.core.rsns s.core.trl
                      s.core.trail_pos s.core.trail_end s.core.unassigned s.core.unflushed
                      wvec2 wstk2 wlen2 wu2 (s.core.num_binary + 1#64) s.core.oom
                      s.core.inconsistent s.scratch.phases wsort2 _ ?_ ?_
                      (Or.inr (Or.inl rfl)) (fun h2 => by cases h2) (fun h2 => by cases h2)
                      (by assumption)
                    · exact (hfl2_len _ (by simp [s1, hfll0])).1
                    · exact (hfl2_len _ (by simp [s1, hfll0])).2
                  · have hw2_fail : ModeWatchesInv F_cur s2.core := by
                      refine fbl_watchPush_fail_preserves_modeWatches hw1_ok hlay2 rfl rfl
                        (fun _ r => r) ?_
                      intro l hl
                      by_cases hle : l = b.toNat
                      · subst hle; exact (hok2f (by assumption)).1 hb_lt
                      · exact hother2 l hl hle
                    exact hJ () m2 ⟨wvec2, wstk2, wlen2, wu2, wsort2, hlen2, hw2_fail, hm2⟩
                · have hw1_fail : ModeWatchesInv F_cur s1.core := by
                    refine fbl_watchPush_fail_preserves_modeWatches hw.watches hlay1 rfl rfl
                      (fun _ r => r) ?_
                    intro l hl
                    by_cases hle : l = a.toNat
                    · subst hle; exact (hok1f (by assumption)).1 ha_lt
                    · exact hother1 l hl hle
                  exact hJ () m1 ⟨wvec1, wstk1, wlen1, wu1, wsort1, hlen1, hw1_fail, hm1⟩)
            rintro _ _ mO ⟨wvecO, wstkO, wlenO, wuO, wsortO, hlenO, hwO, hmO⟩
            have hlenO' : ({ s with
                core := { s.core with wvec := wvecO, wstk := wstkO, wlen := wlenO,
                                      wusable := wuO, oom := 1#64 }
                scratch := { s.scratch with wsort := wsortO } } :
                FullState).LengthsOk c := ⟨{ hlenO.core_ok with }, hlenO.scratch_ok⟩
            have hwO' : FullWitnessInv c F0 F_cur
                { s.core with wvec := wvecO, wstk := wstkO, wlen := wlenO,
                              wusable := wuO, oom := 1#64 } :=
              { hw with
                arena := { hw.arena with len_ok := hw.arena.len_ok }
                watches := hwO.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
            fbl_group
            exact hQ 2#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl
              s.core.trail_pos s.core.trail_end s.core.unassigned s.core.unflushed
              wvecO wstkO wlenO wuO s.core.num_binary 1#64 s.core.inconsistent
              s.scratch.phases wsortO _ hlenO' hwO'
              (Or.inr (Or.inr (Or.inl rfl))) (fun h2 => by cases h2)
              (fun _ => by decide) (by assumption))
    rintro _ _ mK ⟨rfl, hcond⟩
    have hvb0 : s.core.vals[b.toNat]?.getD 0#8 = 0#8 := by
      have hnb : s.core.vals[b.toNat]?.getD 0#8 ≠ 0xFF#8 := by
        rcases hcond with hva_neg | rfl
        · exact fun hb => hnot_both ⟨hva_neg, hb⟩
        · exact fun hb => hnot_both ⟨hb, hb⟩
      rcases hdom_b with h | h | h <;> first | exact h | contradiction
    have hunit_b : (cnfOfClauses F_cur).EntailsClause (cnfClause [b.toNat]) := by
      rcases hcond with hva_neg | rfl
      · refine entails_of_mem_or_false hent_ab fun l hl => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · obtain ⟨ia, hia, haeq⟩ := (hw.vals_false_iff _ ha_lt).mp hva_neg
          have hs := hw.level0_sound ia hia (by have := hw.lvl_le ia hia; omega)
          right; rwa [haeq] at hs
        · exact Or.inl (by simp)
      · exact backbone_collapse_eq hent_ab
    exact hassign_lit b hb_lt hvb0 hunit_b

/-- Canonical `Full.fullAddBinSpec` corollary for `full_add_bin_m6`. -/
theorem full_add_bin_m6_wp (Γ : Env)
    (hhas : ∀ a m Q X, Full.fullHasBinSpec a m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] a m Q X)
    (halvl : ∀ a m Q X, Full.fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hwpush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ args m Q X, Full.fullAddBinSpec args m Q X →
      Func.wp Γ full_add_bin_m6_body args m Q X :=
  full_add_bin_m6_ext_wp Γ hhas halvl hwpush

end AddBinM6Proof

/-! ## 6. `full_init_fresh_var_m6` `Func.wp` Proof (BVA Heap + Canonical Spec) -/

section InitFreshVarM6Proof

open scoped FullArenaTactics FullBvaHeap.FullBvaHeapTactics

private theorem initFreshVarM6_post {c : FullCfg} {s s' : FullState} {fv : BitVec 32}
    {R : Mem 64 → Prop} {Q : Post []} {m' : Mem 64}
    (hfv_lt : fv.toNat < s.core.cur_vars) (hclen : s.core.LengthsOk c) (hlen' : s'.LengthsOk c)
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hcore : s'.core =
      { s.core with
        wvec := (((s.core.wvec.set (4 * fv.toNat) 0#32).set (4 * fv.toNat + 1) 0#32).set
          (4 * fv.toNat + 2) 0#32).set (4 * fv.toNat + 3) 0#32
        vals := (s.core.vals.set (2 * fv.toNat) 0#8).set (2 * fv.toNat + 1) 0#8
        mrk := s.core.mrk.set fv.toNat 0#8, lvl := s.core.lvl.set fv.toNat 0#32
        rsns := s.core.rsns.set fv.toNat 0xFFFFFFFF#32, flags := s.core.flags.set fv.toNat 2041#32
        unassigned := s.core.unassigned + 1#64 })
    (hext_pres : FullExtScratchPres s s')
    (hsb : s'.scratch.scratch_buf = s.scratch.scratch_buf)
    (hws : s'.scratch.wsort = s.scratch.wsort)
    (htm : s'.scratch.tarjan_mark = s.scratch.tarjan_mark)
    (htr : s'.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (hss : s'.scratch.sim_sig = s.scratch.sim_sig)
    (hm' : (FullMem c s' ⋆ R) m')
    (hQ : ∀ vals' mrk' flags' lvl' rsns' wvec' unass' sc' m',
      let s1 : FullState :=
        { s with
          core := { s.core with vals := vals', mrk := mrk', flags := flags', lvl := lvl',
                                rsns := rsns', wvec := wvec', unassigned := unass' }
          scratch := sc' }
      s1.LengthsOk c → FullExtScratchPres s s1 →
      sc'.scratch_buf = s.scratch.scratch_buf → sc'.wsort = s.scratch.wsort →
      sc'.tarjan_mark = s.scratch.tarjan_mark → sc'.tarjan_reach = s.scratch.tarjan_reach →
      sc'.sim_sig = s.scratch.sim_sig →
      vals'[2 * fv.toNat]?.getD 1#8 = 0#8 → vals'[2 * fv.toNat + 1]?.getD 1#8 = 0#8 →
      (∀ l < 2 * c.max_vars, l / 2 ≠ fv.toNat → vals'[l]? = s.core.vals[l]?) →
      mrk'[fv.toNat]?.getD 1#8 = 0#8 →
      (∀ v < c.max_vars, v ≠ fv.toNat → mrk'[v]? = s.core.mrk[v]?) →
      lvl'[fv.toNat]?.getD 1#32 = 0#32 →
      (∀ v < c.max_vars, v ≠ fv.toNat → lvl'[v]? = s.core.lvl[v]?) →
      rsns'[fv.toNat]?.getD 0#32 = 0xFFFFFFFF#32 →
      (∀ v < c.max_vars, v ≠ fv.toNat → rsns'[v]? = s.core.rsns[v]?) →
      (∀ k < 4, wvec'[4 * fv.toNat + k]?.getD 1#32 = 0#32) →
      (∀ i < 4 * c.max_vars, i / 4 ≠ fv.toNat → wvec'[i]? = s.core.wvec[i]?) →
      (FullMem c s1 ⋆ R) m' → Q () m') : Q () m' := by
  have hs'_eq : s' = { s with core := s'.core, scratch := s'.scratch } := by cases s'; rfl
  let vals' := (s.core.vals.set (2 * fv.toNat) 0#8).set (2 * fv.toNat + 1) 0#8
  let mrk' := s.core.mrk.set fv.toNat 0#8
  let flags' := s.core.flags.set fv.toNat 2041#32
  let lvl' := s.core.lvl.set fv.toNat 0#32
  let rsns' := s.core.rsns.set fv.toNat 0xFFFFFFFF#32
  let wvec' := (((s.core.wvec.set (4 * fv.toNat) 0#32).set (4 * fv.toNat + 1) 0#32).set
    (4 * fv.toNat + 2) 0#32).set (4 * fv.toNat + 3) 0#32
  let unass' := s.core.unassigned + 1#64
  refine hQ vals' mrk' flags' lvl' rsns' wvec' unass' s'.scratch m'
    (by rw [← hcore, ← hs'_eq]; exact hlen')
    hext_pres hsb hws htm htr hss ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (by rw [← hcore, ← hs'_eq]; exact hm')
  · dsimp only [vals']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by rw [hclen.vals_len]; omega)]
    rfl
  · dsimp only [vals']
    rw [List.getElem?_set_self (by simp [hclen.vals_len]; omega)]; rfl
  · intro l _ _; dsimp only [vals']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  · dsimp only [mrk']; rw [List.getElem?_set_self (by rw [hclen.mrk_len]; omega)]; rfl
  · intro v _ hv; exact List.getElem?_set_ne (Ne.symm hv)
  · dsimp only [lvl']; rw [List.getElem?_set_self (by rw [hclen.lvl_len]; omega)]; rfl
  · intro v _ hv; exact List.getElem?_set_ne (Ne.symm hv)
  · dsimp only [rsns']; rw [List.getElem?_set_self (by rw [hclen.rsns_len]; omega)]; rfl
  · intro v _ hv; exact List.getElem?_set_ne (Ne.symm hv)
  · intro k hk; dsimp only [wvec']
    rcases k with _ | _ | _ | _ | k
    · rw [show 4 * fv.toNat + 0 = 4 * fv.toNat from rfl, List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by simp [hclen.wvec_len]; omega)]; rfl
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by simp [hclen.wvec_len]; omega)]; rfl
    · rw [List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by simp [hclen.wvec_len]; omega)]; rfl
    · rw [List.getElem?_set_self (by simp [hclen.wvec_len]; omega)]; rfl
    · omega
  · intro i _ hi; dsimp only [wvec']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]

/-- `full_init_fresh_var_m6` satisfies `FullBvaHeap.fullInitFreshVarHeapSpec`. -/
theorem full_init_fresh_var_m6_heap_wp (Γ : Env) :
    ∀ args m Q X, FullBvaHeap.fullInitFreshVarHeapSpec args m Q X →
      Func.wp Γ full_init_fresh_var_m6_body args m Q X := by
  rintro ⟨h, fv, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hslen, hfv_lt, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hclen := hslen.core_ok; have hsc := hslen.scratch_ok; have hcv_le := hclen.cur_vars_le
  have hwv_len := hclen.wvec_len; have hvals_len := hclen.vals_len; have hmrk_len := hclen.mrk_len
  have hlvl_len := hclen.lvl_len; have hrsns_len := hclen.rsns_len; have hfl_len := hclen.flags_len
  have hpos_len := hsc.pos_len; have hph_len := hsc.phases_len; have hqp_len := hsc.q_prev_len
  have hqn_len := hsc.q_next_len; have hqs_len := hsc.q_stamp_len; have hsc_len := hsc.score_len
  have hfv64 : (BitVec.setWidth 64 fv).toNat = fv.toNat := by c0_bound
  have hwb0 : (BitVec.setWidth 64 fv <<< (2 : Nat)).toNat = 4 * fv.toNat := by c0_bound
  have hwb1 : ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 1).toNat = 4 * fv.toNat + 1 := by
    change ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 1#64).toNat = _; c0_bound
  have hwb2 : ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 2).toNat = 4 * fv.toNat + 2 := by
    change ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 2#64).toNat = _; c0_bound
  have hwb3 : ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 3).toNat = 4 * fv.toNat + 3 := by
    change ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 3#64).toNat = _; c0_bound
  have hv2 : (BitVec.setWidth 64 fv <<< (1 : Nat)).toNat = 2 * fv.toNat := by c0_bound
  have hv2p1 : ((BitVec.setWidth 64 fv <<< (1 : Nat)) ||| 1).toNat = 2 * fv.toNat + 1 := by
    change ((BitVec.setWidth 64 fv <<< (1 : Nat)) ||| 1#64).toNat = _
    rw [FullBvaFwdTactics.bv64_or1_of_even (by rw [hv2]; omega), hv2]
  have hv2p1_lt : ((BitVec.setWidth 64 fv <<< (1 : Nat)) ||| 1).toNat < s.core.vals.length := by
    rw [hv2p1, hvals_len]; omega
  have hfl_or :
      ((((((((1 : BitVec 32) ||| 8) ||| 16) ||| 1024) ||| 32) ||| 64) ||| 512) ||| 128) ||| 256 =
      2041#32 := by decide
  unfold Func.wp full_init_fresh_var_m6_body; dsimp only
  open scoped FullBvaFwdTactics in bf_fast_nogrp
  refine wp_join_state0 (α := FullState)
    (fun sm mm =>
      (FullMem c sm ⋆ R) mm ∧ sm.LengthsOk c ∧
      sm.core =
        { s.core with
          wvec := (((s.core.wvec.set (4 * fv.toNat) 0#32).set (4 * fv.toNat + 1) 0#32).set
            (4 * fv.toNat + 2) 0#32).set (4 * fv.toNat + 3) 0#32
          vals := (s.core.vals.set (2 * fv.toNat) 0#8).set (2 * fv.toNat + 1) 0#8
          mrk := s.core.mrk.set fv.toNat 0#8, lvl := s.core.lvl.set fv.toNat 0#32
          rsns := s.core.rsns.set fv.toNat 0xFFFFFFFF#32
          flags := s.core.flags.set fv.toNat 2041#32 } ∧
      FullExtScratchPres s sm ∧ sm.scratch.scratch_buf = s.scratch.scratch_buf ∧
      sm.scratch.wsort = s.scratch.wsort ∧ sm.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
      sm.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
      sm.scratch.sim_sig = s.scratch.sim_sig)
    (fun _ sm mm ⟨hmm, hlenm, hcorem, hextm, hsbm, hwsm, htmm, htrm, hssm⟩ => ?_)
    (fun Jm hJm => ?_)
  · clear hm
    have hqsm_len := hlenm.scratch_ok.q_stamp_len
    open scoped FullBvaFwdTactics in bf_fast
    refine initFreshVarM6_post hfv_lt hclen ?_ hcv_le ?_ ?_ ?_ ?_ ?_ ?_ ?_ hm hQ
    · exact ⟨{ hlenm.core_ok with }, { hlenm.scratch_ok with q_stamp_len := by simp [hqsm_len] }⟩
    · dsimp only; rw [hcorem]; rfl
    · exact ⟨hextm.1, hextm.2⟩
    · exact hsbm
    · exact hwsm
    · exact htmm
    · exact htrm
    · exact hssm
  · open scoped FullBvaFwdTactics in bf_fast
    all_goals
      refine hJm _ _ ⟨hm, ?_, ?_, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩
      · exact ⟨
          { hclen with
            wvec_len := by simp [hwv_len], vals_len := by simp [hvals_len],
            mrk_len := by simp [hmrk_len], lvl_len := by simp [hlvl_len],
            rsns_len := by simp [hrsns_len], flags_len := by simp [hfl_len] },
          { hsc with
            phases_len := by simp [hph_len], pos_len := by simp [hpos_len],
            score_len := by simp [hsc_len], q_prev_len := by simp [hqp_len],
            q_next_len := by simp [hqn_len] }⟩
      · dsimp only; rw [hfv64, hwb0, hwb1, hwb2, hwb3, hv2, hv2p1, hfl_or]; rfl

/-- Canonical `Full.fullInitFreshVarSpec` corollary for `full_init_fresh_var_m6`. -/
theorem full_init_fresh_var_m6_wp (Γ : Env) :
    ∀ args m Q X, Full.fullInitFreshVarSpec args m Q X →
      Func.wp Γ full_init_fresh_var_m6_body args m Q X := by
  rintro ⟨h, fv, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hslen, hfv_lt, hm, hQ⟩
  exact full_init_fresh_var_m6_heap_wp Γ _ m Q X ⟨c, s, R, rfl, hslen, hfv_lt, hm,
    fun vals' mrk' flags' lvl' rsns' wvec' unass' sc' m' hlen' hext' hsb _ _ _ _
      hv0 hv1 hv_oth hm0 hm_oth hl0 hl_oth hr0 hr_oth hw0 hw_oth hm' =>
      hQ vals' mrk' flags' lvl' rsns' wvec' unass' sc' m' hlen' hext' hsb
        hv0 hv1 hv_oth hm0 hm_oth hl0 hl_oth hr0 hr_oth hw0 hw_oth hm'⟩

end InitFreshVarM6Proof

/-! ## 7. `full_prioritize_binaries_m6` `Func.wp` Proof -/

section PrioritizeBinariesProof

open FullVivTopTactics
open scoped FullArenaTactics FullVivTopTactics

private theorem prio_replace_slice_sparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) {l : Nat}
    (hl : l < 2 * s.core.cur_vars) {wstk' scr' : List (BitVec 32)}
    (hwl : wstk'.length = c.wcap) (hscl : scr'.length = c.scratch_cap)
    (hout : ∀ idx, (idx < fullWatchOff s l ∨ fullWatchOff s l + fullWatchSize s l ≤ idx) →
      wstk'[idx]? = s.core.wstk[idx]?)
    (hslice : WatchSliceOk F_cur { s.core with wstk := wstk' } l
      (fullWatchOff s l) (fullWatchSize s l)) :
    let s' : FullState :=
      { s with core := { s.core with wstk := wstk' }
               scratch := { s.scratch with scratch_buf := scr' } }
    FullSparseInvW c F0 F_cur s' := by
  intro s'
  have hw := hsp.2.1; have hdm := hsp.2.2.2.2.2
  have hmw := hw.watches; unfold ModeWatchesInv at hmw; rw [ite_eq_left hdm] at hmw
  have hlay := hmw.layout
  have hwat' : ModeWatchesInv F_cur s'.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices hlay.bounds hlay.pos_off hlay.disjoint fun l2 hl2 => ?_
    by_cases heq : l2 = l
    · subst heq; exact hslice
    · refine (hmw.slices l2 hl2).mono (k := s.core) (k' := s'.core)
        (by rw [CNF.entails_def]; exact fun _ h => h)
        (Nat.le_refl _) (fun _ hr => hr) fun idx hi1 hi2 => ?_
      dsimp only [s']; unfold fullWatchOff fullWatchSize at hout
      have hoff2 : fullWatchOffCore s'.core l2 = fullWatchOffCore s.core l2 := rfl
      have hsz2 : fullWatchSizeCore s'.core l2 = fullWatchSizeCore s.core l2 := rfl
      rw [hoff2] at hi1 hi2; rw [hsz2] at hi2
      by_cases hsz0 : fullWatchSizeCore s.core l = 0
      · exact hout idx (by omega)
      · have hpos2 : 0 < fullWatchSizeCore s.core l2 := by omega
        have hdisj := hlay.disjoint l l2 hl hl2 (Ne.symm heq) (by omega) hpos2
        rcases hdisj with h1 | h2
        · exact hout idx (Or.inr (by omega))
        · exact hout idx (Or.inl (by omega))
  exact ⟨⟨{ hsp.1.core_ok with wstk_len_arr := hwl },
          { hsp.1.scratch_ok with scratch_buf_len := hscl }⟩,
    { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hwat' },
    hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hdm⟩

private theorem prio_largeBuf_snoc {k : FullCoreState} {scr : List (BitVec 32)} {ln : Nat}
    {w0 cr : BitVec 32} (hbuf : LargeWatchBufOk k scr ln) (hln_lt : ln + 1 < scr.length)
    (hfl : (w0 &&& 0x80000000#32) = 0#32) (hlt : cr.toNat < 0x80000000)
    (href : cr.toNat ∈ fullArenaClauseRefsCore k) :
    LargeWatchBufOk k ((scr.set ln w0).set (ln + 1) cr) (ln + 2) := by
  refine ⟨by have := hbuf.1; omega, fun i hi => ?_⟩
  by_cases hie : 2 * i = ln
  · refine ⟨w0, cr, ?_, ?_, hfl, hlt, href⟩
    · rw [hie, List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
    · rw [hie, List.getElem?_set_self (by simp; omega)]
  · have hlt2 : 2 * i + 1 < ln := by have := hbuf.1; omega
    obtain ⟨w', cr', hw', hcr', hfl', hlt', href'⟩ := hbuf.2 i hlt2
    refine ⟨w', cr', ?_, ?_, hfl', hlt', href'⟩
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hw'
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hcr'

private theorem prio_copy_loop_wp (Γ : Env) {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {wstk_l wstk_p scr_p : List (BitVec 32)} {R : Mem 64 → Prop}
    {Q : Post [.bool]} {X : XPost} {J : Cont [.bool]}
    {all_p : Val .bool} {l_v q_v ln_v : Val i64} {mp : Mem 64}
    (hsp_l : FullSparseInvW c F0 F_cur
      { s0 with core := { s0.core with wstk := wstk_l }
                scratch := { s0.scratch with scratch_buf := scr_p } })
    (hl_lt : l_v.toNat < 2 * s0.core.cur_vars)
    (hq_ge : fullWatchOff s0 l_v.toNat ≤ q_v.toNat)
    (hq_ln : q_v.toNat + ln_v.toNat = fullWatchOff s0 l_v.toNat + fullWatchSize s0 l_v.toNat)
    (hend_le : fullWatchOff s0 l_v.toNat + fullWatchSize s0 l_v.toNat ≤ c.wcap)
    (hwpl : wstk_p.length = c.wcap) (hspl : scr_p.length = c.scratch_cap)
    (hln_le : ln_v.toNat ≤ c.scratch_cap)
    (hout_p : ∀ idx,
      (idx < fullWatchOff s0 l_v.toNat ∨
        fullWatchOff s0 l_v.toNat + fullWatchSize s0 l_v.toNat ≤ idx) →
      wstk_p[idx]? = wstk_l[idx]?)
    (hbin_p : WatchSliceOk F_cur { s0.core with wstk := wstk_p } l_v.toNat
      (fullWatchOff s0 l_v.toNat) (q_v.toNat - fullWatchOff s0 l_v.toNat))
    (hbuf_p : LargeWatchBufOk s0.core scr_p ln_v.toNat)
    (hm_p : (FullMem c { s0 with
      core := { s0.core with wstk := wstk_p }
      scratch := { s0.scratch with scratch_buf := scr_p } } ⋆ R) mp)
    (hJ : ∀ wstk_k mk,
      FullSparseInvW c F0 F_cur
        { s0 with core := { s0.core with wstk := wstk_k }
                  scratch := { s0.scratch with scratch_buf := scr_p } } →
      (FullMem c
        { s0 with core := { s0.core with wstk := wstk_k }
                  scratch := { s0.scratch with scratch_buf := scr_p } } ⋆ R) mk →
      J (all_p, ()) mk) :
    wp Γ Q X
      (Expr.group (sig := [[i64]])
        (fun Js => Blocks.cons (fun p =>
          Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
                      args := (Arg.var p.fst, Arg.var ln_v, ()) } fun p_1 =>
          Expr.jnz (Arg.var p_1.fst)
            (Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var q_v, Arg.var p.fst, ()) } fun p_2 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                         args := (Arg.var p_2.fst, Arg.imm 4, ()) } fun p_3 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var c.pWstk, Arg.var p_3.fst, ()) } fun p_4 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                         args := (Arg.var p.fst, Arg.imm 4, ()) } fun p_5 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var c.pScratchBuf, Arg.var p_5.fst, ()) } fun p_6 =>
             Expr.load i32 (Arg.var p_6.fst) fun ld =>
             Expr.store (Arg.var ld) (Arg.var p_4.fst)
               (Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                            args := (Arg.var p.fst, Arg.imm 1, ()) } fun p =>
                Expr.jump Js.fst (Arg.var p.fst, ())))
            (Expr.jump J (Arg.var all_p, ()))) Blocks.nil)
        (fun Js => Expr.jump Js.fst (Arg.imm 0, ()))) mp := by
  have hwc := c.hwcap; have hsc := c.hscr; unfold dimacsBound at hwc hsc
  let off_n := fullWatchOff s0 l_v.toNat
  let sz_n := fullWatchSize s0 l_v.toNat
  refine wp_loop_inv (ts := [i64])
    (fun (k_v, ()) mk =>
      k_v.toNat ≤ ln_v.toNat ∧
      ∃ wstk_k, wstk_k.length = c.wcap ∧
        (∀ idx, (idx < off_n ∨ off_n + sz_n ≤ idx) → wstk_k[idx]? = wstk_l[idx]?) ∧
        (∀ idx, off_n ≤ idx → idx < q_v.toNat → wstk_k[idx]? = wstk_p[idx]?) ∧
        (∀ j < k_v.toNat, wstk_k[q_v.toNat + j]? = scr_p[j]?) ∧
        (FullMem c { s0 with
          core := { s0.core with wstk := wstk_k }
          scratch := { s0.scratch with scratch_buf := scr_p } } ⋆ R) mk)
    (fun (k_v, _) _ => ln_v.toNat - k_v.toNat) ?_ ?_
  · intro Jk hJk; fvt_steps
    exact hJk (0#64, ()) mp ⟨Nat.zero_le _, wstk_p, hwpl, hout_p,
      fun _ _ _ => rfl, fun _ hj => by simp at hj, hm_p⟩
  · rintro Jk ⟨k_v, ⟨⟩⟩ mk ⟨hk_le, wstk_k, hwkl, hout_k, hpref_k, hcp_k, hm_k⟩ ihk
    fvt_step; fvt_step
    · have hk_lt : k_v.toNat < ln_v.toNat := by c0_bound
      have hk1_eq : (k_v + 1#64).toNat = k_v.toNat + 1 := by bv_omega
      have hqk_eq : (q_v + k_v).toNat = q_v.toNat + k_v.toNat := by bv_omega
      fvt_steps
      let wstk_n := wstk_k.set (q_v.toNat + k_v.toNat) (scr_p[k_v.toNat]'(by omega))
      refine ihk (k_v + 1#64, ()) _ (by dsimp only; omega)
        ⟨by omega, wstk_n, by simp [wstk_n, hwkl],
          fun idx hidx => by
            dsimp only [wstk_n]
            rw [List.getElem?_set_ne (by rcases hidx with h1 | h2 <;> omega)]
            exact hout_k idx hidx,
          fun idx hi1 hi2 => by
            dsimp only [wstk_n]
            rw [List.getElem?_set_ne (by omega)]; exact hpref_k idx hi1 hi2,
          fun j hj => by
            dsimp only [wstk_n]; rw [hk1_eq] at hj
            by_cases hje : j = k_v.toNat
            · subst hje
              rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
            · rw [List.getElem?_set_ne (by omega)]; exact hcp_k j (by omega),
          by simpa only [wstk_n, hqk_eq] using hm⟩
    · have hk_eq : k_v.toNat = ln_v.toNat := by
        have hge : ln_v.toNat ≤ k_v.toNat := by c0_bound
        omega
      have hbin_k : WatchSliceOk F_cur { s0.core with wstk := wstk_k } l_v.toNat
          off_n (q_v.toNat - off_n) :=
        hbin_p.mono (k := { s0.core with wstk := wstk_p }) (k' := { s0.core with wstk := wstk_k })
          (by rw [CNF.entails_def]; exact fun _ h => h)
          (Nat.le_refl _) (fun _ hr => hr) fun idx hi1 hi2 => hpref_k idx hi1 (by omega)
      have hlg_k : WatchSliceOk F_cur { s0.core with wstk := wstk_k } l_v.toNat
          q_v.toNat ln_v.toNat :=
        largeWatchBuf_to_slice (k := { s0.core with wstk := wstk_k })
          (by simpa [LargeWatchBufOk, fullArenaClauseRefsCore] using hbuf_p)
          (fun j hj => hcp_k j (by omega))
      have hcomb : WatchSliceOk F_cur { s0.core with wstk := wstk_k } l_v.toNat off_n sz_n := by
        have hq_add : off_n + (q_v.toNat - off_n) = q_v.toNat := by omega
        have hsz_add : (q_v.toNat - off_n) + ln_v.toNat = sz_n := by omega
        rw [← hsz_add]; exact watchSliceOk_append hbin_k (by rwa [hq_add])
      have hsp_n := prio_replace_slice_sparse hsp_l hl_lt hwkl hspl hout_k hcomb
      exact hJ wstk_k mk hsp_n hm_k

private theorem prio_part_loop_wp (Γ : Env) {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {wstk_l scr_l : List (BitVec 32)} {R : Mem 64 → Prop}
    {Q : Post [.bool]} {X : XPost} {Jo : Cont [.bool]}
    {all_p : Val .bool} {l_v off_v end_v : Val i64} {ml : Mem 64}
    (hsp_l : FullSparseInvW c F0 F_cur
      { s0 with core := { s0.core with wstk := wstk_l }
                scratch := { s0.scratch with scratch_buf := scr_l } })
    (hl_lt : l_v.toNat < 2 * s0.core.cur_vars)
    (hoff_v : off_v.toNat = fullWatchOff s0 l_v.toNat)
    (hend_v : end_v.toNat = fullWatchOff s0 l_v.toNat + fullWatchSize s0 l_v.toNat)
    (hend_le : fullWatchOff s0 l_v.toNat + fullWatchSize s0 l_v.toNat ≤ c.wcap)
    (hsz_le_cap : fullWatchSize s0 l_v.toNat ≤ c.scratch_cap)
    (hslice_l : WatchSliceOk F_cur { s0.core with wstk := wstk_l } l_v.toNat
      (fullWatchOff s0 l_v.toNat) (fullWatchSize s0 l_v.toNat))
    (hm_l : (FullMem c { s0 with
      core := { s0.core with wstk := wstk_l }
      scratch := { s0.scratch with scratch_buf := scr_l } } ⋆ R) ml)
    (hJo : ∀ wstk_k scr_p mk,
      FullSparseInvW c F0 F_cur
        { s0 with core := { s0.core with wstk := wstk_k }
                  scratch := { s0.scratch with scratch_buf := scr_p } } →
      (FullMem c
        { s0 with core := { s0.core with wstk := wstk_k }
                  scratch := { s0.scratch with scratch_buf := scr_p } } ⋆ R) mk →
      Jo (all_p, ()) mk) :
    wp Γ Q X
      (Expr.group (sig := [[i64, i64, i64]])
        (fun Js => Blocks.cons (fun p =>
          Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
                      args := (Arg.var p.fst, Arg.var end_v, ()) } fun p_1 =>
          Expr.jnz (Arg.var p_1.fst)
            (Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                         args := (Arg.var p.fst, Arg.imm 4, ()) } fun p_2 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var c.pWstk, Arg.var p_2.fst, ()) } fun p_3 =>
             Expr.load i32 (Arg.var p_3.fst) fun ld =>
             Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var p.fst, Arg.imm 1, ()) } fun p_4 =>
             Expr.group (sig := [[i64, i64, i64]])
               (fun _ => Blocks.cons (fun p =>
                 Expr.jump Js.fst (Arg.var p.fst, Arg.var p.snd.fst, Arg.var p.snd.snd.fst, ()))
                 Blocks.nil) fun Js_a =>
             Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                         args := (Arg.var ld, Arg.imm 2147483648, ()) } fun p_5 =>
             Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
                         args := (Arg.var p_5.fst, Arg.imm 0, ()) } fun p_6 =>
             Expr.jnz (Arg.var p_6.fst)
               (Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                            args := (Arg.var p.snd.fst, Arg.imm 4, ()) } fun p_7 =>
                Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                            args := (Arg.var c.pWstk, Arg.var p_7.fst, ()) } fun p_8 =>
                Expr.store (Arg.var ld) (Arg.var p_8.fst)
                  (Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                               args := (Arg.var p.snd.fst, Arg.imm 1, ()) } fun p_9 =>
                   Expr.jump Js_a.fst
                     (Arg.var p_4.fst, Arg.var p_9.fst, Arg.var p.snd.snd.fst, ())))
               (Expr.group (sig := [[i64, i64]])
                  (fun _ => Blocks.cons (fun p_7 =>
                    Expr.jump Js_a.fst
                      (Arg.var p_7.fst, Arg.var p.snd.fst, Arg.var p_7.snd.fst, ()))
                    Blocks.nil) fun Js_b =>
                Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
                            args := (Arg.var p_4.fst, Arg.var end_v, ()) } fun p_7 =>
                Expr.jnz (Arg.var p_7.fst)
                  (Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                               args := (Arg.var p_4.fst, Arg.imm 4, ()) } fun p_8 =>
                   Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                               args := (Arg.var c.pWstk, Arg.var p_8.fst, ()) } fun p_9 =>
                   Expr.load i32 (Arg.var p_9.fst) fun ld_1 =>
                   Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                               args := (Arg.var p_4.fst, Arg.imm 1, ()) } fun p_10 =>
                   Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                               args := (Arg.var p.snd.snd.fst, Arg.imm 4, ()) } fun p_11 =>
                   Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                               args := (Arg.var c.pScratchBuf, Arg.var p_11.fst, ()) } fun p_12 =>
                   Expr.store (Arg.var ld) (Arg.var p_12.fst)
                     (Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                  args := (Arg.var p.snd.snd.fst, Arg.imm 1, ()) } fun p_13 =>
                      Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                  args := (Arg.var p_13.fst, Arg.imm 4, ()) } fun p_14 =>
                      Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                  args := (Arg.var c.pScratchBuf, Arg.var p_14.fst, ()) }
                        fun p_15 =>
                      Expr.store (Arg.var ld_1) (Arg.var p_15.fst)
                        (Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                     args := (Arg.var p.snd.snd.fst, Arg.imm 2, ()) } fun p_16 =>
                         Expr.jump Js_b.fst (Arg.var p_10.fst, Arg.var p_16.fst, ()))))
                  (Expr.jump Js_b.fst (Arg.var p_4.fst, Arg.var p.snd.snd.fst, ()))))
            (Expr.group (sig := [[i64]])
              (fun Js_1 => Blocks.cons (fun p_2 =>
                Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
                            args := (Arg.var p_2.fst, Arg.var p.snd.snd.fst, ()) } fun p_3 =>
                Expr.jnz (Arg.var p_3.fst)
                  (Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                               args := (Arg.var p.snd.fst, Arg.var p_2.fst, ()) } fun p_4 =>
                   Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                               args := (Arg.var p_4.fst, Arg.imm 4, ()) } fun p_5 =>
                   Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                               args := (Arg.var c.pWstk, Arg.var p_5.fst, ()) } fun p_6 =>
                   Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                               args := (Arg.var p_2.fst, Arg.imm 4, ()) } fun p_7 =>
                   Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                               args := (Arg.var c.pScratchBuf, Arg.var p_7.fst, ()) } fun p_8 =>
                   Expr.load i32 (Arg.var p_8.fst) fun ld =>
                   Expr.store (Arg.var ld) (Arg.var p_6.fst)
                     (Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                  args := (Arg.var p_2.fst, Arg.imm 1, ()) } fun p_9 =>
                      Expr.jump Js_1.fst (Arg.var p_9.fst, ())))
                  (Expr.jump Jo (Arg.var all_p, ()))) Blocks.nil)
              (fun Js_1 => Expr.jump Js_1.fst (Arg.imm 0, ())))) Blocks.nil)
        (fun Js => Expr.jump Js.fst (Arg.var off_v, Arg.var off_v, Arg.imm 0, ()))) ml := by
  have hwc := c.hwcap; have hsc := c.hscr; unfold dimacsBound at hwc hsc
  let off_n := fullWatchOff s0 l_v.toNat
  let sz_n := fullWatchSize s0 l_v.toNat
  refine wp_loop_inv (ts := [i64, i64, i64])
    (fun (p_v, q_v, ln_v, ()) mp =>
      off_n ≤ q_v.toNat ∧ q_v.toNat ≤ p_v.toNat ∧ p_v.toNat ≤ off_n + sz_n ∧
      (q_v.toNat - off_n) + ln_v.toNat = p_v.toNat - off_n ∧
      ∃ wstk_p scr_p, wstk_p.length = c.wcap ∧ scr_p.length = c.scratch_cap ∧
        (∀ idx, (idx < off_n ∨ p_v.toNat ≤ idx) → wstk_p[idx]? = wstk_l[idx]?) ∧
        WatchSliceOk F_cur { s0.core with wstk := wstk_p } l_v.toNat
          off_n (q_v.toNat - off_n) ∧
        WatchSliceOk F_cur { s0.core with wstk := wstk_p } l_v.toNat
          p_v.toNat (off_n + sz_n - p_v.toNat) ∧
        LargeWatchBufOk s0.core scr_p ln_v.toNat ∧
        (FullMem c { s0 with
          core := { s0.core with wstk := wstk_p }
          scratch := { s0.scratch with scratch_buf := scr_p } } ⋆ R) mp)
    (fun (p_v, _, _, _) _ => off_n + sz_n - p_v.toNat) ?_ ?_
  · intro Jp hJp; fvt_steps
    exact hJp (off_v, off_v, 0#64, ()) ml
      ⟨by omega, by omega, by omega, by simp [hoff_v],
        wstk_l, scr_l, hsp_l.1.core_ok.wstk_len_arr, hsp_l.1.scratch_ok.scratch_buf_len,
        fun _ _ => rfl, by rw [hoff_v, Nat.sub_self]; exact .empty,
        by rw [hoff_v, show off_n + sz_n - off_n = sz_n by omega]; exact hslice_l,
        ⟨rfl, fun _ hi => by simp at hi⟩, hm_l⟩
  · rintro Jp ⟨p_v, q_v, ln_v, ⟨⟩⟩ mp
      ⟨hq_ge, hq_le, hp_le, hsum, wstk_p, scr_p, hwpl, hspl, hout_p, hbin_p, hrem_p,
        hbuf_p, hm_p⟩ ihp
    fvt_step; fvt_step
    · have hp_lt : p_v.toNat < off_n + sz_n := by
        have hlt : p_v.toNat < end_v.toNat := by c0_bound
        omega
      have hp1_eq : (p_v + 1#64).toNat = p_v.toNat + 1 := by bv_omega
      have hq1_eq : (q_v + 1#64).toNat = q_v.toNat + 1 := by bv_omega
      have hw0_at : wstk_p[p_v.toNat]? = some (wstk_p[p_v.toNat]'(by omega)) :=
        List.getElem?_eq_getElem (by omega)
      fvt_steps
      · -- Binary watch
        have hbf : (wstk_p[p_v.toNat]'(by omega) &&& 0x80000000#32) ≠ 0#32 := by c0_bound
        generalize hrem_n_eq : off_n + sz_n - p_v.toNat = rem_n at hrem_p
        cases hrem_p with
        | empty => omega
        | @large _ _ w0' _ hw0' _ hfl' _ _ _ =>
          exfalso
          exact hbf (Option.some.inj (hw0_at.symm.trans hw0') ▸ hfl')
        | @bin _ rem1 w0' hw0' _ hne_ff hlt_ot hent_ot htail =>
          have hw0_eq : wstk_p[p_v.toNat]'(by omega) = w0' :=
            Option.some.inj (hw0_at.symm.trans hw0')
          let wstk_n := wstk_p.set q_v.toNat (wstk_p[p_v.toNat]'(by omega))
          have hbin_n : WatchSliceOk F_cur { s0.core with wstk := wstk_n } l_v.toNat
              off_n (q_v.toNat + 1 - off_n) := by
            have hpref := hbin_p.mono (k := { s0.core with wstk := wstk_p })
              (k' := { s0.core with wstk := wstk_n })
              (by rw [CNF.entails_def]; exact fun _ h => h)
              (Nat.le_refl _) (fun _ hr => hr) fun idx hi1 hi2 => by
              exact List.getElem?_set_ne (by omega)
            have hsn := watchSliceOk_snoc_bin hpref
              (by dsimp only [wstk_n]
                  rw [show off_n + (q_v.toNat - off_n) = q_v.toNat by omega,
                    List.getElem?_set_self (by omega), hw0_eq])
              (hw0_eq ▸ hbf) hne_ff hlt_ot hent_ot
            simpa [show q_v.toNat - off_n + 1 = q_v.toNat + 1 - off_n by omega] using hsn
          have hrem_n : WatchSliceOk F_cur { s0.core with wstk := wstk_n } l_v.toNat
              (p_v.toNat + 1) (off_n + sz_n - (p_v.toNat + 1)) := by
            have heq_r : rem1 = off_n + sz_n - (p_v.toNat + 1) := by omega
            rw [← heq_r]
            exact htail.mono (k := { s0.core with wstk := wstk_p })
              (k' := { s0.core with wstk := wstk_n })
              (by rw [CNF.entails_def]; exact fun _ h => h)
              (Nat.le_refl _) (fun _ hr => hr) fun idx hi1 _ => by
              exact List.getElem?_set_ne (by omega)
          refine ihp (p_v + 1#64, q_v + 1#64, ln_v, ()) _
            (by dsimp only; omega)
            ⟨by omega, by omega, by omega, by omega, wstk_n, scr_p,
              by simp [wstk_n, hwpl], hspl, fun idx hidx => ?_,
              by rw [hq1_eq]; exact hbin_n,
              by rw [hp1_eq]; exact hrem_n, hbuf_p, by assumption⟩
          dsimp only [wstk_n]
          rw [List.getElem?_set_ne (by rcases hidx with h1 | h2 <;> omega)]
          exact hout_p idx (by
            rcases hidx with h1 | h2
            · exact Or.inl (by omega)
            · exact Or.inr (by omega))
      · -- Large watch with `p + 1 < end`
        have hbf : (wstk_p[p_v.toNat]'(by omega) &&& 0x80000000#32) = 0#32 := by c0_bound
        generalize hrem_n_eq : off_n + sz_n - p_v.toNat = rem_n at hrem_p
        cases hrem_p with
        | empty => omega
        | @bin _ _ _ hw0' hfl' _ _ _ _ =>
          exfalso
          exact hfl' (Option.some.inj (hw0_at.symm.trans hw0') ▸ hbf)
        | @large _ rem2 w0' cr' hw0' hcr' _ hlt_cr href_cr htail =>
          have hp1_lt : (p_v + 1#64).toNat < off_n + sz_n := by omega
          have hp1_wstk : (p_v + 1#64).toNat < wstk_p.length := by omega
          have hp2_eq : ((p_v + 1#64) + 1#64).toNat = p_v.toNat + 2 := by bv_omega
          have hln1_eq : (ln_v + 1#64).toNat = ln_v.toNat + 1 := by bv_omega
          have hln2_eq : (ln_v + 2#64).toNat = ln_v.toNat + 2 := by bv_omega
          have hln0_scr : ln_v.toNat < scr_p.length := by omega
          have hln1_scr : (ln_v + 1#64).toNat < scr_p.length := by omega
          have hw0_eq : wstk_p[p_v.toNat]'(by omega) = w0' :=
            Option.some.inj (hw0_at.symm.trans hw0')
          have hcr_eq' : wstk_p[(p_v + 1#64).toNat]'hp1_wstk = cr' :=
            Option.some.inj (by
              rw [← List.getElem?_eq_getElem hp1_wstk, hp1_eq, hcr'])
          fvt_steps
          let scr_n := (scr_p.set ln_v.toNat (wstk_p[p_v.toNat]'(by omega))).set
            (ln_v.toNat + 1) (wstk_p[(p_v + 1#64).toNat]'hp1_wstk)
          have hbuf_n : LargeWatchBufOk s0.core scr_n (ln_v.toNat + 2) := by
            dsimp only [scr_n]; rw [hw0_eq, hcr_eq']
            exact prio_largeBuf_snoc hbuf_p (by omega) (hw0_eq ▸ hbf) hlt_cr href_cr
          have hrem_n : WatchSliceOk F_cur { s0.core with wstk := wstk_p } l_v.toNat
              (p_v.toNat + 2) (off_n + sz_n - (p_v.toNat + 2)) := by
            have heq_r : rem2 = off_n + sz_n - (p_v.toNat + 2) := by omega
            rwa [← heq_r]
          have hscr_eq :
              (scr_p.set ln_v.toNat (wstk_p[p_v.toNat]'(by omega))).set
                (ln_v + 1#64).toNat (wstk_p[(p_v + 1#64).toNat]'hp1_wstk) = scr_n := by
            dsimp only [scr_n]; rw [hln1_eq]
          have hm_n : (FullMem c { s0 with
              core := { s0.core with wstk := wstk_p }
              scratch := { s0.scratch with scratch_buf := scr_n } } ⋆ R) m := by
            rw [← hscr_eq]; exact hm
          refine ihp ((p_v + 1#64) + 1#64, q_v, ln_v + 2#64, ()) _
            (by dsimp only; omega)
            ⟨hq_ge, by omega, by omega, by omega, wstk_p, scr_n, hwpl,
              by simp [scr_n, hspl],
              fun idx hidx => hout_p idx (by
                rcases hidx with h1 | h2
                · exact Or.inl (by omega)
                · exact Or.inr (by omega)),
              hbin_p, by rw [hp2_eq]; exact hrem_n,
              by rw [hln2_eq]; exact hbuf_n, hm_n⟩
      · -- Unreachable `!bin ∧ !(p + 1 < end)` ruled out by `WatchSliceOk.large`
        exfalso
        have hbf : (wstk_p[p_v.toNat]'(by omega) &&& 0x80000000#32) = 0#32 := by c0_bound
        generalize hrem_n_eq : off_n + sz_n - p_v.toNat = rem_n at hrem_p
        cases hrem_p with
        | empty => omega
        | @bin _ _ _ hw0' hfl' _ _ _ _ =>
          exact hfl' (Option.some.inj (hw0_at.symm.trans hw0') ▸ hbf)
        | @large _ _ _ _ _ _ _ _ _ _ =>
          have hge : end_v.toNat ≤ (p_v + 1#64).toNat := by c0_bound
          omega
    · -- Exit of partition loop: `p_v = off_n + sz_n`
      have hp_eq : p_v.toNat = off_n + sz_n := by
        have hge : end_v.toNat ≤ p_v.toNat := by c0_bound
        omega
      have hsp_ls : FullSparseInvW c F0 F_cur
          { s0 with core := { s0.core with wstk := wstk_l }
                    scratch := { s0.scratch with scratch_buf := scr_p } } :=
        ⟨⟨hsp_l.1.core_ok, { hsp_l.1.scratch_ok with scratch_buf_len := hspl }⟩,
          hsp_l.2.1, hsp_l.2.2.1, hsp_l.2.2.2.1, hsp_l.2.2.2.2.1, hsp_l.2.2.2.2.2⟩
      exact prio_copy_loop_wp Γ hsp_ls hl_lt hq_ge (by omega) hend_le hwpl hspl
        (by omega) (fun idx hidx => hout_p idx (by
          rcases hidx with h1 | h2
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)))
        hbin_p hbuf_p hm_p fun wstk_k mk hsp_k hm_k => hJo wstk_k scr_p mk hsp_k hm_k

/-- `full_prioritize_binaries_m6` satisfies `fullPrioritizeBinariesM6Spec` parametrically in `Γ`. -/
theorem full_prioritize_binaries_m6_wp (Γ : Env) :
    ∀ args m Q X, fullPrioritizeBinariesM6Spec args m Q X →
      Func.wp Γ full_prioritize_binaries_m6_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s0, R, rfl, hsp0, hm0, hQ⟩
  have hcl0 := hsp0.1.core_ok
  have hmx := c.hmaxv; have hwc := c.hwcap; have hsc := c.hscr
  unfold dimacsBound at hmx hwc hsc
  have hcv_le := hcl0.cur_vars_le
  have hnlits : ((BitVec.ofNat 64 s0.core.cur_vars) <<< (1 : Nat)).toNat =
      2 * s0.core.cur_vars := by c0_bound
  unfold Func.wp full_prioritize_binaries_m6_body
  fvt_to_group
  refine wp_loop_inv (ts := [.bool, i64])
    (fun (all_p, l_v, ()) ml =>
      l_v.toNat ≤ 2 * s0.core.cur_vars ∧
      ∃ wstk' scr',
        let sl : FullState :=
          { s0 with core := { s0.core with wstk := wstk' }
                    scratch := { s0.scratch with scratch_buf := scr' } }
        FullSparseInvW c F0 F_cur sl ∧ (FullMem c sl ⋆ R) ml)
    (fun (_, l_v, _) _ => 2 * s0.core.cur_vars - l_v.toNat) ?_ ?_
  · intro J hJ; fvt_steps
    exact hJ (true, 0#64, ()) m0 ⟨Nat.zero_le _, s0.core.wstk, s0.scratch.scratch_buf, hsp0, hm0⟩
  · rintro J ⟨all_p, l_v, ⟨⟩⟩ ml ⟨hl_le, wstk_l, scr_l, hsp_l, hm_l⟩ ih
    let sl : FullState :=
      { s0 with core := { s0.core with wstk := wstk_l }
                scratch := { s0.scratch with scratch_buf := scr_l } }
    fvt_steps
    · have hl_lt : l_v.toNat < 2 * s0.core.cur_vars := by
        have : l_v.toNat < ((BitVec.ofNat 64 s0.core.cur_vars) <<< (1 : Nat)).toNat := by c0_bound
        omega
      have hl1_eq : (l_v + 1#64).toNat = l_v.toNat + 1 := by bv_omega
      have hwv_len := hcl0.wvec_len
      have hcv_le_l := hcl0.cur_vars_le
      have hl_w0 : (l_v <<< (1 : Nat)).toNat = 2 * l_v.toNat := by c0_bound
      have hl_w1 : ((l_v <<< (1 : Nat)) + 1#64).toNat = 2 * l_v.toNat + 1 := by c0_bound
      have hdm := hsp_l.2.2.2.2.2
      have hmw := hsp_l.2.1.watches; unfold ModeWatchesInv at hmw; rw [ite_eq_left hdm] at hmw
      have hbd := hmw.layout.bounds l_v.toNat hl_lt
      have hwl_le := hsp_l.1.core_ok.wlen_le
      have hoff_eq : (s0.core.wvec[(l_v <<< (1 : Nat)).toNat]'(by omega)).toNat =
          fullWatchOff s0 l_v.toNat := by
        unfold fullWatchOff fullWatchOffCore
        have h1 := List.getElem?_eq_getElem
          (by omega : (l_v <<< (1 : Nat)).toNat < s0.core.wvec.length)
        rw [← hl_w0, h1, Option.getD_some]
      have hsz_eq : (s0.core.wvec[((l_v <<< (1 : Nat)) + 1#64).toNat]'(by omega)).toNat =
          fullWatchSize s0 l_v.toNat := by
        unfold fullWatchSize fullWatchSizeCore
        have h1 := List.getElem?_eq_getElem
          (by omega : ((l_v <<< (1 : Nat)) + 1#64).toNat < s0.core.wvec.length)
        rw [← hl_w1, h1, Option.getD_some]
      have hslice_l := hmw.slices l_v.toNat hl_lt
      let off_n := fullWatchOff s0 l_v.toNat
      let sz_n := fullWatchSize s0 l_v.toNat
      have hend_n : off_n + sz_n ≤ c.wcap := Nat.le_trans hbd hwl_le
      fvt_to_group
      refine wp_join_group (ts := [.bool])
        (fun (ap_n, ()) mj => ∃ wstk_n scr_n,
          let sn : FullState :=
            { s0 with core := { s0.core with wstk := wstk_n }
                      scratch := { s0.scratch with scratch_buf := scr_n } }
          FullSparseInvW c F0 F_cur sn ∧ (FullMem c sn ⋆ R) mj) ?_ ?_
      · rintro _ ⟨ap_n, ⟨⟩⟩ mj ⟨wstk_n, scr_n, hsp_n, hm_n⟩
        fvt_steps
        exact ih (ap_n, l_v + 1#64, ()) mj (by dsimp only; omega)
          ⟨by omega, wstk_n, scr_n, hsp_n, hm_n⟩
      · intro Jo hJo
        fvt_to_group
        · fvt_step; fvt_to_group
          · fvt_steps
            exact hJo (false, ()) ml ⟨wstk_l, scr_l, hsp_l, hm_l⟩
          · have hsz_le_cap : sz_n ≤ c.scratch_cap := by
              have hle : (BitVec.setWidth 64
                  (s0.core.wvec[((l_v <<< (1 : Nat)) + 1#64).toNat]'(by omega))).toNat ≤
                  (BitVec.ofNat 64 c.scratch_cap).toNat := by c0_bound
              rw [bv32_setWidth64_toNat, hsz_eq, bv64_ofNat_toNat (by omega)] at hle; exact hle
            have hoff_64 : (BitVec.setWidth 64
                (s0.core.wvec[(l_v <<< (1 : Nat)).toNat]'(by omega))).toNat = off_n := by
              rw [bv32_setWidth64_toNat, hoff_eq]
            have hsz_64 : (BitVec.setWidth 64
                (s0.core.wvec[((l_v <<< (1 : Nat)) + 1#64).toNat]'(by omega))).toNat = sz_n := by
              rw [bv32_setWidth64_toNat, hsz_eq]
            have hend_64 : (BitVec.setWidth 64
                  (s0.core.wvec[(l_v <<< (1 : Nat)).toNat]'(by omega)) +
                BitVec.setWidth 64
                  (s0.core.wvec[((l_v <<< (1 : Nat)) + 1#64).toNat]'(by omega))).toNat =
                off_n + sz_n := by
              rw [BitVec.toNat_add, hoff_64, hsz_64, Nat.mod_eq_of_lt (by omega)]
            fvt_to_group
            exact prio_part_loop_wp Γ hsp_l hl_lt hoff_64 hend_64 hend_n hsz_le_cap hslice_l hm_l
              fun wstk_k scr_p mk hsp_k hm_k => by
                fvt_steps; exact hJo (all_p, ()) mk ⟨wstk_k, scr_p, hsp_k, hm_k⟩
        · fvt_steps
          exact hJo (all_p, ()) ml ⟨wstk_l, scr_l, hsp_l, hm_l⟩
    · exact hQ all_p wstk_l scr_l ml hsp_l hm_l

end PrioritizeBinariesProof

end LeanQbe.T.Examples.Kissat.FullM6VivBackbone
