module

public import LeanQbe.T.Examples.Kissat.FullM4VivBce
public import LeanQbe.T.Examples.Kissat.FullM4VivBceProof0
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
public import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
public import LeanQbe.T.Examples.Kissat.FullBveVarLemmas2
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb

/-!
# Kissat M4f UNSAT-Only Specs & Vivification `Func.wp` Proofs (`12` Functions)

Defines all `16` standalone M4f function contracts (reusing canonical
`FullFastBveBudgets.fullVivifyFastSpec` for `full_vivify_m4`), shared state/BCE helper lemmas, and
complete UNSAT-sound `Func.wp` proofs (`XPost := False`, `0` SAT model proofs) for all `12` M4f
vivification functions:
1. `full_viv_sort_noccs_m4_wp`
2. `full_viv_has_l0_m4_wp`
3. `full_viv_l0_simp_m4_wp`
4. `full_viv_reuse_prefix_m4_wp`
5. `full_viv_finish_m4_wp`
6. `full_viv_clause_m4_wp`
7. `full_viv_sort_sched_m4_wp`
8. `full_viv_tier_match_m4_wp`
9. `full_viv_collect_m4_wp`
10. `full_viv_keys_m4_wp`
11. `full_viv_clear_tier_m4_wp`
12. `full_vivify_m4_wp` (exact canonical `FullFastBveBudgets.fullVivifyFastSpec`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4VivBce

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. Scoped load/store helpers, scratch-update lemmas, & BCE validity bridges -/

namespace M4Tactics

open FullArenaTactics
open scoped FullArenaTactics

@[scoped c0_load] theorem load_full_tmp0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pTmp = some s.core.tmp[0] := by
  simpa using load_full_tmp (i := 0) hi hm

@[scoped c0_store] theorem store_full_tmp0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.core.tmp.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pTmp ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
        (storeMem m i32 c.pTmp v) := by
  simpa using store_full_tmp (i := 0) v hi hm

end M4Tactics

theorem FullSparseInv.with_tarjan_reach {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {tr' : List (BitVec 32)} (htr : tr'.length = 2 * c.max_vars) :
    FullSparseInv c F0 { s with scratch := { s.scratch with tarjan_reach := tr' } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with tarjan_reach_len := htr }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem FullSparseInv.with_red_refs {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {rr' : List (BitVec 32)} (hrr : rr'.length = c.red_cap) :
    FullSparseInv c F0 { s with scratch := { s.scratch with red_refs := rr' } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with red_refs_len := hrr }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- Geometric BCE candidate validity matching `Full.fullBveTryBceSpec` (`FullBveBceWeakOk` plus
distinct clause variables when non-binary, preserved across `PH_GARB` marking). -/
def FullBceCandOk (c : FullCfg) (s : FullState) (w : BitVec 32) : Prop :=
  FullBveBceWeakOk c s w ∧
  ((w &&& 0x80000000#32) = 0#32 → ((fullArenaClauseLits s w.toNat).map (· / 2)).Nodup)

theorem FullBceCandOk.toWeak {c : FullCfg} {s : FullState} {w : BitVec 32}
    (h : FullBceCandOk c s w) : FullBveBceWeakOk c s w := h.1

private theorem bceCand_to_tryBceEntry {c : FullCfg} {s : FullState} {w : BitVec 32}
    (h : FullBceCandOk c s w) : FullBveVarSpecs.FullBveTryBceEntryOk c s w := by
  unfold FullBceCandOk FullBveBceWeakOk at h
  unfold FullBveVarSpecs.FullBveTryBceEntryOk
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hb)] at h ⊢; exact h.1
  · have hz : (w &&& 0x80000000#32) = 0#32 := Classical.not_not.mp hb
    rw [ite_eq_right_of_eq_false _ _ (eq_false hb)] at h ⊢; exact ⟨h.1.1, h.1.2.1, h.1.2.2, h.2 hz⟩

private theorem tryBceEntry_to_bceCand {c : FullCfg} {s : FullState} {w : BitVec 32}
    (h : FullBveVarSpecs.FullBveTryBceEntryOk c s w) : FullBceCandOk c s w := by
  unfold FullBveVarSpecs.FullBveTryBceEntryOk at h
  unfold FullBceCandOk FullBveBceWeakOk
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hb)] at h ⊢; exact ⟨h, fun hz => absurd hz hb⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hb)] at h ⊢
    exact ⟨⟨h.1, h.2.1, h.2.2.1⟩, fun _ => h.2.2.2⟩

theorem FullBceCandOk.of_entry {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {lit : Nat} {w : BitVec 32}
    (he : FullBveEntryOkW F_cur s lit w) : FullBceCandOk c s w :=
  tryBceEntry_to_bceCand (FullBveVarHelpers.FullBveEntryOkW.to_tryBceEntry h he)

theorem FullBceCandOk.with_same_arena {c : FullCfg} {s s' : FullState}
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    {w : BitVec 32} (h : FullBceCandOk c s w) : FullBceCandOk c s' w :=
  tryBceEntry_to_bceCand
    (FullBveVarHelpers.FullBveTryBceEntryOk.with_same_arena har hal (bceCand_to_tryBceEntry h))

theorem FullBceCandOk.of_markGarb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (ag' : BitVec 64)
    {w : BitVec 32} (h : FullBceCandOk c s w) :
    let s' : FullState :=
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } }
    FullBceCandOk c s' w :=
  tryBceEntry_to_bceCand
    (FullBveVarHelpers.FullBveTryBceEntryOk.of_arena_set_hdr hlen hw href ag'
      (bceCand_to_tryBceEntry h))

theorem FullBveBceWeakOk.with_same_arena {c : FullCfg} {s s' : FullState}
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    {w : BitVec 32} (h : FullBveBceWeakOk c s w) : FullBveBceWeakOk c s' w :=
  FullBveVarHelpers.FullBveTryBceOppOk.with_same_arena har hal h

theorem FullBveBceWeakOk.of_markGarb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (ag' : BitVec 64)
    {w : BitVec 32} (h : FullBveBceWeakOk c s w) :
    let s' : FullState :=
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } }
    FullBveBceWeakOk c s' w :=
  FullBveVarHelpers.FullBveTryBceOppOk.of_arena_set_hdr hlen hw href ag' h

theorem m4_sparseInvW_of_prop_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' unfl' : BitVec 64} {wvec' arena' wstk' : List (BitVec 32)}
    {wlen' : Nat} {wu' fuel' ctype' cref' c0' c1' oom' ticks' : BitVec 64}
    {wsort' : List (BitVec 32)} {phases' : List (BitVec 8)}
    (hlen' : ({ s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                            fuel := fuel', confl_type := ctype', confl_ref := cref',
                            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } } :
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
          search_ticks := ticks', wsort := wsort', phases := phases' } } := by
  let s' : FullState :=
    { s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                            fuel := fuel', confl_type := ctype', confl_ref := cref',
                            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } }
  have hnd' : FullArenaVarsNodup s' := fun ref href hng => by
    have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 ref href0 (hgb.symm.trans hng))
  have hrefs : ∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s' := fun ref hr => by
    change ref ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact hr
  exact FullVivTop.fullSparseInvW_of_prop_state hsp hlen' hw' hnd'
    ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hrefs

theorem m4_unsat_of_inconsistent {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hsp : FullSparseInv c F0 s) (hinc : s.core.inconsistent ≠ 0#64) : F0.Unsat := by
  obtain ⟨_, hw⟩ := hsp.1.witness
  exact hw.ext_sound.2 (hw.inconsistent_sound hinc)

private theorem m4_tmp_lt_of_perm {xs orig : List (BitVec 32)} {sz B : Nat}
    (hxs : sz ≤ xs.length) (hperm : (xs.take sz).Perm (orig.take sz))
    (hlt : ∀ idx < sz, (orig[idx]?.getD 0#32).toNat < B) :
    ∀ k < sz, (xs[k]?.getD 0#32).toNat < B := fun k hk => by
  have hm : xs[k]'(by omega) ∈ orig.take sz := hperm.mem_iff.mp (by
    rw [List.mem_iff_getElem]
    exact ⟨k, by rw [List.length_take]; omega, by simp [List.getElem_take]⟩)
  obtain ⟨idx, hidx, heq⟩ := List.mem_iff_getElem.mp hm
  have hle_o : (orig.take sz).length ≤ orig.length := by
    rw [List.length_take]; exact Nat.min_le_right _ _
  have hidx_sz : idx < sz := by rw [List.length_take] at hidx; omega
  have hget := hlt idx hidx_sz
  rw [List.getElem_take] at heq
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← heq]
  rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hget

private theorem m4_tmp_shift_hole {xs orig : List (BitVec 32)} {sz j : Nat} {x prev : BitVec 32}
    (hlen : xs.length = orig.length) (hsz : sz ≤ orig.length) (hj0 : 0 < j) (hjsz : j < sz)
    (hprev : xs[j - 1]? = some prev) (hperm : ((xs.set j x).take sz).Perm (orig.take sz)) :
    (((xs.set j prev).set (j - 1) x).take sz).Perm (orig.take sz) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj0)
  rw [Nat.succ_sub_one] at hprev ⊢
  let A := (xs.set (m + 1) x).take sz; let B := ((xs.set (m + 1) prev).set m x).take sz
  have hAl : A.length = sz := by simp [A, List.length_take, hlen]; omega
  let head := A.take m; let tail := A.drop (m + 2)
  have htk : head.length = m := by simp [head, List.length_take, hAl]; omega
  have hsp : ∀ (C : List (BitVec 32)) (a b : BitVec 32), C.length = sz →
      (∀ k < m, C[k]? = A[k]?) → C[m]? = some a → C[m + 1]? = some b →
      (∀ k, m + 2 ≤ k → C[k]? = A[k]?) → C = head ++ a :: b :: tail := by
    intro C a b hCl hk_lt hk_m hk_j hk_gt; refine List.ext_getElem? fun k => ?_
    by_cases hkm : k < m
    · rw [List.getElem?_append_left (by omega), List.getElem?_take]; simp [hkm, hk_lt k hkm]
    · rw [List.getElem?_append_right (by omega), htk]
      by_cases hk0 : k = m
      · subst hk0; simp [hk_m]
      · by_cases hk1 : k = m + 1
        · subst hk1; simp [hk_j]
        · rw [show k - m = (k - (m + 2)) + 2 by omega]
          simp only [List.getElem?_cons_succ, tail, List.getElem?_drop]
          rw [show m + 2 + (k - (m + 2)) = k by omega]; exact hk_gt k (by omega)
  have hA := hsp A prev x hAl (fun _ _ => rfl)
    (by simp only [A, List.getElem?_take, show m < sz by omega, ↓reduceIte,
          List.getElem?_set_ne (by omega : m + 1 ≠ m)]; exact hprev)
    (by simp only [A, List.getElem?_take, hjsz, ↓reduceIte]
        exact List.getElem?_set_self (by omega))
    fun _ _ => rfl
  have hB := hsp B x prev (by simp [B, List.length_take, hlen]; omega)
    (fun k hk => by
      simp only [A, B, List.getElem?_take, List.getElem?_set_ne (by omega : m ≠ k),
        List.getElem?_set_ne (by omega : m + 1 ≠ k)])
    (by simp only [B, List.getElem?_take, show m < sz by omega, ↓reduceIte]
        exact List.getElem?_set_self (by simp; omega))
    (by simp only [B, List.getElem?_take, hjsz, ↓reduceIte,
          List.getElem?_set_ne (by omega : m ≠ m + 1)]
        exact List.getElem?_set_self (by omega))
    fun k hk => by
      simp only [A, B, List.getElem?_take, List.getElem?_set_ne (by omega : m ≠ k),
        List.getElem?_set_ne (by omega : m + 1 ≠ k)]
  have hswap : B.Perm A := by
    rw [hA, hB]; exact List.Perm.append_left head (List.Perm.swap prev x tail)
  exact hswap.trans hperm

/-! ## 2. Per-function UNSAT-only `Spec` contracts (`9` new + canonical `fullVivifyFastSpec`) -/

/-- `full_viv_sort_noccs_m4(h, sz)`: sorts `tmp_lits[0 ..< sz)` in place by static `noccs` in
`tarjan_reach` (descending `noccs`, ascending literal ID tie-break). -/
def fullVivSortNoccsM4Spec : Spec [i64, i32] [] := fun (h, sz, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ sz.toNat ≤ c.max_vars ∧
    (∀ k < sz.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ tmp' m', tmp'.length = c.max_vars →
      (tmp'.take sz.toNat).Perm (s.core.tmp.take sz.toNat) →
      (∀ k, sz.toNat ≤ k → k < c.max_vars → tmp'[k]? = s.core.tmp[k]?) →
      (FullMem c { s with core := { s.core with tmp := tmp' } } ⋆ R) m' → Q () m'

/-- `full_viv_has_l0_m4(h, cref, sz)`: read-only level-0 assignment scan over `cref`. -/
def fullVivHasL0M4Spec : Spec [i64, i32, i32] [.bool] := fun (h, cref, sz, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    fullArenaClauseGarb s cref.toNat = false ∧ sz.toNat = fullArenaClauseSize s cref.toNat ∧
    (FullMem c s ⋆ R) m ∧ ∀ r : Bool, Q (r, ()) m

/-- `full_viv_l0_simp_m4(h, cref, sz)`: if `cref` has a level-0 assigned literal, backtracks to
level `0` and runs `full_viv_simplify`; returns `0` (continue), `1` (done/skip), or `20` (UNSAT). -/
def fullVivL0SimpM4Spec : Spec [i64, i32, i32] [i64] := fun (h, cref, sz, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    fullArenaClauseGarb s cref.toNat = false ∧ sz.toNat = fullArenaClauseSize s cref.toNat ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.fuel = s.core.fuel →
      s'.core.arena_len = s.core.arena_len → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 0#64 → cref.toNat ∈ fullArenaClauseRefs s' ∧ fullArenaClauseGarb s' cref.toNat = false) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `full_viv_reuse_prefix_m4(h, cref, sz)`: non-mutating prefix-trail reuse keeping the longest
shared decision prefix `frame_dec[1 .. keep_lvl]` and backtracking only to `keep_lvl`. -/
def fullVivReusePrefixM4Spec : Spec [i64, i32, i32] [] := fun (h, _cref, sz, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ sz.toNat ≤ c.max_vars ∧
    (∀ k < sz.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.probing = s.core.probing → s'.core.fuel = s.core.fuel →
      s'.core.tmp = s.core.tmp → s'.scratch.red_refs = s.scratch.red_refs →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- `full_viv_finish_m4(h, cref, sz, confl, implied, all_done)`: post-loop deduction, level-0
strengthening commit (`olen < sz`), or single-level conflict unwind preserving `FullSparseInvW`,
`fullArenaClauseRefs`, `fuel`, and `red_refs`. -/
def fullVivFinishM4Spec : Spec [i64, i32, i32, .bool, i32, .bool] [i64] :=
  fun (h, cref, sz, confl, implied, all_done, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ sz.toNat ≤ c.max_vars ∧
      cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
      fullArenaClauseSize s cref.toNat = sz.toNat ∧
      (confl = true → FullConflictOkW F_cur s) ∧
      (confl = false → implied ≠ 0xFFFFFFFF#32 →
        implied.toNat < 2 * s.core.cur_vars ∧ s.core.vals[implied.toNat]?.getD 0#8 = 1#8) ∧
      (confl = false → implied = 0xFFFFFFFF#32 → all_done = true →
        s.core.confl_type = 0#64 ∧
        ∀ l ∈ fullArenaClauseLits s cref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        FullSparseInvW c F0 F_cur s' → s'.core.fuel = s.core.fuel →
        s'.core.arena_len = s.core.arena_len → fullArenaClauseRefs s' = fullArenaClauseRefs s →
        s'.scratch.red_refs = s.scratch.red_refs →
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `full_viv_clause_m4(h, cref)`: prefix-trail-reusing single-clause vivification preserving
`FullSparseInvW`, `fullArenaClauseRefs`, and `red_refs` (early returns `1` on `PH_GARB`). -/
def fullVivClauseM4Spec : Spec [i64, i32] [i64] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.arena_len = s.core.arena_len → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `full_viv_sort_sched_m4(h, bn)`: shellsort on `red_refs[0 ..< 3*bn)` by watch-degree
descending with prefix grouping `(deg(k0) desc, k0 asc, deg(k1) desc, k1 asc, cref asc)`,
preserving `red_refs.length = c.red_cap` and `∀ k < bn, rr[3*k] ∈ fullArenaClauseRefs s`. -/
def fullVivSortSchedM4Spec : Spec [i64, i64] [] := fun (h, bn, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ 3 * bn.toNat ≤ c.red_cap ∧
    (∀ k < bn.toNat, (s.scratch.red_refs[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ rr' m', rr'.length = c.red_cap →
      (∀ k < bn.toNat, (rr'[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) →
      (FullMem c { s with scratch := { s.scratch with red_refs := rr' } } ⋆ R) m' → Q () m'

/-- `full_viv_tier_match_m4(h, hdr, tier_mode)`: read-only tier filter predicate. -/
def fullVivTierMatchM4Spec : Spec [i64, i32, i64] [.bool] := fun (h, _hdr, _tier_mode, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ (FullMem c s ⋆ R) m ∧ ∀ r, Q (r, ()) m

/-- `full_viv_collect_m4(h, tier_mode)`: collects unvivified tier-matching candidate clause refs
into `red_refs[3*k]` (read-only on `tarjan_reach`, only mutates `red_refs`). -/
def fullVivCollectM4Spec : Spec [i64, i64] [i64] := fun (h, _tier_mode, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ bn tr' rr' m',
      3 * bn.toNat ≤ c.red_cap → tr'.length = 2 * c.max_vars → rr'.length = c.red_cap →
      (∀ k < bn.toNat, (rr'[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) →
      (FullMem c { s with scratch := { s.scratch with tarjan_reach := tr', red_refs := rr' } } ⋆ R)
        m' → Q (bn, ()) m'

/-- `full_viv_keys_m4(h, bn)`: populates top-2 sort keys `(k0, k1)` into `red_refs[3*bi+1..2]`
for `bi < bn`, preserving valid clause refs in `red_refs[3*k]`. Only mutates `red_refs`. -/
def fullVivKeysM4Spec : Spec [i64, i64] [] := fun (h, bn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ 3 * bn.toNat ≤ c.red_cap ∧
    (∀ k < bn.toNat, (s.scratch.red_refs[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ rr' m',
      rr'.length = c.red_cap →
      (∀ k < bn.toNat, (rr'[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) →
      (FullMem c { s with scratch := { s.scratch with red_refs := rr' } } ⋆ R) m' → Q () m'

/-- `full_viv_clear_tier_m4(h, tier_mode)`: wrap-around scan clearing `PH_VIV` on matching tier
clauses at level `0`, preserving `FullSparseInv`, `cur_level = 0`, and `fuel`. -/
def fullVivClearTierM4Spec : Spec [i64, i64] [] := fun (h, _tier_mode, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = 0 → s'.core.fuel = s.core.fuel →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- `full_bce_side_m4(h, blk_lit, cand_off, cand_n, opp_off, opp_n)`: dense-mode single-polarity
BCE loop deleting blocked clauses and compacting surviving entries in `scratch_buf`. -/
def fullBceSideM4Spec : Spec [i64, i32, i32, i32, i32, i32] [i32] :=
  fun (h, blk_lit, cand_off, cand_n, opp_off, opp_n, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ blk_lit.toNat < 2 * s.core.cur_vars ∧
      cand_off.toNat + cand_n.toNat ≤ c.scratch_cap ∧
      opp_off.toNat + opp_n.toNat ≤ c.scratch_cap ∧
      (cand_off.toNat + cand_n.toNat ≤ opp_off.toNat ∨
        opp_off.toNat + opp_n.toNat ≤ cand_off.toNat) ∧
      (∀ i < cand_n.toNat,
        FullBceCandOk c s (s.scratch.scratch_buf[cand_off.toNat + i]?.getD 0#32)) ∧
      (∀ j < opp_n.toNat,
        FullBveBceWeakOk c s (s.scratch.scratch_buf[opp_off.toNat + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ rem s' m',
        FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
        s'.core.fuel = s.core.fuel → rem.toNat ≤ cand_n.toNat →
        (∀ k < rem.toNat,
          FullBceCandOk c s' (s'.scratch.scratch_buf[cand_off.toNat + k]?.getD 0#32)) →
        (∀ j < opp_n.toNat,
          s'.scratch.scratch_buf[opp_off.toNat + j]? =
            s.scratch.scratch_buf[opp_off.toNat + j]?) →
        (∀ w, FullBceCandOk c s w → FullBceCandOk c s' w) →
        (FullMem c s' ⋆ R) m' → Q (rem, ()) m'

/-- `full_bce_pair_m4(h, v, np, nn)`: dual-polarity BCE pass over both `pl = 2*v` and `nl = 2*v+1`.
-/
def fullBcePairM4Spec : Spec [i64, i32, i32, i32] [] := fun (h, v, np, nn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 128 ≤ c.scratch_cap ∧
    v.toNat < s.core.cur_vars ∧ np.toNat ≤ 64 ∧ nn.toNat ≤ 64 ∧
    (∀ i < np.toNat, FullBceCandOk c s (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
    (∀ j < nn.toNat, FullBceCandOk c s (s.scratch.scratch_buf[64 + j]?.getD 0#32)) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → (FullMem c s' ⋆ R) m' → Q () m'

/-- `full_bce_var_m4(h, v)`: per-variable dual-polarity dense-mode BCE driver (`cap = 64`). -/
def fullBceVarM4Spec : Spec [i64, i32] [] := fun (h, v, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ v.toNat < s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → (FullMem c s' ⋆ R) m' → Q () m'

/-- `full_bce_m4(h, budget)`: standalone sparse-mode dual-polarity BCE pass preserving
`FullSparseInv`, `cur_level = 0`, fuel monotonicity, and UNSAT soundness (`20#64 → F0.Unsat`). -/
def fullBceM4Spec : Spec [i64, i64] [i64] := fun (h, _budget, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ## 3. Vivification M4f `Func.wp` proofs (`6` functions) -/

section VivM4Proofs

open FullVivTopTactics FullVivTop
open scoped FullArenaTactics FullVivTopTactics M4Tactics

/-- Watch-vec length slot index `((u64)x << 1) + 1ULL` evaluates to `2 * x.toNat + 1`. -/
private theorem m4_bv32_shl1_add1 (x : BitVec 32) :
    (x.setWidth 64 <<< (BitVec.toNat (1 : BitVec 64) % 64) + 1#64).toNat = 2 * x.toNat + 1 := by
  have hx : (x.setWidth 64).toNat = x.toNat := bv32_setWidth64_toNat x
  have h1 : BitVec.toNat (1 : BitVec 64) % 64 = 1 := rfl
  have hlt : x.toNat < 2 ^ 32 := x.isLt
  rw [h1, BitVec.toNat_add, BitVec.toNat_shiftLeft, hx, Nat.shiftLeft_eq]
  simp only [show (1#64 : BitVec 64).toNat = 1 from rfl]
  omega

theorem full_viv_sort_noccs_m4_wp (Γ : Env) :
    ∀ a m Q X, fullVivSortNoccsM4Spec a m Q X →
      Func.wp Γ full_viv_sort_noccs_m4_body a m Q X := by
  rintro ⟨h, sz, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hsz_le, hlt_orig, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have htl0 := hlen.core_ok.tmp_len_arr; have hwl0 := hlen.core_ok.wvec_len
  unfold Func.wp full_viv_sort_noccs_m4_body
  fvt_steps
  refine wp_loop_inv (ts := [i32])
    (fun (i, ()) m1 => ∃ tmp1 : List (BitVec 32),
      1 ≤ i.toNat ∧ (sz.toNat = 0 → i.toNat = 1) ∧ (0 < sz.toNat → i.toNat ≤ sz.toNat) ∧
      tmp1.length = c.max_vars ∧ (tmp1.take sz.toNat).Perm (s.core.tmp.take sz.toNat) ∧
      (∀ k, sz.toNat ≤ k → k < c.max_vars → tmp1[k]? = s.core.tmp[k]?) ∧
      (FullMem c { s with core := { s.core with tmp := tmp1 } } ⋆ R) m1)
    (fun (i, ()) _ => sz.toNat - i.toNat)
    (fun J_out hJ => by
      fvt_steps
      have h1 : (1#32 : BitVec 32).toNat = 1 := rfl
      exact hJ (1#32, ()) m ⟨s.core.tmp, by omega, fun _ => rfl, fun h => by omega, htl0,
        .refl _, fun _ _ _ => rfl, hm0⟩)
    (fun J_out ⟨i, ⟨⟩⟩ m1 ⟨tmp1, hi1, hiz, hipos, htl1, hperm1, hout1, hm1⟩ ih => ?_)
  fvt_steps
  · have hi_lt : i.toNat < sz.toNat := by c0_bound
    have hi64 : (i.setWidth 64).toNat = i.toNat := bv32_setWidth64_toNat i
    have hi_tmp : (i.setWidth 64).toNat < tmp1.length := by rw [hi64]; omega
    have htmp1_lt := m4_tmp_lt_of_perm (by omega) hperm1 hlt_orig
    let x : BitVec 32 := tmp1[i.toNat]'(by omega)
    have hx_eq : tmp1[(i.setWidth 64).toNat]'hi_tmp = x :=
      Option.some.inj (by
        rw [← List.getElem?_eq_getElem hi_tmp, hi64, List.getElem?_eq_getElem (by omega)])
    have hx_lt_v : x.toNat < 2 * c.max_vars := by
      have h := htmp1_lt i.toNat hi_lt
      rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
    have hx_wv : ((tmp1[(i.setWidth 64).toNat]'hi_tmp).setWidth 64 <<<
        (BitVec.toNat (1 : BitVec 64) % 64) + 1#64).toNat < s.core.wvec.length := by
      rw [hx_eq, m4_bv32_shl1_add1, hwl0]; omega
    have hperm_init : ((tmp1.set i.toNat x).take sz.toNat).Perm (s.core.tmp.take sz.toNat) := by
      rwa [show tmp1.set i.toNat x = tmp1 from List.ext_getElem (by simp) fun k hk _ => by
        by_cases hki : k = i.toNat
        · subst hki; rw [List.getElem_set_self]
        · rw [List.getElem_set_ne (Ne.symm hki)]]
    fvt_steps
    refine wp_loop_inv (ts := [i32])
      (fun (j, ()) m2 => ∃ tmp2 : List (BitVec 32),
        j.toNat ≤ i.toNat ∧ tmp2.length = c.max_vars ∧
        ((tmp2.set j.toNat x).take sz.toNat).Perm (s.core.tmp.take sz.toNat) ∧
        (∀ k, sz.toNat ≤ k → k < c.max_vars → tmp2[k]? = s.core.tmp[k]?) ∧
        (FullMem c { s with core := { s.core with tmp := tmp2 } } ⋆ R) m2)
      (fun (j, ()) _ => j.toNat)
      (fun J2 hJ2 => by
        fvt_steps; exact hJ2 (i, ()) m1 ⟨tmp1, Nat.le_refl _, htl1, hperm_init, hout1, hm1⟩)
      (fun J2 ⟨j, ⟨⟩⟩ m2 ⟨tmp2, hj_le, htl2, hperm2, hout2, hm2⟩ ih2 => ?_)
    have hj64 : (j.setWidth 64).toNat = j.toNat := bv32_setWidth64_toNat j
    have hj_tmp : (j.setWidth 64).toNat < tmp2.length := by rw [hj64]; omega
    have hplace : ∀ (j0 : BitVec 32) (tmp_f : List (BitVec 32)) (mf : Mem 64),
        j0.toNat ≤ i.toNat → tmp_f.length = c.max_vars →
        ((tmp_f.set j0.toNat x).take sz.toNat).Perm (s.core.tmp.take sz.toNat) →
        (∀ k, sz.toNat ≤ k → k < c.max_vars → tmp_f[k]? = s.core.tmp[k]?) →
        (FullMem c { s with core := { s.core with tmp := tmp_f.set j0.toNat x } } ⋆ R) mf →
        J_out (i + 1#32, ()) mf := by
      intro j0 tmp_f mf hj0 htlf hpermf houtf hmf
      have hi1_nat : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
      exact ih (i + 1#32, ()) mf (by dsimp only; omega)
        ⟨tmp_f.set j0.toNat x, by omega, fun hz => by omega, fun _ => by omega, by simp [htlf],
         hpermf, fun k hk1 hk2 => by rw [List.getElem?_set_ne (by omega)]; exact houtf k hk1 hk2,
         hmf⟩
    fvt_steps
    · have hj_pos : 0 < j.toNat := by c0_bound
      have hj1_nat : (j - 1).toNat = j.toNat - 1 := by bv_omega
      have hj1_64 : ((j - 1).setWidth 64).toNat = j.toNat - 1 := by
        rw [bv32_setWidth64_toNat, hj1_nat]
      have hj1_tmp : ((j - 1).setWidth 64).toNat < tmp2.length := by rw [hj1_64]; omega
      let prev : BitVec 32 := tmp2[j.toNat - 1]'(by omega)
      have hprev_raw : tmp2[((j - 1).setWidth 64).toNat]'hj1_tmp = prev :=
        Option.some.inj (by
          rw [← List.getElem?_eq_getElem hj1_tmp, hj1_64, List.getElem?_eq_getElem (by omega)])
      have hprev_eq : tmp2[j.toNat - 1]? = some prev := List.getElem?_eq_getElem (by omega)
      have hprev_lt : prev.toNat < 2 * c.max_vars := by
        have h := m4_tmp_lt_of_perm (by simp [htl2]; omega) hperm2 hlt_orig (j.toNat - 1) (by omega)
        rwa [List.getElem?_set_ne (by omega), hprev_eq, Option.getD_some] at h
      have hp_wv : ((tmp2[((j - 1).setWidth 64).toNat]'hj1_tmp).setWidth 64 <<<
          (BitVec.toNat (1 : BitVec 64) % 64) + 1#64).toNat < s.core.wvec.length := by
        rw [hprev_raw, m4_bv32_shl1_add1, hwl0]; omega
      have hperm_sh := m4_tmp_shift_hole (by omega : tmp2.length = s.core.tmp.length)
        (by omega : sz.toNat ≤ s.core.tmp.length) hj_pos (by omega) hprev_eq hperm2
      fvt_steps
      · exact hplace j tmp2 _ hj_le htl2 hperm2 hout2 (by simpa only [hj64, hx_eq] using hm)
      · exact hplace j tmp2 _ hj_le htl2 hperm2 hout2 (by simpa only [hj64, hx_eq] using hm)
      · exact ih2 (j - 1, ()) _ (by dsimp only; omega) ⟨tmp2.set j.toNat prev, by omega,
          by simp [htl2], by rw [hj1_nat]; exact hperm_sh,
          fun k hk1 hk2 => by rw [List.getElem?_set_ne (by omega)]; exact hout2 k hk1 hk2,
          by simpa only [hj64, hprev_raw] using hm⟩
      · exact ih2 (j - 1, ()) _ (by dsimp only; omega) ⟨tmp2.set j.toNat prev, by omega,
          by simp [htl2], by rw [hj1_nat]; exact hperm_sh,
          fun k hk1 hk2 => by rw [List.getElem?_set_ne (by omega)]; exact hout2 k hk1 hk2,
          by simpa only [hj64, hprev_raw] using hm⟩
    · exact hplace j tmp2 _ hj_le htl2 hperm2 hout2 (by simpa only [hj64, hx_eq] using hm)
  · exact hQ tmp1 m1 htl1 hperm1 hout1 hm1

theorem full_viv_has_l0_m4_wp (Γ : Env) :
    ∀ a m Q X, fullVivHasL0M4Spec a m Q X → Func.wp Γ full_viv_has_l0_m4_body a m Q X := by
  rintro ⟨h, cref, sz, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hsp, href, hng, hsz, hm0, hQ⟩
  have hwf := hsp.2.1.arena.refs_wf cref.toNat href
  have hcl := hsp.1.core_ok
  have harc := c.harena; have hmx := c.hmaxv; unfold dimacsBound at harc hmx
  have har_len := hcl.arena_len_arr; have har_le := hcl.arena_len_le
  have hvl := hcl.vals_len; have hll := hcl.lvl_len; have hcv := hcl.cur_vars_le
  have hbd : cref.toNat + 3 + sz.toNat ≤ s.core.arena.length := by
    rw [hsz]; unfold fullArenaClauseSize at *; omega
  unfold Func.wp full_viv_has_l0_m4_body
  fvt_steps
  refine wp_loop_inv (ts := [i32])
    (fun (i, ()) ml => i.toNat ≤ sz.toNat ∧ ml = m0)
    (fun (i, ()) _ => sz.toNat - i.toNat)
    (fun J hJ => by fvt_steps; exact hJ (0#32, ()) m0 ⟨Nat.zero_le _, rfl⟩)
    (fun J ⟨i, ⟨⟩⟩ ml ⟨hi_le, rfl⟩ ih => by
      fvt_steps
      · have hi_lt : i.toNat < sz.toNat := by c0_bound
        have hidx : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat =
            cref.toNat + 3 + i.toNat := by bv_omega
        have hidx_lt : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat <
            s.core.arena.length := by omega
        have hl_mem : (s.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hidx_lt).toNat
            ∈ fullArenaClauseLits s cref.toNat := by
          unfold fullArenaClauseLits fullArenaClauseLitsCore
          rw [show fullArenaClauseSizeCore s.core cref.toNat = sz.toNat from hsz.symm, List.mem_map]
          refine ⟨s.core.arena[cref.toNat + 3 + i.toNat]'(by omega), ?_, ?_⟩
          · have hlt : i.toNat < ((s.core.arena.drop (cref.toNat + 3)).take sz.toNat).length := by
              simp [List.length_take, List.length_drop]; omega
            simpa [List.getElem_take, List.getElem_drop] using List.getElem_mem hlt
          · exact congrArg BitVec.toNat (Option.some.inj (by
              rw [← List.getElem?_eq_getElem (by omega), ← hidx,
                List.getElem?_eq_getElem hidx_lt]))
        have hl_lt : (s.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hidx_lt).toNat <
            2 * s.core.cur_vars := hsp.2.1.arena.lits_lt cref.toNat href hng _ hl_mem
        have hl_vl : ((s.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'
            hidx_lt).setWidth 64).toNat < s.core.vals.length := by
          rw [bv32_setWidth64_toNat]; omega
        have hl_lv : (((s.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'
            hidx_lt) >>> (1#32 : BitVec 32).toNat).setWidth 64).toNat < s.core.lvl.length := by
          rw [bv32_setWidth64_toNat]
          have : ((s.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hidx_lt) >>>
              1).toNat = (s.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'
              hidx_lt).toNat / 2 := bv32_lshr_1 _
          rw [show (1#32 : BitVec 32).toNat = 1 from rfl, this]; omega
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
        fvt_steps
        · exact hQ true
        · exact ih (i + 1#32, ()) ml (by dsimp only; omega) ⟨by omega, rfl⟩
        · exact ih (i + 1#32, ()) ml (by dsimp only; omega) ⟨by omega, rfl⟩
      · exact hQ false)

theorem full_viv_l0_simp_m4_wp (Γ : Env)
    (hHasL0 : ∀ a m Q X, fullVivHasL0M4Spec a m Q X →
      Γ "full_viv_has_l0_m4" [i64, i32, i32] [.bool] a m Q X)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hSimplify : ∀ a m Q X, fullVivSimplifyM4Spec a m Q X →
      Γ "full_viv_simplify" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, fullVivL0SimpM4Spec a m Q X → Func.wp Γ full_viv_l0_simp_m4_body a m Q X := by
  rintro ⟨h, cref, sz, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hsp0, href0, hng0, hsz0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl0 := hsp0.1.core_ok
  unfold Func.wp full_viv_l0_simp_m4_body
  fvt_steps
  c0_call hHasL0
  refine ⟨c, F0, F_cur, s, R, rfl, hsp0, href0, hng0, hsz0, hm0, fun hasl0 => ?_⟩
  fvt_to_group
  · refine wp_join_group (ts := [])
      (fun () m_bt => ∃ s_bt : FullState,
        FullSparseInvW c F0 F_cur s_bt ∧ s_bt.core.cur_level = 0 ∧
        s_bt.core.fuel = s.core.fuel ∧ s_bt.core.arena_len = s.core.arena_len ∧
        fullArenaClauseRefs s_bt = fullArenaClauseRefs s ∧
        s_bt.scratch.red_refs = s.scratch.red_refs ∧
        cref.toNat ∈ fullArenaClauseRefs s_bt ∧ fullArenaClauseGarb s_bt cref.toNat = false ∧
        (FullMem c s_bt ⋆ R) m_bt) ?_ ?_
    · rintro _ ⟨⟩ m_bt ⟨s_bt, hsp_bt, hcl_bt0, hfl_bt, hal_bt, hrefs_bt, hrr_bt, href_bt, hng_bt,
        hm_bt⟩
      fvt_steps
      c0_call hSimplify
      refine ⟨c, F0, F_cur, s_bt, R, rfl, hsp_bt, hcl_bt0, href_bt, hng_bt, hm_bt,
        fun sr s_s m_s hsp_s _ _ hal_s _ hfl_s hrefs_s hrr_s hsr h20 h0 hm_s => ?_⟩
      rcases hsr with rfl | rfl | rfl
      · fvt_steps
        · contradiction
        · exact hQ 0#64 s_s m_s hsp_s (hfl_s.trans hfl_bt) (hal_s.trans hal_bt)
            (hrefs_s.trans hrefs_bt) (hrr_s.trans hrr_bt) (Or.inl rfl) (fun h => by cases h)
            h0 hm_s
      · fvt_steps
        exact hQ 1#64 s_s m_s hsp_s (hfl_s.trans hfl_bt) (hal_s.trans hal_bt)
          (hrefs_s.trans hrefs_bt) (hrr_s.trans hrr_bt) (Or.inr (Or.inl rfl))
          (fun h => by cases h) (fun h => by cases h) hm_s
      · fvt_steps
        · exact hQ 20#64 s_s m_s hsp_s (hfl_s.trans hfl_bt) (hal_s.trans hal_bt)
            (hrefs_s.trans hrefs_bt) (hrr_s.trans hrr_bt) (Or.inr (Or.inr rfl))
            (fun _ => h20 rfl) (fun h => by cases h) hm_s
        · contradiction
    · intro Jbt hJbt
      have hcl0_lt : s.core.cur_level < 2 ^ 64 := by
        have := hsp0.2.1.cur_level_le; have := hcl0.trail_end_le
        have := hcl0.cur_vars_le; omega
      fvt_steps
      · c0_call hBacktrack
        refine ⟨c, s, R, rfl, hsp0.1, hcl0_lt,
          (by have h0n : BitVec.toNat (0 : BitVec 64) = 0 := rfl; rw [h0n]; intro;
              have := hsp0.2.1.cur_level_le; have := hcl0.trail_end_le
              have := hcl0.cur_vars_le; omega),
          hsp0.2.1.trail_lits_lt, hm0,
          fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
            hlen_bt _ _ hcl_bt hpres_bt hsc_bt _ _ hw_bt _ hm_bt => ?_⟩
        have hsp_bt : FullSparseInvW c F0 F_cur _ :=
          FullVivTop.FullSparseInvW.of_backtrack hsp0 (Nat.zero_le _) hlen_bt hpres_bt
            (hw_bt F0 F_cur hsp0.2.1 (Nat.zero_le _))
        rcases hsc_bt with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
        exact hJbt () m_bt ⟨_, hsp_bt, by rw [hcl_bt]; simp, rfl, rfl, rfl, rfl, href0, hng0, hm_bt⟩
      · have hcl0_eq : s.core.cur_level = 0 := by
          have h0 : (BitVec.ofNat 64 s.core.cur_level).toNat = 0 := by rw [hc]; rfl
          rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl0_lt] at h0
        exact hJbt () m0 ⟨s, hsp0, hcl0_eq, rfl, rfl, rfl, rfl, href0, hng0, hm0⟩
  · fvt_steps
    exact hQ 0#64 s m0 hsp0 rfl rfl rfl rfl (Or.inl rfl) (fun h => by cases h)
      (fun _ => ⟨href0, hng0⟩) hm0

theorem full_viv_reuse_prefix_m4_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X) :
    ∀ a m Q X, fullVivReusePrefixM4Spec a m Q X →
      Func.wp Γ full_viv_reuse_prefix_m4_body a m Q X := by
  rintro ⟨h, cref, sz, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hsp0, hsz_le, htmp0_lt, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl0 := hsp0.1.core_ok
  have hclvl_le : s.core.cur_level ≤ c.max_vars := by
    have := hsp0.2.1.cur_level_le; have := hcl0.trail_end_le; have := hcl0.cur_vars_le; omega
  have hclvl_lt64 : s.core.cur_level < 2 ^ 64 := by omega
  unfold Func.wp full_viv_reuse_prefix_m4_body
  fvt_to_group
  · fvt_steps; exact hQ s m0 hsp0 rfl rfl rfl rfl rfl rfl rfl hm0
  · fvt_to_group
    let clvl : BitVec 64 := BitVec.ofNat 64 s.core.cur_level
    have hclvl_nat : clvl.toNat = s.core.cur_level := by
      simp [clvl, Nat.mod_eq_of_lt hclvl_lt64]
    -- Read-only prefix-matching loop `while (i < sz && keep_lvl < clvl)` with `break`
    refine wp_loop_break_group (brkTs := [i64, i32]) (lpTs := [i64, i32])
      (fun (keep_b, _ib, ()) mb => keep_b.toNat ≤ s.core.cur_level ∧ mb = m0)
      (fun rem (keep, i, ()) mp =>
        keep.toNat ≤ s.core.cur_level ∧ i.toNat ≤ sz.toNat ∧ rem = sz.toNat - i.toNat ∧ mp = m0)
      ?_ ?_ ?_
    · -- After prefix loop: scan `j < sz && keep_lvl > 0` for `cref` reasons, then backtrack
      rintro _ ⟨keep_b, _ib, ⟨⟩⟩ mb ⟨hkb_le, hmb⟩
      rw [hmb]
      refine wp_loop_inv (ts := [i64, i32])
        (fun (kl, j, ()) ml => j.toNat ≤ sz.toNat ∧ kl.toNat ≤ s.core.cur_level ∧ ml = m0)
        (fun (_, j, ()) _ => sz.toNat - j.toNat) ?_ ?_
      · intro J2 hJ2; fvt_steps; exact hJ2 (keep_b, 0#32, ()) m0 ⟨Nat.zero_le _, hkb_le, rfl⟩
      · intro J2 ⟨kl, j, ⟨⟩⟩ ml ⟨hj_le, hkl_le, hml⟩ ih2
        rw [hml]
        fvt_steps
        · have hj_lt : j.toNat < sz.toNat := by c0_bound
          have hj_nat : (j.setWidth 64).toNat = j.toNat := bv32_setWidth64_toNat j
          have hj_tmp : (j.setWidth 64).toNat < s.core.tmp.length := by
            rw [hj_nat, hcl0.tmp_len_arr]; omega
          have hl_lt : (s.core.tmp[(j.setWidth 64).toNat]'hj_tmp).toNat < 2 * s.core.cur_vars :=
            by
            have h := htmp0_lt j.toNat hj_lt
            rw [List.getElem?_eq_getElem (by rw [hcl0.tmp_len_arr]; omega), Option.getD_some] at h
            simpa [hj_nat] using h
          have hl_vl : ((s.core.tmp[(j.setWidth 64).toNat]'hj_tmp).setWidth 64).toNat <
              s.core.vals.length := by
            rw [bv32_setWidth64_toNat, hcl0.vals_len]; have := hcl0.cur_vars_le; omega
          have hl_rsn : (((s.core.tmp[(j.setWidth 64).toNat]'hj_tmp) >>>
              (1#32 : BitVec 32).toNat).setWidth 64).toNat < s.core.rsns.length := by
            rw [bv32_setWidth64_toNat, hcl0.rsns_len,
              show (1#32 : BitVec 32).toNat = 1 from rfl, bv32_lshr_1]
            have := hcl0.cur_vars_le; omega
          have hl_lv : (((s.core.tmp[(j.setWidth 64).toNat]'hj_tmp) >>>
              (1#32 : BitVec 32).toNat).setWidth 64).toNat < s.core.lvl.length := by
            rw [bv32_setWidth64_toNat, hcl0.lvl_len,
              show (1#32 : BitVec 32).toNat = 1 from rfl, bv32_lshr_1]
            have := hcl0.cur_vars_le; omega
          have hj1 : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
          fvt_to_group
          refine wp_join_group (ts := [i64])
            (fun (kl', ()) mj => kl'.toNat ≤ s.core.cur_level ∧ mj = m0) ?_ ?_
          · rintro _ ⟨kl', ⟨⟩⟩ mj ⟨hkl', hmj⟩
            rw [hmj]; fvt_steps
            exact ih2 (kl', j + 1#32, ()) m0 (by dsimp only; omega) ⟨by omega, hkl', rfl⟩
          · intro Jj hJj
            fvt_to_group
            · refine wp_join_group (ts := [i64])
                (fun (kl', ()) mj => kl'.toNat ≤ s.core.cur_level ∧ mj = m0) ?_ ?_
              · rintro _ ⟨kl', ⟨⟩⟩ mj h; fvt_steps; exact hJj (kl', ()) mj h
              · intro Ji hJi
                fvt_steps
                · exact hJi (0#64, ()) m0 ⟨Nat.zero_le _, rfl⟩
                · exact hJi _ m0 ⟨Nat.le_trans (Nat.le_of_lt (by c0_bound)) hkl_le, rfl⟩
                · exact hJi (kl, ()) m0 ⟨hkl_le, rfl⟩
            · fvt_steps; exact hJj (kl, ()) m0 ⟨hkl_le, rfl⟩
            · fvt_steps; exact hJj (kl, ()) m0 ⟨hkl_le, rfl⟩
        -- Loop 2 exits (`kl < clvl` -> backtrack; `¬(kl < clvl)` -> return `s`)
        all_goals try exact hQ s m0 hsp0 rfl rfl rfl rfl rfl rfl rfl hm0
        all_goals
          have hkl_lt : kl.toNat < s.core.cur_level := by
            have hc0 : kl.toNat < clvl.toNat := by c0_bound
            omega
          c0_call hBacktrack
          refine ⟨c, s, R, rfl, hsp0.1, hclvl_lt64, fun _ => by omega,
            hsp0.2.1.trail_lits_lt, hm0,
            fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
              hlen_bt _ _ _ hpres_bt hsc_bt _ _ hw_bt _ hm_bt => ?_⟩
          have hsp_bt : FullSparseInvW c F0 F_cur _ :=
            FullVivTop.FullSparseInvW.of_backtrack hsp0 (by omega) hlen_bt hpres_bt
              (hw_bt F0 F_cur hsp0.2.1 (by omega))
          rcases hsc_bt with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
          dsimp only; apply hJ; fvt_steps
          exact hQ _ m_bt hsp_bt rfl rfl rfl rfl rfl rfl rfl hm_bt
    · -- Prefix loop body (read-only)
      intro B L rem ⟨keep, i, ⟨⟩⟩ mp hB hL ⟨hkp_le, hi_le, hrem, hmp⟩
      subst hrem; rw [hmp]
      fvt_steps
      · have hi_lt : i.toNat < sz.toNat := by c0_bound
        have hkp_lt : keep.toNat < s.core.cur_level := by
          have hc0 : keep.toNat < clvl.toNat := by c0_bound
          omega
        have hi_nat : (i.setWidth 64).toNat = i.toNat := bv32_setWidth64_toNat i
        have hi_tmp : (i.setWidth 64).toNat < s.core.tmp.length := by
          rw [hi_nat, hcl0.tmp_len_arr]; omega
        have hfd_idx : (keep + 1#64).toNat < s.core.frame_dec.length := by
          rw [hcl0.frame_dec_len]; bv_omega
        have hl_lt : (s.core.tmp[(i.setWidth 64).toNat]'hi_tmp).toNat < 2 * s.core.cur_vars := by
          have h := htmp0_lt i.toNat hi_lt
          rw [List.getElem?_eq_getElem (by rw [hcl0.tmp_len_arr]; omega), Option.getD_some] at h
          simpa [hi_nat] using h
        have hl_vl : ((s.core.tmp[(i.setWidth 64).toNat]'hi_tmp).setWidth 64).toNat <
            s.core.vals.length := by
          rw [bv32_setWidth64_toNat, hcl0.vals_len]; have := hcl0.cur_vars_le; omega
        have hl_lv : (((s.core.tmp[(i.setWidth 64).toNat]'hi_tmp) >>>
            (1#32 : BitVec 32).toNat).setWidth 64).toNat < s.core.lvl.length := by
          rw [bv32_setWidth64_toNat, hcl0.lvl_len,
            show (1#32 : BitVec 32).toNat = 1 from rfl, bv32_lshr_1]
          have := hcl0.cur_vars_le; omega
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
        have hkp1 : (keep + 1#64).toNat = keep.toNat + 1 := by bv_omega
        fvt_to_group
        refine wp_join_group (ts := [i64])
          (fun (keep', ()) mj => keep'.toNat ≤ s.core.cur_level ∧ mj = m0) ?_ ?_
        · rintro _ ⟨keep', ⟨⟩⟩ mj ⟨hkp', hmj⟩
          rw [hmj]; fvt_steps
          exact hL (sz.toNat - (i + 1#32).toNat) (keep', i + 1#32, ()) m0
            (by rw [hi1]; omega) ⟨hkp', by rw [hi1]; omega, rfl, rfl⟩
        · intro Jk hJk
          fvt_steps
          · exact hJk (keep + 1#64, ()) m0 ⟨by rw [hkp1]; omega, rfl⟩
          · exact hJk (keep, ()) m0 ⟨hkp_le, rfl⟩
          · exact hB (keep, i, ()) m0 ⟨hkp_le, rfl⟩
          · exact hB (keep, i, ()) m0 ⟨hkp_le, rfl⟩
      · exact hB (keep, i, ()) m0 ⟨hkp_le, rfl⟩
      · exact hB (keep, i, ()) m0 ⟨hkp_le, rfl⟩
    · intro B L _ hL
      fvt_steps
      exact hL sz.toNat (0#64, 0#32, ()) m0 ⟨Nat.zero_le _, Nat.zero_le _, by simp, rfl⟩

private theorem m4_viv_clause_prop_step (Γ : Env)
    (hPropIgn : ∀ a m Q X, Full.fullPropagateIgnoreSpec a m Q X →
      Γ "full_propagate_ignore" [i64, i64] [i64] a m Q X)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s5 sp s_as : FullState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {B : Cont [i32, .bool, i32]} {J_jn : Cont [.bool]}
    {cref i lit sz : BitVec 32} {tmp5 : List (BitVec 32)} {lits2 : List Nat} {m_as : Mem 64}
    (hQ : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullSparseInvW c F0 F_cur s' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.arena_len = s.core.arena_len → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs →
      r = 1#64 ∨ r = 2#64 ∨ r = 20#64 → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hB : ∀ (r : Tup Val [i32, .bool, i32]) (m' : Mem 64),
      (match r with
      | (ib, confl, implied, ()) => ∃ sb : FullState,
        FullSparseInvW c F0 F_cur sb ∧
        sb.core.cur_vars = s5.core.cur_vars ∧ sb.core.arena_len = s5.core.arena_len ∧
        sb.core.probing = s5.core.probing ∧ sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        fullArenaClauseRefs sb = fullArenaClauseRefs s ∧
        sb.scratch.red_refs = s.scratch.red_refs ∧
        cref.toNat ∈ fullArenaClauseRefs sb ∧
        fullArenaClauseGarb sb cref.toNat = false ∧
        fullArenaClauseSize sb cref.toNat = sz.toNat ∧
        (confl = true ∨ implied ≠ 0xFFFFFFFF#32 ∨ ib.toNat = sz.toNat) ∧
        (confl = true → FullConflictOkW F_cur sb) ∧
        (confl = false → implied ≠ 0xFFFFFFFF#32 →
          implied.toNat < 2 * sb.core.cur_vars ∧
          sb.core.vals[implied.toNat]?.getD 0#8 = 1#8) ∧
        (confl = false → implied = 0xFFFFFFFF#32 →
          sb.core.confl_type = 0#64 ∧
          ∀ l ∈ fullArenaClauseLits sb cref.toNat, sb.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
        (FullMem c sb ⋆ R) m') → B r m')
    (hJ_jn : ∀ (xs : Tup Val [.bool]) (m : Mem 64),
      (match xs with
      | (_, ()) => ∃ s_jn : FullState,
        FullSparseInvW c F0 F_cur s_jn ∧
        s_jn.core.cur_vars = s5.core.cur_vars ∧
        s_jn.core.arena_len = s5.core.arena_len ∧
        s_jn.core.probing = s5.core.probing ∧ s_jn.core.tmp = tmp5 ∧
        s_jn.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        fullArenaClauseRefs s_jn = fullArenaClauseRefs s ∧
        s_jn.scratch.red_refs = s.scratch.red_refs ∧
        cref.toNat ∈ fullArenaClauseRefs s_jn ∧
        fullArenaClauseGarb s_jn cref.toNat = false ∧
        fullArenaClauseSize s_jn cref.toNat = sz.toNat ∧
        (fullArenaClauseLits s_jn cref.toNat).Perm lits2 ∧
        s_jn.core.confl_type = 0#64 ∧
        (∀ k < (i + 1#32).toNat,
          s_jn.core.vals[(tmp5[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
        (FullMem c s_jn ⋆ R) m) → J_jn xs m)
    (hsp_as : FullSparseInvW c F0 F_cur s_as)
    (hcvp : sp.core.cur_vars = s5.core.cur_vars)
    (hcv_as : s_as.core.cur_vars = sp.core.cur_vars)
    (halp : sp.core.arena_len = s5.core.arena_len)
    (hal_as : s_as.core.arena_len = sp.core.arena_len)
    (hprp : sp.core.probing = s5.core.probing)
    (hpr_as : s_as.core.probing = sp.core.probing)
    (hflp : sp.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hfl_as : s_as.core.fuel = sp.core.fuel)
    (hal5 : s5.core.arena_len = s.core.arena_len)
    (hrefsp : fullArenaClauseRefs sp = fullArenaClauseRefs s)
    (hrefs_as : fullArenaClauseRefs s_as = fullArenaClauseRefs sp)
    (hrr_as : s_as.scratch.red_refs = s.scratch.red_refs)
    (hrefp : cref.toNat ∈ fullArenaClauseRefs sp)
    (hng_as : fullArenaClauseGarb s_as cref.toNat = false)
    (hsz_as : fullArenaClauseSize s_as cref.toNat = sz.toNat)
    (hpermp : (fullArenaClauseLits sp cref.toNat).Perm lits2)
    (hlits_as : fullArenaClauseLits s_as cref.toNat = fullArenaClauseLits sp cref.toNat)
    (hct_as : s_as.core.confl_type = 0#64)
    (htmp_as : s_as.core.tmp = tmp5)
    (hlits2_lt : ∀ l ∈ lits2, l < 2 * s5.core.cur_vars)
    (hlits2_mem : ∀ k < sz.toNat, (tmp5[k]?.getD 0#32).toNat ∈ lits2)
    (hi_lt : i.toNat < sz.toNat)
    (hlit_eq : lit = tmp5[i.toNat]?.getD 0#32)
    (hlit_lt : lit.toNat < 2 * sp.core.cur_vars)
    (hfalp : ∀ k < i.toNat, sp.core.vals[(tmp5[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8)
    (hfal_as : ∀ l < 2 * sp.core.cur_vars,
      sp.core.vals[l]?.getD 0#8 = 0xFF#8 → s_as.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hlit_as_ff : s_as.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8)
    (hm_as : (FullMem c s_as ⋆ R) m_as) :
    wp Γ Q X
      (Expr.call (as := [i64, i64]) (bs := [i64]) "full_propagate_ignore"
        (Arg.var c.hdr, Arg.var (cref.setWidth 64), ()) fun p =>
        Expr.let_
          { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
            args := (Arg.var p.fst, Arg.imm 2, ()) }
          fun p_1 =>
        Expr.jnz (Arg.var p_1.fst)
          (Expr.call (as := [i64, i64]) (bs := []) "full_backtrack"
            (Arg.var c.hdr, Arg.imm 0, ()) fun _ =>
            Expr.ret (Arg.imm 2, ()))
          (Expr.let_
            { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
              args := (Arg.var p.fst, Arg.imm 1, ()) }
            fun p =>
            Expr.jnz (Arg.var p.fst)
              (Expr.jump B (Arg.var i, Arg.imm true, Arg.imm 4294967295, ()))
              (Expr.jump J_jn (Arg.imm false, ()))))
      m_as := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  c0_call hPropIgn
  refine ⟨c, F0, F_cur, s_as, R, rfl, hsp_as.1, hsp_as.2.1, hsp_as.2.2.2.2.2, hm_as,
    fun pr vals_p flags_p lvl_p rsns_p trl_p tp_p te_p prop_p unass_p unfl_p
      wvec_p arena_p wstk_p wlen_p wu_p fuel_p ctype_p cref_p c0_p c1_p oom_p
      ticks_p wsort_p phases_p m_p hlen_p hw_p htr_p hperm_p hfl_p hpr_disj hpr0 hpr1 _ _ hm_p =>
      ?_⟩
  let s_p : FullState :=
    { s_as with
      core := { s_as.core with
        vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p,
        trl := trl_p, trail_pos := tp_p, trail_end := te_p, propagated := prop_p,
        unassigned := unass_p, unflushed := unfl_p, wvec := wvec_p,
        arena := arena_p, wstk := wstk_p, wlen := wlen_p, wusable := wu_p,
        fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
        confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
      scratch := { s_as.scratch with
        search_ticks := ticks_p, wsort := wsort_p, phases := phases_p } }
  have hsp_p : FullSparseInvW c F0 F_cur s_p :=
    m4_sparseInvW_of_prop_canon hsp_as hlen_p hw_p hperm_p
  have hrefs_p : fullArenaClauseRefs s_p = fullArenaClauseRefs s_as := hperm_p.2.1
  have hcv_p : s_p.core.cur_vars = s5.core.cur_vars := hcv_as.trans hcvp
  have hal_p : s_p.core.arena_len = s5.core.arena_len := hal_as.trans halp
  have hpr_p : s_p.core.probing = s5.core.probing := hpr_as.trans hprp
  have hfl_p' : s_p.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl_p (hfl_as ▸ hflp)
  have hrefs_p' : fullArenaClauseRefs s_p = fullArenaClauseRefs s :=
    hrefs_p.trans (hrefs_as.trans hrefsp)
  have hrr_p : s_p.scratch.red_refs = s.scratch.red_refs := hrr_as
  have href_p : cref.toNat ∈ fullArenaClauseRefs s_p := hrefs_p ▸ hrefs_as ▸ hrefp
  have hprops_p := hperm_p.2.2 cref.toNat (by
    change cref.toNat ∈ fullArenaClauseRefs s_as; rw [hrefs_as]; exact hrefp)
  have hng_p : fullArenaClauseGarb s_p cref.toNat = false := hprops_p.2.1.trans hng_as
  have hsz_p : fullArenaClauseSize s_p cref.toNat = sz.toNat := hprops_p.1.trans hsz_as
  have hlits_p : (fullArenaClauseLits s_p cref.toNat).Perm lits2 :=
    hprops_p.2.2.trans (by
      change (fullArenaClauseLits s_as cref.toNat).Perm lits2; rw [hlits_as]; exact hpermp)
  have hm_p' : (FullMem c s_p ⋆ R) m_p := hm_p
  have hcv_p_as : s_p.core.cur_vars = s_as.core.cur_vars := rfl
  have htmp_p : s_p.core.tmp = tmp5 := htmp_as
  have hte_p' : s_as.core.trail_end ≤ s_p.core.trail_end := htr_p.1
  have htrl_p' : ∀ idx < s_as.core.trail_end, s_p.core.trl[idx]? = s_as.core.trl[idx]? := htr_p.2.1
  have hcok_p_fn : pr = 1#64 → FullConflictOkW F_cur s_p := fun h => (hpr1 h).2.2.1
  have hct_p0_fn : pr = 0#64 → s_p.core.confl_type = 0#64 := fun h => (hpr0 h).2.1.trans hct_as
  clear_value s_p; clear hm_p hm_as hprops_p hperm_p htr_p
  fvt_steps
  · have hpr_eq2 : pr = 2#64 := by c0_bound
    have hp_cl_lt : s_p.core.cur_level < 2 ^ 64 := by
      have := hsp_p.2.1.cur_level_le; have := hsp_p.1.core_ok.trail_end_le
      have := hsp_p.1.core_ok.cur_vars_le; omega
    c0_call hBacktrack
    refine ⟨c, s_p, R, rfl, hsp_p.1, hp_cl_lt,
      (by have h0n : BitVec.toNat (0 : BitVec 64) = 0 := rfl; rw [h0n]; intro;
          have := hsp_p.2.1.cur_level_le; have := hsp_p.1.core_ok.trail_end_le
          have := hsp_p.1.core_ok.cur_vars_le; omega),
      hsp_p.2.1.trail_lits_lt, hm_p',
      fun vals_b lvl_b rsns_b trl_b tp_b te_b prop_b cl_b unass_b sc_b m_b
        hlen_b _ _ _ hpres_b hsc_b _ _ hw_b _ hm_b => ?_⟩
    have hsp_b : FullSparseInvW c F0 F_cur _ :=
      FullVivTop.FullSparseInvW.of_backtrack hsp_p (Nat.zero_le _) hlen_b hpres_b
        (hw_b F0 F_cur hsp_p.2.1 (Nat.zero_le _))
    rcases hsc_b with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
    fvt_steps
    exact hQ 2#64 _ m_b hsp_b hfl_p' (hal_p.trans hal5) hrefs_p' hrr_p
      (Or.inr (Or.inl rfl)) (fun h => by cases h) hm_b
  · have hpr_eq1 : pr = 1#64 := by c0_bound
    fvt_steps
    exact hB (i, true, 0xFFFFFFFF#32, ()) _ ⟨s_p, hsp_p, hcv_p, hal_p, hpr_p,
      hfl_p', hrefs_p', hrr_p, href_p, hng_p, hsz_p, Or.inl rfl, fun _ => hcok_p_fn hpr_eq1,
      (fun h => by cases h), (fun h => by cases h), hm_p'⟩
  · have hpr_eq0 : pr = 0#64 := by
      rcases hpr_disj with rfl | rfl | rfl
      · rfl
      · exact absurd rfl (by c0_bound)
      · exact absurd rfl (by c0_bound)
    have hct_p0 : s_p.core.confl_type = 0#64 := hct_p0_fn hpr_eq0
    have hi1_nat : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
    have hfal_p1 : ∀ k < (i + 1#32).toNat,
        s_p.core.vals[(tmp5[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 := by
      intro k hk; rw [hi1_nat] at hk
      rcases (by omega : k < i.toNat ∨ k = i.toNat) with hk' | rfl
      · have hk_lt_sp : (tmp5[k]?.getD 0#32).toNat < 2 * sp.core.cur_vars := by
          rw [hcvp]; exact hlits2_lt _ (hlits2_mem k (by omega))
        exact falsified_preserved_of_trailExt hsp_as.2.1 hsp_p.2.1 hcv_p_as hte_p' htrl_p'
          (hcv_as ▸ hk_lt_sp) (hfal_as _ hk_lt_sp (hfalp k hk'))
      · rw [← hlit_eq]
        exact falsified_preserved_of_trailExt hsp_as.2.1 hsp_p.2.1 hcv_p_as hte_p' htrl_p'
          (hcv_as ▸ hlit_lt) hlit_as_ff
    fvt_steps
    exact hJ_jn _ _ ⟨s_p, hsp_p, hcv_p, hal_p, hpr_p, htmp_p, hfl_p', hrefs_p', hrr_p,
      href_p, hng_p, hsz_p, hlits_p, hct_p0, hfal_p1, hm_p'⟩

theorem full_viv_finish_m4_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hDeduce : ∀ a m Q X, Full.fullVivDeduceSpec a m Q X →
      Γ "full_viv_deduce" [i64, i32, i32, i64] [i32] a m Q X)
    (hCommit : ∀ a m Q X, fullVivCommitM4Spec a m Q X →
      Γ "full_viv_commit" [i64, i32, i64, i32, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullVivFinishM4Spec a m Q X → Func.wp Γ full_viv_finish_m4_body a m Q X := by
  rintro ⟨h, cref, sz, confl, implied, all_done, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hsp0, hsz_le, href0, hng0, hsz0, hcok0, himpl0, hfal0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  unfold Func.wp full_viv_finish_m4_body
  fvt_to_group
  let sb1 : FullState := { s with scratch := { s.scratch with res_sz := 0#64 } }
  have hspb1 : FullSparseInvW c F0 F_cur sb1 := FullVivTop.FullSparseInvW.with_res_sz hsp0 0#64
  refine wp_join_group (ts := [i32])
    (fun (olen, ()) md => ∃ sd : FullState,
      FullSparseInvW c F0 F_cur sd ∧ sd.core.cur_vars = s.core.cur_vars ∧
      sd.core.arena_len = s.core.arena_len ∧ sd.core.fuel = s.core.fuel ∧
      fullArenaClauseRefs sd = fullArenaClauseRefs s ∧ sd.scratch.red_refs = s.scratch.red_refs ∧
      cref.toNat ∈ fullArenaClauseRefs sd ∧ fullArenaClauseGarb sd cref.toNat = false ∧
      fullArenaClauseSize sd cref.toNat = sz.toNat ∧ olen.toNat ≤ c.max_vars ∧
      (olen.toNat < sz.toNat →
        (∀ k < olen.toNat,
          (sd.scratch.work_stk2[k]?.getD 0#32).toNat < 2 * sd.core.cur_vars) ∧
        ((sd.scratch.work_stk2.take olen.toNat).map fun x => x.toNat / 2).Nodup ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((sd.scratch.work_stk2.take olen.toNat).map BitVec.toNat))) ∧
      (FullMem c sd ⋆ R) md) ?_ ?_
  · rintro _ ⟨olen, ⟨⟩⟩ md
      ⟨sd, hspd, hcvd, hald, hfld, hrefsd, hrrd, hrefd, hngd, hszd, hol_le, hol_ok, hmd⟩
    have hd_cl_le : sd.core.cur_level ≤ c.max_vars := by
      have := hspd.2.1.cur_level_le; have := hspd.1.core_ok.trail_end_le
      have := hspd.1.core_ok.cur_vars_le; omega
    have hd_cl_lt : sd.core.cur_level < 2 ^ 64 := by omega
    fvt_to_group
    · -- `olen < sz`: backtrack to 0 if needed, then `full_viv_commit`
      have hol_lt : olen.toNat < sz.toNat := by c0_bound
      obtain ⟨hws_lt, hws_nd, hws_ent⟩ := hol_ok hol_lt
      refine wp_join_group (ts := [])
        (fun () m_bt => ∃ s_bt : FullState,
          FullSparseInvW c F0 F_cur s_bt ∧ s_bt.core.cur_level = 0 ∧
          s_bt.core.cur_vars = sd.core.cur_vars ∧ s_bt.core.arena_len = sd.core.arena_len ∧
          s_bt.core.fuel = sd.core.fuel ∧ fullArenaClauseRefs s_bt = fullArenaClauseRefs sd ∧
          s_bt.scratch.red_refs = s.scratch.red_refs ∧
          cref.toNat ∈ fullArenaClauseRefs s_bt ∧ fullArenaClauseGarb s_bt cref.toNat = false ∧
          fullArenaClauseSize s_bt cref.toNat = sz.toNat ∧
          s_bt.scratch.work_stk2 = sd.scratch.work_stk2 ∧ (FullMem c s_bt ⋆ R) m_bt) ?_ ?_
      · rintro _ ⟨⟩ m_bt ⟨s_bt, hsp_bt, hcl_bt0, hcv_bt, hal_bt, hfl_bt, hrefs_bt, hrr_bt,
          href_bt, hng_bt, hsz_bt, hws2_bt, hm_bt⟩
        fvt_steps
        c0_call hCommit
        refine ⟨c, F0, F_cur, s_bt, R, rfl, rfl, hsp_bt, hcl_bt0, href_bt, hng_bt, hol_le,
          fun _ => ⟨by simpa [hws2_bt, hcv_bt] using hws_lt,
                    by simpa [hws2_bt] using hws_nd,
                    by simpa [hws2_bt] using hws_ent⟩,
          hm_bt, fun r_c s_cm m_cm hspc _ _ halc _ hflc hrefsc hrrc hrc h20c hm_cm => ?_⟩
        exact hQ r_c s_cm m_cm hspc (hflc.trans (hfl_bt.trans hfld))
          (halc.trans (hal_bt.trans hald)) (hrefsc.trans (hrefs_bt.trans hrefsd))
          (hrrc.trans hrr_bt) hrc h20c hm_cm
      · intro Jbt hJbt
        fvt_steps
        · c0_call hBacktrack
          refine ⟨c, sd, R, rfl, hspd.1, hd_cl_lt,
            (by have h0n : BitVec.toNat (0 : BitVec 64) = 0 := rfl; rw [h0n]; intro; omega),
            hspd.2.1.trail_lits_lt, hmd,
            fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
              hlen_bt _ _ hcl_bt hpres_bt hsc_bt _ _ hw_bt _ hm_bt => ?_⟩
          have hsp_bt : FullSparseInvW c F0 F_cur _ :=
            FullVivTop.FullSparseInvW.of_backtrack hspd (Nat.zero_le _) hlen_bt hpres_bt
              (hw_bt F0 F_cur hspd.2.1 (Nat.zero_le _))
          rcases hsc_bt with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
          exact hJbt () m_bt ⟨_, hsp_bt, by rw [hcl_bt]; simp, rfl, rfl, rfl, rfl,
            hrrd, hrefd, hngd, hszd, rfl, hm_bt⟩
        · have hcl0_d : sd.core.cur_level = 0 := by
            have h0 : (BitVec.ofNat 64 sd.core.cur_level).toNat = 0 := by rw [hc]; rfl
            rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd_cl_lt] at h0
          exact hJbt () md ⟨sd, hspd, hcl0_d, rfl, rfl, rfl, rfl, hrrd, hrefd, hngd,
            hszd, rfl, hmd⟩
    · -- `¬ (olen < sz)`: unwind 1 level on conflict, re-establish 2WL on `cref`, return 1
      refine wp_join_group (ts := [])
        (fun () mr => ∃ sr : FullState,
          FullSparseInvW c F0 F_cur sr ∧ sr.core.arena_len = s.core.arena_len ∧
          sr.core.fuel = s.core.fuel ∧ fullArenaClauseRefs sr = fullArenaClauseRefs s ∧
          sr.scratch.red_refs = s.scratch.red_refs ∧ cref.toNat ∈ fullArenaClauseRefs sr ∧
          fullArenaClauseGarb sr cref.toNat = false ∧ (FullMem c sr ⋆ R) mr) ?_ ?_
      · rintro _ ⟨⟩ mr ⟨sr, hspr, halr, hflr, hrefsr, hrrr, hrefr, hngr, hmr⟩
        have hr_cl_le : sr.core.cur_level ≤ c.max_vars := by
          have := hspr.2.1.cur_level_le; have := hspr.1.core_ok.trail_end_le
          have := hspr.1.core_ok.cur_vars_le; omega
        have hr_cl_lt : sr.core.cur_level < 2 ^ 64 := by omega
        refine wp_join_group (ts := [])
          (fun () mf => ∃ sf : FullState,
            FullSparseInvW c F0 F_cur sf ∧ sf.core.arena_len = s.core.arena_len ∧
            sf.core.fuel = s.core.fuel ∧ fullArenaClauseRefs sf = fullArenaClauseRefs s ∧
            sf.scratch.red_refs = s.scratch.red_refs ∧ (FullMem c sf ⋆ R) mf) ?_ ?_
        · rintro _ ⟨⟩ mf ⟨sf, hspf, half, hflf, hrefsf, hrrf, hmf⟩
          fvt_steps
          exact hQ 1#64 sf mf hspf hflf half hrefsf hrrf (Or.inl rfl) (fun h => by cases h) hmf
        · intro Jrw hJrw
          fvt_steps
          · have hwf_r := hspr.2.1.arena.refs_wf cref.toNat hrefr
            have hcl_r := hspr.1.core_ok
            have har_cap := c.harena; unfold dimacsBound at har_cap
            have hcr3_nat : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3 := by bv_omega
            have hcr4_nat : (cref.setWidth 64 + 4#64).toNat = cref.toNat + 4 := by bv_omega
            have hcr3_lt : cref.toNat + 3 < sr.core.arena.length := by
              have := hcl_r.arena_len_arr; have := hcl_r.arena_len_le; omega
            have hcr4_lt : cref.toNat + 4 < sr.core.arena.length := by
              have := hcl_r.arena_len_arr; have := hcl_r.arena_len_le; omega
            have hcr3_bv : (cref.setWidth 64 + 3#64).toNat < sr.core.arena.length := by omega
            have hcr4_bv : (cref.setWidth 64 + 4#64).toNat < sr.core.arena.length := by omega
            let l0 := sr.core.arena[(cref.setWidth 64 + 3#64).toNat]'hcr3_bv
            let l1 := sr.core.arena[(cref.setWidth 64 + 4#64).toNat]'hcr4_bv
            have hsz3_r : 3 ≤ fullArenaClauseSizeCore sr.core cref.toNat := hwf_r.2.1
            have hbd_r : cref.toNat + 3 + fullArenaClauseSizeCore sr.core cref.toNat ≤
                sr.core.arena.length := by
              have := hwf_r.2.2.1; have := hwf_r.2.2.2.1
              have := hcl_r.arena_len_arr; have := hcl_r.arena_len_le; omega
            have hl0_mem : l0.toNat ∈ fullArenaClauseLits sr cref.toNat := by
              unfold fullArenaClauseLits fullArenaClauseLitsCore
              rw [List.mem_map]
              refine ⟨l0, ?_, rfl⟩
              rw [List.mem_iff_getElem]
              refine ⟨0, by simp [List.length_take, List.length_drop]; omega, ?_⟩
              simp only [List.getElem_take, List.getElem_drop, Nat.add_zero, l0, hcr3_nat]
            have hl1_mem : l1.toNat ∈ fullArenaClauseLits sr cref.toNat := by
              unfold fullArenaClauseLits fullArenaClauseLitsCore
              rw [List.mem_map]
              refine ⟨l1, ?_, rfl⟩
              rw [List.mem_iff_getElem]
              refine ⟨1, by simp [List.length_take, List.length_drop]; omega, ?_⟩
              simp only [List.getElem_take, List.getElem_drop, l1, hcr4_nat]
            have hl0_lt : l0.toNat < 2 * sr.core.cur_vars :=
              hspr.2.1.arena.lits_lt cref.toNat hrefr hngr l0.toNat hl0_mem
            have hl1_lt : l1.toNat < 2 * sr.core.cur_vars :=
              hspr.2.1.arena.lits_lt cref.toNat hrefr hngr l1.toNat hl1_mem
            have hl0_vals : (l0.setWidth 64).toNat < sr.core.vals.length := by
              rw [bv32_setWidth64_toNat, hcl_r.vals_len]; have := hcl_r.cur_vars_le; omega
            have hl1_vals : (l1.setWidth 64).toNat < sr.core.vals.length := by
              rw [bv32_setWidth64_toNat, hcl_r.vals_len]; have := hcl_r.cur_vars_le; omega
            have hl0_lvl : ((l0 >>> (1 : BitVec 32)).setWidth 64).toNat < sr.core.lvl.length := by
              rw [bv32_setWidth64_toNat, hcl_r.lvl_len]
              have : (l0 >>> (1 : BitVec 32)).toNat = l0.toNat / 2 := by
                change (l0 >>> (1 : Nat)).toNat = l0.toNat / 2
                rw [BitVec.toNat_ushiftRight]; simp [Nat.shiftRight_eq_div_pow]
              have := hcl_r.cur_vars_le; omega
            have hl1_lvl : ((l1 >>> (1 : BitVec 32)).setWidth 64).toNat < sr.core.lvl.length := by
              rw [bv32_setWidth64_toNat, hcl_r.lvl_len]
              have : (l1 >>> (1 : BitVec 32)).toNat = l1.toNat / 2 := by
                change (l1 >>> (1 : Nat)).toNat = l1.toNat / 2
                rw [BitVec.toNat_ushiftRight]; simp [Nat.shiftRight_eq_div_pow]
              have := hcl_r.cur_vars_le; omega
            fvt_to_group
            refine wp_join_group (ts := [i64]) (fun _ m1 => m1 = mr) ?_ ?_
            · rintro _ ⟨lvl0, ⟨⟩⟩ m1 hm1; subst m1
              fvt_to_group
              refine wp_join_group (ts := [i64]) (fun _ m2 => m2 = mr) ?_ ?_
              · rintro _ ⟨lvl1, ⟨⟩⟩ m2 hm2; subst m2
                fvt_to_group
                refine wp_join_group (ts := [i64]) (fun _ m3 => m3 = mr) ?_ ?_
                · rintro _ ⟨new_lvl, ⟨⟩⟩ m3 hm3; subst m3
                  fvt_steps
                  · have hnl_lt : (new_lvl - 1#64).toNat < sr.core.cur_level := by
                      have hlt_bv : (new_lvl - 1#64).toNat <
                          (BitVec.ofNat 64 sr.core.cur_level).toNat := by c0_bound
                      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_cl_lt] at hlt_bv
                    have hnl_le : (new_lvl - 1#64).toNat ≤ sr.core.cur_level := Nat.le_of_lt hnl_lt
                    c0_call hBacktrack
                    refine ⟨c, sr, R, rfl, hspr.1, hr_cl_lt,
                      fun _ => Nat.lt_of_lt_of_le hnl_lt hr_cl_le,
                      hspr.2.1.trail_lits_lt, hmr,
                      fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
                        hlen_bt _ _ _ hpres_bt hsc_bt _ _ hw_bt _ hm_bt => ?_⟩
                    have hsp_bt : FullSparseInvW c F0 F_cur _ :=
                      FullVivTop.FullSparseInvW.of_backtrack hspr hnl_le hlen_bt
                        hpres_bt (hw_bt F0 F_cur hspr.2.1 hnl_le)
                    rcases hsc_bt with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
                    dsimp only; apply hJ; fvt_steps
                    exact hJrw () m_bt ⟨_, hsp_bt, halr, hflr, hrefsr, hrrr, hm_bt⟩
                  · exact hJrw () mr ⟨sr, hspr, halr, hflr, hrefsr, hrrr, hmr⟩
                  · exact hJrw () mr ⟨sr, hspr, halr, hflr, hrefsr, hrrr, hmr⟩
                · intro Jnl hJnl
                  fvt_steps <;> exact hJnl _ mr rfl
              · intro Jl1 hJl1; fvt_steps <;> exact hJl1 _ mr rfl
            · intro Jl0 hJl0; fvt_steps <;> exact hJl0 _ mr rfl
          · exact hJrw () mr ⟨sr, hspr, halr, hflr, hrefsr, hrrr, hmr⟩
      · intro Jcf hJcf
        fvt_steps
        · have hpos : 0 < sd.core.cur_level := by
            have hc0 : 0 < (BitVec.ofNat 64 sd.core.cur_level).toNat := by c0_bound
            rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd_cl_lt] at hc0
          have htgt_nat : (BitVec.ofNat 64 sd.core.cur_level - 1).toNat =
              sd.core.cur_level - 1 := by
            have hsd_bv : (BitVec.ofNat 64 sd.core.cur_level).toNat = sd.core.cur_level := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd_cl_lt]
            have h1 : (1 : BitVec 64).toNat = 1 := rfl
            rw [BitVec.toNat_sub, hsd_bv, h1]; omega
          c0_call hBacktrack
          refine ⟨c, sd, R, rfl, hspd.1, hd_cl_lt, fun _ => by rw [htgt_nat]; omega,
            hspd.2.1.trail_lits_lt, hmd,
            fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
              hlen_bt _ _ _ hpres_bt hsc_bt _ _ hw_bt _ hm_bt => ?_⟩
          have hle_bt : (BitVec.ofNat 64 sd.core.cur_level - 1).toNat ≤ sd.core.cur_level :=
            by rw [htgt_nat]; omega
          have hsp_bt : FullSparseInvW c F0 F_cur _ :=
            FullVivTop.FullSparseInvW.of_backtrack hspd hle_bt hlen_bt
              hpres_bt (hw_bt F0 F_cur hspd.2.1 hle_bt)
          rcases hsc_bt with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
          exact hJcf () m_bt ⟨_, hsp_bt, hald, hfld, hrefsd, hrrd, hrefd, hngd, hm_bt⟩
        · exact hJcf () md ⟨sd, hspd, hald, hfld, hrefsd, hrrd, hrefd, hngd, hmd⟩
        · exact hJcf () md ⟨sd, hspd, hald, hfld, hrefsd, hrrd, hrefd, hngd, hmd⟩
  · -- `if (confl || implied != 0xFFFFFFFFu || all_done)` entry
    intro Jif hJif
    fvt_steps
    all_goals try
      have hct : confl = true := by assumption
      have hcf : confl = false := by assumption
      exact absurd (hct.symm.trans hcf) (by decide)
    · have hcfl_t : confl = true := by first | assumption | c0_bound
      c0_call hDeduce
      refine ⟨c, F0, F_cur, sb1, R, rfl, rfl, hspb1, href0, hng0,
        fun _ => Or.inl (hcok0 hcfl_t), fun h => absurd rfl h, hm,
        fun olen mrk' ws1' ws2' rsz' md hspd hol_le hol_ok hmd => ?_⟩
      exact hJif (olen, ()) md ⟨_, hspd, rfl, rfl, rfl, rfl, rfl, href0, hng0, hsz0, hol_le,
        fun h => hol_ok (by rw [hsz0]; exact h), hmd⟩
    · have hcfl_f : confl = false := by first | assumption | c0_bound
      have himpl_ne : implied ≠ 0xFFFFFFFF#32 := by first | assumption | c0_bound
      obtain ⟨him_lt, him_val⟩ := himpl0 hcfl_f himpl_ne
      c0_call hDeduce
      refine ⟨c, F0, F_cur, sb1, R, rfl, rfl, hspb1, href0, hng0,
        fun h => absurd h himpl_ne, fun _ => ⟨him_lt, him_val⟩, hm,
        fun olen mrk' ws1' ws2' rsz' md hspd hol_le hol_ok hmd => ?_⟩
      exact hJif (olen, ()) md ⟨_, hspd, rfl, rfl, rfl, rfl, rfl, href0, hng0, hsz0, hol_le,
        fun h => hol_ok (by rw [hsz0]; exact h), hmd⟩
    · have hcfl_f : confl = false := by first | assumption | c0_bound
      have himpl_eq : implied = 0xFFFFFFFF#32 := by first | assumption | c0_bound
      have hall_t : all_done = true := by first | assumption | c0_bound
      obtain ⟨hct0, hfal⟩ := hfal0 hcfl_f himpl_eq hall_t
      c0_call hDeduce
      refine ⟨c, F0, F_cur, sb1, R, rfl, rfl, hspb1, href0, hng0,
        fun _ => Or.inr ⟨hct0, hfal⟩, fun h => absurd himpl_eq h, hm,
        fun olen mrk' ws1' ws2' rsz' md hspd hol_le hol_ok hmd => ?_⟩
      exact hJif (olen, ()) md ⟨_, hspd, rfl, rfl, rfl, rfl, rfl, href0, hng0, hsz0, hol_le,
        fun h => hol_ok (by rw [hsz0]; exact h), hmd⟩
    · exact hJif (sz, ()) _ ⟨sb1, hspb1, rfl, rfl, rfl, rfl, rfl, href0, hng0, hsz0, hsz_le,
        fun h => absurd h (Nat.lt_irrefl _), hm⟩

theorem full_viv_clause_m4_wp (Γ : Env)
    (hL0Simp : ∀ a m Q X, fullVivL0SimpM4Spec a m Q X →
      Γ "full_viv_l0_simp_m4" [i64, i32, i32] [i64] a m Q X)
    (hSort : ∀ a m Q X, fullVivSortNoccsM4Spec a m Q X →
      Γ "full_viv_sort_noccs_m4" [i64, i32] [] a m Q X)
    (hReuse : ∀ a m Q X, fullVivReusePrefixM4Spec a m Q X →
      Γ "full_viv_reuse_prefix_m4" [i64, i32, i32] [] a m Q X)
    (hAssign : ∀ a m Q X, Full.fullAssignSpec a m Q X →
      Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hPropIgn : ∀ a m Q X, Full.fullPropagateIgnoreSpec a m Q X →
      Γ "full_propagate_ignore" [i64, i64] [i64] a m Q X)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hFinish : ∀ a m Q X, fullVivFinishM4Spec a m Q X →
      Γ "full_viv_finish_m4" [i64, i32, i32, .bool, i32, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullVivClauseM4Spec a m Q X → Func.wp Γ full_viv_clause_m4_body a m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hsp0, href0, hm0, hQ⟩
  have hmx := c.hmaxv; have har_cap := c.harena; unfold dimacsBound at hmx har_cap
  have hwf0 := hsp0.2.1.arena.refs_wf cref.toNat href0
  have hcl0 := hsp0.1.core_ok
  have hcr0_nat : (cref.setWidth 64).toNat = cref.toNat := bv32_setWidth64_toNat cref
  have hcr0_lt0 : cref.toNat < s.core.arena.length := by
    have := hcl0.arena_len_arr; have := hcl0.arena_len_le; omega
  have hcr0_bv0 : (cref.setWidth 64).toNat < s.core.arena.length := by omega
  have hcr2_nat : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2 := by bv_omega
  have hcr2_lt0 : cref.toNat + 2 < s.core.arena.length := by
    have := hcl0.arena_len_arr; have := hcl0.arena_len_le; omega
  have hcr2_bv0 : (cref.setWidth 64 + 2#64).toNat < s.core.arena.length := by omega
  unfold Func.wp full_viv_clause_m4_body
  fvt_steps
  · exact hQ 1#64 s m0 hsp0 (Nat.le_refl _) rfl rfl rfl (Or.inl rfl) (fun h => by cases h) hm0
  · exact hQ 1#64 s m0 hsp0 (Nat.le_refl _) rfl rfl rfl (Or.inl rfl) (fun h => by cases h) hm0
  · exact hQ 1#64 s m0 hsp0 (Nat.le_refl _) rfl rfl rfl (Or.inl rfl) (fun h => by cases h) hm0
  · have hgb_eq : (s.core.arena[(cref.setWidth 64).toNat]'hcr0_bv0 &&& 0x00080000#32) = 0#32 := by
      c0_bound
    have hng0 : fullArenaClauseGarb s cref.toNat = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
      have hg : s.core.arena[cref.toNat]? =
          some (s.core.arena[(cref.setWidth 64).toNat]'hcr0_bv0) := by
        rw [← hcr0_nat, List.getElem?_eq_getElem hcr0_bv0]
      rw [hg, Option.getD_some, hgb_eq]; rfl
    let sz0 := s.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_bv0
    have hsz0_eq : sz0 = s.core.arena[cref.toNat + 2]'hcr2_lt0 :=
      Option.some.inj (by
        rw [← List.getElem?_eq_getElem hcr2_bv0, hcr2_nat, List.getElem?_eq_getElem hcr2_lt0])
    have hsz0_nat : sz0.toNat = fullArenaClauseSize s cref.toNat := by
      rw [hsz0_eq]; unfold fullArenaClauseSize fullArenaClauseSizeCore
      rw [List.getElem?_eq_getElem hcr2_lt0, Option.getD_some]
    c0_call hL0Simp
    refine ⟨c, F0, F_cur, s, R, rfl, hsp0, href0, hng0, hsz0_nat, hm0,
      fun l0r s1 m1 hsp1 hfl1_eq hal1 hrefs1 hrr1 hl0r h20_1 h0_1 hm1 => ?_⟩
    have hfl1 : s1.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hfl1_eq]; exact Nat.le_refl _
    by_cases hl0 : l0r ≠ 0#64
    · rcases hl0r with rfl | rfl | rfl
      · exact absurd rfl hl0
      · fvt_steps
        exact hQ 1#64 s1 m1 hsp1 hfl1 hal1 hrefs1 hrr1 (Or.inl rfl) (fun h => by cases h) hm1
      · fvt_steps
        exact hQ 20#64 s1 m1 hsp1 hfl1 hal1 hrefs1 hrr1 (Or.inr (Or.inr rfl))
          (fun _ => h20_1 rfl) hm1
    obtain rfl : l0r = 0#64 := Classical.not_not.mp hl0
    fvt_steps
    · contradiction
    obtain ⟨href1, hng1⟩ := h0_1 rfl
    have hwf1 := hsp1.2.1.arena.refs_wf cref.toNat href1
    have hcl1 := hsp1.1.core_ok
    have hcr2_lt1 : cref.toNat + 2 < s1.core.arena.length := by
      have := hcl1.arena_len_arr; have := hcl1.arena_len_le; omega
    have hcr2_bv1 : (cref.setWidth 64 + 2#64).toNat < s1.core.arena.length := by omega
    fvt_steps
    · exact hQ 1#64 s1 m1 hsp1 hfl1 hal1 hrefs1 hrr1 (Or.inl rfl) (fun h => by cases h) hm1
    · exact hQ 1#64 s1 m1 hsp1 hfl1 hal1 hrefs1 hrr1 (Or.inl rfl) (fun h => by cases h) hm1
    let sz := s1.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_bv1
    have hsz_eq : sz = s1.core.arena[cref.toNat + 2]'hcr2_lt1 :=
      Option.some.inj (by
        rw [← List.getElem?_eq_getElem hcr2_bv1, hcr2_nat, List.getElem?_eq_getElem hcr2_lt1])
    have hsz_nat : sz.toNat = fullArenaClauseSize s1 cref.toNat := by
      rw [hsz_eq]; unfold fullArenaClauseSize fullArenaClauseSizeCore
      rw [List.getElem?_eq_getElem hcr2_lt1, Option.getD_some]
    have hsz_le_cv : sz.toNat ≤ s1.core.cur_vars := by
      have hcv_lt : s1.core.cur_vars < 2 ^ 64 := by have := hcl1.cur_vars_le; omega
      have hc0 : ¬ (BitVec.ofNat 64 s1.core.cur_vars).toNat < (sz.setWidth 64).toNat := by
        c0_bound
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_lt, bv32_setWidth64_toNat] at hc0
      omega
    have hsz_le_mv : sz.toNat ≤ c.max_vars := by have := hcl1.cur_vars_le; omega
    let s2 : FullState := s1
    have hsp2 : FullSparseInvW c F0 F_cur s2 := hsp1
    have hrefs2 : fullArenaClauseRefs s2 = fullArenaClauseRefs s1 := rfl
    have href2 : cref.toNat ∈ fullArenaClauseRefs s2 := href1
    have hng2 : fullArenaClauseGarb s2 cref.toNat = false := hng1
    have hsz2 : fullArenaClauseSize s2 cref.toNat = sz.toNat := hsz_nat.symm
    have har2_len : s2.core.arena.length = c.arena_cap := hsp2.1.core_ok.arena_len_arr
    have htmp2_len : s2.core.tmp.length = c.max_vars := hsp2.1.core_ok.tmp_len_arr
    have hbd2 : cref.toNat + 3 + sz.toNat ≤ s2.core.arena.length := by
      have := hwf1.2.2.1; have := hwf1.2.2.2.1; have := hcl1.arena_len_le
      rw [hsz_nat]
      change cref.toNat + 3 + fullArenaClauseSizeCore s1.core cref.toNat ≤ s2.core.arena.length
      omega
    clear hL0Simp hwf0 hcl0 hcr0_lt0 hgb_eq hfl1_eq h20_1 h0_1
    fvt_steps
    -- Copy `ar[cref + 3 .. cref + 3 + sz)` into `tmp[0 .. sz)`
    refine wp_loop_inv (ts := [i32])
      (fun (i, ()) mc => ∃ tmpc : List (BitVec 32),
        i.toNat ≤ sz.toNat ∧ tmpc.length = c.max_vars ∧
        (∀ k < i.toNat, tmpc[k]? = s2.core.arena[cref.toNat + 3 + k]?) ∧
        (FullMem c { s2 with core := { s2.core with tmp := tmpc } } ⋆ R) mc)
      (fun (i, ()) _ => sz.toNat - i.toNat)
      (fun Jc hJc => by
        fvt_steps
        exact hJc (0#32, ()) _ ⟨s2.core.tmp, Nat.zero_le _, htmp2_len,
          fun _ hk => by simp at hk, hm1⟩)
      (fun Jc ⟨i, ⟨⟩⟩ mc ⟨tmpc, hi_le, htc_len, hcp, hmc⟩ ihc => ?_)
    fvt_steps
    · have hi_lt : i.toNat < sz.toNat := by c0_bound
      have hidx_nat : (cref.setWidth 64 + 3 + i.setWidth 64).toNat =
          cref.toNat + 3 + i.toNat := by bv_omega
      have hi64_nat : (i.setWidth 64).toNat = i.toNat := bv32_setWidth64_toNat i
      have hi_lt_ar :
          (cref.setWidth 64 + 3 + i.setWidth 64).toNat < s2.core.arena.length := by omega
      have hi_lt_tmp : i.toNat < tmpc.length := by omega
      have hi1_nat : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
      fvt_steps
      let tmpc' := tmpc.set i.toNat (s2.core.arena[cref.toNat + 3 + i.toNat]'(by omega))
      have har_eq :
          s2.core.arena[(cref.setWidth 64 + 3 + i.setWidth 64).toNat]'hi_lt_ar =
            s2.core.arena[cref.toNat + 3 + i.toNat]'(by omega) :=
        Option.some.inj (by
          rw [← List.getElem?_eq_getElem hi_lt_ar, hidx_nat, List.getElem?_eq_getElem (by omega)])
      refine ihc (i + 1#32, ()) _ (by dsimp only; omega)
        ⟨tmpc', by omega, by simp [tmpc', htc_len], fun k hk => ?_, ?_⟩
      · rcases (by omega : k < i.toNat ∨ k = i.toNat) with hk' | rfl
        · dsimp only [tmpc']; rw [List.getElem?_set_ne (by omega)]; exact hcp k hk'
        · dsimp only [tmpc']
          rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
      · simpa only [tmpc', hi64_nat, har_eq] using hm
    · have hi_eq : i.toNat = sz.toNat := by dsimp only [sz] at hi_le ⊢; c0_bound
      rw [hi_eq] at hcp
      have htmpc_lits_lt : ∀ k < sz.toNat, (tmpc[k]?.getD 0#32).toNat < 2 * c.max_vars := by
        intro k hk
        have hmem : (tmpc[k]?.getD 0#32).toNat ∈ fullArenaClauseLits s2 cref.toNat := by
          have := (vivTmp_mem_of_perm (by omega)
            (vivCopy_perm_lits (by omega) hbd2 hcp
              (List.Perm.refl (tmpc.take sz.toNat)) (by omega))).1 k hk
          simpa [fullArenaClauseLits, fullArenaClauseLitsCore, hsz2] using this
        have := hsp2.2.1.arena.lits_lt cref.toNat href2 hng2 _ hmem
        have := hsp2.1.core_ok.cur_vars_le; omega
      c0_call hSort
      refine ⟨c, { s2 with core := { s2.core with tmp := tmpc } }, R,
        rfl, ⟨{ hsp2.1.core_ok with tmp_len_arr := htc_len }, hsp2.1.scratch_ok⟩,
        hsz_le_mv, htmpc_lits_lt, hmc, fun tmp4 m4 htmp4_len hperm4 _ hm4 => ?_⟩
      have hperm_lits4 : ((tmp4.take sz.toNat).map BitVec.toNat).Perm
          (fullArenaClauseLits s2 cref.toNat) := by
        have := vivCopy_perm_lits (by omega) hbd2 hcp hperm4 (by omega)
        simpa [fullArenaClauseLits, fullArenaClauseLitsCore, hsz2] using this
      let s4 : FullState := { s2 with core := { s2.core with tmp := tmp4 } }
      have hsp4 : FullSparseInvW c F0 F_cur s4 :=
        FullVivTop.FullSparseInvW.with_tmp hsp2 htmp4_len
      have htmp4_lt_cv : ∀ k < sz.toNat, (tmp4[k]?.getD 0#32).toNat < 2 * s4.core.cur_vars := by
        intro k hk
        have hmem := (vivTmp_mem_of_perm (by omega) hperm_lits4).1 k hk
        exact hsp2.2.1.arena.lits_lt cref.toNat href2 hng2 _ hmem
      fvt_steps
      c0_call hReuse
      refine ⟨c, F0, F_cur, s4, R, rfl, hsp4, hsz_le_mv, htmp4_lt_cv, hm4,
        fun s4r m4r hsp4r hcv4r har4r hal4r hpr4r hfl4r htmp4r hrr4r hm4r => ?_⟩
      let tmp5 := s4r.core.tmp
      have hperm_lits5 : ((tmp5.take sz.toNat).map BitVec.toNat).Perm
          (fullArenaClauseLits s2 cref.toNat) := by
        dsimp only [tmp5]; rw [htmp4r]; exact hperm_lits4
      obtain ⟨htmp5_mem, hlits5_inv⟩ := vivTmp_mem_of_perm
        (by rw [show tmp5.length = c.max_vars from hsp4r.1.core_ok.tmp_len_arr]; omega)
        hperm_lits5
      fvt_to_group
      let s5 : FullState :=
        { s4r with core := { s4r.core with confl_type := 0#64, confl_ref := 0xFFFFFFFF#64 } }
      have hsp5 : FullSparseInvW c F0 F_cur s5 :=
        FullVivTop.FullSparseInvW.with_confl hsp4r 0#64 0xFFFFFFFF#64
      have hfl5 : s5.core.fuel.toNat ≤ s.core.fuel.toNat := by
        change s4r.core.fuel.toNat ≤ s.core.fuel.toNat; rw [hfl4r]; exact hfl1
      have hal5 : s5.core.arena_len = s.core.arena_len := hal4r.trans hal1
      have hrefs_eq4r : fullArenaClauseRefs s5 = fullArenaClauseRefs s2 := by
        unfold fullArenaClauseRefs fullArenaClauseRefsCore; change _ = _; rw [har4r, hal4r]
      have hrefs5 : fullArenaClauseRefs s5 = fullArenaClauseRefs s :=
        hrefs_eq4r.trans (hrefs2.trans hrefs1)
      have hrr5 : s5.scratch.red_refs = s.scratch.red_refs := hrr4r.trans hrr1
      have href5 : cref.toNat ∈ fullArenaClauseRefs s5 := hrefs_eq4r ▸ href2
      have hng5 : fullArenaClauseGarb s5 cref.toNat = false := by
        unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
        change (s4r.core.arena[cref.toNat]?.getD 0#32 &&& 0x00080000#32 != 0#32) = false
        rw [har4r]; exact hng2
      have hsz5 : fullArenaClauseSize s5 cref.toNat = sz.toNat := by
        unfold fullArenaClauseSize fullArenaClauseSizeCore
        change (s4r.core.arena[cref.toNat + 2]?.getD 0#32).toNat = sz.toNat
        rw [har4r]; exact hsz2
      let lits2 := fullArenaClauseLits s2 cref.toNat
      have hperm5 : (fullArenaClauseLits s5 cref.toNat).Perm lits2 := by
        have heq : fullArenaClauseLits s5 cref.toNat = lits2 := by
          unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore lits2
          change ((s4r.core.arena.drop (cref.toNat + 3)).take
            (s4r.core.arena[cref.toNat + 2]?.getD 0#32).toNat).map BitVec.toNat = _
          rw [har4r]; rfl
        rw [heq]
      have hlits2_lt : ∀ l ∈ lits2, l < 2 * s5.core.cur_vars := fun l hl => by
        change l < 2 * s4r.core.cur_vars; rw [hcv4r]
        exact hsp2.2.1.arena.lits_lt cref.toNat href2 hng2 l hl
      have hlits2_mem : ∀ k < sz.toNat, (tmp5[k]?.getD 0#32).toNat ∈ lits2 := htmp5_mem
      have hlits2_inv : ∀ l ∈ lits2, ∃ k < sz.toNat, (tmp5[k]?.getD 0#32).toNat = l := hlits5_inv
      have hct5 : s5.core.confl_type = 0#64 := rfl
      have htmp5 : s5.core.tmp = tmp5 := rfl
      have htmp5_len : tmp5.length = c.max_vars := hsp4r.1.core_ok.tmp_len_arr
      have hm5 : (FullMem c s5 ⋆ R) m := hm
      clear_value s5 s4 s2 tmp5 lits2
      clear hm hwf1 hperm4 hperm_lits4 hperm_lits5 htmp5_mem hlits5_inv hsp4 hsp2
        s4 hrefs2 href2 hng2 hsz2 har2_len htmp2_len hbd2 htmpc_lits_lt hsp1
        hfl1 hal1 hrefs1 hrr1 href1 hng1 hcl1 hsz_nat hsz_le_cv hsp0 href0
        hng0 hm0 hsp4r hcv4r har4r hal4r hpr4r hfl4r htmp4r hrr4r hrefs_eq4r htmp4_lt_cv
      try clear hi_eq ihc hmc hcp htc_len hi_le tmpc mc Jc i s2 s4r
      -- Inner assumption-propagation loop `while (i < sz)`
      refine wp_loop_break_group (brkTs := [i32, .bool, i32]) (lpTs := [i32])
        (fun (i, confl, implied, ()) mb => ∃ sb : FullState,
          FullSparseInvW c F0 F_cur sb ∧
          sb.core.cur_vars = s5.core.cur_vars ∧ sb.core.arena_len = s5.core.arena_len ∧
          sb.core.probing = s5.core.probing ∧ sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          fullArenaClauseRefs sb = fullArenaClauseRefs s ∧
          sb.scratch.red_refs = s.scratch.red_refs ∧
          cref.toNat ∈ fullArenaClauseRefs sb ∧
          fullArenaClauseGarb sb cref.toNat = false ∧
          fullArenaClauseSize sb cref.toNat = sz.toNat ∧
          (confl = true ∨ implied ≠ 0xFFFFFFFF#32 ∨ i.toNat = sz.toNat) ∧
          (confl = true → FullConflictOkW F_cur sb) ∧
          (confl = false → implied ≠ 0xFFFFFFFF#32 →
            implied.toNat < 2 * sb.core.cur_vars ∧
            sb.core.vals[implied.toNat]?.getD 0#8 = 1#8) ∧
          (confl = false → implied = 0xFFFFFFFF#32 →
            sb.core.confl_type = 0#64 ∧
            ∀ l ∈ fullArenaClauseLits sb cref.toNat, sb.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
          (FullMem c sb ⋆ R) mb)
        (fun rem (i, ()) mp => ∃ sp : FullState,
          i.toNat ≤ sz.toNat ∧ rem = sz.toNat - i.toNat ∧
          FullSparseInvW c F0 F_cur sp ∧
          sp.core.cur_vars = s5.core.cur_vars ∧ sp.core.arena_len = s5.core.arena_len ∧
          sp.core.probing = s5.core.probing ∧ sp.core.tmp = tmp5 ∧
          sp.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          fullArenaClauseRefs sp = fullArenaClauseRefs s ∧
          sp.scratch.red_refs = s.scratch.red_refs ∧
          cref.toNat ∈ fullArenaClauseRefs sp ∧
          fullArenaClauseGarb sp cref.toNat = false ∧
          fullArenaClauseSize sp cref.toNat = sz.toNat ∧
          (fullArenaClauseLits sp cref.toNat).Perm lits2 ∧
          sp.core.confl_type = 0#64 ∧
          (∀ k < i.toNat, sp.core.vals[(tmp5[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
          (FullMem c sp ⋆ R) mp)
        ?_ ?_ ?_
      · -- After inner loop: delegate to `full_viv_finish_m4`
        rintro _ ⟨i_b, confl_b, impl_b, ⟨⟩⟩ mb
          ⟨sb, hspb, _, halb, _, hflb, hrefsb, hrrb, hrefb, hngb, hszb,
           _, hcokb, himplb, hfalb, hmb⟩
        fvt_steps
        c0_call hFinish
        refine ⟨c, F0, F_cur, sb, R, rfl, hspb, hsz_le_mv, hrefb, hngb, hszb, hcokb, himplb,
          fun hc hi _ => hfalb hc hi, hmb,
          fun r_f s_f m_f hspf hflf half hrefsf hrrf hrf h20f hm_f => ?_⟩
        have href_f : cref.toNat ∈ fullArenaClauseRefs s_f := hrefsf ▸ hrefb
        have hwf_f := hspf.2.1.arena.refs_wf cref.toNat href_f
        have hcr_f_lt : cref.toNat < s_f.core.arena.length := by
          have := hspf.1.core_ok.arena_len_arr; have := hspf.1.core_ok.arena_len_le; omega
        have hcr_f_bv : (cref.setWidth 64).toNat < s_f.core.arena.length := by omega
        fvt_steps
        · let hdr_f := s_f.core.arena[cref.toNat]'hcr_f_lt
          have hhdr_f : fullArenaHdr s_f cref.toNat = hdr_f := by
            unfold fullArenaHdr fullArenaHdrCore
            rw [List.getElem?_eq_getElem hcr_f_lt, Option.getD_some]
          let hdr_v := hdr_f ||| 0x00100000#32
          let s_v : FullState :=
            { s_f with core := { s_f.core with arena := s_f.core.arena.set cref.toNat hdr_v } }
          obtain ⟨(hsp_v : FullSparseInvW c F0 F_cur s_v), hrefs_v, _⟩ :=
            fullArena_setHdr_preserves_sparseW hspf href_f
              (hdr' := hdr_v) (by rw [hhdr_f]; exact bv32_or_viv_garb hdr_f)
              (by rw [hhdr_f]; exact bv32_or_viv_shrk hdr_f)
          have hm_v : (FullMem c s_v ⋆ R) m := by
            simpa only [s_v, hdr_v, hdr_f, hcr0_nat,
              show (1048576 : BitVec 32) = 0x00100000#32 from rfl] using hm
          exact hQ r_f s_v m hsp_v (by change s_f.core.fuel.toNat ≤ _; rw [hflf]; exact hflb)
            (half.trans (halb.trans hal5)) (hrefs_v.trans (hrefsf.trans hrefsb))
            (hrrf.trans hrrb) hrf h20f hm_v
        · exact hQ r_f s_f m_f hspf (by rw [hflf]; exact hflb) (half.trans (halb.trans hal5))
            (hrefsf.trans hrefsb) (hrrf.trans hrrb) hrf h20f hm_f
        · exact hQ r_f s_f m_f hspf (by rw [hflf]; exact hflb) (half.trans (halb.trans hal5))
            (hrefsf.trans hrefsb) (hrrf.trans hrrb) hrf h20f hm_f
      · -- Inner loop body
        intro B L rem ⟨i, ⟨⟩⟩ mp hB hL
          ⟨sp, hi_le, hrem, hspp, hcvp, halp, hprp, htmpp, hflp, hrefsp, hrrp, hrefp, hngp, hszp,
           hpermp, hct0, hfalp, hmp⟩
        clear hSort hReuse hFinish
        fvt_steps
        · have hi_lt : i.toNat < sz.toNat := by c0_bound
          have hsp_len := hspp.1.core_ok
          have hi_lt_tmp : i.toNat < sp.core.tmp.length := by rw [hsp_len.tmp_len_arr]; omega
          have hlit_lt_cv : (tmp5[i.toNat]?.getD 0#32).toNat < 2 * sp.core.cur_vars := by
            rw [hcvp]; exact hlits2_lt _ (hlits2_mem i.toNat hi_lt)
          have hlit_lt_vals : (tmp5[i.toNat]?.getD 0#32).toNat < sp.core.vals.length := by
            rw [hsp_len.vals_len]; have := hsp_len.cur_vars_le; omega
          have hi64_nat : (i.setWidth 64).toNat = i.toNat := bv32_setWidth64_toNat i
          have hi_lt_tmp64 : (i.setWidth 64).toNat < sp.core.tmp.length := by
            rw [hi64_nat]; exact hi_lt_tmp
          have htmp_i_eq : sp.core.tmp[(i.setWidth 64).toNat]'hi_lt_tmp64 =
              tmp5[i.toNat]?.getD 0#32 :=
            Option.some.inj (by
              rw [← List.getElem?_eq_getElem hi_lt_tmp64, htmpp, hi64_nat,
                List.getElem?_eq_getElem (by omega), Option.getD_some])
          have htmp_i_lt' : (sp.core.tmp[(i.setWidth 64).toNat].setWidth 64).toNat <
              sp.core.vals.length := by
            rw [bv32_setWidth64_toNat, htmp_i_eq]; exact hlit_lt_vals
          let lit := sp.core.tmp[i.toNat]'hi_lt_tmp
          have hlit_eq : lit = tmp5[i.toNat]?.getD 0#32 :=
            Option.some.inj (by
              dsimp only [lit]
              rw [← List.getElem?_eq_getElem hi_lt_tmp, htmpp,
                List.getElem?_eq_getElem (by omega), Option.getD_some])
          have hlit_i64 : sp.core.tmp[(i.setWidth 64).toNat]'hi_lt_tmp64 = lit := by
            rw [htmp_i_eq, hlit_eq]
          have hlit_lt : lit.toNat < 2 * sp.core.cur_vars := hlit_eq ▸ hlit_lt_cv
          have hlit_lt_vals' : lit.toNat < sp.core.vals.length := hlit_eq ▸ hlit_lt_vals
          fvt_to_group
          · have hdom := hspp.2.1.vals_domain lit.toNat hlit_lt
            have hlv1 : sp.core.vals[lit.toNat]?.getD 0#8 = 1#8 := by
              rw [List.getElem?_eq_getElem hlit_lt_vals', Option.getD_some]
              exact (bv8_dom_sgt0_iff
                (by simpa [List.getElem?_eq_getElem hlit_lt_vals'] using hdom)).mp (by c0_bound)
            have hcv_le_mx := hsp_len.cur_vars_le
            have hlit_neff : lit ≠ 0xFFFFFFFF#32 := bv32_ne_sentinel_of_lt (by omega)
            rw [hlit_i64]
            exact hB (i, false, lit, ()) _ ⟨sp, hspp, hcvp, halp, hprp, hflp, hrefsp, hrrp,
              hrefp, hngp, hszp, Or.inr (Or.inl hlit_neff), (fun h => by cases h),
              fun _ _ => ⟨hlit_lt, hlv1⟩, fun _ h => absurd h hlit_neff, hmp⟩
          · refine wp_join_group (ts := [.bool])
              (fun (_, ()) m_jn => ∃ s_jn : FullState,
                FullSparseInvW c F0 F_cur s_jn ∧
                s_jn.core.cur_vars = s5.core.cur_vars ∧ s_jn.core.arena_len = s5.core.arena_len ∧
                s_jn.core.probing = s5.core.probing ∧ s_jn.core.tmp = tmp5 ∧
                s_jn.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                fullArenaClauseRefs s_jn = fullArenaClauseRefs s ∧
                s_jn.scratch.red_refs = s.scratch.red_refs ∧
                cref.toNat ∈ fullArenaClauseRefs s_jn ∧
                fullArenaClauseGarb s_jn cref.toNat = false ∧
                fullArenaClauseSize s_jn cref.toNat = sz.toNat ∧
                (fullArenaClauseLits s_jn cref.toNat).Perm lits2 ∧
                s_jn.core.confl_type = 0#64 ∧
                (∀ k < (i + 1#32).toNat,
                  s_jn.core.vals[(tmp5[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
                (FullMem c s_jn ⋆ R) m_jn) ?_ ?_
            · rintro _ ⟨_, ⟨⟩⟩ m_jn ⟨s_jn, hsp_jn, hcv_jn, hal_jn, hpr_jn, htmp_jn, hfl_jn,
                hrefs_jn, hrr_jn, href_jn, hng_jn, hsz_jn, hperm_jn, hct_jn, hfal_jn, hm_jn⟩
              have hi1_nat : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
              fvt_steps
              exact hL (sz.toNat - (i + 1#32).toNat) (i + 1#32, ()) _
                (by (try dsimp only); (try rw [hi1_nat]); omega)
                ⟨s_jn, by omega, rfl, hsp_jn, hcv_jn, hal_jn, hpr_jn, htmp_jn, hfl_jn,
                 hrefs_jn, hrr_jn, href_jn, hng_jn, hsz_jn, hperm_jn, hct_jn, hfal_jn, hm_jn⟩
            · intro J_jn hJ_jn
              fvt_steps
              · exfalso
                have hlv0 : sp.core.vals[lit.toNat]?.getD 0#8 = 0#8 := by
                  rw [List.getElem?_eq_getElem hlit_lt_vals', Option.getD_some]
                  exact (bv8_sext32_eq0_iff _).mp (by first | assumption | c0_bound)
                have hte_lt := hspp.2.1.trail_end_lt_of_unassigned hlit_lt hlv0
                have hnlvl_le : sp.core.cur_level + 1 ≤ c.max_vars := by
                  have := hspp.2.1.cur_level_le; have := hsp_len.cur_vars_le; omega
                have hc0 : c.max_vars % 2 ^ 64 <
                    (sp.core.cur_level + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 := by assumption
                have h1n : BitVec.toNat (1 : BitVec 64) = 1 := rfl
                rw [h1n] at hc0; omega
              · have hlv0 : sp.core.vals[lit.toNat]?.getD 0#8 = 0#8 := by
                  rw [List.getElem?_eq_getElem hlit_lt_vals', Option.getD_some]
                  exact (bv8_sext32_eq0_iff _).mp (by first | assumption | c0_bound)
                have hte_lt := hspp.2.1.trail_end_lt_of_unassigned hlit_lt hlv0
                have hnlvl_le : sp.core.cur_level + 1 ≤ c.max_vars := by
                  have := hspp.2.1.cur_level_le; have := hsp_len.cur_vars_le; omega
                have hnlvl_nat : (BitVec.ofNat 64 sp.core.cur_level + 1).toNat =
                    sp.core.cur_level + 1 := by bv_omega
                have hnlvl_lt_ft : (BitVec.ofNat 64 sp.core.cur_level + 1).toNat <
                    sp.core.frame_trail.length := by
                  rw [hnlvl_nat, hsp_len.frame_trail_len]; omega
                have hnlvl_lt_fd : (BitVec.ofNat 64 sp.core.cur_level + 1).toNat <
                    sp.core.frame_dec.length := by
                  rw [hnlvl_nat, hsp_len.frame_dec_len]; omega
                fvt_steps
                let nlvl := sp.core.cur_level + 1
                let dlit := lit ^^^ 1#32
                let ftrl' := sp.core.frame_trail.set nlvl (BitVec.ofNat 32 sp.core.trail_end)
                let fdec' := sp.core.frame_dec.set nlvl dlit
                let s_pre : FullState :=
                  { sp with core :=
                    { sp.core with frame_trail := ftrl', frame_dec := fdec', cur_level := nlvl } }
                have hlen_pre : s_pre.LengthsOk c :=
                  ⟨{ hsp_len with
                       frame_trail_len := by simp [s_pre, ftrl', hsp_len.frame_trail_len],
                       frame_dec_len := by simp [s_pre, fdec', hsp_len.frame_dec_len] },
                   hspp.1.scratch_ok⟩
                have hdlit_nat : dlit.toNat = lit.toNat ^^^ 1 := bv32_xor1_toNat lit
                have hdlit_lt : dlit.toNat < 2 * sp.core.cur_vars :=
                  hdlit_nat ▸ bv32_xor1_lt_even hlit_lt
                have hdlit_zero : sp.core.vals[dlit.toNat]?.getD 0#8 = 0#8 :=
                  hdlit_nat ▸ vals_xor1_eq_zero hspp.2.1 hlit_lt hlv0
                have hnot_guard : ¬ (s_pre.core.cur_vars ≤ dlit.toNat / 2 ∨
                    c.max_vars ≤ s_pre.core.trail_end ∨
                    s_pre.core.vals[dlit.toNat]?.getD 0#8 ≠ 0#8) := by
                  intro hor; rcases hor with h1 | h2 | h3
                  · dsimp only [s_pre] at h1; omega
                  · have := hsp_len.cur_vars_le; dsimp only [s_pre] at h2; omega
                  · exact h3 hdlit_zero
                have hte_bv : BitVec.setWidth 32 (BitVec.ofNat 64 sp.core.trail_end) =
                    BitVec.ofNat 32 sp.core.trail_end := by apply BitVec.eq_of_toNat_eq; simp
                rw [hlit_i64]
                c0_call hAssign
                refine ⟨c, s_pre, R, rfl, hlen_pre, by dsimp [s_pre, nlvl]; omega,
                  (by simp only [s_pre, nlvl, ftrl', fdec', ← hnlvl_nat, ← hte_bv]
                      exact (by assumption)),
                  ?_⟩
                by_cases hguard : s_pre.core.cur_vars ≤ (lit ^^^ 1).toNat / 2 ∨
                    c.max_vars ≤ s_pre.core.trail_end ∨
                    s_pre.core.vals[(lit ^^^ 1).toNat]?.getD 0#8 ≠ 0#8
                · exact absurd hguard hnot_guard
                simp only [hguard, ↓reduceIte]
                intro flags' unass' phases' m_as hfll' hphl' hm_as
                have hnlvl_ne0 : nlvl ≠ 0 := by omega
                simp only [show s_pre.core.cur_level ≠ 0 from hnlvl_ne0, ↓reduceIte] at hm_as ⊢
                obtain ⟨_, hsp_as, hfal_as, hlit_as_ff⟩ :=
                  vivDecideAssign_preserves_sparseW hspp hlit_lt hlv0 hfll' hphl'
                let s_as : FullState :=
                  { sp with
                    core :=
                      { sp.core with
                        vals := (sp.core.vals.set dlit.toNat 1#8).set (dlit.toNat ^^^ 1) 0xFF#8
                        flags := flags',
                        lvl := sp.core.lvl.set (dlit.toNat / 2) (BitVec.ofNat 32 nlvl),
                        rsns := sp.core.rsns.set (dlit.toNat / 2) 0xFFFFFFFF#32,
                        trl := sp.core.trl.set sp.core.trail_end dlit,
                        trail_pos := sp.core.trail_pos.set (dlit.toNat / 2)
                          (BitVec.ofNat 32 sp.core.trail_end),
                        frame_trail := ftrl', frame_dec := fdec',
                        trail_end := sp.core.trail_end + 1, cur_level := nlvl,
                        unassigned := unass' }
                    scratch := { sp.scratch with phases := phases' } }
                have hsp_as' : FullSparseInvW c F0 F_cur s_as := hsp_as
                have hrefs_as : fullArenaClauseRefs s_as = fullArenaClauseRefs sp := rfl
                have hrr_as : s_as.scratch.red_refs = s.scratch.red_refs := hrrp
                have hng_as : fullArenaClauseGarb s_as cref.toNat = false := hngp
                have hsz_as : fullArenaClauseSize s_as cref.toNat = sz.toNat := hszp
                have hlits_as : fullArenaClauseLits s_as cref.toNat =
                    fullArenaClauseLits sp cref.toNat := rfl
                have hcv_as : s_as.core.cur_vars = sp.core.cur_vars := rfl
                have hal_as : s_as.core.arena_len = sp.core.arena_len := rfl
                have hpr_as : s_as.core.probing = sp.core.probing := rfl
                have hfl_as : s_as.core.fuel = sp.core.fuel := rfl
                have hct_as : s_as.core.confl_type = 0#64 := hct0
                have htmp_as : s_as.core.tmp = tmp5 := htmpp
                have hfal_as' : ∀ l < 2 * sp.core.cur_vars,
                    sp.core.vals[l]?.getD 0#8 = 0xFF#8 →
                    s_as.core.vals[l]?.getD 0#8 = 0xFF#8 := hfal_as
                have hlit_as_ff' : s_as.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8 := hlit_as_ff
                have hm_as' : (FullMem c s_as ⋆ R) m_as := hm_as
                clear_value s_as
                try clear hsp_as hfal_as hlit_as_ff hm_as hlen_pre hguard hnot_guard
                fvt_steps
                exact m4_viv_clause_prop_step Γ hPropIgn hBacktrack hQ hB hJ_jn hsp_as'
                  hcvp hcv_as halp hal_as hprp hpr_as hflp hfl_as hal5 hrefsp hrefs_as hrr_as
                  hrefp hng_as hsz_as hpermp hlits_as hct_as htmp_as
                  hlits2_lt hlits2_mem hi_lt hlit_eq hlit_lt hfalp hfal_as' hlit_as_ff' hm_as'
              · have hdom := hspp.2.1.vals_domain lit.toNat hlit_lt
                have hlv_eq : sp.core.vals[lit.toNat]? =
                    some (sp.core.vals[lit.toNat]'hlit_lt_vals') :=
                  List.getElem?_eq_getElem hlit_lt_vals'
                have hne1 : sp.core.vals[lit.toNat]'hlit_lt_vals' ≠ 1#8 := fun heq => by
                  have hgt : (0#32).slt ((sp.core.vals[lit.toNat]'hlit_lt_vals').signExtend 32) =
                      true := by rw [heq]; decide
                  have hflt : (0#32).slt ((sp.core.vals[lit.toNat]'hlit_lt_vals').signExtend 32) =
                      false := by assumption
                  exact Bool.false_ne_true (hflt.symm.trans hgt)
                have hne0 : sp.core.vals[lit.toNat]'hlit_lt_vals' ≠ 0#8 := fun heq => by
                  have heq0 : (sp.core.vals[lit.toNat]'hlit_lt_vals').signExtend 32 = 0#32 := by
                    rw [heq]; decide
                  have hne0_raw : (sp.core.vals[lit.toNat]'hlit_lt_vals').signExtend 32 ≠ 0#32 :=
                    by assumption
                  exact hne0_raw heq0
                have hlv_ff : sp.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8 := by
                  rw [hlv_eq, Option.getD_some]
                  rcases (by simpa [hlv_eq] using hdom) with h | h | h
                  · exact absurd h hne0
                  · exact absurd h hne1
                  · exact h
                have hi1_nat : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
                fvt_steps
                exact hJ_jn _ _ ⟨sp, hspp, hcvp, halp, hprp, htmpp, hflp, hrefsp, hrrp, hrefp,
                  hngp, hszp, hpermp, hct0, fun k hk => by
                    rw [hi1_nat] at hk
                    rcases (by omega : k < i.toNat ∨ k = i.toNat) with hk' | rfl
                    · exact hfalp k hk'
                    · rw [← hlit_eq]; exact hlv_ff,
                  hmp⟩
        · have hi_eq : i.toNat = sz.toNat := by dsimp only [sz] at hi_le ⊢; c0_bound
          have hfal_all : ∀ l ∈ fullArenaClauseLits sp cref.toNat,
              sp.core.vals[l]?.getD 0#8 = 0xFF#8 := by
            intro l hl
            obtain ⟨k, hk, hget⟩ := hlits2_inv l (hpermp.mem_iff.mp hl)
            rw [← hget]; exact hfalp k (by omega)
          fvt_steps
          exact hB (i, false, 0xFFFFFFFF#32, ()) _ ⟨sp, hspp, hcvp, halp, hprp, hflp, hrefsp,
            hrrp, hrefp, hngp, hszp, Or.inr (Or.inr hi_eq), (fun h => by cases h),
            fun _ h => absurd rfl h, fun _ _ => ⟨hct0, hfal_all⟩, hmp⟩
      · intro B L _ hL
        fvt_steps
        exact hL sz.toNat (0#32, ()) _ ⟨s5, Nat.zero_le _, by simp, hsp5, rfl, rfl, rfl,
          htmp5, hfl5, hrefs5, hrr5, href5, hng5, hsz5, hperm5, hct5,
          fun _ hk => by simp at hk, hm5⟩

private theorem sched_set3_ok {rr : List (BitVec 32)} {cap bn j : Nat}
    {cr k0 k1 : BitVec 32} {refs : List Nat}
    (hlen : rr.length = cap) (h3 : 3 * bn ≤ cap) (hj : j < bn)
    (hok : ∀ k < bn, (rr[3 * k]?.getD 0#32).toNat ∈ refs) (hcr : cr.toNat ∈ refs) :
    let rr' := ((rr.set (3 * j) cr).set (3 * j + 1) k0).set (3 * j + 2) k1
    rr'.length = cap ∧ ∀ k < bn, (rr'[3 * k]?.getD 0#32).toNat ∈ refs := by
  refine ⟨by simp [hlen], fun k hk => ?_⟩
  have hne2 : 3 * j + 2 ≠ 3 * k := by omega
  have hne1 : 3 * j + 1 ≠ 3 * k := by omega
  rw [List.getElem?_set_ne hne2, List.getElem?_set_ne hne1]
  by_cases hkj : k = j
  · subst hkj
    rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hcr
  · rw [List.getElem?_set_ne (by omega)]; exact hok k hk

private theorem m4_mul3_toNat {x : BitVec 64} (hx : 3 * x.toNat + 2 < 2 ^ 64) :
    (x * 3).toNat = 3 * x.toNat := by
  rw [BitVec.toNat_mul, show (3 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem m4_mul3_add1_toNat {x : BitVec 64} (hx : 3 * x.toNat + 2 < 2 ^ 64) :
    (x * 3 + 1).toNat = 3 * x.toNat + 1 := by
  rw [BitVec.toNat_add, m4_mul3_toNat hx, show (1 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega)]

private theorem m4_mul3_add2_toNat {x : BitVec 64} (hx : 3 * x.toNat + 2 < 2 ^ 64) :
    (x * 3 + 2).toNat = 3 * x.toNat + 2 := by
  rw [BitVec.toNat_add, m4_mul3_toNat hx, show (2 : BitVec 64).toNat = 2 from rfl,
    Nat.mod_eq_of_lt (by omega)]

private theorem m4_add1_toNat {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + 1).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt hx]

private theorem m4_sub_toNat {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)]

private theorem m4_getElem_eq {α : Type} {l : List α} {i j : Nat}
    (hi : i < l.length) (hj : j < l.length) (h : i = j) : l[i] = l[j] := by
  subst h; rfl

theorem full_viv_sort_sched_m4_wp (Γ : Env) :
    ∀ a m Q X, fullVivSortSchedM4Spec a m Q X →
      Func.wp Γ full_viv_sort_sched_m4_body a m Q X := by
  rintro ⟨h, bn, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hlen, h3bn, hok0, hm0, hQ⟩
  have hrc := c.hred; have hmx := c.hmaxv; unfold dimacsBound at hrc hmx
  have hrr0_len : s.scratch.red_refs.length = c.red_cap := hlen.scratch_ok.red_refs_len
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
  have hwl0 : s.core.wvec.length = 4 * c.max_vars := hlen.core_ok.wvec_len
  let nlits : BitVec 64 := BitVec.ofNat 64 s.core.cur_vars <<< (BitVec.toNat (1 : BitVec 64) % 64)
  have hnlits_nat : nlits.toNat = 2 * s.core.cur_vars := by
    dsimp only [nlits]
    rw [show BitVec.toNat (1 : BitVec 64) % 64 = 1 from rfl, BitVec.toNat_shiftLeft,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hnlits_le : nlits.toNat ≤ 2 * c.max_vars := by omega
  unfold Func.wp full_viv_sort_sched_m4_body
  fvt_steps
  -- Outer loop on `gap`: `while (gap > 0ULL)`
  refine wp_loop_inv (ts := [i64])
    (fun (gap, ()) mg => ∃ rr : List (BitVec 32),
      gap.toNat ≤ bn.toNat ∧ rr.length = c.red_cap ∧
      (∀ k < bn.toNat, (rr[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
      (FullMem c { s with scratch := { s.scratch with red_refs := rr } } ⋆ R) mg)
    (fun (gap, ()) _ => gap.toNat)
    (fun Jg hJg => by
      fvt_steps
      have hshr : (bn >>> (BitVec.toNat (1#64 : BitVec 64) % 64)).toNat = bn.toNat / 2 := by
        rw [show BitVec.toNat (1#64 : BitVec 64) % 64 = 1 from rfl, BitVec.toNat_ushiftRight,
          Nat.shiftRight_eq_div_pow]
      exact hJg (bn >>> (BitVec.toNat (1#64 : BitVec 64) % 64), ()) m0
        ⟨s.scratch.red_refs, by rw [hshr]; omega, hrr0_len, hok0, hm0⟩)
    (fun Jg ⟨gap, ⟨⟩⟩ mg ⟨rrg, hgap_le, hrrg_len, hokg, hmg⟩ ihg => ?_)
  fvt_steps
  · have hgap_pos : 0 < gap.toNat := by c0_bound
    -- Middle loop on `si`: `while (si < bn)`
    refine wp_loop_inv (ts := [i64])
      (fun (si, ()) msi => ∃ rrs : List (BitVec 32),
        gap.toNat ≤ si.toNat ∧ si.toNat ≤ bn.toNat ∧ rrs.length = c.red_cap ∧
        (∀ k < bn.toNat, (rrs[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
        (FullMem c { s with scratch := { s.scratch with red_refs := rrs } } ⋆ R) msi)
      (fun (si, ()) _ => bn.toNat - si.toNat)
      (fun Ji hJi => by
        fvt_steps
        exact hJi (gap, ()) mg ⟨rrg, Nat.le_refl _, hgap_le, hrrg_len, hokg, hmg⟩)
      (fun Ji ⟨si, ⟨⟩⟩ msi ⟨rrs, hgsi, hsi_le, hrrs_len, hoks, hmsi⟩ ihi => ?_)
    fvt_to_group
    · have hsi_lt : si.toNat < bn.toNat := by c0_bound
      have hsb_nat : (si * 3).toNat = 3 * si.toNat := m4_mul3_toNat (by omega)
      have hsb1_nat : (si * 3 + 1).toNat = 3 * si.toNat + 1 := m4_mul3_add1_toNat (by omega)
      have hsb2_nat : (si * 3 + 2).toNat = 3 * si.toNat + 2 := m4_mul3_add2_toNat (by omega)
      have hsb_lt : (si * 3).toNat < rrs.length := by omega
      have hsb1_lt : (si * 3 + 1).toNat < rrs.length := by omega
      have hsb2_lt : (si * 3 + 2).toNat < rrs.length := by omega
      let cr := rrs[(si * 3).toNat]'hsb_lt
      let k0 := rrs[(si * 3 + 1).toNat]'hsb1_lt
      let k1 := rrs[(si * 3 + 2).toNat]'hsb2_lt
      have hcr_ref : cr.toNat ∈ fullArenaClauseRefs s := by
        have h := hoks si.toNat hsi_lt
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
        have heq : cr = rrs[3 * si.toNat]'(by omega) := Option.some.inj (by
          rw [← List.getElem?_eq_getElem hsb_lt, hsb_nat, List.getElem?_eq_getElem (by omega)])
        rwa [heq]
      fvt_to_group
      -- Join `dk0 = ((u64)k0 < nlits) ? wvec[(k0<<1)+1] : 0u`
      refine wp_join_group (ts := [i32]) (fun _ md0 => md0 = msi) ?_
        (fun Jd0 hJd0 => by
          fvt_steps
          · have hk0_lt : k0.toNat < 2 * s.core.cur_vars := by
              have h3 : (3 : BitVec 64).toNat = 3 := rfl
              have h1 : (1 : BitVec 64).toNat = 1 := rfl
              have hget : k0 = rrs[(si.toNat * (3 : BitVec 64).toNat +
                  (1 : BitVec 64).toNat) % 2 ^ 64]'(by rw [h3, h1]; omega) :=
                m4_getElem_eq hsb1_lt (by rw [h3, h1]; omega) (by rw [hsb1_nat, h3, h1]; omega)
              rw [hget]; omega
            have hk0_wv : (k0.setWidth 64 <<< (BitVec.toNat (1 : BitVec 64) % 64) + 1#64).toNat <
                s.core.wvec.length := by rw [m4_bv32_shl1_add1]; omega
            fvt_steps; exact hJd0 _ msi rfl
          · exact hJd0 _ msi rfl)
      rintro _ ⟨dk0, ⟨⟩⟩ md0 hmd0; rw [hmd0]; fvt_to_group
      -- Join `dk1 = ((u64)k1 < nlits) ? wvec[(k1<<1)+1] : 0u`
      refine wp_join_group (ts := [i32]) (fun _ md1 => md1 = msi) ?_
        (fun Jd1 hJd1 => by
          fvt_steps
          · have hk1_lt : k1.toNat < 2 * s.core.cur_vars := by
              have h3 : (3 : BitVec 64).toNat = 3 := rfl
              have h2 : (2 : BitVec 64).toNat = 2 := rfl
              have hget : k1 = rrs[(si.toNat * (3 : BitVec 64).toNat +
                  (2 : BitVec 64).toNat) % 2 ^ 64]'(by rw [h3, h2]; omega) :=
                m4_getElem_eq hsb2_lt (by rw [h3, h2]; omega) (by rw [hsb2_nat, h3, h2]; omega)
              rw [hget]; omega
            have hk1_wv : (k1.setWidth 64 <<< (BitVec.toNat (1 : BitVec 64) % 64) + 1#64).toNat <
                s.core.wvec.length := by rw [m4_bv32_shl1_add1]; omega
            fvt_steps; exact hJd1 _ msi rfl
          · exact hJd1 _ msi rfl)
      rintro _ ⟨dk1, ⟨⟩⟩ md1 hmd1; rw [hmd1]; fvt_to_group
      -- Inner gap-shift loop on `sj`: `while (sj >= gap)` with `break`
      refine wp_loop_break_group (brkTs := [i64]) (lpTs := [i64])
        (fun (sj_b, ()) mb => ∃ rrb : List (BitVec 32),
          sj_b.toNat < bn.toNat ∧ rrb.length = c.red_cap ∧
          (∀ k < bn.toNat, (rrb[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
          (FullMem c { s with scratch := { s.scratch with red_refs := rrb } } ⋆ R) mb)
        (fun rem (sj, ()) mj => ∃ rrj : List (BitVec 32),
          sj.toNat < bn.toNat ∧ rem = sj.toNat ∧ rrj.length = c.red_cap ∧
          (∀ k < bn.toNat, (rrj[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
          (FullMem c { s with scratch := { s.scratch with red_refs := rrj } } ⋆ R) mj)
        ?_ ?_ ?_
      · -- After inner loop: write `rr[3*sj_b .. +2] = (cr, k0, k1)`, advance `si + 1`
        rintro _ ⟨sj_b, ⟨⟩⟩ mb ⟨rrb, hsjb_lt, hrrb_len, hokb, hmb⟩
        have hfb_nat : (sj_b * 3).toNat = 3 * sj_b.toNat := m4_mul3_toNat (by omega)
        have hfb1_nat : (sj_b * 3 + 1).toNat = 3 * sj_b.toNat + 1 :=
          m4_mul3_add1_toNat (by omega)
        have hfb2_nat : (sj_b * 3 + 2).toNat = 3 * sj_b.toNat + 2 :=
          m4_mul3_add2_toNat (by omega)
        have hfb_lt : (sj_b * 3).toNat < rrb.length := by omega
        have hfb1_lt : (sj_b * 3 + 1).toNat <
            (rrb.set (sj_b * 3).toNat cr).length := by rw [List.length_set]; omega
        have hfb2_lt : (sj_b * 3 + 2).toNat <
            ((rrb.set (sj_b * 3).toNat cr).set (sj_b * 3 + 1).toNat k0).length := by
          rw [List.length_set, List.length_set]; omega
        have hsi1 : (si + 1).toNat = si.toNat + 1 := m4_add1_toNat (by omega)
        fvt_steps
        let rrf := ((rrb.set (3 * sj_b.toNat) cr).set (3 * sj_b.toNat + 1) k0).set
          (3 * sj_b.toNat + 2) k1
        obtain ⟨hrrf_len, hokf⟩ := sched_set3_ok hrrb_len h3bn hsjb_lt hokb hcr_ref
        exact ihi (si + 1, ()) _ (by dsimp only; omega)
          ⟨rrf, by omega, by omega, hrrf_len, hokf,
            by dsimp only [rrf]; rw [hfb_nat, hfb1_nat, hfb2_nat] at hm; exact hm⟩
      · -- Inner loop body
        intro B L rem ⟨sj, ⟨⟩⟩ mj hB hL ⟨rrj, hsj_lt, hrem, hrrj_len, hokj, hmj⟩
        subst hrem
        fvt_steps
        · have hsj_ge : gap.toNat ≤ sj.toNat := by c0_bound
          have hpj_nat : (sj - gap).toNat = sj.toNat - gap.toNat := m4_sub_toNat hsj_ge
          have hpj_lt : (sj - gap).toNat < bn.toNat := by omega
          have hpb_nat : ((sj - gap) * 3).toNat = 3 * (sj - gap).toNat :=
            m4_mul3_toNat (by omega)
          have hpb1_nat : ((sj - gap) * 3 + 1).toNat = 3 * (sj - gap).toNat + 1 :=
            m4_mul3_add1_toNat (by omega)
          have hpb2_nat : ((sj - gap) * 3 + 2).toNat = 3 * (sj - gap).toNat + 2 :=
            m4_mul3_add2_toNat (by omega)
          have hpb_lt : ((sj - gap) * 3).toNat < rrj.length := by omega
          have hpb1_lt : ((sj - gap) * 3 + 1).toNat < rrj.length := by omega
          have hpb2_lt : ((sj - gap) * 3 + 2).toNat < rrj.length := by omega
          let pcr := rrj[((sj - gap) * 3).toNat]'hpb_lt
          let pk0 := rrj[((sj - gap) * 3 + 1).toNat]'hpb1_lt
          let pk1 := rrj[((sj - gap) * 3 + 2).toNat]'hpb2_lt
          have hpcr_ref : pcr.toNat ∈ fullArenaClauseRefs s := by
            have h := hokj (sj - gap).toNat hpj_lt
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
            have heq : pcr = rrj[3 * (sj - gap).toNat]'(by omega) := Option.some.inj (by
              rw [← List.getElem?_eq_getElem hpb_lt, hpb_nat, List.getElem?_eq_getElem (by omega)])
            rwa [heq]
          fvt_to_group
          -- Join `dpk0`
          refine wp_join_group (ts := [i32]) (fun _ mp0 => mp0 = mj) ?_
            (fun Jp0 hJp0 => by
              fvt_steps
              · have hpk0_lt : pk0.toNat < 2 * s.core.cur_vars := by
                  have h3 : (3 : BitVec 64).toNat = 3 := rfl
                  have h1 : (1 : BitVec 64).toNat = 1 := rfl
                  have hget : pk0 = rrj[((2 ^ 64 - gap.toNat + sj.toNat) % 2 ^ 64 *
                      (3 : BitVec 64).toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'(by
                      rw [h3, h1]; omega) :=
                    m4_getElem_eq hpb1_lt (by rw [h3, h1]; omega)
                      (by rw [hpb1_nat, hpj_nat, h3, h1]; omega)
                  rw [hget]; omega
                have hpk0_wv : (pk0.setWidth 64 <<<
                    (BitVec.toNat (1 : BitVec 64) % 64) + 1#64).toNat < s.core.wvec.length := by
                  rw [m4_bv32_shl1_add1]; omega
                fvt_steps; exact hJp0 _ mj rfl
              · exact hJp0 _ mj rfl)
          rintro _ ⟨dpk0, ⟨⟩⟩ mp0 hmp0; rw [hmp0]; fvt_to_group
          -- Join `dpk1`
          refine wp_join_group (ts := [i32]) (fun _ mp1 => mp1 = mj) ?_
            (fun Jp1 hJp1 => by
              fvt_steps
              · have hpk1_lt : pk1.toNat < 2 * s.core.cur_vars := by
                  have h3 : (3 : BitVec 64).toNat = 3 := rfl
                  have h2 : (2 : BitVec 64).toNat = 2 := rfl
                  have hget : pk1 = rrj[((2 ^ 64 - gap.toNat + sj.toNat) % 2 ^ 64 *
                      (3 : BitVec 64).toNat + (2 : BitVec 64).toNat) % 2 ^ 64]'(by
                      rw [h3, h2]; omega) :=
                    m4_getElem_eq hpb2_lt (by rw [h3, h2]; omega)
                      (by rw [hpb2_nat, hpj_nat, h3, h2]; omega)
                  rw [hget]; omega
                have hpk1_wv : (pk1.setWidth 64 <<<
                    (BitVec.toNat (1 : BitVec 64) % 64) + 1#64).toNat < s.core.wvec.length := by
                  rw [m4_bv32_shl1_add1]; omega
                fvt_steps; exact hJp1 _ mj rfl
              · exact hJp1 _ mj rfl)
          rintro _ ⟨dpk1, ⟨⟩⟩ mp1 hmp1; rw [hmp1]
          fvt_to_group
          · exact hB (sj, ()) mj ⟨rrj, hsj_lt, hrrj_len, hokj, hmj⟩
          · -- Join after `if (dpk0 == dk0) { ... }` -> single shift copy
            refine wp_join_group (ts := []) (fun () ms => ms = mj) ?_ ?_
            · rintro _ ⟨⟩ ms hms; rw [hms]
              have hjb_nat : (sj * 3).toNat = 3 * sj.toNat := m4_mul3_toNat (by omega)
              have hjb1_nat : (sj * 3 + 1).toNat = 3 * sj.toNat + 1 :=
                m4_mul3_add1_toNat (by omega)
              have hjb2_nat : (sj * 3 + 2).toNat = 3 * sj.toNat + 2 :=
                m4_mul3_add2_toNat (by omega)
              have hjb_lt : (sj * 3).toNat < rrj.length := by omega
              have hjb1_lt : (sj * 3 + 1).toNat <
                  (rrj.set (sj * 3).toNat pcr).length := by rw [List.length_set]; omega
              have hjb2_lt : (sj * 3 + 2).toNat <
                  ((rrj.set (sj * 3).toNat pcr).set (sj * 3 + 1).toNat pk0).length := by
                rw [List.length_set, List.length_set]; omega
              fvt_steps
              let rrj' := ((rrj.set (3 * sj.toNat) pcr).set (3 * sj.toNat + 1) pk0).set
                (3 * sj.toNat + 2) pk1
              obtain ⟨hrrj'_len, hokj'⟩ := sched_set3_ok hrrj_len h3bn hsj_lt hokj hpcr_ref
              exact hL (sj - gap).toNat (sj - gap, ()) _ (by omega)
                ⟨rrj', hpj_lt, rfl, hrrj'_len, hokj',
                  by dsimp only [rrj']; rw [hjb_nat, hjb1_nat, hjb2_nat] at hm; exact hm⟩
            · intro Js hJs
              refine head_wp_cmp_eq rfl rfl ⟨fun _ => ?_, fun _ => hJs () mj rfl⟩
              refine head_wp_cmp_ult rfl rfl
                ⟨fun _ => hB (sj, ()) mj ⟨rrj, hsj_lt, hrrj_len, hokj, hmj⟩, fun _ => ?_⟩
              refine wp_join_group (ts := []) (fun () ms => ms = mj)
                (fun _ _ _ hm1 => by rw [hm1]; exact hJs () mj rfl) fun Js1 hJs1 => ?_
              refine head_wp_cmp_eq rfl rfl ⟨fun _ => ?_, fun _ => hJs1 () mj rfl⟩
              refine head_wp_cmp_ugt rfl rfl
                ⟨fun _ => hB (sj, ()) mj ⟨rrj, hsj_lt, hrrj_len, hokj, hmj⟩, fun _ => ?_⟩
              refine wp_join_group (ts := []) (fun () ms => ms = mj)
                (fun _ _ _ hm2 => by rw [hm2]; exact hJs1 () mj rfl) fun Js2 hJs2 => ?_
              refine head_wp_cmp_eq rfl rfl ⟨fun _ => ?_, fun _ => hJs2 () mj rfl⟩
              refine head_wp_cmp_ult rfl rfl
                ⟨fun _ => hB (sj, ()) mj ⟨rrj, hsj_lt, hrrj_len, hokj, hmj⟩, fun _ => ?_⟩
              refine head_wp_cmp_eq rfl rfl ⟨fun _ => ?_, fun _ => hJs2 () mj rfl⟩
              exact head_wp_cmp_ule rfl rfl
                ⟨fun _ => hB (sj, ()) mj ⟨rrj, hsj_lt, hrrj_len, hokj, hmj⟩,
                 fun _ => hJs2 () mj rfl⟩
        · exact hB (sj, ()) mj ⟨rrj, hsj_lt, hrrj_len, hokj, hmj⟩
      · intro B L _ hL
        fvt_steps
        exact hL si.toNat (si, ()) msi ⟨rrs, hsi_lt, rfl, hrrs_len, hoks, hmsi⟩
    · -- Middle loop exit: `gap = gap >> 1`
      have hshr : (gap >>> (BitVec.toNat (1#64 : BitVec 64) % 64)).toNat = gap.toNat / 2 := by
        rw [show BitVec.toNat (1#64 : BitVec 64) % 64 = 1 from rfl, BitVec.toNat_ushiftRight,
          Nat.shiftRight_eq_div_pow]
      exact ihg (gap >>> (BitVec.toNat (1#64 : BitVec 64) % 64), ()) msi
        (by dsimp only; rw [hshr]; omega)
        ⟨rrs, by rw [hshr]; omega, hrrs_len, hoks, hmsi⟩
  · exact hQ rrg mg hrrg_len hokg hmg

theorem full_viv_tier_match_m4_wp (Γ : Env) :
    ∀ a m Q X, fullVivTierMatchM4Spec a m Q X →
      Func.wp Γ full_viv_tier_match_m4_body a m Q X := by
  rintro ⟨h, hdr, tier_mode, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hm0, hQ⟩
  unfold Func.wp full_viv_tier_match_m4_body
  fvt_steps <;> exact hQ _

theorem full_viv_collect_m4_wp (Γ : Env)
    (hNext : ∀ a m Q X, Full.fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hTierMatch : ∀ a m Q X, fullVivTierMatchM4Spec a m Q X →
      Γ "full_viv_tier_match_m4" [i64, i32, i64] [.bool] a m Q X) :
    ∀ a m Q X, fullVivCollectM4Spec a m Q X →
      Func.wp Γ full_viv_collect_m4_body a m Q X := by
  rintro ⟨h, tier_mode, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp0, hm0, hQ⟩
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred
  unfold dimacsBound at har_cap hmx hrc
  obtain ⟨F_cur0, hsw0⟩ := hsp0.exists_witness
  have hal0 : s.core.arena_len ≤ c.arena_cap := hsp0.1.lengths.core_ok.arena_len_le
  have har0_len : s.core.arena.length = c.arena_cap := hsp0.1.lengths.core_ok.arena_len_arr
  have htr0_len : s.scratch.tarjan_reach.length = 2 * c.max_vars :=
    hsp0.1.lengths.scratch_ok.tarjan_reach_len
  have hrr0_len : s.scratch.red_refs.length = c.red_cap := hsp0.1.lengths.scratch_ok.red_refs_len
  let bmax : BitVec 64 := BitVec.ofNat 64 c.red_cap / 3#64
  have hbmax_nat : bmax.toNat = c.red_cap / 3 := by
    dsimp only [bmax]
    rw [BitVec.toNat_udiv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      show (3#64 : BitVec 64).toNat = 3 from rfl]
  have h3bmax : 3 * bmax.toNat ≤ c.red_cap := by omega
  have h0_mem : 0 = s.core.arena_len ∨ 0 ∈ fullArenaClauseRefs s := by
    rcases Nat.eq_zero_or_pos s.core.arena_len with h0 | hpos
    · exact Or.inl h0.symm
    · exact Or.inr (fullArenaClauseRefs_zero_mem hsw0.2.1.arena hpos)
  unfold Func.wp full_viv_collect_m4_body
  fvt_steps
  -- Collect unvivified tier-matching candidate clause refs into `red_refs`
  refine wp_loop_inv (ts := [i64, i64])
    (fun (bn, p, ()) mp => ∃ rrp : List (BitVec 32),
      p.toNat ≤ s.core.arena_len ∧
      (p.toNat = s.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s) ∧
      bn.toNat ≤ bmax.toNat ∧ rrp.length = c.red_cap ∧
      (∀ k < bn.toNat, (rrp[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
      (FullMem c { s with scratch := { s.scratch with red_refs := rrp } } ⋆ R) mp)
    (fun (_, p, ()) _ => s.core.arena_len - p.toNat) ?_ ?_
  · intro J1 hJ1; fvt_steps
    exact hJ1 (0#64, 0#64, ()) m0 ⟨s.scratch.red_refs, Nat.zero_le _, h0_mem,
      Nat.zero_le _, hrr0_len, fun _ hk => by simp at hk, hm0⟩
  · intro J1 ⟨bn, p, ⟨⟩⟩ mp ⟨rrp, hp_le, hp_mem, hbn_le, hrrp_len, hokp, hmp⟩ ih1
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
          bn'.toNat ≤ bmax.toNat ∧ rrn.length = c.red_cap ∧
          (∀ k < bn'.toNat, (rrn[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
          (FullMem c { s with scratch := { s.scratch with red_refs := rrn } } ⋆ R) mn) ?_ ?_
      · rintro _ ⟨bn', ⟨⟩⟩ mn ⟨rrn, hbn'_le, hrrn_len, hokn, hmn⟩
        fvt_steps
        exact ih1 (bn', (BitVec.ofNat 32 np_nat).setWidth 64, ()) mn
          (by dsimp only; rw [hnp_bv]; omega)
          ⟨rrn, by rw [hnp_bv]; exact hnb.2, by rw [hnp_bv]; exact hnp_mem,
            hbn'_le, hrrn_len, hokn, hmn⟩
      · intro Jn hJn
        fvt_steps
        · c0_call hTierMatch
          refine ⟨c, { s with scratch := { s.scratch with red_refs := rrp } },
            R, rfl, hmp, fun _take => ?_⟩
          fvt_steps
          · have hbn_lt : bn.toNat < bmax.toNat := by dsimp only [bmax]; c0_bound
            have hbn3_nat : (bn * 3).toNat = 3 * bn.toNat := by bv_omega
            have hbn3_lt : (bn * 3).toNat < rrp.length := by omega
            have hbn1 : (bn + 1).toNat = bn.toNat + 1 := by bv_omega
            let rrp1 := rrp.set (3 * bn.toNat) (p.setWidth 32)
            have hrrp1_len : rrp1.length = c.red_cap := by simp [rrp1, hrrp_len]
            have hokp1 : ∀ k < (bn + 1).toNat,
                (rrp1[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s := by
              intro k hk; rw [hbn1] at hk
              rcases (by omega : k < bn.toNat ∨ k = bn.toNat) with hk' | rfl
              · dsimp only [rrp1]; rw [List.getElem?_set_ne (by omega)]; exact hokp k hk'
              · dsimp only [rrp1]
                rw [List.getElem?_set_self (by omega), Option.getD_some, hp32]
                exact hp_ref
            fvt_steps
            exact hJn (bn + 1, ()) _ ⟨rrp1, by omega, hrrp1_len, hokp1,
              by simpa only [rrp1, hbn3_nat] using hm⟩
          · exact hJn (bn, ()) mp ⟨rrp, hbn_le, hrrp_len, hokp, hmp⟩
          · exact hJn (bn, ()) mp ⟨rrp, hbn_le, hrrp_len, hokp, hmp⟩
        · exact hJn (bn, ()) mp ⟨rrp, hbn_le, hrrp_len, hokp, hmp⟩
    · exact hQ bn s.scratch.tarjan_reach rrp mp (by omega) htr0_len hrrp_len hokp hmp

theorem full_viv_keys_m4_wp (Γ : Env) :
    ∀ a m Q X, fullVivKeysM4Spec a m Q X →
      Func.wp Γ full_viv_keys_m4_body a m Q X := by
  rintro ⟨h, bn, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp0, h3bn, hok0, hm0, hQ⟩
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred
  unfold dimacsBound at har_cap hmx hrc
  obtain ⟨F_cur0, hsw0⟩ := hsp0.exists_witness
  have hcv0_le : s.core.cur_vars ≤ c.max_vars := hsp0.1.lengths.core_ok.cur_vars_le
  have hal0 : s.core.arena_len ≤ c.arena_cap := hsp0.1.lengths.core_ok.arena_len_le
  have har0_len : s.core.arena.length = c.arena_cap := hsp0.1.lengths.core_ok.arena_len_arr
  have hwl0 : s.core.wvec.length = 4 * c.max_vars := hsp0.1.lengths.core_ok.wvec_len
  have hrr0_len : s.scratch.red_refs.length = c.red_cap := hsp0.1.lengths.scratch_ok.red_refs_len
  let nlits : BitVec 64 := BitVec.ofNat 64 s.core.cur_vars <<< (BitVec.toNat (1 : BitVec 64) % 64)
  have hnlits_nat : nlits.toNat = 2 * s.core.cur_vars := by
    dsimp only [nlits]
    rw [show BitVec.toNat (1 : BitVec 64) % 64 = 1 from rfl, BitVec.toNat_shiftLeft,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hnlits_le : nlits.toNat ≤ 2 * c.max_vars := by omega
  unfold Func.wp full_viv_keys_m4_body
  fvt_steps
  refine wp_loop_inv (ts := [i64])
    (fun (bi, ()) mbi => ∃ rri : List (BitVec 32),
      bi.toNat ≤ bn.toNat ∧ rri.length = c.red_cap ∧
      (∀ k < bn.toNat, (rri[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
      (FullMem c { s with scratch := { s.scratch with red_refs := rri } } ⋆ R) mbi)
    (fun (bi, ()) _ => bn.toNat - bi.toNat) ?_ ?_
  · intro J2 hJ2; fvt_steps
    exact hJ2 (0#64, ()) m0 ⟨s.scratch.red_refs, Nat.zero_le _, hrr0_len, hok0, hm0⟩
  · intro J2 ⟨bi, ⟨⟩⟩ mbi ⟨rri, hbi_le, hrri_len, hoki, hmbi⟩ ih2
    fvt_steps
    · have hbi_lt : bi.toNat < bn.toNat := by c0_bound
      have hbi3_nat : (bi * 3).toNat = 3 * bi.toNat := by bv_omega
      have hbi31_nat : (bi * 3 + 1).toNat = 3 * bi.toNat + 1 := by bv_omega
      have hbi32_nat : (bi * 3 + 2).toNat = 3 * bi.toNat + 2 := by bv_omega
      have hbi3_lt : (bi * 3).toNat < rri.length := by omega
      let cr := rri[(bi * 3).toNat]'hbi3_lt
      have hcr_ref : cr.toNat ∈ fullArenaClauseRefs s := by
        have h := hoki bi.toNat hbi_lt
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
        have heq : cr = rri[3 * bi.toNat]'(by omega) := Option.some.inj (by
          rw [← List.getElem?_eq_getElem hbi3_lt, hbi3_nat,
            List.getElem?_eq_getElem (by omega)])
        rwa [heq]
      have hwfcr := hsw0.2.1.arena.refs_wf cr.toNat hcr_ref
      have hcr2_nat : (cr.setWidth 64 + 2).toNat = cr.toNat + 2 := by bv_omega
      have hcr2_lt : (cr.setWidth 64 + 2).toNat < s.core.arena.length := by omega
      let szc := s.core.arena[(cr.setWidth 64 + 2).toNat]'hcr2_lt
      have hszc_nat : szc.toNat = fullArenaClauseSizeCore s.core cr.toNat := by
        unfold fullArenaClauseSizeCore
        have hg : s.core.arena[cr.toNat + 2]? = some szc := by
          rw [← hcr2_nat, List.getElem?_eq_getElem hcr2_lt]
        rw [hg, Option.getD_some]
      have hbdc : cr.toNat + 3 + szc.toNat ≤ s.core.arena.length := by
        have := hwfcr.2.2.1; have := hwfcr.2.2.2.1; omega
      fvt_steps
      -- Inner key-selection loop `while (j < szc)` (read-only on memory)
      refine wp_loop_inv (ts := [i32, i32, i32, i32, i32])
        (fun (k0, d0, k1, d1, j, ()) mj => j.toNat ≤ szc.toNat ∧ mj = mbi)
        (fun (_, _, _, _, j, ()) _ => szc.toNat - j.toNat) ?_ ?_
      · intro Jk hJk; fvt_steps
        exact hJk (0xFFFFFFFF#32, 0#32, 0xFFFFFFFF#32, 0#32, 0#32, ()) mbi
          ⟨Nat.zero_le _, rfl⟩
      · intro Jk ⟨k0, d0, k1, d1, j, ⟨⟩⟩ mj ⟨hj_le, hmj⟩ ihk
        rw [hmj]; fvt_steps
        · have hj_lt : j.toNat < szc.toNat := by c0_bound
          have hj_idx : (cr.setWidth 64 + 3 + j.setWidth 64).toNat =
              cr.toNat + 3 + j.toNat := by bv_omega
          have hj_ar : (cr.setWidth 64 + 3 + j.setWidth 64).toNat <
              s.core.arena.length := by omega
          have hj1 : (j + 1).toNat = j.toNat + 1 := by bv_omega
          fvt_to_group
          -- Join `dl = ((u64)l < nlits) ? wvec[(l<<1)+1] : 0u`
          refine wp_join_group (ts := [i32]) (fun _ mdl => mdl = mbi) ?_ ?_
          · rintro _ ⟨dl, ⟨⟩⟩ mdl hmdl; rw [hmdl]; fvt_to_group
            refine wp_join_group (ts := [i32, i32, i32, i32]) (fun _ mu => mu = mbi) ?_ ?_
            · rintro _ ⟨k0', d0', k1', d1', ⟨⟩⟩ mu hmu
              rw [hmu]; fvt_steps
              exact ihk (k0', d0', k1', d1', j + 1, ()) mbi
                (by dsimp only; omega) ⟨by omega, rfl⟩
            · intro Ju hJu
              fvt_steps <;> exact hJu _ mbi rfl
          · intro Jdl hJdl
            fvt_steps
            · let l := s.core.arena[(cr.setWidth 64 + 3 + j.setWidth 64).toNat]'hj_ar
              have hl_lt : l.toNat < 2 * s.core.cur_vars := by dsimp only [l, cr]; c0_bound
              have hl_wv : (l.setWidth 64 <<< (BitVec.toNat (1 : BitVec 64) % 64) + 1#64).toNat <
                  s.core.wvec.length := by rw [m4_bv32_shl1_add1]; omega
              fvt_steps; exact hJdl _ mbi rfl
            · exact hJdl _ mbi rfl
        · -- Key loop exit: write `rr[3*bi + 1] = k0; rr[3*bi + 2] = k1;`
          have hbi31_lt : (bi * 3 + 1).toNat < rri.length := by omega
          have hbi32_lt : (bi * 3 + 2).toNat <
              (rri.set (bi * 3 + 1).toNat k0).length := by simp [hrri_len]; omega
          have hbi1 : (bi + 1).toNat = bi.toNat + 1 := by bv_omega
          fvt_steps
          let rri' := (rri.set (3 * bi.toNat + 1) k0).set (3 * bi.toNat + 2) k1
          have hoki' : ∀ k < bn.toNat,
              (rri'[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s := by
            intro k hk
            dsimp only [rri']
            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
            exact hoki k hk
          exact ih2 (bi + 1, ()) _ (by dsimp only; omega)
            ⟨rri', by omega, by simp [rri', hrri_len], hoki',
              by simpa only [rri', hbi31_nat, hbi32_nat] using hm⟩
    · exact hQ rri mbi hrri_len hoki hmbi

theorem full_viv_clear_tier_m4_wp (Γ : Env)
    (hNext : ∀ a m Q X, Full.fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hTierMatch : ∀ a m Q X, fullVivTierMatchM4Spec a m Q X →
      Γ "full_viv_tier_match_m4" [i64, i32, i64] [.bool] a m Q X) :
    ∀ a m Q X, fullVivClearTierM4Spec a m Q X →
      Func.wp Γ full_viv_clear_tier_m4_body a m Q X := by
  rintro ⟨h, tier_mode, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp0, hcl0, hm0, hQ⟩
  have har_cap := c.harena; unfold dimacsBound at har_cap
  unfold Func.wp full_viv_clear_tier_m4_body
  fvt_steps
  refine wp_loop_inv (ts := [i64])
    (fun (q, ()) mq => ∃ sq : FullState,
      sq.core.arena_len ≤ c.arena_cap ∧ q.toNat ≤ sq.core.arena_len ∧
      (q.toNat = sq.core.arena_len ∨ q.toNat ∈ fullArenaClauseRefs sq) ∧
      FullSparseInv c F0 sq ∧ sq.core.cur_level = 0 ∧ sq.core.fuel = s.core.fuel ∧
      (FullMem c sq ⋆ R) mq)
    (fun (q, ()) _ => c.arena_cap - q.toNat) ?_ ?_
  · intro Jq hJq; fvt_steps
    obtain ⟨F_cur0, hsw0⟩ := hsp0.exists_witness
    have h0_mem : 0 = s.core.arena_len ∨ 0 ∈ fullArenaClauseRefs s := by
      rcases Nat.eq_zero_or_pos s.core.arena_len with h0 | hpos
      · exact Or.inl h0.symm
      · exact Or.inr (fullArenaClauseRefs_zero_mem hsw0.2.1.arena hpos)
    exact hJq (0#64, ()) m0 ⟨s, hsp0.1.lengths.core_ok.arena_len_le, Nat.zero_le _, h0_mem,
      hsp0, hcl0, rfl, hm0⟩
  · intro Jq ⟨q, ⟨⟩⟩ mq ⟨sq, halq, hq_le, hq_mem, hspq, hclq, hflq, hmq⟩ ihq
    fvt_steps
    · have hq_lt : q.toNat < sq.core.arena_len := by c0_bound
      have hq_ref : q.toNat ∈ fullArenaClauseRefs sq := hq_mem.resolve_left (by omega)
      obtain ⟨F_curq, hswq⟩ := hspq.exists_witness
      have hq_lt_ar : q.toNat < sq.core.arena.length := by
        have := hspq.1.lengths.core_ok.arena_len_arr; omega
      have hq32 : (q.setWidth 32).toNat = q.toNat := by bv_omega
      let hdrq := sq.core.arena[q.toNat]'hq_lt_ar
      have hhdrq : fullArenaHdr sq q.toNat = hdrq := by
        unfold fullArenaHdr fullArenaHdrCore
        rw [List.getElem?_eq_getElem hq_lt_ar, Option.getD_some]
      fvt_to_group
      refine wp_join_group (ts := [])
        (fun () mq2 => ∃ sq2 : FullState,
          sq2.core.arena_len = sq.core.arena_len ∧ sq2.core.arena_len ≤ c.arena_cap ∧
          FullSparseInv c F0 sq2 ∧ sq2.core.cur_level = 0 ∧ sq2.core.fuel = s.core.fuel ∧
          q.toNat ∈ fullArenaClauseRefs sq2 ∧ (FullMem c sq2 ⋆ R) mq2) ?_ ?_
      · rintro _ ⟨⟩ mq2 ⟨sq2, _, halq2, hspq2, hclq2, hflq2, hq_ref2, hmq2⟩
        fvt_steps
        c0_call hNext
        refine ⟨c, sq2, R, rfl, hspq2.1.lengths, hmq2, ?_⟩
        obtain ⟨F_curq2, hswq2⟩ := hspq2.exists_witness
        have hwfq2 := hswq2.2.1.arena.refs_wf q.toNat hq_ref2
        let nq_nat := fullArenaNextOff sq2.core.arena sq2.core.arena_len q.toNat
        have hnb : q.toNat < nq_nat ∧ nq_nat ≤ sq2.core.arena_len := by
          dsimp only [nq_nat]; simpa using fullArenaNextOff_bounds hwfq2.1
        have hnq_mem : nq_nat = sq2.core.arena_len ∨ nq_nat ∈ fullArenaClauseRefs sq2 :=
          fullArenaClauseRefs_next_mem_or_end hswq2.2.1.arena hq_ref2
        have hnq_bv : ((BitVec.ofNat 32 nq_nat).setWidth 64).toNat = nq_nat := by
          rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)]
        simp only [hq32]
        exact ihq ((BitVec.ofNat 32 nq_nat).setWidth 64, ()) _ (by dsimp only; rw [hnq_bv]; omega)
          ⟨sq2, halq2, by rw [hnq_bv]; exact hnb.2, by rw [hnq_bv]; exact hnq_mem,
            hspq2, hclq2, hflq2, hmq2⟩
      · intro Jn2 hJn2
        fvt_steps
        · c0_call hTierMatch
          refine ⟨c, sq, R, rfl, hmq, fun _take => ?_⟩
          fvt_steps
          · let hdrq' := hdrq &&& ~~~0x00100000#32
            obtain ⟨hsw_cl, hrefs_cl, _⟩ :=
              fullArena_setHdr_preserves_sparseW hswq hq_ref (hdr' := hdrq')
                (by rw [hhdrq]; exact bv32_clr_viv_garb hdrq)
                (by rw [hhdrq]; exact bv32_clr_viv_shrk hdrq)
            let s_cl : FullState :=
              { sq with core := { sq.core with arena := sq.core.arena.set q.toNat hdrq' } }
            exact hJn2 () _ ⟨s_cl, rfl, halq, hsw_cl.toSparse, hclq, hflq,
              by rw [hrefs_cl]; exact hq_ref, by assumption⟩
          · exact hJn2 () mq ⟨sq, rfl, halq, hspq, hclq, hflq, hq_ref, hmq⟩
        · exact hJn2 () mq ⟨sq, rfl, halq, hspq, hclq, hflq, hq_ref, hmq⟩
    · exact hQ sq mq hspq hclq hflq hmq

theorem full_vivify_m4_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hCollect : ∀ a m Q X, fullVivCollectM4Spec a m Q X →
      Γ "full_viv_collect_m4" [i64, i64] [i64] a m Q X)
    (hKeys : ∀ a m Q X, fullVivKeysM4Spec a m Q X →
      Γ "full_viv_keys_m4" [i64, i64] [] a m Q X)
    (hSortSched : ∀ a m Q X, fullVivSortSchedM4Spec a m Q X →
      Γ "full_viv_sort_sched_m4" [i64, i64] [] a m Q X)
    (hVivClause : ∀ a m Q X, fullVivClauseM4Spec a m Q X →
      Γ "full_viv_clause_m4" [i64, i32] [i64] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hClearTier : ∀ a m Q X, fullVivClearTierM4Spec a m Q X →
      Γ "full_viv_clear_tier_m4" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullFastBveBudgets.fullVivifyFastSpec a m Q X →
      Func.wp Γ full_vivify_m4_body a m Q X := by
  rintro ⟨h, tier_mode, budget0, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp0, hm0, hQ⟩
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred
  unfold dimacsBound at har_cap hmx hrc
  unfold Func.wp full_vivify_m4_body; fvt_to_group
  · fvt_steps
    exact hQ 1#64 s m0 hsp0 id id (fun hnz => absurd (by c0_bound) hnz)
      (Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm0
  -- Entry backtrack to level 0
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ s1 : FullState, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1) ?_ ?_
  · rintro _ ⟨⟩ m1 ⟨s1, hsp1, hcl1, hfl1, hm1⟩
    fvt_to_group
    -- Join `delta = (start_ticks > fwd_sub_cnt) ? ... : 0`
    refine wp_join_group (ts := [i64]) (fun _ md => md = m1) ?_
      (fun Jd hJd => by fvt_steps <;> exact hJd _ m1 rfl)
    rintro _ ⟨delta, ⟨⟩⟩ md hmd; rw [hmd]
    fvt_to_group
    -- Join `eff_ref = (delta < 10000000ULL) ? 10000000ULL : delta`
    refine wp_join_group (ts := [i64]) (fun _ me => me = m1) ?_
      (fun Je hJe => by fvt_steps <;> exact hJe _ m1 rfl)
    rintro _ ⟨eff_ref, ⟨⟩⟩ me hme; rw [hme]
    fvt_to_group
    -- Join `tick_cap = (tier_mode == 3ULL) ? base_eff : (base_eff * 3ULL)`
    refine wp_join_group (ts := [i64]) (fun _ mtc => mtc = m1) ?_
      (fun Jtc hJtc => by fvt_steps <;> exact hJtc _ m1 rfl)
    rintro _ ⟨tick_cap, ⟨⟩⟩ mtc hmtc; rw [hmtc]
    fvt_steps
    let s2 : FullState := { s1 with core := { s1.core with probing := 1#64 } }
    have hsp2 : FullSparseInv c F0 s2 := FullVivTop.FullSparseInv.with_probing hsp1 1#64
    have hm2 : (FullMem c s2 ⋆ R) m := hm
    have hfl2 : s2.core.fuel.toNat ≤ s.core.fuel.toNat := hfl1
    clear_value s2
    clear hsp1 hcl1 hfl1 hm
    -- Pass 1: zero `noccs`, collect candidate clause refs, count literal occurrences
    c0_call hCollect
    refine ⟨c, F0, s2, R, rfl, hsp2, hm2, fun bn tr3 rr3 m3 h3bn htr3 hrr3 hok3 hm3 => ?_⟩
    let s3 : FullState :=
      { s2 with scratch := { s2.scratch with tarjan_reach := tr3, red_refs := rr3 } }
    have hsp3 : FullSparseInv c F0 s3 :=
      FullSparseInv.with_red_refs (FullSparseInv.with_tarjan_reach hsp2 htr3) hrr3
    -- Pass 2: compute top-2 `(k0, k1)` keys in `red_refs`
    c0_call hKeys
    refine ⟨c, F0, s3, R, rfl, hsp3, h3bn, hok3, hm3, fun rr4 m4 hrr4 hok4 hm4 => ?_⟩
    let s4 : FullState := { s3 with scratch := { s3.scratch with red_refs := rr4 } }
    have hsp4 : FullSparseInv c F0 s4 := FullSparseInv.with_red_refs hsp3 hrr4
    -- Pass 3: shellsort schedule in `red_refs`
    c0_call hSortSched
    refine ⟨c, s4, R, rfl, hsp4.1.lengths, h3bn, hok4, hm4,
      fun rr5 m5 hrr5_len hok5 hm5 => ?_⟩
    let s5 : FullState := { s4 with scratch := { s4.scratch with red_refs := rr5 } }
    have hsp5 : FullSparseInv c F0 s5 := FullSparseInv.with_red_refs hsp4 hrr5_len
    have hfl5 : s5.core.fuel.toNat ≤ s.core.fuel.toNat := hfl2
    have hrefs5 : fullArenaClauseRefs s5 = fullArenaClauseRefs s2 := rfl
    have hrr5 : s5.scratch.red_refs = rr5 := rfl
    have hok5' : ∀ k < bn.toNat, (rr5[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s2 := hok5
    have hm5' : (FullMem c s5 ⋆ R) m5 := hm5
    clear_value s5 s4 s3
    clear s4 s3 hsp4 hsp3 tr3 rr3 rr4 htr3 hrr3 hrr4 hok3 hok4 hok5 hm3 hm4 hm5 hsp2 hm2 hfl2
      hCollect hKeys hSortSched
    fvt_to_group
    -- Pass 4: Vivify sorted candidates `while (bi < bn && ...)`
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
    · -- Post-loop: backtrack to 0, optional wrap-around `PH_VIV` clear, zero `noccs`, `probing = 0`
      rintro _ ⟨_, res_b, bi_b, ⟨⟩⟩ mb ⟨sb, hspb, hflb, hresb, h20b, hmb⟩
      refine wp_join_group (ts := [])
        (fun () m_bt => ∃ sbt : FullState,
          FullSparseInv c F0 sbt ∧ sbt.core.cur_level = 0 ∧
          sbt.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sbt ⋆ R) m_bt) ?_ ?_
      · rintro _ ⟨⟩ m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
        -- Join after optional wrap-around `full_viv_clear_tier_m4`
        refine wp_join_group (ts := [])
          (fun () m_w => ∃ sw : FullState,
            FullSparseInv c F0 sw ∧ sw.core.cur_level = 0 ∧
            sw.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sw ⋆ R) m_w) ?_ ?_
        · -- Set `probing = 0`, return `res_b`
          rintro _ ⟨⟩ m_w ⟨sw, hspw, hclw, hflw, hm_w⟩
          fvt_steps
          let sf : FullState := { sw with core := { sw.core with probing := 0#64 } }
          have hspf : FullSparseInv c F0 sf := FullVivTop.FullSparseInv.with_probing hspw 0#64
          exact hQ res_b sf _ hspf (fun _ => hclw) (fun _ => rfl)
            (fun _ => ⟨hclw, rfl⟩) hflw hresb h20b hm
        · -- Optional wrap-around `if (res == 1 && bi >= bn && bn < bmax) full_viv_clear_tier_m4`
          intro Jw hJw
          fvt_steps
          · c0_call hClearTier
            refine ⟨c, F0, sbt, R, rfl, hspbt, hclbt, hm_bt,
              fun sw m_w hspw hclw hflw hm_w =>
                hJw () m_w ⟨sw, hspw, hclw, by rw [hflw]; exact hflbt, hm_w⟩⟩
          · exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
          · exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
          · exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
      · -- Post-loop `if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }`
        intro Jbt hJbt
        obtain ⟨F_curb, hswb⟩ := hspb.exists_witness
        have hclb_lt : sb.core.cur_level < 2 ^ 64 := by
          have := hswb.2.1.cur_level_le; have := hspb.1.lengths.core_ok.trail_end_le
          have := hspb.1.lengths.core_ok.cur_vars_le; omega
        fvt_steps
        · c0_call hBacktrack
          refine ⟨c, sb, R, rfl, hspb.1.lengths, hclb_lt,
            (by have h0n : BitVec.toNat (0 : BitVec 64) = 0 := rfl; rw [h0n]; intro;
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
    · -- Pass 4 loop body
      intro B L rem ⟨budget, bi, ⟨⟩⟩ mvi hB hL
        ⟨svi, hbi_le, hrem, hspv, hflv, hrefsv, hrrv, hmvi⟩
      subst hrem
      fvt_steps
      · have hbi_lt : bi.toNat < bn.toNat := by c0_bound
        have hbi3_nat : (bi * 3).toNat = 3 * bi.toNat := by bv_omega
        have hbi3_lt : (bi * 3).toNat < svi.scratch.red_refs.length := by
          rw [hrrv, hrr5_len]; omega
        let cr := svi.scratch.red_refs[(bi * 3).toNat]'hbi3_lt
        have hcr_ref : cr.toNat ∈ fullArenaClauseRefs svi := by
          rw [hrefsv]
          have h := hok5' bi.toNat hbi_lt
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
          have heq : cr = rr5[3 * bi.toNat]'(by omega) := Option.some.inj (by
            rw [← List.getElem?_eq_getElem hbi3_lt, hrrv, hbi3_nat,
              List.getElem?_eq_getElem (by omega)])
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
        · -- `cur_level == 0`: call `full_propagate(h)`
          have hcl_vc_lt : s_vc.core.cur_level < 2 ^ 64 := by
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
              ticks_p wsort_p phases_p m_p hlen_p hw_p _ hperm_p hfl_p _ _ hpr1 _ _
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
                search_ticks := ticks_p, wsort := wsort_p, phases := phases_p } }
          have hsw_p : FullSparseInvW c F0 F_curv s_p :=
            m4_sparseInvW_of_prop_canon hsw_vc hlen_p hw_p hperm_p
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
        · -- `cur_level != 0`: keep trail alive for next clause
          exact hL (bn.toNat - (bi + 1#64).toNat) (budget - 1#64, bi + 1#64, ()) m_vc
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
    · -- Pass 4 loop entry
      intro B L _ hL; fvt_steps
      exact hL bn.toNat (budget0, 0#64, ()) m5
        ⟨s5, Nat.zero_le _, by simp, hsp5, hfl5, hrefs5, hrr5, hm5'⟩
  · -- Entry `if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }`
    intro Jc hJc
    obtain ⟨F_cur0, hsw0⟩ := hsp0.exists_witness
    have hcl0_lt : s.core.cur_level < 2 ^ 64 := by
      have := hsw0.2.1.cur_level_le; have := hsp0.1.lengths.core_ok.trail_end_le
      have := hsp0.1.lengths.core_ok.cur_vars_le; omega
    fvt_steps
    · c0_call hBacktrack
      refine ⟨c, s, R, rfl, hsp0.1.lengths, hcl0_lt,
        (by have h0n : BitVec.toNat (0 : BitVec 64) = 0 := rfl; rw [h0n]; intro;
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

end VivM4Proofs

end LeanQbe.T.Examples.Kissat.FullM4VivBce
