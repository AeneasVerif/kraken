module

public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof2a
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof2b
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat M6 Vivification — Instantiation, Finish, & Clause Loop (`Proof3a`)

Certifies UNSAT-sound `Func.wp` (`XPost := False`, `0` SAT model proofs) for the `7` mid-level
vivification functions in `FullM6VivBackbone.lean`:
1. `full_viv_inst_m6_wp` (instantiation strengthening via `inst_resolve_entails`)
2. `full_viv_finish_m6_wp` (subsumption promotion/glue-lowering, prefix-preserving commit,
   same-size AT deletion, instantiation fallback, & 2WL re-establishment)
3. `full_viv_sort_counts_m6_wp` (insertion sort on `tmp_lits` by `tarjan_reach` literal counts)
4. `full_viv_has_l0_m6_wp` (read-only level-0 assignment scan)
5. `full_viv_l0_simp_m6_wp` (level-0 backtrack + `full_viv_simplify_m6`, OOM `2ULL`)
6. `full_viv_reuse_prefix_m6_wp` (prefix-trail reuse backtrack)
7. `full_viv_clause_m6_wp` (single-clause vivification driver with `full_viv_best_implied_m6`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6VivBackbone

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open FullVivTopTactics FullVivTop
open scoped FullArenaTactics FullVivTopTactics

/-! ## 1. Cross-File Specifications (`7` Vivification Mid-Level Functions) -/

section Specs

/-- `full_viv_inst_m6(h, cref, sz)`: instantiation strengthening trying the last literal of
`tmp[0 ..< sz)` positively, certifying resolvent entailment via `inst_resolve_entails`, and
committing `tmp[0 ..< sz - 1)`. Returns `0` (unchanged), `1` (strengthened), `2` (OOM), or
`20` (UNSAT). -/
@[expose] def fullVivInstM6Spec : Spec [i64, i32, i32] [i64] := fun (h, cref, sz, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧
    cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
    fullArenaClauseSize s cref.toNat = sz.toNat ∧ sz.toNat ≤ c.max_vars ∧
    ((s.core.tmp.take sz.toNat).map BitVec.toNat).Perm (fullArenaClauseLits s cref.toNat) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.arena_len = s.core.arena_len → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `full_viv_finish_m6(h, cref, sz, confl, implied, all_done)`: post-loop deduction, subsumption
promotion/glue-lowering, prefix-preserving commit, AT deletion, instantiation strengthening, and
2WL watch-invariant re-establishment. -/
@[expose] def fullVivFinishM6Spec : Spec [i64, i32, i32, .bool, i32, .bool] [i64] :=
  fun (h, cref, sz, confl, implied, all_done, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ sz.toNat ≤ c.max_vars ∧
      cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
      fullArenaClauseSize s cref.toNat = sz.toNat ∧
      ((s.core.tmp.take sz.toNat).map BitVec.toNat).Perm (fullArenaClauseLits s cref.toNat) ∧
      (confl = true → FullConflictOkW F_cur s) ∧
      (confl = false → implied ≠ 0xFFFFFFFF#32 →
        implied.toNat < 2 * s.core.cur_vars ∧ s.core.vals[implied.toNat]?.getD 0#8 = 1#8) ∧
      (confl = false → implied = 0xFFFFFFFF#32 → all_done = true →
        s.core.confl_type = 0#64 ∧
        ∀ l ∈ fullArenaClauseLits s cref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        FullSparseInvW c F0 F_cur s' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        s'.core.arena_len = s.core.arena_len → fullArenaClauseRefs s' = fullArenaClauseRefs s →
        s'.scratch.red_refs = s.scratch.red_refs →
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `full_viv_sort_counts_m6(h, sz)`: sorts `tmp_lits[0 ..< sz)` in place by literal counts stored
in `tarjan_reach` (descending count, ascending literal ID tie-break). -/
@[expose] def fullVivSortCountsM6Spec : Spec [i64, i32] [] := fun (h, sz, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ sz.toNat ≤ c.max_vars ∧
    (∀ k < sz.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ tmp' m', tmp'.length = c.max_vars →
      (tmp'.take sz.toNat).Perm (s.core.tmp.take sz.toNat) →
      (∀ k, sz.toNat ≤ k → k < c.max_vars → tmp'[k]? = s.core.tmp[k]?) →
      (FullMem c { s with core := { s.core with tmp := tmp' } } ⋆ R) m' → Q () m'

/-- `full_viv_has_l0_m6(h, cref, sz)`: read-only level-0 assignment scan over `cref`. -/
@[expose] def fullVivHasL0M6Spec : Spec [i64, i32, i32] [.bool] := fun (h, cref, sz, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    fullArenaClauseGarb s cref.toNat = false ∧ sz.toNat = fullArenaClauseSize s cref.toNat ∧
    (FullMem c s ⋆ R) m ∧ ∀ r : Bool, Q (r, ()) m

/-- `full_viv_l0_simp_m6(h, cref, sz)`: if `cref` has a level-0 assigned literal, backtracks to
level `0` and runs `full_viv_simplify_m6`; returns `0`, `1`, `2` (OOM), or `20` (UNSAT). -/
@[expose] def fullVivL0SimpM6Spec : Spec [i64, i32, i32] [i64] := fun (h, cref, sz, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    fullArenaClauseGarb s cref.toNat = false ∧ sz.toNat = fullArenaClauseSize s cref.toNat ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.fuel = s.core.fuel →
      s'.core.arena_len = s.core.arena_len → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 0#64 → cref.toNat ∈ fullArenaClauseRefs s' ∧ fullArenaClauseGarb s' cref.toNat = false) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `full_viv_reuse_prefix_m6(h, cref, sz)`: prefix-trail reuse keeping the longest shared decision
prefix `frame_dec[1 .. keep_lvl]` and backtracking only to `keep_lvl`. -/
@[expose] def fullVivReusePrefixM6Spec : Spec [i64, i32, i32] [] := fun (h, _cref, sz, ()) m Q _ =>
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

/-- `full_viv_clause_m6(h, cref)`: full M6 single-clause vivification preserving
`FullSparseInvW`, `fullArenaClauseRefs`, and `red_refs`. -/
@[expose] def fullVivClauseM6Spec : Spec [i64, i32] [i64] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.arena_len = s.core.arena_len → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

end Specs

/-! ## 2. Private Pure & State Helpers -/

section Helpers

private theorem m6_bv32_xor1_xor1 (x : BitVec 32) : (x ^^^ 1#32) ^^^ 1#32 = x := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

private theorem m6_conflictOkW_to_viv {F_cur : List (List Nat)} {s : FullState}
    (h : FullConflictOkW F_cur s) : FullVivifySpecs.FullVivConflictOk F_cur s := by
  rcases h with ⟨ht, h0, h1, hf0, hf1, hent⟩ | h2
  · exact Or.inl ⟨ht, h0, h1, hent, hf0, hf1⟩
  · exact Or.inr h2

private theorem m6_sparseInvW_with_ant_res {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (asz rsz : BitVec 64) :
    FullSparseInvW c F0 F_cur
      { s with scratch := { s.scratch with ant_sz := asz, res_sz := rsz } } :=
  ⟨⟨hsp.1.core_ok, { hsp.1.scratch_ok with }⟩,
    hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

private theorem m6_sparseInvW_with_ws2 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) {ws2' : List (BitVec 32)}
    (hlen : ws2'.length = 2 * c.max_vars) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with work_stk2 := ws2' } } :=
  ⟨⟨hsp.1.core_ok, { hsp.1.scratch_ok with work_stk2_len := hlen }⟩,
    hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

private theorem m6_sparseInvW_of_prop_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
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

private theorem m6_tmp_lt_of_perm {xs orig : List (BitVec 32)} {sz B : Nat}
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

private theorem m6_tmp_shift_hole {xs orig : List (BitVec 32)} {sz j : Nat} {x prev : BitVec 32}
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

private theorem m6_take_snoc {α : Type} {xs : List α} {n : Nat} (hn : 0 < n) (hle : n ≤ xs.length) :
    xs.take n = xs.take (n - 1) ++ [xs[n - 1]'(by omega)] := by
  refine List.ext_getElem? fun k => ?_
  by_cases hk1 : k < n - 1
  · rw [List.getElem?_take, ite_eq_left (by omega), List.getElem?_append_left
        (by rw [List.length_take]; omega), List.getElem?_take, ite_eq_left hk1]
  · by_cases hk2 : k = n - 1
    · subst hk2
      rw [List.getElem?_take, ite_eq_left (by omega), List.getElem?_append_right
          (by rw [List.length_take]; omega)]
      have hlen : (xs.take (n - 1)).length = n - 1 := by rw [List.length_take]; omega
      rw [hlen, Nat.sub_self, List.getElem?_cons_zero, List.getElem?_eq_getElem (by omega)]
    · rw [List.getElem?_take, ite_eq_right (by omega), List.getElem?_append_right
          (by rw [List.length_take]; omega)]
      have hlen : (xs.take (n - 1)).length = n - 1 := by rw [List.length_take]; omega
      rw [hlen, show k - (n - 1) = (k - n) + 1 by omega, List.getElem?_cons_succ, List.getElem?_nil]

private theorem m6_entails_of_perm {F : CNF Nat} {xs ys : List Nat}
    (hp : xs.Perm ys) (h : F.EntailsClause (cnfClause ys)) :
    F.EntailsClause (cnfClause xs) := by
  rw [CNF.entails_clause_def] at h ⊢
  intro α hsat
  rw [clause_sat_cnfClause_iff]
  obtain ⟨l, hl, hls⟩ := (clause_sat_cnfClause_iff α ys).mp (h α hsat)
  exact ⟨l, hp.mem_iff.mpr hl, hls⟩

private theorem m6_take_eq_of_copy {ws2 tmp : List (BitVec 32)} {n : Nat}
    (hcp : ∀ j < n, ws2[j]? = tmp[j]?) : ws2.take n = tmp.take n := by
  refine List.ext_getElem? fun j => ?_
  by_cases hj : j < n
  · rw [List.getElem?_take, ite_eq_left hj, List.getElem?_take, ite_eq_left hj]; exact hcp j hj
  · rw [List.getElem?_take, ite_eq_right hj, List.getElem?_take, ite_eq_right hj]

private theorem m6_nodup_prefix_of_perm {xs : List (BitVec 32)} {lits : List Nat} {sz : Nat}
    (hsz : 1 ≤ sz) (hperm : ((xs.take sz).map BitVec.toNat).Perm lits)
    (hnd : (lits.map (· / 2)).Nodup) :
    ((xs.take (sz - 1)).map fun x => x.toNat / 2).Nodup := by
  have hnd_sz : (((xs.take sz).map BitVec.toNat).map (· / 2)).Nodup :=
    (hperm.map (· / 2)).nodup_iff.mpr hnd
  rw [List.map_map] at hnd_sz
  have htake : xs.take (sz - 1) = (xs.take sz).take (sz - 1) := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
  rw [htake, List.map_take]
  exact hnd_sz.sublist (List.take_sublist _ _)

private theorem m6_bv32_or_viv_garb (x : BitVec 32) :
    ((x ||| 0x00100000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) := by
  rw [BitVec.and_or_distrib_right,
    show (0x00100000#32 &&& 0x00080000#32) = 0#32 from rfl, BitVec.or_zero]

private theorem m6_bv32_or_viv_shrk (x : BitVec 32) :
    ((x ||| 0x00100000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) := by
  rw [BitVec.and_or_distrib_right,
    show (0x00100000#32 &&& 0x00800000#32) = 0#32 from rfl, BitVec.or_zero]

private theorem m6_sub_ref_in_refs {c : FullCfg} {s : FullState} {sub_ref : BitVec 64}
    (hlen : s.LengthsOk c) (hok : M6SubRefOk s sub_ref)
    (hne : sub_ref ≠ 0xFFFFFFFFFFFFFFFF#64) (hlt : sub_ref.toNat < s.core.arena_len) :
    sub_ref.toNat ∈ fullArenaClauseRefs s := by
  have har := c.harena; unfold dimacsBound at har
  have hale := hlen.core_ok.arena_len_le
  rcases hok with h1 | h2 | h3
  · exact absurd h1 hne
  · exfalso; rw [h2] at hlt
    have : (0xFFFFFFFFFFFFFFFE#64 : BitVec 64).toNat = 18446744073709551614 := rfl
    omega
  · exact h3

private theorem m6_fullMem_eq {c : FullCfg} {s1 s2 : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (h : s1 = s2) (hm : (FullMem c s1 ⋆ R) m) : (FullMem c s2 ⋆ R) m := h ▸ hm

end Helpers

/-! ## 3. `full_viv_inst_m6_wp` & `full_viv_finish_m6_wp` -/

section InstFinishProofs

private theorem m6_viv_inst_copy_commit_wp (Γ : Env)
    (hCommit : ∀ a m Q X, fullVivCommitM6Spec a m Q X →
      Γ "full_viv_commit_m6" [i64, i32, i32, i32] [i64] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s_d s_ic : FullState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {cref sz iolen lit : BitVec 32}
    {m_ic : Mem 64}
    (hsp0 : FullSparseInvW c F0 F_cur s)
    (hsp_ic : FullSparseInvW c F0 F_cur s_ic)
    (href0 : cref.toNat ∈ fullArenaClauseRefs s)
    (hng0 : fullArenaClauseGarb s cref.toNat = false)
    (hsz3 : 3 ≤ sz.toNat) (hsz_le : sz.toNat ≤ c.max_vars)
    (hperm0 : ((s.core.tmp.take sz.toNat).map BitVec.toNat).Perm
      (fullArenaClauseLits s cref.toNat))
    (htmp0_lt : ∀ k < sz.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hlit_eq : lit = s.core.tmp[sz.toNat - 1]'(by rw [hsp0.1.core_ok.tmp_len_arr]; omega))
    (hcv_ic : s_ic.core.cur_vars = s.core.cur_vars)
    (hal_ic : s_ic.core.arena_len = s.core.arena_len)
    (htmp_ic : s_ic.core.tmp = s.core.tmp)
    (htmp_d : s_d.core.tmp = s.core.tmp)
    (hrr_ic : s_ic.scratch.red_refs = s.scratch.red_refs)
    (hfl_ic : s_ic.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hrefs_ic : fullArenaClauseRefs s_ic = fullArenaClauseRefs s)
    (hng_ic : fullArenaClauseGarb s_ic cref.toNat = false)
    (hiol_le : iolen.toNat ≤ s_d.scratch.work_stk2.length)
    (hws2_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s_d.scratch.work_stk2.take iolen.toNat).map BitVec.toNat)))
    (hsub_ic : ∀ i < iolen.toNat,
      s_d.scratch.work_stk2[i]?.getD 0#32 = lit ^^^ 1#32 ∨
      ∃ j, j + 1 < sz.toNat ∧ s_d.scratch.work_stk2[i]?.getD 0#32 = s_d.core.tmp[j]?.getD 0#32)
    (hm_ic : (FullMem c s_ic ⋆ R) m_ic)
    (hQ : ∀ r s' m', FullSparseInvW c F0 F_cur s' →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.arena_len = s.core.arena_len →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X
      (Expr.group (sig := [[i32]])
        (fun Js => Blocks.cons (fun p_1 =>
          Expr.let_
            { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool rfl,
              args := (Arg.var p_1.fst, Arg.var (sz - 1#32), ()) } fun p_2 =>
          Expr.jnz (Arg.var p_2.fst)
            (Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                         args := (Arg.var p_1.fst, ()) } fun p =>
             Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                         args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
             Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var c.pWorkStk2, Arg.var p.fst, ()) } fun p =>
             Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                         args := (Arg.var p_1.fst, ()) } fun p_3 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                         args := (Arg.var p_3.fst, Arg.imm 4, ()) } fun p_4 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var c.pTmp, Arg.var p_4.fst, ()) } fun p_5 =>
             Expr.load i32 (Arg.var p_5.fst) fun ld =>
             Expr.store (Arg.var ld) (Arg.var p.fst)
               (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                            args := (Arg.var p_1.fst, Arg.imm 1, ()) } fun p =>
                Expr.jump Js.fst (Arg.var p.fst, ())))
            (Expr.call (as := [i64, i32, i32, i32]) (bs := [i64]) "full_viv_commit_m6"
              (Arg.var c.hdr, Arg.var cref, Arg.var (sz - 1#32), Arg.imm 4294967295, ())
              fun p => Expr.ret (Arg.var p.fst, ()))) Blocks.nil)
        (fun Js => Expr.jump Js.fst (Arg.imm 0, ()))) m_ic := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl0 := hsp0.1.core_ok
  let nsz : BitVec 32 := sz - 1#32
  have hnsz_nat : nsz.toNat = sz.toNat - 1 := by dsimp only [nsz]; bv_omega
  have hws2_len0 : s_ic.scratch.work_stk2.length = 2 * c.max_vars :=
    hsp_ic.1.scratch_ok.work_stk2_len
  refine wp_loop_inv (ts := [i32])
    (fun (k, ()) mk => ∃ ws2k : List (BitVec 32),
      k.toNat ≤ nsz.toNat ∧ ws2k.length = 2 * c.max_vars ∧
      (∀ j < k.toNat, ws2k[j]? = s_ic.core.tmp[j]?) ∧
      (FullMem c { s_ic with scratch := { s_ic.scratch with work_stk2 := ws2k } } ⋆ R) mk)
    (fun (k, ()) _ => nsz.toNat - k.toNat)
    (fun Jk hJk => by
      fvt_steps
      exact hJk (0#32, ()) m_ic ⟨s_ic.scratch.work_stk2, Nat.zero_le _, hws2_len0,
        fun _ hj => by simp at hj, hm_ic⟩)
    (fun Jk ⟨k, ⟨⟩⟩ mk ⟨ws2k, hk_le, hws2k_len, hcp_k, hmk⟩ ihk => ?_)
  fvt_steps
  · have hk_lt : k.toNat < nsz.toNat := by c0_bound
    have hk64 : (k.setWidth 64).toNat = k.toNat := bv32_setWidth64_toNat k
    have hk_tmp : (k.setWidth 64).toNat < s_ic.core.tmp.length := by
      rw [hk64, hsp_ic.1.core_ok.tmp_len_arr]; omega
    have hk_ws2 : (k.setWidth 64).toNat < ws2k.length := by rw [hk64]; omega
    have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
    fvt_steps
    let ws2k' := ws2k.set k.toNat (s_ic.core.tmp[k.toNat]'(by
      rw [hsp_ic.1.core_ok.tmp_len_arr]; omega))
    have htmp_eq : s_ic.core.tmp[(k.setWidth 64).toNat]'hk_tmp =
        s_ic.core.tmp[k.toNat]'(by rw [hsp_ic.1.core_ok.tmp_len_arr]; omega) :=
      Option.some.inj (by
        rw [← List.getElem?_eq_getElem hk_tmp, hk64,
          List.getElem?_eq_getElem (by rw [hsp_ic.1.core_ok.tmp_len_arr]; omega)])
    refine ihk (k + 1#32, ()) _ (by dsimp only; omega)
      ⟨ws2k', by omega, by simp [ws2k', hws2k_len], fun j hj => ?_, ?_⟩
    · rcases (by omega : j < k.toNat ∨ j = k.toNat) with hj' | rfl
      · dsimp only [ws2k']; rw [List.getElem?_set_ne (by omega)]; exact hcp_k j hj'
      · dsimp only [ws2k']
        rw [List.getElem?_set_self (by omega),
          List.getElem?_eq_getElem (by rw [hsp_ic.1.core_ok.tmp_len_arr]; omega)]
    · simpa only [ws2k', hk64, htmp_eq] using hm
  · have hk_eq : k.toNat = nsz.toNat := by c0_bound
    rw [hk_eq] at hcp_k
    let s_cm : FullState :=
      { s_ic with scratch := { s_ic.scratch with work_stk2 := ws2k } }
    have hsp_cm : FullSparseInvW c F0 F_cur s_cm :=
      m6_sparseInvW_with_ws2 hsp_ic hws2k_len
    have htk_eq : ws2k.take nsz.toNat = s.core.tmp.take (sz.toNat - 1) := by
      rw [hnsz_nat]
      exact m6_take_eq_of_copy (by simpa [hnsz_nat, htmp_ic] using hcp_k)
    have hrest_ent : (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((ws2k.take nsz.toNat).map BitVec.toNat)) := by
      rw [htk_eq]
      have hfull : (cnfOfClauses F_cur).EntailsClause
          (cnfClause (((s.core.tmp.take (sz.toNat - 1)).map BitVec.toNat) ++
            [lit.toNat])) := by
        have hsnoc : (s.core.tmp.take sz.toNat).map BitVec.toNat =
            ((s.core.tmp.take (sz.toNat - 1)).map BitVec.toNat) ++ [lit.toNat] := by
          rw [m6_take_snoc (by omega) (by rw [hcl0.tmp_len_arr]; omega),
            List.map_append, List.map_singleton, ← hlit_eq]
        rw [← hsnoc]
        exact m6_entails_of_perm hperm0 (hsp0.2.1.arena.entails cref.toNat href0 hng0)
      refine inst_resolve_entails hws2_ent hfull fun x hx => ?_
      rw [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [List.mem_iff_getElem] at hy
      obtain ⟨idx, hidx, hyeq⟩ := hy
      have hidx_lt : idx < iolen.toNat := by rw [List.length_take] at hidx; omega
      have hyeq' : s_d.scratch.work_stk2[idx]?.getD 0#32 = y := by
        have hlt_w : idx < s_d.scratch.work_stk2.length := by omega
        rw [List.getElem?_eq_getElem hlt_w, Option.getD_some]
        simpa [List.getElem_take] using hyeq
      rcases hsub_ic idx hidx_lt with heq_not | ⟨j, hj, heq_j⟩
      · left; rw [← hyeq', heq_not, bv32_xor1_toNat]
      · right; rw [List.mem_map]
        refine ⟨y, ?_, rfl⟩
        rw [List.mem_iff_getElem]
        refine ⟨j, by rw [List.length_take, hcl0.tmp_len_arr]; omega, ?_⟩
        rw [List.getElem_take, ← hyeq', heq_j, htmp_d]
        have hlt_t : j < s.core.tmp.length := by rw [hcl0.tmp_len_arr]; omega
        change s.core.tmp[j]'hlt_t = (s.core.tmp[j]?.getD 0#32)
        rw [List.getElem?_eq_getElem hlt_t, Option.getD_some]
    have hrest_lt : ∀ j < nsz.toNat,
        (ws2k[j]?.getD 0#32).toNat < 2 * s_cm.core.cur_vars := fun j hj => by
      have h1 : ws2k[j]? = s.core.tmp[j]? := by rw [hcp_k j hj, htmp_ic]
      rw [h1, show s_cm.core.cur_vars = s.core.cur_vars from hcv_ic]
      exact htmp0_lt j (by omega)
    have hrest_nd : ((ws2k.take nsz.toNat).map fun x => x.toNat / 2).Nodup := by
      rw [htk_eq]
      exact m6_nodup_prefix_of_perm (by omega) hperm0
        (hsp0.2.2.2.1 cref.toNat href0 hng0)
    c0_call hCommit
    refine ⟨c, F0, F_cur, s_cm, R, rfl, hsp_cm,
      (by simpa [s_cm, hrefs_ic] using href0),
      (by simpa [s_cm] using hng_ic), (by change nsz.toNat ≤ c.max_vars; omega),
      fun _ => ⟨hrest_lt, hrest_nd, hrest_ent⟩, hmk,
      fun r_c s_f m_f hsp_f _ hal_f _ hfl_f hrefs_f hrr_f _ hr_c h20_c hm_f => ?_⟩
    exact hQ r_c s_f m_f hsp_f (by rw [hfl_f]; exact hfl_ic)
      (hal_f.trans hal_ic) (hrefs_f.trans hrefs_ic) (hrr_f.trans hrr_ic)
      (Or.inr hr_c) h20_c hm_f

theorem full_viv_inst_m6_del_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAssign : ∀ a m Q X, Full.fullAssignSpec a m Q X →
      Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hPropIgn : ∀ a m Q X, Full.fullPropagateIgnoreDelSpec a m Q X →
      Γ "full_propagate_ignore" [i64, i64] [i64] a m Q X)
    (hDeduce : ∀ a m Q X, fullVivDeduceM6Spec a m Q X →
      Γ "full_viv_deduce_m6" [i64, i32, i32, i32] [i32] a m Q X)
    (hInstChk : ∀ a m Q X, fullVivInstCheckM6Spec a m Q X →
      Γ "full_viv_inst_check_m6" [i64, i32, i32, i32] [.bool] a m Q X)
    (hCommit : ∀ a m Q X, fullVivCommitM6Spec a m Q X →
      Γ "full_viv_commit_m6" [i64, i32, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, fullVivInstM6Spec a m Q X →
      Func.wp Γ full_viv_inst_m6_body a m Q X := by
  rintro ⟨h, cref, sz, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hsp0, href0, hng0, hsz0, hsz_le, hperm0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl0 := hsp0.1.core_ok
  have hcl0_le : s.core.cur_level ≤ c.max_vars := by
    have := hsp0.2.1.cur_level_le; have := hcl0.trail_end_le; have := hcl0.cur_vars_le; omega
  have hcl0_lt64 : s.core.cur_level < 2 ^ 64 := by omega
  have htmp0_lt : ∀ k < sz.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars := by
    intro k hk
    have hmem := (vivTmp_mem_of_perm (by rw [hcl0.tmp_len_arr]; omega) hperm0).1 k hk
    exact hsp0.2.1.arena.lits_lt cref.toNat href0 hng0 _ hmem
  unfold Func.wp full_viv_inst_m6_body
  fvt_steps
  · exact hQ 0#64 s m0 hsp0 (Nat.le_refl _) rfl rfl rfl (Or.inl rfl) (fun h => by cases h) hm0
  · exact hQ 0#64 s m0 hsp0 (Nat.le_refl _) rfl rfl rfl (Or.inl rfl) (fun h => by cases h) hm0
  · have hcl0_pos : 0 < s.core.cur_level := by
      have hne : BitVec.ofNat 64 s.core.cur_level ≠ 0#64 := by c0_bound
      exact Nat.pos_of_ne_zero fun h0 => hne (by simp [h0])
    have hsz3 : 3 ≤ sz.toNat := by c0_bound
    have hsz1_nat : (sz - 1#32).toNat = sz.toNat - 1 := by bv_omega
    have hsz1_64 : ((sz - 1#32).setWidth 64).toNat = sz.toNat - 1 := by
      rw [bv32_setWidth64_toNat, hsz1_nat]
    have hsz1_tmp : ((sz - 1#32).setWidth 64).toNat < s.core.tmp.length := by
      rw [hsz1_64, hcl0.tmp_len_arr]; omega
    let lit := s.core.tmp[((sz - 1#32).setWidth 64).toNat]'hsz1_tmp
    have hlit_eq : lit = s.core.tmp[sz.toNat - 1]'(by rw [hcl0.tmp_len_arr]; omega) :=
      Option.some.inj (by
        rw [← List.getElem?_eq_getElem hsz1_tmp, hsz1_64,
          List.getElem?_eq_getElem (by rw [hcl0.tmp_len_arr]; omega)])
    have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by
      have h := htmp0_lt (sz.toNat - 1) (by omega)
      rw [List.getElem?_eq_getElem (by rw [hcl0.tmp_len_arr]; omega), Option.getD_some] at h
      rwa [hlit_eq]
    have hlit_vl : (lit.setWidth 64).toNat < s.core.vals.length := by
      rw [bv32_setWidth64_toNat, hcl0.vals_len]; have := hcl0.cur_vars_le; omega
    have hlit_lv : ((lit >>> (1#32 : BitVec 32).toNat).setWidth 64).toNat < s.core.lvl.length := by
      rw [bv32_setWidth64_toNat, hcl0.lvl_len, show (1#32 : BitVec 32).toNat = 1 from rfl,
        bv32_lshr_1]
      have := hcl0.cur_vars_le; omega
    have hlit_rs : ((lit >>> (1#32 : BitVec 32).toNat).setWidth 64).toNat < s.core.rsns.length := by
      rw [bv32_setWidth64_toNat, hcl0.rsns_len, show (1#32 : BitVec 32).toNat = 1 from rfl,
        bv32_lshr_1]
      have := hcl0.cur_vars_le; omega
    have hret0 : Q (0#64, ()) m0 :=
      hQ 0#64 s m0 hsp0 (Nat.le_refl _) rfl rfl rfl (Or.inl rfl) (fun h => by cases h) hm0
    fvt_steps
    all_goals try exact hret0
    have hbt_tgt : (BitVec.ofNat 64 s.core.cur_level - 1).toNat = s.core.cur_level - 1 := by
      have hcv : (BitVec.ofNat 64 s.core.cur_level).toNat = s.core.cur_level := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl0_lt64]
      have h1 : (1 : BitVec 64).toNat = 1 := rfl
      rw [BitVec.toNat_sub, hcv, h1]; omega
    c0_call hBacktrack
    refine ⟨c, s, R, rfl, hsp0.1, hcl0_lt64, fun _ => by rw [hbt_tgt]; omega,
      hsp0.2.1.trail_lits_lt, hm0,
      fun vals_b lvl_b rsns_b trl_b tp_b te_b prop_b cl_b unass_b sc_b m_bt
        hlen_bt _ _ _ hpres_bt hsc_bt _ _ hw_bt _ hm_bt => ?_⟩
    have hle_bt : (BitVec.ofNat 64 s.core.cur_level - 1).toNat ≤ s.core.cur_level := by
      rw [hbt_tgt]; omega
    have hsp_bt : FullSparseInvW c F0 F_cur _ :=
      FullVivTop.FullSparseInvW.of_backtrack hsp0 hle_bt hlen_bt hpres_bt
        (hw_bt F0 F_cur hsp0.2.1 hle_bt)
    rcases hsc_bt with ⟨ta', ba', pt', pb', hp', ps', hl', qsi', qss', hsc_eq⟩
    let s_bt : FullState :=
      { s with
        core := { s.core with
          vals := vals_b, lvl := lvl_b, rsns := rsns_b, trl := trl_b,
          trail_pos := tp_b, trail_end := te_b, propagated := prop_b, cur_level := cl_b,
          unassigned := unass_b }
        scratch := sc_b }
    have hsp_bt' : FullSparseInvW c F0 F_cur s_bt := hsp_bt
    have hm_bt' : (FullMem c s_bt ⋆ R) m_bt := hm_bt
    have hrr_bt : s_bt.scratch.red_refs = s.scratch.red_refs := by dsimp only [s_bt]; rw [hsc_eq]
    have hlit_vl_bt : (lit.setWidth 64).toNat < s_bt.core.vals.length := by
      rw [bv32_setWidth64_toNat, hsp_bt'.1.core_ok.vals_len]; have := hcl0.cur_vars_le; omega
    have hlit_lt_bt : lit.toNat < 2 * s_bt.core.cur_vars := hlit_lt
    have hbt_cl_le : s_bt.core.cur_level ≤ c.max_vars := by
      have := hsp_bt'.2.1.cur_level_le; have := hsp_bt'.1.core_ok.trail_end_le
      have := hsp_bt'.1.core_ok.cur_vars_le; omega
    have hret_bt : Q (0#64, ()) m_bt :=
      hQ 0#64 s_bt m_bt hsp_bt' (Nat.le_refl _) rfl rfl hrr_bt (Or.inl rfl)
        (fun h => by cases h) hm_bt'
    fvt_steps
    all_goals try exact hret_bt
    have hlv0 : s_bt.core.vals[lit.toNat]?.getD 0#8 = 0#8 := by
      have hlt_v : lit.toNat < s_bt.core.vals.length := by
        rw [hsp_bt'.1.core_ok.vals_len]; have := hcl0.cur_vars_le; omega
      rw [List.getElem?_eq_getElem hlt_v, Option.getD_some]
      have hse : (s_bt.core.vals[(lit.setWidth 64).toNat]'hlit_vl_bt).signExtend 32 = 0#32 := by
        first | assumption | c0_bound
      have hget : s_bt.core.vals[(lit.setWidth 64).toNat]'hlit_vl_bt =
          s_bt.core.vals[lit.toNat]'hlt_v := Option.some.inj (by
        rw [← List.getElem?_eq_getElem hlit_vl_bt, bv32_setWidth64_toNat,
          List.getElem?_eq_getElem hlt_v])
      rw [hget] at hse
      exact (bv8_sext32_eq0_iff _).mp hse
    have hnot_lit_lt : (lit ^^^ 1#32).toNat < 2 * s_bt.core.cur_vars := by
      rw [bv32_xor1_toNat]; exact bv32_xor1_lt_even hlit_lt_bt
    have hnot_lit_zero : s_bt.core.vals[(lit ^^^ 1#32).toNat]?.getD 0#8 = 0#8 := by
      rw [bv32_xor1_toNat]; exact vals_xor1_eq_zero hsp_bt'.2.1 hlit_lt_bt hlv0
    have hte_lt := hsp_bt'.2.1.trail_end_lt_of_unassigned hlit_lt_bt hlv0
    have hnlvl_le : s_bt.core.cur_level + 1 ≤ c.max_vars := by
      have := hsp_bt'.2.1.cur_level_le; have := hsp_bt'.1.core_ok.cur_vars_le; omega
    have hnlvl_nat : (BitVec.ofNat 64 s_bt.core.cur_level + 1).toNat =
        s_bt.core.cur_level + 1 := by bv_omega
    have hnlvl_ft : (BitVec.ofNat 64 s_bt.core.cur_level + 1).toNat <
        s_bt.core.frame_trail.length := by
      rw [hnlvl_nat, hsp_bt'.1.core_ok.frame_trail_len]; omega
    have hnlvl_fd : (BitVec.ofNat 64 s_bt.core.cur_level + 1).toNat <
        s_bt.core.frame_dec.length := by
      rw [hnlvl_nat, hsp_bt'.1.core_ok.frame_dec_len]; omega
    fvt_steps
    let nlvl := s_bt.core.cur_level + 1
    let ftrl' := s_bt.core.frame_trail.set nlvl (BitVec.ofNat 32 s_bt.core.trail_end)
    let fdec' := s_bt.core.frame_dec.set nlvl lit
    let s_pre : FullState :=
      { s_bt with core :=
        { s_bt.core with frame_trail := ftrl', frame_dec := fdec', cur_level := nlvl } }
    have hlen_pre : s_pre.LengthsOk c :=
      ⟨{ hsp_bt'.1.core_ok with
           frame_trail_len := by simp [s_pre, ftrl', hsp_bt'.1.core_ok.frame_trail_len],
           frame_dec_len := by simp [s_pre, fdec', hsp_bt'.1.core_ok.frame_dec_len] },
       hsp_bt'.1.scratch_ok⟩
    have hte_bv : BitVec.setWidth 32 (BitVec.ofNat 64 s_bt.core.trail_end) =
        BitVec.ofNat 32 s_bt.core.trail_end := by apply BitVec.eq_of_toNat_eq; simp
    have hnot_guard : ¬ (s_pre.core.cur_vars ≤ lit.toNat / 2 ∨
        c.max_vars ≤ s_pre.core.trail_end ∨ s_pre.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
      intro hor; rcases hor with h1 | h2 | h3
      · dsimp only [s_pre] at h1; omega
      · have := hsp_bt'.1.core_ok.cur_vars_le; dsimp only [s_pre] at h2; omega
      · exact h3 hlv0
    c0_call hAssign
    refine ⟨c, s_pre, R, rfl, hlen_pre, by dsimp [s_pre, nlvl]; omega,
      (by simp only [s_pre, nlvl, ftrl', fdec', ← hnlvl_nat, ← hte_bv]; exact (by assumption)),
      ?_⟩
    refine (ite_eq_right hnot_guard).mpr ?_
    dsimp only
    intro flags' unass' phases' m_as hfll' hphl' hm_as
    have hnlvl_ne0 : nlvl ≠ 0 := by omega
    simp only [show s_pre.core.cur_level ≠ 0 from hnlvl_ne0, ↓reduceIte] at hm_as ⊢
    have hsp_as_raw :=
      (vivDecideAssign_preserves_sparseW (unass' := unass') (unfl' := s_bt.core.unflushed)
        hsp_bt' hnot_lit_lt hnot_lit_zero hfll' hphl').2.1
    rw [m6_bv32_xor1_xor1] at hsp_as_raw
    let s_as : FullState :=
      { s_bt with
        core :=
          { s_bt.core with
            vals := (s_bt.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
            flags := flags',
            lvl := s_bt.core.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 nlvl),
            rsns := s_bt.core.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32,
            trl := s_bt.core.trl.set s_bt.core.trail_end lit,
            trail_pos := s_bt.core.trail_pos.set (lit.toNat / 2)
              (BitVec.ofNat 32 s_bt.core.trail_end),
            frame_trail := ftrl', frame_dec := fdec',
            trail_end := s_bt.core.trail_end + 1, cur_level := nlvl,
            unassigned := unass' }
        scratch := { s_bt.scratch with phases := phases' } }
    have hsp_as : FullSparseInvW c F0 F_cur s_as := hsp_as_raw
    fvt_steps
    let s_c : FullState :=
      { s_as with core := { s_as.core with confl_type := 0#64, confl_ref := 0xFFFFFFFF#64 } }
    have hsp_c : FullSparseInvW c F0 F_cur s_c :=
      FullVivTop.FullSparseInvW.with_confl hsp_as 0#64 0xFFFFFFFF#64
    c0_call hPropIgn
    refine ⟨c, F0, F_cur, s_c, R, rfl, hsp_c.1, hsp_c.2.1, hsp_c.2.2.2.2.2, (by assumption),
      fun pr vals_p flags_p lvl_p rsns_p trl_p tp_p te_p prop_p unass_p unfl_p
        wvec_p arena_p wstk_p wlen_p wu_p fuel_p ctype_p cref_p c0_p c1_p oom_p
        ticks_p wsort_p phases_p delayed_p m_p hlen_p hw_p _ hperm_p hfl_p _ _ hpr1 _ _ hm_p => ?_⟩
    let s_p : FullState :=
      { s_c with
        core := { s_c.core with
          vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p,
          trl := trl_p, trail_pos := tp_p, trail_end := te_p, propagated := prop_p,
          unassigned := unass_p, unflushed := unfl_p, wvec := wvec_p,
          arena := arena_p, wstk := wstk_p, wlen := wlen_p, wusable := wu_p,
          fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
          confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
        scratch := { s_c.scratch with
          search_ticks := ticks_p, wsort := wsort_p, phases := phases_p, delayed := delayed_p } }
    have hsp_p : FullSparseInvW c F0 F_cur s_p :=
      m6_sparseInvW_of_prop_canon hsp_c hlen_p hw_p hperm_p
    have hm_p' : (FullMem c s_p ⋆ R) m_p := hm_p
    have hcv_p : s_p.core.cur_vars = s.core.cur_vars := rfl
    have hal_p : s_p.core.arena_len = s.core.arena_len := rfl
    have htmp_p : s_p.core.tmp = s.core.tmp := rfl
    have hrr_p : s_p.scratch.red_refs = s.scratch.red_refs := hrr_bt
    have hrefs_p : fullArenaClauseRefs s_p = fullArenaClauseRefs s := hperm_p.2.1
    have href_p : cref.toNat ∈ fullArenaClauseRefs s_p := hrefs_p ▸ href0
    have hprops_p := hperm_p.2.2 cref.toNat href0
    have hng_p : fullArenaClauseGarb s_p cref.toNat = false := hprops_p.2.1.trans hng0
    have hcl_p_eq : s_p.core.cur_level = nlvl := rfl
    have hcl_p_lt64 : s_p.core.cur_level < 2 ^ 64 := by omega
    have hfl_p' : s_p.core.fuel.toNat ≤ s.core.fuel.toNat := hfl_p
    have hcok_p_fn : pr = 1#64 → FullVivifySpecs.FullVivConflictOk F_cur s_p :=
      fun h => m6_conflictOkW_to_viv (hpr1 h).2.2.1
    clear_value s_p s_c s_as s_pre s_bt
    clear hm_p hsp_c hsp_as hsp_as_raw hlen_pre hnot_guard hte_bv hsp_bt' hsp_bt hAssign hPropIgn
      hperm_p hprops_p hpr1 hw_p hlen_p hfl_p
    have hbt_p_tgt : (BitVec.ofNat 64 s_p.core.cur_level - 1).toNat =
        s_p.core.cur_level - 1 := by
      have hcv : (BitVec.ofNat 64 s_p.core.cur_level).toNat = s_p.core.cur_level := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_p_lt64]
      have h1 : (1 : BitVec 64).toNat = 1 := rfl
      rw [BitVec.toNat_sub, hcv, h1]; omega
    fvt_steps
    · -- `pr == 2ULL`: backtrack to 0 and return `2ULL`
      c0_call hBacktrack
      refine ⟨c, s_p, R, rfl, hsp_p.1, hcl_p_lt64,
        (by have h0n : BitVec.toNat (0 : BitVec 64) = 0 := rfl; rw [h0n]; intro; omega),
        hsp_p.2.1.trail_lits_lt, hm_p',
        fun vals_2 lvl_2 rsns_2 trl_2 tp_2 te_2 prop_2 cl_2 unass_2 sc_2 m_2
          hlen_2 _ _ _ hpres_2 hsc_2 _ _ hw_2 _ hm_2 => ?_⟩
      have hsp_2 : FullSparseInvW c F0 F_cur _ :=
        FullVivTop.FullSparseInvW.of_backtrack hsp_p (Nat.zero_le _) hlen_2 hpres_2
          (hw_2 F0 F_cur hsp_p.2.1 (Nat.zero_le _))
      rcases hsc_2 with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
      fvt_steps
      exact hQ 2#64 _ m_2 hsp_2 hfl_p' hal_p hrefs_p hrr_p (Or.inr (Or.inr (Or.inl rfl)))
        (fun h => by cases h) hm_2
    · -- `pr != 1ULL`: backtrack 1 level and return `0ULL`
      c0_call hBacktrack
      refine ⟨c, s_p, R, rfl, hsp_p.1, hcl_p_lt64, fun _ => by rw [hbt_p_tgt]; omega,
        hsp_p.2.1.trail_lits_lt, hm_p',
        fun vals_2 lvl_2 rsns_2 trl_2 tp_2 te_2 prop_2 cl_2 unass_2 sc_2 m_2
          hlen_2 _ _ _ hpres_2 hsc_2 _ _ hw_2 _ hm_2 => ?_⟩
      have hle_bt2 : (BitVec.ofNat 64 s_p.core.cur_level - 1).toNat ≤ s_p.core.cur_level := by
        rw [hbt_p_tgt]; omega
      have hsp_2 : FullSparseInvW c F0 F_cur _ :=
        FullVivTop.FullSparseInvW.of_backtrack hsp_p hle_bt2 hlen_2 hpres_2
          (hw_2 F0 F_cur hsp_p.2.1 hle_bt2)
      rcases hsc_2 with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
      fvt_steps
      exact hQ 0#64 _ m_2 hsp_2 hfl_p' hal_p hrefs_p hrr_p (Or.inl rfl) (fun h => by cases h) hm_2
    · -- `pr == 1ULL`: deduce + inst_check + copy `tmp[0 ..< sz-1)` + commit
      have hpr_eq1 : pr = 1#64 := by c0_bound
      have hcok_p : FullVivifySpecs.FullVivConflictOk F_cur s_p := hcok_p_fn hpr_eq1
      c0_call hDeduce
      refine ⟨c, F0, F_cur, s_p, R, rfl, hsp_p, href_p, hng_p, hsz_le,
        (by rw [htmp_p, hcv_p]; exact htmp0_lt),
        fun _ => Or.inl hcok_p, fun h => absurd rfl h, hm_p',
        fun iolen mrk_d lm_d ws1_d ws2_d asz_d rsz_d m_d hsp_d _ hiolen_ok hm_d => ?_⟩
      let s_d : FullState :=
        { s_p with
          core := { s_p.core with mrk := mrk_d, lit_mark := lm_d }
          scratch := { s_p.scratch with
            work_stk1 := ws1_d, work_stk2 := ws2_d, ant_sz := asz_d, res_sz := rsz_d } }
      have hsp_d' : FullSparseInvW c F0 F_cur s_d := hsp_d
      have hm_d' : (FullMem c s_d ⋆ R) m_d := hm_d
      have hcv_d : s_d.core.cur_vars = s.core.cur_vars := hcv_p
      have hal_d : s_d.core.arena_len = s.core.arena_len := hal_p
      have htmp_d : s_d.core.tmp = s.core.tmp := htmp_p
      have hrr_d : s_d.scratch.red_refs = s.scratch.red_refs := hrr_p
      have hcl_d : s_d.core.cur_level = nlvl := hcl_p_eq
      have hfl_d : s_d.core.fuel = s_p.core.fuel := rfl
      have hrefs_d : fullArenaClauseRefs s_d = fullArenaClauseRefs s := hrefs_p
      have hng_d : fullArenaClauseGarb s_d cref.toNat = false := hng_p
      have hws2_d_eq : s_d.scratch.work_stk2 = ws2_d := rfl
      clear_value s_d; clear hsp_d hm_d hDeduce hcok_p hcok_p_fn
      have hbt_ret0 : ∀ (s_f : FullState) (m_f : Mem 64),
          FullSparseInvW c F0 F_cur s_f → s_f.core.cur_level = nlvl →
          s_f.core.fuel = s_p.core.fuel → s_f.core.arena_len = s.core.arena_len →
          fullArenaClauseRefs s_f = fullArenaClauseRefs s →
          s_f.scratch.red_refs = s.scratch.red_refs →
          (FullMem c s_f ⋆ R) m_f →
          wp Γ Q X
            (Expr.call (as := [i64, i64]) (bs := []) "full_backtrack"
              (Arg.var c.hdr, Arg.var (BitVec.ofNat 64 s_f.core.cur_level - 1), ())
              fun _ => Expr.ret (Arg.imm 0, ())) m_f := by
        intro s_f m_f hsp_f hcl_f hfl_f hal_f hrefs_f hrr_f hm_f
        have hcl_f_lt : s_f.core.cur_level < 2 ^ 64 := by omega
        have htgt_f : (BitVec.ofNat 64 s_f.core.cur_level - 1).toNat =
            s_f.core.cur_level - 1 := by
          have hcv : (BitVec.ofNat 64 s_f.core.cur_level).toNat = s_f.core.cur_level := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_f_lt]
          have h1 : (1 : BitVec 64).toNat = 1 := rfl
          rw [BitVec.toNat_sub, hcv, h1]; omega
        c0_call hBacktrack
        refine ⟨c, s_f, R, rfl, hsp_f.1, hcl_f_lt, fun _ => by rw [htgt_f]; omega,
          hsp_f.2.1.trail_lits_lt, hm_f,
          fun vals_2 lvl_2 rsns_2 trl_2 tp_2 te_2 prop_2 cl_2 unass_2 sc_2 m_2
            hlen_2 _ _ _ hpres_2 hsc_2 _ _ hw_2 _ hm_2 => ?_⟩
        have hle_f : (BitVec.ofNat 64 s_f.core.cur_level - 1).toNat ≤ s_f.core.cur_level := by
          rw [htgt_f]; omega
        have hsp_2 : FullSparseInvW c F0 F_cur _ :=
          FullVivTop.FullSparseInvW.of_backtrack hsp_f hle_f hlen_2 hpres_2
            (hw_2 F0 F_cur hsp_f.2.1 hle_f)
        rcases hsc_2 with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
        fvt_steps
        exact hQ 0#64 _ m_2 hsp_2 (by rw [hfl_f]; exact hfl_p') hal_f hrefs_f hrr_f
          (Or.inl rfl) (fun h => by cases h) hm_2
      fvt_steps
      · first
        | exact hbt_ret0 s_d m_d hsp_d' hcl_d hfl_d hal_d hrefs_d hrr_d hm_d'
        | (apply hJ; fvt_steps
           exact hbt_ret0 s_d m_d hsp_d' hcl_d hfl_d hal_d hrefs_d hrr_d hm_d')
      · have hiolen_ne : iolen ≠ 0xFFFFFFFF#32 := by c0_bound
        obtain ⟨hiol_le, hws2_lt, _, hws2_ent⟩ := hiolen_ok hiolen_ne
        have hiol_mv : iolen.toNat ≤ c.max_vars := Nat.le_trans hiol_le hsp_p.1.core_ok.cur_vars_le
        fvt_steps
        c0_call hInstChk
        refine ⟨c, F0, F_cur, s_d, R, rfl, hsp_d', by omega, hsz_le, hiol_mv,
          (by rw [htmp_d, hcv_d]; exact htmp0_lt),
          (by rw [hws2_d_eq, hcv_d, ← hcv_p]; exact hws2_lt), hm_d',
          fun ok lm_ic m_ic hsp_ic hok_ic hm_ic => ?_⟩
        let s_ic : FullState := { s_d with core := { s_d.core with lit_mark := lm_ic } }
        have hsp_ic' : FullSparseInvW c F0 F_cur s_ic := hsp_ic
        have hm_ic' : (FullMem c s_ic ⋆ R) m_ic := hm_ic
        have hcv_ic : s_ic.core.cur_vars = s.core.cur_vars := hcv_d
        have hal_ic : s_ic.core.arena_len = s.core.arena_len := hal_d
        have htmp_ic : s_ic.core.tmp = s.core.tmp := htmp_d
        have hrr_ic : s_ic.scratch.red_refs = s.scratch.red_refs := hrr_d
        have hcl_ic : s_ic.core.cur_level = nlvl := hcl_d
        have hfl_ic : s_ic.core.fuel = s_p.core.fuel := hfl_d
        have hrefs_ic : fullArenaClauseRefs s_ic = fullArenaClauseRefs s := hrefs_d
        have hng_ic : fullArenaClauseGarb s_ic cref.toNat = false := hng_d
        clear_value s_ic; clear hsp_ic hm_ic hInstChk
        fvt_to_group
        · -- `ok = true`: copy `tmp[0 ..< sz - 1)` to `work_stk2`, call `full_viv_commit_m6`
          have hok_t : ok = true := by c0_bound
          have hsub_ic := hok_ic hok_t
          exact m6_viv_inst_copy_commit_wp (iolen := iolen) Γ hCommit hsp0 hsp_ic' href0
            hng0 hsz3 hsz_le hperm0 htmp0_lt hlit_eq hcv_ic hal_ic htmp_ic htmp_d hrr_ic
            (by rw [hfl_ic]; exact hfl_p') hrefs_ic hng_ic
            (by rw [hsp_d'.1.scratch_ok.work_stk2_len]; omega)
            (by rw [hws2_d_eq]; exact hws2_ent) hsub_ic hm_ic' hQ
        · -- `ok = false`: backtrack 1 level and return `0ULL`
          fvt_steps
          first
          | exact hbt_ret0 s_ic m_ic hsp_ic' hcl_ic hfl_ic hal_ic hrefs_ic hrr_ic hm_ic'
          | (apply hJ; fvt_steps
             exact hbt_ret0 s_ic m_ic hsp_ic' hcl_ic hfl_ic hal_ic hrefs_ic hrr_ic hm_ic')

theorem full_viv_inst_m6_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAssign : ∀ a m Q X, Full.fullAssignSpec a m Q X →
      Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hPropIgn : ∀ a m Q X, Full.fullPropagateIgnoreSpec a m Q X →
      Γ "full_propagate_ignore" [i64, i64] [i64] a m Q X)
    (hDeduce : ∀ a m Q X, fullVivDeduceM6Spec a m Q X →
      Γ "full_viv_deduce_m6" [i64, i32, i32, i32] [i32] a m Q X)
    (hInstChk : ∀ a m Q X, fullVivInstCheckM6Spec a m Q X →
      Γ "full_viv_inst_check_m6" [i64, i32, i32, i32] [.bool] a m Q X)
    (hCommit : ∀ a m Q X, fullVivCommitM6Spec a m Q X →
      Γ "full_viv_commit_m6" [i64, i32, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, fullVivInstM6Spec a m Q X →
      Func.wp Γ full_viv_inst_m6_body a m Q X :=
  full_viv_inst_m6_del_wp Γ hBacktrack hAssign
    (fun a m Q X h => hPropIgn a m Q X (Full.fullPropagateIgnoreSpec_of_del h))
    hDeduce hInstChk hCommit

theorem full_viv_finish_m6_wp (Γ : Env)
    (hDeduce : ∀ a m Q X, fullVivDeduceM6Spec a m Q X →
      Γ "full_viv_deduce_m6" [i64, i32, i32, i32] [i32] a m Q X)
    (hMarkGarb : ∀ a m Q X, fullVivMarkGarbM6Spec a m Q X →
      Γ "full_viv_mark_garb_m6" [i64, i32] [] a m Q X)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hCommit : ∀ a m Q X, fullVivCommitM6Spec a m Q X →
      Γ "full_viv_commit_m6" [i64, i32, i32, i32] [i64] a m Q X)
    (hReest : ∀ a m Q X, fullVivReestablishM6Spec a m Q X →
      Γ "full_viv_reestablish_m6" [i64, i32] [] a m Q X)
    (hInst : ∀ a m Q X, fullVivInstM6Spec a m Q X →
      Γ "full_viv_inst_m6" [i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, fullVivFinishM6Spec a m Q X →
      Func.wp Γ full_viv_finish_m6_body a m Q X := by
  rintro ⟨h, cref, sz, confl, implied, all_done, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hsp0, hsz_le, href0, hng0, hsz0, hperm0,
     hcok0, himpl0, hfal0, hm0, hQ⟩
  have hmx := c.hmaxv; have har_cap := c.harena; unfold dimacsBound at hmx har_cap
  have htmp0_lt : ∀ k < sz.toNat, (s.core.tmp[k]?.getD 0#32).toNat < 2 * s.core.cur_vars := by
    intro k hk
    have hmem := (vivTmp_mem_of_perm (by rw [hsp0.1.core_ok.tmp_len_arr]; omega) hperm0).1 k hk
    exact hsp0.2.1.arena.lits_lt cref.toNat href0 hng0 _ hmem
  unfold Func.wp full_viv_finish_m6_body
  fvt_to_group
  let sb1 : FullState :=
    { s with scratch := { s.scratch with ant_sz := 0xFFFFFFFFFFFFFFFF#64, res_sz := 0#64 } }
  have hspb1 : FullSparseInvW c F0 F_cur sb1 :=
    m6_sparseInvW_with_ant_res hsp0 0xFFFFFFFFFFFFFFFF#64 0#64
  have hsb1_core : sb1.core = s.core := rfl
  have hsb1_rr : sb1.scratch.red_refs = s.scratch.red_refs := rfl
  have hsb1_sub : M6SubRefOk sb1 sb1.scratch.ant_sz := Or.inl rfl
  have hmb1 : (FullMem c sb1 ⋆ R) m := hm
  clear_value sb1; clear hm
  -- Join after `if (confl || implied != 0xFFFFFFFFu || all_done)`
  refine wp_join_group (ts := [i32, .bool])
    (fun (olen, has_ded, ()) md => ∃ sd : FullState,
      FullSparseInvW c F0 F_cur sd ∧
      sd.core.cur_vars = s.core.cur_vars ∧ sd.core.arena = s.core.arena ∧
      sd.core.arena_len = s.core.arena_len ∧ sd.core.fuel = s.core.fuel ∧
      sd.core.tmp = s.core.tmp ∧ sd.scratch.red_refs = s.scratch.red_refs ∧
      M6SubRefOk sd sd.scratch.ant_sz ∧
      (has_ded = true →
        olen.toNat ≤ sd.core.cur_vars ∧
        (∀ k < olen.toNat,
          (sd.scratch.work_stk2[k]?.getD 0#32).toNat < 2 * sd.core.cur_vars) ∧
        ((sd.scratch.work_stk2.take olen.toNat).map fun x => x.toNat / 2).Nodup ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((sd.scratch.work_stk2.take olen.toNat).map BitVec.toNat))) ∧
      (FullMem c sd ⋆ R) md) ?_ ?_
  · rintro _ ⟨olen, has_ded, ⟨⟩⟩ md
      ⟨sd, hspd, hcvd, hard, hald, hfld, htmpd, hrrd, hsubd, hded_ok, hmd⟩
    clear hspb1 hsb1_core hsb1_rr hsb1_sub hmb1 sb1 hDeduce
    have hrefs_d : fullArenaClauseRefs sd = fullArenaClauseRefs s := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [hard, hald]
    have href_d : cref.toNat ∈ fullArenaClauseRefs sd := hrefs_d ▸ href0
    have hng_d : fullArenaClauseGarb sd cref.toNat = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [hard]; exact hng0
    have hsz_d : fullArenaClauseSize sd cref.toNat = sz.toNat := by
      unfold fullArenaClauseSize fullArenaClauseSizeCore; rw [hard]; exact hsz0
    have hperm_d : ((sd.core.tmp.take sz.toNat).map BitVec.toNat).Perm
        (fullArenaClauseLits sd cref.toNat) := by
      have hl : fullArenaClauseLits sd cref.toNat = fullArenaClauseLits s cref.toNat := by
        unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [hard]
      rw [htmpd, hl]; exact hperm0
    have hcr_d_nat : (cref.setWidth 64).toNat = cref.toNat := bv32_setWidth64_toNat cref
    have hcr_d_lt : cref.toNat < sd.core.arena.length := by
      have := (hspd.2.1.arena.refs_wf cref.toNat href_d).1
      have := hspd.1.core_ok.arena_len_arr; have := hspd.1.core_ok.arena_len_le; omega
    have hcr_d_bv : (cref.setWidth 64).toNat < sd.core.arena.length := by omega
    have hfl_d_le : sd.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hfld]; exact Nat.le_refl _
    fvt_to_group
    · -- Branch 1: `sub_ref != 0xFFFFFFFFFFFFFFFFULL`
      have hsub_ne : sd.scratch.ant_sz ≠ 0xFFFFFFFFFFFFFFFF#64 := by c0_bound
      refine wp_join_group (ts := [])
        (fun () ms => ∃ ss : FullState,
          FullSparseInvW c F0 F_cur ss ∧ ss.core.fuel = sd.core.fuel ∧
          ss.core.arena_len = sd.core.arena_len ∧
          fullArenaClauseRefs ss = fullArenaClauseRefs sd ∧
          ss.scratch.red_refs = sd.scratch.red_refs ∧ (FullMem c ss ⋆ R) ms) ?_ ?_
      · rintro _ ⟨⟩ ms ⟨ss, hsps, hfls, hals, hrefss, hrrs, hms⟩
        fvt_steps
        c0_call hMarkGarb
        refine ⟨c, F0, F_cur, ss, R, rfl, hsps, hrefss ▸ href_d, hms,
          fun sm mm hspm _ halm _ hflm hrefsm hrrm _ hmm => ?_⟩
        have hcl_m_le : sm.core.cur_level ≤ c.max_vars := by
          have := hspm.2.1.cur_level_le; have := hspm.1.core_ok.trail_end_le
          have := hspm.1.core_ok.cur_vars_le; omega
        have hcl_m_lt : sm.core.cur_level < 2 ^ 64 := by omega
        have hfl_m_le : sm.core.fuel.toNat ≤ s.core.fuel.toNat := by
          rw [hflm, hfls]; exact hfl_d_le
        refine wp_join_group (ts := [])
          (fun () mf => ∃ sf : FullState,
            FullSparseInvW c F0 F_cur sf ∧ sf.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            sf.core.arena_len = s.core.arena_len ∧ fullArenaClauseRefs sf = fullArenaClauseRefs s ∧
            sf.scratch.red_refs = s.scratch.red_refs ∧ (FullMem c sf ⋆ R) mf)
          (fun _ _ mf ⟨sf, hspf, hflf, half, hrefsf, hrrf, hmf⟩ => by
            fvt_steps
            exact hQ 1#64 sf mf hspf hflf half hrefsf hrrf (Or.inl rfl) (fun h => by cases h) hmf)
          fun Jb hJb => ?_
        fvt_steps
        · have hpos : 0 < sm.core.cur_level := by
            have hc0 : 0 < (BitVec.ofNat 64 sm.core.cur_level).toNat := by c0_bound
            rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_m_lt] at hc0
          have htgt : (BitVec.ofNat 64 sm.core.cur_level - 1).toNat = sm.core.cur_level - 1 := by
            have hcv : (BitVec.ofNat 64 sm.core.cur_level).toNat = sm.core.cur_level := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_m_lt]
            have h1 : (1 : BitVec 64).toNat = 1 := rfl
            rw [BitVec.toNat_sub, hcv, h1]; omega
          c0_call hBacktrack
          refine ⟨c, sm, R, rfl, hspm.1, hcl_m_lt, fun _ => by rw [htgt]; omega,
            hspm.2.1.trail_lits_lt, hmm,
            fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
              hlen_bt _ _ _ hpres_bt hsc_bt _ _ hw_bt _ hm_bt => ?_⟩
          have hle_bt : (BitVec.ofNat 64 sm.core.cur_level - 1).toNat ≤ sm.core.cur_level := by
            rw [htgt]; omega
          have hsp_bt : FullSparseInvW c F0 F_cur _ :=
            FullVivTop.FullSparseInvW.of_backtrack hspm hle_bt hlen_bt hpres_bt
              (hw_bt F0 F_cur hspm.2.1 hle_bt)
          rcases hsc_bt with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
          exact hJb () m_bt ⟨_, hsp_bt, hfl_m_le, halm.trans (hals.trans hald),
            hrefsm.trans (hrefss.trans hrefs_d), hrrm.trans (hrrs.trans hrrd), hm_bt⟩
        · exact hJb () mm ⟨sm, hspm, hfl_m_le, halm.trans (hals.trans hald),
            hrefsm.trans (hrefss.trans hrefs_d), hrrm.trans (hrrs.trans hrrd), hmm⟩
        · exact hJb () mm ⟨sm, hspm, hfl_m_le, halm.trans (hals.trans hald),
            hrefsm.trans (hrefss.trans hrefs_d), hrrm.trans (hrrs.trans hrrd), hmm⟩
      · intro Js hJs
        fvt_steps
        · -- `sub_ref < arena_len`: promote or lower glue on `ar[sub_ref]`
          have hsub_lt_al : sd.scratch.ant_sz.toNat < sd.core.arena_len := by
            have hle := hspd.1.core_ok.arena_len_le
            have hc0 : sd.scratch.ant_sz.toNat <
                (BitVec.ofNat 64 sd.core.arena_len).toNat := by c0_bound
            rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc0
          have hsub_ref_in : sd.scratch.ant_sz.toNat ∈ fullArenaClauseRefs sd :=
            m6_sub_ref_in_refs hspd.1 hsubd hsub_ne hsub_lt_al
          have hsub_lt_ar : sd.scratch.ant_sz.toNat < sd.core.arena.length := by
            have := hspd.1.core_ok.arena_len_arr; have := hspd.1.core_ok.arena_len_le; omega
          let shdr := sd.core.arena[sd.scratch.ant_sz.toNat]'hsub_lt_ar
          have hshdr_eq : fullArenaHdr sd sd.scratch.ant_sz.toNat = shdr := by
            unfold fullArenaHdr fullArenaHdrCore
            rw [List.getElem?_eq_getElem hsub_lt_ar, Option.getD_some]
          fvt_steps
          all_goals try exact hJs () md ⟨sd, hspd, rfl, rfl, rfl, rfl, hmd⟩
          all_goals first
            | (let shdr' := shdr &&& ~~~0x00400000#32
               obtain ⟨hsp_p, hrefs_p, _⟩ :=
                 fullSparseInvW_set_hdr_non_gs hspd hsub_ref_in shdr'
                   (sd.core.num_irred + 1#64) (sd.core.num_redundant - 1#64)
                   (by rw [hshdr_eq]; exact bv32_and_not_red_garb shdr)
                   (by rw [hshdr_eq]; exact bv32_and_not_red_shrk shdr)
               exact hJs () _ ⟨_, hsp_p, rfl, rfl, hrefs_p, rfl,
                 by refine m6_fullMem_eq ?_ (by assumption); rfl⟩)
            | (let shdr' := shdr &&& ~~~0x00400000#32
               obtain ⟨hsp_p, hrefs_p, _⟩ :=
                 fullSparseInvW_set_hdr_non_gs hspd hsub_ref_in shdr'
                   (sd.core.num_irred + 1#64) sd.core.num_redundant
                   (by rw [hshdr_eq]; exact bv32_and_not_red_garb shdr)
                   (by rw [hshdr_eq]; exact bv32_and_not_red_shrk shdr)
               exact hJs () _ ⟨_, hsp_p, rfl, rfl, hrefs_p, rfl,
                 by refine m6_fullMem_eq ?_ (by assumption); rfl⟩)
            | (let hdr_c := sd.core.arena[(cref.setWidth 64).toNat]'hcr_d_bv
               let cgl := hdr_c &&& 0x7FFFF#32
               let shdr' := (shdr &&& ~~~0x7FFFF#32) ||| cgl
               obtain ⟨hsp_g, hrefs_g, _⟩ :=
                 fullSparseInvW_set_hdr_non_gs hspd hsub_ref_in shdr'
                   sd.core.num_irred sd.core.num_redundant
                   (by rw [hshdr_eq]
                       exact bv32_set_glue_garb shdr cgl (bv32_glue_mask_garb hdr_c))
                   (by rw [hshdr_eq]
                       exact bv32_set_glue_shrk shdr cgl (bv32_glue_mask_shrk hdr_c))
               exact hJs () _ ⟨_, hsp_g, rfl, rfl, hrefs_g, rfl,
                 by refine m6_fullMem_eq ?_ (by assumption); rfl⟩)
        · exact hJs () md ⟨sd, hspd, rfl, rfl, rfl, rfl, hmd⟩
    · -- Branch 2+: `sub_ref == 0xFFFFFFFFFFFFFFFFULL`
      refine wp_join_group (ts := []) (fun () mf => mf = md) ?_ ?_
      · -- After `if (has_ded && olen < sz)`
        rintro _ ⟨⟩ mf hmf; rw [hmf]
        refine wp_join_group (ts := []) (fun () mg => mg = md) ?_ ?_
        · -- After `if (has_ded && (confl || implied != FFFF) && (is_red || !used_red))`
          rintro _ ⟨⟩ mg hmg; rw [hmg]
          refine wp_join_group (ts := [])
            (fun () mf => ∃ sf : FullState,
              FullSparseInvW c F0 F_cur sf ∧ sf.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              sf.core.arena_len = s.core.arena_len ∧
              fullArenaClauseRefs sf = fullArenaClauseRefs s ∧
              sf.scratch.red_refs = s.scratch.red_refs ∧ (FullMem c sf ⋆ R) mf) ?_ ?_
          · -- Fallback: optional 1-level backtrack + `full_viv_reestablish_m6` + return 1
            rintro _ ⟨⟩ mf ⟨sf, hspf, hflf, half, hrefsf, hrrf, hmf⟩
            have hcl_f_le : sf.core.cur_level ≤ c.max_vars := by
              have := hspf.2.1.cur_level_le; have := hspf.1.core_ok.trail_end_le
              have := hspf.1.core_ok.cur_vars_le; omega
            have hcl_f_lt : sf.core.cur_level < 2 ^ 64 := by omega
            refine wp_join_group (ts := [])
              (fun () mb => ∃ sb : FullState,
                FullSparseInvW c F0 F_cur sb ∧ sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                sb.core.arena_len = s.core.arena_len ∧
                fullArenaClauseRefs sb = fullArenaClauseRefs s ∧
                sb.scratch.red_refs = s.scratch.red_refs ∧ (FullMem c sb ⋆ R) mb) ?_ ?_
            · rintro _ ⟨⟩ mb ⟨sb, hspb, hflb, halb, hrefsb, hrrb, hmb⟩
              c0_call hReest
              refine ⟨c, F0, F_cur, sb, R, rfl, hspb, hrefsb ▸ href0, hmb,
                fun sr mr hspr _ harr halr _ hflr hrrr _ hmr => ?_⟩
              have hrefsr : fullArenaClauseRefs sr = fullArenaClauseRefs sb := by
                unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [harr, halr]
              fvt_steps
              exact hQ 1#64 sr mr hspr (by rw [hflr]; exact hflb) (halr.trans halb)
                (hrefsr.trans hrefsb) (hrrr.trans hrrb) (Or.inl rfl) (fun h => by cases h) hmr
            · intro Jb hJb; fvt_steps
              · have hpos : 0 < sf.core.cur_level := by
                  have hc0 : 0 < (BitVec.ofNat 64 sf.core.cur_level).toNat := by c0_bound
                  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_f_lt] at hc0
                have htgt : (BitVec.ofNat 64 sf.core.cur_level - 1).toNat =
                    sf.core.cur_level - 1 := by
                  have hcv : (BitVec.ofNat 64 sf.core.cur_level).toNat = sf.core.cur_level := by
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_f_lt]
                  have h1 : (1 : BitVec 64).toNat = 1 := rfl
                  rw [BitVec.toNat_sub, hcv, h1]; omega
                c0_call hBacktrack
                refine ⟨c, sf, R, rfl, hspf.1, hcl_f_lt, fun _ => by rw [htgt]; omega,
                  hspf.2.1.trail_lits_lt, hmf,
                  fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
                    hlen_bt _ _ _ hpres_bt hsc_bt _ _ hw_bt _ hm_bt => ?_⟩
                have hle_bt : (BitVec.ofNat 64 sf.core.cur_level - 1).toNat ≤
                    sf.core.cur_level := by rw [htgt]; omega
                have hsp_bt : FullSparseInvW c F0 F_cur _ :=
                  FullVivTop.FullSparseInvW.of_backtrack hspf hle_bt hlen_bt hpres_bt
                    (hw_bt F0 F_cur hspf.2.1 hle_bt)
                rcases hsc_bt with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
                exact hJb () m_bt ⟨_, hsp_bt, hflf, half, hrefsf, hrrf, hm_bt⟩
              · exact hJb () mf ⟨sf, hspf, hflf, half, hrefsf, hrrf, hmf⟩
              · exact hJb () mf ⟨sf, hspf, hflf, half, hrefsf, hrrf, hmf⟩
          · -- `if (!confl && implied == 0xFFFFFFFFu && all_done)`: instantiation strengthening
            intro Ji hJi
            clear hMarkGarb hBacktrack hCommit hded_ok hsubd hcok0 himpl0 hfal0
            fvt_steps
            all_goals try exact hJi () md ⟨sd, hspd, hfl_d_le, hald, hrefs_d, hrrd, hmd⟩
            c0_call hInst
            refine ⟨c, F0, F_cur, sd, R, rfl, hspd, href_d, hng_d, hsz_d, hsz_le, hperm_d, hmd,
              fun ir s_i m_i hspi hfli hali hrefsi hrri hir h20i hm_i => ?_⟩
            have hfli' : s_i.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfli hfl_d_le
            fvt_steps
            · have hir_ne0 : ir ≠ 0#64 := by c0_bound
              have hir_12 : ir = 1#64 ∨ ir = 2#64 ∨ ir = 20#64 := hir.resolve_left hir_ne0
              c0_call hReest
              refine ⟨c, F0, F_cur, s_i, R, rfl, hspi, hrefsi ▸ href_d, hm_i,
                fun sr mr hspr _ harr halr _ hflr hrrr _ hmr => ?_⟩
              have hrefsr : fullArenaClauseRefs sr = fullArenaClauseRefs s_i := by
                unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [harr, halr]
              fvt_steps
              apply hJ; fvt_steps
              exact hQ ir sr mr hspr (by rw [hflr]; exact hfli')
                (halr.trans (hali.trans hald)) (hrefsr.trans (hrefsi.trans hrefs_d))
                (hrrr.trans (hrri.trans hrrd)) hir_12 h20i hmr
            · have hir_ne0 : ir ≠ 0#64 := by c0_bound
              have hir_12 : ir = 1#64 ∨ ir = 2#64 ∨ ir = 20#64 := hir.resolve_left hir_ne0
              exact hQ ir s_i m_i hspi hfli' (hali.trans hald) (hrefsi.trans hrefs_d)
                (hrri.trans hrrd) hir_12 h20i hm_i
            · exact hJi () m_i ⟨s_i, hspi, hfli', hali.trans hald, hrefsi.trans hrefs_d,
                hrri.trans hrrd, hm_i⟩
        · -- `if (has_ded && (confl || implied != 0xFFFFFFFFu) && (is_red || !used_red))`
          intro Jg hJg
          clear hCommit hReest hInst hperm0 hperm_d htmp0_lt hcok0 himpl0 hfal0
            hsz_le hded_ok hsubd
          fvt_to_group
          · refine wp_join_group (ts := []) (fun () m1 => m1 = md)
              (fun _ _ m1 hm1 => by
                rw [hm1]
                refine wp_join_group (ts := []) (fun () m2 => m2 = md)
                  (fun _ _ m2 hm2 => by
                    rw [hm2]
                    c0_call hMarkGarb
                    refine ⟨c, F0, F_cur, sd, R, rfl, hspd, href_d, hmd,
                      fun sm mm hspm _ halm _ hflm hrefsm hrrm _ hmm => ?_⟩
                    have hcl_m_le : sm.core.cur_level ≤ c.max_vars := by
                      have := hspm.2.1.cur_level_le; have := hspm.1.core_ok.trail_end_le
                      have := hspm.1.core_ok.cur_vars_le; omega
                    have hcl_m_lt : sm.core.cur_level < 2 ^ 64 := by omega
                    have hfl_m_le : sm.core.fuel.toNat ≤ s.core.fuel.toNat := by
                      rw [hflm]; exact hfl_d_le
                    refine wp_join_group (ts := [])
                      (fun () mf => ∃ sf : FullState,
                        FullSparseInvW c F0 F_cur sf ∧ sf.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        sf.core.arena_len = s.core.arena_len ∧
                        fullArenaClauseRefs sf = fullArenaClauseRefs s ∧
                        sf.scratch.red_refs = s.scratch.red_refs ∧ (FullMem c sf ⋆ R) mf)
                      (fun _ _ mf ⟨sf, hspf, hflf, half, hrefsf, hrrf, hmf⟩ => by
                        fvt_steps
                        exact hQ 1#64 sf mf hspf hflf half hrefsf hrrf (Or.inl rfl)
                          (fun h => by cases h) hmf)
                      fun Jb hJb => ?_
                    fvt_steps
                    · have hpos : 0 < sm.core.cur_level := by
                        have hc0 : 0 < (BitVec.ofNat 64 sm.core.cur_level).toNat := by c0_bound
                        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_m_lt] at hc0
                      have htgt : (BitVec.ofNat 64 sm.core.cur_level - 1).toNat =
                          sm.core.cur_level - 1 := by
                        have hcv : (BitVec.ofNat 64 sm.core.cur_level).toNat =
                            sm.core.cur_level := by
                          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_m_lt]
                        have h1 : (1 : BitVec 64).toNat = 1 := rfl
                        rw [BitVec.toNat_sub, hcv, h1]; omega
                      have hle_bt : (BitVec.ofNat 64 sm.core.cur_level - 1).toNat ≤
                          sm.core.cur_level := by rw [htgt]; omega
                      c0_call hBacktrack
                      refine ⟨c, sm, R, rfl, hspm.1, hcl_m_lt, fun _ => by rw [htgt]; omega,
                        hspm.2.1.trail_lits_lt, hmm,
                        fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
                          hlen_bt _ _ _ hpres_bt hsc_bt _ _ hw_bt _ hm_bt => ?_⟩
                      have hsp_bt : FullSparseInvW c F0 F_cur _ :=
                        FullVivTop.FullSparseInvW.of_backtrack hspm hle_bt hlen_bt hpres_bt
                          (hw_bt F0 F_cur hspm.2.1 hle_bt)
                      rcases hsc_bt with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
                      exact hJb () m_bt ⟨_, hsp_bt, hfl_m_le, halm.trans hald,
                        hrefsm.trans hrefs_d, hrrm.trans hrrd, hm_bt⟩
                    · exact hJb () mm ⟨sm, hspm, hfl_m_le, halm.trans hald,
                        hrefsm.trans hrefs_d, hrrm.trans hrrd, hmm⟩
                    · exact hJb () mm ⟨sm, hspm, hfl_m_le, halm.trans hald,
                        hrefsm.trans hrefs_d, hrrm.trans hrrd, hmm⟩)
                  fun Jm2 hJm2 => by
                    fvt_steps
                    all_goals first | exact hJm2 () md rfl | exact hJg () md rfl)
              fun Jm hJm => by
                fvt_steps
                all_goals first | exact hJm () md rfl | exact hJg () md rfl
          · exact hJg () md rfl
      · -- `if (has_ded && olen < sz)`: commit + optional reestablish
        intro Jc hJc
        fvt_to_group
        · have hhd_t : has_ded = true := by assumption
          obtain ⟨hol_cv, hws_lt, hws_nd, hws_ent⟩ := hded_ok hhd_t
          have hol_mv : olen.toNat ≤ c.max_vars := by
            have := hspd.1.core_ok.cur_vars_le; omega
          refine wp_join_group (ts := [i32]) (fun _ m2 => m2 = md)
            (fun _ ⟨_impl_arg, ⟨⟩⟩ m2 hm2 => by
              rw [hm2]
              c0_call hCommit
              refine ⟨c, F0, F_cur, sd, R, rfl, hspd, href_d, hng_d, hol_mv,
                fun _ => ⟨hws_lt, hws_nd, hws_ent⟩, hmd,
                fun cr s_c m_c hspc _ halc _ hflc hrefsc hrrc _ hcr h20c hm_c => ?_⟩
              refine wp_join_group (ts := [])
                (fun () mf => ∃ sf : FullState,
                  FullSparseInvW c F0 F_cur sf ∧ sf.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                  sf.core.arena_len = s.core.arena_len ∧
                  fullArenaClauseRefs sf = fullArenaClauseRefs s ∧
                  sf.scratch.red_refs = s.scratch.red_refs ∧ (FullMem c sf ⋆ R) mf)
                (fun _ _ mf ⟨sf, hspf, hflf, half, hrefsf, hrrf, hmf⟩ => by
                  fvt_steps; exact hQ cr sf mf hspf hflf half hrefsf hrrf hcr h20c hmf)
                fun Jr hJr => ?_
              fvt_steps
              · c0_call hReest
                refine ⟨c, F0, F_cur, s_c, R, rfl, hspc, hrefsc ▸ href_d, hm_c,
                  fun s_r m_r hspr _ har_r hal_r _ hfl_r hrr_r _ hm_r => ?_⟩
                have hrefs_r : fullArenaClauseRefs s_r = fullArenaClauseRefs s_c := by
                  unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har_r, hal_r]
                exact hJr () m_r ⟨s_r, hspr, by rw [hfl_r, hflc]; exact hfl_d_le,
                  hal_r.trans (halc.trans hald), hrefs_r.trans (hrefsc.trans hrefs_d),
                  hrr_r.trans (hrrc.trans hrrd), hm_r⟩
              · exact hJr () m_c ⟨s_c, hspc, by rw [hflc]; exact hfl_d_le, halc.trans hald,
                  hrefsc.trans hrefs_d, hrrc.trans hrrd, hm_c⟩)
            fun Jt hJt => by fvt_steps <;> exact hJt _ md rfl
        · exact hJc () md rfl
        · exact hJc () md rfl
  · -- `if (confl || implied != 0xFFFFFFFFu || all_done)` entry
    intro Jif hJif
    clear hMarkGarb hBacktrack hCommit hReest hInst hsz0 hperm0
    have href_b1 : cref.toNat ∈ fullArenaClauseRefs sb1 := by
      unfold fullArenaClauseRefs; rw [hsb1_core]; exact href0
    have hng_b1 : fullArenaClauseGarb sb1 cref.toNat = false := by
      unfold fullArenaClauseGarb; rw [hsb1_core]; exact hng0
    have htmp_b1 : ∀ k < sz.toNat, (sb1.core.tmp[k]?.getD 0#32).toNat < 2 * sb1.core.cur_vars := by
      rw [hsb1_core]; exact htmp0_lt
    have hcv_b1 : sb1.core.cur_vars = s.core.cur_vars := congrArg FullCoreState.cur_vars hsb1_core
    have har_b1 : sb1.core.arena = s.core.arena := congrArg FullCoreState.arena hsb1_core
    have hal_b1 : sb1.core.arena_len = s.core.arena_len :=
      congrArg FullCoreState.arena_len hsb1_core
    have hfl_b1 : sb1.core.fuel = s.core.fuel := congrArg FullCoreState.fuel hsb1_core
    have htm_b1 : sb1.core.tmp = s.core.tmp := congrArg FullCoreState.tmp hsb1_core
    fvt_to_group
    refine wp_join_group (ts := [])
      (fun () m1 => m1 = m ∧ (confl = true ∨ implied ≠ 0xFFFFFFFF#32 ∨ all_done = true))
      (fun _ _ m1 ⟨hm1, hdisj⟩ => by
        rw [hm1]
        refine wp_join_group (ts := [i32])
          (fun (impl_a, ()) m2 => m2 = m ∧
            ((confl = true ∧ impl_a = 0xFFFFFFFF#32) ∨ (confl = false ∧ impl_a = implied)))
          (fun _ ⟨impl_a, ⟨⟩⟩ m2 ⟨hm2, himpla⟩ => by
            rw [hm2]
            c0_call hDeduce
            refine ⟨c, F0, F_cur, sb1, R, rfl, hspb1, href_b1, hng_b1,
              hsz_le, htmp_b1, fun heq_ff => ?_, fun hne_ff => ?_, hmb1,
              fun olen mrk' lm' ws1' ws2' asz' rsz' md hspd hsubd hol_ok hmd => ?_⟩
            · rcases himpla with ⟨hc_t, _⟩ | ⟨hc_f, hi_eq⟩
              · left
                have hvc := m6_conflictOkW_to_viv (hcok0 hc_t)
                unfold FullVivifySpecs.FullVivConflictOk at hvc ⊢
                unfold fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits at hvc ⊢
                rwa [hsb1_core]
              · have him_ff : implied = 0xFFFFFFFF#32 := hi_eq.symm.trans heq_ff
                have hall_t : all_done = true := by
                  rcases hdisj with ht | hne | ha
                  · rw [hc_f] at ht; cases ht
                  · exact absurd him_ff hne
                  · exact ha
                obtain ⟨hct0, hfal⟩ := hfal0 hc_f him_ff hall_t
                exact Or.inr ⟨by rw [hsb1_core]; exact hct0, fun l hl => by
                  unfold fullArenaClauseLits at hl; rw [hsb1_core] at hl ⊢; exact hfal l hl⟩
            · rcases himpla with ⟨_, hi_ff⟩ | ⟨hc_f, hi_eq⟩
              · exact absurd hi_ff hne_ff
              · subst hi_eq
                obtain ⟨him_lt, him_val⟩ := himpl0 hc_f hne_ff
                exact ⟨by rw [hcv_b1]; exact him_lt, by rw [hsb1_core]; exact him_val⟩
            · fvt_steps
              exact hJif (olen, olen != 0xFFFFFFFF#32, ()) md
                ⟨_, hspd, hcv_b1, har_b1, hal_b1, hfl_b1, htm_b1, hsb1_rr, hsubd,
                 fun h => hol_ok (by
                   revert h; cases Decidable.em (olen = 0xFFFFFFFF#32) <;> simp [*]), hmd⟩)
          fun Jt hJt => by
            fvt_steps
            · exact hJt _ m ⟨rfl, Or.inl ⟨by assumption, rfl⟩⟩
            · exact hJt _ m ⟨rfl, Or.inr ⟨by assumption, rfl⟩⟩)
      fun Jthen hJthen => by
        fvt_steps
        · exact hJthen () m ⟨rfl, Or.inl (by assumption)⟩
        · exact hJthen () m ⟨rfl, Or.inr (Or.inl (by c0_bound))⟩
        · exact hJthen () m ⟨rfl, Or.inr (Or.inr (by assumption))⟩
        · exact hJif (sz, false, ()) m
            ⟨sb1, hspb1, hcv_b1, har_b1, hal_b1, hfl_b1, htm_b1, hsb1_rr, hsb1_sub,
             (fun h => by cases h), hmb1⟩

end InstFinishProofs

/-! ## 4. `sort_counts`, `has_l0`, `l0_simp`, `reuse_prefix`, & `clause` Proofs -/

section ClauseProofs

theorem full_viv_sort_counts_m6_wp (Γ : Env) :
    ∀ a m Q X, fullVivSortCountsM6Spec a m Q X →
      Func.wp Γ full_viv_sort_counts_m6_body a m Q X := by
  rintro ⟨h, sz, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hsz_le, hlt_orig, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have htl0 := hlen.core_ok.tmp_len_arr; have htrl0 := hlen.scratch_ok.tarjan_reach_len
  unfold Func.wp full_viv_sort_counts_m6_body
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
    have htmp1_lt := m6_tmp_lt_of_perm (by omega) hperm1 hlt_orig
    let x : BitVec 32 := tmp1[i.toNat]'(by omega)
    have hx_eq : tmp1[(i.setWidth 64).toNat]'hi_tmp = x :=
      Option.some.inj (by
        rw [← List.getElem?_eq_getElem hi_tmp, hi64, List.getElem?_eq_getElem (by omega)])
    have hx_lt_v : x.toNat < 2 * c.max_vars := by
      have h := htmp1_lt i.toNat hi_lt
      rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
    have hx_tr : ((tmp1[(i.setWidth 64).toNat]'hi_tmp).setWidth 64).toNat <
        s.scratch.tarjan_reach.length := by
      rw [hx_eq, bv32_setWidth64_toNat, htrl0]; omega
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
        have h := m6_tmp_lt_of_perm (by simp [htl2]; omega) hperm2 hlt_orig (j.toNat - 1) (by omega)
        rwa [List.getElem?_set_ne (by omega), hprev_eq, Option.getD_some] at h
      have hp_tr : ((tmp2[((j - 1).setWidth 64).toNat]'hj1_tmp).setWidth 64).toNat <
          s.scratch.tarjan_reach.length := by
        rw [hprev_raw, bv32_setWidth64_toNat, htrl0]; omega
      have hperm_sh := m6_tmp_shift_hole (by omega : tmp2.length = s.core.tmp.length)
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

theorem full_viv_has_l0_m6_wp (Γ : Env) :
    ∀ a m Q X, fullVivHasL0M6Spec a m Q X → Func.wp Γ full_viv_has_l0_m6_body a m Q X := by
  rintro ⟨h, cref, sz, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hsp, href, hng, hsz, hm0, hQ⟩
  have hwf := hsp.2.1.arena.refs_wf cref.toNat href
  have hcl := hsp.1.core_ok
  have harc := c.harena; have hmx := c.hmaxv; unfold dimacsBound at harc hmx
  have har_len := hcl.arena_len_arr; have har_le := hcl.arena_len_le
  have hvl := hcl.vals_len; have hll := hcl.lvl_len; have hcv := hcl.cur_vars_le
  have hbd : cref.toNat + 3 + sz.toNat ≤ s.core.arena.length := by
    rw [hsz]; unfold fullArenaClauseSize at *; omega
  unfold Func.wp full_viv_has_l0_m6_body
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

theorem full_viv_l0_simp_m6_wp (Γ : Env)
    (hHasL0 : ∀ a m Q X, fullVivHasL0M6Spec a m Q X →
      Γ "full_viv_has_l0_m6" [i64, i32, i32] [.bool] a m Q X)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hSimplify : ∀ a m Q X, fullVivSimplifyM6Spec a m Q X →
      Γ "full_viv_simplify_m6" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, fullVivL0SimpM6Spec a m Q X → Func.wp Γ full_viv_l0_simp_m6_body a m Q X := by
  rintro ⟨h, cref, sz, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hsp0, href0, hng0, hsz0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl0 := hsp0.1.core_ok
  unfold Func.wp full_viv_l0_simp_m6_body
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
        fun sr s_s m_s hsp_s _ _ hal_s _ hfl_s hrefs_s hrr_s _ hsr h20 h0 hm_s => ?_⟩
      fvt_steps
      exact hQ sr s_s m_s hsp_s (hfl_s.trans hfl_bt) (hal_s.trans hal_bt)
        (hrefs_s.trans hrefs_bt) (hrr_s.trans hrr_bt) hsr h20 h0 hm_s
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

theorem full_viv_reuse_prefix_m6_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X) :
    ∀ a m Q X, fullVivReusePrefixM6Spec a m Q X →
      Func.wp Γ full_viv_reuse_prefix_m6_body a m Q X := by
  rintro ⟨h, cref, sz, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hsp0, hsz_le, htmp0_lt, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl0 := hsp0.1.core_ok
  have hclvl_le : s.core.cur_level ≤ c.max_vars := by
    have := hsp0.2.1.cur_level_le; have := hcl0.trail_end_le; have := hcl0.cur_vars_le; omega
  have hclvl_lt64 : s.core.cur_level < 2 ^ 64 := by omega
  unfold Func.wp full_viv_reuse_prefix_m6_body
  fvt_to_group
  · fvt_steps; exact hQ s m0 hsp0 rfl rfl rfl rfl rfl rfl rfl hm0
  · fvt_to_group
    let clvl : BitVec 64 := BitVec.ofNat 64 s.core.cur_level
    have hclvl_nat : clvl.toNat = s.core.cur_level := by
      simp [clvl, Nat.mod_eq_of_lt hclvl_lt64]
    refine wp_loop_break_group (brkTs := [i64, i32]) (lpTs := [i64, i32])
      (fun (keep_b, _ib, ()) mb => keep_b.toNat ≤ s.core.cur_level ∧ mb = m0)
      (fun rem (keep, i, ()) mp =>
        keep.toNat ≤ s.core.cur_level ∧ i.toNat ≤ sz.toNat ∧ rem = sz.toNat - i.toNat ∧ mp = m0)
      ?_ ?_ ?_
    · rintro _ ⟨keep_b, _ib, ⟨⟩⟩ mb ⟨hkb_le, hmb⟩
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
    · intro B L rem ⟨keep, i, ⟨⟩⟩ mp hB hL ⟨hkp_le, hi_le, hrem, hmp⟩
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

private theorem m6_viv_clause_prop_step (Γ : Env)
    (hPropIgn : ∀ a m Q X, Full.fullPropagateIgnoreDelSpec a m Q X →
      Γ "full_propagate_ignore" [i64, i64] [i64] a m Q X)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hBestImpl : ∀ a m Q X, fullVivBestImpliedM6Spec a m Q X →
      Γ "full_viv_best_implied_m6" [i64, i32] [i32] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s5 sp s_as : FullState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {B : Cont [i32, .bool, i32]} {J_jn : Cont [.bool, i32]}
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
        sb.core.probing = s5.core.probing ∧ sb.core.tmp = tmp5 ∧
        sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        fullArenaClauseRefs sb = fullArenaClauseRefs s ∧
        sb.scratch.red_refs = s.scratch.red_refs ∧
        cref.toNat ∈ fullArenaClauseRefs sb ∧
        fullArenaClauseGarb sb cref.toNat = false ∧
        fullArenaClauseSize sb cref.toNat = sz.toNat ∧
        (fullArenaClauseLits sb cref.toNat).Perm lits2 ∧
        (confl = true → FullConflictOkW F_cur sb) ∧
        (confl = false → implied ≠ 0xFFFFFFFF#32 →
          implied.toNat < 2 * sb.core.cur_vars ∧
          sb.core.vals[implied.toNat]?.getD 0#8 = 1#8) ∧
        (confl = false → implied = 0xFFFFFFFF#32 → ib = sz →
          sb.core.confl_type = 0#64 ∧
          ∀ l ∈ fullArenaClauseLits sb cref.toNat, sb.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
        (FullMem c sb ⋆ R) m') → B r m')
    (hJ_jn : ∀ (xs : Tup Val [.bool, i32]) (m : Mem 64),
      (∃ s_jn : FullState,
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
    (hsz_le_mv : sz.toNat ≤ c.max_vars)
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
              (Expr.call (as := [i64, i32]) (bs := [i32]) "full_viv_best_implied_m6"
                (Arg.var c.hdr, Arg.var sz, ()) fun p =>
                Expr.let_
                  { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
                    args := (Arg.var p.fst, Arg.imm 4294967295, ()) }
                  fun p_1 =>
                Expr.jnz (Arg.var p_1.fst)
                  (Expr.jump B (Arg.var i, Arg.imm false, Arg.var p.fst, ()))
                  (Expr.jump J_jn (Arg.imm false, Arg.imm 4294967295, ())))))
      m_as := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  c0_call hPropIgn
  refine ⟨c, F0, F_cur, s_as, R, rfl, hsp_as.1, hsp_as.2.1, hsp_as.2.2.2.2.2, hm_as,
    fun pr vals_p flags_p lvl_p rsns_p trl_p tp_p te_p prop_p unass_p unfl_p
      wvec_p arena_p wstk_p wlen_p wu_p fuel_p ctype_p cref_p c0_p c1_p oom_p
      ticks_p wsort_p phases_p delayed_p m_p hlen_p hw_p htr_p hperm_p hfl_p hpr_disj hpr0 hpr1
      _ _ hm_p => ?_⟩
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
        search_ticks := ticks_p, wsort := wsort_p, phases := phases_p, delayed := delayed_p } }
  have hsp_p : FullSparseInvW c F0 F_cur s_p :=
    m6_sparseInvW_of_prop_canon hsp_as hlen_p hw_p hperm_p
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
  · have hp_cl_lt : s_p.core.cur_level < 2 ^ 64 := by
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
    exact hB (i, true, 0xFFFFFFFF#32, ()) _ ⟨s_p, hsp_p, hcv_p, hal_p, hpr_p, htmp_p,
      hfl_p', hrefs_p', hrr_p, href_p, hng_p, hsz_p, hlits_p, fun _ => hcok_p_fn hpr_eq1,
      (fun h => by cases h), (fun h => by cases h), hm_p'⟩
  · have hpr_eq0 : pr = 0#64 := by
      rcases hpr_disj with rfl | rfl | rfl
      · rfl
      · exact absurd rfl (by c0_bound)
      · exact absurd rfl (by c0_bound)
    have hct_p0 : s_p.core.confl_type = 0#64 := hct_p0_fn hpr_eq0
    have htmp_p_lt : ∀ k < sz.toNat, (s_p.core.tmp[k]?.getD 0#32).toNat < 2 * s_p.core.cur_vars :=
      fun k hk => by rw [htmp_p, hcv_p]; exact hlits2_lt _ (hlits2_mem k hk)
    c0_call hBestImpl
    refine ⟨c, F0, F_cur, s_p, R, rfl, hsp_p, hsz_le_mv, htmp_p_lt, hm_p', fun bi hbi => ?_⟩
    fvt_steps
    · have hbi_ne : bi ≠ 0xFFFFFFFF#32 := by c0_bound
      exact hB (i, false, bi, ()) _ ⟨s_p, hsp_p, hcv_p, hal_p, hpr_p, htmp_p, hfl_p', hrefs_p',
        hrr_p, href_p, hng_p, hsz_p, hlits_p, (fun h => by cases h), fun _ _ => hbi hbi_ne,
        fun _ h => absurd h hbi_ne, hm_p'⟩
    · have hi1_nat : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
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
      exact hJ_jn _ _ ⟨s_p, hsp_p, hcv_p, hal_p, hpr_p, htmp_p, hfl_p', hrefs_p', hrr_p,
        href_p, hng_p, hsz_p, hlits_p, hct_p0, hfal_p1, hm_p'⟩

theorem full_viv_clause_m6_del_wp (Γ : Env)
    (hL0Simp : ∀ a m Q X, fullVivL0SimpM6Spec a m Q X →
      Γ "full_viv_l0_simp_m6" [i64, i32, i32] [i64] a m Q X)
    (hSort : ∀ a m Q X, fullVivSortCountsM6Spec a m Q X →
      Γ "full_viv_sort_counts_m6" [i64, i32] [] a m Q X)
    (hReuse : ∀ a m Q X, fullVivReusePrefixM6Spec a m Q X →
      Γ "full_viv_reuse_prefix_m6" [i64, i32, i32] [] a m Q X)
    (hBestImpl : ∀ a m Q X, fullVivBestImpliedM6Spec a m Q X →
      Γ "full_viv_best_implied_m6" [i64, i32] [i32] a m Q X)
    (hAssign : ∀ a m Q X, Full.fullAssignSpec a m Q X →
      Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hPropIgn : ∀ a m Q X, Full.fullPropagateIgnoreDelSpec a m Q X →
      Γ "full_propagate_ignore" [i64, i64] [i64] a m Q X)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hFinish : ∀ a m Q X, fullVivFinishM6Spec a m Q X →
      Γ "full_viv_finish_m6" [i64, i32, i32, .bool, i32, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullVivClauseM6Spec a m Q X → Func.wp Γ full_viv_clause_m6_body a m Q X := by
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
  unfold Func.wp full_viv_clause_m6_body
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
    · rcases hl0r with rfl | rfl | rfl | rfl
      · exact absurd rfl hl0
      · fvt_steps
        exact hQ 1#64 s1 m1 hsp1 hfl1 hal1 hrefs1 hrr1 (Or.inl rfl) (fun h => by cases h) hm1
      · fvt_steps
        exact hQ 2#64 s1 m1 hsp1 hfl1 hal1 hrefs1 hrr1 (Or.inr (Or.inl rfl))
          (fun h => by cases h) hm1
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
      let lits2 := fullArenaClauseLits s2 cref.toNat
      have hperm_lits5 : ((tmp5.take sz.toNat).map BitVec.toNat).Perm lits2 := by
        dsimp only [tmp5, lits2]; rw [htmp4r]; exact hperm_lits4
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
      clear hm hwf1 hperm4 hperm_lits4 htmp5_mem hlits5_inv hsp4 hsp2
        s4 hrefs2 href2 hng2 hsz2 har2_len htmp2_len hbd2 htmpc_lits_lt hsp1
        hfl1 hal1 hrefs1 hrr1 href1 hng1 hcl1 hsz_nat hsz_le_cv hsp0 href0
        hng0 hm0 hsp4r hcv4r har4r hal4r hpr4r hfl4r htmp4r hrr4r hrefs_eq4r htmp4_lt_cv
      try clear hi_eq ihc hmc hcp htc_len hi_le tmpc mc Jc i s2 s4r
      -- Inner assumption-propagation loop `while (i < sz)`
      refine wp_loop_break_group (brkTs := [i32, .bool, i32]) (lpTs := [i32])
        (fun (i, confl, implied, ()) mb => ∃ sb : FullState,
          FullSparseInvW c F0 F_cur sb ∧
          sb.core.cur_vars = s5.core.cur_vars ∧ sb.core.arena_len = s5.core.arena_len ∧
          sb.core.probing = s5.core.probing ∧ sb.core.tmp = tmp5 ∧
          sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          fullArenaClauseRefs sb = fullArenaClauseRefs s ∧
          sb.scratch.red_refs = s.scratch.red_refs ∧
          cref.toNat ∈ fullArenaClauseRefs sb ∧
          fullArenaClauseGarb sb cref.toNat = false ∧
          fullArenaClauseSize sb cref.toNat = sz.toNat ∧
          (fullArenaClauseLits sb cref.toNat).Perm lits2 ∧
          (confl = true → FullConflictOkW F_cur sb) ∧
          (confl = false → implied ≠ 0xFFFFFFFF#32 →
            implied.toNat < 2 * sb.core.cur_vars ∧
            sb.core.vals[implied.toNat]?.getD 0#8 = 1#8) ∧
          (confl = false → implied = 0xFFFFFFFF#32 → i = sz →
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
      · -- After inner loop: delegate to `full_viv_finish_m6`, then mark `PH_VIV`
        rintro _ ⟨i_b, confl_b, impl_b, ⟨⟩⟩ mb
          ⟨sb, hspb, _, halb, _, htmpb, hflb, hrefsb, hrrb, hrefb, hngb, hszb, hpermb,
           hcokb, himplb, hfalb, hmb⟩
        fvt_steps
        c0_call hFinish
        refine ⟨c, F0, F_cur, sb, R, rfl, hspb, hsz_le_mv, hrefb, hngb, hszb,
          (by rw [htmpb]; exact hperm_lits5.trans hpermb.symm),
          hcokb, himplb,
          fun hc hi hall => hfalb hc hi (by
            revert hall; cases Decidable.em (i_b = sz) <;> simp [*]),
          hmb, fun r_f s_f m_f hspf hflf half hrefsf hrrf hrf h20f hm_f => ?_⟩
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
          obtain ⟨hsp_v, hrefs_v, _⟩ :=
            fullSparseInvW_set_hdr_non_gs hspf href_f hdr_v
              s_f.core.num_irred s_f.core.num_redundant
              (by rw [hhdr_f]; exact m6_bv32_or_viv_garb hdr_f)
              (by rw [hhdr_f]; exact m6_bv32_or_viv_shrk hdr_f)
          have hm_v : (FullMem c
              { s_f with core := { s_f.core with arena := s_f.core.arena.set cref.toNat hdr_v } }
              ⋆ R) m := by
            simpa only [hdr_v, hdr_f, hcr0_nat,
              show (1048576 : BitVec 32) = 0x00100000#32 from rfl] using hm
          exact hQ r_f _ m hsp_v (Nat.le_trans hflf hflb)
            (half.trans (halb.trans hal5)) (hrefs_v.trans (hrefsf.trans hrefsb))
            (hrrf.trans hrrb) hrf h20f hm_v
        · exact hQ r_f s_f m_f hspf (Nat.le_trans hflf hflb) (half.trans (halb.trans hal5))
            (hrefsf.trans hrefsb) (hrrf.trans hrrb) hrf h20f hm_f
        · exact hQ r_f s_f m_f hspf (Nat.le_trans hflf hflb) (half.trans (halb.trans hal5))
            (hrefsf.trans hrefsb) (hrrf.trans hrrb) hrf h20f hm_f
      · -- Inner loop body
        intro B L rem ⟨i, ⟨⟩⟩ mp hB hL
          ⟨sp, hi_le, hrem, hspp, hcvp, halp, hprp, htmpp, hflp, hrefsp, hrrp, hrefp, hngp, hszp,
           hpermp, hct0, hfalp, hmp⟩
        clear hSort hReuse hFinish
        fvt_steps
        · have hi_lt : i.toNat < sz.toNat := by c0_bound
          have hi_ne_sz : i ≠ sz := fun heq => by rw [heq] at hi_lt; exact Nat.lt_irrefl _ hi_lt
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
          · -- `lv > 0`: call `full_viv_best_implied_m6(h, sz)` and break
            have htmp_sp_lt : ∀ k < sz.toNat,
                (sp.core.tmp[k]?.getD 0#32).toNat < 2 * sp.core.cur_vars := fun k hk => by
              rw [htmpp, hcvp]; exact hlits2_lt _ (hlits2_mem k hk)
            c0_call hBestImpl
            refine ⟨c, F0, F_cur, sp, R, rfl, hspp, hsz_le_mv, htmp_sp_lt, hmp, fun bi hbi => ?_⟩
            fvt_steps
            exact hB (i, false, bi, ()) mp ⟨sp, hspp, hcvp, halp, hprp, htmpp, hflp, hrefsp, hrrp,
              hrefp, hngp, hszp, hpermp, (fun h => by cases h), fun _ hne => hbi hne,
              fun _ _ heq => absurd heq hi_ne_sz, hmp⟩
          · refine wp_join_group (ts := [.bool, i32])
              (fun (_, _, ()) m_jn => ∃ s_jn : FullState,
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
            · rintro _ ⟨_, _, ⟨⟩⟩ m_jn ⟨s_jn, hsp_jn, hcv_jn, hal_jn, hpr_jn, htmp_jn, hfl_jn,
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
                exact m6_viv_clause_prop_step Γ hPropIgn hBacktrack hBestImpl hQ hB hJ_jn
                  hsp_as' hsz_le_mv hcvp hcv_as halp hal_as hprp hpr_as hflp hfl_as hal5
                  hrefsp hrefs_as hrr_as hrefp hng_as hsz_as hpermp hlits_as hct_as htmp_as
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
          exact hB (i, false, 0xFFFFFFFF#32, ()) _ ⟨sp, hspp, hcvp, halp, hprp, htmpp, hflp,
            hrefsp, hrrp, hrefp, hngp, hszp, hpermp, (fun h => by cases h),
            fun _ h => absurd rfl h, fun _ _ _ => ⟨hct0, hfal_all⟩, hmp⟩
      · intro B L _ hL
        fvt_steps
        exact hL sz.toNat (0#32, ()) _ ⟨s5, Nat.zero_le _, by simp, hsp5, rfl, rfl, rfl,
          htmp5, hfl5, hrefs5, hrr5, href5, hng5, hsz5, hperm5, hct5,
          fun _ hk => by simp at hk, hm5⟩

theorem full_viv_clause_m6_wp (Γ : Env)
    (hL0Simp : ∀ a m Q X, fullVivL0SimpM6Spec a m Q X →
      Γ "full_viv_l0_simp_m6" [i64, i32, i32] [i64] a m Q X)
    (hSort : ∀ a m Q X, fullVivSortCountsM6Spec a m Q X →
      Γ "full_viv_sort_counts_m6" [i64, i32] [] a m Q X)
    (hReuse : ∀ a m Q X, fullVivReusePrefixM6Spec a m Q X →
      Γ "full_viv_reuse_prefix_m6" [i64, i32, i32] [] a m Q X)
    (hBestImpl : ∀ a m Q X, fullVivBestImpliedM6Spec a m Q X →
      Γ "full_viv_best_implied_m6" [i64, i32] [i32] a m Q X)
    (hAssign : ∀ a m Q X, Full.fullAssignSpec a m Q X →
      Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hPropIgn : ∀ a m Q X, Full.fullPropagateIgnoreSpec a m Q X →
      Γ "full_propagate_ignore" [i64, i64] [i64] a m Q X)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hFinish : ∀ a m Q X, fullVivFinishM6Spec a m Q X →
      Γ "full_viv_finish_m6" [i64, i32, i32, .bool, i32, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullVivClauseM6Spec a m Q X → Func.wp Γ full_viv_clause_m6_body a m Q X :=
  full_viv_clause_m6_del_wp Γ hL0Simp hSort hReuse hBestImpl hAssign
    (fun a m Q X h => hPropIgn a m Q X (Full.fullPropagateIgnoreSpec_of_del h))
    hBacktrack hFinish

end ClauseProofs

end LeanQbe.T.Examples.Kissat.FullM6VivBackbone
