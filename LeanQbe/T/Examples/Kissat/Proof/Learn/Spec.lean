/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Learn
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Reduce.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical `Spec` Table for `Kissat/Src/Learn.lean` (`4` fns)

Canonical UNSAT-sound `Spec` definitions, `deps`, `Spec.XFree` proofs, `specs` table matching
`Src.Learn.fns` 1:1 (`noExit := true`), `specs_sigs`, `specs_nodup`, `specs_noExit`,
`specs_xfree`, and `Env.Has` projections (`0` legacy imports, `0` `@[expose]` on theorems).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Learn.Spec

open Std.Sat
open LeanQbe.T
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Learn

public section

/-! ## 1. Upstream Extern Dependency Table (`deps`) -/

/-- Canonical upstream specification dependencies for `Src.Learn.fns` (`8` externs across
`Backtrack`, `Clause`, `Reduce`, `Watch`). -/
@[expose] def deps : List SpecEntry :=
  Backtrack.Spec.specs ++ Clause.Spec.specs ++ Reduce.Spec.specs ++ Watch.Spec.specs

/-! ## 2. Canonical Per-Function Specifications (`4` Functions) -/

/-- Canonical contract for `full_eager_subsume(h, new_ref)`: subsumption updates `arena`,
`arena_garbage`, `num_redundant`, and `scratch` while preserving `FullSparseInvW` and
`work_stk1` / `work_stk2`. -/
@[expose] def fullEagerSubsumeSpec : Spec [i64, i64] [] :=
  fun (h, new_ref, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧
      (∀ k < s.core.tmp_len, (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars) ∧
      (new_ref.toNat < 0x80000000 → new_ref.toNat ∈ fullArenaClauseRefs s) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ arena' ag' nr' sc' m',
        let s' : FullState :=
          { s with
            core :=
              { s.core with arena := arena', arena_garbage := ag', num_redundant := nr' }
            scratch := sc' }
        FullSparseInvW c F0 F_cur s' → sc'.work_stk1 = s.scratch.work_stk1 →
        sc'.work_stk2 = s.scratch.work_stk2 →
        (FullMem c s' ⋆ R) m' → Q () m'

/-- Canonical M6 header-threaded contract for `full_learn_clause_m6(h, glue)`. -/
@[expose] def fullLearnClauseM6Spec : Spec [i64, i64] [i64] :=
  fun (h, _glue, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ext : List (BitVec 64))
      (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧
      FullOtfsInvW c F0 F_cur s ∧ 0 < s.core.cur_level ∧
      1 ≤ s.core.tmp_len ∧ s.core.tmp_len ≤ s.core.cur_vars ∧
      ((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
      (∀ k < s.core.tmp_len, let l := (s.core.tmp[k]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
      (∀ k, 1 ≤ k → k < s.core.tmp_len →
        let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
        0 < lv ∧ lv < s.core.cur_level) ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
        M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        s'.core.probing = s.core.probing → s'.core.min_clr_len = s.core.min_clr_len →
        s'.scratch.work_stk1 = s.scratch.work_stk1 →
        s'.scratch.work_stk2 = s.scratch.work_stk2 →
        (r = 20#64 → F0.Unsat ∧ FullSparseInvW c F0 F_cur s' ∧
          s'.core.cur_level < s.core.cur_level) →
        (r = 0#64 → FullSparseInvW c F0 F_cur s') →
        (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧
          s'.core.cur_level < s.core.cur_level) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-! ## 3. Canonical Table (`specs`) & Structural Theorems -/

/-- Canonical specification table aligned 1:1 with `Src.Learn.fns`. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_det_new_level",    [i64, i64], [i64], Proof.Spec.fullDetNewLevelSpec, true⟩
  , ⟨"full_one_lit_confl",    [i64],      [i64], Proof.Spec.fullOneLitConflSpec, true⟩
  , ⟨"full_eager_subsume",    [i64, i64], [],    fullEagerSubsumeSpec,           true⟩
  , ⟨"full_learn_clause_m6", [i64, i64], [i64], fullLearnClauseM6Spec,          true⟩
  ]

theorem fullDetNewLevelSpec_xfree : Proof.Spec.fullDetNewLevelSpec.XFree := by xfree

theorem fullOneLitConflSpec_xfree : Proof.Spec.fullOneLitConflSpec.XFree := by xfree

theorem fullEagerSubsumeSpec_xfree : fullEagerSubsumeSpec.XFree := by xfree

theorem fullLearnClauseM6Spec_xfree : fullLearnClauseM6Spec.XFree := by xfree

theorem specs_sigs : specs.map SpecEntry.sig = fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

theorem specs_xfree : ∀ e ∈ specs, e.spec.XFree := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact fullDetNewLevelSpec_xfree
  · exact fullOneLitConflSpec_xfree
  · exact fullEagerSubsumeSpec_xfree
  · exact fullLearnClauseM6Spec_xfree

/-! ## 4. Constructors, Eliminators & `Env.Has` Projections -/

theorem fullEagerSubsumeSpec_intro
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {new_ref : BitVec 64} {m : Mem 64} {Q : Post []} {X : XPost}
    (hinv : FullSparseInvW c F0 F_cur s)
    (htmp : ∀ k < s.core.tmp_len, (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars)
    (href : new_ref.toNat < 0x80000000 → new_ref.toNat ∈ fullArenaClauseRefs s)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ arena' ag' nr' sc' m',
      let s' : FullState :=
        { s with
          core :=
            { s.core with arena := arena', arena_garbage := ag', num_redundant := nr' }
          scratch := sc' }
      FullSparseInvW c F0 F_cur s' → sc'.work_stk1 = s.scratch.work_stk1 →
      sc'.work_stk2 = s.scratch.work_stk2 →
      (FullMem c s' ⋆ R) m' → Q () m') :
    fullEagerSubsumeSpec (c.hdr, new_ref, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, rfl, hinv, htmp, href, hm, hQ⟩

theorem fullEagerSubsumeSpec_elim
    {h new_ref : BitVec 64} {m : Mem 64} {Q : Post []} {X : XPost}
    (hs : fullEagerSubsumeSpec (h, new_ref, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧
      (∀ k < s.core.tmp_len, (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars) ∧
      (new_ref.toNat < 0x80000000 → new_ref.toNat ∈ fullArenaClauseRefs s) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ arena' ag' nr' sc' m',
        let s' : FullState :=
          { s with
            core :=
              { s.core with arena := arena', arena_garbage := ag', num_redundant := nr' }
            scratch := sc' }
        FullSparseInvW c F0 F_cur s' → sc'.work_stk1 = s.scratch.work_stk1 →
        sc'.work_stk2 = s.scratch.work_stk2 →
        (FullMem c s' ⋆ R) m' → Q () m' :=
  hs

theorem fullLearnClauseM6Spec_intro
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {glue : BitVec 64} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext)
    (hinv : FullOtfsInvW c F0 F_cur s) (hlvl : 0 < s.core.cur_level)
    (htl1 : 1 ≤ s.core.tmp_len) (htlc : s.core.tmp_len ≤ s.core.cur_vars)
    (hnodup : ((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup)
    (hvals : ∀ k < s.core.tmp_len, let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hlvls : ∀ k, 1 ≤ k → k < s.core.tmp_len →
      let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)))
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.probing = s.core.probing → s'.core.min_clr_len = s.core.min_clr_len →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullSparseInvW c F0 F_cur s' ∧
        s'.core.cur_level < s.core.cur_level) →
      (r = 0#64 → FullSparseInvW c F0 F_cur s') →
      (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧
        s'.core.cur_level < s.core.cur_level) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    fullLearnClauseM6Spec (c.hdr, glue, ()) m Q X :=
  ⟨c, F0, F_cur, ext, s, R, rfl, hcfg, hext, hinv, hlvl, htl1, htlc, hnodup,
    hvals, hlvls, hent, hm, hQ⟩

theorem fullLearnClauseM6Spec_elim
    {h glue : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hs : fullLearnClauseM6Spec (h, glue, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ext : List (BitVec 64))
      (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧
      FullOtfsInvW c F0 F_cur s ∧ 0 < s.core.cur_level ∧
      1 ≤ s.core.tmp_len ∧ s.core.tmp_len ≤ s.core.cur_vars ∧
      ((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
      (∀ k < s.core.tmp_len, let l := (s.core.tmp[k]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
      (∀ k, 1 ≤ k → k < s.core.tmp_len →
        let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
        0 < lv ∧ lv < s.core.cur_level) ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
        M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        s'.core.probing = s.core.probing → s'.core.min_clr_len = s.core.min_clr_len →
        s'.scratch.work_stk1 = s.scratch.work_stk1 →
        s'.scratch.work_stk2 = s.scratch.work_stk2 →
        (r = 20#64 → F0.Unsat ∧ FullSparseInvW c F0 F_cur s' ∧
          s'.core.cur_level < s.core.cur_level) →
        (r = 0#64 → FullSparseInvW c F0 F_cur s') →
        (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧
          s'.core.cur_level < s.core.cur_level) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m' :=
  hs

private theorem mem_has_specs {Γ : Env} (h : Γ.Sat specs) {nm : Sym} {as bs : List Ty}
    {sp : Spec as bs} (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ specs)
    (hx : sp.XFree) : Γ.Has nm sp :=
  Env.Sat.has h hmem hx

theorem has_full_det_new_level {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_det_new_level" Proof.Spec.fullDetNewLevelSpec :=
  mem_has_specs h (by simp [specs]) fullDetNewLevelSpec_xfree

theorem has_full_one_lit_confl {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_one_lit_confl" Proof.Spec.fullOneLitConflSpec :=
  mem_has_specs h (by simp [specs]) fullOneLitConflSpec_xfree

theorem has_full_eager_subsume {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_eager_subsume" fullEagerSubsumeSpec :=
  mem_has_specs h (by simp [specs]) fullEagerSubsumeSpec_xfree

theorem has_full_learn_clause_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_learn_clause_m6" fullLearnClauseM6Spec :=
  mem_has_specs h (by simp [specs]) fullLearnClauseM6Spec_xfree

end

end LeanQbe.T.Examples.Kissat.Proof.Learn.Spec
