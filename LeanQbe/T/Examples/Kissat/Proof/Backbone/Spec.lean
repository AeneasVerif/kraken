/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Backbone.Inv
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Src.Backbone
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Kissat Backbone Segment Specifications (`Proof.Backbone.Spec`)

Canonical flat-`Env` specification table (`specs : List SpecEntry`) aligned 1:1 with
`LeanQbe.T.Examples.Kissat.Src.Backbone.fns`, matching Step-13 contract strength for
downstream `Src.Probe`:
1. `full_backbone_sched_m6` (`fullBackboneSchedM6Spec`)
2. `full_backbone_keep_m6` (`fullBackboneKeepM6Spec`)
3. `full_backbone_unwind_m6` (`fullBackboneUnwindM6Spec`)
4. `full_backbone_prop_m6` (`fullBackbonePropM6Spec`)
5. `full_backbone_analyze_m6` (`fullBackboneAnalyzeM6Spec`)
6. `full_backbone_round_m6` (`fullBackboneRoundM6Spec`)
7. `full_backbone_m6` (`fullBackboneM6Spec`, `FullM6HdrMem`-threaded Step-13 contract)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Backbone.Spec

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Backbone
open LeanQbe.T.Examples.Kissat.Src.Backbone

/-! ## 1. Segment Dependency Table -/

@[expose] def deps : List SpecEntry :=
  Backtrack.Spec.specs ++ Clause.Spec.specs ++ Float64.Spec.specs ++
    PropSearch.Spec.specs ++ Watch.Spec.specs

/-! ## 2. Segment Contracts (`fullBackbone*Spec`) -/

@[expose] def fullBackboneSchedM6Spec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ cand_n fl' ws1' m',
      let s' : FullState :=
        { s with core := { s.core with flags := fl' }
                 scratch := { s.scratch with work_stk1 := ws1' } }
      FullSparseInvW c F0 F_cur s' → cand_n.toNat ≤ 2 * s.core.cur_vars →
      (∀ i < cand_n.toNat, (ws1'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
      (FullMem c s' ⋆ R) m' → Q (cand_n, ()) m'

@[expose] def fullBackboneKeepM6Spec : Spec [i64, i64] [] := fun (h, cand_n, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ cand_n.toNat ≤ 2 * s.core.cur_vars ∧
    (∀ i < cand_n.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ fl' m',
      let s' : FullState := { s with core := { s.core with flags := fl' } }
      FullSparseInvW c F0 F_cur s' → (FullMem c s' ⋆ R) m' → Q () m'

@[expose] def fullBackboneUnwindM6Spec : Spec [i64, i64, i64] [] :=
  fun (h, saved, target_lvl, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s0 st : FullState)
      (saved0 max_lvl : Nat) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s0 ∧ BbTrailInv c F0 F_cur s0 st saved0 max_lvl ∧
      saved0 ≤ saved.toNat ∧ saved.toNat ≤ st.core.trail_end ∧ target_lvl.toNat ≤ c.max_vars ∧
      (∀ i < saved.toNat,
        (st.core.lvl[(st.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          target_lvl.toNat) ∧
      (FullMem c st ⋆ R) m ∧
      ∀ vals' m',
        let st' : FullState :=
          { st with core := { st.core with
            vals := vals', trail_end := saved.toNat, cur_level := target_lvl.toNat } }
        BbTrailInv c F0 F_cur s0 st' saved0 target_lvl.toNat → (FullMem c st' ⋆ R) m' → Q () m'

@[expose] def fullBackbonePropM6Spec : Spec [i64, i64, .bool] [.bool] :=
  fun (h, prop_start, _stop_early, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s0 st : FullState)
      (saved0 max_lvl : Nat) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s0 ∧ BbTrailInv c F0 F_cur s0 st saved0 max_lvl ∧
      saved0 ≤ prop_start.toNat ∧ prop_start.toNat ≤ st.core.trail_end ∧
      ((st.core.cur_level = 0 ∧
        ∀ i, prop_start.toNat ≤ i → i < st.core.trail_end →
          (st.core.lvl[(st.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0) ∨
       (0 < st.core.cur_level ∧ st.core.cur_level ≤ c.max_vars)) ∧
      (FullMem c st ⋆ R) m ∧
      ∀ (ok : Bool) vals' lvl' rsns' trl' te' c0' c1' asz' m',
        let st' : FullState :=
          { st with
            core := { st.core with
              vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_end := te',
              confl_lit0 := c0', confl_lit1 := c1' }
            scratch := { st.scratch with ant_sz := asz' } }
        BbTrailInv c F0 F_cur s0 st' saved0 max_lvl →
        st.core.trail_end ≤ te' →
        (∀ i < st.core.trail_end, trl'[i]? = st.core.trl[i]?) →
        (∀ i < st.core.trail_end,
          let v := (st.core.trl[i]?.getD 0#32).toNat / 2
          lvl'[v]? = st.core.lvl[v]? ∧ rsns'[v]? = st.core.rsns[v]?) →
        (∀ saved, saved0 ≤ saved → saved ≤ prop_start.toNat → 0 < st.core.cur_level →
          BackboneProbeSeg F_cur st saved st.core.cur_level →
          BackboneProbeSeg F_cur st' saved st.core.cur_level) →
        (ok = false →
          c0'.toNat < 2 * s0.core.cur_vars ∧ c1'.toNat < 2 * s0.core.cur_vars ∧
          vals'[c0'.toNat]?.getD 0#8 = 0xFF#8 ∧ vals'[c1'.toNat]?.getD 0#8 = 0xFF#8 ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause [c0'.toNat, c1'.toNat]) ∧
          ∃ idx0, prop_start.toNat ≤ idx0 ∧ idx0 < te' ∧
            (trl'[idx0]?.getD 0#32).toNat = c0'.toNat ^^^ 1) →
        (FullMem c st' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullBackboneAnalyzeM6Spec : Spec [i64, i32, i32, i64] [i32] :=
  fun (h, c0, c1, saved, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s0 st : FullState)
      (saved0 max_lvl : Nat) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s0 ∧ BbTrailInv c F0 F_cur s0 st saved0 max_lvl ∧
      0 < st.core.cur_level ∧ st.scratch.res_sz = BitVec.ofNat 64 saved0 ∧
      saved0 ≤ saved.toNat ∧
      st.core.rsns[(st.core.trl[saved.toNat]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
        0xFFFFFFFF#32 ∧
      BackboneProbeSeg F_cur st saved.toNat st.core.cur_level ∧
      c0.toNat < 2 * s0.core.cur_vars ∧ c1.toNat < 2 * s0.core.cur_vars ∧
      st.core.vals[c0.toNat]?.getD 0#8 = 0xFF#8 ∧
      st.core.vals[c1.toNat]?.getD 0#8 = 0xFF#8 ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [c0.toNat, c1.toNat]) ∧
      (∃ idx0, saved.toNat ≤ idx0 ∧ idx0 < st.core.trail_end ∧
        (st.core.trl[idx0]?.getD 0#32).toNat = c0.toNat ^^^ 1) ∧
      (FullMem c st ⋆ R) m ∧
      ∀ (uip : BitVec 32) (mrk' : List (BitVec 8)) m',
        mrk'.length = c.max_vars → (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
        (uip ≠ 0xFFFFFFFF#32 → uip.toNat < 2 * s0.core.cur_vars ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause [uip.toNat ^^^ 1])) →
        (FullMem c { st with core := { st.core with mrk := mrk' } } ⋆ R) m' → Q (uip, ()) m'

@[expose] def fullBackboneRoundM6Spec : Spec [i64, i64, .bool] [i64] :=
  fun (h, cand_n, _stop_early, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s0 : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s0 ∧ s0.core.cur_level = 0 ∧
      cand_n.toNat ≤ 2 * s0.core.cur_vars ∧
      (∀ i < cand_n.toNat, (s0.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) ∧
      (FullMem c s0 ⋆ R) m ∧
      ∀ keep' s' m',
        FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 →
        s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
        keep'.toNat ≤ 2 * s0.core.cur_vars →
        (∀ i < keep'.toNat, (s'.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars) →
        (s'.scratch.res_sz &&& 0x7FFFFFFFFFFFFFFF#64).toNat ≤ 2 * s0.core.cur_vars →
        (∀ i < (s'.scratch.res_sz &&& 0x7FFFFFFFFFFFFFFF#64).toNat,
          (s'.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars ∧
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause [(s'.scratch.work_stk2[i]?.getD 0#32).toNat])) →
        (FullMem c s' ⋆ R) m' → Q (keep', ()) m'

@[expose] def fullBackboneM6Spec : Spec [i64, i64] [i64] := fun (h, _tick_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ FullSparseInv c F0 s ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      M6HdrExtOk ext' ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      FullSparseInv c F0 s' →
      (s.core.cur_level = 0 → s'.core.cur_level = 0) →
      s'.core.probing = s.core.probing →
      (s'.core.cur_level = 0 ∧ s'.core.probing = s.core.probing) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-! ## 3. Canonical `SpecEntry` Table (`specs : List SpecEntry`) -/

@[expose] def specs : List SpecEntry :=
  [ ⟨"full_backbone_sched_m6",   [i64],                [i64],   fullBackboneSchedM6Spec,   true⟩
  , ⟨"full_backbone_keep_m6",    [i64, i64],           [],      fullBackboneKeepM6Spec,    true⟩
  , ⟨"full_backbone_unwind_m6",  [i64, i64, i64],      [],      fullBackboneUnwindM6Spec,  true⟩
  , ⟨"full_backbone_prop_m6",    [i64, i64, .bool],    [.bool], fullBackbonePropM6Spec,    true⟩
  , ⟨"full_backbone_analyze_m6", [i64, i32, i32, i64], [i32],   fullBackboneAnalyzeM6Spec, true⟩
  , ⟨"full_backbone_round_m6",   [i64, i64, .bool],    [i64],   fullBackboneRoundM6Spec,   true⟩
  , ⟨"full_backbone_m6",         [i64, i64],           [i64],   fullBackboneM6Spec,        true⟩
  ]

theorem fullBackboneSchedM6Spec_xfree : Spec.XFree fullBackboneSchedM6Spec := by xfree
theorem fullBackboneKeepM6Spec_xfree : Spec.XFree fullBackboneKeepM6Spec := by xfree
theorem fullBackboneUnwindM6Spec_xfree : Spec.XFree fullBackboneUnwindM6Spec := by xfree
theorem fullBackbonePropM6Spec_xfree : Spec.XFree fullBackbonePropM6Spec := by xfree
theorem fullBackboneAnalyzeM6Spec_xfree : Spec.XFree fullBackboneAnalyzeM6Spec := by xfree
theorem fullBackboneRoundM6Spec_xfree : Spec.XFree fullBackboneRoundM6Spec := by xfree
theorem fullBackboneM6Spec_xfree : Spec.XFree fullBackboneM6Spec := by xfree

theorem specs_sigs : specs.map SpecEntry.sig = Src.Backbone.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : ∀ e ∈ specs, e.noExit = true := by decide

theorem specs_xfree : ∀ e ∈ specs, Spec.XFree e.spec := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fullBackboneSchedM6Spec_xfree
  · exact fullBackboneKeepM6Spec_xfree
  · exact fullBackboneUnwindM6Spec_xfree
  · exact fullBackbonePropM6Spec_xfree
  · exact fullBackboneAnalyzeM6Spec_xfree
  · exact fullBackboneRoundM6Spec_xfree
  · exact fullBackboneM6Spec_xfree

theorem has_full_backbone_sched_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_backbone_sched_m6" fullBackboneSchedM6Spec :=
  Env.Sat.has h (.head _) fullBackboneSchedM6Spec_xfree

theorem has_full_backbone_keep_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_backbone_keep_m6" fullBackboneKeepM6Spec :=
  Env.Sat.has h (.tail _ (.head _)) fullBackboneKeepM6Spec_xfree

theorem has_full_backbone_unwind_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_backbone_unwind_m6" fullBackboneUnwindM6Spec :=
  Env.Sat.has h (.tail _ (.tail _ (.head _))) fullBackboneUnwindM6Spec_xfree

theorem has_full_backbone_prop_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_backbone_prop_m6" fullBackbonePropM6Spec :=
  Env.Sat.has h (.tail _ (.tail _ (.tail _ (.head _)))) fullBackbonePropM6Spec_xfree

theorem has_full_backbone_analyze_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_backbone_analyze_m6" fullBackboneAnalyzeM6Spec :=
  Env.Sat.has h (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
    fullBackboneAnalyzeM6Spec_xfree

theorem has_full_backbone_round_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_backbone_round_m6" fullBackboneRoundM6Spec :=
  Env.Sat.has h (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
    fullBackboneRoundM6Spec_xfree

theorem has_full_backbone_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_backbone_m6" fullBackboneM6Spec :=
  Env.Sat.has h (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
    fullBackboneM6Spec_xfree

end LeanQbe.T.Examples.Kissat.Proof.Backbone.Spec
