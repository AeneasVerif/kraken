/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts2
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Src.Deduce
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specification Table for `Kissat.Src.Deduce` (`Proof.Deduce.Spec`)

Defines one canonical `XFree` (`XPost`-polymorphic) specification per function in
`Src.Deduce.fns` (`7` functions), aligns `specs : List SpecEntry` 1-to-1 with `Src.Deduce.fns`,
and bundles `deps := Arena.Spec.specs ++ Tiers.Spec.specs ++ Watch.Spec.specs` (`0` legacy imports,
`0` `@[expose]` on theorems/lemmas/sections).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Deduce.Spec

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src
open Kraken.Bedrock2.Test

/-- Canonical specification for `full_analyze_lit`. -/
abbrev fullAnalyzeLitSpec : Spec [i64, i32, i32] [.bool] :=
  Proof.Spec.fullAnalyzeLitSpec

/-- Canonical specification for `full_clear_ana`. -/
abbrev fullClearAnaSpec : Spec [i64] [] :=
  Proof.Spec.fullClearAnaSpec

/-- Canonical specification for `full_otfs_bin`. -/
abbrev fullOtfsBinSpec : Spec [i64, i32, i32] [.bool] :=
  Proof.Spec.fullOtfsBinSpec

/-- Canonical specification for `full_otfs_subsume`. -/
abbrev fullOtfsSubsumeSpec : Spec [i64, i32, i64, i64, .bool] [] :=
  Proof.Spec.fullOtfsSubsumeSpec

/-- Canonical Step-13 specification for `full_analyze_rsn_m6_hdr`: extends
`Proof.Spec.m6HdrAnalyzeRsnSpec` with `min_clr'` updates from `frame_trail` bit-31 glue
recomputation. -/
@[expose] def s13AnalyzeRsnHdrSpec : Spec [i64, i32, i32] [.bool] :=
  fun (h, rsn, skip_var, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat)
      (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      FullWitnessCutInv c F0 F_cur cut s.core ∧ FullAnaMarksCov c s ∧
      s.core.tmp_len ≤ s.core.cur_vars ∧ s.core.tmp_cnt + s.core.cur_vars + 1 < 2 ^ 64 ∧
      (rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
        rsn.toNat ∈ fullArenaClauseRefs s) ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (ok : Bool) mrk' tmp' mclr' tc' tl' mcl' arena' sc' ext' m',
        let s' : FullState :=
          { s with
            core := { s.core with mrk := mrk', tmp := tmp', min_clr := mclr',
                                  tmp_cnt := tc', tmp_len := tl',
                                  min_clr_len := mcl', arena := arena' }
            scratch := sc' }
        M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6ExtW2bPres ext ext') →
        s'.LengthsOk c → FullWitnessCutInv c F0 F_cur cut s'.core → FullAnaMarksCov c s' →
        FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
        s.core.tmp_len ≤ tl' → tl' ≤ s.core.cur_vars → s.core.tmp_cnt ≤ tc' →
        fullArenaClauseRefs s' = fullArenaClauseRefs s →
        (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
          fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
          fullArenaClauseLits s' r = fullArenaClauseLits s r) →
        (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
          mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8) →
        (∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?) →
        (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
          ∃ l ∈ fullRsnLits s rsn, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
            0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
            (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level) →
        (∀ j, s.core.tmp_len ≤ j → j < tl' → let l := (tmp'[j]?.getD 0#32).toNat
          l ∈ fullRsnLits s rsn ∧ l < 2 * s.core.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
          s.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
          (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧ mrk'[l / 2]?.getD 0#8 ≠ 0#8) →
        (∀ j1 j2, s.core.tmp_len ≤ j1 → j1 < j2 → j2 < tl' →
          (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2) →
        (tc' - s.core.tmp_cnt = ((List.range s.core.cur_vars).filter fun w =>
          decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
          decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level)).length) →
        (sc'.res_sz = s.scratch.res_sz + BitVec.ofNat 64 ((List.range s.core.cur_vars).filter
          fun w => decide (s.core.mrk[w]?.getD 0#8 = 0#8) &&
            decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length) →
        (ok = true → rsn ≠ 0xFFFFFFFF#32 ∧
          sc'.ant_sz = s.scratch.ant_sz + BitVec.ofNat 64 ((fullRsnLits s rsn).countP fun l =>
            decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
              (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)) ∧
          ∀ l ∈ fullRsnLits s rsn, l / 2 < s.core.cur_vars ∧ (l / 2 ≠ skip_var.toNat →
            (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
            (s.core.mrk[l / 2]?.getD 0#8 = 0#8 →
              (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
              (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat →
                (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level →
                ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧
                  (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (ok, ()) m'

/-- Canonical Step-13 contract for `full_otfs_large`: extends `Proof.Spec.fullOtfsLargeSpec` by
allowing `s'.core.flags` (`flags'`) to mark irredundant OTFS literals with `|= 24u`. -/
@[expose] def step13OtfsLargeSpec : Spec [i64, i32, i32] [.bool] :=
  fun (h, cref, uip, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut idx_u : Nat) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut s.core ∧
      FullArenaVarsNodup s ∧ s.core.dense_mode = 0#64 ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
      fullArenaClauseGarb s cref.toNat = false ∧ uip.toNat < 2 * s.core.cur_vars ∧
      idx_u < cut ∧ (s.core.trl[idx_u]?.getD 0#32).toNat = uip.toNat ∧
      s.core.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref ∧
      (s.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = s.core.cur_level ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((fullArenaClauseLits s cref.toNat).filter fun l =>
          decide (l ≠ uip.toNat ∧ (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∨
            l = (s.core.arena[cref.toNat + 3]?.getD 0#32).toNat ∨
            l = (s.core.arena[cref.toNat + 4]?.getD 0#32).toNat)))) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) flags' arena' wvec' wstk' wlen' wu' oom' sc' m',
        let s' : FullState :=
          { s with
            core := { s.core with flags := flags', arena := arena', wvec := wvec',
                                  wstk := wstk', wlen := wlen', wusable := wu', oom := oom' }
            scratch := sc' }
        s'.LengthsOk c → FullWitnessCutInv c F0 F_cur idx_u s'.core → FullArenaVarsNodup s' →
        FullExtScratchPres s s' → sc'.work_stk1 = s.scratch.work_stk1 →
        sc'.work_stk2 = s.scratch.work_stk2 → sc'.res_sz = s.scratch.res_sz →
        fullArenaClauseRefs s' = fullArenaClauseRefs s →
        (ok = true → cref.toNat ∈ fullArenaClauseRefs s' ∧
          fullArenaClauseGarb s' cref.toNat = false ∧
          ∀ l ∈ fullArenaClauseLits s' cref.toNat, s'.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
            ((s'.core.lvl[l / 2]?.getD 0#32).toNat = s'.core.cur_level →
              ∃ m < idx_u, (s'.core.trl[m]?.getD 0#32).toNat = l ^^^ 1)) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Canonical `M6HdrMem` specification for `full_deduce_1uip_m6_hdr` (identical to
`m7Deduce1uipHdrSpec` / `s13Deduce1uipHdrSpec`). -/
@[expose] def fullDeduce1uipM6HdrSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ c F0 F_cur cut ext s R, h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧
    FullCutInvW c F0 F_cur cut s ∧ 0 < s.core.cur_level ∧ FullConflictOkCut F_cur cut s ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullOtfsInvW c F0 F_cur s' ∧ s'.core.cur_level = s.core.cur_level ∧
        1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
        ((s'.core.tmp.take s'.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
        (∀ k < s'.core.tmp_len, let l := (s'.core.tmp[k]?.getD 0#32).toNat
          l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
        (∀ k, 1 ≤ k → k < s'.core.tmp_len →
          let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
          0 < lv ∧ lv < s'.core.cur_level) ∧
        (s'.core.lvl[(s'.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
          s'.core.cur_level ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s'.core.tmp.take s'.core.tmp_len).map BitVec.toNat))) →
      (r = 2#64 → ∃ cut' ≤ s'.core.trail_end, FullCutInvW c F0 F_cur cut' s' ∧
        s'.core.cur_level = s.core.cur_level ∧ FullConflictOkCut F_cur cut' s') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

theorem fullAnalyzeLitSpec_xfree : Spec.XFree fullAnalyzeLitSpec := by xfree

theorem s13AnalyzeRsnHdrSpec_xfree : Spec.XFree s13AnalyzeRsnHdrSpec := by xfree

theorem fullClearAnaSpec_xfree : Spec.XFree fullClearAnaSpec := by xfree

theorem step13OtfsLargeSpec_xfree : Spec.XFree step13OtfsLargeSpec := by xfree

theorem fullOtfsBinSpec_xfree : Spec.XFree fullOtfsBinSpec := by xfree

theorem fullOtfsSubsumeSpec_xfree : Spec.XFree fullOtfsSubsumeSpec := by xfree

theorem fullDeduce1uipM6HdrSpec_xfree : Spec.XFree fullDeduce1uipM6HdrSpec := by xfree

/-- Upstream capability dependencies for `Kissat.Src.Deduce` (`Arena`, `Tiers`, `Watch`). -/
@[expose] def deps : List SpecEntry :=
  Arena.Spec.specs ++ Tiers.Spec.specs ++ Watch.Spec.specs

/-- Canonical `SpecEntry` table matching `Src.Deduce.fns` 1-to-1. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_analyze_lit", [i64, i32, i32], [.bool], fullAnalyzeLitSpec, true⟩
  , ⟨"full_analyze_rsn_m6_hdr", [i64, i32, i32], [.bool], s13AnalyzeRsnHdrSpec, true⟩
  , ⟨"full_clear_ana", [i64], [], fullClearAnaSpec, true⟩
  , ⟨"full_otfs_large", [i64, i32, i32], [.bool], step13OtfsLargeSpec, true⟩
  , ⟨"full_otfs_bin", [i64, i32, i32], [.bool], fullOtfsBinSpec, true⟩
  , ⟨"full_otfs_subsume", [i64, i32, i64, i64, .bool], [], fullOtfsSubsumeSpec, true⟩
  , ⟨"full_deduce_1uip_m6_hdr", [i64], [i64], fullDeduce1uipM6HdrSpec, true⟩ ]

theorem specs_xfree : ∀ e ∈ specs, e.spec.XFree := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fullAnalyzeLitSpec_xfree
  · exact s13AnalyzeRsnHdrSpec_xfree
  · exact fullClearAnaSpec_xfree
  · exact step13OtfsLargeSpec_xfree
  · exact fullOtfsBinSpec_xfree
  · exact fullOtfsSubsumeSpec_xfree
  · exact fullDeduce1uipM6HdrSpec_xfree

theorem specs_sigs : specs.map SpecEntry.sig = Deduce.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

theorem has_full_analyze_lit {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_analyze_lit" fullAnalyzeLitSpec :=
  Env.Sat.has h List.mem_cons_self fullAnalyzeLitSpec_xfree

theorem has_full_analyze_rsn_m6_hdr {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_analyze_rsn_m6_hdr" s13AnalyzeRsnHdrSpec :=
  Env.Sat.has h (.tail _ List.mem_cons_self) s13AnalyzeRsnHdrSpec_xfree

theorem has_full_clear_ana {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_clear_ana" fullClearAnaSpec :=
  Env.Sat.has h (.tail _ (.tail _ List.mem_cons_self)) fullClearAnaSpec_xfree

theorem has_full_otfs_large {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_otfs_large" step13OtfsLargeSpec :=
  Env.Sat.has h (.tail _ (.tail _ (.tail _ List.mem_cons_self))) step13OtfsLargeSpec_xfree

theorem has_full_otfs_bin {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_otfs_bin" fullOtfsBinSpec :=
  Env.Sat.has h (.tail _ (.tail _ (.tail _ (.tail _ List.mem_cons_self))))
    fullOtfsBinSpec_xfree

theorem has_full_otfs_subsume {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_otfs_subsume" fullOtfsSubsumeSpec :=
  Env.Sat.has h (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ List.mem_cons_self)))))
    fullOtfsSubsumeSpec_xfree

theorem has_full_deduce_1uip_m6_hdr {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_deduce_1uip_m6_hdr" fullDeduce1uipM6HdrSpec :=
  Env.Sat.has h
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ List.mem_cons_self))))))
    fullDeduce1uipM6HdrSpec_xfree

end LeanQbe.T.Examples.Kissat.Proof.Deduce.Spec
