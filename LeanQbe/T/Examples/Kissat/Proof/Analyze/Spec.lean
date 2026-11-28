/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Analyze
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Bump.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Deduce.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Learn.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Minimize.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical `Spec` Table for `Kissat/Src/Analyze.lean` (`5` fns)

Canonical UNSAT-sound `Spec` definitions, `deps`, `Spec.XFree` proofs, `specs` table matching
`Src.Analyze.fns` 1:1 (`noExit := true`), `specs_sigs`, `specs_nodup`, `specs_noExit`,
`specs_xfree`, and `Env.Has` projections (`0` legacy imports, `0` `@[expose]` on theorems).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Analyze.Spec

open Std.Sat
open LeanQbe.T
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Analyze

public section

/-! ## 1. Upstream Extern Dependency Table (`deps`) -/

/-- Canonical upstream specification dependencies for `Src.Analyze.fns` (`16` externs across
`Backtrack`, `Bump`, `Deduce`, `Learn`, `Limits`, `Minimize`, `Tiers`). -/
@[expose] def deps : List SpecEntry :=
  Backtrack.Spec.specs ++ Bump.Spec.specs ++ Deduce.Spec.specs ++
  Learn.Spec.specs ++ Limits.Spec.specs ++ Minimize.Spec.specs ++
  Tiers.Spec.specs

/-! ## 2. Canonical Per-Function Specifications (`5` Functions) -/

/-- Canonical M6 header-threaded contract for `full_ana_failed_lit_m6_hdr(h)`,
equivalent to `m6aAnaFailedLitSpecP M6ExtW2bPres`. -/
@[expose] def fullAnaFailedLitM6HdrSpec : Spec [i64] [i64] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat)
      (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧
      FullCutInvW c F0 F_cur cut s ∧ 0 < s.core.cur_level ∧
      FullConflictOkCut F_cur cut s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
        M6HdrExtOk ext' →
        (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.scratch.work_stk2 = s.scratch.work_stk2 →
        (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
          s'.core.cur_level ≤ s.core.cur_level ∧
          s'.core.dense_mode = s.core.dense_mode) →
        (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
        (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧
          s'.core.cur_level < s.core.cur_level) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Canonical M6 header-threaded contract for `full_restore_bump_ana_mode_fid(h, allow_reasons)`,
equivalent to `s13RestoreBumpAnaModeSpecP M6ExtW2bPres`. -/
@[expose] def fullRestoreBumpAnaModeSpec : Spec [i64, .bool] [] :=
  fun (h, _allow_reasons, ()) m Q _ =>
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ mrk' mcl' repr' sc' ext' m',
        let s' : FullState :=
          { core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' }
            scratch := sc' }
        s'.LengthsOk c → (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
        (s.core.probing = 0#64 → mcl' = 0) →
        (s.core.probing ≠ 0#64 → mcl' = s.core.min_clr_len) →
        FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
        M6HdrExtOk ext' →
        (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m'

/-- Canonical M6 header-threaded contract for `full_analyze_reasons_fid(h)`,
equivalent to `s13AnalyzeReasonsSpecP M6ExtW2bPres`. -/
@[expose] def fullAnalyzeReasonsSpec : Spec [i64] [] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ mrk' mcl' sc' ext' m',
        let s' : FullState :=
          { core := { s.core with mrk := mrk', min_clr_len := mcl' }
            scratch := sc' }
        s'.LengthsOk c →
        (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
        (s.core.probing = 0#64 → mcl' ≤ s.core.cur_vars ∧
          ∀ k < mcl', (sc'.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars) →
        (s.core.probing ≠ 0#64 → mcl' = s.core.min_clr_len) →
        FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
        M6HdrExtOk ext' →
        (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m'

/-! ## 3. Canonical Table (`specs`) & Structural Theorems -/

/-- Canonical specification table aligned 1:1 with `Src.Analyze.fns`. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_ana_failed_lit_m6_hdr",      [i64],        [i64], fullAnaFailedLitM6HdrSpec,    true⟩
  , ⟨"full_restore_bump_ana_mode_fid", [i64, .bool], [],    fullRestoreBumpAnaModeSpec,   true⟩
  , ⟨"full_analyze_reasons_fid",       [i64],        [],    fullAnalyzeReasonsSpec,       true⟩
  , ⟨"full_analyze_core_m6",           [i64],        [i64], Proof.Spec.m6HdrAnalyzeSpec, true⟩
  , ⟨"full_analyze_m6_hdr",            [i64],        [i64], Proof.Spec.m6HdrAnalyzeSpec, true⟩
  ]

theorem fullAnaFailedLitM6HdrSpec_xfree : fullAnaFailedLitM6HdrSpec.XFree := by xfree

theorem fullRestoreBumpAnaModeSpec_xfree : fullRestoreBumpAnaModeSpec.XFree := by xfree

theorem fullAnalyzeReasonsSpec_xfree : fullAnalyzeReasonsSpec.XFree := by xfree

theorem m6HdrAnalyzeSpec_xfree : Proof.Spec.m6HdrAnalyzeSpec.XFree :=
  fun _ _ _ _ _ h => Proof.Spec.m6HdrAnalyzeSpec_monoX h

theorem specs_sigs : specs.map SpecEntry.sig = fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

theorem specs_xfree : ∀ e ∈ specs, e.spec.XFree := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact fullAnaFailedLitM6HdrSpec_xfree
  · exact fullRestoreBumpAnaModeSpec_xfree
  · exact fullAnalyzeReasonsSpec_xfree
  · exact m6HdrAnalyzeSpec_xfree
  · exact m6HdrAnalyzeSpec_xfree

/-! ## 4. Constructors, Eliminators & `Env.Has` Projections -/

theorem fullAnaFailedLitM6HdrSpec_intro
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat}
    {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext)
    (hcut : FullCutInvW c F0 F_cur cut s) (hlvl : 0 < s.core.cur_level)
    (hcf : FullConflictOkCut F_cur cut s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      M6HdrExtOk ext' →
      (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧
        s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧
        s'.core.cur_level < s.core.cur_level) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    fullAnaFailedLitM6HdrSpec (c.hdr, ()) m Q X :=
  ⟨c, F0, F_cur, cut, ext, s, R, rfl, hcfg, hext, hcut, hlvl, hcf, hm, hQ⟩

theorem fullAnaFailedLitM6HdrSpec_elim
    {h : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hs : fullAnaFailedLitM6HdrSpec (h, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat)
      (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧
      FullCutInvW c F0 F_cur cut s ∧ 0 < s.core.cur_level ∧
      FullConflictOkCut F_cur cut s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
        M6HdrExtOk ext' →
        (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.scratch.work_stk2 = s.scratch.work_stk2 →
        (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
          s'.core.cur_level ≤ s.core.cur_level ∧
          s'.core.dense_mode = s.core.dense_mode) →
        (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
        (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧
          s'.core.cur_level < s.core.cur_level) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m' :=
  hs

theorem fullRestoreBumpAnaModeSpec_intro
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState} {allow_reasons : Bool}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hmrk0 : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ mrk' mcl' repr' sc' ext' m',
      let s' : FullState :=
        { core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' }
          scratch := sc' }
      s'.LengthsOk c → (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
      (s.core.probing = 0#64 → mcl' = 0) →
      (s.core.probing ≠ 0#64 → mcl' = s.core.min_clr_len) →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      M6HdrExtOk ext' →
      (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m') :
    fullRestoreBumpAnaModeSpec (c.hdr, allow_reasons, ()) m Q X :=
  ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hmrk0, hm, hQ⟩

theorem fullRestoreBumpAnaModeSpec_elim
    {h : BitVec 64} {allow_reasons : Bool} {m : Mem 64} {Q : Post []} {X : XPost}
    (hs : fullRestoreBumpAnaModeSpec (h, allow_reasons, ()) m Q X) :
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ mrk' mcl' repr' sc' ext' m',
        let s' : FullState :=
          { core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' }
            scratch := sc' }
        s'.LengthsOk c → (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
        (s.core.probing = 0#64 → mcl' = 0) →
        (s.core.probing ≠ 0#64 → mcl' = s.core.min_clr_len) →
        FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
        M6HdrExtOk ext' →
        (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m' :=
  hs

theorem fullAnalyzeReasonsSpec_intro
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post []} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hmrk0 : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ mrk' mcl' sc' ext' m',
      let s' : FullState :=
        { core := { s.core with mrk := mrk', min_clr_len := mcl' }
          scratch := sc' }
      s'.LengthsOk c →
      (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
      (s.core.probing = 0#64 → mcl' ≤ s.core.cur_vars ∧
        ∀ k < mcl', (sc'.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars) →
      (s.core.probing ≠ 0#64 → mcl' = s.core.min_clr_len) →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      M6HdrExtOk ext' →
      (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m') :
    fullAnalyzeReasonsSpec (c.hdr, ()) m Q X :=
  ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hmrk0, hm, hQ⟩

theorem fullAnalyzeReasonsSpec_elim
    {h : BitVec 64} {m : Mem 64} {Q : Post []} {X : XPost}
    (hs : fullAnalyzeReasonsSpec (h, ()) m Q X) :
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ mrk' mcl' sc' ext' m',
        let s' : FullState :=
          { core := { s.core with mrk := mrk', min_clr_len := mcl' }
            scratch := sc' }
        s'.LengthsOk c →
        (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
        (s.core.probing = 0#64 → mcl' ≤ s.core.cur_vars ∧
          ∀ k < mcl', (sc'.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars) →
        (s.core.probing ≠ 0#64 → mcl' = s.core.min_clr_len) →
        FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
        M6HdrExtOk ext' →
        (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m' :=
  hs

private theorem mem_has_specs {Γ : Env} (h : Γ.Sat specs) {nm : Sym} {as bs : List Ty}
    {sp : Spec as bs} (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ specs)
    (hx : sp.XFree) : Γ.Has nm sp :=
  Env.Sat.has h hmem hx

theorem has_full_ana_failed_lit_m6_hdr {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_ana_failed_lit_m6_hdr" fullAnaFailedLitM6HdrSpec :=
  mem_has_specs h (by simp [specs]) fullAnaFailedLitM6HdrSpec_xfree

theorem has_full_restore_bump_ana_mode_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_restore_bump_ana_mode_fid" fullRestoreBumpAnaModeSpec :=
  mem_has_specs h (by simp [specs]) fullRestoreBumpAnaModeSpec_xfree

theorem has_full_analyze_reasons_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_analyze_reasons_fid" fullAnalyzeReasonsSpec :=
  mem_has_specs h (by simp [specs]) fullAnalyzeReasonsSpec_xfree

theorem has_full_analyze_core_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_analyze_core_m6" Proof.Spec.m6HdrAnalyzeSpec :=
  mem_has_specs h (by simp [specs]) m6HdrAnalyzeSpec_xfree

theorem has_full_analyze_m6_hdr {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_analyze_m6_hdr" Proof.Spec.m6HdrAnalyzeSpec :=
  mem_has_specs h (by simp [specs]) m6HdrAnalyzeSpec_xfree

end

end LeanQbe.T.Examples.Kissat.Proof.Analyze.Spec
