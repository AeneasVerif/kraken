/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Bump
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Heap.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Kissat Canonical `Spec` Table for `Src.Bump` (`Proof.Bump.Spec`)

Canonical `Env` contracts and `CanonicalEnv` `SpecEntry` list (`specs`) for the `9` functions in
`Src.Bump.fns`, depending strictly on `Float64.Spec.specs ++ Heap.Spec.specs ++ Tiers.Spec.specs`
with `0` legacy `Full[A-Z0-9]`/`PatchModule`/`Solver` imports.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Bump.Spec

open Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

public section

/-! ## 1. Canonical Contracts for `Src.Bump` Functions -/

@[expose] def fullAnaSiftSpec : Spec [i64, i64, i64, i64, i64] [] :=
  fun (qs_ptr, ana_ptr, cv, start, n, ()) m Q _ =>
    ∃ (qs ana : List (BitVec 32)) (R : Mem 64 → Prop),
      cv.toNat ≤ qs.length ∧ start.toNat ≤ n.toNat ∧ n.toNat ≤ ana.length ∧
      n.toNat < 2 ^ 62 ∧
      (∀ k < n.toNat, (ana[k]?.getD 0#32).toNat < cv.toNat) ∧
      (array (t := i32) qs_ptr qs ⋆ array (t := i32) ana_ptr ana ⋆ R) m ∧
      ∀ ana' m',
        ana'.length = ana.length → (ana'.take n.toNat).Perm (ana.take n.toNat) →
        (∀ k, n.toNat ≤ k → ana'[k]? = ana[k]?) →
        (∀ k < n.toNat, (ana'[k]?.getD 0#32).toNat < cv.toNat) →
        (array (t := i32) qs_ptr qs ⋆ array (t := i32) ana_ptr ana' ⋆ R) m' → Q () m'

theorem fullAnaSiftSpec_monoX {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post []} {X X' : XPost} (h : fullAnaSiftSpec xs m Q X) :
    fullAnaSiftSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, _, _, ⟨⟩⟩; exact h

theorem fullAnaSiftSpec_xfree : fullAnaSiftSpec.XFree := by xfree

theorem fullAnaSiftSpec_of {qs_ptr ana_ptr cv start n : BitVec 64}
    {qs ana : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hcv_qs : cv.toNat ≤ qs.length) (hst_n : start.toNat ≤ n.toNat)
    (hn_ana : n.toNat ≤ ana.length) (hn62 : n.toNat < 2 ^ 62)
    (hcov : ∀ k < n.toNat, (ana[k]?.getD 0#32).toNat < cv.toNat)
    (hm : (array (t := i32) qs_ptr qs ⋆ array (t := i32) ana_ptr ana ⋆ R) m)
    (hQ : ∀ ana' m',
      ana'.length = ana.length → (ana'.take n.toNat).Perm (ana.take n.toNat) →
      (∀ k, n.toNat ≤ k → ana'[k]? = ana[k]?) →
      (∀ k < n.toNat, (ana'[k]?.getD 0#32).toNat < cv.toNat) →
      (array (t := i32) qs_ptr qs ⋆ array (t := i32) ana_ptr ana' ⋆ R) m' → Q () m') :
    fullAnaSiftSpec (qs_ptr, ana_ptr, cv, start, n, ()) m Q X :=
  ⟨qs, ana, R, hcv_qs, hst_n, hn_ana, hn62, hcov, hm, hQ⟩

theorem fullAnaSiftSpec_elim {qs_ptr ana_ptr cv start n : BitVec 64} {m : Mem 64}
    {Q : Post []} {X : XPost} (hs : fullAnaSiftSpec (qs_ptr, ana_ptr, cv, start, n, ()) m Q X) :
    ∃ (qs ana : List (BitVec 32)) (R : Mem 64 → Prop),
      cv.toNat ≤ qs.length ∧ start.toNat ≤ n.toNat ∧ n.toNat ≤ ana.length ∧
      n.toNat < 2 ^ 62 ∧
      (∀ k < n.toNat, (ana[k]?.getD 0#32).toNat < cv.toNat) ∧
      (array (t := i32) qs_ptr qs ⋆ array (t := i32) ana_ptr ana ⋆ R) m ∧
      ∀ ana' m',
        ana'.length = ana.length → (ana'.take n.toNat).Perm (ana.take n.toNat) →
        (∀ k, n.toNat ≤ k → ana'[k]? = ana[k]?) →
        (∀ k < n.toNat, (ana'[k]?.getD 0#32).toNat < cv.toNat) →
        (array (t := i32) qs_ptr qs ⋆ array (t := i32) ana_ptr ana' ⋆ R) m' → Q () m' :=
  hs

@[expose] def fullSortAnaQsSpec : Spec [i64, i64] [] := fun (h, n, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ n.toNat ≤ s.core.cur_vars ∧
    (∀ k < n.toNat, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ ws1' repr' wsort' sbuf' m',
      ws1'.length = 2 * c.max_vars →
      repr'.length = 2 * c.max_vars →
      wsort'.length = 2 * c.max_vars →
      sbuf'.length = c.scratch_cap →
      (ws1'.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) →
      (∀ k, n.toNat ≤ k → ws1'[k]? = s.scratch.work_stk1[k]?) →
      (∀ k < n.toNat, (ws1'[k]?.getD 0#32).toNat < s.core.cur_vars) →
      (FullMem c { s with core := { s.core with repr := repr' }
                          scratch := { s.scratch with
                            work_stk1 := ws1', wsort := wsort', scratch_buf := sbuf' } } ⋆
        R) m' →
      Q () m'

theorem fullSortAnaQsSpec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post []}
    {X X' : XPost} (h : fullSortAnaQsSpec xs m Q X) : fullSortAnaQsSpec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

theorem fullSortAnaQsSpec_xfree : fullSortAnaQsSpec.XFree := by xfree

theorem fullSortAnaQsSpec_of {c : FullCfg} {s : FullState} {n : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hlen : s.LengthsOk c) (hn : n.toNat ≤ s.core.cur_vars)
    (hlt : ∀ k < n.toNat, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ ws1' repr' wsort' sbuf' m',
      ws1'.length = 2 * c.max_vars →
      repr'.length = 2 * c.max_vars →
      wsort'.length = 2 * c.max_vars →
      sbuf'.length = c.scratch_cap →
      (ws1'.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) →
      (∀ k, n.toNat ≤ k → ws1'[k]? = s.scratch.work_stk1[k]?) →
      (∀ k < n.toNat, (ws1'[k]?.getD 0#32).toNat < s.core.cur_vars) →
      (FullMem c { s with core := { s.core with repr := repr' }
                          scratch := { s.scratch with
                            work_stk1 := ws1', wsort := wsort', scratch_buf := sbuf' } } ⋆
        R) m' →
      Q () m') :
    fullSortAnaQsSpec (c.hdr, n, ()) m Q X :=
  ⟨c, s, R, rfl, hlen, hn, hlt, hm, hQ⟩

theorem fullSortAnaQsSpec_elim {h n : BitVec 64} {m : Mem 64} {Q : Post []} {X : XPost}
    (hs : fullSortAnaQsSpec (h, n, ()) m Q X) :
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ n.toNat ≤ s.core.cur_vars ∧
      (∀ k < n.toNat, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ ws1' repr' wsort' sbuf' m',
        ws1'.length = 2 * c.max_vars →
        repr'.length = 2 * c.max_vars →
        wsort'.length = 2 * c.max_vars →
        sbuf'.length = c.scratch_cap →
        (ws1'.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) →
        (∀ k, n.toNat ≤ k → ws1'[k]? = s.scratch.work_stk1[k]?) →
        (∀ k < n.toNat, (ws1'[k]?.getD 0#32).toNat < s.core.cur_vars) →
        (FullMem c { s with core := { s.core with repr := repr' }
                            scratch := { s.scratch with
                              work_stk1 := ws1', wsort := wsort', scratch_buf := sbuf' } } ⋆
          R) m' →
        Q () m' :=
  hs

@[expose] def FullBumpPre (allow_reasons : Bool) (c : FullCfg) (s : FullState) : Prop :=
  if allow_reasons then FullAnaMarksCov c s
  else s.core.min_clr_len ≤ s.core.cur_vars ∧
    ∀ k < s.core.min_clr_len, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars

theorem fullBumpPre_of_cov (allow_reasons : Bool) {c : FullCfg} {s : FullState}
    (hcov : FullAnaMarksCov c s) : FullBumpPre allow_reasons c s := by
  unfold FullBumpPre
  cases allow_reasons
  · exact ⟨hcov.1, fun k hk => (hcov.2.2.1 k hk).1⟩
  · exact hcov

theorem fullBumpPre_false_of {c : FullCfg} {s : FullState}
    (hmcl : s.core.min_clr_len ≤ s.core.cur_vars)
    (hlt : ∀ k < s.core.min_clr_len, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars) :
    FullBumpPre false c s := by
  unfold FullBumpPre; exact ⟨hmcl, hlt⟩

@[expose] def fullBumpAnalyzedModeSpec : Spec [i64, .bool] [] :=
  fun (h, allow_reasons, ()) m Q _ =>
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      FullBumpPre allow_reasons c s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ mrk' mcl' repr' sc' ext' m',
        let s' : FullState :=
          { s with
            core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' }
            scratch := sc' }
        s'.LengthsOk c →
        (FullAnaMarksCov c s → FullAnaMarksCov c s') →
        (allow_reasons = false → mrk' = s.core.mrk ∧ mcl' = s.core.min_clr_len ∧ ext' = ext) →
        (allow_reasons = false →
          ∀ k < mcl', (sc'.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars) →
        FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
        M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m'

theorem fullBumpAnalyzedModeSpec_monoX {xs : Tup Val [i64, .bool]} {m : Mem 64} {Q : Post []}
    {X X' : XPost} (h : fullBumpAnalyzedModeSpec xs m Q X) :
    fullBumpAnalyzedModeSpec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

theorem fullBumpAnalyzedModeSpec_xfree : fullBumpAnalyzedModeSpec.XFree := by xfree

theorem fullBumpAnalyzedModeSpec_of {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {allow_reasons : Bool} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hpre : FullBumpPre allow_reasons c s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ mrk' mcl' repr' sc' ext' m',
      let s' : FullState :=
        { s with
          core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' }
          scratch := sc' }
      s'.LengthsOk c →
      (FullAnaMarksCov c s → FullAnaMarksCov c s') →
      (allow_reasons = false → mrk' = s.core.mrk ∧ mcl' = s.core.min_clr_len ∧ ext' = ext) →
      (allow_reasons = false →
        ∀ k < mcl', (sc'.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars) →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m') :
    fullBumpAnalyzedModeSpec (c.hdr, allow_reasons, ()) m Q X :=
  ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hpre, hm, hQ⟩

theorem fullBumpAnalyzedModeSpec_elim {h : BitVec 64} {allow_reasons : Bool} {m : Mem 64}
    {Q : Post []} {X : XPost} (hs : fullBumpAnalyzedModeSpec (h, allow_reasons, ()) m Q X) :
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      FullBumpPre allow_reasons c s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ mrk' mcl' repr' sc' ext' m',
        let s' : FullState :=
          { s with
            core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' }
            scratch := sc' }
        s'.LengthsOk c →
        (FullAnaMarksCov c s → FullAnaMarksCov c s') →
        (allow_reasons = false → mrk' = s.core.mrk ∧ mcl' = s.core.min_clr_len ∧ ext' = ext) →
        (allow_reasons = false →
          ∀ k < mcl', (sc'.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars) →
        FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
        M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m' :=
  hs

private theorem safetyVoidSpec_xfree : fullSafetyVoidSpec.XFree := by xfree

private theorem safetyVarVoidSpec_xfree : fullSafetyVarVoidSpec.XFree := by xfree

/-! ## 2. Canonical `SpecEntry` Table & `Env.Sat` Projections -/

@[expose] def deps : List SpecEntry :=
  Float64.Spec.specs ++ Heap.Spec.specs ++ Tiers.Spec.specs

@[expose] def specs : List SpecEntry :=
  [ ⟨"full_rescale_m6", [i64], [], fullRescaleSpec, true⟩
  , ⟨"full_rescale", [i64], [], fullRescaleSpec, true⟩
  , ⟨"full_bump_var", [i64, i32], [], fullBumpVarSpec, true⟩
  , ⟨"full_bump_decay", [i64], [], fullBumpDecaySpec, true⟩
  , ⟨"full_queue_renumber", [i64], [], fullQueueRenumberSpec, true⟩
  , ⟨"full_queue_mtf", [i64, i32], [], fullQueueMtfSpec, true⟩
  , ⟨"full_ana_sift_m6", [i64, i64, i64, i64, i64], [], fullAnaSiftSpec, true⟩
  , ⟨"full_sort_ana_qs_m6", [i64, i64], [], fullSortAnaQsSpec, true⟩
  , ⟨"full_bump_analyzed_mode_fid", [i64, .bool], [], fullBumpAnalyzedModeSpec, true⟩
  ]

theorem specs_sigs : specs.map SpecEntry.sig = Src.Bump.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : ∀ e ∈ specs, e.noExit = true := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem specs_xfree : ∀ e ∈ specs, e.spec.XFree := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact safetyVoidSpec_xfree
  · exact safetyVoidSpec_xfree
  · exact safetyVarVoidSpec_xfree
  · exact safetyVoidSpec_xfree
  · exact safetyVoidSpec_xfree
  · exact safetyVarVoidSpec_xfree
  · exact fullAnaSiftSpec_xfree
  · exact fullSortAnaQsSpec_xfree
  · exact fullBumpAnalyzedModeSpec_xfree

theorem has_full_rescale_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_rescale_m6" fullRescaleSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 0) (by decide)) safetyVoidSpec_xfree

theorem has_full_rescale {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_rescale" fullRescaleSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 1) (by decide)) safetyVoidSpec_xfree

theorem has_full_bump_var {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bump_var" fullBumpVarSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 2) (by decide)) safetyVarVoidSpec_xfree

theorem has_full_bump_decay {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bump_decay" fullBumpDecaySpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 3) (by decide)) safetyVoidSpec_xfree

theorem has_full_queue_renumber {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_queue_renumber" fullQueueRenumberSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 4) (by decide)) safetyVoidSpec_xfree

theorem has_full_queue_mtf {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_queue_mtf" fullQueueMtfSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 5) (by decide)) safetyVarVoidSpec_xfree

theorem has_full_ana_sift_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_ana_sift_m6" fullAnaSiftSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 6) (by decide)) fullAnaSiftSpec_xfree

theorem has_full_sort_ana_qs_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_sort_ana_qs_m6" fullSortAnaQsSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 7) (by decide)) fullSortAnaQsSpec_xfree

theorem has_full_bump_analyzed_mode_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_bump_analyzed_mode_fid" fullBumpAnalyzedModeSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 8) (by decide)) fullBumpAnalyzedModeSpec_xfree

end

end LeanQbe.T.Examples.Kissat.Proof.Bump.Spec
