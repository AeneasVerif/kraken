/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Analyze.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
public import LeanQbe.T.Examples.Kissat.Proof.Lucky.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Src.Lucky
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Lucky.Wp0
import LeanQbe.T.Examples.Kissat.Proof.Lucky.Wp1

/-!
# Canonical Segment Certificate for `Kissat.Src.Lucky` (`Proof.Lucky.Cert`)

Defines `deps`, `specs_sigs`, `specs_nodup`, `specs_noExit`, and assembles
`cert : SegCert deps Src.Lucky.fns Spec.specs`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Lucky

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Proof.Lib
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Lucky
open LeanQbe.T.Examples.Kissat.Proof.Lucky.Spec

/-- Canonical upstream specification table covering all `extern` callees of
`Src.Lucky` (`Arena`, `Backtrack`, `PropSearch`, `Analyze`). -/
@[expose] def deps : List SpecEntry :=
  Arena.Spec.specs ++ Backtrack.Spec.specs ++
  PropSearch.Spec.specs ++ Analyze.Spec.specs

theorem specs_sigs : Spec.specs.map SpecEntry.sig = Src.Lucky.fns.map Fn.sig := rfl

theorem specs_nodup : (Spec.specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : Spec.specs.all SpecEntry.noExit = true := rfl

private theorem luckyOrdSpec_xfree : Spec.luckyOrdSpec.XFree := by
  unfold Spec.luckyOrdSpec; exact FullContract.toSpec_xfree _

private theorem luckyScanSpec_xfree : Spec.luckyScanSpec.XFree := by
  unfold Spec.luckyScanSpec; exact M6HdrContract.toSpec_xfree _

private theorem luckyPolarSpec_xfree : Spec.luckyPolarSpec.XFree := by
  unfold Spec.luckyPolarSpec; exact FullContract.toSpec_xfree _

/-- Canonical segment certificate for `Kissat.Src.Lucky` (`4` functions). -/
theorem cert : SegCert deps Src.Lucky.fns Spec.specs := by
  intro Γ hdeps hSat
  have hAr : Γ.Sat Arena.Spec.specs := fun e he => hdeps e (by
    simp only [deps, List.mem_append]; exact Or.inl (Or.inl (Or.inl he)))
  have hBk : Γ.Sat Backtrack.Spec.specs := fun e he => hdeps e (by
    simp only [deps, List.mem_append]; exact Or.inl (Or.inl (Or.inr he)))
  have hPr : Γ.Sat PropSearch.Spec.specs := fun e he => hdeps e (by
    simp only [deps, List.mem_append]; exact Or.inl (Or.inr he))
  have hAn : Γ.Sat Analyze.Spec.specs := fun e he => hdeps e (by
    simp only [deps, List.mem_append]; exact Or.inr he)
  have hOrd := SpecTable.has_at hSat 0 rfl luckyOrdSpec_xfree
  have hScan := SpecTable.has_at hSat 1 rfl luckyScanSpec_xfree
  have hPolar := SpecTable.has_at hSat 2 rfl luckyPolarSpec_xfree
  have hAssign := Backtrack.Spec.has_full_assign hBk
  have hBt := Backtrack.Spec.has_full_backtrack hBk
  have hProp := PropSearch.Spec.has_full_propagate hPr
  have hAnaRaw := SpecTable.has_at hAn 4 rfl
    (by unfold Analyze.Spec.analyzeSpec; exact M6HdrContract.toSpec_xfree _)
  have hAna : Γ.Has "full_analyze_m6_hdr" m6HdrAnalyzeSpec := fun ⟨a0, ⟨⟩⟩ m Q X hs => by
    obtain ⟨c, F0, F_cur, ext, s, R, rfl, hinv, hcf, hm, hQ⟩ := m6HdrAnalyzeSpec_elim hs
    refine hAnaRaw (c.hdr, ()) m Q X ?_
    dsimp only [Analyze.Spec.analyzeSpec]
    exact M6HdrContract.intro (w := (F0, F_cur))
      hinv.cfgOk hinv.extOk hinv.sparseW.1 ⟨hinv.sparseW, hcf⟩ hm
      fun ⟨r, ⟨⟩⟩ ext' s' m' hext' _ hlen' ⟨hr, hcv', hfu', hws2', h20', h0', h1'⟩ hm' =>
        hQ r ext' s' m' hext' hlen' hr hcv' hfu'
          ⟨hws2', fun eq20 => let ⟨_, ho, hcl, hdm⟩ := h20' eq20; ⟨ho, hcl, hdm⟩⟩
          (fun eq20 => (h20' eq20).1) h0'
          (fun eq1 => let ⟨hsp', hcl'⟩ := h1' eq1
                      ⟨FullM6HdrInvW.mk_inv hinv.cfgOk hext' hsp', hcl'⟩)
          hm'
  have hNext := Arena.Spec.has_full_arena_next hAr
  exact
    ⟨ SpecEntry.Impl.of (full_lucky_ord_fid_wp Γ)
    , SpecEntry.Impl.of (full_lucky_scan_wp Γ hOrd hAssign hBt hProp hAna)
    , SpecEntry.Impl.of (full_lucky_polar_m7_wp Γ hNext)
    , SpecEntry.Impl.of (full_lucky_late_m7_wp Γ hPolar hScan hAssign hBt hProp)
    , trivial
    ⟩

end LeanQbe.T.Examples.Kissat.Proof.Lucky
