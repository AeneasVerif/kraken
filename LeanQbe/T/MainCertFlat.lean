/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainFlat
public import LeanQbe.T.MainCertCore
import LeanQbe.T.MainFlatLemmas

/-!
# Flat-Path Certificate Bridges (`MainCertFlat`)

Non-meta leaf exposing O(1) slice-map and `compileModuleFlat → compileModule` bridges for
`compile_linked_chunks! ... (flat := true)`. Proof terms stay opaque in `.olean.private`
(`0` `@[expose]` on theorems) so `MainFlatLemmas` proof edits do not rebuild downstream slices.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

universe u v

/-- Per-chunk slice equality lifting `l = fl.map g` to `(l.drop s).take k` in O(1). -/
theorem map_slice_eq {α : Type u} {β : Type v} (g : α → β) {l : List β} {fl : List α}
    (h : l = fl.map g) (s k : Nat) :
    (l.drop s).take k = ((fl.drop s).take k).map g := by
  subst h
  rw [List.map_take, List.map_drop]

/-- Last-chunk slice equality lifting `l = fl.map g` to `l.drop s` in O(1). -/
theorem map_drop_eq {α : Type u} {β : Type v} (g : α → β) {l : List β} {fl : List α}
    (h : l = fl.map g) (s : Nat) :
    l.drop s = (fl.drop s).map g := by
  subst h
  rw [List.map_drop]

/-- Transport a kernel-checked `compileModuleFlat` equality directly to `compileModule` over
`fs = ffs.map TFlatFn.toFn` without kernel unfolding of PHOAS `compileModule`. -/
theorem compileModule_of_flat_eq {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {ext : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {fs : List Fn} {ffs : List TFlatFn} {hs : List I.Hints}
    {code : List I.Directive} {bounds : List (Sym × Nat)}
    (hfs : fs = ffs.map TFlatFn.toFn)
    (h : compileModuleFlat I lt raBytes ext exits nX ffs hs = .ok (code, bounds)) :
    compileModule I lt raBytes ext exits nX fs hs = .ok (code, bounds) := by
  rw [hfs]
  exact compileModule_of_compileModuleFlat I lt raBytes ext exits nX ffs hs code bounds h

end LeanQbe.T
