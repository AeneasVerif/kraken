/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Src.Arena
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specification Table for `Kissat.Src.Arena` (`Proof.Arena.Spec`)

Reuses `Proof.Spec.fullArenaNextSpec` and `Proof.Spec.fullAllocClSpec` directly (`0` spec
duplication, `0` legacy imports, `0` `@[expose]` on theorems/lemmas).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Arena.Spec

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src

theorem fullArenaNextSpec_xfree : Spec.XFree fullArenaNextSpec := by xfree

theorem fullAllocClSpec_xfree : Spec.XFree fullAllocClSpec := by xfree

/-- Canonical `SpecEntry` table matching `Src.Arena.fns` 1-to-1. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  , ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], fullAllocClSpec, true⟩ ]

theorem specs_sigs : specs.map SpecEntry.sig = Arena.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

theorem has_full_arena_next {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_arena_next" fullArenaNextSpec :=
  Env.Sat.has h List.mem_cons_self fullArenaNextSpec_xfree

theorem has_full_alloc_cl {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_alloc_cl" fullAllocClSpec :=
  Env.Sat.has h (.tail _ List.mem_cons_self) fullAllocClSpec_xfree

end LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
