/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Src.Heap
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specification Table for `Kissat.Src.Heap` (`Proof.Heap.Spec`)

Reuses `Proof.Spec.fullHeapUpSpec`, `fullHeapDownSpec`, `fullHeapPushSpec`, and
`fullHeapPopSpec` directly (`0` spec duplication, `0` legacy imports, `0` `@[expose]` on
theorems/lemmas).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Heap.Spec

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src

theorem fullHeapUpSpec_xfree : Spec.XFree fullHeapUpSpec := by xfree

theorem fullHeapDownSpec_xfree : Spec.XFree fullHeapDownSpec := by xfree

theorem fullHeapPushSpec_xfree : Spec.XFree fullHeapPushSpec := by xfree

theorem fullHeapPopSpec_xfree : Spec.XFree fullHeapPopSpec := by xfree

/-- Canonical `SpecEntry` table matching `Src.Heap.fns` 1-to-1. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_heap_up", [i64, i32], [], fullHeapUpSpec, true⟩
  , ⟨"full_heap_down", [i64, i32], [], fullHeapDownSpec, true⟩
  , ⟨"full_heap_push", [i64, i32], [], fullHeapPushSpec, true⟩
  , ⟨"full_heap_pop", [i64], [i64], fullHeapPopSpec, true⟩ ]

theorem specs_sigs : specs.map SpecEntry.sig = Heap.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

theorem has_full_heap_up {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_heap_up" fullHeapUpSpec :=
  Env.Sat.has h List.mem_cons_self fullHeapUpSpec_xfree

theorem has_full_heap_down {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_heap_down" fullHeapDownSpec :=
  Env.Sat.has h (.tail _ List.mem_cons_self) fullHeapDownSpec_xfree

theorem has_full_heap_push {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_heap_push" fullHeapPushSpec :=
  Env.Sat.has h (.tail _ (.tail _ List.mem_cons_self)) fullHeapPushSpec_xfree

theorem has_full_heap_pop {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_heap_pop" fullHeapPopSpec :=
  Env.Sat.has h (.tail _ (.tail _ (.tail _ List.mem_cons_self))) fullHeapPopSpec_xfree

end LeanQbe.T.Examples.Kissat.Proof.Heap.Spec
