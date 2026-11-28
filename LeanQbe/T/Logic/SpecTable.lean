/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module

/-!
# Pure Specification Table Leaf (`SpecTable`)

Minimal pure leaf defining `SpecEntry` rows, `SpecEntry.{ofFn,eff,cast,sig}`, and `Env.ofTable`
with zero `meta import`s, zero tactics, and zero separation-logic tactic dependencies so pure
specification modules (`Kissat/Spec/*`) can depend on `SpecEntry` without pulling `C0Step`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-- One row of a specification table: contract `spec` for symbol `name : as → rs`.
With `noExit := true` the row ignores the caller's exit continuation (`X`), as required by
`Compiled.fnSpec_noExit_id`. -/
structure SpecEntry where
  name : Sym
  as : List Ty
  rs : List Ty
  spec : Spec as rs
  noExit : Bool := false

/-- Table row for the module function `fn`. -/
abbrev SpecEntry.ofFn (fn : Fn) (spec : Spec fn.as fn.rs) (noExit : Bool := false) : SpecEntry :=
  ⟨fn.name, fn.as, fn.rs, spec, noExit⟩

/-- Effective contract of a row: `spec`, with `X := ⊥` when `noExit`. -/
def SpecEntry.eff (e : SpecEntry) : Spec e.as e.rs :=
  fun xs m Q X => e.spec xs m Q (if e.noExit then fun _ _ _ _ => False else X)

/-- `e.eff` transported along signature equalities. -/
def SpecEntry.cast (e : SpecEntry) {as bs : List Ty} (ha : e.as = as) (hr : e.rs = bs) :
    Spec as bs :=
  ha ▸ hr ▸ e.eff

/-- Signature triple `(name, as, rs)` of a specification row, matching `Fn.sig`. -/
def SpecEntry.sig (e : SpecEntry) : SigEntry :=
  (e.name, e.as, e.rs)

/-- First-match environment of a specification table (`False` off the table). -/
def Env.ofTable : List SpecEntry → Env
  | [] => fun _ _ _ _ _ _ _ => False
  | e :: es => fun f as bs xs m Q X =>
    (∃ h : e.name = f ∧ e.as = as ∧ e.rs = bs, e.cast h.2.1 h.2.2 xs m Q X) ∨
      (¬ (e.name = f ∧ e.as = as ∧ e.rs = bs) ∧ Env.ofTable es f as bs xs m Q X)

end LeanQbe.T
