module

public import LeanQbe.T.Unified.Core
public import LeanQbe.T.Unified.Ssa
public import LeanQbe.T.Unified.Caps

/-!
# Unified Multi-Frontend Driver (`Unified.Driver`)

Definitions-only driver assembling frontends, the shared `midEnd`, and backend slots
(`Backend`, `Backends`, `Factoring`, `unified`, `legacyMid`, `pick`, `refBackend`). All theorems
live in `LeanQbe.T.Unified.DriverLemmas` so downstream consumers remain firewall-clean.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Unified

open LeanQbe.T

universe u v w

/-- Backend lowering slot from `ssa` to target directive lists `List D` satisfying `MSat`. -/
structure Backend : Type (max (u + 1) 2) where
  D : Type u
  MSat : List D → SSpec → Prop
  lower : Fn → Except String (List D)
  correct : ∀ fn ds s, fn.Wf → lower fn = .ok ds → ssa.Sat fn s → MSat ds s

/-- Target machine-code tier induced by a `Backend`. -/
@[expose] def Backend.tier (B : Backend.{u}) : Tier.{u, 1} where
  Prog := List B.D
  Ok _ := True
  Spec := SSpec
  top := ssa.top
  Sat := B.MSat

/-- Backend lowering viewed as a `Stage ssa B.tier`. -/
@[expose] def Backend.stage (B : Backend.{u}) : Stage ssa B.tier where
  run := B.lower
  tr _ s := s
  ok _ _ _ _ := trivial
  sound fn ds s hf h hs := B.correct fn ds s hf h hs

/-- Factoring firewall: a VLLIR route `vll` whose assembly `asm` equals `direct` inherits every
production certificate and produces byte-identical output. -/
structure Factoring (Src D I : Type) : Type where
  direct : Src → Except String (List D)
  vll : Src → Except String (List I)
  asm : I → List D
  factor : ∀ f, (vll f).map (·.flatMap asm) = direct f

/-- Per-route backend table. -/
structure Backends : Type (max (u + 1) 2) where
  direct : Backend.{u}
  designB : Backend.{u}
  word : Backend.{u}

/-- Unified front-to-back stage for any frontend: `fe.lower ≫ midEnd t ≫ B.stage`. -/
@[expose] def unified (fe : Frontend.{u, v}) (t : LegalTarget) (B : Backend.{w}) :
    Stage fe.src B.tier :=
  fe.lower ≫ midEnd t ≫ B.stage

/-- Legacy per-function `compileFn` front half: `supportsSource` guard followed by `Fn.mid`. -/
@[expose] def legacyMid (t : LegalTarget) (fn : Fn) : Except String Fn :=
  if (fn.earlyOpt).body.supportsSource t then .ok (fn.mid t) else .error "mid: unsupported"

/-- Select a backend from `Bs` according to `Route`. -/
@[expose] def pick (Bs : Backends.{w}) : Route → Backend.{w}
  | .direct => Bs.direct
  | .designB => Bs.designB
  | .word => Bs.word

/-- Non-vacuous reference backend emitting the legalized `Fn` itself. -/
@[expose] def refBackend : Backend.{1} where
  D := Fn
  MSat ds s := ∃ fn, ds = [fn] ∧ ssa.Sat fn s
  lower fn := .ok [fn]
  correct fn ds s _ h hs := by cases h; exact ⟨fn, rfl, hs⟩

end LeanQbe.T.Unified
