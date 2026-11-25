module

public import LeanQbe.T.Unified.Core
public import LeanQbe.T.Unified.Ssa

/-!
# Capability Routing and Frontend Adapter Interface (`Unified.Caps`)

Defines per-function capability summaries (`Caps`), pipeline route selection (`Route`, `route`),
and the `Frontend` interface landing source programs into `Unified.Ssa.ssa`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Unified

open LeanQbe.T

universe u v

/-- Capabilities required by a frontend program from the unified pipeline. -/
structure Caps : Type where
  /-- Design B `symAddr`/`call .ptr`/`tailCall` (LCNF closures, Bedrock2 fn-ptrs). -/
  indirect : Bool := false
  /-- Open word-level control (`ijmp`, computed code addresses, own frames): L0/L1 only. -/
  wordCtl : Bool := false
  deriving DecidableEq, Repr

/-- Capability lattice join. -/
@[expose] def Caps.or (c₁ c₂ : Caps) : Caps :=
  ⟨c₁.indirect || c₂.indirect, c₁.wordCtl || c₂.wordCtl⟩

/-- Compilation route selected from per-function `Caps`. -/
inductive Route : Type
  /-- Legacy direct-call SSA path (Kissat C0, Bootstrap0): byte-identical to today. -/
  | direct
  /-- SSA + Design B indirect/tail extensions. -/
  | designB
  /-- Word-control tier L0 `BedrockWord` → L1 `BedrockMach`. -/
  | word
  deriving DecidableEq, Repr

/-- Select the pipeline route from a function's capabilities. -/
@[expose] def route (c : Caps) : Route :=
  if c.wordCtl then .word else if c.indirect then .designB else .direct

/-- A frontend: source tier, capability classifier, and checked lowering stage into `ssa`. -/
structure Frontend : Type (max (u + 1) (v + 1)) where
  src : Tier.{u, v}
  caps : src.Prog → Caps
  lower : Stage src ssa

/-- Capability summary for a direct `LeanQbe.T.Fn` (always empty `{}` on direct SSA). -/
@[expose] def fnCaps (_fn : Fn) : Caps := {}

end LeanQbe.T.Unified
