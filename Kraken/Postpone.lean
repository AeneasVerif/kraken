module

/-
Kraken Postpone - Values with a Deferred Type Index

`Postponable` represents a value of an indexed type family whose index is either already fixed or
still to be determined by other values. The assembly elaborators use it to infer operation widths from
operands: a register operand fixes the width of an operation, whereas an immediate or memory operand is
valid at any width.
-/

public import Lean
public meta import Lean

open Lean

namespace Kraken

public meta section

/-- A value of a type family `T` indexed by `U` whose index is either already fixed (`instantiated`),
    or still to be determined by other operands (`postponed`). -/
inductive Postponable {U : Type} (T : U → Type) where
  | instantiated (u : U) (t : T u)
  | postponed (p : {u : U} → T u)

namespace Postponable

variable {U : Type} {T T₁ T₂ : U → Type}
variable {m : Type _ → Type _} [Monad m] [MonadError m]

/-- Instantiate a postponed value at `u`; an already instantiated value keeps its own index. -/
def getD (v : Postponable T) (u : U) : Σ u : U, T u :=
  match v with
  | .instantiated u v => ⟨u, v⟩
  | .postponed f  => ⟨u, f⟩

/-- The index and value of an instantiated value, failing with `msg` if it is still postponed. -/
def getM (v : Postponable T) (msg : MessageData := m!"Could not infer postponed choice") : m (Σ u : U, T u) :=
  match v with
  | .postponed _  => throwError msg
  | .instantiated u x => pure ⟨u, x⟩

variable [ToMessageData U] [DecidableEq U]

/-- Instantiate at `u`, failing if the value is already instantiated at a different index. -/
def instantiateE (v : Postponable T) (u : U) : Except MessageData (T u) :=
  match v with
  | .postponed f   => .ok f
  | .instantiated u' x =>
    if h : u = u' then .ok (h ▸ x)
    else .error m!"type error: {u} != {u'}"

def instantiateM (v : Postponable T) (u : U) : m (T u) :=
  match v.instantiateE u with
  | .ok res  => pure res
  | .error m => throwError m

/-- Combine two values so that they share a single index, instantiating the postponed one. -/
def syncE : Postponable T₁ → Postponable T₂ → Except MessageData (Postponable (λ {u : U} ↦ T₁ u × T₂ u))
  | .instantiated u₁ v₁, mt₂ => do
    return instantiated u₁ (v₁, ← mt₂.instantiateE u₁)
  | .postponed t, instantiated u v =>
    .ok <| instantiated u (t, v)
  | .postponed t₁, .postponed t₂ =>
    .ok <| .postponed (λ {u} ↦ (@t₁ u, @t₂ u))

/-- `syncE`, reporting index mismatches at `ref` so that calls can be chained. -/
def syncM (mt₁ : Postponable T₁) (mt₂ : Postponable T₂) (ref : Syntax) : m (Postponable (λ {u : U} ↦ T₁ u × T₂ u)) := do
  match mt₁.syncE mt₂ with
  | .ok res => pure res
  | .error m => throwErrorAt ref m

end Postponable

variable {m : Type _ → Type _} [Monad m] [MonadError m] in
/-- Instantiate `mt` at `opt`'s index when it is given, reporting mismatches at `ref`. -/
def _root_.Option.syncM {U : Type} [DecidableEq U] [ToMessageData U] {T : U → Type}
    (opt : Option U) (mt : Postponable T) (ref : Syntax) : m (Postponable T) := do
  match opt with
  | none => pure mt
  | some w => return .instantiated w (← withRef ref <| mt.instantiateM w)

end

end Kraken
