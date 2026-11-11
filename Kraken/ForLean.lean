module

/-
Kraken ForLean - General-Purpose Lean Helpers

Definitions that are not specific to Kraken and could equally live in Lean itself.
-/

public import Lean
public meta import Lean

open Lean

namespace Lean.Elab.Term

public meta section

/-- Parse `input` as the syntax category `cat` with `Lean.Parser.runParserCategory` and elaborate the
    resulting syntax tree with `elabStx`. -/
def elabCategory (cat : Name) (elabStx : TSyntax cat → TermElabM Expr) (input : String) : TermElabM Expr := do
  match Parser.runParserCategory (← getEnv) cat input with
  | .ok stx    => elabStx ⟨stx⟩
  | .error err => throwError err

end

end Lean.Elab.Term

namespace Int64

public meta section

variable {m : Type → Type} [Monad m] [MonadError m]

/-- Convert a signed arbitrary-precision `Int` into `Int64`, enforcing 64-bit signed/unsigned range. -/
def ofIntNoOverflow (v : Int) : m Int64 := do
  unless Int64.minValue.toInt ≤ v && v < UInt64.size do throwError "integer {v} out of 64-bit range"
  pure (Int64.ofInt v)

/-- Convert an arbitrary-precision `Nat` into `Int64`, enforcing 64-bit signed/unsigned range. -/
def ofNatNoOverflow (v : Nat) : m Int64 := do
  unless v < UInt64.size do throwError "number {v} out of 64-bit range"
  pure (Int64.ofInt v)

end

end Int64

public section

theorem List.mem_takeWhile {α : Type _} {p : α → Bool} {l : List α} {x : α}
    (hx : x ∈ l.takeWhile p) : p x = true := by
  induction l <;> grind [List.takeWhile_cons, List.takeWhile_nil]

theorem Int64.add_ofNat_inj {a : Int64} {m n : Nat} (hm : m < UInt64.size) (hn : n < UInt64.size)
    (h : a + .ofNat m = a + .ofNat n) : m = n := by
  have : (Int64.ofNat m).toBitVec = OfNat.ofNat m := Int64.toBitVec_ofNat'
  have : (Int64.ofNat n).toBitVec = OfNat.ofNat n := Int64.toBitVec_ofNat'
  grind

end
