module

public import LeanQbe.T.Logic.C0Step

/-!
# Lawful Lenses (`C0Lens`) for C0 State Records

Lawful per-field lenses (`C0Lens.comp`, `C0Lens.modify`, `C0Lens.set_list`) with
`AgreesExcept` integration (`C0Lens.agreesExcept_set`, `C0Lens.get_of_agreesExcept`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-- Lawful lens into a C0 state record `σ` focusing field `α`. -/
structure C0Lens (σ α : Type) where
  get : σ → α
  set : σ → α → σ
  get_set : ∀ s v, get (set s v) = v
  set_get : ∀ s, set s (get s) = s
  set_set : ∀ s v w, set (set s v) w = set s w

namespace C0Lens

/-- Apply a pure function to the focused field. -/
def modify {σ α : Type} (l : C0Lens σ α) (f : α → α) (s : σ) : σ :=
  l.set s (f (l.get s))

/-- Compose two lenses (`outer` into a sub-record such as `s.core`, `inner` into its field). -/
def comp {σ τ α : Type} (outer : C0Lens σ τ) (inner : C0Lens τ α) : C0Lens σ α where
  get s := inner.get (outer.get s)
  set s v := outer.set s (inner.set (outer.get s) v)
  get_set s v := by rw [outer.get_set, inner.get_set]
  set_get s := by rw [inner.set_get, outer.set_get]
  set_set s v w := by rw [outer.get_set, inner.set_set, outer.set_set]

/-- Update element `i` of a list-valued field. -/
def set_list {σ α : Type} (l : C0Lens σ (List α)) (s : σ) (i : Nat) (v : α) : σ :=
  l.set s ((l.get s).set i v)

end C0Lens

end LeanQbe.T

end

public section

namespace LeanQbe.T.C0Lens

theorem length_set_list {σ α : Type} (l : C0Lens σ (List α)) (s : σ) (i : Nat) (v : α) :
    (l.get (l.set_list s i v)).length = (l.get s).length := by
  simp only [set_list, l.get_set, List.length_set]

theorem getElem?_set_list_self {σ α : Type} (l : C0Lens σ (List α)) (s : σ) {i : Nat} (v : α)
    (hi : i < (l.get s).length) :
    (l.get (l.set_list s i v))[i]? = some v := by
  simp only [set_list, l.get_set, List.getElem?_set_self hi]

theorem getElem?_set_list_ne {σ α : Type} (l : C0Lens σ (List α)) (s : σ) {i j : Nat} (v : α)
    (hne : i ≠ j) :
    (l.get (l.set_list s i v))[j]? = (l.get s)[j]? := by
  simp only [set_list, l.get_set, List.getElem?_set_ne hne]

/-- Updating a field covered by `mask` satisfies `AgreesExcept mask`. -/
theorem agreesExcept_set {σ α : Type} (l : C0Lens σ α) (mask : σ → σ) (s : σ) (v : α)
    (hm : ∀ t x, mask (l.set t x) = mask t := by intro _ _; rfl) :
    AgreesExcept mask s (l.set s v) :=
  hm s v

/-- Project an unmasked field across `AgreesExcept mask`. -/
theorem get_of_agreesExcept {σ α : Type} (l : C0Lens σ α) {mask : σ → σ} {s s' : σ}
    (h : AgreesExcept mask s s')
    (hm : ∀ t, l.get (mask t) = l.get t := by intro _; rfl) :
    l.get s' = l.get s :=
  h.get l.get hm

end LeanQbe.T.C0Lens

end
