module

public import LeanQbe.T.Unified.Driver

/-!
# Soundness and Regression Firewall Theorems (`Unified.DriverLemmas`)

Proof module companion to `LeanQbe.T.Unified.Driver`:

* `midEnd_run`, `route_direct`.
* `Factoring.transport`, `Factoring.same_bytes`.
* `unified_sound`, `unified_eq_legacy` (`rfl`), `unified_direct`, and
  `unified_refBackend_sound` (generic end-to-end correctness through `midEnd`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Unified

open LeanQbe.T

universe u v w

theorem midEnd_run (t : LegalTarget) (fn : Fn)
    (hs : (fn.earlyOpt).body.supportsSource t = true) :
    (midEnd t).run fn = .ok (fn.mid t) := by
  simp [midEnd, hs]

theorem route_direct : route {} = .direct := rfl

/-- Transport any production certificate along a `Factoring` equivalence. -/
theorem Factoring.transport {Src D I : Type} (F : Factoring Src D I)
    (Cert : Src → List D → Prop) (hc : ∀ f ds, F.direct f = .ok ds → Cert f ds) :
    ∀ f is, F.vll f = .ok is → Cert f (is.flatMap F.asm) := by
  intro f is h
  apply hc
  rw [← F.factor f, h]
  rfl

/-- Byte-identical output between `F.direct` and `F.vll` followed by `F.asm`. -/
theorem Factoring.same_bytes {Src D I : Type} (F : Factoring Src D I) (f : Src)
    (is : List I) (h : F.vll f = .ok is) : F.direct f = .ok (is.flatMap F.asm) := by
  rw [← F.factor f, h]
  rfl

/-- Generic end-to-end soundness for any frontend × legal target × routed backend. -/
theorem unified_sound (fe : Frontend.{u, v}) (t : LegalTarget) (Bs : Backends.{w})
    (p : fe.src.Prog) (s : fe.src.Spec) (ds : List (pick Bs (route (fe.caps p))).D)
    (hp : fe.src.Ok p)
    (hrun : (unified fe t (pick Bs (route (fe.caps p)))).run p = .ok ds)
    (hs : fe.src.Sat p s) :
    (pick Bs (route (fe.caps p))).MSat ds
      ((unified fe t (pick Bs (route (fe.caps p)))).tr p s) :=
  (unified fe t _).sound p ds s hp hrun hs

/-- Regression firewall (1/2): `(unified fe t B).run` is definitionally
`frontend ; legacyMid ; B.lower`. -/
theorem unified_eq_legacy (fe : Frontend.{u, v}) (t : LegalTarget) (B : Backend.{w}) :
    (unified fe t B).run =
      fun p => bindE (fe.lower.run p) fun q => bindE (legacyMid t q) B.lower :=
  rfl

/-- Regression firewall (2/2): direct-capability programs always select `Bs.direct`. -/
theorem unified_direct (fe : Frontend.{u, v}) (Bs : Backends.{w}) (p : fe.src.Prog)
    (h : route (fe.caps p) = .direct) : pick Bs (route (fe.caps p)) = Bs.direct := by
  rw [h]
  rfl

/-- Generic end-to-end correctness into `refBackend` through the production `midEnd`. -/
theorem unified_refBackend_sound (fe : Frontend.{u, v}) (t : LegalTarget) (p : fe.src.Prog)
    (s : fe.src.Spec) (ds : List Fn) (hp : fe.src.Ok p)
    (hrun : (unified fe t refBackend).run p = .ok ds) (hs : fe.src.Sat p s) :
    ∃ fn, ds = [fn] ∧ ssa.Sat fn ((unified fe t refBackend).tr p s) :=
  (unified fe t refBackend).sound p ds s hp hrun hs

end LeanQbe.T.Unified
