module

public import LeanQbe.T.FlatLemmas
public import LeanQbeTest.T.Examples
public import LeanQbeTest.T.Smoke

/-!
# Reification and well-formedness tests

* Kernel `rfl` (`t_wf_reify`) proofs of `Func.Wf` for all 8 example programs in `Examples.lean`
  (including concrete `Ty.vec k` instances of `vumin`, plus parametric `∀ k, Func.Wf (vumin k)`)
  and all 6 closed functions in `Smoke.lean`.
* Total computable `Func.checkTFlat ... = true` checks.
* Out-of-scope / type-mismatched `TFlat` negative tests (`wfCheck = false`, `denote` yields `.hlt`
  while preserving `denote_wf`).
* Smoke test of `induction hwf using Wf.induct` and `Wf.weaken`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.ReifyTest

/-! ## 1. All 8 example programs from `Examples.lean` -/

theorem add128_wf : Func.Wf Examples.add128 := by t_wf_reify
theorem add256_wf : Func.Wf Examples.add256 := by t_wf_reify
theorem mac_wf : Func.Wf Examples.mac := by t_wf_reify
theorem ult128_wf : Func.Wf Examples.ult128 := by t_wf_reify
theorem umin_wf : Func.Wf Examples.umin := by t_wf_reify
theorem mulByAdd_wf : Func.Wf Examples.mulByAdd := by t_wf_reify
theorem qrStep_wf : Func.Wf Examples.qrStep := by t_wf_reify
theorem vumin_0_wf : Func.Wf (Examples.vumin 0) := by t_wf_reify
theorem vumin_2_wf : Func.Wf (Examples.vumin 2) := by t_wf_reify
theorem vumin_3_wf : Func.Wf (Examples.vumin 3) := by t_wf_reify

/-- Parametric `Func.Wf` for `vumin k` across all symbolic `k : Nat`, proved by `t_wf_tac`. -/
theorem vumin_wf (k : Nat) : Func.Wf (Examples.vumin k) := by
  t_wf_tac

/-- Syntax-directed `t_wf_tac` smoke checks covering `let_`, `group`, `load`/`store`, and `call`/`exit`. -/
theorem umin_wf_tac : Func.Wf Examples.umin := by t_wf_tac
theorem evenOdd_wf_tac : Func.Wf Smoke.evenOdd := by t_wf_tac
theorem tracer_wf_tac : Func.Wf Smoke.tracer := by t_wf_tac
theorem caller_wf_tac : Func.Wf Smoke.caller := by t_wf_tac

/-! ## 2. All 6 closed functions from `Smoke.lean` -/

theorem evenOdd_wf : Func.Wf Smoke.evenOdd := by t_wf_reify
theorem sumLanes_wf : Func.Wf Smoke.sumLanes := by t_wf_reify
theorem tracer_wf : Func.Wf Smoke.tracer := by t_wf_reify
theorem storeThenLoadOther_wf : Func.Wf Smoke.storeThenLoadOther := by t_wf_reify
theorem caller_wf : Func.Wf Smoke.caller := by t_wf_reify
theorem spin_wf : Func.Wf Smoke.spin := by t_wf_reify

/-! ## 3. Direct `Func.wf_of_reify rfl`, `Func.checkTFlat = true`, and `NoHlt` soundness -/

theorem umin_wf_rfl : Func.Wf Examples.umin :=
  Func.wf_of_reify rfl

theorem evenOdd_wf_rfl : Func.Wf Smoke.evenOdd :=
  Func.wf_of_reify rfl

theorem add128_check : Func.checkTFlat Examples.add128 = true := by decide
theorem add256_check : Func.checkTFlat Examples.add256 = true := by decide
theorem mac_check : Func.checkTFlat Examples.mac = true := by decide
theorem ult128_check : Func.checkTFlat Examples.ult128 = true := by decide
theorem umin_check : Func.checkTFlat Examples.umin = true := by decide
theorem mulByAdd_check : Func.checkTFlat Examples.mulByAdd = true := by decide
theorem qrStep_check : Func.checkTFlat Examples.qrStep = true := by decide
theorem vumin_2_check : Func.checkTFlat (Examples.vumin 2) = true := by decide
theorem evenOdd_check : Func.checkTFlat Smoke.evenOdd = true := by decide
theorem sumLanes_check : Func.checkTFlat Smoke.sumLanes = true := by decide
theorem tracer_check : Func.checkTFlat Smoke.tracer = true := by decide
theorem storeThenLoadOther_check : Func.checkTFlat Smoke.storeThenLoadOther = true := by decide
theorem caller_check : Func.checkTFlat Smoke.caller = true := by decide
theorem spin_check : Func.checkTFlat Smoke.spin = true := by decide

theorem add128_noHlt (V : Ty → Type) (L : List Ty → Type)
    (xs : Tup V [Examples.u128, Examples.u128]) :
    Expr.NoHlt (denote V L
      (toTFlat (Examples.add128 K KL (Tup.levels [Examples.u128, Examples.u128] 0))
      [Examples.u128, Examples.u128].length 0) (pushTup xs []) []) :=
  Func.denote_noHlt_of_check Examples.add128 (by decide) (by decide) V L xs

theorem evenOdd_noHlt (V : Ty → Type) (L : List Ty → Type) (xs : Tup V [i64]) :
    Expr.NoHlt (denote V L (toTFlat (Smoke.evenOdd K KL (Tup.levels [i64] 0))
      [i64].length 0) (pushTup xs []) []) :=
  Func.denote_noHlt_of_check Smoke.evenOdd (by decide) (by decide) V L xs

/-! ## 4. Negative tests: out-of-scope / type-mismatched `TFlat` -/

/-- Out-of-scope variable level `99` in raw `Expr K KL` reifies to out-of-bounds index `1`,
fails `wfCheck`, and denotes `.hlt` (still `Wf` by `denote_wf`). -/
def oobRawExpr : Expr K KL [i64] := .ret (.var 99, ())

theorem oob_wfCheck_false : (toTFlat oobRawExpr 1 0).wfCheck [i64] [] = false := by
  decide

theorem oob_denote_eq_hlt (V : Ty → Type) (L : List Ty → Type) (v : V i64) :
    denote V L (toTFlat oobRawExpr 1 0) [⟨i64, v⟩] [] = .hlt := by
  rfl

/-- Type-mismatched de Bruijn index (`i32` expected where `i64` is bound) fails `wfCheck`
and denotes `.hlt`, yet `denote_wf` still holds across any two instantiations. -/
def illTypedTFlat : TFlat [i32] := .ret (.var 0, ())

theorem illTyped_wfCheck_false : illTypedTFlat.wfCheck [i64] [] = false := by
  decide

theorem illTyped_not_noHlt (V : Ty → Type) (L : List Ty → Type) (v : V i64) :
    ¬ Expr.NoHlt (denote V L illTypedTFlat [⟨i64, v⟩] []) := by
  intro h
  cases h

theorem illTyped_denote_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    (v₁ : V₁ i64) (v₂ : V₂ i64) :
    Wf [⟨i64, v₁, v₂⟩] ([] : Ctx L₁ L₂)
      (denote V₁ L₁ illTypedTFlat [⟨i64, v₁⟩] [])
      (denote V₂ L₂ illTypedTFlat [⟨i64, v₂⟩] []) :=
  denote_wf illTypedTFlat (.cons List.mem_cons_self .nil) .nil

/-! ## 5. Dependent `Wf.induct` and `Wf.weaken` test -/

/-- Weakening an empty-context `Wf` derivation to arbitrary contexts `G`, `D`. -/
theorem wf_weaken_empty {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {e₁ : Expr V₁ L₁ rs} {e₂ : Expr V₂ L₂ rs}
    (h : Wf ([] : Ctx V₁ V₂) ([] : Ctx L₁ L₂) e₁ e₂)
    (G : Ctx V₁ V₂) (D : Ctx L₁ L₂) : Wf G D e₁ e₂ :=
  h.weaken (fun _ hp => nomatch hp) (fun _ hp => nomatch hp)

/-- Direct `induction hwf using Wf.induct` smoke check over `group` and `let_`. -/
theorem wf_self_symm_smoke {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    {G : Ctx V V} {D : Ctx L L} {e₁ e₂ : Expr V L rs} (hwf : Wf G D e₁ e₂) :
    Wf G.flip D.flip e₂ e₁ := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    exact .let_ hop.symm fun xs₂ xs₁ => by
      simpa [Ctx.flip_append, Tup.zip_flip] using ih xs₁ xs₂
  | load t ha _ ih => exact .load t ha.symm fun v₂ v₁ => ih v₁ v₂
  | store hv ha _ ih => exact .store hv.symm ha.symm ih
  | call f hargs _ ih =>
    exact .call f (TRel.argRel_symm hargs) fun xs₂ xs₁ => by
      simpa [Ctx.flip_append, Tup.zip_flip] using ih xs₁ xs₂
  | jnz hc _ _ iht ihe => exact .jnz hc.symm iht ihe
  | jump hj hargs => exact .jump (mem_ctx_flip hj) (TRel.argRel_symm hargs)
  | ret hvs => exact .ret (TRel.argRel_symm hvs)
  | exit f hargs => exact .exit f (TRel.argRel_symm hargs)
  | hlt => exact .hlt
  | group _ _ ihb ihk =>
    exact .group
      (fun Js₂ Js₁ => WfB.of_get fun i xs₂ xs₁ => by
        simpa [Ctx.flip_append, Tup.zip_flip] using ihb Js₁ Js₂ i xs₁ xs₂)
      (fun Js₂ Js₁ => by
        simpa [Ctx.flip_append, Tup.zip_flip] using ihk Js₁ Js₂)

end LeanQbe.T.ReifyTest
