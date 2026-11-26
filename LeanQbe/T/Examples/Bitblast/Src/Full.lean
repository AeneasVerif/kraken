/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
public import LeanQbe.T.Examples.Bitblast.Src.Validate
public import LeanQbe.T.Examples.Bitblast.Src.Aig
public import LeanQbe.T.Examples.Bitblast.Src.Tseitin
public import LeanQbe.T.Examples.Bitblast.Src.Driver
import LeanQbe.T.Examples.Bitblast.Src.Header
meta import LeanQbe.T.Examples.Bitblast.Src.Header
meta import LeanQbe.T.Examples.Bitblast.Src.Validate
meta import LeanQbe.T.Examples.Bitblast.Src.Aig
meta import LeanQbe.T.Examples.Bitblast.Src.Tseitin
meta import LeanQbe.T.Examples.Bitblast.Src.Driver

/-!
# Flat Acyclic Bitblast C0 Module Assembly (`Bitblast/Src/Full.lean`)

Direct acyclic list concatenation (`Validate.fns ++ Aig.fns ++ Tseitin.fns ++ Driver.fns`) with:
- `0` `PatchModule`
- `0` `exits`
- exact single extern `kissat_solve_bytes : [i64, i64, i64, i64, i64] -> [i64]`
- `<= 6` SysV arguments on every function
- kernel-verified `bitblastModule_wf : ∀ f ∈ bitblastModule.fns, f.Wf` (`<= std3`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Src.Full

open LeanQbe.T
open LeanQbe.T.Examples.Bitblast.Src

@[expose] public section

/-- Flat topological concatenation of all `Bitblast/Src` C0 modules (`30` live fns). -/
def bitblastFns : List Fn :=
  Validate.fns
  ++ Aig.fns
  ++ Tseitin.fns
  ++ Driver.fns

/-- Single external callee (`kissat_solve_bytes`) resolved via `LinkedCert.append`. -/
def bitblastExterns : List Extern :=
  [⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64]⟩]

/-- Closed acyclic `LeanQbe.T.Module` for the C0 bitblaster core. -/
def bitblastModule : LeanQbe.T.Module :=
  { fns := bitblastFns, externs := bitblastExterns, exits := [] }

end

#guard bitblastModule.fns.length == 30
#guard (bitblastModule.fns.map Fn.name).eraseDups.length == 30
#guard bitblastModule.checkAcyclic == true
#guard bitblastModule.exits.isEmpty
#guard bitblastModule.externs == [⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64]⟩]
#guard bitblastModule.fns.all (fun f => f.as.length <= 6)

public section

theorem bitblastModule_fns : bitblastModule.fns = bitblastFns := rfl

theorem bitblastModule_externs : bitblastModule.externs = bitblastExterns := rfl

theorem bitblastModule_noExit : bitblastModule.exits = [] := rfl

theorem bitblastModule_checkAcyclic : bitblastModule.checkAcyclic = true := by
  bitblast_kernel_rfl

private theorem append_wf {xs ys : List Fn}
    (hx : ∀ f ∈ xs, f.Wf) (hy : ∀ f ∈ ys, f.Wf) :
    ∀ f ∈ xs ++ ys, f.Wf := fun f hf =>
  (List.mem_append.mp hf).elim (hx f) (hy f)

/-- Every function in `bitblastModule` is PHOAS well-formed (`Func.Wf`). -/
theorem bitblastModule_wf : ∀ f ∈ bitblastModule.fns, f.Wf := by
  have h := append_wf Validate.fns_wf Aig.fns_wf
  have h := append_wf h Tseitin.fns_wf
  exact append_wf h Driver.fns_wf

end

end LeanQbe.T.Examples.Bitblast.Src.Full
