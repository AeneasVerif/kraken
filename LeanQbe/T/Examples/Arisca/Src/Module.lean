/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
public import LeanQbe.T.Examples.Arisca.Src.Header
public import LeanQbe.T.Examples.Arisca.Src.Parse
public import LeanQbe.T.Examples.Arisca.Src.Poly
public import LeanQbe.T.Examples.Arisca.Src.Driver
meta import LeanQbe.T.Examples.Arisca.Src.Header
meta import LeanQbe.T.Examples.Arisca.Src.Parse
meta import LeanQbe.T.Examples.Arisca.Src.Poly
meta import LeanQbe.T.Examples.Arisca.Src.Driver

/-!
# Flat Acyclic ARiSCA C0 Module Assembly (`Arisca/Src/Module.lean`)

Direct acyclic list concatenation (`Header.fns ++ Parse.fns ++ Poly.fns ++ Driver.fns`,
`44` live fns) with:
- `0` `PatchModule`
- `0` `externs`
- `0` `exits`
- `<= 6` SysV / AAPCS64 arguments on every function
- kernel-verified `ariscaModule_wf : ∀ f ∈ ariscaModule.fns, f.Wf` (`<= std3`).

Strictly data-pure (`0` `*Proof*`/`*Spec*`/`*Lemmas*`/`*Audit*`/`Amd64`/`Arm64`/`Kraken` imports).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Src.Module

open LeanQbe.T
open LeanQbe.T.Examples.Arisca.Src

@[expose] public section

/-- Flat topological concatenation of all `Arisca/Src` C0 modules (`44` live fns). -/
def ariscaFns : List Fn :=
  Header.fns
  ++ Parse.fns
  ++ Poly.fns
  ++ Driver.fns

/-- Closed acyclic `LeanQbe.T.Module` for the baseline ART v1 C0 checker (`0` externs). -/
def ariscaModule : LeanQbe.T.Module :=
  { fns := ariscaFns, externs := [], exits := [] }

end

#guard ariscaModule.fns.length == 44
#guard (ariscaModule.fns.map Fn.name).eraseDups.length == 44
#guard ariscaModule.checkAcyclic == true
#guard ariscaModule.exits.isEmpty
#guard ariscaModule.externs.isEmpty
#guard ariscaModule.fns.all (fun f => f.as.length <= 6)

public section

theorem ariscaModule_fns : ariscaModule.fns = ariscaFns := rfl

theorem ariscaModule_externs : ariscaModule.externs = [] := rfl

theorem ariscaModule_noExit : ariscaModule.exits = [] := rfl

theorem ariscaModule_checkAcyclic : ariscaModule.checkAcyclic = true := by
  arisca_kernel_rfl

private theorem append_wf {xs ys : List Fn}
    (hx : ∀ f ∈ xs, f.Wf) (hy : ∀ f ∈ ys, f.Wf) :
    ∀ f ∈ xs ++ ys, f.Wf := fun f hf =>
  (List.mem_append.mp hf).elim (hx f) (hy f)

/-- Every function in `ariscaFns` is PHOAS well-formed (`Func.Wf`). -/
theorem ariscaFns_wf : ∀ f ∈ ariscaFns, f.Wf := by
  have h := append_wf Header.fns_wf Parse.fns_wf
  have h := append_wf h Poly.fns_wf
  exact append_wf h Driver.fns_wf

/-- Every function in `ariscaModule` is PHOAS well-formed (`Func.Wf`). -/
theorem ariscaModule_wf : ∀ f ∈ ariscaModule.fns, f.Wf :=
  ariscaFns_wf

end

end LeanQbe.T.Examples.Arisca.Src.Module
