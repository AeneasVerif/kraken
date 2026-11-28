/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Main
public import LeanQbe.T.Flat
public import LeanQbe.T.Examples.Arisca.Src.Module
meta import Lean
meta import LeanQbe.T.MainCertInline
meta import LeanQbe.T.Examples.Arisca.Src.Module

/-!
# Materialized `TFlatFn` Data Leaf for `ariscaModule` (`Arisca.Build.Flat`)

Proof-free, arch-free data leaf materializing all `44` C0 functions of
`LeanQbe.T.Examples.Arisca.Src.Module.ariscaModule` into exposed, noncomputable
(`compile := false`) `TFlatFn` definitions (`ariscaFlatFns` and `ariscaFlatMod`) with
kernel-checked `rfl` bridges (`ariscaFlatMod_fns_flat_eq`, `ariscaFlatMod_fns_eq`,
`ariscaFlatMod_eq`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Build

open LeanQbe.T
open LeanQbe.T.Examples.Arisca.Src.Module

public section

meta section

open Lean Elab Command

run_cmd do
  let ns ← getCurrNamespace
  let pfx := ns ++ `ariscaFlatMod
  let srcModE := Lean.mkConst ``ariscaModule
  let tfs : List TFlatFn :=
    ariscaModule.fns.map fun fn => ⟨fn.name, fn.as, fn.rs, reifyFunc fn.body⟩
  let flatTy := Lean.mkConst ``LeanQbe.T.TFlatFn
  let fnTy := Lean.mkConst ``LeanQbe.T.Fn
  let listFlatTy := mkApp (Lean.mkConst ``List [.zero]) flatTy
  let listFnTy := mkApp (Lean.mkConst ``List [.one]) fnTy
  let modTy := Lean.mkConst ``LeanQbe.T.Module
  liftCoreM do
    let (flatConsts, fnConsts) ← InlineMeta.emitMatFnDefs pfx tfs false
    let fnsNm := ns ++ `ariscaFlatFns
    addCertDef fnsNm listFlatTy (InlineMeta.mkListLit .zero flatTy flatConsts) false
    let modNm := ns ++ `ariscaFlatMod
    let modVal := mkApp3 (Lean.mkConst ``LeanQbe.T.Module.mk)
      (InlineMeta.mkListLit .one fnTy fnConsts)
      (mkApp (Lean.mkConst ``List.nil [.zero]) (Lean.mkConst ``LeanQbe.T.Extern))
      (mkApp (Lean.mkConst ``List.nil [.zero]) (Lean.mkConst ``LeanQbe.T.Sym))
    addCertDef modNm modTy modVal false
    let flatModFnsE := mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) (Lean.mkConst modNm)
    let mapFlatE := mkApp4 (Lean.mkConst ``List.map [.zero, .one])
      flatTy fnTy (Lean.mkConst ``LeanQbe.T.TFlatFn.toFn) (Lean.mkConst fnsNm)
    addKernelEqThm (ns ++ `ariscaFlatMod_fns_flat_eq) listFnTy flatModFnsE mapFlatE .one
    let srcModFnsE := mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) srcModE
    addKernelEqThm (ns ++ `ariscaFlatMod_fns_eq) listFnTy flatModFnsE srcModFnsE .one

end

/-- Whole-module equality between materialized `ariscaFlatMod` and `ariscaModule`. -/
theorem ariscaFlatMod_eq : ariscaFlatMod = ariscaModule :=
  congrArg (fun fs => ({ fns := fs, externs := [], exits := [] } : Module))
    ariscaFlatMod_fns_eq

end

end LeanQbe.T.Examples.Arisca.Build
