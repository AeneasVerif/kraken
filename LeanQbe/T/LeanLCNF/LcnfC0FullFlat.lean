/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Flat
public import LeanQbe.T.LeanLCNF.LcnfC0Full
public import LeanQbe.T.Module
meta import Lean
meta import LeanQbe.T.LeanLCNF.LcnfC0Full
meta import LeanQbe.T.MainCertInline

/-!
# Materialized `TFlatFn` Data Leaf for `rtC0CoreMod` (`LcnfC0FullFlat`)

Proof-free data leaf materializing all `80` pure-C0 runtime functions of `rtC0CoreMod` into
exposed, noncomputable (`compile := false`) `TFlatFn` definitions (`rtC0CoreFlatFns` and
`rtC0CoreFlatMod`) with kernel-checked `rfl` bridges (`rtC0CoreFlatMod_fns_flat_eq`,
`rtC0CoreFlatMod_fns_eq`, `rtC0CoreFlatMod_eq`) matching `rtC0CoreMod`.
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T

public section

open Lean Elab Command Meta InlineMeta in
run_cmd do
  let ns ← getCurrNamespace
  let modNm := ns ++ `rtC0CoreFlatMod
  let fnsNm := ns ++ `rtC0CoreFlatFns
  let pfx := ns ++ `rtC0CoreFlat
  let srcModE := Lean.mkConst ``rtC0CoreMod
  let tfs : List TFlatFn :=
    rtC0CoreMod.fns.map fun fn => ⟨fn.name, fn.as, fn.rs, reifyFunc fn.body⟩
  let flatTy := Lean.mkConst ``LeanQbe.T.TFlatFn
  let fnTy := Lean.mkConst ``LeanQbe.T.Fn
  let listFlatTy := mkApp (Lean.mkConst ``List [.zero]) flatTy
  let listFnTy := mkApp (Lean.mkConst ``List [.one]) fnTy
  let modTy := Lean.mkConst ``LeanQbe.T.Module
  liftCoreM do
    let (flatConsts, fnConsts) ← emitMatFnDefs pfx tfs false
    addCertDef fnsNm listFlatTy (mkListLit .zero flatTy flatConsts) false
    let modVal := mkApp3 (Lean.mkConst ``LeanQbe.T.Module.mk)
      (mkListLit .one fnTy fnConsts)
      (mkApp (Lean.mkConst ``List.nil [.zero]) (Lean.mkConst ``LeanQbe.T.Extern))
      (Lean.mkConst ``rtExitSyms)
    addCertDef modNm modTy modVal false
    let flatModFnsE := mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) (Lean.mkConst modNm)
    let mapFlatE := mkApp4 (Lean.mkConst ``List.map [.zero, .one])
      flatTy fnTy (Lean.mkConst ``LeanQbe.T.TFlatFn.toFn) (Lean.mkConst fnsNm)
    addKernelEqThm (ns ++ `rtC0CoreFlatMod_fns_flat_eq) listFnTy flatModFnsE mapFlatE .one
    let srcModFnsE := mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) srcModE
    addKernelEqThm (ns ++ `rtC0CoreFlatMod_fns_eq) listFnTy flatModFnsE srcModFnsE .one

/-- Whole-module equality between materialized `rtC0CoreFlatMod` and `rtC0CoreMod`. -/
theorem rtC0CoreFlatMod_eq : rtC0CoreFlatMod = rtC0CoreMod :=
  congrArg (fun fs => ({ fns := fs, externs := [], exits := ["lcnf_panic"] } : Module))
    rtC0CoreFlatMod_fns_eq

end

end LeanQbe.T.LeanLCNF
