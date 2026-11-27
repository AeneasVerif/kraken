/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Main
public import LeanQbe.T.Flat
public import LeanQbe.T.Examples.Bitblast.Src.Full
meta import Lean
meta import LeanQbe.T.MainCertInline
meta import LeanQbe.T.Examples.Bitblast.Src.Full

/-!
# Materialized `TFlatFn` Data Leaf for `bitblastModule` (`Flat`)

Materializes all `64` C0 functions of `LeanQbe.T.Examples.Bitblast.Src.Full.bitblastModule` into
exposed, noncomputable (`compile := false`) `TFlatFn` definitions (`bitblastFlatFns` and
`bitblastFlatMod`) with kernel-checked `rfl` bridges (`bitblastFlatMod_fns_flat_eq`,
`bitblastFlatMod_fns_eq`, `bitblastFlatMod_eq`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Build

open LeanQbe.T
open LeanQbe.T.Examples.Bitblast.Src.Full

public section

meta section

open Lean Elab Command

run_cmd do
  let ns ← getCurrNamespace
  let pfx := ns ++ `bitblastFlatMod
  let srcModE := Lean.mkConst ``bitblastModule
  let tfs : List TFlatFn :=
    bitblastModule.fns.map fun fn => ⟨fn.name, fn.as, fn.rs, reifyFunc fn.body⟩
  let flatTy := Lean.mkConst ``LeanQbe.T.TFlatFn
  let fnTy := Lean.mkConst ``LeanQbe.T.Fn
  let listFlatTy := mkApp (Lean.mkConst ``List [.zero]) flatTy
  let listFnTy := mkApp (Lean.mkConst ``List [.one]) fnTy
  let modTy := Lean.mkConst ``LeanQbe.T.Module
  liftCoreM do
    let (flatConsts, fnConsts) ← InlineMeta.emitMatFnDefs pfx tfs false
    let fnsNm := ns ++ `bitblastFlatFns
    addCertDef fnsNm listFlatTy (InlineMeta.mkListLit .zero flatTy flatConsts) false
    let modNm := ns ++ `bitblastFlatMod
    let modVal := mkApp3 (Lean.mkConst ``LeanQbe.T.Module.mk)
      (InlineMeta.mkListLit .one fnTy fnConsts)
      (Lean.mkConst ``bitblastExterns)
      (mkApp (Lean.mkConst ``List.nil [.zero]) (Lean.mkConst ``LeanQbe.T.Sym))
    addCertDef modNm modTy modVal false
    let flatModFnsE := mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) (Lean.mkConst modNm)
    let mapFlatE := mkApp4 (Lean.mkConst ``List.map [.zero, .one])
      flatTy fnTy (Lean.mkConst ``LeanQbe.T.TFlatFn.toFn) (Lean.mkConst fnsNm)
    addKernelEqThm (ns ++ `bitblastFlatMod_fns_flat_eq) listFnTy flatModFnsE mapFlatE .one
    let srcModFnsE := mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) srcModE
    addKernelEqThm (ns ++ `bitblastFlatMod_fns_eq) listFnTy flatModFnsE srcModFnsE .one

end

/-- Whole-module equality between materialized `bitblastFlatMod` and `bitblastModule`. -/
theorem bitblastFlatMod_eq : bitblastFlatMod = bitblastModule :=
  congrArg
    (fun fs => ({ fns := fs, externs := bitblastExterns, exits := [] } : Module))
    bitblastFlatMod_fns_eq

end

end LeanQbe.T.Examples.Bitblast.Build
