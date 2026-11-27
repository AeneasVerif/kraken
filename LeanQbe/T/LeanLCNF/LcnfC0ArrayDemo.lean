module

public import LeanQbe.T.LeanLCNF.Basic
public import LeanQbe.T.LeanLCNF.Lower1
public import LeanQbe.T.Bootstrap0.Splice0
public import LeanQbe.T.LeanLCNF.LcnfC0Full
meta import Lean
meta import LeanQbe.T.LeanLCNF.Basic
meta import LeanQbe.T.LeanLCNF.Lower1
meta import LeanQbe.T.Bootstrap0.Splice0

/-!
# Verified `Array` & `ByteArray` COW Container `LCNF` Demo (`LcnfC0ArrayDemo`)

Pure data/IR module (`0` proof imports, `0` target-arch imports) extracting three straight-line
Lean 4 R2 container clients via `lcnf_of_lean!` and `splice_lcnf_tflat!` for acyclic linking
onto `rtC0CoreMod` via `LcnfC0LinkKit`:

1. `ArrayDemo.arrayPushSetGet`: allocates an `Array Nat` via `Array.emptyWithCapacity 4`, pushes
   two elements, updates slot `0` in-place via `Array.set!`, reads slots `0` and `1`, releases
   the array via `lcnf_dec_ref_cold`, and returns `c + b`.
2. `ArrayDemo.baPushSetGet`: allocates a `ByteArray` via `ByteArray.emptyWithCapacity cap`,
   pushes two bytes, updates byte `0` in-place via `ByteArray.set!`, reads bytes `0` and `1`,
   releases the `ByteArray`, and returns `c + b`.
3. `ArrayDemo.baCowSetGet`: updates byte `0` of an input `ByteArray` via `ByteArray.set!` (both
   exclusive `rc = 1` in-place and shared `rc ≥ 2` copy-on-write paths), reads bytes `0` and `1`,
   and releases the updated handle while preserving any shared original.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T

namespace ArrayDemo

/-- Straight-line `Array Nat` client: `emptyWithCapacity`, `push`, `push`, `set!`, `get!`. -/
@[expose] def arrayPushSetGet (a b c : Nat) : Nat :=
  let arr := (Array.emptyWithCapacity 4).push a
  let arr := arr.push b
  let arr := arr.set! 0 c
  arr[0]! + arr[1]!

/-- Straight-line `ByteArray` client: `emptyWithCapacity`, `push`, `push`, `set!`, `get!`. -/
@[expose] def baPushSetGet (cap : Nat) (a b c : UInt8) : UInt8 :=
  let ba := (ByteArray.emptyWithCapacity cap).push a
  let ba := ba.push b
  let ba := ba.set! 0 c
  ba.get! 0 + ba.get! 1

/-- Shared/exclusive COW `ByteArray` update & read client (`set!` + `get!`). -/
@[expose] def baCowSetGet (ba : ByteArray) (v : UInt8) : UInt8 :=
  let ba' := ba.set! 0 v
  ba'.get! 0 + ba'.get! 1

end ArrayDemo

lcnf_of_lean! arrayDemoLcMod
  [ArrayDemo.arrayPushSetGet, ArrayDemo.baPushSetGet, ArrayDemo.baCowSetGet]

splice_lcnf_tflat! arrayDemoTfs arrayDemoLcMod

/-- Mangled symbol name of `ArrayDemo.arrayPushSetGet`. -/
@[expose] def arrayDemoArrName : Sym :=
  "l_LeanQbe_T_LeanLCNF_ArrayDemo_arrayPushSetGet"

/-- Mangled symbol name of `ArrayDemo.baPushSetGet`. -/
@[expose] def arrayDemoBaName : Sym :=
  "l_LeanQbe_T_LeanLCNF_ArrayDemo_baPushSetGet"

/-- Mangled symbol name of `ArrayDemo.baCowSetGet`. -/
@[expose] def arrayDemoBaCowName : Sym :=
  "l_LeanQbe_T_LeanLCNF_ArrayDemo_baCowSetGet"

/-- Standalone user `Module` containing the three lowered R2 container client functions. -/
@[expose] def arrayDemoProgMod : Module :=
  { fns := Frontend.C0.tflatFnsToFns arrayDemoTfs, externs := [], exits := rtExitSyms }

/-- Full `89`-function linked `Module`: `rtC0CoreMod` (`86` fns) ++ `arrayDemoProgMod` (`3` fns).
-/
@[expose] def arrayDemoLinkedMod : Module :=
  linkLcnfWithRtC0 arrayDemoTfs false

end LeanQbe.T.LeanLCNF
