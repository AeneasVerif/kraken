module

import LeanQbe.T.Wasm.Normalize
import LeanQbe.T.Wasm.Safety
import LeanQbe.T.MainFlat
import LeanQbe.T.Spill
import LeanQbeTest.T.WasmCertKit
meta import LeanQbe.T.Wasm.Normalize
meta import LeanQbe.T.MainFlat
meta import LeanQbe.T.Spill
meta import LeanQbeTest.T.WasmCertKit

/-!
# Untrusted WebAssembly Normalizer Test Suite (`WasmNormalizeTest`)

Verifies `LeanQbe.T.Wasm.Normalize` on self-contained synthetic `.wasm` binaries
covering:
1. Mutable `i32` & `i64` globals (`global.get`/`global.set`), active `Sec 11 (Data)`
   (`13`-byte segment exercising `i64.store` + `i32.store` + `i32.store8`),
   `Sec 12 (DataCount)`, and optional unused empty `Sec 4 (Table)`.
2. `6`-parameter (`> maxWasmParams = 4`) nested call (`call_leaf6 -> leaf6`) with
   mixed `i32`/`i64` spilled arguments via the shadow-stack pointer at `spSlot`.
3. `6`-parameter self-recursive function (`run_sum6 -> sum6_rec`) verifying
   recursion-safe shadow-stack spill/reload.
4. Dual-arch (`LegalTarget.x64` and `LegalTarget.aarch64`) `compileModuleFlat` checks.
5. Negative rejection tests (`call_indirect`, non-empty `Sec 9`, imports, invalid config).
6. End-to-end soundness bridge (`decodeNormalizeAndLowerWasm_ok` + instantiated
   `wasm_preserves_host_mem`) audited with `#print axioms` (`<= std3`).

This module imports neither `Kraken.X64` nor `Kraken.AArch64` directly.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.WasmNormalizeTest

open LeanQbe.T LeanQbe.T.Wasm LeanQbe.T.LinkScc

/-! ## 1. Dual-Arch `compileModuleFlat` & Validation Harness -/

private def checkFlatCompile (lt : LegalTarget) (qm : Module)
    (extCallees : List (SigEntry × Nat) := []) : Bool :=
  let flatFns : List TFlatFn :=
    qm.fns.map fun fn => ⟨fn.name, fn.as, fn.rs, reifyFunc fn.body⟩
  let hints : List WasmCertKit.wasmTestIsa.Hints :=
    flatFns.map fun ff =>
      Spill.hints WasmCertKit.wasmTestIsa (midStageFlat lt (earlyOptFlat ff)).toFn
  match compileModuleFlat WasmCertKit.wasmTestIsa lt WasmCertKit.wasmTestFrame.raBytes
      extCallees [] 0 flatFns hints with
  | .ok (code, bounds) => !code.isEmpty && bounds.length == qm.fns.length
  | .error _ => false

private def checkNormOk (bs : ByteArray) (names : List String)
    (extCallees : List (SigEntry × Nat) := []) (checkAcyc : Bool := true) : Bool :=
  match decodeNormalizeAndLowerWasm {} bs with
  | .ok (wm, qm) =>
    wm.funcs.map (·.name) == names &&
    wm.globals.all (fun g => !g.mut_) &&
    (wm.funcs.all fun f =>
      match wm.types[f.typeIdx]? with
      | some ft => ft.params.length ≤ maxWasmParams
      | none => false) &&
    (!checkAcyc ||
      (checkFlatCompile LegalTarget.x64 qm extCallees &&
       checkFlatCompile LegalTarget.aarch64 qm extCallees)) &&
    WasmCertKit.wasmCheckBudgetRecCompile LegalTarget.x64 qm &&
    WasmCertKit.wasmCheckBudgetRecCompile LegalTarget.aarch64 qm
  | .error _ => false

/-! ## 2. Synthetic `.wasm` Test Fixtures -/

/-- Mutable `i32`/`i64` globals (`global.set`), active `Sec 11 (Data)` (`13` bytes at
`1024`), `Sec 12 (DataCount = 1)`, and unused empty `Sec 4 (Table)`. -/
def modMutGlobDataBytes : ByteArray := ⟨#[
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x06, 0x01, 0x60,
  0x01, 0x7f, 0x01, 0x7f, 0x03, 0x02, 0x01, 0x00, 0x04, 0x04, 0x01, 0x70,
  0x00, 0x01, 0x05, 0x03, 0x01, 0x00, 0x01, 0x06, 0x0d, 0x02, 0x7f, 0x01,
  0x41, 0x90, 0xce, 0x00, 0x0b, 0x7e, 0x01, 0x42, 0x07, 0x0b, 0x07, 0x11,
  0x01, 0x0d, 0x62, 0x75, 0x6d, 0x70, 0x5f, 0x61, 0x6e, 0x64, 0x5f, 0x72,
  0x65, 0x61, 0x64, 0x00, 0x00, 0x0c, 0x01, 0x01, 0x0a, 0x1f, 0x01, 0x1d,
  0x00, 0x23, 0x00, 0x20, 0x00, 0x6a, 0x24, 0x00, 0x23, 0x01, 0x42, 0x03,
  0x7c, 0x24, 0x01, 0x41, 0x80, 0x08, 0x28, 0x02, 0x00, 0x23, 0x00, 0x6a,
  0x23, 0x01, 0xa7, 0x6a, 0x0b, 0x0b, 0x14, 0x01, 0x00, 0x41, 0x80, 0x08,
  0x0b, 0x0d, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a,
  0x0b, 0x0c, 0x0d
]⟩

/-- `6`-param nested call `(i32, i32, i32, i32, i64, i32) -> i32`, mutable `$__stack_pointer`,
and empty `Sec 4 (Table)` (`min=1, max=1`). -/
def modSpill6NestedBytes : ByteArray := ⟨#[
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x10, 0x02, 0x60,
  0x06, 0x7f, 0x7f, 0x7f, 0x7f, 0x7e, 0x7f, 0x01, 0x7f, 0x60, 0x01, 0x7f,
  0x01, 0x7f, 0x03, 0x03, 0x02, 0x00, 0x01, 0x04, 0x05, 0x01, 0x70, 0x01,
  0x01, 0x01, 0x05, 0x03, 0x01, 0x00, 0x01, 0x06, 0x08, 0x01, 0x7f, 0x01,
  0x41, 0x80, 0x80, 0x04, 0x0b, 0x07, 0x0e, 0x01, 0x0a, 0x63, 0x61, 0x6c,
  0x6c, 0x5f, 0x6c, 0x65, 0x61, 0x66, 0x36, 0x00, 0x01, 0x0a, 0x27, 0x02,
  0x14, 0x00, 0x20, 0x00, 0x20, 0x01, 0x6a, 0x20, 0x02, 0x6a, 0x20, 0x03,
  0x6a, 0x20, 0x04, 0xa7, 0x6a, 0x20, 0x05, 0x6a, 0x0b, 0x10, 0x00, 0x20,
  0x00, 0x41, 0x01, 0x41, 0x02, 0x41, 0x03, 0x42, 0x04, 0x41, 0x05, 0x10,
  0x00, 0x0b
]⟩

/-- `6`-param self-recursive function `sum6_rec(n, a1..a5)` called by `run_sum6(n)`. -/
def modSpill6RecBytes : ByteArray := ⟨#[
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x10, 0x02, 0x60,
  0x06, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x01, 0x7f, 0x60, 0x01, 0x7f,
  0x01, 0x7f, 0x03, 0x03, 0x02, 0x00, 0x01, 0x05, 0x03, 0x01, 0x00, 0x01,
  0x06, 0x08, 0x01, 0x7f, 0x01, 0x41, 0x80, 0x80, 0x04, 0x0b, 0x07, 0x0c,
  0x01, 0x08, 0x72, 0x75, 0x6e, 0x5f, 0x73, 0x75, 0x6d, 0x36, 0x00, 0x01,
  0x0a, 0x40, 0x02, 0x2d, 0x00, 0x20, 0x00, 0x41, 0x00, 0x4c, 0x04, 0x7f,
  0x20, 0x01, 0x20, 0x02, 0x6a, 0x20, 0x03, 0x6a, 0x20, 0x04, 0x6a, 0x20,
  0x05, 0x6a, 0x05, 0x20, 0x00, 0x41, 0x01, 0x6b, 0x20, 0x01, 0x41, 0x01,
  0x6a, 0x20, 0x02, 0x20, 0x03, 0x20, 0x04, 0x20, 0x05, 0x10, 0x00, 0x0b,
  0x0b, 0x10, 0x00, 0x20, 0x00, 0x41, 0x01, 0x41, 0x02, 0x41, 0x03, 0x41,
  0x04, 0x41, 0x05, 0x10, 0x00, 0x0b
]⟩

#guard checkNormOk modMutGlobDataBytes ["__init_data", "bump_and_read"]
#guard checkNormOk modSpill6NestedBytes ["__init_data", "wasm_fn_0", "call_leaf6"]
#guard checkNormOk modSpill6RecBytes ["__init_data", "wasm_fn_0", "run_sum6"]
  (checkAcyc := false)
#guard match decodeNormalizeAndLowerWasm {} modSpill6RecBytes with
  | .ok (_, qm) =>
    let recSig : SigEntry := ("wasm_fn_0", [i64, i64, i32, i32, i32, i32], [i32, i64, i32])
    checkFlatCompile LegalTarget.x64 qm [(recSig, 512)] &&
    checkFlatCompile LegalTarget.aarch64 qm [(recSig, 512)]
  | .error _ => false

/-! ## 3. Negative Rejection Tests -/

private def badNorm (body : Array UInt8) : Bool :=
  let hdr : Array UInt8 := #[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00]
  !(decodeNormalizeWasm {} ⟨hdr ++ body⟩).isOk

#guard badNorm #[0x02, 0x05, 0x01, 0x01, 0x6d, 0x01, 0x66, 0x00, 0x00] -- non-empty Sec 2
#guard badNorm #[0x09, 0x07, 0x01, 0x00, 0x41, 0x00, 0x0b, 0x01, 0x00] -- non-empty Sec 9
#guard badNorm #[
  0x01, 0x04, 0x01, 0x60, 0x00, 0x00, 0x03, 0x02, 0x01, 0x00,
  0x04, 0x04, 0x01, 0x70, 0x00, 0x01,
  0x0a, 0x06, 0x01, 0x04, 0x00, 0x11, 0x00, 0x00, 0x0b] -- call_indirect (0x11)
#guard badNorm #[0x0c, 0x01, 0x02] -- DataCount mismatch (2 != 0)
#guard !(decodeNormalizeWasm { maxParams := 5 } modSpill6NestedBytes).isOk

/-! ## 4. Soundness Bridge & `wasm_preserves_host_mem` Axiom Audit -/

/-- End-to-end host-memory preservation via `decodeNormalizeAndLowerWasm_ok` +
`wasm_preserves_host_mem` for normalized Wasm modules (`0` new `Safety.lean` proofs). -/
theorem norm_preserves_host_mem {cfg : WNormConfig} {bs : ByteArray} {wm : WModule}
    {mod : Module} (h : decodeNormalizeAndLowerWasm cfg bs = .ok (wm, mod))
    (Γext : Env) {f : WFunc} (hf : f ∈ wm.funcs)
    (vmCtx memBase memLen memCap fuel : BitVec 64)
    (args : Tup Val (((wm.types[f.typeIdx]?).getD {}).params.map WValTy.toTy))
    {R : Mem 64 → Prop} {mem : Mem 64}
    (hmem : WasmMemInv wm.memory.isSome vmCtx memBase memLen memCap R mem)
    (Q : Post (wasmAbiResults ((wm.types[f.typeIdx]?).getD {}))) (X : XPost)
    (hpost : ∀ ys mem', WasmPost wm.memory.isSome vmCtx memBase memLen memCap fuel
      ((wm.types[f.typeIdx]?).getD {}).results R ys mem' → Q ys mem') :
    Env.semScc mod Γext f.name
      (wasmAbiParams ((wm.types[f.typeIdx]?).getD {}))
      (wasmAbiResults ((wm.types[f.typeIdx]?).getD {})) (vmCtx, fuel, args) mem Q X := by
  obtain ⟨hv, rfl⟩ := decodeNormalizeAndLowerWasm_ok h
  exact wasm_preserves_host_mem hv Γext hf vmCtx memBase memLen memCap fuel args hmem Q X hpost

/-- Concrete instantiated `wasm_preserves_host_mem` corollary for `modMutGlobDataBytes`. -/
theorem norm_mutGlobData_preserves_host {wm : WModule} {mod : Module}
    (h : decodeNormalizeAndLowerWasm {} modMutGlobDataBytes = .ok (wm, mod))
    (Γext : Env) {f : WFunc} (hf : f ∈ wm.funcs)
    (vmCtx memBase memLen memCap fuel : BitVec 64)
    (args : Tup Val (((wm.types[f.typeIdx]?).getD {}).params.map WValTy.toTy))
    {R : Mem 64 → Prop} {mem : Mem 64}
    (hmem : WasmMemInv wm.memory.isSome vmCtx memBase memLen memCap R mem)
    (Q : Post (wasmAbiResults ((wm.types[f.typeIdx]?).getD {}))) (X : XPost)
    (hpost : ∀ ys mem', WasmPost wm.memory.isSome vmCtx memBase memLen memCap fuel
      ((wm.types[f.typeIdx]?).getD {}).results R ys mem' → Q ys mem') :
    Env.semScc mod Γext f.name
      (wasmAbiParams ((wm.types[f.typeIdx]?).getD {}))
      (wasmAbiResults ((wm.types[f.typeIdx]?).getD {})) (vmCtx, fuel, args) mem Q X :=
  norm_preserves_host_mem h Γext hf vmCtx memBase memLen memCap fuel args hmem Q X hpost

/-- Concrete instantiated `wasm_preserves_host_mem` corollary for `modSpill6RecBytes`. -/
theorem norm_spill6Rec_preserves_host {wm : WModule} {mod : Module}
    (h : decodeNormalizeAndLowerWasm {} modSpill6RecBytes = .ok (wm, mod))
    (Γext : Env) {f : WFunc} (hf : f ∈ wm.funcs)
    (vmCtx memBase memLen memCap fuel : BitVec 64)
    (args : Tup Val (((wm.types[f.typeIdx]?).getD {}).params.map WValTy.toTy))
    {R : Mem 64 → Prop} {mem : Mem 64}
    (hmem : WasmMemInv wm.memory.isSome vmCtx memBase memLen memCap R mem)
    (Q : Post (wasmAbiResults ((wm.types[f.typeIdx]?).getD {}))) (X : XPost)
    (hpost : ∀ ys mem', WasmPost wm.memory.isSome vmCtx memBase memLen memCap fuel
      ((wm.types[f.typeIdx]?).getD {}).results R ys mem' → Q ys mem') :
    Env.semScc mod Γext f.name
      (wasmAbiParams ((wm.types[f.typeIdx]?).getD {}))
      (wasmAbiResults ((wm.types[f.typeIdx]?).getD {})) (vmCtx, fuel, args) mem Q X :=
  norm_preserves_host_mem h Γext hf vmCtx memBase memLen memCap fuel args hmem Q X hpost

#print axioms LeanQbe.T.Wasm.decodeNormalizeAndLowerWasm_ok
#print axioms norm_preserves_host_mem
#print axioms norm_mutGlobData_preserves_host
#print axioms norm_spill6Rec_preserves_host

end LeanQbeTest.T.WasmNormalizeTest
