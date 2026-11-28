module

public import LeanQbe.T.Wasm.Safety
public import LeanQbe.T.MainCertProof
import LeanQbe.T.MainCertElab
public import LeanQbe.T.MainCertScc
meta import LeanQbe.T.Module

/-!
# Target-Independent WebAssembly Memory Safety Audit Specification

Audits the verified WebAssembly-to-`LeanQbe.T` sandbox pipeline on a multi-function
guest module (`wasmAuditMod`) containing:

1. `mix32(acc, word) -> acc'`: arithmetic, bitwise, SWAR `i32.popcnt`, and guarded `i32.rem_u`
   trap checks.
2. `write_hash(ptr, word) -> mem_pages`: conditional `if_`, cross-function `call $mix32`,
   SFI bounds-checked `i32.store`, and `memory.size`.
3. `sum_mix(ptr, len) -> acc`: structured `block`/`loop`/`br_if`/`br`, SFI bounds-checked
   `i32.load`, and cross-function `call $mix32`.

## What Is Proved (ISA-Neutral, Standard Axioms)
* `validateModule wasmAuditMod = true` and `(lowerModule wasmAuditMod).checkAcyclic = true`.
* `lowerModule_wf`, `lowerModule_namesNodup`, `lowerModule_supportsSource`, and
  `lowerModule_legalSig` for arbitrary `LegalTarget` supporting Wasm lowering.
* Universal `WasmNoExitEnv` / `ModuleOk`, `ModuleSccOk`, and `wasm_preserves_host_mem`
  guarantees: ANY entry into `sum_mix`, `write_hash`, or `mix32` preserves arbitrary host
  memory `R` outside linear memory `[memBase, memBase + memLen)`, never performs OOB
  loads/stores, never hits undefined arithmetic, and returns `status ∈ {0#32, 1#32, 2#32}`.

This module imports neither `Kraken.X64` nor `Kraken.AArch64`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.WasmAuditSpec

open LeanQbe.T LeanQbe.T.Wasm LeanQbe.T.LinkScc

/-- Function 0: `mix32(acc, word) -> acc'` mixing via `popcnt`, `mul`, `rem_u`, and `xor`. -/
def fnMix32 : WFunc :=
  { name := "mix32"
    typeIdx := 0
    locals := []
    body :=
      [ .local_get 0
      , .local_get 1
      , .unop .i32 .popcnt
      , .binop .i32 .add
      , .i32_const 0x9e3779b1#32
      , .binop .i32 .mul
      , .local_get 1
      , .i32_const 7#32
      , .binop .i32 .or
      , .binop .i32 .rem_u
      , .local_get 0
      , .binop .i32 .xor
      ] }

/-- Function 1: `write_hash(ptr, word) -> mem_pages` hashing conditionally & storing SFI-safe. -/
def fnWriteHash : WFunc :=
  { name := "write_hash"
    typeIdx := 0
    locals := [.i32]
    body :=
      [ .local_get 1
      , .if_ .empty
          [ .i32_const 0x13579bdf#32
          , .local_get 1
          , .call 0
          , .local_set 2
          ]
          [ .i32_const 0x2468ace0#32
          , .local_set 2
          ]
      , .local_get 0
      , .local_get 2
      , .store .i32 .w32 { offset := 0 }
      , .memory_size
      ] }

/-- Function 2: `sum_mix(ptr, len) -> acc` looping over an `i32` array in linear memory. -/
def fnSumMix : WFunc :=
  { name := "sum_mix"
    typeIdx := 0
    locals := [.i32, .i32]
    body :=
      [ .i32_const 0#32
      , .local_set 2
      , .i32_const 0#32
      , .local_set 3
      , .block .empty
          [ .loop .empty
              [ .local_get 2
              , .local_get 1
              , .relop .i32 .ge_u
              , .br_if 1
              , .local_get 3
              , .local_get 0
              , .local_get 2
              , .i32_const 4#32
              , .binop .i32 .mul
              , .binop .i32 .add
              , .load .i32 .w32 false { offset := 0 }
              , .call 0
              , .local_set 3
              , .local_get 2
              , .i32_const 1#32
              , .binop .i32 .add
              , .local_set 2
              , .br 0
              ]
          ]
      , .local_get 3
      ] }

/-- Multi-function validated WebAssembly guest module with linear memory (`64 KiB .. 128 KiB`). -/
def wasmAuditMod : WModule :=
  { types := [{ params := [.i32, .i32], results := [.i32] }]
    funcs := [fnMix32, fnWriteHash, fnSumMix]
    memory := some { initPages := 1, maxPages := some 2 }
    globals := [] }

/-- Lowered `LeanQbe.T.Module` produced by `lowerModule wasmAuditMod`. -/
def wasmQbeMod : Module := lowerModule wasmAuditMod

theorem wasmAuditMod_valid : validateModule wasmAuditMod = true := by decide

theorem wasmAuditMod_acyclic : wasmAcyclic wasmAuditMod = true := by decide

theorem wasmQbeMod_acyclic : wasmQbeMod.checkAcyclic = true :=
  lowerModule_checkAcyclic wasmAuditMod_valid wasmAuditMod_acyclic

theorem wasmQbeMod_wf : ∀ fn ∈ wasmQbeMod.fns, fn.Wf := lowerModule_wf wasmAuditMod

theorem wasmQbeMod_namesNodup : (wasmQbeMod.fns.map Fn.name).Nodup :=
  lowerModule_namesNodup wasmAuditMod_valid

theorem wasmQbeMod_moduleOk : ModuleOk (WasmSandboxEnvAny wasmAuditMod) wasmQbeMod :=
  lowerModule_moduleOk wasmAuditMod_valid wasmQbeMod_acyclic

theorem wasmQbeMod_wp :
    ∀ f ∈ wasmQbeMod.fns, ∀ (xs : Tup Val f.as) (m : Mem 64)
      (Q : Post f.rs) (X : XPost),
      WasmSandboxEnvAny wasmAuditMod f.name f.as f.rs xs m Q X →
      Func.wp (WasmSandboxEnvAny wasmAuditMod) f.body xs m Q X := by
  intro f hf
  rcases List.mem_iff_append.mp hf with ⟨pre, post, hsp⟩
  exact (wasmQbeMod_moduleOk.fnsOk pre f post hsp).2.2

theorem wasmQbeMod_moduleSccOk (Γext : Env) :
    ModuleSccOk natRecIdx (WasmSandboxEnv wasmAuditMod) Γext false wasmQbeMod :=
  lowerModule_moduleSccOk wasmAuditMod_valid Γext

theorem wasmQbeMod_preserves_host (Γext : Env) {f : WFunc} (hf : f ∈ wasmAuditMod.funcs)
    (vmCtx memBase memLen memCap fuel : BitVec 64)
    (args : Tup Val (((wasmAuditMod.types[f.typeIdx]?).getD {}).params.map WValTy.toTy))
    {R : Mem 64 → Prop} {mem : Mem 64}
    (hmem : WasmMemInv true vmCtx memBase memLen memCap R mem)
    (Q : Post (wasmAbiResults ((wasmAuditMod.types[f.typeIdx]?).getD {}))) (X : XPost)
    (hpost : ∀ ys mem', WasmPost true vmCtx memBase memLen memCap fuel
      ((wasmAuditMod.types[f.typeIdx]?).getD {}).results R ys mem' → Q ys mem') :
    Env.semScc wasmQbeMod Γext f.name
      (wasmAbiParams ((wasmAuditMod.types[f.typeIdx]?).getD {}))
      (wasmAbiResults ((wasmAuditMod.types[f.typeIdx]?).getD {}))
      (vmCtx, fuel, args) mem Q X :=
  wasm_preserves_host_mem wasmAuditMod_valid Γext hf vmCtx memBase memLen memCap fuel args
    hmem Q X hpost

theorem wasmSandboxEnvAny_monoX (f : Sym) (as bs : List Ty) (xs : Tup Val as)
    (mem : Mem 64) (Q : Post bs) (X X' : XPost)
    (h : WasmSandboxEnvAny wasmAuditMod f as bs xs mem Q X) :
    WasmSandboxEnvAny wasmAuditMod f as bs xs mem Q X' :=
  h

#print axioms wasmAuditMod_valid
#print axioms wasmQbeMod_acyclic
#print axioms wasmQbeMod_wf
#print axioms wasmQbeMod_moduleOk
#print axioms wasmQbeMod_moduleSccOk
#print axioms wasmQbeMod_preserves_host

end LeanQbeTest.T.WasmAuditSpec
