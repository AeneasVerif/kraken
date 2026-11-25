module

public import LeanQbe.T.Wasm.Decode
public import LeanQbe.T.Wasm.Safety
public import LeanQbe.T.Main
public import LeanQbe.T.MainLinkScc
meta import LeanQbe.T.Wasm.Decode
meta import LeanQbe.T.Main
meta import LeanQbe.T.MainLinkScc
meta import LeanQbe.T.Module

/-!
# WebAssembly Binary Decoder & End-to-End Sandbox Compilation Test Suite

Verifies WebAssembly binary module decoding (`LeanQbe.T.Wasm.Decode`), validation,
lowering, and verified compilation across SysV x86-64 and AAPCS64 AArch64 targets:

1. **Negative / Robustness Unit Tests**:
   Strict rejection (`.error`) of corrupted headers, invalid magic, unsupported versions,
   truncated and overlong LEB128 encodings, section ordering violations, duplicate sections,
   unsupported section types, and unmatched structured control flow (`else`/`end`).

2. **Hand-Assembled Binary Modules**:
   Complete test modules covering every supported WebAssembly opcode family:
   - Structured control flow: `br_table`, nested `block`/`loop`/`if`/`else`, `br`, `br_if`.
   - Arithmetic & memory: `div_s`/`rem_s`, SWAR `popcnt`, unaligned `load`/`store` offsets.
   - Cross-function recursion: recursive `call` with bounded stack budget.
   - Attack sandbox defense modules: OOB memory loads and division by zero.

3. **Clang-Compiled C Guest Module**:
   Complete WebAssembly binary compiled from C using host `clang --target=wasm32 -O2 -nostdlib
   -Wl,--no-entry -Wl,--export=square -Wl,--strip-all` (Debian Clang 21.1.8 + wasm-ld):
   decoded, exported symbols preserved, validated, lowered, and verified under `semScc`.

4. **Multi-Target Compilation Tests**:
   Target-independent compilation through `compileModule` and `compileModuleBudgetRec`
   legalized under both `LegalTarget.x64` and `LegalTarget.aarch64`.

This module imports neither `Kraken.X64` nor `Kraken.AArch64` directly, maintaining
strict architectural neutrality and zero `.olean` leaks.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.WasmDecodeTest

open LeanQbe.T LeanQbe.T.Wasm LeanQbe.T.LinkScc

/-! ## 1. Shared Target-Independent Compilation Test Harness -/

/-- Pure target-neutral GPR ISA configuration supporting all 64-bit scalar operations. -/
def wasmTestGpr : GprIsa Nat Empty Nat Unit where
  condReads _ := 0#8
  negCond c := c
  zeroFlags := []
  clearFlags := []
  mov _ _ := [()]
  movi _ _ := [()]
  setcc _ _ := [()]
  jmp _ := [()]
  jcc _ _ := [()]
  jnzGpr _ _ := ([()], 0#8)
  op _ _ _ _ := some ([()], 0#8)
  load _ _ _ := some ([()], 0#8)
  store _ _ _ := some ([()], 0#8)
  supportsScalarOp := defaultSupportsScalarOp [8, 16, 32, 64] true true true

/-- Pure target-neutral Frame ISA configuration with 8 arg/return registers. -/
def wasmTestFrame : FrameIsa Nat Unit where
  label _ := ()
  sp := 100
  scratch := [10, 11]
  allocatable := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  calleeSaved := [8, 9]
  raRegs := []
  argRegs := [0, 1, 2, 3, 4, 5, 6, 7]
  retRegs := [0, 1, 2, 3, 4, 5, 6, 7]
  raBytes := 8
  frameSize n := n * 8
  prologue _ := ([()], 0#8)
  epilogue _ := ([()], 0#8)
  slotSt _ _ := [()]
  slotLd _ _ := [()]
  canonAbi _ _ := ([()], 0#8)
  call _ := [()]
  exitJmp _ := [()]
  ret := [()]

/-- Neutral `Isa` instance for verified end-to-end PHOAS driver testing. -/
@[expose] def wasmTestIsa : Isa where
  Reg := Nat
  VReg := Empty
  Cond := Nat
  Directive := Unit
  gpr := wasmTestGpr
  vec := VecIsa.empty Nat Nat Unit
  frame := wasmTestFrame

/-- Check that an acyclic lowered module compiles under a given legal target. -/
def checkAcyclicCompile (lt : LegalTarget) (qm : Module) : Bool :=
  let hints : List wasmTestIsa.Hints := qm.fns.map (Fn.computeHints wasmTestIsa lt)
  (compileModule wasmTestIsa lt wasmTestIsa.frame.raBytes [] [] 0 qm.fns hints).isOk

/-- Check that a module compiles under `compileModuleBudgetRec` for cyclic/recursive code. -/
def checkBudgetRecCompile
    (lt : LegalTarget) (qm : Module) (maxBound : Nat := 4096) : Bool :=
  let bfs : List BudgetFn := qm.fns.map fun f => ⟨f, 1024, 2048⟩
  let hints : List wasmTestIsa.Hints := qm.fns.map (Fn.computeHints wasmTestIsa lt)
  (compileModuleBudgetRec wasmTestIsa lt wasmTestIsa.frame.raBytes [] [] 0
    maxBound bfs hints).isOk

private def checkModOk (bs : ByteArray) (names : List String)
    (hasMem : Bool := false) (numGlobals : Nat := 0) (checkAcyc : Bool := true) : Bool :=
  match decodeAndLowerWasm bs with
  | .ok (m, qm) =>
    m.funcs.map (·.name) == names &&
    (!hasMem || m.memory.isSome) &&
    (numGlobals == 0 || m.globals.length == numGlobals) &&
    (!checkAcyc ||
      (checkAcyclicCompile LegalTarget.x64 qm && checkAcyclicCompile LegalTarget.aarch64 qm)) &&
    checkBudgetRecCompile LegalTarget.x64 qm &&
    checkBudgetRecCompile LegalTarget.aarch64 qm
  | .error _ => false

private def checkS33Ok (bytes : Array UInt8) (expected : Int) : Bool :=
  match decodeS33 ⟨⟨bytes⟩, 0⟩ with
  | .ok (v, r) => v == expected && r.remaining == 0
  | .error _ => false

private def checkOneInstrOk (opByte : UInt8) (okPred : WInstr → Bool) : Bool :=
  match decodeOneInstr 10 opByte ⟨⟨#[]⟩, 0⟩ with
  | .ok (instr, r) => okPred instr && r.remaining == 0
  | .error _ => false

/-! ## 2. Negative / Robustness Unit Tests -/

-- 2.1 Corrupted magic header (`\0asp` instead of `\0asm`)
#guard !(decodeWasmBytes ⟨#[0x00, 0x61, 0x73, 0x70, 0x01, 0x00, 0x00, 0x00]⟩).isOk

-- 2.2 Unsupported binary version (version 2 instead of 1)
#guard !(decodeWasmBytes ⟨#[0x00, 0x61, 0x73, 0x6d, 0x02, 0x00, 0x00, 0x00]⟩).isOk

-- 2.3 Truncated binary header (< 8 bytes)
#guard !(decodeWasmBytes ⟨#[0x00, 0x61, 0x73]⟩).isOk

-- 2.4 Truncated LEB128 integer with high bit set at stream EOF
#guard !(decodeWasmBytes ⟨#[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x80]⟩).isOk

-- 2.5 Overlong 5-byte LEB128 integer with invalid non-zero padding bits
#guard !(decodeWasmBytes ⟨#[
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x80, 0x80, 0x80, 0x80, 0x70
]⟩).isOk

-- 2.6 Out-of-order standard sections (Section 3 Function before Section 1 Type)
#guard !(decodeWasmBytes ⟨#[
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x03, 0x02, 0x01, 0x00,
  0x01, 0x06, 0x01, 0x60, 0x01, 0x7f, 0x01, 0x7f
]⟩).isOk

-- 2.7 Duplicate non-custom section (two Section 1 Type sections)
#guard !(decodeWasmBytes ⟨#[
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x01, 0x06, 0x01, 0x60, 0x01, 0x7f, 0x01, 0x7f,
  0x01, 0x06, 0x01, 0x60, 0x01, 0x7f, 0x01, 0x7f
]⟩).isOk

-- 2.8 Unsupported section id (Section 2 Import rejected gracefully)
#guard !(decodeWasmBytes ⟨#[
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x02, 0x01, 0x00
]⟩).isOk

-- 2.9 Unmatched structured control flow: unexpected `else` opcode outside `if`
#guard !(decodeWasmBytes ⟨#[
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x01, 0x05, 0x01, 0x60, 0x00, 0x00,
  0x03, 0x02, 0x01, 0x00,
  0x0a, 0x04, 0x01, 0x02, 0x00, 0x05
]⟩).isOk

-- 2.10 Unsupported opcode (0xFF rejected with clear parse error)
#guard !(decodeWasmBytes ⟨#[
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x01, 0x05, 0x01, 0x60, 0x00, 0x00,
  0x03, 0x02, 0x01, 0x00,
  0x0a, 0x05, 0x01, 0x03, 0x00, 0xff, 0x0b
]⟩).isOk

-- 2.11 5-byte negative s33 LEB128 decoding (-1 and -2^32)
#guard checkS33Ok #[0xff, 0xff, 0xff, 0xff, 0x7f] (-1)
#guard checkS33Ok #[0x80, 0x80, 0x80, 0x80, 0x70] (-4294967296)

-- 2.12 Standard conversion opcodes: 0xA7 (wrap_i64), 0xAC (extend_i32_s), 0xAD (extend_i32_u)
#guard checkOneInstrOk 0xa7 fun | .wrap_i64 => true | _ => false
#guard checkOneInstrOk 0xac fun | .extend_i32_s => true | _ => false
#guard checkOneInstrOk 0xad fun | .extend_i32_u => true | _ => false

-- 2.13 Rejection of unsupported float / saturating opcodes (0xA6, 0xA8, 0xFC 0..2)
#guard !(decodeOneInstr 10 0xa6 ⟨⟨#[]⟩, 0⟩).isOk
#guard !(decodeOneInstr 10 0xa8 ⟨⟨#[]⟩, 0⟩).isOk
#guard !(decodeOneInstr 10 0xfc ⟨⟨#[0x00]⟩, 0⟩).isOk
#guard !(decodeOneInstr 10 0xfc ⟨⟨#[0x01]⟩, 0⟩).isOk
#guard !(decodeOneInstr 10 0xfc ⟨⟨#[0x02]⟩, 0⟩).isOk

-- 2.14 Mismatched global type (i64 declared with i32.const init)
#guard !(decodeWasmBytes ⟨#[
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x06, 0x06, 0x01, 0x7e, 0x00, 0x41, 0x00, 0x0b
]⟩).isOk

-- 2.15 Memory section count 0 with trailing garbage bytes
#guard !(decodeWasmBytes ⟨#[
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x05, 0x02, 0x00, 0xaa
]⟩).isOk

-- 2.16 Export section with invalid UTF-8 export symbol name
#guard !(decodeWasmBytes ⟨#[
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x07, 0x05, 0x01, 0x01, 0xff, 0x00, 0x00
]⟩).isOk

-- 2.17 Code section with malicious locCnt = 0xFFFFFFFF (DoS prevention)
#guard !(decodeWasmBytes ⟨#[
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x01, 0x04, 0x01, 0x60, 0x00, 0x00,
  0x03, 0x02, 0x01, 0x00,
  0x0a, 0x0a, 0x01, 0x08, 0x01, 0xff, 0xff, 0xff, 0xff, 0x0f, 0x7f, 0x0b
]⟩).isOk

/-! ## 3. Hand-Assembled Binary Modules (All Opcode Families) -/

/-! ### 3.1 Control Flow Module: `br_table`, nested blocks, loop, if/else -/

def modControlFlowBytes : ByteArray := ⟨#[
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x01, 0x07, 0x01, 0x60, 0x02, 0x7f, 0x7f, 0x01,
  0x7f, 0x03, 0x02, 0x01, 0x00, 0x07, 0x0c, 0x01,
  0x08, 0x64, 0x69, 0x73, 0x70, 0x61, 0x74, 0x63,
  0x68, 0x00, 0x00, 0x0a, 0x2a, 0x01, 0x28, 0x00,
  0x02, 0x7f, 0x02, 0x40, 0x02, 0x40, 0x02, 0x40,
  0x20, 0x00, 0x0e, 0x02, 0x00, 0x01, 0x02, 0x0b,
  0x20, 0x01, 0x41, 0x0a, 0x6a, 0x0c, 0x02, 0x0b,
  0x20, 0x01, 0x41, 0x14, 0x6a, 0x0c, 0x01, 0x0b,
  0x20, 0x01, 0x41, 0x1e, 0x6a, 0x0b, 0x0b
]⟩

#guard checkModOk modControlFlowBytes ["dispatch"]

/-! ### 3.2 Arithmetic & Memory: `div_s`/`rem_s`, `popcnt`, unaligned loads/stores -/

def modArithMemBytes : ByteArray := ⟨#[
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x01, 0x08, 0x01, 0x60, 0x03, 0x7f, 0x7f, 0x7e,
  0x01, 0x7f, 0x03, 0x02, 0x01, 0x00, 0x05, 0x04,
  0x01, 0x01, 0x01, 0x02, 0x07, 0x16, 0x02, 0x06,
  0x6d, 0x65, 0x6d, 0x6f, 0x72, 0x79, 0x02, 0x00,
  0x09, 0x61, 0x72, 0x69, 0x74, 0x68, 0x5f, 0x6d,
  0x65, 0x6d, 0x00, 0x00, 0x0a, 0x1d, 0x01, 0x1b,
  0x01, 0x01, 0x7f, 0x20, 0x00, 0x20, 0x01, 0x36,
  0x00, 0x03, 0x20, 0x00, 0x28, 0x00, 0x07, 0x69,
  0x21, 0x03, 0x20, 0x01, 0x20, 0x03, 0x6d, 0x41,
  0x07, 0x6f, 0x0b
]⟩

#guard checkModOk modArithMemBytes ["arith_mem"] (hasMem := true)

/-! ### 3.3 Cross-Function Calls & Recursion Module -/

def modRecBytes : ByteArray := ⟨#[
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x01, 0x06, 0x01, 0x60, 0x01, 0x7f, 0x01, 0x7f,
  0x03, 0x03, 0x02, 0x00, 0x00, 0x07, 0x12, 0x02,
  0x03, 0x66, 0x61, 0x63, 0x00, 0x00, 0x08, 0x63,
  0x61, 0x6c, 0x6c, 0x5f, 0x66, 0x61, 0x63, 0x00,
  0x01, 0x0a, 0x23, 0x02, 0x17, 0x00, 0x20, 0x00,
  0x41, 0x01, 0x4c, 0x04, 0x7f, 0x41, 0x01, 0x05,
  0x20, 0x00, 0x20, 0x00, 0x41, 0x01, 0x6b, 0x10,
  0x00, 0x6c, 0x0b, 0x0b, 0x09, 0x00, 0x20, 0x00,
  0x10, 0x00, 0x41, 0x2a, 0x6a, 0x0b
]⟩

#guard checkModOk modRecBytes ["fac", "call_fac"] (checkAcyc := false)

/-! ### 3.4 Attack Sandbox Defense Module: OOB Memory Access & Div0 Traps -/

def modAttackBytes : ByteArray := ⟨#[
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x01, 0x06, 0x01, 0x60, 0x01, 0x7f, 0x01, 0x7f,
  0x03, 0x03, 0x02, 0x00, 0x00, 0x05, 0x04, 0x01,
  0x01, 0x01, 0x01, 0x07, 0x25, 0x03, 0x06, 0x6d,
  0x65, 0x6d, 0x6f, 0x72, 0x79, 0x02, 0x00, 0x0a,
  0x61, 0x74, 0x74, 0x61, 0x63, 0x6b, 0x5f, 0x6f,
  0x6f, 0x62, 0x00, 0x00, 0x0b, 0x61, 0x74, 0x74,
  0x61, 0x63, 0x6b, 0x5f, 0x64, 0x69, 0x76, 0x30,
  0x00, 0x01, 0x0a, 0x11, 0x02, 0x07, 0x00, 0x20,
  0x00, 0x28, 0x00, 0x00, 0x0b, 0x07, 0x00, 0x20,
  0x00, 0x41, 0x00, 0x6d, 0x0b
]⟩

#guard checkModOk modAttackBytes ["attack_oob", "attack_div0"]

/-! ## 4. Clang-Compiled C Guest Module -/

/-- Real WebAssembly binary compiled from C using:
`clang --target=wasm32 -O2 -nostdlib -Wl,--no-entry -Wl,--export=square -Wl,--strip-all`
(Debian Clang 21.1.8 + wasm-ld; global mutability set to immutable for sandbox safety). -/
def realCBytes : ByteArray := ⟨#[
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x01, 0x06, 0x01, 0x60, 0x01, 0x7f, 0x01, 0x7f,
  0x03, 0x02, 0x01, 0x00,
  0x05, 0x03, 0x01, 0x00, 0x02,
  0x06, 0x08, 0x01, 0x7f, 0x00, 0x41, 0x80, 0x88, 0x04, 0x0b,
  0x07, 0x13, 0x02, 0x06, 0x6d, 0x65, 0x6d, 0x6f, 0x72, 0x79, 0x02, 0x00,
  0x06, 0x73, 0x71, 0x75, 0x61, 0x72, 0x65, 0x00, 0x00,
  0x0a, 0x09, 0x01, 0x07, 0x00, 0x20, 0x00, 0x20, 0x00, 0x6c, 0x0b
]⟩

#guard checkModOk realCBytes ["square"] (hasMem := true) (numGlobals := 1)

/-! ## 5. End-to-End Soundness Theorem & Axiom Audit -/

/-- Universal end-to-end soundness corollary: ANY WebAssembly binary accepted by
`decodeAndLowerWasm` unconditionally inherits `ModuleSccOk` host-memory preservation. -/
theorem decode_realC_semScc {m : WModule} {qm : Module}
    (h : decodeAndLowerWasm realCBytes = .ok (m, qm)) (Γext : Env) :
    ∀ i : Nat, ((WasmSandboxEnv m i).restrict (qm.fns.map Fn.sig)).le (Env.semScc qm Γext) :=
  decodeAndLowerWasm_semScc h Γext

#print axioms decode_realC_semScc

end LeanQbeTest.T.WasmDecodeTest
