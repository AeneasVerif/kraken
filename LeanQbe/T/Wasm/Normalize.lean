module

public import LeanQbe.T.Wasm.Ast
public import LeanQbe.T.Wasm.Validate
public import LeanQbe.T.Wasm.Decode
public import LeanQbe.T.Wasm.Lower
public import LeanQbe.T.Wasm.Safety

/-!
# Untrusted WebAssembly Normalizer (`LeanQbe.T.Wasm.Normalize`)

Decodes raw WebAssembly binaries (`RawWModule`) containing Clang/LLVM/wasm-ld constructs
outside the verified core subset and lowers them purely at the Lean AST level into
core `WModule`s accepted by `LeanQbe.T.Wasm.validateModule`:
* Mutable `i32`/`i64` globals + `global.set` (`0x24`) -> linear-memory slots.
* Active `Sec 11 (Data)` segments (memory 0, `i32.const` offset) + optional
  `Sec 12 (DataCount)` -> leaf `__init_data` helper guarded by `initFlagSlot` at the
  entry of every exported function.
* Functions with `> maxParams` (`≤ maxWasmParams`) parameters -> recursion-safe
  guest shadow-stack spill/reload via `*spSlot`.
* Optional unused empty `Sec 4 (Table)` / empty `Sec 9 (Elem)` (`0` elements, `0`
  `call_indirect`) stripped cleanly.

Exports `decodeNormalizeWasm`, `decodeNormalizeAndLowerWasm`, and the soundness bridge
theorem `decodeNormalizeAndLowerWasm_ok`, connecting directly into
`LeanQbe.T.Wasm.wasm_preserves_host_mem` and `lowerModule_semScc` with standard axioms.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Wasm

open LeanQbe.T

/-! ## Configuration & Raw Extended AST -/

/-- Configuration for untrusted WebAssembly normalization into core `WModule`. -/
structure WNormConfig where
  maxParams : Nat := maxWasmParams
  spSlot : UInt32 := 1020
  initFlagSlot : UInt32 := 1016
  initFnName : String := "__init_data"
  resetSpOnExportedEntry : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Active linear-memory data segment from WebAssembly Section 11. -/
structure RawWDataSeg where
  offset : BitVec 32
  data : ByteArray
  deriving Inhabited

/-- Extended WebAssembly instruction AST supporting `global.set` (`0x24`). -/
inductive RawWInstr where
  | block (bt : WBlockTy) (body : List RawWInstr)
  | loop (bt : WBlockTy) (body : List RawWInstr)
  | if_ (bt : WBlockTy) (thenBody : List RawWInstr) (elseBody : List RawWInstr)
  | global_set (idx : Nat)
  | leaf (instr : WInstr)
  deriving Inhabited

/-- Raw decoded WebAssembly function before normalization. -/
structure RawWFunc where
  name : Sym
  typeIdx : Nat
  locals : List WValTy := []
  body : List RawWInstr := []
  isExported : Bool := false
  deriving Inhabited

/-- Raw decoded WebAssembly module before normalization. -/
structure RawWModule where
  types : List WFuncTy := []
  funcs : List RawWFunc := []
  memory : Option WMemSpec := none
  globals : List WGlobalDecl := []
  dataSegs : List RawWDataSeg := []
  deriving Inhabited

/-! ## Extended Binary Section & Instruction Decoder -/

mutual
/-- Decode a raw instruction sequence until `0x0B` (`end`), or `0x05` (`else`) when
`stopOnElse` is true. -/
@[expose] def decodeRawInstrSeq (fuel : Nat) (stopOnElse : Bool) (r : Reader) :
    Except String (List RawWInstr × Bool × Reader) :=
  match fuel with
  | 0 => .error s!"decodeRawInstrSeq: fuel exhausted at offset {r.pos}"
  | fuel + 1 => do
    let (opByte, r1) ← r.readU8
    if opByte == 0x0B then
      .ok ([], false, r1)
    else if opByte == 0x05 then
      if stopOnElse then .ok ([], true, r1)
      else .error s!"unexpected 'else' opcode 0x05 at offset {r.pos}"
    else
      let (instr, r2) ← decodeOneRawInstr fuel opByte r1
      let (rest, endedElse, r3) ← decodeRawInstrSeq fuel stopOnElse r2
      .ok (instr :: rest, endedElse, r3)

/-- Decode one raw instruction (supporting `0x24 global.set` and rejecting
`call_indirect` / table ops). -/
@[expose] def decodeOneRawInstr (fuel : Nat) (opByte : UInt8) (r : Reader) :
    Except String (RawWInstr × Reader) :=
  match fuel with
  | 0 => .error s!"decodeOneRawInstr: fuel exhausted at offset {r.pos}"
  | fuel + 1 => do
    if let some instr := decodePureOp? opByte then return (.leaf instr, r)
    if let some (ty, w, sg) := decodeLoadOp? opByte then
      let (arg, r1) ← decodeMemArg r; return (.leaf (.load ty w sg arg), r1)
    if let some (ty, w) := decodeStoreOp? opByte then
      let (arg, r1) ← decodeMemArg r; return (.leaf (.store ty w arg), r1)
    match opByte with
    | 0x02 | 0x03 =>
      let (bt, r1) ← decodeBlockTy r
      let (body, endedElse, r2) ← decodeRawInstrSeq fuel false r1
      if endedElse then .error s!"structured block closed with 'else' at offset {r1.pos}"
      else .ok (if opByte == 0x02 then .block bt body else .loop bt body, r2)
    | 0x04 =>
      let (bt, r1) ← decodeBlockTy r
      let (thenBody, endedElse, r2) ← decodeRawInstrSeq fuel true r1
      if endedElse then
        let (elseBody, endedElse2, r3) ← decodeRawInstrSeq fuel false r2
        if endedElse2 then .error s!"nested 'else' inside else-branch at offset {r2.pos}"
        else .ok (.if_ bt thenBody elseBody, r3)
      else .ok (.if_ bt thenBody [], r2)
    | 0x0C => let (d, r1) ← decodeU32Nat r; .ok (.leaf (.br d), r1)
    | 0x0D => let (d, r1) ← decodeU32Nat r; .ok (.leaf (.br_if d), r1)
    | 0x0E =>
      let (cnt, r1) ← decodeU32 r
      let (targets, r2) ← decodeList (r1.remaining + 1) cnt.toNat decodeU32Nat r1
      let (defT, r3) ← decodeU32Nat r2; .ok (.leaf (.br_table targets defT), r3)
    | 0x10 => let (idx, r1) ← decodeU32Nat r; .ok (.leaf (.call idx), r1)
    | 0x11 => .error s!"call_indirect (0x11) unsupported at offset {r.pos}"
    | 0x20 => let (idx, r1) ← decodeU32Nat r; .ok (.leaf (.local_get idx), r1)
    | 0x21 => let (idx, r1) ← decodeU32Nat r; .ok (.leaf (.local_set idx), r1)
    | 0x22 => let (idx, r1) ← decodeU32Nat r; .ok (.leaf (.local_tee idx), r1)
    | 0x23 => let (idx, r1) ← decodeU32Nat r; .ok (.leaf (.global_get idx), r1)
    | 0x24 => let (idx, r1) ← decodeU32Nat r; .ok (.global_set idx, r1)
    | 0x3F => let r1 ← r.expectZero "memory.size"; .ok (.leaf .memory_size, r1)
    | 0x40 => let r1 ← r.expectZero "memory.grow"; .ok (.leaf .memory_grow, r1)
    | 0x41 => let (c, r1) ← decodeS32 r; .ok (.leaf (.i32_const c), r1)
    | 0x42 => let (c, r1) ← decodeS64 r; .ok (.leaf (.i64_const c), r1)
    | 0xFC =>
      let (subOp, r1) ← decodeU32 r
      match subOp.toNat with
      | 0x0A =>
        let r2 ← r1.expectZero "memory.copy[0]"; let r3 ← r2.expectZero "memory.copy[1]"
        .ok (.leaf .memory_copy, r3)
      | 0x0B => let r2 ← r1.expectZero "memory.fill"; .ok (.leaf .memory_fill, r2)
      | _ => .error s!"unsupported 0xFC prefix opcode {subOp} at offset {r.pos}"
    | _ => .error s!"unsupported WebAssembly opcode {opByte} at offset {r.pos}"
end

/-- Parse Import section (id 2): only `0` imports allowed. -/
@[expose] def decodeImportSectionEmpty (r : Reader) : Except String Unit := do
  let (count, r1) ← decodeU32 r
  if count != 0 then
    throw s!"imports unsupported in WebAssembly normalizer (got {count})"
  r1.ensureEmpty "import section"

/-- Parse Table section (id 4): allow at most 1 unused table (verified empty with `0`
elements and `0` `call_indirect`). -/
@[expose] def decodeTableSectionUnused (r : Reader) : Except String Unit := do
  let (count, cur) ← decodeU32 r
  if count > 1 then
    throw s!"multiple tables ({count}) unsupported in WebAssembly normalizer"
  let mut rCur := cur
  for _ in [0:count.toNat] do
    let (elemTy, rElem) ← rCur.readU8
    if elemTy != 0x70 && elemTy != 0x6F then
      throw s!"unsupported table element type {elemTy} at offset {rCur.pos}"
    let (flag, rMin) ← rElem.readU8
    let (_, rLim) ← decodeU32 rMin
    match flag with
    | 0x00 => rCur := rLim
    | 0x01 =>
      let (_, rMax) ← decodeU32 rLim
      rCur := rMax
    | _ => throw s!"invalid table limits flag {flag} at offset {rElem.pos}"
  rCur.ensureEmpty "table section"

/-- Parse Element section (id 9): only `0` element segments allowed. -/
@[expose] def decodeElemSectionEmpty (r : Reader) : Except String Unit := do
  let (count, r1) ← decodeU32 r
  if count != 0 then
    throw s!"non-empty element section ({count} segments) unsupported"
  r1.ensureEmpty "element section"

/-- Parse `i32.const` constant expression terminated by `0x0B`. -/
@[expose] def decodeConstI32Expr (r : Reader) : Except String (BitVec 32 × Reader) := do
  let (op, r1) ← r.readU8
  if op != 0x41 then
    throw s!"expected i32.const (0x41) in offset expr, got {op} at offset {r.pos}"
  let (val, r2) ← decodeS32 r1
  let (endB, r3) ← r2.readU8
  if endB != 0x0B then
    throw s!"expected 0x0B end in offset expr, got {endB} at offset {r2.pos}"
  .ok (val, r3)

/-- Parse Data section (id 11): active memory-0 segments with `i32.const` offsets. -/
@[expose] def decodeDataSection (r : Reader) : Except String (List RawWDataSeg) := do
  let (count, r1) ← decodeU32 r
  let mut segs : List RawWDataSeg := []
  let mut cur := r1
  for _ in [0:count.toNat] do
    let (mode, rMode) ← decodeU32Nat cur
    let rAfterMem ←
      if mode == 0 then
        pure rMode
      else if mode == 2 then
        let (memIdx, rMem) ← decodeU32Nat rMode
        if memIdx != 0 then
          throw s!"unsupported non-zero memory index {memIdx} in data segment"
        pure rMem
      else
        throw s!"unsupported data segment mode {mode} (only active memory 0 supported)"
    let (off, rOff) ← decodeConstI32Expr rAfterMem
    let (len, rLen) ← decodeU32Nat rOff
    let (payload, rNext) ← rLen.readBytes len
    segs := ⟨off, payload⟩ :: segs
    cur := rNext
  cur.ensureEmpty "data section"
  .ok segs.reverse

/-- Parse DataCount section (id 12): returns declared segment count. -/
@[expose] def decodeDataCountSection (r : Reader) : Except String Nat := do
  let (count, r1) ← decodeU32 r
  r1.ensureEmpty "datacount section"
  .ok count.toNat

/-- Parse Code section (id 10) into `RawWFunc` definitions. -/
@[expose] def decodeRawCodeSection (r : Reader) (fnCount : Nat) (typeIndices : List Nat)
    (fnNames : List (Nat × String)) : Except String (List RawWFunc) := do
  let (count, r1) ← decodeU32 r
  if count.toNat != fnCount then
    throw s!"function section count ({fnCount}) != code section count ({count})"
  let mut funcs : Array RawWFunc := Array.emptyWithCapacity fnCount
  let mut cur := r1
  for i in [0:fnCount] do
    let (bodySize, rBodySize) ← decodeU32 cur
    let (bodyBytes, rNext) ← rBodySize.readBytes bodySize.toNat
    cur := rNext
    let bodyReader : Reader := ⟨bodyBytes, 0⟩
    let (localDeclsCount, rLocCount) ← decodeU32 bodyReader
    if localDeclsCount.toNat > 65536 then
      throw s!"function {i} exceeds local declarations cap (65536)"
    let mut locals : Array WValTy := #[]
    let mut totalLocals : Nat := 0
    let mut curLoc := rLocCount
    for _ in [0:localDeclsCount.toNat] do
      let (locCnt, rNextCnt) ← decodeU32 curLoc
      let (locTy, rNextTy) ← decodeValTy rNextCnt
      if totalLocals + locCnt.toNat > 65536 then
        throw s!"function {i} exceeds locals cap (65536)"
      totalLocals := totalLocals + locCnt.toNat
      for _ in [0:locCnt.toNat] do
        locals := locals.push locTy
      curLoc := rNextTy
    let (body, endedElse, rEnd) ← decodeRawInstrSeq (bodyReader.remaining + 1) false curLoc
    if endedElse then throw s!"function {i} code body terminated with unexpected 'else'"
    rEnd.ensureEmpty s!"function {i} code body"
    let tIdx := typeIndices[i]?.getD 0
    let expName? := (fnNames.find? (·.1 == i)).map (·.2)
    let fnName := expName?.getD s!"wasm_fn_{i}"
    funcs := funcs.push ⟨fnName, tIdx, locals.toList, body, expName?.isSome⟩
  cur.ensureEmpty "code section"
  .ok funcs.toList

/-- WebAssembly binary section order rank (`1..9`, `12` DataCount, `10` Code, `11` Data). -/
@[expose] def wasmSectionRank (secId : UInt8) : Except String Nat :=
  match secId with
  | 1 => .ok 1
  | 2 => .ok 2
  | 3 => .ok 3
  | 4 => .ok 4
  | 5 => .ok 5
  | 6 => .ok 6
  | 7 => .ok 7
  | 8 => .error "start section (id 8) unsupported in WebAssembly normalizer"
  | 9 => .ok 9
  | 12 => .ok 10
  | 10 => .ok 11
  | 11 => .ok 12
  | _ => .error s!"unknown section id {secId}"

/-- Decode raw `.wasm` binary bytes into a `RawWModule` prior to AST normalization. -/
@[expose] def decodeRawWasmBytes (bs : ByteArray) : Except String RawWModule := do
  if bs.size < 8 then throw s!"binary too short ({bs.size} bytes < 8-byte wasm header)"
  if bs.extract 0 4 != ⟨#[0x00, 0x61, 0x73, 0x6D]⟩ then
    throw "invalid WebAssembly magic header (expected '\\0asm')"
  if bs.extract 4 8 != ⟨#[0x01, 0x00, 0x00, 0x00]⟩ then
    throw "unsupported WebAssembly binary version (expected version 1)"
  let mut cur : Reader := ⟨bs, 8⟩
  let mut lastRank : Nat := 0
  let mut types : List WFuncTy := []
  let mut typeIndices : List Nat := []
  let mut memory : Option WMemSpec := none
  let mut globals : List WGlobalDecl := []
  let mut fnExports : List (Nat × String) := []
  let mut funcs : List RawWFunc := []
  let mut dataSegs : List RawWDataSeg := []
  let mut dataCount? : Option Nat := none
  let mut seenCode : Bool := false
  let mut fuel := bs.size + 100
  while cur.pos < bs.size do
    if fuel == 0 then throw "section loop fuel exhausted"
    fuel := fuel - 1
    let (secId, r1) ← cur.readU8
    let (secLen, r2) ← decodeU32 r1
    let (secBytes, rNext) ← r2.readBytes secLen.toNat
    cur := rNext
    if secId == 0 then continue
    let rank ← wasmSectionRank secId
    if rank ≤ lastRank then
      throw s!"section {secId} out of order or duplicated"
    lastRank := rank
    let secReader : Reader := ⟨secBytes, 0⟩
    match secId with
    | 1 => types ← decodeTypeSection secReader
    | 2 => decodeImportSectionEmpty secReader
    | 3 => typeIndices ← decodeFuncSection secReader
    | 4 => decodeTableSectionUnused secReader
    | 5 => memory ← decodeMemorySection secReader
    | 6 => globals ← decodeGlobalSection secReader
    | 7 => fnExports ← decodeExportSection secReader
    | 9 => decodeElemSectionEmpty secReader
    | 12 => dataCount? ← some <$> decodeDataCountSection secReader
    | 10 =>
      funcs ← decodeRawCodeSection secReader typeIndices.length typeIndices fnExports
      seenCode := true
    | 11 => dataSegs ← decodeDataSection secReader
    | _ => throw s!"unexpected section id {secId}"
  if !typeIndices.isEmpty && !seenCode then
    throw "function section present without corresponding code section"
  if let some dc := dataCount? then
    if dc != dataSegs.length then
      throw s!"datacount mismatch ({dc} != {dataSegs.length})"
  .ok { types := types, funcs := funcs, memory := memory, globals := globals, dataSegs := dataSegs }

/-! ## AST Normalization Analysis & Helpers -/

/-- Global variable lowering target: kept immutable global or linear-memory slot. -/
inductive GlobalLoc where
  | imm (newIdx : Nat)
  | mem (addr : UInt32) (ty : WValTy)
  deriving DecidableEq, Repr, Inhabited

/-- Per-function statistics collected prior to single-pass AST rewriting. -/
structure FnNormStats where
  usesMutI32 : Bool := false
  usesMutI64 : Bool := false
  callsSpilled : Bool := false
  maxExtraI32 : Nat := 0
  maxExtraI64 : Nat := 0
  deriving Inhabited

/-- Count `(i32, i64)` items in a `WValTy` list. -/
@[expose] def countValTys : List WValTy → Nat × Nat
  | [] => (0, 0)
  | .i32 :: ts => let (n32, n64) := countValTys ts; (n32 + 1, n64)
  | .i64 :: ts => let (n32, n64) := countValTys ts; (n32, n64 + 1)

mutual
/-- Pre-scan raw instruction sequence to validate global/call indices and compute temp-local
requirements plus internally called function indices. -/
@[expose] def scanRawSeq (globals : Array WGlobalDecl) (fnParams : Array (List WValTy))
    (maxParams : Nat) : List RawWInstr → FnNormStats → Std.HashSet Nat →
    Except String (FnNormStats × Std.HashSet Nat)
  | [], st, called => .ok (st, called)
  | i :: rest, st, called => do
    let (st1, called1) ← scanRawInstr globals fnParams maxParams i st called
    scanRawSeq globals fnParams maxParams rest st1 called1

/-- Pre-scan one raw instruction. -/
@[expose] def scanRawInstr (globals : Array WGlobalDecl) (fnParams : Array (List WValTy))
    (maxParams : Nat) (instr : RawWInstr) (st : FnNormStats) (called : Std.HashSet Nat) :
    Except String (FnNormStats × Std.HashSet Nat) :=
  match instr with
  | .block _ body | .loop _ body => scanRawSeq globals fnParams maxParams body st called
  | .if_ _ tb eb => do
    let (st1, c1) ← scanRawSeq globals fnParams maxParams tb st called
    scanRawSeq globals fnParams maxParams eb st1 c1
  | .global_set idx =>
    match globals[idx]? with
    | none => .error s!"global.set index {idx} out of bounds"
    | some g =>
      if !g.mut_ then .error s!"global.set on immutable global {idx}"
      else
        let st' := match g.ty with
          | .i32 => { st with usesMutI32 := true }
          | .i64 => { st with usesMutI64 := true }
        .ok (st', called)
  | .leaf (.global_get idx) =>
    if idx < globals.size then .ok (st, called)
    else .error s!"global.get index {idx} out of bounds"
  | .leaf (.call fnIdx) =>
    match fnParams[fnIdx]? with
    | none => .error s!"call target index {fnIdx} out of bounds"
    | some ps =>
      let called' := called.insert fnIdx
      if ps.length ≤ maxParams then
        .ok (st, called')
      else
        let extra := ps.drop maxParams
        if extra.length > 65536 then
          .error s!"callee {fnIdx} exceeds extra spilled param cap"
        else
          let (n32, n64) := countValTys extra
          let st' :=
            { st with
              callsSpilled := true
              maxExtraI32 := max st.maxExtraI32 n32
              maxExtraI64 := max st.maxExtraI64 n64 }
          .ok (st', called')
  | .leaf _ => .ok (st, called)
end

/-- Read an unsigned 64-bit little-endian value from `bs` starting at `i`. -/
@[expose] def readU64LE (bs : ByteArray) (i : Nat) : BitVec 64 :=
  Id.run do
    let mut acc : Nat := 0
    for k in [0:8] do
      let b := if i + k < bs.size then bs[i + k]!.toNat else 0
      acc := acc ||| (b <<< (8 * k))
    return BitVec.ofNat 64 acc

/-- Read an unsigned 32-bit little-endian value from `bs` starting at `i`. -/
@[expose] def readU32LE (bs : ByteArray) (i : Nat) : BitVec 32 :=
  Id.run do
    let mut acc : Nat := 0
    for k in [0:4] do
      let b := if i + k < bs.size then bs[i + k]!.toNat else 0
      acc := acc ||| (b <<< (8 * k))
    return BitVec.ofNat 32 acc

/-- Emit packed little-endian stores (`i64.store`, tail `i32.store`, tail `i32.store8`) for one
data segment into reversed instruction accumulator `acc`. -/
@[expose] def emitDataSegRev (base : Nat) (bs : ByteArray) (i : Nat) (acc : List WInstr) :
    List WInstr :=
  if i + 8 ≤ bs.size then
    let addr := BitVec.ofNat 32 (base + i)
    let val := readU64LE bs i
    let align := if (base + i) % 8 == 0 then 3 else 0
    let acc1 :=
      .store .i64 .w64 { offset := 0, align := align } :: .i64_const val :: .i32_const addr :: acc
    emitDataSegRev base bs (i + 8) acc1
  else if i + 4 ≤ bs.size then
    let addr := BitVec.ofNat 32 (base + i)
    let val := readU32LE bs i
    let align := if (base + i) % 4 == 0 then 2 else 0
    let acc1 :=
      .store .i32 .w32 { offset := 0, align := align } :: .i32_const val :: .i32_const addr :: acc
    emitDataSegRev base bs (i + 4) acc1
  else if i < bs.size then
    let addr := BitVec.ofNat 32 (base + i)
    let val := BitVec.ofNat 32 bs[i]!.toNat
    let acc1 :=
      .store .i32 .w8 { offset := 0, align := 0 } :: .i32_const val :: .i32_const addr :: acc
    emitDataSegRev base bs (i + 1) acc1
  else
    acc
termination_by bs.size - i

/-- Build `__init_data` body: initialize active `Sec 11` data segments, mutable global memory
slots, optional shadow-stack pointer, and `initFlagSlot := 1`. -/
@[expose] def buildInitDataBody (dataSegs : List RawWDataSeg)
    (mutSlots : List (UInt32 × WValTy × BitVec 64)) (spInit? : Option (UInt32 × BitVec 32))
    (initFlagSlot : UInt32) : List WInstr :=
  Id.run do
    let mut acc : List WInstr := []
    for seg in dataSegs do
      acc := emitDataSegRev seg.offset.toNat seg.data 0 acc
    for (addr, ty, initVal) in mutSlots do
      let addr32 := BitVec.ofNat 32 addr.toNat
      match ty with
      | .i32 =>
        acc := .store .i32 .w32 { offset := 0, align := 2 } ::
          .i32_const (BitVec.ofNat 32 initVal.toNat) :: .i32_const addr32 :: acc
      | .i64 =>
        acc := .store .i64 .w64 { offset := 0, align := 3 } ::
          .i64_const initVal :: .i32_const addr32 :: acc
    if let some (spAddr, spVal) := spInit? then
      acc := .store .i32 .w32 { offset := 0, align := 2 } ::
        .i32_const spVal :: .i32_const (BitVec.ofNat 32 spAddr.toNat) :: acc
    acc := .store .i32 .w32 { offset := 0, align := 2 } ::
      .i32_const 1#32 :: .i32_const (BitVec.ofNat 32 initFlagSlot.toNat) :: acc
    return acc.reverse

/-- Intern a `WFuncTy` in `typesArr`, returning `(idx, typesArr')`. -/
@[expose] def internFuncTy (typesArr : Array WFuncTy) (ft : WFuncTy) : Nat × Array WFuncTy :=
  match typesArr.findIdx? (· == ft) with
  | some idx => (idx, typesArr)
  | none => (typesArr.size, typesArr.push ft)

/-- Pick a function name not colliding with `existingNames`. -/
@[expose] def pickFreshFnName (existing : List String) (base : String) : String :=
  if !existing.contains base then base
  else
    let rec go (fuel k : Nat) : String :=
      let cand := s!"{base}_{k}"
      if !existing.contains cand then cand
      else match fuel with
        | 0 => cand
        | f + 1 => go f (k + 1)
    go (existing.length + 1) 0

/-- Check half-open interval overlap `[a, a+aw)` vs `[b, b+bw)`. -/
@[expose] def intervalsOverlap (a aw b bw : Nat) : Bool :=
  a < b + bw && b < a + aw

/-- Validate and allocate global slots and shadow-stack configuration. -/
@[expose] def planGlobalsAndSlots (cfg : WNormConfig) (raw : RawWModule)
    (hasSpilledFn : Bool) : Except String
      (List WGlobalDecl × Array GlobalLoc × List (UInt32 × WValTy × BitVec 64) ×
       Option (UInt32 × BitVec 32) × Bool × Bool) := do
  let hasMutGlobals := raw.globals.any (·.mut_)
  let spCanShareG0 :=
    match raw.globals[0]? with
    | some g0 => g0.mut_ && g0.ty == .i32 && (!hasSpilledFn || g0.init.toNat ≥ 1024)
    | none => false
  let needSpSlot := hasSpilledFn || spCanShareG0
  let needInit := !raw.dataSegs.isEmpty || hasMutGlobals || hasSpilledFn
  if needInit && raw.memory.isNone then
    throw "normalizeRawModule: linear memory section required for normalization"
  let mut immGlobals : Array WGlobalDecl := #[]
  let mut locs : Array GlobalLoc := Array.emptyWithCapacity raw.globals.length
  let mut mutSlots : Array (UInt32 × WValTy × BitVec 64) := #[]
  let mut extraCursor : Nat :=
    ((min cfg.spSlot.toNat cfg.initFlagSlot.toNat) / 8) * 8
  for (g, gIdx) in raw.globals.zipIdx do
    if !g.mut_ then
      locs := locs.push (.imm immGlobals.size)
      immGlobals := immGlobals.push g
    else if gIdx == 0 && spCanShareG0 then
      locs := locs.push (.mem cfg.spSlot .i32)
      mutSlots := mutSlots.push (cfg.spSlot, .i32, g.init)
    else
      if extraCursor < 8 then
        throw "normalizeRawModule: exhausted null-guard slot space for mutable globals"
      extraCursor := extraCursor - 8
      let addr := UInt32.ofNat extraCursor
      locs := locs.push (.mem addr g.ty)
      mutSlots := mutSlots.push (addr, g.ty, g.init)
  let spInit? ←
    if hasSpilledFn && !spCanShareG0 then
      let initPages := (raw.memory.map (·.initPages)).getD 0
      if initPages == 0 then
        throw "normalizeRawModule: memory initPages >= 1 required for shadow stack"
      let spNat := min (initPages * 65536) 0xFFFFFFF0
      pure (some (cfg.spSlot, BitVec.ofNat 32 spNat))
    else
      pure none
  -- Check interval bounds & non-overlap among reserved slots and data segments
  let mut intervals : List (Nat × Nat) := []
  if needInit then
    intervals := (cfg.initFlagSlot.toNat, 4) :: intervals
  if needSpSlot then
    intervals := (cfg.spSlot.toNat, 4) :: intervals
  for (addr, ty, _) in mutSlots do
    if !(addr == cfg.spSlot && needSpSlot) then
      intervals := (addr.toNat, ty.bitWidth / 8) :: intervals
  for (s, w) in intervals do
    if s + w > 2 ^ 32 then
      throw s!"normalizeRawModule: slot {s} overflows 32-bit address space"
  let revInts := intervals.reverse
  for i in [0:revInts.length] do
    let (s1, w1) := revInts[i]!
    for j in [i + 1:revInts.length] do
      let (s2, w2) := revInts[j]!
      if intervalsOverlap s1 w1 s2 w2 then
        throw s!"normalizeRawModule: overlapping slot addresses {s1} and {s2}"
  for seg in raw.dataSegs do
    let base := seg.offset.toNat
    let len := seg.data.size
    if base + len > 2 ^ 32 then
      throw s!"normalizeRawModule: data segment at {base} overflows 32-bit address space"
    for (s, w) in intervals do
      if intervalsOverlap base len s w then
        throw s!"normalizeRawModule: data segment [{base}, {base + len}) overlaps slot {s}"
  .ok (immGlobals.toList, locs, mutSlots.toList, spInit?, spCanShareG0, needInit)

/-! ## AST Rewriting (Mutable Globals & Call/Callee Spill) -/

/-- Context for rewriting one function body. -/
structure FnRewriteCtx where
  cfg : WNormConfig
  rawTypes : Array WFuncTy
  fnParams : Array (List WValTy)
  globalLocs : Array GlobalLoc
  fnShift : Nat
  spTmpIdx : Nat
  i64GlobTmpIdx : Nat
  i32ArgBase : Nat
  i64ArgBase : Nat
  deriving Inhabited

/-- Emit spilled caller sequence for `.call callee` when `calleeParams.length > maxParams`. -/
@[expose] def emitSpilledCall (ctx : FnRewriteCtx) (callee : Nat) (extra : List WValTy)
    (acc : Array WInstr) : Array WInstr := Id.run do
  let frameBytes := ((8 * extra.length + 15) / 16) * 16
  let mut i32C := 0
  let mut i64C := 0
  let mut slots : Array (WValTy × Nat) := Array.emptyWithCapacity extra.length
  for vt in extra do
    match vt with
    | .i32 =>
      slots := slots.push (.i32, ctx.i32ArgBase + i32C)
      i32C := i32C + 1
    | .i64 =>
      slots := slots.push (.i64, ctx.i64ArgBase + i64C)
      i64C := i64C + 1
  let mut out := acc
  for (_, lidx) in slots.reverse do
    out := out.push (.local_set lidx)
  let spAddr32 := BitVec.ofNat 32 ctx.cfg.spSlot.toNat
  out := out.push (.i32_const spAddr32)
  out := out.push (.i32_const spAddr32)
  out := out.push (.load .i32 .w32 false { offset := 0, align := 2 })
  out := out.push (.i32_const (BitVec.ofNat 32 frameBytes))
  out := out.push (.binop .i32 .sub)
  out := out.push (.local_tee ctx.spTmpIdx)
  out := out.push (.store .i32 .w32 { offset := 0, align := 2 })
  for j in [0:slots.size] do
    let (vt, lidx) := slots[j]!
    let off := UInt32.ofNat (8 * j)
    out := out.push (.local_get ctx.spTmpIdx)
    out := out.push (.local_get lidx)
    out := out.push <| match vt with
      | .i32 => .store .i32 .w32 { offset := off, align := 2 }
      | .i64 => .store .i64 .w64 { offset := off, align := 3 }
  out := out.push (.call (callee + ctx.fnShift))
  out := out.push (.i32_const spAddr32)
  out := out.push (.local_get ctx.spTmpIdx)
  out := out.push (.i32_const (BitVec.ofNat 32 frameBytes))
  out := out.push (.binop .i32 .add)
  out := out.push (.store .i32 .w32 { offset := 0, align := 2 })
  return out

/-- Remap a `WBlockTy` against `rawTypes` and intern into `typesArr`. -/
@[expose] def remapBlockTy (rawTypes : Array WFuncTy) (typesArr : Array WFuncTy) :
    WBlockTy → Except String (WBlockTy × Array WFuncTy)
  | .empty => .ok (.empty, typesArr)
  | .val t => .ok (.val t, typesArr)
  | .inline ft => .ok (.inline ft, typesArr)
  | .func idx =>
    match rawTypes[idx]? with
    | none => .error s!"invalid block type index {idx}"
    | some ft =>
      let (newIdx, typesArr') := internFuncTy typesArr ft
      .ok (.func newIdx, typesArr')

mutual
/-- Rewrite a sequence of raw instructions into `acc`, threading `typesArr`. -/
@[expose] def rewriteRawSeq (ctx : FnRewriteCtx) :
    List RawWInstr → Array WInstr → Array WFuncTy →
    Except String (Array WInstr × Array WFuncTy)
  | [], acc, typesArr => .ok (acc, typesArr)
  | i :: rest, acc, typesArr => do
    let (acc1, types1) ← rewriteRawInstr ctx i acc typesArr
    rewriteRawSeq ctx rest acc1 types1

/-- Rewrite one raw instruction into `acc`, threading `typesArr`. -/
@[expose] def rewriteRawInstr (ctx : FnRewriteCtx) (instr : RawWInstr)
    (acc : Array WInstr) (typesArr : Array WFuncTy) :
    Except String (Array WInstr × Array WFuncTy) :=
  match instr with
  | .block bt body => do
    let (bt', types1) ← remapBlockTy ctx.rawTypes typesArr bt
    let (bodyArr, types2) ← rewriteRawSeq ctx body #[] types1
    .ok (acc.push (.block bt' bodyArr.toList), types2)
  | .loop bt body => do
    let (bt', types1) ← remapBlockTy ctx.rawTypes typesArr bt
    let (bodyArr, types2) ← rewriteRawSeq ctx body #[] types1
    .ok (acc.push (.loop bt' bodyArr.toList), types2)
  | .if_ bt tb eb => do
    let (bt', types1) ← remapBlockTy ctx.rawTypes typesArr bt
    let (tbArr, types2) ← rewriteRawSeq ctx tb #[] types1
    let (ebArr, types3) ← rewriteRawSeq ctx eb #[] types2
    .ok (acc.push (.if_ bt' tbArr.toList ebArr.toList), types3)
  | .global_set idx =>
    match ctx.globalLocs[idx]? with
    | some (.mem addr ty) =>
      let addr32 := BitVec.ofNat 32 addr.toNat
      let out := match ty with
        | .i32 =>
          acc.push (.local_set ctx.spTmpIdx)
            |>.push (.i32_const addr32)
            |>.push (.local_get ctx.spTmpIdx)
            |>.push (.store .i32 .w32 { offset := 0, align := 2 })
        | .i64 =>
          acc.push (.local_set ctx.i64GlobTmpIdx)
            |>.push (.i32_const addr32)
            |>.push (.local_get ctx.i64GlobTmpIdx)
            |>.push (.store .i64 .w64 { offset := 0, align := 3 })
      .ok (out, typesArr)
    | _ => .error s!"global.set on non-memory global {idx}"
  | .leaf (.global_get idx) =>
    match ctx.globalLocs[idx]? with
    | some (.imm newIdx) => .ok (acc.push (.global_get newIdx), typesArr)
    | some (.mem addr ty) =>
      let addr32 := BitVec.ofNat 32 addr.toNat
      let ld := match ty with
        | .i32 => WInstr.load .i32 .w32 false { offset := 0, align := 2 }
        | .i64 => WInstr.load .i64 .w64 false { offset := 0, align := 3 }
      .ok (acc.push (.i32_const addr32) |>.push ld, typesArr)
    | none => .error s!"global.get index {idx} out of bounds"
  | .leaf (.call callee) =>
    match ctx.fnParams[callee]? with
    | none => .error s!"call target index {callee} out of bounds"
    | some cParams =>
      if cParams.length ≤ ctx.cfg.maxParams then
        .ok (acc.push (.call (callee + ctx.fnShift)), typesArr)
      else
        .ok (emitSpilledCall ctx callee (cParams.drop ctx.cfg.maxParams) acc, typesArr)
  | .leaf other => .ok (acc.push other, typesArr)
end

/-- Normalize a single raw function body and local declarations. -/
@[expose] def normalizeOneFunc (cfg : WNormConfig) (rawTypes : Array WFuncTy)
    (fnParams : Array (List WValTy)) (globalLocs : Array GlobalLoc)
    (calledFns : Std.HashSet Nat) (spResetVal? : Option (BitVec 32))
    (needInit : Bool) (fnShift : Nat) (fnIdx : Nat) (f : RawWFunc)
    (newTypeIdx : Nat) (stats : FnNormStats) (typesArr : Array WFuncTy) :
    Except String (WFunc × Array WFuncTy) := do
  let origParams := fnParams[fnIdx]!
  let k := origParams.length
  let spilledParams := origParams.drop cfg.maxParams
  let extraBase := min k cfg.maxParams
  let tempBase := k + f.locals.length
  let needSpTmp := !spilledParams.isEmpty || stats.callsSpilled || stats.usesMutI32
  let needI64GlobTmp := stats.usesMutI64
  let spTmpIdx := tempBase
  let i64GlobTmpIdx := tempBase + (if needSpTmp then 1 else 0)
  let i32ArgBase := i64GlobTmpIdx + (if needI64GlobTmp then 1 else 0)
  let i64ArgBase := i32ArgBase + stats.maxExtraI32
  let extraTempLocals : List WValTy :=
    (if needSpTmp then [.i32] else []) ++
    (if needI64GlobTmp then [.i64] else []) ++
    List.replicate stats.maxExtraI32 .i32 ++
    List.replicate stats.maxExtraI64 .i64
  let newLocals := spilledParams ++ f.locals ++ extraTempLocals
  let mut entryPrefix : Array WInstr := #[]
  if needInit && f.isExported then
    entryPrefix := entryPrefix.push (.block .empty
      [ .i32_const (BitVec.ofNat 32 cfg.initFlagSlot.toNat)
      , .load .i32 .w32 false { offset := 0, align := 2 }
      , .br_if 0
      , .call 0
      ])
  if cfg.resetSpOnExportedEntry && f.isExported && !calledFns.contains fnIdx &&
      spilledParams.isEmpty then
    if let some spVal := spResetVal? then
      entryPrefix := entryPrefix.push (.i32_const (BitVec.ofNat 32 cfg.spSlot.toNat))
      entryPrefix := entryPrefix.push (.i32_const spVal)
      entryPrefix := entryPrefix.push (.store .i32 .w32 { offset := 0, align := 2 })
  if !spilledParams.isEmpty then
    entryPrefix := entryPrefix.push (.i32_const (BitVec.ofNat 32 cfg.spSlot.toNat))
    entryPrefix := entryPrefix.push (.load .i32 .w32 false { offset := 0, align := 2 })
    entryPrefix := entryPrefix.push (.local_set spTmpIdx)
    for j in [0:spilledParams.length] do
      let vt := spilledParams[j]!
      let off := UInt32.ofNat (8 * j)
      entryPrefix := entryPrefix.push (.local_get spTmpIdx)
      entryPrefix := entryPrefix.push <| match vt with
        | .i32 => .load .i32 .w32 false { offset := off, align := 2 }
        | .i64 => .load .i64 .w64 false { offset := off, align := 3 }
      entryPrefix := entryPrefix.push (.local_set (extraBase + j))
  let ctx : FnRewriteCtx :=
    { cfg, rawTypes, fnParams, globalLocs, fnShift,
      spTmpIdx, i64GlobTmpIdx, i32ArgBase, i64ArgBase }
  let (bodyArr, typesArr') ← rewriteRawSeq ctx f.body entryPrefix typesArr
  .ok ({ name := f.name, typeIdx := newTypeIdx, locals := newLocals, body := bodyArr.toList },
       typesArr')

/-! ## Top-Level AST Normalizer & Verified Lowering Bridge -/

/-- Transform a decoded `RawWModule` into a core `WModule` with `0` mutable globals,
`0` data segments, and all functions having `≤ cfg.maxParams` parameters. -/
@[expose] def normalizeRawModule (cfg : WNormConfig := {}) (raw : RawWModule) :
    Except String WModule := do
  if cfg.maxParams > maxWasmParams then
    throw s!"normalizeRawModule: maxParams {cfg.maxParams} exceeds maxWasmParams {maxWasmParams}"
  let rawTypes := raw.types.toArray
  let rawGlobals := raw.globals.toArray
  let mut fnParamsArr : Array (List WValTy) := Array.emptyWithCapacity raw.funcs.length
  let mut hasSpilledFn := false
  for (f, i) in raw.funcs.zipIdx do
    match rawTypes[f.typeIdx]? with
    | none => throw s!"normalizeRawModule: function {i} invalid typeIdx {f.typeIdx}"
    | some ft =>
      if ft.params.length > cfg.maxParams then hasSpilledFn := true
      fnParamsArr := fnParamsArr.push ft.params
  let mut statsArr : Array FnNormStats := Array.emptyWithCapacity raw.funcs.length
  let mut calledFns : Std.HashSet Nat := {}
  for f in raw.funcs do
    let (st, called') ← scanRawSeq rawGlobals fnParamsArr cfg.maxParams f.body {} calledFns
    statsArr := statsArr.push st
    calledFns := called'
  let (immGlobals, globalLocs, mutSlots, spInit?, spCanShareG0, needInit) ←
    planGlobalsAndSlots cfg raw hasSpilledFn
  let fnShift := if needInit then 1 else 0
  let mut typesArr : Array WFuncTy := #[]
  let mut initTypeIdx : Nat := 0
  if needInit then
    let (idx, t') := internFuncTy typesArr { params := [], results := [] }
    initTypeIdx := idx
    typesArr := t'
  let mut fnNewTypeIdxs : Array Nat := Array.emptyWithCapacity raw.funcs.length
  for f in raw.funcs do
    let origFt := rawTypes[f.typeIdx]!
    let truncFt : WFuncTy :=
      { params := origFt.params.take cfg.maxParams, results := origFt.results }
    let (ti, t') := internFuncTy typesArr truncFt
    fnNewTypeIdxs := fnNewTypeIdxs.push ti
    typesArr := t'
  let spResetVal? : Option (BitVec 32) :=
    if spCanShareG0 then some (BitVec.ofNat 32 rawGlobals[0]!.init.toNat) else none
  let mut outFuncs : Array WFunc := Array.emptyWithCapacity (raw.funcs.length + fnShift)
  if needInit then
    let initName := pickFreshFnName (raw.funcs.map (·.name)) cfg.initFnName
    let initBody := buildInitDataBody raw.dataSegs mutSlots spInit? cfg.initFlagSlot
    outFuncs := outFuncs.push
      { name := initName, typeIdx := initTypeIdx, locals := [], body := initBody }
  for (f, i) in raw.funcs.zipIdx do
    let (wf, t') ← normalizeOneFunc cfg rawTypes fnParamsArr globalLocs calledFns
      spResetVal? needInit fnShift i f fnNewTypeIdxs[i]! statsArr[i]! typesArr
    typesArr := t'
    outFuncs := outFuncs.push wf
  .ok { types := typesArr.toList, funcs := outFuncs.toList,
        memory := raw.memory, globals := immGlobals }

/-- Decode raw `.wasm` binary bytes and normalize into a core `WModule`. -/
@[expose] def decodeNormalizeWasm (cfg : WNormConfig := {}) (bs : ByteArray) :
    Except String WModule := do
  let raw ← decodeRawWasmBytes bs
  normalizeRawModule cfg raw

/-- Decode raw `.wasm` binary bytes, normalize to core `WModule`, validate via
`validateModule`, and lower into a verified `LeanQbe.T.Module`. -/
@[expose] def decodeNormalizeAndLowerWasm (cfg : WNormConfig := {}) (bs : ByteArray) :
    Except String (WModule × Module) :=
  match decodeNormalizeWasm cfg bs with
  | .error e => .error e
  | .ok wm =>
    if validateModule wm then
      .ok (wm, lowerModule wm)
    else
      .error "decodeNormalizeAndLowerWasm: module validation failed"

/-- Soundness bridge: any module accepted by `decodeNormalizeAndLowerWasm` satisfies
`validateModule wm = true` and `mod = lowerModule wm`, connecting directly to
`wasm_preserves_host_mem` and `lowerModule_semScc`. -/
theorem decodeNormalizeAndLowerWasm_ok {cfg : WNormConfig} {bs : ByteArray}
    {wm : WModule} {mod : Module}
    (h : decodeNormalizeAndLowerWasm cfg bs = .ok (wm, mod)) :
    validateModule wm = true ∧ mod = lowerModule wm := by
  simp only [decodeNormalizeAndLowerWasm] at h
  cases hdec : decodeNormalizeWasm cfg bs <;> simp_all
  split at h <;> simp_all
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- Universal `Env.semScc` soundness corollary for normalized WebAssembly binaries. -/
theorem decodeNormalizeAndLowerWasm_semScc {cfg : WNormConfig} {bs : ByteArray}
    {wm : WModule} {mod : Module}
    (h : decodeNormalizeAndLowerWasm cfg bs = .ok (wm, mod)) (Γext : Env) :
    ∀ i, Env.le (Env.restrict (WasmSandboxEnv wm i) (mod.fns.map Fn.sig))
      (Env.semScc mod Γext) := by
  obtain ⟨hv, rfl⟩ := decodeNormalizeAndLowerWasm_ok h
  exact lowerModule_semScc hv Γext

end LeanQbe.T.Wasm
