module

public import LeanQbe.T.Wasm.Ast
public import LeanQbe.T.Wasm.Validate
public import LeanQbe.T.Wasm.Lower
public import LeanQbe.T.Wasm.Safety

/-!
# WebAssembly 1.0/2.0 Binary Format Decoder (`LeanQbe.T.Wasm.Decode`)

Provides a pure, total, verified-sandbox WebAssembly binary format decoder:
* `decodeWasmBytes : ByteArray → Except String WModule`:
  Decodes standard `.wasm` binaries (magic `\0asm`, version 1, strict LEB128 unsigned/signed
  integers with bounded recursion and overlong/truncation rejection, standard sections in
  order, ignoring custom section 0, structured instruction control trees).
* `decodeAndLowerWasm : ByteArray → Except String (WModule × Module)`:
  Decodes, validates (`validateModule m = true`), and lowers into `LeanQbe.T.Module`.
* `decodeAndLowerWasm_semScc`:
  Universal host-memory preservation and sandbox isolation theorem for decoded binaries.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Wasm

open LeanQbe.T

/-! ## Reader State & Strict LEB128 Decoders -/

/-- Immutable byte slice reader cursor. -/
structure Reader where
  bytes : ByteArray
  pos : Nat := 0
  deriving Inhabited

/-- Remaining unread byte count. -/
@[reducible] def Reader.remaining (r : Reader) : Nat :=
  r.bytes.size - r.pos

/-- Read a single byte from the stream. -/
def Reader.readU8 (r : Reader) : Except String (UInt8 × Reader) :=
  if r.pos < r.bytes.size then
    .ok (r.bytes.get! r.pos, { r with pos := r.pos + 1 })
  else
    .error s!"unexpected EOF at offset {r.pos}"

/-- Read `len` bytes from the stream. -/
def Reader.readBytes (r : Reader) (len : Nat) : Except String (ByteArray × Reader) :=
  if r.pos + len ≤ r.bytes.size then
    .ok (r.bytes.extract r.pos (r.pos + len), { r with pos := r.pos + len })
  else
    .error s!"unexpected EOF reading {len} bytes at offset {r.pos}"

/-- Ensure no unread bytes remain in `r`. -/
def Reader.ensureEmpty (what : String) (r : Reader) : Except String Unit :=
  if r.remaining != 0 then .error s!"trailing {r.remaining} bytes in {what}" else .ok ()

/-- Consume an expected trailing `0x00` byte. -/
def Reader.expectZero (what : String) (r : Reader) : Except String Reader := do
  let (b, r') ← r.readU8
  if b == 0 then .ok r'
  else .error s!"{what} expected trailing 0x00, got {b} at offset {r.pos}"

/-- Strict bounded unsigned LEB128 decoder with overlong rejection. -/
def decodeULeb (maxBytes lastMask : Nat) (label : String) (r : Reader) :
    Except String (Nat × Reader) := do
  let mut res : Nat := 0
  let mut shift : Nat := 0
  let mut cur := r
  for i in [0:maxBytes] do
    let (b, next) ← cur.readU8
    cur := next
    let valBits := (b.toNat &&& 0x7F)
    if i == maxBytes - 1 then
      if (b.toNat &&& lastMask) != 0 then
        return ← .error s!"overlong {label} LEB128 at offset {cur.pos - 1}"
      if (b.toNat &&& 0x80) != 0 then
        return ← .error s!"{label} LEB128 exceeds {maxBytes} bytes at offset {cur.pos - 1}"
    res := res ||| (valBits <<< shift)
    if (b.toNat &&& 0x80) == 0 then
      return (res, cur)
    shift := shift + 7
  .error s!"{label} LEB128 overflow at offset {cur.pos}"

/-- Strict unsigned 32-bit LEB128 decoder with overlong rejection (at most 5 bytes). -/
def decodeU32 (r : Reader) : Except String (UInt32 × Reader) :=
  Prod.map UInt32.ofNat id <$> decodeULeb 5 0x70 "u32" r

/-- Decode an unsigned 32-bit LEB128 integer directly as `Nat`. -/
@[reducible] def decodeU32Nat (r : Reader) : Except String (Nat × Reader) :=
  Prod.map UInt32.toNat id <$> decodeU32 r

/-- Strict unsigned 64-bit LEB128 decoder with overlong rejection (at most 10 bytes). -/
def decodeU64 (r : Reader) : Except String (UInt64 × Reader) :=
  Prod.map UInt64.ofNat id <$> decodeULeb 10 0x7E "u64" r

/-- Strict bounded signed LEB128 decoder with overlong and sign-extension verification. -/
def decodeSLeb (maxBytes signMask padMask : Nat) (label : String) (r : Reader) :
    Except String (Int × Reader) := do
  let mut res : Nat := 0
  let mut shift : Nat := 0
  let mut cur := r
  for i in [0:maxBytes] do
    let (b, next) ← cur.readU8
    cur := next
    res := res ||| ((b.toNat &&& 0x7F) <<< shift)
    shift := shift + 7
    if (b.toNat &&& 0x80) == 0 then
      if i == maxBytes - 1 then
        let signBit := (b.toNat &&& signMask) != 0
        let padBits := b.toNat &&& padMask
        if signBit && padBits != padMask then
          return ← .error s!"invalid signed {label} sign padding at offset {cur.pos - 1}"
        if !signBit && padBits != 0 then
          return ← .error s!"invalid signed {label} zero padding at offset {cur.pos - 1}"
      let val : Int :=
        if (b.toNat &&& 0x40) != 0 then (res : Int) - ((1 : Int) <<< shift) else res
      return (val, cur)
  .error s!"{label} LEB128 overflow at offset {cur.pos}"

/-- Strict signed 32-bit LEB128 decoder with overlong and sign-extension verification. -/
def decodeS32 (r : Reader) : Except String (BitVec 32 × Reader) :=
  Prod.map (BitVec.ofInt 32) id <$> decodeSLeb 5 0x08 0x70 "s32" r

/-- Strict signed 64-bit LEB128 decoder with overlong and sign-extension verification. -/
def decodeS64 (r : Reader) : Except String (BitVec 64 × Reader) :=
  Prod.map (BitVec.ofInt 64) id <$> decodeSLeb 10 0x01 0x7E "s64" r

/-- Signed 33-bit LEB128 decoder for block type indices. -/
def decodeS33 (r : Reader) : Except String (Int × Reader) :=
  decodeSLeb 5 0x10 0x60 "s33" r

/-- Decode a list of `cnt` elements using element decoder `dec`. -/
def decodeList {α : Type} (fuel : Nat) (cnt : Nat)
    (dec : Reader → Except String (α × Reader)) (r : Reader) :
    Except String (List α × Reader) := do
  match cnt with
  | 0 => .ok ([], r)
  | n + 1 =>
    if fuel == 0 then
      .error s!"decodeList: fuel exhausted at offset {r.pos}"
    else
      let (x, r1) ← dec r
      let (xs, r2) ← decodeList (fuel - 1) n dec r1
      .ok (x :: xs, r2)

/-! ## Value and Block Type Decoders -/

/-- Decode a single scalar value type (`0x7F` -> `i32`, `0x7E` -> `i64`). -/
def decodeValTy (r : Reader) : Except String (WValTy × Reader) := do
  let (b, r') ← r.readU8
  match b with
  | 0x7F => .ok (.i32, r')
  | 0x7E => .ok (.i64, r')
  | _ => .error s!"unsupported value type {b} at offset {r.pos}"

/-- Decode structured block type (`0x40` empty, `0x7F` i32, `0x7E` i64, or s33 type index). -/
def decodeBlockTy (r : Reader) : Except String (WBlockTy × Reader) := do
  let (v, r1) ← decodeS33 r
  if v == -64 then
    return (.empty, r1)
  else if v == -1 then
    return (.val .i32, r1)
  else if v == -2 then
    return (.val .i64, r1)
  else if v ≥ 0 then
    return (.func v.toNat, r1)
  else
    .error s!"invalid block type {v} at offset {r.pos}"

/-- Decode a static memory immediate operand `align:u32, offset:u32`. -/
def decodeMemArg (r : Reader) : Except String (WMemArg × Reader) := do
  let (align, r1) ← decodeU32 r
  let (offset, r2) ← decodeU32 r1
  return (⟨offset, align.toNat⟩, r2)

/-! ## Opcode Lookup Tables & Instruction Decoder -/

def relOpTable : Array WRelOp :=
  #[.eq, .ne, .lt_s, .lt_u, .gt_s, .gt_u, .le_s, .le_u, .ge_s, .ge_u]

def binOpTable : Array WBinOp :=
  #[.add, .sub, .mul, .div_s, .div_u, .rem_s, .rem_u, .and, .or, .xor,
    .shl, .shr_s, .shr_u, .rotl, .rotr]

def decodeLoadOp? : UInt8 → Option (WValTy × WMemWidth × Bool)
  | 0x28 => some (.i32, .w32, false)
  | 0x29 => some (.i64, .w64, false)
  | 0x2C => some (.i32, .w8, true)
  | 0x2D => some (.i32, .w8, false)
  | 0x2E => some (.i32, .w16, true)
  | 0x2F => some (.i32, .w16, false)
  | 0x30 => some (.i64, .w8, true)
  | 0x31 => some (.i64, .w8, false)
  | 0x32 => some (.i64, .w16, true)
  | 0x33 => some (.i64, .w16, false)
  | 0x34 => some (.i64, .w32, true)
  | 0x35 => some (.i64, .w32, false)
  | _ => none

def decodeStoreOp? : UInt8 → Option (WValTy × WMemWidth)
  | 0x36 => some (.i32, .w32)
  | 0x37 => some (.i64, .w64)
  | 0x3A => some (.i32, .w8)
  | 0x3B => some (.i32, .w16)
  | 0x3C => some (.i64, .w8)
  | 0x3D => some (.i64, .w16)
  | 0x3E => some (.i64, .w32)
  | _ => none

def decodePureOp? (opByte : UInt8) : Option WInstr :=
  let b := opByte.toNat
  if 0x46 ≤ b && b ≤ 0x4F then relOpTable[b - 0x46]?.map (.relop .i32)
  else if 0x51 ≤ b && b ≤ 0x5A then relOpTable[b - 0x51]?.map (.relop .i64)
  else if 0x6A ≤ b && b ≤ 0x78 then binOpTable[b - 0x6A]?.map (.binop .i32)
  else if 0x7C ≤ b && b ≤ 0x8A then binOpTable[b - 0x7C]?.map (.binop .i64)
  else match opByte with
    | 0x00 => some .unreachable
    | 0x01 => some .nop
    | 0x0F => some .return_
    | 0x1A => some .drop
    | 0x1B => some .select
    | 0x45 => some (.eqz .i32)
    | 0x50 => some (.eqz .i64)
    | 0x67 => some (.unop .i32 .clz)
    | 0x68 => some (.unop .i32 .ctz)
    | 0x69 => some (.unop .i32 .popcnt)
    | 0x79 => some (.unop .i64 .clz)
    | 0x7A => some (.unop .i64 .ctz)
    | 0x7B => some (.unop .i64 .popcnt)
    | 0xA7 => some .wrap_i64
    | 0xAC => some .extend_i32_s
    | 0xAD => some .extend_i32_u
    | 0xC0 => some (.unop .i32 .extend8_s)
    | 0xC1 => some (.unop .i32 .extend16_s)
    | 0xC2 => some (.unop .i64 .extend8_s)
    | 0xC3 => some (.unop .i64 .extend16_s)
    | 0xC4 => some (.unop .i64 .extend32_s)
    | _ => none

mutual
/-- Decode a sequence of instructions until `0x0B` (`end`), or `0x05` (`else`) when
`stopOnElse` is true. Returns the instruction list, whether it ended on `else` (true) vs
`end` (false), and the updated reader. -/
def decodeInstrSeq (fuel : Nat) (stopOnElse : Bool) (r : Reader) :
    Except String (List WInstr × Bool × Reader) :=
  match fuel with
  | 0 => .error s!"decodeInstrSeq: fuel exhausted at offset {r.pos}"
  | fuel + 1 => do
    let (opByte, r1) ← r.readU8
    if opByte == 0x0B then
      .ok ([], false, r1)
    else if opByte == 0x05 then
      if stopOnElse then .ok ([], true, r1)
      else .error s!"unexpected 'else' opcode 0x05 at offset {r.pos}"
    else
      let (instr, r2) ← decodeOneInstr fuel opByte r1
      let (rest, endedElse, r3) ← decodeInstrSeq fuel stopOnElse r2
      .ok (instr :: rest, endedElse, r3)

/-- Decode one instruction whose initial opcode byte is `opByte`. -/
def decodeOneInstr (fuel : Nat) (opByte : UInt8) (r : Reader) :
    Except String (WInstr × Reader) :=
  match fuel with
  | 0 => .error s!"decodeOneInstr: fuel exhausted at offset {r.pos}"
  | fuel + 1 => do
    if let some instr := decodePureOp? opByte then return (instr, r)
    if let some (ty, w, sg) := decodeLoadOp? opByte then
      let (arg, r1) ← decodeMemArg r; return (.load ty w sg arg, r1)
    if let some (ty, w) := decodeStoreOp? opByte then
      let (arg, r1) ← decodeMemArg r; return (.store ty w arg, r1)
    match opByte with
    | 0x02 | 0x03 =>
      let (bt, r1) ← decodeBlockTy r
      let (body, endedElse, r2) ← decodeInstrSeq fuel false r1
      if endedElse then .error s!"structured block closed with 'else' at offset {r1.pos}"
      else .ok (if opByte == 0x02 then .block bt body else .loop bt body, r2)
    | 0x04 =>
      let (bt, r1) ← decodeBlockTy r
      let (thenBody, endedElse, r2) ← decodeInstrSeq fuel true r1
      if endedElse then
        let (elseBody, endedElse2, r3) ← decodeInstrSeq fuel false r2
        if endedElse2 then .error s!"nested 'else' inside else-branch at offset {r2.pos}"
        else .ok (.if_ bt thenBody elseBody, r3)
      else .ok (.if_ bt thenBody [], r2)
    | 0x0C => let (d, r1) ← decodeU32Nat r; .ok (.br d, r1)
    | 0x0D => let (d, r1) ← decodeU32Nat r; .ok (.br_if d, r1)
    | 0x0E =>
      let (cnt, r1) ← decodeU32 r
      let (targets, r2) ← decodeList (r1.remaining + 1) cnt.toNat decodeU32Nat r1
      let (defT, r3) ← decodeU32Nat r2; .ok (.br_table targets defT, r3)
    | 0x10 => let (idx, r1) ← decodeU32Nat r; .ok (.call idx, r1)
    | 0x20 => let (idx, r1) ← decodeU32Nat r; .ok (.local_get idx, r1)
    | 0x21 => let (idx, r1) ← decodeU32Nat r; .ok (.local_set idx, r1)
    | 0x22 => let (idx, r1) ← decodeU32Nat r; .ok (.local_tee idx, r1)
    | 0x23 => let (idx, r1) ← decodeU32Nat r; .ok (.global_get idx, r1)
    | 0x3F => let r1 ← r.expectZero "memory.size"; .ok (.memory_size, r1)
    | 0x40 => let r1 ← r.expectZero "memory.grow"; .ok (.memory_grow, r1)
    | 0x41 => let (c, r1) ← decodeS32 r; .ok (.i32_const c, r1)
    | 0x42 => let (c, r1) ← decodeS64 r; .ok (.i64_const c, r1)
    | 0xFC =>
      let (subOp, r1) ← decodeU32 r
      match subOp.toNat with
      | 0x0A =>
        let r2 ← r1.expectZero "memory.copy[0]"; let r3 ← r2.expectZero "memory.copy[1]"
        .ok (.memory_copy, r3)
      | 0x0B => let r2 ← r1.expectZero "memory.fill"; .ok (.memory_fill, r2)
      | _ => .error s!"unsupported 0xFC prefix opcode {subOp} at offset {r.pos}"
    | _ => .error s!"unsupported WebAssembly opcode {opByte} at offset {r.pos}"
end

/-! ## Section Parsers -/

/-- Parse Type section (id 1): list of function signatures `(params -> results)`. -/
def decodeTypeSection (r : Reader) : Except String (List WFuncTy) := do
  let (count, r1) ← decodeU32 r
  let (types, cur) ← decodeList (r1.remaining + 1) count.toNat (fun c => do
    let (form, c1) ← c.readU8
    if form != 0x60 then .error s!"expected 0x60 for func type, got {form} at offset {c.pos}"
    else
      let (pCount, c2) ← decodeU32 c1
      let (params, c3) ← decodeList (c2.remaining + 1) pCount.toNat decodeValTy c2
      let (rCount, c4) ← decodeU32 c3
      let (results, c5) ← decodeList (c4.remaining + 1) rCount.toNat decodeValTy c4
      return (⟨params, results⟩, c5)) r1
  cur.ensureEmpty "type section"; .ok types

/-- Parse Function section (id 3): list of type indices corresponding to code entries. -/
def decodeFuncSection (r : Reader) : Except String (List Nat) := do
  let (count, r1) ← decodeU32 r
  let (typeIndices, cur) ← decodeList (r1.remaining + 1) count.toNat decodeU32Nat r1
  cur.ensureEmpty "function section"; .ok typeIndices

/-- Parse Memory section (id 5): initial and optional maximum page count. -/
def decodeMemorySection (r : Reader) : Except String (Option WMemSpec) := do
  let (count, cur) ← decodeU32 r
  if count == 0 then cur.ensureEmpty "memory section"; return none
  else if count > 1 then
    throw s!"multiple memories ({count}) unsupported in WebAssembly 1.0/2.0 sandbox"
  let (flag, r1) ← cur.readU8; let (minPages, r2) ← decodeU32 r1
  match flag with
  | 0x00 => r2.ensureEmpty "memory section"; .ok (some ⟨minPages.toNat, none⟩)
  | 0x01 =>
    let (maxPages, r3) ← decodeU32 r2
    r3.ensureEmpty "memory section"; .ok (some ⟨minPages.toNat, some maxPages.toNat⟩)
  | _ => throw s!"invalid memory limits flag {flag} at offset {r1.pos}"

/-- Parse Global section (id 6): declarations with `i32.const`/`i64.const` initializer. -/
def decodeGlobalSection (r : Reader) : Except String (List WGlobalDecl) := do
  let (count, r1) ← decodeU32 r
  let mut globals : List WGlobalDecl := []
  let mut cur := r1
  for _ in [0:count.toNat] do
    let (ty, rTy) ← decodeValTy cur
    let (mutByte, rMut) ← rTy.readU8
    if mutByte > 1 then throw s!"invalid global mutability byte {mutByte} at offset {rTy.pos}"
    let (initOp, rInit) ← rMut.readU8
    let (initVal, rEndByte) ← match initOp with
      | 0x41 =>
        if ty != .i32 then throw s!"mismatched global type {repr ty} with i32.const initializer"
        Prod.map (BitVec.setWidth 64) id <$> decodeS32 rInit
      | 0x42 =>
        if ty != .i64 then throw s!"mismatched global type {repr ty} with i64.const initializer"
        decodeS64 rInit
      | _ => throw s!"unsupported global init opcode {initOp} at offset {rInit.pos}"
    let (endByte, rNext) ← rEndByte.readU8
    if endByte != 0x0B then throw s!"global init expr missing trailing 0x0B (got {endByte})"
    globals := ⟨ty, mutByte == 1, initVal⟩ :: globals
    cur := rNext
  cur.ensureEmpty "global section"
  .ok globals.reverse

/-- Parse Export section (id 7): collect exported function symbols `(fnIdx, name)`. -/
def decodeExportSection (r : Reader) : Except String (List (Nat × String)) := do
  let (count, r1) ← decodeU32 r
  let mut fnExports : List (Nat × String) := []
  let mut cur := r1
  for _ in [0:count.toNat] do
    let (nameLen, rNameLen) ← decodeU32 cur
    let (nameBytes, rKind) ← rNameLen.readBytes nameLen.toNat
    let some nameStr := String.fromUTF8? nameBytes
      | throw s!"invalid UTF-8 in export name at offset {cur.pos}"
    let (kind, rIdx) ← rKind.readU8
    if kind > 0x03 then throw s!"invalid export kind {kind} at offset {rKind.pos}"
    let (itemIdx, rNext) ← decodeU32 rIdx
    if kind == 0x00 then fnExports := (itemIdx.toNat, nameStr) :: fnExports
    cur := rNext
  cur.ensureEmpty "export section"
  .ok fnExports.reverse

/-- Parse Code section (id 10): locals declarations and structured instruction trees. -/
def decodeCodeSection (r : Reader) (fnCount : Nat) (typeIndices : List Nat)
    (fnNames : List (Nat × String)) : Except String (List WFunc) := do
  let (count, r1) ← decodeU32 r
  if count.toNat != fnCount then
    throw s!"function section count ({fnCount}) != code section count ({count})"
  let mut funcs : List WFunc := []
  let mut cur := r1
  for i in [0:fnCount] do
    let (bodySize, rBodySize) ← decodeU32 cur
    let (bodyBytes, rNext) ← rBodySize.readBytes bodySize.toNat
    cur := rNext
    let bodyReader : Reader := ⟨bodyBytes, 0⟩
    let (localDeclsCount, rLocCount) ← decodeU32 bodyReader
    if localDeclsCount.toNat > 65536 then
      throw s!"function {i} exceeds local declarations cap (65536)"
    let mut locals : List WValTy := []
    let mut totalLocals : Nat := 0
    let mut curLoc := rLocCount
    for _ in [0:localDeclsCount.toNat] do
      let (locCnt, rNextCnt) ← decodeU32 curLoc
      let (locTy, rNextTy) ← decodeValTy rNextCnt
      if totalLocals + locCnt.toNat > 65536 then
        throw s!"function {i} exceeds locals cap (65536)"
      totalLocals := totalLocals + locCnt.toNat
      locals := locals ++ List.replicate locCnt.toNat locTy
      curLoc := rNextTy
    let (body, endedElse, rEnd) ← decodeInstrSeq (bodyReader.remaining + 1) false curLoc
    if endedElse then throw s!"function {i} code body terminated with unexpected 'else'"
    rEnd.ensureEmpty s!"function {i} code body"
    let tIdx := typeIndices[i]?.getD 0
    let fnName := (fnNames.find? (·.1 == i)).map (·.2) |>.getD s!"wasm_fn_{i}"
    funcs := ⟨fnName, tIdx, locals, body⟩ :: funcs
  cur.ensureEmpty "code section"
  .ok funcs.reverse

/-! ## Top-Level Binary Module Decoder -/

/-- Total WebAssembly binary format decoder
`decodeWasmBytes : ByteArray → Except String WModule`.
Rejects invalid headers, unknown/unsupported sections, out-of-order sections,
overlong integers, and malformed instruction trees with clean error messages. -/
def decodeWasmBytes (bs : ByteArray) : Except String WModule := do
  if bs.size < 8 then throw s!"binary too short ({bs.size} bytes < 8-byte wasm header)"
  if bs.extract 0 4 != ⟨#[0x00, 0x61, 0x73, 0x6D]⟩ then
    throw "invalid WebAssembly magic header (expected '\\0asm')"
  if bs.extract 4 8 != ⟨#[0x01, 0x00, 0x00, 0x00]⟩ then
    throw "unsupported WebAssembly binary version (expected version 1)"
  let mut cur : Reader := ⟨bs, 8⟩
  let mut lastSectionId : Nat := 0
  let mut types : List WFuncTy := []
  let mut typeIndices : List Nat := []
  let mut memory : Option WMemSpec := none
  let mut globals : List WGlobalDecl := []
  let mut fnExports : List (Nat × String) := []
  let mut funcs : List WFunc := []
  let mut seenCode : Bool := false
  let mut fuel := bs.size + 100
  while cur.pos < bs.size do
    if fuel == 0 then throw "section loop fuel exhausted"
    fuel := fuel - 1
    let (secId, r1) ← cur.readU8
    let (secLen, r2) ← decodeU32 r1
    let (secBytes, rNext) ← r2.readBytes secLen.toNat
    cur := rNext
    let secReader : Reader := ⟨secBytes, 0⟩
    if secId == 0 then continue
    if secId.toNat ≤ lastSectionId then
      throw s!"section {secId} out of order (previous section was {lastSectionId})"
    lastSectionId := secId.toNat
    match secId with
    | 1 => types ← decodeTypeSection secReader
    | 3 => typeIndices ← decodeFuncSection secReader
    | 5 => memory ← decodeMemorySection secReader
    | 6 => globals ← decodeGlobalSection secReader
    | 7 => fnExports ← decodeExportSection secReader
    | 10 =>
      funcs ← decodeCodeSection secReader typeIndices.length typeIndices fnExports
      seenCode := true
    | 2 | 4 | 8 | 9 | 11 | 12 => throw s!"section (id {secId}) unsupported in verified sandbox"
    | _ => throw s!"unknown section id {secId}"
  if !typeIndices.isEmpty && !seenCode then
    throw "function section present without corresponding code section"
  .ok { types := types, funcs := funcs, memory := memory, globals := globals }

/-! ## Verified End-to-End Entry Point & Universal Soundness Theorem -/

/-- Combined total entry point: decode `.wasm` binary bytes into a `WModule`, validate that
it satisfies all core sandbox memory-safety and structured control-flow invariants
(`validateModule m = true`), and lower it directly into a verified `LeanQbe.T.Module`. -/
def decodeAndLowerWasm (bs : ByteArray) : Except String (WModule × Module) :=
  match decodeWasmBytes bs with
  | .error e => .error e
  | .ok m =>
    if validateModule m then
      .ok (m, lowerModule m)
    else
      .error "decodeAndLowerWasm: module validation failed"

/-- Soundness corollary: ANY binary WebAssembly module accepted by `decodeAndLowerWasm`
inherits the universal `WasmMemInv` / host-memory preservation and sandbox isolation theorems
guaranteed by `LeanQbe.T.Wasm.lowerModule_semScc`. -/
theorem decodeAndLowerWasm_semScc {bs : ByteArray} {m : WModule} {qm : Module}
    (h : decodeAndLowerWasm bs = .ok (m, qm)) (Γext : Env) :
    ∀ i, Env.le (Env.restrict (WasmSandboxEnv m i) (qm.fns.map Fn.sig))
      (Env.semScc qm Γext) := by
  simp only [decodeAndLowerWasm] at h
  cases hdec : decodeWasmBytes bs <;> simp_all
  split at h <;> simp_all
  obtain ⟨rfl, rfl⟩ := h
  exact lowerModule_semScc (by assumption) Γext

end LeanQbe.T.Wasm
