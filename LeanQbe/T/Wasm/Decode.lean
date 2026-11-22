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

/-- Strict unsigned 32-bit LEB128 decoder with overlong rejection (at most 5 bytes). -/
def decodeU32 (r : Reader) : Except String (UInt32 × Reader) := do
  let mut res : Nat := 0
  let mut shift : Nat := 0
  let mut cur := r
  for i in [0:5] do
    let (b, next) ← cur.readU8
    cur := next
    let valBits := (b.toNat &&& 0x7F)
    if i == 4 then
      if (b.toNat &&& 0x70) != 0 then
        return ← .error s!"overlong u32 LEB128 at offset {cur.pos - 1}"
      if (b.toNat &&& 0x80) != 0 then
        return ← .error s!"u32 LEB128 exceeds 5 bytes at offset {cur.pos - 1}"
    res := res ||| (valBits <<< shift)
    if (b.toNat &&& 0x80) == 0 then
      return (UInt32.ofNat res, cur)
    shift := shift + 7
  .error s!"u32 LEB128 overflow at offset {cur.pos}"

/-- Strict unsigned 64-bit LEB128 decoder with overlong rejection (at most 10 bytes). -/
def decodeU64 (r : Reader) : Except String (UInt64 × Reader) := do
  let mut res : Nat := 0
  let mut shift : Nat := 0
  let mut cur := r
  for i in [0:10] do
    let (b, next) ← cur.readU8
    cur := next
    let valBits := (b.toNat &&& 0x7F)
    if i == 9 then
      if (b.toNat &&& 0x7E) != 0 then
        return ← .error s!"overlong u64 LEB128 at offset {cur.pos - 1}"
      if (b.toNat &&& 0x80) != 0 then
        return ← .error s!"u64 LEB128 exceeds 10 bytes at offset {cur.pos - 1}"
    res := res ||| (valBits <<< shift)
    if (b.toNat &&& 0x80) == 0 then
      return (UInt64.ofNat res, cur)
    shift := shift + 7
  .error s!"u64 LEB128 overflow at offset {cur.pos}"

/-- Strict signed 32-bit LEB128 decoder with overlong and sign-extension verification. -/
def decodeS32 (r : Reader) : Except String (BitVec 32 × Reader) := do
  let mut res : Nat := 0
  let mut shift : Nat := 0
  let mut cur := r
  for i in [0:5] do
    let (b, next) ← cur.readU8
    cur := next
    let valBits := (b.toNat &&& 0x7F)
    res := res ||| (valBits <<< shift)
    shift := shift + 7
    if (b.toNat &&& 0x80) == 0 then
      if i == 4 then
        let signBit := (b.toNat &&& 0x08) != 0
        let padBits := b.toNat &&& 0x70
        if signBit && padBits != 0x70 then
          return ← .error s!"invalid signed s32 sign padding at offset {cur.pos - 1}"
        if !signBit && padBits != 0 then
          return ← .error s!"invalid signed s32 zero padding at offset {cur.pos - 1}"
      let signExt := (b.toNat &&& 0x40) != 0
      if signExt && shift < 32 then
        let pad := ((1 <<< (32 - shift)) - 1) <<< shift
        res := res ||| pad
      return (BitVec.ofNat 32 res, cur)
  .error s!"s32 LEB128 overflow at offset {cur.pos}"

/-- Strict signed 64-bit LEB128 decoder with overlong and sign-extension verification. -/
def decodeS64 (r : Reader) : Except String (BitVec 64 × Reader) := do
  let mut res : Nat := 0
  let mut shift : Nat := 0
  let mut cur := r
  for i in [0:10] do
    let (b, next) ← cur.readU8
    cur := next
    let valBits := (b.toNat &&& 0x7F)
    res := res ||| (valBits <<< shift)
    shift := shift + 7
    if (b.toNat &&& 0x80) == 0 then
      if i == 9 then
        let signBit := (b.toNat &&& 0x01) != 0
        let padBits := b.toNat &&& 0x7E
        if signBit && padBits != 0x7E then
          return ← .error s!"invalid signed s64 sign padding at offset {cur.pos - 1}"
        if !signBit && padBits != 0 then
          return ← .error s!"invalid signed s64 zero padding at offset {cur.pos - 1}"
      let signExt := (b.toNat &&& 0x40) != 0
      if signExt && shift < 64 then
        let pad := ((1 <<< (64 - shift)) - 1) <<< shift
        res := res ||| pad
      return (BitVec.ofNat 64 res, cur)
  .error s!"s64 LEB128 overflow at offset {cur.pos}"

/-- Signed 33-bit LEB128 decoder for block type indices. -/
def decodeS33 (r : Reader) : Except String (Int × Reader) := do
  let mut res : Nat := 0
  let mut shift : Nat := 0
  let mut cur := r
  for i in [0:5] do
    let (b, next) ← cur.readU8
    cur := next
    let valBits := (b.toNat &&& 0x7F)
    res := res ||| (valBits <<< shift)
    shift := shift + 7
    if (b.toNat &&& 0x80) == 0 then
      if i == 4 then
        let signBit := (b.toNat &&& 0x10) != 0
        let padBits := b.toNat &&& 0x60
        if signBit && padBits != 0x60 then
          return ← .error s!"invalid s33 LEB128 sign padding at offset {cur.pos - 1}"
        if !signBit && padBits != 0 then
          return ← .error s!"invalid s33 LEB128 zero padding at offset {cur.pos - 1}"
      let signExt := (b.toNat &&& 0x40) != 0
      if signExt && shift < 33 then
        let val : Int := (res : Int) - ((1 : Int) <<< shift)
        return (val, cur)
      else
        return ((res : Int), cur)
  .error s!"s33 LEB128 overflow at offset {cur.pos}"

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

/-! ## Instruction Sequence & Structured Control Decoder -/

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
      if stopOnElse then
        .ok ([], true, r1)
      else
        .error s!"unexpected 'else' opcode 0x05 at offset {r.pos}"
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
    match opByte with
    | 0x00 => .ok (.unreachable, r)
    | 0x01 => .ok (.nop, r)
    | 0x02 =>
      let (bt, r1) ← decodeBlockTy r
      let (body, endedElse, r2) ← decodeInstrSeq fuel false r1
      if endedElse then
        .error s!"block instruction closed with 'else' at offset {r1.pos}"
      else
        .ok (.block bt body, r2)
    | 0x03 =>
      let (bt, r1) ← decodeBlockTy r
      let (body, endedElse, r2) ← decodeInstrSeq fuel false r1
      if endedElse then
        .error s!"loop instruction closed with 'else' at offset {r1.pos}"
      else
        .ok (.loop bt body, r2)
    | 0x04 =>
      let (bt, r1) ← decodeBlockTy r
      let (thenBody, endedElse, r2) ← decodeInstrSeq fuel true r1
      if endedElse then
        let (elseBody, endedElse2, r3) ← decodeInstrSeq fuel false r2
        if endedElse2 then
          .error s!"nested 'else' inside else-branch at offset {r2.pos}"
        else
          .ok (.if_ bt thenBody elseBody, r3)
      else
        .ok (.if_ bt thenBody [], r2)
    | 0x0C =>
      let (d, r1) ← decodeU32 r
      .ok (.br d.toNat, r1)
    | 0x0D =>
      let (d, r1) ← decodeU32 r
      .ok (.br_if d.toNat, r1)
    | 0x0E =>
      let (cnt, r1) ← decodeU32 r
      let (targets, r2) ← decodeList (r1.remaining + 1) cnt.toNat
        (fun cur => do let (t, next) ← decodeU32 cur; return (t.toNat, next)) r1
      let (defT, r3) ← decodeU32 r2
      .ok (.br_table targets defT.toNat, r3)
    | 0x0F => .ok (.return_, r)
    | 0x10 =>
      let (idx, r1) ← decodeU32 r
      .ok (.call idx.toNat, r1)
    | 0x1A => .ok (.drop, r)
    | 0x1B => .ok (.select, r)
    | 0x20 =>
      let (idx, r1) ← decodeU32 r
      .ok (.local_get idx.toNat, r1)
    | 0x21 =>
      let (idx, r1) ← decodeU32 r
      .ok (.local_set idx.toNat, r1)
    | 0x22 =>
      let (idx, r1) ← decodeU32 r
      .ok (.local_tee idx.toNat, r1)
    | 0x23 =>
      let (idx, r1) ← decodeU32 r
      .ok (.global_get idx.toNat, r1)
    | 0x28 =>
      let (arg, r1) ← decodeMemArg r
      .ok (.load .i32 .w32 false arg, r1)
    | 0x29 =>
      let (arg, r1) ← decodeMemArg r
      .ok (.load .i64 .w64 false arg, r1)
    | 0x2C =>
      let (arg, r1) ← decodeMemArg r
      .ok (.load .i32 .w8 true arg, r1)
    | 0x2D =>
      let (arg, r1) ← decodeMemArg r
      .ok (.load .i32 .w8 false arg, r1)
    | 0x2E =>
      let (arg, r1) ← decodeMemArg r
      .ok (.load .i32 .w16 true arg, r1)
    | 0x2F =>
      let (arg, r1) ← decodeMemArg r
      .ok (.load .i32 .w16 false arg, r1)
    | 0x30 =>
      let (arg, r1) ← decodeMemArg r
      .ok (.load .i64 .w8 true arg, r1)
    | 0x31 =>
      let (arg, r1) ← decodeMemArg r
      .ok (.load .i64 .w8 false arg, r1)
    | 0x32 =>
      let (arg, r1) ← decodeMemArg r
      .ok (.load .i64 .w16 true arg, r1)
    | 0x33 =>
      let (arg, r1) ← decodeMemArg r
      .ok (.load .i64 .w16 false arg, r1)
    | 0x34 =>
      let (arg, r1) ← decodeMemArg r
      .ok (.load .i64 .w32 true arg, r1)
    | 0x35 =>
      let (arg, r1) ← decodeMemArg r
      .ok (.load .i64 .w32 false arg, r1)
    | 0x36 =>
      let (arg, r1) ← decodeMemArg r
      .ok (.store .i32 .w32 arg, r1)
    | 0x37 =>
      let (arg, r1) ← decodeMemArg r
      .ok (.store .i64 .w64 arg, r1)
    | 0x3A =>
      let (arg, r1) ← decodeMemArg r
      .ok (.store .i32 .w8 arg, r1)
    | 0x3B =>
      let (arg, r1) ← decodeMemArg r
      .ok (.store .i32 .w16 arg, r1)
    | 0x3C =>
      let (arg, r1) ← decodeMemArg r
      .ok (.store .i64 .w8 arg, r1)
    | 0x3D =>
      let (arg, r1) ← decodeMemArg r
      .ok (.store .i64 .w16 arg, r1)
    | 0x3E =>
      let (arg, r1) ← decodeMemArg r
      .ok (.store .i64 .w32 arg, r1)
    | 0x3F =>
      let (zeroByte, r1) ← r.readU8
      if zeroByte == 0 then .ok (.memory_size, r1)
      else .error s!"memory.size expected trailing 0x00, got {zeroByte} at offset {r.pos}"
    | 0x40 =>
      let (zeroByte, r1) ← r.readU8
      if zeroByte == 0 then .ok (.memory_grow, r1)
      else .error s!"memory.grow expected trailing 0x00, got {zeroByte} at offset {r.pos}"
    | 0x41 =>
      let (c, r1) ← decodeS32 r
      .ok (.i32_const c, r1)
    | 0x42 =>
      let (c, r1) ← decodeS64 r
      .ok (.i64_const c, r1)
    | 0x45 => .ok (.eqz .i32, r)
    | 0x46 => .ok (.relop .i32 .eq, r)
    | 0x47 => .ok (.relop .i32 .ne, r)
    | 0x48 => .ok (.relop .i32 .lt_s, r)
    | 0x49 => .ok (.relop .i32 .lt_u, r)
    | 0x4A => .ok (.relop .i32 .gt_s, r)
    | 0x4B => .ok (.relop .i32 .gt_u, r)
    | 0x4C => .ok (.relop .i32 .le_s, r)
    | 0x4D => .ok (.relop .i32 .le_u, r)
    | 0x4E => .ok (.relop .i32 .ge_s, r)
    | 0x4F => .ok (.relop .i32 .ge_u, r)
    | 0x50 => .ok (.eqz .i64, r)
    | 0x51 => .ok (.relop .i64 .eq, r)
    | 0x52 => .ok (.relop .i64 .ne, r)
    | 0x53 => .ok (.relop .i64 .lt_s, r)
    | 0x54 => .ok (.relop .i64 .lt_u, r)
    | 0x55 => .ok (.relop .i64 .gt_s, r)
    | 0x56 => .ok (.relop .i64 .gt_u, r)
    | 0x57 => .ok (.relop .i64 .le_s, r)
    | 0x58 => .ok (.relop .i64 .le_u, r)
    | 0x59 => .ok (.relop .i64 .ge_s, r)
    | 0x5A => .ok (.relop .i64 .ge_u, r)
    | 0x67 => .ok (.unop .i32 .clz, r)
    | 0x68 => .ok (.unop .i32 .ctz, r)
    | 0x69 => .ok (.unop .i32 .popcnt, r)
    | 0x6A => .ok (.binop .i32 .add, r)
    | 0x6B => .ok (.binop .i32 .sub, r)
    | 0x6C => .ok (.binop .i32 .mul, r)
    | 0x6D => .ok (.binop .i32 .div_s, r)
    | 0x6E => .ok (.binop .i32 .div_u, r)
    | 0x6F => .ok (.binop .i32 .rem_s, r)
    | 0x70 => .ok (.binop .i32 .rem_u, r)
    | 0x71 => .ok (.binop .i32 .and, r)
    | 0x72 => .ok (.binop .i32 .or, r)
    | 0x73 => .ok (.binop .i32 .xor, r)
    | 0x74 => .ok (.binop .i32 .shl, r)
    | 0x75 => .ok (.binop .i32 .shr_s, r)
    | 0x76 => .ok (.binop .i32 .shr_u, r)
    | 0x77 => .ok (.binop .i32 .rotl, r)
    | 0x78 => .ok (.binop .i32 .rotr, r)
    | 0x79 => .ok (.unop .i64 .clz, r)
    | 0x7A => .ok (.unop .i64 .ctz, r)
    | 0x7B => .ok (.unop .i64 .popcnt, r)
    | 0x7C => .ok (.binop .i64 .add, r)
    | 0x7D => .ok (.binop .i64 .sub, r)
    | 0x7E => .ok (.binop .i64 .mul, r)
    | 0x7F => .ok (.binop .i64 .div_s, r)
    | 0x80 => .ok (.binop .i64 .div_u, r)
    | 0x81 => .ok (.binop .i64 .rem_s, r)
    | 0x82 => .ok (.binop .i64 .rem_u, r)
    | 0x83 => .ok (.binop .i64 .and, r)
    | 0x84 => .ok (.binop .i64 .or, r)
    | 0x85 => .ok (.binop .i64 .xor, r)
    | 0x86 => .ok (.binop .i64 .shl, r)
    | 0x87 => .ok (.binop .i64 .shr_s, r)
    | 0x88 => .ok (.binop .i64 .shr_u, r)
    | 0x89 => .ok (.binop .i64 .rotl, r)
    | 0x8A => .ok (.binop .i64 .rotr, r)
    | 0xA6 => .ok (.wrap_i64, r)
    | 0xA7 => .ok (.extend_i32_s, r)
    | 0xA8 => .ok (.extend_i32_u, r)
    | 0xC0 => .ok (.unop .i32 .extend8_s, r)
    | 0xC1 => .ok (.unop .i32 .extend16_s, r)
    | 0xC2 => .ok (.unop .i64 .extend8_s, r)
    | 0xC3 => .ok (.unop .i64 .extend16_s, r)
    | 0xC4 => .ok (.unop .i64 .extend32_s, r)
    | 0xFC =>
      let (subOp, r1) ← decodeU32 r
      match subOp with
      | 0 | 0xC0 => .ok (.unop .i32 .extend8_s, r1)
      | 1 | 0xC1 => .ok (.unop .i32 .extend16_s, r1)
      | 2 | 0xC2 => .ok (.unop .i64 .extend8_s, r1)
      | 3 | 0xC3 => .ok (.unop .i64 .extend16_s, r1)
      | 4 | 0xC4 => .ok (.unop .i64 .extend32_s, r1)
      | _ => .error s!"unsupported 0xFC extension opcode {subOp} at offset {r.pos}"
    | _ => .error s!"unsupported WebAssembly opcode {opByte} at offset {r.pos}"
end

/-! ## Section Parsers -/

/-- Parse Type section (id 1): list of function signatures `(params -> results)`. -/
def decodeTypeSection (r : Reader) : Except String (List WFuncTy) := do
  let (count, r1) ← decodeU32 r
  let (types, cur) ← decodeList (r1.remaining + 1) count.toNat (fun c => do
    let (form, c1) ← c.readU8
    if form != 0x60 then
      .error s!"expected 0x60 for func type, got {form} at offset {c.pos}"
    else
      let (pCount, c2) ← decodeU32 c1
      let (params, c3) ← decodeList (c2.remaining + 1) pCount.toNat decodeValTy c2
      let (rCount, c4) ← decodeU32 c3
      let (results, c5) ← decodeList (c4.remaining + 1) rCount.toNat decodeValTy c4
      return (⟨params, results⟩, c5)) r1
  if cur.remaining != 0 then
    .error s!"trailing {cur.remaining} bytes in type section"
  else
    .ok types

/-- Parse Function section (id 3): list of type indices corresponding to code entries. -/
def decodeFuncSection (r : Reader) : Except String (List Nat) := do
  let (count, r1) ← decodeU32 r
  let (typeIndices, cur) ← decodeList (r1.remaining + 1) count.toNat (fun c => do
    let (tIdx, cNext) ← decodeU32 c
    return (tIdx.toNat, cNext)) r1
  if cur.remaining != 0 then
    .error s!"trailing {cur.remaining} bytes in function section"
  else
    .ok typeIndices

/-- Parse Memory section (id 5): initial and optional maximum page count. -/
def decodeMemorySection (r : Reader) : Except String (Option WMemSpec) := do
  let (count, cur) ← decodeU32 r
  if count == 0 then
    return none
  else if count > 1 then
    return ← .error s!"multiple memories ({count}) unsupported in WebAssembly 1.0/2.0 sandbox"
  let (flag, r1) ← cur.readU8
  let (minPages, r2) ← decodeU32 r1
  match flag with
  | 0x00 =>
    if r2.remaining != 0 then
      .error s!"trailing {r2.remaining} bytes in memory section"
    else
      .ok (some ⟨minPages.toNat, none⟩)
  | 0x01 =>
    let (maxPages, r3) ← decodeU32 r2
    if r3.remaining != 0 then
      .error s!"trailing {r3.remaining} bytes in memory section"
    else
      .ok (some ⟨minPages.toNat, some maxPages.toNat⟩)
  | _ => .error s!"invalid memory limits flag {flag} at offset {r1.pos}"

/-- Parse Global section (id 6): declarations with `i32.const`/`i64.const` initializer. -/
def decodeGlobalSection (r : Reader) : Except String (List WGlobalDecl) := do
  let (count, r1) ← decodeU32 r
  let mut globals : List WGlobalDecl := []
  let mut cur := r1
  for _ in [0:count.toNat] do
    let (ty, rTy) ← decodeValTy cur
    let (mutByte, rMut) ← rTy.readU8
    let isMut := mutByte != 0
    let (initOp, rInit) ← rMut.readU8
    let (initVal, rEndByte) ← match initOp with
      | 0x41 =>
        let (v, next) ← decodeS32 rInit
        .ok (v.setWidth 64, next)
      | 0x42 =>
        let (v, next) ← decodeS64 rInit
        .ok (v, next)
      | _ => .error s!"unsupported global init opcode {initOp} at offset {rInit.pos}"
    let (endByte, rNext) ← rEndByte.readU8
    if endByte != 0x0B then
      return ← .error s!"global init expr missing trailing 0x0B (got {endByte})"
    globals := ⟨ty, isMut, initVal⟩ :: globals
    cur := rNext
  if cur.remaining != 0 then
    .error s!"trailing {cur.remaining} bytes in global section"
  else
    .ok globals.reverse

/-- Parse Export section (id 7): collect exported function symbols `(fnIdx, name)`. -/
def decodeExportSection (r : Reader) : Except String (List (Nat × String)) := do
  let (count, r1) ← decodeU32 r
  let mut fnExports : List (Nat × String) := []
  let mut cur := r1
  for _ in [0:count.toNat] do
    let (nameLen, rNameLen) ← decodeU32 cur
    let (nameBytes, rKind) ← rNameLen.readBytes nameLen.toNat
    let nameStr := (String.fromUTF8? nameBytes).getD ""
    let (kind, rIdx) ← rKind.readU8
    let (itemIdx, rNext) ← decodeU32 rIdx
    if kind == 0x00 then
      fnExports := (itemIdx.toNat, nameStr) :: fnExports
    cur := rNext
  if cur.remaining != 0 then
    .error s!"trailing {cur.remaining} bytes in export section"
  else
    .ok fnExports.reverse

/-- Parse Code section (id 10): locals declarations and structured instruction trees. -/
def decodeCodeSection (r : Reader) (fnCount : Nat) (typeIndices : List Nat)
    (fnNames : List (Nat × String)) : Except String (List WFunc) := do
  let (count, r1) ← decodeU32 r
  if count.toNat != fnCount then
    return ← .error s!"function section count ({fnCount}) != code section count ({count})"
  let mut funcs : List WFunc := []
  let mut cur := r1
  for i in [0:fnCount] do
    let (bodySize, rBodySize) ← decodeU32 cur
    let (bodyBytes, rNext) ← rBodySize.readBytes bodySize.toNat
    cur := rNext
    let bodyReader : Reader := ⟨bodyBytes, 0⟩
    let (localDeclsCount, rLocCount) ← decodeU32 bodyReader
    let mut locals : List WValTy := []
    let mut curLoc := rLocCount
    for _ in [0:localDeclsCount.toNat] do
      let (locCnt, rNextCnt) ← decodeU32 curLoc
      let (locTy, rNextTy) ← decodeValTy rNextCnt
      for _ in [0:locCnt.toNat] do
        locals := locTy :: locals
      curLoc := rNextTy
    let (body, endedElse, rEnd) ← decodeInstrSeq (bodyReader.remaining + 1) false curLoc
    if endedElse then
      return ← .error s!"function {i} code body terminated with unexpected 'else'"
    if rEnd.remaining != 0 then
      return ← .error s!"function {i} code body has {rEnd.remaining} trailing unparsed bytes"
    let tIdx := typeIndices[i]? |>.getD 0
    let fnName := (fnNames.find? (·.1 == i)).map (·.2) |>.getD s!"wasm_fn_{i}"
    funcs := ⟨fnName, tIdx, locals.reverse, body⟩ :: funcs
  if cur.remaining != 0 then
    .error s!"trailing {cur.remaining} bytes in code section"
  else
    .ok funcs.reverse

/-! ## Top-Level Binary Module Decoder -/

/-- Total WebAssembly binary format decoder
`decodeWasmBytes : ByteArray → Except String WModule`.
Rejects invalid headers, unknown/unsupported sections, out-of-order sections,
overlong integers, and malformed instruction trees with clean error messages. -/
def decodeWasmBytes (bs : ByteArray) : Except String WModule := do
  if bs.size < 8 then
    return ← .error s!"binary too short ({bs.size} bytes < 8-byte wasm header)"
  let magic := bs.extract 0 4
  if magic.get! 0 != 0x00 || magic.get! 1 != 0x61 ||
      magic.get! 2 != 0x73 || magic.get! 3 != 0x6D then
    return ← .error "invalid WebAssembly magic header (expected '\\0asm')"
  let ver := bs.extract 4 8
  if ver.get! 0 != 0x01 || ver.get! 1 != 0x00 ||
      ver.get! 2 != 0x00 || ver.get! 3 != 0x00 then
    return ← .error "unsupported WebAssembly binary version (expected version 1)"
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
    if fuel == 0 then
      return ← .error "section loop fuel exhausted"
    fuel := fuel - 1
    let (secId, r1) ← cur.readU8
    let (secLen, r2) ← decodeU32 r1
    let (secBytes, rNext) ← r2.readBytes secLen.toNat
    cur := rNext
    let secReader : Reader := ⟨secBytes, 0⟩
    if secId == 0 then
      -- Section 0: custom section (ignored/skipped)
      continue
    else
      if secId.toNat ≤ lastSectionId then
        return ← .error s!"section {secId} out of order (previous section was {lastSectionId})"
      lastSectionId := secId.toNat
      match secId with
      | 1 => types ← decodeTypeSection secReader
      | 2 => return ← .error "import section (id 2) unsupported in verified sandbox"
      | 3 => typeIndices ← decodeFuncSection secReader
      | 4 => return ← .error "table section (id 4) unsupported in verified sandbox"
      | 5 => memory ← decodeMemorySection secReader
      | 6 => globals ← decodeGlobalSection secReader
      | 7 => fnExports ← decodeExportSection secReader
      | 8 => return ← .error "start section (id 8) unsupported in verified sandbox"
      | 9 => return ← .error "element section (id 9) unsupported in verified sandbox"
      | 10 =>
        funcs ← decodeCodeSection secReader typeIndices.length typeIndices fnExports
        seenCode := true
      | 11 => return ← .error "data section (id 11) unsupported in verified sandbox"
      | 12 => return ← .error "datacount section (id 12) unsupported in verified sandbox"
      | _ => return ← .error s!"unknown section id {secId}"
  if !typeIndices.isEmpty && !seenCode then
    return ← .error "function section present without corresponding code section"
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
  have hm : validateModule m = true ∧ qm = lowerModule m := by
    revert h
    simp only [decodeAndLowerWasm]
    cases decodeWasmBytes bs with
    | error _ => intro h; contradiction
    | ok mod =>
      dsimp only
      split
      · intro h
        injection h with h1
        injection h1 with hm1 hm2
        subst hm1 hm2
        rename_i hv
        exact ⟨hv, rfl⟩
      · intro h; contradiction
  rcases hm with ⟨hv, rfl⟩
  exact lowerModule_semScc hv Γext

end LeanQbe.T.Wasm
