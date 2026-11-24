module

public import LeanQbe.T.Wasm.Validate
public import LeanQbe.T.Legal
public import LeanQbe.T.WfLemmas
public import LeanQbe.T.LegalWfBaseLemmas1
public import LeanQbe.T.Module

/-!
# Verified WebAssembly VM-Context & Bulk-Memory IR Lowering (`LeanQbe.T.Wasm.BulkLower`)

Defines the VM-context SFI sandbox ABI (`(vmCtx, fuel, ...wasmParams)` returning
`(status, remFuel, ...wasmResults)` with `vmCtx` pointing to `[memBase, memLen, memCap]`),
shared lowering types/stack helpers, and target-independent IR emitters for:
* `emitLoadVmCtx`: loads `(memBase, memLen)` from `[vmCtx + 0]` and `[vmCtx + 8]`.
* `emitMemBounds`: 64-bit overflow-free linear-memory bounds checks.
* `emitMemSize`: returns current page count `memLen >>> 16`.
* `emitMemGrow`: grows linear memory up to `min(memCap, memMaxBytes)`, zero-initializing newly
  exposed pages (`8192` 8-byte stores/page) with per-page `fuel` metering, updating `[vmCtx + 8]`,
  and returning old page count or `-1` (`0xFFFFFFFF`).
* `emitMemFill`: bounds-checked, fuel-metered byte fill (`0xFC 0x0B 0x00`).
* `emitMemCopy`: bounds-checked, overlap-safe forward/backward copy (`0xFC 0x0A 0x00 0x00`).

Also proves `Wf` and `supportsSource` preservation for all VM-context and bulk-memory emitters.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Wasm

/-! ## Lowered Sandbox ABI & Stack Values -/

/-- Return signature of a lowered WebAssembly function: `(status, remFuel, ...results)`. -/
@[expose, reducible] def wasmRetSig (rs : List WValTy) : List Ty :=
  T.i32 :: T.i64 :: rs.map WValTy.toTy

/-- Lowered `LeanQbe.T` parameter signature: `(vmCtx, fuel, ...params)`. -/
@[expose, reducible] def wasmAbiParams (ft : WFuncTy) : List Ty :=
  [T.i64, T.i64] ++ ft.params.map WValTy.toTy

/-- Lowered `LeanQbe.T` result signature matching `wasmRetSig ft.results`. -/
@[expose, reducible] def wasmAbiResults (ft : WFuncTy) : List Ty :=
  wasmRetSig ft.results

/-- Join/loop block parameter signature carrying `(fuel, ...locals, ...branchArgs)`. -/
@[expose, reducible] def labelSig (locTys argTys : List WValTy) : List Ty :=
  T.i64 :: (locTys.map WValTy.toTy ++ argTys.map WValTy.toTy)

/-- Zero-initialized `Arg V` tuple matching `ts.map WValTy.toTy`. -/
@[expose] def zeroArgs {V : Ty → Type} : (ts : List WValTy) → Tup (Arg V) (ts.map WValTy.toTy)
  | [] => ()
  | t :: ts => (t.zeroArg, zeroArgs ts)

/-- Append zero-initialized extra locals to function parameters without `List.map` casts. -/
@[expose] def appendZeroLocals {V : Ty → Type} :
    (ps ls : List WValTy) → Tup (Arg V) (ps.map WValTy.toTy) →
    Tup (Arg V) ((ps ++ ls).map WValTy.toTy)
  | [], ls, () => zeroArgs ls
  | _ :: ps, ls, (a, as) => (a, appendZeroLocals ps ls as)

/-- Emit a clean trap/error return `(code, fuel, 0, ...)` preserving all host registers/memory. -/
@[expose, reducible] def mkTrapExpr {V : Ty → Type} {L : List Ty → Type} (retTys : List WValTy)
    (code : BitVec 32) (fuel : Arg V T.i64) : Expr V L (wasmRetSig retTys) :=
  .ret (.imm code, fuel, zeroArgs retTys)

/-- Propagate a callee's non-zero `(status, remFuel)` trap return cleanly. -/
@[expose, reducible] def mkStatusTrapExpr {V : Ty → Type} {L : List Ty → Type}
    (retTys : List WValTy) (status : Arg V T.i32) (fuel : Arg V T.i64) :
    Expr V L (wasmRetSig retTys) :=
  .ret (status, fuel, zeroArgs retTys)

/-- Typed operand on the lowered WebAssembly value stack. -/
inductive SVal (V : Ty → Type) where
  | i32 (a : Arg V T.i32)
  | i64 (a : Arg V T.i64)

/-- WebAssembly value type tag of an `SVal`. -/
@[expose, reducible] def SVal.ty {V : Ty → Type} : SVal V → WValTy
  | .i32 _ => .i32
  | .i64 _ => .i64

/-- Wrap an `Arg V t.toTy` as an `SVal V`. -/
@[expose, reducible] def SVal.ofArg {V : Ty → Type} : (t : WValTy) → Arg V t.toTy → SVal V
  | .i32, a => .i32 a
  | .i64, a => .i64 a

/-- Lowered structured control label pairing its branch signature with an `Expr` label. -/
structure WLabel (V : Ty → Type) (L : List Ty → Type) (locTys : List WValTy) where
  argTys : List WValTy
  lbl : L (labelSig locTys argTys)

/-- Lowering context shared across a single function body. -/
structure WLowerCtx where
  types : List WFuncTy
  funcs : List WFunc
  hasMem : Bool
  memMaxBytes : BitVec 64
  globals : List WGlobalDecl
  locTys : List WValTy
  retTys : List WValTy

/-- Continuation type passed to instruction emitters. -/
abbrev WCont (V : Ty → Type) (L : List Ty → Type) (locTys retTys : List WValTy) :=
  Arg V T.i64 → Tup (Arg V) (locTys.map WValTy.toTy) → List (SVal V) →
  Expr V L (wasmRetSig retTys)

/-- Pop an `i32` operand from `stk`. -/
@[expose] def pop32 {V : Ty → Type} : List (SVal V) → Option (Arg V T.i32 × List (SVal V))
  | .i32 a :: rest => some (a, rest)
  | _ => none

/-- Pop an `i64` operand from `stk`. -/
@[expose] def pop64 {V : Ty → Type} : List (SVal V) → Option (Arg V T.i64 × List (SVal V))
  | .i64 a :: rest => some (a, rest)
  | _ => none

/-- Pop an operand matching expected type `t` from `stk`. -/
@[expose] def popExpectS {V : Ty → Type} (t : WValTy) (stk : List (SVal V)) :
    Option (Arg V t.toTy × List (SVal V)) :=
  match t, stk with
  | .i32, .i32 a :: rest => some (a, rest)
  | .i64, .i64 a :: rest => some (a, rest)
  | _, _ => none

/-- Pop `ts` (bottom-to-top WebAssembly order) from `stk` into `Tup (Arg V) (ts.map toTy)`. -/
@[expose] def popArgsAux {V : Ty → Type} :
    (ts : List WValTy) → List (SVal V) →
    Option (Tup (Arg V) (ts.map WValTy.toTy) × List (SVal V))
  | [], stk => some ((), stk)
  | t :: ts, stk => do
    let (tail, stk1) ← popArgsAux ts stk
    let (hd, stk2) ← popExpectS t stk1
    some ((hd, tail), stk2)

/-- Push `Tup (Arg V) (ts.map toTy)` onto `stk` matching `popArgsAux`. -/
@[expose] def pushArgsAux {V : Ty → Type} :
    (ts : List WValTy) → Tup (Arg V) (ts.map WValTy.toTy) → List (SVal V) → List (SVal V)
  | [], (), stk => stk
  | t :: ts, (a, as), stk => pushArgsAux ts as (SVal.ofArg t a :: stk)

/-- Look up local variable `idx` in `locs`. -/
@[expose] def getLocal {V : Ty → Type} :
    (ts : List WValTy) → Tup (Arg V) (ts.map WValTy.toTy) → Nat → Option (SVal V)
  | [], (), _ => none
  | t :: _, (a, _), 0 => some (SVal.ofArg t a)
  | _ :: ts, (_, as), idx + 1 => getLocal ts as idx

/-- Update local variable `idx` in `locs`. -/
@[expose] def setLocal {V : Ty → Type} :
    (ts : List WValTy) → Tup (Arg V) (ts.map WValTy.toTy) → Nat → SVal V →
    Option (Tup (Arg V) (ts.map WValTy.toTy))
  | [], (), _, _ => none
  | .i32 :: _, (_, as), 0, .i32 a => some (a, as)
  | .i64 :: _, (_, as), 0, .i64 a => some (a, as)
  | _ :: _, (_, _), 0, _ => none
  | _t :: ts, (a, as), idx + 1, v => do
    let as' ← setLocal ts as idx v
    some (a, as')

/-! ## VM-Context & Bulk-Memory IR Emitters -/

/-- Load `(memBase, memLen)` from `[vmCtx + 0]` and `[vmCtx + 8]`. -/
@[expose] def emitLoadVmCtx {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (vmCtx : Arg V T.i64) (k : Arg V T.i64 → Arg V T.i64 → Expr V L rs) : Expr V L rs :=
  .load T.i64 vmCtx fun memBase =>
  .let_ (.mk (.add T.i64) (vmCtx, .imm 8#64, ())) fun pLen =>
  .load T.i64 (.var pLen.1) fun memLen =>
    k (.var memBase) (.var memLen)

/-- 64-bit SFI memory bounds check via `vmCtx`: verify `zext32(idx) + off + bytes ≤ᵤ memLen`
before forming host pointer `memBase + zext32(idx) + off`. Never wraps because
`zext32 + off + bytes < 2^34`. -/
@[expose] def emitMemBounds {V : Ty → Type} {L : List Ty → Type} (retTys : List WValTy)
    (vmCtx fuel : Arg V T.i64) (idx32 : Arg V T.i32) (arg : WMemArg) (bytes : Nat)
    (kOk : Arg V T.i64 → Expr V L (wasmRetSig retTys)) : Expr V L (wasmRetSig retTys) :=
  emitLoadVmCtx vmCtx fun memBase memLen =>
    .let_ (.mk (.zext 32 64) (idx32, ())) fun idx64 =>
    .let_ (.mk (.add T.i64) (.var idx64.1, .imm (BitVec.ofNat 64 arg.offset.toNat), ()))
      fun ea =>
    .let_ (.mk (.add T.i64) (.var ea.1, .imm (BitVec.ofNat 64 bytes), ())) fun endOff =>
    .let_ (.mk (.cmp .ule T.i64) (.var endOff.1, memLen, ())) fun inBnd =>
    .jnz (.var inBnd.1)
      (.let_ (.mk (.add T.i64) (memBase, .var ea.1, ())) fun ptr => kOk (.var ptr.1))
      (mkTrapExpr retTys 1#32 fuel)

/-- Emit `memory.size` (`0x3F 0x00`): load `memLen` from `[vmCtx + 8]` and divide by 65536. -/
@[expose] def emitMemSize {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (vmCtx : Arg V T.i64) (k : Arg V T.i32 → Expr V L rs) : Expr V L rs :=
  .let_ (.mk (.add T.i64) (vmCtx, .imm 8#64, ())) fun pLen =>
  .load T.i64 (.var pLen.1) fun memLen =>
  .let_ (.mk (.lshr T.i64) (.var memLen, .imm 16#64, ())) fun pages64 =>
  .let_ (.mk (.trunc 64 32) (.var pages64.1, ())) fun pages32 =>
    k (.var pages32.1)

/-- Zero-initialize one 64 KiB page starting at `pagePtr` (`8192` 8-byte stores), then jump
into `kDone`. -/
@[expose] def emitMemZeroPage {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (pagePtr : Arg V T.i64) (kDone : Expr V L rs) : Expr V L rs :=
  .group (sig := [[]])
    (fun _ => .cons (fun _ => kDone) .nil)
    (fun (jDone, ()) =>
      .group (sig := [[T.i64, T.i64]])
        (fun (lZero, ()) =>
          .cons (fun zxs =>
            let zRem : Arg V T.i64 := .var zxs.1
            let zPtr : Arg V T.i64 := .var zxs.2.1
            .let_ (.mk (.cmp .eq T.i64) (zRem, .imm 0#64, ())) fun zDone =>
            .jnz (.var zDone.1)
              (.jump jDone ())
              (.store (t := T.i64) (.imm 0#64) zPtr
                (.let_ (.mk (.sub T.i64) (zRem, .imm 8#64, ())) fun zRemN =>
                 .let_ (.mk (.add T.i64) (zPtr, .imm 8#64, ())) fun zPtrN =>
                   .jump lZero (.var zRemN.1, .var zPtrN.1, ())))) .nil)
        (fun (lZero, ()) => .jump lZero (.imm 65536#64, pagePtr, ())))

/-- Fuel-metered per-page loop for `memory.grow`: zeroes `delta64` 64 KiB pages from
`startPtr`, stores `newLen` to `[pLen]`, and jumps to `jDone (remFuel, oldPages32)`. -/
@[expose] def emitMemGrowLoop {V : Ty → Type} {L : List Ty → Type} (retTys : List WValTy)
    (jDone : L [T.i64, T.i32]) (pLen newLen : Arg V T.i64) (oldPages32 : Arg V T.i32)
    (fuel delta64 startPtr : Arg V T.i64) : Expr V L (wasmRetSig retTys) :=
  .group (sig := [[T.i64, T.i64, T.i64]])
    (fun (lPage, ()) =>
      .cons (fun pxs =>
        let fHdr : Arg V T.i64 := .var pxs.1
        let pRem : Arg V T.i64 := .var pxs.2.1
        let pPtr : Arg V T.i64 := .var pxs.2.2.1
        .let_ (.mk (.cmp .eq T.i64) (pRem, .imm 0#64, ())) fun pDone =>
        .jnz (.var pDone.1)
          (.store (t := T.i64) newLen pLen (.jump jDone (fHdr, oldPages32, ())))
          (.let_ (.mk (.cmp .eq T.i64) (fHdr, .imm 0#64, ())) fun outFuel =>
           .jnz (.var outFuel.1)
             (mkTrapExpr retTys 2#32 fHdr)
             (.let_ (.mk (.sub T.i64) (fHdr, .imm 1#64, ())) fun fNext =>
              emitMemZeroPage pPtr
                (.let_ (.mk (.sub T.i64) (pRem, .imm 1#64, ())) fun pRemN =>
                 .let_ (.mk (.add T.i64) (pPtr, .imm 65536#64, ())) fun pPtrN =>
                   .jump lPage (.var fNext.1, .var pRemN.1, .var pPtrN.1, ()))))) .nil)
    (fun (lPage, ()) => .jump lPage (fuel, delta64, startPtr, ()))

/-- Emit `memory.grow` (`0x40 0x00`): grows `memLen` up to `min(memCap, memMaxBytes)`,
zero-initializing each newly exposed page with per-page `fuel` metering, updating `[vmCtx + 8]`,
and returning old page count or `-1` (`0xFFFFFFFF`). -/
@[expose] def emitMemGrow {V : Ty → Type} {L : List Ty → Type} (retTys : List WValTy)
    (memMaxBytes : BitVec 64) (vmCtx fuel : Arg V T.i64) (delta32 : Arg V T.i32)
    (k : Arg V T.i64 → Arg V T.i32 → Expr V L (wasmRetSig retTys)) :
    Expr V L (wasmRetSig retTys) :=
  .group (sig := [[T.i64, T.i32]])
    (fun _ => .cons (fun xs => k (.var xs.1) (.var xs.2.1)) .nil)
    (fun (jDone, ()) =>
      .load T.i64 vmCtx fun memBase =>
      .let_ (.mk (.add T.i64) (vmCtx, .imm 8#64, ())) fun pLen =>
      .load T.i64 (.var pLen.1) fun memLen =>
      .let_ (.mk (.add T.i64) (vmCtx, .imm 16#64, ())) fun pCap =>
      .load T.i64 (.var pCap.1) fun memCap =>
      .let_ (.mk (.lshr T.i64) (.var memLen, .imm 16#64, ())) fun oldPages64 =>
      .let_ (.mk (.trunc 64 32) (.var oldPages64.1, ())) fun oldPages32 =>
      .let_ (.mk (.cmp .eq T.i32) (delta32, .imm 0#32, ())) fun isZero =>
      .jnz (.var isZero.1)
        (.jump jDone (fuel, .var oldPages32.1, ()))
        (.let_ (.mk (.zext 32 64) (delta32, ())) fun delta64 =>
         .let_ (.mk (.shl T.i64) (.var delta64.1, .imm 16#64, ())) fun growBytes =>
         .let_ (.mk (.add T.i64) (.var memLen, .var growBytes.1, ())) fun newLen =>
         .let_ (.mk (.cmp .ule T.i64) (.var memLen, .var newLen.1, ())) fun noWrap =>
         .let_ (.mk (.cmp .ule T.i64) (.var newLen.1, .var memCap, ())) fun leCap =>
         .let_ (.mk (.cmp .ule T.i64) (.var newLen.1, .imm memMaxBytes, ())) fun leMax =>
         .let_ (.mk (.and .bool) (.var noWrap.1, .var leCap.1, ())) fun ok1 =>
         .let_ (.mk (.and .bool) (.var ok1.1, .var leMax.1, ())) fun okAll =>
         .jnz (.var okAll.1)
           (.let_ (.mk (.add T.i64) (.var memBase, .var memLen, ())) fun startPtr =>
             emitMemGrowLoop retTys jDone (.var pLen.1) (.var newLen.1) (.var oldPages32.1)
               fuel (.var delta64.1) (.var startPtr.1))
           (.jump jDone (fuel, .imm 0xFFFFFFFF#32, ()))))

/-- Fuel-metered byte-fill loop for `memory.fill`, exiting to `jAfter (remFuel)`. -/
@[expose] def emitMemFillLoop {V : Ty → Type} {L : List Ty → Type} (retTys : List WValTy)
    (jAfter : L [T.i64]) (byteVal : Arg V T.i8) (fuel n64 dstPtr0 : Arg V T.i64) :
    Expr V L (wasmRetSig retTys) :=
  .group (sig := [[T.i64, T.i64, T.i64]])
    (fun (lLoop, ()) =>
      .cons (fun lxs =>
        let fHdr : Arg V T.i64 := .var lxs.1
        let rem : Arg V T.i64 := .var lxs.2.1
        let ptr : Arg V T.i64 := .var lxs.2.2.1
        .let_ (.mk (.cmp .eq T.i64) (rem, .imm 0#64, ())) fun isDone =>
        .jnz (.var isDone.1)
          (.jump jAfter (fHdr, ()))
          (.let_ (.mk (.cmp .eq T.i64) (fHdr, .imm 0#64, ())) fun outFuel =>
           .jnz (.var outFuel.1)
             (mkTrapExpr retTys 2#32 fHdr)
             (.let_ (.mk (.sub T.i64) (fHdr, .imm 1#64, ())) fun fNext =>
              .store (t := T.i8) byteVal ptr
                (.let_ (.mk (.sub T.i64) (rem, .imm 1#64, ())) fun remN =>
                 .let_ (.mk (.add T.i64) (ptr, .imm 1#64, ())) fun ptrN =>
                   .jump lLoop (.var fNext.1, .var remN.1, .var ptrN.1, ()))))) .nil)
    (fun (lLoop, ()) => .jump lLoop (fuel, n64, dstPtr0, ()))

/-- Emit `memory.fill` (`0xFC 0x0B 0x00`): checks `zext32(dst) + zext32(n) ≤ᵤ memLen` in 64-bit
before filling `n` bytes with `val & 0xFF` in a fuel-metered loop; traps with zero writes if
OOB. -/
@[expose] def emitMemFill {V : Ty → Type} {L : List Ty → Type} (retTys : List WValTy)
    (vmCtx fuel : Arg V T.i64) (dst32 val32 n32 : Arg V T.i32)
    (k : Arg V T.i64 → Expr V L (wasmRetSig retTys)) : Expr V L (wasmRetSig retTys) :=
  emitLoadVmCtx vmCtx fun memBase memLen =>
    .let_ (.mk (.zext 32 64) (dst32, ())) fun dst64 =>
    .let_ (.mk (.zext 32 64) (n32, ())) fun n64 =>
    .let_ (.mk (.add T.i64) (.var dst64.1, .var n64.1, ())) fun endOff =>
    .let_ (.mk (.cmp .ule T.i64) (.var endOff.1, memLen, ())) fun inBnd =>
    .jnz (.var inBnd.1)
      (.let_ (.mk (.trunc 32 8) (val32, ())) fun byteVal =>
       .let_ (.mk (.add T.i64) (memBase, .var dst64.1, ())) fun dstPtr0 =>
       .group (sig := [[T.i64]])
         (fun _ => .cons (fun xs => k (.var xs.1)) .nil)
         (fun (jAfter, ()) =>
           emitMemFillLoop retTys jAfter (.var byteVal.1) fuel (.var n64.1) (.var dstPtr0.1)))
      (mkTrapExpr retTys 1#32 fuel)

/-- Shared forward (`fwd = true`) / backward (`fwd = false`) fuel-metered copy loop for
`memory.copy`. -/
@[expose] def emitMemCopyLoop {V : Ty → Type} {L : List Ty → Type} (fwd : Bool)
    (retTys : List WValTy) (jAfter : L [T.i64])
    (fuel n64 dstPtr0 srcPtr0 : Arg V T.i64) : Expr V L (wasmRetSig retTys) :=
  .group (sig := [[T.i64, T.i64, T.i64, T.i64]])
    (fun (lLoop, ()) =>
      .cons (fun lxs =>
        let fHdr : Arg V T.i64 := .var lxs.1
        let rem : Arg V T.i64 := .var lxs.2.1
        let dPtr : Arg V T.i64 := .var lxs.2.2.1
        let sPtr : Arg V T.i64 := .var lxs.2.2.2.1
        .let_ (.mk (.cmp .eq T.i64) (rem, .imm 0#64, ())) fun isDone =>
        .jnz (.var isDone.1)
          (.jump jAfter (fHdr, ()))
          (.let_ (.mk (.cmp .eq T.i64) (fHdr, .imm 0#64, ())) fun outFuel =>
           .jnz (.var outFuel.1)
             (mkTrapExpr retTys 2#32 fHdr)
             (.let_ (.mk (.sub T.i64) (fHdr, .imm 1#64, ())) fun fNext =>
              .let_ (.mk (.sub T.i64) (rem, .imm 1#64, ())) fun remN =>
              if fwd then
                .load T.i8 sPtr fun b =>
                .store (t := T.i8) (.var b) dPtr
                  (.let_ (.mk (.add T.i64) (dPtr, .imm 1#64, ())) fun dPtrN =>
                   .let_ (.mk (.add T.i64) (sPtr, .imm 1#64, ())) fun sPtrN =>
                     .jump lLoop (.var fNext.1, .var remN.1, .var dPtrN.1, .var sPtrN.1, ()))
              else
                .let_ (.mk (.sub T.i64) (dPtr, .imm 1#64, ())) fun dPtrP =>
                .let_ (.mk (.sub T.i64) (sPtr, .imm 1#64, ())) fun sPtrP =>
                .load T.i8 (.var sPtrP.1) fun b =>
                .store (t := T.i8) (.var b) (.var dPtrP.1)
                  (.jump lLoop (.var fNext.1, .var remN.1, .var dPtrP.1, .var sPtrP.1, ())))))
        .nil)
    (fun (lLoop, ()) => .jump lLoop (fuel, n64, dstPtr0, srcPtr0, ()))

/-- Emit `memory.copy` (`0xFC 0x0A 0x00 0x00`): checks `zext32(dst) + zext32(n) ≤ᵤ memLen` and
`zext32(src) + zext32(n) ≤ᵤ memLen` in 64-bit before executing overlap-safe forward/backward copy;
traps with zero writes if OOB. -/
@[expose] def emitMemCopy {V : Ty → Type} {L : List Ty → Type} (retTys : List WValTy)
    (vmCtx fuel : Arg V T.i64) (dst32 src32 n32 : Arg V T.i32)
    (k : Arg V T.i64 → Expr V L (wasmRetSig retTys)) : Expr V L (wasmRetSig retTys) :=
  emitLoadVmCtx vmCtx fun memBase memLen =>
    .let_ (.mk (.zext 32 64) (dst32, ())) fun dst64 =>
    .let_ (.mk (.zext 32 64) (src32, ())) fun src64 =>
    .let_ (.mk (.zext 32 64) (n32, ())) fun n64 =>
    .let_ (.mk (.add T.i64) (.var dst64.1, .var n64.1, ())) fun dstEnd =>
    .let_ (.mk (.add T.i64) (.var src64.1, .var n64.1, ())) fun srcEnd =>
    .let_ (.mk (.cmp .ule T.i64) (.var dstEnd.1, memLen, ())) fun okDst =>
    .let_ (.mk (.cmp .ule T.i64) (.var srcEnd.1, memLen, ())) fun okSrc =>
    .let_ (.mk (.and .bool) (.var okDst.1, .var okSrc.1, ())) fun inBnd =>
    .jnz (.var inBnd.1)
      (.group (sig := [[T.i64]])
        (fun _ => .cons (fun xs => k (.var xs.1)) .nil)
        (fun (jAfter, ()) =>
          .let_ (.mk (.cmp .ule T.i64) (.var dst64.1, .var src64.1, ())) fun isFwd =>
          .jnz (.var isFwd.1)
            (.let_ (.mk (.add T.i64) (memBase, .var dst64.1, ())) fun dFwd =>
             .let_ (.mk (.add T.i64) (memBase, .var src64.1, ())) fun sFwd =>
               emitMemCopyLoop true retTys jAfter fuel (.var n64.1) (.var dFwd.1) (.var sFwd.1))
            (.let_ (.mk (.add T.i64) (memBase, .var dstEnd.1, ())) fun dBwd =>
             .let_ (.mk (.add T.i64) (memBase, .var srcEnd.1, ())) fun sBwd =>
               emitMemCopyLoop false retTys jAfter fuel (.var n64.1)
                 (.var dBwd.1) (.var sBwd.1))))
      (mkTrapExpr retTys 1#32 fuel)

/-! ## Relational Stack & Well-Formedness (`Wf`) Preservation -/

section WfHelpers

theorem ArgRel.mono {V₁ V₂ : Ty → Type} {G G' : Ctx V₁ V₂} (hG : ∀ p ∈ G, p ∈ G')
    {t : Ty} {a₁ : Arg V₁ t} {a₂ : Arg V₂ t} : ArgRel G t a₁ a₂ → ArgRel G' t a₁ a₂
  | .var hv => .var (hG _ hv)
  | .imm _ => .imm _

theorem TRel_ArgRel_mono {V₁ V₂ : Ty → Type} {G G' : Ctx V₁ V₂} (hG : ∀ p ∈ G, p ∈ G') :
    {ts : List Ty} → {xs₁ : Tup (Arg V₁) ts} → {xs₂ : Tup (Arg V₂) ts} →
    TRel (ArgRel G) xs₁ xs₂ → TRel (ArgRel G') xs₁ xs₂
  | [], (), (), .nil => .nil
  | _ :: _, (_, _), (_, _), .cons h hs => .cons (ArgRel.mono hG h) (TRel_ArgRel_mono hG hs)

/-- Relational correspondence between lowered operand stack items. -/
@[expose] def SValRel {V₁ V₂ : Ty → Type} (G : Ctx V₁ V₂) : SVal V₁ → SVal V₂ → Prop
  | .i32 a₁, .i32 a₂ => ArgRel G T.i32 a₁ a₂
  | .i64 a₁, .i64 a₂ => ArgRel G T.i64 a₁ a₂
  | _, _ => False

theorem SValRel.mono {V₁ V₂ : Ty → Type} {G G' : Ctx V₁ V₂} (hG : ∀ p ∈ G, p ∈ G')
    {v₁ : SVal V₁} {v₂ : SVal V₂} : SValRel G v₁ v₂ → SValRel G' v₁ v₂ := by
  cases v₁ <;> cases v₂ <;> simp only [SValRel]
  · exact ArgRel.mono hG
  · exact id
  · exact id
  · exact ArgRel.mono hG

theorem SValRel.ofArg {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} (t : WValTy)
    {a₁ : Arg V₁ t.toTy} {a₂ : Arg V₂ t.toTy} (h : ArgRel G t.toTy a₁ a₂) :
    SValRel G (SVal.ofArg t a₁) (SVal.ofArg t a₂) := by
  cases t <;> exact h

/-- Pointwise relation over two lists of equal length. -/
inductive ListRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : ListRel R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
    R a b → ListRel R as bs → ListRel R (a :: as) (b :: bs)

theorem ListRel.imp {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    {xs : List α} → {ys : List β} → ListRel R xs ys → ListRel S xs ys
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hab hrest => .cons (h _ _ hab) (hrest.imp h)

/-- Relational correspondence across WebAssembly operand stacks. -/
@[expose, reducible] def StkRel {V₁ V₂ : Ty → Type} (G : Ctx V₁ V₂)
    (s₁ : List (SVal V₁)) (s₂ : List (SVal V₂)) : Prop :=
  ListRel (SValRel G) s₁ s₂

theorem StkRel.mono {V₁ V₂ : Ty → Type} {G G' : Ctx V₁ V₂} (hG : ∀ p ∈ G, p ∈ G')
    {s₁ : List (SVal V₁)} {s₂ : List (SVal V₂)} (hs : StkRel G s₁ s₂) : StkRel G' s₁ s₂ :=
  hs.imp fun _ _ h => SValRel.mono hG h

/-- Relational correspondence across structured control labels. -/
@[expose] def LabRel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} (D : Ctx L₁ L₂)
    (locTys : List WValTy) (l₁ : WLabel V₁ L₁ locTys) (l₂ : WLabel V₂ L₂ locTys) : Prop :=
  ∃ h : l₁.argTys = l₂.argTys, ⟨labelSig locTys l₁.argTys, l₁.lbl, h ▸ l₂.lbl⟩ ∈ D

theorem LabRel.mono {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {D D' : Ctx L₁ L₂}
    (hD : ∀ p ∈ D, p ∈ D') {locTys : List WValTy}
    {l₁ : WLabel V₁ L₁ locTys} {l₂ : WLabel V₂ L₂ locTys} :
    LabRel D locTys l₁ l₂ → LabRel D' locTys l₁ l₂
  | ⟨h, hm⟩ => ⟨h, hD _ hm⟩

/-- Relational correspondence across label stacks. -/
@[expose, reducible] def LabsRel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} (D : Ctx L₁ L₂)
    (locTys : List WValTy)
    (ls₁ : List (WLabel V₁ L₁ locTys)) (ls₂ : List (WLabel V₂ L₂ locTys)) : Prop :=
  ListRel (LabRel D locTys) ls₁ ls₂

theorem LabsRel.mono {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {D D' : Ctx L₁ L₂}
    (hD : ∀ p ∈ D, p ∈ D') {locTys : List WValTy}
    {ls₁ : List (WLabel V₁ L₁ locTys)} {ls₂ : List (WLabel V₂ L₂ locTys)}
    (hls : LabsRel D locTys ls₁ ls₂) : LabsRel D' locTys ls₁ ls₂ :=
  hls.imp fun _ _ h => LabRel.mono hD h

/-- Monotonicity-aware well-formedness invariant on lowering continuations. -/
@[expose] def ContWf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} (locTys retTys : List WValTy)
    (G : Ctx V₁ V₂) (D : Ctx L₁ L₂)
    (k₁ : WCont V₁ L₁ locTys retTys) (k₂ : WCont V₂ L₂ locTys retTys) : Prop :=
  ∀ {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂},
    (∀ p ∈ G, p ∈ G') → (∀ p ∈ D, p ∈ D') →
    ∀ {f₁ : Arg V₁ T.i64} {f₂ : Arg V₂ T.i64}
      {locs₁ : Tup (Arg V₁) (locTys.map WValTy.toTy)}
      {locs₂ : Tup (Arg V₂) (locTys.map WValTy.toTy)}
      {stk₁ : List (SVal V₁)} {stk₂ : List (SVal V₂)},
      ArgRel G' T.i64 f₁ f₂ → TRel (ArgRel G') locs₁ locs₂ → StkRel G' stk₁ stk₂ →
      Wf G' D' (k₁ f₁ locs₁ stk₁) (k₂ f₂ locs₂ stk₂)

theorem ContWf.mono {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {locTys retTys : List WValTy}
    {G G' : Ctx V₁ V₂} {D D' : Ctx L₁ L₂}
    (hG : ∀ p ∈ G, p ∈ G') (hD : ∀ p ∈ D, p ∈ D')
    {k₁ : WCont V₁ L₁ locTys retTys} {k₂ : WCont V₂ L₂ locTys retTys}
    (hk : ContWf locTys retTys G D k₁ k₂) : ContWf locTys retTys G' D' k₁ k₂ :=
  fun hG' hD' => hk (fun p hp => hG' p (hG p hp)) (fun p hp => hD' p (hD p hp))

theorem zeroArgs_rel {V₁ V₂ : Ty → Type} (G : Ctx V₁ V₂) :
    ∀ ts, TRel (ArgRel G) (zeroArgs (V := V₁) ts) (zeroArgs (V := V₂) ts)
  | [] => .nil
  | t :: ts => .cons (by cases t <;> exact .imm _) (zeroArgs_rel G ts)

theorem appendZeroLocals_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} :
    ∀ (ps ls : List WValTy) {a₁ : Tup (Arg V₁) (ps.map WValTy.toTy)}
      {a₂ : Tup (Arg V₂) (ps.map WValTy.toTy)},
      TRel (ArgRel G) a₁ a₂ →
      TRel (ArgRel G) (appendZeroLocals ps ls a₁) (appendZeroLocals ps ls a₂)
  | [], ls, (), (), _ => zeroArgs_rel G ls
  | _ :: ps, ls, (_, _), (_, _), .cons ha has => .cons ha (appendZeroLocals_rel ps ls has)

theorem varsTup_rel_nil {V₁ V₂ : Ty → Type} :
    ∀ {ts : List Ty} {xs₁ : Tup V₁ ts} {xs₂ : Tup V₂ ts},
      TRel (ArgRel (Tup.zip xs₁ xs₂)) (varsTup xs₁) (varsTup xs₂)
  | [], (), () => .nil
  | _ :: _, (_, _), (_, _) =>
    .cons (.var List.mem_cons_self)
      (TRel_ArgRel_mono (fun _ hp => List.mem_cons_of_mem _ hp) varsTup_rel_nil)

theorem varsTup_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} :
    ∀ {ts : List Ty} {xs₁ : Tup V₁ ts} {xs₂ : Tup V₂ ts},
      TRel (ArgRel (Tup.zip xs₁ xs₂ ++ G)) (varsTup xs₁) (varsTup xs₂)
  | [], (), () => .nil
  | _ :: _, (_, _), (_, _) =>
    .cons (.var List.mem_cons_self)
      (TRel_ArgRel_mono (fun _ hp => List.mem_cons_of_mem _ hp) varsTup_rel)

theorem tupAppend_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} :
    ∀ {as bs : List Ty} {a₁ : Tup (Arg V₁) as} {a₂ : Tup (Arg V₂) as}
      {b₁ : Tup (Arg V₁) bs} {b₂ : Tup (Arg V₂) bs},
      TRel (ArgRel G) a₁ a₂ → TRel (ArgRel G) b₁ b₂ →
      TRel (ArgRel G) (tupAppend a₁ b₁) (tupAppend a₂ b₂)
  | [], _, (), (), _, _, _, hb => hb
  | _ :: _, _, (_, _), (_, _), _, _, .cons ha has, hb => .cons ha (tupAppend_rel has hb)

theorem tupSplit_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} :
    ∀ {as bs : List Ty} {zs₁ : Tup (Arg V₁) (as ++ bs)} {zs₂ : Tup (Arg V₂) (as ++ bs)},
      TRel (ArgRel G) zs₁ zs₂ →
      TRel (ArgRel G) (tupSplit (as := as) (bs := bs) zs₁).1
                      (tupSplit (as := as) (bs := bs) zs₂).1 ∧
      TRel (ArgRel G) (tupSplit (as := as) (bs := bs) zs₁).2
                      (tupSplit (as := as) (bs := bs) zs₂).2
  | [], _, _, _, hz => ⟨.nil, hz⟩
  | _ :: _, _, (_, _), (_, _), .cons ha hzs =>
    let ⟨h1, h2⟩ := tupSplit_rel hzs
    ⟨.cons ha h1, h2⟩

theorem popAny_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂}
    {s₁ : List (SVal V₁)} {s₂ : List (SVal V₂)} (hs : StkRel G s₁ s₂) :
    (s₁ = [] ∧ s₂ = []) ∨
    (∃ v₁ v₂ t₁ t₂, s₁ = v₁ :: t₁ ∧ s₂ = v₂ :: t₂ ∧ SValRel G v₁ v₂ ∧ StkRel G t₁ t₂) := by
  cases hs with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons hv hr => exact Or.inr ⟨_, _, _, _, rfl, rfl, hv, hr⟩

theorem pop32_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} {s₁ : List (SVal V₁)} {s₂ : List (SVal V₂)}
    (hs : StkRel G s₁ s₂) :
    (pop32 s₁ = none ∧ pop32 s₂ = none) ∨
    (∃ a₁ a₂ r₁ r₂, pop32 s₁ = some (a₁, r₁) ∧ pop32 s₂ = some (a₂, r₂) ∧
      ArgRel G T.i32 a₁ a₂ ∧ StkRel G r₁ r₂) := by
  rcases popAny_rel hs with ⟨rfl, rfl⟩ | ⟨v₁, v₂, t₁, t₂, rfl, rfl, hv, hr⟩
  · left; exact ⟨rfl, rfl⟩
  · cases v₁ <;> cases v₂ <;> simp only [SValRel] at hv
    · right; exact ⟨_, _, _, _, rfl, rfl, hv, hr⟩
    · left; exact ⟨rfl, rfl⟩

theorem pop64_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} {s₁ : List (SVal V₁)} {s₂ : List (SVal V₂)}
    (hs : StkRel G s₁ s₂) :
    (pop64 s₁ = none ∧ pop64 s₂ = none) ∨
    (∃ a₁ a₂ r₁ r₂, pop64 s₁ = some (a₁, r₁) ∧ pop64 s₂ = some (a₂, r₂) ∧
      ArgRel G T.i64 a₁ a₂ ∧ StkRel G r₁ r₂) := by
  rcases popAny_rel hs with ⟨rfl, rfl⟩ | ⟨v₁, v₂, t₁, t₂, rfl, rfl, hv, hr⟩
  · left; exact ⟨rfl, rfl⟩
  · cases v₁ <;> cases v₂ <;> simp only [SValRel] at hv
    · left; exact ⟨rfl, rfl⟩
    · right; exact ⟨_, _, _, _, rfl, rfl, hv, hr⟩

theorem popExpectS_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} (t : WValTy)
    {s₁ : List (SVal V₁)} {s₂ : List (SVal V₂)} (hs : StkRel G s₁ s₂) :
    (popExpectS t s₁ = none ∧ popExpectS t s₂ = none) ∨
    (∃ a₁ a₂ r₁ r₂, popExpectS t s₁ = some (a₁, r₁) ∧ popExpectS t s₂ = some (a₂, r₂) ∧
      ArgRel G t.toTy a₁ a₂ ∧ StkRel G r₁ r₂) := by
  rcases popAny_rel hs with ⟨rfl, rfl⟩ | ⟨v₁, v₂, t₁, t₂, rfl, rfl, hv, hr⟩
  · cases t <;> left <;> exact ⟨rfl, rfl⟩
  · cases t <;> cases v₁ <;> cases v₂ <;> simp only [SValRel] at hv
    · right; exact ⟨_, _, _, _, rfl, rfl, hv, hr⟩
    · left; exact ⟨rfl, rfl⟩
    · left; exact ⟨rfl, rfl⟩
    · right; exact ⟨_, _, _, _, rfl, rfl, hv, hr⟩

theorem popArgsAux_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} :
    ∀ (ts : List WValTy) {s₁ : List (SVal V₁)} {s₂ : List (SVal V₂)},
      StkRel G s₁ s₂ →
      (popArgsAux ts s₁ = none ∧ popArgsAux ts s₂ = none) ∨
      (∃ a₁ a₂ r₁ r₂, popArgsAux ts s₁ = some (a₁, r₁) ∧ popArgsAux ts s₂ = some (a₂, r₂) ∧
        TRel (ArgRel G) a₁ a₂ ∧ StkRel G r₁ r₂)
  | [], s₁, s₂, hs => Or.inr ⟨(), (), s₁, s₂, rfl, rfl, .nil, hs⟩
  | t :: ts, s₁, s₂, hs => by
    rcases popArgsAux_rel ts hs with ⟨hn1, hn2⟩ | ⟨t₁, t₂, u₁, u₂, hp1, hp2, ht, hu⟩
    · left; simp [popArgsAux, hn1, hn2]
    · rcases popExpectS_rel t hu with ⟨hn1, hn2⟩ | ⟨hd₁, hd₂, r₁, r₂, he1, he2, hhd, hr⟩
      · left; simp [popArgsAux, hp1, hp2, hn1, hn2]
      · right; exact ⟨(hd₁, t₁), (hd₂, t₂), r₁, r₂,
          by simp [popArgsAux, hp1, he1], by simp [popArgsAux, hp2, he2],
          .cons hhd ht, hr⟩

theorem pushArgsAux_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} :
    ∀ (ts : List WValTy) {a₁ : Tup (Arg V₁) (ts.map WValTy.toTy)}
      {a₂ : Tup (Arg V₂) (ts.map WValTy.toTy)}
      {s₁ : List (SVal V₁)} {s₂ : List (SVal V₂)},
      TRel (ArgRel G) a₁ a₂ → StkRel G s₁ s₂ →
      StkRel G (pushArgsAux ts a₁ s₁) (pushArgsAux ts a₂ s₂)
  | [], (), (), _, _, .nil, hs => hs
  | t :: ts, (_, _), (_, _), _, _, .cons ha has, hs =>
    pushArgsAux_rel ts has (.cons (SValRel.ofArg t ha) hs)

theorem getLocal_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} :
    ∀ (ts : List WValTy) {l₁ : Tup (Arg V₁) (ts.map WValTy.toTy)}
      {l₂ : Tup (Arg V₂) (ts.map WValTy.toTy)} (idx : Nat),
      TRel (ArgRel G) l₁ l₂ →
      (getLocal ts l₁ idx = none ∧ getLocal ts l₂ idx = none) ∨
      (∃ v₁ v₂, getLocal ts l₁ idx = some v₁ ∧ getLocal ts l₂ idx = some v₂ ∧ SValRel G v₁ v₂)
  | [], (), (), _, _ => Or.inl ⟨rfl, rfl⟩
  | t :: _, (_, _), (_, _), 0, .cons ha _ =>
    Or.inr ⟨_, _, rfl, rfl, SValRel.ofArg t ha⟩
  | _ :: ts, (_, _), (_, _), idx + 1, .cons _ hls =>
    getLocal_rel ts idx hls

theorem setLocal_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} :
    ∀ (ts : List WValTy) {l₁ : Tup (Arg V₁) (ts.map WValTy.toTy)}
      {l₂ : Tup (Arg V₂) (ts.map WValTy.toTy)} (idx : Nat) {v₁ : SVal V₁} {v₂ : SVal V₂},
      TRel (ArgRel G) l₁ l₂ → SValRel G v₁ v₂ →
      (setLocal ts l₁ idx v₁ = none ∧ setLocal ts l₂ idx v₂ = none) ∨
      (∃ l₁' l₂', setLocal ts l₁ idx v₁ = some l₁' ∧ setLocal ts l₂ idx v₂ = some l₂' ∧
        TRel (ArgRel G) l₁' l₂')
  | [], (), (), _, _, _, _, _ => Or.inl ⟨rfl, rfl⟩
  | .i32 :: _, (_, _), (_, _), 0, v₁, v₂, .cons _ hls, hv => by
    cases v₁ <;> cases v₂ <;> simp only [SValRel] at hv
    · exact Or.inr ⟨_, _, rfl, rfl, .cons hv hls⟩
    · exact Or.inl ⟨rfl, rfl⟩
  | .i64 :: _, (_, _), (_, _), 0, v₁, v₂, .cons _ hls, hv => by
    cases v₁ <;> cases v₂ <;> simp only [SValRel] at hv
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨_, _, rfl, rfl, .cons hv hls⟩
  | _ :: ts, (_, _), (_, _), idx + 1, v₁, v₂, .cons ha hls, hv => by
    rcases setLocal_rel ts idx hls hv with ⟨hn1, hn2⟩ | ⟨l₁', l₂', hs1, hs2, hr⟩
    · exact Or.inl ⟨by simp [setLocal, hn1], by simp [setLocal, hn2]⟩
    · exact Or.inr ⟨_, _, by simp [setLocal, hs1], by simp [setLocal, hs2], .cons ha hr⟩

theorem LabsRel_getElem?_rel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {D : Ctx L₁ L₂}
    {locTys : List WValTy} {labs₁ : List (WLabel V₁ L₁ locTys)}
    {labs₂ : List (WLabel V₂ L₂ locTys)} (hlabs : LabsRel D locTys labs₁ labs₂) :
    ∀ (depth : Nat),
      (labs₁[depth]? = none ∧ labs₂[depth]? = none) ∨
      (∃ l₁ l₂, labs₁[depth]? = some l₁ ∧ labs₂[depth]? = some l₂ ∧ LabRel D locTys l₁ l₂) := by
  induction hlabs with
  | nil => intro depth; left; simp
  | cons hd _ ih =>
    intro depth
    cases depth with
    | zero => right; exact ⟨_, _, rfl, rfl, hd⟩
    | succ d => simpa using ih d

theorem wf_let1 {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a u : Ty} (code : OpCode [a] [u])
    {x₁ : Arg V₁ a} {x₂ : Arg V₂ a} (hx : ArgRel G a x₁ x₂)
    {k₁ : Tup V₁ [u] → Expr V₁ L₁ rs} {k₂ : Tup V₂ [u] → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' u (.var y₁) (.var y₂) →
      Wf G' D (k₁ (y₁, ())) (k₂ (y₂, ()))) :
    Wf G D (.let_ (.mk code (x₁, ())) k₁) (.let_ (.mk code (x₂, ())) k₂) :=
  .let_ (.mk code (.cons hx .nil)) fun ⟨r₁, ()⟩ ⟨r₂, ()⟩ =>
    hk (fun _ hp => List.mem_cons_of_mem _ hp) r₁ r₂ (.var List.mem_cons_self)

theorem wf_let2 {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a b u : Ty} (code : OpCode [a, b] [u])
    {x₁ : Arg V₁ a} {x₂ : Arg V₂ a} {y₁ : Arg V₁ b} {y₂ : Arg V₂ b}
    (hx : ArgRel G a x₁ x₂) (hy : ArgRel G b y₁ y₂)
    {k₁ : Tup V₁ [u] → Expr V₁ L₁ rs} {k₂ : Tup V₂ [u] → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r₁ r₂, ArgRel G' u (.var r₁) (.var r₂) →
      Wf G' D (k₁ (r₁, ())) (k₂ (r₂, ()))) :
    Wf G D (.let_ (.mk code (x₁, y₁, ())) k₁) (.let_ (.mk code (x₂, y₂, ())) k₂) :=
  .let_ (.mk code (.cons hx (.cons hy .nil))) fun ⟨r₁, ()⟩ ⟨r₂, ()⟩ =>
    hk (fun _ hp => List.mem_cons_of_mem _ hp) r₁ r₂ (.var List.mem_cons_self)

theorem wf_let3 {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a b c u : Ty} (code : OpCode [a, b, c] [u])
    {x₁ : Arg V₁ a} {x₂ : Arg V₂ a} {y₁ : Arg V₁ b} {y₂ : Arg V₂ b}
    {z₁ : Arg V₁ c} {z₂ : Arg V₂ c}
    (hx : ArgRel G a x₁ x₂) (hy : ArgRel G b y₁ y₂) (hz : ArgRel G c z₁ z₂)
    {k₁ : Tup V₁ [u] → Expr V₁ L₁ rs} {k₂ : Tup V₂ [u] → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r₁ r₂, ArgRel G' u (.var r₁) (.var r₂) →
      Wf G' D (k₁ (r₁, ())) (k₂ (r₂, ()))) :
    Wf G D (.let_ (.mk code (x₁, y₁, z₁, ())) k₁) (.let_ (.mk code (x₂, y₂, z₂, ())) k₂) :=
  .let_ (.mk code (.cons hx (.cons hy (.cons hz .nil)))) fun ⟨r₁, ()⟩ ⟨r₂, ()⟩ =>
    hk (fun _ hp => List.mem_cons_of_mem _ hp) r₁ r₂ (.var List.mem_cons_self)

theorem wf_load {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (t : Ty)
    {a₁ : Arg V₁ T.i64} {a₂ : Arg V₂ T.i64} (ha : ArgRel G T.i64 a₁ a₂)
    {k₁ : V₁ t → Expr V₁ L₁ rs} {k₂ : V₂ t → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ v₁ v₂, ArgRel G' t (.var v₁) (.var v₂) →
      Wf G' D (k₁ v₁) (k₂ v₂)) :
    Wf G D (.load t a₁ k₁) (.load t a₂ k₂) :=
  .load t ha fun v₁ v₂ =>
    hk (fun _ hp => List.mem_cons_of_mem _ hp) v₁ v₂ (.var List.mem_cons_self)

theorem mkTrapExpr_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (retTys : List WValTy) (code : BitVec 32)
    {f₁ : Arg V₁ T.i64} {f₂ : Arg V₂ T.i64} (hf : ArgRel G T.i64 f₁ f₂) :
    Wf G D (mkTrapExpr (L := L₁) retTys code f₁) (mkTrapExpr (L := L₂) retTys code f₂) :=
  .ret (.cons (.imm _) (.cons hf (zeroArgs_rel G retTys)))

theorem emitLoadVmCtx_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {vc₁ : Arg V₁ T.i64} {vc₂ : Arg V₂ T.i64}
    (hvc : ArgRel G T.i64 vc₁ vc₂)
    {k₁ : Arg V₁ T.i64 → Arg V₁ T.i64 → Expr V₁ L₁ rs}
    {k₂ : Arg V₂ T.i64 → Arg V₂ T.i64 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ mb₁ mb₂ ml₁ ml₂,
      ArgRel G' T.i64 mb₁ mb₂ → ArgRel G' T.i64 ml₁ ml₂ → Wf G' D (k₁ mb₁ ml₁) (k₂ mb₂ ml₂)) :
    Wf G D (emitLoadVmCtx vc₁ k₁) (emitLoadVmCtx vc₂ k₂) := by
  refine wf_load T.i64 hvc fun h1 mb₁ mb₂ hmb =>
    wf_let2 (.add T.i64) (ArgRel.mono h1 hvc) (.imm _) fun h2 _ _ hpl =>
    wf_load T.i64 hpl fun h3 ml₁ ml₂ hml =>
    let h123 : ∀ p ∈ G, p ∈ _ := fun p hp => h3 p (h2 p (h1 p hp))
    hk h123 _ _ _ _ (ArgRel.mono (fun p hp => h3 p (h2 p hp)) hmb) hml

theorem emitMemBounds_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (retTys : List WValTy)
    {vc₁ f₁ : Arg V₁ T.i64} {vc₂ f₂ : Arg V₂ T.i64}
    (hvc : ArgRel G T.i64 vc₁ vc₂) (hf : ArgRel G T.i64 f₁ f₂)
    {i₁ : Arg V₁ T.i32} {i₂ : Arg V₂ T.i32} (hi : ArgRel G T.i32 i₁ i₂)
    (arg : WMemArg) (bytes : Nat)
    {k₁ : Arg V₁ T.i64 → Expr V₁ L₁ (wasmRetSig retTys)}
    {k₂ : Arg V₂ T.i64 → Expr V₂ L₂ (wasmRetSig retTys)}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ p₁ p₂, ArgRel G' T.i64 p₁ p₂ →
      Wf G' D (k₁ p₁) (k₂ p₂)) :
    Wf G D (emitMemBounds retTys vc₁ f₁ i₁ arg bytes k₁)
           (emitMemBounds retTys vc₂ f₂ i₂ arg bytes k₂) := by
  refine emitLoadVmCtx_wf hvc fun hvm mb₁ mb₂ ml₁ ml₂ hmb hml => ?_
  refine wf_let1 (.zext 32 64) (ArgRel.mono hvm hi) fun h1 _ _ hi64 =>
    wf_let2 (.add T.i64) hi64 (.imm _) fun h2 _ _ hea =>
    wf_let2 (.add T.i64) hea (.imm _) fun h3 _ _ hend => ?_
  have h13 : ∀ q ∈ _, q ∈ _ := fun q hq => h3 q (h2 q (h1 q hq))
  refine wf_let2 (.cmp .ule T.i64) hend (ArgRel.mono h13 hml) fun h4 _ _ hib => ?_
  have h14 : ∀ q ∈ _, q ∈ _ := fun q hq => h4 q (h13 q hq)
  exact .jnz hib
    (wf_let2 (.add T.i64) (ArgRel.mono h14 hmb)
      (ArgRel.mono (fun q hq => h4 q (h3 q hq)) hea)
      fun h5 _ _ hptr => hk (fun q hq => h5 q (h14 q (hvm q hq))) _ _ hptr)
    (mkTrapExpr_wf retTys 1#32 (ArgRel.mono (fun q hq => h14 q (hvm q hq)) hf))

theorem emitMemSize_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {vc₁ : Arg V₁ T.i64} {vc₂ : Arg V₂ T.i64}
    (hvc : ArgRel G T.i64 vc₁ vc₂)
    {k₁ : Arg V₁ T.i32 → Expr V₁ L₁ rs} {k₂ : Arg V₂ T.i32 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ p₁ p₂, ArgRel G' T.i32 p₁ p₂ →
      Wf G' D (k₁ p₁) (k₂ p₂)) :
    Wf G D (emitMemSize vc₁ k₁) (emitMemSize vc₂ k₂) := by
  refine wf_let2 (.add T.i64) hvc (.imm _) fun h1 _ _ hpl =>
    wf_load T.i64 hpl fun h2 _ _ hml =>
    wf_let2 (.lshr T.i64) hml (.imm _) fun h3 _ _ hp64 =>
    wf_let1 (.trunc 64 32) hp64 fun h4 _ _ hp32 =>
      hk (fun q hq => h4 q (h3 q (h2 q (h1 q hq)))) _ _ hp32

theorem emitMemZeroPage_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {p₁ : Arg V₁ T.i64} {p₂ : Arg V₂ T.i64}
    (hp : ArgRel G T.i64 p₁ p₂) {k₁ : Expr V₁ L₁ rs} {k₂ : Expr V₂ L₂ rs}
    (hk : Wf G D k₁ k₂) :
    Wf G D (emitMemZeroPage p₁ k₁) (emitMemZeroPage p₂ k₂) := by
  refine .group (sig := [[]]) ?_ ?_
  · intro ⟨j₁, ()⟩ ⟨j₂, ()⟩
    exact .cons (fun _ _ => hk.weaken_D fun _ h => List.mem_append_right _ h) .nil
  · intro ⟨j₁, ()⟩ ⟨j₂, ()⟩
    have hjD : ⟨[], j₁, j₂⟩ ∈ Tup.zip (as := [[]]) (j₁, ()) (j₂, ()) ++ D := List.mem_cons_self
    refine .group (sig := [[T.i64, T.i64]]) ?_ ?_
    · intro ⟨l₁, ()⟩ ⟨l₂, ()⟩
      refine .cons (fun z₁ z₂ => ?_) .nil
      rcases z₁ with ⟨zr₁, zp₁, ⟨⟩⟩
      rcases z₂ with ⟨zr₂, zp₂, ⟨⟩⟩
      let Gz := Tup.zip (as := [T.i64, T.i64]) (zr₁, zp₁, ()) (zr₂, zp₂, ()) ++ G
      let Dz := Tup.zip (as := [[T.i64, T.i64]]) (l₁, ()) (l₂, ()) ++
        (Tup.zip (as := [[]]) (j₁, ()) (j₂, ()) ++ D)
      have hlD : ⟨[T.i64, T.i64], l₁, l₂⟩ ∈ Dz := List.mem_cons_self
      have hjDz : ⟨[], j₁, j₂⟩ ∈ Dz := List.mem_cons_of_mem _ hjD
      have hzr : ArgRel Gz T.i64 (.var zr₁) (.var zr₂) := .var List.mem_cons_self
      have hzp : ArgRel Gz T.i64 (.var zp₁) (.var zp₂) :=
        .var (List.mem_cons_of_mem _ List.mem_cons_self)
      refine wf_let2 (.cmp .eq T.i64) hzr (.imm _) fun h1 _ _ hzd =>
        .jnz hzd (.jump hjDz .nil)
          (.store (ArgRel.imm (t := T.i64) 0#64) (ArgRel.mono h1 hzp)
            (wf_let2 (.sub T.i64) (ArgRel.mono h1 hzr) (.imm _) fun h2 _ _ hzrn =>
             wf_let2 (.add T.i64) (ArgRel.mono (fun q h => h2 q (h1 q h)) hzp) (.imm _)
               fun h3 _ _ hzpn =>
               .jump hlD (.cons (ArgRel.mono h3 hzrn) (.cons hzpn .nil))))
    · intro ⟨l₁, ()⟩ ⟨l₂, ()⟩
      exact .jump List.mem_cons_self (.cons (.imm _) (.cons hp .nil))

theorem emitMemGrowLoop_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (retTys : List WValTy)
    {j₁ : L₁ [T.i64, T.i32]} {j₂ : L₂ [T.i64, T.i32]} (hj : ⟨[T.i64, T.i32], j₁, j₂⟩ ∈ D)
    {pl₁ nl₁ f₁ d₁ sp₁ : Arg V₁ T.i64} {pl₂ nl₂ f₂ d₂ sp₂ : Arg V₂ T.i64}
    {op₁ : Arg V₁ T.i32} {op₂ : Arg V₂ T.i32}
    (hpl : ArgRel G T.i64 pl₁ pl₂) (hnl : ArgRel G T.i64 nl₁ nl₂) (hop : ArgRel G T.i32 op₁ op₂)
    (hf : ArgRel G T.i64 f₁ f₂) (hd : ArgRel G T.i64 d₁ d₂) (hsp : ArgRel G T.i64 sp₁ sp₂) :
    Wf G D (emitMemGrowLoop retTys j₁ pl₁ nl₁ op₁ f₁ d₁ sp₁)
           (emitMemGrowLoop retTys j₂ pl₂ nl₂ op₂ f₂ d₂ sp₂) := by
  refine .group (sig := [[T.i64, T.i64, T.i64]]) ?_ ?_
  · intro ⟨l₁, ()⟩ ⟨l₂, ()⟩
    refine .cons (fun p₁ p₂ => ?_) .nil
    rcases p₁ with ⟨pf₁, pr₁, pp₁, ⟨⟩⟩
    rcases p₂ with ⟨pf₂, pr₂, pp₂, ⟨⟩⟩
    let Gp := Tup.zip (as := [T.i64, T.i64, T.i64]) (pf₁, pr₁, pp₁, ()) (pf₂, pr₂, pp₂, ()) ++ G
    let Dp := Tup.zip (as := [[T.i64, T.i64, T.i64]]) (l₁, ()) (l₂, ()) ++ D
    have hGGp : ∀ q ∈ G, q ∈ Gp := fun _ h =>
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
    have hlD : ⟨[T.i64, T.i64, T.i64], l₁, l₂⟩ ∈ Dp := List.mem_cons_self
    have hjDp : ⟨[T.i64, T.i32], j₁, j₂⟩ ∈ Dp := List.mem_cons_of_mem _ hj
    have hpf : ArgRel Gp T.i64 (.var pf₁) (.var pf₂) := .var List.mem_cons_self
    have hpr : ArgRel Gp T.i64 (.var pr₁) (.var pr₂) :=
      .var (List.mem_cons_of_mem _ List.mem_cons_self)
    have hpp : ArgRel Gp T.i64 (.var pp₁) (.var pp₂) :=
      .var (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    refine wf_let2 (.cmp .eq T.i64) hpr (.imm _) fun h1 _ _ hpd =>
      .jnz hpd
        (.store (ArgRel.mono (fun q h => h1 q (hGGp q h)) hnl)
          (ArgRel.mono (fun q h => h1 q (hGGp q h)) hpl)
          (.jump hjDp (.cons (ArgRel.mono h1 hpf)
            (.cons (ArgRel.mono (fun q h => h1 q (hGGp q h)) hop) .nil))))
        (wf_let2 (.cmp .eq T.i64) (ArgRel.mono h1 hpf) (.imm _) fun h2 _ _ hof =>
          .jnz hof (mkTrapExpr_wf retTys 2#32 (ArgRel.mono (fun q h => h2 q (h1 q h)) hpf))
            (wf_let2 (.sub T.i64) (ArgRel.mono (fun q h => h2 q (h1 q h)) hpf) (.imm _)
              fun h3 _ _ hfn =>
              have h13 : ∀ q ∈ Gp, q ∈ _ := fun q h => h3 q (h2 q (h1 q h))
              emitMemZeroPage_wf (ArgRel.mono h13 hpp)
                (wf_let2 (.sub T.i64) (ArgRel.mono h13 hpr) (.imm _) fun h4 _ _ hprn =>
                 wf_let2 (.add T.i64) (ArgRel.mono (fun q h => h4 q (h13 q h)) hpp) (.imm _)
                   fun h5 _ _ hppn =>
                   .jump hlD (.cons (ArgRel.mono (fun q h => h5 q (h4 q h)) hfn)
                     (.cons (ArgRel.mono h5 hprn) (.cons hppn .nil))))))
  · intro ⟨l₁, ()⟩ ⟨l₂, ()⟩
    exact .jump List.mem_cons_self (.cons hf (.cons hd (.cons hsp .nil)))

theorem emitMemGrow_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (retTys : List WValTy) (memMaxBytes : BitVec 64)
    {vc₁ f₁ : Arg V₁ T.i64} {vc₂ f₂ : Arg V₂ T.i64}
    (hvc : ArgRel G T.i64 vc₁ vc₂) (hf : ArgRel G T.i64 f₁ f₂)
    {d₁ : Arg V₁ T.i32} {d₂ : Arg V₂ T.i32} (hd : ArgRel G T.i32 d₁ d₂)
    {k₁ : Arg V₁ T.i64 → Arg V₁ T.i32 → Expr V₁ L₁ (wasmRetSig retTys)}
    {k₂ : Arg V₂ T.i64 → Arg V₂ T.i32 → Expr V₂ L₂ (wasmRetSig retTys)}
    (hk : ∀ {G' D'}, (∀ p ∈ G, p ∈ G') → (∀ p ∈ D, p ∈ D') →
      ∀ {f₁' f₂' r₁ r₂}, ArgRel G' T.i64 f₁' f₂' → ArgRel G' T.i32 r₁ r₂ →
      Wf G' D' (k₁ f₁' r₁) (k₂ f₂' r₂)) :
    Wf G D (emitMemGrow retTys memMaxBytes vc₁ f₁ d₁ k₁)
           (emitMemGrow retTys memMaxBytes vc₂ f₂ d₂ k₂) := by
  refine .group (sig := [[T.i64, T.i32]]) ?_ ?_
  · intro ⟨j₁, ()⟩ ⟨j₂, ()⟩
    refine .cons (fun xs₁ xs₂ => ?_) .nil
    rcases xs₁ with ⟨fx₁, rx₁, ⟨⟩⟩
    rcases xs₂ with ⟨fx₂, rx₂, ⟨⟩⟩
    exact hk (fun _ h => List.mem_append_right _ h) (fun _ h => List.mem_append_right _ h)
      (.var List.mem_cons_self) (.var (List.mem_cons_of_mem _ List.mem_cons_self))
  · intro ⟨j₁, ()⟩ ⟨j₂, ()⟩
    have hjD : ⟨[T.i64, T.i32], j₁, j₂⟩ ∈
        Tup.zip (as := [[T.i64, T.i32]]) (j₁, ()) (j₂, ()) ++ D := List.mem_cons_self
    refine wf_load T.i64 hvc fun h1 _ _ hmb =>
      wf_let2 (.add T.i64) (ArgRel.mono h1 hvc) (.imm _) fun h2 _ _ hpl =>
      wf_load T.i64 hpl fun h3 _ _ hml =>
      wf_let2 (.add T.i64) (ArgRel.mono (fun q h => h3 q (h2 q (h1 q h))) hvc) (.imm _)
        fun h4 _ _ hpc =>
      wf_load T.i64 hpc fun h5 _ _ hmc =>
      wf_let2 (.lshr T.i64) (ArgRel.mono (fun q h => h5 q (h4 q h)) hml) (.imm _)
        fun h6 _ _ hop64 =>
      wf_let1 (.trunc 64 32) hop64 fun h7 _ _ hop32 => ?_
    have h17 : ∀ q ∈ G, q ∈ _ :=
      fun q h => h7 q (h6 q (h5 q (h4 q (h3 q (h2 q (h1 q h))))))
    refine wf_let2 (.cmp .eq T.i32) (ArgRel.mono h17 hd) (.imm _) fun h8 _ _ hiz =>
      .jnz hiz (.jump hjD (.cons (ArgRel.mono (fun q h => h8 q (h17 q h)) hf)
        (.cons (ArgRel.mono h8 hop32) .nil))) ?_
    refine wf_let1 (.zext 32 64) (ArgRel.mono (fun q h => h8 q (h17 q h)) hd) fun h9 _ _ hd64 =>
      wf_let2 (.shl T.i64) hd64 (.imm _) fun h10 _ _ hgb => ?_
    have hml9 : ArgRel _ T.i64 _ _ :=
      ArgRel.mono (fun q h => h10 q (h9 q (h8 q (h7 q (h6 q (h5 q (h4 q h))))))) hml
    refine wf_let2 (.add T.i64) hml9 hgb fun h11 _ _ hnl =>
      wf_let2 (.cmp .ule T.i64) (ArgRel.mono h11 hml9) hnl fun h12 _ _ hnw =>
      wf_let2 (.cmp .ule T.i64) (ArgRel.mono h12 hnl)
        (ArgRel.mono (fun q h => h12 q (h11 q (h10 q (h9 q (h8 q (h7 q (h6 q h))))))) hmc)
        fun h13 _ _ hlc =>
      wf_let2 (.cmp .ule T.i64) (ArgRel.mono (fun q h => h13 q (h12 q h)) hnl) (.imm _)
        fun h14 _ _ hlm =>
      wf_let2 (.and .bool) (ArgRel.mono (fun q h => h14 q (h13 q h)) hnw)
        (ArgRel.mono h14 hlc) fun h15 _ _ ho1 =>
      wf_let2 (.and .bool) ho1 (ArgRel.mono h15 hlm) fun h16 _ _ hoa => ?_
    have hG16 : ∀ q ∈ G, q ∈ _ := fun q h =>
      h16 q (h15 q (h14 q (h13 q (h12 q (h11 q (h10 q (h9 q (h8 q (h17 q h)))))))))
    have hmb16 : ArgRel _ T.i64 _ _ := ArgRel.mono
      (fun q h => h16 q (h15 q (h14 q (h13 q (h12 q (h11 q (h10 q (h9 q (h8 q
        (h7 q (h6 q (h5 q (h4 q (h3 q (h2 q h))))))))))))))) hmb
    have hml16 : ArgRel _ T.i64 _ _ := ArgRel.mono
      (fun q h => h16 q (h15 q (h14 q (h13 q (h12 q (h11 q h)))))) hml9
    have hpl16 : ArgRel _ T.i64 _ _ := ArgRel.mono
      (fun q h => h16 q (h15 q (h14 q (h13 q (h12 q (h11 q (h10 q (h9 q (h8 q
        (h7 q (h6 q (h5 q (h4 q (h3 q h)))))))))))))) hpl
    have hnl16 : ArgRel _ T.i64 _ _ := ArgRel.mono
      (fun q h => h16 q (h15 q (h14 q (h13 q (h12 q h))))) hnl
    have hop16 : ArgRel _ T.i32 _ _ := ArgRel.mono
      (fun q h => h16 q (h15 q (h14 q (h13 q (h12 q (h11 q (h10 q (h9 q (h8 q h))))))))) hop32
    have hd16 : ArgRel _ T.i64 _ _ := ArgRel.mono
      (fun q h => h16 q (h15 q (h14 q (h13 q (h12 q (h11 q (h10 q h))))))) hd64
    refine .jnz hoa
      (wf_let2 (.add T.i64) hmb16 hml16 fun h17' _ _ hsp =>
        emitMemGrowLoop_wf retTys hjD (ArgRel.mono h17' hpl16) (ArgRel.mono h17' hnl16)
          (ArgRel.mono h17' hop16) (ArgRel.mono (fun q h => h17' q (hG16 q h)) hf)
          (ArgRel.mono h17' hd16) hsp)
      (.jump hjD (.cons (ArgRel.mono hG16 hf) (.cons (.imm _) .nil)))

theorem emitMemFillLoop_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (retTys : List WValTy)
    {j₁ : L₁ [T.i64]} {j₂ : L₂ [T.i64]} (hj : ⟨[T.i64], j₁, j₂⟩ ∈ D)
    {bv₁ : Arg V₁ T.i8} {bv₂ : Arg V₂ T.i8}
    {f₁ n₁ dp₁ : Arg V₁ T.i64} {f₂ n₂ dp₂ : Arg V₂ T.i64}
    (hbv : ArgRel G T.i8 bv₁ bv₂) (hf : ArgRel G T.i64 f₁ f₂)
    (hn : ArgRel G T.i64 n₁ n₂) (hdp : ArgRel G T.i64 dp₁ dp₂) :
    Wf G D (emitMemFillLoop retTys j₁ bv₁ f₁ n₁ dp₁)
           (emitMemFillLoop retTys j₂ bv₂ f₂ n₂ dp₂) := by
  refine .group (sig := [[T.i64, T.i64, T.i64]]) ?_ ?_
  · intro ⟨l₁, ()⟩ ⟨l₂, ()⟩
    refine .cons (fun lxs₁ lxs₂ => ?_) .nil
    rcases lxs₁ with ⟨lf₁, lr₁, lp₁, ⟨⟩⟩
    rcases lxs₂ with ⟨lf₂, lr₂, lp₂, ⟨⟩⟩
    let Gl := Tup.zip (as := [T.i64, T.i64, T.i64]) (lf₁, lr₁, lp₁, ()) (lf₂, lr₂, lp₂, ()) ++ G
    let Dl := Tup.zip (as := [[T.i64, T.i64, T.i64]]) (l₁, ()) (l₂, ()) ++ D
    have hGGl : ∀ q ∈ G, q ∈ Gl := fun _ h =>
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
    have hlD : ⟨[T.i64, T.i64, T.i64], l₁, l₂⟩ ∈ Dl := List.mem_cons_self
    have hjDl : ⟨[T.i64], j₁, j₂⟩ ∈ Dl := List.mem_cons_of_mem _ hj
    have hlf : ArgRel Gl T.i64 (.var lf₁) (.var lf₂) := .var List.mem_cons_self
    have hlr : ArgRel Gl T.i64 (.var lr₁) (.var lr₂) :=
      .var (List.mem_cons_of_mem _ List.mem_cons_self)
    have hlp : ArgRel Gl T.i64 (.var lp₁) (.var lp₂) :=
      .var (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    refine wf_let2 (.cmp .eq T.i64) hlr (.imm _) fun h1 _ _ hid =>
      .jnz hid (.jump hjDl (.cons (ArgRel.mono h1 hlf) .nil))
        (wf_let2 (.cmp .eq T.i64) (ArgRel.mono h1 hlf) (.imm _) fun h2 _ _ hof =>
          .jnz hof (mkTrapExpr_wf retTys 2#32 (ArgRel.mono (fun q h => h2 q (h1 q h)) hlf))
            (wf_let2 (.sub T.i64) (ArgRel.mono (fun q h => h2 q (h1 q h)) hlf) (.imm _)
              fun h3 _ _ hfn =>
              have h13 : ∀ q ∈ Gl, q ∈ _ := fun q h => h3 q (h2 q (h1 q h))
              .store (ArgRel.mono (fun q h => h13 q (hGGl q h)) hbv) (ArgRel.mono h13 hlp)
                (wf_let2 (.sub T.i64) (ArgRel.mono h13 hlr) (.imm _) fun h4 _ _ hrn =>
                 wf_let2 (.add T.i64) (ArgRel.mono (fun q h => h4 q (h13 q h)) hlp) (.imm _)
                   fun h5 _ _ hpn =>
                   .jump hlD (.cons (ArgRel.mono (fun q h => h5 q (h4 q h)) hfn)
                     (.cons (ArgRel.mono h5 hrn) (.cons hpn .nil))))))
  · intro ⟨l₁, ()⟩ ⟨l₂, ()⟩
    exact .jump List.mem_cons_self (.cons hf (.cons hn (.cons hdp .nil)))

theorem emitMemFill_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (retTys : List WValTy)
    {vc₁ f₁ : Arg V₁ T.i64} {vc₂ f₂ : Arg V₂ T.i64}
    (hvc : ArgRel G T.i64 vc₁ vc₂) (hf : ArgRel G T.i64 f₁ f₂)
    {d₁ v₁ n₁ : Arg V₁ T.i32} {d₂ v₂ n₂ : Arg V₂ T.i32}
    (hd : ArgRel G T.i32 d₁ d₂) (hv : ArgRel G T.i32 v₁ v₂) (hn : ArgRel G T.i32 n₁ n₂)
    {k₁ : Arg V₁ T.i64 → Expr V₁ L₁ (wasmRetSig retTys)}
    {k₂ : Arg V₂ T.i64 → Expr V₂ L₂ (wasmRetSig retTys)}
    (hk : ∀ {G' D'}, (∀ p ∈ G, p ∈ G') → (∀ p ∈ D, p ∈ D') →
      ∀ {f₁' f₂'}, ArgRel G' T.i64 f₁' f₂' → Wf G' D' (k₁ f₁') (k₂ f₂')) :
    Wf G D (emitMemFill retTys vc₁ f₁ d₁ v₁ n₁ k₁)
           (emitMemFill retTys vc₂ f₂ d₂ v₂ n₂ k₂) := by
  refine emitLoadVmCtx_wf hvc fun hvm mb₁ mb₂ ml₁ ml₂ hmb hml => ?_
  have hG4 : ∀ q ∈ G, q ∈ _ := hvm
  refine wf_let1 (.zext 32 64) (ArgRel.mono hG4 hd) fun h1 _ _ hd64 =>
    wf_let1 (.zext 32 64) (ArgRel.mono (fun q h => h1 q (hG4 q h)) hn) fun h2 _ _ hn64 =>
    wf_let2 (.add T.i64) (ArgRel.mono h2 hd64) hn64 fun h3 _ _ hend => ?_
  have h13 : ∀ q ∈ _, q ∈ _ := fun q h => h3 q (h2 q (h1 q h))
  refine wf_let2 (.cmp .ule T.i64) hend (ArgRel.mono h13 hml) fun h4 _ _ hib => ?_
  have h14 : ∀ q ∈ _, q ∈ _ := fun q h => h4 q (h13 q h)
  have hG14 : ∀ q ∈ G, q ∈ _ := fun q h => h14 q (hG4 q h)
  refine .jnz hib ?_ (mkTrapExpr_wf retTys 1#32 (ArgRel.mono hG14 hf))
  refine wf_let1 (.trunc 32 8) (ArgRel.mono hG14 hv) fun h5 _ _ hbv =>
    wf_let2 (.add T.i64) (ArgRel.mono (fun q h => h5 q (h14 q h)) hmb)
      (ArgRel.mono (fun q h => h5 q (h4 q (h3 q (h2 q h)))) hd64) fun h6 _ _ hdp => ?_
  refine .group (sig := [[T.i64]]) ?_ ?_
  · intro ⟨j₁, ()⟩ ⟨j₂, ()⟩
    refine .cons (fun xs₁ xs₂ => ?_) .nil
    rcases xs₁ with ⟨fx₁, ⟨⟩⟩
    rcases xs₂ with ⟨fx₂, ⟨⟩⟩
    exact hk (fun _ h => List.mem_append_right _ (h6 _ (h5 _ (hG14 _ h))))
      (fun _ h => List.mem_append_right _ h) (.var List.mem_cons_self)
  · intro ⟨j₁, ()⟩ ⟨j₂, ()⟩
    exact emitMemFillLoop_wf retTys List.mem_cons_self
      (ArgRel.mono h6 hbv)
      (ArgRel.mono (fun q h => h6 q (h5 q (hG14 q h))) hf)
      (ArgRel.mono (fun q h => h6 q (h5 q (h4 q (h3 q h)))) hn64)
      hdp

theorem emitMemCopyLoop_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} (fwd : Bool)
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (retTys : List WValTy)
    {j₁ : L₁ [T.i64]} {j₂ : L₂ [T.i64]} (hj : ⟨[T.i64], j₁, j₂⟩ ∈ D)
    {f₁ n₁ dp₁ sp₁ : Arg V₁ T.i64} {f₂ n₂ dp₂ sp₂ : Arg V₂ T.i64}
    (hf : ArgRel G T.i64 f₁ f₂) (hn : ArgRel G T.i64 n₁ n₂)
    (hdp : ArgRel G T.i64 dp₁ dp₂) (hsp : ArgRel G T.i64 sp₁ sp₂) :
    Wf G D (emitMemCopyLoop fwd retTys j₁ f₁ n₁ dp₁ sp₁)
           (emitMemCopyLoop fwd retTys j₂ f₂ n₂ dp₂ sp₂) := by
  refine .group (sig := [[T.i64, T.i64, T.i64, T.i64]]) ?_ ?_
  · intro ⟨l₁, ()⟩ ⟨l₂, ()⟩
    refine .cons (fun lxs₁ lxs₂ => ?_) .nil
    rcases lxs₁ with ⟨lf₁, lr₁, ld₁, ls₁, ⟨⟩⟩
    rcases lxs₂ with ⟨lf₂, lr₂, ld₂, ls₂, ⟨⟩⟩
    let Gl := Tup.zip (as := [T.i64, T.i64, T.i64, T.i64])
      (lf₁, lr₁, ld₁, ls₁, ()) (lf₂, lr₂, ld₂, ls₂, ()) ++ G
    let Dl := Tup.zip (as := [[T.i64, T.i64, T.i64, T.i64]]) (l₁, ()) (l₂, ()) ++ D
    have hlD : ⟨[T.i64, T.i64, T.i64, T.i64], l₁, l₂⟩ ∈ Dl := List.mem_cons_self
    have hjDl : ⟨[T.i64], j₁, j₂⟩ ∈ Dl := List.mem_cons_of_mem _ hj
    have hlf : ArgRel Gl T.i64 (.var lf₁) (.var lf₂) := .var List.mem_cons_self
    have hlr : ArgRel Gl T.i64 (.var lr₁) (.var lr₂) :=
      .var (List.mem_cons_of_mem _ List.mem_cons_self)
    have hld : ArgRel Gl T.i64 (.var ld₁) (.var ld₂) :=
      .var (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    have hls : ArgRel Gl T.i64 (.var ls₁) (.var ls₂) :=
      .var (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)))
    refine wf_let2 (.cmp .eq T.i64) hlr (.imm _) fun h1 _ _ hid =>
      .jnz hid (.jump hjDl (.cons (ArgRel.mono h1 hlf) .nil))
        (wf_let2 (.cmp .eq T.i64) (ArgRel.mono h1 hlf) (.imm _) fun h2 _ _ hof =>
          .jnz hof (mkTrapExpr_wf retTys 2#32 (ArgRel.mono (fun q h => h2 q (h1 q h)) hlf))
            (wf_let2 (.sub T.i64) (ArgRel.mono (fun q h => h2 q (h1 q h)) hlf) (.imm _)
              fun h3 _ _ hfn =>
              wf_let2 (.sub T.i64)
                (ArgRel.mono (fun q h => h3 q (h2 q (h1 q h))) hlr) (.imm _) fun h4 _ _ hrn => ?_))
    have h14 : ∀ q ∈ Gl, q ∈ _ := fun q h => h4 q (h3 q (h2 q (h1 q h)))
    cases fwd
    · refine wf_let2 (.sub T.i64) (ArgRel.mono h14 hld) (.imm _) fun h5 _ _ hdpP =>
        wf_let2 (.sub T.i64) (ArgRel.mono (fun q h => h5 q (h14 q h)) hls) (.imm _)
          fun h6 _ _ hspP =>
        wf_load T.i8 hspP fun h7 _ _ hb =>
        .store hb (ArgRel.mono (fun q h => h7 q (h6 q h)) hdpP)
          (.jump hlD (.cons (ArgRel.mono
            (fun q h => h7 q (h6 q (h5 q (h4 q h)))) hfn)
            (.cons (ArgRel.mono (fun q h => h7 q (h6 q (h5 q h))) hrn)
              (.cons (ArgRel.mono (fun q h => h7 q (h6 q h)) hdpP)
                (.cons (ArgRel.mono h7 hspP) .nil)))))
    · refine wf_load T.i8 (ArgRel.mono h14 hls) fun h5 _ _ hb =>
        .store hb (ArgRel.mono (fun q h => h5 q (h14 q h)) hld)
          (wf_let2 (.add T.i64) (ArgRel.mono (fun q h => h5 q (h14 q h)) hld) (.imm _)
            fun h6 _ _ hdpN =>
           wf_let2 (.add T.i64) (ArgRel.mono (fun q h => h6 q (h5 q (h14 q h))) hls) (.imm _)
            fun h7 _ _ hspN =>
            .jump hlD (.cons (ArgRel.mono
              (fun q h => h7 q (h6 q (h5 q (h4 q h)))) hfn)
              (.cons (ArgRel.mono (fun q h => h7 q (h6 q (h5 q h))) hrn)
                (.cons (ArgRel.mono h7 hdpN) (.cons hspN .nil)))))
  · intro ⟨l₁, ()⟩ ⟨l₂, ()⟩
    exact .jump List.mem_cons_self (.cons hf (.cons hn (.cons hdp (.cons hsp .nil))))

theorem emitMemCopy_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (retTys : List WValTy)
    {vc₁ f₁ : Arg V₁ T.i64} {vc₂ f₂ : Arg V₂ T.i64}
    (hvc : ArgRel G T.i64 vc₁ vc₂) (hf : ArgRel G T.i64 f₁ f₂)
    {d₁ s₁ n₁ : Arg V₁ T.i32} {d₂ s₂ n₂ : Arg V₂ T.i32}
    (hd : ArgRel G T.i32 d₁ d₂) (hs : ArgRel G T.i32 s₁ s₂) (hn : ArgRel G T.i32 n₁ n₂)
    {k₁ : Arg V₁ T.i64 → Expr V₁ L₁ (wasmRetSig retTys)}
    {k₂ : Arg V₂ T.i64 → Expr V₂ L₂ (wasmRetSig retTys)}
    (hk : ∀ {G' D'}, (∀ p ∈ G, p ∈ G') → (∀ p ∈ D, p ∈ D') →
      ∀ {f₁' f₂'}, ArgRel G' T.i64 f₁' f₂' → Wf G' D' (k₁ f₁') (k₂ f₂')) :
    Wf G D (emitMemCopy retTys vc₁ f₁ d₁ s₁ n₁ k₁)
           (emitMemCopy retTys vc₂ f₂ d₂ s₂ n₂ k₂) := by
  refine emitLoadVmCtx_wf hvc fun hvm mb₁ mb₂ ml₁ ml₂ hmb hml => ?_
  refine wf_let1 (.zext 32 64) (ArgRel.mono hvm hd) fun h1 _ _ hd64 =>
    wf_let1 (.zext 32 64) (ArgRel.mono (fun q h => h1 q (hvm q h)) hs) fun h2 _ _ hs64 =>
    wf_let1 (.zext 32 64) (ArgRel.mono (fun q h => h2 q (h1 q (hvm q h))) hn) fun h3 _ _ hn64 =>
    wf_let2 (.add T.i64) (ArgRel.mono (fun q h => h3 q (h2 q h)) hd64) hn64 fun h4 _ _ hde =>
    wf_let2 (.add T.i64) (ArgRel.mono (fun q h => h4 q (h3 q h)) hs64)
      (ArgRel.mono h4 hn64) fun h5 _ _ hse => ?_
  have h15 : ∀ q ∈ _, q ∈ _ := fun q h => h5 q (h4 q (h3 q (h2 q (h1 q h))))
  refine wf_let2 (.cmp .ule T.i64) (ArgRel.mono h5 hde) (ArgRel.mono h15 hml)
    fun h6 _ _ hod =>
    wf_let2 (.cmp .ule T.i64) (ArgRel.mono h6 hse) (ArgRel.mono (fun q h => h6 q (h15 q h)) hml)
      fun h7 _ _ hos =>
    wf_let2 (.and .bool) (ArgRel.mono h7 hod) hos fun h8 _ _ hib => ?_
  have hvm8 : ∀ q ∈ G, q ∈ _ :=
    fun q h => h8 q (h7 q (h6 q (h15 q (hvm q h))))
  refine .jnz hib ?_ (mkTrapExpr_wf retTys 1#32 (ArgRel.mono hvm8 hf))
  refine .group (sig := [[T.i64]]) ?_ ?_
  · intro ⟨j₁, ()⟩ ⟨j₂, ()⟩
    refine .cons (fun xs₁ xs₂ => ?_) .nil
    rcases xs₁ with ⟨fx₁, ⟨⟩⟩
    rcases xs₂ with ⟨fx₂, ⟨⟩⟩
    exact hk (fun _ h => List.mem_append_right _ (hvm8 _ h))
      (fun _ h => List.mem_append_right _ h) (.var List.mem_cons_self)
  · intro ⟨j₁, ()⟩ ⟨j₂, ()⟩
    have hjD : ⟨[T.i64], j₁, j₂⟩ ∈
        Tup.zip (as := [[T.i64]]) (j₁, ()) (j₂, ()) ++ D := List.mem_cons_self
    have hd8 : ArgRel _ T.i64 _ _ :=
      ArgRel.mono (fun q h => h8 q (h7 q (h6 q (h5 q (h4 q (h3 q (h2 q h))))))) hd64
    have hs8 : ArgRel _ T.i64 _ _ :=
      ArgRel.mono (fun q h => h8 q (h7 q (h6 q (h5 q (h4 q (h3 q h)))))) hs64
    have hn8 : ArgRel _ T.i64 _ _ :=
      ArgRel.mono (fun q h => h8 q (h7 q (h6 q (h5 q (h4 q h))))) hn64
    have hde8 : ArgRel _ T.i64 _ _ :=
      ArgRel.mono (fun q h => h8 q (h7 q (h6 q (h5 q h)))) hde
    have hse8 : ArgRel _ T.i64 _ _ :=
      ArgRel.mono (fun q h => h8 q (h7 q (h6 q h))) hse
    have hmb8 : ArgRel _ T.i64 _ _ :=
      ArgRel.mono (fun q h => h8 q (h7 q (h6 q (h15 q h)))) hmb
    refine wf_let2 (.cmp .ule T.i64) hd8 hs8 fun h9 _ _ hif =>
      .jnz hif
        (wf_let2 (.add T.i64) (ArgRel.mono h9 hmb8) (ArgRel.mono h9 hd8) fun h10 _ _ hdf =>
         wf_let2 (.add T.i64) (ArgRel.mono (fun q h => h10 q (h9 q h)) hmb8)
           (ArgRel.mono (fun q h => h10 q (h9 q h)) hs8) fun h11 _ _ hsf =>
           emitMemCopyLoop_wf true retTys hjD
             (ArgRel.mono (fun q h => h11 q (h10 q (h9 q (hvm8 q h)))) hf)
             (ArgRel.mono (fun q h => h11 q (h10 q (h9 q h))) hn8)
             (ArgRel.mono h11 hdf) hsf)
        (wf_let2 (.add T.i64) (ArgRel.mono h9 hmb8) (ArgRel.mono h9 hde8) fun h10 _ _ hdb =>
         wf_let2 (.add T.i64) (ArgRel.mono (fun q h => h10 q (h9 q h)) hmb8)
           (ArgRel.mono (fun q h => h10 q (h9 q h)) hse8) fun h11 _ _ hsb =>
           emitMemCopyLoop_wf false retTys hjD
             (ArgRel.mono (fun q h => h11 q (h10 q (h9 q (hvm8 q h)))) hf)
             (ArgRel.mono (fun q h => h11 q (h10 q (h9 q h))) hn8)
             (ArgRel.mono h11 hdb) hsb)

end WfHelpers

/-! ## Target-Independent `supportsSource` Preservation -/

section SupportsSourceHelpers

theorem supportsTy_le64 {lt : LegalTarget} (hv : lt.valid = true)
    {n : Nat} (hn : n ≤ 64) : lt.supportsTy (.bits n) = true := by
  have h64 : 64 ∈ lt.bitWidths := by
    simp only [LegalTarget.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact hv.1.1.2
  simp only [LegalTarget.supportsTy, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq]
  exact ⟨⟨64, h64, hn⟩, hn⟩

theorem WValTy.toTy_supportsTy {lt : LegalTarget} (hv : lt.valid = true) (w : WValTy) :
    lt.supportsTy w.toTy = true := by
  cases w <;> exact supportsTy_le64 hv (by omega)

theorem list_map_toTy_supportsTy {lt : LegalTarget} (hv : lt.valid = true) :
    ∀ ts : List WValTy, (ts.map WValTy.toTy).all lt.supportsTy = true
  | [] => rfl
  | t :: ts => by
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true]
    exact ⟨t.toTy_supportsTy hv, list_map_toTy_supportsTy hv ts⟩

theorem wasmRetSig_supportsTy {lt : LegalTarget} (hv : lt.valid = true) (rs : List WValTy) :
    (wasmRetSig rs).all lt.supportsTy = true := by
  simp only [wasmRetSig, List.all_cons, Bool.and_eq_true]
  exact ⟨supportsTy_le64 hv (by omega), supportsTy_le64 hv (by omega),
    list_map_toTy_supportsTy hv rs⟩

theorem wasmAbiParams_supportsTy {lt : LegalTarget} (hv : lt.valid = true) (ft : WFuncTy) :
    (wasmAbiParams ft).all lt.supportsTy = true := by
  simp only [wasmAbiParams, List.cons_append, List.nil_append, List.all_cons, Bool.and_eq_true]
  exact ⟨supportsTy_le64 hv (by omega), supportsTy_le64 hv (by omega),
    list_map_toTy_supportsTy hv ft.params⟩

theorem labelSig_supportsTy {lt : LegalTarget} (hv : lt.valid = true)
    (locTys argTys : List WValTy) :
    (labelSig locTys argTys).all lt.supportsTy = true := by
  simp only [labelSig, List.all_cons, List.all_append, Bool.and_eq_true]
  exact ⟨supportsTy_le64 hv (by omega),
    list_map_toTy_supportsTy hv locTys, list_map_toTy_supportsTy hv argTys⟩

theorem labelSig_supportsTy_pair {lt : LegalTarget} (hv : lt.valid = true)
    (locTys argTys : List WValTy) :
    lt.supportsTy T.i64 = true ∧
      (locTys.map WValTy.toTy ++ argTys.map WValTy.toTy).all lt.supportsTy = true := by
  have h := labelSig_supportsTy hv locTys argTys
  simp only [labelSig, List.all_cons, Bool.and_eq_true] at h
  exact h

theorem tflat_let1_ss (lt : LegalTarget) {rs : List Ty} {a u : Ty} (code : OpCode [a] [u])
    (x : Arg K a) {k : Tup K [u] → Expr K KL rs} {nv nl : Nat}
    (hop : lt.supportsOpCode code = true)
    (hk : (toTFlat (k (Tup.levels [u] nv)) (nv + 1) nl).supportsSource lt = true) :
    (toTFlat (.let_ (.mk code (x, ())) k) nv nl).supportsSource lt = true := by
  simp only [toTFlat, TFlat.supportsSource, Bool.and_eq_true, List.length_cons, List.length_nil,
    Nat.zero_add] at *
  exact ⟨hop, hk⟩

theorem tflat_let2_ss (lt : LegalTarget) {rs : List Ty} {a b u : Ty} (code : OpCode [a, b] [u])
    (x : Arg K a) (y : Arg K b) {k : Tup K [u] → Expr K KL rs} {nv nl : Nat}
    (hop : lt.supportsOpCode code = true)
    (hk : (toTFlat (k (Tup.levels [u] nv)) (nv + 1) nl).supportsSource lt = true) :
    (toTFlat (.let_ (.mk code (x, y, ())) k) nv nl).supportsSource lt = true := by
  simp only [toTFlat, TFlat.supportsSource, Bool.and_eq_true, List.length_cons, List.length_nil,
    Nat.zero_add] at *
  exact ⟨hop, hk⟩

theorem tflat_let3_ss (lt : LegalTarget) {rs : List Ty} {a b c u : Ty}
    (code : OpCode [a, b, c] [u])
    (x : Arg K a) (y : Arg K b) (z : Arg K c) {k : Tup K [u] → Expr K KL rs} {nv nl : Nat}
    (hop : lt.supportsOpCode code = true)
    (hk : (toTFlat (k (Tup.levels [u] nv)) (nv + 1) nl).supportsSource lt = true) :
    (toTFlat (.let_ (.mk code (x, y, z, ())) k) nv nl).supportsSource lt = true := by
  simp only [toTFlat, TFlat.supportsSource, Bool.and_eq_true, List.length_cons, List.length_nil,
    Nat.zero_add] at *
  exact ⟨hop, hk⟩

theorem tflat_load_ss (lt : LegalTarget) {rs : List Ty} (t : Ty) (a : Arg K T.i64)
    {k : K t → Expr K KL rs} {nv nl : Nat}
    (ht : lt.supportsTy t = true) (hb : t.bytes ≤ 2 ^ 64)
    (hk : (toTFlat (k nv) (nv + 1) nl).supportsSource lt = true) :
    (toTFlat (.load t a k) nv nl).supportsSource lt = true := by
  simp only [toTFlat, TFlat.supportsSource, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨ht, hb⟩, hk⟩

theorem tflat_store_ss (lt : LegalTarget) {rs : List Ty} {t : Ty} (v : Arg K t) (a : Arg K T.i64)
    {k : Expr K KL rs} {nv nl : Nat}
    (ht : lt.supportsTy t = true) (hb : t.bytes ≤ 2 ^ 64)
    (hk : (toTFlat k nv nl).supportsSource lt = true) :
    (toTFlat (.store (t := t) v a k) nv nl).supportsSource lt = true := by
  simp only [toTFlat, TFlat.supportsSource, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨ht, hb⟩, hk⟩

theorem tflat_jnz_ss (lt : LegalTarget) {rs : List Ty} (c : Arg K .bool)
    {t e : Expr K KL rs} {nv nl : Nat}
    (ht : (toTFlat t nv nl).supportsSource lt = true)
    (he : (toTFlat e nv nl).supportsSource lt = true) :
    (toTFlat (.jnz c t e) nv nl).supportsSource lt = true := by
  simp only [toTFlat, TFlat.supportsSource, Bool.and_eq_true]
  exact ⟨ht, he⟩

theorem tflat_jump_ss (lt : LegalTarget) {rs ts : List Ty} (j : KL ts) (args : Tup (Arg K) ts)
    {nv nl : Nat} (hts : ts.all lt.supportsTy = true) :
    (toTFlat (rs := rs) (.jump j args) nv nl).supportsSource lt = true := by
  simpa [toTFlat, TFlat.supportsSource] using hts

theorem tflat_group1_ss (lt : LegalTarget) {rs : List Ty} (ts : List Ty)
    (bodies : Tup KL [ts] → Blocks K KL rs [ts]) (k : Tup KL [ts] → Expr K KL rs)
    {nv nl : Nat} (hts : ts.all lt.supportsTy = true)
    (hb : (match bodies (nl, ()) with
      | .cons b .nil =>
        (toTFlat (b (Tup.levels ts nv)) (nv + ts.length) (nl + 1)).supportsSource lt) = true)
    (hk : (toTFlat (k (nl, ())) nv (nl + 1)).supportsSource lt = true) :
    (toTFlat (.group (sig := [ts]) bodies k) nv nl).supportsSource lt = true := by
  cases hEq : bodies (nl, ()) with
  | cons b bs =>
    cases bs
    simp only [toTFlat, hEq, toTBlocks, TFlat.supportsSource, TBlocks.supportsSource,
      List.length_cons, List.length_nil, Nat.zero_add, Bool.and_eq_true, Tup.levels]
    refine ⟨⟨by simpa [List.all_cons, List.all_nil] using hts, ⟨hts, ?_⟩, trivial⟩, hk⟩
    simpa [hEq] using hb

theorem mkTrapExpr_ss {lt : LegalTarget} (hv : lt.valid = true) (retTys : List WValTy)
    (code : BitVec 32) (f : Arg K T.i64) (nv nl : Nat) :
    (toTFlat (mkTrapExpr (L := KL) retTys code f) nv nl).supportsSource lt = true := by
  simpa [mkTrapExpr, toTFlat, TFlat.supportsSource] using wasmRetSig_supportsTy hv retTys

theorem mkStatusTrapExpr_ss {lt : LegalTarget} (hv : lt.valid = true) (retTys : List WValTy)
    (st : Arg K T.i32) (f : Arg K T.i64) (nv nl : Nat) :
    (toTFlat (mkStatusTrapExpr (L := KL) retTys st f) nv nl).supportsSource lt = true := by
  simpa [mkStatusTrapExpr, toTFlat, TFlat.supportsSource] using wasmRetSig_supportsTy hv retTys

theorem tflat_ret_ss (lt : LegalTarget) {rs : List Ty} (args : Tup (Arg K) rs)
    {nv nl : Nat} (hrs : rs.all lt.supportsTy = true) :
    (toTFlat (.ret args) nv nl).supportsSource lt = true := by
  simpa [toTFlat, TFlat.supportsSource] using hrs

theorem tflat_call_ss (lt : LegalTarget) {rs as bs : List Ty} (f : Sym)
    (args : Tup (Arg K) as) {k : Tup K bs → Expr K KL rs} {nv nl : Nat}
    (has : as.all lt.supportsTy = true) (hbs : bs.all lt.supportsTy = true)
    (hk : (toTFlat (k (Tup.levels bs nv)) (nv + bs.length) nl).supportsSource lt = true) :
    (toTFlat (.call f args k) nv nl).supportsSource lt = true := by
  simp only [toTFlat, TFlat.supportsSource, Bool.and_eq_true]
  exact ⟨⟨has, hbs⟩, hk⟩

theorem supportsTy_bool {lt : LegalTarget} : lt.supportsTy .bool = true := by
  simp [LegalTarget.supportsTy]

macro "tflat_op_ss" hv:ident : tactic =>
  `(tactic| (
    simp only [LegalTarget.supportsOpCode, Bool.and_eq_true]
    repeat' constructor
    all_goals (try assumption)
    all_goals (try exact supportsTy_le64 $hv (by omega))
    all_goals (try exact supportsTy_bool)
    all_goals (try decide)))

macro "tflat_step_ss" hv:ident : tactic =>
  `(tactic| first
    | assumption
    | (apply_assumption; done)
    | exact mkTrapExpr_ss $hv _ _ _ _ _
    | exact mkStatusTrapExpr_ss $hv _ _ _ _ _
    | refine tflat_let1_ss _ _ _ (by tflat_op_ss $hv) ?_
    | refine tflat_let2_ss _ _ _ _ (by tflat_op_ss $hv) ?_
    | refine tflat_let3_ss _ _ _ _ _ (by tflat_op_ss $hv) ?_
    | refine tflat_load_ss _ _ _ (supportsTy_le64 $hv (by omega)) (by decide) ?_
    | refine tflat_store_ss _ _ _ (supportsTy_le64 $hv (by omega)) (by decide) ?_
    | refine tflat_jnz_ss _ _ ?_ ?_
    | refine tflat_call_ss _ _ _ (wasmAbiParams_supportsTy $hv _) (wasmRetSig_supportsTy $hv _) ?_
    | exact tflat_ret_ss _ _ (wasmRetSig_supportsTy $hv _)
    | exact tflat_jump_ss _ _ _ (labelSig_supportsTy $hv _ _)
    | exact labelSig_supportsTy_pair $hv _ _)

macro "tflat_builder_ss!" hv:ident : tactic =>
  `(tactic| repeat tflat_step_ss $hv)

theorem emitLoadVmCtx_ss {lt : LegalTarget} (hv : lt.valid = true) {rs : List Ty}
    (vmCtx : Arg K T.i64) (k : Arg K T.i64 → Arg K T.i64 → Expr K KL rs)
    (hk : ∀ mb ml nv' nl', (toTFlat (k mb ml) nv' nl').supportsSource lt = true) :
    ∀ nv nl, (toTFlat (emitLoadVmCtx vmCtx k) nv nl).supportsSource lt = true := by
  intro nv nl
  have h64 : lt.supportsTy (.bits 64) = true := supportsTy_le64 hv (by omega)
  refine tflat_load_ss lt T.i64 vmCtx h64 (by decide) ?_
  refine tflat_let2_ss lt (.add T.i64) vmCtx (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_load_ss lt T.i64 _ h64 (by decide) ?_
  apply hk

theorem emitMemBounds_ss {lt : LegalTarget} (hv : lt.valid = true) (retTys : List WValTy)
    (vmCtx f : Arg K T.i64) (idx : Arg K T.i32) (arg : WMemArg) (bytes : Nat)
    (k : Arg K T.i64 → Expr K KL (wasmRetSig retTys))
    (hk : ∀ p nv' nl', (toTFlat (k p) nv' nl').supportsSource lt = true) :
    ∀ nv nl,
      (toTFlat (emitMemBounds retTys vmCtx f idx arg bytes k) nv nl).supportsSource lt = true := by
  intro nv nl
  have h32 : lt.supportsTy (.bits 32) = true := supportsTy_le64 hv (by omega)
  have h64 : lt.supportsTy (.bits 64) = true := supportsTy_le64 hv (by omega)
  refine emitLoadVmCtx_ss hv vmCtx _ (fun mb ml nv' nl' => ?_) nv nl
  refine tflat_let1_ss lt (.zext 32 64) idx (by simp [LegalTarget.supportsOpCode, h32, h64]) ?_
  refine tflat_let2_ss lt (.add T.i64) _ (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_let2_ss lt (.add T.i64) _ (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_let2_ss lt (.cmp .ule T.i64) _ ml (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_jnz_ss lt _ ?_ (mkTrapExpr_ss hv retTys 1#32 f _ _)
  refine tflat_let2_ss lt (.add T.i64) mb _ (by simp [LegalTarget.supportsOpCode, h64]) ?_
  apply hk

theorem emitMemSize_ss {lt : LegalTarget} (hv : lt.valid = true) {rs : List Ty}
    (vmCtx : Arg K T.i64) (k : Arg K T.i32 → Expr K KL rs)
    (hk : ∀ p nv' nl', (toTFlat (k p) nv' nl').supportsSource lt = true) :
    ∀ nv nl, (toTFlat (emitMemSize vmCtx k) nv nl).supportsSource lt = true := by
  intro nv nl
  have h32 : lt.supportsTy (.bits 32) = true := supportsTy_le64 hv (by omega)
  have h64 : lt.supportsTy (.bits 64) = true := supportsTy_le64 hv (by omega)
  refine tflat_let2_ss lt (.add T.i64) vmCtx (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_load_ss lt T.i64 _ h64 (by decide) ?_
  refine tflat_let2_ss lt (.lshr T.i64) _ (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_let1_ss lt (.trunc 64 32) _ (by simp [LegalTarget.supportsOpCode, h64, h32]) ?_
  apply hk

theorem emitMemZeroPage_ss {lt : LegalTarget} (hv : lt.valid = true) {rs : List Ty}
    (pagePtr : Arg K T.i64) (kDone : Expr K KL rs)
    (hk : ∀ nv' nl', (toTFlat kDone nv' nl').supportsSource lt = true) :
    ∀ nv nl, (toTFlat (emitMemZeroPage pagePtr kDone) nv nl).supportsSource lt = true := by
  intro nv nl
  have h64 : lt.supportsTy (.bits 64) = true := supportsTy_le64 hv (by omega)
  have hts0 : ([] : List Ty).all lt.supportsTy = true := rfl
  have hts2 : ([T.i64, T.i64] : List Ty).all lt.supportsTy = true := by simp [h64]
  refine tflat_group1_ss lt [] _ _ hts0 (hk _ _) ?_
  refine tflat_group1_ss lt [T.i64, T.i64] _ _ hts2 ?_ (tflat_jump_ss lt _ _ hts2)
  refine tflat_let2_ss lt (.cmp .eq T.i64) _ (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_jnz_ss lt _ (tflat_jump_ss lt _ _ hts0) ?_
  refine tflat_store_ss lt (.imm _) _ h64 (by decide) ?_
  refine tflat_let2_ss lt (.sub T.i64) _ (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_let2_ss lt (.add T.i64) _ (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
  exact tflat_jump_ss lt _ _ hts2

theorem emitMemGrowLoop_ss {lt : LegalTarget} (hv : lt.valid = true) (retTys : List WValTy)
    (jDone : KL [T.i64, T.i32]) (pLen newLen : Arg K T.i64) (oldPages32 : Arg K T.i32)
    (fuel delta64 startPtr : Arg K T.i64) :
    ∀ nv nl, (toTFlat (emitMemGrowLoop retTys jDone pLen newLen oldPages32
      fuel delta64 startPtr) nv nl).supportsSource lt = true := by
  intro nv nl
  have h32 : lt.supportsTy (.bits 32) = true := supportsTy_le64 hv (by omega)
  have h64 : lt.supportsTy (.bits 64) = true := supportsTy_le64 hv (by omega)
  have hts2 : ([T.i64, T.i32] : List Ty).all lt.supportsTy = true := by simp [h64, h32]
  have hts3 : ([T.i64, T.i64, T.i64] : List Ty).all lt.supportsTy = true := by simp [h64]
  refine tflat_group1_ss lt [T.i64, T.i64, T.i64] _ _ hts3 ?_ (tflat_jump_ss lt _ _ hts3)
  refine tflat_let2_ss lt (.cmp .eq T.i64) _ (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_jnz_ss lt _ (tflat_store_ss lt newLen pLen h64 (by decide)
    (tflat_jump_ss lt jDone _ hts2)) ?_
  refine tflat_let2_ss lt (.cmp .eq T.i64) _ (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_jnz_ss lt _ (mkTrapExpr_ss hv retTys 2#32 _ _ _) ?_
  refine tflat_let2_ss lt (.sub T.i64) _ (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine emitMemZeroPage_ss hv _ _ (fun _ _ => ?_) _ _
  refine tflat_let2_ss lt (.sub T.i64) _ (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_let2_ss lt (.add T.i64) _ (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
  exact tflat_jump_ss lt _ _ hts3

theorem emitMemGrow_ss {lt : LegalTarget} (hv : lt.valid = true) (retTys : List WValTy)
    (memMaxBytes : BitVec 64) (vmCtx f : Arg K T.i64) (delta32 : Arg K T.i32)
    (k : Arg K T.i64 → Arg K T.i32 → Expr K KL (wasmRetSig retTys))
    (hk : ∀ f' r nv' nl', (toTFlat (k f' r) nv' nl').supportsSource lt = true) :
    ∀ nv nl,
      (toTFlat (emitMemGrow retTys memMaxBytes vmCtx f delta32 k) nv nl).supportsSource lt =
        true := by
  intro nv nl
  have h32 : lt.supportsTy (.bits 32) = true := supportsTy_le64 hv (by omega)
  have h64 : lt.supportsTy (.bits 64) = true := supportsTy_le64 hv (by omega)
  have hts2 : ([T.i64, T.i32] : List Ty).all lt.supportsTy = true := by simp [h64, h32]
  refine tflat_group1_ss lt [T.i64, T.i32] _ _ hts2 (hk _ _ _ _) ?_
  refine tflat_load_ss lt T.i64 vmCtx h64 (by decide) ?_
  refine tflat_let2_ss lt (.add T.i64) vmCtx (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_load_ss lt T.i64 _ h64 (by decide) ?_
  refine tflat_let2_ss lt (.add T.i64) vmCtx (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_load_ss lt T.i64 _ h64 (by decide) ?_
  refine tflat_let2_ss lt (.lshr T.i64) _ (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_let1_ss lt (.trunc 64 32) _ (by simp [LegalTarget.supportsOpCode, h64, h32]) ?_
  refine tflat_let2_ss lt (.cmp .eq T.i32) delta32 (.imm _)
    (by simp [LegalTarget.supportsOpCode, h32]) ?_
  refine tflat_jnz_ss lt _ (tflat_jump_ss lt _ _ hts2) ?_
  refine tflat_let1_ss lt (.zext 32 64) delta32 (by simp [LegalTarget.supportsOpCode, h32, h64]) ?_
  refine tflat_let2_ss lt (.shl T.i64) _ (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_let2_ss lt (.add T.i64) _ _ (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_let2_ss lt (.cmp .ule T.i64) _ _ (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_let2_ss lt (.cmp .ule T.i64) _ _ (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_let2_ss lt (.cmp .ule T.i64) _ (.imm _)
    (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_let2_ss lt (.and .bool) _ _
    (by simp [LegalTarget.supportsOpCode, LegalTarget.supportsTy]) ?_
  refine tflat_let2_ss lt (.and .bool) _ _
    (by simp [LegalTarget.supportsOpCode, LegalTarget.supportsTy]) ?_
  refine tflat_jnz_ss lt _ ?_ (tflat_jump_ss lt _ _ hts2)
  refine tflat_let2_ss lt (.add T.i64) _ _ (by simp [LegalTarget.supportsOpCode, h64]) ?_
  exact emitMemGrowLoop_ss hv retTys _ _ _ _ f _ _ _ _

theorem emitMemFillLoop_ss {lt : LegalTarget} (hv : lt.valid = true) (retTys : List WValTy)
    (jAfter : KL [T.i64]) (byteVal : Arg K T.i8) (f n64 dstPtr0 : Arg K T.i64) :
    ∀ nv nl,
      (toTFlat (emitMemFillLoop retTys jAfter byteVal f n64 dstPtr0) nv nl).supportsSource lt =
        true := by
  intro nv nl
  have h8 : lt.supportsTy (.bits 8) = true := supportsTy_le64 hv (by omega)
  have h64 : lt.supportsTy (.bits 64) = true := supportsTy_le64 hv (by omega)
  have hts1 : ([T.i64] : List Ty).all lt.supportsTy = true := by simp [h64]
  have hts3 : ([T.i64, T.i64, T.i64] : List Ty).all lt.supportsTy = true := by simp [h64]
  refine tflat_group1_ss lt [T.i64, T.i64, T.i64] _ _ hts3 ?_ (tflat_jump_ss lt _ _ hts3)
  refine tflat_let2_ss lt (.cmp .eq T.i64) _ (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_jnz_ss lt _ (tflat_jump_ss lt jAfter _ hts1) ?_
  refine tflat_let2_ss lt (.cmp .eq T.i64) _ (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_jnz_ss lt _ (mkTrapExpr_ss hv retTys 2#32 _ _ _) ?_
  refine tflat_let2_ss lt (.sub T.i64) _ (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_store_ss lt byteVal _ h8 (by decide) ?_
  refine tflat_let2_ss lt (.sub T.i64) _ (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_let2_ss lt (.add T.i64) _ (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
  exact tflat_jump_ss lt _ _ hts3

theorem emitMemFill_ss {lt : LegalTarget} (hv : lt.valid = true) (retTys : List WValTy)
    (vmCtx f : Arg K T.i64) (dst32 val32 n32 : Arg K T.i32)
    (k : Arg K T.i64 → Expr K KL (wasmRetSig retTys))
    (hk : ∀ f' nv' nl', (toTFlat (k f') nv' nl').supportsSource lt = true) :
    ∀ nv nl,
      (toTFlat (emitMemFill retTys vmCtx f dst32 val32 n32 k) nv nl).supportsSource lt = true := by
  intro nv nl
  have h8 : lt.supportsTy (.bits 8) = true := supportsTy_le64 hv (by omega)
  have h32 : lt.supportsTy (.bits 32) = true := supportsTy_le64 hv (by omega)
  have h64 : lt.supportsTy (.bits 64) = true := supportsTy_le64 hv (by omega)
  have hts1 : ([T.i64] : List Ty).all lt.supportsTy = true := by simp [h64]
  refine emitLoadVmCtx_ss hv vmCtx _ (fun mb ml nv' nl' => ?_) nv nl
  refine tflat_let1_ss lt (.zext 32 64) dst32 (by simp [LegalTarget.supportsOpCode, h32, h64]) ?_
  refine tflat_let1_ss lt (.zext 32 64) n32 (by simp [LegalTarget.supportsOpCode, h32, h64]) ?_
  refine tflat_let2_ss lt (.add T.i64) _ _ (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_let2_ss lt (.cmp .ule T.i64) _ ml (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_jnz_ss lt _ ?_ (mkTrapExpr_ss hv retTys 1#32 f _ _)
  refine tflat_let1_ss lt (.trunc 32 8) val32 (by simp [LegalTarget.supportsOpCode, h32, h8]) ?_
  refine tflat_let2_ss lt (.add T.i64) mb _ (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_group1_ss lt [T.i64] _ _ hts1 (hk _ _ _) ?_
  exact emitMemFillLoop_ss hv retTys _ _ f _ _ _ _

theorem emitMemCopyLoop_ss {lt : LegalTarget} (hv : lt.valid = true) (fwd : Bool)
    (retTys : List WValTy) (jAfter : KL [T.i64]) (f n64 dp0 sp0 : Arg K T.i64) :
    ∀ nv nl,
      (toTFlat (emitMemCopyLoop fwd retTys jAfter f n64 dp0 sp0) nv nl).supportsSource lt =
        true := by
  intro nv nl
  have h8 : lt.supportsTy (.bits 8) = true := supportsTy_le64 hv (by omega)
  have h64 : lt.supportsTy (.bits 64) = true := supportsTy_le64 hv (by omega)
  have hts1 : ([T.i64] : List Ty).all lt.supportsTy = true := by simp [h64]
  have hts4 : ([T.i64, T.i64, T.i64, T.i64] : List Ty).all lt.supportsTy = true := by simp [h64]
  refine tflat_group1_ss lt [T.i64, T.i64, T.i64, T.i64] _ _ hts4 ?_ (tflat_jump_ss lt _ _ hts4)
  refine tflat_let2_ss lt (.cmp .eq T.i64) _ (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_jnz_ss lt _ (tflat_jump_ss lt jAfter _ hts1) ?_
  refine tflat_let2_ss lt (.cmp .eq T.i64) _ (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_jnz_ss lt _ (mkTrapExpr_ss hv retTys 2#32 _ _ _) ?_
  refine tflat_let2_ss lt (.sub T.i64) _ (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_let2_ss lt (.sub T.i64) _ (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
  cases fwd
  · refine tflat_let2_ss lt (.sub T.i64) _ (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
    refine tflat_let2_ss lt (.sub T.i64) _ (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
    refine tflat_load_ss lt T.i8 _ h8 (by decide) ?_
    refine tflat_store_ss lt _ _ h8 (by decide) ?_
    exact tflat_jump_ss lt _ _ hts4
  · refine tflat_load_ss lt T.i8 _ h8 (by decide) ?_
    refine tflat_store_ss lt _ _ h8 (by decide) ?_
    refine tflat_let2_ss lt (.add T.i64) _ (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
    refine tflat_let2_ss lt (.add T.i64) _ (.imm _) (by simp [LegalTarget.supportsOpCode, h64]) ?_
    exact tflat_jump_ss lt _ _ hts4

theorem emitMemCopy_ss {lt : LegalTarget} (hv : lt.valid = true) (retTys : List WValTy)
    (vmCtx f : Arg K T.i64) (dst32 src32 n32 : Arg K T.i32)
    (k : Arg K T.i64 → Expr K KL (wasmRetSig retTys))
    (hk : ∀ f' nv' nl', (toTFlat (k f') nv' nl').supportsSource lt = true) :
    ∀ nv nl,
      (toTFlat (emitMemCopy retTys vmCtx f dst32 src32 n32 k) nv nl).supportsSource lt = true := by
  intro nv nl
  have h32 : lt.supportsTy (.bits 32) = true := supportsTy_le64 hv (by omega)
  have h64 : lt.supportsTy (.bits 64) = true := supportsTy_le64 hv (by omega)
  have hts1 : ([T.i64] : List Ty).all lt.supportsTy = true := by simp [h64]
  refine emitLoadVmCtx_ss hv vmCtx _ (fun mb ml nv' nl' => ?_) nv nl
  refine tflat_let1_ss lt (.zext 32 64) dst32 (by simp [LegalTarget.supportsOpCode, h32, h64]) ?_
  refine tflat_let1_ss lt (.zext 32 64) src32 (by simp [LegalTarget.supportsOpCode, h32, h64]) ?_
  refine tflat_let1_ss lt (.zext 32 64) n32 (by simp [LegalTarget.supportsOpCode, h32, h64]) ?_
  refine tflat_let2_ss lt (.add T.i64) _ _ (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_let2_ss lt (.add T.i64) _ _ (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_let2_ss lt (.cmp .ule T.i64) _ ml (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_let2_ss lt (.cmp .ule T.i64) _ ml (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_let2_ss lt (.and .bool) _ _
    (by simp [LegalTarget.supportsOpCode, LegalTarget.supportsTy]) ?_
  refine tflat_jnz_ss lt _ ?_ (mkTrapExpr_ss hv retTys 1#32 f _ _)
  refine tflat_group1_ss lt [T.i64] _ _ hts1 (hk _ _ _) ?_
  refine tflat_let2_ss lt (.cmp .ule T.i64) _ _ (by simp [LegalTarget.supportsOpCode, h64]) ?_
  refine tflat_jnz_ss lt _
    (tflat_let2_ss lt (.add T.i64) mb _ (by simp [LegalTarget.supportsOpCode, h64])
      (tflat_let2_ss lt (.add T.i64) mb _ (by simp [LegalTarget.supportsOpCode, h64])
        (emitMemCopyLoop_ss hv true retTys _ f _ _ _ _ _)))
    (tflat_let2_ss lt (.add T.i64) mb _ (by simp [LegalTarget.supportsOpCode, h64])
      (tflat_let2_ss lt (.add T.i64) mb _ (by simp [LegalTarget.supportsOpCode, h64])
        (emitMemCopyLoop_ss hv false retTys _ f _ _ _ _ _)))

end SupportsSourceHelpers

end LeanQbe.T.Wasm
