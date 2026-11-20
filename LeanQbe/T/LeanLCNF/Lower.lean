module

public import LeanQbe.T.LeanLCNF.Basic
public import LeanQbe.T.Frontend.C0
public import LeanQbe.T.Module

/-!
# Impure `LCNF` → `LeanQbe.T`: builder combinators and inline primitives

Code is generated as named SSA (`Frontend.C0.LExpr`, fresh ids from a state monad) and then
scope-checked into de Bruijn `TFlat` by `lExprToTFlat` (`Lower1.lean`), so every lowered function
reifies to a `Func.Wf` PHOAS `Fn` (`TFlatFn.toFn_wf`).

Runtime conventions (shared with `test/lcnf/lcnf_rt.c`):
* Every function takes `rt : i64` first. At most `regArgs = 5` further parameters travel in
  registers; parameters `5..` are spilled by the caller to `rt->extra_args[i - 5]` (offset
  `8 * (i - 5)`) and reloaded by the callee prologue.
* Object header (`lean.h`): `m_rc : i32 @0`, `m_cs_sz : u16 @4`, `m_other : u8 @6` (number of object
  fields), `m_tag : u8 @7`; fields at `8 + 8 * i`; closures: `fun_id @8`, `arity : u16 @16`,
  `num_fixed : u16 @18`, captured objects at `24 + 8 * i`. Tagged scalars are `2 * n + 1`.
* Hot operations are inline `T`: tagged-scalar `ctor`, `box`/`unbox`, `oproj`/`uproj`/`sproj`,
  `oset`/`uset`/`sset`/`setTag`, `isShared` (`m_rc != 1`), `inc`/`dec` with a scalar fast path
  and an inline `m_rc` update (the cold runtime is called only when `m_rc` drops `1 → 0`),
  `UIntN`/`USize` arithmetic, and tagged-fixnum `Nat` fast paths (runtime called only on
  non-scalar/overflow).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T
open LeanQbe.T.Frontend.C0 (LExpr LVar LArg LOp)

/-! ## Runtime layout constants -/

/-- Parameters (after `rt`) passed in registers. -/
def regArgs : Nat := 5
/-- Offset of `rt->extra_args[0]`. -/
def rtExtraOff : Nat := 0
/-- Number of `extra_args` slots. -/
def rtExtraSlots : Nat := 32
/-- Offset of `rt->globals[0]` (once-cells of closed constants). -/
def rtGlobalsOff : Nat := 256
/-- Number of global once-cells. -/
def rtGlobalSlots : Nat := 256
/-- Closure object tag (`LeanClosure`). -/
def closureTag : Nat := 245

/-- Runtime calls (`(name, params, results)`), all `i64`, implemented by `lcnf_rt.c`. -/
def rtCalls : List (Sym × List Ty × List Ty) :=
  [ ("lcnf_alloc", [i64, i64], [i64])
  , ("lcnf_dec_ref_cold", [i64, i64], [])
  , ("lcnf_free_obj", [i64, i64], [])
  , ("lcnf_mark_persistent", [i64, i64], [])
  , ("lcnf_nat_slow", [i64, i64, i64, i64], [i64])
  , ("lcnf_clo_under", [i64, i64, i64], [i64]) ]

/-- Exit (never-returning) runtime symbols. -/
def rtExitSyms : List Sym := ["lcnf_panic"]

/-- `lcnf_nat_slow` operation codes. -/
def natOpCode : String → Nat
  | "add" => 1 | "sub" => 2 | "mul" => 3 | "div" => 4 | "mod" => 5
  | "decEq" => 6 | "decLt" => 7 | "decLe" => 8 | "shiftRight" => 9
  | "land" => 10 | "lor" => 11 | "xor" => 12 | "ofNat" => 13 | "toNat" => 14
  | _ => 0

/-- Panic codes passed to `lcnf_panic`. -/
def panicUnreachable : Nat := 1
/-- Panic code: closure dispatch found no matching `fun_id`. -/
def panicBadClosure : Nat := 2

/-! ## Builder monad -/

/-- Fresh-id generator over `Except String`. -/
abbrev LM := StateT Nat (Except String)

/-- A fresh SSA / label id. -/
def fresh : LM Nat := modifyGet fun n => (n, n + 1)

/-- Fail with a message. -/
def lfail {α : Type} (msg : String) : LM α := throw msg

/-- A fresh typed binder. -/
def freshVar (t : Ty) : LM LVar := do pure { id := ← fresh, name := "", ty := t }

/-- The operand naming a binder. -/
def vArg (v : LVar) : LArg := .var v.id v.ty

/-- Typed immediate of width `w`. -/
def imm (w : Nat) (n : Nat) : LArg := .imm (.bits w) (BitVec.ofNat w n)

/-- 64-bit immediate. -/
def imm64 (n : Nat) : LArg := imm 64 n

/-- Emit a single-result operation and continue with its result. -/
def op1 (t : Ty) {sig : List Ty} (code : OpCode sig [t]) (args : List LArg)
    (k : LArg → LM LExpr) : LM LExpr := do
  let v ← freshVar t
  let body ← k (vArg v)
  pure (.let_ { rs := [t], sig, code, args } [v] body)

/-- Emit a two-result operation. -/
def op2 (t u : Ty) {sig : List Ty} (code : OpCode sig [t, u]) (args : List LArg)
    (k : LArg → LArg → LM LExpr) : LM LExpr := do
  let v ← freshVar t
  let w ← freshVar u
  let body ← k (vArg v) (vArg w)
  pure (.let_ { rs := [t, u], sig, code, args } [v, w] body)

/-- 64-bit binary helpers. -/
def add64 (a b : LArg) (k : LArg → LM LExpr) : LM LExpr := op1 i64 (.add i64) [a, b] k
def sub64 (a b : LArg) (k : LArg → LM LExpr) : LM LExpr := op1 i64 (.sub i64) [a, b] k
def and64 (a b : LArg) (k : LArg → LM LExpr) : LM LExpr := op1 i64 (.and i64) [a, b] k
def or64 (a b : LArg) (k : LArg → LM LExpr) : LM LExpr := op1 i64 (.or i64) [a, b] k
def shl64 (a b : LArg) (k : LArg → LM LExpr) : LM LExpr := op1 i64 (.shl i64) [a, b] k
def lshr64 (a b : LArg) (k : LArg → LM LExpr) : LM LExpr := op1 i64 (.lshr i64) [a, b] k

/-- Integer comparison at type `t`. -/
def cmpOp (o : CmpOp) (w : Nat) (a b : LArg) (k : LArg → LM LExpr) : LM LExpr :=
  op1 .bool (.cmp o (.bits w)) [a, b] k

/-- Address `x + off`. -/
def addrOf (x : LArg) (off : Nat) (k : LArg → LM LExpr) : LM LExpr :=
  if off == 0 then k x else add64 x (imm64 off) k

/-- `load t [x + off]`. -/
def loadAt (t : Ty) (x : LArg) (off : Nat) (k : LArg → LM LExpr) : LM LExpr :=
  addrOf x off fun a => do
    let v ← freshVar t
    pure (.load t a v (← k (vArg v)))

/-- `store t v [x + off]`. -/
def storeAt (t : Ty) (v x : LArg) (off : Nat) (k : LM LExpr) : LM LExpr :=
  addrOf x off fun a => do pure (.store t v a (← k))

/-- Call with results. -/
def callN (f : Sym) (as bs : List Ty) (args : List LArg) (k : List LArg → LM LExpr) :
    LM LExpr := do
  let vs ← bs.mapM freshVar
  let body ← k (vs.map vArg)
  pure (.call f as bs args vs body)

/-- Call with one result. -/
def call1 (f : Sym) (as : List Ty) (b : Ty) (args : List LArg) (k : LArg → LM LExpr) :
    LM LExpr :=
  callN f as [b] args fun
    | [r] => k r
    | _ => lfail "call1: arity"

/-- Call with no result. -/
def call0 (f : Sym) (as : List Ty) (args : List LArg) (k : LM LExpr) : LM LExpr :=
  callN f as [] args fun _ => k

/-- A one-block join point: `rest` is the block (receiving its parameters), `pre` the code that
jumps to it (receiving the jump builder). -/
def withJoin (ts : List Ty) (rest : List LArg → LM LExpr)
    (pre : (List LArg → LExpr) → LM LExpr) : LM LExpr := do
  let lbl ← fresh
  let ps ← ts.mapM freshVar
  let blk ← rest (ps.map vArg)
  let body ← pre fun args => .jump lbl ts args
  pure (.group [(lbl, ps, blk)] body)

/-- A one-result join point. -/
def withJoin1 (t : Ty) (rest : LArg → LM LExpr) (pre : (LArg → LExpr) → LM LExpr) :
    LM LExpr :=
  withJoin [t] (fun | [r] => rest r | _ => lfail "withJoin1") fun j => pre fun r => j [r]

/-- `(x & 1) != 0`: is `x` a tagged scalar? -/
def isScalarObj (x : LArg) (k : LArg → LM LExpr) : LM LExpr :=
  and64 x (imm64 1) fun b => cmpOp .ne 64 b (imm64 0) k

/-- Width conversion between bit-vector types. -/
def convW (m n : Nat) (x : LArg) (k : LArg → LM LExpr) : LM LExpr :=
  if m == n then k x
  else if m < n then op1 (.bits n) (.zext m n) [x] k
  else op1 (.bits n) (.trunc m n) [x] k

/-- Materialize a boolean as `uint8`. -/
def boolToU8 (b : LArg) (k : LArg → LM LExpr) : LM LExpr := op1 i8 (.ofBool 8) [b] k

/-! ## Reference counting -/

/-- Inline `m_rc += n` for a definite pointer, skipping persistent (`m_rc ≤ 0`) objects. -/
def incRef (x : LArg) (n : Nat) (k : LM LExpr) : LM LExpr :=
  loadAt i32 x 0 fun rc =>
  cmpOp .sgt 32 rc (imm 32 0) fun pos =>
  op1 i32 (.ofBool 32) [pos] fun b =>
  (if n == 1 then fun k' => k' b else op1 i32 (.mul i32) [b, imm 32 n]) fun d =>
  op1 i32 (.add i32) [rc, d] fun rc' =>
  storeAt i32 rc' x 0 k

/-- Inline `dec` of a definite pointer: `m_rc == 1` → cold `lcnf_dec_ref_cold`, else
`m_rc -= (m_rc > 1)`; continues by jumping with `j`. -/
def decRefJ (rt x : LArg) (j : LExpr) : LM LExpr :=
  loadAt i32 x 0 fun rc =>
  cmpOp .eq 32 rc (imm 32 1) fun is1 => do
    let cold ← call0 "lcnf_dec_ref_cold" [i64, i64] [rt, x] (pure j)
    let hot ← cmpOp .sgt 32 rc (imm 32 1) fun gt =>
      op1 i32 (.ofBool 32) [gt] fun b =>
      op1 i32 (.sub i32) [rc, b] fun rc' =>
      storeAt i32 rc' x 0 (pure j)
    pure (.jnz is1 cold hot)

/-- Does a value of type `t` need RC operations? -/
def LcTy.needsRc : LcTy → Bool
  | .object | .tobject => true
  | _ => false

/-- `inc x n` (scalar test only when `check` and `x` may be a scalar). -/
def emitInc (x : LArg) (ty : LcTy) (n : Nat) (check : Bool) (k : LM LExpr) : LM LExpr :=
  if !ty.needsRc || n == 0 then k
  else if !check || ty == .object then incRef x n k
  else withJoin [] (fun _ => k) fun j => do
    let e ← incRef x n (pure (j []))
    isScalarObj x fun s => pure (.jnz s (j []) e)

/-- `dec x` (once). -/
def emitDec1 (rt x : LArg) (ty : LcTy) (check : Bool) (k : LM LExpr) : LM LExpr :=
  if !ty.needsRc then k
  else withJoin [] (fun _ => k) fun j => do
    let e ← decRefJ rt x (j [])
    if !check || ty == .object then pure e
    else isScalarObj x fun s => pure (.jnz s (j []) e)

/-- `dec x n`. -/
def emitDec (rt x : LArg) (ty : LcTy) (n : Nat) (check : Bool) (k : LM LExpr) : LM LExpr :=
  match n with
  | 0 => k
  | n + 1 => emitDec1 rt x ty check (emitDec rt x ty n check k)

/-! ## Allocation -/

/-- Allocate `sz` bytes and write the 64-bit header `hdr`. -/
def allocObj (rt : LArg) (sz hdr : Nat) (k : LArg → LM LExpr) : LM LExpr :=
  call1 "lcnf_alloc" [i64, i64] i64 [rt, imm64 sz] fun p =>
  storeAt i64 (imm64 hdr) p 0 (k p)

/-- Byte size of a constructor object (rounded up to 8). -/
def LcCtor.byteSize (c : LcCtor) : Nat := (8 + 8 * c.size + 8 * c.usize + c.ssize + 7) / 8 * 8

/-- Header word of a freshly allocated constructor (`m_rc = 1`). -/
def LcCtor.header (c : LcCtor) : Nat :=
  1 + c.byteSize * 2 ^ 32 + c.size * 2 ^ 48 + c.cidx * 2 ^ 56

/-- Store object fields `vs` at `8 * (base + i) + off` of `p`. -/
def storeFields (p : LArg) (off : Nat) : List LArg → LM LExpr → LM LExpr
  | [], k => k
  | v :: vs, k => storeAt i64 v p off (storeFields p (off + 8) vs k)

/-- Allocate a boxed `UInt64`/`USize` (`lean_box_uint64`: tag 0, 8 scalar bytes). -/
def boxU64 (rt x : LArg) (k : LArg → LM LExpr) : LM LExpr :=
  allocObj rt 16 (1 + 16 * 2 ^ 32) fun p => storeAt i64 x p 8 (k p)

/-! ## Inline `Nat` (tagged fixnum) and `UIntN` primitives -/

/-- Run `fast` when both tagged-`Nat` operands are scalars, else (or when `fast` reports
overflow by calling its `slow` argument) call `lcnf_nat_slow(rt, op, a, b)`. -/
def natBin (rt : LArg) (op : String) (resW : Nat) (a b : LArg)
    (fast : (slow : LM LExpr) → (LArg → LExpr) → LM LExpr)
    (k : LArg → LM LExpr) : LM LExpr :=
  withJoin1 (.bits resW) k fun j => do
    let slow : LM LExpr :=
      call1 "lcnf_nat_slow" [i64, i64, i64, i64] i64 [rt, imm64 (natOpCode op), a, b] fun r =>
        convW 64 resW r fun r' => pure (j r')
    let fastE ← fast slow j
    let slowE ← slow
    and64 a b fun ab => isScalarObj ab fun both => pure (.jnz both fastE slowE)

/-- Box an unboxed `i64` (`< 2^63`) as a tagged scalar. -/
def boxSmall (x : LArg) (k : LArg → LM LExpr) : LM LExpr :=
  shl64 x (imm64 1) fun s => or64 s (imm64 1) k

/-- Inline `Nat.*` externs. -/
def natPrim (rt : LArg) (op : String) (as : List LArg) (k : LArg → LM LExpr) : LM LExpr := do
  match op, as with
  | "add", [a, b] => natBin rt op 64 a b (fun slow j =>
      sub64 a (imm64 1) fun s => add64 s b fun r =>
      cmpOp .ult 64 r b fun ovf => do pure (.jnz ovf (← slow) (j r))) k
  | "sub", [a, b] => natBin rt op 64 a b (fun _ j =>
      cmpOp .ult 64 a b fun lt => do
        let e ← sub64 a b fun d => add64 d (imm64 1) fun r => pure (j r)
        pure (.jnz lt (j (imm64 1)) e)) k
  | "mul", [a, b] => natBin rt op 64 a b (fun slow j =>
      lshr64 a (imm64 1) fun x => lshr64 b (imm64 1) fun y =>
      op2 i64 i64 (.umulw 64) [x, y] fun lo hi =>
      lshr64 lo (imm64 63) fun top => or64 hi top fun bad =>
      cmpOp .ne 64 bad (imm64 0) fun ovf => do
        let e ← boxSmall lo fun r => pure (j r)
        pure (.jnz ovf (← slow) e)) k
  | "div", [a, b] => natBin rt op 64 a b (fun _ j =>
      lshr64 b (imm64 1) fun y => cmpOp .eq 64 y (imm64 0) fun z => do
        let e ← lshr64 a (imm64 1) fun x => op1 i64 (.udiv 64) [x, y] fun q =>
          boxSmall q fun r => pure (j r)
        pure (.jnz z (j (imm64 1)) e)) k
  | "mod", [a, b] => natBin rt op 64 a b (fun _ j =>
      lshr64 b (imm64 1) fun y => cmpOp .eq 64 y (imm64 0) fun z => do
        let e ← lshr64 a (imm64 1) fun x => op1 i64 (.urem 64) [x, y] fun q =>
          boxSmall q fun r => pure (j r)
        pure (.jnz z (j a) e)) k
  | "decEq", [a, b] | "beq", [a, b] => natBin rt "decEq" 8 a b (fun _ j =>
      cmpOp .eq 64 a b fun c => boolToU8 c fun r => pure (j r)) k
  | "decLt", [a, b] | "blt", [a, b] => natBin rt "decLt" 8 a b (fun _ j =>
      cmpOp .ult 64 a b fun c => boolToU8 c fun r => pure (j r)) k
  | "decLe", [a, b] | "ble", [a, b] => natBin rt "decLe" 8 a b (fun _ j =>
      cmpOp .ule 64 a b fun c => boolToU8 c fun r => pure (j r)) k
  | "shiftRight", [a, b] => natBin rt op 64 a b (fun _ j =>
      lshr64 b (imm64 1) fun y => cmpOp .ult 64 y (imm64 63) fun ok => do
        let e ← add64 y (imm64 1) fun y1 => lshr64 a y1 fun x =>
          boxSmall x fun r => pure (j r)
        pure (.jnz ok e (j (imm64 1)))) k
  | "land", [a, b] => natBin rt op 64 a b (fun _ j => and64 a b fun r => pure (j r)) k
  | "lor", [a, b] => natBin rt op 64 a b (fun _ j => or64 a b fun r => pure (j r)) k
  | "xor", [a, b] => natBin rt op 64 a b (fun _ j =>
      op1 i64 (.xor i64) [a, b] fun x => or64 x (imm64 1) fun r => pure (j r)) k
  | _, _ => lfail s!"LeanLCNF: unsupported Nat primitive Nat.{op}/{as.length}"

/-- Width of a `UIntN`/`USize` type name. -/
def uintWidth? : String → Option Nat
  | "UInt8" => some 8 | "UInt16" => some 16 | "UInt32" => some 32
  | "UInt64" => some 64 | "USize" => some 64
  | _ => none

/-- Inline `UIntN.*` / `USize.*` externs at width `w`. -/
def uintPrim (rt : LArg) (w : Nat) (op : String) (as : List LArg) (k : LArg → LM LExpr) :
    LM LExpr := do
  let t : Ty := .bits w
  let bin (code : OpCode [t, t] [t]) (a b : LArg) := op1 t code [a, b] k
  let cmpU (o : CmpOp) (a b : LArg) := cmpOp o w a b fun c => boolToU8 c k
  match op, as with
  | "add", [a, b] => bin (.add t) a b
  | "sub", [a, b] => bin (.sub t) a b
  | "mul", [a, b] => bin (.mul t) a b
  | "land", [a, b] => bin (.and t) a b
  | "lor", [a, b] => bin (.or t) a b
  | "xor", [a, b] => bin (.xor t) a b
  | "shiftLeft", [a, b] => op1 t (.and t) [b, imm w (w - 1)] fun s => bin (.shl t) a s
  | "shiftRight", [a, b] => op1 t (.and t) [b, imm w (w - 1)] fun s => bin (.lshr t) a s
  | "complement", [a] => op1 t (.not t) [a] k
  | "neg", [a] => op1 t (.neg t) [a] k
  | "div", [a, b] => withJoin1 t k fun j => do
      let e ← op1 t (.udiv w) [a, b] fun q => pure (j q)
      cmpOp .eq w b (imm w 0) fun z => pure (.jnz z (j (imm w 0)) e)
  | "mod", [a, b] => withJoin1 t k fun j => do
      let e ← op1 t (.urem w) [a, b] fun q => pure (j q)
      cmpOp .eq w b (imm w 0) fun z => pure (.jnz z (j a) e)
  | "decEq", [a, b] | "beq", [a, b] => cmpU .eq a b
  | "decLt", [a, b] | "blt", [a, b] => cmpU .ult a b
  | "decLe", [a, b] | "ble", [a, b] => cmpU .ule a b
  | "ofNat", [a] | "ofNatLT", [a] | "ofNatTruncate", [a] =>
    withJoin1 t k fun j => do
      let slow ← call1 "lcnf_nat_slow" [i64, i64, i64, i64] i64
        [rt, imm64 (natOpCode "ofNat"), a, imm64 w] fun r => convW 64 w r fun r' => pure (j r')
      let fast ← lshr64 a (imm64 1) fun x => convW 64 w x fun r => pure (j r)
      isScalarObj a fun s => pure (.jnz s fast slow)
  | "toNat", [a] =>
    convW w 64 a fun x =>
    if w < 64 then boxSmall x k
    else withJoin1 i64 k fun j => do
      let slow ← call1 "lcnf_nat_slow" [i64, i64, i64, i64] i64
        [rt, imm64 (natOpCode "toNat"), x, imm64 0] fun r => pure (j r)
      let fast ← boxSmall x fun r => pure (j r)
      lshr64 x (imm64 63) fun top => cmpOp .eq 64 top (imm64 0) fun ok =>
        pure (.jnz ok fast slow)
  | "toUInt8", [a] => convW w 8 a k
  | "toUInt16", [a] => convW w 16 a k
  | "toUInt32", [a] => convW w 32 a k
  | "toUInt64", [a] | "toUSize", [a] => convW w 64 a k
  | _, _ => lfail s!"LeanLCNF: unsupported UInt{w} primitive {op}/{as.length}"

/-- Inline an imported extern by its Lean name, or fail. -/
def externPrim (rt : LArg) (name : String) (as : List LArg) (k : LArg → LM LExpr) :
    LM LExpr :=
  match name.splitOn "." with
  | ["Nat", op] => natPrim rt op as k
  | [ty, op] =>
    match uintWidth? ty with
    | some w => uintPrim rt w op as k
    | none => lfail s!"LeanLCNF: unsupported imported callee '{name}'"
  | _ => lfail s!"LeanLCNF: unsupported imported callee '{name}'"

end LeanQbe.T.LeanLCNF
