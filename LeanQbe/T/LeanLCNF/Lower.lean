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
* `Int`: tagged small ints `2 * v + 1` (`-2^62 ≤ v < 2^62`) with inline `ofNat`/`natAbs`/`add`/
  `sub`/comparison fast paths; sign-magnitude bignums (the `Nat` limb layout + a sign byte) in
  `lcnf_int_op`.
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
def rtGlobalSlots : Nat := 4096
/-- Closure object tag (`LeanClosure`). -/
def closureTag : Nat := 245

/-- Runtime calls (`(name, params, results)`), all `i64`, implemented by `lcnf_rt.c`. -/
def rtCalls : List (Sym × List Ty × List Ty) :=
  [ ("lcnf_alloc", [i64, i64], [i64])
  , ("lcnf_dec_ref_cold", [i64, i64], [])
  , ("lcnf_free_obj", [i64, i64], [])
  , ("lcnf_mark_persistent", [i64, i64], [])
  , ("lcnf_nat_slow", [i64, i64, i64, i64], [i64])
  , ("lcnf_clo_under", [i64, i64, i64], [i64])
  , ("lcnf_str_alloc", [i64, i64, i64], [i64])
  , ("lcnf_nat_alloc", [i64, i64], [i64])
  , ("lcnf_nat_to_str", [i64, i64], [i64])
  , ("lcnf_char_op", [i64, i64, i64], [i64])
  , ("lcnf_oob", [i64, i64], [i64])
  , ("lcnf_array_mk_empty", [i64, i64], [i64])
  , ("lcnf_array_mk", [i64, i64], [i64])
  , ("lcnf_array_to_list", [i64, i64], [i64])
  , ("lcnf_array_push", [i64, i64, i64], [i64])
  , ("lcnf_array_replicate", [i64, i64, i64], [i64])
  , ("lcnf_array_get", [i64, i64, i64, i64, i64], [i64])
  , ("lcnf_array_set", [i64, i64, i64, i64, i64], [i64])
  , ("lcnf_array_pop", [i64, i64], [i64])
  , ("lcnf_array_swap", [i64, i64, i64, i64, i64], [i64])
  , ("lcnf_string_push", [i64, i64, i64], [i64])
  , ("lcnf_string_append", [i64, i64, i64], [i64])
  , ("lcnf_string_to_list", [i64, i64], [i64])
  , ("lcnf_string_mk", [i64, i64], [i64])
  , ("lcnf_string_cmp_op", [i64, i64, i64, i64], [i64])
  , ("lcnf_string_pos_op", [i64, i64, i64, i64, i64], [i64])
  , ("lcnf_ba_empty", [i64], [i64])
  , ("lcnf_ba_mk_empty", [i64, i64], [i64])
  , ("lcnf_ba_mk", [i64, i64], [i64])
  , ("lcnf_ba_data", [i64, i64], [i64])
  , ("lcnf_ba_push", [i64, i64, i64], [i64])
  , ("lcnf_ba_get", [i64, i64, i64, i64], [i64])
  , ("lcnf_ba_set", [i64, i64, i64, i64, i64], [i64])
  , ("lcnf_ba_cmp_op", [i64, i64, i64, i64], [i64])
  , ("lcnf_float_bin", [i64, i64, i64, i64], [i64])
  , ("lcnf_float_un", [i64, i64, i64], [i64])
  , ("lcnf_float_of_sci", [i64, i64, i64, i64], [i64])
  , ("lcnf_int_op", [i64, i64, i64, i64], [i64]) ]

/-- Exit (never-returning) runtime symbols. -/
def rtExitSyms : List Sym := ["lcnf_panic"]

/-- `lcnf_nat_slow` operation codes. -/
def natOpCode : String → Nat
  | "add" => 1 | "sub" => 2 | "mul" => 3 | "div" => 4 | "mod" => 5
  | "decEq" => 6 | "decLt" => 7 | "decLe" => 8 | "shiftRight" => 9
  | "land" => 10 | "lor" => 11 | "xor" => 12 | "ofNat" => 13 | "toNat" => 14
  | "shiftLeft" => 15 | "pow" => 16 | "pred" => 17 | "gcd" => 18 | "log2" => 19
  | _ => 0

/-- `lcnf_int_op` operation codes (`ofInt64` is `Int64.toInt`, `divExact` is `tdiv`). -/
def intOpCode : String → Nat
  | "ofNat" => 1 | "negSucc" => 2 | "neg" => 3 | "add" => 4 | "sub" => 5 | "mul" => 6
  | "ediv" => 7 | "emod" => 8 | "natAbs" => 9 | "decEq" => 10 | "decLt" => 11 | "decLe" => 12
  | "ofInt64" => 13 | "tdiv" => 14 | "divExact" => 14 | "tmod" => 15 | "decNonneg" => 16
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

/-- Bit width of an `LArg` (`64` for non-bits). -/
def argBitsWidth : LArg → Nat
  | .var _ (.bits w) | .imm (.bits w) _ => w
  | _ => 64

/-- Call a C runtime function `(rt, i64...) -> i64` and convert the result to `resW` bits. -/
def rtCall1 (rt : LArg) (fn : Sym) (args : List LArg) (resW : Nat)
    (k : LArg → LM LExpr) : LM LExpr :=
  let rec go : List LArg → List LArg → LM LExpr
    | [], acc =>
      let ts := List.replicate (acc.length + 1) i64
      call1 fn ts i64 (rt :: acc) fun r => convW 64 resW r k
    | a :: rest, acc => convW (argBitsWidth a) 64 a fun a64 => go rest (acc ++ [a64])
  go args []

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

/-- `inc x n` (scalar test only when `check` and `x` may be a scalar). The scalar test is emitted
*before* the join is opened, so that it dominates the continuation `k` and `Gvn` reuses it for
the later `inc`/`dec`/`cases` of the same `x`. -/
def emitInc (x : LArg) (ty : LcTy) (n : Nat) (check : Bool) (k : LM LExpr) : LM LExpr :=
  if !ty.needsRc || n == 0 then k
  else if !check || ty == .object then incRef x n k
  else isScalarObj x fun s => withJoin [] (fun _ => k) fun j => do
    let e ← incRef x n (pure (j []))
    pure (.jnz s (j []) e)

/-- `dec x` (once). As in `emitInc`, the scalar test is emitted before the join is opened. -/
def emitDec1 (rt x : LArg) (ty : LcTy) (check : Bool) (k : LM LExpr) : LM LExpr :=
  if !ty.needsRc then k
  else if !check || ty == .object then withJoin [] (fun _ => k) fun j => decRefJ rt x (j [])
  else isScalarObj x fun s => withJoin [] (fun _ => k) fun j => do
    let e ← decRefJ rt x (j [])
    pure (.jnz s (j []) e)

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

/-- Allocate a boxed `UInt64`/`USize`/`Float` (tag 0, 8 scalar bytes). -/
def boxU64 (rt x : LArg) (k : LArg → LM LExpr) : LM LExpr :=
  allocObj rt 16 (1 + 16 * 2 ^ 32) fun p => storeAt i64 x p 8 (k p)

/-! ## Inline `Nat` (tagged fixnum) and `UIntN` primitives -/

/-- Run `fast` when both tagged operands are scalars, else (or when `fast` reports overflow by
calling its `slow` argument) call the runtime `fn(rt, code, a, b)`. The scalar test is emitted
before the join is opened (see `emitInc`). -/
def tagBin (rt : LArg) (fn : Sym) (code resW : Nat) (a b : LArg)
    (fast : (slow : LM LExpr) → (LArg → LExpr) → LM LExpr)
    (k : LArg → LM LExpr) : LM LExpr :=
  and64 a b fun ab => isScalarObj ab fun both =>
  withJoin1 (.bits resW) k fun j => do
    let slow : LM LExpr :=
      call1 fn [i64, i64, i64, i64] i64 [rt, imm64 code, a, b] fun r =>
        convW 64 resW r fun r' => pure (j r')
    let fastE ← fast slow j
    let slowE ← slow
    pure (.jnz both fastE slowE)

/-- `tagBin` for tagged-`Nat` operands (`lcnf_nat_slow(rt, op, a, b)` on the slow path). -/
def natBin (rt : LArg) (op : String) (resW : Nat) (a b : LArg)
    (fast : (slow : LM LExpr) → (LArg → LExpr) → LM LExpr)
    (k : LArg → LM LExpr) : LM LExpr :=
  tagBin rt "lcnf_nat_slow" (natOpCode op) resW a b fast k

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
  | "shiftLeft", [a, b] => natBin rt op 64 a b (fun slow j =>
      lshr64 b (imm64 1) fun y => cmpOp .ult 64 y (imm64 63) fun ok => do
        let sh ← lshr64 a (imm64 1) fun x => shl64 x y fun z =>
          lshr64 z y fun x' => cmpOp .eq 64 x' x fun ok1 =>
          lshr64 z (imm64 63) fun top => cmpOp .eq 64 top (imm64 0) fun ok2 => do
            let boxed ← boxSmall z fun r => pure (j r)
            pure (.jnz ok1 (.jnz ok2 boxed (← slow)) (← slow))
        pure (.jnz ok sh (← slow))) k
  | "pred", [a] =>
    isScalarObj a fun s => withJoin1 i64 k fun j => do
      let slow ← rtCall1 rt "lcnf_nat_slow" [imm64 (natOpCode "pred"), a, imm64 1] 64
        fun r => pure (j r)
      let fast ← cmpOp .eq 64 a (imm64 1) fun z => do
        let sub ← sub64 a (imm64 2) fun r => pure (j r)
        pure (.jnz z (j (imm64 1)) sub)
      pure (.jnz s fast slow)
  | "pow", [a, b] | "gcd", [a, b] =>
    rtCall1 rt "lcnf_nat_slow" [imm64 (natOpCode op), a, b] 64 k
  | "log2", [a] => rtCall1 rt "lcnf_nat_slow" [imm64 (natOpCode "log2"), a, imm64 1] 64 k
  | "reprFast", [a] => rtCall1 rt "lcnf_nat_to_str" [a] 64 k
  | _, _ => lfail s!"LeanLCNF: unsupported Nat primitive Nat.{op}/{as.length}"

/-- Width of a `UIntN`/`USize` type name. -/
def uintWidth? : String → Option Nat
  | "UInt8" => some 8 | "UInt16" => some 16 | "UInt32" => some 32
  | "UInt64" => some 64 | "USize" => some 64
  | _ => none

/-- `UIntN.ofNat` (borrowed tagged `Nat` → `bits w`, wrapping). -/
def uintOfNat (rt : LArg) (w : Nat) (a : LArg) (k : LArg → LM LExpr) : LM LExpr :=
  let t : Ty := .bits w
  isScalarObj a fun s => withJoin1 t k fun j => do
    let slow ← call1 "lcnf_nat_slow" [i64, i64, i64, i64] i64
      [rt, imm64 (natOpCode "ofNat"), a, imm64 w] fun r => convW 64 w r fun r' => pure (j r')
    let fast ← lshr64 a (imm64 1) fun x => convW 64 w x fun r => pure (j r)
    pure (.jnz s fast slow)

/-- `UIntN.toNat` (`bits w` → fresh tagged `Nat`). -/
def uintToNat (rt : LArg) (w : Nat) (a : LArg) (k : LArg → LM LExpr) : LM LExpr :=
  convW w 64 a fun x =>
  if w < 64 then boxSmall x k
  else withJoin1 i64 k fun j => do
    let slow ← call1 "lcnf_nat_slow" [i64, i64, i64, i64] i64
      [rt, imm64 (natOpCode "toNat"), x, imm64 0] fun r => pure (j r)
    let fast ← boxSmall x fun r => pure (j r)
    lshr64 x (imm64 63) fun top => cmpOp .eq 64 top (imm64 0) fun ok =>
      pure (.jnz ok fast slow)

/-- Inline `UIntN.*` / `USize.*` externs at width `w`. `BitVec w` is a `Nat` at runtime, so
`ofBitVec`/`toBitVec` are `ofNat`/`toNat`; `ofBitVec` consumes its argument
(`lean_uintN_of_nat_mk`). -/
def uintPrim (rt : LArg) (w : Nat) (op : String) (as : List LArg) (k : LArg → LM LExpr) :
    LM LExpr := do
  let t : Ty := .bits w
  let bin (code : OpCode [t, t] [t]) (a b : LArg) := op1 t code [a, b] k
  let cmpU (o : CmpOp) (a b : LArg) := cmpOp o w a b fun c => boolToU8 c k
  let divMod (code : OpCode [t, t] [t]) (a b zVal : LArg) := withJoin1 t k fun j => do
    let e ← op1 t code [a, b] fun q => pure (j q)
    cmpOp .eq w b (imm w 0) fun z => pure (.jnz z (j zVal) e)
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
  | "div", [a, b] => divMod (.udiv w) a b (imm w 0)
  | "mod", [a, b] => divMod (.urem w) a b a
  | "decEq", [a, b] | "beq", [a, b] => cmpU .eq a b
  | "decLt", [a, b] | "blt", [a, b] => cmpU .ult a b
  | "decLe", [a, b] | "ble", [a, b] => cmpU .ule a b
  | "ofNat", [a] | "ofNatLT", [a] | "ofNatLT", [a, _] => uintOfNat rt w a k
  | "ofBitVec", [a] => uintOfNat rt w a fun r => emitDec1 rt a .tobject true (k r)
  | "toNat", [a] | "toBitVec", [a] => uintToNat rt w a k
  | "repr", [a] => uintToNat rt w a fun n => rtCall1 rt "lcnf_nat_to_str" [n] 64 k
  | "toUInt8", [a] => convW w 8 a k
  | "toUInt16", [a] => convW w 16 a k
  | "toUInt32", [a] => convW w 32 a k
  | "toUInt64", [a] | "toUSize", [a] => convW w 64 a k
  | "toFloat", [a] => convW w 64 a fun x => rtCall1 rt "lcnf_float_un" [imm64 15, x] 64 k
  | _, _ => lfail s!"LeanLCNF: unsupported UInt{w} primitive {op}/{as.length}"

/-- Inline/runtime `Array.*` externs. -/
def arrayPrim (rt : LArg) (op : String) (as : List LArg) (k : LArg → LM LExpr) : LM LExpr :=
  let call (fn : Sym) (args : List LArg) := rtCall1 rt fn args 64 k
  let get (dv arr i : LArg) (m : Nat) := call "lcnf_array_get" [dv, arr, i, imm64 m]
  let set (arr i v : LArg) (m : Nat) := call "lcnf_array_set" [arr, i, v, imm64 m]
  match op, as with
  | "empty", [_] => call "lcnf_array_mk_empty" [imm64 1]
  | "mkEmpty", [_, cap] | "emptyWithCapacity", [_, cap] => call "lcnf_array_mk_empty" [cap]
  | "mk", [_, xs] => call "lcnf_array_mk" [xs]
  | "toList", [_, arr] => call "lcnf_array_to_list" [arr]
  | "push", [_, arr, v] => call "lcnf_array_push" [arr, v]
  | "replicate", [_, n, v] => call "lcnf_array_replicate" [n, v]
  | "size", [_, arr] => loadAt i64 arr 8 fun sz => boxSmall sz k
  | "usize", [_, arr] => loadAt i64 arr 8 k
  | "get!Internal", [_, dv, arr, i] => get dv arr i 0
  | "get!InternalBorrowed", [_, dv, arr, i] => get dv arr i 1
  | "getInternal", [_, arr, i, _] => get (imm64 1) arr i 0
  | "getInternalBorrowed", [_, arr, i, _] => get (imm64 1) arr i 1
  | "uget", [_, arr, i, _] => get (imm64 1) arr i 2
  | "ugetBorrowed", [_, arr, i, _] => get (imm64 1) arr i 3
  | "set!", [_, arr, i, v] | "set", [_, arr, i, v, _] => set arr i v 0
  | "uset", [_, arr, i, v, _] => set arr i v 1
  | "pop", [_, arr] => call "lcnf_array_pop" [arr]
  | "swap", [_, arr, i, j, _, _] => call "lcnf_array_swap" [arr, i, j, imm64 0]
  | "swapIfInBounds", [_, arr, i, j] => call "lcnf_array_swap" [arr, i, j, imm64 1]
  | "propagateMark", [_, _, _, ys] => k ys
  | _, _ => lfail s!"LeanLCNF: unsupported Array primitive Array.{op}/{as.length}"

/-- Inline/runtime `String.*` externs. -/
def stringPrim (rt : LArg) (parts : List String) (as : List LArg) (k : LArg → LM LExpr) :
    LM LExpr :=
  let call (fn : Sym) (args : List LArg) := rtCall1 rt fn args 64 k
  let cmp (c : Nat) (s1 s2 : LArg) := rtCall1 rt "lcnf_string_cmp_op" [imm64 c, s1, s2] 8 k
  let pos (c rw : Nat) (s a1 : LArg) (a2 := imm64 0) :=
    rtCall1 rt "lcnf_string_pos_op" [imm64 c, s, a1, a2] rw k
  let fail (_ : Unit) :=
    let p := String.intercalate "." parts
    lfail s!"LeanLCNF: unsupported String primitive String.{p}/{as.length}"
  match as with
  | [s] => match parts with
    | ["length"] | ["Internal", "length"] => loadAt i64 s 24 fun n => boxSmall n k
    | ["utf8ByteSize"] => loadAt i64 s 8 fun n => sub64 n (imm64 1) fun b => boxSmall b k
    | ["toListImpl"] | ["data"] => call "lcnf_string_to_list" [s]
    | ["ofList"] | ["mk"] => call "lcnf_string_mk" [s]
    | _ => fail ()
  | [s, i] => match parts with
    | ["push"] => call "lcnf_string_push" [s, i]
    | ["propagateMark"] => k i
    | ["append"] | ["Internal", "append"] => call "lcnf_string_append" [s, i]
    | ["decEq"] => cmp 0 s i
    | ["decidableLT"] => cmp 1 s i
    | ["compare"] => cmp 2 s i
    | ["Pos", "Raw", "get"] | ["Pos", "Raw", "get!"]
    | ["get"] | ["get!"] | ["Internal", "get"] => pos 0 32 s i
    | ["Pos", "Raw", "next"] | ["next"] | ["Internal", "next"] => pos 1 64 s i
    | ["Pos", "Raw", "atEnd"] | ["atEnd"] | ["Internal", "atEnd"] => pos 2 8 s i
    | ["Pos", "Raw", "isValid"] => pos 5 8 s i
    | _ => fail ()
  | [s, a1, a2] => match parts with
    | ["Pos", "Raw", "get'"] | ["get'"] | ["decodeChar"] => pos 0 32 s a1
    | ["Pos", "Raw", "next'"] | ["Pos", "next"] => pos 1 64 s a1
    | ["Pos", "Raw", "extract"] | ["extract"] | ["Internal", "extract"] => pos 3 64 s a1 a2
    | ["getUTF8Byte"] | ["getUtf8Byte"] | ["Internal", "getUTF8Byte"] => pos 4 8 s a1
    | _ => fail ()
  | _ => fail ()

/-- Inline/runtime `ByteArray.*` externs. -/
def byteArrayPrim (rt : LArg) (op : String) (as : List LArg) (k : LArg → LM LExpr) :
    LM LExpr :=
  match op, as with
  | "empty", [] => rtCall1 rt "lcnf_ba_empty" [] 64 k
  | "emptyWithCapacity", [cap] => rtCall1 rt "lcnf_ba_mk_empty" [cap] 64 k
  | "mk", [arr] => rtCall1 rt "lcnf_ba_mk" [arr] 64 k
  | "data", [ba] => rtCall1 rt "lcnf_ba_data" [ba] 64 k
  | "push", [ba, b] => rtCall1 rt "lcnf_ba_push" [ba, b] 64 k
  | "size", [ba] => loadAt i64 ba 8 fun sz => boxSmall sz k
  | "usize", [ba] => loadAt i64 ba 8 k
  | "get!", [ba, i] | "get", [ba, i, _] =>
    rtCall1 rt "lcnf_ba_get" [ba, i, imm64 0] 8 k
  | "uget", [ba, i, _] => rtCall1 rt "lcnf_ba_get" [ba, i, imm64 1] 8 k
  | "set!", [ba, i, b] | "set", [ba, i, b, _] =>
    rtCall1 rt "lcnf_ba_set" [ba, i, b, imm64 0] 64 k
  | "uset", [ba, i, b, _] => rtCall1 rt "lcnf_ba_set" [ba, i, b, imm64 1] 64 k
  | "beq", [a, b] | "decEq", [a, b] => rtCall1 rt "lcnf_ba_cmp_op" [imm64 0, a, b] 8 k
  | "decidableLT", [a, b] => rtCall1 rt "lcnf_ba_cmp_op" [imm64 1, a, b] 8 k
  | "compare", [a, b] => rtCall1 rt "lcnf_ba_cmp_op" [imm64 2, a, b] 8 k
  | "propagateMark", [_, b] => k b
  | _, _ => lfail s!"LeanLCNF: unsupported ByteArray primitive ByteArray.{op}/{as.length}"

/-- `Float.*` operation code and result bit width. -/
def floatBinCode : String → Option (Nat × Nat)
  | "add" => some (0, 64) | "sub" => some (1, 64) | "mul" => some (2, 64)
  | "div" => some (3, 64) | "beq" => some (4, 8) | "decLt" => some (5, 8)
  | "lt" => some (5, 8) | "decLe" => some (6, 8) | "le" => some (6, 8)
  | "pow" => some (7, 64) | "atan2" => some (8, 64)
  | "minimum" => some (9, 64) | "maximum" => some (10, 64)
  | _ => none

/-- `Float.*` unary operation code and result bit width. -/
def floatUnCode : String → Option (Nat × Nat)
  | "neg" => some (0, 64) | "abs" => some (1, 64) | "sqrt" => some (2, 64)
  | "sin" => some (3, 64) | "cos" => some (4, 64) | "tan" => some (5, 64)
  | "exp" => some (6, 64) | "log" => some (7, 64) | "floor" => some (8, 64)
  | "ceil" => some (9, 64) | "round" => some (10, 64) | "isNaN" => some (11, 8)
  | "isInf" => some (12, 8) | "isFinite" => some (13, 8) | "toUInt64" => some (14, 64)
  | "toUInt32" => some (16, 32) | "toUInt16" => some (17, 16)
  | "toUInt8" => some (18, 8) | "toInt64" => some (19, 64) | "toString" => some (20, 64)
  | _ => none

/-- Runtime `Float.*` externs (`Float` represented as `bits 64`). -/
def floatPrim (rt : LArg) (op : String) (as : List LArg) (k : LArg → LM LExpr) : LM LExpr :=
  match op, as with
  | "toBits", [a] | "ofBits", [a] | "toModel", [a] | "ofModel", [a] => k a
  | "ofScientific", [m, s, e] => rtCall1 rt "lcnf_float_of_sci" [m, s, e] 64 k
  | _, [a, b] =>
    match floatBinCode op with
    | some (c, rw) => rtCall1 rt "lcnf_float_bin" [imm64 c, a, b] rw k
    | none => lfail s!"LeanLCNF: unsupported Float primitive Float.{op}/2"
  | _, [a] =>
    match floatUnCode op with
    | some (c, rw) => rtCall1 rt "lcnf_float_un" [imm64 c, a] rw k
    | none => lfail s!"LeanLCNF: unsupported Float primitive Float.{op}/1"
  | _, _ => lfail s!"LeanLCNF: unsupported Float primitive Float.{op}/{as.length}"

/-- Inline/runtime `Char.*` externs. -/
def charPrim (rt : LArg) (op : String) (as : List LArg) (k : LArg → LM LExpr) : LM LExpr :=
  match op, as with
  | "ofNat", [n] => rtCall1 rt "lcnf_char_op" [imm64 0, n] 32 k
  | "ofNatAux", [n, _] => uintPrim rt 64 "ofNat" [n] fun r => convW 64 32 r k
  | "utf8Size", [c] => rtCall1 rt "lcnf_char_op" [imm64 1, c] 64 k
  | _, _ => lfail s!"LeanLCNF: unsupported Char primitive Char.{op}/{as.length}"

/-! ## `Int` (tagged small ints + sign-magnitude bignums) and `Int64` -/

/-- Call `lcnf_int_op(rt, intOpCode op, a, b)` with result width `resW`. -/
def intCall (rt : LArg) (op : String) (a b : LArg) (resW : Nat) (k : LArg → LM LExpr) :
    LM LExpr :=
  rtCall1 rt "lcnf_int_op" [imm64 (intOpCode op), a, b] resW k

/-- `-2^62 ≤ x < 2^62` (`x + 2^62 <u 2^63`): does the `i64` `x` fit a tagged small `Int`? -/
def intFitsSmall (x : LArg) (k : LArg → LM LExpr) : LM LExpr :=
  add64 x (imm64 (2 ^ 62)) fun t => cmpOp .ult 64 t (imm64 (2 ^ 63)) k

/-- Inline/runtime `Int.*` externs. A small `Int` `v` (`-2^62 ≤ v < 2^62`) is the tagged word
`2 * v + 1`, so signed comparison of tagged words orders the values, and a tagged word `< 2^63` is
a non-negative small `Int` with the encoding of the equal `Nat`; every other value is a
sign-magnitude bignum handled by `lcnf_int_op`. `ofNat`/`negSucc` consume their `Nat`; all other
operands are borrowed (`@&`). -/
def intPrim (rt : LArg) (op : String) (as : List LArg) (k : LArg → LM LExpr) : LM LExpr :=
  let cmpI (o : CmpOp) (a b : LArg) := tagBin rt "lcnf_int_op" (intOpCode op) 8 a b
    (fun _ j => cmpOp o 64 a b fun c => boolToU8 c fun r => pure (j r)) k
  let addSub (code : OpCode [i64, i64] [i64]) (a b : LArg) :=
    tagBin rt "lcnf_int_op" (intOpCode op) 64 a b (fun slow j =>
      op1 i64 (.ashr i64) [a, imm64 1] fun x => op1 i64 (.ashr i64) [b, imm64 1] fun y =>
      op1 i64 code [x, y] fun s => intFitsSmall s fun ok => do
        let e ← boxSmall s fun r => pure (j r)
        pure (.jnz ok e (← slow))) k
  let natLike (a : LArg) := isScalarObj a fun s => withJoin1 i64 k fun j => do
    let slow : LM LExpr := intCall rt op a (imm64 1) 64 fun r => pure (j r)
    let fast ← lshr64 a (imm64 63) fun top => cmpOp .eq 64 top (imm64 0) fun ok => do
      pure (.jnz ok (j a) (← slow))
    pure (.jnz s fast (← slow))
  match op, as with
  | "ofNat", [a] | "natAbs", [a] => natLike a
  | "add", [a, b] => addSub (.add i64) a b
  | "sub", [a, b] => addSub (.sub i64) a b
  | "decEq", [a, b] => cmpI .eq a b
  | "decLt", [a, b] => cmpI .slt a b
  | "decLe", [a, b] => cmpI .sle a b
  | "negSucc", [a] | "neg", [a] => intCall rt op a (imm64 1) 64 k
  | "decNonneg", [a] => intCall rt op a (imm64 1) 8 k
  | "mul", [a, b] | "ediv", [a, b] | "emod", [a, b] | "tdiv", [a, b] | "tmod", [a, b]
  | "divExact", [a, b, _] => intCall rt op a b 64 k
  | _, _ => lfail s!"LeanLCNF: unsupported Int primitive Int.{op}/{as.length}"

/-- `Int64.*` externs (`Int64` is an unboxed `bits 64`; two's-complement wrapping ops are the
`UInt64` ones). -/
def int64Prim (rt : LArg) (op : String) (as : List LArg) (k : LArg → LM LExpr) : LM LExpr :=
  match op, as with
  | "ofNat", [n] => uintOfNat rt 64 n k
  | "decEq", [a, b] => cmpOp .eq 64 a b fun c => boolToU8 c k
  | "decLt", [a, b] => cmpOp .slt 64 a b fun c => boolToU8 c k
  | "decLe", [a, b] => cmpOp .sle 64 a b fun c => boolToU8 c k
  | "add", _ | "sub", _ | "mul", _ | "land", _ | "lor", _ | "xor", _ | "neg", _
  | "complement", _ => uintPrim rt 64 op as k
  | "toInt", [a] =>
    convW (argBitsWidth a) 64 a fun x => withJoin1 i64 k fun j => do
      let slow ← intCall rt "ofInt64" x (imm64 1) 64 fun r => pure (j r)
      let fast ← boxSmall x fun r => pure (j r)
      intFitsSmall x fun ok => pure (.jnz ok fast slow)
  | _, _ => lfail s!"LeanLCNF: unsupported Int64 primitive Int64.{op}/{as.length}"

/-- `getObjTagNat {α} (x : @& α) : Nat` (`lean_obj_tag_nat`): a tagged scalar is its own tag,
else `box m_tag`. -/
def objTagNat (x : LArg) (k : LArg → LM LExpr) : LM LExpr :=
  isScalarObj x fun s => withJoin1 i64 k fun j => do
    let e ← loadAt i8 x 7 fun t => convW 8 64 t fun t64 => boxSmall t64 fun r => pure (j r)
    pure (.jnz s (j x) e)

/-- Kernel-reducible `s.splitOn "."` (`String.splitOn` is stuck under kernel reduction, which
`lowerModule` must survive for the `<tfs>_lower` theorems of `splice_lcnf_tflat!`). -/
def splitDot (s : String) : List String :=
  let rec go : List Char → List Char → List String
    | [], acc => [String.ofList acc.reverse]
    | c :: cs, acc =>
      if c == '.' then String.ofList acc.reverse :: go cs [] else go cs (c :: acc)
  go s.toList []

/-- Inline an imported extern by its Lean name, or fail. -/
def externPrim (rt : LArg) (name : String) (as : List LArg) (k : LArg → LM LExpr) :
    LM LExpr :=
  match splitDot name with
  | ["Nat", op] => natPrim rt op as k
  | ["Array", op] => arrayPrim rt op as k
  | "String" :: rest => stringPrim rt rest as k
  | ["ByteArray", op] => byteArrayPrim rt op as k
  | ["Float", op] => floatPrim rt op as k
  | ["Char", op] => charPrim rt op as k
  | ["Int", op] => intPrim rt op as k
  | ["Int64", op] => int64Prim rt op as k
  | ["getObjTagNat"] =>
    match as with
    | [_, x] | [x] => objTagNat x k
    | _ => lfail s!"LeanLCNF: unsupported getObjTagNat arity {as.length}"
  | ["System", "Platform", "getNumBits"] => k (imm64 (2 * 64 + 1))
  | ["outOfBounds", "_redArg"] =>
    match as with
    | [dv] => rtCall1 rt "lcnf_oob" [dv] 64 k
    | _ => lfail s!"LeanLCNF: unsupported outOfBounds arity {as.length}"
  | [ty, op] =>
    match uintWidth? ty with
    | some w => uintPrim rt w op as k
    | none => lfail s!"LeanLCNF: unsupported imported callee '{name}'"
  | _ => lfail s!"LeanLCNF: unsupported imported callee '{name}'"

end LeanQbe.T.LeanLCNF
