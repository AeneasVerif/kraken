module

public import LeanQbe.T.Bootstrap0.Types0
public import LeanQbe.T.LeanLCNF.Basic

/-!
# Bootstrap Stage A (`leanqbe0`) General Closure-Free Compiler

Strictly first-order, monomorphic, closure-free compiler `leanqbe0Compile : TFlatModule0 →
CompileRes0`:
* **Zero closures / globals:** no lambdas, no partial applications, no `String` literals, no `Nat`
  literals `≥ 2^63`, no `ExtractClosed` or `__boxed_const_` heap constants, all functions `≤ 5`
  arguments.
* **100% acyclic lowered call graph:** iterative `UInt32`-bounded worklists and tail-recursive
  helpers (`0` mutual recursion, `0` non-tail calls).
* **Kernel-chunk friendly (`≤ 125` fns, `≤ 250` directives/fn):** scalar `Ty0`/`Width`/`UInt32` ops,
  borrowed read-only validators (`0` error-branch RC), `@[noinline]` accessors/emitters, and
  `≤ 5`-arg helpers.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T
open LeanQbe.T.LeanLCNF

/-- Proof lemma allowing `UInt32` fuel decrement without runtime `Nat` overhead. -/
theorem u32Sub1Lt0 (n : UInt32) (h : n ≠ 0) : (n - 1).toNat < n.toNat := by
  have hn : n.toNat ≠ 0 := by
    intro hz
    apply h
    calc n = UInt32.ofNat n.toNat := UInt32.ofNat_toNat.symm
      _ = UInt32.ofNat 0 := by rw [hz]
      _ = 0 := rfl
  have h1 : (1 : UInt32) ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
  rw [UInt32.toNat_sub_of_le n 1 h1]
  exact Nat.sub_lt (Nat.pos_of_ne_zero hn) Nat.zero_lt_one

/-! ## 1. Scalar `Ty0` / `Width` / `UInt32` Helpers and Array Accessors -/

/-- Scalar code for `Ty0` (`0..4`). -/
@[inline] def ty0Code : Ty0 → UInt32
  | .bool => 0 | .b8 => 1 | .b16 => 2 | .b32 => 3 | .b64 => 4

/-- Equality on `Ty0` using single `UInt32` compare. -/
@[inline] def ty0Eq (a b : Ty0) : Bool := decide (ty0Code a = ty0Code b)

/-- Bit width of `Width` as `UInt32` (`8/16/32/64`). -/
@[inline] def widthBits0 : Width → UInt32
  | .W8 => 8 | .W16 => 16 | .W32 => 32 | .W64 => 64

/-- Equality on `Width`. -/
@[inline] def widthEq0 (a b : Width) : Bool := decide (widthBits0 a = widthBits0 b)

/-- `Ty0` corresponding to `Width`. -/
@[inline] def widthTy0 : Width → Ty0
  | .W8 => .b8 | .W16 => .b16 | .W32 => .b32 | .W64 => .b64

/-- `Width` corresponding to `Ty0` (`.bool` maps to `.W8`). -/
@[inline] def tyWidth0 : Ty0 → Width
  | .bool => .W8 | .b8 => .W8 | .b16 => .W16 | .b32 => .W32 | .b64 => .W64

/-- Map `CmpOp` to `CondCode`. -/
@[inline] def condOf0 : CmpOp → CondCode
  | .eq => .z | .ne => .nz
  | .ult => .c | .ule => .be | .ugt => .a | .uge => .nc
  | .slt => .l | .sle => .le | .sgt => .g | .sge => .ge

/-- Maximum of two `UInt32`s. -/
@[inline] def u32Max0 (a b : UInt32) : UInt32 := if decide (a < b) then b else a

/-- Check whether `UInt64` frame offset `< 2^31`. -/
@[inline] def fitsImm31U0 (n : UInt64) : Bool := decide (n < 0x80000000)

/-- SysV 16-byte-aligned frame byte size (`frameSize ns ≡ 8 (mod 16)`). -/
@[inline] def x64FrameSizeU0 (ns : UInt32) : UInt64 :=
  let n := ns.toUInt64
  let pad : UInt64 := if decide (UInt64.land n 1 = 0) then 8 else 0
  UInt64.add (UInt64.mul n 8) pad

/-- Mask immediate to `Width`. -/
@[inline] def maskImmW0 (w : Width) (val : UInt64) : UInt64 :=
  match w with
  | .W8 => UInt64.land val 0xff
  | .W16 => UInt64.land val 0xffff
  | .W32 => UInt64.land val 0xffffffff
  | .W64 => val

/-- Structural equality on `List Ty0`. -/
def tyListEq0 (xs ys : List Ty0) : Bool :=
  match xs with
  | [] => match ys with | [] => true | _ => false
  | x :: xs' =>
    match ys with
    | [] => false
    | y :: ys' => if ty0Eq x y then tyListEq0 xs' ys' else false

/-- Length of `List Ty0` as `UInt32`. -/
def tyLenU0 (xs : List Ty0) (acc : UInt32) : UInt32 :=
  match xs with
  | [] => acc
  | _ :: rest => tyLenU0 rest (acc + 1)

/-- Length of `List Arg0` as `UInt32`. -/
def argLenU0 (xs : List Arg0) (acc : UInt32) : UInt32 :=
  match xs with
  | [] => acc
  | _ :: rest => argLenU0 rest (acc + 1)

/-- Read `List Ty0` element code at index `i` (`99` if out of bounds). -/
def listGetTyCode0 (xs : List Ty0) (i : UInt32) : UInt32 :=
  match xs with
  | [] => 99
  | x :: rest => if i = 0 then ty0Code x else listGetTyCode0 rest (i - 1)

/-- Tail-recursive list index lookup for `List UInt32`. -/
def listGetU32 (xs : List UInt32) (i : UInt32) : UInt32 :=
  match xs with
  | [] => 0
  | x :: rest => if i = 0 then x else listGetU32 rest (i - 1)

/-- Tail-recursive list index lookup for `List (List Ty0)`. -/
def listGetSig0 (xs : List (List Ty0)) (i : UInt32) : Option (List Ty0) :=
  match xs with
  | [] => none
  | x :: rest => if i = 0 then some x else listGetSig0 rest (i - 1)

/-- Tail-recursive reverse for `List Dir0`. -/
def revDirAux0 (xs acc : List Dir0) : List Dir0 :=
  match xs with
  | [] => acc
  | d :: rest => revDirAux0 rest (d :: acc)

/-- SysV ABI argument (`isRet = false`) or return (`isRet = true`) register by index. -/
def abiRegAt0 (isRet : Bool) (i : UInt32) : Reg64 :=
  if isRet then
    if i = 0 then .rax else if i = 1 then .rdx else if i = 2 then .rcx
    else if i = 3 then .rsi else if i = 4 then .rdi else if i = 5 then .r8 else .r9
  else
    if i = 0 then .rdi else if i = 1 then .rsi else if i = 2 then .rdx
    else if i = 3 then .rcx else if i = 4 then .r8 else .r9

/-- Read `UInt32` from `Array Nat` (`@[noinline]` avoids `Nat`/bounds bloat at callers). -/
@[noinline] def arrGetU0 (arr : Array Nat) (i : UInt32) : UInt32 :=
  UInt32.ofNat (arr.getD i.toNat 0)

/-- Write `UInt32` into `Array Nat` (`0` `__boxed_const_` globals). -/
@[inline] def arrSetU0 (arr : Array Nat) (i v : UInt32) : Array Nat :=
  arr.set! i.toNat v.toNat

/-- Read `List UInt32` from `Array (List UInt32)` (`@[noinline]` keeps `emitJump0` small). -/
@[noinline] def arrGetLL0 (arr : Array (List UInt32)) (i : UInt32) : List UInt32 :=
  arr.getD i.toNat []

/-- Borrowed check for leaf terminators (`.tailCall`/`.jump`/`.ret`/`.exit`/`.hlt`). -/
def isTerm0 : TFlat0 → Bool
  | .tailCall _ _ _ => true
  | .jump _ _ => true
  | .ret _ => true
  | .exit _ _ _ => true
  | .hlt => true
  | _ => false

/-- Extract straight-line continuation `k` (`@[noinline]` prevents `cases` bloat at callers). -/
@[noinline] def linK0 (node : TFlat0) : TFlat0 :=
  match node with
  | .let1 _ _ k => k
  | .let2Umulw64 _ _ k => k
  | .load _ _ k => k
  | .store _ _ _ k => k
  | .call _ _ _ _ k => k
  | _ => node

/-- Extract bound result count (`0/1/2/bs.len`) for straight-line nodes. -/
def linCnt0 (node : TFlat0) : UInt32 :=
  match node with
  | .let1 _ _ _ => 1
  | .let2Umulw64 _ _ _ => 2
  | .load _ _ _ => 1
  | .call _ _ bs _ _ => tyLenU0 bs 0
  | _ => 0

/-! ## 2. `@[noinline]` `Dir0` Emitters (Zero `ExtractClosed` Globals) -/

/-- Packed directive emitter A (`0=movRR, 1=movzx32, 2=ldMem, 3=stMem, 4=testbRR, 5=mulq`). -/
@[noinline] def pushDRR0 (tag : UInt32) (w : Width) (rd rs : Reg64)
    (acc : List Dir0) : List Dir0 :=
  if decide (tag = 0) then .movRR w rd rs :: acc
  else if decide (tag = 1) then .movzx32 w rd rs :: acc
  else if decide (tag = 2) then .ldMem w rd rs :: acc
  else if decide (tag = 3) then .stMem w rd rs :: acc
  else if decide (tag = 4) then .testbRR rd rs :: acc
  else .mulq rd :: acc

/-- Packed emitter B (`0=not, 1=neg, 2=divU, 3=divS, 4=spSubR, 5=spAddR, 6=xorRR`). -/
@[noinline] def pushDUnary0 (tag : UInt32) (w : Width) (rd rs : Reg64)
    (acc : List Dir0) : List Dir0 :=
  if decide (tag = 0) then .unary w false rd :: acc
  else if decide (tag = 1) then .unary w true rd :: acc
  else if decide (tag = 2) then .divCore w false rs :: acc
  else if decide (tag = 3) then .divCore w true rs :: acc
  else if decide (tag = 4) then .spAddReg true rd :: acc
  else if decide (tag = 5) then .spAddReg false rd :: acc
  else .aluRR w .xor rd rs :: acc

/-- Packed immediate directive emitter (`0=movRI, 1=spAdd false, 2=spAdd true, 3=shMaskCl`). -/
@[noinline] def pushDImm0 (tag : UInt32) (rd : Reg64) (imm : UInt64)
    (acc : List Dir0) : List Dir0 :=
  if decide (tag = 0) then .movRI rd imm :: acc
  else if decide (tag = 1) then .spAdd false imm :: acc
  else if decide (tag = 2) then .spAdd true imm :: acc
  else .shMaskCl imm :: acc

/-- Inline two-address ALU directive emitter (`w` and `k` are runtime inside `emitBinAlu0`). -/
@[inline] def pushDAlu0 (w : Width) (k : AluKind0) (rd rs : Reg64)
    (acc : List Dir0) : List Dir0 :=
  .aluRR w k rd rs :: acc

/-- Inline `%cl` shift/rotate directive emitter (`w` and `k` are runtime). -/
@[inline] def pushDShift0 (w : Width) (k : ShiftKind0) (rd : Reg64)
    (acc : List Dir0) : List Dir0 :=
  .shiftCl w k rd :: acc

/-- Non-inlined sign-extending move emitter (`keeps emitDiv0 & emitConvSext0 <= 210 dirs`). -/
@[noinline] def pushDMovsx0 (wDst : Width) (rd : Reg64) (wSrc : Width) (rs : Reg64)
    (acc : List Dir0) : List Dir0 :=
  .movsx wDst rd wSrc rs :: acc

/-- Zero-extend low bits of register `r` to 64 bits (`non-inline` keeps Isel small). -/
def emitCanon0 (w : Width) (r : Reg64) (acc : List Dir0) : List Dir0 :=
  match w with
  | .W8 => pushDRR0 1 .W8 r r acc
  | .W16 => pushDRR0 1 .W16 r r acc
  | .W32 => pushDRR0 0 .W32 r r acc
  | .W64 => acc

/-- Emit stack slot load (`isLd = true`) or store (`isLd = false`) (`≤ 5` args, `0` globals). -/
def emitSlotMem0 (isLd : Bool) (reg : Reg64) (slot : UInt32) (acc : List Dir0) : List Dir0 :=
  let off := UInt64.mul slot.toUInt64 8
  if isLd then
    if fitsImm31U0 off then .ldSlot reg off :: acc
    else .ldSlotIdx reg .r10 :: pushDImm0 0 .r10 off acc
  else
    if fitsImm31U0 off then .stSlot off reg :: acc
    else .stSlotIdx .r10 reg :: pushDImm0 0 .r10 off acc

/-! ## 3. `Legal0`: Borrowed Read-Only Validation (`0` Error-Branch RC) -/

/-- Immutable module/function context for `Legal0`. -/
structure LegalCtx0 where
  sigs : List ExtSig0
  exits : List Sym0
  curRs : List Ty0

/-- Worklist item for `Legal0`. -/
structure LegalItem0 where
  node : TFlat0
  venv : List Ty0
  lenv : List (List Ty0)

/-- Push `ts` onto `venv` in `Flat.pushTypes` order (`last` at index `0`). -/
def pushTys0 (ts : List Ty0) (acc : List Ty0) : List Ty0 :=
  match ts with
  | [] => acc
  | t :: rest => pushTys0 rest (t :: acc)

/-- Check that `arg` matches expected scalar `Ty0` `expT` in `venv`. -/
def checkArg0 (venv : List Ty0) (expT : Ty0) (arg : Arg0) : Bool :=
  match arg with
  | .var idx => decide (listGetTyCode0 venv idx = ty0Code expT)
  | .immBool _ => ty0Eq expT .bool
  | .immBits w _ => ty0Eq (widthTy0 w) expT

/-- Check `args` matches parameter `List Ty0` in `venv`. -/
def checkArgs0 (venv : List Ty0) (ts : List Ty0) (args : List Arg0) : Bool :=
  match ts with
  | [] => match args with | [] => true | _ => false
  | t :: ts' =>
    match args with
    | [] => false
    | a :: args' => if checkArg0 venv t a then checkArgs0 venv ts' args' else false

/-- Check `sym` exists in `sigs` with exact signature `(as, rs)`. -/
def hasSig0 (sigs : List ExtSig0) (sym : Sym0) (as rs : List Ty0) : Bool :=
  match sigs with
  | [] => false
  | s :: rest =>
    if s.name = sym then tyListEq0 s.as as && tyListEq0 s.rs rs
    else hasSig0 rest sym as rs

/-- Check `sym` appears in `fns` (duplicate fn symbol guard). -/
def hasFnSym0 (fns : List TFlatFn0) (sym : Sym0) : Bool :=
  match fns with
  | [] => false
  | f :: rest => if f.name = sym then true else hasFnSym0 rest sym

/-- Check `sym` appears in `exits`. -/
def hasExit0 (exits : List Sym0) (sym : Sym0) : Bool :=
  match exits with
  | [] => false
  | e :: rest => if e = sym then true else hasExit0 rest sym

/-- Validate `.bin` binary arithmetic / bitwise / shift opcodes. -/
def checkBinOp0 (venv : List Ty0) (b : BinOp0) (t : Ty0) (args : List Arg0) : Bool :=
  let isLog := match b with | .and | .or | .xor => true | _ => false
  let okTy := match t with | .bool => isLog | _ => true
  match args with
  | [a, bArg] => okTy && checkArg0 venv t a && checkArg0 venv t bArg
  | _ => false

/-- Validate `.un` / `.bin` / `.select` opcodes (`args` match scalar signature). `.un .neg .bool` is
rejected: `negb` maps `true` to `0xff`, whereas `OpCode.wp (.neg .bool)` is the identity. -/
def checkOpArith0 (venv : List Ty0) (op : OpCode0) (args : List Arg0) : Bool :=
  match op with
  | .un .neg .bool => false
  | .un _ t => match args with | [a] => checkArg0 venv t a | _ => false
  | .bin b t => checkBinOp0 venv b t args
  | .select t =>
    match args with
    | [c, a, b] => checkArg0 venv .bool c && checkArg0 venv t a && checkArg0 venv t b
    | _ => false
  | _ => false

/-- Validate `.conv` opcode (`ofBool`, `zext`, `sext`, `trunc`). -/
def checkConv0 (venv : List Ty0) (c : ConvOp0) (m n : Width) (args : List Arg0) : Bool :=
  let mw := widthBits0 m
  let nw := widthBits0 n
  let okDir :=
    match c with
    | .ofBool => true
    | .zext => decide (mw ≤ nw)
    | .sext => decide (mw ≤ nw)
    | .trunc => decide (nw ≤ mw)
  let argT := match c with | .ofBool => Ty0.bool | _ => widthTy0 m
  match args with | [a] => okDir && checkArg0 venv argT a | _ => false

/-- Validate any `OpCode0` (`umulw64` belongs to `.let2Umulw64`, rejected here). -/
def checkOp0 (venv : List Ty0) (op : OpCode0) (args : List Arg0) : Bool :=
  match op with
  | .un _ _ | .bin _ _ | .select _ => checkOpArith0 venv op args
  | .cmp _ t =>
    let notBool := match t with | .bool => false | _ => true
    match args with | [a, b] => notBool && checkArg0 venv t a && checkArg0 venv t b | _ => false
  | .conv c m n => checkConv0 venv c m n args
  | .div _ w =>
    let wt := widthTy0 w
    match args with | [a, b] => checkArg0 venv wt a && checkArg0 venv wt b | _ => false
  | .umulw64 => false

/-- Borrowed read-only check for `.let1`, `.let2Umulw64`, `.load`, `.store` (`0` = ok). -/
def checkLegalOp0 (venv : List Ty0) (node : TFlat0) : UInt32 :=
  match node with
  | .let1 op args _ => if checkOp0 venv op args then 0 else 10
  | .let2Umulw64 a b _ =>
    if checkArg0 venv .b64 a && checkArg0 venv .b64 b then 0 else 11
  | .load _ addr _ => if checkArg0 venv .b64 addr then 0 else 12
  | .store t val addr _ =>
    if checkArg0 venv t val && checkArg0 venv .b64 addr then 0 else 13
  | _ => 98

/-- Borrowed read-only check for `.call`, `.tailCall`, `.exit` (`0` = ok). -/
def checkLegalCall0 (ctx : LegalCtx0) (venv : List Ty0) (node : TFlat0) : UInt32 :=
  match node with
  | .call fnSym as bs args _ =>
    if decide (tyLenU0 as 0 ≤ 6) && decide (tyLenU0 bs 0 ≤ 7) &&
        hasSig0 ctx.sigs fnSym as bs && checkArgs0 venv as args then 0
    else 14
  | .tailCall fnSym as args =>
    if decide (tyLenU0 as 0 ≤ 6) && hasSig0 ctx.sigs fnSym as ctx.curRs &&
        checkArgs0 venv as args then 0
    else 15
  | .exit fnSym as args =>
    if decide (tyLenU0 as 0 ≤ 6) && hasExit0 ctx.exits fnSym &&
        checkArgs0 venv as args then 0
    else 19
  | _ => 98

/-- Borrowed read-only check for `.jnz`, `.jump`, `.ret`, `.hlt`, `.group` (`0` = ok). -/
def checkLegalCtrl0 (ctx : LegalCtx0) (venv : List Ty0) (lenv : List (List Ty0))
    (node : TFlat0) : UInt32 :=
  match node with
  | .jnz c _ _ => if checkArg0 venv .bool c then 0 else 16
  | .jump j args =>
    match listGetSig0 lenv j with
    | some pts => if checkArgs0 venv pts args then 0 else 17
    | none => 17
  | .ret vs => if checkArgs0 venv ctx.curRs vs then 0 else 18
  | .hlt | .group _ _ => 0
  | _ => 98

/-- Extend `lenv` with all block signatures from `.group` bodies. -/
def legalAddSigs0 (bodies : List (List Ty0 × TFlat0)) (acc : List (List Ty0)) :
    List (List Ty0) :=
  match bodies with
  | [] => acc
  | (pts, _) :: rest => legalAddSigs0 rest (pts :: acc)

/-- Push `.group` block items onto `work` (always succeeds for `Ty0`). -/
def legalPushGroup0 (bodies : List (List Ty0 × TFlat0)) (venv : List Ty0)
    (lenv' : List (List Ty0)) (work : List LegalItem0) : List LegalItem0 :=
  match bodies with
  | [] => work
  | (pts, b) :: rest =>
    let item := LegalItem0.mk b (pushTys0 pts venv) lenv'
    legalPushGroup0 rest venv lenv' (item :: work)

/-- Result type of a single `OpCode0` (`@&` borrowed). -/
def opRetTy0 : OpCode0 → Ty0
  | .un _ t => t
  | .bin _ t => t
  | .select t => t
  | .cmp _ _ => .bool
  | .conv _ _ wDst => widthTy0 wDst
  | .div _ w => widthTy0 w
  | .umulw64 => .b64

/-- Compute updated `venv` after straight-line binding node (`@&` borrowed `0` RC). -/
def legalNextVenv0 (node : TFlat0) (venv : List Ty0) : List Ty0 :=
  match node with
  | .let1 op _ _ => opRetTy0 op :: venv
  | .let2Umulw64 _ _ _ => .b64 :: .b64 :: venv
  | .load t _ _ => t :: venv
  | .call _ _ bs _ _ => pushTys0 bs venv
  | _ => venv

/-- Enqueue straight-line continuation using shared `linK0` and `legalNextVenv0` (`0` `if`s). -/
def legalAdvLin0 (cur : LegalItem0) (work : List LegalItem0) : List LegalItem0 :=
  LegalItem0.mk (linK0 cur.node) (legalNextVenv0 cur.node cur.venv) cur.lenv :: work

/-- Enqueue `.jnz` continuations onto `work` (`0` `TFlat0` match). -/
def legalAdvJnz0 (t e : TFlat0) (cur : LegalItem0)
    (work : List LegalItem0) : List LegalItem0 :=
  LegalItem0.mk t cur.venv cur.lenv :: LegalItem0.mk e cur.venv cur.lenv :: work

/-- Enqueue `.group` continuations onto `work` (`0` `TFlat0` match). -/
def legalAdvGroup0 (bodies : List (List Ty0 × TFlat0)) (k : TFlat0) (cur : LegalItem0)
    (work : List LegalItem0) : List LegalItem0 :=
  let lenv' := legalAddSigs0 bodies cur.lenv
  LegalItem0.mk k cur.venv lenv' :: legalPushGroup0 bodies cur.venv lenv' work

/-- Enqueue validated continuations of `cur.node` onto `work`. -/
def legalAdvance0 (cur : LegalItem0) (work : List LegalItem0) : List LegalItem0 :=
  if isTerm0 cur.node then work
  else
    match cur.node with
    | .jnz _ t e => legalAdvJnz0 t e cur work
    | .group bodies k => legalAdvGroup0 bodies k cur work
    | _ => legalAdvLin0 cur work

/-- Check single node validity for `Legal0` (`0` = ok). -/
def legalCheckNode0 (ctx : LegalCtx0) (cur : LegalItem0) : UInt32 :=
  match cur.node with
  | .let1 _ _ _ | .let2Umulw64 _ _ _ | .load _ _ _ | .store _ _ _ _ =>
    checkLegalOp0 cur.venv cur.node
  | .call _ _ _ _ _ | .tailCall _ _ _ | .exit _ _ _ =>
    checkLegalCall0 ctx cur.venv cur.node
  | _ => checkLegalCtrl0 ctx cur.venv cur.lenv cur.node

/-- Iterative `UInt32`-bounded worklist loop for `Legal0`. -/
def legalWorkLoop0 (fuel : UInt32) (ctx : LegalCtx0) (work : List LegalItem0) : UInt32 :=
  if h : fuel = 0 then 99
  else
    have _ := u32Sub1Lt0 fuel h
    match work with
    | [] => 0
    | cur :: rest =>
      let ec := legalCheckNode0 ctx cur
      if ec = 0 then legalWorkLoop0 (fuel - 1) ctx (legalAdvance0 cur rest) else ec
termination_by fuel.toNat

/-- Borrowed check that all externs satisfy SysV scalar arity limits (`≤ 6` args, `≤ 7` rets). -/
def allValidExts0 (exts : List ExtSig0) : Bool :=
  match exts with
  | [] => true
  | e :: rest =>
    if decide (tyLenU0 e.as 0 ≤ 6) && decide (tyLenU0 e.rs 0 ≤ 7) then
      allValidExts0 rest
    else false

/-- Prepend `exts` onto `acc`. -/
def prepSigsExts0 (exts : List ExtSig0) (acc : List ExtSig0) : List ExtSig0 :=
  match exts with
  | [] => acc
  | e :: rest => prepSigsExts0 rest (e :: acc)

/-- Prepend module `fns` signatures onto `acc`. -/
def prepSigsFns0 (fns : List TFlatFn0) (acc : List ExtSig0) : List ExtSig0 :=
  match fns with
  | [] => acc
  | f :: rest => prepSigsFns0 rest (ExtSig0.mk f.name f.as f.rs :: acc)

/-- Borrowed check for function header validity (duplicate symbol & ABI arities). -/
def checkFnHdr0 (rest : List TFlatFn0) (fn : TFlatFn0) : Bool :=
  !hasFnSym0 rest fn.name && decide (tyLenU0 fn.as 0 ≤ 6) && decide (tyLenU0 fn.rs 0 ≤ 7)

/-- Validate one function header and body (`0` = ok). -/
def checkOneFn0 (exits : List Sym0) (sigs : List ExtSig0) (rest : List TFlatFn0)
    (fn : TFlatFn0) : UInt32 :=
  if checkFnHdr0 rest fn then
    let ctx := LegalCtx0.mk sigs exits fn.rs
    legalWorkLoop0 0x7fffffff ctx [LegalItem0.mk fn.body (pushTys0 fn.as []) []]
  else 1

/-- Validate function list sequentially; returns packed `UInt64` (`0` = ok). -/
def legalFnsLoop0 (exits : List Sym0) (sigs : List ExtSig0) (fns : List TFlatFn0)
    (idx : UInt32) : UInt64 :=
  match fns with
  | [] => 0
  | fn :: rest =>
    let ec := checkOneFn0 exits sigs rest fn
    if ec = 0 then legalFnsLoop0 exits sigs rest (idx + 1)
    else UInt64.lor (UInt64.shiftLeft ec.toUInt64 32) idx.toUInt64

/-! ## 4. `PrePass0`: Flat `Array Nat` Use Counting & Escape Analysis -/

/-- Flat state for `PrePass0` (`Array Nat` holds unboxed scalars, `0` `__boxed_const_`s). -/
structure PreSt0 where
  nextVid : UInt32
  defScope : Array Nat
  uses : Array Nat
  escaped : Array Nat

/-- Worklist item for `PrePass0`. -/
structure PreItem0 where
  node : TFlat0
  venv : List UInt32
  scope : UInt32

/-- Output of `.group` / step update in `PrePass0`. -/
structure PreOut0 where
  st : PreSt0
  nextScope : UInt32
  work : List PreItem0

/-- Record one operand use: increment in-scope `uses` or mark `escaped`. -/
def preNoteArg0 (scope : UInt32) (venv : List UInt32) (st : PreSt0) (a : Arg0) : PreSt0 :=
  match a with
  | .var idx =>
    let vid := listGetU32 venv idx
    let ds := arrGetU0 st.defScope vid
    if ds = scope then
      let u := arrGetU0 st.uses vid
      { st with uses := arrSetU0 st.uses vid (u + 1) }
    else
      { st with escaped := arrSetU0 st.escaped vid 1 }
  | _ => st

/-- Record all operands in `args`. -/
def preNoteArgs0 (scope : UInt32) (venv : List UInt32) (st : PreSt0)
    (args : List Arg0) : PreSt0 :=
  match args with
  | [] => st
  | a :: rest => preNoteArgs0 scope venv (preNoteArg0 scope venv st a) rest

/-- Bind `n` new variables at `scope` onto `venv` and push entries into `PreSt0`. -/
def preBindLoop0 (n scope : UInt32) (venv : List UInt32) (st : PreSt0) :
    List UInt32 × PreSt0 :=
  if h : n = 0 then (venv, st)
  else
    have _ := u32Sub1Lt0 n h
    let vid := st.nextVid
    let st' : PreSt0 :=
      { nextVid := vid + 1
        defScope := st.defScope.push scope.toNat
        uses := st.uses.push 0
        escaped := st.escaped.push 0 }
    preBindLoop0 (n - 1) scope (vid :: venv) st'
termination_by n.toNat

/-- Allocate `PreSt0` and bind initial function parameter variables. -/
def preInit0 (as : List Ty0) : List UInt32 × PreSt0 :=
  let nArgs := tyLenU0 as 0
  let cap := Nat.add 32 nArgs.toNat
  let pre0 := PreSt0.mk 0 (Array.emptyWithCapacity cap)
    (Array.emptyWithCapacity cap) (Array.emptyWithCapacity cap)
  preBindLoop0 nArgs 0 [] pre0

/-- Bind one `.group` block's parameters at a fresh scope and stage its item onto `out.work`. -/
def prePushOne0 (entry : List Ty0 × TFlat0) (venv : List UInt32) (out : PreOut0) : PreOut0 :=
  let (pts, b) := entry
  let sB := out.nextScope
  let (venvB, st1) := preBindLoop0 (tyLenU0 pts 0) sB venv out.st
  PreOut0.mk st1 (sB + 1) (PreItem0.mk b venvB sB :: out.work)

/-- Step 1 of `.group`: bind block parameters in forward order (`b_0..b_{m-1}`, matching
`regaPrepGroup0`), staging items onto `out.work` in reverse (`[b_{m-1}, ..., b_0]`). -/
def prePushGroup0 (bodies : List (List Ty0 × TFlat0)) (venv : List UInt32)
    (out : PreOut0) : PreOut0 :=
  match bodies with
  | [] => out
  | entry :: rest => prePushGroup0 rest venv (prePushOne0 entry venv out)

/-- Step 2 of `.group`: push staged block items onto `work` so `b_0` ends on top (bodies are then
popped as `b_0..b_{m-1}`, the exact `vid` binding order of `regaEnqueueGroup0`). -/
def preEnqueueGroup0 (staged : List PreItem0) (work : List PreItem0) : List PreItem0 :=
  match staged with
  | [] => work
  | item :: rest => preEnqueueGroup0 rest (item :: work)

/-- Record operand uses for any `TFlat0` node without duplicating continuation binding. -/
def preNoteNode0 (scope : UInt32) (venv : List UInt32) (node : TFlat0) (st : PreSt0) :
    PreSt0 :=
  match node with
  | .let1 _ args _ => preNoteArgs0 scope venv st args
  | .let2Umulw64 a b _ => preNoteArg0 scope venv (preNoteArg0 scope venv st a) b
  | .load _ addr _ => preNoteArg0 scope venv st addr
  | .store _ val addr _ => preNoteArg0 scope venv (preNoteArg0 scope venv st val) addr
  | .call _ _ _ args _ => preNoteArgs0 scope venv st args
  | .tailCall _ _ args => preNoteArgs0 scope venv st args
  | .jump _ args => preNoteArgs0 scope venv st args
  | .ret args => preNoteArgs0 scope venv st args
  | .exit _ _ args => preNoteArgs0 scope venv st args
  | .jnz c _ _ => preNoteArg0 scope venv st c
  | .hlt | .group _ _ => st

/-- Push `.jnz` branches onto `PreOut0` (`4` args, `0` `TFlat0` match). -/
def preStepJnz0 (t e : TFlat0) (cur : PreItem0) (out : PreOut0) : PreOut0 :=
  let sT := out.nextScope
  PreOut0.mk out.st (sT + 2)
    (PreItem0.mk e cur.venv (sT + 1) :: PreItem0.mk t cur.venv sT :: out.work)

/-- Push `.group` bodies (staged via `prePushGroup0` from `out0`, whose `work` is `[]`, then
enqueued via `preEnqueueGroup0`) and the continuation `k` (scope allocated after the bodies) onto
`rest`, popping `k, b_0, ..., b_{m-1}` exactly like `groupEnqCont0` (`5` args, `0` `TFlat0`
match). -/
def preStepGroup0 (bodies : List (List Ty0 × TFlat0)) (k : TFlat0) (cur : PreItem0)
    (out0 : PreOut0) (rest : List PreItem0) : PreOut0 :=
  let res := prePushGroup0 bodies cur.venv out0
  let sK := res.nextScope
  PreOut0.mk res.st (sK + 1) (PreItem0.mk k cur.venv sK :: preEnqueueGroup0 res.work rest)

/-- Package straight-line `preBindLoop0` result into `PreOut0` (`5` args). -/
def preLinFinish0 (k : TFlat0) (scope nextSc : UInt32) (vs : List UInt32 × PreSt0)
    (rest : List PreItem0) : PreOut0 :=
  PreOut0.mk vs.2 nextSc (PreItem0.mk k vs.1 scope :: rest)

/-- Push straight-line continuation unconditionally (`0` `if`s, `0` `TFlat0` match). -/
def preStepLin0 (cur : PreItem0) (st1 : PreSt0) (nextSc : UInt32)
    (rest : List PreItem0) : PreOut0 :=
  let vs := preBindLoop0 (linCnt0 cur.node) cur.scope cur.venv st1
  preLinFinish0 (linK0 cur.node) cur.scope nextSc vs rest

/-- Advance `PrePass0` worklist after operand uses for `cur` have been noted. -/
def preStepPush0 (cur : PreItem0) (st1 : PreSt0) (nextSc : UInt32)
    (rest : List PreItem0) : PreOut0 :=
  if isTerm0 cur.node then PreOut0.mk st1 nextSc rest
  else
    match cur.node with
    | .jnz _ t e => preStepJnz0 t e cur (PreOut0.mk st1 nextSc rest)
    | .group bodies k => preStepGroup0 bodies k cur (PreOut0.mk st1 nextSc []) rest
    | _ => preStepLin0 cur st1 nextSc rest

/-- Iterative `UInt32`-bounded worklist pass for `PrePass0`. -/
def preWorkLoop0 (fuel : UInt32) (nextSc : UInt32) (st : PreSt0)
    (work : List PreItem0) : PreSt0 :=
  if h : fuel = 0 then st
  else
    have _ := u32Sub1Lt0 fuel h
    match work with
    | [] => st
    | cur :: rest =>
      let st1 := preNoteNode0 cur.scope cur.venv cur.node st
      let out := preStepPush0 cur st1 nextSc rest
      preWorkLoop0 (fuel - 1) out.nextScope out.st out.work
termination_by fuel.toNat

/-! ## 5. `Isel0` & `Frame0`: Baseline x86-64 Instruction Selection -/

/-- Load operand `a` into register `rd` (`rd` and `%r10` only clobbered). -/
def emitLoadArg0 (rd : Reg64) (a : Arg0) (venv : List UInt32) (vslot : Array Nat)
    (acc : List Dir0) : List Dir0 :=
  match a with
  | .var idx =>
    let vid := listGetU32 venv idx
    emitSlotMem0 true rd (arrGetU0 vslot vid) acc
  | .immBool b => pushDImm0 0 rd (if b then 1 else 0) acc
  | .immBits w val => pushDImm0 0 rd (maskImmW0 w val) acc

/-- Emit unary op (`%rdi` → `%rax`); `.neg .bool` never reaches here (see `checkOpArith0`). -/
def emitUn0 (op : UnOp0) (t : Ty0) (acc : List Dir0) : List Dir0 :=
  let acc1 := pushDRR0 0 .W64 .rax .rdi acc
  let w := tyWidth0 t
  match op with
  | .copy => emitCanon0 w .rax acc1
  | .neg => emitCanon0 w .rax (pushDUnary0 1 w .rax .rax acc1)
  | .not =>
    match t with
    | .bool =>
      pushDRR0 1 .W8 .rax .rax (pushDUnary0 6 .W32 .rax .r11 (pushDImm0 0 .r11 1 acc1))
    | _ => emitCanon0 w .rax (pushDUnary0 0 w .rax .rax acc1)

/-- Emit shift or rotate binary op (`%rdi`, `%rsi` → `%rax`). -/
def emitBinShift0 (b : BinOp0) (t : Ty0) (acc : List Dir0) : List Dir0 :=
  let w := tyWidth0 t
  let sk : ShiftKind0 :=
    match b with
    | .shl => .shl | .lshr => .lshr | .ashr => .ashr | .rotl => .rotl | _ => .rotr
  let acc2 := pushDRR0 0 .W64 .rcx .rsi (pushDRR0 0 .W64 .rax .rdi acc)
  let acc3 :=
    match w with
    | .W8 => pushDImm0 3 .rcx 7 acc2
    | .W16 => pushDImm0 3 .rcx 15 acc2
    | _ => acc2
  emitCanon0 w .rax (pushDShift0 w sk .rax acc3)

/-- Emit two-address ALU binary op (`%rdi`, `%rsi` → `%rax`). -/
def emitBinAlu0 (b : BinOp0) (t : Ty0) (acc : List Dir0) : List Dir0 :=
  let w := tyWidth0 t
  let ak : AluKind0 :=
    match b with
    | .add => .add | .sub => .sub | .mul => .mul | .and => .and | .or => .or | _ => .xor
  let acc1 := pushDRR0 0 .W64 .rax .rdi acc
  match t with
  | .bool => pushDRR0 1 .W8 .rax .rax (pushDAlu0 .W32 ak .rax .rsi acc1)
  | .b8 =>
    let wAlu := match ak with | .mul => Width.W32 | _ => Width.W8
    pushDRR0 1 .W8 .rax .rax (pushDAlu0 wAlu ak .rax .rsi acc1)
  | _ => emitCanon0 w .rax (pushDAlu0 w ak .rax .rsi acc1)

/-- Emit integer comparison (`%rdi`, `%rsi` → `%rax` `.bool`) or conditional select. -/
def emitCmpSelect0 (isSel : Bool) (co : CmpOp) (t : Ty0) (acc : List Dir0) : List Dir0 :=
  if isSel then
    let cw := match t with | .b64 => Width.W64 | _ => Width.W32
    let acc1 := pushDRR0 4 .W8 .rdi .rdi acc
    .cmovcc cw .nz .rax .rsi :: pushDRR0 0 cw .rax .rdx acc1
  else
    let w := tyWidth0 t
    pushDRR0 1 .W8 .rax .rax (.setcc (condOf0 co) .rax :: .cmpRR w .rdi .rsi :: acc)

/-- Emit `ofBool` / `zext` / `trunc` (`%rdi` → `%rax`). -/
def emitConvZextTrunc0 (op : ConvOp0) (wSrc wDst : Width) (acc : List Dir0) : List Dir0 :=
  match op with
  | .ofBool => pushDRR0 1 .W8 .rax .rdi acc
  | .zext =>
    if widthEq0 wSrc wDst then emitCanon0 wDst .rax (pushDRR0 0 .W64 .rax .rdi acc)
    else
      match wSrc with
      | .W8 => pushDRR0 1 .W8 .rax .rdi acc
      | .W16 => pushDRR0 1 .W16 .rax .rdi acc
      | _ => pushDRR0 0 .W32 .rax .rdi acc
  | _ => emitCanon0 wDst .rax (pushDRR0 0 .W64 .rax .rdi acc)

/-- Emit `sext` (`%rdi` → `%rax`). -/
def emitConvSext0 (wSrc wDst : Width) (acc : List Dir0) : List Dir0 :=
  if widthEq0 wSrc wDst then emitCanon0 wSrc .rax (pushDRR0 0 .W64 .rax .rdi acc)
  else if widthEq0 wDst .W64 then pushDMovsx0 .W64 .rax wSrc .rdi acc
  else emitCanon0 wDst .rax (pushDMovsx0 .W32 .rax wSrc .rdi acc)

/-- Emit `udiv`/`urem`/`sdiv`/`srem` (`%rdi`, `%rsi` → `%rax`). -/
def emitDiv0 (op : DivOp0) (w : Width) (acc : List Dir0) : List Dir0 :=
  let isSigned := match op with | .sdiv | .srem => true | _ => false
  let isRem := match op with | .urem | .srem => true | _ => false
  let divTag : UInt32 := if isSigned then 3 else 2
  match w with
  | .W64 =>
    let acc2 := pushDUnary0 divTag .W64 .rax .rsi (pushDRR0 0 .W64 .rax .rdi acc)
    if isRem then pushDRR0 0 .W64 .rax .rdx acc2 else acc2
  | .W32 =>
    let acc1 := pushDRR0 0 .W32 .r11 .rsi (pushDRR0 0 .W32 .rax .rdi acc)
    let acc2 := pushDUnary0 divTag .W32 .rax .r11 acc1
    if isRem then pushDRR0 0 .W32 .rax .rdx acc2 else acc2
  | _ =>
    let acc1 :=
      if isSigned then pushDMovsx0 .W32 .r11 w .rsi (pushDMovsx0 .W32 .rax w .rdi acc)
      else pushDRR0 1 w .r11 .rsi (pushDRR0 1 w .rax .rdi acc)
    let acc2 := pushDUnary0 divTag .W32 .rax .r11 acc1
    let acc3 := if isRem then pushDRR0 0 .W32 .rax .rdx acc2 else acc2
    emitCanon0 w .rax acc3

/-- Dispatch `OpCode0` instruction selection (`args` in `%rdi`, `%rsi`, `%rdx`; out `%rax`). -/
def emitOp0 (op : OpCode0) (acc : List Dir0) : List Dir0 :=
  match op with
  | .un u t => emitUn0 u t acc
  | .bin .shl t => emitBinShift0 .shl t acc
  | .bin .lshr t => emitBinShift0 .lshr t acc
  | .bin .ashr t => emitBinShift0 .ashr t acc
  | .bin .rotl t => emitBinShift0 .rotl t acc
  | .bin .rotr t => emitBinShift0 .rotr t acc
  | .bin b t => emitBinAlu0 b t acc
  | .cmp co t => emitCmpSelect0 false co t acc
  | .select t => emitCmpSelect0 true .eq t acc
  | .conv .sext m n => emitConvSext0 m n acc
  | .conv c m n => emitConvZextTrunc0 c m n acc
  | .div d w => emitDiv0 d w acc
  | .umulw64 => acc

/-- Emit prologue / epilogue `subq`/`addq` on `%rsp`. -/
@[inline] def emitSpAdj0 (isSub : Bool) (bytes : UInt64) (acc : List Dir0) : List Dir0 :=
  if fitsImm31U0 bytes then
    pushDImm0 (if isSub then 2 else 1) .rsp bytes acc
  else
    pushDUnary0 (if isSub then 4 else 5) .W64 .r10 .r10 (pushDImm0 0 .r10 bytes acc)

/-- Patch epilogue placeholders (`.spAdd false 0`) after final `maxSlots` is computed. -/
def patchEpilogues0 (bytes : UInt64) (xs acc : List Dir0) : List Dir0 :=
  match xs with
  | [] => revDirAux0 acc []
  | d :: rest =>
    match d with
    | .spAdd false 0 => patchEpilogues0 bytes rest (emitSpAdj0 false bytes acc)
    | _ => patchEpilogues0 bytes rest (d :: acc)

/-! ## 6. `Rega0` + `Spill0`: Flat Return Structs (`≤ 5` Args/Fn) & Small Steps -/

/-- Compact slot allocation step result. -/
structure SlotPool0 where
  slot : UInt32
  maxSlots : UInt32
  free : List UInt32
  nxt : UInt32

/-- Compact variable-release step result. -/
structure RelRes0 where
  remUses : Array Nat
  free : List UInt32

/-- Read-only config passed to `loadRegArgs0` (`≤ 5` args). -/
structure LoadCfg0 where
  useRet : Bool
  canon : Bool
  venv : List UInt32
  vslot : Array Nat

/-- Compact 5-field lowering state for linear/value-producing instructions. -/
structure RegaSt0 where
  nextVid : UInt32
  maxSlots : UInt32
  vslot : Array Nat
  remUses : Array Nat
  revDirs : List Dir0

/-- Compact 3-field control/label state passed only where blocks/labels change. -/
structure CtrlSt0 where
  fnIdx : UInt32
  nextLbl : UInt32
  lblSlots : Array (List UInt32)

/-- Flat result of binding one SSA variable slot (`0` nested `Prod` allocations). -/
structure BindOut0 where
  vid : UInt32
  st : RegaSt0
  free : List UInt32
  nxt : UInt32

/-- Flat result of binding a list of variables (`entry` args or `.call` returns). -/
structure BindListOut0 where
  venv : List UInt32
  st : RegaSt0
  free : List UInt32
  nxt : UInt32

/-- Flat result of binding one `.group` block's parameters. -/
structure BlockBind0 where
  venv : List UInt32
  slots : List UInt32
  st : RegaSt0
  free : List UInt32
  nxt : UInt32

/-- Per-block / continuation task on `Rega0`'s worklist. -/
structure RegaTask0 where
  lblId : UInt32
  node : TFlat0
  venv : List UInt32
  lenv : List UInt32
  freeSlots : List UInt32
  nextSlot : UInt32

/-- Staged group block entry awaiting finalized `(lenv', freeSlots, nextSlot)`. -/
structure GroupMeta0 where
  lbl : UInt32
  body : TFlat0
  venv : List UInt32

/-- Flat accumulator for `regaPrepGroup0` (`0` nested `Prod`/`BlockBind0`). -/
structure GroupPrepOut0 where
  lenv : List UInt32
  st : RegaSt0
  ctrl : CtrlSt0
  free : List UInt32
  nxt : UInt32
  metas : List GroupMeta0

/-- Combined loop state returned by control helpers (`st` + `ctrl` + updated `work`). -/
structure LoopStep0 where
  st : RegaSt0
  ctrl : CtrlSt0
  work : List RegaTask0

/-- Prepared `.jnz` state + `lblT` + `free` returned by `jnzBuildSt0`. -/
structure JnzRes0 where
  st : RegaSt0
  ctrl : CtrlSt0
  lblT : UInt32
  free : List UInt32

/-- Pop a free stack slot if available, otherwise bump `nxt`. -/
def allocSlot0 (free : List UInt32) (nxt maxSl : UInt32) : SlotPool0 :=
  match free with
  | s :: rest => SlotPool0.mk s (u32Max0 maxSl (s + 1)) rest nxt
  | [] => SlotPool0.mk nxt (u32Max0 maxSl (nxt + 1)) [] (nxt + 1)

/-- Release one operand use; return its slot to `free` if non-escaped and `remUses` hits `0`. -/
def releaseArg0 (esc vslot : Array Nat) (venv : List UInt32) (res : RelRes0)
    (a : Arg0) : RelRes0 :=
  match a with
  | .var idx =>
    let vid := listGetU32 venv idx
    if arrGetU0 esc vid = 0 then
      let rem := arrGetU0 res.remUses vid
      if decide (rem ≤ 1) then
        RelRes0.mk (arrSetU0 res.remUses vid 0) (arrGetU0 vslot vid :: res.free)
      else
        RelRes0.mk (arrSetU0 res.remUses vid (rem - 1)) res.free
    else res
  | _ => res

/-- Release all operand uses in `args`. -/
def releaseArgs0 (esc vslot : Array Nat) (venv : List UInt32) (res : RelRes0)
    (args : List Arg0) : RelRes0 :=
  match args with
  | [] => res
  | a :: rest => releaseArgs0 esc vslot venv (releaseArg0 esc vslot venv res a) rest

/-- Load arguments into SysV arg/ret registers (`cfg` borrowed read-only, `5` args). -/
def loadRegArgs0 (cfg : LoadCfg0) (ts : List Ty0) (args : List Arg0) (i : UInt32)
    (acc : List Dir0) : List Dir0 :=
  match args with
  | [] => acc
  | a :: aRest =>
    let rd := abiRegAt0 cfg.useRet i
    let acc1 := emitLoadArg0 rd a cfg.venv cfg.vslot acc
    match ts with
    | [] => loadRegArgs0 cfg [] aRest (i + 1) acc1
    | t :: tRest =>
      let acc2 := if cfg.canon then emitCanon0 (tyWidth0 t) rd acc1 else acc1
      loadRegArgs0 cfg tRest aRest (i + 1) acc2

/-- Allocate slot + emit `stSlot` if `vid` is live or escaped (`push` to `vslot`). -/
def bindOneSlot0 (esc : Array Nat) (reg : Reg64) (st : RegaSt0)
    (free : List UInt32) (nxt : UInt32) : BindOut0 :=
  let vid := st.nextVid
  let need := decide (0 < arrGetU0 st.remUses vid) || decide (0 < arrGetU0 esc vid)
  if need then
    let sp := allocSlot0 free nxt st.maxSlots
    let st2 : RegaSt0 :=
      { nextVid := vid + 1
        maxSlots := sp.maxSlots
        vslot := st.vslot.push sp.slot.toNat
        remUses := st.remUses
        revDirs := emitSlotMem0 false reg sp.slot st.revDirs }
    BindOut0.mk vid st2 sp.free sp.nxt
  else
    let st2 : RegaSt0 := { st with nextVid := vid + 1, vslot := st.vslot.push 0 }
    BindOut0.mk vid st2 free nxt

/-- Store and bind one ABI entry parameter at slot `i` (`3` args). -/
def bindOneEntryArg0 (i : UInt32) (t : Ty0) (st : RegaSt0) : RegaSt0 :=
  let reg := abiRegAt0 false i
  let d1 := emitCanon0 (tyWidth0 t) reg st.revDirs
  { nextVid := st.nextVid + 1
    maxSlots := u32Max0 st.maxSlots (i + 1)
    vslot := st.vslot.push i.toNat
    remUses := st.remUses
    revDirs := emitSlotMem0 false reg i d1 }

/-- Allocate and store ABI entry parameters into slots `0..k-1` (`4` args). -/
def bindEntryArgs0 (ts : List Ty0) (i : UInt32) (venv : List UInt32)
    (st : RegaSt0) : BindListOut0 :=
  match ts with
  | [] => BindListOut0.mk venv st [] i
  | t :: rest =>
    let vid := st.nextVid
    bindEntryArgs0 rest (i + 1) (vid :: venv) (bindOneEntryArg0 i t st)

/-- Bind `rem` result slots (`abiRegAt0 true idx`) via `BindOut0` (`4` args). -/
def bindRetsN0 (esc : Array Nat) (rem idx : UInt32) (bl : BindListOut0) : BindListOut0 :=
  if h : rem = 0 then bl
  else
    have _ := u32Sub1Lt0 rem h
    let bo := bindOneSlot0 esc (abiRegAt0 true idx) bl.st bl.free bl.nxt
    bindRetsN0 esc (rem - 1) (idx + 1)
      (BindListOut0.mk (bo.vid :: bl.venv) bo.st bo.free bo.nxt)
termination_by rem.toNat

/-- Read `n` newly bound block parameter slots from `vslot` in forward order (`[s0..s_{n-1}]`). -/
def slotsOfVids0 (n : UInt32) (venv : List UInt32) (vslot : Array Nat)
    (acc : List UInt32) : List UInt32 :=
  if h : n = 0 then acc
  else
    have _ := u32Sub1Lt0 n h
    match venv with
    | [] => acc
    | vid :: rest => slotsOfVids0 (n - 1) rest vslot (arrGetU0 vslot vid :: acc)
termination_by n.toNat

/-- Allocate one slot unconditionally for a block parameter (`3` args). -/
def bindOneBlockSlot0 (st : RegaSt0) (free : List UInt32) (nxt : UInt32) : BindOut0 :=
  let vid := st.nextVid
  let sp := allocSlot0 free nxt st.maxSlots
  let st2 : RegaSt0 :=
    { st with nextVid := vid + 1, maxSlots := sp.maxSlots, vslot := st.vslot.push sp.slot.toNat }
  BindOut0.mk vid st2 sp.free sp.nxt

/-- Allocate parameter slots for one `.group` block (`5` args). -/
def bindBlockParams0 (pts : List Ty0) (venv : List UInt32) (st : RegaSt0)
    (free : List UInt32) (nxt : UInt32) : BlockBind0 :=
  match pts with
  | [] => BlockBind0.mk venv [] st free nxt
  | _ :: rest =>
    let bo := bindOneBlockSlot0 st free nxt
    bindBlockParams0 rest (bo.vid :: venv) bo.st bo.free bo.nxt

/-- Stage `.jump` arguments into non-aliasing temporary slots (`5` args, returns `List Dir0`). -/
def jumpStageLoop0 (args : List Arg0) (tmpIdx : UInt32) (venv : List UInt32)
    (vslot : Array Nat) (acc : List Dir0) : List Dir0 :=
  match args with
  | [] => acc
  | a :: rest =>
    let acc1 := emitSlotMem0 false .rax tmpIdx (emitLoadArg0 .rax a venv vslot acc)
    jumpStageLoop0 rest (tmpIdx + 1) venv vslot acc1

/-- Copy staged `.jump` arguments `[tmpBase + i]` into target parameter slots `tgts`. -/
def jumpCopyLoop0 (tgts : List UInt32) (tmpIdx : UInt32) (acc : List Dir0) : List Dir0 :=
  match tgts with
  | [] => acc
  | s :: rest =>
    let acc1 := emitSlotMem0 false .rax s (emitSlotMem0 true .rax tmpIdx acc)
    jumpCopyLoop0 rest (tmpIdx + 1) acc1

/-- Emit single-slot load+store sequence for 1-arg `.jump` (`5` args). -/
def emitJumpOneStore0 (a : Arg0) (s : UInt32) (venv : List UInt32) (vslot : Array Nat)
    (revDirs : List Dir0) : List Dir0 :=
  emitSlotMem0 false .rax s (emitLoadArg0 .rax a venv vslot revDirs)

/-- Compute directive list for single-arg `.jump` body move (`5` args). -/
def emitJumpOneDir0 (tgts : List UInt32) (a : Arg0) (venv : List UInt32)
    (vslot : Array Nat) (revDirs : List Dir0) : List Dir0 :=
  match tgts with
  | [s] => emitJumpOneStore0 a s venv vslot revDirs
  | _ => revDirs

/-- Emit single-argument `.jump` move + `.jmp` (`5` args). -/
def emitJumpOne0 (lbl : UInt32) (a : Arg0) (task : RegaTask0) (st : RegaSt0)
    (ctrl : CtrlSt0) : RegaSt0 :=
  let tgts := arrGetLL0 ctrl.lblSlots lbl
  let rev := emitJumpOneDir0 tgts a task.venv st.vslot st.revDirs
  { st with revDirs := .jmp (.loc ctrl.fnIdx lbl) :: rev }

/-- Emit staged multi-arg parallel `.jump` moves + `.jmp` (`5` args). -/
def emitJumpMulti0 (lbl : UInt32) (task : RegaTask0) (st : RegaSt0) (ctrl : CtrlSt0)
    (args : List Arg0) : RegaSt0 :=
  let tgts := arrGetLL0 ctrl.lblSlots lbl
  let tmpBase := task.nextSlot
  let nArgs := argLenU0 args 0
  let d1 := jumpStageLoop0 args tmpBase task.venv st.vslot st.revDirs
  let d2 := jumpCopyLoop0 tgts tmpBase d1
  { st with
    maxSlots := u32Max0 st.maxSlots (tmpBase + nArgs)
    revDirs := .jmp (.loc ctrl.fnIdx lbl) :: d2 }

/-- Emit parallel-safe `.jump` argument moves and `.jmp (.loc fnIdx targetLbl)` (`5` args). -/
def emitJump0 (j : UInt32) (args : List Arg0) (task : RegaTask0) (st : RegaSt0)
    (ctrl : CtrlSt0) : RegaSt0 :=
  let lbl := listGetU32 task.lenv j
  match args with
  | [] => { st with revDirs := .jmp (.loc ctrl.fnIdx lbl) :: st.revDirs }
  | [a] => emitJumpOne0 lbl a task st ctrl
  | _ => emitJumpMulti0 lbl task st ctrl args

/-- Push block slots into `CtrlSt0` cleanly without unpacking `GroupPrepOut0` (`4` args). -/
def prepUpdCtrl0 (pts : List Ty0) (venv : List UInt32) (vslot : Array Nat)
    (ctrl : CtrlSt0) : CtrlSt0 :=
  let slots := slotsOfVids0 (tyLenU0 pts 0) venv vslot []
  { ctrl with nextLbl := ctrl.nextLbl + 1, lblSlots := ctrl.lblSlots.push slots }

/-- Run `bindBlockParams0` and `prepUpdCtrl0` for one block (`4` args). -/
def prepOneBind0 (pts : List Ty0) (venv : List UInt32) (st : RegaSt0)
    (out : GroupPrepOut0) : BlockBind0 × CtrlSt0 :=
  let bb := bindBlockParams0 pts venv st out.free out.nxt
  let ctrl1 := prepUpdCtrl0 pts bb.venv bb.st.vslot out.ctrl
  (bb, ctrl1)

/-- Package one `.group` block's bound state into `GroupPrepOut0` (`5` args). -/
def prepFinishBlock0 (lbl : UInt32) (b : TFlat0) (bc : BlockBind0 × CtrlSt0)
    (lenv : List UInt32) (metas : List GroupMeta0) : GroupPrepOut0 :=
  let bb := bc.1
  GroupPrepOut0.mk (lbl :: lenv) bb.st bc.2 bb.free bb.nxt
    (GroupMeta0.mk lbl b bb.venv :: metas)

/-- Prepare one `.group` block: bind block slots then build updated `GroupPrepOut0` (`3` args). -/
def prepOneBlock0 (entry : List Ty0 × TFlat0) (venv : List UInt32)
    (out : GroupPrepOut0) : GroupPrepOut0 :=
  let (pts, b) := entry
  let lbl := out.ctrl.nextLbl
  let lenv := out.lenv
  let metas := out.metas
  let bc := prepOneBind0 pts venv out.st out
  prepFinishBlock0 lbl b bc lenv metas

/-- Step 1 of `.group` lowering: allocate labels and parameter slots (`3` args). -/
def regaPrepGroup0 (bodies : List (List Ty0 × TFlat0)) (venv : List UInt32)
    (out : GroupPrepOut0) : GroupPrepOut0 :=
  match bodies with
  | [] => out
  | entry :: rest => regaPrepGroup0 rest venv (prepOneBlock0 entry venv out)

/-- Step 2 of `.group`: push block tasks onto `work` with finalized `(lenv', free, nxt)`. -/
def regaEnqueueGroup0 (metas : List GroupMeta0) (lenv' free : List UInt32) (nxt : UInt32)
    (work : List RegaTask0) : List RegaTask0 :=
  match metas with
  | [] => work
  | gm :: rest =>
    let tsk := RegaTask0.mk gm.lbl gm.body gm.venv lenv' free nxt
    regaEnqueueGroup0 rest lenv' free nxt (tsk :: work)

/-- Borrowed instruction emission for `.let2Umulw64` (`0` RC). -/
def emitLinUmulw0 (a b : Arg0) (cur : RegaTask0) (st : RegaSt0) : List Dir0 :=
  let d1 := emitLoadArg0 .rdi a cur.venv st.vslot st.revDirs
  let d2 := emitLoadArg0 .rsi b cur.venv st.vslot d1
  pushDRR0 5 .W64 .rsi .rsi (pushDRR0 0 .W64 .rax .rdi d2)

/-- Borrowed instruction emission for `.store` (`0` RC). -/
def emitLinStore0 (t : Ty0) (val addr : Arg0) (cur : RegaTask0) (st : RegaSt0) : List Dir0 :=
  let d1 := emitLoadArg0 .rdi val cur.venv st.vslot st.revDirs
  let d2 := emitLoadArg0 .rsi addr cur.venv st.vslot d1
  pushDRR0 3 (tyWidth0 t) .rsi .rdi d2

/-- Borrowed instruction emission for `.load`, `.store`, `.let2Umulw64` (`0` RC). -/
def emitLinMem0 (cur : RegaTask0) (st : RegaSt0) : List Dir0 :=
  match cur.node with
  | .let2Umulw64 a b _ => emitLinUmulw0 a b cur st
  | .load t addr _ =>
    pushDRR0 2 (tyWidth0 t) .rax .rdi (emitLoadArg0 .rdi addr cur.venv st.vslot st.revDirs)
  | .store t val addr _ => emitLinStore0 t val addr cur st
  | _ => st.revDirs

/-- Borrowed emission for `.let1`/`.call` (delegates memory ops to `emitLinMem0`). -/
def emitLinNode0 (cur : RegaTask0) (st : RegaSt0) : List Dir0 :=
  match cur.node with
  | .let1 op args _ =>
    let cfg := LoadCfg0.mk false false cur.venv st.vslot
    emitOp0 op (loadRegArgs0 cfg [] args 0 st.revDirs)
  | .call fnSym as _ args _ =>
    let cfg := LoadCfg0.mk false true cur.venv st.vslot
    .callSym fnSym :: loadRegArgs0 cfg as args 0 st.revDirs
  | _ => emitLinMem0 cur st

/-- Release operand uses for `.let1`, `.let2Umulw64`, `.load`, `.store`, `.call` (`5` args). -/
def relNodeArgs0 (esc vslot : Array Nat) (venv : List UInt32) (node : TFlat0)
    (res : RelRes0) : RelRes0 :=
  match node with
  | .let1 _ args _ => releaseArgs0 esc vslot venv res args
  | .let2Umulw64 a b _ =>
    releaseArg0 esc vslot venv (releaseArg0 esc vslot venv res a) b
  | .load _ addr _ => releaseArg0 esc vslot venv res addr
  | .store _ val addr _ =>
    releaseArg0 esc vslot venv (releaseArg0 esc vslot venv res val) addr
  | .call _ _ _ args _ => releaseArgs0 esc vslot venv res args
  | _ => res

/-- Release `cur`'s operands, update `st`, and package `BindListOut0` (`4` args). -/
def relAndUpdateSt0 (esc : Array Nat) (cur : RegaTask0) (st : RegaSt0)
    (dOut : List Dir0) : BindListOut0 :=
  let rr := relNodeArgs0 esc st.vslot cur.venv cur.node (RelRes0.mk st.remUses cur.freeSlots)
  let st1 : RegaSt0 := { st with remUses := rr.remUses, revDirs := dOut }
  BindListOut0.mk cur.venv st1 rr.free cur.nextSlot

/-- Package straight-line `BindListOut0` into next task + `LoopStep0` (`4` args). -/
def linBindPush0 (cur : RegaTask0) (bl : BindListOut0) (ctrl : CtrlSt0)
    (work : List RegaTask0) : LoopStep0 :=
  LoopStep0.mk bl.st ctrl
    (RegaTask0.mk 0 (linK0 cur.node) bl.venv cur.lenv bl.free bl.nxt :: work)

/-- Bind straight-line results (`bindRetsN0`) and push continuation `linK0` (`5` args). -/
def stepLinBindPush0 (esc : Array Nat) (cur : RegaTask0) (bl0 : BindListOut0)
    (ctrl : CtrlSt0) (work : List RegaTask0) : LoopStep0 :=
  let bl := bindRetsN0 esc (linCnt0 cur.node) 0 bl0
  linBindPush0 cur bl ctrl work

/-- Lower any straight-line node using shared `linCnt0`/`linK0` (`5` args). -/
def stepLinear0 (esc : Array Nat) (cur : RegaTask0) (st : RegaSt0) (ctrl : CtrlSt0)
    (work : List RegaTask0) : LoopStep0 :=
  let dOut := emitLinNode0 cur st
  let bl0 := relAndUpdateSt0 esc cur st dOut
  stepLinBindPush0 esc cur bl0 ctrl work

/-- Prepare `.jnz` test, `.jcc`, and condition release without building `RegaSt0` (`5` args). -/
def jnzPrep0 (esc : Array Nat) (c : Arg0) (cur : RegaTask0) (st : RegaSt0)
    (ctrl : CtrlSt0) : RelRes0 × List Dir0 :=
  let d1 := pushDRR0 4 .W8 .rax .rax (emitLoadArg0 .rax c cur.venv st.vslot st.revDirs)
  let d2 := .jcc .nz (.loc ctrl.fnIdx ctrl.nextLbl) :: d1
  let r1 := releaseArg0 esc st.vslot cur.venv (RelRes0.mk st.remUses cur.freeSlots) c
  (r1, d2)

/-- Wrap `jnzPrep0` results into `JnzRes0` with updated `st` and `ctrl` (`3` args). -/
def jnzWrapRes0 (rd : RelRes0 × List Dir0) (st : RegaSt0) (ctrl : CtrlSt0) : JnzRes0 :=
  let lblT := ctrl.nextLbl
  let st2 : RegaSt0 := { st with remUses := rd.1.remUses, revDirs := rd.2 }
  let ctrl2 : CtrlSt0 := { ctrl with nextLbl := lblT + 1 }
  JnzRes0.mk st2 ctrl2 lblT rd.1.free

/-- Build `JnzRes0` updating `st` and `ctrl` for `.jnz` (`5` args). -/
def jnzBuildSt0 (esc : Array Nat) (c : Arg0) (cur : RegaTask0) (st : RegaSt0)
    (ctrl : CtrlSt0) : JnzRes0 :=
  jnzWrapRes0 (jnzPrep0 esc c cur st ctrl) st ctrl

/-- Enqueue `[eTask, tTask]` onto `rest` (`5` args, `0` `{ with }` updates). -/
def stepJnzPush0 (t e : TFlat0) (cur : RegaTask0) (jr : JnzRes0)
    (rest : List RegaTask0) : LoopStep0 :=
  let tTask := RegaTask0.mk jr.lblT t cur.venv cur.lenv jr.free cur.nextSlot
  let eTask := RegaTask0.mk 0 e cur.venv cur.lenv jr.free cur.nextSlot
  LoopStep0.mk jr.st jr.ctrl (eTask :: tTask :: rest)

/-- Enqueue `.group` body tasks followed by continuation `k` (`4` args). -/
def groupEnqCont0 (k : TFlat0) (venv : List UInt32) (gp : GroupPrepOut0)
    (rest : List RegaTask0) : List RegaTask0 :=
  let work2 := regaEnqueueGroup0 gp.metas gp.lenv gp.free gp.nxt rest
  RegaTask0.mk 0 k venv gp.lenv gp.free gp.nxt :: work2

/-- Enqueue `.group` body tasks and continuation `k` (`4` args, `0` `TFlat0` match). -/
def stepGroupFinish0 (k : TFlat0) (cur : RegaTask0) (gp : GroupPrepOut0)
    (rest : List RegaTask0) : LoopStep0 :=
  LoopStep0.mk gp.st gp.ctrl (groupEnqCont0 k cur.venv gp rest)

/-- Lower `.tailCall` and `.exit` terminators (`5` args, `0` `TFlat0` match). -/
def stepTail0 (fnSym : Sym0) (as : List Ty0) (args : List Arg0) (cur : RegaTask0)
    (st : RegaSt0) : RegaSt0 :=
  let cfg := LoadCfg0.mk false true cur.venv st.vslot
  let d1 := loadRegArgs0 cfg as args 0 st.revDirs
  { st with revDirs := .jmp (.sym fnSym) :: pushDImm0 1 .rsp 0 d1 }

/-- Lower `.ret` terminator (`3` args, `0` `TFlat0` match). -/
def stepRet0 (vs : List Arg0) (cur : RegaTask0) (st : RegaSt0) : RegaSt0 :=
  let cfg := LoadCfg0.mk true false cur.venv st.vslot
  let d1 := loadRegArgs0 cfg [] vs 0 st.revDirs
  { st with revDirs := .ret :: pushDImm0 1 .rsp 0 d1 }

/-- Dispatcher for `.jump`, `.hlt`, `.tailCall`, `.exit`, `.ret` (`4` args). -/
def regaStepCtrl0 (cur : RegaTask0) (st : RegaSt0) (ctrl : CtrlSt0)
    (rest : List RegaTask0) : LoopStep0 :=
  match cur.node with
  | .jump j args => LoopStep0.mk (emitJump0 j args cur st ctrl) ctrl rest
  | .tailCall fnSym as args => LoopStep0.mk (stepTail0 fnSym as args cur st) ctrl rest
  | .exit fnSym as args => LoopStep0.mk (stepTail0 fnSym as args cur st) ctrl rest
  | .ret vs => LoopStep0.mk (stepRet0 vs cur st) ctrl rest
  | _ => LoopStep0.mk st ctrl rest

/-- Prepend block label directive when entering a non-zero `lblId` block (`3` args). -/
def regaPrependLbl0 (cur : RegaTask0) (st : RegaSt0) (ctrl : CtrlSt0) : RegaSt0 :=
  if cur.lblId = 0 then st
  else { st with revDirs := .label (.loc ctrl.fnIdx cur.lblId) :: st.revDirs }

/-- Initialize and run `regaPrepGroup0` for `.group` blocks (`4` args). -/
def stepGroupPrep0 (bodies : List (List Ty0 × TFlat0)) (cur : RegaTask0) (st : RegaSt0)
    (ctrl : CtrlSt0) : GroupPrepOut0 :=
  let gp0 := GroupPrepOut0.mk cur.lenv st ctrl cur.freeSlots cur.nextSlot []
  regaPrepGroup0 bodies cur.venv gp0

/-- Single-step dispatcher for `regaWorkLoop0` (`5` args, `<= 4` top arms). -/
def regaStep0 (esc : Array Nat) (cur : RegaTask0) (st : RegaSt0) (ctrl : CtrlSt0)
    (rest : List RegaTask0) : LoopStep0 :=
  match cur.node with
  | .jnz c t e => stepJnzPush0 t e cur (jnzBuildSt0 esc c cur st ctrl) rest
  | .group bodies k => stepGroupFinish0 k cur (stepGroupPrep0 bodies cur st ctrl) rest
  | .let1 _ _ _ | .let2Umulw64 _ _ _ | .load _ _ _ | .store _ _ _ _ | .call _ _ _ _ _ =>
    stepLinear0 esc cur st ctrl rest
  | _ => regaStepCtrl0 cur st ctrl rest

/-- Iterative `UInt32`-bounded worklist lowering loop for one function body (`Rega0` + `Spill0`). -/
def regaWorkLoop0 (fuel : UInt32) (esc : Array Nat) (st : RegaSt0) (ctrl : CtrlSt0)
    (work : List RegaTask0) : RegaSt0 :=
  if h : fuel = 0 then st
  else
    have _ := u32Sub1Lt0 fuel h
    match work with
    | [] => st
    | cur :: rest =>
      let st0 := regaPrependLbl0 cur st ctrl
      let ls := regaStep0 esc cur st0 ctrl rest
      regaWorkLoop0 (fuel - 1) esc ls.st ls.ctrl ls.work
termination_by fuel.toNat

/-- Run `PrePass0` for one function returning `PreSt0`. -/
def compileFnPre0 (fn : TFlatFn0) : PreSt0 :=
  let (preVenv, pre1) := preInit0 fn.as
  preWorkLoop0 0x7fffffff 1 pre1 [PreItem0.mk fn.body preVenv 0]

/-- Run `regaWorkLoop0`, emit prologue, patch epilogues, and finalize directives (`5` args). -/
def compileFnFinish0 (fn : TFlatFn0) (esc : Array Nat) (bl : BindListOut0)
    (ctrl0 : CtrlSt0) : List Dir0 × UInt32 :=
  let initTask := RegaTask0.mk 0 fn.body bl.venv [] bl.free bl.nxt
  let regaOut := regaWorkLoop0 0x7fffffff esc bl.st ctrl0 [initTask]
  let fSz := x64FrameSizeU0 regaOut.maxSlots
  let headRev := emitSpAdj0 true fSz [.label (.sym fn.name)]
  let bodyFwd := patchEpilogues0 fSz (revDirAux0 regaOut.revDirs []) []
  (revDirAux0 headRev bodyFwd, regaOut.maxSlots)

/-- Compile one `TFlatFn0` to `Dir0` directives + its peak slot count. -/
def compileFn0 (fnIdx : UInt32) (fn : TFlatFn0) : List Dir0 × UInt32 :=
  let preRes := compileFnPre0 fn
  let cap := Nat.add 32 (tyLenU0 fn.as 0).toNat
  let lblArr0 : Array (List UInt32) := (Array.emptyWithCapacity cap).push []
  let rega0 := RegaSt0.mk 0 0 (Array.emptyWithCapacity cap) preRes.uses []
  let ctrl0 := CtrlSt0.mk fnIdx 1 lblArr0
  let bl := bindEntryArgs0 fn.as 0 [] rega0
  compileFnFinish0 fn preRes.escaped bl ctrl0

/-! ## 7. Module Driver -/

/-- Compile all functions in `fns` sequentially, accumulating directives and max slot count. -/
def compileModuleLoop0 (fns : List TFlatFn0) (idx maxSl : UInt32)
    (revAcc : List Dir0) : List Dir0 × UInt32 :=
  match fns with
  | [] => (revDirAux0 revAcc [], maxSl)
  | fn :: rest =>
    let (dirs, msl) := compileFn0 idx fn
    compileModuleLoop0 rest (idx + 1) (u32Max0 maxSl msl) (revDirAux0 dirs revAcc)

/-- Validate whole module `mod` (`0` = ok, otherwise packed `(code << 32) | fnIdx`). -/
def legalMod0 (mod : TFlatModule0) : UInt64 :=
  if allValidExts0 mod.externs then
    let sigs := prepSigsFns0 mod.fns (prepSigsExts0 mod.externs [])
    legalFnsLoop0 mod.exits sigs mod.fns 0
  else UInt64.shiftLeft 2 32

/-- General Stage-A (`leanqbe0`) compiler entry point (`TFlatModule0 → CompileRes0`). -/
def leanqbe0Compile (mod : TFlatModule0) : CompileRes0 :=
  let res := legalMod0 mod
  if res = 0 then
    let (dirs, maxSl) := compileModuleLoop0 mod.fns 0 0 []
    .ok dirs maxSl
  else
    let ec := UInt64.toUInt32 (UInt64.shiftRight res 32)
    let badFn := UInt64.toUInt32 (UInt64.land res 0xffffffff)
    .err ec badFn

lcnf_of_lean! leanqbe0LcMod [leanqbe0Compile]

end LeanQbe.T.Bootstrap0
