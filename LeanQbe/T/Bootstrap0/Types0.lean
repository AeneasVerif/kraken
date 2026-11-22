module

public import LeanQbe.T.Ops
public import LeanQbe.T.Amd64.Base

/-!
# Bootstrap Stage A (`leanqbe0`) First-Order Monomorphic IR & Assembly Types

Strictly first-order, closure-free datatypes used by `leanqbe0Compile`:
* `Ty0` / `TFlatModule0` / `TFlatFn0` / `TFlat0` / `OpCode0` / `Arg0`: all-scalar monomorphic de
  Bruijn IR (with `UInt32` symbol/variable/block indices and `Width` tags, avoiding `Nat` slow paths
  and nested type checks inside `Compiler0.lean`).
* `Dir0` / `Label0` / `CompileRes0`: flat x86-64 assembly directive representation avoiding `String`
  labels, `BitVec`, and nested `AddrExpr` heap allocations inside `leanqbe0Compile`'s LCNF.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Bootstrap0

/-- Numeric `UInt32` symbol ID used throughout `leanqbe0` to avoid string/bignum checks in LCNF. -/
abbrev Sym0 := UInt32

/-- Scalar value type tag supported by Stage A (`leanqbe0`). -/
inductive Ty0 where
  | bool
  | b8
  | b16
  | b32
  | b64
  deriving Repr, Inhabited

/-- First-order operand in `TFlat0`. -/
inductive Arg0 where
  | var (idx : UInt32)
  | immBool (b : Bool)
  | immBits (w : Width) (val : UInt64)
  deriving Repr, Inhabited

/-- Unary scalar operations in `OpCode0`. -/
inductive UnOp0 where
  | copy
  | neg
  | not
  deriving Repr, Inhabited

/-- Binary scalar operations in `OpCode0`. -/
inductive BinOp0 where
  | add
  | sub
  | mul
  | and
  | or
  | xor
  | shl
  | lshr
  | ashr
  | rotl
  | rotr
  deriving Repr, Inhabited

/-- Division and remainder operations in `OpCode0`. -/
inductive DivOp0 where
  | udiv
  | urem
  | sdiv
  | srem
  deriving Repr, Inhabited

/-- Width conversion and boolean materialization operations in `OpCode0`. -/
inductive ConvOp0 where
  | ofBool
  | zext
  | sext
  | trunc
  deriving Repr, Inhabited

/-- First-order scalar opcode subset covering `LeanLCNF` and `self.tflat`. -/
inductive OpCode0 where
  | un (op : UnOp0) (t : Ty0)
  | bin (op : BinOp0) (t : Ty0)
  | cmp (co : CmpOp) (t : Ty0)
  | select (t : Ty0)
  | conv (op : ConvOp0) (wSrc wDst : Width)
  | div (op : DivOp0) (w : Width)
  | umulw64
  deriving Repr, Inhabited

/-- First-order monomorphic de Bruijn flat IR (with `.tailCall`). -/
inductive TFlat0 where
  | let1 (op : OpCode0) (args : List Arg0) (k : TFlat0)
  | let2Umulw64 (a b : Arg0) (k : TFlat0)
  | load (t : Ty0) (addr : Arg0) (k : TFlat0)
  | store (t : Ty0) (val addr : Arg0) (k : TFlat0)
  | call (fnSym : Sym0) (as bs : List Ty0) (args : List Arg0) (k : TFlat0)
  | tailCall (fnSym : Sym0) (as : List Ty0) (args : List Arg0)
  | jnz (c : Arg0) (t e : TFlat0)
  | jump (j : UInt32) (args : List Arg0)
  | ret (vs : List Arg0)
  | exit (fnSym : Sym0) (as : List Ty0) (args : List Arg0)
  | hlt
  | group (bodies : List (List Ty0 × TFlat0)) (k : TFlat0)
  deriving Repr, Inhabited

/-- Function definition in `TFlatModule0`. -/
structure TFlatFn0 where
  name : Sym0
  as : List Ty0
  rs : List Ty0
  body : TFlat0
  deriving Repr, Inhabited

/-- External callee signature in `TFlatModule0`. -/
structure ExtSig0 where
  name : Sym0
  as : List Ty0
  rs : List Ty0
  deriving Repr, Inhabited

/-- Whole-module compilation input for `leanqbe0Compile`. -/
structure TFlatModule0 where
  fns : List TFlatFn0
  externs : List ExtSig0
  exits : List Sym0
  deriving Repr, Inhabited

/-- Structured label reference avoiding string concatenation inside `leanqbe0Compile`. -/
inductive Label0 where
  | sym (id : Sym0)
  | loc (fnId lblId : UInt32)
  deriving Repr, Inhabited

/-- Two-address binary ALU operation kinds in `Dir0`. -/
inductive AluKind0 where
  | add
  | sub
  | mul
  | and
  | or
  | xor
  deriving Repr, Inhabited

/-- Shift and rotate operation kinds in `Dir0`. -/
inductive ShiftKind0 where
  | shl
  | lshr
  | ashr
  | rotl
  | rotr
  deriving Repr, Inhabited

/-- Flat x86-64 directive representation emitted by `leanqbe0Compile`. -/
inductive Dir0 where
  | label (l : Label0)
  | movRR (w : Width) (rd rs : Reg64)
  | movRI (rd : Reg64) (imm : UInt64)
  | movzx32 (wSrc : Width) (rd rs : Reg64)
  | movsx (wDst : Width) (rd : Reg64) (wSrc : Width) (rs : Reg64)
  | ldMem (w : Width) (rd base : Reg64)
  | stMem (w : Width) (base val : Reg64)
  | ldSlot (rd : Reg64) (disp : UInt64)
  | stSlot (disp : UInt64) (rs : Reg64)
  | ldSlotIdx (rd idx : Reg64)
  | stSlotIdx (idx rs : Reg64)
  | spAdd (isSub : Bool) (imm32 : UInt64)
  | spAddReg (isSub : Bool) (r : Reg64)
  | aluRR (w : Width) (k : AluKind0) (rd rs : Reg64)
  | unary (w : Width) (isNeg : Bool) (rd : Reg64)
  | shiftCl (w : Width) (k : ShiftKind0) (rd : Reg64)
  | shMaskCl (imm : UInt64)
  | cmpRR (w : Width) (ra rb : Reg64)
  | testbRR (ra rb : Reg64)
  | setcc (cc : CondCode) (rd : Reg64)
  | cmovcc (w : Width) (cc : CondCode) (rd rs : Reg64)
  | divCore (w : Width) (isSigned : Bool) (rhs : Reg64)
  | mulq (rhs : Reg64)
  | jmp (l : Label0)
  | jcc (cc : CondCode) (l : Label0)
  | callSym (sym : Sym0)
  | ret
  deriving Repr, Inhabited

/-- Compilation outcome returned by `leanqbe0Compile`. -/
inductive CompileRes0 where
  | ok (dirs : List Dir0) (maxSlots : UInt32)
  | err (code : UInt32) (fnIdx : UInt32)
  deriving Repr, Inhabited

end LeanQbe.T.Bootstrap0
