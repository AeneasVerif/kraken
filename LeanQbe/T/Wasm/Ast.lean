module

public import LeanQbe.T.IL

/-!
# WebAssembly 1.0/2.0 Core Integer AST (`LeanQbe.T.Wasm.Ast`)

Defines the target-independent core integer WebAssembly syntax for verified sandbox lowering:
* Value and signature types (`WValTy`, `WFuncTy`, `WBlockTy`), supporting `i32`/`i64` scalars and
  multi-value block/function signatures.
* Core integer operations: unary (`eqz`, `clz`, `ctz`, `popcnt`, `extend{8,16,32}_s`), binary
  (`add`, `sub`, `mul`, `div_{u,s}`, `rem_{u,s}`, `and`, `or`, `xor`, `shl`, `shr_{u,s}`,
  `rot{l,r}`), relational (`eq`, `ne`, `{lt,gt,le,ge}_{s,u}`), conversions (`wrap_i64`,
  `extend_i32_{s,u}`), and parametric (`drop`, `select`).
* Locals, immutable globals, linear memory (`{i32,i64}.{load,store}*` with static `offset`),
  `memory.size`/`memory.grow`, structured control (`block`, `loop`, `if_`, `br`, `br_if`,
  `br_table`, `return_`, `unreachable`, `nop`), and direct function `call`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Wasm

/-- Core integer WebAssembly scalar value type (`i32` or `i64`). -/
inductive WValTy where
  | i32
  | i64
  deriving DecidableEq, Repr, Inhabited

/-- Lower a WebAssembly value type to its `LeanQbe.T.Ty` representation. -/
@[reducible] def WValTy.toTy : WValTy → Ty
  | .i32 => T.i32
  | .i64 => T.i64

/-- Bit width of a `WValTy` (`32` or `64`). -/
@[reducible] def WValTy.bitWidth : WValTy → Nat
  | .i32 => 32
  | .i64 => 64

/-- Default zero `Val t.toTy` for trap/error padding returns. -/
def WValTy.zeroVal : (t : WValTy) → Val t.toTy
  | .i32 => 0#32
  | .i64 => 0#64

/-- Default zero `Arg V t.toTy` for trap/error padding returns. -/
def WValTy.zeroArg {V : Ty → Type} : (t : WValTy) → Arg V t.toTy
  | .i32 => .imm 0#32
  | .i64 => .imm 0#64

/-- WebAssembly function signature (`params -> results`). -/
structure WFuncTy where
  params : List WValTy := []
  results : List WValTy := []
  deriving DecidableEq, Repr, Inhabited

/-- Structured block type annotation (Wasm 1.0 empty/single value or Wasm 2.0 type index /
inline multi-value signature). -/
inductive WBlockTy where
  | empty
  | val (t : WValTy)
  | func (typeIdx : Nat)
  | inline (ft : WFuncTy)
  deriving DecidableEq, Repr, Inhabited

/-- Resolve a `WBlockTy` against a module's type section `types`. -/
def WBlockTy.resolve (types : List WFuncTy) : WBlockTy → Option WFuncTy
  | .empty => some ⟨[], []⟩
  | .val t => some ⟨[], [t]⟩
  | .func idx => types[idx]?
  | .inline ft => some ft

/-- Linear memory access width (`1`, `2`, `4`, or `8` bytes). -/
inductive WMemWidth where
  | w8
  | w16
  | w32
  | w64
  deriving DecidableEq, Repr, Inhabited

/-- Access byte count of `WMemWidth`. -/
@[reducible] def WMemWidth.bytes : WMemWidth → Nat
  | .w8 => 1
  | .w16 => 2
  | .w32 => 4
  | .w64 => 8

/-- Access bit width of `WMemWidth`. -/
@[reducible] def WMemWidth.bits : WMemWidth → Nat
  | .w8 => 8
  | .w16 => 16
  | .w32 => 32
  | .w64 => 64

/-- `LeanQbe.T.Ty` corresponding to `WMemWidth`. -/
@[reducible] def WMemWidth.memTy : WMemWidth → Ty
  | .w8 => T.i8
  | .w16 => T.i16
  | .w32 => T.i32
  | .w64 => T.i64

/-- Static WebAssembly memory immediate (`offset` added unsigned in 64-bit effective address, plus
alignment hint `align`). -/
structure WMemArg where
  offset : UInt32 := 0
  align : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- Core integer unary operators (`eqz` has separate fixed `i32` output type). -/
inductive WUnOp where
  | clz
  | ctz
  | popcnt
  | extend8_s
  | extend16_s
  | extend32_s
  deriving DecidableEq, Repr, Inhabited

/-- Core integer binary arithmetic, division/remainder, bitwise, shift, and rotate operators. -/
inductive WBinOp where
  | add
  | sub
  | mul
  | div_u
  | div_s
  | rem_u
  | rem_s
  | and
  | or
  | xor
  | shl
  | shr_u
  | shr_s
  | rotl
  | rotr
  deriving DecidableEq, Repr, Inhabited

/-- Core integer relational operators (`[w, w] -> [i32]`). -/
inductive WRelOp where
  | eq
  | ne
  | lt_s
  | lt_u
  | gt_s
  | gt_u
  | le_s
  | le_u
  | ge_s
  | ge_u
  deriving DecidableEq, Repr, Inhabited

/-- Core integer WebAssembly 1.0/2.0 instruction AST with structured control trees. -/
inductive WInstr where
  | unreachable
  | nop
  | block (bt : WBlockTy) (body : List WInstr)
  | loop (bt : WBlockTy) (body : List WInstr)
  | if_ (bt : WBlockTy) (thenBody : List WInstr) (elseBody : List WInstr)
  | br (depth : Nat)
  | br_if (depth : Nat)
  | br_table (targets : List Nat) (defaultTarget : Nat)
  | return_
  | call (fnIdx : Nat)
  | drop
  | select
  | local_get (idx : Nat)
  | local_set (idx : Nat)
  | local_tee (idx : Nat)
  | global_get (idx : Nat)
  | load (resTy : WValTy) (width : WMemWidth) (signed : Bool) (arg : WMemArg)
  | store (srcTy : WValTy) (width : WMemWidth) (arg : WMemArg)
  | memory_size
  | memory_grow
  | memory_copy
  | memory_fill
  | i32_const (v : BitVec 32)
  | i64_const (v : BitVec 64)
  | eqz (w : WValTy)
  | unop (w : WValTy) (op : WUnOp)
  | binop (w : WValTy) (op : WBinOp)
  | relop (w : WValTy) (op : WRelOp)
  | wrap_i64
  | extend_i32_s
  | extend_i32_u
  deriving Inhabited

/-- Immutable global variable declaration. -/
structure WGlobalDecl where
  ty : WValTy
  mut_ : Bool := false
  init : BitVec 64 := 0#64
  deriving DecidableEq, Repr, Inhabited

/-- Linear memory section metadata. -/
structure WMemSpec where
  initPages : Nat := 1
  maxPages : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

/-- Effective page cap for `memory.grow`, clamped to the Wasm32 65536-page (4 GiB) limit. -/
@[reducible] def WMemSpec.effectiveMaxPages (spec : WMemSpec) : Nat :=
  Nat.min (spec.maxPages.getD 65536) 65536

/-- Effective byte cap (`effectiveMaxPages * 65536`) as a 64-bit value (`≤ 2^32`). -/
@[reducible] def WMemSpec.maxBytes (spec : WMemSpec) : BitVec 64 :=
  BitVec.ofNat 64 (spec.effectiveMaxPages * 65536)

/-- Core WebAssembly function definition. -/
structure WFunc where
  name : Sym
  typeIdx : Nat
  locals : List WValTy := []
  body : List WInstr := []
  deriving Inhabited

/-- Core WebAssembly module (`types`, `funcs`, optional `memory`, immutable `globals`). -/
structure WModule where
  types : List WFuncTy := []
  funcs : List WFunc := []
  memory : Option WMemSpec := some {}
  globals : List WGlobalDecl := []
  deriving Inhabited

namespace WInstr

/-- Shorthand constructors for readable WebAssembly guest kernels. -/
abbrev i32_load (off : UInt32 := 0) : WInstr := .load .i32 .w32 false { offset := off }
abbrev i32_load8_u (off : UInt32 := 0) : WInstr := .load .i32 .w8 false { offset := off }
abbrev i32_load8_s (off : UInt32 := 0) : WInstr := .load .i32 .w8 true { offset := off }
abbrev i32_load16_u (off : UInt32 := 0) : WInstr := .load .i32 .w16 false { offset := off }
abbrev i32_load16_s (off : UInt32 := 0) : WInstr := .load .i32 .w16 true { offset := off }
abbrev i64_load (off : UInt32 := 0) : WInstr := .load .i64 .w64 false { offset := off }
abbrev i64_load32_u (off : UInt32 := 0) : WInstr := .load .i64 .w32 false { offset := off }
abbrev i64_load32_s (off : UInt32 := 0) : WInstr := .load .i64 .w32 true { offset := off }
abbrev i32_store (off : UInt32 := 0) : WInstr := .store .i32 .w32 { offset := off }
abbrev i32_store8 (off : UInt32 := 0) : WInstr := .store .i32 .w8 { offset := off }
abbrev i32_store16 (off : UInt32 := 0) : WInstr := .store .i32 .w16 { offset := off }
abbrev i64_store (off : UInt32 := 0) : WInstr := .store .i64 .w64 { offset := off }
abbrev i64_store32 (off : UInt32 := 0) : WInstr := .store .i64 .w32 { offset := off }
abbrev i32_eqz : WInstr := .eqz .i32
abbrev i64_eqz : WInstr := .eqz .i64
abbrev i32_add : WInstr := .binop .i32 .add
abbrev i32_sub : WInstr := .binop .i32 .sub
abbrev i32_mul : WInstr := .binop .i32 .mul
abbrev i32_div_u : WInstr := .binop .i32 .div_u
abbrev i32_div_s : WInstr := .binop .i32 .div_s
abbrev i32_rem_u : WInstr := .binop .i32 .rem_u
abbrev i32_rem_s : WInstr := .binop .i32 .rem_s
abbrev i32_and : WInstr := .binop .i32 .and
abbrev i32_or : WInstr := .binop .i32 .or
abbrev i32_xor : WInstr := .binop .i32 .xor
abbrev i32_shl : WInstr := .binop .i32 .shl
abbrev i32_shr_u : WInstr := .binop .i32 .shr_u
abbrev i32_shr_s : WInstr := .binop .i32 .shr_s
abbrev i32_rotl : WInstr := .binop .i32 .rotl
abbrev i32_rotr : WInstr := .binop .i32 .rotr
abbrev i32_eq : WInstr := .relop .i32 .eq
abbrev i32_ne : WInstr := .relop .i32 .ne
abbrev i32_lt_s : WInstr := .relop .i32 .lt_s
abbrev i32_lt_u : WInstr := .relop .i32 .lt_u
abbrev i32_gt_s : WInstr := .relop .i32 .gt_s
abbrev i32_gt_u : WInstr := .relop .i32 .gt_u
abbrev i32_le_s : WInstr := .relop .i32 .le_s
abbrev i32_le_u : WInstr := .relop .i32 .le_u
abbrev i32_ge_s : WInstr := .relop .i32 .ge_s
abbrev i32_ge_u : WInstr := .relop .i32 .ge_u
abbrev i64_add : WInstr := .binop .i64 .add
abbrev i64_sub : WInstr := .binop .i64 .sub
abbrev i64_mul : WInstr := .binop .i64 .mul
abbrev i64_and : WInstr := .binop .i64 .and
abbrev i64_or : WInstr := .binop .i64 .or
abbrev i64_xor : WInstr := .binop .i64 .xor
abbrev i64_shl : WInstr := .binop .i64 .shl
abbrev i64_shr_u : WInstr := .binop .i64 .shr_u
abbrev i64_rotl : WInstr := .binop .i64 .rotl
abbrev i64_rotr : WInstr := .binop .i64 .rotr
abbrev i64_eq : WInstr := .relop .i64 .eq
abbrev i64_lt_u : WInstr := .relop .i64 .lt_u
abbrev i64_ge_u : WInstr := .relop .i64 .ge_u

end WInstr

end LeanQbe.T.Wasm
