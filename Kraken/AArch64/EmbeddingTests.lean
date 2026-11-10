module

/-
  Embedding Tests: standalone embeddings of the elements of an AArch64 program
  (`⸨instr|`, `⸨mem|`, `⸨reg|`, `⸨const|`, `⸨cc|`).
-/

import Kraken.AArch64.Parser

section Tests
open Kraken hiding Directive Label
open AArch64.Parser

-- Test: instructions
/--
info: { operation_size := RegWidth.W64,
  operation :=
    Operation.ADD_e (↑↑XReg.X0 RegWidth.W64) (↑↑XReg.X1 RegWidth.W64) ↑{ imm := ↑1, shift := ImmShift.S0 } } : Instr
-/
#guard_msgs in
#check ⸨instr| add x0, x1, #1 ⸩

/--
info: { operation_size := RegWidth.W32,
  operation :=
    Operation.LDR (↑↑XReg.X0 RegWidth.W32)
      ↑{ base := ↑XRegOrSp.SP RegWidth.W64, off := ↑{ imm := ↑8, index := none } } } : Instr
-/
#guard_msgs in
#check ⸨instr| ldr w0, [sp, #8] ⸩

/--
info: { operation_size := RegWidth.W64, operation := Operation.B_cond CondCode.NE ↑"loop" } : Instr
-/
#guard_msgs in
#check ⸨instr| b.ne loop ⸩

-- Test: memory operands
/-- info: { base := ↑↑XReg.X0 RegWidth.W64, off := ↑{ imm := ↑0, index := none } } : AddrExpr -/
#guard_msgs in
#check ⸨mem| [x0] ⸩

/--
info: { base := ↑XRegOrSp.SP RegWidth.W64, off := ↑{ imm := ↑16, index := none } } : AddrExpr
-/
#guard_msgs in
#check ⸨mem| [sp, #16] ⸩

/--
info: { base := ↑↑XReg.X1 RegWidth.W64, off := ↑{ imm := ↑(-8), index := some Index.Pre } } : AddrExpr
-/
#guard_msgs in
#check ⸨mem| [x1, #-8]! ⸩

/--
info: { base := ↑↑XReg.X1 RegWidth.W64, off := ↑{ imm := ↑8, index := some Index.Post } } : AddrExpr
-/
#guard_msgs in
#check ⸨mem| [x1], #8 ⸩

/--
info: { base := ↑↑XReg.X0 RegWidth.W64,
  off :=
    ↑{ reg := { w := RegWidth.W64, reg := ↑↑XReg.X1 RegWidth.W64 },
        ext := { type := MemExtendType.UXTX, amount := MemExtendAmount.E3 } } } : AddrExpr
-/
#guard_msgs in
#check ⸨mem| [x0, x1, lsl #3] ⸩

/--
info: { base := ↑↑XReg.X0 RegWidth.W64,
  off :=
    ↑{ reg := { w := RegWidth.W32, reg := ↑↑XReg.X1 RegWidth.W32 },
        ext := { type := MemExtendType.SXTW, amount := MemExtendAmount.E0 } } } : AddrExpr
-/
#guard_msgs in
#check ⸨mem| [x0, w1, sxtw] ⸩

/--
info: { base := ↑↑XReg.X0 RegWidth.W64, off := ↑{ imm := (↑"sym").lo12, index := none } } : AddrExpr
-/
#guard_msgs in
#check ⸨mem| [x0, :lo12:sym] ⸩

/-- info: { base := ↑↑XReg.X0 RegWidth.W64, imm := ↑(-3) } : UnscaledAddrExpr -/
#guard_msgs in
#check (⸨mem| [x0, #-3] ⸩ : UnscaledAddrExpr)

/--
info: { base := ↑↑XReg.X0 RegWidth.W64,
  off :=
    ↑{ reg := { w := RegWidth.W64, reg := ↑XRegOrXzr.XZR RegWidth.W64 },
        ext := { type := MemExtendType.UXTX, amount := MemExtendAmount.E0 } } } : AddrExpr
-/
#guard_msgs in
#check ⸨mem| [x0, xzr] ⸩

/-- error: xzr/wzr not allowed here (sp/wsp expected) -/
#guard_msgs in
#check ⸨mem| [xzr] ⸩

-- Test: registers
/-- info: ↑↑XReg.X0 RegWidth.W64 : RegOrZr RegWidth.W64 -/
#guard_msgs in
#check ⸨reg| x0 ⸩

/-- info: ↑↑XReg.X3 RegWidth.W32 : RegOrZr RegWidth.W32 -/
#guard_msgs in
#check ⸨reg| w3 ⸩

/-- info: ↑XRegOrXzr.XZR RegWidth.W64 : RegOrZr RegWidth.W64 -/
#guard_msgs in
#check ⸨reg| xzr ⸩

/-- info: ↑XRegOrSp.SP RegWidth.W64 : RegOrSp RegWidth.W64 -/
#guard_msgs in
#check ⸨reg| sp ⸩

/-- info: ↑↑XReg.X0 RegWidth.W64 : RegOrSp RegWidth.W64 -/
#guard_msgs in
#check (⸨reg| x0 ⸩ : RegOrSp .W64)

/--
error: Type mismatch
  ↑↑XReg.X0 RegWidth.W64
has type
  RegOrZr RegWidth.W64
but is expected to have type
  RegOrZr RegWidth.W32
-/
#guard_msgs in
#check (⸨reg| x0 ⸩ : RegOrZr .W32)

-- Test: constant expressions
/-- info: ↑42 : ConstExpr -/
#guard_msgs in
#check ⸨const| #42 ⸩

/-- info: ↑"sym" : ConstExpr -/
#guard_msgs in
#check ⸨const| sym ⸩

/-- info: (↑"sym").pg_hi21 : ConstExpr -/
#guard_msgs in
#check ⸨const| :pg_hi21:sym ⸩

-- Test: condition codes
/-- info: CondCode.EQ : CondCode -/
#guard_msgs in
#check ⸨cc| eq ⸩

/-- info: CondCode.CS : CondCode -/
#guard_msgs in
#check ⸨cc| hs ⸩

-- Test: embeddings with antiquotations
section antiquotations

variable {w : RegWidth} (r : RegOrZr w) (rsp : RegOrSp w) (x : RegOrSp .W64) (c : ConstExpr)
  (lbl : Kraken.Label) (cc : CondCode) (a : AddrExpr) (u : UnscaledAddrExpr) (i : Int64)

/-- info: r : RegOrZr w -/
#guard_msgs in
#check ⸨reg| ❰r❱ ⸩

/-- info: rsp : RegOrSp w -/
#guard_msgs in
#check (⸨reg| ❰rsp❱ ⸩ : RegOrSp w)

/-- info: { base := x, off := ↑{ imm := c, index := none } } : AddrExpr -/
#guard_msgs in
#check ⸨mem| [❰x❱, ❰c❱] ⸩

/--
info: { base := ↑↑XReg.X0 RegWidth.W64, off := ↑{ imm := ↑i, index := some Index.Pre } } : AddrExpr
-/
#guard_msgs in
#check ⸨mem| [x0, #❰i❱]! ⸩

/-- info: a : AddrExpr -/
#guard_msgs in
#check ⸨mem| ❰a❱ ⸩

/-- info: u : UnscaledAddrExpr -/
#guard_msgs in
#check (⸨mem| ❰u❱ ⸩ : UnscaledAddrExpr)

/-- info: (↑lbl).lo12 : ConstExpr -/
#guard_msgs in
#check ⸨const| :lo12:❰lbl❱ ⸩

/-- info: cc : CondCode -/
#guard_msgs in
#check ⸨cc| ❰cc❱ ⸩

/-- info: { operation_size := w, operation := Operation.CSEL r r r cc } : Instr -/
#guard_msgs in
#check ⸨instr| csel ❰r❱, ❰r❱, ❰r❱, ❰cc❱ ⸩

-- Embeddings compose with each other through antiquotations
/--
info: { operation_size := RegWidth.W64,
  operation :=
    Operation.LDR (↑↑XReg.X0 RegWidth.W64)
      ↑{ base := ↑XRegOrSp.SP RegWidth.W64, off := ↑{ imm := ↑8, index := none } } } : Instr
-/
#guard_msgs in
#check ⸨instr| ldr x0, ❰⸨mem| [sp, #8] ⸩❱ ⸩

/--
info: { operation_size := RegWidth.W64,
  operation :=
    Operation.CSEL (↑↑XReg.X0 RegWidth.W64) (↑↑XReg.X1 RegWidth.W64) (↑↑XReg.X2 RegWidth.W64) CondCode.NE } : Instr
-/
#guard_msgs in
#check ⸨instr| csel x0, x1, x2, ❰⸨cc| ne ⸩❱ ⸩

end antiquotations

end Tests
