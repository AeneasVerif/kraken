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
/-- info: ⸨instr| add x0, x1, #1 ⸩ : Instr -/
#guard_msgs in
#check ⸨instr| add x0, x1, #1 ⸩

/-- info: ⸨instr| ldr w0, [sp, #8] ⸩ : Instr -/
#guard_msgs in
#check ⸨instr| ldr w0, [sp, #8] ⸩

/-- info: ⸨instr| b.ne loop ⸩ : Instr -/
#guard_msgs in
#check ⸨instr| b.ne loop ⸩

-- Test: memory operands
/-- info: ⸨mem| [x0] ⸩ : AddrExpr -/
#guard_msgs in
#check ⸨mem| [x0] ⸩

/-- info: ⸨mem| [sp, #16] ⸩ : AddrExpr -/
#guard_msgs in
#check ⸨mem| [sp, #16] ⸩

/-- info: ⸨mem| [x1, #-8]! ⸩ : AddrExpr -/
#guard_msgs in
#check ⸨mem| [x1, #-8]! ⸩

/-- info: ⸨mem| [x1], #8 ⸩ : AddrExpr -/
#guard_msgs in
#check ⸨mem| [x1], #8 ⸩

/-- info: ⸨mem| [x0, x1, lsl #3] ⸩ : AddrExpr -/
#guard_msgs in
#check ⸨mem| [x0, x1, lsl #3] ⸩

/-- info: ⸨mem| [x0, w1, sxtw] ⸩ : AddrExpr -/
#guard_msgs in
#check ⸨mem| [x0, w1, sxtw] ⸩

/-- info: ⸨mem| [x0, :lo12:sym] ⸩ : AddrExpr -/
#guard_msgs in
#check ⸨mem| [x0, :lo12:sym] ⸩

/-- info: ⸨mem| [x0, #-3] ⸩ : UnscaledAddrExpr -/
#guard_msgs in
#check (⸨mem| [x0, #-3] ⸩ : UnscaledAddrExpr)

/-- info: ⸨mem| [x0, xzr] ⸩ : AddrExpr -/
#guard_msgs in
#check ⸨mem| [x0, xzr] ⸩

/-- error: xzr/wzr not allowed here (sp/wsp expected) -/
#guard_msgs in
#check ⸨mem| [xzr] ⸩

-- Test: registers
/-- info: ⸨reg| x0 ⸩ : RegOrZr RegWidth.W64 -/
#guard_msgs in
#check ⸨reg| x0 ⸩

/-- info: ⸨reg| w3 ⸩ : RegOrZr RegWidth.W32 -/
#guard_msgs in
#check ⸨reg| w3 ⸩

/-- info: ⸨reg| xzr ⸩ : RegOrZr RegWidth.W64 -/
#guard_msgs in
#check ⸨reg| xzr ⸩

/-- info: ⸨reg| sp ⸩ : RegOrSp RegWidth.W64 -/
#guard_msgs in
#check ⸨reg| sp ⸩

/-- info: ⸨reg| x0 ⸩ : RegOrSp RegWidth.W64 -/
#guard_msgs in
#check (⸨reg| x0 ⸩ : RegOrSp .W64)

/--
error: Type mismatch
  ⸨reg| x0 ⸩
has type
  RegOrZr RegWidth.W64
but is expected to have type
  RegOrZr RegWidth.W32
-/
#guard_msgs in
#check (⸨reg| x0 ⸩ : RegOrZr .W32)

-- Test: constant expressions
/-- info: ⸨const| #42 ⸩ : ConstExpr -/
#guard_msgs in
#check ⸨const| #42 ⸩

/-- info: ⸨const| sym ⸩ : ConstExpr -/
#guard_msgs in
#check ⸨const| sym ⸩

/-- info: ⸨const| :pg_hi21:sym ⸩ : ConstExpr -/
#guard_msgs in
#check ⸨const| :pg_hi21:sym ⸩

-- Test: condition codes
/-- info: ⸨cc| eq ⸩ : CondCode -/
#guard_msgs in
#check ⸨cc| eq ⸩

/-- info: ⸨cc| cs ⸩ : CondCode -/
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

/-- info: ⸨mem| [❰x❱, ❰c❱] ⸩ : AddrExpr -/
#guard_msgs in
#check ⸨mem| [❰x❱, ❰c❱] ⸩

/-- info: ⸨mem| [x0, #❰i❱]! ⸩ : AddrExpr -/
#guard_msgs in
#check ⸨mem| [x0, #❰i❱]! ⸩

/-- info: a : AddrExpr -/
#guard_msgs in
#check ⸨mem| ❰a❱ ⸩

/-- info: u : UnscaledAddrExpr -/
#guard_msgs in
#check (⸨mem| ❰u❱ ⸩ : UnscaledAddrExpr)

/-- info: ⸨const| :lo12:❰lbl❱ ⸩ : ConstExpr -/
#guard_msgs in
#check ⸨const| :lo12:❰lbl❱ ⸩

/-- info: cc : CondCode -/
#guard_msgs in
#check ⸨cc| ❰cc❱ ⸩

/-- info: ⸨instr| csel ❰r❱, ❰r❱, ❰r❱, ❰cc❱ ⸩ : Instr -/
#guard_msgs in
#check ⸨instr| csel ❰r❱, ❰r❱, ❰r❱, ❰cc❱ ⸩

-- Embeddings compose with each other through antiquotations
/-- info: ⸨instr| ldr x0, [sp, #8] ⸩ : Instr -/
#guard_msgs in
#check ⸨instr| ldr x0, ❰⸨mem| [sp, #8] ⸩❱ ⸩

/-- info: ⸨instr| csel x0, x1, x2, ne ⸩ : Instr -/
#guard_msgs in
#check ⸨instr| csel x0, x1, x2, ❰⸨cc| ne ⸩❱ ⸩

end antiquotations

end Tests
