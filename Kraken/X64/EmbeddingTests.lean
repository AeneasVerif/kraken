module

/-
  Embedding Tests: standalone embeddings of the elements of an X64 program
  (`⸨instr|`, `⸨operand|`, `⸨mem|`, `⸨reg|`, `⸨const|`).
-/

import Kraken.X64.Parser
meta import Kraken.X64.Parser

section Tests
open Kraken.X64.Parser

open Instr Operand Reg Kraken

-- Test: instructions
/-- info: ⸨instr| addq %rax, %rbx ⸩ : Instr -/
#guard_msgs in
#check ⸨instr| addq %rax, %rbx ⸩

/-- info: ⸨instr| movl $1, 8(%esp) ⸩ : Instr -/
#guard_msgs in
#check ⸨instr| movl $1, 8(%esp) ⸩

/-- info: ⸨instr| vmovdqu %ymm1, %ymm2 ⸩ : Instr -/
#guard_msgs in
#check ⸨instr| vmovdqu %ymm1, %ymm2 ⸩

-- Test: operands take their width from their registers, or else from the expected type
/-- info: ⸨operand| %eax ⸩ : Operand Width.W32 -/
#guard_msgs in
#check ⸨operand| %eax ⸩

/-- info: ⸨operand| 8(%rax) ⸩ : Operand Width.W64 -/
#guard_msgs in
#check (⸨operand| 8(%rax) ⸩ : Operand .W64)

/-- info: ⸨operand| $1 ⸩ : Operand Width.W16 -/
#guard_msgs in
#check (⸨operand| $1 ⸩ : Operand .W16)

/-- error: could not infer operand width, consider adding a type ascription -/
#guard_msgs in
#check ⸨operand| $1 ⸩

-- Test: memory operands
/-- info: ⸨mem| (%rax) ⸩ : AddrExpr -/
#guard_msgs in
#check ⸨mem| 0(%eax) ⸩

/-- info: ⸨mem| (%rax) ⸩ : AddrExpr -/
#guard_msgs in
#check ⸨mem| 0(%rax) ⸩

/-- info: ⸨mem| -8(%rbp, %rcx, 4) ⸩ : AddrExpr -/
#guard_msgs in
#check ⸨mem| -8(%rbp, %rcx, 4) ⸩

/-- info: ⸨mem| lbl(%rip) ⸩ : AddrExpr -/
#guard_msgs in
#check ⸨mem| lbl(%rip) ⸩

/-- info: ⸨mem| 16 ⸩ : AddrExpr -/
#guard_msgs in
#check ⸨mem| 16 ⸩

example : ⸨mem| 0(%eax) ⸩ = ⸨mem| 0(%rax) ⸩ := rfl

-- Test: registers
/-- info: ⸨reg| %eax ⸩ : Reg Width.W32 -/
#guard_msgs in
#check ⸨reg| %eax ⸩

/-- info: ⸨reg| %ah ⸩ : Reg Width.W8 -/
#guard_msgs in
#check ⸨reg| %ah ⸩

/-- info: ⸨reg| %r9w ⸩ : Reg Width.W16 -/
#guard_msgs in
#check ⸨reg| %r9w ⸩

/-- info: ⸨reg| %ymm3 ⸩ : AvxReg AvxWidth.W256 -/
#guard_msgs in
#check ⸨reg| %ymm3 ⸩

/--
error: Type mismatch
  ⸨reg| %rax ⸩
has type
  Reg Width.W64
but is expected to have type
  Reg Width.W32
-/
#guard_msgs in
#check (⸨reg| %rax ⸩ : Reg .W32)

-- Test: constant expressions
/-- info: ⸨const| 42 ⸩ : ConstExpr -/
#guard_msgs in
#check ⸨const| 42 ⸩

/-- info: ⸨const| -1 ⸩ : ConstExpr -/
#guard_msgs in
#check ⸨const| -1 ⸩

/-- info: ⸨const| lbl+8 ⸩ : ConstExpr -/
#guard_msgs in
#check ⸨const| lbl+8 ⸩

/-- info: ⸨const| .Lend-.Lstart ⸩ : ConstExpr -/
#guard_msgs in
#check ⸨const| .Lend - .Lstart ⸩

-- Test: embeddings with antiquotations
section antiquotations

variable {w : Width} (r : Reg w) (v : AvxReg .W256) (r64 : Reg64) (lbl : Kraken.Label) (c : ConstExpr)
  (o : Operand .W32)

/-- info: r : Reg w -/
#guard_msgs in
#check ⸨reg| %❰r❱ ⸩

/-- info: v : AvxReg AvxWidth.W256 -/
#guard_msgs in
#check ⸨reg| %❰v❱ ⸩

/-- info: ⸨operand| %❰r❱ ⸩ : Operand w -/
#guard_msgs in
#check ⸨operand| %❰r❱ ⸩

/-- info: o : Operand Width.W32 -/
#guard_msgs in
#check ⸨operand| ❰o❱ ⸩

/-- info: ⸨mem| ❰c❱(%❰r64❱) ⸩ : AddrExpr -/
#guard_msgs in
#check ⸨mem| ❰c❱(%❰r64❱) ⸩

/-- info: ⸨const| ❰lbl❱+4 ⸩ : ConstExpr -/
#guard_msgs in
#check ⸨const| ❰lbl❱+4 ⸩

/-- info: ⸨instr| add %❰r❱, %❰r❱ ⸩ : Instr -/
#guard_msgs in
#check ⸨instr| add %❰r❱, %❰r❱ ⸩

-- Embeddings compose with each other through antiquotations
/-- info: ⸨instr| movq %rax, 8(%rsp) ⸩ : Instr -/
#guard_msgs in
#check ⸨instr| movq ❰⸨operand| %rax ⸩❱, ❰⸨mem| 8(%rsp) ⸩❱ ⸩

end antiquotations

end Tests
