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
/--
info: regular Width.W64 Width.W64 (Operation.add ↑(low Reg64.rbx Width.W64) ↑↑(low Reg64.rax Width.W64)) : Instr
-/
#guard_msgs in
#check ⸨instr| addq %rax, %rbx ⸩

/--
info: regular Width.W32 Width.W32
  (Operation.mov ↑{ base := some (RegOrRip.reg Reg64.rsp), idx := none, disp := ↑8 } ↑↑1) : Instr
-/
#guard_msgs in
#check ⸨instr| movl $1, 8(%esp) ⸩

/--
info: avx Width.W64 AvxWidth.W256 (AvxOperation.vmovdqu ↑(AvxReg.ymm RegMm.mm2) ↑(AvxReg.ymm RegMm.mm1)) : Instr
-/
#guard_msgs in
#check ⸨instr| vmovdqu %ymm1, %ymm2 ⸩

-- Test: operands take their width from their registers, or else from the expected type
/-- info: ↑↑(low Reg64.rax Width.W32) : Operand Width.W32 -/
#guard_msgs in
#check ⸨operand| %eax ⸩

/--
info: ↑↑{ base := some (RegOrRip.reg Reg64.rax), idx := none, disp := ↑8 } : Operand Width.W64
-/
#guard_msgs in
#check (⸨operand| 8(%rax) ⸩ : Operand .W64)

/-- info: ↑↑1 : Operand Width.W16 -/
#guard_msgs in
#check (⸨operand| $1 ⸩ : Operand .W16)

/-- error: could not infer operand width, consider adding a type ascription -/
#guard_msgs in
#check ⸨operand| $1 ⸩

-- Test: memory operands
/-- info: { base := some (RegOrRip.reg Reg64.rax), idx := none } : AddrExpr -/
#guard_msgs in
#check ⸨mem| 0(%eax) ⸩

/-- info: { base := some (RegOrRip.reg Reg64.rax), idx := none } : AddrExpr -/
#guard_msgs in
#check ⸨mem| 0(%rax) ⸩

/--
info: { base := some (RegOrRip.reg Reg64.rbp), idx := some { reg := Reg64.rcx, scale := Width.W32 },
  disp := ↑(-8) } : AddrExpr
-/
#guard_msgs in
#check ⸨mem| -8(%rbp, %rcx, 4) ⸩

/--
info: { base := some RegOrRip.rip, idx := none, disp := (↑"lbl").sub ConstExpr.after_current_instruction } : AddrExpr
-/
#guard_msgs in
#check ⸨mem| lbl(%rip) ⸩

/-- info: { base := none, idx := none, disp := ↑16 } : AddrExpr -/
#guard_msgs in
#check ⸨mem| 16 ⸩

example : ⸨mem| 0(%eax) ⸩ = ⸨mem| 0(%rax) ⸩ := rfl

-- Test: registers
/-- info: low Reg64.rax Width.W32 : Reg Width.W32 -/
#guard_msgs in
#check ⸨reg| %eax ⸩

/-- info: ah : Reg Width.W8 -/
#guard_msgs in
#check ⸨reg| %ah ⸩

/-- info: low Reg64.r9 Width.W16 : Reg Width.W16 -/
#guard_msgs in
#check ⸨reg| %r9w ⸩

/-- info: AvxReg.ymm RegMm.mm3 : AvxReg AvxWidth.W256 -/
#guard_msgs in
#check ⸨reg| %ymm3 ⸩

/--
error: Type mismatch
  low Reg64.rax Width.W64
has type
  Reg Width.W64
but is expected to have type
  Reg Width.W32
-/
#guard_msgs in
#check (⸨reg| %rax ⸩ : Reg .W32)

-- Test: constant expressions
/-- info: ↑42 : ConstExpr -/
#guard_msgs in
#check ⸨const| 42 ⸩

/-- info: ↑(-1) : ConstExpr -/
#guard_msgs in
#check ⸨const| -1 ⸩

/-- info: (↑"lbl").add ↑8 : ConstExpr -/
#guard_msgs in
#check ⸨const| lbl+8 ⸩

/-- info: (↑".Lend").sub ↑".Lstart" : ConstExpr -/
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

/-- info: ↑↑r : Operand w -/
#guard_msgs in
#check ⸨operand| %❰r❱ ⸩

/-- info: o : Operand Width.W32 -/
#guard_msgs in
#check ⸨operand| ❰o❱ ⸩

/-- info: { base := some (RegOrRip.reg r64), idx := none, disp := c } : AddrExpr -/
#guard_msgs in
#check ⸨mem| ❰c❱(%❰r64❱) ⸩

/-- info: (↑lbl).add ↑4 : ConstExpr -/
#guard_msgs in
#check ⸨const| ❰lbl❱+4 ⸩

/-- info: regular Width.W64 w (Operation.add ↑r ↑↑r) : Instr -/
#guard_msgs in
#check ⸨instr| add %❰r❱, %❰r❱ ⸩

-- Embeddings compose with each other through antiquotations
/--
info: regular Width.W64 Width.W64
  (Operation.mov ↑{ base := some (RegOrRip.reg Reg64.rsp), idx := none, disp := ↑8 }
    ↑↑(low Reg64.rax Width.W64)) : Instr
-/
#guard_msgs in
#check ⸨instr| movq ❰⸨operand| %rax ⸩❱, ❰⸨mem| 8(%rsp) ⸩❱ ⸩

end antiquotations

end Tests
