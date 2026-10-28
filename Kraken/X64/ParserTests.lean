module

/-
  Parser Tests - Extracted from Parser.lean
  Uses #guard_msgs to verify parser output against expected results.
-/

import Kraken.X64.Parser

section Tests
open Kraken.X64.Parser

open Instr Operand Reg

-- Test: Simple instruction
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.add ↑(low Reg64.rbx Width.W64) ↑↑(low Reg64.rax Width.W64)))] : List Directive
-/
#guard_msgs in
#check parse("addq %rax, %rbx")

-- Test: Immediate operand
/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.mov ↑(low Reg64.rax Width.W64) ↑↑42))] : List Directive
-/
#guard_msgs in
#check parse("movq $42, %rax")
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .mov (.Reg (.low .rax .W64)) (.imm 42) }]

/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.mov ↑(low Reg64.rax Width.W64) ↑↑0))] : List Directive
-/
#guard_msgs in
#check parse("movq $0, %rax")

/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.push ↑↑0))] : List Directive
-/
#guard_msgs in
#check parse("pushq $0x0")

/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.push ↑↑0))] : List Directive
-/
#guard_msgs in
#check parse("pushq $0")

-- Test: unsuffixed push and pop take their width from a register, else 64 bits
/--
info: [Directive.instr (regular Width.W64 Width.W16 (Operation.push ↑↑(low Reg64.rax Width.W16)))] : List Directive
-/
#guard_msgs in
#check parse("push %ax")

/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.push ↑↑1))] : List Directive
-/
#guard_msgs in
#check parse("push $1")

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.push ↑↑{ base := some (RegOrRip.reg Reg64.rax), idx := none }))] : List Directive
-/
#guard_msgs in
#check parse("push (%rax)")

/--
info: [Directive.instr (regular Width.W64 Width.W16 (Operation.pop ↑(low Reg64.rax Width.W16)))] : List Directive
-/
#guard_msgs in
#check parse("pop %ax")

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.pop ↑{ base := some (RegOrRip.reg Reg64.rax), idx := none }))] : List Directive
-/
#guard_msgs in
#check parse("pop (%rax)")

-- Test: Memory operand with displacement
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rax Width.W64)
        ↑↑{ base := some (RegOrRip.reg Reg64.rsp), idx := none, disp := ↑8 }))] : List Directive
-/
#guard_msgs in
#check parse("movq 8(%rsp), %rax")
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .mov (.Reg (.low .rax .W64)) (.mem .rsp .none 1 8) }]

-- Test: Memory operand with index and scale
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rax Width.W64)
        ↑↑{ base := some (RegOrRip.reg Reg64.rsi),
              idx := some { reg := Reg64.r15, scale := Width.W64 } }))] : List Directive
-/
#guard_msgs in
#check parse("movq (%rsi, %r15, 8), %rax")
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .mov (.Reg (.low .rax .W64)) (.mem .rsi (some .r15) 8 0) }]

-- Test: movsx/movzx with a memory source, movslq and movsxd
/--
info: [Directive.instr
    (regular Width.W64 Width.W16
      (Operation.movsx ↑(low Reg64.rbx Width.W16)
        ↑{ base := some (RegOrRip.reg Reg64.rax), idx := none }))] : List Directive
-/
#guard_msgs in
#check parse("movsbw (%rax), %bx")

/--
info: [Directive.instr
    (regular Width.W64 Width.W32
      (Operation.movsx ↑(low Reg64.rbx Width.W32)
        ↑{ base := some (RegOrRip.reg Reg64.rax), idx := none }))] : List Directive
-/
#guard_msgs in
#check parse("movsbl (%rax), %ebx")

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.movsx ↑(low Reg64.rbx Width.W64)
        ↑{ base := some (RegOrRip.reg Reg64.rax), idx := none }))] : List Directive
-/
#guard_msgs in
#check parse("movslq (%rax), %rbx")

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.movsx ↑(low Reg64.rbx Width.W64) ↑(low Reg64.rax Width.W32)))] : List Directive
-/
#guard_msgs in
#check parse("movslq %eax, %rbx")

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.movsx ↑(low Reg64.rbx Width.W64)
        ↑{ base := some (RegOrRip.reg Reg64.rax), idx := none }))] : List Directive
-/
#guard_msgs in
#check parse("movsxd (%rax), %rbx")

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.movsx ↑(low Reg64.rbx Width.W64) ↑(low Reg64.rax Width.W32)))] : List Directive
-/
#guard_msgs in
#check parse("movsxd %eax, %rbx")

/--
info: [Directive.instr
    (regular Width.W64 Width.W32
      (Operation.movzx ↑(low Reg64.rbx Width.W32)
        ↑{ base := some (RegOrRip.reg Reg64.rax), idx := none }))] : List Directive
-/
#guard_msgs in
#check parse("movzbl (%rax), %ebx")

-- Test: Labeled instruction
/--
info: [Directive.label "loop",
  Directive.instr (regular Width.W64 Width.W64 (Operation.add ↑(low Reg64.rcx Width.W64) ↑↑1))] : List Directive
-/
#guard_msgs in
#check parse("loop: addq $1, %rcx")
-- Expected: [.Label "loop", .Instr { address_size := .W64, operation_size := .W64, operation := .add (.Reg (.low .rcx .W64)) (.imm 1) }]

-- Test: Conditional jump
/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.jcc CondCode.nz "loop"))] : List Directive
-/
#guard_msgs in
#check parse("jnz loop")
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .jcc .nz "loop" }]

-- Symbol operands, as in GNU as: a bare symbol is a memory operand at that
-- absolute address (a load, not the address), `$sym` is the symbol's address
-- as an immediate, and `sym(%rip)` / `sym(%reg)` are memory operands with a
-- symbolic displacement.
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rax Width.W64) ↑↑{ base := none, idx := none, disp := ↑"sym" }))] : List Directive
-/
#guard_msgs in
#check parse("movq sym, %rax")

/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.mov ↑(low Reg64.rax Width.W64) ↑↑"sym"))] : List Directive
-/
#guard_msgs in
#check parse("movq $sym, %rax")

/--
info: [Directive.instr
    (regular Width.W64 Width.W64 (Operation.mov ↑(low Reg64.rax Width.W64) ↑((↑"sym").add ↑8)))] : List Directive
-/
#guard_msgs in
#check parse("movq $sym+8, %rax")

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rax Width.W64)
        ↑↑{ base := some RegOrRip.rip, idx := none,
              disp := (↑"sym").sub ConstExpr.after_current_instruction }))] : List Directive
-/
#guard_msgs in
#check parse("movq sym(%rip), %rax")

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rax Width.W64)
        ↑↑{ base := some RegOrRip.rip, idx := none,
              disp := ((↑"sym").add ↑8).sub ConstExpr.after_current_instruction }))] : List Directive
-/
#guard_msgs in
#check parse("movq sym+8(%rip), %rax")

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rbx Width.W64)
        ↑↑{ base := some (RegOrRip.reg Reg64.rax), idx := none, disp := ↑"sym" }))] : List Directive
-/
#guard_msgs in
#check parse("movq sym(%rax), %rbx")

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rbx Width.W64)
        ↑↑{ base := some (RegOrRip.reg Reg64.rax), idx := some { reg := Reg64.rcx, scale := Width.W32 },
              disp := (↑"sym").sub ↑8 }))] : List Directive
-/
#guard_msgs in
#check parse("movq sym-8(%rax,%rcx,4), %rbx")

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.add ↑{ base := none, idx := none, disp := ↑"sym" } ↑↑(low Reg64.rax Width.W64)))] : List Directive
-/
#guard_msgs in
#check parse("addq %rax, sym")

/--
info: [Directive.instr
    (avx Width.W64 AvxWidth.W128
      (AvxOperation.movups ↑(AvxReg.xmm RegMm.mm0)
        ↑{ base := some RegOrRip.rip, idx := none,
            disp := (↑"sym").sub ConstExpr.after_current_instruction }))] : List Directive
-/
#guard_msgs in
#check parse("movups sym(%rip), %xmm0")

-- Neighbouring forms: lea, branch targets, numeric
-- RIP-relative offsets.
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.lea (low Reg64.rax Width.W64)
        { base := some RegOrRip.rip, idx := none,
          disp := (↑"sym").sub ConstExpr.after_current_instruction }))] : List Directive
-/
#guard_msgs in
#check parse("leaq sym(%rip), %rax")

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.lea (low Reg64.rax Width.W64)
        { base := some (RegOrRip.reg Reg64.rax), idx := none, disp := ↑"sym" }))] : List Directive
-/
#guard_msgs in
#check parse("leaq sym(%rax), %rax")

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.jmp (RelRegOrMem.rel ((↑"sym").sub ConstExpr.after_current_instruction))))] : List Directive
-/
#guard_msgs in
#check parse("jmp sym")

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.call (RelRegOrMem.rel ((↑"sym").sub ConstExpr.after_current_instruction))))] : List Directive
-/
#guard_msgs in
#check parse("call sym")

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rax Width.W64)
        ↑↑{ base := some RegOrRip.rip, idx := none, disp := ↑8 }))] : List Directive
-/
#guard_msgs in
#check parse("movq 8(%rip), %rax")

-- Like a bare symbol, a bare number is a memory operand at that absolute
-- address (`as`: `mov 0x1,%rax`, `xor %rax,0x1`).
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rax Width.W64) ↑↑{ base := none, idx := none, disp := ↑1 }))] : List Directive
-/
#guard_msgs in
#check parse("movq 1, %rax")

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.xor ↑{ base := none, idx := none, disp := ↑1 } ↑↑(low Reg64.rax Width.W64)))] : List Directive
-/
#guard_msgs in
#check parse("xorq %rax, 1")

-- Test: Multi-line program
/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.mov ↑(low Reg64.rax Width.W64) ↑↑0)), Directive.label "loop",
  Directive.instr (regular Width.W64 Width.W64 (Operation.add ↑(low Reg64.rax Width.W64) ↑↑1)),
  Directive.instr (regular Width.W64 Width.W64 (Operation.cmp ↑(low Reg64.rax Width.W64) ↑↑10)),
  Directive.instr (regular Width.W64 Width.W64 (Operation.jcc CondCode.nz "loop"))] : List Directive
-/
#guard_msgs in
#check parse("
  movq $0, %rax
loop:
  addq $1, %rax
  cmpq $10, %rax
  jne loop
")

-- Test: Negative immediate
/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.add ↑(low Reg64.rax Width.W64) ↑↑(-1)))] : List Directive
-/
#guard_msgs in
#check parse("addq $-1, %rax")

-- Test: Hex immediate
/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.mov ↑(low Reg64.rax Width.W64) ↑↑255))] : List Directive
-/
#guard_msgs in
#check parse("movq $0xff, %rax")

-- Test: mulx instruction
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mulx (low Reg64.r10 Width.W64) (low Reg64.r9 Width.W64) ↑(low Reg64.r8 Width.W64)))] : List Directive
-/
#guard_msgs in
#check parse("mulxq %r8, %r9, %r10")

-- Test: xor for zeroing
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.xor ↑(low Reg64.rax Width.W64) ↑↑(low Reg64.rax Width.W64)))] : List Directive
-/
#guard_msgs in
#check parse("xorq %rax, %rax")

-- Test: lea with complex addressing
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.lea (low Reg64.rax Width.W64)
        { base := some (RegOrRip.reg Reg64.rbp), idx := some { reg := Reg64.rcx, scale := Width.W32 },
          disp := ↑16 }))] : List Directive
-/
#guard_msgs in
#check parse("leaq 16(%rbp, %rcx, 4), %rax")

/--
info: [Directive.instr
    (regular Width.W32 Width.W64
      (Operation.lea (low Reg64.rax Width.W64)
        { base := some (RegOrRip.reg Reg64.rbp), idx := some { reg := Reg64.rcx, scale := Width.W32 },
          disp := ↑16 }))] : List Directive
-/
#guard_msgs in
#check parse("leaq 16(%ebp, %ecx, 4), %rax")

section error_reporting

/-- error: <input>:1:12: expected x64_reg_name -/
#guard_msgs in
#check parse("xorq %rax, %unlikely")

/-- error: type error: w64 != w32 -/
#guard_msgs in
#check parse("mov (%rax, %ebx), %rax")

/-- error: can't have two memory operands -/
#guard_msgs in
#check parse("mov (%rax), (%rax)")

/-- error: high byte register cannot be used for an addrexpr -/
#guard_msgs in
#check parse("mov $2, (%ah)")

/-- error: <input>:1:9: unexpected end of input; expected ',' -/
#guard_msgs in
#check parse("addq %rax")

/-- error: expected register or memory operand, got $ -/
#guard_msgs in
#check parse("xorq %rax, $1")

/-- error: can't have two memory operands -/
#guard_msgs in
#check parse("movq sym, sym2")

/-- error: absolute branch targets are not supported -/
#guard_msgs in
#check parse("jmp 0x10")

/-- error: <input>:1:4: unexpected end of input -/
#guard_msgs in
#check parse("addq")

/-- error: <input>:3:2: expected ',' -/
#guard_msgs in
#check parse("
  addq %rax
  cmpq $10, %rax
")

/-- error: type error: w64 != w32 -/
#guard_msgs in
#check parse("movq %eax, %rbx")

/-- error: invalid scale 3, must be 1, 2, 4, or 8 -/
#guard_msgs in
#check parse("movq (%rax, %rcx, 3), %rbx")

/-- error: <input>:1:16: unexpected element; expected ';' -/
#guard_msgs in
#check parse("movq %rax, %rbx garbage")

/-- error: <input>:1:9: unexpected element; expected ';' -/
#guard_msgs in
#check parse("shlq %rcx, %rax")

/-- error: <input>:1:0: expected end of input -/
#guard_msgs in
#check parse("foo\n:")

end error_reporting

section syntax_cat_and_include

/--
info: [Directive.label "loop", Directive.instr (regular Width.W64 Width.W64 (Operation.add ↑(low Reg64.rax Width.W64) ↑↑1)),
  Directive.instr (regular Width.W64 Width.W64 (Operation.jcc CondCode.nz "loop"))] : List Directive
-/
#guard_msgs in
#check [x64|
  loop:
    addq $1, %rax
    jnz loop
]

/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.nop 1))] : List Directive
-/
#guard_msgs in
#check include_x64 "Kraken/X64/Test/asm/test_nop.S"

/--
info: [Directive.label "aa.1.aa.1",
  Directive.instr
    (regular Width.W64 Width.W64
      (Operation.jmp
        (RelRegOrMem.rel ((↑".L.str.1.llvm.12345").sub ConstExpr.after_current_instruction))))] : List Directive
-/
#guard_msgs in
#check [x64|
  aa.1.aa.1:
    jmp .L.str.1.llvm.12345
]

end syntax_cat_and_include

section antiquotations

variable {w : Width} (r : Reg w) (q : Reg .W64) (r64 : Reg64) (v : AvxReg .W256)

-- Test: an antiquoted register decides the width of its instruction, which may be a variable
/-- info: [Directive.instr (regular Width.W64 w (Operation.add ↑r ↑↑2))] : List Directive -/
#guard_msgs in
#check [x64| add $2, %❰r❱ ]

-- Test: antiquoted and concrete registers unify
/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.mov ↑q ↑↑(low Reg64.rax Width.W64)))] : List Directive
-/
#guard_msgs in
#check [x64| mov %rax, %❰q❱ ]

-- Test: a width suffix must agree with the antiquoted register's width
/--
error: Type mismatch
  r
has type
  Reg w
but is expected to have type
  Reg Width.W64
-/
#guard_msgs in
#check [x64| addq $1, %❰r❱ ]

/-- error: type error: w != w32 -/
#guard_msgs in
#check [x64| add %❰r❱, %eax ]

-- Test: in address positions, antiquotations denote `Reg64`
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rcx Width.W64)
        ↑↑{ base := some (RegOrRip.reg r64), idx := some { reg := Reg64.rax, scale := Width.W32 },
              disp := ↑8 }))] : List Directive
-/
#guard_msgs in
#check [x64| mov 8(%❰r64❱, %rax, 4), %rcx ]

-- Test: AVX registers
/--
info: [Directive.instr
    (avx Width.W64 AvxWidth.W256
      (AvxOperation.vmovups ↑v ↑{ base := some (RegOrRip.reg Reg64.rax), idx := none }))] : List Directive
-/
#guard_msgs in
#check [x64| vmovups (%rax), %❰v❱ ]

-- Test: a width that no operand or suffix determines is an error
/-- error: could not infer operand width -/
#guard_msgs in
#check [x64| add $1, (%rax) ]

-- Test: the source of a widening move must be narrower than its destination
/-- error: source width w64 must be narrower than destination width w16 -/
#guard_msgs in
#check [x64| movsx %rax, %bx ]

-- Test: antiquotations for operands, instructions and directives
variable (o : Operand .W32) (rm : RegOrMem w) (av : AvxRegOrMem .W128) (rt : RelRegOrMem) (i : Instr) (d : Directive)

/-- info: [Directive.instr (regular Width.W64 Width.W32 (Operation.add (↑(low Reg64.rax Width.W32)) o))] : List Directive -/
#guard_msgs in
#check [x64| add ❰o❱, %eax ]

/-- info: [Directive.instr (regular Width.W64 w (Operation.inc rm))] : List Directive -/
#guard_msgs in
#check [x64| inc ❰rm❱ ]

/-- info: [Directive.instr (avx Width.W64 AvxWidth.W128 (AvxOperation.movaps (↑(AvxReg.xmm RegMm.mm1)) av))] : List Directive -/
#guard_msgs in
#check [x64| movaps ❰av❱, %xmm1 ]

/-- info: [Directive.instr (regular Width.W64 Width.W64 (Operation.jmp rt))] : List Directive -/
#guard_msgs in
#check [x64| jmp ❰rt❱ ]

/-- info: [Directive.instr i, d, Directive.instr (regular Width.W64 Width.W64 Operation.ret)] : List Directive -/
#guard_msgs in
#check [x64| ❰.instr i❱; ❰d❱; ret ]

/-- info: [Directive.label "foo", Directive.instr (regular Width.W64 Width.W64 Operation.ret)] : List Directive -/
#guard_msgs in
#check [x64| ❰.label "foo"❱; ❰.instr <| .regular .W64 .W64 .ret❱ ]

end antiquotations

end Tests
