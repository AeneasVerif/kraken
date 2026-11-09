module

/-
  Parser Tests - Extracted from Parser.lean
  Uses #guard_msgs to verify parser output against expected results.
-/

public import Lean
public meta import Lean
public import Kraken.X64.Parser
public meta import Kraken.X64.Parser
import Kraken.X64.PrintATT
meta import Kraken.X64.PrintATT

section Tests
open Kraken.X64.Parser

open Instr Operand Reg Kraken

-- Test: Simple instruction
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.add ↑(low Reg64.rbx Width.W64) ↑↑(low Reg64.rax Width.W64)))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| addq %rax, %rbx ⸩

-- Test: Immediate operand
/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.mov ↑(low Reg64.rax Width.W64) ↑↑42))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq $42, %rax ⸩
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .mov (.Reg (.low .rax .W64)) (.imm 42) }]

/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.mov ↑(low Reg64.rax Width.W64) ↑↑0))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq $0, %rax ⸩

/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.push ↑↑0))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| pushq $0x0 ⸩

/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.push ↑↑0))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| pushq $0 ⸩

-- Test: unsuffixed push and pop take their width from a register, else 64 bits
/--
info: [Directive.instr (regular Width.W64 Width.W16 (Operation.push ↑↑(low Reg64.rax Width.W16)))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| push %ax ⸩

/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.push ↑↑1))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| push $1 ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.push ↑↑{ base := some (RegOrRip.reg Reg64.rax), idx := none }))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| push (%rax) ⸩

/--
info: [Directive.instr (regular Width.W64 Width.W16 (Operation.pop ↑(low Reg64.rax Width.W16)))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| pop %ax ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.pop ↑{ base := some (RegOrRip.reg Reg64.rax), idx := none }))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| pop (%rax) ⸩

-- Test: Memory operand with displacement
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rax Width.W64)
        ↑↑{ base := some (RegOrRip.reg Reg64.rsp), idx := none, disp := ↑8 }))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq 8(%rsp), %rax ⸩
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .mov (.Reg (.low .rax .W64)) (.mem .rsp .none 1 8) }]

-- Test: Memory operand with index and scale
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rax Width.W64)
        ↑↑{ base := some (RegOrRip.reg Reg64.rsi),
              idx := some { reg := Reg64.r15, scale := Width.W64 } }))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq (%rsi, %r15, 8), %rax ⸩
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .mov (.Reg (.low .rax .W64)) (.mem .rsi (some .r15) 8 0) }]

-- Test: movsx/movzx with a memory source, movslq and movsxd
/--
info: [Directive.instr
    (regular Width.W64 Width.W16
      (Operation.movsx ↑(low Reg64.rbx Width.W16)
        ↑{ base := some (RegOrRip.reg Reg64.rax), idx := none }))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movsbw (%rax), %bx ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W32
      (Operation.movsx ↑(low Reg64.rbx Width.W32)
        ↑{ base := some (RegOrRip.reg Reg64.rax), idx := none }))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movsbl (%rax), %ebx ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.movsx ↑(low Reg64.rbx Width.W64)
        ↑{ base := some (RegOrRip.reg Reg64.rax), idx := none }))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movslq (%rax), %rbx ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.movsx ↑(low Reg64.rbx Width.W64) ↑(low Reg64.rax Width.W32)))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movslq %eax, %rbx ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.movsx ↑(low Reg64.rbx Width.W64)
        ↑{ base := some (RegOrRip.reg Reg64.rax), idx := none }))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movsxd (%rax), %rbx ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.movsx ↑(low Reg64.rbx Width.W64) ↑(low Reg64.rax Width.W32)))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movsxd %eax, %rbx ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W32
      (Operation.movzx ↑(low Reg64.rbx Width.W32)
        ↑{ base := some (RegOrRip.reg Reg64.rax), idx := none }))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movzbl (%rax), %ebx ⸩

-- Test: Labeled instruction
/--
info: [Directive.label "loop",
  Directive.instr (regular Width.W64 Width.W64 (Operation.add ↑(low Reg64.rcx Width.W64) ↑↑1))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| loop: addq $1, %rcx ⸩
-- Expected: [.Label "loop", .Instr { address_size := .W64, operation_size := .W64, operation := .add (.Reg (.low .rcx .W64)) (.imm 1) }]

-- Test: Conditional jump
/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.jcc CondCode.nz "loop"))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| jnz loop ⸩
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .jcc .nz "loop" }]

-- Symbol operands, as in GNU as: a bare symbol is a memory operand at that
-- absolute address (a load, not the address), `$sym` is the symbol's address
-- as an immediate, and `sym(%rip)` / `sym(%reg)` are memory operands with a
-- symbolic displacement.
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rax Width.W64) ↑↑{ base := none, idx := none, disp := ↑"sym" }))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq sym, %rax ⸩

/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.mov ↑(low Reg64.rax Width.W64) ↑↑"sym"))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq $sym, %rax ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W64 (Operation.mov ↑(low Reg64.rax Width.W64) ↑((↑"sym").add ↑8)))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq $sym+8, %rax ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rax Width.W64)
        ↑↑{ base := some RegOrRip.rip, idx := none,
              disp := (↑"sym").sub ConstExpr.after_current_instruction }))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq sym(%rip), %rax ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rax Width.W64)
        ↑↑{ base := some RegOrRip.rip, idx := none,
              disp := ((↑"sym").add ↑8).sub ConstExpr.after_current_instruction }))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq sym+8(%rip), %rax ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rbx Width.W64)
        ↑↑{ base := some (RegOrRip.reg Reg64.rax), idx := none, disp := ↑"sym" }))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq sym(%rax), %rbx ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rbx Width.W64)
        ↑↑{ base := some (RegOrRip.reg Reg64.rax), idx := some { reg := Reg64.rcx, scale := Width.W32 },
              disp := (↑"sym").sub ↑8 }))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq sym-8(%rax,%rcx,4), %rbx ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.add ↑{ base := none, idx := none, disp := ↑"sym" } ↑↑(low Reg64.rax Width.W64)))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| addq %rax, sym ⸩

/--
info: [Directive.instr
    (avx Width.W64 AvxWidth.W128
      (AvxOperation.movups ↑(AvxReg.xmm RegMm.mm0)
        ↑{ base := some RegOrRip.rip, idx := none,
            disp := (↑"sym").sub ConstExpr.after_current_instruction }))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movups sym(%rip), %xmm0 ⸩

-- Neighbouring forms: lea, branch targets, numeric
-- RIP-relative offsets.
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.lea (low Reg64.rax Width.W64)
        { base := some RegOrRip.rip, idx := none,
          disp := (↑"sym").sub ConstExpr.after_current_instruction }))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| leaq sym(%rip), %rax ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.lea (low Reg64.rax Width.W64)
        { base := some (RegOrRip.reg Reg64.rax), idx := none, disp := ↑"sym" }))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| leaq sym(%rax), %rax ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.jmp (RelRegOrMem.rel ((↑"sym").sub ConstExpr.after_current_instruction))))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| jmp sym ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.call (RelRegOrMem.rel ((↑"sym").sub ConstExpr.after_current_instruction))))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| call sym ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rax Width.W64)
        ↑↑{ base := some RegOrRip.rip, idx := none, disp := ↑8 }))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq 8(%rip), %rax ⸩

-- Like a bare symbol, a bare number is a memory operand at that absolute
-- address (`as`: `mov 0x1,%rax`, `xor %rax,0x1`).
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rax Width.W64) ↑↑{ base := none, idx := none, disp := ↑1 }))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq 1, %rax ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.xor ↑{ base := none, idx := none, disp := ↑1 } ↑↑(low Reg64.rax Width.W64)))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| xorq %rax, 1 ⸩

-- Test: Multi-line program
/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.mov ↑(low Reg64.rax Width.W64) ↑↑0)), Directive.label "loop",
  Directive.instr (regular Width.W64 Width.W64 (Operation.add ↑(low Reg64.rax Width.W64) ↑↑1)),
  Directive.instr (regular Width.W64 Width.W64 (Operation.cmp ↑(low Reg64.rax Width.W64) ↑↑10)),
  Directive.instr (regular Width.W64 Width.W64 (Operation.jcc CondCode.nz "loop"))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog|
  movq $0, %rax
loop:
  addq $1, %rax
  cmpq $10, %rax
  jne loop
⸩

-- Test: Negative immediate
/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.add ↑(low Reg64.rax Width.W64) ↑↑(-1)))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| addq $-1, %rax ⸩

-- Test: Hex immediate
/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.mov ↑(low Reg64.rax Width.W64) ↑↑255))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq $0xff, %rax ⸩

-- Test: mulx instruction
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mulx (low Reg64.r10 Width.W64) (low Reg64.r9 Width.W64) ↑(low Reg64.r8 Width.W64)))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| mulxq %r8, %r9, %r10 ⸩

-- Test: xor for zeroing
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.xor ↑(low Reg64.rax Width.W64) ↑↑(low Reg64.rax Width.W64)))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| xorq %rax, %rax ⸩

-- Test: lea with complex addressing
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.lea (low Reg64.rax Width.W64)
        { base := some (RegOrRip.reg Reg64.rbp), idx := some { reg := Reg64.rcx, scale := Width.W32 },
          disp := ↑16 }))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| leaq 16(%rbp, %rcx, 4), %rax ⸩

/--
info: [Directive.instr
    (regular Width.W32 Width.W64
      (Operation.lea (low Reg64.rax Width.W64)
        { base := some (RegOrRip.reg Reg64.rbp), idx := some { reg := Reg64.rcx, scale := Width.W32 },
          disp := ↑16 }))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| leaq 16(%ebp, %ecx, 4), %rax ⸩

section data_words

/-- info: [Directive.word 4 ((↑"end").sub ↑"start")] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| .long end - start ⸩

/-- info: [Directive.word 8 ↑"sym"] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| .quad sym ⸩

/-- info: [Directive.word 2 ↑7] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| .short 7 ⸩

/-- info: [Directive.word 4 ((↑"sym").add ↑8)] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| .long sym+8 ⸩

/-- info: [Directive.word 8 ↑(-1)] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| .quad -1 ⸩

/-- info: [Directive.instr (regular Width.W64 Width.W64 (Operation.mov ↑(low Reg64.rax Width.W64) ↑((↑"b").sub ↑"a")))] : List _root_.Directive -/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movq $b-a, %rax ⸩

-- A label that begins with a directive word is still a label.
/--
info: [Directive.label ".longest", Directive.instr (regular Width.W64 Width.W64 (Operation.nop 1))] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog|
.longest:
  nop
⸩

-- The jump table of clang's `sel` (as in `PrintATTTests.jumpTable`) elaborates to the same words as
-- the combinator parser produces.
#guard (⸨prog|
sel:
  cmpl $2, %edi
  ja .Ldefault
  movl %edi, %eax
  leaq .LJTI0_0(%rip), %rcx
  movslq (%rcx,%rax,4), %rax
  addq %rcx, %rax
  jmp %rax
.Lcase0:
  movl $10, %eax
  ret
.Lcase1:
  movl $20, %eax
  ret
.Lcase2:
  movl $30, %eax
  ret
.Ldefault:
  xorl %eax, %eax
  ret
  .align 4
.LJTI0_0:
  .long .Lcase0 - .LJTI0_0
  .long .Lcase1 - .LJTI0_0
  .long .Lcase2 - .LJTI0_0
⸩ : Program).drop 22 ==
  [0, 1, 2].map (fun k => .word 4 (.sub (.label s!".Lcase{k}") (.label ".LJTI0_0")))

/-- Printing `p` in AT&T syntax and reading it back with the combinator parser gives `p`. -/
def agreesWithCombinatorParser (p : Program) : Bool :=
  match Kraken.X64.Parser.parse (Kraken.X64.toATT p) with
  | .ok p' => p' == p
  | .error _ => false

#guard [⸨prog| .long end - start ⸩, ⸨prog| .quad sym ⸩, ⸨prog| .short 7 ⸩, ⸨prog| .long sym+8 ⸩,
  ⸨prog| .quad -1 ⸩, ⸨prog| movq $b-a, %rax ⸩, ⸨prog|
.longest:
  nop
⸩].all agreesWithCombinatorParser

end data_words

section error_reporting

local elab "elabX64% " s:str : term => elabX64 s.getString

/-- error: <input>:1:5: unexpected end of input -/
#guard_msgs in
#check elabX64% ".long"

/-- error: <input>:1:12: expected x64_reg_name -/
#guard_msgs in
#check elabX64% "xorq %rax, %unlikely"

/-- error: type error: w64 != w32 -/
#guard_msgs in
#check ⸨prog| mov (%rax, %ebx), %rax ⸩

/-- error: can't have two memory operands -/
#guard_msgs in
#check ⸨prog| mov (%rax), (%rax) ⸩

/-- error: high byte register cannot be used for an addrexpr -/
#guard_msgs in
#check ⸨prog| mov $2, (%ah) ⸩

/-- error: <input>:1:9: unexpected end of input; expected ',' -/
#guard_msgs in
#check elabX64% "addq %rax"

/-- error: expected register or memory operand, got $ -/
#guard_msgs in
#check ⸨prog| xorq %rax, $1 ⸩

/-- error: can't have two memory operands -/
#guard_msgs in
#check ⸨prog| movq sym, sym2 ⸩

/-- error: absolute branch targets are not supported -/
#guard_msgs in
#check ⸨prog| jmp 0x10 ⸩

/-- error: <input>:1:4: unexpected end of input -/
#guard_msgs in
#check elabX64% "addq"

/-- error: <input>:3:2: expected ',' -/
#guard_msgs in
#check elabX64% "
  addq %rax
  cmpq $10, %rax
"

/-- error: type error: w64 != w32 -/
#guard_msgs in
#check ⸨prog| movq %eax, %rbx ⸩

/-- error: invalid scale 3, must be 1, 2, 4, or 8 -/
#guard_msgs in
#check ⸨prog| movq (%rax, %rcx, 3), %rbx ⸩

/-- error: <input>:1:16: unexpected element; expected ';' -/
#guard_msgs in
#check elabX64% "movq %rax, %rbx garbage"

/-- error: <input>:1:9: unexpected element; expected ';' -/
#guard_msgs in
#check elabX64% "shlq %rcx, %rax"

/-- error: <input>:1:0: expected end of input -/
#guard_msgs in
#check elabX64% "foo\n:"

end error_reporting

section syntax_cat_and_include

/--
info: [Directive.label "loop", Directive.instr (regular Width.W64 Width.W64 (Operation.add ↑(low Reg64.rax Width.W64) ↑↑1)),
  Directive.instr (regular Width.W64 Width.W64 (Operation.jcc CondCode.nz "loop"))] : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog|
  loop:
    addq $1, %rax
    jnz loop
⸩

/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.nop 1))] : List _root_.Directive
-/
#guard_msgs in
#check include_x64 "Kraken/X64/Test/asm/test_nop.S"

/--
info: [Directive.label "aa.1.aa.1",
  Directive.instr
    (regular Width.W64 Width.W64
      (Operation.jmp
        (RelRegOrMem.rel ((↑".L.str.1.llvm.12345").sub ConstExpr.after_current_instruction))))] : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog|
  aa.1.aa.1:
    jmp .L.str.1.llvm.12345
⸩

/--
info: Directive.instr
  (regular Width.W64 Width.W64 (Operation.add ↑(low Reg64.rax Width.W64) ↑↑1)) : Kraken.Directive Instr ConstExpr
-/
#guard_msgs in
#check ⸨dir| addq $1, %rax ⸩

/--
info: { directive := Directive.instr (regular Width.W64 Width.W64 (Operation.add ↑(low Reg64.rax Width.W64) ↑↑1)),
  size := Layout.size Instr ConstExpr 1 } : Sized _root_.Directive
-/
#guard_msgs (whitespace := lax) in
variable [Kraken.Layout Instr ConstExpr] in
#check ⸨dir 1 | addq $1, %rax ⸩

end syntax_cat_and_include

section antiquotations

variable {w : Width} (r : Reg w) (q : Reg .W64) (r64 : Reg64) (v : AvxReg .W256)

-- Test: an antiquoted register decides the width of its instruction, which may be a variable
/-- info: [Directive.instr (regular Width.W64 w (Operation.add ↑r ↑↑2))] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| add $2, %❰r❱ ⸩

-- Test: antiquoted and concrete registers unify
/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.mov ↑q ↑↑(low Reg64.rax Width.W64)))] : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| mov %rax, %❰q❱ ⸩

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
#check ⸨prog| addq $1, %❰r❱ ⸩

/-- error: type error: w != w32 -/
#guard_msgs in
#check ⸨prog| add %❰r❱, %eax ⸩

-- Test: in address positions, antiquotations denote `Reg64`
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rcx Width.W64)
        ↑↑{ base := some (RegOrRip.reg r64), idx := some { reg := Reg64.rax, scale := Width.W32 },
              disp := ↑8 }))] : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| mov 8(%❰r64❱, %rax, 4), %rcx ⸩

-- Test: AVX registers
/--
info: [Directive.instr
    (avx Width.W64 AvxWidth.W256
      (AvxOperation.vmovups ↑v ↑{ base := some (RegOrRip.reg Reg64.rax), idx := none }))] : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| vmovups (%rax), %❰v❱ ⸩

-- Test: a width that no operand or suffix determines is an error
/-- error: could not infer operand width -/
#guard_msgs in
#check ⸨prog| add $1, (%rax) ⸩

-- Test: the source of a widening move must be narrower than its destination
/-- error: source width w64 must be narrower than destination width w16 -/
#guard_msgs in
#check ⸨prog| movsx %rax, %bx ⸩

-- Test: antiquotations for operands, instructions and directives
variable (o : Operand .W32) (rm : RegOrMem w) (av : AvxRegOrMem .W128) (rt : RelRegOrMem) (i : Instr) (d : Directive)

/-- info: [Directive.instr (regular Width.W64 Width.W32 (Operation.add (↑(low Reg64.rax Width.W32)) o))] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| add ❰o❱, %eax ⸩

/-- info: [Directive.instr (regular Width.W64 w (Operation.inc rm))] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| inc ❰rm❱ ⸩

/--
info: [Directive.instr
    (avx Width.W64 AvxWidth.W128 (AvxOperation.movaps (↑(AvxReg.xmm RegMm.mm1)) av))] : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| movaps ❰av❱, %xmm1 ⸩

/-- info: [Directive.instr (regular Width.W64 Width.W64 (Operation.jmp rt))] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| jmp ❰rt❱ ⸩

/-- info: [Directive.instr i, d, Directive.instr (regular Width.W64 Width.W64 Operation.ret)] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| ❰.instr i❱; ❰d❱; ret ⸩

/-- info: [Directive.label "foo", Directive.instr (regular Width.W64 Width.W64 Operation.ret)] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| ❰.label "foo"❱; ❰.instr <| .regular .W64 .W64 .ret❱ ⸩

-- Test: label antiquotations (`x64_ident`)
variable (lbl : Kraken.Label)

/-- info: [Directive.label lbl, Directive.instr (regular Width.W64 Width.W64 Operation.ret)] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| ❰lbl❱: ret ⸩

/-- info: [Directive.instr (regular Width.W64 Width.W64 (Operation.jcc CondCode.z lbl))] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| jz ❰lbl❱ ⸩

/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.mov ↑(low Reg64.rax Width.W64) ↑↑lbl))] : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| movq $❰lbl❱, %rax ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W64 (Operation.mov ↑(low Reg64.rax Width.W64) ↑((↑lbl).add ↑8)))] : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| movq $❰lbl❱+8, %rax ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W64 (Operation.mov ↑(low Reg64.rax Width.W64) ↑((↑lbl).sub ↑8)))] : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| movq $❰lbl❱-8, %rax ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.lea (low Reg64.rax Width.W64)
        { base := some RegOrRip.rip, idx := none,
          disp := (↑lbl).sub ConstExpr.after_current_instruction }))] : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| leaq ❰lbl❱(%rip), %rax ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rax Width.W64)
        ↑↑{ base := some RegOrRip.rip, idx := none,
              disp := ((↑lbl).add ↑8).sub ConstExpr.after_current_instruction }))] : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| movq ❰lbl❱+8(%rip), %rax ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rdx Width.W64)
        ↑↑{ base := some (RegOrRip.reg Reg64.rax), idx := some { reg := Reg64.rcx, scale := Width.W32 },
              disp := (↑lbl).sub ↑8 }))] : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| movq ❰lbl❱-8(%rax, %rcx, 4), %rdx ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rax Width.W64)
        ↑↑{ base := none, idx := none, disp := (↑lbl).add ↑8 }))] : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| movq ❰lbl❱+8, %rax ⸩

/-- info: [Directive.word 4 ((↑lbl).sub ↑"start")] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| .long ❰lbl❱ - start ⸩

/--
error: Type mismatch
  r
has type
  Reg w
but is expected to have type
  Kraken.Label
-/
#guard_msgs in
#check ⸨prog| jz ❰r❱ ⸩

-- Test: `Int64` / `ConstExpr` antiquotations (`x64_const` and `x64_operand`)
variable (imm : Int64) (ce : ConstExpr)

/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.mov ↑(low Reg64.rax Width.W64) ↑↑imm))] : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| mov $❰imm❱, %rax ⸩

/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.mov ↑(low Reg64.rax Width.W64) ↑↑imm))] : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| mov ❰imm❱, %rax ⸩

/--
info: [Directive.instr (regular Width.W64 Width.W32 (Operation.mov ↑(low Reg64.rax Width.W32) ↑↑imm))] : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| mov ❰imm❱, %eax ⸩

/-- info: [Directive.instr (regular Width.W64 Width.W64 (Operation.push ↑↑imm))] : List _root_.Directive -/
#guard_msgs in
#check ⸨prog| push ❰imm❱ ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rax Width.W64)
        ↑↑{ base := some (RegOrRip.reg Reg64.rsp), idx := none, disp := ↑imm }))] : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| movq ❰imm❱(%rsp), %rax ⸩

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rax Width.W64)
        ↑↑{ base := some RegOrRip.rip, idx := none, disp := ↑imm }))] : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| movq ❰imm❱(%rip), %rax ⸩

/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.mov ↑(low Reg64.rax Width.W64) ↑ce))] : List _root_.Directive
-/
#guard_msgs in
#check ⸨prog| mov $❰ce❱, %rax ⸩

end antiquotations

-- Test: flag control instructions (`cld`/`std`), string parser and `⸨prog| ⸩` syntax
/--
info: [Directive.instr (regular Width.W64 Width.W64 Operation.cld),
  Directive.instr (regular Width.W64 Width.W64 Operation.std)] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog|
cld
std
⸩

/--
info: [Directive.instr (regular Width.W64 Width.W64 Operation.cld),
  Directive.instr (regular Width.W64 Width.W64 Operation.std)] : List _root_.Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| cld; std ⸩

section sse_and_vex

#guard [
  ⸨prog|
movdqu (%rsp), %xmm0
movdqa %xmm1, 16(%rsp)
paddd (%rax), %xmm2
pshufb %xmm3, %xmm4
⸩,
  ⸨prog|
pshufd $0x1b, %xmm5, %xmm6
palignr $8, (%rsp), %xmm7
pblendw $0xf0, %xmm8, %xmm9
⸩,
  ⸨prog|
vmovdqu (%rsp), %ymm0
vmovd %eax, %xmm0
vmovd %xmm1, 16(%rsp)
vmovq %rax, %xmm0
vmovq %xmm3, %xmm2
vmovq %xmm1, 24(%rsp)
vzeroupper
⸩,
  ⸨prog|
seto %al
setno %bl
sets %cl
setns %dl
setp %sil
setnp %dil
setge %r8b
setg %r9b
⸩
].all agreesWithCombinatorParser

/-- error: vmovd takes no two xmm operands -/
#guard_msgs in
#check ⸨prog| vmovd %xmm0, %xmm1 ⸩

end sse_and_vex

end Tests

