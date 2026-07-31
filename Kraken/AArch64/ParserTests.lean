/-
  ParserAArch64 Tests
  Uses #guard_msgs to verify AArch64 parser output against expected results.
-/

import Kraken.AArch64.Parser

section Tests
open Kraken.AArch64.Parser

-- Test: Simple LDR with base register
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.LDR (↑↑XReg.X0 Width.W64)
          ↑{ base := ↑XRegOrSp.SP Width.W64, off := ↑{ imm := ↑0, index := none } } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ldr x0, [sp]")

-- Test: Simple STR with 32-bit register and immediate offset
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation :=
        Operation.STR (↑↑XReg.X0 Width.W32)
          { base := ↑↑XReg.X1 Width.W64, off := ↑{ imm := ↑8, index := none } } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("str w0, [x1, #8]")

-- Test: Pre-indexed memory addressing
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.LDR (↑↑XReg.X1 Width.W64)
          ↑{ base := ↑XRegOrSp.SP Width.W64, off := ↑{ imm := ↑(-16), index := some Index.Pre } } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ldr x1, [sp, #-16]!")

-- Test: Post-indexed memory addressing
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.STR (↑↑XReg.X2 Width.W64)
          { base := ↑↑XReg.X1 Width.W64, off := ↑{ imm := ↑16, index := some Index.Post } } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("str x2, [x1], #16")

-- Test: Register offset with extension and shift in LDR
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.LDR (↑↑XReg.X0 Width.W64)
          ↑{ base := ↑↑XReg.X1 Width.W64,
              off :=
                ↑{ reg := { w := Width.W64, reg := ↑↑XReg.X2 Width.W64 },
                    ext := { type := MemExtendType.UXTX, amount := MemExtendAmount.E3 } } } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ldr x0, [x1, x2, lsl #3]")

-- Test: ADD_e with immediate
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ADD_e (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          ↑{ imm := ↑42, shift := ImmShift.S0 } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("add x0, x1, #42")

-- Test: ADD_e with immediate and shifted immediate (lsl #12)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ADD_e (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          ↑{ imm := ↑42, shift := ImmShift.S12 } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("add x0, x1, #42, lsl #12")

-- Test: ADD_e with immediate and shifted immediate (lsl #0)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ADD_e (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          ↑{ imm := ↑10, shift := ImmShift.S0 } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("add x0, x1, #10, lsl #0")

-- Test: ADD_e with SP as destination
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ADD_e (↑XRegOrSp.SP Width.W64) (↑XRegOrSp.SP Width.W64)
          ↑{ imm := ↑16, shift := ImmShift.S0 } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("add sp, sp, #16")

-- Test: ADD_e with binary immediate (#0b1010)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ADD_e (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          ↑{ imm := ↑10, shift := ImmShift.S0 } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("add x0, x1, #0b1010")

-- Test: LDR with flexible sign ordering (-#16)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.LDR (↑↑XReg.X1 Width.W64)
          ↑{ base := ↑XRegOrSp.SP Width.W64, off := ↑{ imm := ↑(-16), index := some Index.Pre } } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ldr x1, [sp, -#16]!")

-- Test: ADD_s with shifted register (lsl #2)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ADD_s (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          { reg := ↑↑XReg.X2 Width.W64, amount := 2, shift := ShiftType.LSL } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("add x0, x1, x2, lsl #2")

-- Test: ADD_e with extended register (uxtw #2)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ADD_e (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          ↑{ reg := { w := Width.W32, reg := ↑↑XReg.X2 Width.W32 },
              ext := { type := ExtendType.UXTW, amount := ExtendAmount.E2 } } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("add x0, x1, w2, uxtw #2")

-- Test: ADDS_e with immediate
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ADDS_e (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          ↑{ imm := ↑42, shift := ImmShift.S0 } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("adds x0, x1, #42")

-- Test: ADDS_s with shifted register (lsl #2)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ADDS_s (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          { reg := ↑↑XReg.X2 Width.W64, amount := 2, shift := ShiftType.LSL } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("adds x0, x1, x2, lsl #2")

-- Test: CMN with immediate (alias for adds xzr, x1, #10)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ADDS_e (↑XRegOrXzr.XZR Width.W64) (↑↑XReg.X1 Width.W64)
          ↑{ imm := ↑10, shift := ImmShift.S0 } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("cmn x1, #10")

-- Test: SUB_e with immediate
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.SUB_e (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          ↑{ imm := ↑5, shift := ImmShift.S0 } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("sub x0, x1, #5")

-- Test: SUBS_e with immediate
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.SUBS_e (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          ↑{ imm := ↑5, shift := ImmShift.S0 } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("subs x0, x1, #5")

-- Test: CMP with shifted register (alias for subs xzr, x1, x2)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.SUBS_s (↑XRegOrXzr.XZR Width.W64) (↑↑XReg.X1 Width.W64)
          { reg := ↑↑XReg.X2 Width.W64, amount := 0, shift := ShiftType.LSL } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("cmp x1, x2")

-- Test: AND_s with shifted register (lsr #4)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.AND_s (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          { reg := ↑↑XReg.X2 Width.W64, amount := 4, shift := ShiftType.LSR } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("and x0, x1, x2, lsr #4")

-- Test: ORR_s 32-bit without shift
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation :=
        Operation.ORR_s (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32)
          { reg := ↑↑XReg.X2 Width.W32, amount := 0, shift := ShiftType.LSL } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("orr w0, w1, w2")

-- Test: ANDS_s 64-bit
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ANDS_s (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          { reg := ↑↑XReg.X2 Width.W64, amount := 0, shift := ShiftType.LSL } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ands x0, x1, x2")

-- Test: ORN_s 64-bit
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ORN_s (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          { reg := ↑↑XReg.X2 Width.W64, amount := 0, shift := ShiftType.LSL } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("orn x0, x1, x2")

-- Test: EOR_s 64-bit
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.EOR_s (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          { reg := ↑↑XReg.X2 Width.W64, amount := 0, shift := ShiftType.LSL } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("eor x0, x1, x2")

-- Test: BIC_s 64-bit
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.BIC_s (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          { reg := ↑↑XReg.X2 Width.W64, amount := 0, shift := ShiftType.LSL } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("bic x0, x1, x2")

-- Test: TST 64-bit (alias for ANDS_s XZR, x1, x2)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ANDS_s (↑XRegOrXzr.XZR Width.W64) (↑↑XReg.X1 Width.W64)
          { reg := ↑↑XReg.X2 Width.W64, amount := 0, shift := ShiftType.LSL } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("tst x1, x2")

-- Test: NEG 64-bit (alias for SUB_s x0, xzr, x1)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.SUB_s (↑↑XReg.X0 Width.W64) (↑XRegOrXzr.XZR Width.W64)
          { reg := ↑↑XReg.X1 Width.W64, amount := 0, shift := ShiftType.LSL } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("neg x0, x1")

-- Test: NEGS 64-bit (alias for SUBS_s x0, xzr, x1)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.SUBS_s (↑↑XReg.X0 Width.W64) (↑XRegOrXzr.XZR Width.W64)
          { reg := ↑↑XReg.X1 Width.W64, amount := 0, shift := ShiftType.LSL } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("negs x0, x1")

-- Test: LSL 64-bit (alias for LSLV)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.LSLV (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("lsl x0, x1, x2")

-- Test: LSLV 32-bit
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation := Operation.LSLV (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) (↑↑XReg.X2 Width.W32) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("lslv w0, w1, w2")

-- Test: LSR 64-bit (alias for LSRV)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.LSRV (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("lsr x0, x1, x2")

-- Test: ASR 64-bit (alias for ASRV)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.ASRV (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("asr x0, x1, x2")

-- Test: ROR 64-bit (alias for RORV)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.RORV (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ror x0, x1, x2")


-- Test: ADC 64-bit
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.ADC (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("adc x0, x1, x2")

-- Test: ADCS 32-bit
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation := Operation.ADCS (↑↑XReg.X3 Width.W32) (↑↑XReg.X4 Width.W32) (↑↑XReg.X5 Width.W32) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("adcs w3, w4, w5")

-- Test: SBC 64-bit
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.SBC (↑↑XReg.X6 Width.W64) (↑↑XReg.X7 Width.W64) (↑↑XReg.X8 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("sbc x6, x7, x8")

-- Test: SBCS 32-bit
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation :=
        Operation.SBCS (↑↑XReg.X9 Width.W32) (↑↑XReg.X10 Width.W32) (↑↑XReg.X11 Width.W32) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("sbcs w9, w10, w11")

-- Test: MADD 64-bit
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.MADD (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64)
          (↑↑XReg.X3 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("madd x0, x1, x2, x3")

-- Test: MADD 32-bit
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation :=
        Operation.MADD (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) (↑↑XReg.X2 Width.W32)
          (↑↑XReg.X3 Width.W32) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("madd w0, w1, w2, w3")

-- Test: MUL 64-bit (alias for madd x0, x1, x2, xzr)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.MADD (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64)
          (↑XRegOrXzr.XZR Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("mul x0, x1, x2")

-- Test: MUL 32-bit (alias for madd w0, w1, w2, wzr)
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation :=
        Operation.MADD (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) (↑↑XReg.X2 Width.W32)
          (↑XRegOrXzr.XZR Width.W32) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("mul w0, w1, w2")

-- Test: MSUB 64-bit
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.MSUB (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64)
          (↑↑XReg.X3 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("msub x0, x1, x2, x3")

-- Test: MSUB 32-bit
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation :=
        Operation.MSUB (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) (↑↑XReg.X2 Width.W32)
          (↑↑XReg.X3 Width.W32) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("msub w0, w1, w2, w3")

-- Test: MNEG 64-bit (alias for msub x0, x1, x2, xzr)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.MSUB (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64)
          (↑XRegOrXzr.XZR Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("mneg x0, x1, x2")

-- Test: MNEG 32-bit (alias for msub w0, w1, w2, wzr)
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation :=
        Operation.MSUB (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) (↑↑XReg.X2 Width.W32)
          (↑XRegOrXzr.XZR Width.W32) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("mneg w0, w1, w2")


-- Test: SMULH 64-bit
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.SMULH (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("smulh x0, x1, x2")

-- Test: UMULH 64-bit
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.UMULH (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("umulh x0, x1, x2")

-- Test: ADR with label
/--
info: [Directive.instr
    { operation_size := Width.W64, operation := Operation.ADR (↑↑XReg.X0 Width.W64) ↑"main" }] : List Directive
-/
#guard_msgs in
#check parseAArch64("adr x0, main")

-- Test: ADR with immediate
/--
info: [Directive.instr
    { operation_size := Width.W64, operation := Operation.ADR (↑↑XReg.X1 Width.W64) ↑4096 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("adr x1, #4096")

-- Test: ADRP with label
/--
info: [Directive.instr
    { operation_size := Width.W64, operation := Operation.ADRP (↑↑XReg.X0 Width.W64) ↑"main" }] : List Directive
-/
#guard_msgs in
#check parseAArch64("adrp x0, main")

-- Test: ADRP with immediate
/--
info: [Directive.instr
    { operation_size := Width.W64, operation := Operation.ADRP (↑↑XReg.X1 Width.W64) ↑16384 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("adrp x1, #0x4000")

-- Test: ADRP with :pg_hi21: modifier
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.ADRP (↑↑XReg.X0 Width.W64) (↑"main").pg_hi21 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("adrp x0, :pg_hi21:main")

-- Test: ADD_e with :lo12: modifier on label
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ADD_e (↑↑XReg.X0 Width.W64) (↑↑XReg.X0 Width.W64)
          ↑{ imm := (↑"main").lo12, shift := ImmShift.S0 } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("add x0, x0, :lo12:main")

-- Test: LDR with #:lo12: modifier on memory offset
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.LDR (↑↑XReg.X1 Width.W64)
          ↑{ base := ↑↑XReg.X0 Width.W64, off := ↑{ imm := (↑"main").lo12, index := none } } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ldr x1, [x0, #:lo12:main]")

-- Test: NOP
/--
info: [Directive.instr { operation_size := Width.W64, operation := Operation.NOP }] : List Directive
-/
#guard_msgs in
#check parseAArch64("nop")

-- Test: Multi-line program with label
/--
info: [Directive.label "main",
  Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.LDR (↑↑XReg.X1 Width.W64) ↑{ base := ↑XRegOrSp.SP Width.W64, off := ↑{ imm := ↑0, index := none } } },
  Directive.instr
    { operation_size := Width.W64,
      operation := Operation.ADD_e (↑↑XReg.X1 Width.W64) (↑↑XReg.X1 Width.W64) ↑{ imm := ↑16, shift := ImmShift.S0 } },
  Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.STR (↑↑XReg.X1 Width.W64)
          { base := ↑XRegOrSp.SP Width.W64, off := ↑{ imm := ↑0, index := none } } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("
main:
  ldr x1, [sp]
  add x1, x1, #16
  str x1, [sp]
")

-- Test: LDUR and STUR explicit mnemonics
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.LDUR (↑↑XReg.X0 Width.W64) { base := ↑↑XReg.X1 Width.W64, imm := ↑(-8) } },
  Directive.instr
    { operation_size := Width.W32,
      operation := Operation.STUR (↑↑XReg.X2 Width.W32) { base := ↑↑XReg.X3 Width.W64, imm := ↑13 } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("
  ldur x0, [x1, #-8]
  stur w2, [x3, #13]
")

-- Test: LDR/STR automatic conversion to LDUR/STUR for negative or unaligned offsets
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.LDUR (↑↑XReg.X0 Width.W64) { base := ↑↑XReg.X1 Width.W64, imm := ↑(-8) } },
  Directive.instr
    { operation_size := Width.W64,
      operation := Operation.LDUR (↑↑XReg.X0 Width.W64) { base := ↑↑XReg.X1 Width.W64, imm := ↑13 } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("
  ldr x0, [x1, #-8]
  ldr x0, [x1, #13]
")

-- Test: ADD_s with XZR destination
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ADD_s (↑XRegOrXzr.XZR Width.W64) (↑↑XReg.X1 Width.W64)
          { reg := ↑↑XReg.X2 Width.W64, amount := 0, shift := ShiftType.LSL } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("add xzr, x1, x2")

-- Test: Logical instruction with ROR shift
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ORR_s (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          { reg := ↑↑XReg.X2 Width.W64, amount := 4, shift := ShiftType.ROR } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("orr x0, x1, x2, ror #4")

-- Test: Conditional select instructions and aliases
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.CSEL (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64) CondCode.EQ },
  Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.CSINV (↑↑XReg.X3 Width.W64) (↑XRegOrXzr.XZR Width.W64) (↑XRegOrXzr.XZR Width.W64) CondCode.EQ },
  Directive.instr
    { operation_size := Width.W32,
      operation :=
        Operation.CSINC (↑↑XReg.X4 Width.W32) (↑↑XReg.X5 Width.W32) (↑↑XReg.X5 Width.W32)
          CondCode.CS }] : List Directive
-/
#guard_msgs in
#check parseAArch64("
  csel x0, x1, x2, eq
  csetm x3, ne
  cinc w4, w5, lo
")

-- Test: Logical immediate instructions and TST immediate alias
/--
info: [Directive.instr
    { operation_size := Width.W64, operation := Operation.AND_i (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) ↑255 },
  Directive.instr
    { operation_size := Width.W32, operation := Operation.ORR_i (↑↑XReg.X2 Width.W32) (↑↑XReg.X3 Width.W32) ↑255 },
  Directive.instr
    { operation_size := Width.W64, operation := Operation.EOR_i (↑XRegOrSp.SP Width.W64) (↑↑XReg.X4 Width.W64) ↑255 },
  Directive.instr
    { operation_size := Width.W32, operation := Operation.ANDS_i (↑↑XReg.X5 Width.W32) (↑↑XReg.X6 Width.W32) ↑255 },
  Directive.instr
    { operation_size := Width.W64,
      operation := Operation.ANDS_i (↑XRegOrXzr.XZR Width.W64) (↑↑XReg.X7 Width.W64) ↑255 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("
  and x0, x1, #255
  orr w2, w3, #255
  eor sp, x4, #255
  ands w5, w6, #255
  tst x7, #255
")

-- Test: LDP with 64-bit registers and signed immediate offset
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.LDP (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          { base := ↑XRegOrSp.SP Width.W64, off := ↑{ imm := ↑16, index := none } } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ldp x0, x1, [sp, #16]")

-- Test: STP with 32-bit registers and pre-indexed offset
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation :=
        Operation.STP (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32)
          { base := ↑XRegOrSp.SP Width.W64, off := ↑{ imm := ↑(-32), index := some Index.Pre } } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("stp w0, w1, [sp, #-32]!")

-- Test: STP with zero registers and post-indexed offset
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.STP (↑XRegOrXzr.XZR Width.W64) (↑XRegOrXzr.XZR Width.W64)
          { base := ↑XRegOrSp.SP Width.W64, off := ↑{ imm := ↑32, index := some Index.Post } } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("stp xzr, xzr, [sp], #32")

-- Test: B with label
/--
info: [Directive.instr { operation_size := Width.W64, operation := Operation.B ↑"main" }] : List Directive
-/
#guard_msgs in
#check parseAArch64("b main")

-- Test: B with immediate offset
/--
info: [Directive.instr { operation_size := Width.W64, operation := Operation.B ↑16 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("b #16")

-- Test: B.eq with label
/--
info: [Directive.instr { operation_size := Width.W64, operation := Operation.B_cond CondCode.EQ ↑"loop" }] : List Directive
-/
#guard_msgs in
#check parseAArch64("b.eq loop")

-- Test: B.ne with label
/--
info: [Directive.instr { operation_size := Width.W64, operation := Operation.B_cond CondCode.NE ↑"exit" }] : List Directive
-/
#guard_msgs in
#check parseAArch64("b.ne exit")

-- Test: BL with label
/--
info: [Directive.instr { operation_size := Width.W64, operation := Operation.BL ↑"foo" }] : List Directive
-/
#guard_msgs in
#check parseAArch64("bl foo")

-- Test: BLR with register
/--
info: [Directive.instr { operation_size := Width.W64, operation := Operation.BLR (↑↑XReg.X16 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("blr x16")

-- Test: BR with register
/--
info: [Directive.instr { operation_size := Width.W64, operation := Operation.BR (↑↑XReg.X30 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("br x30")

-- Test: RET without operand (defaults to X30)
/--
info: [Directive.instr { operation_size := Width.W64, operation := Operation.RET (↑↑XReg.X30 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ret")

-- Test: RET with explicit register (x19)
/--
info: [Directive.instr { operation_size := Width.W64, operation := Operation.RET (↑↑XReg.X19 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ret x19")

-- Test: RET with lr alias
/--
info: [Directive.instr { operation_size := Width.W64, operation := Operation.RET (↑↑XReg.X30 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ret lr")

-- Test: RET followed by line comment //
/--
info: [Directive.instr { operation_size := Width.W64, operation := Operation.RET (↑↑XReg.X30 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ret // return to caller")

-- Test: CBZ 64-bit
/--
info: [Directive.instr
    { operation_size := Width.W64, operation := Operation.CBZ (↑↑XReg.X0 Width.W64) ↑"target" }] : List Directive
-/
#guard_msgs in
#check parseAArch64("cbz x0, target")

-- Test: CBNZ 32-bit
/--
info: [Directive.instr
    { operation_size := Width.W32, operation := Operation.CBNZ (↑↑XReg.X1 Width.W32) ↑"loop" }] : List Directive
-/
#guard_msgs in
#check parseAArch64("cbnz w1, loop")

-- Test: TBZ 64-bit
/--
info: [Directive.instr
    { operation_size := Width.W64, operation := Operation.TBZ (↑↑XReg.X2 Width.W64) 5 ↑"label" }] : List Directive
-/
#guard_msgs in
#check parseAArch64("tbz x2, #5, label")

-- Test: TBNZ 32-bit
/--
info: [Directive.instr
    { operation_size := Width.W32, operation := Operation.TBNZ (↑↑XReg.X3 Width.W32) 31 ↑"exit" }] : List Directive
-/
#guard_msgs in
#check parseAArch64("tbnz w3, #31, exit")

section error_reporting

/-- error: line 1: unknown register or xzr: x31 -/
#guard_msgs in
#check parseAArch64("ldr x31, [sp]")

/-- error: line 1: expected w64 register, got w32 -/
#guard_msgs in
#check parseAArch64("ldr x0, [w1]")

/-- error: line 1: invalid memory extension shift amount 1 for width w64 -/
#guard_msgs in
#check parseAArch64("ldr x0, [x1, x2, lsl #1]")

/-- error: line 1: unexpected trailing characters on line -/
#guard_msgs in
#check parseAArch64("nop extra_tokens")

/-- error: line 1: immediate 5000 out of range [0, 4095] -/
#guard_msgs in
#check parseAArch64("add x0, x1, #5000")

/-- error: line 1: invalid immediate shift for add: 1 (must be 0 or 12) -/
#guard_msgs in
#check parseAArch64("add x0, x1, #10, lsl #1")

/-- error: line 1: invalid extend amount: 65 -/
#guard_msgs in
#check parseAArch64("add x0, x1, x2, lsl #65")

/-- error: line 1: invalid extend amount: 33 -/
#guard_msgs in
#check parseAArch64("add w0, w1, w2, lsl #33")

/-- error: line 1: unknown extension type: ror -/
#guard_msgs in
#check parseAArch64("add x0, x1, x2, ror #4")

/-- error: line 1: pre-indexed offset 300 out of range [-256, 255] -/
#guard_msgs in
#check parseAArch64("ldr x1, [sp, #300]!")

/-- error: line 1: post-indexed offset -300 out of range [-256, 255] -/
#guard_msgs in
#check parseAArch64("str x2, [x1], #-300")

/-- error: line 1: offset 257 is neither a valid scaled offset [0, 32760] (multiple of 8) nor a valid unscaled offset [-256, 255] -/
#guard_msgs in
#check parseAArch64("ldr x0, [x1, #257]")

/-- error: line 1: condition not satisfied -/
#guard_msgs in
#check parseAArch64("add xzr, x1, #42")

/-- error: line 1: pair offset 600 out of range [-512, 504] or not a multiple of 8 -/
#guard_msgs in
#check parseAArch64("ldp x0, x1, [sp, #600]")

/-- error: line 1: pair offset 13 out of range [-512, 504] or not a multiple of 8 -/
#guard_msgs in
#check parseAArch64("ldp x0, x1, [sp, #13]")

/-- error: line 1: register offsets are not supported for ldp/stp instructions -/
#guard_msgs in
#check parseAArch64("ldp x0, x1, [sp, x2]")

/-- error: line 1: expected w64 register, got w32 -/
#guard_msgs in
#check parseAArch64("ldp x0, w1, [sp, #16]")

/-- error: line 1: unpredictable: identical destination registers in ldp instruction -/
#guard_msgs in
#check parseAArch64("ldp x0, x0, [sp, #16]")

/-- error: line 1: relocation modifiers and labels cannot be shifted with lsl in immediate operands -/
#guard_msgs in
#check parseAArch64("add x1, x1, :lo12:main, lsl #12")

/-- error: line 1: relocation modifiers and labels cannot be shifted with lsl in immediate operands -/
#guard_msgs in
#check parseAArch64("add x1, x1, :lo12:main, lsl #0")

/-- error: line 1: unpredictable: writeback base register is also a transfer register -/
#guard_msgs in
#check parseAArch64("ldp x0, x1, [x0, #16]!")

/-- error: line 1: unpredictable: writeback base register is also a transfer register -/
#guard_msgs in
#check parseAArch64("stp x0, x1, [x0, #16]!")

/-- error: line 1: sp/wsp not allowed in shifted register instruction (xzr expected) -/
#guard_msgs in
#check parseAArch64("and sp, x1, x2")

/-- error: line 1: expected w64 register, got w32 -/
#guard_msgs in
#check parseAArch64("adr w0, main")

/-- error: line 1: adr offset 0x200000 out of range [-0x100000, 0xfffff] -/
#guard_msgs in
#check parseAArch64("adr x0, #0x200000")

/-- error: line 1: expected w64 register, got w32 -/
#guard_msgs in
#check parseAArch64("adrp w0, main")

/-- error: line 1: adrp offset 0x1004 not page aligned (must be multiple of 0x1000) -/
#guard_msgs in
#check parseAArch64("adrp x0, #0x1004")

/-- error: line 1: adrp offset 0x200000000 out of range [-0x100000000, 0xfffff000] -/
#guard_msgs in
#check parseAArch64("adrp x0, #0x200000000")

/-- error: line 1: expected w64 register, got w32 -/
#guard_msgs in
#check parseAArch64("br w0")

/-- error: line 1: expected w64 register, got w32 -/
#guard_msgs in
#check parseAArch64("ret w0")

/-- error: line 1: unknown condition code in branch instruction: b.invalid -/
#guard_msgs in
#check parseAArch64("b.invalid main")

/-- error: line 1: b offset 0x8000004 out of range [-0x8000000, 0x7fffffc] -/
#guard_msgs in
#check parseAArch64("b #0x8000004")

/-- error: line 1: b.cond offset 0x100000 out of range [-0x100000, 0xffffc] -/
#guard_msgs in
#check parseAArch64("b.eq #0x100000")

/-- error: line 1: cbz offset 0x200000 out of range [-0x100000, 0xffffc] or not a multiple of 4 -/
#guard_msgs in
#check parseAArch64("cbz x0, #0x200000")

/-- error: line 1: tbz bit position 32 out of range [0, 31] for 32-bit instruction -/
#guard_msgs in
#check parseAArch64("tbz w0, #32, target")

/-- error: line 1: tbz offset 0x10000 out of range [-0x8000, 0x7fc] or not a multiple of 4 -/
#guard_msgs in
#check parseAArch64("tbz x0, #10, #0x10000")

/-- error: line 1: invalid logical immediate: 0x1f4 -/
#guard_msgs in
#check parseAArch64("and x0, x1, #500")

/-- error: line 1: invalid logical immediate: 0x0 -/
#guard_msgs in
#check parseAArch64("orr x0, x1, #0")

/-- error: line 1: invalid logical immediate: -0x1 -/
#guard_msgs in
#check parseAArch64("eor x0, x1, #-1")

end error_reporting

end Tests
