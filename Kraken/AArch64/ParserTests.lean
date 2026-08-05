/-
  ParserAArch64 Tests
  Uses #guard_msgs to verify AArch64 parser output against expected results.
-/

import Kraken.AArch64.Parser

section Tests
open Kraken.AArch64.Parser

-- ============================================================================
-- 1. Memory Access: Loads and Stores (LDR, STR, LDUR, STUR, LDP, STP)
-- ============================================================================

-- Test: LDR 64-bit with base register only
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.LDR (↑↑XReg.X0 Width.W64)
          ↑{ base := ↑XRegOrSp.SP Width.W64, off := ↑{ imm := ↑0, index := none } } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ldr x0, [sp]")

-- Test: STR 32-bit with unsigned scaled immediate offset
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation :=
        Operation.STR (↑↑XReg.X0 Width.W32)
          { base := ↑↑XReg.X1 Width.W64, off := ↑{ imm := ↑8, index := none } } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("str w0, [x1, #8]")

-- Test: LDR 64-bit with pre-indexed immediate offset
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.LDR (↑↑XReg.X1 Width.W64)
          ↑{ base := ↑XRegOrSp.SP Width.W64, off := ↑{ imm := ↑(-16), index := some Index.Pre } } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ldr x1, [sp, #-16]!")

-- Test: STR 64-bit with post-indexed immediate offset
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.STR (↑↑XReg.X2 Width.W64)
          { base := ↑↑XReg.X1 Width.W64, off := ↑{ imm := ↑16, index := some Index.Post } } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("str x2, [x1], #16")

-- Test: LDR 64-bit with register offset, extension, and shift
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

-- Test: LDUR 64-bit unscaled immediate offset
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.LDUR (↑↑XReg.X0 Width.W64) { base := ↑↑XReg.X1 Width.W64, imm := ↑(-8) } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ldur x0, [x1, #-8]")

-- Test: STUR 32-bit unscaled immediate offset
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation := Operation.STUR (↑↑XReg.X2 Width.W32) { base := ↑↑XReg.X3 Width.W64, imm := ↑13 } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("stur w2, [x3, #13]")

-- Test: LDR automatic conversion to LDUR for negative unscaled offset
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.LDUR (↑↑XReg.X0 Width.W64) { base := ↑↑XReg.X1 Width.W64, imm := ↑(-8) } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ldr x0, [x1, #-8]")

-- Test: LDR automatic conversion to LDUR for unaligned unscaled offset
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.LDUR (↑↑XReg.X0 Width.W64) { base := ↑↑XReg.X1 Width.W64, imm := ↑13 } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ldr x0, [x1, #13]")

-- Test: LDP 64-bit load pair with signed immediate offset
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.LDP (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          { base := ↑XRegOrSp.SP Width.W64, off := ↑{ imm := ↑16, index := none } } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ldp x0, x1, [sp, #16]")

-- Test: STP 32-bit store pair with pre-indexed offset
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation :=
        Operation.STP (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32)
          { base := ↑XRegOrSp.SP Width.W64, off := ↑{ imm := ↑(-32), index := some Index.Pre } } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("stp w0, w1, [sp, #-32]!")

-- Test: STP 64-bit store pair with zero registers and post-indexed offset
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.STP (↑XRegOrXzr.XZR Width.W64) (↑XRegOrXzr.XZR Width.W64)
          { base := ↑XRegOrSp.SP Width.W64, off := ↑{ imm := ↑32, index := some Index.Post } } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("stp xzr, xzr, [sp], #32")

-- ============================================================================
-- 2. Arithmetic Instructions (ADD, ADDS, SUB, SUBS, CMP, CMN, NEG, NEGS)
-- ============================================================================

-- Test: ADD_e with immediate and shift 0
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ADD_e (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          ↑{ imm := ↑42, shift := ImmShift.S0 } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("add x0, x1, #42")

-- Test: ADD_e with immediate and shift 12
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ADD_e (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          ↑{ imm := ↑42, shift := ImmShift.S12 } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("add x0, x1, #42, lsl #12")

-- Test: ADD_e with SP operands
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ADD_e (↑XRegOrSp.SP Width.W64) (↑XRegOrSp.SP Width.W64)
          ↑{ imm := ↑16, shift := ImmShift.S0 } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("add sp, sp, #16")

-- Test: ADD_e with binary immediate literal (#0b1010)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ADD_e (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          ↑{ imm := ↑10, shift := ImmShift.S0 } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("add x0, x1, #0b1010")

-- Test: ADD_s with shifted register operand
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ADD_s (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          { reg := ↑↑XReg.X2 Width.W64, amount := 2, shift := ShiftType.LSL } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("add x0, x1, x2, lsl #2")

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

-- Test: ADD_e with extended register operand
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

-- Test: ADDS_e with immediate operand
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ADDS_e (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          ↑{ imm := ↑42, shift := ImmShift.S0 } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("adds x0, x1, #42")

-- Test: ADDS_s with shifted register operand
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ADDS_s (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          { reg := ↑↑XReg.X2 Width.W64, amount := 2, shift := ShiftType.LSL } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("adds x0, x1, x2, lsl #2")

-- Test: CMN alias for ADDS XZR, Xn, #imm
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ADDS_e (↑XRegOrXzr.XZR Width.W64) (↑↑XReg.X1 Width.W64)
          ↑{ imm := ↑10, shift := ImmShift.S0 } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("cmn x1, #10")

-- Test: SUB_e with immediate operand
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.SUB_e (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          ↑{ imm := ↑5, shift := ImmShift.S0 } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("sub x0, x1, #5")

-- Test: SUBS_e with immediate operand
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.SUBS_e (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          ↑{ imm := ↑5, shift := ImmShift.S0 } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("subs x0, x1, #5")

-- Test: CMP alias for SUBS XZR, Xn, Xm
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.SUBS_s (↑XRegOrXzr.XZR Width.W64) (↑↑XReg.X1 Width.W64)
          { reg := ↑↑XReg.X2 Width.W64, amount := 0, shift := ShiftType.LSL } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("cmp x1, x2")

-- Test: NEG alias for SUB Xd, XZR, Xm
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.SUB_s (↑↑XReg.X0 Width.W64) (↑XRegOrXzr.XZR Width.W64)
          { reg := ↑↑XReg.X1 Width.W64, amount := 0, shift := ShiftType.LSL } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("neg x0, x1")

-- Test: NEGS alias for SUBS Xd, XZR, Xm
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.SUBS_s (↑↑XReg.X0 Width.W64) (↑XRegOrXzr.XZR Width.W64)
          { reg := ↑↑XReg.X1 Width.W64, amount := 0, shift := ShiftType.LSL } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("negs x0, x1")

-- ============================================================================
-- 3. Carry Arithmetic (ADC, ADCS, SBC, SBCS)
-- ============================================================================

-- Test: ADC 64-bit add with carry
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.ADC (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("adc x0, x1, x2")

-- Test: ADCS 32-bit add with carry and set flags
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation := Operation.ADCS (↑↑XReg.X3 Width.W32) (↑↑XReg.X4 Width.W32) (↑↑XReg.X5 Width.W32) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("adcs w3, w4, w5")

-- Test: SBC 64-bit subtract with carry
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.SBC (↑↑XReg.X6 Width.W64) (↑↑XReg.X7 Width.W64) (↑↑XReg.X8 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("sbc x6, x7, x8")

-- Test: SBCS 32-bit subtract with carry and set flags
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation :=
        Operation.SBCS (↑↑XReg.X9 Width.W32) (↑↑XReg.X10 Width.W32) (↑↑XReg.X11 Width.W32) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("sbcs w9, w10, w11")

-- ============================================================================
-- 4. Multiply & Divide Instructions (MADD, MSUB, MUL, MNEG, SMULH, UMULH, SMULL, UMULL, SMADDL, UMADDL, SMSUBL, UMSUBL, SDIV, UDIV)
-- ============================================================================

-- Test: MADD 64-bit multiply-add
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.MADD (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64)
          (↑↑XReg.X3 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("madd x0, x1, x2, x3")

-- Test: MADD 32-bit multiply-add
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation :=
        Operation.MADD (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) (↑↑XReg.X2 Width.W32)
          (↑↑XReg.X3 Width.W32) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("madd w0, w1, w2, w3")

-- Test: MUL 64-bit alias for MADD Xd, Xn, Xm, XZR
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.MADD (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64)
          (↑XRegOrXzr.XZR Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("mul x0, x1, x2")

-- Test: MUL 32-bit alias for MADD Wd, Wn, Wm, WZR
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation :=
        Operation.MADD (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) (↑↑XReg.X2 Width.W32)
          (↑XRegOrXzr.XZR Width.W32) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("mul w0, w1, w2")

-- Test: MSUB 64-bit multiply-subtract
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.MSUB (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64)
          (↑↑XReg.X3 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("msub x0, x1, x2, x3")

-- Test: MSUB 32-bit multiply-subtract
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation :=
        Operation.MSUB (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) (↑↑XReg.X2 Width.W32)
          (↑↑XReg.X3 Width.W32) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("msub w0, w1, w2, w3")

-- Test: MNEG 64-bit alias for MSUB Xd, Xn, Xm, XZR
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.MSUB (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64)
          (↑XRegOrXzr.XZR Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("mneg x0, x1, x2")

-- Test: MNEG 32-bit alias for MSUB Wd, Wn, Wm, WZR
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation :=
        Operation.MSUB (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) (↑↑XReg.X2 Width.W32)
          (↑XRegOrXzr.XZR Width.W32) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("mneg w0, w1, w2")

-- Test: SMULH signed multiply high 64-bit
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.SMULH (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("smulh x0, x1, x2")

-- Test: UMULH unsigned multiply high 64-bit
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.UMULH (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("umulh x0, x1, x2")

-- Test: SDIV
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.SDIV (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("sdiv x0, x1, x2")

-- Test: UDIV
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation := Operation.UDIV (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) (↑↑XReg.X2 Width.W32) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("udiv w0, w1, w2")

-- Test: SMULL
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.SMADDL (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W32) (↑↑XReg.X2 Width.W32)
          (↑XRegOrXzr.XZR Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("smull x0, w1, w2")

-- Test: UMULL
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.UMADDL (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W32) (↑↑XReg.X2 Width.W32)
          (↑XRegOrXzr.XZR Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("umull x0, w1, w2")

-- Test: SMNEGL
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.SMSUBL (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W32) (↑↑XReg.X2 Width.W32)
          (↑XRegOrXzr.XZR Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("smnegl x0, w1, w2")

-- Test: UMNEGL
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.UMSUBL (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W32) (↑↑XReg.X2 Width.W32)
          (↑XRegOrXzr.XZR Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("umnegl x0, w1, w2")

-- Test: SMADDL
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.SMADDL (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W32) (↑↑XReg.X2 Width.W32)
          (↑↑XReg.X3 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("smaddl x0, w1, w2, x3")

-- Test: UMADDL
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.UMADDL (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W32) (↑↑XReg.X2 Width.W32)
          (↑↑XReg.X3 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("umaddl x0, w1, w2, x3")

-- Test: SMSUBL
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.SMSUBL (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W32) (↑↑XReg.X2 Width.W32)
          (↑↑XReg.X3 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("smsubl x0, w1, w2, x3")

-- Test: UMSUBL
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.UMSUBL (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W32) (↑↑XReg.X2 Width.W32)
          (↑↑XReg.X3 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("umsubl x0, w1, w2, x3")

-- ============================================================================
-- 5. Logical Instructions (AND, ANDS, TST, ORR, ORN, EOR, BIC, EON, BICS)
-- ============================================================================

-- Test: AND_s with shifted register operand (lsr #4)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.AND_s (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          { reg := ↑↑XReg.X2 Width.W64, amount := 4, shift := ShiftType.LSR } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("and x0, x1, x2, lsr #4")

-- Test: AND_i with immediate bitmask
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.AND_i (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) ↑255 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("and x0, x1, #255")

-- Test: ANDS_s 64-bit register logical AND with flags
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ANDS_s (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          { reg := ↑↑XReg.X2 Width.W64, amount := 0, shift := ShiftType.LSL } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ands x0, x1, x2")

-- Test: ANDS_i 32-bit immediate bitmask with flags
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation := Operation.ANDS_i (↑↑XReg.X5 Width.W32) (↑↑XReg.X6 Width.W32) ↑255 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ands w5, w6, #255")

-- Test: TST register alias for ANDS XZR, Xn, Xm
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ANDS_s (↑XRegOrXzr.XZR Width.W64) (↑↑XReg.X1 Width.W64)
          { reg := ↑↑XReg.X2 Width.W64, amount := 0, shift := ShiftType.LSL } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("tst x1, x2")

-- Test: TST immediate alias for ANDS XZR, Xn, #imm
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.ANDS_i (↑XRegOrXzr.XZR Width.W64) (↑↑XReg.X7 Width.W64) ↑255 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("tst x7, #255")

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

-- Test: ORR_i 32-bit immediate bitmask
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation := Operation.ORR_i (↑↑XReg.X2 Width.W32) (↑↑XReg.X3 Width.W32) ↑255 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("orr w2, w3, #255")

-- Test: ORR_s with ROR shift
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ORR_s (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          { reg := ↑↑XReg.X2 Width.W64, amount := 4, shift := ShiftType.ROR } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("orr x0, x1, x2, ror #4")

-- Test: ORN_s 64-bit logical OR NOT
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ORN_s (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          { reg := ↑↑XReg.X2 Width.W64, amount := 0, shift := ShiftType.LSL } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("orn x0, x1, x2")

-- Test: EOR_s 64-bit logical XOR
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.EOR_s (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          { reg := ↑↑XReg.X2 Width.W64, amount := 0, shift := ShiftType.LSL } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("eor x0, x1, x2")

-- Test: EOR_i 64-bit immediate bitmask with SP destination
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.EOR_i (↑XRegOrSp.SP Width.W64) (↑↑XReg.X4 Width.W64) ↑255 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("eor sp, x4, #255")

-- Test: BIC_s 64-bit bit clear
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.BIC_s (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          { reg := ↑↑XReg.X2 Width.W64, amount := 0, shift := ShiftType.LSL } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("bic x0, x1, x2")

-- Test: EON_s 64-bit logical XOR NOT
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.EON_s (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          { reg := ↑↑XReg.X2 Width.W64, amount := 0, shift := ShiftType.LSL } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("eon x0, x1, x2")

-- Test: BICS_s 64-bit logical AND NOT setting flags
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.BICS_s (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64)
          { reg := ↑↑XReg.X2 Width.W64, amount := 0, shift := ShiftType.LSL } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("bics x0, x1, x2")

-- ============================================================================
-- 6. Move & Move Wide Immediate Family (MOV, MVN, MOVZ, MOVK, MOVN)
-- ============================================================================

-- Test: MOV register alias for ORR Xd, XZR, Xm
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ORR_s (↑↑XReg.X0 Width.W64) (↑XRegOrXzr.XZR Width.W64)
          { reg := ↑↑XReg.X1 Width.W64, amount := 0, shift := ShiftType.LSL } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("mov x0, x1")

-- Test: MOV SP alias for ADD SP, Xn, #0
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ADD_e (↑XRegOrSp.SP Width.W64) (↑↑XReg.X0 Width.W64)
          ↑{ imm := ↑0, shift := ImmShift.S0 } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("mov sp, x0")

-- Test: MVN register alias for ORN Xd, XZR, Xm
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ORN_s (↑↑XReg.X2 Width.W64) (↑XRegOrXzr.XZR Width.W64)
          { reg := ↑↑XReg.X3 Width.W64, amount := 0, shift := ShiftType.LSL } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("mvn x2, x3")

-- Test: MOVZ move wide with zeroes (LSL #16)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.MOVZ (↑↑XReg.X0 Width.W64) (↑1234) MovShift.LSL16 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("movz x0, #1234, lsl #16")

-- Test: MOVK move wide with keep (LSL #0)
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation := Operation.MOVK (↑↑XReg.X1 Width.W32) (↑5678) MovShift.LSL0 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("movk w1, #5678, lsl #0")

-- Test: MOVN move wide with NOT (LSL #48)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.MOVN (↑↑XReg.X2 Width.W64) (↑65535) MovShift.LSL48 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("movn x2, #65535, lsl #48")

-- Test: MOV immediate Priority 1 -> MOVZ (#0)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.MOVZ (↑↑XReg.X0 Width.W64) (↑0) MovShift.LSL0 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("mov x0, #0")

-- Test: MOV immediate Priority 1 -> MOVZ shifted (#0x12340000)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.MOVZ (↑↑XReg.X1 Width.W64) (↑4660) MovShift.LSL16 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("mov x1, #0x12340000")

-- Test: MOV immediate Priority 2 -> MOVN 64-bit (#0xfffffffffffffffe)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.MOVN (↑↑XReg.X2 Width.W64) (↑1) MovShift.LSL0 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("mov x2, #0xfffffffffffffffe")

-- Test: MOV immediate Priority 2 -> MOVN 32-bit (#0xffffffff)
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation := Operation.MOVN (↑↑XReg.X3 Width.W32) (↑0) MovShift.LSL0 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("mov w3, #0xffffffff")

-- Test: MOV immediate Priority 3 -> ORR_i bitmask (#0x0101010101010101)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ORR_i (↑↑XReg.X4 Width.W64) (↑XRegOrXzr.XZR Width.W64) ↑72340172838076673 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("mov x4, #0x0101010101010101")

-- Test: MOV immediate negative 64-bit alias (#-1)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.MOVN (↑↑XReg.X5 Width.W64) (↑0) MovShift.LSL0 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("mov x5, #-1")

-- Test: MOV immediate negative 32-bit alias (#-5)
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation := Operation.MOVN (↑↑XReg.X6 Width.W32) (↑4) MovShift.LSL0 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("mov w6, #-5")

-- ============================================================================
-- 7. Shifts, Rotates, and Bit Manipulation (LSL, LSR, ASR, ROR, LSLV, LSRV, ASRV, RORV, BFM, SBFM, UBFM, UBFX, SBFX, BFXIL, BFI, SBFIZ, UBFIZ, SXTW, CLZ, CLS, RBIT, REV, REV16, REV32, REV64, EXTR)
-- ============================================================================

-- Test: LSL register shift left (alias for LSLV)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.LSLV (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("lsl x0, x1, x2")

-- Test: LSLV explicit mnemonic 32-bit
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation := Operation.LSLV (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) (↑↑XReg.X2 Width.W32) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("lslv w0, w1, w2")

-- Test: LSR register shift right (alias for LSRV)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.LSRV (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("lsr x0, x1, x2")

-- Test: ASR arithmetic shift right (alias for ASRV)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.ASRV (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("asr x0, x1, x2")

-- Test: ROR rotate right (alias for RORV)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.RORV (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ror x0, x1, x2")

-- Test: UBFX
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation := Operation.UBFM (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) 4 11 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ubfx w0, w1, #4, #8")

-- Test: SXTW
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.SBFM (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) 0 31 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("sxtw x0, w1")

-- Test: CLZ
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation := Operation.CLZ (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("clz w0, w1")

-- Test: REV
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.REV (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("rev x0, x1")

-- Test: SBFX
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.SBFM (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) 0 15 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("sbfx x0, x1, #0, #16")

-- Test: BFXIL
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation := Operation.BFM (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) 4 11 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("bfxil w0, w1, #4, #8")

-- Test: BFI
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation := Operation.BFM (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) 24 7 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("bfi w0, w1, #8, #8")

-- Test: SBFIZ
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation := Operation.SBFM (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) 28 7 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("sbfiz w0, w1, #4, #8")

-- Test: UBFIZ
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation := Operation.UBFM (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) 28 7 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ubfiz w0, w1, #4, #8")

-- Test: SXTB
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation := Operation.SBFM (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) 0 7 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("sxtb w0, w1")

-- Test: SXTH
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation := Operation.SBFM (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) 0 15 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("sxth w0, w1")

-- Test: UXTB
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation := Operation.UBFM (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) 0 7 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("uxtb w0, w1")

-- Test: UXTH
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation := Operation.UBFM (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) 0 15 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("uxth w0, w1")

-- Test: UXTW
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.UBFM (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) 0 31 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("uxtw x0, w1")

-- Test: LSL imm
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.UBFM (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) 60 59 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("lsl x0, x1, #4")

-- Test: LSR imm
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation := Operation.UBFM (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) 4 31 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("lsr w0, w1, #4")

-- Test: ASR imm
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.SBFM (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) 4 63 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("asr x0, x1, #4")

-- Test: ROR imm
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation :=
        Operation.EXTR (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) (↑↑XReg.X1 Width.W32) 4 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ror w0, w1, #4")

-- Test: CLS
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.CLS (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("cls x0, x1")

-- Test: RBIT
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation := Operation.RBIT (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("rbit w0, w1")

-- Test: REV16
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation := Operation.REV16 (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("rev16 w0, w1")

-- Test: REV32
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.REV32 (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("rev32 x0, x1")

-- Test: REV64
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.REV (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("rev64 x0, x1")

-- Test: EXTR
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation :=
        Operation.EXTR (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) (↑↑XReg.X2 Width.W32) 8 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("extr w0, w1, w2, #8")

-- ============================================================================
-- 8. Conditional Select & Compare Instructions (CSEL, CSINC, CSINV, CSNEG, CSET, CSETM, CINC, CINV, CNEG, CCMP, CCMN)
-- ============================================================================

-- Test: CSEL conditional select
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.CSEL (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64) CondCode.EQ }] : List Directive
-/
#guard_msgs in
#check parseAArch64("csel x0, x1, x2, eq")

-- Test: CSINC conditional select increment
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.CSINC (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64)
          CondCode.CS }] : List Directive
-/
#guard_msgs in
#check parseAArch64("csinc x0, x1, x2, cs")

-- Test: CSINV conditional select invert
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.CSINV (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64)
          CondCode.EQ }] : List Directive
-/
#guard_msgs in
#check parseAArch64("csinv x0, x1, x2, eq")

-- Test: CSNEG conditional select negate
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.CSNEG (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X2 Width.W64)
          CondCode.MI }] : List Directive
-/
#guard_msgs in
#check parseAArch64("csneg x0, x1, x2, mi")

-- Test: CSET alias for CSINC Xd, XZR, XZR, invert(cond)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.CSINC (↑↑XReg.X0 Width.W64) (↑XRegOrXzr.XZR Width.W64) (↑XRegOrXzr.XZR Width.W64)
          CondCode.NE }] : List Directive
-/
#guard_msgs in
#check parseAArch64("cset x0, eq")

-- Test: CSETM alias for CSINV Xd, XZR, XZR, invert(cond)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.CSINV (↑↑XReg.X3 Width.W64) (↑XRegOrXzr.XZR Width.W64) (↑XRegOrXzr.XZR Width.W64)
          CondCode.EQ }] : List Directive
-/
#guard_msgs in
#check parseAArch64("csetm x3, ne")

-- Test: CINC alias for CSINC Wd, Wn, Wn, invert(cond)
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation :=
        Operation.CSINC (↑↑XReg.X4 Width.W32) (↑↑XReg.X5 Width.W32) (↑↑XReg.X5 Width.W32)
          CondCode.CS }] : List Directive
-/
#guard_msgs in
#check parseAArch64("cinc w4, w5, lo")

-- Test: CINV alias for CSINV Xd, Xn, Xn, invert(cond)
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.CSINV (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) (↑↑XReg.X1 Width.W64)
          CondCode.MI }] : List Directive
-/
#guard_msgs in
#check parseAArch64("cinv x0, x1, pl")

-- Test: CNEG alias for CSNEG Wd, Wn, Wn, invert(cond)
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation :=
        Operation.CSNEG (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) (↑↑XReg.X1 Width.W32)
          CondCode.LE }] : List Directive
-/
#guard_msgs in
#check parseAArch64("cneg w0, w1, gt")

-- Test: CCMP reg
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.CCMP_reg (↑↑XReg.X0 Width.W64) (↑↑XReg.X1 Width.W64) 4 CondCode.EQ }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ccmp x0, x1, #4, eq")

-- Test: CCMP imm
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.CCMP_imm (↑↑XReg.X0 Width.W64) 10 2 CondCode.NE }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ccmp x0, #10, #2, ne")

-- Test: CCMN reg
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation := Operation.CCMN_reg (↑↑XReg.X0 Width.W32) (↑↑XReg.X1 Width.W32) 0 CondCode.EQ }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ccmn w0, w1, #0, eq")

-- Test: CCMN imm
/--
info: [Directive.instr
    { operation_size := Width.W32,
      operation := Operation.CCMN_imm (↑↑XReg.X0 Width.W32) 1 0 CondCode.NE }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ccmn w0, #1, #0, ne")

-- ============================================================================
-- 9. PC-Relative Addressing & Relocation Modifiers (ADR, ADRP, :lo12:, :pg_hi21:)
-- ============================================================================

-- Test: ADR with label
/--
info: [Directive.instr
    { operation_size := Width.W64, operation := Operation.ADR (↑↑XReg.X0 Width.W64) ↑"main" }] : List Directive
-/
#guard_msgs in
#check parseAArch64("adr x0, main")

-- Test: ADR with immediate offset
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

-- Test: ADRP with immediate offset
/--
info: [Directive.instr
    { operation_size := Width.W64, operation := Operation.ADRP (↑↑XReg.X1 Width.W64) ↑16384 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("adrp x1, #0x4000")

-- Test: ADRP with :pg_hi21: relocation modifier
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation := Operation.ADRP (↑↑XReg.X0 Width.W64) (↑"main").pg_hi21 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("adrp x0, :pg_hi21:main")

-- Test: ADD_e with :lo12: relocation modifier on label
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.ADD_e (↑↑XReg.X0 Width.W64) (↑↑XReg.X0 Width.W64)
          ↑{ imm := (↑"main").lo12, shift := ImmShift.S0 } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("add x0, x0, :lo12:main")

-- Test: LDR with #:lo12: relocation modifier on memory offset
/--
info: [Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.LDR (↑↑XReg.X1 Width.W64)
          ↑{ base := ↑↑XReg.X0 Width.W64, off := ↑{ imm := (↑"main").lo12, index := none } } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ldr x1, [x0, #:lo12:main]")

-- ============================================================================
-- 10. Control Flow Instructions (B, B.cond, BL, BLR, BR, RET, CBZ, CBNZ, TBZ, TBNZ)
-- ============================================================================

-- Test: B unconditional branch with label
/--
info: [Directive.instr { operation_size := Width.W64, operation := Operation.B ↑"main" }] : List Directive
-/
#guard_msgs in
#check parseAArch64("b main")

-- Test: B unconditional branch with immediate offset
/--
info: [Directive.instr { operation_size := Width.W64, operation := Operation.B ↑16 }] : List Directive
-/
#guard_msgs in
#check parseAArch64("b #16")

-- Test: B.eq conditional branch with dotted syntax
/--
info: [Directive.instr { operation_size := Width.W64, operation := Operation.B_cond CondCode.EQ ↑"loop" }] : List Directive
-/
#guard_msgs in
#check parseAArch64("b.eq loop")

-- Test: B.ne conditional branch with dotted syntax
/--
info: [Directive.instr { operation_size := Width.W64, operation := Operation.B_cond CondCode.NE ↑"exit" }] : List Directive
-/
#guard_msgs in
#check parseAArch64("b.ne exit")

-- Test: BEQ conditional branch with undotted syntax
/--
info: [Directive.instr { operation_size := Width.W64, operation := Operation.B_cond CondCode.EQ ↑"loop" }] : List Directive
-/
#guard_msgs in
#check parseAArch64("beq loop")

-- Test: BNE conditional branch with undotted syntax
/--
info: [Directive.instr { operation_size := Width.W64, operation := Operation.B_cond CondCode.NE ↑"exit" }] : List Directive
-/
#guard_msgs in
#check parseAArch64("bne exit")

-- Test: BL branch with link
/--
info: [Directive.instr { operation_size := Width.W64, operation := Operation.BL ↑"foo" }] : List Directive
-/
#guard_msgs in
#check parseAArch64("bl foo")

-- Test: BLR branch with link to register
/--
info: [Directive.instr { operation_size := Width.W64, operation := Operation.BLR (↑↑XReg.X16 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("blr x16")

-- Test: BR branch to register
/--
info: [Directive.instr { operation_size := Width.W64, operation := Operation.BR (↑↑XReg.X30 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("br x30")

-- Test: RET return without operand (defaults to X30)
/--
info: [Directive.instr { operation_size := Width.W64, operation := Operation.RET (↑↑XReg.X30 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ret")

-- Test: RET return with explicit register (X19)
/--
info: [Directive.instr { operation_size := Width.W64, operation := Operation.RET (↑↑XReg.X19 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ret x19")

-- Test: RET return with LR alias
/--
info: [Directive.instr { operation_size := Width.W64, operation := Operation.RET (↑↑XReg.X30 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ret lr")

-- Test: CBZ compare and branch if zero 64-bit
/--
info: [Directive.instr
    { operation_size := Width.W64, operation := Operation.CBZ (↑↑XReg.X0 Width.W64) ↑"target" }] : List Directive
-/
#guard_msgs in
#check parseAArch64("cbz x0, target")

-- Test: CBNZ compare and branch if non-zero 32-bit
/--
info: [Directive.instr
    { operation_size := Width.W32, operation := Operation.CBNZ (↑↑XReg.X1 Width.W32) ↑"loop" }] : List Directive
-/
#guard_msgs in
#check parseAArch64("cbnz w1, loop")

-- Test: TBZ test bit and branch if zero 64-bit
/--
info: [Directive.instr
    { operation_size := Width.W64, operation := Operation.TBZ (↑↑XReg.X2 Width.W64) 5 ↑"label" }] : List Directive
-/
#guard_msgs in
#check parseAArch64("tbz x2, #5, label")

-- Test: TBNZ test bit and branch if non-zero 32-bit
/--
info: [Directive.instr
    { operation_size := Width.W32, operation := Operation.TBNZ (↑↑XReg.X3 Width.W32) 31 ↑"exit" }] : List Directive
-/
#guard_msgs in
#check parseAArch64("tbnz w3, #31, exit")

-- ============================================================================
-- 11. Miscellaneous & Directives (NOP, Labels, Comments)
-- ============================================================================

-- Test: NOP no-operation
/--
info: [Directive.instr { operation_size := Width.W64, operation := Operation.NOP }] : List Directive
-/
#guard_msgs in
#check parseAArch64("nop")

-- Test: Label definition with instruction on a single line
/--
info: [Directive.label "main",
  Directive.instr
    { operation_size := Width.W64,
      operation :=
        Operation.LDR (↑↑XReg.X1 Width.W64)
          ↑{ base := ↑XRegOrSp.SP Width.W64, off := ↑{ imm := ↑0, index := none } } }] : List Directive
-/
#guard_msgs in
#check parseAArch64("main: ldr x1, [sp]")

-- Test: Instruction followed by line comment
/--
info: [Directive.instr { operation_size := Width.W64, operation := Operation.RET (↑↑XReg.X30 Width.W64) }] : List Directive
-/
#guard_msgs in
#check parseAArch64("ret // return to caller")

-- ============================================================================
-- 12. Error Reporting
-- ============================================================================
section error_reporting

--
-- Register Constraints & Aliasing Errors
--

/-- error: line 1: unknown register or xzr: x31 -/
#guard_msgs in
#check parseAArch64("ldr x31, [sp]")

/-- error: line 1: expected w64 register, got w32 -/
#guard_msgs in
#check parseAArch64("ldr x0, [w1]")

/-- error: line 1: condition not satisfied -/
#guard_msgs in
#check parseAArch64("add xzr, x1, #42")

/-- error: line 1: expected w64 register, got w32 -/
#guard_msgs in
#check parseAArch64("adr w0, main")

/-- error: line 1: expected w64 register, got w32 -/
#guard_msgs in
#check parseAArch64("adrp w0, main")

/-- error: line 1: expected w64 register, got w32 -/
#guard_msgs in
#check parseAArch64("br w0")

/-- error: line 1: expected w64 register, got w32 -/
#guard_msgs in
#check parseAArch64("ret w0")

/-- error: line 1: UXTW extension requires a 32-bit index register (Wn) -/
#guard_msgs in
#check parseAArch64("ldr x0, [sp, x1, uxtw]")

/-- error: line 1: SXTX extension requires a 64-bit index register (Xn) -/
#guard_msgs in
#check parseAArch64("ldr x0, [sp, w1, sxtx]")

/-- error: line 1: unknown register, sp, or xzr: wlr -/
#guard_msgs in
#check parseAArch64("add w0, wlr, #1")

/-- error: line 1: condition not satisfied -/
#guard_msgs in
#check parseAArch64("ldr x1, [sp, -#16]!")

/-- error: line 1: condition not satisfied -/
#guard_msgs in
#check parseAArch64("add x0, x1, -#16")

/-- error: line 1: condition not satisfied -/
#guard_msgs in
#check parseAArch64("ldur x0, [x1, -#8]")

/-- error: line 1: SP/WSP is not allowed as destination of adds -/
#guard_msgs in
#check parseAArch64("adds sp, x1, #0")

/-- error: line 1: condition not satisfied -/
#guard_msgs in
#check parseAArch64("add x0, xzr, #1")

/-- error: line 1: SXTW extension requires a 32-bit index register (Wn) -/
#guard_msgs in
#check parseAArch64("ldr x0, [x1, x2, sxtw]")

/-- error: line 1: UXTX extension requires a 64-bit index register (Xn) -/
#guard_msgs in
#check parseAArch64("ldr x0, [x1, w2, uxtx]")

/-- error: line 1: unknown register, sp, or xzr: badreg -/
#guard_msgs in
#check parseAArch64("add sp, badreg, #1")

--
-- Immediate Values & Range Bounds Errors
--

/-- error: line 1: immediate 5000 out of range [0, 4095] -/
#guard_msgs in
#check parseAArch64("add x0, x1, #5000")

/-- error: line 1: invalid immediate shift for add: 1 (must be 0 or 12) -/
#guard_msgs in
#check parseAArch64("add x0, x1, #10, lsl #1")

/-- error: line 1: relocation modifiers and labels cannot be shifted with lsl in immediate operands -/
#guard_msgs in
#check parseAArch64("add x1, x1, :lo12:main, lsl #12")

/-- error: line 1: relocation modifiers and labels cannot be shifted with lsl in immediate operands -/
#guard_msgs in
#check parseAArch64("add x1, x1, :lo12:main, lsl #0")

/-- error: line 1: tbz bit position 32 out of range [0, 31] for 32-bit instruction -/
#guard_msgs in
#check parseAArch64("tbz w0, #32, target")

/-- error: line 1: invalid logical immediate: 0x1f4 -/
#guard_msgs in
#check parseAArch64("and x0, x1, #500")

/-- error: line 1: invalid logical immediate: 0x0 -/
#guard_msgs in
#check parseAArch64("orr x0, x1, #0")

/-- error: line 1: invalid logical immediate: -0x1 -/
#guard_msgs in
#check parseAArch64("eor x0, x1, #-1")

/-- error: line 1: ccmp/ccmn immediate 32 out of range [0, 31] -/
#guard_msgs in
#check parseAArch64("ccmp x0, #32, #0, eq")

/-- error: line 1: nzcv immediate 16 out of range [0, 15] -/
#guard_msgs in
#check parseAArch64("ccmp x0, x1, #16, eq")

/-- error: line 1: immediate 18446744073709551616 out of 64-bit range -/
#guard_msgs in
#check parseAArch64("mov x0, #0x10000000000000000")

/-- error: line 1: expected non-negative immediate, got -1 -/
#guard_msgs in
#check parseAArch64("ubfm x0, x1, #-1, #0")

/-- error: line 1: immediate cannot be moved by a single instruction (requires MOVZ/MOVK sequence) -/
#guard_msgs in
#check parseAArch64("mov x0, #0x123456")

/-- error: line 1: move wide immediate 65536 out of range [0, 65535] -/
#guard_msgs in
#check parseAArch64("movz x0, #65536")

/-- error: line 1: bitfield extract bounds invalid: lsb=0, width=65, w=64 -/
#guard_msgs in
#check parseAArch64("ubfx x0, x1, #0, #65")

/-- error: line 1: expected immediate offset in unscaled address operand -/
#guard_msgs in
#check parseAArch64("ldur x0, [x1, x2]")

/-- error: line 1: expected lsl for immediate shift, got asr -/
#guard_msgs in
#check parseAArch64("add x0, x1, #10, asr #0")

/-- error: line 1: shift immediate 32 out of range [0, 31] -/
#guard_msgs in
#check parseAArch64("lsl w0, w1, #32")

--
-- Memory Addressing, Offset Bounds & Alignment Errors
--

/-- error: line 1: pre-indexed offset 300 out of range [-256, 255] -/
#guard_msgs in
#check parseAArch64("ldr x1, [sp, #300]!")

/-- error: line 1: post-indexed offset -300 out of range [-256, 255] -/
#guard_msgs in
#check parseAArch64("str x2, [x1], #-300")

/-- error: line 1: offset 257 is neither a valid scaled offset [0, 32760] (multiple of 8) nor a valid unscaled offset [-256, 255] -/
#guard_msgs in
#check parseAArch64("ldr x0, [x1, #257]")

/-- error: line 1: pair offset 600 out of range [-512, 504] or not a multiple of 8 -/
#guard_msgs in
#check parseAArch64("ldp x0, x1, [sp, #600]")

/-- error: line 1: pair offset 13 out of range [-512, 504] or not a multiple of 8 -/
#guard_msgs in
#check parseAArch64("ldp x0, x1, [sp, #13]")

/-- error: line 1: register offsets are not supported for ldp/stp instructions -/
#guard_msgs in
#check parseAArch64("ldp x0, x1, [sp, x2]")

/-- error: line 1: unpredictable: identical destination registers in ldp instruction -/
#guard_msgs in
#check parseAArch64("ldp x0, x0, [sp, #16]")

/-- error: line 1: unpredictable: writeback base register is also a transfer register -/
#guard_msgs in
#check parseAArch64("ldp x0, x1, [x0, #16]!")

/-- error: line 1: unpredictable: writeback base register is also a transfer register -/
#guard_msgs in
#check parseAArch64("stp x0, x1, [x0, #16]!")

/-- error: line 1: adr offset 0x200000 out of range [-0x100000, 0xfffff] -/
#guard_msgs in
#check parseAArch64("adr x0, #0x200000")

/-- error: line 1: adrp offset 0x1004 not page aligned (must be multiple of 0x1000) -/
#guard_msgs in
#check parseAArch64("adrp x0, #0x1004")

/-- error: line 1: adrp offset 0x200000000 out of range [-0x100000000, 0xfffff000] -/
#guard_msgs in
#check parseAArch64("adrp x0, #0x200000000")

/-- error: line 1: offset 32768 is neither a valid scaled offset [0, 32760] (multiple of 8) nor a valid unscaled offset [-256, 255] -/
#guard_msgs in
#check parseAArch64("ldr x0, [x1, #32768]")

/-- error: line 1: unscaled offset -300 out of range [-256, 255] -/
#guard_msgs in
#check parseAArch64("ldur x0, [x1, #-300]")

/-- error: line 1: expected ',' or ']' after base register in memory operand, got x -/
#guard_msgs in
#check parseAArch64("ldr x0, [x1 x2]")

/-- error: line 1: expected ',' or ']' after base register in pair memory operand, got x -/
#guard_msgs in
#check parseAArch64("ldp x0, x1, [x2 x3]")

/-- error: line 1: expected ',' or ']' after base register in unscaled address operand, got x -/
#guard_msgs in
#check parseAArch64("ldur x0, [x1 x2]")

/-- error: line 1: expected ',' or ']' after index register in memory operand, got x -/
#guard_msgs in
#check parseAArch64("ldr x0, [x1, x2 x3]")

--
-- Shifts, Extensions & Relocation Modifier Errors
--

/-- error: line 1: invalid memory extension shift amount 1 for width w64 -/
#guard_msgs in
#check parseAArch64("ldr x0, [x1, x2, lsl #1]")

/-- error: line 1: invalid extend amount: 65 -/
#guard_msgs in
#check parseAArch64("add x0, x1, x2, lsl #65")

/-- error: line 1: invalid extend amount: 33 -/
#guard_msgs in
#check parseAArch64("add w0, w1, w2, lsl #33")

/-- error: line 1: unknown extension type: ror -/
#guard_msgs in
#check parseAArch64("add x0, x1, x2, ror #4")

/-- error: line 1: sp/wsp not allowed in shifted register instruction (xzr expected) -/
#guard_msgs in
#check parseAArch64("and sp, x1, x2")

/-- error: line 1: unknown memory extension type: badext -/
#guard_msgs in
#check parseAArch64("ldr x0, [x1, w2, badext]")

/-- error: line 1: unknown extension type: ror -/
#guard_msgs in
#check parseAArch64("add x0, x1, x2, ror #1")

/-- error: line 1: unknown shift type: badshift -/
#guard_msgs in
#check parseAArch64("orr x0, x1, x2, badshift #1")

--
-- Control Flow & General Parser Syntax Errors
--

/-- error: line 1: unexpected trailing characters on line -/
#guard_msgs in
#check parseAArch64("nop extra_tokens")

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

/-- error: line 1: tbz offset 0x10000 out of range [-0x8000, 0x7fc] or not a multiple of 4 -/
#guard_msgs in
#check parseAArch64("tbz x0, #10, #0x10000")

/-- error: line 1: unexpected trailing characters on line -/
#guard_msgs in
#check parseAArch64("add x0, x1, #1 # comment")

/-- error: line 1: unexpected trailing characters on line -/
#guard_msgs in
#check parseAArch64("ldr x0, [x1, x2]!")

/-- error: line 1: unexpected trailing characters on line -/
#guard_msgs in
#check parseAArch64("movz x0, #1, asr #0")

/-- error: line 1: unexpected trailing characters on line -/
#guard_msgs in
#check parseAArch64("movz w0, #1, lsl #32")

/-- error: line 1: unexpected end of input -/
#guard_msgs in
#check parseAArch64("add x0, x1")

/-- error: line 1: unknown condition code: invalid -/
#guard_msgs in
#check parseAArch64("csel x0, x1, x2, invalid")

/-- error: line 1: unsupported instruction: foobar -/
#guard_msgs in
#check parseAArch64("foobar x0, x1")

end error_reporting

end Tests
