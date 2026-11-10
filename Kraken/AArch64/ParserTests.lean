module

/-
  ParserAArch64 Tests
  Uses #guard_msgs to verify AArch64 parser output against expected results.
-/

public import Lean
public meta import Lean
public import Kraken.AArch64.Parser
public meta import Kraken.AArch64.Parser

section Tests
open Kraken hiding Directive
open AArch64.Parser

-- ============================================================================
-- 1. Memory Access: Loads and Stores (LDR, STR, LDUR, STUR, LDP, STP)
-- ============================================================================

-- Test: LDR 64-bit with base register only
/--
info: ⸨prog|
  ldr x0, [sp]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ldr x0, [sp] ⸩

-- Test: STR 32-bit with unsigned scaled immediate offset
/--
info: ⸨prog|
  str w0, [x1, #8]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| str w0, [x1, #8] ⸩

-- Test: LDR 64-bit with pre-indexed immediate offset
/--
info: ⸨prog|
  ldr x1, [sp, #-16]!⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ldr x1, [sp, #-16]! ⸩

-- Test: STR 64-bit with post-indexed immediate offset
/--
info: ⸨prog|
  str x2, [x1], #16⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| str x2, [x1], #16 ⸩

-- Test: LDR 64-bit with register offset, extension, and shift
/--
info: ⸨prog|
  ldr x0, [x1, x2, lsl #3]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ldr x0, [x1, x2, lsl #3] ⸩

-- Test: LDUR 64-bit unscaled immediate offset
/--
info: ⸨prog|
  ldur x0, [x1, #-8]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ldur x0, [x1, #-8] ⸩

-- Test: STUR 32-bit unscaled immediate offset
/--
info: ⸨prog|
  stur w2, [x3, #13]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| stur w2, [x3, #13] ⸩

-- Test: LDR automatic conversion to LDUR for negative unscaled offset
/--
info: ⸨prog|
  ldur x0, [x1, #-8]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ldr x0, [x1, #-8] ⸩

-- Test: LDR automatic conversion to LDUR for unaligned unscaled offset
/--
info: ⸨prog|
  ldur x0, [x1, #13]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ldr x0, [x1, #13] ⸩

-- Test: LDP 64-bit load pair with signed immediate offset
/--
info: ⸨prog|
  ldp x0, x1, [sp, #16]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ldp x0, x1, [sp, #16] ⸩

-- Test: STP 32-bit store pair with pre-indexed offset
/--
info: ⸨prog|
  stp w0, w1, [sp, #-32]!⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| stp w0, w1, [sp, #-32]! ⸩

-- Test: STP 64-bit store pair with zero registers and post-indexed offset
/--
info: ⸨prog|
  stp xzr, xzr, [sp], #32⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| stp xzr, xzr, [sp], #32 ⸩

-- Test: LDRB 32-bit with unsigned offset
/--
info: ⸨prog|
  ldrb w0, [x1, #5]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ldrb w0, [x1, #5] ⸩

-- Test: LDURB 32-bit with negative unscaled offset
/--
info: ⸨prog|
  ldurb w0, [x1, #-5]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ldurb w0, [x1, #-5] ⸩

-- Test: STRB 32-bit with unsigned offset
/--
info: ⸨prog|
  strb w0, [x1, #10]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| strb w0, [x1, #10] ⸩

-- Test: STURB 32-bit with negative unscaled offset
/--
info: ⸨prog|
  sturb w0, [x1, #-10]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| sturb w0, [x1, #-10] ⸩

-- Test: LDRSB 32-bit destination with unsigned offset
/--
info: ⸨prog|
  ldrsb w0, [x1, #5]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ldrsb w0, [x1, #5] ⸩

-- Test: LDRSB 64-bit destination with unsigned offset
/--
info: ⸨prog|
  ldrsb x0, [x1, #5]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ldrsb x0, [x1, #5] ⸩

-- Test: LDURSB 64-bit destination with negative unscaled offset
/--
info: ⸨prog|
  ldursb x0, [x1, #-5]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ldursb x0, [x1, #-5] ⸩

-- Test: LDRH 32-bit with unsigned offset
/--
info: ⸨prog|
  ldrh w0, [x1, #6]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ldrh w0, [x1, #6] ⸩

-- Test: LDURH 32-bit with negative unscaled offset
/--
info: ⸨prog|
  ldurh w0, [x1, #-6]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ldurh w0, [x1, #-6] ⸩

-- Test: STRH 32-bit with unsigned offset
/--
info: ⸨prog|
  strh w0, [x1, #8]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| strh w0, [x1, #8] ⸩

-- Test: STURH 32-bit with negative unscaled offset
/--
info: ⸨prog|
  sturh w0, [x1, #-8]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| sturh w0, [x1, #-8] ⸩

-- Test: LDRSH 32-bit destination with unsigned offset
/--
info: ⸨prog|
  ldrsh w0, [x1, #6]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ldrsh w0, [x1, #6] ⸩

-- Test: LDRSH 64-bit destination with unsigned offset
/--
info: ⸨prog|
  ldrsh x0, [x1, #6]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ldrsh x0, [x1, #6] ⸩

-- Test: LDURSH 64-bit destination with negative unscaled offset
/--
info: ⸨prog|
  ldursh x0, [x1, #-6]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ldursh x0, [x1, #-6] ⸩

-- Test: LDRSW 64-bit destination with unsigned offset
/--
info: ⸨prog|
  ldrsw x0, [x1, #8]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ldrsw x0, [x1, #8] ⸩

-- Test: LDURSW 64-bit destination with negative unscaled offset
/--
info: ⸨prog|
  ldursw x0, [x1, #-8]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ldursw x0, [x1, #-8] ⸩

-- Test: LDPSW 64-bit load pair with signed immediate offset
/--
info: ⸨prog|
  ldpsw x0, x1, [sp, #8]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ldpsw x0, x1, [sp, #8] ⸩

-- ============================================================================
-- 2. Arithmetic Instructions (ADD, ADDS, SUB, SUBS, CMP, CMN, NEG, NEGS)
-- ============================================================================

-- Test: ADD_e with immediate and shift 0
/--
info: ⸨prog|
  add x0, x1, #42⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| add x0, x1, #42 ⸩

-- Test: ADD_e with immediate and shift 12
/--
info: ⸨prog|
  add x0, x1, #42, lsl #12⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| add x0, x1, #42, lsl #12 ⸩

-- Test: ADD_e with SP operands
/--
info: ⸨prog|
  add sp, sp, #16⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| add sp, sp, #16 ⸩

-- Test: ADD_e with binary immediate literal (#0b1010)
/--
info: ⸨prog|
  add x0, x1, #10⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| add x0, x1, #0b1010 ⸩

-- Test: ADD_s with shifted register operand
/--
info: ⸨prog|
  add x0, x1, x2, lsl #2⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| add x0, x1, x2, lsl #2 ⸩

-- Test: ADD_s with XZR destination
/--
info: ⸨prog|
  add xzr, x1, x2⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| add xzr, x1, x2 ⸩

-- Test: ADD_e with extended register operand
/--
info: ⸨prog|
  add x0, x1, w2, uxtw #2⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| add x0, x1, w2, uxtw #2 ⸩

-- Test: ADDS_e with immediate operand
/--
info: ⸨prog|
  adds x0, x1, #42⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| adds x0, x1, #42 ⸩

-- Test: ADDS_s with shifted register operand
/--
info: ⸨prog|
  adds x0, x1, x2, lsl #2⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| adds x0, x1, x2, lsl #2 ⸩

-- Test: CMN alias for ADDS XZR, Xn, #imm
/--
info: ⸨prog|
  adds xzr, x1, #10⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| cmn x1, #10 ⸩

-- Test: SUB_e with immediate operand
/--
info: ⸨prog|
  sub x0, x1, #5⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| sub x0, x1, #5 ⸩

-- Test: SUBS_e with immediate operand
/--
info: ⸨prog|
  subs x0, x1, #5⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| subs x0, x1, #5 ⸩

-- Test: CMP alias for SUBS XZR, Xn, Xm
/--
info: ⸨prog|
  subs xzr, x1, x2⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| cmp x1, x2 ⸩

-- Test: NEG alias for SUB Xd, XZR, Xm
/--
info: ⸨prog|
  sub x0, xzr, x1⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| neg x0, x1 ⸩

-- Test: NEGS alias for SUBS Xd, XZR, Xm
/--
info: ⸨prog|
  subs x0, xzr, x1⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| negs x0, x1 ⸩

-- ============================================================================
-- 3. Carry Arithmetic (ADC, ADCS, SBC, SBCS)
-- ============================================================================

-- Test: ADC 64-bit add with carry
/--
info: ⸨prog|
  adc x0, x1, x2⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| adc x0, x1, x2 ⸩

-- Test: ADCS 32-bit add with carry and set flags
/--
info: ⸨prog|
  adcs w3, w4, w5⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| adcs w3, w4, w5 ⸩

-- Test: SBC 64-bit subtract with carry
/--
info: ⸨prog|
  sbc x6, x7, x8⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| sbc x6, x7, x8 ⸩

-- Test: SBCS 32-bit subtract with carry and set flags
/--
info: ⸨prog|
  sbcs w9, w10, w11⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| sbcs w9, w10, w11 ⸩

-- ============================================================================
-- 4. Multiply & Divide Instructions (MADD, MSUB, MUL, MNEG, SMULH, UMULH, SMULL, UMULL, SMADDL, UMADDL, SMSUBL, UMSUBL, SDIV, UDIV)
-- ============================================================================

-- Test: MADD 64-bit multiply-add
/--
info: ⸨prog|
  madd x0, x1, x2, x3⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| madd x0, x1, x2, x3 ⸩

-- Test: MADD 32-bit multiply-add
/--
info: ⸨prog|
  madd w0, w1, w2, w3⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| madd w0, w1, w2, w3 ⸩

-- Test: MUL 64-bit alias for MADD Xd, Xn, Xm, XZR
/--
info: ⸨prog|
  madd x0, x1, x2, xzr⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| mul x0, x1, x2 ⸩

-- Test: MUL 32-bit alias for MADD Wd, Wn, Wm, WZR
/--
info: ⸨prog|
  madd w0, w1, w2, wzr⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| mul w0, w1, w2 ⸩

-- Test: MSUB 64-bit multiply-subtract
/--
info: ⸨prog|
  msub x0, x1, x2, x3⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| msub x0, x1, x2, x3 ⸩

-- Test: MSUB 32-bit multiply-subtract
/--
info: ⸨prog|
  msub w0, w1, w2, w3⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| msub w0, w1, w2, w3 ⸩

-- Test: MNEG 64-bit alias for MSUB Xd, Xn, Xm, XZR
/--
info: ⸨prog|
  msub x0, x1, x2, xzr⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| mneg x0, x1, x2 ⸩

-- Test: MNEG 32-bit alias for MSUB Wd, Wn, Wm, WZR
/--
info: ⸨prog|
  msub w0, w1, w2, wzr⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| mneg w0, w1, w2 ⸩

-- Test: SMULH signed multiply high 64-bit
/--
info: ⸨prog|
  smulh x0, x1, x2⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| smulh x0, x1, x2 ⸩

-- Test: UMULH unsigned multiply high 64-bit
/--
info: ⸨prog|
  umulh x0, x1, x2⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| umulh x0, x1, x2 ⸩

-- Test: SDIV
/--
info: ⸨prog|
  sdiv x0, x1, x2⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| sdiv x0, x1, x2 ⸩

-- Test: UDIV
/--
info: ⸨prog|
  udiv w0, w1, w2⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| udiv w0, w1, w2 ⸩

-- Test: SMULL
/--
info: ⸨prog|
  smaddl x0, w1, w2, xzr⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| smull x0, w1, w2 ⸩

-- Test: UMULL
/--
info: ⸨prog|
  umaddl x0, w1, w2, xzr⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| umull x0, w1, w2 ⸩

-- Test: SMNEGL
/--
info: ⸨prog|
  smsubl x0, w1, w2, xzr⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| smnegl x0, w1, w2 ⸩

-- Test: UMNEGL
/--
info: ⸨prog|
  umsubl x0, w1, w2, xzr⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| umnegl x0, w1, w2 ⸩

-- Test: SMADDL
/--
info: ⸨prog|
  smaddl x0, w1, w2, x3⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| smaddl x0, w1, w2, x3 ⸩

-- Test: UMADDL
/--
info: ⸨prog|
  umaddl x0, w1, w2, x3⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| umaddl x0, w1, w2, x3 ⸩

-- Test: SMSUBL
/--
info: ⸨prog|
  smsubl x0, w1, w2, x3⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| smsubl x0, w1, w2, x3 ⸩

-- Test: UMSUBL
/--
info: ⸨prog|
  umsubl x0, w1, w2, x3⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| umsubl x0, w1, w2, x3 ⸩

-- ============================================================================
-- 5. Logical Instructions (AND, ANDS, TST, ORR, ORN, EOR, BIC, EON, BICS)
-- ============================================================================

-- Test: AND_s with shifted register operand (lsr #4)
/--
info: ⸨prog|
  and x0, x1, x2, lsr #4⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| and x0, x1, x2, lsr #4 ⸩

-- Test: AND_i with immediate bitmask
/--
info: ⸨prog|
  and x0, x1, #255⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| and x0, x1, #255 ⸩

-- Test: ANDS_s 64-bit register logical AND with flags
/--
info: ⸨prog|
  ands x0, x1, x2⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ands x0, x1, x2 ⸩

-- Test: ANDS_i 32-bit immediate bitmask with flags
/--
info: ⸨prog|
  ands w5, w6, #255⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ands w5, w6, #255 ⸩

-- Test: TST register alias for ANDS XZR, Xn, Xm
/--
info: ⸨prog|
  ands xzr, x1, x2⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| tst x1, x2 ⸩

-- Test: TST immediate alias for ANDS XZR, Xn, #imm
/--
info: ⸨prog|
  ands xzr, x7, #255⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| tst x7, #255 ⸩

-- Test: ORR_s 32-bit without shift
/--
info: ⸨prog|
  orr w0, w1, w2⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| orr w0, w1, w2 ⸩

-- Test: ORR_i 32-bit immediate bitmask
/--
info: ⸨prog|
  orr w2, w3, #255⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| orr w2, w3, #255 ⸩

-- Test: ORR_s with ROR shift
/--
info: ⸨prog|
  orr x0, x1, x2, ror #4⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| orr x0, x1, x2, ror #4 ⸩

-- Test: ORN_s 64-bit logical OR NOT
/--
info: ⸨prog|
  orn x0, x1, x2⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| orn x0, x1, x2 ⸩

-- Test: EOR_s 64-bit logical XOR
/--
info: ⸨prog|
  eor x0, x1, x2⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| eor x0, x1, x2 ⸩

-- Test: EOR_i 64-bit immediate bitmask with SP destination
/--
info: ⸨prog|
  eor sp, x4, #255⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| eor sp, x4, #255 ⸩

-- Test: BIC_s 64-bit bit clear
/--
info: ⸨prog|
  bic x0, x1, x2⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| bic x0, x1, x2 ⸩

-- Test: EON_s 64-bit logical XOR NOT
/--
info: ⸨prog|
  eon x0, x1, x2⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| eon x0, x1, x2 ⸩

-- Test: BICS_s 64-bit logical AND NOT setting flags
/--
info: ⸨prog|
  bics x0, x1, x2⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| bics x0, x1, x2 ⸩

-- ============================================================================
-- 6. Move & Move Wide Immediate Family (MOV, MVN, MOVZ, MOVK, MOVN)
-- ============================================================================

-- Test: MOV register alias for ORR Xd, XZR, Xm
/--
info: ⸨prog|
  orr x0, xzr, x1⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| mov x0, x1 ⸩

-- Test: MOV SP alias for ADD SP, Xn, #0
/--
info: ⸨prog|
  add sp, x0, #0⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| mov sp, x0 ⸩

-- Test: MVN register alias for ORN Xd, XZR, Xm
/--
info: ⸨prog|
  orn x2, xzr, x3⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| mvn x2, x3 ⸩

-- Test: MOVZ move wide with zeroes (LSL #16)
/--
info: ⸨prog|
  movz x0, #1234, lsl #16⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movz x0, #1234, lsl #16 ⸩

-- Test: MOVK move wide with keep (LSL #0)
/--
info: ⸨prog|
  movk w1, #5678, lsl #0⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movk w1, #5678, lsl #0 ⸩

-- Test: MOVN move wide with NOT (LSL #48)
/--
info: ⸨prog|
  movn x2, #65535, lsl #48⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| movn x2, #65535, lsl #48 ⸩

-- Test: MOV immediate Priority 1 -> MOVZ (#0)
/--
info: ⸨prog|
  movz x0, #0, lsl #0⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| mov x0, #0 ⸩

-- Test: MOV immediate Priority 1 -> MOVZ shifted (#0x12340000)
/--
info: ⸨prog|
  movz x1, #4660, lsl #16⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| mov x1, #0x12340000 ⸩

-- Test: MOV immediate Priority 2 -> MOVN 64-bit (#0xfffffffffffffffe)
/--
info: ⸨prog|
  movn x2, #1, lsl #0⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| mov x2, #0xfffffffffffffffe ⸩

-- Test: MOV immediate Priority 2 -> MOVN 32-bit (#0xffffffff)
/--
info: ⸨prog|
  movn w3, #0, lsl #0⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| mov w3, #0xffffffff ⸩

-- Test: MOV immediate Priority 3 -> ORR_i bitmask (#0x0101010101010101)
/--
info: ⸨prog|
  orr x4, xzr, #72340172838076673⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| mov x4, #0x0101010101010101 ⸩

-- Test: MOV immediate negative 64-bit alias (#-1)
/--
info: ⸨prog|
  movn x5, #0, lsl #0⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| mov x5, #-1 ⸩

-- Test: MOV immediate negative 32-bit alias (#-5)
/--
info: ⸨prog|
  movn w6, #4, lsl #0⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| mov w6, #-5 ⸩

-- ============================================================================
-- 7. Shifts, Rotates, and Bit Manipulation (LSL, LSR, ASR, ROR, LSLV, LSRV, ASRV, RORV, BFM, SBFM, UBFM, UBFX, SBFX, BFXIL, BFI, SBFIZ, UBFIZ, SXTW, CLZ, CLS, RBIT, REV, REV16, REV32, REV64, EXTR)
-- ============================================================================

-- Test: LSL register shift left (alias for LSLV)
/--
info: ⸨prog|
  lslv x0, x1, x2⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| lsl x0, x1, x2 ⸩

-- Test: LSLV explicit mnemonic 32-bit
/--
info: ⸨prog|
  lslv w0, w1, w2⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| lslv w0, w1, w2 ⸩

-- Test: LSR register shift right (alias for LSRV)
/--
info: ⸨prog|
  lsrv x0, x1, x2⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| lsr x0, x1, x2 ⸩

-- Test: ASR arithmetic shift right (alias for ASRV)
/--
info: ⸨prog|
  asrv x0, x1, x2⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| asr x0, x1, x2 ⸩

-- Test: ROR rotate right (alias for RORV)
/--
info: ⸨prog|
  rorv x0, x1, x2⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ror x0, x1, x2 ⸩

-- Test: UBFX
/--
info: ⸨prog|
  ubfm w0, w1, #4, #11⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ubfx w0, w1, #4, #8 ⸩

-- Test: SXTW
/--
info: ⸨prog|
  sbfm x0, x1, #0, #31⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| sxtw x0, w1 ⸩

-- Test: CLZ
/--
info: ⸨prog|
  clz w0, w1⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| clz w0, w1 ⸩

-- Test: REV
/--
info: ⸨prog|
  rev x0, x1⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| rev x0, x1 ⸩

-- Test: SBFX
/--
info: ⸨prog|
  sbfm x0, x1, #0, #15⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| sbfx x0, x1, #0, #16 ⸩

-- Test: BFXIL
/--
info: ⸨prog|
  bfm w0, w1, #4, #11⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| bfxil w0, w1, #4, #8 ⸩

-- Test: BFI
/--
info: ⸨prog|
  bfm w0, w1, #24, #7⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| bfi w0, w1, #8, #8 ⸩

-- Test: SBFIZ
/--
info: ⸨prog|
  sbfm w0, w1, #28, #7⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| sbfiz w0, w1, #4, #8 ⸩

-- Test: UBFIZ
/--
info: ⸨prog|
  ubfm w0, w1, #28, #7⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ubfiz w0, w1, #4, #8 ⸩

-- Test: SXTB
/--
info: ⸨prog|
  sbfm w0, w1, #0, #7⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| sxtb w0, w1 ⸩

-- Test: SXTH
/--
info: ⸨prog|
  sbfm w0, w1, #0, #15⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| sxth w0, w1 ⸩

-- Test: UXTB
/--
info: ⸨prog|
  ubfm w0, w1, #0, #7⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| uxtb w0, w1 ⸩

-- Test: UXTH
/--
info: ⸨prog|
  ubfm w0, w1, #0, #15⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| uxth w0, w1 ⸩

-- Test: UXTW
/--
info: ⸨prog|
  ubfm x0, x1, #0, #31⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| uxtw x0, w1 ⸩

-- Test: LSL imm
/--
info: ⸨prog|
  ubfm x0, x1, #60, #59⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| lsl x0, x1, #4 ⸩

-- Test: LSR imm
/--
info: ⸨prog|
  ubfm w0, w1, #4, #31⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| lsr w0, w1, #4 ⸩

-- Test: ASR imm
/--
info: ⸨prog|
  sbfm x0, x1, #4, #63⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| asr x0, x1, #4 ⸩

-- Test: ROR imm
/--
info: ⸨prog|
  extr w0, w1, w1, #4⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ror w0, w1, #4 ⸩

-- Test: CLS
/--
info: ⸨prog|
  cls x0, x1⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| cls x0, x1 ⸩

-- Test: RBIT
/--
info: ⸨prog|
  rbit w0, w1⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| rbit w0, w1 ⸩

-- Test: REV16
/--
info: ⸨prog|
  rev16 w0, w1⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| rev16 w0, w1 ⸩

-- Test: REV32
/--
info: ⸨prog|
  rev32 x0, x1⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| rev32 x0, x1 ⸩

-- Test: REV64
/--
info: ⸨prog|
  rev x0, x1⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| rev64 x0, x1 ⸩

-- Test: EXTR
/--
info: ⸨prog|
  extr w0, w1, w2, #8⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| extr w0, w1, w2, #8 ⸩

-- ============================================================================
-- 8. Conditional Select & Compare Instructions (CSEL, CSINC, CSINV, CSNEG, CSET, CSETM, CINC, CINV, CNEG, CCMP, CCMN)
-- ============================================================================

-- Test: CSEL conditional select
/--
info: ⸨prog|
  csel x0, x1, x2, eq⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| csel x0, x1, x2, eq ⸩

-- Test: CSINC conditional select increment
/--
info: ⸨prog|
  csinc x0, x1, x2, cs⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| csinc x0, x1, x2, cs ⸩

-- Test: CSINV conditional select invert
/--
info: ⸨prog|
  csinv x0, x1, x2, eq⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| csinv x0, x1, x2, eq ⸩

-- Test: CSNEG conditional select negate
/--
info: ⸨prog|
  csneg x0, x1, x2, mi⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| csneg x0, x1, x2, mi ⸩

-- Test: CSET alias for CSINC Xd, XZR, XZR, invert(cond)
/--
info: ⸨prog|
  csinc x0, xzr, xzr, ne⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| cset x0, eq ⸩

-- Test: CSETM alias for CSINV Xd, XZR, XZR, invert(cond)
/--
info: ⸨prog|
  csinv x3, xzr, xzr, eq⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| csetm x3, ne ⸩

-- Test: CINC alias for CSINC Wd, Wn, Wn, invert(cond)
/--
info: ⸨prog|
  csinc w4, w5, w5, cs⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| cinc w4, w5, lo ⸩

-- Test: CINV alias for CSINV Xd, Xn, Xn, invert(cond)
/--
info: ⸨prog|
  csinv x0, x1, x1, mi⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| cinv x0, x1, pl ⸩

-- Test: CNEG alias for CSNEG Wd, Wn, Wn, invert(cond)
/--
info: ⸨prog|
  csneg w0, w1, w1, le⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| cneg w0, w1, gt ⸩

-- Test: CCMP reg
/--
info: ⸨prog|
  ccmp x0, x1, #4, eq⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ccmp x0, x1, #4, eq ⸩

-- Test: CCMP imm
/--
info: ⸨prog|
  ccmp x0, #10, #2, ne⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ccmp x0, #10, #2, ne ⸩

-- Test: CCMN reg
/--
info: ⸨prog|
  ccmn w0, w1, #0, eq⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ccmn w0, w1, #0, eq ⸩

-- Test: CCMN imm
/--
info: ⸨prog|
  ccmn w0, #1, #0, ne⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ccmn w0, #1, #0, ne ⸩

-- ============================================================================
-- 9. PC-Relative Addressing & Relocation Modifiers (ADR, ADRP, :lo12:, :pg_hi21:)
-- ============================================================================

-- Test: ADR with label
/--
info: ⸨prog|
  adr x0, main⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| adr x0, main ⸩

-- Test: ADR with immediate offset
/--
info: ⸨prog|
  adr x1, #4096⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| adr x1, #4096 ⸩

-- Test: ADRP with label
/--
info: ⸨prog|
  adrp x0, main⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| adrp x0, main ⸩

-- Test: ADRP with immediate offset
/--
info: ⸨prog|
  adrp x1, #16384⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| adrp x1, #0x4000 ⸩

-- Test: ADRP with :pg_hi21: relocation modifier
/--
info: ⸨prog|
  adrp x0, :pg_hi21:main⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| adrp x0, :pg_hi21:main ⸩

-- Test: ADD_e with :lo12: relocation modifier on label
/--
info: ⸨prog|
  add x0, x0, :lo12:main⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| add x0, x0, :lo12:main ⸩

-- Test: LDR with #:lo12: relocation modifier on memory offset
/--
info: ⸨prog|
  ldr x1, [x0, :lo12:main]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ldr x1, [x0, #:lo12:main] ⸩

-- ============================================================================
-- 10. Control Flow Instructions (B, B.cond, BL, BLR, BR, RET, CBZ, CBNZ, TBZ, TBNZ)
-- ============================================================================

-- Test: B unconditional branch with label
/--
info: ⸨prog|
  b main⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| b main ⸩

-- Test: B unconditional branch with immediate offset
/--
info: ⸨prog|
  b #16⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| b #16 ⸩

-- Test: B.eq conditional branch with dotted syntax
/--
info: ⸨prog|
  b.eq loop⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| b.eq loop ⸩

-- Test: B.ne conditional branch with dotted syntax
/--
info: ⸨prog|
  b.ne exit⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| b.ne exit ⸩

-- Test: BEQ conditional branch with undotted syntax
/--
info: ⸨prog|
  b.eq loop⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| beq loop ⸩

-- Test: BNE conditional branch with undotted syntax
/--
info: ⸨prog|
  b.ne exit⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| bne exit ⸩

-- Test: BL branch with link
/--
info: ⸨prog|
  bl foo⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| bl foo ⸩

-- Test: BLR branch with link to register
/--
info: ⸨prog|
  blr x16⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| blr x16 ⸩

-- Test: BR branch to register
/--
info: ⸨prog|
  br x30⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| br x30 ⸩

-- Test: RET return without operand (defaults to X30)
/--
info: ⸨prog|
  ret⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ret ⸩

-- Test: RET return with explicit register (X19)
/--
info: ⸨prog|
  ret x19⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ret x19 ⸩

-- Test: RET return with LR alias
/--
info: ⸨prog|
  ret⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| ret lr ⸩

-- Test: CBZ compare and branch if zero 64-bit
/--
info: ⸨prog|
  cbz x0, target⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| cbz x0, target ⸩

-- Test: CBNZ compare and branch if non-zero 32-bit
/--
info: ⸨prog|
  cbnz w1, loop⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| cbnz w1, loop ⸩

-- Test: TBZ test bit and branch if zero 64-bit
/--
info: ⸨prog|
  tbz x2, #5, label⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| tbz x2, #5, label ⸩

-- Test: TBNZ test bit and branch if non-zero 32-bit
/--
info: ⸨prog|
  tbnz w3, #31, exit⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| tbnz w3, #31, exit ⸩

-- ============================================================================
-- 11. Miscellaneous & Directives (NOP, Labels, Comments)
-- ============================================================================

-- Test: NOP no-operation
/--
info: ⸨prog|
  nop⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| nop ⸩

-- Test: Label definition with instruction on a single line
/--
info: ⸨prog|
  main:
  ldr x1, [sp]⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog| main: ldr x1, [sp] ⸩

-- Test: Instruction followed by line comment
/--
info: ⸨prog|
  ret⸩ : List Directive
-/
#guard_msgs (whitespace := lax) in
#check ⸨prog|
  ret -- return to caller
⸩

-- ============================================================================
-- 12. Error Reporting
-- ============================================================================
section error_reporting

local elab "elabAArch64% " s:str : term => elabAArch64 s.getString

--
-- Register Constraints & Aliasing Errors
--

/-- error: <input>:1:4: expected aarch64_reg -/
#guard_msgs in
#check elabAArch64% "ldr x31, [sp]"

/-- error: expected w64 register, got w32 -/
#guard_msgs in
#check ⸨prog| ldr x0, [w1] ⸩

/-- error: requires 32-bit registers (got 64-bit) -/
#guard_msgs in
#check ⸨prog| ldrb x0, [x1] ⸩

/-- error: requires 32-bit registers (got 64-bit) -/
#guard_msgs in
#check ⸨prog| strb x0, [x1] ⸩

/-- error: requires 32-bit registers (got 64-bit) -/
#guard_msgs in
#check ⸨prog| ldrh x0, [x1] ⸩

/-- error: requires 32-bit registers (got 64-bit) -/
#guard_msgs in
#check ⸨prog| strh x0, [x1] ⸩

/-- error: xzr/wzr not allowed here (sp/wsp expected) -/
#guard_msgs in
#check ⸨prog| add xzr, x1, #42 ⸩

/-- error: expected w64 register, got w32 -/
#guard_msgs in
#check ⸨prog| adr w0, main ⸩

/-- error: expected w64 register, got w32 -/
#guard_msgs in
#check ⸨prog| adrp w0, main ⸩

/-- error: expected w64 register, got w32 -/
#guard_msgs in
#check ⸨prog| br w0 ⸩

/-- error: expected w64 register, got w32 -/
#guard_msgs in
#check ⸨prog| ret w0 ⸩

/-- error: UXTW extension requires a 32-bit index register (Wn) -/
#guard_msgs in
#check ⸨prog| ldr x0, [sp, x1, uxtw] ⸩

/-- error: SXTX extension requires a 64-bit index register (Xn) -/
#guard_msgs in
#check ⸨prog| ldr x0, [sp, w1, sxtx] ⸩

/-- error: <input>:1:8: expected aarch64_reg -/
#guard_msgs in
#check elabAArch64% "add w0, wlr, #1"

/-- error: <input>:1:14: expected numeral -/
#guard_msgs in
#check elabAArch64% "ldr x1, [sp, -#16]!"

/-- error: <input>:1:13: expected numeral -/
#guard_msgs in
#check elabAArch64% "add x0, x1, -#16"

/-- error: <input>:1:15: expected numeral -/
#guard_msgs in
#check elabAArch64% "ldur x0, [x1, -#8]"

/-- error: sp/wsp not allowed here (xzr/wzr expected) -/
#guard_msgs in
#check ⸨prog| adds sp, x1, #0 ⸩

/-- error: xzr/wzr not allowed here (sp/wsp expected) -/
#guard_msgs in
#check ⸨prog| add x0, xzr, #1 ⸩

/-- error: SXTW extension requires a 32-bit index register (Wn) -/
#guard_msgs in
#check ⸨prog| ldr x0, [x1, x2, sxtw] ⸩

/-- error: UXTX extension requires a 64-bit index register (Xn) -/
#guard_msgs in
#check ⸨prog| ldr x0, [x1, w2, uxtx] ⸩

/-- error: <input>:1:8: expected aarch64_reg -/
#guard_msgs in
#check elabAArch64% "add sp, badreg, #1"

--
-- Immediate Values & Range Bounds Errors
--

/-- error: immediate 5000 out of range [0, 4095] -/
#guard_msgs in
#check ⸨prog| add x0, x1, #5000 ⸩

/-- error: invalid immediate shift 1 (must be 0 or 12) -/
#guard_msgs in
#check ⸨prog| add x0, x1, #10, lsl #1 ⸩

/-- error: relocation modifiers and labels cannot be shifted with lsl in immediate operands -/
#guard_msgs in
#check ⸨prog| add x1, x1, :lo12:main, lsl #12 ⸩

/-- error: relocation modifiers and labels cannot be shifted with lsl in immediate operands -/
#guard_msgs in
#check ⸨prog| add x1, x1, :lo12:main, lsl #0 ⸩

/-- error: tbz bit position 32 out of range [0, 31] for 32-bit instruction -/
#guard_msgs in
#check ⸨prog| tbz w0, #32, target ⸩

/-- error: invalid logical immediate: 0x1f4 -/
#guard_msgs in
#check ⸨prog| and x0, x1, #500 ⸩

/-- error: invalid logical immediate: 0x0 -/
#guard_msgs in
#check ⸨prog| orr x0, x1, #0 ⸩

/-- error: invalid logical immediate: -0x1 -/
#guard_msgs in
#check ⸨prog| eor x0, x1, #-1 ⸩

/-- error: ccmp/ccmn immediate 32 out of range [0, 31] -/
#guard_msgs in
#check ⸨prog| ccmp x0, #32, #0, eq ⸩

/-- error: nzcv immediate 16 out of range [0, 15] -/
#guard_msgs in
#check ⸨prog| ccmp x0, x1, #16, eq ⸩

/-- error: integer 18446744073709551616 out of 64-bit range -/
#guard_msgs in
#check ⸨prog| mov x0, #0x10000000000000000 ⸩

/-- error: expected non-negative immediate, got -1 -/
#guard_msgs in
#check ⸨prog| ubfm x0, x1, #-1, #0 ⸩

/-- error: immediate cannot be moved by a single instruction (requires MOVZ/MOVK sequence) -/
#guard_msgs in
#check ⸨prog| mov x0, #0x123456 ⸩

/-- error: move wide immediate 65536 out of range [0, 65535] -/
#guard_msgs in
#check ⸨prog| movz x0, #65536 ⸩

/-- error: bitfield extract bounds invalid: lsb=0, width=65, w=64 -/
#guard_msgs in
#check ⸨prog| ubfx x0, x1, #0, #65 ⸩

/-- error: expected immediate offset in unscaled address operand -/
#guard_msgs in
#check ⸨prog| ldur x0, [x1, x2] ⸩

/-- error: expected lsl for immediate shift, got asr -/
#guard_msgs in
#check ⸨prog| add x0, x1, #10, asr #0 ⸩

/-- error: shift immediate 32 out of range [0, 31] -/
#guard_msgs in
#check ⸨prog| lsl w0, w1, #32 ⸩

--
-- Memory Addressing, Offset Bounds & Alignment Errors
--

/-- error: pre-indexed offset 300 out of range [-256, 255] -/
#guard_msgs in
#check ⸨prog| ldr x1, [sp, #300]! ⸩

/-- error: post-indexed offset -300 out of range [-256, 255] -/
#guard_msgs in
#check ⸨prog| str x2, [x1], #-300 ⸩

/-- error: offset 257 is neither a valid scaled offset [0, 32760] (multiple of 8) nor a valid unscaled offset [-256, 255] -/
#guard_msgs in
#check ⸨prog| ldr x0, [x1, #257] ⸩

/-- error: pair offset 600 out of range [-512, 504] or not a multiple of 8 -/
#guard_msgs in
#check ⸨prog| ldp x0, x1, [sp, #600] ⸩

/-- error: pair offset 13 out of range [-512, 504] or not a multiple of 8 -/
#guard_msgs in
#check ⸨prog| ldp x0, x1, [sp, #13] ⸩

/-- error: register offsets are not supported for ldp/stp instructions -/
#guard_msgs in
#check ⸨prog| ldp x0, x1, [sp, x2] ⸩

/-- error: unpredictable: identical destination registers in ldp instruction -/
#guard_msgs in
#check ⸨prog| ldp x0, x0, [sp, #16] ⸩

/-- error: unpredictable: writeback base register is also a transfer register -/
#guard_msgs in
#check ⸨prog| ldp x0, x1, [x0, #16]! ⸩

/-- error: unpredictable: writeback base register is also a transfer register -/
#guard_msgs in
#check ⸨prog| stp x0, x1, [x0, #16]! ⸩

/-- error: unpredictable: writeback base register is also a transfer register -/
#guard_msgs in
#check ⸨prog| ldr x0, [x0, #16]! ⸩

/-- error: unpredictable: writeback base register is also a transfer register -/
#guard_msgs in
#check ⸨prog| ldr w0, [x0], #4 ⸩

/-- error: unpredictable: writeback base register is also a transfer register -/
#guard_msgs in
#check ⸨prog| str x0, [x0, #16]! ⸩

/-- error: unpredictable: writeback base register is also a transfer register -/
#guard_msgs in
#check ⸨prog| str w0, [x0], #4 ⸩

/-- error: unpredictable: writeback base register is also a transfer register -/
#guard_msgs in
#check ⸨prog| ldrb w0, [x0, #1]! ⸩

/-- error: unpredictable: writeback base register is also a transfer register -/
#guard_msgs in
#check ⸨prog| strb w0, [x0], #1 ⸩

/-- error: unpredictable: writeback base register is also a transfer register -/
#guard_msgs in
#check ⸨prog| ldrsw x0, [x0, #4]! ⸩

/-- error: adr offset 0x200000 out of range [-0x100000, 0xfffff] -/
#guard_msgs in
#check ⸨prog| adr x0, #0x200000 ⸩

/-- error: adrp offset 0x1004 not page aligned (must be multiple of 0x1000) -/
#guard_msgs in
#check ⸨prog| adrp x0, #0x1004 ⸩

/-- error: adrp offset 0x200000000 out of range [-0x100000000, 0xfffff000] -/
#guard_msgs in
#check ⸨prog| adrp x0, #0x200000000 ⸩

/-- error: offset 32768 is neither a valid scaled offset [0, 32760] (multiple of 8) nor a valid unscaled offset [-256, 255] -/
#guard_msgs in
#check ⸨prog| ldr x0, [x1, #32768] ⸩

/-- error: unscaled offset -300 out of range [-256, 255] -/
#guard_msgs in
#check ⸨prog| ldur x0, [x1, #-300] ⸩

/-- error: <input>:1:12: expected ',' or ']' -/
#guard_msgs in
#check elabAArch64% "ldr x0, [x1 x2]"

/-- error: <input>:1:16: expected ',' or ']' -/
#guard_msgs in
#check elabAArch64% "ldp x0, x1, [x2 x3]"

/-- error: <input>:1:13: expected ',' or ']' -/
#guard_msgs in
#check elabAArch64% "ldur x0, [x1 x2]"

/-- error: <input>:1:16: expected ']' -/
#guard_msgs in
#check elabAArch64% "ldr x0, [x1, x2 x3]"

--
-- Shifts, Extensions & Relocation Modifier Errors
--

/-- error: invalid memory extension shift amount 1 for width w64 -/
#guard_msgs in
#check ⸨prog| ldr x0, [x1, x2, lsl #1] ⸩

/-- error: invalid memory extension shift amount 1 for width w32 -/
#guard_msgs in
#check ⸨prog| ldrb w0, [x1, x2, lsl #1] ⸩

/-- error: invalid memory extension shift amount 2 for width w32 -/
#guard_msgs in
#check ⸨prog| ldrh w0, [x1, x2, lsl #2] ⸩

/-- error: shift amount 65 out of range [0, 63] for 64-bit instruction -/
#guard_msgs in
#check ⸨prog| add x0, x1, x2, lsl #65 ⸩

/-- error: shift amount 33 out of range [0, 31] for 32-bit instruction -/
#guard_msgs in
#check ⸨prog| add w0, w1, w2, lsl #33 ⸩

/-- error: arithmetic instructions do not support ROR shift -/
#guard_msgs in
#check ⸨prog| add x0, x1, x2, ror #4 ⸩

/-- error: sp/wsp not allowed here (xzr/wzr expected) -/
#guard_msgs in
#check ⸨prog| and sp, x1, x2 ⸩

/-- error: <input>:1:17: expected aarch64_modifier_kind -/
#guard_msgs in
#check elabAArch64% "ldr x0, [x1, w2, badext]"

/-- error: arithmetic instructions do not support ROR shift -/
#guard_msgs in
#check ⸨prog| add x0, x1, x2, ror #1 ⸩

/-- error: <input>:1:16: expected aarch64_modifier_kind -/
#guard_msgs in
#check elabAArch64% "orr x0, x1, x2, badshift #1"

--
-- Control Flow & General Parser Syntax Errors
--

/-- error: <input>:1:4: unexpected element -/
#guard_msgs in
#check elabAArch64% "nop extra_tokens"

/-- error: <input>:1:0: expected end of input -/
#guard_msgs in
#check elabAArch64% "b.invalid main"

/-- error: b offset 0x8000004 out of range [-0x8000000, 0x7fffffc] or not a multiple of 4 -/
#guard_msgs in
#check ⸨prog| b #0x8000004 ⸩

/-- error: b.cond offset 0x100000 out of range [-0x100000, 0xffffc] or not a multiple of 4 -/
#guard_msgs in
#check ⸨prog| b.eq #0x100000 ⸩

/-- error: cbz offset 0x200000 out of range [-0x100000, 0xffffc] or not a multiple of 4 -/
#guard_msgs in
#check ⸨prog| cbz x0, #0x200000 ⸩

/-- error: tbz offset 0x10000 out of range [-0x8000, 0x7ffc] or not a multiple of 4 -/
#guard_msgs in
#check ⸨prog| tbz x0, #10, #0x10000 ⸩

/-- error: b offset 0x1 out of range [-0x8000000, 0x7fffffc] or not a multiple of 4 -/
#guard_msgs in
#check ⸨prog| b #1 ⸩

/-- error: b.cond offset 0x3 out of range [-0x100000, 0xffffc] or not a multiple of 4 -/
#guard_msgs in
#check ⸨prog| b.eq #3 ⸩

/-- error: 32-bit extended register instruction requires a 32-bit register (Wn) -/
#guard_msgs in
#check ⸨prog| add w0, wsp, x1, uxtb #1 ⸩

/-- error: UXTB extension requires a 32-bit register (Wn) -/
#guard_msgs in
#check ⸨prog| add x0, sp, x1, uxtb #1 ⸩

/-- error: UXTX extension requires a 64-bit register (Xn) -/
#guard_msgs in
#check ⸨prog| add x0, sp, w1, uxtx #1 ⸩

/-- error: expected w32 register, got w64 -/
#guard_msgs in
#check ⸨prog| sxtb x0, x1 ⸩

/-- error: requires 64-bit registers (got 32-bit) -/
#guard_msgs in
#check ⸨prog| sxtw w0, w1 ⸩

/-- error: unpredictable: identical destination registers in ldp instruction -/
#guard_msgs in
#check ⸨prog| ldp xzr, xzr, [x0] ⸩

/-- error: literal pool (=expr) is not supported for ldrsw -/
#guard_msgs in
#check ⸨prog| ldrsw x0, =0 ⸩

/-- error: literal pool immediate 4294967296 out of range [-2147483648, 2147483647] -/
#guard_msgs in
#check ⸨prog| ldr w0, =0x100000000 ⸩

/-- error: <input>:1:15: expected end of input -/
#guard_msgs in
#check elabAArch64% "add x0, x1, #1 # comment"

/-- error: <input>:1:16: expected end of input -/
#guard_msgs in
#check elabAArch64% "ldr x0, [x1, x2]!"

/-- error: pre-indexed / post-indexed offsets must be constant numeric immediates -/
#guard_msgs in
#check ⸨prog| ldr x0, [x1, foo]! ⸩

/-- error: only lsl shift supported for move wide -/
#guard_msgs in
#check ⸨prog| movz x0, #1, asr #0 ⸩

/-- error: invalid move wide shift amount 32 for width w32 -/
#guard_msgs in
#check ⸨prog| movz w0, #1, lsl #32 ⸩

/-- error: <input>:1:10: unexpected end of input; expected ',' -/
#guard_msgs in
#check elabAArch64% "add x0, x1"

/-- error: <input>:1:17: expected aarch64_cond -/
#guard_msgs in
#check elabAArch64% "csel x0, x1, x2, invalid"

/-- error: <input>:1:0: expected end of input -/
#guard_msgs in
#check elabAArch64% "foobar x0, x1"

end error_reporting

section syntax_cat_and_include_aarch64

local elab "elabAArch64% " s:str : term => elabAArch64 s.getString

theorem test_aarch64_syntax_cat :
  ⸨prog|
    main:
      add x0, x0, #1
      ret
  ⸩ = elabAArch64% "main:\n  add x0, x0, #1\n  ret" := rfl

/-- info: ⸨dir| add x0, x0, #1 ⸩ : Kraken.Directive Instr ConstExpr -/
#guard_msgs in
#check ⸨dir| add x0, x0, #1 ⸩

/-- info: ⸨dir 1| add x0, x0, #1 ⸩ : Sized Directive -/
#guard_msgs (whitespace := lax) in
variable [Kraken.Layout Instr ConstExpr] in
#check ⸨dir 1 | add x0, x0, #1 ⸩

theorem test_include_aarch64_nop :
  include_aarch64 "Kraken/AArch64/Test/asm/test_nop.S" =
  [Directive.instr ⟨.W64, .NOP⟩] := rfl

theorem test_aarch64_complex_labels :
  ⸨prog|
    aa.1.aa.1:
      b .L.str.1.llvm.12345
  ⸩ = [
    Directive.label "aa.1.aa.1",
    Directive.instr ⟨.W64, .B (↑".L.str.1.llvm.12345")⟩
  ] := rfl

end syntax_cat_and_include_aarch64

section antiquotations

variable {w : RegWidth} (r : RegOrZr w) (rsp : RegOrSp w)
  (x : RegOrZr .W64) (wReg : RegOrZr .W32) (sp64 : RegOrSp .W64)
  (k : Int64) (n m : Nat) (sh : Int64)
  (addr : AddrExpr) (uaddr : UnscaledAddrExpr) (cc : CondCode)
  (i : Instr) (d : Directive) (lbl : Kraken.Label)

-- Test: an antiquoted register decides the width of its instruction, which may be a variable
/--
info: ⸨prog|
  add ❰rsp❱, ❰rsp❱, #2⸩ : List Directive
-/
#guard_msgs in
#check ⸨prog| add ❰rsp❱, ❰rsp❱, #2 ⸩

/--
info: ⸨prog|
  add ❰r❱, ❰r❱, ❰r❱, lsl #2⸩ : List Directive
-/
#guard_msgs in
#check ⸨prog| add ❰r❱, ❰r❱, ❰r❱, lsl #2 ⸩

-- Test: antiquoted and concrete registers unify
/--
info: ⸨prog|
  orr ❰x❱, xzr, x0⸩ : List Directive
-/
#guard_msgs in
#check ⸨prog| mov ❰x❱, x0 ⸩

theorem test_antiquot_polymorphic_reg :
  let rPoly : ∀ {w}, RegOrZr w := .low (.reg .X3) _
  ⸨prog|
    add ❰rPoly❱, x1, x2
    add w0, ❰rPoly❱, w2
  ⸩ = [
    Directive.instr ⟨.W64, .ADD_s .X3 .X1 (RegOrZr.X2 : ShiftRegExpr .W64)⟩,
    Directive.instr ⟨.W32, .ADD_s .W0 .W3 (RegOrZr.W2 : ShiftRegExpr .W32)⟩
  ] := rfl

-- Test: width mismatches with antiquotations
/-- error: expected w register, got w32 -/
#guard_msgs in
#check ⸨prog| add ❰r❱, w0, w1 ⸩

/-- error: requires 32-bit registers (got w) -/
#guard_msgs in
#check ⸨prog| ldrb ❰r❱, [x0] ⸩

/-- error: requires 32-bit registers (got 64-bit) -/
#guard_msgs in
#check ⸨prog| ldrb ❰x❱, [x0] ⸩

/-- error: requires 64-bit registers (got 32-bit) -/
#guard_msgs in
#check ⸨prog| sxtw ❰wReg❱, w1 ⸩

/--
error: Type mismatch
  x
has type
  RegOrZr RegWidth.W64
but is expected to have type
  RegOrZr RegWidth.W32
-/
#guard_msgs in
#check ⸨prog| sxtb x0, ❰x❱ ⸩

-- Test: memory base and index register antiquotations
/--
info: ⸨prog|
  ldr x0, [❰sp64❱, ❰wReg❱, uxtw #3]⸩ : List Directive
-/
#guard_msgs in
#check ⸨prog| ldr x0, [❰sp64❱, ❰wReg❱, uxtw #3] ⸩

/--
info: ⸨prog|
  ldur ❰x❱, [❰sp64❱, #-8]⸩ : List Directive
-/
#guard_msgs in
#check ⸨prog| ldr ❰x❱, [❰sp64❱, #-8] ⸩

-- Test: a concrete offset is scaled by the access size, which a variable width leaves undetermined
/-- error: could not infer operand width -/
#guard_msgs in
#check ⸨prog| ldr ❰r❱, [❰sp64❱, #-8] ⸩

-- Test: immediate and constant antiquotations (`#❰...❱`)
/--
info: ⸨prog|
  add x0, x1, #❰k❱, lsl #12⸩ : List Directive
-/
#guard_msgs in
#check ⸨prog| add x0, x1, #❰k❱, lsl #12 ⸩

/--
info: ⸨prog|
  add x0, x1, x2, lsl #❰sh❱⸩ : List Directive
-/
#guard_msgs in
#check ⸨prog| add x0, x1, x2, lsl #❰sh❱ ⸩

/--
info: ⸨prog|
  ldr x0, [x1, #❰k❱]!⸩ : List Directive
-/
#guard_msgs in
#check ⸨prog| ldr x0, [x1, #❰k❱]! ⸩

/--
info: ⸨prog|
  ubfm ❰r❱, ❰r❱, #❰n❱, #❰m❱⸩ : List Directive
-/
#guard_msgs in
#check ⸨prog| ubfm ❰r❱, ❰r❱, #❰n❱, #❰m❱ ⸩

/--
info: ⸨prog|
  tbz ❰r❱, #❰n❱, #❰k❱⸩ : List Directive
-/
#guard_msgs in
#check ⸨prog| tbz ❰r❱, #❰n❱, #❰k❱ ⸩

-- Test: memory, condition code, and directive antiquotations
/--
info: ⸨prog|
  ldr ❰r❱, ❰addr❱
  ldur ❰r❱, ❰uaddr❱
  ldp x0, ❰x❱, ❰addr❱⸩ : List Directive
-/
#guard_msgs in
#check ⸨prog|
  ldr ❰r❱, ❰addr❱
  ldur ❰r❱, ❰uaddr❱
  ldp x0, ❰x❱, ❰addr❱
⸩

/--
info: ⸨prog|
  csel ❰r❱, ❰r❱, ❰r❱, ❰cc❱
  csinc ❰r❱, ❰r❱, ❰r❱, ❰cc.invert❱
  csinc ❰r❱, ❰↑XRegOrXzr.XZR w❱, ❰↑XRegOrXzr.XZR w❱, ❰cc.invert❱
  ccmp ❰r❱, #❰n❱, #❰m❱, ❰cc❱⸩ : List Directive
-/
#guard_msgs in
#check ⸨prog|
  csel ❰r❱, ❰r❱, ❰r❱, ❰cc❱
  cinc ❰r❱, ❰r❱, ❰cc❱
  cset ❰r❱, ❰cc❱
  ccmp ❰r❱, #❰n❱, #❰m❱, ❰cc❱
⸩

/--
info: ⸨prog|
  ❰Directive.instr i❱
  ❰d❱
  ret⸩ : List Directive
-/
#guard_msgs in
#check ⸨prog|
  ❰.instr i❱
  ❰d❱
  ret
⸩

-- Test: an immediate antiquotation denotes an integer, even where a constant expression is expected
/--
error: Type mismatch
  lbl
has type
  Kraken.Label
but is expected to have type
  Int64
-/
#guard_msgs in
#check ⸨prog|
❰.label lbl❱
  b #❰lbl❱
⸩

-- Test: constant expression antiquotations
variable (c : ConstExpr)

/--
info: ⸨prog|
  b ❰lbl❱
  adr x0, ❰c❱
  cbz x0, ❰c❱
  movz x0, ❰c❱, lsl #16
  ldr x0, =❰c❱⸩ : List Directive
-/
#guard_msgs in
#check ⸨prog|
  b ❰lbl❱
  adr x0, ❰c❱
  cbz x0, ❰c❱
  movz x0, ❰c❱, lsl #16
  ldr x0, =❰c❱
⸩

-- Test: in a flexible source and after the base of a memory operand, `❰t❱` may be a register or a
-- constant expression, decided by its type
/--
info: ⸨prog|
  add x0, x1, ❰x❱
  ldr x0, [x1, ❰x❱, lsl #0]⸩ : List Directive
-/
#guard_msgs in
#check ⸨prog|
  add x0, x1, ❰x❱
  ldr x0, [x1, ❰x❱]
⸩

/--
info: ⸨prog|
  add x0, x1, ❰c❱
  and x0, x1, ❰c❱
  ands xzr, x0, ❰lbl❱
  ldr x0, [x1, ❰c❱]
  ldur x0, [x1, ❰c❱]⸩ : List Directive
-/
#guard_msgs in
#check ⸨prog|
  add x0, x1, ❰c❱
  and x0, x1, ❰c❱
  tst x0, ❰lbl❱
  ldr x0, [x1, ❰c❱]
  ldur x0, [x1, ❰c❱]
⸩

/-- error: relocation modifiers and labels cannot be shifted with lsl in immediate operands -/
#guard_msgs in
#check ⸨prog| add x0, x1, ❰c❱, lsl #12 ⸩

-- Test: an antiquotation that is not a register is elaborated as a constant expression
/--
error: Type mismatch
  true
has type
  Bool
but is expected to have type
  ConstExpr
-/
#guard_msgs in
#check ⸨prog| add x0, x1, ❰true❱ ⸩

-- Test: pre/post-indexed offsets must be numeric
/-- error: pre-indexed / post-indexed offsets must be constant numeric immediates -/
#guard_msgs in
#check ⸨prog| ldr x0, [x1], ❰c❱ ⸩

-- Test: label antiquotations, in label declarations and relocations
/--
info: ⸨prog|
  ❰lbl❱:
  adrp x0, :pg_hi21:❰lbl❱
  add x0, x0, :lo12:❰lbl❱
  b ❰lbl❱⸩ : List Directive
-/
#guard_msgs in
#check ⸨prog|
  ❰lbl❱:
  adrp x0, :pg_hi21:❰lbl❱
  add x0, x0, :lo12:❰lbl❱
  b ❰lbl❱
⸩

/--
info: ⸨prog|
  foo:
  ret⸩ : List Directive
-/
#guard_msgs in
#check ⸨prog|
  ❰.label "foo"❱
  ❰.instr ⟨.W64, .RET .X30⟩❱
⸩

-- Test: open program tail delaborates as `⸨prog| ...⸩ ++ rest`
variable (rest : List Directive) in
/--
info: ⸨prog|
    add x0, x1, #1⸩ ++
  rest : List (Kraken.Directive Instr ConstExpr)
-/
#guard_msgs in
#check (Directive.instr ⟨.W64, .ADD_e .X0 .X1 ↑(1 : Int64)⟩ :: rest)

/-- info: ⸨dir| hi: ⸩ : Kraken.Directive Instr ConstExpr -/
#guard_msgs in
#check (Directive.label "hi" : Directive)

/-- info: ⸨dir| add x0, x1, #1 ⸩ : Kraken.Directive Instr ConstExpr -/
#guard_msgs in
#check (Directive.instr ⟨.W64, .ADD_e .X0 .X1 ↑(1 : Int64)⟩ : Directive)

end antiquotations

end Tests
