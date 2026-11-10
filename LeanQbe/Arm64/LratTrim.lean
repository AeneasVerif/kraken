module

public import LeanQbe.Arm64.Abi
public import LeanQbe.Arm64.Litmus
public import LeanQbe.Examples.LratTrimCheckLemmas
public import LeanQbe.MainLemmas
public import Kraken.AArch64.Parser
import all Kraken.Separation
import all Kraken.Mem

/-!
# LRAT-trim checker end to end on AArch64 (plan step 7)

Compiles the four-function verified LRAT checker module `LratTrim.lratCheckFns`:
* `br_check_clause_non_strictly_by_propagation` (`LratRup.checkRup`, 17 spill slots, 144-byte frame)
* `br_check_clause_strictly_by_resolution` (`LratTrim.strictCheck`, 9 spill slots, 80-byte frame)
* `br_check_clause` (`LratTrim.checkClause`, 0 spill slots, 16-byte frame)
* `br_check_proof` (`LratTrim.checkProof`, 7 spill slots, 64-byte frame)

through the full verified pipeline (`compile Arm64.isa`), checks the emitted AArch64 assembly in
the kernel (`kernel_rfl`), links all four contracts via `compile_correct` and `lratEnv_step`
(`lrat_module_fnspec`), and proves the closed Kraken-AArch64 end-to-end theorem
`checkProof_arm64_correct` concluding `cnf₀.Unsat` on normal return (or exit to `"lrat_fail"`),
plus a concrete-byte non-vacuity instance `checkProof_arm64_nonvacuous`.
-/

set_option autoImplicit false

open Lean Elab Tactic Meta in
elab "kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let some (α, lhs, _) := tgt.eq?
    | throwError "kernel_rfl: goal is not an equality{indentExpr tgt}"
  let u ← getLevel α
  goal.assign (mkApp2 (mkConst ``Eq.refl [u]) α lhs)
  replaceMainGoal []

@[expose] public section

namespace LeanQbe.Arm64.LratTrim

open LeanQbe LeanQbe.LratRup LeanQbe.LratTrim Rega Arm64 Arm64.Litmus Kraken.AArch64 Kraken.AArch64.Parser
open Std.Sat Std.Tactic.BVDecide.LRAT.Internal Kraken.Bedrock2.Test

abbrev rupFn : Fn := ⟨"br_check_clause_non_strictly_by_propagation", LratRup.checkRup⟩
abbrev strictFn : Fn := ⟨"br_check_clause_strictly_by_resolution", strictCheck⟩
abbrev clauseFn : Fn := ⟨"br_check_clause", checkClause⟩
abbrev proofFn : Fn := ⟨"br_check_proof", checkProof⟩

def rupCode : Program := parseAArch64("br_check_clause_non_strictly_by_propagation:
  sub sp, sp, #144
  str x30, [sp, #136]
  ldr x17, =16
  add x4, x0, x17
  ldr x4, [x4]
  ldr x17, =24
  add x5, x0, x17
  ldr x5, [x5]
  ldr x17, =40
  add x6, x0, x17
  ldr x6, [x6]
  ldr x17, =48
  add x7, x0, x17
  ldr x8, [x7]
  ldr x17, =144
  add x9, x0, x17
  ldr x10, [x9]
  ldr x17, =1
  add x10, x10, x17
  ldr x17, =152
  add x0, x0, x17
  ldr x11, [x0]
  b br_check_clause_non_strictly_by_propagation.L3
  br_check_clause_non_strictly_by_propagation.L3:
  ldrsw x12, [x2]
  cbnz w12, br_check_clause_non_strictly_by_propagation.L4
  add x2, x8, #0
  add x8, x11, #0
  b br_check_clause_non_strictly_by_propagation.L2
  br_check_clause_non_strictly_by_propagation.L4:
  ldr x17, =63
  asrv x13, x12, x17
  eor x14, x12, x13
  str x14, [sp]
  sub x14, x14, x13
  str x14, [sp, #8]
  add x14, x5, x14
  str x14, [sp, #16]
  ldrsb x14, [x14]
  str x14, [sp, #24]
  eor x14, x14, x13
  str x14, [sp, #32]
  sub x13, x14, x13
  ldr x17, =4
  add x2, x2, x17
  ldr x17, =0
  subs xzr, x13, x17
  csinc w14, wzr, wzr, ge
  str x14, [sp, #40]
  cbnz w14, br_check_clause_non_strictly_by_propagation.L5
  ldr x16, =0
  subs xzr, x16, x13
  csinc w13, wzr, wzr, ge
  cbnz w13, br_check_clause_non_strictly_by_propagation.L6
  ldr x16, =0
  sub x12, x16, x12
  ldr x17, =63
  asrv x13, x12, x17
  ldr x17, =1
  orr x13, x13, x17
  ldr x14, [sp, #16]
  strb w13, [x14]
  str w12, [x8]
  ldr x17, =4
  add x8, x8, x17
  ldr x17, =1
  add x11, x11, x17
  b br_check_clause_non_strictly_by_propagation.L3
  br_check_clause_non_strictly_by_propagation.L6:
  add x1, x8, #0
  add x2, x10, #0
  add x3, x11, #0
  b br_check_clause_non_strictly_by_propagation.L1
  br_check_clause_non_strictly_by_propagation.L5:
  b br_check_clause_non_strictly_by_propagation.L3
  br_check_clause_non_strictly_by_propagation.L2:
  add x16, x2, #0
  add x2, x3, #0
  add x3, x16, #0
  add x16, x8, #0
  add x8, x10, #0
  add x10, x16, #0
  b br_check_clause_non_strictly_by_propagation.L7
  br_check_clause_non_strictly_by_propagation.L7:
  ldrsw x11, [x2]
  cbnz w11, br_check_clause_non_strictly_by_propagation.L8
  add x4, x3, #0
  add x5, x8, #0
  add x6, x10, #0
  ldr x2, =3
  ldr x3, =0
  b br_check_clause_non_strictly_by_propagation.L0
  br_check_clause_non_strictly_by_propagation.L8:
  ldr x17, =0
  subs xzr, x11, x17
  csinc w12, wzr, wzr, ge
  cbnz w12, br_check_clause_non_strictly_by_propagation.L9
  ldr x17, =3
  lslv x12, x11, x17
  add x12, x4, x12
  ldr x12, [x12]
  ldr x17, =1
  add x8, x8, x17
  add x13, x10, #0
  add x16, x3, #0
  add x3, x12, #0
  add x12, x16, #0
  ldr x10, =0
  b br_check_clause_non_strictly_by_propagation.L11
  br_check_clause_non_strictly_by_propagation.L11:
  ldrsw x14, [x3]
  str x14, [sp, #48]
  cbnz w14, br_check_clause_non_strictly_by_propagation.L12
  add x3, x10, #0
  add x10, x12, #0
  add x11, x13, #0
  b br_check_clause_non_strictly_by_propagation.L10
  br_check_clause_non_strictly_by_propagation.L12:
  ldr x14, [sp, #48]
  ldr x17, =63
  asrv x14, x14, x17
  str x14, [sp, #56]
  ldr x15, [sp, #48]
  eor x14, x15, x14
  str x14, [sp, #64]
  ldr x15, [sp, #56]
  sub x14, x14, x15
  str x14, [sp, #72]
  add x14, x5, x14
  str x14, [sp, #80]
  ldrsb x14, [x14]
  str x14, [sp, #88]
  ldr x15, [sp, #56]
  eor x14, x14, x15
  str x14, [sp, #96]
  ldr x15, [sp, #56]
  sub x14, x14, x15
  str x14, [sp, #104]
  ldr x17, =4
  add x3, x3, x17
  ldr x14, [sp, #104]
  ldr x17, =0
  subs xzr, x14, x17
  csinc w14, wzr, wzr, ge
  str x14, [sp, #112]
  cbnz w14, br_check_clause_non_strictly_by_propagation.L13
  cbnz w10, br_check_clause_non_strictly_by_propagation.L15
  b br_check_clause_non_strictly_by_propagation.L14
  br_check_clause_non_strictly_by_propagation.L15:
  ldr x14, [sp, #48]
  subs xzr, x10, x14
  csinc w10, wzr, wzr, ne
  cbnz w10, br_check_clause_non_strictly_by_propagation.L16
  add x3, x11, #0
  add x4, x12, #0
  add x5, x8, #0
  add x6, x13, #0
  ldr x2, =2
  b br_check_clause_non_strictly_by_propagation.L0
  br_check_clause_non_strictly_by_propagation.L16:
  b br_check_clause_non_strictly_by_propagation.L14
  br_check_clause_non_strictly_by_propagation.L14:
  ldr x10, [sp, #104]
  ldr x17, =0
  subs xzr, x10, x17
  csinc w10, wzr, wzr, ne
  cbnz w10, br_check_clause_non_strictly_by_propagation.L17
  ldr x10, [sp, #48]
  b br_check_clause_non_strictly_by_propagation.L11
  br_check_clause_non_strictly_by_propagation.L17:
  ldr x10, [sp, #56]
  ldr x17, =1
  orr x10, x10, x17
  ldr x14, [sp, #80]
  strb w10, [x14]
  ldr x10, [sp, #48]
  str w10, [x12]
  ldr x17, =4
  add x10, x12, x17
  ldr x17, =1
  add x12, x13, x17
  add x13, x12, #0
  add x12, x10, #0
  ldr x10, [sp, #48]
  b br_check_clause_non_strictly_by_propagation.L11
  br_check_clause_non_strictly_by_propagation.L13:
  ldr x14, [sp, #48]
  ldr x16, =0
  sub x14, x16, x14
  str x14, [sp, #120]
  subs xzr, x10, x14
  csinc w14, wzr, wzr, ne
  str x14, [sp, #128]
  cbnz w14, br_check_clause_non_strictly_by_propagation.L18
  b br_check_clause_non_strictly_by_propagation.L11
  br_check_clause_non_strictly_by_propagation.L18:
  add x3, x11, #0
  add x4, x12, #0
  add x5, x8, #0
  add x6, x13, #0
  ldr x2, =2
  b br_check_clause_non_strictly_by_propagation.L0
  br_check_clause_non_strictly_by_propagation.L10:
  cbnz w3, br_check_clause_non_strictly_by_propagation.L19
  add x1, x10, #0
  add x2, x8, #0
  add x3, x11, #0
  b br_check_clause_non_strictly_by_propagation.L1
  br_check_clause_non_strictly_by_propagation.L19:
  ldr x17, =4
  add x2, x2, x17
  add x3, x10, #0
  add x10, x11, #0
  b br_check_clause_non_strictly_by_propagation.L7
  br_check_clause_non_strictly_by_propagation.L9:
  add x4, x3, #0
  add x3, x11, #0
  add x5, x8, #0
  add x6, x10, #0
  ldr x2, =1
  b br_check_clause_non_strictly_by_propagation.L0
  br_check_clause_non_strictly_by_propagation.L1:
  add x4, x6, #0
  b br_check_clause_non_strictly_by_propagation.L20
  br_check_clause_non_strictly_by_propagation.L20:
  subs xzr, x4, x1
  csinc w8, wzr, wzr, ne
  cbnz w8, br_check_clause_non_strictly_by_propagation.L21
  ldrsw x8, [x4]
  ldr x17, =63
  asrv x10, x8, x17
  eor x8, x8, x10
  sub x8, x8, x10
  add x8, x5, x8
  ldr x17, =0
  strb w17, [x8]
  ldr x17, =4
  add x4, x4, x17
  b br_check_clause_non_strictly_by_propagation.L20
  br_check_clause_non_strictly_by_propagation.L21:
  str x6, [x7]
  str x2, [x9]
  str x3, [x0]
  ldr x30, [sp, #136]
  add sp, sp, #144
  ret
  br_check_clause_non_strictly_by_propagation.L0:
  str x4, [x7]
  str x5, [x9]
  str x6, [x0]
  add x0, x2, #0
  add x2, x3, #0
  ldr x3, =0
  ldr x4, =0
  ldr x30, [sp, #136]
  add sp, sp, #144
  b lrat_fail")

def strictCode : Program := parseAArch64("br_check_clause_strictly_by_resolution:
  sub sp, sp, #80
  str x30, [sp, #72]
  add x4, x3, #0
  b br_check_clause_strictly_by_resolution.L1
  br_check_clause_strictly_by_resolution.L1:
  ldrsw x5, [x4]
  cbnz w5, br_check_clause_strictly_by_resolution.L2
  b br_check_clause_strictly_by_resolution.L0
  br_check_clause_strictly_by_resolution.L2:
  ldr x17, =0
  subs xzr, x5, x17
  csinc w6, wzr, wzr, ge
  cbnz w6, br_check_clause_strictly_by_resolution.L3
  ldr x17, =4
  add x4, x4, x17
  b br_check_clause_strictly_by_resolution.L1
  br_check_clause_strictly_by_resolution.L3:
  add x2, x5, #0
  ldr x0, =1
  ldr x3, =0
  ldr x4, =0
  ldr x30, [sp, #72]
  add sp, sp, #80
  b lrat_fail
  br_check_clause_strictly_by_resolution.L0:
  ldr x17, =16
  add x5, x0, x17
  ldr x5, [x5]
  ldr x17, =32
  add x6, x0, x17
  ldr x6, [x6]
  ldr x17, =144
  add x0, x0, x17
  ldr x7, [x0]
  ldr x8, =0
  ldr x9, =1
  b br_check_clause_strictly_by_resolution.L5
  br_check_clause_strictly_by_resolution.L5:
  subs xzr, x4, x3
  csinc w10, wzr, wzr, ne
  cbnz w10, br_check_clause_strictly_by_resolution.L6
  ldr x17, =4
  sub x4, x4, x17
  ldrsw x10, [x4]
  ldr x17, =3
  lslv x11, x10, x17
  add x11, x5, x11
  ldr x11, [x11]
  ldr x17, =1
  add x7, x7, x17
  add x12, x8, #0
  add x8, x11, #0
  ldr x11, =0
  b br_check_clause_strictly_by_resolution.L8
  br_check_clause_strictly_by_resolution.L8:
  ldrsw x13, [x8]
  cbnz w13, br_check_clause_strictly_by_resolution.L9
  add x8, x11, #0
  add x11, x12, #0
  b br_check_clause_strictly_by_resolution.L7
  br_check_clause_strictly_by_resolution.L9:
  ldr x17, =63
  asrv x14, x13, x17
  str x14, [sp]
  eor x14, x13, x14
  str x14, [sp, #8]
  ldr x15, [sp]
  sub x14, x14, x15
  str x14, [sp, #16]
  add x14, x6, x14
  str x14, [sp, #24]
  ldrsb x14, [x14]
  str x14, [sp, #32]
  ldr x17, =4
  add x8, x8, x17
  ldr x14, [sp, #32]
  ldr x17, =0
  subs xzr, x14, x17
  csinc w14, wzr, wzr, ne
  str x14, [sp, #40]
  cbnz w14, br_check_clause_strictly_by_resolution.L10
  ldr x14, [sp, #32]
  ldr x15, [sp]
  eor x14, x14, x15
  str x14, [sp, #48]
  ldr x15, [sp]
  sub x14, x14, x15
  str x14, [sp, #56]
  ldr x16, =0
  subs xzr, x16, x14
  csinc w14, wzr, wzr, ge
  str x14, [sp, #64]
  cbnz w14, br_check_clause_strictly_by_resolution.L11
  cbnz w11, br_check_clause_strictly_by_resolution.L12
  add x11, x13, #0
  b br_check_clause_strictly_by_resolution.L8
  br_check_clause_strictly_by_resolution.L12:
  str x7, [x0]
  add x2, x11, #0
  add x3, x13, #0
  add x4, x10, #0
  ldr x0, =4
  ldr x30, [sp, #72]
  add sp, sp, #80
  b lrat_fail
  br_check_clause_strictly_by_resolution.L11:
  b br_check_clause_strictly_by_resolution.L8
  br_check_clause_strictly_by_resolution.L10:
  ldr x13, [sp]
  ldr x17, =1
  orr x13, x13, x17
  ldr x14, [sp, #24]
  strb w13, [x14]
  ldr x17, =1
  add x12, x12, x17
  b br_check_clause_strictly_by_resolution.L8
  br_check_clause_strictly_by_resolution.L7:
  cbnz w9, br_check_clause_strictly_by_resolution.L13
  cbnz w8, br_check_clause_strictly_by_resolution.L14
  str x7, [x0]
  add x2, x10, #0
  ldr x0, =5
  ldr x3, =0
  ldr x4, =0
  ldr x30, [sp, #72]
  add sp, sp, #80
  b lrat_fail
  br_check_clause_strictly_by_resolution.L14:
  ldr x17, =63
  asrv x10, x8, x17
  eor x8, x8, x10
  sub x8, x8, x10
  add x8, x6, x8
  ldr x17, =0
  strb w17, [x8]
  ldr x17, =1
  sub x8, x11, x17
  b br_check_clause_strictly_by_resolution.L5
  br_check_clause_strictly_by_resolution.L13:
  cbnz w8, br_check_clause_strictly_by_resolution.L15
  add x8, x11, #0
  ldr x9, =0
  b br_check_clause_strictly_by_resolution.L5
  br_check_clause_strictly_by_resolution.L15:
  str x7, [x0]
  ldr x16, =0
  sub x0, x16, x8
  add x2, x0, #0
  add x3, x8, #0
  add x4, x10, #0
  ldr x0, =4
  ldr x30, [sp, #72]
  add sp, sp, #80
  b lrat_fail
  br_check_clause_strictly_by_resolution.L6:
  add x3, x7, #0
  add x4, x8, #0
  add x5, x9, #0
  b br_check_clause_strictly_by_resolution.L4
  br_check_clause_strictly_by_resolution.L4:
  str x3, [x0]
  cbnz w5, br_check_clause_strictly_by_resolution.L16
  add x0, x2, #0
  add x2, x4, #0
  b br_check_clause_strictly_by_resolution.L18
  br_check_clause_strictly_by_resolution.L18:
  ldrsw x3, [x0]
  cbnz w3, br_check_clause_strictly_by_resolution.L19
  add x0, x2, #0
  b br_check_clause_strictly_by_resolution.L17
  br_check_clause_strictly_by_resolution.L19:
  ldr x17, =63
  asrv x4, x3, x17
  eor x5, x3, x4
  sub x5, x5, x4
  add x5, x6, x5
  ldrsb x7, [x5]
  ldr x17, =0
  subs xzr, x7, x17
  csinc w8, wzr, wzr, ne
  cbnz w8, br_check_clause_strictly_by_resolution.L20
  eor x7, x7, x4
  sub x4, x7, x4
  ldr x17, =0
  subs xzr, x4, x17
  csinc w4, wzr, wzr, ge
  cbnz w4, br_check_clause_strictly_by_resolution.L21
  ldr x17, =0
  strb w17, [x5]
  ldr x17, =1
  sub x2, x2, x17
  ldr x17, =4
  add x0, x0, x17
  b br_check_clause_strictly_by_resolution.L18
  br_check_clause_strictly_by_resolution.L21:
  add x2, x3, #0
  ldr x0, =7
  ldr x3, =0
  ldr x4, =0
  ldr x30, [sp, #72]
  add sp, sp, #80
  b lrat_fail
  br_check_clause_strictly_by_resolution.L20:
  add x2, x3, #0
  ldr x0, =6
  ldr x3, =0
  ldr x4, =0
  ldr x30, [sp, #72]
  add sp, sp, #80
  b lrat_fail
  br_check_clause_strictly_by_resolution.L17:
  ldr x17, =0
  subs xzr, x0, x17
  csinc w2, wzr, wzr, eq
  cbnz w2, br_check_clause_strictly_by_resolution.L22
  ldr x30, [sp, #72]
  add sp, sp, #80
  ret
  br_check_clause_strictly_by_resolution.L22:
  add x2, x0, #0
  ldr x0, =8
  ldr x3, =0
  ldr x4, =0
  ldr x30, [sp, #72]
  add sp, sp, #80
  b lrat_fail
  br_check_clause_strictly_by_resolution.L16:
  ldr x0, =3
  ldr x2, =0
  ldr x3, =0
  ldr x4, =0
  ldr x30, [sp, #72]
  add sp, sp, #80
  b lrat_fail")

def clauseCode : Program := parseAArch64("br_check_clause:
  sub sp, sp, #16
  str x30, [sp]
  ldr x17, =128
  add x4, x0, x17
  ldr x5, [x4]
  ldr x17, =1
  add x5, x5, x17
  str x5, [x4]
  ldr w4, [x2]
  ldr x17, =0
  subs xzr, x4, x17
  csinc w4, wzr, wzr, ne
  cbnz w4, br_check_clause.L1
  b br_check_clause.L0
  br_check_clause.L1:
  ldr x17, =136
  add x4, x0, x17
  ldr x5, [x4]
  ldr x17, =1
  add x5, x5, x17
  str x5, [x4]
  b br_check_clause.L0
  br_check_clause.L0:
  ldr x17, =80
  add x4, x0, x17
  ldr x4, [x4]
  ldr x17, =0
  subs xzr, x4, x17
  csinc w4, wzr, wzr, eq
  cbnz w4, br_check_clause.L2
  bl br_check_clause_non_strictly_by_propagation
  ldr x30, [sp]
  add sp, sp, #16
  ret
  br_check_clause.L2:
  bl br_check_clause_strictly_by_resolution
  ldr x30, [sp]
  add sp, sp, #16
  ret")

def proofCode : Program := parseAArch64("br_check_proof:
  sub sp, sp, #64
  str x30, [sp, #56]
  str x0, [sp]
  ldr x17, =96
  add x0, x0, x17
  ldr x0, [x0]
  ldr x1, [sp]
  ldr x17, =104
  add x1, x1, x17
  ldr x1, [x1]
  ldr x2, [sp]
  ldr x17, =64
  add x2, x2, x17
  ldrsw x2, [x2]
  str x2, [sp, #8]
  ldr x2, [sp]
  ldr x17, =72
  add x2, x2, x17
  ldrsw x2, [x2]
  ldr x17, =0
  subs xzr, x0, x17
  csinc w0, wzr, wzr, eq
  cbnz w0, br_check_proof.L0
  ldr x30, [sp, #56]
  add sp, sp, #64
  ret
  br_check_proof.L0:
  ldr x17, =0
  subs xzr, x1, x17
  csinc w0, wzr, wzr, ne
  cbnz w0, br_check_proof.L1
  ldr x30, [sp, #56]
  add sp, sp, #64
  ret
  br_check_proof.L1:
  ldr x0, [sp, #8]
  cbnz w0, br_check_proof.L2
  ldr x30, [sp, #56]
  add sp, sp, #64
  ret
  br_check_proof.L2:
  cbnz w2, br_check_proof.L3
  ldr x30, [sp, #56]
  add sp, sp, #64
  ret
  br_check_proof.L3:
  ldr x0, [sp]
  ldr x17, =88
  add x0, x0, x17
  ldr x0, [x0]
  str x0, [sp, #16]
  ldr x0, [sp]
  ldr x0, [x0]
  str x0, [sp, #24]
  ldr x0, [sp]
  ldr x17, =16
  add x0, x0, x17
  ldr x0, [x0]
  str x0, [sp, #32]
  ldr x0, [sp]
  ldr x17, =8
  add x0, x0, x17
  ldr x0, [x0]
  str x0, [sp, #40]
  add x0, x2, #0
  b br_check_proof.L4
  br_check_proof.L4:
  str x0, [sp, #48]
  ldr x1, [sp, #8]
  subs xzr, x1, x0
  csinc w0, wzr, wzr, ge
  cbnz w0, br_check_proof.L5
  ldr x0, [sp, #16]
  ldr x17, =0
  subs xzr, x0, x17
  csinc w0, wzr, wzr, eq
  cbnz w0, br_check_proof.L8
  ldr x0, =-1
  b br_check_proof.L7
  br_check_proof.L8:
  ldr x0, [sp, #48]
  ldr x17, =2
  lslv x0, x0, x17
  ldr x1, [sp, #24]
  add x0, x1, x0
  ldrsw x0, [x0]
  b br_check_proof.L7
  br_check_proof.L7:
  cbnz w0, br_check_proof.L9
  b br_check_proof.L6
  br_check_proof.L9:
  ldr x0, [sp, #48]
  ldr x17, =3
  lslv x0, x0, x17
  ldr x1, [sp, #32]
  add x1, x1, x0
  ldr x1, [x1]
  ldr x2, [sp, #40]
  add x0, x2, x0
  ldr x0, [x0]
  add x2, x1, #0
  ldr x1, [sp, #48]
  add x3, x0, #0
  ldr x0, [sp]
  bl br_check_clause
  b br_check_proof.L6
  br_check_proof.L6:
  ldr x0, [sp, #48]
  ldr x17, =1
  add x0, x0, x17
  b br_check_proof.L4
  br_check_proof.L5:
  ldr x30, [sp, #56]
  add sp, sp, #64
  ret")

def lratCheckCode : Program := rupCode ++ (strictCode ++ (clauseCode ++ proofCode))

theorem rup_compile : compileFn isa rupFn = .ok rupCode := by kernel_rfl
theorem strict_compile : compileFn isa strictFn = .ok strictCode := by kernel_rfl
theorem clause_compile : compileFn isa clauseFn = .ok clauseCode := by kernel_rfl
theorem proof_compile : compileFn isa proofFn = .ok proofCode := by kernel_rfl

theorem lrat_module_compile :
    compile isa lratCheckFns = .ok lratCheckCode := by kernel_rfl

def lratBound : String → Nat := fun g =>
  if g = "br_check_clause_non_strictly_by_propagation" then 144
  else if g = "br_check_clause_strictly_by_resolution" then 80
  else if g = "br_check_clause" then 160
  else 224

private theorem rupFn_nslots : rupFn.nslots isa = 17 := by kernel_rfl
private theorem rupFn_callees : rupFn.opt.ext.callees = [] := by kernel_rfl
private theorem rupFn_exits : rupFn.opt.ext.exits = ["lrat_fail"] := by kernel_rfl

private theorem strictFn_nslots : strictFn.nslots isa = 9 := by kernel_rfl
private theorem strictFn_callees : strictFn.opt.ext.callees = [] := by kernel_rfl
private theorem strictFn_exits : strictFn.opt.ext.exits =
    ["lrat_fail", "lrat_fail", "lrat_fail", "lrat_fail",
     "lrat_fail", "lrat_fail", "lrat_fail", "lrat_fail"] := by kernel_rfl

private theorem clauseFn_nslots : clauseFn.nslots isa = 0 := by kernel_rfl
private theorem clauseFn_callees : clauseFn.opt.ext.callees =
    ["br_check_clause_strictly_by_resolution",
     "br_check_clause_non_strictly_by_propagation"] := by kernel_rfl
private theorem clauseFn_exits : clauseFn.opt.ext.exits = [] := by kernel_rfl

private theorem proofFn_nslots : proofFn.nslots isa = 7 := by kernel_rfl
private theorem proofFn_callees : proofFn.opt.ext.callees = ["br_check_clause"] := by kernel_rfl
private theorem proofFn_exits : proofFn.opt.ext.exits = [] := by kernel_rfl

section Generic
variable [hh : Host]

/-- Linking `lratCheckFns` (`checkRup`, `strictCheck`, `checkClause`, `checkProof`) via
`compile_correct` in any AArch64 host that also defines `"lrat_fail"`. -/
theorem lrat_module_fnspec (k₀ : Nat)
    (hc : lratCheckCode.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hfail : target.Defined hh "lrat_fail") (nX : Nat) (hnX : nX ≤ 80) :
    ∀ f ∈ lratCheckFns,
      target.FnSpec hh f.name (lratEnv f.name) (lratBound f.name) nX := by
  refine compile_correct (T := target) hh lratEnv lratBound nX lratCheckFns
    lratCheckCode k₀ lrat_module_compile hc hu ?_
  intro pre f post heq
  rcases pre with _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, _ | ⟨f4, pre⟩⟩⟩⟩
  · injection heq with hf _
    subst hf
    refine ⟨checkRup_wf, lratEnv_step.1, by rw [rupFn_nslots]; decide, by decide, ?_, ?_⟩
    · rw [rupFn_callees]; intro _ h; nomatch h
    · rw [rupFn_exits]
      intro g hg; simp only [List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact ⟨hfail, by simp [lratBound]; omega⟩
      · nomatch hg
  · injection heq with hf1 h1
    injection h1 with hf _
    subst hf1 hf
    refine ⟨strictCheck_wf, lratEnv_step.2.1, by rw [strictFn_nslots]; decide, by decide, ?_, ?_⟩
    · rw [strictFn_callees]; intro _ h; nomatch h
    · rw [strictFn_exits]
      intro g hg; simp only [List.mem_cons] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hg
      all_goals try exact ⟨hfail, by simp [lratBound]; omega⟩
      nomatch hg
  · injection heq with hf1 h1
    injection h1 with hf2 h2
    injection h2 with hf _
    subst hf1 hf2 hf
    refine ⟨checkClause_wf, lratEnv_step.2.2.1, by rw [clauseFn_nslots]; decide, by decide, ?_, ?_⟩
    · rw [clauseFn_callees]
      intro g hg; simp only [List.mem_cons] at hg
      rcases hg with rfl | rfl | hg
      · exact ⟨Or.inl (by simp), by rw [clauseFn_nslots]; decide⟩
      · exact ⟨Or.inl (by simp), by rw [clauseFn_nslots]; decide⟩
      · nomatch hg
    · rw [clauseFn_exits]; intro _ h; nomatch h
  · injection heq with hf1 h1
    injection h1 with hf2 h2
    injection h2 with hf3 h3
    injection h3 with hf _
    subst hf1 hf2 hf3 hf
    refine ⟨checkProof_wf, lratEnv_step.2.2.2, by rw [proofFn_nslots]; decide, by decide, ?_, ?_⟩
    · rw [proofFn_callees]
      intro g hg; simp only [List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact ⟨Or.inl (by simp), by rw [proofFn_nslots]; decide⟩
      · nomatch hg
    · rw [proofFn_exits]; intro _ h; nomatch h
  · simp [lratCheckFns] at heq

/-- End-to-end correctness of compiled `br_check_proof` on Kraken AArch64: in every host containing
`lratCheckCode` at `k₀` and `.label "lrat_fail"` at `k_fail` with unique labels, from a state
meeting `CheckProofPre` for formula `cnf₀` with `st` in `x0`, 224 bytes of stack space below `sp`,
return address `ra` in `x30`, and 16-byte aligned `sp`, execution of `br_check_proof` either:
* returns to `ra` with `cnf₀.Unsat` established, callee-saved registers `x19`–`x29` and `sp`
  restored, and `FullMemInv` preserved in memory; or
* exits to `"lrat_fail"` at `Host.addrOf k_fail` with a 16-byte aligned entry stack pointer. -/
theorem checkProof_arm64_correct (k₀ k_fail : Nat)
    (hc : lratCheckCode.IsInfixAt Host.prog k₀)
    (hfail : Host.prog[k_fail]? = some (.label "lrat_fail")) (hu : Host.LabelsUnique)
    {max_var n : Nat} {st_ptr : BitVec 64} {k₀_fields : KernelFields}
    {usedWords litsPtrs antePtrs trail_free0 : List Val} {cnf₀ : CNF Nat}
    {clauses : List (CNF.Clause Nat)} {litsTable anteTable : List (List Val)}
    {P_ro : Mem 64 → Prop} {m : Mem 64}
    (pre : CheckProofPre max_var n st_ptr k₀_fields usedWords litsPtrs antePtrs trail_free0 cnf₀
      clauses litsTable anteTable P_ro m)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = st_ptr)
    (hra : s.regs.X30 = ra.toUInt64)
    (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆
      (fun f => ∃ bs : List UInt8, bs.length = 224 ∧ f = bs.At (s.regs.SP.toBitVec - 224#64)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        (st.pc = ra ∧ cnf₀.Unsat ∧
          (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
            st.data.regs.getXReg r = s.regs.getXReg r) ∧
          st.data.regs.SP = s.regs.SP ∧
          ∃ m' k', FullMemInv max_var n trail_free0.length st_ptr k₀_fields P_ro k' m' ∧
            (st.data.dmem =⋆ Eq m' ⋆
              (fun f => ∃ bs : List UInt8, bs.length = 224 ∧ f = bs.At (s.regs.SP.toBitVec - 224#64)) ⋆ R)) ∨
        (st.pc = Host.addrOf k_fail ∧ st.data.regs.SP.toNat % 16 = 0))
      ⟨s, Host.addrOf (k₀ + rupCode.length + strictCode.length + clauseCode.length)⟩ := by
  obtain ⟨f_ab, f_rest, hu1, hd1, ⟨f_m, f_entry, hu2, hd2, rfl, hentry⟩, hrest⟩ := hmem
  let Q : LeanQbe.Post := fun rets m' =>
    rets = [] ∧ (∃ k', FullMemInv max_var n trail_free0.length st_ptr k₀_fields P_ro k' m') ∧ cnf₀.Unsat
  let X : XPost := fun g _ _ => g = "lrat_fail"
  have hspec : checkProofSpec [st_ptr] m Q X :=
    ⟨max_var, n, st_ptr, k₀_fields, usedWords, litsPtrs, antePtrs, trail_free0, cnf₀,
      clauses, litsTable, anteTable, P_ro, rfl, pre,
      fun _ hinv hunsat => ⟨rfl, hinv, hunsat⟩, fun _ _ => rfl⟩
  have hargs : target.ArgsIn [st_ptr] s := by
    simp [Target.ArgsIn, Target.ValsIn, argRegs, get_reg, hx0]
  have hlratBound : lratBound proofFn.name = 224 := rfl
  have hf := lrat_module_fnspec k₀ hc hu ⟨k_fail, hfail⟩ 80 (by decide) proofFn
    (by simp [lratCheckFns, proofFn]) [st_ptr] m Q X hspec s ra R hargs hra hsp
    (by
      simp only [Target.Entry, hlratBound, region_zero, Std.ExtHashMap.sep_emp]
      exact ⟨f_ab, f_rest, hu1, hd1, ⟨m, f_entry, hu2, hd2, rfl, hentry⟩, hrest⟩)
  have hproof_infix : proofCode.IsInfixAt Host.prog
      (k₀ + rupCode.length + strictCode.length + clauseCode.length) := by
    have h1 := hc.append.2.append.2.append.2
    simpa only [Nat.add_assoc] using h1
  have hlab : target.labelAddr hh proofFn.name =
      Host.addrOf (k₀ + rupCode.length + strictCode.length + clauseCode.length) :=
    labelAddr_of_unique (T := target) hu hproof_infix.cons.1
  have hflab : target.labelAddr hh "lrat_fail" = Host.addrOf k_fail :=
    labelAddr_of_unique (T := target) hu hfail
  rw [hlab] at hf
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st (⟨hpc, rets, m', ⟨rfl, ⟨k', hinv'⟩, hunsat⟩, -, ⟨hcs, hsp'⟩, hm'⟩ |
    ⟨sym', as', m', rfl, _, hpc, _, hspE, _⟩)
  · rw [Target.Exit, hlratBound] at hm'
    refine Or.inl ⟨hpc, hunsat, fun r hr => ?_, ?_, m', k', hinv',
      sep_mono (fun _ => sep_mono (fun _ h => h)) hm'⟩
    · have := hcs (.reg r) (by simp [calleeSaved] at hr ⊢; omega)
      exact UInt64.toBitVec_inj.mp this
    · have : get st.data .SP = get s .SP := by simpa using hsp'
      exact UInt64.toBitVec_inj.mp this
  · rw [hflab] at hpc
    exact Or.inr ⟨hpc, hspE⟩

end Generic

/-! ## Non-vacuity: concrete host and concrete memory `nvCheckBytes` -/

def lratProg : Program := lratCheckCode ++ [.label "lrat_fail"]

abbrev lratHost : Host :=
  .ofLayout lratProg (layoutOf lratProg) (layoutOf_zero _) (of_decide_eq_true (by kernel_rfl))

attribute [local instance] lratHost

theorem lratHost_unique : Host.LabelsUnique :=
  Host.labelsUnique_of_nodup (of_decide_eq_true (by kernel_rfl))

def zeros224 : List UInt8 := List.replicate 224 0

def lratState0 : MachineData :=
  { regs := { X0 := 0x1000, SP := 0x1000, X30 := (0x1234 : Int64).toUInt64 },
    dmem := (zeros224 ++ nvCheckBytes).At 0x0f20#64 }

theorem checkProof_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st =>
        (st.pc = 0x1234 ∧ (CNF.empty : CNF Nat).Unsat) ∨
        st.pc = Host.addrOf lratCheckCode.length)
      ⟨lratState0, Host.addrOf (rupCode.length + strictCode.length + clauseCode.length)⟩ := by
  have h224 : zeros224.length = 224 := List.length_replicate
  have hnv_len : nvCheckBytes.length = 210 := by
    simp [nvCheckBytes, bytesN_length, KernelFields.toList]
  have hmem : lratState0.dmem =⋆ Eq (nvCheckBytes.At 0x1000#64) ⋆
      (fun f => ∃ bs : List UInt8, bs.length = 224 ∧ f = bs.At (lratState0.regs.SP.toBitVec - 224#64)) ⋆
      Std.ExtHashMap.emp := by
    rw [Std.ExtHashMap.sep_emp, Std.ExtHashMap.sep_comm]
    have h1 := Mem.At_append_sep zeros224 nvCheckBytes 0x0f20#64 (by simp [h224, hnv_len])
    have e1 : (0x0f20#64 + BitVec.ofNat 64 zeros224.length) = 0x1000#64 := by simp [h224]
    rw [e1] at h1
    have h0 : (Eq ((zeros224 ++ nvCheckBytes).At 0x0f20#64)) lratState0.dmem := rfl
    rw [h1] at h0
    exact sep_mono (fun f hf => ⟨zeros224, h224, hf.symm⟩) h0
  have hc : lratCheckCode.IsInfixAt Host.prog 0 := ⟨[.label "lrat_fail"], rfl⟩
  have hfail : Host.prog[lratCheckCode.length]? = some (.label "lrat_fail") :=
    of_decide_eq_true (by kernel_rfl)
  have h := checkProof_arm64_correct 0 lratCheckCode.length hc hfail lratHost_unique nvCheck_pre
    lratState0 0x1234 Std.ExtHashMap.emp rfl rfl
    (show (0x1000 : UInt64).toNat % 16 = 0 by decide) hmem
  rw [Nat.zero_add] at h
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st (⟨hpc, hunsat, -⟩ | ⟨hpc, -⟩)
  · exact Or.inl ⟨hpc, hunsat⟩
  · exact Or.inr hpc

end LeanQbe.Arm64.LratTrim
