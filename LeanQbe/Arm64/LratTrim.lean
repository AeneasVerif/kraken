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
* `br_check_clause_non_strictly_by_propagation` (`LratRup.checkRup`, 4 spill slots, 48-byte frame, 80-byte bound)
* `br_check_clause_strictly_by_resolution` (`LratTrim.strictCheck`, 3 spill slots, 32-byte frame, 80-byte bound)
* `br_check_clause` (`LratTrim.checkClause`, 0 spill slots, 16-byte frame, 96-byte bound)
* `br_check_proof` (`LratTrim.checkProof`, 7 spill slots, 64-byte frame, 160-byte bound)

through the full verified pipeline (`compileModule Arm64.isa`), checks the emitted AArch64 assembly
and stack bounds in the kernel (`kernel_rfl`), links all four contracts via `compile_sound` and
`lratEnv_sound` (`lrat_module_fnspec`), and proves the closed Kraken-AArch64 end-to-end theorem
`checkProof_arm64_correct` concluding `cnf₀.Unsat` on normal return (or exit to `"lrat_fail"`),
plus a concrete-byte non-vacuity instance `checkProof_arm64_nonvacuous` and a concrete accepting
UNSAT instance `checkProof_arm64_accepts` (for `[[1], [-1]]` concluding `st.pc = 0x1234 ∧ nvAcceptCnf.Unsat`).
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
  sub sp, sp, #48
  str x30, [sp, #32]
  str x19, [sp, #8]
  str x20, [sp, #16]
  str x21, [sp, #24]
  str x1, [sp]
  add x9, x3, #0
  add x4, x2, #0
  add x19, x0, #0
  add x0, x19, #16
  ldr x21, [x0]
  add x0, x19, #24
  ldr x8, [x0]
  add x0, x19, #40
  ldr x20, [x0]
  add x13, x19, #48
  ldr x0, [x13]
  add x14, x19, #144
  ldr x7, [x14]
  add x7, x7, #1
  add x19, x19, #152
  ldr x1, [x19]
  br_check_clause_non_strictly_by_propagation.L3:
  ldrsw x2, [x4]
  cbnz w2, br_check_clause_non_strictly_by_propagation.L4
  b br_check_clause_non_strictly_by_propagation.L2
  br_check_clause_non_strictly_by_propagation.L4:
  ldr x17, =63
  asrv x3, x2, x17
  eor x5, x2, x3
  sub x5, x5, x3
  add x5, x8, x5
  ldrsb x6, [x5]
  eor x6, x6, x3
  sub x3, x6, x3
  add x4, x4, #4
  subs xzr, x3, #0
  b.lt br_check_clause_non_strictly_by_propagation.L5
  subs xzr, x3, #0
  b.gt br_check_clause_non_strictly_by_propagation.L6
  ldr x16, =0
  sub x2, x16, x2
  ldr x17, =63
  asrv x3, x2, x17
  ldr x17, =1
  orr x3, x3, x17
  strb w3, [x5]
  str w2, [x0]
  add x0, x0, #4
  add x1, x1, #1
  b br_check_clause_non_strictly_by_propagation.L3
  br_check_clause_non_strictly_by_propagation.L6:
  add x3, x0, #0
  add x6, x7, #0
  add x4, x1, #0
  b br_check_clause_non_strictly_by_propagation.L1
  br_check_clause_non_strictly_by_propagation.L5:
  b br_check_clause_non_strictly_by_propagation.L3
  br_check_clause_non_strictly_by_propagation.L2:
  add x6, x7, #0
  add x3, x1, #0
  add x1, x0, #0
  br_check_clause_non_strictly_by_propagation.L7:
  ldrsw x2, [x9]
  cbnz w2, br_check_clause_non_strictly_by_propagation.L8
  ldr x0, =3
  ldr x2, =0
  b br_check_clause_non_strictly_by_propagation.L0
  br_check_clause_non_strictly_by_propagation.L8:
  subs xzr, x2, #0
  b.lt br_check_clause_non_strictly_by_propagation.L9
  ldr x17, =3
  lslv x0, x2, x17
  add x0, x21, x0
  ldr x7, [x0]
  add x6, x6, #1
  ldr x4, =0
  br_check_clause_non_strictly_by_propagation.L11:
  ldrsw x0, [x7]
  cbnz w0, br_check_clause_non_strictly_by_propagation.L12
  b br_check_clause_non_strictly_by_propagation.L10
  br_check_clause_non_strictly_by_propagation.L12:
  ldr x17, =63
  asrv x5, x0, x17
  eor x10, x0, x5
  sub x10, x10, x5
  add x10, x8, x10
  ldrsb x11, [x10]
  eor x11, x11, x5
  sub x11, x11, x5
  add x7, x7, #4
  subs xzr, x11, #0
  b.lt br_check_clause_non_strictly_by_propagation.L13
  cbnz w4, br_check_clause_non_strictly_by_propagation.L15
  b br_check_clause_non_strictly_by_propagation.L14
  br_check_clause_non_strictly_by_propagation.L15:
  subs xzr, x4, x0
  b.eq br_check_clause_non_strictly_by_propagation.L16
  ldr x0, =2
  b br_check_clause_non_strictly_by_propagation.L0
  br_check_clause_non_strictly_by_propagation.L16:
  br_check_clause_non_strictly_by_propagation.L14:
  subs xzr, x11, #0
  b.eq br_check_clause_non_strictly_by_propagation.L17
  add x4, x0, #0
  b br_check_clause_non_strictly_by_propagation.L11
  br_check_clause_non_strictly_by_propagation.L17:
  ldr x17, =1
  orr x5, x5, x17
  strb w5, [x10]
  str w0, [x1]
  add x1, x1, #4
  add x3, x3, #1
  add x4, x0, #0
  b br_check_clause_non_strictly_by_propagation.L11
  br_check_clause_non_strictly_by_propagation.L13:
  ldr x16, =0
  sub x0, x16, x0
  subs xzr, x4, x0
  b.eq br_check_clause_non_strictly_by_propagation.L18
  b br_check_clause_non_strictly_by_propagation.L11
  br_check_clause_non_strictly_by_propagation.L18:
  ldr x0, =2
  b br_check_clause_non_strictly_by_propagation.L0
  br_check_clause_non_strictly_by_propagation.L10:
  cbnz w4, br_check_clause_non_strictly_by_propagation.L19
  add x4, x3, #0
  add x3, x1, #0
  b br_check_clause_non_strictly_by_propagation.L1
  br_check_clause_non_strictly_by_propagation.L19:
  add x9, x9, #4
  b br_check_clause_non_strictly_by_propagation.L7
  br_check_clause_non_strictly_by_propagation.L9:
  ldr x0, =1
  b br_check_clause_non_strictly_by_propagation.L0
  br_check_clause_non_strictly_by_propagation.L1:
  add x0, x20, #0
  br_check_clause_non_strictly_by_propagation.L20:
  subs xzr, x0, x3
  b.eq br_check_clause_non_strictly_by_propagation.L21
  ldrsw x1, [x0]
  ldr x17, =63
  asrv x2, x1, x17
  eor x1, x1, x2
  sub x1, x1, x2
  add x1, x8, x1
  ldr x17, =0
  strb w17, [x1]
  add x0, x0, #4
  b br_check_clause_non_strictly_by_propagation.L20
  br_check_clause_non_strictly_by_propagation.L21:
  str x20, [x13]
  str x6, [x14]
  str x4, [x19]
  ldr x19, [sp, #8]
  ldr x20, [sp, #16]
  ldr x21, [sp, #24]
  ldr x30, [sp, #32]
  add sp, sp, #48
  ret
  br_check_clause_non_strictly_by_propagation.L0:
  str x1, [x13]
  str x6, [x14]
  str x3, [x19]
  ldr x1, [sp]
  ldr x3, =0
  ldr x4, =0
  ldr x19, [sp, #8]
  ldr x20, [sp, #16]
  ldr x21, [sp, #24]
  ldr x30, [sp, #32]
  add sp, sp, #48
  b lrat_fail")

def strictCode : Program := parseAArch64("br_check_clause_strictly_by_resolution:
  sub sp, sp, #32
  str x30, [sp, #24]
  str x19, [sp, #8]
  str x20, [sp, #16]
  str x2, [sp]
  add x19, x3, #0
  add x10, x0, #0
  add x0, x19, #0
  br_check_clause_strictly_by_resolution.L1:
  ldrsw x2, [x0]
  cbnz w2, br_check_clause_strictly_by_resolution.L2
  b br_check_clause_strictly_by_resolution.L0
  br_check_clause_strictly_by_resolution.L2:
  subs xzr, x2, #0
  b.lt br_check_clause_strictly_by_resolution.L3
  add x0, x0, #4
  b br_check_clause_strictly_by_resolution.L1
  br_check_clause_strictly_by_resolution.L3:
  ldr x0, =1
  ldr x3, =0
  ldr x4, =0
  ldr x19, [sp, #8]
  ldr x20, [sp, #16]
  ldr x30, [sp, #24]
  add sp, sp, #32
  b lrat_fail
  br_check_clause_strictly_by_resolution.L0:
  add x2, x10, #16
  ldr x20, [x2]
  add x2, x10, #32
  ldr x11, [x2]
  add x10, x10, #144
  ldr x2, [x10]
  add x8, x0, #0
  add x0, x2, #0
  ldr x6, =0
  ldr x7, =1
  br_check_clause_strictly_by_resolution.L5:
  subs xzr, x8, x19
  b.eq br_check_clause_strictly_by_resolution.L6
  sub x8, x8, #4
  ldrsw x5, [x8]
  ldr x17, =3
  lslv x2, x5, x17
  add x2, x20, x2
  ldr x9, [x2]
  add x0, x0, #1
  ldr x3, =0
  br_check_clause_strictly_by_resolution.L8:
  ldrsw x2, [x9]
  cbnz w2, br_check_clause_strictly_by_resolution.L9
  b br_check_clause_strictly_by_resolution.L7
  br_check_clause_strictly_by_resolution.L9:
  ldr x17, =63
  asrv x4, x2, x17
  eor x12, x2, x4
  sub x12, x12, x4
  add x12, x11, x12
  ldrsb x13, [x12]
  add x9, x9, #4
  subs xzr, x13, #0
  b.eq br_check_clause_strictly_by_resolution.L10
  eor x13, x13, x4
  sub x13, x13, x4
  subs xzr, x13, #0
  b.gt br_check_clause_strictly_by_resolution.L11
  cbnz w3, br_check_clause_strictly_by_resolution.L12
  add x3, x2, #0
  b br_check_clause_strictly_by_resolution.L8
  br_check_clause_strictly_by_resolution.L12:
  str x0, [x10]
  add x4, x5, #0
  add x16, x2, #0
  add x2, x3, #0
  add x3, x16, #0
  ldr x0, =4
  ldr x19, [sp, #8]
  ldr x20, [sp, #16]
  ldr x30, [sp, #24]
  add sp, sp, #32
  b lrat_fail
  br_check_clause_strictly_by_resolution.L11:
  b br_check_clause_strictly_by_resolution.L8
  br_check_clause_strictly_by_resolution.L10:
  ldr x17, =1
  orr x4, x4, x17
  strb w4, [x12]
  add x6, x6, #1
  b br_check_clause_strictly_by_resolution.L8
  br_check_clause_strictly_by_resolution.L7:
  cbnz w7, br_check_clause_strictly_by_resolution.L13
  cbnz w3, br_check_clause_strictly_by_resolution.L14
  str x0, [x10]
  add x2, x5, #0
  ldr x0, =5
  ldr x3, =0
  ldr x4, =0
  ldr x19, [sp, #8]
  ldr x20, [sp, #16]
  ldr x30, [sp, #24]
  add sp, sp, #32
  b lrat_fail
  br_check_clause_strictly_by_resolution.L14:
  ldr x17, =63
  asrv x2, x3, x17
  eor x3, x3, x2
  sub x3, x3, x2
  add x2, x11, x3
  ldr x17, =0
  strb w17, [x2]
  sub x6, x6, #1
  b br_check_clause_strictly_by_resolution.L5
  br_check_clause_strictly_by_resolution.L13:
  cbnz w3, br_check_clause_strictly_by_resolution.L15
  ldr x7, =0
  b br_check_clause_strictly_by_resolution.L5
  br_check_clause_strictly_by_resolution.L15:
  str x0, [x10]
  ldr x16, =0
  sub x2, x16, x3
  add x4, x5, #0
  ldr x0, =4
  ldr x19, [sp, #8]
  ldr x20, [sp, #16]
  ldr x30, [sp, #24]
  add sp, sp, #32
  b lrat_fail
  br_check_clause_strictly_by_resolution.L6:
  br_check_clause_strictly_by_resolution.L4:
  str x0, [x10]
  cbnz w7, br_check_clause_strictly_by_resolution.L16
  ldr x3, [sp]
  add x4, x6, #0
  br_check_clause_strictly_by_resolution.L18:
  ldrsw x2, [x3]
  cbnz w2, br_check_clause_strictly_by_resolution.L19
  b br_check_clause_strictly_by_resolution.L17
  br_check_clause_strictly_by_resolution.L19:
  ldr x17, =63
  asrv x0, x2, x17
  eor x5, x2, x0
  sub x5, x5, x0
  add x5, x11, x5
  ldrsb x6, [x5]
  subs xzr, x6, #0
  b.eq br_check_clause_strictly_by_resolution.L20
  eor x6, x6, x0
  sub x6, x6, x0
  subs xzr, x6, #0
  b.lt br_check_clause_strictly_by_resolution.L21
  ldr x17, =0
  strb w17, [x5]
  sub x4, x4, #1
  add x3, x3, #4
  b br_check_clause_strictly_by_resolution.L18
  br_check_clause_strictly_by_resolution.L21:
  ldr x0, =7
  ldr x3, =0
  ldr x4, =0
  ldr x19, [sp, #8]
  ldr x20, [sp, #16]
  ldr x30, [sp, #24]
  add sp, sp, #32
  b lrat_fail
  br_check_clause_strictly_by_resolution.L20:
  ldr x0, =6
  ldr x3, =0
  ldr x4, =0
  ldr x19, [sp, #8]
  ldr x20, [sp, #16]
  ldr x30, [sp, #24]
  add sp, sp, #32
  b lrat_fail
  br_check_clause_strictly_by_resolution.L17:
  subs xzr, x4, #0
  b.ne br_check_clause_strictly_by_resolution.L22
  ldr x19, [sp, #8]
  ldr x20, [sp, #16]
  ldr x30, [sp, #24]
  add sp, sp, #32
  ret
  br_check_clause_strictly_by_resolution.L22:
  add x2, x4, #0
  ldr x0, =8
  ldr x3, =0
  ldr x4, =0
  ldr x19, [sp, #8]
  ldr x20, [sp, #16]
  ldr x30, [sp, #24]
  add sp, sp, #32
  b lrat_fail
  br_check_clause_strictly_by_resolution.L16:
  ldr x0, =3
  ldr x2, =0
  ldr x3, =0
  ldr x4, =0
  ldr x19, [sp, #8]
  ldr x20, [sp, #16]
  ldr x30, [sp, #24]
  add sp, sp, #32
  b lrat_fail")

def clauseCode : Program := parseAArch64("br_check_clause:
  sub sp, sp, #16
  str x30, [sp]
  add x4, x0, #128
  ldr x5, [x4]
  add x5, x5, #1
  str x5, [x4]
  ldr w4, [x2]
  subs xzr, x4, #0
  b.eq br_check_clause.L1
  b br_check_clause.L0
  br_check_clause.L1:
  add x4, x0, #136
  ldr x5, [x4]
  add x5, x5, #1
  str x5, [x4]
  br_check_clause.L0:
  add x4, x0, #80
  ldr x4, [x4]
  subs xzr, x4, #0
  b.ne br_check_clause.L2
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
  str x19, [sp]
  str x20, [sp, #8]
  str x21, [sp, #16]
  str x22, [sp, #24]
  str x23, [sp, #32]
  str x24, [sp, #40]
  str x25, [sp, #48]
  add x20, x0, #0
  add x0, x20, #96
  ldr x0, [x0]
  add x1, x20, #104
  ldr x1, [x1]
  add x2, x20, #64
  ldrsw x21, [x2]
  add x2, x20, #72
  ldrsw x19, [x2]
  subs xzr, x0, #0
  b.ne br_check_proof.L0
  ldr x19, [sp]
  ldr x20, [sp, #8]
  ldr x21, [sp, #16]
  ldr x22, [sp, #24]
  ldr x23, [sp, #32]
  ldr x24, [sp, #40]
  ldr x25, [sp, #48]
  ldr x30, [sp, #56]
  add sp, sp, #64
  ret
  br_check_proof.L0:
  subs xzr, x1, #0
  b.eq br_check_proof.L1
  ldr x19, [sp]
  ldr x20, [sp, #8]
  ldr x21, [sp, #16]
  ldr x22, [sp, #24]
  ldr x23, [sp, #32]
  ldr x24, [sp, #40]
  ldr x25, [sp, #48]
  ldr x30, [sp, #56]
  add sp, sp, #64
  ret
  br_check_proof.L1:
  cbnz w21, br_check_proof.L2
  ldr x19, [sp]
  ldr x20, [sp, #8]
  ldr x21, [sp, #16]
  ldr x22, [sp, #24]
  ldr x23, [sp, #32]
  ldr x24, [sp, #40]
  ldr x25, [sp, #48]
  ldr x30, [sp, #56]
  add sp, sp, #64
  ret
  br_check_proof.L2:
  cbnz w19, br_check_proof.L3
  ldr x19, [sp]
  ldr x20, [sp, #8]
  ldr x21, [sp, #16]
  ldr x22, [sp, #24]
  ldr x23, [sp, #32]
  ldr x24, [sp, #40]
  ldr x25, [sp, #48]
  ldr x30, [sp, #56]
  add sp, sp, #64
  ret
  br_check_proof.L3:
  add x0, x20, #88
  ldr x22, [x0]
  ldr x23, [x20]
  add x0, x20, #16
  ldr x24, [x0]
  add x0, x20, #8
  ldr x25, [x0]
  br_check_proof.L4:
  subs xzr, x21, x19
  b.lt br_check_proof.L5
  subs xzr, x22, #0
  b.ne br_check_proof.L8
  ldr x0, =-1
  b br_check_proof.L7
  br_check_proof.L8:
  ldr x17, =2
  lslv x0, x19, x17
  add x0, x23, x0
  ldrsw x0, [x0]
  br_check_proof.L7:
  cbnz w0, br_check_proof.L9
  b br_check_proof.L6
  br_check_proof.L9:
  ldr x17, =3
  lslv x0, x19, x17
  add x1, x24, x0
  ldr x2, [x1]
  add x0, x25, x0
  ldr x3, [x0]
  add x0, x20, #0
  add x1, x19, #0
  bl br_check_clause
  br_check_proof.L6:
  add x19, x19, #1
  b br_check_proof.L4
  br_check_proof.L5:
  ldr x19, [sp]
  ldr x20, [sp, #8]
  ldr x21, [sp, #16]
  ldr x22, [sp, #24]
  ldr x23, [sp, #32]
  ldr x24, [sp, #40]
  ldr x25, [sp, #48]
  ldr x30, [sp, #56]
  add sp, sp, #64
  ret")

def lratCheckCode : Program := rupCode ++ (strictCode ++ (clauseCode ++ proofCode))

def lratBounds : List (String × Nat) :=
  [("br_check_clause_non_strictly_by_propagation", 80),
   ("br_check_clause_strictly_by_resolution", 80),
   ("br_check_clause", 96),
   ("br_check_proof", 160)]

theorem rup_compile : compileFn isa rupFn = .ok rupCode := by kernel_rfl
theorem strict_compile : compileFn isa strictFn = .ok strictCode := by kernel_rfl
theorem clause_compile : compileFn isa clauseFn = .ok clauseCode := by kernel_rfl
theorem proof_compile : compileFn isa proofFn = .ok proofCode := by kernel_rfl

theorem lrat_module_compile :
    compileModule isa 0 [] ["lrat_fail"] 80 lratCheckFns =
      .ok (lratCheckCode, lratBounds) := by kernel_rfl

section Generic
variable [hh : Host]

/-- Linking `lratCheckFns` (`checkRup`, `strictCheck`, `checkClause`, `checkProof`) via
`compile_sound` in any AArch64 host that also defines `"lrat_fail"`. -/
theorem lrat_module_fnspec (k₀ : Nat)
    (hc : lratCheckCode.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hfail : target.Defined hh "lrat_fail") :
    ∀ p ∈ lratBounds,
      target.Defined hh p.1 ∧ target.FnSpec hh p.1 (lratEnv p.1) p.2 80 := by
  refine compile_sound (T := target) hh lratEnv [] ["lrat_fail"] 80 lratCheckFns
    lratCheckCode lratBounds k₀ lrat_module_compile hc hu lratCheckFns_wf lratEnv_sound
    (fun _ h => nomatch h) ?_
  intro g hg
  simp only [List.mem_singleton] at hg
  subst hg
  exact hfail

/-- End-to-end correctness of compiled `br_check_proof` on Kraken AArch64: in every host containing
`lratCheckCode` at `k₀` and defining `"lrat_fail"` with unique labels, from a state at
`Labels.label "br_check_proof"` meeting `CheckProofPre` for formula `cnf₀` with `st` in `x0`, 160
bytes of stack space below `sp`, return address `ra` in `x30`, and 16-byte aligned `sp`, execution
of `br_check_proof` either:
* returns to `ra` with `cnf₀.Unsat` established, callee-saved registers `x19`–`x29` and `sp`
  restored, and `FullMemInv` preserved in memory; or
* exits to `"lrat_fail"` at `Labels.label "lrat_fail"` with a 16-byte aligned entry stack pointer. -/
theorem checkProof_arm64_correct (k₀ : Nat)
    (hc : lratCheckCode.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hfail : target.Defined hh "lrat_fail")
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
      (fun f => ∃ bs : List UInt8, bs.length = 160 ∧ f = bs.At (s.regs.SP.toBitVec - 160#64)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        (st.pc = ra ∧ cnf₀.Unsat ∧
          (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
            st.data.regs.getXReg r = s.regs.getXReg r) ∧
          st.data.regs.SP = s.regs.SP ∧
          ∃ m' k', FullMemInv max_var n trail_free0.length st_ptr k₀_fields P_ro k' m' ∧
            (st.data.dmem =⋆ Eq m' ⋆
              (fun f => ∃ bs : List UInt8, bs.length = 160 ∧ f = bs.At (s.regs.SP.toBitVec - 160#64)) ⋆ R)) ∨
        (st.pc = Labels.label "lrat_fail" ∧ st.data.regs.SP.toNat % 16 = 0))
      ⟨s, Labels.label "br_check_proof"⟩ := by
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
  have hf := (lrat_module_fnspec k₀ hc hu hfail ("br_check_proof", 160) (by simp [lratBounds])).2
    [st_ptr] m Q X hspec s ra R hargs hra hsp
    (by
      simp only [Target.Entry, region_zero, Std.ExtHashMap.sep_emp]
      exact ⟨f_ab, f_rest, hu1, hd1, ⟨m, f_entry, hu2, hd2, rfl, hentry⟩, hrest⟩)
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st (⟨hpc, rets, m', ⟨rfl, ⟨k', hinv'⟩, hunsat⟩, -, ⟨hcs, hsp'⟩, hm'⟩ |
    ⟨sym', as', m', rfl, _, hpc, _, hspE, _⟩)
  · rw [Target.Exit] at hm'
    refine Or.inl ⟨hpc, hunsat, fun r hr => ?_, ?_, m', k', hinv',
      sep_mono (fun _ => sep_mono (fun _ h => h)) hm'⟩
    · have := hcs (.reg r) (by simp [calleeSaved] at hr ⊢; omega)
      exact UInt64.toBitVec_inj.mp this
    · have : get st.data .SP = get s .SP := by simpa using hsp'
      exact UInt64.toBitVec_inj.mp this
  · exact Or.inr ⟨hpc, hspE⟩

end Generic

/-! ## Non-vacuity: concrete host and concrete memory `nvCheckBytes` -/

def lratProg : Program := lratCheckCode ++ [.label "lrat_fail"]

abbrev lratHost : Host :=
  .ofLayout lratProg (layoutOf lratProg) (layoutOf_zero _) (of_decide_eq_true (by kernel_rfl))

attribute [local instance] lratHost

theorem lratHost_prog : Host.prog = lratProg := rfl

theorem lratHost_unique : Host.LabelsUnique :=
  Host.labelsUnique_of_nodup (of_decide_eq_true (by kernel_rfl))

def zeros160 : List UInt8 := List.replicate 160 0

def lratState0 : MachineData :=
  { regs := { X0 := 0x1000, SP := 0x1000, X30 := (0x1234 : Int64).toUInt64 },
    dmem := (zeros160 ++ nvCheckBytes).At 0x0f60#64 }

theorem checkProof_arm64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st =>
        (st.pc = 0x1234 ∧ (CNF.empty : CNF Nat).Unsat) ∨
        st.pc = Labels.label "lrat_fail")
      ⟨lratState0, Labels.label "br_check_proof"⟩ := by
  have h160 : zeros160.length = 160 := List.length_replicate
  have hnv_len : nvCheckBytes.length = 210 := by
    simp [nvCheckBytes, bytesN_length, KernelFields.toList]
  have hmem : lratState0.dmem =⋆ Eq (nvCheckBytes.At 0x1000#64) ⋆
      (fun f => ∃ bs : List UInt8, bs.length = 160 ∧ f = bs.At (lratState0.regs.SP.toBitVec - 160#64)) ⋆
      Std.ExtHashMap.emp := by
    rw [Std.ExtHashMap.sep_emp, Std.ExtHashMap.sep_comm]
    have h1 := Mem.At_append_sep zeros160 nvCheckBytes 0x0f60#64 (by simp [h160, hnv_len])
    have e1 : (0x0f60#64 + BitVec.ofNat 64 zeros160.length) = 0x1000#64 := by simp [h160]
    rw [e1] at h1
    have h0 : (Eq ((zeros160 ++ nvCheckBytes).At 0x0f60#64)) lratState0.dmem := rfl
    rw [h1] at h0
    exact sep_mono (fun f hf => ⟨zeros160, h160, hf.symm⟩) h0
  have hc : lratCheckCode.IsInfixAt Host.prog 0 := by
    rw [lratHost_prog]; exact ⟨[.label "lrat_fail"], rfl⟩
  have hfail : target.Defined lratHost "lrat_fail" := by
    refine ⟨lratCheckCode.length, ?_⟩
    change Host.prog[lratCheckCode.length]? = some (.label "lrat_fail")
    rw [lratHost_prog, lratProg, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have h := checkProof_arm64_correct 0 hc lratHost_unique hfail nvCheck_pre
    lratState0 0x1234 Std.ExtHashMap.emp rfl rfl
    (show (0x1000 : UInt64).toNat % 16 = 0 by decide) hmem
  refine eventually_weaken _ _ _ _ ?_ h
  rintro st (⟨hpc, hunsat, -⟩ | ⟨hpc, -⟩)
  · exact Or.inl ⟨hpc, hunsat⟩
  · exact Or.inr hpc

/-! ## Accepting UNSAT instance: concrete bytes `nvAcceptBytes` (`[[1], [-1]]`) -/

theorem lrat_accepts_fnspec [hh : Host] (k₀ : Nat)
    (hc : lratCheckCode.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hfail : target.Defined hh "lrat_fail") :
    ∀ p ∈ lratBounds,
      target.Defined hh p.1 ∧ target.FnSpec hh p.1 (lratAcceptEnv p.1) p.2 80 := by
  refine compile_sound (T := target) hh lratAcceptEnv [] ["lrat_fail"] 80 lratCheckFns
    lratCheckCode lratBounds k₀ lrat_module_compile hc hu lratCheckFns_wf lratAcceptEnv_sound
    (fun _ h => nomatch h) ?_
  intro g hg
  simp only [List.mem_singleton] at hg
  subst hg
  exact hfail

def lratAcceptState0 : MachineData :=
  { regs := { X0 := 0x1000, SP := 0x1000, X30 := (0x1234 : Int64).toUInt64 },
    dmem := (zeros160 ++ nvAcceptBytes).At 0x0f60#64 }

theorem checkProof_arm64_accepts :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ nvAcceptCnf.Unsat)
      ⟨lratAcceptState0, Labels.label "br_check_proof"⟩ := by
  have h160 : zeros160.length = 160 := List.length_replicate
  have hacc_len : nvAcceptBytes.length = 274 := nvAcceptBytes_length
  have hc : lratCheckCode.IsInfixAt Host.prog 0 := by
    rw [lratHost_prog]; exact ⟨[.label "lrat_fail"], rfl⟩
  have hfail : target.Defined lratHost "lrat_fail" := by
    refine ⟨lratCheckCode.length, ?_⟩
    change Host.prog[lratCheckCode.length]? = some (.label "lrat_fail")
    rw [lratHost_prog, lratProg, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have hmem : target.mem lratAcceptState0 =⋆ Eq (nvAcceptBytes.At 0x1000#64) ⋆
      target.Entry (target.get lratAcceptState0 target.sp) (0x1234 : Int64) 160 ⋆
      Std.ExtHashMap.emp := by
    simp only [Target.Entry, region_zero, Std.ExtHashMap.sep_emp]
    rw [Std.ExtHashMap.sep_comm]
    have h1 := Mem.At_append_sep zeros160 nvAcceptBytes 0x0f60#64 (by simp [h160, hacc_len])
    have e1 : (0x0f60#64 + BitVec.ofNat 64 zeros160.length) = 0x1000#64 := by simp [h160]
    rw [e1] at h1
    have h0 : (Eq ((zeros160 ++ nvAcceptBytes).At 0x0f60#64)) lratAcceptState0.dmem := rfl
    rw [h1] at h0
    exact sep_mono (fun f hf => ⟨zeros160, h160, hf.symm⟩) h0
  have hargs : target.ArgsIn [0x1000] lratAcceptState0 := by
    simp [Target.ArgsIn, Target.ValsIn, argRegs, get_reg, lratAcceptState0]
    rfl
  have hf := (lrat_accepts_fnspec 0 hc lratHost_unique hfail ("br_check_proof", 160)
    (by simp [lratBounds])).2
    [0x1000] (nvAcceptBytes.At 0x1000)
    (fun rs m' => rs = [] ∧ nvAcceptMem nvAcceptK2 Std.ExtHashMap.emp m' ∧ nvAcceptCnf.Unsat)
    (fun _ _ _ => False)
    checkProof_accepts_nonvacuous lratAcceptState0 0x1234 Std.ExtHashMap.emp hargs rfl
    (show (0x1000 : UInt64).toNat % 16 = 0 by decide) hmem
  refine eventually_weaken _ _ _ _ ?_ hf
  rintro st (⟨hpc, _, _, ⟨_, _, hunsat⟩, -⟩ | ⟨_, _, _, hx, _⟩)
  · exact ⟨hpc, hunsat⟩
  · exact hx.elim

end LeanQbe.Arm64.LratTrim
