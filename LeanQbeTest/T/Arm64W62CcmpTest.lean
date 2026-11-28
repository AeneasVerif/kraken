module

import LeanQbe.T.Arm64.TargLemmas
import LeanQbe.T.Arm64.IselCcmpLemmas
import LeanQbe.T.RegaLemmas4
import LeanQbe.T.RegaFlatLemmas
import LeanQbe.T.MainLemmas
import LeanQbe.T.Driver
import LeanQbe.T.MainInline
import LeanQbe.T.Examples.Kissat.Plain
import LeanQbeTest.T.Arm64DirPreds
import LeanQbeTest.T.RegaTestKit
meta import LeanQbe.T.Arm64.TargLemmas
meta import LeanQbe.T.Arm64.IselCcmpLemmas
meta import LeanQbe.T.RegaLemmas4
meta import LeanQbe.T.RegaFlatLemmas
meta import LeanQbe.T.MainLemmas
meta import LeanQbe.T.Driver
meta import LeanQbe.T.MainInline
meta import LeanQbe.T.Examples.Kissat.Plain
meta import LeanQbeTest.T.Arm64DirPreds
meta import LeanQbeTest.T.RegaTestKit
meta import Kraken.AArch64.Print

/-!
# Arm64 Wave 6.2-B (`OPT-8`: `CCMP`/`CCMN` + `CSNEG`) Activation Tests

End-to-end `Live` -> `Spill` -> `Rega` -> `Arm64.Isel` activation `#guard`s for the verified
Arm64 Wave 6.2-B bundle (`OPT-8` conditional compare `CCMP`/`CCMN` and conditional negation
`CSNEG`), checked against the same compiler with the `OPT-8` `GprIsa` hooks switched off
(`armIsaNoOpt8`):

* **`CCMP_imm` / `CCMP_reg` / `CCMN_imm`**: flag-chained multi-branch compare lowering (`||` and
  `&&` short-circuit patterns) without intermediate branches or `cset`.
* **`CSNEG`**: conditional negation for `select c x (-x)` / `select c (-x) x` at 32-bit and
  64-bit widths (both flag-condition and GPR-bool inputs).
* Real `Kissat.Plain` hot functions emit strictly fewer instructions with `OPT-8` on, and `#print
  axioms` confirms `std3`-only soundness.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.Arm64W62CcmpTest

open LeanQbe.T LeanQbe.T.Arm64
open LeanQbeTest.T.RegaTestKit LeanQbeTest.T.Arm64DirPreds

/-! ## 1. Compilation & Inspection Helpers -/

/-- `armTarget.toIsa` with Wave 6.2-B `OPT-8` (`ccmp?`, `selectNeg?`) switched off. -/
meta def armIsaNoOpt8 : Isa :=
  { armTarget.toIsa with
    gpr :=
      { armGpr with
        ccmp? := none
        selectNeg? := none } }

meta def armChk (fs : List Fn) : Bool :=
  chk armTarget armLayout armLegalTarget fs

meta def armCode (fs : List Fn) : List armTarget.toIsa.Directive :=
  codeOf armTarget armLegalTarget fs

meta def armCodeOff (fs : List Fn) : List Directive :=
  extractCode (compileModule armIsaNoOpt8 armLegalTarget 0 [] [] 0 fs
    (fs.map (Fn.computeHints armIsaNoOpt8 armLegalTarget)))

meta def isInstrDir : Directive → Bool
  | .instr _ => true
  | _ => false

meta def insnCount (ds : List Directive) : Nat :=
  countDirs isInstrDir ds

meta def isCcmpRegDir : Directive → Bool
  | .instr { operation := .CCMP_reg .., .. } => true
  | _ => false

meta def isCcmpImmDir : Directive → Bool
  | .instr { operation := .CCMP_imm .., .. } => true
  | _ => false

meta def isCcmnImmDir : Directive → Bool
  | .instr { operation := .CCMN_imm .., .. } => true
  | _ => false

meta def isCcmpOrCcmnDir (d : Directive) : Bool :=
  isCcmpRegDir d || isCcmpImmDir d || isCcmnImmDir d

meta def isCsnegDir : Directive → Bool
  | .instr { operation := .CSNEG .., .. } => true
  | _ => false

/-! ## 2. `CCMP` / `CCMN` Conditional Compare Chains -/

/-- 3-way short-circuit `||`: `a == 5 || b < c || d == -1` emits `CCMP_reg` + `CCMN_imm`. -/
def ccmpOr3WayFn : Fn :=
  let neg1 : BitVec 64 := BitVec.ofInt 64 (-1)
  ⟨"ccmp_or3", [i64, i64, i64, i64], [i64], fun _ _ (a, b, c, d, ()) =>
    .group (sig := [[]])
      (fun (lblTrue, ()) => .cons (ts := []) (fun () =>
        .ret (.imm (10 : BitVec 64), ())) .nil)
      (fun (lblTrue, ()) =>
        .let_ (op2 (.cmp .eq i64) (.var a) (.imm 5)) fun (c1, ()) =>
        .jnz (.var c1)
          (.jump lblTrue ())
          (.let_ (op2 (.cmp .ult i64) (.var b) (.var c)) fun (c2, ()) =>
           .jnz (.var c2)
             (.jump lblTrue ())
             (.let_ (op2 (.cmp .eq i64) (.var d) (.imm neg1)) fun (c3, ()) =>
              .jnz (.var c3)
                (.jump lblTrue ())
                (.ret (.imm (20 : BitVec 64), ())))))⟩

#guard armChk [ccmpOr3WayFn]
#guard countDirs isCcmpRegDir (armCode [ccmpOr3WayFn]) == 1
#guard countDirs isCcmnImmDir (armCode [ccmpOr3WayFn]) == 1
#guard countDirs isCcmpOrCcmnDir (armCodeOff [ccmpOr3WayFn]) == 0
#guard insnCount (armCode [ccmpOr3WayFn]) < insnCount (armCodeOff [ccmpOr3WayFn])

/-- Short-circuit `&&` (`a != 5 && b == 3`) emits `CCMP_imm` and fewer instructions. -/
def ccmpAnd2Way32Fn : Fn :=
  ⟨"ccmp_and2_32", [i32, i32, i32], [i32], fun _ _ (a, b, r, ()) =>
    .group (sig := [[]])
      (fun (lblFalse, ()) => .cons (ts := []) (fun () =>
        .ret (.var r, ())) .nil)
      (fun (lblFalse, ()) =>
        .let_ (op2 (.cmp .ne i32) (.var a) (.imm 5)) fun (c1, ()) =>
        .jnz (.var c1)
          (.let_ (op2 (.cmp .eq i32) (.var b) (.imm 3)) fun (c2, ()) =>
           .jnz (.var c2)
             (.ret (.imm (42 : BitVec 32), ()))
             (.jump lblFalse ()))
          (.jump lblFalse ()))⟩

#guard armChk [ccmpAnd2Way32Fn]
#guard countDirs isCcmpImmDir (armCode [ccmpAnd2Way32Fn]) == 1
#guard countDirs isCcmpOrCcmnDir (armCodeOff [ccmpAnd2Way32Fn]) == 0
#guard insnCount (armCode [ccmpAnd2Way32Fn]) < insnCount (armCodeOff [ccmpAnd2Way32Fn])

/-! ## 3. `CSNEG` Dynamic Conditional Negation -/

/-- 64-bit `select c x (-x)` from flag comparison lowers to single `CSNEG`. -/
def csneg64PosNegFn : Fn :=
  ⟨"csneg64_pos_neg", [i64, i64, i64], [i64], fun _ _ (a, b, x, ()) =>
    .let_ (op2 (.cmp .slt i64) (.var a) (.var b)) fun (c, ()) =>
    .let_ (op1 (.neg i64) (.var x)) fun (nx, ()) =>
    .let_ (op3 (.select i64) (.var c) (.var x) (.var nx)) fun (r, ()) =>
    .ret (.var r, ())⟩

/-- 32-bit `select c (-x) x` from flag comparison lowers to single 32-bit `CSNEG`. -/
def csneg32NegPosFn : Fn :=
  ⟨"csneg32_neg_pos", [i32, i32, i32], [i32], fun _ _ (a, b, x, ()) =>
    .let_ (op2 (.cmp .eq i32) (.var a) (.var b)) fun (c, ()) =>
    .let_ (op1 (.neg i32) (.var x)) fun (nx, ()) =>
    .let_ (op3 (.select i32) (.var c) (.var nx) (.var x)) fun (r, ()) =>
    .ret (.var r, ())⟩

/-- GPR-bool argument feeding `select c x (-x)` lowers to `ANDS #1` + `CSNEG`. -/
def csnegGprBoolFn : Fn :=
  ⟨"csneg_gpr_bool", [.bool, i64], [i64], fun _ _ (c, x, ()) =>
    .let_ (op1 (.neg i64) (.var x)) fun (nx, ()) =>
    .let_ (op3 (.select i64) (.var c) (.var x) (.var nx)) fun (r, ()) =>
    .ret (.var r, ())⟩

#guard armChk [csneg64PosNegFn, csneg32NegPosFn, csnegGprBoolFn]
#guard countDirs isCsnegDir (armCode [csneg64PosNegFn]) == 1
#guard countDirs isCsnegDir (armCode [csneg32NegPosFn]) == 1
#guard countDirs isCsnegDir (armCode [csnegGprBoolFn]) == 1
#guard insnCount (armCode [csneg64PosNegFn]) < insnCount (armCodeOff [csneg64PosNegFn])
#guard insnCount (armCode [csneg32NegPosFn]) < insnCount (armCodeOff [csneg32NegPosFn])
#guard insnCount (armCode [csnegGprBoolFn]) < insnCount (armCodeOff [csnegGprBoolFn])

/-! ## 4. Real `Kissat.Plain` Activation -/

meta def plainPolFns : List Fn :=
  (LeanQbe.T.Examples.Kissat.Plain.plainModule.optInlinePolicy {}).fns

meta def okInsns : Except String (List Directive) → Nat
  | .ok ds => insnCount ds
  | .error _ => 0

meta def okCcmpCount : Except String (List Directive) → Nat
  | .ok ds => countDirs isCcmpOrCcmnDir ds
  | .error _ => 0

meta def okCsnegCount : Except String (List Directive) → Nat
  | .ok ds => countDirs isCsnegDir ds
  | .error _ => 0

meta def hotStats (nm : Sym) : Nat × Nat × Nat × Nat :=
  match plainPolFns.find? (·.name == nm) with
  | some f =>
    let onRes := Driver.compileFnFlat armTarget.toIsa armLegalTarget f
    let offRes := Driver.compileFnFlat armIsaNoOpt8 armLegalTarget f
    (okInsns onRes, okInsns offRes, okCcmpCount onRes, okCsnegCount onRes)
  | none => (0, 0, 0, 0)

meta def hotWins (nm : Sym) : Bool :=
  let (on, off, ccmp, csneg) := hotStats nm
  0 < on && on < off && 0 < ccmp + csneg

#guard hotWins "plain_watch_push"
#guard hotWins "plain_heap_up"
#guard hotWins "plain_heap_down"
#guard hotWins "plain_queue_mtf"
#guard hotWins "plain_reduce"
#guard hotWins "plain_min_shrink"
#guard hotWins "plain_rephase"
#guard (hotStats "plain_reduce").2.2.1 >= 2

#eval
  let hots := ["plain_watch_push", "plain_heap_up",
    "plain_heap_down", "plain_queue_mtf", "plain_reduce"]
  hots.map fun nm => (nm, hotStats nm)

/-! ## 5. Axiom Audit (`std3` only) -/

#print axioms LeanQbe.T.Arm64.armTarget
#print axioms LeanQbe.T.Arm64.armLabelClean
#print axioms LeanQbe.T.compile_sound
#print axioms LeanQbe.T.Arm64.armCcmp_spec
#print axioms LeanQbe.T.Arm64.armSelectNeg_spec
#print axioms LeanQbe.T.Rega.lowerFn_correct
#print axioms LeanQbe.T.Rega.lowerFlatFn_eq_lowerFn

end LeanQbeTest.T.Arm64W62CcmpTest
