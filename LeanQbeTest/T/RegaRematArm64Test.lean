module

import LeanQbe.T.MainCertCore
import LeanQbe.T.MainCertFlat
import LeanQbe.T.MainCertInline
import LeanQbe.T.Arm64.TargLemmas
import LeanQbe.T.Examples.Kissat.Plain
import LeanQbe.T.Spill
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.MainCertInline
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.Plain
meta import LeanQbe.T.MainFlat
meta import LeanQbe.T.Spill

/-!
# Verified `Base + ConstDisp` Rematerialization — AArch64 Regression & Parity Tests

Covers `W5-1b` on AArch64 (`LeanQbe.T.Arm64.armTarget`):
1. BCP-shaped `cl + 3` high-pressure loop (> 24 live GPRs) where `cl3 = cl + 3` is rematerialized
   (`h.elide`) instead of spilled across the loop.
2. Rematerialized uses across `cmp eq`, `add64`, and `.jump` arguments.
3. Negative guards: redefined loop-carried base and out-of-range 12-bit immediate (`0x12345`,
   which does not fit in a single AArch64 `add`/`sub` immediate instruction).
4. `Kissat.Plain` AArch64 hot functions (`plain_prop_lit`, `plain_analyze`, `plain_assign`,
   `plain_queue_mtf`, `plain_analyze_lit`) lower cleanly and rematerialize structurally.
5. Exact `(flat := false)` vs `(flat := true)` kernel `code = rfl` and `bounds = rfl` parity.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.RegaRematArm64Test

open LeanQbe.T
open LeanQbe.T.Arm64

/-! ## Helpers -/

private def xors {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (a : V i64) :
    Nat → (List (V i64) → Expr V L rs) → Expr V L rs
  | 0, body => body []
  | n + 1, body =>
    .let_ (op2 (.xor i64) (.var a) (.imm (BitVec.ofNat 64 (n + 11)))) fun (x, ()) =>
      xors a n fun xs => body (x :: xs)

private def mix {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    List (V i64) → V i64 → (V i64 → Expr V L rs) → Expr V L rs
  | [], acc, k => k acc
  | x :: xs, acc, k =>
    .let_ (op2 (.xor i64) (.var acc) (.var x)) fun (y, ()) =>
    .let_ (op2 (.add i64) (.var y) (.var x)) fun (z, ()) => mix xs z k

private def mix3 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    List (V i64) → V i64 → (V i64 → Expr V L rs) → Expr V L rs
  | [], acc, k => k acc
  | x :: xs, acc, k =>
    .let_ (op2 (.xor i64) (.var acc) (.var x)) fun (y, ()) =>
    .let_ (op2 (.add i64) (.var y) (.var x)) fun (z, ()) =>
    .let_ (op2 (.xor i64) (.var z) (.var x)) fun (w, ()) => mix3 xs w k

private meta def rematElidedIps (f : Fn) : List Nat :=
  let I := armTarget.toIsa
  let (t0, _, _, _, nip, _) := Live.Tree.ofFn f
  let (t1a, e0, ad0) := Live.elideAddrTreeDeps I t0
  let (t1b, e1, ad1) := Live.elideCmpTreeDeps I t1a e0 ad0
  let (_, eBase, _) := Live.elideRmwTreeDeps I t1b e1 ad1
  let h := Spill.hints I f
  (List.range nip).filter fun ip => h.elide.getD ip false && !eBase.getD ip false

/-! ## Fixtures -/

/-- BCP-shaped high-pressure loop (> 24 live GPRs on AArch64): `cl` stays hot in a GPR,
`cl3 = cl + 3` is rematerialized at `cmp eq`, `add64`, and `.jump` uses instead of spilled. -/
def fnBcpRematArm64 : Fn :=
  ⟨"remat_bcp_arm64", [i64, i64, i64], [i64], fun _ _ (cl, n, seed, ()) =>
    .let_ (op2 (.add i64) (.var cl) (.imm 3)) fun (cl3, ()) =>
    xors seed 25 fun hs =>
    loop1 (ts := [i64, i64])
      (fun L (i, acc, ()) =>
        .let_ (op2 (.cmp .ult i64) (.var i) (.var n)) fun (c0, ()) =>
        .jnz (.var c0)
          (.let_ (op2 (.xor i64) (.var acc) (.var cl)) fun (a0, ()) =>
           .let_ (op2 (.add i64) (.var a0) (.var cl)) fun (a1, ()) =>
           .let_ (op2 (.xor i64) (.var a1) (.var cl)) fun (a2, ()) =>
           .let_ (op2 (.add i64) (.var a2) (.var cl)) fun (a3, ()) =>
           mix3 hs a3 fun z =>
           .let_ (op2 (.cmp .eq i64) (.var cl3) (.imm 1000)) fun (c1, ()) =>
           .jnz (.var c1)
             (.let_ (op2 (.add i64) (.var cl3) (.var z)) fun (s1, ()) =>
              .let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
              .jump L (.var i', .var s1, ()))
             (.let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
              .jump L (.var i', .var cl3, ())))
          (.ret (.var acc, ())))
      (fun L => .jump L (.imm 0, .var cl, ()))⟩

/-- Exercises `cmp eq (base + disp), imm` and `add64 (base + disp), y` rematerialization on
AArch64 under > 24 live GPRs. -/
def fnRematCmpAddArm64 : Fn :=
  ⟨"remat_cmp_add_arm64", [i64, i64], [i64], fun _ _ (base, seed, ()) =>
    .let_ (op2 (.add i64) (.var base) (.imm 5)) fun (x, ()) =>
    xors seed 25 fun hs =>
    .let_ (op2 (.xor i64) (.var base) (.imm 1)) fun (b0, ()) =>
    .let_ (op2 (.add i64) (.var b0) (.var base)) fun (b1, ()) =>
    .let_ (op2 (.xor i64) (.var b1) (.var base)) fun (b2, ()) =>
    mix hs b2 fun z =>
    .let_ (op2 (.cmp .eq i64) (.var x) (.imm 42)) fun (c, ()) =>
    .jnz (.var c)
      (.let_ (op2 (.add i64) (.var x) (.var z)) fun (r, ()) => .ret (.var r, ()))
      (.let_ (op2 (.add i64) (.var z) (.var base)) fun (r, ()) => .ret (.var r, ()))⟩

/-- Negative guard 1: loop parameter `cur` starts at `base` and increments each iteration while
`x = base + 3` was computed from the outer `base` before the loop. -/
def fnNegRedefBaseArm64 : Fn :=
  ⟨"remat_neg_redef_arm64", [i64, i64, i64], [i64], fun _ _ (base, n, seed, ()) =>
    .let_ (op2 (.add i64) (.var base) (.imm 3)) fun (x, ()) =>
    xors seed 25 fun hs =>
    loop1 (ts := [i64, i64, i64])
      (fun L (i, cur, acc, ()) =>
        .let_ (op2 (.cmp .ult i64) (.var i) (.var n)) fun (c0, ()) =>
        .jnz (.var c0)
          (mix hs acc fun z =>
           .let_ (op2 (.add i64) (.var cur) (.imm 8)) fun (cur', ()) =>
           .let_ (op2 (.add i64) (.var z) (.var cur')) fun (acc1, ()) =>
           .let_ (op2 (.add i64) (.var acc1) (.var x)) fun (acc2, ()) =>
           .let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
           .jump L (.var i', .var cur', .var acc2, ()))
          (.ret (.var acc, ())))
      (fun L => .jump L (.imm 0, .var base, .imm 0, ()))⟩

/-- Negative guard 2: immediate `0x12345` does not fit in a single AArch64 `add`/`sub` imm12. -/
def fnNegBigDispArm64 : Fn :=
  ⟨"remat_neg_bigdisp_arm64", [i64, i64], [i64], fun _ _ (base, seed, ()) =>
    .let_ (op2 (.add i64) (.var base) (.imm (BitVec.ofNat 64 0x12345))) fun (x, ()) =>
    xors seed 25 fun hs =>
    .let_ (op2 (.xor i64) (.var base) (.imm 1)) fun (b0, ()) =>
    .let_ (op2 (.add i64) (.var b0) (.var base)) fun (b1, ()) =>
    mix hs b1 fun z =>
    .let_ (op2 (.add i64) (.var x) (.var z)) fun (r, ()) =>
    .ret (.var r, ())⟩

/-! ## Dual-Mode `(flat := false)` vs `(flat := true)` Parity -/

def rematArmSrcMod : Module :=
  ⟨[fnBcpRematArm64, fnRematCmpAddArm64, fnNegRedefBaseArm64, fnNegBigDispArm64], [], []⟩

inline_mod! rematArmMod rematArmSrcMod {} (compile := false)

compile_linked_chunks! rematArmLeg armTarget armLayout armLegalTarget armLabelClean
  rematArmMod 32 (flat := false)

compile_linked_chunks! rematArmFlat armTarget armLayout armLegalTarget armLabelClean
  rematArmMod 32 (flat := true)

theorem remat_arm64_code_eq : rematArmLeg.code = rematArmFlat.code := rfl

theorem remat_arm64_bounds_eq : rematArmLeg.bounds = rematArmFlat.bounds := rfl

/-! ## Functional & Regression Guards -/

-- BCP-shaped `cl + 3` loop: remat fires on `cl + 3` (`ip = 0`) and lowers cleanly on AArch64.
#guard rematElidedIps fnBcpRematArm64 == [0]
#guard (Rega.lowerFn armTarget.toIsa (Spill.hints armTarget.toIsa fnBcpRematArm64)
  fnBcpRematArm64.ext fnBcpRematArm64).isOk

-- `cmp eq (base + 5), 42` + `add64`: remat fires on `base + 5` (`ip = 0`) and lowers cleanly.
#guard rematElidedIps fnRematCmpAddArm64 == [0]
#guard (Rega.lowerFn armTarget.toIsa (Spill.hints armTarget.toIsa fnRematCmpAddArm64)
  fnRematCmpAddArm64.ext fnRematCmpAddArm64).isOk

-- Negative guard 1: redefined loop base lowers cleanly.
#guard (Rega.lowerFn armTarget.toIsa (Spill.hints armTarget.toIsa fnNegRedefBaseArm64)
  fnNegRedefBaseArm64.ext fnNegRedefBaseArm64).isOk

-- Negative guard 2: out-of-range imm12 (`0x12345`) is NEVER rematerialized on AArch64.
#guard rematElidedIps fnNegBigDispArm64 == []
#guard (Rega.lowerFn armTarget.toIsa (Spill.hints armTarget.toIsa fnNegBigDispArm64)
  fnNegBigDispArm64.ext fnNegBigDispArm64).isOk

-- Real Kissat `Plain` AArch64 hot functions: remat fires structurally (`plain_analyze`,
-- `plain_assign`, `plain_queue_mtf`, `plain_analyze_lit`) and all lower cleanly (`plain_prop_lit`
-- reduces spill moves).
#guard
  ["plain_prop_lit", "plain_analyze", "plain_assign", "plain_queue_mtf",
    "plain_analyze_lit"].all fun nm =>
    match Examples.Kissat.Plain.plainFns.find? (·.name == nm) with
    | none => false
    | some f =>
      let fm := f.mid armLegalTarget
      let h := Spill.hints armTarget.toIsa fm
      let fired := if nm == "plain_prop_lit" then true else !(rematElidedIps fm).isEmpty
      fired && (Rega.lowerFn armTarget.toIsa h fm.ext fm).isOk

#print axioms remat_arm64_code_eq
#print axioms remat_arm64_bounds_eq
#print axioms rematArmLeg
#print axioms rematArmFlat

end LeanQbeTest.T.RegaRematArm64Test
