module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.MainCertInline
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Plain
public import LeanQbe.T.Spill
public meta import Lean
public meta import LeanQbe.T.MainCertElab
public meta import LeanQbe.T.MainCertFlatElab
public meta import LeanQbe.T.MainCertInline
public meta import LeanQbe.T.Amd64.Targ
public meta import LeanQbe.T.Examples.Kissat.Plain
public meta import LeanQbe.T.MainFlat
public meta import LeanQbe.T.Spill

/-!
# Verified `Base + ConstDisp` Rematerialization — SysV x64 Regression & Parity Tests

Covers `W5-1b` on SysV x64 (`LeanQbe.T.Amd64.x64Target`):
1. BCP-shaped `cl + 3` high-pressure loop where `cl3 = cl + 3` is rematerialized (`h.elide`)
   instead of spilled across the loop, eliminating stack traffic.
2. Rematerialized uses across `cmp eq/ne`, `add64`, and `.jump` arguments.
3. Negative guards: redefined loop-carried base and out-of-range 64-bit displacement (`> 32`-bit
   `lea` disp).
4. `Kissat.Plain` x64 hot functions (`plain_prop_lit`, `plain_analyze`, `plain_analyze_lit`,
   `plain_assign`, `plain_queue_mtf`) lower cleanly with structural remat firing and
   reduced spill moves.
5. Exact `(flat := false)` vs `(flat := true)` kernel `code = rfl` and `bounds = rfl` parity.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.RegaRematTest

open LeanQbe.T
open LeanQbe.T.Amd64

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
  let I := x64Target.toIsa
  let (t0, _, _, _, nip, _) := Live.Tree.ofFn f
  let (t1a, e0, ad0) := Live.elideAddrTreeDeps I t0
  let (t1b, e1, ad1) := Live.elideCmpTreeDeps I t1a e0 ad0
  let (_, eBase, _) := Live.elideRmwTreeDeps I t1b e1 ad1
  let h := Spill.hints I f
  (List.range nip).filter fun ip => h.elide.getD ip false && !eBase.getD ip false

private meta def spillMoveCount (h : x64Target.toIsa.Hints) (nip : Nat) : Nat :=
  (List.range nip).foldl (fun n ip =>
    match h.pre.find? ip with
    | none => n
    | some ps =>
      n + (ps.moves.filter fun | .st .. | .ld .. | .vst .. | .vld .. => true | _ => false).length)
    0

/-! ## Fixtures -/

/-- BCP-shaped high-pressure loop: `cl` stays hot in a GPR, `cl3 = cl + 3` is defined once
before the loop and used in `cmp ult cl3, endV` (with spilled `endV`) and `add64 cl3, z`. -/
def fnBcpRematX64 : Fn :=
  ⟨"remat_bcp_x64", [i64, i64, i64], [i64], fun _ _ (cl, n, seed, ()) =>
    .let_ (op2 (.add i64) (.var cl) (.imm 3)) fun (cl3, ()) =>
    .let_ (op2 (.xor i64) (.var seed) (.imm 77)) fun (endV, ()) =>
    xors seed 13 fun hs =>
    loop1 (ts := [i64, i64])
      (fun L (i, acc, ()) =>
        .let_ (op2 (.cmp .ult i64) (.var i) (.var n)) fun (c0, ()) =>
        .jnz (.var c0)
          (.let_ (op2 (.xor i64) (.var acc) (.var cl)) fun (a0, ()) =>
           .let_ (op2 (.add i64) (.var a0) (.var cl)) fun (a1, ()) =>
           .let_ (op2 (.xor i64) (.var a1) (.var cl)) fun (a2, ()) =>
           .let_ (op2 (.add i64) (.var a2) (.var cl)) fun (a3, ()) =>
           mix3 hs a3 fun z =>
           .let_ (op2 (.cmp .ult i64) (.var cl3) (.var endV)) fun (c1, ()) =>
           .jnz (.var c1)
             (.let_ (op2 (.add i64) (.var cl3) (.var z)) fun (s1, ()) =>
              .let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
              .jump L (.var i', .var s1, ()))
             (.let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
              .jump L (.var i', .var z, ())))
          (.ret (.var acc, ())))
      (fun L => .jump L (.imm 0, .var cl, ()))⟩

/-- Exercises `cmp eq (base + disp), imm` and `add64 (base + disp), y` rematerialization. -/
def fnRematCmpAddX64 : Fn :=
  ⟨"remat_cmp_add_x64", [i64, i64], [i64], fun _ _ (base, seed, ()) =>
    .let_ (op2 (.add i64) (.var base) (.imm 5)) fun (x, ()) =>
    xors seed 13 fun hs =>
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
def fnNegRedefBaseX64 : Fn :=
  ⟨"remat_neg_redef_x64", [i64, i64, i64], [i64], fun _ _ (base, n, seed, ()) =>
    .let_ (op2 (.add i64) (.var base) (.imm 3)) fun (x, ()) =>
    xors seed 13 fun hs =>
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

/-- Negative guard 2: 64-bit displacement `0x1_0000_0000` does not fit in a single x64 `lea`. -/
def fnNegBigDispX64 : Fn :=
  ⟨"remat_neg_bigdisp_x64", [i64, i64], [i64], fun _ _ (base, seed, ()) =>
    .let_ (op2 (.add i64) (.var base) (.imm (BitVec.ofNat 64 0x100000000))) fun (x, ()) =>
    xors seed 14 fun hs =>
    .let_ (op2 (.xor i64) (.var base) (.imm 1)) fun (b0, ()) =>
    .let_ (op2 (.add i64) (.var b0) (.var base)) fun (b1, ()) =>
    mix hs b1 fun z =>
    .let_ (op2 (.add i64) (.var x) (.var z)) fun (r, ()) =>
    .ret (.var r, ())⟩

/-! ## Dual-Mode `(flat := false)` vs `(flat := true)` Parity -/

def rematX64SrcMod : Module :=
  ⟨[fnBcpRematX64, fnRematCmpAddX64, fnNegRedefBaseX64, fnNegBigDispX64], [], []⟩

inline_mod! rematX64Mod rematX64SrcMod {} (compile := false)

compile_linked_chunks! rematX64Leg x64Target x64Layout x64LegalTarget x64LabelClean
  rematX64Mod 32 (flat := false)

compile_linked_chunks! rematX64Flat x64Target x64Layout x64LegalTarget x64LabelClean
  rematX64Mod 32 (flat := true)

theorem remat_x64_code_eq : rematX64Leg.code = rematX64Flat.code := rfl

theorem remat_x64_bounds_eq : rematX64Leg.bounds = rematX64Flat.bounds := rfl

/-! ## Functional & Regression Guards -/

-- BCP-shaped `cl + 3` loop: remat fires on `cl + 3` (`ip = 0`) and lowers cleanly.
#guard rematElidedIps fnBcpRematX64 == [0]
#guard (Rega.lowerFn x64Target.toIsa (Spill.hints x64Target.toIsa fnBcpRematX64)
  fnBcpRematX64.ext fnBcpRematX64).isOk

-- `cmp eq (base + 5), 42` + `add64`: remat fires on `base + 5` (`ip = 0`) and lowers cleanly.
#guard rematElidedIps fnRematCmpAddX64 == [0]
#guard (Rega.lowerFn x64Target.toIsa (Spill.hints x64Target.toIsa fnRematCmpAddX64)
  fnRematCmpAddX64.ext fnRematCmpAddX64).isOk

-- Negative guard 1: redefined loop base lowers cleanly.
#guard (Rega.lowerFn x64Target.toIsa (Spill.hints x64Target.toIsa fnNegRedefBaseX64)
  fnNegRedefBaseX64.ext fnNegRedefBaseX64).isOk

-- Negative guard 2: out-of-range 64-bit disp (`0x1_0000_0000`) is NEVER rematerialized.
#guard rematElidedIps fnNegBigDispX64 == []
#guard (Rega.lowerFn x64Target.toIsa (Spill.hints x64Target.toIsa fnNegBigDispX64)
  fnNegBigDispX64.ext fnNegBigDispX64).isOk

-- Real Kissat `Plain` x64 hot functions: remat structurally fires on `plain_analyze`,
-- `plain_analyze_lit`, `plain_assign`, `plain_queue_mtf`, `plain_prop_lit` beats legacy spill
-- moves, and all lower cleanly.
#guard
  ["plain_prop_lit", "plain_analyze", "plain_analyze_lit", "plain_assign",
    "plain_queue_mtf"].all fun nm =>
    match Examples.Kissat.Plain.plainFns.find? (·.name == nm) with
    | none => false
    | some f =>
      let fm := f.mid x64LegalTarget
      let nip := (Live.Tree.ofFn fm).2.2.2.2.1
      let h := Spill.hints x64Target.toIsa fm
      let okSpec :=
        if nm == "plain_prop_lit" then
          let hLeg := Spill.hints x64Target.toIsa fm (cfg := .legacy)
          spillMoveCount h nip < spillMoveCount hLeg nip
        else
          !(rematElidedIps fm).isEmpty
      okSpec && (Rega.lowerFn x64Target.toIsa h fm.ext fm).isOk

#print axioms remat_x64_code_eq
#print axioms remat_x64_bounds_eq
#print axioms rematX64Leg
#print axioms rematX64Flat

end LeanQbeTest.T.RegaRematTest
