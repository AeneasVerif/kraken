module

public import LeanQbe.T.ZeroPeel
public import LeanQbe.T.Examples.LratBytesProg

/-!
# Kernel-Reducibility Tests for `LeanQbe.T.ZeroPeel` (No `import all`)

Verifies under normal `public import LeanQbe.T.ZeroPeel` (zero `import all`) that `Func.zeroPeel`,
`Func.zeroPeelWith`, `ZeroPeel.zpSize`, `ZeroPeel.zpLoops`, `ZeroPeel.widenFillSingle`, and
`ZeroPeel.peelSingle` reduce cleanly in the Lean kernel (`decide +kernel` / `rfl`):
1. 1st-iteration loop peeling (`peelSingle`) on an LEB128-style byte-scanning loop (`peelLoop`);
2. Wide constant-fill loop widening (`widenFillSingle`) on a byte zero-fill loop (`fillLoop`);
3. `LratBytesProg` (`lratBytesFns`, 6 fns) total `zpSize` and `checkTFlat` checks.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.ZeroPeelKernelTest

open LeanQbe.T

/-- Single-block byte-scanning loop triggering `ZeroPeel.peelSingle` under default config. -/
def peelLoop : Func [i64] [.bits 8] := fun _ _ (ptr, ()) =>
  loop1 (ts := [i64, i64])
    (fun loop (p, n, ()) =>
      .load (.bits 8) (.var p) fun b =>
      .let_ (op2 (.ult (.bits 8)) (.var b) (.imm 128#8)) fun (c, ()) =>
      .jnz (.var c) (.ret (.var b, ()))
        (.let_ (op2 (.add i64) (.var p) (.imm 1)) fun (p', ()) =>
         .let_ (op2 (.add i64) (.var n) (.imm 1)) fun (n', ()) =>
         .let_ (op2 (.ult i64) (.var n') (.imm 10)) fun (ok, ()) =>
         .jnz (.var ok) (.jump loop (.var p', .var n', ())) (.ret (.var b, ()))))
    (fun loop => .jump loop (.var ptr, .imm 0, ()))

/-- Byte zero-fill loop triggering `ZeroPeel.widenFillSingle` under default config. -/
def fillLoop : Func [i64, i64] [i64] := fun _ _ (ptr, n, ()) =>
  loop1 (ts := [i64])
    (fun loop (i, ()) =>
      .let_ (op2 (.ult i64) (.var i) (.var n)) fun (cond, ()) =>
      .jnz (.var cond)
        (.let_ (op2 (.add i64) (.var ptr) (.var i)) fun (addr, ()) =>
         .store (t := .bits 8) (.imm 0#8) (.var addr)
           (.let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
            .jump loop (.var i', ())))
        (.ret (.var ptr, ())))
    (fun loop => .jump loop (.imm 0, ()))

/-- Total post-`ZeroPeel` `TFlat` node count across `LratBytesProg` (`6` functions). -/
def lratZpSize : Nat :=
  Examples.LratBytes.lratBytesFns.foldl
    (fun acc f => acc + ZeroPeel.zpSize (reifyFunc (Func.zeroPeel f.body))) 0

theorem peel_checkTFlat :
    Func.checkTFlat (Func.zeroPeel peelLoop) = true := by decide +kernel

theorem peel_loops :
    ZeroPeel.zpLoops (reifyFunc (Func.zeroPeel peelLoop)) = 1 := by decide +kernel

theorem peel_size_le :
    Nat.ble (ZeroPeel.zpSize (reifyFunc (Func.zeroPeel peelLoop))) 999999 = true := by
  decide +kernel

theorem peel_budget0 :
    Func.zeroPeelWith { peelBudget := 0 } peelLoop = peelLoop := by rfl

theorem peel_maxFnSize1 :
    Func.zeroPeelWith { maxFnSize := 1 } peelLoop = peelLoop := by rfl

theorem fill_checkTFlat :
    Func.checkTFlat (Func.zeroPeel fillLoop) = true := by decide +kernel

theorem fill_loops :
    ZeroPeel.zpLoops (reifyFunc (Func.zeroPeel fillLoop)) = 2 := by decide +kernel

theorem fill_size_le :
    Nat.ble (ZeroPeel.zpSize (reifyFunc (Func.zeroPeel fillLoop))) 999999 = true := by
  decide +kernel

theorem fill_unroll0 :
    Func.zeroPeelWith { unrollN := 0, peelBudget := 0 } fillLoop = fillLoop := by rfl

theorem lrat_zp_ble :
    Nat.ble lratZpSize 999999 = true := by decide +kernel

theorem lrat_checkTFlat :
    (Examples.LratBytes.lratBytesFns.all fun f => Func.checkTFlat (Func.zeroPeel f.body)) =
      true := by decide +kernel

#print axioms peel_checkTFlat
#print axioms peel_budget0
#print axioms fill_loops
#print axioms fill_unroll0
#print axioms lrat_zp_ble
#print axioms lrat_checkTFlat

end LeanQbe.T.ZeroPeelKernelTest
