module

public import BvDecideQbe
public meta import BvDecideQbe

/-!
# `bv_cut_qbe`, Ring-Dispatch (`H6a`), and `NormalizeRules` (`H7`) Test Suite

Verifies:
1. `shiftmul` (`BitVec 64`) and `opt_share` (`BitVec 128`) closing fast with zero solver axioms
   (both via `bv_cut_qbe` and via `open scoped BvDecideQbe.NormalizeRules` + `bv_decide_qbe`).
2. `bv_cut_qbe` automatically proving 16-round ARX equivalence (`≤ 1 s`!), in both
   hypothesis-chain and `let`-binding styles (pre-inlining preservation `P1-3`).
3. `bv_cut_qbe` automatically proving MurmurHash `fmix32` and `fmix64` (CSD shift-add vs `*`)
   via `shl → mul` + `grind` ring dispatch with **0 solver axioms** (`≤ std3`, `≤ 2 s`!).
4. Explicit cutpoint lists `bv_cut_qbe [e1 = e2, ...]` (compound and multi-cut).
5. Cone-relevant side-condition retention (`h : a < 100#32` and transitive chains) + `+uf` bailout.
6. Clean rejection on a false explicit cut and on a buggy 16-round ARX (`CEX` emitted,
   **0** solver axioms added to the environment!).
-/

set_option autoImplicit false
set_option Elab.async false

public section

namespace BvDecideQbeTest.CutTest

open Lean
open Lean.Meta
open Lean.Elab.Tactic.BVDecide
open BvDecideQbe

/-! ## 1. `H7` Normalizer Rules (`shiftmul` 64-bit & `opt_share` 128-bit) -/

theorem thm_shiftmul_64 (x : BitVec 64) (s : BitVec 6) :
    x * (1#64 <<< s.zeroExtend 64) = x <<< s.zeroExtend 64 := by
  bv_cut_qbe

theorem thm_shiftmul_left_64 (x : BitVec 64) (s : BitVec 6) :
    (1#64 <<< s.zeroExtend 64) * x = x <<< s.zeroExtend 64 := by
  bv_cut_qbe

theorem thm_shiftmul_pow2_64 (x : BitVec 64) :
    x * BitVec.ofNat 64 (2 ^ 13) = x <<< 13 := by
  bv_cut_qbe

theorem thm_opt_share_128 (s : Bool) (a b c : BitVec 128) :
    (if s then a + b else a + c) = a + (if s then b else c) := by
  bv_cut_qbe

theorem thm_opt_share_right_mul_128 (s : Bool) (a b c : BitVec 128) :
    (if s then b * a else c * a) = (if s then b else c) * a := by
  bv_cut_qbe

theorem thm_opt_share_xor_cond_128 (s : Bool) (a b c : BitVec 128) :
    (bif s then a ^^^ b else a ^^^ c) = a ^^^ (bif s then b else c) := by
  bv_cut_qbe

theorem thm_opt_share_shl_64 (s : Bool) (b c : BitVec 64) :
    (if s then b <<< 5 else c <<< 5) = (if s then b else c) <<< 5 := by
  bv_cut_qbe

section ScopedNorm
open scoped BvDecideQbe.NormalizeRules

theorem thm_scoped_shiftmul_64 (x : BitVec 64) (s : BitVec 6) :
    x * (1#64 <<< s.zeroExtend 64) = x <<< s.zeroExtend 64 := by
  bv_decide_qbe

theorem thm_scoped_opt_share_128 (s : Bool) (a b c : BitVec 128) :
    (if s then a + b else a + c) = a + (if s then b else c) := by
  bv_decide_qbe

end ScopedNorm

/-! ## 2. `H6a` Pure Ring Dispatch (0 Solver Axioms) -/

theorem thm_mul_distrib_64 (x y z : BitVec 64) :
    (x + y) * z = x * z + y * z := by
  bv_cut_qbe

theorem thm_reassoc_add_128 (a b c d : BitVec 128) :
    ((a + b) + c) + d = a + (b + (c + d)) := by
  bv_cut_qbe

/-! ## 3. 16-Round ARX Equivalence (`bv_cut_qbe`, Hyp-Chain & `let`-Binding Styles) -/

theorem thm_arx_r16_hyps
    (x0 y0 x1 y1 u1 v1 x2 y2 u2 v2 x3 y3 u3 v3 x4 y4 u4 v4
     x5 y5 u5 v5 x6 y6 u6 v6 x7 y7 u7 v7 x8 y8 u8 v8
     x9 y9 u9 v9 x10 y10 u10 v10 x11 y11 u11 v11 x12 y12 u12 v12
     x13 y13 u13 v13 x14 y14 u14 v14 x15 y15 u15 v15 x16 y16 u16 v16
     u0 v0 : BitVec 32)
    (hu0 : u0 = x0) (hv0 : v0 = y0)
    (hx1 : x1 = x0 + y0) (hy1 : y1 = y0.rotateLeft 7 ^^^ x1)
    (hx2 : x2 = x1 + y1) (hy2 : y2 = y1.rotateLeft 9 ^^^ x2)
    (hx3 : x3 = x2 + y2) (hy3 : y3 = y2.rotateLeft 13 ^^^ x3)
    (hx4 : x4 = x3 + y3) (hy4 : y4 = y3.rotateLeft 18 ^^^ x4)
    (hx5 : x5 = x4 + y4) (hy5 : y5 = y4.rotateLeft 5 ^^^ x5)
    (hx6 : x6 = x5 + y5) (hy6 : y6 = y5.rotateLeft 11 ^^^ x6)
    (hx7 : x7 = x6 + y6) (hy7 : y7 = y6.rotateLeft 3 ^^^ x7)
    (hx8 : x8 = x7 + y7) (hy8 : y8 = y7.rotateLeft 25 ^^^ x8)
    (hx9 : x9 = x8 + y8) (hy9 : y9 = y8.rotateLeft 16 ^^^ x9)
    (hx10 : x10 = x9 + y9) (hy10 : y10 = y9.rotateLeft 12 ^^^ x10)
    (hx11 : x11 = x10 + y10) (hy11 : y11 = y10.rotateLeft 8 ^^^ x11)
    (hx12 : x12 = x11 + y11) (hy12 : y12 = y11.rotateLeft 21 ^^^ x12)
    (hx13 : x13 = x12 + y12) (hy13 : y13 = y12.rotateLeft 19 ^^^ x13)
    (hx14 : x14 = x13 + y13) (hy14 : y14 = y13.rotateLeft 23 ^^^ x14)
    (hx15 : x15 = x14 + y14) (hy15 : y15 = y14.rotateLeft 2 ^^^ x15)
    (hx16 : x16 = x15 + y15) (hy16 : y16 = y15.rotateLeft 29 ^^^ x16)
    (hu1 : u1 = (u0 ^^^ v0) + ((u0 &&& v0) <<< 1))
    (hv1 : v1 = ((v0 <<< 7) ||| (v0 >>> 25)) ^^^ u1)
    (hu2 : u2 = (u1 ^^^ v1) + ((u1 &&& v1) <<< 1))
    (hv2 : v2 = ((v1 <<< 9) ||| (v1 >>> 23)) ^^^ u2)
    (hu3 : u3 = (u2 ^^^ v2) + ((u2 &&& v2) <<< 1))
    (hv3 : v3 = ((v2 <<< 13) ||| (v2 >>> 19)) ^^^ u3)
    (hu4 : u4 = (u3 ^^^ v3) + ((u3 &&& v3) <<< 1))
    (hv4 : v4 = ((v3 <<< 18) ||| (v3 >>> 14)) ^^^ u4)
    (hu5 : u5 = (u4 ^^^ v4) + ((u4 &&& v4) <<< 1))
    (hv5 : v5 = ((v4 <<< 5) ||| (v4 >>> 27)) ^^^ u5)
    (hu6 : u6 = (u5 ^^^ v5) + ((u5 &&& v5) <<< 1))
    (hv6 : v6 = ((v5 <<< 11) ||| (v5 >>> 21)) ^^^ u6)
    (hu7 : u7 = (u6 ^^^ v6) + ((u6 &&& v6) <<< 1))
    (hv7 : v7 = ((v6 <<< 3) ||| (v6 >>> 29)) ^^^ u7)
    (hu8 : u8 = (u7 ^^^ v7) + ((u7 &&& v7) <<< 1))
    (hv8 : v8 = ((v7 <<< 25) ||| (v7 >>> 7)) ^^^ u8)
    (hu9 : u9 = (u8 ^^^ v8) + ((u8 &&& v8) <<< 1))
    (hv9 : v9 = ((v8 <<< 16) ||| (v8 >>> 16)) ^^^ u9)
    (hu10 : u10 = (u9 ^^^ v9) + ((u9 &&& v9) <<< 1))
    (hv10 : v10 = ((v9 <<< 12) ||| (v9 >>> 20)) ^^^ u10)
    (hu11 : u11 = (u10 ^^^ v10) + ((u10 &&& v10) <<< 1))
    (hv11 : v11 = ((v10 <<< 8) ||| (v10 >>> 24)) ^^^ u11)
    (hu12 : u12 = (u11 ^^^ v11) + ((u11 &&& v11) <<< 1))
    (hv12 : v12 = ((v11 <<< 21) ||| (v11 >>> 11)) ^^^ u12)
    (hu13 : u13 = (u12 ^^^ v12) + ((u12 &&& v12) <<< 1))
    (hv13 : v13 = ((v12 <<< 19) ||| (v12 >>> 13)) ^^^ u13)
    (hu14 : u14 = (u13 ^^^ v13) + ((u13 &&& v13) <<< 1))
    (hv14 : v14 = ((v13 <<< 23) ||| (v13 >>> 9)) ^^^ u14)
    (hu15 : u15 = (u14 ^^^ v14) + ((u14 &&& v14) <<< 1))
    (hv15 : v15 = ((v14 <<< 2) ||| (v14 >>> 30)) ^^^ u15)
    (hu16 : u16 = (u15 ^^^ v15) + ((u15 &&& v15) <<< 1))
    (hv16 : v16 = ((v15 <<< 29) ||| (v15 >>> 3)) ^^^ u16) :
    x16 ++ y16 = u16 ++ v16 := by
  bv_cut_qbe

theorem thm_arx_r16_let (x0 y0 : BitVec 32) :
    let x1 := x0 + y0; let y1 := y0.rotateLeft 7 ^^^ x1
    let x2 := x1 + y1; let y2 := y1.rotateLeft 9 ^^^ x2
    let x3 := x2 + y2; let y3 := y2.rotateLeft 13 ^^^ x3
    let x4 := x3 + y3; let y4 := y3.rotateLeft 18 ^^^ x4
    let x5 := x4 + y4; let y5 := y4.rotateLeft 5 ^^^ x5
    let x6 := x5 + y5; let y6 := y5.rotateLeft 11 ^^^ x6
    let x7 := x6 + y6; let y7 := y6.rotateLeft 3 ^^^ x7
    let x8 := x7 + y7; let y8 := y7.rotateLeft 25 ^^^ x8
    let x9 := x8 + y8; let y9 := y8.rotateLeft 16 ^^^ x9
    let x10 := x9 + y9; let y10 := y9.rotateLeft 12 ^^^ x10
    let x11 := x10 + y10; let y11 := y10.rotateLeft 8 ^^^ x11
    let x12 := x11 + y11; let y12 := y11.rotateLeft 21 ^^^ x12
    let x13 := x12 + y12; let y13 := y12.rotateLeft 19 ^^^ x13
    let x14 := x13 + y13; let y14 := y13.rotateLeft 23 ^^^ x14
    let x15 := x14 + y14; let y15 := y14.rotateLeft 2 ^^^ x15
    let x16 := x15 + y15; let y16 := y15.rotateLeft 29 ^^^ x16
    let u1 := (x0 ^^^ y0) + ((x0 &&& y0) <<< 1)
    let v1 := ((y0 <<< 7) ||| (y0 >>> 25)) ^^^ u1
    let u2 := (u1 ^^^ v1) + ((u1 &&& v1) <<< 1)
    let v2 := ((v1 <<< 9) ||| (v1 >>> 23)) ^^^ u2
    let u3 := (u2 ^^^ v2) + ((u2 &&& v2) <<< 1)
    let v3 := ((v2 <<< 13) ||| (v2 >>> 19)) ^^^ u3
    let u4 := (u3 ^^^ v3) + ((u3 &&& v3) <<< 1)
    let v4 := ((v3 <<< 18) ||| (v3 >>> 14)) ^^^ u4
    let u5 := (u4 ^^^ v4) + ((u4 &&& v4) <<< 1)
    let v5 := ((v4 <<< 5) ||| (v4 >>> 27)) ^^^ u5
    let u6 := (u5 ^^^ v5) + ((u5 &&& v5) <<< 1)
    let v6 := ((v5 <<< 11) ||| (v5 >>> 21)) ^^^ u6
    let u7 := (u6 ^^^ v6) + ((u6 &&& v6) <<< 1)
    let v7 := ((v6 <<< 3) ||| (v6 >>> 29)) ^^^ u7
    let u8 := (u7 ^^^ v7) + ((u7 &&& v7) <<< 1)
    let v8 := ((v7 <<< 25) ||| (v7 >>> 7)) ^^^ u8
    let u9 := (u8 ^^^ v8) + ((u8 &&& v8) <<< 1)
    let v9 := ((v8 <<< 16) ||| (v8 >>> 16)) ^^^ u9
    let u10 := (u9 ^^^ v9) + ((u9 &&& v9) <<< 1)
    let v10 := ((v9 <<< 12) ||| (v9 >>> 20)) ^^^ u10
    let u11 := (u10 ^^^ v10) + ((u10 &&& v10) <<< 1)
    let v11 := ((v10 <<< 8) ||| (v10 >>> 24)) ^^^ u11
    let u12 := (u11 ^^^ v11) + ((u11 &&& v11) <<< 1)
    let v12 := ((v11 <<< 21) ||| (v11 >>> 11)) ^^^ u12
    let u13 := (u12 ^^^ v12) + ((u12 &&& v12) <<< 1)
    let v13 := ((v12 <<< 19) ||| (v12 >>> 13)) ^^^ u13
    let u14 := (u13 ^^^ v13) + ((u13 &&& v13) <<< 1)
    let v14 := ((v13 <<< 23) ||| (v13 >>> 9)) ^^^ u14
    let u15 := (u14 ^^^ v14) + ((u14 &&& v14) <<< 1)
    let v15 := ((v14 <<< 2) ||| (v14 >>> 30)) ^^^ u15
    let u16 := (u15 ^^^ v15) + ((u15 &&& v15) <<< 1)
    let v16 := ((v15 <<< 29) ||| (v15 >>> 3)) ^^^ u16
    x16 ++ y16 = u16 ++ v16 := by
  bv_cut_qbe

/-! ## 4. MurmurHash `fmix32` & `fmix64` (`shl → mul` + Ring Dispatch, 0 Solver Axioms!) -/

theorem thm_fmix32_auto
    (h0 h1 h2 h3 h4 h5 g1 g2 g3 g4 g5 : BitVec 32)
    (e1 : h1 = h0 ^^^ (h0 >>> 16))
    (e2 : h2 = h1 * 0x85ebca6b#32)
    (e3 : h3 = h2 ^^^ (h2 >>> 13))
    (e4 : h4 = h3 * 0xc2b2ae35#32)
    (e5 : h5 = h4 ^^^ (h4 >>> 16))
    (f1 : g1 = h0 ^^^ (h0 >>> 16))
    (f2 : g2 =
      ((((((((((((0#32 - g1) - (g1 <<< 2)) - (g1 <<< 4)) + (g1 <<< 7)) + (g1 <<< 9)) +
        (g1 <<< 11)) - (g1 <<< 14)) - (g1 <<< 18)) - (g1 <<< 20)) - (g1 <<< 25)) +
        (g1 <<< 27)) + (g1 <<< 31)))
    (f3 : g3 = g2 ^^^ (g2 >>> 13))
    (f4 : g4 =
      ((((((((((((((g3 + (g3 <<< 2)) - (g3 <<< 4)) + (g3 <<< 6)) - (g3 <<< 9)) -
        (g3 <<< 12)) - (g3 <<< 14)) - (g3 <<< 16)) + (g3 <<< 18)) - (g3 <<< 20)) -
        (g3 <<< 22)) - (g3 <<< 24)) + (g3 <<< 26)) - (g3 <<< 30)) + (g3 <<< 32)))
    (f5 : g5 = g4 ^^^ (g4 >>> 16)) :
    h5 = g5 := by
  bv_cut_qbe

theorem thm_fmix64_auto
    (h0 h1 h2 h3 h4 h5 g1 g2 g3 g4 g5 : BitVec 64)
    (e1 : h1 = h0 ^^^ (h0 >>> 33))
    (e2 : h2 = h1 * 0xff51afd7ed558ccd#64)
    (e3 : h3 = h2 ^^^ (h2 >>> 33))
    (e4 : h4 = h3 * 0xc4ceb9fe1a85ec53#64)
    (e5 : h5 = h4 ^^^ (h4 >>> 33))
    (f1 : g1 = h0 ^^^ (h0 >>> 33))
    (f2 : g2 =
      ((((((((((((((((((((((g1 - (g1 <<< 2)) + (g1 <<< 4)) - (g1 <<< 6)) + (g1 <<< 8)) -
        (g1 <<< 10)) + (g1 <<< 12)) - (g1 <<< 15)) - (g1 <<< 17)) - (g1 <<< 19)) -
        (g1 <<< 21)) - (g1 <<< 23)) - (g1 <<< 25)) - (g1 <<< 28)) - (g1 <<< 35)) -
        (g1 <<< 37)) - (g1 <<< 44)) - (g1 <<< 46)) + (g1 <<< 49)) + (g1 <<< 52)) +
        (g1 <<< 54)) - (g1 <<< 56)) + (g1 <<< 64)))
    (f3 : g3 = g2 ^^^ (g2 >>> 33))
    (f4 : g4 =
      (((((((((((((((((((((((0#64 - g3) + (g3 <<< 2)) + (g3 <<< 4)) + (g3 <<< 6)) -
        (g3 <<< 10)) - (g3 <<< 12)) - (g3 <<< 17)) + (g3 <<< 19)) + (g3 <<< 23)) +
        (g3 <<< 25)) - (g3 <<< 27)) + (g3 <<< 29)) - (g3 <<< 33)) + (g3 <<< 41)) -
        (g3 <<< 43)) - (g3 <<< 46)) - (g3 <<< 48)) + (g3 <<< 52)) - (g3 <<< 54)) +
        (g3 <<< 56)) + (g3 <<< 58)) - (g3 <<< 62)) + (g3 <<< 64)))
    (f5 : g5 = g4 ^^^ (g4 >>> 33)) :
    h5 = g5 := by
  bv_cut_qbe

theorem thm_fmix32_let (h0 : BitVec 32) :
    let h1 := h0 ^^^ (h0 >>> 16)
    let h2 := h1 * 0x85ebca6b#32
    let h3 := h2 ^^^ (h2 >>> 13)
    let h4 := h3 * 0xc2b2ae35#32
    let h5 := h4 ^^^ (h4 >>> 16)
    let g1 := h0 ^^^ (h0 >>> 16)
    let g2 :=
      ((((((((((((0#32 - g1) - (g1 <<< 2)) - (g1 <<< 4)) + (g1 <<< 7)) + (g1 <<< 9)) +
        (g1 <<< 11)) - (g1 <<< 14)) - (g1 <<< 18)) - (g1 <<< 20)) - (g1 <<< 25)) +
        (g1 <<< 27)) + (g1 <<< 31))
    let g3 := g2 ^^^ (g2 >>> 13)
    let g4 :=
      ((((((((((((((g3 + (g3 <<< 2)) - (g3 <<< 4)) + (g3 <<< 6)) - (g3 <<< 9)) -
        (g3 <<< 12)) - (g3 <<< 14)) - (g3 <<< 16)) + (g3 <<< 18)) - (g3 <<< 20)) -
        (g3 <<< 22)) - (g3 <<< 24)) + (g3 <<< 26)) - (g3 <<< 30)) + (g3 <<< 32))
    let g5 := g4 ^^^ (g4 >>> 16)
    h5 = g5 := by
  bv_cut_qbe

/-! ## 5. Explicit Cutpoint Lists (`bv_cut_qbe [e1 = e2, ...]`) -/

theorem thm_explicit_cut_compound (a b c : BitVec 64) :
    ((a ^^^ b) + ((a &&& b) <<< 1#64)) + c = c + (a + b) := by
  bv_cut_qbe [(a ^^^ b) + ((a &&& b) <<< 1#64) = a + b]

theorem thm_explicit_cut_multi (x0 y0 x1 y1 u1 v1 : BitVec 32)
    (hx1 : x1 = x0 + y0) (hy1 : y1 = y0.rotateLeft 7 ^^^ x1)
    (hu1 : u1 = (x0 ^^^ y0) + ((x0 &&& y0) <<< 1))
    (hv1 : v1 = ((y0 <<< 7) ||| (y0 >>> 25)) ^^^ u1) :
    x1 ++ y1 = u1 ++ v1 := by
  bv_cut_qbe [x1 = u1, y1 = v1]

/-! ## 6. Side-Condition Retention (`P1-3`), Misleading Wire Names, and `+uf` Bailout -/

theorem thm_side_cond_direct (a b : BitVec 32) (h : a < 100#32) :
    let x1 := if a < 200#32 then a + b else 0#32
    let x2 := x1.rotateLeft 5 ^^^ a
    let u1 := (a ^^^ b) + ((a &&& b) <<< 1)
    let u2 := ((u1 <<< 5) ||| (u1 >>> 27)) ^^^ a
    x2 = u2 := by
  bv_cut_qbe

theorem thm_side_cond_transitive (a b c : BitVec 32)
    (h1 : a < b) (h2 : b < 100#32) :
    let x1 := if a < 150#32 then a + c else 7#32
    let x2 := x1 ^^^ c
    let u1 := (a ^^^ c) + ((a &&& c) <<< 1)
    let u2 := u1 ^^^ c
    x2 = u2 := by
  bv_cut_qbe

theorem thm_side_cond_indirect_fallback (a b : BitVec 32) (h : a < 100#32) :
    let x1 := a + 1#32
    let u1 := (a ^^^ 1#32) + ((a &&& 1#32) <<< 1)
    let x2 := if x1 < 200#32 then x1 + b else 0#32
    let u2 := (u1 ^^^ b) + ((u1 &&& b) <<< 1)
    x2 = u2 := by
  bv_cut_qbe

theorem thm_misleading_names (a b c : BitVec 32) :
    let m1 := if a.ult b then a else b
    let g_out := if m1.ult c then m1 else c
    let m2 := if b.ult c then b else c
    let t_out := if a.ult m2 then a else m2
    g_out = t_out := by
  bv_cut_qbe

theorem thm_uf_bailout (f : BitVec 32 → BitVec 32) (x y : BitVec 32)
    (h : x ^^^ y = 0#32) : f x = f y := by
  bv_cut_qbe +uf

/-! ## 7. Programmatic Axiom, Timing, False-Cut, and Buggy-ARX CEX Verification -/

private def assertTrue (msg : String) (b : Bool) : IO Unit := do
  if !b then throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def stdAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

private def countBvSolveAxioms (env : Environment) : Nat :=
  env.constants.fold (init := 0) fun acc name _ =>
    if name.toString.contains "_leanqbe.bv_solve.ax" then acc + 1 else acc

private def assertZeroSolverAxioms (thmName : Name) : CoreM Unit := do
  let axs ← collectAxioms thmName
  for ax in axs do
    if !stdAxioms.contains ax then
      throwError "expected 0 solver axioms (<= std3) in {thmName}, found {ax}"

private def assertOnlyAllowedAxioms (thmName : Name) : CoreM Unit := do
  let axs ← collectAxioms thmName
  for ax in axs do
    if !stdAxioms.contains ax && !ax.toString.contains "_leanqbe.bv_solve.ax" then
      throwError "unexpected axiom {ax} in {thmName}"

private def mkArxGoalExpr (n : Nat) (injectBug : Bool) : MetaM Expr := do
  let rots : Array Nat := #[7, 9, 13, 18, 5, 11, 3, 25, 16, 12, 8, 21, 19, 23, 2, 29]
  let bv32 := mkApp (mkConst ``BitVec) (mkNatLit 32)
  let one32 := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 32) (mkNatLit 1)
  let rec build (rem : Nat) (xPrev yPrev uPrev vPrev : Expr) : MetaM Expr := do
    match rem with
    | 0 =>
      let lhs ← mkAppM ``HAppend.hAppend #[xPrev, yPrev]
      let rhs ← mkAppM ``HAppend.hAppend #[uPrev, vPrev]
      mkEq lhs rhs
    | rem' + 1 =>
      let i := n - rem
      let r := rots[i % rots.size]!
      let rGate := if injectBug && rem' == 0 then (r % 31) + 1 else r
      let xVal ← mkAppM ``HAdd.hAdd #[xPrev, yPrev]
      withLetDecl (Name.mkSimple s!"x{i + 1}") bv32 xVal fun xCur => do
        let rotY := mkApp3 (mkConst ``BitVec.rotateLeft) (mkNatLit 32) yPrev (mkNatLit r)
        let yVal ← mkAppM ``HXor.hXor #[rotY, xCur]
        withLetDecl (Name.mkSimple s!"y{i + 1}") bv32 yVal fun yCur => do
          let uvXor ← mkAppM ``HXor.hXor #[uPrev, vPrev]
          let uvAnd ← mkAppM ``HAnd.hAnd #[uPrev, vPrev]
          let shl1 ← mkAppM ``HShiftLeft.hShiftLeft #[uvAnd, one32]
          let uVal ← mkAppM ``HAdd.hAdd #[uvXor, shl1]
          withLetDecl (Name.mkSimple s!"u{i + 1}") bv32 uVal fun uCur => do
            let vL ← mkAppM ``HShiftLeft.hShiftLeft #[vPrev, mkNatLit rGate]
            let vR ← mkAppM ``HShiftRight.hShiftRight #[vPrev, mkNatLit (32 - rGate)]
            let vOr ← mkAppM ``HOr.hOr #[vL, vR]
            let vVal ← mkAppM ``HXor.hXor #[vOr, uCur]
            withLetDecl (Name.mkSimple s!"v{i + 1}") bv32 vVal fun vCur => do
              let body ← build rem' xCur yCur uCur vCur
              mkLetFVars #[xCur, yCur, uCur, vCur] body
  withLocalDeclD `x0 bv32 fun x0 =>
    withLocalDeclD `y0 bv32 fun y0 => do
      let body ← build n x0 y0 x0 y0
      mkForallFVars #[x0, y0] body

private def runCutTestCore : CoreM Unit := do
  -- 1. Zero-solver-axiom (`<= std3`) audit on H7 normalizer, H6a ring, and fmix32/fmix64!
  let zeroAxThms : List Name := [
    ``thm_shiftmul_64, ``thm_shiftmul_left_64, ``thm_shiftmul_pow2_64,
    ``thm_opt_share_128, ``thm_opt_share_right_mul_128,
    ``thm_opt_share_xor_cond_128, ``thm_opt_share_shl_64,
    ``thm_scoped_shiftmul_64, ``thm_scoped_opt_share_128,
    ``thm_mul_distrib_64, ``thm_reassoc_add_128,
    ``thm_fmix32_auto, ``thm_fmix64_auto, ``thm_fmix32_let
  ]
  for thm in zeroAxThms do
    assertZeroSolverAxioms thm

  -- 2. Zero custom axioms across every declaration in `BvDecideQbe.NormalizeRules`
  for nm in NormalizeRules.normalizeRuleNames ++ NormalizeRules.shiftLeftToMulRuleNames do
    assertZeroSolverAxioms nm

  -- 3. Soundness audit on all cut-discharged theorems (only std3 + per-goal bv_solve.ax)
  for thm in [``thm_arx_r16_hyps, ``thm_arx_r16_let, ``thm_explicit_cut_compound,
              ``thm_explicit_cut_multi, ``thm_side_cond_direct, ``thm_side_cond_transitive,
              ``thm_side_cond_indirect_fallback, ``thm_misleading_names, ``thm_uf_bailout] do
    assertOnlyAllowedAxioms thm

  MetaM.run' do
    -- 4. Timing gate: 16-round ARX equivalence via `bvCutQbe` <= 1.0 s!
    let arxProp ← mkArxGoalExpr 16 false
    let arxMVar ← mkFreshExprSyntheticOpaqueMVar arxProp
    let t0 ← IO.monoNanosNow
    bvCutQbe arxMVar.mvarId! {}
    let t1 ← IO.monoNanosNow
    let arxMs := (t1 - t0) / 1000000
    let arxPrf ← instantiateMVars arxMVar
    assertTrue "ARX-16 proof has no mvars/sorry" (!arxPrf.hasMVar && !arxPrf.hasSorry)
    assertTrue s!"ARX-16 bv_cut_qbe took {arxMs} ms (<= 1000 ms)" (arxMs ≤ 1000)
    IO.println s!"CutTest: ARX-16 bv_cut_qbe proved in {arxMs} ms"

    -- 5. Timing gate: `fmix32` + `fmix64` via `bvCutQbe` <= 2.0 s AND 0 solver axioms!
    let axBeforeFmix := countBvSolveAxioms (← getEnv)
    let fmix32Ty := (← getConstInfo ``thm_fmix32_auto).type
    let fmix64Ty := (← getConstInfo ``thm_fmix64_auto).type
    let m32 ← mkFreshExprSyntheticOpaqueMVar fmix32Ty
    let m64 ← mkFreshExprSyntheticOpaqueMVar fmix64Ty
    let tf0 ← IO.monoNanosNow
    bvCutQbe m32.mvarId! {}
    bvCutQbe m64.mvarId! {}
    let tf1 ← IO.monoNanosNow
    let fmixMs := (tf1 - tf0) / 1000000
    assertTrue "fmix32+fmix64 emitted 0 solver axioms"
      (countBvSolveAxioms (← getEnv) == axBeforeFmix)
    assertTrue s!"fmix32+fmix64 bv_cut_qbe took {fmixMs} ms (<= 2000 ms)" (fmixMs ≤ 2000)
    IO.println s!"CutTest: fmix32 + fmix64 bv_cut_qbe proved in {fmixMs} ms (0 solver axioms)"

    -- 6. Clean rejection on a false explicit cut (CEX emitted, 0 axioms added!)
    let bv16 := mkApp (mkConst ``BitVec) (mkNatLit 16)
    let axBeforeFalseCut := countBvSolveAxioms (← getEnv)
    let falseCutErr ← withLocalDeclD `a bv16 fun a =>
      withLocalDeclD `b bv16 fun b => do
        let abAdd ← mkAppM ``HAdd.hAdd #[a, b]
        let baAdd ← mkAppM ``HAdd.hAdd #[b, a]
        let abSub ← mkAppM ``HSub.hSub #[a, b]
        let goalTy ← mkEq abAdd baAdd
        let badCut ← mkEq abAdd abSub
        let mvar ← mkFreshExprSyntheticOpaqueMVar goalTy
        try
          bvCutQbe mvar.mvarId! {} none {} #[badCut]
          return none
        catch ex =>
          return some (← ex.toMessageData.toString)
    assertTrue "false explicit cut emitted 0 axioms"
      (countBvSolveAxioms (← getEnv) == axBeforeFalseCut)
    match falseCutErr with
    | some msg =>
      assertTrue s!"false explicit cut reports counterexample: {msg}"
        (msg.contains "counterexample")
    | none => throwError "false explicit cut unexpectedly succeeded!"

    -- 7. Clean rejection on a buggy 16-round ARX (CEX rejected cleanly, 0 axioms added!)
    let buggyArxProp ← mkArxGoalExpr 16 true
    let buggyMVar ← mkFreshExprSyntheticOpaqueMVar buggyArxProp
    let axBeforeBug := countBvSolveAxioms (← getEnv)
    let bugErr? ← try
      bvCutQbe buggyMVar.mvarId! {}
      pure none
    catch ex =>
      pure (some (← ex.toMessageData.toString))
    assertTrue "buggy ARX-16 emitted 0 solver axioms (early sim CEX skip!)"
      (countBvSolveAxioms (← getEnv) == axBeforeBug)
    match bugErr? with
    | some msg =>
      assertTrue s!"buggy ARX-16 reports counterexample: {msg}" (msg.contains "counterexample")
    | none => throwError "buggy ARX-16 unexpectedly succeeded!"

  IO.println "CutTest: ALL PASSED (shiftmul, opt_share, ARX-16, fmix32/64, side-cond, CEX)"

def runAll : IO Unit := do
  let opts : Options := {}
  let env ← importModules #[{ module := `BvDecideQbeTest.CutTest }] opts
  let ctx : Core.Context := { fileName := "CutTest.lean", fileMap := default }
  let ((), _) ← (runCutTestCore.toIO ctx { env := env })
  pure ()

#eval runCutTestCore

end BvDecideQbeTest.CutTest

def main : IO Unit := BvDecideQbeTest.CutTest.runAll
