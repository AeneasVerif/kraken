module

import LeanQbe.T.ZeroPeelLemmas
import LeanQbe.T.WPLemmas
import LeanQbe.T.FlatLemmas
import LeanQbe.T.Logic.Rules
import LeanQbe.T.ZeroPeel

/-!
# Tests of `LeanQbe.T.ZeroPeel`

Covers:
1. Bounded 1st-iteration loop peeling (`peelSingle`) on an LEB128-style single-byte fast-path
   loop (`readByteLoop`), verifying the peeled AST, `Func.checkTFlat`, `Func.Wf`, and fast-path
   + inductive WP soundness (`Func.zeroPeel_spec`).
2. Guard behavior: `peelImmOnly` default (`true`) vs `false` on `varEntryLoop`, `peelBudget := 0`,
   `maxFnSize` cap, `unrollN := 0` / `65`, and nested/multi-block loop preservation.
3. Wide constant-fill loop widening (`widenFillSingle`):
   - Byte zero-fill (`memsetZero8`: `i8`, `0#8`, `shift = 0`, `off? = none`, `.ult`) verified over
     `array ptr xs` via `wp_store_array` and `Func.zeroPeel_spec`.
   - Shifted qword non-zero fill (`fillQwordOff`: `i64`, `off? = some`, `shift = 3`, `.ule`,
     commuted `1 + i`), checking widened AST loop count and `Func.zeroPeel_{wf,callsOk}`.
4. Direct `TFlat.wfCheck_zeroPeelWith`, `Func.zeroPeelWith_*`, `Fn.zeroPeel_*`,
   `Module.zeroPeel_ok`, and `#print axioms` verification across all 11 exported theorems.
-/

set_option autoImplicit false

namespace LeanQbe.T.ZeroPeelTest

open LeanQbe.T

/-! ## 1. Bounded 1st-iter loop peeling (`readByteLoop`) -/

/-- Single-block byte-scanning loop modeled on LEB128 varint decoding: returns immediately on a
byte `<u 128`, otherwise advances `(p + 1, n + 1)` up to `10` bytes. Entry passes `.imm 0`,
firing `peelSingle` under default `ZeroPeelConfig`. -/
def readByteLoop : Func [i64] [.bits 8] := fun _ _ (ptr, ()) =>
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

theorem readByteLoop_peel_out : Func.zeroPeel readByteLoop = fun _ _ (ptr, ()) =>
    .group (sig := [[i64, i64]])
      (fun (loop, ()) => .cons (fun (p, n, ()) =>
        .load (.bits 8) (.var p) fun b2 =>
        .let_ (op2 (.ult (.bits 8)) (.var b2) (.imm 128#8)) fun (c2, ()) =>
        .jnz (.var c2) (.ret (.var b2, ()))
          (.let_ (op2 (.add i64) (.var p) (.imm 1)) fun (p2', ()) =>
           .let_ (op2 (.add i64) (.var n) (.imm 1)) fun (n2', ()) =>
           .let_ (op2 (.ult i64) (.var n2') (.imm 10)) fun (ok2, ()) =>
           .jnz (.var ok2) (.jump loop (.var p2', .var n2', ()))
             (.ret (.var b2, ())))) .nil)
      (fun (loop, ()) =>
        .let_ (op1 (.copy i64) (.var ptr)) fun (p0, ()) =>
        .let_ (op1 (.copy i64) (.imm 0)) fun (n0, ()) =>
        .load (.bits 8) (.var p0) fun b =>
        .let_ (op2 (.ult (.bits 8)) (.var b) (.imm 128#8)) fun (c, ()) =>
        .jnz (.var c) (.ret (.var b, ()))
          (.let_ (op2 (.add i64) (.var p0) (.imm 1)) fun (p', ()) =>
           .let_ (op2 (.add i64) (.var n0) (.imm 1)) fun (n', ()) =>
           .let_ (op2 (.ult i64) (.var n') (.imm 10)) fun (ok, ()) =>
           .jnz (.var ok) (.jump loop (.var p', .var n', ()))
             (.ret (.var b, ())))) := by
  t_kernel_rfl

theorem readByteLoop_wf : readByteLoop.Wf := by t_wf_reify
theorem readByteLoop_peel_wf : (Func.zeroPeel readByteLoop).Wf := Func.zeroPeel_wf readByteLoop_wf
theorem readByteLoop_peel_checkTFlat : Func.checkTFlat (Func.zeroPeel readByteLoop) = true := by
  t_kernel_rfl

theorem readByteLoop_peel_fast_spec (Γ : Env) (ptr : BitVec 64) (v : BitVec 8)
    (hv : v < 128#8) (R : Mem 64 → Prop) (m : Mem 64)
    (hm : (cell (t := .bits 8) ptr v ⋆ R) m) (X : XPost) :
    Func.spec Γ (Func.zeroPeel readByteLoop) (ptr, ()) m
      (fun (r, ()) m' => r = v ∧ m' = m) X := by
  rw [readByteLoop_peel_out]
  dsimp only [Func.spec, Func.wp]
  refine wp_loop_group (fun _ _ _ => False) ?_ ?_
  · rintro _ _ _ _ _ hFalse; exact False.elim hFalse
  · intro _ _
    wp_unfold
    refine ⟨v, loadVal_cell (by decide) hm, ?_⟩
    have hlt : BitVec.ult v 128#8 = true := BitVec.ult_iff_lt.mpr hv
    simp [hlt]

theorem readByteLoop_fast_base_spec (Γ : Env) (ptr : BitVec 64) (v : BitVec 8)
    (hv : v < 128#8) (R : Mem 64 → Prop) (m : Mem 64)
    (hm : (cell (t := .bits 8) ptr v ⋆ R) m) (X : XPost) :
    Func.spec Γ readByteLoop (ptr, ()) m (fun (r, ()) m' => r = v ∧ m' = m) X := by
  dsimp only [Func.spec, Func.wp, readByteLoop]
  refine wp_loop1 _ _ (fun _ (x : Tup Val [i64, i64]) m' => x.1 = ptr ∧ m' = m) ?_ ?_
  · rintro _ _ ⟨p, n, ⟨⟩⟩ m' _ ⟨rfl, rfl⟩
    refine wp_load_cell (by decide) hm ?_
    wp_unfold
    have hlt : BitVec.ult v 128#8 = true := BitVec.ult_iff_lt.mpr hv
    simp [hlt]
  · intro J hJ
    wp_unfold
    exact hJ 0 (ptr, 0#64, ()) m ⟨rfl, rfl⟩

theorem readByteLoop_zeroPeel_spec (Γ : Env) (ptr : BitVec 64) (v : BitVec 8)
    (hv : v < 128#8) (R : Mem 64 → Prop) (m : Mem 64)
    (hm : (cell (t := .bits 8) ptr v ⋆ R) m) (X : XPost) :
    Func.spec Γ (Func.zeroPeel readByteLoop) (ptr, ()) m
      (fun (r, ()) m' => r = v ∧ m' = m) X :=
  Func.zeroPeel_spec readByteLoop_wf {} (readByteLoop_fast_base_spec Γ ptr v hv R m hm X)

/-! ## 2. Configuration guards (`peelImmOnly`, `peelBudget`, `maxFnSize`, nested loops) -/

/-- Loop whose entry jump supplies only `.var` operands (`peelImmOnly := true` skips it). -/
def varEntryLoop : Func [i64, i64] [i64] := fun _ _ (n, acc0, ()) =>
  loop1 (ts := [i64, i64])
    (fun loop (i, acc, ()) =>
      .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
      .jnz (.var z) (.ret (.var acc, ()))
        (.let_ (op2 (.add i64) (.var acc) (.var i)) fun (acc', ()) =>
         .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
         .jump loop (.var i', .var acc', ())))
    (fun loop => .jump loop (.var n, .var acc0, ()))

theorem varEntryLoop_wf : varEntryLoop.Wf := by t_wf_reify

theorem varEntryLoop_default_unchanged :
    Func.zeroPeel varEntryLoop = varEntryLoop := by t_kernel_rfl

theorem varEntryLoop_peelImmFalse_peels :
    Func.zeroPeelWith { peelImmOnly := false } varEntryLoop = fun _ _ (n, acc0, ()) =>
      .group (sig := [[i64, i64]])
        (fun (loop, ()) => .cons (fun (i, acc, ()) =>
          .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z2, ()) =>
          .jnz (.var z2) (.ret (.var acc, ()))
            (.let_ (op2 (.add i64) (.var acc) (.var i)) fun (acc2, ()) =>
             .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i2, ()) =>
             .jump loop (.var i2, .var acc2, ()))) .nil)
        (fun (loop, ()) =>
          .let_ (op1 (.copy i64) (.var n)) fun (i0, ()) =>
          .let_ (op1 (.copy i64) (.var acc0)) fun (a0, ()) =>
          .let_ (op2 (.eq i64) (.var i0) (.imm 0)) fun (z, ()) =>
          .jnz (.var z) (.ret (.var a0, ()))
            (.let_ (op2 (.add i64) (.var a0) (.var i0)) fun (acc', ()) =>
             .let_ (op2 (.sub i64) (.var i0) (.imm 1)) fun (i', ()) =>
             .jump loop (.var i', .var acc', ()))) := by
  t_kernel_rfl

theorem readByteLoop_budget0_unchanged :
    Func.zeroPeelWith { peelBudget := 0 } readByteLoop = readByteLoop := by t_kernel_rfl

theorem readByteLoop_maxFnSize1_unchanged :
    Func.zeroPeelWith { maxFnSize := 1 } readByteLoop = readByteLoop := by t_kernel_rfl

/-- Nested loop whose outer body has `zpLoops > 0` (outer peeling blocked, inner eligible). -/
def nestedGuardLoop : Func [i64] [i64] := fun _ _ (n, ()) =>
  loop1 (ts := [i64])
    (fun outer (i, ()) =>
      .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
      .jnz (.var z) (.ret (.imm 0, ()))
        (loop1 (ts := [i64])
          (fun inner (j, ()) =>
            .let_ (op2 (.eq i64) (.var j) (.imm 0)) fun (zj, ()) =>
            .jnz (.var zj)
              (.let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
               .jump outer (.var i', ()))
              (.let_ (op2 (.sub i64) (.var j) (.imm 1)) fun (j', ()) =>
               .jump inner (.var j', ())))
          (fun inner => .jump inner (.imm 3, ()))))
    (fun outer => .jump outer (.var n, ()))

theorem nestedGuardLoop_wf : nestedGuardLoop.Wf := by t_wf_reify
theorem nestedGuardLoop_zpLoops :
    ZeroPeel.zpLoops (reifyFunc (Func.zeroPeel nestedGuardLoop)) = 2 := by t_kernel_rfl

/-! ## 3. Wide constant-fill loop widening (`widenFillSingle`) -/

/-- Byte-fill loop (`shift = 0`, `off? = none`, `0#8`, `.ult`): widens into an unrolled `8x i64`
zero-fill inner loop + enclosing scalar tail loop. -/
def memsetZero8 : Func [i64, i64] [i64] := fun _ _ (ptr, n, ()) =>
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

theorem memsetZero8_wf : memsetZero8.Wf := by t_wf_reify
theorem memsetZero8_zeroPeel_wf : (Func.zeroPeel memsetZero8).Wf := Func.zeroPeel_wf memsetZero8_wf
theorem memsetZero8_zeroPeel_checkTFlat : Func.checkTFlat (Func.zeroPeel memsetZero8) = true := by
  t_kernel_rfl

theorem memsetZero8_widens_loops :
    ZeroPeel.zpLoops (reifyFunc (Func.zeroPeel memsetZero8)) = 2 := by decide

theorem memsetZero8_disabled_unchanged :
    Func.zeroPeelWith { unrollN := 0, peelBudget := 0 } memsetZero8 = memsetZero8 := by
  t_kernel_rfl

theorem memsetZero8_unroll65_disabled :
    Func.zeroPeelWith { unrollN := 65, peelBudget := 0 } memsetZero8 = memsetZero8 := by
  t_kernel_rfl

theorem memsetZero8_array_spec (Γ : Env) (ptr : BitVec 64) (xs : List (Val (.bits 8)))
    (hxs : xs.length < 2 ^ 64) (R : Mem 64 → Prop) (m : Mem 64)
    (hm : (array ptr xs ⋆ R) m) (X : XPost) :
    Func.spec Γ memsetZero8 (ptr, BitVec.ofNat 64 xs.length, ()) m
      (fun (r, ()) m' =>
        r = ptr ∧ ∃ ys : List (Val (.bits 8)),
          ys.length = xs.length ∧ (∀ k < xs.length, ys[k]? = some 0#8) ∧
          (array ptr ys ⋆ R) m')
      X := by
  dsimp only [Func.spec, Func.wp, memsetZero8]
  refine wp_loop1 _ _
    (fun cnt (x : Tup Val [i64]) m' =>
      x.1.toNat + cnt = xs.length ∧
      ∃ ys : List (Val (.bits 8)),
        ys.length = xs.length ∧ (∀ k < x.1.toNat, ys[k]? = some 0#8) ∧ (array ptr ys ⋆ R) m')
    ?_ ?_
  · rintro J cnt ⟨i, ⟨⟩⟩ m' hJ ⟨hsum, ys, hlen, hzero, hmem⟩
    dsimp only at hsum hzero
    wp_unfold
    have hn : (BitVec.ofNat 64 xs.length).toNat = xs.length := by
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxs]
    by_cases hlt : i < BitVec.ofNat 64 xs.length
    · have hc : BitVec.ult i (BitVec.ofNat 64 xs.length) = true := BitVec.ult_iff_lt.mpr hlt
      have hilt : i.toNat < xs.length := by rw [← hn]; exact BitVec.lt_def.mp hlt
      simp only [hc, true_implies]
      have haddr : ptr + i = ptr + BitVec.ofNat 64 ((Ty.bits 8).bytes * i.toNat) := by
        rw [show (Ty.bits 8).bytes = 1 by decide, Nat.one_mul, BitVec.ofNat_toNat,
          BitVec.setWidth_eq]
      obtain ⟨hok, hm''⟩ := store_array 0#8 (by decide) (by omega : i.toNat < ys.length) hmem
      refine ⟨⟨haddr ▸ hok, ?_⟩, fun h => False.elim (by cases h)⟩
      refine hJ (cnt - 1) (i + 1, ()) _ (by omega) ?_
      have h1 : (1 : BitVec 64).toNat = 1 := rfl
      have hadd : (i + (1 : BitVec 64)).toNat = i.toNat + 1 := by
        rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
      refine ⟨by dsimp only; rw [hadd]; omega, ys.set i.toNat 0#8, by simp [hlen], ?_,
        haddr ▸ hm''⟩
      intro k hk
      dsimp only at hk
      rw [hadd] at hk
      rw [List.getElem?_set]
      split
      · have : i.toNat < ys.length := by omega
        simp [this]
      · exact hzero k (by omega)
    · have hcf : BitVec.ult i (BitVec.ofNat 64 xs.length) = false := by
        rw [Bool.eq_false_iff]; intro h
        exact hlt (BitVec.ult_iff_lt.mp h)
      have hige : xs.length ≤ i.toNat := by
        rw [← hn]; exact Nat.le_of_not_lt (fun h => hlt (BitVec.lt_def.mpr h))
      have hieq : i.toNat = xs.length := by omega
      simp only [hcf, false_implies, Bool.false_eq_true, true_implies, true_and]
      exact ⟨ys, hlen, fun k hk => hzero k (by omega), hmem⟩
  · intro J hJ
    wp_unfold
    refine hJ xs.length (0#64, ()) m ⟨by simp, xs, rfl, ?_, hm⟩
    intro _ hk; simp at hk

theorem memsetZero8_zeroPeel_array_spec
    (Γ : Env) (ptr : BitVec 64) (xs : List (Val (.bits 8)))
    (hxs : xs.length < 2 ^ 64) (R : Mem 64 → Prop) (m : Mem 64)
    (hm : (array ptr xs ⋆ R) m) (X : XPost) :
    Func.spec Γ (Func.zeroPeel memsetZero8) (ptr, BitVec.ofNat 64 xs.length, ()) m
      (fun (r, ()) m' =>
        r = ptr ∧ ∃ ys : List (Val (.bits 8)),
          ys.length = xs.length ∧ (∀ k < xs.length, ys[k]? = some 0#8) ∧
          (array ptr ys ⋆ R) m')
      X :=
  Func.zeroPeel_spec memsetZero8_wf {} (memsetZero8_array_spec Γ ptr xs hxs R m hm X)

/-- Shifted qword non-zero fill (`shift = 3`, `off? = some`, `.ule`, commuted `1 + i`). -/
def fillQwordOff : Func [i64, i64, i64, i64] [i64] := fun _ _ (base, off, init, bnd, ()) =>
  loop1 (ts := [i64])
    (fun loop (i, ()) =>
      .let_ (op2 (.ule i64) (.var i) (.var bnd)) fun (cond, ()) =>
      .jnz (.var cond)
        (.let_ (op2 (.add i64) (.var off) (.var i)) fun (idx, ()) =>
         .let_ (op2 (.shl i64) (.var idx) (.imm 3)) fun (scaled, ()) =>
         .let_ (op2 (.add i64) (.var base) (.var scaled)) fun (addr, ()) =>
         .store (t := i64) (.imm 0x0102030405060708#64) (.var addr)
           (.let_ (op2 (.add i64) (.imm 1) (.var i)) fun (i', ()) =>
            .jump loop (.var i', ())))
        (.ret (.var base, ())))
    (fun loop => .jump loop (.var init, ()))

theorem fillQwordOff_wf : fillQwordOff.Wf := by t_wf_reify
theorem fillQwordOff_zeroPeel_wf : (Func.zeroPeel fillQwordOff).Wf :=
  Func.zeroPeel_wf fillQwordOff_wf
theorem fillQwordOff_zeroPeel_checkTFlat : Func.checkTFlat (Func.zeroPeel fillQwordOff) = true := by
  t_kernel_rfl
theorem fillQwordOff_widens_loops :
    ZeroPeel.zpLoops (reifyFunc (Func.zeroPeel fillQwordOff)) = 2 := by decide

theorem fillQwordOff_zeroPeel_callsOk :
    ((Func.zeroPeel fillQwordOff) (fun _ => Unit) (fun _ => Unit) (Tup.units _)).callsOk [] [] := by
  apply Func.zeroPeel_callsOk fillQwordOff_wf
  dsimp only [fillQwordOff, loop1, Expr.callsOk, Blocks.callsOk]
  trivial

/-! ## 4. Direct `TFlat`, `Func.zeroPeelWith`, `Fn.zeroPeel`, `Module.zeroPeel_ok`, and axioms -/

theorem reified_wfCheck_zeroPeelWith :
    (TFlat.zeroPeelWith {} (reifyFunc memsetZero8)).wfCheck
      (pushTypes [i64, i64] []) [] = true := by
  apply TFlat.wfCheck_zeroPeelWith
  decide

theorem readByteLoop_zeroPeelWith_wf :
    (Func.zeroPeelWith { peelBudget := 36 } readByteLoop).Wf :=
  Func.zeroPeelWith_wf { peelBudget := 36 } readByteLoop_wf

def readByteLoopFn : Fn := ⟨"readByteLoop", [i64], [.bits 8], readByteLoop⟩
def memsetZero8Fn : Fn := ⟨"memsetZero8", [i64, i64], [i64], memsetZero8⟩

theorem memsetZero8Fn_sig :
    memsetZero8Fn.zeroPeel.name = "memsetZero8" ∧
    memsetZero8Fn.zeroPeel.as = [i64, i64] ∧
    memsetZero8Fn.zeroPeel.rs = [i64] :=
  ⟨rfl, rfl, rfl⟩

theorem memsetZero8Fn_wf : (memsetZero8Fn.zeroPeel).Wf :=
  Fn.zeroPeel_wf (fn := memsetZero8Fn) memsetZero8_wf

theorem memsetZero8Fn_spec (Γ : Env) (ptr : BitVec 64) (xs : List (Val (.bits 8)))
    (hxs : xs.length < 2 ^ 64) (R : Mem 64 → Prop) (m : Mem 64)
    (hm : (array ptr xs ⋆ R) m) (X : XPost) :
    Func.spec Γ (memsetZero8Fn.zeroPeel).body (ptr, BitVec.ofNat 64 xs.length, ()) m
      (fun (r, ()) m' =>
        r = ptr ∧ ∃ ys : List (Val (.bits 8)),
          ys.length = xs.length ∧ (∀ k < xs.length, ys[k]? = some 0#8) ∧
          (array ptr ys ⋆ R) m')
      X :=
  Fn.zeroPeel_spec memsetZero8Fn memsetZero8_wf {}
    (memsetZero8_array_spec Γ ptr xs hxs R m hm X)

def sampleModule : Module := { fns := [readByteLoopFn, memsetZero8Fn] }

def emptyEnv : Env := fun _ _ _ _ _ _ _ => False

theorem sampleModule_ok :
    ModuleOk emptyEnv { sampleModule with fns := sampleModule.fns.map (Fn.zeroPeel · {}) } := by
  refine Module.zeroPeel_ok (Γ := emptyEnv) ?_ {}
  refine ⟨by
    simp [Module.namesNodup, Module.names, sampleModule, readByteLoopFn, memsetZero8Fn], ?_⟩
  intro pre fn post hsplit
  dsimp only [sampleModule] at hsplit
  rcases pre with _ | ⟨a, pre⟩
  · cases hsplit
    refine ⟨readByteLoop_wf, ?_, fun _ _ _ _ h => False.elim h⟩
    dsimp only [Fn.callsOk, readByteLoopFn, readByteLoop, loop1, Expr.callsOk, Blocks.callsOk]
    trivial
  · rcases pre with _ | ⟨_, pre⟩
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hsplit
      rcases hsplit with ⟨rfl, rfl, rfl⟩
      refine ⟨memsetZero8_wf, ?_, fun _ _ _ _ h => False.elim h⟩
      dsimp only [Fn.callsOk, memsetZero8Fn, memsetZero8, loop1, Expr.callsOk, Blocks.callsOk]
      trivial
    · have hlen := congrArg List.length hsplit
      simp at hlen

/-! ## 5. Regression: `> 600`-node fill function widened under default `maxFnSize` (`4000`) -/

/-- Balanced `.jnz` tree of depth `d` embedding `mainE` alongside `altE` (`> 600` nodes at depth
`9`, keeping AST recursion depth `O(d)`). -/
def padBranch {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    Nat → Expr V L rs → Expr V L rs → Expr V L rs
  | 0, mainE, _ => mainE
  | n + 1, mainE, altE =>
    .jnz (.imm false) (padBranch n altE altE) (padBranch n mainE altE)

private theorem padBranch_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (n : Nat) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {m₁ a₁ : Expr V₁ L₁ rs} {m₂ a₂ : Expr V₂ L₂ rs}
    (hm : Wf G D m₁ m₂) (ha : Wf G D a₁ a₂) :
    Wf G D (padBranch n m₁ a₁) (padBranch n m₂ a₂) := by
  induction n generalizing m₁ m₂ a₁ a₂ with
  | zero => exact hm
  | succ _ ih => exact .jnz (.imm _) (ih ha ha) (ih hm ha)

/-- Byte zero-fill loop embedded in a `> 600`-node body (`zpSize > 600`, depth `< 25`). -/
def bigMemsetZero8 : Func [i64, i64] [i64] := fun V L (ptr, n, ()) =>
  padBranch 9 (memsetZero8 V L (ptr, n, ())) (.ret (.imm 0, ()))

theorem bigMemsetZero8_wf : bigMemsetZero8.Wf :=
  fun _ _ _ _ _ _ =>
    padBranch_wf 9 (memsetZero8_wf _ _ _ _ _ _) (.ret (.cons (.imm _) .nil))

theorem bigMemsetZero8_size_gt_600 :
    ZeroPeel.zpSize (reifyFunc bigMemsetZero8) > 600 := by decide

theorem bigMemsetZero8_cap600_unchanged :
    ZeroPeel.zpLoops (reifyFunc (Func.zeroPeelWith { maxFnSize := 600 } bigMemsetZero8)) = 1 := by
  decide

theorem bigMemsetZero8_widens_loops :
    ZeroPeel.zpLoops (reifyFunc (Func.zeroPeel bigMemsetZero8)) = 2 := by decide

theorem bigMemsetZero8_zeroPeel_wf : (Func.zeroPeel bigMemsetZero8).Wf :=
  Func.zeroPeel_wf bigMemsetZero8_wf

#print axioms LeanQbe.T.TFlat.wfCheck_zeroPeelWith
#print axioms LeanQbe.T.Func.zeroPeelWith_wf
#print axioms LeanQbe.T.Func.zeroPeelWith_spec
#print axioms LeanQbe.T.Func.zeroPeelWith_callsOk
#print axioms LeanQbe.T.Func.zeroPeel_wf
#print axioms LeanQbe.T.Func.zeroPeel_spec
#print axioms LeanQbe.T.Func.zeroPeel_callsOk
#print axioms LeanQbe.T.Fn.zeroPeel_wf
#print axioms LeanQbe.T.Fn.zeroPeel_spec
#print axioms LeanQbe.T.Fn.zeroPeel_callsOk
#print axioms LeanQbe.T.Module.zeroPeel_ok
#print axioms LeanQbe.T.ZeroPeelTest.readByteLoop_peel_fast_spec
#print axioms LeanQbe.T.ZeroPeelTest.memsetZero8_zeroPeel_array_spec
#print axioms LeanQbe.T.ZeroPeelTest.bigMemsetZero8_zeroPeel_wf

end LeanQbe.T.ZeroPeelTest
