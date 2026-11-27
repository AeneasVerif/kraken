module

public import LeanQbe.T.LoopRotateLemmas
public import LeanQbe.T.OptFlatLoopLemmas
public import LeanQbe.T.MainFlatLemmas
public import LeanQbe.T.Logic.Rules
public import LeanQbe.T.Amd64.Targ
public import LeanQbe.T.Examples.Kissat.FullM4
public import LeanQbe.T.Examples.Kissat.Plain
meta import LeanQbe.T.LoopRotate
meta import LeanQbe.T.OptFlatLoop
meta import LeanQbe.T.MainFlat
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM4
meta import LeanQbe.T.Examples.Kissat.Plain

/-!
# Regression, Soundness & Native `TFlat` Parity Tests: Relaxed `LoopRotate`

Covers:
1. Safe header-load rotation (`allowLoadHdr := true` in `defaultRotConfig`):
   - `arrayScanLoadLoop` (`while (a[i] != 0) i++;`): exact `t_kernel_rfl` rotated output,
     `Func.loopRotate_wf`, `Func.checkTFlat`, full `array`-backed `Func.spec` soundness proof,
     and native `OptFlatLoop.loopRotateFlat` parity (`loopRotateFlat_eq` + `t_kernel_rfl`).
   - `watchHdrLoadLoop` (BCP watch-header `i8` load + `dir = false` + `ExitMode.wrap` +
     `callsOk`): `Func.loopRotate_wf`, `Func.loopRotate_callsOk`, `checkTFlat`, and `TFlat` parity.
2. Widened continuation live-var counts (`maxContLiveVars := 16` vs old `4`):
   - `widePartialLoop` (`8` loop vars in partial tail-edge mode): skipped at `maxContLiveVars := 4`,
     rotated under `defaultRotConfig`, with `Func.loopRotate_spec` and `TFlat` parity.
   - `wideHdrLiveLoop` (`5` live header temps in `contArm`): skipped at `4`, rotated at `16`,
     with `TFlat` parity.
   - `tooWideLoop` (`17` loop vars `> 16`): negative guard stays unrotated under `defaultRotConfig`.
3. Negative guards (must NOT rotate under `defaultRotConfig`):
   - Header `.store`, header `.call`, header trapping ops (`.udiv`, `.sdiv`, `.fptoui`),
     adversarial `Func.loopRotateWithPlan` trapping-op rejection, and `allowLoadHdr := false`.
4. Native `TFlat` parity & measured rotation counts across `FullM4` (`231` fns + `optInline 40`)
   and `Kissat.Plain` (`59` fns), plus `#print axioms` audit (`⊆ std3`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.LoopRotateLoadHdrTest

open LeanQbe.T
open LeanQbe.T.LoopRotate
open LeanQbe.T.Examples.Kissat.FullM4
open LeanQbe.T.Examples.Kissat.Plain

/-! ## 1. Safe header-load rotation (`while (a[i] != 0) i++;` & BCP watch-header) -/

/-- `while (a[i] != 0) { i++; }` with address arithmetic + `i32` array load in header. -/
def arrayScanLoadLoop : Func [i64, i64] [i64] := fun _ _ (base, i0, ()) =>
  loop1 (ts := [i64])
    (fun loop (i, ()) =>
      .let_ (op2 (.shl i64) (.var i) (.imm 2)) fun (off, ()) =>
      .let_ (op2 (.add i64) (.var base) (.var off)) fun (ptr, ()) =>
      .load i32 (.var ptr) fun v =>
      .let_ (op2 (.ne i32) (.var v) (.imm 0)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
         .jump loop (.var i', ()))
        (.ret (.var i, ())))
    (fun loop => .jump loop (.var i0, ()))

theorem arrayScanLoadLoop_old_noRot :
    (buildRotPlan (as := [i64, i64]) { allowLoadHdr := false }
      (reifyFunc arrayScanLoadLoop)).hasRot = false := by
  t_kernel_rfl

theorem arrayScanLoadLoop_default_rot :
    (buildRotPlan (as := [i64, i64]) defaultRotConfig
      (reifyFunc arrayScanLoadLoop)).hasRot = true := by
  t_kernel_rfl

theorem arrayScanLoadLoop_rot_out : Func.loopRotate arrayScanLoadLoop = fun _ _ (base, i0, ()) =>
    .group (sig := [[i64]])
      (fun (loopRot, ()) => .cons (fun (i, ()) =>
        .let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
        .let_ (op2 (.shl i64) (.var i') (.imm 2)) fun (off1, ()) =>
        .let_ (op2 (.add i64) (.var base) (.var off1)) fun (ptr1, ()) =>
        .load i32 (.var ptr1) fun v1 =>
        .let_ (op2 (.ne i32) (.var v1) (.imm 0)) fun (c1, ()) =>
        .jnz (.var c1) (.jump loopRot (.var i', ())) (.ret (.var i', ()))) .nil)
      (fun (loopRot, ()) =>
        .let_ (op2 (.shl i64) (.var i0) (.imm 2)) fun (off0, ()) =>
        .let_ (op2 (.add i64) (.var base) (.var off0)) fun (ptr0, ()) =>
        .load i32 (.var ptr0) fun v0 =>
        .let_ (op2 (.ne i32) (.var v0) (.imm 0)) fun (c0, ()) =>
        .jnz (.var c0) (.jump loopRot (.var i0, ())) (.ret (.var i0, ()))) := by
  t_kernel_rfl

theorem arrayScanLoadLoop_wf : arrayScanLoadLoop.Wf := by t_wf_reify

theorem arrayScanLoadLoop_rot_wf : (Func.loopRotate arrayScanLoadLoop).Wf :=
  Func.loopRotate_wf arrayScanLoadLoop_wf

theorem arrayScanLoadLoop_rot_checkTFlat :
    Func.checkTFlat (Func.loopRotate arrayScanLoadLoop) = true := by
  t_kernel_rfl

theorem arrayScanLoadLoop_flat_parity :
    OptFlatLoop.loopRotateFlat [i64, i64] (reifyFunc arrayScanLoadLoop) =
      reifyFunc (Func.loopRotate arrayScanLoadLoop) := by
  t_kernel_rfl

theorem arrayScanLoadLoop_flat_denote_eq :
    denoteFunc (as := [i64, i64])
      (OptFlatLoop.loopRotateFlat [i64, i64] (reifyFunc arrayScanLoadLoop)) =
      Func.loopRotate arrayScanLoadLoop := by
  rw [OptFlatLoop.denoteFunc_loopRotateFlat _ defaultRotConfig
      (PassFlatKit.reifyFunc_wfCheck arrayScanLoadLoop_wf)]
  change Func.loopRotate (Func.renorm arrayScanLoadLoop) = Func.loopRotate arrayScanLoadLoop
  rw [Func.renorm_eq_self arrayScanLoadLoop_wf]

/-- Source `Func.spec` for `arrayScanLoadLoop` over an `i32` array `xs` with zero terminator
at index `z < xs.length` (all elements `< z` are nonzero). -/
theorem arrayScanLoadLoop_src_spec (Γ : Env) (base : BitVec 64) (xs : List (BitVec 32)) (z : Nat)
    (hz : z < xs.length) (hxs : xs[z] = 0#32)
    (hnz : ∀ k, k < z → xs[k]?.any (fun v => decide (v ≠ 0#32)) = true)
    (R : Mem 64 → Prop) (m : Mem 64) (hm : (array (t := i32) base xs ⋆ R) m) (X : XPost) :
    Func.spec Γ arrayScanLoadLoop (base, 0#64, ()) m
      (fun (r, ()) m' => r = BitVec.ofNat 64 z ∧ m' = m) X := by
  dsimp only [Func.spec, Func.wp, arrayScanLoadLoop]
  refine wp_loop1 _ _
    (fun k (x : Tup Val [i64]) m' =>
      ∃ i, i ≤ z ∧ k = z - i ∧ x.1 = BitVec.ofNat 64 i ∧ m' = m) ?_ ?_
  · rintro J k ⟨iv, ⟨⟩⟩ m' hJ ⟨i, hiz, hk, hiv, rfl⟩
    dsimp only at hiv
    subst hiv
    dsimp only [wp, Op.wp, OpCode.wp, op2, vals, Arg.val, lift2, liftCmp,
      CmpOp.evalBits, CmpOp.evalBool, Ty.hasFloat, i64, i32, Closed]
    have hi_len : i < xs.length := Nat.lt_of_le_of_lt hiz hz
    have h2 : (2 : BitVec 64).toNat % 64 = 2 := by decide
    have hshift : BitVec.ofNat 64 i <<< ((2 : BitVec 64).toNat % 64) =
        BitVec.ofNat 64 (4 * i) := by
      rw [h2]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft]
      simp only [BitVec.toNat_ofNat]
      rw [Nat.shiftLeft_eq, show (2 ^ 2 : Nat) = 4 from rfl, Nat.mul_comm,
        Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    have hld : loadVal m' i32 (base + BitVec.ofNat 64 i <<< ((2 : BitVec 64).toNat % 64)) =
        some xs[i] := by
      rw [hshift]
      exact loadVal_array (t := i32) (by decide) hi_len hm
    refine ⟨xs[i], hld, ?_⟩
    by_cases hlt : i < z
    · have hne : xs[i] ≠ 0#32 := by
        have ha := hnz i hlt
        simp [List.getElem?_eq_getElem hi_len] at ha
        exact ha
      have hdec : decide (xs[i] ≠ 0#32) = true := decide_eq_true hne
      constructor
      · intro _
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hlt_k : z - (i + 1) < k := by omega
        refine hJ (z - (i + 1)) (BitVec.ofNat 64 i + 1, ()) m' hlt_k
          ⟨i + 1, hlt, rfl, ?_, rfl⟩
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add]
      · intro hf
        rw [show (0 : BitVec 32) = 0#32 from rfl, hdec] at hf
        cases hf
    · have hiz_eq : i = z := by omega
      subst hiz_eq
      have hdec : decide (xs[i] ≠ 0#32) = false := by simp [hxs]
      constructor
      · intro ht
        rw [show (0 : BitVec 32) = 0#32 from rfl, hdec] at ht
        cases ht
      · intro _
        exact ⟨rfl, rfl⟩
  · intro J hJ
    dsimp only [wp, vals, Arg.val, Closed]
    exact hJ z (0#64, ()) m ⟨0, Nat.zero_le z, rfl, rfl, rfl⟩

theorem arrayScanLoadLoop_rot_spec (Γ : Env) (base : BitVec 64) (xs : List (BitVec 32)) (z : Nat)
    (hz : z < xs.length) (hxs : xs[z] = 0#32)
    (hnz : ∀ k, k < z → xs[k]?.any (fun v => decide (v ≠ 0#32)) = true)
    (R : Mem 64 → Prop) (m : Mem 64) (hm : (array (t := i32) base xs ⋆ R) m) (X : XPost) :
    Func.spec Γ (Func.loopRotate arrayScanLoadLoop) (base, 0#64, ()) m
      (fun (r, ()) m' => r = BitVec.ofNat 64 z ∧ m' = m) X :=
  Func.loopRotate_spec arrayScanLoadLoop_wf defaultRotConfig
    (arrayScanLoadLoop_src_spec Γ base xs z hz hxs hnz R m hm X)

/-- BCP watch-header `i8` load loop (`dir = false`, `ExitMode.wrap`, `.call` in `contArm`). -/
def watchHdrLoadLoop : Func [i64, i64, i64] [i64] := fun _ _ (valsPtr, wstkPtr, n0, ()) =>
  loop1 (ts := [i64, i64])
    (fun loop (i, acc, ()) =>
      .let_ (op2 (.shl i64) (.var i) (.imm 2)) fun (off, ()) =>
      .let_ (op2 (.add i64) (.var wstkPtr) (.var off)) fun (wp, ()) =>
      .load i32 (.var wp) fun lit =>
      .let_ (op2 (.add i64) (.var valsPtr) (.var i)) fun (vp, ()) =>
      .load i8 (.var vp) fun v =>
      .let_ (op2 (.cmp .sle i8) (.var v) (.imm 0)) fun (isFalseOrZero, ()) =>
      .jnz (.var isFalseOrZero)
        (.let_ (op2 (.add i64) (.var acc) (.imm 1)) fun (e1, ()) =>
         .let_ (op2 (.add i64) (.var e1) (.imm 2)) fun (e2, ()) =>
         .let_ (op2 (.add i64) (.var e2) (.imm 3)) fun (e3, ()) =>
         .let_ (op2 (.add i64) (.var e3) (.var n0)) fun (e4, ()) =>
         .ret (.var e4, ()))
        (.call "watch_push" (as := [i32]) (bs := [i64]) (.var lit, ()) fun (delta, ()) =>
         .let_ (op2 (.add i64) (.var acc) (.var delta)) fun (acc', ()) =>
         .let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
         .jump loop (.var i', .var acc', ())))
    (fun loop => .jump loop (.imm 0, .imm 0, ()))

theorem watchHdrLoadLoop_plan_wrap :
    (match buildRotPlan (as := [i64, i64, i64]) defaultRotConfig (reifyFunc watchHdrLoadLoop) with
     | .groupRot false _ _ (.wrap _ _) _ _ _ => true
     | _ => false) = true := by
  t_kernel_rfl

theorem watchHdrLoadLoop_rot_checkTFlat :
    Func.checkTFlat (Func.loopRotate watchHdrLoadLoop) = true := by
  t_kernel_rfl

theorem watchHdrLoadLoop_rot_wf : (Func.loopRotate watchHdrLoadLoop).Wf :=
  Func.loopRotate_wf (by t_wf_reify)

theorem watchHdrLoadLoop_callsOk :
    let allowed : List SigEntry := [("watch_push", [i32], [i64])]
    let f := Func.loopRotate watchHdrLoadLoop
    (f (fun _ => Unit) (fun _ => Unit) (Tup.units [i64, i64, i64])).callsOk allowed [] := by
  refine Func.loopRotate_callsOk (by t_wf_reify) defaultRotConfig ?_
  simp [watchHdrLoadLoop, loop1, Expr.callsOk, Blocks.callsOk]

theorem watchHdrLoadLoop_flat_parity :
    OptFlatLoop.loopRotateFlat [i64, i64, i64] (reifyFunc watchHdrLoadLoop) =
      reifyFunc (Func.loopRotate watchHdrLoadLoop) := by
  t_kernel_rfl

/-! ## 2. Widened live-var counts (`maxContLiveVars = 16` vs old `4`) -/

/-- Partial tail-edge loop carrying `8` `i64` loop variables (`4 < 8 ≤ 16`).
Skipped under `maxContLiveVars := 4`, rotated under `defaultRotConfig`. -/
def widePartialLoop : Func [i64] [i64] := fun _ _ (n, ()) =>
  loop1 (ts := [i64, i64, i64, i64, i64, i64, i64, i64])
    (fun loop (i, acc, v2, v3, v4, v5, v6, v7, ()) =>
      .let_ (op2 (.ne i64) (.var i) (.imm 0)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.cmp .eq i64) (.var i) (.imm 1)) fun (isOne, ()) =>
         .jnz (.var isOne)
           (.jump loop (.imm 0, .var acc, .var v2, .var v3, .var v4, .var v5, .var v6, .var v7, ()))
           (.let_ (op2 (.add i64) (.var acc) (.var v2)) fun (acc', ()) =>
            .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
            .jump loop
              (.var i', .var acc', .var v2, .var v3, .var v4, .var v5, .var v6, .var v7, ())))
        (.let_ (op2 (.add i64) (.var acc) (.var v3)) fun (r1, ()) =>
         .let_ (op2 (.add i64) (.var r1) (.var v4)) fun (r2, ()) =>
         .let_ (op2 (.add i64) (.var r2) (.var v5)) fun (r3, ()) =>
         .let_ (op2 (.add i64) (.var r3) (.var v6)) fun (r4, ()) =>
         .let_ (op2 (.add i64) (.var r4) (.var v7)) fun (r5, ()) =>
         .ret (.var r5, ())))
    (fun loop =>
      .jump loop (.var n, .imm 0, .imm 1, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, ()))

theorem widePartialLoop_old4_noRot :
    (buildRotPlan (as := [i64]) { maxContLiveVars := 4 }
      (reifyFunc widePartialLoop)).hasRot = false := by
  t_kernel_rfl

theorem widePartialLoop_default_rot :
    (buildRotPlan (as := [i64]) defaultRotConfig
      (reifyFunc widePartialLoop)).hasRot = true := by
  t_kernel_rfl

theorem widePartialLoop_rot_checkTFlat :
    Func.checkTFlat (Func.loopRotate widePartialLoop) = true := by
  t_kernel_rfl

theorem widePartialLoop_flat_parity :
    OptFlatLoop.loopRotateFlat [i64] (reifyFunc widePartialLoop) =
      reifyFunc (Func.loopRotate widePartialLoop) := by
  t_kernel_rfl

theorem widePartialLoop_wf : widePartialLoop.Wf := by t_wf_reify

theorem widePartialLoop_src_spec (Γ : Env) (n : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ widePartialLoop (n, ()) m
      (fun (r, ()) m' => r = (if n == 0#64 then 0#64 else n - 1#64) ∧ m' = m) X := by
  dsimp only [Func.spec, Func.wp, widePartialLoop]
  refine wp_loop1 _ _
    (fun k (x : Tup Val [i64, i64, i64, i64, i64, i64, i64, i64]) m' =>
      x.1.toNat = k ∧ m' = m ∧ x.2.2.1 = 1#64 ∧
      x.2.2.2.1 = 0#64 ∧ x.2.2.2.2.1 = 0#64 ∧ x.2.2.2.2.2.1 = 0#64 ∧
      x.2.2.2.2.2.2.1 = 0#64 ∧ x.2.2.2.2.2.2.2.1 = 0#64 ∧
      x.2.1 + (if x.1 == 0#64 then 0#64 else x.1 - 1#64) =
        (if n == 0#64 then 0#64 else n - 1#64)) ?_ ?_
  · rintro J k ⟨i, acc, v2, v3, v4, v5, v6, v7, ⟨⟩⟩ m' hJ
      ⟨hk, rfl, hv2, hv3, hv4, hv5, hv6, hv7, hinv⟩
    dsimp only at hk hv2 hv3 hv4 hv5 hv6 hv7 hinv
    subst hv2 hv3 hv4 hv5 hv6 hv7
    dsimp only [wp, Op.wp, OpCode.wp, op2, vals, Arg.val, liftCmp, lift2, CmpOp.evalBits, i64,
      Ty.hasFloat, Closed]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hz : i = 0#64
    · subst hz
      simp at hinv ⊢
      exact hinv
    · refine ⟨fun _ => ?_, fun hf => False.elim (hz (Classical.not_not.mp (of_decide_eq_false hf)))⟩
      by_cases h1 : i = 1#64
      · refine ⟨fun _ => ?_, fun hf => False.elim (of_decide_eq_false hf h1)⟩
        have hi : i.toNat = 1 := by simp [h1]
        refine hJ 0 (0#64, acc, 1#64, 0#64, 0#64, 0#64, 0#64, 0#64, ()) m' (by omega)
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simpa [h1] using hinv⟩
      · refine ⟨fun ht => False.elim (h1 (of_decide_eq_true ht)), fun _ => ?_⟩
        have hi0 : i.toNat ≠ 0 := fun hz0 => hz (BitVec.eq_of_toNat_eq (by simpa using hz0))
        have hi1 : i.toNat ≠ 1 := fun h10 => h1 (BitVec.eq_of_toNat_eq (by simpa using h10))
        have hsub : (i - 1#64).toNat = i.toNat - 1 :=
          BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; exact Nat.pos_of_ne_zero hi0)
        have him1 : i - 1#64 ≠ 0#64 := fun h => by
          have ht := congrArg BitVec.toNat h
          rw [hsub] at ht
          simp only [BitVec.toNat_ofNat, Nat.zero_mod] at ht
          exact hi1 (Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp ht) (Nat.pos_of_ne_zero hi0))
        have hk_pos : 0 < k := by rw [← hk]; exact Nat.pos_of_ne_zero hi0
        refine hJ (k - 1) (i - 1#64, acc + 1#64, 1#64, 0#64, 0#64, 0#64, 0#64, 0#64, ()) m'
          (Nat.sub_lt hk_pos Nat.zero_lt_one)
          ⟨by rw [hsub, hk], rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
        have hib : (i == 0#64) = false := beq_false_of_ne hz
        have himb : ((i - 1#64) == 0#64) = false := beq_false_of_ne him1
        dsimp only
        rw [hib] at hinv
        rw [himb]
        simp only [Bool.false_eq_true, ↓reduceIte] at hinv ⊢
        calc acc + 1#64 + (i - 1#64 - 1#64)
            = acc + (i - 1#64 - 1#64 + 1#64) := by rw [BitVec.add_assoc, BitVec.add_comm 1#64]
          _ = acc + (i - 1#64) := by rw [BitVec.sub_add_cancel]
          _ = if n == 0#64 then 0#64 else n - 1#64 := hinv
  · intro J hJ
    simp only [wp, vals, Arg.val]
    exact hJ n.toNat (n, 0#64, 1#64, 0#64, 0#64, 0#64, 0#64, 0#64, ()) m
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp⟩

theorem widePartialLoop_rot_spec (Γ : Env) (n : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ (Func.loopRotate widePartialLoop) (n, ()) m
      (fun (r, ()) m' => r = (if n == 0#64 then 0#64 else n - 1#64) ∧ m' = m) X :=
  Func.loopRotate_spec widePartialLoop_wf defaultRotConfig (widePartialLoop_src_spec Γ n m X)

/-- Full loop whose `6`-op header produces `5` live temps (`4 < 5 ≤ 16`) consumed in `contArm`.
Skipped under `maxContLiveVars := 4`, rotated under `defaultRotConfig`. -/
def wideHdrLiveLoop : Func [i64] [i64] := fun _ _ (n, ()) =>
  loop1 (ts := [i64, i64])
    (fun loop (i, acc, ()) =>
      .let_ (op2 (.add i64) (.var i) (.imm 1)) fun (h1, ()) =>
      .let_ (op2 (.add i64) (.var i) (.imm 2)) fun (h2, ()) =>
      .let_ (op2 (.add i64) (.var i) (.imm 3)) fun (h3, ()) =>
      .let_ (op2 (.add i64) (.var i) (.imm 4)) fun (h4, ()) =>
      .let_ (op2 (.add i64) (.var i) (.imm 5)) fun (h5, ()) =>
      .let_ (op2 (.ne i64) (.var h5) (.imm 5)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.add i64) (.var h1) (.var h2)) fun (s1, ()) =>
         .let_ (op2 (.add i64) (.var h3) (.var h4)) fun (s2, ()) =>
         .let_ (op2 (.add i64) (.var s1) (.var s2)) fun (s3, ()) =>
         .let_ (op2 (.add i64) (.var s3) (.var h5)) fun (s4, ()) =>
         .let_ (op2 (.add i64) (.var acc) (.var s4)) fun (acc', ()) =>
         .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
         .jump loop (.var i', .var acc', ()))
        (.ret (.var acc, ())))
    (fun loop => .jump loop (.var n, .imm 0, ()))

theorem wideHdrLiveLoop_old4_noRot :
    (buildRotPlan (as := [i64]) { maxContLiveVars := 4 }
      (reifyFunc wideHdrLiveLoop)).hasRot = false := by
  t_kernel_rfl

theorem wideHdrLiveLoop_default_rot :
    (buildRotPlan (as := [i64]) defaultRotConfig
      (reifyFunc wideHdrLiveLoop)).hasRot = true := by
  t_kernel_rfl

theorem wideHdrLiveLoop_flat_parity :
    OptFlatLoop.loopRotateFlat [i64] (reifyFunc wideHdrLiveLoop) =
      reifyFunc (Func.loopRotate wideHdrLiveLoop) := by
  t_kernel_rfl

/-- Negative guard: partial loop with `17` live loop vars (`> maxContLiveVars = 16`) stays
unrotated under `defaultRotConfig`. -/
def tooWideLoop : Func [i64] [i64] := fun _ _ (n, ()) =>
  loop1 (ts := [i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64,
      i64])
    (fun loop (i, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, ()) =>
      .let_ (op2 (.ne i64) (.var i) (.imm 0)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.cmp .eq i64) (.var i) (.imm 1)) fun (isOne, ()) =>
         .jnz (.var isOne)
           (.jump loop (.imm 0, .var a1, .var a2, .var a3, .var a4, .var a5, .var a6, .var a7,
             .var a8, .var a9, .var a10, .var a11, .var a12, .var a13, .var a14, .var a15,
             .var a16, ()))
           (.let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
            .jump loop (.var i', .var a1, .var a2, .var a3, .var a4, .var a5, .var a6, .var a7,
              .var a8, .var a9, .var a10, .var a11, .var a12, .var a13, .var a14, .var a15,
              .var a16, ())))
        (.ret (.var a1, ())))
    (fun loop =>
      .jump loop (.var n, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0,
        .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, .imm 0, ()))

theorem tooWideLoop_noRot :
    (buildRotPlan (as := [i64]) defaultRotConfig (reifyFunc tooWideLoop)).hasRot = false := by
  t_kernel_rfl

/-! ## 3. Negative guards: header `.store`, `.call`, and trapping ops must NOT rotate -/

/-- Header `.store` must NOT rotate (`cand? := none`). -/
def hdrStoreLoop : Func [i64, i64] [i64] := fun _ _ (n, ptr, ()) =>
  loop1 (ts := [i64])
    (fun loop (i, ()) =>
      .store (.var i) (.var ptr)
        (.let_ (op2 (.ne i64) (.var i) (.imm 0)) fun (c, ()) =>
         .jnz (.var c)
           (.let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) => .jump loop (.var i', ()))
           (.ret (.var i, ()))))
    (fun loop => .jump loop (.var n, ()))

theorem hdrStoreLoop_noRot :
    (buildRotPlan (as := [i64, i64]) defaultRotConfig (reifyFunc hdrStoreLoop)).hasRot = false := by
  t_kernel_rfl

theorem hdrStoreLoop_flat_unchanged :
    OptFlatLoop.loopRotateFlat [i64, i64] (reifyFunc hdrStoreLoop) = reifyFunc hdrStoreLoop := by
  t_kernel_rfl

/-- Header `.call` must NOT rotate (`cand? := none`). -/
def hdrCallLoop : Func [i64] [i64] := fun _ _ (n, ()) =>
  loop1 (ts := [i64])
    (fun loop (i, ()) =>
      .call "probe" (as := [i64]) (bs := [i64]) (.var i, ()) fun (v, ()) =>
      .let_ (op2 (.ne i64) (.var v) (.imm 0)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) => .jump loop (.var i', ()))
        (.ret (.var i, ())))
    (fun loop => .jump loop (.var n, ()))

theorem hdrCallLoop_noRot :
    (buildRotPlan (as := [i64]) defaultRotConfig (reifyFunc hdrCallLoop)).hasRot = false := by
  t_kernel_rfl

theorem hdrCallLoop_flat_unchanged :
    OptFlatLoop.loopRotateFlat [i64] (reifyFunc hdrCallLoop) = reifyFunc hdrCallLoop := by
  t_kernel_rfl

/-- Header trapping `.udiv` must NOT rotate (`isSafeHdrOp` guard in planner & validator). -/
def hdrUdivLoop : Func [i64, i64] [i64] := fun _ _ (n, d, ()) =>
  loop1 (ts := [i64])
    (fun loop (i, ()) =>
      .let_ (op2 (.udiv 64) (.var i) (.var d)) fun (q, ()) =>
      .let_ (op2 (.ne i64) (.var q) (.imm 0)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) => .jump loop (.var i', ()))
        (.ret (.var i, ())))
    (fun loop => .jump loop (.var n, ()))

theorem hdrUdivLoop_noRot :
    (buildRotPlan (as := [i64, i64]) defaultRotConfig (reifyFunc hdrUdivLoop)).hasRot = false := by
  t_kernel_rfl

theorem hdrUdivLoop_flat_unchanged :
    OptFlatLoop.loopRotateFlat [i64, i64] (reifyFunc hdrUdivLoop) = reifyFunc hdrUdivLoop := by
  t_kernel_rfl

/-- Even an adversarial `RotPlan` targeting `hdrUdivLoop` is rejected by `validateHdr`. -/
def advUdivPlan : RotPlan :=
  .groupRot true [.let_ [i64], .let_ [.bool]] [[false], [false]] .inline .leaf .leaf .leaf

theorem hdrUdivLoop_adv_rejected :
    Func.loopRotateWithPlan advUdivPlan hdrUdivLoop = hdrUdivLoop := by
  t_kernel_rfl

/-- Header trapping `.sdiv` must NOT rotate. -/
def hdrSdivLoop : Func [i32, i32] [i32] := fun _ _ (n, d, ()) =>
  loop1 (ts := [i32])
    (fun loop (i, ()) =>
      .let_ (op2 (.sdiv 32) (.var i) (.var d)) fun (q, ()) =>
      .let_ (op2 (.ne i32) (.var q) (.imm 0)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.sub i32) (.var i) (.imm 1)) fun (i', ()) => .jump loop (.var i', ()))
        (.ret (.var i, ())))
    (fun loop => .jump loop (.var n, ()))

theorem hdrSdivLoop_noRot :
    (buildRotPlan (as := [i32, i32]) defaultRotConfig (reifyFunc hdrSdivLoop)).hasRot = false := by
  t_kernel_rfl

/-- Header trapping `.fptoui` must NOT rotate. -/
def hdrFptouiLoop : Func [.float .d] [i64] := fun _ _ (x, ()) =>
  loop1 (ts := [.float .d, i64])
    (fun loop (f, acc, ()) =>
      .let_ (op1 (.fptoui .d 64) (.var f)) fun (u, ()) =>
      .let_ (op2 (.ne i64) (.var u) (.imm 0)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.add i64) (.var acc) (.imm 1)) fun (acc', ()) =>
         .jump loop (.var f, .var acc', ()))
        (.ret (.var acc, ())))
    (fun loop => .jump loop (.var x, .imm 0, ()))

theorem hdrFptouiLoop_noRot :
    (buildRotPlan (as := [.float .d]) defaultRotConfig
      (reifyFunc hdrFptouiLoop)).hasRot = false := by
  t_kernel_rfl

/-! ## 4. Measured Kissat `FullM4` & `Kissat.Plain` rotation counts + native `TFlat` parity -/

private def fnToPreRot (lt : LegalTarget) (fn : Fn) :
    String × List Ty × TFlat (lt.legalSig fn.rs) :=
  let tf := reifyFunc fn.body
  let ef := earlyOptFlat ⟨fn.name, fn.as, fn.rs, tf⟩
  let as' := lt.legalSig ef.as
  let tf0 := legalFlat lt (as := ef.as) ef.body
  let tf1 := OptFlatValue.copyFlat as' (OptFlatMem.divConstFlat as'
    (OptFlatValue.canonFlat as' (OptFlatValue.foldFlat as' tf0)))
  let tf2 := OptFlatValue.foldFlat as' (OptFlatMem.assumeBitsFlat as'
    (OptFlatValue.gvnFlat as' (OptFlatMem.memLoadFlat as' tf1)))
  let tf3 := OptFlatValue.gvnFlat as' (addrRangeOptFlat as' (OptFlatValue.foldFlat as'
    (assumeElimFlat (OptFlatCfg.deadLoadElimFlat as' (simplifyGroupFastFlat as'
      (OptFlatCfg.ifOptFlat true as' tf2))))))
  let tfPreRot := OptFlatCfg.dcePFlat as' (licmFlat as' tf3)
  (fn.name, as', tfPreRot)

mutual
private def countGroupRots : RotPlan → Nat
  | .leaf => 0
  | .letP k | .loadP k | .storeP k | .callP k => countGroupRots k
  | .jnzP t e => countGroupRots t + countGroupRots e
  | .groupKeep bs k => countListRots bs + countGroupRots k
  | .groupRot _ _ _ _ c e k => 1 + countGroupRots c + countGroupRots e + countGroupRots k

private def countListRots : List RotPlan → Nat
  | [] => 0
  | p :: ps => countGroupRots p + countListRots ps
end

private def oldRotCfg : RotConfig := { allowLoadHdr := false, maxContLiveVars := 4 }

/-- Structural monotonicity + strict-gain invariant: across a function list, `defaultRotConfig`
(`allowLoadHdr := true`, `maxContLiveVars := 16`) never rotates fewer loops than `oldRotCfg` on
any function, baseline still rotates at least one loop, and the relaxed config strictly increases
both the number of rotated functions and total rotated loops. -/
private def rotMonotoneGain (lt : LegalTarget) (fns : List Fn) : Bool :=
  let (oldF, oldL, newF, newL, allMono) := fns.foldl (fun (oF, oL, nF, nL, ok) fn =>
    let (_, as', tf) := fnToPreRot lt fn
    let oc := countGroupRots (buildRotPlan (as := as') oldRotCfg tf)
    let nc := countGroupRots (buildRotPlan (as := as') defaultRotConfig tf)
    (oF + (if oc > 0 then 1 else 0), oL + oc,
     nF + (if nc > 0 then 1 else 0), nL + nc,
     ok && nc ≥ oc)) (0, 0, 0, 0, true)
  allMono && oldF > 0 && newF > oldF && newL > oldL && newF ≤ fns.length

#guard rotMonotoneGain Amd64.x64LegalTarget m4Fns
#guard rotMonotoneGain Amd64.x64LegalTarget (m4Module.optInline 40).fns
#guard rotMonotoneGain Amd64.x64LegalTarget plainFns

private def tupArgEq : {ts : List Ty} → Tup (Arg K) ts → Tup (Arg K) ts → Bool
  | [], (), () => true
  | _ :: _, (a, as), (b, bs) => decide (a = b) && tupArgEq as bs

private def opEq {ts : List Ty} (a b : Op K ts) : Bool :=
  match a, b with
  | { sig := sa, code := ca, args := aa }, { sig := sb, code := cb, args := ab } =>
    match listTyDecEq sa sb with
    | isTrue rfl => decide (ca = cb) && tupArgEq aa ab
    | isFalse _ => false

mutual
private def tflatEq {rs : List Ty} : TFlat rs → TFlat rs → Bool
  | .let_ (ts := ts1) op1 k1, .let_ (ts := ts2) op2 k2 =>
    match listTyDecEq ts1 ts2 with
    | isTrue rfl => opEq op1 op2 && tflatEq k1 k2
    | isFalse _ => false
  | .load t1 a1 k1, .load t2 a2 k2 =>
    match tyDecEq t1 t2 with
    | isTrue rfl => decide (a1 = a2) && tflatEq k1 k2
    | isFalse _ => false
  | .store (t := t1) v1 a1 k1, .store (t := t2) v2 a2 k2 =>
    match tyDecEq t1 t2 with
    | isTrue rfl => decide (v1 = v2) && decide (a1 = a2) && tflatEq k1 k2
    | isFalse _ => false
  | .call f1 (as := as1) bs1 args1 k1, .call f2 (as := as2) bs2 args2 k2 =>
    f1 == f2 &&
      match listTyDecEq as1 as2, listTyDecEq bs1 bs2 with
      | isTrue rfl, isTrue rfl => tupArgEq args1 args2 && tflatEq k1 k2
      | _, _ => false
  | .jnz c1 t1 e1, .jnz c2 t2 e2 =>
    decide (c1 = c2) && tflatEq t1 t2 && tflatEq e1 e2
  | .jump (ts := ts1) j1 a1, .jump (ts := ts2) j2 a2 =>
    j1 == j2 &&
      match listTyDecEq ts1 ts2 with
      | isTrue rfl => tupArgEq a1 a2
      | isFalse _ => false
  | .ret v1, .ret v2 => tupArgEq v1 v2
  | .exit (as := as1) f1 a1, .exit (as := as2) f2 a2 =>
    f1 == f2 &&
      match listTyDecEq as1 as2 with
      | isTrue rfl => tupArgEq a1 a2
      | isFalse _ => false
  | .hlt, .hlt => true
  | .group (sig := s1) b1 k1, .group (sig := s2) b2 k2 =>
    match (decEq s1 s2 : Decidable (s1 = s2)) with
    | isTrue rfl => tblocksEq b1 b2 && tflatEq k1 k2
    | isFalse _ => false
  | _, _ => false

private def tblocksEq {rs : List Ty} : {sig : List (List Ty)} →
    TBlocks rs sig → TBlocks rs sig → Bool
  | _, .nil, .nil => true
  | _, .cons b1 bs1, .cons b2 bs2 =>
    tflatEq b1 b2 && tblocksEq bs1 bs2
end

#guard
  let lt := Amd64.x64LegalTarget
  m4Fns.all fun fn =>
    let (_, as', tf) := fnToPreRot lt fn
    let tfRot := OptFlatLoop.loopRotateFlat as' tf defaultRotConfig
    tf.wfCheck (pushTypes as' []) [] &&
      tfRot.wfCheck (pushTypes as' []) [] &&
      tflatEq tfRot (reifyFunc (Func.loopRotate (denoteFunc (as := as') tf) defaultRotConfig))

#guard
  let lt := Amd64.x64LegalTarget
  plainFns.all fun fn =>
    let (_, as', tf) := fnToPreRot lt fn
    let tfRot := OptFlatLoop.loopRotateFlat as' tf defaultRotConfig
    tf.wfCheck (pushTypes as' []) [] &&
      tfRot.wfCheck (pushTypes as' []) [] &&
      tflatEq tfRot (reifyFunc (Func.loopRotate (denoteFunc (as := as') tf) defaultRotConfig))

/-! ## 5. Axiom audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms arrayScanLoadLoop_rot_wf
#print axioms arrayScanLoadLoop_rot_spec
#print axioms arrayScanLoadLoop_flat_denote_eq
#print axioms watchHdrLoadLoop_rot_wf
#print axioms watchHdrLoadLoop_callsOk
#print axioms widePartialLoop_rot_spec
#print axioms LeanQbe.T.OptFlatLoop.loopRotateFlat_eq
#print axioms LeanQbe.T.OptFlatLoop.denoteFunc_loopRotateFlat
#print axioms LeanQbe.T.OptFlatLoop.loopRotateFlatFn_toFn

end LeanQbeTest.T.LoopRotateLoadHdrTest
