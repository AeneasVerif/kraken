module

public import LeanQbe.T.IfOptLemmas
public import LeanQbe.T.LoopRotateLemmas
public import LeanQbe.T.SimplifyGroupPlanLemmas
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Opt
public import LeanQbe.T.OptLemmas
public import LeanQbe.T.Main
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.Examples.Kissat.Plain
meta import LeanQbe.T.IfOpt
meta import LeanQbe.T.LoopRotate
meta import LeanQbe.T.Opt
meta import LeanQbe.T.Main
meta import LeanQbe.T.Examples.LratBytes
meta import LeanQbe.T.Examples.Kissat.Plain

/-!
# Regression, Soundness & Axiom Tests: Nested `IfOpt` + Partial `LoopRotate`

Covers:
1. Nested 2-level & 3-level `IfOpt` / `IfOptBits` (`cmov`/branchless select chains) modeling
   `full_bva_hop1` and `full_prop_lit_raw` patterns, multi-arg + `.call` prefix `callsOk`,
   `Func.ifOptBits_spec` / `Func.ifOpt_wf`, and negative `.load` / `.udiv` / `> 4` op guards
   (explicitly documenting why `.load`-guarded diamonds such as `full_sort_tmp_sift` stay gated).
2. `LoopRotate` partial tail-edge / hot-loop rotation (`isPartialMasks`, `keepJumpPlan`,
   `Keep` + `Expand` 2-block rotation) for `dir = true`, `dir = false`, `.inline` & `.wrap`,
   exact `t_kernel_rfl` plan/output & `.checkTFlat`, `Func.loopRotate_{wf,spec,callsOk}`,
   `allowLoadHdr = false` & all-cond-back rejection, and adversarial `keepJumpPlan` rejection.
3. Real-corpus validation on `LratBytes` (`6` fns) and targeted `Kissat.Plain` (`plain_prop_lit`,
   `plain_min_lit`, `kissat_check_model`, `plain_parse_body`, `plain_clear_marks`).
4. `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.IfOptLoopRotB5Test

open LeanQbe.T
open LeanQbe.T.LoopRotate
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.Plain

def ifSimpBits {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.simplifyGroupPlan (Func.ifOptBits f)

theorem ifSimpBits_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (ifSimpBits f).Wf :=
  Func.simplifyGroupPlan_wf (Func.ifOptBits_wf hf)

theorem ifSimpBits_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (ifSimpBits f) xs m Q X :=
  Func.simplifyGroupPlan_spec (Func.ifOptBits_wf hf) (Func.ifOptBits_spec hf h)

/-! ## 1. Nested `IfOpt` / `IfOptBits` 2-level & 3-level diamonds -/

/-- `full_bva_hop1`-style nested 2-level diamond:
`if (ol != sl) { if ((ol >> 1) == dst) { ol ^^^ 1 } else { ol } } else { sl }`. -/
def bvaHop1Diamond : Func [i32, i32, i32] [i32] := fun _ _ (ol, sl, dst, ()) =>
  .group (sig := [[i32]])
    (fun _ => .cons (fun (r, ()) => .ret (.var r, ())) .nil)
    (fun (J, ()) =>
      .let_ (op2 (.cmp .ne i32) (.var ol) (.var sl)) fun (c1, ()) =>
      .jnz (.var c1)
        (.let_ (op2 (.lshr i32) (.var ol) (.imm 1)) fun (v, ()) =>
         .let_ (op2 (.cmp .eq i32) (.var v) (.var dst)) fun (c2, ()) =>
         .jnz (.var c2)
           (.let_ (op2 (.xor i32) (.var ol) (.imm 1)) fun (flp, ()) => .jump J (.var flp, ()))
           (.jump J (.var ol, ())))
        (.jump J (.var sl, ())))

theorem bvaHop1Diamond_out : ifSimpBits bvaHop1Diamond = fun _ _ (ol, sl, dst, ()) =>
    .let_ (op2 (.lshr i32) (.var ol) (.imm 1)) fun (v, ()) =>
    .let_ (op2 (.cmp .eq i32) (.var v) (.var dst)) fun (c2, ()) =>
    .let_ (op2 (.xor i32) (.var ol) (.imm 1)) fun (flp, ()) =>
    .let_ (op3 (.select i32) (.var c2) (.var flp) (.var ol)) fun (s1, ()) =>
    .let_ (op2 (.cmp .ne i32) (.var ol) (.var sl)) fun (c1, ()) =>
    .let_ (op3 (.select i32) (.var c1) (.var s1) (.var sl)) fun (s2, ()) =>
    .ret (.var s2, ()) := by
  t_kernel_rfl

theorem bvaHop1Diamond_wf : bvaHop1Diamond.Wf := by t_wf_reify
theorem bvaHop1Diamond_opt_wf : (ifSimpBits bvaHop1Diamond).Wf := ifSimpBits_wf bvaHop1Diamond_wf
theorem bvaHop1Diamond_checkTFlat : (ifSimpBits bvaHop1Diamond).checkTFlat = true := by
  t_kernel_rfl

theorem bvaHop1Diamond_spec (Γ : Env) (ol sl dst : BitVec 32) (m : Mem 64) :
    Func.spec Γ (ifSimpBits bvaHop1Diamond) (ol, sl, dst, ()) m
      (fun (r, ()) m' =>
        r = (if ol != sl then (if (ol >>> 1#32) == dst then ol ^^^ 1#32 else ol) else sl) ∧
          m' = m)
      (fun _ _ _ _ => False) := by
  apply ifSimpBits_spec bvaHop1Diamond_wf
  dsimp only [Func.spec, Func.wp, bvaHop1Diamond, wp, Op.wp, OpCode.wp, op2, vals, Arg.val,
    liftCmp, lift2, CmpOp.evalBits, i32, Closed]
  intro ⟨J, ⟨⟩⟩ hJ
  refine ⟨fun hc1 => ?_, fun hc1 => ?_⟩
  · have h1 : ol ≠ sl := of_decide_eq_true hc1
    refine ⟨fun hc2 => ?_, fun hc2 => ?_⟩
    · have h2 : ol >>> 1 = dst := of_decide_eq_true hc2
      exact hJ.1 ((ol ^^^ 1#32), ()) m ⟨by simp [h1, h2], rfl⟩
    · have h2 : ol >>> 1 ≠ dst := of_decide_eq_false hc2
      exact hJ.1 (ol, ()) m ⟨by simp [h1, h2], rfl⟩
  · have h1 : ol = sl := Classical.not_not.mp (of_decide_eq_false hc1)
    exact hJ.1 (sl, ()) m ⟨by simp [h1], rfl⟩

/-- `full_prop_lit_raw`-style 2-level unassigned clamp:
`if ((fl &&& 1) != 0) { if (unass >u 0) { unass - 1 } else { 0 } } else { unass }`. -/
def propLitRawClampDiamond : Func [i32, i32] [i32] := fun _ _ (fl, unass, ()) =>
  .group (sig := [[i32]])
    (fun _ => .cons (fun (r, ()) => .ret (.var r, ())) .nil)
    (fun (J, ()) =>
      .let_ (op2 (.and i32) (.var fl) (.imm 1)) fun (b, ()) =>
      .let_ (op2 (.cmp .ne i32) (.var b) (.imm 0)) fun (c1, ()) =>
      .jnz (.var c1)
        (.let_ (op2 (.cmp .ugt i32) (.var unass) (.imm 0)) fun (c2, ()) =>
         .jnz (.var c2)
           (.let_ (op2 (.sub i32) (.var unass) (.imm 1)) fun (dec, ()) =>
            .jump J (.var dec, ()))
           (.jump J (.imm 0, ())))
        (.jump J (.var unass, ())))

theorem propLitRawClamp_out : ifSimpBits propLitRawClampDiamond = fun _ _ (fl, unass, ()) =>
    .let_ (op2 (.and i32) (.var fl) (.imm 1)) fun (b, ()) =>
    .let_ (op2 (.cmp .ugt i32) (.var unass) (.imm 0)) fun (c2, ()) =>
    .let_ (op2 (.sub i32) (.var unass) (.imm 1)) fun (dec, ()) =>
    .let_ (op3 (.select i32) (.var c2) (.var dec) (.imm 0)) fun (s1, ()) =>
    .let_ (op2 (.cmp .ne i32) (.var b) (.imm 0)) fun (c1, ()) =>
    .let_ (op3 (.select i32) (.var c1) (.var s1) (.var unass)) fun (s2, ()) =>
    .ret (.var s2, ()) := by
  t_kernel_rfl

theorem propLitRawClamp_wf : propLitRawClampDiamond.Wf := by t_wf_reify

theorem propLitRawClamp_spec (Γ : Env) (fl unass : BitVec 32) (m : Mem 64) :
    Func.spec Γ (ifSimpBits propLitRawClampDiamond) (fl, unass, ()) m
      (fun (r, ()) m' =>
        r = (if (fl &&& 1#32) != 0#32 then (if 0#32 < unass then unass - 1#32 else 0#32)
             else unass) ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply ifSimpBits_spec propLitRawClamp_wf
  dsimp only [Func.spec, Func.wp, propLitRawClampDiamond, wp, Op.wp, OpCode.wp, op2, vals, Arg.val,
    liftCmp, lift2, CmpOp.evalBits, i32, Closed]
  intro ⟨J, ⟨⟩⟩ hJ
  refine ⟨fun hc1 => ?_, fun hc1 => ?_⟩
  · have h1 : fl &&& 1#32 ≠ 0#32 := of_decide_eq_true hc1
    refine ⟨fun hc2 => ?_, fun hc2 => ?_⟩
    · have h2 : 0#32 < unass := BitVec.ult_iff_lt.mp hc2
      exact hJ.1 (unass - 1#32, ()) m ⟨by simp [h1, h2], rfl⟩
    · have h2 : ¬(0#32 < unass) := fun h =>
        Bool.false_ne_true (hc2.symm.trans (BitVec.ult_iff_lt.mpr h))
      exact hJ.1 (0#32, ()) m ⟨by simp [h1, h2], rfl⟩
  · have h1 : fl &&& 1#32 = 0#32 := Classical.not_not.mp (of_decide_eq_false hc1)
    exact hJ.1 (unass, ()) m ⟨by simp [h1], rfl⟩

/-- 3-level nested diamond (`jnzFuel = 2`) with `.call` prefix + 2-arg `[i64, i64]` join. -/
def threeLevelCallDiamond : Func [.bool, .bool, .bool, i64, i64] [i64] :=
  fun _ _ (c0, c1, c2, x, y, ()) =>
  .group (sig := [[i64, i64]])
    (fun _ => .cons (fun (a, b, ()) =>
      .let_ (op2 (.add i64) (.var a) (.var b)) fun (s, ()) => .ret (.var s, ())) .nil)
    (fun (J, ()) =>
      .call "tick" (as := [i64]) (bs := [i64]) (.var x, ()) fun (t, ()) =>
      .jnz (.var c0)
        (.jnz (.var c1)
          (.jnz (.var c2)
            (.jump J (.var t, .var y, ()))
            (.let_ (op2 (.add i64) (.var t) (.imm 1)) fun (t1, ()) =>
             .jump J (.var t1, .var y, ())))
          (.jump J (.var x, .imm 7, ())))
        (.jump J (.imm 0, .var y, ())))

theorem threeLevelCall_checkTFlat :
    (Func.ifOpt threeLevelCallDiamond).checkTFlat = true := by
  t_kernel_rfl

theorem threeLevelCall_ifOpt_noJnz :
    (Func.simplifyGroupPlan (Func.ifOpt threeLevelCallDiamond)) =
      fun _ _ (c0, c1, c2, x, y, ()) =>
        .call "tick" (as := [i64]) (bs := [i64]) (.var x, ()) fun (t, ()) =>
        .let_ (op2 (.add i64) (.var t) (.imm 1)) fun (t1, ()) =>
        .let_ (op3 (.select i64) (.var c2) (.var t) (.var t1)) fun (s2, ()) =>
        .let_ (op3 (.select i64) (.var c1) (.var s2) (.var x)) fun (s1a, ()) =>
        .let_ (op3 (.select i64) (.var c1) (.var y) (.imm 7)) fun (s1b, ()) =>
        .let_ (op3 (.select i64) (.var c0) (.var s1a) (.imm 0)) fun (s0a, ()) =>
        .let_ (op3 (.select i64) (.var c0) (.var s1b) (.var y)) fun (s0b, ()) =>
        .let_ (op2 (.add i64) (.var s0a) (.var s0b)) fun (r, ()) =>
        .ret (.var r, ()) := by
  t_kernel_rfl

theorem threeLevelCall_callsOk :
    ((Func.ifOpt threeLevelCallDiamond) (fun _ => Unit) (fun _ => Unit)
      (Tup.units [.bool, .bool, .bool, i64, i64])).callsOk [⟨"tick", [i64], [i64]⟩] [] :=
  Func.ifOpt_callsOk (by t_wf_reify) (by
    simp [threeLevelCallDiamond, Expr.callsOk, Blocks.callsOk])

/-- Negative guard: nested inner `.load` (as in `full_sort_tmp_sift`) must not be hoisted. -/
def nestedLoadGuardDiamond : Func [.bool, .bool, i64, i64] [i64] :=
  fun _ _ (c1, c2, p, x, ()) =>
  .group (sig := [[i64]])
    (fun _ => .cons (fun (r, ()) => .ret (.var r, ())) .nil)
    (fun (J, ()) =>
      .jnz (.var c1)
        (.jnz (.var c2)
          (.load i64 (.var p) fun v => .jump J (.var v, ()))
          (.jump J (.var x, ())))
        (.jump J (.imm 0, ())))

theorem nestedLoadGuard_unchanged :
    Func.ifOpt nestedLoadGuardDiamond = nestedLoadGuardDiamond := by
  t_kernel_rfl

/-- Negative guard: nested partial `.udiv` must not be hoisted. -/
def nestedUdivDiamond : Func [.bool, .bool, i64, i64] [i64] :=
  fun _ _ (c1, c2, x, d, ()) =>
  .group (sig := [[i64]])
    (fun _ => .cons (fun (r, ()) => .ret (.var r, ())) .nil)
    (fun (J, ()) =>
      .jnz (.var c1)
        (.jnz (.var c2)
          (.let_ (op2 (.udiv 64) (.var x) (.var d)) fun (q, ()) => .jump J (.var q, ()))
          (.jump J (.var x, ())))
        (.jump J (.imm 0, ())))

theorem nestedUdiv_unchanged : Func.ifOpt nestedUdivDiamond = nestedUdivDiamond := by t_kernel_rfl

/-- Negative guard: >4 total safe `.let_` ops inside nested arm must not be hoisted. -/
def nestedOver4OpsDiamond : Func [.bool, .bool, i64] [i64] := fun _ _ (c1, c2, x, ()) =>
  .group (sig := [[i64]])
    (fun _ => .cons (fun (r, ()) => .ret (.var r, ())) .nil)
    (fun (J, ()) =>
      .jnz (.var c1)
        (.jnz (.var c2)
          (.let_ (op2 (.add i64) (.var x) (.imm 1)) fun (x1, ()) =>
           .let_ (op2 (.add i64) (.var x1) (.imm 2)) fun (x2, ()) =>
           .let_ (op2 (.add i64) (.var x2) (.imm 3)) fun (x3, ()) =>
           .let_ (op2 (.add i64) (.var x3) (.imm 4)) fun (x4, ()) =>
           .let_ (op2 (.add i64) (.var x4) (.imm 5)) fun (x5, ()) =>
           .jump J (.var x5, ()))
          (.jump J (.var x, ())))
        (.jump J (.imm 0, ())))

theorem nestedOver4Ops_unchanged :
    Func.ifOpt nestedOver4OpsDiamond = nestedOver4OpsDiamond := by
  t_kernel_rfl

/-! ## 2. `LoopRotate` partial tail-edge mode (`Keep` + `Expand`, `.inline` & `.wrap`) -/

/-- Loop with 1 conditional early-continue back-edge (`Keep`) and 1 tail back-edge (`Expand`).
Since `backJumps = 2` and `condBack = 1` (`2 * condBack ≥ backJumps`), `requireTailMajority` blocks
full rotation under `defaultRotConfig`, so partial tail-edge mode rotates the straight-line tail
edge while directing the conditional early-continue edge back to `hdrBlock` (`Keep`). -/
def partialTailLoop : Func [i64] [i64] := fun _ _ (n, ()) =>
  loop1 (ts := [i64, i64])
    (fun loop (i, acc, ()) =>
      .let_ (op2 (.cmp .ne i64) (.var i) (.imm 0)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.cmp .eq i64) (.var i) (.imm 1)) fun (isOne, ()) =>
         .jnz (.var isOne)
           (.jump loop (.imm 0, .var acc, ()))
           (.let_ (op2 (.add i64) (.var acc) (.imm 1)) fun (acc', ()) =>
            .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
            .jump loop (.var i', .var acc', ())))
        (.ret (.var acc, ())))
    (fun loop => .jump loop (.var n, .imm 0, ()))

mutual
def isPartialPlan : RotPlan → Bool
  | .leaf => false
  | .letP k | .loadP k | .storeP k | .callP k => isPartialPlan k
  | .jnzP t e => isPartialPlan t || isPartialPlan e
  | .groupKeep bs k => listIsPartialPlan bs || isPartialPlan k
  | .groupRot _ hdr contMasks _ _ _ _ => isPartialMasks hdr contMasks

def listIsPartialPlan : List RotPlan → Bool
  | [] => false
  | p :: ps => isPartialPlan p || listIsPartialPlan ps
end

theorem partialTailLoop_is_partial :
    isPartialPlan
      (buildRotPlan (as := [i64]) defaultRotConfig (reifyFunc partialTailLoop)) = true := by
  t_kernel_rfl

theorem partialTailLoop_rot_out :
    Func.loopRotate partialTailLoop = fun _ _ (n, ()) =>
    .group (sig := [[i64, i64], [i64, i64]])
      (fun (rotLbl, hdrLbl, ()) =>
        .cons (fun (i, acc, ()) =>
          .let_ (op2 (.cmp .eq i64) (.var i) (.imm 1)) fun (isOne, ()) =>
          .jnz (.var isOne)
            (.jump hdrLbl (.imm 0, .var acc, ()))
            (.let_ (op2 (.add i64) (.var acc) (.imm 1)) fun (acc', ()) =>
             .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
             .let_ (op2 (.cmp .ne i64) (.var i') (.imm 0)) fun (c1, ()) =>
             .jnz (.var c1)
               (.jump rotLbl (.var i', .var acc', ()))
               (.ret (.var acc', ()))))
        (.cons (fun (i, acc, ()) =>
          .let_ (op2 (.cmp .ne i64) (.var i) (.imm 0)) fun (c0, ()) =>
          .jnz (.var c0) (.jump rotLbl (.var i, .var acc, ())) (.ret (.var acc, ()))) .nil))
      (fun (rotLbl, _, ()) =>
        .let_ (op2 (.cmp .ne i64) (.var n) (.imm 0)) fun (ce, ()) =>
        .jnz (.var ce) (.jump rotLbl (.var n, .imm 0, ())) (.ret (.imm 0, ()))) := by
  t_kernel_rfl

theorem partialTailLoop_wf : partialTailLoop.Wf := by t_wf_reify

theorem partialTailLoop_rot_wf : (Func.loopRotate partialTailLoop).Wf :=
  Func.loopRotate_wf partialTailLoop_wf

theorem partialTailLoop_rot_checkTFlat :
    Func.checkTFlat (Func.loopRotate partialTailLoop) = true := by
  t_kernel_rfl

theorem partialTailLoop_spec (Γ : Env) (n : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ partialTailLoop (n, ()) m
      (fun (r, ()) m' => r = (if n == 0#64 then 0#64 else n - 1#64) ∧ m' = m)
      X := by
  dsimp only [Func.spec, Func.wp, partialTailLoop]
  refine wp_loop1 _ _
    (fun k (x : Tup Val [i64, i64]) m' =>
      x.1.toNat = k ∧ m' = m ∧
      x.2.1 + (if x.1 == 0#64 then 0#64 else x.1 - 1#64) =
        (if n == 0#64 then 0#64 else n - 1#64)) ?_ ?_
  · rintro J k ⟨i, acc, ⟨⟩⟩ m' hJ ⟨hk, rfl, hinv⟩
    dsimp only at hk hinv
    dsimp only [wp, Op.wp, OpCode.wp, op2, vals, Arg.val, liftCmp, lift2, CmpOp.evalBits, i64,
      Ty.hasFloat]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hz : i = 0#64
    · subst hz
      simp at hinv ⊢
      exact hinv
    · refine ⟨fun _ => ?_, fun hf => False.elim (hz (Classical.not_not.mp (of_decide_eq_false hf)))⟩
      by_cases h1 : i = 1#64
      · refine ⟨fun _ => ?_, fun hf => False.elim (of_decide_eq_false hf h1)⟩
        refine hJ 0 (0#64, acc, ()) m' (by
          have hi : i.toNat = 1 := by simp [h1]
          omega) ⟨rfl, rfl, ?_⟩
        simpa [h1] using hinv
      · refine ⟨fun ht => False.elim (h1 (of_decide_eq_true ht)), fun _ => ?_⟩
        have hi0 : i.toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq (by simpa using h))
        have hi1 : i.toNat ≠ 1 := fun h => h1 (BitVec.eq_of_toNat_eq (by simpa using h))
        have hsub : (i - 1#64).toNat = i.toNat - 1 :=
          BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)
        refine hJ (k - 1) (i - 1#64, acc + 1#64, ()) m' (by omega)
          ⟨by rw [hsub, hk], rfl, ?_⟩
        have him1 : i - 1#64 ≠ 0#64 := fun h => by
          have ht := congrArg BitVec.toNat h; rw [hsub] at ht; simp at ht; omega
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
    exact hJ n.toNat (n, 0#64, ()) m ⟨rfl, rfl, by simp⟩

theorem partialTailLoop_rot_spec (Γ : Env) (n : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ (Func.loopRotate partialTailLoop) (n, ()) m
      (fun (r, ()) m' => r = (if n == 0#64 then 0#64 else n - 1#64) ∧ m' = m)
      X :=
  Func.loopRotate_spec partialTailLoop_wf defaultRotConfig (partialTailLoop_spec Γ n m X)

/-- Partial rotation with `dir = false`, `ExitMode.wrap` (`exitInfo.size > 4`), and `.call`
preserving `callsOk`. -/
def partialWrapCallLoop : Func [i64, i64] [i64] := fun _ _ (n, acc0, ()) =>
  loop1 (ts := [i64, i64])
    (fun loop (i, acc, ()) =>
      .let_ (op2 (.cmp .eq i64) (.var i) (.imm 0)) fun (done, ()) =>
      .jnz (.var done)
        (.let_ (op2 (.add i64) (.var acc) (.imm 1)) fun (x1, ()) =>
         .let_ (op2 (.add i64) (.var x1) (.imm 2)) fun (x2, ()) =>
         .let_ (op2 (.add i64) (.var x2) (.imm 3)) fun (x3, ()) =>
         .let_ (op2 (.add i64) (.var x3) (.imm 4)) fun (x4, ()) =>
         .let_ (op2 (.add i64) (.var x4) (.imm 5)) fun (x5, ()) =>
         .ret (.var x5, ()))
        (.call "step" (as := [i64]) (bs := [i64]) (.var i, ()) fun (s, ()) =>
         .let_ (op2 (.cmp .eq i64) (.var s) (.imm 0)) fun (skip, ()) =>
         .jnz (.var skip)
           (.jump loop (.imm 0, .var acc, ()))
           (.let_ (op2 (.add i64) (.var acc) (.var s)) fun (acc', ()) =>
            .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
            .jump loop (.var i', .var acc', ()))))
    (fun loop => .jump loop (.var n, .var acc0, ()))

mutual
def hasWrapPartialPlan : RotPlan → Bool
  | .leaf => false
  | .letP k | .loadP k | .storeP k | .callP k => hasWrapPartialPlan k
  | .jnzP t e => hasWrapPartialPlan t || hasWrapPartialPlan e
  | .groupKeep bs k => listHasWrapPartialPlan bs || hasWrapPartialPlan k
  | .groupRot _ hdr contMasks (.wrap _ _) _ _ _ => isPartialMasks hdr contMasks
  | .groupRot _ _ _ .inline c e k =>
    hasWrapPartialPlan c || hasWrapPartialPlan e || hasWrapPartialPlan k

def listHasWrapPartialPlan : List RotPlan → Bool
  | [] => false
  | p :: ps => hasWrapPartialPlan p || listHasWrapPartialPlan ps
end

theorem partialWrapCall_plan_wrap :
    hasWrapPartialPlan (buildRotPlan (as := [i64, i64]) defaultRotConfig
      (reifyFunc partialWrapCallLoop)) = true := by
  t_kernel_rfl

theorem partialWrapCall_rot_checkTFlat :
    Func.checkTFlat (Func.loopRotate partialWrapCallLoop) = true := by
  t_kernel_rfl

theorem partialWrapCall_rot_wf : (Func.loopRotate partialWrapCallLoop).Wf :=
  Func.loopRotate_wf (by t_wf_reify)

theorem pWrap_rot_callsOk :
    ((Func.loopRotate partialWrapCallLoop) (fun _ => Unit) (fun _ => Unit)
      (Tup.units [i64, i64])).callsOk [⟨"step", [i64], [i64]⟩] [] :=
  Func.loopRotate_callsOk (by t_wf_reify) defaultRotConfig (by
    simp [partialWrapCallLoop, loop1, Expr.callsOk, Blocks.callsOk])

/-- Negative guard: load-header loops are skipped when `allowLoadHdr := false`, and rotated under
`defaultRotConfig` (`allowLoadHdr = true`). -/
def loadHdrBlockedLoop : Func [i64] [i64] := fun _ _ (p, ()) =>
  loop1 (ts := [i64])
    (fun loop (q, ()) =>
      .load i64 (.var q) fun v =>
      .let_ (op2 (.cmp .ne i64) (.var v) (.imm 0)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.add i64) (.var q) (.imm 8)) fun (q', ()) => .jump loop (.var q', ()))
        (.ret (.var q, ())))
    (fun loop => .jump loop (.var p, ()))

theorem loadHdrBlocked_disabled_noRot :
    (buildRotPlan (as := [i64]) { allowLoadHdr := false }
      (reifyFunc loadHdrBlockedLoop)).hasRot = false := by
  t_kernel_rfl

theorem loadHdrBlocked_default_rot :
    (buildRotPlan (as := [i64]) defaultRotConfig
      (reifyFunc loadHdrBlockedLoop)).hasRot = true := by
  t_kernel_rfl

/-- Negative guard: loop whose back-edges are all direct conditional jumps (`condBack == backJumps`,
so `expCount = 0`) must not trigger partial rotation. -/
def allCondNoPartialLoop : Func [i64, i64] [i64] := fun _ _ (n, acc0, ()) =>
  loop1 (ts := [i64, i64])
    (fun loop (i, acc, ()) =>
      .let_ (op2 (.cmp .ne i64) (.var i) (.imm 0)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.cmp .eq i64) (.var i) (.imm 1)) fun (c1, ()) =>
         .jnz (.var c1)
           (.jump loop (.imm 0, .var acc, ()))
           (.jump loop (.imm 0, .imm 7, ())))
        (.ret (.var acc, ())))
    (fun loop => .jump loop (.var n, .var acc0, ()))

theorem allCondNoPartial_default_noRot :
    (buildRotPlan (as := [i64, i64]) defaultRotConfig
      (reifyFunc allCondNoPartialLoop)).hasRot = false := by
  t_kernel_rfl

/-- Adversarial safety check: placing `keepJumpPlan` inside a top-level `.jnz` (`allowHdr = false`)
is rejected by `validateRotPlan` and `Func.loopRotateWithPlan` returns `f` unchanged. -/
def topJnzFn : Func [.bool, i64] [i64] := fun _ _ (c, x, ()) =>
  .jnz (.var c) (.ret (.var x, ())) (.ret (.imm 0, ()))

theorem advKeepOutsideCont_noop :
    Func.loopRotateWithPlan keepJumpPlan topJnzFn = topJnzFn := by
  t_kernel_rfl

/-! ## 3. Real-corpus validation (`LratBytes` + `Kissat.Plain` partial & nested) -/

#guard lratBytesFns.length == 6
#guard lratBytesFns.all fun fn =>
  (Func.loopRotate (Func.ifOptBits (Func.earlyCore fn.body))).checkTFlat

def targetPlainNames : List String :=
  ["plain_prop_lit", "plain_min_lit", "kissat_check_model", "plain_parse_body",
    "plain_clear_marks"]

def plainMidFns : List Fn :=
  ((plainModule.optInline 40).fns.filter fun fn =>
      targetPlainNames.contains fn.name).map fun f =>
    let lf := (f.earlyOpt).legal LegalTarget.x64AVX512
    let body := Func.lateCfg (Func.lateCore lf.body)
    ⟨lf.name, lf.as, lf.rs, let tf := reifyFunc body; denoteFunc tf⟩

#guard plainMidFns.length == 5
#guard plainMidFns.all fun fn =>
  let rf := fn.loopRotate LoopRotate.defaultRotConfig
  rf.body.checkTFlat
#guard (plainMidFns.filter fun fn =>
    fn.name == "plain_prop_lit" || fn.name == "plain_min_lit").all fun fn =>
  let plan := LoopRotate.buildRotPlan (as := fn.as) LoopRotate.defaultRotConfig
    (reifyFunc fn.body)
  isPartialPlan plan
#guard (plainMidFns.filter fun fn =>
    fn.name == "kissat_check_model" || fn.name == "plain_parse_body" ||
      fn.name == "plain_clear_marks").all fun fn =>
  let oldPlan := LoopRotate.buildRotPlan (as := fn.as)
    { allowLoadHdr := false, maxContLiveVars := 4 } (reifyFunc fn.body)
  let newPlan := LoopRotate.buildRotPlan (as := fn.as) LoopRotate.defaultRotConfig
    (reifyFunc fn.body)
  !oldPlan.hasRot && newPlan.hasRot

/-! ## 4. Axiom audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms LeanQbe.T.Func.ifOpt_wf
#print axioms LeanQbe.T.Func.ifOpt_spec
#print axioms LeanQbe.T.Func.ifOpt_callsOk
#print axioms LeanQbe.T.Func.ifOptBits_wf
#print axioms LeanQbe.T.Func.ifOptBits_spec
#print axioms LeanQbe.T.Func.ifOptBits_callsOk
#print axioms LeanQbe.T.Func.loopRotate_wf
#print axioms LeanQbe.T.Func.loopRotate_spec
#print axioms LeanQbe.T.Func.loopRotate_callsOk
#print axioms LeanQbeTest.T.IfOptLoopRotB5Test.bvaHop1Diamond_spec
#print axioms LeanQbeTest.T.IfOptLoopRotB5Test.propLitRawClamp_spec
#print axioms LeanQbeTest.T.IfOptLoopRotB5Test.threeLevelCall_callsOk
#print axioms LeanQbeTest.T.IfOptLoopRotB5Test.partialTailLoop_rot_spec
#print axioms LeanQbeTest.T.IfOptLoopRotB5Test.pWrap_rot_callsOk

end LeanQbeTest.T.IfOptLoopRotB5Test
