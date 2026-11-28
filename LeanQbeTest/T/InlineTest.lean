module

import LeanQbe.T.InlineLemmas
import LeanQbe.T.FlatLemmas
import LeanQbe.T.OptLemmas
import LeanQbe.T.MainInline

/-!
# Tests of `LeanQbe.T.Inline`

Covers:
1. Single-return small callee inlining (`singleRetMod`), `ModuleOk`, and `Func.checkTFlat`.
2. Multi-block callee with internal `.jnz`, `.group`, and multiple `.ret` sites (`multiBlockMod`),
   called with both `.var` and `.imm` operands.
3. Nested callee-to-callee inlining (`leafF` -> `midG` -> `topH` in `nestedMod`), verifying that
   `midG` inlines `leafF` and `topH` receives the already-inlined `midG` body with zero `.call`s.
4. Size-threshold bypass (`thresholdMod` with explicit `maxSize := 5` and `defaultThreshMod` with
   default `40`), plus `externs`, `exits`, `Module.inline_sigs`, `Module.inline_namesNodup`, and
   `Module.inline_checkAcyclic`.
5. Concrete `ModuleOk` preservation (`Module.inline_ok`) and `#print axioms` checks.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.InlineTest

open LeanQbe.T

/-- Helper to view a `Fn`'s body at its expected signature `(as, rs)` for kernel `rfl` checks. -/
def fnBodyAs (as rs : List Ty) (fn : Fn) : Func as rs :=
  match listTyDecEq fn.as as, listTyDecEq fn.rs rs with
  | isTrue ha, isTrue hr => ha ▸ hr ▸ fn.body
  | _, _ => fun _ _ _ => .hlt

def dummyFn : Fn := ⟨"", [], [], fun _ _ _ => .hlt⟩

/-! ## 1. Single-return small callee -/

def fnAdd1 : Fn := ⟨"add1", [i64], [i64], fun _ _ (x, ()) =>
  .let_ (op2 (.add i64) (.var x) (.imm 1)) fun (y, ()) =>
  .ret (.var y, ())⟩

def fnAdd1Caller : Fn := ⟨"caller", [i64], [i64], fun _ _ (a, ()) =>
  .call "add1" (as := [i64]) (bs := [i64]) (.var a, ()) fun (r, ()) =>
  .let_ (op2 (.mul i64) (.var r) (.imm 2)) fun (z, ()) =>
  .ret (.var z, ())⟩

def singleRetMod : Module where
  fns := [fnAdd1, fnAdd1Caller]

theorem singleRet_checkAcyclic : singleRetMod.checkAcyclic = true := by rfl

theorem singleRet_wf : ∀ fn ∈ singleRetMod.fns, fn.Wf := by
  intro fn hfn
  simp only [singleRetMod, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl <;> (unfold Fn.Wf; t_wf_reify)

def singleRetΓ : Env
  | "add1", [.bits 64], [.bits 64], (x, ()), m, Q, _ => Q (x + 1#64, ()) m
  | "caller", [.bits 64], [.bits 64], (a, ()), m, Q, _ => Q ((a + 1#64) * 2#64, ()) m
  | _, _, _, _, _, _, _ => False

theorem singleRet_modOk : ModuleOk singleRetΓ singleRetMod := by
  refine Module.moduleOk_of_checkAcyclic singleRet_checkAcyclic singleRet_wf ?_
  intro fn hfn xs m Q X hΓ
  simp only [singleRetMod, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl
  · rcases xs with ⟨x, ⟨⟩⟩
    exact hΓ
  · rcases xs with ⟨a, ⟨⟩⟩
    refine ⟨fun r m' => r = (a + 1#64, ()) ∧ m' = m, fun _ _ _ _ => False,
      ⟨rfl, rfl⟩, ?_, fun _ _ _ _ h => h.elim⟩
    rintro ⟨r, ⟨⟩⟩ m1 ⟨hr, hm1⟩
    subst hm1
    have hr' : r = a + 1#64 := (Prod.ext_iff.mp hr).1
    subst hr'
    exact hΓ

theorem singleRet_inline_modOk : ModuleOk singleRetΓ singleRetMod.inline :=
  Module.inline_ok 40 singleRet_modOk

theorem singleRet_inline_checkAcyclic : singleRetMod.inline.checkAcyclic = true :=
  Module.inline_checkAcyclic 40 singleRet_checkAcyclic singleRet_wf

theorem singleRet_inline_out :
    fnBodyAs [i64] [i64] (singleRetMod.inline.fns.getD 1 dummyFn) =
      fun _ _ (a, ()) =>
        .group (sig := [[i64]])
          (fun _ => .cons (fun (r, ()) =>
            .let_ (op2 (.mul i64) (.var r) (.imm 2)) fun (z, ()) =>
            .ret (.var z, ())) .nil)
          (fun (j, ()) =>
            .let_ (op2 (.add i64) (.var a) (.imm 1)) fun (y, ()) =>
            .jump j (.var y, ())) := by
  t_kernel_rfl

theorem singleRet_caller_checkTFlat :
    (match singleRetMod.inline.fns with
     | [_, c] => Func.checkTFlat c.body
     | _ => false) = true := by
  t_kernel_rfl

theorem singleRet_caller_spec (a : BitVec 64) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (hΓ : singleRetΓ "caller" [i64] [i64] (a, ()) m Q X) :
    Func.wp singleRetΓ (fnAdd1Caller.inline [fnAdd1.inline []]).body (a, ()) m Q X :=
  (singleRet_inline_modOk.fnsOk [fnAdd1.inline []] _ [] rfl).2.2 (a, ()) m Q X hΓ

/-! ## 2. Multi-block callee with `jnz`, `group`, and multiple `.ret` sites -/

/-- If `c` is true, jumps to join block `j(x + 1)` which multiplies by 3 and returns;
otherwise returns `x + 10` directly. -/
def fnMultiPick : Fn := ⟨"pick", [.bool, i64], [i64], fun _ _ (c, x, ()) =>
  .group (sig := [[i64]])
    (fun _ => .cons (fun (y, ()) =>
      .let_ (op2 (.mul i64) (.var y) (.imm 3)) fun (z, ()) =>
      .ret (.var z, ())) .nil)
    (fun (j, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.add i64) (.var x) (.imm 1)) fun (x1, ()) =>
         .jump j (.var x1, ()))
        (.let_ (op2 (.add i64) (.var x) (.imm 10)) fun (x10, ()) =>
         .ret (.var x10, ())))⟩

def fnMultiCaller : Fn := ⟨"mcaller", [.bool, i64], [i64], fun _ _ (c, a, ()) =>
  .call "pick" (as := [.bool, i64]) (bs := [i64]) (.var c, .var a, ()) fun (r1, ()) =>
  .call "pick" (as := [.bool, i64]) (bs := [i64]) (.imm false, .imm 5, ()) fun (r2, ()) =>
  .let_ (op2 (.add i64) (.var r1) (.var r2)) fun (sum, ()) =>
  .ret (.var sum, ())⟩

def multiBlockMod : Module where
  fns := [fnMultiPick, fnMultiCaller]

theorem multiBlock_checkAcyclic : multiBlockMod.checkAcyclic = true := by rfl

theorem multiBlock_wf : ∀ fn ∈ multiBlockMod.fns, fn.Wf := by
  intro fn hfn
  simp only [multiBlockMod, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl <;> (unfold Fn.Wf; t_wf_reify)

def multiPickSpec (c : Bool) (x : BitVec 64) : BitVec 64 :=
  if c then (x + 1#64) * 3#64 else x + 10#64

def multiBlockΓ : Env
  | "pick", [.bool, .bits 64], [.bits 64], (c, x, ()), m, Q, _ =>
      Q (multiPickSpec c x, ()) m
  | "mcaller", [.bool, .bits 64], [.bits 64], (c, a, ()), m, Q, _ =>
      Q (multiPickSpec c a + 15#64, ()) m
  | _, _, _, _, _, _, _ => False

theorem multiBlock_modOk : ModuleOk multiBlockΓ multiBlockMod := by
  refine Module.moduleOk_of_checkAcyclic multiBlock_checkAcyclic multiBlock_wf ?_
  intro fn hfn xs m Q X hΓ
  simp only [multiBlockMod, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl
  · rcases xs with ⟨c, x, ⟨⟩⟩
    intro Js hc
    rcases Js with ⟨j, ⟨⟩⟩
    have hj : ∀ y m', wp multiBlockΓ Q X
        (.let_ (op2 (.mul i64) (.var y.1) (.imm 3)) fun (z, ()) => .ret (.var z, ())) m' →
        j y m' := hc.1
    dsimp only [fnMultiPick] at hΓ
    cases c
    · change Q (multiPickSpec false x, ()) m at hΓ
      refine ⟨fun h => Bool.noConfusion h, fun _ => ?_⟩
      dsimp only [multiPickSpec] at hΓ
      exact hΓ
    · change Q (multiPickSpec true x, ()) m at hΓ
      refine ⟨fun _ => ?_, fun h => Bool.noConfusion h⟩
      apply hj (x + 1#64, ()) m
      dsimp only [multiPickSpec] at hΓ
      exact hΓ
  · rcases xs with ⟨c, a, ⟨⟩⟩
    refine ⟨fun r m' => r = (multiPickSpec c a, ()) ∧ m' = m, fun _ _ _ _ => False,
      ⟨rfl, rfl⟩, ?_, fun _ _ _ _ h => h.elim⟩
    rintro ⟨r1, ⟨⟩⟩ m1 ⟨hr1, hm1⟩
    subst hm1
    have hr1' : r1 = multiPickSpec c a := (Prod.ext_iff.mp hr1).1
    subst hr1'
    refine ⟨fun r m' => r = (15#64, ()) ∧ m' = m1, fun _ _ _ _ => False,
      ⟨rfl, rfl⟩, ?_, fun _ _ _ _ h => h.elim⟩
    rintro ⟨r2, ⟨⟩⟩ m2 ⟨hr2, hm2⟩
    subst hm2
    have hr2' : r2 = 15#64 := (Prod.ext_iff.mp hr2).1
    subst hr2'
    exact hΓ

theorem multiBlock_inline_modOk : ModuleOk multiBlockΓ (multiBlockMod.inline 40) :=
  Module.inline_ok 40 multiBlock_modOk

theorem multiBlock_inline_out :
    fnBodyAs [.bool, i64] [i64] (multiBlockMod.inline.fns.getD 1 dummyFn) =
      fun _ _ (c, a, ()) =>
        .group (sig := [[i64]])
          (fun _ => .cons (fun (r1, ()) =>
            .group (sig := [[i64]])
              (fun _ => .cons (fun (r2, ()) =>
                .let_ (op2 (.add i64) (.var r1) (.var r2)) fun (sum, ()) =>
                .ret (.var sum, ())) .nil)
              (fun (j2, ()) =>
                .group (sig := [[i64]])
                  (fun _ => .cons (fun (y2, ()) =>
                    .let_ (op2 (.mul i64) (.var y2) (.imm 3)) fun (z2, ()) =>
                    .jump j2 (.var z2, ())) .nil)
                  (fun (ji2, ()) =>
                    .jnz (.imm false)
                      (.let_ (op2 (.add i64) (.imm 5) (.imm 1)) fun (x1, ()) =>
                       .jump ji2 (.var x1, ()))
                      (.let_ (op2 (.add i64) (.imm 5) (.imm 10)) fun (x10, ()) =>
                       .jump j2 (.var x10, ()))))) .nil)
          (fun (j1, ()) =>
            .group (sig := [[i64]])
              (fun _ => .cons (fun (y1, ()) =>
                .let_ (op2 (.mul i64) (.var y1) (.imm 3)) fun (z1, ()) =>
                .jump j1 (.var z1, ())) .nil)
              (fun (ji1, ()) =>
                .jnz (.var c)
                  (.let_ (op2 (.add i64) (.var a) (.imm 1)) fun (x1, ()) =>
                   .jump ji1 (.var x1, ()))
                  (.let_ (op2 (.add i64) (.var a) (.imm 10)) fun (x10, ()) =>
                   .jump j1 (.var x10, ())))) := by
  t_kernel_rfl

theorem multiBlock_caller_checkTFlat :
    (match multiBlockMod.inline.fns with
     | [_, c] => Func.checkTFlat c.body
     | _ => false) = true := by
  t_kernel_rfl

/-! ## 3. Nested callee-to-callee inlining (`f -> g -> h`) -/

def fnLeafF : Fn := ⟨"leafF", [i64], [i64], fun _ _ (x, ()) =>
  .let_ (op2 (.add i64) (.var x) (.imm 1)) fun (r, ()) =>
  .ret (.var r, ())⟩

def fnMidG : Fn := ⟨"midG", [i64], [i64], fun _ _ (x, ()) =>
  .call "leafF" (as := [i64]) (bs := [i64]) (.var x, ()) fun (r, ()) =>
  .let_ (op2 (.mul i64) (.var r) (.imm 2)) fun (y, ()) =>
  .ret (.var y, ())⟩

def fnTopH : Fn := ⟨"topH", [i64], [i64], fun _ _ (x, ()) =>
  .call "midG" (as := [i64]) (bs := [i64]) (.var x, ()) fun (r, ()) =>
  .let_ (op2 (.add i64) (.var r) (.imm 3)) fun (z, ()) =>
  .ret (.var z, ())⟩

def nestedMod : Module where
  fns := [fnLeafF, fnMidG, fnTopH]

theorem nested_checkAcyclic : nestedMod.checkAcyclic = true := by rfl

theorem nested_wf : ∀ fn ∈ nestedMod.fns, fn.Wf := by
  intro fn hfn
  simp only [nestedMod, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl <;> (unfold Fn.Wf; t_wf_reify)

def nestedΓ : Env
  | "leafF", [.bits 64], [.bits 64], (x, ()), m, Q, _ => Q (x + 1#64, ()) m
  | "midG", [.bits 64], [.bits 64], (x, ()), m, Q, _ => Q ((x + 1#64) * 2#64, ()) m
  | "topH", [.bits 64], [.bits 64], (x, ()), m, Q, _ => Q ((x + 1#64) * 2#64 + 3#64, ()) m
  | _, _, _, _, _, _, _ => False

theorem nested_modOk : ModuleOk nestedΓ nestedMod := by
  refine Module.moduleOk_of_checkAcyclic nested_checkAcyclic nested_wf ?_
  intro fn hfn xs m Q X hΓ
  simp only [nestedMod, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl
  · rcases xs with ⟨x, ⟨⟩⟩
    exact hΓ
  · rcases xs with ⟨x, ⟨⟩⟩
    refine ⟨fun r m' => r = (x + 1#64, ()) ∧ m' = m, fun _ _ _ _ => False,
      ⟨rfl, rfl⟩, ?_, fun _ _ _ _ h => h.elim⟩
    rintro ⟨r, ⟨⟩⟩ m1 ⟨hr, hm1⟩
    subst hm1
    have hr' : r = x + 1#64 := (Prod.ext_iff.mp hr).1
    subst hr'
    exact hΓ
  · rcases xs with ⟨x, ⟨⟩⟩
    refine ⟨fun r m' => r = ((x + 1#64) * 2#64, ()) ∧ m' = m, fun _ _ _ _ => False,
      ⟨rfl, rfl⟩, ?_, fun _ _ _ _ h => h.elim⟩
    rintro ⟨r, ⟨⟩⟩ m1 ⟨hr, hm1⟩
    subst hm1
    have hr' : r = (x + 1#64) * 2#64 := (Prod.ext_iff.mp hr).1
    subst hr'
    exact hΓ

theorem nested_inline_modOk : ModuleOk nestedΓ (nestedMod.inline 40) :=
  Module.inline_ok 40 nested_modOk

/-- `midG` (inlining `leafF`) has zero remaining `.call` instructions. -/
theorem nested_midG_inline_out :
    fnBodyAs [i64] [i64] (nestedMod.inline.fns.getD 1 dummyFn) =
      fun _ _ (x, ()) =>
        .group (sig := [[i64]])
          (fun _ => .cons (fun (r, ()) =>
            .let_ (op2 (.mul i64) (.var r) (.imm 2)) fun (y, ()) =>
            .ret (.var y, ())) .nil)
          (fun (j1, ()) =>
            .let_ (op2 (.add i64) (.var x) (.imm 1)) fun (r1, ()) =>
            .jump j1 (.var r1, ())) := by
  t_kernel_rfl

/-- `topH` (inlining `midG` which already contains `leafF`) has zero remaining `.call`s. -/
theorem nested_topH_inline_out :
    fnBodyAs [i64] [i64] (nestedMod.inline.fns.getD 2 dummyFn) =
      fun _ _ (x, ()) =>
        .group (sig := [[i64]])
          (fun _ => .cons (fun (r, ()) =>
            .let_ (op2 (.add i64) (.var r) (.imm 3)) fun (z, ()) =>
            .ret (.var z, ())) .nil)
          (fun (j2, ()) =>
            .group (sig := [[i64]])
              (fun _ => .cons (fun (r1, ()) =>
                .let_ (op2 (.mul i64) (.var r1) (.imm 2)) fun (y, ()) =>
                .jump j2 (.var y, ())) .nil)
              (fun (j1, ()) =>
                .let_ (op2 (.add i64) (.var x) (.imm 1)) fun (r0, ()) =>
                .jump j1 (.var r0, ()))) := by
  t_kernel_rfl

theorem nested_topH_checkTFlat :
    (match nestedMod.inline.fns with
     | [_, _, h] => Func.checkTFlat h.body
     | _ => false) = true := by
  t_kernel_rfl

theorem nested_topH_spec (x : BitVec 64) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (hΓ : nestedΓ "topH" [i64] [i64] (x, ()) m Q X) :
    Func.wp nestedΓ
      (fnTopH.inline [fnMidG.inline [fnLeafF.inline []], fnLeafF.inline []]).body
      (x, ()) m Q X :=
  (nested_inline_modOk.fnsOk [fnLeafF.inline [], fnMidG.inline [fnLeafF.inline []]] _ [] rfl).2.2
    (x, ()) m Q X hΓ

/-! ## 4. Threshold bypass (`large` callee stays `.call`), `externs`, `exits`, and metadata -/

def addChain {V : Ty → Type} {L : List Ty → Type} : Nat → Arg V i64 → Expr V L [i64]
  | 0, acc => .ret (acc, ())
  | n + 1, acc => .let_ (op2 (.add i64) acc (.imm 1)) fun (y, ()) => addChain n (.var y)

def fnSmallHelper : Fn := ⟨"small", [i64], [i64], fun _ _ (x, ()) =>
  .let_ (op2 (.add i64) (.var x) (.imm 5)) fun (y, ()) =>
  .ret (.var y, ())⟩

def fnBigHelper : Fn := ⟨"big", [i64], [i64], fun _ _ (x, ()) =>
  addChain 10 (.var x)⟩

def fnHugeHelper : Fn := ⟨"huge", [i64], [i64], fun _ _ (x, ()) =>
  addChain 45 (.var x)⟩

def fnThreshCaller : Fn := ⟨"tcaller", [i64], [i64], fun _ _ (x, ()) =>
  .call "small" (as := [i64]) (bs := [i64]) (.var x, ()) fun (a, ()) =>
  .call "big" (as := [i64]) (bs := [i64]) (.var a, ()) fun (b, ()) =>
  .call "extLog" (as := [i64]) (bs := []) (.var b, ()) fun _ =>
  .jnz (.imm true)
    (.ret (.var b, ()))
    (.exit "abort" (as := [i64]) (.var b, ()))⟩

def thresholdMod : Module where
  fns := [fnSmallHelper, fnBigHelper, fnThreshCaller]
  externs := [⟨"extLog", [i64], []⟩]
  exits := ["abort"]

theorem threshold_size_checks :
    fnSmallHelper.size = 2 ∧ fnBigHelper.size = 11 ∧ fnHugeHelper.size = 46 := by
  decide

theorem threshold_sigs_eq : (thresholdMod.inline 5).sigs = thresholdMod.sigs :=
  Module.inline_sigs thresholdMod 5

theorem threshold_namesNodup_eq : (thresholdMod.inline 5).namesNodup = thresholdMod.namesNodup :=
  Module.inline_namesNodup thresholdMod 5

theorem threshold_checkAcyclic : thresholdMod.checkAcyclic = true := by rfl

theorem threshold_wf : ∀ fn ∈ thresholdMod.fns, fn.Wf := by
  intro fn hfn
  simp only [thresholdMod, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl <;> (unfold Fn.Wf; t_wf_reify)

theorem threshold_inline_checkAcyclic : (thresholdMod.inline 5).checkAcyclic = true :=
  Module.inline_checkAcyclic 5 threshold_checkAcyclic threshold_wf

/-- With `maxSize = 5`, `"small"` (size 2) is inlined while `"big"` (size 11) and extern
`"extLog"` stay `.call`. -/
theorem threshold_inline_out :
    fnBodyAs [i64] [i64] ((thresholdMod.inline 5).fns.getD 2 dummyFn) =
      fun _ _ (x, ()) =>
        .group (sig := [[i64]])
          (fun _ => .cons (fun (a, ()) =>
            .call "big" (as := [i64]) (bs := [i64]) (.var a, ()) fun (b, ()) =>
            .call "extLog" (as := [i64]) (bs := []) (.var b, ()) fun _ =>
            .jnz (.imm true)
              (.ret (.var b, ()))
              (.exit "abort" (as := [i64]) (.var b, ()))) .nil)
          (fun (j, ()) =>
            .let_ (op2 (.add i64) (.var x) (.imm 5)) fun (y, ()) =>
            .jump j (.var y, ())) := by
  t_kernel_rfl

/-- Default threshold `maxSize = 40` bypasses `fnHugeHelper` (size 46) while inlining
`fnSmallHelper`. -/
def defaultThreshMod : Module where
  fns := [fnSmallHelper, fnHugeHelper, fnThreshCaller]
  externs := [⟨"extLog", [i64], []⟩]
  exits := ["abort"]

theorem defaultThresh_inline_out :
    (match (defaultThreshMod.inline).fns with
     | [_, _, c] => Func.size c.body < 46
     | _ => false) = true := by
  decide

def threshΓ : Env
  | "small", [.bits 64], [.bits 64], (x, ()), m, Q, _ => Q (x + 5#64, ()) m
  | "big", [.bits 64], [.bits 64], (x, ()), m, Q, _ => Q (x + 10#64, ()) m
  | "extLog", [.bits 64], [], (_, ()), m, Q, _ => Q () m
  | "tcaller", [.bits 64], [.bits 64], (x, ()), m, Q, _ => Q (x + 15#64, ()) m
  | _, _, _, _, _, _, _ => False

private theorem addChain_wp (Γ : Env) (n : Nat) (x : BitVec 64) (m : Mem 64)
    (Q : Post [i64]) (X : XPost) (h : Q (x + BitVec.ofNat 64 n, ()) m) :
    wp Γ Q X (addChain n (.var x)) m := by
  induction n generalizing x with
  | zero =>
      dsimp only [addChain, wp, vals, Arg.val]
      simpa using h
  | succ n ih =>
      simp only [addChain, wp, Op.wp, op2, OpCode.wp_add, Ty.hasFloat, Bool.false_eq_true,
        ↓reduceIte, lift2, vals, Arg.val]
      apply ih (x + 1#64)
      have hsucc : BitVec.ofNat 64 (n + 1) = 1#64 + BitVec.ofNat 64 n := by
        simp [BitVec.ofNat_add, BitVec.add_comm]
      rw [hsucc, ← BitVec.add_assoc] at h
      exact h

theorem threshold_modOk : ModuleOk threshΓ thresholdMod := by
  refine Module.moduleOk_of_checkAcyclic threshold_checkAcyclic threshold_wf ?_
  intro fn hfn xs m Q X hΓ
  simp only [thresholdMod, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl
  · rcases xs with ⟨x, ⟨⟩⟩
    exact hΓ
  · rcases xs with ⟨x, ⟨⟩⟩
    exact addChain_wp threshΓ 10 x m Q X hΓ
  · rcases xs with ⟨x, ⟨⟩⟩
    refine ⟨fun r m' => r = (x + 5#64, ()) ∧ m' = m, fun _ _ _ _ => False,
      ⟨rfl, rfl⟩, ?_, fun _ _ _ _ h => h.elim⟩
    rintro ⟨a, ⟨⟩⟩ m1 ⟨ha, hm1⟩
    subst hm1
    have ha' : a = x + 5#64 := (Prod.ext_iff.mp ha).1
    subst ha'
    refine ⟨fun r m' => r = ((x + 5#64) + 10#64, ()) ∧ m' = m1, fun _ _ _ _ => False,
      ⟨rfl, rfl⟩, ?_, fun _ _ _ _ h => h.elim⟩
    rintro ⟨b, ⟨⟩⟩ m2 ⟨hb, hm2⟩
    subst hm2
    have hb' : b = (x + 5#64) + 10#64 := (Prod.ext_iff.mp hb).1
    subst hb'
    refine ⟨fun _ m' => m' = m2, fun _ _ _ _ => False, rfl, ?_, fun _ _ _ _ h => h.elim⟩
    intro _ m3 hm3
    subst hm3
    refine ⟨fun _ => ?_, fun h => Bool.noConfusion h⟩
    have h15 : (x + 5#64) + 10#64 = x + 15#64 := by
      rw [BitVec.add_assoc]; rfl
    rwa [h15]

theorem threshold_inline_modOk : ModuleOk threshΓ (thresholdMod.inline 5) :=
  Module.inline_ok 5 threshold_modOk

/-! ## 5. Signature mismatch, unsafe callee guard, and `Func.opt` composition -/

def fnSigMismatchCaller : Fn := ⟨"mcaller", [i32], [i32], fun _ _ (x, ()) =>
  .call "add1" (as := [i32]) (bs := [i32]) (.var x, ()) fun (y, ()) =>
  .ret (.var y, ())⟩

/-- Signature-mismatched calls (`[i32] -> [i32]` vs `fnAdd1 : [i64] -> [i64]`) stay `.call`. -/
theorem sigMismatch_not_inlined :
    Func.inline [fnAdd1] fnSigMismatchCaller.body = fnSigMismatchCaller.body := by
  t_kernel_rfl

/-- An ill-scoped small callee (e.g. calling itself) is rejected by `inlineCandidateOk`. -/
def unsafeMod : Module where
  fns :=
    [selfRecFn,
     ⟨"caller", [], [], fun _ _ _ => .call "self" (as := []) (bs := []) () fun _ => .ret ()⟩]

theorem unsafe_selfRec_not_inlined :
    (unsafeMod.inline.fns.getD 1 dummyFn).body = (unsafeMod.fns.getD 1 dummyFn).body := by
  t_kernel_rfl

/-- Post-inlining `Func.opt` simplifies the spliced callee body and preserves `Wf` and `spec`. -/
theorem singleRet_opt_inlined_wf :
    (Func.opt (fnAdd1Caller.inline [fnAdd1]).body).Wf :=
  Func.opt_wf (Func.inline_wf (fun _ h => by
    simp only [List.mem_singleton] at h; subst h; exact singleRet_wf fnAdd1 List.mem_cons_self)
    (singleRet_wf fnAdd1Caller (List.mem_cons_of_mem _ List.mem_cons_self)))

theorem singleRet_opt_inlined_spec (a : BitVec 64) (m : Mem 64) :
    Func.spec singleRetΓ (Func.opt (fnAdd1Caller.inline [fnAdd1]).body) (a, ()) m
      (fun r m' => r = ((a + 1#64) * 2#64, ()) ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.opt_spec
  · exact Func.inline_wf (fun _ h => by
      simp only [List.mem_singleton] at h; subst h; exact singleRet_wf fnAdd1 List.mem_cons_self)
      (singleRet_wf fnAdd1Caller (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact singleRet_caller_spec a m _ _ ⟨rfl, rfl⟩

/-- `Module.optInline` preserves `ModuleOk` across acyclic inlining + renormalization. -/
theorem singleRet_optInline_modOk : ModuleOk singleRetΓ singleRetMod.optInline :=
  Module.optInline_ok 40 singleRet_modOk

theorem nested_optInline_modOk : ModuleOk nestedΓ nestedMod.optInline :=
  Module.optInline_ok 40 nested_modOk

/-- Post-inlining `Func.earlyOpt` collapses the spliced single-use `.group` into straight-line
code. -/
theorem singleRet_earlyOpt_inlined_out :
    Func.earlyOpt (fnAdd1Caller.inline [fnAdd1]).body = fun _ _ (a, ()) =>
      .let_ (op2 (.add i64) (.var a) (.imm 1)) fun (y, ()) =>
      .let_ (op2 (.shl i64) (.var y) (.imm 1)) fun (z, ()) =>
      .ret (.var z, ()) := by
  t_kernel_rfl

theorem singleRet_earlyOpt_inlined_wf :
    (Func.earlyOpt (fnAdd1Caller.inline [fnAdd1]).body).Wf :=
  Func.earlyOpt_wf (Func.inline_wf (fun _ h => by
    simp only [List.mem_singleton] at h; subst h; exact singleRet_wf fnAdd1 List.mem_cons_self)
    (singleRet_wf fnAdd1Caller (List.mem_cons_of_mem _ List.mem_cons_self)))

theorem singleRet_earlyOpt_inlined_spec (a : BitVec 64) (m : Mem 64) :
    Func.spec singleRetΓ (Func.earlyOpt (fnAdd1Caller.inline [fnAdd1]).body) (a, ()) m
      (fun r m' => r = ((a + 1#64) * 2#64, ()) ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.earlyOpt_spec
  · exact Func.inline_wf (fun _ h => by
      simp only [List.mem_singleton] at h; subst h; exact singleRet_wf fnAdd1 List.mem_cons_self)
      (singleRet_wf fnAdd1Caller (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact singleRet_caller_spec a m _ _ ⟨rfl, rfl⟩

/-! ## 6. Policy-driven inlining (`budget : Sym → Nat` & `singleSiteMax`) -/

def fnSingleSiteBig : Fn := ⟨"singleBig", [i64], [i64], fun _ _ (x, ()) =>
  addChain 10 (.var x)⟩

def fnMultiSiteBig : Fn := ⟨"multiBig", [i64], [i64], fun _ _ (x, ()) =>
  addChain 10 (.var x)⟩

def fnPolicyCaller1 : Fn := ⟨"pcaller1", [i64], [i64], fun _ _ (x, ()) =>
  .call "singleBig" (as := [i64]) (bs := [i64]) (.var x, ()) fun (a, ()) =>
  .call "multiBig" (as := [i64]) (bs := [i64]) (.var a, ()) fun (b, ()) =>
  .ret (.var b, ())⟩

def fnPolicyCaller2 : Fn := ⟨"pcaller2", [i64], [i64], fun _ _ (x, ()) =>
  .call "multiBig" (as := [i64]) (bs := [i64]) (.var x, ()) fun (b, ()) =>
  .ret (.var b, ())⟩

def policyMod : Module where
  fns := [fnSingleSiteBig, fnMultiSiteBig, fnPolicyCaller1, fnPolicyCaller2]

def singleSitePolicy : InlinePolicy :=
  { budget := fun _ => 5, singleSiteMax := 15 }

def symBudgetPolicy : InlinePolicy :=
  { budget := fun s => if s == "multiBig" then 15 else 5, singleSiteMax := 0 }

theorem policyMod_checkAcyclic : policyMod.checkAcyclic = true := by rfl

theorem policyMod_wf : ∀ fn ∈ policyMod.fns, fn.Wf := by
  intro fn hfn
  simp only [policyMod, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl | rfl <;> (unfold Fn.Wf; t_wf_reify)

def policyΓ : Env
  | "singleBig", [.bits 64], [.bits 64], (x, ()), m, Q, _ => Q (x + 10#64, ()) m
  | "multiBig", [.bits 64], [.bits 64], (x, ()), m, Q, _ => Q (x + 10#64, ()) m
  | "pcaller1", [.bits 64], [.bits 64], (x, ()), m, Q, _ => Q (x + 20#64, ()) m
  | "pcaller2", [.bits 64], [.bits 64], (x, ()), m, Q, _ => Q (x + 10#64, ()) m
  | _, _, _, _, _, _, _ => False

theorem policyMod_modOk : ModuleOk policyΓ policyMod := by
  refine Module.moduleOk_of_checkAcyclic policyMod_checkAcyclic policyMod_wf ?_
  intro fn hfn xs m Q X hΓ
  simp only [policyMod, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl | rfl
  · rcases xs with ⟨x, ⟨⟩⟩; exact addChain_wp policyΓ 10 x m Q X hΓ
  · rcases xs with ⟨x, ⟨⟩⟩; exact addChain_wp policyΓ 10 x m Q X hΓ
  · rcases xs with ⟨x, ⟨⟩⟩
    refine ⟨fun r m' => r = (x + 10#64, ()) ∧ m' = m, fun _ _ _ _ => False,
      ⟨rfl, rfl⟩, ?_, fun _ _ _ _ h => h.elim⟩
    rintro ⟨a, ⟨⟩⟩ m1 ⟨ha, hm1⟩; subst hm1
    have ha' : a = x + 10#64 := (Prod.ext_iff.mp ha).1; subst ha'
    refine ⟨fun r m' => r = ((x + 10#64) + 10#64, ()) ∧ m' = m1, fun _ _ _ _ => False,
      ⟨rfl, rfl⟩, ?_, fun _ _ _ _ h => h.elim⟩
    rintro ⟨b, ⟨⟩⟩ m2 ⟨hb, hm2⟩; subst hm2
    have hb' : b = (x + 10#64) + 10#64 := (Prod.ext_iff.mp hb).1; subst hb'
    have h20 : (x + 10#64) + 10#64 = x + 20#64 := by rw [BitVec.add_assoc]; rfl
    rwa [h20]
  · rcases xs with ⟨x, ⟨⟩⟩
    refine ⟨fun r m' => r = (x + 10#64, ()) ∧ m' = m, fun _ _ _ _ => False,
      ⟨rfl, rfl⟩, ?_, fun _ _ _ _ h => h.elim⟩
    rintro ⟨b, ⟨⟩⟩ m1 ⟨hb, hm1⟩; subst hm1
    have hb' : b = x + 10#64 := (Prod.ext_iff.mp hb).1; subst hb'
    exact hΓ

theorem policy_const_eq_rfl :
    singleRetMod.inline 40 = singleRetMod.inlinePolicy (InlinePolicy.const 40) := rfl

theorem policy_optInline_const_eq_rfl :
    singleRetMod.optInline 40 = singleRetMod.optInlinePolicy (InlinePolicy.const 40) := rfl

/-- Under `singleSitePolicy`, `"singleBig"` (1 call site) is inlined while `"multiBig"`
(2 call sites) remains a `.call`. -/
theorem policy_singleSite_inlines_only_single :
    let body :=
      ((policyMod.inlinePolicy singleSitePolicy).fns.getD 2 dummyFn).body
        (fun _ => Unit) (fun _ => Unit) (Tup.units [i64])
    Expr.checkCallsOk [⟨"multiBig", [i64], [i64]⟩] [] body = true ∧
      Expr.checkCallsOk [] [] body = false := by
  decide

/-- Under `symBudgetPolicy`, `"multiBig"` (per-symbol budget 15) is inlined while `"singleBig"`
(budget 5) remains a `.call`. -/
theorem policy_symBudget_selects_multiBig :
    let body :=
      ((policyMod.inlinePolicy symBudgetPolicy).fns.getD 2 dummyFn).body
        (fun _ => Unit) (fun _ => Unit) (Tup.units [i64])
    Expr.checkCallsOk [⟨"singleBig", [i64], [i64]⟩] [] body = true ∧
      Expr.checkCallsOk [] [] body = false := by
  decide

theorem policy_singleSite_modOk :
    ModuleOk policyΓ (policyMod.inlinePolicy singleSitePolicy) :=
  Module.inlinePolicy_ok singleSitePolicy policyMod_modOk

theorem policy_singleSite_optInline_modOk :
    ModuleOk policyΓ (policyMod.optInlinePolicy singleSitePolicy) :=
  Module.optInlinePolicy_ok singleSitePolicy policyMod_modOk

theorem policy_singleSite_checkAcyclic :
    (policyMod.optInlinePolicy singleSitePolicy).checkAcyclic = true :=
  Module.optInlinePolicy_checkAcyclic singleSitePolicy policyMod_checkAcyclic policyMod_wf

theorem policy_symBudget_optInline_modOk :
    ModuleOk policyΓ (policyMod.optInlinePolicy symBudgetPolicy) :=
  Module.optInlinePolicy_ok symBudgetPolicy policyMod_modOk

/-! ## 7. Axiom Audit -/

#print axioms LeanQbe.T.spliceRet_wp
#print axioms LeanQbe.T.inline_wp
#print axioms LeanQbe.T.inline_wf
#print axioms LeanQbe.T.inline_callsOk
#print axioms LeanQbe.T.Module.inline_ok
#print axioms LeanQbe.T.Module.inlinePolicy_ok
#print axioms LeanQbe.T.Module.inline_checkAcyclic
#print axioms LeanQbe.T.Module.inlinePolicy_checkAcyclic
#print axioms LeanQbe.T.Func.renorm_callsOk
#print axioms LeanQbe.T.Module.optInline_ok
#print axioms LeanQbe.T.Module.optInlinePolicy_ok
#print axioms LeanQbe.T.Module.optInlinePolicy_checkAcyclic
#print axioms LeanQbe.T.Module.optInlinePolicy_wf
#print axioms LeanQbe.T.compile_sound_optInlinePolicy
#print axioms LeanQbe.T.optInlinePolicy_sound
#print axioms LeanQbe.T.Compiled.fnSpec_optInlinePolicy
#print axioms LeanQbe.T.Compiled.fnSpec_host_optInlinePolicy
#print axioms LeanQbe.T.Compiled.fnSpec_noExit_id_optInlinePolicy
#print axioms singleRet_inline_modOk
#print axioms singleRet_optInline_modOk
#print axioms multiBlock_inline_modOk
#print axioms nested_inline_modOk
#print axioms nested_optInline_modOk
#print axioms threshold_inline_modOk
#print axioms singleRet_earlyOpt_inlined_spec
#print axioms policy_singleSite_modOk
#print axioms policy_singleSite_optInline_modOk
#print axioms policy_singleSite_checkAcyclic
#print axioms policy_symBudget_optInline_modOk

end LeanQbeTest.T.InlineTest
