module

import LeanQbe.T.LinkBudgetLfp
import LeanQbe.T.WPLemmas
import LeanQbe.T.AbiLemmas

/-!
# Tests for `LeanQbe.T.LinkBudgetLfp`

Exercises:
1. Knaster–Tarski `BudgetEnv.lfp` lattice laws, `lfp_budget_mono`, `lfp_wf`, and
   `lfp_le_of_prefix_below`.
2. Non-uniform mutual cycle (`16 → 80 → 16` = `112 * d + 16 < 240 * d` + tightness witness
   at `127 B`), plus `lfp_wf_mkSccOp` and per-function `minEntry` isolation (no bleed onto
   sibling SCC functions).
3. Well-founded non-tail equivalence (`lfp_eq_wfRec_of_noTail` / `semScc_eq_wfRec_of_noTail`)
   on both `exCycleMod` and a `maxFrame = 0` `NoCall` leaf module.
4. Legacy acyclic `ModuleOk` embedding (`moduleOk_embeds_into_budget_semScc`).
5. Single-shot machine pre-fixpoint and `Target.FnSpec` bridge (`semScc_le_mach_single_shot`,
   `budget_semScc_to_target_fnSpec`).
6. Single-line `#print axioms` audit (`[propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.LinkBudgetLfpTest

open LeanQbe.T

def envBot : Env := fun _ _ _ _ _ _ _ => False

/-! ## 1. `BudgetEnv.lfp` Lattice Laws & Prefix Locality -/

theorem lfp_laws_ok (Φ : BudgetEnv → BudgetEnv) (hm : BudgetEnv.mono Φ) :
    BudgetEnv.le (Φ (BudgetEnv.lfp Φ)) (BudgetEnv.lfp Φ) ∧
    BudgetEnv.le (BudgetEnv.lfp Φ) (Φ (BudgetEnv.lfp Φ)) ∧
    BudgetEnv.lfp Φ = Φ (BudgetEnv.lfp Φ) :=
  ⟨BudgetEnv.lfp_pre hm, BudgetEnv.lfp_post hm, BudgetEnv.lfp_fix hm⟩

/-! ## 2. Non-Uniform Mutual Cycle (`16 → 80 → 16`, `112 * d + 16 < 240 * d`, Tight at `127`) -/

private def stepFn (name next : Sym) : Fn :=
  { name := name, as := [i32], rs := [i32], body := fun _ _ xs =>
      let n := xs.1
      .let_ (op2 (.cmp .eq i32) (.var n) (.imm (0#32))) fun c =>
        .jnz (.var c.1)
          (.ret (.imm (0#32), ()))
          (.let_ (op2 (.sub i32) (.var n) (.imm (1#32))) fun n1 =>
            .call next (as := [i32]) (bs := [i32]) (.var n1.1, ()) fun r =>
              .ret (.var r.1, ())) }

def exCycleMod : BudgetModule :=
  { fns := [
      { toFn := stepFn "f" "g", maxFrame := 16 },
      { toFn := stepFn "g" "h", maxFrame := 80 },
      { toFn := stepFn "h" "f", maxFrame := 16 }
    ] }

private theorem wp_stepFn (Γ : Env) (name next : Sym)
    (n : BitVec 32) (m : Mem 64) (Q : Post [i32]) (X : XPost)
    (h0 : n = 0#32 → Q (0#32, ()) m)
    (hpos : n ≠ 0#32 →
      ∃ P E, Γ next [i32] [i32] (n - 1#32, ()) m P E ∧
        (∀ r m', P r m' → Q r m') ∧ (∀ g cs xs m', E g cs xs m' → X g cs xs m')) :
    Func.wp Γ (stepFn name next).body (n, ()) m Q X := by
  dsimp [Func.wp, stepFn, wp, Op.wp, OpCode.wp, liftCmp, CmpOp.evalBits, vals, Arg.val, lift2]
  constructor
  · intro heq
    have hn : n = 0#32 := of_decide_eq_true heq
    exact h0 hn
  · intro hne
    have hn : n ≠ 0#32 := by
      intro h
      subst h
      exact absurd hne (by decide)
    exact hpos hn

private theorem wp_stepFn_inv {Γ : Env} {name next : Sym}
    {n : BitVec 32} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (h : Func.wp Γ (stepFn name next).body (n, ()) m Q X) (hne : n ≠ 0#32) :
    ∃ P E, Γ next [i32] [i32] (n - 1#32, ()) m P E ∧
      (∀ r m', P r m' → Q r m') ∧ (∀ g cs xs m', E g cs xs m' → X g cs xs m') := by
  dsimp [Func.wp, stepFn, wp, Op.wp, OpCode.wp, liftCmp, CmpOp.evalBits, vals, Arg.val, lift2]
    at h
  exact h.2 (decide_eq_false hne)

private theorem bv32_ne_zero {k : Nat} (hpos : 0 < k) (hlt : k < 2 ^ 32) :
    BitVec.ofNat 32 k ≠ 0#32 := by
  intro heq
  have := congrArg BitVec.toNat heq
  simp [Nat.mod_eq_of_lt hlt] at this
  omega

private theorem bv32_sub_one {k : Nat} (hpos : 0 < k) (hlt : k < 2 ^ 32) :
    BitVec.ofNat 32 k - 1#32 = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_sub, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega : k - 1 < 2 ^ 32)]
  omega

private theorem exCycle_ind (d : Nat) (hd : 3 * d + 2 < 2 ^ 32) :
    (∀ m, BudgetEnv.semScc exCycleMod envBot (112 * d + 16) "f" [i32] [i32]
      (BitVec.ofNat 32 (3 * d), ()) m (fun r _ => r.1 = 0#32) (fun _ _ _ _ => False)) ∧
    (∀ m, BudgetEnv.semScc exCycleMod envBot (112 * d + 112) "g" [i32] [i32]
      (BitVec.ofNat 32 (3 * d + 2), ()) m (fun r _ => r.1 = 0#32) (fun _ _ _ _ => False)) ∧
    (∀ m, BudgetEnv.semScc exCycleMod envBot (112 * d + 32) "h" [i32] [i32]
      (BitVec.ofNat 32 (3 * d + 1), ()) m (fun r _ => r.1 = 0#32) (fun _ _ _ _ => False)) := by
  induction d with
  | zero =>
      have hf0 : ∀ m, BudgetEnv.semScc exCycleMod envBot 16 "f" [i32] [i32]
          (0#32, ()) m (fun r _ => r.1 = 0#32) (fun _ _ _ _ => False) := by
        intro m
        rw [BudgetEnv.semScc_fix]
        refine ⟨{ toFn := stepFn "f" "g", maxFrame := 16 }, by simp [exCycleMod], rfl, rfl, rfl,
          by decide, by decide, ?_⟩
        exact wp_stepFn _ "f" "g" 0#32 m _ _ (fun _ => rfl) (fun hn => absurd rfl hn)
      have hh1 : ∀ m, BudgetEnv.semScc exCycleMod envBot 32 "h" [i32] [i32]
          (1#32, ()) m (fun r _ => r.1 = 0#32) (fun _ _ _ _ => False) := by
        intro m
        rw [BudgetEnv.semScc_fix]
        refine ⟨{ toFn := stepFn "h" "f", maxFrame := 16 }, by simp [exCycleMod], rfl, rfl, rfl,
          by decide, by decide, ?_⟩
        refine wp_stepFn _ "h" "f" 1#32 m _ _ (fun _ => rfl) (fun _ => ?_)
        refine ⟨fun r _ => r.1 = 0#32, fun _ _ _ _ => False, Or.inl ⟨?_, hf0 m⟩,
          fun _ _ hr => hr, fun _ _ _ _ hx => hx⟩
        simp [BudgetModule.fnSigs, exCycleMod, Fn.sig, stepFn]
      have hg2 : ∀ m, BudgetEnv.semScc exCycleMod envBot 112 "g" [i32] [i32]
          (2#32, ()) m (fun r _ => r.1 = 0#32) (fun _ _ _ _ => False) := by
        intro m
        rw [BudgetEnv.semScc_fix]
        refine ⟨{ toFn := stepFn "g" "h", maxFrame := 80 }, by simp [exCycleMod], rfl, rfl, rfl,
          by decide, by decide, ?_⟩
        refine wp_stepFn _ "g" "h" 2#32 m _ _ (fun _ => rfl) (fun _ => ?_)
        refine ⟨fun r _ => r.1 = 0#32, fun _ _ _ _ => False, Or.inl ⟨?_, hh1 m⟩,
          fun _ _ hr => hr, fun _ _ _ _ hx => hx⟩
        simp [BudgetModule.fnSigs, exCycleMod, Fn.sig, stepFn]
      exact ⟨hf0, hg2, hh1⟩
  | succ d ih =>
      rcases ih (by omega) with ⟨_, hg_d, _⟩
      have hf_next : ∀ m, BudgetEnv.semScc exCycleMod envBot (112 * (d + 1) + 16) "f"
          [i32] [i32] (BitVec.ofNat 32 (3 * (d + 1)), ()) m
          (fun r _ => r.1 = 0#32) (fun _ _ _ _ => False) := by
        intro m
        rw [BudgetEnv.semScc_fix]
        refine ⟨{ toFn := stepFn "f" "g", maxFrame := 16 }, by simp [exCycleMod], rfl, rfl, rfl,
          by dsimp only; omega, by dsimp only; omega, ?_⟩
        refine wp_stepFn _ "f" "g" _ m _ _
          (fun h0 => absurd h0 (bv32_ne_zero (by omega) (by omega))) (fun _ => ?_)
        rw [bv32_sub_one (by omega) (by omega)]
        have hsub : 112 * (d + 1) + 16 - 16 = 112 * d + 112 := by omega
        refine ⟨fun r _ => r.1 = 0#32, fun _ _ _ _ => False, Or.inl ⟨?_, ?_⟩,
          fun _ _ hr => hr, fun _ _ _ _ hx => hx⟩
        · simp [BudgetModule.fnSigs, exCycleMod, Fn.sig, stepFn]
        · dsimp only [BudgetEnv.callSlot]; rw [hsub]; exact hg_d m
      have hh_next : ∀ m, BudgetEnv.semScc exCycleMod envBot (112 * (d + 1) + 32) "h"
          [i32] [i32] (BitVec.ofNat 32 (3 * (d + 1) + 1), ()) m
          (fun r _ => r.1 = 0#32) (fun _ _ _ _ => False) := by
        intro m
        rw [BudgetEnv.semScc_fix]
        refine ⟨{ toFn := stepFn "h" "f", maxFrame := 16 }, by simp [exCycleMod], rfl, rfl, rfl,
          by dsimp only; omega, by dsimp only; omega, ?_⟩
        refine wp_stepFn _ "h" "f" _ m _ _
          (fun h0 => absurd h0 (bv32_ne_zero (by omega) (by omega))) (fun _ => ?_)
        rw [bv32_sub_one (by omega) (by omega)]
        have hsub : 112 * (d + 1) + 32 - 16 = 112 * (d + 1) + 16 := by omega
        refine ⟨fun r _ => r.1 = 0#32, fun _ _ _ _ => False, Or.inl ⟨?_, ?_⟩,
          fun _ _ hr => hr, fun _ _ _ _ hx => hx⟩
        · simp [BudgetModule.fnSigs, exCycleMod, Fn.sig, stepFn]
        · dsimp only [BudgetEnv.callSlot]; rw [hsub]; exact hf_next m
      have hg_next : ∀ m, BudgetEnv.semScc exCycleMod envBot (112 * (d + 1) + 112) "g"
          [i32] [i32] (BitVec.ofNat 32 (3 * (d + 1) + 2), ()) m
          (fun r _ => r.1 = 0#32) (fun _ _ _ _ => False) := by
        intro m
        rw [BudgetEnv.semScc_fix]
        refine ⟨{ toFn := stepFn "g" "h", maxFrame := 80 }, by simp [exCycleMod], rfl, rfl, rfl,
          by dsimp only; omega, by dsimp only; omega, ?_⟩
        refine wp_stepFn _ "g" "h" _ m _ _
          (fun h0 => absurd h0 (bv32_ne_zero (by omega) (by omega))) (fun _ => ?_)
        rw [bv32_sub_one (by omega) (by omega)]
        have hsub : 112 * (d + 1) + 112 - 80 = 112 * (d + 1) + 32 := by omega
        refine ⟨fun r _ => r.1 = 0#32, fun _ _ _ _ => False, Or.inl ⟨?_, ?_⟩,
          fun _ _ hr => hr, fun _ _ _ _ hx => hx⟩
        · simp [BudgetModule.fnSigs, exCycleMod, Fn.sig, stepFn]
        · dsimp only [BudgetEnv.callSlot]; rw [hsub]; exact hh_next m
      exact ⟨hf_next, hg_next, hh_next⟩

theorem ex_cycle_ok (d : Nat) (hd : 3 * d + 2 < 2 ^ 32) (m : Mem 64) :
    BudgetEnv.semScc exCycleMod envBot (112 * d + 16) "f" [i32] [i32]
      (BitVec.ofNat 32 (3 * d), ()) m (fun r _ => r.1 = 0#32) (fun _ _ _ _ => False) :=
  (exCycle_ind d hd).1 m

theorem ex_cycle_gap (d : Nat) (hd : 1 ≤ d) :
    112 * d + 16 < 3 * 80 * d := by
  omega

/-- Tightness witness at `d = 1`: `112 * 1 + 16 = 128 B` succeeds, whereas `127 B` fails. -/
theorem ex_cycle_tight :
    ¬ BudgetEnv.semScc exCycleMod envBot 127 "f" [i32] [i32]
      (3#32, ()) default (fun r _ => r.1 = 0#32) (fun _ _ _ _ => False) := by
  intro hf3
  rw [BudgetEnv.semScc_fix] at hf3
  rcases hf3 with ⟨bf1, hm1, hn1, ha1, hr1, _, _, hwp1⟩
  rcases List.mem_cons.mp hm1 with h | hm1
  · subst h; cases ha1; cases hr1
    rcases wp_stepFn_inv hwp1 (by decide) with ⟨_, _, hg2, _, _⟩
    rcases hg2 with ⟨_, hg2⟩ | ⟨hex, _⟩
    · dsimp [BudgetEnv.callSlot] at hg2
      rw [BudgetEnv.semScc_fix] at hg2
      rcases hg2 with ⟨bf2, hm2, hn2, ha2, hr2, _, _, hwp2⟩
      rcases List.mem_cons.mp hm2 with h | hm2
      · subst h; simp [stepFn] at hn2
      · rcases List.mem_cons.mp hm2 with h | hm2
        · subst h; cases ha2; cases hr2
          rcases wp_stepFn_inv hwp2 (by decide) with ⟨_, _, hh1, _, _⟩
          rcases hh1 with ⟨_, hh1⟩ | ⟨hex, _⟩
          · dsimp [BudgetEnv.callSlot] at hh1
            rw [BudgetEnv.semScc_fix] at hh1
            rcases hh1 with ⟨bf3, hm3, hn3, ha3, hr3, _, _, hwp3⟩
            rcases List.mem_cons.mp hm3 with h | hm3
            · subst h; simp [stepFn] at hn3
            · rcases List.mem_cons.mp hm3 with h | hm3
              · subst h; simp [stepFn] at hn3
              · rcases List.mem_cons.mp hm3 with h | hnil
                · subst h; cases ha3; cases hr3
                  rcases wp_stepFn_inv hwp3 (by decide) with ⟨_, _, hf0, _, _⟩
                  rcases hf0 with ⟨_, hf0⟩ | ⟨hex, _⟩
                  · dsimp [BudgetEnv.callSlot] at hf0
                    rw [BudgetEnv.semScc_fix] at hf0
                    rcases hf0 with ⟨bf4, hm4, hn4, _, _, hmax4, _, _⟩
                    rcases List.mem_cons.mp hm4 with h | hm4
                    · subst h; dsimp at hmax4; exact absurd hmax4 (by decide)
                    · rcases List.mem_cons.mp hm4 with h | hm4
                      · subst h; simp [stepFn] at hn4
                      · rcases List.mem_cons.mp hm4 with h | hnil4
                        · subst h; simp [stepFn] at hn4
                        · cases hnil4
                  · simp [BudgetModule.extSigs, exCycleMod] at hex
                · cases hnil
          · simp [BudgetModule.extSigs, exCycleMod] at hex
        · rcases List.mem_cons.mp hm2 with h | hnil
          · subst h; simp [stepFn] at hn2
          · cases hnil
    · simp [BudgetModule.extSigs, exCycleMod] at hex
  · rcases List.mem_cons.mp hm1 with h | hm1
    · subst h; simp [stepFn] at hn1
    · rcases List.mem_cons.mp hm1 with h | hnil
      · subst h; simp [stepFn] at hn1
      · cases hnil

/-! ## 3. Per-Function `minEntry` Isolation (Zero Bleed onto Sibling SCC Functions) -/

private def extCallerFn : Fn :=
  { name := "extCaller", as := [], rs := [i32], body := fun _ _ _ =>
      .call "ext" (as := []) (bs := [i32]) () fun r => .ret (.var r.1, ()) }

private def siblingLeafFn : Fn :=
  { name := "sibLeaf", as := [], rs := [i32], body := fun _ _ _ => .ret (.imm (7#32), ()) }

def minEntryMod : BudgetModule :=
  { fns := [
      { toFn := extCallerFn, maxFrame := 16, minEntry := 96 },
      { toFn := siblingLeafFn, maxFrame := 16 }
    ],
    externs := [{ name := "ext", as := [], rs := [i32] }] }

theorem minEntry_ok (m : Mem 64) :
    BudgetEnv.semScc minEntryMod envBot 16 "sibLeaf" [] [i32] () m
      (fun r _ => r.1 = 7#32) (fun _ _ _ _ => False) ∧
    ¬ BudgetEnv.semScc minEntryMod envBot 80 "extCaller" [] [i32] () m
      (fun _ _ => True) (fun _ _ _ _ => False) := by
  constructor
  · rw [BudgetEnv.semScc_fix]
    refine ⟨{ toFn := siblingLeafFn, maxFrame := 16 }, by simp [minEntryMod], rfl, rfl, rfl,
      by decide, by decide, ?_⟩
    simp [Func.wp, siblingLeafFn, vals, Arg.val]
  · intro h
    rw [BudgetEnv.semScc_fix] at h
    rcases h with ⟨bfn, hmem, hn, _, _, _, hmin, _⟩
    rcases List.mem_cons.mp hmem with h1 | hmem'
    · subst h1; exact absurd hmin (by decide)
    · rcases List.mem_cons.mp hmem' with h2 | hnil
      · subst h2; simp [siblingLeafFn] at hn
      · cases hnil

/-! ## 4. Non-Tail Well-Founded Equivalence (`lfp_eq_wfRec_of_noTail`) -/

theorem exCycle_strictNoTail : StrictNoTailModule exCycleMod := by
  intro bfn hmem _
  simp only [exCycleMod, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl <;> decide

theorem ex_cycle_wf (sb : Nat) :
    BudgetEnv.semScc exCycleMod envBot sb =
      wfSem exCycleMod (BudgetEnv.const envBot) sb :=
  semScc_eq_wfRec_of_noTail envBot exCycle_strictNoTail sb

def zeroLeafMod : BudgetModule :=
  { fns := [{ toFn := siblingLeafFn, maxFrame := 0 }] }

theorem zeroLeaf_strictNoTail : StrictNoTailModule zeroLeafMod := by
  intro bfn hmem ⟨xs, hnot⟩
  simp only [zeroLeafMod, List.mem_singleton] at hmem
  subst hmem
  exact absurd (Expr.NoCall.ret (rs := [i32]) (.imm (7#32), ())) hnot

theorem zeroLeaf_wf_ok (sb : Nat) :
    BudgetEnv.semScc zeroLeafMod envBot sb =
      wfSem zeroLeafMod (BudgetEnv.const envBot) sb :=
  semScc_eq_wfRec_of_noTail envBot zeroLeaf_strictNoTail sb

/-! ## 5. Legacy `ModuleOk` Embedding (`moduleOk_embeds_into_budget_semScc`) -/

def incFn : Fn :=
  { name := "inc", as := [i64], rs := [i64], body := fun _ _ xs =>
      .let_ (op2 (.add i64) (.var xs.1) (.imm (1#64))) fun y => .ret (.var y.1, ()) }

def twiceFn : Fn :=
  { name := "twice", as := [i64], rs := [i64], body := fun _ _ xs =>
      .call "inc" (as := [i64]) (bs := [i64]) (.var xs.1, ()) fun y =>
        .call "inc" (as := [i64]) (bs := [i64]) (.var y.1, ()) fun z =>
          .ret (.var z.1, ()) }

def legacyMod : Module :=
  { fns := [incFn, twiceFn] }

def legacySpec : Env := fun f as bs xs m Q _ =>
  ∃ (ha : as = [i64]) (hb : bs = [i64]),
    (f = "inc" ∧ (hb ▸ Q) ((ha ▸ xs).1 + 1#64, ()) m) ∨
    (f = "twice" ∧ (hb ▸ Q) ((ha ▸ xs).1 + 2#64, ()) m)

def legacyFrame (fn : Fn) : Nat :=
  if fn.name == "inc" then 16 else 32

private theorem legacyMod_checkAcyclic : legacyMod.checkAcyclic = true := by
  decide

private theorem incFn_wf : incFn.Wf := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  exact .let_ (.mk (.add i64) (.cons (.var List.mem_cons_self)
    (.cons (ArgRel.imm (t := i64) (1#64 : Val i64)) .nil)))
    fun _ _ => .ret (.cons (.var List.mem_cons_self) .nil)

private theorem twiceFn_wf : twiceFn.Wf := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  refine .call "inc" (.cons (.var List.mem_cons_self) .nil) fun _ _ => ?_
  refine .call "inc" (.cons (.var List.mem_cons_self) .nil) fun _ _ => ?_
  exact .ret (.cons (.var List.mem_cons_self) .nil)

private theorem legacyMod_ok : ModuleOk legacySpec legacyMod := by
  refine Module.moduleOk_of_checkAcyclic legacyMod_checkAcyclic ?_ ?_
  · intro fn hfn
    simp only [legacyMod, List.mem_cons, List.not_mem_nil, or_false] at hfn
    rcases hfn with rfl | rfl
    · exact incFn_wf
    · exact twiceFn_wf
  · intro fn hfn xs m Q X hΓ
    simp only [legacyMod, List.mem_cons, List.not_mem_nil, or_false] at hfn
    rcases hfn with rfl | rfl
    · dsimp [Func.wp, incFn, wp, Op.wp, op2, OpCode.wp, lift2, vals, Arg.val, legacySpec] at hΓ ⊢
      rcases hΓ with ⟨_, _, ⟨_, hQ⟩ | ⟨hne, _⟩⟩
      · exact hQ
      · simp at hne
    · dsimp [twiceFn, legacySpec] at hΓ
      rcases hΓ with ⟨_, _, ⟨hne, _⟩ | ⟨_, hQ⟩⟩
      · simp at hne
      · dsimp [Func.wp, twiceFn, wp]
        refine ⟨fun r m' => r = (xs.1 + 1#64, ()) ∧ m' = m, fun _ _ _ _ => False,
          ?_, ?_, fun _ _ _ _ h => False.elim h⟩
        · exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
        · rintro ⟨y, ⟨⟩⟩ m' ⟨hy, rfl⟩
          have hy' : y = xs.1 + 1#64 := (Prod.ext_iff.mp hy).1
          subst hy'
          refine ⟨fun r m'' => r = (xs.1 + 1#64 + 1#64, ()) ∧ m'' = m', fun _ _ _ _ => False,
            ?_, ?_, fun _ _ _ _ h => False.elim h⟩
          · exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
          · rintro ⟨z, ⟨⟩⟩ m'' ⟨hz, rfl⟩
            have hz' : z = xs.1 + 1#64 + 1#64 := (Prod.ext_iff.mp hz).1
            subst hz'
            have hadd : xs.1 + 1#64 + 1#64 = xs.1 + 2#64 := by
              apply BitVec.eq_of_toNat_eq
              simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
              omega
            dsimp [vals, Arg.val]
            rw [hadd]
            exact hQ

theorem legacy_embed_ok (x : BitVec 64) (m : Mem 64) :
    BudgetEnv.semScc (BudgetModule.ofModule legacyFrame legacyMod) legacySpec 48
      "twice" [i64] [i64] (x, ()) m (fun r _ => r.1 = x + 2#64) (fun _ _ _ _ => False) := by
  have hbound :
      BudgetModule.sumEntryBound (BudgetModule.ofModule legacyFrame legacyMod).fns = 48 := rfl
  have hle := moduleOk_embeds_into_budget_semScc_ofModule legacyMod_ok legacyFrame
  rw [hbound] at hle
  exact hle "twice" [i64] [i64] (x, ()) m _ _
    ⟨by simp [legacyMod, twiceFn, Fn.sig], rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩

/-! ## 6. Single-Shot Machine Bridge (`Target.FnSpec`) -/

theorem mach_bridge_ok (T : Target) (h : T.mach.Host) (nX : Nat)
    {M : BudgetModule} {Γext : BudgetEnv}
    (hlow : LowerOk M Γext (targetMachEnv T h nX) (2 ^ 64 - T.frame.raBytes))
    {sb sb' : Nat} (hsb : sb ≤ sb') (hsb' : sb' + T.frame.raBytes ≤ 2 ^ 64)
    (sym : Sym) (as bs : List Ty) :
    T.FnSpec h sym (BudgetEnv.semSccWith M Γext sb sym as bs) sb' nX :=
  Target.FnSpec.mono_stack T
    (budget_semScc_to_target_fnSpec T h nX hlow (by omega) sym as bs) hsb hsb'

/-! ## 7. Single-Line Axiom Audit (`[propext, Classical.choice, Quot.sound]`) -/

#print axioms LeanQbe.T.BudgetEnv.lfp_le
#print axioms LeanQbe.T.BudgetEnv.lfp_fix
#print axioms LeanQbe.T.BudgetEnv.lfp_wf
#print axioms LeanQbe.T.BudgetEnv.lfp_budget_mono
#print axioms LeanQbe.T.BudgetEnv.lfp_le_of_prefix_below
#print axioms LeanQbe.T.BudgetEnv.lfp_wf_mkSccOp
#print axioms LeanQbe.T.lfp_eq_wfRec_of_noTail
#print axioms LeanQbe.T.moduleOk_embeds_into_budget_semScc
#print axioms LeanQbe.T.semScc_le_mach_single_shot
#print axioms LeanQbe.T.budget_semScc_to_target_fnSpec
#print axioms lfp_laws_ok
#print axioms ex_cycle_ok
#print axioms ex_cycle_gap
#print axioms ex_cycle_tight
#print axioms minEntry_ok
#print axioms ex_cycle_wf
#print axioms zeroLeaf_wf_ok
#print axioms legacy_embed_ok
#print axioms mach_bridge_ok

end LeanQbeTest.T.LinkBudgetLfpTest
