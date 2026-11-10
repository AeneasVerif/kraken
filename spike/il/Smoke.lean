module

public import LeanQbe

/-!
# Smoke tests of the IR (C1): `wp` proofs, `Wf` by `wf_tac`, calls and exits.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.Smoke

/-! ## The step-1 tracer function: `x = add a b; storel x, p; ret x` -/

def tracer : Func := fun _ _ =>
  .param fun a => .param fun b => .param fun p =>
  .let_ (.bin .l .add (.var a) (.var b)) fun x =>
  .store .l (.var x) (.var p) <|
  .ret [.var x]

theorem tracer_wf : Func.Wf tracer := by wf_tac

theorem tracer_correct (Γ : Env) (a b p : Val) (m : Mem 64) (h : storeOk m .l p) :
    Func.spec Γ tracer [a, b, p] m
      (fun rs m' => rs = [a + b] ∧ m' = storeMem m .l p (a + b)) (fun _ _ _ => False) := by
  simp [Func.spec, tracer, wp, Op.wp, h]

/-! ## even/odd: two mutually recursive join points, operands with immediates -/

def evenOdd : Func := fun _ _ =>
  .param fun n =>
  .label fun even => .label fun odd =>
  .block (.param fun x =>
      .let_ (.cmp .l .ult (.imm 0) (.var x)) fun c =>
      .jnz (.var c) (.let_ (.bin .l .sub (.var x) (.imm 1)) fun x' => .jump odd [.var x'])
        (.ret [.imm 1])) <|
  .block (.param fun x =>
      .let_ (.cmp .l .ult (.imm 0) (.var x)) fun c =>
      .jnz (.var c) (.let_ (.bin .l .sub (.var x) (.imm 1)) fun x' => .jump even [.var x'])
        (.ret [.imm 0])) <|
  .jump even [.var n]

theorem evenOdd_wf : Func.Wf evenOdd := by wf_tac

def parity (k : Nat) : Val := if k % 2 = 0 then 1 else 0

theorem truthy_boolVal (b : Bool) : Truthy (boolVal b) ↔ b = true := by
  cases b <;> decide

theorem evenOdd_correct (Γ : Env) (n : Val) (m : Mem 64) :
    Func.spec Γ evenOdd [n] m (fun r m' => r = [parity n.toNat] ∧ m' = m) (fun _ _ _ => False) := by
  simp only [Func.spec, evenOdd, wp, Op.wp, Op.eval, BinOp.eval, CmpOp.eval, Arg.val, List.map,
    closed_param, forall_args_nil, List.nil_append, List.cons_append, true_and, Option.some.injEq,
    exists_eq_left', truthy_boolVal]
  intro even odd hEven hOdd
  suffices h : ∀ k : Nat, k < 2 ^ 64 →
      (n.toNat % 2 = k % 2 → even [BitVec.ofNat 64 k] m) ∧
      (n.toNat % 2 ≠ k % 2 → odd [BitVec.ofNat 64 k] m) by
    have := (h n.toNat (by omega)).1 rfl
    simpa using this
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun hk => hEven _ _ ?_, fun hk => hOdd _ _ ?_⟩
    · have : n.toNat % 2 = 0 := by omega
      simp [parity, this]
    · have : ¬ n.toNat % 2 = 0 := by omega
      simp [parity, this]
  | succ k ih =>
    intro hk
    have ih := ih (by omega)
    have hsub : BitVec.ofNat 64 (k + 1) - (1 : Val) = BitVec.ofNat 64 k := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have hpos : (0 : Val).ult (BitVec.ofNat 64 (k + 1)) = true := by
      simp [BitVec.ult, BitVec.toNat_ofNat]; omega
    refine ⟨fun h => hEven _ _ ?_, fun h => hOdd _ _ ?_⟩
    · simp only [hpos, hsub]
      exact ⟨fun _ => ih.2 (by omega), fun h0 => absurd trivial h0⟩
    · simp only [hpos, hsub]
      exact ⟨fun _ => ih.1 (by omega), fun h0 => absurd trivial h0⟩

/-! ## Calls and exits (decision D5): `r = call $g(a); jnz r, ret r, exit $abort(a)` -/

def caller : Func := fun _ _ =>
  .param fun a =>
  .call "g" [.var a] <| .param fun r =>
  .jnz (.var r) (.ret [.var r]) (.exit "abort" [.var a])

theorem caller_wf : Func.Wf caller := by wf_tac

/-- `g` returns its argument plus one, without touching memory. External specs must be strict
(`∃ a, args = [a] ∧ …`): a spec that holds vacuously at a wrong arity would let a caller derive anything. -/
def gSpec : Spec := fun args m Q _ => ∃ a, args = [a] ∧ Q [a + 1] m

theorem caller_correct (Γ : Env) (hg : Γ "g" = gSpec) (a : Val) (m : Mem 64) :
    Func.spec Γ caller [a] m (fun r m' => r = [a + 1] ∧ m' = m)
      (fun f xs m' => f = "abort" ∧ xs = [a] ∧ m' = m ∧ lo32 (a + 1) = 0) := by
  simp only [Func.spec, caller, wp_param_cons]
  refine wp_call_of_spec ?_
  rw [hg]
  refine ⟨a, rfl, ?_⟩
  simp [wp, Truthy]

/-! ## Non-vacuity of `wp` (from the review): a self-loop satisfies no postcondition -/

def spin : Func := fun _ _ => .label fun l => .block (.jump l []) (.jump l [])

theorem spin_false (Γ : Env) (Q : Post) (X : XPost) (m : Mem 64) :
    ¬ Func.spec Γ spin [] m Q X := by
  intro h
  simp only [Func.spec, spin, wp, List.nil_append, List.map, true_and] at h
  exact h (fun _ _ => False) (fun _ _ hf => hf.2) |>.elim

end LeanQbe.Smoke
