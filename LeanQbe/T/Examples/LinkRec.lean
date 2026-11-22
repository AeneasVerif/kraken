module

public import LeanQbe.T.LinkRecLemmas
public import LeanQbe.T.Notation
public import LeanQbe.T.Logic.Rules
import LeanQbe.T.FlatLemmas

/-!
# Canonical Cyclic (`isEven`/`isOdd`) & Fuel-Guarded (`recSum`) Examples (`B1.1`)

* Mutually recursive `isEven`/`isOdd` (`evenOddRecMod`), `Func.Wf` (`t_wf_reify`), `checkCyclic`,
  `ModuleRecOk`, and measure-indexed `Env.sound_rec` proofs.
* Fuel-guarded recursive countdown `recSum` (`recSumMod`) with declared `"out_of_fuel"` `.exit`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LinkRec

open LeanQbe.T LeanQbe.T.Notation

/-- Mutually recursive `isEven(n)`: returns `1` if `n == 0`, else calls `isOdd(n - 1)`. -/
def isEven : Fn := tqbe $isEven(%n:l) -> l {
  %c =b ceql %n, 0
  jnz %c, {
    ret 1
  }, {
    %n' =l sub %n, 1
    %r =l call $isOdd(%n')
    ret %r
  }
}

/-- Mutually recursive `isOdd(n)`: returns `0` if `n == 0`, else calls `isEven(n - 1)`. -/
def isOdd : Fn := tqbe $isOdd(%n:l) -> l {
  %c =b ceql %n, 0
  jnz %c, {
    ret 0
  }, {
    %n' =l sub %n, 1
    %r =l call $isEven(%n')
    ret %r
  }
}

/-- Cyclic mutual-recursion module `{isEven, isOdd}`. -/
def evenOddRecMod : Module := ⟨[isEven, isOdd], [], []⟩

/-- Fuel-guarded recursive countdown `recSum(n, fuel)`:
exits to `"out_of_fuel"(n)` at `fuel == 0`, else returns `0` or `n + recSum(n-1, fuel-1)`. -/
def recSum : Fn := tqbe $recSum(%n:l, %fuel:l) -> l {
  %cf =b ceql %fuel, 0
  jnz %cf, {
    exit $out_of_fuel(%n)
  }, {
    %cn =b ceql %n, 0
    jnz %cn, {
      ret 0
    }, {
      %n' =l sub %n, 1
      %f' =l sub %fuel, 1
      %r =l call $recSum(%n', %f')
      %s =l add %n, %r
      ret %s
    }
  }
}

/-- Fuel-guarded cyclic module `{recSum}` with declared exit `"out_of_fuel"`. -/
def recSumMod : Module := ⟨[recSum], [], ["out_of_fuel"]⟩

theorem isEven_wf : Fn.Wf isEven := by t_wf_reify
theorem isOdd_wf : Fn.Wf isOdd := by t_wf_reify
theorem recSum_wf : Fn.Wf recSum := by t_wf_reify

theorem evenOddRecMod_checkCyclic : checkCyclic evenOddRecMod = true := by t_kernel_rfl
theorem recSumMod_checkCyclic : checkCyclic recSumMod = true := by t_kernel_rfl

/-- Mathematical return value of `isEven(n)`. -/
def isEvenVal (n : BitVec 64) : BitVec 64 :=
  if n.toNat % 2 = 0 then 1#64 else 0#64

/-- Mathematical return value of `isOdd(n)`. -/
def isOddVal (n : BitVec 64) : BitVec 64 :=
  if n.toNat % 2 = 1 then 1#64 else 0#64

/-- Measure-indexed contract for `isEven`. -/
def isEvenSpec (k : Nat) : Spec [i64] [i64] := fun (n, ()) m Q _ =>
  n.toNat ≤ k ∧ Q (isEvenVal n, ()) m

/-- Measure-indexed contract for `isOdd`. -/
def isOddSpec (k : Nat) : Spec [i64] [i64] := fun (n, ()) m Q _ =>
  n.toNat ≤ k ∧ Q (isOddVal n, ()) m

/-- Measure-indexed environment for `evenOddRecMod`. -/
def evenOddRecEnv (k : Nat) : Env
  | "isEven", [.bits 64], [.bits 64] => isEvenSpec k
  | "isOdd", [.bits 64], [.bits 64] => isOddSpec k
  | _, _, _ => fun _ _ _ _ => False

private theorem bv64_sub_one_toNat {n : BitVec 64} (hn : n.toNat ≠ 0) :
    (n - 1#64).toNat = n.toNat - 1 := by
  have hlt : n.toNat < 2 ^ 64 := n.isLt
  rw [BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  omega

theorem isEven_step (Γ : Env) (k : Nat)
    (hodd : ∀ k' < k, ∀ args m Q X, isOddSpec k' args m Q X → Γ "isOdd" [i64] [i64] args m Q X) :
    ∀ args m Q X, isEvenSpec k args m Q X → Func.wp Γ isEven.body args m Q X := by
  rintro ⟨n, ⟨⟩⟩ m Q X ⟨hn, hQ⟩
  dsimp only [Func.wp, isEven]; wp_unfold
  constructor
  · intro h0
    subst h0; exact hQ
  · intro hne
    have hnz : n.toNat ≠ 0 := fun hz => hne (BitVec.eq_of_toNat_eq hz)
    have hk1 : k - 1 < k := by omega
    refine wp_call_of_spec _ _ (hodd (k - 1) hk1 (n - 1#64, ()) m Q X ⟨?_, ?_⟩)
    · rw [bv64_sub_one_toNat hnz]; omega
    · have hsub := bv64_sub_one_toNat hnz
      have heq : isOddVal (n - 1#64) = isEvenVal n := by
        simp only [isOddVal, isEvenVal, hsub]
        have : (n.toNat - 1) % 2 = 1 ↔ n.toNat % 2 = 0 := by omega
        simp [this]
      rw [heq]; exact hQ

theorem isOdd_step (Γ : Env) (k : Nat)
    (heven : ∀ k' < k, ∀ args m Q X, isEvenSpec k' args m Q X → Γ "isEven" [i64] [i64] args m Q X) :
    ∀ args m Q X, isOddSpec k args m Q X → Func.wp Γ isOdd.body args m Q X := by
  rintro ⟨n, ⟨⟩⟩ m Q X ⟨hn, hQ⟩
  dsimp only [Func.wp, isOdd]; wp_unfold
  constructor
  · intro h0
    subst h0; exact hQ
  · intro hne
    have hnz : n.toNat ≠ 0 := fun hz => hne (BitVec.eq_of_toNat_eq hz)
    have hk1 : k - 1 < k := by omega
    refine wp_call_of_spec _ _ (heven (k - 1) hk1 (n - 1#64, ()) m Q X ⟨?_, ?_⟩)
    · rw [bv64_sub_one_toNat hnz]; omega
    · have hsub := bv64_sub_one_toNat hnz
      have heq : isEvenVal (n - 1#64) = isOddVal n := by
        simp only [isEvenVal, isOddVal, hsub]
        have : (n.toNat - 1) % 2 = 0 ↔ n.toNat % 2 = 1 := by omega
        simp [this]
      rw [heq]; exact hQ

theorem evenOddRecMod_wp_step :
    ∀ k : Nat, ∀ fn ∈ evenOddRecMod.fns, ∀ xs m Q X,
      evenOddRecEnv k fn.name fn.as fn.rs xs m Q X →
      Func.wp (Env.stepRec (evenOddRecMod.fns.map Fn.sig)
        (evenOddRecMod.externs.map Extern.sig) evenOddRecEnv (fun _ _ _ _ _ _ _ => False) k)
        fn.body xs m Q X := by
  intro k fn hfn xs m Q X hspec
  simp only [evenOddRecMod, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl
  · refine isEven_step _ k (fun k' hk' args' m' Q' X' hg => ?_) xs m Q X hspec
    exact Or.inl ⟨by simp [evenOddRecMod, isOdd, Fn.sig], k', hk', hg⟩
  · refine isOdd_step _ k (fun k' hk' args' m' Q' X' hg => ?_) xs m Q X hspec
    exact Or.inl ⟨by simp [evenOddRecMod, isEven, Fn.sig], k', hk', hg⟩

theorem evenOddRecMod_moduleRecOk :
    ModuleRecOk evenOddRecEnv (fun _ _ _ _ _ _ _ => False) evenOddRecMod := by
  obtain ⟨hnd, hok⟩ := callsOkRec_of_checkCyclic evenOddRecMod_checkCyclic (by
    intro fn hfn
    simp only [evenOddRecMod, List.mem_cons, List.not_mem_nil, or_false] at hfn
    rcases hfn with rfl | rfl <;> first | exact isEven_wf | exact isOdd_wf)
  exact ⟨hnd, fun fn hfn =>
    ⟨(hok fn hfn).1, (hok fn hfn).2, fun k => evenOddRecMod_wp_step k fn hfn⟩⟩

/-- Outcome of `recSum(n, f)`: `.inl sum` on normal return, `.inr rem` on `"out_of_fuel"`. -/
def recSumOutcome (n : BitVec 64) : Nat → Sum (BitVec 64) (BitVec 64)
  | 0 => .inr n
  | f + 1 =>
    if n == 0#64 then .inl 0#64
    else match recSumOutcome (n - 1#64) f with
      | .inl s => .inl (n + s)
      | .inr rem => .inr rem

/-- Measure-indexed contract for `recSum`. -/
def recSumSpec (k : Nat) : Spec [i64, i64] [i64] := fun (n, f, ()) m Q X =>
  f.toNat ≤ k ∧
    match recSumOutcome n f.toNat with
    | .inl s => Q (s, ()) m
    | .inr rem => X "out_of_fuel" [i64] (rem, ()) m

/-- Measure-indexed environment for `recSumMod`. -/
def recSumRecEnv (k : Nat) : Env
  | "recSum", [.bits 64, .bits 64], [.bits 64] => recSumSpec k
  | _, _, _ => fun _ _ _ _ => False

theorem recSum_step (Γ : Env) (k : Nat)
    (hrec : ∀ k' < k, ∀ args m Q X, recSumSpec k' args m Q X →
      Γ "recSum" [i64, i64] [i64] args m Q X) :
    ∀ args m Q X, recSumSpec k args m Q X → Func.wp Γ recSum.body args m Q X := by
  rintro ⟨n, f, ⟨⟩⟩ m Q X ⟨hf, hout⟩
  dsimp only [Func.wp, recSum]; wp_unfold
  constructor
  · intro hf0
    subst hf0; exact hout
  · intro hfne
    have hfnz : f.toNat ≠ 0 := fun hz => hfne (BitVec.eq_of_toNat_eq hz)
    obtain ⟨f', hf'⟩ := Nat.exists_eq_succ_of_ne_zero hfnz
    rw [hf', recSumOutcome] at hout
    constructor
    · intro hn0
      subst hn0; exact hout
    · intro hnne
      have hbeq : (n == 0#64) = false := beq_false_of_ne hnne
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hout
      have hk1 : k - 1 < k := by omega
      have hfsub : (f - 1#64).toNat = f' := by rw [bv64_sub_one_toNat hfnz, hf']; omega
      refine wp_call_of_spec _ _ (hrec (k - 1) hk1 (n - 1#64, f - 1#64, ()) m
        (fun r m' => Q (n + r.1, ()) m') X ⟨?_, ?_⟩)
      · rw [hfsub]; omega
      · rw [hfsub]
        cases ho : recSumOutcome (n - 1#64) f' with
        | inl s => rw [ho] at hout; exact hout
        | inr rem => rw [ho] at hout; exact hout

theorem recSumMod_wp_step :
    ∀ k : Nat, ∀ fn ∈ recSumMod.fns, ∀ xs m Q X,
      recSumRecEnv k fn.name fn.as fn.rs xs m Q X →
      Func.wp (Env.stepRec (recSumMod.fns.map Fn.sig)
        (recSumMod.externs.map Extern.sig) recSumRecEnv (fun _ _ _ _ _ _ _ => False) k)
        fn.body xs m Q X := by
  intro k fn hfn xs m Q X hspec
  simp only [recSumMod, List.mem_singleton] at hfn
  subst hfn
  refine recSum_step _ k (fun k' hk' args' m' Q' X' hg => ?_) xs m Q X hspec
  exact Or.inl ⟨by simp [recSumMod, recSum, Fn.sig], k', hk', hg⟩

theorem recSumMod_moduleRecOk :
    ModuleRecOk recSumRecEnv (fun _ _ _ _ _ _ _ => False) recSumMod := by
  obtain ⟨hnd, hok⟩ := callsOkRec_of_checkCyclic recSumMod_checkCyclic (by
    intro fn hfn
    simp only [recSumMod, List.mem_singleton] at hfn
    subst hfn; exact recSum_wf)
  exact ⟨hnd, fun fn hfn => ⟨(hok fn hfn).1, (hok fn hfn).2, fun k => recSumMod_wp_step k fn hfn⟩⟩

end LeanQbe.T.LinkRec
