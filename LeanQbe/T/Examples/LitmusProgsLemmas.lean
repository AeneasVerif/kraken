module

public import LeanQbe.T.Examples.LitmusProgs
public import LeanQbe.T.Logic.Rules
public import LeanQbe.T.FlatLemmas

/-!
# Well-Formedness, Source Contracts, and `ModuleOk` for `LeanQbe.T.Examples.Litmus`

Proves `*_wf` (`t_wf_reify`), exact `Spec` source contracts (`*_spec`), `*_moduleOk`
(`Module.moduleOk_of_checkAcyclic`), and concrete memory non-vacuity (`tracer_nonvacuous`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Litmus

open Std.ExtHashMap
open LeanQbe.T

/-! ## 1. Well-formedness and acyclicity -/

theorem tracer_wf  : Fn.Wf tracer  := by t_wf_reify
theorem ifelse_wf  : Fn.Wf ifelse  := by t_wf_reify
theorem sumto_wf   : Fn.Wf sumto   := by t_wf_reify
theorem evenodd_wf : Fn.Wf evenodd := by t_wf_reify
theorem nested_wf  : Fn.Wf nested  := by t_wf_reify
theorem swap_wf    : Fn.Wf swap    := by t_wf_reify
theorem inc_wf     : Fn.Wf inc     := by t_wf_reify
theorem callinc_wf : Fn.Wf callinc := by t_wf_reify
theorem check_wf   : Fn.Wf check   := by t_wf_reify
theorem twice_wf   : Fn.Wf twice   := by t_wf_reify
theorem spill10_wf : Fn.Wf spill10 := by t_wf_reify
theorem sumcall_wf : Fn.Wf sumcall := by t_wf_reify

theorem tracerModule_acyclic  : tracerModule.checkAcyclic  = true := by t_kernel_rfl
theorem ifelseModule_acyclic  : ifelseModule.checkAcyclic  = true := by t_kernel_rfl
theorem sumtoModule_acyclic   : sumtoModule.checkAcyclic   = true := by t_kernel_rfl
theorem evenoddModule_acyclic : evenoddModule.checkAcyclic = true := by t_kernel_rfl
theorem nestedModule_acyclic  : nestedModule.checkAcyclic  = true := by t_kernel_rfl
theorem swapModule_acyclic    : swapModule.checkAcyclic    = true := by t_kernel_rfl
theorem spill10Module_acyclic : spill10Module.checkAcyclic = true := by t_kernel_rfl
theorem callincModule_acyclic : callincModule.checkAcyclic = true := by t_kernel_rfl
theorem twiceModule_acyclic   : twiceModule.checkAcyclic   = true := by t_kernel_rfl
theorem sumcallModule_acyclic : sumcallModule.checkAcyclic = true := by t_kernel_rfl

/-! ## 2. Helpers and Source Contracts -/

/-- Low 32 bits of a 64-bit word are nonzero (`cnew (trunc 64 32 _) 0`). -/
def Truthy (c : BitVec 64) : Prop := c.setWidth 32 ≠ 0#32

/-- `1 + 2 + … + k` in 64-bit arithmetic. -/
def tri : Nat → BitVec 64
  | 0 => 0
  | k + 1 => tri k + BitVec.ofNat 64 (k + 1)

private theorem tri_zero : tri 0 = 0 := rfl
private theorem tri_succ (k : Nat) : tri (k + 1) = tri k + BitVec.ofNat 64 (k + 1) := rfl

private theorem truthy_ofNat_succ {k : Nat} (hk : k + 1 < 2 ^ 32) :
    Truthy (BitVec.ofNat 64 (k + 1)) := by
  simp only [Truthy, ne_eq]
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64), Nat.mod_eq_of_lt hk] at this
  omega

private theorem truthy_zero : ¬ Truthy 0#64 := by simp [Truthy]

private theorem bv64_ofNat_succ_sub_one (k : Nat) :
    BitVec.ofNat 64 (k + 1) - 1 = BitVec.ofNat 64 k := by grind

def tracerContract : Spec [i64, i64, i64] [i64] := fun (a, b, p, ()) m Q _ =>
  ∃ v0 R, (cell64 p v0 ⋆ R) m ∧ ∀ m', (cell64 p (a + b) ⋆ R) m' → Q (a + b, ()) m'

def ifelseContract : Spec [i64, i64] [i64] := fun (a, b, ()) m Q _ =>
  (Truthy a → Q (a + b, ()) m) ∧ (¬ Truthy a → Q (b - a, ()) m)

def sumtoContract : Spec [i64] [i64] := fun (n, ()) m Q _ =>
  n.toNat < 2 ^ 32 ∧ Q (tri n.toNat, ()) m

def evenoddContract : Spec [i64] [i64] := fun (n, ()) m Q _ =>
  n.toNat < 2 ^ 32 ∧ Q (if n.toNat % 2 = 0 then 1 else 0, ()) m

def nestedContract : Spec [i64, i64, i64] [i64] := fun (n, m, k, ()) mem Q _ =>
  n.toNat < 2 ^ 32 ∧ m.toNat < 2 ^ 32 ∧ Q (m * (n * k + tri n.toNat), ()) mem

def swapContract : Spec [i64, i64, i64] [i64] := fun (n, a, b, ()) m Q _ =>
  n.toNat < 2 ^ 32 ∧ Q (if n.toNat % 2 = 0 then a else b, ()) m

def incContract : Spec [i64] [i64] := fun (a, ()) m Q _ => Q (a + 1, ()) m

def callincContract : Spec [i64, i64] [i64] := fun (a, b, ()) m Q _ => Q (a + 1 + b, ()) m

def checkContract : Spec [i64] [i64] := fun (a, ()) m Q X =>
  (Truthy a → Q (a, ()) m) ∧ (¬ Truthy a → X "fail" [i64] (a, ()) m)

def twiceContract : Spec [i64, i64] [i64] := fun (a, b, ()) m Q X =>
  (Truthy a → Truthy b → Q (a + b, ()) m) ∧
  (¬ Truthy a → X "fail" [i64] (a, ()) m) ∧
  (Truthy a → ¬ Truthy b → X "fail" [i64] (b, ()) m)

/-- Expected return value of `spill10(a, b)`. -/
def spill10Val (a b : BitVec 64) : BitVec 64 :=
  (a + 1) ^^^ (a + 2) ^^^ (a + 3) ^^^ (a + 4) ^^^ (a + 5) ^^^
  (a + 6) ^^^ (a + 7) ^^^ (a + 8) ^^^ (a + 9) ^^^ (a + 10) ^^^ b

def spill10Contract : Spec [i64, i64] [i64] := fun (a, b, ()) m Q _ => Q (spill10Val a b, ()) m

def sumcallContract : Spec [i64, i64] [i64] := fun (n, b, ()) m Q _ =>
  n.toNat < 2 ^ 32 ∧ Q (tri n.toNat + n + b, ()) m

/-! ## 3. Per-Function Source Correctness Proofs -/

theorem tracer_spec (Γ : Env) :
    ∀ args m Q X, tracerContract args m Q X → Func.spec Γ tracer.body args m Q X := by
  rintro ⟨a, b, p, ⟨⟩⟩ m Q X ⟨v0, R, hm, hQ⟩
  dsimp only [Func.spec, Func.wp, tracer]; wp_unfold
  have ⟨hok, hm'⟩ := store_cell64 (a + b) hm
  exact ⟨hok, hQ _ hm'⟩

theorem ifelse_spec (Γ : Env) :
    ∀ args m Q X, ifelseContract args m Q X → Func.spec Γ ifelse.body args m Q X := by
  rintro ⟨a, b, ⟨⟩⟩ m Q X ⟨ht, hf⟩
  dsimp only [Func.spec, Func.wp, ifelse]; wp_unfold
  exact ⟨ht, fun h => hf (by simp [Truthy, h])⟩

theorem sumto_spec (Γ : Env) :
    ∀ args m Q X, sumtoContract args m Q X → Func.spec Γ sumto.body args m Q X := by
  rintro ⟨n, ⟨⟩⟩ m Q X ⟨hn, hQ⟩
  dsimp only [Func.spec, Func.wp, sumto]
  refine wp_loop_group
    (fun k xs m' => k ≤ n.toNat ∧ xs.1 = BitVec.ofNat 64 k ∧ xs.2.1 + tri k = tri n.toNat ∧ m' = m)
    (fun J k ⟨i, s, ⟨⟩⟩ m' hlt ⟨hk, hi, hs, hm⟩ => ?_) (fun J hJ => ?_)
  · dsimp only at hi hs hm; subst hi; rw [hm]
    dsimp only [Blocks.get_here]; wp_unfold
    cases k with
    | zero =>
      refine ⟨fun h => absurd h truthy_zero, fun _ => ?_⟩
      rw [tri_zero] at hs; have hs' : s = tri n.toNat := by grind
      rw [hs']; exact hQ
    | succ k' =>
      have ht := truthy_ofNat_succ (k := k') (by omega)
      refine ⟨fun _ => ?_, fun h => absurd ht (by simp [Truthy, h])⟩
      rw [bv64_ofNat_succ_sub_one]
      refine hlt k' _ m (by omega) ⟨by omega, rfl, ?_, rfl⟩
      dsimp only; rw [← hs, tri_succ]; ac_rfl
  · wp_unfold
    exact hJ n.toNat (n, 0, ()) m ⟨Nat.le_refl _, by simp, by dsimp only; grind, rfl⟩

theorem evenodd_spec (Γ : Env) :
    ∀ args m Q X, evenoddContract args m Q X → Func.spec Γ evenodd.body args m Q X := by
  rintro ⟨n, ⟨⟩⟩ m Q X ⟨hn, hQ⟩
  dsimp only [Func.spec, Func.wp, evenodd, wp]
  intro ⟨J_even, J_odd, ⟨⟩⟩ hc
  simp only [Closed, and_true] at hc; obtain ⟨hEven, hOdd⟩ := hc
  suffices h : ∀ k : Nat, k ≤ n.toNat →
      (n.toNat % 2 = k % 2 → J_even (BitVec.ofNat 64 k, ()) m) ∧
      (n.toNat % 2 ≠ k % 2 → J_odd (BitVec.ofNat 64 k, ()) m) by
    have hof : BitVec.ofNat 64 n.toNat = n := by simp
    exact hof ▸ (h n.toNat (Nat.le_refl _)).1 rfl
  intro k hk
  induction k with
  | zero =>
    refine ⟨fun heq => hEven _ _ ?_, fun hne => hOdd _ _ ?_⟩ <;> wp_unfold
    · refine ⟨fun h => absurd h truthy_zero, fun _ => ?_⟩
      have hpar : n.toNat % 2 = 0 := by omega
      simpa [hpar] using hQ
    · refine ⟨fun h => absurd h truthy_zero, fun _ => ?_⟩
      have hpar : n.toNat % 2 ≠ 0 := by omega
      simpa [hpar] using hQ
  | succ k' ih =>
    obtain ⟨ihE, ihO⟩ := ih (by omega)
    have ht := truthy_ofNat_succ (k := k') (by omega)
    refine ⟨fun heq => hEven _ _ ?_, fun hne => hOdd _ _ ?_⟩ <;> wp_unfold <;>
      refine ⟨fun _ => ?_, fun h => absurd ht (by simp [Truthy, h])⟩ <;>
      rw [bv64_ofNat_succ_sub_one]
    · exact ihO (by omega)
    · exact ihE (by omega)

theorem nested_spec (Γ : Env) :
    ∀ args m Q X, nestedContract args m Q X → Func.spec Γ nested.body args m Q X := by
  rintro ⟨n, m, k, ⟨⟩⟩ mem Q X ⟨hn, hm, hQ⟩
  dsimp only [Func.spec, Func.wp, nested]
  refine wp_loop_group
    (fun oi xs mem' => oi ≤ n.toNat ∧ xs.1 = BitVec.ofNat 64 oi ∧
      xs.2.1 + m * (xs.1 * k + tri oi) = m * (n * k + tri n.toNat) ∧ mem' = mem)
    (fun Jo oi ⟨i, t, ⟨⟩⟩ mem' hltO ⟨hoi, hi, ht, hmem⟩ => ?_) (fun Jo hJo => ?_)
  · dsimp only at hi ht hmem; subst hi; rw [hmem]
    dsimp only [Blocks.get_here]; wp_unfold
    cases oi with
    | zero =>
      refine ⟨fun h => absurd h truthy_zero, fun _ => ?_⟩
      rw [tri_zero] at ht; have ht' : t = m * (n * k + tri n.toNat) := by grind
      rw [ht']; exact hQ
    | succ oi' =>
      have hti := truthy_ofNat_succ (k := oi') (by omega)
      refine ⟨fun _ => ?_, fun h => absurd hti (by simp [Truthy, h])⟩
      refine wp_loop_group
        (fun oj xs mem' => oj ≤ m.toNat ∧ xs.1 = BitVec.ofNat 64 oj ∧
          xs.2.1 + xs.1 * (k + BitVec.ofNat 64 (oi' + 1)) =
            t + m * (k + BitVec.ofNat 64 (oi' + 1)) ∧ mem' = mem)
        (fun Ji oj ⟨j, u, ⟨⟩⟩ mem' hltI ⟨hoj, hj, hu, hmem⟩ => ?_) (fun Ji hJi => ?_)
      · dsimp only at hj hu hmem; subst hj; rw [hmem]
        dsimp only [Blocks.get_here]; wp_unfold
        cases oj with
        | zero =>
          refine ⟨fun h => absurd h truthy_zero, fun _ => ?_⟩
          rw [bv64_ofNat_succ_sub_one]
          refine hltO oi' _ mem (by omega) ⟨by omega, rfl, ?_, rfl⟩
          dsimp only
          have h0 : u = t + m * (k + BitVec.ofNat 64 (oi' + 1)) := by grind
          have h1 : BitVec.ofNat 64 (oi' + 1) = BitVec.ofNat 64 oi' + 1 := by grind
          rw [h0, ← ht, h1, tri_succ]; grind
        | succ oj' =>
          have htj := truthy_ofNat_succ (k := oj') (by omega)
          refine ⟨fun _ => ?_, fun h => absurd htj (by simp [Truthy, h])⟩
          rw [bv64_ofNat_succ_sub_one]
          refine hltI oj' _ mem (by omega) ⟨by omega, rfl, ?_, rfl⟩
          dsimp only
          have h1 : BitVec.ofNat 64 (oj' + 1) = BitVec.ofNat 64 oj' + 1 := by grind
          rw [← hu, h1]; grind
      · wp_unfold; exact hJi m.toNat (m, t, ()) mem ⟨Nat.le_refl _, by simp, rfl, rfl⟩
  · wp_unfold
    exact hJo n.toNat (n, 0, ()) mem ⟨Nat.le_refl _, by simp, by dsimp only; grind, rfl⟩

theorem swap_spec (Γ : Env) :
    ∀ args m Q X, swapContract args m Q X → Func.spec Γ swap.body args m Q X := by
  rintro ⟨n, a, b, ⟨⟩⟩ m Q X ⟨hn, hQ⟩
  dsimp only [Func.spec, Func.wp, swap]
  refine wp_loop_group
    (fun k xs m' => k ≤ n.toNat ∧ xs.1 = BitVec.ofNat 64 k ∧
      (n.toNat % 2 = k % 2 → xs.2.1 = a ∧ xs.2.2.1 = b) ∧
      (n.toNat % 2 ≠ k % 2 → xs.2.1 = b ∧ xs.2.2.1 = a) ∧ m' = m)
    (fun J k ⟨i, x, y, ⟨⟩⟩ m' hlt ⟨hk, hi, heq, hne, hm⟩ => ?_) (fun J hJ => ?_)
  · dsimp only at hi heq hne hm; subst hi; rw [hm]
    dsimp only [Blocks.get_here]; wp_unfold
    cases k with
    | zero =>
      refine ⟨fun h => absurd h truthy_zero, fun _ => ?_⟩
      by_cases hpar : n.toNat % 2 = 0
      · have hxy := heq (by omega); simpa [hpar, hxy.1] using hQ
      · have hxy := hne (by omega); simpa [hpar, hxy.1] using hQ
    | succ k' =>
      have ht := truthy_ofNat_succ (k := k') (by omega)
      refine ⟨fun _ => ?_, fun h => absurd ht (by simp [Truthy, h])⟩
      rw [bv64_ofNat_succ_sub_one]
      exact hlt k' _ m (by omega)
        ⟨by omega, rfl, fun h => (hne (by omega)).symm, fun h => (heq (by omega)).symm, rfl⟩
  · wp_unfold
    exact hJ n.toNat (n, a, b, ()) m
      ⟨Nat.le_refl _, by simp, fun _ => ⟨rfl, rfl⟩, fun h => absurd rfl h, rfl⟩

theorem inc_spec (Γ : Env) :
    ∀ args m Q X, incContract args m Q X → Func.spec Γ inc.body args m Q X := by
  rintro ⟨a, ⟨⟩⟩ m Q X hQ
  dsimp only [Func.spec, Func.wp, inc]; wp_unfold; exact hQ

theorem callinc_spec (Γ : Env)
    (hinc : ∀ args m Q X, incContract args m Q X → Γ "inc" [i64] [i64] args m Q X) :
    ∀ args m Q X, callincContract args m Q X → Func.spec Γ callinc.body args m Q X := by
  rintro ⟨a, b, ⟨⟩⟩ m Q X hQ
  dsimp only [Func.spec, Func.wp, callinc]
  refine wp_call_of_spec _ _ (hinc _ m _ _ ?_)
  dsimp only [incContract, vals, Arg.val_var]; wp_unfold; exact hQ

theorem check_spec (Γ : Env) :
    ∀ args m Q X, checkContract args m Q X → Func.spec Γ check.body args m Q X := by
  rintro ⟨a, ⟨⟩⟩ m Q X ⟨hQ, hX⟩
  dsimp only [Func.spec, Func.wp, check]; wp_unfold
  exact ⟨hQ, fun h => hX (by simp [Truthy, h])⟩

theorem twice_spec (Γ : Env)
    (hcheck : ∀ args m Q X, checkContract args m Q X → Γ "check" [i64] [i64] args m Q X) :
    ∀ args m Q X, twiceContract args m Q X → Func.spec Γ twice.body args m Q X := by
  rintro ⟨a, b, ⟨⟩⟩ m Q X ⟨hQ, hXa, hXb⟩
  dsimp only [Func.spec, Func.wp, twice]
  refine wp_call_of_spec _ _ (hcheck _ m _ _ ⟨fun ha => ?_, hXa⟩)
  refine wp_call_of_spec _ _ (hcheck _ m _ _ ⟨fun hb => ?_, hXb ha⟩)
  wp_unfold; exact hQ ha hb

theorem spill10_spec (Γ : Env) :
    ∀ args m Q X, spill10Contract args m Q X → Func.spec Γ spill10.body args m Q X := by
  rintro ⟨a, b, ⟨⟩⟩ m Q X hQ
  dsimp only [Func.spec, Func.wp, spill10]; wp_unfold
  dsimp only [spill10Contract] at hQ
  simpa [spill10Val] using hQ

theorem sumcall_spec (Γ : Env)
    (hinc : ∀ args m Q X, incContract args m Q X → Γ "inc" [i64] [i64] args m Q X) :
    ∀ args m Q X, sumcallContract args m Q X → Func.spec Γ sumcall.body args m Q X := by
  rintro ⟨n, b, ⟨⟩⟩ m Q X ⟨hn, hQ⟩
  dsimp only [Func.spec, Func.wp, sumcall]
  refine wp_loop_group
    (fun k xs m' => k ≤ n.toNat ∧ xs.1 = BitVec.ofNat 64 k ∧
      xs.2.1 + tri k + xs.1 = tri n.toNat + n ∧ m' = m)
    (fun J k ⟨i, s, ⟨⟩⟩ m' hlt ⟨hk, hi, hs, hm⟩ => ?_) (fun J hJ => ?_)
  · dsimp only at hi hs hm; subst hi; rw [hm]
    dsimp only [Blocks.get_here]; wp_unfold
    cases k with
    | zero =>
      refine ⟨fun h => absurd h truthy_zero, fun _ => ?_⟩
      rw [tri_zero] at hs; have hs' : s = tri n.toNat + n := by grind
      rw [hs']; exact hQ
    | succ k' =>
      have ht := truthy_ofNat_succ (k := k') (by omega)
      refine ⟨fun _ => ?_, fun h => absurd ht (by simp [Truthy, h])⟩
      refine wp_call_of_spec _ _ (hinc (BitVec.ofNat 64 (k' + 1), ()) m _ _ ?_)
      dsimp only [incContract, vals, Arg.val_var]; wp_unfold
      rw [bv64_ofNat_succ_sub_one]
      refine hlt k' _ m (by omega) ⟨by omega, rfl, ?_, rfl⟩
      dsimp only
      have h1 : BitVec.ofNat 64 (k' + 1) = BitVec.ofNat 64 k' + 1 := by grind
      rw [← hs, tri_succ, h1]; ac_rfl
  · wp_unfold
    exact hJ n.toNat (n, 0, ()) m ⟨Nat.le_refl _, by simp, by dsimp only; grind, rfl⟩

/-! ## 4. Closed Module Environment and `ModuleOk` -/

/-- Closed contract environment for all 12 scalar litmus functions. -/
def litmusEnv : Env
  | "tracer",  [.bits 64, .bits 64, .bits 64], [.bits 64] => tracerContract
  | "ifelse",  [.bits 64, .bits 64], [.bits 64]           => ifelseContract
  | "sumto",   [.bits 64], [.bits 64]                     => sumtoContract
  | "evenodd", [.bits 64], [.bits 64]                     => evenoddContract
  | "nested",  [.bits 64, .bits 64, .bits 64], [.bits 64] => nestedContract
  | "swap",    [.bits 64, .bits 64, .bits 64], [.bits 64] => swapContract
  | "inc",     [.bits 64], [.bits 64]                     => incContract
  | "callinc", [.bits 64, .bits 64], [.bits 64]           => callincContract
  | "check",   [.bits 64], [.bits 64]                     => checkContract
  | "twice",   [.bits 64, .bits 64], [.bits 64]           => twiceContract
  | "spill10", [.bits 64, .bits 64], [.bits 64]           => spill10Contract
  | "sumcall", [.bits 64, .bits 64], [.bits 64]           => sumcallContract
  | _, _, _ => fun _ _ _ _ => False

theorem litmusEnv_sound : ∀ fn ∈ allFns, ∀ xs m Q X,
    litmusEnv fn.name fn.as fn.rs xs m Q X → Func.wp litmusEnv fn.body xs m Q X := by
  intro fn hfn
  simp only [allFns, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tracer_spec litmusEnv
  · exact ifelse_spec litmusEnv
  · exact sumto_spec litmusEnv
  · exact evenodd_spec litmusEnv
  · exact nested_spec litmusEnv
  · exact swap_spec litmusEnv
  · exact inc_spec litmusEnv
  · exact callinc_spec litmusEnv (fun _ _ _ _ h => h)
  · exact check_spec litmusEnv
  · exact twice_spec litmusEnv (fun _ _ _ _ h => h)
  · exact spill10_spec litmusEnv
  · exact sumcall_spec litmusEnv (fun _ _ _ _ h => h)

private theorem allFns_wf : ∀ fn ∈ allFns, fn.Wf := by
  intro fn hfn
  simp only [allFns, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tracer_wf
  · exact ifelse_wf
  · exact sumto_wf
  · exact evenodd_wf
  · exact nested_wf
  · exact swap_wf
  · exact inc_wf
  · exact callinc_wf
  · exact check_wf
  · exact twice_wf
  · exact spill10_wf
  · exact sumcall_wf

private theorem moduleOk_of_subset {M : Module} (hacyc : M.checkAcyclic = true)
    (hsub : ∀ fn ∈ M.fns, fn ∈ allFns) : ModuleOk litmusEnv M :=
  Module.moduleOk_of_checkAcyclic hacyc
    (fun fn hmem => allFns_wf fn (hsub fn hmem))
    (fun fn hmem => litmusEnv_sound fn (hsub fn hmem))

private theorem single_moduleOk {f : Fn} (hf : f ∈ allFns)
    (hacyc : ({ fns := [f], externs := [], exits := [] } : Module).checkAcyclic = true) :
    ModuleOk litmusEnv ⟨[f], [], []⟩ :=
  moduleOk_of_subset hacyc (by intro g hg; simp at hg; subst hg; exact hf)

private theorem pair_moduleOk {f g : Fn} {ex : List String} (hf : f ∈ allFns) (hg : g ∈ allFns)
    (hacyc : ({ fns := [f, g], externs := [], exits := ex } : Module).checkAcyclic = true) :
    ModuleOk litmusEnv ⟨[f, g], [], ex⟩ :=
  moduleOk_of_subset hacyc (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption)

theorem tracer_moduleOk : ModuleOk litmusEnv tracerModule :=
  single_moduleOk (by simp [allFns]) tracerModule_acyclic
theorem ifelse_moduleOk : ModuleOk litmusEnv ifelseModule :=
  single_moduleOk (by simp [allFns]) ifelseModule_acyclic
theorem sumto_moduleOk : ModuleOk litmusEnv sumtoModule :=
  single_moduleOk (by simp [allFns]) sumtoModule_acyclic
theorem evenodd_moduleOk : ModuleOk litmusEnv evenoddModule :=
  single_moduleOk (by simp [allFns]) evenoddModule_acyclic
theorem nested_moduleOk : ModuleOk litmusEnv nestedModule :=
  single_moduleOk (by simp [allFns]) nestedModule_acyclic
theorem swap_moduleOk : ModuleOk litmusEnv swapModule :=
  single_moduleOk (by simp [allFns]) swapModule_acyclic
theorem spill10_moduleOk : ModuleOk litmusEnv spill10Module :=
  single_moduleOk (by simp [allFns]) spill10Module_acyclic
theorem callinc_moduleOk : ModuleOk litmusEnv callincModule :=
  pair_moduleOk (by simp [allFns]) (by simp [allFns]) callincModule_acyclic
theorem twice_moduleOk : ModuleOk litmusEnv twiceModule :=
  pair_moduleOk (by simp [allFns]) (by simp [allFns]) twiceModule_acyclic
theorem sumcall_moduleOk : ModuleOk litmusEnv sumcallModule :=
  pair_moduleOk (by simp [allFns]) (by simp [allFns]) sumcallModule_acyclic

/-! ## 5. Concrete Memory Non-Vacuity (`tracer_nonvacuous`) -/

/-- Concrete 8-byte zero-initialized memory cell at address `p`. -/
def zeros8Mem (p : BitVec 64) : Mem 64 := (Int.toBytes 8 (0#64).toInt).At p

theorem tracer_nonvacuous :
    Func.spec litmusEnv tracer.body (40, 2, 0x1000#64, ()) (zeros8Mem 0x1000#64)
      (fun r m' => r = (42, ()) ∧ (cell64 0x1000#64 42 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  tracer_spec litmusEnv (40, 2, 0x1000#64, ()) (zeros8Mem 0x1000#64) _ _
    ⟨0#64, emp, by rw [sep_emp]; rfl, fun _ hm' => ⟨rfl, hm'⟩⟩

end LeanQbe.T.Examples.Litmus
