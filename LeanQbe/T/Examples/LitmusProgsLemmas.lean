module

public import LeanQbe.T.Examples.LitmusProgs
public import LeanQbe.T.Logic.Rules
public import LeanQbe.T.FlatLemmas
import LeanQbe.T.Logic.ProofKit

/-!
# Well-Formedness, Source Contracts, and `ModuleOk` for `LeanQbe.T.Examples.Litmus`
-/

set_option autoImplicit false
namespace LeanQbe.T.Examples.Litmus
open Std.ExtHashMap LeanQbe.T

@[expose] public section

/-- Low 32 bits of a 64-bit word are nonzero (`cnew (trunc 64 32 _) 0`). -/
def Truthy (c : BitVec 64) : Prop := c.setWidth 32 ≠ 0#32

/-- `1 + 2 + … + k` in 64-bit arithmetic. -/
def tri : Nat → BitVec 64
  | 0 => 0
  | k + 1 => tri k + BitVec.ofNat 64 (k + 1)

def tracerContract : Spec [i64, i64, i64] [i64] := fun (a, b, p, ()) m Q _ =>
  ∃ v0 R, (cell64 p v0 ⋆ R) m ∧ ∀ m', (cell64 p (a + b) ⋆ R) m' → Q (a + b, ()) m'
def ifelseContract : Spec [i64, i64] [i64] := fun (a, b, ()) m Q _ =>
  (Truthy a → Q (a + b, ()) m) ∧ (¬ Truthy a → Q (b - a, ()) m)
def sumtoContract : Spec [i64] [i64] :=
  fun (n, ()) m Q _ => n.toNat < 2 ^ 32 ∧ Q (tri n.toNat, ()) m
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
  (¬ Truthy a → X "fail" [i64] (a, ()) m) ∧ (Truthy a → ¬ Truthy b → X "fail" [i64] (b, ()) m)

/-- Expected return value of `spill10(a, b)`. -/
def spill10Val (a b : BitVec 64) : BitVec 64 :=
  (a + 1) ^^^ (a + 2) ^^^ (a + 3) ^^^ (a + 4) ^^^ (a + 5) ^^^
  (a + 6) ^^^ (a + 7) ^^^ (a + 8) ^^^ (a + 9) ^^^ (a + 10) ^^^ b

def spill10Contract : Spec [i64, i64] [i64] := fun (a, b, ()) m Q _ => Q (spill10Val a b, ()) m
def sumcallContract : Spec [i64, i64] [i64] := fun (n, b, ()) m Q _ =>
  n.toNat < 2 ^ 32 ∧ Q (tri n.toNat + n + b, ()) m

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

/-- Concrete 8-byte zero-initialized memory cell at address `p`. -/
def zeros8Mem (p : BitVec 64) : Mem 64 := (Int.toBytes 8 (0#64).toInt).At p

end

public section

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

private theorem jnz_ofNat {k : Nat} (hk : k < 2 ^ 32) {P Q : Prop}
    (hp : ∀ k', k = k' + 1 → P) (hq : k = 0 → Q) :
    (¬ (BitVec.ofNat 64 k).setWidth 32 = 0 → P) ∧ ((BitVec.ofNat 64 k).setWidth 32 = 0 → Q) := by
  cases k with
  | zero => exact ⟨fun h => absurd (by decide) h, fun _ => hq rfl⟩
  | succ k' =>
    exact ⟨fun _ => hp k' rfl, fun h => by
      have h' : ((BitVec.ofNat 64 (k' + 1)).setWidth 32).toNat = 0 := congrArg BitVec.toNat h
      simp [Nat.mod_eq_of_lt hk] at h'⟩
private theorem bv64_succ (k : Nat) : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 k + 1 := by grind
private theorem bv64_sub (k : Nat) : BitVec.ofNat 64 (k + 1) - 1 = BitVec.ofNat 64 k := by grind
private theorem countdown_loop {Γ : Env} {rs tsRest : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {bodies : Tup Cont [i64 :: tsRest] → Blocks Val Cont rs [i64 :: tsRest]}
    {entry : Tup Cont [i64 :: tsRest] → Expr Val Cont rs}
    (n : BitVec 64) (Inv : Nat → Tup Val tsRest → Prop) (rest₀ : Tup Val tsRest)
    (h0 : Inv n.toNat rest₀)
    (hstep : ∀ J k rest, k ≤ n.toNat → Inv k rest → (∀ k' rest', k' < k → Inv k' rest' →
      J (BitVec.ofNat 64 k', rest') m) →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here (BitVec.ofNat 64 k, rest)) m)
    (hentry : ∀ J : Cont (i64 :: tsRest), J (n, rest₀) m → wp Γ Q X (entry (J, ())) m := by
      intro _ hJ; wp_unfold; exact hJ) :
    wp Γ Q X (.group (sig := [i64 :: tsRest]) bodies entry) m :=
  wp_while_state_pure (fun p : Nat × Tup Val tsRest => (BitVec.ofNat 64 p.1, p.2)) Prod.fst
    (fun p => p.1 ≤ n.toNat ∧ Inv p.1 p.2)
    (fun J hJ => hentry J (by simpa using hJ (n.toNat, rest₀) ⟨Nat.le_refl _, h0⟩))
    (fun J ⟨k, rest⟩ ⟨hk, hinv⟩ hback => hstep J k rest hk hinv fun k' rest' hlt hinv' =>
      hback (k', rest') hlt ⟨by omega, hinv'⟩)
theorem tracer_spec (Γ : Env) :
    ∀ args m Q X, tracerContract args m Q X → Func.spec Γ tracer.body args m Q X := by
  rintro ⟨a, b, p, ⟨⟩⟩ m Q X ⟨v0, R, hm, hQ⟩; dsimp only [Func.spec, Func.wp, tracer]; wp_unfold
  have ⟨hok, hm'⟩ := store_cell64 (a + b) hm; exact ⟨hok, hQ _ hm'⟩
theorem ifelse_spec (Γ : Env) :
    ∀ args m Q X, ifelseContract args m Q X → Func.spec Γ ifelse.body args m Q X := by
  rintro ⟨a, b, ⟨⟩⟩ m Q X ⟨ht, hf⟩; dsimp only [Func.spec, Func.wp, ifelse]; wp_unfold
  exact ⟨ht, fun h => hf (by simp [Truthy, h])⟩
theorem sumto_spec (Γ : Env) :
    ∀ args m Q X, sumtoContract args m Q X → Func.spec Γ sumto.body args m Q X := by
  rintro ⟨n, ⟨⟩⟩ m Q X ⟨hn, hQ⟩; dsimp only [Func.spec, Func.wp, sumto]
  refine countdown_loop n (fun k xs => xs.1 + tri k = tri n.toNat) (0#64, ()) (by simp) ?_
  intro J k ⟨s, ⟨⟩⟩ hk hs hlt; dsimp only [Blocks.get_here] at *; wp_unfold
  refine jnz_ofNat (by omega) (fun k' hkk => ?_) (fun h0 => ?_)
  · subst hkk; rw [bv64_sub]; exact hlt k' _ (by omega) (by dsimp only; rw [← hs, tri]; ac_rfl)
  · subst h0; rwa [show s = tri n.toNat by simpa [tri] using hs]
theorem evenodd_spec (Γ : Env) :
    ∀ args m Q X, evenoddContract args m Q X → Func.spec Γ evenodd.body args m Q X := by
  rintro ⟨n, ⟨⟩⟩ m Q X ⟨hn, hQ⟩; dsimp only [Func.spec, Func.wp, evenodd, wp]
  rintro ⟨Je, Jo, ⟨⟩⟩ ⟨hE, hO, -⟩
  suffices h : ∀ k ≤ n.toNat, (n.toNat % 2 = k % 2 → Je (BitVec.ofNat 64 k, ()) m) ∧
      (n.toNat % 2 ≠ k % 2 → Jo (BitVec.ofNat 64 k, ()) m) from
    (by simp : BitVec.ofNat 64 n.toNat = n) ▸ (h n.toNat (Nat.le_refl _)).1 rfl
  intro k hk; induction k with
  | zero =>
    refine ⟨fun _ => hE _ _ ?_, fun _ => hO _ _ ?_⟩ <;>
      (wp_unfold; refine jnz_ofNat (by omega) (fun _ h => by cases h) fun _ => ?_) <;>
      first | simpa [show n.toNat % 2 = 0 from by omega] using hQ
            | simpa [show n.toNat % 2 ≠ 0 from by omega] using hQ
  | succ k' ih =>
    obtain ⟨ihE, ihO⟩ := ih (by omega)
    refine ⟨fun _ => hE _ _ ?_, fun _ => hO _ _ ?_⟩ <;>
      (wp_unfold; refine jnz_ofNat (by omega) (fun _ h => ?_) fun h => by cases h) <;>
      (cases h; rw [bv64_sub]; first | exact ihO (by omega) | exact ihE (by omega))
theorem nested_spec (Γ : Env) :
    ∀ args m Q X, nestedContract args m Q X → Func.spec Γ nested.body args m Q X := by
  rintro ⟨n, m, k, ⟨⟩⟩ mem Q X ⟨hn, hm, hQ⟩; dsimp only [Func.spec, Func.wp, nested]
  refine countdown_loop n (fun oi xs => xs.1 + m * (BitVec.ofNat 64 oi * k + tri oi) =
    m * (n * k + tri n.toNat)) (0#64, ()) (by simp) ?_
  intro Jo oi ⟨t, ⟨⟩⟩ hoi ht hltO; dsimp only [Blocks.get_here] at *; wp_unfold
  refine jnz_ofNat (by omega) (fun oi' hoi' => ?_) (fun h0 => ?_)
  · subst hoi'
    refine countdown_loop m (fun oj xs => xs.1 + BitVec.ofNat 64 oj *
      (k + BitVec.ofNat 64 (oi' + 1)) = t + m * (k + BitVec.ofNat 64 (oi' + 1))) (t, ())
      (by simp) fun Ji oj ⟨u, ⟨⟩⟩ hoj hu hltI => by
      dsimp only [Blocks.get_here] at *; wp_unfold
      refine jnz_ofNat (by omega) (fun oj' hoj' => ?_) (fun hj0 => ?_)
      · subst hoj'; rw [bv64_sub]
        exact hltI oj' _ (by omega) (by dsimp only; rw [← hu, bv64_succ oj']; grind)
      · subst hj0; rw [bv64_sub]; exact hltO oi' _ (by omega) (by dsimp only; rw [show u = t +
          m * (k + BitVec.ofNat 64 (oi' + 1)) by simpa using hu, ← ht, bv64_succ oi', tri]; grind)
  · subst h0; rwa [show t = m * (n * k + tri n.toNat) by simpa [tri] using ht]
theorem swap_spec (Γ : Env) :
    ∀ args m Q X, swapContract args m Q X → Func.spec Γ swap.body args m Q X := by
  rintro ⟨n, a, b, ⟨⟩⟩ m Q X ⟨hn, hQ⟩; dsimp only [Func.spec, Func.wp, swap]
  refine countdown_loop n (fun k xs => (n.toNat % 2 = k % 2 → xs.1 = a ∧ xs.2.1 = b) ∧
      (n.toNat % 2 ≠ k % 2 → xs.1 = b ∧ xs.2.1 = a))
    (a, b, ()) ⟨fun _ => ⟨rfl, rfl⟩, fun h => absurd rfl h⟩ ?_
  intro J k ⟨x, y, ⟨⟩⟩ hk ⟨heq, hne⟩ hlt; dsimp only [Blocks.get_here] at *; wp_unfold
  refine jnz_ofNat (by omega) (fun k' hkk => ?_) (fun h0 => ?_)
  · subst hkk; rw [bv64_sub]
    exact hlt k' _ (by omega) ⟨fun _ => (hne (by omega)).symm, fun _ => (heq (by omega)).symm⟩
  · subst h0; by_cases hpar : n.toNat % 2 = 0
    · simpa [hpar, (heq (by omega)).1] using hQ
    · simpa [hpar, (hne (by omega)).1] using hQ
theorem inc_spec (Γ : Env) :
    ∀ args m Q X, incContract args m Q X → Func.spec Γ inc.body args m Q X := by
  rintro ⟨a, ⟨⟩⟩ m Q X hQ; dsimp only [Func.spec, Func.wp, inc]; wp_unfold; exact hQ
theorem callinc_spec (Γ : Env)
    (hinc : ∀ args m Q X, incContract args m Q X → Γ "inc" [i64] [i64] args m Q X) :
    ∀ args m Q X, callincContract args m Q X → Func.spec Γ callinc.body args m Q X := by
  rintro ⟨a, b, ⟨⟩⟩ m Q X hQ; dsimp only [Func.spec, Func.wp, callinc]
  refine wp_call_of_spec _ _ (hinc _ m _ _ ?_)
  dsimp only [incContract, vals, Arg.val_var]; wp_unfold; exact hQ
theorem check_spec (Γ : Env) :
    ∀ args m Q X, checkContract args m Q X → Func.spec Γ check.body args m Q X := by
  rintro ⟨a, ⟨⟩⟩ m Q X ⟨hQ, hX⟩; dsimp only [Func.spec, Func.wp, check]; wp_unfold
  exact ⟨hQ, fun h => hX (by simp [Truthy, h])⟩
theorem twice_spec (Γ : Env)
    (hcheck : ∀ args m Q X, checkContract args m Q X → Γ "check" [i64] [i64] args m Q X) :
    ∀ args m Q X, twiceContract args m Q X → Func.spec Γ twice.body args m Q X := by
  rintro ⟨a, b, ⟨⟩⟩ m Q X ⟨hQ, hXa, hXb⟩; dsimp only [Func.spec, Func.wp, twice]
  refine wp_call_of_spec _ _ (hcheck _ m _ _ ⟨fun ha => ?_, hXa⟩)
  refine wp_call_of_spec _ _ (hcheck _ m _ _ ⟨fun hb => ?_, hXb ha⟩); wp_unfold; exact hQ ha hb
theorem spill10_spec (Γ : Env) :
    ∀ args m Q X, spill10Contract args m Q X → Func.spec Γ spill10.body args m Q X := by
  rintro ⟨a, b, ⟨⟩⟩ m Q X hQ; dsimp only [Func.spec, Func.wp, spill10]; wp_unfold
  simpa [spill10Contract, spill10Val] using hQ
theorem sumcall_spec (Γ : Env)
    (hinc : ∀ args m Q X, incContract args m Q X → Γ "inc" [i64] [i64] args m Q X) :
    ∀ args m Q X, sumcallContract args m Q X → Func.spec Γ sumcall.body args m Q X := by
  rintro ⟨n, b, ⟨⟩⟩ m Q X ⟨hn, hQ⟩; dsimp only [Func.spec, Func.wp, sumcall]
  refine countdown_loop n (fun k xs => xs.1 + tri k + BitVec.ofNat 64 k = tri n.toNat + n)
    (0#64, ()) (by simp) ?_
  intro J k ⟨s, ⟨⟩⟩ hk hs hlt; dsimp only [Blocks.get_here] at *; wp_unfold
  refine jnz_ofNat (by omega) (fun k' hkk => ?_) fun h0 => by
    subst h0; rwa [show s = tri n.toNat + n by simpa [tri] using hs]
  subst hkk; refine wp_call_of_spec _ _ (hinc _ m _ _ ?_)
  dsimp only [incContract, vals, Arg.val_var]; wp_unfold; rw [bv64_sub]
  exact hlt k' _ (by omega) (by dsimp only; rw [← hs, tri, bv64_succ k']; ac_rfl)
theorem litmusEnv_sound : ∀ fn ∈ allFns, ∀ xs m Q X,
    litmusEnv fn.name fn.as fn.rs xs m Q X → Func.wp litmusEnv fn.body xs m Q X := by
  intro fn hfn; simp only [allFns, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
    | exact tracer_spec _ | exact ifelse_spec _ | exact sumto_spec _ | exact evenodd_spec _
    | exact nested_spec _ | exact swap_spec _   | exact inc_spec _   | exact check_spec _
    | exact spill10_spec _ | exact callinc_spec _ (fun _ _ _ _ h => h)
    | exact twice_spec _ (fun _ _ _ _ h => h) | exact sumcall_spec _ (fun _ _ _ _ h => h)
private theorem ok1 {f : Fn} (hwf : f.Wf) (hacyc : Module.checkAcyclic ⟨[f], [], []⟩ = true)
    (hf : f ∈ allFns := by simp [allFns]) : ModuleOk litmusEnv ⟨[f], [], []⟩ :=
  Module.moduleOk_of_checkAcyclic hacyc (fun _ hg => by simp at hg; subst hg; exact hwf)
    (fun _ hg => by simp at hg; subst hg; exact litmusEnv_sound _ hf)
private theorem ok2 {f g : Fn} {ex : List String} (hwf : f.Wf) (hwg : g.Wf)
    (hacyc : Module.checkAcyclic ⟨[f, g], [], ex⟩ = true) (hf : f ∈ allFns := by simp [allFns])
    (hg : g ∈ allFns := by simp [allFns]) : ModuleOk litmusEnv ⟨[f, g], [], ex⟩ :=
  Module.moduleOk_of_checkAcyclic hacyc (fun _ hx => by
    simp at hx; rcases hx with rfl | rfl <;> assumption) (fun _ hx => by
      simp at hx; rcases hx with rfl | rfl; exact litmusEnv_sound _ hf; exact litmusEnv_sound _ hg)
theorem tracer_moduleOk  : ModuleOk litmusEnv tracerModule  := ok1 tracer_wf tracerModule_acyclic
theorem ifelse_moduleOk  : ModuleOk litmusEnv ifelseModule  := ok1 ifelse_wf ifelseModule_acyclic
theorem sumto_moduleOk   : ModuleOk litmusEnv sumtoModule   := ok1 sumto_wf sumtoModule_acyclic
theorem evenodd_moduleOk : ModuleOk litmusEnv evenoddModule := ok1 evenodd_wf evenoddModule_acyclic
theorem nested_moduleOk  : ModuleOk litmusEnv nestedModule  := ok1 nested_wf nestedModule_acyclic
theorem swap_moduleOk    : ModuleOk litmusEnv swapModule    := ok1 swap_wf swapModule_acyclic
theorem spill10_moduleOk : ModuleOk litmusEnv spill10Module := ok1 spill10_wf spill10Module_acyclic
theorem callinc_moduleOk : ModuleOk litmusEnv callincModule :=
  ok2 inc_wf callinc_wf callincModule_acyclic
theorem twice_moduleOk : ModuleOk litmusEnv twiceModule := ok2 check_wf twice_wf twiceModule_acyclic
theorem sumcall_moduleOk : ModuleOk litmusEnv sumcallModule :=
  ok2 inc_wf sumcall_wf sumcallModule_acyclic
theorem tracer_nonvacuous : Func.spec litmusEnv tracer.body (40, 2, 0x1000#64, ())
    (zeros8Mem 0x1000#64) (fun r m' => r = (42, ()) ∧ (cell64 0x1000#64 42 ⋆ emp) m')
    (fun _ _ _ _ => False) := tracer_spec litmusEnv (40, 2, 0x1000#64, ())
    (zeros8Mem 0x1000#64) _ _ ⟨0#64, emp, by rw [sep_emp]; rfl, fun _ hm' => ⟨rfl, hm'⟩⟩
end
end LeanQbe.T.Examples.Litmus
