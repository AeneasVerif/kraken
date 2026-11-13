module

public import LeanQbe.Examples.LitmusProgs
public import LeanQbe.Wf
public import LeanQbe.WPLemmas
public import LeanQbe.MainLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Litmus programs: well-formedness and source-level contracts (generic)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.Litmus

theorem tracer_wf : Func.Wf tracer.body := by unfold tracer; wf_tac
theorem ifelse_wf : Func.Wf ifelse.body := by unfold ifelse; wf_tac
theorem sumto_wf : Func.Wf sumto.body := by unfold sumto; wf_tac
theorem evenodd_wf : Func.Wf evenodd.body := by unfold evenodd; wf_tac
theorem nested_wf : Func.Wf nested.body := by unfold nested; wf_tac
theorem swap_wf : Func.Wf swap.body := by unfold swap; wf_tac
theorem inc_wf : Func.Wf inc.body := by unfold inc; wf_tac
theorem callinc_wf : Func.Wf callinc.body := by unfold callinc; wf_tac
theorem check_wf : Func.Wf check.body := by unfold check; wf_tac
theorem twice_wf : Func.Wf twice.body := by unfold twice; wf_tac
theorem spill10_wf : Func.Wf spill10.body := by unfold spill10; wf_tac
theorem sumcall_wf : Func.Wf sumcall.body := by unfold sumcall; wf_tac

/-- `1 + 2 + … + i` in 64-bit arithmetic. -/
def tri : Nat → Val
  | 0 => 0
  | i + 1 => tri i + BitVec.ofNat 64 (i + 1)

/-- The source-level contract of `sumto`, by induction over the loop counter (the join point is
universally quantified and constrained only by its closure hypothesis `hloop`). -/
theorem sumto_spec (Γ : Env) (n : Val) (hn : n.toNat < 2 ^ 32) (m : Mem 64) :
    Func.spec Γ sumto.body [n] m (fun r m' => r = [tri n.toNat] ∧ m' = m) (fun _ _ _ => False) := by
  simp only [Func.spec, sumto, wp, Op.wp, Op.eval, BinOp.eval, Arg.val, List.map,
    closed_param, forall_args_nil, List.nil_append, true_and, Option.some.injEq,
    exists_eq_left']
  intro loop hloop
  suffices h : ∀ k, k ≤ n.toNat → ∀ s, s + tri k = tri n.toNat → loop [BitVec.ofNat 64 k, s] m by
    simpa using h n.toNat (Nat.le_refl _) 0 (by simp)
  intro k
  induction k with
  | zero =>
    intro _ s hs
    refine hloop _ _ _ ⟨fun ht => absurd ht (by decide), fun _ => ⟨?_, rfl⟩⟩
    simpa [tri] using hs
  | succ k ih =>
    intro hk s hs
    have hk32 : k + 1 < 2 ^ 32 := by omega
    have ht : Truthy (BitVec.ofNat 64 (k + 1)) := by
      simp only [Truthy, lo32, ne_eq]
      grind
    refine hloop _ _ _ ⟨fun _ => ?_, fun hnt => absurd ht hnt⟩
    have hsub : BitVec.ofNat 64 (k + 1) - 1 = BitVec.ofNat 64 k := by
      grind
    rw [hsub]
    refine ih (by omega) _ ?_
    rw [← hs]; simp only [tri]; ac_rfl

/-- Source contract of `inc`. -/
def incContract : Spec := fun args m Q _ =>
  ∃ a, args = [a] ∧ Q [a + 1] m

theorem inc_spec (Γ : Env) :
    ∀ args m Q X, incContract args m Q X → Func.spec Γ inc.body args m Q X := by
  rintro _ m Q X ⟨a, rfl, hQ⟩
  simp only [Func.spec, inc, wp, Op.wp, Op.eval, BinOp.eval, Arg.val, List.map, true_and,
    Option.some.injEq, exists_eq_left']
  exact hQ

/-- Source contract of `callinc`. -/
def callincContract : Spec := fun args m Q _ =>
  ∃ a b, args = [a, b] ∧ Q [a + 1 + b] m

theorem callinc_spec (Γ : Env) (hinc : Γ "inc" = incContract) :
    ∀ args m Q X, callincContract args m Q X → Func.spec Γ callinc.body args m Q X := by
  rintro _ m Q X ⟨a, b, rfl, hQ⟩
  simp only [Func.spec, callinc, wp, Arg.val, List.map, true_and]
  refine ⟨fun rs m' => rs = [a + 1] ∧ m' = m, fun _ _ _ => False, ?_, ?_, fun _ _ _ h => h.elim⟩
  · rw [hinc]; exact ⟨a, rfl, rfl, rfl⟩
  · rintro _ _ ⟨rfl, rfl⟩
    exact ⟨rfl, a + 1 + b, rfl, rfl, hQ⟩

/-- Source contract of `check`. -/
def checkContract : Spec := fun args m Q X =>
  ∃ a, args = [a] ∧ (Truthy a → Q [a] m) ∧ (¬Truthy a → X "fail" [a] m)

theorem check_spec (Γ : Env) :
    ∀ args m Q X, checkContract args m Q X → Func.spec Γ check.body args m Q X := by
  rintro _ m Q X ⟨a, rfl, hQ, hX⟩
  simp only [Func.spec, check, wp, Arg.val, List.map, true_and]
  exact ⟨hQ, hX⟩

/-- Source contract of `twice`: returns `[a + b]` if both are truthy, else exits to `"fail"`. -/
def twiceContract : Spec := fun args m Q X =>
  ∃ a b, args = [a, b] ∧
    (Truthy a → Truthy b → Q [a + b] m) ∧
    (¬Truthy a → X "fail" [a] m) ∧
    (Truthy a → ¬Truthy b → X "fail" [b] m)

theorem twice_spec (Γ : Env) (hcheck : Γ "check" = checkContract) :
    ∀ args m Q X, twiceContract args m Q X → Func.spec Γ twice.body args m Q X := by
  rintro _ m Q X ⟨a, b, rfl, hQ, hXa, hXb⟩
  simp only [Func.spec, twice, wp, Arg.val, List.map, true_and]
  refine ⟨fun rs m' => Truthy a ∧ rs = [a] ∧ m' = m,
    fun g xs m' => ¬Truthy a ∧ g = "fail" ∧ xs = [a] ∧ m' = m, ?_, ?_, ?_⟩
  · rw [hcheck]; exact ⟨a, rfl, fun ha => ⟨ha, rfl, rfl⟩, fun hna => ⟨hna, rfl, rfl, rfl⟩⟩
  · rintro _ m1 ⟨ha, rfl, rfl⟩
    refine ⟨rfl, fun rs m' => Truthy b ∧ rs = [b] ∧ m' = m1,
      fun g xs m' => ¬Truthy b ∧ g = "fail" ∧ xs = [b] ∧ m' = m1, ?_, ?_, ?_⟩
    · rw [hcheck]; exact ⟨b, rfl, fun hb => ⟨hb, rfl, rfl⟩, fun hnb => ⟨hnb, rfl, rfl, rfl⟩⟩
    · rintro _ _ ⟨hb, rfl, rfl⟩
      exact ⟨rfl, a + b, rfl, rfl, hQ ha hb⟩
    · grind
  · grind

/-- Expected value of `spill10(a, b)`. -/
def spill10Val (a b : Val) : Val :=
  (a + 1) ^^^ (a + 2) ^^^ (a + 3) ^^^ (a + 4) ^^^ (a + 5) ^^^
  (a + 6) ^^^ (a + 7) ^^^ (a + 8) ^^^ (a + 9) ^^^ (a + 10) ^^^ b

theorem spill10_spec (Γ : Env) (a b : Val) (m : Mem 64) :
    Func.spec Γ spill10.body [a, b] m (fun r m' => r = [spill10Val a b] ∧ m' = m)
      (fun _ _ _ => False) := by
  simp [Func.spec, spill10, spill10Val, wp, Op.wp, Op.eval, BinOp.eval, Arg.val]

theorem tracer_spec (Γ : Env) (a b p : Val) (m : Mem 64) (hp : storeOk m .l p) :
    Func.spec Γ tracer.body [a, b, p] m
      (fun rets m' => rets = [a + b] ∧ m' = storeMem m .l p (a + b))
      (fun _ _ _ => False) := by
  simp [Func.spec, tracer, wp, Op.wp, Op.eval, BinOp.eval, Arg.val, hp]

def zeros8 : List UInt8 := List.replicate 8 0

def m0 : Mem 64 := zeros8.At 0x1000#64

theorem m0_loadInt : ∃ i, m0.loadInt 0x1000#64 8 = some i :=
  ⟨_, Mem.loadInt_sep zeros8 _ 8 Std.ExtHashMap.emp m0 (by rw [Std.ExtHashMap.sep_emp]; rfl)
    (by simp [zeros8]) (by decide)⟩

abbrev emptyEnv : Env := fun _ _ _ _ _ => False

/-- Target-generic `FnSpec` for any single-function `Compiled` module `[f]`. -/
theorem leaf_fnSpec {T : Target} {f : Fn} {maxBound : Nat}
    (M : Compiled T [] [] 0 [f] maxBound) (hwf : Func.Wf f.body)
    (h : T.Host) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.prog h) k₀) (hu : T.LabelsUnique h) :
    T.Defined h f.name ∧ T.FnSpec h f.name (Func.spec emptyEnv f.body) (M.bound f.name) 0 := by
  let Γ : Env := fun _ => Func.spec emptyEnv f.body
  exact M.fnSpec h Γ k₀ hc hu
    (by intro f' hf'; simp at hf'; subst hf'; exact hwf)
    (by
      intro f' hf' args m Q X hs
      simp only [List.mem_singleton] at hf'
      subst hf'
      exact Func.spec_env_mono (fun _ _ _ _ _ h => nomatch h) hs)
    (fun _ hp => nomatch hp) (fun _ hg => nomatch hg) (by simp)

def callincEnv : Env := fun g => if g = "inc" then incContract else callincContract

theorem callinc_wf_all : ∀ f ∈ [inc, callinc], Func.Wf f.body := by
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact inc_wf
  · exact callinc_wf

theorem callincEnv_sound :
    ∀ f ∈ [inc, callinc], ∀ args m Q X,
      callincEnv f.name args m Q X → Func.spec callincEnv f.body args m Q X := by
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact inc_spec _
  · exact callinc_spec _ rfl

/-- Target-generic `FnSpec` for `[inc, callinc]`. -/
theorem callinc_fnSpec {T : Target} {maxBound : Nat}
    (M : Compiled T [] [] 0 [inc, callinc] maxBound)
    (h : T.Host) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.prog h) k₀) (hu : T.LabelsUnique h)
    {nm : String} (hnm : nm ∈ [inc, callinc].map Fn.name) :
    T.Defined h nm ∧ T.FnSpec h nm (callincEnv nm) (M.bound nm) 0 :=
  M.fnSpec h callincEnv k₀ hc hu callinc_wf_all callincEnv_sound
    (fun _ hp => nomatch hp) (fun _ hg => nomatch hg) hnm

def twiceEnv : Env := fun g => if g = "check" then checkContract else twiceContract

theorem twice_wf_all : ∀ f ∈ [check, twice], Func.Wf f.body := by
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact check_wf
  · exact twice_wf

theorem twiceEnv_sound :
    ∀ f ∈ [check, twice], ∀ args m Q X,
      twiceEnv f.name args m Q X → Func.spec twiceEnv f.body args m Q X := by
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact check_spec _
  · exact twice_spec _ rfl

/-- Target-generic `FnSpec` for `[check, twice]`. -/
theorem twice_fnSpec {T : Target} {nX maxBound : Nat}
    (M : Compiled T [] ["fail"] nX [check, twice] maxBound)
    (h : T.Host) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.prog h) k₀) (hu : T.LabelsUnique h)
    (hfail : T.Defined h "fail")
    {nm : String} (hnm : nm ∈ [check, twice].map Fn.name) :
    T.Defined h nm ∧ T.FnSpec h nm (twiceEnv nm) (M.bound nm) nX :=
  M.fnSpec h twiceEnv k₀ hc hu twice_wf_all twiceEnv_sound
    (fun _ hp => nomatch hp)
    (by intro g hg; simp at hg; subst hg; exact hfail) hnm

def incOnlyEnv : Env := fun g =>
  if g = "inc" then incContract else fun _ _ _ _ => False

def sumcallEnv : Env := fun g =>
  if g = "inc" then incContract else Func.spec incOnlyEnv sumcall.body

theorem sumcall_wf_all : ∀ f ∈ [inc, sumcall], Func.Wf f.body := by
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact inc_wf
  · exact sumcall_wf

theorem sumcallEnv_sound :
    ∀ f ∈ [inc, sumcall], ∀ args m Q X,
      sumcallEnv f.name args m Q X → Func.spec sumcallEnv f.body args m Q X := by
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact inc_spec _
  · intro args m Q X hs
    have hs' : Func.spec incOnlyEnv sumcall.body args m Q X := by
      simpa [sumcallEnv, sumcall] using hs
    refine Func.spec_env_mono (fun g xs m' Q' X' hg => ?_) hs'
    by_cases heq : g = "inc" <;> simp [incOnlyEnv, sumcallEnv, heq] at hg ⊢
    exact hg

theorem sumcall_fnSpec {T : Target} {maxBound : Nat}
    (M : Compiled T [] [] 0 [inc, sumcall] maxBound)
    (h : T.Host) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.prog h) k₀) (hu : T.LabelsUnique h)
    {nm : String} (hnm : nm ∈ [inc, sumcall].map Fn.name) :
    T.Defined h nm ∧ T.FnSpec h nm (sumcallEnv nm) (M.bound nm) 0 :=
  M.fnSpec h sumcallEnv k₀ hc hu sumcall_wf_all sumcallEnv_sound
    (fun _ hp => nomatch hp) (fun _ hg => nomatch hg) hnm

section Closed

variable {T : Target} {maxBound : Nat}

theorem tracer_returns (M : Compiled T [] [] 0 [tracer] maxBound) (h : T.Host) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.prog h) k₀) (hu : T.LabelsUnique h)
    (a b p : Val) (m : Mem 64) (hp : storeOk m .l p) :
    T.Returns h "tracer" (M.bound "tracer") [a, b, p] (Eq m)
      (fun rets m' => rets = [a + b] ∧ m' = storeMem m .l p (a + b)) :=
  (leaf_fnSpec M tracer_wf h k₀ hc hu).2.returns fun _ e => e ▸ tracer_spec emptyEnv a b p m hp

theorem sumto_returns (M : Compiled T [] [] 0 [sumto] maxBound) (h : T.Host) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.prog h) k₀) (hu : T.LabelsUnique h)
    (n : Val) (hn : n.toNat < 2 ^ 32) :
    T.Returns h "sumto" (M.bound "sumto") [n] Std.ExtHashMap.emp
      (fun rets m' => rets = [tri n.toNat] ∧ Std.ExtHashMap.emp m') :=
  (leaf_fnSpec M sumto_wf h k₀ hc hu).2.returns fun _ e => e ▸ sumto_spec emptyEnv n hn ∅

theorem callinc_returns (M : Compiled T [] [] 0 [inc, callinc] maxBound) (h : T.Host)
    (k₀ : Nat) (hc : M.code.IsInfixAt (T.prog h) k₀) (hu : T.LabelsUnique h) (a b : Val) :
    T.Returns h "callinc" (M.bound "callinc") [a, b] Std.ExtHashMap.emp
      (fun rets m' => rets = [a + 1 + b] ∧ Std.ExtHashMap.emp m') :=
  (callinc_fnSpec M h k₀ hc hu (nm := "callinc") (by decide)).2.returns
    fun _ e => ⟨a, b, rfl, rfl, e⟩

theorem twice_call {nX : Nat} (M : Compiled T [] ["fail"] nX [check, twice] maxBound)
    (h : T.Host) (k₀ : Nat) (hc : M.code.IsInfixAt (T.prog h) k₀) (hu : T.LabelsUnique h)
    (hfail : T.Defined h "fail") (a b : Val) :
    T.Call h "twice" (M.bound "twice") nX [a, b] Std.ExtHashMap.emp
      (fun rets m' => Truthy a ∧ Truthy b ∧ rets = [a + b] ∧ Std.ExtHashMap.emp m')
      (fun g xs m' => g = "fail" ∧ Std.ExtHashMap.emp m' ∧
        ((¬Truthy a ∧ xs = [a]) ∨ (Truthy a ∧ ¬Truthy b ∧ xs = [b]))) :=
  (twice_fnSpec M h k₀ hc hu hfail (nm := "twice") (by decide)).2.call
    fun _ e => ⟨a, b, rfl, fun ha hb => ⟨ha, hb, rfl, e⟩,
      fun hna => ⟨rfl, e, .inl ⟨hna, rfl⟩⟩, fun ha hnb => ⟨rfl, e, .inr ⟨ha, hnb, rfl⟩⟩⟩

theorem spill10_returns (M : Compiled T [] [] 0 [spill10] maxBound) (h : T.Host) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.prog h) k₀) (hu : T.LabelsUnique h) (a b : Val) :
    T.Returns h "spill10" (M.bound "spill10") [a, b] Std.ExtHashMap.emp
      (fun rets m' => rets = [spill10Val a b] ∧ Std.ExtHashMap.emp m') :=
  (leaf_fnSpec M spill10_wf h k₀ hc hu).2.returns fun _ e => e ▸ spill10_spec emptyEnv a b ∅

end Closed

end LeanQbe.Litmus
