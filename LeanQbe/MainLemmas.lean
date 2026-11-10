module

public import LeanQbe.Main
public import LeanQbe.RegaLemmas
public import LeanQbe.OptLemmas

/-!
# Correctness of the pipeline

* `compileFn_correct`: if `compileFn T.toIsa f = .ok code` and the code sits in host `h`, the
  compiled function meets the *source* function's `wp` as a `FnSpec`. The mid-end refines contracts
  (`Func.opt_spec`), the lowering is `lowerFn_correct`, and `FnSpec` is antitone in the contract.
* `compileFn_leaf_correct`: specialization of `compileFn_correct` to leaf functions without exits.
* `compile_correct`: module-level linking for an acyclic list of functions `fs` (callees first).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

theorem compileFn_correct {T : Target} (h : T.Host) (f : Fn) (Γ : Env)
    (bound : String → Nat) (n nX : Nat) (code : List T.Directive) (k₀ : Nat)
    (hcomp : compileFn T.toIsa f = .ok code) (hcode : code.IsInfixAt (T.prog h) k₀)
    (hu : T.LabelsUnique h) (hwf : Func.Wf f.body)
    (hFn : T.frameSize (f.nslots T.toIsa) ≤ n) (hn : n + T.raBytes ≤ 2 ^ 64)
    (hcallees : ∀ g ∈ f.opt.ext.callees,
      T.FnSpec h g (Γ g) (bound g) nX ∧ T.frameSize (f.nslots T.toIsa) + T.raBytes + bound g ≤ n)
    (hexits : ∀ g ∈ f.opt.ext.exits, T.Defined h g ∧ nX ≤ n) :
    T.FnSpec h f.name (Func.spec Γ f.body) n nX :=
  Target.FnSpec.of_spec T (Rega.lowerFn_correct h (f.hints T.toIsa) f.opt.ext f.opt Γ bound n nX
    code k₀ hcomp hcode hu (Func.opt_wf hwf) hFn hn hcallees hexits)
    fun _ _ _ _ hs => Func.opt_spec hwf hs

theorem compileFn_leaf_correct {T : Target} (h : T.Host) (f : Fn) (Γ : Env) (n nX : Nat)
    (code : List T.Directive) (k₀ : Nat)
    (hcomp : compileFn T.toIsa f = .ok code) (hcode : code.IsInfixAt (T.prog h) k₀)
    (hu : T.LabelsUnique h) (hwf : Func.Wf f.body)
    (hcallees : f.opt.ext.callees = []) (hexits : f.opt.ext.exits = [])
    (hFn : T.frameSize (f.nslots T.toIsa) ≤ n) (hn : n + T.raBytes ≤ 2 ^ 64) :
    T.FnSpec h f.name (Func.spec Γ f.body) n nX :=
  compileFn_correct h f Γ (fun _ => 0) n nX code k₀ hcomp hcode hu hwf hFn hn
    (by rw [hcallees]; intro _ hg; nomatch hg)
    (by rw [hexits]; intro _ hg; nomatch hg)

/-- Compiling and linking a list of functions (callees first). -/
theorem compile_correct {T : Target} (h : T.Host) (Γ : Env) (bound : String → Nat) (nX : Nat) :
    ∀ (fs : List Fn) (code : List T.Directive) (k₀ : Nat),
    compile T.toIsa fs = .ok code → code.IsInfixAt (T.prog h) k₀ → T.LabelsUnique h →
    (∀ (pre : List Fn) (f : Fn) (post : List Fn), fs = pre ++ f :: post →
      Func.Wf f.body ∧
      (∀ args m Q X, Γ f.name args m Q X → Func.spec Γ f.body args m Q X) ∧
      T.frameSize (f.nslots T.toIsa) ≤ bound f.name ∧
      bound f.name + T.raBytes ≤ 2 ^ 64 ∧
      (∀ g ∈ f.opt.ext.callees,
        (g ∈ pre.map Fn.name ∨ T.FnSpec h g (Γ g) (bound g) nX) ∧
        T.frameSize (f.nslots T.toIsa) + T.raBytes + bound g ≤ bound f.name) ∧
      (∀ g ∈ f.opt.ext.exits, T.Defined h g ∧ nX ≤ bound f.name)) →
    ∀ f ∈ fs, T.FnSpec h f.name (Γ f.name) (bound f.name) nX
  | [], _, _, _, _, _, _, f, hf => nomatch hf
  | f₀ :: fs, code, k₀, hcomp, hcode, hu, hstep, f, hf => by
    simp only [compile] at hcomp
    split at hcomp
    · rename_i c₀ cs hc₀ hcs
      simp only [Except.ok.injEq] at hcomp
      subst hcomp
      obtain ⟨hwf₀, hspec₀, hFn₀, hn₀, hcallees₀, hexits₀⟩ := hstep [] f₀ fs rfl
      have hf₀ : T.FnSpec h f₀.name (Γ f₀.name) (bound f₀.name) nX :=
        Target.FnSpec.of_spec T
          (compileFn_correct h f₀ Γ bound (bound f₀.name) nX c₀ k₀ hc₀ hcode.append.1 hu hwf₀
            hFn₀ hn₀
            (fun g hg => by
              obtain ⟨h1 | h1, h2⟩ := hcallees₀ g hg
              · nomatch h1
              · exact ⟨h1, h2⟩)
            hexits₀)
          hspec₀
      rcases List.mem_cons.mp hf with rfl | hf
      · exact hf₀
      · refine compile_correct h Γ bound nX fs cs (k₀ + c₀.length) hcs hcode.append.2 hu
          (fun pre f' post heq => ?_) f hf
        obtain ⟨hwf, hspec, hFn, hn, hcallees, hexits⟩ :=
          hstep (f₀ :: pre) f' post (by simp [heq])
        refine ⟨hwf, hspec, hFn, hn, fun g hg => ?_, hexits⟩
        obtain ⟨h1 | h1, h2⟩ := hcallees g hg
        · simp only [List.map_cons, List.mem_cons] at h1
          rcases h1 with rfl | h1
          · exact ⟨Or.inr hf₀, h2⟩
          · exact ⟨Or.inl h1, h2⟩
        · exact ⟨Or.inr h1, h2⟩
    · simp at hcomp
    · simp at hcomp

end LeanQbe
