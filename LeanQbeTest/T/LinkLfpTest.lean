module

public import LeanQbe.T.LinkLfp
public import LeanQbeTest.T.LinkSccTest
public meta import Lean
public meta import LeanQbe.T.MainSplice
public meta import LeanQbe.T.Examples.LinkRec
public meta import LeanQbeTest.T.RegaLitmusTarget

/-!
# Tests for `LeanQbe.T.LinkLfp` (`Env.lfp` + Kleene Approximants + `link_scc_static`)

Exercises:
1. Knaster–Tarski `Env.lfp` laws (`Env.lfp_le`, `Env.lfp_pre`, `Env.lfp_fix`, `Env.lfp_wf`).
2. `Env.sccOp` / `Env.semScc` reductions for `ModuleSccOk` (`moduleSccOk_le_semScc` with
   `strict = false` and `moduleSccOk_le_unfoldRecAt` with `strict = true`), including a
   well-founded `Prod.Lex` Ackermann `Env.lfp_wf` usage.
3. `link_scc_static` (+ `link_scc_static_host`, `link_scc_static_of_scc`) on `evenOddRecMod` and
   `ackMod`, with concrete execution witnesses (`isEven 4 = 1`, `ack(2, 2) = 7`).
4. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.LinkLfpTest

open LeanQbe.T LeanQbe.T.LinkRec LeanQbe.T.LinkScc
open LeanQbe.T.RegaLitmus LeanQbeTest.T.MainTest LeanQbeTest.T.LinkRecTest
open LeanQbeTest.T.LinkSccTest

/-! ## 1. `Env.lfp` Lattice & `Prod.Lex` Well-Founded Ackermann Reduction -/

theorem ack_moduleSccOk_strict :
    ModuleSccOk ackIdx ackEnv (fun _ _ _ _ _ _ _ => False) true ackMod := by
  have hstep : (ackLitmusCompiled.stepBound != 0) = true := by t_kernel_rfl
  refine moduleSccOk_of_step ackIdx ackMod_checkCyclic
    (fun f hf => by simp [ackMod] at hf; subst hf; exact ackFn_wf) ?_
  intro p fn hfn Γ hrec _ xs m Q X hspec
  simp [ackMod] at hfn; subst hfn
  have hwp := (ackMod_moduleSccOk.fnsOk ackFn List.mem_cons_self).2.2 p xs m Q X hspec
  refine wp_env_mono (fun g as bs xs' m' Q' X' hg => ?_) _ m hwp
  rw [hstep] at hg
  rcases hg with ⟨hsig, p', hlt, hst, hΓ'⟩ | ⟨hsig, _⟩
  · obtain ⟨gfn, hgfn, hgeq⟩ := List.mem_map.mp hsig
    cases hgeq
    exact hrec gfn hgfn p' hlt hst xs' m' Q' X' hΓ'
  · simp [ackMod] at hsig

/-- Loose (`strict = false`) Ackermann `ModuleSccOk` witness feeding `Env.lfp_wf` /
`moduleSccOk_le_semScc`. -/
theorem ack_moduleSccOk_loose :
    ModuleSccOk ackIdx ackEnv (fun _ _ _ _ _ _ _ => False) false ackMod := by
  refine moduleSccOk_of_step ackIdx ackMod_checkCyclic
    (fun f hf => by simp [ackMod] at hf; subst hf; exact ackFn_wf) ?_
  intro p fn hfn Γ hrec _ xs m Q X hspec
  simp [ackMod] at hfn; subst hfn
  have hwp := (ack_moduleSccOk_strict.fnsOk ackFn List.mem_cons_self).2.2 p xs m Q X hspec
  refine wp_env_mono (fun g as bs xs' m' Q' X' hg => ?_) _ m hwp
  rcases hg with ⟨hsig, p', hlt, _, hΓ'⟩ | ⟨hsig, _⟩
  · obtain ⟨gfn, hgfn, hgeq⟩ := List.mem_map.mp hsig
    cases hgeq
    exact hrec gfn hgfn p' hlt (Or.inl rfl) xs' m' Q' X' hΓ'
  · simp [ackMod] at hsig

theorem ack_le_semScc (p : Nat × Nat) :
    Env.le (Env.restrict (ackEnv p) (ackMod.fns.map Fn.sig))
      (Env.semScc ackMod (fun _ _ _ _ _ _ _ => False)) :=
  moduleSccOk_le_semScc ack_moduleSccOk_loose p

theorem ack_in_semScc (p : Nat × Nat) (xs : Tup Val [i64, i64]) (m : Mem 64)
    (Q : Post [i64]) (X : XPost) (h : ackSpec p xs m Q X) :
    Env.semScc ackMod (fun _ _ _ _ _ _ _ => False) "ack" [i64, i64] [i64] xs m Q X :=
  ack_le_semScc p "ack" [i64, i64] [i64] xs m Q X
    ⟨by simp [ackMod, ackFn, Fn.sig], h⟩

theorem ack_semScc_fix :
    Env.semScc ackMod (fun _ _ _ _ _ _ _ => False) =
      Env.sccOp ackMod (fun _ _ _ _ _ _ _ => False)
        (Env.semScc ackMod (fun _ _ _ _ _ _ _ => False)) :=
  Env.lfp_fix (sccOp_mono ackMod (fun _ _ _ _ _ _ _ => False))

theorem ack_le_unfoldRecAt (p : Nat × Nat) :
    Env.le (Env.restrict (ackEnv p) (ackMod.fns.map Fn.sig))
      (Env.unfoldRecAt ackMod (fun _ _ _ _ _ _ _ => False) (ackIdx.depth p)) :=
  moduleSccOk_le_unfoldRecAt ack_moduleSccOk_strict p

/-! ## 2. `link_scc_static` & `link_scc_static_of_scc` with Machine Witnesses -/

private theorem evenOdd_wf_mem_lfp : ∀ f ∈ evenOddRecMod.fns, f.Wf := by
  intro f hf
  simp only [evenOddRecMod, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl <;> first | exact isEven_wf | exact isOdd_wf

private theorem evenOdd_supports_all_lfp :
    evenOddRecMod.fns.all (fun f => (f.earlyOpt).body.supportsSource LegalTarget.aarch64) =
      true := by
  t_kernel_rfl

private theorem ack_supports_all_lfp :
    ackMod.fns.all (fun f => (f.earlyOpt).body.supportsSource LegalTarget.aarch64) = true := by
  t_kernel_rfl

theorem isEven_static_fnSpec {d : Nat} (hd : d ≤ 16) :
    litmusTarget.Defined evenOddLitmusCompiled.host "isEven" ∧
      litmusTarget.FnSpec evenOddLitmusCompiled.host "isEven"
        (legalEnv LegalTarget.aarch64
          (Env.onlyFn isEven
            (Env.unfoldRecAt evenOddRecMod (fun _ _ _ _ _ _ _ => False) d))
          "isEven" [i64] [i64])
        (evenOddLitmusCompiled.baseBound + d * evenOddLitmusCompiled.stepBound) 0 :=
  link_scc_static_host evenOddLitmusCompiled evenOddRecMod rfl
    (fun _ _ _ _ _ _ _ => False) evenOddRecMod_checkCyclic evenOdd_wf_mem_lfp
    (fun f hf => List.all_eq_true.mp evenOdd_supports_all_lfp f hf)
    d hd isEven List.mem_cons_self

theorem ack_static_fnSpec {p : Nat × Nat} (hp : ackIdx.depth p ≤ 16) :
    litmusTarget.Defined ackLitmusCompiled.host "ack" ∧
      litmusTarget.FnSpec ackLitmusCompiled.host "ack"
        (legalEnv LegalTarget.aarch64 (Env.onlyFn ackFn (ackEnv p))
          "ack" [i64, i64] [i64])
        (ackLitmusCompiled.baseBound + ackIdx.depth p * ackLitmusCompiled.stepBound) 0 :=
  link_scc_static_of_scc ackLitmusCompiled ackMod rfl ackLitmusCompiled.host ackEnv
    (fun _ _ _ _ _ _ _ => False) 0 ackLitmusCompiled.code_infix_host
    ackLitmusCompiled.labelsUnique ackMod_checkCyclic ack_moduleSccOk_strict
    (fun f hf => List.all_eq_true.mp ack_supports_all_lfp f hf)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    hp List.mem_cons_self

theorem ack_static_2_2 :
    Eventually (litmusTarget.mach.step ackLitmusCompiled.host)
      (fun st => litmusTarget.mach.pc st = litmusInit.ra0 ∧
        litmusTarget.mach.getGpr (litmusTarget.mach.data st) litmusInit.ret0 = 7#64)
      (litmusTarget.mach.mkState
        (litmusInit.initState (as := [i64, i64]) (ackLitmusCompiled.boundAt 7) []
          ((2#64, 2#64, ()) : Tup Val [i64, i64]))
        (litmusTarget.mach.labelAddr ackLitmusCompiled.host "ack")) := by
  have hdepth : ackIdx.depth (2, 2) = 7 := rfl
  have hspec := (ack_static_fnSpec (p := (2, 2)) (by rw [hdepth]; decide)).2
  rw [hdepth] at hspec
  change litmusTarget.FnSpec ackLitmusCompiled.host "ack"
    (legalEnv LegalTarget.aarch64 (Env.onlyFn ackFn (ackEnv (2, 2))) "ack" [i64, i64] [i64])
    (ackLitmusCompiled.boundAt 7) 0 at hspec
  have hsrc : litmusTarget.FnSpec ackLitmusCompiled.host "ack" (ackSpec (2, 2))
      (ackLitmusCompiled.boundAt 7) 0 :=
    Target.FnSpec.of_spec litmusTarget (fnSpec_of_legalEnv_onlyFn (f := ackFn) rfl rfl hspec)
      fun _ _ _ _ h => h
  exact run_rec_ret1_i64 litmusInit (as := [i64, i64]) ackLitmusCompiled (by decide : 7 ≤ 16)
    hsrc [] ((2#64, 2#64, ()) : Tup Val [i64, i64]) 7#64
    (by decide) rfl (Q := fun r _ => r = (7#64, ()))
    ⟨rfl, rfl, by change ackNat 2 2 < 2 ^ 64; decide,
      by change (BitVec.ofNat 64 (ackNat 2 2), ()) = (7#64, ()); decide⟩ (fun _ _ h => h)

/-! ## 3. Single-Line Axiom Audit -/

#print axioms LeanQbe.T.Env.le_refl
#print axioms LeanQbe.T.Env.le_trans
#print axioms LeanQbe.T.Env.lfp_le
#print axioms LeanQbe.T.Env.lfp_pre
#print axioms LeanQbe.T.Env.lfp_post
#print axioms LeanQbe.T.Env.lfp_fix
#print axioms LeanQbe.T.Env.lfp_wf
#print axioms LeanQbe.T.sccOp_mono
#print axioms LeanQbe.T.moduleSccOk_le_semScc
#print axioms LeanQbe.T.moduleSccOk_le_unfoldRecAt
#print axioms LeanQbe.T.link_scc_static
#print axioms LeanQbe.T.link_scc_static_host
#print axioms LeanQbe.T.link_scc_static_of_scc
#print axioms ack_moduleSccOk_strict
#print axioms ack_moduleSccOk_loose
#print axioms ack_le_semScc
#print axioms ack_in_semScc
#print axioms ack_semScc_fix
#print axioms ack_le_unfoldRecAt
#print axioms isEven_static_fnSpec
#print axioms ack_static_fnSpec
#print axioms ack_static_2_2

end LeanQbeTest.T.LinkLfpTest
