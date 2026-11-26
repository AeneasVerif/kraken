module

public import LeanQbe.T.MainLemmas
public import LeanQbe.T.LinkRecLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.FlatLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Target-Generic Verification Kit (`BenchmarkCertKit`)

Arch-neutral separation-logic extraction, `LegalTarget.legalSig` helpers for `i64` signatures, and
single-function `FnSpec` wrapper shared across `Amd64` and `Arm64` certified modules (`0`
`Amd64`/`Arm64`/`Kraken.X64`/`Kraken.AArch64` imports).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.BenchmarkCertKit

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.LinkRec Kraken

/-- Extract the concrete heap chunk `m` satisfying `P m` from `dmem =⋆ P ⋆ F ⋆ R`. -/
theorem sep_extract_eq {dmem : Mem 64} {P F R : Mem 64 → Prop}
    (hmem : dmem =⋆ P ⋆ F ⋆ R) :
    ∃ m : Mem 64, P m ∧ (dmem =⋆ Eq m ⋆ F ⋆ R) := by
  obtain ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, hm, hf⟩, hmR⟩ := hmem
  exact ⟨m, hm, ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, rfl, hf⟩, hmR⟩⟩

theorem legalSig_singleton_i64_tys {lt : LegalTarget} (hi64 : lt.legalSig [i64] = [i64]) :
    lt.legalTys i64 = [i64] := by
  simpa only [LegalTarget.legalSig, List.append_nil] using hi64

theorem legalSig_two_i64 {lt : LegalTarget} (hi64 : lt.legalSig [i64] = [i64]) :
    lt.legalSig [i64, i64] = [i64, i64] := by
  simp only [LegalTarget.legalSig, legalSig_singleton_i64_tys hi64, List.cons_append,
    List.nil_append]

theorem legalSig_three_i64 {lt : LegalTarget} (hi64 : lt.legalSig [i64] = [i64]) :
    lt.legalSig [i64, i64, i64] = [i64, i64, i64] := by
  simp only [LegalTarget.legalSig, legalSig_singleton_i64_tys hi64, List.cons_append,
    List.nil_append]

/-- Generic closed `FnSpec` wrapper for single-function modules `{ fns := [f] }`. -/
theorem single_fnspec_gen {T : Target} {lt : LegalTarget} {maxBound : Nat}
    {f : Fn} {hints : List T.toIsa.Hints}
    (M : Compiled T lt [] [] 0 [f] hints maxBound)
    (hh : T.mach.Host) (Γ : Env)
    (hacyc : ({ fns := [f], externs := [], exits := [] } : Module).checkAcyclic = true)
    (hwf : f.Wf)
    (hsupp : (f.earlyOpt).body.supportsSource lt = true)
    (hwp : ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    (k₀ : Nat) (hc : M.code.IsInfixAt (T.mach.prog hh) k₀) (hu : T.LabelsUnique hh)
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X',
      Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X') :
    T.Defined hh f.name ∧ T.FnSpec hh f.name (Γ f.name f.as f.rs) (M.bound f.name) 0 :=
  M.fnSpec_noExit_id ⟨[f], [], []⟩ rfl hh Γ k₀ hc hu hacyc
    (fun g hg => by simp only [List.mem_singleton] at hg; subst hg; exact hwf)
    (fun g hg => by simp only [List.mem_singleton] at hg; subst hg; exact hsupp)
    (fun g hg => by simp only [List.mem_singleton] at hg; subst hg; exact hwp)
    List.mem_cons_self has hrs hnoex

/-- Target-generic concrete heap non-vacuous execution witness over `TargetInit.run_fnSpec`. -/
theorem run_sep_nonvacuous {T : Target} (I : TargetInit T 2048 8192)
    {lt : LegalTarget} {as : List Ty} {hints : List T.toIsa.Hints} {fns : List Fn}
    (M : Compiled T lt [] [] 0 fns hints 2048) {sym : Sym} {spec : Spec as []}
    (hfn : T.FnSpec M.host sym spec (M.bound sym) 0)
    (bytes : List UInt8) (xs : Tup Val as) (hlen : bytes.length ≤ 8192)
    (hargs : (T.toIsa.assignArgs as).isSome = true)
    {P : Mem 64 → Prop}
    (hspec : spec xs (bytes.At 0x1000#64) (fun _ m' => P m') (fun _ _ _ _ => False)) :
    Eventually (T.mach.step M.host)
      (fun st => T.mach.pc st = I.ra0 ∧
        (T.mach.mem (T.mach.data st) =⋆ P ⋆ T.Exit I.sp0 (M.bound sym) ⋆ emp))
      (T.mach.mkState (I.initState (M.bound sym) bytes xs) (T.mach.labelAddr M.host sym)) := by
  refine I.run_fnSpec M hfn bytes xs hlen hargs hspec ?_
  rintro st (⟨hpc, _, m', hP, _, hm'⟩ | ⟨_, _, _, _, hx, _⟩)
  · exact ⟨hpc, sep_mono (fun _ => sep_mono (fun _ e => e ▸ hP)) hm'⟩
  · exact hx.elim

end LeanQbe.T.BenchmarkCertKit
