module

public import LeanQbe.T.MainCertScc
public import LeanQbe.T.Notation
public import LeanQbe.T.Logic.Rules
public import LeanQbe.T.FlatLemmas
public import LeanQbeTest.T.MainTest
public meta import Lean
public meta import LeanQbe.T.MainCertScc
public meta import LeanQbeTest.T.RegaLitmusTarget

/-!
# Shared Recursive SCC Test Fixtures & Proof Helpers (`MainCertSccFixtures`)

Factoring shared target-neutral helpers for `MainCertSccTest` and `MainCertBudgetSccTest`:
* `botEnv`, `bv64_sub1_lt`, `bv64_sub1_toNat`, `compiledFrameBytes`, `renormFn`, `wf_of_map_renorm`
* `acyc_single_sem`: single-function `Chunk.acyc` semantic linking helper
* `budget_wp_mono`: monotonicity witness for `BudgetEnv.lfp_wf_mkSccOp`
* `litmus_fnSpec` / `litmus_ret1_exec`: `FnSpec` and `Eventually` wrappers on `litmusTarget`
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.MainCertSccFixtures

open LeanQbe.T LeanQbe.T.LinkRec LeanQbe.T.LinkScc
open LeanQbe.T.Notation LeanQbe.T.RegaLitmus LeanQbeTest.T.MainTest
open Std Std.ExtHashMap Kraken.Bedrock2.Test

def botEnv : Env :=
  fun _ _ _ _ _ _ _ => False

theorem bv64_sub1_lt {n : BitVec 64} (hne : n ≠ 0#64) :
    (n - 1#64).toNat < n.toNat := by
  have hnz : n.toNat ≠ 0 := fun h => hne (BitVec.eq_of_toNat_eq h)
  have hlt : n.toNat < 2 ^ 64 := n.isLt
  rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega

theorem bv64_sub1_toNat {n : BitVec 64} (hne : n ≠ 0#64) :
    (n - 1#64).toNat = n.toNat - 1 := by
  have hnz : n.toNat ≠ 0 := fun h => hne (BitVec.eq_of_toNat_eq h)
  have hlt : n.toNat < 2 ^ 64 := n.isLt
  rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega

def compiledFrameBytes (f : Fn) (h : litmusTarget.toIsa.Hints) : Nat :=
  Rega.effFrame litmusTarget.toIsa h (f.mid LegalTarget.aarch64).ext + litmusTarget.frame.raBytes

def renormFn (f : Fn) : Fn := ⟨f.name, f.as, f.rs, Func.renorm f.body⟩

theorem wf_of_map_renorm {fs : List Fn} (h : fs.map renormFn = fs) :
    ∀ f ∈ fs, f.Wf := by
  intro f hf
  rw [← h, List.mem_map] at hf
  rcases hf with ⟨g, _, rfl⟩
  exact Func.renorm_wf g.body

theorem acyc_single_sem {exits : List Sym} {bound : Nat}
    {c : Chunk litmusTarget LegalTarget.aarch64 exits bound} {exts : List SigEntry} {Γ : Env}
    {f : Fn} {nm : Sym}
    (hcm : ∃ cc, c = Chunk.acyc cc ∧ cc.fs = [f])
    (hnm : f.name = nm) (has : f.as = [i64]) (hrs : f.rs = [i64])
    (xs : Tup Val [i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (hwp : Func.wp (Env.extStep ⟨[f], externsOfSigs exts, exits⟩ Γ) f.body
      (has ▸ xs) m (fun r m' => Q (hrs ▸ r) m') X) :
    c.sem exts Γ nm [i64] [i64] xs m Q X := by
  rcases hcm with ⟨cc, hceq, hfs⟩
  subst hceq; subst hnm
  have hf : f ∈ cc.fs := by rw [hfs]; exact List.mem_cons_self
  have hsem : Env.semScc ⟨cc.fs, externsOfSigs exts, exits⟩ Γ f.name f.as f.rs
      (has ▸ xs) m (fun r m' => Q (hrs ▸ r) m') X := by
    dsimp only [Env.semScc]
    rw [Env.lfp_fix (sccOp_mono _ _), hfs]
    exact ⟨by simp [Fn.sig], f, List.mem_cons_self, rfl, rfl, rfl,
      wp_env_mono (fun _ _ _ _ _ _ _ h => Or.inr h) _ m hwp⟩
  have h := LinkedCertScc.acycChunk_sem_of_semScc cc hf hsem
  have castSem : ∀ (as bs : List Ty) (ha : as = [i64]) (hb : bs = [i64]),
      (Chunk.acyc cc).sem exts Γ f.name as bs (ha ▸ xs) m (fun r m' => Q (hb ▸ r) m') X →
      (Chunk.acyc cc).sem exts Γ f.name [i64] [i64] xs m Q X := by
    rintro _ _ rfl rfl hs; exact hs
  exact castSem f.as f.rs has hrs h

theorem budget_wp_mono :
    ∀ (bfn : BudgetFn) (C₁ C₂ T₁ T₂ : Env), Env.le C₁ C₂ → Env.le T₁ T₂ →
      ∀ (xs : Tup Val bfn.toFn.as) (m' : Mem 64) (Q' : Post bfn.toFn.rs) (X' : XPost),
        Func.wp C₁ bfn.toFn.body xs m' Q' X' → Func.wp C₂ bfn.toFn.body xs m' Q' X' :=
  fun bfn _ _ _ _ hC _ xs m' _ _ hwp => wp_env_mono hC (bfn.toFn.body Val Cont xs) m' hwp

theorem litmus_fnSpec {M : Module} {maxBound : Nat}
    (cert : LinkedCertScc litmusTarget litmusLayout LegalTarget.aarch64 litmusLabelClean
      M [] [] 0 maxBound [])
    (hwf : ∀ f ∈ M.fns, f.Wf) {f : Fn} (hf : f ∈ M.fns)
    (has : LegalTarget.aarch64.legalSig f.as = f.as)
    (hrs : LegalTarget.aarch64.legalSig f.rs = f.rs)
    (spec : Spec f.as f.rs)
    (hsem : ∀ xs m Q X, spec xs m Q X → cert.sem botEnv f.name f.as f.rs xs m Q X)
    (hnoex : ∀ args m Q X X', spec args m Q X → spec args m Q X' :=
      by intro _ _ _ _ _ h; exact h) :
    litmusTarget.Defined cert.host f.name ∧
      litmusTarget.FnSpec cert.host f.name spec (cert.bound f.name) 0 :=
  cert.fnSpec_host_src_of_le hwf (f := f) hf spec has hrs hnoex hsem

theorem litmus_ret1_exec {M : Module} {maxBound : Nat}
    (cert : LinkedCertScc litmusTarget litmusLayout LegalTarget.aarch64 litmusLabelClean
      M [] [] 0 maxBound [])
    (hwf : ∀ f ∈ M.fns, f.Wf) {f : Fn} (hf : f ∈ M.fns)
    (hret : f.rs = [i64])
    (has : LegalTarget.aarch64.legalSig f.as = f.as)
    (hrs : LegalTarget.aarch64.legalSig f.rs = f.rs)
    (spec : Spec f.as [i64])
    (hsem : ∀ xs m Q X, spec xs m Q X → cert.sem botEnv f.name f.as [i64] xs m Q X)
    (args : Tup Val f.as) (ret : BitVec 64)
    (hargs : (litmusTarget.toIsa.assignArgs f.as).isSome = true)
    (hspec : spec args (([] : List UInt8).At 0x1000#64) (fun r _ => r = (ret, ()))
      (fun _ _ _ _ => False))
    (hnoex : ∀ args m Q X X', spec args m Q X → spec args m Q X' :=
      by intro _ _ _ _ _ h; exact h)
    (hbound : maxBound ≤ 2048 := by omega) :
    Eventually (litmusTarget.mach.step cert.host)
      (fun st => litmusTarget.mach.pc st = litmusInit.ra0 ∧
        litmusTarget.mach.getGpr (litmusTarget.mach.data st) litmusInit.ret0 = ret)
      (litmusTarget.mach.mkState
        (litmusInit.initState (cert.bound f.name) [] args)
        (litmusTarget.mach.labelAddr cert.host f.name)) :=
  cert.eventually_ret1_i64_of_le litmusInit hwf (f := f) hf hret has hrs spec
    hnoex hsem [] args ret (by simp) hargs
    (Q := fun r _ => r = (ret, ())) hspec (fun _ _ h => h) hbound

end LeanQbeTest.T.MainCertSccFixtures