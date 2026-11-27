module

public import LeanQbe.T.LeanLCNF.Sem.E2E
public import LeanQbe.T.LeanLCNF.Sem.Tactic
public import LeanQbe.T.Bootstrap0.Splice0
public import LeanQbe.T.LeanLCNF.LcnfC0RecDemo
public import LeanQbe.T.LeanLCNF.LcnfC0TreeDemo
public import LeanQbeTest.T.LcnfPerceusTest
meta import Lean
meta import LeanQbe.T.LeanLCNF.Basic
meta import LeanQbe.T.LeanLCNF.Lower1
meta import LeanQbe.T.Bootstrap0.Splice0

/-!
# End-to-End LCNF `L5` Verification Demos (`LcnfE2EDemos`)

Target-parametric end-to-end compilation theorems (`lean_fn_compiled_{acyclic,loop,scc}`) and
pure symbolic-evaluation proofs (`lcnf_sim`, `lcnf_res_sim`) with ZERO hand-written Tier-H or
Tier-T WP across:
1. `E2EAddNat.addNat` (acyclic extracted Lean function)
2. `E2EFactAcc.factAcc` (self-tail extracted Lean function)
3. `RecDemo.listSum` (structurally recursive `List Nat` Lean function from `LcnfC0RecDemo`)
4. `TreeDemo.treeSum` & `TreeDemo.treeSize` (two-branch `Tree` Lean functions from `LcnfC0TreeDemo`)
5. `goodOsetMod` (FBIP `isShared`-guarded `oset` proved at Tier-P with `lcnf_sim` + `perceus_sound`)
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.LcnfE2EDemos

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.LeanLCNF.Sem

/-! ## 1. Standalone Extracted Lean Functions (`E2EAddNat`, `E2EFactAcc`) & WF Checks -/

namespace E2EAddNat

@[expose, noinline] def addNat (a b : Nat) : Nat := a + b

end E2EAddNat

namespace E2EFactAcc

@[expose, noinline] def factAcc (n acc : Nat) : Nat :=
  if _h : n = 0 then acc else factAcc (n - 1) (acc * n)
termination_by n

end E2EFactAcc

lcnf_of_lean! e2eAddNatLcMod [E2EAddNat.addNat]
splice_lcnf_tflat! e2eAddNatTfs e2eAddNatLcMod

lcnf_of_lean! e2eFactAccLcMod [E2EFactAcc.factAcc]
splice_lcnf_tflat! e2eFactAccTfs e2eFactAccLcMod

@[expose] def e2eAddNatProgMod : Module := lcnfProgMod e2eAddNatTfs
@[expose] def e2eAddNatLinkedMod : Module := linkLcnfWithRtC0 e2eAddNatTfs false
@[expose] def e2eAddNatName : Sym := "l_LeanQbeTest_T_LcnfE2EDemos_E2EAddNat_addNat"

@[expose] def e2eFactAccProgMod : Module := lcnfProgMod e2eFactAccTfs
@[expose] def e2eFactAccLinkedMod : Module := linkLcnfWithRtC0 e2eFactAccTfs false
@[expose] def e2eFactAccName : Sym := "l_LeanQbeTest_T_LcnfE2EDemos_E2EFactAcc_factAcc"

theorem e2eAddNat_wf :
    e2eAddNatLcMod.inFirstOrderFragment = true ∧
    RcCheck e2eAddNatLcMod = true ∧
    perceusModWf e2eAddNatLcMod = true ∧
    e2eAddNatLinkedMod.checkAcyclic = true := by
  refine ⟨by decide, by decide, by decide, by t_kernel_rfl⟩

theorem e2eFactAcc_wf :
    e2eFactAccLcMod.inFirstOrderFragment = true ∧
    RcCheck e2eFactAccLcMod = true ∧
    perceusModWf e2eFactAccLcMod = true ∧
    e2eFactAccLinkedMod.checkAcyclic = true := by
  refine ⟨by decide, by decide, by decide, by t_kernel_rfl⟩

theorem recDemo_wf :
    recDemoLcMod.inFirstOrderFragment = true ∧
    RcCheck recDemoLcMod = true ∧
    perceusModWf recDemoLcMod = true := by
  refine ⟨by decide, by decide, by decide⟩

theorem treeDemo_wf :
    treeDemoLcMod.inFirstOrderFragment = true ∧
    RcCheck treeDemoLcMod = true ∧
    perceusModWf treeDemoLcMod = true := by
  refine ⟨by decide, by decide, by decide⟩

theorem goodOset_wf :
    RcCheck LeanQbeTest.T.LcnfPerceusTest.goodOsetMod = true ∧
    perceusModWf LeanQbeTest.T.LcnfPerceusTest.goodOsetMod = true := by
  refine ⟨by decide, by decide⟩

/-! ## 2. Pure Symbolic Simulation on FBIP `goodOset` (`lcnf_sim` + `perceus_sound`) -/

theorem goodOset_pModuleOk_sim :
    PModuleOk LeanQbeTest.T.LcnfPerceusTest.goodOsetPEnv
      LeanQbeTest.T.LcnfPerceusTest.goodOsetMod := by
  intro d hd as Q _ _ ⟨_, x1, x2, y, has, hq⟩
  subst has
  rcases List.mem_singleton.mp hd with rfl
  lcnf_sim
  intro b
  cases b
  · lcnf_sim; exact hq
  · lcnf_sim; exact hq

/-- End-to-end `perceus_sound` proof for FBIP `isShared`-guarded `oset` (`goodOsetMod`) driven by
`lcnf_sim` in <15 lines. -/
theorem goodOset_perceus_sound :
    HModuleOk (hOfP LeanQbeTest.T.LcnfPerceusTest.goodOsetMod
        LeanQbeTest.T.LcnfPerceusTest.goodOsetPEnv)
      LeanQbeTest.T.LcnfPerceusTest.goodOsetMod :=
  perceus_sound (by decide) (by decide) goodOset_pModuleOk_sim

/-! ## 3. `E2EAddNat.addNat` (Acyclic End-to-End Target-Parametric Compilation) -/

@[expose] def e2eAddNatPEnv : PEnv :=
  fun fn pvs Q _ =>
    fn = "LeanQbeTest.T.LcnfE2EDemos.E2EAddNat.addNat" ∧
    ∃ a b : Nat, pvs = [PEnc.enc a, PEnc.enc b] ∧ Q (PEnc.enc (E2EAddNat.addNat a b))

@[expose] def e2eAddNatResEnv : PResEnv :=
  fun fn pvs rem wr rcr Pr _ =>
    fn = "LeanQbeTest.T.LcnfE2EDemos.E2EAddNat.addNat" ∧
    ∃ a b : Nat, E2EAddNat.addNat a b < 2 ^ 63 ∧
      pvs = [PEnc.enc a, PEnc.enc b] ∧ Pr (PEnc.enc (E2EAddNat.addNat a b)) rem wr rcr

private theorem e2eAddNat_pModuleOk : PModuleOk e2eAddNatPEnv e2eAddNatLcMod := by
  intro d hd pvs Q _ _ ⟨_, a, b, has, hq⟩
  subst has
  rcases List.mem_singleton.mp hd with rfl
  lcnf_sim
  exact hq

private theorem e2eAddNat_pResOk : PResOk e2eAddNatResEnv e2eAddNatLcMod := by
  intro d hd pvs rem wr rcr Pr _ _ ⟨_, a, b, hlt, has, hpr⟩
  subst has
  rcases List.mem_singleton.mp hd with rfl
  have hadd : a + b < 2 ^ 63 := hlt
  lcnf_res_sim
  exact hpr

private theorem e2eAddNat_lowerD :
    lowerDecl (firstOrderLEnv e2eAddNatLcMod) e2eAddNatLcMod.decls[0] = .ok e2eAddNatTfs.tf_0 := by
  t_kernel_rfl

/-- Target-parametric end-to-end compilation theorem for `E2EAddNat.addNat` (`lean_fn_compiled_acyclic`). -/
theorem e2eAddNat_compiled
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {maxB : Nat}
    (cert : LinkedCert T L lt hcl e2eAddNatLinkedMod [] rtExitSyms 64 maxB)
    (hleg : LegalSigAll lt e2eAddNatLinkedMod.fns) :
    T.Defined cert.host e2eAddNatName ∧
      T.FnSpec cert.host e2eAddNatName
        (encSpec2 (e2eAddNatLcMod.decls[0])
          (fun a b _ _ _ => E2EAddNat.addNat a b < 2 ^ 63) E2EAddNat.addNat)
        (cert.bound e2eAddNatName) 64 := by
  have hd : e2eAddNatLcMod.decls[0] ∈ e2eAddNatLcMod.decls := List.getElem_mem (by decide)
  have htf : e2eAddNatTfs.tf_0 ∈ e2eAddNatTfs := by simp [e2eAddNatTfs]
  have hlow : lowerModule e2eAddNatLcMod = .ok e2eAddNatTfs := e2eAddNatTfs_lower
  have hnoLoop : ∀ d ∈ e2eAddNatLcMod.decls,
      hasSelfTail d.name d.params.length d.body = false := by decide
  have hres := lean_fn_compiled_acyclic (m := e2eAddNatLcMod) (progTfs := e2eAddNatTfs)
    e2eAddNat_wf.1 e2eAddNat_wf.2.1 e2eAddNat_wf.2.2.1 hlow e2eAddNat_wf.2.2.2 hnoLoop
    e2eAddNat_pModuleOk cert hleg hd htf e2eAddNat_lowerD
    (PreP := fun pvs _ _ _ =>
      ∃ a b : Nat, pvs = [PEnc.enc a, PEnc.enc b] ∧ E2EAddNat.addNat a b < 2 ^ 63)
    (PostP := fun pvs r _ _ _ =>
      ∀ a b : Nat, pvs = [PEnc.enc a, PEnc.enc b] → r = PEnc.enc (E2EAddNat.addNat a b) ∧ True)
    e2eAddNat_pResOk
    (fun pvs rem₀ wr₀ rcr₀ ⟨a, b, hpvs, hlt⟩ =>
      ⟨fun r => r = PEnc.enc (E2EAddNat.addNat a b),
       fun r _ _ _ => r = PEnc.enc (E2EAddNat.addNat a b),
       ⟨rfl, a, b, hpvs, rfl⟩, ⟨rfl, a, b, hlt, hpvs, rfl⟩,
       fun r _ _ _ hr _ a' b' hpvs' => by
         rw [hpvs] at hpvs'
         obtain ⟨rfl, rfl⟩ := by simpa [PEnc.enc] using hpvs'
         exact ⟨hr, trivial⟩⟩)
    rfl rfl
  exact hres

/-! ## 4. `E2EFactAcc.factAcc` (Self-Tail End-to-End Target-Parametric Compilation) -/

@[expose] def e2eFact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * e2eFact n

private theorem e2eFact_pos (n : Nat) : 0 < e2eFact n := by
  induction n with
  | zero => decide
  | succ m ih => exact Nat.mul_pos (Nat.succ_pos m) ih

private theorem e2eFactAcc_spec_eq (n acc : Nat) :
    E2EFactAcc.factAcc n acc = e2eFact n * acc := by
  induction n generalizing acc with
  | zero => simp [E2EFactAcc.factAcc, e2eFact]
  | succ m ih =>
    unfold E2EFactAcc.factAcc
    split
    · omega
    · rw [Nat.add_sub_cancel, ih (acc * (m + 1))]
      dsimp only [e2eFact]
      rw [Nat.mul_comm acc (m + 1), ← Nat.mul_assoc, Nat.mul_comm (e2eFact m) (m + 1)]

@[expose] def e2eFactAccPEnv : Nat → PEnv
  | 0 => PEnv.bot
  | k + 1 => fun fn pvs Q _ =>
    fn = "LeanQbeTest.T.LcnfE2EDemos.E2EFactAcc.factAcc" ∧
    ∃ n acc : Nat, n < k + 1 ∧ pvs = [PEnc.enc n, PEnc.enc acc] ∧
      Q (PEnc.enc (E2EFactAcc.factAcc n acc))

@[expose] def e2eFactAccResEnv : Nat → PResEnv
  | 0 => PResEnv.bot
  | k + 1 => fun fn pvs rem wr rcr Pr _ =>
    fn = "LeanQbeTest.T.LcnfE2EDemos.E2EFactAcc.factAcc" ∧
    ∃ n acc : Nat,
      n < k + 1 ∧ n < 2 ^ 63 ∧ acc < 2 ^ 63 ∧ E2EFactAcc.factAcc n acc < 2 ^ 63 ∧
      pvs = [PEnc.enc n, PEnc.enc acc] ∧
      Pr (PEnc.enc (E2EFactAcc.factAcc n acc)) rem wr rcr

private theorem e2eFactAcc_pModuleOk : PModuleOkIdx e2eFactAccPEnv e2eFactAccLcMod := by
  refine ⟨?_, fun k d hd pvs Q _ _ hΔ => ?_⟩
  · intro k fn pvs Q X h
    cases k with
    | zero => exact False.elim h
    | succ k' =>
      rcases h with ⟨rfl, n, acc, hn, hpvs, hq⟩
      exact ⟨rfl, n, acc, Nat.lt_succ_of_lt hn, hpvs, hq⟩
  · rcases List.mem_singleton.mp hd with rfl
    cases k with
    | zero => exact False.elim hΔ
    | succ k' =>
      rcases hΔ with ⟨_, n, acc, hn, has, hq⟩
      subst has
      cases n with
      | zero => lcnf_sim; simpa [E2EFactAcc.factAcc] using hq
      | succ m =>
        lcnf_sim
        lcnf_call (fun r => r = PEnc.enc (E2EFactAcc.factAcc m (acc * (m + 1))))
        · cases k' with
          | zero => omega
          | succ k'' => exact ⟨rfl, m, acc * (m + 1), by omega, rfl, rfl⟩
        · intro r hr; rw [hr]; lcnf_sim
          have heq : E2EFactAcc.factAcc m (acc * (m + 1)) = E2EFactAcc.factAcc (m + 1) acc := by
            rw [e2eFactAcc_spec_eq, e2eFactAcc_spec_eq, e2eFact]
            rw [Nat.mul_comm acc (m + 1), ← Nat.mul_assoc, Nat.mul_comm (e2eFact m) (m + 1)]
          simpa [heq] using hq

private theorem e2eFactAcc_pResOk : PResOkIdx e2eFactAccResEnv e2eFactAccLcMod := by
  refine ⟨?_, fun k d hd pvs rem wr rcr Pr _ _ hΔ => ?_⟩
  · intro k fn pvs rem wr rcr Pr X h
    cases k with
    | zero => exact False.elim h
    | succ k' =>
      rcases h with ⟨rfl, n, acc, hn, hn63, hacc63, hres, hpvs, hpr⟩
      exact ⟨rfl, n, acc, Nat.lt_succ_of_lt hn, hn63, hacc63, hres, hpvs, hpr⟩
  · rcases List.mem_singleton.mp hd with rfl
    cases k with
    | zero => exact False.elim hΔ
    | succ k' =>
      rcases hΔ with ⟨_, n, acc, hn, hn63, hacc63, hres63, has, hpr⟩
      subst has
      cases n with
      | zero => lcnf_res_sim; simpa [E2EFactAcc.factAcc] using hpr
      | succ m =>
        have hmul_eq : E2EFactAcc.factAcc m (acc * (m + 1)) =
            E2EFactAcc.factAcc (m + 1) acc := by
          rw [e2eFactAcc_spec_eq, e2eFactAcc_spec_eq, e2eFact]
          rw [Nat.mul_comm acc (m + 1), ← Nat.mul_assoc, Nat.mul_comm (e2eFact m) (m + 1)]
        have hprod63 : acc * (m + 1) < 2 ^ 63 := by
          have h1 : E2EFactAcc.factAcc m (acc * (m + 1)) < 2 ^ 63 := hmul_eq ▸ hres63
          rw [e2eFactAcc_spec_eq] at h1
          have hle : acc * (m + 1) ≤ e2eFact m * (acc * (m + 1)) :=
            Nat.le_mul_of_pos_left _ (e2eFact_pos m)
          omega
        lcnf_res_sim
        lcnf_res_call (fun r rem' wr' rcr' =>
          r = PEnc.enc (E2EFactAcc.factAcc m (acc * (m + 1))) ∧
          rem' = rem ∧ wr' = wr ∧ rcr' = rcr)
        · cases k' with
          | zero => omega
          | succ k'' =>
            exact ⟨rfl, m, acc * (m + 1), by omega, by omega, hprod63,
              hmul_eq ▸ hres63, rfl, rfl, rfl, rfl, rfl⟩
        · intro r _ _ _ ⟨hr, rfl, rfl, rfl⟩
          rw [hr]; lcnf_res_sim
          simpa [hmul_eq] using hpr

private theorem e2eFactAcc_lowerD :
    lowerDecl (firstOrderLEnv e2eFactAccLcMod) e2eFactAccLcMod.decls[0] =
      .ok e2eFactAccTfs.tf_0 := by
  t_kernel_rfl

/-- Target-parametric end-to-end compilation theorem for self-tail `E2EFactAcc.factAcc`
(`lean_fn_compiled_loop`). -/
theorem e2eFactAcc_compiled
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {maxB : Nat}
    (cert : LinkedCert T L lt hcl e2eFactAccLinkedMod [] rtExitSyms 64 maxB)
    (hleg : LegalSigAll lt e2eFactAccLinkedMod.fns) (nBound : Nat) :
    T.Defined cert.host e2eFactAccName ∧
      T.FnSpec cert.host e2eFactAccName
        (encSpec2 (e2eFactAccLcMod.decls[0])
          (fun n acc _ _ _ => n ≤ nBound ∧ n < 2 ^ 63 ∧ acc < 2 ^ 63 ∧
            E2EFactAcc.factAcc n acc < 2 ^ 63)
          E2EFactAcc.factAcc)
        (cert.bound e2eFactAccName) 64 := by
  have hd : e2eFactAccLcMod.decls[0] ∈ e2eFactAccLcMod.decls := List.getElem_mem (by decide)
  have htf : e2eFactAccTfs.tf_0 ∈ e2eFactAccTfs := by simp [e2eFactAccTfs]
  have hlow : lowerModule e2eFactAccLcMod = .ok e2eFactAccTfs := e2eFactAccTfs_lower
  exact lean_fn_compiled_loop (m := e2eFactAccLcMod) (progTfs := e2eFactAccTfs)
    e2eFactAcc_wf.1 e2eFactAcc_wf.2.1 e2eFactAcc_wf.2.2.1 hlow e2eFactAcc_wf.2.2.2
    e2eFactAcc_pModuleOk (nBound + 1) cert hleg hd htf e2eFactAcc_lowerD
    (PreP := fun pvs _ _ _ =>
      ∃ n acc : Nat, pvs = [PEnc.enc n, PEnc.enc acc] ∧
        n ≤ nBound ∧ n < 2 ^ 63 ∧ acc < 2 ^ 63 ∧ E2EFactAcc.factAcc n acc < 2 ^ 63)
    (PostP := fun pvs r _ _ _ =>
      ∀ n acc : Nat, pvs = [PEnc.enc n, PEnc.enc acc] →
        r = PEnc.enc (E2EFactAcc.factAcc n acc) ∧ True)
    e2eFactAcc_pResOk
    (fun pvs rem₀ wr₀ rcr₀ ⟨n, acc, hpvs, hn, hn63, hacc63, hres⟩ =>
      ⟨fun r => r = PEnc.enc (E2EFactAcc.factAcc n acc),
       fun r _ _ _ => r = PEnc.enc (E2EFactAcc.factAcc n acc),
       ⟨rfl, n, acc, Nat.lt_succ_of_le hn, hpvs, rfl⟩,
       ⟨rfl, n, acc, Nat.lt_succ_of_le hn, hn63, hacc63, hres, hpvs, rfl⟩,
       fun r _ _ _ hr _ n' acc' hpvs' => by
         rw [hpvs] at hpvs'
         obtain ⟨rfl, rfl⟩ := by simpa [PEnc.enc] using hpvs'
         exact ⟨hr, trivial⟩⟩)
    rfl rfl

/-! ## 5. `RecDemo.listSum` (Structurally Recursive `LinkedCertScc` E2E Compilation) -/

@[expose] def listSumPEnv : Nat → PEnv
  | 0 => PEnv.bot
  | k + 1 => fun fn pvs Q _ =>
    fn = "LeanQbe.T.LeanLCNF.RecDemo.listSum" ∧
    ∃ xs : List Nat, xs.length < k + 1 ∧ pvs = [PEnc.enc xs] ∧
      Q (PEnc.enc (RecDemo.listSum xs))

@[expose] def listSumResEnv : Nat → PResEnv
  | 0 => PResEnv.bot
  | k + 1 => fun fn pvs rem wr rcr Pr _ =>
    fn = "LeanQbe.T.LeanLCNF.RecDemo.listSum" ∧
    ∃ xs : List Nat,
      xs.length < k + 1 ∧ RecDemo.listSum xs < 2 ^ 63 ∧ pvs = [PEnc.enc xs] ∧
      Pr (PEnc.enc (RecDemo.listSum xs)) rem wr rcr

private theorem listSum_pModuleOk : PModuleOkIdx listSumPEnv recDemoLcMod := by
  refine ⟨?_, fun k d hd pvs Q _ _ hΔ => ?_⟩
  · intro k fn pvs Q X h
    cases k with
    | zero => exact False.elim h
    | succ k' =>
      rcases h with ⟨rfl, xs, hx, hpvs, hq⟩
      exact ⟨rfl, xs, Nat.lt_succ_of_lt hx, hpvs, hq⟩
  · rcases List.mem_singleton.mp hd with rfl
    cases k with
    | zero => exact False.elim hΔ
    | succ k' =>
      rcases hΔ with ⟨_, xs, hlen, has, hq⟩
      subst has
      cases xs with
      | nil => lcnf_sim; exact hq
      | cons x rest =>
        lcnf_sim
        lcnf_call (fun r => r = PEnc.enc (RecDemo.listSum rest))
        · cases k' with
          | zero => simp only [List.length_cons] at hlen; omega
          | succ k'' =>
            exact ⟨rfl, rest, by simp only [List.length_cons] at hlen; omega, rfl, rfl⟩
        · intro r hr; rw [hr]; lcnf_sim; exact hq

private theorem listSum_pResOk : PResOkIdx listSumResEnv recDemoLcMod := by
  refine ⟨?_, fun k d hd pvs rem wr rcr Pr _ _ hΔ => ?_⟩
  · intro k fn pvs rem wr rcr Pr X h
    cases k with
    | zero => exact False.elim h
    | succ k' =>
      rcases h with ⟨rfl, xs, hx, hsum, hpvs, hpr⟩
      exact ⟨rfl, xs, Nat.lt_succ_of_lt hx, hsum, hpvs, hpr⟩
  · rcases List.mem_singleton.mp hd with rfl
    cases k with
    | zero => exact False.elim hΔ
    | succ k' =>
      rcases hΔ with ⟨_, xs, hlen, hsum63, has, hpr⟩
      subst has
      cases xs with
      | nil => lcnf_res_sim; exact hpr
      | cons x rest =>
        have hsum_def : RecDemo.listSum (x :: rest) = x + RecDemo.listSum rest := rfl
        have hadd63 : x + RecDemo.listSum rest < 2 ^ 63 := hsum_def ▸ hsum63
        have hrest63 : RecDemo.listSum rest < 2 ^ 63 := by omega
        have hx63 : x < 2 ^ 63 := by omega
        lcnf_res_sim
        lcnf_res_call (fun r rem' wr' rcr' =>
          r = PEnc.enc (RecDemo.listSum rest) ∧ rem' = rem ∧ wr' = wr ∧ rcr' = rcr)
        · cases k' with
          | zero => simp only [List.length_cons] at hlen; omega
          | succ k'' =>
            exact ⟨rfl, rest, by simp only [List.length_cons] at hlen; omega,
              hrest63, rfl, rfl, rfl, rfl, rfl⟩
        · intro r _ _ _ ⟨hr, rfl, rfl, rfl⟩
          rw [hr]; lcnf_res_sim
          exact hpr

private theorem recDemo_lowerD :
    lowerDecl (firstOrderLEnv recDemoLcMod) recDemoLcMod.decls[0] = .ok recDemoTfs.tf_0 := by
  t_kernel_rfl

private theorem listNat_enc_inj {xs ys : List Nat}
    (h : ([PEnc.enc xs] : List PVal) = [PEnc.enc ys]) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => simp [PEnc.enc, PVal.ofList] at h
  | cons x xs ih =>
    cases ys with
    | nil => simp [PEnc.enc, PVal.ofList] at h
    | cons y ys =>
      change ([PVal.ctor 1 [.nat x, PVal.ofList (xs.map PEnc.enc)] []] : List PVal) =
        [PVal.ctor 1 [.nat y, PVal.ofList (ys.map PEnc.enc)] []] at h
      injection h with h0
      injection h0 with _ h1
      injection h1 with hx h2
      injection h2 with hrest
      injection hx with hx'
      subst hx'
      exact congrArg (x :: ·) (ih (congrArg ([·]) hrest))

/-- Target-parametric end-to-end compilation theorem for structurally recursive `RecDemo.listSum`
via `lean_fn_compiled_scc`. -/
theorem recDemo_listSum_compiled
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {maxBound maxBrt : Nat}
    (cert : LinkedCertScc T L lt hcl recDemoLinkedMod [] rtExitSyms 64 maxBound [])
    (rtCert : LinkedCert T L lt hcl rtC0CoreMod [] rtExitSyms 64 maxBrt)
    (hcalls_rt : checkChunksCalls rtExitSyms [] (rtCert.chunks.map Chunk.acyc) = true)
    (hchunks : ∃ (maxB : Nat) (ext : List (SigEntry × Nat)) (hints : List T.toIsa.Hints)
      (exportBounds : List (Sym × Nat))
      (cbr : CompiledBudgetRec T lt ext rtExitSyms 64 [recDemoListSumBudgetFn] hints
        maxB exportBounds),
      cert.chunks =
        (rtCert.chunks.map Chunk.acyc ++ []) ++
          [Chunk.recBudgetSCC ext [recDemoListSumBudgetFn] hints maxB exportBounds cbr])
    (hwf_linked : ∀ f ∈ recDemoLinkedMod.fns, f.Wf)
    (hk_bound : recDemoMinEntry + recDemoDepthBudget * recDemoMaxFrame ≤
      cert.bound recDemoListSumName)
    (has : lt.legalSig recDemoListSumFn.as = recDemoListSumFn.as)
    (hrs : lt.legalSig recDemoListSumFn.rs = recDemoListSumFn.rs) :
    T.Defined cert.host recDemoListSumName ∧
      T.FnSpec cert.host recDemoListSumName
        (encSpec1 (recDemoLcMod.decls[0])
          (fun xs _ _ _ => xs.length < recDemoDepthBudget ∧ RecDemo.listSum xs < 2 ^ 63)
          RecDemo.listSum)
        (cert.bound recDemoListSumName) 64 := by
  rcases hchunks with ⟨maxB, ext, hints, exportBounds, cbr, hchunks⟩
  have hd : recDemoLcMod.decls[0] ∈ recDemoLcMod.decls := List.getElem_mem (by decide)
  have hf_linked : recDemoListSumBudgetFn.toFn ∈ recDemoLinkedMod.fns := by
    simp [recDemoLinkedMod, linkLcnfWithRtC0_fns_eq, lcnfProgMod, recDemoTfs,
      Frontend.C0.tflatFnsToFns, recDemoListSumBudgetFn, recDemoListSumFn]
  let reqB (k : Nat) : Nat := recDemoMinEntry + k * recDemoMaxFrame
  have hk_bd : reqB recDemoDepthBudget ≤ cert.bound recDemoListSumName := hk_bound
  exact lean_fn_compiled_scc cert rtCert hcalls_rt cbr [] [] hchunks hwf_linked
    recDemo_wf.1 recDemo_wf.2.1 recDemo_wf.2.2 listSum_pModuleOk recDemoDepthBudget reqB
    (fun bfn hbfn => by
      rcases List.mem_singleton.mp hbfn with rfl
      exact ⟨_, hd, recDemoTfs.tf_0, recDemo_lowerD, rfl⟩)
    (fun bfn hbfn idx sb hsb => by
      rcases List.mem_singleton.mp hbfn with rfl
      refine ⟨by
          dsimp [reqB, recDemoListSumBudgetFn, recDemoMaxFrame, recDemoMinEntry] at hsb ⊢
          omega,
        by dsimp [reqB, recDemoListSumBudgetFn, recDemoMinEntry] at hsb ⊢; omega,
        fun j hj => by
          dsimp [reqB, recDemoListSumBudgetFn, recDemoMaxFrame, recDemoMinEntry] at hsb ⊢
          have hj_le : j + 1 ≤ idx := hj
          have hmul : (j + 1) * 32 ≤ idx * 32 := Nat.mul_le_mul_right 32 hj_le
          omega⟩)
    (fun j d₀ hd₀ => by
      rcases List.mem_singleton.mp hd₀ with rfl
      exact Or.inl List.mem_cons_self)
    hd recDemo_lowerD List.mem_cons_self rfl hf_linked hk_bd (by simp [sccChunksFns]) has hrs
    (PreP := fun pvs _ _ _ =>
      ∃ xs : List Nat, pvs = [PEnc.enc xs] ∧
        xs.length < recDemoDepthBudget ∧ RecDemo.listSum xs < 2 ^ 63)
    (PostP := fun pvs r _ _ _ =>
      ∀ xs : List Nat, pvs = [PEnc.enc xs] → r = PEnc.enc (RecDemo.listSum xs) ∧ True)
    listSum_pResOk
    (fun pvs rem₀ wr₀ rcr₀ ⟨xs, hpvs, hlen, hsum⟩ =>
      ⟨fun r => r = PEnc.enc (RecDemo.listSum xs),
       fun r _ _ _ => r = PEnc.enc (RecDemo.listSum xs),
       ⟨rfl, xs, by simp [recDemoDepthBudget] at hlen ⊢; exact hlen, hpvs, rfl⟩,
       ⟨rfl, xs, by simp [recDemoDepthBudget] at hlen ⊢; exact hlen, hsum, hpvs, rfl⟩,
       fun r _ _ _ hr _ xs' hpvs' => by
         rw [hpvs] at hpvs'
         obtain rfl := listNat_enc_inj hpvs'
         exact ⟨hr, trivial⟩⟩)
    rfl rfl

/-! ## 6. `TreeDemo.{treeSum, treeSize}` (`LinkedCertScc` Two-Branch E2E Compilation) -/

@[expose] def encTree : TreeDemo.Tree → PVal
  | .leaf => .ctor 0 [] []
  | .node v l r => .ctor 1 [PEnc.enc v, encTree l, encTree r] []

instance : PEnc TreeDemo.Tree where
  enc := encTree
  lcTy := .tobject

private theorem tree_enc_inj {t₁ t₂ : TreeDemo.Tree}
    (h : ([PEnc.enc t₁] : List PVal) = [PEnc.enc t₂]) : t₁ = t₂ := by
  induction t₁ generalizing t₂ with
  | leaf =>
    cases t₂ with
    | leaf => rfl
    | node _ _ _ => simp [PEnc.enc, encTree] at h
  | node v₁ l₁ r₁ ihl ihr =>
    cases t₂ with
    | leaf => simp [PEnc.enc, encTree] at h
    | node v₂ l₂ r₂ =>
      change ([PVal.ctor 1 [.nat v₁, encTree l₁, encTree r₁] []] : List PVal) =
        [PVal.ctor 1 [.nat v₂, encTree l₂, encTree r₂] []] at h
      injection h with h0
      injection h0 with _ h1
      injection h1 with hv h2
      injection h2 with hl h3
      injection h3 with hr _
      injection hv with hv'
      subst hv'
      obtain rfl := ihl (congrArg ([·]) hl)
      obtain rfl := ihr (congrArg ([·]) hr)
      rfl

@[expose] def treeSumPEnv : Nat → PEnv
  | 0 => PEnv.bot
  | k + 1 => fun fn pvs Q _ =>
    fn = "LeanQbe.T.LeanLCNF.TreeDemo.treeSum" ∧
    ∃ t : TreeDemo.Tree, t.depth < k + 1 ∧ pvs = [PEnc.enc t] ∧
      Q (PEnc.enc (TreeDemo.treeSum t))

@[expose] def treeSumResEnv : Nat → PResEnv
  | 0 => PResEnv.bot
  | k + 1 => fun fn pvs rem wr rcr Pr _ =>
    fn = "LeanQbe.T.LeanLCNF.TreeDemo.treeSum" ∧
    ∃ t : TreeDemo.Tree,
      t.depth < k + 1 ∧ TreeDemo.treeSum t < 2 ^ 63 ∧ pvs = [PEnc.enc t] ∧
      Pr (PEnc.enc (TreeDemo.treeSum t)) rem wr rcr

private theorem treeSum_pModuleOk : PModuleOkIdx treeSumPEnv treeDemoLcMod := by
  refine ⟨?_, fun k d hd pvs Q _ _ hΔ => ?_⟩
  · intro k fn pvs Q X h
    cases k with
    | zero => exact False.elim h
    | succ k' =>
      rcases h with ⟨rfl, t, ht, hpvs, hq⟩
      exact ⟨rfl, t, Nat.lt_succ_of_lt ht, hpvs, hq⟩
  · cases k with
    | zero =>
      rcases List.mem_cons.mp hd with rfl | hd1
      · exact False.elim hΔ
      · rcases List.mem_singleton.mp hd1 with rfl; exact False.elim hΔ
    | succ k' =>
      rcases List.mem_cons.mp hd with rfl | hd1
      · rcases hΔ with ⟨_, t, ht, has, hq⟩
        subst has
        cases t with
        | leaf => lcnf_sim; exact hq
        | node v l r =>
          lcnf_sim
          cases k' with
          | zero => simp [TreeDemo.Tree.depth] at ht
          | succ k'' =>
            have hdl : l.depth < k'' + 1 := by simp [TreeDemo.Tree.depth] at ht; omega
            have hdr : r.depth < k'' + 1 := by simp [TreeDemo.Tree.depth] at ht; omega
            lcnf_call (fun res => res = PEnc.enc (TreeDemo.treeSum l))
            · exact ⟨rfl, l, hdl, rfl, rfl⟩
            · intro resL hrl; rw [hrl]; lcnf_sim
              lcnf_call (fun res => res = PEnc.enc (TreeDemo.treeSum r))
              · exact ⟨rfl, r, hdr, rfl, rfl⟩
              · intro resR hrr; rw [hrr]; lcnf_sim; exact hq
      · rcases List.mem_singleton.mp hd1 with rfl
        have hname : treeDemoLcMod.d1.name = "LeanQbe.T.LeanLCNF.TreeDemo.treeSize" := rfl
        rw [hname] at hΔ
        exact absurd hΔ.1 (by decide)

private theorem treeSum_pResOk : PResOkIdx treeSumResEnv treeDemoLcMod := by
  refine ⟨?_, fun k d hd pvs rem wr rcr Pr _ _ hΔ => ?_⟩
  · intro k fn pvs rem wr rcr Pr X h
    cases k with
    | zero => exact False.elim h
    | succ k' =>
      rcases h with ⟨rfl, t, ht, hsum, hpvs, hpr⟩
      exact ⟨rfl, t, Nat.lt_succ_of_lt ht, hsum, hpvs, hpr⟩
  · cases k with
    | zero =>
      rcases List.mem_cons.mp hd with rfl | hd1
      · exact False.elim hΔ
      · rcases List.mem_singleton.mp hd1 with rfl; exact False.elim hΔ
    | succ k' =>
      rcases List.mem_cons.mp hd with rfl | hd1
      · rcases hΔ with ⟨_, t, ht, hsum63, has, hpr⟩
        subst has
        cases t with
        | leaf => lcnf_res_sim; exact hpr
        | node v l r =>
          have hsum_def : TreeDemo.treeSum (.node v l r) =
              v + TreeDemo.treeSum l + TreeDemo.treeSum r := rfl
          have hadd2 : v + TreeDemo.treeSum l + TreeDemo.treeSum r < 2 ^ 63 := hsum_def ▸ hsum63
          have hvl63 : v + TreeDemo.treeSum l < 2 ^ 63 := by omega
          have hl63 : TreeDemo.treeSum l < 2 ^ 63 := by omega
          have hr63 : TreeDemo.treeSum r < 2 ^ 63 := by omega
          have hv63 : v < 2 ^ 63 := by omega
          lcnf_res_sim
          cases k' with
          | zero => simp [TreeDemo.Tree.depth] at ht
          | succ k'' =>
            have hdl' : l.depth < k'' + 1 := by simp [TreeDemo.Tree.depth] at ht; omega
            have hdr' : r.depth < k'' + 1 := by simp [TreeDemo.Tree.depth] at ht; omega
            lcnf_res_call (fun r0 rem' wr' rcr' =>
              r0 = PEnc.enc (TreeDemo.treeSum l) ∧ rem' = rem ∧ wr' = wr ∧ rcr' = rcr)
            · exact ⟨rfl, l, hdl', hl63, rfl, rfl, rfl, rfl, rfl⟩
            · intro r0 rem0 wr0 rcr0 ⟨hr0, hrem0, hwr0, rcr0_eq⟩
              rw [hr0, hrem0, hwr0, rcr0_eq]; lcnf_res_sim
              lcnf_res_call (fun r1 rem' wr' rcr' =>
                r1 = PEnc.enc (TreeDemo.treeSum r) ∧ rem' = rem ∧ wr' = wr ∧ rcr' = rcr)
              · exact ⟨rfl, r, hdr', hr63, rfl, rfl, rfl, rfl, rfl⟩
              · intro r1 rem1 wr1 rcr1 ⟨hr1, hrem1, hwr1, hrcr1⟩
                rw [hr1, hrem1, hwr1, hrcr1]; lcnf_res_sim; exact hpr
      · rcases List.mem_singleton.mp hd1 with rfl
        have hname : treeDemoLcMod.d1.name = "LeanQbe.T.LeanLCNF.TreeDemo.treeSize" := rfl
        rw [hname] at hΔ
        exact absurd hΔ.1 (by decide)

@[expose] def treeSizePEnv : Nat → PEnv
  | 0 => PEnv.bot
  | k + 1 => fun fn pvs Q _ =>
    fn = "LeanQbe.T.LeanLCNF.TreeDemo.treeSize" ∧
    ∃ t : TreeDemo.Tree, t.depth < k + 1 ∧ pvs = [PEnc.enc t] ∧
      Q (PEnc.enc (TreeDemo.treeSize t))

@[expose] def treeSizeResEnv : Nat → PResEnv
  | 0 => PResEnv.bot
  | k + 1 => fun fn pvs rem wr rcr Pr _ =>
    fn = "LeanQbe.T.LeanLCNF.TreeDemo.treeSize" ∧
    ∃ t : TreeDemo.Tree,
      t.depth < k + 1 ∧ TreeDemo.treeSize t < 2 ^ 63 ∧ pvs = [PEnc.enc t] ∧
      Pr (PEnc.enc (TreeDemo.treeSize t)) rem wr rcr

private theorem treeSize_pModuleOk : PModuleOkIdx treeSizePEnv treeDemoLcMod := by
  refine ⟨?_, fun k d hd pvs Q _ _ hΔ => ?_⟩
  · intro k fn pvs Q X h
    cases k with
    | zero => exact False.elim h
    | succ k' =>
      rcases h with ⟨rfl, t, ht, hpvs, hq⟩
      exact ⟨rfl, t, Nat.lt_succ_of_lt ht, hpvs, hq⟩
  · cases k with
    | zero =>
      rcases List.mem_cons.mp hd with rfl | hd1
      · exact False.elim hΔ
      · rcases List.mem_singleton.mp hd1 with rfl; exact False.elim hΔ
    | succ k' =>
      rcases List.mem_cons.mp hd with rfl | hd1
      · have hname : treeDemoLcMod.d0.name = "LeanQbe.T.LeanLCNF.TreeDemo.treeSum" := rfl
        rw [hname] at hΔ
        exact absurd hΔ.1 (by decide)
      · rcases List.mem_singleton.mp hd1 with rfl
        rcases hΔ with ⟨_, t, ht, has, hq⟩
        subst has
        cases t with
        | leaf => lcnf_sim; exact hq
        | node _ l r =>
          lcnf_sim
          cases k' with
          | zero => simp [TreeDemo.Tree.depth] at ht
          | succ k'' =>
            have hdl : l.depth < k'' + 1 := by simp [TreeDemo.Tree.depth] at ht; omega
            have hdr : r.depth < k'' + 1 := by simp [TreeDemo.Tree.depth] at ht; omega
            lcnf_call (fun res => res = PEnc.enc (TreeDemo.treeSize l))
            · exact ⟨rfl, l, hdl, rfl, rfl⟩
            · intro resL hrl; rw [hrl]; lcnf_sim
              lcnf_call (fun res => res = PEnc.enc (TreeDemo.treeSize r))
              · exact ⟨rfl, r, hdr, rfl, rfl⟩
              · intro resR hrr; rw [hrr]; lcnf_sim; exact hq

private theorem treeSize_pResOk : PResOkIdx treeSizeResEnv treeDemoLcMod := by
  refine ⟨?_, fun k d hd pvs rem wr rcr Pr _ _ hΔ => ?_⟩
  · intro k fn pvs rem wr rcr Pr X h
    cases k with
    | zero => exact False.elim h
    | succ k' =>
      rcases h with ⟨rfl, t, ht, hsz, hpvs, hpr⟩
      exact ⟨rfl, t, Nat.lt_succ_of_lt ht, hsz, hpvs, hpr⟩
  · cases k with
    | zero =>
      rcases List.mem_cons.mp hd with rfl | hd1
      · exact False.elim hΔ
      · rcases List.mem_singleton.mp hd1 with rfl; exact False.elim hΔ
    | succ k' =>
      rcases List.mem_cons.mp hd with rfl | hd1
      · have hname : treeDemoLcMod.d0.name = "LeanQbe.T.LeanLCNF.TreeDemo.treeSum" := rfl
        rw [hname] at hΔ
        exact absurd hΔ.1 (by decide)
      · rcases List.mem_singleton.mp hd1 with rfl
        rcases hΔ with ⟨_, t, ht, hsz63, has, hpr⟩
        subst has
        cases t with
        | leaf => lcnf_res_sim; exact hpr
        | node v l r =>
          have hsz_def : TreeDemo.treeSize (.node v l r) =
              1 + TreeDemo.treeSize l + TreeDemo.treeSize r := rfl
          have hadd2 : 1 + TreeDemo.treeSize l + TreeDemo.treeSize r < 2 ^ 63 := hsz_def ▸ hsz63
          have h1l63 : 1 + TreeDemo.treeSize l < 2 ^ 63 := by omega
          have hl63 : TreeDemo.treeSize l < 2 ^ 63 := by omega
          have hr63 : TreeDemo.treeSize r < 2 ^ 63 := by omega
          lcnf_res_sim
          cases k' with
          | zero => simp [TreeDemo.Tree.depth] at ht
          | succ k'' =>
            have hdl' : l.depth < k'' + 1 := by simp [TreeDemo.Tree.depth] at ht; omega
            have hdr' : r.depth < k'' + 1 := by simp [TreeDemo.Tree.depth] at ht; omega
            lcnf_res_call (fun r0 rem' wr' rcr' =>
              r0 = PEnc.enc (TreeDemo.treeSize l) ∧ rem' = rem ∧ wr' = wr ∧ rcr' = rcr)
            · exact ⟨rfl, l, hdl', hl63, rfl, rfl, rfl, rfl, rfl⟩
            · intro r0 rem0 wr0 rcr0 ⟨hr0, hrem0, hwr0, hrcr0⟩
              rw [hr0, hrem0, hwr0, hrcr0]; lcnf_res_sim
              lcnf_res_call (fun r1 rem' wr' rcr' =>
                r1 = PEnc.enc (TreeDemo.treeSize r) ∧ rem' = rem ∧ wr' = wr ∧ rcr' = rcr)
              · exact ⟨rfl, r, hdr', hr63, rfl, rfl, rfl, rfl, rfl⟩
              · intro r1 rem1 wr1 rcr1 ⟨hr1, hrem1, hwr1, hrcr1⟩
                rw [hr1, hrem1, hwr1, hrcr1]; lcnf_res_sim; exact hpr

private theorem liftDeclSpec_hOfPIdx_false {m : LcModule} {Δp : Nat → PEnv}
    (hnd : (m.decls.map (·.name)).Nodup) {k : Nat} {d₀ : LcDecl} (hd₀ : d₀ ∈ m.decls)
    (hbot : ∀ pvs Q X, Δp k d₀.name pvs Q X → False)
    {xs : Tup Val (i64 :: (d₀.params.map (·.ty.toTTy)).take regArgs)}
    {mem : Mem 64} {Q : Post [d₀.retTy.toTTy]} {X : XPost}
    (h : liftDeclSpec (hOfPIdx m Δp k d₀.name) d₀.params d₀.retTy xs mem Q X) : False := by
  rcases h with ⟨_, _, _, _, _, rt, d', Δr, pvs, extH, ghostH, rem₀, wr₀, rcr₀,
    Qp, Xp, Pr, Er, hd', hnm', _, _, _, _, _, hdp, _⟩
  obtain rfl := mod_decl_unique hnd hd₀ hd' hnm'
  exact hbot _ _ _ hdp

private theorem treeDemo_lowerD0 :
    lowerDecl (firstOrderLEnv treeDemoLcMod) treeDemoLcMod.decls[0] = .ok treeDemoTfs.tf_0 := by
  t_kernel_rfl

private theorem treeDemo_lowerD1 :
    lowerDecl (firstOrderLEnv treeDemoLcMod) treeDemoLcMod.decls[1] = .ok treeDemoTfs.tf_1 := by
  t_kernel_rfl

/-- Target-parametric end-to-end compilation theorem for two-branch `TreeDemo.treeSum` via
`lean_fn_compiled_scc`. -/
theorem treeDemo_treeSum_compiled
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {maxBound maxBrt : Nat}
    (cert : LinkedCertScc T L lt hcl treeDemoLinkedMod [] rtExitSyms 64 maxBound [])
    (rtCert : LinkedCert T L lt hcl rtC0CoreMod [] rtExitSyms 64 maxBrt)
    (hcalls_rt : checkChunksCalls rtExitSyms [] (rtCert.chunks.map Chunk.acyc) = true)
    (hchunks : ∃ (maxB1 maxB2 : Nat) (ext1 ext2 : List (SigEntry × Nat))
      (hints1 hints2 : List T.toIsa.Hints)
      (cbr1 : CompiledBudgetRec T lt ext1 rtExitSyms 64 [treeDemoSumBudgetFn] hints1
        maxB1 treeDemoExportBounds)
      (cbr2 : CompiledBudgetRec T lt ext2 rtExitSyms 64 [treeDemoSizeBudgetFn] hints2
        maxB2 treeDemoExportBounds),
      cert.chunks =
        (rtCert.chunks.map Chunk.acyc ++ []) ++
          [Chunk.recBudgetSCC ext1 [treeDemoSumBudgetFn] hints1
            maxB1 treeDemoExportBounds cbr1,
           Chunk.recBudgetSCC ext2 [treeDemoSizeBudgetFn] hints2
            maxB2 treeDemoExportBounds cbr2])
    (hwf_linked : ∀ f ∈ treeDemoLinkedMod.fns, f.Wf)
    (hk_bound : treeDemoMinEntry + treeDemoDepthBudget * treeDemoMaxFrame ≤
      cert.bound treeDemoSumName)
    (has : lt.legalSig treeDemoSumFn.as = treeDemoSumFn.as)
    (hrs : lt.legalSig treeDemoSumFn.rs = treeDemoSumFn.rs) :
    T.Defined cert.host treeDemoSumName ∧
      T.FnSpec cert.host treeDemoSumName
        (encSpec1 (treeDemoLcMod.decls[0])
          (fun t _ _ _ => t.depth < treeDemoDepthBudget ∧ TreeDemo.treeSum t < 2 ^ 63)
          TreeDemo.treeSum)
        (cert.bound treeDemoSumName) 64 := by
  rcases hchunks with ⟨maxB1, maxB2, ext1, ext2, hints1, hints2, cbr1, cbr2, hchunks⟩
  let ch2 : Chunk T lt rtExitSyms 64 :=
    Chunk.recBudgetSCC ext2 [treeDemoSizeBudgetFn] hints2 maxB2 treeDemoExportBounds cbr2
  have hnot2 : treeDemoSumName ∉ (sccChunksFns [ch2]).map Fn.name := by
    simp only [ch2, sccChunksFns, Chunk.fns, List.append_nil, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false]
    decide
  have hd0 : treeDemoLcMod.decls[0] ∈ treeDemoLcMod.decls := List.getElem_mem (by decide)
  have hf_linked : treeDemoSumBudgetFn.toFn ∈ treeDemoLinkedMod.fns := by
    simp [treeDemoLinkedMod, linkLcnfWithRtC0_fns_eq, lcnfProgMod, treeDemoTfs,
      Frontend.C0.tflatFnsToFns, treeDemoSumBudgetFn, treeDemoSumFn]
  let reqB (k : Nat) : Nat := treeDemoMinEntry + k * treeDemoMaxFrame
  exact lean_fn_compiled_scc cert rtCert hcalls_rt cbr1 [] [ch2] hchunks hwf_linked
    treeDemo_wf.1 treeDemo_wf.2.1 treeDemo_wf.2.2 treeSum_pModuleOk treeDemoDepthBudget reqB
    (fun bfn hbfn => by
      rcases List.mem_singleton.mp hbfn with rfl
      exact ⟨_, hd0, treeDemoTfs.tf_0, treeDemo_lowerD0, rfl⟩)
    (fun bfn hbfn idx sb hsb => by
      rcases List.mem_singleton.mp hbfn with rfl
      refine ⟨by
          dsimp [reqB, treeDemoSumBudgetFn, treeDemoMaxFrame, treeDemoMinEntry] at hsb ⊢
          omega,
        by dsimp [reqB, treeDemoSumBudgetFn, treeDemoMinEntry] at hsb ⊢; omega,
        fun j hj => by
          dsimp [reqB, treeDemoSumBudgetFn, treeDemoMaxFrame, treeDemoMinEntry] at hsb ⊢
          have hmul : (j + 1) * 48 ≤ idx * 48 := Nat.mul_le_mul_right 48 hj
          omega⟩)
    (fun j d₀ hd₀ => by
      rcases List.mem_cons.mp hd₀ with rfl | hd1
      · exact Or.inl List.mem_cons_self
      · rcases List.mem_singleton.mp hd1 with rfl
        refine Or.inr fun _ _ _ _ h => absurd ?_ id
        exact liftDeclSpec_hOfPIdx_false (by decide) hd₀ (fun _ _ _ hdp => by
          have hname : treeDemoLcMod.d1.name = "LeanQbe.T.LeanLCNF.TreeDemo.treeSize" := rfl
          rw [hname] at hdp
          cases j with
          | zero => exact hdp
          | succ _ => exact absurd hdp.1 (by decide)) h)
    hd0 treeDemo_lowerD0 List.mem_cons_self rfl hf_linked hk_bound hnot2 has hrs
    (PreP := fun pvs _ _ _ =>
      ∃ t : TreeDemo.Tree, pvs = [PEnc.enc t] ∧
        t.depth < treeDemoDepthBudget ∧ TreeDemo.treeSum t < 2 ^ 63)
    (PostP := fun pvs r _ _ _ =>
      ∀ t : TreeDemo.Tree, pvs = [PEnc.enc t] → r = PEnc.enc (TreeDemo.treeSum t) ∧ True)
    treeSum_pResOk
    (fun pvs rem₀ wr₀ rcr₀ ⟨t, hpvs, ht, hsum⟩ =>
      ⟨fun r => r = PEnc.enc (TreeDemo.treeSum t),
       fun r _ _ _ => r = PEnc.enc (TreeDemo.treeSum t),
       ⟨rfl, t, by simp [treeDemoDepthBudget] at ht ⊢; exact ht, hpvs, rfl⟩,
       ⟨rfl, t, by simp [treeDemoDepthBudget] at ht ⊢; exact ht, hsum, hpvs, rfl⟩,
       fun r _ _ _ hr _ t' hpvs' => by
         rw [hpvs] at hpvs'
         obtain rfl := tree_enc_inj hpvs'
         exact ⟨hr, trivial⟩⟩)
    rfl rfl

/-- Target-parametric end-to-end compilation theorem for two-branch `TreeDemo.treeSize` via
`lean_fn_compiled_scc`. -/
theorem treeDemo_treeSize_compiled
    {T : Target} {L : TargetLayout T} {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {maxBound maxBrt : Nat}
    (cert : LinkedCertScc T L lt hcl treeDemoLinkedMod [] rtExitSyms 64 maxBound [])
    (rtCert : LinkedCert T L lt hcl rtC0CoreMod [] rtExitSyms 64 maxBrt)
    (hcalls_rt : checkChunksCalls rtExitSyms [] (rtCert.chunks.map Chunk.acyc) = true)
    (hchunks : ∃ (maxB2 : Nat) (ext2 : List (SigEntry × Nat)) (hints2 : List T.toIsa.Hints)
      (cbr1 : Chunk T lt rtExitSyms 64)
      (cbr2 : CompiledBudgetRec T lt ext2 rtExitSyms 64 [treeDemoSizeBudgetFn] hints2
        maxB2 treeDemoExportBounds),
      cert.chunks =
        rtCert.chunks.map Chunk.acyc ++
          [cbr1, Chunk.recBudgetSCC ext2 [treeDemoSizeBudgetFn] hints2
            maxB2 treeDemoExportBounds cbr2])
    (hwf_linked : ∀ f ∈ treeDemoLinkedMod.fns, f.Wf)
    (hk_bound : treeDemoMinEntry + treeDemoDepthBudget * treeDemoMaxFrame ≤
      cert.bound treeDemoSizeName)
    (has : lt.legalSig treeDemoSizeFn.as = treeDemoSizeFn.as)
    (hrs : lt.legalSig treeDemoSizeFn.rs = treeDemoSizeFn.rs) :
    T.Defined cert.host treeDemoSizeName ∧
      T.FnSpec cert.host treeDemoSizeName
        (encSpec1 (treeDemoLcMod.decls[1])
          (fun t _ _ _ => t.depth < treeDemoDepthBudget ∧ TreeDemo.treeSize t < 2 ^ 63)
          TreeDemo.treeSize)
        (cert.bound treeDemoSizeName) 64 := by
  rcases hchunks with ⟨maxB2, ext2, hints2, cbr1, cbr2, hchunks_flat⟩
  have hchunks : cert.chunks =
      (rtCert.chunks.map Chunk.acyc ++ [cbr1]) ++
        [Chunk.recBudgetSCC ext2 [treeDemoSizeBudgetFn] hints2
          maxB2 treeDemoExportBounds cbr2] := by
    simpa [List.append_assoc] using hchunks_flat
  have hd1 : treeDemoLcMod.decls[1] ∈ treeDemoLcMod.decls := List.getElem_mem (by decide)
  have hf_linked : treeDemoSizeBudgetFn.toFn ∈ treeDemoLinkedMod.fns := by
    simp [treeDemoLinkedMod, linkLcnfWithRtC0_fns_eq, lcnfProgMod, treeDemoTfs,
      Frontend.C0.tflatFnsToFns, treeDemoSizeBudgetFn, treeDemoSizeFn]
  let reqB (k : Nat) : Nat := treeDemoMinEntry + k * treeDemoMaxFrame
  exact lean_fn_compiled_scc cert rtCert hcalls_rt cbr2 [cbr1] [] hchunks hwf_linked
    treeDemo_wf.1 treeDemo_wf.2.1 treeDemo_wf.2.2 treeSize_pModuleOk treeDemoDepthBudget reqB
    (fun bfn hbfn => by
      rcases List.mem_singleton.mp hbfn with rfl
      exact ⟨_, hd1, treeDemoTfs.tf_1, treeDemo_lowerD1, rfl⟩)
    (fun bfn hbfn idx sb hsb => by
      rcases List.mem_singleton.mp hbfn with rfl
      refine ⟨by
          dsimp [reqB, treeDemoSizeBudgetFn, treeDemoMaxFrame, treeDemoMinEntry] at hsb ⊢
          omega,
        by dsimp [reqB, treeDemoSizeBudgetFn, treeDemoMinEntry] at hsb ⊢; omega,
        fun j hj => by
          dsimp [reqB, treeDemoSizeBudgetFn, treeDemoMaxFrame, treeDemoMinEntry] at hsb ⊢
          have hmul : (j + 1) * 48 ≤ idx * 48 := Nat.mul_le_mul_right 48 hj
          omega⟩)
    (fun j d₀ hd₀ => by
      rcases List.mem_cons.mp hd₀ with rfl | hd_rest
      · refine Or.inr fun _ _ _ _ h => absurd ?_ id
        exact liftDeclSpec_hOfPIdx_false (by decide) hd₀ (fun _ _ _ hdp => by
          have hname : treeDemoLcMod.d0.name = "LeanQbe.T.LeanLCNF.TreeDemo.treeSum" := rfl
          rw [hname] at hdp
          cases j with
          | zero => exact hdp
          | succ _ => exact absurd hdp.1 (by decide)) h
      · rcases List.mem_singleton.mp hd_rest with rfl
        exact Or.inl List.mem_cons_self)
    hd1 treeDemo_lowerD1 List.mem_cons_self rfl hf_linked hk_bound (by simp [sccChunksFns]) has hrs
    (PreP := fun pvs _ _ _ =>
      ∃ t : TreeDemo.Tree, pvs = [PEnc.enc t] ∧
        t.depth < treeDemoDepthBudget ∧ TreeDemo.treeSize t < 2 ^ 63)
    (PostP := fun pvs r _ _ _ =>
      ∀ t : TreeDemo.Tree, pvs = [PEnc.enc t] → r = PEnc.enc (TreeDemo.treeSize t) ∧ True)
    treeSize_pResOk
    (fun pvs rem₀ wr₀ rcr₀ ⟨t, hpvs, ht, hsz⟩ =>
      ⟨fun r => r = PEnc.enc (TreeDemo.treeSize t),
       fun r _ _ _ => r = PEnc.enc (TreeDemo.treeSize t),
       ⟨rfl, t, by simp [treeDemoDepthBudget] at ht ⊢; exact ht, hpvs, rfl⟩,
       ⟨rfl, t, by simp [treeDemoDepthBudget] at ht ⊢; exact ht, hsz, hpvs, rfl⟩,
       fun r _ _ _ hr _ t' hpvs' => by
         rw [hpvs] at hpvs'
         obtain rfl := tree_enc_inj hpvs'
         exact ⟨hr, trivial⟩⟩)
    rfl rfl

theorem recDemoLinkedMod_fns_wf : ∀ f ∈ recDemoLinkedMod.fns, f.Wf := by
  intro f hf
  simp only [recDemoLinkedMod, linkLcnfWithRtC0, List.mem_append] at hf
  rcases hf with hrt | hprog
  · exact rtC0CoreMod_fns_wf f hrt
  · obtain ⟨tf, _, rfl⟩ := List.mem_map.mp hprog
    exact tf.toFn_wf

theorem treeDemoLinkedMod_fns_wf : ∀ f ∈ treeDemoLinkedMod.fns, f.Wf := by
  intro f hf
  simp only [treeDemoLinkedMod, linkLcnfWithRtC0, List.mem_append] at hf
  rcases hf with hrt | hprog
  · exact rtC0CoreMod_fns_wf f hrt
  · obtain ⟨tf, _, rfl⟩ := List.mem_map.mp hprog
    exact tf.toFn_wf

end LeanQbeTest.T.LcnfE2EDemos
