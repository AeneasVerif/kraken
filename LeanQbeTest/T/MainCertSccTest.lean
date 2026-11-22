module

public import LeanQbe.T.MainCertScc
public import LeanQbe.T.Notation
public import LeanQbe.T.Logic.Rules
public import LeanQbeTest.T.MainTest
public meta import Lean
public meta import LeanQbe.T.MainCertScc
public meta import LeanQbeTest.T.RegaLitmusTarget

/-!
# Smoke, Linking, & Axiom Audit Test for Stage 1 (`LinkDepthLfp` + `MainLinkScc` + `MainCertScc`)

1. Pure `LinkDepthLfp` tests: `DepthEnv.lfp_le`, `DepthEnv.lfp_closed`, `DepthEnv.lfp_fix`,
   `DepthEnv.lfp_mono`, `DepthEnv.lfp_depth_mono`, `DepthEnv.lfp_wf_mkSccOp` on both a
   `d = 0` tail-only `DepthEnv.lfp_tailOnly_zero_eq` example and a `d > 0` mixed non-tail +
   tail example, plus `DepthEnv.semScc_le_envSemScc` and `DepthEnv.semScc_le_unfoldRecAt`.
2. `MainLinkScc` + `MainCertScc` tests (`litmusTarget`, zero arch crate imports):
   * Mixed module `[fnInc1 (.acyc), fnSum (self-rec), fnEven, fnOdd (mutual-rec), fnTop (.acyc)]`
     compiled via `compile_linked_scc!` at `chunkSize := 1` (multi-subchunk `RecSubChunk` +
     `linkRecSubchunks`) and `chunkSize := 4`, plus custom `(fuels := ...)`, `ofLinkedCert`,
     `append`, direct `compileCheckedRecLit`, and negative validation `#guard`s.
   * Closed semantic linking against `cert.sem` + `DepthEnv.lfp_wf_mkSccOp`, and concrete
     `litmusInit` `Eventually` execution (`fnSum(5) = 15`, `fnEven(4) = 1`, `fnTop(5) = 16`).
3. Single-line `< 115` char `#print axioms` strictly `⊆ [propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.MainCertSccTest

open LeanQbe.T LeanQbe.T.LinkRec LeanQbe.T.LinkScc
open LeanQbe.T.Notation LeanQbe.T.RegaLitmus LeanQbeTest.T.MainTest
open Std Std.ExtHashMap Kraken.Bedrock2.Test

def botEnv : Env :=
  fun _ _ _ _ _ _ _ => False

/-! ## 1. Pure `LinkDepthLfp` (`d = 0` Tail-Only, `d > 0` Mixed, and Bridges) -/

/-- Pure `d = 0` tail-only two-slot operator: ignores `Γcall`, routes `"cnt"` calls through
`Γtail`, returning `0` at base case `0` and tail-calling `(n - 1)` otherwise. -/
def tailOnlyOp₂ (_Γcall Γtail : Env) : Env :=
  fun f as bs xs m Q X =>
    f = "cnt" ∧ ∃ (ha : as = [i64]) (hb : bs = [i64]),
      let n : BitVec 64 := (ha ▸ xs).1
      if n = 0#64 then Q (hb ▸ (0#64, ())) m
      else Γtail "cnt" [i64] [i64] (n - 1#64, ()) m (fun r m' => Q (hb ▸ r) m') X

theorem tailOnlyOp₂_biMono : Env.BiMono tailOnlyOp₂ := by
  rintro C₁ C₂ T₁ T₂ _ hT f as bs xs m Q X ⟨rfl, ha, hb, h⟩
  refine ⟨rfl, ha, hb, ?_⟩
  dsimp only at h ⊢
  split at h <;> rename_i hc
  · simp [hc, h]
  · simp only [hc, ↓reduceIte]; exact hT _ _ _ _ _ _ _ h

private theorem bv64_sub1_lt {n : BitVec 64} (hne : n ≠ 0#64) :
    (n - 1#64).toNat < n.toNat := by
  have hnz : n.toNat ≠ 0 := fun h => hne (BitVec.eq_of_toNat_eq h)
  have hlt : n.toNat < 2 ^ 64 := n.isLt
  rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega

private theorem bv64_sub1_toNat {n : BitVec 64} (hne : n ≠ 0#64) :
    (n - 1#64).toNat = n.toNat - 1 := by
  have hnz : n.toNat ≠ 0 := fun h => hne (BitVec.eq_of_toNat_eq h)
  have hlt : n.toNat < 2 ^ 64 := n.isLt
  rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega

def cntMod : Module :=
  ⟨[⟨"cnt", [i64], [i64], fun _ _ (n, ()) => .ret (.var n, ())⟩], [], []⟩

def tailOnlySpec (k : Nat) : Env :=
  fun f as bs xs m Q _ =>
    f = "cnt" ∧ ∃ (ha : as = [i64]) (hb : bs = [i64]),
      (ha ▸ xs).1.toNat ≤ k ∧ Q (hb ▸ (0#64, ())) m

/-- **Test 1a (`d = 0` tail-only `DepthEnv.lfp_wf`):** proves all iterations live at `d = 0`
using `lt j i ∧ depth j ≤ depth i` with `depth _ := 0`, and equates to flat `Env.lfp` via
`DepthEnv.lfp_tailOnly_zero_eq`. -/
theorem tailOnly_zero_lfp_wf (k : Nat) :
    Env.le (Env.restrict (tailOnlySpec k) (cntMod.fns.map Fn.sig))
      (DepthEnv.lfp (DepthEnv.mkSccOp cntMod botEnv tailOnlyOp₂) 0) :=
  DepthEnv.lfp_wf_mkSccOp Nat.lt_wfRel.wf (fun _ => 0) cntMod botEnv tailOnlyOp₂_biMono
    tailOnlySpec (fun i _ Γtail _ _ htail _ f as bs xs m Q X ⟨hsig, heq, ha, hb, hk, hQ⟩ => by
      subst heq; subst ha; subst hb
      dsimp only at hk hQ
      refine ⟨rfl, rfl, rfl, ?_⟩
      by_cases h0 : xs.1 = 0#64
      · simp [h0, hQ]
      · simp only [h0, ↓reduceIte]
        have hlt : (xs.1 - 1#64).toNat < i := by
          have := bv64_sub1_lt h0; omega
        exact htail (xs.1 - 1#64).toNat hlt (Nat.le_refl 0) "cnt" [i64] [i64]
          (xs.1 - 1#64, ()) m (fun r m' => Q r m') X
          ⟨hsig, rfl, rfl, rfl, Nat.le_refl _, hQ⟩) k

theorem tailOnly_zero_eq_flat :
    DepthEnv.lfp (DepthEnv.mkSccOp cntMod botEnv tailOnlyOp₂) 0 =
      Env.lfp (fun Γ => tailOnlyOp₂ (Env.extStep cntMod botEnv) (Env.sccStep cntMod Γ botEnv)) :=
  DepthEnv.lfp_tailOnly_zero_eq cntMod botEnv tailOnlyOp₂_biMono (fun _ _ _ => rfl)

/-- **Test 1b (`d > 0` mixed non-tail + tail `DepthEnv.lfp_wf_mkSccOp`):**
* `"wrap"` makes a depth-preserving tail call (`n ≤ n`) to `"rec"`.
* `"rec"` makes a depth-decreasing non-tail call (`n - 1 < n`) to `"wrap"`.
Exercises BOTH `lt j i ∧ depth j < depth i` (`Γcall`) and `lt j i ∧ depth j ≤ depth i`
(`Γtail`) simultaneously! -/
def mixedOp₂ (Γcall Γtail : Env) : Env :=
  fun f as bs xs m Q X =>
    ∃ (ha : as = [i64]) (hb : bs = [i64]),
      let n : BitVec 64 := (ha ▸ xs).1
      (f = "wrap" ∧ Γtail "rec" [i64] [i64] (n, ()) m (fun r m' => Q (hb ▸ r) m') X) ∨
      (f = "rec" ∧ if n = 0#64 then Q (hb ▸ (0#64, ())) m
        else Γcall "wrap" [i64] [i64] (n - 1#64, ()) m (fun r m' => Q (hb ▸ r) m') X)

theorem mixedOp₂_biMono : Env.BiMono mixedOp₂ := by
  rintro C₁ C₂ T₁ T₂ hC hT f as bs xs m Q X ⟨ha, hb, hw | hr⟩
  · exact ⟨ha, hb, Or.inl ⟨hw.1, hT _ _ _ _ _ _ _ hw.2⟩⟩
  · rcases hr with ⟨rfl, hrest⟩
    refine ⟨ha, hb, Or.inr ⟨rfl, ?_⟩⟩
    split at hrest <;> rename_i hc
    · simp [hc, hrest]
    · simp only [hc, ↓reduceIte]; exact hC _ _ _ _ _ _ _ hrest

def mixedTwoMod : Module :=
  ⟨[⟨"wrap", [i64], [i64], fun _ _ (n, ()) => .ret (.var n, ())⟩,
    ⟨"rec", [i64], [i64], fun _ _ (n, ()) => .ret (.var n, ())⟩], [], []⟩

def mixedSpec : Nat × Nat → Env
  | (n, 0) => fun f as bs xs m Q _ =>
      f = "rec" ∧ ∃ (ha : as = [i64]) (hb : bs = [i64]),
        (ha ▸ xs).1.toNat = n ∧ Q (hb ▸ (0#64, ())) m
  | (n, _ + 1) => fun f as bs xs m Q _ =>
      f = "wrap" ∧ ∃ (ha : as = [i64]) (hb : bs = [i64]),
        (ha ▸ xs).1.toNat = n ∧ Q (hb ▸ (0#64, ())) m

theorem mixed_depth_lfp_wf (p : Nat × Nat) :
    Env.le (Env.restrict (mixedSpec p) (mixedTwoMod.fns.map Fn.sig))
      (DepthEnv.lfp (DepthEnv.mkSccOp mixedTwoMod botEnv mixedOp₂) p.1) := by
  let wfLt : WellFounded (InvImage Nat.lt (fun q : Nat × Nat => 2 * q.1 + q.2)) :=
    InvImage.wf _ Nat.lt_wfRel.wf
  refine DepthEnv.lfp_wf_mkSccOp wfLt Prod.fst mixedTwoMod botEnv mixedOp₂_biMono mixedSpec
    (fun i Γcall _ hrec _ htail _ f as bs xs m Q X ⟨_, hsp⟩ => ?_) p
  rcases i with ⟨n, k⟩
  cases k with
  | zero =>
      rcases hsp with ⟨rfl, ha, hb, hn, hQ⟩
      subst ha; subst hb
      dsimp only at hn hQ
      refine ⟨rfl, rfl, Or.inr ⟨rfl, ?_⟩⟩
      by_cases h0 : xs.1 = 0#64
      · simp [h0, hQ]
      · simp only [h0, ↓reduceIte]
        have hsub : (xs.1 - 1#64).toNat = n - 1 := by rw [bv64_sub1_toNat h0, hn]
        have hlt_n : (n - 1, 1).1 < (n, 0).1 := by
          have := bv64_sub1_lt h0; dsimp only; omega
        have hlt_sc : 2 * (n - 1) + 1 < 2 * n + 0 := by omega
        exact hrec (n - 1, 1) hlt_sc hlt_n "wrap" [i64] [i64] (xs.1 - 1#64, ()) m
          (fun r m' => Q r m') X
          ⟨by simp [mixedTwoMod, Fn.sig], rfl, rfl, rfl, hsub, hQ⟩
  | succ k' =>
      rcases hsp with ⟨rfl, ha, hb, hn, hQ⟩
      subst ha; subst hb
      dsimp only at hn hQ
      refine ⟨rfl, rfl, Or.inl ⟨rfl, ?_⟩⟩
      have hlt_sc : 2 * n + 0 < 2 * n + (k' + 1) := by omega
      exact htail (n, 0) hlt_sc (Nat.le_refl n) "rec" [i64] [i64] xs m (fun r m' => Q r m') X
        ⟨by simp [mixedTwoMod, Fn.sig], rfl, rfl, rfl, hn, hQ⟩

theorem depth_semScc_fix :
    DepthEnv.semScc cntMod botEnv =
      DepthEnv.sccOp cntMod botEnv (DepthEnv.semScc cntMod botEnv) :=
  DepthEnv.semScc_fix cntMod botEnv

theorem depth_semScc_le_flat (d : Nat) :
    Env.le (DepthEnv.semScc cntMod botEnv d) (Env.semScc cntMod botEnv) :=
  DepthEnv.semScc_le_envSemScc cntMod botEnv d

theorem depth_semScc_le_kleene (d : Nat) :
    Env.le (DepthEnv.semScc cntMod botEnv d) (Env.unfoldRecAt cntMod botEnv d) :=
  DepthEnv.semScc_le_unfoldRecAt cntMod botEnv d

/-! ## 2. Mixed Acyclic + Self-Recursive + Mutually-Recursive Module (`compile_linked_scc!`) -/

/-- Acyclic leaf `fnInc1(x) = x + 1`. -/
def fnInc1 : Fn := tqbe $inc1(%x:l) -> l {
  %y =l add %x, 1
  ret %y
}

/-- Self-recursive countdown sum `fnSum(n) = 0 + 1 + ... + n` via `.call`. -/
def fnSum : Fn := tqbe $sum(%n:l) -> l {
  %c =b ceql %n, 0
  jnz %c, {
    ret 0
  }, {
    %n1 =l sub %n, 1
    %r =l call $sum(%n1)
    %s =l add %n, %r
    ret %s
  }
}

/-- Mutually recursive `fnEven(n)` via `.call`. -/
def fnEven : Fn := tqbe $even(%n:l) -> l {
  %c =b ceql %n, 0
  jnz %c, {
    ret 1
  }, {
    %n1 =l sub %n, 1
    %r =l call $odd(%n1)
    ret %r
  }
}

/-- Mutually recursive `fnOdd(n)` via `.call`. -/
def fnOdd : Fn := tqbe $odd(%n:l) -> l {
  %c =b ceql %n, 0
  jnz %c, {
    ret 0
  }, {
    %n1 =l sub %n, 1
    %r =l call $even(%n1)
    ret %r
  }
}

/-- Top acyclic caller `fnTop(n) = inc1(sum(n) + even(n))` across all earlier chunks. -/
def fnTop : Fn := tqbe $top(%n:l) -> l {
  %s =l call $sum(%n)
  %e =l call $even(%n)
  %t =l add %s, %e
  %r =l call $inc1(%t)
  ret %r
}

def mixedMod : Module :=
  { fns := [fnInc1, fnSum, fnEven, fnOdd, fnTop] }

theorem fnInc1_wf : fnInc1.Wf := by t_wf_reify
theorem fnSum_wf : fnSum.Wf := by t_wf_reify
theorem fnEven_wf : fnEven.Wf := by t_wf_reify
theorem fnOdd_wf : fnOdd.Wf := by t_wf_reify
theorem fnTop_wf : fnTop.Wf := by t_wf_reify

theorem mixedMod_wf : ∀ f ∈ mixedMod.fns, f.Wf := by
  intro f hf
  simp only [mixedMod, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact fnInc1_wf
  · exact fnSum_wf
  · exact fnEven_wf
  · exact fnOdd_wf
  · exact fnTop_wf

-- Emit `mixedCert1` (`chunkSize := 1`, splitting `[fnEven, fnOdd]` into 2 `RecSubChunk`s!)
compile_linked_scc! mixedCert1 litmusTarget litmusLayout LegalTarget.aarch64 litmusLabelClean
  mixedMod 1 (fuel := 16) (maxBound := 2048)

-- Emit `mixedCert4` (`chunkSize := 4`) and custom `(fuels := ...)` variant.
compile_linked_scc! mixedCert4 litmusTarget litmusLayout LegalTarget.aarch64 litmusLabelClean
  mixedMod 4 (fuels := [("sum", 10), ("even", 12)]) (maxBound := 2048)

-- Emit empty module cert cleanly.
def emptySccMod : Module := { fns := [] }
compile_linked_scc! emptySccCert litmusTarget litmusLayout LegalTarget.aarch64 litmusLabelClean
  emptySccMod 2

-- Compositional `LinkedCertScc.ofLinkedCert` + `LinkedCertScc.append` check.
def partModA : Module := { fns := [fnInc1] }
def partModB : Module := { fns := [fnSum, fnEven, fnOdd, fnTop] }
def partModBExterns : List SigEntry := partModA.fns.map Fn.sig

compile_linked_chunks! partCertA litmusTarget litmusLayout LegalTarget.aarch64 litmusLabelClean
  partModA 1 (compileExt := true)

compile_linked_scc! partCertB litmusTarget litmusLayout LegalTarget.aarch64 litmusLabelClean
  partModB 2 (ext := partCertA.exportedExt) (extSigs := partModBExterns)

private theorem partCertA_calls :
    checkChunksCalls [] [] (partCertA.chunks.map Chunk.acyc) = true := by
  rfl

noncomputable def partCertA_scc :
    LinkedCertScc litmusTarget litmusLayout LegalTarget.aarch64 litmusLabelClean partModA :=
  LinkedCertScc.ofLinkedCert partCertA rfl partCertA_calls

noncomputable def appendedMixedCert :
    LinkedCertScc litmusTarget litmusLayout LegalTarget.aarch64 litmusLabelClean mixedMod :=
  partCertA_scc.append partCertB rfl
    (by t_kernel_rfl)
    (by t_kernel_rfl)

theorem mixedCert1_numChunks : mixedCert1.numChunks = 4 := by rfl
theorem mixedCert4_numChunks : mixedCert4.numChunks = 4 := by rfl
theorem emptySccCert_numChunks : emptySccCert.numChunks = 1 := by rfl
theorem appendedMixedCert_numChunks : appendedMixedCert.numChunks = 4 := by rfl

-- Direct `MainLinkScc.compileCheckedRecLit` + negative validation checks.
splice_module_hints evenOddHintsOnly litmusTarget.toIsa LegalTarget.aarch64 [fnEven, fnOdd]

def eoCodeLit : List Instr :=
  (compileModuleRec litmusTarget.toIsa LegalTarget.aarch64 litmusTarget.frame.raBytes
    [] [] 0 8 2048 [fnEven, fnOdd] evenOddHintsOnly).toOption.get!.1

def eoBaseLit : Nat :=
  (compileModuleRec litmusTarget.toIsa LegalTarget.aarch64 litmusTarget.frame.raBytes
    [] [] 0 8 2048 [fnEven, fnOdd] evenOddHintsOnly).toOption.get!.2.1

def eoStepLit : Nat :=
  (compileModuleRec litmusTarget.toIsa LegalTarget.aarch64 litmusTarget.frame.raBytes
    [] [] 0 8 2048 [fnEven, fnOdd] evenOddHintsOnly).toOption.get!.2.2

theorem eoDirect_cm :
    compileModuleRec litmusTarget.toIsa LegalTarget.aarch64 litmusTarget.frame.raBytes
      [] [] 0 8 2048 [fnEven, fnOdd] evenOddHintsOnly =
      .ok (eoCodeLit, eoBaseLit, eoStepLit) := by
  t_kernel_rfl

theorem eoDirect_chk :
    checkCompileRecLit litmusTarget.frame.label litmusLayout.progSmall
      eoCodeLit eoBaseLit eoStepLit ["even", "odd"] [] = true := by
  t_kernel_rfl

def eoDirectCompiled :
    CompiledRec litmusTarget LegalTarget.aarch64 [] [] 0 8
      [fnEven, fnOdd] evenOddHintsOnly 2048 :=
  compileCheckedRecLit litmusTarget litmusLayout LegalTarget.aarch64 litmusLabelClean
    [] [] 0 8 [fnEven, fnOdd] evenOddHintsOnly 2048
    eoCodeLit eoBaseLit eoStepLit eoDirect_cm eoDirect_chk

-- Negative validation checks: stack overflow, cyclic module rejected as acyclic, ext collision.
#guard
  match compileModuleRec litmusTarget.toIsa LegalTarget.aarch64 litmusTarget.frame.raBytes
      [] [] 0 100 16 [fnEven, fnOdd] evenOddHintsOnly with
  | .error _ => true
  | .ok _ => false

#guard !Module.checkAcyclic ⟨[fnEven, fnOdd], [], []⟩
#guard !LinkRec.checkCyclic ⟨[fnTop], [], []⟩

private def fnUnsupportedW128 : Fn :=
  ⟨"bad_w128", [.bits 128], [.bits 128], fun _ _ (x, ()) => .ret (.var x, ())⟩

#guard
  match compileModule litmusTarget.toIsa LegalTarget.aarch64
      litmusTarget.frame.raBytes [] [] 0 [fnUnsupportedW128]
      [Fn.computeHints litmusTarget.toIsa LegalTarget.aarch64 fnUnsupportedW128] with
  | .error "bad_w128: unsupported source op for target" => true
  | _ => false

#guard
  match compileModuleRecAuxSupp litmusTarget.toIsa LegalTarget.aarch64
      litmusTarget.frame.raBytes [] [] [] 0 [fnUnsupportedW128]
      [Fn.computeHints litmusTarget.toIsa LegalTarget.aarch64 fnUnsupportedW128] with
  | .error "bad_w128: unsupported source op for target" => true
  | _ => false

theorem neg_ext_collision_rejected :
    checkLinkSccList litmusLayout [(("even", [i64], [i64]), 0)]
      [.recSCC [] 8 [fnEven, fnOdd] evenOddHintsOnly 2048 eoDirectCompiled] = false := by
  decide

/-! ## 3. Semantic Linking (`DepthEnv.lfp_wf_mkSccOp` -> `mixedCert1.sem` -> `Eventually`) -/

private def triNat : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + triNat n

private def parityEvenVal (n : Nat) : BitVec 64 :=
  if n % 2 = 0 then 1#64 else 0#64

private def parityOddVal (n : Nat) : BitVec 64 :=
  if n % 2 = 1 then 1#64 else 0#64

def inc1Spec : Spec [i64] [i64] := fun (x, ()) m Q _ =>
  Q (x + 1#64, ()) m

def sumSpec : Spec [i64] [i64] := fun (n, ()) m Q _ =>
  n.toNat ≤ 16 ∧ Q (BitVec.ofNat 64 (triNat n.toNat), ()) m

def evenSpec : Spec [i64] [i64] := fun (n, ()) m Q _ =>
  n.toNat ≤ 16 ∧ Q (parityEvenVal n.toNat, ()) m

def oddSpec : Spec [i64] [i64] := fun (n, ()) m Q _ =>
  n.toNat ≤ 16 ∧ Q (parityOddVal n.toNat, ()) m

def topSpec : Spec [i64] [i64] := fun (n, ()) m Q _ =>
  n.toNat ≤ 16 ∧
    Q (BitVec.ofNat 64 (triNat n.toNat) + parityEvenVal n.toNat + 1#64, ()) m

private def sumDepthSpec (k : Nat) : Env :=
  fun f as bs xs m Q _ =>
    f = "sum" ∧ ∃ (ha : as = [i64]) (hb : bs = [i64]),
      let n := (ha ▸ xs).1.toNat
      n ≤ k ∧ k ≤ 16 ∧ Q (hb ▸ (BitVec.ofNat 64 (triNat n), ())) m

private def evenOddDepthSpec (k : Nat) : Env :=
  fun f as bs xs m Q _ =>
    ∃ (ha : as = [i64]) (hb : bs = [i64]),
      let n := (ha ▸ xs).1.toNat
      n ≤ k ∧ k ≤ 16 ∧
      ((f = "even" ∧ Q (hb ▸ (parityEvenVal n, ())) m) ∨
       (f = "odd" ∧ Q (hb ▸ (parityOddVal n, ())) m))

private noncomputable abbrev mc0 : Chunk litmusTarget LegalTarget.aarch64 [] 0 :=
  mixedCert1.chunks[0]'(by decide)

private noncomputable abbrev mc1 : Chunk litmusTarget LegalTarget.aarch64 [] 0 :=
  mixedCert1.chunks[1]'(by decide)

private noncomputable abbrev mc2 : Chunk litmusTarget LegalTarget.aarch64 [] 0 :=
  mixedCert1.chunks[2]'(by decide)

private noncomputable abbrev mc3 : Chunk litmusTarget LegalTarget.aarch64 [] 0 :=
  mixedCert1.chunks[3]'(by decide)

private theorem mixedCert1_chunks_split :
    mixedCert1.chunks = [mc0, mc1, mc2, mc3] := by
  rfl

private theorem triNat_step {n : BitVec 64} (hne : n ≠ 0#64) :
    n + BitVec.ofNat 64 (triNat (n - 1#64).toNat) = BitVec.ofNat 64 (triNat n.toNat) := by
  have hsub := bv64_sub1_toNat hne
  have hnz : n.toNat ≠ 0 := fun h => hne (BitVec.eq_of_toNat_eq h)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hnz
  rw [hsub, hk, Nat.succ_sub_one, triNat]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have hnlt : n.toNat < 2 ^ 64 := n.isLt
  rw [hk, Nat.add_mod_mod]

private theorem parity_even_step {n : BitVec 64} (hne : n ≠ 0#64) :
    parityOddVal (n - 1#64).toNat = parityEvenVal n.toNat := by
  have hnz : n.toNat ≠ 0 := fun h => hne (BitVec.eq_of_toNat_eq h)
  rw [bv64_sub1_toNat hne]
  simp only [parityOddVal, parityEvenVal]
  have : (n.toNat - 1) % 2 = 1 ↔ n.toNat % 2 = 0 := by omega
  simp [this]

private theorem parity_odd_step {n : BitVec 64} (hne : n ≠ 0#64) :
    parityEvenVal (n - 1#64).toNat = parityOddVal n.toNat := by
  have hnz : n.toNat ≠ 0 := fun h => hne (BitVec.eq_of_toNat_eq h)
  rw [bv64_sub1_toNat hne]
  simp only [parityEvenVal, parityOddVal]
  have : (n.toNat - 1) % 2 = 0 ↔ n.toNat % 2 = 1 := by omega
  simp [this]

private theorem c0_sem_inc1 :
    ∀ (xs : Tup Val [i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost),
      inc1Spec xs m Q X →
      mc0.sem [] botEnv "inc1" [i64] [i64] xs m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  have hcm : ∃ cc, mc0 = Chunk.acyc cc ∧ cc.fs = [fnInc1] := ⟨_, rfl, rfl⟩
  rcases hcm with ⟨cc, hceq, hfs⟩
  rw [hceq]
  refine LinkedCertScc.acycChunk_sem_of_semScc cc (by rw [hfs]; exact List.mem_cons_self) ?_
  dsimp only [Env.semScc]
  rw [Env.lfp_fix (sccOp_mono _ _), hfs]
  refine ⟨by simp [fnInc1, Fn.sig], fnInc1, List.mem_cons_self, rfl, rfl, rfl, ?_⟩
  dsimp only [Func.wp, fnInc1]; wp_unfold
  exact hQ

private theorem c1_sem_sum :
    ∀ (xs : Tup Val [i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost),
      sumSpec xs m Q X →
      mc1.sem [fnInc1.sig] (mc0.sem [] botEnv) "sum" [i64] [i64] xs m Q X := by
  rintro ⟨n, ⟨⟩⟩ m Q X ⟨hn, hQ⟩
  let Γ₀ := mc0.sem [] botEnv
  have hcr : ∃ ext fs hints maxB cr,
      mc1 = Chunk.recSCC ext 16 fs hints maxB cr ∧ fs = [fnSum] :=
    ⟨_, _, _, _, _, rfl, rfl⟩
  rcases hcr with ⟨ext, fs, hints, maxB, cr, hceq, hfs⟩
  rw [hceq]
  refine LinkedCertScc.recChunk_sem_of_depth cr (by rw [hfs]; exact List.mem_cons_self) hn ?_
  rw [hfs]
  let M : Module := ⟨[fnSum], externsOfSigs [fnInc1.sig], []⟩
  refine DepthEnv.lfp_wf_mkSccOp Nat.lt_wfRel.wf id M Γ₀
    (fun C₁ C₂ _ _ hC _ f as bs xs m' Q' X' ⟨hsig, fn, hfn, hnm, ha, hr, hwp⟩ =>
      ⟨hsig, fn, hfn, hnm, ha, hr, wp_env_mono hC _ m' hwp⟩)
    sumDepthSpec
    (fun i Γcall _ hrec _ _ _ f as bs xs m' Q' X' ⟨hsig, heq, ha, hb, hnk, hk16, hQ'⟩ => by
      subst heq; subst ha; subst hb
      dsimp only at hnk hQ'
      refine ⟨hsig, fnSum, List.mem_cons_self, rfl, rfl, rfl, ?_⟩
      dsimp only [Func.wp, fnSum]; wp_unfold
      constructor
      · intro h0
        have hz : xs.1.toNat = 0 := by rw [h0]; rfl
        rw [hz] at hQ'; exact hQ'
      · intro hne
        have hlt : (xs.1 - 1#64).toNat < i := by have := bv64_sub1_lt hne; omega
        refine wp_call_of_spec _ _ (hrec (xs.1 - 1#64).toNat hlt hlt
          "sum" [i64] [i64] (xs.1 - 1#64, ()) m' (fun r m'' => Q' (xs.1 + r.1, ()) m'') X'
          ⟨hsig, rfl, rfl, rfl, Nat.le_refl _, by omega, ?_⟩)
        dsimp only; rw [triNat_step hne]; exact hQ')
    n.toNat "sum" [i64] [i64] (n, ()) m Q X
    ⟨by simp [M, fnSum, Fn.sig], rfl, rfl, rfl, Nat.le_refl _, hn, hQ⟩

private theorem c2_sem_even :
    ∀ (xs : Tup Val [i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost),
      evenSpec xs m Q X →
      mc2.sem [fnSum.sig, fnInc1.sig] (mc1.sem [fnInc1.sig] (mc0.sem [] botEnv))
        "even" [i64] [i64] xs m Q X := by
  rintro ⟨n, ⟨⟩⟩ m Q X ⟨hn, hQ⟩
  let Γ₁ := mc1.sem [fnInc1.sig] (mc0.sem [] botEnv)
  have hcr : ∃ ext fs hints maxB cr,
      mc2 = Chunk.recSCC ext 16 fs hints maxB cr ∧ fs = [fnEven, fnOdd] :=
    ⟨_, _, _, _, _, rfl, rfl⟩
  rcases hcr with ⟨ext, fs, hints, maxB, cr, hceq, hfs⟩
  rw [hceq]
  refine LinkedCertScc.recChunk_sem_of_depth cr (by rw [hfs]; exact List.mem_cons_self) hn ?_
  rw [hfs]
  let M : Module := ⟨[fnEven, fnOdd], externsOfSigs [fnSum.sig, fnInc1.sig], []⟩
  refine DepthEnv.lfp_wf_mkSccOp Nat.lt_wfRel.wf id M Γ₁
    (fun C₁ C₂ _ _ hC _ f as bs xs m' Q' X' ⟨hsig, fn, hfn, hnm, ha, hr, hwp⟩ =>
      ⟨hsig, fn, hfn, hnm, ha, hr, wp_env_mono hC _ m' hwp⟩)
    evenOddDepthSpec
    (fun i Γcall _ hrec _ _ _ f as bs xs m' Q' X' ⟨hsig, ha, hb, hnk, hk16, hbr⟩ => by
      subst ha; subst hb
      dsimp only at hnk hbr
      rcases hbr with ⟨rfl, hQe⟩ | ⟨rfl, hQo⟩
      · refine ⟨hsig, fnEven, List.mem_cons_self, rfl, rfl, rfl, ?_⟩
        dsimp only [Func.wp, fnEven]; wp_unfold
        constructor
        · intro h0
          have hz : xs.1.toNat = 0 := by rw [h0]; rfl
          rw [hz] at hQe; exact hQe
        · intro hne
          have hlt : (xs.1 - 1#64).toNat < i := by have := bv64_sub1_lt hne; omega
          refine wp_call_of_spec _ _ (hrec (xs.1 - 1#64).toNat hlt hlt
            "odd" [i64] [i64] (xs.1 - 1#64, ()) m' Q' X'
            ⟨by simp [M, fnOdd, Fn.sig], rfl, rfl, Nat.le_refl _, by omega,
              Or.inr ⟨rfl, by rw [parity_even_step hne]; exact hQe⟩⟩)
      · refine ⟨hsig, fnOdd, List.mem_cons_of_mem _ List.mem_cons_self, rfl, rfl, rfl, ?_⟩
        dsimp only [Func.wp, fnOdd]; wp_unfold
        constructor
        · intro h0
          have hz : xs.1.toNat = 0 := by rw [h0]; rfl
          rw [hz] at hQo; exact hQo
        · intro hne
          have hlt : (xs.1 - 1#64).toNat < i := by have := bv64_sub1_lt hne; omega
          refine wp_call_of_spec _ _ (hrec (xs.1 - 1#64).toNat hlt hlt
            "even" [i64] [i64] (xs.1 - 1#64, ()) m' Q' X'
            ⟨by simp [M, fnEven, Fn.sig], rfl, rfl, Nat.le_refl _, by omega,
              Or.inl ⟨rfl, by rw [parity_odd_step hne]; exact hQo⟩⟩))
    n.toNat "even" [i64] [i64] (n, ()) m Q X
    ⟨by simp [M, fnEven, Fn.sig], rfl, rfl, Nat.le_refl _, hn, Or.inl ⟨rfl, hQ⟩⟩

private theorem mixed_sum_sem :
    ∀ xs m Q X, sumSpec xs m Q X → mixedCert1.sem botEnv "sum" [i64] [i64] xs m Q X := by
  intro xs m Q X h
  change semChunks [fnInc1.sig] (mc0.sem [] botEnv) [mc1, mc2, mc3]
    "sum" [i64] [i64] xs m Q X
  exact LinkedCertScc.semChunks_of_head (f := fnSum) (by decide) xs m Q X
    (c1_sem_sum xs m Q X h)

private theorem mixed_even_sem :
    ∀ xs m Q X, evenSpec xs m Q X → mixedCert1.sem botEnv "even" [i64] [i64] xs m Q X := by
  intro xs m Q X h
  change semChunks [fnSum.sig, fnInc1.sig]
    (mc1.sem [fnInc1.sig] (mc0.sem [] botEnv)) [mc2, mc3]
    "even" [i64] [i64] xs m Q X
  exact LinkedCertScc.semChunks_of_head (f := fnEven) (by decide) xs m Q X
    (c2_sem_even xs m Q X h)

private theorem mixed_top_sem :
    ∀ xs m Q X, topSpec xs m Q X → mixedCert1.sem botEnv "top" [i64] [i64] xs m Q X := by
  rintro ⟨n, ⟨⟩⟩ m Q X ⟨hn, hQ⟩
  change semChunks [fnEven.sig, fnOdd.sig, fnSum.sig, fnInc1.sig]
    (mc2.sem [fnSum.sig, fnInc1.sig] (mc1.sem [fnInc1.sig] (mc0.sem [] botEnv)))
    [mc3] "top" [i64] [i64] (n, ()) m Q X
  refine LinkedCertScc.semChunks_of_head (f := fnTop) (by decide) (n, ()) m Q X ?_
  have hcm : ∃ cc, mc3 = Chunk.acyc cc ∧ cc.fs = [fnTop] := ⟨_, rfl, rfl⟩
  rcases hcm with ⟨cc, hceq, hfs⟩
  rw [hceq]
  refine LinkedCertScc.acycChunk_sem_of_semScc cc (by rw [hfs]; exact List.mem_cons_self) ?_
  dsimp only [Env.semScc]
  rw [Env.lfp_fix (sccOp_mono _ _), hfs]
  refine ⟨by simp [fnTop, Fn.sig], fnTop, List.mem_cons_self, rfl, rfl, rfl, ?_⟩
  dsimp only [Func.wp, fnTop]
  let sV : BitVec 64 := BitVec.ofNat 64 (triNat n.toNat)
  let eV : BitVec 64 := parityEvenVal n.toNat
  let Γprev := mc2.sem [fnSum.sig, fnInc1.sig] (mc1.sem [fnInc1.sig] (mc0.sem [] botEnv))
  have hSumP : Γprev "sum" [i64] [i64] (n, ()) m (fun r m' => r = (sV, ()) ∧ m' = m) X := by
    dsimp only [Γprev, Chunk.sem, Env.sccStep]
    refine Or.inr ⟨by decide, ?_⟩
    exact c1_sem_sum (n, ()) m (fun r m' => r = (sV, ()) ∧ m' = m) X ⟨hn, ⟨rfl, rfl⟩⟩
  have hEvenP : Γprev "even" [i64] [i64] (n, ()) m (fun r m' => r = (eV, ()) ∧ m' = m) X :=
    c2_sem_even (n, ()) m (fun r m' => r = (eV, ()) ∧ m' = m) X ⟨hn, ⟨rfl, rfl⟩⟩
  have hIncP : Γprev "inc1" [i64] [i64] (sV + eV, ()) m Q X := by
    have h0 := c0_sem_inc1 (sV + eV, ()) m Q X hQ
    dsimp only [Γprev, Chunk.sem, Env.sccStep]
    refine Or.inr ⟨by decide, Or.inr ⟨by decide, h0⟩⟩
  refine ⟨fun r m' => r = (sV, ()) ∧ m' = m, X, Or.inr ⟨by decide, hSumP⟩, ?_,
    fun _ _ _ _ h => h⟩
  rintro ⟨s, ⟨⟩⟩ m' ⟨hr, hm'⟩
  obtain rfl : s = sV := (Prod.ext_iff.mp hr).1
  subst hm'
  refine ⟨fun r m'' => r = (eV, ()) ∧ m'' = m', X, Or.inr ⟨by decide, hEvenP⟩, ?_,
    fun _ _ _ _ h => h⟩
  rintro ⟨e, ⟨⟩⟩ m'' ⟨hr2, hm''⟩
  obtain rfl : e = eV := (Prod.ext_iff.mp hr2).1
  subst hm''; wp_unfold
  exact wp_call_of_spec _ _ (Or.inr ⟨by decide, hIncP⟩)

theorem fnSum_litmus_fnSpec :
    litmusTarget.Defined mixedCert1.host "sum" ∧
      litmusTarget.FnSpec mixedCert1.host "sum" sumSpec (mixedCert1.bound "sum") 0 :=
  mixedCert1.fnSpec_host_src_of_le mixedMod_wf
    (f := fnSum) (by simp [mixedMod]) sumSpec rfl rfl (fun _ _ _ _ _ h => h)
    mixed_sum_sem

theorem fnEven_litmus_fnSpec :
    litmusTarget.Defined mixedCert1.host "even" ∧
      litmusTarget.FnSpec mixedCert1.host "even" evenSpec (mixedCert1.bound "even") 0 :=
  mixedCert1.fnSpec_host_src_of_le mixedMod_wf
    (f := fnEven) (by simp [mixedMod]) evenSpec rfl rfl
    (fun _ _ _ _ _ h => h) mixed_even_sem

theorem fnTop_litmus_fnSpec :
    litmusTarget.Defined mixedCert1.host "top" ∧
      litmusTarget.FnSpec mixedCert1.host "top" topSpec (mixedCert1.bound "top") 0 :=
  mixedCert1.fnSpec_host_src_of_le mixedMod_wf
    (f := fnTop) (by simp [mixedMod]) topSpec rfl rfl (fun _ _ _ _ _ h => h) mixed_top_sem

theorem fnSum_5_exec :
    Eventually (litmusTarget.mach.step mixedCert1.host)
      (fun st => litmusTarget.mach.pc st = litmusInit.ra0 ∧
        litmusTarget.mach.getGpr (litmusTarget.mach.data st) litmusInit.ret0 = 15#64)
      (litmusTarget.mach.mkState
        (litmusInit.initState (as := [i64]) (mixedCert1.bound "sum") []
          ((5#64, ()) : Tup Val [i64]))
        (litmusTarget.mach.labelAddr mixedCert1.host "sum")) :=
  mixedCert1.eventually_ret1_i64_of_le litmusInit mixedMod_wf
    (f := fnSum) (by simp [mixedMod]) rfl rfl rfl sumSpec
    (fun _ _ _ _ _ h => h) mixed_sum_sem [] ((5#64, ()) : Tup Val [i64]) 15#64
    (by decide) rfl (Q := fun r _ => r = (15#64, ()))
    ⟨by decide, by decide⟩ (fun _ _ h => h)

theorem fnEven_4_exec :
    Eventually (litmusTarget.mach.step mixedCert1.host)
      (fun st => litmusTarget.mach.pc st = litmusInit.ra0 ∧
        litmusTarget.mach.getGpr (litmusTarget.mach.data st) litmusInit.ret0 = 1#64)
      (litmusTarget.mach.mkState
        (litmusInit.initState (as := [i64]) (mixedCert1.bound "even") []
          ((4#64, ()) : Tup Val [i64]))
        (litmusTarget.mach.labelAddr mixedCert1.host "even")) :=
  mixedCert1.eventually_ret1_i64_of_le litmusInit mixedMod_wf
    (f := fnEven) (by simp [mixedMod]) rfl rfl rfl
    evenSpec (fun _ _ _ _ _ h => h) mixed_even_sem [] ((4#64, ()) : Tup Val [i64]) 1#64
    (by decide) rfl (Q := fun r _ => r = (1#64, ()))
    ⟨by decide, by decide⟩ (fun _ _ h => h)

theorem fnTop_5_exec :
    Eventually (litmusTarget.mach.step mixedCert1.host)
      (fun st => litmusTarget.mach.pc st = litmusInit.ra0 ∧
        litmusTarget.mach.getGpr (litmusTarget.mach.data st) litmusInit.ret0 = 16#64)
      (litmusTarget.mach.mkState
        (litmusInit.initState (as := [i64]) (mixedCert1.bound "top") []
          ((5#64, ()) : Tup Val [i64]))
        (litmusTarget.mach.labelAddr mixedCert1.host "top")) :=
  mixedCert1.eventually_ret1_i64_of_le litmusInit mixedMod_wf
    (f := fnTop) (by simp [mixedMod]) rfl rfl rfl topSpec
    (fun _ _ _ _ _ h => h) mixed_top_sem [] ((5#64, ()) : Tup Val [i64]) 16#64
    (by decide) rfl (Q := fun r _ => r = (16#64, ()))
    ⟨by decide, by decide⟩ (fun _ _ h => h)

/-! ## 4. Single-Line Axiom Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms LeanQbe.T.DepthEnv.lfp_le
#print axioms LeanQbe.T.DepthEnv.lfp_closed
#print axioms LeanQbe.T.DepthEnv.lfp_fix
#print axioms LeanQbe.T.DepthEnv.lfp_mono
#print axioms LeanQbe.T.DepthEnv.lfp_depth_mono
#print axioms LeanQbe.T.DepthEnv.lfp_wf
#print axioms LeanQbe.T.DepthEnv.lfp_wf_mkSccOp
#print axioms LeanQbe.T.DepthEnv.semScc_le_envSemScc
#print axioms LeanQbe.T.DepthEnv.semScc_le_unfoldRecAt
#print axioms LeanQbe.T.link_scc_depth_lfp
#print axioms LeanQbe.T.link_scc_lfp_zero
#print axioms LeanQbe.T.linkRecSubchunks
#print axioms LeanQbe.T.linkChunks_fnSpec
#print axioms LeanQbe.T.linkChunks_fnSpec_host
#print axioms LeanQbe.T.LinkedCertScc.fnSpec_linked
#print axioms LeanQbe.T.LinkedCertScc.fnSpec_host
#print axioms LeanQbe.T.LinkedCertScc.eventually_ret1_i64_of_le
#print axioms tailOnly_zero_lfp_wf
#print axioms tailOnly_zero_eq_flat
#print axioms mixed_depth_lfp_wf
#print axioms mixedCert1
#print axioms appendedMixedCert
#print axioms eoDirectCompiled
#print axioms fnSum_litmus_fnSpec
#print axioms fnEven_litmus_fnSpec
#print axioms fnTop_litmus_fnSpec
#print axioms fnSum_5_exec
#print axioms fnEven_4_exec
#print axioms fnTop_5_exec

end LeanQbeTest.T.MainCertSccTest
