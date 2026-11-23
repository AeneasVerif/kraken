module

public import LeanQbe.T.LinkSccLemmas2
public import LeanQbe.T.Examples.LinkRec
public import LeanQbeTest.T.LinkRecTest
public import LeanQbe.T.MainSplice
public meta import Lean
public meta import LeanQbe.T.MainSplice
public meta import LeanQbe.T.Examples.LinkRec
public meta import LeanQbeTest.T.RegaLitmusTarget

/-!
# Tests for Well-Founded SCC Module Linking

Exercises `LeanQbe.T.LinkScc`, `LeanQbe.T.LinkSccLemmas1`, and `LeanQbe.T.LinkSccLemmas2` on
`RegaLitmus.litmusTarget`:
1. `link_scc_export` & `link_scc_export_restrict`: packages `evenOddRecMod` into `Env.exportScc`
   at static bound `boundAt 16`, and composes an outer SCC `paritySum` calling `isEven` as a
   resolved external SCC callee.
2. `link_rec_of_scc`: recovers `LinkRec.link_rec_compiled` shape cleanly on `evenOddRecMod` and
   `recSumMod`.
3. Lexicographic `ι := Nat × Nat` (`Prod.Lex` via `lexNatRecIdx`) Ackermann-shaped `Env.stepIdx`
   example `ackFn` proved with `link_scc_compiled` and executed concretely (`ack(2, 2) = 7`).
4. Single-line `#print axioms` audit on every new public theorem.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.LinkSccTest

open LeanQbe.T LeanQbe.T.LinkRec LeanQbe.T.LinkScc
open LeanQbe.T.RegaLitmus LeanQbeTest.T.MainTest LeanQbeTest.T.LinkRecTest
open LeanQbe.T.Notation Std Std.ExtHashMap Kraken.Bedrock2.Test

/-! ## 1. `link_scc_export`, `link_scc_export_restrict`, & Cross-SCC Composition -/

private theorem evenOdd_wf_mem : ∀ f ∈ evenOddRecMod.fns, f.Wf := by
  intro f hf
  simp only [evenOddRecMod, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl <;> first | exact isEven_wf | exact isOdd_wf

private theorem evenOdd_supports_all :
    evenOddRecMod.fns.all (fun f => (f.earlyOpt).body.supportsSource LegalTarget.aarch64) =
      true := by
  t_kernel_rfl

private theorem evenOdd_supports_mem :
    ∀ f ∈ evenOddRecMod.fns, (f.earlyOpt).body.supportsSource LegalTarget.aarch64 = true :=
  fun f hf => List.all_eq_true.mp evenOdd_supports_all f hf

theorem evenOdd_moduleSccOk :
    ModuleSccOk natRecIdx evenOddRecEnv (fun _ _ _ _ _ _ _ => False)
      (evenOddLitmusCompiled.stepBound != 0) evenOddRecMod := by
  refine moduleSccOk_of_step natRecIdx evenOddRecMod_checkCyclic evenOdd_wf_mem ?_
  intro k fn hfn Γ hrec _ xs m Q X hspec
  refine wp_env_mono (fun g as bs xs' m' Q' X' hg => ?_) _ m
    (evenOddRecMod_wp_step k fn hfn xs m Q X hspec)
  rcases hg with ⟨hsig, k', hk', hΓ'⟩ | ⟨hsig, _⟩
  · obtain ⟨gfn, hgfn, hgeq⟩ := List.mem_map.mp hsig
    cases hgeq
    exact hrec gfn hgfn k' hk' (Or.inr hk') xs' m' Q' X' hΓ'
  · simp [evenOddRecMod] at hsig

theorem isEven_exportScc_fnSpec :
    litmusTarget.Defined evenOddLitmusCompiled.host "isEven" ∧
      litmusTarget.FnSpec evenOddLitmusCompiled.host "isEven"
        (Env.exportScc natRecIdx evenOddRecEnv 16 "isEven" [i64] [i64])
        (evenOddLitmusCompiled.baseBound + 16 * evenOddLitmusCompiled.stepBound) 0 :=
  link_scc_export_src_noExit natRecIdx evenOddLitmusCompiled evenOddRecMod rfl evenOddRecEnv
    (fun _ _ _ _ _ _ _ => False) evenOdd_moduleSccOk evenOdd_supports_mem
    List.mem_cons_self rfl rfl (fun _ _ _ _ _ h => h)

theorem isEven_exportScc_4 :
    Eventually (litmusTarget.mach.step evenOddLitmusCompiled.host)
      (fun st => litmusTarget.mach.pc st = litmusInit.ra0 ∧
        litmusTarget.mach.getGpr (litmusTarget.mach.data st) litmusInit.ret0 = 1#64)
      (litmusTarget.mach.mkState
        (litmusInit.initState (as := [i64]) (evenOddLitmusCompiled.boundAt 16) []
          ((4#64, ()) : Tup Val [i64]))
        (litmusTarget.mach.labelAddr evenOddLitmusCompiled.host "isEven")) :=
  run_rec_ret1_i64 litmusInit (as := [i64]) evenOddLitmusCompiled (by decide : 16 ≤ 16)
    isEven_exportScc_fnSpec.2 [] ((4#64, ()) : Tup Val [i64]) 1#64
    (by decide) rfl (Q := fun r _ => r = (1#64, ())) ⟨4, by decide, by decide, rfl⟩
    (fun _ _ h => h)

/-- Outer SCC function `paritySum(n)` summing `isEven(i)` for `0 ≤ i ≤ n` using `isEven` from the
earlier SCC as an external callee. -/
def paritySum : Fn := tqbe $paritySum(%n:l) -> l {
  %c =b ceql %n, 0
  jnz %c, {
    %e0 =l call $isEven(0:l)
    ret %e0
  }, {
    %en =l call $isEven(%n)
    %n1 =l sub %n, 1
    %rest =l call $paritySum(%n1)
    %s =l add %en, %rest
    ret %s
  }
}

def paritySumMod : Module := ⟨[paritySum], [⟨"isEven", [i64], [i64]⟩], []⟩

theorem paritySum_wf : Fn.Wf paritySum := by t_wf_reify
theorem paritySumMod_checkCyclic : checkCyclic paritySumMod = true := by t_kernel_rfl
theorem paritySumMod_sccOrder :
    checkSccOrder [[isEven, isOdd], [paritySum]] [] = true := by
  t_kernel_rfl

def paritySumVal : Nat → BitVec 64
  | 0 => isEvenVal 0#64
  | n + 1 => isEvenVal (BitVec.ofNat 64 (n + 1)) + paritySumVal n

def paritySumSpec (k : Nat) : Spec [i64] [i64] := fun (n, ()) m Q _ =>
  n.toNat ≤ k ∧ n.toNat ≤ 16 ∧ Q (paritySumVal n.toNat, ()) m

def paritySumEnv (k : Nat) : Env
  | "paritySum", [.bits 64], [.bits 64] => paritySumSpec k
  | _, _, _ => fun _ _ _ _ => False

private theorem paritySum_step (Γ : Env) (k : Nat)
    (heven : ∀ args m Q X,
      Env.exportScc natRecIdx evenOddRecEnv 16 "isEven" [i64] [i64] args m Q X →
      Γ "isEven" [i64] [i64] args m Q X)
    (hrec : ∀ k' < k, ∀ args m Q X, paritySumSpec k' args m Q X →
      Γ "paritySum" [i64] [i64] args m Q X) :
    ∀ args m Q X, paritySumSpec k args m Q X → Func.wp Γ paritySum.body args m Q X := by
  rintro ⟨n, ⟨⟩⟩ m Q X ⟨hn, hn16, hQ⟩
  dsimp only [Func.wp, paritySum]; wp_unfold
  constructor
  · intro h0
    subst h0
    refine wp_call_of_spec _ _ (heven (0#64, ()) m Q X ⟨0, by decide, by decide, hQ⟩)
  · intro hne
    have hnz : n.toNat ≠ 0 := fun hz => hne (BitVec.eq_of_toNat_eq hz)
    obtain ⟨n', hn'⟩ := Nat.exists_eq_succ_of_ne_zero hnz
    have hlt : (n - 1#64).toNat = n' := by
      have := n.isLt; rw [BitVec.toNat_sub]; simp; omega
    have hofn : BitVec.ofNat 64 (n' + 1) = n := by
      rw [← Nat.succ_eq_add_one, ← hn', BitVec.ofNat_toNat, BitVec.setWidth_eq]
    refine ⟨fun r m' => r = (isEvenVal n, ()) ∧ m' = m, X,
      heven (n, ()) m _ X ⟨n.toNat, hn16, Nat.le_refl _, ⟨rfl, rfl⟩⟩, ?_, fun _ _ _ _ h => h⟩
    rintro ⟨en, ⟨⟩⟩ m' ⟨hr, hm'⟩
    have hen : en = isEvenVal n := (Prod.ext_iff.mp hr).1
    subst hen; rcases hm' with rfl
    wp_unfold
    refine wp_call_of_spec _ _ (hrec (k - 1) (by omega) (n - 1#64, ()) m'
      (fun r m'' => Q (isEvenVal n + r.1, ()) m'') X ⟨?_, ?_, ?_⟩)
    · rw [hlt]; omega
    · rw [hlt]; omega
    · rw [hlt]
      have hval : isEvenVal n + paritySumVal n' = paritySumVal n.toNat := by
        rw [hn', paritySumVal, hofn]
      dsimp only
      rw [hval]; exact hQ

splice_module_hints paritySumHints litmusTarget.toIsa LegalTarget.aarch64 paritySumMod.fns

theorem paritySum_check :
    checkCompileRec litmusTarget litmusLayout LegalTarget.aarch64
      [(("isEven", [i64], [i64]), evenOddLitmusCompiled.boundAt 16)] [] 0 16
      paritySumMod.fns paritySumHints 2048 = true := by
  t_kernel_rfl

def paritySumCompiled :
    CompiledRec litmusTarget LegalTarget.aarch64
      [(("isEven", [i64], [i64]), evenOddLitmusCompiled.boundAt 16)] [] 0 16
      paritySumMod.fns paritySumHints 2048 :=
  compileRecChecked litmusTarget litmusLayout LegalTarget.aarch64 litmusLabelClean
    [(("isEven", [i64], [i64]), evenOddLitmusCompiled.boundAt 16)] [] 0 16
    paritySumMod.fns paritySumHints 2048 paritySum_check

theorem paritySumCombined_progSmall :
    litmusLayout.progSmall (evenOddLitmusCompiled.code ++ paritySumCompiled.code) = true := by
  t_kernel_rfl

def paritySumCombinedHost : LHost :=
  litmusLayout.layoutOf (evenOddLitmusCompiled.code ++ paritySumCompiled.code)
    paritySumCombined_progSmall

private theorem extract_compileAux {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX fuel maxBound : Nat}
    {fs : List Fn} {hints : List I.Hints} {code : List I.Directive} {base step : Nat}
    (h : compileModuleRec I lt raBytes extCallees exits nX fuel maxBound fs hints =
      .ok (code, base, step)) :
    compileModuleRecAux I lt raBytes
      (fs.map (fun f => (f.name, lt.legalSig f.as, lt.legalSig f.rs)))
      extCallees exits nX fs hints = .ok (code, base, step) := by
  dsimp only [compileModuleRec] at h
  split at h; · simp at h
  split at h; · simp at h
  rename_i code' b' s' haux
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact haux
  · simp at h

theorem paritySumCombined_labelsUnique : litmusTarget.LabelsUnique paritySumCombinedHost := by
  have hprog : litmusTarget.mach.prog paritySumCombinedHost =
      evenOddLitmusCompiled.code ++ paritySumCompiled.code :=
    litmusLayout.prog_layoutOf _ _
  have hnd : (evenOddRecMod.fns.map Fn.name ++ paritySumMod.fns.map Fn.name).Nodup := by decide
  have hok : (evenOddRecMod.fns.map Fn.name ++ paritySumMod.fns.map Fn.name).all fnNameOk = true :=
    by decide
  have haux1 := extract_compileAux evenOddLitmusCompiled.compileModuleRec_eq
  have haux2 := extract_compileAux paritySumCompiled.compileModuleRec_eq
  have hnd_s := List.nodup_append.mp hnd
  simp only [List.all_append, Bool.and_eq_true, List.all_map] at hok
  obtain ⟨hmem1, huniq1⟩ := compileModuleRecAux_code_labels litmusLabelClean LegalTarget.aarch64
    litmusTarget.frame.raBytes _ [] [] 0 haux1 hnd_s.1 hok.1
  obtain ⟨hmem2, huniq2⟩ := compileModuleRecAux_code_labels litmusLabelClean LegalTarget.aarch64
    litmusTarget.frame.raBytes _ [(("isEven", [i64], [i64]), evenOddLitmusCompiled.boundAt 16)]
    [] 0 haux2 hnd_s.2.1 hok.2
  have hdisj : ∀ (i₁ j₂ : Nat) (l : Sym),
      evenOddLitmusCompiled.code[i₁]? = some (litmusTarget.frame.label l) →
      paritySumCompiled.code[j₂]? = some (litmusTarget.frame.label l) → False := by
    intro i₁ j₂ l hi₁ hj₂
    obtain ⟨f₁, hf₁, h₁⟩ := hmem1 i₁ l hi₁
    obtain ⟨f₂, hf₂, h₂⟩ := hmem2 j₂ l hj₂
    have hok₁ := List.all_eq_true.mp hok.1 f₁ hf₁
    have hok₂ := List.all_eq_true.mp hok.2 f₂ hf₂
    rcases h₁ with rfl | ⟨a, rfl⟩ <;> rcases h₂ with hnm | ⟨b, hnm⟩
    · exact hnd_s.2.2 f₁.name (List.mem_map_of_mem hf₁) f₂.name (List.mem_map_of_mem hf₂) hnm
    · exact lname_ne_cross hok₁ hnm.symm
    · exact lname_ne_cross hok₂ hnm
    · exact hnd_s.2.2 f₁.name (List.mem_map_of_mem hf₁) f₂.name
        (List.mem_map_of_mem hf₂) (lname_inj_cross hok₁ hok₂ hnm).1
  intro i j l hi hj
  rw [hprog] at hi hj
  rcases Nat.lt_or_ge i evenOddLitmusCompiled.code.length with hiL | hiR <;>
    rcases Nat.lt_or_ge j evenOddLitmusCompiled.code.length with hjL | hjR
  · rw [List.getElem?_append_left hiL] at hi
    rw [List.getElem?_append_left hjL] at hj
    exact huniq1 i j l hi hj
  · rw [List.getElem?_append_left hiL] at hi
    rw [List.getElem?_append_right hjR] at hj
    exact absurd hj (fun h' => hdisj i (j - evenOddLitmusCompiled.code.length) l hi h')
  · rw [List.getElem?_append_right hiR] at hi
    rw [List.getElem?_append_left hjL] at hj
    exact absurd hi (fun h' => hdisj j (i - evenOddLitmusCompiled.code.length) l hj h')
  · rw [List.getElem?_append_right hiR] at hi
    rw [List.getElem?_append_right hjR] at hj
    have heq := huniq2 (i - evenOddLitmusCompiled.code.length)
      (j - evenOddLitmusCompiled.code.length) l hi hj
    omega

theorem paritySum_linked_fnSpec {k : Nat} (hk : k ≤ 16) :
    litmusTarget.Defined paritySumCombinedHost "paritySum" ∧
      litmusTarget.FnSpec paritySumCombinedHost "paritySum"
        (legalEnv LegalTarget.aarch64 (Env.onlyFn paritySum (paritySumEnv k))
          "paritySum" [i64] [i64])
        (paritySumCompiled.boundAt k) 0 := by
  have hprog : litmusTarget.mach.prog paritySumCombinedHost =
      evenOddLitmusCompiled.code ++ paritySumCompiled.code :=
    litmusLayout.prog_layoutOf _ _
  have hEvenInfix : evenOddLitmusCompiled.code.IsInfixAt
      (litmusTarget.mach.prog paritySumCombinedHost) 0 := by
    rw [hprog]; exact ⟨paritySumCompiled.code, rfl⟩
  have hSumInfix : paritySumCompiled.code.IsInfixAt
      (litmusTarget.mach.prog paritySumCombinedHost) evenOddLitmusCompiled.code.length := by
    rw [hprog]; exact ⟨[], by simp⟩
  have hEvenRestrict := link_scc_export_restrict natRecIdx evenOddLitmusCompiled evenOddRecMod rfl
    paritySumCombinedHost evenOddRecEnv (fun _ _ _ _ _ _ _ => False) 0 hEvenInfix
    paritySumCombined_labelsUnique evenOdd_moduleSccOk evenOdd_supports_mem
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (S := evenOddRecMod.fns.map Fn.sig) (by decide) List.mem_cons_self
    (by simp [evenOddRecMod, isEven, Fn.sig])
  have hext : ∀ p ∈ [(("isEven", [i64], [i64]), evenOddLitmusCompiled.boundAt 16)],
      litmusTarget.FnSpec paritySumCombinedHost p.1.1
        (legalEnv LegalTarget.aarch64
          (Env.restrict (Env.exportScc natRecIdx evenOddRecEnv 16)
            (paritySumMod.externs.map Extern.sig))
          p.1.1 p.1.2.1 p.1.2.2)
        p.2 0 := by
    intro p hp; simp only [List.mem_singleton] at hp; subst hp
    refine Target.FnSpec.of_spec litmusTarget hEvenRestrict.2 fun args m0 Q X hleg => ?_
    rcases hleg with ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hmem, hΓ⟩
    simp only [paritySumMod, Extern.sig, List.map_cons, List.map_nil,
      List.mem_singleton, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl, rfl⟩
    exact ⟨[i64], [i64], has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀,
      by simp [evenOddRecMod, isEven, Fn.sig], hΓ⟩
  have hM : ModuleSccOk natRecIdx paritySumEnv (Env.exportScc natRecIdx evenOddRecEnv 16)
      (paritySumCompiled.stepBound != 0) paritySumMod := by
    refine moduleSccOk_of_step natRecIdx paritySumMod_checkCyclic (fun f hf => by
      simp [paritySumMod] at hf; subst hf; exact paritySum_wf) ?_
    intro k' fn hfn Γ hrec' hext' xs m Q X hspec
    simp [paritySumMod] at hfn; subst hfn
    refine paritySum_step Γ k'
      (fun args' m' Q' X' h => hext' ⟨"isEven", [i64], [i64]⟩ List.mem_cons_self args' m' Q' X' h)
      (fun k'' hk'' args' m' Q' X' h =>
        hrec' paritySum List.mem_cons_self k'' hk'' (Or.inr hk'') args' m' Q' X' h)
      xs m Q X hspec
  have hsupp : ∀ f ∈ paritySumMod.fns,
      (f.earlyOpt).body.supportsSource LegalTarget.aarch64 = true := by
    intro f hf; simp only [paritySumMod, List.mem_singleton] at hf; subst hf; t_kernel_rfl
  exact link_scc_compiled_le natRecIdx paritySumCompiled paritySumMod rfl paritySumCombinedHost
    paritySumEnv (Env.exportScc natRecIdx evenOddRecEnv 16) evenOddLitmusCompiled.code.length
    hSumInfix paritySumCombined_labelsUnique hM hsupp hext
    (fun _ hp _ hq _ => by simp at hp hq; subst hp hq; rfl) (fun _ h => nomatch h)
    hk paritySum List.mem_cons_self

/-! ## 2. Recovering `LinkRec` via `link_rec_of_scc` -/

theorem isEven_link_rec_scc {k : Nat} (hk : k ≤ 16) :
    litmusTarget.Defined evenOddLitmusCompiled.host "isEven" ∧
      litmusTarget.FnSpec evenOddLitmusCompiled.host "isEven"
        (legalEnv LegalTarget.aarch64 (Env.onlyFn isEven (evenOddRecEnv k))
          "isEven" [i64] [i64])
        (evenOddLitmusCompiled.boundAt k) 0 :=
  link_rec_of_scc evenOddLitmusCompiled evenOddRecMod rfl evenOddLitmusCompiled.host
    evenOddRecEnv (fun _ _ _ _ _ _ _ => False) 0 evenOddLitmusCompiled.code_infix_host
    evenOddLitmusCompiled.labelsUnique evenOddRecMod_checkCyclic evenOdd_wf_mem
    evenOdd_supports_mem (fun k _ fn hf => evenOddRecMod_wp_step k fn hf)
    (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) k hk isEven List.mem_cons_self

/-! ## 3. Lexicographic `ι := Nat × Nat` (`Prod.Lex`) Ackermann Example -/

def ack1 (step : Nat → Nat) : Nat → Nat
  | 0 => step 1
  | n + 1 => step (ack1 step n)

def ackNat : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, n => ack1 (ackNat m) n

def ackDepth1 (valStep depStep : Nat → Nat) : Nat → Nat × Nat
  | 0 => (valStep 1, 1 + depStep 1)
  | n + 1 =>
      let p := ackDepth1 valStep depStep n
      (valStep p.1, 1 + Nat.max p.2 (depStep p.1))

def ackDepth : Nat → Nat → Nat
  | 0, _ => 0
  | m + 1, n => (ackDepth1 (ackNat m) (ackDepth m) n).2

private theorem ackDepth1_fst (valStep depStep : Nat → Nat) (n : Nat) :
    (ackDepth1 valStep depStep n).1 = ack1 valStep n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ackDepth1, ack1, ih]

private theorem ackDepth_succ_succ (m n : Nat) :
    ackDepth (m + 1) (n + 1) =
      1 + Nat.max (ackDepth (m + 1) n) (ackDepth m (ackNat (m + 1) n)) := by
  simp only [ackDepth, ackDepth1, ackNat, ackDepth1_fst]

#guard ackNat 0 5 == 6
#guard ackNat 1 4 == 6
#guard ackNat 2 2 == 7
#guard ackDepth 2 2 == 7

private theorem ackNat_gt (m : Nat) : ∀ n : Nat, n < ackNat m n := by
  induction m with
  | zero => intro n; simp [ackNat]
  | succ m ihm =>
      intro n
      induction n with
      | zero =>
          simp only [ackNat, ack1]
          exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt (ihm 1))
      | succ n ihn =>
          have h1 : n + 1 ≤ ackNat (m + 1) n := ihn
          have h2 : ackNat (m + 1) n < ackNat m (ackNat (m + 1) n) := ihm _
          simpa [ackNat, ack1] using Nat.lt_of_le_of_lt h1 h2

private theorem ackNat_lt_succ_left (m n : Nat) : ackNat (m + 1) n < ackNat (m + 1) (n + 1) := by
  simpa [ackNat, ack1] using ackNat_gt m (ackNat (m + 1) n)

def ackIdx : RecIdx (Nat × Nat) := lexNatRecIdx (fun p => ackDepth p.1 p.2)

def ackFn : Fn := tqbe $ack(%m:l, %n:l) -> l {
  %cm =b ceql %m, 0
  jnz %cm, {
    %r0 =l add %n, 1
    ret %r0
  }, {
    %m1 =l sub %m, 1
    %cn =b ceql %n, 0
    jnz %cn, {
      %r1 =l call $ack(%m1, 1:l)
      ret %r1
    }, {
      %n1 =l sub %n, 1
      %inner =l call $ack(%m, %n1)
      %r2 =l call $ack(%m1, %inner)
      ret %r2
    }
  }
}

def ackMod : Module := ⟨[ackFn], [], []⟩

theorem ackFn_wf : Fn.Wf ackFn := by t_wf_reify
theorem ackMod_checkCyclic : checkCyclic ackMod = true := by t_kernel_rfl

def ackSpec (p : Nat × Nat) : Spec [i64, i64] [i64] := fun (m, n, ()) mem Q _ =>
  m.toNat = p.1 ∧ n.toNat = p.2 ∧ ackNat p.1 p.2 < 2 ^ 64 ∧
    Q (BitVec.ofNat 64 (ackNat p.1 p.2), ()) mem

def ackEnv (p : Nat × Nat) : Env
  | "ack", [.bits 64, .bits 64], [.bits 64] => ackSpec p
  | _, _, _ => fun _ _ _ _ => False

private theorem bv64_sub_one_eq {x : BitVec 64} (hx : x.toNat ≠ 0) :
    (x - 1#64).toNat = x.toNat - 1 := by
  have hlt : x.toNat < 2 ^ 64 := x.isLt
  rw [BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  omega

private theorem ack_step (Γ : Env) (p : Nat × Nat)
    (hrec : ∀ p', ackIdx.lt p' p → ackIdx.depth p' < ackIdx.depth p →
      ∀ args m Q X, ackSpec p' args m Q X → Γ "ack" [i64, i64] [i64] args m Q X) :
    ∀ args m Q X, ackSpec p args m Q X → Func.wp Γ ackFn.body args m Q X := by
  rcases p with ⟨pm, pn⟩
  rintro ⟨m, n, ⟨⟩⟩ mem Q X ⟨hm, hn, hbound, hQ⟩
  dsimp only at hm hn hbound hQ
  dsimp only [Func.wp, ackFn]; wp_unfold
  constructor
  · intro hm0
    have hpm : pm = 0 := by rw [← hm, hm0]; rfl
    subst hpm
    have hval : n + 1#64 = BitVec.ofNat 64 (ackNat 0 pn) := by
      apply BitVec.eq_of_toNat_eq
      simp only [ackNat] at hbound ⊢
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hn,
        Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 64)]
    simpa [hval] using hQ
  · intro hmne
    have hmnz : m.toNat ≠ 0 := fun hz => hmne (BitVec.eq_of_toNat_eq hz)
    obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hmnz
    have hpm : pm = m' + 1 := by rw [← hm, hm']
    subst hpm
    have hm1 : (m - 1#64).toNat = m' := by rw [bv64_sub_one_eq hmnz, hm']; omega
    constructor
    · intro hn0
      have hpn : pn = 0 := by rw [← hn, hn0]; rfl
      subst hpn
      have hlt : ackIdx.lt (m', 1) (m' + 1, 0) := Prod.Lex.left _ _ (Nat.lt_succ_self m')
      have hdep : ackIdx.depth (m', 1) < ackIdx.depth (m' + 1, 0) := by
        simp [ackIdx, lexNatRecIdx, ackDepth, ackDepth1]
      refine wp_call_of_spec _ _ (hrec (m', 1) hlt hdep (m - 1#64, 1#64, ()) mem Q X
        ⟨hm1, rfl, ?_, ?_⟩)
      · simpa [ackNat, ack1] using hbound
      · simpa [ackNat, ack1] using hQ
    · intro hnne
      have hnnz : n.toNat ≠ 0 := fun hz => hnne (BitVec.eq_of_toNat_eq hz)
      obtain ⟨n', hn'⟩ := Nat.exists_eq_succ_of_ne_zero hnnz
      have hpn : pn = n' + 1 := by rw [← hn, hn']
      subst hpn
      have hn1 : (n - 1#64).toNat = n' := by rw [bv64_sub_one_eq hnnz, hn']; omega
      have hlt1 : ackIdx.lt (m' + 1, n') (m' + 1, n' + 1) :=
        Prod.Lex.right _ (Nat.lt_succ_self n')
      have hdep1 : ackIdx.depth (m' + 1, n') < ackIdx.depth (m' + 1, n' + 1) := by
        simp only [ackIdx, lexNatRecIdx, ackDepth_succ_succ]
        rw [Nat.add_comm 1]; exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
      have hinner_lt : ackNat (m' + 1) n' < 2 ^ 64 :=
        Nat.lt_trans (ackNat_lt_succ_left m' n') hbound
      refine ⟨fun r m'mem => r = (BitVec.ofNat 64 (ackNat (m' + 1) n'), ()) ∧ m'mem = mem,
        X, hrec (m' + 1, n') hlt1 hdep1 (m, n - 1#64, ()) mem _ X
          ⟨hm, hn1, hinner_lt, ⟨rfl, rfl⟩⟩, ?_, fun _ _ _ _ h => h⟩
      rintro ⟨inner, ⟨⟩⟩ mem' ⟨hr, hmem'⟩
      have hinner : inner = BitVec.ofNat 64 (ackNat (m' + 1) n') := (Prod.ext_iff.mp hr).1
      subst hinner; rcases hmem' with rfl
      have hinner_toNat : (BitVec.ofNat 64 (ackNat (m' + 1) n')).toNat = ackNat (m' + 1) n' := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hinner_lt]
      have hlt2 : ackIdx.lt (m', ackNat (m' + 1) n') (m' + 1, n' + 1) :=
        Prod.Lex.left _ _ (Nat.lt_succ_self m')
      have hdep2 : ackIdx.depth (m', ackNat (m' + 1) n') < ackIdx.depth (m' + 1, n' + 1) := by
        simp only [ackIdx, lexNatRecIdx, ackDepth_succ_succ]
        rw [Nat.add_comm 1]; exact Nat.lt_succ_of_le (Nat.le_max_right _ _)
      wp_unfold
      refine wp_call_of_spec _ _ (hrec (m', ackNat (m' + 1) n') hlt2 hdep2
        (m - 1#64, BitVec.ofNat 64 (ackNat (m' + 1) n'), ()) mem' Q X
        ⟨hm1, hinner_toNat, ?_, ?_⟩)
      · simpa [ackNat, ack1] using hbound
      · simpa [ackNat, ack1] using hQ

splice_module_hints ackHints litmusTarget.toIsa LegalTarget.aarch64 ackMod.fns

theorem ack_litmus_check :
    checkCompileRec litmusTarget litmusLayout LegalTarget.aarch64 [] [] 0 16
      ackMod.fns ackHints 2048 = true := by
  t_kernel_rfl

def ackLitmusCompiled :
    CompiledRec litmusTarget LegalTarget.aarch64 [] [] 0 16
      ackMod.fns ackHints 2048 :=
  compileRecChecked litmusTarget litmusLayout LegalTarget.aarch64 litmusLabelClean
    [] [] 0 16 ackMod.fns ackHints 2048 ack_litmus_check

theorem ackMod_moduleSccOk :
    ModuleSccOk ackIdx ackEnv (fun _ _ _ _ _ _ _ => False)
      (ackLitmusCompiled.stepBound != 0) ackMod := by
  refine moduleSccOk_of_step ackIdx ackMod_checkCyclic
    (fun f hf => by simp [ackMod] at hf; subst hf; exact ackFn_wf) ?_
  intro p fn hfn Γ hrec _ xs m Q X hspec
  simp [ackMod] at hfn; subst hfn
  refine ack_step Γ p (fun p' hlt hdep args' m' Q' X' gp =>
    hrec ackFn List.mem_cons_self p' hlt (Or.inr hdep) args' m' Q' X' gp) xs m Q X hspec

private theorem ack_supports_all :
    ackMod.fns.all (fun f => (f.earlyOpt).body.supportsSource LegalTarget.aarch64) = true := by
  t_kernel_rfl

theorem ack_litmus_fnSpec {p : Nat × Nat}
    (hbound : ackLitmusCompiled.baseBound + ackIdx.depth p * ackLitmusCompiled.stepBound ≤ 2048)
    (hra : ackLitmusCompiled.baseBound + ackIdx.depth p * ackLitmusCompiled.stepBound +
      litmusTarget.frame.raBytes ≤ 2 ^ 64) :
    litmusTarget.Defined ackLitmusCompiled.host "ack" ∧
      litmusTarget.FnSpec ackLitmusCompiled.host "ack" (ackSpec p)
        (ackLitmusCompiled.boundAt (ackIdx.depth p)) 0 :=
  link_scc_compiled_src_noExit ackIdx ackLitmusCompiled ackMod rfl ackEnv
    (fun _ _ _ _ _ _ _ => False) ackMod_moduleSccOk
    (fun f hf => List.all_eq_true.mp ack_supports_all f hf)
    p hbound hra List.mem_cons_self rfl rfl (fun _ _ _ _ _ h => h)

theorem ack_litmus_2_2 :
    Eventually (litmusTarget.mach.step ackLitmusCompiled.host)
      (fun st => litmusTarget.mach.pc st = litmusInit.ra0 ∧
        litmusTarget.mach.getGpr (litmusTarget.mach.data st) litmusInit.ret0 = 7#64)
      (litmusTarget.mach.mkState
        (litmusInit.initState (as := [i64, i64]) (ackLitmusCompiled.boundAt 7) []
          ((2#64, 2#64, ()) : Tup Val [i64, i64]))
        (litmusTarget.mach.labelAddr ackLitmusCompiled.host "ack")) := by
  have hdepth : ackIdx.depth (2, 2) = 7 := rfl
  have hbound : ackLitmusCompiled.baseBound + ackIdx.depth (2, 2) *
      ackLitmusCompiled.stepBound ≤ 2048 := by
    rw [hdepth]; exact ackLitmusCompiled.boundAt_le_max (by decide : 7 ≤ 16)
  have hra : ackLitmusCompiled.baseBound + ackIdx.depth (2, 2) *
      ackLitmusCompiled.stepBound + litmusTarget.frame.raBytes ≤ 2 ^ 64 := by
    rw [hdepth]; exact ackLitmusCompiled.total_ra_le_at (by decide : 7 ≤ 16)
  have hspec := (ack_litmus_fnSpec hbound hra).2
  rw [hdepth] at hspec
  exact run_rec_ret1_i64 litmusInit (as := [i64, i64]) ackLitmusCompiled (by decide : 7 ≤ 16)
    hspec [] ((2#64, 2#64, ()) : Tup Val [i64, i64]) 7#64
    (by decide) rfl (Q := fun r _ => r = (7#64, ()))
    ⟨rfl, rfl, by change ackNat 2 2 < 2 ^ 64; decide,
      by change (BitVec.ofNat 64 (ackNat 2 2), ()) = (7#64, ()); decide⟩ (fun _ _ h => h)

/-! ## 4. Single-Line Axiom Audit -/

#print axioms LeanQbe.T.LinkScc.Env.ofModuleScc_empty_off_sig
#print axioms LeanQbe.T.LinkScc.Env.ofModuleScc_empty_off_extern_sig
#print axioms LeanQbe.T.LinkScc.Env.ofModuleScc_empty_undeclared
#print axioms LeanQbe.T.LinkScc.Env.stepIdx_le_ofModuleScc
#print axioms LeanQbe.T.LinkScc.Env.sound_scc_at
#print axioms LeanQbe.T.LinkScc.Env.sound_scc
#print axioms LeanQbe.T.LinkScc.moduleSccOk_of_step
#print axioms LeanQbe.T.LinkScc.Env.sound_scc_idx
#print axioms LeanQbe.T.LinkScc.defined_of_compileModuleRecAux
#print axioms LeanQbe.T.LinkScc.compileScc_sound
#print axioms LeanQbe.T.LinkScc.link_scc_compiled
#print axioms LeanQbe.T.LinkScc.link_scc_compiled_le
#print axioms LeanQbe.T.LinkScc.link_scc_compiled_host
#print axioms LeanQbe.T.LinkScc.link_scc_compiled_src
#print axioms LeanQbe.T.LinkScc.link_scc_compiled_src_noExit
#print axioms LeanQbe.T.LinkScc.link_scc_export
#print axioms LeanQbe.T.LinkScc.link_scc_export_restrict
#print axioms LeanQbe.T.LinkScc.link_scc_export_host
#print axioms LeanQbe.T.LinkScc.link_scc_export_src_noExit
#print axioms LeanQbe.T.LinkScc.link_rec_of_scc
#print axioms evenOdd_moduleSccOk
#print axioms isEven_exportScc_fnSpec
#print axioms isEven_exportScc_4
#print axioms paritySum_wf
#print axioms paritySumMod_checkCyclic
#print axioms paritySumMod_sccOrder
#print axioms paritySum_check
#print axioms paritySumCombined_progSmall
#print axioms paritySumCombined_labelsUnique
#print axioms paritySum_linked_fnSpec
#print axioms isEven_link_rec_scc
#print axioms ackFn_wf
#print axioms ackMod_checkCyclic
#print axioms ack_litmus_check
#print axioms ackMod_moduleSccOk
#print axioms ack_litmus_fnSpec
#print axioms ack_litmus_2_2

end LeanQbeTest.T.LinkSccTest
