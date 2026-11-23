module

public import LeanQbe.T.LinkRecLemmas
public import LeanQbe.T.Examples.LinkRec
public import LeanQbeTest.T.MainTest
public import LeanQbe.T.MainSplice
public meta import Lean
public meta import LeanQbe.T.MainSplice
public meta import LeanQbe.T.Examples.LinkRec
public meta import LeanQbeTest.T.RegaLitmusTarget

/-!
# Tests for Measure/Fuel-Indexed Cyclic Module Linking

Exercises `LeanQbe.T.LinkRec`, `LeanQbe.T.LinkRecLemmas`, and `LeanQbe.T.Examples.LinkRec` on
`RegaLitmus.litmusTarget`:
1. Mutual recursion `isEven`/`isOdd` (direct cross-function calls): `checkAcyclic = false`,
   `checkCyclic = true`, `t_wf_reify`, `Env.sound_rec` / `Env.sound_rec_unfold`, `TargetLayout`
   (`litmusLayout` and `litmusLayoutWithLabels`), and concrete `TargetInit.run_rec_ret1_i64`
   execution (`isEven 4 = 1`, `isEven 5 = 0`, `isOdd 5 = 1`).
2. Fuel-guarded countdown `recSum` with `"out_of_fuel"` `.exit`: `t_wf_reify`, `Env.sound_rec`,
   normal return (`recSum 3 5 = 6`), and fuel-exhaustion `.exit` (`recSum 5 2 → out_of_fuel(3)`).
3. Mixed acyclic-external + cyclic SCC linking (`incHelper` + `recInc` via `extCallees`), plus
   negative rejections (missing exit, stack-budget overflow, external name collision).
4. Single-line `[propext, Classical.choice, Quot.sound]` `#print axioms` audit.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.LinkRecTest

open LeanQbe.T LeanQbe.T.LinkRec LeanQbe.T.RegaLitmus LeanQbeTest.T.MainTest
open LeanQbe.T.Notation Std Std.ExtHashMap Kraken.Bedrock2.Test

/-! ## 1. `t_wf_reify`, Acyclic Rejection vs Cyclic Acceptance, and `Env.sound_rec` -/

theorem isEven_wf_reify : Fn.Wf isEven := by t_wf_reify
theorem isOdd_wf_reify : Fn.Wf isOdd := by t_wf_reify
theorem recSum_wf_reify : Fn.Wf recSum := by t_wf_reify

theorem evenOddRecMod_not_acyclic : evenOddRecMod.checkAcyclic = false := by rfl
theorem recSumMod_not_acyclic : recSumMod.checkAcyclic = false := by rfl

theorem evenOdd_sound_rec : ∀ fn ∈ evenOddRecMod.fns, ∀ xs m Q X,
    Env.ofModuleRec evenOddRecMod evenOddRecEnv (fun _ _ _ _ _ _ _ => False)
      fn.name fn.as fn.rs xs m Q X →
    Func.wp (Env.ofModuleRec evenOddRecMod evenOddRecEnv (fun _ _ _ _ _ _ _ => False))
      fn.body xs m Q X :=
  Env.sound_rec evenOddRecMod_moduleRecOk

theorem evenOdd_sound_rec_unfold : ∀ k, ∀ fn ∈ evenOddRecMod.fns, ∀ xs m Q X,
    evenOddRecEnv k fn.name fn.as fn.rs xs m Q X →
    Env.unfoldRecAt evenOddRecMod (fun _ _ _ _ _ _ _ => False) k
      fn.name fn.as fn.rs xs m Q X :=
  Env.sound_rec_unfold evenOddRecMod_moduleRecOk

theorem recSum_sound_rec : ∀ fn ∈ recSumMod.fns, ∀ xs m Q X,
    Env.ofModuleRec recSumMod recSumRecEnv (fun _ _ _ _ _ _ _ => False)
      fn.name fn.as fn.rs xs m Q X →
    Func.wp (Env.ofModuleRec recSumMod recSumRecEnv (fun _ _ _ _ _ _ _ => False))
      fn.body xs m Q X :=
  Env.sound_rec recSumMod_moduleRecOk

theorem recSum_sound_rec_unfold : ∀ k, ∀ fn ∈ recSumMod.fns, ∀ xs m Q X,
    recSumRecEnv k fn.name fn.as fn.rs xs m Q X →
    Env.unfoldRecAt recSumMod (fun _ _ _ _ _ _ _ => False) k
      fn.name fn.as fn.rs xs m Q X :=
  Env.sound_rec_unfold recSumMod_moduleRecOk

/-! ## 2. `evenOddRecMod` Machine Compilation (`TargetLayout` & `CompiledRec`) -/

splice_module_hints evenOddLitmusHints litmusTarget.toIsa LegalTarget.aarch64 evenOddRecMod.fns

theorem evenOdd_litmus_check :
    checkCompileRec litmusTarget litmusLayout LegalTarget.aarch64 [] [] 0 16
      evenOddRecMod.fns evenOddLitmusHints 2048 = true := by
  t_kernel_rfl

theorem evenOdd_litmus_check_withLabels :
    checkCompileRecWithLabels litmusTarget litmusLayoutWithLabels LegalTarget.aarch64 [] [] 0 16
      evenOddRecMod.fns evenOddLitmusHints 2048 = true := by
  t_kernel_rfl

def evenOddLitmusCompiled :
    CompiledRec litmusTarget LegalTarget.aarch64 [] [] 0 16
      evenOddRecMod.fns evenOddLitmusHints 2048 :=
  compileRecChecked litmusTarget litmusLayout LegalTarget.aarch64 litmusLabelClean
    [] [] 0 16 evenOddRecMod.fns evenOddLitmusHints 2048 evenOdd_litmus_check

def evenOddLitmusCompiledWithLabels :
    CompiledRec litmusTarget LegalTarget.aarch64 [] [] 0 16
      evenOddRecMod.fns evenOddLitmusHints 2048 :=
  compileRecCheckedWithLabels litmusTarget litmusLayoutWithLabels LegalTarget.aarch64
    [] [] 0 16 evenOddRecMod.fns evenOddLitmusHints 2048 evenOdd_litmus_check_withLabels

private theorem evenOdd_supports_all :
    evenOddRecMod.fns.all (fun f => (f.earlyOpt).body.supportsSource LegalTarget.aarch64) =
      true := by
  t_kernel_rfl

private theorem evenOdd_wf_mem : ∀ f ∈ evenOddRecMod.fns, f.Wf := by
  intro f hf
  simp only [evenOddRecMod, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl <;> first | exact isEven_wf_reify | exact isOdd_wf_reify

private theorem evenOdd_supports_mem :
    ∀ f ∈ evenOddRecMod.fns, (f.earlyOpt).body.supportsSource LegalTarget.aarch64 = true :=
  fun f hf => List.all_eq_true.mp evenOdd_supports_all f hf

theorem isEven_litmus_fnSpec {k : Nat} (hk : k ≤ 16) :
    litmusTarget.Defined evenOddLitmusCompiled.host "isEven" ∧
      litmusTarget.FnSpec evenOddLitmusCompiled.host "isEven" (isEvenSpec k)
        (evenOddLitmusCompiled.boundAt k) 0 :=
  link_rec_compiled_src_noExit evenOddLitmusCompiled evenOddRecMod rfl evenOddRecEnv
    (fun _ _ _ _ _ _ _ => False) evenOddRecMod_checkCyclic evenOdd_wf_mem evenOdd_supports_mem
    (fun k _ fn hf => evenOddRecMod_wp_step k fn hf) hk List.mem_cons_self rfl rfl
    (fun _ _ _ _ _ h => h)

theorem isOdd_litmus_fnSpec {k : Nat} (hk : k ≤ 16) :
    litmusTarget.Defined evenOddLitmusCompiled.host "isOdd" ∧
      litmusTarget.FnSpec evenOddLitmusCompiled.host "isOdd" (isOddSpec k)
        (evenOddLitmusCompiled.boundAt k) 0 :=
  link_rec_compiled_src_noExit evenOddLitmusCompiled evenOddRecMod rfl evenOddRecEnv
    (fun _ _ _ _ _ _ _ => False) evenOddRecMod_checkCyclic evenOdd_wf_mem evenOdd_supports_mem
    (fun k _ fn hf => evenOddRecMod_wp_step k fn hf) hk
    (List.mem_cons_of_mem _ List.mem_cons_self) rfl rfl (fun _ _ _ _ _ h => h)

theorem isEven_litmus_4 :
    Eventually (litmusTarget.mach.step evenOddLitmusCompiled.host)
      (fun st => litmusTarget.mach.pc st = litmusInit.ra0 ∧
        litmusTarget.mach.getGpr (litmusTarget.mach.data st) litmusInit.ret0 = 1#64)
      (litmusTarget.mach.mkState
        (litmusInit.initState (as := [i64]) (evenOddLitmusCompiled.boundAt 4) []
          ((4#64, ()) : Tup Val [i64]))
        (litmusTarget.mach.labelAddr evenOddLitmusCompiled.host "isEven")) :=
  run_rec_ret1_i64 litmusInit (as := [i64]) evenOddLitmusCompiled (by decide : 4 ≤ 16)
    (isEven_litmus_fnSpec (by decide)).2 [] ((4#64, ()) : Tup Val [i64]) 1#64
    (by decide) rfl (Q := fun r _ => r = (1#64, ())) ⟨by decide, rfl⟩ (fun _ _ h => h)

theorem isEven_litmus_5 :
    Eventually (litmusTarget.mach.step evenOddLitmusCompiled.host)
      (fun st => litmusTarget.mach.pc st = litmusInit.ra0 ∧
        litmusTarget.mach.getGpr (litmusTarget.mach.data st) litmusInit.ret0 = 0#64)
      (litmusTarget.mach.mkState
        (litmusInit.initState (as := [i64]) (evenOddLitmusCompiled.boundAt 5) []
          ((5#64, ()) : Tup Val [i64]))
        (litmusTarget.mach.labelAddr evenOddLitmusCompiled.host "isEven")) :=
  run_rec_ret1_i64 litmusInit (as := [i64]) evenOddLitmusCompiled (by decide : 5 ≤ 16)
    (isEven_litmus_fnSpec (by decide)).2 [] ((5#64, ()) : Tup Val [i64]) 0#64
    (by decide) rfl (Q := fun r _ => r = (0#64, ())) ⟨by decide, rfl⟩ (fun _ _ h => h)

theorem isOdd_litmus_5 :
    Eventually (litmusTarget.mach.step evenOddLitmusCompiled.host)
      (fun st => litmusTarget.mach.pc st = litmusInit.ra0 ∧
        litmusTarget.mach.getGpr (litmusTarget.mach.data st) litmusInit.ret0 = 1#64)
      (litmusTarget.mach.mkState
        (litmusInit.initState (as := [i64]) (evenOddLitmusCompiled.boundAt 5) []
          ((5#64, ()) : Tup Val [i64]))
        (litmusTarget.mach.labelAddr evenOddLitmusCompiled.host "isOdd")) :=
  run_rec_ret1_i64 litmusInit (as := [i64]) evenOddLitmusCompiled (by decide : 5 ≤ 16)
    (isOdd_litmus_fnSpec (by decide)).2 [] ((5#64, ()) : Tup Val [i64]) 1#64
    (by decide) rfl (Q := fun r _ => r = (1#64, ())) ⟨by decide, rfl⟩ (fun _ _ h => h)

/-! ## 3. `recSumMod` Machine Compilation, Normal Return, `.exit`, & Negative Rejections -/

splice_module_hints recSumLitmusHints litmusTarget.toIsa LegalTarget.aarch64 recSumMod.fns

theorem recSum_litmus_check :
    checkCompileRec litmusTarget litmusLayout LegalTarget.aarch64 [] ["out_of_fuel"] 16 16
      recSumMod.fns recSumLitmusHints 2048 = true := by
  t_kernel_rfl

def recSumLitmusCompiled :
    CompiledRec litmusTarget LegalTarget.aarch64 [] ["out_of_fuel"] 16 16
      recSumMod.fns recSumLitmusHints 2048 :=
  compileRecChecked litmusTarget litmusLayout LegalTarget.aarch64 litmusLabelClean
    [] ["out_of_fuel"] 16 16 recSumMod.fns recSumLitmusHints 2048 recSum_litmus_check

private theorem recSum_supports_all :
    recSumMod.fns.all (fun f => (f.earlyOpt).body.supportsSource LegalTarget.aarch64) = true := by
  t_kernel_rfl

theorem recSum_litmus_fnSpec {k : Nat} (hk : k ≤ 16) :
    litmusTarget.Defined recSumLitmusCompiled.host "recSum" ∧
      litmusTarget.FnSpec recSumLitmusCompiled.host "recSum"
        (fun args m Q X => recSumSpec k args m Q
          (fun g cs xs m' => X g (LegalTarget.aarch64.legalSig cs)
            (encodeTup LegalTarget.aarch64 cs xs) m'))
        (recSumLitmusCompiled.boundAt k) 16 :=
  link_rec_compiled_src recSumLitmusCompiled recSumMod rfl recSumRecEnv
    (fun _ _ _ _ _ _ _ => False) recSumMod_checkCyclic
    (fun f hf => by simp [recSumMod] at hf; subst hf; exact recSum_wf_reify)
    (fun f hf => List.all_eq_true.mp recSum_supports_all f hf)
    (fun k _ fn hf => recSumMod_wp_step k fn hf) hk List.mem_cons_self rfl rfl

theorem recSum_litmus_normal :
    Eventually (litmusTarget.mach.step recSumLitmusCompiled.host)
      (fun st => litmusTarget.mach.pc st = litmusInit.ra0 ∧
        litmusTarget.mach.getGpr (litmusTarget.mach.data st) litmusInit.ret0 = 6#64)
      (litmusTarget.mach.mkState
        (litmusInit.initState (as := [i64, i64]) (recSumLitmusCompiled.boundAt 5) []
          ((3#64, 5#64, ()) : Tup Val [i64, i64]))
        (litmusTarget.mach.labelAddr recSumLitmusCompiled.host "recSum")) := by
  have ho : recSumOutcome (3#64) (5#64).toNat = .inl 6#64 := by decide
  refine run_rec_fnSpec litmusInit (as := [i64, i64]) recSumLitmusCompiled (by decide : 5 ≤ 16)
    (recSum_litmus_fnSpec (by decide)).2 [] ((3#64, 5#64, ()) : Tup Val [i64, i64])
    (by decide) rfl (Q := fun r _ => r = (6#64, ())) (X := fun _ _ _ _ => False)
    ⟨by decide, by change match recSumOutcome 3#64 (5#64).toNat with
      | .inl s => (s, ()) = (6#64, ()) | .inr _ => False; rw [ho]⟩ ?_
  rintro st (⟨hpc, rets, m', hq, hrets, _⟩ | ⟨_, _, _, _, hx, _⟩)
  · subst hq; exact ⟨hpc, litmusInit.retsIn_singleton 6#64 _ hrets⟩
  · exact hx.elim

theorem recSum_litmus_exit :
    Eventually (litmusTarget.mach.step recSumLitmusCompiled.host)
      (fun st => litmusTarget.mach.pc st =
          litmusTarget.mach.labelAddr recSumLitmusCompiled.host "out_of_fuel" ∧
        litmusTarget.ArgsIn (as := [i64]) (3#64, ()) (litmusTarget.mach.data st))
      (litmusTarget.mach.mkState
        (litmusInit.initState (as := [i64, i64]) (recSumLitmusCompiled.boundAt 2) []
          ((5#64, 2#64, ()) : Tup Val [i64, i64]))
        (litmusTarget.mach.labelAddr recSumLitmusCompiled.host "recSum")) := by
  have ho : recSumOutcome (5#64) (2#64).toNat = .inr 3#64 := by decide
  refine run_rec_fnSpec litmusInit (as := [i64, i64]) recSumLitmusCompiled (by decide : 2 ≤ 16)
    (recSum_litmus_fnSpec (by decide)).2 [] ((5#64, 2#64, ()) : Tup Val [i64, i64])
    (by decide) rfl (Q := fun _ _ => False)
    (X := fun g cs xs _ => g = "out_of_fuel" ∧ cs = [i64] ∧
      HEq xs ((3#64, ()) : Tup Val [i64]))
    ⟨by decide, by rw [ho]; exact ⟨rfl, rfl, HEq.rfl⟩⟩ ?_
  rintro st (⟨_, _, _, hq, _⟩ | ⟨_, _, _, _, ⟨rfl, rfl, hxs⟩, hpc, has⟩)
  · exact hq.elim
  · obtain rfl := eq_of_heq hxs; exact ⟨hpc, has⟩

/-- Undeclared exit `"out_of_fuel"` is rejected. -/
theorem recSum_missing_exit_rejected :
    checkCompileRec litmusTarget litmusLayout LegalTarget.aarch64 [] [] 16 16
      recSumMod.fns recSumLitmusHints 2048 = false := by
  t_kernel_rfl

/-- Fuel budget exceeding `maxBound` is rejected. -/
theorem evenOdd_stack_overflow_rejected :
    checkCompileRec litmusTarget litmusLayout LegalTarget.aarch64 [] [] 0 1000
      evenOddRecMod.fns evenOddLitmusHints 2048 = false := by
  t_kernel_rfl

/-! ## 4. Mixed External Acyclic (`inc`) + Cyclic (`recInc`) Linking -/

def recInc : Fn := tqbe $recInc(%x:l, %k:l) -> l {
  %c =b ceql %k, 0
  jnz %c, {
    ret %x
  }, {
    %x1 =l call $inc(%x)
    %k1 =l sub %k, 1
    %r =l call $recInc(%x1, %k1)
    ret %r
  }
}

def recIncMod : Module := ⟨[recInc], [⟨"inc", [i64], [i64]⟩], []⟩

theorem recInc_wf_reify : Fn.Wf recInc := by t_wf_reify
theorem recIncMod_checkCyclic : checkCyclic recIncMod = true := by t_kernel_rfl

def recIncSpec (k : Nat) : Spec [i64, i64] [i64] := fun (x, n, ()) m Q _ =>
  n.toNat ≤ k ∧ Q (x + n, ()) m

def recIncEnv (k : Nat) : Env
  | "recInc", [.bits 64, .bits 64], [.bits 64] => recIncSpec k
  | _, _, _ => fun _ _ _ _ => False

def incExtEnv : Env
  | "inc", [.bits 64], [.bits 64] => fun (y, ()) m Q _ => Q (y + 1#64, ()) m
  | _, _, _ => fun _ _ _ _ => False

private theorem recInc_step (Γ : Env) (k : Nat)
    (hinc : ∀ args m Q X, incExtEnv "inc" [i64] [i64] args m Q X → Γ "inc" [i64] [i64] args m Q X)
    (hrec : ∀ k' < k, ∀ args m Q X, recIncSpec k' args m Q X →
      Γ "recInc" [i64, i64] [i64] args m Q X) :
    ∀ args m Q X, recIncSpec k args m Q X → Func.wp Γ recInc.body args m Q X := by
  rintro ⟨x, n, ⟨⟩⟩ m Q X ⟨hn, hQ⟩
  dsimp only [Func.wp, recInc]; wp_unfold
  constructor
  · intro h0
    subst h0; simpa using hQ
  · intro hne
    have hnz : n.toNat ≠ 0 := fun hz => hne (BitVec.eq_of_toNat_eq hz)
    have hlt : (n - 1#64).toNat = n.toNat - 1 := by
      have := n.isLt; rw [BitVec.toNat_sub]; simp; omega
    refine ⟨fun r m' => r = (x + 1#64, ()) ∧ m' = m, X,
      hinc (x, ()) m _ X ⟨rfl, rfl⟩, ?_, fun _ _ _ _ h => h⟩
    rintro ⟨y, ⟨⟩⟩ m' ⟨hr, hm'⟩
    have hy : y = x + 1#64 := (Prod.ext_iff.mp hr).1
    subst hy; rcases hm' with rfl
    wp_unfold
    refine wp_call_of_spec _ _ (hrec (k - 1) (by omega) (x + 1#64, n - 1#64, ()) m' Q X ⟨?_, ?_⟩)
    · rw [hlt]; omega
    · rw [BitVec.add_assoc, BitVec.add_comm 1#64 (n - 1#64), BitVec.sub_add_cancel]; exact hQ

theorem recIncMod_wp_step :
    ∀ k : Nat, ∀ fn ∈ recIncMod.fns, ∀ xs m Q X,
      recIncEnv k fn.name fn.as fn.rs xs m Q X →
      Func.wp (Env.stepRec (recIncMod.fns.map Fn.sig) (recIncMod.externs.map Extern.sig)
        recIncEnv incExtEnv k) fn.body xs m Q X := by
  intro k fn hfn xs m Q X hspec
  simp only [recIncMod, List.mem_singleton] at hfn
  subst hfn
  refine recInc_step _ k (fun _ _ _ _ h => Or.inr ⟨by simp [recIncMod, Extern.sig], h⟩)
    (fun k' hk' _ _ _ _ h => Or.inl ⟨by simp [recIncMod, recInc, Fn.sig], k', hk', h⟩)
    xs m Q X hspec

splice_module_hints recIncHints litmusTarget.toIsa LegalTarget.aarch64 recIncMod.fns

theorem recInc_check :
    checkCompileRec litmusTarget litmusLayout LegalTarget.aarch64
      [(("inc", [i64], [i64]), incOnlyCompiled.bound "inc")] [] 0 8
      recIncMod.fns recIncHints 2048 = true := by
  t_kernel_rfl

def recIncCompiled :
    CompiledRec litmusTarget LegalTarget.aarch64
      [(("inc", [i64], [i64]), incOnlyCompiled.bound "inc")] [] 0 8
      recIncMod.fns recIncHints 2048 :=
  compileRecChecked litmusTarget litmusLayout LegalTarget.aarch64 litmusLabelClean
    [(("inc", [i64], [i64]), incOnlyCompiled.bound "inc")] [] 0 8
    recIncMod.fns recIncHints 2048 recInc_check

theorem recInc_extCollision_rejected :
    checkCompileRec litmusTarget litmusLayout LegalTarget.aarch64
      [(("recInc", [i64, i64], [i64]), 0)] [] 0 8
      recIncMod.fns recIncHints 2048 = false := by
  t_kernel_rfl

theorem recIncCombined_progSmall :
    litmusLayout.progSmall (incOnlyCompiled.code ++ recIncCompiled.code) = true := by
  t_kernel_rfl

def recIncCombinedHost : LHost :=
  litmusLayout.layoutOf (incOnlyCompiled.code ++ recIncCompiled.code) recIncCombined_progSmall

theorem recIncCombined_labelsUnique : litmusTarget.LabelsUnique recIncCombinedHost :=
  compileModule_append_rec_labelsUnique litmusLabelClean recIncCombinedHost
    (litmusLayout.prog_layoutOf _ _)
    incOnlyCompiled.compileModule_eq recIncCompiled.compileModuleRec_eq
    (by decide) (by decide)

theorem recInc_linked_fnSpec {k : Nat} (hk : k ≤ 8) :
    litmusTarget.Defined recIncCombinedHost "recInc" ∧
      litmusTarget.FnSpec recIncCombinedHost "recInc"
        (legalEnv LegalTarget.aarch64 (Env.onlyFn recInc (recIncEnv k)) "recInc" [i64, i64] [i64])
        (recIncCompiled.boundAt k) 0 := by
  have hprog : litmusTarget.mach.prog recIncCombinedHost =
      incOnlyCompiled.code ++ recIncCompiled.code := litmusLayout.prog_layoutOf _ _
  have hIncInfix :
      incOnlyCompiled.code.IsInfixAt (litmusTarget.mach.prog recIncCombinedHost) 0 := by
    rw [hprog]; exact ⟨recIncCompiled.code, rfl⟩
  have hRecInfix : recIncCompiled.code.IsInfixAt (litmusTarget.mach.prog recIncCombinedHost)
      incOnlyCompiled.code.length := by
    rw [hprog]; exact ⟨[], by simp⟩
  have hIncSpec := incOnlyCompiled.fnSpec incOnlyMod rfl recIncCombinedHost litmusΓ 0
    hIncInfix recIncCombined_labelsUnique incOnlyMod_checkAcyclic
    (fun f hf => by
      simp only [incOnlyMod, List.mem_singleton] at hf; subst hf
      exact litmusMod_wf fnModInc List.mem_cons_self)
    (fun f hf => by
      simp only [incOnlyMod, List.mem_singleton] at hf; subst hf
      exact litmusMod_supportsSource fnModInc List.mem_cons_self)
    (fun f hf xs m Q X hΓ => by
      simp only [incOnlyMod, List.mem_singleton] at hf; subst hf
      exact litmusMod_wp fnModInc List.mem_cons_self xs m Q X hΓ)
    (fun _ h => nomatch h) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
    (fun _ h => nomatch h) List.mem_cons_self
  have hExt : ∀ p ∈ [(("inc", [i64], [i64]), incOnlyCompiled.bound "inc")],
      litmusTarget.FnSpec recIncCombinedHost p.1.1
        (legalEnv LegalTarget.aarch64
          (Env.restrict incExtEnv (recIncMod.externs.map Extern.sig)) p.1.1 p.1.2.1 p.1.2.2)
        p.2 0 := by
    intro p hp; simp only [List.mem_singleton] at hp; subst hp
    intro args m Q X ⟨as', bs', has', hbs', args', Q', X', h1, h2, h3, hmem, hΓ⟩
    refine hIncSpec.2 args m Q X ⟨as', bs', has', hbs', args', Q', X', h1, h2, h3, ?_, ?_⟩
    · simp only [recIncMod, incOnlyMod, Module.sigs, fnModInc, Fn.sig, Extern.sig,
        List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.mem_singleton, Prod.mk.injEq] at hmem ⊢
      exact hmem
    · simp only [recIncMod, Extern.sig, List.map_cons, List.map_nil,
        List.mem_singleton, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl, rfl⟩
      rcases args' with ⟨y, ⟨⟩⟩
      exact hΓ
  have hsupp : ∀ f ∈ recIncMod.fns,
      (f.earlyOpt).body.supportsSource LegalTarget.aarch64 = true := by
    intro f hf; simp only [recIncMod, List.mem_singleton] at hf; subst hf; t_kernel_rfl
  exact link_rec_compiled recIncCompiled recIncMod rfl recIncCombinedHost recIncEnv incExtEnv
    incOnlyCompiled.code.length hRecInfix recIncCombined_labelsUnique recIncMod_checkCyclic
    (fun f hf => by
      simp only [recIncMod, List.mem_singleton] at hf; subst hf; exact recInc_wf_reify)
    hsupp (fun k _ fn hf => recIncMod_wp_step k fn hf) hExt
    (fun _ hp _ hq _ => by simp at hp hq; subst hp hq; rfl) (fun _ h => nomatch h)
    k hk recInc List.mem_cons_self

/-! ## 5. Single-Line Axiom Audit -/

#print axioms LeanQbe.T.LinkRec.Env.sound_rec
#print axioms LeanQbe.T.LinkRec.Env.sound_rec_unfold
#print axioms LeanQbe.T.LinkRec.compileRec_sound
#print axioms LeanQbe.T.LinkRec.link_rec_compiled
#print axioms LeanQbe.T.LinkRec.link_rec_compiled_host
#print axioms isEven_wf_reify
#print axioms evenOdd_sound_rec
#print axioms recSum_sound_rec
#print axioms evenOdd_litmus_check
#print axioms recSum_litmus_check
#print axioms isEven_litmus_4
#print axioms isEven_litmus_5
#print axioms isOdd_litmus_5
#print axioms recSum_litmus_normal
#print axioms recSum_litmus_exit
#print axioms recInc_linked_fnSpec

end LeanQbeTest.T.LinkRecTest
