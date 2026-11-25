module

public import LeanQbe.T.Bootstrap0.StageC
public import LeanQbe.T.Bootstrap0.Sound0
public import LeanQbe.T.Amd64.ScalarTarg
public import Kraken.X64.PrintATT
import Lean
meta import Lean
meta import LeanQbe.T.Bootstrap0.StageC

/-!
# Verification Suite for Stage C End-to-End Native Emission & Execution (`StageCTest`)

Validates `LeanQbe.T.Bootstrap0.StageC` on seven small scalar C0 functions (`stageCTfs`) compiled
through `Bridge0`, `leanqbe0Compile`, `Sound0`, and `PrintAsm0`:
1. Arm64 zero-cross-import check (confirming no `LeanQbe.T.Arm64` / `Kraken.AArch64` imports).
2. Concrete single-input execution theorems under Kraken x86-64 scalar semantics
   (`Eventually (x64ScalarMach.step stageCHost)`):
   - `stageC_sqr_exec7`: `c0_sqr 7#64 = 49#64` (arithmetic)
   - `stageC_pipe_exec100`: `c0_pipeline 100#64 = 160#64` (multi-function call chain)
   - `stageC_sat_var_exec42`: `sat_lit_var 42#64 = 21#64` (literal variable helper)
   - `stageC_sat_sign_exec43`: `sat_lit_sign 43#64 = 1#64` (literal sign helper)
   - `stageC_sat_neg_exec42`: `sat_lit_neg 42#64 = 43#64` (literal negation helper)
3. `PrintAsm0` / `Kraken.X64.toATT` parity and static directive/slot/stack bounds on `stageCTfs`.
4. Single-line `#print axioms` checks (`[propext, Classical.choice, Quot.sound]` only).
-/

set_option autoImplicit false

public section

namespace LeanQbeBootstrap0Test.StageCTest

open LeanQbe.T
open LeanQbe.T.Amd64
open LeanQbe.T.Bootstrap0
open LeanQbe.T.Frontend.C0

/-! ## 1. Arm64 / AArch64 Isolation Guard -/

#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  let arm := env.allImportedModuleNames.filter fun n =>
    n.toString.startsWith "LeanQbe.T.Arm64" || n.toString.startsWith "Kraken.AArch64"
  if !arm.isEmpty then
    throwError "forbidden Arm64/AArch64 imports: {arm.toList}"

/-! ## 2. Concrete Machine-Code Execution Theorems for Stage C Kernels -/

private theorem stageC_exec_i64 (tf : Frontend.C0.TFlatFn) (nm : String)
    (spec : BitVec 64 → BitVec 64) (x y : BitVec 64)
    (htf : tf ∈ stageCTfs) (hnm : tf.name = nm) (has : tf.as = [i64]) (hrs : tf.rs = [i64])
    (henv : stageCEnv nm [i64] [i64] = fun args m Q _ => Q (spec args.1, ()) m)
    (hb : ((lookupBound0 stageCBounds (lookupSymId? stageCTbl nm).get!).getD 0) ≤ 2048)
    (hspec : spec x = y) :
    Eventually (x64ScalarMach.step stageCHost)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = y)
      (x64ScalarMach.mkState
        (x64ScalarInit.initState (as := [i64])
          ((lookupBound0 stageCBounds (lookupSymId? stageCTbl nm).get!).getD 0) [] (x, ()))
        (x64ScalarMach.labelAddr stageCHost nm)) := by
  have hspec0 := stageC_host_ok.2.2 tf htf
  rw [hnm, has, hrs] at hspec0
  have hsig : (nm, [i64], [i64]) ∈ stageCMod.sigs :=
    List.mem_map.mpr ⟨tf.toFn, List.mem_map.mpr ⟨tf, htf, rfl⟩,
      by simp [Frontend.C0.TFlatFn.toFn, Fn.sig, hnm, has, hrs]⟩
  have hspec_eq : Env.ofModule stageCMod stageCEnv nm [i64] [i64] =
      (fun (args : Tup Val [i64]) m Q _ => Q (spec args.1, ()) m) := by
    rw [← henv]; funext args m Q X
    exact propext ⟨fun h => h.2, fun h => ⟨hsig, h⟩⟩
  rw [hspec_eq] at hspec0
  exact TargetInit.run_ret1_i64_of_fnSpec x64ScalarInit stageCHost hspec0.2 [] (x, ())
    y hb (by decide) (by decide)
    (Q := fun r _ => r = (y, ())) (Prod.ext hspec rfl) (fun _ _ h => h)

/-- Concrete machine execution theorem: `c0_sqr 7#64 = 49#64`. -/
theorem stageC_sqr_exec7 :
    Eventually (x64ScalarMach.step stageCHost)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 49#64)
      (x64ScalarMach.mkState
        (x64ScalarInit.initState (as := [i64])
          ((lookupBound0 stageCBounds (lookupSymId? stageCTbl "c0_sqr").get!).getD 0) [] (7#64, ()))
        (x64ScalarMach.labelAddr stageCHost "c0_sqr")) :=
  stageC_exec_i64 c0SqrTf "c0_sqr" (fun a => a * a) 7#64 49#64
    (by simp [stageCTfs]) rfl rfl rfl rfl (of_decide_eq_true (by t_kernel_rfl)) rfl

/-- Concrete machine execution theorem: multi-fn pipeline `c0_pipeline 100#64 = 160#64`. -/
theorem stageC_pipe_exec100 :
    Eventually (x64ScalarMach.step stageCHost)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 160#64)
      (x64ScalarMach.mkState
        (x64ScalarInit.initState (as := [i64])
          ((lookupBound0 stageCBounds (lookupSymId? stageCTbl "c0_pipeline").get!).getD 0)
          [] (100#64, ()))
        (x64ScalarMach.labelAddr stageCHost "c0_pipeline")) :=
  stageC_exec_i64 c0PipeTf "c0_pipeline" (fun a => a + 10#64 + 20#64 + 30#64) 100#64 160#64
    (by simp [stageCTfs]) rfl rfl rfl rfl (of_decide_eq_true (by t_kernel_rfl)) rfl

/-- Concrete machine execution theorem: SAT/LRAT literal variable `sat_lit_var 42#64 = 21#64`. -/
theorem stageC_sat_var_exec42 :
    Eventually (x64ScalarMach.step stageCHost)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 21#64)
      (x64ScalarMach.mkState
        (x64ScalarInit.initState (as := [i64])
          ((lookupBound0 stageCBounds (lookupSymId? stageCTbl "sat_lit_var").get!).getD 0)
          [] (42#64, ()))
        (x64ScalarMach.labelAddr stageCHost "sat_lit_var")) :=
  stageC_exec_i64 satLitVarTf "sat_lit_var" (fun a => a >>> 1#64) 42#64 21#64
    (by simp [stageCTfs]) rfl rfl rfl rfl (of_decide_eq_true (by t_kernel_rfl)) rfl

/-- Concrete machine execution theorem: SAT/LRAT literal sign `sat_lit_sign 43#64 = 1#64`. -/
theorem stageC_sat_sign_exec43 :
    Eventually (x64ScalarMach.step stageCHost)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 1#64)
      (x64ScalarMach.mkState
        (x64ScalarInit.initState (as := [i64])
          ((lookupBound0 stageCBounds (lookupSymId? stageCTbl "sat_lit_sign").get!).getD 0)
          [] (43#64, ()))
        (x64ScalarMach.labelAddr stageCHost "sat_lit_sign")) :=
  stageC_exec_i64 satLitSignTf "sat_lit_sign" (fun a => a &&& 1#64) 43#64 1#64
    (by simp [stageCTfs]) rfl rfl rfl rfl (of_decide_eq_true (by t_kernel_rfl)) rfl

/-- Concrete machine execution theorem: SAT/LRAT literal negation `sat_lit_neg 42#64 = 43#64`. -/
theorem stageC_sat_neg_exec42 :
    Eventually (x64ScalarMach.step stageCHost)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 43#64)
      (x64ScalarMach.mkState
        (x64ScalarInit.initState (as := [i64])
          ((lookupBound0 stageCBounds (lookupSymId? stageCTbl "sat_lit_neg").get!).getD 0)
          [] (42#64, ()))
        (x64ScalarMach.labelAddr stageCHost "sat_lit_neg")) :=
  stageC_exec_i64 satLitNegTf "sat_lit_neg" (fun a => a ^^^ 1#64) 42#64 43#64
    (by simp [stageCTfs]) rfl rfl rfl rfl (of_decide_eq_true (by t_kernel_rfl)) rfl

/-! ## 3. Assembly Printer Agreement & Static Guards -/

theorem stageC_printAsm_eq_toATT :
    printAsm0 (toAmd64Program (symNameOf stageCTbl) stageCDirs) =
      Kraken.X64.toATT (toAmd64Program (symNameOf stageCTbl) stageCDirs) :=
  stageC_host_ok.2.1

#guard stageCDirs.length == 84

#guard stageCTfs.length == 7

#guard stageCMaxSl == 1

#guard (stageCBounds.map Prod.snd).all (· ≤ 2048)

/-! ## 4. Single-Line `#print axioms` Audit (`[propext, Classical.choice, Quot.sound]`) -/

#print axioms stageC_bridge_ok
#print axioms stageC_compile_ok
#print axioms stageC_bounds_ok
#print axioms stageC_small
#print axioms stageC_acyc
#print axioms stageC_okGuards
#print axioms stageC_moduleOk
#print axioms stageC_host_ok
#print axioms stageC_sqr_exec7
#print axioms stageC_pipe_exec100
#print axioms stageC_sat_var_exec42
#print axioms stageC_sat_sign_exec43
#print axioms stageC_sat_neg_exec42

end LeanQbeBootstrap0Test.StageCTest
