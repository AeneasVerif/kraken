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

Validates `LeanQbe.T.Bootstrap0.StageC` on seven small scalar C0 functions (`stageCTfs`):
1. Arm64 zero-cross-import check (confirming no `LeanQbe.T.Arm64` / `Kraken.AArch64` imports).
2. Concrete single-input execution theorems under Kraken x86-64 scalar semantics.
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
  let arm := (← Lean.getEnv).allImportedModuleNames.filter fun n =>
    n.toString.startsWith "LeanQbe.T.Arm64" || n.toString.startsWith "Kraken.AArch64"
  if !arm.isEmpty then throwError "forbidden Arm64/AArch64 imports: {arm.toList}"

/-! ## 2. Concrete Machine-Code Execution Theorems for Stage C Kernels -/

local macro "stageC_exec_thm" id:ident tf:ident nm:str spec:term:max x:term:max "=>" y:term :
    command =>
  `(theorem $id :
      Eventually (x64ScalarMach.step stageCHost)
        (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = $y)
        (x64ScalarMach.mkState
          (x64ScalarInit.initState (as := [i64])
            ((lookupBound0 stageCBounds (lookupSymId? stageCTbl $nm).get!).getD 0)
            [] ($x, ()))
          (x64ScalarMach.labelAddr stageCHost $nm)) :=
    stageC_exec_i64 $tf $nm $spec $x $y
      (by simp [stageCTfs]) rfl rfl rfl rfl (of_decide_eq_true (by t_kernel_rfl)) rfl)

stageC_exec_thm stageC_sqr_exec7 c0SqrTf "c0_sqr" (fun a => a * a) 7#64 => 49#64
stageC_exec_thm stageC_pipe_exec100 c0PipeTf "c0_pipeline"
  (· + 10#64 + 20#64 + 30#64) 100#64 => 160#64
stageC_exec_thm stageC_sat_var_exec42 satLitVarTf "sat_lit_var" (· >>> 1#64) 42#64 => 21#64
stageC_exec_thm stageC_sat_sign_exec43 satLitSignTf "sat_lit_sign" (· &&& 1#64) 43#64 => 1#64
stageC_exec_thm stageC_sat_neg_exec42 satLitNegTf "sat_lit_neg" (· ^^^ 1#64) 42#64 => 43#64

/-! ## 3. Assembly Printer Agreement & Static Guards -/

theorem stageC_printAsm_eq_toATT :
    printAsm0 (toAmd64Program (symNameOf stageCTbl) stageCDirs) =
      Kraken.X64.toATT (toAmd64Program (symNameOf stageCTbl) stageCDirs) :=
  stageC_host_ok.2.1

#guard stageCDirs.length == 84 && stageCTfs.length == 7 && stageCMaxSl == 1 &&
  (stageCBounds.map Prod.snd).all (· ≤ 2048)

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
