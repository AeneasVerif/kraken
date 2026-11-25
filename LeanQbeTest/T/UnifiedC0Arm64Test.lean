module

public import LeanQbe.T.Unified.Backend.Rega
public import LeanQbe.T.Unified.Frontend.C0
public import LeanQbe.T.Arm64.TargLemmas
public import Kraken.AArch64.Print
public import LeanQbe.T.Logic.MemLemmas
public import LeanQbe.T.FlatLemmas
import LeanQbe.T.Unified.DriverLemmas
import LeanQbe.T.Spill
public meta import Lean
public meta import LeanQbe.T.Unified.Backend.Rega
public meta import LeanQbe.T.Unified.Frontend.C0
public meta import LeanQbe.T.Arm64.Targ
public meta import LeanQbe.T.Arm64.TargLemmas
public meta import Kraken.AArch64.Print
public meta import LeanQbe.T.Spill

/-!
# Tests for `Unified.Backend.Rega` & `Unified.Frontend.C0` on AArch64 (`UnifiedC0Arm64Test`)

AArch64 companion to `UnifiedC0Test` (isolated from `Kraken.X64` / `LeanQbe.T.Amd64`):
1. Arch-isolation `#eval` audit confirming zero X64/Amd64 imports.
2. C0 extension smoke tests (`#include` headers, `#define ADD(a, b)`, `offsetof`, `_Static_assert`,
   and `assertAsCheck`) compiled via `compileC0SourceWithHeaders` and
   `unified c0SourceFrontend armLegalTarget (regaBackend armTarget hints)` →
   `Kraken.AArch64.print`, verified byte-identical against legacy `compileModule` →
   `Kraken.AArch64.print`.
3. Kernel theorems on a 2-function verified C0 module (`TableImpl` + `AllFns Fn.Wf` + `Compiled`):
   `unified_rega_eq_compileFn`, `c0Fn_unified_rega_mapM_eq_compileModule_code`,
   `rega_compiled_ofTable_fnSpec_noExit`, and concrete `armInit` execution via
   `rega_compiled_ofTable_run_fnSpec` (`std3` axioms only).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.UnifiedC0Arm64Test

open LeanQbe.T LeanQbe.T.Unified LeanQbe.T.Arm64

/-! ## 1. Architecture Isolation Check (`0` X64 / Amd64 Imports) -/

#eval show Lean.CoreM Unit from do
  let curMods := (← Lean.getEnv).allImportedModuleNames
  let x64Leaks := curMods.filter fun m =>
    let s := m.toString
    s.startsWith "Kraken.X64" || s.startsWith "LeanQbe.T.Amd64"
  if !x64Leaks.isEmpty then
    throwError "UnifiedC0Arm64Test leaked X64 import: {x64Leaks.toList}"

/-! ## 2. C0 Extensions Smoke Test on AArch64 (`Kraken.AArch64.print`) -/

meta def c0ExtHdrBase : String := "
typedef struct {
  u32 tag;
  u32 pad;
} HeaderMeta;
"

meta def c0ExtHdr : String := "
#include \"base.h\"
#define ADD(a, b) ((a) + (b))
typedef struct {
  HeaderMeta meta;
  u64 payload;
} Packet;
_Static_assert(sizeof(HeaderMeta) == 8, \"HeaderMeta must be 8 bytes\");
_Static_assert(sizeof(Packet) == 16, \"Packet must be 16 bytes\");
_Static_assert(offsetof(Packet, payload) == 8, \"payload offset must be 8\");
"

meta def c0ExtSrc : String := "
#include \"hdr.h\"
u64 pkt_offset_add(u64 a, u64 b) {
  u64 off = offsetof(Packet, payload);
  return ADD(ADD(a, b), off);
}
u64 pkt_double(u64 x) {
  return pkt_offset_add(x, x);
}
"

meta def c0ExtInput : C0SourceInput where
  src := c0ExtSrc
  headers := Std.HashMap.ofList [("base.h", c0ExtHdrBase), ("hdr.h", c0ExtHdr)]
  exits := ["c0_abort"]
  assertAsCheck := true

#eval show IO Unit from do
  let tfs ← IO.ofExcept (compileC0SourceWithHeaders c0ExtInput)
  if tfs.map (·.name) != ["pkt_offset_add", "pkt_double"] then
    throw <| IO.userError s!"Unexpected C0 extension fn names: {tfs.map (·.name)}"
  let fns := tfs.map Frontend.C0.TFlatFn.toFn
  let hints := fns.map (Fn.computeHints armTarget.toIsa armLegalTarget)
  let hintMap := Std.HashMap.ofList ((fns.map Fn.name).zip hints)
  let hfn : Fn → armTarget.toIsa.Hints :=
    fun fn => hintMap.getD fn.name (Spill.hints armTarget.toIsa fn)
  let perFn ← IO.ofExcept (c0SourceCompile armTarget armLegalTarget hfn c0ExtInput)
  let unifiedCode := perFn.flatten
  let (legacyCode, bounds) ← IO.ofExcept
    (regaCompileModule armTarget armLegalTarget [] c0ExtInput.exits 0 fns hints)
  if perFn.length != 2 || bounds.length != 2 then
    throw <| IO.userError "Unexpected compiled function/bound count in Arm64 C0 ext smoke"
  let unifiedAsm := Kraken.AArch64.print unifiedCode
  let legacyAsm := Kraken.AArch64.print legacyCode
  if unifiedAsm.isEmpty then
    throw <| IO.userError "Empty Arm64 print output for C0 extensions smoke"
  if unifiedAsm != legacyAsm || unifiedAsm.toUTF8 != legacyAsm.toUTF8 then
    throw <| IO.userError "Arm64 print mismatch between unified c0SourceFrontend and compileModule"
  if (unifiedAsm.splitOn "pkt_offset_add:").length < 2 ||
      (unifiedAsm.splitOn "pkt_double:").length < 2 then
    throw <| IO.userError "Missing expected function labels in Arm64 print output"
  let msg := s!"OK: Arm64 C0 ext smoke ({unifiedCode.length} dirs, {unifiedAsm.toUTF8.size} B)"
  IO.println msg

/-! ## 3. Kernel `TableImpl` + `Compiled` + `armInit` Verification -/

@[expose] def c0StepSpec (a b : BitVec 64) : BitVec 64 := (a + b) + 8#64
@[expose] def c0PairSpec (x : BitVec 64) : BitVec 64 := c0StepSpec x (x + 1#64)

@[expose] def c0StepTf : Frontend.C0.TFlatFn :=
  ⟨"c0_step", [i64, i64], [i64],
    .let_ (op2 (.add i64) (.var 1) (.var 0)) <|
    .let_ (op2 (.add i64) (.var 0) (.imm 8#64)) <|
    .ret (.var 0, ())⟩

@[expose] def c0PairTf : Frontend.C0.TFlatFn :=
  ⟨"c0_pair", [i64], [i64],
    .let_ (op2 (.add i64) (.var 0) (.imm 1#64)) <|
    .call "c0_step" (as := [i64, i64]) [i64] (.var 1, .var 0, ()) <|
    .ret (.var 0, ())⟩

@[expose] def c0DemoTfs : List Frontend.C0.TFlatFn := [c0StepTf, c0PairTf]
@[expose] def c0DemoMod : Module := c0SourceModule [] c0DemoTfs

@[expose] def c0DemoTable : List SpecEntry :=
  [ SpecEntry.ofFn c0StepTf.toFn
      (fun (a, b, ()) _ Q _ => ∀ m', Q (c0StepSpec a b, ()) m') true,
    SpecEntry.ofFn c0PairTf.toFn
      (fun (x, ()) _ Q _ => ∀ m', Q (c0PairSpec x, ()) m') true ]

theorem c0DemoMod_acyclic : c0DemoMod.checkAcyclic = true := by
  rfl

theorem c0DemoMod_allWf : AllFns Fn.Wf c0DemoMod.fns :=
  ⟨c0StepTf.toFn_wf, c0PairTf.toFn_wf, trivial⟩

theorem c0DemoMod_tableImpl :
    TableImpl (Env.ofTable c0DemoTable) c0DemoMod.fns c0DemoTable := by
  refine ⟨?_, ?_, trivial⟩
  · refine SpecEntry.Impl.of ?_
    rintro ⟨a, b, ⟨⟩⟩ m Q X hQ
    exact hQ m
  · refine SpecEntry.Impl.of ?_
    rintro ⟨x, ⟨⟩⟩ m Q X hQ
    refine ⟨fun res _ => res = (c0StepSpec x (x + 1#64), ()), X, ?_, ?_, fun _ _ _ _ hx => hx⟩
    · exact (Env.ofTable_cons_self _ _ _ _ _ _).mpr (fun _ => rfl)
    · rintro res m' rfl
      exact hQ m'

@[expose] def c0StepHintsArm : armTarget.toIsa.Hints where
  dest :=
    .node none
      (.node none (.node (some (.gpr (.reg .X0))) .empty .empty) .empty)
      (.node (some (.gpr (.reg .X0))) .empty .empty)
  deferLea := .node (some true) .empty .empty

@[expose] def c0PairHintsArm : armTarget.toIsa.Hints where
  dest := .node none (.node (some (.gpr (.reg .X1))) .empty .empty) .empty

@[expose] def c0DemoHintsArm : List armTarget.toIsa.Hints := [c0StepHintsArm, c0PairHintsArm]

@[expose] def c0DemoHintFnArm (fn : Fn) : armTarget.toIsa.Hints :=
  if fn.name == "c0_step" then c0StepHintsArm else c0PairHintsArm

theorem c0DemoCompiledArm_check :
    checkCompile armTarget armLayout armLegalTarget [] [] 0 c0DemoMod.fns c0DemoHintsArm 2048 =
      true := by
  t_kernel_rfl

noncomputable def c0DemoCompiledArm :
    Compiled armTarget armLegalTarget [] [] 0 c0DemoMod.fns c0DemoHintsArm 2048 :=
  compileChecked armTarget armLayout armLegalTarget armLabelClean [] [] 0
    c0DemoMod.fns c0DemoHintsArm 2048 c0DemoCompiledArm_check

theorem c0Demo_step_supportsArm :
    (c0StepTf.toFn.earlyOpt).body.supportsSource armLegalTarget = true := by
  t_kernel_rfl

theorem c0Demo_step_unified_eq_compileFn_arm :
    (unified c0FnFrontend armLegalTarget (regaBackend armTarget c0DemoHintFnArm)).run
        c0StepTf.toFn =
      compileFn armTarget.toIsa armLegalTarget
        (c0DemoHintFnArm (c0StepTf.toFn.mid armLegalTarget)) c0StepTf.toFn :=
  unified_rega_eq_compileFn c0FnFrontend armTarget armLegalTarget c0DemoHintFnArm
    c0StepTf.toFn c0StepTf.toFn rfl c0Demo_step_supportsArm

theorem c0Demo_mapM_eq_compileModule_arm :
    ∃ perFn,
      (unified c0FnFrontend armLegalTarget (regaBackend armTarget c0DemoHintFnArm)).mapM
          c0DemoMod.fns = .ok perFn ∧
        perFn.flatten = c0DemoCompiledArm.code := by
  refine c0Fn_unified_rega_mapM_eq_compileModule_code armTarget armLegalTarget [] [] 0
    c0DemoMod.fns c0DemoHintsArm c0DemoHintFnArm ?_ c0DemoCompiledArm.compileModule_eq
  intro i hi hj
  rcases i with _ | i
  · rfl
  · rcases i with _ | i
    · rfl
    · dsimp only [c0DemoHintsArm, List.length] at hj
      omega

theorem c0Demo_pair_fnSpec_arm :
    armTarget.Defined c0DemoCompiledArm.host "c0_pair" ∧
    armTarget.FnSpec c0DemoCompiledArm.host "c0_pair"
      (Env.ofTable c0DemoTable "c0_pair" [i64] [i64])
      (c0DemoCompiledArm.bound "c0_pair") 0 := by
  have hmem : c0PairTf.toFn ∈ c0DemoMod.fns := List.mem_cons_of_mem _ List.mem_cons_self
  have hnoex : ∀ e ∈ c0DemoTable, e.noExit = true := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he'
    · rfl
    · rcases List.mem_cons.mp he' with rfl | hnil
      · rfl
      · nomatch hnil
  exact rega_compiled_ofTable_fnSpec_noExit c0DemoMod_acyclic c0DemoMod_allWf
    c0DemoMod_tableImpl hnoex c0DemoCompiledArm hmem rfl rfl

theorem c0Demo_pair_runs_23_arm :
    Eventually (armTarget.mach.step c0DemoCompiledArm.host)
      (fun st =>
        armTarget.mach.pc st = armInit.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) armInit.ret0 = 23#64)
      (armTarget.mach.mkState
        (armInit.initState (as := [i64]) (c0DemoCompiledArm.bound "c0_pair") [] (7#64, ()))
        (armTarget.mach.labelAddr c0DemoCompiledArm.host "c0_pair")) := by
  have hmem : c0PairTf.toFn ∈ c0DemoMod.fns := List.mem_cons_of_mem _ List.mem_cons_self
  have hmem0 : ([] : List UInt8).length ≤ 8192 := by decide
  have hargs : (armTarget.toIsa.assignArgs [i64]).isSome = true := by rfl
  let Q : Post [i64] := fun rets _ => rets = (23#64, ())
  let X : XPost := fun _ _ _ _ => False
  have hspec : Env.ofTable c0DemoTable "c0_pair" [i64] [i64] (7#64, ()) (List.At [] 0x1000#64) Q
      (fun g cs xs m' =>
        X g (armLegalTarget.legalSig cs) (encodeTup armLegalTarget cs xs) m') := by
    have hne : ("c0_step" : Sym) ≠ "c0_pair" := by decide
    exact (Env.ofTable_cons_ne hne _ _ _ _).mpr
      ((Env.ofTable_cons_self _ _ _ _ _ _).mpr (fun _ => rfl))
  refine rega_compiled_ofTable_run_fnSpec armInit c0DemoMod_acyclic c0DemoMod_allWf
    c0DemoMod_tableImpl c0DemoCompiledArm hmem rfl rfl [] (7#64, ()) hmem0 hargs hspec ?_
    (by omega)
  rintro st (⟨hpc, rets, m', hQ, hrets, _⟩ | ⟨_, _, _, _, hX, _⟩)
  · have hr : rets = (23#64, ()) := hQ
    subst hr
    exact ⟨hpc, armInit.retsIn_singleton 23#64 _ hrets⟩
  · exact hX.elim

#print axioms c0Demo_step_unified_eq_compileFn_arm
#print axioms c0Demo_mapM_eq_compileModule_arm
#print axioms c0Demo_pair_fnSpec_arm
#print axioms c0Demo_pair_runs_23_arm

end LeanQbeTest.T.UnifiedC0Arm64Test
