module

public import LeanQbe.T.Unified.Backend.Rega
public import LeanQbe.T.Unified.Frontend.C0
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Amd64.PrintAsm0
public import LeanQbe.T.Bootstrap0.Mod0
public import LeanQbe.T.Bootstrap0.Bridge0
public import LeanQbe.T.Bootstrap0.Codec0
public import LeanQbe.T.Logic.MemLemmas
public import LeanQbe.T.FlatLemmas
import LeanQbe.T.Unified.DriverLemmas
import LeanQbe.T.Spill
public meta import Lean
public meta import LeanQbe.T.Unified.Backend.Rega
public meta import LeanQbe.T.Unified.Frontend.C0
public meta import LeanQbe.T.Amd64.Targ
public meta import LeanQbe.T.Amd64.TargLemmas
public meta import LeanQbe.T.Amd64.PrintAsm0
public meta import LeanQbe.T.Bootstrap0.Mod0
public meta import LeanQbe.T.Bootstrap0.Bridge0
public meta import LeanQbe.T.Bootstrap0.Codec0
public meta import LeanQbe.T.Spill
public meta import Kraken.X64.Syntax

/-!
# Tests for `Unified.Backend.Rega` & `Unified.Frontend.C0` on x86-64 (`UnifiedC0Test`)

Verifies Track 1 Shards 1A & 1B end-to-end on `x64Target` (`PrintAsm0`):
1. Arch & layer isolation `#eval` audit: `Unified.Backend.Rega` and `Unified.Frontend.C0`
   transitively import zero `Kraken.X64`, `Kraken.AArch64`, `Amd64`, `Arm64`, `Bootstrap0`, or
   `Examples.Kissat` modules; this x64 suite imports zero Arm64 modules.
2. C0 extension smoke tests (`#include` headers, `#define ADD(a, b)`, `offsetof`, `_Static_assert`,
   and `assertAsCheck`) compiled via `compileC0SourceWithHeaders` and
   `unified c0SourceFrontend x64LegalTarget (regaBackend x64Target hints)` → `printAsm0`,
   verified byte-identical against legacy `compileModule` → `printAsm0`.
3. Kernel theorems on a 2-function verified C0 module (`TableImpl` + `AllFns Fn.Wf` + `Compiled`):
   `c0FnFrontend_ofTable_sat`, `unified_rega_eq_compileFn`, `rega_mapM_eq_compileModule_code`,
   `c0Fn_unified_rega_mapM_eq_compileModule_code`, `rega_compiled_ofTable_fnSpec`, and concrete
   `x64Init` execution via `rega_compiled_ofTable_run_fnSpec` (`std3` axioms only).
4. Bootstrap0 `leanqbe0Tfs` structural byte-encoding hash `#guard` (`124` fns).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.UnifiedC0Test

open LeanQbe.T LeanQbe.T.Unified LeanQbe.T.Amd64 LeanQbe.T.Bootstrap0

/-! ## 1. Architecture & Layer Isolation Checks -/

#eval show IO Unit from do
  let forbiddenPrefixes := [
    "Kraken.X64", "Kraken.AArch64",
    "LeanQbe.T.Amd64", "LeanQbe.T.Arm64",
    "LeanQbe.T.Bootstrap0", "LeanQbe.T.Examples.Kissat"
  ]
  for modName in [`LeanQbe.T.Unified.Backend.Rega, `LeanQbe.T.Unified.Frontend.C0] do
    let env ← Lean.importModules #[{ module := modName }] {}
    let mods := env.allImportedModuleNames
    let leaks := mods.filter fun m =>
      let s := m.toString
      forbiddenPrefixes.any fun p => s.startsWith p
    if !leaks.isEmpty then
      throw <| IO.userError s!"Arch/Boot0/Kissat leak in {modName}: {leaks.toList}"
    IO.println s!"OK: {modName} transitive imports={mods.size}, leaks=0"

#eval show Lean.CoreM Unit from do
  let curMods := (← Lean.getEnv).allImportedModuleNames
  let armLeaks := curMods.filter fun m =>
    let s := m.toString
    s.startsWith "Kraken.AArch64" || s.startsWith "LeanQbe.T.Arm64"
  if !armLeaks.isEmpty then
    throwError "UnifiedC0Test leaked Arm64 import: {armLeaks.toList}"

/-! ## 2. C0 Extensions Smoke Test (`#include`, `ADD`, `offsetof`, `_Static_assert`) -/

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
  for tf in tfs do
    if route (c0SourceFrontend.caps tf) != .direct then
      throw <| IO.userError s!"Non-direct route on {tf.name}"
  let fns := tfs.map Frontend.C0.TFlatFn.toFn
  let hints := fns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  let hintMap := Std.HashMap.ofList ((fns.map Fn.name).zip hints)
  let hfn : Fn → x64Target.toIsa.Hints :=
    fun fn => hintMap.getD fn.name (Spill.hints x64Target.toIsa fn)
  let perFn ← IO.ofExcept (c0SourceCompile x64Target x64LegalTarget hfn c0ExtInput)
  let unifiedCode := perFn.flatten
  let (legacyCode, bounds) ← IO.ofExcept
    (regaCompileModule x64Target x64LegalTarget [] c0ExtInput.exits 0 fns hints)
  if perFn.length != 2 || bounds.length != 2 then
    throw <| IO.userError "Unexpected compiled function/bound count in C0 ext smoke"
  let unifiedAsm := printAsm0 unifiedCode
  let legacyAsm := printAsm0 legacyCode
  if unifiedAsm.isEmpty then
    throw <| IO.userError "Empty x64 PrintAsm0 output for C0 extensions smoke"
  if unifiedAsm != legacyAsm || unifiedAsm.toUTF8 != legacyAsm.toUTF8 then
    throw <| IO.userError "x64 PrintAsm0 mismatch: unified c0SourceFrontend vs compileModule"
  if (unifiedAsm.splitOn "pkt_offset_add:").length < 2 ||
      (unifiedAsm.splitOn "pkt_double:").length < 2 then
    throw <| IO.userError "Missing expected function labels in x64 PrintAsm0 output"
  let msg := s!"OK: x64 C0 ext smoke ({unifiedCode.length} dirs, {unifiedAsm.toUTF8.size} B)"
  IO.println msg

/-! ## 3. Kernel `TableImpl` + `Compiled` + `x64Init` Verification -/

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

theorem c0DemoMod_pair_sat :
    c0FnSrc.Sat c0PairTf.toFn
      (fnSSpec (Env.ofModule c0DemoMod (Env.ofTable c0DemoTable)) "c0_pair") :=
  c0FnFrontend_ofTable_sat c0DemoMod_acyclic c0DemoMod_allWf c0DemoMod_tableImpl
    (List.mem_cons_of_mem _ List.mem_cons_self)

@[expose] def c0StepHintsX64 : x64Target.toIsa.Hints where
  dest :=
    .node none
      (.node none (.node (some (.gpr .rax)) .empty .empty) .empty)
      (.node (some (.gpr .rax)) .empty .empty)
  pre := .node (some { clearFlags := false, moves := [.mov .rax .rdi] }) .empty .empty
  deferLea := .node (some true) .empty .empty

@[expose] def c0PairHintsX64 : x64Target.toIsa.Hints where
  dest := .node none (.node (some (.gpr .rsi)) .empty .empty) .empty

@[expose] def c0DemoHintsX64 : List x64Target.toIsa.Hints := [c0StepHintsX64, c0PairHintsX64]

@[expose] def c0DemoHintFnX64 (fn : Fn) : x64Target.toIsa.Hints :=
  if fn.name == "c0_step" then c0StepHintsX64 else c0PairHintsX64

theorem c0DemoCompiledX64_check :
    checkCompile x64Target x64Layout x64LegalTarget [] [] 0 c0DemoMod.fns c0DemoHintsX64 2048 =
      true := by
  t_kernel_rfl

noncomputable def c0DemoCompiledX64 :
    Compiled x64Target x64LegalTarget [] [] 0 c0DemoMod.fns c0DemoHintsX64 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean [] [] 0
    c0DemoMod.fns c0DemoHintsX64 2048 c0DemoCompiledX64_check

theorem c0Demo_step_supportsX64 :
    (c0StepTf.toFn.earlyOpt).body.supportsSource x64LegalTarget = true := by
  t_kernel_rfl

theorem c0Demo_step_unified_eq_compileFn_x64 :
    (unified c0FnFrontend x64LegalTarget (regaBackend x64Target c0DemoHintFnX64)).run
        c0StepTf.toFn =
      compileFn x64Target.toIsa x64LegalTarget
        (c0DemoHintFnX64 (c0StepTf.toFn.mid x64LegalTarget)) c0StepTf.toFn :=
  unified_rega_eq_compileFn c0FnFrontend x64Target x64LegalTarget c0DemoHintFnX64
    c0StepTf.toFn c0StepTf.toFn rfl c0Demo_step_supportsX64

theorem c0Demo_mapM_eq_compileModule_x64 :
    ∃ perFn,
      (unified c0FnFrontend x64LegalTarget (regaBackend x64Target c0DemoHintFnX64)).mapM
          c0DemoMod.fns = .ok perFn ∧
        perFn.flatten = c0DemoCompiledX64.code := by
  refine c0Fn_unified_rega_mapM_eq_compileModule_code x64Target x64LegalTarget [] [] 0
    c0DemoMod.fns c0DemoHintsX64 c0DemoHintFnX64 ?_ c0DemoCompiledX64.compileModule_eq
  intro i hi hj
  rcases i with _ | i
  · rfl
  · rcases i with _ | i
    · rfl
    · dsimp only [c0DemoHintsX64, List.length] at hj
      omega

theorem c0Demo_pair_fnSpec_x64 :
    x64Target.Defined c0DemoCompiledX64.host "c0_pair" ∧
    x64Target.FnSpec c0DemoCompiledX64.host "c0_pair"
      (Env.ofTable c0DemoTable "c0_pair" [i64] [i64])
      (c0DemoCompiledX64.bound "c0_pair") 0 := by
  have hmem : c0PairTf.toFn ∈ c0DemoMod.fns := List.mem_cons_of_mem _ List.mem_cons_self
  have hnoex : ∀ e ∈ c0DemoTable, e.noExit = true := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he'
    · rfl
    · rcases List.mem_cons.mp he' with rfl | hnil
      · rfl
      · nomatch hnil
  exact rega_compiled_ofTable_fnSpec_noExit c0DemoMod_acyclic c0DemoMod_allWf
    c0DemoMod_tableImpl hnoex c0DemoCompiledX64 hmem rfl rfl

theorem c0Demo_pair_runs_23_x64 :
    Eventually (x64Target.mach.step c0DemoCompiledX64.host)
      (fun st =>
        x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = 23#64)
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64]) (c0DemoCompiledX64.bound "c0_pair") [] (7#64, ()))
        (x64Target.mach.labelAddr c0DemoCompiledX64.host "c0_pair")) := by
  have hmem : c0PairTf.toFn ∈ c0DemoMod.fns := List.mem_cons_of_mem _ List.mem_cons_self
  have hmem0 : ([] : List UInt8).length ≤ 8192 := by decide
  have hargs : (x64Target.toIsa.assignArgs [i64]).isSome = true := by rfl
  let Q : Post [i64] := fun rets _ => rets = (23#64, ())
  let X : XPost := fun _ _ _ _ => False
  have hspec : Env.ofTable c0DemoTable "c0_pair" [i64] [i64] (7#64, ()) (List.At [] 0x1000#64) Q
      (fun g cs xs m' =>
        X g (x64LegalTarget.legalSig cs) (encodeTup x64LegalTarget cs xs) m') := by
    have hne : ("c0_step" : Sym) ≠ "c0_pair" := by decide
    exact (Env.ofTable_cons_ne hne _ _ _ _).mpr
      ((Env.ofTable_cons_self _ _ _ _ _ _).mpr (fun _ => rfl))
  refine rega_compiled_ofTable_run_fnSpec x64Init c0DemoMod_acyclic c0DemoMod_allWf
    c0DemoMod_tableImpl c0DemoCompiledX64 hmem rfl rfl [] (7#64, ()) hmem0 hargs hspec ?_
    (by omega)
  rintro st (⟨hpc, rets, m', hQ, hrets, _⟩ | ⟨_, _, _, _, hX, _⟩)
  · have hr : rets = (23#64, ()) := hQ
    subst hr
    exact ⟨hpc, x64Init.retsIn_singleton 23#64 _ hrets⟩
  · exact hX.elim

/-! ## 4. Bootstrap0 `leanqbe0Tfs` Structural Hash Pin -/

meta def fnv1aBytes (ba : ByteArray) : UInt64 :=
  ba.data.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211) 14695981039346656037

meta def leanqbe0TfsDigest : Except String (Nat × Nat × UInt64) := do
  let (m0, _) ← ofTFlatModule leanqbe0Tfs
  let enc := Codec0.encodeFnList0 ByteArray.empty m0.fns
  let sigHash := leanqbe0Tfs.foldl
    (fun h tf => mixHash h (hash (tf.name, reprStr tf.as, reprStr tf.rs))) 17
  pure (leanqbe0Tfs.length, enc.size, mixHash sigHash (fnv1aBytes enc))

#guard leanqbe0TfsDigest.toOption == some (124, 185530, 4007694559135456227)

#print axioms c0DemoMod_pair_sat
#print axioms c0Demo_step_unified_eq_compileFn_x64
#print axioms c0Demo_mapM_eq_compileModule_x64
#print axioms c0Demo_pair_fnSpec_x64
#print axioms c0Demo_pair_runs_23_x64

end LeanQbeTest.T.UnifiedC0Test
