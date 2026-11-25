module

public import LeanQbe.T.Unified.Frontend.Bedrock2
public import LeanQbe.T.Arm64.Targ
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Logic.MemLemmas
public import LeanQbeTest.T.UnifiedBedrock2Test
public meta import Lean
import all Kraken.Separation

/-!
# End-to-End AArch64 Verification of `Unified.Frontend.Bedrock2` (`UnifiedBedrock2Arm64Test`)

Compiles verified `Kraken.Bedrock2` kernels (`Examples.swap 64`, `Examples.set_bytes`,
`Examples.bitcopy_store` with `stackalloc`, multi-function `[divmod, useDivmod]`, and `mulh`)
through `bedrock2Module` / `bedrock2Frontend` / `bedrock2TargetBackend` onto `armTarget`
(`armInit`), deriving closed `std3` machine-code `Eventually` and `FnSpec` theorems with zero
X64 imports.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.UnifiedBedrock2Arm64Test

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Unified LeanQbe.T.Bedrock2
open Kraken Kraken.Bedrock2 Kraken.Bedrock2.Test
open LeanQbeTest.T.UnifiedBedrock2Test

/-! ## 1. Arch-Isolation Audit (`0` X64 / Amd64 Imports) -/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.allImportedModuleNames
  for m in mods do
    if (`Kraken.X64).isPrefixOf m || (`LeanQbe.T.Amd64).isPrefixOf m then
      throwError s!"unexpected X64 import `{m}` in UnifiedBedrock2Arm64Test"
  IO.println s!"Arm64 Bedrock2 test closure ok ({mods.size} imported modules, 0 X64 leaks)"

/-! ## 2. Kernel-Checkable Literal `Hints` & Compiled Modules on `armTarget` -/

@[expose] def armSwapHints : armTarget.toIsa.Hints where
  dest :=
    .node none (.node none (.node (some (.gpr (.reg .X3))) .empty .empty) .empty)
      (.node (some (.gpr (.reg .X2))) .empty .empty)

@[expose] def armSetBytesHints : armTarget.toIsa.Hints where
  dest :=
    .node none
      (.node none
        (.node (some (.flag ArmCond.ne)) (.node (some (.flag ArmCond.ne)) .empty .empty)
          (.node (some (.gpr (.reg .X2))) .empty .empty))
        (.node (some (.gpr (.reg .X0))) .empty (.node (some (.gpr (.reg .X1))) .empty .empty)))
      (.node none
        (.node (some (.gpr (.reg .X2))) .empty (.node (some (.gpr (.reg .X0))) .empty .empty))
        (.node (some (.gpr (.reg .X1))) .empty (.node (some (.flag ArmCond.ne)) .empty .empty)))
  entry :=
    .node (some {}) .empty
      (.node (some { ploc := [.gpr (.reg .X0), .gpr (.reg .X1), .gpr (.reg .X3)] })
        .empty .empty)
  pre :=
    .node (some { moves := [Move.mov (.reg .X3) (.reg .X2)] }) .empty .empty
  invertJnz :=
    .node none (.node (some true) .empty .empty)
      (.node none (.node none (.node none (.node (some true) .empty .empty) .empty) .empty)
        .empty)
  deferJnz :=
    .node (some true)
      (.node none
        (.node none (.node (some true) (.node (some true) .empty .empty) .empty) .empty) .empty)
      .empty

@[expose] def armMulhHints : armTarget.toIsa.Hints where
  dest :=
    .node none (.node none (.node (some (.gpr (.reg .X2))) .empty .empty) .empty)
      (.node (some (.gpr (.reg .X3))) (.node (some (.gpr (.reg .X1))) .empty .empty) .empty)

@[expose] def armDivmodHints : armTarget.toIsa.Hints where
  dest :=
    .node none
      (.node none (.node (some (.gpr (.reg .X0))) .empty .empty)
        (.node (some (.flag ArmCond.eq)) .empty .empty))
      (.node (some (.flag ArmCond.eq)) .empty (.node (some (.gpr (.reg .X1))) .empty .empty))
  entry :=
    .node
      (some { live := [(SymArg.var 0, .gpr (.reg .X2)), (SymArg.var 1, .gpr (.reg .X1))],
              ploc := [.gpr (.reg .X0)] })
      .empty
      (.node (some { live := [(SymArg.var 4, .gpr (.reg .X0))], ploc := [.gpr (.reg .X1)] })
        .empty .empty)
  pre :=
    .node (some { moves := [Move.mov (.reg .X2) (.reg .X0)] }) .empty .empty
  deferJnz :=
    .node (some true) (.node none .empty (.node (some true) .empty .empty)) .empty

@[expose] def armUseDivmodHints : armTarget.toIsa.Hints where
  dest :=
    .node none (.node none .empty (.node (some (.gpr (.reg .X0))) .empty .empty))
      (.node none (.node (some (.gpr (.reg .X0))) .empty .empty) .empty)

@[expose] def armBitcopyHints : armTarget.toIsa.Hints where
  dest :=
    .node none
      (.node none
        (.node (some (.gpr (.reg .X2))) .empty (.node (some (.gpr (.reg .X2))) .empty .empty))
        (.node none (.node (some (.flag ArmCond.ne)) .empty .empty)
          (.node (some (.flag ArmCond.ne)) .empty .empty)))
      (.node (some (.flag ArmCond.ne))
        (.node (some (.flag ArmCond.ne))
          (.node none (.node (some (.gpr (.reg .X0))) .empty .empty) .empty)
          (.node (some (.gpr (.reg .X1))) .empty .empty))
        (.node none (.node (some (.gpr (.reg .X3))) .empty .empty) .empty))
  entry :=
    .node
      (some { live := [(SymArg.var 0, .gpr (.reg .X4))],
              ploc := [.gpr (.reg .X0), .gpr (.reg .X2)] })
      (.node
        (some { live := [(SymArg.var 0, .gpr (.reg .X4))],
                ploc := [.gpr (.reg .X0), .gpr (.reg .X2), .gpr (.reg .X1)] })
        .empty .empty)
      .empty
  pre :=
    .node none (.node (some { moves := [Move.mov (.reg .X4) (.reg .X0)] }) .empty .empty)
      (.node none
        (.node none .empty
          (.node none (.node (some { moves := [Move.st 0 (.reg .X0)] }) .empty .empty) .empty))
        .empty)
  elide :=
    .node none (.node none .empty (.node none (.node (some true) .empty .empty) .empty))
      (.node (some true) .empty .empty)
  invertJnz :=
    .node none
      (.node none (.node none (.node none (.node (some true) .empty .empty) .empty) .empty)
        .empty)
      .empty
  deferJnz :=
    .node none (.node none .empty (.node (some true) .empty .empty))
      (.node none .empty (.node none .empty (.node (some true) .empty .empty)))
  nslots := 1

@[expose] def armHints (fn : Fn) : armTarget.toIsa.Hints :=
  if fn.name == "swap" then armSwapHints
  else if fn.name == "set_bytes" then armSetBytesHints
  else if fn.name == "mulh" then armMulhHints
  else if fn.name == "divmod" then armDivmodHints
  else if fn.name == "use_divmod" then armUseDivmodHints
  else if fn.name == "bitcopy_store" then armBitcopyHints
  else {}

@[expose] def armSwapMod : Module := modOf swapFs
@[expose] def armSetBytesMod : Module := modOf setBytesFs
@[expose] def armMulhMod : Module := modOf mulhFs
@[expose] def armDivmodMod : Module := modOf divmodFs
@[expose] def armBitcopyMod : Module := modOf bitcopyFs bedrock2StackExterns

private theorem armSwapMod_ok : bedrock2Module swapFs [] [] = .ok armSwapMod := by
  exact except_of_isOk emptyModuleFallback (by decide)

private theorem armSetBytesMod_ok : bedrock2Module setBytesFs [] [] = .ok armSetBytesMod := by
  exact except_of_isOk emptyModuleFallback (by decide)

private theorem armMulhMod_ok : bedrock2Module mulhFs [] [] = .ok armMulhMod := by
  exact except_of_isOk emptyModuleFallback (by decide)

private theorem armDivmodMod_ok : bedrock2Module divmodFs [] [] = .ok armDivmodMod := by
  exact except_of_isOk emptyModuleFallback (by decide)

private theorem armBitcopyMod_ok :
    bedrock2Module bitcopyFs bedrock2StackExterns [] = .ok armBitcopyMod := by
  exact except_of_isOk emptyModuleFallback (by decide)

@[expose] def armSwapCompiled :
    Compiled armTarget armLegalTarget [] [] 0 armSwapMod.fns [armSwapHints] 2048 :=
  compileChecked armTarget armLayout armLegalTarget armLabelClean [] [] 0
    armSwapMod.fns [armSwapHints] 2048 (by t_kernel_rfl)

@[expose] def armSetBytesCompiled :
    Compiled armTarget armLegalTarget [] [] 0 armSetBytesMod.fns [armSetBytesHints] 2048 :=
  compileChecked armTarget armLayout armLegalTarget armLabelClean [] [] 0
    armSetBytesMod.fns [armSetBytesHints] 2048 (by t_kernel_rfl)

@[expose] def armMulhCompiled :
    Compiled armTarget armLegalTarget [] [] 0 armMulhMod.fns [armMulhHints] 2048 :=
  compileChecked armTarget armLayout armLegalTarget armLabelClean [] [] 0
    armMulhMod.fns [armMulhHints] 2048 (by t_kernel_rfl)

@[expose] def armDivmodCompiled :
    Compiled armTarget armLegalTarget [] [] 0
      armDivmodMod.fns [armDivmodHints, armUseDivmodHints] 2048 :=
  compileChecked armTarget armLayout armLegalTarget armLabelClean [] [] 0
    armDivmodMod.fns [armDivmodHints, armUseDivmodHints] 2048 (by t_kernel_rfl)

@[expose] def armBitcopyCompiled :
    Compiled armTarget armLegalTarget bitcopyExtCallees [] 0
      armBitcopyMod.fns [armBitcopyHints] 2048 :=
  compileChecked armTarget armLayout armLegalTarget armLabelClean bitcopyExtCallees [] 0
    armBitcopyMod.fns [armBitcopyHints] 2048 (by t_kernel_rfl)

private theorem arm_64_mem : 64 ∈ armLegalTarget.bitWidths := by
  decide

/-! ## 3. Closed Machine-Code Theorems: `swap`, `set_bytes`, `mulh`, `use_divmod` -/

theorem arm_swap_runs (bsa bsb : List UInt8)
    (hla : bsa.length = 8) (hlb : bsb.length = 8) :
    Eventually (armTarget.mach.step armSwapCompiled.host)
      (fun st => armTarget.mach.pc st = armInit.ra0 ∧
        (armTarget.mach.mem (armTarget.mach.data st) =⋆
          (Eq (bsb.At 0x1000#64) ⋆ Eq (bsa.At 0x1008#64) ⋆ emp) ⋆
          armTarget.Exit armInit.sp0 (armSwapCompiled.bound "swap") ⋆ emp))
      (armTarget.mach.mkState
        (armInit.initState (as := [i64, i64]) (armSwapCompiled.bound "swap")
          (bsa ++ bsb) (0x1000#64, 0x1008#64, ()))
        (armTarget.mach.labelAddr armSwapCompiled.host "swap")) := by
  have hbs : (bsa ++ bsb).length ≤ 8192 := by
    simp only [List.length_append, hla, hlb]; decide
  have hm0 : (Eq (bsa.At 0x1000#64) ⋆ Eq (bsb.At 0x1008#64) ⋆ emp)
      ((bsa ++ bsb).At 0x1000#64) := by
    have happ := Mem.At_append_sep bsa bsb 0x1000#64 (by simp [hla, hlb])
    have haddr : (0x1000#64 + BitVec.ofNat 64 bsa.length) = 0x1008#64 := by
      rw [hla]; decide
    rw [haddr] at happ
    rw [sep_emp, ← happ]
  have hcall := @Examples.swap_ok 64 (Or.inr rfl) bedrock2ExtEmpty swapFs 0 rfl []
    ((bsa ++ bsb).At 0x1000#64) 0x1000#64 0x1008#64 bsa bsb emp hla hlb hm0
  refine bedrock2Module_compiled_run_call armInit armSwapMod_ok armSwapCompiled
    bedrock2ExtEmpty (by decide) (bedrock2NamesValid_empty (by decide))
    (fun _ h => nomatch h) (And.intro (fun _ h => nomatch h) (fun _ h => nomatch h))
    (p := Examples.swap 64) List.mem_cons_self arm_64_mem
    (bsa ++ bsb) (0x1000#64, 0x1008#64, ()) hbs (by decide) (B := 0) (by decide) []
    (Q := fun _ m' => (Eq (bsb.At 0x1000#64) ⋆ Eq (bsa.At 0x1008#64) ⋆ emp) m') ?_ ?_ (by decide)
  · exact hcall.weaken fun _ _ _ ⟨_, _, hm'⟩ _ _ => hm'
  · rintro st ⟨hpc, _, m', hm', _, hmem⟩
    exact ⟨hpc, sep_mono (fun _ => sep_mono (fun _ e => e ▸ hm')) hmem⟩

theorem arm_set_bytes_runs (bs : List UInt8) (v : BitVec 64) (hl : bs.length = 16) :
    Eventually (armTarget.mach.step armSetBytesCompiled.host)
      (fun st => armTarget.mach.pc st = armInit.ra0 ∧
        (armTarget.mach.mem (armTarget.mach.data st) =⋆
          (Eq ((List.replicate 16 v.toNat.toUInt8).At 0x1000#64) ⋆ emp) ⋆
          armTarget.Exit armInit.sp0 (armSetBytesCompiled.bound "set_bytes") ⋆ emp))
      (armTarget.mach.mkState
        (armInit.initState (as := [i64, i64, i64]) (armSetBytesCompiled.bound "set_bytes")
          bs (0x1000#64, 16#64, v, ()))
        (armTarget.mach.labelAddr armSetBytesCompiled.host "set_bytes")) := by
  have hbs : bs.length ≤ 8192 := by rw [hl]; decide
  have hm0 : (Eq (bs.At 0x1000#64) ⋆ emp) (bs.At 0x1000#64) := by
    rw [sep_emp]
  have hcall := @Examples.set_bytes_ok 64 bedrock2ExtEmpty setBytesFs 0 rfl []
    (bs.At 0x1000#64) 0x1000#64 16#64 v bs emp (by simp [hl]) hm0
  refine bedrock2Module_compiled_run_call armInit armSetBytesMod_ok armSetBytesCompiled
    bedrock2ExtEmpty (by decide) (bedrock2NamesValid_empty (by decide))
    (fun _ h => nomatch h) (And.intro (fun _ h => nomatch h) (fun _ h => nomatch h))
    (p := Examples.set_bytes) List.mem_cons_self arm_64_mem
    bs (0x1000#64, 16#64, v, ()) hbs (by decide) (B := 0) (by decide) []
    (Q := fun _ m' => (Eq ((List.replicate 16 v.toNat.toUInt8).At 0x1000#64) ⋆ emp) m')
    ?_ ?_ (by decide)
  · exact hcall.weaken fun _ _ _ ⟨_, _, hm'⟩ _ _ => by simpa using hm'
  · rintro st ⟨hpc, _, m', hm', _, hmem⟩
    exact ⟨hpc, sep_mono (fun _ => sep_mono (fun _ e => e ▸ hm')) hmem⟩

theorem arm_mulh_runs (x y : BitVec 64) :
    Eventually (armTarget.mach.step armMulhCompiled.host)
      (fun st => armTarget.mach.pc st = armInit.ra0 ∧
        armTarget.RetsIn (bs := [i64, i64]) (interpBinop .mulhuu x y, x * y, ())
          (armTarget.mach.data st))
      (armTarget.mach.mkState
        (armInit.initState (as := [i64, i64]) (armMulhCompiled.bound "mulh") [] (x, y, ()))
        (armTarget.mach.labelAddr armMulhCompiled.host "mulh")) := by
  refine bedrock2Module_compiled_run_exec armInit armMulhMod_ok armMulhCompiled
    bedrock2ExtEmpty (by decide) (bedrock2NamesValid_empty (by decide))
    (fun _ h => nomatch h) (And.intro (fun _ h => nomatch h) (fun _ h => nomatch h))
    (p := mulh) List.mem_cons_self arm_64_mem [] (x, y, ()) (by decide) (by decide)
    (B := 0) (by decide) []
    (Q := fun r m' => r = (interpBinop .mulhuu x y, x * y, ()) ∧
      m' = ([] : List UInt8).At 0x1000#64)
    (mulh_exec x y _) ?_ (by decide)
  rintro st ⟨hpc, rets, m', ⟨rfl, _⟩, hrets, _⟩
  exact ⟨hpc, hrets⟩

theorem arm_useDivmod_runs (x y : BitVec 64) (hy : y ≠ 0#64) :
    Eventually (armTarget.mach.step armDivmodCompiled.host)
      (fun st => armTarget.mach.pc st = armInit.ra0 ∧
        armTarget.RetsIn (bs := [i64, i64]) ((x / y) * 0x3e8#64 + (x % y), x % y, ())
          (armTarget.mach.data st))
      (armTarget.mach.mkState
        (armInit.initState (as := [i64, i64]) (armDivmodCompiled.bound "use_divmod") []
          (x, y, ()))
        (armTarget.mach.labelAddr armDivmodCompiled.host "use_divmod")) := by
  refine bedrock2Module_compiled_run_exec armInit armDivmodMod_ok armDivmodCompiled
    bedrock2ExtEmpty (by decide) (bedrock2NamesValid_empty (by decide))
    (fun _ h => nomatch h) (And.intro (fun _ h => nomatch h) (fun _ h => nomatch h))
    (p := useDivmod) (List.mem_cons_of_mem _ List.mem_cons_self) arm_64_mem
    [] (x, y, ()) (by decide) (by decide) (B := 0) (by decide) []
    (Q := fun r m' => r = ((x / y) * 0x3e8#64 + (x % y), x % y, ()) ∧
      m' = ([] : List UInt8).At 0x1000#64)
    (useDivmod_exec x y hy _) ?_ (by decide)
  rintro st ⟨hpc, rets, m', ⟨rfl, _⟩, hrets, _⟩
  exact ⟨hpc, hrets⟩

/-! ## 4. `stackalloc` + End-to-End `unified` Backend Bridge (`bitcopy_store` & `swap`) -/

theorem arm_bitcopy_runs
    (hext : ∀ q ∈ bitcopyExtCallees,
      armTarget.FnSpec armBitcopyCompiled.host q.1.1
        (legalEnv armLegalTarget
          (Env.ofModule armBitcopyMod (bedrock2Env .default bedrock2ExtEmpty bitcopyFs))
          q.1.1 q.1.2.1 q.1.2.2)
        q.2 0) :
    Eventually (armTarget.mach.step armBitcopyCompiled.host)
      (fun st => armTarget.mach.pc st = armInit.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) armInit.ret0 = 15#64)
      (armTarget.mach.mkState
        (armInit.initState (as := ([] : List Ty))
          (armBitcopyCompiled.bound "bitcopy_store") [] ())
        (armTarget.mach.labelAddr armBitcopyCompiled.host "bitcopy_store")) := by
  have hcall := bitcopy_store_ok_std3 (ext := bedrock2ExtEmpty) (e := bitcopyFs) rfl []
    (([] : List UInt8).At 0x1000#64)
  refine bedrock2Module_compiled_run_call armInit armBitcopyMod_ok armBitcopyCompiled
    bedrock2ExtEmpty (by decide) (bedrock2NamesValid_empty (by decide)) hext
    (And.intro (by decide) (by decide)) (p := Examples.bitcopy_store) List.mem_cons_self
    arm_64_mem [] () (by decide) (by decide) (B := 8) (by decide) []
    (Q := fun r m' => r = (15#64, ()) ∧ m' = ([] : List UInt8).At 0x1000#64) ?_ ?_ (by decide)
  · exact hcall.weaken fun _ _ _ ⟨_, hm', hrets⟩ ⟨r, ⟨⟩⟩ hEq => by
      rw [hrets] at hEq
      change [r] = [15#64] at hEq
      cases hEq
      exact ⟨rfl, hm'⟩
  · rintro st ⟨hpc, _, m', ⟨rfl, _⟩, hrets, _⟩
    exact ⟨hpc, armInit.retsIn_singleton 15#64 _ hrets⟩

@[expose] def armSwapUnifiedDs : List armTarget.Directive :=
  ((unified bedrock2Frontend armLegalTarget
      (bedrock2TargetBackend armTarget armHints)).run (Examples.swap 64)).toOption.getD []

@[expose] def armBitcopyUnifiedDs : List armTarget.Directive :=
  ((unified bedrock2Frontend armLegalTarget
      (bedrock2TargetBackend armTarget armHints)).run Examples.bitcopy_store).toOption.getD []

theorem arm_unified_swap_run :
    (unified bedrock2Frontend armLegalTarget
      (bedrock2TargetBackend armTarget armHints)).run (Examples.swap 64) =
      .ok armSwapUnifiedDs := by
  have hx :
      ((unified bedrock2Frontend armLegalTarget
        (bedrock2TargetBackend armTarget armHints)).run (Examples.swap 64)).isOk = true := by
    t_kernel_rfl
  exact except_isOk_getD _ [] hx

theorem arm_unified_bitcopy_run :
    (unified bedrock2Frontend armLegalTarget
      (bedrock2TargetBackend armTarget armHints)).run Examples.bitcopy_store =
      .ok armBitcopyUnifiedDs := by
  have hx :
      ((unified bedrock2Frontend armLegalTarget
        (bedrock2TargetBackend armTarget armHints)).run Examples.bitcopy_store).isOk = true := by
    t_kernel_rfl
  exact except_isOk_getD _ [] hx

theorem arm_unified_swap_msat :
    bedrock2TargetMSat armTarget armHints armSwapUnifiedDs
      ((unified bedrock2Frontend armLegalTarget (bedrock2TargetBackend armTarget armHints)).tr
        (Examples.swap 64) swapB2Spec) :=
  bedrock2_unified_sound .default armLegalTarget
    ⟨bedrock2TargetBackend armTarget armHints,
      bedrock2TargetBackend armTarget armHints,
      bedrock2TargetBackend armTarget armHints⟩
    (Examples.swap 64) swapB2Spec armSwapUnifiedDs arm_unified_swap_run swap_sat_b2Spec

theorem arm_unified_bitcopy_msat :
    bedrock2TargetMSat armTarget armHints armBitcopyUnifiedDs
      ((unified bedrock2Frontend armLegalTarget (bedrock2TargetBackend armTarget armHints)).tr
        Examples.bitcopy_store bitcopyB2Spec) :=
  bedrock2_unified_sound .default armLegalTarget
    ⟨bedrock2TargetBackend armTarget armHints,
      bedrock2TargetBackend armTarget armHints,
      bedrock2TargetBackend armTarget armHints⟩
    Examples.bitcopy_store bitcopyB2Spec armBitcopyUnifiedDs
    arm_unified_bitcopy_run bitcopy_sat_b2Spec

theorem arm_unified_swap_fnSpec (h : armTarget.mach.Host) (k₀ : Nat)
    (hinf : armSwapUnifiedDs.IsInfixAt (armTarget.mach.prog h) k₀)
    (hu : armTarget.LabelsUnique h) :
    armTarget.Defined h "swap" ∧
    armTarget.FnSpec h "swap" (swapB2Spec.toSpec "swap" 2 0) 2048 0 := by
  refine bedrock2_unified_fnSpec .default armTarget armLegalTarget armHints (Examples.swap 64)
    swapB2Spec armSwapUnifiedDs arm_unified_swap_run swap_sat_b2Spec arm_64_mem
    h k₀ 2048 0 (fun _ => 0) hinf hu ?_ (by decide)
  intro fn hlow
  have hfn : fn = b2LowerDefault (Examples.swap 64) := by
    change b2NamedFuncToFn? .default (Examples.swap 64) = .ok fn at hlow
    dsimp only [b2LowerDefault]; rw [hlow]
  subst hfn
  refine ⟨of_decide_eq_true (by t_kernel_rfl), ?_, ?_⟩
  · intro g as bs hg
    have hc : ((b2LowerDefault (Examples.swap 64)).mid armLegalTarget).ext.callees = [] := by
      t_kernel_rfl
    rw [hc] at hg; cases hg
  · intro g hg
    have he : ((b2LowerDefault (Examples.swap 64)).mid armLegalTarget).ext.exits = [] := by
      t_kernel_rfl
    rw [he] at hg; cases hg

theorem arm_unified_bitcopy_fnSpec (h : armTarget.mach.Host) (k₀ : Nat)
    (hinf : armBitcopyUnifiedDs.IsInfixAt (armTarget.mach.prog h) k₀)
    (hu : armTarget.LabelsUnique h)
    (halloc : armTarget.FnSpec h "__b2_stackalloc"
      (legalEnv armLegalTarget (bedrock2Env .default bedrock2ExtEmpty [Examples.bitcopy_store])
        "__b2_stackalloc" [i64] [i64]) 0 0)
    (hfree : armTarget.FnSpec h "__b2_stackfree"
      (legalEnv armLegalTarget (bedrock2Env .default bedrock2ExtEmpty [Examples.bitcopy_store])
        "__b2_stackfree" [i64, i64] []) 0 0) :
    armTarget.Defined h "bitcopy_store" ∧
    armTarget.FnSpec h "bitcopy_store" (bitcopyB2Spec.toSpec "bitcopy_store" 0 1) 2048 0 := by
  refine bedrock2_unified_fnSpec .default armTarget armLegalTarget armHints Examples.bitcopy_store
    bitcopyB2Spec armBitcopyUnifiedDs arm_unified_bitcopy_run bitcopy_sat_b2Spec arm_64_mem
    h k₀ 2048 0 (fun _ => 0) hinf hu ?_ (by decide)
  intro fn hlow
  have hfn : fn = b2LowerDefault Examples.bitcopy_store := by
    change b2NamedFuncToFn? .default Examples.bitcopy_store = .ok fn at hlow
    dsimp only [b2LowerDefault]; rw [hlow]
  subst hfn
  refine ⟨of_decide_eq_true (by t_kernel_rfl), ?_, ?_⟩
  · intro g as bs hg
    have hc : ((b2LowerDefault Examples.bitcopy_store).mid armLegalTarget).ext.callees =
        [("__b2_stackalloc", [i64], [i64]), ("__b2_stackfree", [i64, i64], [])] := by
      t_kernel_rfl
    rw [hc] at hg
    rcases List.mem_cons.mp hg with h1 | h2
    · cases h1
      exact ⟨halloc, of_decide_eq_true (by t_kernel_rfl)⟩
    · rcases List.mem_cons.mp h2 with h2' | h3
      · cases h2'
        exact ⟨hfree, of_decide_eq_true (by t_kernel_rfl)⟩
      · cases h3
  · intro g hg
    have he : ((b2LowerDefault Examples.bitcopy_store).mid armLegalTarget).ext.exits = [] := by
      t_kernel_rfl
    rw [he] at hg; cases hg

end LeanQbeTest.T.UnifiedBedrock2Arm64Test

#print axioms LeanQbeTest.T.UnifiedBedrock2Arm64Test.arm_swap_runs
#print axioms LeanQbeTest.T.UnifiedBedrock2Arm64Test.arm_set_bytes_runs
#print axioms LeanQbeTest.T.UnifiedBedrock2Arm64Test.arm_mulh_runs
#print axioms LeanQbeTest.T.UnifiedBedrock2Arm64Test.arm_useDivmod_runs
#print axioms LeanQbeTest.T.UnifiedBedrock2Arm64Test.arm_bitcopy_runs
#print axioms LeanQbeTest.T.UnifiedBedrock2Arm64Test.arm_unified_swap_msat
#print axioms LeanQbeTest.T.UnifiedBedrock2Arm64Test.arm_unified_bitcopy_msat
#print axioms LeanQbeTest.T.UnifiedBedrock2Arm64Test.arm_unified_swap_fnSpec
#print axioms LeanQbeTest.T.UnifiedBedrock2Arm64Test.arm_unified_bitcopy_fnSpec
