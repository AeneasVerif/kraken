module

public import LeanQbe.T.Unified.Frontend.Bedrock2
public import LeanQbe.T.Amd64.Targ
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Logic.MemLemmas
public import LeanQbeTest.T.UnifiedBedrock2Test
public meta import Lean
import all Kraken.Separation

/-!
# End-to-End x86-64 Verification of `Unified.Frontend.Bedrock2` (`UnifiedBedrock2X64Test`)

Compiles verified `Kraken.Bedrock2` kernels (`Examples.swap 64`, `Examples.set_bytes`,
`Examples.bitcopy_store` with `stackalloc`, multi-function `[divmod, useDivmod]`, and `mulh`)
through `bedrock2Module` / `bedrock2Frontend` / `bedrock2TargetBackend` onto `x64Target`
(`x64Init`), deriving closed `std3` machine-code `Eventually` and `FnSpec` theorems with zero
Arm64 imports.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.UnifiedBedrock2X64Test

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Unified LeanQbe.T.Bedrock2
open Kraken Kraken.Bedrock2 Kraken.Bedrock2.Test
open LeanQbeTest.T.UnifiedBedrock2Test

/-! ## 1. Arch-Isolation Audit (`0` AArch64 / Arm64 Imports) -/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.allImportedModuleNames
  for m in mods do
    if (`Kraken.AArch64).isPrefixOf m || (`LeanQbe.T.Arm64).isPrefixOf m then
      throwError s!"unexpected Arm64 import `{m}` in UnifiedBedrock2X64Test"
  IO.println s!"x64 Bedrock2 test closure ok ({mods.size} imported modules, 0 Arm64 leaks)"

/-! ## 2. Kernel-Checkable Literal `Hints` & Compiled Modules on `x64Target` -/

@[expose] def x64SwapHints : x64Target.toIsa.Hints where
  dest :=
    .node none (.node none (.node (some (.gpr Reg64.rcx)) .empty .empty) .empty)
      (.node (some (.gpr Reg64.rax)) .empty .empty)

@[expose] def x64SetBytesHints : x64Target.toIsa.Hints where
  dest :=
    .node none
      (.node none
        (.node (some (.flag CondCode.nz)) (.node (some (.flag CondCode.nz)) .empty .empty)
          (.node (some (.gpr Reg64.rdx)) .empty .empty))
        (.node (some (.gpr Reg64.rdi)) .empty (.node (some (.gpr Reg64.rax)) .empty .empty)))
      (.node none
        (.node (some (.gpr Reg64.rdx)) .empty (.node (some (.gpr Reg64.rdi)) .empty .empty))
        (.node (some (.gpr Reg64.rax)) .empty (.node (some (.flag CondCode.nz)) .empty .empty)))
  entry :=
    .node (some {}) .empty
      (.node (some { ploc := [.gpr Reg64.rdi, .gpr Reg64.rax, .gpr Reg64.rcx] }) .empty .empty)
  pre :=
    .node (some { moves := [Move.mov Reg64.rcx Reg64.rdx, Move.mov Reg64.rax Reg64.rsi] })
      .empty .empty
  invertJnz :=
    .node none (.node (some true) .empty .empty)
      (.node none (.node none (.node none (.node (some true) .empty .empty) .empty) .empty)
        .empty)
  deferJnz :=
    .node (some true)
      (.node none
        (.node none (.node (some true) (.node (some true) .empty .empty) .empty) .empty) .empty)
      .empty

@[expose] def x64MulhHints : x64Target.toIsa.Hints where
  dest :=
    .node none (.node none (.node (some (.gpr Reg64.rax)) .empty .empty) .empty)
      (.node (some (.gpr Reg64.rcx)) (.node (some (.gpr Reg64.rdi)) .empty .empty) .empty)

@[expose] def x64DivmodHints : x64Target.toIsa.Hints where
  dest :=
    .node none
      (.node none (.node (some (.gpr Reg64.rax)) .empty .empty)
        (.node (some (.flag CondCode.z)) .empty .empty))
      (.node (some (.flag CondCode.z)) .empty (.node (some (.gpr Reg64.rdx)) .empty .empty))
  entry :=
    .node (some { live := [], ploc := [.gpr Reg64.rax, .gpr Reg64.rdx] })
      (.node
        (some { live := [(SymArg.var 0, .gpr Reg64.rdi), (SymArg.var 1, .gpr Reg64.rsi)],
                ploc := [.gpr Reg64.rax] })
        .empty .empty)
      .empty
  deferJnz :=
    .node (some true) (.node none .empty (.node (some true) .empty .empty)) .empty

@[expose] def x64UseDivmodHints : x64Target.toIsa.Hints where
  dest :=
    .node none (.node none .empty (.node (some (.gpr Reg64.rax)) .empty .empty))
      (.node none (.node (some (.gpr Reg64.rax)) .empty .empty) .empty)

@[expose] def x64BitcopyHints : x64Target.toIsa.Hints where
  dest :=
    .node none
      (.node none
        (.node (some (.gpr Reg64.rdx))
          (.node none (.node (some (.gpr Reg64.rax)) .empty .empty) .empty)
          (.node (some (.gpr Reg64.rcx)) .empty .empty))
        (.node none (.node (some (.gpr Reg64.r8)) .empty .empty) .empty))
      (.node (some (.flag CondCode.nz))
        (.node none (.node (some (.gpr Reg64.rsi)) .empty .empty)
          (.node (some (.flag CondCode.nz)) .empty .empty))
        (.node none (.node (some (.gpr Reg64.rdx)) .empty .empty) .empty))
  entry :=
    .node
      (some { live := [(SymArg.var 0, .gpr Reg64.rdi)],
              ploc := [.gpr Reg64.rax, .gpr Reg64.rdx] })
      (.node
        (some { live := [(SymArg.var 0, .gpr Reg64.rdi)],
                ploc := [.gpr Reg64.rax, .gpr Reg64.rdx, .gpr Reg64.rcx] })
        .empty .empty)
      .empty
  pre :=
    .node none
      (.node (some { moves := [Move.mov Reg64.rdi Reg64.rax] }) .empty
        (.node none
          (.node none
            (.node (some { moves := [Move.st 0 Reg64.rax] }) .empty .empty) .empty)
          .empty))
      .empty
  elide :=
    .node none .empty
      (.node (some true) .empty (.node (some true) .empty .empty))
  invertJnz :=
    .node none .empty
      (.node none
        (.node none .empty (.node (some true) .empty .empty))
        .empty)
  deferJnz :=
    .node none
      (.node none
        (.node none .empty (.node (some true) .empty .empty))
        .empty)
      .empty
  nslots := 1

@[expose] def x64Hints (fn : Fn) : x64Target.toIsa.Hints :=
  if fn.name == "swap" then x64SwapHints
  else if fn.name == "set_bytes" then x64SetBytesHints
  else if fn.name == "mulh" then x64MulhHints
  else if fn.name == "divmod" then x64DivmodHints
  else if fn.name == "use_divmod" then x64UseDivmodHints
  else if fn.name == "bitcopy_store" then x64BitcopyHints
  else {}

@[expose] def x64SwapMod : Module := modOf swapFs
@[expose] def x64SetBytesMod : Module := modOf setBytesFs
@[expose] def x64MulhMod : Module := modOf mulhFs
@[expose] def x64DivmodMod : Module := modOf divmodFs
@[expose] def x64BitcopyMod : Module := modOf bitcopyFs bedrock2StackExterns

private theorem x64SwapMod_ok : bedrock2Module swapFs [] [] = .ok x64SwapMod := by
  exact except_of_isOk emptyModuleFallback (by decide)

private theorem x64SetBytesMod_ok : bedrock2Module setBytesFs [] [] = .ok x64SetBytesMod := by
  exact except_of_isOk emptyModuleFallback (by decide)

private theorem x64MulhMod_ok : bedrock2Module mulhFs [] [] = .ok x64MulhMod := by
  exact except_of_isOk emptyModuleFallback (by decide)

private theorem x64DivmodMod_ok : bedrock2Module divmodFs [] [] = .ok x64DivmodMod := by
  exact except_of_isOk emptyModuleFallback (by decide)

private theorem x64BitcopyMod_ok :
    bedrock2Module bitcopyFs bedrock2StackExterns [] = .ok x64BitcopyMod := by
  exact except_of_isOk emptyModuleFallback (by decide)

@[expose] def x64SwapCompiled :
    Compiled x64Target x64LegalTarget [] [] 0 x64SwapMod.fns [x64SwapHints] 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean [] [] 0
    x64SwapMod.fns [x64SwapHints] 2048 (by t_kernel_rfl)

@[expose] def x64SetBytesCompiled :
    Compiled x64Target x64LegalTarget [] [] 0 x64SetBytesMod.fns [x64SetBytesHints] 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean [] [] 0
    x64SetBytesMod.fns [x64SetBytesHints] 2048 (by t_kernel_rfl)

@[expose] def x64MulhCompiled :
    Compiled x64Target x64LegalTarget [] [] 0 x64MulhMod.fns [x64MulhHints] 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean [] [] 0
    x64MulhMod.fns [x64MulhHints] 2048 (by t_kernel_rfl)

@[expose] def x64DivmodCompiled :
    Compiled x64Target x64LegalTarget [] [] 0
      x64DivmodMod.fns [x64DivmodHints, x64UseDivmodHints] 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean [] [] 0
    x64DivmodMod.fns [x64DivmodHints, x64UseDivmodHints] 2048 (by t_kernel_rfl)

@[expose] def x64BitcopyCompiled :
    Compiled x64Target x64LegalTarget bitcopyExtCallees [] 0
      x64BitcopyMod.fns [x64BitcopyHints] 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean bitcopyExtCallees [] 0
    x64BitcopyMod.fns [x64BitcopyHints] 2048 (by t_kernel_rfl)

private theorem x64_64_mem : 64 ∈ x64LegalTarget.bitWidths := by
  decide

/-! ## 3. Closed Machine-Code Theorems: `swap`, `set_bytes`, `mulh`, `use_divmod` -/

theorem x64_swap_runs (bsa bsb : List UInt8)
    (hla : bsa.length = 8) (hlb : bsb.length = 8) :
    Eventually (x64Target.mach.step x64SwapCompiled.host)
      (fun st => x64Target.mach.pc st = x64Init.ra0 ∧
        (x64Target.mach.mem (x64Target.mach.data st) =⋆
          (Eq (bsb.At 0x1000#64) ⋆ Eq (bsa.At 0x1008#64) ⋆ emp) ⋆
          x64Target.Exit x64Init.sp0 (x64SwapCompiled.bound "swap") ⋆ emp))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64]) (x64SwapCompiled.bound "swap")
          (bsa ++ bsb) (0x1000#64, 0x1008#64, ()))
        (x64Target.mach.labelAddr x64SwapCompiled.host "swap")) := by
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
  refine bedrock2Module_compiled_run_call x64Init x64SwapMod_ok x64SwapCompiled
    bedrock2ExtEmpty (by decide) (bedrock2NamesValid_empty (by decide))
    (fun _ h => nomatch h) (And.intro (fun _ h => nomatch h) (fun _ h => nomatch h))
    (p := Examples.swap 64) List.mem_cons_self x64_64_mem
    (bsa ++ bsb) (0x1000#64, 0x1008#64, ()) hbs (by decide) (B := 0) (by decide) []
    (Q := fun _ m' => (Eq (bsb.At 0x1000#64) ⋆ Eq (bsa.At 0x1008#64) ⋆ emp) m') ?_ ?_ (by decide)
  · exact hcall.weaken fun _ _ _ ⟨_, _, hm'⟩ _ _ => hm'
  · rintro st ⟨hpc, _, m', hm', _, hmem⟩
    exact ⟨hpc, sep_mono (fun _ => sep_mono (fun _ e => e ▸ hm')) hmem⟩

theorem x64_set_bytes_runs (bs : List UInt8) (v : BitVec 64) (hl : bs.length = 16) :
    Eventually (x64Target.mach.step x64SetBytesCompiled.host)
      (fun st => x64Target.mach.pc st = x64Init.ra0 ∧
        (x64Target.mach.mem (x64Target.mach.data st) =⋆
          (Eq ((List.replicate 16 v.toNat.toUInt8).At 0x1000#64) ⋆ emp) ⋆
          x64Target.Exit x64Init.sp0 (x64SetBytesCompiled.bound "set_bytes") ⋆ emp))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64, i64]) (x64SetBytesCompiled.bound "set_bytes")
          bs (0x1000#64, 16#64, v, ()))
        (x64Target.mach.labelAddr x64SetBytesCompiled.host "set_bytes")) := by
  have hbs : bs.length ≤ 8192 := by rw [hl]; decide
  have hm0 : (Eq (bs.At 0x1000#64) ⋆ emp) (bs.At 0x1000#64) := by
    rw [sep_emp]
  have hcall := @Examples.set_bytes_ok 64 bedrock2ExtEmpty setBytesFs 0 rfl []
    (bs.At 0x1000#64) 0x1000#64 16#64 v bs emp (by simp [hl]) hm0
  refine bedrock2Module_compiled_run_call x64Init x64SetBytesMod_ok x64SetBytesCompiled
    bedrock2ExtEmpty (by decide) (bedrock2NamesValid_empty (by decide))
    (fun _ h => nomatch h) (And.intro (fun _ h => nomatch h) (fun _ h => nomatch h))
    (p := Examples.set_bytes) List.mem_cons_self x64_64_mem
    bs (0x1000#64, 16#64, v, ()) hbs (by decide) (B := 0) (by decide) []
    (Q := fun _ m' => (Eq ((List.replicate 16 v.toNat.toUInt8).At 0x1000#64) ⋆ emp) m')
    ?_ ?_ (by decide)
  · exact hcall.weaken fun _ _ _ ⟨_, _, hm'⟩ _ _ => by simpa using hm'
  · rintro st ⟨hpc, _, m', hm', _, hmem⟩
    exact ⟨hpc, sep_mono (fun _ => sep_mono (fun _ e => e ▸ hm')) hmem⟩

theorem x64_mulh_runs (x y : BitVec 64) :
    Eventually (x64Target.mach.step x64MulhCompiled.host)
      (fun st => x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.RetsIn (bs := [i64, i64]) (interpBinop .mulhuu x y, x * y, ())
          (x64Target.mach.data st))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64]) (x64MulhCompiled.bound "mulh") [] (x, y, ()))
        (x64Target.mach.labelAddr x64MulhCompiled.host "mulh")) := by
  refine bedrock2Module_compiled_run_exec x64Init x64MulhMod_ok x64MulhCompiled
    bedrock2ExtEmpty (by decide) (bedrock2NamesValid_empty (by decide))
    (fun _ h => nomatch h) (And.intro (fun _ h => nomatch h) (fun _ h => nomatch h))
    (p := mulh) List.mem_cons_self x64_64_mem [] (x, y, ()) (by decide) (by decide)
    (B := 0) (by decide) []
    (Q := fun r m' => r = (interpBinop .mulhuu x y, x * y, ()) ∧
      m' = ([] : List UInt8).At 0x1000#64)
    (mulh_exec x y _) ?_ (by decide)
  rintro st ⟨hpc, rets, m', ⟨rfl, _⟩, hrets, _⟩
  exact ⟨hpc, hrets⟩

theorem x64_useDivmod_runs (x y : BitVec 64) (hy : y ≠ 0#64) :
    Eventually (x64Target.mach.step x64DivmodCompiled.host)
      (fun st => x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.RetsIn (bs := [i64, i64]) ((x / y) * 0x3e8#64 + (x % y), x % y, ())
          (x64Target.mach.data st))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64]) (x64DivmodCompiled.bound "use_divmod") []
          (x, y, ()))
        (x64Target.mach.labelAddr x64DivmodCompiled.host "use_divmod")) := by
  refine bedrock2Module_compiled_run_exec x64Init x64DivmodMod_ok x64DivmodCompiled
    bedrock2ExtEmpty (by decide) (bedrock2NamesValid_empty (by decide))
    (fun _ h => nomatch h) (And.intro (fun _ h => nomatch h) (fun _ h => nomatch h))
    (p := useDivmod) (List.mem_cons_of_mem _ List.mem_cons_self) x64_64_mem
    [] (x, y, ()) (by decide) (by decide) (B := 0) (by decide) []
    (Q := fun r m' => r = ((x / y) * 0x3e8#64 + (x % y), x % y, ()) ∧
      m' = ([] : List UInt8).At 0x1000#64)
    (useDivmod_exec x y hy _) ?_ (by decide)
  rintro st ⟨hpc, rets, m', ⟨rfl, _⟩, hrets, _⟩
  exact ⟨hpc, hrets⟩

/-! ## 4. `stackalloc` + End-to-End `unified` Backend Bridge (`bitcopy_store` & `swap`) -/

theorem x64_bitcopy_runs
    (hext : ∀ q ∈ bitcopyExtCallees,
      x64Target.FnSpec x64BitcopyCompiled.host q.1.1
        (legalEnv x64LegalTarget
          (Env.ofModule x64BitcopyMod (bedrock2Env .default bedrock2ExtEmpty bitcopyFs))
          q.1.1 q.1.2.1 q.1.2.2)
        q.2 0) :
    Eventually (x64Target.mach.step x64BitcopyCompiled.host)
      (fun st => x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = 15#64)
      (x64Target.mach.mkState
        (x64Init.initState (as := ([] : List Ty))
          (x64BitcopyCompiled.bound "bitcopy_store") [] ())
        (x64Target.mach.labelAddr x64BitcopyCompiled.host "bitcopy_store")) := by
  have hcall := bitcopy_store_ok_std3 (ext := bedrock2ExtEmpty) (e := bitcopyFs) rfl []
    (([] : List UInt8).At 0x1000#64)
  refine bedrock2Module_compiled_run_call x64Init x64BitcopyMod_ok x64BitcopyCompiled
    bedrock2ExtEmpty (by decide) (bedrock2NamesValid_empty (by decide)) hext
    (And.intro (by decide) (by decide)) (p := Examples.bitcopy_store) List.mem_cons_self
    x64_64_mem [] () (by decide) (by decide) (B := 8) (by decide) []
    (Q := fun r m' => r = (15#64, ()) ∧ m' = ([] : List UInt8).At 0x1000#64) ?_ ?_ (by decide)
  · exact hcall.weaken fun _ _ _ ⟨_, hm', hrets⟩ ⟨r, ⟨⟩⟩ hEq => by
      rw [hrets] at hEq
      change [r] = [15#64] at hEq
      cases hEq
      exact ⟨rfl, hm'⟩
  · rintro st ⟨hpc, _, m', ⟨rfl, _⟩, hrets, _⟩
    exact ⟨hpc, x64Init.retsIn_singleton 15#64 _ hrets⟩

@[expose] def x64SwapUnifiedDs : List x64Target.Directive :=
  ((unified bedrock2Frontend x64LegalTarget
      (bedrock2TargetBackend x64Target x64Hints)).run (Examples.swap 64)).toOption.getD []

@[expose] def x64BitcopyUnifiedDs : List x64Target.Directive :=
  ((unified bedrock2Frontend x64LegalTarget
      (bedrock2TargetBackend x64Target x64Hints)).run Examples.bitcopy_store).toOption.getD []

theorem x64_unified_swap_run :
    (unified bedrock2Frontend x64LegalTarget
      (bedrock2TargetBackend x64Target x64Hints)).run (Examples.swap 64) =
      .ok x64SwapUnifiedDs := by
  have hx :
      ((unified bedrock2Frontend x64LegalTarget
        (bedrock2TargetBackend x64Target x64Hints)).run (Examples.swap 64)).isOk = true := by
    t_kernel_rfl
  exact except_isOk_getD _ [] hx

theorem x64_unified_bitcopy_run :
    (unified bedrock2Frontend x64LegalTarget
      (bedrock2TargetBackend x64Target x64Hints)).run Examples.bitcopy_store =
      .ok x64BitcopyUnifiedDs := by
  have hx :
      ((unified bedrock2Frontend x64LegalTarget
        (bedrock2TargetBackend x64Target x64Hints)).run Examples.bitcopy_store).isOk = true := by
    t_kernel_rfl
  exact except_isOk_getD _ [] hx

theorem x64_unified_swap_msat :
    bedrock2TargetMSat x64Target x64Hints x64SwapUnifiedDs
      ((unified bedrock2Frontend x64LegalTarget (bedrock2TargetBackend x64Target x64Hints)).tr
        (Examples.swap 64) swapB2Spec) :=
  bedrock2_unified_sound .default x64LegalTarget
    ⟨bedrock2TargetBackend x64Target x64Hints,
      bedrock2TargetBackend x64Target x64Hints,
      bedrock2TargetBackend x64Target x64Hints⟩
    (Examples.swap 64) swapB2Spec x64SwapUnifiedDs x64_unified_swap_run swap_sat_b2Spec

theorem x64_unified_bitcopy_msat :
    bedrock2TargetMSat x64Target x64Hints x64BitcopyUnifiedDs
      ((unified bedrock2Frontend x64LegalTarget (bedrock2TargetBackend x64Target x64Hints)).tr
        Examples.bitcopy_store bitcopyB2Spec) :=
  bedrock2_unified_sound .default x64LegalTarget
    ⟨bedrock2TargetBackend x64Target x64Hints,
      bedrock2TargetBackend x64Target x64Hints,
      bedrock2TargetBackend x64Target x64Hints⟩
    Examples.bitcopy_store bitcopyB2Spec x64BitcopyUnifiedDs
    x64_unified_bitcopy_run bitcopy_sat_b2Spec

theorem x64_unified_swap_fnSpec (h : x64Target.mach.Host) (k₀ : Nat)
    (hinf : x64SwapUnifiedDs.IsInfixAt (x64Target.mach.prog h) k₀)
    (hu : x64Target.LabelsUnique h) :
    x64Target.Defined h "swap" ∧
    x64Target.FnSpec h "swap" (swapB2Spec.toSpec "swap" 2 0) 2048 0 := by
  refine bedrock2_unified_fnSpec .default x64Target x64LegalTarget x64Hints (Examples.swap 64)
    swapB2Spec x64SwapUnifiedDs x64_unified_swap_run swap_sat_b2Spec x64_64_mem
    h k₀ 2048 0 (fun _ => 0) hinf hu ?_ (by decide)
  intro fn hlow
  have hfn : fn = b2LowerDefault (Examples.swap 64) := by
    change b2NamedFuncToFn? .default (Examples.swap 64) = .ok fn at hlow
    dsimp only [b2LowerDefault]; rw [hlow]
  subst hfn
  refine ⟨of_decide_eq_true (by t_kernel_rfl), ?_, ?_⟩
  · intro g as bs hg
    have hc : ((b2LowerDefault (Examples.swap 64)).mid x64LegalTarget).ext.callees = [] := by
      t_kernel_rfl
    rw [hc] at hg; cases hg
  · intro g hg
    have he : ((b2LowerDefault (Examples.swap 64)).mid x64LegalTarget).ext.exits = [] := by
      t_kernel_rfl
    rw [he] at hg; cases hg

theorem x64_unified_bitcopy_fnSpec (h : x64Target.mach.Host) (k₀ : Nat)
    (hinf : x64BitcopyUnifiedDs.IsInfixAt (x64Target.mach.prog h) k₀)
    (hu : x64Target.LabelsUnique h)
    (halloc : x64Target.FnSpec h "__b2_stackalloc"
      (legalEnv x64LegalTarget (bedrock2Env .default bedrock2ExtEmpty [Examples.bitcopy_store])
        "__b2_stackalloc" [i64] [i64]) 0 0)
    (hfree : x64Target.FnSpec h "__b2_stackfree"
      (legalEnv x64LegalTarget (bedrock2Env .default bedrock2ExtEmpty [Examples.bitcopy_store])
        "__b2_stackfree" [i64, i64] []) 0 0) :
    x64Target.Defined h "bitcopy_store" ∧
    x64Target.FnSpec h "bitcopy_store" (bitcopyB2Spec.toSpec "bitcopy_store" 0 1) 2048 0 := by
  refine bedrock2_unified_fnSpec .default x64Target x64LegalTarget x64Hints Examples.bitcopy_store
    bitcopyB2Spec x64BitcopyUnifiedDs x64_unified_bitcopy_run bitcopy_sat_b2Spec x64_64_mem
    h k₀ 2048 0 (fun _ => 0) hinf hu ?_ (by decide)
  intro fn hlow
  have hfn : fn = b2LowerDefault Examples.bitcopy_store := by
    change b2NamedFuncToFn? .default Examples.bitcopy_store = .ok fn at hlow
    dsimp only [b2LowerDefault]; rw [hlow]
  subst hfn
  refine ⟨of_decide_eq_true (by t_kernel_rfl), ?_, ?_⟩
  · intro g as bs hg
    have hc : ((b2LowerDefault Examples.bitcopy_store).mid x64LegalTarget).ext.callees =
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
    have he : ((b2LowerDefault Examples.bitcopy_store).mid x64LegalTarget).ext.exits = [] := by
      t_kernel_rfl
    rw [he] at hg; cases hg

end LeanQbeTest.T.UnifiedBedrock2X64Test

#print axioms LeanQbeTest.T.UnifiedBedrock2X64Test.x64_swap_runs
#print axioms LeanQbeTest.T.UnifiedBedrock2X64Test.x64_set_bytes_runs
#print axioms LeanQbeTest.T.UnifiedBedrock2X64Test.x64_mulh_runs
#print axioms LeanQbeTest.T.UnifiedBedrock2X64Test.x64_useDivmod_runs
#print axioms LeanQbeTest.T.UnifiedBedrock2X64Test.x64_bitcopy_runs
#print axioms LeanQbeTest.T.UnifiedBedrock2X64Test.x64_unified_swap_msat
#print axioms LeanQbeTest.T.UnifiedBedrock2X64Test.x64_unified_bitcopy_msat
#print axioms LeanQbeTest.T.UnifiedBedrock2X64Test.x64_unified_swap_fnSpec
#print axioms LeanQbeTest.T.UnifiedBedrock2X64Test.x64_unified_bitcopy_fnSpec
