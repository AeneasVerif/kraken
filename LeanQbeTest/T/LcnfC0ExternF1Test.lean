module

import LeanQbe.T.MainCertProof
import LeanQbe.T.Amd64.TargLemmas
import LeanQbe.T.LeanLCNF.C0Extern
import LeanQbe.T.PrintCpp
import LeanQbe.T.PrintQbe
meta import Lean
import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.LeanLCNF.Lower
meta import LeanQbe.T.LeanLCNF.C0Extern
meta import LeanQbe.T.Bootstrap0.Splice0
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe

/-!
# Shard `F1` Verification Tests (`LinkedCert.weakenNoExit` Amd64 & `C0Extern`)

Exercises `LCNF↔C0 FFI` Shard `F1` (Arm64 companion is `LcnfC0ExternF1Arm64Test`):
1. Zero-recompilation `LinkedCert.weakenNoExit` and `LinkedCert.weakenExits` on tiny `2+2`
   SysV x64 `LinkedCert`s (`x64Target`), composing a zero-exit leaf certificate (`exits = []`,
   `nX = 0`) with an exit-using module (`exits = rtExitSyms`, `nX = 64`) via `LinkedCert.append`,
   verifying definitional `code`/`bounds` preservation, `defined_exit_host`, and negative exit
   rejection.
2. Zero-axiom `C0Extern` specification, `ffiC0Externs` validation against `LcnfC0Ffi.ffiMod`,
   elaboration-time `@&` borrow-parity checking (`readLcModuleWithExts`, including negative
   mismatch tests), `splice_lcnf_tflat_with_exts!` kernel lowering (`passRt := true/false` and
   `c0Void := true`), `lowerModuleWithExts_nil` parity, `Fn.Wf`, `PrintCpp`/`PrintQbe`, and
   `#print axioms` (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.LcnfC0ExternF1Test

open LeanQbe.T
open LeanQbe.T.Amd64
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Frontend.C0

#eval show Lean.CoreM Unit from do
  let mods := (← Lean.getEnv).allImportedModuleNames
  let bad := mods.filter fun m =>
    let s := m.toString
    s.startsWith "Kraken.AArch64" || s.startsWith "LeanQbe.T.Arm64"
  if !bad.isEmpty then
    throwError "LcnfC0ExternF1Test leaked Arm64 imports: {bad.toList}"

/-! ## 1. Tiny `2+2` `LinkedCert.weakenNoExit` Fixture (`Amd64`, 0 Recompilation) -/

/-- Pure leaf function (`f1_leaf x = x + 7`), zero exits. -/
def fnF1Leaf : Fn :=
  ⟨"f1_leaf", [i64], [i64], fun _ _ (x, ()) =>
    .let_ ⟨.add i64, (.var x, .imm 7#64, ())⟩ fun (r, ()) =>
    .ret (.var r, ())⟩

/-- Pure caller (`f1_callee x = f1_leaf(x) + 1`), zero exits. -/
def fnF1Callee : Fn :=
  ⟨"f1_callee", [i64], [i64], fun _ _ (x, ()) =>
    .call "f1_leaf" (as := [i64]) (bs := [i64]) (.var x, ()) fun (y, ()) =>
    .let_ ⟨.add i64, (.var y, .imm 1#64, ())⟩ fun (r, ()) =>
    .ret (.var r, ())⟩

/-- Exit-capable caller calling `.exit "lcnf_panic"` on `x = 0` else `f1_callee x`. -/
def fnF1Checked : Fn :=
  ⟨"f1_checked", [i64], [i64], fun _ _ (x, ()) =>
    .let_ ⟨.cmp .eq i64, (.var x, .imm 0#64, ())⟩ fun (b, ()) =>
    .jnz (.var b)
      (.exit (as := [i64, i64]) "lcnf_panic" (.imm 0#64, .imm 1#64, ()))
      (.call "f1_callee" (as := [i64]) (bs := [i64]) (.var x, ()) fun (y, ()) =>
        .ret (.var y, ()))⟩

/-- Second exit-capable wrapper (`f1_top x = f1_checked(x)`). -/
def fnF1Top : Fn :=
  ⟨"f1_top", [i64], [i64], fun _ _ (x, ()) =>
    .call "f1_checked" (as := [i64]) (bs := [i64]) (.var x, ()) fun (y, ()) =>
    .ret (.var y, ())⟩

def noExitMod : Module :=
  { fns := [fnF1Leaf, fnF1Callee], externs := [], exits := [] }

def exitRtMod : Module :=
  { fns := [fnF1Checked, fnF1Top]
    externs := [{ name := "f1_callee", as := [i64], rs := [i64] }]
    exits := rtExitSyms }

def fullF1Mod : Module :=
  { fns := noExitMod.fns ++ exitRtMod.fns, externs := [], exits := rtExitSyms }

compile_linked_chunks! x64NoExitCert
  x64Target x64Layout x64LegalTarget x64LabelClean noExitMod 1
  (compileExt := true)

compile_linked_chunks! x64ExitCert
  x64Target x64Layout x64LegalTarget x64LabelClean exitRtMod 1
  (ext := x64NoExitCert.exportedExt) (exits := rtExitSyms) (nX := 64)

/-- Lift zero-exit `x64NoExitCert` to `exits = rtExitSyms`, `nX = 64` with zero recompilation. -/
noncomputable def x64WeakCert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      noExitMod [] rtExitSyms 64 2048 :=
  x64NoExitCert.weakenNoExit rtExitSyms 64 (by t_kernel_rfl) (by t_kernel_rfl)

theorem x64WeakCert_numChunks : x64WeakCert.numChunks = x64NoExitCert.numChunks :=
  by rfl

theorem x64WeakCert_bounds : x64WeakCert.bounds = x64NoExitCert.bounds :=
  x64NoExitCert.weakenNoExit_bounds rtExitSyms 64 (by t_kernel_rfl) (by t_kernel_rfl)

theorem x64WeakCert_code0 :
    (x64WeakCert.chunks[0]'(by decide)).compiled.code =
      (x64NoExitCert.chunks[0]'(by decide)).compiled.code :=
  by rfl

theorem x64WeakCert_defined_panic :
    x64Target.Defined x64WeakCert.host "lcnf_panic" :=
  x64WeakCert.defined_exit_host (by simp [rtExitSyms])

noncomputable def x64ComposedCert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      fullF1Mod [] rtExitSyms 64 2048 :=
  x64WeakCert.append x64ExitCert rfl (by t_kernel_rfl)

theorem x64ComposedCert_bounds_len : x64ComposedCert.bounds.length = 4 := by
  rw [x64ComposedCert.bounds_length, x64ComposedCert.fns_eq]
  decide

/-- Further lift `x64WeakCert` via `LinkedCert.weakenExits` at fixed `nX = 64`. -/
noncomputable def x64ExtraExitCert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      noExitMod [] (rtExitSyms ++ ["f1_extra_exit"]) 64 2048 :=
  x64WeakCert.weakenExits (rtExitSyms ++ ["f1_extra_exit"])
    (fun _ hs => List.mem_append_left _ hs) (by t_kernel_rfl) (by t_kernel_rfl)

theorem x64ExtraExitCert_defined :
    x64Target.Defined x64ExtraExitCert.host "f1_extra_exit" :=
  x64ExtraExitCert.defined_exit_host (by simp [rtExitSyms])

/-- Negative check: colliding exit symbol or newline in exit name is rejected cleanly. -/
theorem weakenCheck_rejects_dup_fn :
    checkWeakenExitsChunks x64Layout ["f1_leaf"] x64NoExitCert.chunks = false := by
  t_kernel_rfl

theorem weakenCheck_rejects_bad_exit :
    checkWeakenExitsChunks x64Layout [".Lbad"] x64NoExitCert.chunks = false := by
  t_kernel_rfl

/-! ## 2. `C0Extern` Lean Stubs, Borrow-Parity Validation, Lowering & Splicing -/

@[noinline] public def stubBaPtr (ba : @& ByteArray) : USize :=
  ba.size.toUSize

@[noinline] public def stubBaLen (ba : @& ByteArray) : USize :=
  ba.size.toUSize

@[noinline] public def stubCarveScratch (req : USize) : USize :=
  req + 8

@[noinline] public def stubRestoreScratch (saved : USize) : Unit :=
  let _ := saved
  ()

@[noinline] public def stubSentinelIdx (w : USize) : USize :=
  w

@[noinline] public def stubBaToNatS (ba : @& ByteArray) : Nat :=
  ba.size

@[noinline] public def f1Caller (ba : @& ByteArray) (w : USize) : USize :=
  let ptr := stubBaPtr ba
  let len := stubBaLen ba
  let sv := stubCarveScratch len
  let s := stubSentinelIdx w
  let n := stubBaToNatS ba
  ptr + len + sv + s + n.toUSize

@[noinline] public def pureAddDemo (x y : USize) : USize :=
  x + y

def demoExts : List C0Extern :=
  [ { leanName := "LeanQbeTest.T.LcnfC0ExternF1Test.stubBaPtr"
      c0Sym := "lcnf_ffi_ba_ptr"
      params := [.object]
      borrows := [true]
      retTy := .usize
      passRt := false }
  , { leanName := "LeanQbeTest.T.LcnfC0ExternF1Test.stubBaLen"
      c0Sym := "lcnf_ffi_ba_len"
      params := [.object]
      borrows := [true]
      retTy := .usize
      passRt := false }
  , { leanName := "LeanQbeTest.T.LcnfC0ExternF1Test.stubCarveScratch"
      c0Sym := "lcnf_ffi_carve_scratch"
      params := [.usize]
      borrows := [false]
      retTy := .usize
      passRt := true }
  , { leanName := "LeanQbeTest.T.LcnfC0ExternF1Test.stubSentinelIdx"
      c0Sym := "lcnf_ffi_sentinel_byte_idx"
      params := [.usize]
      borrows := [false]
      retTy := .usize
      passRt := false }
  , { leanName := "LeanQbeTest.T.LcnfC0ExternF1Test.stubBaToNatS"
      c0Sym := "lcnf_ffi_ba_to_nat_s"
      params := [.object]
      borrows := [true]
      retTy := .tobject
      passRt := true }
  ]

theorem demoExts_in_ffiMod : checkC0Externs demoExts (some ffiMod) = true := by
  decide

lcnf_of_lean_with_exts! demoLc demoExts [f1Caller]
lcnf_of_lean! pureNilLc [pureAddDemo]

#guard demoLc.decls.length == 1
#guard demoExts.all fun e => demoLc.externs.any (·.name == e.leanName)
#guard checkLcModuleExts demoLc demoExts (some ffiMod)

splice_lcnf_tflat_with_exts! demoTfs demoLc demoExts

def voidExts : List C0Extern :=
  [ { leanName := "LeanQbeTest.T.LcnfC0ExternF1Test.stubRestoreScratch"
      c0Sym := "lcnf_ffi_restore_scratch"
      params := [.usize]
      borrows := [false]
      retTy := .tagged
      passRt := true
      c0Void := true }
  ]

def voidLcMod : LcModule :=
  { name := "voidDemo"
    roots := ["voidCaller"]
    decls :=
      [ { name := "voidCaller"
          params := [{ id := 1, ty := .usize, borrow := false }]
          retTy := .usize
          body :=
            .let_ 2 .tagged
              (.fap "LeanQbeTest.T.LcnfC0ExternF1Test.stubRestoreScratch" [.var 1])
              (.ret (.var 1)) }
      ]
    externs := [{ name := "LeanQbeTest.T.LcnfC0ExternF1Test.stubRestoreScratch",
                  params := [.usize], retTy := .tagged }]
    snaps := [] }

theorem voidExts_in_ffiMod : checkC0Externs voidExts (some ffiMod) = true := by
  decide

splice_lcnf_tflat_with_exts! voidTfs voidLcMod voidExts

theorem voidTfs_fns_wf :
    ∀ f ∈ (lcnfTModuleWithExts voidTfs voidExts).fns, f.Wf :=
  tflatFnsToFns_wf voidTfs

#guard (PrintCpp.ppTModule (lcnfTModuleWithExts voidTfs voidExts)).isOk
#guard (PrintQbe.module (lcnfTModuleWithExts voidTfs voidExts)).isOk

theorem demoTfs_fns_wf :
    ∀ f ∈ (lcnfTModuleWithExts demoTfs demoExts).fns, f.Wf :=
  tflatFnsToFns_wf demoTfs

theorem demoTfs_lower_nil_parity :
    lowerModuleWithExts pureNilLc [] = lowerModule pureNilLc :=
  lowerModuleWithExts_nil pureNilLc

theorem pure_validate_rejects_borrow_mismatch :
    let badDecl : LcDecl :=
      { name := "LeanQbeTest.T.LcnfC0ExternF1Test.stubBaLen"
        params := [{ id := 1, ty := .object, borrow := false }]
        retTy := .usize
        body := .ret (.var 1) }
    let badMod : LcModule :=
      { name := "bad", roots := [], decls := [badDecl], externs := [], snaps := [] }
    checkLcModuleExts badMod demoExts none = false := by
  decide

/- Verify elaboration-time `verifyC0ExternBorrowMeta` catches flipped `@&` borrows and missing
`C0` signatures, while `PrintCpp`/`PrintQbe` cleanly render `lcnfTModuleWithExts`. -/
#eval show Lean.CoreM Unit from do
  let badExt : C0Extern :=
    { leanName := "LeanQbeTest.T.LcnfC0ExternF1Test.stubBaLen"
      c0Sym := "lcnf_ffi_ba_len"
      params := [.object]
      borrows := [false]
      retTy := .usize
      passRt := false }
  let ok ← try
    verifyC0ExternBorrowMeta badExt
    pure true
  catch _ =>
    pure false
  if ok then
    throwError "expected borrow mismatch error for owned vs @& ByteArray"
  let mod := lcnfTModuleWithExts demoTfs demoExts
  if !(LeanQbe.T.PrintCpp.ppTModule mod).isOk then
    throwError "PrintCpp.ppTModule failed on lcnfTModuleWithExts"
  if !(LeanQbe.T.PrintQbe.module mod).isOk then
    throwError "PrintQbe.module failed on lcnfTModuleWithExts"

/--
info: '_private.LeanQbeTest.T.LcnfC0ExternF1Test.0.LeanQbeTest.T.LcnfC0ExternF1Test.x64WeakCert'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms x64WeakCert

/--
info: '_private.LeanQbeTest.T.LcnfC0ExternF1Test.0.LeanQbeTest.T.LcnfC0ExternF1Test.x64ComposedCert'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms x64ComposedCert

/--
info: 'LeanQbeTest.T.LcnfC0ExternF1Test.demoTfs_lower' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms demoTfs_lower

/--
info: '_private.LeanQbeTest.T.LcnfC0ExternF1Test.0.LeanQbeTest.T.LcnfC0ExternF1Test.demoTfs_fns_wf'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms demoTfs_fns_wf

/--
info: 'LeanQbe.T.LeanLCNF.ffiC0Externs_valid' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms LeanQbe.T.LeanLCNF.ffiC0Externs_valid

/--
info: 'LeanQbe.T.LeanLCNF.lowerModuleWithExts_nil' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms LeanQbe.T.LeanLCNF.lowerModuleWithExts_nil

end LeanQbeTest.T.LcnfC0ExternF1Test
