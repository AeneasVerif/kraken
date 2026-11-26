module

public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Amd64.IselLemmas5
public import LeanQbe.T.Amd64.IselZeroLemmas
public import LeanQbe.T.Amd64.VllFactorX64
public import LeanQbe.T.Amd64.VllFactorX64Zero
public import LeanQbe.T.Vll.Passes
public import LeanQbe.T.Vll.PassesLemmas
public import LeanQbe.T.RegaLemmas4
public import LeanQbe.T.Spill
meta import LeanQbe.T.Amd64.TargLemmas
meta import LeanQbe.T.Amd64.VllFactorX64
meta import LeanQbe.T.Vll.Passes
meta import LeanQbe.T.Spill

/-!
# x64 `xorl %rd, %rd` Zero-Idiom & Flag-Liveness Gate Tests (`X64ZeroIdiomTest`)

Regression tests covering Wave-4 Shard 2 (`C-P1.2`):
1. Emits 2-byte `xorl %ed, %ed` (and zero `mov $0`) for zero materializations (`copy i32 0`,
   `copy i64 0`, `copy bool false`, `ofBool 64 false`, and after flag-setting `add 32` via
   `Hints.deadFlags`) when status flags are dead.
2. Preserves flag-safe `mov $0` when a live `.flag` variable spans across zero materialization
   (e.g. between `cmp` and `select`/`jnz`, or across carry-chain `addc`), with `0` spurious
   `test` instructions.
3. Untrusted `Hints.deadFlags` fails closed when poisoned (`true` while a `.flag` is live).
4. `Vll.Passes.elimRedundantWindow` rewrites `[.movi rd 0#64, .clearFlags]` to
   `[.alu .xor .w32 rd rd (.reg rd) true]` under `x64Arch`, and `vllX64_compileFn_eq`
   + `x64Arch_passWf` hold cleanly with only standard Lean axioms (`std3`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.X64ZeroIdiomTest

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Vll

/-! ## 1. `x64Arch_passWf` Witness & `Vll.Passes` `[.movi rd 0#64, .clearFlags]` Rule -/

theorem x64Arch_passWf : x64Arch.PassWf where
  toWf := x64Arch_wf
  prologue0_flags := fun h => by cases h
  epilogue0_flags := fun h => by cases h
  canonAbi64_flags := fun _ _ => rfl
  cmp_overwrite := fun _ _ _ _ => rfl
  test_overwrite := fun _ _ _ _ => rfl
  xor32_zero_clearFlags := fun _ old a f => by
    refine ⟨rfl, ?_⟩
    have hxor : a ^^^ a = 0#32 := by
      apply BitVec.eq_of_getElem_eq; intro i hi; simp
    dsimp only [x64Arch, x64AluFlags, x64ClearFlagsVal]
    rw [hxor]; rfl

example :
    elimRedundantWindow x64Arch [.movi .rax 0#64, .clearFlags, .ret] =
      [.alu .xor .w32 .rax .rax (.reg .rax) true, .ret] := rfl

example :
    elimRedundantWindow x64Arch [.movi .rax 1#64, .clearFlags, .ret] =
      [.movi .rax 1#64, .clearFlags, .ret] := rfl

/-! ## 2. Helpers -/

meta def hintsOf (fs : List Fn) : List x64Target.toIsa.Hints :=
  fs.map (Fn.computeHints x64Target.toIsa x64LegalTarget)

meta def chk (fs : List Fn) : Bool :=
  checkCompile x64Target x64Layout x64LegalTarget [] [] 0 fs (hintsOf fs) 2048

meta def codeOf (fs : List Fn) : List Directive :=
  extractCode (compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes [] [] 0 fs
    (hintsOf fs))

meta def isXorZeroDir : Directive → Bool
  | .instr (.regular _ .W32 (.xor (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))) =>
    rd == rs
  | _ => false

meta def isMoviZeroDir : Directive → Bool
  | .instr (.regular _ .W32 (.mov (.reg _) (.imm (.int64 ⟨0⟩)))) => true
  | .instr (.regular _ .W64 (.mov (.reg _) (.imm (.int64 ⟨0⟩)))) => true
  | _ => false

meta def isTestDir : Directive → Bool
  | .instr (.regular _ _ (.test _ _)) => true
  | _ => false

meta def countDirs (p : Directive → Bool) (ds : List Directive) : Nat := (ds.filter p).length

/-! ## 3. Dead Flags Emit `xorl %ed, %ed` (`0` `mov $0`) -/

meta def retZero32Fn : Fn :=
  ⟨"retZero32", [i64], [i32], fun _ _ (_, ()) =>
    .let_ (op1 (.copy i32) (.imm 0#32)) fun (z, ()) => .ret (.var z, ())⟩

meta def retZero64Fn : Fn :=
  ⟨"retZero64", [i64], [i64], fun _ _ (_, ()) =>
    .let_ (op1 (.copy i64) (.imm 0#64)) fun (z, ()) => .ret (.var z, ())⟩

meta def retZeroOfBoolFn : Fn :=
  ⟨"retZeroOfBool", [i64], [i64], fun _ _ (_, ()) =>
    .let_ (op1 (.ofBool 64) (.imm false)) fun (z, ()) => .ret (.var z, ())⟩

/-- Zero constant after flag-clobbering `mul 32`, emitted via 2-byte `xorl %ed, %ed`. -/
meta def mulThenZeroFn : Fn :=
  ⟨"mulThenZero", [i32, i32], [i32, i64], fun _ _ (a, b, ()) =>
    .let_ (op2 (.mul i32) (.var a) (.var b)) fun (s, ()) =>
    .let_ (op1 (.copy i64) (.imm 0#64)) fun (z, ()) =>
    .ret (.var s, .var z, ())⟩

#guard chk [retZero32Fn] && chk [retZero64Fn] && chk [retZeroOfBoolFn] && chk [mulThenZeroFn]
#guard countDirs isXorZeroDir (codeOf [retZero32Fn]) >= 1
#guard countDirs isMoviZeroDir (codeOf [retZero32Fn]) == 0
#guard countDirs isXorZeroDir (codeOf [retZero64Fn]) >= 1
#guard countDirs isMoviZeroDir (codeOf [retZero64Fn]) == 0
#guard countDirs isXorZeroDir (codeOf [retZeroOfBoolFn]) >= 1
#guard countDirs isMoviZeroDir (codeOf [retZeroOfBoolFn]) == 0
#guard countDirs isXorZeroDir (codeOf [mulThenZeroFn]) >= 1
#guard countDirs isMoviZeroDir (codeOf [mulThenZeroFn]) == 0

/-! ## 4. Live `FlagFact` / `.flag` Preserves `mov $0` (Zero Spurious Clobbering) -/

/-- `z = 0` between `c = (x <u y)` and `select`/`jnz`: `deadFlags = false` preserves `c` in
hardware flags without clobbering (`xorZero = 0`, `moviZero >= 1`, `test = 0`). -/
meta def liveFlagCmpZeroJnzFn : Fn :=
  ⟨"liveFlagCmpZeroJnz", [i64, i64, i64], [i64], fun _ _ (x, y, a, ()) =>
    .let_ (op2 (.cmp .ult i64) (.var x) (.var y)) fun (c, ()) =>
    .let_ (op1 (.copy i64) (.imm 0#64)) fun (z, ()) =>
    .let_ (op3 (.select i64) (.var c) (.var a) (.var z)) fun (s, ()) =>
    .jnz (.var c) (.ret (.var s, ())) (.ret (.var z, ()))⟩

/-- Zero constant between `c = (x == y)` and `ofBool`: preserves live status flags across zero
load (`xorZero = 0`, `moviZero >= 1`). -/
meta def liveFlagCmpOfBoolZeroFn : Fn :=
  ⟨"liveFlagCmpOfBoolZero", [i64, i64], [i64, i64], fun _ _ (x, y, ()) =>
    .let_ (op2 (.cmp .eq i64) (.var x) (.var y)) fun (c, ()) =>
    .let_ (op1 (.copy i64) (.imm 0#64)) fun (z, ()) =>
    .let_ (op1 (.ofBool 64) (.var c)) fun (b, ()) =>
    .ret (.var b, .var z, ())⟩

#guard chk [liveFlagCmpZeroJnzFn] && chk [liveFlagCmpOfBoolZeroFn]
#guard countDirs isXorZeroDir (codeOf [liveFlagCmpZeroJnzFn]) == 0
#guard countDirs isMoviZeroDir (codeOf [liveFlagCmpZeroJnzFn]) >= 1
#guard countDirs isTestDir (codeOf [liveFlagCmpZeroJnzFn]) == 0
#guard countDirs isXorZeroDir (codeOf [liveFlagCmpOfBoolZeroFn]) == 0
#guard countDirs isMoviZeroDir (codeOf [liveFlagCmpOfBoolZeroFn]) >= 1

/-! ## 5. Untrusted `Hints.deadFlags` Fails Closed & `vllX64` Parity Check -/

meta def badHintCheck : Bool :=
  let h := Fn.computeHints x64Target.toIsa x64LegalTarget liveFlagCmpZeroJnzFn
  let hBad := { h with deadFlags := h.deadFlags.insert 1 true }
  match Rega.lowerFn x64Target.toIsa hBad {} liveFlagCmpZeroJnzFn with
  | .error _ => true
  | .ok _ => false

#guard badHintCheck

meta def vllParityCheck (f : Fn) : Bool :=
  let h := sanitizeHints (Fn.computeHints x64Isa x64LegalTarget f)
  match compileFn vllX64Target.toIsa x64LegalTarget h f,
      compileFn x64Target.toIsa x64LegalTarget h f with
  | .ok vc, .ok xc => asmX64List vc == xc
  | _, _ => false

#guard vllParityCheck retZero32Fn && vllParityCheck retZero64Fn &&
  vllParityCheck retZeroOfBoolFn && vllParityCheck mulThenZeroFn &&
  vllParityCheck liveFlagCmpZeroJnzFn && vllParityCheck liveFlagCmpOfBoolZeroFn

/-! ## 6. Axiom Audit (`std3`) -/

#print axioms LeanQbe.T.Amd64.x64Gpr_moviDeadFlags_spec
#print axioms LeanQbe.T.Amd64.vllX64_moviDeadFlags_spec
#print axioms LeanQbe.T.Rega.tryMoviZero_ok
#print axioms LeanQbe.T.Rega.execMove_ok
#print axioms LeanQbe.T.Rega.lowerFn_correct
#print axioms LeanQbe.T.Amd64.vllX64_compileFn_eq
#print axioms x64Arch_passWf

end LeanQbeTest.T.X64ZeroIdiomTest
