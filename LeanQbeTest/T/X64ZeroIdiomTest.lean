module

public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Amd64.IselLemmas5
public import LeanQbe.T.Amd64.IselZeroLemmas
public import LeanQbe.T.RegaLemmasZero
public import LeanQbe.T.RegaLemmas4
public import LeanQbe.T.Spill
public import LeanQbe.T.MainFlatLemmas
meta import Lean
meta import LeanQbe.T.Amd64.TargLemmas
meta import LeanQbe.T.Amd64.IselZeroLemmas
meta import LeanQbe.T.RegaLemmasZero
meta import LeanQbe.T.Spill
meta import LeanQbe.T.MainFlat

/-!
# x64 `xorl %rd, %rd` Zero-Idiom & Flag-Liveness Gate Tests (`X64ZeroIdiomTest`)

Regression tests covering Wave-4 Shard 2 (`C-P1.2`) on production `x64Target` / `x64Gpr`:
1. Production `x64Gpr.moviDeadFlags?` and `Rega.execMovi` rules emit `xorl %ed, %ed` (`maskAll`)
   when flags are dead or `deadHint = true`, and `moviI` (`maskNone`) when flags are live or
   `c ≠ 0`.
2. Emits 2-byte `xorl %ed, %ed` (and zero `mov $0`) for zero materializations (`copy i32 0`,
   `copy i64 0`, `copy bool false`, `ofBool 64 false`, and after flag-setting `mul 32` via
   `Hints.deadFlags`) when status flags are dead.
3. Preserves flag-safe `mov $0` when a live `.flag` variable spans across zero materialization
   (e.g. between `cmp` and `select`/`jnz`), with `0` spurious `test` instructions.
4. Untrusted `Hints.deadFlags` fails closed when poisoned (`true` while a `.flag` is live).
5. `MainFlat` (`compileFlatFn`) parity on all zero-idiom cases, AArch64/Vll isolation checks, and
   `<= std3` axiom audit.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.X64ZeroIdiomTest

open LeanQbe.T LeanQbe.T.Amd64

/-! ## 1. Production `x64Gpr.moviDeadFlags?` & `Rega.execMovi` Rules -/

theorem x64Gpr_moviDeadFlags_eq : x64Gpr.moviDeadFlags? = some x64MoviDeadFlags := rfl

private def emptySymSt : Rega.SymState x64Isa :=
  { regs := [], slots := .empty, defs := .empty, vecWidths := .empty }

private def liveFlagSymSt : Rega.SymState x64Isa :=
  { emptySymSt with flags := some (.cmp 64 (.var 0) (.var 1) false) }

example :
    x64MoviDeadFlags .rax 0#64 =
      ([.instr (x64InsI .W32 (.xor (.reg (d .rax)) (.reg (d .rax))))], maskAll) := rfl

example :
    x64MoviDeadFlags .rax 5#64 = ([.instr (moviI .rax 5#64)], maskNone) := rfl

example :
    Rega.execMovi x64Isa emptySymSt false .rax 0#64 =
      ([.instr (x64InsI .W32 (.xor (.reg (d .rax)) (.reg (d .rax))))], maskAll) := rfl

example :
    Rega.execMovi x64Isa liveFlagSymSt false .rax 0#64 = ([moviD .rax 0#64], maskNone) := rfl

example :
    Rega.execMovi x64Isa liveFlagSymSt true .rax 0#64 =
      ([.instr (x64InsI .W32 (.xor (.reg (d .rax)) (.reg (d .rax))))], maskAll) := rfl

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

/-! ## 5. Untrusted `Hints.deadFlags` Fails Closed & `MainFlat` Parity Check -/

meta def badHintCheck : Bool :=
  let h := Fn.computeHints x64Target.toIsa x64LegalTarget liveFlagCmpZeroJnzFn
  let hBad := { h with deadFlags := h.deadFlags.insert 1 true }
  match Rega.lowerFn x64Target.toIsa hBad {} liveFlagCmpZeroJnzFn with
  | .error _ => true
  | .ok _ => false

#guard badHintCheck

meta def toTFlatFn (f : Fn) : TFlatFn :=
  ⟨f.name, f.as, f.rs, reifyFunc f.body⟩

meta def flatParityCheck (f : Fn) : Bool :=
  let tf := toTFlatFn f
  let h := Fn.computeHints x64Target.toIsa x64LegalTarget tf.toFn
  let hOrig := Fn.computeHints x64Target.toIsa x64LegalTarget f
  if !tf.wfCheck then false
  else
    match compileFlatFn x64Target.toIsa x64LegalTarget h tf,
        compileFn x64Target.toIsa x64LegalTarget h tf.toFn,
        compileFlatFn x64Target.toIsa x64LegalTarget hOrig tf,
        compileFn x64Target.toIsa x64LegalTarget hOrig f with
    | .ok fc, .ok xc, .ok fc0, .ok xc0 => fc == xc && fc0 == xc0
    | _, _, _, _ => false

#guard flatParityCheck retZero32Fn && flatParityCheck retZero64Fn &&
  flatParityCheck retZeroOfBoolFn && flatParityCheck mulThenZeroFn &&
  flatParityCheck liveFlagCmpZeroJnzFn && flatParityCheck liveFlagCmpOfBoolZeroFn

/-! ## 6. Axiom Audit (`std3`) & Isolation Checks -/

theorem x64ZeroIdiom_gprSpec_check : GprTarget x64Mach x64Gpr x64Scratch :=
  x64_gprSpec

theorem x64ZeroIdiom_labelClean_check : Rega.LabelClean x64Target.toIsa :=
  x64LabelClean

theorem x64ZeroIdiom_moviDeadFlags_spec_check {h : Host} {k : Nat} {rd : Reg64}
    {c0 : BitVec 64} {s : MachineData} {post : MachineState → Prop} :
    x64Mach.FallsTo x64Gpr.condReads h k (x64MoviDeadFlags rd c0).1 (rd :: x64Scratch) []
      (x64MoviDeadFlags rd c0).2 s
      (fun s' => s'.regs.get64 rd = c0 ∧ s'.dmem = s.dmem) post :=
  x64Gpr_moviDeadFlags_spec

theorem x64ZeroIdiom_flat_eq_check (h : x64Target.toIsa.Hints) (f : TFlatFn)
    (hwf : f.wfCheck = true) :
    compileFlatFn x64Target.toIsa x64LegalTarget h f =
      compileFn x64Target.toIsa x64LegalTarget h f.toFn :=
  compileFlatFn_eq_compileFn x64Target.toIsa x64LegalTarget h f hwf

#print axioms LeanQbe.T.Amd64.x64Gpr_moviDeadFlags_spec
#print axioms LeanQbe.T.Amd64.x64Gpr_moviDeadFlags_noLab
#print axioms LeanQbe.T.Amd64.x64_gprSpec
#print axioms LeanQbe.T.Amd64.x64LabelClean
#print axioms LeanQbe.T.Rega.tryMoviZero_ok
#print axioms LeanQbe.T.Rega.tryMoviZero_clean
#print axioms LeanQbe.T.Rega.execMove_ok
#print axioms LeanQbe.T.Rega.lowerFn_correct
#print axioms LeanQbe.T.compileFlatFn_eq_compileFn
#print axioms x64ZeroIdiom_gprSpec_check
#print axioms x64ZeroIdiom_labelClean_check
#print axioms x64ZeroIdiom_moviDeadFlags_spec_check
#print axioms x64ZeroIdiom_flat_eq_check

open Lean

private def allowedStdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]
private def isForbiddenArmMod (m : Name) : Bool :=
  (m.toString.splitOn "Arm64").length > 1 || m.toString.startsWith "Kraken.AArch64"
private def isForbiddenVllMod (m : Name) : Bool :=
  (m.toString.splitOn "Vll").length > 1

#eval show MetaM Unit from do
  let testBad := (← getEnv).header.moduleNames.filter fun m =>
    isForbiddenArmMod m || isForbiddenVllMod m
  if !testBad.isEmpty then
    throwError "X64ZeroIdiomTest imports Arm64/AArch64/Vll: {testBad.toList}"
  let env ← getEnv
  for nm in [``LeanQbe.T.Amd64.x64Gpr_moviDeadFlags_spec,
      ``LeanQbe.T.Amd64.x64Gpr_moviDeadFlags_noLab,
      ``LeanQbe.T.Amd64.x64_gprSpec, ``LeanQbe.T.Amd64.x64LabelClean,
      ``LeanQbe.T.Rega.tryMoviZero_ok, ``LeanQbe.T.Rega.tryMoviZero_clean,
      ``LeanQbe.T.Rega.execMove_ok, ``LeanQbe.T.Rega.lowerFn_correct,
      ``LeanQbe.T.compileFlatFn_eq_compileFn,
      ``x64ZeroIdiom_gprSpec_check, ``x64ZeroIdiom_labelClean_check,
      ``x64ZeroIdiom_moviDeadFlags_spec_check, ``x64ZeroIdiom_flat_eq_check] do
    let axs ← Lean.collectAxioms nm
    let badAx := axs.filter fun a => !allowedStdAxioms.contains a
    if !badAx.isEmpty then throwError "Disallowed axioms for {nm}: {badAx.toList}"
    let some ci := env.find? nm | throwError "Missing {nm}"
    if ci.isUnsafe then throwError "{nm} is unsafe"

end LeanQbeTest.T.X64ZeroIdiomTest
