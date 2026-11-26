module

public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Amd64.IselLemmas5
public import LeanQbe.T.RegaLemmasCmpReuse
public import LeanQbe.T.RegaLemmas3b
public import LeanQbe.T.RegaLemmas4
public import LeanQbe.T.Spill
meta import LeanQbe.T.Amd64.TargLemmas
meta import LeanQbe.T.Spill

/-!
# Three-Way Sign-Check Flag Reuse (`C-P1.3`) Tests

Verifies end-to-end x86-64 compilation (`checkCompile` + `compileModule`) and direct
`Spill.hints` + `Rega.lowerFn` lowering for 3-way sign checks (`x > 0` / `x < 0` / `x == 0`):
1. `i64`, `i32`, and `i8` 3-way sign checks (branching `.jnz` via side-effecting arms and
   `ifOpt`-lowered `select` forms, both `x > 0` first and `x < 0` first) emit a single
   `test`/`cmp $0` and reuse flags (`0` `cmp`, `0` `setcc` in branching forms).
2. Zero materialization (`copy 0`) between the two branches keeps `deadFlags == false` and never
   emits `xor` clobbering live sign flags between the first flag-setter and second `jcc`.
3. Asymmetric narrow/wide `sext` (`32→64`, `8→64`) and `zext` (`8→64`, `32→64`) pairs reuse flags
   via `reuseCmpPair?` and `cmpZeroFlagCond?`.
4. Axiom audit (`#print axioms`) on `reuseCmpPair_ok`, `cmpZeroFlagCond_ok`, `tryReuseFlagCmp_ok`,
   and `lowerFn_correct`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.SignCheckFlagTest

open LeanQbe.T LeanQbe.T.Amd64

/-! ## Helpers -/

meta def hintsOf (fs : List Fn) : List x64Target.toIsa.Hints :=
  fs.map (Fn.computeHints x64Target.toIsa x64LegalTarget)

meta def chk (fs : List Fn) : Bool :=
  checkCompile x64Target x64Layout x64LegalTarget [] [] 0 fs (hintsOf fs) 2048

meta def codeOf (fs : List Fn) : List x64Target.toIsa.Directive :=
  extractCode
    (compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes [] [] 0 fs (hintsOf fs))

meta def regaCodeOf (f : Fn) : List x64Target.toIsa.Directive :=
  let h := Spill.hints x64Target.toIsa f
  match Rega.lowerFn x64Target.toIsa h f.ext f with
  | .ok ds => ds
  | .error _ => []

meta def countDirs (p : Directive → Bool) (ds : List Directive) : Nat :=
  (ds.filter p).length

meta def isTestDir : Directive → Bool
  | .instr (.regular _ _ (.test _ _)) => true
  | _ => false

meta def isCmpDir : Directive → Bool
  | .instr (.regular _ _ (.cmp _ _)) => true
  | _ => false

meta def isJccDir : Directive → Bool
  | .instr (.regular _ _ (.jcc _ _)) => true
  | _ => false

meta def isSetccDir : Directive → Bool
  | .instr (.regular _ _ (.setcc _ _)) => true
  | _ => false

meta def isXorDir : Directive → Bool
  | .instr (.regular _ _ (.xor _ _)) => true
  | _ => false

meta def isMoviZeroDir : Directive → Bool
  | .instr (.regular _ .W32 (.mov (.reg _) (.imm (.int64 ⟨0⟩)))) => true
  | .instr (.regular _ .W64 (.mov (.reg _) (.imm (.int64 ⟨0⟩)))) => true
  | _ => false

/-- Check `xor` count between the first `test`/`cmp` and the `k`-th `jcc` (`0`-indexed). -/
meta def xorBeforeJcc (k : Nat) (ds : List Directive) : Nat :=
  let afterFlag := ds.dropWhile (fun d => !isTestDir d && !isCmpDir d)
  let rec go (seenJcc : Nat) (acc : Nat) : List Directive → Nat
    | [] => acc
    | d :: rest =>
      if isJccDir d then
        if seenJcc >= k then acc else go (seenJcc + 1) acc rest
      else
        go seenJcc (if isXorDir d then acc + 1 else acc) rest
  go 0 0 afterFlag

/-! ## 1. End-to-End `i64`, `i32`, and `i8` 3-Way Sign Checks -/

meta def sign3BranchI64Fn : Fn :=
  ⟨"sign3BranchI64", [i64, i64, i64, i64, i64], [i64], fun _ _ (x, p, a, b, c, ()) =>
    .let_ (op2 (.cmp .sgt i64) (.var x) (.imm 0#64)) fun (c1, ()) =>
    .jnz (.var c1) (.store (t := i64) (.imm 1#64) (.var p) (.ret (.var a, ())))
      (.let_ (op2 (.cmp .slt i64) (.var x) (.imm 0#64)) fun (c2, ()) =>
        .jnz (.var c2) (.store (t := i64) (.imm (-1#64)) (.var p) (.ret (.var b, ())))
          (.ret (.var c, ())))⟩

meta def sign3BranchI64RevFn : Fn :=
  ⟨"sign3BranchI64Rev", [i64, i64, i64, i64, i64], [i64], fun _ _ (x, p, a, b, c, ()) =>
    .let_ (op2 (.cmp .slt i64) (.var x) (.imm 0#64)) fun (c1, ()) =>
    .jnz (.var c1) (.store (t := i64) (.imm (-1#64)) (.var p) (.ret (.var b, ())))
      (.let_ (op2 (.cmp .sgt i64) (.var x) (.imm 0#64)) fun (c2, ()) =>
        .jnz (.var c2) (.store (t := i64) (.imm 1#64) (.var p) (.ret (.var a, ())))
          (.ret (.var c, ())))⟩

meta def sign3BranchI32Fn : Fn :=
  ⟨"sign3BranchI32", [i32, i64, i64, i64, i64], [i64], fun _ _ (x, p, a, b, c, ()) =>
    .let_ (op2 (.cmp .sgt i32) (.var x) (.imm 0#32)) fun (c1, ()) =>
    .jnz (.var c1) (.store (t := i64) (.imm 1#64) (.var p) (.ret (.var a, ())))
      (.let_ (op2 (.cmp .slt i32) (.var x) (.imm 0#32)) fun (c2, ()) =>
        .jnz (.var c2) (.store (t := i64) (.imm (-1#64)) (.var p) (.ret (.var b, ())))
          (.ret (.var c, ())))⟩

meta def sign3BranchI8Fn : Fn :=
  ⟨"sign3BranchI8", [i8, i64, i64, i64, i64], [i64], fun _ _ (x, p, a, b, c, ()) =>
    .let_ (op2 (.cmp .sgt i8) (.var x) (.imm 0#8)) fun (c1, ()) =>
    .jnz (.var c1) (.store (t := i64) (.imm 1#64) (.var p) (.ret (.var a, ())))
      (.let_ (op2 (.cmp .slt i8) (.var x) (.imm 0#8)) fun (c2, ()) =>
        .jnz (.var c2) (.store (t := i64) (.imm (-1#64)) (.var p) (.ret (.var b, ())))
          (.ret (.var c, ())))⟩

meta def sign3I64Fn : Fn :=
  ⟨"sign3I64", [i64], [i64], fun _ _ (x, ()) =>
    .let_ (op2 (.cmp .sgt i64) (.var x) (.imm 0#64)) fun (c1, ()) =>
    .jnz (.var c1) (.ret (.imm 1#64, ()))
      (.let_ (op2 (.cmp .slt i64) (.var x) (.imm 0#64)) fun (c2, ()) =>
        .jnz (.var c2) (.ret (.imm (-1#64), ())) (.ret (.imm 0#64, ())))⟩

meta def sign3I64RevFn : Fn :=
  ⟨"sign3I64Rev", [i64], [i64], fun _ _ (x, ()) =>
    .let_ (op2 (.cmp .slt i64) (.var x) (.imm 0#64)) fun (c1, ()) =>
    .jnz (.var c1) (.ret (.imm (-1#64), ()))
      (.let_ (op2 (.cmp .sgt i64) (.var x) (.imm 0#64)) fun (c2, ()) =>
        .jnz (.var c2) (.ret (.imm 1#64, ())) (.ret (.imm 0#64, ())))⟩

meta def sign3I32Fn : Fn :=
  ⟨"sign3I32", [i32], [i64], fun _ _ (x, ()) =>
    .let_ (op2 (.cmp .sgt i32) (.var x) (.imm 0#32)) fun (c1, ()) =>
    .jnz (.var c1) (.ret (.imm 1#64, ()))
      (.let_ (op2 (.cmp .slt i32) (.var x) (.imm 0#32)) fun (c2, ()) =>
        .jnz (.var c2) (.ret (.imm (-1#64), ())) (.ret (.imm 0#64, ())))⟩

meta def sign3I8Fn : Fn :=
  ⟨"sign3I8", [i8], [i64], fun _ _ (x, ()) =>
    .let_ (op2 (.cmp .sgt i8) (.var x) (.imm 0#8)) fun (c1, ()) =>
    .jnz (.var c1) (.ret (.imm 1#64, ()))
      (.let_ (op2 (.cmp .slt i8) (.var x) (.imm 0#8)) fun (c2, ()) =>
        .jnz (.var c2) (.ret (.imm (-1#64), ())) (.ret (.imm 0#64, ())))⟩

meta def sign3SelectI64Fn : Fn :=
  ⟨"sign3SelectI64", [i64, i64, i64, i64], [i64], fun _ _ (x, a, b, c, ()) =>
    .let_ (op2 (.cmp .sgt i64) (.var x) (.imm 0#64)) fun (c1, ()) =>
    .let_ (op2 (.cmp .slt i64) (.var x) (.imm 0#64)) fun (c2, ()) =>
    .let_ (op3 (.select i64) (.var c2) (.var b) (.var c)) fun (r1, ()) =>
    .let_ (op3 (.select i64) (.var c1) (.var a) (.var r1)) fun (r, ()) =>
    .ret (.var r, ())⟩

#guard
  [ sign3BranchI64Fn, sign3BranchI64RevFn, sign3BranchI32Fn, sign3BranchI8Fn ].all fun f =>
    let ds := codeOf [f]
    chk [f] &&
    countDirs isTestDir ds == 1 &&
    countDirs isCmpDir ds == 0 &&
    countDirs isJccDir ds == 2 &&
    countDirs isSetccDir ds == 0 &&
    xorBeforeJcc 1 ds == 0

#guard
  [ sign3I64Fn, sign3I64RevFn, sign3I32Fn, sign3I8Fn, sign3SelectI64Fn ].all fun f =>
    let ds := codeOf [f]
    chk [f] &&
    countDirs isTestDir ds == 1 &&
    countDirs isCmpDir ds == 0 &&
    countDirs isXorDir ds == 0

/-! ## 2. Live Flag Preservation Across Intervening `copy 0` (`deadFlags == false`) -/

/-- Post-`normBitsCmpImm` form `x >=s 1` followed by an intervening `z := copy 0` (live in both
arms of `c2`) before `c2 := x <s 0`: must keep `deadFlags == false`, use `mov $0` instead of `xor`
between the two branches, and still emit only 1 `test` and 0 `cmp`. -/
meta def sign3ZeroBetweenFn : Fn :=
  ⟨"sign3ZeroBetween", [i64, i64, i64, i64], [i64], fun _ _ (x, p, a, b, ()) =>
    .let_ (op2 (.cmp .sge i64) (.var x) (.imm 1#64)) fun (c1, ()) =>
    .jnz (.var c1) (.ret (.var a, ()))
      (.let_ (op1 (.copy i64) (.imm 0#64)) fun (z, ()) =>
        .let_ (op2 (.cmp .slt i64) (.var x) (.imm 0#64)) fun (c2, ()) =>
        .jnz (.var c2)
          (.store (t := i64) (.var z) (.var p) (.ret (.var b, ())))
          (.ret (.var z, ())))⟩

#guard
  let ds := regaCodeOf sign3ZeroBetweenFn
  countDirs isTestDir ds == 1 &&
  countDirs isCmpDir ds == 0 &&
  countDirs isJccDir ds == 2 &&
  countDirs isSetccDir ds == 0 &&
  xorBeforeJcc 1 ds == 0 &&
  countDirs isMoviZeroDir ds >= 1

/-! ## 3. Narrow/Wide `sext` and `zext` Symmetry (`reuseCmpPair?` + `cmpZeroFlagCond?`) -/

meta def sign3Sext32EndToEndFn : Fn :=
  ⟨"sign3Sext32E2E", [i32, i64, i64, i64, i64], [i64], fun _ _ (x, p, a, b, c, ()) =>
    .let_ (op1 (.sext 32 64) (.var x)) fun (y, ()) =>
    .let_ (op2 (.cmp .sgt i64) (.var y) (.imm 0#64)) fun (c1, ()) =>
    .jnz (.var c1) (.store (t := i64) (.var y) (.var p) (.ret (.var a, ())))
      (.let_ (op2 (.cmp .slt i32) (.var x) (.imm 0#32)) fun (c2, ()) =>
        .jnz (.var c2) (.store (t := i64) (.imm (-1#64)) (.var p) (.ret (.var b, ())))
          (.ret (.var c, ())))⟩

meta def sext32WideThenNarrowFn : Fn :=
  ⟨"sext32WideThenNarrow", [i32, i64, i64, i64], [i64], fun _ _ (x, a, b, c, ()) =>
    .let_ (op1 (.sext 32 64) (.var x)) fun (y, ()) =>
    .let_ (op2 (.cmp .sge i64) (.var y) (.imm 1#64)) fun (c1, ()) =>
    .jnz (.var c1) (.ret (.var a, ()))
      (.let_ (op2 (.cmp .slt i32) (.var x) (.imm 0#32)) fun (c2, ()) =>
        .jnz (.var c2) (.ret (.var b, ())) (.ret (.var c, ())))⟩

meta def sext32NarrowThenWideFn : Fn :=
  ⟨"sext32NarrowThenWide", [i32, i64, i64, i64], [i64], fun _ _ (x, a, b, c, ()) =>
    .let_ (op1 (.sext 32 64) (.var x)) fun (y, ()) =>
    .let_ (op2 (.cmp .sge i32) (.var x) (.imm 1#32)) fun (c1, ()) =>
    .jnz (.var c1) (.ret (.var a, ()))
      (.let_ (op2 (.cmp .slt i64) (.var y) (.imm 0#64)) fun (c2, ()) =>
        .jnz (.var c2) (.ret (.var b, ())) (.ret (.var c, ())))⟩

meta def sext8WideThenNarrowFn : Fn :=
  ⟨"sext8WideThenNarrow", [i8, i64, i64, i64], [i64], fun _ _ (x, a, b, c, ()) =>
    .let_ (op1 (.sext 8 64) (.var x)) fun (y, ()) =>
    .let_ (op2 (.cmp .sge i64) (.var y) (.imm 1#64)) fun (c1, ()) =>
    .jnz (.var c1) (.ret (.var a, ()))
      (.let_ (op2 (.cmp .slt i8) (.var x) (.imm 0#8)) fun (c2, ()) =>
        .jnz (.var c2) (.ret (.var b, ())) (.ret (.var c, ())))⟩

meta def sext8NarrowThenWideFn : Fn :=
  ⟨"sext8NarrowThenWide", [i8, i64, i64, i64], [i64], fun _ _ (x, a, b, c, ()) =>
    .let_ (op1 (.sext 8 64) (.var x)) fun (y, ()) =>
    .let_ (op2 (.cmp .sge i8) (.var x) (.imm 1#8)) fun (c1, ()) =>
    .jnz (.var c1) (.ret (.var a, ()))
      (.let_ (op2 (.cmp .slt i64) (.var y) (.imm 0#64)) fun (c2, ()) =>
        .jnz (.var c2) (.ret (.var b, ())) (.ret (.var c, ())))⟩

meta def zext8WideThenNarrowFn : Fn :=
  ⟨"zext8WideThenNarrow", [i8, i64, i64, i64], [i64], fun _ _ (x, a, b, c, ()) =>
    .let_ (op1 (.zext 8 64) (.var x)) fun (y, ()) =>
    .let_ (op2 (.cmp .uge i64) (.var y) (.imm 1#64)) fun (c1, ()) =>
    .jnz (.var c1) (.ret (.var a, ()))
      (.let_ (op2 (.cmp .eq i8) (.var x) (.imm 0#8)) fun (c2, ()) =>
        .jnz (.var c2) (.ret (.var b, ())) (.ret (.var c, ())))⟩

meta def zext32NarrowThenWideFn : Fn :=
  ⟨"zext32NarrowThenWide", [i32, i64, i64, i64], [i64], fun _ _ (x, a, b, c, ()) =>
    .let_ (op1 (.zext 32 64) (.var x)) fun (y, ()) =>
    .let_ (op2 (.cmp .uge i32) (.var x) (.imm 1#32)) fun (c1, ()) =>
    .jnz (.var c1) (.ret (.var a, ()))
      (.let_ (op2 (.cmp .eq i64) (.var y) (.imm 0#64)) fun (c2, ()) =>
        .jnz (.var c2) (.ret (.var b, ())) (.ret (.var c, ())))⟩

#guard chk [sign3Sext32EndToEndFn]
#guard countDirs isTestDir (codeOf [sign3Sext32EndToEndFn]) == 1
#guard countDirs isCmpDir (codeOf [sign3Sext32EndToEndFn]) == 0
#guard countDirs isJccDir (codeOf [sign3Sext32EndToEndFn]) == 2
#guard countDirs isSetccDir (codeOf [sign3Sext32EndToEndFn]) == 0

#guard
  [ sext32WideThenNarrowFn, sext32NarrowThenWideFn,
    sext8WideThenNarrowFn, sext8NarrowThenWideFn,
    zext8WideThenNarrowFn, zext32NarrowThenWideFn ].all fun f =>
    let ds := regaCodeOf f
    countDirs isTestDir ds == 1 && countDirs isCmpDir ds == 0 &&
    countDirs isJccDir ds == 2 && countDirs isSetccDir ds == 0 &&
    xorBeforeJcc 1 ds == 0

/-! ## 4. Standard-Axiom Audit -/

#print axioms LeanQbe.T.Rega.reuseCmpPair_ok
#print axioms LeanQbe.T.Rega.cmpZeroFlagCond_ok
#print axioms LeanQbe.T.Rega.tryReuseFlagCmp_ok
#print axioms LeanQbe.T.Rega.lowerFn_correct

end LeanQbeTest.T.SignCheckFlagTest
