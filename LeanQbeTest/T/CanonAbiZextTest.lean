module

public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Amd64.IselLemmas1
public import LeanQbe.T.Amd64.IselLemmas5
public import LeanQbe.T.RegaLemmas2
public import LeanQbe.T.RegaLemmas4
public import LeanQbe.T.Spill
meta import LeanQbe.T.Amd64.TargLemmas
meta import LeanQbe.T.Spill

/-!
# `canonAbi` Elision, Canonical Zero-Extension Tracking, and `load + sext` Fusion

Regression tests on `x64Target` (a `Kraken.X64` instance; every check compiles through the
verified `Rega.lowerFn` via `checkCompile`) for:

1. `canonAbi` elision (`Rega.abiSkips`): a `ret true` materialized as `movl $1, %eax` needs no
   `movzbl %al, %eax`; an `i32` loaded by `movl (%rdi), %e..` and passed to / returned from a call
   needs no `movl %eX, %eX`.
2. Canonical (`AbiGprHolds`) `.gprZ` tracking of every x64 scalar load (`GprIsa.zeroExtLoad`):
   `zext 8 64 (load i8 p)` emits no register `movzx`.
3. `load (.bits m) + sext m n` fusion (`Rega.loadSextNext` + `Rega.tryLoadSext` +
   `GprIsa.loadSext`): one `movs{b,w,l}q (%rdi), %r..` and no register `movsx`.
4. Axiom audit (`#print axioms`) confirming only `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.CanonAbiZextTest

open LeanQbe.T LeanQbe.T.Amd64

/-! ## Helpers -/

/-- Hints from the default heuristics (`Fn.computeHints` = `Spill.hints ∘ Fn.mid`). -/
meta def hintsOf (fs : List Fn) : List x64Target.toIsa.Hints :=
  fs.map (Fn.computeHints x64Target.toIsa x64LegalTarget)

/-- End-to-end verified compilation check (lowering, labels, stack bounds). -/
meta def chk (fs : List Fn) : Bool :=
  checkCompile x64Target x64Layout x64LegalTarget [] [] 0 fs (hintsOf fs) 2048

/-- Emitted code of a module (empty on a compile error). -/
meta def codeOf (fs : List Fn) : List x64Target.toIsa.Directive :=
  extractCode (compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes [] [] 0 fs
    (hintsOf fs))

/-- `movl %eX, %eX` (32-bit self move: the x64 `canonAbi i32` / `zext 32 64` idiom). -/
meta def isSelfMov32 : Directive → Bool
  | .instr (.regular _ .W32 (.mov (.reg (.low a .W32)) (.regOrMem (.reg (.low b .W32))))) => a == b
  | _ => false

/-- Register-source `movzx` (`movzbl %al, %eax`, the `canonAbi bool/i8` idiom). -/
meta def isMovzxReg : Directive → Bool
  | .instr (.regular _ _ (.movzx _ (.reg _))) => true
  | _ => false

/-- Register-source `movsx`. -/
meta def isMovsxReg : Directive → Bool
  | .instr (.regular _ _ (.movsx _ (.reg _))) => true
  | _ => false

/-- Memory-source `movsx` (`movs{b,w,l}q (addr), %r..`). -/
meta def isMovsxMem : Directive → Bool
  | .instr (.regular _ _ (.movsx _ (.mem _))) => true
  | _ => false

meta def countDirs (p : Directive → Bool) (ds : List Directive) : Nat := (ds.filter p).length

#guard isSelfMov32 (ins32 (.mov (.reg (d .rcx)) (.regOrMem (.reg (d .rcx)))))
#guard !isSelfMov32 (ins32 (.mov (.reg (d .rcx)) (.regOrMem (.reg (d .rdx)))))
#guard isMovzxReg (ins32 (.movzx (.reg (d .rax)) (.reg (b8 .rax))))
#guard isMovsxReg (ins (.movsx (.reg (q .rax)) (.reg (b8 .rax))))
meta def movsxMem8 : Directive :=
  ins (.movsx (.reg (q .rax)) (.mem { base := none, idx := none } : RegOrMem .W8))

#guard !isMovsxReg movsxMem8 && isMovsxMem movsxMem8

/-! ## 1. `canonAbi` elision -/

/-- `ret true`: `movl $1, %eax` is already the canonical ABI `bool`. -/
meta def retTrueFn : Fn :=
  ⟨"retTrue", [i64], [.bool], fun _ _ (_, ()) => .ret (.imm true, ())⟩

/-- `ret (x : i8)` of a narrow `i8` immediate (`movl $200, %eax`, no `movzbl`). -/
meta def retImm8Fn : Fn :=
  ⟨"retImm8", [i64], [i8], fun _ _ (_, ()) => .ret (.imm 200, ())⟩

/-- Identity on `i32`: the incoming ABI argument is already canonical (`.gprZ` binding). -/
meta def g32Fn : Fn :=
  ⟨"g32", [i32], [i32], fun _ _ (x, ()) => .ret (.var x, ())⟩

/-- `g32 (load i32 p)`: the loaded argument and the returned call result are canonical. -/
meta def callLoadFn : Fn :=
  ⟨"callLoad", [i64], [i32], fun _ _ (p, ()) =>
    .load i32 (.var p) fun x =>
    .call "g32" (as := [i32]) (bs := [i32]) (.var x, ()) fun (r, ()) => .ret (.var r, ())⟩

#guard chk [retTrueFn] && chk [retImm8Fn] && chk [g32Fn, callLoadFn]
#guard countDirs isMovzxReg (codeOf [retTrueFn]) == 0
#guard countDirs isMovzxReg (codeOf [retImm8Fn]) == 0
#guard countDirs isSelfMov32 (codeOf [g32Fn, callLoadFn]) == 0

/-! ## 2. Canonical narrow loads: `zext 8 64 (load i8 p)` -/

meta def zextLoadFn : Fn :=
  ⟨"zextLoad", [i64], [i64], fun _ _ (p, ()) =>
    .load i8 (.var p) fun x =>
    .let_ (op1 (.zext 8 64) (.var x)) fun (y, ()) => .ret (.var y, ())⟩

/-- `i16` load returned as `i16`: no `movzwl %ax, %eax` before `ret`. -/
meta def retLoad16Fn : Fn :=
  ⟨"retLoad16", [i64], [i16], fun _ _ (p, ()) =>
    .load i16 (.var p) fun x => .ret (.var x, ())⟩

#guard chk [zextLoadFn] && chk [retLoad16Fn]
#guard countDirs isMovzxReg (codeOf [zextLoadFn]) == 0
#guard countDirs isMovzxReg (codeOf [retLoad16Fn]) == 0

/-! ## 3. `load + sext` fusion -/

meta def sextLoadFn (m : Nat) : Fn :=
  ⟨"sextLoad", [i64], [i64], fun _ _ (p, ()) =>
    .load (.bits m) (.var p) fun x =>
    .let_ (op1 (.sext m 64) (.var x)) fun (y, ()) => .ret (.var y, ())⟩

#guard [8, 16, 32].all fun m => chk [sextLoadFn m]
#guard [8, 16, 32].all fun m => countDirs isMovsxMem (codeOf [sextLoadFn m]) == 1
#guard [8, 16, 32].all fun m => countDirs isMovsxReg (codeOf [sextLoadFn m]) == 0

/-! ## 4. Axiom audit -/

#print axioms LeanQbe.T.Rega.lowerFn_correct
#print axioms LeanQbe.T.Rega.abiHeld_ok
#print axioms LeanQbe.T.Rega.skipOk_of_abiSkips
#print axioms LeanQbe.T.Amd64.x64Gpr_load_zext
#print axioms LeanQbe.T.Amd64.x64Gpr_loadSext_spec
#print axioms LeanQbe.T.Amd64.x64GprSpec
#print axioms LeanQbe.T.Amd64.x64LabelClean

end LeanQbeTest.T.CanonAbiZextTest
