module

public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Main
public import LeanQbe.T.MainLemmas
public import LeanQbe.T.RegaLemmas
public import LeanQbeTest.T.RegaTestKit
meta import LeanQbe.T.Amd64.TargLemmas
meta import LeanQbe.T.Main
meta import LeanQbeTest.T.RegaTestKit

/-!
# Multi-Use Load-to-Compare Folding & Zero-Compare Flag Reuse on x64 (`G2-P3.1b`)

End-to-end verified `Spill.hints` + `Rega.lowerFn` (`checkCompile`) tests on `x64Target`
(self-contained x86-64 module; never imports Arm64):

1. Straight-line multi-use `i8` load (`vals[lit]`): `cmp .sge 1` + `cmp .eq 0` folds into a
   single `cmpb $0, [mem]` with shared flags (`jg` + `je`, zero loads, zero `test`, zero `setcc`).
2. Store-separated multi-use `i8` load (`full_propagate_ignore` pattern): intervening store blocks
   memory-operand folding (no stale reload!), while deferred `.sgt 0` flag reuse turns
   `cmpb $1` + `testb` into a single `testb %r, %r; jg; jl`.
3. Multi-use `sext 8 32` and `zext 32 64` over a load: elides both the extension and load into a
   narrow memory-operand `cmp` with flag reuse (`1` `cmp` mem, `0` loads/`movsx`/`movzx`).
4. Multi-use `and 32` + load (`testl $mask, [mem]`) across two arms of a flag-preserving split.
5. Negative soundness tests: aliasing `.call` and non-compare arithmetic use block load elision
   (preserving the heap GPR load and emitting zero non-stack `cmp` mem ops).
6. `#print axioms` audit (`[propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.X64CmpMemMultiUseTest

open LeanQbe.T LeanQbe.T.Amd64 Kraken
open LeanQbeTest.T.RegaTestKit

meta def hintsOf (fs : List Fn) : List x64Target.toIsa.Hints :=
  RegaTestKit.hintsOf x64Target x64LegalTarget fs

meta def chk (fs : List Fn) (exs : List (SigEntry × Nat) := []) : Bool :=
  RegaTestKit.chk x64Target x64Layout x64LegalTarget fs exs

meta def codeOf (fs : List Fn) (exs : List (SigEntry × Nat) := []) : List Directive :=
  RegaTestKit.codeOf x64Target x64LegalTarget fs exs

meta def isNonRspMem {w : Width} : RegOrMem w → Bool
  | .mem { base := some (.reg r), .. } => r != .rsp
  | .mem _ => true
  | _ => false

meta def isHeapMemCmpDir : Directive → Bool
  | .instr (.regular _ _ (.cmp m@(.mem _) _)) => isNonRspMem m
  | .instr (.regular _ _ (.cmp _ (.regOrMem m@(.mem _)))) => isNonRspMem m
  | _ => false

meta def isMemTestDir : Directive → Bool
  | .instr (.regular _ _ (.test m@(.mem _) _)) => isNonRspMem m
  | _ => false

meta def isCmpImmDir : Directive → Bool
  | .instr (.regular _ _ (.cmp _ _)) => true
  | _ => false

meta def isRegTestDir : Directive → Bool
  | .instr (.regular _ _ (.test (.reg _) (.reg _))) => true
  | _ => false

meta def isJccDir : Directive → Bool
  | .instr (.regular _ _ (.jcc _ _)) => true
  | _ => false

meta def isMovzxOrMovsxDir : Directive → Bool
  | .instr (.regular _ _ (.movzx _ _)) => true
  | .instr (.regular _ _ (.movsx _ _)) => true
  | _ => false

meta def isHeapLoadDir : Directive → Bool
  | .instr (.regular _ _ (.mov _ (.regOrMem (.mem { base := some (.reg r), .. })))) => r != .rsp
  | .instr (.regular _ _ (.movzx _ (.mem { base := some (.reg r), .. }))) => r != .rsp
  | .instr (.regular _ _ (.movsx _ (.mem { base := some (.reg r), .. }))) => r != .rsp
  | _ => false

meta def isSetccDir : Directive → Bool
  | .instr (.regular _ _ (.setcc _ _)) => true
  | _ => false

meta def pingSig : SigEntry := ⟨"ping", [i64], [i64]⟩

/-- Multi-use `i8` load feeding `cmp .sge v 1` and `cmp .eq v 0`: folds into 1 `cmpb $0, [mem]`
and reuses flags for `jg` + `je` (`0` heap loads, `0` `setcc`). -/
meta def multiUseI8MemFn : Fn :=
  ⟨"multi_use_i8_mem", [i64, i64], [i64], fun _ _ (p, out, ()) =>
    .load i8 (.var p) fun v =>
    .let_ (op2 (.cmp .sge i8) (.var v) (.imm 1#8)) fun (b1, ()) =>
    .jnz (.var b1)
      (.store (t := i64) (.imm 1#64) (.var out) (.ret (.imm 1#64, ())))
      (.let_ (op2 (.cmp .eq i8) (.var v) (.imm 0#8)) fun (b2, ()) =>
       .jnz (.var b2)
         (.store (t := i64) (.imm 0#64) (.var out) (.ret (.imm 0#64, ())))
         (.ret (.imm 2#64, ())))⟩

#guard chk [multiUseI8MemFn] = true
#guard
  let ds := codeOf [multiUseI8MemFn]
  countDirs isHeapMemCmpDir ds == 1 &&
  countDirs isHeapLoadDir ds == 0 &&
  countDirs isJccDir ds == 2 &&
  countDirs isSetccDir ds == 0

/-- Store-separated multi-use `i8` load (`bv = *p; *q = 7; if (bv > 0) ... if (bv < 0)`):
does NOT elide the load across the store, and reuses `testb %r, %r` flags for `jg` + `jl`. -/
meta def storeSepI8FlagReuseFn : Fn :=
  ⟨"store_sep_i8_flag_reuse", [i64, i64, i64], [i64], fun _ _ (p, q, out, ()) =>
    .load i8 (.var p) fun v =>
    .store (t := i8) (.imm 7#8) (.var q) <|
    .let_ (op2 (.cmp .sge i8) (.var v) (.imm 1#8)) fun (b1, ()) =>
    .jnz (.var b1)
      (.store (t := i64) (.imm 1#64) (.var out) (.ret (.imm 1#64, ())))
      (.let_ (op2 (.cmp .slt i8) (.var v) (.imm 0#8)) fun (b2, ()) =>
       .jnz (.var b2)
         (.store (t := i64) (.imm 2#64) (.var out) (.ret (.imm 2#64, ())))
         (.ret (.imm 0#64, ())))⟩

#guard chk [storeSepI8FlagReuseFn] = true
#guard
  let ds := codeOf [storeSepI8FlagReuseFn]
  countDirs isHeapMemCmpDir ds == 0 &&
  countDirs isHeapLoadDir ds == 1 &&
  countDirs isRegTestDir ds == 1 &&
  countDirs isCmpImmDir ds == 0 &&
  countDirs isJccDir ds == 2 &&
  countDirs isSetccDir ds == 0

/-- Multi-use `sext 8 32` over `i8` load feeding `cmp .sge i32 1` and `cmp .slt i32 0`:
elides both `sext` and `load` into `cmpb $0, [mem]` + flag reuse. -/
meta def multiUseSextI8Fn : Fn :=
  ⟨"multi_use_sext_i8", [i64, i64], [i64], fun _ _ (p, out, ()) =>
    .load i8 (.var p) fun v =>
    .let_ (op1 (.sext 8 32) (.var v)) fun (vx, ()) =>
    .let_ (op2 (.cmp .sge i32) (.var vx) (.imm 1#32)) fun (b1, ()) =>
    .jnz (.var b1)
      (.store (t := i64) (.imm 1#64) (.var out) (.ret (.imm 1#64, ())))
      (.let_ (op2 (.cmp .slt i32) (.var vx) (.imm 0#32)) fun (b2, ()) =>
       .jnz (.var b2)
         (.store (t := i64) (.imm 2#64) (.var out) (.ret (.imm 2#64, ())))
         (.ret (.imm 0#64, ())))⟩

#guard chk [multiUseSextI8Fn] = true
#guard
  let ds := codeOf [multiUseSextI8Fn]
  countDirs isHeapMemCmpDir ds == 1 &&
  countDirs isMovzxOrMovsxDir ds == 0 &&
  countDirs isHeapLoadDir ds == 0 &&
  countDirs isJccDir ds == 2 &&
  countDirs isSetccDir ds == 0

/-- Multi-use `zext 32 64` over `i32` load feeding `cmp .ugt i64 0` and `cmp .eq i64 5`:
elides both `zext` and `load` into two narrow memory-operand `cmpl`s. -/
meta def multiUseZextI32Fn : Fn :=
  ⟨"multi_use_zext_i32", [i64], [i64], fun _ _ (p, ()) =>
    .load i32 (.var p) fun v =>
    .let_ (op1 (.zext 32 64) (.var v)) fun (vx, ()) =>
    .let_ (op2 (.cmp .ugt i64) (.var vx) (.imm 0#64)) fun (b1, ()) =>
    .jnz (.var b1)
      (.let_ (op2 (.cmp .eq i64) (.var vx) (.imm 5#64)) fun (b2, ()) =>
       .jnz (.var b2) (.ret (.imm 1#64, ())) (.ret (.imm 2#64, ())))
      (.ret (.imm 0#64, ()))⟩

#guard chk [multiUseZextI32Fn] = true
#guard
  let ds := codeOf [multiUseZextI32Fn]
  countDirs isHeapMemCmpDir ds == 2 &&
  countDirs isHeapLoadDir ds == 0

/-- Multi-use `and i32` over `i32` load feeding `== 0` in both arms of an unrelated branch:
elides both `and` and `load` into `testl $mask, [mem]` at both sites. -/
meta def multiUseAndTestMemFn : Fn :=
  ⟨"multi_use_and_test_mem", [i64, i64], [i64], fun _ _ (cond, p, ()) =>
    .load i32 (.var p) fun v =>
    .let_ (op2 (.and i32) (.var v) (.imm 6#32)) fun (m, ()) =>
    .let_ (op2 (.cmp .ne i64) (.var cond) (.imm 0#64)) fun (bc, ()) =>
    .jnz (.var bc)
      (.let_ (op2 (.cmp .eq i32) (.var m) (.imm 0#32)) fun (b1, ()) =>
       .jnz (.var b1) (.ret (.imm 1#64, ())) (.ret (.imm 2#64, ())))
      (.let_ (op2 (.cmp .ne i32) (.var m) (.imm 0#32)) fun (b2, ()) =>
       .jnz (.var b2) (.ret (.imm 3#64, ())) (.ret (.imm 4#64, ())))⟩

#guard chk [multiUseAndTestMemFn] = true
#guard
  let ds := codeOf [multiUseAndTestMemFn]
  countDirs isMemTestDir ds == 2 && countDirs isHeapLoadDir ds == 0

/-- Negative tests: aliasing `.call` or non-compare use (`add`) must NOT elide the load. -/
meta def negCallBarriersLoadFn : Fn :=
  ⟨"neg_call_barriers", [i64], [i64], fun _ _ (p, ()) =>
    .load i8 (.var p) fun v =>
    .call "ping" (as := [i64]) (bs := [i64]) (.var p, ()) fun (_r, ()) =>
    .let_ (op2 (.cmp .sge i8) (.var v) (.imm 1#8)) fun (b1, ()) =>
    .jnz (.var b1) (.ret (.imm 1#64, ())) (.ret (.imm 0#64, ()))⟩

meta def negArithUseLoadFn : Fn :=
  ⟨"neg_arith_use", [i64], [i64], fun _ _ (p, ()) =>
    .load i8 (.var p) fun v =>
    .let_ (op2 (.cmp .sge i8) (.var v) (.imm 1#8)) fun (b1, ()) =>
    .jnz (.var b1)
      (.let_ (op2 (.add i8) (.var v) (.imm 1#8)) fun (s, ()) =>
       .let_ (op1 (.zext 8 64) (.var s)) fun (r, ()) => .ret (.var r, ()))
      (.ret (.imm 0#64, ()))⟩

#guard chk [negCallBarriersLoadFn] [(pingSig, 0)] = true
#guard
  let ds := codeOf [negCallBarriersLoadFn] [(pingSig, 0)]
  countDirs isHeapMemCmpDir ds == 0 && countDirs isHeapLoadDir ds == 1

#guard chk [negArithUseLoadFn] = true
#guard
  let ds := codeOf [negArithUseLoadFn]
  countDirs isHeapMemCmpDir ds == 0 && countDirs isHeapLoadDir ds == 1

/-- Verified compilation soundness theorem backed directly by `Rega.lowerFn_correct`. -/
theorem x64_cmp_mem_lowerFn_correct
    (host : x64Target.mach.Host) (hints : x64Target.toIsa.Hints) (E : Rega.Ext) (f : Fn)
    (Γ : Env) (n nX : Nat) (bound : Sym → Nat) {code : List Directive} {k₀ : Nat}
    (hwf : f.Wf) (hl : Rega.lowerFn x64Target.toIsa hints E f = .ok code)
    (hc : code.IsInfixAt (x64Target.mach.prog host) k₀) (hu : x64Target.LabelsUnique host)
    (hfr : Rega.effFrame x64Target.toIsa hints E ≤ n) (hn : n + x64Target.frame.raBytes ≤ 2 ^ 64)
    (hcal : ∀ g as bs, (g, as, bs) ∈ E.callees →
      x64Target.FnSpec host g (Γ g as bs) (bound g) nX ∧
        Rega.effFrame x64Target.toIsa hints E + x64Target.frame.raBytes + bound g ≤ n)
    (hex : ∀ g, g ∈ E.exits → x64Target.Defined host g ∧ nX ≤ n) :
    x64Target.FnSpec host f.name (Func.spec Γ f.body) n nX :=
  Rega.lowerFn_correct x64Target host hints E f Γ n nX bound hwf hl hc hu hfr hn hcal hex

#print axioms x64_cmp_mem_lowerFn_correct

end LeanQbeTest.T.X64CmpMemMultiUseTest
