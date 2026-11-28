module

import LeanQbe.T.IfOptLemmas
import LeanQbe.T.OptFlatCfgLemmas
import LeanQbe.T.MainFlat
import LeanQbe.T.Arm64.Targ
import Kraken.AArch64.Print
meta import LeanQbe.T.IfOpt
meta import LeanQbe.T.OptFlatCfg
meta import LeanQbe.T.Main
meta import LeanQbe.T.MainFlat
meta import LeanQbe.T.Arm64.Targ
meta import Kraken.AArch64.Print

/-!
# Arm64 Codegen Verification for Store-Sinking RMW Diamond (`IfOptStoreSinkArm64Test`)

AArch64 companion to `IfOptStoreSinkTest` (separate module per `lakefile.toml` `LeanQbeTest`
requirement because `Kraken.X64.Syntax` and `Kraken.AArch64.Syntax` cannot be co-imported):
verifies `csel`, zero conditional branches, and byte-exact `compileFn`/`compileFlatFn` parity on
`Arm64.armTarget` for `full_m6_sweep_sim`-shaped RMW diamonds, pure-store diamonds, and negative
guards.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.IfOptStoreSinkArm64Test

open LeanQbe.T

/-- `full_m6_sweep_sim`-shaped RMW diamond for Arm64 codegen check. -/
def rmwDiaArm : Func [i32, i64, i32, i64] [i64] :=
  fun _ _ (flag, sig, gv, mask, ()) =>
  .let_ (op2 (.cmp .eq i32) (.var flag) (.imm 1#32)) fun (cond, ()) =>
  .jnz (.var cond)
    (.let_ (op1 (.zext 32 64) (.var gv)) fun (gv64, ()) =>
     .let_ (op2 (.shl i64) (.var gv64) (.imm 3#64)) fun (off, ()) =>
     .let_ (op2 (.add i64) (.var sig) (.var off)) fun (addr, ()) =>
     .load i64 (.var addr) fun old =>
     .let_ (op2 (.or i64) (.var old) (.var mask)) fun (nv, ()) =>
     .store (.var nv) (.var addr) <|
     .ret (.imm 1#64, ()))
    (.let_ (op1 (.zext 32 64) (.var gv)) fun (gv64, ()) =>
     .let_ (op2 (.shl i64) (.var gv64) (.imm 3#64)) fun (off, ()) =>
     .let_ (op2 (.add i64) (.var sig) (.var off)) fun (addr, ()) =>
     .load i64 (.var addr) fun old =>
     .let_ (op1 (.not i64) (.var mask)) fun (nmask, ()) =>
     .let_ (op2 (.and i64) (.var old) (.var nmask)) fun (nv, ()) =>
     .store (.var nv) (.var addr) <|
     .ret (.imm 0#64, ()))

/-- Pure identical-address store diamond inside 1-block `.group` for Arm64 codegen check. -/
def pureStoreGroupDiaArm : Func [i32, i64, i64, i64] [i64] :=
  fun _ _ (flag, addr, x, y, ()) =>
  .let_ (op2 (.cmp .eq i32) (.var flag) (.imm 1#32)) fun (c, ()) =>
  .group (sig := [[i64]])
    (fun _ => .cons (fun (r, ()) => .ret (.var r, ())) .nil)
    (fun (J, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.add i64) (.var x) (.imm 5#64)) fun (a, ()) =>
         .store (.var a) (.var addr) <|
         .jump J (.var a, ()))
        (.let_ (op2 (.sub i64) (.var y) (.imm 3#64)) fun (b, ()) =>
         .store (.var b) (.var addr) <|
         .jump J (.var b, ())))

/-- Negative guard fixture (`addr1 ≠ addr2`) must preserve conditional branch on Arm64. -/
def negMismatchAddrArm : Func [i32, i64, i64, i64] [i64] :=
  fun _ _ (flag, a1, a2, v, ()) =>
  .let_ (op2 (.cmp .eq i32) (.var flag) (.imm 1#32)) fun (c, ()) =>
  .jnz (.var c)
    (.store (.var v) (.var a1) <| .ret (.imm 1#64, ()))
    (.store (.var v) (.var a2) <| .ret (.imm 0#64, ()))

theorem rmwDiaArm_flat_parity :
    OptFlatCfg.ifOptFlat true [i32, i64, i32, i64] (reifyFunc rmwDiaArm) =
      reifyFunc (Func.ifOptBits rmwDiaArm) :=
  OptFlatCfg.ifOptFlat_true_eq (reifyFunc rmwDiaArm)
    (PassFlatKit.reifyFunc_wfCheck (Func.wf_of_denote (reifyFunc rmwDiaArm) rfl))

/-- Substring check helper. -/
meta def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

#eval show IO Unit from do
  let rmwFn : Fn := ⟨"rmw_dia", [i32, i64, i32, i64], [i64], rmwDiaArm⟩
  let pureFn : Fn := ⟨"pure_store", [i32, i64, i64, i64], [i64], pureStoreGroupDiaArm⟩
  let negFn : Fn := ⟨"neg_addr", [i32, i64, i64, i64], [i64], negMismatchAddrArm⟩
  for (label, fn, expectBranchless) in
      [("full_m6_rmw", rmwFn, true), ("pure_store", pureFn, true), ("neg_addr", negFn, false)] do
    let ff : TFlatFn := ⟨fn.name, fn.as, fn.rs, reifyFunc fn.body⟩
    let ha := Fn.computeHints Arm64.armTarget.toIsa Arm64.armLegalTarget fn
    let aDirsP ← IO.ofExcept (compileFn Arm64.armTarget.toIsa Arm64.armLegalTarget ha fn)
    let aDirsF ← IO.ofExcept (compileFlatFn Arm64.armTarget.toIsa Arm64.armLegalTarget ha ff)
    let aAsmP := Kraken.AArch64.print aDirsP
    let aAsmF := Kraken.AArch64.print aDirsF
    if aAsmP != aAsmF then
      throw <| IO.userError s!"arm64 flat/phoas mismatch for {label}"
    if expectBranchless then
      if !hasSub aAsmP "csel" then
        throw <| IO.userError s!"arm64 {label}: expected csel in:\n{aAsmP}"
      for bcc in ["cbz ", "cbnz ", "tbz ", "tbnz ", "b."] do
        if hasSub aAsmP bcc then
          throw <| IO.userError s!"arm64 {label}: unexpected branch {bcc} in:\n{aAsmP}"
    else
      if !hasSub aAsmP "b." && !hasSub aAsmP "cbz" && !hasSub aAsmP "cbnz" then
        throw <| IO.userError s!"arm64 {label}: negative case unexpectedly eliminated branch"
  IO.println "OK (IfOptStoreSinkArm64Test): csel + zero branches + flat parity verified"

#print axioms rmwDiaArm_flat_parity

end LeanQbeTest.T.IfOptStoreSinkArm64Test
