module

public import LeanQbe.T.ZeroPeel
public import LeanQbe.T.ZeroPeelLemmas
public import LeanQbe.T.MainFlat
public import LeanQbe.T.MainFlatLemmas
public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertProof
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.MainCertInline
public import LeanQbe.T.Arm64.Targ
public import LeanQbe.T.Arm64.TargLemmas
public import Kraken.AArch64.Print
public import LeanQbe.T.Logic.MemLemmas
public import LeanQbe.T.Examples.Kissat.Plain
public import LeanQbe.T.Examples.Kissat.Plain1
import LeanQbe.T.FlatLemmas
import LeanQbe.T.WPLemmas
public meta import Lean
public meta import LeanQbe.T.MainCertElab
public meta import LeanQbe.T.MainCertFlatElab
public meta import LeanQbe.T.MainCertInline
public meta import LeanQbe.T.Arm64.Targ
public meta import Kraken.AArch64.Print
public meta import LeanQbe.T.MainFlat
public meta import LeanQbe.T.Examples.Kissat.Plain
public meta import LeanQbe.T.Examples.Kissat.Plain1

/-!
# AAPCS64 Arm64 `ZeroPeel` Widening / Unrolling Parity & Execution (`ZeroPeelWidenArm64Test`)

Arm64 companion to `ZeroPeelWidenTest` (zero X64 / Amd64 imports):
1. Arch-isolation audit verifying zero `Kraken.X64` / `LeanQbe.T.Amd64` imports.
2. Arm64 wide-store (`str xzr` / `str x...`) and 4x unrolled (`add w..., #4`) codegen `#guard`
   checks across `u32Zero8`, `u32MultiFill2`, `k6Loop1Shape`, `plain_zero_tables`,
   `plain_rephase`, and `plain_sweep`.
3. Certified `armTarget` parity (`compile_linked_chunks! (flat := false)` vs `(flat := true)`
   `code = rfl`, `bounds = rfl`), Arm64 `compileFlatFn = compileFn`, and `#print axioms`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.ZeroPeelWidenArm64Test

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Arm64 Kraken

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for m in env.allImportedModuleNames do
    if (`Kraken.X64).isPrefixOf m || (`LeanQbe.T.Amd64).isPrefixOf m then
      throwError s!"unexpected X64 import `{m}` in ZeroPeelWidenArm64Test"

@[expose] def countAsmLines (asm : String) (sub : String) : Nat :=
  ((asm.splitOn "\n").filter fun s => (s.splitOn sub).length > 1).length

@[expose] def hasSubstring (asm sub : String) : Bool :=
  (asm.splitOn sub).length > 1

@[expose] def compileArm64Asm (name : String) (as rs : List Ty) (body : Func as rs) :
    Except String String := do
  let tf := reifyFunc body
  let h := Fn.computeHints armTarget.toIsa armLegalTarget ⟨name, as, rs, body⟩
  let ds ← compileFlatFn armTarget.toIsa armLegalTarget h ⟨name, as, rs, tf⟩
  pure (Kraken.AArch64.print ds)

@[expose] def u32Zero8 : Func [i64, i32] [i64] := fun _ _ (ptr, n, ()) =>
  loop1 (ts := [i32])
    (fun loop (i, ()) =>
      .let_ (op2 (.ult i32) (.var i) (.var n)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op1 (.zext 32 64) (.var i)) fun (i64v, ()) =>
         .let_ (op2 (.add i64) (.var ptr) (.var i64v)) fun (addr, ()) =>
         .store (t := .bits 8) (.imm 0#8) (.var addr)
           (.let_ (op2 (.add i32) (.var i) (.imm 1#32)) fun (i', ()) =>
            .jump loop (.var i', ())))
        (.ret (.var ptr, ())))
    (fun loop => .jump loop (.imm 0#32, ()))

@[expose] def u32MultiFill2 : Func [i64, i64, i32] [i64] := fun _ _ (p0, p1, n, ()) =>
  loop1 (ts := [i32])
    (fun loop (i, ()) =>
      .let_ (op2 (.ult i32) (.var i) (.var n)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op1 (.zext 32 64) (.var i)) fun (i64v, ()) =>
         .let_ (op2 (.shl i64) (.var i64v) (.imm 2#64)) fun (off, ()) =>
         .let_ (op2 (.add i64) (.var p0) (.var off)) fun (a0, ()) =>
         .store (t := i32) (.imm 0#32) (.var a0)
           (.let_ (op2 (.add i64) (.var p1) (.var off)) fun (a1, ()) =>
            .store (t := i32) (.imm 0xffffffff#32) (.var a1)
              (.let_ (op2 (.add i32) (.var i) (.imm 1#32)) fun (i', ()) =>
               .jump loop (.var i', ()))))
        (.ret (.var p0, ())))
    (fun loop => .jump loop (.imm 0#32, ()))

@[expose] def k6Loop1Shape : Func [i64, i64, i64, i64, i64, i64, i32] [i32] :=
  fun _ _ (a0, a1, a2, a3, a4, a5, n, ()) =>
    loop1 (ts := [i32])
      (fun loop (i, ()) =>
        .let_ (op2 (.ult i32) (.var i) (.var n)) fun (c, ()) =>
        .jnz (.var c)
          (.let_ (op1 (.zext 32 64) (.var i)) fun (i64v, ()) =>
           .let_ (op2 (.shl i64) (.var i64v) (.imm 2#64)) fun (off, ()) =>
           .let_ (op2 (.add i64) (.var a0) (.var off)) fun (p0, ()) =>
           .store (t := i32) (.imm 0#32) (.var p0)
             (.let_ (op2 (.add i64) (.var a1) (.var off)) fun (p1, ()) =>
              .store (t := i32) (.imm 0xffffffff#32) (.var p1)
                (.let_ (op2 (.add i64) (.var a2) (.var off)) fun (p2, ()) =>
                 .store (t := i32) (.imm 0#32) (.var p2)
                   (.let_ (op2 (.add i32) (.var i) (.imm 1#32)) fun (i1, ()) =>
                    .let_ (op2 (.add i64) (.var a3) (.var off)) fun (p3, ()) =>
                    .store (t := i32) (.var i1) (.var p3)
                      (.let_ (op2 (.sub i32) (.var i) (.imm 1#32)) fun (im1, ()) =>
                       .let_ (op2 (.add i64) (.var a4) (.var off)) fun (p4, ()) =>
                       .store (t := i32) (.var im1) (.var p4)
                         (.let_ (op2 (.add i64) (.var a5) (.var off)) fun (p5, ()) =>
                          .store (t := i32) (.var i) (.var p5)
                            (.jump loop (.var i1, ()))))))))
          (.ret (.var n, ())))
      (fun loop => .jump loop (.imm 0#32, ()))

#guard match compileArm64Asm "plain_zero_tables" [i64] []
    Examples.Kissat.Plain.plain_zero_tables_body with
  | .ok optAsm =>
    countAsmLines optAsm "str xzr," >= 19 &&
    countAsmLines optAsm "str x" >= 21
  | .error _ => false

#guard match compileArm64Asm "u32_multi_fill2" [i64, i64, i32] [i64] u32MultiFill2 with
  | .ok optAsm => countAsmLines optAsm "str xzr," == 4 && countAsmLines optAsm "str x" >= 8
  | .error _ => false

#guard match compileArm64Asm "plain_rephase" [i64] []
    Examples.Kissat.Plain.plain_rephase_body with
  | .ok optAsm =>
    countAsmLines optAsm "str xzr," >= 4 &&
    countAsmLines optAsm "str x" >= 24
  | .error _ => false

#guard match compileArm64Asm "plain_sweep" [i64] [i64]
    Examples.Kissat.Plain.plain_sweep_body with
  | .ok optAsm => hasSubstring optAsm "#4\n" || hasSubstring optAsm "#2\n"
  | .error _ => false

@[expose] def fnU32Zero8 : Fn := ⟨"u32_zero8", [i64, i32], [i64], u32Zero8⟩
@[expose] def fnU32MultiFill2 : Fn := ⟨"u32_multi_fill2", [i64, i64, i32], [i64], u32MultiFill2⟩

@[expose] def widenArm64SrcMod : Module where
  fns := [fnU32Zero8, fnU32MultiFill2]

inline_mod! widenArm64Mod widenArm64SrcMod {} (compile := false)

theorem widenArm64SrcMod_acyclic : widenArm64SrcMod.checkAcyclic = true := by t_kernel_rfl

theorem widenArm64SrcMod_wf : ∀ f ∈ widenArm64SrcMod.fns, f.Wf := by
  intro f hf
  simp only [widenArm64SrcMod, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl <;> t_wf_reify

compile_linked_chunks! widenArm64Leg
  armTarget armLayout armLegalTarget armLabelClean widenArm64Mod 2 (flat := false)

compile_linked_chunks! widenArm64Flat
  armTarget armLayout armLegalTarget armLabelClean widenArm64Mod 2 (flat := true)

theorem arm64_widen_code_eq : widenArm64Leg.code = widenArm64Flat.code := rfl
theorem arm64_widen_bounds_eq : widenArm64Leg.bounds = widenArm64Flat.bounds := rfl

noncomputable def widenArm64FlatCast :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      (widenArm64SrcMod.optInlinePolicy {}) [] [] 0 2048 :=
  widenArm64Flat.castModule widenArm64Mod.eq

theorem arm64_fill2_eq (h : armTarget.toIsa.Hints) :
    compileFlatFn armTarget.toIsa armLegalTarget h
        ⟨fnU32MultiFill2.name, fnU32MultiFill2.as, fnU32MultiFill2.rs,
          reifyFunc fnU32MultiFill2.body⟩ =
      compileFn armTarget.toIsa armLegalTarget h fnU32MultiFill2 :=
  compileFlatFn_eq_compileFn _ _ _ _ (PassFlatKit.reifyFunc_wfCheck (by t_wf_reify))

#print axioms arm64_widen_code_eq
#print axioms arm64_widen_bounds_eq
#print axioms arm64_fill2_eq
#print axioms widenArm64Leg
#print axioms widenArm64Flat
#print axioms widenArm64FlatCast

end LeanQbeTest.T.ZeroPeelWidenArm64Test
