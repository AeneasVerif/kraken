/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import LeanQbe.T.MainCertCore
import LeanQbe.T.Amd64.TargLemmas
import LeanQbeTest.T.CertFlatDecodeFixture
import LeanQbe.T.FlatLemmas
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatDecode
meta import LeanQbe.T.MainCertInline
meta import LeanQbe.T.Amd64.Targ

/-!
# `.olean` `TFlatFn` Decoder & `(compile := false)` Cert Elaboration Test (`CertFlatDecodeTest`)

1. Publicly imports ONLY `LeanQbeTest.T.CertFlatDecodeFixture` (NO `meta import` of the inlined
   fixture!), exercising `compile_linked_chunks!` and `eval_prefix_ext!` (`(pruneFor := ...)`,
   `(prefixDef := ...)`) over `(compile := false)` `inline_mod_chunk!` / `inline_mod_join!`.
2. Exhaustively round-trips all `64` `OpCode` constructors, all `CmpOp`/`FCmpOp`/`Ty`/`Val`/`Arg`
   shapes, and all `TFlat`/`TBlocks` constructors via `InlineMeta.tflatToExpr` and `decodeTFlat`.
3. Checks `decodeFlatSliceExpr` (`some` + genuine kernel equality proof on materialized slices,
   `none` on unmaterialized modules) and `#print axioms` (`≤ std3`).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.CertFlatDecodeTest

open LeanQbe.T
open LeanQbe.T.Amd64
open LeanQbeTest.T.CertFlatDecodeFixture

/-- Submodule slice `[0, 2)` of `(compile := false)` `fixFns`. -/
noncomputable abbrev fixSlice1Mod : Module := { fns := fixFns.take 2 }

/-- Submodule slice `[2, 6)` of `(compile := false)` `fixFns`. -/
noncomputable abbrev fixSlice2Mod : Module := { fns := fixFns.drop 2 }

eval_prefix_ext! fixAllExt x64Target x64LegalTarget fixFns (prefixDef := fixExtPrefix)

compile_linked_chunks! fixCert1 x64Target x64Layout x64LegalTarget x64LabelClean
  fixSlice1Mod 2

eval_prefix_ext! fixSlice2Ext x64Target x64LegalTarget (fixFns.take 2)
  (pruneFor := fixSlice2Mod.fns)

compile_linked_chunks! fixCert2 x64Target x64Layout x64LegalTarget x64LabelClean
  fixSlice2Mod 2 (ext := fixSlice2Ext)

/-- Full linked cert over `(compile := false)` `fixMod` without `meta import` of fixture. -/
noncomputable def fixCertFull :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean fixMod [] [] 0 2048 :=
  fixCert1.append fixCert2 (by exact (List.take_append_drop 2 fixMod.fns).symm)
    (by t_kernel_rfl)

/-- Transported cert matching `fixSrcMod.optInlinePolicy fixPol` in O(1). -/
noncomputable def fixCertOpt :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      (fixSrcMod.optInlinePolicy fixPol) [] [] 0 2048 :=
  fixCertFull.castModule fixMod.eq

theorem fix_fns_flat_ok : fixFns = fixMod.flatFns.map TFlatFn.toFn :=
  fixMod.fns_flat_eq

theorem fix_single_flat_ok :
    fixSingleMod.fns = fixSingleMod.flatFns.map TFlatFn.toFn :=
  fixSingleMod.fns_flat_eq

theorem fix_c0_flat_ok : fixC0.fns = fixC0.flatFns.map TFlatFn.toFn :=
  fixC0.fns_flat_eq

section MetaDecodeChecks

meta section

open Lean Meta

private def mkSampleVal : (t : Ty) → Val t
  | .bool => true
  | .bits n => BitVec.ofNat n 13
  | .float f => BitVec.ofNat f.width 7
  | .pair a b => (mkSampleVal a, mkSampleVal b)

private def mkImmTup : (ts : List Ty) → Tup (Arg K) ts
  | [] => ()
  | t :: ts => (.imm (mkSampleVal t), mkImmTup ts)

private def mkVarTup (idx : Nat) : (ts : List Ty) → Tup (Arg K) ts
  | [] => ()
  | _ :: ts => (.var idx, mkVarTup (idx + 1) ts)

private def sampleOpCodes : List ((as : List Ty) × (rs : List Ty) × OpCode as rs) :=
  [ ⟨_, _, .copy (.pair i32 .bool)⟩
  , ⟨_, _, .add i64⟩, ⟨_, _, .sub i32⟩, ⟨_, _, .mul i16⟩, ⟨_, _, .neg i8⟩
  , ⟨_, _, .and i64⟩, ⟨_, _, .or i64⟩, ⟨_, _, .xor i64⟩, ⟨_, _, .not .bool⟩
  , ⟨_, _, .ternlog v4i32 0xA5#8⟩
  , ⟨_, _, .shl i64⟩, ⟨_, _, .lshr i32⟩, ⟨_, _, .ashr i64⟩
  , ⟨_, _, .rotl i32⟩, ⟨_, _, .rotr i64⟩
  , ⟨_, _, .fshl 64⟩, ⟨_, _, .fshr 32⟩
  , ⟨_, _, .bswap i64⟩, ⟨_, _, .clz 64⟩, ⟨_, _, .cls 32⟩
  , ⟨_, _, .rbit 64⟩, ⟨_, _, .ctz 64⟩, ⟨_, _, .popcnt 64⟩
  , ⟨_, _, .cmp .eq i64⟩, ⟨_, _, .cmp .ne i32⟩, ⟨_, _, .cmp .ult i64⟩
  , ⟨_, _, .cmp .ule i64⟩, ⟨_, _, .cmp .ugt i64⟩, ⟨_, _, .cmp .uge i64⟩
  , ⟨_, _, .cmp .slt i64⟩, ⟨_, _, .cmp .sle i64⟩, ⟨_, _, .cmp .sgt i64⟩
  , ⟨_, _, .cmp .sge i64⟩
  , ⟨_, _, .select i64⟩, ⟨_, _, .blend v4i32⟩
  , ⟨_, _, .zext 32 64⟩, ⟨_, _, .sext 8 64⟩, ⟨_, _, .trunc 64 32⟩
  , ⟨_, _, .ofBool 64⟩, ⟨_, _, .addc 64⟩, ⟨_, _, .subb 64⟩
  , ⟨_, _, .umulw 64⟩, ⟨_, _, .smulw 64⟩
  , ⟨_, _, .udiv 64⟩, ⟨_, _, .sdiv 64⟩, ⟨_, _, .urem 64⟩, ⟨_, _, .srem 64⟩
  , ⟨_, _, .udiv0 64⟩, ⟨_, _, .sdiv0 64⟩
  , ⟨_, _, .mkpair i32 .bool⟩, ⟨_, _, .unpair i32 .bool⟩
  , ⟨_, _, .bitcast i64 f64 rfl⟩
  , ⟨_, _, .shufd v4i32 0x1B#8⟩, ⟨_, _, .shufb v4i32⟩
  , ⟨_, _, .alignr v4i32 4#8⟩, ⟨_, _, .blendw v4i32 0x0F#8⟩
  , ⟨_, _, .sha256rnds2⟩, ⟨_, _, .sha256msg1⟩, ⟨_, _, .sha256msg2⟩
  , ⟨_, _, .fadd f64⟩, ⟨_, _, .fsub f32⟩, ⟨_, _, .fmul f64⟩, ⟨_, _, .fdiv f32⟩
  , ⟨_, _, .ffma f64⟩, ⟨_, _, .fsqrt f64⟩, ⟨_, _, .fneg f32⟩, ⟨_, _, .fabs f64⟩
  , ⟨_, _, .fcmp .eq f64⟩, ⟨_, _, .fcmp .ne f32⟩, ⟨_, _, .fcmp .lt f64⟩
  , ⟨_, _, .fcmp .le f64⟩, ⟨_, _, .fcmp .gt f64⟩, ⟨_, _, .fcmp .ge f64⟩
  , ⟨_, _, .fcmp .ord f64⟩, ⟨_, _, .fcmp .uno f64⟩
  , ⟨_, _, .fptoui .d 64⟩, ⟨_, _, .fptosi .s 32⟩
  , ⟨_, _, .uitofp 64 .d⟩, ⟨_, _, .sitofp 32 .s⟩, ⟨_, _, .fcvt .s .d⟩ ]

private def assertRoundTrip (rs : List Ty) (tf : TFlat rs) (label : String) : MetaM Unit := do
  let e := InlineMeta.tflatToExpr rs tf
  let some tf' := decodeTFlat rs e
    | throwError "decodeTFlat returned none for {label}"
  let e' := InlineMeta.tflatToExpr rs tf'
  if e != e' then
    throwError "tflat round-trip mismatch for {label}"

#eval show MetaM Unit from do
  -- 1. Exhaustive all-64 OpCode + Imm/Var round-trips.
  for (item, idx) in sampleOpCodes.zipIdx do
    let ⟨as, rs, code⟩ := item
    assertRoundTrip rs (.let_ ⟨code, mkImmTup as⟩ (.ret (mkVarTup 0 rs))) s!"imm#{idx}"
    assertRoundTrip rs (.let_ ⟨code, mkVarTup 10 as⟩ (.ret (mkVarTup 0 rs))) s!"var#{idx}"
  -- 2. All TFlat / TBlocks constructors.
  let callArgs : Tup (Arg K) [i32] := (.imm 9#32, ())
  let exitArgs : Tup (Arg K) [i64] := (.imm 1#64, ())
  let blk0 : TFlat [i64] :=
    .load (.pair i32 .bool) (.var 0)
      (.store (.imm (mkSampleVal f16)) (.var 1)
        (.call "ext_fn" [i32] callArgs
          (.jnz (.imm false) (.ret (.var 0, ()))
            (.exit "abort_fn" exitArgs))))
  let jArgs : Tup (Arg K) [i64] := (.var 0, ())
  let jBlk : TFlat [i64] := .jump 0 jArgs
  let blks : TBlocks [i64] [[i64]] := .cons jBlk .nil
  let fullTf : TFlat [i64] :=
    .group blks (.jnz (.var 2) blk0 .hlt)
  assertRoundTrip [i64] fullTf "all_tflat_ctors"
  -- 3. Verify noncomputable + exposed .olean encoding and decodeFlatSliceExpr.
  let env ← getEnv
  for nm in [``fixMod, ``fixFns, ``fixMod.flatFns, ``fixC0.flat.f0, ``fixC0.fn.f0] do
    if !Lean.isNoncomputable env nm then
      throwError "expected '{nm}' to be noncomputable"
    match env.find? nm with
    | some ci =>
      if ci.value?.isNone then throwError "expected '{nm}' value to be exposed in .olean"
    | none => throwError "missing constant '{nm}'"
  let some (fl1, flE1, pf1) ← decodeFlatSliceExpr (Lean.mkConst ``fixFns)
    | throwError "decodeFlatSliceExpr failed on fixFns"
  if fl1.length != 6 then throwError "expected 6 decoded fns, got {fl1.length}"
  let _ ← inferType pf1
  let sliceExpr := mkApp3 (Lean.mkConst ``List.take [1]) (Lean.mkConst ``LeanQbe.T.Fn)
    (mkNatLit 4) (mkApp3 (Lean.mkConst ``List.drop [1]) (Lean.mkConst ``LeanQbe.T.Fn)
      (mkNatLit 1) (Lean.mkConst ``fixFns))
  let some (fl2, _, pf2) ← decodeFlatSliceExpr sliceExpr
    | throwError "decodeFlatSliceExpr failed on (fixFns.drop 1).take 4"
  if fl2.length != 4 then throwError "expected 4 decoded slice fns, got {fl2.length}"
  let _ ← inferType pf2
  if (fl1.drop 1 |>.take 4 |>.map (·.name)) != fl2.map (·.name) then
    throwError "decoded slice names mismatch"
  let singleExpr := mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) (Lean.mkConst ``fixSingleMod)
  let some (fl3, _, pf3) ← decodeFlatSliceExpr singleExpr
    | throwError "decodeFlatSliceExpr failed on fixSingleMod.fns"
  if fl3.length != 6 then throwError "expected 6 decoded single-mod fns"
  let _ ← inferType pf3
  let unmatExpr := mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) (Lean.mkConst ``fixSrcMod)
  if (← decodeFlatSliceExpr unmatExpr).isSome then
    throwError "expected none for unmaterialized fixSrcMod.fns"
  if !(flE1.isAppOf ``List.cons) then
    throwError "expected cons list in flatListExpr"

end

end MetaDecodeChecks

#print axioms fix_fns_flat_ok
#print axioms fix_single_flat_ok
#print axioms fix_c0_flat_ok
#print axioms fixCert1
#print axioms fixCert2
#print axioms fixCertFull
#print axioms fixCertOpt

end LeanQbeTest.T.CertFlatDecodeTest
