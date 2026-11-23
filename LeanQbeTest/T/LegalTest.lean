module

public import LeanQbe
public import LeanQbeTest.T.Examples
public import LeanQbeTest.T.Smoke
public import LeanQbeTest.T.NotationTest

/-!
# Target-parameterized legalisation tests (`LeanQbe.T.Legal`)

Exercises `Func.legal` / `Fn.legal`, `Func.legal_wf`, `Func.legal_wp` / `Func.legal_spec`,
`Func.legal_isLegal`, and computable kernel `rfl` checks (`t_kernel_rfl`) across:
1. All 8 example functions (`LeanQbeTest.T.Examples`) on `x64AVX512`, `x64SSE`, and `aarch64`.
2. Smoke tests (`LeanQbeTest.T.Smoke`), `tqbe` notation programs (`LeanQbeTest.T.NotationTest`),
   and Union-Find (`LeanQbe.T.Examples.UnionFind`).
3. Dedicated coverage of legalisation rules (a)–(d): pair splitting & aligned/unaligned memory,
   narrow/odd `bits n` widening (`n ∈ {0, 7, 12, 24}`), vector halving & scalarization,
   SIMD shuffle/blend/shift expansions, `bool`/`ternlog`/`bitcast` expansions, scalar-float
   pass-through on `x64`/`scalar64` (noting `Fn.backendOk` handles x64 scalar-FP rejection
   separately), and negative `isLegal` / `supportsSource` checks.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.LegalTest

open LeanQbe.T
open LeanQbe.T.Notation

abbrev x64 : LegalTarget := LegalTarget.x64AVX512
abbrev sse : LegalTarget := LegalTarget.x64SSE
abbrev arm : LegalTarget := LegalTarget.aarch64
abbrev sc64 : LegalTarget := LegalTarget.scalar64

/-! ## 1. `Examples` through `Func.legal` (`_wf`, `_isLegal` rfl, `_wp`/`_spec`) -/

-- 1a. `add128`: splits `u128 = .pair i64 i64` on both x64 and AArch64,
-- eliminating `mkpair`/`unpair`

theorem add128_legalSig_args_x64 :
    x64.legalSig [Examples.u128, Examples.u128] = [i64, i64, i64, i64] := rfl
theorem add128_legalSig_ret_x64 :
    x64.legalSig [Examples.u128, .bool] = [i64, i64, .bool] := rfl
theorem add128_src_not_legal_x64 : Examples.add128.isLegal x64 = false := by t_kernel_rfl
theorem add128_wf : Examples.add128.Wf := by t_wf_reify
theorem add128_supp_x64 : Examples.add128.supportsSource x64 = true := by t_kernel_rfl
theorem add128_supp_arm : Examples.add128.supportsSource arm = true := by t_kernel_rfl

theorem add128_legal_x64_wf : (Examples.add128.legal x64).Wf :=
  Func.legal_wf x64 add128_wf
theorem add128_legal_x64_isLegal_rfl : (Examples.add128.legal x64).isLegal x64 = true := by
  t_kernel_rfl
theorem add128_legal_x64_isLegal : (Examples.add128.legal x64).isLegal x64 = true :=
  Func.legal_isLegal x64 Examples.add128 add128_wf add128_supp_x64
theorem add128_legal_x64_check : (Examples.add128.legal x64).checkTFlat = true := by t_kernel_rfl

theorem add128_legal_arm_wf : (Examples.add128.legal arm).Wf :=
  Func.legal_wf arm add128_wf
theorem add128_legal_arm_isLegal_rfl : (Examples.add128.legal arm).isLegal arm = true := by
  t_kernel_rfl

theorem add128_legal_x64_spec (Γ : Env) (X : XPost) (m : Mem 64) (a b : Val Examples.u128) :
    Func.spec (legalEnv x64 Γ) (Examples.add128.legal x64)
      (encodeTup x64 [Examples.u128, Examples.u128] (a, b, ())) m
      (legalPost x64 fun (s, c, ()) _ =>
        c.toNat * 2 ^ 128 + Examples.U128.toNat s = Examples.U128.toNat a + Examples.U128.toNat b)
      (legalXPost x64 X) :=
  Func.legal_spec x64 Examples.add128 add128_wf add128_supp_x64 Γ (a, b, ()) m _ X
    (Examples.add128_spec Γ X m a b)

theorem add128_legal_arm_wp (Γ : Env) (X : XPost) (m : Mem 64) (a b : Val Examples.u128) :
    Func.wp (legalEnv arm Γ) (Examples.add128.legal arm)
      (encodeTup arm [Examples.u128, Examples.u128] (a, b, ())) m
      (legalPost arm fun (s, c, ()) _ =>
        c.toNat * 2 ^ 128 + Examples.U128.toNat s = Examples.U128.toNat a + Examples.U128.toNat b)
      (legalXPost arm X) :=
  Func.legal_wp arm Examples.add128 add128_wf add128_supp_arm Γ (a, b, ()) m _ X
    (Examples.add128_spec Γ X m a b)

-- 1b. `add256`, `mac`, `ult128`, `umin`, `mulByAdd`

theorem add256_wf : Examples.add256.Wf := by t_wf_reify
theorem add256_supp_x64 : Examples.add256.supportsSource x64 = true := by t_kernel_rfl
theorem add256_legal_x64_wf : (Examples.add256.legal x64).Wf :=
  Func.legal_wf x64 add256_wf
theorem add256_legal_x64_isLegal_rfl : (Examples.add256.legal x64).isLegal x64 = true := by
  t_kernel_rfl
theorem add256_legal_arm_isLegal_rfl : (Examples.add256.legal arm).isLegal arm = true := by
  t_kernel_rfl
theorem add256_legal_x64_spec (Γ : Env) (X : XPost) (m : Mem 64)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    Func.spec (legalEnv x64 Γ) (Examples.add256.legal x64)
      (encodeTup x64 _ (a0, a1, a2, a3, b0, b1, b2, b3, ())) m
      (legalPost x64 fun (s0, s1, s2, s3, c, ()) _ =>
        Examples.limbs [.imm s0, .imm s1, .imm s2, .imm s3] + c.toNat * 2 ^ 256 =
          Examples.limbs [.imm a0, .imm a1, .imm a2, .imm a3] +
          Examples.limbs [.imm b0, .imm b1, .imm b2, .imm b3])
      (legalXPost x64 X) :=
  Func.legal_spec x64 Examples.add256 add256_wf add256_supp_x64 Γ _ m _ X
    (Examples.add256_spec Γ X m a0 a1 a2 a3 b0 b1 b2 b3)

theorem mac_wf : Examples.mac.Wf := by t_wf_reify
theorem mac_supp_x64 : Examples.mac.supportsSource x64 = true := by t_kernel_rfl
theorem mac_legal_x64_wf : (Examples.mac.legal x64).Wf := Func.legal_wf x64 mac_wf
theorem mac_legal_x64_isLegal_rfl : (Examples.mac.legal x64).isLegal x64 = true := by t_kernel_rfl
theorem mac_legal_arm_isLegal_rfl : (Examples.mac.legal arm).isLegal arm = true := by t_kernel_rfl
theorem mac_legal_x64_spec (Γ : Env) (X : XPost) (m : Mem 64) (a b c d : BitVec 64) :
    Func.spec (legalEnv x64 Γ) (Examples.mac.legal x64)
      (encodeTup x64 _ (a, b, c, d, ())) m
      (legalPost x64 fun (lo, hi, ()) _ =>
        hi.toNat * 2 ^ 64 + lo.toNat = a.toNat * b.toNat + c.toNat + d.toNat)
      (legalXPost x64 X) :=
  Func.legal_spec x64 Examples.mac mac_wf mac_supp_x64 Γ _ m _ X (Examples.mac_spec Γ X m a b c d)

theorem ult128_wf : Examples.ult128.Wf := by t_wf_reify
theorem ult128_supp_arm : Examples.ult128.supportsSource arm = true := by t_kernel_rfl
theorem ult128_legal_x64_isLegal_rfl : (Examples.ult128.legal x64).isLegal x64 = true := by
  t_kernel_rfl
theorem ult128_legal_arm_wf : (Examples.ult128.legal arm).Wf :=
  Func.legal_wf arm ult128_wf
theorem ult128_legal_arm_isLegal_rfl : (Examples.ult128.legal arm).isLegal arm = true := by
  t_kernel_rfl
theorem ult128_legal_arm_spec (Γ : Env) (X : XPost) (m : Mem 64) (a b : Val Examples.u128) :
    Func.spec (legalEnv arm Γ) (Examples.ult128.legal arm)
      (encodeTup arm _ (a, b, ())) m
      (legalPost arm fun (r, ()) _ => r = decide (Examples.U128.toNat a < Examples.U128.toNat b))
      (legalXPost arm X) :=
  Func.legal_spec arm Examples.ult128 ult128_wf ult128_supp_arm Γ _ m _ X
    (Examples.ult128_spec Γ X m a b)

theorem umin_wf : Examples.umin.Wf := by t_wf_reify
theorem umin_supp_x64 : Examples.umin.supportsSource x64 = true := by t_kernel_rfl
theorem umin_legal_x64_isLegal_rfl : (Examples.umin.legal x64).isLegal x64 = true := by t_kernel_rfl
theorem umin_legal_arm_isLegal_rfl : (Examples.umin.legal arm).isLegal arm = true := by t_kernel_rfl
theorem umin_legal_x64_spec (Γ : Env) (X : XPost) (m : Mem 64) (a b : BitVec 64) :
    Func.spec (legalEnv x64 Γ) (Examples.umin.legal x64)
      (encodeTup x64 _ (a, b, ())) m
      (legalPost x64 fun (r, ()) _ => r.toNat = min a.toNat b.toNat)
      (legalXPost x64 X) :=
  Func.legal_spec x64 Examples.umin umin_wf umin_supp_x64 Γ _ m _ X (Examples.umin_spec Γ X m a b)

theorem mulByAdd_wf : Examples.mulByAdd.Wf := by t_wf_reify
theorem mulByAdd_supp_x64 : Examples.mulByAdd.supportsSource x64 = true := by t_kernel_rfl
theorem mulByAdd_legal_x64_wf : (Examples.mulByAdd.legal x64).Wf :=
  Func.legal_wf x64 mulByAdd_wf
theorem mulByAdd_legal_x64_isLegal_rfl : (Examples.mulByAdd.legal x64).isLegal x64 = true := by
  t_kernel_rfl
theorem mulByAdd_legal_arm_isLegal_rfl : (Examples.mulByAdd.legal arm).isLegal arm = true := by
  t_kernel_rfl
theorem mulByAdd_legal_x64_spec (Γ : Env) (X : XPost) (m : Mem 64) (n b : BitVec 64) :
    Func.spec (legalEnv x64 Γ) (Examples.mulByAdd.legal x64)
      (encodeTup x64 _ (n, b, ())) m
      (legalPost x64 fun (lo, hi, ()) _ => hi.toNat * 2 ^ 64 + lo.toNat = n.toNat * b.toNat)
      (legalXPost x64 X) :=
  Func.legal_spec x64 Examples.mulByAdd mulByAdd_wf mulByAdd_supp_x64 Γ _ m _ X
    (Examples.mulByAdd_spec Γ X m n b)

-- 1c. `qrStep`: stays packed `v4i32` on x64 (`rotl → rotr` expansion), scalarizes on AArch64

theorem qrStep_legalSig_x64 :
    x64.legalSig [v4i32, v4i32, v4i32] = [v4i32, v4i32, v4i32] := rfl
theorem qrStep_legalSig_arm :
    arm.legalSig [v4i32, v4i32, v4i32] =
      [i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32] := rfl
theorem qrStep_src_not_legal_x64 : Examples.qrStep.isLegal x64 = false := by t_kernel_rfl
theorem qrStep_wf : Examples.qrStep.Wf := by t_wf_reify
theorem qrStep_supp_x64 : Examples.qrStep.supportsSource x64 = true := by t_kernel_rfl
theorem qrStep_supp_arm : Examples.qrStep.supportsSource arm = true := by t_kernel_rfl

theorem qrStep_legal_x64_wf : (Examples.qrStep.legal x64).Wf :=
  Func.legal_wf x64 qrStep_wf
theorem qrStep_legal_x64_isLegal_rfl : (Examples.qrStep.legal x64).isLegal x64 = true := by
  t_kernel_rfl
theorem qrStep_legal_x64_check : (Examples.qrStep.legal x64).checkTFlat = true := by t_kernel_rfl
theorem qrStep_legal_arm_wf : (Examples.qrStep.legal arm).Wf :=
  Func.legal_wf arm qrStep_wf
theorem qrStep_legal_arm_isLegal_rfl : (Examples.qrStep.legal arm).isLegal arm = true := by
  t_kernel_rfl

theorem qrStep_legal_x64_spec (Γ : Env) (X : XPost) (m : Mem 64)
    (a0 a1 a2 a3 b0 b1 b2 b3 d0 d1 d2 d3 : BitVec 32) :
    Func.spec (legalEnv x64 Γ) (Examples.qrStep.legal x64)
      (encodeTup x64 _ (((a0, a1), (a2, a3)), ((b0, b1), (b2, b3)), ((d0, d1), (d2, d3)), ())) m
      (legalPost x64 fun (a', d', ()) _ =>
        a' = ((a0 + b0, a1 + b1), (a2 + b2, a3 + b3)) ∧
        d' = (((d0 ^^^ (a0 + b0)).rotateLeft 16, (d1 ^^^ (a1 + b1)).rotateLeft 16),
              ((d2 ^^^ (a2 + b2)).rotateLeft 16, (d3 ^^^ (a3 + b3)).rotateLeft 16)))
      (legalXPost x64 X) :=
  Func.legal_spec x64 Examples.qrStep qrStep_wf qrStep_supp_x64 Γ _ m _ X
    (Examples.qrStep_spec Γ X m a0 a1 a2 a3 b0 b1 b2 b3 d0 d1 d2 d3)

theorem qrStep_legal_arm_spec (Γ : Env) (X : XPost) (m : Mem 64)
    (a0 a1 a2 a3 b0 b1 b2 b3 d0 d1 d2 d3 : BitVec 32) :
    Func.spec (legalEnv arm Γ) (Examples.qrStep.legal arm)
      (encodeTup arm _ (((a0, a1), (a2, a3)), ((b0, b1), (b2, b3)), ((d0, d1), (d2, d3)), ())) m
      (legalPost arm fun (a', d', ()) _ =>
        a' = ((a0 + b0, a1 + b1), (a2 + b2, a3 + b3)) ∧
        d' = (((d0 ^^^ (a0 + b0)).rotateLeft 16, (d1 ^^^ (a1 + b1)).rotateLeft 16),
              ((d2 ^^^ (a2 + b2)).rotateLeft 16, (d3 ^^^ (a3 + b3)).rotateLeft 16)))
      (legalXPost arm X) :=
  Func.legal_spec arm Examples.qrStep qrStep_wf qrStep_supp_arm Γ _ m _ X
    (Examples.qrStep_spec Γ X m a0 a1 a2 a3 b0 b1 b2 b3 d0 d1 d2 d3)

-- 1d. `vumin`: vector `cmp ult` + `blend` (`v4i32` on x64/arm, `v8i32` halved on `sse` vs `x64`)

theorem vumin2_wf : (Examples.vumin 2).Wf := by t_wf_reify
theorem vumin2_supp_x64 : (Examples.vumin 2).supportsSource x64 = true := by t_kernel_rfl
theorem vumin2_legal_x64_wf : ((Examples.vumin 2).legal x64).Wf :=
  Func.legal_wf x64 vumin2_wf
theorem vumin2_legal_x64_isLegal_rfl : ((Examples.vumin 2).legal x64).isLegal x64 = true := by
  t_kernel_rfl
theorem vumin2_legal_arm_isLegal_rfl : ((Examples.vumin 2).legal arm).isLegal arm = true := by
  t_kernel_rfl
theorem vumin2_legal_x64_spec (Γ : Env) (X : XPost) (m : Mem 64)
    (a b : Val (Ty.vec 2 i32)) :
    Func.spec (legalEnv x64 Γ) ((Examples.vumin 2).legal x64)
      (encodeTup x64 _ (a, b, ())) m
      (legalPost x64 fun (r, ()) _ => Examples.LanewiseMin 2 r a b)
      (legalXPost x64 X) :=
  Func.legal_spec x64 (Examples.vumin 2) vumin2_wf vumin2_supp_x64 Γ (a, b, ()) m _ X
    (Examples.vumin_spec 2 Γ X m a b)

theorem vumin3_legalSig_sse :
    sse.legalSig [v8i32, v8i32] = [v4i32, v4i32, v4i32, v4i32] := rfl
theorem vumin3_wf : (Examples.vumin 3).Wf := by t_wf_reify
theorem vumin3_legal_x64_isLegal_rfl : ((Examples.vumin 3).legal x64).isLegal x64 = true := by
  t_kernel_rfl
theorem vumin3_legal_sse_isLegal_rfl : ((Examples.vumin 3).legal sse).isLegal sse = true := by
  t_kernel_rfl
theorem vumin3_legal_arm_isLegal_rfl : ((Examples.vumin 3).legal arm).isLegal arm = true := by
  t_kernel_rfl

/-! ## 2. `Smoke`, `NotationTest`, and `UnionFind` through `Func.legal` -/

theorem evenOdd_wf : Smoke.evenOdd.Wf := by t_wf_reify
theorem evenOdd_supp_x64 : Smoke.evenOdd.supportsSource x64 = true := by t_kernel_rfl
theorem evenOdd_legal_x64_wf : (Smoke.evenOdd.legal x64).Wf :=
  Func.legal_wf x64 evenOdd_wf
theorem evenOdd_legal_x64_isLegal_rfl : (Smoke.evenOdd.legal x64).isLegal x64 = true := by
  t_kernel_rfl
theorem evenOdd_legal_arm_isLegal_rfl : (Smoke.evenOdd.legal arm).isLegal arm = true := by
  t_kernel_rfl
theorem evenOdd_legal_x64_spec (Γ : Env) (X : XPost) (n : BitVec 64) (m : Mem 64) :
    Func.spec (legalEnv x64 Γ) (Smoke.evenOdd.legal x64)
      (encodeTup x64 [i64] (n, ())) m
      (legalPost x64 fun (r, ()) m' => r = Smoke.parity n.toNat ∧ m' = m)
      (legalXPost x64 X) :=
  Func.legal_spec x64 Smoke.evenOdd evenOdd_wf evenOdd_supp_x64 Γ (n, ()) m _ X
    (Smoke.evenOdd_correct Γ X n m)

theorem sumLanes_wf : Smoke.sumLanes.Wf := by t_wf_reify
theorem sumLanes_supp_x64 : Smoke.sumLanes.supportsSource x64 = true := by t_kernel_rfl
theorem sumLanes_legal_x64_isLegal_rfl : (Smoke.sumLanes.legal x64).isLegal x64 = true := by
  t_kernel_rfl
theorem sumLanes_legal_arm_isLegal_rfl : (Smoke.sumLanes.legal arm).isLegal arm = true := by
  t_kernel_rfl
theorem sumLanes_legal_x64_spec (Γ : Env) (X : XPost) (m : Mem 64) :
    Func.spec (legalEnv x64 Γ) (Smoke.sumLanes.legal x64)
      (encodeTup x64 [] ()) m
      (legalPost x64 fun (r, ()) m' => r = 1024#64 ∧ m' = m)
      (legalXPost x64 X) :=
  Func.legal_spec x64 Smoke.sumLanes sumLanes_wf sumLanes_supp_x64 Γ () m _ X
    (Smoke.sumLanes_correct Γ X m)

theorem tracer_wf : Smoke.tracer.Wf := by t_wf_reify
theorem tracer_legal_x64_isLegal_rfl : (Smoke.tracer.legal x64).isLegal x64 = true := by
  t_kernel_rfl
theorem tracer_legal_arm_isLegal_rfl : (Smoke.tracer.legal arm).isLegal arm = true := by
  t_kernel_rfl

theorem caller_wf : Smoke.caller.Wf := by t_wf_reify
theorem caller_supp_x64 : Smoke.caller.supportsSource x64 = true := by t_kernel_rfl
theorem caller_legal_x64_isLegal_rfl : (Smoke.caller.legal x64).isLegal x64 = true := by
  t_kernel_rfl
theorem caller_legal_arm_isLegal_rfl : (Smoke.caller.legal arm).isLegal arm = true := by
  t_kernel_rfl
theorem caller_legal_x64_spec (Γ : Env) (hg : Γ "g" [i64] [.bool, i64] = Smoke.gSpec)
    (a : BitVec 64) (m : Mem 64) :
    Func.spec (legalEnv x64 Γ) (Smoke.caller.legal x64)
      (encodeTup x64 [i64] (a, ())) m
      (legalPost x64 fun (r, ()) m' => a ≠ 0 ∧ r = a + 1 ∧ m' = m)
      (legalXPost x64 fun f as xs m' =>
        f = "abort" ∧ (⟨as, xs⟩ : (ts : List Ty) × Tup Val ts) = ⟨[i64], (a, ())⟩ ∧
          m' = m ∧ a = 0) :=
  Func.legal_spec x64 Smoke.caller caller_wf caller_supp_x64 Γ (a, ()) m _ _
    (Smoke.caller_correct Γ hg a m)

-- `NotationTest` programs through `Func.legal` / `Fn.legal`

theorem notation_add128_legal_x64_isLegal_rfl :
    (NotationTest.add128.legal x64).isLegal x64 = true := by t_kernel_rfl
theorem notation_mulByAdd_legal_x64_isLegal_rfl :
    (NotationTest.mulByAdd.legal x64).isLegal x64 = true := by t_kernel_rfl
theorem notation_qrStepSplat_legal_x64_isLegal_rfl :
    (NotationTest.qrStepSplat.legal x64).isLegal x64 = true := by t_kernel_rfl
theorem notation_qrStepSplat_legal_arm_isLegal_rfl :
    (NotationTest.qrStepSplat.legal arm).isLegal arm = true := by t_kernel_rfl
theorem notation_evenOdd_legal_x64_isLegal_rfl :
    (NotationTest.evenOdd.legal x64).isLegal x64 = true := by t_kernel_rfl
theorem notation_lbCheckPrf_legal_x64_wf : (NotationTest.lbCheckPrf.legal x64).Wf :=
  Func.legal_wf x64 NotationTest.lbCheckPrf_wf
theorem lbCheckPrf_legal_x64_isLegal :
    (NotationTest.lbCheckPrf.legal x64).isLegal x64 = true := by t_kernel_rfl
theorem notation_lbCheckPrf_legal_arm_isLegal_rfl :
    (NotationTest.lbCheckPrf.legal arm).isLegal arm = true := by t_kernel_rfl
theorem notation_loopBreak_legal_x64_isLegal_rfl :
    (NotationTest.loopBreak.legal x64).isLegal x64 = true := by t_kernel_rfl
theorem notation_namedBreak_legal_x64_isLegal_rfl :
    (NotationTest.namedBreak.legal x64).isLegal x64 = true := by t_kernel_rfl
theorem notation_pairAndMulti_legal_x64_isLegal_rfl :
    (NotationTest.pairAndMulti.legal x64).isLegal x64 = true := by t_kernel_rfl
theorem notation_pairAndMulti_legal_arm_isLegal_rfl :
    (NotationTest.pairAndMulti.legal arm).isLegal arm = true := by t_kernel_rfl
theorem notation_vecImmOps_legal_x64_isLegal_rfl :
    (NotationTest.vecImmOps.legal x64).isLegal x64 = true := by t_kernel_rfl
theorem notation_vecImmOps_legal_sse_isLegal_rfl :
    (NotationTest.vecImmOps.legal sse).isLegal sse = true := by t_kernel_rfl
theorem notation_floatCastAndTerms_legal_x64_isLegal_rfl :
    (NotationTest.floatCastAndTerms.legal x64).isLegal x64 = true := by t_kernel_rfl
theorem notation_floatCastAndTerms_legal_sc64_isLegal_rfl :
    (NotationTest.floatCastAndTerms.legal sc64).isLegal sc64 = true := by t_kernel_rfl
theorem notation_floatCastAndTerms_not_supp_arm :
    NotationTest.floatCastAndTerms.supportsSource arm = false := by t_kernel_rfl
theorem notation_storePairImm_legal_x64_isLegal_rfl :
    (NotationTest.storePairImm.legal x64).isLegal x64 = true := by t_kernel_rfl
theorem notation_storePairImm_legal_arm_isLegal_rfl :
    (NotationTest.storePairImm.legal arm).isLegal arm = true := by t_kernel_rfl
theorem notation_namedFn_legal_x64_wf : (NotationTest.namedFn.legal x64).Wf :=
  Fn.legal_wf x64 NotationTest.namedFn_wf
theorem notation_namedFn_legal_x64_isLegal_rfl :
    (NotationTest.namedFn.legal x64).body.isLegal x64 = true := by t_kernel_rfl

-- `UnionFind` through `Func.legal`

theorem uf_find_legal_x64_wf : (Examples.UnionFind.find.legal x64).Wf :=
  Func.legal_wf x64 Examples.UnionFind.find_wf
theorem uf_find_legal_x64_isLegal_rfl : (Examples.UnionFind.find.legal x64).isLegal x64 = true := by
  t_kernel_rfl
theorem uf_find_legal_arm_isLegal_rfl : (Examples.UnionFind.find.legal arm).isLegal arm = true := by
  t_kernel_rfl
theorem uf_union_legal_x64_isLegal_rfl :
    (Examples.UnionFind.union.legal x64).isLegal x64 = true := by t_kernel_rfl
theorem uf_unionInline_legal_x64_isLegal_rfl :
    (Examples.UnionFind.unionInline.legal x64).isLegal x64 = true := by t_kernel_rfl
theorem uf_unionInline_legal_arm_isLegal_rfl :
    (Examples.UnionFind.unionInline.legal arm).isLegal arm = true := by t_kernel_rfl

/-! ## 3. Dedicated legalisation rule coverage (rules a–d, floats, negative checks) -/

/-- Rule (a): pair splitting across `load`, `store`, `call`, and `ret`, including both
byte-aligned (`u128`) and non-byte-aligned (`pair (bits 12) (bits 12)`) memory accesses. -/
def pairMemCallFn : Func [Examples.u128, i64, Ty.pair (Ty.bits 12) (Ty.bits 12)] [Examples.u128] :=
  fun _ _ (a, p, q, ()) =>
    .store (.var a) (.var p) <|
    .load Examples.u128 (.var p) fun a' =>
    .store (.var q) (.var p) <|
    .load (Ty.pair (Ty.bits 12) (Ty.bits 12)) (.var p) fun q' =>
    .call "helper" (as := [Examples.u128, Ty.pair (Ty.bits 12) (Ty.bits 12)])
      (bs := [Examples.u128]) (.var a', .var q', ()) fun (res, ()) =>
    .ret (.var res, ())

theorem pairMemCallFn_wf : pairMemCallFn.Wf := by t_wf_reify
theorem pairMemCallFn_src_illegal : pairMemCallFn.isLegal x64 = false := by t_kernel_rfl
theorem pairMemCallFn_legal_x64_wf : (pairMemCallFn.legal x64).Wf :=
  Func.legal_wf x64 pairMemCallFn_wf
theorem pairMemCallFn_legal_x64_isLegal_rfl : (pairMemCallFn.legal x64).isLegal x64 = true := by
  t_kernel_rfl
theorem pairMemCallFn_legal_arm_isLegal_rfl : (pairMemCallFn.legal arm).isLegal arm = true := by
  t_kernel_rfl

/-- Rule (b): narrow/odd bit widths (`bits 12`, `bits 24`, `bits 7`, `bits 0`) covering arithmetic,
signed/unsigned shifts, compares, division, widening/narrowing casts, bitops, and
multi-result ops. -/
def oddBitsFn :
    Func [Ty.bits 12, Ty.bits 12, Ty.bits 24, Ty.bits 7, Ty.bits 0] [Ty.bits 12, .bool] :=
  fun _ _ (a, b, c, d, z, ()) =>
    .let_ (op2 (.add (.bits 12)) (.var a) (.var b)) fun (s1, ()) =>
    .let_ (op2 (.sub (.bits 12)) (.var s1) (.var b)) fun (s2, ()) =>
    .let_ (op2 (.mul (.bits 12)) (.var s2) (.var a)) fun (s3, ()) =>
    .let_ (op1 (.neg (.bits 12)) (.var s3)) fun (s4, ()) =>
    .let_ (op2 (.ashr (.bits 12)) (.var s4) (.imm 3#12)) fun (s5, ()) =>
    .let_ (op2 (.rotl (.bits 12)) (.var s5) (.imm 5#12)) fun (s6, ()) =>
    .let_ (op2 (.cmp .slt (.bits 12)) (.var s6) (.var a)) fun (cmp1, ()) =>
    .let_ (op2 (.sdiv0 12) (.var s6) (.var b)) fun (q1, ()) =>
    .let_ (op1 (.sext 12 24) (.var q1)) fun (e1, ()) =>
    .let_ (op2 (.add (.bits 24)) (.var e1) (.var c)) fun (e2, ()) =>
    .let_ (op1 (.trunc 24 12) (.var e2)) fun (t1, ()) =>
    .let_ (op1 (.cls 7) (.var d)) fun (cl1, ()) =>
    .let_ (op1 (.popcnt 7) (.var cl1)) fun (pc1, ()) =>
    .let_ (op1 (.zext 7 12) (.var pc1)) fun (z1, ()) =>
    .let_ (op3 (.addc 12) (.var t1) (.var z1) (.var cmp1)) fun (sum12, cout, ()) =>
    .let_ (op2 (.smulw 12) (.var sum12) (.var a)) fun (lo12, hi12, ()) =>
    .let_ (op2 (.xor (.bits 12)) (.var lo12) (.var hi12)) fun (out12, ()) =>
    .let_ (op2 (.add (.bits 0)) (.var z) (.imm 0#0)) fun (_z', ()) =>
    .ret (.var out12, .var cout, ())

theorem oddBitsFn_wf : oddBitsFn.Wf := by t_wf_reify
theorem oddBitsFn_src_illegal : oddBitsFn.isLegal x64 = false := by t_kernel_rfl
theorem oddBitsFn_legalSig_args :
    x64.legalSig [Ty.bits 12, Ty.bits 12, Ty.bits 24, Ty.bits 7, Ty.bits 0] =
      [i16, i16, i32, i8, i8] := rfl
theorem oddBitsFn_legal_x64_wf : (oddBitsFn.legal x64).Wf :=
  Func.legal_wf x64 oddBitsFn_wf
theorem oddBitsFn_legal_x64_isLegal_rfl : (oddBitsFn.legal x64).isLegal x64 = true := by
  t_kernel_rfl
theorem oddBitsFn_legal_arm_isLegal_rfl : (oddBitsFn.legal arm).isLegal arm = true := by
  t_kernel_rfl

/-- Rule (c): vector halving (`v8i32` -> 2×`v4i32` on `sse`, scalarized on `arm`), derived uniform
immediate `shl`/`rotl`, and explicit 128-bit shuffles (`shufd`, `shufb`, `alignr`, `blendw`). -/
def simdShuffleFn : Func [v8i32, v4i32, v4i32] [v8i32, v4i32] :=
  fun _ _ (v8, a, b, ()) =>
    .let_ (op2 (.shl v8i32) (.var v8) (.imm (splatV 3 (5#32 : Val i32)))) fun (sh1, ()) =>
    .let_ (op2 (.rotl v8i32) (.var sh1) (.imm (splatV 3 (7#32 : Val i32)))) fun (r8, ()) =>
    .let_ (op1 (.shufd v4i32 0x1b#8) (.var a)) fun (s1, ()) =>
    .let_ (op2 (.shufb v4i32) (.var s1) (.var b)) fun (s2, ()) =>
    .let_ (op2 (.alignr v4i32 4#8) (.var s2) (.var a)) fun (s3, ()) =>
    .let_ (op2 (.blendw v4i32 0xaa#8) (.var s3) (.var b)) fun (s4, ()) =>
    .ret (.var r8, .var s4, ())

theorem simdShuffleFn_wf : simdShuffleFn.Wf := by t_wf_reify
theorem simdShuffleFn_src_illegal : simdShuffleFn.isLegal sse = false := by t_kernel_rfl
theorem simdShuffleFn_legal_x64_isLegal_rfl : (simdShuffleFn.legal x64).isLegal x64 = true := by
  t_kernel_rfl
theorem simdShuffleFn_legal_sse_isLegal_rfl : (simdShuffleFn.legal sse).isLegal sse = true := by
  t_kernel_rfl
theorem simdShuffleFn_legal_arm_isLegal_rfl : (simdShuffleFn.legal arm).isLegal arm = true := by
  t_kernel_rfl

/-- Rule (d): derived `bool` ops (`cmp`/`select`/`add`/`ternlog`), scalar `ternlog`,
and `bitcast`s (`v4i32 → u128`, `pair (bits 12) (bits 20) → i32`). -/
def derivedOpsFn : Func [.bool, .bool, .bool, i64, v4i32, Ty.pair (Ty.bits 12) (Ty.bits 20)]
    [.bool, i64, Examples.u128, i32] :=
  fun _ _ (c1, c2, c3, x, v, p12_20, ()) =>
    .let_ (op2 (.cmp .ult .bool) (.var c1) (.var c2)) fun (b1, ()) =>
    .let_ (op3 (.select .bool) (.var b1) (.var c2) (.var c3)) fun (b2, ()) =>
    .let_ (op2 (.add .bool) (.var b2) (.var c1)) fun (b3, ()) =>
    .let_ (op3 (.ternlog .bool 0xca#8) (.var b3) (.var c2) (.var c3)) fun (b4, ()) =>
    .let_ (op3 (.ternlog i64 0x96#8) (.var x) (.imm 0x55#64) (.imm 0xaa#64)) fun (tx, ()) =>
    .let_ (op1 (.bitcast v4i32 Examples.u128 rfl) (.var v)) fun (u, ()) =>
    .let_ (op1 (.bitcast (Ty.pair (Ty.bits 12) (Ty.bits 20)) i32 rfl) (.var p12_20)) fun (w, ()) =>
    .ret (.var b4, .var tx, .var u, .var w, ())

theorem derivedOpsFn_wf : derivedOpsFn.Wf := by t_wf_reify
theorem derivedOpsFn_src_illegal : derivedOpsFn.isLegal x64 = false := by t_kernel_rfl
theorem derivedOpsFn_legal_x64_wf : (derivedOpsFn.legal x64).Wf :=
  Func.legal_wf x64 derivedOpsFn_wf
theorem derivedOpsFn_legal_x64_isLegal_rfl : (derivedOpsFn.legal x64).isLegal x64 = true := by
  t_kernel_rfl
theorem derivedOpsFn_legal_arm_isLegal_rfl : (derivedOpsFn.legal arm).isLegal arm = true := by
  t_kernel_rfl

/-- Rule (e): scalar float ops and float bitwise expansion (`xor`/`not` via integer `bitcast`).
Passes `Legal` on `x64` and `scalar64` (backend scalar-FP rejection on x64 is enforced separately
by `Fn.backendOk`); rejected by `supportsSource` on `aarch64`. -/
def scalarFloatFn : Func [f32, f32, i32] [f64, .bool] :=
  fun _ _ (x, y, n, ()) =>
    .let_ (op2 (.fadd f32) (.var x) (.var y)) fun (s, ()) =>
    .let_ (op2 (.xor f32) (.var s) (.var y)) fun (bx, ()) =>
    .let_ (op1 (.not f32) (.var bx)) fun (bn, ()) =>
    .let_ (op2 (.fcmp .lt f32) (.var bn) (.var x)) fun (lt, ()) =>
    .let_ (op1 (.fcvt .s .d) (.var bn)) fun (d1, ()) =>
    .let_ (op1 (.sitofp 32 .d) (.var n)) fun (d2, ()) =>
    .let_ (op2 (.fmul f64) (.var d1) (.var d2)) fun (prod, ()) =>
    .ret (.var prod, .var lt, ())

theorem scalarFloatFn_wf : scalarFloatFn.Wf := by t_wf_reify
theorem scalarFloatFn_supp_x64 : scalarFloatFn.supportsSource x64 = true := by t_kernel_rfl
theorem scalarFloatFn_supp_sc64 : scalarFloatFn.supportsSource sc64 = true := by t_kernel_rfl
theorem scalarFloatFn_not_supp_arm : scalarFloatFn.supportsSource arm = false := by t_kernel_rfl
theorem scalarFloatFn_legal_x64_wf : (scalarFloatFn.legal x64).Wf :=
  Func.legal_wf x64 scalarFloatFn_wf
theorem scalarFloatFn_legal_x64_isLegal_rfl : (scalarFloatFn.legal x64).isLegal x64 = true := by
  t_kernel_rfl
theorem scalarFloatFn_legal_sc64_isLegal_rfl : (scalarFloatFn.legal sc64).isLegal sc64 = true := by
  t_kernel_rfl

end LeanQbeTest.T.LegalTest
