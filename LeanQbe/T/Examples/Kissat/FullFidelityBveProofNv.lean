/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBveProof
public import LeanQbe.T.Examples.Kissat.FullFidelityBveProofNv0
import all LeanQbe.T.Examples.Kissat.FullFidelityBveProof
import all LeanQbe.T.Examples.Kissat.FullFidelityBveProofNv0
import all LeanQbe.T.Examples.Kissat.FullM8CoreParityProof
import all LeanQbe.T.Examples.Kissat.FullM8SweepV2Proof
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof0
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof
import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBve0
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity BVE Parity Closed-Env Concrete `Mem 64` Non-Vacuity (`FullFidelityBveProofNv`)

Instantiates all genuine non-bailout concrete `Mem 64` UNSAT non-vacuity proofs from
`FullFidelityBveProofNv0` directly onto BOTH closed environments:
- `fidBveEnv` (`fidBveModule`, `469` fns, `0` externs, `0` exits)
- `fidBveCoreParityEnv` (`fidBveCoreParityModule`, `472` fns, `0` externs, `0` exits)

Also adds direct `Mem 64` UNSAT non-vacuity `nv_fid_bve_gates` / `nv_fid_bve_gates_sw` exercising
`full_bve_gates_fid_body` on `nvFidCertMem` (`np = 1#32`, `nn = 0#32`, `scratch_buf[0] =
0x80000003#32` proving `(x0 ∨ ~x1)` from `nvFidFCur`). Strictly `std3`, `XPost := False`,
`0` expose attributes, `0` `*Lemmas*` in `public import`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBve

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM8CoreParity

/-! ## 1. Parametric Closed-Environment Instantiation Helpers -/

private theorem nv_fid_cert_at (Γ : Env)
    (hMaxV : ∀ a m Q X, m6MaxVSpec a m Q X → Γ "full_m6_max_v" [i64] [i64] a m Q X)
    (hAssign : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X) :
    Func.wp Γ full_bve_certify_unit_fid_body
      (nvFidCfg.hdr, 0#32, 0#32, 0#32, 1#32, 4002#32, ()) nvFidCertMem
      (fun (ok, ()) m' => ∃ s',
        ok = true ∧ s'.core.trail_end = 2 ∧
        s'.core.vals[0]? = some 1#8 ∧ s'.core.vals[1]? = some 0xFF#8 ∧
        s'.core.trl[1]? = some 0#32 ∧ FullDenseInvW nvFidCfg nvFidF0 nvFidFCur s' ∧
        TmkZero s' ∧ nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_certify_unit_direct_at Γ hMaxV hAssign

private theorem nv_fid_varM7_at (Γ : Env)
    (hBase : ∀ {nm as bs} {sp : Spec as bs},
      (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable →
      nm ∉ mfExclNames → nm ∉ m8CpExclNames →
      (∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) →
      ∀ a m Q X, sp a m Q X → Γ nm as bs a m Q X)
    (hBveRow : ∀ (k : Nat) (hk : k < m7FidBveRows.length) {nm as bs sp},
      m7FidBveRows[k] = ⟨nm, as, bs, sp, true⟩ → nm ∉ mfExclNames → nm ∉ m8CpExclNames →
      ∀ a m Q X, sp a m Q X → Γ nm as bs a m Q X)
    (hGatesFid : ∀ a m Q X, m8BveGatesSpec a m Q X →
      Γ "full_bve_gates_fid" [i64, i32, i32, i32] [] a m Q X) :
    Func.wp Γ full_bve_var_m7_body (nvFidCfg.hdr, 0#32, ()) nvFidCertMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvFidCfg nvFidF0 s' ∧ TmkZero s' ∧
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) := by
  have hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
  have hc2 := m7Part2Callees_of_sub m7FidBase_part2_mem
  exact nv_fid_bve_var_m7_at Γ
    (hBveRow 9 (by decide) rfl (by decide) (by decide))
    (hBase (m7FidP3Bve5_mem (i := 4) (by decide)) (by decide) (by decide) (fun _ _ _ _ h => h))
    (hBase (m7FidP3Bve5_mem (i := 1) (by decide)) (by decide) (by decide) (fun _ _ _ _ h => h))
    (hBase hc2.setInactive (by decide) (by decide) (fun _ _ _ _ h => h))
    hGatesFid
    (hBveRow 31 (by decide) rfl (by decide) (by decide))
    (hBase (m7FidP3Bve5_mem (i := 0) (by decide)) (by decide) (by decide) (fun _ _ _ _ h => h))
    (hBase hc1.assignLvl (by decide) (by decide) (fun _ _ _ _ h => h))
    (hBase (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.wstackDefrag)
      (by decide) (by decide) (fun _ _ _ _ h => h))
    (hBase (m7FidP3Bve5_mem (i := 3) (by decide)) (by decide) (by decide) (fun _ _ _ _ h => h))
    (hBveRow 1 (by decide) rfl (by decide) (by decide))

private theorem nv_fid_elimBve_at (Γ : Env)
    (hBveRow : ∀ (k : Nat) (hk : k < m7FidBveRows.length) {nm as bs sp},
      m7FidBveRows[k] = ⟨nm, as, bs, sp, true⟩ → nm ∉ mfExclNames → nm ∉ m8CpExclNames →
      ∀ a m Q X, sp a m Q X → Γ nm as bs a m Q X)
    (hPush : ∀ a m Q X, m8BveHeapPushSpec a m Q X →
      Γ "full_bve_heap_push_m7" [i64, i64, i32] [i64] a m Q X) :
    Func.wp Γ full_elim_bve_m7_body (nvFidCfg.hdr, 0#64, ()) nvFidCertMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvFidCfg nvFidF0 s' ∧ TmkZero s' ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_elim_bve_m7_at Γ
    (hBveRow 38 (by decide) rfl (by decide) (by decide))
    (hBveRow 39 (by decide) rfl (by decide) (by decide))
    (hBveRow 32 (by decide) rfl (by decide) (by decide))
    (hBveRow 1 (by decide) rfl (by decide) (by decide))
    hPush

private theorem nv_fid_elimM6_at (Γ : Env)
    (hBase : ∀ {nm as bs} {sp : Spec as bs},
      (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable →
      nm ∉ mfExclNames → nm ∉ m8CpExclNames →
      (∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) →
      ∀ a m Q X, sp a m Q X → Γ nm as bs a m Q X)
    (hBveRow : ∀ (k : Nat) (hk : k < m7FidBveRows.length) {nm as bs sp},
      m7FidBveRows[k] = ⟨nm, as, bs, sp, true⟩ → nm ∉ mfExclNames → nm ∉ m8CpExclNames →
      ∀ a m Q X, sp a m Q X → Γ nm as bs a m Q X) :
    Func.wp Γ full_eliminate_m6_body (nvFidCfg.hdr, false, ()) nvFidSparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvFidCfg nvFidF0 s' ∧ s'.core.cur_level = 0 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) := by
  have hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
  have hc2 := m7Part2Callees_of_sub m7FidBase_part2_mem
  exact nv_fid_eliminate_m6_at Γ
    (hBase m7FidP3ElimDticks_mem (by decide) (by decide) (fun _ _ _ _ h => h))
    (hBase hc1.log10Q16M7 (by decide) (by decide)
      (fun _ _ _ _ h => FullM7Search.m7Log10Q16Spec_monoX h))
    (hBase hc1.scaleDelta (by decide) (by decide) (fun _ _ _ _ h => h))
    (hBase hc2.enterDense (by decide) (by decide) (fun _ _ _ _ h => h))
    (hBase m7FidP3MinU64_mem (by decide) (by decide) (fun _ _ _ _ h => h))
    (hBveRow 10 (by decide) rfl (by decide) (by decide))
    (hBveRow 40 (by decide) rfl (by decide) (by decide))
    (hBase hc2.rebuildWatches (by decide) (by decide) (fun _ _ _ _ h => h))

private theorem nv_fid_gates_at (Γ : Env)
    (hHelp : ∀ (k : Nat) (hk : k < fidBveHelperRows.length) {nm as bs sp},
      fidBveHelperRows[k] = ⟨nm, as, bs, sp, true⟩ →
      (∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) →
      ∀ a m Q X, sp a m Q X → Γ nm as bs a m Q X) :
    Func.wp Γ full_bve_gates_fid_body (nvFidCfg.hdr, 0#32, 1#32, 0#32, ()) nvFidCertMem
      (fun () m' => ∃ s',
        FullDenseInvW nvFidCfg nvFidF0 nvFidFCur s' ∧ TmkZero s' ∧
        s'.core.cur_vars = 4 ∧ s'.core.arena = List.replicate 6 0#32 ∧
        s'.core.arena_len = 0 ∧ s'.core.fuel.toNat ≤ 1 ∧
        s'.scratch.scratch_buf[0]? = some 2147483651#32 ∧ nvFidF0.Unsat ∧
        FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) := by
  refine full_bve_gates_fid_wp Γ
    (hHelp 0 (by decide) rfl m8BveFindEquivSpec_noExit)
    (hHelp 1 (by decide) rfl m8BveFindAndSpec_noExit)
    (hHelp 4 (by decide) rfl m8BveFindIteSpec_noExit)
    (hHelp 18 (by decide) rfl m8BveGatesSpec_noExit)
    (nvFidCfg.hdr, 0#32, 1#32, 0#32, ()) nvFidCertMem _ (fun _ _ _ _ => False) ?_
  have hmem : (FullMem nvFidCfg nvFidCertState ⋆ emp) nvFidCertMem :=
    nvFidMkMem_ok 1#64 nvFidCertScr_len
  refine m8BveGatesSpec_intro rfl (nvFidState_denseInvW nvFidCertScr_len)
    (nvFidState_tmkZero 1#64 nvFidCertScr) (by decide) (by decide) (by decide) (by decide)
    ?_ (fun _ hj => by
      have hj0 : (0#32).toNat = 0 := rfl
      rw [hj0] at hj; exact absurd hj (Nat.not_lt_zero _)) hmem ?_
  · intro i hi
    have hi0 : i = 0 := by have h1 : (1#32).toNat = 1 := rfl; rw [h1] at hi; omega
    subst hi0
    dsimp only [FullBveEntryOkW, nvFidCertState, nvFidMkState, nvFidMkScratch]
    rw [nvFidCertScr_get0, Option.getD_some]
    rw [ite_eq_left (by decide : (2147483651#32 &&& 2147483648#32) ≠ 0#32)]
    exact ⟨by decide, nvFid_entails_03⟩
  · intro s' m' hdw htmk hcv har harl hfuel hpos _ hm'
    rw [sep_emp] at hm'
    have h0 : s'.scratch.scratch_buf[0]? = some 2147483651#32 := by
      rw [hpos 0 (by decide)]; exact nvFidCertScr_get0
    exact ⟨s', hdw, htmk, hcv, har, harl, hfuel, h0, nvFidF0_unsat, hm'⟩

/-! ## 2. Closed `fidBveEnv` (`469` fns) Concrete `Mem 64` Non-Vacuity Witnesses -/

/-- `GAP-BVE-01`: `full_bve_k6_mv_fid 0#64 = 0#64` under `fidBveEnv`. -/
theorem nv_fid_bve_k6_mv_zero (m : Mem 64) :
    Func.wp fidBveEnv full_bve_k6_mv_fid_body (0#64, ()) m
      (fun (r, ()) m' => r = 0#64 ∧ m' = m) (fun _ _ _ _ => False) :=
  nv_fid_bve_k6_mv_zero_at fidBveEnv m

/-- `GAP-BVE-01`: `full_bve_k6_mv_fid 16384#64 = 256#64` under `fidBveEnv`. -/
theorem nv_fid_bve_k6_mv_min (m : Mem 64) :
    Func.wp fidBveEnv full_bve_k6_mv_fid_body (16384#64, ()) m
      (fun (r, ()) m' => r = 256#64 ∧ m' = m) (fun _ _ _ _ => False) :=
  nv_fid_bve_k6_mv_min_at fidBveEnv m

/-- `GAP-BVE-01`: `full_bve_k6_mv_fid 65536#64 = 896#64` under `fidBveEnv`. -/
theorem nv_fid_bve_k6_mv_mid (m : Mem 64) :
    Func.wp fidBveEnv full_bve_k6_mv_fid_body (65536#64, ()) m
      (fun (r, ()) m' => r = 896#64 ∧ m' = m) (fun _ _ _ _ => False) :=
  nv_fid_bve_k6_mv_mid_at fidBveEnv m

/-- `GAP-BVE-01`: `full_bve_k6_mv_fid 524288#64 = 8192#64` under `fidBveEnv`. -/
theorem nv_fid_bve_k6_mv_cap (m : Mem 64) :
    Func.wp fidBveEnv full_bve_k6_mv_fid_body (524288#64, ()) m
      (fun (r, ()) m' => r = 8192#64 ∧ m' = m) (fun _ _ _ _ => False) :=
  nv_fid_bve_k6_mv_cap_at fidBveEnv m

/-- `GAP-BVE-01`: non-saturating `full_fid_k6_add_ticks` on `nvFidCertMem` under `fidBveEnv`. -/
theorem nv_fid_k6_add_ticks_add :
    Func.wp fidBveEnv full_fid_k6_add_ticks_body (nvFidCfg.hdr, 1500#64, ()) nvFidCertMem
      (fun _ m' => ∃ s',
        s'.scratch.scratch_buf[4204]? = some 1500#32 ∧ nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_k6_add_ticks_add_at fidBveEnv

/-- `GAP-BVE-01`: saturating (`0xFFFFFFFF#32`) `full_fid_k6_add_ticks` under `fidBveEnv`. -/
theorem nv_fid_k6_add_ticks_sat :
    Func.wp fidBveEnv full_fid_k6_add_ticks_body (nvFidCfg.hdr, 1000#64, ()) nvFidTicksMem
      (fun _ m' => ∃ s',
        s'.scratch.scratch_buf[4204]? = some 0xFFFFFFFF#32 ∧ nvFidF0.Unsat ∧
        FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_k6_add_ticks_sat_at fidBveEnv

/-- `GAP-BVE-03`: direct `Mem 64` unit certification (`trail_end = 2`, `vals[0]=1`,
`vals[1]=0xFF`, `trl[1]=0`) under `fidBveEnv`. -/
theorem nv_fid_certify_unit_direct :
    Func.wp fidBveEnv full_bve_certify_unit_fid_body
      (nvFidCfg.hdr, 0#32, 0#32, 0#32, 1#32, 4002#32, ()) nvFidCertMem
      (fun (ok, ()) m' => ∃ s',
        ok = true ∧ s'.core.trail_end = 2 ∧
        s'.core.vals[0]? = some 1#8 ∧ s'.core.vals[1]? = some 0xFF#8 ∧
        s'.core.trl[1]? = some 0#32 ∧ FullDenseInvW nvFidCfg nvFidF0 nvFidFCur s' ∧
        TmkZero s' ∧ nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_cert_at fidBveEnv
    (fidBveEnv_sweep_at (k := 0) (by decide) rfl (fun _ _ _ _ h => h))
    (fun _ _ _ _ h => fidBveEnv_assignLvl h)

/-- `GAP-BVE-01/03`: concrete `Mem 64` execution of `full_bve_gates_fid` on `nvFidCertMem` under
`fidBveEnv`. -/
theorem nv_fid_bve_gates :
    Func.wp fidBveEnv full_bve_gates_fid_body (nvFidCfg.hdr, 0#32, 1#32, 0#32, ()) nvFidCertMem
      (fun () m' => ∃ s',
        FullDenseInvW nvFidCfg nvFidF0 nvFidFCur s' ∧ TmkZero s' ∧
        s'.core.cur_vars = 4 ∧ s'.core.arena = List.replicate 6 0#32 ∧
        s'.core.arena_len = 0 ∧ s'.core.fuel.toNat ≤ 1 ∧
        s'.scratch.scratch_buf[0]? = some 2147483651#32 ∧ nvFidF0.Unsat ∧
        FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_gates_at fidBveEnv (fun _k hk {_ _ _ _} heq hno => fidBveEnv_helper_at hk heq hno)

/-- `full_bve_var_m7` concrete `Mem 64` UNSAT NV witness under `fidBveEnv`. -/
theorem nv_fid_bve_var_m7 :
    Func.wp fidBveEnv full_bve_var_m7_body (nvFidCfg.hdr, 0#32, ()) nvFidCertMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvFidCfg nvFidF0 s' ∧ TmkZero s' ∧
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_varM7_at fidBveEnv
    (fun hmem hnef hncp hno => fidBveEnv_m7Base_of_mem hmem hnef hncp hno)
    (fun _k hk {_ _ _ _} heq hnef hncp => fidBveEnv_m7BveRow hk heq hnef hncp)
    (fidBveEnv_helper_at (k := 19) (by decide) rfl m8BveGatesSpec_noExit)

/-- `full_bve_var` concrete `Mem 64` UNSAT NV witness under `fidBveEnv`. -/
theorem nv_fid_bve_var :
    Func.wp fidBveEnv full_bve_var_body (nvFidCfg.hdr, 0#32, ()) nvFidCertMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvFidCfg nvFidF0 s' ∧ TmkZero s' ∧
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_bve_var_at fidBveEnv
    (fidBveEnv_m7Base_of_mem m7FidBase_bveVar_mem (by decide) (by decide) (fun _ _ _ _ h => h))

/-- `GAP-BVE-02`: `full_elim_bve_m7` concrete `Mem 64` UNSAT NV witness under `fidBveEnv`. -/
theorem nv_fid_elim_bve_m7 :
    Func.wp fidBveEnv full_elim_bve_m7_body (nvFidCfg.hdr, 0#64, ()) nvFidCertMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvFidCfg nvFidF0 s' ∧ TmkZero s' ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_elimBve_at fidBveEnv
    (fun _k hk {_ _ _ _} heq hnef hncp => fidBveEnv_m7BveRow hk heq hnef hncp)
    (fun _ _ _ _ h => fidBveEnv_heapPush h)

/-- `full_eliminate_m6` concrete `Mem 64` UNSAT NV witness under `fidBveEnv`. -/
theorem nv_fid_eliminate_m6 :
    Func.wp fidBveEnv full_eliminate_m6_body (nvFidCfg.hdr, false, ()) nvFidSparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvFidCfg nvFidF0 s' ∧ s'.core.cur_level = 0 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_elimM6_at fidBveEnv
    (fun hmem hnef hncp hno => fidBveEnv_m7Base_of_mem hmem hnef hncp hno)
    (fun _k hk {_ _ _ _} heq hnef hncp => fidBveEnv_m7BveRow hk heq hnef hncp)

/-! ## 3. Closed `fidBveCoreParityEnv` (`472` fns) Concrete `Mem 64` Non-Vacuity Witnesses -/

/-- `GAP-BVE-01`: `full_bve_k6_mv_fid 0#64 = 0#64` under `fidBveCoreParityEnv`. -/
theorem nv_fid_bve_k6_mv_zero_sw (m : Mem 64) :
    Func.wp fidBveCoreParityEnv full_bve_k6_mv_fid_body (0#64, ()) m
      (fun (r, ()) m' => r = 0#64 ∧ m' = m) (fun _ _ _ _ => False) :=
  nv_fid_bve_k6_mv_zero_at fidBveCoreParityEnv m

/-- `GAP-BVE-01`: `full_bve_k6_mv_fid 16384#64 = 256#64` under `fidBveCoreParityEnv`. -/
theorem nv_fid_bve_k6_mv_min_sw (m : Mem 64) :
    Func.wp fidBveCoreParityEnv full_bve_k6_mv_fid_body (16384#64, ()) m
      (fun (r, ()) m' => r = 256#64 ∧ m' = m) (fun _ _ _ _ => False) :=
  nv_fid_bve_k6_mv_min_at fidBveCoreParityEnv m

/-- `GAP-BVE-01`: `full_bve_k6_mv_fid 65536#64 = 896#64` under `fidBveCoreParityEnv`. -/
theorem nv_fid_bve_k6_mv_mid_sw (m : Mem 64) :
    Func.wp fidBveCoreParityEnv full_bve_k6_mv_fid_body (65536#64, ()) m
      (fun (r, ()) m' => r = 896#64 ∧ m' = m) (fun _ _ _ _ => False) :=
  nv_fid_bve_k6_mv_mid_at fidBveCoreParityEnv m

/-- `GAP-BVE-01`: `full_bve_k6_mv_fid 524288#64 = 8192#64` under `fidBveCoreParityEnv`. -/
theorem nv_fid_bve_k6_mv_cap_sw (m : Mem 64) :
    Func.wp fidBveCoreParityEnv full_bve_k6_mv_fid_body (524288#64, ()) m
      (fun (r, ()) m' => r = 8192#64 ∧ m' = m) (fun _ _ _ _ => False) :=
  nv_fid_bve_k6_mv_cap_at fidBveCoreParityEnv m

/-- `GAP-BVE-01`: non-saturating `full_fid_k6_add_ticks` under `fidBveCoreParityEnv`. -/
theorem nv_fid_k6_add_ticks_add_sw :
    Func.wp fidBveCoreParityEnv full_fid_k6_add_ticks_body (nvFidCfg.hdr, 1500#64, ())
      nvFidCertMem
      (fun _ m' => ∃ s',
        s'.scratch.scratch_buf[4204]? = some 1500#32 ∧ nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_k6_add_ticks_add_at fidBveCoreParityEnv

/-- `GAP-BVE-01`: saturating `full_fid_k6_add_ticks` under `fidBveCoreParityEnv`. -/
theorem nv_fid_k6_add_ticks_sat_sw :
    Func.wp fidBveCoreParityEnv full_fid_k6_add_ticks_body (nvFidCfg.hdr, 1000#64, ())
      nvFidTicksMem
      (fun _ m' => ∃ s',
        s'.scratch.scratch_buf[4204]? = some 0xFFFFFFFF#32 ∧ nvFidF0.Unsat ∧
        FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_k6_add_ticks_sat_at fidBveCoreParityEnv

/-- `GAP-BVE-03`: direct `Mem 64` unit certification under `fidBveCoreParityEnv`. -/
theorem nv_fid_certify_unit_direct_sw :
    Func.wp fidBveCoreParityEnv full_bve_certify_unit_fid_body
      (nvFidCfg.hdr, 0#32, 0#32, 0#32, 1#32, 4002#32, ()) nvFidCertMem
      (fun (ok, ()) m' => ∃ s',
        ok = true ∧ s'.core.trail_end = 2 ∧
        s'.core.vals[0]? = some 1#8 ∧ s'.core.vals[1]? = some 0xFF#8 ∧
        s'.core.trl[1]? = some 0#32 ∧ FullDenseInvW nvFidCfg nvFidF0 nvFidFCur s' ∧
        TmkZero s' ∧ nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_cert_at fidBveCoreParityEnv
    (fidBveCoreParityEnv_sweep_at (k := 0) (by decide) rfl (fun _ _ _ _ h => h))
    (fun _ _ _ _ h => fidBveCoreParityEnv_assignLvl h)

/-- `GAP-BVE-01/03`: concrete `Mem 64` execution of `full_bve_gates_fid` under
`fidBveCoreParityEnv`. -/
theorem nv_fid_bve_gates_sw :
    Func.wp fidBveCoreParityEnv full_bve_gates_fid_body (nvFidCfg.hdr, 0#32, 1#32, 0#32, ())
      nvFidCertMem
      (fun () m' => ∃ s',
        FullDenseInvW nvFidCfg nvFidF0 nvFidFCur s' ∧ TmkZero s' ∧
        s'.core.cur_vars = 4 ∧ s'.core.arena = List.replicate 6 0#32 ∧
        s'.core.arena_len = 0 ∧ s'.core.fuel.toNat ≤ 1 ∧
        s'.scratch.scratch_buf[0]? = some 2147483651#32 ∧ nvFidF0.Unsat ∧
        FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_gates_at fidBveCoreParityEnv
    (fun _k hk {_ _ _ _} heq hno => fidBveCoreParityEnv_helper_at hk heq hno)

/-- `full_bve_var_m7` concrete `Mem 64` UNSAT NV witness under `fidBveCoreParityEnv`. -/
theorem nv_fid_bve_var_m7_sw :
    Func.wp fidBveCoreParityEnv full_bve_var_m7_body (nvFidCfg.hdr, 0#32, ()) nvFidCertMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvFidCfg nvFidF0 s' ∧ TmkZero s' ∧
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_varM7_at fidBveCoreParityEnv
    (fun hmem hnef hncp hno => fidBveCoreParityEnv_m7Base_of_mem hmem hnef hncp hno)
    (fun _k hk {_ _ _ _} heq hnef hncp => fidBveCoreParityEnv_m7BveRow hk heq hnef hncp)
    (fidBveCoreParityEnv_helper_at (k := 19) (by decide) rfl m8BveGatesSpec_noExit)

/-- `full_bve_var` concrete `Mem 64` UNSAT NV witness under `fidBveCoreParityEnv`. -/
theorem nv_fid_bve_var_sw :
    Func.wp fidBveCoreParityEnv full_bve_var_body (nvFidCfg.hdr, 0#32, ()) nvFidCertMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvFidCfg nvFidF0 s' ∧ TmkZero s' ∧
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_bve_var_at fidBveCoreParityEnv
    (fidBveCoreParityEnv_m7Base_of_mem m7FidBase_bveVar_mem
      (by decide) (by decide) (fun _ _ _ _ h => h))

/-- `GAP-BVE-02`: `full_elim_bve_m7` concrete `Mem 64` UNSAT NV witness under
`fidBveCoreParityEnv`. -/
theorem nv_fid_elim_bve_m7_sw :
    Func.wp fidBveCoreParityEnv full_elim_bve_m7_body (nvFidCfg.hdr, 0#64, ()) nvFidCertMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvFidCfg nvFidF0 s' ∧ TmkZero s' ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_elimBve_at fidBveCoreParityEnv
    (fun _k hk {_ _ _ _} heq hnef hncp => fidBveCoreParityEnv_m7BveRow hk heq hnef hncp)
    (fun _ _ _ _ h => fidBveCoreParityEnv_heapPush h)

/-- `full_eliminate_m6` concrete `Mem 64` UNSAT NV witness under `fidBveCoreParityEnv`. -/
theorem nv_fid_eliminate_m6_sw :
    Func.wp fidBveCoreParityEnv full_eliminate_m6_body (nvFidCfg.hdr, false, ()) nvFidSparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvFidCfg nvFidF0 s' ∧ s'.core.cur_level = 0 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvFidF0.Unsat ∧ FullMem nvFidCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_fid_elimM6_at fidBveCoreParityEnv
    (fun hmem hnef hncp hno => fidBveCoreParityEnv_m7Base_of_mem hmem hnef hncp hno)
    (fun _k hk {_ _ _ _} heq hnef hncp => fidBveCoreParityEnv_m7BveRow hk heq hnef hncp)

end LeanQbe.T.Examples.Kissat.FullFidelityBve

end
