module

public import LeanQbe.T.Examples.Kissat.FullM6BvaNoHops
public import LeanQbe.T.Examples.Kissat.FullBvaHeapSpec
public import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M6 Tier-A: Zero-Hop BVA Candidate Picker Proofs (`FullM6BvaNoHopsProof`)

M1-clean verification (`public section`, `0` `@[expose]`, `0` `import all`) proving:
1. `m6_bva_pick_cand_no_hops_wp` directly against canonical `FullBvaHeap.fullBvaPickCandSpec`
   with **zero** callee hypotheses (`∀ Γ args m Q X, ...`).
2. Closed `1`-row `m6BvaNoHopsSpecTable` (`noExit = true`), `m6BvaNoHopsEnv`,
   `m6BvaNoHops_tableImpl`, and unconditional `m6BvaNoHops_moduleOk`.
3. Concrete `Mem 64` UNSAT non-vacuity (`nv_m6_bva_pick_cand_no_hops`, `XPost := False`,
   reusing `FullBvaHeap.nvBvaDenseMem` with `ncntd = 2#32` exercising both loops).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6BvaNoHops

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapTactics
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullBvaHeapTactics

/-! ## 1. Callee-Free `Func.wp` Proof against Canonical `fullBvaPickCandSpec` -/

theorem m6_bva_pick_cand_no_hops_wp (Γ : Env) :
    ∀ args m Q X, fullBvaPickCandSpec args m Q X →
      Func.wp Γ full_bva_pick_cand_no_hops_body args m Q X := by
  rintro ⟨h, ncntd, f0, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hf0_lt, hnc_le, hcntd_ok, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len
  have hws_len := hsc.wsort_len; have hws1_len := hsc.work_stk1_len
  c0_hsteps
  -- Loop 1: single-pass scan maximizing `(cc, deg)` over `cntd[0..ncntd)` with zero memory writes
  refine wp_loop_inv
    (fun (best_c, best_deg, best_lit, ci, ()) ml =>
      ml = m ∧ ci.toNat ≤ ncntd.toNat ∧
      (2 ≤ best_c.toNat → best_lit.toNat < 2 * s.core.cur_vars))
    (fun (_, _, _, ci, _) _ => ncntd.toNat - ci.toNat)
    (fun J1 hJ1 => by
      c0_hsteps
      exact hJ1 (0#32, 0#32, 0xFFFFFFFF#32, 0#32, ()) m
        ⟨rfl, Nat.zero_le _, fun h => by simp only [bv_c0] at h; omega⟩)
    (fun J1 (best_c, best_deg, best_lit, ci, ()) ml ⟨hml, hci_le, hbl_ok⟩ ih1 => ?_)
  rcases hml with rfl
  c0_hsteps_nogrp
  · have hci_lt : ci.toNat < ncntd.toNat := by c0_bound
    have hci64 : (BitVec.setWidth 64 ci).toNat = ci.toNat := by c0_bound
    have hclit_lt :
        (s.scratch.work_stk1[ci.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
      have := hcntd_ok ci.toNat hci_lt
      rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
    have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by c0_bound
    have h2clit :
        ((BitVec.setWidth 64 (s.scratch.work_stk1[ci.toNat]'(by omega)) <<< (1 : Nat)) + 1).toNat =
          2 * (s.scratch.work_stk1[ci.toNat]'(by omega)).toNat + 1 := by
      change ((BitVec.setWidth 64 _ <<< (1 : Nat)) + 1#64).toNat = _; c0_bound
    have hclit_wvec :
        ((BitVec.setWidth 64
          (s.scratch.work_stk1[(BitVec.setWidth 64 ci).toNat]'(by rw [hci64]; omega)) <<<
            (1 : Nat)) + 1).toNat < s.core.wvec.length := by
      simp only [hci64, h2clit, hwv_len]; omega
    c0_hsteps
    all_goals first
      | exact ih1 (_, _, _, ci + 1#32, ()) ml (by dsimp only; rw [hci1]; omega)
          ⟨rfl, by rw [hci1]; omega, fun _ => by simpa only [hci64] using hclit_lt⟩
      | exact ih1 (_, _, best_lit, ci + 1#32, ()) ml (by dsimp only; rw [hci1]; omega)
          ⟨rfl, by rw [hci1]; omega, hbl_ok⟩
  · -- Loop 2: zero `cnt[cntd[0..ncntd)] = 0u`, then return `(best_c < 2u) ? 0xFFFFFFFFu : best_lit`
    let mkSt (ws : List (BitVec 32)) : FullState :=
      { core := { s.core with repr := s.core.repr, min_clr := s.core.min_clr,
                              tmp_cnt := s.core.tmp_cnt, tmp_len := s.core.tmp_len }
        scratch := { s.scratch with wsort := ws, ant_sz := s.scratch.ant_sz,
                                    sim_sig := s.scratch.sim_sig,
                                    shrink_stk := s.scratch.shrink_stk } }
    c0_hsteps
    refine wp_loop_inv
      (fun (ci, ()) m2 => ∃ ws2,
        ci.toNat ≤ ncntd.toNat ∧ ws2.length = 2 * c.max_vars ∧
        (FullMem c (mkSt ws2) ⋆ R) m2)
      (fun (ci, ()) _ => ncntd.toNat - ci.toNat)
      (fun J2 hJ2 => by
        c0_hsteps
        exact hJ2 (0#32, ()) ml ⟨s.scratch.wsort, Nat.zero_le _, hws_len, hm⟩)
      (fun J2 (ci, ()) m2 ⟨ws2, hci_le, hws2_len, hm2⟩ ih2 => ?_)
    dsimp only [mkSt] at hm2
    c0_hsteps_nogrp
    · have hci_lt : ci.toNat < ncntd.toNat := by c0_bound
      have hclit_lt :
          (s.scratch.work_stk1[ci.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
        have := hcntd_ok ci.toNat hci_lt
        rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
      have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by c0_bound
      c0_hsteps
      exact ih2 (ci + 1#32, ()) m (by dsimp only; rw [hci1]; omega)
        ⟨_, by rw [hci1]; omega, by simp [hws2_len], hm⟩
    · have hinv_fin : FullDenseInvNoLm c F0 F_cur (mkSt ws2) :=
        fullDenseInvNoLm_with_core_aux hinv hcl.repr_len hcl.min_clr_len_arr hcl.tmp_len_arr
          hcl.flags_len hcl.tmp_len_le { hsc with wsort_len := hws2_len } rfl rfl
      c0_hsteps
      · exact hQ 0xFFFFFFFF#32 s.core.repr s.core.min_clr s.core.tmp_cnt s.core.tmp_len
          ws2 s.scratch.ant_sz s.scratch.sim_sig s.scratch.shrink_stk m2 hinv_fin (Or.inl rfl) hm2
      · exact hQ best_lit s.core.repr s.core.min_clr s.core.tmp_cnt s.core.tmp_len
          ws2 s.scratch.ant_sz s.scratch.sim_sig s.scratch.shrink_stk m2 hinv_fin
          (Or.inr (hbl_ok (by c0_bound))) hm2

/-! ## 2. Closed `1`-Row Spec Table, `m6BvaNoHopsEnv`, & `m6BvaNoHops_moduleOk` -/

/-- Closed `1`-row specification table for `m6BvaNoHopsModule` (`noExit = true`). -/
def m6BvaNoHopsSpecTable : List SpecEntry :=
  [ ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], fullBvaPickCandSpec, true⟩ ]

/-- Closed specification environment for `m6BvaNoHopsModule`. -/
def m6BvaNoHopsEnv : Env := Env.ofTable m6BvaNoHopsSpecTable

theorem m6BvaNoHopsSpecTable_len : m6BvaNoHopsSpecTable.length = 1 := by
  rfl

theorem m6BvaNoHopsSpecTable_noExit : ∀ e ∈ m6BvaNoHopsSpecTable, e.noExit = true := by
  intro e he
  simp only [m6BvaNoHopsSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  subst he; rfl

theorem m6BvaNoHopsEnv_noExit :
    ∀ f as bs xs m Q X X',
      m6BvaNoHopsEnv f as bs xs m Q X → m6BvaNoHopsEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m6BvaNoHopsSpecTable_noExit

theorem m6BvaNoHops_tableImpl :
    TableImpl m6BvaNoHopsEnv m6BvaNoHopsFns m6BvaNoHopsSpecTable :=
  ⟨SpecEntry.Impl.of (m6_bva_pick_cand_no_hops_wp m6BvaNoHopsEnv), trivial⟩

/-- Unconditional closed `ModuleOk` for `m6BvaNoHopsModule` (`0` externs, `0` exits). -/
theorem m6BvaNoHops_moduleOk : ModuleOk m6BvaNoHopsEnv m6BvaNoHopsModule :=
  Env.ofTable_moduleOk m6BvaNoHops_acyclic ⟨full_bva_pick_cand_no_hops_wf, trivial⟩
    m6BvaNoHops_tableImpl

/-! ## 3. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT proofs) -/

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) on `nvBvaDenseMem` with `ncntd = 2#32`
(exercising both the candidate scan loop and the `cnt` zeroing loop). -/
theorem nv_m6_bva_pick_cand_no_hops :
    Func.wp m6BvaNoHopsEnv full_bva_pick_cand_no_hops_body
      (nvOneLitCfg.hdr, 2#32, 0#32, ()) nvBvaDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInvNoLm nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        (r = 0xFFFFFFFF#32 ∨ r.toNat < 2) ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  refine m6_bva_pick_cand_no_hops_wp m6BvaNoHopsEnv _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], nvBvaDenseState, emp, rfl,
      FullDenseInvW.toNoLm nvBvaDense_invW, by decide, by decide, ?_, hm,
      fun r _ _ _ _ _ _ _ _ m' hnl hr hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hnl, hr, nvDeduceF0_unsat, hm'⟩⟩
  intro i hi
  have hi' : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> decide

end LeanQbe.T.Examples.Kissat.FullM6BvaNoHops

end
