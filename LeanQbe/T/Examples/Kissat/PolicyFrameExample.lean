module

public import LeanQbe.T.Examples.Kissat.FullM7Bump
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
public import LeanQbe.T.Examples.Kissat.PolicyFrame
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Soundness-Boundary Working Example (`PolicyFrameExample`)

Demonstrates `PolicyFrame` on real landed M7 policy code (`FullM7Bump.full_bump_sift_m7`,
`full_bump_sort_stamps_m7` — zero edits to `FullM7Bump.lean` or `FullM7BumpProof.lean`),
showing:
1. Short `PolicyFrameSpec` WP proofs (~165 LOC vs `~1,130` LOC for the functional heap/order/perm
   proofs of `full_bump_sift_m7` + `full_bump_sort_stamps_m7` in `FullM7BumpProof.lean`, a
   >6× reduction).
2. Clean `SpecEntry` / `TableImpl` / `NoExit` / `ModuleOk` composition (`m7BumpPolicy_moduleOk`).
3. Direct lifts into `FullM6HdrInv` and `F0.Unsat` soundness (`m7_bump_sort_m6HdrInv_unsat`
   for Tier P1, `m7_policyDelete_m6HdrInv_unsat` for Tier P2), plus concrete `Mem 64`
   non-vacuity (`nv_policy_bump_sort`, `XPost := False`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.PolicyFrameExample

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM7Bump
open LeanQbe.T.Examples.Kissat.PolicyFrame
open Kraken.Bedrock2.Test

/-! ## 1. `PolicyFrameSpec` Contracts & Short WP Proofs on Landed `FullM7Bump` Code -/

/-- `PolicyFrameSpec` contract for `full_bump_sift_m7`: `(h, start, n) -> ()`. -/
@[expose] def m7BumpSiftPolicySpec : Spec [i64, i64, i64] [] :=
  PolicyFrameSpec (fun c (h, _, _, ()) _ => h = c.hdr)

/-- `PolicyFrameSpec` contract for `full_bump_sort_stamps_m7`: `(h, n) -> ()`. -/
@[expose] def m7BumpSortPolicySpec : Spec [i64, i64] [] :=
  PolicyFrameSpec (fun c (h, _, ()) _ => h = c.hdr)

section ExampleProofs

open scoped FullArenaTactics

private theorem zext32_toNat_ex (x : BitVec 32) : (BitVec.setWidth 64 x).toNat = x.toNat :=
  zext_toNat x (by decide)

private theorem lengthsOk_ws1_swap_ex {c : FullCfg} {s : FullState}
    (h : s.LengthsOk c) {i j : Nat} {vi vj : BitVec 32} :
    ({ s with scratch :=
        { s.scratch with work_stk1 := (s.scratch.work_stk1.set i vi).set j vj } } :
      FullState).LengthsOk c :=
  ⟨h.core_ok, fullScratch_lengthsOk_of_arr_len h.scratch_ok
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by simp)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩

/-- `full_bump_sift_m7` satisfies `m7BumpSiftPolicySpec`: only memory bounds + disjointness. -/
theorem full_bump_sift_m7_policy_wp (Γ : Env) :
    ∀ a m Q X, m7BumpSiftPolicySpec a m Q X → Func.wp Γ full_bump_sift_m7_body a m Q X := by
  refine wp_policy_intro fun c (h, start, n, ()) s R m Q X hpre hlen hm hk => ?_
  subst hpre
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmax
  c0_hsteps_nogrp
  · exact hk () s m (PolicyStep.refl s) hlen trivial hm
  · exact hk () s m (PolicyStep.refl s) hlen trivial hm
  · exact hk () s m (PolicyStep.refl s) hlen trivial hm
  · exact hk () s m (PolicyStep.refl s) hlen trivial hm
  · have hstn : start.toNat < n.toNat := by c0_bound
    have hncv : n.toNat ≤ s.core.cur_vars := by c0_bound
    have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
    refine wp_policy_loop_break (brkTs := [i64]) (lpTs := [i64]) c s R (fun _ _ => True)
      (fun s' (root, ()) => root.toNat < n.toNat ∧ s'.core.cur_vars = s.core.cur_vars)
      (fun _ (root, ()) => n.toNat - root.toNat) ?_ ?_ ?_
    · rintro _ s' ⟨_, ⟨⟩⟩ ml hp hlen' _ hm'
      c0_hsteps_nogrp
      exact hk () _ ml hp hlen' trivial hm'
    · rintro B L s1 ⟨root, ⟨⟩⟩ ml _ hlen1 ⟨hrn, hcv1⟩ hm1 hB hL
      have hroot29 : root.toNat < 2 ^ 29 := by omega
      have hshl : (root <<< 1#64).toNat = 2 * root.toNat := by
        simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
      have hch1 : (root <<< 1#64 + 1#64).toNat = 2 * root.toNat + 1 := by
        rw [BitVec.toNat_add, hshl, show (1#64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
      c0_hsteps_nogrp
      · exact hB s1 (root, ()) ml hm1 (PolicyStep.refl s1) hlen1 trivial
      · have hch_lt : 2 * root.toNat + 1 < n.toNat := by c0_bound
        have hch_wl : (root <<< 1#64 + 1#64).toNat < s1.scratch.work_stk1.length := by
          rw [hlen1.scratch_ok.work_stk1_len]; omega
        refine wp_load_of (FullArenaTactics.c0_load_full_work_stk1 hch_wl hm1) ?_
        refine wp_policy_join (ts := [i32]) c s1 R (fun s' _ => s' = s1) ?_ ?_
        · rintro _ s2 ⟨cq, ⟨⟩⟩ m2 _ hlen2 hs2 hm2
          subst s2
          c0_hsteps_nogrp
          refine wp_policy_join (ts := [i64, i32, i32]) c s1 R
            (fun s' (ch', _, _, ()) => s' = s1 ∧ ch'.toNat < n.toNat ∧ root.toNat < ch'.toNat)
            ?_ ?_
          · rintro _ s3 ⟨ch', cl', cq', ⟨⟩⟩ m3 _ hlen3 ⟨hs3, hch'_n, hrt_lt⟩ hm3
            subst s3
            c0_hsteps_nogrp
            have hrl_wl : root.toNat < s1.scratch.work_stk1.length := by
              rw [hlen3.scratch_ok.work_stk1_len]; omega
            refine wp_policy_join (ts := [i32]) c s1 R (fun s' _ => s' = s1) ?_ ?_
            · rintro _ s4 ⟨rq, ⟨⟩⟩ m4 _ hlen4 hs4 hm4
              subst s4
              clear hm hm1 hm2 hm3
              c0_hsteps
              · exact hB s1 (root, ()) m4 hm4 (PolicyStep.refl s1) hlen4 trivial
              · exact hB s1 (root, ()) m4 hm4 (PolicyStep.refl s1) hlen4 trivial
              all_goals (
                have hch'_wl : ch'.toNat < s1.scratch.work_stk1.length := by
                  rw [hlen4.scratch_ok.work_stk1_len]; omega
                have hrt_wl : root.toNat <
                    (s1.scratch.work_stk1.set ch'.toNat
                      s1.scratch.work_stk1[root.toNat]).length := by
                  rw [List.length_set, hlen4.scratch_ok.work_stk1_len]; omega
                have hset_wl : ch'.toNat < (s1.scratch.work_stk1.set root.toNat cl').length := by
                  rw [List.length_set]; exact hch'_wl
                c0_hsteps_nogrp
                let s_next : FullState := { s1 with scratch := { s1.scratch with
                  work_stk1 := (s1.scratch.work_stk1.set root.toNat cl').set ch'.toNat
                    s1.scratch.work_stk1[root.toNat] } }
                exact hL s_next (ch', ()) m (by assumption) (by dsimp only; omega)
                  (PolicyStep.with_scratch (PolicyStep.refl s1) rfl rfl)
                  (lengthsOk_ws1_swap_ex hlen4) ⟨hch'_n, hcv1⟩)
            · intro _ hJrq
              c0_hsteps_nogrp
              · try rw [zext32_toNat_ex] at hc
                rw [Nat.mod_eq_of_lt (by omega)] at hc
                have hrl_qs :
                    s1.scratch.work_stk1[root.toNat].toNat < s1.scratch.q_stamp.length := by
                  rw [hlen3.scratch_ok.q_stamp_len]; omega
                refine wp_load_of (FullArenaTactics.c0_load_full_q_stamp
                  (by rwa [zext32_toNat_ex]) hm3) ?_
                exact hJrq s1 (_, ()) m3 hm3 (PolicyStep.refl s1) hlen3 rfl
              · exact hJrq s1 (0#32, ()) m3 hm3 (PolicyStep.refl s1) hlen3 rfl
          · intro _ hJsib
            c0_hsteps_nogrp
            · have hs_lt : 2 * root.toNat + 2 < n.toNat := by c0_bound
              have hsl_eq : (root <<< 1#64 + 1#64 + 1#64).toNat = 2 * root.toNat + 2 := by
                bv_omega
              have hsl_wl :
                  (root <<< 1#64 + 1#64 + 1#64).toNat < s1.scratch.work_stk1.length := by
                rw [hlen2.scratch_ok.work_stk1_len, hsl_eq]; omega
              refine wp_load_of (FullArenaTactics.c0_load_full_work_stk1 hsl_wl hm2) ?_
              refine wp_policy_join (ts := [i32]) c s1 R (fun s' _ => s' = s1) ?_ ?_
              · rintro _ s3 ⟨sq, ⟨⟩⟩ m3 _ hlen3 hs3 hm3
                subst s3
                c0_hsteps
                · exact hJsib s1 (root <<< 1#64 + 1#64 + 1#64, _, sq, ()) m3 hm3
                    (PolicyStep.refl s1) hlen3 ⟨rfl, by rw [hsl_eq]; exact hs_lt, by omega⟩
                · exact hJsib s1 (root <<< 1#64 + 1#64 + 1#64, _, sq, ()) m3 hm3
                    (PolicyStep.refl s1) hlen3 ⟨rfl, by rw [hsl_eq]; exact hs_lt, by omega⟩
                · exact hJsib s1 (root <<< 1#64 + 1#64, _, cq, ()) m3 hm3
                    (PolicyStep.refl s1) hlen3 ⟨rfl, by rw [hch1]; exact hch_lt, by omega⟩
                · exact hJsib s1 (root <<< 1#64 + 1#64, _, cq, ()) m3 hm3
                    (PolicyStep.refl s1) hlen3 ⟨rfl, by rw [hch1]; exact hch_lt, by omega⟩
              · intro _ hJsq
                c0_hsteps_nogrp
                · have hidx : ((root <<< 1#64).toNat + 1 + 1) % 2 ^ 64 =
                      (root <<< 1#64 + 1#64 + 1#64).toNat := by bv_omega
                  simp only [hidx] at hc
                  have hsl_qs :
                      s1.scratch.work_stk1[(root <<< 1#64 + 1#64 + 1#64).toNat].toNat <
                        s1.scratch.q_stamp.length := by
                    rw [hlen2.scratch_ok.q_stamp_len]; omega
                  refine wp_load_of (FullArenaTactics.c0_load_full_q_stamp
                    (by rwa [zext32_toNat_ex]) hm2) ?_
                  exact hJsq s1 (_, ()) m2 hm2 (PolicyStep.refl s1) hlen2 rfl
                · exact hJsq s1 (0#32, ()) m2 hm2 (PolicyStep.refl s1) hlen2 rfl
            · exact hJsib s1 (root <<< 1#64 + 1#64, _, cq, ()) m2 hm2
                (PolicyStep.refl s1) hlen2 ⟨rfl, by rw [hch1]; exact hch_lt, by omega⟩
        · intro _ hJcq
          c0_hsteps_nogrp
          · have hidx : ((root <<< 1#64).toNat + 1) % 2 ^ 64 =
                (root <<< 1#64 + 1#64).toNat := by bv_omega
            simp only [hidx] at hc
            have hcl_qs : s1.scratch.work_stk1[(root <<< 1#64 + 1#64).toNat].toNat <
                s1.scratch.q_stamp.length := by
              rw [hlen1.scratch_ok.q_stamp_len]; omega
            refine wp_load_of (FullArenaTactics.c0_load_full_q_stamp
              (by rwa [zext32_toNat_ex]) hm1) ?_
            exact hJcq s1 (_, ()) ml hm1 (PolicyStep.refl s1) hlen1 rfl
          · exact hJcq s1 (0#32, ()) ml hm1 (PolicyStep.refl s1) hlen1 rfl
      · cases hc
    · intro B L _ hL
      c0_hsteps
      exact hL s (start, ()) m hm (PolicyStep.refl s) hlen ⟨hstn, rfl⟩

/-- `full_bump_sort_stamps_m7` satisfies `m7BumpSortPolicySpec` using `wp_policy_loop` and
`wp_policy_call` (ZERO heap/perm/sortedness obligations). -/
theorem full_bump_sort_stamps_m7_policy_wp (Γ : Env)
    (hSift : ∀ a m Q X, m7BumpSiftPolicySpec a m Q X →
      Γ "full_bump_sift_m7" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, m7BumpSortPolicySpec a m Q X → Func.wp Γ full_bump_sort_stamps_m7_body a m Q X := by
  refine wp_policy_intro fun c (h, n, ()) s R m Q X hpre hlen hm hk => ?_
  subst hpre
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmax
  c0_hsteps_nogrp
  · exact hk () s m (PolicyStep.refl s) hlen trivial hm
  · exact hk () s m (PolicyStep.refl s) hlen trivial hm
  · exact hk () s m (PolicyStep.refl s) hlen trivial hm
  · have hn_gt1 : 1 < n.toNat := by c0_bound
    have hncv : n.toNat ≤ s.core.cur_vars := by c0_bound
    have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
    refine wp_policy_loop (ts := [i64]) c s R (fun _ (st, ()) => st.toNat ≤ n.toNat / 2)
      (fun _ (st, ()) => st.toNat) ?_ ?_
    · intro J hJ
      c0_hsteps
      have hhalf : (n >>> 1#64).toNat = n.toNat / 2 := by
        simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      exact hJ s (n >>> 1#64, ()) m hm (PolicyStep.refl s) hlen
        (by dsimp only; rw [hhalf]; exact Nat.le_refl _)
    · rintro J s1 ⟨st, ⟨⟩⟩ ml hp1 hlen1 hst_le hm1 hJ
      c0_hsteps_nogrp
      · have hst_pos : 0 < st.toNat := by c0_bound
        refine wp_policy_call hSift (PolicyStep.refl s1) rfl hlen1 hm1 ?_
        intro ⟨⟩ s2 m2 hp2 _ hlen2 _ hm2
        exact hJ s2 (st - 1#64, ()) m2 hm2 (by dsimp only; bv_omega)
          hp2 hlen2 (by dsimp only; bv_omega)
      · refine wp_policy_loop (ts := [i64]) c s1 R
          (fun _ (ev, ()) => 1 ≤ ev.toNat ∧ ev.toNat ≤ n.toNat)
          (fun _ (ev, ()) => ev.toNat) ?_ ?_
        · intro Je hJe
          c0_hsteps
          exact hJe s1 (n, ()) ml hm1 (PolicyStep.refl s1) hlen1 ⟨by omega, Nat.le_refl _⟩
        · rintro Je s2 ⟨ev, ⟨⟩⟩ m2 hp2 hlen2 ⟨he1, hen⟩ hm2 hJe
          c0_hsteps_nogrp
          · have hev_gt1 : 1 < ev.toNat := by c0_bound
            have hev_sub : (ev - 1).toNat = ev.toNat - 1 := by bv_omega
            have h0_wl : 0 < s2.scratch.work_stk1.length := by
              rw [hlen2.scratch_ok.work_stk1_len]; omega
            have hev_wl : (ev - 1).toNat < s2.scratch.work_stk1.length := by
              rw [hlen2.scratch_ok.work_stk1_len, hev_sub]; omega
            have hset_wl : (ev - 1).toNat <
                (s2.scratch.work_stk1.set 0 s2.scratch.work_stk1[(ev - 1).toNat]).length := by
              rw [List.length_set]; exact hev_wl
            clear hm hm1
            c0_hsteps_nogrp
            refine wp_policy_call (s0 := s2) hSift ?hp3 rfl ?hlen3 (by assumption) ?_
            case hp3 => exact PolicyStep.with_scratch (PolicyStep.refl s2) rfl rfl
            case hlen3 => exact lengthsOk_ws1_swap_ex hlen2
            intro ⟨⟩ s4 m4 hp4 _ hlen4 _ hm4
            exact hJe s4 (ev - 1, ()) m4 hm4 (by dsimp only; rw [hev_sub]; omega)
              hp4 hlen4 (by dsimp only; rw [hev_sub]; omega)
          · exact hk () s2 m2 (hp1.trans hp2) hlen2 trivial hm2

end ExampleProofs

/-! ## 2. Closed Sub-Module `ModuleOk`, `FullM6HdrInv` Soundness Lift & Concrete NV -/

/-- Closed 2-fn sub-module demonstrating `PolicyFrame` table composition (`full_bump_sift_m7`,
`full_bump_sort_stamps_m7`). -/
def m7BumpPolicyFns : List Fn :=
  [full_bump_sift_m7, full_bump_sort_stamps_m7]

def m7BumpPolicyModule : LeanQbe.T.Module :=
  { fns := m7BumpPolicyFns, externs := [], exits := [] }

theorem m7BumpPolicy_acyclic : m7BumpPolicyModule.checkAcyclic = true := by
  t_kernel_rfl

/-- `noExit = true` `SpecEntry` table built directly via `PolicyFrameSpec.specEntry`. -/
def m7BumpPolicyTable : List SpecEntry :=
  [ PolicyFrameSpec.specEntry full_bump_sift_m7 (fun c (h, _, _, ()) _ => h = c.hdr)
  , PolicyFrameSpec.specEntry full_bump_sort_stamps_m7 (fun c (h, _, ()) _ => h = c.hdr)
  ]

def m7BumpPolicyEnv : Env := Env.ofTable m7BumpPolicyTable

theorem m7BumpPolicyTable_nodup : (m7BumpPolicyTable.map SpecEntry.name).Nodup := by
  decide

theorem m7BumpPolicy_noExit :
    ∀ f as bs xs m Q X X',
      m7BumpPolicyEnv f as bs xs m Q X → m7BumpPolicyEnv f as bs xs m Q X' :=
  Env.ofTable_noExit fun e he => by
    simp only [m7BumpPolicyTable, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> rfl

theorem m7BumpPolicy_tableImpl :
    TableImpl m7BumpPolicyEnv m7BumpPolicyFns m7BumpPolicyTable := by
  have hSift := policy_table_row_at (tbl := m7BumpPolicyTable) (idx := 0)
    (fn := full_bump_sift_m7) (Pre := fun c (h, _, _, ()) _ => h = c.hdr)
    rfl m7BumpPolicyTable_nodup
  exact
    ⟨PolicyFrameSpec.tableImpl_of (full_bump_sift_m7_policy_wp m7BumpPolicyEnv),
     PolicyFrameSpec.tableImpl_of (full_bump_sort_stamps_m7_policy_wp m7BumpPolicyEnv hSift),
     trivial⟩

theorem m7BumpPolicy_moduleOk : ModuleOk m7BumpPolicyEnv m7BumpPolicyModule :=
  Env.ofTable_moduleOk m7BumpPolicy_acyclic
    ⟨full_bump_sift_m7_wf, full_bump_sort_stamps_m7_wf, trivial⟩
    m7BumpPolicy_tableImpl

/-- **FullM6 UNSAT Soundness Lift (Tier P1)**:
calling `full_bump_sort_stamps_m7` from any `FullM6HdrInv c F0 ext s` state automatically
transports `FullM6HdrInv c F0 ext s'` and guarantees `s'.core.inconsistent ≠ 0#64 → F0.Unsat`. -/
theorem m7_bump_sort_m6HdrInv_unsat {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {n : BitVec 64}
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    wp (rs := []) m7BumpPolicyEnv
      (fun () m' => ∃ s', FullM6HdrInv c F0 ext s' ∧
        (s'.core.inconsistent ≠ 0#64 → F0.Unsat) ∧ (FullM6HdrMem c ext s' ⋆ R) m')
      (fun _ _ _ _ => False)
      (.call (as := [i64, i64]) (bs := []) "full_bump_sort_stamps_m7"
        (Arg.var c.hdr, Arg.var n, ())
        (fun (_ : Tup Val []) => (.ret () : Expr Val Cont []))) m := by
  have hSort := policy_table_row_at (tbl := m7BumpPolicyTable) (idx := 1)
    (fn := full_bump_sort_stamps_m7) (Pre := fun c (h, _, ()) _ => h = c.hdr)
    rfl m7BumpPolicyTable_nodup
  refine wp_policy_call_m6HdrInv hSort hinv rfl hm ?_
  intro ⟨⟩ s' m' hinv' _ _ hm'
  exact ⟨s', hinv', fullM6HdrInv_inconsistent_unsat hinv', hm'⟩

/-- **FullM6 UNSAT Soundness Lift (Tier P2)**:
calling any `PolicyDeleteSpec` callee (`reduce`, `tumble`, `arena_sweep`, etc.) from
`FullM6HdrInv c F0 ext s` transports `FullM6HdrInv c F0 ext s'` and preserves `F0.Unsat`. -/
theorem m7_policyDelete_m6HdrInv_unsat {Γ : Env} {f : Sym} {as bs : List Ty}
    {Pre : FullCfg → Tup Val as → FullState → Prop}
    {PostFn : FullCfg → Tup Val as → Tup Val bs → FullState → FullState → Prop}
    {args : Tup (Arg Val) as} {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hCallee : ∀ xs m Q X, PolicyDeleteSpec Pre PostFn xs m Q X → Γ f as bs xs m Q X)
    (hinv : FullM6HdrInv c F0 ext s) (hpre : Pre c (vals args) s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    wp (rs := []) Γ (fun () m' => ∃ s', FullM6HdrInv c F0 ext s' ∧
        (s'.core.inconsistent ≠ 0#64 → F0.Unsat) ∧ (FullM6HdrMem c ext s' ⋆ R) m')
      (fun _ _ _ _ => False)
      (.call (as := as) (bs := bs) f args (fun _ => (.ret () : Expr Val Cont []))) m := by
  refine wp_policyDelete_call_m6HdrInv hCallee hinv hpre hm ?_
  intro _ s' m' hinv' _ _ hm'
  exact ⟨s', hinv', fullM6HdrInv_inconsistent_unsat hinv', hm'⟩

section ConcreteNV

private theorem nv_f0_unsat : nvOneLitF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by dsimp only [nvOneLitF0]; simp [cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by dsimp only [nvOneLitF0]; simp [cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1
  simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

private theorem nv_witness :
    FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState.core := by
  have hrefs : fullArenaClauseRefsCore nvOneLitState.core = [] := rfl
  have hcv : nvOneLitState.core.cur_vars = 1 := rfl
  have hte : nvOneLitState.core.trail_end = 1 := rfl
  have hcl : nvOneLitState.core.cur_level = 0 := rfl
  have hdm : nvOneLitState.core.dense_mode = 0#64 := rfl
  have hwat : ModeWatchesInv [[0], [1]] nvOneLitState.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_) (fun l1 _ h1 _ _ hp => ?_)
      (fun l hl => ?_)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvOneLitState] at hp)
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvOneLitState] at hp)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        exact WatchSliceOk.empty
  exact
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl, fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr,
        fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr⟩
      watches := hwat
      cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hte] at hi hj; omega
      vals_domain := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [nvOneLitState]
      vals_true_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
        · constructor
          · intro h; cases h
          · rintro ⟨i, hi, h⟩; rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h
      vals_false_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · constructor
          · intro h; cases h
          · rintro ⟨i, hi, h⟩; rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
      lvl_le := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact Nat.le_refl 0
      dec_earliest := fun _ j _ hj _ hpos => by
        rw [hte] at hj; obtain rfl : j = 0 := (by omega); exact absurd hpos.1 (by decide)
      levels_inhabited := fun _ _ h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega)
        rw [CNF.entails_clause_def]
        intro α hα
        exact absurd (show CNF.Sat α nvOneLitF0 from hα) (CNF.unsat_iff_not_sat.mp nv_f0_unsat α)
      trail_pos_inv := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      level0_rsn_none := fun i hi _ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      frame_trail_lt := fun L hL => by rw [hcl] at hL; obtain rfl : L = 0 := (by omega); decide
      frame_trail_mono := fun L1 L2 _ hL2 => by
        rw [hcl] at hL2; obtain rfl : L1 = 0 := (by omega)
        obtain rfl : L2 = 0 := (by omega); exact Nat.le_refl _
      frame_trail_before_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne
      reason_lit_mem := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne }

/-- Concrete `Mem 64` non-vacuity (`XPost := False`): executing
`full_bump_sort_stamps_m7` on `nvOneLitState` returns with `nvOneLitF0.Unsat` and
`FullSparseInv`. -/
theorem nv_policy_bump_sort :
    Func.wp m7BumpPolicyEnv full_bump_sort_stamps_m7_body (nvOneLitCfg.hdr, 1#64, ()) nvOneLitMem
      (fun () m' => ∃ s' : FullState,
        FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  have hrefs : fullArenaClauseRefs nvOneLitState = [] := rfl
  have hinv : FullSparseInv nvOneLitCfg nvOneLitF0 nvOneLitState := by
    refine ⟨⟨nvOneLit_lengths, [[0], [1]], nv_witness⟩, ?_, fun _ hr => by simp [hrefs] at hr,
      ⟨FullLastLearnedWf.of_cleared fun i hi => by
        simp only [nvOneLitState, nvOneLitScratch, List.getElem?_replicate, show i < 16 by omega,
          ↓reduceIte, Option.getD_some], Nat.le_refl 0⟩,
      rfl⟩
    refine ⟨fun v hv => by
        have h0 : v = 0 := by change v < 1 at hv; omega
        subst h0; rfl,
      fun l hl => by
        have h01 : l = 0 ∨ l = 1 := by change l < 2 at hl; omega
        rcases h01 with rfl | rfl <;> rfl⟩
  have hSort := full_bump_sort_stamps_m7_policy_wp m7BumpPolicyEnv
    (policy_table_row_at (tbl := m7BumpPolicyTable) (idx := 0)
      (fn := full_bump_sift_m7) (Pre := fun c (h, _, _, ()) _ => h = c.hdr)
      rfl m7BumpPolicyTable_nodup)
  refine hSort (nvOneLitCfg.hdr, 1#64, ()) nvOneLitMem _ _ ⟨nvOneLitCfg, nvOneLitState, emp,
    rfl, hinv.lengths, hm, fun () s' m' hp hlen' _ hm' => ?_⟩
  rw [sep_emp] at hm'
  exact ⟨s', fullSparseInv_of_policyStep hinv hlen' hp, nv_f0_unsat, hm'⟩

end ConcreteNV

end LeanQbe.T.Examples.Kissat.PolicyFrameExample

/-! ## 3. Short Root-Namespace Audit Aliases (`< 115`-Char Single-Line `#print axioms`) -/

section AxiomAudit

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM7Bump
open LeanQbe.T.Examples.Kissat.PolicyFrame
open LeanQbe.T.Examples.Kissat.PolicyFrameExample
open Kraken.Bedrock2.Test

theorem pf_ex_sift_wp (Γ : Env) :
    ∀ a m Q X, m7BumpSiftPolicySpec a m Q X →
      Func.wp Γ full_bump_sift_m7_body a m Q X :=
  full_bump_sift_m7_policy_wp Γ

theorem pf_ex_sort_wp (Γ : Env)
    (hSift : ∀ a m Q X, m7BumpSiftPolicySpec a m Q X →
      Γ "full_bump_sift_m7" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, m7BumpSortPolicySpec a m Q X →
      Func.wp Γ full_bump_sort_stamps_m7_body a m Q X :=
  full_bump_sort_stamps_m7_policy_wp Γ hSift

theorem pf_ex_mod_ok : ModuleOk m7BumpPolicyEnv m7BumpPolicyModule :=
  m7BumpPolicy_moduleOk

theorem pf_ex_sort_unsat {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {n : BitVec 64}
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    wp (rs := []) m7BumpPolicyEnv
      (fun () m' => ∃ s', FullM6HdrInv c F0 ext s' ∧
        (s'.core.inconsistent ≠ 0#64 → F0.Unsat) ∧ (FullM6HdrMem c ext s' ⋆ R) m')
      (fun _ _ _ _ => False)
      (.call (as := [i64, i64]) (bs := []) "full_bump_sort_stamps_m7"
        (Arg.var c.hdr, Arg.var n, ())
        (fun (_ : Tup Val []) => (.ret () : Expr Val Cont []))) m :=
  m7_bump_sort_m6HdrInv_unsat hinv hm

theorem pf_ex_del_unsat {Γ : Env} {f : Sym} {as bs : List Ty}
    {Pre : FullCfg → Tup Val as → FullState → Prop}
    {PostFn : FullCfg → Tup Val as → Tup Val bs → FullState → FullState → Prop}
    {args : Tup (Arg Val) as} {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hCallee : ∀ xs m Q X, PolicyDeleteSpec Pre PostFn xs m Q X → Γ f as bs xs m Q X)
    (hinv : FullM6HdrInv c F0 ext s) (hpre : Pre c (vals args) s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    wp (rs := []) Γ (fun () m' => ∃ s', FullM6HdrInv c F0 ext s' ∧
        (s'.core.inconsistent ≠ 0#64 → F0.Unsat) ∧ (FullM6HdrMem c ext s' ⋆ R) m')
      (fun _ _ _ _ => False)
      (.call (as := as) (bs := bs) f args (fun _ => (.ret () : Expr Val Cont []))) m :=
  m7_policyDelete_m6HdrInv_unsat hCallee hinv hpre hm

theorem pf_ex_nv_sort :
    Func.wp m7BumpPolicyEnv full_bump_sort_stamps_m7_body (nvOneLitCfg.hdr, 1#64, ()) nvOneLitMem
      (fun () m' => ∃ s' : FullState,
        FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nv_policy_bump_sort

#print axioms pf_ex_sift_wp
#print axioms pf_ex_sort_wp
#print axioms pf_ex_mod_ok
#print axioms pf_ex_sort_unsat
#print axioms pf_ex_del_unsat
#print axioms pf_ex_nv_sort

end AxiomAudit
