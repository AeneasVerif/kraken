module

public import LeanQbe.T.Examples.Kissat.FullM6TiersProof0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.ControlComb
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat M6 Tiers `Func.wp` Proofs — Part 1a (`FullM6TiersProof1a`)

Proves `Func.wp` (strictly UNSAT-only, ZERO SAT/model proofs) for the first `5` M6
orchestrator upgrades in `FullM6Tiers`:
1. `full_switch_mode_m6` against `Full.fullSwitchModeSpec` (`focused`/`stable` tick watermarks).
2. `full_rephase_m6` against `m6RephaseSpec` (reducing to `Full.fullRephaseSpec` on `stable ≠ 0`).
3. `full_reduce_m6` against `Full.fullReduceSpec` (calling `full_recompute_tiers_m6` + watermarks).
4. `full_analyze_rsn_m6` against `Full.fullAnalyzeRsnSpec` (recording glue histograms on learned).
5. `full_analyze_m6` against `Full.fullAnalyzeSpec` (updating interval-doubled glue tier limits).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM6Tiers

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped FullArenaTactics
open Kraken.Bedrock2.Test

/-! ## 1. Specs & Pure Adapters -/

/-- M6 `full_rephase` contract: matches `Full.fullRephaseSpec` when `stable ≠ 0#64`, and updates
`rephase_limit := mode_confl_lim` cleanly when `stable = 0#64`. -/
def m6RephaseSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullCoreInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ vals' lvl' rsns' trl' tp' te' prop' cl' unass' fuel' sc' m',
      let s' : FullState :=
        { core := { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                                trail_pos := tp', trail_end := te', propagated := prop',
                                cur_level := cl', unassigned := unass', fuel := fuel' }
          scratch := sc' }
      FullCoreInv c F0 s' → (s.scratch.stable ≠ 0#64 → cl' = 0) →
      cl' ≤ s.core.cur_level → fuel'.toNat ≤ s.core.fuel.toNat →
      FullExtScratchPres s s' → (FullMem c s' ⋆ R) m' → Q () m'

/-- When `s.scratch.stable ≠ 0#64`, `m6RephaseSpec` coincides with `Full.fullRephaseSpec`. -/
theorem m6RephaseSpec_of_stable {h : BitVec 64} {m : Mem 64} {Q : Post []} {X : XPost}
    (hc : ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.scratch.stable ≠ 0#64 ∧ FullCoreInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
      ∀ vals' lvl' rsns' trl' tp' te' prop' unass' fuel' sc' m',
        let s' : FullState :=
          { core := { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                                  trail_pos := tp', trail_end := te', propagated := prop',
                                  cur_level := 0, unassigned := unass', fuel := fuel' }
            scratch := sc' }
        FullCoreInv c F0 s' → fuel'.toNat ≤ s.core.fuel.toNat → FullExtScratchPres s s' →
        (FullMem c s' ⋆ R) m' → Q () m') :
    m6RephaseSpec (h, ()) m Q X := by
  rcases hc with ⟨c, F0, s, R, rfl, hst, hinv, hm, hQ⟩
  refine ⟨c, F0, s, R, rfl, hinv, hm, fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' fuel' sc'
      m' hinv' hcl _ hfu' hpres' hm' => ?_⟩
  have hcl0 : cl' = 0 := hcl hst
  subst hcl0
  exact hQ vals' lvl' rsns' trl' tp' te' prop' unass' fuel' sc' m' hinv' hfu' hpres' hm'

private theorem bv64_add1_toNat_m6 {k : BitVec 64} (hk : k.toNat + 1 < 2 ^ 64) :
    (k + 1#64).toNat = k.toNat + 1 := by
  bv_omega

private theorem fullSparseInvW_of_safetySlice {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState}
    (hsp : FullSparseInvW c F0 F_cur s) (hlen' : s'.LengthsOk c)
    (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hpres : FullExtScratchPres s s') : FullSparseInvW c F0 F_cur s' := by
  have heq : s'.core = s.core := fullCoreState_agrees_with_scratch hcore
  refine ⟨hlen', ?_, ?_, ?_, ?_, heq ▸ hsp.2.2.2.2.2⟩
  · rw [heq]; exact hsp.2.1
  · unfold FullLitMarksClear FullMrkZero; rw [heq]; exact hsp.2.2.1
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    rw [heq]; exact hsp.2.2.2.1
  · exact hsp.2.2.2.2.1.of_pres hpres fun r hr => by unfold fullArenaClauseRefs; rwa [heq]

private theorem fullAnaMarksCov_of_safetySlice {c : FullCfg} {s s' : FullState}
    (h : FullAnaMarksCov c s) (heq : s'.core = s.core)
    (hws1 : s'.scratch.work_stk1 = s.scratch.work_stk1) : FullAnaMarksCov c s' := by
  unfold FullAnaMarksCov at h ⊢; rwa [heq, hws1]

private theorem fullConflictOkW_of_coreEq {F_cur : List (List Nat)} {s s' : FullState}
    (h : FullConflictOkW F_cur s) (heq : s'.core = s.core) : FullConflictOkW F_cur s' := by
  unfold FullConflictOkW fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits at h ⊢
  rwa [heq]

private theorem fullWitnessCutInv_of_coreEq {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {s s' : FullState}
    (h : FullWitnessCutInv c F0 F_cur cut s.core) (heq : s'.core = s.core) :
    FullWitnessCutInv c F0 F_cur cut s'.core := by
  rwa [heq]

/-! ## 2. Local Tactics (`FullM6Proof1a`) -/

section M6Proof1aTactics

open Lean Elab Tactic in
local elab "m6_to_group" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let rawTy ← Lean.instantiateMVars (← g.getType)
      let ty := rawTy.consumeMData
      if rawTy.isMData then
        let g' ← g.change ty (checkDefEq := false)
        setGoals [g']
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.group then
        out := out ++ (← getUnsolvedGoals)
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out ++ (← getUnsolvedGoals)
    setGoals out.toList
  go 500

open Lean Elab Tactic in
local elab "m6_split" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let g ← getMainGoal
    let rawTy ← Lean.instantiateMVars (← g.getType)
    let ty := rawTy.consumeMData
    if rawTy.isMData then
      let g' ← g.change ty (checkDefEq := false)
      replaceMainGoal [g']
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
      let _ ← LeanQbe.T.C0Step.stepOnce; return
    if ← LeanQbe.T.C0Step.stepOnce then go (fuel - 1)
  go 100

private theorem wp_let_ult64_m6a {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {hm : Ty.bool = Ty.mask i64} {a b : Arg Val i64}
    {k : Tup Val [.bool] → Expr Val Cont rs} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult i64 .bool hm) (a, b, ())) k) m =
      wp Γ Q X (k (BitVec.ult a.val b.val, ())) m := by
  have hc := @wp_let_cmp_eq Γ rs Q X m .ult i64 .bool hm (a, b, ()) k
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, liftCmp,
    evalBits_ult_eq, cast_eq] using hc

/-! ## 3. `full_switch_mode_m6` `Func.wp` Proof -/

theorem full_switch_mode_m6_wp (Γ : Env)
    (hDown : ∀ a m Q X, fullHeapDownSpec a m Q X → Γ "full_heap_down" [i64, i32] [] a m Q X)
    (hReady : ∀ a m Q X, m6ExtReadySpec a m Q X →
      Γ "full_m6_ext_ready" [i64] [.bool] a m Q X)
    (hGetWm : ∀ a m Q X, m6GetWmSpec a m Q X →
      Γ "full_m6_get_watermark" [i64, i64] [i64] a m Q X)
    (hSetWm : ∀ a m Q X, m6SetWmSpec a m Q X →
      Γ "full_m6_set_watermark" [i64, i64, i64] [] a m Q X)
    (hLog : ∀ a m Q X, m6Log10Q16Spec a m Q X →
      Γ "full_log10_q16_m6" [i64] [i64] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullSwitchModeSpec a m Q X →
      Func.wp Γ full_switch_mode_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  obtain hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmax
  obtain hcv_le := hlen.core_ok.cur_vars_le
  m6_to_group
  refine wp_join_safety_slice (fullSafetySlice c) s R (fun _ => True) trivial
    (fun s1 _ => FullProbeScratchPres s s1)
    (fun J_out s1 _ m1 hcore1 hs1 _ hpres1 hm1 => ?_) (fun J_out hJ_out => ?_)
  · dsimp only [fullSafetySlice] at hs1 hm1
    clear hm
    let s1a : FullState :=
      { s1 with scratch :=
        { s1.scratch with
          switched := s1.scratch.switched + 1#64
          mode_count := s1.scratch.mode_count + 1#64
          ema_fast_biased := 0#64
          ema_fast_exp := 1#64 <<< 32
          ema_slow_biased := 0#64
          ema_slow_exp := 1#64 <<< 32 } }
    c0_hsteps_nogrp
    refine wp_unroll_group fun Jret hJret => ?_
    c0_hsteps_nogrp
    · refine wp_join_group (ts := [i64]) (fun _ m2 => (FullMem c s1a ⋆ R) m2)
        (fun _ (delta, ()) m2 hm2 => ?_) ?_
      · c0_hsteps
        try (apply hJret; rw [Blocks.get_here]; c0_hsteps)
        let s2 : FullState :=
          { s1a with
            scratch := { s1a.scratch with restart_limit := s1a.scratch.conflicts + delta } }
        exact hQ () s2 _ hcore1
          (hs1.with_scratch { hs1.scratch_ok with walk_vals_len := hs1.scratch_ok.walk_vals_len })
          hpres1 (by assumption)
      · intro _ hJd
        c0_hsteps_nogrp
        · refine wp_join_group (ts := [i64]) (fun _ m2 => (FullMem c s1a ⋆ R) m2)
            (fun _ (rc, ()) m2 hm2 => ?_) ?_
          · c0_hsteps_nogrp
            c0_call hIlog
            intro d10 _ _
            c0_hsteps
            · exact hJd (d10 - 1#64, ()) _ hm2
            · exact hJd (1#64, ()) _ hm2
          · intro _ hJrc; c0_hsteps
            · exact hJrc (s1a.scratch.restarts, ()) _ (by assumption)
            · exact hJrc (1000000000000#64, ()) _ (by assumption)
        · exact hJd (1#64, ()) _ (by assumption)
    · try (apply hJret; rw [Blocks.get_here]; c0_hsteps)
      exact hQ () s1a _ hcore1
        (hs1.with_scratch { hs1.scratch_ok with walk_vals_len := hs1.scratch_ok.walk_vals_len })
        hpres1 (by assumption)
  · m6_split
    · m6_split
      · c0_steps; exact hQ () s m rfl hlen (probePres_refl_m6 s) hm
      · clear hQ
        c0_hsteps_nogrp
        let s0a : FullState := { s with scratch := { s.scratch with stable := 1#64 } }
        refine wp_join_safety_slice (ts := [i64]) (fullSafetySlice c) s0a R (fun _ => True) trivial
          (fun s0 _ => FullProbeScratchPres s s0)
          (fun _ s0 (dticks, ()) m0 hcore0 hs0 _ hpres0 hm0 => ?_)
          (fun _ hJdt => ?_)
        · dsimp only [fullSafetySlice] at hs0 hm0
          refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s0 R
            (fun _ => True) trivial (fun s1 _ => FullProbeScratchPres s s1)
            (fun _ s1 _ m1 hcore1 hs1 _ hpres1 hm1 => ?_)
            (fun _ hJwm => ?_)
          · clear hm hlen hm0
            dsimp only [fullSafetySlice] at hs1 hm1
            c0_hsteps_nogrp
            let s1m : FullState :=
              { s1 with scratch :=
                { s1.scratch with
                  mode_tick_lim := s1.scratch.search_ticks + dticks
                  mode_saved_ticks := s1.scratch.search_ticks } }
            have hs1m : s1m.LengthsOk c := hs1.with_scratch
              { hs1.scratch_ok with walk_vals_len := hs1.scratch_ok.walk_vals_len }
            refine wp_join_safety_slice (ts := [i64]) (fullSafetySlice c) s1m R
              (fun _ => True) trivial (fun s1r _ => FullProbeScratchPres s s1r)
              (fun _ s1r (rp, ()) m1r hcore1r hs1r _ hpres1r hm1r => ?_)
              (fun _ hJrp => ?_)
            · dsimp only [fullSafetySlice] at hs1r hm1r
              have heq1 := fullCoreState_agrees_with_scratch hcore1r
              c0_hsteps_nogrp
              let s1' : FullState :=
                { s1r with scratch :=
                  { s1r.scratch with
                    rel_wait := rp, rel_u := 1#64, rel_v := 1#64, rel_trigger := 0#64 } }
              refine wp_loop_safety_slice (ts := [i64, i64]) (fullSafetySlice c) s1' R
                (fun _ => True) trivial
                (fun s2 (n, v, ()) => n.toNat ≤ v.toNat ∧
                  v.toNat ≤ s.core.cur_vars ∧ FullProbeScratchPres s s2)
                (fun (_, (v : BitVec 64), ()) => s.core.cur_vars - v.toNat)
                (fun Jl hJl => ?_)
                (fun Jl s2 (n, v, ()) m2 hcore2 hs2 _ ⟨hnle, hvle, hpres2⟩ hm2 hJl => ?_)
              · c0_steps
                refine hJl _ (0#64, 0#64, ()) _ (by assumption) rfl ?_ ⟨by simp, by simp, hpres1r⟩
                exact hs1r.with_scratch
                  { hs1r.scratch_ok with walk_vals_len := hs1r.scratch_ok.walk_vals_len }
              · dsimp only [fullSafetySlice] at hs2 hm2
                have heq2 := fullCoreState_agrees_with_scratch hcore2
                obtain hfl2 := hs2.core_ok.flags_len
                obtain hvl2 := hs2.core_ok.vals_len
                obtain hhl2 := hs2.scratch_ok.heap_len_arr
                obtain hpl2 := hs2.scratch_ok.pos_len
                repeat clear hc
                rw [Blocks.get_here]; dsimp only
                rw [wp_let_ult64_m6a]
                refine wp_jnz_of (fun hc => ?_) (fun hc => ?_)
                · simp only [Arg.val_var] at hc; c0_cond hc
                  have hv_lt : v.toNat < s.core.cur_vars := by
                    have hcs1 : s1.core = s.core :=
                      (fullCoreState_agrees_with_scratch hcore1).trans
                        (fullCoreState_agrees_with_scratch hcore0)
                    rw [heq1, hcs1] at hc
                    first | exact hc | {
                      have hc_v' : v.toNat < (BitVec.ofNat 64 s.core.cur_vars).toNat := by
                        simpa using hc
                      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc_v'
                      exact hc_v' }
                  have hv_fl : v.toNat < s2.core.flags.length := by rw [hfl2]; omega
                  have hv1 : (v + 1#64).toNat = v.toNat + 1 := by bv_omega
                  refine wp_join_safety_slice (ts := [i64]) (fullSafetySlice c) s2 R
                    (fun _ => True) trivial
                    (fun s2' (n', ()) => n'.toNat ≤ v.toNat + 1 ∧ FullProbeScratchPres s s2')
                    (fun Js s2' (n', ()) m2' hcore2' hs2' _ ⟨hn'le, hpres2'⟩ hm2' => ?_)
                    (fun Js hJs => ?_)
                  · dsimp only [fullSafetySlice] at hs2' hm2'
                    c0_steps
                    exact hJl s2' (n', v + 1#64, ()) m2' hm2' (by dsimp only; rw [hv1]; omega)
                      hcore2' hs2' ⟨by rw [hv1]; omega, by rw [hv1]; omega, hpres2'⟩
                  · dsimp only [fullSafetySlice] at hJs
                    refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s2 R
                      (fun _ => True) trivial (fun s2' _ => FullProbeScratchPres s s2')
                      (fun Js1 s2' _ m2' hcore2' hs2' _ hpres2' hm2' => ?_)
                      (fun Js1 hJs1 => ?_)
                    · dsimp only [fullSafetySlice] at hs2' hm2'
                      have hv_pos : v.toNat < s2'.scratch.pos.length := by
                        rw [hs2'.scratch_ok.pos_len]; omega
                      rw [Blocks.get_here]; dsimp only
                      c0_steps
                      refine wp_store_sep (c0_store_full_pos _ hv_pos hm2') fun m_p hm_p => ?_
                      c0_steps
                      exact hJs _ (n, ()) _ hm_p hcore2'
                        (hs2'.with_scratch { hs2'.scratch_ok with
                          pos_len := by simp [hs2'.scratch_ok.pos_len] })
                        ⟨by dsimp only; omega, hpres2'⟩
                    · m6_split
                      · have hv2 : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
                          rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
                        have hv2_lt : (v <<< (1 : Nat)).toNat < s2.core.vals.length := by
                          rw [hvl2, hv2]; omega
                        refine wp_load_of (c0_load_full_vals hv2_lt hm2) ?_
                        m6_split
                        · have hn_lt : n.toNat < s2.scratch.heap.length := by rw [hhl2]; omega
                          have hv_pos : v.toNat < s2.scratch.pos.length := by rw [hpl2]; omega
                          have hn1 : (n + 1#64).toNat = n.toNat + 1 := by bv_omega
                          c0_steps
                          refine wp_store_sep (c0_store_full_heap _ hn_lt hm2) fun m_h hm_h => ?_
                          c0_steps
                          let s2hp : FullState :=
                            { s2 with scratch :=
                              { s2.scratch with
                                heap := s2.scratch.heap.set n.toNat (v.setWidth 32)
                                pos := s2.scratch.pos.set v.toNat (n.setWidth 32) } }
                          have hs2hp : s2hp.LengthsOk c :=
                            hs2.with_scratch { hs2.scratch_ok with
                              heap_len_arr := by simp [hhl2], pos_len := by simp [hpl2] }
                          exact hJs s2hp (n + 1#64, ()) _ (by assumption) rfl hs2hp
                            ⟨by dsimp only; rw [hn1]; omega, hpres2⟩
                        · exact hJs1 s2 () m2 hm2 rfl hs2 hpres2
                      · exact hJs1 s2 () m2 hm2 rfl hs2 hpres2
                · clear hJl
                  c0_steps
                  refine wp_loop_safety_slice (fullSafetySlice c)
                    { s2 with scratch := { s2.scratch with heap_len := n.toNat } } R
                    (fun _ => True) trivial
                    (fun s3 (sp, ()) => sp.toNat ≤ c.max_vars ∧ FullProbeScratchPres s s3)
                    (fun (sp, ()) => sp.toNat)
                    (fun Js hJs => ?_)
                    (fun Js s3 (sp, ()) m3 hcore3 hs3 _ ⟨hsple, hpres3⟩ hm3 hJs => ?_)
                  · c0_steps
                    refine hJs _ (n >>> (1 : Nat), ()) _ (by assumption) rfl
                      (hs2.with_scratch
                        { hs2.scratch_ok with walk_vals_len := hs2.scratch_ok.walk_vals_len })
                      ⟨by rw [BitVec.toNat_ushiftRight]; simp [Nat.shiftRight_eq_div_pow]; omega,
                        hpres2⟩
                  · dsimp only [fullSafetySlice] at hs3 hm3
                    obtain hhl3 := hs3.scratch_ok.heap_len_arr
                    c0_steps
                    · have hsp_pos : 0 < sp.toNat := by omega
                      have hsm1 : (sp - 1#64).toNat < sp.toNat := by bv_omega
                      c0_call hDown
                      refine ⟨c, s3, R, rfl, hs3, hm3, ?_⟩
                      intro _ s4 m4 hcore4 hs4 ⟨_, hpres34⟩ hm4
                      exact hJs s4 (sp - 1#64, ()) m4 hm4 hsm1 hcore4 hs4
                        ⟨by omega, probePres_trans_m6 hpres3 hpres34⟩
                    · exact hJ_out s3 () m3 hm3
                        (hcore0.trans (hcore1.trans (hcore1r.trans (hcore2.trans hcore3))))
                        hs3 hpres3
            · c0_steps
              · exact hJrp _ (s1m.scratch.rel_limit, ()) _ (by assumption) rfl hs1m hpres1
              · exact hJrp _ (s1m.scratch.rel_period, ()) _ (by assumption) rfl hs1m hpres1
              · exact hJrp _ (s1m.scratch.rel_period, ()) _ (by assumption) rfl hs1m hpres1
          · c0_hsteps_nogrp
            c0_call hReady
            refine ⟨c, s0, R, rfl, hs0, hm0,
              fun ⟨ok, ⟨⟩⟩ s0w m0w hcore0w hs0w hpres0w hm0w => ?_⟩
            dsimp only [fullSafetySlice] at hs0w hm0w
            c0_hsteps_nogrp
            · c0_call hGetWm
              refine ⟨c, s0w, R, rfl, hs0w, hm0w, fun ⟨ft, ⟨⟩⟩ s1 m1 hcore1 hs1 hpres1 hm1 => ?_⟩
              dsimp only [fullSafetySlice] at hs1 hm1
              c0_hsteps_nogrp
              c0_call hSetWm
              refine ⟨c, s1, R, rfl, hs1, hm1, fun () s2 m2 hcore2 hs2 hpres2 hm2 => ?_⟩
              dsimp only [fullSafetySlice] at hs2 hm2
              c0_steps
              exact hJwm s2 () m2 hm2 (hcore0w.trans (hcore1.trans hcore2)) hs2
                (probePres_trans_m6 hpres0
                  (probePres_trans_m6 hpres0w.1.1 (probePres_trans_m6 hpres1.1 hpres2.1)))
            · c0_steps
              exact hJwm s0w () m0w hm0w hcore0w hs0w (probePres_trans_m6 hpres0 hpres0w.1.1)
        · c0_steps
          · exact hJdt _ (_, ()) _ hm rfl
              (hlen.with_scratch
                { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len })
              (probePres_refl_m6 s)
          · exact hJdt _ (_, ()) _ hm rfl
              (hlen.with_scratch
                { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len })
              (probePres_refl_m6 s)
    · m6_split
      · c0_steps; exact hQ () s m rfl hlen (probePres_refl_m6 s) hm
      · clear hQ
        let s0 : FullState := { s with scratch := { s.scratch with stable := 0#64 } }
        c0_hsteps_nogrp
        refine wp_join_safety_slice (ts := [i64]) (fullSafetySlice c) s0 R (fun _ => True) trivial
          (fun s0a _ => FullProbeScratchPres s s0a)
          (fun _ s0a (dticks, ()) m0a hcore0a hs0a _ hpres0a hm0a => ?_)
          (fun _ hJdt => ?_)
        · dsimp only [fullSafetySlice] at hs0a hm0a
          refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s0a R
            (fun _ => True) trivial (fun s1 _ => FullProbeScratchPres s s1)
            (fun _ s1 _ m1 hcore1 hs1 _ hpres1 hm1 => ?_)
            (fun _ hJwm => ?_)
          · clear hm hlen hm0a
            dsimp only [fullSafetySlice] at hs1 hm1 hJ_out
            have hcs1 : s1.core = s.core :=
              (fullCoreState_agrees_with_scratch hcore1).trans
                (fullCoreState_agrees_with_scratch hcore0a)
            m6_to_group
            refine wp_join_group (ts := [i64]) (fun _ m1c => m1c = m1)
              (fun _ (cc, ()) m1c hm1c => ?_) ?_
            · subst m1c; m6_to_group
              c0_call hLog
              intro q _ _
              m6_to_group
              refine wp_join_group (ts := [i64]) (fun _ m2 => m2 = m1)
                (fun _ (scaled, ()) m2 hm2 => ?_) ?_
              · subst m2
                obtain hqsl := hs1.scratch_ok.q_stamp_len
                rw [Blocks.get_here]; dsimp only
                c0_hsteps_nogrp
                refine wp_unroll_group fun Jq hJq => ?_
                have hJq' : ∀ (s' : FullState) (m' : Mem 64),
                    (FullMem c s' ⋆ R) m' → PreservesCoreSlice FullState.core s s' →
                    s'.LengthsOk c → FullProbeScratchPres s s' → Jq () m' :=
                  fun s' m' hm' hc' hl' hp' => hJq () m' (by
                    rw [Blocks.get_here]; c0_hsteps_nogrp
                    exact hJ_out s' () m' hm' hc' hl' hp')
                clear hJq
                have hclose : ∀ (s' : FullState) (m' : Mem 64), (FullMem c s' ⋆ R) m' →
                    s'.core = s1.core →
                    s'.scratch.walk_vals = s1.scratch.walk_vals →
                    s'.scratch.phases = s1.scratch.phases →
                    s'.scratch.phases_target = s1.scratch.phases_target →
                    s'.scratch.phases_best = s1.scratch.phases_best →
                    s'.scratch.walk_best = s1.scratch.walk_best →
                    s'.scratch.heap = s1.scratch.heap →
                    s'.scratch.pos = s1.scratch.pos →
                    s'.scratch.shrink_stk = s1.scratch.shrink_stk →
                    s'.scratch.q_prev = s1.scratch.q_prev →
                    s'.scratch.q_next = s1.scratch.q_next →
                    s'.scratch.q_stamp = s1.scratch.q_stamp →
                    s'.scratch.wsort = s1.scratch.wsort →
                    s'.scratch.work_stk1 = s1.scratch.work_stk1 →
                    s'.scratch.work_stk2 = s1.scratch.work_stk2 →
                    s'.scratch.tarjan_mark = s1.scratch.tarjan_mark →
                    s'.scratch.tarjan_reach = s1.scratch.tarjan_reach →
                    s'.scratch.score = s1.scratch.score →
                    s'.scratch.sim_sig = s1.scratch.sim_sig →
                    s'.scratch.glue_used = s1.scratch.glue_used →
                    s'.scratch.last_learned = s1.scratch.last_learned →
                    s'.scratch.delayed = s1.scratch.delayed →
                    s'.scratch.red_refs = s1.scratch.red_refs →
                    s'.scratch.extend_stk = s1.scratch.extend_stk →
                    s'.scratch.scratch_buf = s1.scratch.scratch_buf →
                    s'.scratch.extend_len = s1.scratch.extend_len →
                    s'.scratch.ant_sz = s1.scratch.ant_sz →
                    s'.scratch.res_sz = s1.scratch.res_sz →
                    Jq () m' := by
                  intro s' m' hm' hc h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
                    h17 h18 h19 h20 h21 h22 h23 h24 hel has hrs
                  have hl' : s'.LengthsOk c :=
                    ⟨by rw [hc]; exact hs1.core_ok,
                     ⟨by rw [h1]; exact hs1.scratch_ok.walk_vals_len,
                      by rw [h2]; exact hs1.scratch_ok.phases_len,
                      by rw [h3]; exact hs1.scratch_ok.phases_target_len,
                      by rw [h4]; exact hs1.scratch_ok.phases_best_len,
                      by rw [h5]; exact hs1.scratch_ok.walk_best_len,
                      by rw [h6]; exact hs1.scratch_ok.heap_len_arr,
                      by rw [h7]; exact hs1.scratch_ok.pos_len,
                      by rw [h8]; exact hs1.scratch_ok.shrink_stk_len,
                      by rw [h9]; exact hs1.scratch_ok.q_prev_len,
                      by rw [h10]; exact hs1.scratch_ok.q_next_len,
                      by rw [h11]; exact hs1.scratch_ok.q_stamp_len,
                      by rw [h12]; exact hs1.scratch_ok.wsort_len,
                      by rw [h13]; exact hs1.scratch_ok.work_stk1_len,
                      by rw [h14]; exact hs1.scratch_ok.work_stk2_len,
                      by rw [h15]; exact hs1.scratch_ok.tarjan_mark_len,
                      by rw [h16]; exact hs1.scratch_ok.tarjan_reach_len,
                      by rw [h17]; exact hs1.scratch_ok.score_len,
                      by rw [h18]; exact hs1.scratch_ok.sim_sig_len,
                      by rw [h19]; exact hs1.scratch_ok.glue_used_len,
                      by rw [h20]; exact hs1.scratch_ok.last_learned_len,
                      by rw [h21]; exact hs1.scratch_ok.delayed_len_arr,
                      by rw [h22]; exact hs1.scratch_ok.red_refs_len,
                      by rw [h23]; exact hs1.scratch_ok.extend_stk_len,
                      by rw [h24]; exact hs1.scratch_ok.scratch_buf_len⟩⟩
                  have hp' : FullProbeScratchPres s s' :=
                    ⟨⟨h20 ▸ hpres1.1.1, hel ▸ hpres1.1.2⟩,
                      h13 ▸ hpres1.2.1, h14 ▸ hpres1.2.2.1, h15 ▸ hpres1.2.2.2.1,
                      h24 ▸ hpres1.2.2.2.2.1, has ▸ hpres1.2.2.2.2.2.1,
                      hrs ▸ hpres1.2.2.2.2.2.2.1, h18 ▸ hpres1.2.2.2.2.2.2.2⟩
                  exact hJq' s' m' hm' ((hcore0a.trans hcore1).trans hc) hl' hp'
                c0_hsplit
                · have hq_ok : s1.scratch.q_last.toNat < s1.scratch.q_stamp.length := by
                    rw [hqsl]
                    have hcv1 : s1.core.cur_vars ≤ c.max_vars := by rw [hcs1]; exact hcv_le
                    c0_cond hc
                    bv_omega
                  c0_hsteps!
                  exact hclose _ _ hm rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                · c0_hsteps!
                  exact hclose _ _ hm rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
              · intro _ hJsc
                m6_split
                · c0_steps; exact hJsc (_, ()) m1 rfl
                · m6_to_group
                  refine wp_join_group (ts := [i64]) (fun _ m2 => m2 = m1)
                    (fun _ (clim, ()) m2 hm2 => ?_) ?_
                  · subst m2; c0_steps; exact hJsc (_, ()) m1 rfl
                  · intro _ hJcl; c0_steps
                    · exact hJcl (100000000#64, ()) m1 rfl
                    · exact hJcl (_, ()) m1 rfl
            · intro _ hJcc; c0_steps
              · exact hJcc (_, ()) m1 rfl
              · exact hJcc (1000000000000#64, ()) m1 rfl
          · c0_hsteps_nogrp
            c0_call hReady
            refine ⟨c, s0a, R, rfl, hs0a, hm0a,
              fun ⟨ok, ⟨⟩⟩ s0w m0w hcore0w hs0w hpres0w hm0w => ?_⟩
            dsimp only [fullSafetySlice] at hs0w hm0w
            c0_hsteps_nogrp
            · c0_call hGetWm
              refine ⟨c, s0w, R, rfl, hs0w, hm0w, fun ⟨st, ⟨⟩⟩ s1 m1 hcore1 hs1 hpres1 hm1 => ?_⟩
              dsimp only [fullSafetySlice] at hs1 hm1
              c0_hsteps_nogrp
              c0_call hSetWm
              refine ⟨c, s1, R, rfl, hs1, hm1, fun () s2 m2 hcore2 hs2 hpres2 hm2 => ?_⟩
              dsimp only [fullSafetySlice] at hs2 hm2
              c0_steps
              exact hJwm s2 () m2 hm2 (hcore0w.trans (hcore1.trans hcore2)) hs2
                (probePres_trans_m6 hpres0a
                  (probePres_trans_m6 hpres0w.1.1 (probePres_trans_m6 hpres1.1 hpres2.1)))
            · c0_steps
              exact hJwm s0w () m0w hm0w hcore0w hs0w (probePres_trans_m6 hpres0a hpres0w.1.1)
        · c0_steps
          · exact hJdt _ (_, ()) _ hm rfl
              (hlen.with_scratch
                { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len })
              (probePres_refl_m6 s)
          · exact hJdt _ (_, ()) _ hm rfl
              (hlen.with_scratch
                { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len })
              (probePres_refl_m6 s)

/-! ## 4. `full_rephase_m6` `Func.wp` Proof -/

theorem full_rephase_m6_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hWalk : ∀ a m Q X, fullWalkSpec a m Q X → Γ "full_walk" [i64] [] a m Q X)
    (hLog : ∀ a m Q X, m6Log10Q16Spec a m Q X →
      Γ "full_log10_q16_m6" [i64] [i64] a m Q X)
    (hSetWm : ∀ a m Q X, m6SetWmSpec a m Q X →
      Γ "full_m6_set_watermark" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, m6RephaseSpec a m Q X → Func.wp Γ full_rephase_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  obtain ⟨F_cur, hw0⟩ := hinv.witness
  have hco0 := hinv.lengths.core_ok
  have hcl_lt64 : s.core.cur_level < 2 ^ 64 := by
    have := hw0.cur_level_le; have := hco0.trail_end_le; have := hco0.cur_vars_le; omega
  have hmaxv_pos : (0 : BitVec 64).toNat < s.core.cur_level →
      (0 : BitVec 64).toNat < c.max_vars := by
    intro _; have := hw0.cur_level_le; have := hco0.trail_end_le
    have := hco0.cur_vars_le; omega
  m6_split
  · c0_hsteps
    let sc_early : FullScratch := { s.scratch with rephase_limit := s.scratch.mode_confl_lim }
    have hsc_early : sc_early.LengthsOk c :=
      { hinv.lengths.scratch_ok with walk_vals_len := hinv.lengths.scratch_ok.walk_vals_len }
    have hinv_e : FullCoreInv c F0
        { core := { s.core with fuel := s.core.fuel }, scratch := sc_early } :=
      hinv.with_fuel_scratch_spec ⟨hinv.lengths.core_ok, hsc_early⟩ rfl
    exact hQ s.core.vals s.core.lvl s.core.rsns s.core.trl s.core.trail_pos s.core.trail_end
      s.core.propagated s.core.cur_level s.core.unassigned s.core.fuel sc_early _
      hinv_e (fun hst => absurd hc hst) (Nat.le_refl _) (Nat.le_refl _) ⟨rfl, rfl⟩ hm
  · refine wp_join_group (ts := [])
      (fun () m1 => ∃ (st1 : FullState),
        FullCoreInv c F0 st1 ∧ st1.core.vals.length = 2 * c.max_vars ∧
        st1.core.cur_vars = s.core.cur_vars ∧ st1.core.cur_level = 0 ∧
        st1.core.fuel = s.core.fuel ∧
        st1.core = { s.core with
          vals := st1.core.vals, lvl := st1.core.lvl, rsns := st1.core.rsns,
          trl := st1.core.trl, trail_pos := st1.core.trail_pos, trail_end := st1.core.trail_end,
          propagated := st1.core.propagated, cur_level := 0, unassigned := st1.core.unassigned } ∧
        FullExtScratchPres s st1 ∧ (FullMem c st1 ⋆ R) m1)
      (fun _ () m1 ⟨st1, hinv1, _, hcv1, hcl1, hfu1, hceq1, ⟨hll1, hext1⟩, hm1⟩ => ?_)
      (fun _ hJbt => ?_)
    · clear hm
      have hcv_le : st1.core.cur_vars ≤ c.max_vars := hinv1.lengths.core_ok.cur_vars_le
      c0_hsteps_nogrp
      let sc2 : FullScratch := { st1.scratch with rephased := st1.scratch.rephased + 1#64 }
      have hsc2_ok : sc2.LengthsOk c :=
        { hinv1.lengths.scratch_ok with walk_vals_len := hinv1.lengths.scratch_ok.walk_vals_len }
      let st2 : FullState := { st1 with scratch := sc2 }
      have hinv2 : FullCoreInv c F0 st2 :=
        hinv1.with_fuel_scratch_spec ⟨hinv1.lengths.core_ok, hsc2_ok⟩ rfl
      refine wp_join_group (ts := []) (fun () m2 => ∃ (fuel' : BitVec 64) (sc3 : FullScratch),
        sc3.LengthsOk c ∧ fuel'.toNat ≤ st1.core.fuel.toNat ∧
        sc3.last_learned = s.scratch.last_learned ∧ sc3.extend_len = s.scratch.extend_len ∧
        (FullMem c { core := { st1.core with fuel := fuel' }, scratch := sc3 } ⋆ R) m2) ?_ ?_
      · rintro _ ⟨⟩ m2 ⟨fuel', sc3, hsc3, hfl3, hll3, hext3, hm2⟩
        refine wp_loop_inv
          (fun (k, ()) m3 => ∃ ptgt' : List (BitVec 8),
            k.toNat ≤ st1.core.cur_vars ∧ ptgt'.length = c.max_vars ∧
            (FullMem c
              { core := { st1.core with fuel := fuel' }
                scratch := { sc3 with phases_target := ptgt' } } ⋆ R) m3)
          (fun (k, ()) _ => st1.core.cur_vars - k.toNat)
          (fun L hL => by
            c0_steps
            exact hL (0#64, ()) m2 ⟨sc3.phases_target, Nat.zero_le _, hsc3.phases_target_len, hm2⟩)
          (fun L (k, ()) m3 ⟨ptgt', hk_le, hpt_len, hm3⟩ ih => ?_)
        have hph3 := hsc3.phases_len
        m6_to_group
        · have hk_lt : k.toNat < st1.core.cur_vars := by c0_bound
          have hk1 : (k + 1#64).toNat = k.toNat + 1 := bv64_add1_toNat_m6 (by omega)
          exact ih (k + 1#64, ()) _ (by dsimp only; omega)
            ⟨ptgt'.set k.toNat (sc3.phases[k.toNat]'(by omega)), by omega, by simp [hpt_len],
              by assumption⟩
        · let st3 : FullState :=
            { core := { st1.core with fuel := fuel' }
              scratch := { sc3 with phases_target := ptgt', target_assigned := 0#64 } }
          refine wp_join_group (ts := [i64]) (fun _ m4 => (FullMem c st3 ⋆ R) m4)
            (fun _ (nc, ()) m4 hm4 => ?_) ?_
          · m6_to_group
            c0_call hLog
            intro q _ _
            refine wp_join_group (ts := [i64]) (fun _ m5 => (FullMem c st3 ⋆ R) m5)
              (fun _ (sc_val, ()) m5 hm5 => ?_) ?_
            · c0_hsteps_nogrp
              let sc4 : FullScratch := { sc3 with
                phases_target := ptgt', target_assigned := 0#64,
                rephase_limit := sc3.conflicts + sc_val }
              have hsc4 : sc4.LengthsOk c := { hsc3 with phases_target_len := hpt_len }
              have hco4 : FullCoreState.LengthsOk c { st1.core with fuel := fuel' } :=
                { hinv1.lengths.core_ok with vals_len := hinv1.lengths.core_ok.vals_len }
              let st4 : FullState := { core := { st1.core with fuel := fuel' }, scratch := sc4 }
              have hinv4 : FullCoreInv c F0 st4 :=
                hinv1.with_fuel_scratch_spec ⟨hco4, hsc4⟩ rfl
              c0_call hSetWm
              refine ⟨c, st4, R, rfl, hinv4.lengths, by assumption,
                fun () s5 m5 hcore5 hlen5 hpres5 hm5 => ?_⟩
              dsimp only [fullSafetySlice] at hlen5 hm5
              have heq5 : s5.core = st4.core := fullCoreState_agrees_with_scratch hcore5
              have hinv_s5 : FullCoreInv c F0 s5 := hinv4.with_scratch hlen5 hcore5
              let core_tgt : FullCoreState :=
                { s.core with
                  vals := st1.core.vals, lvl := st1.core.lvl, rsns := st1.core.rsns,
                  trl := st1.core.trl, trail_pos := st1.core.trail_pos,
                  trail_end := st1.core.trail_end, propagated := st1.core.propagated,
                  cur_level := 0, unassigned := st1.core.unassigned, fuel := fuel' }
              have hc' : s5.core = core_tgt := by
                rw [heq5]; dsimp only [st4]; rw [hceq1]
              have hs5_eq : s5 = { core := core_tgt, scratch := s5.scratch } := by
                cases s5; simp only [FullState.mk.injEq, and_true]; exact hc'
              refine hQ st1.core.vals st1.core.lvl st1.core.rsns st1.core.trl st1.core.trail_pos
                st1.core.trail_end st1.core.propagated 0 st1.core.unassigned fuel' s5.scratch m5
                (hs5_eq ▸ hinv_s5) (fun _ => rfl) (Nat.zero_le _) (hfu1 ▸ hfl3)
                ⟨hpres5.1.1.1.trans hll3, hpres5.1.1.2.trans hext3⟩ (hs5_eq ▸ hm5)
            · intro _ hJsc
              m6_split
              · c0_steps; exact hJsc (_, ()) m4 hm4
              · m6_to_group
                refine wp_join_group (ts := [i64]) (fun _ m5 => m4 = m5)
                  (fun _ (nlim, ()) _ hm5 => ?_) ?_
                · rcases hm5 with rfl; c0_steps; exact hJsc (_, ()) m4 hm4
                · intro _ hJn; c0_steps
                  · exact hJn (100000000#64, ()) m4 rfl
                  · exact hJn (_, ()) m4 rfl
          · intro _ hJnc; c0_steps
            · exact hJnc _ _ (by assumption)
            · exact hJnc _ _ (by assumption)
      · intro Jsel hJsel
        m6_split
        · refine wp_loop_inv
            (fun (k, ()) m3 => ∃ ph' : List (BitVec 8),
              k.toNat ≤ st1.core.cur_vars ∧ ph'.length = c.max_vars ∧
              (FullMem c { st2 with scratch := { sc2 with phases := ph' } } ⋆ R) m3)
            (fun (k, ()) _ => st1.core.cur_vars - k.toNat)
            (fun L hL => by
              c0_hsteps; refine hL (0#64, ()) _
                ⟨sc2.phases, Nat.zero_le _, hsc2_ok.phases_len, by assumption⟩)
            (fun L (k, ()) m3 ⟨ph', hk_le, hph_l, hm3⟩ ih => ?_)
          have hpb_l := hsc2_ok.phases_best_len
          c0_hsteps
          · have hk_lt : k.toNat < st1.core.cur_vars := by c0_bound
            have hk1 : (k + 1#64).toNat = k.toNat + 1 := bv64_add1_toNat_m6 (by omega)
            exact ih (k + 1#64, ()) _ (by dsimp only; omega)
              ⟨ph'.set k.toNat (sc2.phases_best[k.toNat]'(by omega)),
                by omega, by simp [hph_l], by assumption⟩
          · have hk_lt : k.toNat < st1.core.cur_vars := by c0_bound
            have hk1 : (k + 1#64).toNat = k.toNat + 1 := bv64_add1_toNat_m6 (by omega)
            exact ih (k + 1#64, ()) m3 (by dsimp only; omega) ⟨ph', by omega, hph_l, hm3⟩
          · refine hJsel () _
              ⟨st1.core.fuel, { sc2 with phases := ph', best_assigned := 0#64 },
               { hsc2_ok with phases_len := hph_l }, Nat.le_refl _, hll1, hext1, by assumption⟩
        · m6_split
          · c0_call hWalk
            refine ⟨c, F0, st2, R, rfl, hinv2, by assumption,
              fun fuel' sc3 m3 hlen3 hfl3 hpres3 hm3 => ?_⟩
            c0_hsteps
            exact hJsel () m3 ⟨fuel', sc3, hlen3.scratch_ok, hfl3,
              hpres3.1.trans hll1, hpres3.2.trans hext1, hm3⟩
          · m6_split
            · refine wp_loop_inv
                (fun (k, ()) m3 => ∃ ph' : List (BitVec 8),
                  k.toNat ≤ st1.core.cur_vars ∧ ph'.length = c.max_vars ∧
                  (FullMem c { st2 with scratch := { sc2 with phases := ph' } } ⋆ R) m3)
                (fun (k, ()) _ => st1.core.cur_vars - k.toNat)
                (fun L hL => by
                  c0_hsteps; refine hL (0#64, ()) _
                    ⟨sc2.phases, Nat.zero_le _, hsc2_ok.phases_len, by assumption⟩)
                (fun L (k, ()) m3 ⟨ph', hk_le, hph_l, hm3⟩ ih => ?_)
              c0_hsteps
              · have hk_lt : k.toNat < st1.core.cur_vars := by c0_bound
                have hk1 : (k + 1#64).toNat = k.toNat + 1 := bv64_add1_toNat_m6 (by omega)
                exact ih (k + 1#64, ()) _ (by dsimp only; omega)
                  ⟨ph'.set k.toNat _, by omega, by simp [hph_l], by assumption⟩
              · c0_hsteps
                refine hJsel () m3 ⟨st1.core.fuel, { sc2 with phases := ph' },
                  { hsc2_ok with phases_len := hph_l }, Nat.le_refl _, hll1, hext1, hm3⟩
            · refine wp_loop_inv
                (fun (k, ()) m3 => ∃ ph' : List (BitVec 8),
                  k.toNat ≤ st1.core.cur_vars ∧ ph'.length = c.max_vars ∧
                  (FullMem c { st2 with scratch := { sc2 with phases := ph' } } ⋆ R) m3)
                (fun (k, ()) _ => st1.core.cur_vars - k.toNat)
                (fun L hL => by
                  c0_hsteps; refine hL (0#64, ()) _
                    ⟨sc2.phases, Nat.zero_le _, hsc2_ok.phases_len, by assumption⟩)
                (fun L (k, ()) m3 ⟨ph', hk_le, hph_l, hm3⟩ ih => ?_)
              c0_hsteps
              · have hk_lt : k.toNat < st1.core.cur_vars := by c0_bound
                have hk1 : (k + 1#64).toNat = k.toNat + 1 := bv64_add1_toNat_m6 (by omega)
                exact ih (k + 1#64, ()) _ (by dsimp only; omega)
                  ⟨ph'.set k.toNat _, by omega, by simp [hph_l], by assumption⟩
              · c0_hsteps
                refine hJsel () m3 ⟨st1.core.fuel, { sc2 with phases := ph' },
                  { hsc2_ok with phases_len := hph_l }, Nat.le_refl _, hll1, hext1, hm3⟩
    · c0_hsteps_nogrp
      · c0_call hBt
        refine ⟨c, s, R, rfl, hinv.lengths, hcl_lt64, hmaxv_pos, hw0.trail_lits_lt, hm,
          fun vals' lvl' rsns' trl' tp' te' prop' cl' unas' sc1 m1
            hlen1 _ _ hcl' hpres1 _ _ _ hwinv1 _ hm1 => ?_⟩
        have hcl'0 : cl' = 0 := by rw [hcl']; exact Nat.min_zero _
        subst hcl'0
        let st1 : FullState :=
          { core := { s.core with
              vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
              trail_end := te', propagated := prop', cur_level := 0, unassigned := unas' }
            scratch := sc1 }
        have hw1 : FullWitnessInv c F0 F_cur st1.core := hwinv1 F0 F_cur hw0 (Nat.zero_le _)
        exact hJbt () m1 ⟨st1, ⟨hlen1, F_cur, hw1⟩, hlen1.core_ok.vals_len, rfl, rfl, rfl,
          rfl, hpres1.1, hm1⟩
      · have hcl0 : s.core.cur_level = 0 := by c0_bound
        have heq0 : s.core = { s.core with cur_level := 0 } := by
          have hcl' : s.core.cur_level = 0 := hcl0
          cases hs : s.core; simp only [hs] at hcl'
          simp only [FullCoreState.mk.injEq, true_and, and_true]; exact hcl'
        exact hJbt () m ⟨s, hinv, hco0.vals_len, rfl, hcl0, rfl, heq0, ⟨rfl, rfl⟩, hm⟩

/-! ## 5. `full_reduce_m6`, `full_analyze_rsn_m6`, `full_analyze_m6` `Func.wp` Proofs -/

theorem full_reduce_m6_wp (Γ : Env)
    (hRecomp : ∀ a m Q X, m6SafetyVoidSpec a m Q X →
      Γ "full_recompute_tiers_m6" [i64] [] a m Q X)
    (hRed : ∀ a m Q X, fullReduceSpec a m Q X → Γ "full_reduce" [i64, .bool] [i64] a m Q X)
    (hSetWm : ∀ a m Q X, m6SetWmSpec a m Q X →
      Γ "full_m6_set_watermark" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullReduceSpec a m Q X → Func.wp Γ full_reduce_m6_body a m Q X := by
  rintro ⟨h, force, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hspW, hm, hQ⟩
  c0_hsteps_nogrp
  c0_call hRecomp
  refine ⟨c, s, R, rfl, hspW.1, hm, fun () s1 m1 hcore1 hlen1 hpres1 hm1 => ?_⟩
  dsimp only [fullSafetySlice] at hlen1 hm1
  have hspW1 : FullSparseInvW c F0 F_cur s1 :=
    fullSparseInvW_of_safetySlice hspW hlen1 hcore1 hpres1.1.1
  have heq1 : s1.core = s.core := fullCoreState_agrees_with_scratch hcore1
  clear hm
  c0_hsteps_nogrp
  c0_call hRed
  refine ⟨c, F0, F_cur, s1, R, rfl, hspW1, hm1,
    fun rr s2 m2 hspW2 hdom hcl2 hfu2 hcv2 htmp2 htmpl2 hws2 hu2 hoom2 hpos2 hm2 => ?_⟩
  c0_hsteps_nogrp
  c0_call hSetWm
  refine ⟨c, s2, R, rfl, hspW2.1, hm2, fun () s3 m3 hcore3 hlen3 hpres3 hm3 => ?_⟩
  dsimp only [fullSafetySlice] at hlen3 hm3
  c0_hsteps_nogrp
  c0_call hSetWm
  refine ⟨c, s3, R, rfl, hlen3, hm3, fun () s4 m4 hcore4 hlen4 hpres4 hm4 => ?_⟩
  dsimp only [fullSafetySlice] at hlen4 hm4
  have heq34 : s4.core = s2.core :=
    (fullCoreState_agrees_with_scratch hcore4).trans (fullCoreState_agrees_with_scratch hcore3)
  have hspW4 : FullSparseInvW c F0 F_cur s4 :=
    fullSparseInvW_of_safetySlice hspW2 hlen4 (hcore3.trans hcore4)
      ⟨hpres4.1.1.1.trans hpres3.1.1.1, hpres4.1.1.2.trans hpres3.1.1.2⟩
  c0_steps
  exact hQ rr s4 m4 hspW4 hdom (by rw [heq34, ← heq1]; exact hcl2)
    (by rw [heq34, ← heq1]; exact hfu2) (by rw [heq34, ← heq1]; exact hcv2)
    (by rw [heq34, ← heq1]; exact htmp2) (by rw [heq34, ← heq1]; exact htmpl2)
    (hpres4.1.2.2.1.trans (hpres3.1.2.2.1.trans (hws2.trans hpres1.1.2.2.1)))
    hu2 (fun h1 hoom => by rw [heq34]; exact hoom2 h1 (by rw [heq1]; exact hoom))
    (fun h1 hcl => by
      have h0 := hpos2 h1 (by rw [← heq34]; exact hcl)
      rw [heq1] at h0; rw [heq34]; exact h0)
    hm4

theorem full_analyze_rsn_m6_wp (Γ : Env)
    (hRecUsed : ∀ a m Q X, m6SafetyArgVoidSpec i64 a m Q X →
      Γ "full_m6_record_used" [i64, i64] [] a m Q X)
    (hAnaRsn : ∀ a m Q X, fullAnalyzeRsnSpec a m Q X →
      Γ "full_analyze_rsn" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullAnalyzeRsnSpec a m Q X → Func.wp Γ full_analyze_rsn_m6_body a m Q X := by
  rintro ⟨h, rsn, skip_var, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, cut, s, R,
    rfl, hlen, hcut, hcov, htl, htc, href, hm, hQ⟩
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ s1 : FullState,
      s1.core = s.core ∧ s1.LengthsOk c ∧ FullM6ScratchPres s s1 ∧ (FullMem c s1 ⋆ R) m1)
    (fun _ () m1 ⟨s1, heq1, hlen1, hpres1, hm1⟩ => ?_)
    (fun _ hJr => ?_)
  · clear hm
    c0_hsteps_nogrp
    c0_call hAnaRsn
    have href1 : rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
        rsn.toNat ∈ fullArenaClauseRefs s1 := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore; rwa [heq1]
    refine ⟨c, F0, F_cur, cut, s1, R, rfl, hlen1,
      fullWitnessCutInv_of_coreEq hcut heq1, fullAnaMarksCov_of_safetySlice hcov heq1 hpres1.1.2.1,
      heq1 ▸ htl, heq1 ▸ htc, href1, hm1,
      fun ok mrk' tmp' tc' tl' mcl' arena' sc' m' hlen' hcut' hcov' hpre' hws2'
        htl_le htl_cv htc_le hrefs' har_pres hmrk_keep htmp_keep hmrk_new hj_ok hj_nodup
        htc_diff hres_sz hok_post hm' => ?_⟩
    c0_steps
    let s2 : FullState :=
      { s with
        core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                              min_clr_len := mcl', arena := arena' }
        scratch := sc' }
    have hs2_eq :
        ({ s1 with
            core := { s1.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                                   min_clr_len := mcl', arena := arena' }
            scratch := sc' } : FullState) = s2 := by
      cases s1; cases s; dsimp only at heq1; simp only [s2]; subst heq1; rfl
    rw [hs2_eq] at hlen' hcut' hcov' hrefs' har_pres hm'
    have hpre2 : FullExtScratchPres s s2 :=
      ⟨hpre'.1.trans hpres1.1.1.1, hpre'.2.trans hpres1.1.1.2⟩
    have hrl_eq : fullRsnLits s1 rsn = fullRsnLits s rsn := by
      unfold fullRsnLits fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
      rw [heq1]
    have hmrk_s : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
        mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8 := by
      intro v hv hne; exact (hmrk_keep v hv (heq1 ▸ hne)).trans (by rw [heq1])
    have hmrk_new_s : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 →
        mrk'[v]?.getD 0#8 ≠ 0#8 →
        ∃ l ∈ fullRsnLits s rsn, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
          0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
          (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level := by
      intro v hv hz hnz
      have h := hmrk_new v hv (heq1 ▸ hz) hnz
      rw [hrl_eq, heq1] at h; exact h
    have hj_ok_s : ∀ j, s.core.tmp_len ≤ j → j < tl' →
        let l := (tmp'[j]?.getD 0#32).toNat
        l ∈ fullRsnLits s rsn ∧ l < 2 * s.core.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
        s.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
        (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧ mrk'[l / 2]?.getD 0#8 ≠ 0#8 := by
      intro j hj1 hj2
      have h := hj_ok j (heq1 ▸ hj1) hj2
      rwa [hrl_eq, heq1] at h
    have hres_s : sc'.res_sz = s.scratch.res_sz + BitVec.ofNat 64
        ((List.range s.core.cur_vars).filter fun w =>
          decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length := by
      rw [hres_sz, hpres1.1.2.2.2.2.2.2.1, heq1]
    have hok_s : ok = true → rsn ≠ 0xFFFFFFFF#32 ∧
        sc'.ant_sz = s.scratch.ant_sz + BitVec.ofNat 64
          ((fullRsnLits s rsn).countP fun l =>
            decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
              (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)) ∧
        ∀ l ∈ fullRsnLits s rsn, l / 2 < s.core.cur_vars ∧
          (l / 2 ≠ skip_var.toNat →
            (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
            (s.core.mrk[l / 2]?.getD 0#8 = 0#8 →
              (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
              (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat →
                (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level →
                ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧
                  (tmp'[j]?.getD 0#32).toNat / 2 = l / 2))) := by
      intro hok
      have h := hok_post hok
      rwa [hrl_eq, hpres1.1.2.2.2.2.2.1, heq1] at h
    exact hQ ok mrk' tmp' tc' tl' mcl' arena' sc' m' hlen' hcut' hcov' hpre2
      (hws2'.trans hpres1.1.2.2.1) (heq1 ▸ htl_le) (heq1 ▸ htl_cv) (heq1 ▸ htc_le)
      (by unfold fullArenaClauseRefs fullArenaClauseRefsCore at hrefs' ⊢
          rw [heq1] at hrefs'; exact hrefs')
      (fun r hr => by
        have hp := har_pres r
          (by unfold fullArenaClauseRefs fullArenaClauseRefsCore at hr ⊢; rw [heq1]; exact hr)
        unfold fullArenaClauseSize fullArenaClauseSizeCore fullArenaClauseGarb
          fullArenaClauseGarbCore fullArenaHdrCore fullArenaClauseLits
          fullArenaClauseLitsCore at hp ⊢
        rwa [heq1] at hp)
      hmrk_s (by intro k hk; exact (htmp_keep k (heq1 ▸ hk)).trans (by rw [heq1]))
      hmrk_new_s hj_ok_s
      (fun j1 j2 h1 h2 h3 => hj_nodup j1 j2 (heq1 ▸ h1) h2 h3) (by rwa [heq1] at htc_diff)
      hres_s hok_s hm'
  · m6_split
    · m6_split
      · m6_split
        · have hal_le := hlen.core_ok.arena_len_le
          have har_len := hlen.core_ok.arena_len_arr
          have hal_3 : rsn.toNat + 3 ≤ s.core.arena_len := by
            c0_cond hc; have := rsn.isLt; bv_omega
          have hrsn_ar : (rsn.setWidth 64).toNat < s.core.arena.length := by
            have : (rsn.setWidth 64).toNat = rsn.toNat := by bv_omega
            omega
          have hrsn2_ar : (rsn.setWidth 64 + 2#64).toNat < s.core.arena.length := by
            have h1 : (rsn.setWidth 64).toNat = rsn.toNat := by bv_omega
            have h2 : rsn.toNat < 2 ^ 32 := rsn.isLt
            rw [BitVec.toNat_add, h1, show (2#64).toNat = 2 from rfl,
              Nat.mod_eq_of_lt (by omega)]
            omega
          c0_hsteps_nogrp
          refine wp_join_group (ts := [])
            (fun () m1 => ∃ s1 : FullState,
              s1.core = s.core ∧ s1.LengthsOk c ∧ FullM6ScratchPres s s1 ∧
              (FullMem c s1 ⋆ R) m1)
            (fun _ () m1 ⟨s1, heq1, hlen1, hpres1, hm1⟩ =>
              hJr () m1 ⟨s1, heq1, hlen1, hpres1, hm1⟩)
            (fun _ hJs => by
              c0_steps
              · c0_call hRecUsed
                refine ⟨c, s, R, rfl, hlen, hm, fun () s1 m1 hcore1 hlen1 hpres1 hm1 => ?_⟩
                dsimp only [fullSafetySlice] at hlen1 hm1
                c0_steps
                exact hJs () m1 ⟨s1, fullCoreState_agrees_with_scratch hcore1, hlen1, hpres1, hm1⟩
              · exact hJs () m ⟨s, rfl, hlen, FullM6ScratchPres.refl s, hm⟩
              · exact hJs () m ⟨s, rfl, hlen, FullM6ScratchPres.refl s, hm⟩
              · exact hJs () m ⟨s, rfl, hlen, FullM6ScratchPres.refl s, hm⟩)
        · exact hJr () m ⟨s, rfl, hlen, FullM6ScratchPres.refl s, hm⟩
      · exact hJr () m ⟨s, rfl, hlen, FullM6ScratchPres.refl s, hm⟩
    · exact hJr () m ⟨s, rfl, hlen, FullM6ScratchPres.refl s, hm⟩

theorem full_analyze_m6_wp (Γ : Env)
    (hUpd : ∀ a m Q X, m6SafetyVoidSpec a m Q X →
      Γ "full_m6_update_tier_limits" [i64] [] a m Q X)
    (hAna : ∀ a m Q X, fullAnalyzeSpec a m Q X → Γ "full_analyze" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullAnalyzeSpec a m Q X → Func.wp Γ full_analyze_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hspW, hconf, hm, hQ⟩
  c0_hsteps_nogrp
  c0_call hUpd
  refine ⟨c, s, R, rfl, hspW.1, hm, fun () s1 m1 hcore1 hlen1 hpres1 hm1 => ?_⟩
  dsimp only [fullSafetySlice] at hlen1 hm1
  have heq1 : s1.core = s.core := fullCoreState_agrees_with_scratch hcore1
  have hspW1 : FullSparseInvW c F0 F_cur s1 :=
    fullSparseInvW_of_safetySlice hspW hlen1 hcore1 hpres1.1.1
  c0_hsteps_nogrp
  c0_call hAna
  refine ⟨c, F0, F_cur, s1, R, rfl, hspW1, fullConflictOkW_of_coreEq hconf heq1, hm1,
    fun r s2 m2 hlen2 hdom hcv2 hfu2 ⟨hws2, h20s⟩ hu2 h0 h1 hm2 => ?_⟩
  c0_steps
  exact hQ r s2 m2 hlen2 hdom (by rw [heq1] at hcv2; exact hcv2) (by rw [heq1] at hfu2; exact hfu2)
    ⟨hws2.trans hpres1.1.2.2.1, fun h20 => by
      have ⟨ho20, hcl20, hdm20⟩ := h20s h20
      rw [heq1] at hcl20 hdm20; exact ⟨ho20, hcl20, hdm20⟩⟩
    hu2 h0 (fun h1eq => by have p := h1 h1eq; rw [heq1] at p; exact p) hm2

end M6Proof1aTactics

end LeanQbe.T.Examples.Kissat.FullM6Tiers
