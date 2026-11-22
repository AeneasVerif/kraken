module

public import LeanQbe.T.Examples.Kissat.FullM4Bcp
public import LeanQbe.T.Examples.Kissat.FullFastCoreLemmas
import all LeanQbe.T.Examples.Kissat.FullFastCoreBcpLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat M4e Stage 1 (B1): Hot-Loop BCP `Func.wp` & UNSAT Soundness Proofs

Proves canonical `FullSpec2` contracts, `FullSparseInv` preservation, UNSAT soundness, closed
`ModuleOk`, and concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `FullM4Bcp`:
1. `full_prop_lit_m4_wp` (`Full.fullPropLitSpec`) with restored dead-tail `0xFFFFFFFFu` fill.
2. `full_propagate_ignore_m4_wp` (`Full.fullPropagateIgnoreSpec`).
3. `full_bcp_m4_wp` (`Full.fullPropagateSpec`), `full_bcp_m4_preserves_sparseInv`, and
   `full_bcp_m4_unsat_of_confl`.
4. Closed `m4Bcp_tableImpl` and `m4Bcp_moduleOk : ModuleOk m4BcpEnv m4BcpModule`.
5. Concrete `Mem 64` UNSAT non-vacuity `nv_m4_bcp_sound` (`XPost := False`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4Bcp

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FastCore
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat.Full hiding
  full_prop_lit_body full_prop_lit_wf full_prop_lit_wp
  full_propagate_ignore_body full_propagate_ignore_wf full_propagate_ignore_wp
  full_propagate_body full_propagate_wf full_propagate_wp
open LeanQbe.T.Examples.Kissat.Full.FullPropDecSpecs hiding
  fullPropLitSpec fullPropagateIgnoreSpec fullPropagateSpec fullWatchPushSpec
  FullTrailExt FullArenaPermEq
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

attribute [local irreducible] fastPropMem

local macro "fc_hsteps" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps))

local elab "fc_head_steps" : tactic => do
  Lean.Elab.Tactic.evalTactic
    (← `(tactic| try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)))
  fcHeadRun false

local elab "fc_head_split" : tactic => do
  Lean.Elab.Tactic.evalTactic
    (← `(tactic| try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)))
  fcHeadRun true

/-! ## 1. Stage-1 Exit Helper (`Loop 2` + `Loop 3` dead-tail sentinel fill) -/

private def m4PropFinishExpr (h_p pWvec pWstk : Val i64) (not_lit : Val i32)
    (off_v tend_v unass_v unfl_v ticks_v p_v q_v end_v : Val i64) (confl_v : Val .bool) :
    Expr Val Cont [.bool] :=
  .group (sig := [[i64, i64]])
    (fun L1 => .cons (fun q =>
      .let_ (Op.mk (.cmp .ult i64) (.var q.1, (.var end_v, ()))) fun v88 =>
      .jnz (.var v88.1) (
        .let_ (Op.mk (.mul i64) (.var q.2.1, (.imm (4 : BitVec 64), ()))) fun v89 =>
        .let_ (Op.mk (.add i64) (.var pWstk, (.var v89.1, ()))) fun v90 =>
        .let_ (Op.mk (.mul i64) (.var q.1, (.imm (4 : BitVec 64), ()))) fun v91 =>
        .let_ (Op.mk (.add i64) (.var pWstk, (.var v91.1, ()))) fun v92 =>
        .load i32 (.var v92.1) fun v93 =>
        .store (.var v93) (.var v90.1) (
          .let_ (Op.mk (.add i64) (.var q.2.1, (.imm (1 : BitVec 64), ()))) fun v94 =>
          .let_ (Op.mk (.add i64) (.var q.1, (.imm (1 : BitVec 64), ()))) fun v95 =>
          .jump L1.1 (.var v95.1, (.var v94.1, ()))
        )
      ) (
        .group (sig := [[i64]])
          (fun L3 => .cons (fun k =>
            .let_ (Op.mk (.cmp .ult i64) (.var k.1, (.var end_v, ()))) fun c3 =>
            .jnz (.var c3.1) (
              .let_ (Op.mk (.mul i64) (.var k.1, (.imm (4 : BitVec 64), ()))) fun o4 =>
              .let_ (Op.mk (.add i64) (.var pWstk, (.var o4.1, ()))) fun pk =>
              .store (t := i32) (.imm 0xFFFFFFFF#32) (.var pk.1) (
                .let_ (Op.mk (.add i64) (.var k.1, (.imm (1 : BitVec 64), ()))) fun k1 =>
                .jump L3.1 (.var k1.1, ())
              )
            ) (
              .let_ (Op.mk (.zext 32 64) (.var not_lit, ())) fun v89 =>
              .let_ (Op.mk (.sext 32 64) (.imm (1 : BitVec 32), ())) fun v90 =>
              .let_ (Op.mk (.shl i64) (.var v89.1, (.var v90.1, ()))) fun v91 =>
              .let_ (Op.mk (.add i64) (.var v91.1, (.imm (1 : BitVec 64), ()))) fun v92 =>
              .let_ (Op.mk (.mul i64) (.var v92.1, (.imm (4 : BitVec 64), ()))) fun v93 =>
              .let_ (Op.mk (.add i64) (.var pWvec, (.var v93.1, ()))) fun v94 =>
              .let_ (Op.mk (.sub i64) (.var q.2.1, (.var off_v, ()))) fun v95 =>
              .let_ (Op.mk (.trunc 64 32) (.var v95.1, ())) fun v96 =>
              .store (.var v96.1) (.var v94.1) (
                .let_ (Op.mk (.add i64) (.var h_p, (.imm (464 : BitVec 64), ()))) fun v97 =>
                .load i64 (.var v97.1) fun v98 =>
                .let_ (Op.mk (.sub i64) (.var end_v, (.var q.2.1, ()))) fun v99 =>
                .let_ (Op.mk (.add i64) (.var v98, (.var v99.1, ()))) fun v100 =>
                .let_ (Op.mk (.add i64) (.var h_p, (.imm (464 : BitVec 64), ()))) fun v101 =>
                .store (.var v100.1) (.var v101.1) (
                  .let_ (Op.mk (.add i64) (.var h_p, (.imm (144 : BitVec 64), ()))) fun v102 =>
                  .store (.var tend_v) (.var v102.1) (
                    .let_ (Op.mk (.add i64) (.var h_p, (.imm (792 : BitVec 64), ()))) fun v103 =>
                    .store (.var unass_v) (.var v103.1) (
                      .let_ (Op.mk (.add i64) (.var h_p, (.imm (512 : BitVec 64), ()))) fun v104 =>
                      .store (.var unfl_v) (.var v104.1) (
                        .let_ (Op.mk (.add i64) (.var h_p, (.imm (600 : BitVec 64), ())))
                          fun v105 =>
                        .load i64 (.var v105.1) fun v106 =>
                        .let_ (Op.mk (.add i64) (.var v106, (.var ticks_v, ()))) fun v107 =>
                        .let_ (Op.mk (.add i64) (.var h_p, (.imm (600 : BitVec 64), ())))
                          fun v108 =>
                        .store (.var v107.1) (.var v108.1) (
                          .let_ (Op.mk (.not .bool) (.var confl_v, ())) fun v109 =>
                          .ret (.var v109.1, ())
                        )
                      )
                    )
                  )
                )
              )
            )
          ) .nil)
          (fun L3 => .jump L3.1 (.var q.2.1, ()))
      )
    ) .nil)
    (fun L1 => .jump L1.1 (.var p_v, (.var q_v, ())))

private theorem m4Prop_finish_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sem : FullState} {not_lit : BitVec 32}
    {off_v tend_v unass_v unfl_v ticks_v p_v q_v end_v ignore_ref : BitVec 64}
    {confl_v : Bool} {R : Mem 64 → Prop} {mb : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hwc : c.wcap < 2 * dimacsBound) (_hcv0 : s.core.cur_vars ≤ c.max_vars)
    (hdense0 : s.core.dense_mode = 0#64) (hnot_lt : not_lit.toNat < 2 * s.core.cur_vars)
    (hpi : PropLitInv c F0 F_cur s sem not_lit.toNat off_v.toNat q_v.toNat p_v.toNat end_v.toNat)
    (htend_eq : tend_v.toNat = sem.core.trail_end) (hunass_eq : unass_v = sem.core.unassigned)
    (hunfl_eq : unfl_v = sem.core.unflushed)
    (hcf_f : confl_v = false → sem.core.oom = 0#64 ∧ sem.core.confl_type = s.core.confl_type)
    (hcf_t : confl_v = true → PropLitConfl F_cur ignore_ref sem.core)
    (hmb : (FullMem c (fastPropMem s sem) ⋆ R) mb)
    (hret_st : ∀ (ok : Bool) (st : FullState) (ml : Mem 64),
      st.LengthsOk c → FullWitnessInv c F0 F_cur st.core →
      AgreesExcept propLitCoreMask s.core st.core →
      FullPropDecSpecs.FullTrailExt s.core st.core →
      FullPropDecSpecs.FullArenaPermEq s.core st.core →
      st.scratch = { s.scratch with
        search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
        phases := st.scratch.phases } →
      (ok = false → PropLitConfl F_cur ignore_ref st.core) →
      (ok = true → st.core.oom = 0#64 ∧ st.core.confl_type = s.core.confl_type) →
      (FullMem c st ⋆ R) ml → Q (ok, ()) ml) :
    wp Γ Q X (m4PropFinishExpr c.hdr c.pWvec c.pWstk not_lit off_v tend_v unass_v unfl_v
      ticks_v p_v q_v end_v confl_v) mb := by
  have hnot_st : not_lit.toNat < 2 * sem.core.cur_vars := hpi.cur_vars_eq.symm ▸ hnot_lt
  have ⟨hend_le, hwlen_le⟩ := hpi.end_lt_wcap hnot_st
  have hend_wcap : end_v.toNat ≤ c.wcap := Nat.le_trans hend_le hwlen_le
  unfold dimacsBound at hwc
  have hwc64 : c.wcap + 1 < 2 ^ 64 := Nat.lt_trans (Nat.add_lt_add_right hwc 1) (by decide)
  have hq_ge := hpi.sw.q_ge; have hq_le := hpi.sw.q_le_p; have hp_le := hpi.sw.p_le_end
  have hwstk_len := hpi.len.core_ok.wstk_len_arr; have hwvec_len := hpi.len.core_ok.wvec_len
  have hwvec_mem : (fastPropMem s sem).core.wvec.length = 4 * c.max_vars := by
    rw [fastPropMem_wvec]; exact hwvec_len
  have hidx1_nat :
      ((not_lit.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * not_lit.toNat + 1 :=
    fc_bv64_shl1_add1_nat not_lit
  let q_fin : Nat := q_v.toNat + (end_v.toNat - p_v.toNat)
  unfold m4PropFinishExpr
  refine wp_loop_inv
    (fun (p_c, q_c, ()) m2 => ∃ wstk_c : List (BitVec 32),
      wstk_c.length = c.wcap ∧ p_v.toNat ≤ p_c.toNat ∧ p_c.toNat ≤ end_v.toNat ∧
      q_c.toNat = q_v.toNat + (p_c.toNat - p_v.toNat) ∧
      (∀ k, off_v.toNat ≤ k → k < q_v.toNat → wstk_c[k]? = sem.core.wstk[k]?) ∧
      (∀ k < p_c.toNat - p_v.toNat, wstk_c[q_v.toNat + k]? = sem.core.wstk[p_v.toNat + k]?) ∧
      (∀ k, p_c.toNat ≤ k → k < end_v.toNat → wstk_c[k]? = sem.core.wstk[k]?) ∧
      (∀ k, (k < off_v.toNat ∨ end_v.toNat ≤ k) → wstk_c[k]? = sem.core.wstk[k]?) ∧
      (FullMem c (fastPropMem s { sem with core := { sem.core with wstk := wstk_c } }) ⋆ R) m2)
    (fun (p_c, _, ()) _ => end_v.toNat - p_c.toNat)
    (fun L2 hL2 => by
      fc_head_steps
      exact hL2 (p_v, q_v, ()) mb ⟨sem.core.wstk, hwstk_len, Nat.le_refl _, hp_le, by omega,
        fun _ _ _ => rfl, fun _ hk => by omega, fun _ _ _ => rfl, fun _ _ => rfl, hmb⟩)
    (fun L2 (p_c, q_c, ()) m2 ⟨wstk_c, hwl2, hp_ge, hp_le2, hqc_eq,
        hpre, hsuf, hrem, hout, hm2⟩ ih2 => ?_)
  fc_head_steps
  · have hp_lt : p_c.toNat < end_v.toNat := hc
    have hstep := propLit_loop2_step hq_ge hq_le hp_ge hp_lt (by omega) (by omega)
      hpre hsuf hrem hout
    have hpc_add : (p_c + (1 : BitVec 64)).toNat = p_c.toNat + 1 := bv64_add1_toNat (by omega)
    have hqc_add : (q_c + (1 : BitVec 64)).toNat =
        q_v.toNat + ((p_c + (1 : BitVec 64)).toNat - p_v.toNat) := by
      rw [bv64_add1_toNat (by omega), hpc_add]; omega
    refine ih2 (p_c + (1 : BitVec 64), q_c + (1 : BitVec 64), ()) m (by dsimp only; omega)
      ⟨wstk_c.set q_c.toNat (wstk_c[p_c.toNat]'(by omega)), by simp [hwl2],
        by omega, by omega, hqc_add, ?_, ?_, ?_, ?_, by
          simpa only [fastPropMem_wstk, fastPropMem_with_wstk] using hm⟩
    · simpa only [← hqc_eq] using hstep.1
    · rw [hpc_add]; simpa only [← hqc_eq] using hstep.2.1
    · rw [hpc_add]; simpa only [← hqc_eq] using hstep.2.2.1
    · simpa only [← hqc_eq] using hstep.2.2.2
  · have hpc_eq : p_c.toNat = end_v.toNat := by c0_bound
    have hqfin_eq : q_c.toNat = q_fin := by dsimp [q_fin]; omega
    refine wp_loop_inv
      (fun (k_c, ()) m3 => ∃ wstk_k : List (BitVec 32),
        wstk_k.length = c.wcap ∧ q_fin ≤ k_c.toNat ∧ k_c.toNat ≤ end_v.toNat ∧
        (∀ i, (i < q_fin ∨ end_v.toNat ≤ i) → wstk_k[i]? = wstk_c[i]?) ∧
        (FullMem c (fastPropMem s { sem with core := { sem.core with wstk := wstk_k } }) ⋆ R) m3)
      (fun (k_c, ()) _ => end_v.toNat - k_c.toNat)
      (fun L3 hL3 => by
        fc_head_steps
        exact hL3 (q_c, ()) m2 ⟨wstk_c, hwl2, by omega, by omega, fun _ _ => rfl, hm2⟩)
      (fun L3 (k_c, ()) m3 ⟨wstk_k, hwl3, hk_ge, hk_le, hkeep, hm3⟩ ih3 => ?_)
    fc_head_steps
    · have hk_lt : k_c.toNat < end_v.toNat := hc
      have hk_add : (k_c + (1 : BitVec 64)).toNat = k_c.toNat + 1 :=
        bv64_add1_toNat (by omega)
      refine ih3 (k_c + (1 : BitVec 64), ()) m (by dsimp only; omega)
        ⟨wstk_k.set k_c.toNat 0xFFFFFFFF#32, by simp [hwl3], by omega, by omega,
          propLit_loop3_step hk_ge hk_lt hkeep, by
            simpa only [fastPropMem_wstk, fastPropMem_with_wstk] using hm⟩
    · have hk_eq : k_c.toNat = end_v.toNat := by c0_bound
      let sem' : FullState :=
        { sem with scratch :=
            { sem.scratch with search_ticks := s.scratch.search_ticks + ticks_v } }
      have hpi' : PropLitInv c F0 F_cur s sem' not_lit.toNat off_v.toNat q_v.toNat p_v.toNat
          end_v.toNat :=
        { len := ⟨hpi.len.core_ok, hpi.len.scratch_ok.with_ticks _⟩
          nw := hpi.nw, sw := hpi.sw, ag := hpi.ag, tr := hpi.tr, perm := hpi.perm
          sc_eq := by dsimp only [sem']; rw [hpi.sc_eq]
          not_f := hpi.not_f }
      have hm_rew :
          (FullMem c { sem' with core := { sem'.core with
              wstk := wstk_k
              wvec := sem'.core.wvec.set (2 * not_lit.toNat + 1) ((q_c - off_v).setWidth 32)
              wusable := sem'.core.wusable + (end_v - q_c) } } ⋆ R) m := by
        simp only [hidx1_nat, fastPropMem_wvec, fastPropMem_wusable, fastPropMem_search_ticks] at hm
        rw [htend_eq, hunass_eq, hunfl_eq] at hm
        rw [fastPropMem_finish_eq] at hm
        exact hm
      have ⟨hl_f, hw_f, hag_f, htr_f, hperm_f, hsc_f, hcf_f', hoom_f, hm_f⟩ :=
        propLit_finish (ctype0 := s.core.confl_type) hpi' hdense0 hnot_st hwl3 hqfin_eq rfl
          hpre (fun k hk => hsuf k (by omega)) hout hkeep hcf_f hcf_t hm_rew
      exact hret_st (!confl_v) _ m hl_f hw_f hag_f htr_f hperm_f hsc_f hcf_f' hoom_f hm_f

/-! ## 2. Parametric `(Γ : Env)` `Func.wp` Contracts (`full_prop_lit_m4`, `ignore`, `bcp`) -/

theorem full_prop_lit_m4_wp (Γ : Env)
    (hPush : ∀ args m Q X, fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullPropLitSpec args m Q X →
      Func.wp Γ full_prop_lit_m4_body args m Q X := by
  rintro ⟨h, lit, ignore_ref, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hoom0, hm, hQ⟩
  have hmaxv := c.hmaxv; have har := c.harena; have hwc := c.hwcap
  unfold dimacsBound at hmaxv har hwc
  have hcv0 := hlen0.core_ok.cur_vars_le
  let not_lit : BitVec 32 := lit ^^^ 1#32
  have hret_st : ∀ (ok : Bool) (st : FullState) (ml : Mem 64),
      st.LengthsOk c → FullWitnessInv c F0 F_cur st.core →
      AgreesExcept propLitCoreMask s.core st.core →
      FullPropDecSpecs.FullTrailExt s.core st.core →
      FullPropDecSpecs.FullArenaPermEq s.core st.core →
      st.scratch = { s.scratch with
        search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
        phases := st.scratch.phases } →
      (ok = false → PropLitConfl F_cur ignore_ref st.core) →
      (ok = true → st.core.oom = 0#64 ∧ st.core.confl_type = s.core.confl_type) →
      (FullMem c st ⋆ R) ml → Q (ok, ()) ml := by
    intro ok st ml hst_l hst_w hag htr hperm hsc hcf hok_oom hml
    have hst_eq := propLit_eq_upd hag hsc
    have hst_l' := hst_l; have hst_w' := hst_w
    have htr' : FullTrailExt s.core st.core := ⟨htr.te_ge, htr.trl_pref, htr.lvl_pres⟩
    have hperm' : FullArenaPermEq s.core st.core := ⟨hag.get FullCoreState.arena_len, hperm⟩
    rw [hst_eq] at hst_l' hst_w' htr' hperm' hml
    refine hQ ok st.core.vals st.core.flags st.core.lvl st.core.rsns st.core.trl st.core.trail_pos
      st.core.trail_end st.core.unassigned st.core.unflushed st.core.wvec st.core.arena
      st.core.wstk st.core.wlen st.core.wusable st.core.confl_type st.core.confl_ref
      st.core.confl_lit0 st.core.confl_lit1 st.core.oom st.scratch.search_ticks st.scratch.wsort
      st.scratch.phases ml hst_l' hst_w' htr' hperm' ?_ hok_oom hml
    intro hf; rcases (hcf hf) with ho | ⟨hc1, hc2⟩
    · exact Or.inl ho
    · refine Or.inr ⟨?_, hc2⟩
      have hc1' : FullConflictOkW F_cur st := fullConflOkW_to_fullConflictOkW hc1
      rwa [hst_eq] at hc1'
  have hret_noop : Q (true, ()) m :=
    hret_st true s m hlen0 hw0 (.refl _ _) (.refl _) (.refl _) rfl (by simp)
      (fun _ => ⟨hoom0, rfl⟩) hm
  have hvl0 := hlen0.core_ok.vals_len; have hwv0 := hlen0.core_ok.wvec_len
  have hlvl0 := hlen0.core_ok.lvl_len
  have hclv_lt32 : s.core.cur_level < 2 ^ 32 := by
    have := hw0.cur_level_le; have := hlen0.core_ok.trail_end_le; omega
  have hte0_lt64 : s.core.trail_end < 2 ^ 64 := by
    have := hlen0.core_ok.trail_end_le; omega
  unfold Func.wp full_prop_lit_m4_body
  fc_head_steps
  · exact hret_noop
  · exact hret_noop
  · exact hret_noop
  · have hnot_xor : not_lit.toNat = lit.toNat ^^^ 1 := bv32_xor_1 lit
    have hnot_lt : not_lit.toNat < 2 * s.core.cur_vars := by
      have h1 : ¬ 2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 ≤ lit.toNat ^^^ 1 := by assumption
      rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at h1; omega
    have hnot_f0 : s.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 := by
      have hsge : (0#32).sle ((s.core.vals[not_lit.toNat]'(by omega)).signExtend 32) = false := by
        have h2 : (0#32).sle ((s.core.vals[lit.toNat ^^^ 1]'(by omega)).signExtend 32) = false := by
          assumption
        simpa only [hnot_xor] using h2
      rw [bv32_sle0_eq_not_slt0, Bool.not_eq_false'] at hsge
      have hget : s.core.vals[not_lit.toNat]?.getD 0#8 = s.core.vals[not_lit.toNat]'(by omega) := by
        simp [List.getElem?_eq_getElem (show not_lit.toNat < s.core.vals.length by omega)]
      rw [hget]; exact (full_i8_vals_slt0 (by rw [← hget]; exact hw0.vals_domain _ hnot_lt)).mp hsge
    have hidx0 : ((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)).toNat =
        2 * not_lit.toNat := bv64_shl1_u32 not_lit
    have hidx1 : (((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)) +
        (1 : BitVec 64)).toNat = 2 * not_lit.toNat + 1 := by
      rw [bv64_add1_toNat (by rw [hidx0]; omega), hidx0]
    have hoff0_eq : (s.core.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<<
        (1 : BitVec 64)).toNat]'(by omega)).toNat = fullWatchOffCore s.core not_lit.toNat := by
      unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact congrArg BitVec.toNat (by congr 1)
    have hsz0_eq : (s.core.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)) +
        (1 : BitVec 64)).toNat]'(by omega)).toNat = fullWatchSizeCore s.core not_lit.toNat := by
      unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact congrArg BitVec.toNat (by congr 1)
    have hsz0_pos : 0 < fullWatchSizeCore s.core not_lit.toNat := by
      rw [← hsz0_eq]
      have h1 : (2 * (lit.toNat ^^^ 1) + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
          (((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)) +
            (1 : BitVec 64)).toNat := by
        rw [hidx1, ← hnot_xor]; change (2 * not_lit.toNat + 1) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt (by omega)
      have heq_w : s.core.wvec[(2 * (lit.toNat ^^^ 1) + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(
            by omega) = s.core.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)) +
            (1 : BitVec 64)).toNat]'(by omega) := by congr 1
      have hne0 : (s.core.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)) +
          (1 : BitVec 64)).toNat]'(by omega)).setWidth 64 ≠ 0#64 := fun heq => hc (by
        change (s.core.wvec[(2 * (lit.toNat ^^^ 1) + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(
          by omega)).setWidth 64 = 0#64
        rw [heq_w]; exact heq)
      exact Nat.pos_of_ne_zero fun h0 =>
        hne0 (BitVec.eq_of_toNat_eq (by rw [bv_c0_zext32_64, h0]; rfl))
    clear hc; clear hc
    have hwat0 : WatchesInv F_cur s.core := by
      have h := hw0.watches; unfold ModeWatchesInv at h; simpa [hdense0] using h
    have hnw0 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c s.core) :=
      fullWitnessInv_to_nw hcv0 hw0
    have hpi0 : PropLitInv c F0 F_cur s s not_lit.toNat (fullWatchOffCore s.core not_lit.toNat)
        (fullWatchOffCore s.core not_lit.toNat) (fullWatchOffCore s.core not_lit.toNat)
        (fullWatchOffCore s.core not_lit.toNat + fullWatchSizeCore s.core not_lit.toNat) :=
      { len := hlen0, nw := hnw0, sw := SplitWatchesInv.init hnot_lt hwat0 hsz0_pos
        ag := .refl _ _, tr := .refl _, perm := .refl _, sc_eq := rfl, not_f := hnot_f0 }
    have hnl_lvl_idx :
        (BitVec.setWidth 64 ((lit ^^^ (1 : BitVec 32)) >>> (1 : Nat))).toNat <
          s.core.lvl.length := by
      rw [bv_c0_zext32_64, bv32_lshr_1, bv32_xor_1, hlen0.core_ok.lvl_len]; omega
    let nl_lvl0 :=
      s.core.lvl[(BitVec.setWidth 64 ((lit ^^^ (1 : BitVec 32)) >>> (1 : Nat))).toNat]'hnl_lvl_idx
    have hnl_eq0 : s.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 := by
      have hidx : (BitVec.setWidth 64 ((lit ^^^ (1 : BitVec 32)) >>> (1 : Nat))).toNat =
          not_lit.toNat / 2 := by
        rw [bv_c0_zext32_64, bv32_lshr_1]; rfl
      rw [← hidx, List.getElem?_eq_getElem hnl_lvl_idx, Option.getD_some]
    fc_head_steps
    refine wp_loop_break_group
      (brkTs := [i64, i64, i64, i64, i64, i64, i64, i64, .bool])
      (lpTs := [i64, i64, i64, i64, i64, i64, i64, i64])
      (fun (off_v, tend_v, unass_v, unfl_v, ticks_v, p_v, q_v, end_v, confl_v, ()) mb =>
        ∃ sem : FullState,
          PropLitInv c F0 F_cur s sem not_lit.toNat off_v.toNat q_v.toNat p_v.toNat end_v.toNat ∧
          tend_v.toNat = sem.core.trail_end ∧ unass_v = sem.core.unassigned ∧
          unfl_v = sem.core.unflushed ∧
          (confl_v = false → sem.core.oom = 0#64 ∧ sem.core.confl_type = s.core.confl_type) ∧
          (confl_v = true → PropLitConfl F_cur ignore_ref sem.core) ∧
          (FullMem c (fastPropMem s sem) ⋆ R) mb)
      (fun rem (off_v, tend_v, unass_v, unfl_v, ticks_v, p_v, q_v, end_v, ()) ml =>
        ∃ sem : FullState,
          rem = end_v.toNat - p_v.toNat ∧
          PropLitInv c F0 F_cur s sem not_lit.toNat off_v.toNat q_v.toNat p_v.toNat end_v.toNat ∧
          tend_v.toNat = sem.core.trail_end ∧ unass_v = sem.core.unassigned ∧
          unfl_v = sem.core.unflushed ∧
          sem.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 ∧
          sem.core.oom = 0#64 ∧ sem.core.confl_type = s.core.confl_type ∧
          (FullMem c (fastPropMem s sem) ⋆ R) ml) ?_ ?_ ?_
    · rintro _ ⟨off_v, tend_v, unass_v, unfl_v, ticks_v, p_v, q_v, end_v, confl_v, ⟨⟩⟩ mb
        ⟨sem, hpi, htend_eq, hunass_eq, hunfl_eq, hcf_f, hcf_t, hmb⟩
      exact m4Prop_finish_wp c.hwcap hcv0 hdense0 hnot_lt hpi htend_eq hunass_eq
        hunfl_eq hcf_f hcf_t hmb fun ok st ml hl hw hag htr hperm hsc hcf hoom hml =>
        hret_st ok st ml hl hw hag htr hperm hsc hcf hoom hml
    · rintro B L rem ⟨off_v, tend_v, unass_v, unfl_v, ticks_v, p_v, q_v, end_v, ⟨⟩⟩ ml hB ih
        ⟨sem, rfl, hpi, htend_eq, hunass_eq, hunfl_eq, hnl_eq, hoom_st, hct_st, hml⟩
      have hcv_eq : sem.core.cur_vars = s.core.cur_vars := hpi.cur_vars_eq
      have hnot_st : not_lit.toNat < 2 * sem.core.cur_vars := hcv_eq.symm ▸ hnot_lt
      clear hret_noop hoff0_eq hsz0_eq hsz0_pos hpi0 hnw0 hnot_f0 hm hw0 hwat0
      have ⟨hend_le, hwlen_le⟩ := hpi.end_lt_wcap hnot_st
      have hend_wcap : end_v.toNat ≤ c.wcap := Nat.le_trans hend_le hwlen_le
      have hwc64 : c.wcap + 1 < 2 ^ 64 := Nat.lt_trans (Nat.add_lt_add_right hwc 1) (by decide)
      have hwc64_2 : c.wcap + 2 < 2 ^ 64 :=
        Nat.lt_trans (Nat.add_lt_add_right hwc 2) (by decide)
      have hq_ge := hpi.sw.q_ge; have hq_le := hpi.sw.q_le_p; have hp_le := hpi.sw.p_le_end
      have hpr_eq_sem : sem.core.propagated = s.core.propagated :=
        hpi.ag.get FullCoreState.propagated
      have hlen_mem := fastPropMem_lengthsOk hlen0 hpi.len hcv_eq hpr_eq_sem rfl
      have hm_wstk := hlen_mem.core_ok.wstk_len_arr; have hm_vals := hlen_mem.core_ok.vals_len
      have hm_aren := hlen_mem.core_ok.arena_len_arr
      have hm_alen := hlen_mem.core_ok.arena_len_le
      have hm_wvec := hlen_mem.core_ok.wvec_len; have hm_lvl := hlen_mem.core_ok.lvl_len
      have hm_fl := hlen_mem.core_ok.flags_len; have hm_trl := hlen_mem.core_ok.trl_len
      have hm_tp := hlen_mem.core_ok.trail_pos_len; have hm_rsn := hlen_mem.core_ok.rsns_len
      have hm_ph := hlen_mem.scratch_ok.phases_len
      have hwstk_len := hpi.len.core_ok.wstk_len_arr; have hvals_len := hpi.len.core_ok.vals_len
      have hwstk_mem : (fastPropMem s sem).core.wstk.length = c.wcap := by
        rw [fastPropMem_wstk]; exact hwstk_len
      have haren_len := hpi.len.core_ok.arena_len_arr; have halen_le := hpi.len.core_ok.arena_len_le
      have hwvec_len := hpi.len.core_ok.wvec_len; have hlvl_len := hpi.len.core_ok.lvl_len
      have hfl_len := hpi.len.core_ok.flags_len; have htrl_len := hpi.len.core_ok.trl_len
      have htp_len := hpi.len.core_ok.trail_pos_len; have hrsn_len := hpi.len.core_ok.rsns_len
      have hph_len := hpi.len.scratch_ok.phases_len
      have hcv_lt64 : s.core.cur_vars < 2 ^ 64 :=
        Nat.lt_of_le_of_lt hcv0 (Nat.lt_trans hmaxv (by decide))
      have h2cv_lt64 : 2 * s.core.cur_vars < 2 ^ 64 :=
        Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 hcv0)
          (Nat.lt_trans (Nat.mul_lt_mul_of_pos_left hmaxv (by decide)) (by decide))
      have hp1_pre : (p_v + (1 : BitVec 64)).toNat = p_v.toNat + 1 :=
        bv64_add1_toNat (Nat.lt_of_le_of_lt
          (Nat.add_le_add_right (Nat.le_trans hp_le hend_wcap) 1) hwc64)
      fc_head_split
      · have hp_lt : p_v.toNat < end_v.toNat := by assumption
        have hp_lt_w : p_v.toNat < sem.core.wstk.length :=
          hwstk_len ▸ Nat.lt_of_lt_of_le hp_lt hend_wcap
        have hp_rem_pos : 0 < end_v.toNat - p_v.toNat := Nat.sub_pos_of_lt hp_lt
        have hp1_nat : (p_v + 1#64).toNat = p_v.toNat + 1 := hp1_pre
        have hq1_nat : (q_v + 1#64).toNat = q_v.toNat + 1 :=
          bv64_add1_toNat (Nat.lt_of_le_of_lt
            (Nat.add_le_add_right (Nat.le_trans hq_le (Nat.le_trans hp_le hend_wcap)) 1) hwc64)
        have hq_lt_ws : q_v.toNat < sem.core.wstk.length :=
          hwstk_len ▸ Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hq_le hp_lt) hend_wcap
        fc_head_split
        · have hflag : (sem.core.wstk[p_v.toNat]'hp_lt_w &&& 0x80000000#32) ≠ 0#32 := by
            simpa only [ne_eq, ← BitVec.ofNat_eq_ofNat, fc_getElem_wstk, fastPropMem_wstk]
              using hc
          refine fastProp_bin_watch_wp
            (ignore_ref := ignore_ref)
            (q_v := q_v) (tend_v := tend_v) (unass_v := unass_v) (unfl_v := unfl_v)
            (nl_lvl0 := nl_lvl0)
            (rsn_bin := ((lit ^^^ 1#32) &&& 0x7FFFFFFF#32) ||| 0x80000000#32)
            (rec_ph := s.core.probing == 0#64)
            (k_cont := fun te un uf qn => .jump L (.var off_v, (.var te, (.var un,
              (.var uf, (.var ticks_v, (.var (p_v + (1 : BitVec 64)), (.var qn,
              (.var end_v, ())))))))))
            (k_confl := fun qn => .jump B (.var off_v, (.var tend_v, (.var unass_v,
              (.var unfl_v, (.var ticks_v, (.var (p_v + (1 : BitVec 64)), (.var qn,
              (.var end_v, (.imm true, ()))))))))))
            c.hmaxv c.hwcap hlen0 hcv0 hpi hlen_mem ?_ hp_lt
            hend_wcap hp_lt_w (fc_getElem_wstk s sem)
            ((fc_getElem_wstk s sem).symm ▸ hflag) rfl hnot_st hnl_eq htend_eq
            hunass_eq hunfl_eq hoom_st hct_st hp1_nat hq1_nat hq_lt_ws hml ?_ ?_
          · rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_lt64,
              Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm, Nat.mod_eq_of_lt h2cv_lt64]
          · intro sem' tend_n unass_n unfl_n m' hpi' ht' hu' huf' hnl' hoom' hct' hm'
            exact ih (end_v.toNat - (p_v.toNat + 1)) (off_v, tend_n, unass_n, unfl_n, ticks_v,
              p_v + 1#64, q_v + 1#64, end_v, ()) m'
              (Nat.sub_lt hp_rem_pos Nat.zero_lt_one)
              ⟨sem', by rw [hp1_nat], by rwa [hp1_nat], ht', hu', huf', hnl',
                hoom', hct', hm'⟩
          · intro sem' m' hpi' ht' hu' huf' hcf' hm'
            exact hB (off_v, tend_v, unass_v, unfl_v, ticks_v, p_v + 1#64, q_v + 1#64, end_v,
              true, ()) m' ⟨sem', by rwa [hp1_nat], ht', hu', huf', by simp,
                fun _ => hcf', hm'⟩
        · have hw0_get : sem.core.wstk[p_v.toNat]? = some (sem.core.wstk[p_v.toNat]'hp_lt_w) :=
            List.getElem?_eq_getElem hp_lt_w
          have hflag : (sem.core.wstk[p_v.toNat]'hp_lt_w &&& 0x80000000#32) = 0#32 := by
            simpa only [← BitVec.ofNat_eq_ofNat, fc_getElem_wstk, fastPropMem_wstk] using hc
          have ⟨h2le, cref0, hcr_get, hcr_lt, hcr_ref, hrem2⟩ :=
            watchSlice_inv_large hpi.sw.rem_slice hp_rem_pos hw0_get hflag
          fc_head_split
          · have hge : end_v.toNat ≤ (p_v + (1 : BitVec 64)).toNat := hc
            rw [hp1_pre] at hge
            have h2_le_end : p_v.toNat + 2 ≤ end_v.toNat :=
              Nat.add_sub_cancel' hp_le ▸ Nat.add_le_add_left h2le p_v.toNat
            exact absurd hge (Nat.not_le.mpr (Nat.lt_of_succ_le h2_le_end))
          · fc_head_steps
            have h2_le_end : p_v.toNat + 2 ≤ end_v.toNat :=
              Nat.add_sub_cancel' hp_le ▸ Nat.add_le_add_left h2le p_v.toNat
            have hrem_dec : end_v.toNat - (p_v.toNat + 2) < end_v.toNat - p_v.toNat :=
              fc_rem2_lt h2_le_end
            have hp2_wcap : p_v.toNat + 2 ≤ c.wcap := Nat.le_trans h2_le_end hend_wcap
            have hp2_64 : p_v.toNat + 2 < 2 ^ 64 :=
              Nat.lt_of_le_of_lt hp2_wcap (Nat.lt_trans hwc (by decide))
            have hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2 := by
              rw [bv64_add_toNat (a := p_v + 1#64) (b := 1#64) (by rw [hp1_nat]; exact hp2_64),
                hp1_nat]; rfl
            have hq2_nat : (q_v + 2#64).toNat = q_v.toNat + 2 :=
              bv64_add2_toNat (a := q_v) (Nat.lt_of_le_of_lt
                (Nat.add_le_add_right (Nat.le_trans hq_le (Nat.le_trans hp_le hend_wcap)) 2)
                hwc64_2)
            have hq_lt_ws2 : q_v.toNat < sem.core.wstk.length :=
              hwstk_len ▸ Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hq_le
                (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 2)) h2_le_end))
                hend_wcap
            have hq1_lt_ws2 : q_v.toNat + 1 < sem.core.wstk.length :=
              hwstk_len ▸ Nat.lt_of_lt_of_le
                (Nat.lt_of_le_of_lt (Nat.add_le_add_right hq_le 1)
                  (Nat.lt_of_lt_of_le (Nat.lt_succ_self (p_v.toNat + 1)) h2_le_end)) hend_wcap
            have hcr_idx_lt : (p_v + 1#64).toNat < sem.core.wstk.length := by
              rw [hp1_nat, hwstk_len]
              exact Nat.lt_of_lt_of_le (Nat.lt_of_succ_le h2_le_end) hend_wcap
            have hcr_eq : sem.core.wstk[(p_v + 1#64).toNat]'hcr_idx_lt = cref0 := by
              have h1 : sem.core.wstk[p_v.toNat + 1]? =
                  some (sem.core.wstk[(p_v + 1#64).toNat]'hcr_idx_lt) := by
                rw [← hp1_nat]; exact List.getElem?_eq_getElem hcr_idx_lt
              exact Option.some.inj (h1.symm.trans hcr_get)
            simp only [fastPropMem_wstk]
            generalize hcr_gen :
              sem.core.wstk[(p_v + 1#64).toNat]'hcr_idx_lt = cref at hcr_eq ⊢
            generalize hw0_gen : sem.core.wstk[p_v.toNat]'(hwstk_len ▸
              Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 2))
                h2_le_end) hend_wcap) = w0 at hflag ⊢
            rw [← hcr_eq] at hcr_lt hcr_ref
            have hsw_drop : SplitWatchesInv F_cur sem.core not_lit.toNat off_v.toNat q_v.toNat
                (p_v.toNat + 2) end_v.toNat :=
              hpi.sw.advance_rem (p' := p_v.toNat + 2) (by omega) h2_le_end
                (by simpa [Nat.sub_sub] using hrem2)
            refine wp_join_group (fun () m1 => m1 = ml) ?_ ?_
            · rintro _ ⟨⟩ ml1 hml1; subst ml1
              have hcr_wf := hpi.nw.arena.refs_wf cref.toNat hcr_ref
              have hcr3_le : cref.toNat + 3 ≤ sem.core.arena_len := hcr_wf.1
              have hcsz3 : 3 ≤ fullArenaClauseSizeCore sem.core cref.toNat := hcr_wf.2.1
              have hcr_next : cref.toNat + 3 + fullArenaClauseSizeCore sem.core cref.toNat ≤
                  fullArenaNextOff sem.core.arena sem.core.arena_len cref.toNat := hcr_wf.2.2.1
              have hnext_le : fullArenaNextOff sem.core.arena sem.core.arena_len cref.toNat ≤
                  sem.core.arena_len := hcr_wf.2.2.2.1
              have hcr_fit : cref.toNat + 3 + fullArenaClauseSizeCore sem.core cref.toNat ≤
                  sem.core.arena_len := Nat.le_trans hcr_next hnext_le
              have ⟨hcr0_lt_ar, hcr2_lt_ar, hcr3_lt_ar, hcr4_lt_ar, hcr3_lt64, hal_lt64⟩ :=
                fc_cref_bounds hpi.len.core_ok (Nat.lt_trans har (by decide)) hcsz3 hcr_fit
              have hcr64 : (cref.setWidth 64).toNat = cref.toNat := bv_c0_zext32_64 cref
              have hcr_u64 : (cref.setWidth 64).toNat + 4 < 2 ^ 64 := by
                rw [hcr64]; exact Nat.lt_trans (Nat.add_lt_add_right cref.isLt 4) (by decide)
              have h1_idx : (cref.setWidth 64 + 1#64).toNat = cref.toNat + 1 := by
                rw [bv64_add_toNat (a := cref.setWidth 64) (b := 1#64)
                  (Nat.lt_trans (Nat.add_lt_add_left (by decide) _) hcr_u64), hcr64]; rfl
              have h2_idx : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2 := by
                rw [bv64_add_toNat (a := cref.setWidth 64) (b := 2#64)
                  (Nat.lt_trans (Nat.add_lt_add_left (by decide) _) hcr_u64), hcr64]; rfl
              have h3_idx : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3 := by
                rw [bv64_add_toNat (a := cref.setWidth 64) (b := 3#64)
                  (Nat.lt_trans (Nat.add_lt_add_left (by decide) _) hcr_u64), hcr64]; rfl
              have h4_idx : (cref.setWidth 64 + 4#64).toNat = cref.toNat + 4 := by
                rw [bv64_add_toNat (a := cref.setWidth 64) (b := 4#64) hcr_u64, hcr64]; rfl
              fc_head_steps
              · have halen_eq : sem.core.arena_len = s.core.arena_len :=
                  hpi.ag.get FullCoreState.arena_len
                have hgt : sem.core.arena_len % 2 ^ 64 < (cref.toNat + 3) % 2 ^ 64 := by
                  simpa only [halen_eq, fastPropMem_arena_len, hcr64, BitVec.reduceToNat] using hc
                rw [Nat.mod_eq_of_lt hal_lt64, Nat.mod_eq_of_lt hcr3_lt64] at hgt
                exact absurd hgt (Nat.not_lt.mpr hcr3_le)
              · exact ih _ (off_v, tend_v, unass_v, unfl_v, ticks_v + 1#64, p_v + 1#64 + 1#64,
                  q_v, end_v, ()) ml hrem_dec
                  ⟨sem, by rw [hp2_nat], propLit_inv_drop (ticks' := sem.scratch.search_ticks) hpi
                    hsw_drop hp2_nat, htend_eq, hunass_eq, hunfl_eq, hnl_eq, hoom_st, hct_st, hml⟩
              · exact ih _ (off_v, tend_v, unass_v, unfl_v, ticks_v + 1#64, p_v + 1#64 + 1#64,
                  q_v, end_v, ()) ml hrem_dec
                  ⟨sem, by rw [hp2_nat], propLit_inv_drop (ticks' := sem.scratch.search_ticks) hpi
                    hsw_drop hp2_nat, htend_eq, hunass_eq, hunfl_eq, hnl_eq, hoom_st, hct_st, hml⟩
              · exact ih _ (off_v, tend_v, unass_v, unfl_v, ticks_v + 1#64, p_v + 1#64 + 1#64,
                  q_v, end_v, ()) ml hrem_dec
                  ⟨sem, by rw [hp2_nat], propLit_inv_drop (ticks' := sem.scratch.search_ticks) hpi
                    hsw_drop hp2_nat, htend_eq, hunass_eq, hunfl_eq, hnl_eq, hoom_st, hct_st, hml⟩
              · have hng_t : fullArenaClauseGarbCore sem.core cref.toNat = false := by
                  unfold fullArenaClauseGarbCore fullArenaHdrCore
                  have hget : sem.core.arena[cref.toNat]? =
                      some (sem.core.arena[cref.toNat]'hcr0_lt_ar) :=
                    List.getElem?_eq_getElem hcr0_lt_ar
                  rw [hget, Option.getD_some]
                  have hh : ((fastPropMem s sem).core.arena[(cref.setWidth 64).toNat]'
                      (by rw [fastPropMem_arena, hcr64]; exact hcr0_lt_ar) &&&
                        0x00080000#32) = 0#32 := by assumption
                  have h0 : (sem.core.arena[cref.toNat]'hcr0_lt_ar &&& 0x00080000#32) = 0#32 := by
                    have hh' := hh
                    simp only [← BitVec.ofNat_eq_ofNat, fastPropMem_arena, hcr64] at hh'
                    exact hh'
                  rw [h0]; rfl
                try clear hc; try clear hc; try clear hc; try clear hc
                refine wp_join_group
                  (fun (other, ()) mj => ∃ sem1 : FullState,
                    PropLitInv c F0 F_cur s sem1 not_lit.toNat off_v.toNat q_v.toNat
                      (p_v.toNat + 2) end_v.toNat ∧
                    sem1.core.oom = 0#64 ∧ sem1.core.confl_type = s.core.confl_type ∧
                    sem1.core.arena_len = sem.core.arena_len ∧
                    sem1.core.trail_end = sem.core.trail_end ∧
                    sem1.core.unassigned = sem.core.unassigned ∧
                    sem1.core.unflushed = sem.core.unflushed ∧
                    sem1.core.cur_level = sem.core.cur_level ∧
                    sem1.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 ∧
                    cref.toNat ∈ fullArenaClauseRefsCore sem1.core ∧
                    fullArenaClauseGarbCore sem1.core cref.toNat = false ∧
                    fullArenaClauseSizeCore sem1.core cref.toNat =
                      fullArenaClauseSizeCore sem.core cref.toNat ∧
                    sem1.core.arena[cref.toNat + 3]? = some other ∧
                    sem1.core.arena[cref.toNat + 4]? = some not_lit ∧
                    (FullMem c (fastPropMem s sem1) ⋆ R) mj) ?_ ?_
                · rintro _ ⟨other, ⟨⟩⟩ mj ⟨sem1, hpi1, hoom1, hct1, halen1, hte1_eq, hun1_eq,
                    huf1_eq, hcl1_eq, hnl1, hcr_ref1, hng1, hcsz1, har3, har4, hmj⟩
                  have htend1_eq : tend_v.toNat = sem1.core.trail_end := htend_eq.trans hte1_eq.symm
                  have hunass1_eq : unass_v = sem1.core.unassigned := hunass_eq.trans hun1_eq.symm
                  have hunfl1_eq : unfl_v = sem1.core.unflushed := hunfl_eq.trans huf1_eq.symm
                  have hlen1_mem := fastPropMem_lengthsOk hlen0 hpi1.len hpi1.cur_vars_eq
                    (hpi1.ag.get FullCoreState.propagated) rfl
                  have hm1_aren := hlen1_mem.core_ok.arena_len_arr
                  have hm1_alen := hlen1_mem.core_ok.arena_len_le
                  have hm1_vals := hlen1_mem.core_ok.vals_len
                  have haren1 := hpi1.len.core_ok.arena_len_arr
                  have halen1_le := hpi1.len.core_ok.arena_len_le
                  have hvals1 := hpi1.len.core_ok.vals_len
                  have hwstk1 := hpi1.len.core_ok.wstk_len_arr
                  have hwvec1 := hpi1.len.core_ok.wvec_len; have hlvl1 := hpi1.len.core_ok.lvl_len
                  have hfl1 := hpi1.len.core_ok.flags_len; have htrl1 := hpi1.len.core_ok.trl_len
                  have htp1 := hpi1.len.core_ok.trail_pos_len
                  have hrsn1 := hpi1.len.core_ok.rsns_len
                  have hph1 := hpi1.len.scratch_ok.phases_len
                  have hcv1_eq := hpi1.cur_vars_eq
                  have hnot_st1 : not_lit.toNat < 2 * sem1.core.cur_vars := hcv1_eq.symm ▸ hnot_lt
                  have hcsz3_1 : 3 ≤ fullArenaClauseSizeCore sem1.core cref.toNat :=
                    hcsz1.symm ▸ hcsz3
                  have hfit1 : cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤
                      sem1.core.arena_len := by rw [hcsz1, halen1]; exact hcr_fit
                  have hcr3_le1 : cref.toNat + 3 ≤ sem1.core.arena_len :=
                    Nat.le_trans (Nat.le_add_right _ _) hfit1
                  have hcr_lt_alen1 : cref.toNat < sem1.core.arena_len :=
                    Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 3)) hcr3_le1
                  have ⟨_, hcr2_lt_ar1, hcr3_lt_ar1, hcr4_lt_ar1, _, _⟩ :=
                    fc_cref_bounds hpi1.len.core_ok (Nat.lt_trans har (by decide)) hcsz3_1 hfit1
                  have hfit1_ar : ∀ {k}, k < fullArenaClauseSizeCore sem1.core cref.toNat →
                      cref.toNat + 3 + k < sem1.core.arena.length := fun hk =>
                    haren1 ▸ Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk (cref.toNat + 3))
                      (Nat.le_trans hfit1 halen1_le)
                  have hother_mem : other.toNat ∈ fullArenaClauseLitsCore sem1.core cref.toNat := by
                    refine (mem_fullArenaClauseLitsCore_iff (haren1 ▸ Nat.le_trans hfit1
                      halen1_le)).mpr ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 3) hcsz3_1, ?_⟩
                    exact congrArg BitVec.toNat (Option.some.inj
                      ((List.getElem?_eq_getElem hcr3_lt_ar1).symm.trans har3))
                  have hother_lt : other.toNat < 2 * sem1.core.cur_vars :=
                    hpi1.nw.arena.lits_lt cref.toNat hcr_ref1 hng1 other.toNat hother_mem
                  have hother_lt1_vals : other.toNat < sem1.core.vals.length :=
                    fastProp_lt_vals hpi1.len.core_ok hother_lt
                  have hq_lt_ws1 : q_v.toNat < sem1.core.wstk.length := by
                    rw [hwstk1, ← hwstk_len]; exact hq_lt_ws2
                  have hq1_lt_ws1 : q_v.toNat + 1 < sem1.core.wstk.length := by
                    rw [hwstk1, ← hwstk_len]; exact hq1_lt_ws2
                  have hcsz_eq1 :
                      (sem1.core.arena[(cref.setWidth 64 + 2#64).toNat]'(h2_idx ▸
                        hcr2_lt_ar1)).toNat = fullArenaClauseSizeCore sem1.core cref.toNat := by
                    unfold fullArenaClauseSizeCore
                    rw [List.getElem?_eq_getElem hcr2_lt_ar1, Option.getD_some]
                    exact congrArg BitVec.toNat
                      (fc_getElem_eq_of_idx h2_idx (h2_idx ▸ hcr2_lt_ar1) hcr2_lt_ar1)
                  fc_head_steps
                  · have hge : 2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 ≤ other.toNat := by
                      simpa only [fastPropMem_cur_vars] using hc
                    rw [Nat.mod_eq_of_lt hcv_lt64, Nat.mod_eq_of_lt h2cv_lt64] at hge
                    exact absurd (hcv1_eq ▸ hother_lt) (Nat.not_lt.mpr hge)
                  · exact ih _ (off_v, tend_v, unass_v, unfl_v, ticks_v + 1#64,
                        p_v + 1#64 + 1#64, q_v + 2#64, end_v, ()) m hrem_dec
                      ⟨_, by rw [hp2_nat], propLit_inv_keep_large hpi1 hpi1.sw hnot_st1 hq1_nat
                        hq2_nat hp2_nat (Nat.add_le_add_right hq_le 2)
                        hpi1.sw.p_le_end (bv32_mask7f_flag0 other) hcr_lt hcr_ref1,
                        htend1_eq, hunass1_eq, hunfl1_eq, hnl1, hoom1, hct1, by
                          simpa only [← BitVec.ofNat_eq_ofNat, fastPropMem_wstk,
                            fastPropMem_with_wstk] using hm⟩
                  · have hov_np :
                        (0#32).slt ((sem1.core.vals[other.toNat]'hother_lt1_vals).signExtend 32) =
                          false := by simpa only [fastPropMem_vals] using hc
                    try clear hc; try clear hc
                    refine wp_join_group (fun (srch_v, ()) ms =>
                        2 ≤ srch_v.toNat ∧
                        srch_v.toNat < fullArenaClauseSizeCore sem1.core cref.toNat ∧
                        ms = mj) ?_ ?_
                    · rintro _ ⟨srch_v, ⟨⟩⟩ ms ⟨hsrch2, hsrch_lt, hms⟩
                      subst ms
                      have hm0_aren := hlen_mem.core_ok.arena_len_arr
                      let csz32 := (fastPropMem s sem).core.arena[
                        (cref.setWidth 64 + 2#64).toNat]'(by
                          rw [hm0_aren, ← haren_len, h2_idx]; exact hcr2_lt_ar)
                      have hcsz32_nat :
                          csz32.toNat = fullArenaClauseSizeCore sem1.core cref.toNat := by
                        rw [hcsz1]
                        have h1 := congrArg BitVec.toNat
                          ((fc_getElem_arena s sem (hi := (by
                              rw [hm0_aren, ← haren_len, h2_idx]; exact hcr2_lt_ar))).trans
                            (fc_getElem_eq_of_idx h2_idx (h2_idx ▸ hcr2_lt_ar) hcr2_lt_ar))
                        have h2 : (sem.core.arena[cref.toNat + 2]'hcr2_lt_ar).toNat =
                            fullArenaClauseSizeCore sem.core cref.toNat := by
                          unfold fullArenaClauseSizeCore
                          rw [List.getElem?_eq_getElem hcr2_lt_ar, Option.getD_some]
                        exact h1.trans h2
                      have hcsz_lt32 : fullArenaClauseSizeCore sem1.core cref.toNat < 2 ^ 32 :=
                        hcsz32_nat ▸ csz32.isLt
                      have hcsz_lt_ff : fullArenaClauseSizeCore sem1.core cref.toNat < 0xFFFFFFFF :=
                        Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left _ _) hfit1)
                          (Nat.lt_of_le_of_lt halen1_le
                            (Nat.lt_trans har (by decide : 2 * 2 ^ 28 < 0xFFFFFFFF)))
                      fc_head_steps
                      refine fastProp_repl_search_wp
                        (nlits := BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat))
                        c.hmaxv c.harena hcv0 ?_ hpi1 hlen1_mem hfit1
                        h3_idx hcsz32_nat hsrch2 hsrch_lt hmj ?_
                      · rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_lt64,
                          Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm, Nat.mod_eq_of_lt h2cv_lt64]
                      · rintro ri_f repl_f _rf hres_f
                        rcases hres_f with ⟨rfl, hfind_bad⟩ | ⟨hri_ne, hr2, hr_lt, hrepl_def, hcand⟩
                        · have hunit := propLit_hunit hpi1.nw hcr_ref1 hng1
                            (haren1 ▸ Nat.le_trans hfit1 halen1_le) har3 har4
                            hpi1.not_f fun k hk1 hk2 => by
                              change k < fullArenaClauseSizeCore sem1.core cref.toNat at hk2
                              have hb := hfind_bad k hk1 (by rwa [← hcr64] at hk2)
                              unfold fullFindReplBad at hb ⊢; rwa [hcr64]
                          have hnot_mem : not_lit.toNat ∈
                              fullArenaClauseLitsCore sem1.core cref.toNat := by
                            refine (mem_fullArenaClauseLitsCore_iff
                              (haren1 ▸ Nat.le_trans hfit1 halen1_le)).mpr
                                ⟨1, Nat.lt_of_lt_of_le (by decide : 1 < 3) hcsz3_1, ?_⟩
                            exact congrArg BitVec.toNat (Option.some.inj
                              ((List.getElem?_eq_getElem hcr4_lt_ar1).symm.trans har4))
                          have hcur_eq1 :
                              ((BitVec.ofNat 64 s.core.cur_level).setWidth 32).toNat =
                                s.core.cur_level := by
                            have hcl64 : s.core.cur_level < 2 ^ 64 :=
                              Nat.lt_trans hclv_lt32 (by decide)
                            rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                              Nat.mod_eq_of_lt hcl64, Nat.mod_eq_of_lt hclv_lt32]
                          fc_head_split
                          all_goals first
                            | exact absurd rfl hc
                            | exact fastProp_large_norepl_wp
                                (nl_lvl0 := nl_lvl0)
                                (cur_lvl := (BitVec.ofNat 64 s.core.cur_level).setWidth 32)
                                (rec_ph := s.core.probing == 0#64)
                                (k_cont := fun te un uf qn => .jump L (.var off_v, (.var te,
                                  (.var un, (.var uf, (.var (ticks_v + 1#64),
                                  (.var (p_v + 1#64 + 1#64), (.var qn, (.var end_v, ())))))))))
                                (k_confl := fun qn => .jump B (.var off_v, (.var tend_v,
                                  (.var unass_v, (.var unfl_v, (.var (ticks_v + 1#64),
                                  (.var (p_v + 1#64 + 1#64), (.var qn, (.var end_v,
                                  (.imm true, ()))))))))))
                                c.hmaxv c.harena c.hwcap hlen0 hcv0
                                hpi1 hlen1_mem hcr_lt hcr_ref1 hng1 hfit1 hother_lt hnot_st1
                                hother_mem hnot_mem hunit hother_lt1_vals (fc_getElem_vals s sem1)
                                hov_np hnl1 hcur_eq1 hclv_lt32 hcsz32_nat h3_idx htend1_eq
                                hunass1_eq hunfl1_eq hoom1 hct1 hq1_nat hq2_nat hp2_nat
                                hq_le hq_lt_ws1 hq1_lt_ws1 hmj
                                (fun sem' tend_n unass_n unfl_n m' hpi' ht' hu' huf' hnl'
                                    hoom' hct' hm' => by
                                  fc_head_steps
                                  exact ih _ (off_v, tend_n, unass_n, unfl_n, ticks_v + 1#64,
                                    p_v + 1#64 + 1#64, q_v + 2#64, end_v, ()) m' hrem_dec
                                    ⟨sem', by rw [hp2_nat], by rwa [hp2_nat], ht', hu', huf',
                                     hnl', hoom', hct', hm'⟩)
                                (fun sem' m' hpi' ht' hu' huf' hcf' hm' => by
                                  fc_head_steps
                                  exact hB (off_v, tend_v, unass_v, unfl_v, ticks_v + 1#64,
                                    p_v + 1#64 + 1#64, q_v + 2#64, end_v, true, ()) m'
                                    ⟨sem', by rwa [hp2_nat], ht', hu', huf', by simp,
                                     fun _ => hcf', hm'⟩)
                        · have hri_ne : ri_f ≠ 0xFFFFFFFF#32 := hri_ne
                          have h3_1_idx : (cref.setWidth 64 + 3#64 + 1#64).toNat =
                              cref.toNat + 4 := by
                            rw [bv64_add_toNat (by
                              rw [h3_idx, ← hcr64, show (1#64).toNat = 1 from rfl]
                              exact hcr_u64), h3_idx]
                            rfl
                          fc_head_split
                          · refine fastProp_large_push_wp hPush (nl_lvl0 := nl_lvl0)
                              (k_ok := fun o4 pn qn en => .jump L (.var o4, (.var tend_v,
                                (.var unass_v, (.var unfl_v, (.var (ticks_v + 1#64),
                                (.var pn, (.var qn, (.var en, ())))))))))
                              (k_oom := fun o4 pn qn en => .jump B (.var o4, (.var tend_v,
                                (.var unass_v, (.var unfl_v, (.var (ticks_v + 1#64),
                                (.var pn, (.var qn, (.var en, (.imm true, ()))))))))))
                              c.hmaxv c.harena hlen0 hcv0
                              hpi1 hlen1_mem hcr_lt hcr_ref1 hfit1 har4 hnot_st1 hother_lt
                              hflag hr2 hr_lt hrepl_def hcand h1_idx h3_idx h3_1_idx
                              htend1_eq hunass1_eq hunfl1_eq hnl1 hoom1 hct1 hp2_nat hq_le
                              (hwstk1 ▸ hq_lt_ws1) hmj ?_ ?_
                            · intro st4 off4_v m_p hdec4 hpi4 ht4 hu4 huf4 hnl4 hoom4 hct4 hm4
                              exact ih _ (off4_v, tend_v, unass_v, unfl_v, ticks_v + 1#64,
                                off4_v + (p_v + 1#64 + 1#64 - off_v), off4_v + (q_v - off_v),
                                off4_v + (end_v - off_v), ()) m_p hdec4
                                ⟨st4, rfl, hpi4, ht4, hu4, huf4, hnl4, hoom4, hct4, hm4⟩
                            · intro st6 off4_v m_f hpi6 ht6 hu6 huf6 hoom6 hm6
                              exact hB (off4_v, tend_v, unass_v, unfl_v, ticks_v + 1#64,
                                off4_v + (p_v + 1#64 + 1#64 - off_v),
                                off4_v + (q_v - off_v) + 2#64,
                                off4_v + (end_v - off_v), true, ()) m_f
                                ⟨_, hpi6, ht6, hu6, huf6, by simp, fun _ => Or.inl hoom6, hm6⟩
                          · exact absurd hc hri_ne
                    · intro Jsrch hJsrch; fc_head_steps
                      · exact hJsrch (2#32, ()) mj
                          ⟨by decide,
                           Nat.lt_of_lt_of_le (by decide : (2#32).toNat < 3) hcsz3_1, rfl⟩
                      · exact hJsrch (2#32, ()) mj
                          ⟨by decide,
                           Nat.lt_of_lt_of_le (by decide : (2#32).toNat < 3) hcsz3_1, rfl⟩
                      · have h1_mod : (cref.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 =
                            cref.toNat + 1 := by
                          simp only [BitVec.reduceToNat]; exact Nat.mod_eq_of_lt (by omega)
                        have h2_mod : (cref.toNat + (2 : BitVec 64).toNat) % 2 ^ 64 =
                            cref.toNat + 2 := by
                          simp only [BitVec.reduceToNat]; exact Nat.mod_eq_of_lt (by omega)
                        have hnot_le_srch :
                            ¬ fullArenaClauseSizeCore sem1.core cref.toNat ≤
                              (sem1.core.arena[cref.toNat + 1]'(by rw [haren1]; omega)).toNat := by
                          have hh : ¬ (sem.core.arena[(cref.toNat + (2 : BitVec 64).toNat) %
                                  2 ^ 64]'(by rw [h2_mod]; exact hcr2_lt_ar)).toNat ≤
                              (sem1.core.arena[(cref.toNat + (1 : BitVec 64).toNat) %
                                  2 ^ 64]'(by rw [h1_mod, haren1]; omega)).toNat := by
                            simpa only [fc_getElem_arena, fastPropMem_arena] using hc
                          have hcsz_0 : (sem.core.arena[cref.toNat + 2]'hcr2_lt_ar).toNat =
                              fullArenaClauseSizeCore sem1.core cref.toNat := by
                            rw [hcsz1]; unfold fullArenaClauseSizeCore
                            rw [List.getElem?_eq_getElem hcr2_lt_ar, Option.getD_some]
                          simp only [fc_getElem_eq_of_idx h2_mod _ hcr2_lt_ar, hcsz_0,
                            fc_getElem_eq_of_idx h1_mod _ (by rw [haren1]; omega)] at hh
                          exact hh
                        have h1_mod' : (cref.toNat + 1) % 2 ^ 64 = cref.toNat + 1 :=
                          Nat.mod_eq_of_lt (by omega)
                        have hnot_lt_2 :
                            ¬ (sem1.core.arena[cref.toNat + 1]'(by rw [haren1]; omega)).toNat < 2 :=
                          by
                          have hh : ¬ ((fastPropMem s sem1).core.arena[(cref.toNat +
                                (1 : BitVec 64).toNat) % 2 ^ 64]'(by
                              rw [fastPropMem_arena, h1_mod, haren1]; omega)).toNat <
                              (2 : BitVec 32).toNat := by assumption
                          simpa only [fc_getElem_arena, fastPropMem_arena, BitVec.reduceToNat,
                            h1_mod'] using hh
                        have hsrch_mem :
                            (fastPropMem s sem1).core.arena[(cref.setWidth 64 + 1).toNat]'(by
                              rw [show (1 : BitVec 64) = 1#64 from rfl, fastPropMem_arena,
                                h1_idx, haren1]
                              omega) =
                            sem1.core.arena[cref.toNat + 1]'(by rw [haren1]; omega) := by
                          rw [fc_getElem_arena]
                          exact fc_getElem_eq_of_idx
                            (by rw [show (1 : BitVec 64) = 1#64 from rfl]; exact h1_idx) _ _
                        refine hJsrch _ mj
                          ⟨by simpa only [hsrch_mem] using Nat.le_of_not_lt hnot_lt_2,
                           by simpa only [hsrch_mem] using Nat.lt_of_not_le hnot_le_srch, rfl⟩
                · intro J3 hJ3; fc_head_steps
                  · let l1 := sem.core.arena[(cref.setWidth 64 + 4#64).toNat]'(h4_idx ▸ hcr4_lt_ar)
                    have h3_mod : (cref.toNat + BitVec.toNat (3 : BitVec 64)) % 2 ^ 64 =
                        cref.toNat + 3 := by
                      simp only [BitVec.reduceToNat]; exact Nat.mod_eq_of_lt hcr3_lt64
                    have hl0_is_not : sem.core.arena[cref.toNat + 3]'hcr3_lt_ar = not_lit :=
                      (fc_getElem_eq_of_idx h3_mod _ _).symm.trans
                        ((fc_getElem_arena s sem).symm.trans hc)
                    have hpi_drop : PropLitInv c F0 F_cur s sem not_lit.toNat off_v.toNat
                        q_v.toNat (p_v.toNat + 2) end_v.toNat :=
                      ⟨hpi.len, hpi.nw, hsw_drop, hpi.ag, hpi.tr, hpi.perm, hpi.sc_eq,
                       hpi.not_f⟩
                    have ⟨hpi1, href1, hng1, hcsz1, har3, har4⟩ := fastProp_js3_swap hpi_drop
                      hcr_ref hng_t hcsz3 hcr_fit hl0_is_not
                      (fc_getElem_eq_of_idx h4_idx.symm hcr4_lt_ar (h4_idx ▸ hcr4_lt_ar))
                    have h3_1_idx : (cref.setWidth 64 + 3#64 + 1#64).toNat = cref.toNat + 4 := by
                      rw [bv64_add_toNat (by
                        rw [h3_idx, ← hcr64, show (1#64).toNat = 1 from rfl]; exact hcr_u64),
                        h3_idx]; rfl
                    have hl1_mem_eq :
                        (fastPropMem s sem).core.arena[
                          (cref.setWidth 64 + 3#64 + 1#64).toNat]'(by
                            rw [fastPropMem_arena, h3_1_idx]; exact hcr4_lt_ar) = l1 := by
                      rw [fc_getElem_arena]
                      exact (fc_getElem_eq_of_idx h3_1_idx _ hcr4_lt_ar).trans
                        (fc_getElem_eq_of_idx h4_idx.symm hcr4_lt_ar (h4_idx ▸ hcr4_lt_ar))
                    have hm1 : (FullMem c (fastPropMem s { sem with core := { sem.core with
                        arena := (sem.core.arena.set (cref.toNat + 3) l1).set
                          (cref.toNat + 4) not_lit } }) ⋆ R) m := by
                      simp only [BitVec.ofNat_eq_ofNat, fastPropMem_arena,
                        h3_idx, h3_1_idx] at hm
                      have hl1_idx : sem.core.arena[cref.toNat + 4]'hcr4_lt_ar = l1 :=
                        fc_getElem_eq_of_idx h4_idx.symm hcr4_lt_ar (h4_idx ▸ hcr4_lt_ar)
                      rw [hl1_idx, show (lit ^^^ 1#32) = not_lit from rfl] at hm
                      simpa only [← fastPropMem_with_arena] using hm
                    simp only [BitVec.ofNat_eq_ofNat]
                    rw [hl1_mem_eq]
                    exact hJ3 (l1, ()) m ⟨_, hpi1, hoom_st, hct_st, rfl, rfl, rfl, rfl, rfl,
                      hnl_eq, href1, hng1, hcsz1, har3, har4, hm1⟩
                  · exact ih _ (off_v, tend_v, unass_v, unfl_v, ticks_v + 1#64, p_v + 1#64 + 1#64,
                      q_v, end_v, ()) ml hrem_dec
                      ⟨sem, by rw [hp2_nat], propLit_inv_drop (ticks' := sem.scratch.search_ticks)
                        hpi hsw_drop hp2_nat, htend_eq, hunass_eq, hunfl_eq, hnl_eq, hoom_st,
                        hct_st, hml⟩
                  · have h4_mod :
                        (cref.toNat + BitVec.toNat (3 : BitVec 64) + BitVec.toNat (1 : BitVec 64)) %
                          2 ^ 64 = cref.toNat + 4 := by
                      simp only [BitVec.reduceToNat]; exact Nat.mod_eq_of_lt (by omega)
                    have hl1_eq4 : sem.core.arena[cref.toNat + 4]'(hcr4_lt_ar) = not_lit :=
                      (fc_getElem_eq_of_idx h4_mod _ _).symm.trans
                        ((fc_getElem_arena s sem).symm.trans hc)
                    exact hJ3 (_, ()) ml ⟨sem, ⟨hpi.len, hpi.nw, hsw_drop, hpi.ag, hpi.tr,
                        hpi.perm, hpi.sc_eq, hpi.not_f⟩, hoom_st, hct_st, rfl, rfl, rfl, rfl, rfl,
                      hnl_eq, hcr_ref, hng_t, rfl,
                      by rw [fc_getElem_arena, List.getElem?_eq_getElem hcr3_lt_ar]
                         exact congrArg some
                           (fc_getElem_eq_of_idx
                             (by rw [show (3 : BitVec 64) = 3#64 from rfl]; exact h3_idx.symm)
                             hcr3_lt_ar _),
                      by change sem.core.arena[cref.toNat + 4]? = some not_lit
                         rw [← hl1_eq4]; exact List.getElem?_eq_getElem hcr4_lt_ar,
                      hml⟩
            · intro J2 hJ2; fc_head_steps
              · exact ih _ (off_v, tend_v, unass_v, unfl_v, ticks_v, p_v + 1#64 + 1#64,
                  q_v + 2#64, end_v, ()) m hrem_dec
                  ⟨_, by rw [hp2_nat], propLit_inv_keep_large hpi hsw_drop hnot_st hq1_nat hq2_nat
                    hp2_nat (Nat.add_le_add_right hq_le 2) h2_le_end hflag hcr_lt hcr_ref,
                    htend_eq, hunass_eq, hunfl_eq, hnl_eq, hoom_st, hct_st, by
                      simpa only [fastPropMem_wstk, fastPropMem_with_wstk] using hm⟩
              · exact hJ2 () ml rfl
              · exact hJ2 () ml rfl
      · exact hB (off_v, tend_v, unass_v, unfl_v, ticks_v, p_v, q_v, end_v, false, ()) ml
          ⟨sem, hpi, htend_eq, hunass_eq, hunfl_eq, fun _ => ⟨hoom_st, hct_st⟩, by simp, hml⟩
    · intro B L _ hL; fc_head_steps
      have hoff_bd := hwat0.layout.bounds not_lit.toNat hnot_lt
      have hwlen_le := hlen0.core_ok.wlen_le
      have hoff_nat :
          ((s.core.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : Nat)).toNat]'(by
            rw [fc_bv64_shl1_u32_nat, show (lit ^^^ (1 : BitVec 32)) = not_lit from rfl, hwv0]
            have := Nat.mul_le_mul_left 2 hcv0; omega)).setWidth 64).toNat =
          fullWatchOffCore s.core not_lit.toNat := by
        unfold fullWatchOffCore; rw [bv_c0_zext32_64]
        exact congrArg BitVec.toNat (fc_getElem_eq_getD_of_idx (fc_bv64_shl1_u32_nat _) _)
      have hsz_nat : ((s.core.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : Nat)) +
          (1 : BitVec 64)).toNat]'(by
            rw [fc_bv64_shl1_add1_nat, show (lit ^^^ (1 : BitVec 32)) = not_lit from rfl, hwv0]
            have := Nat.mul_le_mul_left 2 hcv0; omega)).setWidth 64).toNat =
          fullWatchSizeCore s.core not_lit.toNat := by
        unfold fullWatchSizeCore; rw [bv_c0_zext32_64]
        exact congrArg BitVec.toNat (fc_getElem_eq_getD_of_idx (fc_bv64_shl1_add1_nat _) _)
      have hend_nat :
          ((s.core.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : Nat)).toNat]'(by
            rw [fc_bv64_shl1_u32_nat, show (lit ^^^ (1 : BitVec 32)) = not_lit from rfl, hwv0]
            have := Nat.mul_le_mul_left 2 hcv0; omega)).setWidth 64 +
          (s.core.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : Nat)) +
            (1 : BitVec 64)).toNat]'(by
              rw [fc_bv64_shl1_add1_nat, show (lit ^^^ (1 : BitVec 32)) = not_lit from rfl, hwv0]
              have := Nat.mul_le_mul_left 2 hcv0; omega)).setWidth 64).toNat =
          fullWatchOffCore s.core not_lit.toNat + fullWatchSizeCore s.core not_lit.toNat := by
        rw [bv64_add_toNat (by
          rw [hoff_nat, hsz_nat]
          exact Nat.lt_of_le_of_lt (Nat.le_trans hoff_bd hwlen_le) (Nat.lt_trans hwc (by decide))),
          hoff_nat, hsz_nat]
      have hoff_g : ∀ h,
          ((s.core.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : Nat)).toNat]'h).setWidth
            64).toNat = fullWatchOffCore s.core not_lit.toNat := fun _ => hoff_nat
      have hend_g : ∀ h1 h2,
          ((s.core.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : Nat)).toNat]'h1).setWidth
            64 +
          (s.core.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : Nat)) +
            (1 : BitVec 64)).toNat]'h2).setWidth 64).toNat =
          fullWatchOffCore s.core not_lit.toNat + fullWatchSizeCore s.core not_lit.toNat :=
        fun _ _ => hend_nat
      have htend0 : (BitVec.ofNat 64 s.core.trail_end).toNat = s.core.trail_end := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hte0_lt64]
      refine hL _ _ m ⟨s, rfl, ?_, htend0, rfl, rfl, hnl_eq0, hoom0, rfl, ?_⟩
      · rw [hend_g, hoff_g]; exact hpi0
      · rw [fastPropMem_self]; exact hm

theorem full_propagate_ignore_m4_wp (Γ : Env)
    (hPropLit : ∀ args m Q X, fullPropLitSpec args m Q X →
      Γ "full_prop_lit_m4" [i64, i32, i64] [.bool] args m Q X) :
    ∀ args m Q X, fullPropagateIgnoreSpec args m Q X →
      Func.wp Γ full_propagate_ignore_m4_body args m Q X := by
  rintro ⟨h, ignore_ref, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hm, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hret_st : ∀ (r : BitVec 64) (st : FullState) (ml : Mem 64),
      st.LengthsOk c → FullWitnessInv c F0 F_cur st.core →
      AgreesExcept fastPropCoreMask s.core st.core →
      FullTrailExt s.core st.core → FullArenaPermEq s.core st.core →
      st.core.fuel.toNat ≤ s.core.fuel.toNat →
      st.scratch = { s.scratch with
        search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
        phases := st.scratch.phases } →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → st.core.propagated = st.core.trail_end ∧
        st.core.confl_type = s.core.confl_type ∧
        (s.core.oom = 0#64 → st.core.oom = 0#64) ∧
        (s.core.propagated < s.core.trail_end → st.core.fuel.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → st.core.fuel.toNat < s.core.fuel.toNat ∧ st.core.oom = 0#64 ∧
        FullConflictOkW F_cur st ∧
        (st.core.confl_type = 2#64 → st.core.confl_ref ≠ ignore_ref)) →
      (r = 2#64 → st.core.oom ≠ 0#64 ∨ st.core.fuel = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ st = s) →
      (FullMem c st ⋆ R) ml → Q (r, ()) ml := by
    intro r st ml hst_l hst_w hag htr hperm hfl hsc hr hr0 hr1 hr2 hnoop hml
    have hst_eq : st =
        { core :=
            { s.core with
              vals := st.core.vals, flags := st.core.flags, lvl := st.core.lvl,
              rsns := st.core.rsns, trl := st.core.trl, trail_pos := st.core.trail_pos,
              trail_end := st.core.trail_end, propagated := st.core.propagated,
              unassigned := st.core.unassigned, unflushed := st.core.unflushed,
              wvec := st.core.wvec, arena := st.core.arena, wstk := st.core.wstk,
              wlen := st.core.wlen, wusable := st.core.wusable, fuel := st.core.fuel,
              confl_type := st.core.confl_type, confl_ref := st.core.confl_ref,
              confl_lit0 := st.core.confl_lit0, confl_lit1 := st.core.confl_lit1,
              oom := st.core.oom }
          scratch := { s.scratch with
            search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
            phases := st.scratch.phases } } := by
      have h1 := hag.get FullCoreState.d_cur; have h2 := hag.get FullCoreState.d_val
      have h3 := hag.get FullCoreState.cur_vars; have h4 := hag.get FullCoreState.arena_len
      have h5 := hag.get FullCoreState.arena_garbage
      have h6 := hag.get FullCoreState.first_reducible
      have h7 := hag.get FullCoreState.num_irred; have h8 := hag.get FullCoreState.num_redundant
      have h9 := hag.get FullCoreState.num_binary; have h10 := hag.get FullCoreState.probing
      have h11 := hag.get FullCoreState.cur_level; have h12 := hag.get FullCoreState.tmp_cnt
      have h13 := hag.get FullCoreState.tmp_len; have h14 := hag.get FullCoreState.min_clr_len
      have h15 := hag.get FullCoreState.min_clr_full; have h16 := hag.get FullCoreState.dense_mode
      have h17 := hag.get FullCoreState.inconsistent; have h18 := hag.get FullCoreState.lit_mark
      have h19 := hag.get FullCoreState.mrk; have h20 := hag.get FullCoreState.tmp
      have h21 := hag.get FullCoreState.min_clr; have h22 := hag.get FullCoreState.frame_trail
      have h23 := hag.get FullCoreState.frame_dec; have h24 := hag.get FullCoreState.repr
      have h25 := hag.get FullCoreState.min_stk
      cases st with | mk stc stsc =>
      cases s with | mk sc ssc =>
      dsimp only at hsc; rw [hsc]
      cases stc; cases sc; simp only at *; subst_vars; rfl
    have hst_l' := hst_l; have hst_w' := hst_w; have htr' := htr; have hperm' := hperm
    rw [hst_eq] at hst_l' hst_w' htr' hperm' hml
    refine hQ r st.core.vals st.core.flags st.core.lvl st.core.rsns st.core.trl st.core.trail_pos
      st.core.trail_end st.core.propagated st.core.unassigned st.core.unflushed st.core.wvec
      st.core.arena st.core.wstk st.core.wlen st.core.wusable st.core.fuel st.core.confl_type
      st.core.confl_ref st.core.confl_lit0 st.core.confl_lit1 st.core.oom
      st.scratch.search_ticks st.scratch.wsort st.scratch.phases ml
      hst_l' hst_w' htr' hperm' hfl hr hr0 ?_ hr2 ?_ hml
    · intro h1; have hcf := hr1 h1; rw [hst_eq] at hcf; exact hcf
    · intro hpe; obtain ⟨h0, heq⟩ := hnoop hpe; exact ⟨h0, hst_eq ▸ heq⟩
  unfold Func.wp full_propagate_ignore_m4_body
  fc_hsteps
  refine wp_loop_group
    (fun rem (prop_v, fuel_v, ()) ml => ∃ memSt : FullState,
      rem = fuel_v.toNat ∧ memSt.LengthsOk c ∧ FullWitnessInv c F0 F_cur memSt.core ∧
      memSt.core.fuel = s.core.fuel ∧ memSt.core.propagated = prop_v.toNat ∧
      AgreesExcept fastPropCoreMask s.core memSt.core ∧
      FullTrailExt s.core memSt.core ∧ FullArenaPermEq s.core memSt.core ∧
      fuel_v.toNat ≤ s.core.fuel.toNat ∧
      memSt.scratch = { s.scratch with
        search_ticks := memSt.scratch.search_ticks, wsort := memSt.scratch.wsort,
        phases := memSt.scratch.phases } ∧
      (s.core.oom = 0#64 → memSt.core.oom = 0#64) ∧
      memSt.core.confl_type = s.core.confl_type ∧
      (fuel_v.toNat = s.core.fuel.toNat →
        { memSt with core := { memSt.core with fuel := fuel_v } } = s) ∧
      (s.core.propagated = s.core.trail_end → memSt = s ∧ fuel_v = s.core.fuel) ∧
      (FullMem c memSt ⋆ R) ml) ?_ ?_
  · rintro L rem ⟨prop_v, fuel_v, ⟨⟩⟩ ml ih
      ⟨memSt, rfl, hml_l, hml_w, hmfuel, hmprop, hag, htr, hperm, hfuel_le, hsc, hoom_pres,
        hct_pres, hsame, hnoop, hml⟩
    have hcl := hml_l.core_ok
    have hcv_le := hcl.cur_vars_le
    have htl := hcl.trl_len; have hte_le := hcl.trail_end_le; have hpr_le := hcl.propagated_le
    have hdm_st : memSt.core.dense_mode = 0#64 := (hag.get FullCoreState.dense_mode).trans hdense0
    fc_hsteps
    · have hpr_lt : prop_v.toNat < memSt.core.trail_end := by c0_bound
      have hne_end : s.core.propagated ≠ s.core.trail_end := fun h => by
        obtain ⟨hm_s, _⟩ := hnoop h; subst hm_s; omega
      let finSt : FullState :=
        { memSt with core := { memSt.core with propagated := prop_v.toNat, fuel := fuel_v } }
      exact hret_st 2#64 finSt m
        ⟨{ hcl with propagated_le := by dsimp [finSt]; omega }, hml_l.scratch_ok⟩
        (hml_w.with_fuel_prop fuel_v prop_v.toNat)
        (hag.update fun k => { k with propagated := prop_v.toNat, fuel := fuel_v })
        (fastTrailExt_congr htr rfl rfl rfl) hperm hfuel_le hsc (Or.inr (Or.inr rfl))
        (by simp) (by simp) (fun _ => Or.inl hc) (fun hpe => absurd hpe hne_end)
        (by simpa [finSt, hmprop] using hm)
    · have hpr_lt : prop_v.toNat < memSt.core.trail_end := by c0_bound
      have hne_end : s.core.propagated ≠ s.core.trail_end := fun h => by
        obtain ⟨hm_s, _⟩ := hnoop h; subst hm_s; omega
      let finSt : FullState :=
        { memSt with core := { memSt.core with propagated := prop_v.toNat, fuel := fuel_v } }
      exact hret_st 2#64 finSt m
        ⟨{ hcl with propagated_le := by dsimp [finSt]; omega }, hml_l.scratch_ok⟩
        (hml_w.with_fuel_prop fuel_v prop_v.toNat)
        (hag.update fun k => { k with propagated := prop_v.toNat, fuel := fuel_v })
        (fastTrailExt_congr htr rfl rfl rfl) hperm hfuel_le hsc (Or.inr (Or.inr rfl))
        (by simp) (by simp) (fun _ => Or.inr hc) (fun hpe => absurd hpe hne_end)
        (by simpa [finSt, hmprop] using hm)
    · have hpr_lt : prop_v.toNat < memSt.core.trail_end := by c0_bound
      have hne_end : s.core.propagated ≠ s.core.trail_end := fun h => by
        obtain ⟨hm_s, _⟩ := hnoop h; subst hm_s; omega
      have hoom0_st : memSt.core.oom = 0#64 := by assumption
      have hfuel_sub : (fuel_v - 1#64).toNat = fuel_v.toNat - 1 := bv64_sub1_toNat hc
      have hfuel_pos : 0 < fuel_v.toNat :=
        Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
      have hpr1 : (prop_v + (1 : BitVec 64)).toNat = prop_v.toNat + 1 := by c0_bound
      let memSt1 : FullState :=
        { memSt with core := { memSt.core with propagated := prop_v.toNat + 1 } }
      have hlen1 : memSt1.LengthsOk c :=
        ⟨{ hcl with propagated_le := by dsimp [memSt1]; omega }, hml_l.scratch_ok⟩
      have hw1 : FullWitnessInv c F0 F_cur memSt1.core := hml_w.with_fuel_prop _ _
      have hm1_mem : (FullMem c memSt1 ⋆ R) m := by
        simpa only [memSt1, show (prop_v + (1 : BitVec 64)).toNat = prop_v.toNat + 1 from hpr1]
          using hm
      c0_call hPropLit
      refine ⟨c, F0, F_cur, memSt1, R, rfl, hlen1, hw1, hdm_st, hoom0_st, hm1_mem,
        fun ok vals' flags' lvl' rsns' trl' tp' te' unas' unfl' wvec' arena' wstk' wlen' wu'
          ctype' cref' c0' c1' oom' ticks' wsort' phases' m2 hlen2 hw2 htr2 hperm2
          hcf hok_t_spec hm2 => ?_⟩
      let memSt2 : FullState :=
        { core :=
            { memSt1.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
              trail_pos := tp', trail_end := te', unassigned := unas', unflushed := unfl',
              wvec := wvec', arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
              confl_type := ctype', confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
              oom := oom' }
          scratch := { memSt1.scratch with
            search_ticks := ticks', wsort := wsort', phases := phases' } }
      have hag1 : AgreesExcept fastPropCoreMask s.core memSt1.core :=
        hag.update fun k => { k with propagated := memSt1.core.propagated }
      have hag2 : AgreesExcept fastPropCoreMask s.core memSt2.core :=
        hag1.update fun k => { k with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', unassigned := unas', unflushed := unfl',
          wvec := wvec', arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
          confl_type := ctype', confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
          oom := oom' }
      have htr12 : FullTrailExt s.core memSt2.core :=
        fastTrailExt_trans (fastTrailExt_congr htr (k2 := memSt1.core) rfl rfl rfl) htr2
      have hperm12 : FullArenaPermEq s.core memSt2.core := fastArenaPerm_trans hperm hperm2
      have hsc2 : memSt2.scratch = { s.scratch with
          search_ticks := memSt2.scratch.search_ticks, wsort := memSt2.scratch.wsort,
          phases := memSt2.scratch.phases } := by dsimp [memSt2, memSt1]; rw [hsc]
      have hfl2_lt : (fuel_v - 1#64).toNat < s.core.fuel.toNat := by omega
      fc_hsteps
      · have hok_t : ok = true := by assumption
        exact ih (fuel_v - 1#64).toNat (prop_v + 1#64, fuel_v - 1#64, ()) m2 (by omega)
          ⟨memSt2, rfl, hlen2, hw2, hmfuel, hpr1.symm, hag2, htr12, hperm12, by omega, hsc2,
            fun _ => (hok_t_spec hok_t).1, (hok_t_spec hok_t).2.trans hct_pres,
            fun heq => by omega, fun hpe => absurd hpe hne_end, hm2⟩
      · have hok_f : ok = false := by assumption
        let finSt2 : FullState := { memSt2 with core := { memSt2.core with fuel := fuel_v - 1#64 } }
        exact hret_st 2#64 finSt2 m
          ⟨{ hlen2.core_ok with vals_len := hlen2.core_ok.vals_len }, hlen2.scratch_ok⟩
          (hw2.with_fuel_prop _ _)
          (hag2.update fun k => { k with fuel := fuel_v - 1#64 })
          (fastTrailExt_congr htr12 rfl rfl rfl) hperm12 (by dsimp [finSt2]; omega) hsc2
          (Or.inr (Or.inr rfl)) (by simp) (by simp) (fun _ => Or.inl hc)
          (fun hpe => absurd hpe hne_end) hm
      · have hok_f : ok = false := by assumption
        have hoom2_0 : oom' = 0#64 := by assumption
        have ⟨hcf_ok, hcf_ign⟩ := (hcf hok_f).resolve_left (fun h => h hoom2_0)
        let finSt2 : FullState := { memSt2 with core := { memSt2.core with fuel := fuel_v - 1#64 } }
        exact hret_st 1#64 finSt2 m
          ⟨{ hlen2.core_ok with vals_len := hlen2.core_ok.vals_len }, hlen2.scratch_ok⟩
          (hw2.with_fuel_prop _ _)
          (hag2.update fun k => { k with fuel := fuel_v - 1#64 })
          (fastTrailExt_congr htr12 rfl rfl rfl) hperm12 (by dsimp [finSt2]; omega) hsc2
          (Or.inr (Or.inl rfl)) (by simp)
          (fun _ => ⟨by dsimp [finSt2]; exact hfl2_lt, hoom2_0,
            by simpa only [FullConflictOkW, fullArenaClauseRefs, fullArenaClauseGarb,
                 fullArenaClauseLits, fullArenaClauseRefsCore, fullArenaClauseGarbCore,
                 fullArenaClauseLitsCore, fullArenaClauseSizeCore, fullArenaHdrCore,
                 finSt2] using hcf_ok,
            hcf_ign⟩)
          (by simp) (fun hpe => absurd hpe hne_end) hm
    · have hpr_eq : prop_v.toNat = memSt.core.trail_end := by c0_bound
      let finSt : FullState :=
        { memSt with core := { memSt.core with propagated := prop_v.toNat, fuel := fuel_v } }
      exact hret_st 0#64 finSt m
        ⟨{ hcl with propagated_le := by dsimp [finSt]; omega }, hml_l.scratch_ok⟩
        (hml_w.with_fuel_prop fuel_v prop_v.toNat)
        (hag.update fun k => { k with propagated := prop_v.toNat, fuel := fuel_v })
        (fastTrailExt_congr htr rfl rfl rfl) hperm hfuel_le hsc (Or.inl rfl)
        (fun _ => ⟨by dsimp [finSt]; exact hpr_eq, hct_pres, hoom_pres, fun hlt => by
          by_cases hf : fuel_v.toNat = s.core.fuel.toNat
          · have hsame_st := hsame hf
            have : finSt = s := by rw [← hsame_st]; dsimp [finSt]; rw [← hmprop]
            subst this; dsimp [finSt] at hlt; omega
          · dsimp [finSt]; omega⟩)
        (by simp) (by simp)
        (fun hpe => by
          obtain ⟨hm_s, hf_s⟩ := hnoop hpe
          refine ⟨rfl, ?_⟩
          dsimp [finSt]; rw [← hmprop, hm_s, hf_s])
        hm
  · intro L hL; fc_hsteps
    have hpr_lt64 : s.core.propagated < 2 ^ 64 := by
      have := hlen0.core_ok.propagated_le; have := hlen0.core_ok.trail_end_le
      have := hlen0.core_ok.cur_vars_le; omega
    exact hL s.core.fuel.toNat (BitVec.ofNat 64 s.core.propagated, s.core.fuel, ()) m
      ⟨s, rfl, hlen0, hw0, rfl, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpr_lt64],
       .refl _ _, ⟨Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl⟩,
       ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, .refl _⟩⟩, Nat.le_refl _, rfl, fun h => h, rfl,
       fun _ => by cases s with | mk sc ssc => cases sc; rfl, fun _ => ⟨rfl, rfl⟩, hm⟩

theorem full_bcp_m4_wp (Γ : Env)
    (hPropIgn : ∀ args m Q X, fullPropagateIgnoreSpec args m Q X →
      Γ "full_propagate_ignore_m4" [i64, i64] [i64] args m Q X) :
    ∀ args m Q X, fullPropagateSpec args m Q X →
      Func.wp Γ full_bcp_m4_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hm, hQ⟩
  unfold Func.wp full_bcp_m4_body
  fc_hsteps
  c0_call hPropIgn
  refine ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hm,
    fun r vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m' hlen' hw' htr' hperm' hfl' hr hr0
      hr1 hr2 hnoop hm' => ?_⟩
  fc_hsteps
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m' hlen' hw' htr' hperm'
    hfl' hr
    (fun h0 => let ⟨hp, _, ho, hf⟩ := hr0 h0; ⟨hp, ho, hf⟩)
    (fun h1 => let ⟨hf, ho, hca, _⟩ := hr1 h1; ⟨hf, ho, hca⟩) hr2 hnoop hm'

/-! ## 3. Explicit `FullSparseInv` Preservation & UNSAT Soundness -/

private theorem m4ConflOkW_of_full {F_cur : List (List Nat)} {s : FullState}
    (h : Full.FullConflictOkW F_cur s) : FullPropDecSpecs.FullConflOkW F_cur s.core := by
  rcases h with ⟨ht, h0, h1, hf0, hf1, hent⟩ | hr
  · exact Or.inl ⟨ht, h0, h1, hent, hf0, hf1⟩
  · exact Or.inr hr

theorem full_bcp_m4_preserves_sparseInv {Γ : Env}
    (hPropIgn : ∀ args m Q X, fullPropagateIgnoreSpec args m Q X →
      Γ "full_propagate_ignore_m4" [i64, i64] [i64] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hsp : FullPropDecSpecs.FullSparseInv c F0 s) (hm : (FullMem c s ⋆ R) m)
    (Q : Post [i64]) (X : XPost)
    (hpost : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullPropDecSpecs.FullSparseInv c F0 s' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 1#64 → s'.core.cur_level = 0 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    Func.wp Γ full_bcp_m4_body (c.hdr, ()) m Q X := by
  obtain ⟨⟨hlen0, F_cur, hw0⟩, hmk0, hnd0, ⟨hll0, hext0⟩, hdm0⟩ := hsp
  apply full_bcp_m4_wp Γ hPropIgn
  refine ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdm0, hm,
    fun r vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m' hlen' hw' _htr' hperm' _hfl' hr
      _hr0 hr1 _hr2 _hnoop hm' => ?_⟩
  let s' : FullState :=
    { core :=
        { s.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', propagated := prop', unassigned := unas',
          unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
          wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
          confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } }
  have hperm_sp : FullPropDecSpecs.FullArenaPermEq s.core s'.core :=
    ⟨hperm'.2.1, hperm'.2.2⟩
  have hmk' : FullPropDecSpecs.FullLitMarksClear c s' := hmk0
  have hnd' : FullPropDecSpecs.FullArenaVarsNodup s' := hperm_sp.preserves_varsNodup hnd0
  have hll' : FullPropDecSpecs.FullLastLearnedWf s' :=
    hperm_sp.preserves_lastLearnedWf rfl hll0
  have hsp' : FullPropDecSpecs.FullSparseInv c F0 s' :=
    ⟨⟨hlen', F_cur, hw'⟩, hmk', hnd', ⟨hll', hext0⟩, hdm0⟩
  refine hpost r s' m' hsp' hr (fun h1 hcl0 => ?_) hm'
  exact hw'.level0_unsat_of_conflOkW hcl0 (m4ConflOkW_of_full (hr1 h1).2.2)

/-! ## 4. Closed `ModuleOk` & Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`) -/

/-- Canonical `FullSpec2` specification table for `m4BcpModule` plus extern `full_watch_push`. -/
def m4BcpSpecTable : List SpecEntry :=
  [ ⟨"full_prop_lit_m4", [i64, i32, i64], [.bool], Full.fullPropLitSpec, true⟩
  , ⟨"full_propagate_ignore_m4", [i64, i64], [i64], Full.fullPropagateIgnoreSpec, true⟩
  , ⟨"full_bcp_m4", [i64], [i64], Full.fullPropagateSpec, true⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  ]

/-- Specification environment induced by `m4BcpSpecTable`. -/
def m4BcpEnv : Env := Env.ofTable m4BcpSpecTable

theorem m4BcpSpecTable_noExit : ∀ e ∈ m4BcpSpecTable, e.noExit = true := by
  intro e he
  simp only [m4BcpSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> rfl

theorem m4Bcp_noExit :
    ∀ f as bs xs m Q X X', m4BcpEnv f as bs xs m Q X → m4BcpEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m4BcpSpecTable_noExit

private theorem m4BcpSpecTable_nodup : (m4BcpSpecTable.map SpecEntry.name).Nodup := by
  show (["full_prop_lit_m4", "full_propagate_ignore_m4", "full_bcp_m4",
    "full_watch_push"] : List String).Nodup
  decide

private theorem m4BcpEnv_row_at (i : Nat) (e : SpecEntry)
    (hi : m4BcpSpecTable[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → m4BcpEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) m4BcpSpecTable_nodup (hno xs m Q X h)

/-- Row-by-row `TableImpl` for `m4Bcp_fns` against `m4BcpSpecTable`. -/
theorem m4Bcp_tableImpl : TableImpl m4BcpEnv m4Bcp_fns m4BcpSpecTable := by
  let hPush := m4BcpEnv_row_at 3
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  let hPropLit := m4BcpEnv_row_at 0
    ⟨"full_prop_lit_m4", [i64, i32, i64], [.bool], Full.fullPropLitSpec, true⟩
  let hPropIgn := m4BcpEnv_row_at 1
    ⟨"full_propagate_ignore_m4", [i64, i64], [i64], Full.fullPropagateIgnoreSpec, true⟩
  exact ⟨.of (full_prop_lit_m4_wp m4BcpEnv hPush),
    ⟨.of (full_propagate_ignore_m4_wp m4BcpEnv hPropLit),
    ⟨.of (full_bcp_m4_wp m4BcpEnv hPropIgn), trivial⟩⟩⟩

/-- Closed `ModuleOk` for standalone `m4BcpModule` under `m4BcpEnv`. -/
theorem m4Bcp_moduleOk : ModuleOk m4BcpEnv m4BcpModule :=
  Env.ofTable_moduleOk m4Bcp_acyclic
    ⟨full_prop_lit_m4_wf, full_propagate_ignore_m4_wf, full_bcp_m4_wf, trivial⟩
    m4Bcp_tableImpl

/-- Concrete `Mem 64` binary-watch UNSAT soundness for `full_bcp_m4_body` under `m4BcpEnv`
(`XPost := False`): proves non-vacuity and derives `nvOneLitF0.Unsat` on conflict (`r = 1#64`). -/
theorem nv_m4_bcp_sound :
    Func.wp m4BcpEnv full_bcp_m4_body (nvFastPropCfg.hdr, ()) nvFastPropMem
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) ∧
        (r = 1#64 → Full.nvOneLitF0.Unsat) ∧
        ∃ s', (FullMem nvFastPropCfg s' ⋆ emp) m')
      (fun _ _ _ _ => False) := by
  let hPropIgn := m4BcpEnv_row_at 1
    ⟨"full_propagate_ignore_m4", [i64, i64], [i64], Full.fullPropagateIgnoreSpec, true⟩
  apply full_bcp_m4_wp m4BcpEnv hPropIgn
  refine ⟨nvFastPropCfg, Full.nvOneLitF0, [[0], [1]], nvFastPropState, emp,
    rfl, nvFastProp_lengths, nvFastProp_witness, rfl,
    by rw [sep_emp]; exact nvFastPropMem_ok, ?_⟩
  intro r _vals' _flags' _lvl' _rsns' _trl' _tp' _te' _prop' _unas' _unfl'
    _wvec' _arena' _wstk' _wlen' _wu' _fuel' _ctype' _cref' _c0' _c1' _oom'
    _ticks' _wsort' _phases' m' s' _hlen' hwf' _htr' _hperm' _hfl' hr _hr0 hr1 _hr2 _hnoop hm'
  refine ⟨hr, fun h1 => ?_, _, hm'⟩
  subst h1
  exact hwf'.level0_unsat_of_conflOkW rfl (m4ConflOkW_of_full (hr1 rfl).2.2)

end LeanQbe.T.Examples.Kissat.FullM4Bcp
