module

public import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof1
public import LeanQbe.T.Examples.Kissat.FullFastCoreLemmas

/-!
# Kissat M6 `S1.5` Delayed-Watch BCP Proofs, `ModuleOk`, & UNSAT NV (`FullM6BcpS15Proof`)

Proves:
1. `full_prop_lit_raw_s15_wp` against `fullPropLitS15Spec`, plus
   `full_prop_lit_raw_s15_wp_canon_dcap0` certifying against exact unchanged `Full.fullPropLitSpec`
   whenever `c.delayed_cap = 0`.
2. `full_propagate_ignore_s15_wp` (`fullPropagateIgnoreS15Spec`) and `full_bcp_s15_wp`
   (`fullBcpS15Spec`).
3. `full_bcp_s15_preserves_sparseInv` against exact canonical `FullPropDecSpecs.FullSparseInv`
   plus level-0 UNSAT soundness.
4. Closed `m6BcpS15_tableImpl`, unconditional `m6BcpS15_moduleOk : ModuleOk m6BcpS15Env
   m6BcpS15Module`, and concrete `Mem 64` UNSAT NV `nv_m6_bcp_s15_sound` (`XPost := False`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6BcpS15

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

local macro "s15_hsteps" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps))

local macro "s15_hsteps_nogrp" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps_nogrp))

local elab "s15_head_steps" : tactic => do
  Lean.Elab.Tactic.evalTactic
    (← `(tactic| try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)))
  fcHeadRun false

local elab "s15_head_split" : tactic => do
  Lean.Elab.Tactic.evalTactic
    (← `(tactic| try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)))
  fcHeadRun true

private def withDel (s : FullState) (del : List (BitVec 32)) : FullState :=
  { s with scratch := { s.scratch with delayed := del } }

private theorem propLit_eq_upd_del {s st : FullState}
    (hag : AgreesExcept propLitCoreMask s.core st.core)
    (hsc : st.scratch = { s.scratch with
      search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
      phases := st.scratch.phases, delayed := st.scratch.delayed }) :
    st =
      { core :=
          { s.core with
            vals := st.core.vals, flags := st.core.flags, lvl := st.core.lvl,
            rsns := st.core.rsns, trl := st.core.trl, trail_pos := st.core.trail_pos,
            trail_end := st.core.trail_end, unassigned := st.core.unassigned,
            unflushed := st.core.unflushed, wvec := st.core.wvec, arena := st.core.arena,
            wstk := st.core.wstk, wlen := st.core.wlen, wusable := st.core.wusable,
            confl_type := st.core.confl_type, confl_ref := st.core.confl_ref,
            confl_lit0 := st.core.confl_lit0, confl_lit1 := st.core.confl_lit1,
            oom := st.core.oom }
        scratch :=
          { s.scratch with
            search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
            phases := st.scratch.phases, delayed := st.scratch.delayed } } := by
  have h1 : st =
      { core :=
          { (withDel s st.scratch.delayed).core with
            vals := st.core.vals, flags := st.core.flags, lvl := st.core.lvl,
            rsns := st.core.rsns, trl := st.core.trl, trail_pos := st.core.trail_pos,
            trail_end := st.core.trail_end, unassigned := st.core.unassigned,
            unflushed := st.core.unflushed, wvec := st.core.wvec, arena := st.core.arena,
            wstk := st.core.wstk, wlen := st.core.wlen, wusable := st.core.wusable,
            confl_type := st.core.confl_type, confl_ref := st.core.confl_ref,
            confl_lit0 := st.core.confl_lit0, confl_lit1 := st.core.confl_lit1,
            oom := st.core.oom }
        scratch :=
          { (withDel s st.scratch.delayed).scratch with
            search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
            phases := st.scratch.phases } } :=
    propLit_eq_upd hag (by simpa only [withDel] using hsc)
  exact h1

private theorem bv64_add2_sub2 (p : BitVec 64) : p + 1#64 + 1#64 - 2#64 = p := by
  bv_omega

private def s15RawCompactFlushExpr (h_p pWvec pWstk pDel : Val i64) (not_lit : Val i32)
    (off_v p_v q_v end_v di_v : Val i64) (confl_v : Val .bool) : Expr Val Cont [.bool] :=
  .group (sig := [[i64, i64]])
    (fun L1 => .cons (fun q =>
      .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var q.1, (.var end_v, ()))) fun v1 =>
      .jnz (.var v1.1) (
        .let_ (Op.mk (.mul i64) (.var q.2.1, (.imm (4 : BitVec 64), ()))) fun v2 =>
        .let_ (Op.mk (.add i64) (.var pWstk, (.var v2.1, ()))) fun v3 =>
        .let_ (Op.mk (.mul i64) (.var q.1, (.imm (4 : BitVec 64), ()))) fun v4 =>
        .let_ (Op.mk (.add i64) (.var pWstk, (.var v4.1, ()))) fun v5 =>
        .load i32 (.var v5.1) fun v6 =>
        .store (.var v6) (.var v3.1) (
          .let_ (Op.mk (.add i64) (.var q.2.1, (.imm (1 : BitVec 64), ()))) fun v7 =>
          .let_ (Op.mk (.add i64) (.var q.1, (.imm (1 : BitVec 64), ()))) fun v8 =>
          .jump L1.1 (.var v8.1, (.var v7.1, ()))
        )
      ) (
        .group (sig := [[i64]])
          (fun L3 => .cons (fun k =>
            .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var k.1, (.var end_v, ()))) fun c3 =>
            .jnz (.var c3.1) (
              .let_ (Op.mk (.mul i64) (.var k.1, (.imm (4 : BitVec 64), ()))) fun o4 =>
              .let_ (Op.mk (.add i64) (.var pWstk, (.var o4.1, ()))) fun pk =>
              .store (t := i32) (.imm 0xFFFFFFFF#32) (.var pk.1) (
                .let_ (Op.mk (.add i64) (.var k.1, (.imm (1 : BitVec 64), ()))) fun k1 =>
                .jump L3.1 (.var k1.1, ())
              )
            ) (
              .let_ (Op.mk (.zext 32 64) (.var not_lit, ())) fun w1 =>
              .let_ (Op.mk (.sext 32 64) (.imm (1 : BitVec 32), ())) fun w2 =>
              .let_ (Op.mk (.shl i64) (.var w1.1, (.var w2.1, ()))) fun w3 =>
              .let_ (Op.mk (.add i64) (.var w3.1, (.imm (1 : BitVec 64), ()))) fun w4 =>
              .let_ (Op.mk (.mul i64) (.var w4.1, (.imm (4 : BitVec 64), ()))) fun w5 =>
              .let_ (Op.mk (.add i64) (.var pWvec, (.var w5.1, ()))) fun w6 =>
              .let_ (Op.mk (.sub i64) (.var q.2.1, (.var off_v, ()))) fun w7 =>
              .let_ (Op.mk (.trunc 64 32) (.var w7.1, ())) fun w8 =>
              .store (.var w8.1) (.var w6.1) (
                .let_ (Op.mk (.add i64) (.var h_p, (.imm (464 : BitVec 64), ()))) fun u1 =>
                .load i64 (.var u1.1) fun u2 =>
                .let_ (Op.mk (.sub i64) (.var end_v, (.var q.2.1, ()))) fun u3 =>
                .let_ (Op.mk (.add i64) (.var u2, (.var u3.1, ()))) fun u4 =>
                .let_ (Op.mk (.add i64) (.var h_p, (.imm (464 : BitVec 64), ()))) fun u5 =>
                .store (.var u4.1) (.var u5.1) (
                  .group (sig := [[.bool]])
                    (fun _ => .cons (fun cf =>
                      .let_ (Op.mk (.not .bool) (.var cf.1, ())) fun r0 =>
                      .ret (.var r0.1, ())
                    ) .nil)
                    (fun Jfl =>
                      .let_ (Op.mk (.cmp .ugt i64 .bool rfl)
                        (.var di_v, (.imm (0 : BitVec 64), ()))) fun cdi =>
                      .jnz (.var cdi.1) (
                        .group (sig := [[.bool, i64]])
                          (fun _ => .cons (fun b => .jump Jfl.1 (.var b.1, ())) .nil)
                          (fun Bfl =>
                            .group (sig := [[i64]])
                              (fun Lfl => .cons (fun j =>
                                .let_ (Op.mk (.cmp .ult i64 .bool rfl)
                                  (.var j.1, (.var di_v, ()))) fun cj =>
                                .jnz (.var cj.1) (
                                  .let_ (Op.mk (.mul i64) (.var j.1, (.imm (4 : BitVec 64), ())))
                                    fun a0 =>
                                  .let_ (Op.mk (.add i64) (.var pDel, (.var a0.1, ()))) fun a1 =>
                                  .load i32 (.var a1.1) fun rlit =>
                                  .let_ (Op.mk (.add i64) (.var j.1, (.imm (1 : BitVec 64), ())))
                                    fun a2 =>
                                  .let_ (Op.mk (.mul i64) (.var a2.1, (.imm (4 : BitVec 64), ())))
                                    fun a3 =>
                                  .let_ (Op.mk (.add i64) (.var pDel, (.var a3.1, ()))) fun a4 =>
                                  .load i32 (.var a4.1) fun rw0 =>
                                  .let_ (Op.mk (.add i64) (.var j.1, (.imm (2 : BitVec 64), ())))
                                    fun a5 =>
                                  .let_ (Op.mk (.mul i64) (.var a5.1, (.imm (4 : BitVec 64), ())))
                                    fun a6 =>
                                  .let_ (Op.mk (.add i64) (.var pDel, (.var a6.1, ()))) fun a7 =>
                                  .load i32 (.var a7.1) fun rcr =>
                                  .let_ (Op.mk (.add i64) (.var j.1, (.imm (3 : BitVec 64), ())))
                                    fun j1 =>
                                  .call (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
                                    "full_watch_push"
                                    (.var h_p, (.var rlit, (.var rw0, (.var rcr,
                                      (.imm (2 : BitVec 32), ()))))) fun pok =>
                                  .jnz (.var pok.1) (
                                    .jump Lfl.1 (.var j1.1, ())
                                  ) (
                                    .let_ (Op.mk (.add i64)
                                      (.var h_p, (.imm (760 : BitVec 64), ()))) fun o1 =>
                                    .store (t := i64) (.imm (1 : BitVec 64)) (.var o1.1) (
                                      .jump Bfl.1 (.imm true, (.var j1.1, ()))
                                    )
                                  )
                                ) (
                                  .jump Bfl.1 (.var confl_v, (.var j.1, ()))
                                )
                              ) .nil)
                              (fun Lfl => .jump Lfl.1 (.imm (0 : BitVec 64), ()))
                          )
                      ) (
                        .jump Jfl.1 (.var confl_v, ())
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

private theorem s15_raw_compact_flush_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sem sem_s : FullState} {not_lit : BitVec 32}
    {off0_v p_v q_v end0_v di_v ignore_ref : BitVec 64} {confl_v : Bool} {dlen : Nat}
    {R : Mem 64 → Prop} {m_sync : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hPush : ∀ args m Q X, fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    (hwc : c.wcap < 2 * dimacsBound) (hdelc : c.delayed_cap < dimacsBound)
    (hdense0 : s.core.dense_mode = 0#64) (hnot_s : not_lit.toNat < 2 * sem_s.core.cur_vars)
    (hpi_s : PropLitInv c F0 F_cur (withDel s sem_s.scratch.delayed) sem_s not_lit.toNat
      off0_v.toNat q_v.toNat p_v.toNat end0_v.toNat)
    (hcore_s : sem_s.core = sem.core)
    (hdi_eq : di_v.toNat = 3 * dlen) (hdlen_le : dlen ≤ c.delayed_cap)
    (hdel_ok_s : DelayedWatchesOk sem_s.core sem_s.scratch.delayed dlen not_lit.toNat)
    (hd0_s : c.delayed_cap = 0 → sem_s.scratch.delayed = s.scratch.delayed)
    (hcf_f : confl_v = false → sem.core.oom = 0#64 ∧ sem.core.confl_type = s.core.confl_type)
    (hcf_t : confl_v = true → PropLitConfl F_cur ignore_ref sem.core)
    (hm_sync : (FullMem c sem_s ⋆ R) m_sync)
    (hret_st : ∀ (ok : Bool) (st : FullState) (ml : Mem 64),
      st.LengthsOk c → FullWitnessInv c F0 F_cur st.core →
      AgreesExcept propLitCoreMask s.core st.core →
      FullPropDecSpecs.FullTrailExt s.core st.core →
      FullPropDecSpecs.FullArenaPermEq s.core st.core →
      st.scratch = { s.scratch with
        search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
        phases := st.scratch.phases, delayed := st.scratch.delayed } →
      (c.delayed_cap = 0 → st.scratch.delayed = s.scratch.delayed) →
      (ok = false → PropLitConfl F_cur ignore_ref st.core) →
      (ok = true → st.core.oom = 0#64 ∧ st.core.confl_type = s.core.confl_type) →
      (FullMem c st ⋆ R) ml → Q (ok, ()) ml) :
    wp Γ Q X (s15RawCompactFlushExpr c.hdr c.pWvec c.pWstk c.pDelayed not_lit off0_v p_v q_v
      end0_v di_v confl_v) m_sync := by
  unfold dimacsBound at hwc hdelc
  have ⟨hend_le, hwlen_le⟩ := hpi_s.end_lt_wcap hnot_s
  have hend_wcap : end0_v.toNat ≤ c.wcap := Nat.le_trans hend_le hwlen_le
  have hwc64 : c.wcap + 1 < 2 ^ 64 := Nat.lt_trans (Nat.add_lt_add_right hwc 1) (by decide)
  have hq_ge := hpi_s.sw.q_ge; have hq_le := hpi_s.sw.q_le_p; have hp_le := hpi_s.sw.p_le_end
  have hwstk_s := hpi_s.len.core_ok.wstk_len_arr
  have hwvec_s := hpi_s.len.core_ok.wvec_len
  have hcv_s := hpi_s.len.core_ok.cur_vars_le
  have hidx1_nat :
      ((not_lit.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * not_lit.toNat + 1 :=
    fc_bv64_shl1_add1_nat not_lit
  unfold s15RawCompactFlushExpr
  let q_fin : Nat := q_v.toNat + (end0_v.toNat - p_v.toNat)
  refine wp_loop_inv
    (fun (p_c, q_c, ()) m2 => ∃ wstk_c : List (BitVec 32),
      wstk_c.length = c.wcap ∧ p_v.toNat ≤ p_c.toNat ∧ p_c.toNat ≤ end0_v.toNat ∧
      q_c.toNat = q_v.toNat + (p_c.toNat - p_v.toNat) ∧
      (∀ k, off0_v.toNat ≤ k → k < q_v.toNat → wstk_c[k]? = sem_s.core.wstk[k]?) ∧
      (∀ k < p_c.toNat - p_v.toNat,
        wstk_c[q_v.toNat + k]? = sem_s.core.wstk[p_v.toNat + k]?) ∧
      (∀ k, p_c.toNat ≤ k → k < end0_v.toNat → wstk_c[k]? = sem_s.core.wstk[k]?) ∧
      (∀ k, (k < off0_v.toNat ∨ end0_v.toNat ≤ k) → wstk_c[k]? = sem_s.core.wstk[k]?) ∧
      (FullMem c { sem_s with core := { sem_s.core with wstk := wstk_c } } ⋆ R) m2)
    (fun (p_c, _, ()) _ => end0_v.toNat - p_c.toNat)
    (fun L2 hL2 => by
      s15_head_steps
      exact hL2 (p_v, q_v, ()) m_sync ⟨sem_s.core.wstk, hwstk_s, Nat.le_refl _, hp_le,
        by omega, fun _ _ _ => rfl, fun _ hk => by omega, fun _ _ _ => rfl,
        fun _ _ => rfl, hm_sync⟩)
    (fun L2 (p_c, q_c, ()) m2 ⟨wstk_c, hwl2, hp_ge, hp_le2, hqc_eq,
        hpre, hsuf, hrem, hout, hm2⟩ ih2 => ?_)
  s15_head_steps
  · have hp_lt : p_c.toNat < end0_v.toNat := hc
    have hstep := propLit_loop2_step hq_ge hq_le hp_ge hp_lt (by omega) (by omega)
      hpre hsuf hrem hout
    have hpc_add : (p_c + (1 : BitVec 64)).toNat = p_c.toNat + 1 := bv64_add1_toNat (by omega)
    have hqc_add : (q_c + (1 : BitVec 64)).toNat =
        q_v.toNat + ((p_c + (1 : BitVec 64)).toNat - p_v.toNat) := by
      rw [bv64_add1_toNat (by omega), hpc_add]; omega
    refine ih2 (p_c + (1 : BitVec 64), q_c + (1 : BitVec 64), ()) m (by dsimp only; omega)
      ⟨wstk_c.set q_c.toNat (wstk_c[p_c.toNat]'(by omega)), by simp [hwl2],
        by omega, by omega, hqc_add, ?_, ?_, ?_, ?_, hm⟩
    · simpa only [← hqc_eq] using hstep.1
    · rw [hpc_add]; simpa only [← hqc_eq] using hstep.2.1
    · rw [hpc_add]; simpa only [← hqc_eq] using hstep.2.2.1
    · simpa only [← hqc_eq] using hstep.2.2.2
  · have hp_eq : p_c.toNat = end0_v.toNat := by c0_bound
    have hqfin_eq : q_c.toNat = q_fin := by dsimp [q_fin]; omega
    refine wp_loop_inv
      (fun (k_c, ()) m3 => ∃ wstk_k : List (BitVec 32),
        wstk_k.length = c.wcap ∧ q_fin ≤ k_c.toNat ∧ k_c.toNat ≤ end0_v.toNat ∧
        (∀ i, (i < q_fin ∨ end0_v.toNat ≤ i) → wstk_k[i]? = wstk_c[i]?) ∧
        (FullMem c { sem_s with core := { sem_s.core with wstk := wstk_k } } ⋆ R) m3)
      (fun (k_c, ()) _ => end0_v.toNat - k_c.toNat)
      (fun L3 hL3 => by
        s15_head_steps
        exact hL3 (q_c, ()) m2 ⟨wstk_c, hwl2, by omega, by omega, fun _ _ => rfl, hm2⟩)
      (fun L3 (k_c, ()) m3 ⟨wstk_k, hwl3, hk_ge, hk_le, hkeep, hm3⟩ ih3 => ?_)
    s15_head_steps
    · have hk_lt : k_c.toNat < end0_v.toNat := hc
      have hk_add : (k_c + (1 : BitVec 64)).toNat = k_c.toNat + 1 := bv64_add1_toNat (by omega)
      refine ih3 (k_c + (1 : BitVec 64), ()) m (by dsimp only; omega)
        ⟨wstk_k.set k_c.toNat 0xFFFFFFFF#32, by simp [hwl3], by omega, by omega,
          propLit_loop3_step hk_ge hk_lt hkeep, hm⟩
    · have hk_eq : k_c.toNat = end0_v.toNat := by c0_bound
      s15_head_steps
      have hm_c : (FullMem c { sem_s with core := { sem_s.core with
          wstk := wstk_k
          wvec := sem_s.core.wvec.set (2 * not_lit.toNat + 1) ((q_c - off0_v).setWidth 32)
          wusable := sem_s.core.wusable + (end0_v - q_c) } } ⋆ R) m := by
        simpa only [hidx1_nat] using hm
      have ⟨hl_c, hw_c, hag_c, htr_c, hperm_c, hsc_c, hcf_c, hoom_c, hm_c'⟩ :=
        propLit_finish (ctype0 := s.core.confl_type) (confl_v := confl_v)
          (ignore_ref := ignore_ref) hpi_s hdense0 hnot_s hwl3 hqfin_eq rfl
          hpre (fun k hk => hsuf k (by omega)) hout hkeep
          (fun hf => hcore_s.symm ▸ hcf_f hf) (fun ht => hcore_s.symm ▸ hcf_t ht) hm_c
      let st_c : FullState :=
        { sem_s with core := { sem_s.core with
            wstk := wstk_k
            wvec := sem_s.core.wvec.set (2 * not_lit.toNat + 1)
              (BitVec.ofNat 32 (q_v.toNat + (end0_v.toNat - p_v.toNat) - off0_v.toNat))
            wusable := sem_s.core.wusable + (end0_v - q_c) } }
      have hsc_c' : st_c.scratch = { s.scratch with
          search_ticks := st_c.scratch.search_ticks, wsort := st_c.scratch.wsort,
          phases := st_c.scratch.phases, delayed := st_c.scratch.delayed } := by
        simpa only [st_c, withDel] using hsc_c
      have hdel_ok_c : DelayedWatchesOk st_c.core st_c.scratch.delayed dlen not_lit.toNat :=
        hdel_ok_s
      refine wp_join_group (ts := [.bool])
        (fun (confl_fin, ()) m_fin => ∃ st_f : FullState,
          st_f.LengthsOk c ∧ FullWitnessInv c F0 F_cur st_f.core ∧
          AgreesExcept propLitCoreMask s.core st_f.core ∧
          FullPropDecSpecs.FullTrailExt s.core st_f.core ∧
          FullPropDecSpecs.FullArenaPermEq s.core st_f.core ∧
          st_f.scratch = { s.scratch with
            search_ticks := st_f.scratch.search_ticks, wsort := st_f.scratch.wsort,
            phases := st_f.scratch.phases, delayed := st_f.scratch.delayed } ∧
          (c.delayed_cap = 0 → st_f.scratch.delayed = s.scratch.delayed) ∧
          ((!confl_fin) = false → PropLitConfl F_cur ignore_ref st_f.core) ∧
          ((!confl_fin) = true → st_f.core.oom = 0#64 ∧
            st_f.core.confl_type = s.core.confl_type) ∧
          (FullMem c st_f ⋆ R) m_fin) ?_ ?_
      · rintro _ ⟨confl_fin, ⟨⟩⟩ m_fin
          ⟨st_f, hlf, hwf, hagf, htrf, hpermf, hscf, hd0f, hcff, hokf, hmf⟩
        s15_head_steps
        exact hret_st (!confl_fin) st_f m_fin hlf hwf hagf htrf hpermf hscf hd0f hcff hokf hmf
      · intro Jfl hJfl
        s15_head_split
        · -- `di > 0`: flush `del[0 ..< di)` via `full_watch_push`
          s15_head_steps
          refine wp_loop_break_group (brkTs := [.bool, i64]) (lpTs := [i64])
            (fun (confl_b, _, ()) m_b => ∃ st_b : FullState,
              st_b.LengthsOk c ∧ FullWitnessInv c F0 F_cur st_b.core ∧
              AgreesExcept propLitCoreMask s.core st_b.core ∧
              FullPropDecSpecs.FullTrailExt s.core st_b.core ∧
              FullPropDecSpecs.FullArenaPermEq s.core st_b.core ∧
              st_b.scratch = { s.scratch with
                search_ticks := st_b.scratch.search_ticks, wsort := st_b.scratch.wsort,
                phases := st_b.scratch.phases, delayed := st_b.scratch.delayed } ∧
              (c.delayed_cap = 0 → st_b.scratch.delayed = s.scratch.delayed) ∧
              ((!confl_b) = false → PropLitConfl F_cur ignore_ref st_b.core) ∧
              ((!confl_b) = true → st_b.core.oom = 0#64 ∧
                st_b.core.confl_type = s.core.confl_type) ∧
              (FullMem c st_b ⋆ R) m_b)
            (fun rem (j_v, ()) m_j => ∃ (st_j : FullState) (idx : Nat),
              rem = dlen - idx ∧ j_v.toNat = 3 * idx ∧ idx ≤ dlen ∧
              st_j.LengthsOk c ∧ FullWitnessInv c F0 F_cur st_j.core ∧
              AgreesExcept propLitCoreMask s.core st_j.core ∧
              FullPropDecSpecs.FullTrailExt s.core st_j.core ∧
              FullPropDecSpecs.FullArenaPermEq s.core st_j.core ∧
              st_j.scratch = { s.scratch with
                search_ticks := st_j.scratch.search_ticks, wsort := st_j.scratch.wsort,
                phases := st_j.scratch.phases, delayed := st_j.scratch.delayed } ∧
              st_j.scratch.delayed = st_c.scratch.delayed ∧
              DelayedWatchesOk st_j.core st_j.scratch.delayed dlen not_lit.toNat ∧
              (c.delayed_cap = 0 → st_j.scratch.delayed = s.scratch.delayed) ∧
              ((!confl_v) = false → PropLitConfl F_cur ignore_ref st_j.core) ∧
              ((!confl_v) = true → st_j.core.oom = 0#64 ∧
                st_j.core.confl_type = s.core.confl_type) ∧
              (FullMem c st_j ⋆ R) m_j) ?_ ?_ ?_
          · rintro _ ⟨confl_b, _, ⟨⟩⟩ m_b hb
            s15_head_steps
            exact hJfl (confl_b, ()) m_b hb
          · rintro Bfl Lfl rem ⟨j_v, ⟨⟩⟩ m_j hBfl ihfl
              ⟨st_j, idx, rfl, hj_eq, hidx_le, hlj, hwj, hagj, htrj, hpermj, hscj,
                hdel_eq_j, hdel_ok_j, hd0j, hcfj, hokj, hmj⟩
            have hdel_len_j := hlj.scratch_ok.delayed_len_arr
            have hdm_j : st_j.core.dense_mode = 0#64 :=
              (hagj.get FullCoreState.dense_mode).trans hdense0
            have hwat_j : WatchesInv F_cur st_j.core := by
              have h := hwj.watches; unfold ModeWatchesInv at h; simpa [hdm_j] using h
            have hnw_j : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st_j.core) :=
              fullWitnessInv_to_nw hlj.core_ok.cur_vars_le hwj
            s15_hsteps
            · have hlt_j : j_v.toNat < di_v.toNat := hc
              have hidx_lt : idx < dlen := by omega
              have h3i_lt : 3 * idx + 2 < st_j.scratch.delayed.length := by omega
              have hj1_nat : (j_v + 1#64).toNat = 3 * idx + 1 := by
                rw [BitVec.toNat_add, hj_eq]
                change (3 * idx + 1) % 2 ^ 64 = 3 * idx + 1
                exact Nat.mod_eq_of_lt (by omega)
              have hj2_nat : (j_v + 2#64).toNat = 3 * idx + 2 := by
                rw [BitVec.toNat_add, hj_eq]
                change (3 * idx + 2) % 2 ^ 64 = 3 * idx + 2
                exact Nat.mod_eq_of_lt (by omega)
              have hj3_nat : (j_v + 3#64).toNat = 3 * (idx + 1) := by
                rw [BitVec.toNat_add, hj_eq]
                change (3 * idx + 3) % 2 ^ 64 = 3 * (idx + 1)
                rw [Nat.mod_eq_of_lt (by omega)]; omega
              obtain ⟨hrlit_lt, hrlit_ne, hrw0_f, hrcr_lt, hrcr_ref⟩ := hdel_ok_j idx hidx_lt
              have hrlit_get : st_j.scratch.delayed[j_v.toNat]'(by omega) =
                  st_j.scratch.delayed[3 * idx]?.getD 0#32 := by
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; simp only [hj_eq]
              have hrw0_get : st_j.scratch.delayed[(j_v + 1#64).toNat]'(
                  by rw [hj1_nat]; omega) =
                  st_j.scratch.delayed[3 * idx + 1]?.getD 0#32 := by
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; simp only [hj1_nat]
              have hrcr_get : st_j.scratch.delayed[(j_v + 2#64).toNat]'(
                  by rw [hj2_nat]; omega) =
                  st_j.scratch.delayed[3 * idx + 2]?.getD 0#32 := by
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; simp only [hj2_nat]
              let rlit_v := st_j.scratch.delayed[j_v.toNat]'(by omega)
              let rw0_v := st_j.scratch.delayed[(j_v + 1#64).toNat]'(by rw [hj1_nat]; omega)
              let rcr_v := st_j.scratch.delayed[(j_v + 2#64).toNat]'(by rw [hj2_nat]; omega)
              have hrlit_lt_j : rlit_v.toNat < 2 * st_j.core.cur_vars := by
                dsimp only [rlit_v]; rw [hrlit_get]; exact hrlit_lt
              have hrw0_f_j : (rw0_v &&& 0x80000000#32) = 0#32 := by
                dsimp only [rw0_v]; rw [hrw0_get]; exact hrw0_f
              have hrcr_lt_j : rcr_v.toNat < 0x80000000 := by
                dsimp only [rcr_v]; rw [hrcr_get]; exact hrcr_lt
              have hrcr_ref_j : rcr_v.toNat ∈ fullArenaClauseRefsCore st_j.core := by
                dsimp only [rcr_v]; rw [hrcr_get]; exact hrcr_ref
              have hrw0_ne : rw0_v ≠ 0xFFFFFFFF#32 := fun heq => by
                rw [heq] at hrw0_f_j; exact absurd hrw0_f_j (by decide)
              have hrcr_ne : rcr_v ≠ 0xFFFFFFFF#32 := fun heq => by
                rw [heq] at hrcr_lt_j; revert hrcr_lt_j; decide
              c0_call hPush
              refine ⟨c, st_j, R, rfl, hlj, hwat_j.layout, fun h => absurd h (by decide),
                fun _ => ⟨hrw0_ne, hrcr_ne⟩, hmj,
                fun pok wvec' wstk' wlen' wu' wsort' mp hlen_p hlay_p hpres_o hpok_t
                  hpok_f hmp => ?_⟩
              let st_p : FullState :=
                { st_j with
                  core := { st_j.core with
                    wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
                  scratch := { st_j.scratch with wsort := wsort' } }
              have hag_p : AgreesExcept propLitCoreMask s.core st_p.core :=
                hagj.update (fun k => { k with
                  wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' })
              have hsc_p : st_p.scratch = { s.scratch with
                  search_ticks := st_p.scratch.search_ticks, wsort := st_p.scratch.wsort,
                  phases := st_p.scratch.phases, delayed := st_p.scratch.delayed } := by
                dsimp only [st_p]; rw [hscj]
              unfold fullWatchSize fullWatchOff at hpres_o hpok_t hpok_f
              s15_head_split
              · have hpok_eq : pok = true := hc
                have ⟨_, _, hsz_p, hpre_p, hw0_p, hw1_p⟩ := hpok_t hpok_eq
                have hwat_p := (s15_flush_step_preserves (k := st_j.core) (k' := st_p.core)
                  (lit := rlit_v) (w0 := rw0_v) (cref := rcr_v) (skip_lit := not_lit.toNat)
                  rfl rfl hlay_p hrlit_lt_j hrw0_f_j hrcr_lt_j hrcr_ref_j hpres_o
                  ⟨hsz_p, hpre_p, hw0_p, hw1_p rfl⟩).1 hwat_j
                have hw_p : FullWitnessInv c F0 F_cur st_p.core :=
                  fullWitnessInv_of_nw
                    (fullWitnessInv_nw_congr hlen_p.core_ok.cur_vars_le hnw_j
                      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
                    hdm_j hwat_p
                exact ihfl (dlen - (idx + 1)) (j_v + 3#64, ()) mp (by omega)
                  ⟨st_p, idx + 1, rfl, hj3_nat, by omega, hlen_p, hw_p, hag_p,
                    htrj.congr rfl rfl rfl, hpermj, hsc_p, hdel_eq_j, hdel_ok_j, hd0j,
                    hcfj, hokj, hmp⟩
              · have hpok_eq : pok = false := hc
                s15_head_steps
                let st_o : FullState :=
                  { st_p with core := { st_p.core with oom := 1#64 } }
                have hlay_o : WatchStackLayout st_o.core :=
                  hlay_p.with_wstk rfl rfl rfl rfl
                have hwat_o := (s15_flush_step_false_preserves (k := st_j.core)
                  (k' := st_o.core) (lit := rlit_v) (skip_lit := not_lit.toNat)
                  rfl rfl hlay_o hpres_o (hpok_f hpok_eq).1).1 hwat_j
                have hw_o : FullWitnessInv c F0 F_cur st_o.core :=
                  fullWitnessInv_of_nw
                    (fullWitnessInv_nw_congr hlen_p.core_ok.cur_vars_le hnw_j
                      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
                    hdm_j hwat_o
                exact hBfl (true, _, ()) m ⟨st_o,
                  ⟨{ hlen_p.core_ok with vals_len := hlen_p.core_ok.vals_len },
                   hlen_p.scratch_ok⟩,
                  hw_o, hag_p.update (fun k => { k with oom := 1#64 }),
                  htrj.congr rfl rfl rfl, hpermj, hsc_p, hd0j,
                  fun _ => Or.inl (by show (1#64 : BitVec 64) ≠ 0#64; decide),
                  by simp, hm⟩
            · exact hBfl (confl_v, _, ()) m_j
                ⟨st_j, hlj, hwj, hagj, htrj, hpermj, hscj, hd0j, hcfj, hokj, hmj⟩
          · intro Bfl Lfl _ hLfl; s15_head_steps
            exact hLfl dlen (0#64, ()) m ⟨st_c, 0, by omega, by decide, Nat.zero_le _,
              hl_c, hw_c, hag_c, htr_c, hperm_c, hsc_c', rfl, hdel_ok_c, hd0_s, hcf_c,
              hoom_c, hm_c'⟩
        · -- `di == 0`: skip flush loop
          exact hJfl (confl_v, ()) m
            ⟨st_c, hl_c, hw_c, hag_c, htr_c, hperm_c, hsc_c', hd0_s, hcf_c, hoom_c, hm_c'⟩

private theorem s15_repl_idx_bounds {c : FullCfg} {k : FullCoreState} {repl_f : BitVec 32}
    {di_v : BitVec 64} {dlen : Nat}
    (hwc : c.wcap < 2 * dimacsBound) (hdelc : c.delayed_cap < dimacsBound)
    (hlen : k.LengthsOk c) (hlay : WatchStackLayout k)
    (hrepl_lt : repl_f.toNat < 2 * k.cur_vars)
    (hdi_eq : di_v.toNat = 3 * dlen) (hdlen_le : dlen ≤ c.delayed_cap) :
    ∃ (hlt0 : (repl_f.setWidth 64 <<< (1 : Nat)).toNat < k.wvec.length)
      (hlt1 : ((repl_f.setWidth 64 <<< (1 : Nat)) + 1#64).toNat < k.wvec.length),
      let roff_v := (k.wvec[(repl_f.setWidth 64 <<< (1 : Nat)).toNat]'hlt0).setWidth 64
      let rsz_v := (k.wvec[((repl_f.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'hlt1).setWidth 64
      let rwend_v := roff_v + rsz_v
      roff_v.toNat = fullWatchOffCore k repl_f.toNat ∧
      rsz_v.toNat = fullWatchSizeCore k repl_f.toNat ∧
      rwend_v.toNat = fullWatchOffCore k repl_f.toNat + fullWatchSizeCore k repl_f.toNat ∧
      (rwend_v + 1#64).toNat = rwend_v.toNat + 1 ∧
      (rwend_v + 2#64).toNat = rwend_v.toNat + 2 ∧
      (rsz_v + 2#64).setWidth 32 = BitVec.ofNat 32 (fullWatchSizeCore k repl_f.toNat + 2) ∧
      (BitVec.ofNat 64 k.wlen).toNat = k.wlen ∧
      (di_v + 1#64).toNat = 3 * dlen + 1 ∧
      (di_v + 2#64).toNat = 3 * dlen + 2 ∧
      (di_v + 3#64).toNat = 3 * (dlen + 1) := by
  unfold dimacsBound at hwc hdelc
  have hcv := hlen.cur_vars_le; have hwv := hlen.wvec_len; have hwlen := hlen.wlen_le
  have hr0 := fc_bv64_shl1_u32_nat repl_f
  have hr1 := fc_bv64_shl1_add1_nat repl_f
  have hlt0 : (repl_f.setWidth 64 <<< (1 : Nat)).toNat < k.wvec.length := by omega
  have hlt1 : ((repl_f.setWidth 64 <<< (1 : Nat)) + 1#64).toNat < k.wvec.length := by
    rw [show (1#64 : BitVec 64) = (1 : BitVec 64) from rfl, hr1, hwv]; omega
  refine ⟨hlt0, hlt1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold fullWatchOffCore; rw [bv_c0_zext32_64]
    exact congrArg BitVec.toNat (fc_getElem_eq_getD_of_idx hr0 _)
  · unfold fullWatchSizeCore; rw [bv_c0_zext32_64]
    exact congrArg BitVec.toNat (fc_getElem_eq_getD_of_idx hr1 _)
  · have hroff : ((k.wvec[(repl_f.setWidth 64 <<< (1 : Nat)).toNat]'hlt0).setWidth 64).toNat =
        fullWatchOffCore k repl_f.toNat := by
      unfold fullWatchOffCore; rw [bv_c0_zext32_64]
      exact congrArg BitVec.toNat (fc_getElem_eq_getD_of_idx hr0 _)
    have hrsz : ((k.wvec[((repl_f.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'hlt1).setWidth 64
        ).toNat = fullWatchSizeCore k repl_f.toNat := by
      unfold fullWatchSizeCore; rw [bv_c0_zext32_64]
      exact congrArg BitVec.toNat (fc_getElem_eq_getD_of_idx hr1 _)
    have hbd := hlay.bounds repl_f.toNat hrepl_lt
    rw [bv64_add_toNat (by omega), hroff, hrsz]
  · have hroff : ((k.wvec[(repl_f.setWidth 64 <<< (1 : Nat)).toNat]'hlt0).setWidth 64).toNat =
        fullWatchOffCore k repl_f.toNat := by
      unfold fullWatchOffCore; rw [bv_c0_zext32_64]
      exact congrArg BitVec.toNat (fc_getElem_eq_getD_of_idx hr0 _)
    have hrsz : ((k.wvec[((repl_f.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'hlt1).setWidth 64
        ).toNat = fullWatchSizeCore k repl_f.toNat := by
      unfold fullWatchSizeCore; rw [bv_c0_zext32_64]
      exact congrArg BitVec.toNat (fc_getElem_eq_getD_of_idx hr1 _)
    have hbd := hlay.bounds repl_f.toNat hrepl_lt
    exact bv64_add1_toNat (by rw [bv64_add_toNat (by omega), hroff, hrsz]; omega)
  · have hroff : ((k.wvec[(repl_f.setWidth 64 <<< (1 : Nat)).toNat]'hlt0).setWidth 64).toNat =
        fullWatchOffCore k repl_f.toNat := by
      unfold fullWatchOffCore; rw [bv_c0_zext32_64]
      exact congrArg BitVec.toNat (fc_getElem_eq_getD_of_idx hr0 _)
    have hrsz : ((k.wvec[((repl_f.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'hlt1).setWidth 64
        ).toNat = fullWatchSizeCore k repl_f.toNat := by
      unfold fullWatchSizeCore; rw [bv_c0_zext32_64]
      exact congrArg BitVec.toNat (fc_getElem_eq_getD_of_idx hr1 _)
    have hbd := hlay.bounds repl_f.toNat hrepl_lt
    exact bv64_add2_toNat (by rw [bv64_add_toNat (by omega), hroff, hrsz]; omega)
  · have hrsz : ((k.wvec[((repl_f.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'hlt1).setWidth 64
        ).toNat = fullWatchSizeCore k repl_f.toNat := by
      unfold fullWatchSizeCore; rw [bv_c0_zext32_64]
      exact congrArg BitVec.toNat (fc_getElem_eq_getD_of_idx hr1 _)
    have hbd := hlay.bounds repl_f.toNat hrepl_lt
    apply BitVec.eq_of_toNat_eq
    have hadd : ((k.wvec[((repl_f.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'hlt1).setWidth 64 +
        2#64).toNat = fullWatchSizeCore k repl_f.toNat + 2 := by
      rw [show (2#64 : BitVec 64) = (2 : BitVec 64) from rfl,
        bv64_add2_toNat (by rw [hrsz]; omega), hrsz]
    rw [BitVec.toNat_setWidth, hadd, BitVec.toNat_ofNat]
  · exact Nat.mod_eq_of_lt (by omega)
  · rw [BitVec.toNat_add, hdi_eq]
    change (3 * dlen + 1) % 2 ^ 64 = 3 * dlen + 1; exact Nat.mod_eq_of_lt (by omega)
  · rw [BitVec.toNat_add, hdi_eq]
    change (3 * dlen + 2) % 2 ^ 64 = 3 * dlen + 2; exact Nat.mod_eq_of_lt (by omega)
  · rw [BitVec.toNat_add, hdi_eq]
    change (3 * dlen + 3) % 2 ^ 64 = 3 * (dlen + 1); rw [Nat.mod_eq_of_lt (by omega)]; omega

private theorem s15_repl_sentinel_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sem sem1 st3 : FullState} {not_lit other repl_f cref : BitVec 32}
    {off0_v p_v q_v end0_v rwend_v wu' : BitVec 64}
    (hpi1 : PropLitInv c F0 F_cur (withDel s sem.scratch.delayed) sem1 not_lit.toNat
      off0_v.toNat q_v.toNat (p_v.toNat + 2) end0_v.toNat)
    (_hdel1_eq : sem1.scratch.delayed = sem.scratch.delayed)
    (hst3_core_eq : st3.core = { sem1.core with arena := st3.core.arena })
    (hst3_sc_eq : st3.scratch = sem1.scratch)
    (hlen3 : st3.LengthsOk c)
    (hnw3 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st3.core))
    (hsw3 : SplitWatchesInv F_cur st3.core not_lit.toNat off0_v.toNat q_v.toNat
      (p_v.toNat + 2) end0_v.toNat)
    (hperm13 : FullPropDecSpecs.FullArenaPermEq sem1.core st3.core)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref3 : cref.toNat ∈ fullArenaClauseRefsCore st3.core)
    (hrepl_lt3 : repl_f.toNat < 2 * st3.core.cur_vars)
    (hrepl_ne_not : repl_f.toNat ≠ not_lit.toNat)
    (hnot_st3 : not_lit.toNat < 2 * st3.core.cur_vars)
    (hroff_pos : 0 < fullWatchOffCore st3.core repl_f.toNat)
    (hrwend2_le : fullWatchOffCore st3.core repl_f.toNat +
      fullWatchSizeCore st3.core repl_f.toNat + 2 ≤ st3.core.wlen)
    (hsent0 : st3.core.wstk[fullWatchOffCore st3.core repl_f.toNat +
      fullWatchSizeCore st3.core repl_f.toNat]? = some 0xFFFFFFFF#32)
    (hsent1 : st3.core.wstk[fullWatchOffCore st3.core repl_f.toNat +
      fullWatchSizeCore st3.core repl_f.toNat + 1]? = some 0xFFFFFFFF#32)
    (hrwend_nat : rwend_v.toNat =
      fullWatchOffCore st3.core repl_f.toNat + fullWatchSizeCore st3.core repl_f.toNat)
    (hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2) :
    let st4 : FullState :=
      { st3 with core := { st3.core with
          wstk := (st3.core.wstk.set rwend_v.toNat
            (other &&& 0x7FFFFFFF#32)).set (rwend_v.toNat + 1) cref
          wvec := st3.core.wvec.set (2 * repl_f.toNat + 1)
            (BitVec.ofNat 32 (fullWatchSizeCore st3.core repl_f.toNat + 2))
          wusable := wu' } }
    PropLitInv c F0 F_cur (withDel s st4.scratch.delayed) st4 not_lit.toNat off0_v.toNat
      q_v.toNat (p_v + 1#64 + 1#64).toNat end0_v.toNat := by
  intro st4
  have hq_ge := hsw3.q_ge; have hq_le := hsw3.q_le_p; have hp_le := hsw3.p_le_end
  have hwo_st3 : fullWatchOffCore st3.core not_lit.toNat = off0_v.toNat := hsw3.off_eq
  have ⟨hlen4c, hlay4, hwo4, hpres4, hsz4, hpre4, hw0_4, hw1_4⟩ :=
    s15_append_sentinel_layout (wu' := wu') hsw3.layout hlen3.core_ok
      hrepl_lt3 hroff_pos hrwend2_le hsent0 hsent1 (bv32_mask7f_flag0 other) hcr_lt
  have hsw4_raw := (s15_flush_step_preserves (k := st3.core) (k' := st4.core)
    (lit := repl_f) (w0 := other &&& 0x7FFFFFFF#32) (cref := cref) (skip_lit := not_lit.toNat)
    rfl rfl (by simpa [st4, hrwend_nat] using hlay4) hrepl_lt3 (bv32_mask7f_flag0 other)
    hcr_lt hcr_ref3 (by simpa [st4, hrwend_nat] using hpres4)
    ⟨by simpa [st4, hrwend_nat] using hsz4, by simpa [st4, hrwend_nat] using hpre4,
     by simpa [st4, hrwend_nat] using hw0_4, by simpa [st4, hrwend_nat] using hw1_4⟩).2
    hrepl_ne_not hnot_st3 _ _ _ _ hsw3
  have hoff4_eq : fullWatchOffCore st4.core not_lit.toNat = off0_v.toNat := by
    have h := hwo4 not_lit.toNat; simpa only [st4, hrwend_nat, hwo_st3] using h
  have hsw4 : SplitWatchesInv F_cur st4.core not_lit.toNat off0_v.toNat q_v.toNat
      (p_v.toNat + 2) end0_v.toNat := by
    dsimp only at hsw4_raw
    rw [hoff4_eq,
      show off0_v.toNat + (q_v.toNat - off0_v.toNat) = q_v.toNat by omega,
      show off0_v.toNat + (p_v.toNat + 2 - off0_v.toNat) = p_v.toNat + 2 by omega,
      show off0_v.toNat + (end0_v.toNat - off0_v.toNat) = end0_v.toNat by omega] at hsw4_raw
    exact hsw4_raw
  have hlen4 : st4.LengthsOk c :=
    ⟨by simpa [st4, hrwend_nat] using hlen4c, hlen3.scratch_ok⟩
  have hnw4 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st4.core) :=
    fullWitnessInv_nw_congr hlen4.core_ok.cur_vars_le hnw3
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hag4 : AgreesExcept propLitCoreMask (withDel s st4.scratch.delayed).core st4.core := by
    have hag1 := hpi1.ag.update (fun k => { k with
      arena := st3.core.arena, wstk := st4.core.wstk, wvec := st4.core.wvec, wusable := wu' })
    have hcore4 : st4.core = { sem1.core with
        arena := st3.core.arena, wstk := st4.core.wstk, wvec := st4.core.wvec, wusable := wu' } :=
      by dsimp only [st4]; rw [hst3_core_eq]
    rw [hcore4]; exact hag1
  exact
    { len := hlen4, nw := hnw4, sw := hp2_nat.symm ▸ hsw4
      ag := hag4
      tr := hpi1.tr.congr (by dsimp only [st4]; rw [hst3_core_eq])
        (by dsimp only [st4]; rw [hst3_core_eq]) (by dsimp only [st4]; rw [hst3_core_eq])
      perm := hpi1.perm.trans hperm13
      sc_eq := by
        have hs1 := hpi1.sc_eq; dsimp only [withDel] at hs1 ⊢
        dsimp only [st4]; rw [hst3_sc_eq, hs1]
      not_f := by dsimp only [st4]; rw [hst3_core_eq]; exact hpi1.not_f }

private theorem s15_repl_end_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sem sem1 st3 : FullState} {not_lit other repl_f cref : BitVec 32}
    {off0_v p_v q_v end0_v rwend_v : BitVec 64}
    (hpi1 : PropLitInv c F0 F_cur (withDel s sem.scratch.delayed) sem1 not_lit.toNat
      off0_v.toNat q_v.toNat (p_v.toNat + 2) end0_v.toNat)
    (_hdel1_eq : sem1.scratch.delayed = sem.scratch.delayed)
    (hst3_core_eq : st3.core = { sem1.core with arena := st3.core.arena })
    (hst3_sc_eq : st3.scratch = sem1.scratch)
    (hlen3 : st3.LengthsOk c)
    (hnw3 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st3.core))
    (hsw3 : SplitWatchesInv F_cur st3.core not_lit.toNat off0_v.toNat q_v.toNat
      (p_v.toNat + 2) end0_v.toNat)
    (hperm13 : FullPropDecSpecs.FullArenaPermEq sem1.core st3.core)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref3 : cref.toNat ∈ fullArenaClauseRefsCore st3.core)
    (hrepl_lt3 : repl_f.toNat < 2 * st3.core.cur_vars)
    (hrepl_ne_not : repl_f.toNat ≠ not_lit.toNat)
    (hnot_st3 : not_lit.toNat < 2 * st3.core.cur_vars)
    (hroff_pos : 0 < fullWatchOffCore st3.core repl_f.toNat)
    (hend_wlen : fullWatchOffCore st3.core repl_f.toNat +
      fullWatchSizeCore st3.core repl_f.toNat = st3.core.wlen)
    (hfit2 : st3.core.wlen + 2 ≤ c.wcap)
    (hrwend_nat : rwend_v.toNat =
      fullWatchOffCore st3.core repl_f.toNat + fullWatchSizeCore st3.core repl_f.toNat)
    (hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2) :
    let st4 : FullState :=
      { st3 with core := { st3.core with
          wstk := (st3.core.wstk.set rwend_v.toNat
            (other &&& 0x7FFFFFFF#32)).set (rwend_v.toNat + 1) cref
          wvec := st3.core.wvec.set (2 * repl_f.toNat + 1)
            (BitVec.ofNat 32 (fullWatchSizeCore st3.core repl_f.toNat + 2))
          wlen := rwend_v.toNat + 2 } }
    PropLitInv c F0 F_cur (withDel s st4.scratch.delayed) st4 not_lit.toNat off0_v.toNat
      q_v.toNat (p_v + 1#64 + 1#64).toNat end0_v.toNat := by
  intro st4
  have hq_ge := hsw3.q_ge; have hq_le := hsw3.q_le_p; have hp_le := hsw3.p_le_end
  have hwo_st3 : fullWatchOffCore st3.core not_lit.toNat = off0_v.toNat := hsw3.off_eq
  have ⟨hlen4c, hlay4, hwo4, hpres4, hsz4, hpre4, hw0_4, hw1_4⟩ :=
    s15_append_end_layout hsw3.layout hlen3.core_ok hrepl_lt3 hroff_pos hend_wlen hfit2
      (bv32_mask7f_flag0 other) hcr_lt
  have hsw4_raw := (s15_flush_step_preserves (k := st3.core) (k' := st4.core)
    (lit := repl_f) (w0 := other &&& 0x7FFFFFFF#32) (cref := cref) (skip_lit := not_lit.toNat)
    rfl rfl (by simpa [st4, hrwend_nat, hend_wlen] using hlay4) hrepl_lt3
    (bv32_mask7f_flag0 other) hcr_lt hcr_ref3
    (by simpa [st4, hrwend_nat, hend_wlen] using hpres4)
    ⟨by simpa [st4, hrwend_nat, hend_wlen] using hsz4,
     by simpa [st4, hrwend_nat, hend_wlen] using hpre4,
     by simpa [st4, hrwend_nat, hend_wlen] using hw0_4,
     by simpa [st4, hrwend_nat, hend_wlen] using hw1_4⟩).2
    hrepl_ne_not hnot_st3 _ _ _ _ hsw3
  have hoff4_eq : fullWatchOffCore st4.core not_lit.toNat = off0_v.toNat := by
    have h := hwo4 not_lit.toNat; simpa only [st4, hrwend_nat, hend_wlen, hwo_st3] using h
  have hsw4 : SplitWatchesInv F_cur st4.core not_lit.toNat off0_v.toNat q_v.toNat
      (p_v.toNat + 2) end0_v.toNat := by
    dsimp only at hsw4_raw
    rw [hoff4_eq,
      show off0_v.toNat + (q_v.toNat - off0_v.toNat) = q_v.toNat by omega,
      show off0_v.toNat + (p_v.toNat + 2 - off0_v.toNat) = p_v.toNat + 2 by omega,
      show off0_v.toNat + (end0_v.toNat - off0_v.toNat) = end0_v.toNat by omega] at hsw4_raw
    exact hsw4_raw
  have hlen4 : st4.LengthsOk c :=
    ⟨by simpa [st4, hrwend_nat, hend_wlen] using hlen4c, hlen3.scratch_ok⟩
  have hnw4 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st4.core) :=
    fullWitnessInv_nw_congr hlen4.core_ok.cur_vars_le hnw3
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hag4 : AgreesExcept propLitCoreMask (withDel s st4.scratch.delayed).core st4.core := by
    have hag1 := hpi1.ag.update (fun k => { k with
      arena := st3.core.arena, wstk := st4.core.wstk, wvec := st4.core.wvec,
      wlen := st4.core.wlen })
    have hcore4 : st4.core = { sem1.core with
        arena := st3.core.arena, wstk := st4.core.wstk, wvec := st4.core.wvec,
        wlen := st4.core.wlen } := by dsimp only [st4]; rw [hst3_core_eq]
    rw [hcore4]; exact hag1
  exact
    { len := hlen4, nw := hnw4, sw := hp2_nat.symm ▸ hsw4
      ag := hag4
      tr := hpi1.tr.congr (by dsimp only [st4]; rw [hst3_core_eq])
        (by dsimp only [st4]; rw [hst3_core_eq]) (by dsimp only [st4]; rw [hst3_core_eq])
      perm := hpi1.perm.trans hperm13
      sc_eq := by
        have hs1 := hpi1.sc_eq; dsimp only [withDel] at hs1 ⊢
        dsimp only [st4]; rw [hst3_sc_eq, hs1]
      not_f := by dsimp only [st4]; rw [hst3_core_eq]; exact hpi1.not_f }

private theorem s15_repl_delay_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sem sem1 st3 : FullState} {not_lit other repl_f cref : BitVec 32}
    {off0_v p_v q_v end0_v : BitVec 64} {dlen : Nat}
    (hpi1 : PropLitInv c F0 F_cur (withDel s sem.scratch.delayed) sem1 not_lit.toNat
      off0_v.toNat q_v.toNat (p_v.toNat + 2) end0_v.toNat)
    (hst3_core_eq : st3.core = { sem1.core with arena := st3.core.arena })
    (hst3_sc_eq : st3.scratch = sem1.scratch)
    (hlen3 : st3.LengthsOk c)
    (hnw3 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st3.core))
    (hsw3 : SplitWatchesInv F_cur st3.core not_lit.toNat off0_v.toNat q_v.toNat
      (p_v.toNat + 2) end0_v.toNat)
    (hperm13 : FullPropDecSpecs.FullArenaPermEq sem1.core st3.core)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref3 : cref.toNat ∈ fullArenaClauseRefsCore st3.core)
    (hrepl_lt3 : repl_f.toNat < 2 * st3.core.cur_vars)
    (hrepl_ne_not : repl_f.toNat ≠ not_lit.toNat)
    (hdel3_ok : DelayedWatchesOk st3.core st3.scratch.delayed dlen not_lit.toNat)
    (hdlen_lt : dlen < c.delayed_cap)
    (hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2) :
    let del' : List (BitVec 32) :=
      ((st3.scratch.delayed.set (3 * dlen) repl_f).set
        (3 * dlen + 1) (other &&& 0x7FFFFFFF#32)).set (3 * dlen + 2) cref
    let st4 : FullState := { st3 with scratch := { st3.scratch with delayed := del' } }
    PropLitInv c F0 F_cur (withDel s del') st4 not_lit.toNat off0_v.toNat q_v.toNat
      (p_v + 1#64 + 1#64).toNat end0_v.toNat ∧
    DelayedWatchesOk st4.core del' (dlen + 1) not_lit.toNat := by
  intro del' st4
  have hdel_len := hlen3.scratch_ok.delayed_len_arr
  have hlen4 : st4.LengthsOk c :=
    ⟨hlen3.core_ok, { hlen3.scratch_ok with delayed_len_arr := by simp [st4, del', hdel_len] }⟩
  have hag4 : AgreesExcept propLitCoreMask (withDel s del').core st4.core := by
    have hag1 := hpi1.ag.update (fun k => { k with arena := st3.core.arena })
    have hcore4 : st4.core = { sem1.core with arena := st3.core.arena } := hst3_core_eq
    rw [hcore4]; exact hag1
  refine ⟨{ len := hlen4, nw := hnw3, sw := hp2_nat.symm ▸ hsw3
            ag := hag4
            tr := hpi1.tr.congr (by dsimp only [st4]; rw [hst3_core_eq])
              (by dsimp only [st4]; rw [hst3_core_eq]) (by dsimp only [st4]; rw [hst3_core_eq])
            perm := hpi1.perm.trans hperm13
            sc_eq := by
              have hs1 := hpi1.sc_eq; dsimp only [withDel] at hs1 ⊢
              dsimp only [st4]; rw [hst3_sc_eq, hs1]
            not_f := by dsimp only [st4]; rw [hst3_core_eq]; exact hpi1.not_f },
          delayedWatchesOk_push hdel3_ok (by rw [hdel_len]; omega) hrepl_lt3 hrepl_ne_not
            (bv32_mask7f_flag0 other) hcr_lt hcr_ref3⟩

private def s15ReplArenaStores (pArena : Val i64) (not_lit cref ri_f repl_f : Val i32)
    (cbase_v ticks1_v : Val i64) (k : Val i64 → Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  .let_ (Op.mk (.add i64) (.var ticks1_v, (.imm (1 : BitVec 64), ()))) fun t2 =>
  .let_ (Op.mk (.zext 32 64) (.var cref, ())) fun cr64 =>
  .let_ (Op.mk (.add i64) (.var cr64.1, (.imm (1 : BitVec 64), ()))) fun cr1 =>
  .let_ (Op.mk (.mul i64) (.var cr1.1, (.imm (4 : BitVec 64), ()))) fun cr1_4 =>
  .let_ (Op.mk (.add i64) (.var pArena, (.var cr1_4.1, ()))) fun ar1 =>
  .store (.var ri_f) (.var ar1.1) (
    .let_ (Op.mk (.add i64) (.var cbase_v, (.imm (1 : BitVec 64), ()))) fun cb1 =>
    .let_ (Op.mk (.mul i64) (.var cb1.1, (.imm (4 : BitVec 64), ()))) fun cb1_4 =>
    .let_ (Op.mk (.add i64) (.var pArena, (.var cb1_4.1, ()))) fun ar2 =>
    .store (.var repl_f) (.var ar2.1) (
      .let_ (Op.mk (.zext 32 64) (.var ri_f, ())) fun ri64 =>
      .let_ (Op.mk (.add i64) (.var cbase_v, (.var ri64.1, ()))) fun cb_r =>
      .let_ (Op.mk (.mul i64) (.var cb_r.1, (.imm (4 : BitVec 64), ()))) fun cb_r4 =>
      .let_ (Op.mk (.add i64) (.var pArena, (.var cb_r4.1, ()))) fun ar3 =>
      .store (.var not_lit) (.var ar3.1) (k t2.1)
    )
  )

private def s15ReplWatchStores (pWvec pWstk : Val i64) (other cref repl_f : Val i32)
    (rsz_v rwend_v : Val i64) (k : Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  .let_ (Op.mk (.mul i64) (.var rwend_v, (.imm (4 : BitVec 64), ()))) fun rw4 =>
  .let_ (Op.mk (.add i64) (.var pWstk, (.var rw4.1, ()))) fun ws0 =>
  .let_ (Op.mk (.and i32) (.var other, (.imm 0x7FFFFFFF#32, ()))) fun ob =>
  .store (.var ob.1) (.var ws0.1) (
    .let_ (Op.mk (.add i64) (.var rwend_v, (.imm (1 : BitVec 64), ()))) fun rw1 =>
    .let_ (Op.mk (.mul i64) (.var rw1.1, (.imm (4 : BitVec 64), ()))) fun rw1_4 =>
    .let_ (Op.mk (.add i64) (.var pWstk, (.var rw1_4.1, ()))) fun ws1 =>
    .store (.var cref) (.var ws1.1) (
      .let_ (Op.mk (.zext 32 64) (.var repl_f, ())) fun rp64 =>
      .let_ (Op.mk (.sext 32 64) (.imm (1 : BitVec 32), ())) fun one64 =>
      .let_ (Op.mk (.shl i64) (.var rp64.1, (.var one64.1, ()))) fun rsh =>
      .let_ (Op.mk (.add i64) (.var rsh.1, (.imm (1 : BitVec 64), ()))) fun ridx =>
      .let_ (Op.mk (.mul i64) (.var ridx.1, (.imm (4 : BitVec 64), ()))) fun ridx4 =>
      .let_ (Op.mk (.add i64) (.var pWvec, (.var ridx4.1, ()))) fun wv1 =>
      .let_ (Op.mk (.add i64) (.var rsz_v, (.imm (2 : BitVec 64), ()))) fun rsz2 =>
      .let_ (Op.mk (.trunc 64 32) (.var rsz2.1, ())) fun rsz32 =>
      .store (.var rsz32.1) (.var wv1.1) k
    )
  )

private def s15RawReplInstallExpr (h_p pArena pWvec pWstk pDel : Val i64)
    (not_lit other cref ri_f repl_f : Val i32)
    (cbase_v tend_v unass_v unfl_v ticks1_v p2_v q_v di_v dlim_v wcap_v
      roff_v rsz_v rwend_v wlen_v : Val i64)
    (L : Cont [i64, i64, i64, i64, i64, i64, i64, .bool])
    (B : Cont [i64, i64, i64, i64, i64, i64, i64, .bool, .bool]) : Expr Val Cont [.bool] :=
  .group (sig := [[]])
    (fun _ => .cons (fun _ =>
      .group (sig := [[]])
        (fun _ => .cons (fun _ =>
          .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var di_v, (.var dlim_v, ()))) fun cdi =>
          .jnz (.var cdi.1) (
            s15ReplArenaStores pArena not_lit cref ri_f repl_f cbase_v ticks1_v fun t2 =>
              .let_ (Op.mk (.mul i64) (.var di_v, (.imm (4 : BitVec 64), ()))) fun d0_4 =>
              .let_ (Op.mk (.add i64) (.var pDel, (.var d0_4.1, ()))) fun d0 =>
              .store (.var repl_f) (.var d0.1) (
                .let_ (Op.mk (.add i64) (.var di_v, (.imm (1 : BitVec 64), ()))) fun di1 =>
                .let_ (Op.mk (.mul i64) (.var di1.1, (.imm (4 : BitVec 64), ()))) fun d1_4 =>
                .let_ (Op.mk (.add i64) (.var pDel, (.var d1_4.1, ()))) fun d1 =>
                .let_ (Op.mk (.and i32) (.var other, (.imm 0x7FFFFFFF#32, ()))) fun ob =>
                .store (.var ob.1) (.var d1.1) (
                  .let_ (Op.mk (.add i64) (.var di_v, (.imm (2 : BitVec 64), ()))) fun di2 =>
                  .let_ (Op.mk (.mul i64) (.var di2.1, (.imm (4 : BitVec 64), ()))) fun d2_4 =>
                  .let_ (Op.mk (.add i64) (.var pDel, (.var d2_4.1, ()))) fun d2 =>
                  .store (.var cref) (.var d2.1) (
                    .let_ (Op.mk (.add i64) (.var di_v, (.imm (3 : BitVec 64), ()))) fun di3 =>
                    .jump L (.var tend_v, (.var unass_v, (.var unfl_v, (.var t2,
                      (.var p2_v, (.var q_v, (.var di3.1, (.var false, ()))))))))
                  )
                )
              )
          ) (
            .let_ (Op.mk (.sub i64) (.var p2_v, (.imm (2 : BitVec 64), ()))) fun pb =>
            .let_ (Op.mk (.sub i64) (.var ticks1_v, (.imm (1 : BitVec 64), ()))) fun tb =>
            .jump B (.var tend_v, (.var unass_v, (.var unfl_v, (.var tb.1,
              (.var pb.1, (.var q_v, (.var di_v, (.imm false, (.imm true, ())))))))))
          )
        ) .nil)
        (fun J2 =>
          .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var roff_v, (.imm (0 : BitVec 64), ())))
            fun c0 =>
          .jnz (.var c0.1) (
            .let_ (Op.mk (.cmp .eq i64 .bool rfl) (.var rwend_v, (.var wlen_v, ()))) fun c1 =>
            .jnz (.var c1.1) (
              .let_ (Op.mk (.sub i64) (.var wcap_v, (.var wlen_v, ()))) fun rem =>
              .let_ (Op.mk (.cmp .ule i64 .bool rfl) (.imm (2 : BitVec 64), (.var rem.1, ())))
                fun c2 =>
              .jnz (.var c2.1) (
                s15ReplArenaStores pArena not_lit cref ri_f repl_f cbase_v ticks1_v fun t2 =>
                s15ReplWatchStores pWvec pWstk other cref repl_f rsz_v rwend_v (
                  .let_ (Op.mk (.add i64) (.var rwend_v, (.imm (2 : BitVec 64), ()))) fun rw2 =>
                  .let_ (Op.mk (.add i64) (.var h_p, (.imm (56 : BitVec 64), ()))) fun wlp =>
                  .store (.var rw2.1) (.var wlp.1) (
                    .jump L (.var tend_v, (.var unass_v, (.var unfl_v, (.var t2,
                      (.var p2_v, (.var q_v, (.var di_v, (.var false, ()))))))))
                  )
                )
              ) (.jump J2.1 ())
            ) (.jump J2.1 ())
          ) (.jump J2.1 ())
        )
    ) .nil)
    (fun J1 =>
      .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var roff_v, (.imm (0 : BitVec 64), ()))) fun c0 =>
      .jnz (.var c0.1) (
        .let_ (Op.mk (.add i64) (.var rwend_v, (.imm (2 : BitVec 64), ()))) fun rw2 =>
        .let_ (Op.mk (.cmp .ule i64 .bool rfl) (.var rw2.1, (.var wlen_v, ()))) fun c1 =>
        .jnz (.var c1.1) (
          .let_ (Op.mk (.mul i64) (.var rwend_v, (.imm (4 : BitVec 64), ()))) fun rw4 =>
          .let_ (Op.mk (.add i64) (.var pWstk, (.var rw4.1, ()))) fun ws0 =>
          .load i32 (.var ws0.1) fun ld0 =>
          .let_ (Op.mk (.cmp .eq i32 .bool rfl) (.var ld0, (.imm 0xFFFFFFFF#32, ()))) fun c2 =>
          .jnz (.var c2.1) (
            .let_ (Op.mk (.add i64) (.var rwend_v, (.imm (1 : BitVec 64), ()))) fun rw1 =>
            .let_ (Op.mk (.mul i64) (.var rw1.1, (.imm (4 : BitVec 64), ()))) fun rw1_4 =>
            .let_ (Op.mk (.add i64) (.var pWstk, (.var rw1_4.1, ()))) fun ws1 =>
            .load i32 (.var ws1.1) fun ld1 =>
            .let_ (Op.mk (.cmp .eq i32 .bool rfl) (.var ld1, (.imm 0xFFFFFFFF#32, ()))) fun c3 =>
            .jnz (.var c3.1) (
              s15ReplArenaStores pArena not_lit cref ri_f repl_f cbase_v ticks1_v fun t2 =>
              s15ReplWatchStores pWvec pWstk other cref repl_f rsz_v rwend_v (
                .group (sig := [[]])
                  (fun _ => .cons (fun _ =>
                    .jump L (.var tend_v, (.var unass_v, (.var unfl_v, (.var t2,
                      (.var p2_v, (.var q_v, (.var di_v, (.var false, ()))))))))
                  ) .nil)
                  (fun Jwu =>
                    .let_ (Op.mk (.add i64) (.var h_p, (.imm (464 : BitVec 64), ()))) fun wu0 =>
                    .load i64 (.var wu0.1) fun wuv =>
                    .let_ (Op.mk (.cmp .uge i64 .bool rfl) (.var wuv, (.imm (2 : BitVec 64), ())))
                      fun cwu =>
                    .jnz (.var cwu.1) (
                      .let_ (Op.mk (.add i64) (.var h_p, (.imm (464 : BitVec 64), ()))) fun wu1 =>
                      .load i64 (.var wu1.1) fun wuv1 =>
                      .let_ (Op.mk (.sub i64) (.var wuv1, (.imm (2 : BitVec 64), ()))) fun wud =>
                      .let_ (Op.mk (.add i64) (.var h_p, (.imm (464 : BitVec 64), ()))) fun wu2 =>
                      .store (.var wud.1) (.var wu2.1) (.jump Jwu.1 ())
                    ) (.jump Jwu.1 ())
                  )
              )
            ) (.jump J1.1 ())
          ) (.jump J1.1 ())
        ) (.jump J1.1 ())
      ) (.jump J1.1 ())
    )

private theorem s15_raw_repl_install_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sem sem1 : FullState}
    {not_lit other cref ri_f repl_f nl_lvl0 : BitVec 32}
    {off0_v tend_v unass_v unfl_v ticks_v p_v q_v end0_v di_v ignore_ref : BitVec 64}
    {roff_v rsz_v rwend_v wlen_v : BitVec 64} {dlen : Nat} {R : Mem 64 → Prop} {mj : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    {L : Cont [i64, i64, i64, i64, i64, i64, i64, .bool]}
    {B : Cont [i64, i64, i64, i64, i64, i64, i64, .bool, .bool]}
    (hB : ∀ a mb,
      (∃ (sem : FullState) (dlen : Nat),
        PropLitInv c F0 F_cur (withDel s sem.scratch.delayed) sem not_lit.toNat
          off0_v.toNat a.2.2.2.2.2.1.toNat a.2.2.2.2.1.toNat end0_v.toNat ∧
        a.2.2.2.2.2.2.1.toNat = 3 * dlen ∧ dlen ≤ c.delayed_cap ∧
        DelayedWatchesOk sem.core sem.scratch.delayed dlen not_lit.toNat ∧
        (c.delayed_cap = 0 → sem.scratch.delayed = s.scratch.delayed) ∧
        a.1.toNat = sem.core.trail_end ∧ a.2.1 = sem.core.unassigned ∧
        a.2.2.1 = sem.core.unflushed ∧
        (a.2.2.2.2.2.2.2.2.1 = true → a.2.2.2.2.2.2.2.1 = false) ∧
        (a.2.2.2.2.2.2.2.1 = false → sem.core.oom = 0#64 ∧
          sem.core.confl_type = s.core.confl_type) ∧
        (a.2.2.2.2.2.2.2.1 = true → PropLitConfl F_cur ignore_ref sem.core) ∧
        (FullMem c (fastPropMem s sem) ⋆ R) mb) → B a mb)
    (ih : ∀ a ml, end0_v.toNat - a.2.2.2.2.1.toNat < end0_v.toNat - p_v.toNat →
      (∃ (sem : FullState) (dlen : Nat),
        a.2.2.2.2.2.2.2.1 = false ∧
        end0_v.toNat - a.2.2.2.2.1.toNat = end0_v.toNat - a.2.2.2.2.1.toNat ∧
        PropLitInv c F0 F_cur (withDel s sem.scratch.delayed) sem not_lit.toNat
          off0_v.toNat a.2.2.2.2.2.1.toNat a.2.2.2.2.1.toNat end0_v.toNat ∧
        a.2.2.2.2.2.2.1.toNat = 3 * dlen ∧ dlen ≤ c.delayed_cap ∧
        DelayedWatchesOk sem.core sem.scratch.delayed dlen not_lit.toNat ∧
        (c.delayed_cap = 0 → sem.scratch.delayed = s.scratch.delayed) ∧
        a.1.toNat = sem.core.trail_end ∧ a.2.1 = sem.core.unassigned ∧
        a.2.2.1 = sem.core.unflushed ∧
        sem.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 ∧
        sem.core.oom = 0#64 ∧ sem.core.confl_type = s.core.confl_type ∧
        (FullMem c (fastPropMem s sem) ⋆ R) ml) → L a ml)
    (hrem_dec : end0_v.toNat - (p_v.toNat + 2) < end0_v.toNat - p_v.toNat)
    (hwc : c.wcap < 2 * dimacsBound) (hdelc : c.delayed_cap < dimacsBound)
    (hpi1 : PropLitInv c F0 F_cur (withDel s sem.scratch.delayed) sem1 not_lit.toNat
      off0_v.toNat q_v.toNat (p_v.toNat + 2) end0_v.toNat)
    (hsw1_pre : SplitWatchesInv F_cur sem1.core not_lit.toNat off0_v.toNat q_v.toNat
      p_v.toNat end0_v.toNat)
    (hdel1_eq : sem1.scratch.delayed = sem.scratch.delayed)
    (hdi_eq : di_v.toNat = 3 * dlen) (hdlen_le : dlen ≤ c.delayed_cap)
    (hdel1_ok : DelayedWatchesOk sem1.core sem1.scratch.delayed dlen not_lit.toNat)
    (hd0_1 : c.delayed_cap = 0 → sem1.scratch.delayed = s.scratch.delayed)
    (htend1_eq : tend_v.toNat = sem1.core.trail_end)
    (hunass1_eq : unass_v = sem1.core.unassigned) (hunfl1_eq : unfl_v = sem1.core.unflushed)
    (hnl1 : sem1.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0)
    (hoom1 : sem1.core.oom = 0#64) (hct1 : sem1.core.confl_type = s.core.confl_type)
    (hnot_st1 : not_lit.toNat < 2 * sem1.core.cur_vars)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref1 : cref.toNat ∈ fullArenaClauseRefsCore sem1.core)
    (hcr_lt_alen1 : cref.toNat < sem1.core.arena_len)
    (hfit1 : cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤ sem1.core.arena_len)
    (har4 : sem1.core.arena[cref.toNat + 4]? = some not_lit)
    (hr2 : 2 ≤ ri_f.toNat) (hr_lt : ri_f.toNat < fullArenaClauseSizeCore sem1.core cref.toNat)
    (hrepl_def : repl_f = sem1.core.arena[cref.toNat + 3 + ri_f.toNat]'(by
      have := hpi1.len.core_ok.arena_len_arr; have := hpi1.len.core_ok.arena_len_le; omega))
    (hcand : repl_f.toNat < 2 * sem1.core.cur_vars ∧
      (BitVec.signExtend 32 (sem1.core.vals[repl_f.toNat]?.getD 0#8)).slt 0#32 = false)
    (hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2)
    (h1_idx : (cref.setWidth 64 + 1#64).toNat = cref.toNat + 1)
    (h3_idx : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3)
    (h4_idx : (cref.setWidth 64 + 3#64 + 1#64).toNat = cref.toNat + 4)
    (h3r_idx : (cref.setWidth 64 + 3#64 + ri_f.setWidth 64).toNat = cref.toNat + 3 + ri_f.toNat)
    (hroff_eq : roff_v.toNat = fullWatchOffCore sem1.core repl_f.toNat)
    (hrsz_eq : rsz_v.toNat = fullWatchSizeCore sem1.core repl_f.toNat)
    (hrwend_def : rwend_v = roff_v + rsz_v)
    (hwlen_eq : wlen_v = BitVec.ofNat 64 sem1.core.wlen)
    (hmj : (FullMem c (fastPropMem s sem1) ⋆ R) mj) :
    wp Γ Q X (s15RawReplInstallExpr c.hdr c.pArena c.pWvec c.pWstk c.pDelayed not_lit other
      cref ri_f repl_f (cref.setWidth 64 + 3#64) tend_v unass_v unfl_v (ticks_v + 1#64)
      (p_v + 1#64 + 1#64) q_v di_v (BitVec.ofNat 64 c.delayed_cap * 3#64)
      (BitVec.ofNat 64 c.wcap) roff_v rsz_v rwend_v wlen_v L B) mj := by
  subst hwlen_eq
  have hwstk1 := hpi1.len.core_ok.wstk_len_arr
  have hwvec1 := hpi1.len.core_ok.wvec_len
  have haren1 := hpi1.len.core_ok.arena_len_arr
  have halen1 := hpi1.len.core_ok.arena_len_le
  have hwlen1_le := hpi1.len.core_ok.wlen_le
  have hdel1_len := hpi1.len.scratch_ok.delayed_len_arr
  have hwc' := hwc; have hdelc' := hdelc
  unfold dimacsBound at hwc' hdelc'
  have hwc64 : c.wcap + 2 < 2 ^ 64 := Nat.lt_trans (Nat.add_lt_add_right hwc' 2) (by decide)
  have hwcap_nat : (BitVec.ofNat 64 c.wcap).toNat = c.wcap := Nat.mod_eq_of_lt (by omega)
  have hdlim_nat : (BitVec.ofNat 64 c.delayed_cap * 3#64).toNat = 3 * c.delayed_cap := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c.delayed_cap < 2 ^ 64)]
    change (c.delayed_cap * 3) % 2 ^ 64 = 3 * c.delayed_cap
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have h3r_ne1 : cref.toNat + 1 ≠ cref.toNat + 3 + ri_f.toNat := by omega
  have hfit1_ar : cref.toNat + 3 + ri_f.toNat < sem1.core.arena.length := by omega
  have hrepl_set1 : repl_f = (sem1.core.arena.set (cref.toNat + 1)
      (BitVec.ofNat 32 ri_f.toNat))[cref.toNat + 3 + ri_f.toNat]'(by simp [hfit1_ar]) := by
    rw [List.getElem_set_ne h3r_ne1]; exact hrepl_def
  let st3 : FullState :=
    { sem1 with core := { sem1.core with
        arena := ((sem1.core.arena.set (cref.toNat + 1) (BitVec.ofNat 32 ri_f.toNat)).set
          (cref.toNat + 4) repl_f).set (cref.toNat + 3 + ri_f.toNat) not_lit } }
  have ⟨hlen3, hnw3, hsw3, hperm13, hcr_ref3, _hcsz3, hrepl_lt,
      hrepl_ne_not, _hw0_ne_ff, _hcr_ne_ff⟩ :=
    fastProp_b1_swap (other := other) (r := ri_f.toNat) hpi1 hcr_lt_alen1
      hcr_ref1 hfit1 har4 hr2 hr_lt hrepl_set1
      (by simpa only [List.getElem?_eq_getElem hfit1_ar, Option.getD_some, ← hrepl_def] using hcand)
  have hri32 : BitVec.setWidth 32 ri_f = ri_f := by apply BitVec.eq_of_toNat_eq; simp
  have hridx1 : ((repl_f.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * repl_f.toNat + 1 :=
    fc_bv64_shl1_add1_nat repl_f
  have hr_bd := hpi1.sw.layout.bounds repl_f.toNat hrepl_lt
  have hrwend_nat : rwend_v.toNat =
      fullWatchOffCore sem1.core repl_f.toNat + fullWatchSizeCore sem1.core repl_f.toNat := by
    rw [hrwend_def, bv64_add_toNat (by rw [hroff_eq, hrsz_eq]; omega), hroff_eq, hrsz_eq]
  have hrwend1_nat : (rwend_v + 1#64).toNat = rwend_v.toNat + 1 :=
    bv64_add1_toNat (by rw [hrwend_nat]; omega)
  have hrwend2_nat : (rwend_v + 2#64).toNat = rwend_v.toNat + 2 :=
    bv64_add2_toNat (by rw [hrwend_nat]; omega)
  have hrsz2_32 : (rsz_v + 2#64).setWidth 32 =
      BitVec.ofNat 32 (fullWatchSizeCore sem1.core repl_f.toNat + 2) := by
    apply BitVec.eq_of_toNat_eq
    have hadd : (rsz_v + 2#64).toNat = fullWatchSizeCore sem1.core repl_f.toNat + 2 := by
      rw [show (2#64 : BitVec 64) = (2 : BitVec 64) from rfl,
        bv64_add2_toNat (by rw [hrsz_eq]; omega), hrsz_eq]
    rw [BitVec.toNat_setWidth, hadd, BitVec.toNat_ofNat]
  have hwlen1_nat : (BitVec.ofNat 64 sem1.core.wlen).toNat = sem1.core.wlen :=
    Nat.mod_eq_of_lt (by omega)
  have hdi1_nat : (di_v + 1#64).toNat = 3 * dlen + 1 := by
    rw [BitVec.toNat_add, hdi_eq]; change (3 * dlen + 1) % 2 ^ 64 = 3 * dlen + 1
    exact Nat.mod_eq_of_lt (by omega)
  have hdi2_nat : (di_v + 2#64).toNat = 3 * dlen + 2 := by
    rw [BitVec.toNat_add, hdi_eq]; change (3 * dlen + 2) % 2 ^ 64 = 3 * dlen + 2
    exact Nat.mod_eq_of_lt (by omega)
  have hdi3_nat : (di_v + 3#64).toNat = 3 * (dlen + 1) := by
    rw [BitVec.toNat_add, hdi_eq]; change (3 * dlen + 3) % 2 ^ 64 = 3 * (dlen + 1)
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hdel3_ok : DelayedWatchesOk st3.core st3.scratch.delayed dlen not_lit.toNat :=
    delayedWatchesOk_congr (k1 := sem1.core) rfl hperm13.1 hdel1_ok
  have hm1_wvec : (fastPropMem s sem1).core.wvec.length = 4 * c.max_vars := by
    rw [fastPropMem_wvec]; exact hwvec1
  have hm1_wstk : (fastPropMem s sem1).core.wstk.length = c.wcap := by
    rw [fastPropMem_wstk]; exact hwstk1
  have hm1_aren : (fastPropMem s sem1).core.arena.length = c.arena_cap := by
    rw [fastPropMem_arena]; exact haren1
  have hm1_del : (fastPropMem s sem1).scratch.delayed.length = 3 * c.delayed_cap := by
    rw [fastPropMem_delayed]; exact hdel1_len
  have hsd_fpm : ∀ st, fastPropMem (withDel s sem.scratch.delayed) st = fastPropMem s st :=
    fun st => fastPropMem_s_delayed_irrel s st sem.scratch.delayed
  have hrepl_max : repl_f.toNat < 2 * c.max_vars :=
    Nat.lt_of_lt_of_le hrepl_lt (Nat.mul_le_mul_left 2 hpi1.len.core_ok.cur_vars_le)
  unfold s15RawReplInstallExpr s15ReplArenaStores s15ReplWatchStores
  refine wp_join_group (ts := []) (fun () m1 => mj = m1) ?_ ?_
  · rintro _ ⟨⟩ _ rfl
    refine wp_join_group (ts := []) (fun () m2 => mj = m2) ?_ ?_
    · rintro _ ⟨⟩ _ rfl
      -- Sub-branch 3 (`di < dlim`) & Sub-branch 4 (`ovf = true; break`)
      c0_hsplit
      · have hdi_lt_lim : di_v.toNat < 3 * c.delayed_cap := by rw [← hdlim_nat]; exact hc
        have hdlen_lt : dlen < c.delayed_cap := by omega
        s15_hsteps_nogrp
        have ⟨hpi4, hdel4_ok⟩ := s15_repl_delay_step (st3 := st3) (other := other) hpi1 rfl rfl
          hlen3 hnw3 hsw3 hperm13 hcr_lt hcr_ref3 hrepl_lt hrepl_ne_not hdel3_ok hdlen_lt hp2_nat
        exact ih (tend_v, unass_v, unfl_v, ticks_v + 1#64 + 1#64, p_v + 1#64 + 1#64, q_v,
          di_v + 3#64, false, ()) m (by dsimp only; rwa [hp2_nat])
          ⟨_, dlen + 1, rfl, rfl, hpi4, hdi3_nat, by omega, hdel4_ok, fun h0 => by omega,
            htend1_eq, hunass1_eq, hunfl1_eq, hnl1, hoom1, hct1, by
              have h_ad : ∀ a d,
                  ({ core := { (fastPropMem s sem1).core with arena := a }
                     scratch := { (fastPropMem s sem1).scratch with delayed := d } } :
                    FullState) =
                  fastPropMem s { sem1 with
                    core := { sem1.core with arena := a }
                    scratch := { sem1.scratch with delayed := d } } := fun a d => by
                rw [fastPropMem_def, fastPropMem_def]
              simpa only [st3, fastPropMem_arena, fastPropMem_delayed, BitVec.ofNat_eq_ofNat,
                BitVec.ofNat_toNat, hri32, h1_idx, h4_idx, h3r_idx, hdi_eq, hdi1_nat, hdi2_nat,
                h_ad, hsd_fpm] using hm⟩
      · s15_hsteps_nogrp
        have hp_back : (p_v + 1#64 + 1#64 - 2#64) = p_v := bv64_add2_sub2 p_v
        have hpi_ovf : PropLitInv c F0 F_cur (withDel s sem1.scratch.delayed) sem1 not_lit.toNat
            off0_v.toNat q_v.toNat (p_v + 1#64 + 1#64 - 2#64).toNat end0_v.toNat :=
          { len := hpi1.len, nw := hpi1.nw, sw := hp_back.symm ▸ hsw1_pre
            ag := hpi1.ag, tr := hpi1.tr, perm := hpi1.perm
            sc_eq := by
              have hs1 := hpi1.sc_eq; dsimp only [withDel] at hs1 ⊢; rw [hs1]
            not_f := hpi1.not_f }
        exact hB (tend_v, unass_v, unfl_v, ticks_v + 1#64 - 1#64, p_v + 1#64 + 1#64 - 2#64,
          q_v, di_v, false, true, ()) mj
          ⟨sem1, dlen, hpi_ovf, hdi_eq, hdlen_le, hdel1_ok, hd0_1, htend1_eq, hunass1_eq,
            hunfl1_eq, fun _ => rfl, fun _ => ⟨hoom1, hct1⟩, by simp, hmj⟩
    · intro J2 hJ2
      -- Sub-branch 2: in-place end-of-stack append
      c0_hsplit
      · have hroff_pos : 0 < fullWatchOffCore st3.core repl_f.toNat := by
          change 0 < fullWatchOffCore sem1.core repl_f.toNat; rw [← hroff_eq]; exact hc
        c0_hsplit
        · have hend_wlen : fullWatchOffCore st3.core repl_f.toNat +
              fullWatchSizeCore st3.core repl_f.toNat = st3.core.wlen := by
            change fullWatchOffCore sem1.core repl_f.toNat +
              fullWatchSizeCore sem1.core repl_f.toNat = sem1.core.wlen
            rw [← hrwend_nat, ← hwlen1_nat]; exact congrArg BitVec.toNat hc
          c0_hsplit
          · have hfit2 : st3.core.wlen + 2 ≤ c.wcap := by
              change sem1.core.wlen + 2 ≤ c.wcap
              simp only [BitVec.reduceToNat] at hc; omega
            s15_hsteps_nogrp
            have hpi4 := s15_repl_end_step (st3 := st3) (other := other) hpi1 hdel1_eq rfl rfl
              hlen3 hnw3 hsw3 hperm13 hcr_lt hcr_ref3 hrepl_lt hrepl_ne_not hnot_st1 hroff_pos
              hend_wlen hfit2 hrwend_nat hp2_nat
            have hrsz2_st3 : (rsz_v + 2#64).setWidth 32 =
                BitVec.ofNat 32 (fullWatchSizeCore st3.core repl_f.toNat + 2) := hrsz2_32
            exact ih (tend_v, unass_v, unfl_v, ticks_v + 1#64 + 1#64, p_v + 1#64 + 1#64, q_v,
              di_v, false, ()) m (by dsimp only; rwa [hp2_nat])
              ⟨_, dlen, rfl, rfl, hpi4, hdi_eq, hdlen_le, hdel3_ok, hd0_1, htend1_eq, hunass1_eq,
                hunfl1_eq, hnl1, hoom1, hct1, by
                  simpa only [st3, fastPropMem_arena, fastPropMem_wstk, fastPropMem_wvec,
                    fastPropMem_wlen, BitVec.ofNat_eq_ofNat, BitVec.ofNat_toNat, hri32, h1_idx,
                    h4_idx, h3r_idx, hridx1, hrwend1_nat, hrwend2_nat, hrsz2_st3,
                    fastPropMem_with_wvec_wstk_wl, hsd_fpm] using hm⟩
          · s15_hsteps_nogrp; exact hJ2 () mj rfl
        · s15_hsteps_nogrp; exact hJ2 () mj rfl
      · s15_hsteps_nogrp; exact hJ2 () mj rfl
  · intro J1 hJ1
    -- Sub-branch 1: in-place sentinel-reuse append
    c0_hsplit
    · have hroff_pos : 0 < fullWatchOffCore st3.core repl_f.toNat := by
        change 0 < fullWatchOffCore sem1.core repl_f.toNat; rw [← hroff_eq]; exact hc
      c0_hsplit
      · have hrwend2_le' : fullWatchOffCore sem1.core repl_f.toNat +
            fullWatchSizeCore sem1.core repl_f.toNat + 2 ≤ sem1.core.wlen := by
          have hc' : (rwend_v.toNat + 2) % 2 ^ 64 ≤ sem1.core.wlen % 2 ^ 64 := by
            simpa only [show (2 : BitVec 64).toNat = 2 from rfl] using hc
          rw [Nat.mod_eq_of_lt (by rw [hrwend_nat]; omega),
            Nat.mod_eq_of_lt (by omega)] at hc'
          omega
        have hrwend2_le : fullWatchOffCore st3.core repl_f.toNat +
            fullWatchSizeCore st3.core repl_f.toNat + 2 ≤ st3.core.wlen := hrwend2_le'
        have hrwend_lt_ws : rwend_v.toNat < (fastPropMem s sem1).core.wstk.length := by
          rw [hm1_wstk, hrwend_nat]; omega
        have hrwend1_lt_ws :
            (rwend_v + (1 : BitVec 64)).toNat < (fastPropMem s sem1).core.wstk.length := by
          rw [show (1 : BitVec 64) = 1#64 from rfl, hrwend1_nat, hm1_wstk, hrwend_nat]; omega
        c0_hsplit
        · have hsent0 : st3.core.wstk[fullWatchOffCore st3.core repl_f.toNat +
              fullWatchSizeCore st3.core repl_f.toNat]? = some 0xFFFFFFFF#32 := by
            change sem1.core.wstk[fullWatchOffCore sem1.core repl_f.toNat +
              fullWatchSizeCore sem1.core repl_f.toNat]? = some 0xFFFFFFFF#32
            rw [← hrwend_nat, List.getElem?_eq_getElem (by rw [hwstk1, hrwend_nat]; omega)]
            congr 1; simpa only [fc_getElem_wstk] using hc
          c0_hsplit
          · have hsent1 : st3.core.wstk[fullWatchOffCore st3.core repl_f.toNat +
                fullWatchSizeCore st3.core repl_f.toNat + 1]? = some 0xFFFFFFFF#32 := by
              change sem1.core.wstk[fullWatchOffCore sem1.core repl_f.toNat +
                fullWatchSizeCore sem1.core repl_f.toNat + 1]? = some 0xFFFFFFFF#32
              rw [← hrwend_nat, ← hrwend1_nat,
                List.getElem?_eq_getElem (by rw [hwstk1, hrwend1_nat, hrwend_nat]; omega)]
              congr 1
              simpa only [fc_getElem_wstk, BitVec.ofNat_eq_ofNat, BitVec.toNat_add] using hc
            s15_hsteps_nogrp
            refine wp_join_group (ts := [])
              (fun () mw => ∃ wu' : BitVec 64,
                let st4 : FullState :=
                  { st3 with core := { st3.core with
                      wstk := (st3.core.wstk.set rwend_v.toNat
                        (other &&& 0x7FFFFFFF#32)).set (rwend_v.toNat + 1) cref
                      wvec := st3.core.wvec.set (2 * repl_f.toNat + 1)
                        (BitVec.ofNat 32 (fullWatchSizeCore sem1.core repl_f.toNat + 2))
                      wusable := wu' } }
                (FullMem c (fastPropMem s st4) ⋆ R) mw) ?_ ?_
            · rintro _ ⟨⟩ mw ⟨wu', hmw⟩
              have hpi4 := s15_repl_sentinel_step (st3 := st3) (other := other) (wu' := wu') hpi1
                hdel1_eq rfl rfl hlen3 hnw3 hsw3 hperm13 hcr_lt hcr_ref3 hrepl_lt hrepl_ne_not
                hnot_st1 hroff_pos hrwend2_le hsent0 hsent1 hrwend_nat hp2_nat
              s15_head_steps
              exact ih (tend_v, unass_v, unfl_v, ticks_v + 1#64 + 1#64, p_v + 1#64 + 1#64, q_v,
                di_v, false, ()) mw (by dsimp only; rwa [hp2_nat])
                ⟨_, dlen, rfl, rfl, hpi4, hdi_eq, hdlen_le, hdel3_ok, hd0_1, htend1_eq,
                  hunass1_eq, hunfl1_eq, hnl1, hoom1, hct1, hmw⟩
            · intro Jwu hJwu; s15_hsteps_nogrp
              · refine hJwu () m ⟨sem1.core.wusable - 2#64, ?_⟩
                simpa only [st3, fastPropMem_arena, fastPropMem_wstk, fastPropMem_wvec,
                  fastPropMem_wusable, BitVec.ofNat_eq_ofNat, BitVec.ofNat_toNat, hri32, h1_idx,
                  h4_idx, h3r_idx, hridx1, hrwend1_nat, hrsz2_32,
                  fastPropMem_with_wvec_wstk_wu, hsd_fpm] using hm
              · refine hJwu () m ⟨sem1.core.wusable, ?_⟩
                simpa only [st3, fastPropMem_arena, fastPropMem_wstk, fastPropMem_wvec,
                  fastPropMem_wusable, BitVec.ofNat_eq_ofNat, BitVec.ofNat_toNat, hri32, h1_idx,
                  h4_idx, h3r_idx, hridx1, hrwend1_nat, hrsz2_32,
                  fastPropMem_with_wvec_wstk_wu, hsd_fpm] using hm
          · s15_hsteps_nogrp; exact hJ1 () mj rfl
        · s15_hsteps_nogrp; exact hJ1 () mj rfl
      · s15_hsteps_nogrp; exact hJ1 () mj rfl
    · s15_hsteps_nogrp; exact hJ1 () mj rfl

/-! ## 1. Hot-Loop Single-Function BCP Proof (`full_prop_lit_raw_s15_wp`) -/

theorem full_prop_lit_raw_s15_wp (Γ : Env)
    (hPush : ∀ args m Q X, fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    (hOvf : ∀ args m Q X, fullPropLitOvfS15Spec args m Q X →
      Γ "full_prop_lit_ovf_s15" [i64, i32, i64, i64, i64, i64] [.bool] args m Q X) :
    ∀ args m Q X, fullPropLitS15Spec args m Q X →
      Func.wp Γ full_prop_lit_raw_s15_body args m Q X := by
  rintro ⟨h, lit, ignore_ref, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hoom0, hm, hQ⟩
  have hmaxv := c.hmaxv; have har := c.harena; have hwc := c.hwcap; have hdelc := c.hdel
  unfold dimacsBound at hmaxv har hwc hdelc
  have hcv0 := hlen0.core_ok.cur_vars_le
  let not_lit : BitVec 32 := lit ^^^ 1#32
  have hret_st : ∀ (ok : Bool) (st : FullState) (ml : Mem 64),
      st.LengthsOk c → FullWitnessInv c F0 F_cur st.core →
      AgreesExcept propLitCoreMask s.core st.core →
      FullPropDecSpecs.FullTrailExt s.core st.core →
      FullPropDecSpecs.FullArenaPermEq s.core st.core →
      st.scratch = { s.scratch with
        search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
        phases := st.scratch.phases, delayed := st.scratch.delayed } →
      (c.delayed_cap = 0 → st.scratch.delayed = s.scratch.delayed) →
      (ok = false → PropLitConfl F_cur ignore_ref st.core) →
      (ok = true → st.core.oom = 0#64 ∧ st.core.confl_type = s.core.confl_type) →
      (FullMem c st ⋆ R) ml → Q (ok, ()) ml := by
    intro ok st ml hst_l hst_w hag htr hperm hsc hd0 hcf hok_oom hml
    have hst_eq := propLit_eq_upd_del hag hsc
    have hst_l' := hst_l; have hst_w' := hst_w
    have htr' : FullTrailExt s.core st.core := ⟨htr.te_ge, htr.trl_pref, htr.lvl_pres⟩
    have hperm' : FullArenaPermEq s.core st.core := ⟨hag.get FullCoreState.arena_len, hperm⟩
    rw [hst_eq] at hst_l' hst_w' htr' hperm' hml
    refine hQ ok st.core.vals st.core.flags st.core.lvl st.core.rsns st.core.trl st.core.trail_pos
      st.core.trail_end st.core.unassigned st.core.unflushed st.core.wvec st.core.arena
      st.core.wstk st.core.wlen st.core.wusable st.core.confl_type st.core.confl_ref
      st.core.confl_lit0 st.core.confl_lit1 st.core.oom st.scratch.search_ticks st.scratch.wsort
      st.scratch.phases st.scratch.delayed ml hst_l' hst_w' htr' hperm' hd0 ?_ hok_oom hml
    intro hf; rcases (hcf hf) with ho | ⟨hc1, hc2⟩
    · exact Or.inl ho
    · refine Or.inr ⟨?_, hc2⟩
      have hc1' : FullConflictOkW F_cur st := fullConflOkW_to_fullConflictOkW hc1
      rwa [hst_eq] at hc1'
  have hret_noop : Q (true, ()) m :=
    hret_st true s m hlen0 hw0 (.refl _ _) (.refl _) (.refl _) rfl (fun _ => rfl) (by simp)
      (fun _ => ⟨hoom0, rfl⟩) hm
  have hvl0 := hlen0.core_ok.vals_len; have hwv0 := hlen0.core_ok.wvec_len
  have hlvl0 := hlen0.core_ok.lvl_len
  have hclv_lt32 : s.core.cur_level < 2 ^ 32 := by
    have := hw0.cur_level_le; have := hlen0.core_ok.trail_end_le; omega
  have hte0_lt64 : s.core.trail_end < 2 ^ 64 := by
    have := hlen0.core_ok.trail_end_le; omega
  have hdlim_nat : (BitVec.ofNat 64 c.delayed_cap * 3#64).toNat = 3 * c.delayed_cap := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c.delayed_cap < 2 ^ 64)]
    change (c.delayed_cap * 3) % 2 ^ 64 = 3 * c.delayed_cap
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hwcap_nat : (BitVec.ofNat 64 c.wcap).toNat = c.wcap :=
    Nat.mod_eq_of_lt (by omega)
  unfold Func.wp full_prop_lit_raw_s15_body
  s15_head_split
  · s15_head_steps; exact hret_noop
  s15_head_split
  · s15_head_steps; exact hret_noop
  s15_head_split
  · s15_head_steps; exact hret_noop
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
    have hpi0 : PropLitInv c F0 F_cur (withDel s s.scratch.delayed) s not_lit.toNat
        (fullWatchOffCore s.core not_lit.toNat) (fullWatchOffCore s.core not_lit.toNat)
        (fullWatchOffCore s.core not_lit.toNat)
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
    s15_hsteps_nogrp
    have hoff_bd := hwat0.layout.bounds not_lit.toNat hnot_lt
    have hwlen0_le := hlen0.core_ok.wlen_le
    have hoff_idx0 : ((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : Nat)).toNat <
        s.core.wvec.length := by
      rw [fc_bv64_shl1_u32_nat, show (lit ^^^ (1 : BitVec 32)) = not_lit from rfl, hwv0]
      have := Nat.mul_le_mul_left 2 hcv0; omega
    have hsz_idx0 : (((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : Nat)) +
        (1 : BitVec 64)).toNat < s.core.wvec.length := by
      rw [fc_bv64_shl1_add1_nat, show (lit ^^^ (1 : BitVec 32)) = not_lit from rfl, hwv0]
      have := Nat.mul_le_mul_left 2 hcv0; omega
    generalize hend0_def :
      (s.core.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : Nat)).toNat]'hoff_idx0
        ).setWidth 64 +
      (s.core.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : Nat)) +
        (1 : BitVec 64)).toNat]'hsz_idx0).setWidth 64 = end0_v
    generalize hoff0_def :
      (s.core.wvec[((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : Nat)).toNat]'hoff_idx0
        ).setWidth 64 = off0_v
    have hoff_nat : off0_v.toNat = fullWatchOffCore s.core not_lit.toNat := by
      rw [← hoff0_def]; unfold fullWatchOffCore; rw [bv_c0_zext32_64]
      exact congrArg BitVec.toNat (fc_getElem_eq_getD_of_idx (fc_bv64_shl1_u32_nat _) _)
    have hsz_nat :
        ((s.core.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : Nat)) +
          (1 : BitVec 64)).toNat]'hsz_idx0).setWidth 64).toNat =
        fullWatchSizeCore s.core not_lit.toNat := by
      unfold fullWatchSizeCore; rw [bv_c0_zext32_64]
      exact congrArg BitVec.toNat (fc_getElem_eq_getD_of_idx (fc_bv64_shl1_add1_nat _) _)
    have hend_nat : end0_v.toNat =
        fullWatchOffCore s.core not_lit.toNat + fullWatchSizeCore s.core not_lit.toNat := by
      rw [← hend0_def, hoff0_def]
      rw [bv64_add_toNat (by
        rw [hoff_nat, hsz_nat]
        exact Nat.lt_of_le_of_lt (Nat.le_trans hoff_bd hwlen0_le) (Nat.lt_trans hwc (by decide))),
        hoff_nat, hsz_nat]
    clear hend0_def hoff0_def
    refine wp_loop_break_group
      (brkTs := [i64, i64, i64, i64, i64, i64, i64, .bool, .bool])
      (lpTs := [i64, i64, i64, i64, i64, i64, i64, .bool])
      (fun (tend_v, unass_v, unfl_v, ticks_v, p_v, q_v, di_v, confl_v, ovf_v, ()) mb =>
        ∃ (sem : FullState) (dlen : Nat),
          PropLitInv c F0 F_cur (withDel s sem.scratch.delayed) sem not_lit.toNat
            off0_v.toNat q_v.toNat p_v.toNat end0_v.toNat ∧
          di_v.toNat = 3 * dlen ∧ dlen ≤ c.delayed_cap ∧
          DelayedWatchesOk sem.core sem.scratch.delayed dlen not_lit.toNat ∧
          (c.delayed_cap = 0 → sem.scratch.delayed = s.scratch.delayed) ∧
          tend_v.toNat = sem.core.trail_end ∧ unass_v = sem.core.unassigned ∧
          unfl_v = sem.core.unflushed ∧
          (ovf_v = true → confl_v = false) ∧
          (confl_v = false → sem.core.oom = 0#64 ∧ sem.core.confl_type = s.core.confl_type) ∧
          (confl_v = true → PropLitConfl F_cur ignore_ref sem.core) ∧
          (FullMem c (fastPropMem s sem) ⋆ R) mb)
      (fun rem (tend_v, unass_v, unfl_v, ticks_v, p_v, q_v, di_v, ovf_v, ()) ml =>
        ∃ (sem : FullState) (dlen : Nat),
          ovf_v = false ∧
          rem = end0_v.toNat - p_v.toNat ∧
          PropLitInv c F0 F_cur (withDel s sem.scratch.delayed) sem not_lit.toNat
            off0_v.toNat q_v.toNat p_v.toNat end0_v.toNat ∧
          di_v.toNat = 3 * dlen ∧ dlen ≤ c.delayed_cap ∧
          DelayedWatchesOk sem.core sem.scratch.delayed dlen not_lit.toNat ∧
          (c.delayed_cap = 0 → sem.scratch.delayed = s.scratch.delayed) ∧
          tend_v.toNat = sem.core.trail_end ∧ unass_v = sem.core.unassigned ∧
          unfl_v = sem.core.unflushed ∧
          sem.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 ∧
          sem.core.oom = 0#64 ∧ sem.core.confl_type = s.core.confl_type ∧
          (FullMem c (fastPropMem s sem) ⋆ R) ml) ?_ ?_ ?_
    · -- Post-loop break handler: sync headers, dispatch `if (ovf)`, else compact + sentinel + flush
      rintro _ ⟨tend_v, unass_v, unfl_v, ticks_v, p_v, q_v, di_v, confl_v, ovf_v, ⟨⟩⟩ mb
        ⟨sem, dlen, hpi, hdi_eq, hdlen_le, hdel_ok, hd0_sem, htend_eq, hunass_eq, hunfl_eq,
          hovf_ncf, hcf_f, hcf_t, hmb⟩
      have hnot_sem : not_lit.toNat < 2 * sem.core.cur_vars := hpi.cur_vars_eq.symm ▸ hnot_lt
      have ⟨hend_le, hwlen_le⟩ := hpi.end_lt_wcap hnot_sem
      have hend_wcap : end0_v.toNat ≤ c.wcap := Nat.le_trans hend_le hwlen_le
      have hwc64 : c.wcap + 1 < 2 ^ 64 := Nat.lt_trans (Nat.add_lt_add_right hwc 1) (by decide)
      have hq_ge := hpi.sw.q_ge; have hq_le := hpi.sw.q_le_p; have hp_le := hpi.sw.p_le_end
      have hidx1_nat :
          ((not_lit.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * not_lit.toNat + 1 :=
        fc_bv64_shl1_add1_nat not_lit
      s15_head_steps
      refine wp_join_group (ts := [])
        (fun () m_sync => ∃ sem_s : FullState,
          PropLitInv c F0 F_cur (withDel s sem_s.scratch.delayed) sem_s not_lit.toNat
            off0_v.toNat q_v.toNat p_v.toNat end0_v.toNat ∧
          sem_s.core = sem.core ∧ sem_s.scratch.delayed = sem.scratch.delayed ∧
          (FullMem c sem_s ⋆ R) m_sync) ?_ ?_
      · rintro _ ⟨⟩ m_sync ⟨sem_s, hpi_s, hcore_s, hdel_s, hm_sync⟩
        have hdel_ok_s : DelayedWatchesOk sem_s.core sem_s.scratch.delayed dlen not_lit.toNat := by
          rw [hcore_s, hdel_s]; exact hdel_ok
        have hd0_s : c.delayed_cap = 0 → sem_s.scratch.delayed = s.scratch.delayed :=
          fun h0 => hdel_s.trans (hd0_sem h0)
        have hnot_s : not_lit.toNat < 2 * sem_s.core.cur_vars := hcore_s ▸ hnot_sem
        s15_head_split
        · -- `ovf = true`: call cold `full_prop_lit_ovf_s15`
          have hovf_t : ovf_v = true := hc
          have hcf_false : confl_v = false := hovf_ncf hovf_t
          have ⟨hoom_s, hct_s⟩ := hcf_f hcf_false
          have hp_sub : (p_v - off0_v).toNat = p_v.toNat - off0_v.toNat :=
            bv64_sub_toNat (by omega)
          have hq_sub : (q_v - off0_v).toNat = q_v.toNat - off0_v.toNat :=
            bv64_sub_toNat (by omega)
          have hsw_ovf : SplitWatchesInv F_cur sem_s.core not_lit.toNat
              (fullWatchOffCore sem_s.core not_lit.toNat)
              (fullWatchOffCore sem_s.core not_lit.toNat + (q_v - off0_v).toNat)
              (fullWatchOffCore sem_s.core not_lit.toNat + (p_v - off0_v).toNat)
              (fullWatchOffCore sem_s.core not_lit.toNat +
                fullWatchSizeCore sem_s.core not_lit.toNat) := by
            have hoff_s := hpi_s.sw.off_eq
            have hsz_s := hpi_s.sw.sz_eq
            rw [hp_sub, hq_sub, hoff_s]
            have h1 : off0_v.toNat + (q_v.toNat - off0_v.toNat) = q_v.toNat := by omega
            have h2 : off0_v.toNat + (p_v.toNat - off0_v.toNat) = p_v.toNat := by omega
            have h3 : off0_v.toNat + fullWatchSizeCore sem_s.core not_lit.toNat = end0_v.toNat := by
              omega
            rw [h1, h2, h3]; exact hpi_s.sw
          s15_head_steps
          c0_call hOvf
          refine ⟨c, F0, F_cur, sem_s, R, dlen, rfl, hpi_s.len, hpi_s.nw,
            hpi_s.dense_eq.trans hdense0, hcore_s ▸ hoom_s, hnot_s, hpi_s.not_f, hsw_ovf,
            hdi_eq, hdlen_le, hdel_ok_s, hm_sync,
            fun ok vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' arena' wstk' wlen' wu'
              ctype' cref' c0' c1' oom' ticks' wsort' phases' m_ovf hlen_o hnw_o htr_o hperm_o
              hcf_o hok_o hm_ovf => ?_⟩
          let st_o : FullState :=
            { sem_s with
              core :=
                { sem_s.core with
                  vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                  trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
                  wvec := wvec', arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                  confl_type := ctype', confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                  oom := oom' }
              scratch :=
                { sem_s.scratch with
                  search_ticks := ticks', wsort := wsort', phases := phases' } }
          have hag_o : AgreesExcept propLitCoreMask s.core st_o.core :=
            hpi_s.ag.update (fun k =>
              { k with
                vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
                wvec := wvec', arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                confl_type := ctype', confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                oom := oom' })
          have htr_so : FullPropDecSpecs.FullTrailExt s.core st_o.core :=
            hpi_s.tr.trans ⟨htr_o.1, htr_o.2.1, htr_o.2.2⟩
          have hperm_so : FullPropDecSpecs.FullArenaPermEq s.core st_o.core :=
            hpi_s.perm.trans ⟨hperm_o.2.1, hperm_o.2.2⟩
          have hsc_o : st_o.scratch = { s.scratch with
              search_ticks := st_o.scratch.search_ticks, wsort := st_o.scratch.wsort,
              phases := st_o.scratch.phases, delayed := st_o.scratch.delayed } := by
            have hs1 := hpi_s.sc_eq; dsimp only [withDel] at hs1
            dsimp only [st_o]; rw [hs1]
          have hd0_o : c.delayed_cap = 0 → st_o.scratch.delayed = s.scratch.delayed := by
            intro h0; dsimp only [st_o]; exact hd0_s h0
          s15_head_steps
          refine hret_st ok st_o m_ovf hlen_o hnw_o hag_o htr_so hperm_so hsc_o hd0_o
            (fun hf => ?_) (fun ht => ?_) hm_ovf
          · rcases hcf_o hf with ho | ⟨hck, hign⟩
            · exact Or.inl ho
            · refine Or.inr ⟨?_, hign⟩
              rcases hck with ⟨h1, h2, h3, h4, h5, h6⟩ | h2
              · exact Or.inl ⟨h1, h2, h3, h6, h4, h5⟩
              · exact Or.inr h2
          · obtain ⟨ho, hc2⟩ := hok_o ht
            exact ⟨ho, hc2.trans (hcore_s ▸ hct_s)⟩
        · -- `ovf = false`: compact tail, fill `0xFFFFFFFFu` sentinels, flush `h->delayed`
          exact s15_raw_compact_flush_wp hPush c.hwcap c.hdel hdense0 hnot_s hpi_s hcore_s
            hdi_eq hdlen_le hdel_ok_s hd0_s hcf_f hcf_t hm_sync hret_st
      · intro Lsync hLsync
        s15_head_steps
        · let sem_s : FullState :=
            { sem with scratch :=
                { sem.scratch with search_ticks := s.scratch.search_ticks + ticks_v } }
          have hpi_s : PropLitInv c F0 F_cur (withDel s sem_s.scratch.delayed) sem_s not_lit.toNat
              off0_v.toNat q_v.toNat p_v.toNat end0_v.toNat :=
            { len := ⟨hpi.len.core_ok, hpi.len.scratch_ok.with_ticks _⟩
              nw := hpi.nw, sw := hpi.sw, ag := hpi.ag, tr := hpi.tr, perm := hpi.perm
              sc_eq := by
                have hs := hpi.sc_eq; dsimp only [sem_s, withDel] at hs ⊢; rw [hs]
              not_f := hpi.not_f }
          have hm_s : (FullMem c sem_s ⋆ R) m := by
            simp only [fastPropMem_search_ticks] at hm
            rw [htend_eq, hunass_eq, hunfl_eq, fastPropMem_sync_eq] at hm
            exact hm
          exact hLsync () m ⟨sem_s, hpi_s, rfl, rfl, hm_s⟩
        · let sem_s : FullState :=
            { sem with scratch := { sem.scratch with search_ticks := s.scratch.search_ticks } }
          have hpi_s : PropLitInv c F0 F_cur (withDel s sem_s.scratch.delayed) sem_s not_lit.toNat
              off0_v.toNat q_v.toNat p_v.toNat end0_v.toNat :=
            { len := ⟨hpi.len.core_ok, hpi.len.scratch_ok.with_ticks _⟩
              nw := hpi.nw, sw := hpi.sw, ag := hpi.ag, tr := hpi.tr, perm := hpi.perm
              sc_eq := by
                have hs := hpi.sc_eq; dsimp only [sem_s, withDel] at hs ⊢; rw [hs]
              not_f := hpi.not_f }
          have hm_s : (FullMem c sem_s ⋆ R) m := by
            rw [htend_eq, hunass_eq, hunfl_eq, fastPropMem_def] at hm
            exact hm
          exact hLsync () m ⟨sem_s, hpi_s, rfl, rfl, hm_s⟩
    · -- Main `while (p < end)` loop body (100% call-free!)
      rintro B L rem ⟨tend_v, unass_v, unfl_v, ticks_v, p_v, q_v, di_v, ovf_v, ⟨⟩⟩ ml hB ih
        ⟨sem, dlen, rfl, rfl, hpi, hdi_eq, hdlen_le, hdel_ok, hd0_sem, htend_eq, hunass_eq,
          hunfl_eq, hnl_eq, hoom_st, hct_st, hml⟩
      clear hnot_xor hidx0 hidx1 hoff0_eq hsz0_eq hsz0_pos hwat0 hnw0 hpi0 hnl_eq0 hnot_f0
        hoff_bd hwlen0_le hoff_idx0 hsz_idx0 hoff_nat hsz_nat hend_nat hvl0 hwv0 hlvl0
        hte0_lt64 hret_noop hret_st hOvf hPush hQ hw0 hm
      let sd : FullState := withDel s sem.scratch.delayed
      have hsd_fpm : ∀ st, fastPropMem sd st = fastPropMem s st := fun st =>
        fastPropMem_s_delayed_irrel s st sem.scratch.delayed
      have hlen0_sd : sd.LengthsOk c :=
        ⟨hlen0.core_ok,
         { hlen0.scratch_ok with delayed_len_arr := hpi.len.scratch_ok.delayed_len_arr }⟩
      have hcv_eq : sem.core.cur_vars = s.core.cur_vars := hpi.cur_vars_eq
      have hnot_st : not_lit.toNat < 2 * sem.core.cur_vars := hcv_eq.symm ▸ hnot_lt
      have ⟨hend_le, hwlen_le⟩ := hpi.end_lt_wcap hnot_st
      have hend_wcap : end0_v.toNat ≤ c.wcap := Nat.le_trans hend_le hwlen_le
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
      s15_head_split
      · have hp_lt : p_v.toNat < end0_v.toNat := by assumption
        have hp_lt_w : p_v.toNat < sem.core.wstk.length :=
          hwstk_len ▸ Nat.lt_of_lt_of_le hp_lt hend_wcap
        have hp_rem_pos : 0 < end0_v.toNat - p_v.toNat := Nat.sub_pos_of_lt hp_lt
        have hp1_nat : (p_v + 1#64).toNat = p_v.toNat + 1 := hp1_pre
        have hq1_nat : (q_v + 1#64).toNat = q_v.toNat + 1 :=
          bv64_add1_toNat (Nat.lt_of_le_of_lt
            (Nat.add_le_add_right (Nat.le_trans hq_le (Nat.le_trans hp_le hend_wcap)) 1) hwc64)
        have hq_lt_ws : q_v.toNat < sem.core.wstk.length :=
          hwstk_len ▸ Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hq_le hp_lt) hend_wcap
        let w0_v := sem.core.wstk[p_v.toNat]'hp_lt_w
        have hw0_get : sem.core.wstk[p_v.toNat]? = some w0_v := List.getElem?_eq_getElem hp_lt_w
        s15_head_steps
        refine wp_join_group (ts := [])
          (fun () m1 => m1 = ml ∧
            ∀ hlt : (w0_v &&& 0x7FFFFFFF#32).toNat < 2 * sem.core.cur_vars,
              (0#32).slt ((sem.core.vals[(w0_v &&& 0x7FFFFFFF#32).toNat]'(fastProp_lt_vals
                hpi.len.core_ok hlt)).signExtend 32) = false)
          ?_ ?_
        · rintro _ ⟨⟩ ml1 ⟨hml1, hblk_nsgt⟩
          subst ml1
          s15_head_split
          · have hflag : (w0_v &&& 0x80000000#32) ≠ 0#32 := by
              simpa only [ne_eq, ← BitVec.ofNat_eq_ofNat, fc_getElem_wstk, fastPropMem_wstk]
                using hc
            obtain ⟨hother_lt, hent, hrem1⟩ :=
              watchSlice_inv_bin hpi.sw.rem_slice hp_rem_pos hw0_get hflag
            have hsw1 := (hpi.sw.advance_rem (p' := p_v.toNat + 1) (Nat.le_succ _) hp_lt
              (by simpa [Nat.sub_sub] using hrem1)).write_bin
              (c := c) hpi.len.core_ok.cur_vars_le hnot_st hq_le hq_lt_ws hflag hother_lt hent
            let other := w0_v &&& 0x7FFFFFFF#32
            let wstk1 := sem.core.wstk.set q_v.toNat w0_v
            let sem1 : FullState := { sem with core := { sem.core with wstk := wstk1 } }
            have hlen1 : sem1.LengthsOk c :=
              ⟨{ hpi.len.core_ok with wstk_len_arr := by simp [sem1, wstk1, hwstk_len] },
               hpi.len.scratch_ok⟩
            have hnw1 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c sem1.core) :=
              fullWitnessInv_nw_congr hlen1.core_ok.cur_vars_le hpi.nw
                rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            have hother_vals1 : (w0_v &&& 2147483647#32).toNat < sem1.core.vals.length :=
              fastProp_lt_vals hlen1.core_ok hother_lt
            have hother_vals0 : (w0_v &&& 2147483647#32).toNat < sem.core.vals.length :=
              fastProp_lt_vals hpi.len.core_ok hother_lt
            have hov_nsgt : (0#32).slt
                ((sem1.core.vals[other.toNat]'hother_vals1).signExtend 32) = false :=
              hblk_nsgt hother_lt
            have hq_lt_mem : q_v.toNat < (fastPropMem s sem).core.wstk.length := by
              rw [fastPropMem_wstk]; exact hq_lt_ws
            have hother_vals_mem : (BitVec.setWidth 64
                ((fastPropMem s sem).core.wstk[p_v.toNat]'(fastPropMem_wstk s sem ▸ hp_lt_w) &&&
                  2147483647)).toNat <
                ({ fastPropMem s sem with core := { (fastPropMem s sem).core with
                  wstk := (fastPropMem s sem).core.wstk.set q_v.toNat
                    ((fastPropMem s sem).core.wstk[p_v.toNat]'(fastPropMem_wstk s sem ▸
                      hp_lt_w)) } }).core.vals.length := by
              dsimp only [w0_v] at hother_vals0
              simp only [bv_c0_zext32_64, fc_getElem_wstk, fastPropMem_vals]
              exact hother_vals0
            s15_head_steps
            · have hge : 2 * s.core.cur_vars ≤ other.toNat := by
                dsimp only [other, w0_v]
                simpa only [← BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt hcv_lt64, Nat.mod_eq_of_lt h2cv_lt64,
                  fc_getElem_wstk, fastPropMem_wstk] using hc
              exact absurd hother_lt (Nat.not_lt.mpr (hcv_eq.symm ▸ hge))
            · have hov_f := propLit_vals_neg hpi.nw hother_lt
                (fastProp_lt_vals hpi.len.core_ok hother_lt)
                (by simpa only [BitVec.ofNat_eq_ofNat, fastPropMem_wstk,
                  fastPropMem_vals] using hc)
              have ⟨hpi_c, hcf_c⟩ := propLit_bin_confl (ignore_ref := ignore_ref) hpi hsw1 hnot_st
                hother_lt hent hov_f hp1_nat hq1_nat
              let sem_c : FullState :=
                { sem with core :=
                    { sem.core with
                      wstk := wstk1, confl_type := 1#64,
                      confl_lit0 := not_lit.setWidth 64, confl_lit1 := other.setWidth 64,
                      confl_ref := 0xFFFFFFFF#64 } }
              exact hB (tend_v, unass_v, unfl_v, ticks_v, p_v + 1#64, q_v + 1#64, di_v,
                true, false, ()) m ⟨sem_c, dlen, hpi_c, hdi_eq, hdlen_le, hdel_ok, hd0_sem,
                htend_eq, hunass_eq, hunfl_eq, by simp, by simp, fun _ => hcf_c,
                by simpa only [sem_c, wstk1, not_lit, other, BitVec.ofNat_eq_ofNat,
                  fastPropMem_wstk, fastPropMem_with_bin_confl_wstk] using hm⟩
            · have hov_un : sem1.core.vals[other.toNat]?.getD 0#8 = 0#8 :=
                propLit_vals_un hnw1 hother_lt hother_vals1 hov_nsgt
                  (by simpa only [other, BitVec.ofNat_eq_ofNat, fastPropMem_wstk,
                    fastPropMem_vals] using hc)
              have hte_lt : sem.core.trail_end < sem.core.cur_vars :=
                hnw1.trail_end_lt_of_unassigned hother_lt hov_un
              have hlen1_mem := fastPropMem_lengthsOk hlen0 hlen1 hcv_eq
                (hpi.ag.get FullCoreState.propagated) rfl
              rw [show ((fastPropMem s sem).core.wstk[p_v.toNat]'(by
                    rw [fastPropMem_wstk]; exact hp_lt_w) &&& (2147483647 : BitVec 32)) =
                  other from by
                rw [show (2147483647 : BitVec 32) = 2147483647#32 from rfl, fc_getElem_wstk]]
              dsimp only
              refine fastProp_assign_wp (k_next := fun tn un uf => .jump L (.var tn,
                (.var un, (.var uf, (.var (ticks_v + 1#64), (.var (p_v + 1#64),
                (.var (q_v + 1#64), (.var di_v, (.var false, ())))))))))
                hmaxv hcv0 hlen1_mem hpi.cur_vars_eq hother_lt hte_lt
                htend_eq (by simpa only [BitVec.ofNat_eq_ofNat, fastPropMem_wstk,
                  fastPropMem_with_wstk] using hm) ?_
              intro flags' ph' unass_n unfl_n m' hfl' hph' hm'
              dsimp only at hm'
              simp only [BitVec.ofNat_eq_ofNat] at hm'
              rw [fastPropMem_assign_eq (te' := sem.core.trail_end + 1)
                (un' := unass_n) (uf' := unfl_n)] at hm'
              have hassign := full_bin_assign_nw_step hlen1.core_ok hnw1 hnot_st hother_lt hov_un
                hpi.not_f hent (flags' := flags') (unas' := unass_n) (unfl' := unfl_n)
              rw [show sem1.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 from hnl_eq]
                at hassign
              have ⟨hlen2, hnw2, hsw2, hag2, htr2, hperm2, hsc2, hnot_f2, hnl2⟩ :=
                fastPropMem_eq_of_eq hpi hsw1 (by simp [hwstk_len]) hfl' hph' hnot_st
                  hother_lt hov_un hnl_eq hassign
              have hmv64 : c.max_vars + 1 < 2 ^ 64 :=
                Nat.lt_trans (Nat.add_lt_add_right hmaxv 1) (by decide)
              have htend_max : tend_v.toNat < c.max_vars := by
                rw [htend_eq]; exact Nat.lt_of_lt_of_le hte_lt hpi.len.core_ok.cur_vars_le
              have ht1_lt : tend_v.toNat + 1 < 2 ^ 64 :=
                Nat.lt_of_le_of_lt (Nat.add_le_add_right (Nat.le_of_lt htend_max) 1) hmv64
              have htend1 : (tend_v + 1#64).toNat = sem.core.trail_end + 1 := by
                rw [BitVec.toNat_add, htend_eq]
                change (sem.core.trail_end + 1) % 2 ^ 64 = sem.core.trail_end + 1
                exact Nat.mod_eq_of_lt (htend_eq ▸ ht1_lt)
              exact ih (end0_v.toNat - (p_v.toNat + 1)) (tend_v + 1#64, unass_n, unfl_n,
                ticks_v + 1#64, p_v + 1#64, q_v + 1#64, di_v, false, ()) m'
                (Nat.sub_lt hp_rem_pos Nat.zero_lt_one)
                ⟨_, dlen, rfl, by rw [hp1_nat],
                  ⟨hlen2, hnw2, (by rw [hp1_nat, hq1_nat]; exact hsw2),
                  hag2, htr2, hperm2, hsc2, hnot_f2⟩, hdi_eq, hdlen_le, hdel_ok, hd0_sem,
                  htend1, rfl, rfl, hnl2, hoom_st, hct_st, hm'⟩
          · have hflag : (w0_v &&& 0x80000000#32) = 0#32 := by
              simpa only [← BitVec.ofNat_eq_ofNat, fc_getElem_wstk, fastPropMem_wstk] using hc
            have ⟨h2le, cref0, hcr_get, hcr_lt, hcr_ref, hrem2⟩ :=
              watchSlice_inv_large hpi.sw.rem_slice hp_rem_pos hw0_get hflag
            s15_head_split
            · have hge : end0_v.toNat ≤ (p_v + (1 : BitVec 64)).toNat := hc
              rw [hp1_pre] at hge
              have h2_le_end : p_v.toNat + 2 ≤ end0_v.toNat :=
                Nat.add_sub_cancel' hp_le ▸ Nat.add_le_add_left h2le p_v.toNat
              exact absurd hge (Nat.not_le.mpr (Nat.lt_of_succ_le h2_le_end))
            · s15_head_split
              · have halen_eq : sem.core.arena_len = s.core.arena_len :=
                  hpi.ag.get FullCoreState.arena_len
                have h2_le_end : p_v.toNat + 2 ≤ end0_v.toNat :=
                  Nat.add_sub_cancel' hp_le ▸ Nat.add_le_add_left h2le p_v.toNat
                have hcr_idx0 : (p_v + 1#64).toNat < sem.core.wstk.length := by
                  rw [hp1_nat, hwstk_len]; exact Nat.lt_of_lt_of_le (by omega) hend_wcap
                have hc_alen : sem.core.arena_len % 2 ^ 64 <
                    ((sem.core.wstk[(p_v + 1#64).toNat]'hcr_idx0).toNat + 3) % 2 ^ 64 := by
                  have hp1_mod : (p_v.toNat + 1) % 2 ^ 64 = (p_v + 1#64).toNat := by
                    rw [hp1_nat]
                    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega)
                      (Nat.lt_trans hwc (by decide)))
                  have hc' := hc
                  simp only [fastPropMem_wstk, BitVec.reduceToNat] at hc'
                  rw [← halen_eq] at hc'
                  simp only [hp1_mod] at hc'
                  exact hc'
                have hcr_eq0 : sem.core.wstk[(p_v + 1#64).toNat]'hcr_idx0 = cref0 := by
                  have h1 : sem.core.wstk[p_v.toNat + 1]? =
                      some (sem.core.wstk[(p_v + 1#64).toNat]'hcr_idx0) := by
                    rw [← hp1_nat]; exact List.getElem?_eq_getElem hcr_idx0
                  exact Option.some.inj (h1.symm.trans hcr_get)
                have hwf0 := hpi.nw.arena.refs_wf cref0.toNat hcr_ref
                have hal_lt64 : sem.core.arena_len < 2 ^ 64 :=
                  Nat.lt_of_le_of_lt hpi.len.core_ok.arena_len_le (Nat.lt_trans har (by decide))
                have hcr3_lt64 : cref0.toNat + 3 < 2 ^ 64 :=
                  Nat.lt_of_le_of_lt hwf0.1 hal_lt64
                rw [hcr_eq0, Nat.mod_eq_of_lt hal_lt64, Nat.mod_eq_of_lt hcr3_lt64] at hc_alen
                exact absurd hc_alen (Nat.not_lt.mpr hwf0.1)
              have h2_le_end : p_v.toNat + 2 ≤ end0_v.toNat :=
                Nat.add_sub_cancel' hp_le ▸ Nat.add_le_add_left h2le p_v.toNat
              have hrem_dec : end0_v.toNat - (p_v.toNat + 2) < end0_v.toNat - p_v.toNat :=
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
              have hcr_idx_mem : (p_v + (1 : BitVec 64)).toNat <
                  (fastPropMem s sem).core.wstk.length := by
                rw [fastPropMem_wstk]; exact hcr_idx_lt
              have hcr_eq :
                  (fastPropMem s sem).core.wstk[(p_v + (1 : BitVec 64)).toNat]'hcr_idx_mem =
                    cref0 := by
                have h1 : sem.core.wstk[p_v.toNat + 1]? =
                    some (sem.core.wstk[(p_v + 1#64).toNat]'hcr_idx_lt) := by
                  rw [← hp1_nat]; exact List.getElem?_eq_getElem hcr_idx_lt
                have h2 := Option.some.inj (h1.symm.trans hcr_get)
                simpa only [fc_getElem_wstk, BitVec.ofNat_eq_ofNat] using h2
              generalize hcr_gen :
                (fastPropMem s sem).core.wstk[(p_v + (1 : BitVec 64)).toNat]'hcr_idx_mem = cref
                at hcr_eq ⊢
              rw [← hcr_eq] at hcr_lt hcr_ref
              have hsw_drop : SplitWatchesInv F_cur sem.core not_lit.toNat off0_v.toNat q_v.toNat
                  (p_v.toNat + 2) end0_v.toNat :=
                hpi.sw.advance_rem (p' := p_v.toNat + 2) (by omega) h2_le_end
                  (by simpa [Nat.sub_sub] using hrem2)
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
              s15_head_steps
              · exact ih _ (tend_v, unass_v, unfl_v, ticks_v + 1#64, p_v + 1#64 + 1#64,
                  q_v, di_v, false, ()) ml hrem_dec
                  ⟨sem, dlen, rfl, by rw [hp2_nat],
                    propLit_inv_drop (ticks' := sem.scratch.search_ticks) hpi hsw_drop hp2_nat,
                    hdi_eq, hdlen_le, hdel_ok, hd0_sem, htend_eq, hunass_eq,
                    hunfl_eq, hnl_eq, hoom_st, hct_st, hml⟩
              · exact ih _ (tend_v, unass_v, unfl_v, ticks_v + 1#64, p_v + 1#64 + 1#64,
                  q_v, di_v, false, ()) ml hrem_dec
                  ⟨sem, dlen, rfl, by rw [hp2_nat],
                    propLit_inv_drop (ticks' := sem.scratch.search_ticks) hpi hsw_drop hp2_nat,
                    hdi_eq, hdlen_le, hdel_ok, hd0_sem, htend_eq, hunass_eq,
                    hunfl_eq, hnl_eq, hoom_st, hct_st, hml⟩
              · exact ih _ (tend_v, unass_v, unfl_v, ticks_v + 1#64, p_v + 1#64 + 1#64,
                  q_v, di_v, false, ()) ml hrem_dec
                  ⟨sem, dlen, rfl, by rw [hp2_nat],
                    propLit_inv_drop (ticks' := sem.scratch.search_ticks) hpi hsw_drop hp2_nat,
                    hdi_eq, hdlen_le, hdel_ok, hd0_sem, htend_eq, hunass_eq,
                    hunfl_eq, hnl_eq, hoom_st, hct_st, hml⟩
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
                    PropLitInv c F0 F_cur sd sem1 not_lit.toNat off0_v.toNat q_v.toNat
                      (p_v.toNat + 2) end0_v.toNat ∧
                    SplitWatchesInv F_cur sem1.core not_lit.toNat off0_v.toNat q_v.toNat
                      p_v.toNat end0_v.toNat ∧
                    sem1.scratch.delayed = sem.scratch.delayed ∧
                    DelayedWatchesOk sem1.core sem1.scratch.delayed dlen not_lit.toNat ∧
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
                · rintro _ ⟨other, ⟨⟩⟩ mj ⟨sem1, hpi1, hsw1_pre, hdel1_eq, hdel1_ok, hoom1, hct1,
                    halen1, hte1_eq, hun1_eq, huf1_eq, hcl1_eq, hnl1, hcr_ref1, hng1, hcsz1,
                    har3, har4, hmj⟩
                  have hd0_1 : c.delayed_cap = 0 → sem1.scratch.delayed = s.scratch.delayed :=
                    fun h0 => hdel1_eq.trans (hd0_sem h0)
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
                  s15_head_steps
                  · have hge : 2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 ≤ other.toNat := hc
                    rw [Nat.mod_eq_of_lt hcv_lt64, Nat.mod_eq_of_lt h2cv_lt64] at hge
                    exact absurd (hcv1_eq ▸ hother_lt) (Nat.not_lt.mpr hge)
                  · let sem_k : FullState :=
                      { sem1 with core := { sem1.core with
                          wstk := (sem1.core.wstk.set q_v.toNat
                            (other &&& 0x7FFFFFFF#32)).set (q_v + 1#64).toNat cref } }
                    exact ih _ (tend_v, unass_v, unfl_v, ticks_v + 1#64,
                        p_v + 1#64 + 1#64, q_v + 2#64, di_v, false, ()) m hrem_dec
                      ⟨sem_k, dlen, rfl, by rw [hp2_nat], by
                          have h := propLit_inv_keep_large hpi1 hpi1.sw hnot_st1 hq1_nat
                            hq2_nat hp2_nat (Nat.add_le_add_right hq_le 2)
                            hpi1.sw.p_le_end (bv32_mask7f_flag0 other) hcr_lt hcr_ref1
                          simpa only [sem_k, sd, hdel1_eq, BitVec.ofNat_eq_ofNat] using h,
                        hdi_eq, hdlen_le, hdel1_ok, hd0_1,
                        htend1_eq, hunass1_eq, hunfl1_eq, hnl1, hoom1, hct1, by
                          simpa only [sem_k, BitVec.ofNat_eq_ofNat, fastPropMem_wstk,
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
                      s15_head_steps
                      have hlen1_mem_sd : (fastPropMem sd sem1).LengthsOk c := by
                        rw [hsd_fpm]; exact hlen1_mem
                      have hmj_sd : (FullMem c (fastPropMem sd sem1) ⋆ R) mj := by
                        rw [hsd_fpm]; exact hmj
                      refine s15_repl_search_wp (s := sd)
                        (nlits := BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat))
                        c.hmaxv c.harena hcv0 ?_ hpi1 hlen1_mem_sd hfit1
                        h3_idx hcsz32_nat hsrch2 hsrch_lt hmj_sd ?_
                      · rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_lt64,
                          Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm, Nat.mod_eq_of_lt h2cv_lt64]
                        rfl
                      · rintro ri_f repl_f _rf hres_f
                        rcases hres_f with ⟨rfl, hfind_bad⟩ | ⟨hri_ne, hr2, hr_lt, hrepl_def, hcand⟩
                        · -- No replacement found: keep watch, conflict or unit assign
                          have hunit := propLit_hunit hpi1.nw hcr_ref1 hng1
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
                              (BitVec.ofNat 64 s.core.cur_level).setWidth 32 =
                                BitVec.ofNat 32 s.core.cur_level := by
                            apply BitVec.eq_of_toNat_eq
                            have hcl64 : s.core.cur_level < 2 ^ 64 :=
                              Nat.lt_trans hclv_lt32 (by decide)
                            rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                              Nat.mod_eq_of_lt hcl64, Nat.mod_eq_of_lt hclv_lt32,
                              BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclv_lt32]
                          have hsw2 := hpi1.sw.write_large hnot_st1 hq_le
                            hq_lt_ws1 hq1_lt_ws1 (bv32_mask7f_flag0 other) hcr_lt hcr_ref1
                          let wstk2 := (sem1.core.wstk.set q_v.toNat
                            (other &&& 0x7FFFFFFF#32)).set (q_v.toNat + 1) cref
                          let sem2 : FullState :=
                            { sem1 with core := { sem1.core with wstk := wstk2 } }
                          have hlen2 : sem2.LengthsOk c :=
                            ⟨{ hpi1.len.core_ok with
                                 wstk_len_arr := by simp [sem2, wstk2, hwstk1] },
                             hpi1.len.scratch_ok⟩
                          have hlen2_mem := fastPropMem_lengthsOk hlen0_sd hlen2 hpi1.cur_vars_eq
                            (hpi1.ag.get FullCoreState.propagated) rfl
                          have hnw2 :
                              FullWitnessInv c F0 F_cur (withEmptyWatchesCore c sem2.core) :=
                            fullWitnessInv_nw_congr hlen2.core_ok.cur_vars_le hpi1.nw
                              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                          have hpi2 : PropLitInv c F0 F_cur sd sem2 not_lit.toNat off0_v.toNat
                              (q_v + 2#64).toNat (p_v.toNat + 2) end0_v.toNat :=
                            { len := hlen2, nw := hnw2, sw := by rw [hq2_nat]; exact hsw2
                              ag := hpi1.ag.update (fun k => { k with wstk := wstk2 })
                              tr := hpi1.tr.congr rfl rfl rfl, perm := hpi1.perm,
                              sc_eq := hpi1.sc_eq, not_f := hpi1.not_f }
                          have hclv_sem2 : sem2.core.cur_level < 2 ^ 32 := by
                            rw [hpi2.ag.get FullCoreState.cur_level]; exact hclv_lt32
                          have hcur_eq2 : (BitVec.ofNat 64 s.core.cur_level).setWidth 32 =
                              BitVec.ofNat 32 sem2.core.cur_level := by
                            rw [hcur_eq1, hpi2.ag.get FullCoreState.cur_level]; rfl
                          s15_head_steps
                          · have hinv2 := propLit_inv_keep_large hpi1 hpi1.sw hnot_st1 hq1_nat
                              hq2_nat hp2_nat (Nat.add_le_add_right hq_le 2) hpi1.sw.p_le_end
                              (bv32_mask7f_flag0 other) hcr_lt hcr_ref1
                            simp only [BitVec.ofNat_eq_ofNat, hp2_nat] at hinv2
                            exact ih _ (tend_v, unass_v, unfl_v, ticks_v + 1#64,
                              p_v + 1#64 + 1#64, q_v + 2#64, di_v, false, ()) m hrem_dec
                              ⟨sem2, dlen, rfl, by rw [hp2_nat], by
                                  have h : PropLitInv c F0 F_cur sd sem2 not_lit.toNat off0_v.toNat
                                      (q_v + 2#64).toNat (p_v + 1#64 + 1#64).toNat end0_v.toNat :=
                                    by rwa [hp2_nat]
                                  simpa only [sd, sem2, hdel1_eq] using h,
                                hdi_eq, hdlen_le, hdel1_ok, hd0_1,
                                htend1_eq, hunass1_eq, hunfl1_eq, hnl1, hoom1, hct1, by
                                  simpa only [sem2, wstk2, BitVec.ofNat_eq_ofNat, hq1_nat,
                                    fastPropMem_wstk, fastPropMem_with_wstk, hsd_fpm] using hm⟩
                          · have hne_ign : cref.setWidth 64 ≠ ignore_ref := by assumption
                            have hov_f := propLit_vals_neg hpi1.nw hother_lt hother_lt1_vals
                              (by simpa only [fastPropMem_vals] using hc)
                            have ⟨hpi_c, hcf_c⟩ := propLit_large_confl hpi1 hnot_st1 hq_le
                              hq1_nat hq2_nat hp2_nat hcr_lt hcr_ref1 hng1 hne_ign hov_f hunit
                            let sem_c : FullState :=
                              { sem1 with core :=
                                  { sem1.core with
                                    wstk := wstk2, confl_type := 2#64,
                                    confl_ref := cref.setWidth 64 } }
                            simp only [BitVec.ofNat_eq_ofNat, hp2_nat] at hpi_c
                            have hm_c : (FullMem c (fastPropMem s sem_c) ⋆ R) m := by
                              simpa only [sem_c, wstk2,
                                show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl,
                                show (1 : BitVec 64) = 1#64 from rfl,
                                show (2 : BitVec 64) = 2#64 from rfl, hq1_nat,
                                fastPropMem_wstk, fastPropMem_with_large_confl_wstk,
                                hsd_fpm] using hm
                            exact hB (tend_v, unass_v, unfl_v, ticks_v + 1#64,
                              p_v + 1#64 + 1#64, q_v + 2#64, di_v, true, false, ()) m
                              ⟨sem_c, dlen, by
                                  have h : PropLitInv c F0 F_cur sd sem_c not_lit.toNat off0_v.toNat
                                      (q_v + 2#64).toNat (p_v + 1#64 + 1#64).toNat end0_v.toNat :=
                                    by simpa only [hq1_nat, hp2_nat, hq2_nat] using hpi_c
                                  simpa only [sd, sem_c, hdel1_eq] using h,
                                hdi_eq, hdlen_le, hdel1_ok, hd0_1,
                                htend1_eq, hunass1_eq, hunfl1_eq, by simp, by simp,
                                fun _ => hcf_c, hm_c⟩
                          · have hov_un := propLit_vals_un hpi1.nw hother_lt hother_lt1_vals
                              hov_np (by simpa only [fastPropMem_vals] using hc)
                            dsimp only
                            have hm2 : (FullMem c (fastPropMem sd sem2) ⋆ R) m := by
                              simpa only [sem2, wstk2,
                                show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl,
                                show (1 : BitVec 64) = 1#64 from rfl,
                                hq1_nat, fastPropMem_wstk, fastPropMem_with_wstk] using hm
                            refine fastProp_large_assign_wp (s := sd)
                              (k_next := fun tn un uf => .jump L
                              (.var tn, (.var un, (.var uf,
                              (.var (ticks_v + 1#64 + 1#64), (.var (p_v + 1#64 + 1#64),
                              (.var (q_v + 2#64), (.var di_v, (.var false, ())))))))))
                              hmaxv har hcv0 hpi2 hlen2_mem hcr_lt
                              hcr_ref1 hng1 hfit1 hother_lt hov_un hnot_st1 hother_mem hnot_mem
                              hunit hnl1 hcur_eq2 hclv_sem2 hcsz32_nat h3_idx htend1_eq hoom1 hct1
                              hm2 ?_
                            intro sem3 tend_n unass_n unfl_n m' hpi3 ht3 hu3 huf3 hnl3 hoom3
                              hct3 hm'
                            have hdel3_eq : sem3.scratch.delayed = sem1.scratch.delayed := by
                              have hs3 := hpi3.sc_eq; dsimp only [sd, withDel] at hs3
                              rw [hs3, hdel1_eq]
                            have hdel3_ok :
                                DelayedWatchesOk sem3.core sem3.scratch.delayed dlen
                                  not_lit.toNat := by
                              rw [hdel3_eq]
                              refine delayedWatchesOk_congr ?_ ?_ hdel1_ok
                              · exact hpi3.cur_vars_eq.trans hcv1_eq.symm
                              · exact hpi3.perm.1.trans hpi1.perm.1.symm
                            exact ih _ (tend_n, unass_n, unfl_n, ticks_v + 1#64 + 1#64,
                              p_v + 1#64 + 1#64, q_v + 2#64, di_v, false, ()) m' hrem_dec
                              ⟨sem3, dlen, rfl, by rw [hp2_nat], by
                                  have h : PropLitInv c F0 F_cur sd sem3 not_lit.toNat off0_v.toNat
                                      (q_v + 2#64).toNat (p_v + 1#64 + 1#64).toNat end0_v.toNat :=
                                    by rwa [hp2_nat]
                                  simpa only [sd, hdel3_eq, hdel1_eq] using h,
                                hdi_eq, hdlen_le, hdel3_ok,
                                fun h0 => hdel3_eq.trans (hd0_1 h0),
                                ht3, hu3, huf3, hnl3, hoom3, hct3, by rwa [hsd_fpm] at hm'⟩
                        · -- Replacement found (`ri_f != 0xFFFFFFFFu`):
                          -- Try (1) in-place sentinel, (2) in-place end, (3) `h->delayed`, (4) ovf
                          have hri_ne : ri_f ≠ 0xFFFFFFFF#32 := hri_ne
                          have hfit1_ar : ∀ {r}, r < fullArenaClauseSizeCore sem1.core cref.toNat →
                              cref.toNat + 3 + r < sem1.core.arena.length := fun hr => by
                            rw [haren1]
                            exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hr _)
                              (Nat.le_trans hfit1 halen1_le)
                          have h3_1_idx : (cref.setWidth 64 + 3#64 + 1#64).toNat =
                              cref.toNat + 4 := by
                            rw [bv64_add_toNat (by
                              rw [h3_idx, ← hcr64, show (1#64).toNat = 1 from rfl]
                              exact hcr_u64), h3_idx]; rfl
                          have h3r_idx : (cref.setWidth 64 + 3#64 + ri_f.setWidth 64).toNat =
                              cref.toNat + 3 + ri_f.toNat := by
                            rw [bv64_add_toNat (by
                              rw [h3_idx, bv_c0_zext32_64]
                              exact Nat.lt_of_lt_of_le (hfit1_ar hr_lt) (Nat.le_trans
                                (Nat.le_of_eq haren1) (Nat.le_of_lt (Nat.lt_trans har
                                  (by decide))))),
                              h3_idx, bv_c0_zext32_64]
                          have hrepl_lt : repl_f.toNat < 2 * sem1.core.cur_vars := hcand.1
                          have ⟨hlt0_r, hlt1_r, hroff_eq, hrsz_eq, _, _, _, _, _, _, _, _⟩ :=
                            s15_repl_idx_bounds c.hwcap c.hdel hpi1.len.core_ok hpi1.sw.layout
                              hrepl_lt hdi_eq hdlen_le
                          have hrepl_lt_wvec0 : (repl_f.setWidth 64 <<< (1 : Nat)).toNat <
                              (fastPropMem s sem1).core.wvec.length := by
                            rw [fastPropMem_wvec]; exact hlt0_r
                          have hrepl_lt_wvec0_bv : (repl_f.setWidth 64 <<< (1 : BitVec 64)).toNat <
                              (fastPropMem s sem1).core.wvec.length := hrepl_lt_wvec0
                          have hrepl_lt_wvec1 :
                              ((repl_f.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat <
                              (fastPropMem s sem1).core.wvec.length := by
                            rw [fastPropMem_wvec]; exact hlt1_r
                          have hrepl_lt_wvec1_bv :
                              ((repl_f.setWidth 64 <<< (1 : BitVec 64)) + (1 : BitVec 64)).toNat <
                              (fastPropMem s sem1).core.wvec.length := hrepl_lt_wvec1
                          clear hmj_sd hlen1_mem_sd
                          s15_head_split
                          · s15_hsteps_nogrp
                            refine s15_raw_repl_install_wp (sem1 := sem1)
                              hB (fun a ml hlt h => ih _ a ml hlt h) hrem_dec c.hwcap c.hdel
                              hpi1 hsw1_pre hdel1_eq hdi_eq hdlen_le hdel1_ok hd0_1
                              htend1_eq hunass1_eq hunfl1_eq hnl1 hoom1 hct1 hnot_st1 hcr_lt
                              hcr_ref1 hcr_lt_alen1 hfit1 har4 hr2 hr_lt hrepl_def hcand hp2_nat
                              h1_idx h3_idx
                              (by
                                rw [BitVec.add_assoc,
                                  show (3#64 : BitVec 64) + 1#64 = 4#64 from rfl]
                                exact h4_idx)
                              h3r_idx ?_ ?_ rfl (by rw [fastPropMem_wlen]) hmj
                            · simpa only [fc_getElem_wvec, BitVec.ofNat_eq_ofNat] using hroff_eq
                            · simpa only [fc_getElem_wvec, BitVec.ofNat_eq_ofNat] using hrsz_eq
                          · exact absurd hc hri_ne
                    · intro Jsrch hJsrch; s15_head_steps
                      · exact hJsrch (2#32, ()) mj
                          ⟨by decide,
                           Nat.lt_of_lt_of_le (by decide : (2#32).toNat < 3) hcsz3_1, rfl⟩
                      · exact hJsrch (2#32, ()) mj
                          ⟨by decide,
                           Nat.lt_of_lt_of_le (by decide : (2#32).toNat < 3) hcsz3_1, rfl⟩
                      · have hcr1_lt_ar1 : cref.toNat + 1 < sem1.core.arena.length := by
                          rw [haren1, ← haren_len]; exact Nat.lt_of_succ_lt hcr2_lt_ar
                        have hcr1_lt64 : cref.toNat + 1 < 2 ^ 64 :=
                          Nat.lt_trans (Nat.add_lt_add_left (by decide) _) (hcr64 ▸ hcr_u64)
                        have hcr2_lt64 : cref.toNat + 2 < 2 ^ 64 :=
                          Nat.lt_trans (Nat.add_lt_add_left (by decide) _) (hcr64 ▸ hcr_u64)
                        have h1_mod : (cref.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 =
                            cref.toNat + 1 := by
                          simp only [BitVec.reduceToNat]; exact Nat.mod_eq_of_lt hcr1_lt64
                        have h2_mod : (cref.toNat + (2 : BitVec 64).toNat) % 2 ^ 64 =
                            cref.toNat + 2 := by
                          simp only [BitVec.reduceToNat]; exact Nat.mod_eq_of_lt hcr2_lt64
                        have hnot_le_srch :
                            ¬ fullArenaClauseSizeCore sem1.core cref.toNat ≤
                              (sem1.core.arena[cref.toNat + 1]'hcr1_lt_ar1).toNat := by
                          have hh : ¬ (sem.core.arena[(cref.toNat + (2 : BitVec 64).toNat) %
                                  2 ^ 64]'(by rw [h2_mod]; exact hcr2_lt_ar)).toNat ≤
                              (sem1.core.arena[(cref.toNat + (1 : BitVec 64).toNat) %
                                  2 ^ 64]'(by rw [h1_mod]; exact hcr1_lt_ar1)).toNat := by
                            simpa only [fc_getElem_arena, fastPropMem_arena] using hc
                          have hcsz_0 : (sem.core.arena[cref.toNat + 2]'hcr2_lt_ar).toNat =
                              fullArenaClauseSizeCore sem1.core cref.toNat := by
                            rw [hcsz1]; unfold fullArenaClauseSizeCore
                            rw [List.getElem?_eq_getElem hcr2_lt_ar, Option.getD_some]
                          simp only [fc_getElem_eq_of_idx h2_mod _ hcr2_lt_ar, hcsz_0,
                            fc_getElem_eq_of_idx h1_mod _ hcr1_lt_ar1] at hh
                          exact hh
                        have h1_mod' : (cref.toNat + 1) % 2 ^ 64 = cref.toNat + 1 :=
                          Nat.mod_eq_of_lt hcr1_lt64
                        have hnot_lt_2 :
                            ¬ (sem1.core.arena[cref.toNat + 1]'hcr1_lt_ar1).toNat < 2 := by
                          have hh : ¬ ((fastPropMem s sem1).core.arena[(cref.toNat +
                                (1 : BitVec 64).toNat) % 2 ^ 64]'(by
                              rw [fastPropMem_arena, h1_mod]; exact hcr1_lt_ar1)).toNat <
                              (2 : BitVec 32).toNat := by assumption
                          simpa only [fc_getElem_arena, fastPropMem_arena, BitVec.reduceToNat,
                            h1_mod'] using hh
                        have hsrch_mem :
                            (fastPropMem s sem1).core.arena[(cref.setWidth 64 + 1).toNat]'(by
                              rw [show (1 : BitVec 64) = 1#64 from rfl, fastPropMem_arena,
                                h1_idx]; exact hcr1_lt_ar1) =
                            sem1.core.arena[cref.toNat + 1]'hcr1_lt_ar1 := by
                          rw [fc_getElem_arena]
                          exact fc_getElem_eq_of_idx
                            (by rw [show (1 : BitVec 64) = 1#64 from rfl]; exact h1_idx) _ _
                        refine hJsrch _ mj
                          ⟨by simpa only [hsrch_mem] using Nat.le_of_not_lt hnot_lt_2,
                           by simpa only [hsrch_mem] using Nat.lt_of_not_le hnot_le_srch, rfl⟩
                · intro J3 hJ3; s15_head_steps
                  · let l1 := sem.core.arena[(cref.setWidth 64 + 4#64).toNat]'(h4_idx ▸ hcr4_lt_ar)
                    have h3_mod : (cref.toNat + BitVec.toNat (3 : BitVec 64)) % 2 ^ 64 =
                        cref.toNat + 3 := by
                      simp only [BitVec.reduceToNat]; exact Nat.mod_eq_of_lt hcr3_lt64
                    have hl0_is_not : sem.core.arena[cref.toNat + 3]'hcr3_lt_ar = not_lit :=
                      (fc_getElem_eq_of_idx h3_mod _ _).symm.trans
                        ((fc_getElem_arena s sem).symm.trans hc)
                    have hpi_drop : PropLitInv c F0 F_cur sd sem not_lit.toNat off0_v.toNat
                        q_v.toNat (p_v.toNat + 2) end0_v.toNat :=
                      ⟨hpi.len, hpi.nw, hsw_drop, hpi.ag, hpi.tr, hpi.perm, hpi.sc_eq,
                       hpi.not_f⟩
                    have ⟨hpi1, href1, hng1, hcsz1, har3, har4⟩ := fastProp_js3_swap hpi_drop
                      hcr_ref hng_t hcsz3 hcr_fit hl0_is_not
                      (fc_getElem_eq_of_idx h4_idx.symm hcr4_lt_ar (h4_idx ▸ hcr4_lt_ar))
                    have href_eq1 :
                        fullArenaClauseRefsCore
                          { sem.core with
                            arena := (sem.core.arena.set (cref.toNat + 3) l1).set
                              (cref.toNat + 4) not_lit } =
                        fullArenaClauseRefsCore sem.core :=
                      hpi1.perm.1.trans hpi.perm.1.symm
                    have hsw1_pre : SplitWatchesInv F_cur
                        { sem.core with
                          arena := (sem.core.arena.set (cref.toNat + 3) l1).set
                            (cref.toNat + 4) not_lit }
                        not_lit.toNat off0_v.toNat q_v.toNat p_v.toNat end0_v.toNat :=
                      hpi.sw.with_nonwatch rfl rfl rfl rfl href_eq1
                    have hdel1_ok : DelayedWatchesOk
                        { sem.core with
                          arena := (sem.core.arena.set (cref.toNat + 3) l1).set
                            (cref.toNat + 4) not_lit }
                        sem.scratch.delayed dlen not_lit.toNat :=
                      delayedWatchesOk_congr (k1 := sem.core) rfl href_eq1 hdel_ok
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
                    exact hJ3 (l1, ()) m ⟨_, hpi1, hsw1_pre, rfl, hdel1_ok, hoom_st, hct_st, rfl,
                      rfl, rfl, rfl, rfl, hnl_eq, href1, hng1, hcsz1, har3, har4, hm1⟩
                  · exact ih _ (tend_v, unass_v, unfl_v, ticks_v + 1#64, p_v + 1#64 + 1#64,
                      q_v, di_v, false, ()) ml hrem_dec
                      ⟨sem, dlen, rfl, by rw [hp2_nat],
                        propLit_inv_drop (ticks' := sem.scratch.search_ticks) hpi hsw_drop hp2_nat,
                        hdi_eq, hdlen_le, hdel_ok, hd0_sem, htend_eq, hunass_eq, hunfl_eq, hnl_eq,
                        hoom_st, hct_st, hml⟩
                  · have h4_mod :
                        (cref.toNat + BitVec.toNat (3 : BitVec 64) + BitVec.toNat (1 : BitVec 64)) %
                          2 ^ 64 = cref.toNat + 4 := by
                      simp only [BitVec.reduceToNat]; exact Nat.mod_eq_of_lt (by omega)
                    have hl1_eq4 : sem.core.arena[cref.toNat + 4]'(hcr4_lt_ar) = not_lit :=
                      (fc_getElem_eq_of_idx h4_mod _ _).symm.trans
                        ((fc_getElem_arena s sem).symm.trans hc)
                    exact hJ3 (_, ()) ml ⟨sem, ⟨hpi.len, hpi.nw, hsw_drop, hpi.ag, hpi.tr,
                        hpi.perm, hpi.sc_eq, hpi.not_f⟩, hpi.sw, rfl, hdel_ok, hoom_st, hct_st,
                      rfl, rfl, rfl, rfl, rfl, hnl_eq, hcr_ref, hng_t, rfl,
                      by rw [fc_getElem_arena, List.getElem?_eq_getElem hcr3_lt_ar]
                         exact congrArg some
                           (fc_getElem_eq_of_idx
                             (by rw [show (3 : BitVec 64) = 3#64 from rfl]; exact h3_idx.symm)
                             hcr3_lt_ar _),
                      by change sem.core.arena[cref.toNat + 4]? = some not_lit
                         rw [← hl1_eq4]; exact List.getElem?_eq_getElem hcr4_lt_ar,
                      hml⟩
        · intro J2 hJ2
          s15_head_split
          · have hblk_lt_2cv : (w0_v &&& 2147483647#32).toNat < 2 * sem.core.cur_vars := by
              rw [hcv_eq]
              have hc' := hc
              simp only [fastPropMem_wstk] at hc'
              rw [Nat.mod_eq_of_lt hcv_lt64, Nat.mod_eq_of_lt h2cv_lt64] at hc'
              exact hc'
            have hblk_vals_lt : (w0_v &&& 2147483647#32).toNat < sem.core.vals.length :=
              fastProp_lt_vals hpi.len.core_ok hblk_lt_2cv
            have hblk_vals_mem : (BitVec.setWidth 64
                ((fastPropMem s sem).core.wstk[p_v.toNat]'(fastPropMem_wstk s sem ▸ hp_lt_w) &&&
                  2147483647)).toNat < (fastPropMem s sem).core.vals.length := by
              dsimp only [w0_v] at hblk_vals_lt
              simp only [bv_c0_zext32_64, fc_getElem_wstk, fastPropMem_vals]
              exact hblk_vals_lt
            s15_head_split
            · s15_head_split
              · have hflag : (w0_v &&& 0x80000000#32) ≠ 0#32 := by
                  simpa only [ne_eq, ← BitVec.ofNat_eq_ofNat, fc_getElem_wstk, fastPropMem_wstk]
                    using hc
                obtain ⟨hother_lt, hent, hrem1⟩ :=
                  watchSlice_inv_bin hpi.sw.rem_slice hp_rem_pos hw0_get hflag
                have hsw1 := (hpi.sw.advance_rem (p' := p_v.toNat + 1) (Nat.le_succ _) hp_lt
                  (by simpa [Nat.sub_sub] using hrem1)).write_bin
                  (c := c) hpi.len.core_ok.cur_vars_le hnot_st hq_le hq_lt_ws hflag hother_lt hent
                let wstk1 := sem.core.wstk.set q_v.toNat w0_v
                let sem1 : FullState := { sem with core := { sem.core with wstk := wstk1 } }
                have hlen1 : sem1.LengthsOk c :=
                  ⟨{ hpi.len.core_ok with wstk_len_arr := by simp [sem1, wstk1, hwstk_len] },
                   hpi.len.scratch_ok⟩
                have hnw1 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c sem1.core) :=
                  fullWitnessInv_nw_congr hlen1.core_ok.cur_vars_le hpi.nw
                    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                have hsw1_rw : SplitWatchesInv F_cur sem1.core not_lit.toNat off0_v.toNat
                    (q_v + 1#64).toNat (p_v.toNat + 1) end0_v.toNat := by
                  rw [hq1_nat]; exact hsw1
                have hpi1 : PropLitInv c F0 F_cur (withDel s sem1.scratch.delayed) sem1
                    not_lit.toNat off0_v.toNat (q_v + 1#64).toNat (p_v + 1#64).toNat
                    end0_v.toNat := by
                  rw [hp1_nat]
                  exact ⟨hlen1, hnw1, hsw1_rw,
                    hpi.ag.update (fun k => { k with wstk := wstk1 }),
                    hpi.tr.congr rfl rfl rfl, hpi.perm, hpi.sc_eq, hpi.not_f⟩
                have hq_lt_mem : q_v.toNat < (fastPropMem s sem).core.wstk.length := by
                  rw [fastPropMem_wstk]; exact hq_lt_ws
                s15_head_steps
                exact ih (end0_v.toNat - (p_v.toNat + 1)) (tend_v, unass_v, unfl_v, ticks_v,
                  p_v + 1#64, q_v + 1#64, di_v, false, ()) m
                  (Nat.sub_lt hp_rem_pos Nat.zero_lt_one)
                  ⟨sem1, dlen, rfl, by rw [hp1_nat], hpi1, hdi_eq, hdlen_le, hdel_ok, hd0_sem,
                    htend_eq, hunass_eq, hunfl_eq, hnl_eq, hoom_st, hct_st, by
                      simpa only [BitVec.ofNat_eq_ofNat, fastPropMem_wstk,
                        fastPropMem_with_wstk] using hm⟩
              · have hflag : (w0_v &&& 0x80000000#32) = 0#32 := by
                  simpa only [← BitVec.ofNat_eq_ofNat, fc_getElem_wstk, fastPropMem_wstk] using hc
                have ⟨h2le, cref0, hcr_get, hcr_lt, hcr_ref, hrem2⟩ :=
                  watchSlice_inv_large hpi.sw.rem_slice hp_rem_pos hw0_get hflag
                s15_head_split
                · have hp1_lt : (p_v + (1 : BitVec 64)).toNat < end0_v.toNat := hc
                  have h2_le_end : p_v.toNat + 2 ≤ end0_v.toNat :=
                    Nat.add_sub_cancel' hp_le ▸ Nat.add_le_add_left h2le p_v.toNat
                  have hp2_wcap : p_v.toNat + 2 ≤ c.wcap := Nat.le_trans h2_le_end hend_wcap
                  have hp2_64 : p_v.toNat + 2 < 2 ^ 64 :=
                    Nat.lt_of_le_of_lt hp2_wcap (Nat.lt_trans hwc (by decide))
                  have hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2 := by
                    rw [bv64_add_toNat (a := p_v + 1#64) (b := 1#64)
                      (by rw [hp1_nat]; exact hp2_64), hp1_nat]; rfl
                  have hq2_nat : (q_v + 2#64).toNat = q_v.toNat + 2 :=
                    bv64_add2_toNat (a := q_v) (Nat.lt_of_le_of_lt
                      (Nat.add_le_add_right (Nat.le_trans hq_le (Nat.le_trans hp_le hend_wcap)) 2)
                      hwc64_2)
                  have hcr_idx_lt : (p_v + 1#64).toNat < sem.core.wstk.length := by
                    rw [hp1_nat, hwstk_len]
                    exact Nat.lt_of_lt_of_le (Nat.lt_of_succ_le h2_le_end) hend_wcap
                  have hcr_eq : sem.core.wstk[(p_v + 1#64).toNat]'hcr_idx_lt = cref0 := by
                    have h1 : sem.core.wstk[p_v.toNat + 1]? =
                        some (sem.core.wstk[(p_v + 1#64).toNat]'hcr_idx_lt) := by
                      rw [← hp1_nat]; exact List.getElem?_eq_getElem hcr_idx_lt
                    exact Option.some.inj (h1.symm.trans hcr_get)
                  have hsw_drop : SplitWatchesInv F_cur sem.core not_lit.toNat off0_v.toNat
                      q_v.toNat (p_v.toNat + 2) end0_v.toNat :=
                    hpi.sw.advance_rem (p' := p_v.toNat + 2) (Nat.le_add_right _ 2) h2_le_end
                      (by simpa [Nat.sub_sub] using hrem2)
                  have hcr_eq_c0 : sem.core.wstk[(p_v + 1).toNat]'(by
                      rw [show (1 : BitVec 64) = 1#64 from rfl]; exact hcr_idx_lt) = cref0 := hcr_eq
                  s15_head_steps
                  exact ih (end0_v.toNat - (p_v.toNat + 2)) (tend_v, unass_v, unfl_v,
                    ticks_v, p_v + 1#64 + 1#64, q_v + 2#64, di_v, false, ()) m
                    (fc_rem2_lt h2_le_end)
                    ⟨_, dlen, rfl, by rw [hp2_nat],
                      propLit_inv_keep_large hpi hsw_drop hnot_st hq1_nat
                      hq2_nat hp2_nat (Nat.add_le_add_right hq_le 2) h2_le_end hflag hcr_lt
                      (hcr_eq ▸ hcr_ref), hdi_eq, hdlen_le, hdel_ok, hd0_sem,
                      htend_eq, hunass_eq, hunfl_eq, hnl_eq, hoom_st, hct_st, by
                        dsimp only [w0_v]
                        simpa only [hq1_nat, hcr_eq_c0, fc_getElem_wstk,
                          fastPropMem_wstk, fastPropMem_with_wstk] using hm⟩
                · have hge : end0_v.toNat ≤ (p_v + (1 : BitVec 64)).toNat := by
                    have hc' : ¬ (p_v.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 < end0_v.toNat := hc
                    rw [show (1 : BitVec 64).toNat = 1 from rfl,
                      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.add_le_add_right hp_le 1)
                        (Nat.lt_of_le_of_lt (Nat.add_le_add_right hend_wcap 1) hwc64)),
                      ← hp1_pre] at hc'
                    exact Nat.not_lt.mp hc'
                  rw [hp1_pre] at hge
                  have h2_le_end : p_v.toNat + 2 ≤ end0_v.toNat :=
                    Nat.add_sub_cancel' hp_le ▸ Nat.add_le_add_left h2le p_v.toNat
                  exact absurd hge (Nat.not_le.mpr (Nat.lt_of_succ_le h2_le_end))
            · s15_head_steps
              exact hJ2 () ml ⟨rfl, fun hlt => by
                dsimp only [w0_v]
                simpa only [← BitVec.ofNat_eq_ofNat, fc_getElem_wstk, fastPropMem_wstk,
                  fc_getElem_vals, fastPropMem_vals] using hc⟩
          · s15_head_steps
            exact hJ2 () ml ⟨rfl, fun hlt => by
              have hc' := hc
              simp only [fastPropMem_wstk] at hc'
              rw [Nat.mod_eq_of_lt hcv_lt64, Nat.mod_eq_of_lt h2cv_lt64] at hc'
              dsimp only [w0_v]
              exact absurd (hcv_eq ▸ hlt) hc'⟩
      · exact hB (tend_v, unass_v, unfl_v, ticks_v, p_v, q_v, di_v, false, false, ()) ml
          ⟨sem, dlen, hpi, hdi_eq, hdlen_le, hdel_ok, hd0_sem, htend_eq, hunass_eq, hunfl_eq,
            by simp, fun _ => ⟨hoom_st, hct_st⟩, by simp, hml⟩
    · intro B L _ hL; s15_head_steps
      have htend0 : (BitVec.ofNat 64 s.core.trail_end).toNat = s.core.trail_end := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hte0_lt64]
      refine hL _ _ m ⟨s, 0, rfl, rfl, ?_, by decide, Nat.zero_le _, fun _ hj => by omega,
        fun _ => rfl, htend0, rfl, rfl, hnl_eq0, hoom0, rfl, ?_⟩
      · rw [hend_nat, hoff_nat]; exact hpi0
      · rw [fastPropMem_self]; exact hm

/-- Exact canonical `Full.fullPropLitSpec` corollary whenever `c.delayed_cap = 0` (`S1.5` never
writes `h->delayed`). -/
theorem full_prop_lit_raw_s15_wp_canon_dcap0 (Γ : Env)
    (hPush : ∀ args m Q X, fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    (hOvf : ∀ args m Q X, fullPropLitOvfS15Spec args m Q X →
      Γ "full_prop_lit_ovf_s15" [i64, i32, i64, i64, i64, i64] [.bool] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {lit : BitVec 32} {ignore_ref : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (hdcap0 : c.delayed_cap = 0)
    (hlen0 : s.LengthsOk c) (hw0 : FullWitnessInv c F0 F_cur s.core)
    (hdense0 : s.core.dense_mode = 0#64) (hoom0 : s.core.oom = 0#64)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' arena' wstk'
      wlen' wu' ctype' cref' c0' c1' oom' ticks' wsort' phases' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                unassigned := unass', unflushed := unfl', wvec := wvec',
                                arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                                confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' }
          scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      (ok = false → oom' ≠ 0#64 ∨
        (FullConflictOkW F_cur s' ∧ (ctype' = 2#64 → cref' ≠ ignore_ref))) →
      (ok = true → oom' = 0#64 ∧ ctype' = s.core.confl_type) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    Func.wp Γ full_prop_lit_raw_s15_body (c.hdr, lit, ignore_ref, ()) m Q X := by
  apply full_prop_lit_raw_s15_wp Γ hPush hOvf
  refine ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hoom0, hm,
    fun ok vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' arena' wstk' wlen' wu'
      ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m' hlen' hw' htr' hperm'
      hd0 hcf hok hm' => ?_⟩
  have hdeq : delayed' = s.scratch.delayed := hd0 hdcap0
  subst hdeq
  exact hQ ok vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' arena' wstk' wlen' wu'
    ctype' cref' c0' c1' oom' ticks' wsort' phases' m' hlen' hw' htr' hperm' hcf hok hm'

/-! ## 2. Outer Propagation Loops (`full_propagate_ignore_s15_wp`, `full_bcp_s15_wp`) -/

theorem full_propagate_ignore_s15_wp (Γ : Env)
    (hPropLit : ∀ args m Q X, fullPropLitS15Spec args m Q X →
      Γ "full_prop_lit_raw_s15" [i64, i32, i64] [.bool] args m Q X) :
    ∀ args m Q X, fullPropagateIgnoreS15Spec args m Q X →
      Func.wp Γ full_propagate_ignore_s15_body args m Q X := by
  rintro ⟨h, ignore_ref, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hm, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hret_st : ∀ (r : BitVec 64) (st : FullState) (ml : Mem 64),
      st.LengthsOk c → FullWitnessInv c F0 F_cur st.core →
      AgreesExcept fastPropCoreMask s.core st.core →
      FullTrailExt s.core st.core → FullArenaPermEq s.core st.core →
      st.core.fuel.toNat ≤ s.core.fuel.toNat →
      st.scratch = { s.scratch with
        search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
        phases := st.scratch.phases, delayed := st.scratch.delayed } →
      (c.delayed_cap = 0 → st.scratch.delayed = s.scratch.delayed) →
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
    intro r st ml hst_l hst_w hag htr hperm hfl hsc hd0 hr hr0 hr1 hr2 hnoop hml
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
            phases := st.scratch.phases, delayed := st.scratch.delayed } } := by
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
      st.scratch.search_ticks st.scratch.wsort st.scratch.phases st.scratch.delayed ml
      hst_l' hst_w' htr' hperm' hd0 hfl hr hr0 ?_ hr2 ?_ hml
    · intro h1; have hcf := hr1 h1; rw [hst_eq] at hcf; exact hcf
    · intro hpe; obtain ⟨h0, heq⟩ := hnoop hpe; exact ⟨h0, hst_eq ▸ heq⟩
  unfold Func.wp full_propagate_ignore_s15_body
  s15_hsteps
  refine wp_loop_group
    (fun rem (prop_v, fuel_v, ()) ml => ∃ memSt : FullState,
      rem = fuel_v.toNat ∧ memSt.LengthsOk c ∧ FullWitnessInv c F0 F_cur memSt.core ∧
      memSt.core.fuel = s.core.fuel ∧ memSt.core.propagated = prop_v.toNat ∧
      AgreesExcept fastPropCoreMask s.core memSt.core ∧
      FullTrailExt s.core memSt.core ∧ FullArenaPermEq s.core memSt.core ∧
      fuel_v.toNat ≤ s.core.fuel.toNat ∧
      memSt.scratch = { s.scratch with
        search_ticks := memSt.scratch.search_ticks, wsort := memSt.scratch.wsort,
        phases := memSt.scratch.phases, delayed := memSt.scratch.delayed } ∧
      (c.delayed_cap = 0 → memSt.scratch.delayed = s.scratch.delayed) ∧
      (s.core.oom = 0#64 → memSt.core.oom = 0#64) ∧
      memSt.core.confl_type = s.core.confl_type ∧
      (fuel_v.toNat = s.core.fuel.toNat →
        { memSt with core := { memSt.core with fuel := fuel_v } } = s) ∧
      (s.core.propagated = s.core.trail_end → memSt = s ∧ fuel_v = s.core.fuel) ∧
      (FullMem c memSt ⋆ R) ml) ?_ ?_
  · rintro L rem ⟨prop_v, fuel_v, ⟨⟩⟩ ml ih
      ⟨memSt, rfl, hml_l, hml_w, hmfuel, hmprop, hag, htr, hperm, hfuel_le, hsc, hd0_m, hoom_pres,
        hct_pres, hsame, hnoop, hml⟩
    have hcl := hml_l.core_ok
    have hcv_le := hcl.cur_vars_le
    have htl := hcl.trl_len; have hte_le := hcl.trail_end_le; have hpr_le := hcl.propagated_le
    have hdm_st : memSt.core.dense_mode = 0#64 := (hag.get FullCoreState.dense_mode).trans hdense0
    s15_hsteps
    · have hpr_lt : prop_v.toNat < memSt.core.trail_end := by c0_bound
      have hne_end : s.core.propagated ≠ s.core.trail_end := fun h => by
        obtain ⟨hm_s, _⟩ := hnoop h; subst hm_s; omega
      let finSt : FullState :=
        { memSt with core := { memSt.core with propagated := prop_v.toNat, fuel := fuel_v } }
      exact hret_st 2#64 finSt m
        ⟨{ hcl with propagated_le := by dsimp [finSt]; omega }, hml_l.scratch_ok⟩
        (hml_w.with_fuel_prop fuel_v prop_v.toNat)
        (hag.update fun k => { k with propagated := prop_v.toNat, fuel := fuel_v })
        (fastTrailExt_congr htr rfl rfl rfl) hperm hfuel_le hsc hd0_m (Or.inr (Or.inr rfl))
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
        (fastTrailExt_congr htr rfl rfl rfl) hperm hfuel_le hsc hd0_m (Or.inr (Or.inr rfl))
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
          ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m2 hlen2 hw2 htr2 hperm2
          hd0_2 hcf hok_t_spec hm2 => ?_⟩
      let memSt2 : FullState :=
        { core :=
            { memSt1.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
              trail_pos := tp', trail_end := te', unassigned := unas', unflushed := unfl',
              wvec := wvec', arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
              confl_type := ctype', confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
              oom := oom' }
          scratch := { memSt1.scratch with
            search_ticks := ticks', wsort := wsort', phases := phases', delayed := delayed' } }
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
          phases := memSt2.scratch.phases, delayed := memSt2.scratch.delayed } := by
        dsimp [memSt2, memSt1]; rw [hsc]
      have hd0_12 : c.delayed_cap = 0 → memSt2.scratch.delayed = s.scratch.delayed :=
        fun h0 => (hd0_2 h0).trans (hd0_m h0)
      have hfl2_lt : (fuel_v - 1#64).toNat < s.core.fuel.toNat := by omega
      s15_hsteps
      · have hok_t : ok = true := by assumption
        exact ih (fuel_v - 1#64).toNat (prop_v + 1#64, fuel_v - 1#64, ()) m2 (by omega)
          ⟨memSt2, rfl, hlen2, hw2, hmfuel, hpr1.symm, hag2, htr12, hperm12, by omega, hsc2,
            hd0_12, fun _ => (hok_t_spec hok_t).1, (hok_t_spec hok_t).2.trans hct_pres,
            fun heq => by omega, fun hpe => absurd hpe hne_end, hm2⟩
      · have hok_f : ok = false := by assumption
        let finSt2 : FullState := { memSt2 with core := { memSt2.core with fuel := fuel_v - 1#64 } }
        exact hret_st 2#64 finSt2 m
          ⟨{ hlen2.core_ok with vals_len := hlen2.core_ok.vals_len }, hlen2.scratch_ok⟩
          (hw2.with_fuel_prop _ _)
          (hag2.update fun k => { k with fuel := fuel_v - 1#64 })
          (fastTrailExt_congr htr12 rfl rfl rfl) hperm12 (by dsimp [finSt2]; omega) hsc2 hd0_12
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
          (fastTrailExt_congr htr12 rfl rfl rfl) hperm12 (by dsimp [finSt2]; omega) hsc2 hd0_12
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
        (fastTrailExt_congr htr rfl rfl rfl) hperm hfuel_le hsc hd0_m (Or.inl rfl)
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
  · intro L hL; s15_hsteps
    have hpr_lt64 : s.core.propagated < 2 ^ 64 := by
      have := hlen0.core_ok.propagated_le; have := hlen0.core_ok.trail_end_le
      have := hlen0.core_ok.cur_vars_le; omega
    exact hL s.core.fuel.toNat (BitVec.ofNat 64 s.core.propagated, s.core.fuel, ()) m
      ⟨s, rfl, hlen0, hw0, rfl, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpr_lt64],
       .refl _ _, ⟨Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl⟩,
       ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, .refl _⟩⟩, Nat.le_refl _, rfl, fun _ => rfl, fun h => h,
       rfl, fun _ => by cases s with | mk sc ssc => cases sc; rfl, fun _ => ⟨rfl, rfl⟩, hm⟩

theorem full_bcp_s15_wp (Γ : Env)
    (hPropIgn : ∀ args m Q X, fullPropagateIgnoreS15Spec args m Q X →
      Γ "full_propagate_ignore_s15" [i64, i64] [i64] args m Q X) :
    ∀ args m Q X, fullBcpS15Spec args m Q X →
      Func.wp Γ full_bcp_s15_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hm, hQ⟩
  unfold Func.wp full_bcp_s15_body
  s15_hsteps
  c0_call hPropIgn
  refine ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hm,
    fun r vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m' hlen' hw' htr' hperm'
      hd0 hfl' hr hr0 hr1 hr2 hnoop hm' => ?_⟩
  s15_hsteps
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m' hlen' hw' htr' hperm'
    hd0 hfl' hr
    (fun h0 => let ⟨hp, _, ho, hf⟩ := hr0 h0; ⟨hp, ho, hf⟩)
    (fun h1 => let ⟨hf, ho, hca, _⟩ := hr1 h1; ⟨hf, ho, hca⟩) hr2 hnoop hm'

/-! ## 3. Canonical `FullSparseInv` Preservation & Level-0 UNSAT Soundness -/

private theorem s15ConflOkW_of_full {F_cur : List (List Nat)} {s : FullState}
    (h : Full.FullConflictOkW F_cur s) : FullPropDecSpecs.FullConflOkW F_cur s.core := by
  rcases h with ⟨ht, h0, h1, hf0, hf1, hent⟩ | hr
  · exact Or.inl ⟨ht, h0, h1, hent, hf0, hf1⟩
  · exact Or.inr hr

theorem full_bcp_s15_preserves_sparseInv {Γ : Env}
    (hPropIgn : ∀ args m Q X, fullPropagateIgnoreS15Spec args m Q X →
      Γ "full_propagate_ignore_s15" [i64, i64] [i64] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hsp : FullPropDecSpecs.FullSparseInv c F0 s) (hm : (FullMem c s ⋆ R) m)
    (Q : Post [i64]) (X : XPost)
    (hpost : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullPropDecSpecs.FullSparseInv c F0 s' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 1#64 → s'.core.cur_level = 0 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    Func.wp Γ full_bcp_s15_body (c.hdr, ()) m Q X := by
  obtain ⟨⟨hlen0, F_cur, hw0⟩, hmk0, hnd0, ⟨hll0, hext0⟩, hdm0⟩ := hsp
  apply full_bcp_s15_wp Γ hPropIgn
  refine ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdm0, hm,
    fun r vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m' hlen' hw' _htr' hperm'
      _hd0 _hfl' hr _hr0 hr1 _hr2 _hnoop hm' => ?_⟩
  let s' : FullState :=
    { core :=
        { s.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', propagated := prop', unassigned := unas',
          unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
          wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
          confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with
        search_ticks := ticks', wsort := wsort', phases := phases', delayed := delayed' } }
  have hperm_sp : FullPropDecSpecs.FullArenaPermEq s.core s'.core :=
    ⟨hperm'.2.1, hperm'.2.2⟩
  have hmk' : FullPropDecSpecs.FullLitMarksClear c s' := hmk0
  have hnd' : FullPropDecSpecs.FullArenaVarsNodup s' := hperm_sp.preserves_varsNodup hnd0
  have hll' : FullPropDecSpecs.FullLastLearnedWf s' :=
    hperm_sp.preserves_lastLearnedWf rfl hll0
  have hsp' : FullPropDecSpecs.FullSparseInv c F0 s' :=
    ⟨⟨hlen', F_cur, hw'⟩, hmk', hnd', ⟨hll', hext0⟩, hdm0⟩
  refine hpost r s' m' hsp' hr (fun h1 hcl0 => ?_) hm'
  exact hw'.level0_unsat_of_conflOkW hcl0 (s15ConflOkW_of_full (hr1 h1).2.2)

/-! ## 4. Closed `ModuleOk` & Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`) -/

/-- Specification table for `m6BcpS15Module` (`4` module functions + extern `full_watch_push`). -/
@[expose] def m6BcpS15SpecTable : List SpecEntry :=
  [ ⟨"full_prop_lit_ovf_s15", [i64, i32, i64, i64, i64, i64], [.bool], fullPropLitOvfS15Spec, true⟩
  , ⟨"full_prop_lit_raw_s15", [i64, i32, i64], [.bool], fullPropLitS15Spec, true⟩
  , ⟨"full_propagate_ignore_s15", [i64, i64], [i64], fullPropagateIgnoreS15Spec, true⟩
  , ⟨"full_bcp_s15", [i64], [i64], fullBcpS15Spec, true⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  ]

/-- Specification environment induced by `m6BcpS15SpecTable`. -/
@[expose] def m6BcpS15Env : Env := Env.ofTable m6BcpS15SpecTable

theorem m6BcpS15SpecTable_noExit : ∀ e ∈ m6BcpS15SpecTable, e.noExit = true := by
  intro e he
  simp only [m6BcpS15SpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem m6BcpS15_noExit :
    ∀ f as bs xs m Q X X', m6BcpS15Env f as bs xs m Q X → m6BcpS15Env f as bs xs m Q X' :=
  Env.ofTable_noExit m6BcpS15SpecTable_noExit

private theorem m6BcpS15SpecTable_nodup : (m6BcpS15SpecTable.map SpecEntry.name).Nodup := by
  show (["full_prop_lit_ovf_s15", "full_prop_lit_raw_s15", "full_propagate_ignore_s15",
    "full_bcp_s15", "full_watch_push"] : List String).Nodup
  decide

private theorem m6BcpS15Env_row_at (i : Nat) (e : SpecEntry)
    (hi : m6BcpS15SpecTable[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → m6BcpS15Env e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) m6BcpS15SpecTable_nodup (hno xs m Q X h)

/-- Row-by-row `TableImpl` for `m6BcpS15_fns` against `m6BcpS15SpecTable`. -/
theorem m6BcpS15_tableImpl : TableImpl m6BcpS15Env m6BcpS15_fns m6BcpS15SpecTable := by
  let hPush := m6BcpS15Env_row_at 4
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  let hOvf := m6BcpS15Env_row_at 0
    ⟨"full_prop_lit_ovf_s15", [i64, i32, i64, i64, i64, i64], [.bool], fullPropLitOvfS15Spec, true⟩
  let hPropLit := m6BcpS15Env_row_at 1
    ⟨"full_prop_lit_raw_s15", [i64, i32, i64], [.bool], fullPropLitS15Spec, true⟩
  let hPropIgn := m6BcpS15Env_row_at 2
    ⟨"full_propagate_ignore_s15", [i64, i64], [i64], fullPropagateIgnoreS15Spec, true⟩
  exact ⟨.of (full_prop_lit_ovf_s15_wp m6BcpS15Env hPush),
    ⟨.of (full_prop_lit_raw_s15_wp m6BcpS15Env hPush hOvf),
    ⟨.of (full_propagate_ignore_s15_wp m6BcpS15Env hPropLit),
    ⟨.of (full_bcp_s15_wp m6BcpS15Env hPropIgn), trivial⟩⟩⟩⟩

/-- Closed unconditional `ModuleOk` for standalone `m6BcpS15Module` under `m6BcpS15Env`. -/
theorem m6BcpS15_moduleOk : ModuleOk m6BcpS15Env m6BcpS15Module :=
  Env.ofTable_moduleOk m6BcpS15_acyclic
    ⟨full_prop_lit_ovf_s15_wf, full_prop_lit_raw_s15_wf,
     full_propagate_ignore_s15_wf, full_bcp_s15_wf, trivial⟩
    m6BcpS15_tableImpl

/-- Concrete `Mem 64` binary-watch UNSAT soundness for `full_bcp_s15_body` under `m6BcpS15Env`
(`XPost := False`): proves non-vacuity and derives `nvOneLitF0.Unsat` on conflict (`r = 1#64`). -/
theorem nv_m6_bcp_s15_sound :
    Func.wp m6BcpS15Env full_bcp_s15_body (nvFastPropCfg.hdr, ()) nvFastPropMem
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) ∧
        (r = 1#64 → Full.nvOneLitF0.Unsat) ∧
        ∃ s', (FullMem nvFastPropCfg s' ⋆ emp) m')
      (fun _ _ _ _ => False) := by
  let hPropIgn := m6BcpS15Env_row_at 2
    ⟨"full_propagate_ignore_s15", [i64, i64], [i64], fullPropagateIgnoreS15Spec, true⟩
  apply full_bcp_s15_wp m6BcpS15Env hPropIgn
  refine ⟨nvFastPropCfg, Full.nvOneLitF0, [[0], [1]], nvFastPropState, emp,
    rfl, nvFastProp_lengths, nvFastProp_witness, rfl,
    by rw [sep_emp]; exact nvFastPropMem_ok, ?_⟩
  intro r _vals' _flags' _lvl' _rsns' _trl' _tp' _te' _prop' _unas' _unfl'
    _wvec' _arena' _wstk' _wlen' _wu' _fuel' _ctype' _cref' _c0' _c1' _oom'
    _ticks' _wsort' _phases' _delayed' m' s' _hlen' hwf' _htr' _hperm' _hd0 _hfl' hr _hr0 hr1
    _hr2 _hnoop hm'
  refine ⟨hr, fun h1 => ?_, _, hm'⟩
  subst h1
  exact hwf'.level0_unsat_of_conflOkW rfl (s15ConflOkW_of_full (hr1 rfl).2.2)

end LeanQbe.T.Examples.Kissat.FullM6BcpS15
