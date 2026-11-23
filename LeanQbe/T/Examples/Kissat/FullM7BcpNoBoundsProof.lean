module

public import LeanQbe.T.Examples.Kissat.FullM7BcpNoBoundsProof0
public import LeanQbe.T.Examples.Kissat.FullFastCoreLemmas

/-!
# Kissat M7 Inner-Bounds-Check-Free BCP `Func.wp`, `ModuleOk`, & Non-Vacuity

Proves:
1. Inner `wp` helpers (`noBoundsLargePush_wp`, `noBoundsLargeNoRepl_wp`).
2. `full_prop_lit_nobounds_m7_wp` (`fullPropLitNoBoundsSpec`): under `FullWatchBoundsInv s`,
   eliminates all per-watch inner bounds checks while preserving `FullSafetySlice`,
   `FullWitnessInv`, and `FullWatchBoundsInv`.
3. `full_propagate_ignore_nobounds_m7_wp` (`fullPropagateIgnoreNoBoundsSpec`),
   `full_bcp_nobounds_m7_wp` (`fullPropagateNoBoundsSpec`), and
   `full_bcp_nobounds_m7_preserves_sparse_watchBounds` (UNSAT soundness + safety only).
4. Closed `m7BcpNoBounds_tableImpl`, `m7BcpNoBounds_moduleOk : ModuleOk m7BcpNoBoundsEnv
   m7BcpNoBoundsModule`, `m7BcpNoBoundsEnv_noExit`, and concrete `nv_m7_bcp_nobounds`
   (`XPost := False`, `Full.nvOneLitF0.Unsat`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds

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
open LeanQbe.T.Examples.Kissat.Full.FullAssignAddTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

attribute [local irreducible] fastPropMem

local macro "nb_hsteps" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps))

local elab "nb_head_steps" : tactic => do
  Lean.Elab.Tactic.evalTactic
    (← `(tactic| try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)))
  fcHeadRun false

local elab "nb_head_split" : tactic => do
  Lean.Elab.Tactic.evalTactic
    (← `(tactic| try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)))
  fcHeadRun true

/-! ## 1. Inner-Bounds-Check-Free Watch-Body `wp` Helpers -/

private theorem bv32_mask7f_toNat_le (x : BitVec 32) : (x &&& 0x7FFFFFFF#32).toNat ≤ x.toNat := by
  rw [BitVec.toNat_and]; exact Nat.and_le_left

private def noBoundsLargePushExpr (h_p cbase pAr pWvec pWstk off_v p2_v q_v end_v : Val i64)
    (ri_f repl_f cref not_lit other w0 : Val i32)
    (k_ok k_oom : Val i64 → Val i64 → Val i64 → Val i64 → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  .let_ (Op.mk (.zext 32 64) (.var cref, ())) fun x166 =>
  .let_ (Op.mk (.add i64) (.var x166.1, (.imm (1 : BitVec 64), ()))) fun x167 =>
  .let_ (Op.mk (.mul i64) (.var x167.1, (.imm (4 : BitVec 64), ()))) fun x168 =>
  .let_ (Op.mk (.add i64) (.var pAr, (.var x168.1, ()))) fun x169 =>
  .store (.var ri_f) (.var x169.1) (
    .let_ (Op.mk (.add i64) (.var cbase, (.imm (1 : BitVec 64), ()))) fun x170 =>
    .let_ (Op.mk (.mul i64) (.var x170.1, (.imm (4 : BitVec 64), ()))) fun x171 =>
    .let_ (Op.mk (.add i64) (.var pAr, (.var x171.1, ()))) fun x172 =>
    .store (.var repl_f) (.var x172.1) (
      .let_ (Op.mk (.zext 32 64) (.var ri_f, ())) fun x173 =>
      .let_ (Op.mk (.add i64) (.var cbase, (.var x173.1, ()))) fun x174 =>
      .let_ (Op.mk (.mul i64) (.var x174.1, (.imm (4 : BitVec 64), ()))) fun x175 =>
      .let_ (Op.mk (.add i64) (.var pAr, (.var x175.1, ()))) fun x176 =>
      .store (.var not_lit) (.var x176.1) (
        .let_ (Op.mk (.sub i64) (.var p2_v, (.var off_v, ()))) fun x177 =>
        .let_ (Op.mk (.sub i64) (.var q_v, (.var off_v, ()))) fun x178 =>
        .let_ (Op.mk (.sub i64) (.var end_v, (.var off_v, ()))) fun x179 =>
        .let_ (Op.mk (.and i32) (.var other, (.imm (2147483647 : BitVec 32), ()))) fun x180 =>
        .call "full_watch_push" (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
          (.var h_p, (.var repl_f, (.var x180.1, (.var cref, (.imm (2 : BitVec 32), ())))))
          fun x181 =>
        .let_ (Op.mk (.zext 32 64) (.var not_lit, ())) fun x182 =>
        .let_ (Op.mk (.sext 32 64) (.imm (1 : BitVec 32), ())) fun x183 =>
        .let_ (Op.mk (.shl i64) (.var x182.1, (.var x183.1, ()))) fun x184 =>
        .let_ (Op.mk (.mul i64) (.var x184.1, (.imm (4 : BitVec 64), ()))) fun x185 =>
        .let_ (Op.mk (.add i64) (.var pWvec, (.var x185.1, ()))) fun x186 =>
        .load i32 (.var x186.1) fun x187 =>
        .let_ (Op.mk (.zext 32 64) (.var x187, ())) fun x188 =>
        .let_ (Op.mk (.add i64) (.var x188.1, (.var x177.1, ()))) fun x189 =>
        .let_ (Op.mk (.add i64) (.var x188.1, (.var x178.1, ()))) fun x190 =>
        .let_ (Op.mk (.add i64) (.var x188.1, (.var x179.1, ()))) fun x191 =>
        .jnz (.var x181.1)
          (k_ok x188.1 x189.1 x190.1 x191.1) (
          .let_ (Op.mk (.add i64) (.var cbase, (.imm (1 : BitVec 64), ()))) fun x192 =>
          .let_ (Op.mk (.mul i64) (.var x192.1, (.imm (4 : BitVec 64), ()))) fun x193 =>
          .let_ (Op.mk (.add i64) (.var pAr, (.var x193.1, ()))) fun x194 =>
          .store (.var not_lit) (.var x194.1) (
            .let_ (Op.mk (.zext 32 64) (.var ri_f, ())) fun x195 =>
            .let_ (Op.mk (.add i64) (.var cbase, (.var x195.1, ()))) fun x196 =>
            .let_ (Op.mk (.mul i64) (.var x196.1, (.imm (4 : BitVec 64), ()))) fun x197 =>
            .let_ (Op.mk (.add i64) (.var pAr, (.var x197.1, ()))) fun x198 =>
            .store (.var repl_f) (.var x198.1) (
              .let_ (Op.mk (.mul i64) (.var x190.1, (.imm (4 : BitVec 64), ()))) fun x199 =>
              .let_ (Op.mk (.add i64) (.var pWstk, (.var x199.1, ()))) fun x200 =>
              .store (.var w0) (.var x200.1) (
                .let_ (Op.mk (.add i64) (.var x190.1, (.imm (1 : BitVec 64), ()))) fun x201 =>
                .let_ (Op.mk (.mul i64) (.var x201.1, (.imm (4 : BitVec 64), ()))) fun x202 =>
                .let_ (Op.mk (.add i64) (.var pWstk, (.var x202.1, ()))) fun x203 =>
                .store (.var cref) (.var x203.1) (
                  .let_ (Op.mk (.add i64) (.var x190.1, (.imm (2 : BitVec 64), ()))) fun x204 =>
                  .let_ (Op.mk (.add i64) (.var h_p, (.imm (760 : BitVec 64), ()))) fun x205 =>
                  .store (t := i64) (.imm (1 : BitVec 64)) (.var x205.1)
                    (k_oom x188.1 x189.1 x204.1 x191.1)
                )
              )
            )
          )
        )
      )
    )
  )

private theorem noBoundsLargePush_wp {Γ : Env}
    (hPush : ∀ args m Q X, Full.fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s sem1 : FullState}
    {not_lit w0 other cref ri_f repl_f : BitVec 32}
    {off_v p_v q_v end_v tend_v unass_v unfl_v : BitVec 64}
    {nl_lvl0 : BitVec 32} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    {k_ok k_oom : Val i64 → Val i64 → Val i64 → Val i64 → Expr Val Cont [.bool]}
    (_hmaxv : c.max_vars < 2 * dimacsBound) (har : c.arena_cap < 2 * dimacsBound)
    (hlen0 : s.LengthsOk c) (_hcv0 : s.core.cur_vars ≤ c.max_vars)
    (hnb1 : PropLitNoBoundsInv c F0 F_cur s sem1 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hlen1_mem : (fastPropMem s sem1).LengthsOk c)
    (hcr_lt : cref.toNat < 0x80000000)
    (hcr_ref1 : cref.toNat ∈ fullArenaClauseRefsCore sem1.core)
    (hfit1 : cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤ sem1.core.arena_len)
    (har4 : sem1.core.arena[cref.toNat + 4]? = some not_lit)
    (hnot_st1 : not_lit.toNat < 2 * sem1.core.cur_vars)
    (hother_lt : other.toNat < 2 * sem1.core.cur_vars)
    (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hw0_blk : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * sem1.core.cur_vars)
    (hr2 : 2 ≤ ri_f.toNat) (hr_lt : ri_f.toNat < fullArenaClauseSizeCore sem1.core cref.toNat)
    (hrepl_def : repl_f = sem1.core.arena[cref.toNat + 3 + ri_f.toNat]'(by
      rw [hnb1.prop.len.core_ok.arena_len_arr]
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hr_lt _)
        (Nat.le_trans hfit1 hnb1.prop.len.core_ok.arena_len_le)))
    (hcand : repl_f.toNat < 2 * sem1.core.cur_vars ∧
      ((sem1.core.vals[repl_f.toNat]?.getD 0#8).signExtend 32).slt 0#32 = false)
    (h1_idx : (cref.setWidth 64 + 1#64).toNat = cref.toNat + 1)
    (h3_idx : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3)
    (h4_idx : (cref.setWidth 64 + 3#64 + 1#64).toNat = cref.toNat + 4)
    (htend1_eq : tend_v.toNat = sem1.core.trail_end) (hunass1_eq : unass_v = sem1.core.unassigned)
    (hunfl1_eq : unfl_v = sem1.core.unflushed)
    (hnl1 : sem1.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0)
    (hoom1 : sem1.core.oom = 0#64) (hct1 : sem1.core.confl_type = s.core.confl_type)
    (hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2) (hq_le : q_v.toNat ≤ p_v.toNat)
    (hq_lt : q_v.toNat < c.wcap)
    (hm : (FullMem c (fastPropMem s sem1) ⋆ R) m)
    (hk_ok : ∀ (st4 : FullState) (off4_v : BitVec 64) (m_p : Mem 64),
      (off4_v + (end_v - off_v)).toNat -
        (off4_v + (p_v + 1#64 + 1#64 - off_v)).toNat < end_v.toNat - p_v.toNat →
      PropLitNoBoundsInv c F0 F_cur s st4 not_lit.toNat off4_v.toNat
        (off4_v + (q_v - off_v)).toNat (off4_v + (p_v + 1#64 + 1#64 - off_v)).toNat
        (off4_v + (end_v - off_v)).toNat →
      tend_v.toNat = st4.core.trail_end → unass_v = st4.core.unassigned →
      unfl_v = st4.core.unflushed → st4.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 →
      st4.core.oom = 0#64 → st4.core.confl_type = s.core.confl_type →
      (FullMem c (fastPropMem s st4) ⋆ R) m_p →
      wp Γ Q X (k_ok off4_v (off4_v + (p_v + 1#64 + 1#64 - off_v)) (off4_v + (q_v - off_v))
        (off4_v + (end_v - off_v))) m_p)
    (hk_oom : ∀ (st6 : FullState) (off4_v : BitVec 64) (m_f : Mem 64),
      PropLitNoBoundsInv c F0 F_cur s st6 not_lit.toNat off4_v.toNat
        (off4_v + (q_v - off_v) + 2#64).toNat (off4_v + (p_v + 1#64 + 1#64 - off_v)).toNat
        (off4_v + (end_v - off_v)).toNat →
      tend_v.toNat = st6.core.trail_end → unass_v = st6.core.unassigned →
      unfl_v = st6.core.unflushed → st6.core.oom ≠ 0#64 →
      (FullMem c (fastPropMem s st6) ⋆ R) m_f →
      wp Γ Q X (k_oom off4_v (off4_v + (p_v + 1#64 + 1#64 - off_v))
        (off4_v + (q_v - off_v) + 2#64) (off4_v + (end_v - off_v))) m_f) :
    wp Γ Q X (noBoundsLargePushExpr c.hdr (cref.setWidth 64 + 3#64) c.pArena c.pWvec c.pWstk
      off_v (p_v + 1#64 + 1#64) q_v end_v ri_f repl_f cref not_lit other w0 k_ok k_oom) m := by
  have hpi1 := hnb1.prop
  unfold dimacsBound at har
  have haren1 := hpi1.len.core_ok.arena_len_arr
  have halen1_le := hpi1.len.core_ok.arena_len_le
  have _hm1_aren := hlen1_mem.core_ok.arena_len_arr
  have _hm1_wvec := hlen1_mem.core_ok.wvec_len
  have hfit1_ar : ∀ {r}, r < fullArenaClauseSizeCore sem1.core cref.toNat →
      cref.toNat + 3 + r < sem1.core.arena.length := fun hr => by
    rw [haren1]; exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hr _) (Nat.le_trans hfit1 halen1_le)
  have h3r_idx : (cref.setWidth 64 + 3#64 + ri_f.setWidth 64).toNat =
      cref.toNat + 3 + ri_f.toNat := by
    rw [bv64_add_toNat (by
      rw [h3_idx, bv_c0_zext32_64]
      exact Nat.lt_of_lt_of_le (hfit1_ar hr_lt) (Nat.le_trans
        (Nat.le_of_eq haren1) (Nat.le_of_lt (Nat.lt_trans har (by decide))))),
      h3_idx, bv_c0_zext32_64]
  have h1_lt_ar : cref.toNat + 1 < c.arena_cap := by
    have := Nat.lt_of_lt_of_le (hfit1_ar hr_lt) (Nat.le_of_eq haren1); omega
  have h4_lt_ar : cref.toNat + 4 < c.arena_cap := by
    have := Nat.lt_of_lt_of_le (hfit1_ar hr_lt) (Nat.le_of_eq haren1); omega
  have h3r_lt_ar : cref.toNat + 3 + ri_f.toNat < c.arena_cap :=
    Nat.lt_of_lt_of_le (hfit1_ar hr_lt) (Nat.le_of_eq haren1)
  have hcr_lt_alen1 : cref.toNat < sem1.core.arena_len := by omega
  unfold noBoundsLargePushExpr
  nb_head_steps
  let st3 : FullState :=
    { sem1 with core := { sem1.core with
        arena := ((sem1.core.arena.set (cref.toNat + 1) (BitVec.ofNat 32 ri_f.toNat)).set
          (cref.toNat + 4) repl_f).set (cref.toNat + 3 + ri_f.toNat) not_lit } }
  have h3r_ne1 : cref.toNat + 1 ≠ cref.toNat + 3 + ri_f.toNat := by omega
  have hrepl_set1 : repl_f = (sem1.core.arena.set (cref.toNat + 1)
      (BitVec.ofNat 32 ri_f.toNat))[cref.toNat + 3 + ri_f.toNat]'(by simp [hfit1_ar hr_lt]) := by
    rw [List.getElem_set_ne h3r_ne1]; exact hrepl_def
  have ⟨hlen3, hnw3, hsw3, hperm13, hcr_ref3, hcsz3, hrepl_lt,
      hrepl_ne_not, hw0_ne_ff, hcr_ne_ff⟩ :=
    fastProp_b1_swap (other := other) (r := ri_f.toNat) hpi1 hcr_lt_alen1
      hcr_ref1 hfit1 har4 hr2 hr_lt hrepl_set1
      (by simpa only [List.getElem?_eq_getElem (hfit1_ar hr_lt), Option.getD_some,
        ← hrepl_def] using hcand)
  have har_len3 : st3.core.arena_len ≤ st3.core.arena.length :=
    Nat.le_trans hlen3.core_ok.arena_len_le (Nat.le_of_eq hlen3.core_ok.arena_len_arr.symm)
  have hsb3 : SplitWatchBoundsInv st3.core not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat :=
    hnb1.sb.reconstruct_of_nw_arenaInv hsw3 hnw3.arena har_len3 rfl rfl rfl
  have hri32 : BitVec.setWidth 32 ri_f = ri_f := by apply BitVec.eq_of_toNat_eq; simp
  have hm3 : (FullMem c (fastPropMem s st3) ⋆ R) m := by
    simpa only [st3, fastPropMem_arena, BitVec.ofNat_eq_ofNat, BitVec.ofNat_toNat, hri32,
      h1_idx, h4_idx, h3r_idx, fastPropMem_with_arena] using hm
  c0_call hPush
  refine ⟨c, fastPropMem s st3, R, rfl,
    fastPropMem_lengthsOk hlen0 hlen3 (hpi1.ag.get FullCoreState.cur_vars)
      (hpi1.ag.get FullCoreState.propagated) rfl,
    fastPropMem_watchLayout hsw3.layout rfl,
    fun h => absurd h (by decide), fun _ => ⟨hw0_ne_ff, hcr_ne_ff⟩,
    hm3, fun pok wvec' wstk' wlen' wu' wsort' m_p hlen_p hlay_p hpres_o
      hpok_t hpok_f hm_p => ?_⟩
  let st4 : FullState :=
    { st3 with
      core := { st3.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
      scratch := { st3.scratch with wsort := wsort' } }
  have hs4_eq :
      { fastPropMem s st3 with
        core := { (fastPropMem s st3).core with
          wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
        scratch := { (fastPropMem s st3).scratch with wsort := wsort' } } =
      fastPropMem s st4 :=
    fastPropMem_with_push_rec s st3 wvec' wstk' wlen' wu' wsort'
  rw [hs4_eq] at hpres_o hpok_t hpok_f hm_p
  unfold fullWatchSize fullWatchOff at hpres_o hpok_t hpok_f
  simp only [fastPropMem_watchSize, fastPropMem_watchOff, fastPropMem_wstk,
    fastPropMem_cur_vars] at hpres_o hpok_t hpok_f
  have hlen4 : st4.LengthsOk c :=
    ⟨{ hlen3.core_ok with
        wvec_len := by simpa only [st4, fastPropMem_wvec] using hlen_p.core_ok.wvec_len
        wstk_len_arr := by
          simpa only [st4, fastPropMem_wstk] using hlen_p.core_ok.wstk_len_arr
        wlen_le := by simpa only [st4, fastPropMem_wlen] using hlen_p.core_ok.wlen_le },
     { hlen3.scratch_ok with
        wsort_len := by simpa only [st4, fastPropMem_wsort] using hlen_p.scratch_ok.wsort_len }⟩
  have hnw4 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st4.core) :=
    Full.fullWitnessInv_nw_congr hlen4.core_ok.cur_vars_le hnw3
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hst4_alen := hlen4.core_ok.arena_len_arr
  have hwvec'_len := hlen4.core_ok.wvec_len
  have hwstk'_len := hlen4.core_ok.wstk_len_arr
  have hidx0_nat : (not_lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * not_lit.toNat :=
    fc_bv64_shl1_u32_nat not_lit
  have hnl_eq_xor : (not_lit ^^^ 1#32) ^^^ 1#32 = not_lit := by
    rw [BitVec.xor_assoc, show (1#32 ^^^ 1#32 : BitVec 32) = 0#32 from by decide,
      BitVec.xor_zero]
  have hlay4 : WatchStackLayout st4.core :=
    hlay_p.with_wstk (by dsimp only [st4]; exact (fastPropMem_cur_vars s st3).symm) rfl rfl rfl
  have ⟨hoff4_bd, hoff4_nat, hp4_nat, hq4_nat, hend4_nat, hq4_1, hq4_2,
      hsw4'⟩ := Full.propLit_b1_after_push (c := c) (F_cur := F_cur) (lit := not_lit ^^^ 1#32)
    (st3 := st3) (st4 := st4) (other := other) (pok := pok) (off_v := off_v) (p_v := p_v)
    (q_v := q_v) (end_v := end_v) (idx0 := (not_lit.setWidth 64 <<< (1 : Nat)).toNat)
    (by rw [hidx0_nat, hnl_eq_xor]) rfl
    (by rw [hnl_eq_xor]; exact hnot_st1) hlen4 hlay4
    (by rw [hnl_eq_xor]; exact hsw3) rfl hrepl_lt
    (by rw [hnl_eq_xor]; exact hrepl_ne_not) hcr_lt hcr_ref3 hp2_nat hq_le
    (fun l hl hne => hpres_o l hl hne)
    (fun ht => let ⟨_, _, hsz, hpre, hw0, hw1⟩ := hpok_t ht; ⟨hsz, hpre, hw0, hw1 rfl⟩)
    (fun hf => (hpok_f hf).1 hrepl_lt)
  simp only [hnl_eq_xor] at hoff4_bd hoff4_nat hp4_nat hq4_nat hend4_nat hsw4'
  have hnot_max4 : not_lit.toNat < 2 * c.max_vars :=
    Nat.lt_of_lt_of_le hnot_st1 (Nat.mul_le_mul_left 2 hlen4.core_ok.cur_vars_le)
  have hidx0_lt4 : (not_lit.setWidth 64 <<< (1 : Nat)).toNat < st4.core.wvec.length := by
    rw [hidx0_nat, hwvec'_len, show 4 * c.max_vars = 2 * (2 * c.max_vars) from by omega]
    exact Nat.mul_lt_mul_of_pos_left hnot_max4 (by decide)
  have hm4_mem_len := fastPropMem_lengthsOk hlen0 hlen4
    (by dsimp [st4, st3]; exact hpi1.cur_vars_eq)
    (by dsimp [st4, st3]; exact hpi1.ag.get FullCoreState.propagated) rfl
  have hm4_wvec := hm4_mem_len.core_ok.wvec_len
  let off4_v : BitVec 64 := (st4.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'
    hidx0_lt4).setWidth 64
  let q4_v := off4_v + (q_v - off_v)
  have hq4_lt_c : q4_v.toNat < c.wcap := by
    rw [hq4_nat]; have := hoff4_bd; have := hpi1.sw.q_ge; have := hpi1.sw.p_le_end
    have := hlen4.core_ok.wlen_le; omega
  have hq4_1_lt_c : (q4_v + (1 : BitVec 64)).toNat < c.wcap := by
    rw [hq4_1, hq4_nat]; have := hoff4_bd; have := hpi1.sw.q_ge; have := hpi1.sw.p_le_end
    have := hlen4.core_ok.wlen_le; omega
  have hidx0_lt4_m :
      (not_lit.setWidth 64 <<< (1 : Nat)).toNat < (fastPropMem s st4).core.wvec.length := by
    rw [hm4_wvec, hidx0_nat]; omega
  have hoff4_mem_eq :
      ((fastPropMem s st4).core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'
        hidx0_lt4_m).setWidth 64 = off4_v :=
    congrArg (BitVec.setWidth 64) (fc_getElem_wvec s st4)
  have hq4_mem_lt_c :
      (BitVec.setWidth 64 ((fastPropMem s st4).core.wvec[
        (not_lit.setWidth 64 <<< (1 : Nat)).toNat]'hidx0_lt4_m) + (q_v - off_v)).toNat <
        c.wcap := by
    rw [hoff4_mem_eq]; exact hq4_lt_c
  have hq4_1_mem_lt_c :
      (BitVec.setWidth 64 ((fastPropMem s st4).core.wvec[
        (not_lit.setWidth 64 <<< (1 : Nat)).toNat]'hidx0_lt4_m) + (q_v - off_v) +
        (1 : BitVec 64)).toNat < c.wcap := by
    rw [hoff4_mem_eq]; exact hq4_1_lt_c
  have hidx0_lt4_2 : 2 * not_lit.toNat < st4.core.wvec.length := by
    rw [← hidx0_nat]; exact hidx0_lt4
  have hoff4_eq_2 :
      (st4.core.wvec[2 * not_lit.toNat]'hidx0_lt4_2).setWidth 64 = off4_v :=
    congrArg (BitVec.setWidth 64) (fc_getElem_eq_of_idx hidx0_nat hidx0_lt4 hidx0_lt4_2).symm
  have hq4_2_lt_c :
      (BitVec.setWidth 64 (st4.core.wvec[2 * not_lit.toNat]'hidx0_lt4_2) +
        (q_v - off_v)).toNat < c.wcap := by
    rw [hoff4_eq_2]; exact hq4_lt_c
  have hq4_1_2_lt_c :
      (BitVec.setWidth 64 (st4.core.wvec[2 * not_lit.toNat]'hidx0_lt4_2) +
        (q_v - off_v) + (1 : BitVec 64)).toNat < c.wcap := by
    rw [hoff4_eq_2]; exact hq4_1_lt_c
  have hag4 : AgreesExcept Full.propLitCoreMask s.core st4.core :=
    hpi1.ag.update (fun k => { k with
      arena := st4.core.arena, wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' })
  have hperm4 : Full.FullPropDecSpecs.FullArenaPermEq s.core st4.core := hpi1.perm.trans hperm13
  have hsc4 : st4.scratch = { s.scratch with
      search_ticks := st4.scratch.search_ticks, wsort := st4.scratch.wsort,
      phases := st4.scratch.phases } := by
    dsimp only [st4, st3]; rw [hpi1.sc_eq]
  have hnl4 : st4.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 := hnl1
  have hm4_aren := hm4_mem_len.core_ok.arena_len_arr
  have hm4_wstk := hm4_mem_len.core_ok.wstk_len_arr
  have hwf3 := hnw3.arena.refs_wf cref.toNat hcr_ref3
  have hsb4_raw := hsb3.after_push (k' := st4.core)
    (w0 := other &&& 0x7FFFFFFF#32) (cref := cref) (pok := pok)
    hsw3.off_eq.symm
    (by have hsz3 : fullWatchSizeCore st3.core not_lit.toNat = end_v.toNat - off_v.toNat :=
          hsw3.sz_eq
        have hq_ge3 := hsw3.q_ge; have hp_le3 := hsw3.p_le_end; have hqp3 := hsw3.q_le_p
        omega)
    hsw3.q_ge (by omega) hsw3.p_le_end rfl rfl rfl hnot_st1 hrepl_lt
    (fun heq => hrepl_ne_not (by rw [← heq]))
    (Full.bv32_mask7f_flag0 other)
    (Nat.lt_of_le_of_lt (bv32_mask7f_toNat_le (other &&& 0x7FFFFFFF#32))
      (Nat.lt_of_le_of_lt (bv32_mask7f_toNat_le other) hother_lt))
    hcr_lt (Nat.le_trans (by decide : 2 ≤ 3) hwf3.2.1) (Nat.le_trans hwf3.2.2.1 hwf3.2.2.2.1)
    (fullArenaLiveLitsLt_of_nw_arenaInv hnw3.arena har_len3 hcr_ref3)
    (fun l hl hne => hpres_o l hl hne)
    (fun ht => let ⟨_, _, hsz, hpre, hw0, hw1⟩ := hpok_t ht; ⟨hsz, hpre, hw0, hw1 rfl⟩)
    (fun hf => (hpok_f hf).1 hrepl_lt)
  have hsb4 : SplitWatchBoundsInv st4.core not_lit.toNat off4_v.toNat
      (off4_v + (q_v - off_v)).toNat (off4_v + (p_v + 1#64 + 1#64 - off_v)).toNat
      (off4_v + (end_v - off_v)).toNat := by
    rw [hoff4_nat, hq4_nat, show (off4_v + (p_v + 1#64 + 1#64 - off_v)).toNat =
        fullWatchOffCore st4.core not_lit.toNat + (p_v.toNat + 2 - off_v.toNat) by
      simpa only [BitVec.ofNat_eq_ofNat] using hp4_nat, hend4_nat]
    exact hsb4_raw
  nb_head_steps
  · dsimp only
    simp only [hoff4_mem_eq]
    exact hk_ok st4 off4_v m_p (by
      have he4 : (off4_v + (end_v - off_v)).toNat =
          fullWatchOffCore st4.core not_lit.toNat + (end_v.toNat - off_v.toNat) := hend4_nat
      have hp4 : (off4_v + (p_v + 1#64 + 1#64 - off_v)).toNat =
          fullWatchOffCore st4.core not_lit.toNat + (p_v.toNat + 2 - off_v.toNat) := by
        simpa only [BitVec.ofNat_eq_ofNat] using hp4_nat
      rw [he4, hp4]
      exact Full.propLit_measure_lt (Nat.le_trans hpi1.sw.q_ge hq_le) hpi1.sw.p_le_end)
      ⟨⟨hlen4, hnw4, hsw4', hag4, hpi1.tr.congr rfl rfl rfl, hperm4, hsc4, hpi1.not_f⟩, hsb4⟩
      htend1_eq hunass1_eq hunfl1_eq hnl4 hoom1 hct1 hm_p
  · have hfit4 : cref.toNat + 3 + fullArenaClauseSizeCore st4.core cref.toNat ≤
        sem1.core.arena_len := by
      change _ + fullArenaClauseSizeCore st3.core _ ≤ _; rw [hcsz3]; exact hfit1
    have hr_lt4 : ri_f.toNat < fullArenaClauseSizeCore st4.core cref.toNat := by
      change ri_f.toNat < fullArenaClauseSizeCore st3.core _; rw [hcsz3]; exact hr_lt
    have hpi6 := fastProp_b1_oom (off4_v := off4_v) hpi1 hlen4 hnw4
      hsw4' hperm4 rfl rfl hag4 (hpi1.tr.congr rfl rfl rfl) hsc4 hpi1.not_f
      hnot_st1 hq_le hcr_lt hcr_ref3 hflag hfit4 hr2 hr_lt4 hq4_nat
      hp4_nat hq4_2
    have halen4 := hlen4.core_ok.arena_len_le
    have hst4_ar4 : st4.core.arena[cref.toNat + 3 + 1]'(by omega) = repl_f := by
      have h1 : st4.core.arena[cref.toNat + 4]'(by omega) = repl_f := by
        dsimp [st4, st3]
        rw [List.getElem_set_ne (by omega), List.getElem_set_self]
      exact h1
    have hst4_arr : st4.core.arena[cref.toNat + 3 + ri_f.toNat]'(by omega) = not_lit := by
      dsimp [st4, st3]; rw [List.getElem_set_self]
    have ⟨hnw5, hperm45⟩ := Full.full_swapLits_preserves_nw hlen4.core_ok hnw4 hcr_ref3
      (k1 := 1) (k2 := ri_f.toNat) (by omega) (by omega)
    let st5 : FullState := { st4 with core := { st4.core with
      arena := (st4.core.arena.set (cref.toNat + 4) not_lit).set (cref.toNat + 3 + ri_f.toNat)
        repl_f } }
    have hst5_sw : st5.core = { st4.core with
      arena := (st4.core.arena.set (cref.toNat + 3 + 1)
          (st4.core.arena[cref.toNat + 3 + ri_f.toNat]'(by omega))).set
        (cref.toNat + 3 + ri_f.toNat) (st4.core.arena[cref.toNat + 3 + 1]'(by omega)) } := by
      simp only [st5, hst4_ar4, hst4_arr]
    rw [← hst5_sw] at hnw5 hperm45
    have hcr_ref5 : cref.toNat ∈ fullArenaClauseRefsCore st5.core := hperm45.1.symm ▸ hcr_ref3
    have hsw5 := hsw4'.with_nonwatch (k' := st5.core) rfl rfl rfl rfl hperm45.1
    have har_len5 : st5.core.arena_len ≤ st5.core.arena.length := by
      simp only [st5, List.length_set]; exact Nat.le_trans halen4 (Nat.le_of_eq hst4_alen.symm)
    have hsb5 := hsb4.reconstruct_of_nw_arenaInv hsw5 hnw5.arena har_len5 rfl rfl rfl
    have hwf5 := hnw5.arena.refs_wf cref.toNat hcr_ref5
    have hq4_1_off : (off4_v + (q_v - off_v) + 1#64).toNat =
        (off4_v + (q_v - off_v)).toNat + 1 := by
      simpa only [BitVec.ofNat_eq_ofNat] using hq4_1
    have h_le_p : off_v.toNat ≤ p_v.toNat := Nat.le_trans hpi1.sw.q_ge hq_le
    have hp4_off_sub : (off4_v + (p_v - off_v)).toNat =
        off4_v.toNat + (p_v.toNat - off_v.toNat) := by
      have h1 := hp4_nat
      simp only [BitVec.ofNat_eq_ofNat] at h1
      rw [← hoff4_nat] at h1
      have h1_lt : off4_v.toNat + (p_v.toNat + 2 - off_v.toNat) < 2 ^ 64 := by
        rw [← h1]; exact BitVec.isLt _
      have hsub : (p_v - off_v).toNat = p_v.toNat - off_v.toNat := bv64_sub_toNat h_le_p
      rw [bv64_add_toNat (by
        rw [hsub]
        exact Nat.lt_of_le_of_lt
          (Nat.add_le_add_left (Nat.sub_le_sub_right (Nat.le_add_right _ 2) _) _) h1_lt), hsub]
    have hp4_split : (off4_v + (p_v + 1#64 + 1#64 - off_v)).toNat =
        (off4_v + (p_v - off_v)).toNat + 2 := by
      have h1 := hp4_nat
      simp only [BitVec.ofNat_eq_ofNat] at h1
      rw [← hoff4_nat] at h1
      rw [h1, hp4_off_sub, Nat.sub_add_comm h_le_p, Nat.add_assoc]
    have hsb5_w : SplitWatchBoundsInv
        { st5.core with wstk := (st5.core.wstk.set q4_v.toNat w0).set (q4_v.toNat + 1) cref }
        not_lit.toNat off4_v.toNat (q4_v + 2#64).toNat
        (off4_v + (p_v + 1#64 + 1#64 - off_v)).toNat (off4_v + (end_v - off_v)).toNat := by
      change SplitWatchBoundsInv st5.core not_lit.toNat off4_v.toNat q4_v.toNat
        (off4_v + (p_v + 1#64 + 1#64 - off_v)).toNat (off4_v + (end_v - off_v)).toNat at hsb5
      change Full.SplitWatchesInv F_cur st5.core not_lit.toNat off4_v.toNat q4_v.toNat
        (off4_v + (p_v + 1#64 + 1#64 - off_v)).toNat (off4_v + (end_v - off_v)).toNat at hsw5
      rw [hp4_split] at hsb5 hsw5
      rw [show (q4_v + 2#64).toNat = q4_v.toNat + 2 from hq4_2, hp4_split]
      have h_qp_ok : q4_v.toNat ≤ (off4_v + (p_v - off_v)).toNat := by
        rw [hq4_nat, ← hoff4_nat, hp4_off_sub]
        exact Nat.add_le_add_left (by have := hpi1.sw.q_ge; have := hq_le; omega) _
      have hq4_1_lt_c' : q4_v.toNat + 1 < c.wcap := by
        rw [← hq4_1]; exact hq4_1_lt_c
      exact hsb5.write_large hsw5 hnot_st1 h_qp_ok
        (by simp [st5, hwstk'_len]; exact hq4_lt_c) (by simp [st5, hwstk'_len]; exact hq4_1_lt_c')
        hflag (by exact hw0_blk)
        hcr_lt (Nat.le_trans (by decide : 2 ≤ 3) hwf5.2.1)
        (Nat.le_trans hwf5.2.2.1 hwf5.2.2.2.1)
        (fullArenaLiveLitsLt_of_arenaInv hnw5.arena har_len5 hcr_ref5)
    have hm6 : (FullMem c (fastPropMem s { st4 with core := { st4.core with
        arena := (st4.core.arena.set (cref.toNat + 4) not_lit).set
          (cref.toNat + 3 + ri_f.toNat) repl_f,
        wstk := (st4.core.wstk.set q4_v.toNat w0).set (q4_v.toNat + 1) cref,
        oom := 1#64 } }) ⋆ R) m := by
      simp only [BitVec.ofNat_eq_ofNat, hoff4_mem_eq, fastPropMem_arena, fastPropMem_wstk] at hm
      rw [h4_idx, h3r_idx, hq4_1_off] at hm
      rw [← fastPropMem_with_oom_revert]
      exact hm
    dsimp only
    simp only [hoff4_mem_eq, BitVec.ofNat_eq_ofNat]
    exact hk_oom _ off4_v m ⟨hpi6, hsb5_w.with_nonwatch rfl rfl rfl rfl rfl⟩
      htend1_eq hunass1_eq hunfl1_eq (by show (1 : BitVec 64) ≠ 0#64; decide) hm6

section
attribute [local irreducible] noBoundsAlvlAssignExpr

private def noBoundsLargeNoReplExpr
    (h_p ignore_ref cbase pAr pWstk vals_p fl_p lvl_p rsns_p tpos_p trl_p ph_p
      q_v tend_v unass_v unfl_v ticks_v : Val i64)
    (cref other nl_lvl cur_lvl csz : Val i32) (ov : Val i8) (rec_ph : Val .bool)
    (k_cont : Val i64 → Val i64 → Val i64 → Val i64 → Val i64 → Expr Val Cont [.bool])
    (k_confl : Val i64 → Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  .let_ (Op.mk (.mul i64) (.var q_v, (.imm (4 : BitVec 64), ()))) fun x166 =>
  .let_ (Op.mk (.add i64) (.var pWstk, (.var x166.1, ()))) fun x167 =>
  .let_ (Op.mk (.and i32) (.var other, (.imm (2147483647 : BitVec 32), ()))) fun x168 =>
  .store (.var x168.1) (.var x167.1) (
    .let_ (Op.mk (.add i64) (.var q_v, (.imm (1 : BitVec 64), ()))) fun x169 =>
    .let_ (Op.mk (.mul i64) (.var x169.1, (.imm (4 : BitVec 64), ()))) fun x170 =>
    .let_ (Op.mk (.add i64) (.var pWstk, (.var x170.1, ()))) fun x171 =>
    .store (.var cref) (.var x171.1) (
      .let_ (Op.mk (.add i64) (.var q_v, (.imm (2 : BitVec 64), ()))) fun x172 =>
      .let_ (Op.mk (.zext 32 64) (.var cref, ())) fun x173 =>
      .let_ (Op.mk (.cmp .eq i64) (.var x173.1, (.var ignore_ref, ()))) fun x174 =>
      .jnz (.var x174.1) (k_cont ticks_v tend_v unass_v unfl_v x172.1) (
        .let_ (Op.mk (.trunc 32 8) (.imm (0 : BitVec 32), ())) fun x175 =>
        .let_ (Op.mk (.sext 8 32) (.var ov, ())) fun x176 =>
        .let_ (Op.mk (.sext 8 32) (.var x175.1, ())) fun x177 =>
        .let_ (Op.mk (.cmp .slt i32) (.var x176.1, (.var x177.1, ()))) fun x178 =>
        .jnz (.var x178.1) (
          .let_ (Op.mk (.add i64) (.var h_p, (.imm (528 : BitVec 64), ()))) fun x179 =>
          .store (t := i64) (.imm (2 : BitVec 64)) (.var x179.1) (
            .let_ (Op.mk (.zext 32 64) (.var cref, ())) fun x180 =>
            .let_ (Op.mk (.add i64) (.var h_p, (.imm (176 : BitVec 64), ()))) fun x181 =>
            .store (.var x180.1) (.var x181.1) (k_confl x172.1)
          )
        ) (
          .let_ (Op.mk (.add i64) (.var ticks_v, (.imm (1 : BitVec 64), ()))) fun tk1 =>
          noBoundsAlvlAssignExpr nl_lvl cur_lvl csz other cref rec_ph cbase pAr
            tend_v unass_v unfl_v vals_p fl_p lvl_p rsns_p tpos_p trl_p ph_p
            (fun te un uf => k_cont tk1.1 te un uf x172.1)
        )
      )
    )
  )

private theorem noBoundsLargeNoRepl_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sem1 : FullState}
    {not_lit other cref nl_lvl0 cur_lvl csz32 : BitVec 32} {ov : BitVec 8} {rec_ph : Bool}
    {off_v p_v q_v end_v tend_v unass_v unfl_v ticks_v ignore_ref : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    {k_cont : Val i64 → Val i64 → Val i64 → Val i64 → Val i64 → Expr Val Cont [.bool]}
    {k_confl : Val i64 → Expr Val Cont [.bool]}
    (hmaxv : c.max_vars < 2 * dimacsBound) (har : c.arena_cap < 2 * dimacsBound)
    (hwc : c.wcap < 2 * dimacsBound)
    (hlen0 : s.LengthsOk c) (hcv0 : s.core.cur_vars ≤ c.max_vars)
    (hnb1 : PropLitNoBoundsInv c F0 F_cur s sem1 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hlen1_mem : (fastPropMem s sem1).LengthsOk c)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref1 : cref.toNat ∈ fullArenaClauseRefsCore sem1.core)
    (hng1 : fullArenaClauseGarbCore sem1.core cref.toNat = false)
    (hfit1 : cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤ sem1.core.arena_len)
    (hother_lt : other.toNat < 2 * sem1.core.cur_vars)
    (hnot_st1 : not_lit.toNat < 2 * sem1.core.cur_vars)
    (hother_mem : other.toNat ∈ fullArenaClauseLitsCore sem1.core cref.toNat)
    (hnot_mem : not_lit.toNat ∈ fullArenaClauseLitsCore sem1.core cref.toNat)
    (hunit : ∀ l ∈ fullArenaClauseLitsCore sem1.core cref.toNat,
      l = other.toNat ∨ sem1.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hother_lt1_vals : other.toNat < sem1.core.vals.length)
    (hov_eq : ov = sem1.core.vals[other.toNat]'hother_lt1_vals)
    (hov_np : (0#32).slt ((sem1.core.vals[other.toNat]'hother_lt1_vals).signExtend 32) = false)
    (hnl1 : sem1.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0)
    (hcur_eq : cur_lvl.toNat = s.core.cur_level)
    (hclv_lt32 : s.core.cur_level < 2 ^ 32)
    (hcsz32 : csz32.toNat = fullArenaClauseSizeCore sem1.core cref.toNat)
    (h3_idx : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3)
    (htend1_eq : tend_v.toNat = sem1.core.trail_end) (hunass1_eq : unass_v = sem1.core.unassigned)
    (hunfl1_eq : unfl_v = sem1.core.unflushed) (hoom1 : sem1.core.oom = 0#64)
    (hct1 : sem1.core.confl_type = s.core.confl_type)
    (hq1_nat : (q_v + 1#64).toNat = q_v.toNat + 1)
    (hq2_nat : (q_v + 2#64).toNat = q_v.toNat + 2)
    (hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2)
    (hq_le : q_v.toNat ≤ p_v.toNat)
    (hq_lt_ws1 : q_v.toNat < sem1.core.wstk.length)
    (hq1_lt_ws1 : q_v.toNat + 1 < sem1.core.wstk.length)
    (hm : (FullMem c (fastPropMem s sem1) ⋆ R) m)
    (hk_cont : ∀ (sem' : FullState) (ticks_n tend_n unass_n unfl_n : BitVec 64) (m' : Mem 64),
      (ticks_n = ticks_v ∨ ticks_n = ticks_v + 1#64) →
      PropLitNoBoundsInv c F0 F_cur s sem' not_lit.toNat off_v.toNat (q_v + 2#64).toNat
        (p_v.toNat + 2) end_v.toNat →
      tend_n.toNat = sem'.core.trail_end → unass_n = sem'.core.unassigned →
      unfl_n = sem'.core.unflushed → sem'.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 →
      sem'.core.oom = 0#64 → sem'.core.confl_type = s.core.confl_type →
      (FullMem c (fastPropMem s sem') ⋆ R) m' →
      wp Γ Q X (k_cont ticks_n tend_n unass_n unfl_n (q_v + 2#64)) m')
    (hk_confl : ∀ (sem' : FullState) (m' : Mem 64),
      PropLitNoBoundsInv c F0 F_cur s sem' not_lit.toNat off_v.toNat (q_v + 2#64).toNat
        (p_v.toNat + 2) end_v.toNat →
      tend_v.toNat = sem'.core.trail_end → unass_v = sem'.core.unassigned →
      unfl_v = sem'.core.unflushed → Full.PropLitConfl F_cur ignore_ref sem'.core →
      (FullMem c (fastPropMem s sem') ⋆ R) m' →
      wp Γ Q X (k_confl (q_v + 2#64)) m') :
    wp Γ Q X (noBoundsLargeNoReplExpr c.hdr ignore_ref (cref.setWidth 64 + 3#64) c.pArena c.pWstk
      c.pVals c.pFlags c.pLevel c.pReason c.pTrailPos c.pTrail c.pPhases
      q_v tend_v unass_v unfl_v ticks_v cref other nl_lvl0 cur_lvl csz32 ov rec_ph
      k_cont k_confl) m := by
  subst hov_eq
  have hpi1 := hnb1.prop
  unfold dimacsBound at hmaxv har hwc
  have hm1_wstk := hlen1_mem.core_ok.wstk_len_arr
  have hm1_aren := hlen1_mem.core_ok.arena_len_arr
  have hm1_alen := hlen1_mem.core_ok.arena_len_le
  have hm1_vals := hlen1_mem.core_ok.vals_len
  have hwstk1 := hpi1.len.core_ok.wstk_len_arr
  have hwc64_2 : c.wcap + 2 < 2 ^ 64 :=
    Nat.lt_trans (Nat.add_lt_add_right hwc 2) (by decide)
  have _hq_lt_cap : q_v.toNat < c.wcap := hwstk1 ▸ hq_lt_ws1
  have _hq1_lt_cap : q_v.toNat + 1 < c.wcap := hwstk1 ▸ hq1_lt_ws1
  have har_len1 : sem1.core.arena_len ≤ sem1.core.arena.length :=
    Nat.le_trans hpi1.len.core_ok.arena_len_le (Nat.le_of_eq hpi1.len.core_ok.arena_len_arr.symm)
  have hwf1 := hpi1.nw.arena.refs_wf cref.toNat hcr_ref1
  have hsb2_raw := hnb1.sb.write_large hpi1.sw hnot_st1 hq_le hq_lt_ws1 hq1_lt_ws1
    (Full.bv32_mask7f_flag0 other)
    (Nat.lt_of_le_of_lt (bv32_mask7f_toNat_le (other &&& 0x7FFFFFFF#32))
      (Nat.lt_of_le_of_lt (bv32_mask7f_toNat_le other) hother_lt))
    hcr_lt (Nat.le_trans (by decide : 2 ≤ 3) hwf1.2.1) hfit1
    (fullArenaLiveLitsLt_of_nw_arenaInv hpi1.nw.arena har_len1 hcr_ref1)
  unfold noBoundsLargeNoReplExpr
  nb_head_steps
  · let sem2 : FullState :=
      { sem1 with core :=
          { sem1.core with
            wstk := (sem1.core.wstk.set q_v.toNat (other &&& 0x7FFFFFFF#32)).set
              (q_v + 1#64).toNat cref } }
    have hinv2 := Full.propLit_inv_keep_large hpi1 hpi1.sw hnot_st1 hq1_nat hq2_nat hp2_nat
      (Nat.add_le_add_right hq_le 2) hpi1.sw.p_le_end (Full.bv32_mask7f_flag0 other)
      hcr_lt hcr_ref1
    simp only [BitVec.ofNat_eq_ofNat, hp2_nat] at hinv2
    have hsb2 : SplitWatchBoundsInv sem2.core not_lit.toNat off_v.toNat (q_v + 2#64).toNat
        (p_v.toNat + 2) end_v.toNat := by
      simpa only [sem2, hq1_nat, hq2_nat] using hsb2_raw
    exact hk_cont sem2 ticks_v tend_v unass_v unfl_v m (Or.inl rfl) ⟨hinv2, hsb2⟩
      htend1_eq hunass1_eq hunfl1_eq hnl1 hoom1 hct1
      (by simpa only [sem2, BitVec.ofNat_eq_ofNat, fastPropMem_wstk,
        fastPropMem_with_wstk] using hm)
  · have hne_ign : cref.setWidth 64 ≠ ignore_ref := by assumption
    have hov_f := Full.propLit_vals_neg hpi1.nw hother_lt hother_lt1_vals hc
    have ⟨hpi_c, hcf_c⟩ := Full.propLit_large_confl hpi1 hnot_st1 hq_le
      hq1_nat hq2_nat hp2_nat hcr_lt hcr_ref1 hng1 hne_ign hov_f hunit
    let sem_c : FullState :=
      { sem1 with core :=
          { sem1.core with
            wstk := (sem1.core.wstk.set q_v.toNat (other &&& 0x7FFFFFFF#32)).set
              (q_v + 1#64).toNat cref,
            confl_type := 2#64, confl_ref := cref.setWidth 64 } }
    simp only [BitVec.ofNat_eq_ofNat, hp2_nat] at hpi_c
    have hsb_c : SplitWatchBoundsInv sem_c.core not_lit.toNat off_v.toNat (q_v + 2#64).toNat
        (p_v.toNat + 2) end_v.toNat := by
      have h1 : SplitWatchBoundsInv { sem1.core with
          wstk := (sem1.core.wstk.set q_v.toNat (other &&& 0x7FFFFFFF#32)).set
            (q_v + 1#64).toNat cref } not_lit.toNat off_v.toNat (q_v + 2#64).toNat
          (p_v.toNat + 2) end_v.toNat := by simpa only [hq1_nat, hq2_nat] using hsb2_raw
      exact h1.with_nonwatch rfl rfl rfl rfl rfl
    exact hk_confl sem_c m ⟨hpi_c, hsb_c⟩ htend1_eq hunass1_eq hunfl1_eq hcf_c
      (by simpa only [sem_c, BitVec.ofNat_eq_ofNat, fastPropMem_wstk,
        fastPropMem_with_large_confl_wstk] using hm)
  · have hov_un := Full.propLit_vals_un hpi1.nw hother_lt hother_lt1_vals hov_np hc
    have hsw2 := hpi1.sw.write_large hnot_st1 hq_le
      hq_lt_ws1 hq1_lt_ws1 (Full.bv32_mask7f_flag0 other) hcr_lt hcr_ref1
    let wstk2 := (sem1.core.wstk.set q_v.toNat (other &&& 0x7FFFFFFF#32)).set (q_v.toNat + 1) cref
    let sem2 : FullState := { sem1 with core := { sem1.core with wstk := wstk2 } }
    have hlen2 : sem2.LengthsOk c :=
      ⟨{ hpi1.len.core_ok with wstk_len_arr := by simp [sem2, wstk2, hwstk1] },
       hpi1.len.scratch_ok⟩
    have hlen2_mem := fastPropMem_lengthsOk hlen0 hlen2 hpi1.cur_vars_eq
      (hpi1.ag.get FullCoreState.propagated) rfl
    have hnw2 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c sem2.core) :=
      Full.fullWitnessInv_nw_congr hlen2.core_ok.cur_vars_le hpi1.nw
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    have hpi2 : Full.PropLitInv c F0 F_cur s sem2 not_lit.toNat off_v.toNat
        (q_v + 2#64).toNat (p_v.toNat + 2) end_v.toNat :=
      { len := hlen2, nw := hnw2, sw := by rw [hq2_nat]; exact hsw2
        ag := hpi1.ag.update (fun k => { k with wstk := wstk2 })
        tr := hpi1.tr.congr rfl rfl rfl, perm := hpi1.perm,
        sc_eq := hpi1.sc_eq, not_f := hpi1.not_f }
    have hsb2 : SplitWatchBoundsInv sem2.core not_lit.toNat off_v.toNat
        (q_v + 2#64).toNat (p_v.toNat + 2) end_v.toNat := by
      rw [hq2_nat]; exact hsb2_raw
    have hclv_sem2 : sem2.core.cur_level < 2 ^ 32 := by
      rw [hpi2.ag.get FullCoreState.cur_level]; exact hclv_lt32
    have hcur_eq2 : cur_lvl = BitVec.ofNat 32 sem2.core.cur_level := by
      apply BitVec.eq_of_toNat_eq
      rw [hcur_eq, ← hpi2.ag.get FullCoreState.cur_level,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclv_sem2]
    nb_head_steps
    refine noBoundsAlvlAssign_wp hmaxv har hcv0 hpi2 hlen2_mem hcr_lt hcr_ref1 hng1 hfit1
      hother_lt hov_un hnot_st1 hother_mem hnot_mem hunit hnl1 hcur_eq2 hclv_sem2 hcsz32 h3_idx
      htend1_eq hoom1 hct1
      (by simpa only [sem2, wstk2, BitVec.ofNat_eq_ofNat, hq1_nat, fastPropMem_wstk,
        fastPropMem_with_wstk] using hm) ?_
    intro sem3 tend_n unass_n unfl_n m' hpi3 hcv3 hwv3 hws3 hal3 har3 ht3 hu3 huf3 hnl3 hoom3
      hct3 hm'
    exact hk_cont sem3 (ticks_v + 1#64) tend_n unass_n unfl_n m' (Or.inr rfl)
      ⟨hpi3, hsb2.with_nonwatch hcv3 hwv3 hws3 hal3 har3⟩
      ht3 hu3 huf3 hnl3 hoom3 hct3 hm'

end

private theorem noBoundsBinAssignStep_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sem : FullState}
    {lit w0_v other nl_lvl0 : BitVec 32} {rec_ph : Bool}
    {off_v p_v q_v end_v tend_v unass_v unfl_v : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    {k_next : Val i64 → Val i64 → Val i64 → Expr Val Cont [.bool]}
    (hmaxv : c.max_vars < 2 * dimacsBound) (hlen0 : s.LengthsOk c)
    (hcv0 : s.core.cur_vars ≤ c.max_vars)
    (hpi : Full.PropLitInv c F0 F_cur s sem (lit ^^^ 1#32).toNat off_v.toNat q_v.toNat p_v.toNat
      end_v.toNat)
    (hsb : SplitWatchBoundsInv sem.core (lit ^^^ 1#32).toNat off_v.toNat q_v.toNat p_v.toNat
      end_v.toNat)
    (hp_lt : p_v.toNat < end_v.toNat) (_hp_lt_w : p_v.toNat < sem.core.wstk.length)
    (_hw0_get : sem.core.wstk[p_v.toNat]? = some w0_v)
    (hflag : (w0_v &&& 0x80000000#32) ≠ 0#32)
    (hother_eq : other = w0_v &&& 0x7FFFFFFF#32)
    (hother_lt : other.toNat < 2 * sem.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [(lit ^^^ 1#32).toNat, other.toNat]))
    (hrem1 : Full.WatchSliceOk F_cur sem.core (lit ^^^ 1#32).toNat (p_v.toNat + 1)
      (end_v.toNat - (p_v.toNat + 1)))
    (hne_ff : w0_v ≠ 0xFFFFFFFF#32)
    (hrem1_sb : WatchSliceBoundsOk sem.core (p_v.toNat + 1) (end_v.toNat - (p_v.toNat + 1)))
    (hnot_st : (lit ^^^ 1#32).toNat < 2 * sem.core.cur_vars)
    (hq_lt_ws : q_v.toNat < sem.core.wstk.length)
    (hp1_nat : (p_v + 1#64).toNat = p_v.toNat + 1)
    (hq1_nat : (q_v + 1#64).toNat = q_v.toNat + 1)
    (hov_un : ({ sem with core := { sem.core with
        wstk := sem.core.wstk.set q_v.toNat w0_v } }).core.vals[other.toNat]?.getD 0#8 = 0#8)
    (hnl_eq : sem.core.lvl[(lit ^^^ 1#32).toNat / 2]?.getD 0#32 = nl_lvl0)
    (htend_eq : tend_v.toNat = sem.core.trail_end) (hoom_st : sem.core.oom = 0#64)
    (hct_st : sem.core.confl_type = s.core.confl_type)
    (hm : (FullMem c (fastPropMem s { sem with core := { sem.core with
      wstk := sem.core.wstk.set q_v.toNat w0_v } }) ⋆ R) m)
    (hk_next : ∀ (sem' : FullState) (tend_n unass_n unfl_n : BitVec 64) (m' : Mem 64),
      PropLitNoBoundsInv c F0 F_cur s sem' (lit ^^^ 1#32).toNat off_v.toNat (q_v + 1#64).toNat
        (p_v + 1#64).toNat end_v.toNat →
      tend_n.toNat = sem'.core.trail_end → unass_n = sem'.core.unassigned →
      unfl_n = sem'.core.unflushed →
      sem'.core.lvl[(lit ^^^ 1#32).toNat / 2]?.getD 0#32 = nl_lvl0 →
      sem'.core.oom = 0#64 → sem'.core.confl_type = s.core.confl_type →
      (FullMem c (fastPropMem s sem') ⋆ R) m' →
      wp Γ Q X (k_next tend_n unass_n unfl_n) m') :
    wp Γ Q X (noBoundsAssignExpr other nl_lvl0
      (((lit ^^^ 1#32) &&& 0x7FFFFFFF#32) ||| 0x80000000#32) rec_ph
      tend_v unass_v unfl_v c.pVals c.pFlags c.pLevel c.pReason c.pTrailPos c.pTrail c.pPhases
      k_next) m := by
  subst hother_eq
  let not_lit : BitVec 32 := lit ^^^ 1#32
  let other : BitVec 32 := w0_v &&& 0x7FFFFFFF#32
  have hwstk_len := hpi.len.core_ok.wstk_len_arr
  have hcv_eq : sem.core.cur_vars = s.core.cur_vars := hpi.cur_vars_eq
  have hq_le := hpi.sw.q_le_p
  have hsw_adv := hpi.sw.advance_rem (p' := p_v.toNat + 1) (Nat.le_succ _) hp_lt hrem1
  have hsw1 := hsw_adv.write_bin (c := c) hpi.len.core_ok.cur_vars_le hnot_st hq_le
    hq_lt_ws hflag hother_lt hent
  have hsb1 := (hsb.advance_rem (p' := p_v.toNat + 1) hrem1_sb).write_bin hsw_adv hnot_st hq_le
    hq_lt_ws hflag hne_ff hother_lt
  let wstk1 := sem.core.wstk.set q_v.toNat w0_v
  let sem1 : FullState := { sem with core := { sem.core with wstk := wstk1 } }
  have hlen1 : sem1.LengthsOk c :=
    ⟨{ hpi.len.core_ok with wstk_len_arr := by simp [sem1, wstk1, hwstk_len] },
     hpi.len.scratch_ok⟩
  have hnw1 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c sem1.core) :=
    Full.fullWitnessInv_nw_congr hlen1.core_ok.cur_vars_le hpi.nw
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hsb1' : SplitWatchBoundsInv sem1.core not_lit.toNat off_v.toNat
      (q_v + 1#64).toNat (p_v.toNat + 1) end_v.toNat := by rw [hq1_nat]; exact hsb1
  have hte_lt : sem.core.trail_end < sem.core.cur_vars :=
    hnw1.trail_end_lt_of_unassigned hother_lt hov_un
  have hlen1_mem := fastPropMem_lengthsOk hlen0 hlen1 hcv_eq
    (hpi.ag.get FullCoreState.propagated) rfl
  refine noBoundsAssign_wp (alvl := nl_lvl0)
    (rsn := ((lit ^^^ 1#32) &&& 0x7FFFFFFF#32) ||| 0x80000000#32)
    (k_next := k_next) hmaxv hcv0 hlen1_mem hpi.cur_vars_eq hother_lt hte_lt htend_eq hm ?_
  intro flags' ph' unass_n unfl_n m' hfl' hph' hm'
  dsimp only at hm'
  try simp only [BitVec.ofNat_eq_ofNat] at hm'
  rw [fastPropMem_assign_eq (te' := sem.core.trail_end + 1)
    (un' := unass_n) (uf' := unfl_n)] at hm'
  have hassign := Full.full_bin_assign_nw_step hlen1.core_ok hnw1 hnot_st hother_lt
    hov_un hpi.not_f hent (flags' := flags') (unas' := unass_n) (unfl' := unfl_n)
  rw [show sem1.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 from hnl_eq] at hassign
  have ⟨hlen2, hnw2, hsw2, hag2, htr2, hperm2, hsc2, hnot_f2, hnl2⟩ :=
    fastPropMem_eq_of_eq hpi hsw1 (by simp [hwstk_len]) hfl' hph' hnot_st
      hother_lt hov_un hnl_eq hassign
  have hsb2 := hsb1'.with_nonwatch (k' := { sem1.core with
    vals := (sem1.core.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
    flags := flags', lvl := sem1.core.lvl.set (other.toNat / 2) nl_lvl0
    rsns := sem1.core.rsns.set (other.toNat / 2)
      (if nl_lvl0 = 0#32 then 0xFFFFFFFF#32 else
        ((lit ^^^ 1#32) &&& 0x7FFFFFFF#32) ||| 0x80000000#32)
    trl := sem1.core.trl.set sem1.core.trail_end other
    trail_pos :=
      sem1.core.trail_pos.set (other.toNat / 2) (BitVec.ofNat 32 sem1.core.trail_end)
    trail_end := sem1.core.trail_end + 1
    unassigned := unass_n, unflushed := unfl_n }) rfl rfl rfl rfl rfl
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
  exact hk_next _ (tend_v + 1#64) unass_n unfl_n m'
    ⟨⟨hlen2, hnw2, by rwa [hq1_nat, hp1_nat], hag2, htr2, hperm2, hsc2, hnot_f2⟩,
     by rwa [hp1_nat]⟩
    htend1 rfl rfl hnl2 hoom_st hct_st hm'

private def noBoundsValsGt0Expr (pWstk p1_v q_v : Val i64) (w0 : Val i32)
    (k_bin : Val i64 → Expr Val Cont [.bool])
    (k_large : Val i64 → Val i64 → Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  .let_ (Op.mk (.and i32) (.var w0, (.imm (2147483648 : BitVec 32), ()))) fun x1 =>
  .let_ (Op.mk (.cmp .ne i32) (.var x1.1, (.imm (0 : BitVec 32), ()))) fun x2 =>
  .jnz (.var x2.1) (
    .let_ (Op.mk (.mul i64) (.var q_v, (.imm (4 : BitVec 64), ()))) fun x3 =>
    .let_ (Op.mk (.add i64) (.var pWstk, (.var x3.1, ()))) fun x4 =>
    .store (.var w0) (.var x4.1) (
      .let_ (Op.mk (.add i64) (.var q_v, (.imm (1 : BitVec 64), ()))) fun q1 =>
      k_bin q1.1
    )
  ) (
    .let_ (Op.mk (.mul i64) (.var p1_v, (.imm (4 : BitVec 64), ()))) fun x3 =>
    .let_ (Op.mk (.add i64) (.var pWstk, (.var x3.1, ()))) fun x4 =>
    .load i32 (.var x4.1) fun cref =>
    .let_ (Op.mk (.add i64) (.var p1_v, (.imm (1 : BitVec 64), ()))) fun p2 =>
    .let_ (Op.mk (.mul i64) (.var q_v, (.imm (4 : BitVec 64), ()))) fun x5 =>
    .let_ (Op.mk (.add i64) (.var pWstk, (.var x5.1, ()))) fun x6 =>
    .store (.var w0) (.var x6.1) (
      .let_ (Op.mk (.add i64) (.var q_v, (.imm (1 : BitVec 64), ()))) fun q1 =>
      .let_ (Op.mk (.mul i64) (.var q1.1, (.imm (4 : BitVec 64), ()))) fun x7 =>
      .let_ (Op.mk (.add i64) (.var pWstk, (.var x7.1, ()))) fun x8 =>
      .store (.var cref) (.var x8.1) (
        .let_ (Op.mk (.add i64) (.var q_v, (.imm (2 : BitVec 64), ()))) fun q2 =>
        k_large p2.1 q2.1
      )
    )
  )

private theorem noBoundsValsGt0_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sem : FullState} {not_lit w0_v : BitVec 32}
    {off_v p_v q_v end_v : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    {k_bin : Val i64 → Expr Val Cont [.bool]}
    {k_large : Val i64 → Val i64 → Expr Val Cont [.bool]}
    (hwc : c.wcap < 2 * dimacsBound)
    (hlen0 : s.LengthsOk c)
    (hnb : PropLitNoBoundsInv c F0 F_cur s sem not_lit.toNat off_v.toNat q_v.toNat p_v.toNat
      end_v.toNat)
    (hend_wcap : end_v.toNat ≤ c.wcap)
    (hp_lt : p_v.toNat < end_v.toNat) (_hp_lt_w : p_v.toNat < sem.core.wstk.length)
    (hw0_get : sem.core.wstk[p_v.toNat]? = some w0_v)
    (hnot_st : not_lit.toNat < 2 * sem.core.cur_vars)
    (hp1_nat : (p_v + 1#64).toNat = p_v.toNat + 1)
    (hq1_nat : (q_v + 1#64).toNat = q_v.toNat + 1)
    (hm : (FullMem c (fastPropMem s sem) ⋆ R) m)
    (hk_bin : ∀ (sem' : FullState) (m' : Mem 64),
      end_v.toNat - (p_v.toNat + 1) < end_v.toNat - p_v.toNat →
      (p_v + 1#64).toNat = p_v.toNat + 1 →
      PropLitNoBoundsInv c F0 F_cur s sem' not_lit.toNat off_v.toNat (q_v + 1#64).toNat
        (p_v + 1#64).toNat end_v.toNat →
      sem'.core.trail_end = sem.core.trail_end → sem'.core.unassigned = sem.core.unassigned →
      sem'.core.unflushed = sem.core.unflushed → sem'.core.lvl = sem.core.lvl →
      sem'.core.oom = sem.core.oom → sem'.core.confl_type = sem.core.confl_type →
      (FullMem c (fastPropMem s sem') ⋆ R) m' →
      wp Γ Q X (k_bin (q_v + 1#64)) m')
    (hk_large : ∀ (sem' : FullState) (m' : Mem 64),
      end_v.toNat - (p_v.toNat + 2) < end_v.toNat - p_v.toNat →
      (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2 →
      PropLitNoBoundsInv c F0 F_cur s sem' not_lit.toNat off_v.toNat (q_v + 2#64).toNat
        (p_v + 1#64 + 1#64).toNat end_v.toNat →
      sem'.core.trail_end = sem.core.trail_end → sem'.core.unassigned = sem.core.unassigned →
      sem'.core.unflushed = sem.core.unflushed → sem'.core.lvl = sem.core.lvl →
      sem'.core.oom = sem.core.oom → sem'.core.confl_type = sem.core.confl_type →
      (FullMem c (fastPropMem s sem') ⋆ R) m' →
      wp Γ Q X (k_large (p_v + 1#64 + 1#64) (q_v + 2#64)) m') :
    wp Γ Q X (noBoundsValsGt0Expr c.pWstk (p_v + 1#64) q_v w0_v k_bin k_large) m := by
  have hpi := hnb.prop
  have hcv_eq := hpi.cur_vars_eq
  have hq_le := hpi.sw.q_le_p; have hp_le := hpi.sw.p_le_end
  have hwstk_len := hpi.len.core_ok.wstk_len_arr
  have hlen_mem := fastPropMem_lengthsOk hlen0 hpi.len hcv_eq
    (hpi.ag.get FullCoreState.propagated) rfl
  have hm_wstk := hlen_mem.core_ok.wstk_len_arr
  unfold dimacsBound at hwc
  have hwc64 : c.wcap + 1 < 2 ^ 64 := Nat.lt_trans (Nat.add_lt_add_right hwc 1) (by decide)
  have hwc64_2 : c.wcap + 2 < 2 ^ 64 := Nat.lt_trans (Nat.add_lt_add_right hwc 2) (by decide)
  have hp_rem_pos : 0 < end_v.toNat - p_v.toNat := Nat.sub_pos_of_lt hp_lt
  have hq_lt_ws : q_v.toNat < sem.core.wstk.length :=
    hwstk_len ▸ Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hq_le hp_lt) hend_wcap
  unfold noBoundsValsGt0Expr
  nb_head_split
  · have hflag : (w0_v &&& 0x80000000#32) ≠ 0#32 := by
      simpa only [ne_eq, ← BitVec.ofNat_eq_ofNat] using hc
    obtain ⟨hother_lt, hent, hrem1⟩ :=
      Full.watchSlice_inv_bin hpi.sw.rem_slice hp_rem_pos hw0_get hflag
    obtain ⟨hne_ff, hblk_sb, hrem1_sb⟩ :=
      hnb.sb.rem_slice.inv_bin hp_rem_pos hw0_get hflag
    have hsw_adv := hpi.sw.advance_rem (p' := p_v.toNat + 1) (Nat.le_succ _) hp_lt
      (by simpa [Nat.sub_sub] using hrem1)
    have hsw1 := hsw_adv.write_bin (c := c) hpi.len.core_ok.cur_vars_le hnot_st hq_le
      hq_lt_ws hflag hother_lt hent
    have hsb1 := (hnb.sb.advance_rem (p' := p_v.toNat + 1)
      (by simpa [Nat.sub_sub] using hrem1_sb)).write_bin hsw_adv hnot_st hq_le
      hq_lt_ws hflag hne_ff hblk_sb
    let wstk1 := sem.core.wstk.set q_v.toNat w0_v
    let sem1 : FullState := { sem with core := { sem.core with wstk := wstk1 } }
    have hlen1 : sem1.LengthsOk c :=
      ⟨{ hpi.len.core_ok with wstk_len_arr := by simp [sem1, wstk1, hwstk_len] },
       hpi.len.scratch_ok⟩
    have hnw1 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c sem1.core) :=
      Full.fullWitnessInv_nw_congr hlen1.core_ok.cur_vars_le hpi.nw
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    nb_head_steps
    exact hk_bin sem1 m (Nat.sub_lt hp_rem_pos Nat.zero_lt_one) hp1_nat
      { prop := { len := hlen1, nw := hnw1, sw := by rw [hq1_nat, hp1_nat]; exact hsw1
                  ag := hpi.ag.update (fun k => { k with wstk := wstk1 })
                  tr := hpi.tr.congr rfl rfl rfl, perm := hpi.perm, sc_eq := hpi.sc_eq,
                  not_f := hpi.not_f }
        sb := by rw [hq1_nat, hp1_nat]; exact hsb1 }
      rfl rfl rfl rfl rfl rfl
      (by simpa only [sem1, wstk1, BitVec.ofNat_eq_ofNat, fastPropMem_wstk,
        fastPropMem_with_wstk] using hm)
  · have hflag : (w0_v &&& 0x80000000#32) = 0#32 := by
      simpa only [← BitVec.ofNat_eq_ofNat] using hc
    obtain ⟨h2le, cref0, hcr_get, hcr_lt, hcr_ref, hrem2⟩ :=
      Full.watchSlice_inv_large hpi.sw.rem_slice hp_rem_pos hw0_get hflag
    obtain ⟨_, cref0_sb, hcr_get_sb, hblk_sb, hcr_lt_sb, hsz_sb, hfit_sb, hlive_sb,
        hrem2_sb⟩ :=
      hnb.sb.rem_slice.inv_large hp_rem_pos hw0_get hflag
    have hcr_sb_eq : cref0_sb = cref0 := Option.some.inj (hcr_get_sb.symm.trans hcr_get)
    subst cref0_sb
    have h2_le_end : p_v.toNat + 2 ≤ end_v.toNat :=
      Nat.add_sub_cancel' hp_le ▸ Nat.add_le_add_left h2le p_v.toNat
    have hp2_wcap : p_v.toNat + 2 ≤ c.wcap := Nat.le_trans h2_le_end hend_wcap
    have hp2_64 : p_v.toNat + 2 < 2 ^ 64 :=
      Nat.lt_of_le_of_lt hp2_wcap (Nat.lt_trans hwc (by decide))
    have hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2 := by
      rw [bv64_add_toNat (a := p_v + 1#64) (b := 1#64) (by rw [hp1_nat]; exact hp2_64),
        hp1_nat]; rfl
    have hq2_nat : (q_v + 2#64).toNat = q_v.toNat + 2 :=
      bv64_add2_toNat (a := q_v) (Nat.lt_of_le_of_lt
        (Nat.add_le_add_right (Nat.le_trans hq_le (Nat.le_trans hp_le hend_wcap)) 2) hwc64_2)
    have hq_lt_ws2 : q_v.toNat < sem.core.wstk.length :=
      hwstk_len ▸ Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hq_le
        (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 2)) h2_le_end)) hend_wcap
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
    have hsw_drop := hpi.sw.advance_rem (p' := p_v.toNat + 2) (by omega) h2_le_end
      (by simpa [Nat.sub_sub] using hrem2)
    have hsb_drop := hnb.sb.advance_rem (p' := p_v.toNat + 2)
      (by simpa [Nat.sub_sub] using hrem2_sb)
    have hsb_keep := hsb_drop.write_large hsw_drop hnot_st hq_le hq_lt_ws2 hq1_lt_ws2
      hflag hblk_sb (hcr_eq ▸ hcr_lt) (hcr_eq ▸ hsz_sb) (hcr_eq ▸ hfit_sb)
      (hcr_eq ▸ hlive_sb)
    have hpi_keep := Full.propLit_inv_keep_large hpi hsw_drop hnot_st hq1_nat hq2_nat
      hp2_nat (Nat.add_le_add_right hq_le 2) h2_le_end hflag hcr_lt (hcr_eq ▸ hcr_ref)
    have hcr_eq_c0 : sem.core.wstk[(p_v + 1).toNat]'(by
        rw [show (1 : BitVec 64) = 1#64 from rfl]; exact hcr_idx_lt) = cref0 := hcr_eq
    have hq1_nat' : (q_v + (1 : BitVec 64)).toNat = q_v.toNat + 1 := hq1_nat
    nb_head_steps
    exact hk_large _ m (fc_rem2_lt h2_le_end) hp2_nat
      ⟨hpi_keep, by rw [hp2_nat, hq2_nat, hq1_nat', ← hcr_eq]; exact hsb_keep⟩
      rfl rfl rfl rfl rfl rfl
      (by simpa only [hq1_nat', hcr_eq, fc_getElem_wstk, fastPropMem_wstk,
        fastPropMem_with_wstk] using hm)

private def noBoundsBinBranchExpr
    (h_p pWstk vals_p fl_p lvl_p rsns_p tpos_p trl_p ph_p
      q_v tend_v unass_v unfl_v ticks_v : Val i64)
    (w0 blk not_lit nl_lvl bin_rsn : Val i32) (rec_ph : Val .bool)
    (k_confl : Val i64 → Expr Val Cont [.bool])
    (k_cont : Val i64 → Val i64 → Val i64 → Val i64 → Val i64 → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  .let_ (Op.mk (.mul i64) (.var q_v, (.imm (4 : BitVec 64), ()))) fun x1 =>
  .let_ (Op.mk (.add i64) (.var pWstk, (.var x1.1, ()))) fun x2 =>
  .store (.var w0) (.var x2.1) (
    .let_ (Op.mk (.add i64) (.var q_v, (.imm (1 : BitVec 64), ()))) fun q1 =>
    .let_ (Op.mk (.zext 32 64) (.var blk, ())) fun b64 =>
    .let_ (Op.mk (.add i64) (.var vals_p, (.var b64.1, ()))) fun pv =>
    .load i8 (.var pv.1) fun ov =>
    .let_ (Op.mk (.trunc 32 8) (.imm (0 : BitVec 32), ())) fun z8 =>
    .let_ (Op.mk (.sext 8 32) (.var ov, ())) fun ov32 =>
    .let_ (Op.mk (.sext 8 32) (.var z8.1, ())) fun z32 =>
    .let_ (Op.mk (.cmp .slt i32) (.var ov32.1, (.var z32.1, ()))) fun cc =>
    .jnz (.var cc.1) (
      .let_ (Op.mk (.add i64) (.var h_p, (.imm (528 : BitVec 64), ()))) fun pct =>
      .store (t := i64) (.imm (1 : BitVec 64)) (.var pct.1) (
        .let_ (Op.mk (.zext 32 64) (.var not_lit, ())) fun nl64 =>
        .let_ (Op.mk (.add i64) (.var h_p, (.imm (536 : BitVec 64), ()))) fun pc0 =>
        .store (.var nl64.1) (.var pc0.1) (
          .let_ (Op.mk (.zext 32 64) (.var blk, ())) fun b64' =>
          .let_ (Op.mk (.add i64) (.var h_p, (.imm (544 : BitVec 64), ()))) fun pc1 =>
          .store (.var b64'.1) (.var pc1.1) (
            .let_ (Op.mk (.add i64) (.var h_p, (.imm (176 : BitVec 64), ()))) fun pcr =>
            .store (t := i64) (.imm (4294967295 : BitVec 64)) (.var pcr.1) (k_confl q1.1)
          )
        )
      )
    ) (
      .let_ (Op.mk (.add i64) (.var ticks_v, (.imm (1 : BitVec 64), ()))) fun tk1 =>
      noBoundsAssignExpr blk nl_lvl bin_rsn rec_ph tend_v unass_v unfl_v
        vals_p fl_p lvl_p rsns_p tpos_p trl_p ph_p
        (fun te un uf => k_cont tk1.1 te un uf q1.1)
    )
  )

private theorem noBoundsBinBranch_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sem : FullState} {lit w0_v nl_lvl0 : BitVec 32}
    {rec_ph : Bool} {off_v p_v q_v end_v tend_v unass_v unfl_v ticks_v ignore_ref : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    {k_confl : Val i64 → Expr Val Cont [.bool]}
    {k_cont : Val i64 → Val i64 → Val i64 → Val i64 → Val i64 → Expr Val Cont [.bool]}
    (hmaxv : c.max_vars < 2 * dimacsBound) (hlen0 : s.LengthsOk c)
    (hcv0 : s.core.cur_vars ≤ c.max_vars)
    (hnb : PropLitNoBoundsInv c F0 F_cur s sem (lit ^^^ 1#32).toNat off_v.toNat q_v.toNat
      p_v.toNat end_v.toNat)
    (hp_lt : p_v.toNat < end_v.toNat) (hp_lt_w : p_v.toNat < sem.core.wstk.length)
    (hw0_get : sem.core.wstk[p_v.toNat]? = some w0_v)
    (hflag : (w0_v &&& 0x80000000#32) ≠ 0#32)
    (hblk_nsgt : ∀ hlt : (w0_v &&& 0x7FFFFFFF#32).toNat < 2 * sem.core.cur_vars,
      (0#32).slt ((sem.core.vals[(w0_v &&& 0x7FFFFFFF#32).toNat]'(fastProp_lt_vals
        hnb.prop.len.core_ok hlt)).signExtend 32) = false)
    (hnot_st : (lit ^^^ 1#32).toNat < 2 * sem.core.cur_vars)
    (hq_lt_ws : q_v.toNat < sem.core.wstk.length)
    (hp1_nat : (p_v + 1#64).toNat = p_v.toNat + 1)
    (hq1_nat : (q_v + 1#64).toNat = q_v.toNat + 1)
    (hnl_eq : sem.core.lvl[(lit ^^^ 1#32).toNat / 2]?.getD 0#32 = nl_lvl0)
    (htend_eq : tend_v.toNat = sem.core.trail_end) (hoom_st : sem.core.oom = 0#64)
    (hct_st : sem.core.confl_type = s.core.confl_type)
    (hm : (FullMem c (fastPropMem s sem) ⋆ R) m)
    (hk_confl : ∀ (sem' : FullState) (m' : Mem 64),
      PropLitNoBoundsInv c F0 F_cur s sem' (lit ^^^ 1#32).toNat off_v.toNat (q_v + 1#64).toNat
        (p_v + 1#64).toNat end_v.toNat →
      tend_v.toNat = sem'.core.trail_end → sem'.core.unassigned = sem.core.unassigned →
      sem'.core.unflushed = sem.core.unflushed → Full.PropLitConfl F_cur ignore_ref sem'.core →
      (FullMem c (fastPropMem s sem') ⋆ R) m' →
      wp Γ Q X (k_confl (q_v + 1#64)) m')
    (hk_cont : ∀ (sem' : FullState) (tend_n unass_n unfl_n : BitVec 64) (m' : Mem 64),
      PropLitNoBoundsInv c F0 F_cur s sem' (lit ^^^ 1#32).toNat off_v.toNat (q_v + 1#64).toNat
        (p_v + 1#64).toNat end_v.toNat →
      tend_n.toNat = sem'.core.trail_end → unass_n = sem'.core.unassigned →
      unfl_n = sem'.core.unflushed →
      sem'.core.lvl[(lit ^^^ 1#32).toNat / 2]?.getD 0#32 = nl_lvl0 →
      sem'.core.oom = 0#64 → sem'.core.confl_type = s.core.confl_type →
      (FullMem c (fastPropMem s sem') ⋆ R) m' →
      wp Γ Q X (k_cont (ticks_v + 1#64) tend_n unass_n unfl_n (q_v + 1#64)) m') :
    wp Γ Q X (noBoundsBinBranchExpr c.hdr c.pWstk c.pVals c.pFlags c.pLevel c.pReason
      c.pTrailPos c.pTrail c.pPhases q_v tend_v unass_v unfl_v ticks_v
      w0_v (w0_v &&& 0x7FFFFFFF#32) (lit ^^^ 1#32) nl_lvl0
      (((lit ^^^ 1#32) &&& 0x7FFFFFFF#32) ||| 0x80000000#32) rec_ph k_confl k_cont) m := by
  have hpi := hnb.prop
  have hwstk_len := hpi.len.core_ok.wstk_len_arr
  have hq_le := hpi.sw.q_le_p
  have hp_rem_pos : 0 < end_v.toNat - p_v.toNat := Nat.sub_pos_of_lt hp_lt
  have hlen_mem := fastPropMem_lengthsOk hlen0 hpi.len hpi.cur_vars_eq
    (hpi.ag.get FullCoreState.propagated) rfl
  have hm_wstk := hlen_mem.core_ok.wstk_len_arr
  have hm_vals := hlen_mem.core_ok.vals_len
  have hq_lt_mem_ws : q_v.toNat < (fastPropMem s sem).core.wstk.length :=
    fastPropMem_wstk s sem ▸ hq_lt_ws
  have _hq_lt_cap : q_v.toNat < c.wcap := hwstk_len ▸ hq_lt_ws
  have hwstk_mem : (fastPropMem s sem).core.wstk.length = c.wcap := by
    rw [fastPropMem_wstk]; exact hwstk_len
  obtain ⟨hother_lt, hent, hrem1⟩ :=
    Full.watchSlice_inv_bin hpi.sw.rem_slice hp_rem_pos hw0_get hflag
  obtain ⟨hne_ff, hblk_sb, hrem1_sb⟩ :=
    hnb.sb.rem_slice.inv_bin hp_rem_pos hw0_get hflag
  have hsw_adv := hpi.sw.advance_rem (p' := p_v.toNat + 1) (Nat.le_succ _) hp_lt
    (by simpa [Nat.sub_sub] using hrem1)
  have hsw1 := hsw_adv.write_bin (c := c) hpi.len.core_ok.cur_vars_le hnot_st hq_le
    hq_lt_ws hflag hother_lt hent
  have hsb1 := (hnb.sb.advance_rem (p' := p_v.toNat + 1)
    (by simpa [Nat.sub_sub] using hrem1_sb)).write_bin hsw_adv hnot_st hq_le
    hq_lt_ws hflag hne_ff hblk_sb
  let not_lit : BitVec 32 := lit ^^^ 1#32
  let other := w0_v &&& 0x7FFFFFFF#32
  have hother_lt' : other.toNat < 2 * sem.core.cur_vars := hother_lt
  let wstk1 := sem.core.wstk.set q_v.toNat w0_v
  let sem1 : FullState := { sem with core := { sem.core with wstk := wstk1 } }
  have hlen1 : sem1.LengthsOk c :=
    ⟨{ hpi.len.core_ok with wstk_len_arr := by simp [sem1, wstk1, hwstk_len] },
     hpi.len.scratch_ok⟩
  have hnw1 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c sem1.core) :=
    Full.fullWitnessInv_nw_congr hlen1.core_ok.cur_vars_le hpi.nw
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hother_vals1 : other.toNat < sem1.core.vals.length :=
    fastProp_lt_vals hlen1.core_ok hother_lt'
  unfold dimacsBound at hmaxv
  have hother_vals_2m : other.toNat < 2 * c.max_vars := by
    have := hpi.cur_vars_eq; have := hother_lt; omega
  have hov_nsgt : (0#32).slt ((sem1.core.vals[other.toNat]'hother_vals1).signExtend 32) =
      false := hblk_nsgt hother_lt'
  have hidx_and : w0_v.toNat &&& 2147483647 % 2 ^ 32 = other.toNat := by
    dsimp only [other]; rw [BitVec.toNat_and]; rfl
  have hsb1' : SplitWatchBoundsInv sem1.core not_lit.toNat off_v.toNat
      (q_v + 1#64).toNat (p_v.toNat + 1) end_v.toNat := by
    rw [hq1_nat]; exact hsb1
  unfold noBoundsBinBranchExpr
  nb_head_split
  · nb_head_steps
    have hov_f := Full.propLit_vals_neg hpi.nw hother_lt'
      (fastProp_lt_vals hpi.len.core_ok hother_lt')
      (by simpa only [fastPropMem_vals, hidx_and] using hc)
    have ⟨hpi_c, hcf_c⟩ := Full.propLit_bin_confl (ignore_ref := ignore_ref) hpi hsw1
      hnot_st hother_lt' hent hov_f hp1_nat hq1_nat
    let sem_c : FullState :=
      { sem with core :=
          { sem.core with
            wstk := wstk1, confl_type := 1#64,
            confl_lit0 := not_lit.setWidth 64, confl_lit1 := other.setWidth 64,
            confl_ref := 0xFFFFFFFF#64 } }
    have hsb_c : SplitWatchBoundsInv sem_c.core not_lit.toNat off_v.toNat
        (q_v + 1#64).toNat (p_v.toNat + 1) end_v.toNat :=
      hsb1'.with_nonwatch rfl rfl rfl rfl rfl
    exact hk_confl sem_c m ⟨hpi_c, by rw [hp1_nat]; exact hsb_c⟩ htend_eq rfl rfl hcf_c
      (by simpa only [sem_c, wstk1, not_lit, other, BitVec.ofNat_eq_ofNat,
        fastPropMem_wstk, fastPropMem_with_bin_confl_wstk] using hm)
  · have hov_un : sem1.core.vals[other.toNat]?.getD 0#8 = 0#8 :=
      Full.propLit_vals_un hnw1 hother_lt' hother_vals1 hov_nsgt
        (by simpa only [sem1, fastPropMem_vals, hidx_and] using hc)
    refine fc_let_add rfl rfl ?_
    exact noBoundsBinAssignStep_wp
      (k_next := fun tn un uf => k_cont (ticks_v + 1#64) tn un uf (q_v + 1#64))
      hmaxv hlen0 hcv0 hpi hnb.sb hp_lt hp_lt_w hw0_get hflag rfl hother_lt' hent
      (by simpa [Nat.sub_sub, not_lit] using hrem1) hne_ff (by simpa [Nat.sub_sub] using hrem1_sb)
      hnot_st hq_lt_ws hp1_nat hq1_nat hov_un hnl_eq htend_eq hoom_st hct_st
      (by simpa only [wstk1, BitVec.ofNat_eq_ofNat, fastPropMem_wstk,
        fastPropMem_with_wstk] using hm) hk_cont

private def noBoundsJ6BodyExpr
    (h_p ignore_ref cbase pAr pWvec pWstk vals_p fl_p lvl_p rsns_p tpos_p trl_p ph_p
      off_v p2_v q_v end_v tend_v unass_v unfl_v ticks_v : Val i64)
    (ri_f repl_f cref not_lit other w0 nl_lvl cur_lvl csz : Val i32)
    (ov : Val i8) (rec_ph : Val .bool)
    (k_push_ok k_push_oom : Val i64 → Val i64 → Val i64 → Val i64 → Val i64 →
      Expr Val Cont [.bool])
    (k_nr_cont : Val i64 → Val i64 → Val i64 → Val i64 → Val i64 → Expr Val Cont [.bool])
    (k_nr_confl : Val i64 → Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  .let_ (Op.mk (.cmp .ne i32) (.var ri_f, (.imm (4294967295 : BitVec 32), ()))) fun cc =>
  .jnz (.var cc.1) (
    .let_ (Op.mk (.add i64) (.var ticks_v, (.imm (1 : BitVec 64), ()))) fun tk1 =>
    noBoundsLargePushExpr h_p cbase pAr pWvec pWstk off_v p2_v q_v end_v
      ri_f repl_f cref not_lit other w0
      (fun o4 pn qn en => k_push_ok tk1.1 o4 pn qn en)
      (fun o4 pn qn en => k_push_oom tk1.1 o4 pn qn en)
  ) (
    noBoundsLargeNoReplExpr h_p ignore_ref cbase pAr pWstk vals_p fl_p lvl_p rsns_p tpos_p
      trl_p ph_p q_v tend_v unass_v unfl_v ticks_v cref other nl_lvl cur_lvl csz ov rec_ph
      k_nr_cont k_nr_confl
  )

private theorem noBoundsJ6Body_wp {Γ : Env}
    (hPush : ∀ args m Q X, Full.fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s sem1 : FullState}
    {ri_f repl_f not_lit other w0 w0_mem cref nl_lvl0 cur_lvl csz32 : BitVec 32}
    {ov : BitVec 8} {rec_ph : Bool}
    {off_v p_v q_v end_v tend_v unass_v unfl_v ticks_v ignore_ref : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    {k_push_ok k_push_oom : Val i64 → Val i64 → Val i64 → Val i64 → Val i64 →
      Expr Val Cont [.bool]}
    {k_nr_cont : Val i64 → Val i64 → Val i64 → Val i64 → Val i64 → Expr Val Cont [.bool]}
    {k_nr_confl : Val i64 → Expr Val Cont [.bool]}
    (hmaxv : c.max_vars < 2 * dimacsBound) (har : c.arena_cap < 2 * dimacsBound)
    (hwc : c.wcap < 2 * dimacsBound)
    (hlen0 : s.LengthsOk c) (hcv0 : s.core.cur_vars ≤ c.max_vars)
    (hnb1 : PropLitNoBoundsInv c F0 F_cur s sem1 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hlen1_mem : (fastPropMem s sem1).LengthsOk c)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref1 : cref.toNat ∈ fullArenaClauseRefsCore sem1.core)
    (hng1 : fullArenaClauseGarbCore sem1.core cref.toNat = false)
    (hfit1 : cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤ sem1.core.arena_len)
    (hother_lt : other.toNat < 2 * sem1.core.cur_vars)
    (hnot_st1 : not_lit.toNat < 2 * sem1.core.cur_vars)
    (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hw0_eq : w0_mem = w0)
    (hw0_blk : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * sem1.core.cur_vars)
    (hother_mem : other.toNat ∈ fullArenaClauseLitsCore sem1.core cref.toNat)
    (hnot_mem : not_lit.toNat ∈ fullArenaClauseLitsCore sem1.core cref.toNat)
    (hother_lt1_vals : other.toNat < sem1.core.vals.length)
    (hov_eq : ov = sem1.core.vals[other.toNat]'hother_lt1_vals)
    (hov_np : (0#32).slt ((sem1.core.vals[other.toNat]'hother_lt1_vals).signExtend 32) = false)
    (har3 : sem1.core.arena[cref.toNat + 3]? = some other)
    (har4 : sem1.core.arena[cref.toNat + 4]? = some not_lit)
    (hnl1 : sem1.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0)
    (hcur_eq : cur_lvl.toNat = s.core.cur_level) (hclv_lt32 : s.core.cur_level < 2 ^ 32)
    (hcsz32 : csz32.toNat = fullArenaClauseSizeCore sem1.core cref.toNat)
    (_hcsz3_1 : 3 ≤ fullArenaClauseSizeCore sem1.core cref.toNat)
    (h1_idx : (cref.setWidth 64 + 1#64).toNat = cref.toNat + 1)
    (h3_idx : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3)
    (h4_idx : (cref.setWidth 64 + 3#64 + 1#64).toNat = cref.toNat + 4)
    (htend1_eq : tend_v.toNat = sem1.core.trail_end) (hunass1_eq : unass_v = sem1.core.unassigned)
    (hunfl1_eq : unfl_v = sem1.core.unflushed) (hoom1 : sem1.core.oom = 0#64)
    (hct1 : sem1.core.confl_type = s.core.confl_type)
    (hq1_nat : (q_v + 1#64).toNat = q_v.toNat + 1)
    (hq2_nat : (q_v + 2#64).toNat = q_v.toNat + 2)
    (hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2)
    (hq_le : q_v.toNat ≤ p_v.toNat) (hq_lt : q_v.toNat < c.wcap)
    (hq_lt_ws1 : q_v.toNat < sem1.core.wstk.length)
    (hq1_lt_ws1 : q_v.toNat + 1 < sem1.core.wstk.length)
    (hres : (ri_f = 0xFFFFFFFF#32 ∧
      ∀ k, 2 ≤ k → k < fullArenaClauseSizeCore sem1.core cref.toNat →
        Full.FullPropDecSpecs.fullFindReplBad sem1 cref.toNat k) ∨
      (ri_f ≠ 0xFFFFFFFF#32 ∧ 2 ≤ ri_f.toNat ∧
       ∃ hr_lt : ri_f.toNat < fullArenaClauseSizeCore sem1.core cref.toNat,
       repl_f = sem1.core.arena[cref.toNat + 3 + ri_f.toNat]'(by
         rw [hnb1.prop.len.core_ok.arena_len_arr]
         exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hr_lt _)
           (Nat.le_trans hfit1 hnb1.prop.len.core_ok.arena_len_le)) ∧
       repl_f.toNat < 2 * sem1.core.cur_vars ∧
       ((sem1.core.vals[repl_f.toNat]?.getD 0#8).signExtend 32).slt 0#32 = false))
    (hm : (FullMem c (fastPropMem s sem1) ⋆ R) m)
    (hk_push_ok : ∀ (st4 : FullState) (off4_v : BitVec 64) (m_p : Mem 64),
      (off4_v + (end_v - off_v)).toNat -
        (off4_v + (p_v + 1#64 + 1#64 - off_v)).toNat < end_v.toNat - p_v.toNat →
      PropLitNoBoundsInv c F0 F_cur s st4 not_lit.toNat off4_v.toNat
        (off4_v + (q_v - off_v)).toNat (off4_v + (p_v + 1#64 + 1#64 - off_v)).toNat
        (off4_v + (end_v - off_v)).toNat →
      tend_v.toNat = st4.core.trail_end → unass_v = st4.core.unassigned →
      unfl_v = st4.core.unflushed → st4.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 →
      st4.core.oom = 0#64 → st4.core.confl_type = s.core.confl_type →
      (FullMem c (fastPropMem s st4) ⋆ R) m_p →
      wp Γ Q X (k_push_ok (ticks_v + 1#64) off4_v (off4_v + (p_v + 1#64 + 1#64 - off_v))
        (off4_v + (q_v - off_v)) (off4_v + (end_v - off_v))) m_p)
    (hk_push_oom : ∀ (st6 : FullState) (off4_v : BitVec 64) (m_f : Mem 64),
      PropLitNoBoundsInv c F0 F_cur s st6 not_lit.toNat off4_v.toNat
        (off4_v + (q_v - off_v) + 2#64).toNat (off4_v + (p_v + 1#64 + 1#64 - off_v)).toNat
        (off4_v + (end_v - off_v)).toNat →
      tend_v.toNat = st6.core.trail_end → unass_v = st6.core.unassigned →
      unfl_v = st6.core.unflushed → st6.core.oom ≠ 0#64 →
      (FullMem c (fastPropMem s st6) ⋆ R) m_f →
      wp Γ Q X (k_push_oom (ticks_v + 1#64) off4_v (off4_v + (p_v + 1#64 + 1#64 - off_v))
        (off4_v + (q_v - off_v) + 2#64) (off4_v + (end_v - off_v))) m_f)
    (hk_nr_cont : ∀ (sem' : FullState) (tk_n tend_n unass_n unfl_n : BitVec 64) (m' : Mem 64),
      (tk_n = ticks_v ∨ tk_n = ticks_v + 1#64) →
      PropLitNoBoundsInv c F0 F_cur s sem' not_lit.toNat off_v.toNat (q_v + 2#64).toNat
        (p_v.toNat + 2) end_v.toNat →
      tend_n.toNat = sem'.core.trail_end → unass_n = sem'.core.unassigned →
      unfl_n = sem'.core.unflushed → sem'.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 →
      sem'.core.oom = 0#64 → sem'.core.confl_type = s.core.confl_type →
      (FullMem c (fastPropMem s sem') ⋆ R) m' →
      wp Γ Q X (k_nr_cont tk_n tend_n unass_n unfl_n (q_v + 2#64)) m')
    (hk_nr_confl : ∀ (sem' : FullState) (m' : Mem 64),
      PropLitNoBoundsInv c F0 F_cur s sem' not_lit.toNat off_v.toNat (q_v + 2#64).toNat
        (p_v.toNat + 2) end_v.toNat →
      tend_v.toNat = sem'.core.trail_end → unass_v = sem'.core.unassigned →
      unfl_v = sem'.core.unflushed → Full.PropLitConfl F_cur ignore_ref sem'.core →
      (FullMem c (fastPropMem s sem') ⋆ R) m' →
      wp Γ Q X (k_nr_confl (q_v + 2#64)) m') :
    wp Γ Q X (noBoundsJ6BodyExpr c.hdr ignore_ref (cref.setWidth 64 + 3#64) c.pArena c.pWvec
      c.pWstk c.pVals c.pFlags c.pLevel c.pReason c.pTrailPos c.pTrail c.pPhases
      off_v (p_v + 1#64 + 1#64) q_v end_v tend_v unass_v unfl_v ticks_v
      ri_f repl_f cref not_lit other w0_mem nl_lvl0 cur_lvl csz32 ov rec_ph
      k_push_ok k_push_oom k_nr_cont k_nr_confl) m := by
  subst hw0_eq; subst hov_eq
  have hpi1 := hnb1.prop
  have har_len1 : sem1.core.arena_len ≤ sem1.core.arena.length :=
    Nat.le_trans hpi1.len.core_ok.arena_len_le (Nat.le_of_eq hpi1.len.core_ok.arena_len_arr.symm)
  unfold noBoundsJ6BodyExpr
  rcases hres with ⟨rfl, hfind_bad⟩ | ⟨hri_ne, hr2, hr_lt, hrepl_def, hcand⟩
  · have hunit := Full.propLit_hunit hpi1.nw hcr_ref1 hng1
      (hpi1.len.core_ok.arena_len_arr ▸ Nat.le_trans hfit1 hpi1.len.core_ok.arena_len_le)
      har3 har4 hpi1.not_f hfind_bad
    nb_head_steps
    exact noBoundsLargeNoRepl_wp hmaxv har hwc hlen0 hcv0 hnb1 hlen1_mem hcr_lt hcr_ref1 hng1
      hfit1 hother_lt hnot_st1 hother_mem hnot_mem hunit hother_lt1_vals rfl hov_np hnl1
      hcur_eq hclv_lt32 hcsz32 h3_idx htend1_eq hunass1_eq hunfl1_eq hoom1 hct1
      hq1_nat hq2_nat hp2_nat hq_le hq_lt_ws1 hq1_lt_ws1 hm hk_nr_cont hk_nr_confl
  · nb_head_split
    · refine fc_let_add rfl rfl ?_
      exact noBoundsLargePush_wp hPush hmaxv har hlen0 hcv0 hnb1 hlen1_mem hcr_lt hcr_ref1 hfit1
        har4 hnot_st1 hother_lt hflag hw0_blk hr2 hr_lt hrepl_def hcand h1_idx h3_idx h4_idx
        htend1_eq hunass1_eq hunfl1_eq hnl1 hoom1 hct1 hp2_nat hq_le hq_lt hm
        (hk_push_ok · · ·) (hk_push_oom · · ·)
    · exact absurd hc hri_ne

private theorem noBoundsReplAndJ6_wp {Γ : Env}
    (hPush : ∀ args m Q X, Full.fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s sem1 : FullState}
    {not_lit other w0 w0_mem cref srch_v nl_lvl0 cur_lvl csz32 : BitVec 32}
    {ov : BitVec 8} {rec_ph : Bool}
    {off_v p_v q_v end_v tend_v unass_v unfl_v ticks_v ignore_ref : BitVec 64}
    {R : Mem 64 → Prop} {mj : Mem 64} {Q : Post [.bool]} {X : XPost}
    {k_push_ok k_push_oom : Val i64 → Val i64 → Val i64 → Val i64 → Val i64 →
      Expr Val Cont [.bool]}
    {k_nr_cont : Val i64 → Val i64 → Val i64 → Val i64 → Val i64 → Expr Val Cont [.bool]}
    {k_nr_confl : Val i64 → Expr Val Cont [.bool]}
    (hmaxv : c.max_vars < 2 * dimacsBound) (har : c.arena_cap < 2 * dimacsBound)
    (hwc : c.wcap < 2 * dimacsBound)
    (hlen0 : s.LengthsOk c) (hcv0 : s.core.cur_vars ≤ c.max_vars)
    (hnb1 : PropLitNoBoundsInv c F0 F_cur s sem1 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hlen1_mem : (fastPropMem s sem1).LengthsOk c)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref1 : cref.toNat ∈ fullArenaClauseRefsCore sem1.core)
    (hng1 : fullArenaClauseGarbCore sem1.core cref.toNat = false)
    (hfit1 : cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤ sem1.core.arena_len)
    (hother_lt : other.toNat < 2 * sem1.core.cur_vars)
    (hnot_st1 : not_lit.toNat < 2 * sem1.core.cur_vars)
    (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hw0_eq : w0_mem = w0)
    (hw0_blk : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * sem1.core.cur_vars)
    (hother_mem : other.toNat ∈ fullArenaClauseLitsCore sem1.core cref.toNat)
    (hother_lt1_vals : other.toNat < sem1.core.vals.length)
    (hov_eq : ov = sem1.core.vals[other.toNat]'hother_lt1_vals)
    (hov_np : (0#32).slt ((sem1.core.vals[other.toNat]'hother_lt1_vals).signExtend 32) = false)
    (har3 : sem1.core.arena[cref.toNat + 3]? = some other)
    (har4 : sem1.core.arena[cref.toNat + 4]? = some not_lit)
    (hnl1 : sem1.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0)
    (hcur_eq : cur_lvl.toNat = s.core.cur_level) (hclv_lt32 : s.core.cur_level < 2 ^ 32)
    (hcsz32 : csz32.toNat = fullArenaClauseSizeCore sem1.core cref.toNat)
    (hcsz3_1 : 3 ≤ fullArenaClauseSizeCore sem1.core cref.toNat)
    (h1_idx : (cref.setWidth 64 + 1#64).toNat = cref.toNat + 1)
    (h3_idx : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3)
    (h4_idx : (cref.setWidth 64 + 3#64 + 1#64).toNat = cref.toNat + 4)
    (hsrch2 : 2 ≤ srch_v.toNat)
    (hsrch_lt : srch_v.toNat < fullArenaClauseSizeCore sem1.core cref.toNat)
    (htend1_eq : tend_v.toNat = sem1.core.trail_end) (hunass1_eq : unass_v = sem1.core.unassigned)
    (hunfl1_eq : unfl_v = sem1.core.unflushed) (hoom1 : sem1.core.oom = 0#64)
    (hct1 : sem1.core.confl_type = s.core.confl_type)
    (hq1_nat : (q_v + 1#64).toNat = q_v.toNat + 1)
    (hq2_nat : (q_v + 2#64).toNat = q_v.toNat + 2)
    (hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2)
    (hq_le : q_v.toNat ≤ p_v.toNat) (hq_lt : q_v.toNat < c.wcap)
    (hq_lt_ws1 : q_v.toNat < sem1.core.wstk.length)
    (hq1_lt_ws1 : q_v.toNat + 1 < sem1.core.wstk.length)
    (hmj : (FullMem c (fastPropMem s sem1) ⋆ R) mj)
    (hk_push_ok : ∀ (st4 : FullState) (off4_v : BitVec 64) (m_p : Mem 64),
      (off4_v + (end_v - off_v)).toNat -
        (off4_v + (p_v + 1#64 + 1#64 - off_v)).toNat < end_v.toNat - p_v.toNat →
      PropLitNoBoundsInv c F0 F_cur s st4 not_lit.toNat off4_v.toNat
        (off4_v + (q_v - off_v)).toNat (off4_v + (p_v + 1#64 + 1#64 - off_v)).toNat
        (off4_v + (end_v - off_v)).toNat →
      tend_v.toNat = st4.core.trail_end → unass_v = st4.core.unassigned →
      unfl_v = st4.core.unflushed → st4.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 →
      st4.core.oom = 0#64 → st4.core.confl_type = s.core.confl_type →
      (FullMem c (fastPropMem s st4) ⋆ R) m_p →
      wp Γ Q X (k_push_ok (ticks_v + 1#64) off4_v (off4_v + (p_v + 1#64 + 1#64 - off_v))
        (off4_v + (q_v - off_v)) (off4_v + (end_v - off_v))) m_p)
    (hk_push_oom : ∀ (st6 : FullState) (off4_v : BitVec 64) (m_f : Mem 64),
      PropLitNoBoundsInv c F0 F_cur s st6 not_lit.toNat off4_v.toNat
        (off4_v + (q_v - off_v) + 2#64).toNat (off4_v + (p_v + 1#64 + 1#64 - off_v)).toNat
        (off4_v + (end_v - off_v)).toNat →
      tend_v.toNat = st6.core.trail_end → unass_v = st6.core.unassigned →
      unfl_v = st6.core.unflushed → st6.core.oom ≠ 0#64 →
      (FullMem c (fastPropMem s st6) ⋆ R) m_f →
      wp Γ Q X (k_push_oom (ticks_v + 1#64) off4_v (off4_v + (p_v + 1#64 + 1#64 - off_v))
        (off4_v + (q_v - off_v) + 2#64) (off4_v + (end_v - off_v))) m_f)
    (hk_nr_cont : ∀ (sem' : FullState) (tk_n tend_n unass_n unfl_n : BitVec 64) (m' : Mem 64),
      (tk_n = ticks_v ∨ tk_n = ticks_v + 1#64) →
      PropLitNoBoundsInv c F0 F_cur s sem' not_lit.toNat off_v.toNat (q_v + 2#64).toNat
        (p_v.toNat + 2) end_v.toNat →
      tend_n.toNat = sem'.core.trail_end → unass_n = sem'.core.unassigned →
      unfl_n = sem'.core.unflushed → sem'.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 →
      sem'.core.oom = 0#64 → sem'.core.confl_type = s.core.confl_type →
      (FullMem c (fastPropMem s sem') ⋆ R) m' →
      wp Γ Q X (k_nr_cont tk_n tend_n unass_n unfl_n (q_v + 2#64)) m')
    (hk_nr_confl : ∀ (sem' : FullState) (m' : Mem 64),
      PropLitNoBoundsInv c F0 F_cur s sem' not_lit.toNat off_v.toNat (q_v + 2#64).toNat
        (p_v.toNat + 2) end_v.toNat →
      tend_v.toNat = sem'.core.trail_end → unass_v = sem'.core.unassigned →
      unfl_v = sem'.core.unflushed → Full.PropLitConfl F_cur ignore_ref sem'.core →
      (FullMem c (fastPropMem s sem') ⋆ R) m' →
      wp Γ Q X (k_nr_confl (q_v + 2#64)) m') :
    wp Γ Q X (noBoundsReplSearchExpr srch_v csz32 (cref.setWidth 64 + 3#64) c.pArena c.pVals
      (fun (ri_f, repl_f, _) =>
        noBoundsJ6BodyExpr c.hdr ignore_ref (cref.setWidth 64 + 3#64) c.pArena c.pWvec
          c.pWstk c.pVals c.pFlags c.pLevel c.pReason c.pTrailPos c.pTrail c.pPhases
          off_v (p_v + 1#64 + 1#64) q_v end_v tend_v unass_v unfl_v ticks_v
          ri_f repl_f cref not_lit other w0_mem nl_lvl0 cur_lvl csz32 ov rec_ph
          k_push_ok k_push_oom k_nr_cont k_nr_confl)) mj := by
  have hpi1 := hnb1.prop
  have haren1 := hpi1.len.core_ok.arena_len_arr
  have halen1_le := hpi1.len.core_ok.arena_len_le
  have hcr4_lt_ar1 : cref.toNat + 4 < sem1.core.arena.length := by
    rw [haren1]
    exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans hfit1 halen1_le)
  have hnot_mem : not_lit.toNat ∈ fullArenaClauseLitsCore sem1.core cref.toNat := by
    refine (mem_fullArenaClauseLitsCore_iff (haren1 ▸ Nat.le_trans hfit1 halen1_le)).mpr
      ⟨1, Nat.lt_of_lt_of_le (by decide : 1 < 3) hcsz3_1, ?_⟩
    exact congrArg BitVec.toNat (Option.some.inj
      ((List.getElem?_eq_getElem hcr4_lt_ar1).symm.trans har4))
  refine noBoundsReplSearch_wp hmaxv har hcv0 hpi1 hlen1_mem hcr_ref1 hng1 hfit1
    h3_idx hcsz32 hsrch2 hsrch_lt hmj ?_
  intro ri_f repl_f _rf hres_f
  exact noBoundsJ6Body_wp hPush hmaxv har hwc hlen0 hcv0 hnb1 hlen1_mem hcr_lt hcr_ref1 hng1
    hfit1 hother_lt hnot_st1 hflag hw0_eq hw0_blk hother_mem hnot_mem hother_lt1_vals hov_eq
    hov_np har3 har4 hnl1 hcur_eq hclv_lt32 hcsz32 hcsz3_1 h1_idx h3_idx h4_idx htend1_eq
    hunass1_eq hunfl1_eq hoom1 hct1 hq1_nat hq2_nat hp2_nat hq_le hq_lt hq_lt_ws1 hq1_lt_ws1
    hres_f hmj hk_push_ok hk_push_oom hk_nr_cont hk_nr_confl

/-! ## 2. Parametric `(Γ : Env)` `Func.wp` Contracts & UNSAT Soundness -/

theorem full_prop_lit_nobounds_m7_wp (Γ : Env)
    (hPush : ∀ args m Q X, Full.fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullPropLitNoBoundsSpec args m Q X →
      Func.wp Γ full_prop_lit_nobounds_m7_body args m Q X := by
  rintro ⟨h, lit, ignore_ref, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hwb0, hdense0, hoom0, hm, hQ⟩
  have hmaxv := c.hmaxv; have har := c.harena; have hwc := c.hwcap
  unfold dimacsBound at hmaxv har hwc
  have hcv0 := hlen0.core_ok.cur_vars_le
  let not_lit : BitVec 32 := lit ^^^ 1#32
  have hret_st : ∀ (ok : Bool) (st : FullState) (ml : Mem 64),
      st.LengthsOk c → FullWitnessInv c F0 F_cur st.core → FullWatchBoundsInv st →
      AgreesExcept Full.propLitCoreMask s.core st.core →
      Full.FullPropDecSpecs.FullTrailExt s.core st.core →
      Full.FullPropDecSpecs.FullArenaPermEq s.core st.core →
      st.scratch = { s.scratch with
        search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
        phases := st.scratch.phases } →
      (ok = false → Full.PropLitConfl F_cur ignore_ref st.core) →
      (ok = true → st.core.oom = 0#64 ∧ st.core.confl_type = s.core.confl_type) →
      (FullMem c st ⋆ R) ml → Q (ok, ()) ml := by
    intro ok st ml hst_l hst_w hst_wb hag htr hperm hsc hcf hok_oom hml
    have hst_eq := Full.propLit_eq_upd hag hsc
    have hst_l' := hst_l; have hst_w' := hst_w; have hst_wb' := hst_wb
    have htr' := htr
    have hperm' := hperm
    rw [hst_eq] at hst_l' hst_w' hst_wb' htr' hperm' hml
    refine hQ ok st.core.vals st.core.flags st.core.lvl st.core.rsns st.core.trl st.core.trail_pos
      st.core.trail_end st.core.unassigned st.core.unflushed st.core.wvec st.core.arena
      st.core.wstk st.core.wlen st.core.wusable st.core.confl_type st.core.confl_ref
      st.core.confl_lit0 st.core.confl_lit1 st.core.oom st.scratch.search_ticks st.scratch.wsort
      st.scratch.phases ml hst_l' hst_w' hst_wb' htr' hperm' ?_ hok_oom hml
    intro hf; rcases (hcf hf) with ho | ⟨hc1, hc2⟩
    · exact Or.inl ho
    · refine Or.inr ⟨?_, hc2⟩
      have hc1' : Full.FullConflictOkW F_cur st := fullConflOkW_to_fullConflictOkW hc1
      rwa [hst_eq] at hc1'
  have hret_noop : Q (true, ()) m :=
    hret_st true s m hlen0 hw0 hwb0 (.refl _ _) (.refl _) (.refl _) rfl (by simp)
      (fun _ => ⟨hoom0, rfl⟩) hm
  have hvl0 := hlen0.core_ok.vals_len; have hwv0 := hlen0.core_ok.wvec_len
  have hlvl0 := hlen0.core_ok.lvl_len
  have hclv_lt32 : s.core.cur_level < 2 ^ 32 := by
    have := hw0.cur_level_le; have := hlen0.core_ok.trail_end_le; omega
  have hte0_lt64 : s.core.trail_end < 2 ^ 64 := by
    have := hlen0.core_ok.trail_end_le; omega
  unfold Func.wp full_prop_lit_nobounds_m7_body
  nb_head_split
  · exact hret_noop
  · have hnot_xor : not_lit.toNat = lit.toNat ^^^ 1 := bv32_xor_1 lit
    have hnot_arith : not_lit.toNat = lit.toNat + 1 - 2 * (lit.toNat % 2) := by
      rw [hnot_xor, fc_nat_xor_one]; split <;> omega
    have hnot_lt : not_lit.toNat < 2 * s.core.cur_vars := by
      have h1 : ¬ s.core.cur_vars % 2 ^ 64 * 2 ^ 1 % 2 ^ 64 ≤
          lit.toNat + 1 - 2 * (lit.toNat % 2) := by assumption
      rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64), Nat.pow_one,
        Nat.mod_eq_of_lt (by omega : s.core.cur_vars * 2 < 2 ^ 64)] at h1
      omega
    have hnot_2m : (lit ^^^ 1#32).toNat < 2 * c.max_vars := by
      change not_lit.toNat < 2 * c.max_vars; omega
    have hnot_2m_arith : lit.toNat + 1 - 2 * (lit.toNat % 2) < 2 * c.max_vars := by
      omega
    nb_head_split
    · exact hret_noop
    have hnot_f0 : s.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 := by
      have hsge :
          (0#32).sle ((s.core.vals[not_lit.toNat]'(by omega)).signExtend 32) = false := by
        simpa only [← hnot_arith] using hc
      rw [bv32_sle0_eq_not_slt0, Bool.not_eq_false'] at hsge
      have hget :
          s.core.vals[not_lit.toNat]?.getD 0#8 = s.core.vals[not_lit.toNat]'(by omega) := by
        simp [List.getElem?_eq_getElem (show not_lit.toNat < s.core.vals.length by omega)]
      rw [hget]
      exact (Full.full_i8_vals_slt0 (by rw [← hget]; exact hw0.vals_domain _ hnot_lt)).mp hsge
    clear hc
    nb_head_split
    · exact hret_noop
    have hidx0 : ((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)).toNat =
        2 * not_lit.toNat := bv64_shl1_u32 not_lit
    have hidx1 : (((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)) +
        (1 : BitVec 64)).toNat = 2 * not_lit.toNat + 1 := by
      rw [bv64_add1_no_ovf (by rw [hidx0]; omega), hidx0]
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
      have hne0 : (s.core.wvec[(((lit ^^^ (1 : BitVec 32)).setWidth 64 <<< (1 : BitVec 64)) +
          (1 : BitVec 64)).toNat]'(by omega)).setWidth 64 ≠ 0#64 := fun heq => hc (by
        change (s.core.wvec[((lit.toNat + 1 - 2 * (lit.toNat % 2)) * 2 ^ 1 + 1) % 2 ^ 64]'
          (by omega)).setWidth 64 = 0#64
        rw [← heq]; congr 4; rw [hidx0, ← hnot_arith, Nat.pow_one]; omega)
      exact Nat.pos_of_ne_zero fun h0 =>
        hne0 (BitVec.eq_of_toNat_eq (by rw [bv_c0_zext32_64, h0]; rfl))
    clear hc
    have hwat0 : Full.WatchesInv F_cur s.core := by
      have h := hw0.watches; unfold Full.ModeWatchesInv at h; simpa [hdense0] using h
    have hnw0 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c s.core) :=
      Full.fullWitnessInv_to_nw hcv0 hw0
    have hnb0 : PropLitNoBoundsInv c F0 F_cur s s not_lit.toNat
        (fullWatchOffCore s.core not_lit.toNat) (fullWatchOffCore s.core not_lit.toNat)
        (fullWatchOffCore s.core not_lit.toNat)
        (fullWatchOffCore s.core not_lit.toNat + fullWatchSizeCore s.core not_lit.toNat) :=
      { prop :=
          { len := hlen0, nw := hnw0, sw := Full.SplitWatchesInv.init hnot_lt hwat0 hsz0_pos
            ag := .refl _ _, tr := .refl _, perm := .refl _, sc_eq := rfl, not_f := hnot_f0 }
        sb := SplitWatchBoundsInv.init hwb0 hdense0 hnot_lt }
    have hnl_lvl_idx :
        (BitVec.setWidth 64 ((lit ^^^ (1 : BitVec 32)) >>> (1 : Nat))).toNat <
          s.core.lvl.length := by
      rw [bv_c0_zext32_64, bv32_lshr_1, bv32_xor_1, hlen0.core_ok.lvl_len]; omega
    let nl_lvl0 :=
      s.core.lvl[(BitVec.setWidth 64 ((lit ^^^ (1 : BitVec 32)) >>> (1 : Nat))).toNat]'
        hnl_lvl_idx
    have hnl_eq0 : s.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 := by
      have hidx : (BitVec.setWidth 64 ((lit ^^^ (1 : BitVec 32)) >>> (1 : Nat))).toNat =
          not_lit.toNat / 2 := by
        rw [bv_c0_zext32_64, bv32_lshr_1]; rfl
      rw [← hidx, List.getElem?_eq_getElem hnl_lvl_idx, Option.getD_some]
    c0_hsteps_nogrp
    · exact hret_noop
    refine wp_loop_break_group
      (brkTs := [i64, i64, i64, i64, i64, i64, i64, i64, .bool])
      (lpTs := [i64, i64, i64, i64, i64, i64, i64, i64])
      (fun (off_v, end_v, tend_v, unass_v, unfl_v, ticks_v, p_v, q_v, confl_v, ()) mb =>
        ∃ sem : FullState,
          PropLitNoBoundsInv c F0 F_cur s sem not_lit.toNat off_v.toNat q_v.toNat p_v.toNat
            end_v.toNat ∧
          tend_v.toNat = sem.core.trail_end ∧ unass_v = sem.core.unassigned ∧
          unfl_v = sem.core.unflushed ∧
          (confl_v = false → sem.core.oom = 0#64 ∧ sem.core.confl_type = s.core.confl_type) ∧
          (confl_v = true → Full.PropLitConfl F_cur ignore_ref sem.core) ∧
          (FullMem c (fastPropMem s sem) ⋆ R) mb)
      (fun rem (off_v, end_v, tend_v, unass_v, unfl_v, ticks_v, p_v, q_v, ()) ml =>
        ∃ sem : FullState,
          rem = end_v.toNat - p_v.toNat ∧
          PropLitNoBoundsInv c F0 F_cur s sem not_lit.toNat off_v.toNat q_v.toNat p_v.toNat
            end_v.toNat ∧
          tend_v.toNat = sem.core.trail_end ∧ unass_v = sem.core.unassigned ∧
          unfl_v = sem.core.unflushed ∧
          sem.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 ∧
          sem.core.oom = 0#64 ∧ sem.core.confl_type = s.core.confl_type ∧
          (FullMem c (fastPropMem s sem) ⋆ R) ml) ?_ ?_ ?_
    · rintro _ ⟨off_v, end_v, tend_v, unass_v, unfl_v, ticks_v, p_v, q_v, confl_v, ⟨⟩⟩ mb
        ⟨sem, hnb, htend_eq, hunass_eq, hunfl_eq, hcf_f, hcf_t, hmb⟩
      exact m7NoBoundsFinish_wp c.hwcap hcv0 hdense0 hnot_lt hnb htend_eq hunass_eq
        hunfl_eq hcf_f hcf_t hmb fun ok st ml hl hw hwb hag htr hperm hsc hcf hoom hml =>
        hret_st ok st ml hl hw hwb hag htr hperm hsc hcf hoom hml
    · rintro B L rem ⟨off_v, end_v, tend_v, unass_v, unfl_v, ticks_v, p_v, q_v, ⟨⟩⟩ ml hB ih
        ⟨sem, rfl, hnb, htend_eq, hunass_eq, hunfl_eq, hnl_eq, hoom_st, hct_st, hml⟩
      have hpi := hnb.prop
      have hcv_eq : sem.core.cur_vars = s.core.cur_vars := hpi.cur_vars_eq
      have hnot_st : not_lit.toNat < 2 * sem.core.cur_vars := hcv_eq.symm ▸ hnot_lt
      clear hret_noop hoff0_eq hsz0_eq hsz0_pos hnb0 hnw0 hnot_f0 hm hw0 hwat0 hwb0
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
        bv64_add1_no_ovf (Nat.lt_of_le_of_lt
          (Nat.add_le_add_right (Nat.le_trans hp_le hend_wcap) 1) hwc64)
      nb_head_split
      · have hp_lt : p_v.toNat < end_v.toNat := by assumption
        have hp_lt_w : p_v.toNat < sem.core.wstk.length :=
          hwstk_len ▸ Nat.lt_of_lt_of_le hp_lt hend_wcap
        have hp_rem_pos : 0 < end_v.toNat - p_v.toNat := Nat.sub_pos_of_lt hp_lt
        have hp1_nat : (p_v + 1#64).toNat = p_v.toNat + 1 := hp1_pre
        have hq1_nat : (q_v + 1#64).toNat = q_v.toNat + 1 :=
          bv64_add1_no_ovf (Nat.lt_of_le_of_lt
            (Nat.add_le_add_right (Nat.le_trans hq_le (Nat.le_trans hp_le hend_wcap)) 1) hwc64)
        have hq_lt_ws : q_v.toNat < sem.core.wstk.length :=
          hwstk_len ▸ Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hq_le hp_lt) hend_wcap
        let w0_v := sem.core.wstk[p_v.toNat]'hp_lt_w
        have hw0_get : sem.core.wstk[p_v.toNat]? = some w0_v := List.getElem?_eq_getElem hp_lt_w
        have hblk_lt_sem : (w0_v &&& 0x7FFFFFFF#32).toNat < 2 * sem.core.cur_vars :=
          hnb.sb.rem_slice.head_blk_lt hp_rem_pos hw0_get
        have hblk_vals : (w0_v &&& 0x7FFFFFFF#32).toNat < sem.core.vals.length :=
          fastProp_lt_vals hpi.len.core_ok hblk_lt_sem
        have hblk_vals_mem : (BitVec.setWidth 64
            ((fastPropMem s sem).core.wstk[p_v.toNat]'(fastPropMem_wstk s sem ▸ hp_lt_w) &&&
              2147483647)).toNat < (fastPropMem s sem).core.vals.length := by
          dsimp only [w0_v] at hblk_vals
          simp only [bv_c0_zext32_64, fc_getElem_wstk, fastPropMem_vals]
          exact hblk_vals
        nb_head_split
        · rw [fc_getElem_wstk]
          let k_bin : Val i64 → Expr Val Cont [.bool] := fun q1 =>
            .jump L (.var off_v, (.var end_v, (.var tend_v, (.var unass_v,
              (.var unfl_v, (.var ticks_v, (.var (p_v + 1#64), (.var q1, ()))))))))
          let k_large : Val i64 → Val i64 → Expr Val Cont [.bool] := fun p2 q2 =>
            .jump L (.var off_v, (.var end_v, (.var tend_v, (.var unass_v,
              (.var unfl_v, (.var ticks_v, (.var p2, (.var q2, ()))))))))
          refine noBoundsValsGt0_wp (k_bin := k_bin) (k_large := k_large)
            hwc hlen0 hnb hend_wcap hp_lt hp_lt_w hw0_get hnot_st hp1_nat hq1_nat hml ?_ ?_
          · intro sem1 m1 hrem1 _hp1 hnb1 hte1 hun1 huf1 hnl1 hoom1 hct1 hm1
            exact ih _ (off_v, end_v, tend_v, unass_v, unfl_v, ticks_v, p_v + 1#64, q_v + 1#64, ())
              m1 hrem1 ⟨sem1, by rw [hp1_nat], hnb1, hte1 ▸ htend_eq, hun1 ▸ hunass_eq,
              huf1 ▸ hunfl_eq, hnl1 ▸ hnl_eq, hoom1 ▸ hoom_st, hct1 ▸ hct_st, hm1⟩
          · intro sem1 m1 hrem2 _hp2 hnb1 hte1 hun1 huf1 hnl1 hoom1 hct1 hm1
            exact ih _ (off_v, end_v, tend_v, unass_v, unfl_v, ticks_v,
                p_v + 1#64 + 1#64, q_v + 2#64, ())
              m1 hrem2 ⟨sem1, by rw [_hp2], hnb1, hte1 ▸ htend_eq, hun1 ▸ hunass_eq,
              huf1 ▸ hunfl_eq, hnl1 ▸ hnl_eq, hoom1 ▸ hoom_st, hct1 ▸ hct_st, hm1⟩
        · have hblk_nsgt : ∀ hlt : (w0_v &&& 0x7FFFFFFF#32).toNat < 2 * sem.core.cur_vars,
              (0#32).slt ((sem.core.vals[(w0_v &&& 0x7FFFFFFF#32).toNat]'(fastProp_lt_vals
                hpi.len.core_ok hlt)).signExtend 32) = false := by
            intro _
            simpa only [w0_v, ← BitVec.ofNat_eq_ofNat, BitVec.toNat_and, fc_getElem_wstk,
              fastPropMem_wstk, fc_getElem_vals, fastPropMem_vals] using hc
          nb_head_split
          · have hflag : (w0_v &&& 0x80000000#32) ≠ 0#32 := by
              simpa only [ne_eq, ← BitVec.ofNat_eq_ofNat, fc_getElem_wstk, fastPropMem_wstk]
                using hc
            rw [fc_getElem_wstk]
            let k_confl : Val i64 → Expr Val Cont [.bool] := fun q1 =>
              .jump B (.var off_v, (.var end_v, (.var tend_v, (.var unass_v,
                (.var unfl_v, (.var ticks_v, (.var (p_v + 1#64), (.var q1, (.imm true, ())))))))))
            let k_cont : Val i64 → Val i64 → Val i64 → Val i64 → Val i64 →
                Expr Val Cont [.bool] := fun tk1 tn un uf q1 =>
              .jump L (.var off_v, (.var end_v, (.var tn, (.var un,
                (.var uf, (.var tk1, (.var (p_v + 1#64), (.var q1, ()))))))))
            refine noBoundsBinBranch_wp (ignore_ref := ignore_ref)
              (k_confl := k_confl) (k_cont := k_cont)
              hmaxv hlen0 hcv0 hnb hp_lt hp_lt_w hw0_get hflag hblk_nsgt hnot_st hq_lt_ws
              hp1_nat hq1_nat hnl_eq htend_eq hoom_st hct_st hml ?_ ?_
            · intro sem_c m' hnb_c hte_c hun_c huf_c hcf_c hm'
              exact hB (off_v, end_v, tend_v, unass_v, unfl_v, ticks_v, p_v + 1#64, q_v + 1#64,
                true, ()) m' ⟨sem_c, hnb_c, hte_c, hun_c ▸ hunass_eq, huf_c ▸ hunfl_eq,
                by simp, fun _ => hcf_c, hm'⟩
            · intro sem' tend_n unass_n unfl_n m' hnb' ht' hu' huf' hnl' hoom' hct' hm'
              exact ih (end_v.toNat - (p_v.toNat + 1)) (off_v, end_v, tend_n, unass_n, unfl_n,
                ticks_v + 1#64, p_v + 1#64, q_v + 1#64, ()) m'
                (by rw [← Nat.sub_sub]; exact Nat.sub_lt hp_rem_pos Nat.zero_lt_one)
                ⟨sem', by rw [hp1_nat], hnb', ht', hu', huf', hnl', hoom', hct', hm'⟩
          · have hflag : (w0_v &&& 0x80000000#32) = 0#32 := by
              simpa only [← BitVec.ofNat_eq_ofNat, fc_getElem_wstk, fastPropMem_wstk] using hc
            obtain ⟨h2le, cref, hcr_get, hcr_lt, hcr_ref, hrem2⟩ :=
              Full.watchSlice_inv_large hpi.sw.rem_slice hp_rem_pos hw0_get hflag
            obtain ⟨_, cref_sb, hcr_get_sb, hblk_sb, hcr_lt_sb, hsz_sb, hfit_sb, hlive_sb,
                hrem2_sb⟩ :=
              hnb.sb.rem_slice.inv_large hp_rem_pos hw0_get hflag
            have hcr_sb_eq : cref_sb = cref := Option.some.inj (hcr_get_sb.symm.trans hcr_get)
            subst cref_sb
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
            have hcr_eq : sem.core.wstk[(p_v + 1#64).toNat]'hcr_idx_lt = cref := by
              have h1 : sem.core.wstk[p_v.toNat + 1]? =
                  some (sem.core.wstk[(p_v + 1#64).toNat]'hcr_idx_lt) := by
                rw [← hp1_nat]; exact List.getElem?_eq_getElem hcr_idx_lt
              exact Option.some.inj (h1.symm.trans hcr_get)
            refine fc_let_mul rfl rfl ?_
            refine fc_let_add rfl rfl ?_
            rw [wp_load]
            refine ⟨_, FullArenaTactics.c0_load_full_wstk (i := p_v + (1 : BitVec 64))
              (by rw [fastPropMem_wstk]; exact hcr_idx_lt) hml, ?_⟩
            rw [show (fastPropMem s sem).core.wstk[(p_v + (1 : BitVec 64)).toNat]'
                (by rw [fastPropMem_wstk]; exact hcr_idx_lt) = cref from
              (fc_getElem_wstk s sem).trans hcr_eq]
            dsimp only
            have hsw_drop : Full.SplitWatchesInv F_cur sem.core not_lit.toNat off_v.toNat q_v.toNat
                (p_v.toNat + 2) end_v.toNat :=
              hpi.sw.advance_rem (p' := p_v.toNat + 2) (by omega) h2_le_end
                (by simpa [Nat.sub_sub] using hrem2)
            have hsb_drop : SplitWatchBoundsInv sem.core not_lit.toNat off_v.toNat q_v.toNat
                (p_v.toNat + 2) end_v.toNat :=
              hnb.sb.advance_rem (p' := p_v.toNat + 2) (by simpa [Nat.sub_sub] using hrem2_sb)
            clear hnb hblk_lt_sem hblk_vals hw0_get hcr_get hrem2 hcr_get_sb
              hcr_lt_sb hrem2_sb hcr_eq
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
            have h3_1_idx : (cref.setWidth 64 + 3#64 + 1#64).toNat = cref.toNat + 4 := by
              rw [bv64_add_toNat (by
                rw [h3_idx, ← hcr64, show (1#64).toNat = 1 from rfl]; exact hcr_u64),
                h3_idx]; rfl
            refine fc_let_add rfl rfl ?_
            refine fc_let_add rfl rfl ?_
            refine fc_let_zext32_64 rfl ?_
            refine fc_let_mul rfl rfl ?_
            refine fc_let_add rfl rfl ?_
            rw [wp_load]
            refine ⟨_, FullArenaTactics.c0_load_full_arena (i := cref.setWidth 64)
              (by rw [fastPropMem_arena, hcr64]; exact hcr0_lt_ar) hml, ?_⟩
            refine fc_let_zext32_64 rfl ?_
            refine fc_let_add rfl rfl ?_
            refine fc_let_mul rfl rfl ?_
            refine fc_let_add rfl rfl ?_
            rw [wp_load]
            refine ⟨_, FullArenaTactics.c0_load_full_arena (i := cref.setWidth 64 + 2#64)
              (by rw [fastPropMem_arena, h2_idx]; exact hcr2_lt_ar) hml, ?_⟩
            refine fc_let_zext32_64 rfl ?_
            refine fc_let_add rfl rfl ?_
            refine fc_let_and rfl rfl ?_
            refine fc_let_ne rfl rfl ?_
            rw [wp_jnz]
            refine ⟨fun _ => ?_, fun hno_garb => ?_⟩
            · rw [wp_jump]
              exact ih _ (off_v, end_v, tend_v, unass_v, unfl_v, ticks_v + 1#64,
                  p_v + 1#64 + 1#64, q_v, ()) ml hrem_dec
                ⟨sem, by rw [hp2_nat],
                  ⟨Full.propLit_inv_drop (ticks' := sem.scratch.search_ticks) hpi hsw_drop hp2_nat,
                   by rw [hp2_nat]; exact hsb_drop⟩,
                  htend_eq, hunass_eq, hunfl_eq, hnl_eq, hoom_st, hct_st, hml⟩
            · have hng_t : fullArenaClauseGarbCore sem.core cref.toNat = false := by
                unfold fullArenaClauseGarbCore fullArenaHdrCore
                have hget : sem.core.arena[cref.toNat]? =
                    some (sem.core.arena[cref.toNat]'hcr0_lt_ar) :=
                  List.getElem?_eq_getElem hcr0_lt_ar
                rw [hget, Option.getD_some]
                have hh' : (sem.core.arena[cref.toNat]'hcr0_lt_ar &&& 524288#32 != 0#32) = false :=
                  by simpa only [Arg.val_var, Arg.val_imm, ← BitVec.ofNat_eq_ofNat,
                    fastPropMem_arena, hcr64] using hno_garb
                rw [hh']
              refine fc_let_mul rfl rfl ?_
              refine fc_let_add rfl rfl ?_
              rw [wp_load]
              refine ⟨_, FullArenaTactics.c0_load_full_arena (i := cref.setWidth 64 + 3#64)
                (by rw [fastPropMem_arena, h3_idx]; exact hcr3_lt_ar) hml, ?_⟩
              refine fc_let_add rfl rfl ?_
              refine fc_let_mul rfl rfl ?_
              refine fc_let_add rfl rfl ?_
              rw [wp_load]
              refine ⟨_, FullArenaTactics.c0_load_full_arena (i := cref.setWidth 64 + 3#64 + 1#64)
                (by rw [fastPropMem_arena, h3_1_idx]; exact hcr4_lt_ar) hml, ?_⟩
              refine wp_join_group
                (fun (other, ()) mj => ∃ sem1 : FullState,
                  PropLitNoBoundsInv c F0 F_cur s sem1 not_lit.toNat off_v.toNat q_v.toNat
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
              · rintro _ ⟨other, ⟨⟩⟩ mj ⟨sem1, hnb1, hoom1, hct1, halen1, hte1_eq, hun1_eq,
                  huf1_eq, hcl1_eq, hnl1, hcr_ref1, hng1, hcsz1, har3, har4, hmj⟩
                have hpi1 := hnb1.prop
                clear hblk_nsgt hpi hsw_drop hsb_drop
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
                have hq1_lt_ws1' : (q_v + 1#64).toNat < sem1.core.wstk.length :=
                  hq1_nat ▸ hq1_lt_ws1
                have hq_mem_ws1 : q_v.toNat < (fastPropMem s sem1).core.wstk.length :=
                  fastPropMem_wstk s sem1 ▸ hq_lt_ws1
                have hq1_mem_ws1 : (q_v + 1#64).toNat < (fastPropMem s sem1).core.wstk.length :=
                  fastPropMem_wstk s sem1 ▸ hq1_lt_ws1'
                have h1_mem_ar1 : (cref.setWidth 64 + 1#64).toNat <
                    (fastPropMem s sem1).core.arena.length := by
                  rw [fastPropMem_arena, h1_idx, haren1]
                  exact Nat.lt_of_lt_of_le (by omega) halen1_le
                have hcsz_eq1 :
                    (sem1.core.arena[(cref.setWidth 64 + 2#64).toNat]'(h2_idx ▸
                      hcr2_lt_ar1)).toNat = fullArenaClauseSizeCore sem1.core cref.toNat := by
                  unfold fullArenaClauseSizeCore
                  rw [List.getElem?_eq_getElem hcr2_lt_ar1, Option.getD_some]
                  exact congrArg BitVec.toNat
                    (fc_getElem_eq_of_idx h2_idx (h2_idx ▸ hcr2_lt_ar1) hcr2_lt_ar1)
                refine fc_let_zext32_64 rfl ?_
                refine fc_let_add rfl rfl ?_
                rw [wp_load]
                refine ⟨_, FullArenaTactics.c0_load_full_vals (i := other.setWidth 64)
                  (by rw [fastPropMem_vals, bv_c0_zext32_64]; exact hother_lt1_vals) hmj, ?_⟩
                nb_head_split
                · have hpi_keep := Full.propLit_inv_keep_large hpi1 hpi1.sw hnot_st1 hq1_nat
                    hq2_nat hp2_nat (Nat.add_le_add_right hq_le 2) hpi1.sw.p_le_end
                    (Full.bv32_mask7f_flag0 other) hcr_lt hcr_ref1
                  have har_len1 : sem1.core.arena_len ≤ sem1.core.arena.length :=
                    Nat.le_trans halen1_le (Nat.le_of_eq haren1.symm)
                  have hwf1 := hpi1.nw.arena.refs_wf cref.toNat hcr_ref1
                  have hsb_keep := hnb1.sb.write_large hpi1.sw hnot_st1 hq_le hq_lt_ws1
                    hq1_lt_ws1 (Full.bv32_mask7f_flag0 other)
                    (Nat.lt_of_le_of_lt (bv32_mask7f_toNat_le (other &&& 0x7FFFFFFF#32))
                      (Nat.lt_of_le_of_lt (bv32_mask7f_toNat_le other) hother_lt))
                    hcr_lt (Nat.le_trans (by decide : 2 ≤ 3) hwf1.2.1) hfit1
                    (fullArenaLiveLitsLt_of_arenaInv hpi1.nw.arena har_len1 hcr_ref1)
                  clear hnb1 hblk_sb hsz_sb hfit_sb hlive_sb hflag h2le
                  nb_head_steps
                  let sem2 : FullState :=
                    { sem1 with core :=
                        { sem1.core with
                          wstk := (sem1.core.wstk.set q_v.toNat (other &&& 0x7FFFFFFF#32)).set
                            (q_v.toNat + 1) cref } }
                  exact ih _ (off_v, end_v, tend_v, unass_v, unfl_v, ticks_v + 1#64,
                      p_v + 1#64 + 1#64, q_v + 2#64, ()) m hrem_dec
                    ⟨sem2, by rw [hp2_nat],
                      ⟨by simpa only [sem2, hq1_nat, hq2_nat, hp2_nat, BitVec.ofNat_eq_ofNat]
                          using hpi_keep,
                       by simpa only [sem2, hq2_nat, hp2_nat] using hsb_keep⟩,
                      htend1_eq, hunass1_eq, hunfl1_eq, hnl1, hoom1, hct1, by
                        simpa only [sem2, hq1_nat, show (1 : BitVec 64) = 1#64 from rfl,
                          BitVec.ofNat_eq_ofNat, fastPropMem_wstk,
                          fastPropMem_with_wstk] using hm⟩
                · have hov_np :
                      (0#32).slt ((sem1.core.vals[other.toNat]'hother_lt1_vals).signExtend 32) =
                        false := by simpa only [fastPropMem_vals, bv_c0_zext32_64] using hc
                  try clear hc; try clear hc
                  nb_head_steps
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
                    have hcur_eq1 :
                        (BitVec.ofNat 64 s.core.cur_level).setWidth 32 =
                          BitVec.ofNat 32 s.core.cur_level := by
                      apply BitVec.eq_of_toNat_eq
                      have hcl64 : s.core.cur_level < 2 ^ 64 := Nat.lt_trans hclv_lt32 (by decide)
                      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl64,
                        Nat.mod_eq_of_lt hclv_lt32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclv_lt32]
                    let k_push_ok : Val i64 → Val i64 → Val i64 → Val i64 → Val i64 →
                        Expr Val Cont [.bool] := fun tk1 o4 pn qn en =>
                      .jump L (.var o4, (.var en, (.var tend_v, (.var unass_v,
                        (.var unfl_v, (.var tk1, (.var pn, (.var qn, ()))))))))
                    let k_push_oom : Val i64 → Val i64 → Val i64 → Val i64 → Val i64 →
                        Expr Val Cont [.bool] := fun tk1 o4 pn qn en =>
                      .jump B (.var o4, (.var en, (.var tend_v, (.var unass_v,
                        (.var unfl_v, (.var tk1, (.var pn, (.var qn, (.imm true, ())))))))))
                    let k_nr_cont : Val i64 → Val i64 → Val i64 → Val i64 → Val i64 →
                        Expr Val Cont [.bool] := fun tk tn un uf qn =>
                      .jump L (.var off_v, (.var end_v, (.var tn, (.var un,
                        (.var uf, (.var tk, (.var (p_v + 1#64 + 1#64), (.var qn, ()))))))))
                    let k_nr_confl : Val i64 → Expr Val Cont [.bool] := fun qn =>
                      .jump B (.var off_v, (.var end_v, (.var tend_v, (.var unass_v,
                        (.var unfl_v, (.var (ticks_v + 1#64),
                        (.var (p_v + 1#64 + 1#64), (.var qn, (.imm true, ())))))))))
                    nb_head_steps
                    have hw0_mem_eq :
                        (fastPropMem s sem).core.wstk[p_v.toNat]'(by
                          rw [fastPropMem_wstk]; exact hp_lt_w) = w0_v :=
                      fc_getElem_wstk s sem
                    have hov_mem_eq :
                        (fastPropMem s sem1).core.vals[(BitVec.setWidth 64 other).toNat]'(by
                          rw [hm1_vals, bv_c0_zext32_64]
                          exact Nat.lt_of_lt_of_le hother_lt
                            (Nat.mul_le_mul_left 2 hpi1.len.core_ok.cur_vars_le)) =
                          sem1.core.vals[other.toNat]'hother_lt1_vals :=
                      (fc_getElem_vals s sem1).trans
                        (fc_getElem_eq_of_idx (bv_c0_zext32_64 other) _ hother_lt1_vals)
                    refine noBoundsReplAndJ6_wp hPush
                      (w0 := w0_v) (ignore_ref := ignore_ref) (ticks_v := ticks_v + 1#64)
                      (cur_lvl := (BitVec.ofNat 64 s.core.cur_level).setWidth 32)
                      (csz32 := csz32) (rec_ph := s.core.probing == 0#64)
                      (k_push_ok := k_push_ok) (k_push_oom := k_push_oom)
                      (k_nr_cont := k_nr_cont) (k_nr_confl := k_nr_confl)
                      c.hmaxv c.harena c.hwcap hlen0 hcv0 hnb1 hlen1_mem hcr_lt
                      hcr_ref1 hng1 hfit1 hother_lt hnot_st1 hflag hw0_mem_eq
                      (by rw [hpi1.cur_vars_eq, ← hcv_eq]; exact hblk_sb)
                      hother_mem hother_lt1_vals hov_mem_eq hov_np har3 har4 hnl1
                      (by rw [hcur_eq1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclv_lt32])
                      hclv_lt32 hcsz32_nat hcsz3_1 h1_idx h3_idx h3_1_idx hsrch2 hsrch_lt
                      htend1_eq hunass1_eq hunfl1_eq hoom1 hct1 hq1_nat hq2_nat hp2_nat
                      hq_le (hwstk1 ▸ hq_lt_ws1) hq_lt_ws1 hq1_lt_ws1 hmj ?_ ?_ ?_ ?_
                    · intro st4 off4_v m_p hdec4 hnb4 ht4 hu4 huf4 hnl4 hoom4 hct4 hm4
                      exact ih _ (off4_v, off4_v + (end_v - off_v), tend_v, unass_v, unfl_v,
                        ticks_v + 1#64 + 1#64, off4_v + (p_v + 1#64 + 1#64 - off_v),
                        off4_v + (q_v - off_v), ()) m_p hdec4
                        ⟨st4, rfl, hnb4, ht4, hu4, huf4, hnl4, hoom4, hct4, hm4⟩
                    · intro st6 off4_v m_f hnb6 ht6 hu6 huf6 hoom6 hm6
                      exact hB (off4_v, off4_v + (end_v - off_v), tend_v, unass_v, unfl_v,
                        ticks_v + 1#64 + 1#64, off4_v + (p_v + 1#64 + 1#64 - off_v),
                        off4_v + (q_v - off_v) + 2#64, true, ()) m_f
                        ⟨_, hnb6, ht6, hu6, huf6, by simp, fun _ => Or.inl hoom6, hm6⟩
                    · intro sem' tk_n tn un uf m' _htk hnb' ht' hu' huf' hnl' hoom' hct' hm'
                      exact ih _ (off_v, end_v, tn, un, uf, tk_n,
                        p_v + 1#64 + 1#64, q_v + 2#64, ()) m' hrem_dec
                        ⟨sem', by rw [hp2_nat], by rwa [hp2_nat], ht', hu', huf', hnl',
                          hoom', hct', hm'⟩
                    · intro sem' m' hnb' ht' hu' huf' hcf' hm'
                      exact hB (off_v, end_v, tend_v, unass_v, unfl_v, ticks_v + 1#64,
                        p_v + 1#64 + 1#64, q_v + 2#64, true, ()) m'
                        ⟨sem', by
                            simpa only [hq1_nat, hp2_nat, hq2_nat,
                              show (lit ^^^ (1 : BitVec 32)) = not_lit from rfl] using hnb',
                          ht', hu', huf', by simp, fun _ => hcf', hm'⟩
                  · intro Jsrch hJsrch; nb_head_steps
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
                          simpa only [BitVec.reduceToNat, fc_getElem_arena,
                            fastPropMem_arena] using hc
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
              · intro J3 hJ3
                clear hblk_nsgt hblk_sb hsz_sb hfit_sb hlive_sb hflag h2le
                have h3_mem_ar : (cref.setWidth 64 + 3#64).toNat <
                    (fastPropMem s sem).core.arena.length := by
                  rw [fastPropMem_arena, h3_idx]; exact hcr3_lt_ar
                have h31_mem_ar : (cref.setWidth 64 + 3#64 + 1#64).toNat <
                    (fastPropMem s sem).core.arena.length := by
                  rw [fastPropMem_arena, h3_1_idx]; exact hcr4_lt_ar
                nb_head_steps
                · let l1 := sem.core.arena[(cref.setWidth 64 + 4#64).toNat]'(h4_idx ▸ hcr4_lt_ar)
                  have h3_mod : (cref.toNat + BitVec.toNat (3 : BitVec 64)) % 2 ^ 64 =
                      cref.toNat + 3 := by
                    simp only [BitVec.reduceToNat]; exact Nat.mod_eq_of_lt hcr3_lt64
                  have hl0_is_not : sem.core.arena[cref.toNat + 3]'hcr3_lt_ar = not_lit :=
                    (fc_getElem_eq_of_idx h3_mod _ _).symm.trans
                      ((fc_getElem_arena s sem).symm.trans hc)
                  have hpi_drop : Full.PropLitInv c F0 F_cur s sem not_lit.toNat off_v.toNat
                      q_v.toNat (p_v.toNat + 2) end_v.toNat :=
                    ⟨hpi.len, hpi.nw, hsw_drop, hpi.ag, hpi.tr, hpi.perm, hpi.sc_eq,
                     hpi.not_f⟩
                  have ⟨hpi1, href1, hng1, hcsz1, har3, har4⟩ := fastProp_js3_swap hpi_drop
                    hcr_ref hng_t hcsz3 hcr_fit hl0_is_not
                    (fc_getElem_eq_of_idx h4_idx.symm hcr4_lt_ar (h4_idx ▸ hcr4_lt_ar))
                  have hsb1 : SplitWatchBoundsInv { sem.core with
                        arena := (sem.core.arena.set (cref.toNat + 3) l1).set
                          (cref.toNat + 4) not_lit }
                      not_lit.toNat off_v.toNat q_v.toNat (p_v.toNat + 2) end_v.toNat :=
                    hsb_drop.reconstruct_of_nw_arenaInv hpi1.sw hpi1.nw.arena
                      (Nat.le_trans hpi1.len.core_ok.arena_len_le
                        (Nat.le_of_eq hpi1.len.core_ok.arena_len_arr.symm)) rfl rfl rfl
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
                  rw [hl1_mem_eq]
                  exact hJ3 (l1, ()) _ ⟨_, ⟨hpi1, hsb1⟩, hoom_st, hct_st, rfl, rfl, rfl, rfl, rfl,
                    hnl_eq, href1, hng1, hcsz1, har3, har4, hm1⟩
                · exact ih _ (off_v, end_v, tend_v, unass_v, unfl_v, ticks_v + 1#64,
                      p_v + 1#64 + 1#64, q_v, ()) ml hrem_dec
                    ⟨sem, by rw [hp2_nat],
                      ⟨Full.propLit_inv_drop (ticks' := sem.scratch.search_ticks) hpi hsw_drop
                        hp2_nat, by rw [hp2_nat]; exact hsb_drop⟩,
                      htend_eq, hunass_eq, hunfl_eq, hnl_eq, hoom_st, hct_st, hml⟩
                · let l0 := sem.core.arena[(cref.setWidth 64 + 3#64).toNat]'(h3_idx ▸ hcr3_lt_ar)
                  have hl0_idx : sem.core.arena[cref.toNat + 3]? = some l0 := by
                    rw [List.getElem?_eq_getElem hcr3_lt_ar]
                    exact congrArg some (fc_getElem_eq_of_idx h3_idx.symm _ _)
                  have hl1_eq : sem.core.arena[cref.toNat + 4]? = some not_lit := by
                    rw [List.getElem?_eq_getElem hcr4_lt_ar]
                    have h3_1_idx : (cref.setWidth 64 + 3#64 + 1#64).toNat = cref.toNat + 4 := by
                      rw [bv64_add_toNat (by
                        rw [h3_idx, ← hcr64, show (1#64).toNat = 1 from rfl]; exact hcr_u64),
                        h3_idx]; rfl
                    have hl1_mem_eq :
                        (fastPropMem s sem).core.arena[
                          (cref.setWidth 64 + 3#64 + 1#64).toNat]'(by
                            rw [fastPropMem_arena, h3_1_idx]; exact hcr4_lt_ar) =
                          sem.core.arena[cref.toNat + 4]'hcr4_lt_ar :=
                      (fc_getElem_arena s sem).trans (fc_getElem_eq_of_idx h3_1_idx _ hcr4_lt_ar)
                    have h31_mod : (cref.toNat + 3 + 1) % 2 ^ 64 = cref.toNat + 4 :=
                      Nat.mod_eq_of_lt (by omega)
                    have hl1_c : (fastPropMem s sem).core.arena[
                        (cref.setWidth 64 + 3#64 + 1#64).toNat]'(by
                          rw [fastPropMem_arena, h3_1_idx]; exact hcr4_lt_ar) = not_lit := by
                      simpa only [BitVec.ofNat_eq_ofNat, fastPropMem_arena, h3_1_idx, h31_mod]
                        using hc
                    exact congrArg some (hl1_mem_eq.symm.trans hl1_c)
                  have hl0_mem_eq :
                      (fastPropMem s sem).core.arena[(cref.setWidth 64 + 3#64).toNat]'(by
                        rw [fastPropMem_arena, h3_idx]; exact hcr3_lt_ar) = l0 :=
                    fc_getElem_arena s sem
                  rw [hl0_mem_eq]
                  exact hJ3 (l0, ()) ml
                    ⟨sem, ⟨⟨hpi.len, hpi.nw, hsw_drop, hpi.ag, hpi.tr, hpi.perm, hpi.sc_eq,
                       hpi.not_f⟩, hsb_drop⟩,
                     hoom_st, hct_st, rfl, rfl, rfl, rfl, rfl, hnl_eq, hcr_ref, hng_t, rfl, hl0_idx,
                     hl1_eq, hml⟩
      · exact hB (off_v, end_v, tend_v, unass_v, unfl_v, ticks_v, p_v, q_v, false, ()) ml
          ⟨sem, hnb, htend_eq, hunass_eq, hunfl_eq, fun _ => ⟨hoom_st, hct_st⟩, by simp, hml⟩
    · intro B L _ hL; nb_head_steps
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
      · rw [hend_g, hoff_g]; exact hnb0
      · rw [fastPropMem_self]; exact hm

theorem full_propagate_ignore_nobounds_m7_wp (Γ : Env)
    (hPropLit : ∀ args m Q X, fullPropLitNoBoundsSpec args m Q X →
      Γ "full_prop_lit_nobounds_m7" [i64, i32, i64] [.bool] args m Q X) :
    ∀ args m Q X, fullPropagateIgnoreNoBoundsSpec args m Q X →
      Func.wp Γ full_propagate_ignore_nobounds_m7_body args m Q X := by
  rintro ⟨h, ignore_ref, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hwb0, hdense0, hm, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hret_st : ∀ (r : BitVec 64) (st : FullState) (ml : Mem 64),
      st.LengthsOk c → FullWitnessInv c F0 F_cur st.core → FullWatchBoundsInv st →
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
        Full.FullConflictOkW F_cur st ∧
        (st.core.confl_type = 2#64 → st.core.confl_ref ≠ ignore_ref)) →
      (r = 2#64 → st.core.oom ≠ 0#64 ∨ st.core.fuel = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ st = s) →
      (FullMem c st ⋆ R) ml → Q (r, ()) ml := by
    intro r st ml hst_l hst_w hst_wb hag htr hperm hfl hsc hr hr0 hr1 hr2 hnoop hml
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
    have hst_l' := hst_l; have hst_w' := hst_w; have hst_wb' := hst_wb
    have htr' : Full.FullPropDecSpecs.FullTrailExt s.core st.core :=
      ⟨htr.1, htr.2.1, htr.2.2⟩
    have hperm' : Full.FullPropDecSpecs.FullArenaPermEq s.core st.core :=
      ⟨hperm.2.1, hperm.2.2⟩
    rw [hst_eq] at hst_l' hst_w' hst_wb' htr' hperm' hml
    refine hQ r st.core.vals st.core.flags st.core.lvl st.core.rsns st.core.trl st.core.trail_pos
      st.core.trail_end st.core.propagated st.core.unassigned st.core.unflushed st.core.wvec
      st.core.arena st.core.wstk st.core.wlen st.core.wusable st.core.fuel st.core.confl_type
      st.core.confl_ref st.core.confl_lit0 st.core.confl_lit1 st.core.oom
      st.scratch.search_ticks st.scratch.wsort st.scratch.phases ml
      hst_l' hst_w' hst_wb' htr' hperm' hfl hr hr0 ?_ hr2 ?_ hml
    · intro h1; have hcf := hr1 h1; rw [hst_eq] at hcf; exact hcf
    · intro hpe; obtain ⟨h0, heq⟩ := hnoop hpe; exact ⟨h0, hst_eq ▸ heq⟩
  unfold Func.wp full_propagate_ignore_nobounds_m7_body
  nb_hsteps
  refine wp_loop_group
    (fun rem (prop_v, fuel_v, ()) ml => ∃ memSt : FullState,
      rem = fuel_v.toNat ∧ memSt.LengthsOk c ∧ FullWitnessInv c F0 F_cur memSt.core ∧
      FullWatchBoundsInv memSt ∧ memSt.core.fuel = s.core.fuel ∧
      memSt.core.propagated = prop_v.toNat ∧
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
      ⟨memSt, rfl, hml_l, hml_w, hml_wb, hmfuel, hmprop, hag, htr, hperm, hfuel_le, hsc, hoom_pres,
        hct_pres, hsame, hnoop, hml⟩
    have hcl := hml_l.core_ok
    have hcv_le := hcl.cur_vars_le
    have htl := hcl.trl_len; have hte_le := hcl.trail_end_le; have hpr_le := hcl.propagated_le
    have hdm_st : memSt.core.dense_mode = 0#64 := (hag.get FullCoreState.dense_mode).trans hdense0
    nb_hsteps
    · have hpr_lt : prop_v.toNat < memSt.core.trail_end := by c0_bound
      have hne_end : s.core.propagated ≠ s.core.trail_end := fun h => by
        obtain ⟨hm_s, _⟩ := hnoop h; subst hm_s; omega
      let finSt : FullState :=
        { memSt with core := { memSt.core with propagated := prop_v.toNat, fuel := fuel_v } }
      have hfin_wb : FullWatchBoundsInv finSt :=
        hml_wb.with_nonwatch rfl rfl rfl rfl rfl (Nat.le_refl _) (fun _ _ h1 h2 h3 => ⟨h1, h2, h3⟩)
      exact hret_st 2#64 finSt m
        ⟨{ hcl with propagated_le := by dsimp [finSt]; omega }, hml_l.scratch_ok⟩
        (hml_w.with_fuel_prop fuel_v prop_v.toNat) hfin_wb
        (hag.update fun k => { k with propagated := prop_v.toNat, fuel := fuel_v })
        (fastTrailExt_congr htr rfl rfl rfl) hperm hfuel_le hsc (Or.inr (Or.inr rfl))
        (by simp) (by simp) (fun _ => Or.inl hc) (fun hpe => absurd hpe hne_end)
        (by simpa [finSt, hmprop] using hm)
    · have hpr_lt : prop_v.toNat < memSt.core.trail_end := by c0_bound
      have hne_end : s.core.propagated ≠ s.core.trail_end := fun h => by
        obtain ⟨hm_s, _⟩ := hnoop h; subst hm_s; omega
      let finSt : FullState :=
        { memSt with core := { memSt.core with propagated := prop_v.toNat, fuel := fuel_v } }
      have hfin_wb : FullWatchBoundsInv finSt :=
        hml_wb.with_nonwatch rfl rfl rfl rfl rfl (Nat.le_refl _) (fun _ _ h1 h2 h3 => ⟨h1, h2, h3⟩)
      exact hret_st 2#64 finSt m
        ⟨{ hcl with propagated_le := by dsimp [finSt]; omega }, hml_l.scratch_ok⟩
        (hml_w.with_fuel_prop fuel_v prop_v.toNat) hfin_wb
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
      have hwb1 : FullWatchBoundsInv memSt1 :=
        hml_wb.with_nonwatch rfl rfl rfl rfl rfl (Nat.le_refl _) (fun _ _ h1 h2 h3 => ⟨h1, h2, h3⟩)
      have hm1_mem : (FullMem c memSt1 ⋆ R) m := by
        simpa only [memSt1, show (prop_v + (1 : BitVec 64)).toNat = prop_v.toNat + 1 from hpr1]
          using hm
      c0_call hPropLit
      refine ⟨c, F0, F_cur, memSt1, R, rfl, hlen1, hw1, hwb1, hdm_st, hoom0_st, hm1_mem,
        fun ok vals' flags' lvl' rsns' trl' tp' te' unas' unfl' wvec' arena' wstk' wlen' wu'
          ctype' cref' c0' c1' oom' ticks' wsort' phases' m2 hlen2 hw2 hwb2 htr2 hperm2
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
        fastTrailExt_trans (fastTrailExt_congr htr (k2 := memSt1.core) rfl rfl rfl)
          ⟨htr2.1, htr2.2, htr2.3⟩
      have hperm12 : FullArenaPermEq s.core memSt2.core :=
        fastArenaPerm_trans hperm ⟨rfl, hperm2.1, hperm2.2⟩
      have hsc2 : memSt2.scratch = { s.scratch with
          search_ticks := memSt2.scratch.search_ticks, wsort := memSt2.scratch.wsort,
          phases := memSt2.scratch.phases } := by dsimp [memSt2, memSt1]; rw [hsc]
      have hfl2_lt : (fuel_v - 1#64).toNat < s.core.fuel.toNat := by omega
      nb_hsteps
      · have hok_t : ok = true := by assumption
        exact ih (fuel_v - 1#64).toNat (prop_v + 1#64, fuel_v - 1#64, ()) m2 (by omega)
          ⟨memSt2, rfl, hlen2, hw2, hwb2, hmfuel, hpr1.symm, hag2, htr12, hperm12, by omega, hsc2,
            fun _ => (hok_t_spec hok_t).1, (hok_t_spec hok_t).2.trans hct_pres,
            fun heq => by omega, fun hpe => absurd hpe hne_end, hm2⟩
      · have hok_f : ok = false := by assumption
        let finSt2 : FullState := { memSt2 with core := { memSt2.core with fuel := fuel_v - 1#64 } }
        have hfin2_wb : FullWatchBoundsInv finSt2 :=
          hwb2.with_nonwatch rfl rfl rfl rfl rfl (Nat.le_refl _) (fun _ _ h1 h2 h3 => ⟨h1, h2, h3⟩)
        exact hret_st 2#64 finSt2 m
          ⟨{ hlen2.core_ok with vals_len := hlen2.core_ok.vals_len }, hlen2.scratch_ok⟩
          (hw2.with_fuel_prop _ _) hfin2_wb
          (hag2.update fun k => { k with fuel := fuel_v - 1#64 })
          (fastTrailExt_congr htr12 rfl rfl rfl) hperm12 (by dsimp [finSt2]; omega) hsc2
          (Or.inr (Or.inr rfl)) (by simp) (by simp) (fun _ => Or.inl hc)
          (fun hpe => absurd hpe hne_end) hm
      · have hok_f : ok = false := by assumption
        have hoom2_0 : oom' = 0#64 := by assumption
        have ⟨hcf_ok, hcf_ign⟩ := (hcf hok_f).resolve_left (fun h => h hoom2_0)
        let finSt2 : FullState := { memSt2 with core := { memSt2.core with fuel := fuel_v - 1#64 } }
        have hfin2_wb : FullWatchBoundsInv finSt2 :=
          hwb2.with_nonwatch rfl rfl rfl rfl rfl (Nat.le_refl _) (fun _ _ h1 h2 h3 => ⟨h1, h2, h3⟩)
        exact hret_st 1#64 finSt2 m
          ⟨{ hlen2.core_ok with vals_len := hlen2.core_ok.vals_len }, hlen2.scratch_ok⟩
          (hw2.with_fuel_prop _ _) hfin2_wb
          (hag2.update fun k => { k with fuel := fuel_v - 1#64 })
          (fastTrailExt_congr htr12 rfl rfl rfl) hperm12 (by dsimp [finSt2]; omega) hsc2
          (Or.inr (Or.inl rfl)) (by simp)
          (fun _ => ⟨by dsimp [finSt2]; exact hfl2_lt, hoom2_0,
            by simpa only [Full.FullConflictOkW, fullArenaClauseRefs, fullArenaClauseGarb,
                 fullArenaClauseLits, fullArenaClauseRefsCore, fullArenaClauseGarbCore,
                 fullArenaClauseLitsCore, fullArenaClauseSizeCore, fullArenaHdrCore,
                 finSt2] using hcf_ok,
            hcf_ign⟩)
          (by simp) (fun hpe => absurd hpe hne_end) hm
    · have hpr_eq : prop_v.toNat = memSt.core.trail_end := by c0_bound
      let finSt : FullState :=
        { memSt with core := { memSt.core with propagated := prop_v.toNat, fuel := fuel_v } }
      have hfin_wb : FullWatchBoundsInv finSt :=
        hml_wb.with_nonwatch rfl rfl rfl rfl rfl (Nat.le_refl _) (fun _ _ h1 h2 h3 => ⟨h1, h2, h3⟩)
      exact hret_st 0#64 finSt m
        ⟨{ hcl with propagated_le := by dsimp [finSt]; omega }, hml_l.scratch_ok⟩
        (hml_w.with_fuel_prop fuel_v prop_v.toNat) hfin_wb
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
  · intro L hL; nb_hsteps
    have hpr_lt64 : s.core.propagated < 2 ^ 64 := by
      have := hlen0.core_ok.propagated_le; have := hlen0.core_ok.trail_end_le
      have := hlen0.core_ok.cur_vars_le; omega
    exact hL s.core.fuel.toNat (BitVec.ofNat 64 s.core.propagated, s.core.fuel, ()) m
      ⟨s, rfl, hlen0, hw0, hwb0, rfl, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpr_lt64],
       .refl _ _, ⟨Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl⟩,
       ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, .refl _⟩⟩, Nat.le_refl _, rfl, fun h => h, rfl,
       fun _ => by cases s with | mk sc ssc => cases sc; rfl, fun _ => ⟨rfl, rfl⟩, hm⟩

theorem full_bcp_nobounds_m7_wp (Γ : Env)
    (hPropIgn : ∀ args m Q X, fullPropagateIgnoreNoBoundsSpec args m Q X →
      Γ "full_propagate_ignore_nobounds_m7" [i64, i64] [i64] args m Q X) :
    ∀ args m Q X, fullPropagateNoBoundsSpec args m Q X →
      Func.wp Γ full_bcp_nobounds_m7_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hwb0, hdense0, hm, hQ⟩
  unfold Func.wp full_bcp_nobounds_m7_body
  nb_hsteps
  c0_call hPropIgn
  refine ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hwb0, hdense0, hm,
    fun r vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m' hlen' hw' hwb' htr' hperm' hfl' hr
      hr0 hr1 hr2 hnoop hm' => ?_⟩
  nb_hsteps
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m' hlen' hw' hwb' htr' hperm'
    hfl' hr
    (fun h0 => let ⟨hp, _, ho, hf⟩ := hr0 h0; ⟨hp, ho, hf⟩)
    (fun h1 => let ⟨hf, ho, hca, _⟩ := hr1 h1; ⟨hf, ho, hca⟩) hr2 hnoop hm'

private theorem m7NbConflOkW_of_full {F_cur : List (List Nat)} {s : FullState}
    (h : Full.FullConflictOkW F_cur s) : FullPropDecSpecs.FullConflOkW F_cur s.core := by
  rcases h with ⟨ht, h0, h1, hf0, hf1, hent⟩ | hr
  · exact Or.inl ⟨ht, h0, h1, hent, hf0, hf1⟩
  · exact Or.inr hr

/-- End-to-end `FullSparseInv ∧ FullWatchBoundsInv` preservation and level-0 UNSAT soundness
for `full_bcp_nobounds_m7_body` (UNSAT safety + memory safety, no model-finding proofs). -/
theorem full_bcp_nobounds_m7_preserves_sparse_watchBounds {Γ : Env}
    (hPropIgn : ∀ args m Q X, fullPropagateIgnoreNoBoundsSpec args m Q X →
      Γ "full_propagate_ignore_nobounds_m7" [i64, i64] [i64] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hsp : FullPropDecSpecs.FullSparseInv c F0 s) (hwb0 : FullWatchBoundsInv s)
    (hm : (FullMem c s ⋆ R) m) (Q : Post [i64]) (X : XPost)
    (hpost : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullPropDecSpecs.FullSparseInv c F0 s' → FullWatchBoundsInv s' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 1#64 → s'.core.cur_level = 0 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    Func.wp Γ full_bcp_nobounds_m7_body (c.hdr, ()) m Q X := by
  obtain ⟨⟨hlen0, F_cur, hw0⟩, hmk0, hnd0, ⟨hll0, hext0⟩, hdm0⟩ := hsp
  apply full_bcp_nobounds_m7_wp Γ hPropIgn
  refine ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hwb0, hdm0, hm,
    fun r vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m' hlen' hw' hwb' _htr' hperm' _hfl' hr
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
  have hperm_sp : FullPropDecSpecs.FullArenaPermEq s.core s'.core := hperm'
  have hmk' : FullPropDecSpecs.FullLitMarksClear c s' := hmk0
  have hnd' : FullPropDecSpecs.FullArenaVarsNodup s' := hperm_sp.preserves_varsNodup hnd0
  have hll' : FullPropDecSpecs.FullLastLearnedWf s' :=
    hperm_sp.preserves_lastLearnedWf rfl hll0
  have hsp' : FullPropDecSpecs.FullSparseInv c F0 s' :=
    ⟨⟨hlen', F_cur, hw'⟩, hmk', hnd', ⟨hll', hext0⟩, hdm0⟩
  refine hpost r s' m' hsp' hwb' hr (fun h1 hcl0 => ?_) hm'
  exact hw'.level0_unsat_of_conflOkW hcl0 (m7NbConflOkW_of_full (hr1 h1).2.2)

/-! ## 3. Closed `ModuleOk` & Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`) -/

/-- Specification table for `m7BcpNoBoundsModule` plus extern `full_watch_push`. -/
def m7BcpNoBoundsSpecTable : List SpecEntry :=
  [ ⟨"full_prop_lit_nobounds_m7", [i64, i32, i64], [.bool], fullPropLitNoBoundsSpec, true⟩
  , ⟨"full_propagate_ignore_nobounds_m7", [i64, i64], [i64], fullPropagateIgnoreNoBoundsSpec, true⟩
  , ⟨"full_bcp_nobounds_m7", [i64], [i64], fullPropagateNoBoundsSpec, true⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  ]

/-- Specification environment induced by `m7BcpNoBoundsSpecTable`. -/
def m7BcpNoBoundsEnv : Env := Env.ofTable m7BcpNoBoundsSpecTable

theorem m7BcpNoBoundsSpecTable_noExit : ∀ e ∈ m7BcpNoBoundsSpecTable, e.noExit = true := by
  intro e he
  simp only [m7BcpNoBoundsSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> rfl

theorem m7BcpNoBoundsEnv_noExit :
    ∀ f as bs xs m Q X X',
      m7BcpNoBoundsEnv f as bs xs m Q X → m7BcpNoBoundsEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m7BcpNoBoundsSpecTable_noExit

private theorem m7BcpNoBoundsSpecTable_nodup :
    (m7BcpNoBoundsSpecTable.map SpecEntry.name).Nodup := by
  show (["full_prop_lit_nobounds_m7", "full_propagate_ignore_nobounds_m7",
    "full_bcp_nobounds_m7", "full_watch_push"] : List String).Nodup
  decide

private theorem m7BcpNoBoundsEnv_row_at (i : Nat) (e : SpecEntry)
    (hi : m7BcpNoBoundsSpecTable[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → m7BcpNoBoundsEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) m7BcpNoBoundsSpecTable_nodup (hno xs m Q X h)

/-- Row-by-row `TableImpl` for `m7BcpNoBounds_fns` against `m7BcpNoBoundsSpecTable`. -/
theorem m7BcpNoBounds_tableImpl :
    TableImpl m7BcpNoBoundsEnv m7BcpNoBounds_fns m7BcpNoBoundsSpecTable := by
  let hPush := m7BcpNoBoundsEnv_row_at 3
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  let hPropLit := m7BcpNoBoundsEnv_row_at 0
    ⟨"full_prop_lit_nobounds_m7", [i64, i32, i64], [.bool], fullPropLitNoBoundsSpec, true⟩
  let hPropIgn := m7BcpNoBoundsEnv_row_at 1
    ⟨"full_propagate_ignore_nobounds_m7", [i64, i64], [i64], fullPropagateIgnoreNoBoundsSpec, true⟩
  exact ⟨.of (full_prop_lit_nobounds_m7_wp m7BcpNoBoundsEnv hPush),
    ⟨.of (full_propagate_ignore_nobounds_m7_wp m7BcpNoBoundsEnv hPropLit),
    ⟨.of (full_bcp_nobounds_m7_wp m7BcpNoBoundsEnv hPropIgn), trivial⟩⟩⟩

/-- Closed `ModuleOk` for standalone `m7BcpNoBoundsModule` under `m7BcpNoBoundsEnv`. -/
theorem m7BcpNoBounds_moduleOk : ModuleOk m7BcpNoBoundsEnv m7BcpNoBoundsModule :=
  Env.ofTable_moduleOk m7BcpNoBounds_acyclic
    ⟨full_prop_lit_nobounds_m7_wf, full_propagate_ignore_nobounds_m7_wf,
     full_bcp_nobounds_m7_wf, trivial⟩
    m7BcpNoBounds_tableImpl

/-- Concrete `nvFastPropState` satisfies `FullWatchBoundsInv`. -/
theorem nvFastProp_watchBounds : FullWatchBoundsInv nvFastPropState := by
  refine FullWatchBoundsInv.of_witnessInv nvFastProp_witness
    (Nat.le_trans nvFastProp_lengths.core_ok.arena_len_le
      (Nat.le_of_eq nvFastProp_lengths.core_ok.arena_len_arr.symm))
    rfl (fun l hl q w0 cr hq1 hq2 _ _ _ => ?_)
  have hcv : nvFastPropState.core.cur_vars = 1 := rfl
  rw [hcv] at hl
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · simp [fullWatchOffCore, fullWatchSizeCore, nvFastPropState] at hq1 hq2; try omega
  · simp [fullWatchOffCore, fullWatchSizeCore, nvFastPropState] at hq1 hq2; try omega

/-- Concrete `Mem 64` binary-watch UNSAT non-vacuity for `full_bcp_nobounds_m7_body` under
`m7BcpNoBoundsEnv` (`XPost := False`): preserves `FullWatchBoundsInv` and derives
`Full.nvOneLitF0.Unsat` on conflict (`r = 1#64`). -/
theorem nv_m7_bcp_nobounds :
    Func.wp m7BcpNoBoundsEnv full_bcp_nobounds_m7_body (nvFastPropCfg.hdr, ()) nvFastPropMem
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) ∧
        (r = 1#64 → Full.nvOneLitF0.Unsat) ∧
        ∃ s', FullWatchBoundsInv s' ∧ (FullMem nvFastPropCfg s' ⋆ emp) m')
      (fun _ _ _ _ => False) := by
  let hPropIgn := m7BcpNoBoundsEnv_row_at 1
    ⟨"full_propagate_ignore_nobounds_m7", [i64, i64], [i64], fullPropagateIgnoreNoBoundsSpec, true⟩
  apply full_bcp_nobounds_m7_wp m7BcpNoBoundsEnv hPropIgn
  refine ⟨nvFastPropCfg, Full.nvOneLitF0, [[0], [1]], nvFastPropState, emp,
    rfl, nvFastProp_lengths, nvFastProp_witness, nvFastProp_watchBounds, rfl,
    by rw [sep_emp]; exact nvFastPropMem_ok, ?_⟩
  intro r _vals' _flags' _lvl' _rsns' _trl' _tp' _te' _prop' _unas' _unfl'
    _wvec' _arena' _wstk' _wlen' _wu' _fuel' _ctype' _cref' _c0' _c1' _oom'
    _ticks' _wsort' _phases' m' s' _hlen' hwf' hwb' _htr' _hperm' _hfl' hr _hr0 hr1 _hr2 _hnoop hm'
  refine ⟨hr, fun h1 => ?_, _, hwb', hm'⟩
  subst h1
  exact hwf'.level0_unsat_of_conflOkW rfl (m7NbConflOkW_of_full (hr1 rfl).2.2)

end LeanQbe.T.Examples.Kissat.FullM7BcpNoBounds
