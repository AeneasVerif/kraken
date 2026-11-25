/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityCongProof0
import LeanQbe.T.Examples.Kissat.FullCongLemmas1
import LeanQbe.T.Examples.Kissat.FullCongLemmas2
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.C0Agrees
import LeanQbe.T.Logic.MemLemmas

/-!
# Kissat 4.0.4 Congruence Parity Proofs — Part 2a0 (`FullFidelityCongProof2a0`)

Proves the parametric `(Γ : Env)` `Func.wp` contract `full_cong_eval_gate_wp` for
`FullFidelityCong.full_cong_eval_gate_body` against `fidCongEvalGateSpec` (`maxA ≤ 64`, wide AND
arity `≤ 64`, XOR LHS self-cancellation, ITE-to-XOR & ITE-to-AND rewriting, and 128-probe HT).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityCong

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
open LeanQbe.T.Examples.Kissat.FullM8FidV12
open Kraken.Bedrock2.Test
open scoped FullArenaTactics Full.FullCongTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6CongSubst.M6bHeadTactics

/-! ## 1. Evaluation Context, State Invariants & Frame Helpers -/

section Helpers

structure FidEvCtx where
  maxA : Nat
  hmaxA : maxA ≤ 64
  cfg : FullCfg
  F0 : CNF Nat
  F_cur : List (List Nat)
  fuel0 : BitVec 64
  ar0 : List (BitVec 32)
  alen0 : Nat
  cv0 : Nat
  g_len : Nat
  ht_off : Nat
  ht_sz : Nat
  ctrl_off : Nat
  scr0 : List (BitVec 32)
  scr_init : List (BitVec 32)
  R : Mem 64 → Prop

abbrev FidEvStOk (ctx : FidEvCtx) (st : FullState) : Prop :=
  FullDenseInvW ctx.cfg ctx.F0 ctx.F_cur st ∧
  st.core.cur_vars = ctx.cv0 ∧ st.core.fuel = ctx.fuel0 ∧
  st.core.arena = ctx.ar0 ∧ st.core.arena_len = ctx.alen0 ∧
  FullCongReprInv ctx.F_cur (2 * ctx.cv0) st.core.repr ∧
  FidCongHtInv ctx.maxA ctx.F_cur ctx.cv0 ctx.scr0 st.scratch.scratch_buf
    ctx.g_len ctx.ht_off ctx.ht_sz ∧
  M8QueueCtx ctx.cfg st.scratch.scratch_buf ctx.g_len ctx.ctrl_off ctx.ht_off ctx.ht_sz ∧
  M8ScrFrame ctx.cfg ctx.g_len ctx.ctrl_off ctx.ht_off ctx.ht_sz
    ctx.scr_init st.scratch.scratch_buf

abbrev FidHashGateOk (F_cur : List (List Nat)) (cv0 : Nat) (lhs : BitVec 32)
    (tmps : List (BitVec 32)) (htag harity : BitVec 32) : Prop :=
  harity.toNat ≤ cv0 ∧
  (htag = 0#32 → 2 ≤ harity.toNat ∧ harity.toNat ≤ 64 ∧
    ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      evalLitVal α lhs.toNat =
        (List.range harity.toNat).all (fun k => evalLitVal α (tmps[k]?.getD 0#32).toNat)) ∧
  (htag = 1#32 → 2 ≤ harity.toNat ∧ harity.toNat ≤ 4 ∧
    (∀ k < harity.toNat, (tmps[k]?.getD 0#32).toNat < 2 * cv0) ∧
    XorListGateDef (cnfOfClauses F_cur) lhs.toNat
      ((tmps.take harity.toNat).map BitVec.toNat)) ∧
  (htag = 2#32 → harity = 3#32 ∧
    IteGateDef (cnfOfClauses F_cur) lhs.toNat
      (tmps[0]?.getD 0#32).toNat (tmps[1]?.getD 0#32).toNat (tmps[2]?.getD 0#32).toNat)

structure FidEvOutCtx (ctx : FidEvCtx) (s0 : FullState) (Q : Post [i64]) : Prop where
  hcv0 : ctx.cv0 = s0.core.cur_vars
  hf0 : ctx.fuel0 = s0.core.fuel
  ha0 : ctx.ar0 = s0.core.arena
  hal0 : ctx.alen0 = s0.core.arena_len
  hs0 : ctx.scr_init = s0.scratch.scratch_buf
  hle : ctx.g_len ≤ ctx.ht_off
  hht : ctx.ht_off + ctx.ht_sz ≤ ctx.cfg.scratch_cap
  hpref0 : ∀ idx < ctx.g_len, ctx.scr_init[idx]? = ctx.scr0[idx]?
  hq0 : M8QueueCtx ctx.cfg ctx.scr_init ctx.g_len ctx.ctrl_off ctx.ht_off ctx.ht_sz
  hQ : ∀ (r : BitVec 64) s' m',
    FullDenseInvW ctx.cfg ctx.F0 ctx.F_cur s' →
    s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
    s'.core.arena = s0.core.arena → s'.core.arena_len = s0.core.arena_len →
    FullCongReprInv ctx.F_cur (2 * s'.core.cur_vars) s'.core.repr →
    (∀ idx < ctx.g_len, s'.scratch.scratch_buf[idx]? = ctx.scr0[idx]?) →
    FidCongHtInv ctx.maxA ctx.F_cur s'.core.cur_vars ctx.scr0 s'.scratch.scratch_buf
      ctx.g_len ctx.ht_off ctx.ht_sz →
    M8QueueCtx ctx.cfg s'.scratch.scratch_buf ctx.g_len ctx.ctrl_off ctx.ht_off ctx.ht_sz →
    ((r &&& 2#64) = 0#64 →
      (∀ idx < ctx.cfg.scratch_cap, idx < ctx.ht_off →
        (ctx.ctrl_off = ctx.cfg.scratch_cap →
          s'.scratch.scratch_buf[idx]? = s0.scratch.scratch_buf[idx]?) ∧
        (∀ occ_bkt bkt_off inq_off q_off,
          M8CtrlLayout ctx.cfg s0.scratch.scratch_buf ctx.g_len ctx.ctrl_off
            occ_bkt bkt_off inq_off q_off ctx.ht_off ctx.ht_sz →
          idx ≠ ctx.ctrl_off + 5 →
          ¬ (q_off ≤ idx ∧ idx < q_off + occ_bkt) →
          ¬ (inq_off ≤ idx ∧ idx < inq_off + occ_bkt) →
          s'.scratch.scratch_buf[idx]? = s0.scratch.scratch_buf[idx]?))) →
    ((r &&& 2#64) ≠ 0#64 → ctx.F0.Unsat) →
    (FullMem ctx.cfg s' ⋆ ctx.R) m' → Q (r, ()) m'

theorem fidEvStOk_dw {ctx : FidEvCtx} {st : FullState} (h : FidEvStOk ctx st) :
    FullDenseInvW ctx.cfg ctx.F0 ctx.F_cur st := h.1

theorem fidEvStOk_wit {ctx : FidEvCtx} {st : FullState} (h : FidEvStOk ctx st) :
    FullWitnessInv ctx.cfg ctx.F0 ctx.F_cur st.core := h.1.2.1

theorem fidEvStOk_cl {ctx : FidEvCtx} {st : FullState} (h : FidEvStOk ctx st) :
    st.core.cur_level = 0 := h.1.2.2.2.2.2.1

theorem fidEvStOk_cv {ctx : FidEvCtx} {st : FullState} (h : FidEvStOk ctx st) :
    st.core.cur_vars = ctx.cv0 := h.2.1

theorem fidEvStOk_repr {ctx : FidEvCtx} {st : FullState} (h : FidEvStOk ctx st) :
    FullCongReprInv ctx.F_cur (2 * ctx.cv0) st.core.repr := h.2.2.2.2.2.1

theorem fidEvStOk_ht {ctx : FidEvCtx} {st : FullState} (h : FidEvStOk ctx st) :
    FidCongHtInv ctx.maxA ctx.F_cur ctx.cv0 ctx.scr0 st.scratch.scratch_buf
      ctx.g_len ctx.ht_off ctx.ht_sz := h.2.2.2.2.2.2.1

theorem fidEvStOk_fr {ctx : FidEvCtx} {st : FullState} (h : FidEvStOk ctx st) :
    M8ScrFrame ctx.cfg ctx.g_len ctx.ctrl_off ctx.ht_off ctx.ht_sz
      ctx.scr_init st.scratch.scratch_buf := h.2.2.2.2.2.2.2.2

theorem fidQueueCtx_set_ht {c : FullCfg} {scr : List (BitVec 32)}
    {g_len ctrl_off ht_off ht_sz : Nat}
    (hq : M8QueueCtx c scr g_len ctrl_off ht_off ht_sz) {slot : Nat} (v : BitVec 32) :
    M8QueueCtx c (scr.set (ht_off + slot) v) g_len ctrl_off ht_off ht_sz := by
  rcases hq with rfl | ⟨o, b, i, q, hl⟩
  · exact Or.inl rfl
  · right; refine ⟨o, b, i, q, ?_⟩
    rcases hl with ⟨h1, h2, h3, h4, s0, s1, s2, s3, s6, s7, h5, h6, hp, h7, h8, h9, h10, h11, h12,
      hqh, hql, hqok⟩
    refine ⟨h1, h2, h3, h4, by rw [List.getElem?_set_ne (by omega)]; exact s0,
      by rw [List.getElem?_set_ne (by omega)]; exact s1,
      by rw [List.getElem?_set_ne (by omega)]; exact s2,
      by rw [List.getElem?_set_ne (by omega)]; exact s3,
      by rw [List.getElem?_set_ne (by omega)]; exact s6,
      by rw [List.getElem?_set_ne (by omega)]; exact s7,
      h5, h6, hp, h7, h8, h9, h10, h11, h12,
      by rw [List.getElem?_set_ne (by omega)]; exact hqh,
      by rw [List.getElem?_set_ne (by omega)]; exact hql, fun k hk => ?_⟩
    have h4 : (scr.set (ht_off + slot) v)[ctrl_off + 4]? = scr[ctrl_off + 4]? :=
      List.getElem?_set_ne (by omega)
    have h5' : (scr.set (ht_off + slot) v)[ctrl_off + 5]? = scr[ctrl_off + 5]? :=
      List.getElem?_set_ne (by omega)
    rw [h5'] at hk; rw [h4]
    have hmod := Nat.mod_lt ((scr[ctrl_off + 4]?.getD 0#32).toNat + k) h5
    rw [List.getElem?_set_ne (by omega)]; exact hqok k hk

theorem fidScrFrame_ht_set {c : FullCfg} {g_len ctrl_off ht_off ht_sz : Nat}
    {scr0 scr : List (BitVec 32)} (hfr : M8ScrFrame c g_len ctrl_off ht_off ht_sz scr0 scr)
    (slot : Nat) (v : BitVec 32) :
    M8ScrFrame c g_len ctrl_off ht_off ht_sz scr0 (scr.set (ht_off + slot) v) := by
  refine ⟨by rw [List.length_set]; exact hfr.1, fun idx h1 h2 => ?_⟩
  rw [List.getElem?_set_ne (by omega)]; exact hfr.2 idx h1 h2

theorem fidScrFrame_enq {c : FullCfg} {g_len ctrl_off ht_off ht_sz : Nat}
    {scr0 scr1 scr2 : List (BitVec 32)}
    (hfr1 : M8ScrFrame c g_len ctrl_off ht_off ht_sz scr0 scr1)
    (hq1 : M8QueueCtx c scr1 g_len ctrl_off ht_off ht_sz) (hlen2 : scr2.length = c.scratch_cap)
    (hcap_eq : ctrl_off = c.scratch_cap → scr2 = scr1)
    (hlay2 : ∀ occ_bkt bkt_off inq_off q_off,
      M8CtrlLayout c scr1 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz →
      scr2[ctrl_off]? = some (BitVec.ofNat 32 occ_bkt) ∧
      scr2[ctrl_off + 1]? = some (BitVec.ofNat 32 bkt_off) ∧
      scr2[ctrl_off + 2]? = some (BitVec.ofNat 32 inq_off) ∧
      scr2[ctrl_off + 3]? = some (BitVec.ofNat 32 q_off) ∧
      scr2[ctrl_off + 4]? = scr1[ctrl_off + 4]? ∧
      scr2[ctrl_off + 6]? = some (BitVec.ofNat 32 ht_off) ∧
      scr2[ctrl_off + 7]? = some (BitVec.ofNat 32 ht_sz) ∧
      (∀ idx, idx ≠ ctrl_off + 5 → ¬ (q_off ≤ idx ∧ idx < q_off + occ_bkt) →
        ¬ (inq_off ≤ idx ∧ idx < inq_off + occ_bkt) → scr2[idx]? = scr1[idx]?)) :
    M8ScrFrame c g_len ctrl_off ht_off ht_sz scr0 scr2 := by
  refine ⟨hlen2, fun idx h1 h2 => ⟨fun hcap => by
    rw [hcap_eq hcap]; exact (hfr1.2 idx h1 h2).1 hcap,
    fun o b i q hl0 hne5 hnq hni => ?_⟩⟩
  rcases hq1 with hcap | ⟨o1, b1, i1, q1, hl1⟩
  · have := hl0.1; omega
  · have hsc := c.hscr; unfold dimacsBound at hsc
    have hl0' := hl0; have hl1' := hl1
    rcases hl0 with ⟨_, h8, _, _, s0_0, _, s0_2, s0_3, _, _, _, ho0, _, _, hcq, hqi, hib, hbh, hhc,
      _⟩
    rcases hl1 with ⟨_, _, _, _, s1_0, _, s1_2, s1_3, _, _, _, ho1, _, _, _, hqi1, hib1, hbh1,
      hhc1, _⟩
    have h_eq : ∀ k < 4, scr1[ctrl_off + k]? = scr0[ctrl_off + k]? := fun k hk =>
      (hfr1.2 (ctrl_off + k) (by omega) (by omega)).2 o b i q hl0' (by omega) (by omega) (by omega)
    have heqc : ∀ {x y : Nat}, x < 2 ^ 32 → y < 2 ^ 32 →
        BitVec.ofNat 32 x = BitVec.ofNat 32 y → x = y := fun hx hy hv => by
      have h := congrArg BitVec.toNat hv; rwa [bv32_ofNat_toNat hx, bv32_ofNat_toNat hy] at h
    have e0 := h_eq 0 (by decide); rw [Nat.add_zero] at e0
    have ho : o1 = o := heqc (by omega) (by omega) (by rw [← s1_0, e0, s0_0])
    have hi : i1 = i := heqc (by omega) (by omega) (by rw [← s1_2, h_eq 2 (by decide), s0_2])
    have hq : q1 = q := heqc (by omega) (by omega) (by rw [← s1_3, h_eq 3 (by decide), s0_3])
    rw [(hlay2 o1 b1 i1 q1 hl1').2.2.2.2.2.2.2 idx hne5 (by rwa [hq, ho]) (by rwa [hi, ho])]
    exact (hfr1.2 idx h1 h2).2 o b i q hl0' hne5 hnq hni

theorem fidCongHtInv_enq {maxA : Nat} {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len ctrl_off ht_off ht_sz : Nat} {scr_init scr1 scr2 : List (BitVec 32)}
    (hht : FidCongHtInv maxA F_cur cv scr_init scr1 g_len ht_off ht_sz)
    (hq1 : M8QueueCtx c scr1 g_len ctrl_off ht_off ht_sz)
    (hcap_eq : ctrl_off = c.scratch_cap → scr2 = scr1)
    (hlay2 : ∀ occ_bkt bkt_off inq_off q_off,
      M8CtrlLayout c scr1 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz →
      scr2[ctrl_off]? = some (BitVec.ofNat 32 occ_bkt) ∧
      scr2[ctrl_off + 1]? = some (BitVec.ofNat 32 bkt_off) ∧
      scr2[ctrl_off + 2]? = some (BitVec.ofNat 32 inq_off) ∧
      scr2[ctrl_off + 3]? = some (BitVec.ofNat 32 q_off) ∧
      scr2[ctrl_off + 4]? = scr1[ctrl_off + 4]? ∧
      scr2[ctrl_off + 6]? = some (BitVec.ofNat 32 ht_off) ∧
      scr2[ctrl_off + 7]? = some (BitVec.ofNat 32 ht_sz) ∧
      (∀ idx, idx ≠ ctrl_off + 5 → ¬ (q_off ≤ idx ∧ idx < q_off + occ_bkt) →
        ¬ (inq_off ≤ idx ∧ idx < inq_off + occ_bkt) → scr2[idx]? = scr1[idx]?)) :
    FidCongHtInv maxA F_cur cv scr_init scr2 g_len ht_off ht_sz := by
  intro k hk
  rcases hq1 with hcap | ⟨o, b, i, q, hl⟩
  · rw [hcap_eq hcap]; exact hht k hk
  · have hl' := hl; rcases hl with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hco, hqi, hib, hbh, _⟩
    rw [(hlay2 o b i q hl').2.2.2.2.2.2.2 (ht_off + k) (by omega) (by omega) (by omega)]
    exact hht k hk

theorem fidEvStOk_of_fold {ctx : FidEvCtx} {st s' : FullState} (hok : FidEvStOk ctx st)
    (hl' : s'.LengthsOk ctx.cfg) (hw' : FullWitnessInv ctx.cfg ctx.F0 ctx.F_cur s'.core)
    (hmk' : FullLitMarksClear ctx.cfg s') (hnd' : FullArenaVarsNodup s')
    (hext' : FullExtScratchOk ctx.cfg s') (hcl' : s'.core.cur_level = 0)
    (hdm' : s'.core.dense_mode ≠ 0#64) (hcv' : s'.core.cur_vars = st.core.cur_vars)
    (hfl' : s'.core.fuel = st.core.fuel) (har' : s'.core.arena = st.core.arena)
    (hal' : s'.core.arena_len = st.core.arena_len)
    (hscr' : s'.scratch.scratch_buf = st.scratch.scratch_buf)
    (hrepr' : FullCongReprInv ctx.F_cur (2 * s'.core.cur_vars) s'.core.repr) :
    FidEvStOk ctx s' :=
  ⟨⟨hl', hw', hmk', hnd', hext', hcl', hdm'⟩, hcv'.trans hok.2.1, hfl'.trans hok.2.2.1,
   har'.trans hok.2.2.2.1, hal'.trans hok.2.2.2.2.1,
   by rw [hcv'.trans hok.2.1] at hrepr'; exact hrepr',
   by rw [hscr']; exact hok.2.2.2.2.2.2.1, by rw [hscr']; exact hok.2.2.2.2.2.2.2.1,
   by unfold M8ScrFrame; rw [hscr']; exact hok.2.2.2.2.2.2.2.2⟩

theorem fidEvStOk_wsState {ctx : FidEvCtx} {s0 : FullState} (h : FidEvStOk ctx s0)
    {r t : List (BitVec 32)} (hr : r.length = 2 * ctx.cfg.max_vars)
    (ht : t.length = ctx.cfg.max_vars) (hrepr : FullCongReprInv ctx.F_cur (2 * ctx.cv0) r) :
    FidEvStOk ctx (wsState s0 r t) :=
  ⟨⟨⟨{ h.1.1.core_ok with repr_len := hr, tmp_len_arr := ht }, h.1.1.scratch_ok⟩,
    fullWitnessInv_with_tmp (fullWitnessInv_with_repr h.1.2.1 r) t,
    h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1, h.1.2.2.2.2.2.1, h.1.2.2.2.2.2.2⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, hrepr, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem fidEvStOk_with_repr {ctx : FidEvCtx} {st : FullState} (h : FidEvStOk ctx st)
    {r : List (BitVec 32)} (hr : r.length = 2 * ctx.cfg.max_vars)
    (hrepr : FullCongReprInv ctx.F_cur (2 * ctx.cv0) r) :
    FidEvStOk ctx { st with core := { st.core with repr := r } } :=
  ⟨⟨⟨{ h.1.1.core_ok with repr_len := hr }, h.1.1.scratch_ok⟩,
    fullWitnessInv_with_repr h.1.2.1 r, h.1.2.2.1, h.1.2.2.2.1,
    h.1.2.2.2.2.1, h.1.2.2.2.2.2.1, h.1.2.2.2.2.2.2⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, hrepr, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem fidEvStOk_with_repr_mclr {ctx : FidEvCtx} {st : FullState} (h : FidEvStOk ctx st)
    {r mc : List (BitVec 32)} (hr : r.length = 2 * ctx.cfg.max_vars)
    (hmc : mc.length = ctx.cfg.max_vars) (hrepr : FullCongReprInv ctx.F_cur (2 * ctx.cv0) r) :
    FidEvStOk ctx { st with core := { st.core with repr := r, min_clr := mc } } :=
  ⟨⟨⟨{ h.1.1.core_ok with repr_len := hr, min_clr_len_arr := hmc }, h.1.1.scratch_ok⟩,
    fullWitnessInv_with_min_clr (fullWitnessInv_with_repr h.1.2.1 r) mc,
    h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1, h.1.2.2.2.2.2.1, h.1.2.2.2.2.2.2⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, hrepr, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem fidEvStOk_with_inconsistent {ctx : FidEvCtx} {st : FullState}
    (h : FidEvStOk ctx st) (hu : (cnfOfClauses ctx.F_cur).Unsat) :
    FidEvStOk ctx { st with core := { st.core with inconsistent := 1#64 } } :=
  ⟨⟨⟨{ h.1.1.core_ok with }, h.1.1.scratch_ok⟩,
    fullWitnessInv_with_inconsistent h.1.2.1 1#64 (fun _ => hu),
    h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1, h.1.2.2.2.2.2.1, h.1.2.2.2.2.2.2⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem fidEvStOk_ht_insert {ctx : FidEvCtx} {stp : FullState}
    {ht_off ht_sz g slot : BitVec 64} (hok : FidEvStOk ctx stp)
    (hho : ctx.ht_off = ht_off.toNat) (hhs : ctx.ht_sz = ht_sz.toNat)
    (hg_lt : g.toNat < ctx.g_len) (hg_le_ht : ctx.g_len ≤ ht_off.toNat)
    (hht_le : ht_off.toNat + ht_sz.toNat ≤ ctx.cfg.scratch_cap)
    (hslot_lt : slot.toNat < ht_sz.toNat)
    (hgat : FidGateAt ctx.maxA ctx.F_cur ctx.cv0 ctx.scr0 ctx.g_len g.toNat) :
    let scr_ins := stp.scratch.scratch_buf.set (ht_off.toNat + slot.toNat) (g.setWidth 32)
    FidEvStOk ctx { stp with scratch := { stp.scratch with
      scratch_buf := scr_ins, res_sz := stp.scratch.res_sz + 1#64 } } := by
  intro scr_ins
  have hsc := ctx.cfg.hscr; unfold dimacsBound at hsc
  have hscrl := hok.1.1.scratch_ok.scratch_buf_len
  have htr : (g.setWidth 32).toNat = g.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have hdw' : FullDenseInvW ctx.cfg ctx.F0 ctx.F_cur { stp with scratch := { stp.scratch with
      scratch_buf := scr_ins, res_sz := stp.scratch.res_sz + 1#64 } } :=
    ⟨⟨hok.1.1.core_ok, { hok.1.1.scratch_ok with
      scratch_buf_len := by rw [List.length_set]; exact hscrl }⟩,
     hok.1.2.1, hok.1.2.2.1, hok.1.2.2.2.1,
     fullExtScratchOk_of_eq hok.1.2.2.2.2.1 rfl rfl rfl rfl,
     hok.1.2.2.2.2.2.1, hok.1.2.2.2.2.2.2⟩
  refine ⟨hdw', hok.2.1, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1, hok.2.2.2.2.2.1, ?_,
    hho ▸ fidQueueCtx_set_ht (hho ▸ hok.2.2.2.2.2.2.2.1) _,
    hho ▸ fidScrFrame_ht_set (hho ▸ hok.2.2.2.2.2.2.2.2) slot.toNat _⟩
  rw [hho]; exact fidCongHtInv_set_gate (hho ▸ hok.2.2.2.2.2.2.1) (hhs ▸ hslot_lt)
    (by omega) (by rw [htr]; exact hgat)

theorem fidEv_ret2 {ctx : FidEvCtx} {s0 su : FullState} {Q : Post [i64]} {mu : Mem 64}
    (hex : FidEvOutCtx ctx s0 Q) (hoku : FidEvStOk ctx su)
    (huns : ctx.F0.Unsat) (hmu : (FullMem ctx.cfg su ⋆ ctx.R) mu) : Q (2#64, ()) mu :=
  hex.hQ 2#64 su mu hoku.1 (hoku.2.1.trans hex.hcv0) (hoku.2.2.1.trans hex.hf0)
    (hoku.2.2.2.1.trans hex.ha0) (hoku.2.2.2.2.1.trans hex.hal0)
    (by rw [hoku.2.1]; exact hoku.2.2.2.2.2.1)
    (m8ScrFrame_pref hex.hle hex.hht hex.hpref0 hex.hq0 hoku.2.2.2.2.2.2.2.2)
    (by rw [hoku.2.1]; exact hoku.2.2.2.2.2.2.1)
    hoku.2.2.2.2.2.2.2.1 (fun h => absurd h (by decide)) (fun _ => huns) hmu

theorem fidEv_exit {ctx : FidEvCtx} {s0 su : FullState} {Q : Post [i64]} {mu : Mem 64}
    (hex : FidEvOutCtx ctx s0 Q) (hoku : FidEvStOk ctx su)
    (hmu : (FullMem ctx.cfg su ⋆ ctx.R) mu) (ch keep : Bool) :
    let rv : BitVec 64 := (if ch then 1#64 else 0#64) ||| (if keep then 4#64 else 0#64)
    Q (rv, ()) mu := by
  intro rv
  have hand0 : (rv &&& 2#64) = 0#64 := by dsimp only [rv]; cases ch <;> cases keep <;> decide
  exact hex.hQ rv su mu hoku.1 (hoku.2.1.trans hex.hcv0) (hoku.2.2.1.trans hex.hf0)
    (hoku.2.2.2.1.trans hex.ha0) (hoku.2.2.2.2.1.trans hex.hal0)
    (by rw [hoku.2.1]; exact hoku.2.2.2.2.2.1)
    (m8ScrFrame_pref hex.hle hex.hht hex.hpref0 hex.hq0 hoku.2.2.2.2.2.2.2.2)
    (by rw [hoku.2.1]; exact hoku.2.2.2.2.2.2.1)
    hoku.2.2.2.2.2.2.2.1 (fun _ idx h1 h2 => hex.hs0 ▸ hoku.2.2.2.2.2.2.2.2.2 idx h1 h2)
    (fun h => absurd hand0 h) hmu

theorem fidEv_unit {ctx : FidEvCtx} {st : FullState} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {lit next_ep : BitVec 32}
    (hok : FidEvStOk ctx st) (hl : lit.toNat < 2 * ctx.cv0)
    (hent : (cnfOfClauses ctx.F_cur).EntailsClause (cnfClause [lit.toNat]))
    (hm : (FullMem ctx.cfg st ⋆ ctx.R) m)
    (k : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FidEvStOk ctx s' → s'.core.tmp = st.core.tmp → (r = 2#64 → ctx.F0.Unsat) →
      (FullMem ctx.cfg s' ⋆ ctx.R) m' → Q (r, ()) m') :
    m3CongUnitFoldSpec (ctx.cfg.hdr, lit, next_ep, ()) m Q X :=
  ⟨ctx.cfg, ctx.F0, ctx.F_cur, st, ctx.R, rfl, hok.1.1, hok.1.2.1, hok.1.2.2.1, hok.1.2.2.2.1,
   hok.1.2.2.2.2.1, hok.1.2.2.2.2.2.1, hok.1.2.2.2.2.2.2,
   hok.2.1 ▸ hok.2.2.2.2.2.1, hok.2.1 ▸ hl, hent, hm,
   fun r s' m' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 htmp h12 h13 _ h2u hm' =>
     k r s' m' (fidEvStOk_of_fold hok h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13)
       htmp (fun h => (h2u h).2) hm'⟩

theorem fidEv_unit_xor1 {ctx : FidEvCtx} {st : FullState} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {lit next_ep : BitVec 32}
    (hok : FidEvStOk ctx st) (hl : lit.toNat < 2 * ctx.cv0)
    (hent : (cnfOfClauses ctx.F_cur).EntailsClause (cnfClause [litNeg lit.toNat]))
    (hm : (FullMem ctx.cfg st ⋆ ctx.R) m)
    (k : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FidEvStOk ctx s' → s'.core.tmp = st.core.tmp → (r = 2#64 → ctx.F0.Unsat) →
      (FullMem ctx.cfg s' ⋆ ctx.R) m' → Q (r, ()) m') :
    m3CongUnitFoldSpec (ctx.cfg.hdr, lit ^^^ 1#32, next_ep, ()) m Q X :=
  fidEv_unit hok (by rw [FullCongHelpers.bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hl)
    (by rw [FullCongHelpers.bv32_xor1_eq_litNeg]; exact hent) hm k

theorem fidEv_equiv {ctx : FidEvCtx} {st : FullState} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {a b next_ep : BitVec 32}
    (hok : FidEvStOk ctx st) (ha : a.toNat < 2 * ctx.cv0) (hb : b.toNat < 2 * ctx.cv0)
    (heqv : LitEquiv (cnfOfClauses ctx.F_cur) a.toNat b.toNat)
    (hm : (FullMem ctx.cfg st ⋆ ctx.R) m)
    (k : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FidEvStOk ctx s' → s'.core.tmp = st.core.tmp → (r = 2#64 → ctx.F0.Unsat) →
      (FullMem ctx.cfg s' ⋆ ctx.R) m' → Q (r, ()) m') :
    m3CongEquivFoldSpec (ctx.cfg.hdr, a, b, next_ep, ()) m Q X :=
  ⟨ctx.cfg, ctx.F0, ctx.F_cur, st, ctx.R, rfl, hok.1.1, hok.1.2.1, hok.1.2.2.1, hok.1.2.2.2.1,
   hok.1.2.2.2.2.1, hok.1.2.2.2.2.2.1, hok.1.2.2.2.2.2.2,
   hok.2.1 ▸ hok.2.2.2.2.2.1, hok.2.1 ▸ ha, hok.2.1 ▸ hb, heqv, hm,
   fun r s' m' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 htmp h12 h13 _ h2u hm' =>
     k r s' m' (fidEvStOk_of_fold hok h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13)
       htmp h2u hm'⟩

theorem fidEv_enq_core {ctx : FidEvCtx} {s0 st : FullState} {Qo : Post [i64]}
    {m : Mem 64} {Q : Post []} {X : XPost} {ctrl_off : BitVec 64} {v : BitVec 32}
    (_hex : FidEvOutCtx ctx s0 Qo) (hok : FidEvStOk ctx st) (hco : ctrl_off.toNat = ctx.ctrl_off)
    (hm : (FullMem ctx.cfg st ⋆ ctx.R) m)
    (k : ∀ s' m', FidEvStOk ctx s' → s'.core = st.core → (FullMem ctx.cfg s' ⋆ ctx.R) m' → Q () m')
      :
    m8CongEnqVarSpec (ctx.cfg.hdr, ctrl_off, v, ()) m Q X := by
  refine ⟨ctx.cfg, st, ctx.g_len, ctx.ht_off, ctx.ht_sz, ctx.R, rfl, hok.1.1,
    by rw [hco]; exact hok.2.2.2.2.2.2.2.1, hm, fun scr' m' hscrl' hq' hcap_eq hlay' hm' => ?_⟩
  rw [hco] at hq' hcap_eq hlay'
  have hdw' : FullDenseInvW ctx.cfg ctx.F0 ctx.F_cur
      { st with scratch := { st.scratch with scratch_buf := scr' } } :=
    ⟨⟨hok.1.1.core_ok, { hok.1.1.scratch_ok with scratch_buf_len := hscrl' }⟩,
     hok.1.2.1, hok.1.2.2.1, hok.1.2.2.2.1,
     fullExtScratchOk_of_eq hok.1.2.2.2.2.1 rfl rfl rfl rfl,
     hok.1.2.2.2.2.2.1, hok.1.2.2.2.2.2.2⟩
  exact k { st with scratch := { st.scratch with scratch_buf := scr' } } m'
    ⟨hdw', hok.2.1, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1, hok.2.2.2.2.2.1,
     fidCongHtInv_enq hok.2.2.2.2.2.2.1 hok.2.2.2.2.2.2.2.1 hcap_eq hlay',
     hq', fidScrFrame_enq hok.2.2.2.2.2.2.2.2 hok.2.2.2.2.2.2.2.1 hscrl' hcap_eq hlay'⟩ rfl hm'

theorem fidEv_enq {ctx : FidEvCtx} {s0 st : FullState} {Qo : Post [i64]}
    {m : Mem 64} {Q : Post []} {X : XPost} {ctrl_off : BitVec 64} {v : BitVec 32}
    (hex : FidEvOutCtx ctx s0 Qo) (hok : FidEvStOk ctx st) (hco : ctrl_off.toNat = ctx.ctrl_off)
    (hm : (FullMem ctx.cfg st ⋆ ctx.R) m)
    (k : ∀ s' m', FidEvStOk ctx s' → s'.core.tmp = st.core.tmp →
      (FullMem ctx.cfg s' ⋆ ctx.R) m' → Q () m') :
    m8CongEnqVarSpec (ctx.cfg.hdr, ctrl_off, v, ()) m Q X :=
  fidEv_enq_core hex hok hco hm fun s' m' h1 hc hm' =>
    k s' m' h1 (congrArg FullCoreState.tmp hc) hm'

abbrev FidEvOut (ctx : FidEvCtx) (lhs' htag' harity : BitVec 32) (nh' : Bool)
    (mj : Mem 64) : Prop :=
  ∃ stj : FullState,
    FidEvStOk ctx stj ∧
    (nh' = true → FidHashGateOk ctx.F_cur ctx.cv0 lhs' stj.core.tmp htag' harity) ∧
    (nh' = true → lhs'.toNat < 2 * ctx.cv0) ∧
    (FullMem ctx.cfg stj ⋆ ctx.R) mj

theorem fidEvOut_nohash {ctx : FidEvCtx} {lhs' htag' harity : BitVec 32} {mj : Mem 64}
    (stj : FullState) (hokj : FidEvStOk ctx stj) (hm : (FullMem ctx.cfg stj ⋆ ctx.R) mj) :
    FidEvOut ctx lhs' htag' harity false mj :=
  ⟨stj, hokj, (fun h => by cases h), (fun h => by cases h), hm⟩

abbrev FidEvFindInv (ctx : FidEvCtx) (s0 : FullState) (g_n ar_n : Nat) :
    Tup Val [i32] → Mem 64 → Prop :=
  fun (i, ()) mi => ∃ (repri tmpi : List (BitVec 32)),
    repri.length = 2 * ctx.cfg.max_vars ∧ tmpi.length = ctx.cfg.max_vars ∧
    i.toNat ≤ ar_n ∧ FullCongReprInv ctx.F_cur (2 * ctx.cv0) repri ∧
    (∀ k' < i.toNat,
      (tmpi[k']?.getD 0#32).toNat < 2 * ctx.cv0 ∧
      LitEquiv (cnfOfClauses ctx.F_cur) (ctx.scr0[g_n + 2 + k']?.getD 0#32).toNat
        (tmpi[k']?.getD 0#32).toNat) ∧
    (FullMem ctx.cfg (wsState s0 repri tmpi) ⋆ ctx.R) mi

abbrev FidEvProbeInv (ctx : FidEvCtx) (stj : FullState) (ht_sz : Nat)
    (remp : Nat) : Tup Val [i64, i64, .bool] → Mem 64 → Prop :=
  fun (slot, probes, _, ()) mp => ∃ stp : FullState,
    slot.toNat < ht_sz ∧ probes.toNat ≤ 128 ∧ remp = 128 - probes.toNat ∧
    stp.core.tmp = stj.core.tmp ∧ FidEvStOk ctx stp ∧ (FullMem ctx.cfg stp ⋆ ctx.R) mp

abbrev FidEvMatchInv (ctx : FidEvCtx) (stp : FullState) (lhs' : BitVec 32) :
    Tup Val [.bool, i32] → Mem 64 → Prop :=
  fun (matched, mlhs, ()) mmatch =>
    ∃ repr_m mclr_m : List (BitVec 32),
      repr_m.length = 2 * ctx.cfg.max_vars ∧ mclr_m.length = ctx.cfg.max_vars ∧
      FullCongReprInv ctx.F_cur (2 * ctx.cv0) repr_m ∧
      (matched = true → mlhs.toNat < 2 * ctx.cv0 ∧
        LitEquiv (cnfOfClauses ctx.F_cur) lhs'.toNat mlhs.toNat) ∧
      (FullMem ctx.cfg { stp with core :=
        { stp.core with repr := repr_m, min_clr := mclr_m } } ⋆ ctx.R) mmatch

abbrev FidEvTag0P1Inv (ctx : FidEvCtx) (s0 : FullState) (repri raw : List (BitVec 32))
    (ar_n : Nat) (il na : BitVec 32) (ml : Mem 64) : Prop :=
  ∃ tmpl : List (BitVec 32),
    tmpl.length = ctx.cfg.max_vars ∧ na.toNat ≤ il.toNat ∧ il.toNat ≤ ar_n ∧
    (∀ j, il.toNat ≤ j → j < ar_n → tmpl[j]? = raw[j]?) ∧
    (∀ j < na.toNat, ∃ k < ar_n, tmpl[j]? = raw[k]?) ∧
    (∀ k < il.toNat, s0.core.vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
      ∃ j < na.toNat, tmpl[j]? = raw[k]?) ∧
    (FullMem ctx.cfg (wsState s0 repri tmpl) ⋆ ctx.R) ml

abbrev FidEvTag0P1Brk (ctx : FidEvCtx) (s0 : FullState) (repri raw : List (BitVec 32))
    (ar_n : Nat) (il : BitVec 32) (has_false : Bool) (na : BitVec 32) (ml : Mem 64) : Prop :=
  ∃ tmpl : List (BitVec 32),
    tmpl.length = ctx.cfg.max_vars ∧ na.toNat ≤ ar_n ∧
    (has_false = true → ∃ k < ar_n,
      s0.core.vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
    (has_false = false → il.toNat = ar_n ∧
      (∀ j < na.toNat, ∃ k < ar_n, tmpl[j]? = raw[k]?) ∧
      (∀ k < ar_n, s0.core.vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
        ∃ j < na.toNat, tmpl[j]? = raw[k]?)) ∧
    (FullMem ctx.cfg (wsState s0 repri tmpl) ⋆ ctx.R) ml

abbrev FidEvTag0DedupInv (ctx : FidEvCtx) (s0 : FullState) (repri tmps : List (BitVec 32))
    (na_n : Nat) (ua si : BitVec 32) (md : Mem 64) : Prop :=
  ∃ tmpd : List (BitVec 32),
    tmpd.length = ctx.cfg.max_vars ∧ ua.toNat ≤ si.toNat ∧ si.toNat ≤ na_n ∧
    (0 < si.toNat → 0 < ua.toNat) ∧
    (∀ j, si.toNat ≤ j → j < na_n → tmpd[j]? = tmps[j]?) ∧
    (∀ j < ua.toNat, ∃ k < na_n, tmpd[j]? = tmps[k]?) ∧
    (∀ j < si.toNat, ∃ q < ua.toNat, tmpd[q]?.getD 0#32 = tmps[j]?.getD 0#32) ∧
    (FullMem ctx.cfg (wsState s0 repri tmpd) ⋆ ctx.R) md

abbrev FidEvTag0DedupBrk (ctx : FidEvCtx) (s0 : FullState) (repri tmps : List (BitVec 32))
    (lhs : BitVec 32) (na_n : Nat) (clash : Bool) (ua : BitVec 32) (md : Mem 64) : Prop :=
  ∃ tmpd : List (BitVec 32),
    tmpd.length = ctx.cfg.max_vars ∧ ua.toNat ≤ na_n ∧
    (∀ j < ua.toNat, ∃ k < na_n, tmpd[j]? = tmps[k]?) ∧
    (clash = true →
      litNeg lhs.toNat ∈ (tmps.take na_n).map BitVec.toNat ∨
      ∃ z ∈ (tmps.take na_n).map BitVec.toNat, litNeg z ∈ (tmps.take na_n).map BitVec.toNat) ∧
    (clash = false → 0 < ua.toNat ∧
      ∀ j < na_n, ∃ q < ua.toNat, tmpd[q]?.getD 0#32 = tmps[j]?.getD 0#32) ∧
    (FullMem ctx.cfg (wsState s0 repri tmpd) ⋆ ctx.R) md

abbrev FidEvTag1P1Inv (ctx : FidEvCtx) (s0 : FullState) (repri tmpi : List (BitVec 32))
    (rx0 : List Nat) (ar_n : Nat) (i1 flip1 na1 : BitVec 32) (ml : Mem 64) : Prop :=
  ∃ tmpl : List (BitVec 32),
    tmpl.length = ctx.cfg.max_vars ∧ na1.toNat ≤ i1.toNat ∧ i1.toNat ≤ ar_n ∧
    (flip1 = 0#32 ∨ flip1 = 1#32) ∧
    (∀ q, i1.toNat ≤ q → q < ar_n → tmpl[q]? = tmpi[q]?) ∧
    (∀ q < na1.toNat, (tmpl[q]?.getD 0#32).toNat < 2 * ctx.cv0 ∧
      (tmpl[q]?.getD 0#32).toNat % 2 = 0) ∧
    (∀ α : Nat → Bool, (cnfOfClauses ctx.F_cur).Sat α →
      xorEvalList α (rx0.take i1.toNat) =
        ((flip1 == 1#32) != xorEvalList α ((tmpl.take na1.toNat).map BitVec.toNat))) ∧
    (FullMem ctx.cfg (wsState s0 repri tmpl) ⋆ ctx.R) ml

abbrev FidEvTag1DedupInv (ctx : FidEvCtx) (s0 : FullState) (repri tmps : List (BitVec 32))
    (lhs' : BitVec 32) (na1_n : Nat) : Tup Val [i32, i32] → Mem 64 → Prop :=
  fun (jd, ua, ()) md => ∃ tmpd : List (BitVec 32),
    tmpd.length = ctx.cfg.max_vars ∧ ua.toNat ≤ jd.toNat ∧ jd.toNat ≤ na1_n ∧
    (∀ q, jd.toNat ≤ q → q < na1_n → tmpd[q]? = tmps[q]?) ∧
    (∀ q < ua.toNat, (tmpd[q]?.getD 0#32).toNat < 2 * ctx.cv0 ∧
      (tmpd[q]?.getD 0#32).toNat % 2 = 0) ∧
    (∀ α : Nat → Bool, (cnfOfClauses ctx.F_cur).Sat α →
      evalLitVal α lhs'.toNat =
        (xorEvalList α ((tmpd.take ua.toNat).map BitVec.toNat) !=
         xorEvalList α (((tmps.drop jd.toNat).take (na1_n - jd.toNat)).map BitVec.toNat))) ∧
    (FullMem ctx.cfg (wsState s0 repri tmpd) ⋆ ctx.R) md

/-! ## 2. Pure Semantic Lemmas for XOR Self-Cancel, ITE-to-XOR, and ITE-to-AND -/

theorem fid_tag1_match_equiv {F_cur : List (List Nat)} {cv0 : Nat}
    {lhs ml : BitVec 32} {tmps : List (BitVec 32)} {harity : BitVec 32}
    (hgate : FidHashGateOk F_cur cv0 lhs tmps 1#32 harity)
    (hm : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      evalLitVal α ml.toNat = xorEvalList α ((tmps.take harity.toNat).map BitVec.toNat)) :
    LitEquiv (cnfOfClauses F_cur) lhs.toNat ml.toNat := by
  refine litEquiv_of_eval_eq fun α hα => ?_
  have hxor := (hgate.2.2.1 rfl).2.2.2 α hα
  rw [hxor, hm α hα]

theorem bv32_and1_eq01 (x : BitVec 32) : (x &&& 1#32) = 0#32 ∨ (x &&& 1#32) = 1#32 := by
  have hlt : (x &&& 1#32).toNat < 2 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
    exact Nat.mod_lt _ (by decide)
  rcases (by omega : (x &&& 1#32).toNat = 0 ∨ (x &&& 1#32).toNat = 1) with h0 | h1
  · exact Or.inl (BitVec.eq_of_toNat_eq h0)
  · exact Or.inr (BitVec.eq_of_toNat_eq h1)

theorem bv32_xor1_and1_eq01 (x : BitVec 32) :
    (1#32 ^^^ (x &&& 1#32)) = 0#32 ∨ (1#32 ^^^ (x &&& 1#32)) = 1#32 := by
  rcases bv32_and1_eq01 x with h | h <;> rw [h] <;> decide

theorem list_getElem?_eraseIdx_lt {α : Type _} (xs : List α) {i k : Nat} (hk : k < i) :
    (xs.eraseIdx i)[k]? = xs[k]? := by
  by_cases hkl : k < xs.length
  · have hlen : k < (xs.eraseIdx i).length := by rw [List.length_eraseIdx]; split <;> omega
    rw [List.getElem?_eq_getElem hlen, List.getElem_eraseIdx_of_lt hlen hk,
      List.getElem?_eq_getElem hkl]
  · rw [List.getElem?_eq_none (by rw [List.length_eraseIdx]; split <;> omega),
      List.getElem?_eq_none (by omega)]

theorem list_getElem?_eraseIdx_ge {α : Type _} (xs : List α) {i k : Nat}
    (hge : i ≤ k) (hk1 : k + 1 < xs.length) :
    (xs.eraseIdx i)[k]? = xs[k + 1]? := by
  have hlen : k < (xs.eraseIdx i).length := by rw [List.length_eraseIdx]; split <;> omega
  rw [List.getElem?_eq_getElem hlen, List.getElem_eraseIdx_of_ge hlen hge,
    List.getElem?_eq_getElem hk1]

theorem list_map_eraseIdx {α β : Type _} (f : α → β) :
    ∀ (xs : List α) (i : Nat), (xs.eraseIdx i).map f = (xs.map f).eraseIdx i
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: t, i + 1 => by simp [List.eraseIdx_cons_succ, list_map_eraseIdx f t i]

theorem fid_xor_self_shift_done {F_cur : List (List Nat)} {cv0 ua_n self_i : Nat}
    {lhs' : BitVec 32} {tmpd tmpj : List (BitVec 32)}
    (hsi : self_i < ua_n) (hua_le : ua_n ≤ tmpd.length) (htl_j : tmpj.length = tmpd.length)
    (hpref : ∀ k < ua_n - 1, tmpj[k]? = ((tmpd.take ua_n).eraseIdx self_i)[k]?)
    (hget : tmpd[self_i]?.getD 0#32 = lhs' &&& ~~~1#32)
    (hlt_d : ∀ q < ua_n, (tmpd[q]?.getD 0#32).toNat < 2 * cv0 ∧
      (tmpd[q]?.getD 0#32).toNat % 2 = 0)
    (hxor_d : XorListGateDef (cnfOfClauses F_cur) lhs'.toNat
      ((tmpd.take ua_n).map BitVec.toNat)) :
    (∀ q < ua_n - 1, (tmpj[q]?.getD 0#32).toNat < 2 * cv0 ∧
      (tmpj[q]?.getD 0#32).toNat % 2 = 0) ∧
    (∀ α, (cnfOfClauses F_cur).Sat α →
      decide ((lhs' &&& 1#32) ≠ 0#32) =
        xorEvalList α ((tmpj.take (ua_n - 1)).map BitVec.toNat)) := by
  have htk_len : (tmpd.take ua_n).length = ua_n := by simp [List.length_take]; omega
  have her_len : ((tmpd.take ua_n).eraseIdx self_i).length = ua_n - 1 := by
    rw [List.length_eraseIdx, ite_eq_left (by omega), htk_len]
  have htake_eq : tmpj.take (ua_n - 1) = (tmpd.take ua_n).eraseIdx self_i := by
    apply List.ext_getElem
    · rw [List.length_take, her_len]; omega
    · intro k hk1 hk2
      have hk : k < ua_n - 1 := by rw [her_len] at hk2; exact hk2
      have h := hpref k hk
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hk2] at h
      simp only [List.getElem_take]; exact Option.some.inj h
  refine ⟨fun q hq => ?_, fun α hα => ?_⟩
  · rw [hpref q hq]
    by_cases hqs : q < self_i
    · rw [list_getElem?_eraseIdx_lt _ hqs, List.getElem?_take_of_lt (by omega)]
      exact hlt_d q (by omega)
    · rw [list_getElem?_eraseIdx_ge _ (by omega) (by rw [htk_len]; omega),
        List.getElem?_take_of_lt (by omega)]
      exact hlt_d (q + 1) (by omega)
  · rw [htake_eq, list_map_eraseIdx]
    have hmap_len : self_i < ((tmpd.take ua_n).map BitVec.toNat).length := by
      rw [List.length_map, htk_len]; exact hsi
    have hmap_get : ((tmpd.take ua_n).map BitVec.toNat)[self_i]'hmap_len =
        (lhs' &&& ~~~1#32).toNat := by
      simp only [List.getElem_map, List.getElem_take]
      rw [← hget, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact fid_xor_self_cancel_sem hmap_len hmap_get (hxor_d α hα)

theorem fid_ite_to_xor_pack {F_cur : List (List Nat)} {cv0 : Nat}
    {lhs cl tl el : BitVec 32}
    (hite : IteGateDef (cnfOfClauses F_cur) lhs.toNat cl.toNat tl.toNat el.toNat)
    (hlhs : lhs.toNat < 2 * cv0) (hcl : cl.toNat < 2 * cv0) (htl : tl.toNat < 2 * cv0)
    (hte : tl = el ^^^ 1#32) :
    let lhs_x := lhs ^^^ ((1#32 ^^^ cl ^^^ tl) &&& 1#32)
    let r0 := cl &&& ~~~1#32; let r1 := tl &&& ~~~1#32
    lhs_x.toNat < 2 * cv0 ∧ r0.toNat < 2 * cv0 ∧ r1.toNat < 2 * cv0 ∧
    XorListGateDef (cnfOfClauses F_cur) lhs_x.toNat [r0.toNat, r1.toNat] := by
  intro lhs_x r0 r1
  have hel_neg : el.toNat = litNeg tl.toNat := by
    have heq : el = tl ^^^ 1#32 := by rw [hte, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    rw [heq, FullCongHelpers.bv32_xor1_eq_litNeg]
  have hsem := fid_ite_to_xor_sem (hel_neg ▸ hite)
  refine ⟨xor1_bit01_lt hlhs (bv32_and1_eq01 _),
    by dsimp only [r0]; rw [m6_bv32_and_not1_toNat]; omega,
    by dsimp only [r1]; rw [m6_bv32_and_not1_toNat]; omega,
    fun α hα => by rw [xorEvalList_pair]; exact hsem α hα⟩

theorem fid_xor_pair_eq_entails {F_cur : List (List Nat)} {lhs r0 : BitVec 32}
    (hxor : XorListGateDef (cnfOfClauses F_cur) lhs.toNat [r0.toNat, r0.toNat]) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg lhs.toNat]) := by
  refine entails_of_eval_mem fun α hα => ⟨litNeg lhs.toNat, List.mem_cons_self .., ?_⟩
  have h := hxor α hα
  rw [xorEvalList_pair] at h
  rw [evalLitVal_litNeg, h]; cases evalLitVal α r0.toNat <;> rfl

theorem fid_pair_xor_hash_ok {F_cur : List (List Nat)} {cv0 : Nat}
    {lhs r0 r1 : BitVec 32} {tmpi : List (BitVec 32)}
    (ht2 : 2 ≤ tmpi.length) (h2cv : 2 ≤ cv0) (hr0 : r0.toNat < 2 * cv0) (hr1 : r1.toNat < 2 * cv0)
    (hxor : XorListGateDef (cnfOfClauses F_cur) lhs.toNat [r0.toNat, r1.toNat]) :
    let v0 := if r0.ult r1 then r0 else r1
    let v1 := if r0.ult r1 then r1 else r0
    FidHashGateOk F_cur cv0 lhs ((tmpi.set 0 v0).set 1 v1) 1#32 2#32 := by
  intro v0 v1
  let tmps := (tmpi.set 0 v0).set 1 v1
  have hg0 : tmps[0]?.getD 0#32 = v0 := by
    dsimp only [tmps]; rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by omega),
      Option.getD_some]
  have hg1 : tmps[1]?.getD 0#32 = v1 := by
    dsimp only [tmps]; rw [List.getElem?_set_self (by simp; omega), Option.getD_some]
  have hlen : tmps.length = tmpi.length := by simp [tmps]
  have htwo : (tmps.take 2).map BitVec.toNat = [v0.toNat, v1.toNat] := by
    apply List.ext_getElem
    · simp [List.length_take, hlen]; omega
    · intro k hk1 hk2
      rcases k with _ | _ | k'
      · simp only [List.getElem_map, List.getElem_take, List.getElem_cons_zero]
        rw [← hg0, List.getElem?_eq_getElem (by omega), Option.getD_some]
      · simp only [List.getElem_map, List.getElem_take, List.getElem_cons_succ,
          List.getElem_cons_zero]
        rw [← hg1, List.getElem?_eq_getElem (by omega), Option.getD_some]
      · simp at hk2; omega
  refine ⟨h2cv, fun h => absurd h (by decide), fun _ => ⟨by decide, by decide, fun k hk => ?_, ?_⟩,
    fun h => absurd h (by decide)⟩
  · change k < 2 at hk; rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · rw [hg0]; dsimp only [v0]; split <;> assumption
    · rw [hg1]; dsimp only [v1]; split <;> assumption
  · intro α hα; rw [show (2#32 : BitVec 32).toNat = 2 from rfl, htwo, xorEvalList_pair]
    have h := hxor α hα; rw [xorEvalList_pair] at h; rw [h]
    dsimp only [v0, v1]; split
    · rfl
    · cases evalLitVal α r0.toNat <;> cases evalLitVal α r1.toNat <;> rfl

abbrev And2Sem (F_cur : List (List Nat)) (lhs a0 a1 : BitVec 32) : Prop :=
  ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
    evalLitVal α lhs.toNat = (evalLitVal α a0.toNat && evalLitVal α a1.toNat)

theorem fid_and2_eq_equiv {F_cur : List (List Nat)} {lhs a0 : BitVec 32}
    (h : And2Sem F_cur lhs a0 a0) : LitEquiv (cnfOfClauses F_cur) lhs.toNat a0.toNat :=
  litEquiv_of_eval_eq fun α hα => by rw [h α hα]; cases evalLitVal α a0.toNat <;> rfl

theorem fid_and2_clash_entails {F_cur : List (List Nat)} {lhs a0 a1 : BitVec 32}
    (h : And2Sem F_cur lhs a0 a1)
    (hcl : a0 = a1 ^^^ 1#32 ∨ a0 = lhs ^^^ 1#32 ∨ a1 = lhs ^^^ 1#32) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg lhs.toNat]) := by
  refine entails_of_eval_mem fun α hα => ⟨litNeg lhs.toNat, List.mem_cons_self .., ?_⟩
  have he := h α hα; rw [evalLitVal_litNeg]
  rcases hcl with rfl | rfl | rfl
  · rw [FullCongHelpers.bv32_xor1_eq_litNeg, evalLitVal_litNeg] at he
    rw [he]; cases evalLitVal α a1.toNat <;> rfl
  · rw [FullCongHelpers.bv32_xor1_eq_litNeg, evalLitVal_litNeg] at he
    cases hl : evalLitVal α lhs.toNat <;> cases evalLitVal α a1.toNat <;> simp_all
  · rw [FullCongHelpers.bv32_xor1_eq_litNeg, evalLitVal_litNeg] at he
    cases hl : evalLitVal α lhs.toNat <;> cases evalLitVal α a0.toNat <;> simp_all

theorem fid_and2_lhs_true_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {lhs a0 a1 : BitVec 32} (hlhs : lhs.toNat < 2 * k.cur_vars)
    (hv1 : k.vals[lhs.toNat]?.getD 0#8 = 1#8) (h : And2Sem F_cur lhs a0 a1) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [a0.toNat]) ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [a1.toNat]) := by
  have ht : ∀ α, (cnfOfClauses F_cur).Sat α →
      evalLitVal α a0.toNat = true ∧ evalLitVal α a1.toNat = true := fun α hα => by
    have h1 := entails_eval_true (vals1_entails hw hcl0 hlhs hv1) hα
    have he := h α hα; rw [h1] at he
    exact Bool.and_eq_true_iff.mp he.symm
  exact ⟨entails_of_eval_mem fun α hα => ⟨a0.toNat, List.mem_cons_self .., (ht α hα).1⟩,
    entails_of_eval_mem fun α hα => ⟨a1.toNat, List.mem_cons_self .., (ht α hα).2⟩⟩

theorem fid_pair_and_hash_ok {F_cur : List (List Nat)} {cv0 : Nat}
    {lhs a0 a1 : BitVec 32} {tmpi : List (BitVec 32)}
    (ht2 : 2 ≤ tmpi.length) (h2cv : 2 ≤ cv0) (h : And2Sem F_cur lhs a0 a1) :
    let v0 := if a0.ult a1 then a0 else a1
    let v1 := if a0.ult a1 then a1 else a0
    FidHashGateOk F_cur cv0 lhs ((tmpi.set 0 v0).set 1 v1) 0#32 2#32 := by
  intro v0 v1
  let tmps := (tmpi.set 0 v0).set 1 v1
  have hg0 : tmps[0]?.getD 0#32 = v0 := by
    dsimp only [tmps]; rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by omega),
      Option.getD_some]
  have hg1 : tmps[1]?.getD 0#32 = v1 := by
    dsimp only [tmps]; rw [List.getElem?_set_self (by simp; omega), Option.getD_some]
  refine ⟨h2cv, fun _ => ⟨by decide, by decide, fun α hα => ?_⟩,
    fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  rw [show (2#32 : BitVec 32).toNat = 2 from rfl,
    show List.range 2 = [0, 1] from rfl]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  dsimp only [tmps] at hg0 hg1
  rw [hg0, hg1, h α hα]; dsimp only [v0, v1]; split
  · rfl
  · cases evalLitVal α a0.toNat <;> cases evalLitVal α a1.toNat <;> rfl

theorem fid_and2_of_vt_pos {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {lhs cl tl el : BitVec 32} (hite : IteGateDef (cnfOfClauses F_cur) lhs.toNat cl.toNat
      tl.toNat el.toNat) (htl : tl.toNat < 2 * k.cur_vars)
    (hvt : k.vals[tl.toNat]?.getD 0#8 = 1#8) :
    And2Sem F_cur (lhs ^^^ 1#32) (cl ^^^ 1#32) (el ^^^ 1#32) := fun α hα => by
  rw [FullCongHelpers.bv32_xor1_eq_litNeg, FullCongHelpers.bv32_xor1_eq_litNeg,
    FullCongHelpers.bv32_xor1_eq_litNeg]
  exact fid_ite_and_vt_true hite (fun _ hβ => entails_eval_true (vals1_entails hw hcl0 htl hvt) hβ)
    α hα

theorem fid_and2_of_vt_neg {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {lhs cl tl el : BitVec 32} (hite : IteGateDef (cnfOfClauses F_cur) lhs.toNat cl.toNat
      tl.toNat el.toNat) (htl : tl.toNat < 2 * k.cur_vars)
    (hvt : k.vals[tl.toNat]?.getD 0#8 = 0xFF#8) :
    And2Sem F_cur lhs (cl ^^^ 1#32) el := fun α hα => by
  rw [FullCongHelpers.bv32_xor1_eq_litNeg]
  exact fid_ite_and_vt_false hite
    (fun _ hβ => entails_neg_eval_false (valsff_entails_neg hw hcl0 htl hvt) hβ) α hα

theorem fid_and2_of_ve_pos {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {lhs cl tl el : BitVec 32} (hite : IteGateDef (cnfOfClauses F_cur) lhs.toNat cl.toNat
      tl.toNat el.toNat) (hel : el.toNat < 2 * k.cur_vars)
    (hve : k.vals[el.toNat]?.getD 0#8 = 1#8) :
    And2Sem F_cur (lhs ^^^ 1#32) cl (tl ^^^ 1#32) := fun α hα => by
  rw [FullCongHelpers.bv32_xor1_eq_litNeg, FullCongHelpers.bv32_xor1_eq_litNeg]
  exact fid_ite_and_ve_true hite (fun _ hβ => entails_eval_true (vals1_entails hw hcl0 hel hve) hβ)
    α hα

theorem fid_and2_of_ve_neg {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {lhs cl tl el : BitVec 32} (hite : IteGateDef (cnfOfClauses F_cur) lhs.toNat cl.toNat
      tl.toNat el.toNat) (hel : el.toNat < 2 * k.cur_vars)
    (hve : k.vals[el.toNat]?.getD 0#8 = 0xFF#8) :
    And2Sem F_cur lhs cl tl := fun α hα =>
  fid_ite_and_ve_false hite
    (fun _ hβ => entails_neg_eval_false (valsff_entails_neg hw hcl0 hel hve) hβ) α hα

theorem bv32_xor1_lt_cv {x : BitVec 32} {cv : Nat} (hx : x.toNat < 2 * cv) :
    (x ^^^ 1#32).toNat < 2 * cv := by
  rw [FullCongHelpers.bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hx


end Helpers

end LeanQbe.T.Examples.Kissat.FullFidelityCong

end
