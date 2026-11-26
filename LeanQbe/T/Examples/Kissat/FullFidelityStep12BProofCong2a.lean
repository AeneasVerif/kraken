/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep12BProofSpec
public import LeanQbe.T.Examples.Kissat.FullFidelityCongProof2a0
import LeanQbe.T.Examples.Kissat.FullCongLemmas1
import LeanQbe.T.Examples.Kissat.FullCongLemmas2
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.C0Agrees
import LeanQbe.T.Logic.MemLemmas

/-!
# Kissat Fidelity Step 12B — Congruence `eval_gate` Support (`FullFidelityStep12BProofCong2a`)

Evaluation context, state invariants, frame lemmas, and wide-AND (`≤ 1,000,000`, `tag ∈ {0, 3}`)
helper theorems supporting `full_cong_eval_gate_s12b_wp` (`FullFidelityStep12BProofCong2b`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep12B

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
open LeanQbe.T.Examples.Kissat.FullM8FidV12
open LeanQbe.T.Examples.Kissat.FullFidelityCong
open Kraken.Bedrock2.Test
open scoped FullArenaTactics Full.FullCongTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6CongSubst.M6bHeadTactics

/-! ## 1. Evaluation Context, State Invariants & Loop Invariant Abbreviations -/

@[expose] public section

structure Step12BEvCtx where
  maxA : Nat
  hmaxA : maxA ≤ step12BCongAndArityMax
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

abbrev Step12BEvStOk (ctx : Step12BEvCtx) (st : FullState) : Prop :=
  FullDenseInvW ctx.cfg ctx.F0 ctx.F_cur st ∧
  st.core.cur_vars = ctx.cv0 ∧ st.core.fuel = ctx.fuel0 ∧
  st.core.arena = ctx.ar0 ∧ st.core.arena_len = ctx.alen0 ∧
  FullCongReprInv ctx.F_cur (2 * ctx.cv0) st.core.repr ∧
  Step12BCongHtInv ctx.maxA ctx.F_cur ctx.cv0 ctx.scr0 st.scratch.scratch_buf
    ctx.g_len ctx.ht_off ctx.ht_sz ∧
  Step12BQueueCtx ctx.cfg st.scratch.scratch_buf ctx.g_len ctx.ctrl_off ctx.ht_off ctx.ht_sz ∧
  Step12BScrFrame ctx.cfg ctx.g_len ctx.ctrl_off ctx.ht_off ctx.ht_sz
    ctx.scr_init st.scratch.scratch_buf

abbrev Step12BHashGateOk (F_cur : List (List Nat)) (cv0 : Nat) (lhs : BitVec 32)
    (tmps : List (BitVec 32)) (htag harity : BitVec 32) : Prop :=
  harity.toNat ≤ cv0 ∧
  (htag = 0#32 → 2 ≤ harity.toNat ∧ harity.toNat ≤ step12BCongAndArityMax ∧
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

structure Step12BEvOutCtx (ctx : Step12BEvCtx) (s0 : FullState) (Q : Post [i64]) : Prop where
  hcv0 : ctx.cv0 = s0.core.cur_vars
  hf0 : ctx.fuel0 = s0.core.fuel
  ha0 : ctx.ar0 = s0.core.arena
  hal0 : ctx.alen0 = s0.core.arena_len
  hs0 : ctx.scr_init = s0.scratch.scratch_buf
  hle : ctx.g_len ≤ ctx.ht_off
  hht : ctx.ht_off + ctx.ht_sz ≤ ctx.cfg.scratch_cap
  hpref0 : ∀ idx < ctx.g_len, ctx.scr_init[idx]? = ctx.scr0[idx]?
  hq0 : Step12BQueueCtx ctx.cfg ctx.scr_init ctx.g_len ctx.ctrl_off ctx.ht_off ctx.ht_sz
  hQ : ∀ (r : BitVec 64) s' m',
    FullDenseInvW ctx.cfg ctx.F0 ctx.F_cur s' →
    s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
    s'.core.arena = s0.core.arena → s'.core.arena_len = s0.core.arena_len →
    FullCongReprInv ctx.F_cur (2 * s'.core.cur_vars) s'.core.repr →
    (∀ idx < ctx.g_len, s'.scratch.scratch_buf[idx]? = ctx.scr0[idx]?) →
    Step12BCongHtInv ctx.maxA ctx.F_cur s'.core.cur_vars ctx.scr0 s'.scratch.scratch_buf
      ctx.g_len ctx.ht_off ctx.ht_sz →
    Step12BQueueCtx ctx.cfg s'.scratch.scratch_buf ctx.g_len ctx.ctrl_off ctx.ht_off ctx.ht_sz →
    ((r &&& 2#64) = 0#64 →
      (∀ idx < ctx.cfg.scratch_cap, idx < ctx.ht_off →
        (ctx.ctrl_off = ctx.cfg.scratch_cap →
          s'.scratch.scratch_buf[idx]? = s0.scratch.scratch_buf[idx]?) ∧
        (∀ occ_bkt bkt_off inq_off q_off,
          Step12BCtrlLayout ctx.cfg s0.scratch.scratch_buf ctx.g_len ctx.ctrl_off
            occ_bkt bkt_off inq_off q_off ctx.ht_off ctx.ht_sz →
          idx ≠ ctx.ctrl_off + 5 →
          ¬ (q_off ≤ idx ∧ idx < q_off + occ_bkt) →
          ¬ (inq_off ≤ idx ∧ idx < inq_off + occ_bkt) →
          s'.scratch.scratch_buf[idx]? = s0.scratch.scratch_buf[idx]?))) →
    ((r &&& 2#64) ≠ 0#64 → ctx.F0.Unsat) →
    (FullMem ctx.cfg s' ⋆ ctx.R) m' → Q (r, ()) m'

abbrev Step12BEvOut (ctx : Step12BEvCtx) (lhs' htag' harity : BitVec 32) (nh' : Bool)
    (mj : Mem 64) : Prop :=
  ∃ stj : FullState,
    Step12BEvStOk ctx stj ∧
    (nh' = true → Step12BHashGateOk ctx.F_cur ctx.cv0 lhs' stj.core.tmp htag' harity) ∧
    (nh' = true → lhs'.toNat < 2 * ctx.cv0) ∧
    (FullMem ctx.cfg stj ⋆ ctx.R) mj

abbrev Step12BEvFindInv (ctx : Step12BEvCtx) (s0 : FullState) (g_n ar_n : Nat) :
    Tup Val [i32] → Mem 64 → Prop :=
  fun (i, ()) mi => ∃ (repri tmpi : List (BitVec 32)),
    repri.length = 2 * ctx.cfg.max_vars ∧ tmpi.length = ctx.cfg.max_vars ∧
    i.toNat ≤ ar_n ∧ FullCongReprInv ctx.F_cur (2 * ctx.cv0) repri ∧
    (∀ k' < i.toNat,
      (tmpi[k']?.getD 0#32).toNat < 2 * ctx.cv0 ∧
      LitEquiv (cnfOfClauses ctx.F_cur) (ctx.scr0[g_n + 2 + k']?.getD 0#32).toNat
        (tmpi[k']?.getD 0#32).toNat) ∧
    (FullMem ctx.cfg (wsState s0 repri tmpi) ⋆ ctx.R) mi

abbrev Step12BEvProbeInv (ctx : Step12BEvCtx) (stj : FullState) (ht_sz : Nat)
    (remp : Nat) : Tup Val [i64, i64, .bool] → Mem 64 → Prop :=
  fun (slot, probes, _, ()) mp => ∃ stp : FullState,
    slot.toNat < ht_sz ∧ probes.toNat ≤ 128 ∧ remp = 128 - probes.toNat ∧
    stp.core.tmp = stj.core.tmp ∧ Step12BEvStOk ctx stp ∧ (FullMem ctx.cfg stp ⋆ ctx.R) mp

abbrev Step12BEvMatchInv (ctx : Step12BEvCtx) (stp : FullState) (lhs' : BitVec 32) :
    Tup Val [.bool, i32] → Mem 64 → Prop :=
  fun (matched, mlhs, ()) mmatch =>
    ∃ (repr_m mclr_m : List (BitVec 32)) (lm_m : List (BitVec 8)),
      let st_m : FullState :=
        { stp with core :=
          { stp.core with repr := repr_m, min_clr := mclr_m, lit_mark := lm_m } }
      repr_m.length = 2 * ctx.cfg.max_vars ∧ mclr_m.length = ctx.cfg.max_vars ∧
      lm_m.length = 2 * ctx.cfg.max_vars ∧
      FullLitMarksClear ctx.cfg st_m ∧
      FullCongReprInv ctx.F_cur (2 * ctx.cv0) repr_m ∧
      (matched = true → mlhs.toNat < 2 * ctx.cv0 ∧
        LitEquiv (cnfOfClauses ctx.F_cur) lhs'.toNat mlhs.toNat) ∧
      (FullMem ctx.cfg st_m ⋆ ctx.R) mmatch

abbrev Step12BEvTag0P1Inv (ctx : Step12BEvCtx) (s0 : FullState) (repri raw : List (BitVec 32))
    (ar_n : Nat) (il na : BitVec 32) (ml : Mem 64) : Prop :=
  ∃ tmpl : List (BitVec 32),
    tmpl.length = ctx.cfg.max_vars ∧ na.toNat ≤ il.toNat ∧ il.toNat ≤ ar_n ∧
    (∀ j, il.toNat ≤ j → j < ar_n → tmpl[j]? = raw[j]?) ∧
    (∀ j < na.toNat, ∃ k < ar_n, tmpl[j]? = raw[k]?) ∧
    (∀ k < il.toNat, s0.core.vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
      ∃ j < na.toNat, tmpl[j]? = raw[k]?) ∧
    (FullMem ctx.cfg (wsState s0 repri tmpl) ⋆ ctx.R) ml

abbrev Step12BEvTag0P1Brk (ctx : Step12BEvCtx) (s0 : FullState) (repri raw : List (BitVec 32))
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

abbrev Step12BEvTag0DedupInv (ctx : Step12BEvCtx) (s0 : FullState) (repri tmps : List (BitVec 32))
    (na_n : Nat) (ua si : BitVec 32) (md : Mem 64) : Prop :=
  ∃ tmpd : List (BitVec 32),
    tmpd.length = ctx.cfg.max_vars ∧ ua.toNat ≤ si.toNat ∧ si.toNat ≤ na_n ∧
    (0 < si.toNat → 0 < ua.toNat) ∧
    (∀ j, si.toNat ≤ j → j < na_n → tmpd[j]? = tmps[j]?) ∧
    (∀ j < ua.toNat, ∃ k < na_n, tmpd[j]? = tmps[k]?) ∧
    (∀ j < si.toNat, ∃ q < ua.toNat, tmpd[q]?.getD 0#32 = tmps[j]?.getD 0#32) ∧
    (FullMem ctx.cfg (wsState s0 repri tmpd) ⋆ ctx.R) md

abbrev Step12BEvTag0DedupBrk (ctx : Step12BEvCtx) (s0 : FullState) (repri tmps : List (BitVec 32))
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

abbrev Step12BEvTag1P1Inv (ctx : Step12BEvCtx) (s0 : FullState) (repri tmpi : List (BitVec 32))
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

abbrev Step12BEvTag1DedupInv (ctx : Step12BEvCtx) (s0 : FullState) (repri tmps : List (BitVec 32))
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

end

/-! ## 2. Projections, Frame Helpers & Gate-Type Bridges -/

public section

theorem step12BEvStOk_dw {ctx : Step12BEvCtx} {st : FullState} (h : Step12BEvStOk ctx st) :
    FullDenseInvW ctx.cfg ctx.F0 ctx.F_cur st := h.1

theorem step12BEvStOk_wit {ctx : Step12BEvCtx} {st : FullState} (h : Step12BEvStOk ctx st) :
    FullWitnessInv ctx.cfg ctx.F0 ctx.F_cur st.core := h.1.2.1

theorem step12BEvStOk_mk {ctx : Step12BEvCtx} {st : FullState} (h : Step12BEvStOk ctx st) :
    FullLitMarksClear ctx.cfg st := h.1.2.2.1

theorem step12BEvStOk_cl {ctx : Step12BEvCtx} {st : FullState} (h : Step12BEvStOk ctx st) :
    st.core.cur_level = 0 := h.1.2.2.2.2.2.1

theorem step12BEvStOk_cv {ctx : Step12BEvCtx} {st : FullState} (h : Step12BEvStOk ctx st) :
    st.core.cur_vars = ctx.cv0 := h.2.1

theorem step12BEvStOk_repr {ctx : Step12BEvCtx} {st : FullState} (h : Step12BEvStOk ctx st) :
    FullCongReprInv ctx.F_cur (2 * ctx.cv0) st.core.repr := h.2.2.2.2.2.1

theorem step12BEvStOk_ht {ctx : Step12BEvCtx} {st : FullState} (h : Step12BEvStOk ctx st) :
    Step12BCongHtInv ctx.maxA ctx.F_cur ctx.cv0 ctx.scr0 st.scratch.scratch_buf
      ctx.g_len ctx.ht_off ctx.ht_sz := h.2.2.2.2.2.2.1

theorem step12BEvStOk_fr {ctx : Step12BEvCtx} {st : FullState} (h : Step12BEvStOk ctx st) :
    Step12BScrFrame ctx.cfg ctx.g_len ctx.ctrl_off ctx.ht_off ctx.ht_sz
      ctx.scr_init st.scratch.scratch_buf := h.2.2.2.2.2.2.2.2

theorem step12BQueueCtx_set_ht {c : FullCfg} {scr : List (BitVec 32)}
    {g_len ctrl_off ht_off ht_sz : Nat}
    (hq : Step12BQueueCtx c scr g_len ctrl_off ht_off ht_sz) {slot : Nat} (v : BitVec 32) :
    Step12BQueueCtx c (scr.set (ht_off + slot) v) g_len ctrl_off ht_off ht_sz := by
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
    have h4' : (scr.set (ht_off + slot) v)[ctrl_off + 4]? = scr[ctrl_off + 4]? :=
      List.getElem?_set_ne (by omega)
    have h5' : (scr.set (ht_off + slot) v)[ctrl_off + 5]? = scr[ctrl_off + 5]? :=
      List.getElem?_set_ne (by omega)
    rw [h5'] at hk; rw [h4']
    have hmod := Nat.mod_lt ((scr[ctrl_off + 4]?.getD 0#32).toNat + k) h5
    rw [List.getElem?_set_ne (by omega)]; exact hqok k hk

theorem step12BScrFrame_ht_set {c : FullCfg} {g_len ctrl_off ht_off ht_sz : Nat}
    {scr0 scr : List (BitVec 32)} (hfr : Step12BScrFrame c g_len ctrl_off ht_off ht_sz scr0 scr)
    (slot : Nat) (v : BitVec 32) :
    Step12BScrFrame c g_len ctrl_off ht_off ht_sz scr0 (scr.set (ht_off + slot) v) := by
  refine ⟨by rw [List.length_set]; exact hfr.1, fun idx h1 h2 => ?_⟩
  rw [List.getElem?_set_ne (by omega)]; exact hfr.2 idx h1 h2

theorem step12BScrFrame_enq {c : FullCfg} {g_len ctrl_off ht_off ht_sz : Nat}
    {scr0 scr1 scr2 : List (BitVec 32)}
    (hfr1 : Step12BScrFrame c g_len ctrl_off ht_off ht_sz scr0 scr1)
    (hq1 : Step12BQueueCtx c scr1 g_len ctrl_off ht_off ht_sz) (hlen2 : scr2.length = c.scratch_cap)
    (hcap_eq : ctrl_off = c.scratch_cap → scr2 = scr1)
    (hlay2 : ∀ occ_bkt bkt_off inq_off q_off,
      Step12BCtrlLayout c scr1 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz →
      scr2[ctrl_off]? = some (BitVec.ofNat 32 occ_bkt) ∧
      scr2[ctrl_off + 1]? = some (BitVec.ofNat 32 bkt_off) ∧
      scr2[ctrl_off + 2]? = some (BitVec.ofNat 32 inq_off) ∧
      scr2[ctrl_off + 3]? = some (BitVec.ofNat 32 q_off) ∧
      scr2[ctrl_off + 4]? = scr1[ctrl_off + 4]? ∧
      scr2[ctrl_off + 6]? = some (BitVec.ofNat 32 ht_off) ∧
      scr2[ctrl_off + 7]? = some (BitVec.ofNat 32 ht_sz) ∧
      (∀ idx, idx ≠ ctrl_off + 5 → ¬ (q_off ≤ idx ∧ idx < q_off + occ_bkt) →
        ¬ (inq_off ≤ idx ∧ idx < inq_off + occ_bkt) → scr2[idx]? = scr1[idx]?)) :
    Step12BScrFrame c g_len ctrl_off ht_off ht_sz scr0 scr2 := by
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
    unfold step12BOccBktMax at ho0 ho1
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

theorem step12BCongHtInv_enq {maxA : Nat} {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len ctrl_off ht_off ht_sz : Nat} {scr_init scr1 scr2 : List (BitVec 32)}
    (hht : Step12BCongHtInv maxA F_cur cv scr_init scr1 g_len ht_off ht_sz)
    (hq1 : Step12BQueueCtx c scr1 g_len ctrl_off ht_off ht_sz)
    (hcap_eq : ctrl_off = c.scratch_cap → scr2 = scr1)
    (hlay2 : ∀ occ_bkt bkt_off inq_off q_off,
      Step12BCtrlLayout c scr1 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz →
      scr2[ctrl_off]? = some (BitVec.ofNat 32 occ_bkt) ∧
      scr2[ctrl_off + 1]? = some (BitVec.ofNat 32 bkt_off) ∧
      scr2[ctrl_off + 2]? = some (BitVec.ofNat 32 inq_off) ∧
      scr2[ctrl_off + 3]? = some (BitVec.ofNat 32 q_off) ∧
      scr2[ctrl_off + 4]? = scr1[ctrl_off + 4]? ∧
      scr2[ctrl_off + 6]? = some (BitVec.ofNat 32 ht_off) ∧
      scr2[ctrl_off + 7]? = some (BitVec.ofNat 32 ht_sz) ∧
      (∀ idx, idx ≠ ctrl_off + 5 → ¬ (q_off ≤ idx ∧ idx < q_off + occ_bkt) →
        ¬ (inq_off ≤ idx ∧ idx < inq_off + occ_bkt) → scr2[idx]? = scr1[idx]?)) :
    Step12BCongHtInv maxA F_cur cv scr_init scr2 g_len ht_off ht_sz := by
  intro k hk
  rcases hq1 with hcap | ⟨o, b, i, q, hl⟩
  · rw [hcap_eq hcap]; exact hht k hk
  · have hl' := hl; rcases hl with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hco, hqi, hib, hbh, _⟩
    rw [(hlay2 o b i q hl').2.2.2.2.2.2.2 (ht_off + k) (by omega) (by omega) (by omega)]
    exact hht k hk

theorem step12BEvStOk_of_fold {ctx : Step12BEvCtx} {st s' : FullState} (hok : Step12BEvStOk ctx st)
    (hl' : s'.LengthsOk ctx.cfg) (hw' : FullWitnessInv ctx.cfg ctx.F0 ctx.F_cur s'.core)
    (hmk' : FullLitMarksClear ctx.cfg s') (hnd' : FullArenaVarsNodup s')
    (hext' : FullExtScratchOk ctx.cfg s') (hcl' : s'.core.cur_level = 0)
    (hdm' : s'.core.dense_mode ≠ 0#64) (hcv' : s'.core.cur_vars = st.core.cur_vars)
    (hfl' : s'.core.fuel = st.core.fuel) (har' : s'.core.arena = st.core.arena)
    (hal' : s'.core.arena_len = st.core.arena_len)
    (hscr' : s'.scratch.scratch_buf = st.scratch.scratch_buf)
    (hrepr' : FullCongReprInv ctx.F_cur (2 * s'.core.cur_vars) s'.core.repr) :
    Step12BEvStOk ctx s' :=
  ⟨⟨hl', hw', hmk', hnd', hext', hcl', hdm'⟩, hcv'.trans hok.2.1, hfl'.trans hok.2.2.1,
   har'.trans hok.2.2.2.1, hal'.trans hok.2.2.2.2.1,
   by rw [hcv'.trans hok.2.1] at hrepr'; exact hrepr',
   by rw [hscr']; exact hok.2.2.2.2.2.2.1, by rw [hscr']; exact hok.2.2.2.2.2.2.2.1,
   by unfold Step12BScrFrame; rw [hscr']; exact hok.2.2.2.2.2.2.2.2⟩

theorem step12BEvStOk_wsState {ctx : Step12BEvCtx} {s0 : FullState} (h : Step12BEvStOk ctx s0)
    {r t : List (BitVec 32)} (hr : r.length = 2 * ctx.cfg.max_vars)
    (ht : t.length = ctx.cfg.max_vars) (hrepr : FullCongReprInv ctx.F_cur (2 * ctx.cv0) r) :
    Step12BEvStOk ctx (wsState s0 r t) :=
  ⟨⟨⟨{ h.1.1.core_ok with repr_len := hr, tmp_len_arr := ht }, h.1.1.scratch_ok⟩,
    fullWitnessInv_with_tmp (fullWitnessInv_with_repr h.1.2.1 r) t,
    h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1, h.1.2.2.2.2.2.1, h.1.2.2.2.2.2.2⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, hrepr, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem step12BEvStOk_with_repr {ctx : Step12BEvCtx} {st : FullState} (h : Step12BEvStOk ctx st)
    {r : List (BitVec 32)} (hr : r.length = 2 * ctx.cfg.max_vars)
    (hrepr : FullCongReprInv ctx.F_cur (2 * ctx.cv0) r) :
    Step12BEvStOk ctx { st with core := { st.core with repr := r } } :=
  ⟨⟨⟨{ h.1.1.core_ok with repr_len := hr }, h.1.1.scratch_ok⟩,
    fullWitnessInv_with_repr h.1.2.1 r, h.1.2.2.1, h.1.2.2.2.1,
    h.1.2.2.2.2.1, h.1.2.2.2.2.2.1, h.1.2.2.2.2.2.2⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, hrepr, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

private theorem s12b_wit_with_lm {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (lm' : List (BitVec 8)) :
    FullWitnessInv c F0 F_cur { k with lit_mark := lm' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem step12BEvStOk_with_repr_mclr_lm {ctx : Step12BEvCtx} {st : FullState}
    (h : Step12BEvStOk ctx st) {r mc : List (BitVec 32)} {lm : List (BitVec 8)}
    (hr : r.length = 2 * ctx.cfg.max_vars) (hmc : mc.length = ctx.cfg.max_vars)
    (hlm : lm.length = 2 * ctx.cfg.max_vars)
    (hmk : FullLitMarksClear ctx.cfg
      { st with core := { st.core with repr := r, min_clr := mc, lit_mark := lm } })
    (hrepr : FullCongReprInv ctx.F_cur (2 * ctx.cv0) r) :
    Step12BEvStOk ctx
      { st with core := { st.core with repr := r, min_clr := mc, lit_mark := lm } } :=
  ⟨⟨⟨{ h.1.1.core_ok with repr_len := hr, min_clr_len_arr := hmc, lit_mark_len := hlm },
     h.1.1.scratch_ok⟩,
    s12b_wit_with_lm (fullWitnessInv_with_min_clr (fullWitnessInv_with_repr h.1.2.1 r) mc) lm,
    hmk, h.1.2.2.2.1, h.1.2.2.2.2.1, h.1.2.2.2.2.2.1, h.1.2.2.2.2.2.2⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, hrepr, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem step12BEvStOk_with_inconsistent {ctx : Step12BEvCtx} {st : FullState}
    (h : Step12BEvStOk ctx st) (hu : (cnfOfClauses ctx.F_cur).Unsat) :
    Step12BEvStOk ctx { st with core := { st.core with inconsistent := 1#64 } } :=
  ⟨⟨⟨{ h.1.1.core_ok with }, h.1.1.scratch_ok⟩,
    fullWitnessInv_with_inconsistent h.1.2.1 1#64 (fun _ => hu),
    h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1, h.1.2.2.2.2.2.1, h.1.2.2.2.2.2.2⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem step12BEvStOk_ht_insert {ctx : Step12BEvCtx} {stp : FullState}
    {ht_off ht_sz g slot : BitVec 64} (hok : Step12BEvStOk ctx stp)
    (hho : ctx.ht_off = ht_off.toNat) (hhs : ctx.ht_sz = ht_sz.toNat)
    (hg_lt : g.toNat < ctx.g_len) (hg_le_ht : ctx.g_len ≤ ht_off.toNat)
    (hht_le : ht_off.toNat + ht_sz.toNat ≤ ctx.cfg.scratch_cap)
    (hslot_lt : slot.toNat < ht_sz.toNat)
    (hgat : Step12BGateAt ctx.maxA ctx.F_cur ctx.cv0 ctx.scr0 ctx.g_len g.toNat) :
    let scr_ins := stp.scratch.scratch_buf.set (ht_off.toNat + slot.toNat) (g.setWidth 32)
    Step12BEvStOk ctx { stp with scratch := { stp.scratch with
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
    hho ▸ step12BQueueCtx_set_ht (hho ▸ hok.2.2.2.2.2.2.2.1) _,
    hho ▸ step12BScrFrame_ht_set (hho ▸ hok.2.2.2.2.2.2.2.2) slot.toNat _⟩
  rw [hho]; exact step12BCongHtInv_set_gate (hho ▸ hok.2.2.2.2.2.2.1) (hhs ▸ hslot_lt)
    (by omega) (by rw [htr]; exact hgat)

theorem step12BEv_ret2 {ctx : Step12BEvCtx} {s0 su : FullState} {Q : Post [i64]} {mu : Mem 64}
    (hex : Step12BEvOutCtx ctx s0 Q) (hoku : Step12BEvStOk ctx su)
    (huns : ctx.F0.Unsat) (hmu : (FullMem ctx.cfg su ⋆ ctx.R) mu) : Q (2#64, ()) mu :=
  hex.hQ 2#64 su mu hoku.1 (hoku.2.1.trans hex.hcv0) (hoku.2.2.1.trans hex.hf0)
    (hoku.2.2.2.1.trans hex.ha0) (hoku.2.2.2.2.1.trans hex.hal0)
    (by rw [hoku.2.1]; exact hoku.2.2.2.2.2.1)
    (step12BScrFrame_pref hex.hle hex.hht hex.hpref0 hex.hq0 hoku.2.2.2.2.2.2.2.2)
    (by rw [hoku.2.1]; exact hoku.2.2.2.2.2.2.1)
    hoku.2.2.2.2.2.2.2.1 (fun h => absurd h (by decide)) (fun _ => huns) hmu

theorem step12BEv_exit {ctx : Step12BEvCtx} {s0 su : FullState} {Q : Post [i64]} {mu : Mem 64}
    (hex : Step12BEvOutCtx ctx s0 Q) (hoku : Step12BEvStOk ctx su)
    (hmu : (FullMem ctx.cfg su ⋆ ctx.R) mu) (ch keep : Bool) :
    let rv : BitVec 64 := (if ch then 1#64 else 0#64) ||| (if keep then 4#64 else 0#64)
    Q (rv, ()) mu := by
  intro rv
  have hand0 : (rv &&& 2#64) = 0#64 := by dsimp only [rv]; cases ch <;> cases keep <;> decide
  exact hex.hQ rv su mu hoku.1 (hoku.2.1.trans hex.hcv0) (hoku.2.2.1.trans hex.hf0)
    (hoku.2.2.2.1.trans hex.ha0) (hoku.2.2.2.2.1.trans hex.hal0)
    (by rw [hoku.2.1]; exact hoku.2.2.2.2.2.1)
    (step12BScrFrame_pref hex.hle hex.hht hex.hpref0 hex.hq0 hoku.2.2.2.2.2.2.2.2)
    (by rw [hoku.2.1]; exact hoku.2.2.2.2.2.2.1)
    hoku.2.2.2.2.2.2.2.1 (fun _ idx h1 h2 => hex.hs0 ▸ hoku.2.2.2.2.2.2.2.2.2 idx h1 h2)
    (fun h => absurd hand0 h) hmu

theorem step12BEv_unit {ctx : Step12BEvCtx} {st : FullState} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {lit next_ep : BitVec 32}
    (hok : Step12BEvStOk ctx st) (hl : lit.toNat < 2 * ctx.cv0)
    (hent : (cnfOfClauses ctx.F_cur).EntailsClause (cnfClause [lit.toNat]))
    (hm : (FullMem ctx.cfg st ⋆ ctx.R) m)
    (k : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      Step12BEvStOk ctx s' → s'.core.tmp = st.core.tmp → (r = 2#64 → ctx.F0.Unsat) →
      (FullMem ctx.cfg s' ⋆ ctx.R) m' → Q (r, ()) m') :
    m3CongUnitFoldSpec (ctx.cfg.hdr, lit, next_ep, ()) m Q X :=
  ⟨ctx.cfg, ctx.F0, ctx.F_cur, st, ctx.R, rfl, hok.1.1, hok.1.2.1, hok.1.2.2.1, hok.1.2.2.2.1,
   hok.1.2.2.2.2.1, hok.1.2.2.2.2.2.1, hok.1.2.2.2.2.2.2,
   hok.2.1 ▸ hok.2.2.2.2.2.1, hok.2.1 ▸ hl, hent, hm,
   fun r s' m' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 htmp h12 h13 _ h2u hm' =>
     k r s' m' (step12BEvStOk_of_fold hok h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13)
       htmp (fun h => (h2u h).2) hm'⟩

theorem step12BEv_unit_xor1 {ctx : Step12BEvCtx} {st : FullState} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {lit next_ep : BitVec 32}
    (hok : Step12BEvStOk ctx st) (hl : lit.toNat < 2 * ctx.cv0)
    (hent : (cnfOfClauses ctx.F_cur).EntailsClause (cnfClause [litNeg lit.toNat]))
    (hm : (FullMem ctx.cfg st ⋆ ctx.R) m)
    (k : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      Step12BEvStOk ctx s' → s'.core.tmp = st.core.tmp → (r = 2#64 → ctx.F0.Unsat) →
      (FullMem ctx.cfg s' ⋆ ctx.R) m' → Q (r, ()) m') :
    m3CongUnitFoldSpec (ctx.cfg.hdr, lit ^^^ 1#32, next_ep, ()) m Q X :=
  step12BEv_unit hok (by rw [FullCongHelpers.bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hl)
    (by rw [FullCongHelpers.bv32_xor1_eq_litNeg]; exact hent) hm k

theorem step12BEv_equiv {ctx : Step12BEvCtx} {st : FullState} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {a b next_ep : BitVec 32}
    (hok : Step12BEvStOk ctx st) (ha : a.toNat < 2 * ctx.cv0) (hb : b.toNat < 2 * ctx.cv0)
    (heqv : LitEquiv (cnfOfClauses ctx.F_cur) a.toNat b.toNat)
    (hm : (FullMem ctx.cfg st ⋆ ctx.R) m)
    (k : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      Step12BEvStOk ctx s' → s'.core.tmp = st.core.tmp → (r = 2#64 → ctx.F0.Unsat) →
      (FullMem ctx.cfg s' ⋆ ctx.R) m' → Q (r, ()) m') :
    m3CongEquivFoldSpec (ctx.cfg.hdr, a, b, next_ep, ()) m Q X :=
  ⟨ctx.cfg, ctx.F0, ctx.F_cur, st, ctx.R, rfl, hok.1.1, hok.1.2.1, hok.1.2.2.1, hok.1.2.2.2.1,
   hok.1.2.2.2.2.1, hok.1.2.2.2.2.2.1, hok.1.2.2.2.2.2.2,
   hok.2.1 ▸ hok.2.2.2.2.2.1, hok.2.1 ▸ ha, hok.2.1 ▸ hb, heqv, hm,
   fun r s' m' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 htmp h12 h13 _ h2u hm' =>
     k r s' m' (step12BEvStOk_of_fold hok h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13)
       htmp h2u hm'⟩

theorem step12BEv_enq_core {ctx : Step12BEvCtx} {s0 st : FullState} {Qo : Post [i64]}
    {m : Mem 64} {Q : Post []} {X : XPost} {ctrl_off : BitVec 64} {v : BitVec 32}
    (_hex : Step12BEvOutCtx ctx s0 Qo) (hok : Step12BEvStOk ctx st)
    (hco : ctrl_off.toNat = ctx.ctrl_off) (hm : (FullMem ctx.cfg st ⋆ ctx.R) m)
    (k : ∀ s' m', Step12BEvStOk ctx s' → s'.core = st.core →
      (FullMem ctx.cfg s' ⋆ ctx.R) m' → Q () m') :
    step12BCongEnqVarSpec (ctx.cfg.hdr, ctrl_off, v, ()) m Q X := by
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
     step12BCongHtInv_enq hok.2.2.2.2.2.2.1 hok.2.2.2.2.2.2.2.1 hcap_eq hlay',
     hq', step12BScrFrame_enq hok.2.2.2.2.2.2.2.2 hok.2.2.2.2.2.2.2.1 hscrl' hcap_eq hlay'⟩ rfl hm'

theorem step12BEv_enq {ctx : Step12BEvCtx} {s0 st : FullState} {Qo : Post [i64]}
    {m : Mem 64} {Q : Post []} {X : XPost} {ctrl_off : BitVec 64} {v : BitVec 32}
    (hex : Step12BEvOutCtx ctx s0 Qo) (hok : Step12BEvStOk ctx st)
    (hco : ctrl_off.toNat = ctx.ctrl_off) (hm : (FullMem ctx.cfg st ⋆ ctx.R) m)
    (k : ∀ s' m', Step12BEvStOk ctx s' → s'.core.tmp = st.core.tmp →
      (FullMem ctx.cfg s' ⋆ ctx.R) m' → Q () m') :
    step12BCongEnqVarSpec (ctx.cfg.hdr, ctrl_off, v, ()) m Q X :=
  step12BEv_enq_core hex hok hco hm fun s' m' h1 hc hm' =>
    k s' m' h1 (congrArg FullCoreState.tmp hc) hm'

theorem step12BEvOut_nohash {ctx : Step12BEvCtx} {lhs' htag' harity : BitVec 32} {mj : Mem 64}
    (stj : FullState) (hokj : Step12BEvStOk ctx stj) (hm : (FullMem ctx.cfg stj ⋆ ctx.R) mj) :
    Step12BEvOut ctx lhs' htag' harity false mj :=
  ⟨stj, hokj, (fun h => by cases h), (fun h => by cases h), hm⟩

theorem step12B_tag1_match_equiv {F_cur : List (List Nat)} {cv0 : Nat}
    {lhs ml : BitVec 32} {tmps : List (BitVec 32)} {harity : BitVec 32}
    (hgate : Step12BHashGateOk F_cur cv0 lhs tmps 1#32 harity)
    (hm : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      evalLitVal α ml.toNat = xorEvalList α ((tmps.take harity.toNat).map BitVec.toNat)) :
    LitEquiv (cnfOfClauses F_cur) lhs.toNat ml.toNat := by
  refine litEquiv_of_eval_eq fun α hα => ?_
  have hxor := (hgate.2.2.1 rfl).2.2.2 α hα
  rw [hxor, hm α hα]

theorem step12B_pair_xor_hash_ok {F_cur : List (List Nat)} {cv0 : Nat}
    {lhs r0 r1 : BitVec 32} {tmpi : List (BitVec 32)}
    (ht2 : 2 ≤ tmpi.length) (h2cv : 2 ≤ cv0) (hr0 : r0.toNat < 2 * cv0) (hr1 : r1.toNat < 2 * cv0)
    (hxor : XorListGateDef (cnfOfClauses F_cur) lhs.toNat [r0.toNat, r1.toNat]) :
    let v0 := if r0.ult r1 then r0 else r1
    let v1 := if r0.ult r1 then r1 else r0
    Step12BHashGateOk F_cur cv0 lhs ((tmpi.set 0 v0).set 1 v1) 1#32 2#32 := by
  have h := fid_pair_xor_hash_ok ht2 h2cv hr0 hr1 hxor
  exact ⟨h.1, fun h0 => absurd h0 (by decide), h.2.2.1, h.2.2.2⟩

theorem step12B_pair_and_hash_ok {F_cur : List (List Nat)} {cv0 : Nat}
    {lhs a0 a1 : BitVec 32} {tmpi : List (BitVec 32)}
    (ht2 : 2 ≤ tmpi.length) (h2cv : 2 ≤ cv0) (h : And2Sem F_cur lhs a0 a1) :
    let v0 := if a0.ult a1 then a0 else a1
    let v1 := if a0.ult a1 then a1 else a0
    Step12BHashGateOk F_cur cv0 lhs ((tmpi.set 0 v0).set 1 v1) 0#32 2#32 := by
  have hf := fid_pair_and_hash_ok ht2 h2cv h
  exact ⟨hf.1, fun _ => ⟨by decide, by unfold step12BCongAndArityMax; decide, (hf.2.1 rfl).2.2⟩,
    hf.2.2.1, hf.2.2.2⟩

theorem step12B_gtype_eq0 {mword gtype : BitVec 32}
    (hg : gtype = if (mword >>> 28) == 3#32 then 0#32 else mword >>> 28) (h0 : gtype = 0#32) :
    (mword >>> 28) = 0#32 ∨ (mword >>> 28) = 3#32 := by
  by_cases h3 : (mword >>> 28) = 3#32
  · exact Or.inr h3
  · have hb : ((mword >>> 28) == 3#32) = false := beq_false_of_ne h3
    rw [hb] at hg; exact Or.inl (hg.symm.trans h0)

theorem step12B_gtype_eq1 {mword gtype : BitVec 32}
    (hg : gtype = if (mword >>> 28) == 3#32 then 0#32 else mword >>> 28) (h1 : gtype = 1#32) :
    (mword >>> 28) = 1#32 := by
  by_cases h3 : (mword >>> 28) = 3#32
  · have hb : ((mword >>> 28) == 3#32) = true := beq_iff_eq.mpr h3
    simp only [hb, ↓reduceIte] at hg; exact absurd (hg.symm.trans h1) (by decide)
  · have hb : ((mword >>> 28) == 3#32) = false := beq_false_of_ne h3
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at hg; exact hg.symm.trans h1

theorem step12B_gtype_eq2 {mword gtype : BitVec 32}
    (hg : gtype = if (mword >>> 28) == 3#32 then 0#32 else mword >>> 28) (h2 : gtype = 2#32) :
    (mword >>> 28) = 2#32 := by
  by_cases h3 : (mword >>> 28) = 3#32
  · have hb : ((mword >>> 28) == 3#32) = true := beq_iff_eq.mpr h3
    simp only [hb, ↓reduceIte] at hg; exact absurd (hg.symm.trans h2) (by decide)
  · have hb : ((mword >>> 28) == 3#32) = false := beq_false_of_ne h3
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at hg; exact hg.symm.trans h2

theorem step12B_gate_tag0_and {F_cur : List (List Nat)} {lhs0 mword : BitVec 32}
    {scr0 : List (BitVec 32)} {g_n : Nat}
    (ht03 : (mword >>> 28) = 0#32 ∨ (mword >>> 28) = 3#32)
    (hsem : ((((mword >>> 28).toNat = 0 ∧ 2 ≤ step12BGateArity mword ∧
                step12BGateArity mword ≤ 64) ∨
              ((mword >>> 28).toNat = 3 ∧ 65 ≤ step12BGateArity mword)) ∧
              AndGateDef (cnfOfClauses F_cur) lhs0.toNat
                (((scr0.drop (g_n + 2)).take (step12BGateArity mword)).map BitVec.toNat)) ∨
            ((mword >>> 28).toNat = 1 ∧ 2 ≤ step12BGateArity mword ∧
              step12BGateArity mword ≤ 4 ∧
              XorListGateDef (cnfOfClauses F_cur) lhs0.toNat
                (((scr0.drop (g_n + 2)).take (step12BGateArity mword)).map BitVec.toNat)) ∨
            ((mword >>> 28).toNat = 2 ∧ step12BGateArity mword = 3 ∧
              IteGateDef (cnfOfClauses F_cur) lhs0.toNat
                (scr0[g_n + 2]?.getD 0#32).toNat (scr0[g_n + 3]?.getD 0#32).toNat
                (scr0[g_n + 4]?.getD 0#32).toNat)) :
    2 ≤ step12BGateArity mword ∧
    AndGateDef (cnfOfClauses F_cur) lhs0.toNat
      (((scr0.drop (g_n + 2)).take (step12BGateArity mword)).map BitVec.toNat) := by
  have htn : (mword >>> 28).toNat = 0 ∨ (mword >>> 28).toNat = 3 :=
    ht03.elim (fun h => Or.inl (by rw [h]; rfl)) (fun h => Or.inr (by rw [h]; rfl))
  rcases hsem with ⟨hdisj, hand⟩ | ⟨ht1, _⟩ | ⟨ht2, _⟩
  · rcases hdisj with ⟨_, h2, _⟩ | ⟨_, h65⟩
    · exact ⟨h2, hand⟩
    · exact ⟨by omega, hand⟩
  · omega
  · omega

theorem step12B_gate_tag1_xor {F_cur : List (List Nat)} {lhs0 mword : BitVec 32}
    {scr0 : List (BitVec 32)} {g_n : Nat}
    (ht1 : (mword >>> 28) = 1#32)
    (hsem : ((((mword >>> 28).toNat = 0 ∧ 2 ≤ step12BGateArity mword ∧
                step12BGateArity mword ≤ 64) ∨
              ((mword >>> 28).toNat = 3 ∧ 65 ≤ step12BGateArity mword)) ∧
              AndGateDef (cnfOfClauses F_cur) lhs0.toNat
                (((scr0.drop (g_n + 2)).take (step12BGateArity mword)).map BitVec.toNat)) ∨
            ((mword >>> 28).toNat = 1 ∧ 2 ≤ step12BGateArity mword ∧
              step12BGateArity mword ≤ 4 ∧
              XorListGateDef (cnfOfClauses F_cur) lhs0.toNat
                (((scr0.drop (g_n + 2)).take (step12BGateArity mword)).map BitVec.toNat)) ∨
            ((mword >>> 28).toNat = 2 ∧ step12BGateArity mword = 3 ∧
              IteGateDef (cnfOfClauses F_cur) lhs0.toNat
                (scr0[g_n + 2]?.getD 0#32).toNat (scr0[g_n + 3]?.getD 0#32).toNat
                (scr0[g_n + 4]?.getD 0#32).toNat)) :
    2 ≤ step12BGateArity mword ∧ step12BGateArity mword ≤ 4 ∧
    XorListGateDef (cnfOfClauses F_cur) lhs0.toNat
      (((scr0.drop (g_n + 2)).take (step12BGateArity mword)).map BitVec.toNat) := by
  have htn : (mword >>> 28).toNat = 1 := by rw [ht1]; rfl
  rcases hsem with ⟨⟨ht0, _⟩ | ⟨ht3, _⟩, _⟩ | ⟨_, h2, h4, hxor⟩ | ⟨ht2, _⟩
  · omega
  · omega
  · exact ⟨h2, h4, hxor⟩
  · omega

theorem step12B_gate_tag2_ite {F_cur : List (List Nat)} {lhs0 mword : BitVec 32}
    {scr0 : List (BitVec 32)} {g_n : Nat}
    (ht2 : (mword >>> 28) = 2#32)
    (hsem : ((((mword >>> 28).toNat = 0 ∧ 2 ≤ step12BGateArity mword ∧
                step12BGateArity mword ≤ 64) ∨
              ((mword >>> 28).toNat = 3 ∧ 65 ≤ step12BGateArity mword)) ∧
              AndGateDef (cnfOfClauses F_cur) lhs0.toNat
                (((scr0.drop (g_n + 2)).take (step12BGateArity mword)).map BitVec.toNat)) ∨
            ((mword >>> 28).toNat = 1 ∧ 2 ≤ step12BGateArity mword ∧
              step12BGateArity mword ≤ 4 ∧
              XorListGateDef (cnfOfClauses F_cur) lhs0.toNat
                (((scr0.drop (g_n + 2)).take (step12BGateArity mword)).map BitVec.toNat)) ∨
            ((mword >>> 28).toNat = 2 ∧ step12BGateArity mword = 3 ∧
              IteGateDef (cnfOfClauses F_cur) lhs0.toNat
                (scr0[g_n + 2]?.getD 0#32).toNat (scr0[g_n + 3]?.getD 0#32).toNat
                (scr0[g_n + 4]?.getD 0#32).toNat)) :
    step12BGateArity mword = 3 ∧
    IteGateDef (cnfOfClauses F_cur) lhs0.toNat
      (scr0[g_n + 2]?.getD 0#32).toNat (scr0[g_n + 3]?.getD 0#32).toNat
      (scr0[g_n + 4]?.getD 0#32).toNat := by
  have htn : (mword >>> 28).toNat = 2 := by rw [ht2]; rfl
  rcases hsem with ⟨⟨ht0, _⟩ | ⟨ht3, _⟩, _⟩ | ⟨ht1, _⟩ | ⟨_, h3, hite⟩
  · omega
  · omega
  · omega
  · exact ⟨h3, hite⟩

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep12B
