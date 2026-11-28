/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Probe.Spec
public import LeanQbe.T.Examples.Kissat.Src.Probe
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Canonical WP Proofs for `Kissat.Src.Probe` Part 0 (`Wp0`)

Proves `full_probe_dticks_m6_hdr_wp` and shared `full_probe_m6` building blocks
(`ProbeEnv`, `ProbeQ`, `ProbeStateInv`, `probe_ret_wm`, `probe_subst_if`,
`probe_bone_if`, `probe_reb20`, `probe_bin_rt`, `probe_var_cnt_*`, and
`probe_factor_block`) with zero legacy imports.
-/

set_option autoImplicit false

local elab "c0_hfast_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

local macro "c0_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Probe

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Probe
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Probe.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.M6HdrTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.M6ProofUtilTactics

/-! ## 1. `full_probe_dticks_m6_hdr_wp` -/

theorem full_probe_dticks_m6_hdr_wp (Γ : Env)
    (hGetWm : Γ.Has "m6_hdr_get_watermark" (m6HdrW2aSpec [i64] [i64])) :
    ∀ a m Q X, fullProbeDticksM6HdrSpec a m Q X →
      Func.wp Γ full_probe_dticks_m6_hdr_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  rw [fullM6HdrMem_iff] at hm
  unfold Func.wp full_probe_dticks_m6_hdr_body
  c0_hsteps_nogrp
  · exact hQ (_, ()) ext s _ rfl hlen (M6HdrScratchPres.refl s) hext
      (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) ((fullM6HdrMem_iff ..).mpr hm)
  · m6h_call hGetWm
    refine m6HdrW2aSpec_of rfl hcfg hext hlen ((fullM6HdrMem_iff ..).mpr hm)
      fun ⟨last_p, ⟨⟩⟩ ext1 s1 m1 hcore1 hlen1 hsc1 hext1 hpres1 hm1 => ?_
    rw [fullM6HdrMem_iff] at hm1
    c0_hsteps
    all_goals
      refine hQ (_, ()) ext1 s1 _ hcore1 hlen1 hsc1 hext1 hpres1
        ((fullM6HdrMem_iff ..).mpr hm1)

/-! ## 2. Probing Environment, Postcondition, Invariants, and Tail Return -/

structure ProbeEnv (Γ : Env) : Prop where
  probeDt : ∀ a m Q X, fullProbeDticksM6HdrSpec a m Q X →
    Γ "full_probe_dticks_m6_hdr" [i64, .bool] [i64] a m Q X
  delay : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
    Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X
  redD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
    Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X
  bumpD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
    Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X
  getWm : ∀ a m Q X, m6HdrW2aSpec [i64] [i64] a m Q X →
    Γ "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X
  setWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
    Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X
  updCls : ∀ a m Q X, Internal.Spec.fullUpdateClassifyFidSpec a m Q X →
    Γ "full_update_classify_fid" [i64] [] a m Q X
  enter : ∀ a m Q X, Dense.Spec.fullEnterDenseM6Spec a m Q X →
    Γ "full_enter_dense" [i64] [.bool] a m Q X
  enterEx : ∀ a m Q X, Dense.Spec.fullEnterDenseExM6Spec a m Q X →
    Γ "full_enter_dense_ex_fid" [i64, .bool] [.bool] a m Q X
  cong : ∀ a m Q X, Congruence.Spec.fullCongruenceDenseSpec a m Q X →
    Γ "full_congruence_dense" [i64, i64] [i64] a m Q X
  binRt : ∀ a m Q X, Forward.Spec.fullDenseBinRoundtripFidSpec a m Q X →
    Γ "full_dense_bin_roundtrip_fid" [i64] [] a m Q X
  rebNosort : ∀ a m Q X, Dense.Spec.fullRebuildWatchesM6Spec a m Q X →
    Γ "full_rebuild_watches_nosort_fid" [i64] [i64] a m Q X
  subst : ∀ a m Q X, Substitute.Spec.fullSubstituteM6Spec a m Q X →
    Γ "full_substitute" [i64] [i64] a m Q X
  bone : ∀ a m Q X, Backbone.Spec.fullBackboneM6Spec a m Q X →
    Γ "full_backbone_m6" [i64, i64] [i64] a m Q X
  sweepD : ∀ a m Q X, Sweep.Spec.fullSweepDenseM6Spec a m Q X →
    Γ "full_sweep_dense_m6" [i64, i64, i64] [i64] a m Q X
  hasFact : ∀ a m Q X, Factor.Spec.step13HasFactorCandsSpec a m Q X →
    Γ "full_has_factor_cands_fid" [i64] [.bool] a m Q X
  factor : ∀ a m Q X, Factor.Spec.fullFactorHeapSpec a m Q X →
    Γ "full_factor" [i64, i64] [i64] a m Q X
  viv : ∀ a m Q X, Vivify.Spec.vivifyM6HdrSpec a m Q X →
    Γ "full_vivify_m6_hdr" [i64] [i64] a m Q X
  trans : ∀ a m Q X, Transitive.Spec.fullTransitiveM6Spec a m Q X →
    Γ "full_transitive_m6" [i64, i64] [i64] a m Q X
  nlogpown : ∀ a m Q X, Float64.Spec.f64uPure2Spec a m Q X →
    Γ "f64u_nlogpown" [i64, i64] [i64] a m Q X
  mul : ∀ a m Q X, Float64.Spec.f64uPure2Spec a m Q X →
    Γ "f64u_mul" [i64, i64] [i64] a m Q X
  toU64 : ∀ a m Q X, Float64.Spec.f64uPure1Spec a m Q X →
    Γ "f64u_to_u64" [i64] [i64] a m Q X
  scaleM5 : ∀ a m Q X, Limits.Spec.schedScaleDeltaSpec a m Q X →
    Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X

abbrev ProbeQ (c : FullCfg) (F0 : CNF Nat) (s : FullState)
    (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ r ext' s' m',
    s'.LengthsOk c → M6HdrExtOk ext' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
    (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
    (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
    (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

abbrev ProbeStateInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop)
    (ext1 : List (BitVec 64)) (s1 : FullState) (m1 : Mem 64) : Prop :=
  FullM6HdrInv c F0 ext1 s1 ∧ s1.core.cur_level = 0 ∧
  s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c ext1 s1 ⋆ R) m1

theorem probeM6HdrInv_with_probing {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s : FullState} (h : FullM6HdrInv c F0 ext s) (p' : BitVec 64) :
    FullM6HdrInv c F0 ext { s with core := { s.core with probing := p' } } := by
  obtain ⟨F_cur, hw⟩ := h.sparse.1.witness
  have hw' : FullWitnessInv c F0 F_cur { s.core with probing := p' } :=
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
  exact FullM6HdrInv.mk_inv h.cfgOk h.extOk
    ⟨⟨⟨{ h.sparse.1.lengths.core_ok with vals_len := h.sparse.1.lengths.core_ok.vals_len },
        h.sparse.1.lengths.scratch_ok⟩, F_cur, hw'⟩,
      h.sparse.2.1, h.sparse.2.2.1, h.sparse.2.2.2.1, h.sparse.2.2.2.2⟩

theorem probeDense_zero_gu32 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) :
    FullDenseInv c F0
      { s with scratch := { s.scratch with glue_used := s.scratch.glue_used.set 32 0#32 } } :=
  let sc_ok := h.lengths.scratch_ok
  h.of_safetySlice
    ⟨h.lengths.core_ok, { sc_ok with glue_used_len := (by simp [sc_ok.glue_used_len]) }⟩
    rfl ⟨rfl, rfl⟩

abbrev probeRetWmExpr (c : FullCfg) (saved_prob : Val i64) (r : BitVec 64) :
    Expr Val Cont [i64] :=
  Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 520, ())) fun p =>
  Expr.store (t := i64) (Arg.var saved_prob) (Arg.var p.fst)
    (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 600, ())) fun p_1 =>
    Expr.load i64 (Arg.var p_1.fst) fun ld =>
    Expr.call (as := [i64, i64, i64]) (bs := []) "m6_hdr_set_watermark"
      (Arg.var c.hdr, Arg.imm 0, Arg.var ld, ()) fun _ => Expr.ret (Arg.imm r, ()))

theorem probe_ret_wm {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s s0 : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {saved_prob : Val i64} {r : BitVec 64} {Q : Post [i64]} {X : XPost}
    (henv : ProbeEnv Γ) (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext)
    (hlen : s0.LengthsOk c) (hfu : s0.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hr : r = 1#64 ∨ r = 20#64) (hu : r = 20#64 → F0.Unsat)
    (h1 : r = 1#64 → FullM6HdrInv c F0 ext s0 ∧ s0.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s0 ⋆ R) m) (hQ : ProbeQ c F0 s R Q) :
    wp Γ Q X (probeRetWmExpr c saved_prob r) m := by
  dsimp only [probeRetWmExpr]
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  c0_hfast_nogrp
  let s1 : FullState := { s0 with core := { s0.core with probing := saved_prob } }
  have hlen1 : s1.LengthsOk c :=
    ⟨{ hlen.core_ok with vals_len := hlen.core_ok.vals_len }, hlen.scratch_ok⟩
  have hm1 : (FullM6HdrMem c ext s1 ⋆ R) _ := fullM6HdrMem_unfocus (by assumption)
  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.setWm _ _ _ _ h) hcfg hext hlen1 hm1
    fun _ ext' s' m' hc' hlen' hms' hext' _ hm' => ?_
  c0_hfast_nogrp
  refine hQ r ext' s' m' hlen' hext' (by rw [hc']; exact hfu) hr hu (fun h => ?_) hm'
  obtain ⟨hi, hcl⟩ := h1 h
  exact ⟨fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres (probeM6HdrInv_with_probing hi saved_prob)
    hlen' hc' hms') hext', by rw [hc']; exact hcl⟩

/-! ## 3. Shared Sparse/Dense Call Blocks (`substitute`, `backbone`, `reb`, `bin_rt`) -/

theorem probe_subst_if {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {ext1 : List (BitVec 64)}
    {s s1 : FullState} {R : Mem 64 → Prop} {m1 : Mem 64} {saved_prob : Val i64}
    {Q : Post [i64]} {X : XPost} {k : Expr Val Cont [i64]}
    (henv : ProbeEnv Γ) (hinv1 : ProbeStateInv c F0 s R ext1 s1 m1)
    (hQ : ProbeQ c F0 s R Q)
    (hk : ∀ ext' s' m', ProbeStateInv c F0 s R ext' s' m' → wp Γ Q X k m') :
    wp Γ Q X (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 504, ())) fun p =>
      Expr.load i64 (Arg.var p.fst) fun ld =>
      Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p_1 =>
      Expr.jnz (Arg.var p_1.fst)
        (Expr.call (as := [i64]) (bs := [i64]) "full_substitute" (Arg.var c.hdr, ()) fun p_2 =>
          Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_2.fst, Arg.imm 20, ()))
            fun p_3 =>
          Expr.jnz (Arg.var p_3.fst) (probeRetWmExpr c saved_prob 20#64) k) k) m1 := by
  obtain ⟨hinv, hcl, hfu, hm⟩ := hinv1
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  c0_hfast_nogrp
  · c0_call henv.subst
    refine ⟨c, F0, ext1, s1, R, rfl, hinv, fullM6HdrMem_unfocus hmf,
      fun rSu extSu sSu mSu hinvSu hclSu hfuSu _ huSu hmSu => ?_⟩
    have hfuSu' := Nat.le_trans hfuSu hfu
    c0_hfast_nogrp
    · exact probe_ret_wm henv hinvSu.cfgOk hinvSu.extOk hinvSu.sparse.lengths hfuSu'
        (Or.inr rfl) (fun _ => huSu ‹_›) (fun h => by cases h) hmSu hQ
    · exact hk extSu sSu mSu ⟨hinvSu, hclSu, hfuSu', hmSu⟩
  · exact hk ext1 s1 m1 ⟨hinv, hcl, hfu, fullM6HdrMem_unfocus hmf⟩

theorem probe_bone_if {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {ext1 : List (BitVec 64)}
    {s s1 : FullState} {R : Mem 64 → Prop} {m1 : Mem 64} {saved_prob dticks : Val i64}
    {Q : Post [i64]} {X : XPost} {k : Expr Val Cont [i64]}
    (henv : ProbeEnv Γ) (hinv1 : ProbeStateInv c F0 s R ext1 s1 m1)
    (hQ : ProbeQ c F0 s R Q)
    (hk : ∀ ext' s' m', ProbeStateInv c F0 s R ext' s' m' → wp Γ Q X k m') :
    wp Γ Q X (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 504, ())) fun p =>
      Expr.load i64 (Arg.var p.fst) fun ld =>
      Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p_1 =>
      Expr.jnz (Arg.var p_1.fst)
        (Expr.let_ (Op.mk (.udiv 64) (Arg.var dticks, Arg.imm 50, ())) fun p_2 =>
          Expr.call (as := [i64, i64]) (bs := [i64]) "full_backbone_m6"
              (Arg.var c.hdr, Arg.var p_2.fst, ()) fun p_3 =>
            Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_3.fst, Arg.imm 20, ()))
              fun p_4 =>
            Expr.jnz (Arg.var p_4.fst) (probeRetWmExpr c saved_prob 20#64) k) k) m1 := by
  obtain ⟨hinv, hcl, hfu, hm⟩ := hinv1
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  c0_hfast_nogrp
  · c0_call henv.bone
    refine ⟨c, F0, ext1, s1, R, rfl, hinv.cfgOk, hinv.extOk, hinv.sparse,
      fullM6HdrMem_unfocus hmf,
      fun rB extB sB mB hextB hspB _ _ hclprB hfuB _ huB hmB => ?_⟩
    have hinvB := FullM6HdrInv.mk_inv hinv.cfgOk hextB.1 hspB
    have hfuB' := Nat.le_trans hfuB hfu
    c0_hfast_nogrp
    · exact probe_ret_wm henv hinvB.cfgOk hextB.1 hinvB.sparse.lengths hfuB'
        (Or.inr rfl) (fun _ => huB ‹_›) (fun h => by cases h) hmB hQ
    · exact hk extB sB mB ⟨hinvB, hclprB.1, hfuB', hmB⟩
  · exact hk ext1 s1 m1 ⟨hinv, hcl, hfu, fullM6HdrMem_unfocus hmf⟩

theorem probe_reb20 {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {extD : List (BitVec 64)}
    {s sD : FullState} {R : Mem 64 → Prop} {mD : Mem 64} {saved_prob : Val i64}
    {Q : Post [i64]} {X : XPost} {k_ok : Expr Val Cont [i64]}
    (henv : ProbeEnv Γ) (hcfg : FullM6HdrCfgOk c) (hextD : M6HdrExtOk extD)
    (hdenD : FullDenseInv c F0 sD) (hfuD : sD.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hmD : (FullM6HdrMem c extD sD ⋆ R) mD) (hQ : ProbeQ c F0 s R Q)
    (hk : ∀ extR sR mR, ProbeStateInv c F0 s R extR sR mR → wp Γ Q X k_ok mR) :
    wp Γ Q X (Expr.call (as := [i64]) (bs := [i64]) "full_rebuild_watches_nosort_fid"
        (Arg.var c.hdr, ()) fun p =>
      Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p.fst, Arg.imm 20, ())) fun p_1 =>
      Expr.jnz (Arg.var p_1.fst) (probeRetWmExpr c saved_prob 20#64) k_ok) mD := by
  c0_call henv.rebNosort
  refine ⟨c, F0, extD, sD, R, rfl, hcfg, hextD, hdenD, hmD,
    fun rR extR sR mR hinvR hclR hfuR _ huR hmR => ?_⟩
  have hfuR' := Nat.le_trans hfuR hfuD
  c0_hfast_nogrp
  · exact probe_ret_wm henv hinvR.cfgOk hinvR.extOk hinvR.sparse.lengths hfuR'
      (Or.inr rfl) (fun _ => huR ‹_›) (fun h => by cases h) hmR hQ
  · exact hk extR sR mR ⟨hinvR, hclR, hfuR', hmR⟩

theorem probe_bin_rt {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {extD : List (BitVec 64)}
    {sD : FullState} {R : Mem 64 → Prop} {mD : Mem 64} {Q : Post [i64]} {X : XPost}
    {k : Expr Val Cont [i64]}
    (henv : ProbeEnv Γ) (hdenD : FullDenseInv c F0 sD)
    (hmD : (FullM6HdrMem c extD sD ⋆ R) mD)
    (hk : ∀ sRt mRt, FullDenseInv c F0 sRt → sRt.core.fuel = sD.core.fuel →
      (FullM6HdrMem c extD sRt ⋆ R) mRt → wp Γ Q X k mRt) :
    wp Γ Q X (Expr.call (as := [i64]) (bs := []) "full_dense_bin_roundtrip_fid"
      (Arg.var c.hdr, ()) fun _ => k) mD := by
  obtain ⟨F_cur, hwD⟩ := hdenD.1.witness
  refine wp_m6Hdr_focus_frame hmD fun hmf => ?_
  c0_call henv.binRt
  refine ⟨c, F0, F_cur, sD, m6ExtMem (m6ExtAddr c.hdr) extD ⋆ R, rfl,
    hdenD.lengths, hwD, hdenD.2.1, hdenD.2.2.1, hdenD.2.2.2.1, hmf,
    fun sRt mRt hlenRt hwRt hlmRt hndRt hesRt _ hclRt hdmRt _ _ _ _ _ hfuRt
      _ _ _ _ _ _ _ _ _ _ _ _ _ hmRt => ?_⟩
  exact hk sRt mRt
    ⟨⟨hlenRt, F_cur, hwRt⟩, hlmRt, hndRt, hesRt,
      hclRt.trans hdenD.2.2.2.2.1, hdmRt ▸ hdenD.2.2.2.2.2⟩
    hfuRt (fullM6HdrMem_unfocus hmRt)

/-! ## 4. Shared Active-Variable Count Loop & Factor Block -/

theorem probe_var_cnt_loop {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {ext1 : List (BitVec 64)}
    {s1 : FullState} {R : Mem 64 → Prop} {m1 : Mem 64} {flags_ptr : Val i64}
    {Q : Post [i64]} {X : XPost} {k_done : Tup Val [i64, i64] → Expr Val Cont [i64]}
    (hfptr : flags_ptr = c.pFlags) (hinv1 : FullM6HdrInv c F0 ext1 s1)
    (hm1 : (FullM6HdrMem c ext1 s1 ⋆ R) m1)
    (hk : ∀ p, wp Γ Q X (k_done p) m1) :
    wp Γ Q X (Expr.group (sig := [[i64, i64]]) (fun JL => Blocks.cons (fun p =>
      Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 776, ())) fun p_1 =>
      Expr.load i64 (Arg.var p_1.fst) fun ld_1 =>
      Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.var p.snd.fst, Arg.var ld_1, ()))
        fun p_2 =>
      Expr.jnz (Arg.var p_2.fst)
        (Expr.group (sig := [[i64]]) (fun _Js => Blocks.cons (fun p_3 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var p.snd.fst, Arg.imm 1, ())) fun p_4 =>
          Expr.jump JL.fst (Arg.var p_3.fst, Arg.var p_4.fst, ())) Blocks.nil)
        fun Js =>
          Expr.let_ (Op.mk (.mul i64) (Arg.var p.snd.fst, Arg.imm 4, ())) fun p_3 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var flags_ptr, Arg.var p_3.fst, ())) fun p_4 =>
          Expr.load i32 (Arg.var p_4.fst) fun ld_2 =>
          Expr.let_ (Op.mk (.and i32) (Arg.var ld_2, Arg.imm 1, ())) fun p_5 =>
          Expr.let_ (Op.mk (.cmp .ne i32 Ty.bool rfl) (Arg.var p_5.fst, Arg.imm 0, ())) fun p_6 =>
          Expr.jnz (Arg.var p_6.fst)
            (Expr.let_ (Op.mk (.add i64) (Arg.var p.fst, Arg.imm 1, ())) fun p_7 =>
            Expr.jump Js.fst (Arg.var p_7.fst, ()))
            (Expr.jump Js.fst (Arg.var p.fst, ())))
        (k_done p)) Blocks.nil)
      (fun Js => Expr.jump Js.fst (Arg.imm 0, Arg.imm 0, ()))) m1 := by
  subst hfptr
  have hcl := hinv1.sparse.lengths.core_ok
  have hcv_le := hcl.cur_vars_le
  have hfl_len := hcl.flags_len
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  refine wp_loop_inv (fun (_cnt, ai, ()) mL => mL = m1 ∧ ai.toNat ≤ s1.core.cur_vars)
    (fun (_cnt, ai, ()) _ => s1.core.cur_vars - ai.toNat)
    (fun JL hJL => by c0_hfast_nogrp; exact hJL (0#64, 0#64, ()) m1 ⟨rfl, Nat.zero_le _⟩)
    (fun JL (cnt, ai, ()) mL ⟨hmL, hai_le⟩ ihL => by
      subst mL
      refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
      c0_hfast_nogrp
      · have hai_lt : ai.toNat < s1.core.cur_vars := by
          have hlt := BitVec.lt_def.mp ‹ai < BitVec.ofNat 64 s1.core.cur_vars›
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hlt; exact hlt
        have hai1 : (ai + 1#64).toNat = ai.toNat + 1 := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        refine wp_join_group (ts := [i64]) (fun _ mc => mc = m1)
          (fun _ ⟨cnt', ⟨⟩⟩ mc hmc => by
            subst mc; c0_hfast_nogrp
            exact ihL (cnt', ai + 1#64, ()) m1 (by dsimp only; omega) ⟨rfl, by omega⟩)
          (fun Js hJs => by
            c0_hfast_nogrp <;> exact hJs (_, ()) m1 rfl)
      · exact hk (cnt, ai, ()))

theorem probe_var_cnt_ai_loop {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {ext1 : List (BitVec 64)}
    {s1 : FullState} {R : Mem 64 → Prop} {m1 : Mem 64} {flags_ptr : Val i64}
    {Q : Post [i64]} {X : XPost} {k_done : Tup Val [i64, i64] → Expr Val Cont [i64]}
    (hfptr : flags_ptr = c.pFlags) (hinv1 : FullM6HdrInv c F0 ext1 s1)
    (hm1 : (FullM6HdrMem c ext1 s1 ⋆ R) m1)
    (hk : ∀ p, wp Γ Q X (k_done p) m1) :
    wp Γ Q X (Expr.group (sig := [[i64, i64]]) (fun JL => Blocks.cons (fun p =>
      Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 776, ())) fun p_1 =>
      Expr.load i64 (Arg.var p_1.fst) fun ld_1 =>
      Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.var p.fst, Arg.var ld_1, ()))
        fun p_2 =>
      Expr.jnz (Arg.var p_2.fst)
        (Expr.group (sig := [[i64]]) (fun _Js => Blocks.cons (fun p_3 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var p.fst, Arg.imm 1, ())) fun p_4 =>
          Expr.jump JL.fst (Arg.var p_4.fst, Arg.var p_3.fst, ())) Blocks.nil)
        fun Js =>
          Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p_3 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var flags_ptr, Arg.var p_3.fst, ())) fun p_4 =>
          Expr.load i32 (Arg.var p_4.fst) fun ld_2 =>
          Expr.let_ (Op.mk (.and i32) (Arg.var ld_2, Arg.imm 1, ())) fun p_5 =>
          Expr.let_ (Op.mk (.cmp .ne i32 Ty.bool rfl) (Arg.var p_5.fst, Arg.imm 0, ())) fun p_6 =>
          Expr.jnz (Arg.var p_6.fst)
            (Expr.let_ (Op.mk (.add i64) (Arg.var p.snd.fst, Arg.imm 1, ())) fun p_7 =>
            Expr.jump Js.fst (Arg.var p_7.fst, ()))
            (Expr.jump Js.fst (Arg.var p.snd.fst, ())))
        (k_done p)) Blocks.nil)
      (fun Js => Expr.jump Js.fst (Arg.imm 0, Arg.imm 0, ()))) m1 := by
  subst hfptr
  have hcl := hinv1.sparse.lengths.core_ok
  have hcv_le := hcl.cur_vars_le
  have hfl_len := hcl.flags_len
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  refine wp_loop_inv (fun (ai, _cnt, ()) mL => mL = m1 ∧ ai.toNat ≤ s1.core.cur_vars)
    (fun (ai, _, ()) _ => s1.core.cur_vars - ai.toNat)
    (fun JL hJL => by c0_hfast_nogrp; exact hJL (0#64, 0#64, ()) m1 ⟨rfl, Nat.zero_le _⟩)
    (fun JL (ai, cnt, ()) mL ⟨hmL, hai_le⟩ ihL => by
      subst mL
      refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
      c0_hfast_nogrp
      · have hai_lt : ai.toNat < s1.core.cur_vars := by
          have hlt := BitVec.lt_def.mp ‹ai < BitVec.ofNat 64 s1.core.cur_vars›
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hlt; exact hlt
        have hai1 : (ai + 1#64).toNat = ai.toNat + 1 := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        refine wp_join_group (ts := [i64]) (fun _ mc => mc = m1)
          (fun _ ⟨cnt', ⟨⟩⟩ mc hmc => by
            subst mc; c0_hfast_nogrp
            exact ihL (ai + 1#64, cnt', ()) m1 (by dsimp only; omega) ⟨rfl, by omega⟩)
          (fun Js hJs => by
            c0_hfast_nogrp <;> exact hJs (_, ()) m1 rfl)
      · exact hk (ai, cnt, ()))

abbrev probeReb20Expr (c : FullCfg) (saved_prob : Val i64) (k_ok : Expr Val Cont [i64]) :
    Expr Val Cont [i64] :=
  Expr.call (as := [i64]) (bs := [i64]) "full_rebuild_watches_nosort_fid"
    (Arg.var c.hdr, ()) fun p =>
  Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p.fst, Arg.imm 20, ())) fun p_1 =>
  Expr.jnz (Arg.var p_1.fst) (probeRetWmExpr c saved_prob 20#64) k_ok

theorem probe_factor_block {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {ext1 : List (BitVec 64)}
    {s s1 : FullState} {R : Mem 64 → Prop} {m1 : Mem 64} {saved_prob dticks : Val i64}
    {Q : Post [i64]} {X : XPost} {k_done : Expr Val Cont [i64]}
    (henv : ProbeEnv Γ) (hinv1 : ProbeStateInv c F0 s R ext1 s1 m1)
    (hQ : ProbeQ c F0 s R Q)
    (hk : ∀ ext' s' m', ProbeStateInv c F0 s R ext' s' m' → wp Γ Q X k_done m') :
    wp Γ Q X (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 792, ())) fun p =>
      Expr.load i64 (Arg.var p.fst) fun ld =>
      Expr.let_ (Op.mk (.udiv 64) (Arg.var ld, Arg.imm 10, ())) fun p_1 =>
      Expr.group (sig := [[i64, i64]]) (fun JL => Blocks.cons (fun p_2 =>
        Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ =>
          Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun p_7 =>
            Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ => k_done) Blocks.nil)
              fun Jf =>
            Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 792, ())) fun p_8 =>
            Expr.load i64 (Arg.var p_8.fst) fun ld_2 =>
            Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var ld_2, Arg.imm 0, ()))
              fun p_9 =>
            Expr.jnz (Arg.var p_9.fst)
              (Expr.let_ (Op.mk (.cmp .ule i64 Ty.bool rfl) (Arg.var p_2.fst, Arg.var p_7.fst, ()))
                fun p_10 =>
              Expr.jnz (Arg.var p_10.fst)
                (Expr.call (as := [i64]) (bs := [.bool]) "full_has_factor_cands_fid"
                    (Arg.var c.hdr, ()) fun p_11 =>
                  Expr.jnz (Arg.var p_11.fst)
                    (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ => Expr.jump Jf.fst ())
                        Blocks.nil) fun Js =>
                      Expr.call (as := [i64, .bool]) (bs := [.bool]) "full_enter_dense_ex_fid"
                          (Arg.var c.hdr, Arg.imm false, ()) fun p_12 =>
                        Expr.jnz (Arg.var p_12.fst)
                          (Expr.call (as := [i64, i64]) (bs := [i64]) "m6_hdr_get_watermark"
                              (Arg.var c.hdr, Arg.imm 1, ()) fun p_13 =>
                            Expr.let_ (Op.mk (.add i64) (Arg.var p_13.fst, Arg.imm 1, ()))
                              fun p_14 =>
                            Expr.call (as := [i64, i64, i64]) (bs := []) "m6_hdr_set_watermark"
                                (Arg.var c.hdr, Arg.imm 1, Arg.var p_14.fst, ()) fun _ =>
                              Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun fbud =>
                                Expr.call (as := [i64, i64]) (bs := [i64]) "full_factor"
                                    (Arg.var c.hdr, Arg.var fbud.fst, ()) fun _ =>
                                  probeReb20Expr c saved_prob (Expr.jump Js.fst ()))
                                  Blocks.nil)
                                fun Jfb =>
                                Expr.let_ (Op.mk (.cmp .ule i64 Ty.bool rfl)
                                    (Arg.var p_14.fst, Arg.imm 1, ())) fun p_15 =>
                                Expr.jnz (Arg.var p_15.fst)
                                  (Expr.jump Jfb.fst (Arg.imm 700000000, ()))
                                  (Expr.let_ (Op.mk (.udiv 64) (Arg.var dticks, Arg.imm 20, ()))
                                    fun p_16 => Expr.jump Jfb.fst (Arg.var p_16.fst, ())))
                          (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1024, ()))
                            fun p_13 =>
                            Expr.load i64 (Arg.var p_13.fst) fun ld_3 =>
                            Expr.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl)
                                (Arg.var ld_3, Arg.imm 0, ())) fun p_14 =>
                            Expr.jnz (Arg.var p_14.fst) (probeRetWmExpr c saved_prob 20#64)
                              (Expr.jump Js.fst ())))
                    (Expr.jump Jf.fst ()))
                (Expr.jump Jf.fst ()))
              (Expr.jump Jf.fst ())) Blocks.nil)
            fun Jfe =>
              Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1000, ())) fun p_3 =>
              Expr.load i64 (Arg.var p_3.fst) fun ld_1 =>
              Expr.let_ (Op.mk (.not i64) (Arg.imm 0, ())) fun p_4 =>
              Expr.let_ (Op.mk (.sub i64) (Arg.var p_4.fst, Arg.imm 4, ())) fun p_5 =>
              Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var ld_1, Arg.var p_5.fst, ()))
                fun p_6 =>
              Expr.jnz (Arg.var p_6.fst)
                (Expr.let_ (Op.mk (.not i64) (Arg.imm 0, ())) fun p_7 =>
                Expr.jump Jfe.fst (Arg.var p_7.fst, ()))
                (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 1000, ())) fun p_7 =>
                Expr.load i64 (Arg.var p_7.fst) fun ld_1b =>
                Expr.let_ (Op.mk (.add i64) (Arg.var ld_1b, Arg.imm 4, ())) fun p_8 =>
                Expr.jump Jfe.fst (Arg.var p_8.fst, ()))) Blocks.nil)
        fun Jex => Expr.let_ (Op.mk (.cmp .uge i64 Ty.bool rfl)
            (Arg.var p_1.fst, Arg.var p_2.snd.fst, ())) fun p_3 =>
          Expr.jnz (Arg.var p_3.fst)
            (Expr.let_ (Op.mk (.cmp .ult i64 Ty.bool rfl) (Arg.var p_2.fst, Arg.imm 19, ()))
              fun p_4 =>
            Expr.jnz (Arg.var p_4.fst)
              (Expr.let_ (Op.mk (.add i64) (Arg.var p_2.fst, Arg.imm 1, ())) fun p_5 =>
              Expr.let_ (Op.mk (.mul i64) (Arg.var p_2.snd.fst, Arg.imm 10, ())) fun p_6 =>
              Expr.jump JL.fst (Arg.var p_5.fst, Arg.var p_6.fst, ()))
              (Expr.jump Jex.fst ()))
            (Expr.jump Jex.fst ())) Blocks.nil)
        (fun Js => Expr.jump Js.fst (Arg.imm 1, Arg.imm 10, ()))) m1 := by
  obtain ⟨hinv, hcl, hfu, hm⟩ := hinv1
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  c0_hfast_nogrp
  refine wp_loop_inv (ts := [i64, i64]) (fun (fr, _fp, ()) mL => mL = m1 ∧ fr.toNat ≤ 19)
    (fun (fr, _, ()) _ => 19 - fr.toNat)
    (fun JL hJL => by c0_hfast_nogrp; exact hJL (1#64, 10#64, ()) m1 ⟨rfl, by decide⟩)
    (fun JL (fr, fp, ()) mL ⟨hmL, hfr_le⟩ ihL => by
      subst mL
      refine wp_join_group (ts := []) (fun _ mEx => mEx = m1) ?_ ?_
      · rintro _ _ mEx hmEx; subst mEx; clear ihL
        refine wp_join_group (ts := [i64]) (fun _ mf => mf = m1) ?_
          (fun _ hJfe => by
            refine wp_m6Hdr_focus_frame hm fun hmf2 => ?_
            c0_hfast_nogrp <;> exact hJfe (_, ()) m1 rfl)
        rintro _ ⟨fe4, ⟨⟩⟩ mf hmf_eq; subst mf
        refine wp_join_group (ts := [])
          (fun _ mDone => ∃ extD sD, ProbeStateInv c F0 s R extD sD mDone)
          (fun _ _ mDone ⟨extD, sD, hD⟩ => by
            try dsimp only [Blocks.get_here]
            exact hk extD sD mDone hD)
          (fun Jf hJf => by
            refine wp_m6Hdr_focus_frame hm fun hmf3 => ?_
            c0_hfast_nogrp
            · c0_call henv.hasFact
              refine ⟨c, s1, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hinv.sparse.lengths,
                hmf3, fun hcnd => ?_⟩
              c0_hfast_nogrp
              · refine wp_join_group (ts := [])
                  (fun _ mInc => ∃ extI sI, ProbeStateInv c F0 s R extI sI mInc)
                  (fun _ _ mInc ⟨extI, sI, hinvI⟩ => hJf () mInc ⟨extI, sI, hinvI⟩)
                  (fun Jinc hJinc => by
                    c0_call henv.enterEx
                    refine ⟨c, F0, ext1, s1, R, rfl, hinv.cfgOk, hinv.extOk, hinv.sparse.lengths,
                      hinv.sparse.1, hinv.sparse.2.1, hinv.sparse.2.2.1, hinv.sparse.2.2.2.1,
                      (fun hdm => absurd hinv.sparse.2.2.2.2 hdm), fullM6HdrMem_unfocus hmf3,
                      fun okE extE sE mE _ hextE _ hlenE hlmE hndE hesE _ hfuE hdenE hspE
                        hmE => ?_⟩
                    have hfuE' := Nat.le_trans hfuE hfu
                    c0_hfast_nogrp
                    · obtain ⟨hdenE', _⟩ := hdenE ‹okE = true›
                      refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.getWm _ _ _ _ h)
                        hinv.cfgOk hextE hlenE hmE
                        fun ⟨wval, ⟨⟩⟩ extW sW mW hcW hlW hmsW hextW _ hmW => ?_
                      have hdenW := fullDenseInv_of_core_eq hdenE' hlW hcW hmsW.extPres
                      have hfuW : sW.core.fuel.toNat ≤ s.core.fuel.toNat := by
                        rw [hcW]; exact hfuE'
                      c0_hfast_nogrp
                      refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.setWm _ _ _ _ h)
                        hinv.cfgOk hextW hlW hmW fun _ extS sS mS hcS hlS hmsS hextS _ hmS => ?_
                      have hdenS := fullDenseInv_of_core_eq hdenW hlS hcS hmsS.extPres
                      have hfuS : sS.core.fuel.toNat ≤ s.core.fuel.toNat := by
                        rw [hcS]; exact hfuW
                      refine wp_join_group (ts := [i64]) (fun _ mb => mb = mS)
                        (fun _ ⟨fbud, ⟨⟩⟩ mb hmb => by
                          subst mb
                          refine wp_m6Hdr_focus_frame hmS fun hmSf => ?_
                          c0_call henv.factor
                          refine ⟨c, F0, sS, m6ExtMem (m6ExtAddr c.hdr) extS ⋆ R, rfl, hdenS, hmSf,
                            fun _ sFa mFa hdenFa _ hfuFa _ hmFa => ?_⟩
                          have hfuFa' : sFa.core.fuel.toNat ≤ s.core.fuel.toNat := by
                            rw [hfuFa]; exact hfuS
                          refine probe_reb20 henv hinv.cfgOk hextS hdenFa hfuFa'
                            (fullM6HdrMem_unfocus hmFa) hQ
                            fun extR sR mR hinvR => hJinc () mR ⟨extR, sR, hinvR⟩)
                        (fun _ hJfb => by c0_hfast_nogrp <;> exact hJfb (_, ()) mS rfl)
                    · refine wp_m6Hdr_focus_frame hmE fun hmEf => ?_
                      have hinvE := FullM6HdrInv.mk_inv hinv.cfgOk hextE (hspE ‹okE = false›).1
                      c0_hfast_nogrp
                      · exact probe_ret_wm henv hinvE.cfgOk hextE hinvE.sparse.lengths hfuE'
                          (Or.inr rfl) (fun _ => fullM6HdrInv_inconsistent_unsat hinvE ‹_›)
                          (fun h => by cases h) (fullM6HdrMem_unfocus (by assumption)) hQ
                      · exact hJinc () mE ⟨extE, sE, hinvE, (hspE ‹okE = false›).2, hfuE',
                          fullM6HdrMem_unfocus (by assumption)⟩)
              · exact hJf () m1 ⟨ext1, s1, hinv, hcl, hfu, fullM6HdrMem_unfocus hmf3⟩
            all_goals exact hJf () m1 ⟨ext1, s1, hinv, hcl, hfu, fullM6HdrMem_unfocus hmf3⟩)
      · intro Jex hJex
        c0_hfast_nogrp
        · have hfr_lt : fr.toNat < 19 :=
            Nat.lt_of_lt_of_eq (BitVec.lt_def.mp ‹fr < 19#64›) (by decide)
          have hfr1 : (fr + 1#64).toNat = fr.toNat + 1 := by
            rw [BitVec.toNat_add, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
          exact ihL (fr + 1#64, fp * 10#64, ()) m1 (by dsimp only; rw [hfr1]; omega)
            ⟨rfl, by rw [hfr1]; omega⟩
        all_goals exact hJex () m1 rfl)

end LeanQbe.T.Examples.Kissat.Proof.Probe
