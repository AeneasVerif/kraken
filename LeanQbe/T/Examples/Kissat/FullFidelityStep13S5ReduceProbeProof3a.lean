/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5ReduceProbeProof0
public import LeanQbe.T.Examples.Kissat.FullM6Orch
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof1
public import LeanQbe.T.Examples.Kissat.FullM3BackboneLemmas1
public import LeanQbe.T.Examples.Kissat.FullFastSchedLemmas
public import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas1
public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas1
public import LeanQbe.T.Examples.Kissat.FullBvaHeapSpec
public import LeanQbe.T.Examples.Kissat.FullSpec1
import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Step 13 S5 `full_probe_m6` Helpers & `!initial` Path (`Proof3a`)

Provides shared probing environment/postcondition helpers, `s5_probe_ret_wm`,
shared `substitute`/`backbone`/`rebuild`/`bin_roundtrip`/factor/var-count helpers,
and `full_probe_m6_notinit_core` (`<= 390` lines per decl, `< 1,400` LOC, `<= 100` cols).
-/

set_option autoImplicit false

local elab "c0_hfast_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

local macro "c0_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullDefSweep (fullSweepDenseSpec)
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM6Hdr LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open FullArenaTactics
open scoped FullArenaTactics FullM6Hdr.M6HdrTactics FullM6ProofUtil.M6ProofUtilTactics

/-! ## 1. Probing Environment, Postcondition, Invariants, and Tail Return -/

structure S5ProbeEnv (Γ : Env) : Prop where
  probeDt : ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
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
  updCls : ∀ a m Q X, step13UpdateClassifyM6Spec a m Q X →
    Γ "full_update_classify_fid" [i64] [] a m Q X
  enter : ∀ a m Q X, step13EnterDenseM6Spec a m Q X →
    Γ "full_enter_dense" [i64] [.bool] a m Q X
  enterEx : ∀ a m Q X, step13EnterDenseExM6Spec a m Q X →
    Γ "full_enter_dense_ex_fid" [i64, .bool] [.bool] a m Q X
  cong : ∀ a m Q X, FullM3CongBva.m3CongruenceDenseSpec a m Q X →
    Γ "full_congruence_dense" [i64, i64] [i64] a m Q X
  binRt : ∀ a m Q X, step13DenseBinRoundtripSpec a m Q X →
    Γ "full_dense_bin_roundtrip_fid" [i64] [] a m Q X
  rebNosort : ∀ a m Q X, step13RebuildWatchesM6Spec a m Q X →
    Γ "full_rebuild_watches_nosort_fid" [i64] [i64] a m Q X
  subst : ∀ a m Q X, step13SubstituteM6Spec a m Q X →
    Γ "full_substitute" [i64] [i64] a m Q X
  bone : ∀ a m Q X, s5aBackboneSpec a m Q X →
    Γ "full_backbone_m6" [i64, i64] [i64] a m Q X
  sweepD : ∀ a m Q X, fullSweepDenseSpec a m Q X →
    Γ "full_sweep_dense_m6" [i64, i64, i64] [i64] a m Q X
  hasFact : ∀ a m Q X, step13HasFactorCandsSpec a m Q X →
    Γ "full_has_factor_cands_fid" [i64] [.bool] a m Q X
  factor : ∀ a m Q X, fullFactorHeapSpec a m Q X →
    Γ "full_factor" [i64, i64] [i64] a m Q X
  viv : ∀ a m Q X, s5aVivifySpec a m Q X →
    Γ "full_vivify_m6_hdr" [i64] [i64] a m Q X
  trans : ∀ a m Q X, s5aTransitiveSpec a m Q X →
    Γ "full_transitive_m6" [i64, i64] [i64] a m Q X
  nlogpown : ∀ a m Q X, f64uPure2Spec a m Q X →
    Γ "f64u_nlogpown" [i64, i64] [i64] a m Q X
  mul : ∀ a m Q X, f64uPure2Spec a m Q X →
    Γ "f64u_mul" [i64, i64] [i64] a m Q X
  toU64 : ∀ a m Q X, f64uPure1Spec a m Q X →
    Γ "f64u_to_u64" [i64] [i64] a m Q X
  scaleM5 : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
    Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X

abbrev S5ProbeQ (c : FullCfg) (F0 : CNF Nat) (s : FullState)
    (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ r ext' s' m',
    s'.LengthsOk c → M6HdrExtOk ext' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
    (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
    (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
    (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

abbrev S5ProbeStateInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop)
    (ext1 : List (BitVec 64)) (s1 : FullState) (m1 : Mem 64) : Prop :=
  FullM6HdrInv c F0 ext1 s1 ∧ s1.core.cur_level = 0 ∧
  s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c ext1 s1 ⋆ R) m1

theorem s5M6HdrInv_with_probing {c : FullCfg} {F0 : CNF Nat}
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

theorem s5Dense_zero_gu32 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) :
    FullDenseInv c F0
      { s with scratch := { s.scratch with glue_used := s.scratch.glue_used.set 32 0#32 } } :=
  let sc_ok := h.lengths.scratch_ok
  h.of_safetySlice
    ⟨h.lengths.core_ok, { sc_ok with glue_used_len := (by simp [sc_ok.glue_used_len]) }⟩
    rfl ⟨rfl, rfl⟩

abbrev s5RetWmExpr (c : FullCfg) (saved_prob : Val i64) (r : BitVec 64) : Expr Val Cont [i64] :=
  Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 520, ())) fun p =>
  Expr.store (t := i64) (Arg.var saved_prob) (Arg.var p.fst)
    (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 600, ())) fun p_1 =>
    Expr.load i64 (Arg.var p_1.fst) fun ld =>
    Expr.call (as := [i64, i64, i64]) (bs := []) "m6_hdr_set_watermark"
      (Arg.var c.hdr, Arg.imm 0, Arg.var ld, ()) fun _ => Expr.ret (Arg.imm r, ()))

theorem s5_probe_ret_wm {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s s0 : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {saved_prob : Val i64} {r : BitVec 64} {Q : Post [i64]} {X : XPost}
    (henv : S5ProbeEnv Γ) (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext)
    (hlen : s0.LengthsOk c) (hfu : s0.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hr : r = 1#64 ∨ r = 20#64) (hu : r = 20#64 → F0.Unsat)
    (h1 : r = 1#64 → FullM6HdrInv c F0 ext s0 ∧ s0.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s0 ⋆ R) m) (hQ : S5ProbeQ c F0 s R Q) :
    wp Γ Q X (s5RetWmExpr c saved_prob r) m := by
  dsimp only [s5RetWmExpr]
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
  exact ⟨fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres (s5M6HdrInv_with_probing hi saved_prob)
    hlen' hc' hms') hext', by rw [hc']; exact hcl⟩

/-! ## 2. Shared Sparse/Dense Call Blocks (`substitute`, `backbone`, `reb`, `bin_rt`) -/

theorem s5_probe_subst_if {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {ext1 : List (BitVec 64)}
    {s s1 : FullState} {R : Mem 64 → Prop} {m1 : Mem 64} {saved_prob : Val i64}
    {Q : Post [i64]} {X : XPost} {k : Expr Val Cont [i64]}
    (henv : S5ProbeEnv Γ) (hinv1 : S5ProbeStateInv c F0 s R ext1 s1 m1)
    (hQ : S5ProbeQ c F0 s R Q)
    (hk : ∀ ext' s' m', S5ProbeStateInv c F0 s R ext' s' m' → wp Γ Q X k m') :
    wp Γ Q X (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 504, ())) fun p =>
      Expr.load i64 (Arg.var p.fst) fun ld =>
      Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p_1 =>
      Expr.jnz (Arg.var p_1.fst)
        (Expr.call (as := [i64]) (bs := [i64]) "full_substitute" (Arg.var c.hdr, ()) fun p_2 =>
          Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_2.fst, Arg.imm 20, ()))
            fun p_3 =>
          Expr.jnz (Arg.var p_3.fst) (s5RetWmExpr c saved_prob 20#64) k) k) m1 := by
  obtain ⟨hinv, hcl, hfu, hm⟩ := hinv1
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  c0_hfast_nogrp
  · c0_call henv.subst
    refine ⟨c, F0, ext1, s1, R, rfl, hinv, fullM6HdrMem_unfocus hmf,
      fun rSu extSu sSu mSu hinvSu hclSu hfuSu _ huSu hmSu => ?_⟩
    have hfuSu' := Nat.le_trans hfuSu hfu
    c0_hfast_nogrp
    · exact s5_probe_ret_wm henv hinvSu.cfgOk hinvSu.extOk hinvSu.sparse.lengths hfuSu'
        (Or.inr rfl) (fun _ => huSu ‹_›) (fun h => by cases h) hmSu hQ
    · exact hk extSu sSu mSu ⟨hinvSu, hclSu, hfuSu', hmSu⟩
  · exact hk ext1 s1 m1 ⟨hinv, hcl, hfu, fullM6HdrMem_unfocus hmf⟩

theorem s5_probe_bone_if {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {ext1 : List (BitVec 64)}
    {s s1 : FullState} {R : Mem 64 → Prop} {m1 : Mem 64} {saved_prob dticks : Val i64}
    {Q : Post [i64]} {X : XPost} {k : Expr Val Cont [i64]}
    (henv : S5ProbeEnv Γ) (hinv1 : S5ProbeStateInv c F0 s R ext1 s1 m1)
    (hQ : S5ProbeQ c F0 s R Q)
    (hk : ∀ ext' s' m', S5ProbeStateInv c F0 s R ext' s' m' → wp Γ Q X k m') :
    wp Γ Q X (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 504, ())) fun p =>
      Expr.load i64 (Arg.var p.fst) fun ld =>
      Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p_1 =>
      Expr.jnz (Arg.var p_1.fst)
        (Expr.let_ (Op.mk (.udiv 64) (Arg.var dticks, Arg.imm 50, ())) fun p_2 =>
          Expr.call (as := [i64, i64]) (bs := [i64]) "full_backbone_m6"
              (Arg.var c.hdr, Arg.var p_2.fst, ()) fun p_3 =>
            Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_3.fst, Arg.imm 20, ()))
              fun p_4 =>
            Expr.jnz (Arg.var p_4.fst) (s5RetWmExpr c saved_prob 20#64) k) k) m1 := by
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
    · exact s5_probe_ret_wm henv hinvB.cfgOk hextB.1 hinvB.sparse.lengths hfuB'
        (Or.inr rfl) (fun _ => huB ‹_›) (fun h => by cases h) hmB hQ
    · exact hk extB sB mB ⟨hinvB, hclprB.1, hfuB', hmB⟩
  · exact hk ext1 s1 m1 ⟨hinv, hcl, hfu, fullM6HdrMem_unfocus hmf⟩

theorem s5_probe_reb20 {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {extD : List (BitVec 64)}
    {s sD : FullState} {R : Mem 64 → Prop} {mD : Mem 64} {saved_prob : Val i64}
    {Q : Post [i64]} {X : XPost} {k_ok : Expr Val Cont [i64]}
    (henv : S5ProbeEnv Γ) (hcfg : FullM6HdrCfgOk c) (hextD : M6HdrExtOk extD)
    (hdenD : FullDenseInv c F0 sD) (hfuD : sD.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hmD : (FullM6HdrMem c extD sD ⋆ R) mD) (hQ : S5ProbeQ c F0 s R Q)
    (hk : ∀ extR sR mR, S5ProbeStateInv c F0 s R extR sR mR → wp Γ Q X k_ok mR) :
    wp Γ Q X (Expr.call (as := [i64]) (bs := [i64]) "full_rebuild_watches_nosort_fid"
        (Arg.var c.hdr, ()) fun p =>
      Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p.fst, Arg.imm 20, ())) fun p_1 =>
      Expr.jnz (Arg.var p_1.fst) (s5RetWmExpr c saved_prob 20#64) k_ok) mD := by
  c0_call henv.rebNosort
  refine ⟨c, F0, extD, sD, R, rfl, hcfg, hextD, hdenD, hmD,
    fun rR extR sR mR hinvR hclR hfuR _ huR hmR => ?_⟩
  have hfuR' := Nat.le_trans hfuR hfuD
  c0_hfast_nogrp
  · exact s5_probe_ret_wm henv hinvR.cfgOk hinvR.extOk hinvR.sparse.lengths hfuR'
      (Or.inr rfl) (fun _ => huR ‹_›) (fun h => by cases h) hmR hQ
  · exact hk extR sR mR ⟨hinvR, hclR, hfuR', hmR⟩

theorem s5_probe_bin_rt {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {extD : List (BitVec 64)}
    {sD : FullState} {R : Mem 64 → Prop} {mD : Mem 64} {Q : Post [i64]} {X : XPost}
    {k : Expr Val Cont [i64]}
    (henv : S5ProbeEnv Γ) (hdenD : FullDenseInv c F0 sD)
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
      _ _ _ _ _ _ _ _ _ _ _ hmRt => ?_⟩
  exact hk sRt mRt
    ⟨⟨hlenRt, F_cur, hwRt⟩, hlmRt, hndRt, hesRt,
      hclRt.trans hdenD.2.2.2.2.1, hdmRt ▸ hdenD.2.2.2.2.2⟩
    hfuRt (fullM6HdrMem_unfocus hmRt)

/-! ## 3. Shared Active-Variable Count Loop & Factor Block -/

theorem s5_probe_var_cnt_loop {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {ext1 : List (BitVec 64)}
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

theorem s5_probe_var_cnt_ai_loop {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {ext1 : List (BitVec 64)}
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

abbrev s5Reb20Expr (c : FullCfg) (saved_prob : Val i64) (k_ok : Expr Val Cont [i64]) :
    Expr Val Cont [i64] :=
  Expr.call (as := [i64]) (bs := [i64]) "full_rebuild_watches_nosort_fid"
    (Arg.var c.hdr, ()) fun p =>
  Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p.fst, Arg.imm 20, ())) fun p_1 =>
  Expr.jnz (Arg.var p_1.fst) (s5RetWmExpr c saved_prob 20#64) k_ok

theorem s5_probe_factor_block {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {ext1 : List (BitVec 64)}
    {s s1 : FullState} {R : Mem 64 → Prop} {m1 : Mem 64} {saved_prob dticks : Val i64}
    {Q : Post [i64]} {X : XPost} {k_done : Expr Val Cont [i64]}
    (henv : S5ProbeEnv Γ) (hinv1 : S5ProbeStateInv c F0 s R ext1 s1 m1)
    (hQ : S5ProbeQ c F0 s R Q)
    (hk : ∀ ext' s' m', S5ProbeStateInv c F0 s R ext' s' m' → wp Γ Q X k_done m') :
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
                                  s5Reb20Expr c saved_prob (Expr.jump Js.fst ()))
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
                            Expr.jnz (Arg.var p_14.fst) (s5RetWmExpr c saved_prob 20#64)
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
          (fun _ mDone => ∃ extD sD, S5ProbeStateInv c F0 s R extD sD mDone)
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
                  (fun _ mInc => ∃ extI sI, S5ProbeStateInv c F0 s R extI sI mInc)
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
                          refine s5_probe_reb20 henv hinv.cfgOk hextS hdenFa hfuFa'
                            (fullM6HdrMem_unfocus hmFa) hQ
                            fun extR sR mR hinvR => hJinc () mR ⟨extR, sR, hinvR⟩)
                        (fun _ hJfb => by c0_hfast_nogrp <;> exact hJfb (_, ()) mS rfl)
                    · refine wp_m6Hdr_focus_frame hmE fun hmEf => ?_
                      have hinvE := FullM6HdrInv.mk_inv hinv.cfgOk hextE (hspE ‹okE = false›).1
                      c0_hfast_nogrp
                      · exact s5_probe_ret_wm henv hinvE.cfgOk hextE hinvE.sparse.lengths hfuE'
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

/-! ## 4. `!initial` Path (`full_probe_m6_notinit_core`) -/

private theorem s5_probe_tail_ret1 {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {s : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {saved_prob : Val i64} {ext1 : List (BitVec 64)} {s1 : FullState} {m1 : Mem 64}
    (henv : S5ProbeEnv Γ) (hinv1 : S5ProbeStateInv c F0 s R ext1 s1 m1)
    (hQ : S5ProbeQ c F0 s R Q) :
    wp Γ Q X (Expr.call (as := [i64]) (bs := []) "full_update_classify_fid"
        (Arg.var c.hdr, ()) fun _ =>
      Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun _ =>
          s5RetWmExpr c saved_prob 1#64) Blocks.nil) fun Js =>
        Expr.jnz (Arg.var (false : Val .bool)) (Expr.jump Js.fst ())
          (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 984, ())) fun p =>
          Expr.load i64 (Arg.var p.fst) fun ld =>
          Expr.call (as := [i64, i64]) (bs := [i64]) "f64u_nlogpown"
            (Arg.var ld, Arg.imm 1, ()) fun p_1 =>
          Expr.call (as := [i64, i64]) (bs := [i64]) "f64u_mul"
            (Arg.imm 4636737291354636288, Arg.var p_1.fst, ()) fun p_2 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 336, ())) fun p_3 =>
          Expr.load i64 (Arg.var p_3.fst) fun ld_1 =>
          Expr.call (as := [i64]) (bs := [i64]) "f64u_to_u64" (Arg.var p_2.fst, ()) fun p_4 =>
          Expr.call (as := [i64, i64]) (bs := [i64]) "full_scale_delta_m5"
            (Arg.var c.hdr, Arg.var p_4.fst, ()) fun p_5 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var ld_1, Arg.var p_5.fst, ())) fun p_6 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 976, ())) fun p_7 =>
          Expr.store (t := i64) (Arg.var p_6.fst) (Arg.var p_7.fst) (Expr.jump Js.fst ()))) m1 := by
  obtain ⟨hinv, hcl, hfu, hm⟩ := hinv1
  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.updCls _ _ _ _ h) hinv.cfgOk hinv.extOk
    hinv.sparse.lengths hm fun _ extU sU mU hcU hlU hmsU hextU _ hmU => ?_
  have hinvU := fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres hinv hlU hcU hmsU) hextU
  have hclU : sU.core.cur_level = 0 := by rw [hcU]; exact hcl
  have hfuU : sU.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hcU]; exact hfu
  refine wp_join_group (ts := []) (fun _ mF => ∃ extF sF, S5ProbeStateInv c F0 s R extF sF mF)
    (fun _ _ mF ⟨extF, sF, hinvF, hclF, hfuF, hmF⟩ =>
      s5_probe_ret_wm henv hinvF.cfgOk hinvF.extOk hinvF.sparse.lengths hfuF
        (Or.inl rfl) (fun h => by cases h) (fun _ => ⟨hinvF, hclF⟩) hmF hQ)
    (fun JF hJF => by
      refine wp_m6Hdr_focus_frame hmU fun hmUf => ?_
      c0_hfast_nogrp
      c0_call henv.nlogpown; intro _
      c0_call henv.mul; intro _
      c0_hfast_nogrp
      c0_call henv.toU64; intro _
      c0_call henv.scaleM5
      refine ⟨c, sU, m6ExtMem (m6ExtAddr c.hdr) extU ⋆ R, rfl, hinvU.sparse.lengths,
        by assumption, fun sd => ?_⟩
      c0_hfast_nogrp
      have hstP := fullState_upd_probe_step hinvU.sparse.lengths
        (sU.scratch.conflicts + sd) sU.scratch.probings
      have hinvP := fullM6HdrInv_of_probeStep hinvU hstP
      have hlim : ({ sU with scratch := { sU.scratch with
          probe_limit := sU.scratch.conflicts + sd, probings := sU.scratch.probings } } :
          FullState) =
          { sU with scratch := { sU.scratch with probe_limit := sU.scratch.conflicts + sd } } := by
        cases sU with | mk _ sc => cases sc; rfl
      have hmP : (FullM6HdrMem c extU
          { sU with scratch := { sU.scratch with probe_limit := sU.scratch.conflicts + sd } } ⋆ R)
          _ := fullM6HdrMem_unfocus (by rw [← hlim]; exact hm)
      exact hJF () _ ⟨extU, _, hinvP, hstP.2.1 ▸ hclU, by rw [hstP.2.1]; exact hfuU, hmP⟩)

theorem full_probe_m6_notinit_core (Γ : Env) (henv : S5ProbeEnv Γ)
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hinv : FullM6HdrInv c F0 ext s) (hcl0 : s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m) (hQ : S5ProbeQ c F0 s R Q) :
    Func.wp Γ FullFidelityStep13S5ReduceProbe.full_probe_m6_body (c.hdr, false, ()) m Q X := by
  unfold Func.wp FullFidelityStep13S5ReduceProbe.full_probe_m6_body
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  c0_hfast_nogrp
  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.probeDt _ _ _ _ h)
    hinv.cfgOk hinv.extOk hinv.sparse.lengths (fullM6HdrMem_unfocus hmf)
    fun ⟨dticks, ⟨⟩⟩ ext0 s0 m0 hc0 hlen0 hms0 hext0 _ hm0 => ?_
  have hinv0 := fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres hinv hlen0 hc0 hms0) hext0
  have hcl0' : s0.core.cur_level = 0 := by rw [hc0]; exact hcl0
  refine wp_m6Hdr_focus_frame hm0 fun hm0f => ?_
  c0_hfast_nogrp
  let s0s : FullState :=
    { s0 with scratch := { s0.scratch with probings := s0.scratch.probings + 1#64 } }
  have hst0a := fullState_upd_probe_step hinv0.sparse.lengths s0.scratch.probe_limit
    (s0.scratch.probings + 1#64)
  let s0a : FullState := { s0s with core := { s0s.core with probing := 1#64 } }
  have hinv0a := s5M6HdrInv_with_probing (fullM6HdrInv_of_probeStep hinv0 hst0a) 1#64
  have hcl0a : s0a.core.cur_level = 0 := hcl0'
  have hfu0a : s0a.core.fuel.toNat ≤ s.core.fuel.toNat := by
    dsimp only [s0a, s0s]; rw [hc0]; exact Nat.le_refl _
  have hm0a : (FullM6HdrMem c ext0 s0a ⋆ R) _ := fullM6HdrMem_unfocus (by assumption)
  refine wp_join_group (ts := []) (fun _ m1 => ∃ ext1 s1, S5ProbeStateInv c F0 s R ext1 s1 m1)
    ?_ ?_
  · rintro _ _ m1 ⟨ext1, s1, hinv1⟩
    try dsimp only [Blocks.get_here]
    exact s5_probe_tail_ret1 henv hinv1 hQ
  · intro J1 hJ1
    c0_hfast_nogrp
    refine wp_join_group (ts := [i64])
      (fun _ mB => ∃ extB sB, S5ProbeStateInv c F0 s R extB sB mB) ?_ ?_
    · rintro _ ⟨_, ⟨⟩⟩ mB hB; try dsimp only [Blocks.get_here]; c0_hfast_nogrp; exact hJ1 () mB hB
    · intro Jbrk hJbrk
      c0_hfast_nogrp
      refine wp_loop_inv (fun (round, ()) mL => round.toNat ≤ 2 ∧
          ∃ extL sL, S5ProbeStateInv c F0 s R extL sL mL)
        (fun (round, ()) _ => 2 - round.toNat)
        (fun JL hJL => by
          c0_hfast_nogrp
          exact hJL (0#64, ()) _ ⟨Nat.zero_le _, ext0, s0a, hinv0a, hcl0a, hfu0a, hm0a⟩)
        (fun JL (round, ()) mL ⟨hnd_le, extL, sL, hinvL, hclL, hfuL, hmL⟩ ihL => ?_)
      · c0_hfast_nogrp
        · have hnd_lt : round.toNat < 2 :=
            Nat.lt_of_lt_of_eq (BitVec.lt_def.mp ‹round < 2#64›) (by decide)
          have hnd1 : (round + 1#64).toNat = round.toNat + 1 := by
            rw [BitVec.toNat_add, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
          refine wp_m6Hdr_focus_frame hmL fun hmLf => ?_
          c0_hfast_nogrp
          refine s5_probe_var_cnt_loop rfl hinvL (fullM6HdrMem_unfocus hmLf) fun _ => ?_
          refine wp_join_group (ts := [])
            (fun _ mC => ∃ extC sC, S5ProbeStateInv c F0 s R extC sC mC) ?_ ?_
          · rintro _ _ mC ⟨extC, sC, hC⟩; try dsimp only [Blocks.get_here]
            refine wp_join_group (ts := [])
              (fun _ mS1 => ∃ extS1 sS1, S5ProbeStateInv c F0 s R extS1 sS1 mS1) ?_ ?_
            · rintro _ _ mS1 ⟨extS1, sS1, hS1⟩; try dsimp only [Blocks.get_here]
              refine wp_join_group (ts := [])
                (fun _ mB1 => ∃ extB1 sB1, S5ProbeStateInv c F0 s R extB1 sB1 mB1) ?_ ?_
              · rintro _ _ mB1 ⟨extB1, sB1, hinvB1, hclB1, hfuB1, hmB1⟩
                try dsimp only [Blocks.get_here]
                c0_call henv.viv
                refine ⟨c, F0, extB1, sB1, R, rfl, hinvB1.cfgOk, hinvB1.extOk, hinvB1.sparse,
                  hmB1, fun rV extV sV mV hextV hspV hclprV hfuV _ huV hmV => ?_⟩
                have hinvV := FullM6HdrInv.mk_inv hinvB1.cfgOk hextV.1 hspV
                have hfuV' := Nat.le_trans hfuV hfuB1
                c0_hfast_nogrp
                · exact s5_probe_ret_wm henv hinvV.cfgOk hextV.1 hinvV.sparse.lengths hfuV'
                    (Or.inr rfl) (fun _ => huV ‹_›) (fun h => by cases h) hmV hQ
                · refine wp_join_group (ts := [])
                      (fun _ mSw => ∃ extSw sSw, S5ProbeStateInv c F0 s R extSw sSw mSw) ?_ ?_
                  · rintro _ _ mSw ⟨extSw, sSw, hSw⟩; try dsimp only [Blocks.get_here]
                    refine wp_join_group (ts := [])
                      (fun _ mS2 => ∃ extS2 sS2, S5ProbeStateInv c F0 s R extS2 sS2 mS2) ?_ ?_
                    · rintro _ _ mS2 ⟨extS2, sS2, hinvS2, hclS2, hfuS2, hmS2⟩
                      try dsimp only [Blocks.get_here]
                      c0_hfast_nogrp
                      refine wp_join_group (ts := [])
                          (fun _ mTr => ∃ extTr sTr, S5ProbeStateInv c F0 s R extTr sTr mTr) ?_ ?_
                      · rintro _ _ mTr ⟨extTr, sTr, hTr⟩; try dsimp only [Blocks.get_here]
                        refine wp_join_group (ts := [])
                          (fun _ mB2 => ∃ extB2 sB2, S5ProbeStateInv c F0 s R extB2 sB2 mB2) ?_ ?_
                        · rintro _ _ mB2 ⟨extB2, sB2, hB2⟩; try dsimp only [Blocks.get_here]
                          refine s5_probe_factor_block henv hB2 hQ ?_
                          intro extF sF mF ⟨hinvF, hclF, hfuF, hmF⟩
                          refine wp_m6Hdr_focus_frame hmF fun hmFf => ?_
                          c0_hfast_nogrp
                          refine s5_probe_var_cnt_ai_loop rfl hinvF
                            (fullM6HdrMem_unfocus hmFf) fun _ => ?_
                          c0_hfast_nogrp
                          · exact hJbrk (_, ()) _
                              ⟨extF, sF, hinvF, hclF, hfuF, fullM6HdrMem_unfocus hmFf⟩
                          · exact ihL (round + 1#64, ()) _ (by dsimp only; omega)
                              ⟨by omega, extF, sF, hinvF, hclF, hfuF,
                                fullM6HdrMem_unfocus hmFf⟩
                        · intro JB2 hJB2
                          refine s5_probe_bone_if henv hTr hQ fun extB2 sB2 mB2 hB2 => by
                            c0_hfast_nogrp; exact hJB2 () mB2 ⟨extB2, sB2, hB2⟩
                      · intro JTr hJTr
                        refine wp_m6Hdr_focus_frame hmS2 fun hmS2f => ?_
                        c0_hfast_nogrp
                        · c0_call henv.trans
                          refine ⟨c, F0, extS2, sS2, R, rfl, hinvS2.cfgOk, hinvS2.extOk,
                            hinvS2.sparse, fullM6HdrMem_unfocus hmS2f,
                            fun rT extT sT mT hextT hspT _ _ hclprT hfuT _ huT hmT => ?_⟩
                          have hinvT := FullM6HdrInv.mk_inv hinvS2.cfgOk hextT.1 hspT
                          have hfuT' := Nat.le_trans hfuT hfuS2
                          c0_hfast_nogrp
                          · exact s5_probe_ret_wm henv hinvT.cfgOk hextT.1 hinvT.sparse.lengths
                              hfuT' (Or.inr rfl) (fun _ => huT ‹_›) (fun h => by cases h) hmT hQ
                          · exact hJTr () mT ⟨extT, sT, hinvT, hclprT.1, hfuT', hmT⟩
                        · exact hJTr () mS2
                            ⟨extS2, sS2, hinvS2, hclS2, hfuS2, fullM6HdrMem_unfocus hmS2f⟩
                    · intro JS2 hJS2
                      refine s5_probe_subst_if henv hSw hQ fun extS2 sS2 mS2 hS2 => by
                        c0_hfast_nogrp; exact hJS2 () mS2 ⟨extS2, sS2, hS2⟩
                  · -- Sweep `!initial`
                    intro JSw hJSw
                    refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.delay _ _ _ _ h) hinvV.cfgOk
                      hextV.1 hinvV.sparse.lengths hmV
                      fun ⟨delSw, ⟨⟩⟩ extSd sSd mSd hcSd hlSd hmsSd hextSd _ hmSd => ?_
                    have hinvSd := fullM6HdrInv_with_ext
                      (fullM6HdrInv_of_m6Pres hinvV hlSd hcSd hmsSd) hextSd
                    have hclSd : sSd.core.cur_level = 0 := by rw [hcSd]; exact hclprV.1
                    have hfuSd : sSd.core.fuel.toNat ≤ s.core.fuel.toNat := by
                      rw [hcSd]; exact hfuV'
                    c0_hfast_nogrp
                    · exact hJSw () mSd ⟨extSd, sSd, hinvSd, hclSd, hfuSd, hmSd⟩
                    · refine wp_join_group (ts := [])
                        (fun _ mE => ∃ extE sE, S5ProbeStateInv c F0 s R extE sE mE) ?_ ?_
                      · rintro _ _ mE hE; try dsimp only [Blocks.get_here]
                        c0_hfast_nogrp; exact hJSw () mE hE
                      · intro JSw' hJSw'
                        refine wp_m6Hdr_focus_frame hmSd fun hmSdf => ?_
                        c0_call henv.enter
                        refine ⟨c, F0, extSd, sSd, R, rfl, hinvSd.cfgOk, hinvSd.extOk,
                          hinvSd.sparse.lengths, hinvSd.sparse.1, hinvSd.sparse.2.1,
                          hinvSd.sparse.2.2.1, hinvSd.sparse.2.2.2.1,
                          (fun hdm => absurd hinvSd.sparse.2.2.2.2 hdm),
                          fullM6HdrMem_unfocus hmSdf,
                          fun okE extE sE mE _ hextE _ hlenE hlmE hndE hesE _ hfuE hdenE hspE
                            hmE => ?_⟩
                        have hfuE' := Nat.le_trans hfuE hfuSd
                        c0_hfast_nogrp
                        · have hdenE' := hdenE ‹okE = true›
                          refine wp_m6Hdr_focus_frame hmE fun hmEf => ?_
                          have hgu32E : 32 < sE.scratch.glue_used.length := by
                            rw [hdenE'.lengths.scratch_ok.glue_used_len]; decide
                          c0_hfast_nogrp
                          have hdenEz := s5Dense_zero_gu32 hdenE'
                          c0_call henv.sweepD
                          refine ⟨c, F0, _, m6ExtMem (m6ExtAddr c.hdr) extE ⋆ R, rfl, hdenEz,
                            by assumption, fun rSw sSw mSw hdenSw _ hfuSw _ huSw hmSw => ?_⟩
                          have hfuSw' := Nat.le_trans hfuSw hfuE'
                          have hgu32Sw : 32 < sSw.scratch.glue_used.length := by
                            rw [hdenSw.lengths.scratch_ok.glue_used_len]; decide
                          c0_hfast_nogrp
                          · c0_call henv.rebNosort
                            refine ⟨c, F0, extE, sSw, R, rfl, hinvV.cfgOk, hextE, hdenSw,
                              fullM6HdrMem_unfocus hmSw,
                              fun _ extR sR mR hinvR _ hfuR _ _ hmR => ?_⟩
                            exact s5_probe_ret_wm henv hinvR.cfgOk hinvR.extOk
                              hinvR.sparse.lengths (Nat.le_trans hfuR hfuSw') (Or.inr rfl)
                              (fun _ => huSw ‹_›) (fun h => by cases h) hmR hQ
                          · have hmSw' := fullM6HdrMem_unfocus hmSw
                            refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
                                M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧
                                sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                (FullM6HdrMem c extDl sDl ⋆ R) mDl) ?_ ?_
                            · rintro _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩
                              try dsimp only [Blocks.get_here]
                              exact s5_probe_reb20 henv hinvV.cfgOk hextDl hdenDl hfuDl hmDl hQ
                                (fun _ _ mR hR => hJSw' () mR ⟨_, _, hR⟩)
                            · intro JDl hJDl
                              c0_hfast_nogrp
                              refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
                                  M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧
                                  sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                  (FullM6HdrMem c extDl sDl ⋆ R) mDl) ?_ ?_
                              · rintro _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩
                                try dsimp only [Blocks.get_here]
                                refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.bumpD _ _ _ _ h)
                                  hinvV.cfgOk hextDl hdenDl.lengths hmDl
                                  fun _ extDl' sDl' mDl' hcDl hlDl hmsDl hextDl' _ hmDl' => ?_
                                exact hJDl () mDl' ⟨extDl', sDl', hextDl',
                                  fullDenseInv_of_core_eq hdenDl hlDl hcDl hmsDl.extPres,
                                  by rw [hcDl]; exact hfuDl, hmDl'⟩
                              · intro JDb hJDb
                                refine wp_m6Hdr_focus_frame hmSw' fun hmSwf => ?_
                                c0_hfast_nogrp
                                · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.redD _ _ _ _ h)
                                    hinvV.cfgOk hextE hdenSw.lengths (fullM6HdrMem_unfocus hmSwf)
                                    fun _ extDl sDl mDl hcDl hlDl hmsDl hextDl _ hmDl => ?_
                                  exact hJDl () mDl ⟨extDl, sDl, hextDl,
                                    fullDenseInv_of_core_eq hdenSw hlDl hcDl hmsDl.extPres,
                                    by rw [hcDl]; exact hfuSw', hmDl⟩
                                all_goals exact hJDb () _ ⟨extE, sSw, hextE, hdenSw, hfuSw',
                                  fullM6HdrMem_unfocus hmSwf⟩
                        · have hinvE := FullM6HdrInv.mk_inv hinvV.cfgOk hextE (hspE ‹okE = false›).1
                          refine wp_m6Hdr_focus_frame hmE fun hmEf => ?_
                          c0_hfast_nogrp
                          · have hinvE' := s5M6HdrInv_with_probing hinvE s0.core.probing
                            refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.setWm _ _ _ _ h)
                              hinvE'.cfgOk hextE hinvE'.sparse.lengths
                              (fullM6HdrMem_unfocus (by assumption))
                              fun _ ext' s' m' hc' hlen' hms' hext' _ hm' => ?_
                            c0_hfast_nogrp
                            exact hQ 20#64 ext' s' m' hlen' hext' (by rw [hc']; exact hfuE')
                              (Or.inr rfl) (fun _ => fullM6HdrInv_inconsistent_unsat hinvE ‹_›)
                              (fun h => by cases h) hm'
                          · exact hJSw' () mE ⟨extE, sE, hinvE, (hspE ‹okE = false›).2, hfuE',
                              fullM6HdrMem_unfocus (by assumption)⟩
              · intro JB1 hJB1
                refine s5_probe_bone_if henv hS1 hQ fun extB1 sB1 mB1 hB1 => by
                  c0_hfast_nogrp; exact hJB1 () mB1 ⟨extB1, sB1, hB1⟩
            · intro JS1 hJS1
              refine s5_probe_subst_if henv hC hQ fun extS1 sS1 mS1 hS1 => by
                c0_hfast_nogrp; exact hJS1 () mS1 ⟨extS1, sS1, hS1⟩
          · -- Congruence `!initial`
            intro JC hJC
            refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.delay _ _ _ _ h) hinvL.cfgOk
              hinvL.extOk hinvL.sparse.lengths (fullM6HdrMem_unfocus hmLf)
              fun ⟨delC, ⟨⟩⟩ extCd sCd mCd hcCd hlCd hmsCd hextCd _ hmCd => ?_
            have hinvCd := fullM6HdrInv_with_ext
              (fullM6HdrInv_of_m6Pres hinvL hlCd hcCd hmsCd) hextCd
            have hclCd : sCd.core.cur_level = 0 := by rw [hcCd]; exact hclL
            have hfuCd : sCd.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hcCd]; exact hfuL
            c0_hfast_nogrp
            · exact hJC () mCd ⟨extCd, sCd, hinvCd, hclCd, hfuCd, hmCd⟩
            · refine wp_join_group (ts := [])
                (fun _ mC' => ∃ extC' sC', S5ProbeStateInv c F0 s R extC' sC' mC') ?_ ?_
              · rintro _ _ mC' hC'; try dsimp only [Blocks.get_here]
                c0_hfast_nogrp; exact hJC () mC' hC'
              · intro JC' hJC'
                refine wp_m6Hdr_focus_frame hmCd fun hmCdf => ?_
                c0_call henv.enter
                refine ⟨c, F0, extCd, sCd, R, rfl, hinvCd.cfgOk, hinvCd.extOk,
                  hinvCd.sparse.lengths, hinvCd.sparse.1, hinvCd.sparse.2.1,
                  hinvCd.sparse.2.2.1, hinvCd.sparse.2.2.2.1,
                  (fun hdm => absurd hinvCd.sparse.2.2.2.2 hdm),
                  fullM6HdrMem_unfocus hmCdf,
                  fun okE extE sE mE _ hextE _ hlenE hlmE hndE hesE _ hfuE hdenE hspE hmE => ?_⟩
                have hfuE' := Nat.le_trans hfuE hfuCd
                c0_hfast_nogrp
                · have hdenE' := hdenE ‹okE = true›
                  refine wp_m6Hdr_focus_frame hmE fun hmEf => ?_
                  c0_hfast_nogrp; c0_call henv.cong
                  refine ⟨c, F0, sE, m6ExtMem (m6ExtAddr c.hdr) extE ⋆ R, rfl, hdenE', hmEf,
                    fun rC sC mC hdenC _ hfuC _ huC hmC => ?_⟩
                  have hfuC' := Nat.le_trans (Nat.le_of_eq (congrArg BitVec.toNat hfuC)) hfuE'
                  c0_hfast_nogrp
                  · refine s5_probe_bin_rt henv hdenC (fullM6HdrMem_unfocus hmC)
                      fun sRt mRt hdenRt hfuRt hmRt => ?_
                    c0_call henv.rebNosort
                    refine ⟨c, F0, extE, sRt, R, rfl, hinvL.cfgOk, hextE, hdenRt, hmRt,
                      fun _ extR sR mR hinvR _ hfuR _ _ hmR => ?_⟩
                    exact s5_probe_ret_wm henv hinvR.cfgOk hinvR.extOk hinvR.sparse.lengths
                      (Nat.le_trans hfuR (by rw [hfuRt]; exact hfuC')) (Or.inr rfl)
                      (fun _ => huC ‹_›) (fun h => by cases h) hmR hQ
                  · have hmC' := fullM6HdrMem_unfocus hmC
                    refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
                        M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧
                        sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        (FullM6HdrMem c extDl sDl ⋆ R) mDl) ?_ ?_
                    · rintro _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩
                      try dsimp only [Blocks.get_here]
                      refine s5_probe_bin_rt henv hdenDl hmDl fun sRt mRt hdenRt hfuRt hmRt => ?_
                      exact s5_probe_reb20 henv hinvL.cfgOk hextDl hdenRt
                        (by rw [hfuRt]; exact hfuDl) hmRt hQ
                        (fun _ _ mR hR => hJC' () mR ⟨_, _, hR⟩)
                    · intro JDl hJDl
                      c0_hfast_nogrp
                      refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
                          M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧
                          sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          (FullM6HdrMem c extDl sDl ⋆ R) mDl) ?_ ?_
                      · rintro _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩
                        try dsimp only [Blocks.get_here]
                        refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.bumpD _ _ _ _ h)
                          hinvL.cfgOk hextDl hdenDl.lengths hmDl
                          fun _ extDl' sDl' mDl' hcDl hlDl hmsDl hextDl' _ hmDl' => ?_
                        exact hJDl () mDl' ⟨extDl', sDl', hextDl',
                          fullDenseInv_of_core_eq hdenDl hlDl hcDl hmsDl.extPres,
                          by rw [hcDl]; exact hfuDl, hmDl'⟩
                      · intro JDb hJDb
                        refine wp_m6Hdr_focus_frame hmC' fun hmCf => ?_
                        c0_hfast_nogrp
                        · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.redD _ _ _ _ h)
                            hinvL.cfgOk hextE hdenC.lengths (fullM6HdrMem_unfocus hmCf)
                            fun _ extDl sDl mDl hcDl hlDl hmsDl hextDl _ hmDl => ?_
                          exact hJDl () mDl ⟨extDl, sDl, hextDl,
                            fullDenseInv_of_core_eq hdenC hlDl hcDl hmsDl.extPres,
                            by rw [hcDl]; exact hfuC', hmDl⟩
                        all_goals
                          exact hJDb () mC
                            ⟨extE, sC, hextE, hdenC, hfuC', fullM6HdrMem_unfocus hmCf⟩
                · have hinvE := FullM6HdrInv.mk_inv hinvL.cfgOk hextE (hspE ‹okE = false›).1
                  refine wp_m6Hdr_focus_frame hmE fun hmEf => ?_
                  c0_hfast_nogrp
                  · have hinvE' := s5M6HdrInv_with_probing hinvE s0.core.probing
                    refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => henv.setWm _ _ _ _ h)
                      hinvE'.cfgOk hextE hinvE'.sparse.lengths
                      (fullM6HdrMem_unfocus (by assumption))
                      fun _ ext' s' m' hc' hlen' hms' hext' _ hm' => ?_
                    c0_hfast_nogrp
                    exact hQ 20#64 ext' s' m' hlen' hext' (by rw [hc']; exact hfuE')
                      (Or.inr rfl) (fun _ => fullM6HdrInv_inconsistent_unsat hinvE ‹_›)
                      (fun h => by cases h) hm'
                  · exact hJC' () mE ⟨extE, sE, hinvE, (hspE ‹okE = false›).2, hfuE',
                      fullM6HdrMem_unfocus (by assumption)⟩
        · exact hJbrk (_, ()) mL ⟨extL, sL, hinvL, hclL, hfuL, hmL⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S5
