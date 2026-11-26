/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep9
public import LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof1a
public import LeanQbe.T.Examples.Kissat.FullM7FidelitySchedFixProof
public import LeanQbe.T.Examples.Kissat.FullM7FidelitySearchProof
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 9 Proofs — Top-Level Probing (`FullFidelityStep9ProofProbe`)

M1-clean UNSAT-only parametric `(Γ : Env)` `Func.wp` proof (`public section`, `0` `@[expose]`,
`0` `import all`, `std3`, `XPost`-polymorphic) for Step 9 `full_probe_m6` against
`FullM6Orch.m6ProbeSpec`:
- Separate `initial` vs `!initial` (`while (round < 2ULL)`) stages without `full_probe_tail_m6`,
- Calls `full_rebuild_watches_nosort_fid` after dense congruence/sweep/factor passes, tracking
  `bin_dirty` and calling `full_sort_bin_watches_fid` once on final exit when `bin_dirty` holds.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep9

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullFidelityStep7 (step7SortBinWatchesSpec)
open LeanQbe.T.Examples.Kissat.FullM3Backbone
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullDefSweep (fullSweepDenseSpec)
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM7Search
open Kraken.Bedrock2.Test
open scoped FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6Hdr.M6HdrTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6ProofUtil.M6ProofUtilTactics

@[local bv_c0] private theorem p9_bv64_0 : (0 : BitVec 64).toNat = 0 := rfl
@[local bv_c0] private theorem p9_bv64_1 : (1 : BitVec 64).toNat = 1 := rfl
@[local bv_c0] private theorem p9_bv64_2 : (2 : BitVec 64).toNat = 2 := rfl
@[local bv_c0] private theorem p9_bv64_19 : (19 : BitVec 64).toNat = 19 := rfl

/-! ## 1. Shared Probing Helpers -/

section ProbeHelpersStep9

private theorem s9ProbeRetWm {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s0 s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {r : BitVec 64} {Q : Post [i64]} {X : XPost}
    {args : Tup (Arg Val) [i64, i64, i64]}
    {k : Tup Val [] → Expr Val Cont [i64]}
    (hk_ret : k () = .ret (Arg.imm r, ()))
    (hargs : vals args = (c.hdr, 0#64, BitVec.ofNat 64 s.scratch.search_ticks.toNat, ()) ∨
      vals args = (c.hdr, 0#64, s.scratch.search_ticks, ()))
    (hSetWm : EnvSpec Γ "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] []))
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hfu : s.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hr : r = 1#64 ∨ r = 20#64) (hu : r = 20#64 → F0.Unsat)
    (h1 : r = 1#64 → FullM6HdrInv c F0 ext s ∧ s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' → s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (.call "m6_hdr_set_watermark" (as := [i64, i64, i64]) (bs := []) args k) m := by
  have hargs' : ∃ v, vals args = (c.hdr, 0#64, v, ()) :=
    hargs.elim (fun h => ⟨_, h⟩) (fun h => ⟨_, h⟩)
  obtain ⟨v, hv⟩ := hargs'
  refine m6Hdr_call_m6HdrW2a hv (fun _ _ h => hSetWm _ _ _ _ h) hcfg hext hlen hm
    fun _ ext' s' m' hc' hlen' hms' hext' _ hm' => ?_
  rw [hk_ret]; c0_hsteps_nogrp
  exact hQ ext' s' m' hlen' hext' (by rw [hc']; exact hfu) hr hu
    (fun h => let ⟨hi, hcl⟩ := h1 h
      ⟨fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres hi hlen' hc' hms') hext',
        by rw [hc']; exact hcl⟩) hm'

private theorem s9_scratch_probe_upd_eq (sc : FullScratch) (lim : BitVec 64) :
    ({ sc with probe_limit := lim } : FullScratch) =
      { sc with probe_limit := lim, probings := sc.probings } := by
  cases sc; rfl

private theorem s9_probe_init_call {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {ext0 : List (BitVec 64)} {s s0a : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {parg : BitVec 64}
    {J1 : Cont []}
    (hLog10 : EnvSpec Γ "full_log10_q16_m7" m7Log10Q16Spec)
    (hScaleM5 : EnvSpec Γ "full_scale_delta_m5" FullFastSched.schedScaleDeltaSpec)
    (hinv0a : FullM6HdrInv c F0 ext0 s0a) (hcl0a : s0a.core.cur_level = 0)
    (hfu0a : s0a.core.fuel = s.core.fuel)
    (hm0af : (FullMem c s0a ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) m)
    (hJ1 : ∀ xs m1, (∃ ext1 s1, FullM6HdrInv c F0 ext1 s1 ∧
        s1.core.cur_level = 0 ∧ s1.core.fuel = s.core.fuel ∧
        (FullM6HdrMem c ext1 s1 ⋆ R) m1) → J1 xs m1) :
    wp Γ Q X
      (.call "full_log10_q16_m7" (as := [i64]) (bs := [i64]) (Arg.var parg, ()) fun r =>
        .group (sig := [[i64]]) (fun _Js => Blocks.cons (fun p =>
          .let_ (Op.mk (.mul i64) (Arg.imm 100, Arg.var p.fst, ())) fun p2 =>
          .let_ (Op.mk (.mul i64) (Arg.var p2.fst, Arg.var r.fst, ())) fun p3 =>
          .let_ (Op.mk (.sext 32 64) (Arg.imm 16, ())) fun p4 =>
          .let_ (Op.mk (.lshr i64) (Arg.var p3.fst, Arg.var p4.fst, ())) fun p5 =>
          .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 336, ())) fun p6 =>
          .load i64 (Arg.var p6.fst) fun ld1 =>
          .call "full_scale_delta_m5" (as := [i64, i64]) (bs := [i64])
            (Arg.var c.hdr, Arg.var p5.fst, ()) fun psd =>
          .let_ (Op.mk (.add i64) (Arg.var ld1, Arg.var psd.fst, ())) fun p7 =>
          .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 976, ())) fun p8 =>
          .store (t := i64) (Arg.var p7.fst) (Arg.var p8.fst) (.jump J1 ())) Blocks.nil)
        fun Js =>
        .let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 984, ())) fun p0 =>
        .load i64 (Arg.var p0.fst) fun ld0 =>
        .let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var ld0, Arg.imm 100000000, ())) fun p1 =>
        .jnz (Arg.var p1.fst) (.jump Js.fst (Arg.imm 100000000, ()))
          (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 984, ())) fun p9 =>
           .load i64 (Arg.var p9.fst) fun ld2 => .jump Js.fst (Arg.var ld2, ()))) m := by
  c0_call hLog10
  refine m7Log10Q16Spec_of fun qlog _ _ => ?_
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (_ : Tup Val [i64]) mb =>
      (FullMem c s0a ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) mb)
    (fun _ ⟨pc, ⟨⟩⟩ mb hmb => by
      c0_hsteps_nogrp; c0_call hScaleM5
      refine ⟨c, s0a, m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R, rfl, hinv0a.sparse.lengths, hmb,
        fun sd => ?_⟩
      c0_hsteps_nogrp
      have hst1 := fullState_upd_probe_step hinv0a.sparse.lengths (s0a.scratch.conflicts + sd)
        s0a.scratch.probings
      have hinv1 := fullM6HdrInv_of_probeStep hinv0a hst1
      have hm_lim : (FullMem c { s0a with scratch := { s0a.scratch with
          probe_limit := s0a.scratch.conflicts + sd } } ⋆
          (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) m := by assumption
      rw [s9_scratch_probe_upd_eq] at hm_lim
      exact hJ1 () m ⟨ext0, _, hinv1, hst1.2.1 ▸ hcl0a,
        by rw [hst1.2.1, hfu0a], fullM6HdrMem_unfocus hm_lim⟩)
    (fun _ hJp => by c0_hsteps_nogrp <;> exact hJp (_, ()) _ (by assumption))

end ProbeHelpersStep9

private def s9DummyVal : (t : Ty) → Val t
  | .bits _ => 0 | .bool => true | .float _ => 0 | .pair a b => (s9DummyVal a, s9DummyVal b)

private def s9DummyTup : (ts : List Ty) → Tup Val ts
  | [] => () | t :: ts => (s9DummyVal t, s9DummyTup ts)

private def s9Step {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (ts := ts) _ k => k (s9DummyTup ts)
  | .load t _ k => k (s9DummyVal t)
  | .store _ _ k => k
  | .call (bs := bs) _ _ k => k (s9DummyTup bs)
  | _ => .hlt

private def s9Ld64 {rs : List Ty} (v : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .load (.bits 64) _ k => k v | _ => .hlt

private def s9Call64 {rs : List Ty} (v : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .call (bs := [.bits 64]) _ _ k => k (v, ()) | _ => .hlt

private def s9Grp0 : Expr Val Cont [i64] → Expr Val Cont [i64]
  | .group (sig := [[]]) bs _ =>
    (match bs (fun _ _ => True, ()) with | .cons f .nil => f ())
  | _ => .hlt

private def s9GrpB (b : Val .bool) : Expr Val Cont [i64] → Expr Val Cont [i64]
  | .group (sig := [[.bool]]) bs _ =>
    (match bs (fun _ _ => True, ()) with | .cons f .nil => f (b, ()))
  | _ => .hlt

private def s9ProbeTailExpr (h sv dt : Val i64) (bin_dirty : Val .bool) :
    Expr Val Cont [i64] :=
  full_probe_m6_body Val Cont (h, false, ())
    |> s9Step |> s9Ld64 sv |> s9Call64 dt
    |> s9Step |> s9Step |> s9Step |> s9Step |> s9Step
    |> s9Grp0 |> s9GrpB bin_dirty

private theorem s9_probe_tail_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    (hEnter : EnvSpec Γ "full_enter_dense" FullFastSched.schedEnterDenseSpec)
    (hGetWm : EnvSpec Γ "m6_hdr_get_watermark" (m6HdrW2aSpec [i64] [i64]))
    (hSetWm : EnvSpec Γ "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] []))
    (hFactor : EnvSpec Γ "full_factor" FullBvaHeap.fullFactorHeapSpec)
    (hRebNosort : EnvSpec Γ "full_rebuild_watches_nosort_fid" Full.fullRebuildWatchesSpec)
    (hSortBin : EnvSpec Γ "full_sort_bin_watches_fid" step7SortBinWatchesSpec)
    {c : FullCfg} {F0 : CNF Nat} {extT : List (BitVec 64)} {s sT : FullState}
    (dticks : BitVec 64) (bin_dirty : Bool) {R : Mem 64 → Prop} {mT : Mem 64}
    (hinvT : FullM6HdrInv c F0 extT sT) (hclT : sT.core.cur_level = 0)
    (hfuT : sT.core.fuel.toNat ≤ s.core.fuel.toNat) (hmT : (FullM6HdrMem c extT sT ⋆ R) mT)
    (hQ : ∀ r ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m')
    {e : Expr Val Cont [i64]}
    (he : e = s9ProbeTailExpr c.hdr s.scratch.search_ticks dticks bin_dirty) :
    wp Γ Q X e mT := by
  subst he
  dsimp only [s9ProbeTailExpr, full_probe_m6_body,
    s9Step, s9Ld64, s9Call64, s9Grp0, s9GrpB, s9DummyVal, s9DummyTup]
  refine wp_m6Hdr_focus_frame hmT fun hmTf => by
      c0_hsteps_nogrp
      refine wp_loop_inv (fun (fr, fp, ()) mL => mL = mT ∧ fr.toNat ≤ 19)
        (fun (fr, _, _) _ => 19 - fr.toNat)
        (fun JL hJL => by
          c0_hsteps_nogrp
          exact hJL (1#64, 10#64, ()) mT ⟨rfl, by bv_omega⟩)
        (fun JL (fr, fp, ()) mL ⟨hmL, hfr_le⟩ hJL => ?_)
      · have hmTfl : (FullMem c sT ⋆ (m6ExtMem (m6ExtAddr c.hdr) extT ⋆ R)) mL := hmL ▸ hmTf
        refine wp_join_group (ts := []) (fun _ mEx => mEx = mL) ?_ ?_
        · rintro _ _ mEx hmEx
          have hmTex : (FullMem c sT ⋆ (m6ExtMem (m6ExtAddr c.hdr) extT ⋆ R)) mEx := hmEx ▸ hmTfl
          refine wp_join_group (ts := [i64]) (fun (_ : Tup Val [i64]) ma => ma = mEx) ?_ ?_
          · rintro _ ⟨fe4, ⟨⟩⟩ ma hma
            have hmTfa : (FullMem c sT ⋆ (m6ExtMem (m6ExtAddr c.hdr) extT ⋆ R)) ma := hma ▸ hmTex
            refine wp_join_group (ts := [.bool]) (fun _ mEnd => ∃ extE sE,
                FullM6HdrInv c F0 extE sE ∧ sE.core.cur_level = 0 ∧
                sE.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extE sE ⋆ R) mEnd)
              ?_ ?_
            · rintro _ ⟨bin_dE, ⟨⟩⟩ mEnd ⟨extE, sE, hinvE, hclE, hfuE, hmE⟩
              refine wp_join_group (ts := []) (fun _ mRet => ∃ extRet sRet,
                  FullM6HdrInv c F0 extRet sRet ∧ sRet.core.cur_level = 0 ∧
                  sRet.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                  (FullM6HdrMem c extRet sRet ⋆ R) mRet)
                ?_ ?_
              · rintro _ _ mRet ⟨extRet, sRet, hinvRet, hclRet, hfuRet, hmRet⟩
                refine wp_m6Hdr_focus_frame hmRet fun hmRetf => ?_
                c0_hsteps_nogrp
                let sRet' : FullState :=
                  { sRet with scratch :=
                    { sRet.scratch with search_ticks := s.scratch.search_ticks } }
                have hspRet' : FullSparseInv c F0 sRet' :=
                  FullM3CongBva.fullSparseInv_with_scratch_keep hinvRet.sparse
                    { hinvRet.sparse.lengths.scratch_ok with
                      walk_vals_len := hinvRet.sparse.lengths.scratch_ok.walk_vals_len } rfl rfl
                have hinvRet' := FullM6HdrInv.mk_inv hinvRet.cfgOk hinvRet.extOk hspRet'
                exact s9ProbeRetWm rfl (Or.inr rfl) hSetWm hinvRet'.cfgOk hinvRet'.extOk
                  hinvRet'.sparse.lengths hfuRet (Or.inl rfl) (fun h => by cases h)
                  (fun _ => ⟨hinvRet', hclRet⟩) (fullM6HdrMem_unfocus (by assumption)) (hQ 1#64)
              · intro Jret hJret
                c0_hsteps_nogrp
                · obtain ⟨F_curE, hspWE⟩ := hinvE.sparse.exists_witness
                  c0_call hSortBin
                  refine ⟨c, F0, F_curE, sE, m6ExtMem (m6ExtAddr c.hdr) extE ⋆ R, rfl, hspWE,
                    fullM6HdrMem_focus hmE, fun wstk' m2 _ hsp' _ hm2 => ?_⟩
                  have hinv2 := FullM6HdrInv.mk_inv hinvE.cfgOk hinvE.extOk hsp'.toSparse
                  c0_hsteps_nogrp
                  exact hJret () m2 ⟨extE, _, hinv2, hclE, hfuE, fullM6HdrMem_unfocus hm2⟩
                · exact hJret () mEnd ⟨extE, sE, hinvE, hclE, hfuE, hmE⟩
            · intro Jend hJend
              c0_hsteps_nogrp
              refine wp_join_group (ts := []) (fun _ mInc => ∃ extInc sInc,
                  FullM6HdrInv c F0 extInc sInc ∧ sInc.core.cur_level = 0 ∧
                  sInc.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extInc sInc ⋆ R) mInc)
                ?_ ?_
              · rintro _ _ mInc ⟨extInc, sInc, hinvInc, hclInc, hfuInc, hmInc⟩
                refine wp_m6Hdr_focus_frame hmInc fun hmIncf => ?_
                c0_hsteps_nogrp
                · exact s9ProbeRetWm rfl (Or.inr rfl) hSetWm hinvInc.cfgOk hinvInc.extOk
                    hinvInc.sparse.lengths hfuInc (Or.inr rfl)
                    (fun _ => fullM6HdrInv_inconsistent_unsat hinvInc ‹_›)
                    (fun h => by cases h) (fullM6HdrMem_unfocus hmIncf) (hQ 20#64)
                · exact hJend (bin_dirty, ()) mInc
                    ⟨extInc, sInc, hinvInc, hclInc, hfuInc, fullM6HdrMem_unfocus hmIncf⟩
              · intro Jinc hJinc
                c0_hsteps_nogrp
                · c0_call hEnter
                  refine ⟨c, F0, sT, m6ExtMem (m6ExtAddr c.hdr) extT ⋆ R, rfl, hinvT.sparse,
                    hmTfa, fun ok sF mF hclF hfuF hdenF hspF hmF => ?_⟩
                  have hmF' := fullM6HdrMem_unfocus hmF
                  c0_hsteps_nogrp
                  · have hdenF' := hdenF ‹_›
                    refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hGetWm _ _ _ _ h)
                      hinvT.cfgOk hinvT.extOk hdenF'.lengths hmF'
                      fun ⟨_wm1, ⟨⟩⟩ extF1 sF1 mF1 hcF1 hlF1 hmsF1 hextF1 _ hmF1 => ?_
                    have hdenF1 := fullDenseInv_of_core_eq hdenF' hlF1 hcF1 hmsF1.extPres
                    c0_hsteps_nogrp
                    refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hSetWm _ _ _ _ h)
                      hinvT.cfgOk hextF1 hdenF1.lengths hmF1
                      fun _ extF2 sF2 mF2 hcF2 hlF2 hmsF2 hextF2 _ hmF2 => ?_
                    have hdenF2 := fullDenseInv_of_core_eq hdenF1 hlF2 hcF2 hmsF2.extPres
                    have hmF2f := fullM6HdrMem_focus hmF2
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := [i64]) (fun _ mB => mB = mF2)
                      (fun _ ⟨fbud, ⟨⟩⟩ mB hmB => by
                        subst hmB
                        c0_hsteps_nogrp
                        c0_call hFactor
                        refine ⟨c, F0, sF2, m6ExtMem (m6ExtAddr c.hdr) extF2 ⋆ R, rfl, hdenF2,
                          hmF2f, fun _ sFc mFc hdenFc _ hfuFc _ hmFc => ?_⟩
                        c0_hsteps_nogrp
                        c0_call hRebNosort
                        refine ⟨c, F0, sFc, m6ExtMem (m6ExtAddr c.hdr) extF2 ⋆ R, rfl, hdenFc,
                          hmFc, fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                        have hinvR := FullM6HdrInv.mk_inv hinvT.cfgOk hextF2 hspR
                        have hmR' := fullM6HdrMem_unfocus hmR
                        have hfuR' : sR.core.fuel.toNat ≤ s.core.fuel.toNat := by
                          rw [hfuFc, hcF2, hcF1] at hfuR
                          exact Nat.le_trans hfuR (Nat.le_trans hfuF hfuT)
                        c0_hsteps_nogrp
                        · refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                          c0_hsteps_nogrp
                          exact s9ProbeRetWm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                            hinvR.sparse.lengths hfuR' (Or.inr rfl) (fun _ => huR ‹_›)
                            (fun h => by cases h) (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                        · exact hJend (true, ()) mR ⟨extF2, sR, hinvR, hclR, hfuR', hmR'⟩)
                      (fun _ hJ0 => by c0_hsteps_nogrp <;> exact hJ0 (_, ()) mF2 rfl)
                  · have hinvF := FullM6HdrInv.mk_inv hinvT.cfgOk hinvT.extOk (hspF ‹_›)
                    exact hJinc () mF ⟨extT, sF, hinvF, hclF, Nat.le_trans hfuF hfuT, hmF'⟩
                · exact hJinc () ma ⟨extT, sT, hinvT, hclT, hfuT, fullM6HdrMem_unfocus hmTfa⟩
                · exact hJinc () ma ⟨extT, sT, hinvT, hclT, hfuT, fullM6HdrMem_unfocus hmTfa⟩
          · intro Je hJe; c0_hsteps_nogrp <;> exact hJe (_, ()) mEx rfl
        · intro Jex hJex; c0_hsteps_nogrp
          · have hfr_lt : fr.toNat < 19 := by
              have h := BitVec.lt_def.mp (by assumption : fr < 19#64)
              exact Nat.lt_of_lt_of_eq h (by decide)
            have hfr1 : (fr + 1#64).toNat = fr.toNat + 1 := by c0_bound
            exact hJL (fr + 1#64, _, ()) mL (by dsimp only; omega) ⟨hmL, by omega⟩
          all_goals exact hJex () mL rfl

private theorem full_probe_m6_init_step9_wp (Γ : Env)
    (hProbeDt : EnvSpec Γ "full_probe_dticks_m6_hdr" (m6HdrW2aSpec [.bool] [i64]))
    (hEnter : EnvSpec Γ "full_enter_dense" FullFastSched.schedEnterDenseSpec)
    (hDelay : EnvSpec Γ "m6_hdr_delaying" (m6HdrW2aSpec [i64] [.bool]))
    (hCong : EnvSpec Γ "full_congruence_dense" FullM3CongBva.m3CongruenceDenseSpec)
    (hRebNosort : EnvSpec Γ "full_rebuild_watches_nosort_fid" Full.fullRebuildWatchesSpec)
    (hGetWm : EnvSpec Γ "m6_hdr_get_watermark" (m6HdrW2aSpec [i64] [i64]))
    (hSetWm : EnvSpec Γ "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] []))
    (hRedD : EnvSpec Γ "m6_hdr_reduce_delay" (m6HdrW2aSpec [i64] []))
    (hBumpD : EnvSpec Γ "m6_hdr_bump_delay" (m6HdrW2aSpec [i64] []))
    (hSweepD : EnvSpec Γ "full_sweep_dense_m6" FullDefSweep.fullSweepDenseSpec)
    (hSubst : EnvSpec Γ "full_substitute" Full.fullSubstituteSpec)
    (hBone : EnvSpec Γ "full_backbone_m6" FullM3Backbone.fullBackboneSpec)
    (hFactor : EnvSpec Γ "full_factor" FullBvaHeap.fullFactorHeapSpec)
    (hSortBin : EnvSpec Γ "full_sort_bin_watches_fid" step7SortBinWatchesSpec) :
    ∀ h m Q X, m6ProbeSpec (h, true, ()) m Q X →
      Func.wp Γ fidStep9ProbeM6Fn.body (h, true, ()) m Q X := by
  intro h m Q X hs
  rcases m6ProbeSpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp fidStep9ProbeM6Fn; dsimp only; unfold full_probe_m6_body
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  c0_hsteps_nogrp
  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hProbeDt _ _ _ _ h)
    hinv.cfgOk hinv.extOk hinv.sparse.lengths (fullM6HdrMem_unfocus hmf)
    fun ⟨dticks, ⟨⟩⟩ ext0 s0 m0 hc0 hlen0 hms0 hext0 _ hm0 => ?_
  have hinv0 := fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres hinv hlen0 hc0 hms0) hext0
  have hcl0' : s0.core.cur_level = 0 := by rw [hc0]; exact hcl0
  refine wp_m6Hdr_focus_frame hm0 fun hm0f => ?_
  c0_hsteps_nogrp
  let s0a : FullState :=
    { s0 with scratch := { s0.scratch with probings := s0.scratch.probings + 1#64 } }
  have hst0a := fullState_upd_probe_step hinv0.sparse.lengths s0.scratch.probe_limit
    (s0.scratch.probings + 1#64)
  have hinv0a := fullM6HdrInv_of_probeStep hinv0 hst0a
  have hcl0a : s0a.core.cur_level = 0 := by rw [hst0a.2.1]; exact hcl0'
  have hm0a : (FullM6HdrMem c ext0 s0a ⋆ R) _ := fullM6HdrMem_unfocus (by assumption)
  refine wp_join_group (ts := []) (fun _ m1 => ∃ ext1 s1, FullM6HdrInv c F0 ext1 s1 ∧
      s1.core.cur_level = 0 ∧ s1.core.fuel = s.core.fuel ∧ (FullM6HdrMem c ext1 s1 ⋆ R) m1) ?_ ?_
  · rintro _ _ m1 ⟨ext1, s1, hinv1, hcl1, hfu1, hm1⟩
    clear hm s0a hst0a hinv0a hcl0a hm0a s0 hc0 hlen0 hms0 hext0 hinv0 hcl0' hProbeDt
    c0_hsteps_nogrp
    refine wp_join_group (ts := [.bool]) (fun _ mT => ∃ extT sT, FullM6HdrInv c F0 extT sT ∧
        sT.core.cur_level = 0 ∧ sT.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullM6HdrMem c extT sT ⋆ R) mT) ?_ ?_
    · rintro _ ⟨bin_dirty, ⟨⟩⟩ mT ⟨extT, sT, hinvT, hclT, hfuT, hmT⟩
      refine s9_probe_tail_wp hEnter hGetWm hSetWm hFactor hRebNosort hSortBin
        dticks bin_dirty hinvT hclT hfuT hmT hQ ?_
      dsimp only [s9ProbeTailExpr, full_probe_m6_body,
        s9Step, s9Ld64, s9Call64, s9Grp0, s9GrpB, s9DummyVal, s9DummyTup]
      rfl
    · intro JT hJT
      clear hGetWm hFactor hSortBin
      c0_hsteps_nogrp
      · -- Branch 1: `initial = true` (`cong/nosort/subst -> bb -> sweep/nosort/subst`)
        refine wp_join_group (ts := [.bool, .bool]) (fun _ mC1 => ∃ extC1 sC1,
            FullM6HdrInv c F0 extC1 sC1 ∧ sC1.core.cur_level = 0 ∧
            sC1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extC1 sC1 ⋆ R) mC1) ?_ ?_
        · rintro _ ⟨bin_d1, subst_end1, ⟨⟩⟩ mC1 ⟨extC1, sC1, hinvC1, hclC1, hfuC1, hmC1⟩
          refine wp_join_group (ts := []) (fun _ mB1 => ∃ extB1 sB1,
              FullM6HdrInv c F0 extB1 sB1 ∧ sB1.core.cur_level = 0 ∧
              sB1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extB1 sB1 ⋆ R) mB1) ?_ ?_
          · rintro _ _ mB1 ⟨extB1, sB1, hinvB1, hclB1, hfuB1, hmB1⟩
            refine wp_join_group (ts := [.bool, .bool]) (fun _ mS1 => ∃ extS1 sS1,
                FullM6HdrInv c F0 extS1 sS1 ∧ sS1.core.cur_level = 0 ∧
                sS1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extS1 sS1 ⋆ R) mS1)
              ?_ ?_
            · rintro _ ⟨bin_d2, subst_end2, ⟨⟩⟩ mS1 ⟨extS1, sS1, hinvS1, hclS1, hfuS1, hmS1⟩
              refine wp_m6Hdr_focus_frame hmS1 fun hmS1f => ?_
              c0_hsteps_nogrp
              · c0_call hSubst
                refine ⟨c, F0, sS1, m6ExtMem (m6ExtAddr c.hdr) extS1 ⋆ R, rfl, hinvS1.sparse,
                  hmS1f, fun rSu sSu mSu hspSu hclSu hfuSu _ huSu hmSu => ?_⟩
                have hinvSu := FullM6HdrInv.mk_inv hinvS1.cfgOk hinvS1.extOk hspSu
                have hmSu' := fullM6HdrMem_unfocus hmSu
                have hfuSu' := Nat.le_trans hfuSu hfuS1
                c0_hsteps_nogrp
                · refine wp_m6Hdr_focus_frame hmSu' fun hmSuf => ?_
                  c0_hsteps_nogrp
                  exact s9ProbeRetWm rfl (Or.inr rfl) hSetWm hinvSu.cfgOk hinvSu.extOk
                    hinvSu.sparse.lengths hfuSu' (Or.inr rfl) (fun _ => huSu ‹_›)
                    (fun h => by cases h) (fullM6HdrMem_unfocus hmSuf) (hQ 20#64)
                · exact hJT (bin_d2, ()) mSu ⟨extS1, sSu, hinvSu, hclSu, hfuSu', hmSu'⟩
              · exact hJT (bin_d2, ()) mS1
                  ⟨extS1, sS1, hinvS1, hclS1, hfuS1, fullM6HdrMem_unfocus hmS1f⟩
              · exact hJT (bin_d2, ()) mS1
                  ⟨extS1, sS1, hinvS1, hclS1, hfuS1, fullM6HdrMem_unfocus hmS1f⟩
            · -- Initial `M6_DELAY_SWEEP` block
              intro JS1 hJS1
              refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hDelay _ _ _ _ h)
                hinvB1.cfgOk hinvB1.extOk hinvB1.sparse.lengths hmB1
                fun ⟨delS, ⟨⟩⟩ extSd sSd mSd hcSd hlSd hmsSd hextSd _ hmSd => ?_
              have hinvSd := fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres hinvB1 hlSd hcSd hmsSd)
                hextSd
              have hclSd : sSd.core.cur_level = 0 := by rw [hcSd]; exact hclB1
              have hfuSd : sSd.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hcSd]; exact hfuB1
              c0_hsteps_nogrp
              · exact hJS1 (bin_d1, subst_end1, ()) mSd ⟨extSd, sSd, hinvSd, hclSd, hfuSd, hmSd⟩
              · refine wp_join_group (ts := [.bool, .bool]) (fun _ mW => ∃ extW sW,
                    FullM6HdrInv c F0 extW sW ∧ sW.core.cur_level = 0 ∧
                    sW.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extW sW ⋆ R) mW)
                  (fun _ p mp hp => by
                    dsimp only [Blocks.get_here, Blocks.get_there]; exact hJS1 p mp hp) ?_
                intro JS1' hJS1'
                refine wp_m6Hdr_focus_frame hmSd fun hmSdf => ?_
                c0_hsteps_nogrp
                · c0_call hEnter
                  refine ⟨c, F0, sSd, m6ExtMem (m6ExtAddr c.hdr) extSd ⋆ R, rfl,
                    hinvSd.sparse, hmSdf, fun okE sE mE hclE hfuE hdenE hspE hmE => ?_⟩
                  have hmE' := fullM6HdrMem_unfocus hmE
                  have hfuE' := Nat.le_trans hfuE hfuSd
                  c0_hsteps_nogrp
                  · have hdenE' := hdenE ‹_›
                    refine wp_m6Hdr_focus_frame hmE' fun hmEf => ?_
                    c0_hsteps_nogrp; c0_call hSweepD
                    refine ⟨c, F0, sE, m6ExtMem (m6ExtAddr c.hdr) extSd ⋆ R, rfl, hdenE', hmEf,
                      fun rSw sSw mSw hdenSw _ hfuSw _ huSw hmSw => ?_⟩
                    have hfuSw' := Nat.le_trans hfuSw hfuE'
                    c0_hsteps_nogrp
                    · c0_call hRebNosort
                      refine ⟨c, F0, sSw, m6ExtMem (m6ExtAddr c.hdr) extSd ⋆ R, rfl, hdenSw, hmSw,
                        fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                      have hinvR := FullM6HdrInv.mk_inv hinvB1.cfgOk hextSd hspR
                      have hmR' := fullM6HdrMem_unfocus hmR
                      refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                      c0_hsteps_nogrp
                      exact s9ProbeRetWm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hextSd
                        hinvR.sparse.lengths (Nat.le_trans hfuR hfuSw') (Or.inr rfl)
                        (fun _ => huSw ‹_›) (fun h => by cases h) (fullM6HdrMem_unfocus hmRf)
                        (hQ 20#64)
                    · have hmSw' := fullM6HdrMem_unfocus hmSw
                      refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
                          M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧
                          sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          (FullM6HdrMem c extDl sDl ⋆ R) mDl) ?_ ?_
                      · rintro _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩
                        refine wp_m6Hdr_focus_frame hmDl fun hmDlf => ?_
                        c0_hsteps_nogrp
                        · c0_call hRebNosort
                          refine ⟨c, F0, sDl, m6ExtMem (m6ExtAddr c.hdr) extDl ⋆ R, rfl, hdenDl,
                            hmDlf, fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                          have hinvR := FullM6HdrInv.mk_inv hinvB1.cfgOk hextDl hspR
                          have hmR' := fullM6HdrMem_unfocus hmR
                          have hfuR' := Nat.le_trans hfuR hfuDl
                          c0_hsteps_nogrp
                          · refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                            c0_hsteps_nogrp
                            exact s9ProbeRetWm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hextDl
                              hinvR.sparse.lengths hfuR' (Or.inr rfl) (fun _ => huR ‹_›)
                              (fun h => by cases h) (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                          · refine wp_join_group (ts := [.bool]) (fun _ mW => ∃ extW sW,
                                FullM6HdrInv c F0 extW sW ∧ sW.core.cur_level = 0 ∧
                                sW.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                (FullM6HdrMem c extW sW ⋆ R) mW)
                              (fun _ p mp hp => by
                                dsimp only [Blocks.get_here, Blocks.get_there]
                                exact hJS1' (true, p.1, ()) mp hp) ?_
                            intro JSe hJSe
                            refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                            c0_hsteps_nogrp
                            · c0_call hSubst
                              refine ⟨c, F0, sR, m6ExtMem (m6ExtAddr c.hdr) extDl ⋆ R, rfl,
                                hinvR.sparse, hmRf, fun rSu sSu mSu hspSu hclSu hfuSu _ huSu hmSu =>
                                  ?_⟩
                              have hinvSu := FullM6HdrInv.mk_inv hinvR.cfgOk hextDl hspSu
                              have hmSu' := fullM6HdrMem_unfocus hmSu
                              have hfuSu' := Nat.le_trans hfuSu hfuR'
                              c0_hsteps_nogrp
                              · refine wp_m6Hdr_focus_frame hmSu' fun hmSuf => ?_
                                c0_hsteps_nogrp
                                exact s9ProbeRetWm rfl (Or.inr rfl) hSetWm hinvSu.cfgOk hextDl
                                  hinvSu.sparse.lengths hfuSu' (Or.inr rfl) (fun _ => huSu ‹_›)
                                  (fun h => by cases h) (fullM6HdrMem_unfocus hmSuf) (hQ 20#64)
                              · exact hJSe (false, ()) mSu
                                  ⟨extDl, sSu, hinvSu, hclSu, hfuSu', hmSu'⟩
                            · exact hJSe (false, ()) mR
                                ⟨extDl, sR, hinvR, hclR, hfuR', fullM6HdrMem_unfocus hmRf⟩
                            · exact hJSe (subst_end1, ()) mR
                                ⟨extDl, sR, hinvR, hclR, hfuR', fullM6HdrMem_unfocus hmRf⟩
                      · intro JDl hJDl
                        c0_hsteps_nogrp
                        refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
                            M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧
                            sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                            (FullM6HdrMem c extDl sDl ⋆ R) mDl)
                          (fun _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩ => by
                            refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hBumpD _ _ _ _ h)
                              hinvB1.cfgOk hextDl hdenDl.lengths hmDl
                              fun _ extDl' sDl' mDl' hcDl hlDl hmsDl hextDl' _ hmDl' => ?_
                            exact hJDl () mDl' ⟨extDl', sDl', hextDl',
                              fullDenseInv_of_core_eq hdenDl hlDl hcDl hmsDl.extPres,
                              by rw [hcDl]; exact hfuDl, hmDl'⟩) ?_
                        intro JDb hJDb
                        refine wp_m6Hdr_focus_frame hmSw' fun hmSwf => ?_
                        c0_hsteps_nogrp
                        · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hRedD _ _ _ _ h)
                            hinvB1.cfgOk hextSd hdenSw.lengths (fullM6HdrMem_unfocus hmSwf)
                            fun _ extDl sDl mDl hcDl hlDl hmsDl hextDl _ hmDl => ?_
                          exact hJDl () mDl ⟨extDl, sDl, hextDl,
                            fullDenseInv_of_core_eq hdenSw hlDl hcDl hmsDl.extPres,
                            by rw [hcDl]; exact hfuSw', hmDl⟩
                        · exact hJDb () mSw ⟨extSd, sSw, hextSd, hdenSw, hfuSw',
                            fullM6HdrMem_unfocus hmSwf⟩
                        · exact hJDb () mSw ⟨extSd, sSw, hextSd, hdenSw, hfuSw',
                            fullM6HdrMem_unfocus hmSwf⟩
                  · have hinvE := FullM6HdrInv.mk_inv hinvB1.cfgOk hextSd (hspE ‹_›)
                    refine wp_m6Hdr_focus_frame hmE' fun hmEf => ?_
                    c0_hsteps_nogrp
                    exact s9ProbeRetWm rfl (Or.inr rfl) hSetWm hinvE.cfgOk hextSd
                      hinvE.sparse.lengths hfuE' (Or.inr rfl)
                      (fun _ => fullM6HdrInv_inconsistent_unsat hinvE ‹_›)
                      (fun h => by cases h) (fullM6HdrMem_unfocus hmEf) (hQ 20#64)
                  · have hinvE := FullM6HdrInv.mk_inv hinvB1.cfgOk hextSd (hspE ‹_›)
                    exact hJS1' (bin_d1, subst_end1, ()) mE
                      ⟨extSd, sE, hinvE, hclE, hfuE', hmE'⟩
          · -- Initial `full_backbone_m6`
            intro JB1 hJB1
            refine wp_m6Hdr_focus_frame hmC1 fun hmC1f => ?_
            c0_hsteps_nogrp
            · c0_call hBone
              refine ⟨c, F0, sC1, m6ExtMem (m6ExtAddr c.hdr) extC1 ⋆ R, rfl, hinvC1.sparse,
                hmC1f, fun rB sB mB hspB hclB _ hfuB _ huB hmB => ?_⟩
              have hinvB := FullM6HdrInv.mk_inv hinvC1.cfgOk hinvC1.extOk hspB
              have hmB' := fullM6HdrMem_unfocus hmB
              have hfuB' := Nat.le_trans hfuB hfuC1
              c0_hsteps_nogrp
              · refine wp_m6Hdr_focus_frame hmB' fun hmBf => ?_
                c0_hsteps_nogrp
                exact s9ProbeRetWm rfl (Or.inr rfl) hSetWm hinvB.cfgOk hinvB.extOk
                  hinvB.sparse.lengths hfuB' (Or.inr rfl) (fun _ => huB ‹_›)
                  (fun h => by cases h) (fullM6HdrMem_unfocus hmBf) (hQ 20#64)
              · exact hJB1 () mB ⟨extC1, sB, hinvB, hclB, hfuB', hmB'⟩
            · exact hJB1 () mC1 ⟨extC1, sC1, hinvC1, hclC1, hfuC1, fullM6HdrMem_unfocus hmC1f⟩
        · -- Initial `M6_DELAY_CONGRUENCE` block
          intro JC1 hJC1
          refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hDelay _ _ _ _ h)
            hinv1.cfgOk hinv1.extOk hinv1.sparse.lengths hm1
            fun ⟨delC, ⟨⟩⟩ extCd sCd mCd hcCd hlCd hmsCd hextCd _ hmCd => ?_
          have hinvCd := fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres hinv1 hlCd hcCd hmsCd)
            hextCd
          have hclCd : sCd.core.cur_level = 0 := by rw [hcCd]; exact hcl1
          have hfuCd : sCd.core.fuel.toNat ≤ s.core.fuel.toNat := by
            rw [hcCd, hfu1]; exact Nat.le_refl _
          c0_hsteps_nogrp
          · exact hJC1 (false, true, ()) mCd ⟨extCd, sCd, hinvCd, hclCd, hfuCd, hmCd⟩
          · refine wp_join_group (ts := [.bool, .bool]) (fun _ mW => ∃ extW sW,
                FullM6HdrInv c F0 extW sW ∧ sW.core.cur_level = 0 ∧
                sW.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extW sW ⋆ R) mW)
              (fun _ p mp hp => by
                dsimp only [Blocks.get_here, Blocks.get_there]; exact hJC1 p mp hp) ?_
            intro JC1' hJC1'
            refine wp_m6Hdr_focus_frame hmCd fun hmCdf => ?_
            c0_hsteps_nogrp
            · c0_call hEnter
              refine ⟨c, F0, sCd, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl, hinvCd.sparse, hmCdf,
                fun okE sE mE hclE hfuE hdenE hspE hmE => ?_⟩
              have hmE' := fullM6HdrMem_unfocus hmE
              have hfuE' := Nat.le_trans hfuE hfuCd
              c0_hsteps_nogrp
              · have hdenE' := hdenE ‹_›
                refine wp_m6Hdr_focus_frame hmE' fun hmEf => ?_
                c0_hsteps_nogrp; c0_call hCong
                refine ⟨c, F0, sE, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl, hdenE', hmEf,
                  fun rC sC mC hdenC _ hfuC _ huC hmC => ?_⟩
                have hfuC' := Nat.le_trans (Nat.le_of_eq (congrArg BitVec.toNat hfuC)) hfuE'
                c0_hsteps_nogrp
                · c0_call hRebNosort
                  refine ⟨c, F0, sC, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl, hdenC, hmC,
                    fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                  have hinvR := FullM6HdrInv.mk_inv hinv1.cfgOk hextCd hspR
                  have hmR' := fullM6HdrMem_unfocus hmR
                  refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                  c0_hsteps_nogrp
                  exact s9ProbeRetWm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hextCd
                    hinvR.sparse.lengths (Nat.le_trans hfuR hfuC') (Or.inr rfl)
                    (fun _ => huC ‹_›) (fun h => by cases h) (fullM6HdrMem_unfocus hmRf)
                    (hQ 20#64)
                · have hmC' := fullM6HdrMem_unfocus hmC
                  refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
                      M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧
                      sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                      (FullM6HdrMem c extDl sDl ⋆ R) mDl) ?_ ?_
                  · rintro _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩
                    refine wp_m6Hdr_focus_frame hmDl fun hmDlf => ?_
                    c0_hsteps_nogrp
                    · c0_call hRebNosort
                      refine ⟨c, F0, sDl, m6ExtMem (m6ExtAddr c.hdr) extDl ⋆ R, rfl, hdenDl,
                        hmDlf, fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                      have hinvR := FullM6HdrInv.mk_inv hinv1.cfgOk hextDl hspR
                      have hmR' := fullM6HdrMem_unfocus hmR
                      have hfuR' := Nat.le_trans hfuR hfuDl
                      c0_hsteps_nogrp
                      · refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                        c0_hsteps_nogrp
                        exact s9ProbeRetWm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hextDl
                          hinvR.sparse.lengths hfuR' (Or.inr rfl) (fun _ => huR ‹_›)
                          (fun h => by cases h) (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                      · refine wp_join_group (ts := [.bool]) (fun _ mW => ∃ extW sW,
                            FullM6HdrInv c F0 extW sW ∧ sW.core.cur_level = 0 ∧
                            sW.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                            (FullM6HdrMem c extW sW ⋆ R) mW)
                          (fun _ p mp hp => by
                            dsimp only [Blocks.get_here, Blocks.get_there]
                            exact hJC1' (true, p.1, ()) mp hp) ?_
                        intro JCe hJCe
                        refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                        c0_hsteps_nogrp
                        · c0_call hSubst
                          refine ⟨c, F0, sR, m6ExtMem (m6ExtAddr c.hdr) extDl ⋆ R, rfl,
                            hinvR.sparse, hmRf, fun rSu sSu mSu hspSu hclSu hfuSu _ huSu hmSu =>
                              ?_⟩
                          have hinvSu := FullM6HdrInv.mk_inv hinvR.cfgOk hextDl hspSu
                          have hmSu' := fullM6HdrMem_unfocus hmSu
                          have hfuSu' := Nat.le_trans hfuSu hfuR'
                          c0_hsteps_nogrp
                          · refine wp_m6Hdr_focus_frame hmSu' fun hmSuf => ?_
                            c0_hsteps_nogrp
                            exact s9ProbeRetWm rfl (Or.inr rfl) hSetWm hinvSu.cfgOk hextDl
                              hinvSu.sparse.lengths hfuSu' (Or.inr rfl) (fun _ => huSu ‹_›)
                              (fun h => by cases h) (fullM6HdrMem_unfocus hmSuf) (hQ 20#64)
                          · exact hJCe (false, ()) mSu
                              ⟨extDl, sSu, hinvSu, hclSu, hfuSu', hmSu'⟩
                        · exact hJCe (false, ()) mR
                            ⟨extDl, sR, hinvR, hclR, hfuR', fullM6HdrMem_unfocus hmRf⟩
                        · exact hJCe (true, ()) mR
                            ⟨extDl, sR, hinvR, hclR, hfuR', fullM6HdrMem_unfocus hmRf⟩
                  · intro JDl hJDl
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
                        M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧
                        sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        (FullM6HdrMem c extDl sDl ⋆ R) mDl)
                      (fun _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩ => by
                        refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hBumpD _ _ _ _ h)
                          hinv1.cfgOk hextDl hdenDl.lengths hmDl
                          fun _ extDl' sDl' mDl' hcDl hlDl hmsDl hextDl' _ hmDl' => ?_
                        exact hJDl () mDl' ⟨extDl', sDl', hextDl',
                          fullDenseInv_of_core_eq hdenDl hlDl hcDl hmsDl.extPres,
                          by rw [hcDl]; exact hfuDl, hmDl'⟩) ?_
                    intro JDb hJDb
                    refine wp_m6Hdr_focus_frame hmC' fun hmCf => ?_
                    c0_hsteps_nogrp
                    · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hRedD _ _ _ _ h)
                        hinv1.cfgOk hextCd hdenC.lengths (fullM6HdrMem_unfocus hmCf)
                        fun _ extDl sDl mDl hcDl hlDl hmsDl hextDl _ hmDl => ?_
                      exact hJDl () mDl ⟨extDl, sDl, hextDl,
                        fullDenseInv_of_core_eq hdenC hlDl hcDl hmsDl.extPres,
                        by rw [hcDl]; exact hfuC', hmDl⟩
                    · exact hJDb () mC ⟨extCd, sC, hextCd, hdenC, hfuC', fullM6HdrMem_unfocus hmCf⟩
                    · exact hJDb () mC ⟨extCd, sC, hextCd, hdenC, hfuC', fullM6HdrMem_unfocus hmCf⟩
              · have hinvE := FullM6HdrInv.mk_inv hinv1.cfgOk hextCd (hspE ‹_›)
                refine wp_m6Hdr_focus_frame hmE' fun hmEf => ?_
                c0_hsteps_nogrp
                exact s9ProbeRetWm rfl (Or.inr rfl) hSetWm hinvE.cfgOk hextCd
                  hinvE.sparse.lengths hfuE' (Or.inr rfl)
                  (fun _ => fullM6HdrInv_inconsistent_unsat hinvE ‹_›)
                  (fun h => by cases h) (fullM6HdrMem_unfocus hmEf) (hQ 20#64)
              · have hinvE := FullM6HdrInv.mk_inv hinv1.cfgOk hextCd (hspE ‹_›)
                exact hJC1' (false, true, ()) mE ⟨extCd, sE, hinvE, hclE, hfuE', hmE'⟩
      · exact absurd hc (by decide)
  · intro J1 hJ1; c0_hsteps_nogrp
    · exact hJ1 () _ ⟨ext0, s0a, hinv0a, hcl0a, by rw [hst0a.2.1, hc0], hm0a⟩
    · exact absurd hc (by decide)

private theorem full_probe_m6_inproc_step9_wp (Γ : Env)
    (hProbeDt : EnvSpec Γ "full_probe_dticks_m6_hdr" (m6HdrW2aSpec [.bool] [i64]))
    (hLog10 : EnvSpec Γ "full_log10_q16_m7" m7Log10Q16Spec)
    (hScaleM5 : EnvSpec Γ "full_scale_delta_m5" FullFastSched.schedScaleDeltaSpec)
    (hViv : EnvSpec Γ "full_vivify_m6_hdr" m6aVivifySpec)
    (hEnter : EnvSpec Γ "full_enter_dense" FullFastSched.schedEnterDenseSpec)
    (hDelay : EnvSpec Γ "m6_hdr_delaying" (m6HdrW2aSpec [i64] [.bool]))
    (hCong : EnvSpec Γ "full_congruence_dense" FullM3CongBva.m3CongruenceDenseSpec)
    (hRebNosort : EnvSpec Γ "full_rebuild_watches_nosort_fid" Full.fullRebuildWatchesSpec)
    (hGetWm : EnvSpec Γ "m6_hdr_get_watermark" (m6HdrW2aSpec [i64] [i64]))
    (hSetWm : EnvSpec Γ "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] []))
    (hRedD : EnvSpec Γ "m6_hdr_reduce_delay" (m6HdrW2aSpec [i64] []))
    (hBumpD : EnvSpec Γ "m6_hdr_bump_delay" (m6HdrW2aSpec [i64] []))
    (hSweepD : EnvSpec Γ "full_sweep_dense_m6" FullDefSweep.fullSweepDenseSpec)
    (hSubst : EnvSpec Γ "full_substitute" Full.fullSubstituteSpec)
    (hBone : EnvSpec Γ "full_backbone_m6" FullM3Backbone.fullBackboneSpec)
    (hTrans : EnvSpec Γ "full_transitive_m6" FullFastBveBudgets.fullTransitiveFastSpec)
    (hFactor : EnvSpec Γ "full_factor" FullBvaHeap.fullFactorHeapSpec)
    (hSortBin : EnvSpec Γ "full_sort_bin_watches_fid" step7SortBinWatchesSpec) :
    ∀ h m Q X, m6ProbeSpec (h, false, ()) m Q X →
      Func.wp Γ fidStep9ProbeM6Fn.body (h, false, ()) m Q X := by
  intro h m Q X hs
  rcases m6ProbeSpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp fidStep9ProbeM6Fn; dsimp only; unfold full_probe_m6_body
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  c0_hsteps_nogrp
  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hProbeDt _ _ _ _ h)
    hinv.cfgOk hinv.extOk hinv.sparse.lengths (fullM6HdrMem_unfocus hmf)
    fun ⟨dticks, ⟨⟩⟩ ext0 s0 m0 hc0 hlen0 hms0 hext0 _ hm0 => ?_
  have hinv0 := fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres hinv hlen0 hc0 hms0) hext0
  have hcl0' : s0.core.cur_level = 0 := by rw [hc0]; exact hcl0
  refine wp_m6Hdr_focus_frame hm0 fun hm0f => ?_
  c0_hsteps_nogrp
  let s0a : FullState :=
    { s0 with scratch := { s0.scratch with probings := s0.scratch.probings + 1#64 } }
  have hst0a := fullState_upd_probe_step hinv0.sparse.lengths s0.scratch.probe_limit
    (s0.scratch.probings + 1#64)
  have hinv0a := fullM6HdrInv_of_probeStep hinv0 hst0a
  have hcl0a : s0a.core.cur_level = 0 := by rw [hst0a.2.1]; exact hcl0'
  have hm0a : (FullM6HdrMem c ext0 s0a ⋆ R) _ := fullM6HdrMem_unfocus (by assumption)
  refine wp_join_group (ts := []) (fun _ m1 => ∃ ext1 s1, FullM6HdrInv c F0 ext1 s1 ∧
      s1.core.cur_level = 0 ∧ s1.core.fuel = s.core.fuel ∧ (FullM6HdrMem c ext1 s1 ⋆ R) m1) ?_ ?_
  · rintro _ _ m1 ⟨ext1, s1, hinv1, hcl1, hfu1, hm1⟩
    clear hm s0a hst0a hinv0a hcl0a hm0a s0 hc0 hlen0 hms0 hext0 hinv0 hcl0' hProbeDt
    c0_hsteps_nogrp
    refine wp_join_group (ts := [.bool]) (fun _ mT => ∃ extT sT, FullM6HdrInv c F0 extT sT ∧
        sT.core.cur_level = 0 ∧ sT.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullM6HdrMem c extT sT ⋆ R) mT) ?_ ?_
    · rintro _ ⟨bin_dirty, ⟨⟩⟩ mT ⟨extT, sT, hinvT, hclT, hfuT, hmT⟩
      refine s9_probe_tail_wp hEnter hGetWm hSetWm hFactor hRebNosort hSortBin
        dticks bin_dirty hinvT hclT hfuT hmT hQ ?_
      dsimp only [s9ProbeTailExpr, full_probe_m6_body,
        s9Step, s9Ld64, s9Call64, s9Grp0, s9GrpB, s9DummyVal, s9DummyTup]
      rfl
    · intro JT hJT
      clear hGetWm hFactor hSortBin
      c0_hsteps_nogrp
      · -- Branch 2: `!initial` (`while (round < 2ULL)`)
        c0_hsteps_nogrp
        refine wp_join_group (ts := [.bool, i64]) (fun (bin_b, _rnd, ()) mB => ∃ extB sB,
            FullM6HdrInv c F0 extB sB ∧ sB.core.cur_level = 0 ∧
            sB.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extB sB ⋆ R) mB)
          (fun _ (bin_b, _rnd, ()) mB ⟨extB, sB, hinvB, hclB, hfuB, hmB⟩ =>
            hJT (bin_b, ()) mB ⟨extB, sB, hinvB, hclB, hfuB, hmB⟩) ?_
        intro Jbrk hJbrk
        c0_hsteps_nogrp
        refine wp_loop_inv (fun (bin_dL, round, ()) mL => round.toNat ≤ 2 ∧
            ∃ extL sL, FullM6HdrInv c F0 extL sL ∧ sL.core.cur_level = 0 ∧
              sL.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extL sL ⋆ R) mL)
          (fun (_bin, round, ()) _ => 2 - round.toNat)
          (fun JL hJL => by
            c0_hsteps_nogrp
            exact hJL (false, 0#64, ()) m1
              ⟨Nat.zero_le _, ext1, s1, hinv1, hcl1, by rw [hfu1]; exact Nat.le_refl _, hm1⟩)
          (fun JL (bin_dL, round, ()) mL ⟨hnd_le, extL, sL, hinvL, hclL, hfuL, hmL⟩ hJL => ?_)
        · c0_hsteps_nogrp
          · have hnd_lt : round.toNat < 2 := by
              have h := BitVec.lt_def.mp (by assumption : round < 2#64)
              exact Nat.lt_of_lt_of_eq h (by decide)
            have hnd1 : (round + 1#64).toNat = round.toNat + 1 := by c0_bound
            let before_unass := sL.core.unassigned
            refine wp_m6Hdr_focus_frame hmL fun hmLf => ?_
            c0_hsteps_nogrp
            have hmL' := fullM6HdrMem_unfocus hmLf
            refine wp_join_group (ts := [.bool]) (fun _ mC => ∃ extC sC,
                FullM6HdrInv c F0 extC sC ∧ sC.core.cur_level = 0 ∧
                sC.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extC sC ⋆ R) mC) ?_ ?_
            · rintro _ ⟨bin_dC, ⟨⟩⟩ mC ⟨extC, sC, hinvC, hclC, hfuC, hmC⟩
              refine wp_join_group (ts := []) (fun _ mS1 => ∃ extS1 sS1,
                  FullM6HdrInv c F0 extS1 sS1 ∧ sS1.core.cur_level = 0 ∧
                  sS1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extS1 sS1 ⋆ R) mS1)
                ?_ ?_
              · rintro _ _ mS1 ⟨extS1, sS1, hinvS1, hclS1, hfuS1, hmS1⟩
                refine wp_join_group (ts := []) (fun _ mB1 => ∃ extB1 sB1,
                    FullM6HdrInv c F0 extB1 sB1 ∧ sB1.core.cur_level = 0 ∧
                    sB1.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                    (FullM6HdrMem c extB1 sB1 ⋆ R) mB1) ?_ ?_
                · rintro _ _ mB1 ⟨extB1, sB1, hinvB1, hclB1, hfuB1, hmB1⟩
                  dsimp only [Blocks.get_here, Blocks.get_there]
                  c0_call hViv
                  refine m6aVivifySpec_of hinvB1.cfgOk hinvB1.extOk hinvB1.sparse hmB1
                    fun rV extV sV mV ⟨hextV, _⟩ hspV ⟨hclV, _⟩ hfuV _ huV hmV => ?_
                  have hinvV := FullM6HdrInv.mk_inv hinvB1.cfgOk hextV hspV
                  have hfuV' := Nat.le_trans hfuV hfuB1
                  c0_hsteps_nogrp
                  · refine wp_m6Hdr_focus_frame hmV fun hmVf => ?_
                    c0_hsteps_nogrp
                    exact s9ProbeRetWm rfl (Or.inr rfl) hSetWm hinvV.cfgOk hextV
                      hinvV.sparse.lengths hfuV' (Or.inr rfl) (fun _ => huV ‹_›)
                      (fun h => by cases h) (fullM6HdrMem_unfocus hmVf) (hQ 20#64)
                  · refine wp_join_group (ts := [.bool]) (fun _ mSw => ∃ extSw sSw,
                        FullM6HdrInv c F0 extSw sSw ∧ sSw.core.cur_level = 0 ∧
                        sSw.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        (FullM6HdrMem c extSw sSw ⋆ R) mSw) ?_ ?_
                    · rintro _ ⟨bin_dSw, ⟨⟩⟩ mSw ⟨extSw, sSw, hinvSw, hclSw, hfuSw, hmSw⟩
                      dsimp only [Blocks.get_here, Blocks.get_there]
                      refine wp_join_group (ts := []) (fun _ mS2 => ∃ extS2 sS2,
                          FullM6HdrInv c F0 extS2 sS2 ∧ sS2.core.cur_level = 0 ∧
                          sS2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          (FullM6HdrMem c extS2 sS2 ⋆ R) mS2) ?_ ?_
                      · rintro _ _ mS2 ⟨extS2, sS2, hinvS2, hclS2, hfuS2, hmS2⟩
                        dsimp only [Blocks.get_here, Blocks.get_there]; c0_hsteps_nogrp
                        refine wp_join_group (ts := []) (fun _ mTr => ∃ extTr sTr,
                            FullM6HdrInv c F0 extTr sTr ∧ sTr.core.cur_level = 0 ∧
                            sTr.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                            (FullM6HdrMem c extTr sTr ⋆ R) mTr) ?_ ?_
                        · rintro _ _ mTr ⟨extTr, sTr, hinvTr, hclTr, hfuTr, hmTr⟩
                          dsimp only [Blocks.get_here, Blocks.get_there]; c0_hsteps_nogrp
                          refine wp_join_group (ts := []) (fun _ mB2 => ∃ extB2 sB2,
                              FullM6HdrInv c F0 extB2 sB2 ∧ sB2.core.cur_level = 0 ∧
                              sB2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                              (FullM6HdrMem c extB2 sB2 ⋆ R) mB2) ?_ ?_
                          · rintro _ _ mB2 ⟨extB2, sB2, hinvB2, hclB2, hfuB2, hmB2⟩
                            refine wp_m6Hdr_focus_frame hmB2 fun hmB2f => ?_
                            c0_hsteps_nogrp
                            · exact hJbrk (bin_dSw, round, ()) mB2
                                ⟨extB2, sB2, hinvB2, hclB2, hfuB2, fullM6HdrMem_unfocus hmB2f⟩
                            · exact hJL (bin_dSw, round + 1#64, ()) mB2 (by dsimp only; omega)
                                ⟨by omega, extB2, sB2, hinvB2, hclB2, hfuB2,
                                  fullM6HdrMem_unfocus hmB2f⟩
                          · -- Inproc `full_backbone_m6` #2
                            intro JB2 hJB2
                            refine wp_m6Hdr_focus_frame hmTr fun hmTrf => ?_
                            c0_hsteps_nogrp
                            · c0_call hBone
                              refine ⟨c, F0, sTr, m6ExtMem (m6ExtAddr c.hdr) extTr ⋆ R, rfl,
                                hinvTr.sparse, hmTrf, fun rB sB mB hspB hclB _ hfuB _ huB hmB => ?_⟩
                              have hinvB := FullM6HdrInv.mk_inv hinvTr.cfgOk hinvTr.extOk hspB
                              have hmB' := fullM6HdrMem_unfocus hmB
                              have hfuB' := Nat.le_trans hfuB hfuTr
                              c0_hsteps_nogrp
                              · refine wp_m6Hdr_focus_frame hmB' fun hmBf => ?_
                                c0_hsteps_nogrp
                                exact s9ProbeRetWm rfl (Or.inr rfl) hSetWm hinvB.cfgOk hinvB.extOk
                                  hinvB.sparse.lengths hfuB' (Or.inr rfl) (fun _ => huB ‹_›)
                                  (fun h => by cases h) (fullM6HdrMem_unfocus hmBf) (hQ 20#64)
                              · exact hJB2 () mB ⟨extTr, sB, hinvB, hclB, hfuB', hmB'⟩
                            · exact hJB2 () mTr ⟨extTr, sTr, hinvTr, hclTr, hfuTr,
                                fullM6HdrMem_unfocus hmTrf⟩
                        · -- Inproc `full_transitive_m6`
                          intro JTr hJTr
                          refine wp_m6Hdr_focus_frame hmS2 fun hmS2f => ?_
                          c0_hsteps_nogrp
                          · c0_call hTrans
                            refine ⟨c, F0, sS2, m6ExtMem (m6ExtAddr c.hdr) extS2 ⋆ R, rfl,
                              hinvS2.sparse, hmS2f,
                              fun rT sT mT hspT hclT _ _ hfuT _ huT hmT => ?_⟩
                            have hinvT := FullM6HdrInv.mk_inv hinvS2.cfgOk hinvS2.extOk hspT
                            have hmT' := fullM6HdrMem_unfocus hmT
                            have hfuT' := Nat.le_trans hfuT hfuS2
                            c0_hsteps_nogrp
                            · refine wp_m6Hdr_focus_frame hmT' fun hmTf => ?_
                              c0_hsteps_nogrp
                              exact s9ProbeRetWm rfl (Or.inr rfl) hSetWm hinvT.cfgOk hinvT.extOk
                                hinvT.sparse.lengths hfuT' (Or.inr rfl) (fun _ => huT ‹_›)
                                (fun h => by cases h) (fullM6HdrMem_unfocus hmTf) (hQ 20#64)
                            · exact hJTr () mT ⟨extS2, sT, hinvT, hclT hclS2, hfuT', hmT'⟩
                          · exact hJTr () mS2 ⟨extS2, sS2, hinvS2, hclS2, hfuS2,
                              fullM6HdrMem_unfocus hmS2f⟩
                      · -- Inproc `full_substitute` #2
                        intro JS2 hJS2
                        refine wp_m6Hdr_focus_frame hmSw fun hmSwf => ?_
                        c0_hsteps_nogrp
                        · c0_call hSubst
                          refine ⟨c, F0, sSw, m6ExtMem (m6ExtAddr c.hdr) extSw ⋆ R, rfl,
                            hinvSw.sparse, hmSwf, fun rSu sSu mSu hspSu hclSu hfuSu _ huSu hmSu =>
                              ?_⟩
                          have hinvSu := FullM6HdrInv.mk_inv hinvSw.cfgOk hinvSw.extOk hspSu
                          have hmSu' := fullM6HdrMem_unfocus hmSu
                          have hfuSu' := Nat.le_trans hfuSu hfuSw
                          c0_hsteps_nogrp
                          · refine wp_m6Hdr_focus_frame hmSu' fun hmSuf => ?_
                            c0_hsteps_nogrp
                            exact s9ProbeRetWm rfl (Or.inr rfl) hSetWm hinvSu.cfgOk hinvSu.extOk
                              hinvSu.sparse.lengths hfuSu' (Or.inr rfl) (fun _ => huSu ‹_›)
                              (fun h => by cases h) (fullM6HdrMem_unfocus hmSuf) (hQ 20#64)
                          · exact hJS2 () mSu ⟨extSw, sSu, hinvSu, hclSu, hfuSu', hmSu'⟩
                        · exact hJS2 () mSw ⟨extSw, sSw, hinvSw, hclSw, hfuSw,
                            fullM6HdrMem_unfocus hmSwf⟩
                    · -- Inproc `M6_DELAY_SWEEP` block
                      intro JSw hJSw
                      refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hDelay _ _ _ _ h)
                        hinvV.cfgOk hinvV.extOk hinvV.sparse.lengths hmV
                        fun ⟨delS, ⟨⟩⟩ extSd sSd mSd hcSd hlSd hmsSd hextSd _ hmSd => ?_
                      have hinvSd := fullM6HdrInv_with_ext
                        (fullM6HdrInv_of_m6Pres hinvV hlSd hcSd hmsSd) hextSd
                      have hclSd : sSd.core.cur_level = 0 := by rw [hcSd]; exact hclV
                      have hfuSd : sSd.core.fuel.toNat ≤ s.core.fuel.toNat := by
                        rw [hcSd]; exact hfuV'
                      c0_hsteps_nogrp
                      · exact hJSw (bin_dC, ()) mSd ⟨extSd, sSd, hinvSd, hclSd, hfuSd, hmSd⟩
                      · refine wp_join_group (ts := [.bool]) (fun _ mW => ∃ extW sW,
                            FullM6HdrInv c F0 extW sW ∧ sW.core.cur_level = 0 ∧
                            sW.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                            (FullM6HdrMem c extW sW ⋆ R) mW)
                          (fun _ p mp hp => by
                            dsimp only [Blocks.get_here, Blocks.get_there]; exact hJSw p mp hp) ?_
                        intro JSw' hJSw'
                        refine wp_m6Hdr_focus_frame hmSd fun hmSdf => ?_
                        c0_hsteps_nogrp
                        · c0_call hEnter
                          refine ⟨c, F0, sSd, m6ExtMem (m6ExtAddr c.hdr) extSd ⋆ R, rfl,
                            hinvSd.sparse, hmSdf, fun okE sE mE hclE hfuE hdenE hspE hmE => ?_⟩
                          have hmE' := fullM6HdrMem_unfocus hmE
                          have hfuE' := Nat.le_trans hfuE hfuSd
                          c0_hsteps_nogrp
                          · have hdenE' := hdenE ‹_›
                            refine wp_m6Hdr_focus_frame hmE' fun hmEf => ?_
                            c0_hsteps_nogrp; c0_call hSweepD
                            refine ⟨c, F0, sE, m6ExtMem (m6ExtAddr c.hdr) extSd ⋆ R, rfl, hdenE',
                              hmEf, fun rSw sSw mSw hdenSw _ hfuSw _ huSw hmSw => ?_⟩
                            have hfuSw' := Nat.le_trans hfuSw hfuE'
                            c0_hsteps_nogrp
                            · c0_call hRebNosort
                              refine ⟨c, F0, sSw, m6ExtMem (m6ExtAddr c.hdr) extSd ⋆ R, rfl,
                                hdenSw, hmSw, fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                              have hinvR := FullM6HdrInv.mk_inv hinvV.cfgOk hextSd hspR
                              have hmR' := fullM6HdrMem_unfocus hmR
                              refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                              c0_hsteps_nogrp
                              exact s9ProbeRetWm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hextSd
                                hinvR.sparse.lengths (Nat.le_trans hfuR hfuSw') (Or.inr rfl)
                                (fun _ => huSw ‹_›) (fun h => by cases h)
                                (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                            · have hmSw' := fullM6HdrMem_unfocus hmSw
                              refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
                                  M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧
                                  sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                  (FullM6HdrMem c extDl sDl ⋆ R) mDl) ?_ ?_
                              · rintro _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩
                                refine wp_m6Hdr_focus_frame hmDl fun hmDlf => ?_
                                c0_hsteps_nogrp
                                c0_call hRebNosort
                                refine ⟨c, F0, sDl, m6ExtMem (m6ExtAddr c.hdr) extDl ⋆ R, rfl,
                                  hdenDl, hmDlf, fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                                have hinvR := FullM6HdrInv.mk_inv hinvV.cfgOk hextDl hspR
                                have hmR' := fullM6HdrMem_unfocus hmR
                                have hfuR' := Nat.le_trans hfuR hfuDl
                                c0_hsteps_nogrp
                                · refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                                  c0_hsteps_nogrp
                                  exact s9ProbeRetWm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hextDl
                                    hinvR.sparse.lengths hfuR' (Or.inr rfl) (fun _ => huR ‹_›)
                                    (fun h => by cases h) (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                                · exact hJSw' (true, ()) mR ⟨extDl, sR, hinvR, hclR, hfuR', hmR'⟩
                              · intro JDl hJDl
                                c0_hsteps_nogrp
                                refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
                                    M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧
                                    sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                    (FullM6HdrMem c extDl sDl ⋆ R) mDl)
                                  (fun _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩ => by
                                    refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hBumpD _ _ _ _ h)
                                      hinvV.cfgOk hextDl hdenDl.lengths hmDl
                                      fun _ extDl' sDl' mDl' hcDl hlDl hmsDl hextDl' _ hmDl' => ?_
                                    exact hJDl () mDl' ⟨extDl', sDl', hextDl',
                                      fullDenseInv_of_core_eq hdenDl hlDl hcDl hmsDl.extPres,
                                      by rw [hcDl]; exact hfuDl, hmDl'⟩) ?_
                                intro JDb hJDb
                                refine wp_m6Hdr_focus_frame hmSw' fun hmSwf => ?_
                                c0_hsteps_nogrp
                                · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hRedD _ _ _ _ h)
                                    hinvV.cfgOk hextSd hdenSw.lengths (fullM6HdrMem_unfocus hmSwf)
                                    fun _ extDl sDl mDl hcDl hlDl hmsDl hextDl _ hmDl => ?_
                                  exact hJDl () mDl ⟨extDl, sDl, hextDl,
                                    fullDenseInv_of_core_eq hdenSw hlDl hcDl hmsDl.extPres,
                                    by rw [hcDl]; exact hfuSw', hmDl⟩
                                · exact hJDb () mSw ⟨extSd, sSw, hextSd, hdenSw, hfuSw',
                                    fullM6HdrMem_unfocus hmSwf⟩
                                · exact hJDb () mSw ⟨extSd, sSw, hextSd, hdenSw, hfuSw',
                                    fullM6HdrMem_unfocus hmSwf⟩
                          · have hinvE := FullM6HdrInv.mk_inv hinvV.cfgOk hextSd (hspE ‹_›)
                            refine wp_m6Hdr_focus_frame hmE' fun hmEf => ?_
                            c0_hsteps_nogrp
                            exact s9ProbeRetWm rfl (Or.inr rfl) hSetWm hinvE.cfgOk hextSd
                              hinvE.sparse.lengths hfuE' (Or.inr rfl)
                              (fun _ => fullM6HdrInv_inconsistent_unsat hinvE ‹_›)
                              (fun h => by cases h) (fullM6HdrMem_unfocus hmEf) (hQ 20#64)
                          · have hinvE := FullM6HdrInv.mk_inv hinvV.cfgOk hextSd (hspE ‹_›)
                            exact hJSw' (bin_dC, ()) mE ⟨extSd, sE, hinvE, hclE, hfuE', hmE'⟩
                · -- Inproc `full_backbone_m6` #1
                  intro JB1 hJB1
                  refine wp_m6Hdr_focus_frame hmS1 fun hmS1f => ?_
                  c0_hsteps_nogrp
                  · c0_call hBone
                    refine ⟨c, F0, sS1, m6ExtMem (m6ExtAddr c.hdr) extS1 ⋆ R, rfl,
                      hinvS1.sparse, hmS1f, fun rB sB mB hspB hclB _ hfuB _ huB hmB => ?_⟩
                    have hinvB := FullM6HdrInv.mk_inv hinvS1.cfgOk hinvS1.extOk hspB
                    have hmB' := fullM6HdrMem_unfocus hmB
                    have hfuB' := Nat.le_trans hfuB hfuS1
                    c0_hsteps_nogrp
                    · refine wp_m6Hdr_focus_frame hmB' fun hmBf => ?_
                      c0_hsteps_nogrp
                      exact s9ProbeRetWm rfl (Or.inr rfl) hSetWm hinvB.cfgOk hinvB.extOk
                        hinvB.sparse.lengths hfuB' (Or.inr rfl) (fun _ => huB ‹_›)
                        (fun h => by cases h) (fullM6HdrMem_unfocus hmBf) (hQ 20#64)
                    · exact hJB1 () mB ⟨extS1, sB, hinvB, hclB, hfuB', hmB'⟩
                  · exact hJB1 () mS1 ⟨extS1, sS1, hinvS1, hclS1, hfuS1, fullM6HdrMem_unfocus hmS1f⟩
              · -- Inproc `full_substitute` #1
                intro JS1 hJS1
                refine wp_m6Hdr_focus_frame hmC fun hmCf => ?_
                c0_hsteps_nogrp
                · c0_call hSubst
                  refine ⟨c, F0, sC, m6ExtMem (m6ExtAddr c.hdr) extC ⋆ R, rfl, hinvC.sparse, hmCf,
                    fun rSu sSu mSu hspSu hclSu hfuSu _ huSu hmSu => ?_⟩
                  have hinvSu := FullM6HdrInv.mk_inv hinvC.cfgOk hinvC.extOk hspSu
                  have hmSu' := fullM6HdrMem_unfocus hmSu
                  have hfuSu' := Nat.le_trans hfuSu hfuC
                  c0_hsteps_nogrp
                  · refine wp_m6Hdr_focus_frame hmSu' fun hmSuf => ?_
                    c0_hsteps_nogrp
                    exact s9ProbeRetWm rfl (Or.inr rfl) hSetWm hinvSu.cfgOk hinvSu.extOk
                      hinvSu.sparse.lengths hfuSu' (Or.inr rfl) (fun _ => huSu ‹_›)
                      (fun h => by cases h) (fullM6HdrMem_unfocus hmSuf) (hQ 20#64)
                  · exact hJS1 () mSu ⟨extC, sSu, hinvSu, hclSu, hfuSu', hmSu'⟩
                · exact hJS1 () mC ⟨extC, sC, hinvC, hclC, hfuC, fullM6HdrMem_unfocus hmCf⟩
            · -- Inproc `M6_DELAY_CONGRUENCE` block
              intro JC hJC
              refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hDelay _ _ _ _ h)
                hinvL.cfgOk hinvL.extOk hinvL.sparse.lengths hmL'
                fun ⟨delC, ⟨⟩⟩ extCd sCd mCd hcCd hlCd hmsCd hextCd _ hmCd => ?_
              have hinvCd := fullM6HdrInv_with_ext
                (fullM6HdrInv_of_m6Pres hinvL hlCd hcCd hmsCd) hextCd
              have hclCd : sCd.core.cur_level = 0 := by rw [hcCd]; exact hclL
              have hfuCd : sCd.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hcCd]; exact hfuL
              c0_hsteps_nogrp
              · exact hJC (bin_dL, ()) mCd ⟨extCd, sCd, hinvCd, hclCd, hfuCd, hmCd⟩
              · refine wp_join_group (ts := [.bool]) (fun _ mW => ∃ extW sW,
                    FullM6HdrInv c F0 extW sW ∧ sW.core.cur_level = 0 ∧
                    sW.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extW sW ⋆ R) mW)
                  (fun _ p mp hp => by
                    dsimp only [Blocks.get_here, Blocks.get_there]; exact hJC p mp hp) ?_
                intro JC' hJC'
                refine wp_m6Hdr_focus_frame hmCd fun hmCdf => ?_
                c0_hsteps_nogrp
                · c0_call hEnter
                  refine ⟨c, F0, sCd, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl, hinvCd.sparse,
                    hmCdf, fun okE sE mE hclE hfuE hdenE hspE hmE => ?_⟩
                  have hmE' := fullM6HdrMem_unfocus hmE
                  have hfuE' := Nat.le_trans hfuE hfuCd
                  c0_hsteps_nogrp
                  · have hdenE' := hdenE ‹_›
                    refine wp_m6Hdr_focus_frame hmE' fun hmEf => ?_
                    c0_hsteps_nogrp; c0_call hCong
                    refine ⟨c, F0, sE, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl, hdenE', hmEf,
                      fun rC sC mC hdenC _ hfuC _ huC hmC => ?_⟩
                    have hfuC' := Nat.le_trans (Nat.le_of_eq (congrArg BitVec.toNat hfuC)) hfuE'
                    c0_hsteps_nogrp
                    · c0_call hRebNosort
                      refine ⟨c, F0, sC, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl, hdenC, hmC,
                        fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                      have hinvR := FullM6HdrInv.mk_inv hinvL.cfgOk hextCd hspR
                      have hmR' := fullM6HdrMem_unfocus hmR
                      refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                      c0_hsteps_nogrp
                      exact s9ProbeRetWm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hextCd
                        hinvR.sparse.lengths (Nat.le_trans hfuR hfuC') (Or.inr rfl)
                        (fun _ => huC ‹_›) (fun h => by cases h) (fullM6HdrMem_unfocus hmRf)
                        (hQ 20#64)
                    · have hmC' := fullM6HdrMem_unfocus hmC
                      refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
                          M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧
                          sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          (FullM6HdrMem c extDl sDl ⋆ R) mDl) ?_ ?_
                      · rintro _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩
                        refine wp_m6Hdr_focus_frame hmDl fun hmDlf => ?_
                        c0_hsteps_nogrp
                        c0_call hRebNosort
                        refine ⟨c, F0, sDl, m6ExtMem (m6ExtAddr c.hdr) extDl ⋆ R, rfl, hdenDl,
                          hmDlf, fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                        have hinvR := FullM6HdrInv.mk_inv hinvL.cfgOk hextDl hspR
                        have hmR' := fullM6HdrMem_unfocus hmR
                        have hfuR' := Nat.le_trans hfuR hfuDl
                        c0_hsteps_nogrp
                        · refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                          c0_hsteps_nogrp
                          exact s9ProbeRetWm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hextDl
                            hinvR.sparse.lengths hfuR' (Or.inr rfl) (fun _ => huR ‹_›)
                            (fun h => by cases h) (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                        · exact hJC' (true, ()) mR ⟨extDl, sR, hinvR, hclR, hfuR', hmR'⟩
                      · intro JDl hJDl
                        c0_hsteps_nogrp
                        refine wp_join_group (ts := []) (fun _ mDl => ∃ extDl sDl,
                            M6HdrExtOk extDl ∧ FullDenseInv c F0 sDl ∧
                            sDl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                            (FullM6HdrMem c extDl sDl ⋆ R) mDl)
                          (fun _ _ mDl ⟨extDl, sDl, hextDl, hdenDl, hfuDl, hmDl⟩ => by
                            refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hBumpD _ _ _ _ h)
                              hinvL.cfgOk hextDl hdenDl.lengths hmDl
                              fun _ extDl' sDl' mDl' hcDl hlDl hmsDl hextDl' _ hmDl' => ?_
                            exact hJDl () mDl' ⟨extDl', sDl', hextDl',
                              fullDenseInv_of_core_eq hdenDl hlDl hcDl hmsDl.extPres,
                              by rw [hcDl]; exact hfuDl, hmDl'⟩) ?_
                        intro JDb hJDb
                        refine wp_m6Hdr_focus_frame hmC' fun hmCf => ?_
                        c0_hsteps_nogrp
                        · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hRedD _ _ _ _ h)
                            hinvL.cfgOk hextCd hdenC.lengths (fullM6HdrMem_unfocus hmCf)
                            fun _ extDl sDl mDl hcDl hlDl hmsDl hextDl _ hmDl => ?_
                          exact hJDl () mDl ⟨extDl, sDl, hextDl,
                            fullDenseInv_of_core_eq hdenC hlDl hcDl hmsDl.extPres,
                            by rw [hcDl]; exact hfuC', hmDl⟩
                        · exact hJDb () mC
                            ⟨extCd, sC, hextCd, hdenC, hfuC', fullM6HdrMem_unfocus hmCf⟩
                        · exact hJDb () mC
                            ⟨extCd, sC, hextCd, hdenC, hfuC', fullM6HdrMem_unfocus hmCf⟩
                  · have hinvE := FullM6HdrInv.mk_inv hinvL.cfgOk hextCd (hspE ‹_›)
                    refine wp_m6Hdr_focus_frame hmE' fun hmEf => ?_
                    c0_hsteps_nogrp
                    exact s9ProbeRetWm rfl (Or.inr rfl) hSetWm hinvE.cfgOk hextCd
                      hinvE.sparse.lengths hfuE' (Or.inr rfl)
                      (fun _ => fullM6HdrInv_inconsistent_unsat hinvE ‹_›)
                      (fun h => by cases h) (fullM6HdrMem_unfocus hmEf) (hQ 20#64)
                  · have hinvE := FullM6HdrInv.mk_inv hinvL.cfgOk hextCd (hspE ‹_›)
                    exact hJC' (bin_dL, ()) mE ⟨extCd, sE, hinvE, hclE, hfuE', hmE'⟩
          · exact hJbrk (bin_dL, round, ()) mL ⟨extL, sL, hinvL, hclL, hfuL, hmL⟩
  · intro J1 hJ1; c0_hsteps_nogrp
    refine wp_m6Hdr_focus_frame hm0a fun hm0af => ?_
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun (_ : Tup Val [i64]) ma =>
        (FullMem c s0a ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) ma)
      (fun _ ⟨parg, ⟨⟩⟩ ma hma =>
        s9_probe_init_call hLog10 hScaleM5 hinv0a hcl0a (by rw [hst0a.2.1, hc0]) hma hJ1)
      (fun _ hJp => by c0_hsteps_nogrp <;> exact hJp (_, ()) _ (by assumption))

/-- Parametric `Func.wp` proof for Step-9 `fidStep9ProbeM6Fn` (`full_probe_m6`) against
`FullM6Orch.m6ProbeSpec`: calls `full_rebuild_watches_nosort_fid`, tracks `bin_dirty` across
explicit `initial` and `!initial` (`while (round < 2ULL)`) passes, and sorts binary watches once
before returning `1ULL`. -/
theorem full_probe_m6_step9_wp (Γ : Env)
    (hProbeDt : EnvSpec Γ "full_probe_dticks_m6_hdr" (m6HdrW2aSpec [.bool] [i64]))
    (hLog10 : EnvSpec Γ "full_log10_q16_m7" m7Log10Q16Spec)
    (hScaleM5 : EnvSpec Γ "full_scale_delta_m5" FullFastSched.schedScaleDeltaSpec)
    (hViv : EnvSpec Γ "full_vivify_m6_hdr" m6aVivifySpec)
    (hEnter : EnvSpec Γ "full_enter_dense" FullFastSched.schedEnterDenseSpec)
    (hDelay : EnvSpec Γ "m6_hdr_delaying" (m6HdrW2aSpec [i64] [.bool]))
    (hCong : EnvSpec Γ "full_congruence_dense" FullM3CongBva.m3CongruenceDenseSpec)
    (hRebNosort : EnvSpec Γ "full_rebuild_watches_nosort_fid" Full.fullRebuildWatchesSpec)
    (hGetWm : EnvSpec Γ "m6_hdr_get_watermark" (m6HdrW2aSpec [i64] [i64]))
    (hSetWm : EnvSpec Γ "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] []))
    (hRedD : EnvSpec Γ "m6_hdr_reduce_delay" (m6HdrW2aSpec [i64] []))
    (hBumpD : EnvSpec Γ "m6_hdr_bump_delay" (m6HdrW2aSpec [i64] []))
    (hSweepD : EnvSpec Γ "full_sweep_dense_m6" FullDefSweep.fullSweepDenseSpec)
    (hSubst : EnvSpec Γ "full_substitute" Full.fullSubstituteSpec)
    (hBone : EnvSpec Γ "full_backbone_m6" FullM3Backbone.fullBackboneSpec)
    (hTrans : EnvSpec Γ "full_transitive_m6" FullFastBveBudgets.fullTransitiveFastSpec)
    (hFactor : EnvSpec Γ "full_factor" FullBvaHeap.fullFactorHeapSpec)
    (hSortBin : EnvSpec Γ "full_sort_bin_watches_fid" step7SortBinWatchesSpec) :
    ∀ a m Q X, m6ProbeSpec a m Q X → Func.wp Γ fidStep9ProbeM6Fn.body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X hs
  cases initial
  · exact full_probe_m6_inproc_step9_wp Γ hProbeDt hLog10 hScaleM5 hViv hEnter hDelay hCong
      hRebNosort hGetWm hSetWm hRedD hBumpD hSweepD hSubst hBone hTrans hFactor hSortBin h m Q X hs
  · exact full_probe_m6_init_step9_wp Γ hProbeDt hEnter hDelay hCong hRebNosort hGetWm hSetWm
      hRedD hBumpD hSweepD hSubst hBone hFactor hSortBin h m Q X hs

end LeanQbe.T.Examples.Kissat.FullFidelityStep9

end
