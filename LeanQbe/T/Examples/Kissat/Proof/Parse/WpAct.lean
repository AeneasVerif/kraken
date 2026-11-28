/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Heap.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Parse.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
public import LeanQbe.T.Examples.Kissat.Src.Parse
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.ControlComb

/-!
# Soundness Proof for `full_activate_lit_fid` (`Proof.Parse.WpAct`)

Proves parametric `(Γ : Env)` `Func.wp` theorem `full_activate_lit_fid_wp` against
`Parse.Spec.fullActivateLitFidSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Parse

open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Parse
open Kraken.Bedrock2.Test
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

private def ActPost (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) (m' : Mem 64) : Prop :=
  ∃ flags' unass' sc',
    let s' : FullState :=
      { core := { s.core with flags := flags', unassigned := unass' }, scratch := sc' }
    (FullMem c s' ⋆ R) m' ∧ s'.LengthsOk c ∧ FullExtScratchPres s s'

private theorem act_pres_trans {s s1 s2 : FullState}
    (h1 : FullExtScratchPres s s1) (h2 : FullExtScratchPres s1 s2) :
    FullExtScratchPres s s2 :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

private theorem act_scratch_lengths {c : FullCfg} {sc sc' : FullScratch}
    (hs : sc.LengthsOk c)
    (h1 : sc'.walk_vals = sc.walk_vals) (h2 : sc'.phases = sc.phases)
    (h3 : sc'.phases_target = sc.phases_target) (h4 : sc'.phases_best = sc.phases_best)
    (h5 : sc'.walk_best = sc.walk_best) (h6 : sc'.heap = sc.heap) (h7 : sc'.pos = sc.pos)
    (h8 : sc'.shrink_stk = sc.shrink_stk)
    (h9 : sc'.q_prev.length = c.max_vars) (h10 : sc'.q_next.length = c.max_vars)
    (h11 : sc'.q_stamp.length = c.max_vars)
    (h12 : sc'.wsort = sc.wsort) (h13 : sc'.work_stk1 = sc.work_stk1)
    (h14 : sc'.work_stk2 = sc.work_stk2) (h15 : sc'.tarjan_mark = sc.tarjan_mark)
    (h16 : sc'.tarjan_reach = sc.tarjan_reach) (h17 : sc'.score.length = c.max_vars)
    (h18 : sc'.sim_sig = sc.sim_sig) (h19 : sc'.glue_used.length = 64)
    (h20 : sc'.last_learned = sc.last_learned) (h21 : sc'.delayed = sc.delayed)
    (h22 : sc'.red_refs = sc.red_refs) (h23 : sc'.extend_stk = sc.extend_stk)
    (h24 : sc'.scratch_buf = sc.scratch_buf) :
    sc'.LengthsOk c :=
  ⟨h1 ▸ hs.1, h2 ▸ hs.2, h3 ▸ hs.3, h4 ▸ hs.4, h5 ▸ hs.5, h6 ▸ hs.6, h7 ▸ hs.7, h8 ▸ hs.8,
   h9, h10, h11, h12 ▸ hs.12, h13 ▸ hs.13, h14 ▸ hs.14, h15 ▸ hs.15, h16 ▸ hs.16, h17,
   h18 ▸ hs.18, h19, h20 ▸ hs.20, h21 ▸ hs.21, h22 ▸ hs.22, h23 ▸ hs.23, h24 ▸ hs.24⟩

private theorem act_g84_push (Γ : Env) (hPush : Γ.Has "full_heap_push" fullHeapPushSpec)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {Q : Post []} {X : XPost}
    {m : Mem 64} {J84 : Cont []} {lit : BitVec 32}
    (hpost : ActPost c s R m)
    (hJ84 : ∀ (xs : Tup Val []) (m' : Mem 64), ActPost c s R m' → J84 xs m') :
    wp Γ Q X (Expr.call (V := Val) (L := Cont) (rs := []) "full_heap_push"
      (as := [i64, i32]) (bs := [])
      (Arg.var (t := i64) c.hdr, Arg.var (t := i32) lit, ())
      fun _ => Expr.jump J84 ()) m := by
  obtain ⟨f2, u2, sc2, hm2, hlen2, hpres2⟩ := hpost
  let s2 : FullState := { core := { s.core with flags := f2, unassigned := u2 }, scratch := sc2 }
  refine wp_call_of_spec _ _
    (hPush _ _ _ _ ⟨c, s2, R, rfl, hlen2, hm2, fun _ s4 m4 hc4 hlen4 hsp4 hm4 => ?_⟩)
  dsimp only [fullSafetySlice, PreservesCoreSlice] at hc4 hlen4 hm4
  have hce4 : s4.core = { s.core with flags := f2, unassigned := u2 } := hc4
  have hm4' : (FullMem c ({ core := { s.core with flags := f2, unassigned := u2 },
                            scratch := s4.scratch } : FullState) ⋆ R) m4 := by rwa [← hce4]
  have hlen4' : ({ core := { s.core with flags := f2, unassigned := u2 },
                   scratch := s4.scratch } : FullState).LengthsOk c := by rwa [← hce4]
  have hsp4' : FullExtScratchPres s
      { core := { s.core with flags := f2, unassigned := u2 }, scratch := s4.scratch } := by
    rw [← hce4]; exact act_pres_trans hpres2 hsp4.1
  exact hJ84 () m4 ⟨f2, u2, s4.scratch, hm4', hlen4', hsp4'⟩

/-- Soundness proof for `full_activate_lit_fid` against `fullActivateLitFidSpec`. -/
theorem full_activate_lit_fid_wp (Γ : Env)
    (hInv : Γ.Has "f64u_inv_u64" Float64.Spec.f64uPure1Spec)
    (hSub : Γ.Has "f64u_sub" Float64.Spec.f64uPure2Spec)
    (hPush : Γ.Has "full_heap_push" fullHeapPushSpec) :
    ∀ a m Q X, Spec.fullActivateLitFidSpec a m Q X →
      Func.wp Γ full_activate_lit_fid_body a m Q X := by
  rintro ⟨h, lit, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  obtain hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  obtain hok := hlen.core_ok; obtain hsok := hlen.scratch_ok
  obtain hcv_le := hok.cur_vars_le
  have h31_gu : 31 < s.scratch.glue_used.length := by rw [hsok.glue_used_len]; omega
  unfold Func.wp full_activate_lit_fid_body
  c0_hfast_nogrp
  · exact hQ s.core.flags s.core.unassigned s.scratch m hlen ⟨rfl, rfl⟩ hm
  · have hlit_lt : lit.toNat < s.core.cur_vars := by
      have : s.core.cur_vars % 2 ^ 64 = s.core.cur_vars := Nat.mod_eq_of_lt (by omega)
      omega
    have hlit_fl : lit.toNat < s.core.flags.length := by rw [hok.flags_len]; omega
    have hlit_mv : lit.toNat < c.max_vars := by omega
    c0_hfast_nogrp
    · exact hQ s.core.flags s.core.unassigned s.scratch m hlen ⟨rfl, rfl⟩ hm
    · refine wp_join_group (ts := [i32]) (fun _ m37 => ActPost c s R m37) ?_ ?_
      · rintro _ ⟨p37_0, ⟨⟩⟩ m37 ⟨flags1, unass1, sc1, hm37, hlen1, hpres1⟩
        have hlen1' : ({ core := { s.core with flags := flags1, unassigned := unass1 },
                          scratch := sc1 } : FullState).LengthsOk c := hlen1
        have h31_gu1 : 31 < sc1.glue_used.length := by rw [hlen1'.scratch_ok.glue_used_len]; omega
        have hlit_qp1 : lit.toNat < sc1.q_prev.length := by
          rw [hlen1'.scratch_ok.q_prev_len]; exact hlit_mv
        have hlit_qn1 : lit.toNat < sc1.q_next.length := by
          rw [hlen1'.scratch_ok.q_next_len]; exact hlit_mv
        c0_hfast_nogrp
        · refine wp_join_group (ts := []) (fun _ m57 => ActPost c s R m57) ?_ ?_
          · rintro _ ⟨⟩ m57 ⟨flags2, unass2, sc2, hm57, hlen2, hpres2⟩
            have hlen2' : ({ core := { s.core with flags := flags2, unassigned := unass2 },
                              scratch := sc2 } : FullState).LengthsOk c := hlen2
            have hlit_qs2 : lit.toNat < sc2.q_stamp.length := by
              rw [hlen2'.scratch_ok.q_stamp_len]; exact hlit_mv
            have hlit_sc2 : lit.toNat < sc2.score.length := by
              rw [hlen2'.scratch_ok.score_len]; exact hlit_mv
            c0_hfast_nogrp
            refine wp_call_of_spec _ _ (hInv _ _ _ _ fun r82 => ?_)
            c0_hfast_nogrp
            refine wp_call_of_spec _ _ (hSub _ _ _ _ fun r83 => ?_)
            c0_hfast_nogrp
            refine wp_join_group (ts := []) (fun _ m84 => ActPost c s R m84) ?_ ?_
            · rintro _ ⟨⟩ m84 ⟨flags3, unass3, sc3, hm84, hlen3, hpres3⟩
              c0_hfast
              exact hQ flags3 unass3 sc3 m84 hlen3 hpres3 hm84
            · intro J84 hJ84
              c0_hfast_nogrp
              · refine act_g84_push Γ hPush ?_ hJ84
                refine ⟨flags2, unass2, ?sc3, ?hm3, ?hlen3, ?hpres3⟩
                case hm3 => assumption
                case hpres3 => exact hpres2
                case hlen3 =>
                  refine ⟨hlen2'.core_ok, act_scratch_lengths hlen2'.scratch_ok
                    rfl rfl rfl rfl rfl rfl rfl rfl
                    hlen2'.scratch_ok.q_prev_len hlen2'.scratch_ok.q_next_len
                    (by dsimp only; rw [List.length_set]; exact hlen2'.scratch_ok.q_stamp_len)
                    rfl rfl rfl rfl rfl
                    (by dsimp only; rw [List.length_set]; exact hlen2'.scratch_ok.score_len)
                    rfl hlen2'.scratch_ok.glue_used_len rfl rfl rfl rfl rfl⟩
              · refine hJ84 () _ ?_
                refine ⟨flags2, unass2, ?sc3b, ?hm3b, ?hlen3b, ?hpres3b⟩
                case hm3b => assumption
                case hlen3b =>
                  refine ⟨hlen2'.core_ok, act_scratch_lengths hlen2'.scratch_ok
                    rfl rfl rfl rfl rfl rfl rfl rfl
                    hlen2'.scratch_ok.q_prev_len hlen2'.scratch_ok.q_next_len
                    (by dsimp only; rw [List.length_set]; exact hlen2'.scratch_ok.q_stamp_len)
                    rfl rfl rfl rfl rfl
                    (by dsimp only; rw [List.length_set]; exact hlen2'.scratch_ok.score_len)
                    rfl hlen2'.scratch_ok.glue_used_len rfl rfl rfl rfl rfl⟩
                case hpres3b => exact hpres2
          · intro J57 hJ57
            c0_hfast_nogrp
            · refine hJ57 () _ ?_
              refine ⟨flags1, unass1, ?sc2a, ?hm2a, ?hlen2a, ?hpres2a⟩
              case hm2a => assumption
              case hlen2a =>
                refine ⟨hlen1'.core_ok, act_scratch_lengths hlen1'.scratch_ok
                  rfl rfl rfl rfl rfl rfl rfl rfl
                  (by dsimp only; rw [List.length_set]; exact hlen1'.scratch_ok.q_prev_len)
                  (by dsimp only; rw [List.length_set]; exact hlen1'.scratch_ok.q_next_len)
                  hlen1'.scratch_ok.q_stamp_len rfl rfl rfl rfl rfl hlen1'.scratch_ok.score_len rfl
                  (by dsimp only; rw [List.length_set]; exact hlen1'.scratch_ok.glue_used_len)
                  rfl rfl rfl rfl rfl⟩
              case hpres2a => exact hpres1
            · have hql_qn : (BitVec.setWidth 32 sc1.q_last).toNat <
                  (sc1.q_next.set lit.toNat 0xFFFFFFFF#32).length := by
                rw [List.length_set, hlen1'.scratch_ok.q_next_len, BitVec.toNat_setWidth]
                omega
              c0_hfast_nogrp
              refine hJ57 () _ ?_
              refine ⟨flags1, unass1, ?sc2b, ?hm2b, ?hlen2b, ?hpres2b⟩
              case hm2b => assumption
              case hlen2b =>
                refine ⟨hlen1'.core_ok, act_scratch_lengths hlen1'.scratch_ok
                  rfl rfl rfl rfl rfl rfl rfl rfl
                  (by dsimp only; rw [List.length_set]; exact hlen1'.scratch_ok.q_prev_len)
                  (by
                    dsimp only; rw [List.length_set, List.length_set]
                    exact hlen1'.scratch_ok.q_next_len)
                  hlen1'.scratch_ok.q_stamp_len rfl rfl rfl rfl rfl hlen1'.scratch_ok.score_len rfl
                  (by dsimp only; rw [List.length_set]; exact hlen1'.scratch_ok.glue_used_len)
                  rfl rfl rfl rfl rfl⟩
              case hpres2b => exact hpres1
      · intro J37 hJ37
        let mask : BitVec 32 :=
          1#32 ||| 8#32 ||| 16#32 ||| 32#32 ||| 64#32 ||| 128#32 ||| 256#32 ||| 512#32 ||| 1024#32
        let f1 := s.core.flags.set lit.toNat (s.core.flags[lit.toNat] ||| mask)
        let u1 := s.core.unassigned + 1#64
        have hok' : ({ s.core with flags := f1, unassigned := u1 } : FullCoreState).LengthsOk c :=
          ⟨hok.1, hok.2, hok.3, (by dsimp only [f1]; rw [List.length_set]; exact hok.flags_len),
            hok.5, hok.6, hok.7, hok.8, hok.9, hok.10, hok.11, hok.12, hok.13, hok.14, hok.15,
            hok.16, hok.17, hok.18, hok.19, hok.20, hok.21, hok.22, hok.23, hok.24, hok.25⟩
        c0_hfast_nogrp
        · exact hJ37 _ _ ⟨f1, u1, s.scratch, by assumption, ⟨hok', hsok⟩, ⟨rfl, rfl⟩⟩
        · exact hJ37 _ _ ⟨f1, u1, s.scratch, by assumption, ⟨hok', hsok⟩, ⟨rfl, rfl⟩⟩

end LeanQbe.T.Examples.Kissat.Proof.Parse
