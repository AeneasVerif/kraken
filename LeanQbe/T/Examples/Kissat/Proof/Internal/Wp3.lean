/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Internal.Spec
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Internal Variable Lifecycle & Mode WP Proofs (`Proof.Internal.Wp3`)

Parametric `(Γ : Env)` `Func.wp` proofs (`0` legacy `Full*` imports, `0` `@[expose]` theorems):
1. `full_set_inactive_wp` (`Spec.fullSetInactiveSpec`, calling `full_heap_down`)
2. `full_init_fresh_var_wp` (`Spec.fullInitFreshVarSpec`, calling `full_heap_push`)
3. `full_update_classify_fid_wp` (`Spec.fullUpdateClassifyFidSpec`, calling `m6_wm4_{get,set}`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Internal

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src
open LeanQbe.T.Examples.Kissat.Src.Internal
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapTactics

local elab "c0_hfast" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

local elab "c0_hfast_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

local elab "in_steps" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := true, splitJnz := false } 10000

local elab "in_steps_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 10000

local elab "in_steps_nogrp_nb" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps
    { unrollGroup := false, splitJnz := false, useBound := false } 10000

local elab "in_hfast_nogrp_nb" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps
    { unrollGroup := false, pruneJnz := false, useBound := false } 10000

local elab "in_steps_75" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 75

local elab "in_steps_15_nb" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false, useBound := false } 15

local elab "in_steps_8_nb" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false, useBound := false } 8

local macro "c0_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. `full_update_classify_fid_wp` -/

section UpdateClassifyFid

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.M6ProofUtilTactics

theorem full_update_classify_fid_wp (Γ : Env)
    (hGet : ∀ a m Q X, m6HdrW2aSpec [] [i64] a m Q X → Γ "m6_wm4_get" [i64] [i64] a m Q X)
    (hSet : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X → Γ "m6_wm4_set" [i64, i64] [] a m Q X) :
    ∀ a m Q X, Spec.fullUpdateClassifyFidSpec a m Q X →
      Func.wp Γ full_update_classify_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hsp
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hsp
  have hm_f : (FullMem c s ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m :=
    fullM6HdrMem_focus_full hm
  unfold Func.wp full_update_classify_fid_body
  c0_hfast_nogrp
  refine wp_join_group (fun (_ : Tup Val [.bool]) mg => mg = m) ?_ (fun J hJ => ?_)
  · rintro _ ⟨b, ⟨⟩⟩ _ rfl; simp only [Blocks.get_here]
    c0_call hGet
    refine m6HdrW2aSpec_of rfl hcfg hext hlen hm ?_
    rintro ⟨w0, ⟨⟩⟩ ext1 s1 m1 hcore1 hlen1 hpr1 hext1 hinit1 hm1
    c0_hfast_nogrp
    refine wp_join_group (fun (_ : Tup Val [i64]) mg1 => mg1 = m1) ?_ (fun J1 hJ1 => ?_)
    · rintro _ ⟨w1, ⟨⟩⟩ _ rfl; simp only [Blocks.get_here]
      c0_call hSet
      refine m6HdrW2aSpec_of rfl hcfg hext1 hlen1 hm1 ?_
      rintro ⟨⟩ ext2 s2 m2 hcore2 hlen2 hpr2 hext2 hinit2 hm2
      c0_hfast
      exact hQ () ext2 s2 m2 (hcore2.trans hcore1) hlen2 (hpr1.trans hpr2) hext2
        (fun hi => let ⟨hi1, hw1⟩ := hinit1 hi; let ⟨hi2, hw2⟩ := hinit2 hi1
          ⟨hi2, M6ExtW2bPres.trans hw1 hw2⟩) hm2
    · c0_hfast <;> exact hJ1 _ m1 rfl
  · c0_hfast <;> exact hJ _ m rfl

end UpdateClassifyFid

/-! ## 2. `full_init_fresh_var_wp` -/

section InitFreshVar

@[local bv_c0] private theorem bv64_shl1_or1_toNat (x : BitVec 64) :
    ((x <<< (1 : Nat)) ||| (1 : BitVec 64)).toNat = (2 * x.toNat + 1) % 2 ^ 64 := by
  have hs : (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 64 := by
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
  have he : (x <<< (1 : Nat)).toNat % 2 = 0 := by rw [hs]; omega
  rw [show (1 : BitVec 64) = 1#64 from rfl, FullBvaFwdTactics.bv64_or1_of_even he, hs]
  omega

private theorem add1_toNat {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by bv_omega

private theorem zext32_toNat (v : BitVec 32) : (BitVec.setWidth 64 v).toNat = v.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans v.isLt (by decide))]

private structure EqBox {α : Type _} (a b : α) : Prop where
  eq : a = b

private theorem with_abs_full {c : FullCfg} {R : Mem 64 → Prop} {m : Mem 64} {G : Prop}
    (s0 : FullState) (hm : (FullMem c s0 ⋆ R) m)
    (k : ∀ s1 : FullState, EqBox s1 s0 → (FullMem c s1 ⋆ R) m → G) : G :=
  k s0 ⟨rfl⟩ hm

private theorem bv64_shl2_toNat (v : BitVec 32) :
    (BitVec.setWidth 64 v <<< (2 : Nat)).toNat = 4 * v.toNat := by bv_omega

private theorem bv64_shl2_or1_toNat (v : BitVec 32) :
    ((BitVec.setWidth 64 v <<< (2 : Nat)) ||| (1 : BitVec 64)).toNat = 4 * v.toNat + 1 := by
  have hs : (BitVec.setWidth 64 v <<< (2 : Nat)).toNat = 4 * v.toNat := bv64_shl2_toNat v
  have he : (BitVec.setWidth 64 v <<< (2 : Nat)).toNat % 2 = 0 := by rw [hs]; omega
  rw [show (1 : BitVec 64) = 1#64 from rfl, FullBvaFwdTactics.bv64_or1_of_even he, hs]

private theorem bv64_shl2_add1_toNat (v : BitVec 32) :
    ((BitVec.setWidth 64 v <<< (2 : Nat)) + (1 : BitVec 64)).toNat = 4 * v.toNat + 1 := by
  bv_omega

private theorem bv64_shl2_add2_toNat (v : BitVec 32) :
    ((BitVec.setWidth 64 v <<< (2 : Nat)) + (2 : BitVec 64)).toNat = 4 * v.toNat + 2 := by
  bv_omega

private theorem bv64_shl2_add3_toNat (v : BitVec 32) :
    ((BitVec.setWidth 64 v <<< (2 : Nat)) + (3 : BitVec 64)).toNat = 4 * v.toNat + 3 := by
  bv_omega

private theorem bv64_shl1_toNat (v : BitVec 32) :
    (BitVec.setWidth 64 v <<< (1 : Nat)).toNat = 2 * v.toNat := by bv_omega

private theorem bv64_zext_shl1_or1 (v : BitVec 32) :
    ((BitVec.setWidth 64 v <<< (1 : Nat)) ||| (1 : BitVec 64)).toNat = 2 * v.toNat + 1 := by
  have h1 : (2 * (BitVec.setWidth 64 v).toNat + 1) % 2 ^ 64 = 2 * v.toNat + 1 := by
    rw [zext32_toNat]; exact Nat.mod_eq_of_lt (by have := v.isLt; omega)
  rw [bv64_shl1_or1_toNat, h1]

private theorem mul4_add3_lt {a b : Nat} (h : a < b) : 4 * a + 3 < 4 * b := by omega

private theorem mul2_add1_lt {a b : Nat} (h : a < b) : 2 * a + 1 < 2 * b := by omega

private theorem wvec4_at {xs : List (BitVec 32)} {fv k i0 i1 i2 i3 : Nat} {a b c d : BitVec 32}
    (hi0 : i0 = 4 * fv) (hi1 : i1 = 4 * fv + 1) (hi2 : i2 = 4 * fv + 2)
    (hi3 : i3 = 4 * fv + 3) (ha : a = 0#32) (hb : b = 0#32) (hc : c = 0#32) (hd : d = 0#32)
    (hbd : 4 * fv + 3 < xs.length) (hk : k < 4) :
    ((((xs.set i0 a).set i1 b).set i2 c).set i3 d)[4 * fv + k]?.getD 1#32 = 0#32 := by
  subst hi0 hi1 hi2 hi3 ha hb hc hd
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), Nat.add_zero, List.getElem?_set_self (by omega)]; rfl
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by simp; omega)]; rfl
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]; rfl
  · rw [List.getElem?_set_self (by simp; omega)]; rfl

private theorem wvec4_oth {xs : List (BitVec 32)} {fv i i0 i1 i2 i3 : Nat} {a b c d : BitVec 32}
    (hi0 : i0 = 4 * fv) (hi1 : i1 = 4 * fv + 1) (hi2 : i2 = 4 * fv + 2)
    (hi3 : i3 = 4 * fv + 3) (hneq : i / 4 ≠ fv) :
    ((((xs.set i0 a).set i1 b).set i2 c).set i3 d)[i]? = xs[i]? := by
  subst hi0 hi1 hi2 hi3
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
    List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]

private theorem vals2_at0 {xs : List (BitVec 8)} {fv i0 i1 : Nat} {a b : BitVec 8}
    (hi0 : i0 = 2 * fv) (hi1 : i1 = 2 * fv + 1) (ha : a = 0#8)
    (hbd : 2 * fv + 1 < xs.length) : ((xs.set i0 a).set i1 b)[2 * fv]?.getD 1#8 = 0#8 := by
  subst hi0 hi1 ha
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]; rfl

private theorem vals2_at1 {xs : List (BitVec 8)} {fv i0 i1 : Nat} {a b : BitVec 8}
    (hi0 : i0 = 2 * fv) (hi1 : i1 = 2 * fv + 1) (hb : b = 0#8)
    (hbd : 2 * fv + 1 < xs.length) :
    ((xs.set i0 a).set i1 b)[2 * fv + 1]?.getD 1#8 = 0#8 := by
  subst hi0 hi1 hb
  rw [List.getElem?_set_self (by simp; omega)]; rfl

private theorem vals2_oth {xs : List (BitVec 8)} {fv i i0 i1 : Nat} {a b : BitVec 8}
    (hi0 : i0 = 2 * fv) (hi1 : i1 = 2 * fv + 1) (hneq : i / 2 ≠ fv) :
    ((xs.set i0 a).set i1 b)[i]? = xs[i]? := by
  subst hi0 hi1
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]

private theorem list_set_at_eq {α : Type _} {xs : List α} {i i0 : Nat} {v d : α}
    (hi : i0 = i) (hbd : i < xs.length) : (xs.set i0 v)[i]?.getD d = v := by
  subst hi; rw [List.getElem?_set_self hbd]; rfl

private theorem list_set_oth_eq {α : Type _} {xs : List α} {i j i0 : Nat} {v : α}
    (hi : i0 = i) (hne : j ≠ i) : (xs.set i0 v)[j]? = xs[j]? := by
  subst hi; exact List.getElem?_set_ne (by omega)

private theorem call_heap_push_spec {Q : Post []} {X : XPost} {c : FullCfg} {s0 : FullState}
    {R : Mem 64 → Prop} {m0 : Mem 64} {v : BitVec 32}
    (hm : (FullMem c s0 ⋆ R) m0) (hlen : s0.LengthsOk c)
    (hcont : ∀ (r : Tup Val []) (s' : FullState) (m' : Mem 64),
      PreservesCoreSlice (fullSafetySlice c).coreProj s0 s' →
      (fullSafetySlice c).safe s' →
      FullProbeScratchPresWith s0 s'
        (∃ hp' ps' hl', s'.scratch = { s0.scratch with heap := hp', pos := ps', heap_len := hl' }) →
      ((fullSafetySlice c).mem s' ⋆ R) m' → Q r m') :
    fullHeapPushSpec (c.hdr, v, ()) m0 Q X :=
  ⟨c, s0, R, rfl, hlen, hm, hcont⟩

private theorem mk_ifv_ext {s s' : FullState}
    (h1 : s'.scratch.last_learned = s.scratch.last_learned)
    (h2 : s'.scratch.extend_len = s.scratch.extend_len)
    (h3 : s'.scratch.scratch_buf = s.scratch.scratch_buf)
    (h4 : s'.scratch.wsort = s.scratch.wsort)
    (h5 : s'.scratch.tarjan_mark = s.scratch.tarjan_mark)
    (h6 : s'.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (h7 : s'.scratch.sim_sig = s.scratch.sim_sig)
    (h8 : s'.scratch.res_sz = s.scratch.res_sz) :
    FullExtScratchPres s s' ∧
      s'.scratch.scratch_buf = s.scratch.scratch_buf ∧ s'.scratch.wsort = s.scratch.wsort ∧
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ s'.scratch.sim_sig = s.scratch.sim_sig ∧
      s'.scratch.res_sz = s.scratch.res_sz :=
  ⟨⟨h1, h2⟩, h3, h4, h5, h6, h7, h8⟩

private theorem ifv_ext_trans {s s1 s2 : FullState}
    (hA : FullExtScratchPres s s1 ∧
      s1.scratch.scratch_buf = s.scratch.scratch_buf ∧ s1.scratch.wsort = s.scratch.wsort ∧
      s1.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
      s1.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ s1.scratch.sim_sig = s.scratch.sim_sig ∧
      s1.scratch.res_sz = s.scratch.res_sz)
    (h1 : s2.scratch.last_learned = s1.scratch.last_learned)
    (h2 : s2.scratch.extend_len = s1.scratch.extend_len)
    (h3 : s2.scratch.scratch_buf = s1.scratch.scratch_buf)
    (h4 : s2.scratch.wsort = s1.scratch.wsort)
    (h5 : s2.scratch.tarjan_mark = s1.scratch.tarjan_mark)
    (h6 : s2.scratch.tarjan_reach = s1.scratch.tarjan_reach)
    (h7 : s2.scratch.sim_sig = s1.scratch.sim_sig)
    (h8 : s2.scratch.res_sz = s1.scratch.res_sz) :
    FullExtScratchPres s s2 ∧
      s2.scratch.scratch_buf = s.scratch.scratch_buf ∧ s2.scratch.wsort = s.scratch.wsort ∧
      s2.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
      s2.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ s2.scratch.sim_sig = s.scratch.sim_sig ∧
      s2.scratch.res_sz = s.scratch.res_sz :=
  ⟨⟨h1.trans hA.1.1, h2.trans hA.1.2⟩,
    h3.trans hA.2.1, h4.trans hA.2.2.1, h5.trans hA.2.2.2.1,
    h6.trans hA.2.2.2.2.1, h7.trans hA.2.2.2.2.2.1, h8.trans hA.2.2.2.2.2.2⟩

private abbrev IfvExtOk (s s' : FullState) : Prop :=
  FullExtScratchPres s s' ∧
    s'.scratch.scratch_buf = s.scratch.scratch_buf ∧ s'.scratch.wsort = s.scratch.wsort ∧
    s'.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
    s'.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ s'.scratch.sim_sig = s.scratch.sim_sig ∧
    s'.scratch.res_sz = s.scratch.res_sz

private theorem ifv_ext_of_eq {s s1 s2 : FullState}
    (hA : IfvExtOk s s1) (heq : s2.scratch = s1.scratch) : IfvExtOk s s2 :=
  ⟨⟨by rw [heq]; exact hA.1.1, by rw [heq]; exact hA.1.2⟩,
    by rw [heq]; exact hA.2.1, by rw [heq]; exact hA.2.2.1,
    by rw [heq]; exact hA.2.2.2.1, by rw [heq]; exact hA.2.2.2.2.1,
    by rw [heq]; exact hA.2.2.2.2.2.1, by rw [heq]; exact hA.2.2.2.2.2.2⟩

private theorem mk_ifv_ex {c : FullCfg} {R : Mem 64 → Prop} {m : Mem 64}
    {s s' : FullState} {core0 : FullCoreState} {G : Prop}
    (hJ : (∃ sj : FullState, sj.core = core0 ∧ sj.LengthsOk c ∧ IfvExtOk s sj ∧
      (FullMem c sj ⋆ R) m) → G)
    (hm : (FullMem c s' ⋆ R) m) (hc : s'.core = core0)
    (hl : s'.LengthsOk c) (hext : IfvExtOk s s') : G :=
  hJ ⟨s', hc, hl, hext, hm⟩

private theorem qf_lt_len {q : BitVec 64} {cv mv qpl : Nat}
    (hult : q.toNat % 2 ^ 32 < cv % 2 ^ 64)
    (hcv : cv ≤ mv) (hmx : mv < 2 * 2 ^ 28) (hqpl : qpl = mv) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 q)).toNat < qpl := by
  have h1 : cv < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h1] at hult
  simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : q.toNat % 2 ^ 32 < 2 ^ 64)]
  omega

private theorem ifv_ext_of_heap_push {s sj1 sp : FullState}
    (hext : IfvExtOk s sj1)
    (hprp : FullProbeScratchPresWith sj1 sp
      (∃ hp' ps' hl', sp.scratch = { sj1.scratch with heap := hp', pos := ps', heap_len := hl' })) :
    IfvExtOk s sp := by
  rcases hprp.2.2.2.2.2.2.2.2 with ⟨hp', ps', hl', hsc⟩
  exact ifv_ext_trans hext
    (by rw [hsc]) (by rw [hsc]) (by rw [hsc]) (by rw [hsc])
    (by rw [hsc]) (by rw [hsc]) (by rw [hsc]) (by rw [hsc])

theorem full_init_fresh_var_wp (Γ : Env)
    (hHeapPush : ∀ a m Q X, fullHeapPushSpec a m Q X →
      Γ "full_heap_push" [i64, i32] [] a m Q X) :
    ∀ a m Q X, Spec.fullInitFreshVarSpec a m Q X →
      Func.wp Γ full_init_fresh_var_body a m Q X := by
  rintro ⟨h, fv, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hfv, hm, hQ⟩
  have hcl := hlen.core_ok
  have hsc := hlen.scratch_ok
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hcl.cur_vars_le
  have hwvl := hcl.wvec_len; have hvl := hcl.vals_len; have hmrl := hcl.mrk_len
  unfold Func.wp full_init_fresh_var_body
  in_steps_75
  refine with_abs_full _ hm fun s1 hs1 hm1 => ?_
  clear hm
  have hfll := hcl.flags_len; have hlvll := hcl.lvl_len; have hrsl := hcl.rsns_len
  have hphl := hsc.phases_len; have hphtl := hsc.phases_target_len
  have hphbl := hsc.phases_best_len; have hwbl := hsc.walk_best_len
  have hscl := hsc.score_len
  have hqpl := hsc.q_prev_len; have hqnl := hsc.q_next_len; have hqsl := hsc.q_stamp_len
  have hlen1 : s1.LengthsOk c := by
    rw [hs1.eq]
    exact ⟨{ hcl with
        wvec_len := by simp [hwvl], vals_len := by simp [hvl], mrk_len := by simp [hmrl] },
      hsc⟩
  have hsc1_eq : s1.scratch = s.scratch := by rw [hs1.eq]
  have hfv_lt : fv.toNat < c.max_vars := Nat.lt_of_lt_of_le hfv hcv_le
  have hwv1_at : ∀ k < 4, s1.core.wvec[4 * fv.toNat + k]?.getD 1#32 = 0#32 := by
    intro k hk; rw [hs1.eq]
    exact wvec4_at (bv64_shl2_toNat fv)
      (by first | exact bv64_shl2_or1_toNat fv | exact bv64_shl2_add1_toNat fv)
      (bv64_shl2_add2_toNat fv) (bv64_shl2_add3_toNat fv)
      rfl rfl rfl rfl (hwvl ▸ mul4_add3_lt hfv_lt) hk
  have hwv1_oth : ∀ i < 4 * c.max_vars, i / 4 ≠ fv.toNat →
      s1.core.wvec[i]? = s.core.wvec[i]? := by
    intro i _ hneq; rw [hs1.eq]
    exact wvec4_oth (bv64_shl2_toNat fv)
      (by first | exact bv64_shl2_or1_toNat fv | exact bv64_shl2_add1_toNat fv)
      (bv64_shl2_add2_toNat fv) (bv64_shl2_add3_toNat fv) hneq
  have hvl1_0 : s1.core.vals[2 * fv.toNat]?.getD 1#8 = 0#8 := by
    rw [hs1.eq]
    exact vals2_at0 (bv64_shl1_toNat fv) (bv64_zext_shl1_or1 fv) rfl
      (hvl ▸ mul2_add1_lt hfv_lt)
  have hvl1_1 : s1.core.vals[2 * fv.toNat + 1]?.getD 1#8 = 0#8 := by
    rw [hs1.eq]
    exact vals2_at1 (bv64_shl1_toNat fv) (bv64_zext_shl1_or1 fv) rfl
      (hvl ▸ mul2_add1_lt hfv_lt)
  have hvl1_oth : ∀ l < 2 * c.max_vars, l / 2 ≠ fv.toNat →
      s1.core.vals[l]? = s.core.vals[l]? := by
    intro l _ hneq; rw [hs1.eq]
    exact vals2_oth (bv64_shl1_toNat fv) (bv64_zext_shl1_or1 fv) hneq
  have hmr1_at : s1.core.mrk[fv.toNat]?.getD 1#8 = 0#8 := by
    rw [hs1.eq]
    exact list_set_at_eq (zext32_toNat fv) (hmrl ▸ hfv_lt)
  have hmr1_oth : ∀ v < c.max_vars, v ≠ fv.toNat → s1.core.mrk[v]? = s.core.mrk[v]? := by
    intro v _ hne; rw [hs1.eq]
    exact list_set_oth_eq (zext32_toNat fv) hne
  have hs1_c_eq : s1.core = { s.core with
      vals := s1.core.vals, mrk := s1.core.mrk, wvec := s1.core.wvec } := by
    rw [hs1.eq]
  clear hs1
  have hph1 : s1.scratch.phases.length = c.max_vars := hlen1.scratch_ok.phases_len
  have hpht1 : s1.scratch.phases_target.length = c.max_vars := hlen1.scratch_ok.phases_target_len
  have hphb1 : s1.scratch.phases_best.length = c.max_vars := hlen1.scratch_ok.phases_best_len
  have hwb1 : s1.scratch.walk_best.length = c.max_vars := hlen1.scratch_ok.walk_best_len
  have hlvl1 : s1.core.lvl.length = c.max_vars := hlen1.core_ok.lvl_len
  have hrs1 : s1.core.rsns.length = c.max_vars := hlen1.core_ok.rsns_len
  have hpos1 : s1.scratch.pos.length = c.max_vars := hlen1.scratch_ok.pos_len
  have hscr1 : s1.scratch.score.length = c.max_vars := hlen1.scratch_ok.score_len
  have hqp1 : s1.scratch.q_prev.length = c.max_vars := hlen1.scratch_ok.q_prev_len
  have hqn1 : s1.scratch.q_next.length = c.max_vars := hlen1.scratch_ok.q_next_len
  have hqs1 : s1.scratch.q_stamp.length = c.max_vars := hlen1.scratch_ok.q_stamp_len
  have hfl1 : s1.core.flags.length = c.max_vars := hlen1.core_ok.flags_len
  have hfv_lt_mv : (BitVec.setWidth 64 fv).toNat < c.max_vars := by
    rw [zext32_toNat]; exact hfv_lt
  have hv_ph1 : (BitVec.setWidth 64 fv).toNat < s1.scratch.phases.length := hph1 ▸ hfv_lt_mv
  have hv_pht1 : (BitVec.setWidth 64 fv).toNat < s1.scratch.phases_target.length :=
    hpht1 ▸ hfv_lt_mv
  have hv_phb1 : (BitVec.setWidth 64 fv).toNat < s1.scratch.phases_best.length :=
    hphb1 ▸ hfv_lt_mv
  have hv_wb1 : (BitVec.setWidth 64 fv).toNat < s1.scratch.walk_best.length := hwb1 ▸ hfv_lt_mv
  in_steps_15_nb
  refine with_abs_full _ hm fun s2a hs2a hm2a => ?_
  clear hm
  have hlen2a : s2a.LengthsOk c := by
    rw [hs2a.eq]
    exact ⟨hlen1.core_ok, { hlen1.scratch_ok with
      phases_len := by simp [hph1], phases_target_len := by simp [hpht1],
      phases_best_len := by simp [hphb1], walk_best_len := by simp [hwb1] }⟩
  have hs2a_c : s2a.core = s1.core := by rw [hs2a.eq]
  have hs2a_ext : IfvExtOk s s2a := by
    have h8 : s2a.scratch.last_learned = s1.scratch.last_learned ∧
        s2a.scratch.extend_len = s1.scratch.extend_len ∧
        s2a.scratch.scratch_buf = s1.scratch.scratch_buf ∧
        s2a.scratch.wsort = s1.scratch.wsort ∧
        s2a.scratch.tarjan_mark = s1.scratch.tarjan_mark ∧
        s2a.scratch.tarjan_reach = s1.scratch.tarjan_reach ∧
        s2a.scratch.sim_sig = s1.scratch.sim_sig ∧
        s2a.scratch.res_sz = s1.scratch.res_sz := by
      rw [hs2a.eq]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact mk_ifv_ext
      (h8.1.trans (congrArg FullScratch.last_learned hsc1_eq))
      (h8.2.1.trans (congrArg FullScratch.extend_len hsc1_eq))
      (h8.2.2.1.trans (congrArg FullScratch.scratch_buf hsc1_eq))
      (h8.2.2.2.1.trans (congrArg FullScratch.wsort hsc1_eq))
      (h8.2.2.2.2.1.trans (congrArg FullScratch.tarjan_mark hsc1_eq))
      (h8.2.2.2.2.2.1.trans (congrArg FullScratch.tarjan_reach hsc1_eq))
      (h8.2.2.2.2.2.2.1.trans (congrArg FullScratch.sim_sig hsc1_eq))
      (h8.2.2.2.2.2.2.2.trans (congrArg FullScratch.res_sz hsc1_eq))
  clear hs2a
  have hv_lvl2a : (BitVec.setWidth 64 fv).toNat < s2a.core.lvl.length :=
    hlen2a.core_ok.lvl_len ▸ hfv_lt_mv
  have hv_rs2a : (BitVec.setWidth 64 fv).toNat < s2a.core.rsns.length :=
    hlen2a.core_ok.rsns_len ▸ hfv_lt_mv
  in_steps_8_nb
  refine with_abs_full _ hm fun s2b hs2b hm2b => ?_
  clear hm
  have hlen2b : s2b.LengthsOk c := by
    rw [hs2b.eq]
    exact ⟨{ hlen2a.core_ok with
        lvl_len := by rw [List.length_set, hlen2a.core_ok.lvl_len],
        rsns_len := by rw [List.length_set, hlen2a.core_ok.rsns_len] },
      hlen2a.scratch_ok⟩
  have hs2b_sc : s2b.scratch = s2a.scratch := by rw [hs2b.eq]
  have hlvl_at : s2b.core.lvl[fv.toNat]?.getD 1#32 = 0#32 := by
    rw [hs2b.eq, hs2a_c]
    exact list_set_at_eq (zext32_toNat fv) (hlen1.core_ok.lvl_len ▸ hfv_lt)
  have hlvl_oth : ∀ v < c.max_vars, v ≠ fv.toNat → s2b.core.lvl[v]? = s.core.lvl[v]? := by
    intro v _ hne; rw [hs2b.eq, hs2a_c, hs1_c_eq]
    exact list_set_oth_eq (zext32_toNat fv) hne
  have hrs_at : s2b.core.rsns[fv.toNat]?.getD 0#32 = 4294967295#32 := by
    rw [hs2b.eq, hs2a_c]
    exact list_set_at_eq (zext32_toNat fv) (hlen1.core_ok.rsns_len ▸ hfv_lt)
  have hrs_oth : ∀ v < c.max_vars, v ≠ fv.toNat → s2b.core.rsns[v]? = s.core.rsns[v]? := by
    intro v _ hne; rw [hs2b.eq, hs2a_c, hs1_c_eq]
    exact list_set_oth_eq (zext32_toNat fv) hne
  have hs2b_c : s2b.core = { s.core with
      vals := s1.core.vals, mrk := s1.core.mrk, lvl := s2b.core.lvl,
      rsns := s2b.core.rsns, wvec := s1.core.wvec } := by
    rw [hs2b.eq, hs2a_c, hs1_c_eq]
  clear hs2b
  have hs2b_ext : IfvExtOk s s2b := ifv_ext_of_eq hs2a_ext hs2b_sc
  clear hs2a_c hs2b_sc hs1_c_eq hsc1_eq
  have hv_pos2b : (BitVec.setWidth 64 fv).toNat < s2b.scratch.pos.length :=
    hlen2b.scratch_ok.pos_len ▸ hfv_lt_mv
  have hv_scr2b : (BitVec.setWidth 64 fv).toNat < s2b.scratch.score.length :=
    hlen2b.scratch_ok.score_len ▸ hfv_lt_mv
  have hv_qp2b : (BitVec.setWidth 64 fv).toNat < s2b.scratch.q_prev.length :=
    hlen2b.scratch_ok.q_prev_len ▸ hfv_lt_mv
  have hv_qn2b : (BitVec.setWidth 64 fv).toNat < s2b.scratch.q_next.length :=
    hlen2b.scratch_ok.q_next_len ▸ hfv_lt_mv
  have hv_fl2b : (BitVec.setWidth 64 fv).toNat < s2b.core.flags.length :=
    hlen2b.core_ok.flags_len ▸ hfv_lt_mv
  in_steps_nogrp_nb
  refine with_abs_full _ hm fun s3 hs3 hm3 => ?_
  clear hm
  have hlen3 : s3.LengthsOk c := by
    rw [hs3.eq]
    exact ⟨{ hlen2b.core_ok with flags_len := by simp [hlen2b.core_ok.flags_len] },
      { hlen2b.scratch_ok with
        pos_len := by simp [hlen2b.scratch_ok.pos_len],
        score_len := by simp [hlen2b.scratch_ok.score_len],
        q_prev_len := by simp [hlen2b.scratch_ok.q_prev_len],
        q_next_len := by simp [hlen2b.scratch_ok.q_next_len] }⟩
  have hs3_c : s3.core = { s.core with
      vals := s1.core.vals, mrk := s1.core.mrk, flags := s3.core.flags,
      lvl := s2b.core.lvl, rsns := s2b.core.rsns, wvec := s1.core.wvec } := by
    rw [hs3.eq, hs2b_c]
  have hs3_ext : IfvExtOk s s3 := ifv_ext_trans hs2b_ext
    (by rw [hs3.eq]) (by rw [hs3.eq]) (by rw [hs3.eq]) (by rw [hs3.eq])
    (by rw [hs3.eq]) (by rw [hs3.eq]) (by rw [hs3.eq]) (by rw [hs3.eq])
  clear hs3 hs2b_c
  have hqn3 : (BitVec.setWidth 64 fv).toNat < s3.scratch.q_next.length :=
    hlen3.scratch_ok.q_next_len ▸ hfv_lt_mv
  refine wp_join_group (fun (_ : Tup Val []) mj =>
      ∃ (sj : FullState),
        sj.core = s3.core ∧ sj.LengthsOk c ∧ IfvExtOk s sj ∧ (FullMem c sj ⋆ R) mj) ?_
    (fun J1 hJ1 => ?_)
  · rintro _ ⟨⟩ mj ⟨sj, hsj_c, hlenj, hextj, hmj⟩
    simp only [Blocks.get_here]
    have hv_qsj : (BitVec.setWidth 64 fv).toNat < sj.scratch.q_stamp.length :=
      hlenj.scratch_ok.q_stamp_len ▸ hfv_lt_mv
    in_steps_nogrp_nb
    refine with_abs_full _ hm fun sj1 hsj1 hmj1 => ?_
    clear hm
    have hlenj1 : sj1.LengthsOk c := by
      rw [hsj1.eq]
      exact ⟨hlenj.core_ok, { hlenj.scratch_ok with
        q_stamp_len := by simp [hlenj.scratch_ok.q_stamp_len] }⟩
    have hsj1_c : sj1.core = s3.core := by rw [hsj1.eq, hsj_c]
    have hextj1 : IfvExtOk s sj1 := ifv_ext_trans hextj
      (by rw [hsj1.eq]) (by rw [hsj1.eq]) (by rw [hsj1.eq]) (by rw [hsj1.eq])
      (by rw [hsj1.eq]) (by rw [hsj1.eq]) (by rw [hsj1.eq]) (by rw [hsj1.eq])
    clear hsj1 hsj_c
    refine wp_join_group (fun (_ : Tup Val []) mk =>
        ∃ (sk : FullState),
          sk.core = s3.core ∧ sk.LengthsOk c ∧ IfvExtOk s sk ∧ (FullMem c sk ⋆ R) mk) ?_
      (fun J2 hJ2 => ?_)
    · rintro _ ⟨⟩ mk ⟨sk, hsk_c, hlenk, hextk, hmk⟩
      simp only [Blocks.get_here]
      in_steps_nogrp_nb
      refine with_abs_full _ hm fun sf hsf hmf => ?_
      clear hm
      have hlenf : sf.LengthsOk c := by
        rw [hsf.eq]; exact ⟨{ hlenk.core_ok with }, hlenk.scratch_ok⟩
      have hextf : IfvExtOk s sf := ifv_ext_of_eq hextk (by rw [hsf.eq])
      have hsf_c : sf.core = { s.core with
          unassigned := sf.core.unassigned, vals := s1.core.vals, mrk := s1.core.mrk,
          flags := s3.core.flags, lvl := s2b.core.lvl, rsns := s2b.core.rsns,
          wvec := s1.core.wvec } := by
        rw [hsf.eq, hsk_c, hs3_c]
      have hsf_eq : sf =
          { core := { s.core with
              unassigned := sf.core.unassigned, vals := s1.core.vals, mrk := s1.core.mrk,
              flags := s3.core.flags, lvl := s2b.core.lvl, rsns := s2b.core.rsns,
              wvec := s1.core.wvec },
            scratch := sf.scratch } := by
        cases sf; exact congrArg (FullState.mk · _) hsf_c
      rw [hsf_eq] at hlenf hextf hmf
      exact hQ s1.core.vals s1.core.mrk s3.core.flags s2b.core.lvl s2b.core.rsns
        s1.core.wvec sf.core.unassigned sf.scratch _ hlenf hextf.1 hextf.2.1 hextf.2.2.1
        hextf.2.2.2.1 hextf.2.2.2.2.1 hextf.2.2.2.2.2.1 hextf.2.2.2.2.2.2 hvl1_0 hvl1_1
        hvl1_oth hmr1_at hmr1_oth hlvl_at hlvl_oth hrs_at hrs_oth hwv1_at hwv1_oth hmf
    · c0_hsplit_nobound
      · clear hc
        c0_hcall hHeapPush
        refine call_heap_push_spec hmj1 hlenj1 ?_
        rintro ⟨⟩ sp mp hcp hlsp hprp hmp
        in_steps_nogrp_nb
        dsimp only [PreservesCoreSlice, fullSafetySlice] at hcp
        exact hJ2 () _ ⟨sp, hcp.trans hsj1_c, hlsp, ifv_ext_of_heap_push hextj1 hprp, hmp⟩
      · clear hc
        in_steps_nogrp_nb
        exact hJ2 () _ ⟨sj1, hsj1_c, hlenj1, hextj1, hmj1⟩
  · c0_hsplit_nobound
    · have hqp3 := qf_lt_len hc hlen3.core_ok.cur_vars_le hmx hlen3.scratch_ok.q_prev_len
      clear hc
      in_steps_nogrp_nb
      refine mk_ifv_ex (hJ1 () _) hm rfl ?_
        (ifv_ext_trans hs3_ext rfl rfl rfl rfl rfl rfl rfl rfl)
      exact ⟨hlen3.core_ok, { hlen3.scratch_ok with
        q_prev_len := by rw [List.length_set, hlen3.scratch_ok.q_prev_len],
        q_next_len := by rw [List.length_set, hlen3.scratch_ok.q_next_len] }⟩
    · clear hc
      in_steps_nogrp_nb
      refine mk_ifv_ex (hJ1 () _) hm rfl ?_
        (ifv_ext_trans hs3_ext rfl rfl rfl rfl rfl rfl rfl rfl)
      exact ⟨hlen3.core_ok, { hlen3.scratch_ok with
        q_next_len := by simp [hlen3.scratch_ok.q_next_len] }⟩

end InitFreshVar

/-! ## 3. `full_set_inactive_wp` -/

section SetInactive

private abbrev s5InactVmtfSt (s1 : FullState) (qp qn : List (BitVec 32))
    (qsi qss qf ql : BitVec 64) : FullState :=
  { s1 with scratch := { s1.scratch with
    q_prev := qp, q_next := qn, q_search_idx := qsi, q_search_stamp := qss,
    q_first := qf, q_last := ql } }

private theorem core_upd_unass_self (k : FullCoreState) :
    { k with unassigned := k.unassigned } = k := by cases k; rfl

private theorem bv64_sub1_toNat {x : BitVec 64} (h : 0 < x.toNat) :
    (x - 1#64).toNat = x.toNat - 1 := by bv_omega

private theorem maxv_lt64 {m : Nat} (h : m < 2 * 2 ^ 28) : m < 2 ^ 64 := by omega

private theorem bv_ult_le_toNat {a b n m : Nat} (h1 : a < b) (h2 : b ≤ n) (h3 : n ≤ m) :
    a < m := by omega

private theorem bv_sub1_le_toNat {y : BitVec 64} {n m : Nat} (h0 : 0 < y.toNat) (h2 : y.toNat ≤ n)
    (h3 : n ≤ m) : (y - 1#64).toNat < m := by
  rw [bv64_sub1_toNat h0]; omega

private theorem bv_nle_lt_maxv {x c n : Nat} (h1 : ¬ c % 2 ^ 64 ≤ x) (h2 : c < 2 ^ 64)
    (h3 : c ≤ n) : x < n := by
  rw [Nat.mod_eq_of_lt h2] at h1; omega

private theorem with_abs_full_upd_flags {c : FullCfg} {R : Mem 64 → Prop} {m : Mem 64} {G : Prop}
    {s0 : FullState} {fl0 : List (BitVec 32)}
    (hm : (FullMem c { s0 with core := { s0.core with flags := fl0 } } ⋆ R) m)
    (hl0 : fl0.length = c.max_vars)
    (k : ∀ (s1 : FullState) (fl : List (BitVec 32)),
      s1.core = { s0.core with flags := fl } → s1.scratch = s0.scratch →
      fl.length = c.max_vars → (FullMem c s1 ⋆ R) m → G) : G :=
  k { s0 with core := { s0.core with flags := fl0 } } fl0 rfl rfl hl0 hm

private theorem fullProbeScratchPres_of_eq {s s1 : FullState} (h : s1.scratch = s.scratch) :
    FullProbeScratchPres s s1 :=
  ⟨⟨by rw [h], by rw [h]⟩, by rw [h], by rw [h], by rw [h], by rw [h], by rw [h],
    by rw [h], by rw [h]⟩

private abbrev s5InactSrchSt (s1 : FullState) (qsi qss : BitVec 64) : FullState :=
  { s1 with scratch := { s1.scratch with q_search_idx := qsi, q_search_stamp := qss } }

private theorem s5InactSrch_lengths {c : FullCfg} {s1 : FullState} {qsi qss : BitVec 64}
    (hl1 : s1.LengthsOk c) : (s5InactSrchSt s1 qsi qss).LengthsOk c :=
  ⟨hl1.core_ok, { hl1.scratch_ok with }⟩

private theorem s5InactSrch_pres {s s1 : FullState} {qsi qss : BitVec 64}
    (hp : FullProbeScratchPres s s1) : FullProbeScratchPres s (s5InactSrchSt s1 qsi qss) :=
  ⟨⟨hp.1.1, hp.1.2⟩, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2⟩

private abbrev s5InactQSt (s1 : FullState) (qp qn : List (BitVec 32))
    (qf ql : BitVec 64) : FullState :=
  { s1 with scratch := { s1.scratch with q_prev := qp, q_next := qn, q_first := qf, q_last := ql } }

private theorem s5InactQ_lengths {c : FullCfg} {s1 : FullState} {qp qn : List (BitVec 32)}
    {qf ql : BitVec 64} (hl1 : s1.LengthsOk c) (hqp : qp.length = c.max_vars)
    (hqn : qn.length = c.max_vars) : (s5InactQSt s1 qp qn qf ql).LengthsOk c :=
  ⟨hl1.core_ok, { hl1.scratch_ok with q_prev_len := hqp, q_next_len := hqn }⟩

private theorem s5InactQ_pres {s s1 : FullState} {qp qn : List (BitVec 32)}
    {qf ql : BitVec 64} (hp : FullProbeScratchPres s s1) :
    FullProbeScratchPres s (s5InactQSt s1 qp qn qf ql) :=
  ⟨⟨hp.1.1, hp.1.2⟩, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2⟩

private theorem s5InactVmtf_pres_of {s s1 : FullState} {qp qn : List (BitVec 32)}
    {qsi qss qf ql : BitVec 64} (hp : FullProbeScratchPres s s1) :
    FullProbeScratchPres s (s5InactVmtfSt s1 qp qn qsi qss qf ql) :=
  ⟨⟨hp.1.1, hp.1.2⟩, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2⟩

private theorem s5InactVmtf_pres {s s1 s2 : FullState} {qp qn : List (BitVec 32)}
    {qsi qss qf ql : BitVec 64} (hs1 : s1.scratch = s.scratch)
    (hs2 : s2 = s5InactVmtfSt s1 qp qn qsi qss qf ql) : FullProbeScratchPres s s2 := by
  subst hs2
  dsimp only [s5InactVmtfSt]
  exact ⟨⟨by rw [hs1], by rw [hs1]⟩, by rw [hs1], by rw [hs1], by rw [hs1],
    by rw [hs1], by rw [hs1], by rw [hs1], by rw [hs1]⟩

private theorem s5InactVmtf_lengths {c : FullCfg} {s1 s2 : FullState} {qp qn : List (BitVec 32)}
    {qsi qss qf ql : BitVec 64} (hl1 : s1.LengthsOk c)
    (hqp : qp.length = c.max_vars) (hqn : qn.length = c.max_vars)
    (hs2 : s2 = s5InactVmtfSt s1 qp qn qsi qss qf ql) : s2.LengthsOk c := by
  subst hs2
  exact ⟨hl1.core_ok, { hl1.scratch_ok with q_prev_len := hqp, q_next_len := hqn }⟩

private theorem bv64_sub1_idx (n : Nat) :
    (BitVec.ofNat 64 n - 1#64).toNat =
      (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + n) % 2 ^ 64 := by
  rw [BitVec.toNat_sub]; simp [BitVec.toNat_ofNat]

private theorem call_heap_up_spec {Q : Post []} {X : XPost} {c : FullCfg} {s0 : FullState}
    {R : Mem 64 → Prop} {m0 : Mem 64} {v : BitVec 32}
    (hm : (FullMem c s0 ⋆ R) m0) (hlen : s0.LengthsOk c)
    (hcont : ∀ (r : Tup Val []) (s' : FullState) (m' : Mem 64),
      PreservesCoreSlice (fullSafetySlice c).coreProj s0 s' →
      (fullSafetySlice c).safe s' →
      (FullProbeScratchPres s0 s' ∧
        ∃ hp' ps', s'.scratch = { s0.scratch with heap := hp', pos := ps' }) →
      ((fullSafetySlice c).mem s' ⋆ R) m' → Q r m') :
    fullHeapUpSpec (c.hdr, v, ()) m0 Q X :=
  ⟨c, s0, R, rfl, hlen, hm, hcont⟩

private theorem mk_inact_ex {c : FullCfg} {s s' : FullState} {k0 : FullCoreState}
    {R : Mem 64 → Prop} {m : Mem 64} {J : Cont []}
    (hJ : ∀ xs m, (∃ st : FullState, st.core = k0 ∧ st.LengthsOk c ∧
      FullProbeScratchPres s st ∧ (FullMem c st ⋆ R) m) → J xs m)
    (hm : (FullMem c s' ⋆ R) m) (hc : s'.core = k0) (hlen : s'.LengthsOk c)
    (hpres : FullProbeScratchPres s s') : J () m :=
  hJ () m ⟨s', hc, hlen, hpres, hm⟩

private theorem mk_inact_srch {c : FullCfg} {s s' s0 : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {J : Cont []}
    (hJ : ∀ xs m, (∃ st : FullState, st.core = s0.core ∧
      st.scratch.q_prev = s0.scratch.q_prev ∧ st.scratch.q_next = s0.scratch.q_next ∧
      st.LengthsOk c ∧ FullProbeScratchPres s st ∧ (FullMem c st ⋆ R) m) → J xs m)
    (hm : (FullMem c s' ⋆ R) m) (hc : s'.core = s0.core)
    (hqp : s'.scratch.q_prev = s0.scratch.q_prev)
    (hqn : s'.scratch.q_next = s0.scratch.q_next)
    (hlen : s'.LengthsOk c) (hpres : FullProbeScratchPres s s') : J () m :=
  hJ () m ⟨s', hc, hqp, hqn, hlen, hpres, hm⟩

private theorem call_heap_down_spec {Q : Post []} {X : XPost} {c : FullCfg} {s0 : FullState}
    {R : Mem 64 → Prop} {m0 : Mem 64} {v : BitVec 32}
    (hm : (FullMem c s0 ⋆ R) m0) (hlen : s0.LengthsOk c)
    (hcont : ∀ (r : Tup Val []) (s' : FullState) (m' : Mem 64),
      PreservesCoreSlice (fullSafetySlice c).coreProj s0 s' →
      (fullSafetySlice c).safe s' →
      (s'.scratch.heap_len = s0.scratch.heap_len ∧ FullProbeScratchPres s0 s') →
      ((fullSafetySlice c).mem s' ⋆ R) m' → Q r m') :
    fullHeapDownSpec (c.hdr, v, ()) m0 Q X :=
  ⟨c, s0, R, rfl, hlen, hm, hcont⟩

private theorem s5InactSwap_lengths {c : FullCfg} {s2 : FullState} {hl : Nat}
    {hp ps : List (BitVec 32)} (hl2 : s2.LengthsOk c) (hhp : hp.length = c.max_vars)
    (hps : ps.length = c.max_vars) :
    ({ s2 with scratch := { s2.scratch with heap_len := hl, heap := hp, pos := ps } }).LengthsOk
      c :=
  ⟨hl2.core_ok, { hl2.scratch_ok with heap_len_arr := hhp, pos_len := hps }⟩

private theorem s5InactSwap_pres {s s2 : FullState} {hl : Nat} {hp ps : List (BitVec 32)}
    (hp2 : FullProbeScratchPres s s2) :
    FullProbeScratchPres s
      { s2 with scratch := { s2.scratch with heap_len := hl, heap := hp, pos := ps } } :=
  ⟨⟨hp2.1.1, hp2.1.2⟩, hp2.2.1, hp2.2.2.1, hp2.2.2.2.1, hp2.2.2.2.2.1, hp2.2.2.2.2.2.1,
    hp2.2.2.2.2.2.2.1, hp2.2.2.2.2.2.2.2⟩

private theorem fullProbeScratchPres_trans' {a b d : FullState}
    (hab : FullProbeScratchPres a b) (hbd : FullProbeScratchPres b d) :
    FullProbeScratchPres a d :=
  fullProbeScratchPres_trans hab hbd

theorem full_set_inactive_wp (Γ : Env)
    (hUp : ∀ a m Q X, fullHeapUpSpec a m Q X →
      Γ "full_heap_up" [i64, i32] [] a m Q X)
    (hDown : ∀ a m Q X, fullHeapDownSpec a m Q X →
      Γ "full_heap_down" [i64, i32] [] a m Q X) :
    ∀ a m Q X, Spec.fullSetInactiveSpec a m Q X → Func.wp Γ full_set_inactive_body a m Q X := by
  rintro ⟨h, v, flag, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hcl := hlen.core_ok
  have hsc := hlen.scratch_ok
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hcl.cur_vars_le; have hfll := hcl.flags_len; have hvl := hcl.vals_len
  have hqpl := hsc.q_prev_len; have hqnl := hsc.q_next_len; have hqsl := hsc.q_stamp_len
  have hpl := hsc.pos_len; have hhl := hsc.heap_len_arr; have hdll := hsc.delayed_len_arr
  unfold Func.wp full_set_inactive_body
  c0_hfast_nogrp
  · rw [ite_eq_left (by c0_bound)] at hQ; exact hQ
  · have hv_lt : v.toNat < s.core.cur_vars := by c0_bound
    rw [ite_eq_right (by omega)] at hQ
    refine wp_join_group (fun (_ : Tup Val []) m1 =>
        ∃ (s1 : FullState) (unass1 : BitVec 64),
          s1.core = { s.core with unassigned := unass1 } ∧ s1.scratch = s.scratch ∧
          (FullMem c s1 ⋆ R) m1) ?_ (fun J hJ => ?_)
    · rintro _ ⟨⟩ m1 ⟨s1, unass1, hs1_c, hs1_sc, hm1⟩
      clear hm
      simp only [Blocks.get_here]
      have hlen1 : s1.LengthsOk c :=
        ⟨by rw [hs1_c]; exact { hcl with }, by rw [hs1_sc]; exact hsc⟩
      have hfl1 : s1.core.flags.length = c.max_vars := by rw [hs1_c]; exact hfll
      have hqp1 : s1.scratch.q_prev.length = c.max_vars := by rw [hs1_sc]; exact hqpl
      have hqn1 : s1.scratch.q_next.length = c.max_vars := by rw [hs1_sc]; exact hqnl
      have hqs1 : s1.scratch.q_stamp.length = c.max_vars := by rw [hs1_sc]; exact hqsl
      have hps1 : s1.scratch.pos.length = c.max_vars := by rw [hs1_sc]; exact hpl
      have hhl1 : s1.scratch.heap.length = c.max_vars := by rw [hs1_sc]; exact hhl
      have hdl1 : s1.scratch.delayed.length = 3 * c.delayed_cap := by rw [hs1_sc]; exact hdll
      have hv_fl1 : (BitVec.setWidth 64 v).toNat < s1.core.flags.length := by
        rw [hfl1, zext32_toNat]; exact Nat.lt_of_lt_of_le hv_lt hcv_le
      in_steps_nogrp_nb
      refine with_abs_full_upd_flags hm (by simp [hfl1])
        fun s1f fl1f hs1f_c hs1f_sc hfl1f hm1f => ?_
      clear hm
      have hs1f_sc' : s1f.scratch = s.scratch := by rw [hs1f_sc, hs1_sc]
      have hlen1f : s1f.LengthsOk c :=
        ⟨by rw [hs1f_c, hs1_c]; exact { hcl with flags_len := hfl1f },
         by rw [hs1f_sc']; exact hsc⟩
      have hpres1f : FullProbeScratchPres s s1f := fullProbeScratchPres_of_eq hs1f_sc'
      have hqp1f : s1f.scratch.q_prev.length = c.max_vars := by rw [hs1f_sc']; exact hqpl
      have hqn1f : s1f.scratch.q_next.length = c.max_vars := by rw [hs1f_sc']; exact hqnl
      have hqs1f : s1f.scratch.q_stamp.length = c.max_vars := by rw [hs1f_sc']; exact hqsl
      have hps1f : s1f.scratch.pos.length = c.max_vars := by rw [hs1f_sc']; exact hpl
      have hhl1f : s1f.scratch.heap.length = c.max_vars := by rw [hs1f_sc']; exact hhl
      have hdl1f : s1f.scratch.delayed.length = 3 * c.delayed_cap := by rw [hs1f_sc']; exact hdll
      have hv_qp1f : (BitVec.setWidth 64 v).toNat < s1f.scratch.q_prev.length := by
        rw [hqp1f, zext32_toNat]; exact Nat.lt_of_lt_of_le hv_lt hcv_le
      have hv_qn1f : (BitVec.setWidth 64 v).toNat < s1f.scratch.q_next.length := by
        rw [hqn1f, zext32_toNat]; exact Nat.lt_of_lt_of_le hv_lt hcv_le
      in_steps_nogrp_nb
      refine wp_join_group (fun (_ : Tup Val []) m2 =>
          ∃ (s2 : FullState) (fl2 : List (BitVec 32)),
            s2.core = { s.core with flags := fl2, unassigned := unass1 } ∧
            s2.LengthsOk c ∧ FullProbeScratchPres s s2 ∧ (FullMem c s2 ⋆ R) m2) ?_
        (fun Jv hJv => ?_)
      · rintro _ ⟨⟩ m2 ⟨s2, fl2, hs2_c, hlen2, hpres2, hm2⟩
        simp only [Blocks.get_here]
        have hfl2 : s2.core.flags.length = c.max_vars := hlen2.core_ok.flags_len
        have hps2 : s2.scratch.pos.length = c.max_vars := hlen2.scratch_ok.pos_len
        have hhl2 : s2.scratch.heap.length = c.max_vars := hlen2.scratch_ok.heap_len_arr
        have hdl2 : s2.scratch.delayed.length = 3 * c.delayed_cap :=
          hlen2.scratch_ok.delayed_len_arr
        have hv_pos2 : (BitVec.setWidth 64 v).toNat < s2.scratch.pos.length := by
          rw [hps2, zext32_toNat]; exact Nat.lt_of_lt_of_le hv_lt hcv_le
        in_steps_nogrp_nb
        refine wp_join_group (fun (_ : Tup Val []) m3 =>
            ∃ (s3 : FullState),
              s3.core = { s.core with flags := fl2, unassigned := unass1 } ∧
              s3.LengthsOk c ∧ FullProbeScratchPres s s3 ∧ (FullMem c s3 ⋆ R) m3) ?_
          (fun Jd hJd => ?_)
        · rintro _ ⟨⟩ m3 ⟨s3, hs3_c, hlen3, hpres3, hm3⟩
          simp only [Blocks.get_here]
          in_steps_nogrp_nb
          have hs3_eq : s3 =
              { core := { s.core with unassigned := unass1, flags := fl2 },
                scratch := s3.scratch } := by
            cases s3; simp only at hs3_c; rw [hs3_c]
          rw [hs3_eq] at hlen3 hpres3 hm3
          exact hQ fl2 unass1 s3.scratch m3 hlen3 hpres3 hm3
        · c0_hsplit_nobound
          · have hhl_gt0 : 0 < (BitVec.ofNat 64 s2.scratch.heap_len).toNat := by simpa using hc
            clear hc
            c0_hsplit_nobound
            · have hhl_le :
                  (BitVec.ofNat 64 s2.scratch.heap_len).toNat ≤
                    (BitVec.ofNat 64 s.core.cur_vars).toNat := hc
              clear hc
              have hcv64 : s.core.cur_vars < 2 ^ 64 :=
                Nat.lt_of_le_of_lt hcv_le (maxv_lt64 hmx)
              have hcv_m : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars :=
                bv64_ofNat_toNat hcv64
              c0_hsplit_nobound
              · have hidx_lt :
                    (BitVec.setWidth 64 s2.scratch.pos[(BitVec.setWidth 64 v).toNat]).toNat <
                      (BitVec.ofNat 64 s2.scratch.heap_len).toNat := hc
                clear hc
                have hposv_lt :
                    (BitVec.setWidth 64 s2.scratch.pos[(BitVec.setWidth 64 v).toNat]).toNat <
                      s2.scratch.heap.length := by
                  rw [hhl2]; rw [hcv_m] at hhl_le
                  exact bv_ult_le_toNat hidx_lt hhl_le hcv_le
                in_steps_nogrp_nb
                c0_hsplit_nobound
                · clear hc
                  have hhlen_sub_lt :
                      (BitVec.ofNat 64 s2.scratch.heap_len - 1#64).toNat <
                        s2.scratch.heap.length := by
                    rw [hhl2]; rw [hcv_m] at hhl_le
                    exact bv_sub1_le_toNat hhl_gt0 hhl_le hcv_le
                  in_steps_nogrp_nb
                  refine wp_join_group (fun (_ : Tup Val []) m2' =>
                      ∃ (s2' : FullState),
                        s2'.core = s2.core ∧ s2'.LengthsOk c ∧
                        FullProbeScratchPres s s2' ∧ (FullMem c s2' ⋆ R) m2') ?_
                    (fun Jhd hJhd => ?_)
                  · rintro _ ⟨⟩ m2' ⟨s2', hs2'_c, hlen2', hpres2', hm2'⟩
                    simp only [Blocks.get_here]
                    in_steps_nogrp_nb
                    exact hJd () _ ⟨s2', by rw [hs2'_c, hs2_c], hlen2', hpres2', hm2'⟩
                  · c0_hsplit_nobound
                    · clear hc
                      c0_hsplit_nobound
                      · have hlast_lt :
                            (BitVec.setWidth 64
                              s2.scratch.heap[(BitVec.ofNat 64
                                s2.scratch.heap_len - 1#64).toNat]).toNat <
                              s.core.cur_vars := by
                          have h1 := hc
                          rw [Nat.mod_eq_of_lt hcv64] at h1
                          simpa only [zext32_toNat, bv64_sub1_idx] using h1
                        clear hc
                        have hposv_lt2 :
                            (BitVec.setWidth 64
                              s2.scratch.pos[(BitVec.setWidth 64 v).toNat]).toNat <
                              s2.scratch.heap.length := hposv_lt
                        have hlast_pos :
                            (BitVec.setWidth 64
                              s2.scratch.heap[(BitVec.ofNat 64
                                s2.scratch.heap_len - 1#64).toNat]).toNat <
                              (s2.scratch.pos.set (BitVec.setWidth 64 v).toNat
                                4294967295#32).length := by
                          rw [List.length_set, hps2]
                          exact Nat.lt_of_lt_of_le hlast_lt hcv_le
                        in_steps_nogrp_nb
                        c0_hcall hUp
                        refine call_heap_up_spec hm ?_ ?_
                        · exact ⟨hlen2.core_ok, { hlen2.scratch_ok with
                            heap_len_arr := by rw [List.length_set, hhl2],
                            pos_len := by rw [List.length_set, List.length_set, hps2] }⟩
                        rintro ⟨⟩ su mu hcu hlsu ⟨hpru, _⟩ hmu
                        c0_hcall hDown
                        refine call_heap_down_spec hmu hlsu ?_
                        rintro ⟨⟩ sd md hcd hlsd ⟨_, hprd⟩ hmd
                        in_steps_nogrp_nb
                        dsimp only [PreservesCoreSlice, fullSafetySlice] at hcu hcd
                        exact hJhd () _ ⟨sd, hcd.trans hcu, hlsd,
                          fullProbeScratchPres_trans' hpres2
                            (fullProbeScratchPres_trans'
                              (s5InactSwap_pres (fullProbeScratchPres_refl s2))
                              (fullProbeScratchPres_trans' hpru hprd)),
                          hmd⟩
                      · in_steps_nogrp_nb
                        refine mk_inact_ex hJhd hm rfl ?_ (by exact hpres2)
                        exact ⟨hlen2.core_ok, { hlen2.scratch_ok with
                          pos_len := by rw [List.length_set, hps2] }⟩
                    · in_steps_nogrp_nb
                      refine mk_inact_ex hJhd hm rfl ?_ (by exact hpres2)
                      exact ⟨hlen2.core_ok, { hlen2.scratch_ok with
                        pos_len := by rw [List.length_set, hps2] }⟩
                · in_steps_nogrp_nb; exact hJd () _ ⟨s2, hs2_c, hlen2, hpres2, hm2⟩
              · in_steps_nogrp_nb; exact hJd () _ ⟨s2, hs2_c, hlen2, hpres2, hm2⟩
            · in_steps_nogrp_nb; exact hJd () _ ⟨s2, hs2_c, hlen2, hpres2, hm2⟩
          · in_steps_nogrp_nb; exact hJd () _ ⟨s2, hs2_c, hlen2, hpres2, hm2⟩
      · refine wp_join_group (fun (_ : Tup Val []) mq => (FullMem c s1f ⋆ R) mq) ?_
          (fun Jq hJq => ?_)
        · rintro _ ⟨⟩ mq1 hm1q
          clear hm1f
          simp only [Blocks.get_here]
          refine wp_join_group (fun (_ : Tup Val []) mq2 =>
              ∃ (s1s : FullState),
                s1s.core = s1f.core ∧ s1s.scratch.q_prev = s1f.scratch.q_prev ∧
                s1s.scratch.q_next = s1f.scratch.q_next ∧ s1s.LengthsOk c ∧
                FullProbeScratchPres s s1s ∧ (FullMem c s1s ⋆ R) mq2) ?_ (fun J2 hJ2 => ?_)
          · rintro _ ⟨⟩ mq2 ⟨s1s, hs1s_c, hs1s_qp, hs1s_qn, hlen1s, hpres1s, hm1s⟩
            simp only [Blocks.get_here]
            have hqp1s : (BitVec.setWidth 64 v).toNat < s1s.scratch.q_prev.length := by
              rw [hs1s_qp]; exact hv_qp1f
            have hqn1s : (BitVec.setWidth 64 v).toNat < s1s.scratch.q_next.length := by
              rw [hs1s_qn]; exact hv_qn1f
            in_steps_nogrp_nb
            refine wp_join_group (fun (_ : Tup Val []) mq3 =>
                ∃ (s1u : FullState),
                  s1u.core = s1f.core ∧ s1u.LengthsOk c ∧ FullProbeScratchPres s s1u ∧
                  (FullMem c s1u ⋆ R) mq3) ?_ (fun J3 hJ3 => ?_)
            · rintro _ ⟨⟩ mq3 ⟨s1u, hs1u_c, hlen1u, hpres1u, hm1u⟩
              simp only [Blocks.get_here]
              refine wp_join_group (fun (_ : Tup Val []) mq4 =>
                  ∃ (s1w : FullState),
                    s1w.core = s1f.core ∧ s1w.LengthsOk c ∧ FullProbeScratchPres s s1w ∧
                    (FullMem c s1w ⋆ R) mq4) ?_ (fun J4 hJ4 => ?_)
              · rintro _ ⟨⟩ mq4 ⟨s1w, hs1w_c, hlen1w, hpres1w, hm1w⟩
                simp only [Blocks.get_here]
                in_steps_nogrp_nb
                exact hJv () _ ⟨s1w, fl1f, by rw [hs1w_c, hs1f_c, hs1_c], hlen1w, hpres1w, hm1w⟩
              · c0_hsplit_nobound
                · clear hc
                  in_steps_nogrp_nb
                  refine mk_inact_ex hJ4 hm hs1u_c ?_ (by exact hpres1u)
                  exact ⟨hlen1u.core_ok, { hlen1u.scratch_ok with }⟩
                · have hqn_lt := hc
                  clear hc
                  have hqn_idx :
                      (BitVec.setWidth 64 s1f.scratch.q_next[(BitVec.setWidth 64 v).toNat]).toNat <
                        s1u.scratch.q_prev.length := by
                    rw [hlen1u.scratch_ok.q_prev_len, zext32_toNat]
                    exact bv_nle_lt_maxv hqn_lt (Nat.lt_of_le_of_lt hcv_le (maxv_lt64 hmx)) hcv_le
                  in_steps_nogrp_nb
                  refine mk_inact_ex hJ4 hm hs1u_c ?_ (by exact hpres1u)
                  exact ⟨hlen1u.core_ok, { hlen1u.scratch_ok with
                    q_prev_len := by rw [List.length_set, hlen1u.scratch_ok.q_prev_len] }⟩
            · c0_hsplit_nobound
              · clear hc
                in_steps_nogrp_nb
                refine mk_inact_ex hJ3 hm hs1s_c ?_ (by exact hpres1s)
                exact ⟨hlen1s.core_ok, { hlen1s.scratch_ok with
                  q_prev_len := by rw [List.length_set, hlen1s.scratch_ok.q_prev_len],
                  q_next_len := by rw [List.length_set, hlen1s.scratch_ok.q_next_len] }⟩
              · have hqp_lt := hc
                clear hc
                have hqp_idx :
                    (BitVec.setWidth 64 s1f.scratch.q_prev[(BitVec.setWidth 64 v).toNat]).toNat <
                      (s1s.scratch.q_next.set
                        (BitVec.setWidth 64 v).toNat 4294967295#32).length := by
                  rw [List.length_set, hlen1s.scratch_ok.q_next_len, zext32_toNat]
                  exact bv_nle_lt_maxv hqp_lt (Nat.lt_of_le_of_lt hcv_le (maxv_lt64 hmx)) hcv_le
                in_steps_nogrp_nb
                refine mk_inact_ex hJ3 hm hs1s_c ?_ (by exact hpres1s)
                exact ⟨hlen1s.core_ok, { hlen1s.scratch_ok with
                  q_prev_len := by rw [List.length_set, hlen1s.scratch_ok.q_prev_len],
                  q_next_len := by
                    rw [List.length_set, List.length_set, hlen1s.scratch_ok.q_next_len] }⟩
          · c0_hsplit_nobound
            · clear hc
              refine wp_join_group (fun (_ : Tup Val [i32]) mq3 => (FullMem c s1f ⋆ R) mq3) ?_
                (fun Js hJs => ?_)
              · rintro _ ⟨repl, ⟨⟩⟩ mq3 hm3
                clear hm1q
                simp only [Blocks.get_here]
                refine wp_join_group (fun (_ : Tup Val []) mq4 =>
                    ∃ (s1s : FullState),
                      s1s.core = s1f.core ∧ s1s.scratch.q_prev = s1f.scratch.q_prev ∧
                      s1s.scratch.q_next = s1f.scratch.q_next ∧ s1s.LengthsOk c ∧
                      FullProbeScratchPres s s1s ∧ (FullMem c s1s ⋆ R) mq4) ?_ (fun J2' hJ2' => ?_)
                · rintro _ ⟨⟩ mq4 h4
                  simp only [Blocks.get_here]
                  in_steps_nogrp_nb
                  exact hJ2 () _ h4
                · c0_hsplit_nobound
                  · clear hc
                    in_steps_nogrp_nb
                    refine mk_inact_srch hJ2' hm rfl rfl rfl ?_ (by exact hpres1f)
                    exact ⟨hlen1f.core_ok, { hlen1f.scratch_ok with }⟩
                  · have hrepl_lt := hc
                    clear hc
                    have hrepl_qs :
                        (BitVec.setWidth 64 repl).toNat < s1f.scratch.q_stamp.length := by
                      rw [hqs1f, zext32_toNat]
                      exact bv_nle_lt_maxv hrepl_lt
                        (Nat.lt_of_le_of_lt hcv_le (maxv_lt64 hmx)) hcv_le
                    in_steps_nogrp_nb
                    refine mk_inact_srch hJ2' hm rfl rfl rfl ?_ (by exact hpres1f)
                    exact ⟨hlen1f.core_ok, { hlen1f.scratch_ok with }⟩
              · in_hfast_nogrp_nb <;> exact hJs _ _ hm1q
            · in_steps_nogrp_nb; exact hJ2 () _ ⟨s1f, rfl, rfl, rfl, hlen1f, hpres1f, hm1q⟩
        · in_hfast_nogrp_nb <;> first
            | exact hJq () _ hm1f
            | exact hJv () _ ⟨s1f, fl1f, by rw [hs1f_c, hs1_c], hlen1f, hpres1f, hm1f⟩
    · c0_hfast <;> first
        | exact hJ () _
            ⟨{ s with core := { s.core with unassigned := s.core.unassigned - 1 } },
              _, rfl, rfl, by assumption⟩
        | exact hJ () _ ⟨s, s.core.unassigned, (core_upd_unass_self s.core).symm, rfl, hm⟩

end SetInactive

end LeanQbe.T.Examples.Kissat.Proof.Internal