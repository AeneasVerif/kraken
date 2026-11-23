module

public import LeanQbe.T.Examples.Kissat.FullM6Orch
public import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
public import LeanQbe.T.Examples.Kissat.FullM6SatSound
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof2
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
public import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof1
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof
public import LeanQbe.T.Examples.Kissat.FullM6CompactFlushProof1
public import LeanQbe.T.Examples.Kissat.FullSpec1
public import LeanQbe.T.Examples.Kissat.FullSpec2
public import LeanQbe.T.Examples.Kissat.FullSpec3
public import LeanQbe.T.Examples.Kissat.FullM3BackboneLemmas1
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
public import LeanQbe.T.Examples.Kissat.FullFastSchedLemmas
public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas1
public import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas1
public import LeanQbe.T.Examples.Kissat.FullM4CompactLemmas

import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas1
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.WPLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `M6.0` Orchestration Proofs Part 1 (`FullM6OrchProof1`)

M1-clean proof module (plain `public section`, opaque specs, `0` `@[expose]`):
Proves parametric `(Γ : Env)` `Func.wp` contracts for the `4` Group-1 `FullM6Orch` functions
and the `full_preprocess` forwarding shim:
1. `full_probe_tail_m6_wp` (`m6ProbeTailSpec`)
2. `full_probe_m6_wp` (`m6ProbeSpec`)
3. `full_preprocess_m6_wp` (`fullM6PreprocessSpec`)
4. `full_preprocess_fwd_wp` (`fullM6PreprocessSpec` forwarding shim for `full_preprocess`)
5. `full_simplify_m6_wp` (`fullM6SimplifySpec`)
6. `full_reduce_m6_wp` (`m6ReduceSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Orch

open Std Std.Sat Std.ExtHashMap LeanQbe.T.Examples.LratBytes
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6ProofUtil.M6ProofUtilTactics

/-! ## 1. Probing Contracts (`m6ProbeTailSpec`, `m6ProbeSpec`) -/

def m6ProbeTailSpec : Spec [i64, i64] [i64] := fun (h, _dticks, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ s.core.cur_level = 0 ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

theorem m6ProbeTailSpec_of {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {dticks : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hinv : FullM6HdrInv c F0 ext s) (hcl0 : s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ r ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    m6ProbeTailSpec (c.hdr, dticks, ()) m Q X :=
  ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩

theorem m6ProbeTailSpec_elim {h dticks : BitVec 64} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (hs : m6ProbeTailSpec (h, dticks, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ s.core.cur_level = 0 ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' s' m',
        s'.LengthsOk c → M6HdrExtOk ext' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m' := hs

theorem m6ProbeTailSpec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : m6ProbeTailSpec xs m Q X) : m6ProbeTailSpec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

def m6ProbeSpec : Spec [i64, .bool] [i64] := fun (h, _initial, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ s.core.cur_level = 0 ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

theorem m6ProbeSpec_of {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {initial : Bool} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hinv : FullM6HdrInv c F0 ext s) (hcl0 : s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ r ext' s' m',
      s'.LengthsOk c → M6HdrExtOk ext' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    m6ProbeSpec (c.hdr, initial, ()) m Q X :=
  ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩

theorem m6ProbeSpec_elim {h : BitVec 64} {initial : Bool} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hs : m6ProbeSpec (h, initial, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ s.core.cur_level = 0 ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' s' m',
        s'.LengthsOk c → M6HdrExtOk ext' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (r = 1#64 → FullM6HdrInv c F0 ext' s' ∧ s'.core.cur_level = 0) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m' := hs

theorem m6ProbeSpec_monoX {xs : Tup Val [i64, .bool]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : m6ProbeSpec xs m Q X) : m6ProbeSpec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

/-! ## 2. Private Probing & Compact Helpers -/

private theorem m6o1_probe_ret_wm {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s0 s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {r : BitVec 64} {Q : Post [i64]} {X : XPost}
    {args : Tup (Arg Val) [i64, i64, i64]}
    {k : Tup Val [] → Expr Val Cont [i64]}
    (hk_ret : k () = .ret (Arg.imm r, ()))
    (hargs : vals args = (c.hdr, 0#64, BitVec.ofNat 64 s.scratch.search_ticks.toNat, ()) ∨
      vals args = (c.hdr, 0#64, s.scratch.search_ticks, ()))
    (hSetWm : ∀ a m' Q' X', m6HdrW2aSpec [i64, i64] [] a m' Q' X' →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m' Q' X')
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

private theorem m6o1_dense_inconsistent_unsat {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s : FullState} (_hcfg : FullM6HdrCfgOk c)
    (_hext : M6HdrExtOk ext) (hd : FullDenseInv c F0 s)
    (hinc : s.core.inconsistent ≠ 0#64) : F0.Unsat := by
  obtain ⟨F_cur, hw⟩ := hd.1.witness
  exact hw.ext_sound.2 (hw.inconsistent_sound hinc)

private theorem m6o1_fullInv_of_backtrack0 {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s : FullState}
    (hinv : FullM6HdrInv c F0 ext s) :
    s.core.cur_level < 2 ^ 64 ∧
    ((0#64 : BitVec 64).toNat < s.core.cur_level → (0#64 : BitVec 64).toNat < c.max_vars) ∧
    (∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) := by
  obtain ⟨_, hw⟩ := hinv.sparse.1.witness
  have hmax := c.hmaxv; unfold dimacsBound at hmax
  have hte := hinv.sparse.lengths.core_ok.trail_end_le
  have hcv := hinv.sparse.lengths.core_ok.cur_vars_le
  have hcl := hw.cur_level_le
  exact ⟨by omega, fun _ => by omega, hw.trail_lits_lt⟩

private theorem m6o1_conflict_level0_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hl0 : s.core.cur_level = 0)
    (hc : FullConflictOkW F_cur s) : F0.Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨_, href, hng, hfals⟩
  · refine hw.ext_sound.2
      (unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => Or.inr ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h0lt).mp hf0
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h1lt).mp hf1
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
  · refine hw.ext_sound.2 (unsat_of_entails_nil
      (entails_of_mem_or_false (hw.arena.entails _ href hng) fun l hl => Or.inr ?_))
    obtain ⟨i, hi, hieq⟩ :=
      (hw.vals_false_iff l (hw.arena.lits_lt _ href hng l hl)).mp (hfals l hl)
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs

/-! ## 3. `full_probe_tail_m6_wp` (`m6ProbeTailSpec`) -/

theorem full_probe_tail_m6_wp (Γ : Env)
    (hBackbone : ∀ a m Q X, FullM3Backbone.fullBackboneSpec a m Q X →
      Γ "full_backbone_m6" [i64, i64] [i64] a m Q X)
    (hTrans : ∀ a m Q X, FullFastBveBudgets.fullTransitiveFastSpec a m Q X →
      Γ "full_transitive_m6" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hProbeRun : ∀ a m Q X, FullM3Backbone.fullProbeRunCursorSpec a m Q X →
      Γ "full_probe_run" [i64, i64] [i64] a m Q X)
    (hViv : ∀ a m Q X, FullM6OrchAdapters.m6aVivifySpec a m Q X →
      Γ "full_vivify_m6_hdr" [i64] [i64] a m Q X) :
    ∀ a m Q X, m6ProbeTailSpec a m Q X →
      Func.wp Γ full_probe_tail_m6_body a m Q X := by
  rintro ⟨h, dticks, ⟨⟩⟩ m Q X hs
  rcases m6ProbeTailSpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, _hcl0, hm, hQ⟩
  unfold Func.wp full_probe_tail_m6_body
  refine wp_join_group (ts := []) (fun _ m1 => ∃ s1, FullM6HdrInv c F0 ext s1 ∧
      s1.core.cur_level = 0 ∧ s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      (FullM6HdrMem c ext s1 ⋆ R) m1) ?_ ?_
  · rintro _ _ m1 ⟨s1, hinv1, _hcl1, hfu1, hm1⟩
    c0_hsteps_nogrp
    refine wp_join_group (ts := []) (fun _ m2 => ∃ s2, FullM6HdrInv c F0 ext s2 ∧
        s2.core.cur_level = 0 ∧ s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullM6HdrMem c ext s2 ⋆ R) m2) ?_ ?_
    · rintro _ _ m2 ⟨s2, hinv2, _hcl2, hfu2, hm2⟩
      c0_hsteps_nogrp; c0_call hMin; intro pbud _; c0_hsteps_nogrp
      refine wp_join_group (ts := []) (fun _ m3 => ∃ s3, FullM6HdrInv c F0 ext s3 ∧
          s3.core.cur_level = 0 ∧ s3.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          (FullM6HdrMem c ext s3 ⋆ R) m3) ?_ ?_
      · rintro _ _ m3 ⟨s3, hinv3, _hcl3, hfu3, hm3⟩
        c0_hsteps_nogrp; c0_call hViv
        refine FullM6OrchAdapters.m6aVivifySpec_of hinv3.cfgOk hinv3.extOk hinv3.sparse hm3
          fun r4 ext4 s4 m4 ⟨hext4, _⟩ hsp4 ⟨hcl4, _⟩ hfu4 hdom4 hu4 hm4 => ?_
        have hinv4 := FullM6HdrInv.mk_inv hinv3.cfgOk hext4 hsp4
        c0_hsteps_nogrp
        · exact hQ 20#64 ext4 s4 m4 hsp4.lengths hext4 (Nat.le_trans hfu4 hfu3)
            (Or.inr rfl) (fun _ => hu4 ‹_›) (fun h => by cases h) hm4
        · exact hQ 1#64 ext4 s4 m4 hsp4.lengths hext4 (Nat.le_trans hfu4 hfu3)
            (Or.inl rfl) (fun h => by cases h) (fun _ => ⟨hinv4, hcl4⟩) hm4
      · intro J3 hJ3
        refine wp_m6Hdr_focus_frame hm2 fun hm2f => ?_
        c0_hsteps_nogrp
        · c0_call hProbeRun
          refine ⟨c, F0, s2, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv2.sparse, hm2f,
            fun r3 s3 m3 hsp3 hcl3 _ hfu3 hdom3 hu3 _ hm3 => ?_⟩
          have hinv3 := FullM6HdrInv.mk_inv hinv2.cfgOk hinv2.extOk hsp3
          have hm3' := fullM6HdrMem_unfocus hm3
          c0_hsteps_nogrp
          · exact hQ 20#64 ext s3 m3 hsp3.lengths hinv3.extOk (Nat.le_trans hfu3 hfu2)
              (Or.inr rfl) (fun _ => hu3 ‹_›) (fun h => by cases h) hm3'
          · exact hJ3 () m3 ⟨s3, hinv3, hcl3, Nat.le_trans hfu3 hfu2, hm3'⟩
        · exact hJ3 () m2 ⟨s2, hinv2, _hcl2, hfu2, hm2⟩
    · intro J2 hJ2
      refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
      c0_hsteps_nogrp
      · c0_call hTrans
        refine ⟨c, F0, s1, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv1.sparse, hm1f,
          fun r2 s2 m2 hsp2 hcl2 _ _ hfu2 hdom2 hu2 hm2 => ?_⟩
        have hinv2 := FullM6HdrInv.mk_inv hinv1.cfgOk hinv1.extOk hsp2
        have hm2' := fullM6HdrMem_unfocus hm2
        c0_hsteps_nogrp
        · exact hQ 20#64 ext s2 m2 hsp2.lengths hinv2.extOk (Nat.le_trans hfu2 hfu1)
            (Or.inr rfl) (fun _ => hu2 ‹_›) (fun h => by cases h) hm2'
        · exact hJ2 () m2 ⟨s2, hinv2, hcl2 _hcl1, Nat.le_trans hfu2 hfu1, hm2'⟩
      · exact hJ2 () m1 ⟨s1, hinv1, _hcl1, hfu1, hm1⟩
  · intro J1 hJ1
    refine wp_m6Hdr_focus_frame hm fun hmf => ?_
    c0_hsteps_nogrp
    · c0_call hBackbone
      refine ⟨c, F0, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv.sparse, hmf,
        fun r1 s1 m1 hsp1 hcl1 _ hfu1 hdom1 hu1 hm1 => ?_⟩
      have hinv1 := FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk hsp1
      have hm1' := fullM6HdrMem_unfocus hm1
      c0_hsteps_nogrp
      · exact hQ 20#64 ext s1 m1 hsp1.lengths hinv1.extOk hfu1
          (Or.inr rfl) (fun _ => hu1 ‹_›) (fun h => by cases h) hm1'
      · exact hJ1 () m1 ⟨s1, hinv1, hcl1, hfu1, hm1'⟩
    · exact hJ1 () m ⟨s, hinv, _hcl0, Nat.le_refl _, hm⟩

/-! ## 4. `full_probe_m6_wp` (`m6ProbeSpec`) -/

theorem full_probe_m6_wp (Γ : Env)
    (hDticks : ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Γ "full_probe_dticks_m6_hdr" [i64, .bool] [i64] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hCong : ∀ a m Q X, FullM3CongBva.m3CongruenceDenseSpec a m Q X →
      Γ "full_congruence_dense" [i64, i64] [i64] a m Q X)
    (hRebuild : ∀ a m Q X, Full.fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hRedD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    (hBumpD : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hSweep : ∀ a m Q X, FullDefSweep.fullSweepDenseSpec a m Q X →
      Γ "full_sweep_dense_m6" [i64, i64, i64] [i64] a m Q X)
    (hSubst : ∀ a m Q X, Full.fullSubstituteSpec a m Q X →
      Γ "full_substitute" [i64] [i64] a m Q X)
    (hTail : ∀ a m Q X, m6ProbeTailSpec a m Q X →
      Γ "full_probe_tail_m6" [i64, i64] [i64] a m Q X)
    (hBackbone : ∀ a m Q X, FullM3Backbone.fullBackboneSpec a m Q X →
      Γ "full_backbone_m6" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hFactor : ∀ a m Q X, FullM3CongBva.fullFactorHeapSpec a m Q X →
      Γ "full_factor" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m6ProbeSpec a m Q X →
      Func.wp Γ full_probe_m6_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X hs
  rcases m6ProbeSpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_probe_m6_body
  c0_hsteps_nogrp
  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hDticks _ _ _ _ h)
    hinv.cfgOk hinv.extOk hinv.sparse.lengths hm
    fun ⟨dticks, ⟨⟩⟩ ext0 s0 m0 hc0 hlen0 hms0 hext0 _ hm0 => ?_
  have hinv0 := fullM6HdrInv_with_ext (fullM6HdrInv_of_m6Pres hinv hlen0 hc0 hms0) hext0
  have hcl0' : s0.core.cur_level = 0 := by rw [hc0]; exact hcl0
  -- Join after optional `!initial` `probings` / `probe_limit` update.
  refine wp_join_group (ts := []) (fun _ m1 => ∃ ext1 s1, FullM6HdrInv c F0 ext1 s1 ∧
      s1.core.cur_level = 0 ∧ s1.core.fuel = s.core.fuel ∧ (FullM6HdrMem c ext1 s1 ⋆ R) m1) ?_ ?_
  · rintro _ _ m1 ⟨ext1, s1, hinv1, hcl1, hfu1, hm1⟩
    c0_hsteps_nogrp
    -- Round loop (`while (round < 2ULL)`).
    refine wp_join_group (ts := [i64]) (fun _ mW => ∃ extW sW, FullM6HdrInv c F0 extW sW ∧
        sW.core.cur_level = 0 ∧ sW.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullM6HdrMem c extW sW ⋆ R) mW) ?_ ?_
    · rintro _ ⟨_, ⟨⟩⟩ mW ⟨extW, sW, hinvW, hclW, hfuW, hmW⟩
      c0_hsteps_nogrp
      -- Join after `if (!initial)` `full_probe_tail_m6` / `full_backbone_m6`.
      refine wp_join_group (ts := []) (fun _ mT => ∃ extT sT, FullM6HdrInv c F0 extT sT ∧
          sT.core.cur_level = 0 ∧ sT.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          (FullM6HdrMem c extT sT ⋆ R) mT) ?_ ?_
      · rintro _ _ mT ⟨extT, sT, hinvT, hclT, hfuT, hmT⟩
        c0_hsteps_nogrp
        refine wp_join_group (ts := []) (fun _ mRet => ∃ extRet sRet,
            FullM6HdrInv c F0 extRet sRet ∧ sRet.core.cur_level = 0 ∧
            sRet.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extRet sRet ⋆ R) mRet)
          (?_ ) (?_ )
        · rintro _ _ mRet ⟨extRet, sRet, hinvRet, hclRet, hfuRet, hmRet⟩
          refine wp_m6Hdr_focus_frame hmRet fun hmRetf => ?_
          c0_hsteps_nogrp
          exact m6o1_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvRet.cfgOk hinvRet.extOk
            hinvRet.sparse.lengths hfuRet (Or.inl rfl) (fun h => by cases h)
            (fun _ => ⟨hinvRet, hclRet⟩) (fullM6HdrMem_unfocus hmRetf) (hQ 1#64)
        · intro Jret hJret; c0_hsteps_nogrp
          refine wp_join_group (ts := []) (fun _ mInc => ∃ extInc sInc,
              FullM6HdrInv c F0 extInc sInc ∧ sInc.core.cur_level = 0 ∧
              sInc.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extInc sInc ⋆ R) mInc)
            (?_ ) (?_ )
          · rintro _ _ mInc ⟨extInc, sInc, hinvInc, hclInc, hfuInc, hmInc⟩
            refine wp_m6Hdr_focus_frame hmInc fun hmIncf => ?_
            c0_hsteps_nogrp
            · exact m6o1_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvInc.cfgOk hinvInc.extOk
                hinvInc.sparse.lengths hfuInc (Or.inr rfl)
                (fun _ => fullM6HdrInv_inconsistent_unsat hinvInc ‹_›)
                (fun h => by cases h) (fullM6HdrMem_unfocus hmIncf) (hQ 20#64)
            · exact hJret () mInc
                ⟨extInc, sInc, hinvInc, hclInc, hfuInc, fullM6HdrMem_unfocus hmIncf⟩
          · intro Jinc hJinc; c0_hsteps_nogrp
            refine wp_join_group (ts := []) (fun _ mF0 => ∃ extF0 sF0,
                FullM6HdrInv c F0 extF0 sF0 ∧ sF0.core.cur_level = 0 ∧
                sF0.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extF0 sF0 ⋆ R) mF0)
              (?_ ) (?_ )
            · rintro _ _ mF0 ⟨extF0, sF0, hinvF0, hclF0, hfuF0, hmF0⟩
              refine wp_m6Hdr_focus_frame hmF0 fun hmTf => ?_
              c0_hsteps_nogrp
              · c0_call hEnter
                refine ⟨c, F0, sF0, m6ExtMem (m6ExtAddr c.hdr) extF0 ⋆ R, rfl, hinvF0.sparse,
                  hmTf, fun ok sF mF hclF hfuF hdenF hspF hmF => ?_⟩
                have hmF' := fullM6HdrMem_unfocus hmF
                c0_hsteps_nogrp
                · have hdenF' := hdenF ‹_›
                  refine wp_join_group (ts := [i64]) (fun _ mB => mB = mF)
                    (fun _ ⟨fbud0, ⟨⟩⟩ mB hmB => by
                      subst hmB
                      c0_hsteps_nogrp; c0_call hMin; intro fbud _; c0_hsteps_nogrp
                      c0_call hFactor
                      refine ⟨c, F0, sF, m6ExtMem (m6ExtAddr c.hdr) extF0 ⋆ R, rfl, hdenF',
                        hmF, fun _ sFc mFc hdenFc _ hfuFc _ hmFc => ?_⟩
                      c0_hsteps_nogrp; c0_call hRebuild
                      refine ⟨c, F0, sFc, m6ExtMem (m6ExtAddr c.hdr) extF0 ⋆ R, rfl, hdenFc,
                        hmFc, fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                      have hinvR := FullM6HdrInv.mk_inv hinvF0.cfgOk hinvF0.extOk hspR
                      have hmR' := fullM6HdrMem_unfocus hmR
                      have hfuR' : sR.core.fuel.toNat ≤ s.core.fuel.toNat := by
                        rw [hfuFc] at hfuR; exact Nat.le_trans hfuR (Nat.le_trans hfuF hfuF0)
                      c0_hsteps_nogrp
                      · refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                        c0_hsteps_nogrp
                        exact m6o1_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                          hinvR.sparse.lengths hfuR' (Or.inr rfl) (fun _ => huR ‹_›)
                          (fun h => by cases h) (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                      · exact hJret () mR ⟨extF0, sR, hinvR, hclR, hfuR', hmR'⟩)
                    (fun _ hJ0 => by c0_hsteps_nogrp <;> exact hJ0 (_, ()) mF rfl)
                · have hinvF := FullM6HdrInv.mk_inv hinvF0.cfgOk hinvF0.extOk (hspF ‹_›)
                  exact hJinc () mF ⟨extF0, sF, hinvF, hclF, Nat.le_trans hfuF hfuF0, hmF'⟩
            · intro Jfact hJfact
              refine wp_m6Hdr_focus_frame hmT fun hmTf => ?_
              c0_hsteps_nogrp
              · exact hJfact () mT ⟨extT, sT, hinvT, hclT, hfuT, fullM6HdrMem_unfocus hmTf⟩
              · exact hJfact () mT ⟨extT, sT, hinvT, hclT, hfuT, fullM6HdrMem_unfocus hmTf⟩
              · exact hJinc () mT ⟨extT, sT, hinvT, hclT, hfuT, fullM6HdrMem_unfocus hmTf⟩
      · intro JT hJT; c0_hsteps_nogrp
        · refine wp_m6Hdr_focus_frame hmW fun hmWf => ?_
          c0_hsteps_nogrp
          · c0_call hBackbone
            refine ⟨c, F0, sW, m6ExtMem (m6ExtAddr c.hdr) extW ⋆ R, rfl, hinvW.sparse, hmWf,
              fun rB sB mB hspB hclB _ hfuB hdB huB hmB => ?_⟩
            have hinvB := FullM6HdrInv.mk_inv hinvW.cfgOk hinvW.extOk hspB
            have hmB' := fullM6HdrMem_unfocus hmB
            c0_hsteps_nogrp
            · refine wp_m6Hdr_focus_frame hmB' fun hmBf => ?_
              c0_hsteps_nogrp
              exact m6o1_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvB.cfgOk hinvB.extOk
                hinvB.sparse.lengths (Nat.le_trans hfuB hfuW) (Or.inr rfl)
                (fun _ => huB ‹_›) (fun h => by cases h) (fullM6HdrMem_unfocus hmBf) (hQ 20#64)
            · exact hJT () mB ⟨extW, sB, hinvB, hclB, Nat.le_trans hfuB hfuW, hmB'⟩
          · exact hJT () mW ⟨extW, sW, hinvW, hclW, hfuW, fullM6HdrMem_unfocus hmWf⟩
        · c0_call hTail
          refine m6ProbeTailSpec_of hinvW hclW hmW
            fun rT extT sT mT hlT heT hfuT hdT huT h1T hmT => ?_
          c0_hsteps_nogrp
          · refine wp_m6Hdr_focus_frame hmT fun hmTf => ?_
            c0_hsteps_nogrp
            exact m6o1_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvW.cfgOk heT hlT
              (Nat.le_trans hfuT hfuW) (Or.inr rfl) (fun _ => huT ‹_›)
              (fun h => by cases h) (fullM6HdrMem_unfocus hmTf) (hQ 20#64)
          · exact hJT () mT ⟨extT, sT, (h1T (hdT.resolve_right ‹_›)).1,
              (h1T (hdT.resolve_right ‹_›)).2, Nat.le_trans hfuT hfuW, hmT⟩
    · intro JW hJW; c0_hsteps_nogrp
      refine wp_loop_inv (fun (round, ()) mL => round.toNat ≤ 2 ∧
          ∃ extL sL, FullM6HdrInv c F0 extL sL ∧ sL.core.cur_level = 0 ∧
            sL.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extL sL ⋆ R) mL)
        (fun (round, ()) _ => 2 - round.toNat)
        (fun JL hJL => by
          c0_hsteps_nogrp
          exact hJL (0#64, ()) m1 ⟨Nat.zero_le _, ext1, s1, hinv1, hcl1,
            by rw [hfu1]; exact Nat.le_refl _, hm1⟩)
        (fun JL (round, ()) mL ⟨hnd_le, extL, sL, hinvL, hclL, hfuL, hmL⟩ hJL => ?_)
      · refine wp_m6Hdr_focus_frame hmL fun hmLf => ?_
        c0_hsteps_nogrp
        · have hnd_lt : round.toNat < 2 := BitVec.lt_def.mp ‹_›
          have hnd1 : (round + 1#64).toNat = round.toNat + 1 := by bv_omega
          let before_unass := sL.core.unassigned
          -- Join after dense pass (`full_enter_dense` / `inconsistent`).
          refine wp_join_group (ts := []) (fun _ mD => ∃ extD sD, FullM6HdrInv c F0 extD sD ∧
              sD.core.cur_level = 0 ∧ sD.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullM6HdrMem c extD sD ⋆ R) mD) ?_ ?_
          · rintro _ _ mD ⟨extD, sD, hinvD, hclD, hfuD, hmD⟩
            c0_hsteps_nogrp
            -- Join after `full_substitute`.
            refine wp_join_group (ts := []) (fun _ mS => ∃ extS sS, FullM6HdrInv c F0 extS sS ∧
                sS.core.cur_level = 0 ∧ sS.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                (FullM6HdrMem c extS sS ⋆ R) mS) ?_ ?_
            · rintro _ _ mS ⟨extS, sS, hinvS, hclS, hfuS, hmS⟩
              refine wp_m6Hdr_focus_frame hmS fun hmSf => ?_
              c0_hsteps_nogrp
              · exact hJW (round, ()) mS ⟨extS, sS, hinvS, hclS, hfuS, fullM6HdrMem_unfocus hmSf⟩
              · exact hJL (round + 1#64, ()) mS (by dsimp only; omega)
                  ⟨by omega, extS, sS, hinvS, hclS, hfuS, fullM6HdrMem_unfocus hmSf⟩
            · intro JS hJS; refine wp_m6Hdr_focus_frame hmD fun hmDf => ?_
              c0_hsteps_nogrp
              · c0_call hSubst
                refine ⟨c, F0, sD, m6ExtMem (m6ExtAddr c.hdr) extD ⋆ R, rfl, hinvD.sparse, hmDf,
                  fun rS sS mS hspS hclS hfuS hdS huS hmS => ?_⟩
                have hinvS := FullM6HdrInv.mk_inv hinvD.cfgOk hinvD.extOk hspS
                have hmS' := fullM6HdrMem_unfocus hmS
                c0_hsteps_nogrp
                · refine wp_m6Hdr_focus_frame hmS' fun hmSf => ?_
                  c0_hsteps_nogrp
                  exact m6o1_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvS.cfgOk hinvS.extOk
                    hinvS.sparse.lengths (Nat.le_trans hfuS hfuD) (Or.inr rfl)
                    (fun _ => huS ‹_›) (fun h => by cases h) (fullM6HdrMem_unfocus hmSf) (hQ 20#64)
                · exact hJS () mS ⟨extD, sS, hinvS, hclS, Nat.le_trans hfuS hfuD, hmS'⟩
              · exact hJS () mD ⟨extD, sD, hinvD, hclD, hfuD, fullM6HdrMem_unfocus hmDf⟩
          · intro JD hJD
            c0_hsteps_nogrp; c0_call hEnter
            refine ⟨c, F0, sL, m6ExtMem (m6ExtAddr c.hdr) extL ⋆ R, rfl, hinvL.sparse, hmLf,
              fun ok sE mE hclE hfuE hdenE hspE hmE => ?_⟩
            have hmE' := fullM6HdrMem_unfocus hmE
            c0_hsteps_nogrp
            · have hdenE' := hdenE ‹_›
              -- Congruence step (`m6_hdr_delaying(0)`).
              refine wp_join_group (ts := []) (fun _ mC => ∃ extC sC,
                  FullM6HdrCfgOk c ∧ M6HdrExtOk extC ∧ FullDenseInv c F0 sC ∧
                  sC.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                  (FullM6HdrMem c extC sC ⋆ R) mC) ?_ ?_
              · rintro _ _ mC ⟨extC, sC, _, hextC, hdenC, hfuC, hmC⟩
                c0_hsteps_nogrp
                -- Sweep step (`m6_hdr_delaying(1)`).
                refine wp_join_group (ts := []) (fun _ mW2 => ∃ extW2 sW2,
                    FullM6HdrCfgOk c ∧ M6HdrExtOk extW2 ∧ FullDenseInv c F0 sW2 ∧
                    sW2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                    (FullM6HdrMem c extW2 sW2 ⋆ R) mW2) ?_ ?_
                · rintro _ _ mW2 ⟨extW2, sW2, _, hextW2, hdenW2, hfuW2, hmW2⟩
                  refine wp_m6Hdr_focus_frame hmW2 fun hmW2f => ?_
                  c0_hsteps_nogrp; c0_call hRebuild
                  refine ⟨c, F0, sW2, m6ExtMem (m6ExtAddr c.hdr) extW2 ⋆ R, rfl, hdenW2, hmW2f,
                    fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                  have hinvR := FullM6HdrInv.mk_inv hinvL.cfgOk hextW2 hspR
                  have hmR' := fullM6HdrMem_unfocus hmR
                  have hfuR' := Nat.le_trans hfuR hfuW2
                  c0_hsteps_nogrp
                  · refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                    c0_hsteps_nogrp
                    exact m6o1_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                      hinvR.sparse.lengths hfuR' (Or.inr rfl) (fun _ => huR ‹_›)
                      (fun h => by cases h) (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                  · exact hJD () mR ⟨extW2, sR, hinvR, hclR, hfuR', hmR'⟩
                · intro JW2 hJW2
                  refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hDelay _ _ _ _ h)
                    hinvL.cfgOk hextC hdenC.lengths hmC
                    fun ⟨del2, ⟨⟩⟩ extCd sCd mCd hcCd hlCd hmsCd hextCd _ hmCd => ?_
                  have hdenCd := fullDenseInv_of_core_eq hdenC hlCd hcCd hmsCd.extPres
                  have hfuCd : sCd.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hcCd]; exact hfuC
                  c0_hsteps_nogrp
                  · exact hJW2 () mCd ⟨extCd, sCd, hinvL.cfgOk, hextCd, hdenCd, hfuCd, hmCd⟩
                  · refine wp_m6Hdr_focus_frame hmCd fun hmCdf => ?_
                    c0_hsteps_nogrp; c0_call hSweep
                    refine ⟨c, F0, sCd, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl, hdenCd,
                      hmCdf, fun rS sS mS hdenS _ hfuS _ huS hmS => ?_⟩
                    have hfuS' := Nat.le_trans hfuS hfuCd
                    c0_hsteps_nogrp
                    · c0_call hRebuild
                      refine ⟨c, F0, sS, m6ExtMem (m6ExtAddr c.hdr) extCd ⋆ R, rfl, hdenS, hmS,
                        fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                      have hinvR := FullM6HdrInv.mk_inv hinvL.cfgOk hextCd hspR
                      have hmR' := fullM6HdrMem_unfocus hmR
                      refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                      c0_hsteps_nogrp
                      exact m6o1_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                        hinvR.sparse.lengths (Nat.le_trans hfuR hfuS') (Or.inr rfl)
                        (fun _ => huS ‹_›) (fun h => by cases h)
                        (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                    · have hmS' := fullM6HdrMem_unfocus hmS
                      refine wp_join_group (ts := []) (fun _ mSd => ∃ extSd sSd,
                          M6HdrExtOk extSd ∧ FullDenseInv c F0 sSd ∧
                          sSd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          (FullM6HdrMem c extSd sSd ⋆ R) mSd)
                        (fun _ _ mSd ⟨extSd, sSd, hextSd, hdenSd, hfuSd, hmSd⟩ =>
                          hJW2 () mSd ⟨extSd, sSd, hinvL.cfgOk, hextSd, hdenSd, hfuSd, hmSd⟩) ?_
                      intro JSd hJSd; c0_hsteps_nogrp
                      refine wp_join_group (ts := []) (fun _ mSd => ∃ extSd sSd,
                          M6HdrExtOk extSd ∧ FullDenseInv c F0 sSd ∧
                          sSd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          (FullM6HdrMem c extSd sSd ⋆ R) mSd)
                        (fun _ _ mSd ⟨extSd, sSd, hextSd, hdenSd, hfuSd, hmSd⟩ => by
                          refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hBumpD _ _ _ _ h)
                            hinvL.cfgOk hextSd hdenSd.lengths hmSd
                            fun _ extSd' sSd' mSd' hcSd hlSd hmsSd hextSd' _ hmSd' => ?_
                          exact hJSd () mSd' ⟨extSd', sSd', hextSd',
                            fullDenseInv_of_core_eq hdenSd hlSd hcSd hmsSd.extPres,
                            by rw [hcSd]; exact hfuSd, hmSd'⟩) ?_
                      intro JSdb hJSdb
                      refine wp_m6Hdr_focus_frame hmS' fun hmSf => ?_
                      c0_hsteps_nogrp
                      · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hRedD _ _ _ _ h)
                          hinvL.cfgOk hextCd hdenS.lengths (fullM6HdrMem_unfocus hmSf)
                          fun _ extSd sSd mSd hcSd hlSd hmsSd hextSd _ hmSd => ?_
                        exact hJSd () mSd ⟨extSd, sSd, hextSd,
                          fullDenseInv_of_core_eq hdenS hlSd hcSd hmsSd.extPres,
                          by rw [hcSd]; exact hfuS', hmSd⟩
                      · exact hJSdb () mS
                          ⟨extCd, sS, hextCd, hdenS, hfuS', fullM6HdrMem_unfocus hmSf⟩
                      · exact hJSdb () mS
                          ⟨extCd, sS, hextCd, hdenS, hfuS', fullM6HdrMem_unfocus hmSf⟩
              · intro JC hJC
                refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hDelay _ _ _ _ h)
                  hinvL.cfgOk hinvL.extOk hdenE'.lengths hmE'
                  fun ⟨del1, ⟨⟩⟩ extEd sEd mEd hcEd hlEd hmsEd hextEd _ hmEd => ?_
                have hdenEd := fullDenseInv_of_core_eq hdenE' hlEd hcEd hmsEd.extPres
                have hfuEd : sEd.core.fuel.toNat ≤ s.core.fuel.toNat := by
                  rw [hcEd]; exact Nat.le_trans hfuE hfuL
                c0_hsteps_nogrp
                · exact hJC () mEd ⟨extEd, sEd, hinvL.cfgOk, hextEd, hdenEd, hfuEd, hmEd⟩
                · refine wp_m6Hdr_focus_frame hmEd fun hmEdf => ?_
                  c0_hsteps_nogrp; c0_call hCong
                  refine ⟨c, F0, sEd, m6ExtMem (m6ExtAddr c.hdr) extEd ⋆ R, rfl, hdenEd, hmEdf,
                    fun rC sC mC hdenC _ hfuC hdomC huC hmC => ?_⟩
                  have hfuC' : sC.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hfuC]; exact hfuEd
                  c0_hsteps_nogrp
                  · c0_call hRebuild
                    refine ⟨c, F0, sC, m6ExtMem (m6ExtAddr c.hdr) extEd ⋆ R, rfl, hdenC, hmC,
                      fun rR sR mR hspR hclR hfuR _ huR hmR => ?_⟩
                    have hinvR := FullM6HdrInv.mk_inv hinvL.cfgOk hextEd hspR
                    have hmR' := fullM6HdrMem_unfocus hmR
                    refine wp_m6Hdr_focus_frame hmR' fun hmRf => ?_
                    c0_hsteps_nogrp
                    exact m6o1_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvR.cfgOk hinvR.extOk
                      hinvR.sparse.lengths (Nat.le_trans hfuR hfuC') (Or.inr rfl)
                      (fun _ => huC ‹_›) (fun h => by cases h)
                      (fullM6HdrMem_unfocus hmRf) (hQ 20#64)
                  · have hmC' := fullM6HdrMem_unfocus hmC
                    refine wp_join_group (ts := []) (fun _ mCd => ∃ extCd sCd,
                        M6HdrExtOk extCd ∧ FullDenseInv c F0 sCd ∧
                        sCd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        (FullM6HdrMem c extCd sCd ⋆ R) mCd)
                      (fun _ _ mCd ⟨extCd, sCd, hextCd, hdenCd, hfuCd, hmCd⟩ =>
                        hJC () mCd ⟨extCd, sCd, hinvL.cfgOk, hextCd, hdenCd, hfuCd, hmCd⟩) ?_
                    intro JCd hJCd; c0_hsteps_nogrp
                    refine wp_join_group (ts := []) (fun _ mCd => ∃ extCd sCd,
                        M6HdrExtOk extCd ∧ FullDenseInv c F0 sCd ∧
                        sCd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        (FullM6HdrMem c extCd sCd ⋆ R) mCd)
                      (fun _ _ mCd ⟨extCd, sCd, hextCd, hdenCd, hfuCd, hmCd⟩ => by
                        refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hBumpD _ _ _ _ h)
                          hinvL.cfgOk hextCd hdenCd.lengths hmCd
                          fun _ extCd' sCd' mCd' hcCd hlCd hmsCd hextCd' _ hmCd' => ?_
                        exact hJCd () mCd' ⟨extCd', sCd', hextCd',
                          fullDenseInv_of_core_eq hdenCd hlCd hcCd hmsCd.extPres,
                          by rw [hcCd]; exact hfuCd, hmCd'⟩) ?_
                    intro JCdb hJCdb
                    refine wp_m6Hdr_focus_frame hmC' fun hmCf => ?_
                    c0_hsteps_nogrp
                    · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hRedD _ _ _ _ h)
                        hinvL.cfgOk hextEd hdenC.lengths (fullM6HdrMem_unfocus hmCf)
                        fun _ extCd sCd mCd hcCd hlCd hmsCd hextCd _ hmCd => ?_
                      exact hJCd () mCd ⟨extCd, sCd, hextCd,
                        fullDenseInv_of_core_eq hdenC hlCd hcCd hmsCd.extPres,
                        by rw [hcCd]; exact hfuC', hmCd⟩
                    · exact hJCdb () mC ⟨extEd, sC, hextEd, hdenC, hfuC', fullM6HdrMem_unfocus hmCf⟩
                    · exact hJCdb () mC ⟨extEd, sC, hextEd, hdenC, hfuC', fullM6HdrMem_unfocus hmCf⟩
            · have hinvE := FullM6HdrInv.mk_inv hinvL.cfgOk hinvL.extOk (hspE ‹_›)
              refine wp_m6Hdr_focus_frame hmE' fun hmEf => ?_
              c0_hsteps_nogrp
              exact m6o1_probe_ret_wm rfl (Or.inr rfl) hSetWm hinvE.cfgOk hinvE.extOk
                hinvE.sparse.lengths (Nat.le_trans hfuE hfuL) (Or.inr rfl)
                (fun _ => fullM6HdrInv_inconsistent_unsat hinvE ‹_›)
                (fun h => by cases h) (fullM6HdrMem_unfocus hmEf) (hQ 20#64)
            · have hinvE := FullM6HdrInv.mk_inv hinvL.cfgOk hinvL.extOk (hspE ‹_›)
              exact hJD () mE ⟨extL, sE, hinvE, hclE, Nat.le_trans hfuE hfuL, hmE'⟩
        · exact hJW (round, ()) mL ⟨extL, sL, hinvL, hclL, hfuL, fullM6HdrMem_unfocus hmLf⟩
  · intro J1 hJ1; c0_hsteps_nogrp
    · exact hJ1 () m0 ⟨ext0, s0, hinv0, hcl0', hc0 ▸ rfl, hm0⟩
    · refine wp_m6Hdr_focus_frame hm0 fun hm0f => ?_
      c0_hsteps_nogrp; c0_call hIlog; intro logp _ _
      c0_hsteps_nogrp; c0_call hScale
      refine ⟨c, _, m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R, rfl,
        (fullState_upd_probe_step hinv0.sparse.lengths s0.scratch.probe_limit
          (s0.scratch.probings + 1#64)).1, by assumption, fun sd => ?_⟩
      c0_hsteps_nogrp
      have hst1 := fullState_upd_probe_step hinv0.sparse.lengths
        (s0.scratch.conflicts + sd) (s0.scratch.probings + 1#64)
      have hinv1 := fullM6HdrInv_of_probeStep hinv0 hst1
      exact hJ1 () _ ⟨ext0, _, hinv1, hst1.2.1 ▸ hcl0',
        by rw [hst1.2.1, hc0], fullM6HdrMem_unfocus (by assumption)⟩

/-! ## 5. `full_preprocess_m6_wp`, `full_preprocess_fwd_wp`, `full_simplify_m6_wp` -/

private theorem m6o1_call_bcp {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', FullM6BcpS15.fullBcpS15Spec (c.hdr, ()) m Q' X' →
      Γ "full_propagate" [i64] [i64] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInvW c F0 F_cur ext s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullM6HdrInvW c F0 F_cur ext s' → s'.core.cur_level = s.core.cur_level →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 1#64 → s'.core.fuel.toNat < s.core.fuel.toNat ∧ s'.core.oom = 0#64 ∧
        FullConflictOkW F_cur s') →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_propagate" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  have hsp := hinv.sparseW
  refine hΓ _ X ⟨c, F0, F_cur, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hsp.1, hsp.2.1,
    hsp.2.2.2.2.2, (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m' s'
    hlen' hw' htr' hperm' _ hfu' hdom _ hr1 _ _ hm'
  have hnd' : FullArenaVarsNodup s' := by
    intro r' hr' hgb'
    have hr0' : r' ∈ fullArenaClauseRefs s := by
      change r' ∈ fullArenaClauseRefsCore s'.core at hr'
      change r' ∈ fullArenaClauseRefsCore s.core
      rwa [← hperm'.2.1]
    have hp := hperm'.2.2 r' hr0'
    have hgb0 : fullArenaClauseGarb s r' = false := by
      change fullArenaClauseGarbCore s.core r' = false
      change fullArenaClauseGarbCore s'.core r' = false at hgb'
      rwa [← hp.2.1]
    exact (hp.2.2.map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 r' hr0' hgb0)
  have hll' : FullLastLearnedWf s' :=
    hsp.2.2.2.2.1.1.of_refs_subset rfl fun r' hr' => by
      change r' ∈ fullArenaClauseRefsCore s.core at hr'
      change r' ∈ fullArenaClauseRefsCore s'.core
      rwa [hperm'.2.1]
  have hinv' : FullM6HdrInvW c F0 F_cur ext s' :=
    FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk
      ⟨hlen', hw', hsp.2.2.1, hnd', ⟨hll', hsp.2.2.2.2.1.2⟩, hsp.2.2.2.2.2⟩
  exact hk r s' m' hinv' rfl htr' hperm' hfu' hdom hr1
    ((fullM6HdrMem_iff c ext s' R m').mpr hm')

theorem full_preprocess_m6_wp (Γ : Env)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, Full.fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hLucky : ∀ a m Q X, Full.fullLuckySpec a m Q X →
      Γ "full_lucky" [i64] [i64] a m Q X)
    (hCompNeed : ∀ a m Q X, FullM6CompactFlush.fullCompactNeededM6Spec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, FullM4Compact.fullCompactSpec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hProbe : ∀ a m Q X, m6ProbeSpec a m Q X →
      Γ "full_probe_m6" [i64, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullM6PreprocessSpec a m Q X →
      Func.wp Γ full_preprocess_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  rcases fullM6PreprocessSpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_preprocess_m6_body
  obtain ⟨F_cur, hw0⟩ := hinv.sparse.1.witness
  have hinvW0 : FullM6HdrInvW c F0 F_cur ext s :=
    FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk ⟨hinv.sparse.lengths, hw0, hinv.sparse.2.1,
      hinv.sparse.2.2.1, hinv.sparse.2.2.2.1, hinv.sparse.2.2.2.2⟩
  c0_hsteps_nogrp
  refine m6o1_call_bcp rfl (fun _ _ h => hProp _ _ _ _ h) hinvW0 hm
    fun r1 s1 m1 hinvW1 hcl1 _ _ hfu1 _ hr1_1 hm1 => ?_
  have hinv1 := hinvW1.toInv
  have hcl1' : s1.core.cur_level = 0 := by rw [hcl1]; exact hcl0
  refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
  c0_hsteps_nogrp
  · exact hQ 20#64 c ext s1 m1 (FullM4Compact.FullCfgCompat.refl c) hinv1.sparse.lengths hinv1.cfgOk
      hinv1.extOk (Or.inr (Or.inr (Or.inr rfl))) hfu1
      (fun _ => m6o1_conflict_level0_unsat hinvW1.sparseW.2.1 hcl1' (hr1_1 ‹_›).2.2)
      (fun h => by cases h) (fun h => by cases h) (fullM6HdrMem_unfocus hm1f)
  · exact hQ 0#64 c ext s1 m1 (FullM4Compact.FullCfgCompat.refl c) hinv1.sparse.lengths hinv1.cfgOk
      hinv1.extOk (Or.inl rfl) hfu1 (fun h => by cases h)
      (fun h => by cases h) (fun h => by cases h) (fullM6HdrMem_unfocus hm1f)
  · exact hQ 0#64 c ext s1 m1 (FullM4Compact.FullCfgCompat.refl c) hinv1.sparse.lengths hinv1.cfgOk
      hinv1.extOk (Or.inl rfl) hfu1 (fun h => by cases h)
      (fun h => by cases h) (fun h => by cases h) (fullM6HdrMem_unfocus hm1f)
  · refine wp_join_group (ts := []) (fun _ m2 => ∃ s2, FullM6HdrInv c F0 ext s2 ∧
        s2.core.cur_level = 0 ∧ s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullM6HdrMem c ext s2 ⋆ R) m2) ?_ ?_
    · rintro _ _ m2 ⟨s2, hinv2, hcl2, hfu2, hm2⟩
      refine wp_m6Hdr_focus_frame hm2 fun hm2f => ?_
      c0_hsteps_nogrp
      · exact hQ 10#64 c ext s2 m2 (FullM4Compact.FullCfgCompat.refl c) hinv2.sparse.lengths
          hinv2.cfgOk hinv2.extOk (Or.inr (Or.inr (Or.inl rfl))) hfu2
          (fun h => by cases h) (fun h => by cases h)
          (fun _ => hinv2.sparse.2.2.2.1.2) (fullM6HdrMem_unfocus hm2f)
      · c0_call hLucky
        refine ⟨c, F0, s2, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv2.sparse, hcl2, hm2f,
          fun lk s3 m3 hlen3 hlk hfu3 _ hu3 hsp3 h10_3 hm3 => ?_⟩
        have hm3' := fullM6HdrMem_unfocus hm3
        have hfu3' := Nat.le_trans hfu3 hfu2
        let mkInv3 : lk ≠ 20#64 → lk ≠ 10#64 →
            FullM6HdrInv c F0 ext s3 ∧ s3.core.cur_level = 0 := fun h20 h10 =>
          let h02 : lk = 0#64 ∨ lk = 2#64 := by
            rcases hlk with rfl | rfl | rfl | rfl <;>
              (first | exact Or.inl rfl | exact Or.inr rfl | contradiction)
          let ⟨hs3, hc3⟩ := hsp3 h02
          ⟨FullM6HdrInv.mk_inv hinv2.cfgOk hinv2.extOk hs3, hc3⟩
        c0_hsteps_nogrp
        · rw [‹lk = 20#64›]
          exact hQ 20#64 c ext s3 m3 (FullM4Compact.FullCfgCompat.refl c) hlen3 hinv2.cfgOk
            hinv2.extOk (Or.inr (Or.inr (Or.inr rfl))) hfu3' (fun _ => hu3 ‹_›)
            (fun h => by cases h) (fun h => by cases h) hm3'
        · rw [‹lk = 10#64›]
          exact hQ 10#64 c ext s3 m3 (FullM4Compact.FullCfgCompat.refl c) hlen3 hinv2.cfgOk
            hinv2.extOk (Or.inr (Or.inr (Or.inl rfl))) hfu3' (fun _ => by cases ‹_›)
            (fun h => by cases h) (fun _ => h10_3 ‹_›) hm3'
        · obtain ⟨hinv3, _⟩ := mkInv3 ‹_› ‹_›
          exact hQ 20#64 c ext s3 m3 (FullM4Compact.FullCfgCompat.refl c) hlen3 hinv3.cfgOk
            hinv3.extOk (Or.inr (Or.inr (Or.inr rfl))) hfu3'
            (fun _ => fullM6HdrInv_inconsistent_unsat hinv3 ‹_›)
            (fun h => by cases h) (fun h => by cases h) hm3'
        · obtain ⟨hinv3, _⟩ := mkInv3 ‹_› ‹_›
          exact hQ 0#64 c ext s3 m3 (FullM4Compact.FullCfgCompat.refl c) hlen3 hinv3.cfgOk
            hinv3.extOk (Or.inl rfl) hfu3' (fun h => by cases h)
            (fun h => by cases h) (fun h => by cases h) hm3'
        · obtain ⟨hinv3, _⟩ := mkInv3 ‹_› ‹_›
          exact hQ 0#64 c ext s3 m3 (FullM4Compact.FullCfgCompat.refl c) hlen3 hinv3.cfgOk
            hinv3.extOk (Or.inl rfl) hfu3' (fun h => by cases h)
            (fun h => by cases h) (fun h => by cases h) hm3'
        · obtain ⟨hinv3, hcl3⟩ := mkInv3 ‹_› ‹_›
          let hm3f := hm3
          -- First optional `compact_needed` -> `full_compact`.
          refine wp_join_group (fun (_ : Tup Val []) m4 => ∃ c4 s4,
              FullM4Compact.FullCfgCompat c c4 ∧ FullM6HdrInv c4 F0 ext s4 ∧
              s4.core.cur_level = 0 ∧ s4.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullM6HdrMem c4 ext s4 ⋆ R) m4) ?_ ?_
          · rintro _ _ m4 ⟨c4, s4, hcmp4, hinv4, hcl4, hfu4, hm4⟩
            rw [← hcmp4.hdr]
            refine wp_m6Hdr_focus_frame hm4 fun hm4f => ?_
            c0_hsteps_nogrp
            · exact hQ 20#64 c4 ext s4 m4 hcmp4 hinv4.sparse.lengths hinv4.cfgOk hinv4.extOk
                (Or.inr (Or.inr (Or.inr rfl))) hfu4
                (fun _ => fullM6HdrInv_inconsistent_unsat hinv4 ‹_›)
                (fun h => by cases h) (fun h => by cases h) (fullM6HdrMem_unfocus hm4f)
            · exact hQ 0#64 c4 ext s4 m4 hcmp4 hinv4.sparse.lengths hinv4.cfgOk hinv4.extOk
                (Or.inl rfl) hfu4 (fun h => by cases h)
                (fun h => by cases h) (fun h => by cases h) (fullM6HdrMem_unfocus hm4f)
            · exact hQ 10#64 c4 ext s4 m4 hcmp4 hinv4.sparse.lengths hinv4.cfgOk hinv4.extOk
                (Or.inr (Or.inr (Or.inl rfl))) hfu4 (fun h => by cases h)
                (fun h => by cases h) (fun _ => hinv4.sparse.2.2.2.1.2)
                (fullM6HdrMem_unfocus hm4f)
            · c0_call hScale
              refine ⟨c4, s4, m6ExtMem (m6ExtAddr c4.hdr) ext ⋆ R, rfl, hinv4.sparse.lengths,
                hm4f, fun sd1 => ?_⟩
              c0_hsteps_nogrp; c0_call hScale
              refine ⟨c4, _, m6ExtMem (m6ExtAddr c4.hdr) ext ⋆ R, rfl,
                (fullState_upd_probe_step hinv4.sparse.lengths sd1 s4.scratch.probings).1,
                by assumption, fun sd2 => ?_⟩
              c0_hsteps_nogrp
              have hst4 := fullState_upd_probe_step hinv4.sparse.lengths sd1 s4.scratch.probings
              have hst4' := fullState_upd_elim_step hst4.1 sd2 s4.scratch.eliminations
                s4.scratch.elim_bound
              have hinv4' := fullM6HdrInv_of_probeStep hinv4 (probeStep_trans hst4 hst4')
              have hm4' := fullM6HdrMem_unfocus (by assumption)
              c0_call hProbe
              refine m6ProbeSpec_of hinv4' (by rw [hst4'.2.1, hst4.2.1]; exact hcl4) hm4'
                fun r5 ext5 s5 m5 hlen5 hext5 hfu5 hr5 hu5 h15 hm5 => ?_
              have hfu5' : s5.core.fuel.toNat ≤ s.core.fuel.toNat := by
                rw [hst4'.2.1, hst4.2.1] at hfu5; exact Nat.le_trans hfu5 hfu4
              c0_hsteps_nogrp
              · exact hQ 20#64 c4 ext5 s5 m5 hcmp4 hlen5 hinv4'.cfgOk hext5
                  (Or.inr (Or.inr (Or.inr rfl))) hfu5' (fun _ => hu5 ‹_›)
                  (fun h => by cases h) (fun h => by cases h) hm5
              · obtain ⟨hinv5, hcl5⟩ := h15 (hr5.resolve_right ‹_›)
                refine wp_m6Hdr_focus_frame hm5 fun hm5f => ?_
                c0_hsteps_nogrp
                · exact hQ 20#64 c4 ext5 s5 m5 hcmp4 hlen5 hinv5.cfgOk hext5
                    (Or.inr (Or.inr (Or.inr rfl))) hfu5'
                    (fun _ => fullM6HdrInv_inconsistent_unsat hinv5 ‹_›)
                    (fun h => by cases h) (fun h => by cases h) (fullM6HdrMem_unfocus hm5f)
                · exact hQ 0#64 c4 ext5 s5 m5 hcmp4 hlen5 hinv5.cfgOk hext5
                    (Or.inl rfl) hfu5' (fun h => by cases h)
                    (fun h => by cases h) (fun h => by cases h) (fullM6HdrMem_unfocus hm5f)
                · exact hQ 0#64 c4 ext5 s5 m5 hcmp4 hlen5 hinv5.cfgOk hext5
                    (Or.inl rfl) hfu5' (fun h => by cases h)
                    (fun h => by cases h) (fun h => by cases h) (fullM6HdrMem_unfocus hm5f)
                · -- Second optional `compact_needed` -> `full_compact`.
                  refine wp_join_group (fun (_ : Tup Val []) m6 => ∃ c6 s6,
                      FullM4Compact.FullCfgCompat c c6 ∧ FullM6HdrInv c6 F0 ext5 s6 ∧
                      s6.core.cur_level = 0 ∧ s6.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                      (FullM6HdrMem c6 ext5 s6 ⋆ R) m6) ?_ ?_
                  · rintro _ _ m6 ⟨c6, s6, hcmp6, hinv6, hcl6, hfu6, hm6⟩
                    rw [hcmp4.hdr, ← hcmp6.hdr]
                    refine wp_m6Hdr_focus_frame hm6 fun hm6f => ?_
                    c0_hsteps_nogrp
                    · exact hQ 20#64 c6 ext5 s6 m6 hcmp6 hinv6.sparse.lengths hinv6.cfgOk
                        hinv6.extOk (Or.inr (Or.inr (Or.inr rfl))) hfu6
                        (fun _ => fullM6HdrInv_inconsistent_unsat hinv6 ‹_›)
                        (fun h => by cases h) (fun h => by cases h) (fullM6HdrMem_unfocus hm6f)
                    · exact hQ 0#64 c6 ext5 s6 m6 hcmp6 hinv6.sparse.lengths hinv6.cfgOk
                        hinv6.extOk (Or.inl rfl) hfu6 (fun h => by cases h)
                        (fun h => by cases h) (fun h => by cases h) (fullM6HdrMem_unfocus hm6f)
                    · exact hQ 10#64 c6 ext5 s6 m6 hcmp6 hinv6.sparse.lengths hinv6.cfgOk
                        hinv6.extOk (Or.inr (Or.inr (Or.inl rfl))) hfu6 (fun h => by cases h)
                        (fun h => by cases h) (fun _ => hinv6.sparse.2.2.2.1.2)
                        (fullM6HdrMem_unfocus hm6f)
                    · c0_call hScale
                      refine ⟨c6, s6, m6ExtMem (m6ExtAddr c6.hdr) ext5 ⋆ R, rfl,
                        hinv6.sparse.lengths, hm6f, fun sd3 => ?_⟩
                      c0_hsteps_nogrp; c0_call hScale
                      refine ⟨c6, _, m6ExtMem (m6ExtAddr c6.hdr) ext5 ⋆ R, rfl,
                        (fullState_upd_probe_step hinv6.sparse.lengths sd3 s6.scratch.probings).1,
                        by assumption, fun sd4 => ?_⟩
                      c0_hsteps_nogrp
                      have hst6 := fullState_upd_probe_step hinv6.sparse.lengths sd3
                        s6.scratch.probings
                      have hst6' := fullState_upd_elim_step hst6.1 sd4 s6.scratch.eliminations
                        s6.scratch.elim_bound
                      have hinv6' := fullM6HdrInv_of_probeStep hinv6
                        (probeStep_trans hst6 hst6')
                      exact hQ 1#64 c6 ext5 _ _ hcmp6 hinv6'.sparse.lengths hinv6'.cfgOk
                        hinv6'.extOk (Or.inr (Or.inl rfl))
                        (by rw [hst6'.2.1, hst6.2.1]; exact hfu6) (fun h => by cases h)
                        (fun _ => ⟨hinv6', by rw [hst6'.2.1, hst6.2.1]; exact hcl6⟩)
                        (fun h => by cases h) (fullM6HdrMem_unfocus (by assumption))
                  · intro JC2 hJC2
                    c0_hsteps_nogrp; c0_call hCompNeed
                    refine ⟨c4, s5, m6ExtMem (m6ExtAddr c4.hdr) ext5 ⋆ R, rfl, hlen5,
                      by have := hlen5.core_ok.trail_end_le; have := hlen5.core_ok.cur_vars_le
                         have := c4.hmaxv; unfold dimacsBound at *; omega,
                      hm5f, fun need _ => ?_⟩
                    c0_hsteps_nogrp
                    · c0_call hCompact
                      refine ⟨c4, F0, s5, m6ExtMem (m6ExtAddr c4.hdr) ext5 ⋆ R, rfl, hinv5.sparse,
                        hm5f, fun rC c6 s6 m6 hcmpC hspC hrC _ hfuC huC h1C hm6 => ?_⟩
                      have hcfg6 := M6HdrCfgOk_of_le
                        (by rw [hcmpC.hdr]; exact M6HdrCfgOk_le hinv5.cfgOk)
                      have hinv6 := FullM6HdrInv.mk_inv hcfg6 hext5 hspC
                      have hm6' := fullM6HdrMem_unfocus (hcmpC.hdr ▸ hm6)
                      have hcmp6 := hcmp4.trans hcmpC
                      have hfu6 := Nat.le_trans hfuC hfu5'
                      c0_hsteps_nogrp
                      · exact hQ 20#64 c6 ext5 s6 m6 hcmp6 hspC.lengths hcfg6 hext5
                          (Or.inr (Or.inr (Or.inr rfl))) hfu6 (fun _ => huC ‹_›)
                          (fun h => by cases h) (fun h => by cases h) hm6'
                      · exact hQ 0#64 c6 ext5 s6 m6 hcmp6 hspC.lengths hcfg6 hext5
                          (Or.inl rfl) hfu6 (fun h => by cases h)
                          (fun h => by cases h) (fun h => by cases h) hm6'
                      · exact hJC2 () m6 ⟨c6, s6, hcmp6, hinv6, h1C ‹_›, hfu6, hm6'⟩
                    · exact hJC2 () m5 ⟨c4, s5, hcmp4, hinv5, hcl5, hfu5',
                        fullM6HdrMem_unfocus hm5f⟩
          · intro JC1 hJC1
            c0_hsteps_nogrp; c0_call hCompNeed
            refine ⟨c, s3, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hlen3,
              by have := hlen3.core_ok.trail_end_le; have := hlen3.core_ok.cur_vars_le
                 have := c.hmaxv; unfold dimacsBound at *; omega,
              hm3f, fun need _ => ?_⟩
            c0_hsteps_nogrp
            · c0_call hCompact
              refine ⟨c, F0, s3, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv3.sparse,
                hm3f, fun rC c4 s4 m4 hcmp4 hsp4 hrC _ hfu4 huC h1C hm4 => ?_⟩
              have hcfg4 := M6HdrCfgOk_of_le (by rw [hcmp4.hdr]; exact M6HdrCfgOk_le hinv3.cfgOk)
              have hinv4 := FullM6HdrInv.mk_inv hcfg4 hinv3.extOk hsp4
              have hm4' := fullM6HdrMem_unfocus (hcmp4.hdr ▸ hm4)
              have hfu4' := Nat.le_trans hfu4 hfu3'
              c0_hsteps_nogrp
              · exact hQ 20#64 c4 ext s4 m4 hcmp4 hsp4.lengths hcfg4 hinv4.extOk
                  (Or.inr (Or.inr (Or.inr rfl))) hfu4' (fun _ => huC ‹_›)
                  (fun h => by cases h) (fun h => by cases h) hm4'
              · exact hQ 0#64 c4 ext s4 m4 hcmp4 hsp4.lengths hcfg4 hinv4.extOk
                  (Or.inl rfl) hfu4' (fun h => by cases h)
                  (fun h => by cases h) (fun h => by cases h) hm4'
              · exact hJC1 () m4 ⟨c4, s4, hcmp4, hinv4, h1C ‹_›, hfu4', hm4'⟩
            · exact hJC1 () m3 ⟨c, s3, FullM4Compact.FullCfgCompat.refl c, hinv3, hcl3, hfu3',
                fullM6HdrMem_unfocus hm3f⟩
    · intro J2 hJ2; c0_hsteps_nogrp
      · refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
        obtain ⟨F_cur1, hw1⟩ := hinv1.sparse.1.witness
        c0_hsteps_nogrp; c0_call hSweep
        refine ⟨c, F0, F_cur1, s1, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl,
          hinv1.sparse.lengths, hw1, hinv1.sparse.2.2.1, hinv1.sparse.2.2.2.2,
          fun hpos => by omega, hm1f,
          fun sr vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen' wlen'
            wu' fred' ni' nr' nb' oom' sc' mS hlenS hsr hexlenS hws2S hllS hwS hndS
            _ _ _ h20S _ hmS => ?_⟩
        have hmS' := fullM6HdrMem_unfocus hmS
        let sSc : FullCoreState :=
          { s1.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
            wvec := wvec', wstk := wstk', arena := arena', arena_len := alen', wlen := wlen',
            wusable := wu', arena_garbage := 0#64, first_reducible := fred', num_irred := ni',
            num_redundant := nr', num_binary := nb', oom := oom' }
        let sS : FullState := { core := sSc, scratch := sc' }
        have hinvWS : FullM6HdrInvW c F0 F_cur1 ext sS :=
          FullM6HdrInvW.mk_inv hinv1.cfgOk hinv1.extOk
            ⟨hlenS, hwS, hinv1.sparse.2.1, hndS,
              ⟨hllS, (by
                change sc'.extend_len ≤ c.extend_cap
                rw [hexlenS]; exact hinv1.sparse.2.2.2.1.2)⟩,
              hinv1.sparse.2.2.2.2⟩
        c0_hsteps_nogrp
        · exact hQ 20#64 c ext sS mS (FullM4Compact.FullCfgCompat.refl c) hlenS hinvWS.cfgOk
            hinvWS.extOk (Or.inr (Or.inr (Or.inr rfl))) hfu1 (fun _ => (h20S ‹_›).2)
            (fun h => by cases h) (fun h => by cases h) hmS'
        · refine m6o1_call_bcp rfl (fun _ _ h => hProp _ _ _ _ h) hinvWS hmS'
            fun pr sP mP hinvWP hclP _ _ hfuP _ hrP1 hmP => ?_
          have hinvP := hinvWP.toInv
          have hfuP' := Nat.le_trans hfuP hfu1
          c0_hsteps_nogrp
          · exact hQ 20#64 c ext sP mP (FullM4Compact.FullCfgCompat.refl c) hinvP.sparse.lengths
              hinvP.cfgOk hinvP.extOk (Or.inr (Or.inr (Or.inr rfl))) hfuP'
              (fun _ => m6o1_conflict_level0_unsat hinvWP.sparseW.2.1 (hclP ▸ hcl1') (hrP1 ‹_›).2.2)
              (fun h => by cases h) (fun h => by cases h) hmP
          · refine wp_m6Hdr_focus_frame hmP fun hmPf => ?_
            c0_hsteps_nogrp
            have hinvP' : FullM6HdrInv c F0 ext
                { sP with core := { sP.core with unflushed := 0#64 } } :=
              FullM6HdrInv.mk_inv hinvP.cfgOk hinvP.extOk
                ⟨⟨⟨{ hinvP.sparse.lengths.core_ok with
                      vals_len := hinvP.sparse.lengths.core_ok.vals_len },
                    hinvP.sparse.lengths.scratch_ok⟩,
                  ⟨F_cur1, { hinvWP.sparseW.2.1 with
                    arena := { hinvWP.sparseW.2.1.arena with
                      len_ok := hinvWP.sparseW.2.1.arena.len_ok }
                    watches := hinvWP.sparseW.2.1.watches.with_wstk rfl rfl rfl rfl rfl
                      (fun _ r => r) }⟩⟩,
                  hinvP.sparse.2.1, hinvP.sparse.2.2.1, hinvP.sparse.2.2.2.1,
                  hinvP.sparse.2.2.2.2⟩
            exact hJ2 () _ ⟨_, hinvP', hclP ▸ hcl1', hfuP', fullM6HdrMem_unfocus (by assumption)⟩
      · exact hJ2 () m1 ⟨s1, hinv1, hcl1', hfu1, fullM6HdrMem_unfocus hm1f⟩

theorem full_preprocess_fwd_wp (Γ : Env)
    (hPreM6 : ∀ a m Q X, fullM6PreprocessSpec a m Q X →
      Γ "full_preprocess_m6" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullM6PreprocessSpec a m Q X →
      Func.wp Γ full_preprocess_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  unfold Func.wp full_preprocess_body
  c0_call hPreM6
  exact hs

theorem full_simplify_m6_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProbe : ∀ a m Q X, m6ProbeSpec a m Q X →
      Γ "full_probe_m6" [i64, .bool] [i64] a m Q X)
    (hElim : ∀ a m Q X, FullFastSched.schedEliminateSpec a m Q X →
      Γ "full_eliminate_m6" [i64, .bool] [i64] a m Q X)
    (hCompNeed : ∀ a m Q X, FullM6CompactFlush.fullCompactNeededM6Spec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, FullM4Compact.fullCompactSpec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullM6SimplifySpec a m Q X →
      Func.wp Γ full_simplify_m6_body a m Q X := by
  rintro ⟨h, dp, de, ⟨⟩⟩ m Q X hs
  rcases fullM6SimplifySpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hm, hQ⟩
  unfold Func.wp full_simplify_m6_body
  -- Step 1: backtrack to 0 if needed.
  refine wp_join_group (fun (_ : Tup Val []) m0 => ∃ s0, FullM6HdrInv c F0 ext s0 ∧
      s0.core.cur_level = 0 ∧ s0.core.fuel = s.core.fuel ∧ (FullM6HdrMem c ext s0 ⋆ R) m0) ?_ ?_
  · rintro _ _ m0 ⟨s0, hinv0, hcl0, hfu0, hm0⟩
    -- Step 2: optional `do_probe -> full_probe_m6(h, false)`.
    refine wp_join_group (fun (_ : Tup Val []) m1 => ∃ ext1 s1, FullM6HdrInv c F0 ext1 s1 ∧
        s1.core.cur_level = 0 ∧ s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullM6HdrMem c ext1 s1 ⋆ R) m1) ?_ ?_
    · rintro _ _ m1 ⟨ext1, s1, hinv1, hcl1, hfu1, hm1⟩
      refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
      c0_hsteps_nogrp
      · exact hQ 0#64 c ext1 s1 m1 (FullM4Compact.FullCfgCompat.refl c) hinv1.sparse.lengths
          hinv1.cfgOk hinv1.extOk (Or.inl rfl) hfu1 (fun h => by cases h) (fun h => by cases h) hm1
      · exact hQ 0#64 c ext1 s1 m1 (FullM4Compact.FullCfgCompat.refl c) hinv1.sparse.lengths
          hinv1.cfgOk hinv1.extOk (Or.inl rfl) hfu1 (fun h => by cases h) (fun h => by cases h) hm1
      · -- Step 3: optional `do_elim -> full_eliminate_m6(h, false)`.
        refine wp_join_group (fun (_ : Tup Val []) m2 => ∃ s2, FullM6HdrInv c F0 ext1 s2 ∧
            s2.core.cur_level = 0 ∧ s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (FullM6HdrMem c ext1 s2 ⋆ R) m2) ?_ ?_
        · rintro _ _ m2 ⟨s2, hinv2, hcl2, hfu2, hm2⟩
          refine wp_m6Hdr_focus_frame hm2 fun hm2f => ?_
          c0_hsteps_nogrp
          · exact hQ 20#64 c ext1 s2 m2 (FullM4Compact.FullCfgCompat.refl c) hinv2.sparse.lengths
              hinv2.cfgOk hinv2.extOk (Or.inr (Or.inr rfl)) hfu2
              (fun _ => fullM6HdrInv_inconsistent_unsat hinv2 ‹_›) (fun h => by cases h) hm2
          · exact hQ 0#64 c ext1 s2 m2 (FullM4Compact.FullCfgCompat.refl c) hinv2.sparse.lengths
              hinv2.cfgOk hinv2.extOk (Or.inl rfl) hfu2
              (fun h => by cases h) (fun h => by cases h) hm2
          · -- Step 4: optional `compact_needed` -> `full_compact`.
            refine wp_join_group (fun (_ : Tup Val []) m3 => ∃ c3 s3,
                FullM4Compact.FullCfgCompat c c3 ∧
                FullM6HdrInv c3 F0 ext1 s3 ∧ s3.core.cur_level = 0 ∧
                s3.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c3 ext1 s3 ⋆ R) m3) ?_ ?_
            · rintro _ _ m3 ⟨c3, s3, hcmp3, hinv3, hcl3, hfu3, hm3⟩
              rw [← hcmp3.hdr]
              refine wp_m6Hdr_focus_frame hm3 fun hm3f => ?_
              c0_hsteps_nogrp
              · exact hQ 20#64 c3 ext1 s3 m3 hcmp3 hinv3.sparse.lengths hinv3.cfgOk
                  hinv3.extOk (Or.inr (Or.inr rfl)) hfu3
                  (fun _ => fullM6HdrInv_inconsistent_unsat hinv3 ‹_›) (fun h => by cases h) hm3
              · exact hQ 0#64 c3 ext1 s3 m3 hcmp3 hinv3.sparse.lengths hinv3.cfgOk
                  hinv3.extOk (Or.inl rfl) hfu3 (fun h => by cases h) (fun h => by cases h) hm3
              · exact hQ 1#64 c3 ext1 s3 m3 hcmp3 hinv3.sparse.lengths hinv3.cfgOk
                  hinv3.extOk (Or.inr (Or.inl rfl)) hfu3 (fun h => by cases h)
                  (fun _ => ⟨hinv3, hcl3⟩) hm3
            · intro J3 hJ3
              c0_hsteps_nogrp; c0_call hCompNeed
              refine ⟨c, s2, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hinv2.sparse.lengths,
                by have := hinv2.sparse.lengths.core_ok.trail_end_le
                   have := hinv2.sparse.lengths.core_ok.cur_vars_le
                   have := c.hmaxv; unfold dimacsBound at *; omega,
                hm2f, fun need _ => ?_⟩
              c0_hsteps_nogrp
              · c0_call hCompact
                refine ⟨c, F0, s2, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hinv2.sparse,
                  hm2f, fun rC c3 s3 m3 hcmp3 hsp3 hrC _ hfu3 hu3 h13 hm3 => ?_⟩
                have hcfg3 := M6HdrCfgOk_of_le (by rw [hcmp3.hdr]; exact M6HdrCfgOk_le hinv2.cfgOk)
                have hinv3 := FullM6HdrInv.mk_inv hcfg3 hinv2.extOk hsp3
                have hm3' := fullM6HdrMem_unfocus (hcmp3.hdr ▸ hm3)
                have hfu3' := Nat.le_trans hfu3 hfu2
                c0_hsteps_nogrp
                · exact hQ 20#64 c3 ext1 s3 m3 hcmp3 hsp3.lengths hcfg3 hinv3.extOk
                    (Or.inr (Or.inr rfl)) hfu3' (fun _ => hu3 ‹_›)
                    (fun h => by cases h) hm3'
                · exact hQ 0#64 c3 ext1 s3 m3 hcmp3 hsp3.lengths hcfg3 hinv3.extOk
                    (Or.inl rfl) hfu3' (fun h => by cases h) (fun h => by cases h) hm3'
                · exact hJ3 () m3 ⟨c3, s3, hcmp3, hinv3, h13 hc, hfu3', hm3'⟩
              · exact hJ3 () m2 ⟨c, s2, FullM4Compact.FullCfgCompat.refl c, hinv2, hcl2, hfu2, hm2⟩
        · intro J2 hJ2
          c0_hsteps_nogrp
          · c0_call hElim
            refine ⟨c, F0, s1, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hinv1.sparse, hcl1,
              hm1f, fun rE s2 m2 hsp2 hcl2 hfu2 hr2 hu2 hm2 => ?_⟩
            have hinv2 := FullM6HdrInv.mk_inv hinv1.cfgOk hinv1.extOk hsp2
            have hm2' := fullM6HdrMem_unfocus hm2
            c0_hsteps_nogrp
            · exact hQ 20#64 c ext1 s2 m2 (FullM4Compact.FullCfgCompat.refl c) hsp2.lengths
                hinv2.cfgOk hinv2.extOk (Or.inr (Or.inr rfl)) (Nat.le_trans hfu2 hfu1)
                (fun _ => hu2 ‹_›) (fun h => by cases h) hm2'
            · exact hJ2 () m2 ⟨s2, hinv2, hcl2, Nat.le_trans hfu2 hfu1, hm2'⟩
          · exact hJ2 () m1 ⟨s1, hinv1, hcl1, hfu1, hm1⟩
    · intro J1 hJ1; c0_hsteps_nogrp
      · c0_call hProbe
        refine m6ProbeSpec_of hinv0 hcl0 hm0
          fun rP ext1 s1 m1 hlen1 hext1 hfu1 hr1 hu1 h11 hm1 => ?_
        have hfu1' : s1.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [← hfu0]; exact hfu1
        c0_hsteps_nogrp
        · exact hQ 20#64 c ext1 s1 m1 (FullM4Compact.FullCfgCompat.refl c) hlen1 hinv0.cfgOk hext1
            (Or.inr (Or.inr rfl)) hfu1' (fun _ => hu1 ‹_›) (fun h => by cases h) hm1
        · obtain ⟨hinv1, hcl1⟩ := h11 (hr1.resolve_right ‹_›)
          exact hJ1 () m1 ⟨ext1, s1, hinv1, hcl1, hfu1', hm1⟩
      · exact hJ1 () m0 ⟨ext, s0, hinv0, hcl0, by rw [hfu0]; exact Nat.le_refl _, hm0⟩
  · intro J0 hJ0
    refine wp_m6Hdr_focus_frame hm fun hmf => ?_
    c0_hsteps_nogrp
    · obtain ⟨hcl_lt, htl_bd, htrl_bd⟩ := m6o1_fullInv_of_backtrack0 hinv
      obtain ⟨F_cur, hw⟩ := hinv.sparse.1.witness
      c0_call hBacktrack
      refine ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv.sparse.lengths,
        hcl_lt, htl_bd, htrl_bd, hmf, fun vals' lvl' rsns' trl' tp' te' prop' cl' unass'
          sc' m' hlen' hte' hprop' hcl' _ hsc _ _ hwi _ hm' => ?_⟩
      have hcl0' : cl' = 0 := by rw [hcl']; exact Nat.min_zero _
      let s0c : FullCoreState :=
        { s.core with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', propagated := prop', cur_level := cl', unassigned := unass' }
      let s0 : FullState := { core := s0c, scratch := sc' }
      obtain ⟨_, _, _, _, _, _, _, _, _, rfl⟩ := hsc
      have hsp0 : FullSparseInv c F0 s0 :=
        ⟨⟨hlen', F_cur, hwi F0 F_cur hw (Nat.zero_le _)⟩,
          by unfold FullLitMarksClear FullMrkZero; exact hinv.sparse.2.1,
          by unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb
               fullArenaClauseLits; exact hinv.sparse.2.2.1,
          FullExtScratchOk.of_pres hinv.sparse.2.2.2.1 ⟨rfl, rfl⟩ (fun _ hr => hr),
          hinv.sparse.2.2.2.2⟩
      exact hJ0 () _ ⟨s0, FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk hsp0,
        hcl0', rfl, fullM6HdrMem_unfocus hm'⟩
    · have hcl0 : s.core.cur_level = 0 := by
        have := hinv.sparse.1.witness.choose_spec.cur_level_le
        have := hinv.sparse.lengths.core_ok.trail_end_le
        have := hinv.sparse.lengths.core_ok.cur_vars_le
        have := c.hmaxv; unfold dimacsBound at *
        have hnot : ¬ 0 < s.core.cur_level % 2 ^ 64 := ‹_›
        rw [Nat.mod_eq_of_lt (by omega)] at hnot; omega
      exact hJ0 () m ⟨s, hinv, hcl0, rfl, hm⟩

/-! ### `full_reduce_m6` -/

section ReduceM6

private theorem m6o_arenaVarsNodup_perm {s s' : FullState}
    (hap : FullArenaPermEq s.core s'.core) (hnd : FullArenaVarsNodup s) :
    FullArenaVarsNodup s' := by
  intro r hr hgb
  change r ∈ fullArenaClauseRefs s' at hr
  have hmem : r ∈ fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs at hr ⊢; rw [hap.2.1] at hr; exact hr
  have hperm := hap.2.2 r hmem
  unfold fullArenaClauseGarb at hgb
  rw [hperm.2.1] at hgb
  exact (List.Perm.map (fun x => x / 2) hperm.2.2).nodup_iff.mpr (hnd r hmem hgb)

private structure M6oRedSt (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (ext : List (BitVec 64))
    (st : FullState) (ml : Mem 64) : Prop where
  inv : FullM6HdrInvW c F0 F_cur ext st
  cl : st.core.cur_level ≤ s.core.cur_level
  fu : st.core.fuel.toNat ≤ s.core.fuel.toNat
  cv : st.core.cur_vars = s.core.cur_vars
  tmp : st.core.tmp = s.core.tmp
  tl : st.core.tmp_len = s.core.tmp_len
  ws2 : st.scratch.work_stk2 = s.scratch.work_stk2
  pos : 0 < st.core.cur_level →
    st.core.cur_level = s.core.cur_level ∧ st.core.vals = s.core.vals ∧
    st.core.lvl = s.core.lvl ∧ st.core.trl = s.core.trl ∧
    st.core.trail_pos = s.core.trail_pos ∧ st.core.trail_end = s.core.trail_end
  mem : (FullM6HdrMem c ext st ⋆ R) ml

private theorem m6oRedSt_refl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    M6oRedSt c F0 F_cur s R ext s m :=
  ⟨hinv, Nat.le_refl _, Nat.le_refl _, rfl, rfl, rfl, rfl,
    fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, hm⟩

private theorem m6oRedSt_with_scratch {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    (hst : M6oRedSt c F0 F_cur s R ext st ml) {sc' : FullScratch}
    (hsc : sc'.LengthsOk c) (hll : sc'.last_learned = st.scratch.last_learned)
    (hext : sc'.extend_len = st.scratch.extend_len) (hws2 : sc'.work_stk2 = st.scratch.work_stk2)
    {ml' : Mem 64} (hm' : (FullM6HdrMem c ext { st with scratch := sc' } ⋆ R) ml') :
    M6oRedSt c F0 F_cur s R ext { st with scratch := sc' } ml' :=
  have hsp := hst.inv.sparseW
  ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk
      ⟨⟨hsp.1.core_ok, hsc⟩, hsp.2.1, hsp.2.2.1, hsp.2.2.2.1,
        FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨hll, hext⟩ (fun _ hr => hr), hsp.2.2.2.2.2⟩,
    hst.cl, hst.fu, hst.cv, hst.tmp, hst.tl, hws2.trans hst.ws2, hst.pos, hm'⟩

private theorem m6oRedSt_w2a {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st s' : FullState} {R : Mem 64 → Prop} {ext ext' : List (BitVec 64)} {ml ml' : Mem 64}
    (hst : M6oRedSt c F0 F_cur s R ext st ml) (hc : s'.core = st.core) (hl : s'.LengthsOk c)
    (hms : M6HdrScratchPres st s') (hext : M6HdrExtOk ext')
    (hm' : (FullM6HdrMem c ext' s' ⋆ R) ml') : M6oRedSt c F0 F_cur s R ext' s' ml' := by
  have hsp := hst.inv.sparseW
  have hlm' : FullLitMarksClear c s' :=
    ⟨fun v hv => by rw [hc]; exact hsp.2.2.1.1 v hv,
      by simpa only [hc] using hsp.2.2.1.2⟩
  have hsp' : FullSparseInvW c F0 F_cur s' :=
    ⟨hl, hc ▸ hsp.2.1, hlm',
      fun r hr hng => by
        change r ∈ fullArenaClauseRefs s' at hr; unfold fullArenaClauseRefs at hr
        unfold fullArenaClauseGarb at hng; unfold fullArenaClauseLits
        rw [hc] at hr hng ⊢; exact hsp.2.2.2.1 r hr hng,
      FullExtScratchOk.of_pres hsp.2.2.2.2.1 hms.extPres
        fun _ hr => by unfold fullArenaClauseRefs at hr ⊢; rwa [hc],
      hc ▸ hsp.2.2.2.2.2⟩
  refine ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hext hsp', ?_, ?_, ?_, ?_, ?_,
    hms.ws2.trans hst.ws2, ?_, hm'⟩
  · rw [hc]; exact hst.cl
  · rw [hc]; exact hst.fu
  · rw [hc]; exact hst.cv
  · rw [hc]; exact hst.tmp
  · rw [hc]; exact hst.tl
  · intro hpos; rw [hc] at hpos ⊢; exact hst.pos hpos

private theorem m6oRedSt_with_unflushed {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml ml' : Mem 64}
    (hst : M6oRedSt c F0 F_cur s R ext st ml) (u' : BitVec 64)
    (hm' : (FullM6HdrMem c ext { st with core := { st.core with unflushed := u' } } ⋆ R) ml') :
    M6oRedSt c F0 F_cur s R ext { st with core := { st.core with unflushed := u' } } ml' :=
  have hsp := hst.inv.sparseW
  ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk
      ⟨⟨{ hsp.1.core_ok with vals_len := hsp.1.core_ok.vals_len }, hsp.1.scratch_ok⟩,
        Full.FullDenseWatchHelpers.fullWitnessInv_with_unflushed hsp.2.1 u', hsp.2.2.1,
        hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩,
    hst.cl, hst.fu, hst.cv, hst.tmp, hst.tl, hst.ws2, hst.pos, hm'⟩

private theorem m6oRedSt_mark_reasons {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml ml' : Mem 64}
    {ar' : List (BitVec 32)} (hst : M6oRedSt c F0 F_cur s R ext st ml)
    (hlen' : ({ st with core := { st.core with arena := ar' } } : FullState).LengthsOk c)
    (hrefs : fullArenaClauseRefs { st with core := { st.core with arena := ar' } } =
      fullArenaClauseRefs st)
    (hper : ∀ r ∈ fullArenaClauseRefs st,
      fullArenaClauseSize { st with core := { st.core with arena := ar' } } r =
        fullArenaClauseSize st r ∧
      fullArenaClauseGarb { st with core := { st.core with arena := ar' } } r =
        fullArenaClauseGarb st r ∧
      fullArenaClauseLits { st with core := { st.core with arena := ar' } } r =
        fullArenaClauseLits st r)
    (hw' : FullWitnessInv c F0 F_cur { st.core with arena := ar' })
    (hm' : (FullM6HdrMem c ext { st with core := { st.core with arena := ar' } } ⋆ R) ml') :
    M6oRedSt c F0 F_cur s R ext { st with core := { st.core with arena := ar' } } ml' :=
  have hsp := hst.inv.sparseW
  ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk
      ⟨hlen', hw', hsp.2.2.1, fun r hr hng => by
          rw [hrefs] at hr; rw [(hper r hr).2.1] at hng; rw [(hper r hr).2.2]
          exact hsp.2.2.2.1 r hr hng,
        FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ hr => by rwa [hrefs]),
        hsp.2.2.2.2.2⟩,
    hst.cl, hst.fu, hst.cv, hst.tmp, hst.tl, hst.ws2, hst.pos, hm'⟩

private theorem m6oRedSt_backtrack0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    (hst : M6oRedSt c F0 F_cur s R ext st ml)
    {vals' : List (BitVec 8)} {lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' : BitVec 64} {sc' : FullScratch} {m' : Mem 64}
    (hlen' : (
      { core :=
          { st.core with
            vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
            trail_end := te', propagated := prop', cur_level := 0, unassigned := unass' }
        scratch := sc' } : FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { st.core with
        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', cur_level := 0, unassigned := unass' })
    (hll' : sc'.last_learned = st.scratch.last_learned)
    (hext' : sc'.extend_len = st.scratch.extend_len)
    (hws2' : sc'.work_stk2 = st.scratch.work_stk2)
    (hm' : (FullM6HdrMem c ext
      { core :=
          { st.core with
            vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
            trail_end := te', propagated := prop', cur_level := 0, unassigned := unass' }
        scratch := sc' } ⋆ R) m') :
    M6oRedSt c F0 F_cur s R ext
      { core :=
          { st.core with
            vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
            trail_end := te', propagated := prop', cur_level := 0, unassigned := unass' }
        scratch := sc' } m' :=
  have hsp := hst.inv.sparseW
  ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk
      ⟨hlen', hw', hsp.2.2.1, hsp.2.2.2.1, FullExtScratchOk.of_pres hsp.2.2.2.2.1
        ⟨hll', hext'⟩ (fun _ hr => hr), hsp.2.2.2.2.2⟩,
    Nat.zero_le _, hst.fu, hst.cv, hst.tmp, hst.tl, hws2'.trans hst.ws2,
    (fun hpos => by cases hpos), hm'⟩

private theorem m6o_call_fullBcpS15_red {Γ : Env} {f : Sym} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s st : FullState} {R : Mem 64 → Prop} {ml : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ a m' Q' X', FullM6BcpS15.fullBcpS15Spec a m' Q' X' → Γ f [i64] [i64] a m' Q' X')
    (hst : M6oRedSt c F0 F_cur s R ext st ml) (hcl0 : st.core.cur_level = 0)
    (hk : ∀ r s' m', M6oRedSt c F0 F_cur s R ext s' m' → s'.core.cur_level = 0 →
      st.core.trail_end ≤ s'.core.trail_end → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → st.core.oom = 0#64 → s'.core.oom = 0#64) →
      (r = 1#64 → F0.Unsat) → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call f (as := [i64]) (bs := [i64]) args k) ml := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  have hsp := hst.inv.sparseW
  refine hΓ _ _ _ X ⟨c, F0, F_cur, st, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl,
    hsp.1, hsp.2.1, hsp.2.2.2.2.2, fullM6HdrMem_focus_full hst.mem, ?_⟩
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m' s'
    hs' hw' hte hap _hdel hfu hr h0 h1 _h2 _hno hm'
  have hsp' : FullSparseInvW c F0 F_cur s' :=
    ⟨hs', hw', hsp.2.2.1, m6o_arenaVarsNodup_perm hap hsp.2.2.2.1,
      FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨rfl, rfl⟩ fun _ hr =>
        by unfold fullArenaClauseRefs at hr ⊢; rwa [hap.2.1],
      hsp.2.2.2.2.2⟩
  have hst' : M6oRedSt c F0 F_cur s R ext s' m' :=
    ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk hsp', hst.cl,
      Nat.le_trans hfu hst.fu, hst.cv, hst.tmp, hst.tl, hst.ws2,
      fun hpos => by change 0 < st.core.cur_level at hpos; omega, fullM6HdrMem_unfocus_full hm'⟩
  exact hk r s' m' hst' hcl0 hte.1 hr (fun h0eq hso => (h0 h0eq).2.1 hso)
    (fun h1eq => level0_unsat_of_conflict_okW hw' hcl0 (h1 h1eq).2.2)

private theorem m6oRedSt_arena_sweep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    (hst : M6oRedSt c F0 F_cur s R ext st ml)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' wvec' wstk' arena' : List (BitVec 32)}
    {te' alen' wlen' : Nat} {unass' unfl' wu' fred' ni' nr' nb' oom' : BitVec 64}
    {sc' : FullScratch} {m' : Mem 64} :
    let sA : FullState :=
      { core :=
          { st.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
            wvec := wvec', wstk := wstk', arena := arena', arena_len := alen', wlen := wlen',
            wusable := wu', arena_garbage := 0#64, first_reducible := fred', num_irred := ni',
            num_redundant := nr', num_binary := nb', oom := oom' }
        scratch := sc' }
    sA.LengthsOk c → FullWitnessInv c F0 F_cur sA.core → FullArenaVarsNodup sA →
    FullLastLearnedWf sA → sc'.extend_len = st.scratch.extend_len →
    sc'.work_stk2 = st.scratch.work_stk2 →
    (0 < st.core.cur_level → vals' = st.core.vals ∧ lvl' = st.core.lvl ∧ trl' = st.core.trl ∧
      tp' = st.core.trail_pos ∧ te' = st.core.trail_end) →
    (FullM6HdrMem c ext sA ⋆ R) m' → M6oRedSt c F0 F_cur s R ext sA m' := by
  intro sA hlenA hwA hndA hllA hextA hws2A hposA hm'
  have hsp := hst.inv.sparseW
  refine ⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk
      ⟨hlenA, hwA, hsp.2.2.1, hndA, ⟨hllA, hextA ▸ hsp.2.2.2.2.1.2⟩, hsp.2.2.2.2.2⟩,
    hst.cl, hst.fu, hst.cv, hst.tmp, hst.tl, hws2A.trans hst.ws2, fun hpos => ?_, hm'⟩
  obtain ⟨hv, hl, ht, htp, hte⟩ := hposA hpos
  obtain ⟨hcl, hv0, hl0, ht0, htp0, hte0⟩ := hst.pos hpos
  exact ⟨hcl, hv.trans hv0, hl.trans hl0, ht.trans ht0, htp.trans htp0, hte.trans hte0⟩

private def M6oRedRefsOk (s : FullState) (rc : Nat) : Prop :=
  ∀ j < rc,
    let r := (s.scratch.red_refs[j]?.getD 0#32).toNat
    r ∈ fullArenaClauseRefs s ∧ (fullArenaHdr s r &&& 0x00200000#32) = 0#32

private theorem m6oRedRefsOk_push {c : FullCfg} {s : FullState} {rc p : Nat}
    (hrr_len : s.scratch.red_refs.length = c.red_cap) (hrc_lt : rc < c.red_cap)
    (hp_lt32 : p < 2 ^ 32) (hp_mem : p ∈ fullArenaClauseRefs s)
    (hp_norsn : (fullArenaHdr s p &&& 0x00200000#32) = 0#32)
    (hprev : M6oRedRefsOk s rc) :
    M6oRedRefsOk { s with scratch :=
      { s.scratch with red_refs := s.scratch.red_refs.set rc (BitVec.ofNat 32 p) } } (rc + 1) := by
  intro j hj
  by_cases hje : j = rc
  · subst j
    have hget : (s.scratch.red_refs.set rc (BitVec.ofNat 32 p))[rc]? = some (BitVec.ofNat 32 p) :=
      List.getElem?_set_self (by omega)
    simpa [hget, bv32_ofNat_toNat hp_lt32] using And.intro hp_mem hp_norsn
  · have hget : (s.scratch.red_refs.set rc (BitVec.ofNat 32 p))[j]? = s.scratch.red_refs[j]? :=
      List.getElem?_set_ne (Ne.symm hje)
    simpa [hget] using hprev j (by omega)

private theorem m6oRedSt_update_used {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml ml' : Mem 64}
    {p rc : Nat} {u : BitVec 32}
    (hst : M6oRedSt c F0 F_cur s R ext st ml) (hrmL : FullReasonsMarked st)
    (hrrL : M6oRedRefsOk st rc) (hp_in : p ∈ fullArenaClauseRefs st)
    (hp_ar : p < st.core.arena.length)
    (hm' : (FullM6HdrMem c ext
      { core := { st.core with
          arena := st.core.arena.set p
            ((st.core.arena[p]'hp_ar &&& 0x07FFFFFF#32) ||| (u <<< (27 : Nat))) }
        scratch := st.scratch } ⋆ R) ml') :
    let v' := (st.core.arena[p]'hp_ar &&& 0x07FFFFFF#32) ||| (u <<< (27 : Nat))
    let sU : FullState := { st with core := { st.core with arena := st.core.arena.set p v' } }
    M6oRedSt c F0 F_cur s R ext sU ml' ∧ FullReasonsMarked sU ∧
    fullArenaClauseRefs sU = fullArenaClauseRefs st ∧ M6oRedRefsOk sU rc ∧
    (fullArenaHdr sU p &&& 0x00200000#32) = (st.core.arena[p]'hp_ar &&& 0x00200000#32) := by
  intro v' sU
  have hsp := hst.inv.sparseW
  have hhdr_eq : st.core.arena[p]'hp_ar = fullArenaHdr st p := by
    unfold fullArenaHdr fullArenaHdrCore; rw [List.getElem?_eq_getElem hp_ar, Option.getD_some]
  have hup := Full.FullDenseWatchHelpers.updateUsed_preserves_fullWitnessInv hsp.1 hsp.2.1 hp_in u
  rw [← hhdr_eq] at hup
  obtain ⟨hlenU, hrefsU, hperU, hwU⟩ := hup
  have hndU : FullArenaVarsNodup sU := fun r hr hng => by
    rw [hrefsU] at hr; rw [(hperU r hr).2.1] at hng; rw [(hperU r hr).2.2.1]
    exact hsp.2.2.2.1 r hr hng
  have hspU : FullSparseInvW c F0 F_cur sU :=
    ⟨hlenU, hwU, hsp.2.2.1, hndU, FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨rfl, rfl⟩
      (fun _ hr => by rwa [hrefsU]), hsp.2.2.2.2.2⟩
  have hrmU : FullReasonsMarked sU := fun idx hidx hlp hlg => by
    have hne0 : st.core.rsns[(st.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := fun heq => by rw [heq] at hlg; revert hlg; decide
    have hrs := hsp.2.1.reason_inv idx hidx hne0
    have hbf : ¬ (st.core.rsns[(st.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
    rw [ite_eq_right hbf] at hrs; rw [(hperU _ hrs.1).2.2.2]; exact hrmL idx hidx hlp hlg
  have hrrU : M6oRedRefsOk sU rc := fun j hj => by
    obtain ⟨hjm, hjr⟩ := hrrL j hj; exact ⟨hrefsU ▸ hjm, (hperU _ hjm).2.2.2.trans hjr⟩
  exact ⟨⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk hspU, hst.cl, hst.fu,
    hst.cv, hst.tmp, hst.tl, hst.ws2, hst.pos, hm'⟩, hrmU, hrefsU, hrrU,
    by rw [(hperU p hp_in).2.2.2, ← hhdr_eq]⟩

private theorem m6oRedSt_mark_garb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml ml' : Mem 64}
    {cr rc : Nat} {agN : BitVec 64}
    (hst : M6oRedSt c F0 F_cur s R ext st ml) (hrmI : FullReasonsMarked st)
    (hrrI : M6oRedRefsOk st rc) (hcr_mem : cr ∈ fullArenaClauseRefs st)
    (hcr_norsn : (fullArenaHdr st cr &&& 0x00200000#32) = 0#32)
    (hcr_ar : cr < st.core.arena.length)
    (hm' : (FullM6HdrMem c ext
      { core := { st.core with
          arena := st.core.arena.set cr (st.core.arena[cr]'hcr_ar ||| 0x00080000#32)
          arena_garbage := agN }
        scratch := st.scratch } ⋆ R) ml') :
    let sN : FullState :=
      { core := { st.core with
          arena := st.core.arena.set cr (st.core.arena[cr]'hcr_ar ||| 0x00080000#32)
          arena_garbage := agN }
        scratch := st.scratch }
    M6oRedSt c F0 F_cur s R ext sN ml' ∧ FullReasonsMarked sN ∧
    fullArenaClauseRefs sN = fullArenaClauseRefs st ∧ M6oRedRefsOk sN rc := by
  intro sN
  have hsp := hst.inv.sparseW
  have hhdr_eq : st.core.arena[cr]'hcr_ar = fullArenaHdr st cr := by
    unfold fullArenaHdr fullArenaHdrCore; rw [List.getElem?_eq_getElem hcr_ar, Option.getD_some]
  have hnonact := Full.FullDenseWatchHelpers.markGarb_nonact_of_reasonsMarked hsp.2.1 hrmI hcr_norsn
  have hmg := Full.FullDenseWatchHelpers.markGarb_preserves_fullWitnessInv
    hsp.1 hsp.2.1 hcr_mem agN hnonact
  rw [← hhdr_eq] at hmg
  obtain ⟨hlenN, hrefsN, hwN, hrsnN, hndN⟩ := hmg
  have hspN : FullSparseInvW c F0 F_cur sN :=
    ⟨hlenN, hwN, hsp.2.2.1, hndN hsp.2.2.2.1, FullExtScratchOk.of_pres hsp.2.2.2.2.1 ⟨rfl, rfl⟩
      (fun _ hr => by rwa [hrefsN]), hsp.2.2.2.2.2⟩
  have hrmN : FullReasonsMarked sN := fun idx hidx hlp hlg => by
    have hne0 : st.core.rsns[(st.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := fun heq => by rw [heq] at hlg; revert hlg; decide
    have hrs := hsp.2.1.reason_inv idx hidx hne0
    have hbf : ¬ (st.core.rsns[(st.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
        0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
    rw [ite_eq_right hbf] at hrs; rw [hrsnN _ hrs.1]; exact hrmI idx hidx hlp hlg
  have hrrN : M6oRedRefsOk sN rc := fun j hj => by
    obtain ⟨hjm, hjr⟩ := hrrI j hj; exact ⟨hrefsN ▸ hjm, (hrsnN _ hjm).trans hjr⟩
  exact ⟨⟨FullM6HdrInvW.mk_inv hst.inv.cfgOk hst.inv.extOk hspN, hst.cl, hst.fu,
    hst.cv, hst.tmp, hst.tl, hst.ws2, hst.pos, hm'⟩, hrmN, hrefsN, hrrN⟩

private theorem m6o_reduce_jt_loop {Γ : Env} {ret : Val i64} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext2 : List (BitVec 64)} {s sT : FullState}
    {R : Mem 64 → Prop} {mT : Mem 64} {Q : Post [i64]} {X : XPost} {Jt : Cont [i64]}
    {e_else : Expr Val Cont [i64]} (hret : ret = 1#64)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hJt : ∀ (xs : Tup Val [i64]) (m : Mem 64), (match xs with
      | (rret, ()) => ∃ st : FullState,
        M6oRedSt c F0 F_cur s R ext2 st m ∧ (rret = 0#64 ∨ rret = 1#64 ∨ rret = 20#64) ∧
        (rret = 20#64 → F0.Unsat) ∧ (rret = 1#64 → s.core.oom = 0#64 → st.core.oom = 0#64)) →
      Jt xs m)
    (hstT : M6oRedSt c F0 F_cur s R ext2 sT mT)
    (hoomT : s.core.oom = 0#64 → sT.core.oom = 0#64) (hrmT : FullReasonsMarked sT) :
    wp Γ Q X (Expr.group (sig := [[]]) (fun L => Blocks.cons (fun _ =>
      Expr.jnz (Arg.imm true)
        (Expr.call (as := [i64]) (bs := [i64]) "full_arena_sweep" (Arg.var c.hdr, ()) fun p =>
          Expr.let_
            { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
              args := (Arg.var p.fst, Arg.imm 2, ()) } fun p_1 =>
            Expr.jnz (Arg.var p_1.fst) (Expr.jump Jt (Arg.imm 20, ()))
              (Expr.let_
                { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                  args := (Arg.var p.fst, Arg.imm 3, ()) } fun p_2 =>
                Expr.jnz (Arg.var p_2.fst) (Expr.jump Jt (Arg.imm 0, ()))
                  (Expr.let_
                    { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                      args := (Arg.var p.fst, Arg.imm 0, ()) } fun p_3 =>
                    Expr.jnz (Arg.var p_3.fst) (Expr.jump Jt (Arg.var ret, ()))
                      (Expr.call (as := [i64]) (bs := [i64]) "full_propagate"
                          (Arg.var c.hdr, ()) fun p_4 =>
                        Expr.let_
                          { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                            args := (Arg.var p_4.fst, Arg.imm 1, ()) } fun p_5 =>
                          Expr.jnz (Arg.var p_5.fst) (Expr.jump Jt (Arg.imm 20, ()))
                            (Expr.let_
                              { sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64 Ty.bool rfl,
                                args := (Arg.var p_4.fst, Arg.imm 0, ()) } fun p_6 =>
                              Expr.jnz (Arg.var p_6.fst) (Expr.jump Jt (Arg.imm 0, ()))
                                (Expr.let_
                                  { sig := [i64, i64], code := OpCode.add i64,
                                    args := (Arg.var c.hdr, Arg.imm 512, ()) } fun p_7 =>
                                  Expr.store (t := i64) (Arg.imm 0) (Arg.var p_7.fst)
                                    (Expr.jump L.fst ()))))))) e_else) .nil)
      (fun L => Expr.jump L.fst ())) mT := by
  refine wp_loop_group (ts := [])
    (fun rem () ml => ∃ st : FullState,
      rem = c.max_vars - st.core.trail_end ∧
      M6oRedSt c F0 F_cur s R ext2 st ml ∧
      (s.core.oom = 0#64 → st.core.oom = 0#64) ∧
      (0 < st.core.cur_level → FullReasonsMarked st))
    ?_ ?_
  · rintro L rem ⟨⟩ ml ih ⟨st, rfl, hst_st, hoom_st, hrm_st⟩
    refine wp_jnz_of (fun _ => ?_) (fun hc => by cases hc)
    refine wp_m6Hdr_focus_frame hst_st.mem fun hmf => ?_
    c0_call hSweep
    refine ⟨c, F0, F_cur, st, m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R,
      rfl, hst_st.inv.sparseW.1, hst_st.inv.sparseW.2.1,
      hst_st.inv.sparseW.2.2.2.1, hst_st.inv.sparseW.2.2.2.2.2,
      hrm_st, hmf,
      fun sr vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec'
        wstk' arena' alen' wlen' wu' fred' ni' nr' nb' oom' sc' mA
        hlenA hsr_dom hextA hws2A hllA hwA hndA hoomA hposA hsr1 hsr2 _hsr3 hmA => ?_⟩
    have hstA := m6oRedSt_arena_sweep hst_st hlenA hwA hndA hllA hextA
      hws2A (fun hpos => by
        obtain ⟨_, _, hv, hl, ht, htp, hte⟩ := hposA hpos
        exact ⟨hv, hl, ht, htp, hte⟩) (fullM6HdrMem_unfocus_full hmA)
    c0_hsteps_nogrp
    · exact hJt (20#64, ()) mA ⟨_, hstA, Or.inr (Or.inr rfl),
        fun _ => (hsr2 hc).2, fun h => by cases h⟩
    · exact hJt (0#64, ()) mA ⟨_, hstA, Or.inl rfl,
        (fun h => by cases h), fun h => by cases h⟩
    · simpa only [← hret] using hJt (1#64, ()) mA ⟨_, hstA, Or.inr (Or.inl rfl),
        (fun h => by cases h), fun _ _ => hoomA (Or.inl hc)⟩
    · have hsr_eq1 : sr = 1#64 := by
        rcases hsr_dom with rfl | rfl | rfl | rfl <;> first | rfl | contradiction
      obtain ⟨hcl0, hteA⟩ := hsr1 hsr_eq1
      have hoomA0 : oom' = 0#64 := hoomA (Or.inr hsr_eq1)
      refine m6o_call_fullBcpS15_red rfl
        (fun _ _ _ _ h => hProp _ _ _ _ h) hstA hcl0
        fun pr sB mB hstB hclB hteB hrB h0B h1B => ?_
      c0_hsteps_nogrp
      · exact hJt (20#64, ()) mB ⟨sB, hstB, Or.inr (Or.inr rfl),
          fun _ => h1B hc, fun h => by cases h⟩
      · exact hJt (0#64, ()) mB ⟨sB, hstB, Or.inl rfl,
          (fun h => by cases h), fun h => by cases h⟩
      · refine wp_m6Hdr_focus_frame hstB.mem fun hmBf => ?_
        c0_hsteps_nogrp
        have hte_bd : sB.core.trail_end ≤ c.max_vars :=
          Nat.le_trans hstB.inv.sparseW.1.core_ok.trail_end_le
            hstB.inv.sparseW.1.core_ok.cur_vars_le
        dsimp only at hteB
        exact ih (c.max_vars - sB.core.trail_end) () _ (by omega)
          ⟨{ sB with core := { sB.core with unflushed := 0#64 } }, rfl,
            m6oRedSt_with_unflushed hstB 0#64
              (fullM6HdrMem_unfocus (by assumption)),
            fun _ => h0B hc hoomA0,
            fun hpos => by change 0 < sB.core.cur_level at hpos; omega⟩
  · intro L hL
    c0_hsteps_nogrp
    exact hL (c.max_vars - sT.core.trail_end) () mT ⟨sT, rfl, hstT, hoomT, fun _ => hrmT⟩

private theorem m6o_reduce_j4_post {Γ : Env} {ret : Val i64} {force : Val .bool}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext2 : List (BitVec 64)}
    {s s4 : FullState} {R : Mem 64 → Prop} {m4 : Mem 64} {Q : Post [i64]} {X : XPost}
    {Jret : Cont [i64]} (hret : ret = 1#64)
    (hMarkRsn : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hJret : ∀ (xs : Tup Val [i64]) (m : Mem 64), (match xs with
      | (rret, ()) => ∃ extR sR,
        M6oRedSt c F0 F_cur s R extR sR m ∧ (rret = 0#64 ∨ rret = 1#64 ∨ rret = 20#64) ∧
        (rret = 20#64 → F0.Unsat) ∧ (rret = 1#64 → s.core.oom = 0#64 → sR.core.oom = 0#64)) →
      Jret xs m)
    (hst4 : M6oRedSt c F0 F_cur s R ext2 s4 m4)
    (hoom4 : s.core.oom = 0#64 → s4.core.oom = 0#64) (hrm4 : FullReasonsMarked s4) :
    wp Γ Q X (Expr.group (sig := [[i64]])
      (fun _Js => Blocks.cons (fun p => Expr.jump Jret (Arg.var p.fst, ())) Blocks.nil)
      fun Js => Expr.group (sig := [[]])
        (fun _Js_1 => Blocks.cons (fun _ =>
          Expr.group (sig := [[i64]])
            (fun _Js_2 => Blocks.cons (fun p => Expr.jump Js.fst (Arg.var p.fst, ())) Blocks.nil)
            fun Js => Expr.group (sig := [[]])
              (fun Js_2 => Blocks.cons (fun _ =>
                Expr.jnz (Arg.imm true)
                  (Expr.call (as := [i64]) (bs := [i64]) "full_arena_sweep"
                    (Arg.var c.hdr, ()) fun p =>
                    Expr.let_
                      { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                        args := (Arg.var p.fst, Arg.imm 2, ()) } fun p_1 =>
                      Expr.jnz (Arg.var p_1.fst) (Expr.jump Js.fst (Arg.imm 20, ()))
                        (Expr.let_
                          { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                            args := (Arg.var p.fst, Arg.imm 3, ()) } fun p_2 =>
                          Expr.jnz (Arg.var p_2.fst) (Expr.jump Js.fst (Arg.imm 0, ()))
                            (Expr.let_
                              { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                                args := (Arg.var p.fst, Arg.imm 0, ()) } fun p =>
                              Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.var ret, ()))
                                (Expr.call (as := [i64]) (bs := [i64]) "full_propagate"
                                    (Arg.var c.hdr, ()) fun p =>
                                  Expr.let_
                                    { sig := [i64, i64],
                                      code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                                      args := (Arg.var p.fst, Arg.imm 1, ()) } fun p_3 =>
                                    Expr.jnz (Arg.var p_3.fst) (Expr.jump Js.fst (Arg.imm 20, ()))
                                      (Expr.let_
                                        { sig := [i64, i64],
                                          code := OpCode.cmp CmpOp.ne i64 Ty.bool rfl,
                                          args := (Arg.var p.fst, Arg.imm 0, ()) } fun p =>
                                        Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.imm 0, ()))
                                          (Expr.let_
                                            { sig := [i64, i64], code := OpCode.add i64,
                                              args := (Arg.var c.hdr, Arg.imm 512, ()) } fun p =>
                                            Expr.store (t := i64) (Arg.imm 0) (Arg.var p.fst)
                                              (Expr.jump Js_2.fst ())))))))
                  (Expr.jump Js.fst (Arg.var ret, ()))) Blocks.nil)
              fun Js => Expr.jump Js.fst ()) Blocks.nil)
        fun Js_1 => Expr.jnz (Arg.var force) (Expr.jump Js_1.fst ())
          (Expr.group (sig := [[]])
            (fun _Js_2 => Blocks.cons (fun _ =>
              Expr.call (as := [i64, .bool]) (bs := []) "full_mark_reasons"
                (Arg.var c.hdr, Arg.imm false, ()) fun _ =>
                Expr.jump Js.fst (Arg.var ret, ())) Blocks.nil)
            fun Js => Expr.let_
              { sig := [i64, i64], code := OpCode.add i64,
                args := (Arg.var c.hdr, Arg.imm 512, ()) } fun p =>
              Expr.load i64 (Arg.var p.fst) fun ld =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                    args := (Arg.var ld, Arg.imm 0, ()) } fun p =>
                  Expr.jnz (Arg.var p.fst)
                    (Expr.let_
                      { sig := [i64, i64], code := OpCode.add i64,
                        args := (Arg.var c.hdr, Arg.imm 472, ()) } fun p =>
                      Expr.load i64 (Arg.var p.fst) fun ld =>
                        Expr.let_
                          { sig := [i64, i64], code := OpCode.mul i64,
                            args := (Arg.var ld, Arg.imm 4, ()) } fun p =>
                          Expr.let_
                            { sig := [i64, i64], code := OpCode.add i64,
                              args := (Arg.var c.hdr, Arg.imm 48, ()) } fun p_1 =>
                            Expr.load i64 (Arg.var p_1.fst) fun ld =>
                              Expr.let_
                                { sig := [i64, i64], code := OpCode.cmp CmpOp.uge i64 Ty.bool rfl,
                                  args := (Arg.var p.fst, Arg.var ld, ()) } fun p =>
                                Expr.jnz (Arg.var p.fst) (Expr.jump Js_1.fst ())
                                  (Expr.let_
                                    { sig := [i64, i64], code := OpCode.add i64,
                                      args := (Arg.var c.hdr, Arg.imm 48, ()) } fun p =>
                                    Expr.load i64 (Arg.var p.fst) fun ld =>
                                      Expr.let_
                                        { sig := [i64, i64], code := OpCode.mul i64,
                                          args := (Arg.var ld, Arg.imm 5, ()) } fun p =>
                                        Expr.let_
                                          { sig := [i64, i64], code := OpCode.add i64,
                                            args := (Arg.var c.hdr, Arg.imm 32, ()) } fun p_2 =>
                                          Expr.load i64 (Arg.var p_2.fst) fun ld =>
                                            Expr.let_
                                              { sig := [i64, i64], code := OpCode.mul i64,
                                                args := (Arg.var ld, Arg.imm 4, ()) } fun p_3 =>
                                              Expr.let_
                                                { sig := [i64, i64],
                                                  code := OpCode.cmp CmpOp.uge i64 Ty.bool rfl,
                                                  args := (Arg.var p.fst, Arg.var p_3.fst, ()) }
                                                fun p => Expr.jnz (Arg.var p.fst)
                                                  (Expr.jump Js_1.fst ()) (Expr.jump Js.fst ())))
                    (Expr.jump Js.fst ()))) m4 := by
  refine wp_join_group (fun ((rret : Val i64), ()) m5 => ∃ s5 : FullState,
      M6oRedSt c F0 F_cur s R ext2 s5 m5 ∧
      (rret = 0#64 ∨ rret = 1#64 ∨ rret = 20#64) ∧
      (rret = 20#64 → F0.Unsat) ∧
      (rret = 1#64 → s.core.oom = 0#64 → s5.core.oom = 0#64))
    (fun _ (rret, ()) m5 ⟨s5, hst5, hr5, hu5, ho5⟩ => by
      c0_hsteps_nogrp
      exact hJret (rret, ()) m5 ⟨ext2, s5, hst5, hr5, hu5, ho5⟩)
    (fun J5 hJ5 => by
      refine wp_join_group (fun _ mT => ∃ sT : FullState,
          M6oRedSt c F0 F_cur s R ext2 sT mT ∧
          (s.core.oom = 0#64 → sT.core.oom = 0#64) ∧ FullReasonsMarked sT)
        (fun _ _ mT ⟨sT, hstT, hoomT, hrmT⟩ => by
          refine wp_join_group (fun ((rret : Val i64), ()) mt => ∃ st : FullState,
              M6oRedSt c F0 F_cur s R ext2 st mt ∧
              (rret = 0#64 ∨ rret = 1#64 ∨ rret = 20#64) ∧
              (rret = 20#64 → F0.Unsat) ∧
              (rret = 1#64 → s.core.oom = 0#64 → st.core.oom = 0#64))
            (fun _ (rret, ()) mt h => hJ5 (rret, ()) mt h)
            (fun Jt hJt => @m6o_reduce_jt_loop Γ ret c F0 F_cur ext2 s sT R mT Q X Jt
              (Expr.jump Jt (Arg.var ret, ())) hret hProp hSweep hJt hstT hoomT hrmT))
        (fun JT hJT => by
          refine wp_m6Hdr_focus_frame hst4.mem fun hm4f => ?_
          c0_hsteps_nogrp
          · exact hJT () m4 ⟨s4, hst4, hoom4, hrm4⟩
          · refine wp_join_group (fun _ mE => ∃ sE : FullState,
                M6oRedSt c F0 F_cur s R ext2 sE mE ∧
                (s.core.oom = 0#64 → sE.core.oom = 0#64))
              (fun _ _ mE ⟨sE, hstE, hoomE⟩ => by
                refine wp_m6Hdr_focus_frame hstE.mem fun hmEf => ?_
                c0_call hMarkRsn
                refine ⟨c, F0, F_cur, sE, m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R,
                  rfl, hstE.inv.sparseW.1, hstE.inv.sparseW.2.1, hmEf,
                  fun ar5 m5 hl5 hrefs5 hper5 _ hw5 hm5 => ?_⟩
                c0_hsteps_nogrp
                simpa only [← hret] using hJ5 (1#64, ()) _
                  ⟨_, m6oRedSt_mark_reasons hstE hl5 hrefs5 hper5 hw5
                    (fullM6HdrMem_unfocus_full hm5), Or.inr (Or.inl rfl),
                    (fun h => absurd h (by decide)), fun _ => hoomE⟩)
              (fun JE hJE => by
                c0_hsteps_nogrp <;> first
                | exact hJT () m4 ⟨s4, hst4, hoom4, hrm4⟩
                | exact hJE () m4 ⟨s4, hst4, hoom4⟩)))

private theorem m6o_reduce_j4_mark_garb {Γ : Env} {rc : Val i64} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext2 : List (BitVec 64)} {s sL : FullState}
    {R : Mem 64 → Prop} {mL : Mem 64} {Q : Post [i64]} {X : XPost} {J4 : Cont []}
    (hIlog10 : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hSortReds : ∀ a m Q X, fullSortRedsSpec a m Q X → Γ "full_sort_reds" [i64, i64] [] a m Q X)
    (hJ4 : ∀ (xs : Tup Val []) (m : Mem 64), (∃ s4 : FullState,
      M6oRedSt c F0 F_cur s R ext2 s4 m ∧ (s.core.oom = 0#64 → s4.core.oom = 0#64) ∧
      FullReasonsMarked s4) → J4 xs m)
    (hrc_le : rc.toNat ≤ c.red_cap) (hstL : M6oRedSt c F0 F_cur s R ext2 sL mL)
    (hoomL : s.core.oom = 0#64 → sL.core.oom = 0#64) (hrmL : FullReasonsMarked sL)
    (hrrL : M6oRedRefsOk sL rc.toNat)
    (hmL : (FullMem c sL ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) mL) :
    wp Γ Q X (Expr.let_
      { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
        args := (Arg.var rc, Arg.imm 0, ()) } fun p_21 =>
      Expr.jnz (Arg.var p_21.fst)
        (Expr.call (as := [i64, i64]) (bs := []) "full_sort_reds"
            (Arg.var c.hdr, Arg.var rc, ()) fun _p_22 =>
          Expr.let_
            { sig := [i64, i64], code := OpCode.add i64,
              args := (Arg.var c.hdr, Arg.imm 688, ()) } fun p_23 =>
            Expr.load i64 (Arg.var p_23.fst) fun ld_6 =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var ld_6, Arg.imm 9, ()) } fun p_24 =>
                Expr.call (as := [i64]) (bs := [i64]) "full_ilog10"
                    (Arg.var p_24.fst, ()) fun p_25 =>
                  Expr.let_
                    { sig := [i64, i64], code := OpCode.udiv 64,
                      args := (Arg.imm 400, Arg.var p_25.fst, ()) } fun p_26 =>
                    Expr.let_
                      { sig := [i64, i64], code := OpCode.sub i64,
                        args := (Arg.imm 900, Arg.var p_26.fst, ()) } fun p_27 =>
                      Expr.let_
                        { sig := [i64, i64], code := OpCode.mul i64,
                          args := (Arg.var rc, Arg.var p_27.fst, ()) } fun p_28 =>
                        Expr.let_
                          { sig := [i64, i64], code := OpCode.udiv 64,
                            args := (Arg.var p_28.fst, Arg.imm 1000, ()) } fun p_29 =>
                          Expr.group (sig := [[i64]])
                            (fun Js_2 => Blocks.cons (fun p_30 =>
                              Expr.let_
                                { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
                                  args := (Arg.var p_30.fst, Arg.var p_29.fst, ()) } fun p_31 =>
                                Expr.jnz (Arg.var p_31.fst)
                                  (Expr.let_
                                    { sig := [i64, i64],
                                      code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
                                      args := (Arg.var p_30.fst, Arg.var rc, ()) } fun p_32 =>
                                    Expr.jnz (Arg.var p_32.fst)
                                      (Expr.let_
                                        { sig := [i64, i64], code := OpCode.mul i64,
                                          args := (Arg.var p_30.fst, Arg.imm 4, ()) } fun p_33 =>
                                        Expr.let_
                                          { sig := [i64, i64], code := OpCode.add i64,
                                            args := (Arg.var c.pRedRefs, Arg.var p_33.fst, ()) }
                                            fun p_34 =>
                                          Expr.load i32 (Arg.var p_34.fst) fun ld_7 =>
                                            Expr.let_
                                              { sig := [i32], code := OpCode.zext 32 64,
                                                args := (Arg.var ld_7, ()) } fun p_35 =>
                                              Expr.let_
                                                { sig := [i64, i64],
                                                  code := OpCode.mul i64,
                                                  args := (Arg.var p_35.fst, Arg.imm 4, ()) }
                                                  fun p_36 =>
                                                Expr.let_
                                                  { sig := [i64, i64],
                                                    code := OpCode.add i64,
                                                    args :=
                                                      (Arg.var c.pArena, Arg.var p_36.fst, ()) }
                                                    fun p_37 =>
                                                  Expr.load i32 (Arg.var p_37.fst) fun ld_8 =>
                                                    Expr.group (sig := [[]])
                                                      (fun _Js => Blocks.cons (fun _p =>
                                                        Expr.let_
                                                          { sig := [i64, i64],
                                                            code := OpCode.add i64,
                                                            args := (Arg.var p_30.fst,
                                                              Arg.imm 1, ()) } fun p =>
                                                          Expr.jump Js_2.fst (Arg.var p.fst, ()))
                                                        Blocks.nil)
                                                      fun Js =>
                                                      Expr.let_
                                                        { sig := [i32, i32],
                                                          code := OpCode.and i32,
                                                          args := (Arg.var ld_8,
                                                            Arg.imm 524288, ()) } fun p_38 =>
                                                        Expr.let_
                                                          { sig := [i32, i32],
                                                            code := OpCode.cmp CmpOp.eq i32
                                                              Ty.bool rfl,
                                                            args := (Arg.var p_38.fst,
                                                              Arg.imm 0, ()) } fun p_39 =>
                                  Expr.jnz (Arg.var p_39.fst)
                                    (Expr.let_
                                      { sig := [i64, i64], code := OpCode.mul i64,
                                        args := (Arg.var p_35.fst, Arg.imm 4, ()) } fun p_40 =>
                                      Expr.let_
                                        { sig := [i64, i64], code := OpCode.add i64,
                                          args := (Arg.var c.pArena, Arg.var p_40.fst, ()) }
                                          fun p_41 =>
                                        Expr.let_
                                          { sig := [i32, i32], code := OpCode.or i32,
                                            args := (Arg.var ld_8, Arg.imm 524288, ()) }
                                            fun p_42 =>
                                          Expr.store (t := i32) (Arg.var p_42.fst)
                                            (Arg.var p_41.fst)
                                            (Expr.let_
                                              { sig := [i64, i64], code := OpCode.add i64,
                                                args := (Arg.var c.hdr, Arg.imm 472, ()) }
                                                fun p_43 =>
                                              Expr.load i64 (Arg.var p_43.fst) fun ld_9 =>
                                                Expr.let_
                                                  { sig := [i64, i64], code := OpCode.add i64,
                                                    args := (Arg.var ld_9, Arg.imm 3, ()) }
                                                    fun p_44 =>
                                                  Expr.let_
                                                    { sig := [i64, i64], code := OpCode.add i64,
                                                      args := (Arg.var p_35.fst, Arg.imm 2, ()) }
                                                      fun p_45 =>
                                                    Expr.let_
                                                      { sig := [i64, i64], code := OpCode.mul i64,
                                                        args := (Arg.var p_45.fst, Arg.imm 4, ()) }
                                                        fun p_46 =>
                                                      Expr.let_
                                                        { sig := [i64, i64], code := OpCode.add i64,
                                                          args := (Arg.var c.pArena,
                                                            Arg.var p_46.fst, ()) } fun p_47 =>
                                                        Expr.load i32 (Arg.var p_47.fst) fun ld =>
                                                          Expr.let_
                                                            { sig := [i32],
                                                              code := OpCode.zext 32 64,
                                                              args := (Arg.var ld, ()) }
                                                              fun p_48 =>
                                                            Expr.let_
                                                              { sig := [i64, i64],
                                                                code := OpCode.add i64,
                                                                args := (Arg.var p_44.fst,
                                                                  Arg.var p_48.fst, ()) }
                                                                fun p_49 =>
                                                              Expr.let_
                                                                { sig := [i64, i64],
                                                                  code := OpCode.add i64,
                                                                  args := (Arg.var c.hdr,
                                                                    Arg.imm 472, ()) } fun p =>
                                                                Expr.store (t := i64)
                                                                  (Arg.var p_49.fst) (Arg.var p.fst)
                                                                  (Expr.jump Js.fst ())))
                                    (Expr.jump Js.fst ()))
                                      (Expr.jump J4 ()))
                                  (Expr.jump J4 ())) Blocks.nil)
                            (fun Js => Expr.jump Js.fst (Arg.imm 0, ())))
        (Expr.jump J4 ())) mL := by
  have hlenL := hstL.inv.sparseW.1
  c0_hsteps_nogrp
  · have hrr_bd : ∀ k < rc.toNat,
        (sL.scratch.red_refs[k]?.getD 0#32).toNat + 2 < c.arena_cap := fun k hk => by
      have hwf := (hstL.inv.sparseW.2.1.arena.refs_wf _ (hrrL k hk).1).1
      have halL := hlenL.core_ok.arena_len_le
      omega
    c0_call hSortReds
    refine ⟨c, sL, m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R, rfl, hlenL, hrc_le,
      hrr_bd, hmL, fun rr' mS hrr_len hpermS hmS => ?_⟩
    let scS : FullScratch := { sL.scratch with red_refs := rr' }
    have hstS := m6oRedSt_with_scratch hstL (sc' := scS)
      { hlenL.scratch_ok with red_refs_len := hrr_len }
      rfl rfl rfl (fullM6HdrMem_unfocus_full hmS)
    have hrrS : M6oRedRefsOk { sL with scratch := scS } rc.toNat := fun k hk => by
      obtain ⟨j, hj, heq⟩ := hpermS k hk
      change (scS.red_refs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs sL ∧
        (fullArenaHdr sL (scS.red_refs[k]?.getD 0#32).toNat &&& 0x00200000#32) = 0#32
      rw [heq]; exact hrrL j hj
    let sS : FullState := { sL with scratch := scS }
    c0_hsteps_nogrp
    c0_call hIlog10
    intro logv hlog1 _
    have hlog_ne : logv ≠ 0#64 := fun hz => by rw [hz] at hlog1; cases hlog1
    c0_hsteps_nogrp
    refine wp_loop_inv
      (fun (i, ()) mI => i.toNat ≤ rc.toNat ∧ ∃ sI : FullState,
        M6oRedSt c F0 F_cur s R ext2 sI mI ∧ (s.core.oom = 0#64 → sI.core.oom = 0#64) ∧
        FullReasonsMarked sI ∧ M6oRedRefsOk sI rc.toNat)
      (fun (i, ()) _ => rc.toNat - i.toNat)
      (fun JI hLoopI => by
        c0_hsteps_nogrp
        exact hLoopI (0#64, ()) _ ⟨Nat.zero_le _, sS,
          ⟨hstS.inv, hstS.cl, hstS.fu, hstS.cv, hstS.tmp, hstS.tl, hstS.ws2,
            hstS.pos, fullM6HdrMem_unfocus_full hmS⟩,
          hoomL, hrmL, hrrS⟩)
      (fun JI (i, ()) mI ⟨hi_le, sI, hstI, hoomI, hrmI, hrrI⟩ hLoopI => ?_)
    · have hlenI := hstI.inv.sparseW.1
      have hrrlI := hlenI.scratch_ok.red_refs_len
      have halI := hlenI.core_ok.arena_len_le
      have haarI := hlenI.core_ok.arena_len_arr
      clear hIlog10 hSortReds hrr_bd hmS hstS hrrS sS hlog1 hmL hstL hoomL hrmL hrrL hlenL
      refine wp_m6Hdr_focus_frame hstI.mem fun hmIf => ?_
      c0_hsteps_nogrp
      · have hi_lt : i.toNat < rc.toNat := by c0_bound
        have hi_rr : i.toNat < sI.scratch.red_refs.length := by omega
        have hcr_ok := hrrI i.toNat hi_lt
        have hcr_get : (sI.scratch.red_refs[i.toNat]'hi_rr).toNat =
            (sI.scratch.red_refs[i.toNat]?.getD 0#32).toNat := by
          rw [List.getElem?_eq_getElem hi_rr, Option.getD_some]
        have hcr_mem : (sI.scratch.red_refs[i.toNat]'hi_rr).toNat ∈
            fullArenaClauseRefs sI := by rw [hcr_get]; exact hcr_ok.1
        have hcr_norsn : (fullArenaHdr sI
            (sI.scratch.red_refs[i.toNat]'hi_rr).toNat &&& 0x00200000#32) = 0#32 := by
          rw [hcr_get]; exact hcr_ok.2
        have hcr_wf := hstI.inv.sparseW.2.1.arena.refs_wf _ hcr_mem
        have hcr_lt : (sI.scratch.red_refs[i.toNat]'hi_rr).toNat < sI.core.arena.length := by
          have := hcr_wf.1; omega
        have hi1 : (i + 1#64).toNat = i.toNat + 1 := by c0_bound
        have hcr_idx : ((sI.scratch.red_refs[i.toNat]'hi_rr).setWidth 64).toNat =
            (sI.scratch.red_refs[i.toNat]'hi_rr).toNat := by
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
            (Nat.lt_trans (sI.scratch.red_refs[i.toNat]'hi_rr).isLt (by decide))]
        have hcr_z_lt : ((sI.scratch.red_refs[i.toNat]'hi_rr).setWidth 64).toNat <
            sI.core.arena.length := by rw [hcr_idx]; exact hcr_lt
        c0_hsteps_nogrp
        refine wp_join_group (ts := []) (fun _ mN => ∃ sN : FullState,
            M6oRedSt c F0 F_cur s R ext2 sN mN ∧ (s.core.oom = 0#64 → sN.core.oom = 0#64) ∧
            FullReasonsMarked sN ∧ M6oRedRefsOk sN rc.toNat) ?_ ?_
        · rintro _ _ mN ⟨sN, hstN, hoomN, hrmN, hrrN⟩
          c0_hsteps_nogrp
          exact hLoopI (i + 1#64, ()) mN (by dsimp only; omega)
            ⟨by omega, sN, hstN, hoomN, hrmN, hrrN⟩
        · intro _Js hJs
          c0_hsteps_nogrp
          · simp only [hcr_idx] at hc hm
            obtain ⟨hstN, hrmN, _, hrrN⟩ := m6oRedSt_mark_garb (agN := _)
              hstI hrmI hrrI hcr_mem hcr_norsn (by omega)
              (fullM6HdrMem_unfocus hm)
            exact hJs () _ ⟨_, hstN, hoomI, hrmN, hrrN⟩
          · exact hJs () mI ⟨sI, hstI, hoomI, hrmI, hrrI⟩
      · exact hJ4 () mI ⟨sI, hstI, hoomI, hrmI⟩
      · exact hJ4 () mI ⟨sI, hstI, hoomI, hrmI⟩
  · exact hJ4 () mL ⟨sL, hstL, hoomL, hrmL⟩

private theorem m6o_reduce_unflushed {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext : List (BitVec 64)} {s s0 : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost} {J1 : Cont [i64]}
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hJ1 : ∀ (xs : Tup Val [i64]) (m : Mem 64), (match xs with
      | (ret, ()) => ∃ ext1 s1,
        M6oRedSt c F0 F_cur s R ext1 s1 m ∧ (ret = 0#64 ∨ ret = 1#64 ∨ ret = 20#64) ∧
        (ret = 20#64 → F0.Unsat) ∧ (ret = 1#64 → s.core.oom = 0#64 → s1.core.oom = 0#64)) →
      J1 xs m)
    (hst0 : M6oRedSt c F0 F_cur s R ext s0 m) (hlen0 : s0.LengthsOk c)
    (hs0_core : s0.core = s.core) :
    wp Γ Q X (Expr.let_
      { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var c.hdr, Arg.imm 512, ()) }
        fun p_10 =>
      Expr.load i64 (Arg.var p_10.fst) fun ld =>
        Expr.let_
          { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
            args := (Arg.var ld, Arg.imm 0, ()) } fun p_11 =>
          Expr.jnz (Arg.var p_11.fst)
            (Expr.group (sig := [[]])
              (fun _Js_1 => Blocks.cons (fun _p_12 =>
                Expr.call (as := [i64]) (bs := [i64]) "full_propagate" (Arg.var c.hdr, ())
                    fun p_13 =>
                  Expr.group (sig := [[i64]])
                    (fun _Js_2 => Blocks.cons (fun p => Expr.jump J1 (Arg.var p.fst, ()))
                      Blocks.nil)
                    fun Js =>
                    Expr.let_
                      { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                        args := (Arg.var p_13.fst, Arg.imm 1, ()) } fun p_14 =>
                      Expr.jnz (Arg.var p_14.fst) (Expr.jump Js.fst (Arg.imm 20, ()))
                        (Expr.group (sig := [[i64]])
                          (fun _Js_2 => Blocks.cons (fun p => Expr.jump Js.fst (Arg.var p.fst, ()))
                            Blocks.nil)
                          fun Js =>
                          Expr.let_
                            { sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64 Ty.bool rfl,
                              args := (Arg.var p_13.fst, Arg.imm 0, ()) } fun p_15 =>
                            Expr.jnz (Arg.var p_15.fst) (Expr.jump Js.fst (Arg.imm 0, ()))
                              (Expr.let_
                                { sig := [i64, i64], code := OpCode.add i64,
                                  args := (Arg.var c.hdr, Arg.imm 512, ()) } fun p =>
                                Expr.store (t := i64) (Arg.imm 0) (Arg.var p.fst)
                                  (Expr.jump Js.fst (Arg.imm 1, ()))))) Blocks.nil)
              fun Js =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var c.hdr, Arg.imm 160, ()) } fun p_12 =>
                Expr.load i64 (Arg.var p_12.fst) fun ld =>
                  Expr.let_
                    { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
                      args := (Arg.var ld, Arg.imm 0, ()) } fun p_13 =>
                    Expr.jnz (Arg.var p_13.fst)
                      (Expr.call (as := [i64, i64]) (bs := []) "full_backtrack"
                          (Arg.var c.hdr, Arg.imm 0, ()) fun _p =>
                        Expr.jump Js.fst ())
                      (Expr.jump Js.fst ()))
            (Expr.jump J1 (Arg.imm 1, ()))) m := by
  refine wp_m6Hdr_focus_frame hst0.mem fun hm0f => ?_
  c0_hsteps_nogrp
  · refine wp_join_group (fun _ mB => ∃ sB : FullState,
        M6oRedSt c F0 F_cur s R ext sB mB ∧ sB.core.cur_level = 0 ∧
        (s.core.oom = 0#64 → sB.core.oom = 0#64))
      (fun _ _ mB ⟨sB, hstB, hclB, hoomB⟩ => by
        c0_hsteps_nogrp
        refine m6o_call_fullBcpS15_red rfl (fun _ _ _ _ h => hProp _ _ _ _ h) hstB hclB
          fun pr sP mP hstP hclP _hteP hrP h0P h1P => ?_
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64]) (fun ((ret : Val i64), ()) mJ => ∃ sJ : FullState,
            M6oRedSt c F0 F_cur s R ext sJ mJ ∧ (ret = 0#64 ∨ ret = 1#64 ∨ ret = 20#64) ∧
            (ret = 20#64 → F0.Unsat) ∧ (ret = 1#64 → s.core.oom = 0#64 → sJ.core.oom = 0#64))
          ?_ ?_
        · rintro _ ⟨ret, ⟨⟩⟩ mJ ⟨sJ, hstJ, hrJ, huJ, hoJ⟩
          c0_hsteps_nogrp; exact hJ1 (ret, ()) mJ ⟨ext, sJ, hstJ, hrJ, huJ, hoJ⟩
        · intro Jp1 hJp1
          c0_hsteps_nogrp
          · exact hJp1 (20#64, ()) mP ⟨sP, hstP, Or.inr (Or.inr rfl),
              fun _ => h1P (by assumption), fun h => by cases h⟩
          · refine wp_join_group (ts := [i64]) (fun ((ret : Val i64), ()) mJ => ∃ sJ : FullState,
                M6oRedSt c F0 F_cur s R ext sJ mJ ∧
                (ret = 0#64 ∨ ret = 1#64 ∨ ret = 20#64) ∧
                (ret = 20#64 → F0.Unsat) ∧
                (ret = 1#64 → s.core.oom = 0#64 → sJ.core.oom = 0#64)) ?_ ?_
            · rintro _ ⟨ret, ⟨⟩⟩ mJ hJ
              c0_hsteps_nogrp; exact hJp1 (ret, ()) mJ hJ
            · intro Jp2 hJp2
              c0_hsteps_nogrp
              · exact hJp2 (0#64, ()) mP ⟨sP, hstP, Or.inl rfl,
                  fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
              · refine wp_m6Hdr_focus_frame hstP.mem fun hmPf => ?_
                c0_hsteps_nogrp
                exact hJp2 (1#64, ()) _ ⟨_, m6oRedSt_with_unflushed hstP 0#64
                    (fullM6HdrMem_unfocus (by assumption)),
                  Or.inr (Or.inl rfl), fun h => absurd h (by decide),
                  fun _ hso => h0P (by assumption) (hoomB hso)⟩)
      (fun JB hJB => by
        c0_hsteps_nogrp
        · c0_call hBacktrack
          refine ⟨c, s0, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hlen0,
            by have hmax := c.hmaxv; unfold dimacsBound at hmax
               have := hst0.inv.sparseW.2.1.cur_level_le
               have := hlen0.core_ok.trail_end_le
               have := hlen0.core_ok.cur_vars_le; omega,
            fun _ => by
              have hmax := c.hmaxv; unfold dimacsBound at hmax
              have := hst0.inv.sparseW.2.1.cur_level_le
              have := hlen0.core_ok.trail_end_le
              have := hlen0.core_ok.cur_vars_le; omega,
            hst0.inv.sparseW.2.1.trail_lits_lt, hm0f,
            fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
              hlen' _ _ hcl' _ hsc' _ _ hw' _ hm' => ?_⟩
          have hcl'0 : cl' = 0 := by simpa using hcl'
          subst hcl'0
          obtain ⟨ta', ba', pt', pb', hp', ps', hl', qsi', qss', hsc_eq⟩ := hsc'
          c0_hsteps_nogrp
          exact hJB () _
            ⟨_, m6oRedSt_backtrack0 hst0 hlen'
              (hw' F0 F_cur hst0.inv.sparseW.2.1 (Nat.zero_le _))
              (by rw [hsc_eq]) (by rw [hsc_eq]) (by rw [hsc_eq])
              (fullM6HdrMem_unfocus_full hm'),
              rfl, fun h => by dsimp only; rwa [hs0_core]⟩
        · have hcl0 : s0.core.cur_level = 0 := by
            have hmax := c.hmaxv; unfold dimacsBound at hmax
            have hle := hlen0.core_ok.trail_end_le
            have hcv := hlen0.core_ok.cur_vars_le
            have hcl := hst0.inv.sparseW.2.1.cur_level_le
            c0_bound
          exact hJB () m ⟨s0, hst0, hcl0, fun h => hs0_core ▸ h⟩)
  · exact hJ1 (1#64, ()) m
      ⟨ext, s0, hst0, Or.inr (Or.inl rfl), fun h => absurd h (by decide),
        fun _ hso => by rwa [hs0_core]⟩

theorem full_reduce_m6_wp (Γ : Env)
    (hIsqrt : ∀ a m Q X, fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hIlog10 : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hRecomp : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_recompute_tiers" [i64] [] a m Q X)
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hMarkRsn : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hSortReds : ∀ a m Q X, fullSortRedsSpec a m Q X →
      Γ "full_sort_reds" [i64, i64] [] a m Q X)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X) :
    ∀ a m Q X, m6ReduceSpec a m Q X → Func.wp Γ full_reduce_m6_body a m Q X := by
  rintro ⟨h, force, ⟨⟩⟩ m Q X hs
  rcases m6ReduceSpec_elim hs with ⟨c, F0, F_cur, ext, s, R, rfl, hinv, hm0, hQ⟩
  have har_cap : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hred_cap : c.red_cap < 2 * 2 ^ 28 := c.hred
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  unfold Func.wp full_reduce_m6_body
  have hst_init := m6oRedSt_refl hinv hm0
  refine wp_m6Hdr_focus_frame hm0 fun hmf => ?_
  c0_hsteps_nogrp
  c0_call hIsqrt
  intro r_isq _ _ _
  dsimp only
  c0_hsteps_nogrp
  let s0 : FullState := { s with scratch :=
    { s.scratch with
      reductions := s.scratch.reductions + 1#64
      reduce_limit := s.scratch.conflicts + 1000#64 * r_isq } }
  have hlen0 : s0.LengthsOk c :=
    ⟨hinv.sparseW.1.core_ok, { hinv.sparseW.1.scratch_ok with
      walk_vals_len := hinv.sparseW.1.scratch_ok.walk_vals_len }⟩
  have hmf0 : (FullMem c s0 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m := by
    simpa only [s0, BitVec.ofNat_eq_ofNat] using hm
  have hst0 : M6oRedSt c F0 F_cur s R ext s0 m :=
    m6oRedSt_with_scratch hst_init hlen0.scratch_ok rfl rfl rfl (fullM6HdrMem_unfocus hmf0)
  refine wp_join_group (fun ((ret : Val i64), ()) m1 => ∃ ext1 s1,
      M6oRedSt c F0 F_cur s R ext1 s1 m1 ∧ (ret = 0#64 ∨ ret = 1#64 ∨ ret = 20#64) ∧
      (ret = 20#64 → F0.Unsat) ∧ (ret = 1#64 → s.core.oom = 0#64 → s1.core.oom = 0#64)) ?_ ?_
  · rintro J1 ⟨ret, ⟨⟩⟩ m1 ⟨ext1, s1, hst1, hr1, hu1, ho1⟩
    refine wp_join_group (fun ((rret : Val i64), ()) mr => ∃ extR sR,
        M6oRedSt c F0 F_cur s R extR sR mr ∧ (rret = 0#64 ∨ rret = 1#64 ∨ rret = 20#64) ∧
        (rret = 20#64 → F0.Unsat) ∧ (rret = 1#64 → s.core.oom = 0#64 → sR.core.oom = 0#64))
      (fun _ (rret, ()) mr ⟨extR, sR, hstR, hrR, huR, hoR⟩ => by
        refine wp_m6Hdr_focus_frame hstR.mem fun hmRf => ?_
        c0_hsteps_nogrp
        refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hSetWm _ _ _ _ h) hstR.inv.cfgOk
          hstR.inv.extOk hstR.inv.sparseW.1 (fullM6HdrMem_unfocus hmRf)
          fun _ extR1 sR1 mR1 hcR1 hlR1 hmsR1 hextR1 _ hmR1 => ?_
        have hstR1 := m6oRedSt_w2a hstR hcR1 hlR1 hmsR1 hextR1 hmR1
        refine wp_m6Hdr_focus_frame hstR1.mem fun hmR1f => ?_
        c0_hsteps_nogrp
        refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hSetWm _ _ _ _ h) hstR1.inv.cfgOk
          hstR1.inv.extOk hstR1.inv.sparseW.1 (fullM6HdrMem_unfocus hmR1f)
          fun _ extR2 sR2 mR2 hcR2 hlR2 hmsR2 hextR2 _ hmR2 => ?_
        have hstR2 := m6oRedSt_w2a hstR1 hcR2 hlR2 hmsR2 hextR2 hmR2
        c0_hsteps_nogrp
        exact hQ rret extR2 sR2 mR2 hstR2.inv hrR hstR2.cl hstR2.fu hstR2.cv hstR2.tmp hstR2.tl
          hstR2.ws2 huR (fun h1 hso => by rw [hcR2, hcR1]; exact hoR h1 hso) (fun _ => hstR2.pos)
          hstR2.mem)
      (fun Jret hJret => by
        c0_hsteps_nogrp
        · have hc_ret : ret = 1#64 := hc
          have hoom1 : s.core.oom = 0#64 → s1.core.oom = 0#64 := ho1 hc_ret
          refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hRecomp _ _ _ _ h) hst1.inv.cfgOk
            hst1.inv.extOk hst1.inv.sparseW.1 hst1.mem
            fun _ ext2 s2 m2 hc2 hl2 hms2 hext2 _ hm2 => ?_
          have hst2 := m6oRedSt_w2a hst1 hc2 hl2 hms2 hext2 hm2
          have hoom2 : s.core.oom = 0#64 → s2.core.oom = 0#64 := fun h => hc2 ▸ hoom1 h
          c0_hsteps_nogrp
          c0_call hMarkRsn
          refine ⟨c, F0, F_cur, s2, m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R, rfl,
            hst2.inv.sparseW.1, hst2.inv.sparseW.2.1, fullM6HdrMem_focus_full hst2.mem,
            fun ar3 m3 hl3 hrefs3 hper3 hrm3 hw3 hm3 => ?_⟩
          have hst3 := m6oRedSt_mark_reasons hst2 hl3 hrefs3 hper3 hw3
            (fullM6HdrMem_unfocus_full hm3)
          have hrm3' : FullReasonsMarked { s2 with core := { s2.core with arena := ar3 } } :=
            hrm3 rfl
          have hoom3 : s.core.oom = 0#64 →
              ({ s2 with core := { s2.core with arena := ar3 } } : FullState).core.oom = 0#64 :=
            hoom2
          let s3 : FullState := { s2 with core := { s2.core with arena := ar3 } }
          refine wp_m6Hdr_focus_frame hst3.mem fun hm3f => ?_
          c0_hsteps_nogrp
          refine wp_loop_inv
            (fun (rc, p, ()) mL =>
              rc.toNat ≤ c.red_cap ∧ p.toNat ≤ s3.core.arena_len ∧
              (p.toNat = s3.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s3) ∧
              ∃ sL : FullState,
                sL.core.arena_len = s3.core.arena_len ∧
                M6oRedSt c F0 F_cur s R ext2 sL mL ∧
                (s.core.oom = 0#64 → sL.core.oom = 0#64) ∧
                FullReasonsMarked sL ∧ fullArenaClauseRefs sL = fullArenaClauseRefs s3 ∧
                M6oRedRefsOk sL rc.toNat ∧
                (FullMem c sL ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) mL)
            (fun (_, p, ()) _ => s3.core.arena_len - p.toNat)
            (fun JL hLoopL => by
              c0_hsteps_nogrp
              refine hLoopL (0#64, 0#64, ()) m3 ⟨Nat.zero_le _, Nat.zero_le _, ?_, s3, rfl,
                hst3, hoom3, hrm3', rfl, fun _ h => by simp at h, hm3f⟩
              by_cases hz : s3.core.arena_len = 0
              · exact Or.inl hz.symm
              · exact Or.inr (Full.FullDenseWatchHelpers.fullArenaClauseRefs_zero_mem
                  hst3.inv.sparseW.2.1.arena (Nat.pos_of_ne_zero hz)))
            (fun JL (rc, p, ()) mL
                ⟨hrc_le, hp_le, hp_mem, sL, halenL, hstL, hoomL, hrmL, hrefsL, hrrL, hmL⟩
                hLoopL => ?_)
          · have hlenL := hstL.inv.sparseW.1
            have halL := hlenL.core_ok.arena_len_le
            have haarL := hlenL.core_ok.arena_len_arr
            have hrrlL := hlenL.scratch_ok.red_refs_len
            c0_hsteps_nogrp
            · have hp_lt : p.toNat < sL.core.arena_len := by c0_bound
              have hp_in : p.toNat ∈ fullArenaClauseRefs sL := by
                rw [hrefsL]; exact hp_mem.resolve_left (by omega)
              have hp_wf := hstL.inv.sparseW.2.1.arena.refs_wf p.toNat hp_in
              have hp_lt32 : p.toNat < 2 ^ 32 := by omega
              have hp_trunc : (p.setWidth 32).toNat = p.toNat := by
                rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt hp_lt32
              c0_call hArenaNext
              refine ⟨c, sL, m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R, rfl, hlenL, hmL, ?_⟩
              have hnb := fullArenaNextOff_bounds (ar := sL.core.arena) (alen := sL.core.arena_len)
                (cref := p.toNat) hp_wf.1
              have hnxt_mem := FullDenseWatchHelpers.fullArenaClauseRefs_next_mem
                hstL.inv.sparseW.2.1.arena hp_in
              have hn_eq : ((BitVec.ofNat 32 (fullArenaNextOff sL.core.arena sL.core.arena_len
                  (p.setWidth 32).toNat)).setWidth 64).toNat =
                  fullArenaNextOff sL.core.arena sL.core.arena_len p.toNat := by
                rw [hp_trunc, BitVec.toNat_setWidth, bv32_ofNat_toNat (by omega)]
                exact Nat.mod_eq_of_lt (by omega)
              refine wp_join_group
                (fun (rc', ()) mN =>
                  rc'.toNat ≤ c.red_cap ∧
                  ∃ sN : FullState,
                    sN.core.arena_len = s3.core.arena_len ∧
                    M6oRedSt c F0 F_cur s R ext2 sN mN ∧
                    (s.core.oom = 0#64 → sN.core.oom = 0#64) ∧
                    FullReasonsMarked sN ∧ fullArenaClauseRefs sN = fullArenaClauseRefs s3 ∧
                    M6oRedRefsOk sN rc'.toNat ∧
                    (FullMem c sN ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) mN)
                (fun _ (rc', ()) mN ⟨hrcN, sN, halenN, hstN, hoomN, hrmN, hrefsN, hrrN, hmN⟩ => by
                  c0_hsteps_nogrp
                  exact hLoopL (rc', _, ()) mN (by dsimp only; rw [hn_eq]; omega)
                    ⟨hrcN, by rw [hn_eq]; omega,
                      by rw [hn_eq]
                         rcases hnxt_mem with hend | hmem
                         · exact Or.inl (hend.trans halenL)
                         · exact Or.inr (hrefsL ▸ hmem),
                      sN, halenN, hstN, hoomN, hrmN, hrefsN, hrrN, hmN⟩)
                (fun JN hJN => ?_)
              c0_hsteps_nogrp
              · refine wp_join_group
                  (fun _ mU =>
                    ∃ sU : FullState,
                      sU.core.arena_len = s3.core.arena_len ∧
                      M6oRedSt c F0 F_cur s R ext2 sU mU ∧
                      (s.core.oom = 0#64 → sU.core.oom = 0#64) ∧
                      FullReasonsMarked sU ∧ fullArenaClauseRefs sU = fullArenaClauseRefs s3 ∧
                      M6oRedRefsOk sU rc.toNat ∧
                      (fullArenaHdr sU p.toNat &&& 0x00200000#32) =
                        (sL.core.arena[p.toNat]'(by omega) &&& 0x00200000#32) ∧
                      (FullMem c sU ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) mU)
                  (fun _ _ mU ⟨sU, halenU, hstU, hoomU, hrmU, hrefsU, hrrU, hhdrU, hmU⟩ => by
                    have hlenU := hstU.inv.sparseW.1
                    have hrrlU := hlenU.scratch_ok.red_refs_len
                    c0_hsteps_nogrp
                    refine wp_join_group
                      (fun (rc', ()) mR =>
                        rc'.toNat ≤ c.red_cap ∧
                        ∃ sR : FullState,
                          sR.core.arena_len = s3.core.arena_len ∧
                          M6oRedSt c F0 F_cur s R ext2 sR mR ∧
                          (s.core.oom = 0#64 → sR.core.oom = 0#64) ∧
                          FullReasonsMarked sR ∧ fullArenaClauseRefs sR = fullArenaClauseRefs s3 ∧
                          M6oRedRefsOk sR rc'.toNat ∧
                          (FullMem c sR ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) mR)
                      (fun _ (rc', ()) mR hR => by c0_hsteps_nogrp; exact hJN (rc', ()) mR hR)
                      (fun JR hJR => by
                        c0_hsteps_nogrp
                        · have hno_rsn : (fullArenaHdr sU p.toNat &&& 0x00200000#32) = 0#32 := by
                            rw [hhdrU]; exact hc
                          have hp_inU : p.toNat ∈ fullArenaClauseRefs sU := by
                            rw [hrefsU]; exact hp_mem.resolve_left (by omega)
                          refine wp_join_group (fun (_ : Tup Val [.bool]) mK => mK = mU)
                            (by
                              rintro _ ⟨keep, ⟨⟩⟩ mK rfl
                              refine wp_join_group
                                (fun (rc', ()) mR =>
                                  rc'.toNat ≤ c.red_cap ∧
                                  ∃ sR : FullState,
                                    sR.core.arena_len = s3.core.arena_len ∧
                                    M6oRedSt c F0 F_cur s R ext2 sR mR ∧
                                    (s.core.oom = 0#64 → sR.core.oom = 0#64) ∧
                                    FullReasonsMarked sR ∧
                                    fullArenaClauseRefs sR = fullArenaClauseRefs s3 ∧
                                    M6oRedRefsOk sR rc'.toNat ∧
                                    (FullMem c sR ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) mR)
                                (fun _ (rc', ()) mR hR => by
                                  c0_hsteps_nogrp; exact hJR (rc', ()) mR hR)
                                (fun Jrc2 hJrc2 => by
                                  c0_hsteps_nogrp
                                  · exact hJrc2 (rc, ()) mK ⟨hrc_le, sU, halenU, hstU, hoomU,
                                      hrmU, hrefsU, hrrU, hmU⟩
                                  · have hrc_lt : rc.toNat < c.red_cap := by
                                      have := BitVec.lt_def.mp (by assumption :
                                        rc < BitVec.ofNat 64 c.red_cap)
                                      rw [bv64_ofNat_toNat (by omega)] at this; exact this
                                    have hrc1 : (rc + 1#64).toNat = rc.toNat + 1 := by
                                      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
                                      exact Nat.mod_eq_of_lt (by omega)
                                    c0_hsteps_nogrp
                                    let scU' : FullScratch := { sU.scratch with
                                      red_refs := sU.scratch.red_refs.set rc.toNat (p.setWidth 32) }
                                    let sU' : FullState := { sU with scratch := scU' }
                                    have hmU' : (FullMem c sU' ⋆
                                        (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) m := hm
                                    have hstU' := m6oRedSt_with_scratch hstU (sc' := scU')
                                      { hlenU.scratch_ok with
                                        red_refs_len := by simp [scU', hrrlU] }
                                      rfl rfl rfl (fullM6HdrMem_unfocus hmU')
                                    have hp_sw : p.setWidth 32 = BitVec.ofNat 32 p.toNat :=
                                      BitVec.eq_of_toNat_eq
                                        (by rw [hp_trunc, bv32_ofNat_toNat hp_lt32])
                                    have hrrU' : M6oRedRefsOk sU' (rc + 1#64).toNat := by
                                      dsimp only [sU', scU']; rw [hrc1, hp_sw]
                                      exact m6oRedRefsOk_push hrrlU hrc_lt hp_lt32 hp_inU
                                        hno_rsn hrrU
                                    exact hJrc2 (rc + 1#64, ()) _ ⟨by omega, sU', halenU, hstU',
                                      hoomU, hrmU, hrefsU, hrrU', hmU'⟩
                                  · exact hJrc2 (rc, ()) mK ⟨hrc_le, sU, halenU, hstU, hoomU,
                                      hrmU, hrefsU, hrrU, hmU⟩))
                            (fun JK hJK => by
                              c0_hsteps_nogrp
                              refine wp_join_group (fun (_ : Tup Val []) mS => mS = mU)
                                (fun _ _ mS hmS => by
                                  cases hmS; c0_hsteps_nogrp <;> exact hJK (_, ()) mU rfl)
                                (fun Js hJs => by
                                  c0_hsteps_nogrp
                                  · exact hJK (true, ()) mU rfl
                                  · exact hJs () mU rfl
                                  · exact hJs () mU rfl))
                        · exact hJR (rc, ()) mU ⟨hrc_le, sU, halenU, hstU, hoomU, hrmU, hrefsU,
                            hrrU, hmU⟩))
                  (fun JU hJU => by
                    c0_hsteps_nogrp
                    · let sU : FullState :=
                        { core := { sL.core with
                            arena := sL.core.arena.set p.toNat
                              ((sL.core.arena[p.toNat]'(by omega) &&& 0x07FFFFFF#32) |||
                                ((((sL.core.arena[p.toNat]'(by omega) >>> (27 : Nat)) &&&
                                  31#32) - 1#32) <<< (27 : Nat))) }
                          scratch := sL.scratch }
                      have hmUf : (FullMem c sU ⋆
                          (m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R)) m := hm
                      obtain ⟨hstU, hrmU, hrefsU, hrrU, hhdrU⟩ := m6oRedSt_update_used
                        (u := (((sL.core.arena[p.toNat]'(by omega) >>> (27 : Nat))
                        &&& 31#32) - 1#32)) hstL hrmL hrrL hp_in (by omega)
                        (fullM6HdrMem_unfocus hmUf)
                      exact hJU () m ⟨sU, halenL, hstU, hoomL, hrmU, hrefsU.trans hrefsL, hrrU,
                        hhdrU, hmUf⟩
                    · have hhdr_eq :
                          fullArenaHdr sL p.toNat = sL.core.arena[p.toNat]'(by omega) := by
                        unfold fullArenaHdr fullArenaHdrCore
                        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                      exact hJU () mL ⟨sL, halenL, hstL, hoomL, hrmL, hrefsL, hrrL,
                        by rw [hhdr_eq], hmL⟩)
              all_goals exact hJN (rc, ()) mL ⟨hrc_le, sL, halenL, hstL, hoomL, hrmL, hrefsL, hrrL,
                hmL⟩
            · refine wp_join_group
                (fun _ m4 => ∃ s4 : FullState, M6oRedSt c F0 F_cur s R ext2 s4 m4 ∧
                  (s.core.oom = 0#64 → s4.core.oom = 0#64) ∧ FullReasonsMarked s4)
                ?_ ?_
              · rintro _ _ m4 ⟨s4, hst4, hoom4, hrm4⟩
                exact m6o_reduce_j4_post hc_ret hMarkRsn hProp hSweep hJret hst4 hoom4 hrm4
              · intro J4 hJ4
                exact m6o_reduce_j4_mark_garb hIlog10 hSortReds hJ4 hrc_le hstL hoomL hrmL
                  hrrL hmL
        · exact hJret (ret, ()) m1 ⟨ext1, s1, hst1, hr1, hu1, ho1⟩)
  · intro J1 hJ1
    exact m6o_reduce_unflushed hBacktrack hProp hJ1 hst0 hlen0 rfl

end ReduceM6

end LeanQbe.T.Examples.Kissat.FullM6Orch
