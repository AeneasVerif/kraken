/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Collect
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
import LeanQbe.T.Examples.Kissat.Proof.Collect.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersWatch
import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersArena
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Sweep-Copy WP Proof (`Proof.Collect.WpSweepCopy`)

Canonical `Func.wp` proof for `full_sweep_copy` from `Src.Collect`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Collect

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Collect
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullKissatMath
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
open Kraken.Bedrock2.Test
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Collect.M6Tactics1

public section

/-! ## 1. Pure Helpers (`sc_*`, `Sc*Inv`) -/

private abbrev ScPost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (src dst : BitVec 64) (old_sz : BitVec 32)
    (at_root : Bool) (Q : Post [i64]) : Prop :=
  ∀ (r : BitVec 64) (arena' : List (BitVec 32)) (vals' : List (BitVec 8))
    (flags' lvl' rsns' trl' tp' : List (BitVec 32)) (te' : Nat) (unass' unfl' : BitVec 64)
    (wvec' wstk' : List (BitVec 32)) (wlen' : Nat) (wu' nb' oom' : BitVec 64)
    (ph' : List (BitVec 8)) (wsort' : List (BitVec 32)) (m' : Mem 64),
    let s' : FullState :=
      { core := { s.core with
          unassigned := unass', wlen := wlen', wusable := wu', num_binary := nb',
          unflushed := unfl', trail_end := te', oom := oom', vals := vals',
          flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          wvec := wvec', arena := arena', wstk := wstk' }
        scratch := { s.scratch with phases := ph', wsort := wsort' } }
    s'.LengthsOk c →
    OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + old_sz.toNat) s.core.arena arena' →
    (at_root = false →
      r = old_sz.setWidth 64 ∧ vals' = s.core.vals ∧ flags' = s.core.flags ∧
      lvl' = s.core.lvl ∧ rsns' = s.core.rsns ∧ trl' = s.core.trl ∧
      tp' = s.core.trail_pos ∧ te' = s.core.trail_end ∧ unass' = s.core.unassigned ∧
      unfl' = s.core.unflushed ∧ wvec' = s.core.wvec ∧ wstk' = s.core.wstk ∧
      wlen' = s.core.wlen ∧ wu' = s.core.wusable ∧ nb' = s.core.num_binary ∧
      oom' = s.core.oom ∧ ph' = s.scratch.phases ∧ wsort' = s.scratch.wsort ∧
      ∀ j < old_sz.toNat, arena'[dst.toNat + 3 + j]? = s.core.arena[src.toNat + 3 + j]?) →
    (at_root = true →
      FullWitnessInv c F0 F_cur { s'.core with arena_len := dst.toNat } ∧
      FullBinOnlyWatchesInv F_cur s'.core ∧
      s.core.trail_end ≤ te' ∧
      (r = 0xFFFFFFFE#64 ∨ r = 0xFFFFFFFD#64 ∨ r = 1#64 ∨ r = 0xFFFFFFFF#64 ∨
        (3 ≤ r.toNat ∧ r.toNat ≤ old_sz.toNat)) ∧
      (r = 0xFFFFFFFE#64 → F0.Unsat) ∧
      (r = 0xFFFFFFFD#64 → oom' = 1#64) ∧
      (r ≠ 0xFFFFFFFD#64 → oom' = s.core.oom) ∧
      (r = 1#64 → s.core.trail_end < te') ∧
      (3 ≤ r.toNat ∧ r.toNat ≤ old_sz.toNat →
        (∀ j < r.toNat, (arena'[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
        List.Sublist (((arena'.drop (dst.toNat + 3)).take r.toNat).map BitVec.toNat)
          (((s.core.arena.drop (src.toNat + 3)).take old_sz.toNat).map BitVec.toNat) ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause (((arena'.drop (dst.toNat + 3)).take r.toNat).map BitVec.toNat)))) →
    (FullMem c s' ⋆ R) m' → Q (r, ()) m'

private abbrev scArState (s : FullState) (ar : List (BitVec 32)) : FullState :=
  { s with core := { s.core with arena := ar } }

private abbrev scNew1State (s : FullState) (arL : List (BitVec 32)) (u : BitVec 32)
    (flags' : List (BitVec 32)) (unass' : BitVec 64) (phases' : List (BitVec 8)) : FullState :=
  { core := { s.core with
      unassigned := unass', unflushed := s.core.unflushed + 1#64,
      trail_end := s.core.trail_end + 1,
      vals := (s.core.vals.set u.toNat 1#8).set (u.toNat ^^^ 1) 255#8,
      flags := flags', lvl := s.core.lvl.set (u.toNat / 2) 0#32,
      rsns := s.core.rsns.set (u.toNat / 2) 0xFFFFFFFF#32,
      trl := s.core.trl.set s.core.trail_end u,
      trail_pos := s.core.trail_pos.set (u.toNat / 2) (BitVec.ofNat 32 s.core.trail_end),
      arena := arL }
    scratch := { s.scratch with phases := phases' } }

private theorem bv8_domain_sext_lt0 {x : BitVec 8}
    (hx : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    BitVec.slt (BitVec.signExtend 32 x) (BitVec.signExtend 32 (BitVec.truncate 8 0#32)) = true ↔
      x = 0xFF#8 := by
  rcases hx with rfl | rfl | rfl <;> decide

private theorem bv8_domain_sext_gt0 {x : BitVec 8}
    (hx : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    BitVec.slt (BitVec.signExtend 32 (BitVec.truncate 8 0#32)) (BitVec.signExtend 32 x) = true ↔
      x = 1#8 := by
  rcases hx with rfl | rfl | rfl <;> decide

private theorem bv8_domain_sext_eq0 {x : BitVec 8}
    (hx : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    BitVec.signExtend 32 x = BitVec.signExtend 32 (BitVec.truncate 8 0#32) ↔ x = 0#8 := by
  rcases hx with rfl | rfl | rfl <;> decide

private theorem bv32_shr1_ofNat (x : BitVec 32) : (x >>> (1 : BitVec 32)).toNat = x.toNat / 2 :=
  bv32_shr1_toNat x

private theorem bv32_bin_watch_props {l : BitVec 32} (hl : l.toNat < 2 ^ 30) :
    let w := (l &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    (w &&& 0x80000000#32) ≠ 0#32 ∧ w ≠ 0xFFFFFFFF#32 ∧
    (w &&& 0x7FFFFFFF#32).toNat = l.toNat := by
  intro w
  have hl31 : l.toNat < 2 ^ 31 := by omega
  have hand : l &&& 0x7FFFFFFF#32 = l := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hl31]
  have hlo : w &&& 0x7FFFFFFF#32 = l := by
    dsimp only [w]
    rw [BitVec.and_or_distrib_right, BitVec.and_assoc,
      show (0x7FFFFFFF#32 &&& 0x7FFFFFFF#32 : BitVec 32) = 0x7FFFFFFF#32 from rfl,
      show (0x80000000#32 &&& 0x7FFFFFFF#32 : BitVec 32) = 0#32 from rfl, BitVec.or_zero, hand]
  have hhi : w &&& 0x80000000#32 = 0x80000000#32 := by
    dsimp only [w]
    rw [BitVec.and_or_distrib_right, BitVec.and_assoc,
      show (0x7FFFFFFF#32 &&& 0x80000000#32 : BitVec 32) = 0#32 from rfl,
      show (0x80000000#32 &&& 0x80000000#32 : BitVec 32) = 0x80000000#32 from rfl,
      BitVec.and_zero, BitVec.zero_or]
  refine ⟨by rw [hhi]; decide, fun he => ?_, by rw [hlo]⟩
  have h1 := congrArg (fun x : BitVec 32 => (x &&& 0x7FFFFFFF#32).toNat) he
  rw [hlo, show (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl] at h1
  omega

private theorem sc_arenaInv_with_core {c : FullCfg} {F_cur : List (List Nat)}
    {k0 k1 : FullCoreState} (ha : FullArenaClausesInv c F_cur k0)
    (har : k1.arena = k0.arena) (hal : k1.arena_len = k0.arena_len)
    (hcv : k1.cur_vars = k0.cur_vars) :
    FullArenaClausesInv c F_cur k1 := by
  have hrefs : fullArenaClauseRefsCore k1 = fullArenaClauseRefsCore k0 :=
    fullArenaClauseRefsCore_congr hal fun r _ => by
      unfold fullArenaNextOff; simp only [har]
  have hsz : ∀ r, fullArenaClauseSizeCore k1 r = fullArenaClauseSizeCore k0 r := fun r => by
    unfold fullArenaClauseSizeCore; rw [har]
  have hhdr : ∀ r, fullArenaHdrCore k1 r = fullArenaHdrCore k0 r := fun r => by
    unfold fullArenaHdrCore; rw [har]
  have hgarb : ∀ r, fullArenaClauseGarbCore k1 r = fullArenaClauseGarbCore k0 r := fun r => by
    unfold fullArenaClauseGarbCore; rw [hhdr]
  have hlits : ∀ r, fullArenaClauseLitsCore k1 r = fullArenaClauseLitsCore k0 r := fun r => by
    unfold fullArenaClauseLitsCore; rw [har, hsz]
  refine ⟨by rw [hal]; exact ha.len_ok,
    fun r hr => by
      have h := ha.refs_wf r (hrefs ▸ hr)
      simpa only [har, hal, hsz, fullArenaNextOff] using h,
    fun r hr hsh => by
      rw [hrefs] at hr; rw [hhdr] at hsh
      obtain ⟨t, ht1, ht2, ht3⟩ := ha.shrk_term r hr hsh
      exact ⟨t, by rw [hsz]; exact ht1, by rw [hal]; exact ht2, by rw [har]; exact ht3⟩,
    fun r hr hng l hl => by
      rw [hrefs] at hr; rw [hgarb] at hng; rw [hlits] at hl; rw [hcv]
      exact ha.lits_lt r hr hng l hl,
    fun r hr hng => by
      rw [hrefs] at hr; rw [hgarb] at hng; rw [hlits]
      exact ha.entails r hr hng⟩

private theorem sc_witness_with_ar {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {dst : Nat} {arL : List (BitVec 32)}
    (har_len : s.core.arena.length = c.arena_cap) (hdst_le : dst ≤ c.arena_cap)
    (hw_dst : FullWitnessInv c F0 F_cur { s.core with arena_len := dst })
    (harL : arL.length = c.arena_cap) (hpre : ∀ idx < dst, arL[idx]? = s.core.arena[idx]?) :
    FullWitnessInv c F0 F_cur { s.core with arena := arL, arena_len := dst } := by
  let k0 : FullCoreState := { s.core with arena_len := dst }
  let k1 : FullCoreState := { s.core with arena := arL, arena_len := dst }
  have hk0_ar : k0.arena.length = c.arena_cap := har_len
  have hk1_ar : k1.arena.length = c.arena_cap := harL
  have hnxt := hw_dst.arena.arenaNextOff_extend (arena' := arL) (alen' := dst) (Nat.le_refl _)
    (fun i hi => hpre i hi)
  have hrefs : fullArenaClauseRefsCore k1 = fullArenaClauseRefsCore k0 :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hcl : ∀ r ∈ fullArenaClauseRefsCore k0,
      fullArenaHdrCore k1 r = fullArenaHdrCore k0 r ∧
      fullArenaClauseSizeCore k1 r = fullArenaClauseSizeCore k0 r ∧
      fullArenaClauseGarbCore k1 r = fullArenaClauseGarbCore k0 r ∧
      fullArenaClauseLitsCore k1 r = fullArenaClauseLitsCore k0 r := fun r hr => by
    have hwf := hw_dst.arena.refs_wf r hr; dsimp [k0] at hwf
    have hwf1 := hwf.2.2.1; have hwf2 := hwf.2.2.2.1
    have h0 := hpre r (by omega); have h2 := hpre (r + 2) (by omega)
    have hsz : fullArenaClauseSizeCore k1 r = fullArenaClauseSizeCore k0 r := by
      unfold fullArenaClauseSizeCore; dsimp [k1, k0]; rw [h2]
    refine ⟨by unfold fullArenaHdrCore; dsimp [k1, k0]; rw [h0], hsz,
      by unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp [k1, k0]; rw [h0],
      fullArenaClauseLitsCore_eq_of_hold
        (by dsimp only [k0] at hwf2 ⊢; rw [hk0_ar]; omega)
        (by dsimp only [k0] at hwf2 ⊢; rw [hk1_ar]; omega) hsz
        fun j hj => hpre (r + 3 + j) (by dsimp only [k0] at hj; omega)⟩
  change FullWitnessInv c F0 F_cur k1
  refine { hw_dst with
    arena := ⟨hw_dst.arena.len_ok,
      fun r hr => by
        rw [hrefs] at hr; have h := hw_dst.arena.refs_wf r hr
        dsimp [k1, k0] at hnxt h ⊢; rw [hnxt r hr, (hcl r hr).2.1]; exact h,
      fun r hr hsh => by
        rw [hrefs] at hr; rw [(hcl r hr).1] at hsh
        obtain ⟨t, ht1, ht2, ht3⟩ := hw_dst.arena.shrk_term r hr hsh
        dsimp [k0] at ht1 ht2 ht3
        exact ⟨t, by dsimp [k1]; rw [(hcl r hr).2.1]; exact ht1, ht2,
          by dsimp [k1]; rw [hpre t ht2]; exact ht3⟩,
      fun r hr hng l hl => by
        rw [hrefs] at hr; rw [(hcl r hr).2.2.1] at hng; rw [(hcl r hr).2.2.2] at hl
        exact hw_dst.arena.lits_lt r hr hng l hl,
      fun r hr hng => by
        rw [hrefs] at hr; rw [(hcl r hr).2.2.1] at hng; rw [(hcl r hr).2.2.2]
        exact hw_dst.arena.entails r hr hng⟩
    watches := hw_dst.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
    reason_inv := fun idx hidx hne => by
      have hrs := hw_dst.reason_inv idx hidx hne; dsimp only [k1, k0] at hrs ⊢
      by_cases hb : (k0.rsns[(k0.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
      · rw [ite_eq_left hb] at hrs ⊢; exact hrs
      · rw [ite_eq_right hb] at hrs ⊢
        have hc := hcl _ hrs.1
        exact ⟨hrefs ▸ hrs.1, hc.2.2.1.trans hrs.2.1, fun q hq => hrs.2.2 q (hc.2.2.2 ▸ hq)⟩
    reason_lit_mem := fun idx hidx hne hlg => by
      have hrs := hw_dst.reason_inv idx hidx hne
      have hb : ¬ (k0.rsns[(k0.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
      rw [ite_eq_right hb] at hrs
      exact (hcl _ hrs.1).2.2.2 ▸ hw_dst.reason_lit_mem idx hidx hne hlg }

private def ScNoZredPrefix (s : FullState) (src : BitVec 64) (n : Nat) : Prop :=
  (s.core.arena[src.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 →
  ∀ j < n,
    let v := (s.core.arena[src.toNat + 3 + j]?.getD 0#32).toNat / 2
    v < s.core.cur_vars → (s.core.flags[v]?.getD 0#32 &&& 1#32) ≠ 0#32

private def ScLoopInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (src dst : BitVec 64) (old_sz : BitVec 32) (p : Tup Val [i32, i32]) (mL : Mem 64) : Prop :=
  let (new_sz, i, ()) := p
  new_sz.toNat ≤ i.toNat ∧ i.toNat ≤ old_sz.toNat ∧
  ∃ arL : List (BitVec 32), arL.length = c.arena_cap ∧
    OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + new_sz.toNat) s.core.arena arL ∧
    (∀ j < new_sz.toNat, (arL[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    List.Sublist (((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat)
      (((s.core.arena.drop (src.toNat + 3)).take i.toNat).map BitVec.toNat) ∧
    (∀ l ∈ ((s.core.arena.drop (src.toNat + 3)).take i.toNat).map BitVec.toNat,
      l ∈ ((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat ∨
        (l < 2 * s.core.cur_vars ∧ (s.core.lvl[l / 2]?.getD 0#32).toNat = 0 ∧
          s.core.vals[l]?.getD 0#8 = 0xFF#8)) ∧
    ScNoZredPrefix s src i.toNat ∧ (FullMem c (scArState s arL) ⋆ R) mL

private def ScJoinInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (src dst : BitVec 64) (i : BitVec 32) (p : Tup Val [i32]) (m' : Mem 64) : Prop :=
  let (new_sz', ()) := p
  new_sz'.toNat ≤ i.toNat + 1 ∧
  ∃ ar' : List (BitVec 32), ar'.length = c.arena_cap ∧
    OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + new_sz'.toNat) s.core.arena ar' ∧
    (∀ j < new_sz'.toNat, (ar'[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    List.Sublist (((ar'.drop (dst.toNat + 3)).take new_sz'.toNat).map BitVec.toNat)
      (((s.core.arena.drop (src.toNat + 3)).take (i.toNat + 1)).map BitVec.toNat) ∧
    (∀ l ∈ ((s.core.arena.drop (src.toNat + 3)).take (i.toNat + 1)).map BitVec.toNat,
      l ∈ ((ar'.drop (dst.toNat + 3)).take new_sz'.toNat).map BitVec.toNat ∨
        (l < 2 * s.core.cur_vars ∧ (s.core.lvl[l / 2]?.getD 0#32).toNat = 0 ∧
          s.core.vals[l]?.getD 0#8 = 0xFF#8)) ∧
    ScNoZredPrefix s src (i.toNat + 1) ∧ (FullMem c (scArState s ar') ⋆ R) m'

private theorem drop_take_add_one_eq {α : Type} (xs : List α) {off n : Nat}
    (hn : off + n < xs.length) :
    (xs.drop off).take (n + 1) = (xs.drop off).take n ++ [xs[off + n]'hn] := by
  have h1 : n < (xs.drop off).length := by simp; omega
  rw [List.take_add_one, List.getElem?_eq_getElem h1, Option.toList_some, List.getElem_drop]

private theorem sc_step_drop {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {src dst : BitVec 64} {old_sz new_sz i : BitVec 32} {arL : List (BitVec 32)} {mL : Mem 64}
    (hlen : s.LengthsOk c) (hsro : src.toNat + 3 + old_sz.toNat ≤ s.core.arena_len)
    (hi_lt : i.toNat < old_sz.toNat) (hnz_i : new_sz.toNat ≤ i.toNat)
    (harL : arL.length = c.arena_cap)
    (hout : OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + new_sz.toNat) s.core.arena arL)
    (hlits : ∀ j < new_sz.toNat, (arL[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hsub : List.Sublist (((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat)
      (((s.core.arena.drop (src.toNat + 3)).take i.toNat).map BitVec.toNat))
    (hdrop : ∀ l ∈ ((s.core.arena.drop (src.toNat + 3)).take i.toNat).map BitVec.toNat,
      l ∈ ((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat ∨
        (l < 2 * s.core.cur_vars ∧ (s.core.lvl[l / 2]?.getD 0#32).toNat = 0 ∧
          s.core.vals[l]?.getD 0#8 = 0xFF#8))
    (hnozr : ScNoZredPrefix s src (i.toNat + 1))
    (hlit_lt : (s.core.arena[src.toNat + 3 + i.toNat]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hlvl0 : (s.core.lvl[(s.core.arena[src.toNat + 3 + i.toNat]?.getD 0#32).toNat / 2]?.getD
      0#32).toNat = 0)
    (hff : s.core.vals[(s.core.arena[src.toNat + 3 + i.toNat]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8)
    (hmL : (FullMem c (scArState s arL) ⋆ R) mL) :
    ScJoinInv c s R src dst i (new_sz, ()) mL := by
  have hlen_ar := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have hs_lt : src.toNat + 3 + i.toNat < s.core.arena.length := by omega
  have htake : (((s.core.arena.drop (src.toNat + 3)).take (i.toNat + 1)).map BitVec.toNat) =
      (((s.core.arena.drop (src.toNat + 3)).take i.toNat).map BitVec.toNat) ++
        [(s.core.arena[src.toNat + 3 + i.toNat]'hs_lt).toNat] := by
    rw [drop_take_add_one_eq _ hs_lt, List.map_append, List.map_singleton]
  refine ⟨by omega, arL, harL, hout, hlits, ?_, ?_, hnozr, hmL⟩
  · rw [htake]; simpa using hsub.append (List.nil_sublist _)
  · intro l hl; rw [htake, List.mem_append, List.mem_singleton] at hl
    rcases hl with hl_prev | rfl
    · exact hdrop l hl_prev
    · right
      rw [List.getElem?_eq_getElem hs_lt, Option.getD_some] at hlit_lt hlvl0 hff
      exact ⟨hlit_lt, hlvl0, hff⟩

private theorem sc_step_keep {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {src dst : BitVec 64} {old_sz new_sz i : BitVec 32} {arL : List (BitVec 32)}
    {lit : BitVec 32} {m' : Mem 64}
    (hlen : s.LengthsOk c) (hsro : src.toNat + 3 + old_sz.toNat ≤ s.core.arena_len)
    (hds : dst.toNat ≤ src.toNat) (hi_lt : i.toNat < old_sz.toNat) (hnz_i : new_sz.toNat ≤ i.toNat)
    (harL : arL.length = c.arena_cap)
    (hout : OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + new_sz.toNat) s.core.arena arL)
    (hlits : ∀ j < new_sz.toNat, (arL[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hsub : List.Sublist (((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat)
      (((s.core.arena.drop (src.toNat + 3)).take i.toNat).map BitVec.toNat))
    (hdrop : ∀ l ∈ ((s.core.arena.drop (src.toNat + 3)).take i.toNat).map BitVec.toNat,
      l ∈ ((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat ∨
        (l < 2 * s.core.cur_vars ∧ (s.core.lvl[l / 2]?.getD 0#32).toNat = 0 ∧
          s.core.vals[l]?.getD 0#8 = 0xFF#8))
    (hnozr : ScNoZredPrefix s src (i.toNat + 1))
    (hlit_eq : s.core.arena[src.toNat + 3 + i.toNat]? = some lit)
    (hlit_lt : lit.toNat < 2 * s.core.cur_vars)
    (hm' : (FullMem c (scArState s (arL.set (dst.toNat + 3 + new_sz.toNat) lit)) ⋆ R) m') :
    ScJoinInv c s R src dst i (new_sz + 1#32, ()) m' := by
  have hlen_ar := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have har_cap := c.harena; have hdb : dimacsBound = 2 ^ 28 := rfl
  have hnz1_lt : new_sz.toNat + 1 < 2 ^ 32 := by omega
  have hnz1 : (new_sz + 1#32).toNat = new_sz.toNat + 1 := by
    rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
      Nat.mod_eq_of_lt hnz1_lt]
  let pos := dst.toNat + 3 + new_sz.toNat
  let ar' := arL.set pos lit
  have hpos_lt : pos < arL.length := by omega
  have hs_lt : src.toNat + 3 + i.toNat < s.core.arena.length := by omega
  have hlit_get : s.core.arena[src.toNat + 3 + i.toNat]'hs_lt = lit := by
    rw [List.getElem?_eq_getElem hs_lt] at hlit_eq; exact Option.some.inj hlit_eq
  have hdrop_pre : (ar'.drop (dst.toNat + 3)).take new_sz.toNat =
      (arL.drop (dst.toNat + 3)).take new_sz.toNat := by
    refine List.ext_getElem (by simp [ar', pos]) fun j hj1 _ => ?_
    simp only [List.getElem_take, List.getElem_drop, ar', pos]
    have hj_lt : j < new_sz.toNat := by simp [ar', pos] at hj1; omega
    have hne : pos ≠ dst.toNat + 3 + j := by dsimp [pos]; omega
    rw [List.getElem_set_ne hne]
  have htake_ar' : ((ar'.drop (dst.toNat + 3)).take (new_sz.toNat + 1)).map BitVec.toNat =
      ((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat ++ [lit.toNat] := by
    have hbd : pos < ar'.length := by simp [ar', pos]; omega
    rw [drop_take_add_one_eq _ hbd, hdrop_pre, List.map_append, List.map_singleton]
    have hel : ar'[pos]'hbd = lit := List.getElem_set_self hbd
    simp only [pos] at hel; rw [hel]
  have htake_src : (((s.core.arena.drop (src.toNat + 3)).take (i.toNat + 1)).map BitVec.toNat) =
      (((s.core.arena.drop (src.toNat + 3)).take i.toNat).map BitVec.toNat) ++ [lit.toNat] := by
    rw [drop_take_add_one_eq _ hs_lt, hlit_get, List.map_append, List.map_singleton]
  refine ⟨by rw [hnz1]; omega, ar', by simp [ar', harL], ?_, ?_, ?_, ?_, hnozr, hm'⟩
  · intro j hj; rw [hnz1] at hj
    by_cases hjn : j = pos
    · subst hjn; dsimp [pos] at hj; omega
    · simp only [ar', List.getElem?_set_ne (Ne.symm hjn)]
      exact hout j (by dsimp [pos] at hjn; omega)
  · intro j hj; rw [hnz1] at hj
    by_cases hjn : j = new_sz.toNat
    · subst hjn; simp only [ar', pos, List.getElem?_set_self hpos_lt, Option.getD_some]
      exact hlit_lt
    · simp only [ar', pos, List.getElem?_set_ne (by omega : dst.toNat + 3 + new_sz.toNat ≠
        dst.toNat + 3 + j)]
      exact hlits j (by omega)
  · rw [hnz1, htake_ar', htake_src]; exact hsub.append (List.Sublist.refl _)
  · intro l hl
    rw [htake_src, List.mem_append, List.mem_singleton] at hl
    rw [hnz1, htake_ar', List.mem_append, List.mem_singleton]
    rcases hl with hl_prev | rfl
    · rcases hdrop l hl_prev with hin | hfl
      · exact Or.inl (Or.inl hin)
      · exact Or.inr hfl
    · exact Or.inl (Or.inr rfl)

private theorem sc_ret_sat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {src dst : BitVec 64} {old_sz : BitVec 32}
    {at_root : Bool} {Q : Post [i64]} {arL : List (BitVec 32)} {mL : Mem 64}
    (hlen : s.LengthsOk c) (hdst_le : dst.toNat ≤ c.arena_cap) (_hsz_lt : old_sz.toNat < 2 * 2 ^ 28)
    (har_t : at_root = true)
    (hw_dst : FullWitnessInv c F0 F_cur { s.core with arena_len := dst.toNat })
    (hbin0 : FullBinOnlyWatchesInv F_cur s.core)
    (hQ : ScPost c F0 F_cur s R src dst old_sz at_root Q)
    (harL : arL.length = c.arena_cap)
    (hout : OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + old_sz.toNat) s.core.arena arL)
    (hmL : (FullMem c (scArState s arL) ⋆ R) mL) :
    Q (0xFFFFFFFF#64, ()) mL := by
  have hbin_k : BinOnlyWatchesInv F_cur { s.core with arena := arL } :=
    (FullBinOnlyWatchesInv.toBinOnly hbin0).with_core rfl rfl rfl rfl
  exact hQ 0xFFFFFFFF#64 arL s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl
    s.core.trail_pos s.core.trail_end s.core.unassigned s.core.unflushed s.core.wvec s.core.wstk
    s.core.wlen s.core.wusable s.core.num_binary s.core.oom s.scratch.phases s.scratch.wsort mL
    ⟨{ hlen.core_ok with arena_len_arr := harL }, hlen.scratch_ok⟩ hout
    (fun hf => Bool.noConfusion (har_t.symm.trans hf))
    (fun _ => ⟨sc_witness_with_ar (s := s) hlen.core_ok.arena_len_arr hdst_le hw_dst harL
        (fun idx hidx => hout idx (Or.inl (by omega))),
      hbin_k.toFull, Nat.le_refl _, Or.inr (Or.inr (Or.inr (Or.inl rfl))),
      (fun h => by cases h), (fun h => by cases h), (fun _ => rfl), (fun h => by cases h),
      (fun ⟨_, hle⟩ => by revert hle; simp; omega)⟩) hmL

private theorem sc_ret_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {src dst : BitVec 64} {old_sz : BitVec 32}
    {at_root : Bool} {Q : Post [i64]} {arL : List (BitVec 32)} {mL : Mem 64}
    (hlen : s.LengthsOk c) (hdst_le : dst.toNat ≤ c.arena_cap) (_hsz_lt : old_sz.toNat < 2 * 2 ^ 28)
    (har_t : at_root = true)
    (hw_dst : FullWitnessInv c F0 F_cur { s.core with arena_len := dst.toNat })
    (hbin0 : FullBinOnlyWatchesInv F_cur s.core)
    (hQ : ScPost c F0 F_cur s R src dst old_sz at_root Q)
    (harL : arL.length = c.arena_cap)
    (hout : OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + old_sz.toNat) s.core.arena arL)
    (hunsat : F0.Unsat)
    (hmL : (FullMem c (scArState s arL) ⋆ R) mL) :
    Q (0xFFFFFFFE#64, ()) mL := by
  have hbin_k : BinOnlyWatchesInv F_cur { s.core with arena := arL } :=
    (FullBinOnlyWatchesInv.toBinOnly hbin0).with_core rfl rfl rfl rfl
  exact hQ 0xFFFFFFFE#64 arL s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl
    s.core.trail_pos s.core.trail_end s.core.unassigned s.core.unflushed s.core.wvec s.core.wstk
    s.core.wlen s.core.wusable s.core.num_binary s.core.oom s.scratch.phases s.scratch.wsort mL
    ⟨{ hlen.core_ok with arena_len_arr := harL }, hlen.scratch_ok⟩ hout
    (fun hf => Bool.noConfusion (har_t.symm.trans hf))
    (fun _ => ⟨sc_witness_with_ar (s := s) hlen.core_ok.arena_len_arr hdst_le hw_dst harL
        (fun idx hidx => hout idx (Or.inl (by omega))),
      hbin_k.toFull, Nat.le_refl _, Or.inl rfl, (fun _ => hunsat),
      (fun h => by cases h), (fun _ => rfl), (fun h => by cases h),
      (fun ⟨_, hle⟩ => by revert hle; simp; omega)⟩) hmL

private theorem sc_ret_keep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {src dst : BitVec 64} {old_sz new_sz : BitVec 32}
    {at_root : Bool} {Q : Post [i64]} {arL : List (BitVec 32)} {mL : Mem 64}
    (hlen : s.LengthsOk c) (hdst_le : dst.toNat ≤ c.arena_cap) (hsz_lt : old_sz.toNat < 2 * 2 ^ 28)
    (har_t : at_root = true) (h3 : 3 ≤ new_sz.toNat) (hne_old : new_sz.toNat ≤ old_sz.toNat)
    (hw_dst : FullWitnessInv c F0 F_cur { s.core with arena_len := dst.toNat })
    (hbin0 : FullBinOnlyWatchesInv F_cur s.core)
    (horig : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (List.map BitVec.toNat
        (List.take old_sz.toNat (List.drop (src.toNat + 3) s.core.arena)))))
    (hQ : ScPost c F0 F_cur s R src dst old_sz at_root Q)
    (harL : arL.length = c.arena_cap)
    (hout : OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + old_sz.toNat) s.core.arena arL)
    (hlits : ∀ j < new_sz.toNat, (arL[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hsub : List.Sublist (((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat)
      (((s.core.arena.drop (src.toNat + 3)).take old_sz.toNat).map BitVec.toNat))
    (hdrop : ∀ l ∈ ((s.core.arena.drop (src.toNat + 3)).take old_sz.toNat).map BitVec.toNat,
      l ∈ ((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat ∨
        (l < 2 * s.core.cur_vars ∧ (s.core.lvl[l / 2]?.getD 0#32).toNat = 0 ∧
          s.core.vals[l]?.getD 0#8 = 0xFF#8))
    (hmL : (FullMem c (scArState s arL) ⋆ R) mL) :
    Q (new_sz.setWidth 64, ()) mL := by
  have hz : (new_sz.setWidth 64).toNat = new_sz.toNat := zext_toNat new_sz (by decide)
  have hge3 : 3 ≤ (new_sz.setWidth 64).toNat ∧ (new_sz.setWidth 64).toNat ≤ old_sz.toNat := by
    rw [hz]; exact ⟨h3, hne_old⟩
  have hne2 : new_sz.setWidth 64 ≠ 0xFFFFFFFE#64 := fun h => by
    have h1 := congrArg BitVec.toNat h
    rw [hz, show (0xFFFFFFFE#64 : BitVec 64).toNat = 4294967294 from rfl] at h1; omega
  have hne3 : new_sz.setWidth 64 ≠ 0xFFFFFFFD#64 := fun h => by
    have h1 := congrArg BitVec.toNat h
    rw [hz, show (0xFFFFFFFD#64 : BitVec 64).toNat = 4294967293 from rfl] at h1; omega
  have hne4 : new_sz.setWidth 64 ≠ 1#64 := fun h => by
    have h1 := congrArg BitVec.toNat h
    rw [hz, show (1#64 : BitVec 64).toNat = 1 from rfl] at h1; omega
  have hent := level0_entails_of_filter hw_dst horig hdrop
  have hbin_k : BinOnlyWatchesInv F_cur { s.core with arena := arL } :=
    (FullBinOnlyWatchesInv.toBinOnly hbin0).with_core rfl rfl rfl rfl
  exact hQ (new_sz.setWidth 64) arL s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl
    s.core.trail_pos s.core.trail_end s.core.unassigned s.core.unflushed s.core.wvec s.core.wstk
    s.core.wlen s.core.wusable s.core.num_binary s.core.oom s.scratch.phases s.scratch.wsort mL
    ⟨{ hlen.core_ok with arena_len_arr := harL }, hlen.scratch_ok⟩ hout
    (fun hf => Bool.noConfusion (har_t.symm.trans hf))
    (fun _ => ⟨sc_witness_with_ar (s := s) hlen.core_ok.arena_len_arr hdst_le hw_dst harL
        (fun idx hidx => hout idx (Or.inl (by omega))),
      hbin_k.toFull, Nat.le_refl _, Or.inr (Or.inr (Or.inr (Or.inr hge3))),
      (fun h => absurd h hne2), (fun h => absurd h hne3), (fun _ => rfl),
      (fun h => absurd h hne4), (fun _ => ⟨fun j hj => hlits j (hz ▸ hj), hz ▸ hsub, hz ▸ hent⟩)⟩)
    hmL

private theorem sc_ret_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {src dst : BitVec 64} {old_sz : BitVec 32}
    {at_root : Bool} {Q : Post [i64]} {arL wvec' wstk' wsort' : List (BitVec 32)}
    {wlen' : Nat} {wu' : BitVec 64} {m' : Mem 64}
    (hlen : s.LengthsOk c) (hdst_le : dst.toNat ≤ c.arena_cap) (_hsz_lt : old_sz.toNat < 2 * 2 ^ 28)
    (har_t : at_root = true)
    (hw_dst : FullWitnessInv c F0 F_cur { s.core with arena_len := dst.toNat })
    (harL : arL.length = c.arena_cap)
    (hout : OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + old_sz.toNat) s.core.arena arL)
    (hlen' : ({ core := { s.core with arena := arL, wvec := wvec', wstk := wstk', wlen := wlen',
                                       wusable := wu', oom := 1#64 },
                 scratch := { s.scratch with wsort := wsort' } } : FullState).LengthsOk c)
    (hbin' : BinOnlyWatchesInv F_cur
      { s.core with arena := arL, wvec := wvec', wstk := wstk', wlen := wlen',
                    wusable := wu', oom := 1#64 })
    (hQ : ScPost c F0 F_cur s R src dst old_sz at_root Q)
    (hm' : (FullMem c
      { core := { s.core with arena := arL, wvec := wvec', wstk := wstk', wlen := wlen',
                              wusable := wu', oom := 1#64 },
        scratch := { s.scratch with wsort := wsort' } } ⋆ R) m') :
    Q (0xFFFFFFFD#64, ()) m' := by
  have hw0 := sc_witness_with_ar (s := s) hlen.core_ok.arena_len_arr hdst_le hw_dst harL
    (fun idx hidx => hout idx (Or.inl (by omega)))
  let k1 : FullCoreState :=
    { s.core with arena := arL, arena_len := dst.toNat, wvec := wvec', wstk := wstk',
                  wlen := wlen', wusable := wu', oom := 1#64 }
  have hbin_k1 : BinOnlyWatchesInv F_cur k1 := hbin'.with_core rfl rfl rfl rfl
  have hbin_f : BinOnlyWatchesInv F_cur
      { s.core with arena := arL, wvec := wvec', wstk := wstk', wlen := wlen',
                    wusable := wu', oom := 1#64 } := hbin'.with_core rfl rfl rfl rfl
  have hw1 : FullWitnessInv c F0 F_cur k1 :=
    { hw0 with
      arena := sc_arenaInv_with_core hw0.arena rfl rfl rfl
      watches := hbin_k1.toModeWatchesInv }
  exact hQ 0xFFFFFFFD#64 arL s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl
    s.core.trail_pos s.core.trail_end s.core.unassigned s.core.unflushed wvec' wstk' wlen'
    wu' s.core.num_binary 1#64 s.scratch.phases wsort' m' hlen' hout
    (fun hf => Bool.noConfusion (har_t.symm.trans hf))
    (fun _ => ⟨hw1, hbin_f.toFull, Nat.le_refl _,
      Or.inr (Or.inl rfl), (fun h => by cases h), (fun _ => rfl),
      (fun h => absurd rfl h), (fun h => by cases h),
      (fun ⟨_, hle⟩ => by revert hle; simp; omega)⟩) hm'

private theorem sc_ret_new1 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {src dst : BitVec 64} {old_sz : BitVec 32}
    {at_root : Bool} {Q : Post [i64]} {arL : List (BitVec 32)} {u : BitVec 32}
    {flags' : List (BitVec 32)} {unass' : BitVec 64} {phases' : List (BitVec 8)} {m' : Mem 64}
    (hlen : s.LengthsOk c) (hdst_le : dst.toNat ≤ c.arena_cap) (_hsz_lt : old_sz.toNat < 2 * 2 ^ 28)
    (har_t : at_root = true) (hcl0 : s.core.cur_level = 0)
    (hw_dst : FullWitnessInv c F0 F_cur { s.core with arena_len := dst.toNat })
    (hbin0 : FullBinOnlyWatchesInv F_cur s.core)
    (harL : arL.length = c.arena_cap)
    (hout : OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + old_sz.toNat) s.core.arena arL)
    (hu_lt : u.toNat < 2 * s.core.cur_vars) (hun : s.core.vals[u.toNat]?.getD 0#8 = 0#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [u.toNat]))
    (hf' : flags'.length = c.max_vars) (hp' : phases'.length = c.max_vars)
    (hQ : ScPost c F0 F_cur s R src dst old_sz at_root Q)
    (hm' : (FullMem c (scNew1State s arL u flags' unass' phases') ⋆ R) m') :
    Q (1#64, ()) m' := by
  have hw0 := sc_witness_with_ar (s := s) hlen.core_ok.arena_len_arr hdst_le hw_dst harL
    (fun idx hidx => hout idx (Or.inl (by omega)))
  have hlen0 : ({ s.core with arena := arL, arena_len := dst.toNat } : FullCoreState).LengthsOk c :=
    { hlen.core_ok with arena_len_arr := harL, arena_len_le := hdst_le }
  have hw1 := level0Assign_preserves_witness hlen0 hw0 hcl0 hu_lt hun hent flags' unass'
    (s.core.unflushed + 1#64)
  have hte_lt := hw0.trail_end_lt_of_unassigned hu_lt hun
  have hcv := hlen.core_ok.cur_vars_le
  have hprop_le : s.core.propagated ≤ s.core.trail_end + 1 := by
    have := hlen.core_ok.propagated_le; omega
  have hte_le1 : s.core.trail_end + 1 ≤ s.core.cur_vars := hte_lt
  have hlen' : (scNew1State s arL u flags' unass' phases').LengthsOk c :=
    ⟨{ hlen.core_ok with
      arena_len_arr := harL, flags_len := hf',
      vals_len := by simp [hlen.core_ok.vals_len], lvl_len := by simp [hlen.core_ok.lvl_len],
      rsns_len := by simp [hlen.core_ok.rsns_len], trl_len := by simp [hlen.core_ok.trl_len],
      trail_pos_len := by simp [hlen.core_ok.trail_pos_len],
      propagated_le := hprop_le, trail_end_le := hte_le1 },
     { hlen.scratch_ok with phases_len := hp' }⟩
  have hbin_f : BinOnlyWatchesInv F_cur (scNew1State s arL u flags' unass' phases').core :=
    (FullBinOnlyWatchesInv.toBinOnly hbin0).with_core rfl rfl rfl rfl
  exact hQ 1#64 arL ((s.core.vals.set u.toNat 1#8).set (u.toNat ^^^ 1) 255#8)
    flags' (s.core.lvl.set (u.toNat / 2) 0#32) (s.core.rsns.set (u.toNat / 2) 0xFFFFFFFF#32)
    (s.core.trl.set s.core.trail_end u)
    (s.core.trail_pos.set (u.toNat / 2) (BitVec.ofNat 32 s.core.trail_end))
    (s.core.trail_end + 1) unass' (s.core.unflushed + 1#64) s.core.wvec s.core.wstk s.core.wlen
    s.core.wusable s.core.num_binary s.core.oom phases' s.scratch.wsort m' hlen' hout
    (fun hf => Bool.noConfusion (har_t.symm.trans hf))
    (fun _ => ⟨hw1, hbin_f.toFull, Nat.le_succ _, Or.inr (Or.inr (Or.inl rfl)),
      (fun h => by cases h), (fun h => by cases h), (fun _ => rfl),
      (fun _ => Nat.lt_succ_self _), (fun ⟨hle, _⟩ => by revert hle; simp)⟩) hm'

private theorem sc_ret_new2_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {src dst : BitVec 64} {old_sz : BitVec 32}
    {at_root : Bool} {Q : Post [i64]} {arL wvec' wstk' wsort' : List (BitVec 32)}
    {wlen' : Nat} {wu' : BitVec 64} {m' : Mem 64}
    (hlen : s.LengthsOk c) (hdst_le : dst.toNat ≤ c.arena_cap) (_hsz_lt : old_sz.toNat < 2 * 2 ^ 28)
    (har_t : at_root = true)
    (hw_dst : FullWitnessInv c F0 F_cur { s.core with arena_len := dst.toNat })
    (harL : arL.length = c.arena_cap)
    (hout : OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + old_sz.toNat) s.core.arena arL)
    (hlen' : ({ core := { s.core with arena := arL, wvec := wvec', wstk := wstk', wlen := wlen',
                                       wusable := wu', num_binary := s.core.num_binary + 1#64 },
                 scratch := { s.scratch with wsort := wsort' } } : FullState).LengthsOk c)
    (hbin' : BinOnlyWatchesInv F_cur
      { s.core with arena := arL, wvec := wvec', wstk := wstk', wlen := wlen',
                    wusable := wu', num_binary := s.core.num_binary + 1#64 })
    (hQ : ScPost c F0 F_cur s R src dst old_sz at_root Q)
    (hm' : (FullMem c
      { core := { s.core with arena := arL, wvec := wvec', wstk := wstk', wlen := wlen',
                              wusable := wu', num_binary := s.core.num_binary + 1#64 },
        scratch := { s.scratch with wsort := wsort' } } ⋆ R) m') :
    Q (0xFFFFFFFF#64, ()) m' := by
  have hw0 := sc_witness_with_ar (s := s) hlen.core_ok.arena_len_arr hdst_le hw_dst harL
    (fun idx hidx => hout idx (Or.inl (by omega)))
  let k1 : FullCoreState :=
    { s.core with arena := arL, arena_len := dst.toNat, wvec := wvec', wstk := wstk',
                  wlen := wlen', wusable := wu', num_binary := s.core.num_binary + 1#64 }
  have hbin_k1 : BinOnlyWatchesInv F_cur k1 := hbin'.with_core rfl rfl rfl rfl
  have hbin_f : BinOnlyWatchesInv F_cur
      { s.core with arena := arL, wvec := wvec', wstk := wstk', wlen := wlen',
                    wusable := wu', num_binary := s.core.num_binary + 1#64 } :=
    hbin'.with_core rfl rfl rfl rfl
  have hw1 : FullWitnessInv c F0 F_cur k1 :=
    { hw0 with
      arena := sc_arenaInv_with_core hw0.arena rfl rfl rfl
      watches := hbin_k1.toModeWatchesInv }
  exact hQ 0xFFFFFFFF#64 arL s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl
    s.core.trail_pos s.core.trail_end s.core.unassigned s.core.unflushed wvec' wstk' wlen'
    wu' (s.core.num_binary + 1#64) s.core.oom s.scratch.phases wsort' m' hlen' hout
    (fun hf => Bool.noConfusion (har_t.symm.trans hf))
    (fun _ => ⟨hw1, hbin_f.toFull, Nat.le_refl _,
      Or.inr (Or.inr (Or.inr (Or.inl rfl))),
      (fun h => by cases h), (fun h => by cases h), (fun _ => rfl), (fun h => by cases h),
      (fun ⟨_, hle⟩ => by revert hle; simp; omega)⟩) hm'

private theorem sc_core_lengths_with_nb_oom {c : FullCfg} {k : FullCoreState}
    (h : k.LengthsOk c) (nb oom' : BitVec 64) :
    ({ k with num_binary := nb, oom := oom' } : FullCoreState).LengthsOk c := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25⟩

private abbrev scPushCore (k : FullCoreState) (wvec' wstk' : List (BitVec 32))
    (wlen' : Nat) (wu' : BitVec 64) : FullCoreState :=
  { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }

private abbrev scPopCore (k : FullCoreState) (wvec' wstk' : List (BitVec 32))
    (wu' : BitVec 64) : FullCoreState :=
  { k with wvec := wvec', wstk := wstk', wusable := wu' }

private theorem sc_push_bin {F_cur : List (List Nat)} {s : FullState}
    {wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wu' : BitVec 64}
    {lit oth : BitVec 32} {ok : Bool}
    (hbin : BinOnlyWatchesInv F_cur s.core)
    (hlay' : WatchStackLayout (scPushCore s.core wvec' wstk' wlen' wu'))
    (_hlit_lt : lit.toNat < 2 * s.core.cur_vars) (hoth_lt : oth.toNat < 2 * s.core.cur_vars)
    (hcv_bd : 2 * s.core.cur_vars ≤ 2 ^ 30)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, oth.toNat]))
    (hother : ∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore (scPushCore s.core wvec' wstk' wlen' wu') l = fullWatchSize s l ∧
      ∀ j < fullWatchSize s l,
        wstk'[fullWatchOffCore (scPushCore s.core wvec' wstk' wlen' wu') l + j]? =
          s.core.wstk[fullWatchOff s l + j]?)
    (hokt : ok = true →
      lit.toNat < 2 * s.core.cur_vars ∧
      fullWatchSizeCore (scPushCore s.core wvec' wstk' wlen' wu') lit.toNat =
        fullWatchSize s lit.toNat + 1 ∧
      (∀ j < fullWatchSize s lit.toNat,
        wstk'[fullWatchOffCore (scPushCore s.core wvec' wstk' wlen' wu') lit.toNat + j]? =
          s.core.wstk[fullWatchOff s lit.toNat + j]?) ∧
      wstk'[fullWatchOffCore (scPushCore s.core wvec' wstk' wlen' wu') lit.toNat +
          fullWatchSize s lit.toNat]? =
        some ((oth &&& 0x7FFFFFFF#32) ||| 0x80000000#32))
    (hokf : ok = false →
      lit.toNat < 2 * s.core.cur_vars →
      fullWatchSizeCore (scPushCore s.core wvec' wstk' wlen' wu') lit.toNat =
        fullWatchSize s lit.toNat ∧
      ∀ j < fullWatchSize s lit.toNat,
        wstk'[fullWatchOffCore (scPushCore s.core wvec' wstk' wlen' wu') lit.toNat + j]? =
          s.core.wstk[fullWatchOff s lit.toNat + j]?) :
    BinOnlyWatchesInv F_cur (scPushCore s.core wvec' wstk' wlen' wu') := by
  have hp := bv32_bin_watch_props (l := oth) (by omega)
  exact fullWatchPush_preserves_binOnly
    (lit := lit) (w0 := (oth &&& 0x7FFFFFFF#32) ||| 0x80000000#32) (ok := ok)
    hbin hlay' rfl ⟨hp.1, hp.2.1, by rw [hp.2.2]; exact hoth_lt, by rw [hp.2.2]; exact hent⟩
    (fun l hl hne => by
      simpa only [fullWatchSize, fullWatchOff] using hother l hl hne)
    (fun h => let t := hokt h
      ⟨t.1,
        by simpa only [fullWatchSize] using t.2.1,
        fun j hj => by simpa only [fullWatchSize, fullWatchOff] using t.2.2.1 j hj,
        by simpa only [fullWatchSize, fullWatchOff] using t.2.2.2⟩)
    (fun h hl => by
      simpa only [fullWatchSize, fullWatchOff] using hokf h hl)

private theorem sc_push_bin_spec {F_cur : List (List Nat)} {s s' : FullState}
    {wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wu' : BitVec 64}
    {lit oth : BitVec 32} {ok : Bool}
    (hs' : s'.core = scPushCore s.core wvec' wstk' wlen' wu')
    (hbin : BinOnlyWatchesInv F_cur s.core)
    (hlay' : WatchStackLayout (scPushCore s.core wvec' wstk' wlen' wu'))
    (hlit_lt : lit.toNat < 2 * s.core.cur_vars) (hoth_lt : oth.toNat < 2 * s.core.cur_vars)
    (hcv_bd : 2 * s.core.cur_vars ≤ 2 ^ 30)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, oth.toNat]))
    (hother : ∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore (scPushCore s.core wvec' wstk' wlen' wu') l = fullWatchSize s l ∧
      ∀ j < fullWatchSize s l,
        wstk'[fullWatchOffCore (scPushCore s.core wvec' wstk' wlen' wu') l + j]? =
          s.core.wstk[fullWatchOff s l + j]?)
    (hokt : ok = true →
      lit.toNat < 2 * s.core.cur_vars ∧
      ((1 : BitVec 32).toNat = 1 ∨ (1 : BitVec 32).toNat = 2) ∧
      fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat + (1 : BitVec 32).toNat ∧
      (∀ j < fullWatchSize s lit.toNat,
        s'.core.wstk[fullWatchOff s' lit.toNat + j]? = s.core.wstk[fullWatchOff s lit.toNat + j]?) ∧
      s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat]? =
        some ((oth &&& 2147483647) ||| 2147483648) ∧
      ((1 : BitVec 32).toNat = 2 →
        s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat + 1]? = some 0))
    (hokf : ok = false →
      lit.toNat < 2 * s.core.cur_vars →
      fullWatchSizeCore (scPushCore s.core wvec' wstk' wlen' wu') lit.toNat =
        fullWatchSize s lit.toNat ∧
      ∀ j < fullWatchSize s lit.toNat,
        wstk'[fullWatchOffCore (scPushCore s.core wvec' wstk' wlen' wu') lit.toNat + j]? =
          s.core.wstk[fullWatchOff s lit.toNat + j]?) :
    BinOnlyWatchesInv F_cur (scPushCore s.core wvec' wstk' wlen' wu') :=
  sc_push_bin hbin hlay' hlit_lt hoth_lt hcv_bd hent hother
    (fun h => let t := hokt h
      ⟨t.1,
        by simpa only [hs', show (1 : BitVec 32).toNat = 1 from rfl, fullWatchSize] using t.2.2.1,
        fun j hj => by simpa only [hs', fullWatchOff, fullWatchSize] using t.2.2.2.1 j hj,
        by simpa only [hs', fullWatchOff, fullWatchSize,
          show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl,
          show (2147483648 : BitVec 32) = 0x80000000#32 from rfl] using t.2.2.2.2.1⟩)
    hokf

private theorem sc_pop_bin {F_cur : List (List Nat)} {s0 s1 s2 : FullState}
    {wvec3 wstk3 : List (BitVec 32)} {wu3 : BitVec 64} {l0 l1 : BitVec 32}
    (hbin0 : BinOnlyWatchesInv F_cur s0.core) (hbin2 : BinOnlyWatchesInv F_cur s2.core)
    (hlay3 : WatchStackLayout (scPopCore s2.core wvec3 wstk3 wu3))
    (hcv1 : s1.core.cur_vars = s0.core.cur_vars) (hcv2 : s2.core.cur_vars = s1.core.cur_vars)
    (hl0_lt : l0.toNat < 2 * s0.core.cur_vars) (_hl1_lt : l1.toNat < 2 * s1.core.cur_vars)
    (hp0_sz : fullWatchSize s1 l0.toNat = fullWatchSize s0 l0.toNat + 1)
    (hp0_sl : ∀ j < fullWatchSize s0 l0.toNat,
      s1.core.wstk[fullWatchOff s1 l0.toNat + j]? = s0.core.wstk[fullWatchOff s0 l0.toNat + j]?)
    (hok1f_all : l0.toNat = l1.toNat →
      fullWatchSize s2 l1.toNat = fullWatchSize s1 l1.toNat ∧
      ∀ j < fullWatchSize s1 l1.toNat,
        s2.core.wstk[fullWatchOff s2 l1.toNat + j]? = s1.core.wstk[fullWatchOff s1 l1.toNat + j]?)
    (hother2 : ∀ l < 2 * s1.core.cur_vars, l ≠ l1.toNat →
      fullWatchSize s2 l = fullWatchSize s1 l ∧
      ∀ j < fullWatchSize s1 l,
        s2.core.wstk[fullWatchOff s2 l + j]? = s1.core.wstk[fullWatchOff s1 l + j]?)
    (hother3 : ∀ l < 2 * s2.core.cur_vars, l ≠ l0.toNat →
      fullWatchOffCore (scPopCore s2.core wvec3 wstk3 wu3) l = fullWatchOffCore s2.core l ∧
      fullWatchSizeCore (scPopCore s2.core wvec3 wstk3 wu3) l = fullWatchSizeCore s2.core l ∧
      ∀ j < fullWatchSizeCore s2.core l,
        wstk3[fullWatchOffCore (scPopCore s2.core wvec3 wstk3 wu3) l + j]? =
          s2.core.wstk[fullWatchOffCore s2.core l + j]?)
    (_hoff3 : fullWatchOffCore (scPopCore s2.core wvec3 wstk3 wu3) l0.toNat =
      fullWatchOffCore s2.core l0.toNat)
    (hsz3 : fullWatchSizeCore (scPopCore s2.core wvec3 wstk3 wu3) l0.toNat =
      fullWatchSizeCore s2.core l0.toNat - 1)
    (hslice3 : ∀ j < fullWatchSizeCore s2.core l0.toNat - 1,
      wstk3[fullWatchOffCore (scPopCore s2.core wvec3 wstk3 wu3) l0.toNat + j]? =
        s2.core.wstk[fullWatchOffCore s2.core l0.toNat + j]?) :
    BinOnlyWatchesInv F_cur (scPopCore s2.core wvec3 wstk3 wu3) := by
  have hsz_l0 : fullWatchSizeCore s2.core l0.toNat = fullWatchSizeCore s0.core l0.toNat + 1 := by
    by_cases h01 : l0.toNat = l1.toNat
    · have h1 := (hok1f_all h01).1
      dsimp only [fullWatchSize] at h1 hp0_sz; rw [← h01] at h1; rw [h1, hp0_sz]
    · have h1 := (hother2 l0.toNat (by omega) h01).1
      dsimp only [fullWatchSize] at h1 hp0_sz; rw [h1, hp0_sz]
  refine binOnlyWatchesInv_of_pop hbin0 hbin2 hlay3 (hcv2.trans hcv1) (hcv2.trans hcv1) hl0_lt
    ⟨?_, ?_⟩ (fun l hl hne =>
      let ho := hother3 l (by omega) hne
      ⟨ho.2.1, ho.2.2⟩)
  · rw [hsz3, hsz_l0]; omega
  · intro j hj
    have hm3' := hslice3 j (by rw [hsz_l0]; omega)
    have hs12 : s2.core.wstk[fullWatchOffCore s2.core l0.toNat + j]? =
        s1.core.wstk[fullWatchOffCore s1.core l0.toNat + j]? := by
      by_cases h01 : l0.toNat = l1.toNat
      · rw [h01]
        exact (hok1f_all h01).2 j (by
          dsimp only [fullWatchSize] at hp0_sz ⊢; rw [← h01, hp0_sz]; omega)
      · exact (hother2 l0.toNat (by omega) h01).2 j
          (by dsimp only [fullWatchSize] at hp0_sz ⊢; rw [hp0_sz]; omega)
    have hs01 := hp0_sl j (by dsimp only [fullWatchSize]; exact hj)
    dsimp only [fullWatchOff] at hs01
    rw [hm3', hs12, hs01]

/-! ## 2. `full_sweep_copy_wp` -/

private theorem sc_at_root_false_wp (Γ : Env) (a : Tup Val [i64, i64, i64, i32, Ty.bool])
    (m : Mem 64) (Q : Post [i64]) (X : XPost) (c : FullCfg) (F0 : CNF Nat)
    (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop)
    {src dst : BitVec 64} {old_sz : BitVec 32}
    (ha : a = (c.hdr, src, dst, old_sz, false, ()))
    (hlen : s.LengthsOk c) (hds : dst.toNat ≤ src.toNat)
    (hsro : src.toNat + 3 + old_sz.toNat ≤ s.core.arena_len)
    (hm : (FullMem c s ⋆ R) m) (hQ : ScPost c F0 F_cur s R src dst old_sz false Q) :
    Func.wp Γ full_sweep_copy_body a m Q X := by
  subst ha
  have hdb : dimacsBound = 2 ^ 28 := rfl
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have har_cap := c.harena
  have hzext32 : ∀ x : BitVec 32, (x.setWidth 64).toNat = x.toNat :=
    fun x => zext_toNat x (by decide)
  have h3_64 : (3 : BitVec 64).toNat = 3 := rfl
  unfold Func.wp full_sweep_copy_body
  c0_hsteps_nogrp; c0_hsplit
  refine wp_loop_inv (ts := [i32])
      (fun ⟨i, ⟨⟩⟩ mL => i.toNat ≤ old_sz.toNat ∧
        ∃ arL : List (BitVec 32), arL.length = c.arena_cap ∧
          OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + i.toNat) s.core.arena arL ∧
          (∀ j < i.toNat, arL[dst.toNat + 3 + j]? = s.core.arena[src.toNat + 3 + j]?) ∧
          (FullMem c (scArState s arL) ⋆ R) mL)
      (fun ⟨i, ⟨⟩⟩ _ => old_sz.toNat - i.toNat) (fun JL hLoop => ?_) ?_
  · c0_hsteps
    exact hLoop ⟨0#32, ⟨⟩⟩ m ⟨Nat.zero_le _, s.core.arena, har_len, fun _ _ => rfl,
      fun _ hj => absurd hj (Nat.not_lt_zero _), hm⟩
  · rintro JL ⟨i, ⟨⟩⟩ mL ⟨hi_le, arL, harL, hout, hcp, hmL⟩ hLoop
    c0_hsplit
    · have hi_lt : i.toNat < old_sz.toNat := hc
      have hs_mod1 : (src.toNat + 3) % 2 ^ 64 = src.toNat + 3 := Nat.mod_eq_of_lt (by omega)
      have hs_mod2 : (src.toNat + 3 + i.toNat) % 2 ^ 64 = src.toNat + 3 + i.toNat :=
        Nat.mod_eq_of_lt (by omega)
      have hd_mod1 : (dst.toNat + 3) % 2 ^ 64 = dst.toNat + 3 := Nat.mod_eq_of_lt (by omega)
      have hd_mod2 : (dst.toNat + 3 + i.toNat) % 2 ^ 64 = dst.toNat + 3 + i.toNat :=
        Nat.mod_eq_of_lt (by omega)
      have hs_idx : (src + 3 + i.setWidth 64).toNat = src.toNat + 3 + i.toNat := by
        simp only [BitVec.toNat_add, h3_64, hzext32, hs_mod1, hs_mod2]
      have hd_idx : (dst + 3 + i.setWidth 64).toNat = dst.toNat + 3 + i.toNat := by
        simp only [BitVec.toNat_add, h3_64, hzext32, hd_mod1, hd_mod2]
      have hs_ar : (src + 3 + i.setWidth 64).toNat < arL.length := by rw [hs_idx]; omega
      have hd_ar : (dst + 3 + i.setWidth 64).toNat < arL.length := by rw [hd_idx]; omega
      have hi1_eq : (i + 1#32).toNat = i.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      have hs_ag : arL[(src + 3 + i.setWidth 64).toNat]'hs_ar =
          s.core.arena[src.toNat + 3 + i.toNat]'(by omega) := by
        have h1 := hout (src.toNat + 3 + i.toNat) (Or.inr (by omega))
        rw [List.getElem?_eq_getElem (by omega : src.toNat + 3 + i.toNat < s.core.arena.length),
          List.getElem?_eq_getElem (by omega : src.toNat + 3 + i.toNat < arL.length)] at h1
        simp only [hs_idx]; exact Option.some.inj h1
      c0_hsteps
      let ar' := arL.set (dst + 3 + i.setWidth 64).toNat
        (arL[(src + 3 + i.setWidth 64).toNat]'hs_ar)
      refine hLoop ⟨i + 1#32, ⟨⟩⟩ _ (by simp [hi1_eq]; omega)
        ⟨by omega, ar', by rw [List.length_set, harL], fun k hk => ?_, fun j hj => ?_,
          by assumption⟩
      · dsimp only [ar']
        by_cases hke : k = (dst + 3 + i.setWidth 64).toNat
        · rw [hd_idx] at hke; rw [hi1_eq] at hk; omega
        · rw [List.getElem?_set_ne (Ne.symm hke)]
          exact hout k (by rw [hd_idx] at hke; rw [hi1_eq] at hk; omega)
      · dsimp only [ar']
        rw [hi1_eq] at hj
        by_cases hji : j = i.toNat
        · subst hji
          rw [hd_idx, List.getElem?_set_self (by omega),
            List.getElem?_eq_getElem (by omega : src.toNat + 3 + i.toNat < s.core.arena.length)]
          exact congrArg some hs_ag
        · rw [List.getElem?_set_ne (by rw [hd_idx]; omega)]
          exact hcp j (by omega)
    · have hi_eq : i.toNat = old_sz.toNat := by have := hc; omega
      rw [hi_eq] at hout hcp
      c0_hsteps
      exact hQ (old_sz.setWidth 64) arL s.core.vals s.core.flags s.core.lvl s.core.rsns
        s.core.trl s.core.trail_pos s.core.trail_end s.core.unassigned s.core.unflushed
        s.core.wvec s.core.wstk s.core.wlen s.core.wusable s.core.num_binary s.core.oom
        s.scratch.phases s.scratch.wsort _
        ⟨{ hlen.core_ok with arena_len_arr := harL }, hlen.scratch_ok⟩ hout
        (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, hcp⟩)
        (fun ht => by cases ht) (by assumption)

theorem full_sweep_copy_wp (Γ : Env)
    (hAssign : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hPop : ∀ a m Q X, fullWatchPopC0Spec a m Q X →
      Γ "full_watch_pop_c0" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, Proof.Spec.fullSweepCopySpec a m Q X →
      Func.wp Γ full_sweep_copy_body a m Q X := by
  intro a m Q X hPre
  rcases a with ⟨hdr, src, dst, old_sz, at_root, ⟨⟩⟩
  rcases hPre with
    ⟨c, F0, F_cur, s, R, rfl, hlen, hds, hsz3, hsro, hat, hlits0, hroot, hm, hQ⟩
  by_cases har_t : at_root = true
  · subst har_t
    have hdb : dimacsBound = 2 ^ 28 := rfl
    have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
    have har_cap := c.harena; have hcv_le := hlen.core_ok.cur_vars_le; have hmax := c.hmaxv
    have hv_len := hlen.core_ok.vals_len; have hfl_len := hlen.core_ok.flags_len
    have hl_len := hlen.core_ok.lvl_len
    have hdst_le : dst.toNat ≤ c.arena_cap := by omega
    have hsz_lt : old_sz.toNat < 2 * 2 ^ 28 := by omega
    have hzext32 : ∀ x : BitVec 32, (x.setWidth 64).toNat = x.toNat :=
      fun x => zext_toNat x (by decide)
    have h3_64 : (3 : BitVec 64).toNat = 3 := rfl
    have h4_64 : (4 : BitVec 64).toNat = 4 := rfl
    obtain ⟨hw_dst, hbin0, horig⟩ := hroot rfl
    have hcl0 : s.core.cur_level = 0 := decide_eq_true_eq.mp hat.symm
    have hsrc_lt : src.toNat < s.core.arena.length := by omega
    unfold Func.wp full_sweep_copy_body
    c0_hsteps_nogrp; c0_hsplit
    · c0_hsteps_nogrp
      refine wp_loop_inv (ScLoopInv c s R src dst old_sz)
        (fun (_, i, ()) _ => old_sz.toNat - i.toNat) (fun JL hLoop => ?_) ?_
      · c0_hsteps
        exact hLoop (0#32, 0#32, ()) m ⟨Nat.zero_le _, Nat.zero_le _, s.core.arena, har_len,
          fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _), List.nil_sublist _,
          fun _ h => by simp at h, fun _ _ h => absurd h (Nat.not_lt_zero _), hm⟩
      · rintro JL ⟨new_sz, i, ⟨⟩⟩ mL
          ⟨hnz_i, hi_le, arL, harL, hout, hlits, hsub, hdrop, hnozr, hmL⟩ hLoop
        c0_hsplit
        · have hi_lt : i.toNat < old_sz.toNat := hc
          have hs_mod1 : (src.toNat + 3) % 2 ^ 64 = src.toNat + 3 := Nat.mod_eq_of_lt (by omega)
          have hs_mod2 : (src.toNat + 3 + i.toNat) % 2 ^ 64 = src.toNat + 3 + i.toNat :=
            Nat.mod_eq_of_lt (by omega)
          have hs_idx : (src + 3 + i.setWidth 64).toNat = src.toNat + 3 + i.toNat := by
            simp only [BitVec.toNat_add, h3_64, hzext32, hs_mod1, hs_mod2]
          have hs_ar : (src + 3 + i.setWidth 64).toNat < arL.length := by rw [hs_idx]; omega
          have hs_ag : arL[src.toNat + 3 + i.toNat]? = s.core.arena[src.toNat + 3 + i.toNat]? :=
            hout (src.toNat + 3 + i.toNat) (Or.inr (by omega))
          have hs_orig_lt : src.toNat + 3 + i.toNat < s.core.arena.length := by omega
          let lit := s.core.arena[src.toNat + 3 + i.toNat]'hs_orig_lt
          have hlit_eq_ar : arL[src.toNat + 3 + i.toNat]'(by omega) = lit := by
            have h1 := hs_ag; rw [List.getElem?_eq_getElem hs_orig_lt,
              List.getElem?_eq_getElem (by omega : src.toNat + 3 + i.toNat < arL.length)] at h1
            exact Option.some.inj h1
          have hlit_ar_c0 : arL[(src + 3 + i.setWidth 64).toNat]'hs_ar = lit := by
            simp only [hs_idx]; exact hlit_eq_ar
          have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by
            have h := hlits0 i.toNat hi_lt
            rwa [List.getElem?_eq_getElem hs_orig_lt, Option.getD_some] at h
          have hv_zext : ((lit >>> 1#32).setWidth 64).toNat = lit.toNat / 2 := by
            rw [hzext32, bv32_shr1_toNat lit]
          have hfl_lt' : (((arL[(src + 3 + i.setWidth 64).toNat]'hs_ar >>>
              (1 : BitVec 32)).setWidth 64).toNat) < s.core.flags.length := by
            rw [hlit_ar_c0, hzext32, bv32_shr1_ofNat lit]; omega
          have hl_lt' : (((arL[(src + 3 + i.setWidth 64).toNat]'hs_ar >>>
              (1 : BitVec 32)).setWidth 64).toNat) < s.core.lvl.length := by
            rw [hlit_ar_c0, hzext32, bv32_shr1_ofNat lit]; omega
          have hv_v : ((arL[(src + 3 + i.setWidth 64).toNat]'hs_ar).setWidth 64).toNat <
              s.core.vals.length := by
            rw [hlit_ar_c0, hzext32]; omega
          have hlit_mod_c0 : arL[(src.toNat + 3 + i.toNat) % 2 ^ 64]'(by rw [hs_mod2]; omega) =
              lit := by
            simp only [hs_mod2]; exact hlit_eq_ar
          c0_hsteps_nogrp
          refine wp_join_group (ts := [])
            (fun () m26 => m26 = mL ∧ ScNoZredPrefix s src (i.toNat + 1)) ?_ ?_
          · rintro _ ⟨⟩ m26 ⟨hm26, hnozr'⟩; subst m26; c0_hsteps_nogrp
            refine wp_join_group (ts := [i32]) (ScJoinInv c s R src dst i) ?_ ?_
            · rintro _ ⟨new_sz', ⟨⟩⟩ m27 hJ27
              have hi1_eq : (i + 1#32).toNat = i.toNat + 1 := by
                rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt (by omega)]
              c0_hsteps
              exact hLoop (new_sz', i + 1#32, ()) m27 (by simp [hi1_eq]; omega)
                ⟨by rw [hi1_eq]; exact hJ27.1, by rw [hi1_eq]; omega, by rw [hi1_eq]; exact hJ27.2⟩
            · intro J27 hJ27
              refine wp_join_group (ts := []) (fun () m28 => m28 = mL) ?_ ?_
              · rintro _ ⟨⟩ m28 hm28; subst m28
                have hnd_mod1 : (dst.toNat + 3) % 2 ^ 64 = dst.toNat + 3 :=
                  Nat.mod_eq_of_lt (by omega)
                have hnd_mod2 : (dst.toNat + 3 + new_sz.toNat) % 2 ^ 64 =
                    dst.toNat + 3 + new_sz.toNat := Nat.mod_eq_of_lt (by omega)
                have hnd_idx : (dst + 3 + new_sz.setWidth 64).toNat =
                    dst.toNat + 3 + new_sz.toNat := by
                  simp only [BitVec.toNat_add, h3_64, hzext32, hnd_mod1, hnd_mod2]
                have hnd_lt : (dst + 3 + new_sz.setWidth 64).toNat < arL.length := by
                  rw [hnd_idx]; omega
                c0_hsteps
                exact hJ27 (new_sz + 1#32, ()) _ (sc_step_keep (lit := lit) hlen hsro hds hi_lt
                  hnz_i harL hout hlits hsub hdrop hnozr' (List.getElem?_eq_getElem hs_orig_lt)
                  hlit_lt (by rw [← hnd_idx, ← hlit_ar_c0]; assumption))
              · intro J28 hJ28
                c0_hsteps_nogrp; c0_hsplit
                · c0_hsteps
                  exact sc_ret_sat hlen hdst_le hsz_lt rfl hw_dst hbin0 hQ harL
                    (fun k hk => hout k
                      (by rcases hk with h | h; exact Or.inl h; exact Or.inr (by omega)))
                    hmL
                · rename_i hc_cv hc_lv hc_nz
                  have hv_lt : lit.toNat / 2 < s.core.cur_vars := by
                    rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc_cv
                    simpa only [h3_64, hs_mod2, hlit_eq_ar] using hc_cv
                  have hlvl0 : (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = 0 := by
                    have h1 := congrArg BitVec.toNat hc_lv
                    rw [List.getElem?_eq_getElem (by omega : lit.toNat / 2 < s.core.lvl.length),
                      Option.getD_some]
                    simpa only [h3_64, hs_mod2, hlit_eq_ar,
                      show (0 : BitVec 32).toNat = 0 from rfl] using h1
                  have hget_l : s.core.vals[lit.toNat]?.getD 0#8 =
                      s.core.vals[lit.toNat]'(by omega) := by
                    rw [List.getElem?_eq_getElem (by omega : lit.toNat < s.core.vals.length),
                      Option.getD_some]
                  have hdom' : s.core.vals[lit.toNat]'(by omega) = 0#8 ∨
                      s.core.vals[lit.toNat]'(by omega) = 1#8 ∨
                      s.core.vals[lit.toNat]'(by omega) = 0xFF#8 := by
                    have h := hw_dst.vals_domain lit.toNat hlit_lt; rwa [hget_l] at h
                  have hff : s.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8 := by
                    have h1 : s.core.vals[lit.toNat]'(by omega) ≠ 0#8 := fun he => by
                      apply hc_nz
                      simpa only [h3_64, hs_mod2, hlit_eq_ar, he] using
                        (by decide : BitVec.signExtend 32 0#8 = BitVec.ofNat 32 0)
                    have h2 : s.core.vals[lit.toNat]'(by omega) ≠ 1#8 := fun he => by
                      have hgt' : (BitVec.ofNat 32 0).slt
                          (BitVec.signExtend 32 (s.core.vals[lit.toNat]'(by omega))) = false := by
                        simpa only [h3_64, hs_mod2, hlit_eq_ar] using hc
                      rw [he] at hgt'
                      exact Bool.noConfusion
                        (hgt'.symm.trans (by decide : (BitVec.ofNat 32 0).slt
                          (BitVec.signExtend 32 1#8) = true))
                    rw [hget_l]
                    rcases hdom' with h0 | h1' | hff'
                    · exact absurd h0 h1
                    · exact absurd h1' h2
                    · exact hff'
                  have hlit_d : s.core.arena[src.toNat + 3 + i.toNat]?.getD 0#32 = lit := by
                    rw [List.getElem?_eq_getElem hs_orig_lt, Option.getD_some]
                  c0_hsteps
                  exact hJ27 (new_sz, ()) mL (sc_step_drop hlen hsro hi_lt hnz_i harL hout
                    hlits hsub hdrop hnozr' (hlit_d.symm ▸ hlit_lt) (hlit_d.symm ▸ hlvl0)
                    (hlit_d.symm ▸ hff) hmL)
                · c0_hsteps; exact hJ28 () mL rfl
                · c0_hsteps; exact hJ28 () mL rfl
                · c0_hsteps; exact hJ28 () mL rfl
          · intro J26 hJ26
            have hnozr_triv :
                (lit.toNat / 2 < s.core.cur_vars →
                  (s.core.arena[src.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 →
                  (s.core.flags[lit.toNat / 2]?.getD 0#32 &&& 1#32) ≠ 0#32) →
                ScNoZredPrefix s src (i.toNat + 1) := fun hok hred j hj => by
              by_cases hji : j = i.toNat
              · subst hji
                have hlit_d : (s.core.arena[src.toNat + 3 + i.toNat]?.getD 0#32).toNat =
                    lit.toNat := by
                  rw [List.getElem?_eq_getElem hs_orig_lt, Option.getD_some]
                rw [hlit_d]; exact fun hv => hok hv hred
              · exact hnozr hred j (by omega)
            c0_hsplit
            · c0_hsplit
              · c0_hsteps_nogrp; c0_hsplit
                · c0_hsteps
                  exact sc_ret_sat hlen hdst_le hsz_lt rfl hw_dst hbin0 hQ harL
                    (fun k hk => hout k
                      (by rcases hk with h | h; exact Or.inl h; exact Or.inr (by omega)))
                    hmL
                · c0_hsteps
                  refine hJ26 () mL ⟨rfl, hnozr_triv fun _ _ h0 => by
                    apply hc
                    simpa only [h3_64, hs_mod2, hlit_eq_ar,
                      show (1#32 : BitVec 32) = 1 from rfl,
                      show (0#32 : BitVec 32) = 0 from rfl,
                      List.getElem?_eq_getElem (by omega : lit.toNat / 2 < s.core.flags.length),
                      Option.getD_some] using h0⟩
              · c0_hsteps
                refine hJ26 () mL ⟨rfl, hnozr_triv fun _ hred => by
                  exact absurd hred (by simpa [List.getElem?_eq_getElem hsrc_lt,
                    Option.getD_some] using hc)⟩
            · c0_hsteps
              refine hJ26 () mL ⟨rfl, hnozr_triv fun hv _ => False.elim (by
                simp only [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64), h3_64,
                  hs_mod2, hlit_eq_ar] at hc
                exact hc hv)⟩
        · have hi_eq : i.toNat = old_sz.toNat := by have := hc; omega
          rw [hi_eq] at hnz_i hsub hdrop
          have hout_old : OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + old_sz.toNat)
              s.core.arena arL := fun k hk =>
            hout k (by rcases hk with h | h; exact Or.inl h; exact Or.inr (by omega))
          c0_hsplit
          · have hnz0 : new_sz.toNat = 0 := by have := congrArg BitVec.toNat hc; exact this
            rw [hnz0] at hsub hdrop
            have hnil : (cnfOfClauses F_cur).EntailsClause (cnfClause []) :=
              level0_entails_of_filter hw_dst horig (by simpa using hdrop)
            c0_hsteps
            exact sc_ret_unsat hlen hdst_le hsz_lt rfl hw_dst hbin0 hQ harL hout_old
              (level0_unsat_of_entails_nil hw_dst hnil) hmL
          · have hnz_ne0 : new_sz ≠ 0#32 := hc
            c0_hsplit
            · have hnz1 : new_sz.toNat = 1 := by have := congrArg BitVec.toNat hc; exact this
              have hd_mod : (dst.toNat + 3) % 2 ^ 64 = dst.toNat + 3 := Nat.mod_eq_of_lt (by omega)
              have hd_idx : (dst + 3).toNat = dst.toNat + 3 := by
                simp only [BitVec.toNat_add, h3_64, hd_mod]
              have hd_lt : (dst + 3).toNat < arL.length := by rw [hd_idx]; omega
              let u := arL[dst.toNat + 3]'(by omega)
              have hu_c0 : arL[(dst + 3).toNat]'hd_lt = u := by simp only [hd_idx]; rfl
              have hu_lt : u.toNat < 2 * s.core.cur_vars := by
                have h := hlits 0 (by omega)
                rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
              have hu_v : ((arL[(dst + 3).toNat]'hd_lt).setWidth 64).toNat <
                  s.core.vals.length := by
                rw [hu_c0, hzext32]; omega
              have hget_u : s.core.vals[u.toNat]?.getD 0#8 = s.core.vals[u.toNat]'(by omega) := by
                rw [List.getElem?_eq_getElem (by omega : u.toNat < s.core.vals.length),
                  Option.getD_some]
              have hdom' : s.core.vals[u.toNat]'(by omega) = 0#8 ∨
                  s.core.vals[u.toNat]'(by omega) = 1#8 ∨
                  s.core.vals[u.toNat]'(by omega) = 0xFF#8 := by
                have h := hw_dst.vals_domain u.toNat hu_lt; rwa [hget_u] at h
              have hent_u : (cnfOfClauses F_cur).EntailsClause (cnfClause [u.toNat]) := by
                have h1 := level0_entails_of_filter hw_dst horig hdrop
                have htake1 : (arL.drop (dst.toNat + 3)).take new_sz.toNat = [u] := by
                  rw [hnz1]
                  refine List.ext_getElem (by simp; omega) fun j hj _ => ?_
                  have hj1 : j < 1 := by simp only [List.length_take] at hj; omega
                  have : j = 0 := by omega
                  subst this; simp [u]
                rwa [htake1, List.map_singleton] at h1
              c0_hsteps_nogrp; c0_hsplit
              · have hff : s.core.vals[u.toNat]?.getD 0#8 = 0xFF#8 := by
                  have hlt0 : BitVec.slt (BitVec.signExtend 32 (s.core.vals[u.toNat]'(by omega)))
                      (BitVec.signExtend 32 (BitVec.truncate 8 0#32)) = true := by
                    simpa only [h3_64, hd_mod, hzext32, u,
                      show BitVec.truncate 8 0#32 = 0#8 from rfl,
                      show BitVec.signExtend 32 0#8 = BitVec.ofNat 32 0 from rfl] using hc
                  rw [hget_u]; exact (bv8_domain_sext_lt0 hdom').mp hlt0
                c0_hsteps
                exact sc_ret_unsat hlen hdst_le hsz_lt rfl hw_dst hbin0 hQ harL hout_old
                  (level0_unsat_of_unit_false hw_dst hcl0 hu_lt hent_u hff) hmL
              · have hun : s.core.vals[u.toNat]?.getD 0#8 = 0#8 := by
                  have heq0 : BitVec.signExtend 32 (s.core.vals[u.toNat]'(by omega)) =
                      BitVec.signExtend 32 (BitVec.truncate 8 0#32) := by
                    simpa only [h3_64, hd_mod, hzext32, u,
                      show BitVec.truncate 8 0#32 = 0#8 from rfl,
                      show BitVec.signExtend 32 0#8 = BitVec.ofNat 32 0 from rfl] using hc
                  rw [hget_u]; exact (bv8_domain_sext_eq0 hdom').mp heq0
                c0_hsteps; c0_call hAssign
                refine ⟨c, scArState s arL, R, rfl,
                  ⟨{ hlen.core_ok with arena_len_arr := harL }, hlen.scratch_ok⟩, hmL, ?_⟩
                have hnot_out : ¬ (s.core.cur_vars ≤ u.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
                    s.core.vals[u.toNat]?.getD 0#8 ≠ 0#8) := by
                  have hte_u : s.core.trail_end < s.core.cur_vars :=
                    hw_dst.trail_end_lt_of_unassigned hu_lt hun
                  rw [not_or, not_or]; refine ⟨by omega, by omega, fun h => h hun⟩
                rw [hu_c0, ite_eq_right hnot_out]
                intro _v _rsn' _unfl' flags' unass' phases' m' hf' hp' _s1 hm'
                c0_hsteps
                exact sc_ret_new1 hlen hdst_le hsz_lt rfl hcl0 hw_dst hbin0 harL hout_old
                  hu_lt hun hent_u hf' hp' hQ (by
                    dsimp only [_v, _rsn', _unfl', _s1, scNew1State, scArState] at hm' ⊢
                    simpa only [show (0 : BitVec 32) = 0#32 from rfl,
                      show (4294967295 : BitVec 32) = 4294967295#32 from rfl,
                      ↓reduceIte] using hm')
              · c0_hsteps
                exact sc_ret_sat hlen hdst_le hsz_lt rfl hw_dst hbin0 hQ harL hout_old hmL
            · have hnz_ne1 : new_sz ≠ 1#32 := hc
              c0_hsplit
              · have hnz2 : new_sz.toNat = 2 := by have := congrArg BitVec.toNat hc; exact this
                have hd0_mod : (dst.toNat + 3) % 2 ^ 64 = dst.toNat + 3 :=
                  Nat.mod_eq_of_lt (by omega)
                have hd1_mod : (dst.toNat + 4) % 2 ^ 64 = dst.toNat + 4 :=
                  Nat.mod_eq_of_lt (by omega)
                have hd0_idx : (dst + 3).toNat = dst.toNat + 3 := by
                  simp only [BitVec.toNat_add, h3_64, hd0_mod]
                have hd1_idx : (dst + 4).toNat = dst.toNat + 4 := by
                  simp only [BitVec.toNat_add, h4_64, hd1_mod]
                have hd0_lt : (dst + 3).toNat < arL.length := by rw [hd0_idx]; omega
                have hd1_lt : (dst + 4).toNat < arL.length := by rw [hd1_idx]; omega
                let l0 := arL[dst.toNat + 3]'(by omega)
                let l1 := arL[dst.toNat + 4]'(by omega)
                have hl0_c0 : arL[(dst + 3).toNat]'hd0_lt = l0 := by simp only [hd0_idx]; rfl
                have hl1_c0 : arL[(dst + 4).toNat]'hd1_lt = l1 := by simp only [hd1_idx]; rfl
                have hl0_lt : l0.toNat < 2 * s.core.cur_vars := by
                  have h := hlits 0 (by omega)
                  rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
                have hl1_lt : l1.toNat < 2 * s.core.cur_vars := by
                  have h := hlits 1 (by omega)
                  rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
                have hent_01 : (cnfOfClauses F_cur).EntailsClause
                    (cnfClause [l0.toNat, l1.toNat]) := by
                  have h1 := level0_entails_of_filter hw_dst horig hdrop
                  have htake2 : (arL.drop (dst.toNat + 3)).take new_sz.toNat = [l0, l1] := by
                    rw [hnz2]
                    refine List.ext_getElem (by simp; omega) fun j hj _ => ?_
                    have hj2 : j < 2 := by simp only [List.length_take] at hj; omega
                    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp [l0, l1]
                  rwa [htake2, List.map_cons, List.map_singleton] at h1
                have hent_10 : (cnfOfClauses F_cur).EntailsClause
                    (cnfClause [l1.toNat, l0.toNat]) := entails_swap2 hent_01
                have hw0_props := bv32_bin_watch_props (l := l1) (by omega)
                have hw1_props := bv32_bin_watch_props (l := l0) (by omega)
                have hbin0_ar : BinOnlyWatchesInv F_cur (scArState s arL).core :=
                  (FullBinOnlyWatchesInv.toBinOnly hbin0).with_core rfl rfl rfl rfl
                let s0 : FullState := scArState s arL
                have hcv_bd0 : 2 * s0.core.cur_vars ≤ 2 ^ 30 := by dsimp only [s0]; omega
                have hlen0 : s0.LengthsOk c :=
                  ⟨{ hlen.core_ok with arena_len_arr := harL }, hlen.scratch_ok⟩
                c0_hsteps; c0_call hPush
                refine ⟨c, s0, R, rfl, hlen0, hbin0_ar.layout,
                  fun _ => by rw [hl1_c0]; exact hw0_props.2.1,
                  fun h2 => absurd h2 (by decide), hmL, ?_⟩
                intro ok0 wvec1 wstk1 wlen1 wu1 wsort1 m1 _s1 hlen1 hlay1 hother1 hok0t hok0f hm1
                let s1 : FullState := _s1
                have hbin1 : BinOnlyWatchesInv F_cur
                    (scPushCore s0.core wvec1 wstk1 wlen1 wu1) := by
                  rw [hl0_c0] at hother1 hok0t hok0f
                  rw [hl1_c0] at hok0t
                  exact sc_push_bin_spec (s' := _s1) rfl hbin0_ar hlay1 hl0_lt hl1_lt hcv_bd0
                    hent_01 hother1 hok0t (fun hf hl => (hok0f hf).1 hl)
                c0_hsteps_nogrp; c0_hsplit
                · have hok0 : ok0 = true := hc
                  c0_hsteps; c0_call hPush
                  refine ⟨c, s1, R, rfl, hlen1, hlay1,
                    fun _ => by rw [hl0_c0]; exact hw1_props.2.1,
                    fun h2 => absurd h2 (by decide), hm1, ?_⟩
                  intro ok1 wvec2 wstk2 wlen2 wu2 wsort2 m2 _s2 hlen2 hlay2 hother2 hok1t hok1f hm2
                  let s2 : FullState := _s2
                  have hbin2 : BinOnlyWatchesInv F_cur
                      (scPushCore s1.core wvec2 wstk2 wlen2 wu2) := by
                    rw [hl1_c0] at hother2 hok1t hok1f
                    rw [hl0_c0] at hok1t
                    exact sc_push_bin_spec (s' := _s2) rfl hbin1 hlay2 hl1_lt
                      (by dsimp only [s1]; exact hl0_lt) hcv_bd0 hent_10 hother2 hok1t
                      (fun hf hl => (hok1f hf).1 hl)
                  c0_hsteps_nogrp; c0_hsplit
                  · c0_hsteps
                    let k2' : FullCoreState :=
                      { s.core with arena := arL, wvec := wvec2, wstk := wstk2, wlen := wlen2,
                                    wusable := wu2, num_binary := s.core.num_binary + 1#64 }
                    have hbin2' : BinOnlyWatchesInv F_cur k2' := hbin2.with_core rfl rfl rfl rfl
                    have hlen2' : ({ core := k2',
                                     scratch := { s.scratch with wsort := wsort2 } } :
                        FullState).LengthsOk c :=
                      ⟨sc_core_lengths_with_nb_oom hlen2.core_ok (s.core.num_binary + 1#64)
                         s.core.oom, hlen2.scratch_ok⟩
                    exact sc_ret_new2_ok hlen hdst_le hsz_lt rfl hw_dst harL hout_old hlen2'
                      hbin2' hQ (by assumption)
                  · have hok1f' : ok1 = false := hc
                    have hp0 := hok0t hok0
                    rw [hl0_c0] at hp0
                    have hok1f_all := (hok1f hok1f').1
                    rw [hl1_c0] at hok1f_all
                    have hsz_l0 : fullWatchSizeCore s2.core l0.toNat =
                        fullWatchSizeCore s0.core l0.toNat + 1 := by
                      by_cases h01 : l0.toNat = l1.toNat
                      · have h1 := (hok1f_all (by dsimp only [s1] at hl1_lt ⊢; exact hl1_lt)).1
                        dsimp only [fullWatchSize] at h1; rw [← h01] at h1
                        have hp0s := hp0.2.2.1; dsimp only [fullWatchSize] at hp0s
                        simpa only [show (1 : BitVec 32).toNat = 1 from rfl] using h1.trans hp0s
                      · have h1 := (hother2 l0.toNat (by dsimp only [s1]; exact hl0_lt)
                            (by rw [hl1_c0]; exact h01)).1
                        dsimp only [fullWatchSize] at h1
                        have hp0s := hp0.2.2.1; dsimp only [fullWatchSize] at hp0s
                        simpa only [show (1 : BitVec 32).toNat = 1 from rfl] using h1.trans hp0s
                    have hsz_l0_ge1 : 1 ≤ fullWatchSize s2 l0.toNat := by
                      dsimp only [fullWatchSize]; rw [hsz_l0]; omega
                    c0_hsteps; c0_call hPop
                    refine ⟨c, s2, R, rfl, hlen2, hlay2,
                      by rw [hl0_c0]; dsimp only [s2, s1, s0]; exact hl0_lt, by decide,
                      by rw [hl0_c0]; exact hsz_l0_ge1, hm2, ?_⟩
                    intro wvec3 wstk3 wu3 m3 _s3 hlen3 hlay3 hother3 hoff3 hsz3' hslice3 hm3
                    rw [hl0_c0] at hother3 hoff3 hsz3' hslice3
                    have hbin3 : BinOnlyWatchesInv F_cur
                        (scPopCore s2.core wvec3 wstk3 wu3) :=
                      sc_pop_bin (s1 := s1) (s2 := s2) hbin0_ar hbin2 hlay3 rfl rfl
                        hl0_lt (by dsimp only [s1]; exact hl1_lt)
                        (by simpa only [show (1 : BitVec 32).toNat = 1 from rfl] using hp0.2.2.1)
                        hp0.2.2.2.1
                        (fun _ => hok1f_all (by dsimp only [s1]; exact hl1_lt))
                        (fun l hl hne => hother2 l hl (by rw [hl1_c0]; exact hne))
                        hother3 hoff3
                        (by simpa only [show (1 : BitVec 32).toNat = 1 from rfl] using hsz3')
                        (by simpa only [show (1 : BitVec 32).toNat = 1 from rfl] using hslice3)
                    c0_hsteps
                    let k3' : FullCoreState :=
                      { s.core with arena := arL, wvec := wvec3, wstk := wstk3, wlen := wlen2,
                                    wusable := wu3, oom := 1#64 }
                    have hlen3' : ({ core := k3',
                                     scratch := { s.scratch with wsort := wsort2 } } :
                        FullState).LengthsOk c :=
                      ⟨sc_core_lengths_with_nb_oom hlen3.core_ok s.core.num_binary 1#64,
                        hlen3.scratch_ok⟩
                    exact sc_ret_oom hlen hdst_le hsz_lt rfl hw_dst harL hout_old hlen3'
                      (hbin3.with_core rfl rfl rfl rfl) hQ (by assumption)
                · c0_hsteps
                  let k1' : FullCoreState :=
                    { s.core with arena := arL, wvec := wvec1, wstk := wstk1, wlen := wlen1,
                                  wusable := wu1, oom := 1#64 }
                  have hlen1' : ({ core := k1',
                                   scratch := { s.scratch with wsort := wsort1 } } :
                      FullState).LengthsOk c :=
                    ⟨sc_core_lengths_with_nb_oom hlen1.core_ok s.core.num_binary 1#64,
                      hlen1.scratch_ok⟩
                  exact sc_ret_oom hlen hdst_le hsz_lt rfl hw_dst harL hout_old hlen1'
                    (hbin1.with_core rfl rfl rfl rfl) hQ (by assumption)
              · have h3 : 3 ≤ new_sz.toNat := by
                  have hn0 : new_sz.toNat ≠ 0 := fun e => hnz_ne0 (BitVec.eq_of_toNat_eq e)
                  have hn1 : new_sz.toNat ≠ 1 := fun e => hnz_ne1 (BitVec.eq_of_toNat_eq e)
                  have hn2 : new_sz.toNat ≠ 2 := fun e => hc (BitVec.eq_of_toNat_eq e)
                  omega
                c0_hsteps
                exact sc_ret_keep hlen hdst_le hsz_lt rfl h3 hnz_i hw_dst hbin0 horig hQ harL
                  hout_old hlits hsub hdrop hmL
    · exact Bool.noConfusion hc
  · have hat_f : at_root = false := Bool.eq_false_iff.mpr har_t
    subst hat_f
    exact sc_at_root_false_wp Γ (c.hdr, src, dst, old_sz, false, ()) m Q X c F0 F_cur s R
      rfl hlen hds hsro hm hQ

end

end LeanQbe.T.Examples.Kissat.Proof.Collect
