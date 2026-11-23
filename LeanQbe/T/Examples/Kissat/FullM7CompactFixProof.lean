module

public import LeanQbe.T.Examples.Kissat.FullM7CompactFix
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullM4CompactLemmas
public import LeanQbe.T.Examples.Kissat.FullM4CompactProof
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
public import LeanQbe.T.Examples.Kissat.FullReduceLemmas3
public import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.C0Agrees

/-!
# Kissat `D-Full` M7 Purely Additive Compaction Fix Proofs (`FullM7CompactFixProof`)

M1-clean UNSAT-only proofs (`public section`, `0 @[expose]`, `0 import all`):
1. `full_compact_needed_m7fix_exact_wp` + `full_compact_needed_m7fix_wp` (canonical
   `FullM4Compact.fullCompactNeededSpec`), proving exact `1%` trigger parity (`dead * 100 > cv`,
   `128 ≤ cur_vars`, `cur_level = 0`, `dense_mode = 0`).
2. `full_compact_mark_live_m7fix_no_zombie_wp` + `full_compact_mark_live_m7fix_wp` (canonical
   `FullM4Compact.fullCompactMarkLiveSpec`), proving `!FL_ACTIVE` variables stay unmapped (`0u`).
3. `full_compact_vars_m7fix_flags_wp` + `full_compact_vars_m7fix_wp` (canonical
   `FullM4Compact.fullCompactVarsSpec`), proving exact flag preservation `fl'[nv] = fl[inv[nv]]`
   under `nv ≤ inv[nv]`.
4. Closed `4`-row `m7CompactFixSpecTable`, `m7CompactFixEnv`, `m7CompactFix_moduleOk`, and
   drop-in `Impl` bridges.
5. Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) for all `3` fixes,
   including zombie `PH_RED` clause `[1, 2, 4]` and flag preservation `fl'[0] = 8#32`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7CompactFix

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Compact
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullCompactTactics

/-! ## 1. `full_compact_needed_m7fix` (`1%` Trigger Parity & `fullCompactNeededSpec`) -/

section CompactNeededProof

/-- Exact `1%` compaction-trigger specification for `full_compact_needed_m7fix`. -/
def fullCompactNeededM7FixSpec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.cur_level < 2 ^ 64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ res : Bool,
      (res = true ↔ s.core.cur_level = 0 ∧ s.core.dense_mode = 0#64 ∧
        128 ≤ s.core.cur_vars ∧ s.core.unassigned.toNat < s.core.cur_vars ∧
        s.core.cur_vars < 100 * (s.core.cur_vars - s.core.unassigned.toNat)) →
      Q (res, ()) m

private theorem m7fix_1pct_ult_iff {cv : Nat} {un : BitVec 64}
    (hcv_le : cv ≤ 2 * 2 ^ 28) (hun : un.toNat < cv) :
    BitVec.ult (BitVec.ofNat 64 cv) ((BitVec.ofNat 64 cv - un) * 100#64) = true ↔
      cv < 100 * (cv - un.toNat) := by
  have hsub : (BitVec.ofNat 64 cv - un).toNat = cv - un.toNat := by bv_omega
  have hmul : ((BitVec.ofNat 64 cv - un) * 100#64).toNat = (cv - un.toNat) * 100 := by
    rw [BitVec.toNat_mul, hsub, show (100#64 : BitVec 64).toNat = 100 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.ult_iff_toNat_lt, hmul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Parametric `Func.wp` proof for `full_compact_needed_m7fix` against exact `1%` trigger. -/
theorem full_compact_needed_m7fix_exact_wp (Γ : Env) :
    ∀ a m Q X, fullCompactNeededM7FixSpec a m Q X →
      Func.wp Γ full_compact_needed_m7fix_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl_lt, hm, hQ⟩
  have hcv := hlen.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  unfold Func.wp full_compact_needed_m7fix_body
  c0_hsteps <;>
    first
    | exact hQ false ⟨fun hf => Bool.noConfusion hf, fun h => by
        rcases h with ⟨hcl0, hdm0, h128, hun, h100⟩
        have hbad : False := by c0_bound
        exact hbad.elim⟩
    | (refine hQ _ ?_
       have hcl0 : s.core.cur_level = 0 := by c0_bound
       have hdm0 : s.core.dense_mode = 0#64 := by c0_bound
       have h128 : 128 ≤ s.core.cur_vars := by c0_bound
       have hun : s.core.unassigned.toNat < s.core.cur_vars := by c0_bound
       have hiff := m7fix_1pct_ult_iff (by omega) hun
       constructor
       · intro hres; exact ⟨hcl0, hdm0, h128, hun, hiff.mp hres⟩
       · intro ⟨_, _, _, _, hlt⟩; exact hiff.mpr hlt)

/-- Drop-in `Func.wp` proof for `full_compact_needed_m7fix` against `fullCompactNeededSpec`. -/
theorem full_compact_needed_m7fix_wp (Γ : Env) :
    ∀ a m Q X, fullCompactNeededSpec a m Q X →
      Func.wp Γ full_compact_needed_m7fix_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl_lt, hm, hQ⟩
  exact full_compact_needed_m7fix_exact_wp Γ _ m Q X
    ⟨c, s, R, rfl, hlen, hcl_lt, hm, fun res hiff =>
      hQ res fun hres => let ⟨h1, h2, h3, _, _⟩ := hiff.mp hres; ⟨h1, h2, h3⟩⟩

end CompactNeededProof

/-! ## 2. `full_compact_mark_live_m7fix` (No-Zombie Marking & `fullCompactMarkLiveSpec`) -/

section CompactMarkLiveProof

def NoZombieMap (k : FullCoreState) (ws : List (BitVec 32)) : Prop :=
  ∀ u < k.cur_vars, (k.flags[u]?.getD 0#32 &&& 1#32) = 0#32 → ws[u]? = some 0#32

private theorem noZombieMap_set_active {k : FullCoreState} {ws : List (BitVec 32)}
    (hnz : NoZombieMap k ws) {v : Nat} (hv : v < k.flags.length)
    (hact : ((k.flags[v]'hv) &&& 1#32) ≠ 0#32) (val : BitVec 32) :
    NoZombieMap k (ws.set v val) := by
  intro u hu hdead
  have hne : u ≠ v := by
    intro h; subst h
    simp only [List.getElem?_eq_getElem hv, Option.getD_some] at hdead
    exact hact hdead
  rw [List.getElem?_set_ne (Ne.symm hne)]
  exact hnz u hu hdead

private theorem fullSparseInvW_with_ws1 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {ws1 : List (BitVec 32)}
    (hsp : FullSparseInvW c F0 F_cur s) (hlen1 : ws1.length = 2 * c.max_vars) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with work_stk1 := ws1 } } :=
  ⟨hsp.1.with_scratch { hsp.1.scratch_ok with work_stk1_len := hlen1 },
    hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

/-- Stronger `Func.wp` proof for `full_compact_mark_live_m7fix` certifying both
`FullSparseInvW` preservation and `NoZombieMap` (every `!FL_ACTIVE` variable keeps `map[u] = 0`). -/
theorem full_compact_mark_live_m7fix_no_zombie_wp (Γ : Env)
    (hnext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [] } {X : XPost}
    (hsp : FullSparseInvW c F0 F_cur s) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ ws1' m',
      let s' : FullState := { s with scratch := { s.scratch with work_stk1 := ws1' } }
      FullSparseInvW c F0 F_cur s' → NoZombieMap s.core ws1' →
      (FullMem c s' ⋆ R) m' → Q () m') :
    Func.wp Γ full_compact_mark_live_m7fix_body (c.hdr, ()) m Q X := by
  have hlen := hsp.1
  have hw := hsp.2.1
  have hdm := hsp.2.2.2.2.2
  have hwat : WatchesInv F_cur s.core := by
    have hm' := hw.watches; unfold ModeWatchesInv at hm'; rwa [ite_eq_left hdm] at hm'
  have hcv_le := hlen.core_ok.cur_vars_le
  have hal_le := hlen.core_ok.arena_len_le
  have har_len := hlen.core_ok.arena_len_arr
  have hwl_le := hlen.core_ok.wlen_le
  have hws_len := hlen.core_ok.wstk_len_arr
  have hwv_len := hlen.core_ok.wvec_len
  have hv_len := hlen.core_ok.vals_len
  have hfl_len := hlen.core_ok.flags_len
  have hws1_len := hlen.scratch_ok.work_stk1_len
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have har_lt : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hcv_64 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hnlits_eq : ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat =
      2 * s.core.cur_vars := by
    rw [bv64_shl1_toNat (by rw [hcv_64]; omega), hcv_64]
  unfold Func.wp full_compact_mark_live_m7fix_body
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (v, ()) m1 =>
      v.toNat ≤ s.core.cur_vars ∧
      ∃ ws1 : List (BitVec 32), ws1.length = 2 * c.max_vars ∧
        (∀ u < v.toNat, ws1[u]? = some 0#32) ∧
        (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1 } } ⋆ R) m1)
    (fun (v, ()) _ => s.core.cur_vars - v.toNat)
    (fun J1 hLoop1 => by
      c0_hsteps
      exact hLoop1 (0#64, ()) m
        ⟨Nat.zero_le _, s.scratch.work_stk1, hws1_len, (fun _ h => by cases h), hm⟩)
    (fun J1 ⟨v, ⟨⟩⟩ m1 ⟨hv_le, ws1, hlen1, hz1, hm1⟩ hLoop1 => ?_)
  c0_hsplit
  · have hv_lt : v.toNat < s.core.cur_vars := by c0_bound
    have hv1_eq : (v + 1#64).toNat = v.toNat + 1 := bv64_add1 (by omega)
    have hv_ws : v.toNat < ws1.length := by omega
    c0_hsteps
    refine hLoop1 (v + 1#64, ()) _ (by dsimp only; rw [hv1_eq]; omega)
      ⟨by rw [hv1_eq]; omega, ws1.set v.toNat 0#32, by simp [hlen1], fun u hu => ?_, hm⟩
    rw [hv1_eq] at hu
    by_cases huv : u = v.toNat
    · subst huv; exact List.getElem?_set_self hv_ws
    · rw [List.getElem?_set_ne (Ne.symm huv)]; exact hz1 u (by omega)
  · clear hLoop1 J1
    have hv_eq : v.toNat = s.core.cur_vars := by c0_bound
    have hnz1 : NoZombieMap s.core ws1 := fun u hu _ => hz1 u (hv_eq ▸ hu)
    clear hv_le hv_eq hz1
    c0_hsteps_nogrp
    refine wp_loop_inv
      (fun (l, ()) m2 =>
        l.toNat ≤ 2 * s.core.cur_vars ∧
        ∃ ws2 : List (BitVec 32), ws2.length = 2 * c.max_vars ∧ NoZombieMap s.core ws2 ∧
          (FullMem c { s with scratch := { s.scratch with work_stk1 := ws2 } } ⋆ R) m2)
      (fun (l, ()) _ => 2 * s.core.cur_vars - l.toNat)
      (fun J2 hLoop2 => by
        c0_hsteps; exact hLoop2 (0#64, ()) m1 ⟨Nat.zero_le _, ws1, hlen1, hnz1, hm1⟩)
      (fun J2 ⟨l, ⟨⟩⟩ m2 ⟨hl_le, ws2, hlen2, hnz2, hm2⟩ hLoop2 => ?_)
    c0_hsplit
    · have hl_lt : l.toNat < 2 * s.core.cur_vars := by
        have : l.toNat < ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat := by c0_bound
        omega
      have hl1_eq : (l + 1#64).toNat = l.toNat + 1 := bv64_add1 (by omega)
      have h2l_eq : (l <<< (1 : Nat)).toNat = 2 * l.toNat := bv64_shl1_toNat (by omega)
      have h2l1_eq : ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * l.toNat + 1 := by
        rw [bv64_add1 (by rw [h2l_eq]; omega), h2l_eq]
      have h2l_lt : 2 * l.toNat < s.core.wvec.length := by omega
      have h2l1_lt : 2 * l.toNat + 1 < s.core.wvec.length := by omega
      let off0 := fullWatchOffCore s.core l.toNat
      let sz0 := fullWatchSizeCore s.core l.toNat
      have hoff_eq : (s.core.wvec[2 * l.toNat]'h2l_lt).toNat = off0 := by
        unfold off0 fullWatchOffCore
        rw [List.getElem?_eq_getElem h2l_lt, Option.getD_some]
      have hsz_eq : (s.core.wvec[2 * l.toNat + 1]'h2l1_lt).toNat = sz0 := by
        unfold sz0 fullWatchSizeCore
        rw [List.getElem?_eq_getElem h2l1_lt, Option.getD_some]
      have hbd : off0 + sz0 ≤ s.core.wlen := hwat.layout.bounds l.toNat hl_lt
      have hslice0 : WatchSliceOk F_cur s.core l.toNat off0 sz0 := hwat.slices l.toNat hl_lt
      let end0 := off0 + sz0
      have hend_nat :
          ((s.core.wvec[(l <<< (1 : Nat)).toNat]'(by rw [h2l_eq]; omega)).setWidth 64 +
            (s.core.wvec[((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'(by
              rw [h2l1_eq]; omega)).setWidth 64).toNat = end0 := by
        rw [BitVec.toNat_add, zext_toNat _ (by decide), zext_toNat _ (by decide)]
        simp only [h2l_eq, h2l1_eq, hoff_eq, hsz_eq]
        exact Nat.mod_eq_of_lt (by omega)
      c0_hsteps_nogrp
      refine wp_loop_inv
        (fun (p, ()) mP =>
          off0 ≤ p.toNat ∧ p.toNat ≤ end0 ∧
          WatchSliceOk F_cur s.core l.toNat p.toNat (end0 - p.toNat) ∧
          ∃ wsP : List (BitVec 32), wsP.length = 2 * c.max_vars ∧ NoZombieMap s.core wsP ∧
            (FullMem c { s with scratch := { s.scratch with work_stk1 := wsP } } ⋆ R) mP)
        (fun (p, ()) _ => end0 - p.toNat)
        (fun Jp hLoopP => by
          c0_hsteps
          have hoff64 : ((s.core.wvec[2 * l.toNat]'h2l_lt).setWidth 64).toNat = off0 := by
            rw [zext_toNat _ (by decide)]; exact hoff_eq
          refine hLoopP _ m2 ⟨by simp only [h2l_eq, hoff64]; exact Nat.le_refl _,
            by simp only [h2l_eq, hoff64]; omega, ?_, ws2, hlen2, hnz2, hm2⟩
          simpa only [h2l_eq, hoff64, show end0 - off0 = sz0 by omega] using hslice0)
        (fun Jp ⟨p, ⟨⟩⟩ mP ⟨hop, hpe, hrem, wsP, hlenP, hnzP, hmP⟩ hLoopP => ?_)
      c0_hsplit
      · have hp_lt : p.toNat < end0 := by
          have h1 : p.toNat < ((s.core.wvec[(l <<< (1 : Nat)).toNat]'(by
              rw [h2l_eq]; omega)).setWidth 64 +
              (s.core.wvec[((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'(by
                rw [h2l1_eq]; omega)).setWidth 64).toNat := by c0_bound
          omega
        have hp_wstk : p.toNat < s.core.wstk.length := by omega
        let w0 := s.core.wstk[p.toNat]'hp_wstk
        have hw0_some : s.core.wstk[p.toNat]? = some w0 := List.getElem?_eq_getElem hp_wstk
        have hstep := FullM4Compact.WatchSliceOk_step hrem (by omega) hw0_some
        c0_hsteps_nogrp; c0_hstep; c0_hsplit
        · have hbin0 : (w0 &&& 0x80000000#32) ≠ 0#32 := by
            change ((s.core.wstk[p.toNat]'hp_wstk) &&& 0x80000000#32) ≠ 0#32; assumption
          obtain ⟨_, hot_lt, _, hrem'⟩ := hstep.1 hbin0
          have hp1_eq : (p + 1#64).toNat = p.toNat + 1 := bv64_add1 (by omega)
          have hlv_eq : (l >>> (1 : Nat)).toNat = l.toNat / 2 := bv64_shr1_toNat l
          have hrem_p1 : WatchSliceOk F_cur s.core l.toNat (p.toNat + 1)
              (end0 - (p.toNat + 1)) := by simpa [Nat.sub_sub] using hrem'
          have hl_v : l.toNat < s.core.vals.length := by omega
          have hot_v : ((w0 &&& 0x7FFFFFFF#32).setWidth 64).toNat < s.core.vals.length := by
            rw [zext_toNat _ (by decide)]; omega
          have hl_fl : (l >>> (1 : Nat)).toNat < s.core.flags.length := by rw [hlv_eq]; omega
          have hot_fl :
              (((w0 &&& 0x7FFFFFFF#32) >>> 1#32).setWidth 64).toNat < s.core.flags.length := by
            rw [zext_toNat _ (by decide), bv32_shr1_toNat]; omega
          have hl_wsP : (l >>> (1 : Nat)).toNat < wsP.length := by rw [hlv_eq]; omega
          have hot_wsP :
              (((w0 &&& 0x7FFFFFFF#32) >>> 1#32).setWidth 64).toNat < wsP.length := by
            rw [zext_toNat _ (by decide), bv32_shr1_toNat]; omega
          c0_hsteps_nogrp
          refine wp_join_state0 (α := List (BitVec 32))
            (fun ws' m' => ws'.length = 2 * c.max_vars ∧ NoZombieMap s.core ws' ∧
              (FullMem c { s with scratch := { s.scratch with work_stk1 := ws' } } ⋆ R) m')
            ?_ ?_
          · rintro _ ws' m' ⟨hlen', hnz', hm'⟩
            c0_hsteps
            exact hLoopP (p + 1#64, ()) m' (by dsimp only; rw [hp1_eq]; omega)
              ⟨by rw [hp1_eq]; omega, by rw [hp1_eq]; omega,
               by rw [hp1_eq]; exact hrem_p1, ws', hlen', hnz', hm'⟩
          · intro Jb hJb
            c0_hsteps <;>
              first
              | exact hJb _ _ ⟨by simp [hlenP],
                  noZombieMap_set_active
                    (noZombieMap_set_active hnzP hl_fl (by c0_bound) 1#32)
                    hot_fl (by c0_bound) 1#32,
                  hm⟩
              | exact hJb wsP mP ⟨hlenP, hnzP, hmP⟩
        · have hlg0 : (w0 &&& 0x80000000#32) = 0#32 := by
            change ((s.core.wstk[p.toNat]'hp_wstk) &&& 0x80000000#32) = 0#32; assumption
          have ⟨_, hrem'⟩ := hstep.2 hlg0
          have hp2_eq : (p + 2#64).toNat = p.toNat + 2 := bv64_add2 (by omega)
          have hrem_p2 : WatchSliceOk F_cur s.core l.toNat (p.toNat + 2)
              (end0 - (p.toNat + 2)) := by simpa [Nat.sub_sub] using hrem'
          c0_hsteps
          exact hLoopP (p + 2#64, ()) mP (by dsimp only; rw [hp2_eq]; omega)
            ⟨by rw [hp2_eq]; omega, by rw [hp2_eq]; omega, by rw [hp2_eq]; exact hrem_p2,
             wsP, hlenP, hnzP, hmP⟩
      · c0_hsteps
        exact hLoop2 (l + 1#64, ()) mP (by dsimp only; rw [hl1_eq]; omega)
          ⟨by rw [hl1_eq]; omega, wsP, hlenP, hnzP, hmP⟩
    · clear hLoop2 J2 hm1 hm ws1 hlen1 hnz1 hw hdm hwat hwl_le hws_len hwv_len hcv_64
      have h2bv : (2 : BitVec 64).toNat = 2 := rfl
      have h3bv : (3 : BitVec 64).toNat = 3 := rfl
      have h2cv : 2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 = 2 * s.core.cur_vars := by omega
      c0_hsteps_nogrp
      refine wp_join_state1 (t := i64) (α := BitVec 64 × List (BitVec 32)) Prod.fst
        (fun ⟨_, wsE⟩ mE => wsE.length = 2 * c.max_vars ∧ NoZombieMap s.core wsE ∧
          (FullMem c { s with scratch := { s.scratch with work_stk1 := wsE } } ⋆ R) mE)
        (fun _ ⟨_, wsE⟩ mE ⟨hlenE, hnzE, hmE⟩ => by
          c0_hsteps; exact hQ wsE mE (fullSparseInvW_with_ws1 hsp hlenE) hnzE hmE)
        (fun J3x hJ3x => ?_)
      c0_hsteps_nogrp
      refine wp_loop_inv
        (fun (pos, ()) m3 =>
          pos.toNat ≤ s.core.arena_len ∧
          ∃ ws3 : List (BitVec 32), ws3.length = 2 * c.max_vars ∧ NoZombieMap s.core ws3 ∧
            (FullMem c { s with scratch := { s.scratch with work_stk1 := ws3 } } ⋆ R) m3)
        (fun (pos, ()) _ => s.core.arena_len - pos.toNat)
        (fun J3 hLoop3 => by
          c0_hsteps; exact hLoop3 (0#64, ()) m2 ⟨Nat.zero_le _, ws2, hlen2, hnz2, hm2⟩)
        (fun J3 ⟨pos, ⟨⟩⟩ m3 ⟨hpos_le, ws3, hlen3, hnz3, hm3⟩ hLoop3 => ?_)
      c0_hsplit
      · have hpos_lt : pos.toNat < s.core.arena_len := by c0_bound
        c0_hsplit
        · c0_hsteps
          exact hJ3x (pos, ws3) m3 ⟨hlen3, hnz3, hm3⟩
        · have hpos3_le : pos.toNat + 3 ≤ s.core.arena_len := by bv_omega
          have hpos2_eq : (pos + (2 : BitVec 64)).toNat = pos.toNat + 2 := bv64_add2 (by omega)
          have hpos2_mod : (pos.toNat + (2 : BitVec 64).toNat) % 2 ^ 64 = pos.toNat + 2 := by
            rw [h2bv, Nat.mod_eq_of_lt (by omega)]
          have hpos2_lt : (pos + (2 : BitVec 64)).toNat < s.core.arena.length := by
            rw [hpos2_eq]; omega
          let csz := s.core.arena[pos.toNat + 2]'(by omega)
          have hn_bounds := fullArenaNextOff_bounds (ar := s.core.arena)
            (alen := s.core.arena_len) (cref := pos.toNat) hpos3_le
          have hpos32_eq : (pos.setWidth 32).toNat = pos.toNat := by bv_omega
          c0_hsteps; c0_call hnext
          refine ⟨c, { s with scratch := { s.scratch with work_stk1 := ws3 } }, R, rfl,
            hlen.with_scratch { hlen.scratch_ok with work_stk1_len := hlen3 }, hm3, ?_⟩
          dsimp only
          simp only [hpos32_eq]
          let npos_nat := fullArenaNextOff s.core.arena s.core.arena_len pos.toNat
          have hnpos_to : ((BitVec.ofNat 32 npos_nat).setWidth 64).toNat = npos_nat := by
            rw [zext_toNat _ (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          c0_hsteps_nogrp
          refine wp_join_state0 (α := List (BitVec 32))
            (fun ws4 m4 => ws4.length = 2 * c.max_vars ∧ NoZombieMap s.core ws4 ∧
              (FullMem c { s with scratch := { s.scratch with work_stk1 := ws4 } } ⋆ R) m4)
            (fun _ ws4 m4 ⟨hlen4, hnz4, hm4⟩ => by
              c0_hsteps
              exact hLoop3 _ m4 (by dsimp only; rw [hnpos_to]; omega)
                ⟨by rw [hnpos_to]; omega, ws4, hlen4, hnz4, hm4⟩)
            (fun J4 hJ4 => ?_)
          c0_hsplit
          · c0_hsplit
            · c0_hsplit
              · have hfit : pos.toNat + 3 + csz.toNat ≤ s.core.arena_len := by
                  have h1 := hc
                  have hal64 : s.core.arena_len % 2 ^ 64 = s.core.arena_len :=
                    Nat.mod_eq_of_lt (by omega)
                  have hcsz32 := csz.isLt
                  have hp3c : (pos.toNat + 3 + csz.toNat) % 2 ^ 64 = pos.toNat + 3 + csz.toNat :=
                    Nat.mod_eq_of_lt (by omega)
                  simp only [hpos2_mod, h3bv, hal64] at h1
                  change (pos.toNat + 3 + csz.toNat) % 2 ^ 64 ≤ s.core.arena_len at h1
                  rwa [hp3c] at h1
                c0_hsteps_nogrp
                refine wp_join_group (fun (_, _, _, _, ()) mE => mE = m3) ?_ ?_
                · rintro _ ⟨sat, has_dead, ucnt, i0, ⟨⟩⟩ mE hmE
                  rcases hmE.symm with rfl
                  c0_hsteps_nogrp
                  refine wp_join_state1 (t := i32) (α := BitVec 32 × List (BitVec 32)) Prod.fst
                    (fun ⟨_, ws'⟩ m' => ws'.length = 2 * c.max_vars ∧ NoZombieMap s.core ws' ∧
                      (FullMem c { s with scratch := { s.scratch with work_stk1 := ws' } } ⋆ R) m')
                    (fun _ ⟨_, ws'⟩ m' ⟨hlen', hnz', hm'⟩ => by
                      c0_hsteps; exact hJ4 ws' m' ⟨hlen', hnz', hm'⟩)
                    (fun Jif hJif => ?_)
                  c0_hsplit
                  · c0_hsteps; exact hJif (i0, ws3) m3 ⟨hlen3, hnz3, hm3⟩
                  · c0_hsteps_nogrp
                    refine wp_join_group (fun () m' => m' = m3) ?_ ?_
                    · rintro _ ⟨⟩ m' hm'
                      rcases hm'.symm with rfl
                      c0_hsteps_nogrp
                      c0_hsplit
                      · c0_hsteps_nogrp
                        refine wp_loop_inv
                            (fun (i2, ()) mK =>
                              i2.toNat ≤ csz.toNat ∧
                              ∃ wsK : List (BitVec 32), wsK.length = 2 * c.max_vars ∧
                                NoZombieMap s.core wsK ∧
                                (FullMem c { s with scratch := { s.scratch with
                                  work_stk1 := wsK } } ⋆ R) mK)
                            (fun (i2, ()) _ => csz.toNat - i2.toNat)
                            (fun Jk hLoopK => by
                              c0_hsteps
                              exact hLoopK (0#32, ()) m3 ⟨Nat.zero_le _, ws3, hlen3, hnz3, hm3⟩)
                            (fun Jk ⟨i2, ⟨⟩⟩ mK ⟨hi2_le, wsK, hlenK, hnzK, hmK⟩ hLoopK => ?_)
                        c0_hsplit
                        · have hi2_lt : i2.toNat < csz.toNat := by
                            have h1 := hc; simp only [hpos2_mod] at h1; exact h1
                          have hi2_1 : (i2 + 1#32).toNat = i2.toNat + 1 := bv32_add1 (by omega)
                          have hpi2_eq : (pos + 3#64 + i2.setWidth 64).toNat =
                              pos.toNat + 3 + i2.toNat := by bv_omega
                          have hpi2_mod :
                              (pos.toNat + (3 : BitVec 64).toNat + i2.toNat) % 2 ^ 64 =
                                pos.toNat + 3 + i2.toNat := by
                            rw [h3bv, Nat.mod_eq_of_lt (by omega)]
                          have hpi2_lt :
                              (pos + 3#64 + i2.setWidth 64).toNat < s.core.arena.length := by
                            rw [hpi2_eq]; omega
                          c0_hsteps_nogrp
                          refine wp_join_state0 (α := List (BitVec 32))
                            (fun ws' m' => ws'.length = 2 * c.max_vars ∧
                              NoZombieMap s.core ws' ∧
                              (FullMem c { s with scratch := { s.scratch with
                                work_stk1 := ws' } } ⋆ R) m')
                            (fun _ ws' m' ⟨hlen', hnz', hm'⟩ => by
                              c0_hsteps
                              exact hLoopK (i2 + 1#32, ()) m' (by dsimp only; rw [hi2_1]; omega)
                                ⟨by rw [hi2_1]; omega, ws', hlen', hnz', hm'⟩)
                            (fun Jm hJm => ?_)
                          c0_hsplit
                          · have hlit2_lt :
                                (s.core.arena[(pos + 3#64 + i2.setWidth 64).toNat]'hpi2_lt).toNat <
                                2 * s.core.cur_vars := by
                              have h1 := hc; simp only [hpi2_mod, h2cv] at h1
                              simp only [hpi2_eq]; exact h1
                            have hlit2_v :
                                ((s.core.arena[(pos + 3#64 +
                                  i2.setWidth 64).toNat]'hpi2_lt).setWidth 64).toNat <
                                  s.core.vals.length := by
                              rw [zext_toNat _ (by decide)]; omega
                            have hlit2_fl :
                                (((s.core.arena[(pos + 3#64 +
                                  i2.setWidth 64).toNat]'hpi2_lt) >>> 1#32).setWidth 64).toNat <
                                  s.core.flags.length := by
                              rw [zext_toNat _ (by decide), bv32_shr1_toNat]; omega
                            have hlit2_ws :
                                (((s.core.arena[(pos + 3#64 +
                                  i2.setWidth 64).toNat]'hpi2_lt) >>> 1#32).setWidth 64).toNat <
                                  wsK.length := by
                              rw [zext_toNat _ (by decide), bv32_shr1_toNat]; omega
                            c0_hsplit
                            · c0_hsplit
                              · have hact : ((s.core.flags[(((s.core.arena[(pos + 3#64 +
                                    i2.setWidth 64).toNat]'hpi2_lt) >>> 1#32).setWidth
                                    64).toNat]'hlit2_fl) &&& 1#32) ≠ 0#32 := by
                                  have h1 := hc
                                  simp only [hpi2_mod] at h1
                                  have hidx_eq :
                                      (((s.core.arena[(pos + 3#64 +
                                          i2.setWidth 64).toNat]'hpi2_lt) >>> 1#32).setWidth
                                          64).toNat =
                                        (s.core.arena[pos.toNat + 3 + i2.toNat]'(by
                                          rw [← hpi2_eq]; exact hpi2_lt)).toNat / 2 := by
                                    rw [zext_toNat _ (by decide), bv32_shr1_toNat]
                                    simp only [hpi2_eq]
                                  have hgoal :
                                      s.core.flags[(s.core.arena[pos.toNat + 3 + i2.toNat]'(by
                                        rw [← hpi2_eq]; exact hpi2_lt)).toNat / 2]'(by
                                        rw [← hidx_eq]; exact hlit2_fl) &&& 1#32 ≠ 0#32 := h1
                                  simpa only [hidx_eq] using hgoal
                                c0_hsteps
                                exact hJm _ _ ⟨by simp [hlenK],
                                  noZombieMap_set_active hnzK hlit2_fl hact 1#32, hm⟩
                              · c0_hsteps; exact hJm wsK mK ⟨hlenK, hnzK, hmK⟩
                            · c0_hsteps; exact hJm wsK mK ⟨hlenK, hnzK, hmK⟩
                          · c0_hsteps; exact hJm wsK mK ⟨hlenK, hnzK, hmK⟩
                        · c0_hsteps; exact hJif (i2, wsK) mK ⟨hlenK, hnzK, hmK⟩
                      · c0_hsteps; exact hJif (i0, ws3) m3 ⟨hlen3, hnz3, hm3⟩
                    · intro Jhd hJhd
                      c0_hsteps <;>
                        first
                        | exact hJhd () m3 rfl
                        | exact hJif (i0, ws3) m3 ⟨hlen3, hnz3, hm3⟩
                · intro Jex hJex
                  obtain ⟨s3, hs3c, hm3s⟩ :
                      ∃ s3 : FullState, s3.core = s.core ∧ (FullMem c s3 ⋆ R) m3 :=
                    ⟨{ s with scratch := { s.scratch with work_stk1 := ws3 } }, rfl, hm3⟩
                  clear hm3 hJ4 hJ3x hLoop3
                  c0_hsteps_nogrp
                  refine wp_loop_inv
                    (fun (_, _, i, ()) mI => i.toNat ≤ csz.toNat ∧ mI = m3)
                    (fun (_, _, i, ()) _ => csz.toNat - i.toNat)
                    (fun Ji hLoopI => by
                      c0_hsteps; exact hLoopI (false, 0#32, 0#32, ()) m3 ⟨Nat.zero_le _, rfl⟩)
                    (fun Ji ⟨hd, ucnt, i, ⟨⟩⟩ mI ⟨hi_le, hmI⟩ hLoopI => ?_)
                  rcases hmI.symm with rfl
                  c0_hsplit
                  · have hi_lt : i.toNat < csz.toNat := by
                      have h1 := hc; simp only [hpos2_mod] at h1; exact h1
                    have hi1_eq : (i + 1#32).toNat = i.toNat + 1 := bv32_add1 (by omega)
                    have hpi_eq : (pos + 3#64 + i.setWidth 64).toNat =
                        pos.toNat + 3 + i.toNat := by bv_omega
                    have hpi_mod : (pos.toNat + (3 : BitVec 64).toNat + i.toNat) % 2 ^ 64 =
                        pos.toNat + 3 + i.toNat := by rw [h3bv, Nat.mod_eq_of_lt (by omega)]
                    have hpi_lt : (pos + 3#64 + i.setWidth 64).toNat < s3.core.arena.length := by
                      rw [hs3c, hpi_eq]; omega
                    c0_hsteps_nogrp
                    refine wp_join_group (fun (_, _, _, ()) m' => m' = m3)
                      (fun _ ⟨_, hd', u', ⟨⟩⟩ m' hm' => by
                        rcases hm'.symm with rfl
                        c0_hsteps
                        exact hLoopI (hd', u', i + 1#32, ()) m3 (by dsimp only; rw [hi1_eq]; omega)
                          ⟨by rw [hi1_eq]; omega, rfl⟩)
                      (fun Ju hJu => ?_)
                    c0_hsplit
                    · have hlit_lt :
                          (s3.core.arena[(pos + 3#64 + i.setWidth 64).toNat]'hpi_lt).toNat <
                          2 * s.core.cur_vars := by
                        have h1 := hc; simp only [hpi_mod, h2cv] at h1
                        simpa only [hpi_eq] using h1
                      have hlit_v :
                          ((s3.core.arena[(pos + 3#64 +
                            i.setWidth 64).toNat]'hpi_lt).setWidth 64).toNat <
                            s3.core.vals.length := by
                        have hv3 : s3.core.vals.length = 2 * c.max_vars := by
                          rw [hs3c]; exact hv_len
                        rw [zext_toNat _ (by decide)]; omega
                      have hlit_fl :
                          (((s3.core.arena[(pos + 3#64 +
                            i.setWidth 64).toNat]'hpi_lt) >>> 1#32).setWidth 64).toNat <
                            s3.core.flags.length := by
                        have hfl3 : s3.core.flags.length = c.max_vars := by rw [hs3c]; exact hfl_len
                        rw [zext_toNat _ (by decide), bv32_shr1_toNat]; omega
                      c0_hsteps <;>
                        first
                        | exact hJex (true, hd, ucnt, i, ()) m3 rfl
                        | exact hJu (false, true, ucnt, ()) m3 rfl
                        | exact hJu (false, hd, ucnt + 1#32, ()) m3 rfl
                        | exact hJu (false, hd, ucnt, ()) m3 rfl
                    · c0_hsteps; exact hJu (false, hd, ucnt, ()) m3 rfl
                  · c0_hsteps; exact hJex (false, hd, ucnt, i, ()) m3 rfl
              · c0_hsteps; exact hJ4 ws3 m3 ⟨hlen3, hnz3, hm3⟩
            · c0_hsteps; exact hJ4 ws3 m3 ⟨hlen3, hnz3, hm3⟩
          · c0_hsteps; exact hJ4 ws3 m3 ⟨hlen3, hnz3, hm3⟩
      · c0_hsteps; exact hJ3x (pos, ws3) m3 ⟨hlen3, hnz3, hm3⟩

/-- Drop-in `Func.wp` proof for `full_compact_mark_live_m7fix` against `fullCompactMarkLiveSpec`. -/
theorem full_compact_mark_live_m7fix_wp (Γ : Env)
    (hnext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, fullCompactMarkLiveSpec a m Q X →
      Func.wp Γ full_compact_mark_live_m7fix_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hm, hQ⟩
  exact full_compact_mark_live_m7fix_no_zombie_wp Γ hnext hsp hm
    (fun ws1' m' hsp' _ hm' => hQ ws1' m' hsp' hm')

end CompactMarkLiveProof

/-! ## 3. `full_compact_vars_m7fix` (Exact Flag Preservation & `fullCompactVarsSpec`) -/

section CompactVarsProof

private theorem bv8_sext32_eq0_fix {x : BitVec 8} (h : x.signExtend 32 = 0#32) : x = 0#8 := by
  ext i hi; have h1 := congrArg (·[i]) h
  simp [BitVec.getElem_signExtend, hi] at h1; simp [h1]

private theorem full_compact_vars_m7fix_lengths {c c' : FullCfg} {s : FullState}
    {vals1 : List (BitVec 8)} {fl3 lvl3 rsns3 : List (BitVec 32)}
    {ph2 pt2 pb2 wb2 : List (BitVec 8)} {sc3 : List (BitVec 64)}
    {qs3 qp3 qn3 ps3 : List (BitVec 32)} {ncv tgt_asg bst_asg : BitVec 64}
    (hlen : s.LengthsOk c) (hcompat : FullCfgCompat c c')
    (hcv_ge' : c'.mv ≤ ncv.toNat) (hmv_lt_max : ncv.toNat ≤ c.max_vars)
    (hvl1 : vals1.length = 2 * c.max_vars)
    (hfl3 : fl3.length = c.max_vars) (hlv3 : lvl3.length = c.max_vars)
    (hrs3 : rsns3.length = c.max_vars) (hph2 : ph2.length = c.max_vars)
    (hpt2 : pt2.length = c.max_vars) (hpb2 : pb2.length = c.max_vars)
    (hwb2 : wb2.length = c.max_vars) (hsc3 : sc3.length = c.max_vars)
    (hqs3 : qs3.length = c.max_vars) (hqp3 : qp3.length = c.max_vars)
    (hqn3 : qn3.length = c.max_vars) (hps3 : ps3.length = c.max_vars) :
    ({ core := { s.core with
        vals := vals1, flags := fl3, lvl := lvl3, rsns := rsns3,
        frame_trail := s.core.frame_trail.set 0 0#32,
        frame_dec := s.core.frame_dec.set 0 0xFFFFFFFF#32,
        trail_end := 0, propagated := 0, cur_level := 0,
        unflushed := 0#64, confl_ref := 0xFFFFFFFF#64, confl_type := 0#64,
        cur_vars := ncv.toNat, unassigned := ncv }
       scratch := { s.scratch with
        phases := ph2, phases_target := pt2, phases_best := pb2, walk_best := wb2,
        score := sc3, q_stamp := qs3, q_prev := qp3, q_next := qn3, pos := ps3,
        target_assigned := tgt_asg, best_assigned := bst_asg } } : FullState).LengthsOk c' := by
  obtain ⟨_, _, _, hmax, _, har, hwc, hdel, hred, hext, hscr⟩ := hcompat
  have hft_len := hlen.core_ok.frame_trail_len
  have hfd_len := hlen.core_ok.frame_dec_len
  exact ⟨⟨hmax ▸ hvl1, hmax ▸ hlen.core_ok.lit_mark_len,
      hmax ▸ hlen.core_ok.mrk_len, hmax ▸ hfl3, hmax ▸ hlv3, hmax ▸ hrs3,
      hmax ▸ hlen.core_ok.trl_len, hmax ▸ hlen.core_ok.trail_pos_len,
      hmax ▸ hlen.core_ok.tmp_len_arr, hmax ▸ hlen.core_ok.min_clr_len_arr,
      hmax ▸ (by rw [List.length_set]; exact hft_len),
      hmax ▸ (by rw [List.length_set]; exact hfd_len),
      hmax ▸ hlen.core_ok.wvec_len, hmax ▸ hlen.core_ok.repr_len,
      (by simp only [FullCfg.minDepth, hmax]; exact hlen.core_ok.min_stk_len),
      har ▸ hlen.core_ok.arena_len_arr,
      hwc ▸ hlen.core_ok.wstk_len_arr, hcv_ge', hmax ▸ hmv_lt_max,
      har ▸ hlen.core_ok.arena_len_le, hwc ▸ hlen.core_ok.wlen_le,
      Nat.zero_le _, Nat.zero_le _, hmax ▸ hlen.core_ok.tmp_len_le,
      hmax ▸ hlen.core_ok.min_clr_len_le⟩,
    ⟨hmax ▸ hlen.scratch_ok.walk_vals_len, hmax ▸ hph2, hmax ▸ hpt2,
      hmax ▸ hpb2, hmax ▸ hwb2, hmax ▸ hlen.scratch_ok.heap_len_arr,
      hmax ▸ hps3, hmax ▸ hlen.scratch_ok.shrink_stk_len, hmax ▸ hqp3,
      hmax ▸ hqn3, hmax ▸ hqs3, hmax ▸ hlen.scratch_ok.wsort_len,
      hmax ▸ hlen.scratch_ok.work_stk1_len, hmax ▸ hlen.scratch_ok.work_stk2_len,
      hmax ▸ hlen.scratch_ok.tarjan_mark_len,
      hmax ▸ hlen.scratch_ok.tarjan_reach_len, hmax ▸ hsc3,
      hmax ▸ hlen.scratch_ok.sim_sig_len, hlen.scratch_ok.glue_used_len,
      hlen.scratch_ok.last_learned_len, hdel ▸ hlen.scratch_ok.delayed_len_arr,
      hred ▸ hlen.scratch_ok.red_refs_len, hext ▸ hlen.scratch_ok.extend_stk_len,
      hscr ▸ hlen.scratch_ok.scratch_buf_len⟩⟩

private def M7FixFlPres (s : FullState) (ncv : BitVec 64) (nv : Nat)
    (fl2 : List (BitVec 32)) : Prop :=
  (∀ k < ncv.toNat, k ≤ (s.scratch.work_stk2[k]?.getD 0#32).toNat) →
    (∀ k < nv, fl2[k]? = s.core.flags[(s.scratch.work_stk2[k]?.getD 0#32).toNat]?) ∧
    (∀ j, nv ≤ j → fl2[j]? = s.core.flags[j]?)

private def M7FixFlPres3 (s : FullState) (ncv : BitVec 64) (fl3 : List (BitVec 32))
    (hi : Nat) : Prop :=
  ((∀ k < ncv.toNat, k ≤ (s.scratch.work_stk2[k]?.getD 0#32).toNat) →
    ∀ k < ncv.toNat, fl3[k]? = s.core.flags[(s.scratch.work_stk2[k]?.getD 0#32).toNat]?) ∧
  (∀ v, ncv.toNat ≤ v → v < hi → fl3[v]? = some 0#32)

/-- Stronger `Func.wp` proof for `full_compact_vars_m7fix` certifying both `fullCompactVarsSpec`
and exact flag preservation `fl'[nv]? = s.core.flags[inv[nv]]?` under `nv ≤ inv[nv]`. -/
theorem full_compact_vars_m7fix_flags_wp (Γ : Env)
    {c : FullCfg} {s : FullState} {old_cv ncv : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [] } {X : XPost}
    (hlen : s.LengthsOk c) (hold : old_cv.toNat = s.core.cur_vars)
    (hncv_le : ncv.toNat ≤ old_cv.toNat)
    (hinv_ok : ∀ nv < ncv.toNat, (s.scratch.work_stk2[nv]?.getD 0#32).toNat < old_cv.toNat)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ c' vals' fl' lvl' rsns' ft0' fd0' sc' m',
      let s' : FullState :=
        { core := { s.core with vals := vals', flags := fl', lvl := lvl', rsns := rsns',
                                frame_trail := s.core.frame_trail.set 0 ft0',
                                frame_dec := s.core.frame_dec.set 0 fd0',
                                trail_end := 0, propagated := 0, cur_level := 0,
                                unflushed := 0#64, confl_ref := 0xFFFFFFFF#64, confl_type := 0#64,
                                cur_vars := ncv.toNat, unassigned := ncv }
          scratch := sc' }
      FullCfgCompat c c' → c'.mv ≤ ncv.toNat → (ncv.toNat < c.mv → c'.mv = ncv.toNat) →
      s'.LengthsOk c' → ft0' = 0#32 →
      (∀ l < 2 * c'.max_vars, l < 2 * old_cv.toNat → vals'[l]? = some 0#8) →
      FullExtScratchPres s s' →
      sc'.work_stk1 = s.scratch.work_stk1 → sc'.work_stk2 = s.scratch.work_stk2 →
      ((∀ nv < ncv.toNat, nv ≤ (s.scratch.work_stk2[nv]?.getD 0#32).toNat) →
        (∀ nv < ncv.toNat, fl'[nv]? = s.core.flags[(s.scratch.work_stk2[nv]?.getD 0#32).toNat]?) ∧
        (∀ v, ncv.toNat ≤ v → v < old_cv.toNat → fl'[v]? = some 0#32)) →
      (FullMem c' s' ⋆ R) m' → Q () m') :
    Func.wp Γ full_compact_vars_m7fix_body (c.hdr, old_cv, ncv, ()) m Q X := by
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hcv_le := hlen.core_ok.cur_vars_le
  have hcv2_lt64 : 2 * old_cv.toNat < 2 ^ 64 := by unfold dimacsBound at hmax_lt; omega
  have hcv_lt64 : old_cv.toNat < 2 ^ 64 := by omega
  have hncv_lt64 : ncv.toNat < 2 ^ 64 := by omega
  have hv_len := hlen.core_ok.vals_len
  have hfl_len := hlen.core_ok.flags_len
  have hlv_len := hlen.core_ok.lvl_len
  have hrs_len := hlen.core_ok.rsns_len
  have hft_len := hlen.core_ok.frame_trail_len
  have hfd_len := hlen.core_ok.frame_dec_len
  have hph_len := hlen.scratch_ok.phases_len
  have hpt_len := hlen.scratch_ok.phases_target_len
  have hpb_len := hlen.scratch_ok.phases_best_len
  have hwb_len := hlen.scratch_ok.walk_best_len
  have hsc_len := hlen.scratch_ok.score_len
  have hqs_len := hlen.scratch_ok.q_stamp_len
  have hqp_len := hlen.scratch_ok.q_prev_len
  have hqn_len := hlen.scratch_ok.q_next_len
  have hps_len := hlen.scratch_ok.pos_len
  have hws2_len := hlen.scratch_ok.work_stk2_len
  have hnlits_eq : (old_cv <<< (1 : Nat)).toNat = 2 * old_cv.toNat := bv64_shl1_toNat (by omega)
  unfold Func.wp full_compact_vars_m7fix_body
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (l, ()) m1 =>
      l.toNat ≤ 2 * old_cv.toNat ∧
      ∃ vals1 : List (BitVec 8), vals1.length = 2 * c.max_vars ∧
        (∀ i < l.toNat, vals1[i]? = some 0#8) ∧
        (FullMem c { s with core := { s.core with vals := vals1 } } ⋆ R) m1)
    (fun (l, ()) _ => 2 * old_cv.toNat - l.toNat)
    (fun J1 hLoop1 => by
      c0_hsteps
      exact hLoop1 (0#64, ()) m ⟨Nat.zero_le _, s.core.vals, hv_len, fun _ h => by simp at h, hm⟩)
    (fun J1 ⟨l, ⟨⟩⟩ m1 ⟨hl_le, vals1, hvl1, hz1, hm1⟩ hLoop1 => ?_)
  c0_hsplit
  · have hl_lt : l.toNat < 2 * old_cv.toNat := by
      have h1 : l.toNat < (old_cv <<< (1 : Nat)).toNat := hc
      rwa [hnlits_eq] at h1
    have hl1_eq : (l + 1#64).toNat = l.toNat + 1 :=
      bv64_add1 (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hl_lt) hcv2_lt64)
    have hl_vals : l.toNat < vals1.length :=
      hvl1 ▸ Nat.lt_of_lt_of_le hl_lt (Nat.mul_le_mul_left 2 (hold ▸ hcv_le))
    c0_hsteps
    refine hLoop1 (l + 1#64, ()) m
      (by dsimp only; rw [hl1_eq]; exact Nat.sub_lt_sub_left hl_lt (Nat.lt_succ_self _))
      ⟨by rw [hl1_eq]; exact Nat.succ_le_of_lt hl_lt, vals1.set l.toNat 0#8,
       by rw [List.length_set, hvl1], fun i hi => ?_, hm⟩
    rw [hl1_eq] at hi
    by_cases hil : i = l.toNat
    · subst hil; exact List.getElem?_set_self hl_vals
    · rw [List.getElem?_set_ne (Ne.symm hil)]
      exact hz1 i (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hi) hil)
  · clear hLoop1 J1
    have hl_eq : l.toNat = 2 * old_cv.toNat := by
      have h1 : ¬ l.toNat < (old_cv <<< (1 : Nat)).toNat := hc
      rw [hnlits_eq] at h1; exact Nat.le_antisymm hl_le (Nat.le_of_not_lt h1)
    rw [hl_eq] at hz1
    c0_hsteps_nogrp
    refine wp_loop_inv
      (fun (tgt_asg, bst_asg, nv, ()) m2 =>
        nv.toNat ≤ ncv.toNat ∧
        ∃ fl2 lvl2 rsns2 : List (BitVec 32),
          fl2.length = c.max_vars ∧ lvl2.length = c.max_vars ∧ rsns2.length = c.max_vars ∧
          M7FixFlPres s ncv nv.toNat fl2 ∧
          ∃ ph2 pt2 pb2 wb2 : List (BitVec 8),
            ph2.length = c.max_vars ∧ pt2.length = c.max_vars ∧
            pb2.length = c.max_vars ∧ wb2.length = c.max_vars ∧
            ∃ sc2 : List (BitVec 64), sc2.length = c.max_vars ∧
              ∃ qs2 : List (BitVec 32), qs2.length = c.max_vars ∧
                (FullMem c {
                  core := { s.core with vals := vals1, flags := fl2, lvl := lvl2, rsns := rsns2 }
                  scratch := { s.scratch with phases := ph2, phases_target := pt2,
                                                phases_best := pb2, walk_best := wb2,
                                                score := sc2, q_stamp := qs2 } } ⋆ R) m2)
      (fun (_, _, nv, ()) _ => ncv.toNat - nv.toNat)
      (fun J2 hLoop2 => by
        c0_hsteps
        exact hLoop2 (0#64, 0#64, 0#64, ()) m1 ⟨Nat.zero_le _, s.core.flags, s.core.lvl,
          s.core.rsns, hfl_len, hlv_len, hrs_len,
          (fun _ => ⟨(fun _ h => by cases h), fun _ _ => rfl⟩),
          s.scratch.phases, s.scratch.phases_target, s.scratch.phases_best, s.scratch.walk_best,
          hph_len, hpt_len, hpb_len, hwb_len, s.scratch.score, hsc_len, s.scratch.q_stamp,
          hqs_len, hm1⟩)
      (fun J2 ⟨tgt_asg, bst_asg, nv, ⟨⟩⟩ m2 ⟨hnv_le2, fl2, lvl2, rsns2, hfl2, hlv2, hrs2, hflp2,
          ph2, pt2, pb2, wb2, hph2, hpt2, hpb2, hwb2, sc2, hsc2, qs2, hqs2, hm2⟩ hLoop2 => ?_)
    c0_hsplit
    · clear hm1
      have hnv_lt : nv.toNat < ncv.toNat := hc
      have hnv_cm : nv.toNat < c.max_vars :=
        Nat.lt_of_lt_of_le hnv_lt (Nat.le_trans hncv_le (hold ▸ hcv_le))
      have hnv_ws2 : nv.toNat < s.scratch.work_stk2.length := hws2_len ▸
        Nat.lt_of_lt_of_le hnv_cm (Nat.le_mul_of_pos_left _ Nat.zero_lt_two)
      have hov_lt : (s.scratch.work_stk2[nv.toNat]'hnv_ws2).toNat < old_cv.toNat := by
        simpa [List.getElem?_eq_getElem hnv_ws2] using hinv_ok nv.toNat hnv_lt
      have hov64_lt : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat <
          old_cv.toNat := by rw [zext_toNat _ (by decide)]; exact hov_lt
      have hov_cm : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat <
          c.max_vars := Nat.lt_of_lt_of_le hov64_lt (hold ▸ hcv_le)
      have hnv_fl2 : nv.toNat < fl2.length := hfl2 ▸ hnv_cm
      have hov_fl2 : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat <
          fl2.length := hfl2 ▸ hov_cm
      have hnv_ph2 : nv.toNat < ph2.length := hph2 ▸ hnv_cm
      have hov_ph2 : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat <
          ph2.length := hph2 ▸ hov_cm
      have hnv_pt2 : nv.toNat < pt2.length := hpt2 ▸ hnv_cm
      have hov_pt2 : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat <
          pt2.length := hpt2 ▸ hov_cm
      have hnv_pb2 : nv.toNat < pb2.length := hpb2 ▸ hnv_cm
      have hov_pb2 : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat <
          pb2.length := hpb2 ▸ hov_cm
      have hnv_wb2 : nv.toNat < wb2.length := hwb2 ▸ hnv_cm
      have hov_wb2 : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat <
          wb2.length := hwb2 ▸ hov_cm
      have hnv_sc2 : nv.toNat < sc2.length := hsc2 ▸ hnv_cm
      have hov_sc2 : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat <
          sc2.length := hsc2 ▸ hov_cm
      have hnv_qs2 : nv.toNat < qs2.length := hqs2 ▸ hnv_cm
      have hov_qs2 : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat <
          qs2.length := hqs2 ▸ hov_cm
      have hnv_lv2 : nv.toNat < lvl2.length := hlv2 ▸ hnv_cm
      have hnv_rs2 : nv.toNat < rsns2.length := hrs2 ▸ hnv_cm
      have hnv1_eq : (nv + 1#64).toNat = nv.toNat + 1 :=
        bv64_add1 (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hnv_lt) hncv_lt64)
      have hflp2' : M7FixFlPres s ncv (nv.toNat + 1) (fl2.set nv.toNat
          (fl2[((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat]'hov_fl2)) := by
        intro hord
        have ⟨hpre, hpost⟩ := hflp2 hord
        have hself : nv.toNat ≤ (s.scratch.work_stk2[nv.toNat]?.getD 0#32).toNat :=
          hord nv.toNat hnv_lt
        have hov_eq : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat =
            (s.scratch.work_stk2[nv.toNat]?.getD 0#32).toNat := by
          rw [zext_toNat _ (by decide), List.getElem?_eq_getElem hnv_ws2, Option.getD_some]
        have hfl_ov := hpost _ (hov_eq ▸ hself)
        constructor
        · intro k hk
          by_cases hkn : k = nv.toNat
          · subst hkn
            rw [List.getElem?_set_self hnv_fl2, ← hov_eq, ← List.getElem?_eq_getElem hov_fl2]
            exact hfl_ov
          · rw [List.getElem?_set_ne (Ne.symm hkn)]
            exact hpre k (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkn)
        · intro j hj
          rw [List.getElem?_set_ne (Nat.ne_of_lt hj)]
          exact hpost j (Nat.le_trans (Nat.le_succ _) hj)
      c0_hsteps <;>
        (refine hLoop2 (_, _, nv + 1#64, ()) m
          (by dsimp only; rw [hnv1_eq]; exact Nat.sub_lt_sub_left hnv_lt (Nat.lt_succ_self _))
          ⟨by rw [hnv1_eq]; exact Nat.succ_le_of_lt hnv_lt, _, _, _,
           by rw [List.length_set]; exact hfl2, by rw [List.length_set]; exact hlv2,
           by rw [List.length_set]; exact hrs2, by rw [hnv1_eq]; exact hflp2',
           _, _, _, _, by rw [List.length_set]; exact hph2, by rw [List.length_set]; exact hpt2,
           by rw [List.length_set]; exact hpb2, by rw [List.length_set]; exact hwb2,
           _, by rw [List.length_set]; exact hsc2, _, by rw [List.length_set]; exact hqs2, hm⟩)
    · clear hLoop2 J2 hm1
      have hnv_eq : nv.toNat = ncv.toNat :=
        Nat.le_antisymm hnv_le2 (Nat.le_of_not_lt hc)
      rw [hnv_eq] at hflp2
      c0_hsteps_nogrp
      refine wp_loop_inv
        (fun (v, ()) m3 =>
          ncv.toNat ≤ v.toNat ∧ v.toNat ≤ old_cv.toNat ∧
          ∃ fl3 lvl3 rsns3 qp3 qn3 qs3 ps3 : List (BitVec 32),
            fl3.length = c.max_vars ∧ lvl3.length = c.max_vars ∧ rsns3.length = c.max_vars ∧
            qp3.length = c.max_vars ∧ qn3.length = c.max_vars ∧ qs3.length = c.max_vars ∧
            ps3.length = c.max_vars ∧ M7FixFlPres3 s ncv fl3 v.toNat ∧
            ∃ sc3 : List (BitVec 64), sc3.length = c.max_vars ∧
              (FullMem c {
                core := { s.core with vals := vals1, flags := fl3, lvl := lvl3, rsns := rsns3 }
                scratch := { s.scratch with phases := ph2, phases_target := pt2,
                                              phases_best := pb2, walk_best := wb2,
                                              score := sc3, q_stamp := qs3, q_prev := qp3,
                                              q_next := qn3, pos := ps3 } } ⋆ R) m3)
        (fun (v, ()) _ => old_cv.toNat - v.toNat)
        (fun J3 hLoop3 => by
          c0_hsteps
          exact hLoop3 (ncv, ()) m2 ⟨Nat.le_refl _, hncv_le, fl2, lvl2, rsns2, s.scratch.q_prev,
            s.scratch.q_next, qs2, s.scratch.pos, hfl2, hlv2, hrs2, hqp_len, hqn_len, hqs2,
            hps_len, ⟨(fun hord => (hflp2 hord).1), fun _ h1 h2 =>
              absurd h2 (Nat.not_lt_of_ge h1)⟩, sc2, hsc2, hm2⟩)
        (fun J3 ⟨v, ⟨⟩⟩ m3 ⟨hnv_v, hv_le3, fl3, lvl3, rsns3, qp3, qn3, qs3, ps3,
            hfl3, hlv3, hrs3, hqp3, hqn3, hqs3, hps3, hflp3, sc3, hsc3, hm3⟩ hLoop3 => ?_)
      c0_hsplit
      · clear hm2
        have hv_lt : v.toNat < old_cv.toNat := hc
        have hv_cm : v.toNat < c.max_vars := Nat.lt_of_lt_of_le hv_lt (hold ▸ hcv_le)
        have hv_fl3 : v.toNat < fl3.length := hfl3 ▸ hv_cm
        have hv_lv3 : v.toNat < lvl3.length := hlv3 ▸ hv_cm
        have hv_rs3 : v.toNat < rsns3.length := hrs3 ▸ hv_cm
        have hv_sc3 : v.toNat < sc3.length := hsc3 ▸ hv_cm
        have hv_qs3 : v.toNat < qs3.length := hqs3 ▸ hv_cm
        have hv_qp3 : v.toNat < qp3.length := hqp3 ▸ hv_cm
        have hv_qn3 : v.toNat < qn3.length := hqn3 ▸ hv_cm
        have hv_ps3 : v.toNat < ps3.length := hps3 ▸ hv_cm
        have hv1_eq : (v + 1#64).toNat = v.toNat + 1 :=
          bv64_add1 (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hv_lt) hcv_lt64)
        have hflp3' : M7FixFlPres3 s ncv (fl3.set v.toNat 0#32) (v.toNat + 1) := by
          constructor
          · intro hord k hk
            rw [List.getElem?_set_ne (Nat.ne_of_gt (Nat.lt_of_lt_of_le hk hnv_v))]
            exact hflp3.1 hord k hk
          · intro u hu1 hu2
            by_cases huv : u = v.toNat
            · subst huv; exact List.getElem?_set_self hv_fl3
            · rw [List.getElem?_set_ne (Ne.symm huv)]
              exact hflp3.2 u hu1 (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hu2) huv)
        c0_hsteps
        exact hLoop3 (v + 1#64, ()) m
          (by dsimp only; rw [hv1_eq]; exact Nat.sub_lt_sub_left hv_lt (Nat.lt_succ_self _))
          ⟨by rw [hv1_eq]; exact Nat.le_trans hnv_v (Nat.le_succ _),
           by rw [hv1_eq]; exact Nat.succ_le_of_lt hv_lt, _, _, _, _, _, _, _,
           by rw [List.length_set]; exact hfl3, by rw [List.length_set]; exact hlv3,
           by rw [List.length_set]; exact hrs3, by rw [List.length_set]; exact hqp3,
           by rw [List.length_set]; exact hqn3, by rw [List.length_set]; exact hqs3,
           by rw [List.length_set]; exact hps3, by rw [hv1_eq]; exact hflp3',
           _, by rw [List.length_set]; exact hsc3, hm⟩
      · have hv_eq : v.toNat = old_cv.toNat :=
          Nat.le_antisymm hv_le3 (Nat.le_of_not_lt hc)
        rw [hv_eq] at hflp3
        have hft0 : 0 < s.core.frame_trail.length := by rw [hft_len]; exact Nat.zero_lt_succ _
        have hfd0 : 0 < s.core.frame_dec.length := by rw [hfd_len]; exact Nat.zero_lt_succ _
        clear hLoop3 J3 hm2 hinv_ok hws2_len hncv_lt64 hfl_len hlv_len hrs_len hph_len hpt_len
          hpb_len hwb_len hsc_len hqs_len hqp_len hqn_len hps_len hmax_lt hcv2_lt64 hcv_lt64 hv_len
        have hc_mv_lt : c.mv < 2 ^ 64 := Nat.lt_trans c.hmv (by unfold dimacsBound; decide)
        have hmax_lt64 : c.max_vars < 2 ^ 64 := Nat.lt_trans c.hmaxv (by unfold dimacsBound; decide)
        have hmv_lt_max : ncv.toNat ≤ c.max_vars := Nat.le_trans hncv_le (hold ▸ hcv_le)
        have hncv_bv : ncv = BitVec.ofNat 64 ncv.toNat := (@bv_ofNat_toNat_eq 64 ncv).symm
        have hsub_bv : BitVec.ofNat 64 c.max_vars - ncv =
            BitVec.ofNat 64 (c.max_vars - ncv.toNat) :=
          (congrArg (BitVec.ofNat 64 c.max_vars - ·) hncv_bv).trans
            (bv_sub_ofNat hmv_lt_max hmax_lt64)
        let sc_final : FullScratch :=
          { s.scratch with
            phases := ph2, phases_target := pt2, phases_best := pb2, walk_best := wb2,
            score := sc3, q_stamp := qs3, q_prev := qp3, q_next := qn3, pos := ps3,
            target_assigned := tgt_asg, best_assigned := bst_asg }
        let s_final : FullState :=
          { core := { s.core with
              vals := vals1, flags := fl3, lvl := lvl3, rsns := rsns3,
              frame_trail := s.core.frame_trail.set 0 0#32,
              frame_dec := s.core.frame_dec.set 0 0xFFFFFFFF#32,
              trail_end := 0, propagated := 0, cur_level := 0,
              unflushed := 0#64, confl_ref := 0xFFFFFFFF#64, confl_type := 0#64,
              cur_vars := ncv.toNat, unassigned := ncv }
            scratch := sc_final }
        c0_hsteps_nogrp
        refine wp_join_group
          (fun () mJ =>
            ∃ c' : FullCfg, FullCfgCompat c c' ∧ c'.mv ≤ ncv.toNat ∧
              (ncv.toNat < c.mv → c'.mv = ncv.toNat) ∧ (FullMem c' s_final ⋆ R) mJ)
          (fun _ ⟨⟩ mJ ⟨c', hcompat', hcv_ge', hmv_eq', hmJ⟩ => by
            c0_hsteps
            exact hQ c' vals1 fl3 lvl3 rsns3 0#32 0xFFFFFFFF#32 sc_final mJ hcompat' hcv_ge'
              hmv_eq' (full_compact_vars_m7fix_lengths hlen hcompat' hcv_ge' hmv_lt_max hvl1 hfl3
                hlv3 hrs3 hph2 hpt2 hpb2 hwb2 hsc3 hqs3 hqp3 hqn3 hps3)
              rfl (fun l _ hl => hz1 l hl) ⟨rfl, rfl⟩ rfl rfl
              (fun hord => ⟨hflp3.1 hord, hflp3.2⟩) hmJ)
          (fun Jmv hJmv => ?_)
        c0_hsplit
        · have hlt_mv : ncv.toNat < c.mv := by
            have h1 : ncv.toNat < (BitVec.ofNat 64 c.mv).toNat := hc
            rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc_mv_lt] at h1
          let c' := fullCfgShrinkMv c ncv.toNat (Nat.le_of_lt hlt_mv)
          refine wp_store_sep (full_store_mv_mid ncv hm) ?_
          intro m4 hm4
          c0_hsteps_nogrp
          refine wp_load_of (full_load_max_vars_mid hm4) ?_
          have hm4' : (FullMemShrinkMid c (BitVec.ofNat 64 ncv.toNat) _ ⋆ R) m4 :=
            (show ∀ {x : BitVec 64},
                ncv = x → (FullMemShrinkMid c x _ ⋆ R) m4 from fun h => h ▸ hm4)
              hncv_bv
          c0_hsteps_nogrp
          refine wp_store_sep (by
            rw [hsub_bv]; exact full_store_bva_mid (Nat.le_of_lt hlt_mv) hm4') ?_
          intro m5 hm5
          c0_hsteps
          exact hJmv () m5 ⟨c', FullCfgCompat.shrinkMv c ncv.toNat (Nat.le_of_lt hlt_mv),
            Nat.le_refl _, fun _ => rfl, compactMem_cast hm5 (by
              dsimp only [s_final, sc_final]; simp only [← hncv_bv]; rfl)⟩
        · have hge_mv : c.mv ≤ ncv.toNat := by
            have h1 : ¬ ncv.toNat < (BitVec.ofNat 64 c.mv).toNat := hc
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc_mv_lt] at h1
            exact Nat.le_of_not_lt h1
          c0_hsteps
          exact hJmv () m ⟨c, FullCfgCompat.refl c, hge_mv,
            fun h => absurd h (Nat.not_lt_of_ge hge_mv),
            compactMem_cast hm (by dsimp only [s_final, sc_final]; rfl)⟩

/-- Drop-in `Func.wp` proof for `full_compact_vars_m7fix` against `fullCompactVarsSpec`. -/
theorem full_compact_vars_m7fix_wp (Γ : Env) :
    ∀ a m Q X, fullCompactVarsSpec a m Q X →
      Func.wp Γ full_compact_vars_m7fix_body a m Q X := by
  rintro ⟨h, old_cv, ncv, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hold, hncv_le, hinv_ok, hm, hQ⟩
  exact full_compact_vars_m7fix_flags_wp Γ hlen hold hncv_le hinv_ok hm
    (fun c' vals' fl' lvl' rsns' ft0' fd0' sc' m' hc' _ _ hl' hft hval hex hw1 hw2 _ hm' =>
      hQ c' vals' fl' lvl' rsns' ft0' fd0' sc' m' hc' hl' hft hval hex hw1 hw2 hm')

end CompactVarsProof

/-! ## 3b. `full_sweep_copy_m7fix` (`PH_RED` Zombie Drop & `fullSweepCopySpec`) -/

section SweepCopyProof

private theorem m7scRedBinOnlySlice_get {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : FullReduceSpecs.BinOnlyWatchSliceOk F_cur k lit p rem) :
    ∀ i < rem, let w := k.wstk[p + i]?.getD 0#32
      (w &&& 0x80000000#32) ≠ 0#32 ∧ (w &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w &&& 0x7FFFFFFF#32).toNat]) := by
  induction h with
  | empty => intro i hi; omega
  | bin hw hmsb _ hlt hent _ ih =>
    intro i hi; cases i with
    | zero => simpa [hw] using ⟨hmsb, hlt, hent⟩
    | succ j => simpa [Nat.add_assoc, Nat.add_comm 1 j] using ih j (by omega)

private theorem m7scRedBinOnlySlice_of_all {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c) {lit p rem : Nat} (hbd : p + rem ≤ k.wstk.length)
    (hall : ∀ i < rem, let w := k.wstk[p + i]?.getD 0#32
      (w &&& 0x80000000#32) ≠ 0#32 ∧ (w &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w &&& 0x7FFFFFFF#32).toNat])) :
    FullReduceSpecs.BinOnlyWatchSliceOk F_cur k lit p rem := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx; have hcv := hlen.cur_vars_le
  induction rem generalizing p with
  | zero => exact .empty
  | succ r ih =>
    have hp_lt : p < k.wstk.length := by omega
    have h0 := hall 0 (Nat.zero_lt_succ r)
    rw [Nat.add_zero, List.getElem?_eq_getElem hp_lt, Option.getD_some] at h0
    have hne : k.wstk[p]'hp_lt ≠ 0xFFFFFFFF#32 := by
      intro heq; have h2 := h0.2.1; rw [heq] at h2
      have hm : (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 := by decide
      rw [hm] at h2; omega
    refine .bin (List.getElem?_eq_getElem hp_lt) h0.1 hne h0.2.1 h0.2.2
      (ih (by omega) fun j hj => ?_)
    simpa [Nat.add_assoc, Nat.add_comm 1 j] using hall (j + 1) (by omega)

private theorem m7scRedBinOnly_to_full {F_cur : List (List Nat)} {k : FullCoreState}
    (h : FullReduceSpecs.BinOnlyWatchesInv F_cur k) : FullBinOnlyWatchesInv F_cur k :=
  ⟨h.layout, fun l hl => m7scRedBinOnlySlice_get (h.slices l hl)⟩

private theorem m7scFullBinOnly_to_red {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (hlen : k.LengthsOk c) (h : FullBinOnlyWatchesInv F_cur k) :
    FullReduceSpecs.BinOnlyWatchesInv F_cur k :=
  ⟨h.1, fun l hl => m7scRedBinOnlySlice_of_all hlen
    (by have := h.1.bounds l hl; have := hlen.wlen_le; have := hlen.wstk_len_arr; omega)
    (h.2 l hl)⟩

private theorem m7sc_witness_with_ar {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {dst : Nat} {ar' : List (BitVec 32)}
    (har_len : s.core.arena.length = c.arena_cap) (hdst_le : dst ≤ c.arena_cap)
    (hcl0 : s.core.cur_level = 0)
    (hw_dst : FullWitnessInv c F0 F_cur { s.core with arena_len := dst })
    (har' : ar'.length = c.arena_cap) (hpre : PrefixAgrees dst s.core.arena ar') :
    FullWitnessInv c F0 F_cur { s.core with arena := ar', arena_len := dst } := by
  let k0 : FullCoreState := { s.core with arena_len := dst }
  let k1 : FullCoreState := { s.core with arena := ar', arena_len := dst }
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore k0,
      fullArenaNextOff k1.arena k0.arena_len r = fullArenaNextOff k0.arena k0.arena_len r :=
    fun r hr => hw_dst.arena.arenaNextOff_extend (Nat.le_refl _) (fun i hi => hpre i hi) r hr
  have hrefs : fullArenaClauseRefsCore k1 = fullArenaClauseRefsCore k0 :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hmeta : ∀ r ∈ fullArenaClauseRefsCore k0,
      fullArenaHdrCore k1 r = fullArenaHdrCore k0 r ∧
      fullArenaClauseSizeCore k1 r = fullArenaClauseSizeCore k0 r ∧
      fullArenaClauseGarbCore k1 r = fullArenaClauseGarbCore k0 r ∧
      fullArenaClauseLitsCore k1 r = fullArenaClauseLitsCore k0 r := fun r hr => by
    have hwf := hw_dst.arena.refs_wf r hr
    have h1 : r + 3 + fullArenaClauseSizeCore k0 r ≤ fullArenaNextOff k0.arena dst r := hwf.2.2.1
    have h3 : fullArenaNextOff k0.arena dst r ≤ dst := hwf.2.2.2.1
    have hk0_len : k0.arena.length = c.arena_cap := har_len
    have hk1_len : k1.arena.length = c.arena_cap := har'
    have h0 := hpre r (by omega); have h2 := hpre (r + 2) (by omega)
    have hsz : fullArenaClauseSizeCore k1 r = fullArenaClauseSizeCore k0 r := by
      unfold fullArenaClauseSizeCore k1 k0; rw [h2]
    refine ⟨by unfold fullArenaHdrCore k1 k0; rw [h0], hsz,
      by unfold fullArenaClauseGarbCore fullArenaHdrCore k1 k0; rw [h0],
      fullArenaClauseLitsCore_eq_of_hold (by omega) (by omega) hsz
        fun j hj => hpre (r + 3 + j) (by omega)⟩
  have harena1 : FullArenaClausesInv c F_cur k1 := by
    refine ⟨hw_dst.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have h := hw_dst.arena.refs_wf r hr
      dsimp only [k1, k0] at hnxt h ⊢; rw [hnxt r hr, (hmeta r hr).2.1]; exact h
    · intro r hr hsh; rw [hrefs] at hr; rw [(hmeta r hr).1] at hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := hw_dst.arena.shrk_term r hr hsh
      dsimp only [k0] at ht2
      exact ⟨t, by rw [(hmeta r hr).2.1]; exact ht1, ht2,
        by dsimp only [k1]; rw [hpre t ht2]; exact hsent⟩
    · intro r hr hng l hl; rw [hrefs] at hr
      rw [(hmeta r hr).2.2.1] at hng; rw [(hmeta r hr).2.2.2] at hl
      exact hw_dst.arena.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      rw [(hmeta r hr).2.2.1] at hng; rw [(hmeta r hr).2.2.2]
      exact hw_dst.arena.entails r hr hng
  exact { hw_dst with
    arena := harena1
    watches := hw_dst.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
    reason_inv := fun idx hidx hne => absurd (hw_dst.level0_rsn_none idx hidx
      (by have := hw_dst.lvl_le idx hidx; change _ ≤ s.core.cur_level at this; omega)) hne
    reason_lit_mem := fun idx hidx hne => absurd (hw_dst.level0_rsn_none idx hidx
      (by have := hw_dst.lvl_le idx hidx; change _ ≤ s.core.cur_level at this; omega)) hne }

private theorem m7sc_witness_with_binWatches {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} {arL wvec' wstk' : List (BitVec 32)}
    {dst wlen' : Nat} {wu' nb' oom' : BitVec 64}
    (hw : FullWitnessInv c F0 F_cur { k with arena := arL, arena_len := dst })
    (hbin : FullReduceSpecs.BinOnlyWatchesInv F_cur
      { k with arena := arL, wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
               num_binary := nb', oom := oom' }) :
    FullWitnessInv c F0 F_cur
      { k with arena := arL, arena_len := dst, wvec := wvec', wstk := wstk', wlen := wlen',
               wusable := wu', num_binary := nb', oom := oom' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := (hbin.with_core
      (k' := { k with arena := arL, arena_len := dst, wvec := wvec', wstk := wstk',
                      wlen := wlen', wusable := wu', num_binary := nb', oom := oom' })
      rfl rfl rfl rfl).toModeWatchesInv }

private theorem m7sc_new1_prep {F_cur : List (List Nat)} {arL : List (BitVec 32)}
    {dst : BitVec 64} {cur_vars : Nat}
    (hd3_eq : (dst + (3 : BitVec 64)).toNat = dst.toNat + 3)
    (hd3_lt : (dst + (3 : BitVec 64)).toNat < arL.length)
    (hlt0 : (arL[dst.toNat + 3 + 0]?.getD 0#32).toNat < 2 * cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (((arL.drop (dst.toNat + 3)).take 1).map BitVec.toNat))) :
    let ulit := arL[(dst + (3 : BitVec 64)).toNat]'hd3_lt
    ulit = arL[dst.toNat + 3]'(by omega) ∧ ulit.toNat < 2 * cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [ulit.toNat]) := by
  intro ulit
  have hulit_eq : ulit = arL[dst.toNat + 3]'(by omega) := by dsimp only [ulit]; simp only [hd3_eq]
  refine ⟨hulit_eq, ?_, ?_⟩
  · rw [Nat.add_zero, List.getElem?_eq_getElem (by omega : dst.toNat + 3 < arL.length),
      Option.getD_some, ← hulit_eq] at hlt0; exact hlt0
  · rw [show (1 : Nat) = 0 + 1 from rfl,
      FullReduceHelpers.drop_take_succ (by omega : dst.toNat + 3 + 0 < arL.length)] at hent
    simpa [hulit_eq] using hent

private theorem m7sc_new2_prep {F_cur : List (List Nat)} {arL : List (BitVec 32)}
    {dst : BitVec 64} {cur_vars : Nat} (hcv_lt : cur_vars < 2 * 2 ^ 28)
    (hd3_eq : (dst + (3 : BitVec 64)).toNat = dst.toNat + 3)
    (hd4_eq : (dst + (4 : BitVec 64)).toNat = dst.toNat + 4)
    (hd3_lt : (dst + (3 : BitVec 64)).toNat < arL.length)
    (hd4_lt : (dst + (4 : BitVec 64)).toNat < arL.length)
    (hlt0 : (arL[dst.toNat + 3 + 0]?.getD 0#32).toNat < 2 * cur_vars)
    (hlt1 : (arL[dst.toNat + 3 + 1]?.getD 0#32).toNat < 2 * cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (((arL.drop (dst.toNat + 3)).take 2).map BitVec.toNat))) :
    let l0 := arL[(dst + (3 : BitVec 64)).toNat]'hd3_lt
    let l1 := arL[(dst + (4 : BitVec 64)).toNat]'hd4_lt
    l0.toNat < 2 * cur_vars ∧ l1.toNat < 2 * cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l0.toNat, l1.toNat]) ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l1.toNat, l0.toNat]) ∧
    l0.toNat < 0x7FFFFFFF ∧ l1.toNat < 0x7FFFFFFF := by
  intro l0 l1
  have hl0_eq : l0 = arL[dst.toNat + 3]'(by omega) := by dsimp only [l0]; simp only [hd3_eq]
  have hl1_eq : l1 = arL[dst.toNat + 4]'(by omega) := by dsimp only [l1]; simp only [hd4_eq]
  have hl0_lt : l0.toNat < 2 * cur_vars := by
    rw [Nat.add_zero, List.getElem?_eq_getElem (by omega : dst.toNat + 3 < arL.length),
      Option.getD_some, ← hl0_eq] at hlt0; exact hlt0
  have hl1_lt : l1.toNat < 2 * cur_vars := by
    rw [show dst.toNat + 3 + 1 = dst.toNat + 4 by omega,
      List.getElem?_eq_getElem (by omega : dst.toNat + 4 < arL.length),
      Option.getD_some, ← hl1_eq] at hlt1; exact hlt1
  have hent_01 : (cnfOfClauses F_cur).EntailsClause (cnfClause [l0.toNat, l1.toNat]) := by
    have htk : (arL.drop (dst.toNat + 3)).take 2 = [l0, l1] := by
      apply List.ext_getElem (by simp; omega)
      intro j hj1 _; have hj : j < 2 := by simp at hj1; omega
      simp only [List.getElem_take, List.getElem_drop]
      match j, hj with
      | 0, _ => simp [hl0_eq]
      | 1, _ => simp [hl1_eq, show dst.toNat + 3 + 1 = dst.toNat + 4 by omega]
    rw [htk] at hent; simpa using hent
  have hent_10 : (cnfOfClauses F_cur).EntailsClause (cnfClause [l1.toNat, l0.toNat]) :=
    entails_of_mem_or_false hent_01 fun q hq =>
      Or.inl (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
                 rcases hq with rfl | rfl <;> simp)
  exact ⟨hl0_lt, hl1_lt, hent_01, hent_10, by omega, by omega⟩

private theorem m7sc_keep_inv {c : FullCfg} {s : FullState} {src dst : BitVec 64}
    {new_sz i : BitVec 32} {arL : List (BitVec 32)} {lit : BitVec 32}
    (harL : arL.length = c.arena_cap)
    (hdst_idx : (dst + (3 : BitVec 64) + new_sz.setWidth 64).toNat = dst.toNat + 3 + new_sz.toNat)
    (hdst_lt : (dst + (3 : BitVec 64) + new_sz.setWidth 64).toNat < arL.length)
    (hnsz1_eq : (new_sz + (1 : BitVec 32)).toNat = new_sz.toNat + 1)
    (hlit_cv : lit.toNat < 2 * s.core.cur_vars)
    (houtL : OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + new_sz.toNat) s.core.arena arL)
    (hltL : ∀ j < new_sz.toNat, (arL[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hsubL : List.Sublist (((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat)
      (((s.core.arena.drop (src.toNat + 3)).take i.toNat).map BitVec.toNat))
    (hdropL : ∀ l ∈ ((s.core.arena.drop (src.toNat + 3)).take i.toNat).map BitVec.toNat,
      l ∈ ((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat ∨
        (l < 2 * s.core.cur_vars ∧ (s.core.lvl[l / 2]?.getD 0#32).toNat = 0 ∧
          s.core.vals[l]?.getD 0#8 = 0xFF#8))
    (horig_succ : ((s.core.arena.drop (src.toNat + 3)).take (i.toNat + 1)).map BitVec.toNat =
      ((s.core.arena.drop (src.toNat + 3)).take i.toNat).map BitVec.toNat ++ [lit.toNat]) :
    let ar' := arL.set (dst + (3 : BitVec 64) + new_sz.setWidth 64).toNat lit
    ar'.length = c.arena_cap ∧
    OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + (new_sz + (1 : BitVec 32)).toNat)
      s.core.arena ar' ∧
    (∀ j < (new_sz + (1 : BitVec 32)).toNat,
      (ar'[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    List.Sublist (((ar'.drop (dst.toNat + 3)).take (new_sz + (1 : BitVec 32)).toNat).map
      BitVec.toNat) (((s.core.arena.drop (src.toNat + 3)).take (i.toNat + 1)).map BitVec.toNat) ∧
    (∀ l ∈ ((s.core.arena.drop (src.toNat + 3)).take (i.toNat + 1)).map BitVec.toNat,
      l ∈ ((ar'.drop (dst.toNat + 3)).take (new_sz + (1 : BitVec 32)).toNat).map BitVec.toNat ∨
        (l < 2 * s.core.cur_vars ∧ (s.core.lvl[l / 2]?.getD 0#32).toNat = 0 ∧
          s.core.vals[l]?.getD 0#8 = 0xFF#8)) := by
  intro ar'
  have hkept_succ :
      ((ar'.drop (dst.toNat + 3)).take (new_sz.toNat + 1)).map BitVec.toNat =
      ((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat ++ [lit.toNat] := by
    dsimp only [ar']
    rw [hdst_idx,
      FullReduceHelpers.drop_take_set_append (by omega : dst.toNat + 3 + new_sz.toNat < arL.length),
      List.map_append, List.map_singleton]
  refine ⟨by simp [ar', harL], ?_, ?_, ?_, ?_⟩
  · intro idx hidx; rw [hnsz1_eq] at hidx; dsimp only [ar']
    rw [List.getElem?_set_ne (by omega)]; exact houtL idx (by omega)
  · intro j hj; rw [hnsz1_eq] at hj; dsimp only [ar']
    by_cases hje : j = new_sz.toNat
    · subst hje; rw [← hdst_idx, List.getElem?_set_self hdst_lt, Option.getD_some]; exact hlit_cv
    · rw [List.getElem?_set_ne (by omega)]; exact hltL j (by omega)
  · rw [hnsz1_eq, hkept_succ, horig_succ]; exact hsubL.append (List.Sublist.refl _)
  · intro l hl; rw [horig_succ, List.mem_append, List.mem_singleton] at hl
    rw [hnsz1_eq, hkept_succ, List.mem_append, List.mem_singleton]
    rcases hl with hl | rfl
    · rcases hdropL l hl with hin | hd
      · exact Or.inl (Or.inl hin)
      · exact Or.inr hd
    · exact Or.inl (Or.inr rfl)

private def M7ScNoZredPrefix (s : FullState) (src : BitVec 64) (n : Nat) : Prop :=
  (s.core.arena[src.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 →
  ∀ j < n,
    let v := (s.core.arena[src.toNat + 3 + j]?.getD 0#32).toNat / 2
    v < s.core.cur_vars → (s.core.flags[v]?.getD 0#32 &&& 1#32) ≠ 0#32

private def M7ScLoopInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
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
    M7ScNoZredPrefix s src i.toNat ∧
    (FullMem c { s with core := { s.core with arena := arL } } ⋆ R) mL

private def M7ScJoinInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
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
    M7ScNoZredPrefix s src (i.toNat + 1) ∧
    (FullMem c { s with core := { s.core with arena := ar' } } ⋆ R) m'

private def M7ScOomInv (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (arL : List (BitVec 32)) (_ : Tup Val []) (mOom : Mem 64) : Prop :=
  ∃ wvecO wstkO wlenO wuO wsO,
    let sO : FullState :=
      { core := { s.core with arena := arL, wvec := wvecO, wstk := wstkO, wlen := wlenO,
                              wusable := wuO }
        scratch := { s.scratch with wsort := wsO } }
    sO.LengthsOk c ∧ FullReduceSpecs.BinOnlyWatchesInv F_cur sO.core ∧ (FullMem c sO ⋆ R) mOom

private theorem m7sc_ret_sat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {src dst : BitVec 64} {old_sz : BitVec 32}
    {at_root : Bool} {Q : Post [i64]} {arL : List (BitVec 32)} {mL : Mem 64}
    (hlen : s.LengthsOk c) (hdst_le : dst.toNat ≤ c.arena_cap) (hsz_lt : old_sz.toNat < 2 * 2 ^ 28)
    (har_t : at_root = true) (hcl0 : s.core.cur_level = 0)
    (hw_dst : FullWitnessInv c F0 F_cur { s.core with arena_len := dst.toNat })
    (hbin0 : FullReduceSpecs.BinOnlyWatchesInv F_cur s.core)
    (hQ : FullReduceSpecs.fullSweepCopyPost c F0 F_cur s R src dst old_sz at_root Q)
    (harL : arL.length = c.arena_cap)
    (hout : OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + old_sz.toNat) s.core.arena arL)
    (hmL : (FullMem c { s with core := { s.core with arena := arL } } ⋆ R) mL) :
    Q (0xFFFFFFFF#64, ()) mL :=
  hQ 0xFFFFFFFF#64 arL s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
    s.core.trail_end s.core.unassigned s.core.unflushed s.core.wvec s.core.wstk s.core.wlen
    s.core.wusable s.core.num_binary s.core.oom s.scratch.phases s.scratch.wsort mL
    ⟨{ hlen.core_ok with arena_len_arr := harL }, hlen.scratch_ok⟩ hout
    ⟨fun hf => Bool.noConfusion (har_t.symm.trans hf),
     fun _ => ⟨m7sc_witness_with_ar (s := s) hlen.core_ok.arena_len_arr hdst_le hcl0 hw_dst
         harL (fun idx (hidx : idx < dst.toNat) => hout.getElem?_lt (by omega)),
       hbin0.with_core rfl rfl rfl rfl, Nat.le_refl _, Or.inr (Or.inr (Or.inr (Or.inl rfl))),
       (fun h => by cases h), (fun h => by cases h), (fun _ => rfl), (fun h => by cases h),
       (fun ⟨_, hle⟩ => by revert hle; simp; omega)⟩⟩ hmL

private theorem m7sc_ret_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {src dst : BitVec 64} {old_sz : BitVec 32}
    {at_root : Bool} {Q : Post [i64]} {arL : List (BitVec 32)} {mL : Mem 64}
    (hlen : s.LengthsOk c) (hdst_le : dst.toNat ≤ c.arena_cap) (hsz_lt : old_sz.toNat < 2 * 2 ^ 28)
    (har_t : at_root = true) (hcl0 : s.core.cur_level = 0)
    (hw_dst : FullWitnessInv c F0 F_cur { s.core with arena_len := dst.toNat })
    (hbin0 : FullReduceSpecs.BinOnlyWatchesInv F_cur s.core)
    (hQ : FullReduceSpecs.fullSweepCopyPost c F0 F_cur s R src dst old_sz at_root Q)
    (harL : arL.length = c.arena_cap)
    (hout : OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + old_sz.toNat) s.core.arena arL)
    (hunsat : F0.Unsat)
    (hmL : (FullMem c { s with core := { s.core with arena := arL } } ⋆ R) mL) :
    Q (0xFFFFFFFE#64, ()) mL :=
  hQ 0xFFFFFFFE#64 arL s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
    s.core.trail_end s.core.unassigned s.core.unflushed s.core.wvec s.core.wstk s.core.wlen
    s.core.wusable s.core.num_binary s.core.oom s.scratch.phases s.scratch.wsort mL
    ⟨{ hlen.core_ok with arena_len_arr := harL }, hlen.scratch_ok⟩ hout
    ⟨fun hf => Bool.noConfusion (har_t.symm.trans hf),
     fun _ => ⟨m7sc_witness_with_ar (s := s) hlen.core_ok.arena_len_arr hdst_le hcl0 hw_dst
         harL (fun idx (hidx : idx < dst.toNat) => hout.getElem?_lt (by omega)),
       hbin0.with_core rfl rfl rfl rfl, Nat.le_refl _, Or.inl rfl, (fun _ => hunsat),
       (fun h => by cases h), (fun _ => rfl), (fun h => by cases h),
       (fun ⟨_, hle⟩ => by revert hle; simp; omega)⟩⟩ hmL

/-- Generalized `Func.wp` proof for `full_sweep_copy_m7fix`: proves `fullSweepCopySpec` AND
certifies that at root level (`at_root = true`), any `PH_RED` clause referencing a `!FL_ACTIVE`
variable unconditionally returns `0xFFFFFFFF#64` (dropping the clause). -/
theorem full_sweep_copy_m7fix_no_zombie_wp (Γ : Env)
    (hassign : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hpush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {src dst : BitVec 64} {old_sz : BitVec 32}
    {at_root : Bool} {Q : Post [i64]} {X : XPost}
    (hlen : s.LengthsOk c) (hdst_src : dst.toNat ≤ src.toNat) (hsz3 : 3 ≤ old_sz.toNat)
    (hsrc_fit : src.toNat + 3 + old_sz.toNat ≤ s.core.arena_len)
    (hat_eq : at_root = decide (s.core.cur_level = 0))
    (hlits_lt : ∀ j < old_sz.toNat,
      (s.core.arena[src.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hroot_pre : at_root = true →
      FullWitnessInv c F0 F_cur { s.core with arena_len := dst.toNat } ∧
      FullBinOnlyWatchesInv F_cur s.core ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause (((s.core.arena.drop (src.toNat + 3)).take old_sz.toNat).map BitVec.toNat)))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ r arena' vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb'
      oom' ph' wsort' m',
      (at_root = true →
        (s.core.arena[src.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 →
        (∃ j < old_sz.toNat,
          let v := (s.core.arena[src.toNat + 3 + j]?.getD 0#32).toNat / 2
          v < s.core.cur_vars ∧ (s.core.flags[v]?.getD 0#32 &&& 1#32) = 0#32) →
        r = 0xFFFFFFFF#64) →
      let s' : FullState :=
        { s with
          core := { s.core with arena := arena', vals := vals', flags := flags', lvl := lvl',
                                rsns := rsns', trl := trl', trail_pos := tp', trail_end := te',
                                unassigned := unass', unflushed := unfl', wvec := wvec',
                                wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                                oom := oom' }
          scratch := { s.scratch with phases := ph', wsort := wsort' } }
      s'.LengthsOk c →
      (∀ i, (i < dst.toNat + 3 ∨ dst.toNat + 3 + old_sz.toNat ≤ i) →
        arena'[i]? = s.core.arena[i]?) →
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
        FullBinOnlyWatchesInv F_cur s'.core ∧ s.core.trail_end ≤ te' ∧
        (r = 0xFFFFFFFE#64 ∨ r = 0xFFFFFFFD#64 ∨ r = 1#64 ∨ r = 0xFFFFFFFF#64 ∨
          (3 ≤ r.toNat ∧ r.toNat ≤ old_sz.toNat)) ∧
        (r = 0xFFFFFFFE#64 → F0.Unsat) ∧ (r = 0xFFFFFFFD#64 → oom' = 1#64) ∧
        (r ≠ 0xFFFFFFFD#64 → oom' = s.core.oom) ∧ (r = 1#64 → s.core.trail_end < te') ∧
        (3 ≤ r.toNat ∧ r.toNat ≤ old_sz.toNat →
          (∀ j < r.toNat, (arena'[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
          List.Sublist (((arena'.drop (dst.toNat + 3)).take r.toNat).map BitVec.toNat)
            (((s.core.arena.drop (src.toNat + 3)).take old_sz.toNat).map BitVec.toNat) ∧
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause (((arena'.drop (dst.toNat + 3)).take r.toNat).map BitVec.toNat)))) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    Func.wp Γ full_sweep_copy_m7fix_body (c.hdr, src, dst, old_sz, at_root, ()) m Q X := by
  have hcap_lt : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hal_le := hlen.core_ok.arena_len_le
  have har_len := hlen.core_ok.arena_len_arr
  have hcv_le := hlen.core_ok.cur_vars_le
  have hv_len := hlen.core_ok.vals_len
  have hfl_len := hlen.core_ok.flags_len
  have hl_len := hlen.core_ok.lvl_len
  have hfit_cap : src.toNat + 3 + old_sz.toNat ≤ c.arena_cap := by omega
  have hdst_fit : dst.toNat + 3 + old_sz.toNat ≤ c.arena_cap := by omega
  have hsrc_lt0 : src.toNat < s.core.arena.length := by omega
  let Qsp : FullReduceSpecs.fullSweepCopyPost c F0 F_cur s R src dst old_sz at_root
      (fun (r, ()) m' =>
        ((at_root = true →
          (s.core.arena[src.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 →
          (∃ j < old_sz.toNat,
            let v := (s.core.arena[src.toNat + 3 + j]?.getD 0#32).toNat / 2
            v < s.core.cur_vars ∧ (s.core.flags[v]?.getD 0#32 &&& 1#32) = 0#32) →
          r = 0xFFFFFFFF#64)) → Q (r, ()) m') :=
    fun r arena' vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb'
      oom' ph' wsort' m' hl' ho' ⟨hf_out, ht_out⟩ hm' hz =>
      hQ r arena' vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb'
        oom' ph' wsort' m' hz hl' ho' hf_out
        (fun ht => let ⟨hw', hbo', rest⟩ := ht_out ht; ⟨hw', m7scRedBinOnly_to_full hbo', rest⟩)
        hm'
  unfold Func.wp full_sweep_copy_m7fix_body
  c0_hsteps_nogrp
  c0_hsplit
  · have har_t : at_root = true := by simpa using hc
    have hcl0 : s.core.cur_level = 0 := of_decide_eq_true (hat_eq.symm.trans har_t)
    obtain ⟨hw_dst, hfb0, hent0⟩ := hroot_pre har_t
    have hbin0 : FullReduceSpecs.BinOnlyWatchesInv F_cur s.core :=
      m7scFullBinOnly_to_red hlen.core_ok hfb0
    clear hfb0 hroot_pre hat_eq
    have hQsat : ∀ {arL mL}, arL.length = c.arena_cap →
        OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + old_sz.toNat) s.core.arena arL →
        (FullMem c { s with core := { s.core with arena := arL } } ⋆ R) mL →
        Q (0xFFFFFFFF#64, ()) mL := fun harL hout hmL =>
      m7sc_ret_sat hlen (by omega) (by omega) har_t hcl0 hw_dst hbin0 Qsp harL hout hmL
        (fun _ _ _ => rfl)
    c0_hsteps_nogrp
    refine wp_loop_inv (M7ScLoopInv c s R src dst old_sz)
      (fun (_, i, ()) _ => old_sz.toNat - i.toNat) (fun J hLoop => ?_) ?_
    · c0_hsteps
      exact hLoop (0#32, 0#32, ()) m ⟨Nat.le_refl _, Nat.zero_le _, s.core.arena, har_len,
        fun _ _ => rfl, fun _ hj => by simp at hj, by simp, fun _ hl => by simp at hl,
        (fun _ _ hj => by cases hj), hm⟩
    · rintro J ⟨new_sz, i, ⟨⟩⟩ mL ⟨hni, hi_le, arL, harL, houtL, hltL, hsubL, hdropL, hnzL, hmL⟩
        hLoop
      c0_hsplit
      · have hi_lt : i.toNat < old_sz.toNat := by c0_bound
        have hi1_eq : (i + (1 : BitVec 32)).toNat = i.toNat + 1 := bv32_add1 (by omega)
        have hnsz1_eq : (new_sz + (1 : BitVec 32)).toNat = new_sz.toNat + 1 :=
          bv32_add1 (by omega)
        have hsrc_idx : (src + (3 : BitVec 64) + i.setWidth 64).toNat = src.toNat + 3 + i.toNat :=
          bv64_add3_zext_toNat (by omega)
        have hdst_idx : (dst + (3 : BitVec 64) + new_sz.setWidth 64).toNat =
            dst.toNat + 3 + new_sz.toNat := bv64_add3_zext_toNat (by omega)
        have hsrc_lt : (src + (3 : BitVec 64) + i.setWidth 64).toNat < arL.length := by omega
        have hdst_lt : (dst + (3 : BitVec 64) + new_sz.setWidth 64).toNat < arL.length := by omega
        let lit := arL[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'hsrc_lt
        have hlit_eq : lit = arL[src.toNat + 3 + i.toNat]'(by omega) := by
          dsimp only [lit]; simp only [hsrc_idx]
        have hlit_orig : lit = s.core.arena[src.toNat + 3 + i.toNat]'(by omega) := by
          have h1 := houtL.getElem?_ge (i := src.toNat + 3 + i.toNat) (by omega)
          rw [List.getElem?_eq_getElem (by omega : src.toNat + 3 + i.toNat < arL.length),
            List.getElem?_eq_getElem (by omega : src.toNat + 3 + i.toNat < s.core.arena.length)]
            at h1
          rw [hlit_eq]; exact Option.some.inj h1
        have hlit_cv : lit.toNat < 2 * s.core.cur_vars := by
          have := hlits_lt i.toNat hi_lt
          rw [List.getElem?_eq_getElem (by omega : src.toNat + 3 + i.toNat < s.core.arena.length),
            Option.getD_some, ← hlit_orig] at this; exact this
        have horig_succ : ((s.core.arena.drop (src.toNat + 3)).take (i.toNat + 1)).map BitVec.toNat
            = ((s.core.arena.drop (src.toNat + 3)).take i.toNat).map BitVec.toNat ++
                [lit.toNat] := by
          rw [FullReduceHelpers.drop_take_succ
              (by omega : src.toNat + 3 + i.toNat < s.core.arena.length),
            List.map_append, List.map_singleton, hlit_orig]
        have hlit_vlen : (arL[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'hsrc_lt).toNat <
            s.core.vals.length := by change lit.toNat < _; omega
        have hidx_mod : (src.toNat + (3 : BitVec 64).toNat + i.toNat) % 2 ^ 64 =
            src.toNat + 3 + i.toNat := by
          rw [show (3 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
        have ha_lit : arL[(src.toNat + (3 : BitVec 64).toNat + i.toNat) % 2 ^ 64]'(by
            rw [hidx_mod]; omega) = lit := by rw [hlit_eq]; simp only [hidx_mod]
        have hnz_step :
            ¬ (lit.toNat / 2 < s.core.cur_vars ∧
                (s.core.arena[src.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
                (s.core.flags[lit.toNat / 2]?.getD 0#32 &&& 1#32) = 0#32) →
            M7ScNoZredPrefix s src (i.toNat + 1) := by
          intro hnot hred j hj v hv_lt hfl0
          by_cases hji : j = i.toNat
          · rcases hji with rfl
            have har_j : s.core.arena[src.toNat + 3 + i.toNat]?.getD 0#32 = lit := by
              rw [List.getElem?_eq_getElem
                    (by omega : src.toNat + 3 + i.toNat < s.core.arena.length),
                Option.getD_some, ← hlit_orig]
            dsimp only [v] at hv_lt hfl0
            rw [har_j] at hv_lt hfl0
            exact hnot ⟨hv_lt, hred, hfl0⟩
          · exact hnzL hred j (by omega) hv_lt hfl0
        c0_hsteps_nogrp
        refine wp_join_group (fun (_ : Tup Val []) m' =>
            M7ScNoZredPrefix s src (i.toNat + 1) ∧ m' = mL)
          (by
            rintro _ ⟨⟩ m' ⟨hnz_i1, hm'⟩
            subst m'
            c0_hsteps_nogrp
            refine wp_join_group (M7ScJoinInv c s R src dst i) ?_ ?_
            · rintro _ ⟨new_sz', ⟨⟩⟩ m' ⟨hni', ar', har', hout', hlt', hsub', hdrop', hnz', hm'⟩
              c0_hsteps
              exact hLoop (new_sz', i + (1 : BitVec 32), ()) m' (by dsimp only; rw [hi1_eq]; omega)
                ⟨by rw [hi1_eq]; exact hni', by rw [hi1_eq]; omega, ar', har', hout', hlt',
                 by rw [hi1_eq]; exact hsub', by rw [hi1_eq]; exact hdrop',
                 by rw [hi1_eq]; exact hnz', hm'⟩
            · intro Ji hJi
              clear hLoop J hassign hpush hent0 hlits_lt
              c0_hsteps_nogrp
              refine wp_join_group (fun (_ : Tup Val []) m'' => m'' = mL) ?_ ?_
              · rintro _ ⟨⟩ m'' hm''
                have hm''_mem :
                    (FullMem c { s with core := { s.core with arena := arL } } ⋆ R) m'' :=
                  hm''.symm ▸ hmL
                clear hm''
                c0_hsteps
                obtain ⟨har', hout', hlt', hsub', hdrop'⟩ := m7sc_keep_inv harL
                  hdst_idx hdst_lt hnsz1_eq hlit_cv houtL hltL hsubL hdropL horig_succ
                exact hJi (new_sz + (1 : BitVec 32), ()) _
                  ⟨by rw [hnsz1_eq]; omega, _, har', hout', hlt', hsub', hdrop', hnz_i1,
                   by assumption⟩
              · intro Je hJe
                c0_hsplit
                · c0_hsplit
                  · have hlvl_z : (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = 0 := by
                      have h1 : s.core.lvl[lit.toNat / 2]'(by omega) = (0 : BitVec 32) := by
                        simpa only [ha_lit] using hc
                      rw [List.getElem?_eq_getElem (by omega), Option.getD_some, h1]; rfl
                    c0_hsplit
                    · have hval_ne : s.core.vals[lit.toNat]'(by omega) ≠ 0#8 := fun h0 => by
                        have h1 : (s.core.vals[lit.toNat]'(by omega)).signExtend 32 ≠ 0#32 := by
                          simpa only [ha_lit] using hc
                        rw [h0] at h1; exact h1 rfl
                      c0_hsplit
                      · c0_hsteps
                        exact hQsat harL (fun idx hidx => houtL idx (by omega)) hmL
                      · have hval_ff : s.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8 := by
                          have hdom := hw_dst.vals_domain lit.toNat hlit_cv
                          have hv_get : s.core.vals[lit.toNat]?.getD 0#8 =
                              s.core.vals[lit.toNat]'(by omega) := by
                            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                          have hng : (0#32).slt
                              ((s.core.vals[lit.toNat]'(by omega)).signExtend 32) = false := by
                            simpa only [ha_lit] using hc
                          rw [hv_get] at hdom ⊢
                          rcases hdom with h0 | h1 | hff
                          · exact absurd h0 hval_ne
                          · exact absurd ((bv8_gt0_of_dom (Or.inr (Or.inl h1))).1.mpr h1)
                              (by simp [hng])
                          · exact hff
                        c0_hsteps
                        refine hJi (new_sz, ()) mL
                          ⟨by omega, arL, harL, houtL, hltL, ?_, ?_, hnz_i1, hmL⟩
                        · rw [horig_succ]; exact hsubL.trans (List.sublist_append_left _ _)
                        · intro l hl; rw [horig_succ, List.mem_append, List.mem_singleton] at hl
                          rcases hl with hl | rfl
                          · exact hdropL l hl
                          · exact Or.inr ⟨hlit_cv, hlvl_z, hval_ff⟩
                    · c0_hsteps; exact hJe () mL rfl
                  · c0_hsteps; exact hJe () mL rfl
                · c0_hsteps; exact hJe () mL rfl)
          (fun Jz hJz => ?_)
        · have hlit_v2_lt :
              (arL[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'hsrc_lt).toNat / 2 <
              s.core.cur_vars := by
            change lit.toNat / 2 < _; omega
          c0_hsplit
          · c0_hsplit
            · have his_red : (s.core.arena[src.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 := by
                rw [List.getElem?_eq_getElem hsrc_lt0, Option.getD_some]; exact hc
              have hv_fl_lt :
                  (((arL[(src + (3 : BitVec 64) +
                    i.setWidth 64).toNat]'hsrc_lt) >>> 1#32).setWidth 64).toNat <
                    s.core.flags.length := by
                rw [zext_toNat _ (by decide), bv32_shr1_toNat]; change lit.toNat / 2 < _; omega
              c0_hsplit
              · c0_hsteps
                exact hQsat harL (fun idx hidx => houtL idx (by omega)) hmL
              · c0_hsteps
                refine hJz () mL ⟨hnz_step fun ⟨_, _, hfl0⟩ => ?_, rfl⟩
                have hfl_ne : s.core.flags[lit.toNat / 2]'(by omega) &&& 1#32 ≠ 0#32 :=
                  fun h0 => hc (by simp only [ha_lit]; exact h0)
                rw [List.getElem?_eq_getElem (by omega : lit.toNat / 2 < s.core.flags.length),
                  Option.getD_some] at hfl0
                exact hfl_ne hfl0
            · c0_hsteps
              refine hJz () mL ⟨hnz_step fun ⟨_, hred, _⟩ => ?_, rfl⟩
              rw [List.getElem?_eq_getElem hsrc_lt0, Option.getD_some] at hred
              exact absurd hc hred
          · c0_hsteps
            have hcv_le_v : s.core.cur_vars ≤ lit.toNat / 2 := by
              rw [show lit.toNat / 2 =
                  (((arL[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'hsrc_lt) >>>
                    1#32).setWidth 64).toNat by
                rw [zext_toNat _ (by decide), bv32_shr1_toNat]]
              c0_bound
            exact hJz () mL ⟨hnz_step fun ⟨hv_lt, _, _⟩ => absurd hv_lt (by omega), rfl⟩
      · have hi_eq : i.toNat = old_sz.toNat := by c0_bound
        have hnz_fin : M7ScNoZredPrefix s src old_sz.toNat := hi_eq ▸ hnzL
        have hz_absurd :
            (at_root = true →
              (s.core.arena[src.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 →
              (∃ j < old_sz.toNat,
                let v := (s.core.arena[src.toNat + 3 + j]?.getD 0#32).toNat / 2
                v < s.core.cur_vars ∧ (s.core.flags[v]?.getD 0#32 &&& 1#32) = 0#32) →
              False) := fun _ hred ⟨j, hj, hv, hfl⟩ => absurd hfl (hnz_fin hred j hj hv)
        have hpre : PrefixAgrees dst.toNat s.core.arena arL :=
          fun idx hidx => houtL.getElem?_lt (by omega)
        have hwL : FullWitnessInv c F0 F_cur { s.core with arena := arL, arena_len := dst.toNat } :=
          m7sc_witness_with_ar har_len (by omega) hcl0 hw_dst harL hpre
        have hsub_fin : List.Sublist
            (((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat)
            (((s.core.arena.drop (src.toNat + 3)).take old_sz.toNat).map BitVec.toNat) :=
          hi_eq ▸ hsubL
        have hent_kept : (cnfOfClauses F_cur).EntailsClause
            (cnfClause (((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat)) :=
          FullReduceHelpers.level0_entails_of_filter hw_dst hent0 (hi_eq ▸ hdropL)
        have hout_fin : OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + old_sz.toNat)
            s.core.arena arL := fun idx hidx => houtL idx (by omega)
        have hlenL : ({ s with core := { s.core with arena := arL } } : FullState).LengthsOk c :=
          ⟨{ hlen.core_ok with arena_len_arr := harL }, hlen.scratch_ok⟩
        have hbinL : FullReduceSpecs.BinOnlyWatchesInv F_cur { s.core with arena := arL } :=
          hbin0.with_core rfl rfl rfl rfl
        c0_hsplit
        · have hnsz0 : new_sz.toNat = 0 := by c0_bound
          rw [hnsz0] at hent_kept; simp only [List.take_zero, List.map_nil] at hent_kept
          c0_hsteps
          exact m7sc_ret_unsat hlen (by omega) (by omega) har_t hcl0 hw_dst hbin0 Qsp harL hout_fin
            (FullReduceHelpers.level0_unsat_of_entails_nil hwL hent_kept) hmL
            fun ht hr hex => absurd (hz_absurd ht hr hex) id
        · c0_hsplit
          · have hnsz1 : new_sz.toNat = 1 := by c0_bound
            have hd3_eq : (dst + (3 : BitVec 64)).toNat = dst.toNat + 3 := bv64_add3 (by omega)
            have hd3_lt : (dst + (3 : BitVec 64)).toNat < arL.length := by omega
            let ulit := arL[(dst + (3 : BitVec 64)).toNat]'hd3_lt
            obtain ⟨hulit_eq, hulit_lt, hent_u⟩ :=
              m7sc_new1_prep hd3_eq hd3_lt (hltL 0 (by omega)) (hnsz1 ▸ hent_kept)
            have hulit_lt' : ulit.toNat < 2 * s.core.cur_vars := hulit_lt
            have hulit_vlen : (arL[(dst + (3 : BitVec 64)).toNat]'hd3_lt).toNat <
                s.core.vals.length := by omega
            clear hLoop J hsub_fin hent_kept hent0 hlits_lt hpush hltL hsubL hdropL houtL hpre
              hnzL hnz_fin
            c0_hsplit
            · have hff : s.core.vals[ulit.toNat]?.getD 0#8 = 0xFF#8 := by
                have hdom := hwL.vals_domain ulit.toNat hulit_lt'
                have hget :
                    s.core.vals[ulit.toNat]?.getD 0#8 = s.core.vals[ulit.toNat]'(by omega) := by
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                rw [hget] at hdom ⊢
                exact (bv8_gt0_of_dom hdom).2.mp hc
              c0_hsteps
              exact m7sc_ret_unsat hlen (by omega) (by omega) har_t hcl0 hw_dst hbin0 Qsp harL
                hout_fin
                (FullReduceHelpers.level0_unsat_of_unit_false hwL hcl0 hulit_lt' hent_u hff)
                hmL fun ht hr hex => absurd (hz_absurd ht hr hex) id
            · c0_hsplit
              · have hun : s.core.vals[ulit.toNat]?.getD 0#8 = 0#8 := by
                  have hdm : (dst.toNat + (3 : BitVec 64).toNat) % 2 ^ 64 = dst.toNat + 3 := by
                    rw [show (3 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
                  have hua : arL[(dst.toNat + (3 : BitVec 64).toNat) % 2 ^ 64]'(by
                      rw [hdm]; omega) = ulit := by
                    dsimp only [ulit]; rw [hulit_eq]; simp only [hdm]
                  have hsext0 : (s.core.vals[ulit.toNat]'(by omega)).signExtend 32 = 0#32 := by
                    simpa only [hua] using hc
                  have hdom := hwL.vals_domain ulit.toNat hulit_lt'
                  have hg : s.core.vals[ulit.toNat]?.getD 0#8 =
                      s.core.vals[ulit.toNat]'(by omega) := by
                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  rw [hg] at hdom ⊢
                  exact (bv8_sext32_eq0_of_dom hdom).mp hsext0
                have hte_lt : s.core.trail_end < s.core.cur_vars :=
                  hwL.trail_end_lt_of_unassigned hulit_lt' hun
                have hnot_skip : ¬ (s.core.cur_vars ≤ ulit.toNat / 2 ∨
                    c.max_vars ≤ s.core.trail_end ∨ s.core.vals[ulit.toNat]?.getD 0#8 ≠ 0#8) := by
                  simp only [hun, ne_eq, not_true_eq_false, or_false]; omega
                c0_hsteps; c0_call hassign
                refine ⟨c, { s with core := { s.core with arena := arL } }, R, rfl, hlenL, hmL, ?_⟩
                split
                · rename_i hskip; exact absurd hskip hnot_skip
                · dsimp only
                  intro flags' unass' phases' m' hfl' hph' hm'
                  have hw' := FullReduceHelpers.level0Assign_preserves_witness
                    (k := { s.core with arena := arL, arena_len := dst.toNat })
                    { hlenL.core_ok with arena_len_le := by change dst.toNat ≤ c.arena_cap; omega }
                    hwL hcl0 hulit_lt' hun hent_u flags' unass' (s.core.unflushed + 1#64)
                  c0_hsteps
                  exact Qsp 1#64 arL
                    ((s.core.vals.set ulit.toNat 1#8).set (ulit.toNat ^^^ 1) 0xFF#8)
                    flags' (s.core.lvl.set (ulit.toNat / 2) 0#32)
                    (s.core.rsns.set (ulit.toNat / 2) 0xFFFFFFFF#32)
                    (s.core.trl.set s.core.trail_end ulit)
                    (s.core.trail_pos.set (ulit.toNat / 2) (BitVec.ofNat 32 s.core.trail_end))
                    (s.core.trail_end + 1) unass' (s.core.unflushed + 1#64) s.core.wvec s.core.wstk
                    s.core.wlen s.core.wusable s.core.num_binary s.core.oom phases' s.scratch.wsort
                    m'
                    ⟨{ hlenL.core_ok with
                       vals_len := by simp [hlenL.core_ok.vals_len], flags_len := hfl'
                       lvl_len := by simp [hlenL.core_ok.lvl_len]
                       rsns_len := by simp [hlenL.core_ok.rsns_len]
                       trl_len := by simp [hlenL.core_ok.trl_len]
                       trail_pos_len := by simp [hlenL.core_ok.trail_pos_len]
                       trail_end_le := hte_lt
                       propagated_le := Nat.le_succ_of_le hlenL.core_ok.propagated_le },
                     { hlenL.scratch_ok with phases_len := hph' }⟩
                    hout_fin ⟨fun hf => Bool.noConfusion (har_t.symm.trans hf),
                     fun _ => ⟨hw', hbinL.with_core rfl rfl rfl rfl, by dsimp only; omega,
                       Or.inr (Or.inr (Or.inl rfl)), (fun h => by cases h), (fun h => by cases h),
                       (fun _ => rfl), (fun _ => by dsimp only; omega),
                       (fun ⟨h3, _⟩ => by exfalso; revert h3; decide)⟩⟩ hm'
                    fun ht hr hex => absurd (hz_absurd ht hr hex) id
              · c0_hsteps; exact hQsat harL hout_fin hmL
          · c0_hsplit
            · have hnsz2 : new_sz.toNat = 2 := by c0_bound
              have hd3_eq : (dst + (3 : BitVec 64)).toNat = dst.toNat + 3 := bv64_add3 (by omega)
              have hd4_eq : (dst + (4 : BitVec 64)).toNat = dst.toNat + 4 := bv64_add4 (by omega)
              have hd3_lt : (dst + (3 : BitVec 64)).toNat < arL.length := by omega
              have hd4_lt : (dst + (4 : BitVec 64)).toNat < arL.length := by omega
              let l0 := arL[(dst + (3 : BitVec 64)).toNat]'hd3_lt
              let l1 := arL[(dst + (4 : BitVec 64)).toNat]'hd4_lt
              obtain ⟨hl0_lt, hl1_lt, hent_01, hent_10, hl0_b, hl1_b⟩ :=
                m7sc_new2_prep (by omega) hd3_eq hd4_eq hd3_lt hd4_lt
                  (hltL 0 (by omega)) (hltL 1 (by omega)) (hnsz2 ▸ hent_kept)
              have hb0 := bv32_bin_word_props hl1_b
              have hb1 := bv32_bin_word_props hl0_b
              have hsz_lt_cap : old_sz.toNat < 2 * 2 ^ 28 := by omega
              clear hLoop J hsub_fin hent_kept hw_dst hent0 hlits_lt
                hassign hltL hsubL hdropL houtL hpre hbin0 hnzL hnz_fin
                hcap_lt hmax_lt hal_le har_len hcv_le hv_len hfl_len hl_len hfit_cap hdst_fit
                hcl0 hlen hdst_src hsz3 hsrc_fit hnsz2 hl0_b hl1_b
              c0_hsteps_nogrp
              refine wp_join_group (M7ScOomInv c F_cur s R arL) ?_ ?_
              · rintro _ ⟨⟩ mOom ⟨wvecO, wstkO, wlenO, wuO, wsO, hlenO, hbinO, hmO⟩
                have hbinO' : FullReduceSpecs.BinOnlyWatchesInv F_cur
                    { s.core with arena := arL, wvec := wvecO, wstk := wstkO, wlen := wlenO,
                                  wusable := wuO, oom := 1#64 } :=
                  hbinO.with_core rfl rfl rfl rfl
                have hwO := m7sc_witness_with_binWatches hwL hbinO'
                c0_hsteps
                exact Qsp 0xFFFFFFFD#64 arL s.core.vals s.core.flags s.core.lvl s.core.rsns
                  s.core.trl s.core.trail_pos s.core.trail_end s.core.unassigned s.core.unflushed
                  wvecO wstkO wlenO wuO s.core.num_binary 1#64 s.scratch.phases wsO m
                  ⟨{ hlenO.core_ok with }, hlenO.scratch_ok⟩ hout_fin
                  ⟨fun hf => Bool.noConfusion (har_t.symm.trans hf),
                   fun _ => ⟨hwO, hbinO', Nat.le_refl _, Or.inr (Or.inl rfl),
                     (fun h => by cases h), (fun _ => rfl), (fun h => absurd rfl h),
                     (fun h => by cases h),
                     (fun ⟨_, hle⟩ => by revert hle; simp; omega)⟩⟩
                    (FullReduceHelpers.fullMem_cast hm rfl)
                  fun ht hr hex => absurd (hz_absurd ht hr hex) id
              · intro Joom hJoom
                c0_hsteps; c0_call hpush
                refine ⟨c, { s with core := { s.core with arena := arL } }, R, rfl, hlenL,
                  hbinL.layout, fun _ => hb0.2.1, fun h => by exfalso; revert h; decide, hmL,
                  fun ok1 wvec1 wstk1 wlen1 wu1 ws1 m1 hlen1 hlay1 hoth1 hok1t hok1f hm1 => ?_⟩
                have hbin1 : FullReduceSpecs.BinOnlyWatchesInv F_cur
                    { s.core with arena := arL, wvec := wvec1, wstk := wstk1, wlen := wlen1,
                                  wusable := wu1 } :=
                  FullReduceHelpers.fullWatchPush_preserves_binOnly hbinL hlay1 rfl
                    ⟨hb0.1, hb0.2.1, by rw [hb0.2.2]; exact hl1_lt, by rw [hb0.2.2]; exact hent_01⟩
                    hoth1
                    (fun h => by obtain ⟨a, _, b, c, d, _⟩ := hok1t h; exact ⟨a, b, c, d⟩)
                    (hok1f · |>.1)
                clear hbinL hb0 hl1_lt hent_01 hoth1 hok1t hok1f hlenL hmL
                c0_hsplit
                · c0_hsteps; c0_call hpush
                  refine ⟨c, { core := { s.core with arena := arL, wvec := wvec1, wstk := wstk1,
                                                     wlen := wlen1, wusable := wu1 }
                               scratch := { s.scratch with wsort := ws1 } }, R, rfl, hlen1,
                    hlay1, fun _ => hb1.2.1, fun h => by exfalso; revert h; decide, hm1,
                    fun ok2 wvec2 wstk2 wlen2 wu2 ws2 m2 hlen2 hlay2 hoth2 hok2t hok2f hm2 => ?_⟩
                  have hbin2 : FullReduceSpecs.BinOnlyWatchesInv F_cur
                      { s.core with arena := arL, wvec := wvec2, wstk := wstk2, wlen := wlen2,
                                    wusable := wu2 } :=
                    FullReduceHelpers.fullWatchPush_preserves_binOnly hbin1 hlay2 rfl
                      ⟨hb1.1, hb1.2.1, by rw [hb1.2.2]; exact hl0_lt,
                        by rw [hb1.2.2]; exact hent_10⟩
                      hoth2
                      (fun h => by obtain ⟨a, _, b, c, d, _⟩ := hok2t h; exact ⟨a, b, c, d⟩)
                      (hok2f · |>.1)
                  clear hbin1 hb1 hl0_lt hent_10 hoth2 hok2t hok2f hlen1 hlay1 hm1 hpush
                  c0_hsplit
                  · have hbin2' : FullReduceSpecs.BinOnlyWatchesInv F_cur
                        { s.core with arena := arL, wvec := wvec2, wstk := wstk2, wlen := wlen2,
                                      wusable := wu2, num_binary := s.core.num_binary + 1#64 } :=
                      hbin2.with_core rfl rfl rfl rfl
                    have hw2 := m7sc_witness_with_binWatches hwL hbin2'
                    c0_hsteps
                    exact Qsp 0xFFFFFFFF#64 arL s.core.vals s.core.flags s.core.lvl s.core.rsns
                      s.core.trl s.core.trail_pos s.core.trail_end s.core.unassigned
                      s.core.unflushed wvec2 wstk2 wlen2 wu2 (s.core.num_binary + 1#64) s.core.oom
                      s.scratch.phases ws2 m ⟨{ hlen2.core_ok with }, hlen2.scratch_ok⟩ hout_fin
                      ⟨fun hf => Bool.noConfusion (har_t.symm.trans hf),
                       fun _ => ⟨hw2, hbin2', Nat.le_refl _,
                         Or.inr (Or.inr (Or.inr (Or.inl rfl))),
                         (fun h => by cases h), (fun h => by cases h), (fun _ => rfl),
                         (fun h => by cases h),
                         (fun ⟨_, hle⟩ => by revert hle; simp; omega)⟩⟩
                      (FullReduceHelpers.fullMem_cast hm rfl)
                      (fun _ _ _ => rfl)
                  · c0_hsteps; exact hJoom () m2 ⟨wvec2, wstk2, wlen2, wu2, ws2, hlen2, hbin2, hm2⟩
                · c0_hsteps; exact hJoom () m1 ⟨wvec1, wstk1, wlen1, wu1, ws1, hlen1, hbin1, hm1⟩
            · have hge3 : 3 ≤ new_sz.toNat := by
                have h0 : new_sz.toNat ≠ 0 := by c0_bound
                have h1 : new_sz.toNat ≠ 1 := by c0_bound
                have h2 : new_sz.toNat ≠ 2 := by c0_bound
                omega
              have hnsz64 : (new_sz.setWidth 64).toNat = new_sz.toNat := zext_toNat _ (by decide)
              c0_hsteps
              exact Qsp (new_sz.setWidth 64) arL s.core.vals s.core.flags s.core.lvl s.core.rsns
                s.core.trl s.core.trail_pos s.core.trail_end s.core.unassigned s.core.unflushed
                s.core.wvec s.core.wstk s.core.wlen s.core.wusable s.core.num_binary s.core.oom
                s.scratch.phases s.scratch.wsort mL hlenL hout_fin
                ⟨fun hf => Bool.noConfusion (har_t.symm.trans hf),
                 fun _ => ⟨hwL, hbinL, Nat.le_refl _,
                   Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))),
                   fun h => by have := congrArg BitVec.toNat h; rw [hnsz64] at this; simp at this
                               omega,
                   fun h => by have := congrArg BitVec.toNat h; rw [hnsz64] at this; simp at this
                               omega,
                   fun _ => rfl,
                   fun h => by have := congrArg BitVec.toNat h; rw [hnsz64] at this; simp at this
                               omega,
                   fun _ => ⟨by simpa [hnsz64] using hltL, by simpa [hnsz64] using hsub_fin,
                     by simpa [hnsz64] using hent_kept⟩⟩⟩ hmL
                fun ht hr hex => absurd (hz_absurd ht hr hex) id
  · have har_f : at_root = false := by simpa using hc
    clear hassign hpush hroot_pre hat_eq hlits_lt hv_len hfl_len hl_len hcv_le hmax_lt
    c0_hsteps
    refine wp_loop_inv
      (fun (i, ()) mL =>
        i.toNat ≤ old_sz.toNat ∧
        ∃ arL : List (BitVec 32), arL.length = c.arena_cap ∧
          OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + i.toNat) s.core.arena arL ∧
          (∀ j < i.toNat, arL[dst.toNat + 3 + j]? = s.core.arena[src.toNat + 3 + j]?) ∧
          (FullMem c { s with core := { s.core with arena := arL } } ⋆ R) mL)
      (fun (i, ()) _ => old_sz.toNat - i.toNat)
      (fun J hLoop => ?_) ?_
    · c0_hsteps
      exact hLoop (0#32, ()) m ⟨Nat.zero_le _, s.core.arena, har_len,
        fun _ _ => rfl, fun _ hj => by simp at hj, hm⟩
    · rintro J ⟨i, ⟨⟩⟩ mL ⟨hi_le, arL, harL, houtL, hcpL, hmL⟩ hLoop
      c0_hsplit
      · have hi_lt : i.toNat < old_sz.toNat := by c0_bound
        have hi1_eq : (i + (1 : BitVec 32)).toNat = i.toNat + 1 := bv32_add1 (by omega)
        have hsrc_idx : (src + (3 : BitVec 64) + i.setWidth 64).toNat = src.toNat + 3 + i.toNat :=
          bv64_add3_zext_toNat (by omega)
        have hdst_idx : (dst + (3 : BitVec 64) + i.setWidth 64).toNat = dst.toNat + 3 + i.toNat :=
          bv64_add3_zext_toNat (by omega)
        have hsrc_lt : (src + (3 : BitVec 64) + i.setWidth 64).toNat < arL.length := by omega
        have hdst_lt : (dst + (3 : BitVec 64) + i.setWidth 64).toNat < arL.length := by omega
        have hread_orig : arL[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'hsrc_lt =
            s.core.arena[src.toNat + 3 + i.toNat]'(by omega) := by
          have h1 := houtL.getElem?_ge (i := src.toNat + 3 + i.toNat) (by omega)
          rw [List.getElem?_eq_getElem (by omega : src.toNat + 3 + i.toNat < arL.length),
            List.getElem?_eq_getElem (by omega : src.toNat + 3 + i.toNat < s.core.arena.length)]
            at h1
          simp only [hsrc_idx]; exact Option.some.inj h1
        c0_hsteps
        let ar' := arL.set (dst + (3 : BitVec 64) + i.setWidth 64).toNat
          (arL[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'hsrc_lt)
        refine hLoop (i + (1 : BitVec 32), ()) m (by dsimp only; rw [hi1_eq]; omega)
          ⟨by rw [hi1_eq]; omega, ar', by simp [ar', harL], ?_, ?_, hm⟩
        · intro idx hidx
          rw [hi1_eq] at hidx; dsimp only [ar']
          rw [List.getElem?_set_ne (by omega)]
          exact houtL idx (by omega)
        · intro j hj; rw [hi1_eq] at hj
          by_cases hje : j = i.toNat
          · subst hje; dsimp only [ar']
            rw [← hdst_idx, List.getElem?_set_self hdst_lt, hread_orig,
              List.getElem?_eq_getElem (by omega)]
          · dsimp only [ar']; rw [List.getElem?_set_ne (by omega)]; exact hcpL j (by omega)
      · have hi_eq : i.toNat = old_sz.toNat := by c0_bound
        c0_hsteps
        exact Qsp (old_sz.setWidth 64) arL s.core.vals s.core.flags s.core.lvl s.core.rsns
          s.core.trl s.core.trail_pos s.core.trail_end s.core.unassigned s.core.unflushed
          s.core.wvec s.core.wstk s.core.wlen s.core.wusable s.core.num_binary s.core.oom
          s.scratch.phases s.scratch.wsort mL
          ⟨{ hlen.core_ok with arena_len_arr := harL }, hlen.scratch_ok⟩
          (hi_eq ▸ houtL)
          ⟨fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
             rfl, rfl, rfl, hi_eq ▸ hcpL⟩,
           fun ht => Bool.noConfusion (har_f.symm.trans ht)⟩ hmL
          fun ht => absurd ht (by simp [har_f])

/-- Drop-in `Func.wp` proof for `full_sweep_copy_m7fix` vs canonical `Full.fullSweepCopySpec`. -/
theorem full_sweep_copy_m7fix_wp (Γ : Env)
    (hassign : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hpush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullSweepCopySpec a m Q X → Func.wp Γ full_sweep_copy_m7fix_body a m Q X := by
  rintro ⟨h, src, dst, old_sz, at_root, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hdst_src, hsz3, hsrc_fit, hat_eq, hlits_lt, hroot_pre, hm, hQ⟩
  exact full_sweep_copy_m7fix_no_zombie_wp Γ hassign hpush hlen hdst_src hsz3 hsrc_fit hat_eq
    hlits_lt hroot_pre hm fun r ar' v' f' l' rs' t' tp' te' un' uf' wv' ws' wl' wu' nb' om' ph'
    wst' m' _ => hQ r ar' v' f' l' rs' t' tp' te' un' uf' wv' ws' wl' wu' nb' om' ph' wst' m'

end SweepCopyProof

/-! ## 4. Closed `7`-Row `m7CompactFixSpecTable`, `m7CompactFixEnv`, and `ModuleOk` -/

section ModuleOkSection

/-- Closed `7`-row specification table for `m7CompactFixModule` (`4` M7 fixes + `3` externs). -/
def m7CompactFixSpecTable : List SpecEntry :=
  [ ⟨"full_compact_needed_m7fix", [i64], [.bool], fullCompactNeededSpec, true⟩
  , ⟨"full_compact_mark_live_m7fix", [i64], [], fullCompactMarkLiveSpec, true⟩
  , ⟨"full_compact_vars_m7fix", [i64, i64, i64], [], fullCompactVarsSpec, true⟩
  , ⟨"full_sweep_copy_m7fix", [i64, i64, i64, i32, .bool], [i64], fullSweepCopySpec, true⟩
  , ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  , ⟨"full_assign_lvl", [i64, i32, i32, i32], [], fullAssignLvlSpec, true⟩
  , ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩ ]

theorem m7CompactFixSpecTable_length : m7CompactFixSpecTable.length = 7 := by t_kernel_rfl

theorem m7CompactFixSpecTable_nodup : (m7CompactFixSpecTable.map SpecEntry.name).Nodup := by
  decide

theorem m7CompactFixSpecTable_noExit : ∀ e ∈ m7CompactFixSpecTable, e.noExit = true := by
  intro e he
  simp only [m7CompactFixSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Closed environment induced by `m7CompactFixSpecTable`. -/
def m7CompactFixEnv : Env := Env.ofTable m7CompactFixSpecTable

theorem m7CompactFixEnv_noExit :
    ∀ f as bs xs m Q X X',
      m7CompactFixEnv f as bs xs m Q X → m7CompactFixEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m7CompactFixSpecTable_noExit

private theorem m7cfEnv_row {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m7CompactFixSpecTable)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ xs m Q X, sp xs m Q X → m7CompactFixEnv nm as bs xs m Q X :=
  fun xs m Q X hs =>
    Env.ofTable_of_mem (e := ⟨nm, as, bs, sp, true⟩) hmem m7CompactFixSpecTable_nodup
      (hno xs m Q X hs)

theorem m7_compact_needed_impl :
    SpecEntry.Impl m7CompactFixEnv
      ⟨"full_compact_needed_m7fix", [i64], [.bool], full_compact_needed_m7fix_body⟩
      ⟨"full_compact_needed_m7fix", [i64], [.bool], fullCompactNeededSpec, true⟩ :=
  SpecEntry.Impl.of (full_compact_needed_m7fix_wp m7CompactFixEnv)

theorem m7_compact_mark_live_impl :
    SpecEntry.Impl m7CompactFixEnv
      ⟨"full_compact_mark_live_m7fix", [i64], [], full_compact_mark_live_m7fix_body⟩
      ⟨"full_compact_mark_live_m7fix", [i64], [], fullCompactMarkLiveSpec, true⟩ :=
  SpecEntry.Impl.of (full_compact_mark_live_m7fix_wp m7CompactFixEnv
    (m7cfEnv_row (by simp [m7CompactFixSpecTable]) (fun _ _ _ _ h => h)))

theorem m7_compact_vars_impl :
    SpecEntry.Impl m7CompactFixEnv
      ⟨"full_compact_vars_m7fix", [i64, i64, i64], [], full_compact_vars_m7fix_body⟩
      ⟨"full_compact_vars_m7fix", [i64, i64, i64], [], fullCompactVarsSpec, true⟩ :=
  SpecEntry.Impl.of (full_compact_vars_m7fix_wp m7CompactFixEnv)

theorem m7_sweep_copy_impl :
    SpecEntry.Impl m7CompactFixEnv
      ⟨"full_sweep_copy_m7fix", [i64, i64, i64, i32, .bool], [i64], full_sweep_copy_m7fix_body⟩
      ⟨"full_sweep_copy_m7fix", [i64, i64, i64, i32, .bool], [i64], fullSweepCopySpec, true⟩ :=
  SpecEntry.Impl.of (full_sweep_copy_m7fix_wp m7CompactFixEnv
    (m7cfEnv_row (by simp [m7CompactFixSpecTable]) (fun _ _ _ _ h => h))
    (m7cfEnv_row (by simp [m7CompactFixSpecTable]) (fun _ _ _ _ h => h)))

theorem m7fixCompactNeededFn_impl :
    SpecEntry.Impl m7CompactFixEnv m7fixCompactNeededFn
      ⟨"full_compact_needed", [i64], [.bool], fullCompactNeededSpec, true⟩ :=
  SpecEntry.Impl.of (full_compact_needed_m7fix_wp m7CompactFixEnv)

theorem m7fixCompactMarkLiveFn_impl :
    SpecEntry.Impl m7CompactFixEnv m7fixCompactMarkLiveFn
      ⟨"full_compact_mark_live", [i64], [], fullCompactMarkLiveSpec, true⟩ :=
  SpecEntry.Impl.of (full_compact_mark_live_m7fix_wp m7CompactFixEnv
    (m7cfEnv_row (by simp [m7CompactFixSpecTable]) (fun _ _ _ _ h => h)))

theorem m7fixCompactVarsFn_impl :
    SpecEntry.Impl m7CompactFixEnv m7fixCompactVarsFn
      ⟨"full_compact_vars", [i64, i64, i64], [], fullCompactVarsSpec, true⟩ :=
  SpecEntry.Impl.of (full_compact_vars_m7fix_wp m7CompactFixEnv)

theorem m7fixSweepCopyFn_impl :
    SpecEntry.Impl m7CompactFixEnv m7fixSweepCopyFn
      ⟨"full_sweep_copy", [i64, i64, i64, i32, .bool], [i64], fullSweepCopySpec, true⟩ :=
  SpecEntry.Impl.of (full_sweep_copy_m7fix_wp m7CompactFixEnv
    (m7cfEnv_row (by simp [m7CompactFixSpecTable]) (fun _ _ _ _ h => h))
    (m7cfEnv_row (by simp [m7CompactFixSpecTable]) (fun _ _ _ _ h => h)))

theorem m7CompactFix_allFns_wf : AllFns Fn.Wf m7CompactFixModule.fns :=
  ⟨full_compact_needed_m7fix_wf, full_compact_mark_live_m7fix_wf,
    full_compact_vars_m7fix_wf, full_sweep_copy_m7fix_wf, trivial⟩

theorem m7CompactFix_tableImpl :
    TableImpl m7CompactFixEnv m7CompactFixModule.fns m7CompactFixSpecTable :=
  ⟨m7_compact_needed_impl, m7_compact_mark_live_impl, m7_compact_vars_impl,
    m7_sweep_copy_impl, trivial⟩

/-- Closed `ModuleOk` certifying `m7CompactFixModule` under `m7CompactFixEnv` (`0` exits). -/
theorem m7CompactFix_moduleOk : ModuleOk m7CompactFixEnv m7CompactFixModule :=
  Env.ofTable_moduleOk m7CompactFix_acyclic m7CompactFix_allFns_wf m7CompactFix_tableImpl

end ModuleOkSection

/-! ## 5. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

section ConcreteUnsatNonVacuity

private theorem nvM7CfF0_unsat : nvOneLitF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [nvOneLitF0, cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [nvOneLitF0, cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1; simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have : v0 = 0 := by omega
    have : v1 = 0 := by omega
    subst v0 v1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_compact_needed_m7fix`:
below the `128`-var floor on `nvCompactMem` (`cur_vars = 2`), returns `res = false`. -/
theorem nv_m7fix_compact_needed :
    Func.wp m7CompactFixEnv full_compact_needed_m7fix_body (nvCompactCfg.hdr, ()) nvCompactMem
      (fun (res, ()) m' =>
        res = false ∧ nvCompactF0.Unsat ∧ FullMem nvCompactCfg nvCompactState m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvCompactCfg nvCompactState ⋆ emp) nvCompactMem := by
    rw [sep_emp]; exact nvCompactMem_ok
  refine full_compact_needed_m7fix_exact_wp m7CompactFixEnv _ _ _ _
    ⟨nvCompactCfg, nvCompactState, emp, rfl, nvCompact_lengths, by decide, hm,
      fun res hiff => ?_⟩
  have hf : res = false := by
    cases hres : res
    · rfl
    · have h128 := (hiff.mp hres).2.2.1
      have hcv : nvCompactState.core.cur_vars = 2 := rfl
      omega
  exact ⟨hf, nvCompactF0_unsat, nvCompactMem_ok⟩

/-- Concrete `FullCfg` (`max_vars = 3`, `arena_cap = 6`, `wcap = 1`, `avail = 2076`) housing a
`PH_RED` arena clause `[1, 2, 4]` with `!FL_ACTIVE` var `1` (`flags[1] = 8#32`) and poisoned
`work_stk1 = [99, 99, 99, 99, 99, 99]`. -/
def nvM7MkLiveCfg : FullCfg where
  hdr := 0x1000#64
  avail := 2076
  mv := 3
  max_vars := 3
  bva_cap := 0
  nc := 2
  arena_cap := 6
  wcap := 1
  delayed_cap := 0
  red_cap := 0
  extend_cap := 0
  scratch_cap := 0
  hbva := rfl
  hmv := by decide
  hmaxv := by decide
  hnc := by decide
  harena := by decide
  hwcap := by decide
  hdel := by decide
  hred := by decide
  hext := by decide
  hscr := by decide
  havail_fit := by decide
  hsize := by decide

/-- Concrete `FullScratch` for `nvM7MkLiveCfg` with poisoned `work_stk1` (`99#32`) and
`work_stk2 = [1#32, 0#32, 0#32, ...]`. -/
def nvM7MkLiveScratch : FullScratch where
  heap_len := 0; scinc := 0#64; rel_period := 0#64; rel_limit := 0#64; rel_wait := 0#64
  rel_u := 0#64; rel_v := 0#64; rel_trigger := 0#64; conflicts := 0#64; learned_lits := 0#64
  min_removed := 0#64; delayed_len := 0; stable := 0#64; switched := 0#64; mode_count := 0#64
  mode_confl_lim := 0#64; mode_tick_lim := 0#64; mode_saved_ticks := 0#64; search_ticks := 0#64
  q_first := 0#64; q_last := 0#64; q_search_idx := 0#64; q_search_stamp := 0#64
  q_cur_stamp := 0#64; target_assigned := 0#64; best_assigned := 0#64; rephase_limit := 0#64
  rephased := 0#64; reduce_limit := 0#64; reductions := 0#64; tier1 := 0#64; tier2 := 0#64
  restarts := 0#64; restart_limit := 0#64; ema_fast_biased := 0#64; ema_fast_exp := 0#64
  ema_slow_biased := 0#64; ema_slow_exp := 0#64; extend_len := 0; rng_state := 0#64
  chrono_levels := 0#64; otfs_cnt := 0#64; eager_sub_cnt := 0#64; probe_limit := 0#64
  probings := 0#64; elim_limit := 0#64; eliminations := 0#64; elim_bound := 0#64
  iterating := 0#64; hbr_cnt := 0#64; trans_cnt := 0#64; viv_cnt := 0#64; subst_cnt := 0#64
  cong_cnt := 0#64; sweep_cnt := 0#64; bve_cnt := 0#64; bce_cnt := 0#64; bva_cnt := 0#64
  walk_cnt_stat := 0#64; fwd_sub_cnt := 0#64; fwd_str_cnt := 0#64; ant_sz := 0#64; res_sz := 0#64
  walk_vals := List.replicate 6 0#8; phases := List.replicate 3 0#8
  phases_target := List.replicate 3 0#8; phases_best := List.replicate 3 0#8
  walk_best := List.replicate 3 0#8; heap := List.replicate 3 0#32
  pos := List.replicate 3 0#32; shrink_stk := List.replicate 3 0#32
  q_prev := List.replicate 3 0#32; q_next := List.replicate 3 0#32; q_stamp := List.replicate 3 0#32
  wsort := List.replicate 6 0#32; work_stk1 := List.replicate 6 99#32
  work_stk2 := [1#32, 0#32, 0#32, 0#32, 0#32, 0#32]
  tarjan_mark := List.replicate 6 0#32; tarjan_reach := List.replicate 6 0#32
  score := List.replicate 3 0#64; sim_sig := List.replicate 3 0#64
  glue_used := List.replicate 64 0#32; last_learned := List.replicate 16 0xFFFFFFFF#32
  delayed := []; red_refs := []; extend_stk := []; scratch_buf := []

/-- Concrete `FullState` with `flags = [1#32, 8#32, 1#32]`, root assignment `x0 = true`,
and `PH_RED` clause `[1, 2, 4]` referencing zombie var `1`. -/
def nvM7MkLiveState : FullState where
  core :=
    { d_cur := 0#64, d_val := 0#64, arena_len := 6, wlen := 0, trail_end := 1, propagated := 1,
      cur_level := 0, fuel := 0#64, confl_ref := 0xFFFFFFFF#64, tmp_cnt := 0, tmp_len := 0,
      min_clr_len := 0, min_clr_full := 0#64, wusable := 0#64, probing := 0#64,
      arena_garbage := 0#64, first_reducible := 0#64, num_irred := 0#64, num_redundant := 1#64,
      num_binary := 0#64, unflushed := 0#64, confl_type := 0#64, confl_lit0 := 0#64,
      confl_lit1 := 0#64, cur_vars := 3, unassigned := 2#64, dense_mode := 0#64,
      inconsistent := 0#64, oom := 0#64,
      vals := [1#8, 0xFF#8, 0#8, 0#8, 0#8, 0#8],
      lit_mark := List.replicate 6 0#8, mrk := List.replicate 3 0#8,
      flags := [1#32, 8#32, 1#32], lvl := List.replicate 3 0#32,
      rsns := List.replicate 3 0xFFFFFFFF#32, trl := List.replicate 3 0#32,
      trail_pos := List.replicate 3 0#32, tmp := List.replicate 3 0#32,
      min_clr := List.replicate 3 0#32, frame_trail := List.replicate 4 0#32,
      frame_dec := List.replicate 4 0#32, wvec := List.replicate 12 0#32,
      repr := List.replicate 6 0#32, min_stk := List.replicate 8 0#32,
      arena := [0x00400028#32, 0#32, 3#32, 1#32, 2#32, 4#32], wstk := [0#32] }
  scratch := nvM7MkLiveScratch

private def nvM7BlockHdr : List UInt8 :=
  bytes64 [3#64, 2#64, 0#64, 0#64] ++ bytes64 (Full.hdrTailWords nvM7MkLiveCfg nvM7MkLiveState)

private def nvM7BlockBytes : List UInt8 :=
  (bytesOf (t := i8) nvM7MkLiveState.core.vals ++ List.replicate 2 0) ++
  (bytesOf (t := i8) nvM7MkLiveState.scratch.walk_vals ++ List.replicate 2 0) ++
  (bytesOf (t := i8) nvM7MkLiveState.core.lit_mark ++ List.replicate 2 0) ++
  (bytesOf (t := i8) nvM7MkLiveState.core.mrk ++ List.replicate 5 0) ++
  (bytesOf (t := i8) nvM7MkLiveState.scratch.phases ++ List.replicate 5 0) ++
  (bytesOf (t := i8) nvM7MkLiveState.scratch.phases_target ++ List.replicate 5 0) ++
  (bytesOf (t := i8) nvM7MkLiveState.scratch.phases_best ++ List.replicate 5 0) ++
  (bytesOf (t := i8) nvM7MkLiveState.scratch.walk_best ++ List.replicate 5 0)

private def nvM7BlockU32A : List UInt8 :=
  (bytesOf (t := i32) nvM7MkLiveState.core.flags ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM7MkLiveState.core.lvl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM7MkLiveState.core.rsns ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM7MkLiveState.core.trl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM7MkLiveState.core.trail_pos ++ List.replicate 4 0)

private def nvM7BlockU32B : List UInt8 :=
  (bytesOf (t := i32) nvM7MkLiveState.core.tmp ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM7MkLiveState.scratch.heap ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM7MkLiveState.scratch.pos ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM7MkLiveState.core.min_clr ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM7MkLiveState.scratch.shrink_stk ++ List.replicate 4 0)

private def nvM7BlockU32C : List UInt8 :=
  (bytesOf (t := i32) nvM7MkLiveState.scratch.q_prev ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM7MkLiveState.scratch.q_next ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM7MkLiveState.scratch.q_stamp ++ List.replicate 4 0) ++
  bytesOf (t := i32) nvM7MkLiveState.core.frame_trail ++
  bytesOf (t := i32) nvM7MkLiveState.core.frame_dec

private def nvM7BlockWvec : List UInt8 :=
  bytesOf (t := i32) nvM7MkLiveState.core.wvec ++ bytesOf (t := i32) nvM7MkLiveState.core.repr ++
  bytesOf (t := i32) nvM7MkLiveState.scratch.wsort ++
  bytesOf (t := i32) nvM7MkLiveState.scratch.work_stk1 ++
  bytesOf (t := i32) nvM7MkLiveState.scratch.work_stk2 ++
  bytesOf (t := i32) nvM7MkLiveState.scratch.tarjan_mark ++
  bytesOf (t := i32) nvM7MkLiveState.scratch.tarjan_reach ++
  bytes64 nvM7MkLiveState.scratch.score ++ bytes64 nvM7MkLiveState.scratch.sim_sig

private def nvM7BlockTail : List UInt8 :=
  bytesOf (t := i32) nvM7MkLiveState.core.min_stk ++
  bytesOf (t := i32) nvM7MkLiveState.scratch.glue_used ++
  bytesOf (t := i32) nvM7MkLiveState.scratch.last_learned ++
  bytesOf (t := i32) nvM7MkLiveState.core.arena ++ bytesOf (t := i32) nvM7MkLiveState.core.wstk

/-- Concrete byte image for `nvM7MkLiveCfg` / `nvM7MkLiveState`. -/
def nvM7MkLiveBytes : List UInt8 :=
  nvM7BlockHdr ++ nvM7BlockBytes ++ nvM7BlockU32A ++ nvM7BlockU32B ++
  nvM7BlockU32C ++ nvM7BlockWvec ++ nvM7BlockTail

/-- Concrete `Mem 64` mapped at `nvM7MkLiveCfg.hdr` (`0x1000`). -/
def nvM7MkLiveMem : Mem 64 := nvM7MkLiveBytes.At nvM7MkLiveCfg.hdr

private theorem nvM7MkLiveMem_ok : FullMem nvM7MkLiveCfg nvM7MkLiveState nvM7MkLiveMem := by
  let c := nvM7MkLiveCfg; let s := nvM7MkLiveState
  have hvb : valsBytes c.max_vars - 2 * c.max_vars = 2 := by decide
  have hmb : markBytes c.max_vars - c.max_vars = 5 := by decide
  have hu4 : u32FullBytes c.max_vars - 4 * c.max_vars = 4 := by decide
  have hu8 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 0 := by decide
  have hmv1 : BitVec.ofNat 64 c.max_vars = 3#64 := rfl
  have hmv2 : BitVec.ofNat 64 (2 * c.max_vars) = 6#64 := rfl
  have hmv4 : BitVec.ofNat 64 (4 * c.max_vars) = 12#64 := rfl
  have hmv8 : BitVec.ofNat 64 (4 * (c.max_vars + 1)) = 16#64 := rfl
  have hHdr : nvM7BlockHdr.length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s))
        (nvM7BlockHdr.At c.hdr) :=
    nv_join_pair
      (nv_arr64_p (a := c.hdr) (xs := [3#64, 2#64, 0#64, 0#64]) 32 rfl (by decide))
      (nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide)) (by decide) (by decide)
  have hBytes : nvM7BlockBytes.length = 64 ∧
      (FullCoreByteArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆ c.padBytes)
        (nvM7BlockBytes.At c.pVals) := by
    let pB1 : Mem 64 → Prop :=
      region (c.pVals + 6#64) 2 ⋆ region (c.pWalkVals + 6#64) 2 ⋆
      region (c.pLitMark + 6#64) 2 ⋆ region (c.pMark + 3#64) 5
    have h1234 := nv_sep_reorg (nv_join_pair (nv_join_pair (nv_join_pair
      (nv_arr_pad_p (t := i8) (a := c.pVals) (xs := s.core.vals) 6 2 rfl (by decide))
      (nv_arr_pad_p (t := i8) (a := c.pWalkVals) (xs := s.scratch.walk_vals) 6 2 rfl (by decide))
      (by decide) (by decide))
      (nv_arr_pad_p (t := i8) (a := c.pLitMark) (xs := s.core.lit_mark) 6 2 rfl (by decide))
      (by decide) (by decide))
      (nv_arr_pad_p (t := i8) (a := c.pMark) (xs := s.core.mrk) 3 5 rfl (by decide))
      (by decide) (by decide))
      (Q := (FullCoreByteArrs c s.core ⋆ array (t := i8) c.pWalkVals s.scratch.walk_vals) ⋆ pB1)
      fun _ hm => nv_zip4 hm
    have hall := nv_join_pair (nv_join_pair (nv_join_pair (nv_join_pair h1234
      (nv_arr_pad_p (t := i8) (a := c.pPhases) (xs := s.scratch.phases) 3 5 rfl (by decide))
      (by decide) (by decide))
      (nv_arr_pad_p (t := i8) (a := c.pPhasesTarget) (xs := s.scratch.phases_target) 3 5 rfl
        (by decide)) (by decide) (by decide))
      (nv_arr_pad_p (t := i8) (a := c.pPhasesBest) (xs := s.scratch.phases_best) 3 5 rfl
        (by decide)) (by decide) (by decide))
      (nv_arr_pad_p (t := i8) (a := c.pWalkBest) (xs := s.scratch.walk_best) 3 5 rfl (by decide))
      (by decide) (by decide)
    exact nv_sep_reorg hall fun _ hm => by
      have hfin := nv_zip4_tail hm
      unfold FullScrByteArrs FullCfg.padBytes; rw [hvb, hmb, hmv2, hmv1]
      simpa only [pB1, sep_assoc] using hfin
  have hU32A : nvM7BlockU32A.length = 80 ∧
      ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
        (nvM7BlockU32A.At c.pFlags) := by
    have hall := nv_join_pair (nv_join_pair (nv_join_pair (nv_join_pair
      (nv_arr_pad_p (t := i32) (a := c.pFlags) (xs := s.core.flags) 12 4 rfl (by decide))
      (nv_arr_pad_p (t := i32) (a := c.pLevel) (xs := s.core.lvl) 12 4 rfl (by decide))
      (by decide) (by decide))
      (nv_arr_pad_p (t := i32) (a := c.pReason) (xs := s.core.rsns) 12 4 rfl (by decide))
      (by decide) (by decide))
      (nv_arr_pad_p (t := i32) (a := c.pTrail) (xs := s.core.trl) 12 4 rfl (by decide))
      (by decide) (by decide))
      (nv_arr_pad_p (t := i32) (a := c.pTrailPos) (xs := s.core.trail_pos) 12 4 rfl (by decide))
      (by decide) (by decide)
    exact nv_sep_reorg hall fun _ hm => by unfold FullCfg.padU32A; rw [hu4, hmv4]; exact sep_ac hm
  have hU32B : nvM7BlockU32B.length = 80 ∧
      ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
        (array (t := i32) c.pHeap s.scratch.heap ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
         array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
        (nvM7BlockU32B.At c.pTmp) := by
    have hall := nv_join_pair (nv_join_pair (nv_join_pair (nv_join_pair
      (nv_arr_pad_p (t := i32) (a := c.pTmp) (xs := s.core.tmp) 12 4 rfl (by decide))
      (nv_arr_pad_p (t := i32) (a := c.pHeap) (xs := s.scratch.heap) 12 4 rfl (by decide))
      (by decide) (by decide))
      (nv_arr_pad_p (t := i32) (a := c.pPos) (xs := s.scratch.pos) 12 4 rfl (by decide))
      (by decide) (by decide))
      (nv_arr_pad_p (t := i32) (a := c.pMinClr) (xs := s.core.min_clr) 12 4 rfl (by decide))
      (by decide) (by decide))
      (nv_arr_pad_p (t := i32) (a := c.pShrinkStk) (xs := s.scratch.shrink_stk) 12 4 rfl
        (by decide))
      (by decide) (by decide)
    exact nv_sep_reorg hall fun _ hm => by unfold FullCfg.padU32B; rw [hu4, hmv4]; exact sep_ac hm
  have hU32C : nvM7BlockU32C.length = 80 ∧
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆ array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
         array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
        (nvM7BlockU32C.At c.pQPrev) := by
    have hft : (bytesOf (t := i32) s.core.frame_trail).length = 16 ∧
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆ region (c.pFrameTrail + 16#64) 0)
          ((bytesOf (t := i32) s.core.frame_trail).At c.pFrameTrail) := by
      simpa only [List.replicate_zero, List.append_nil] using
        nv_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail) 16 0 rfl (by decide)
    have hfd : (bytesOf (t := i32) s.core.frame_dec).length = 16 ∧
        (array (t := i32) c.pFrameDec s.core.frame_dec ⋆ region (c.pFrameDec + 16#64) 0)
          ((bytesOf (t := i32) s.core.frame_dec).At c.pFrameDec) := by
      simpa only [List.replicate_zero, List.append_nil] using
        nv_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec) 16 0 rfl (by decide)
    have hall := nv_join_pair (nv_join_pair (nv_join_pair (nv_join_pair
      (nv_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev) 12 4 rfl (by decide))
      (nv_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next) 12 4 rfl (by decide))
      (by decide) (by decide))
      (nv_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 12 4 rfl (by decide))
      (by decide) (by decide)) hft (by decide) (by decide)) hfd (by decide) (by decide)
    exact nv_sep_reorg hall fun _ hm => by
      unfold FullCfg.padU32C; rw [hu4, hu8, hmv4, hmv8]; exact sep_ac hm
  have hWvec : nvM7BlockWvec.length = 240 ∧
      ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
        FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
        (nvM7BlockWvec.At c.pWvec) := by
    have hall := nv_join_pair (nv_join_pair (nv_join_pair (nv_join_pair (nv_join_pair (nv_join_pair
      (nv_join_pair (nv_join_pair
        (nv_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 48 rfl (by decide))
        (nv_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 24 rfl (by decide))
        (by decide) (by decide))
        (nv_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 24 rfl (by decide))
        (by decide) (by decide))
        (nv_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1) 24 rfl (by decide))
        (by decide) (by decide))
        (nv_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2) 24 rfl (by decide))
        (by decide) (by decide))
        (nv_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 24 rfl (by decide))
        (by decide) (by decide))
        (nv_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach) 24 rfl
          (by decide)) (by decide) (by decide))
        (nv_arr64_p (a := c.pScore) (xs := s.scratch.score) 24 rfl (by decide))
        (by decide) (by decide))
      (nv_arr64_p (a := c.pSimSig) (xs := s.scratch.sim_sig) 24 rfl (by decide))
      (by decide) (by decide)
    exact nv_sep_reorg hall fun _ hm => by unfold FullScrWksArrs; exact sep_ac hm
  have hTail : nvM7BlockTail.length = 380 ∧
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
        (nvM7BlockTail.At c.pMinStk) := by
    have h1 := nv_arr_p (t := i32) (a := c.pMinStk) (xs := s.core.min_stk) 32 rfl (by decide)
    have h2 := nv_arr_p (t := i32) (a := c.pGlueUsed) (xs := s.scratch.glue_used) 256 rfl
      (by decide)
    have h3 := nv_arr_p (t := i32) (a := c.pLastLearned) (xs := s.scratch.last_learned) 64 rfl
      (by decide)
    have h4 := nv_arr_p (t := i32) (a := c.pArena) (xs := s.core.arena) 24 rfl (by decide)
    have h5 := nv_arr_p (t := i32) (a := c.pWstk) (xs := s.core.wstk) 4 rfl (by decide)
    have h6 := nv_arr_p (t := i32) (a := c.pDelayed) (xs := s.scratch.delayed) 0 rfl (by decide)
    have h7 := nv_arr_p (t := i32) (a := c.pRedRefs) (xs := s.scratch.red_refs) 0 rfl (by decide)
    have h8 := nv_arr_p (t := i32) (a := c.pExtendStk) (xs := s.scratch.extend_stk) 0 rfl
      (by decide)
    have h9 := nv_arr_p (t := i32) (a := c.pScratchBuf) (xs := s.scratch.scratch_buf) 0 rfl
      (by decide)
    have h10 : ([] : List UInt8).length = 0 ∧
        region c.pSlack c.slack (([] : List UInt8).At c.pSlack) :=
      ⟨rfl, ⟨[], by decide, rfl⟩⟩
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    have h12345 := nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := nv_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := nv_join_pair h1234567 h8 (by decide) (by decide)
    have h123456789 := nv_join_pair h12345678 h9 (by decide) (by decide)
    have hall := nv_join_pair h123456789 h10 (by decide) (by decide)
    have htail_eq :
        (((((((((bytesOf (t := i32) s.core.min_stk ++ bytesOf (t := i32) s.scratch.glue_used) ++
          bytesOf (t := i32) s.scratch.last_learned) ++ bytesOf (t := i32) s.core.arena) ++
          bytesOf (t := i32) s.core.wstk) ++ bytesOf (t := i32) s.scratch.delayed) ++
          bytesOf (t := i32) s.scratch.red_refs) ++ bytesOf (t := i32) s.scratch.extend_stk) ++
          bytesOf (t := i32) s.scratch.scratch_buf) ++ []) = nvM7BlockTail := by
      change (((((((((bytesOf (t := i32) nvM7MkLiveState.core.min_stk ++
        bytesOf (t := i32) nvM7MkLiveState.scratch.glue_used) ++
        bytesOf (t := i32) nvM7MkLiveState.scratch.last_learned) ++
        bytesOf (t := i32) nvM7MkLiveState.core.arena) ++
        bytesOf (t := i32) nvM7MkLiveState.core.wstk) ++ []) ++ []) ++ []) ++ []) ++ []) =
        nvM7BlockTail
      unfold nvM7BlockTail
      simp only [List.append_nil, List.append_assoc]
    rw [htail_eq] at hall
    exact nv_sep_reorg hall fun _ hm => by
      unfold FullCoreDynArrs FullScrDynArrs; exact sep_ac hm
  have hall := nv_join_pair (nv_join_pair (nv_join_pair (nv_join_pair (nv_join_pair
    (nv_join_pair hHdr hBytes (by decide) (by decide)) hU32A (by decide) (by decide))
    hU32B (by decide) (by decide)) hU32C (by decide) (by decide)) hWvec (by decide) (by decide))
    hTail (by decide) (by decide)
  exact (nv_sep_reorg hall fun _ hm => by
    unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B FullScratchArrays FullScrU32A
      FullScrMetaArrs FullCfg.pad
    exact sep_ac hm).2

private theorem nvM7MkLive_lengths : nvM7MkLiveState.LengthsOk nvM7MkLiveCfg :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.zero_le _, by decide, Nat.le_refl _,
    Nat.zero_le _, Nat.zero_le _⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem nvM7MkLive_sparseW :
    FullSparseInvW nvM7MkLiveCfg nvOneLitF0 [[0], [1]] nvM7MkLiveState := by
  have hrefs : fullArenaClauseRefsCore nvM7MkLiveState.core = [0] := rfl
  have hcv : nvM7MkLiveState.core.cur_vars = 3 := rfl
  have hte : nvM7MkLiveState.core.trail_end = 1 := rfl
  have hcl : nvM7MkLiveState.core.cur_level = 0 := rfl
  have hdm : nvM7MkLiveState.core.dense_mode = 0#64 := rfl
  have hwat : ModeWatchesInv [[0], [1]] nvM7MkLiveState.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_) (fun l1 _ h1 _ _ hp => ?_)
      (fun l hl => ?_)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [fullWatchSizeCore, nvM7MkLiveState] at hp)
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1 ∨ l1 = 2 ∨ l1 = 3 ∨ l1 = 4 ∨ l1 = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [fullWatchSizeCore, nvM7MkLiveState] at hp)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> exact WatchSliceOk.empty
  have hent0 : (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0]) := by
    rw [CNF.entails_clause_def]; intro α hα
    exact (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  have hent1 : (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [1]) := by
    rw [CNF.entails_clause_def]; intro α hα
    exact (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  have hent124 : (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [1, 2, 4]) := by
    rw [CNF.entails_clause_def]; intro α hα
    have hs1 : (cnfClause [1]).Sat α := (CNF.entails_clause_def.mp hent1) α hα
    rw [CNF.Clause.sat_iff_exists_mem_eq] at hs1 ⊢
    obtain ⟨lit, hm, heq⟩ := hs1; refine ⟨lit, ?_, heq⟩
    rw [mem_cnfClause_iff] at hm ⊢; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    exact Or.inl hm
  have har : FullArenaClausesInv nvM7MkLiveCfg [[0], [1]] nvM7MkLiveState.core := by
    refine ⟨Or.inr (by decide),
      (fun r hr => by rw [hrefs, List.mem_singleton] at hr; subst hr; decide),
      (fun r hr hsh => by
        rw [hrefs, List.mem_singleton] at hr; subst hr
        exact absurd (by decide : fullArenaHdrCore nvM7MkLiveState.core 0 &&& 0x00800000#32 = 0#32)
          hsh),
      (fun r hr _ l hl => ?_), (fun r hr _ => ?_)⟩
    · rw [hrefs, List.mem_singleton] at hr; subst hr
      have h124 : fullArenaClauseLitsCore nvM7MkLiveState.core 0 = [1, 2, 4] := rfl
      rw [h124] at hl; rw [hcv]
      exact (by decide : ∀ l ∈ ([1, 2, 4] : List Nat), l < 2 * 3) l hl
    · rw [hrefs, List.mem_singleton] at hr; subst hr
      have h124 : fullArenaClauseLitsCore nvM7MkLiveState.core 0 = [1, 2, 4] := rfl
      rw [h124]; exact hent124
  have hw : FullWitnessInv nvM7MkLiveCfg nvOneLitF0 [[0], [1]] nvM7MkLiveState.core :=
    { ext_sound := ⟨(varsBoundedBool_iff 3 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := har, watches := hwat, cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hte] at hi hj; omega
      vals_domain := fun l hl =>
        (by decide : ∀ l < 6, nvM7MkLiveState.core.vals[l]?.getD 0#8 = 0#8 ∨
          nvM7MkLiveState.core.vals[l]?.getD 0#8 = 1#8 ∨
          nvM7MkLiveState.core.vals[l]?.getD 0#8 = 0xFF#8) l (by rw [hcv] at hl; exact hl)
      vals_true_iff := fun l hl => by
        have h0 : (nvM7MkLiveState.core.vals[l]?.getD 0#8 = 1#8) ↔ l = 0 :=
          (by decide : ∀ l < 6, nvM7MkLiveState.core.vals[l]?.getD 0#8 = 1#8 ↔ l = 0) l
            (by rw [hcv] at hl; exact hl)
        rw [h0]; exact ⟨(fun he => by subst he; exact ⟨0, by decide, by decide⟩),
          (fun ⟨i, hi, he⟩ => by
            obtain rfl : i = 0 := by rw [hte] at hi; omega
            change l = 0; simp only [← he]; decide)⟩
      vals_false_iff := fun l hl => by
        have h1 : (nvM7MkLiveState.core.vals[l]?.getD 0#8 = 0xFF#8) ↔ l ^^^ 1 = 0 :=
          (by decide : ∀ l < 6, nvM7MkLiveState.core.vals[l]?.getD 0#8 = 0xFF#8 ↔ l ^^^ 1 = 0) l
            (by rw [hcv] at hl; exact hl)
        rw [h1]; exact ⟨(fun he => by
            have hl1 : l = 1 := by
              rw [hcv] at hl
              rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
                rfl | rfl | rfl | rfl | rfl | rfl
              · exact absurd he (by decide)
              · rfl
              · exact absurd he (by decide)
              · exact absurd he (by decide)
              · exact absurd he (by decide)
              · exact absurd he (by decide)
            subst hl1; exact ⟨0, by decide, by decide⟩),
          (fun ⟨i, hi, he⟩ => by
            obtain rfl : i = 0 := by rw [hte] at hi; omega
            have h0 : (nvM7MkLiveState.core.trl[0]?.getD 0#32).toNat = 0 := by decide
            rw [h0] at he; change l ^^^ 1 = 0
            rw [hcv] at hl
            rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
              rfl | rfl | rfl | rfl | rfl | rfl <;>
              first | exact absurd he (by decide) | rfl)⟩
      lvl_le := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact Nat.le_refl 0
      dec_earliest := fun _ j _ hj _ hpos => by
        rw [hte] at hj; obtain rfl : j = 0 := (by omega); exact absurd hpos.1 (by decide)
      levels_inhabited := fun _ _ h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact hent0
      trail_pos_inv := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      level0_rsn_none := fun i hi _ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      frame_trail_lt := fun L hL => by rw [hcl] at hL; obtain rfl : L = 0 := (by omega); decide
      frame_trail_mono := fun L1 L2 _ hL2 => by
        rw [hcl] at hL2; obtain rfl : L1 = 0 := (by omega); obtain rfl : L2 = 0 := (by omega)
        exact Nat.le_refl _
      frame_trail_before_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne
      reason_lit_mem := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne }
  have hmv : nvM7MkLiveCfg.max_vars = 3 := rfl
  have hmarks : FullLitMarksClear nvM7MkLiveCfg nvM7MkLiveState := by
    refine ⟨fun v hv => ?_, fun l hl => ?_⟩
    · rw [hmv] at hv; rcases (by omega : v = 0 ∨ v = 1 ∨ v = 2) with rfl | rfl | rfl <;> rfl
    · rw [hmv] at hl
      rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hnd : FullArenaVarsNodup nvM7MkLiveState := fun r hr => by
    have : fullArenaClauseRefs nvM7MkLiveState = [0] := rfl
    rw [this, List.mem_singleton] at hr; subst hr; decide
  have hext : FullExtScratchOk nvM7MkLiveCfg nvM7MkLiveState :=
    ⟨FullLastLearnedWf.of_cleared fun i hi => by
      simp only [nvM7MkLiveState, nvM7MkLiveScratch, List.getElem?_replicate, show i < 16 by omega,
        ↓reduceIte, Option.getD_some], Nat.le_refl 0⟩
  exact ⟨nvM7MkLive_lengths, hw, hmarks, hnd, hext, rfl⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) for
`full_compact_mark_live_m7fix` on a `PH_RED` clause `[1, 2, 4]` referencing zombie var `1`
(`flags[1] = 8#32`) with poisoned `work_stk1 = [99, ...]`: proves `ws1'[1]? = some 0#32`. -/
theorem nv_m7fix_compact_mark_live :
    Func.wp m7CompactFixEnv full_compact_mark_live_m7fix_body (nvM7MkLiveCfg.hdr, ()) nvM7MkLiveMem
      (fun () m' => ∃ ws1',
        let s' : FullState :=
          { nvM7MkLiveState with scratch := { nvM7MkLiveState.scratch with work_stk1 := ws1' } }
        FullSparseInv nvM7MkLiveCfg nvOneLitF0 s' ∧ ws1'[1]? = some 0#32 ∧
        nvOneLitF0.Unsat ∧ FullMem nvM7MkLiveCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM7MkLiveCfg nvM7MkLiveState ⋆ emp) nvM7MkLiveMem := by
    rw [sep_emp]; exact nvM7MkLiveMem_ok
  refine full_compact_mark_live_m7fix_no_zombie_wp m7CompactFixEnv
    (m7cfEnv_row (by simp [m7CompactFixSpecTable]) (fun _ _ _ _ h => h))
    nvM7MkLive_sparseW hm fun ws1' m' hsp' hnz' hm' => ?_
  rw [sep_emp] at hm'
  have hdead1 : ws1'[1]? = some 0#32 := hnz' 1 (by decide) (by decide)
  exact ⟨ws1', hsp'.toSparse, hdead1, nvM7CfF0_unsat, hm'⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) for
`full_compact_vars_m7fix` remapping `inv[0] = 1` with `flags = [1#32, 8#32, 1#32]` (`ncv = 1`):
proves `fl'[0]? = some 8#32` (`FL_ELIM` preserved, NOT resurrected as `FL_ACTIVE`). -/
theorem nv_m7fix_compact_vars :
    Func.wp m7CompactFixEnv full_compact_vars_m7fix_body
      (nvM7MkLiveCfg.hdr, 3#64, 1#64, ()) nvM7MkLiveMem
      (fun () m' => ∃ c' vals' fl' lvl' rsns' ft0' fd0' sc',
        let s' : FullState :=
          { core := { nvM7MkLiveState.core with
                      vals := vals', flags := fl', lvl := lvl', rsns := rsns',
                      frame_trail := nvM7MkLiveState.core.frame_trail.set 0 ft0',
                      frame_dec := nvM7MkLiveState.core.frame_dec.set 0 fd0',
                      trail_end := 0, propagated := 0, cur_level := 0,
                      unflushed := 0#64, confl_ref := 0xFFFFFFFF#64, confl_type := 0#64,
                      cur_vars := 1, unassigned := 1#64 }
            scratch := sc' }
        FullCfgCompat nvM7MkLiveCfg c' ∧ c'.mv = 1 ∧ s'.LengthsOk c' ∧
        fl'[0]? = some 8#32 ∧ nvOneLitF0.Unsat ∧ FullMem c' s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM7MkLiveCfg nvM7MkLiveState ⋆ emp) nvM7MkLiveMem := by
    rw [sep_emp]; exact nvM7MkLiveMem_ok
  have h1nat : (1#64 : BitVec 64).toNat = 1 := rfl
  have h3nat : (3#64 : BitVec 64).toNat = 3 := rfl
  refine full_compact_vars_m7fix_flags_wp m7CompactFixEnv nvM7MkLive_lengths rfl
    (by rw [h1nat, h3nat]; omega)
    (fun nv hnv => by
      obtain rfl : nv = 0 := by rw [h1nat] at hnv; omega
      rw [h3nat]; decide) hm
    fun c' vals' fl' lvl' rsns' ft0' fd0' sc' m' hcompat' hmv_le hmv_eq hl' _ _ _ _ _
        hflp' hm' => ?_
  rw [sep_emp] at hm'
  have hfl0 : fl'[0]? = some 8#32 :=
    (hflp' (fun nv hnv => by
      obtain rfl : nv = 0 := by rw [h1nat] at hnv; omega
      decide)).1 0 (by rw [h1nat]; omega)
  have hcmv : c'.mv = 1 := by
    have h1 := hmv_eq (by rw [h1nat]; decide : (1#64 : BitVec 64).toNat < nvM7MkLiveCfg.mv)
    simpa [h1nat] using h1
  exact ⟨c', vals', fl', lvl', rsns', ft0', fd0', sc', hcompat', hcmv, hl', hfl0,
    nvM7CfF0_unsat, hm'⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) for
`full_sweep_copy_m7fix` on `PH_RED` clause `[1, 2, 4]` referencing zombie var `1`
(`flags[1] = 8#32`): proves it returns `r = 0xFFFFFFFF#64` (drops the clause). -/
theorem nv_m7fix_sweep_copy :
    Func.wp m7CompactFixEnv full_sweep_copy_m7fix_body
      (nvM7MkLiveCfg.hdr, 0#64, 0#64, 3#32, true, ()) nvM7MkLiveMem
      (fun (r, ()) _ => r = 0xFFFFFFFF#64 ∧ nvOneLitF0.Unsat)
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM7MkLiveCfg nvM7MkLiveState ⋆ emp) nvM7MkLiveMem := by
    rw [sep_emp]; exact nvM7MkLiveMem_ok
  have hsp := nvM7MkLive_sparseW
  have h0lt : (0#64 : BitVec 64).toNat = 0 := rfl
  have h3nat : (3#32 : BitVec 32).toNat = 3 := rfl
  refine full_sweep_copy_m7fix_no_zombie_wp m7CompactFixEnv
    (m7cfEnv_row (by simp [m7CompactFixSpecTable]) (fun _ _ _ _ h => h))
    (m7cfEnv_row (by simp [m7CompactFixSpecTable]) (fun _ _ _ _ h => h))
    (c := nvM7MkLiveCfg) (F0 := nvOneLitF0) (F_cur := [[0], [1]]) (s := nvM7MkLiveState)
    (R := emp) (src := 0#64) (dst := 0#64) (old_sz := 3#32) (at_root := true)
    nvM7MkLive_lengths (by decide) (by decide) (by decide) rfl
    (fun j hj => by
      rw [h3nat] at hj
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> decide)
    (fun _ => by
      rw [h0lt, h3nat]
      have hwat0 : ModeWatchesInv [[0], [1]] { nvM7MkLiveState.core with arena_len := 0 } := by
        have hdm : ({ nvM7MkLiveState.core with arena_len := 0 }).dense_mode = 0#64 := rfl
        have hcv : ({ nvM7MkLiveState.core with arena_len := 0 }).cur_vars = 3 := rfl
        unfold ModeWatchesInv; rw [ite_eq_left hdm]
        refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_)
          (fun l1 _ h1 _ _ hp => ?_) (fun l hl => ?_)
        · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
            rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
            rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [fullWatchSizeCore, nvM7MkLiveState] at hp)
        · rw [hcv] at h1
          rcases (by omega : l1 = 0 ∨ l1 = 1 ∨ l1 = 2 ∨ l1 = 3 ∨ l1 = 4 ∨ l1 = 5) with
            rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [fullWatchSizeCore, nvM7MkLiveState] at hp)
        · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
            rfl | rfl | rfl | rfl | rfl | rfl <;> exact WatchSliceOk.empty
      have hb0 : FullBinOnlyWatchesInv [[0], [1]] nvM7MkLiveState.core := by
        have hm' := FullReduceHelpers.modeWatchesInv_to_sparse hsp.2.1.watches rfl
        refine ⟨hm'.layout, fun l hl i hi => ?_⟩
        have hcv : nvM7MkLiveState.core.cur_vars = 3 := rfl
        rw [hcv] at hl
        rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
          rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [fullWatchSizeCore, nvM7MkLiveState] at hi)
      have hnil : fullArenaClauseRefsCore { nvM7MkLiveState.core with arena_len := 0 } = [] := rfl
      have hte1 : ({ nvM7MkLiveState.core with arena_len := 0 }).trail_end = 1 := rfl
      have hw0 : FullWitnessInv nvM7MkLiveCfg nvOneLitF0 [[0], [1]]
          { nvM7MkLiveState.core with arena_len := 0 } :=
        { hsp.2.1 with
          arena :=
            { len_ok := Or.inl rfl
              refs_wf := fun _ hr => by rw [hnil] at hr; cases hr
              shrk_term := fun _ hr => by rw [hnil] at hr; cases hr
              lits_lt := fun _ hr => by rw [hnil] at hr; cases hr
              entails := fun _ hr => by rw [hnil] at hr; cases hr }
          watches := hwat0
          reason_inv := fun i hi hne => by
            rw [hte1] at hi; obtain rfl : i = 0 := by omega
            exact absurd rfl hne
          reason_lit_mem := fun i hi hne => by
            rw [hte1] at hi; obtain rfl : i = 0 := by omega
            exact absurd rfl hne }
      have hent : (cnfOfClauses [[0], [1]]).EntailsClause
          (cnfClause (((nvM7MkLiveState.core.arena.drop (0 + 3)).take 3).map BitVec.toNat)) := by
        rw [CNF.entails_clause_def]; intro α hα
        have h1 : (cnfClause [1]).Sat α :=
          (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
        obtain ⟨lit, hmem, hsat⟩ := CNF.Clause.sat_iff_exists_mem_eq.mp h1
        rw [mem_cnfClause_iff, List.mem_singleton] at hmem
        refine CNF.Clause.sat_iff_exists_mem_eq.mpr ⟨lit, ?_, hsat⟩
        rw [mem_cnfClause_iff, hmem]; decide
      exact ⟨hw0, hb0, hent⟩)
    hm fun r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hz _ _ _ _ _ => ?_
  have hr : r = 0xFFFFFFFF#64 :=
    hz rfl (by decide) ⟨1, by decide, by decide, by decide⟩
  exact ⟨hr, nvM7CfF0_unsat⟩

end ConcreteUnsatNonVacuity

end LeanQbe.T.Examples.Kissat.FullM7CompactFix
