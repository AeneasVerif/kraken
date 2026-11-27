/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3SearchRestart
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3Spec
public import LeanQbe.T.Examples.Kissat.FullFastSchedLemmas
public import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullParseInitLemmas1
import LeanQbe.T.Examples.Kissat.FullM6HdrProof0

/-!
# Kissat Fidelity Step 13 Shard S3-B Proofs — Part 0 (`FullFidelityStep13S3SearchRestartProof0`)

Callee-parametric (`Γ : Env`, `XPost := False`, `0` SAT model proofs) `Func.wp` proofs for the
first `11` Search/Restart/EMA/Init functions in `FullFidelityStep13S3SearchRestart`:
1. `full_scale_delta_m5_step13_wp` (`FullFastSched.schedScaleDeltaSpec`)
2. `full_ema_update_step13_wp` (`Full.fullEmaUpdateSpec`)
3. `full_scale_delta_step13_wp` (`FullFastSched.schedScaleDeltaSpec`)
4. `full_zero_tables2_step13_wp` (`Full.fullZeroTables2Spec`)
5. `m6_hdr_dr_init_step13_wp` (`FullM6Hdr.m6HdrDrMutSpec`)
6. `m6_hdr_dr_update_step13_wp` (`FullM6Hdr.m6HdrDrMutSpec`)
7. `m6_hdr_dr_allow_step13_wp` (`FullM6Hdr.m6HdrDrAllowSpec`)
8. `full_rephase_step13_wp` (`step13RephaseM6Spec`)
9. `full_restart_due_step13_wp` (`Full.fullRestartDueSpec`)
10. `full_restart_step13_wp` (`Full.fullRestartSpec`)
11. `full_init_fresh_var_step13_wp` (`FullFidelityStep7.step7InitFreshVarSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S3

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open Kraken.Bedrock2.Test
open scoped FullArenaTactics

/-! ## 1. Shared Helpers -/

section Helpers

private theorem sr0_add1 {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by bv_omega

private theorem sr0_add1_nat {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + (1 : BitVec 64)).toNat = x.toNat + 1 := sr0_add1 h

private theorem sr0_bv64_add_small {k x : BitVec 64} {n : Nat} (hk : k.toNat = n)
    (hsum : n + x.toNat < 2 ^ 64) : (k + x).toNat = n + x.toNat := by
  rw [BitVec.toNat_add, hk, Nat.mod_eq_of_lt hsum]

private theorem sr0_w2b_pres_of_init {ext ext1 ext' : List (BitVec 64)}
    (h1 : M6HdrExtInitOk ext → ext1 = ext) (h2 : M6ExtW2aPres ext1 ext') :
    M6HdrExtInitOk ext → M6ExtW2aPres ext ext' :=
  fun hi => (h1 hi) ▸ h2

private theorem sr0_arenaPermEq_refl (s : FullCoreState) : FullArenaPermEq s s :=
  ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩

private theorem sr0_arenaPermEq_trans {s1 s2 s3 : FullCoreState}
    (h1 : FullArenaPermEq s1 s2) (h2 : FullArenaPermEq s2 s3) : FullArenaPermEq s1 s3 := by
  refine ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun r hr => ?_⟩
  have hr1 : r ∈ fullArenaClauseRefsCore s2 := by rw [h1.2.1]; exact hr
  obtain ⟨hs1, hg1, hp1⟩ := h1.2.2 r hr
  obtain ⟨hs2, hg2, hp2⟩ := h2.2.2 r hr1
  exact ⟨hs2.trans hs1, hg2.trans hg1, hp2.trans hp1⟩

private theorem sr0_sparse_of_scratch {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (hsp : FullSparseInv c F0 s) (hcore : s'.core = s.core)
    (hlen : s'.LengthsOk c) (hpres : FullExtScratchPres s s') : FullSparseInv c F0 s' :=
  hsp.with_fuel_scratch hlen (by rw [hcore]) hpres

private theorem sr0_backtrack_sparse_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {args : Tup (Arg Val) [i64, i64]} {k : Tup Val [] → Expr Val Cont rs}
    (hBT : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {s : FullState} {R : Mem 64 → Prop}
    (hhdr : args.fst.val = c.hdr) (hsp : FullSparseInv c F0 s)
    (htgt : args.snd.fst.val.toNat ≤ s.core.cur_level) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ s' m', FullSparseInv c F0 s' → FullArenaPermEq s.core s'.core →
      s'.core.cur_vars = s.core.cur_vars →
      s'.core.cur_level = min s.core.cur_level args.snd.fst.val.toNat →
      s'.core.fuel = s.core.fuel → FullExtScratchPres s s' →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_backtrack" args k) m := by
  obtain ⟨⟨hlen, F_cur, hw⟩, hlm, hnd, hscr, hd0⟩ := hsp
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcl_lt : s.core.cur_level < 2 ^ 64 := by
    have := hw.cur_level_le; have := hlen.core_ok.trail_end_le
    have := hlen.core_ok.cur_vars_le; omega
  have htv : args.snd.fst.val.toNat < s.core.cur_level → args.snd.fst.val.toNat < c.max_vars := by
    intro hlt; have := hw.cur_level_le; have := hlen.core_ok.trail_end_le
    have := hlen.core_ok.cur_vars_le; omega
  refine wp_call_of_spec args k
    (hBT _ _ _ _ ⟨c, s, R, hhdr, hlen, hcl_lt, htv, hw.trail_lits_lt, hm, ?_⟩)
  intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m' s' hs' _ _ hcl hpres _ _ _ hw1 _ hm'
  have hperm : FullArenaPermEq s.core s'.core := ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩
  have hsp' : FullSparseInv c F0 s' :=
    ⟨⟨hs', F_cur, hw1 F0 F_cur hw htgt⟩, hlm, hnd, hscr.of_pres hpres.1 (fun _ hr => hr), hd0⟩
  exact hk s' m' hsp' hperm rfl hcl rfl hpres.1 hm'

private theorem sr0_list_eq_replicate {α : Type} {xs : List α} {n : Nat} {v : α}
    (hlen : xs.length = n) (h : ∀ j < n, xs[j]? = some v) : xs = List.replicate n v := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi1 hi2
    have hget := h i (by simpa [hlen] using hi1)
    rw [List.getElem?_eq_getElem hi1, Option.some.injEq] at hget
    simpa [List.getElem_replicate] using hget

private theorem sr0_shl2_fv (fv : BitVec 32) :
    (BitVec.setWidth 64 fv <<< (2 : Nat)).toNat = 4 * fv.toNat := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

private theorem sr0_shl2_add_fv (fv : BitVec 32) (k : Nat) (hk : k < 4) :
    ((BitVec.setWidth 64 fv <<< (2 : Nat)) + BitVec.ofNat 64 k).toNat = 4 * fv.toNat + k := by
  rw [BitVec.toNat_add, sr0_shl2_fv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by have := fv.isLt; omega)]

private theorem sr0_shl1_fv (fv : BitVec 32) :
    (BitVec.setWidth 64 fv <<< (1 : Nat)).toNat = 2 * fv.toNat := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

private theorem sr0_shl1_or1_fv (fv : BitVec 32) :
    ((BitVec.setWidth 64 fv <<< (1 : Nat)) ||| 1#64).toNat = 2 * fv.toNat + 1 := by
  rw [BitVec.toNat_or, sr0_shl1_fv, show (1#64 : BitVec 64).toNat = 1 from rfl]
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_or]
  cases k with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    simp [Nat.testBit_succ, show (2 * fv.toNat) / 2 = fv.toNat by omega,
      show (2 * fv.toNat + 1) / 2 = fv.toNat by omega]

end Helpers

/-! ## 2. `full_scale_delta_m5` & `full_scale_delta` (`schedScaleDeltaSpec`) -/

private theorem sr0_scale_delta_core {Γ : Env} {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost} {delta : BitVec 64}
    (hLog : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_log10_u64" [i64] [i64] a m Q X)
    (hSub : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_sub" [i64, i64] [i64] a m Q X)
    (hMul : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_mul" [i64, i64] [i64] a m Q X)
    (hAdd : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_add" [i64, i64] [i64] a m Q X)
    (hFrom : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_from_u64" [i64] [i64] a m Q X)
    (hTo : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_to_u64" [i64] [i64] a m Q X)
    (hm : (FullMem c s ⋆ R) m) (hQ : ∀ r : BitVec 64, Q (r, ()) m) :
    Func.wp Γ FullFidelityStep13S3.full_scale_delta_m5_body (c.hdr, delta, ()) m Q X := by
  dsimp only [Func.wp, FullFidelityStep13S3.full_scale_delta_m5_body]
  c0_hsteps_nogrp
  · exact hQ _
  · refine wp_join_group (ts := [i64]) (fun _ m1 => m = m1)
      (fun _ _ m1 hm1 => ?_) (fun J hJ => by c0_hsteps <;> exact hJ _ m rfl)
    rcases hm1 with rfl
    refine wp_join_group (ts := [i64]) (fun _ m2 => m = m2)
      (fun _ _ m2 hm2 => ?_) (fun J hJ => by c0_hsteps <;> exact hJ _ m rfl)
    rcases hm2 with rfl
    c0_hsteps_nogrp; c0_call hLog; intro _
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ m3 => m = m3)
      (fun _ _ m3 hm3 => ?_) (fun J hJ => by c0_hsteps <;> exact hJ _ m rfl)
    rcases hm3 with rfl
    refine wp_join_group (ts := [i64]) (fun _ m4 => m = m4)
      (fun _ _ m4 hm4 => ?_)
      (fun J hJ => by
        c0_hsplit
        · c0_hsteps_nogrp; c0_call hSub; intro _; c0_hsteps; exact hJ _ m rfl
        · c0_hsteps_nogrp; c0_call hSub; intro _; c0_hsteps; exact hJ _ m rfl)
    rcases hm4 with rfl
    c0_hsteps_nogrp; c0_call hMul; intro _
    c0_hsteps_nogrp; c0_call hMul; intro _
    c0_hsteps_nogrp; c0_call hAdd; intro _
    c0_hsteps_nogrp; c0_call hFrom; intro _
    c0_hsteps_nogrp; c0_call hMul; intro _
    c0_hsteps_nogrp; c0_call hTo; intro _
    c0_hsteps; exact hQ _

/-- Step-13 `full_scale_delta_m5` satisfies `FullFastSched.schedScaleDeltaSpec`. -/
theorem full_scale_delta_m5_step13_wp (Γ : Env)
    (hLog : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_log10_u64" [i64] [i64] a m Q X)
    (hSub : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_sub" [i64, i64] [i64] a m Q X)
    (hMul : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_mul" [i64, i64] [i64] a m Q X)
    (hAdd : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_add" [i64, i64] [i64] a m Q X)
    (hFrom : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_from_u64" [i64] [i64] a m Q X)
    (hTo : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_to_u64" [i64] [i64] a m Q X) :
    ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.full_scale_delta_m5_body a m Q X := by
  rintro ⟨h, delta, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, _, hm, hQ⟩
  exact sr0_scale_delta_core hLog hSub hMul hAdd hFrom hTo hm hQ

/-- Step-13 `full_scale_delta` satisfies `FullFastSched.schedScaleDeltaSpec` (identical body). -/
theorem full_scale_delta_step13_wp (Γ : Env)
    (hLog : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_log10_u64" [i64] [i64] a m Q X)
    (hSub : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_sub" [i64, i64] [i64] a m Q X)
    (hMul : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_mul" [i64, i64] [i64] a m Q X)
    (hAdd : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_add" [i64, i64] [i64] a m Q X)
    (hFrom : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_from_u64" [i64] [i64] a m Q X)
    (hTo : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_to_u64" [i64] [i64] a m Q X) :
    ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.full_scale_delta_body a m Q X := by
  rintro ⟨h, delta, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, _, hm, hQ⟩
  exact sr0_scale_delta_core hLog hSub hMul hAdd hFrom hTo hm hQ

/-! ## 3. `full_ema_update` (`Full.fullEmaUpdateSpec`) -/

/-- Step-13 `full_ema_update` satisfies `Full.fullEmaUpdateSpec` (mutates only EMA header words). -/
theorem full_ema_update_step13_wp (Γ : Env)
    (hFrom : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_from_u64" [i64] [i64] a m Q X)
    (hAdd : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_add" [i64, i64] [i64] a m Q X)
    (hSub : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_sub" [i64, i64] [i64] a m Q X)
    (hMul : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_mul" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullEmaUpdateSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.full_ema_update_body a m Q X := by
  rintro ⟨h, glue, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  dsimp only [Func.wp, FullFidelityStep13S3.full_ema_update_body]
  c0_hsteps_nogrp
  · exact hQ () s m rfl hlen ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hm
  · c0_call hFrom; intro _
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ m1 => m = m1)
      (fun _ ⟨fb', ⟨⟩⟩ m1 hm1 => ?_)
      (fun J hJ => by
        c0_hsplit
        · c0_hsteps_nogrp; c0_call hSub; intro _; c0_hsteps_nogrp; c0_call hMul; intro _
          c0_hsteps_nogrp; c0_call hAdd; intro _; c0_hsteps; exact hJ _ m rfl
        · c0_hsteps_nogrp; c0_call hSub; intro _; c0_hsteps_nogrp; c0_call hMul; intro _
          c0_hsteps_nogrp; c0_call hSub; intro _; c0_hsteps; exact hJ _ m rfl)
    rcases hm1 with rfl
    c0_hsteps_nogrp
    let s1 : FullState := { s with scratch := { s.scratch with ema_fast_biased := fb' } }
    have hlen1 : s1.LengthsOk c := ⟨hlen.core_ok, { hlen.scratch_ok with }⟩
    refine wp_join_group (ts := [])
      (fun _ m2 => ∃ fe', (FullMem c { s1 with scratch := { s1.scratch with
        ema_fast_exp := fe' } } ⋆ R) m2)
      (fun _ ⟨⟩ m2 ⟨fe', hm2⟩ => ?_)
      (fun J hJ => by
        c0_hsplit
        · c0_hsteps_nogrp; c0_call hMul; intro _
          refine wp_join_group (ts := [i64]) (fun _ m3 => m = m3)
            (fun _ ⟨nfe, ⟨⟩⟩ m3 hm3 => by
              rcases hm3 with rfl; c0_hsteps; exact hJ () _ ⟨nfe, ‹_›⟩)
            (fun J2 hJ2 => by c0_hsteps <;> exact hJ2 _ m rfl)
        · c0_hsteps; exact hJ () _ ⟨s1.scratch.ema_fast_exp, ‹_›⟩)
    let s2 : FullState := { s1 with scratch := { s1.scratch with ema_fast_exp := fe' } }
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ m3 => m2 = m3)
      (fun _ ⟨sb', ⟨⟩⟩ m3 hm3 => ?_)
      (fun J hJ => by
        c0_hsplit
        · c0_hsteps_nogrp; c0_call hSub; intro _; c0_hsteps_nogrp; c0_call hMul; intro _
          c0_hsteps_nogrp; c0_call hAdd; intro _; c0_hsteps; exact hJ _ m2 rfl
        · c0_hsteps_nogrp; c0_call hSub; intro _; c0_hsteps_nogrp; c0_call hMul; intro _
          c0_hsteps_nogrp; c0_call hSub; intro _; c0_hsteps; exact hJ _ m2 rfl)
    rcases hm3 with rfl
    c0_hsteps_nogrp
    let s3 : FullState := { s2 with scratch := { s2.scratch with ema_slow_biased := sb' } }
    have hm3' : (FullMem c s3 ⋆ R) _ := hm
    refine wp_join_group (ts := [])
      (fun _ m4 => ∃ se', (FullMem c { s3 with scratch := { s3.scratch with
        ema_slow_exp := se' } } ⋆ R) m4)
      (fun _ ⟨⟩ m4 ⟨se', hm4⟩ => by
        let s4 : FullState := { s3 with scratch := { s3.scratch with ema_slow_exp := se' } }
        have hlen4 : s4.LengthsOk c := ⟨hlen.core_ok, { hlen.scratch_ok with }⟩
        c0_hsteps; exact hQ () s4 m4 rfl hlen4
          ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hm4)
      (fun J hJ => by
        c0_hsplit
        · c0_hsteps_nogrp; c0_call hMul; intro _
          refine wp_join_group (ts := [i64]) (fun _ m4 => (FullMem c s3 ⋆ R) m4)
            (fun _ ⟨nse, ⟨⟩⟩ m4 hm4 => by
              c0_hsteps; exact hJ () _ ⟨nse, ‹_›⟩)
            (fun J2 hJ2 => by c0_hsteps <;> exact hJ2 _ _ hm3')
        · c0_hsteps; exact hJ () _ ⟨s3.scratch.ema_slow_exp, hm3'⟩)

/-! ## 4. `full_zero_tables2` (`Full.fullZeroTables2Spec`) -/

section ZeroTables2Step13

open Full.FullParseInitHelpers
open scoped Full.FullParseInitTactics

@[irreducible] private def Zt2S13CorePres (s st : FullState) : Prop :=
  st.core =
    { s.core with
      mrk := st.core.mrk, flags := st.core.flags, lvl := st.core.lvl, rsns := st.core.rsns
      frame_trail := st.core.frame_trail, frame_dec := st.core.frame_dec }

private def Zt2S13LoopInv (c : FullCfg) (s st : FullState) (n : Nat) : Prop :=
  n ≤ c.max_vars ∧ Zt2S13CorePres s st ∧ st.LengthsOk c ∧
  Full.FullExtScratchPres s st ∧
  ∀ j < n,
    st.core.mrk[j]? = some 0#8 ∧ st.core.lvl[j]? = some 0#32 ∧
    st.core.rsns[j]? = some 0xFFFFFFFF#32 ∧ st.core.frame_trail[j]? = some 0#32

private theorem zt2_s13_step_ok {c : FullCfg} {s st st' : FullState} {v : Nat}
    (hv : v < c.max_vars) (hinv : Zt2S13LoopInv c s st v)
    (hcore : st'.core =
      { st.core with
        mrk := st.core.mrk.set v 0#8, flags := st.core.flags.set v 0#32,
        lvl := st.core.lvl.set v 0#32, rsns := st.core.rsns.set v 0xFFFFFFFF#32,
        frame_trail := st.core.frame_trail.set v 0#32,
        frame_dec := st.core.frame_dec.set v 0xFFFFFFFF#32 })
    (hsc_ok : st'.scratch.LengthsOk c)
    (hll : st'.scratch.last_learned = st.scratch.last_learned)
    (hel : st'.scratch.extend_len = st.scratch.extend_len) :
    Zt2S13LoopInv c s st' (v + 1) := by
  obtain ⟨_, hag, hlok, hpres, hall⟩ := hinv
  unfold Zt2S13CorePres at hag
  have hc := hlok.core_ok
  refine ⟨by omega, ?_,
    ⟨{ hc with
        cur_vars_ge := by rw [hcore]; exact hc.cur_vars_ge
        cur_vars_le := by rw [hcore]; exact hc.cur_vars_le
        trail_end_le := by rw [hcore]; exact hc.trail_end_le
        propagated_le := by rw [hcore]; exact hc.propagated_le
        arena_len_le := by rw [hcore]; exact hc.arena_len_le
        wlen_le := by rw [hcore]; exact hc.wlen_le
        tmp_len_le := by rw [hcore]; exact hc.tmp_len_le
        min_clr_len_le := by rw [hcore]; exact hc.min_clr_len_le
        vals_len := by rw [hcore]; exact hc.vals_len
        lit_mark_len := by rw [hcore]; exact hc.lit_mark_len
        mrk_len := by rw [hcore]; simp [hc.mrk_len]
        flags_len := by rw [hcore]; simp [hc.flags_len]
        lvl_len := by rw [hcore]; simp [hc.lvl_len]
        rsns_len := by rw [hcore]; simp [hc.rsns_len]
        trl_len := by rw [hcore]; exact hc.trl_len
        trail_pos_len := by rw [hcore]; exact hc.trail_pos_len
        tmp_len_arr := by rw [hcore]; exact hc.tmp_len_arr
        min_clr_len_arr := by rw [hcore]; exact hc.min_clr_len_arr
        frame_trail_len := by rw [hcore]; simp [hc.frame_trail_len]
        frame_dec_len := by rw [hcore]; simp [hc.frame_dec_len]
        wvec_len := by rw [hcore]; exact hc.wvec_len
        repr_len := by rw [hcore]; exact hc.repr_len
        min_stk_len := by rw [hcore]; exact hc.min_stk_len
        arena_len_arr := by rw [hcore]; exact hc.arena_len_arr
        wstk_len_arr := by rw [hcore]; exact hc.wstk_len_arr }, hsc_ok⟩,
    ⟨hll.trans hpres.1, hel.trans hpres.2⟩, fun j hj => ?_⟩
  · unfold Zt2S13CorePres
    rw [hcore]
    exact congrArg (fun x =>
      { x with
        mrk := st.core.mrk.set v 0#8, flags := st.core.flags.set v 0#32,
        lvl := st.core.lvl.set v 0#32, rsns := st.core.rsns.set v 0xFFFFFFFF#32,
        frame_trail := st.core.frame_trail.set v 0#32,
        frame_dec := st.core.frame_dec.set v 0xFFFFFFFF#32 }) hag
  rw [hcore]
  by_cases hje : j = v
  · subst hje
    exact ⟨List.getElem?_set_self (by rw [hc.mrk_len]; exact hv),
      List.getElem?_set_self (by rw [hc.lvl_len]; exact hv),
      List.getElem?_set_self (by rw [hc.rsns_len]; exact hv),
      List.getElem?_set_self (by rw [hc.frame_trail_len]; omega)⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hall j (by omega)
    simp only [List.getElem?_set_ne (Ne.symm hje)]
    exact ⟨h1, h2, h3, h4⟩

private theorem zt2_s13_tail6_wp (Γ : Env) {c : FullCfg} {st1 : FullState}
    {v_v addr_fl : Val i64} {m : Mem 64} {Q : Post []} {X : XPost} {R : Mem 64 → Prop}
    {k : Expr Val Cont []}
    (haddr : addr_fl = c.pFlags + v_v * (4 : BitVec 64))
    (hfl1 : st1.core.flags.length = c.max_vars) (hhp1 : st1.scratch.heap.length = c.max_vars)
    (hps1 : st1.scratch.pos.length = c.max_vars) (hqp1 : st1.scratch.q_prev.length = c.max_vars)
    (hqn1 : st1.scratch.q_next.length = c.max_vars)
    (hqs1 : st1.scratch.q_stamp.length = c.max_vars)
    (hvv : v_v.toNat < c.max_vars) (hm1 : (FullMem c st1 ⋆ R) m)
    (hk : ∀ m',
      (FullMem c
        ({ core := { st1.core with flags := st1.core.flags.set v_v.toNat 0#32 },
           scratch := { st1.scratch with
             heap := st1.scratch.heap.set v_v.toNat 0#32,
             pos := st1.scratch.pos.set v_v.toNat 0xFFFFFFFF#32,
             q_prev := st1.scratch.q_prev.set v_v.toNat 0xFFFFFFFF#32,
             q_next := st1.scratch.q_next.set v_v.toNat 0xFFFFFFFF#32,
             q_stamp := st1.scratch.q_stamp.set v_v.toNat 0#32 } } :
          FullState) ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X
      (Expr.store (Arg.imm (t := i32) 0) (Arg.var addr_fl)
        (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
         Expr.let_ (Op.mk (.add i64) (Arg.var c.pHeap, Arg.var p.1, ())) fun p =>
         Expr.store (Arg.imm (t := i32) 0) (Arg.var p.1)
           (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
            Expr.let_ (Op.mk (.add i64) (Arg.var c.pPos, Arg.var p.1, ())) fun p =>
            Expr.store (Arg.imm (t := i32) 4294967295) (Arg.var p.1)
              (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
               Expr.let_ (Op.mk (.add i64) (Arg.var c.pQPrev, Arg.var p.1, ())) fun p =>
               Expr.store (Arg.imm (t := i32) 4294967295) (Arg.var p.1)
                 (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var c.pQNext, Arg.var p.1, ())) fun p =>
                  Expr.store (Arg.imm (t := i32) 4294967295) (Arg.var p.1)
                    (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
                     Expr.let_ (Op.mk (.add i64) (Arg.var c.pQStamp, Arg.var p.1, ())) fun p =>
                     Expr.store (Arg.imm (t := i32) 0) (Arg.var p.1) k)))))) m := by
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmx
  subst haddr
  fp_head_steps
  exact hk m hm

/-- Step-13 `full_zero_tables2` (`ph[v] = 0`) satisfies canonical `Full.fullZeroTables2Spec`. -/
theorem full_zero_tables2_step13_wp (Γ : Env) :
    ∀ a m Q X, fullZeroTables2Spec a m Q X →
      Func.wp Γ FullFidelityStep13S3.full_zero_tables2_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv; unfold dimacsBound at hmx
  have hmx_to : (BitVec.ofNat 64 c.max_vars).toNat = c.max_vars := bv64_ofNat_toNat (by omega)
  unfold Func.wp FullFidelityStep13S3.full_zero_tables2_body
  fp_head_steps
  refine wp_loop_inv
    (fun (v_v : Tup Val [i64]) ml => ∃ st : FullState, (FullMem c st ⋆ R) ml ∧
      Zt2S13LoopInv c s st v_v.1.toNat)
    (fun v_v _ => c.max_vars - v_v.1.toNat) ?_ ?_
  · intro L hL; fp_head_steps
    exact hL (0#64, ()) m ⟨s, hm, ⟨Nat.zero_le _, by unfold Zt2S13CorePres; rfl,
      hlen, ⟨rfl, rfl⟩, fun _ h0 => by cases h0⟩⟩
  · intro L ⟨v_v, ⟨⟩⟩ ml ⟨st, hm, hinv⟩ hL
    have hv_le := hinv.1; have hlok := hinv.2.2.1; dsimp only at hv_le
    have hc := hlok.core_ok; have hs := hlok.scratch_ok
    have hmrk_l := hc.mrk_len; have hfl_l := hc.flags_len; have hlvl_l := hc.lvl_len
    have hrsns_l := hc.rsns_len; have hft_l := hc.frame_trail_len; have hfd_l := hc.frame_dec_len
    have hph_l := hs.phases_len; have hpt_l := hs.phases_target_len
    have hpb_l := hs.phases_best_len; have hwb_l := hs.walk_best_len
    have hsc_l := hs.score_len; have hsg_l := hs.sim_sig_len
    have hhp_l := hs.heap_len_arr; have hps_l := hs.pos_len
    have hqp_l := hs.q_prev_len; have hqn_l := hs.q_next_len; have hqs_l := hs.q_stamp_len
    fp_head_steps
    refine wp_jnz_of (fun hvlt => ?_) (fun hvge => ?_)
    · have hvlt' : v_v.toNat < c.max_vars := by
        dsimp only [Arg.val_var, liftCmp, CmpOp.evalBits, Ty.hasFloat] at hvlt
        rw [BitVec.ult, decide_eq_true_eq, hmx_to] at hvlt; exact hvlt
      have hv1 : (v_v + 1#64).toNat = v_v.toNat + 1 :=
        sr0_add1 (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hvlt') (Nat.lt_trans hmx (by decide)))
      clear hc hlok hfl_l hhp_l hps_l hqp_l hqn_l hqs_l hs
      fp_head_steps
      have hc0 := hinv.2.2.1.core_ok; have hs0 := hinv.2.2.1.scratch_ok
      obtain ⟨st1, hm1, hcore1, hll1, hel1, hfl1, hhp1, hps1, hqp1, hqn1, hqs1, hsc_ok1⟩ :
          ∃ st1 : FullState, (FullMem c st1 ⋆ R) m ∧
            st1.core = { st.core with
              mrk := st.core.mrk.set v_v.toNat 0#8, lvl := st.core.lvl.set v_v.toNat 0#32,
              rsns := st.core.rsns.set v_v.toNat 0xFFFFFFFF#32,
              frame_trail := st.core.frame_trail.set v_v.toNat 0#32,
              frame_dec := st.core.frame_dec.set v_v.toNat 0xFFFFFFFF#32 } ∧
            st1.scratch.last_learned = st.scratch.last_learned ∧
            st1.scratch.extend_len = st.scratch.extend_len ∧
            st1.core.flags.length = c.max_vars ∧ st1.scratch.heap.length = c.max_vars ∧
            st1.scratch.pos.length = c.max_vars ∧ st1.scratch.q_prev.length = c.max_vars ∧
            st1.scratch.q_next.length = c.max_vars ∧ st1.scratch.q_stamp.length = c.max_vars ∧
            st1.scratch.LengthsOk c :=
        ⟨_, hm, rfl, rfl, rfl, hc0.flags_len, hs0.heap_len_arr, hs0.pos_len, hs0.q_prev_len,
          hs0.q_next_len, hs0.q_stamp_len,
          { hs0 with
            phases_len := by simp [hph_l], phases_target_len := by simp [hpt_l],
            phases_best_len := by simp [hpb_l], walk_best_len := by simp [hwb_l],
            score_len := by simp [hsc_l], sim_sig_len := by simp [hsg_l] }⟩
      clear hm hc0 hs0
      refine zt2_s13_tail6_wp Γ rfl hfl1 hhp1 hps1 hqp1 hqn1 hqs1 hvlt' hm1 fun m2 hm2 => ?_
      fp_head_steps
      exact hL (v_v + 1#64, ()) m2
        (by dsimp only; rw [hv1]; exact Nat.sub_lt_sub_left hvlt' (Nat.lt_succ_self _))
        ⟨_, hm2, by
          dsimp only; rw [hv1]
          exact zt2_s13_step_ok hvlt' hinv (by rw [hcore1])
            { hsc_ok1 with
              heap_len_arr := by simp [hhp1], pos_len := by simp [hps1],
              q_prev_len := by simp [hqp1], q_next_len := by simp [hqn1],
              q_stamp_len := by simp [hqs1] } hll1 hel1⟩
    · have hvge' : ¬ v_v.toNat < c.max_vars := by
        dsimp only [Arg.val_var, liftCmp, CmpOp.evalBits, Ty.hasFloat] at hvge
        rw [BitVec.ult, decide_eq_false_iff_not, hmx_to] at hvge; exact hvge
      have hveq : v_v.toNat = c.max_vars := Nat.le_antisymm hv_le (Nat.not_lt.mp hvge')
      obtain ⟨_, hag, _, hpres, hall⟩ := hinv
      rw [hveq] at hall
      fp_head_steps
      have hmrk : st.core.mrk = List.replicate c.max_vars 0#8 :=
        sr0_list_eq_replicate hmrk_l fun j hj => (hall j hj).1
      have hlvl : st.core.lvl = List.replicate c.max_vars 0#32 :=
        sr0_list_eq_replicate hlvl_l fun j hj => (hall j hj).2.1
      have hrsns : st.core.rsns = List.replicate c.max_vars 0xFFFFFFFF#32 :=
        sr0_list_eq_replicate hrsns_l fun j hj => (hall j hj).2.2.1
      let ftrl' := st.core.frame_trail.set c.max_vars 0#32
      let fdec' := st.core.frame_dec.set c.max_vars 0xFFFFFFFF#32
      have hftrl_len : ftrl'.length = c.max_vars + 1 := by simp [ftrl', hft_l]
      have hfdec_len : fdec'.length = c.max_vars + 1 := by simp [fdec', hfd_l]
      have hftrl : ftrl' = List.replicate (c.max_vars + 1) 0#32 := by
        refine sr0_list_eq_replicate hftrl_len fun j hj => ?_
        by_cases hje : j = c.max_vars
        · subst hje; exact List.getElem?_set_self (by rw [hft_l]; exact Nat.lt_succ_self _)
        · rw [List.getElem?_set_ne (Ne.symm hje)]
          exact (hall j (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hj) hje)).2.2.2
      have hcore_eq :
          { s.core with
            mrk := List.replicate c.max_vars 0#8, flags := st.core.flags,
            lvl := List.replicate c.max_vars 0#32,
            rsns := List.replicate c.max_vars 0xFFFFFFFF#32,
            frame_trail := List.replicate (c.max_vars + 1) 0#32, frame_dec := fdec' } =
          { st.core with
            frame_trail := st.core.frame_trail.set c.max_vars 0#32,
            frame_dec := st.core.frame_dec.set c.max_vars 0xFFFFFFFF#32 } := by
        unfold Zt2S13CorePres at hag
        rw [hag, hmrk, hlvl, hrsns, ← hftrl]
      have hm_out : (FullMem c { s with
          core := { s.core with
            mrk := List.replicate c.max_vars 0#8, flags := st.core.flags,
            lvl := List.replicate c.max_vars 0#32, rsns := List.replicate c.max_vars 0xFFFFFFFF#32,
            frame_trail := List.replicate (c.max_vars + 1) 0#32, frame_dec := fdec' },
          scratch := st.scratch } ⋆ R) m := by
        rw [hcore_eq]; dsimp only [ftrl', fdec']; rw [hmx_to] at hm; exact hm
      exact hQ st.core.flags fdec' st.scratch m hfl_l hfdec_len hs hpres hm_out

end ZeroTables2Step13

/-! ## 5. `m6_hdr_dr_{init,update,allow}` (`m6HdrDrMutSpec`, `m6HdrDrAllowSpec`) -/

section M6HdrDrStep13

open scoped FullM6Hdr.M6HdrTactics

/-- Step-13 `m6_hdr_dr_init` (`se = 0x3FF0000000000000ULL`) satisfies `m6HdrDrMutSpec`. -/
theorem m6_hdr_dr_init_step13_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrDrMutSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.m6_hdr_dr_init_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrDrMutSpec_elim hs
  unfold Func.wp FullFidelityStep13S3.m6_hdr_dr_init_body
  c0_hsteps_nogrp
  c0_call hEnsure
  refine m6ExtEnsureInitSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hpres1 hm1 => ?_
  have hl1 : ext1.length = 288 := hinit1.toOk.len
  rw [fullM6HdrMem_iff] at hm1
  c0_hsteps
  · exact hQ ext1 m1 hinit1 (sr0_w2b_pres_of_init hpres1 (M6ExtW2aPres.refl ext1))
      ((fullM6HdrMem_iff ..).mpr hm1)
  · refine hQ _ _ ?_ ?_ ((fullM6HdrMem_iff ..).mpr (by assumption))
    · exact ((((((hinit1.set_pos _ (by decide)).set_pos _ (by decide)).set_pos _
        (by decide)).set_pos _ (by decide)).set_pos _ (by decide)).set_pos _
        (by decide)).set_pos _ (by decide)
    · refine sr0_w2b_pres_of_init hpres1 ?_
      exact (((((M6ExtW2aPres.set_w2b _ (by decide) (by decide)).trans
        (M6ExtW2aPres.set_w2b _ (by decide) (by decide))).trans
        (M6ExtW2aPres.set_w2b _ (by decide) (by decide))).trans
        (M6ExtW2aPres.set_w2b _ (by decide) (by decide))).trans
        (M6ExtW2aPres.set_w2b _ (by decide) (by decide))).trans
        ((M6ExtW2aPres.set_w2b _ (by decide) (by decide)).trans
          (M6ExtW2aPres.set_w2b _ (by decide) (by decide)))

/-- Step-13 `m6_hdr_dr_update` (`f64u_*`) satisfies `m6HdrDrMutSpec`. -/
theorem m6_hdr_dr_update_step13_wp (Γ : Env)
    (hDrInit : ∀ a m Q X, m6HdrDrMutSpec a m Q X → Γ "m6_hdr_dr_init" [i64] [] a m Q X)
    (hFrom : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_from_u64" [i64] [i64] a m Q X)
    (hAdd : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_add" [i64, i64] [i64] a m Q X)
    (hSub : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_sub" [i64, i64] [i64] a m Q X)
    (hMul : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_mul" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m6HdrDrMutSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.m6_hdr_dr_update_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrDrMutSpec_elim hs
  unfold Func.wp FullFidelityStep13S3.m6_hdr_dr_update_body
  c0_hsteps_nogrp
  c0_call hDrInit
  refine m6HdrDrMutSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hw1 hm1 => ?_
  have hl1 : ext1.length = 288 := hinit1.toOk.len
  rw [fullM6HdrMem_iff] at hm1
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (mode, ()) m2 => m1 = m2 ∧ (mode = 0#64 ∨ mode = 1#64))
    (fun _ (mode, ()) m2 ⟨hm2, hmode⟩ => ?_)
    (fun _ hJm => by
      c0_hsteps
      · exact hJm (1#64, ()) m1 ⟨rfl, Or.inr rfl⟩
      · exact hJm (0#64, ()) m1 ⟨rfl, Or.inl rfl⟩)
  rcases hm2 with rfl
  have hmode_le : mode.toNat ≤ 1 := by rcases hmode with rfl | rfl <;> decide
  have hp_eq : ((2 : BitVec 64) + mode).toNat = 2 + mode.toNat :=
    sr0_bv64_add_small (n := 2) rfl (by omega)
  have hsb_eq : ((4 : BitVec 64) + mode).toNat = 4 + mode.toNat :=
    sr0_bv64_add_small (n := 4) rfl (by omega)
  have hse_eq : ((6 : BitVec 64) + mode).toNat = 6 + mode.toNat :=
    sr0_bv64_add_small (n := 6) rfl (by omega)
  have hp_lt : ((2 : BitVec 64) + mode).toNat < ext1.length := by rw [hl1, hp_eq]; omega
  have hsb_lt : ((4 : BitVec 64) + mode).toNat < ext1.length := by rw [hl1, hsb_eq]; omega
  have hse_lt : ((6 : BitVec 64) + mode).toNat < ext1.length := by rw [hl1, hse_eq]; omega
  c0_hsteps_nogrp
  · c0_hsteps
    refine hQ _ _ ?_ ?_ ((fullM6HdrMem_iff ..).mpr (by assumption))
    · exact (((hinit1.set_pos _ (by decide)).set_pos _ (by rw [hp_eq]; omega)).set_pos _
        (by rw [hsb_eq]; omega)).set_pos _ (by rw [hse_eq]; omega)
    · intro hi
      exact (hw1 hi).trans (((M6ExtW2aPres.set_w2b _ (by decide) (by decide)).trans
        (M6ExtW2aPres.set_w2b _ (by rw [hp_eq]; omega) (by rw [hp_eq]; omega))).trans
        ((M6ExtW2aPres.set_w2b _ (by rw [hsb_eq]; omega) (by rw [hsb_eq]; omega)).trans
          (M6ExtW2aPres.set_w2b _ (by rw [hse_eq]; omega) (by rw [hse_eq]; omega))))
  · obtain ⟨ext2, hm2, hl2, hinit2, hw12⟩ :
        ∃ ext2 : List (BitVec 64), (FullMem c s ⋆ (array64 (c.hdr - 2304) ext2 ⋆ R)) m ∧
          ext2.length = 288 ∧ M6HdrExtInitOk ext2 ∧ M6ExtW2aPres ext1 ext2 :=
      ⟨_, hm, by simp [hl1], hinit1.set_pos _ (by rw [hp_eq]; omega),
        M6ExtW2aPres.set_w2b _ (by rw [hp_eq]; omega) (by rw [hp_eq]; omega)⟩
    have hsb2_lt : ((4 : BitVec 64) + mode).toNat < ext2.length := by rw [hl2, hsb_eq]; omega
    have hse2_lt : ((6 : BitVec 64) + mode).toNat < ext2.length := by rw [hl2, hse_eq]; omega
    let m2 := m
    have hm2' : (FullMem c s ⋆ (array64 (c.hdr - 2304) ext2 ⋆ R)) m2 := hm2
    clear hm hm2
    refine wp_join_group (ts := [i64]) (fun _ m3 => m2 = m3)
      (fun _ (_d, ()) m3 hm3 => ?_) (fun _ hJd => by c0_hsteps <;> exact hJd (_, ()) m2 rfl)
    rcases hm3 with rfl
    c0_hsteps_nogrp; c0_call hFrom; intro _
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ m3 => m2 = m3)
      (fun _ (sb, ()) m3 hm3 => ?_)
      (fun _ hJsb => by
        c0_hsplit
        · c0_hsteps_nogrp; c0_call hSub; intro _; c0_hsteps_nogrp; c0_call hMul; intro _
          c0_hsteps_nogrp; c0_call hAdd; intro _; c0_hsteps; exact hJsb (_, ()) m2 rfl
        · c0_hsteps_nogrp; c0_call hSub; intro _; c0_hsteps_nogrp; c0_call hMul; intro _
          c0_hsteps_nogrp; c0_call hSub; intro _; c0_hsteps; exact hJsb (_, ()) m2 rfl)
    rcases hm3 with rfl
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ m3 => m2 = m3)
      (fun _ (se, ()) m3 hm3 => ?_)
      (fun _ hJse => by
        c0_hsplit
        · c0_hsteps_nogrp; c0_call hMul; intro _
          refine wp_join_group (ts := [i64]) (fun _ m4 => m2 = m4)
            (fun _ (se1, ()) m4 hm4 => by rcases hm4 with rfl; exact hJse (se1, ()) m2 rfl)
            (fun _ hJse1 => by c0_hsteps <;> exact hJse1 (_, ()) m2 rfl)
        · c0_hsteps; exact hJse (_, ()) m2 rfl)
    rcases hm3 with rfl
    c0_hsteps
    refine hQ _ _ ?_ ?_ ((fullM6HdrMem_iff ..).mpr (by assumption))
    · exact (hinit2.set_pos sb (by rw [hsb_eq]; omega)).set_pos se (by rw [hse_eq]; omega)
    · intro hi
      exact ((hw1 hi).trans hw12).trans
        ((M6ExtW2aPres.set_w2b sb (by rw [hsb_eq]; omega) (by rw [hsb_eq]; omega)).trans
          (M6ExtW2aPres.set_w2b se (by rw [hse_eq]; omega) (by rw [hse_eq]; omega)))

/-- Step-13 `m6_hdr_dr_allow` (`f64u_sub`, `f64u_div`) satisfies `m6HdrDrAllowSpec`. -/
theorem m6_hdr_dr_allow_step13_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X)
    (hSub : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_sub" [i64, i64] [i64] a m Q X)
    (hDiv : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_div" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m6HdrDrAllowSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.m6_hdr_dr_allow_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrDrAllowSpec_elim hs
  unfold Func.wp FullFidelityStep13S3.m6_hdr_dr_allow_body
  c0_hsteps_nogrp
  c0_call hEnsure
  refine m6ExtEnsureInitSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hpres1 hm1 => ?_
  have hl1 : ext1.length = 288 := hinit1.toOk.len
  rw [fullM6HdrMem_iff] at hm1
  c0_hsteps_nogrp
  · exact hQ true ext1 m1 hinit1 hpres1 ((fullM6HdrMem_iff ..).mpr hm1)
  · refine wp_join_group (ts := [i64]) (fun (mode, ()) m2 => m1 = m2 ∧ (mode = 0#64 ∨ mode = 1#64))
      (fun _ (mode, ()) m2 ⟨hm2, hmode⟩ => ?_)
      (fun _ hJm => by
        c0_hsteps
        · exact hJm (1#64, ()) m1 ⟨rfl, Or.inr rfl⟩
        · exact hJm (0#64, ()) m1 ⟨rfl, Or.inl rfl⟩)
    rcases hm2 with rfl
    have hmode_le : mode.toNat ≤ 1 := by rcases hmode with rfl | rfl <;> decide
    have hsb_lt : ((4 : BitVec 64) + mode).toNat < ext1.length := by
      rw [hl1, sr0_bv64_add_small (n := 4) rfl (by omega)]; omega
    have hse_lt : ((6 : BitVec 64) + mode).toNat < ext1.length := by
      rw [hl1, sr0_bv64_add_small (n := 6) rfl (by omega)]; omega
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ m2 => m1 = m2)
      (fun _ _ m2 hm2 => by
        rcases hm2 with rfl; c0_hsteps
        exact hQ _ ext1 m1 hinit1 hpres1 ((fullM6HdrMem_iff ..).mpr hm1))
      (fun _ hJval => by
        c0_hsplit
        · c0_hsteps_nogrp; c0_call hSub; intro _
          c0_hsteps_nogrp
          · exact hQ true ext1 m1 hinit1 hpres1 ((fullM6HdrMem_iff ..).mpr hm1)
          · c0_call hDiv; intro _; c0_hsteps; exact hJval (_, ()) m1 rfl
        · c0_hsteps; exact hJval (_, ()) m1 rfl)

end M6HdrDrStep13

/-! ## 6. `full_rephase` (`step13RephaseM6Spec`) -/

/-- Step-13 `full_rephase` satisfies `step13RephaseM6Spec`: `FullM6HdrMem`-threaded rephase
calling `full_backtrack`, `full_walk` (`step13WarmupM6Spec`), `f64u_nlogpown`, and `f64u_to_u64`. -/
theorem full_rephase_step13_wp (Γ : Env)
    (hBT : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hWalk : ∀ a m Q X, step13WarmupM6Spec a m Q X → Γ "full_walk" [i64] [] a m Q X)
    (hNlog : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_nlogpown" [i64, i64] [i64] a m Q X)
    (hTo : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_to_u64" [i64] [i64] a m Q X) :
    ∀ a m Q X, step13RephaseM6Spec a m Q X →
      Func.wp Γ FullFidelityStep13S3.full_rephase_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, ext, s, R, rfl, hinv, hm, hQ⟩
  have hcfg := hinv.cfgOk; have hext := hinv.extOk; have hsp := hinv.sparse
  have hlen := hsp.lengths; have hmax := c.hmaxv; unfold dimacsBound at hmax
  rw [fullM6HdrMem_iff] at hm
  dsimp only [Func.wp, FullFidelityStep13S3.full_rephase_body]
  c0_hsteps_nogrp
  · let s0 : FullState := { s with scratch := { s.scratch with
      rephase_limit := s.scratch.mode_confl_lim } }
    have hinv0 : FullM6HdrInv c F0 ext s0 := .mk_inv hcfg hext
      (sr0_sparse_of_scratch hsp rfl ⟨hlen.core_ok, { hlen.scratch_ok with }⟩ ⟨rfl, rfl⟩)
    exact hQ ext s0 _ hinv0 (sr0_arenaPermEq_refl _) (fun hne => absurd hc hne)
      (Nat.le_refl _) (Nat.le_refl _) ⟨rfl, rfl⟩ ((fullM6HdrMem_iff ..).mpr ‹_›)
  · refine wp_join_group (ts := [])
      (fun _ m1 => ∃ s1, FullSparseInv c F0 s1 ∧ FullArenaPermEq s.core s1.core ∧
        s1.core.cur_level = 0 ∧ s1.core.fuel = s.core.fuel ∧ FullExtScratchPres s s1 ∧
        (FullMem c s1 ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) m1)
      (fun _ ⟨⟩ m1 ⟨s1, hsp1, hperm1, hcl1, hfuel1, hpres1, hm1⟩ => ?_)
      (fun J hJ => by
        c0_hsplit
        · c0_hsteps_nogrp
          refine sr0_backtrack_sparse_call hBT rfl hsp (Nat.zero_le _) hm
            fun sB mB hspB hpermB _ hclB hfuelB hpresB hmB => ?_
          c0_hsteps; exact hJ () mB ⟨sB, hspB, hpermB, by simpa using hclB, hfuelB, hpresB, hmB⟩
        · have hcl0 : s.core.cur_level = 0 := by
            have := hlen.core_ok.trail_end_le; have := hlen.core_ok.cur_vars_le
            obtain ⟨_, hw⟩ := hsp.1.witness; have := hw.cur_level_le
            have h0 : (0 : BitVec 64).toNat = 0 := rfl
            rw [Nat.mod_eq_of_lt (by omega : s.core.cur_level < 2 ^ 64)] at hc; omega
          c0_hsteps; exact hJ () m ⟨s, hsp, sr0_arenaPermEq_refl _, hcl0, rfl, ⟨rfl, rfl⟩, hm⟩)
    have hlen1 := hsp1.lengths
    c0_hsteps_nogrp
    let s2 : FullState := { s1 with scratch := { s1.scratch with
      rephased := s1.scratch.rephased + 1#64 } }
    have hlen2 : s2.LengthsOk c := ⟨hlen1.core_ok, { hlen1.scratch_ok with }⟩
    have hsp2 : FullSparseInv c F0 s2 := sr0_sparse_of_scratch hsp1 rfl hlen2 ⟨rfl, rfl⟩
    have hcv2_le : s2.core.cur_vars ≤ c.max_vars := hlen2.core_ok.cur_vars_le
    refine wp_join_group (ts := [])
      (fun _ m3 => ∃ ext3 s3, FullM6HdrInv c F0 ext3 s3 ∧ FullArenaPermEq s.core s3.core ∧
        s3.core.cur_vars = s2.core.cur_vars ∧ s3.core.cur_level = 0 ∧
        s3.core.fuel.toNat ≤ s.core.fuel.toNat ∧ FullExtScratchPres s s3 ∧
        (FullMem c s3 ⋆ (array64 (c.hdr - 2304) ext3 ⋆ R)) m3)
      (fun _ ⟨⟩ m3 ⟨ext3, s3, hinv3, hperm3, hcv3, hcl3, hfuel3, hpres3, hm3⟩ => ?_)
      (fun J_ph hJ_ph => ?_)
    · -- Post-switch: copy `ph[0..cv)` to `pt[0..cv)`, set `target_assigned = 0`, `rephase_limit`
      c0_hsteps_nogrp
      refine wp_loop_group (ts := [i64])
        (fun nk ⟨k, ⟨⟩⟩ mK => ∃ sK, k.toNat ≤ s2.core.cur_vars ∧
          nk = s2.core.cur_vars - k.toNat ∧ sK.core = s3.core ∧ sK.LengthsOk c ∧
          FullExtScratchPres s3 sK ∧ (FullMem c sK ⋆ (array64 (c.hdr - 2304) ext3 ⋆ R)) mK) ?_ ?_
      · intro JK nk ⟨k, ⟨⟩⟩ mK hJK ⟨sK, hk_le, hnk, hcoreK, hlenK, hpresK, hmK⟩
        c0_hsplit
        · have hk_lt : k.toNat < s2.core.cur_vars := by
            rw [Nat.mod_eq_of_lt (by omega : s2.core.cur_vars < 2 ^ 64)] at hc; exact hc
          have hk_ph : k.toNat < sK.scratch.phases.length := by
            rw [hlenK.scratch_ok.phases_len]; omega
          have hk_pt : k.toNat < sK.scratch.phases_target.length := by
            rw [hlenK.scratch_ok.phases_target_len]; omega
          have hk1 : (k + 1).toNat = k.toNat + 1 := sr0_add1_nat (by omega)
          c0_hsteps
          let sK' : FullState := { sK with scratch := { sK.scratch with
            phases_target := sK.scratch.phases_target.set k.toNat
              (sK.scratch.phases[k.toNat]'hk_ph) } }
          have hlenK' : sK'.LengthsOk c := ⟨hlenK.core_ok,
            { hlenK.scratch_ok with
              phases_target_len := by simp [sK', hlenK.scratch_ok.phases_target_len] }⟩
          exact hJK (s2.core.cur_vars - (k.toNat + 1)) _ _ (by omega)
            ⟨sK', by rw [hk1]; omega, by rw [hk1], hcoreK, hlenK', hpresK, ‹_›⟩
        · c0_hsteps_nogrp; c0_call hNlog; intro _
          c0_hsteps_nogrp; c0_call hTo; intro sc_v
          c0_hsteps
          let sF : FullState := { sK with scratch := { sK.scratch with
            target_assigned := 0#64, rephase_limit := sK.scratch.conflicts + 1000#64 * sc_v } }
          have hlenF : sF.LengthsOk c := ⟨hlenK.core_ok, { hlenK.scratch_ok with }⟩
          have hinvF : FullM6HdrInv c F0 ext3 sF :=
            .mk_inv hcfg hinv3.extOk (sr0_sparse_of_scratch hinv3.sparse hcoreK hlenF hpresK)
          exact hQ ext3 sF _ hinvF (by rw [hcoreK]; exact hperm3)
            (fun _ => by rw [hcoreK]; exact hcl3)
            (by rw [hcoreK, hcl3]; exact Nat.zero_le _) (by rw [hcoreK]; exact hfuel3)
            ⟨hpresK.1.trans hpres3.1, hpresK.2.trans hpres3.2⟩ ((fullM6HdrMem_iff ..).mpr ‹_›)
      · intro JK hJK; c0_hsteps
        exact hJK s2.core.cur_vars (0#64, ()) m3
          ⟨s3, Nat.zero_le _, by simp, rfl, hinv3.sparse.lengths, ⟨rfl, rfl⟩, hm3⟩
    · -- 4-way rephase dispatch (`step == 0 || 3`, `1 || 4`, `2`, `5`)
      c0_hsteps_nogrp
      refine wp_join_group (ts := [])
        (fun _ mA => (FullMem c s2 ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) mA)
        (fun _ ⟨⟩ mA hmA => by
          -- `step == 0 || step == 3`: copy `pb` -> `ph`, `best_assigned = 0`
          refine wp_loop_group (ts := [i64])
            (fun nv ⟨v, ⟨⟩⟩ mV => ∃ sV, v.toNat ≤ s2.core.cur_vars ∧
              nv = s2.core.cur_vars - v.toNat ∧ sV.core = s2.core ∧ sV.LengthsOk c ∧
              FullExtScratchPres s2 sV ∧
              (FullMem c sV ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) mV) ?_ ?_
          · intro JV nv ⟨v, ⟨⟩⟩ mV hJV ⟨sV, hv_le, hnv, hcoreV, hlenV, hpresV, hmV⟩
            c0_hsplit
            · have hv_lt : v.toNat < s2.core.cur_vars := by
                rw [Nat.mod_eq_of_lt (by omega : s2.core.cur_vars < 2 ^ 64)] at hc; exact hc
              have hv_pb : v.toNat < sV.scratch.phases_best.length := by
                rw [hlenV.scratch_ok.phases_best_len]; omega
              have hv_ph : v.toNat < sV.scratch.phases.length := by
                rw [hlenV.scratch_ok.phases_len]; omega
              have hv1 : (v + 1).toNat = v.toNat + 1 := sr0_add1_nat (by omega)
              c0_hsteps_nogrp
              refine wp_join_group (ts := [])
                (fun _ mW => ∃ sW, sW.core = s2.core ∧ sW.LengthsOk c ∧
                  FullExtScratchPres s2 sW ∧
                  (FullMem c sW ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) mW)
                (fun _ ⟨⟩ mW ⟨sW, hcoreW, hlenW, hpresW, hmW⟩ => by
                  c0_hsteps; exact hJV (s2.core.cur_vars - (v.toNat + 1)) _ mW (by omega)
                    ⟨sW, by rw [hv1]; omega, by rw [hv1], hcoreW, hlenW, hpresW, hmW⟩)
                (fun JW hJW => by
                  c0_hsplit
                  · c0_hsteps
                    let sW : FullState := { sV with scratch := { sV.scratch with
                      phases := sV.scratch.phases.set v.toNat
                        (sV.scratch.phases_best[v.toNat]'hv_pb) } }
                    have hlenW : sW.LengthsOk c := ⟨hlenV.core_ok,
                      { hlenV.scratch_ok with
                        phases_len := by simp [sW, hlenV.scratch_ok.phases_len] }⟩
                    exact hJW () _ ⟨sW, hcoreV, hlenW, hpresV, ‹_›⟩
                  · c0_hsteps; exact hJW () mV ⟨sV, hcoreV, hlenV, hpresV, hmV⟩)
            · c0_hsteps
              let sF : FullState :=
                { sV with scratch := { sV.scratch with best_assigned := 0#64 } }
              have hinvF : FullM6HdrInv c F0 ext sF := .mk_inv hcfg hext
                (sr0_sparse_of_scratch hsp2 hcoreV ⟨hlenV.core_ok, { hlenV.scratch_ok with }⟩
                  hpresV)
              exact hJ_ph () _ ⟨ext, sF, hinvF, by rw [hcoreV]; exact hperm1, by rw [hcoreV],
                by rw [hcoreV]; exact hcl1, by rw [hcoreV, hfuel1]; exact Nat.le_refl _,
                ⟨hpresV.1.trans hpres1.1, hpresV.2.trans hpres1.2⟩, ‹_›⟩
          · intro JV hJV; c0_hsteps
            exact hJV s2.core.cur_vars (0#64, ()) mA ⟨s2, Nat.zero_le _, by simp, rfl, hlen2,
              ⟨rfl, rfl⟩, hmA⟩)
        (fun J03 hJ03 => by
          c0_hsplit; · c0_hsteps; exact hJ03 () _ ‹_›
          c0_hsplit; · c0_hsteps; exact hJ03 () _ ‹_›
          -- `else`: `if (step == 1 || step == 4)` (`full_walk`) vs `step == 2` / `else`
          let RephPost (mW : Mem 64) : Prop :=
            ∃ extW sW, FullM6HdrInv c F0 extW sW ∧ FullArenaPermEq s.core sW.core ∧
              sW.core.cur_vars = s2.core.cur_vars ∧ sW.core.cur_level = 0 ∧
              sW.core.fuel.toNat ≤ s.core.fuel.toNat ∧ FullExtScratchPres s sW ∧
              (FullMem c sW ⋆ (array64 (c.hdr - 2304) extW ⋆ R)) mW
          refine wp_join_group (ts := []) (fun _ mW => RephPost mW)
            (fun _ ⟨⟩ mW hW => by c0_hsteps; exact hJ_ph () mW hW)
            (fun J14 hJ14 => by
              refine wp_join_group (ts := [])
                (fun _ mW => (FullMem c s2 ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) mW)
                (fun _ ⟨⟩ mW hmW => by
                  c0_hsteps_nogrp; c0_call hWalk
                  refine ⟨c, F0, ext, s2, R, rfl, .mk_inv hcfg hext hsp2,
                    (fullM6HdrMem_iff ..).mpr hmW,
                    fun extW sW mW' hinvW hpermW hcvW hclW hfuelW _ hpresW hmW' => ?_⟩
                  rw [fullM6HdrMem_iff] at hmW'; c0_hsteps
                  exact hJ14 () mW' ⟨extW, sW, hinvW, sr0_arenaPermEq_trans hperm1 hpermW, hcvW,
                    by rw [hclW]; exact hcl1, by rw [← hfuel1]; exact hfuelW,
                    ⟨hpresW.1.trans hpres1.1, hpresW.2.trans hpres1.2⟩, hmW'⟩)
                (fun Jwalk hJwalk => by
                  c0_hsplit; · c0_hsteps; exact hJwalk () _ ‹_›
                  c0_hsplit; · c0_hsteps; exact hJwalk () _ ‹_›
                  refine wp_join_group (ts := []) (fun _ mW => RephPost mW)
                    (fun _ ⟨⟩ mW hW => by c0_hsteps; exact hJ14 () mW hW)
                    (fun J2e hJ2e => by
                      c0_hsplit
                      · -- `step == 2`: `ph[v] = 255`
                        refine wp_loop_group (ts := [i64])
                          (fun nv ⟨v, ⟨⟩⟩ mV => ∃ sV, v.toNat ≤ s2.core.cur_vars ∧
                            nv = s2.core.cur_vars - v.toNat ∧ sV.core = s2.core ∧ sV.LengthsOk c ∧
                            FullExtScratchPres s2 sV ∧
                            (FullMem c sV ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) mV) ?_ ?_
                        · intro JV nv ⟨v, ⟨⟩⟩ mV hJV ⟨sV, hv_le, hnv, hcoreV, hlenV, hpresV, hmV⟩
                          c0_hsplit
                          · have hv_lt : v.toNat < s2.core.cur_vars := by
                              rw [Nat.mod_eq_of_lt (by omega : s2.core.cur_vars < 2 ^ 64)] at hc
                              exact hc
                            have hv_ph : v.toNat < sV.scratch.phases.length := by
                              rw [hlenV.scratch_ok.phases_len]; omega
                            have hv1 : (v + 1).toNat = v.toNat + 1 := sr0_add1_nat (by omega)
                            c0_hsteps
                            let sW : FullState := { sV with scratch := { sV.scratch with
                              phases := sV.scratch.phases.set v.toNat 255#8 } }
                            have hlenW : sW.LengthsOk c := ⟨hlenV.core_ok,
                              { hlenV.scratch_ok with
                                phases_len := by simp [sW, hlenV.scratch_ok.phases_len] }⟩
                            exact hJV (s2.core.cur_vars - (v.toNat + 1)) _ _ (by omega)
                              ⟨sW, by rw [hv1]; omega, by rw [hv1], hcoreV, hlenW, hpresV, ‹_›⟩
                          · c0_hsteps
                            exact hJ2e () mV ⟨ext, sV, .mk_inv hcfg hext
                              (sr0_sparse_of_scratch hsp2 hcoreV hlenV hpresV),
                              by rw [hcoreV]; exact hperm1, by rw [hcoreV],
                              by rw [hcoreV]; exact hcl1,
                              by rw [hcoreV, hfuel1]; exact Nat.le_refl _,
                              ⟨hpresV.1.trans hpres1.1, hpresV.2.trans hpres1.2⟩, hmV⟩
                        · intro JV hJV; c0_hsteps
                          exact hJV s2.core.cur_vars (0#64, ()) _ ⟨s2, Nat.zero_le _, by simp, rfl,
                            hlen2, ⟨rfl, rfl⟩, ‹_›⟩
                      · -- `else`: `ph[v] = 1`
                        refine wp_loop_group (ts := [i64])
                          (fun nv ⟨v, ⟨⟩⟩ mV => ∃ sV, v.toNat ≤ s2.core.cur_vars ∧
                            nv = s2.core.cur_vars - v.toNat ∧ sV.core = s2.core ∧ sV.LengthsOk c ∧
                            FullExtScratchPres s2 sV ∧
                            (FullMem c sV ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) mV) ?_ ?_
                        · intro JV nv ⟨v, ⟨⟩⟩ mV hJV ⟨sV, hv_le, hnv, hcoreV, hlenV, hpresV, hmV⟩
                          c0_hsplit
                          · have hv_lt : v.toNat < s2.core.cur_vars := by
                              rw [Nat.mod_eq_of_lt (by omega : s2.core.cur_vars < 2 ^ 64)] at hc
                              exact hc
                            have hv_ph : v.toNat < sV.scratch.phases.length := by
                              rw [hlenV.scratch_ok.phases_len]; omega
                            have hv1 : (v + 1).toNat = v.toNat + 1 := sr0_add1_nat (by omega)
                            c0_hsteps
                            let sW : FullState := { sV with scratch := { sV.scratch with
                              phases := sV.scratch.phases.set v.toNat 1#8 } }
                            have hlenW : sW.LengthsOk c := ⟨hlenV.core_ok,
                              { hlenV.scratch_ok with
                                phases_len := by simp [sW, hlenV.scratch_ok.phases_len] }⟩
                            exact hJV (s2.core.cur_vars - (v.toNat + 1)) _ _ (by omega)
                              ⟨sW, by rw [hv1]; omega, by rw [hv1], hcoreV, hlenW, hpresV, ‹_›⟩
                          · c0_hsteps
                            exact hJ2e () mV ⟨ext, sV, .mk_inv hcfg hext
                              (sr0_sparse_of_scratch hsp2 hcoreV hlenV hpresV),
                              by rw [hcoreV]; exact hperm1, by rw [hcoreV],
                              by rw [hcoreV]; exact hcl1,
                              by rw [hcoreV, hfuel1]; exact Nat.le_refl _,
                              ⟨hpresV.1.trans hpres1.1, hpresV.2.trans hpres1.2⟩, hmV⟩
                        · intro JV hJV; c0_hsteps
                          exact hJV s2.core.cur_vars (0#64, ()) _ ⟨s2, Nat.zero_le _, by simp, rfl,
                            hlen2, ⟨rfl, rfl⟩, ‹_›⟩))))

/-! ## 7. `full_restart_due` & `full_restart` (`fullRestartDueSpec`, `fullRestartSpec`) -/

/-- Step-13 `full_restart_due` (0 integer divisions, `f64u_*`) satisfies `fullRestartDueSpec`. -/
theorem full_restart_due_step13_wp (Γ : Env)
    (hSub : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_sub" [i64, i64] [i64] a m Q X)
    (hMul : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_mul" [i64, i64] [i64] a m Q X)
    (hLog : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_log10_u64" [i64] [i64] a m Q X)
    (hTo : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_to_u64" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullRestartDueSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.full_restart_due_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  have hret0 : Q (0#64, ()) m := hQ (0#64, ()) s m rfl hlen ⟨Or.inl rfl, ⟨rfl, rfl⟩⟩ hm
  dsimp only [Func.wp, FullFidelityStep13S3.full_restart_due_body]
  c0_hsteps_nogrp
  · exact hret0
  · exact hret0
  · let s1 : FullState := { s with scratch := { s.scratch with rel_trigger := 0#64 } }
    exact hQ (1#64, ()) s1 _ rfl ⟨hlen.core_ok, { hlen.scratch_ok with }⟩
      ⟨Or.inr rfl, ⟨rfl, rfl⟩⟩ ‹_›
  · exact hret0
  · refine wp_join_group (ts := [Ty.bool]) (fun _ m1 => m = m1)
      (fun _ ⟨fire, ⟨⟩⟩ m1 hm1 => ?_)
      (fun J hJ => by
        refine wp_join_group (ts := []) (fun _ mE => m = mE)
          (fun _ ⟨⟩ mE hmE => by
            rcases hmE with rfl
            refine wp_join_group (ts := [i64]) (fun _ mB => m = mB)
              (fun _ ⟨fdiv, ⟨⟩⟩ mB hmB => by
                rcases hmB with rfl
                refine wp_join_group (ts := [i64]) (fun _ mC => m = mC)
                  (fun _ ⟨sdiv, ⟨⟩⟩ mC hmC => by
                    rcases hmC with rfl
                    c0_hsteps_nogrp
                    · exact hret0
                    · exact hret0
                    · c0_call hMul; intro _; c0_hsteps_nogrp; c0_call hMul; intro _
                      c0_hsteps_nogrp; c0_call hMul; intro _; c0_hsteps; exact hJ (_, ()) m rfl)
                  (fun J2 hJ2 => by
                    c0_hsplit; · c0_hsteps; exact hJ2 (_, ()) m rfl
                    · c0_hsteps_nogrp; c0_call hSub; intro _; c0_hsteps; exact hJ2 (_, ()) m rfl))
              (fun J1 hJ1 => by
                c0_hsplit; · c0_hsteps; exact hJ1 (_, ()) m rfl
                · c0_hsteps_nogrp; c0_call hSub; intro _; c0_hsteps; exact hJ1 (_, ()) m rfl))
          (fun JE hJE => by
            c0_hsplit
            · c0_hsplit
              · c0_hsteps_nogrp; c0_call hMul; intro _; c0_hsteps; exact hJ (_, ()) m rfl
              · c0_hsteps; exact hJE () m rfl
            · c0_hsteps; exact hJE () m rfl))
    rcases hm1 with rfl
    c0_hsplit
    · refine wp_join_group (ts := [i64]) (fun _ m2 => m = m2)
        (fun _ ⟨rst, ⟨⟩⟩ m2 hm2 => by
          rcases hm2 with rfl
          c0_hsteps_nogrp; c0_call hLog; intro _
          c0_hsteps_nogrp; c0_call hTo; intro _
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64]) (fun _ m3 => m = m3)
            (fun _ ⟨d, ⟨⟩⟩ m3 hm3 => by
              rcases hm3 with rfl; c0_hsteps
              let s1 : FullState := { s with scratch := { s.scratch with
                restart_limit := s.scratch.conflicts + d } }
              exact hQ (1#64, ()) s1 _ rfl ⟨hlen.core_ok, { hlen.scratch_ok with }⟩
                ⟨Or.inr rfl, ⟨rfl, rfl⟩⟩ ‹_›)
            (fun Jd hJd => by c0_hsteps <;> exact hJd (_, ()) m rfl))
        (fun Jr hJr => by c0_hsteps <;> exact hJr (_, ()) m rfl)
    · c0_hsteps; exact hret0

/-- Step-13 `full_restart` satisfies `Full.fullRestartSpec`: calls `full_randec_var_lvl_fid(h, 1)`,
`full_next_dec_var`, and `full_backtrack`. -/
theorem full_restart_step13_wp (Γ : Env)
    (hRandec : ∀ a m Q X, step13RandecVarLvlSpec a m Q X →
      Γ "full_randec_var_lvl_fid" [i64, i64] [i64] a m Q X)
    (hNDV : ∀ a m Q X, fullNextDecVarSpec a m Q X → Γ "full_next_dec_var" [i64] [i64] a m Q X)
    (hBT : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X) :
    ∀ a m Q X, fullRestartSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.full_restart_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hlen := hinv.lengths; have hmax := c.hmaxv; unfold dimacsBound at hmax
  obtain ⟨F_cur, hw0⟩ := hinv.witness
  have hcl_le : s.core.cur_level ≤ c.max_vars :=
    Nat.le_trans hw0.cur_level_le (Nat.le_trans hlen.core_ok.trail_end_le hlen.core_ok.cur_vars_le)
  dsimp only [Func.wp, FullFidelityStep13S3.full_restart_body]
  c0_hsteps_nogrp
  let s1 : FullState := { s with scratch := { s.scratch with
    restarts := s.scratch.restarts + 1#64 } }
  have hlen1 : s1.LengthsOk c := ⟨hlen.core_ok, { hlen.scratch_ok with }⟩
  refine wp_call_of_spec _ _ (hRandec _ _ _ _ ⟨c, s1, R, rfl, hlen1, ‹_›, ?_⟩)
  rintro ⟨nv0, ⟨⟩⟩ s2 m2 hcore2 hlen2 ⟨hpres2, _⟩ hm2
  dsimp only [PreservesCoreSlice, fullSafetySlice] at hcore2 hlen2 hm2
  refine wp_join_group (ts := [i64])
    (fun (nv, ()) m3 => ∃ s3, s3.core = s.core ∧ s3.LengthsOk c ∧ FullExtScratchPres s s3 ∧
      (FullMem c s3 ⋆ R) m3)
    (fun _ ⟨nv, ⟨⟩⟩ m3 ⟨s3, hcore3, hlen3, hpres3, hm3⟩ => ?_)
    (fun Jnv hJnv => by
      c0_hsplit
      · c0_hsteps_nogrp
        refine wp_call_of_spec _ _ (hNDV _ _ _ _ ⟨c, s2, R, rfl, hlen2, hm2, ?_⟩)
        rintro ⟨nv1, ⟨⟩⟩ s3 m3 hcore3 hlen3 ⟨hpres3, _⟩ hm3
        dsimp only [PreservesCoreSlice, fullSafetySlice] at hcore3 hlen3 hm3
        c0_hsteps; exact hJnv (nv1, ()) m3 ⟨s3, hcore3.trans hcore2, hlen3,
          ⟨hpres3.1.trans hpres2.1.1, hpres3.2.trans hpres2.1.2⟩, hm3⟩
      · c0_hsteps; exact hJnv (nv0, ()) m2 ⟨s2, hcore2, hlen2, hpres2.1, hm2⟩)
  have hcv3_le : s3.core.cur_vars ≤ c.max_vars := hlen3.core_ok.cur_vars_le
  refine wp_join_group (ts := [i64])
    (fun (reuse, ()) m4 => m3 = m4 ∧ reuse.toNat ≤ s3.core.cur_level)
    (fun _ ⟨reuse, ⟨⟩⟩ m4 ⟨hm4, hreuse⟩ => ?_)
    (fun Jre hJre => ?_)
  · rcases hm4 with rfl
    have hinv3 : FullCoreInv c F0 s3 := ⟨hlen3, F_cur, by rw [hcore3]; exact hw0⟩
    have hcl3_lt : s3.core.cur_level < 2 ^ 64 := by rw [hcore3]; omega
    have htv : reuse.toNat < s3.core.cur_level → reuse.toNat < c.max_vars := by
      intro hlt; rw [hcore3] at hlt; omega
    c0_hsteps_nogrp
    refine wp_call_of_spec _ _
      (hBT _ _ _ _ ⟨c, s3, R, rfl, hlen3, hcl3_lt, htv,
        by rw [hcore3]; exact hw0.trail_lits_lt, hm3, ?_⟩)
    intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' mB sB hsB _ _ hclB hpresB
      _ _ _ hw1 _ hmB
    have hsB_eq : sB = FullState.mk
        { s.core with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', propagated := prop', cur_level := cl', unassigned := unass' }
        sc' := by
      dsimp only [sB]; rw [hcore3]
    have hinvB : FullCoreInv c F0 sB :=
      ⟨hsB, F_cur, hw1 F0 F_cur (by rw [hcore3]; exact hw0) hreuse⟩
    c0_hsteps
    refine hQ vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' mB
      (by rwa [← hsB_eq]) (by rw [hclB, hcore3]; exact Nat.min_le_left _ _)
      ⟨hpresB.1.1.trans hpres3.1, hpresB.1.2.trans hpres3.2⟩ (by rwa [← hsB_eq])
  · c0_hsplit; rotate_left; · c0_hsteps; exact hJre (0#64, ()) m3 ⟨rfl, Nat.zero_le _⟩
    have hnv_lt : nv.toNat < s3.core.cur_vars := by
      rw [Nat.mod_eq_of_lt (by omega : s3.core.cur_vars < 2 ^ 64)] at hc; exact hc
    c0_hsplit; rotate_left; · c0_hsteps; exact hJre (0#64, ()) m3 ⟨rfl, Nat.zero_le _⟩
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64])
      (fun (r, ()) mS => m3 = mS ∧ r.toNat ≤ s3.core.cur_level)
      (fun _ ⟨r, ⟨⟩⟩ mS h => by c0_hsteps; exact hJre (r, ()) mS h)
      (fun Jst hJst => by
        c0_hsplit
        · -- Stable: score loop
          have hnv_sc : nv.toNat < s3.scratch.score.length := by
            rw [hlen3.scratch_ok.score_len]; omega
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64])
            (fun (r, ()) mB => m3 = mB ∧ r.toNat ≤ s3.core.cur_level)
            (fun _ ⟨r, ⟨⟩⟩ mB h => by c0_hsteps; exact hJst (r, ()) mB h)
            (fun Jbrk hJbrk => by
              refine wp_loop_group (ts := [i64])
                (fun fn ⟨reuse, ⟨⟩⟩ mL => m3 = mL ∧ reuse.toNat ≤ s3.core.cur_level ∧
                  fn = s3.core.cur_level - reuse.toNat) ?_ ?_
              · intro JL fn ⟨reuse, ⟨⟩⟩ mL hJL ⟨hmL, hre_le, hfn⟩
                rcases hmL with rfl
                c0_hsplit; rotate_left; · c0_hsteps; exact hJbrk (reuse, ()) m3 ⟨rfl, hre_le⟩
                have hre_lt : reuse.toNat < s3.core.cur_level := by
                  rw [Nat.mod_eq_of_lt (by rw [hcore3]; omega : s3.core.cur_level < 2 ^ 64)] at hc
                  exact hc
                have hre1 : (reuse + 1).toNat = reuse.toNat + 1 :=
                  sr0_add1_nat (by rw [hcore3] at hre_lt; omega)
                have hre1_fd : (reuse + 1).toNat < s3.core.frame_dec.length := by
                  rw [hlen3.core_ok.frame_dec_len, hre1]; rw [hcore3] at hre_lt; omega
                c0_hsteps_nogrp
                c0_hsplit; · c0_hsteps; exact hJbrk (reuse, ()) m3 ⟨rfl, hre_le⟩
                have hdv_lt :
                    ((s3.core.frame_dec[(reuse + 1).toNat]'hre1_fd >>> 1#32).setWidth 64).toNat <
                    s3.scratch.score.length := by
                  rw [hlen3.scratch_ok.score_len]
                  have h1 : ¬ s3.core.cur_vars % 2 ^ 64 ≤
                      ((s3.core.frame_dec[(reuse + 1).toNat]'hre1_fd >>> 1#32).setWidth 64).toNat :=
                    hc
                  rw [Nat.mod_eq_of_lt (by omega : s3.core.cur_vars < 2 ^ 64)] at h1; omega
                c0_hsplit; · c0_hsteps; exact hJbrk (reuse, ()) m3 ⟨rfl, hre_le⟩
                · c0_hsteps; exact hJL (s3.core.cur_level - (reuse.toNat + 1)) _ m3 (by omega)
                    ⟨rfl, by rw [hre1]; omega, by rw [hre1]⟩
              · intro JL hJL; c0_hsteps
                exact hJL s3.core.cur_level (0#64, ()) m3 ⟨rfl, Nat.zero_le _, by simp⟩)
        · -- Focused: q_stamp loop
          have hnv_qs : nv.toNat < s3.scratch.q_stamp.length := by
            rw [hlen3.scratch_ok.q_stamp_len]; omega
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64])
            (fun (r, ()) mB => m3 = mB ∧ r.toNat ≤ s3.core.cur_level)
            (fun _ ⟨r, ⟨⟩⟩ mB h => by c0_hsteps; exact hJst (r, ()) mB h)
            (fun Jbrk hJbrk => by
              refine wp_loop_group (ts := [i64])
                (fun fn ⟨reuse, ⟨⟩⟩ mL => m3 = mL ∧ reuse.toNat ≤ s3.core.cur_level ∧
                  fn = s3.core.cur_level - reuse.toNat) ?_ ?_
              · intro JL fn ⟨reuse, ⟨⟩⟩ mL hJL ⟨hmL, hre_le, hfn⟩
                rcases hmL with rfl
                c0_hsplit; rotate_left; · c0_hsteps; exact hJbrk (reuse, ()) m3 ⟨rfl, hre_le⟩
                have hre_lt : reuse.toNat < s3.core.cur_level := by
                  rw [Nat.mod_eq_of_lt (by rw [hcore3]; omega : s3.core.cur_level < 2 ^ 64)] at hc
                  exact hc
                have hre1 : (reuse + 1).toNat = reuse.toNat + 1 :=
                  sr0_add1_nat (by rw [hcore3] at hre_lt; omega)
                have hre1_fd : (reuse + 1).toNat < s3.core.frame_dec.length := by
                  rw [hlen3.core_ok.frame_dec_len, hre1]; rw [hcore3] at hre_lt; omega
                c0_hsteps_nogrp
                c0_hsplit; · c0_hsteps; exact hJbrk (reuse, ()) m3 ⟨rfl, hre_le⟩
                have hdv_lt :
                    ((s3.core.frame_dec[(reuse + 1).toNat]'hre1_fd >>> 1#32).setWidth 64).toNat <
                    s3.scratch.q_stamp.length := by
                  rw [hlen3.scratch_ok.q_stamp_len]
                  have h1 : ¬ s3.core.cur_vars % 2 ^ 64 ≤
                      ((s3.core.frame_dec[(reuse + 1).toNat]'hre1_fd >>> 1#32).setWidth 64).toNat :=
                    hc
                  rw [Nat.mod_eq_of_lt (by omega : s3.core.cur_vars < 2 ^ 64)] at h1; omega
                c0_hsplit; · c0_hsteps; exact hJbrk (reuse, ()) m3 ⟨rfl, hre_le⟩
                · c0_hsteps; exact hJL (s3.core.cur_level - (reuse.toNat + 1)) _ m3 (by omega)
                    ⟨rfl, by rw [hre1]; omega, by rw [hre1]⟩
              · intro JL hJL; c0_hsteps
                exact hJL s3.core.cur_level (0#64, ()) m3 ⟨rfl, Nat.zero_le _, by simp⟩))

/-! ## 8. `full_init_fresh_var` (`step13InitFreshVarSpec`) -/

private theorem sr0_init_fresh_post {c : FullCfg} {s : FullState} {fv : BitVec 32}
    {R : Mem 64 → Prop} {Q : Post []} {m' : Mem 64}
    (hfv_lt : fv.toNat < s.core.cur_vars) (hclen : s.core.LengthsOk c)
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (sc' : FullScratch) (hsc' : FullScratch.LengthsOk c sc')
    (hll : sc'.last_learned = s.scratch.last_learned) (hel : sc'.extend_len = s.scratch.extend_len)
    (hsb : sc'.scratch_buf = s.scratch.scratch_buf) (hws : sc'.wsort = s.scratch.wsort)
    (htm : sc'.tarjan_mark = s.scratch.tarjan_mark)
    (htr : sc'.tarjan_reach = s.scratch.tarjan_reach)
    (hsig : sc'.sim_sig = s.scratch.sim_sig) (hres : sc'.res_sz = s.scratch.res_sz)
    (hm' : (FullMem c { core := { s.core with
      unassigned := s.core.unassigned + 1#64,
      vals := (s.core.vals.set (2 * fv.toNat) 0#8).set (2 * fv.toNat + 1) 0#8,
      mrk := s.core.mrk.set fv.toNat 0#8, flags := s.core.flags.set fv.toNat 2041#32,
      lvl := s.core.lvl.set fv.toNat 0#32, rsns := s.core.rsns.set fv.toNat 0xFFFFFFFF#32,
      wvec := (((s.core.wvec.set (4 * fv.toNat) 0#32).set (4 * fv.toNat + 1) 0#32).set
        (4 * fv.toNat + 2) 0#32).set (4 * fv.toNat + 3) 0#32 }, scratch := sc' } ⋆ R) m')
    (hQ : ∀ (vals' mrk' : List (BitVec 8)) (flags' lvl' rsns' wvec' : List (BitVec 32))
      (unass' : BitVec 64) (sc' : FullScratch) (m' : Mem 64),
      have s' : FullState := { core := { s.core with
        unassigned := unass', vals := vals', mrk := mrk', flags := flags',
        lvl := lvl', rsns := rsns', wvec := wvec' }, scratch := sc' }
      s'.LengthsOk c → FullExtScratchPres s s' → sc'.scratch_buf = s.scratch.scratch_buf →
      sc'.wsort = s.scratch.wsort → sc'.tarjan_mark = s.scratch.tarjan_mark →
      sc'.tarjan_reach = s.scratch.tarjan_reach → sc'.sim_sig = s.scratch.sim_sig →
      sc'.res_sz = s.scratch.res_sz →
      vals'[2 * fv.toNat]?.getD 1#8 = 0#8 → vals'[2 * fv.toNat + 1]?.getD 1#8 = 0#8 →
      (∀ l < 2 * c.max_vars, l / 2 ≠ fv.toNat → vals'[l]? = s.core.vals[l]?) →
      mrk'[fv.toNat]?.getD 1#8 = 0#8 →
      (∀ v < c.max_vars, v ≠ fv.toNat → mrk'[v]? = s.core.mrk[v]?) →
      lvl'[fv.toNat]?.getD 1#32 = 0#32 →
      (∀ v < c.max_vars, v ≠ fv.toNat → lvl'[v]? = s.core.lvl[v]?) →
      rsns'[fv.toNat]?.getD 0#32 = 0xFFFFFFFF#32 →
      (∀ v < c.max_vars, v ≠ fv.toNat → rsns'[v]? = s.core.rsns[v]?) →
      (∀ k < 4, wvec'[4 * fv.toNat + k]?.getD 1#32 = 0#32) →
      (∀ i < 4 * c.max_vars, i / 4 ≠ fv.toNat → wvec'[i]? = s.core.wvec[i]?) →
      (FullMem c s' ⋆ R) m' → Q () m') : Q () m' := by
  have hvl := hclen.vals_len; have hml := hclen.mrk_len; have hfl := hclen.flags_len
  have hll' := hclen.lvl_len; have hrl := hclen.rsns_len; have hwl := hclen.wvec_len
  have hlen' : ({ core := { s.core with
      unassigned := s.core.unassigned + 1#64,
      vals := (s.core.vals.set (2 * fv.toNat) 0#8).set (2 * fv.toNat + 1) 0#8,
      mrk := s.core.mrk.set fv.toNat 0#8, flags := s.core.flags.set fv.toNat 2041#32,
      lvl := s.core.lvl.set fv.toNat 0#32, rsns := s.core.rsns.set fv.toNat 0xFFFFFFFF#32,
      wvec := (((s.core.wvec.set (4 * fv.toNat) 0#32).set (4 * fv.toNat + 1) 0#32).set
        (4 * fv.toNat + 2) 0#32).set (4 * fv.toNat + 3) 0#32 }, scratch := sc' } :
      FullState).LengthsOk c :=
    ⟨{ hclen with
      vals_len := by simp [hvl]
      mrk_len := by simp [hml]
      flags_len := by simp [hfl]
      lvl_len := by simp [hll']
      rsns_len := by simp [hrl]
      wvec_len := by simp [hwl] }, hsc'⟩
  refine hQ _ _ _ _ _ _ _ sc' m' hlen' ⟨hll, hel⟩ hsb hws htm htr hsig hres
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hm'
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
  · rw [List.getElem?_set_self (by rw [List.length_set]; omega), Option.getD_some]
  · intro l hl hne; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  · rw [List.getElem?_set_self (by omega), Option.getD_some]
  · intro v hv hne; rw [List.getElem?_set_ne (Ne.symm hne)]
  · rw [List.getElem?_set_self (by omega), Option.getD_some]
  · intro v hv hne; rw [List.getElem?_set_ne (Ne.symm hne)]
  · rw [List.getElem?_set_self (by omega), Option.getD_some]
  · intro v hv hne; rw [List.getElem?_set_ne (Ne.symm hne)]
  · intro k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · simp only [Nat.add_zero]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by rw [List.length_set]; omega), Option.getD_some]
    · rw [List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by rw [List.length_set, List.length_set]; omega), Option.getD_some]
    · rw [List.getElem?_set_self
        (by rw [List.length_set, List.length_set, List.length_set]; omega), Option.getD_some]
  · intro i hi hne
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]

/-- Step-13 `full_init_fresh_var` (`ph[fv] = 0`, `ptgt/pbst/wbst`, + stable `full_heap_push`)
satisfies `step13InitFreshVarSpec`. -/
theorem full_init_fresh_var_step13_wp (Γ : Env)
    (hHeapPush : ∀ a m Q X, fullHeapPushSpec a m Q X →
      Γ "full_heap_push" [i64, i32] [] a m Q X) :
    ∀ a m Q X, step13InitFreshVarSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.full_init_fresh_var_body a m Q X := by
  rintro ⟨h, fv, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hfv_lt, hm, hQ⟩
  have hcl := hlen.core_ok; have hsc := hlen.scratch_ok; have hcv_le := hcl.cur_vars_le
  have hmax := c.hmaxv; unfold dimacsBound at hmax
  have hw0 := sr0_shl2_fv fv
  have hw1 : ((BitVec.setWidth 64 fv <<< (2 : Nat)) + (1 : BitVec 64)).toNat = 4 * fv.toNat + 1 :=
    sr0_shl2_add_fv fv 1 (by decide)
  have hw2 : ((BitVec.setWidth 64 fv <<< (2 : Nat)) + (2 : BitVec 64)).toNat = 4 * fv.toNat + 2 :=
    sr0_shl2_add_fv fv 2 (by decide)
  have hw3 : ((BitVec.setWidth 64 fv <<< (2 : Nat)) + (3 : BitVec 64)).toNat = 4 * fv.toNat + 3 :=
    sr0_shl2_add_fv fv 3 (by decide)
  have hv0 := sr0_shl1_fv fv
  have hv1 : ((BitVec.setWidth 64 fv <<< (1 : Nat)) ||| (1 : BitVec 64)).toNat = 2 * fv.toNat + 1 :=
    sr0_shl1_or1_fv fv
  have hfv64 : (fv.setWidth 64).toNat = fv.toNat := zext_toNat fv (by decide)
  have hwv0 : (fv.setWidth 64 <<< (2 : Nat)).toNat < s.core.wvec.length := by
    rw [hw0, hcl.wvec_len]; omega
  have hwv1 : ((fv.setWidth 64 <<< (2 : Nat)) + (1 : BitVec 64)).toNat < s.core.wvec.length := by
    rw [hw1, hcl.wvec_len]; omega
  have hwv2 : ((fv.setWidth 64 <<< (2 : Nat)) + (2 : BitVec 64)).toNat < s.core.wvec.length := by
    rw [hw2, hcl.wvec_len]; omega
  have hwv3 : ((fv.setWidth 64 <<< (2 : Nat)) + (3 : BitVec 64)).toNat < s.core.wvec.length := by
    rw [hw3, hcl.wvec_len]; omega
  have hvl0 : (fv.setWidth 64 <<< (1 : Nat)).toNat < s.core.vals.length := by
    rw [hv0, hcl.vals_len]; omega
  have hvl1 : ((fv.setWidth 64 <<< (1 : Nat)) ||| (1 : BitVec 64)).toNat < s.core.vals.length := by
    rw [hv1, hcl.vals_len]; omega
  have hmrk : (fv.setWidth 64).toNat < s.core.mrk.length := by rw [hfv64, hcl.mrk_len]; omega
  have hph : (fv.setWidth 64).toNat < s.scratch.phases.length := by
    rw [hfv64, hsc.phases_len]; omega
  have hpt : (fv.setWidth 64).toNat < s.scratch.phases_target.length := by
    rw [hfv64, hsc.phases_target_len]; omega
  have hpb : (fv.setWidth 64).toNat < s.scratch.phases_best.length := by
    rw [hfv64, hsc.phases_best_len]; omega
  have hwb : (fv.setWidth 64).toNat < s.scratch.walk_best.length := by
    rw [hfv64, hsc.walk_best_len]; omega
  have hlvl : (fv.setWidth 64).toNat < s.core.lvl.length := by rw [hfv64, hcl.lvl_len]; omega
  have hrsn : (fv.setWidth 64).toNat < s.core.rsns.length := by rw [hfv64, hcl.rsns_len]; omega
  have hps : (fv.setWidth 64).toNat < s.scratch.pos.length := by rw [hfv64, hsc.pos_len]; omega
  have hsco : (fv.setWidth 64).toNat < s.scratch.score.length := by rw [hfv64, hsc.score_len]; omega
  have hfl : (fv.setWidth 64).toNat < s.core.flags.length := by rw [hfv64, hcl.flags_len]; omega
  have hqp : (fv.setWidth 64).toNat < s.scratch.q_prev.length := by
    rw [hfv64, hsc.q_prev_len]; omega
  have hqn : (fv.setWidth 64).toNat < s.scratch.q_next.length := by
    rw [hfv64, hsc.q_next_len]; omega
  have hqs : (fv.setWidth 64).toNat < s.scratch.q_stamp.length := by
    rw [hfv64, hsc.q_stamp_len]; omega
  have hfl_val : ((1 : BitVec 32) ||| 8 ||| 16 ||| 1024 ||| 32 ||| 64 |||
      128 ||| 256 ||| 512) = 2041#32 := by decide
  dsimp only [Func.wp, FullFidelityStep13S3.full_init_fresh_var_body]
  c0_hsteps_nogrp
  let core1 : FullCoreState := { s.core with
    vals := (s.core.vals.set (2 * fv.toNat) 0#8).set (2 * fv.toNat + 1) 0#8,
    mrk := s.core.mrk.set fv.toNat 0#8, flags := s.core.flags.set fv.toNat 2041#32,
    lvl := s.core.lvl.set fv.toNat 0#32, rsns := s.core.rsns.set fv.toNat 0xFFFFFFFF#32,
    wvec := (((s.core.wvec.set (4 * fv.toNat) 0#32).set (4 * fv.toNat + 1) 0#32).set
      (4 * fv.toNat + 2) 0#32).set (4 * fv.toNat + 3) 0#32 }
  have hcore1_len : core1.LengthsOk c :=
    { hcl with
      vals_len := by simp [core1, hcl.vals_len]
      mrk_len := by simp [core1, hcl.mrk_len]
      flags_len := by simp [core1, hcl.flags_len]
      lvl_len := by simp [core1, hcl.lvl_len]
      rsns_len := by simp [core1, hcl.rsns_len]
      wvec_len := by simp [core1, hcl.wvec_len] }
  refine wp_join_group (ts := [])
    (fun _ m1 => ∃ sc1 : FullScratch, sc1.LengthsOk c ∧
      sc1.last_learned = s.scratch.last_learned ∧ sc1.extend_len = s.scratch.extend_len ∧
      sc1.scratch_buf = s.scratch.scratch_buf ∧ sc1.wsort = s.scratch.wsort ∧
      sc1.tarjan_mark = s.scratch.tarjan_mark ∧ sc1.tarjan_reach = s.scratch.tarjan_reach ∧
      sc1.sim_sig = s.scratch.sim_sig ∧ sc1.res_sz = s.scratch.res_sz ∧
      (FullMem c { core := core1, scratch := sc1 } ⋆ R) m1)
    (fun _ ⟨⟩ m1 ⟨sc1, hsc1, hll1, hel1, hsb1, hws1, htm1, htr1, hsig1, hres1, hm1⟩ => ?_)
    (fun Jq hJq => by
      c0_hsplit
      · have hold_lt : (BitVec.setWidth 32 s.scratch.q_first).toNat < s.core.cur_vars := by
          have h1 : (BitVec.setWidth 64 (BitVec.setWidth 32 s.scratch.q_first)).toNat <
              s.core.cur_vars % 2 ^ 64 := hc
          rw [zext_toNat _ (by decide)] at h1; omega
        have hold_qp : (BitVec.setWidth 64 (BitVec.setWidth 32 s.scratch.q_first)).toNat <
            (s.scratch.q_prev.set (fv.setWidth 64).toNat 0xFFFFFFFF#32).length := by
          rw [List.length_set, zext_toNat _ (by decide), hsc.q_prev_len]; omega
        c0_hsteps
        simp only [hw0, hw1, hw2, hw3, hv0, hv1, hfv64, hfl_val] at hm
        let sc1 : FullScratch := { s.scratch with
          phases := s.scratch.phases.set fv.toNat 0#8,
          phases_target := s.scratch.phases_target.set fv.toNat 0#8,
          phases_best := s.scratch.phases_best.set fv.toNat 0#8,
          walk_best := s.scratch.walk_best.set fv.toNat 1#8,
          pos := s.scratch.pos.set fv.toNat 0xFFFFFFFF#32,
          score := s.scratch.score.set fv.toNat 0#64,
          q_prev := (s.scratch.q_prev.set fv.toNat 0xFFFFFFFF#32).set
            (BitVec.setWidth 64 (BitVec.setWidth 32 s.scratch.q_first)).toNat fv,
          q_next := s.scratch.q_next.set fv.toNat (BitVec.setWidth 32 s.scratch.q_first) }
        exact hJq () _ ⟨sc1, { hsc with
          phases_len := by simp [sc1, hsc.phases_len]
          phases_target_len := by simp [sc1, hsc.phases_target_len]
          phases_best_len := by simp [sc1, hsc.phases_best_len]
          walk_best_len := by simp [sc1, hsc.walk_best_len]
          pos_len := by simp [sc1, hsc.pos_len]
          score_len := by simp [sc1, hsc.score_len]
          q_prev_len := by simp [sc1, hsc.q_prev_len]
          q_next_len := by simp [sc1, hsc.q_next_len] },
          rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm⟩
      · c0_hsteps
        simp only [hw0, hw1, hw2, hw3, hv0, hv1, hfv64, hfl_val] at hm
        let sc1 : FullScratch := { s.scratch with
          q_last := fv.setWidth 64,
          phases := s.scratch.phases.set fv.toNat 0#8,
          phases_target := s.scratch.phases_target.set fv.toNat 0#8,
          phases_best := s.scratch.phases_best.set fv.toNat 0#8,
          walk_best := s.scratch.walk_best.set fv.toNat 1#8,
          pos := s.scratch.pos.set fv.toNat 0xFFFFFFFF#32,
          score := s.scratch.score.set fv.toNat 0#64,
          q_prev := s.scratch.q_prev.set fv.toNat 0xFFFFFFFF#32,
          q_next := s.scratch.q_next.set fv.toNat 0xFFFFFFFF#32 }
        exact hJq () _ ⟨sc1, { hsc with
          phases_len := by simp [sc1, hsc.phases_len]
          phases_target_len := by simp [sc1, hsc.phases_target_len]
          phases_best_len := by simp [sc1, hsc.phases_best_len]
          walk_best_len := by simp [sc1, hsc.walk_best_len]
          pos_len := by simp [sc1, hsc.pos_len]
          score_len := by simp [sc1, hsc.score_len]
          q_prev_len := by simp [sc1, hsc.q_prev_len]
          q_next_len := by simp [sc1, hsc.q_next_len] },
          rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm⟩)
  have hfv_qs1 : (fv.setWidth 64).toNat < sc1.q_stamp.length := by
    rw [hfv64, hsc1.q_stamp_len]; omega
  c0_hsteps_nogrp
  let sc2 : FullScratch := { sc1 with
    q_first := fv.setWidth 64, q_stamp := sc1.q_stamp.set (fv.setWidth 64).toNat 0#32 }
  have hsc2 : sc2.LengthsOk c := { hsc1 with q_stamp_len := by simp [sc2, hsc1.q_stamp_len] }
  let s2 : FullState := { core := core1, scratch := sc2 }
  refine wp_join_group (ts := [])
    (fun _ m2 => ∃ sc3 : FullScratch, sc3.LengthsOk c ∧
      sc3.last_learned = s.scratch.last_learned ∧ sc3.extend_len = s.scratch.extend_len ∧
      sc3.scratch_buf = s.scratch.scratch_buf ∧ sc3.wsort = s.scratch.wsort ∧
      sc3.tarjan_mark = s.scratch.tarjan_mark ∧ sc3.tarjan_reach = s.scratch.tarjan_reach ∧
      sc3.sim_sig = s.scratch.sim_sig ∧ sc3.res_sz = s.scratch.res_sz ∧
      (FullMem c { core := core1, scratch := sc3 } ⋆ R) m2)
    (fun _ ⟨⟩ m2 ⟨sc3, hsc3, hll3, hel3, hsb3, hws3, htm3, htr3, hsig3, hres3, hm2⟩ => by
      c0_hsteps
      exact sr0_init_fresh_post hfv_lt hcl hcv_le sc3 hsc3 hll3 hel3 hsb3 hws3 htm3 htr3 hsig3
        hres3 ‹_› hQ)
    (fun Jh hJh => by
      c0_hsplit
      · c0_hsteps_nogrp
        refine wp_call_of_spec _ _ (hHeapPush _ _ _ _ ⟨c, s2, R, rfl, ⟨hcore1_len, hsc2⟩, ‹_›, ?_⟩)
        rintro ⟨⟩ s3 m3 hcore3 hlen3
          ⟨⟨hll3, hel3⟩, _, _, htm3, hsb3, _, hres3, hsig3, hp', ps', hl', hsc3_eq⟩ hm3
        dsimp only [PreservesCoreSlice, fullSafetySlice] at hcore3 hlen3 hm3
        have hws3 : s3.scratch.wsort = s.scratch.wsort := by rw [hsc3_eq]; exact hws1
        have htr3 : s3.scratch.tarjan_reach = s.scratch.tarjan_reach := by rw [hsc3_eq]; exact htr1
        have hcore3' : s3 = { core := core1, scratch := s3.scratch } := by
          cases s3; dsimp only at hcore3 ⊢; rw [hcore3]
        c0_hsteps
        exact hJh () m3 ⟨s3.scratch, hlen3.scratch_ok,
          hll3.trans hll1, hel3.trans hel1, hsb3.trans hsb1, hws3,
          htm3.trans htm1, htr3, hsig3.trans hsig1, hres3.trans hres1,
          by rwa [← hcore3']⟩
      · c0_hsteps
        exact hJh () _ ⟨sc2, hsc2, hll1, hel1, hsb1, hws1, htm1, htr1, hsig1, hres1, ‹_›⟩)

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S3
