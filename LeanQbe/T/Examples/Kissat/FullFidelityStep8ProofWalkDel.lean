/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep8
public import LeanQbe.T.Examples.Kissat.FullM7WalkProof0
public import LeanQbe.T.Examples.Kissat.FullBinLuckyLemmas1
public import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Agrees

/-!
# Kissat Fidelity Step 8 Walk-Effort & Binary-Watch Deletion Proofs

Parametric `(Γ : Env)` WP proofs (`0` `import all`, `public section`) for:
1. `full_walk_effort_m7_step8_wp`: `fidStep8WalkEffortM7Fn` against `FullM7Walk.m7EffortSpec`.
2. `full_delete_bin_side_step8_wp`: `fidStep8DeleteBinSideFn` against
   `Full.fullDeleteBinSideSpec` (read-only scan then tight left-shift).
-/

set_option autoImplicit false

local elab "s8_hsteps_nj" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep8

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM7Walk
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullBinLuckyTactics

/-! ## 1. `full_walk_effort_m7` Step-8 WP Proof -/

abbrev step8WalkEffortSpec : Spec [i64, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _mf, ()) _ => h = c.hdr)
    (fun _ _ (r, ()) s s' => s' = s ∧ 500000 ≤ r.toNat ∧ r.toNat ≤ 40000000)

theorem full_walk_effort_m7_step8_wp (Γ : Env) :
    ∀ a m Q X, step8WalkEffortSpec a m Q X →
      Func.wp Γ full_walk_effort_m7_body a m Q X := by
  rintro ⟨h, max_flips, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  s8_hsteps_nj
  refine wp_join_group (ts := [i64]) (fun (dt, ()) m1 => (FullMem c s ⋆ R) m1) ?_ ?_
  · rintro _ ⟨dt, ⟨⟩⟩ m1 hm1
    s8_hsteps_nj
    refine wp_join_group (ts := [i64]) (fun (eff, ()) m2 =>
        (FullMem c s ⋆ R) m2 ∧ eff.toNat ≤ 40000000) ?_ ?_
    · rintro _ ⟨eff, ⟨⟩⟩ m2 ⟨hm2, heff⟩
      s8_hsteps_nj
      refine wp_join_group (ts := [i64]) (fun (eff2, ()) m3 =>
          (FullMem c s ⋆ R) m3 ∧ 500000 ≤ eff2.toNat ∧ eff2.toNat ≤ 40000000) ?_ ?_
      · rintro _ ⟨eff2, ⟨⟩⟩ m3 ⟨hm3, he1, he2⟩
        s8_hsteps_nj
        refine wp_join_group (ts := [i64]) (fun (eff3, ()) m4 =>
            (FullMem c s ⋆ R) m4 ∧ 500000 ≤ eff3.toNat ∧ eff3.toNat ≤ 40000000) ?_ ?_
        · rintro _ ⟨eff3, ⟨⟩⟩ m4 ⟨hm4, hf1, hf2⟩
          s8_hsteps_nj
          exact hQ (eff3, ()) s m4 rfl hlen ⟨rfl, hf1, hf2⟩ hm4
        · intro J3 hJ3; s8_hsteps_nj
          · exact hJ3 (40000000#64, ()) m3 ⟨hm3, by decide, by decide⟩
          · exact hJ3 (eff2, ()) m3 ⟨hm3, he1, he2⟩
      · intro J2 hJ2; s8_hsteps_nj
        · exact hJ2 (500000#64, ()) m2 ⟨hm2, by decide, by decide⟩
        · exact hJ2 (eff, ()) m2 ⟨hm2, by c0_bound, heff⟩
    · intro Je hJe; s8_hsteps_nj
      · have hdt : dt.toNat ≤ 800000000 := by c0_bound
        have hdiv : (dt / 20#64).toNat ≤ 40000000 := by
          rw [BitVec.toNat_udiv, show (20#64 : BitVec 64).toNat = 20 from rfl]; omega
        exact hJe (_, ()) m1 ⟨hm1, hdiv⟩
      · exact hJe (40000000#64, ()) m1 ⟨hm1, by decide⟩
  · intro Jdt hJdt; s8_hsteps_nj <;> exact hJdt (_, ()) m hm

/-! ## 2. `BoolSlice` Helpers & `full_delete_bin_side` Step-8 WP Proof -/

private abbrev BoolSlice (sp : Bool) (F_cur : List (List Nat)) (k : FullCoreState)
    (lit p rem : Nat) : Prop :=
  if sp then WatchSliceOk F_cur k lit p rem else DenseWatchSliceOk F_cur k lit p rem

private theorem boolSlice_relocate {sp : Bool} {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : BoolSlice sp F_cur k lit p rem) : BoolSlice sp F_cur k' lit p' rem := by
  have hent : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ x => x
  cases sp <;> simp only [BoolSlice, ↓reduceIte, Bool.false_eq_true] at h ⊢
  · exact h.fbl_relocate hent hvars hsub hwstk
  · exact h.fbl_relocate hent hvars hsub hwstk

private theorem boolSlice_append_slice {sp : Bool} {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p l1 l2 : Nat}
    (h1 : BoolSlice sp F_cur k lit p l1) (h2 : BoolSlice sp F_cur k lit (p + l1) l2) :
    BoolSlice sp F_cur k lit p (l1 + l2) := by
  cases sp <;> simp only [BoolSlice, ↓reduceIte, Bool.false_eq_true] at h1 h2 ⊢
  · exact h1.fbl_append_slice h2
  · exact h1.fbl_append_slice h2

private theorem boolSlice_bin_tail {sp : Bool} {F_cur : List (List Nat)} {k : FullCoreState}
    {src p rem : Nat} {w0 : BitVec 32} (hsl : BoolSlice sp F_cur k src p rem)
    (hpos : 0 < rem) (hp : k.wstk[p]? = some w0) (hbin : (w0 &&& 0x80000000#32) ≠ 0#32) :
    BoolSlice sp F_cur k src p 1 ∧ BoolSlice sp F_cur k src (p + 1) (rem - 1) := by
  cases sp <;> simp only [BoolSlice, ↓reduceIte, Bool.false_eq_true] at hsl ⊢
  · cases hsl with
    | empty => omega
    | bin hp0 hfl hne hlt hent hrest =>
      exact ⟨.bin hp0 hfl hne hlt hent .empty, hrest⟩
    | occ hp0 _ hfl _ _ _ _ => rw [hp] at hp0; cases hp0; exact absurd hfl hbin
  · cases hsl with
    | empty => omega
    | bin hp0 hfl hne hlt hent hrest =>
      exact ⟨.bin hp0 hfl hne hlt hent .empty, hrest⟩
    | large hp0 _ hfl _ _ _ => rw [hp] at hp0; cases hp0; exact absurd hfl hbin

private theorem boolSlice_large_tail {sp : Bool} {F_cur : List (List Nat)} {k : FullCoreState}
    {src p rem : Nat} {w0 : BitVec 32} (hsl : BoolSlice sp F_cur k src p rem)
    (hpos : 0 < rem) (hp : k.wstk[p]? = some w0) (hlg : (w0 &&& 0x80000000#32) = 0#32) :
    2 ≤ rem ∧ BoolSlice sp F_cur k src p 2 ∧ BoolSlice sp F_cur k src (p + 2) (rem - 2) := by
  cases sp <;> simp only [BoolSlice, ↓reduceIte, Bool.false_eq_true] at hsl ⊢
  · cases hsl with
    | empty => omega
    | bin hp0 hfl _ _ _ _ => rw [hp] at hp0; cases hp0; exact absurd hlg hfl
    | occ hp0 hp1 hfl hsz hlt href hrest =>
      exact ⟨by omega, .occ hp0 hp1 hfl hsz hlt href .empty, by simpa using hrest⟩
  · cases hsl with
    | empty => omega
    | bin hp0 hfl _ _ _ _ => rw [hp] at hp0; cases hp0; exact absurd hlg hfl
    | large hp0 hp1 hfl hlt href hrest =>
      exact ⟨by omega, .large hp0 hp1 hfl hlt href .empty, by simpa using hrest⟩

private theorem boolSlice_extend1 {sp : Bool} {F_cur : List (List Nat)} {k : FullCoreState}
    {lit off p end_ : Nat} {w0 : BitVec 32}
    (hoff : off ≤ p) (hp_lt : p < end_)
    (hp : k.wstk[p]? = some w0) (hbin : (w0 &&& 0x80000000#32) ≠ 0#32)
    (hpre : BoolSlice sp F_cur k lit off (p - off))
    (hsuf : BoolSlice sp F_cur k lit p (end_ - p)) :
    BoolSlice sp F_cur k lit off (p + 1 - off) ∧
    BoolSlice sp F_cur k lit (p + 1) (end_ - (p + 1)) := by
  obtain ⟨h1, hrest⟩ := boolSlice_bin_tail hsuf (by omega) hp hbin
  have hjoin := boolSlice_append_slice hpre (by simpa [show off + (p - off) = p by omega] using h1)
  refine ⟨?_, ?_⟩
  · simpa [show p + 1 - off = (p - off) + 1 by omega] using hjoin
  · simpa [show end_ - (p + 1) = (end_ - p) - 1 by omega] using hrest

private theorem boolSlice_extend2 {sp : Bool} {F_cur : List (List Nat)} {k : FullCoreState}
    {lit off p end_ : Nat} {w0 : BitVec 32}
    (hoff : off ≤ p) (hp_lt : p < end_)
    (hp : k.wstk[p]? = some w0) (hlg : (w0 &&& 0x80000000#32) = 0#32)
    (hpre : BoolSlice sp F_cur k lit off (p - off))
    (hsuf : BoolSlice sp F_cur k lit p (end_ - p)) :
    2 ≤ end_ - p ∧ BoolSlice sp F_cur k lit off (p + 2 - off) ∧
    BoolSlice sp F_cur k lit (p + 2) (end_ - (p + 2)) := by
  obtain ⟨h2, h2s, hrest⟩ := boolSlice_large_tail hsuf (by omega) hp hlg
  have hjoin := boolSlice_append_slice hpre (by simpa [show off + (p - off) = p by omega] using h2s)
  refine ⟨h2, ?_, ?_⟩
  · simpa [show p + 2 - off = (p - off) + 2 by omega] using hjoin
  · simpa [show end_ - (p + 2) = (end_ - p) - 2 by omega] using hrest

theorem full_delete_bin_side_step8_wp (Γ : Env) :
    ∀ args m Q X, fullDeleteBinSideSpec args m Q X →
      Func.wp Γ full_delete_bin_side_body args m Q X := by
  rintro ⟨h, lit, other, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hbd_arg, hm, hQ⟩
  have hcl := hlen.core_ok
  have hmx := c.hmaxv; have hwc := c.hwcap; unfold dimacsBound at hmx hwc
  have hcv_le := hcl.cur_vars_le; have hwvl := hcl.wvec_len; have hwl := hcl.wstk_len_arr
  have hwle := hcl.wlen_le
  have hret_same : Q () m := by
    have hlen_id : ({ s with core :=
        { s.core with wvec := s.core.wvec, wstk := s.core.wstk, wusable := s.core.wusable } } :
        FullState).LengthsOk c := ⟨{ hcl with }, hlen.scratch_ok⟩
    exact hQ s.core.wvec s.core.wstk s.core.wusable m hlen_id
      (fun _ => ⟨rfl, Nat.le_refl _⟩) (fun _ _ _ => ⟨rfl, rfl⟩) (fun _ _ _ => rfl)
      (fun _ hw => hw) (fun _ hw => hw) (fun hl => hl) (fun _ hmw => hmw) hm
  fbl_group
  · exact hret_same
  · exact hret_same
  · have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by c0_bound
    have hidx0 : (lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * lit.toNat := by
      have : lit.toNat < 2 ^ 30 := by omega
      bv_omega
    have hidx1 : ((lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * lit.toNat + 1 := by
      have : lit.toNat < 2 ^ 30 := by omega
      bv_omega
    have hoff_eq : (s.core.wvec[2 * lit.toNat]'(by omega)).toNat =
        fullWatchOffCore s.core lit.toNat := by
      unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hsz_eq : (s.core.wvec[2 * lit.toNat + 1]'(by omega)).toNat =
        fullWatchSizeCore s.core lit.toNat := by
      unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hbd_slice : fullWatchOffCore s.core lit.toNat + fullWatchSizeCore s.core lit.toNat ≤
        s.core.wlen := hbd_arg hlit_lt
    have hs0 : 2 * lit.toNat % 2 ^ 64 = 2 * lit.toNat := by omega
    have h1_64 : BitVec.toNat (1 : BitVec 64) = 1 := rfl
    have hs1 : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * lit.toNat + 1 := by
      rw [h1_64]; omega
    have h_off : (BitVec.setWidth 64
        (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'(by rw [hidx0]; omega))).toNat =
        fullWatchOffCore s.core lit.toNat := by
      simp only [hidx0, BitVec.toNat_setWidth, hoff_eq]; omega
    have h_sz : (BitVec.setWidth 64
        (s.core.wvec[2 * lit.toNat + 1]'(by omega))).toNat =
        fullWatchSizeCore s.core lit.toNat := by
      simp only [BitVec.toNat_setWidth, hsz_eq]; omega
    have hsz_pos : 0 < fullWatchSizeCore s.core lit.toNat := by
      refine Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq ?_)
      simp only [h1_64, Nat.mod_eq_of_lt (by omega : 2 * lit.toNat + 1 < 2 ^ 64),
        BitVec.toNat_setWidth, hsz_eq, h0]
      rfl
    let off := fullWatchOffCore s.core lit.toNat
    let sz := fullWatchSizeCore s.core lit.toNat
    let end_ := off + sz
    have h_cond_lt : (s.core.wvec[2 * lit.toNat % 2 ^ 64].toNat +
        s.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat) % 2 ^ 64 =
        end_ := by
      simp only [hs0, hs1, hoff_eq, hsz_eq]; omega
    refine wp_while_break_state
      (β := Val i64 × Bool)
      (projBrk := fun (p, rem) => (p, rem, ()))
      (BrkPost := fun (p, rem) mB => mB = m ∧
        ((rem = false) ∨
         (rem = true ∧ off < p.toNat ∧ p.toNat ≤ end_ ∧
          ∀ sp F_cur, BoolSlice sp F_cur s.core lit.toNat off (end_ - off) →
            BoolSlice sp F_cur s.core lit.toNat off (p.toNat - 1 - off) ∧
            BoolSlice sp F_cur s.core lit.toNat p.toNat (end_ - p.toNat))))
      (α := Val i64)
      (projLp := fun p => (p, ()))
      (μ := fun p => end_ - p.toNat)
      (Inv := fun p mL => mL = m ∧ off ≤ p.toNat ∧ p.toNat ≤ end_ ∧
        ∀ sp F_cur, BoolSlice sp F_cur s.core lit.toNat off (end_ - off) →
          BoolSlice sp F_cur s.core lit.toNat off (p.toNat - off) ∧
          BoolSlice sp F_cur s.core lit.toNat p.toNat (end_ - p.toNat))
      ?_ ?_ ?_
    · -- Post-loop `hafter`: `if (!removed) return;` then Loop 2
      rintro B ⟨pB, remB⟩ mB ⟨hmB, hB⟩
      subst mB
      fbl_group
      · rcases hB with hfalse | ⟨_, hq_lo_strict, hpB_hi, hBslice⟩
        · cases hc.symm.trans hfalse
        · let q0 := pB.toNat - 1
          have hq0_ge : off ≤ q0 := by omega
          have hq0_lt : q0 < end_ := by omega
          refine wp_loop_inv
            (fun (p2, ()) ml2 => ∃ wstk2 : List (BitVec 32),
              pB.toNat ≤ p2.toNat ∧ p2.toNat ≤ end_ ∧ wstk2.length = c.wcap ∧
              (∀ idx, idx < q0 ∨ p2.toNat - 1 ≤ idx → wstk2[idx]? = s.core.wstk[idx]?) ∧
              (∀ j, q0 ≤ j → j < p2.toNat - 1 → wstk2[j]? = s.core.wstk[j + 1]?) ∧
              (FullMem c { s with core := { s.core with wstk := wstk2 } } ⋆ R) ml2)
            (fun (p2, ()) _ => end_ - p2.toNat)
            (fun J2 hJ2 => hJ2 (pB, ()) m ⟨s.core.wstk, le_refl _, hpB_hi, hwl,
              fun _ _ => rfl, fun _ h1 h2 => by omega, hm⟩)
            (fun J2 (p2, ()) ml2 ⟨wstk2, hp2_lo, hp2_hi, hwl2, hout2, hsh2, hm2⟩ ih2 => ?_)
          fbl_group
          · have hp2_lt : p2.toNat < end_ := by rw [← h_cond_lt]; assumption
            have hp2_m1 : (p2 - 1#64).toNat = p2.toNat - 1 := by
              rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
                rw [show (1#64 : BitVec 64).toNat = 1 from rfl]; omega))]
              rfl
            have hp2_p1 : (p2 + 1#64).toNat = p2.toNat + 1 := by
              simp [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega : p2.toNat + 1 < 2 ^ 64)]
            let wstk3 := wstk2.set (p2.toNat - 1) (wstk2[p2.toNat]'(by omega))
            have hsrc_at : wstk2[p2.toNat]'(by omega) = s.core.wstk[p2.toNat]'(by omega) := by
              have := hout2 p2.toNat (Or.inr (by omega))
              rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at this
              exact Option.some.inj this
            fbl_group
            refine ih2 (p2 + 1#64, ()) _ (by dsimp only; omega)
              ⟨wstk3, by rw [hp2_p1]; omega, by rw [hp2_p1]; omega,
              by rw [List.length_set, hwl2], fun idx hidx => ?_, fun j hj1 hj2 => ?_, ?_⟩
            · rw [hp2_p1] at hidx
              dsimp only [wstk3]
              rw [List.getElem?_set_ne (by rcases hidx with h | h <;> omega)]
              exact hout2 idx (hidx.imp (fun h => h) (fun h => by omega))
            · rw [hp2_p1] at hj2
              dsimp only [wstk3]
              by_cases hjeq : j = p2.toNat - 1
              · subst hjeq
                rw [List.getElem?_eq_getElem (by rw [List.length_set]; omega),
                  List.getElem_set_self, hsrc_at,
                  show p2.toNat - 1 + 1 = p2.toNat by omega,
                  List.getElem?_eq_getElem (by omega)]
              · rw [List.getElem?_set_ne (Ne.symm hjeq)]
                exact hsh2 j hj1 (by omega)
            · dsimp only [wstk3]
              change (FullMem c { s with core := { s.core with
                wstk := wstk2.set (p2.toNat - 1) wstk2[p2.toNat] } } ⋆ R) m
              rw [← show (p2 - (1 : BitVec 64)).toNat = p2.toNat - 1 from hp2_m1]
              exact hm
          · have hp2_end : p2.toNat = end_ := by
              have hnot : ¬ p2.toNat < end_ := by rw [← h_cond_lt]; assumption
              omega
            have h1_m1 : (BitVec.setWidth 64 (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'
                (by rw [hidx0]; omega)) +
                BitVec.setWidth 64 (s.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) %
                  2 ^ 64]'(by rw [hs1]; omega)) - 1#64).toNat = end_ - 1 := by
              have hsum : (BitVec.setWidth 64 (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'
                  (by rw [hidx0]; omega)) +
                  BitVec.setWidth 64 (s.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) %
                    2 ^ 64]'(by rw [hs1]; omega))).toNat = end_ := by
                simp only [hidx0, hs1, BitVec.toNat_add, BitVec.toNat_setWidth, hoff_eq, hsz_eq]
                omega
              rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
                rw [hsum, show (1#64 : BitVec 64).toNat = 1 from rfl]; omega)), hsum]
              rfl
            let wstkF := wstk2.set (end_ - 1) 0xFFFFFFFF#32
            have hsz_m1_trunc :
                (BitVec.setWidth 32 (BitVec.setWidth 64 (s.core.wvec[(2 * lit.toNat +
                  BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by rw [hs1]; omega)) - 1#64)).toNat =
                sz - 1 := by
              have hsz_wv : (BitVec.setWidth 64 (s.core.wvec[(2 * lit.toNat +
                  BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by rw [hs1]; omega))).toNat = sz := by
                simpa only [hs1] using h_sz
              rw [BitVec.toNat_setWidth, BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
                rw [hsz_wv, show (1#64 : BitVec 64).toNat = 1 from rfl]; omega)),
                hsz_wv, show (1#64 : BitVec 64).toNat = 1 from rfl,
                Nat.mod_eq_of_lt (by omega)]
            let wvec' := s.core.wvec.set (lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat
              (BitVec.setWidth 32 (BitVec.setWidth 64 (s.core.wvec[(2 * lit.toNat +
                BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by rw [hs1]; omega)) - 1#64))
            let wu' := s.core.wusable + 1#64
            let s' : FullState :=
              { s with core := { s.core with wvec := wvec', wstk := wstkF, wusable := wu' } }
            have hwlF : wstkF.length = c.wcap := by rw [List.length_set, hwl2]
            have hlen' : s'.LengthsOk c :=
              ⟨{ hcl with wvec_len := by simp [s', wvec', hwvl], wstk_len_arr := hwlF },
               hlen.scratch_ok⟩
            have hwvec_self : fullWatchOffCore s'.core lit.toNat = off ∧
                fullWatchSizeCore s'.core lit.toNat = sz - 1 := by
              constructor
              · unfold fullWatchOffCore; simp only [s', wvec']
                rw [List.getElem?_set_ne (by rw [hidx1]; omega)]; rfl
              · unfold fullWatchSizeCore; simp only [s', wvec']
                rw [hidx1, List.getElem?_eq_getElem (by rw [List.length_set]; omega),
                  List.getElem_set_self, Option.getD_some, hsz_m1_trunc]
            have hwvec_other : ∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
                fullWatchOffCore s'.core l = fullWatchOffCore s.core l ∧
                fullWatchSizeCore s'.core l = fullWatchSizeCore s.core l := by
              intro l _ hne; unfold fullWatchOffCore fullWatchSizeCore; simp only [s', wvec']
              rw [List.getElem?_set_ne (by rw [hidx1]; omega),
                  List.getElem?_set_ne (by rw [hidx1]; omega)]
              exact ⟨rfl, rfl⟩
            have h_wvec_le : ∀ l < 2 * s.core.cur_vars,
                fullWatchOffCore s'.core l = fullWatchOffCore s.core l ∧
                fullWatchSizeCore s'.core l ≤ fullWatchSizeCore s.core l := by
              intro l hl_lt
              by_cases hll : l = lit.toNat
              · subst hll; exact ⟨hwvec_self.1, by rw [hwvec_self.2]; omega⟩
              · obtain ⟨ho, hs⟩ := hwvec_other l hl_lt hll; exact ⟨ho, by omega⟩
            have houtF : ∀ idx, idx < off ∨ end_ ≤ idx → wstkF[idx]? = s.core.wstk[idx]? := by
              intro idx hidx
              rw [List.getElem?_set_ne (by rcases hidx with h | h <;> omega)]
              exact hout2 idx (hidx.imp (fun h => by omega) (fun h => by omega))
            have hpreF : ∀ k < q0 - off, wstkF[off + k]? = s.core.wstk[off + k]? := by
              intro k hk
              rw [List.getElem?_set_ne (by omega)]
              exact hout2 (off + k) (Or.inl (by omega))
            have hsufF : ∀ k < end_ - pB.toNat, wstkF[q0 + k]? = s.core.wstk[pB.toNat + k]? := by
              intro k hk
              rw [List.getElem?_set_ne (by omega)]
              simpa [show q0 + k + 1 = pB.toNat + k by omega] using
                hsh2 (q0 + k) (by omega) (by rw [hp2_end]; omega)
            have hsliceF : ∀ sp F_cur, BoolSlice sp F_cur s.core lit.toNat off (end_ - off) →
                BoolSlice sp F_cur s'.core lit.toNat off (sz - 1) := by
              intro sp F_cur hs
              obtain ⟨hBpre, hBsuf⟩ := hBslice sp F_cur hs
              have h1 := boolSlice_relocate (sp := sp) (k := s.core) (k' := s'.core)
                (p := off) (p' := off) (Nat.le_refl _) (fun _ r => r)
                (fun idx hidx => hpreF idx hidx) hBpre
              have h2 := boolSlice_relocate (sp := sp) (k := s.core) (k' := s'.core)
                (p := pB.toNat) (p' := q0) (Nat.le_refl _) (fun _ r => r)
                (fun idx hidx => hsufF idx hidx) hBsuf
              have hlen_eq : (pB.toNat - 1 - off) + (end_ - pB.toNat) = sz - 1 := by omega
              rw [← hlen_eq]
              exact boolSlice_append_slice h1
                (by simpa [show off + (pB.toNat - 1 - off) = q0 by omega] using h2)
            have hws_new : ∀ F_cur, WatchSliceOk F_cur s.core lit.toNat off sz →
                WatchSliceOk F_cur s'.core lit.toNat (fullWatchOff s' lit.toNat)
                  (fullWatchSize s' lit.toNat) := fun F_cur hw => by
              dsimp only [fullWatchOff, fullWatchSize]
              rw [hwvec_self.1, hwvec_self.2]
              exact hsliceF true F_cur (by simpa [BoolSlice, end_] using hw)
            have hdws_new : ∀ F_cur, DenseWatchSliceOk F_cur s.core lit.toNat off sz →
                DenseWatchSliceOk F_cur s'.core lit.toNat (fullWatchOff s' lit.toNat)
                  (fullWatchSize s' lit.toNat) := fun F_cur hw => by
              dsimp only [fullWatchOff, fullWatchSize]
              rw [hwvec_self.1, hwvec_self.2]
              exact hsliceF false F_cur (by simpa [BoolSlice, end_] using hw)
            have hshift_src : ∀ j < sz - 1,
                ∃ src < sz, wstkF[off + j]? = s.core.wstk[off + src]? := by
              intro j hj
              by_cases hjq : j < q0 - off
              · exact ⟨j, by omega, hpreF j hjq⟩
              · refine ⟨pB.toNat - off + (j - (q0 - off)), by omega, ?_⟩
                simpa [show off + j = q0 + (j - (q0 - off)) by omega,
                  show off + (pB.toNat - off + (j - (q0 - off))) =
                    pB.toNat + (j - (q0 - off)) by omega] using hsufF (j - (q0 - off)) (by omega)
            have hlayout' : WatchStackLayout s.core → WatchStackLayout s'.core := fun hlay =>
              ⟨fun l hl_lt => by
                obtain ⟨ho, hs⟩ := h_wvec_le l hl_lt
                have := hlay.bounds l hl_lt
                have hwl_eq : s'.core.wlen = s.core.wlen := rfl
                rw [ho, hwl_eq]; omega,
               fun l hl_lt hpos => by
                obtain ⟨ho, hs⟩ := h_wvec_le l hl_lt
                rw [ho]; exact hlay.pos_off l hl_lt (by omega),
               fun l1 l2 h1 h2 hne hp1 hp2 => by
                obtain ⟨ho1, hs1⟩ := h_wvec_le l1 h1; obtain ⟨ho2, hs2⟩ := h_wvec_le l2 h2
                rcases hlay.disjoint l1 l2 h1 h2 hne (by omega) (by omega) with hl1 | hl2
                · left; rw [ho1, ho2]; omega
                · right; rw [ho1, ho2]; omega,
               fun l hl_lt idx hidx => by
                by_cases hll : l = lit.toNat
                · subst hll
                  rw [hwvec_self.2] at hidx
                  rw [hwvec_self.1]
                  obtain ⟨src, hsrc, heq⟩ := hshift_src idx hidx
                  rw [heq]; exact hlay.no_sentinel lit.toNat hlit_lt src hsrc
                · obtain ⟨ho, hs⟩ := hwvec_other l hl_lt hll
                  rw [ho]; rw [hs] at hidx
                  have hout_idx : fullWatchOffCore s.core l + idx < off ∨
                      end_ ≤ fullWatchOffCore s.core l + idx := by
                    rcases hlay.disjoint l lit.toNat hl_lt hlit_lt hll (by omega) hsz_pos
                      with h1 | h2
                    · left; omega
                    · right; omega
                  rw [houtF _ hout_idx]; exact hlay.no_sentinel l hl_lt idx hidx⟩
            have hmw' : ∀ F_cur, ModeWatchesInv F_cur s.core → ModeWatchesInv F_cur s'.core :=
              fun F_cur hmw => by
                have hslice_mode : if s.core.dense_mode = 0#64 then
                    WatchSliceOk F_cur s'.core lit.toNat off (end_ - 1 - off)
                  else DenseWatchSliceOk F_cur s'.core lit.toNat off (end_ - 1 - off) := by
                  have hsub_eq : end_ - 1 - off = sz - 1 := by omega
                  rw [hsub_eq]
                  by_cases hdm : s.core.dense_mode = 0#64 <;>
                    simp only [ModeWatchesInv, hdm, ↓reduceIte] at hmw ⊢
                  · exact by simpa only [fullWatchOff, fullWatchSize, hwvec_self.1,
                      hwvec_self.2] using hws_new F_cur (hmw.slices lit.toNat hlit_lt)
                  · exact by simpa only [fullWatchOff, fullWatchSize, hwvec_self.1,
                      hwvec_self.2] using hdws_new F_cur (hmw.slices lit.toNat hlit_lt)
                exact fbl_compactSlice_preserves_modeWatches hmw rfl rfl rfl (fun _ r => r) hlit_lt
                  (by omega : off ≤ end_ - 1) (by omega)
                  (by rw [hwvec_self.1, hwvec_self.2]; exact ⟨rfl, by omega⟩)
                  hwvec_other houtF hslice_mode
            have hget1 : s.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                rw [hs1]; omega) = s.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat) + 1).toNat]'(by
                  rw [show (BitVec.setWidth 64 lit <<< (1 : Nat) + (1 : BitVec 64)).toNat =
                    2 * lit.toNat + 1 from hidx1]; omega) :=
              Option.some.inj (by
                rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, hs1,
                  show (1 : BitVec 64) = 1#64 from rfl, hidx1])
            have hwv_hm : wvec' = s.core.wvec.set (BitVec.setWidth 64 lit <<< (1 : Nat) + 1).toNat
                (BitVec.setWidth 32 (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 lit <<<
                  (1 : Nat) + 1).toNat]'(by
                    rw [show (BitVec.setWidth 64 lit <<< (1 : Nat) + (1 : BitVec 64)).toNat =
                      2 * lit.toNat + 1 from hidx1]; omega)) - 1)) := by
              dsimp only [wvec']; rw [hget1, show (1#64 : BitVec 64) = 1 from rfl]
            have hwu_hm : wu' = s.core.wusable + 1 := rfl
            have hst_hm : wstkF = wstk2.set (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64
                lit <<< (1 : Nat)).toNat]'(by rw [hidx0]; omega)) +
                BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat) + 1).toNat]'
                  (by
                    rw [show (BitVec.setWidth 64 lit <<< (1 : Nat) + (1 : BitVec 64)).toNat =
                      2 * lit.toNat + 1 from hidx1]; omega)) - 1).toNat 0xFFFFFFFF#32 := by
              dsimp only [wstkF]; rw [← h1_m1, hget1, show (1#64 : BitVec 64) = 1 from rfl]
            fbl_group
            refine hQ wvec' wstkF wu' _ hlen' (fun _ => ⟨hwvec_self.1, ?_⟩)
              hwvec_other (fun idx _ hidx => houtF idx (by have := hidx hlit_lt; omega))
              hws_new hdws_new hlayout' hmw' (by rw [hwv_hm, hwu_hm, hst_hm]; exact hm)
            change fullWatchSizeCore s'.core lit.toNat ≤ fullWatchSizeCore s.core lit.toNat
            rw [hwvec_self.2]; omega
      · exact hret_same
    · -- Loop 1 body (`hbody`)
      intro B L p mL hB hL ⟨hmL, hp_lo, hp_hi, hLslice⟩
      subst mL
      fbl_group
      · have hp_lt : p.toNat < end_ := by rw [← h_cond_lt]; assumption
        have hp_lt_cap : p.toNat < c.wcap := by omega
        have hw0_eq : s.core.wstk[p.toNat]? = some (s.core.wstk[p.toNat]'(by omega)) :=
          List.getElem?_eq_getElem (by omega)
        have hp1_eq : (p + 1#64).toNat = p.toNat + 1 := by
          simp [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega : p.toNat + 1 < 2 ^ 64)]
        fbl_unmdata; repeat fbl_strip
        fbl_split_jnz
        · have hbin := hc
          fbl_group
          · exact hB (p + 1#64, true) m ⟨rfl, Or.inr ⟨rfl, by omega, by omega, fun sp F_cur hs =>
              have hex := boolSlice_extend1 hp_lo hp_lt hw0_eq hbin
                (hLslice sp F_cur hs).1 (hLslice sp F_cur hs).2
              ⟨by simpa only [hp1_eq, Nat.add_sub_cancel] using (hLslice sp F_cur hs).1,
               by simpa only [hp1_eq] using hex.2⟩⟩⟩
          · exact hL (p + 1#64) m (by rw [hp1_eq]; omega) ⟨rfl, by omega, by omega,
              fun sp F_cur hs => by
                have hex := boolSlice_extend1 hp_lo hp_lt hw0_eq hbin
                  (hLslice sp F_cur hs).1 (hLslice sp F_cur hs).2
                simpa only [hp1_eq] using hex⟩
        · have hlg := hc
          s8_hsteps_nj
          refine wp_join_group (ts := [i64])
            (fun (p', ()) m' => m' = m ∧ off ≤ p'.toNat ∧ p'.toNat ≤ end_ ∧
              p.toNat < p'.toNat ∧
              ∀ sp F_cur, BoolSlice sp F_cur s.core lit.toNat off (end_ - off) →
                BoolSlice sp F_cur s.core lit.toNat off (p'.toNat - off) ∧
                BoolSlice sp F_cur s.core lit.toNat p'.toNat (end_ - p'.toNat))
            (fun _ (p', ()) m' ⟨hm', hp'_lo, hp'_hi, hp'_gt, hP'⟩ =>
              hJ (p', false, ()) m' (hL p' m' (by omega) ⟨hm', hp'_lo, hp'_hi, hP'⟩))
            (fun Jin hJin => by
              fbl_split_jnz
              · have hp1_lt : (p + 1#64).toNat < end_ := by rw [← h_cond_lt]; assumption
                have hp2_eq : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by
                  simp [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega : p.toNat + 2 < 2 ^ 64)]
                fbl_group
                exact hJin (p + 1#64 + 1#64, ()) m ⟨rfl, by omega, by omega, by omega,
                  fun sp F_cur hs => by
                    have hex := boolSlice_extend2 hp_lo hp_lt hw0_eq hlg
                      (hLslice sp F_cur hs).1 (hLslice sp F_cur hs).2
                    simpa only [hp2_eq] using ⟨hex.2.1, hex.2.2⟩⟩
              · have hp1_not : ¬ (p + 1#64).toNat < end_ := by rw [← h_cond_lt]; assumption
                fbl_group
                exact hJin (p + 1#64, ()) m ⟨rfl, by omega, by omega, by omega,
                  fun sp F_cur hs => False.elim (by
                    have h2 := (boolSlice_extend2 hp_lo hp_lt hw0_eq hlg
                      (hLslice sp F_cur hs).1 (hLslice sp F_cur hs).2).1
                    omega)⟩)
      · exact hB (p, false) m ⟨rfl, Or.inl rfl⟩
    · -- Loop 1 entry (`hentry`)
      intro B L hB hL
      fbl_group
      exact hL (BitVec.setWidth 64 (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'
        (by rw [hidx0]; omega))) m ⟨rfl, by simpa only [off, h_off] using Nat.le_refl _,
          by rw [h_off]; omega, fun sp F_cur hs => by
          rw [h_off, show off - off = 0 by omega, show end_ - off = sz by omega]
          refine ⟨?_, by simpa [end_] using hs⟩
          cases sp <;> simp only [BoolSlice, ↓reduceIte, Bool.false_eq_true] <;> exact .empty⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep8

end
