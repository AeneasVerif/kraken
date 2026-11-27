/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Src.Arena
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb

/-!
# Soundness Proofs for `Kissat.Src.Arena` (`Proof.Arena.Wp`)

Proves parametric `(Γ : Env)` `Func.wp` theorems for all `2` functions in `Src.Arena.fns`:
1. `full_arena_next_wp` against `fullArenaNextSpec`.
2. `full_alloc_cl_wp` against `fullAllocClSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Arena

open Std.Sat
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Arena
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

private theorem setWidth32_ofNat64 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.setWidth 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, bv64_ofNat_toNat hn, BitVec.toNat_ofNat]

private theorem bv32_eq_and_7ffff {x : BitVec 32} (hx : x.toNat ≤ 0x7FFFF) :
    x = x &&& 0x7FFFF#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and]
  by_cases h19 : i < 19
  · have hm : ∀ j < 19, (0x7FFFF#32 : BitVec 32).getLsbD j = true := by decide
    simp [hm i h19]
  · have hlt : x.toNat < 2 ^ i :=
      Nat.lt_of_le_of_lt hx (Nat.lt_of_lt_of_le (by decide : 0x7FFFF < 2 ^ 19)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    have hxf : x.getLsbD i = false := Nat.testBit_lt_two_pow hlt
    simp [hxf]

private theorem bv32_or_and_distrib (a b c : BitVec 32) :
    (a ||| b) &&& c = (a &&& c) ||| (b &&& c) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl

private theorem bv32_and_shrk_zero {g : BitVec 32} (hg : g.toNat ≤ 0x7FFFF) :
    (g &&& 0x00800000#32) = 0#32 := by
  rw [bv32_eq_and_7ffff hg, BitVec.and_assoc,
    show (0x7FFFF#32 &&& 0x00800000#32 : BitVec 32) = 0#32 from rfl, BitVec.and_zero]

private theorem bv32_and_garb_zero {g : BitVec 32} (hg : g.toNat ≤ 0x7FFFF) :
    (g &&& 0x00080000#32) = 0#32 := by
  rw [bv32_eq_and_7ffff hg, BitVec.and_assoc,
    show (0x7FFFF#32 &&& 0x00080000#32 : BitVec 32) = 0#32 from rfl, BitVec.and_zero]

private theorem bv32_and_red_zero {g : BitVec 32} (hg : g.toNat ≤ 0x7FFFF) :
    (g &&& 0x00400000#32) = 0#32 := by
  rw [bv32_eq_and_7ffff hg, BitVec.and_assoc,
    show (0x7FFFF#32 &&& 0x00400000#32 : BitVec 32) = 0#32 from rfl, BitVec.and_zero]

private theorem arena_alloc_finish {Q : Post [i64]} {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m' : Mem 64} {sz : BitVec 32} {red : Bool}
    {al' : Nat} {arena' : List (BitVec 32)}
    (hQ : ∀ (arena1 : List (BitVec 32)) (m1 : Mem 64),
      FullState.LengthsOk c { s with core := { s.core with
        arena_len := s.core.arena_len + 3 + sz.toNat, arena := arena1 } } →
      (∀ i < s.core.arena_len, arena1[i]? = s.core.arena[i]?) →
      (arena1[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32 →
      (arena1[s.core.arena_len]?.getD 0#32 &&& 0x00080000#32) = 0#32 →
      ((arena1[s.core.arena_len]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ↔ red = true) →
      (arena1[s.core.arena_len + 2]?.getD 0#32).toNat = sz.toNat →
      (FullMem c { s with core := { s.core with
        arena_len := s.core.arena_len + 3 + sz.toNat, arena := arena1 } } ⋆ R) m1 →
      Q (BitVec.ofNat 64 s.core.arena_len, ()) m1)
    (hm : (FullMem c { s with core := { s.core with
      arena_len := al', arena := arena' } } ⋆ R) m')
    (hal : al' = s.core.arena_len + 3 + sz.toNat)
    (hlen' : FullState.LengthsOk c { s with core := { s.core with
      arena_len := s.core.arena_len + 3 + sz.toNat, arena := arena' } })
    (hpres : ∀ i < s.core.arena_len, arena'[i]? = s.core.arena[i]?)
    (hns : (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hng : (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00080000#32) = 0#32)
    (hred : (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ↔ red = true)
    (hsz : (arena'[s.core.arena_len + 2]?.getD 0#32).toNat = sz.toNat) :
    Q (BitVec.ofNat 64 s.core.arena_len, ()) m' := by
  subst hal; exact hQ arena' m' hlen' hpres hns hng hred hsz hm

private theorem arena_add2_toNat (cref : BitVec 32) :
    (BitVec.setWidth 64 cref + 2).toNat = cref.toNat + 2 := by
  have := cref.isLt; bv_omega

private theorem arena_p0_toNat (cref szv : BitVec 32) :
    (BitVec.setWidth 64 cref + 3 + BitVec.setWidth 64 szv).toNat =
      cref.toNat + 3 + szv.toNat := by
  have := cref.isLt; have := szv.isLt; bv_omega

private theorem fullArenaNextOff_ge_skip {ar : List (BitVec 32)} {alen cref : Nat}
    (hle1 : ¬ (cref + 3 > alen)) (p : Nat)
    (hp : p = cref + 3 + (ar[cref + 2]?.getD 0#32).toNat)
    (hle2 : ¬ (p > alen))
    (hshrk : (ar[cref]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32) :
    fullArenaNextOff ar alen cref = fullArenaSkipShrk ar alen p (alen - p) := by
  unfold fullArenaNextOff
  simp only [hle1, ↓reduceIte, ← hp, hle2, hshrk, ne_eq, not_false_eq_true]

private theorem fullArenaSkipShrk_step {ar : List (BitVec 32)} {alen p : Nat}
    (hlt : p < alen) (_hfl : 0 < alen - p) :
    fullArenaSkipShrk ar alen p (alen - p) =
      if ar[p]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 then
        fullArenaSkipShrk ar alen (p + 1) (alen - (p + 1))
      else p + 1 := by
  have hk : alen - p = (alen - (p + 1)) + 1 := by omega
  conv => lhs; rw [hk]; unfold fullArenaSkipShrk
  simp only [hlt, ↓reduceIte]

/-- Soundness proof for `full_arena_next` against canonical `fullArenaNextSpec`. -/
theorem full_arena_next_wp (Γ : Env) :
    ∀ a m Q X, fullArenaNextSpec a m Q X → Func.wp Γ full_arena_next_body a m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hcl := hlen.core_ok
  have harena_len_arr := hcl.arena_len_arr
  have harena_len_le := hcl.arena_len_le
  have harena_cap_lt : c.arena_cap < 2 * dimacsBound := c.harena
  unfold dimacsBound at harena_cap_lt
  have hcref_lt : cref.toNat < 2 ^ 32 := cref.isLt
  have hm2_64 : (cref.toNat + 2) % 2 ^ 64 = cref.toNat + 2 := Nat.mod_eq_of_lt (by omega)
  have hm3_64 : (cref.toNat + BitVec.toNat (3 : BitVec 64)) % 2 ^ 64 = cref.toNat + 3 :=
    Nat.mod_eq_of_lt (by simp; omega)
  unfold Func.wp full_arena_next_body
  c0_hsteps
  · have hgt : cref.toNat + 3 > s.core.arena_len := by
      simp only [show (BitVec.toNat (3 : BitVec 64)) = 3 from rfl] at *
      c0_bound
    have hnxt : fullArenaNextOff s.core.arena s.core.arena_len cref.toNat = s.core.arena_len := by
      unfold fullArenaNextOff; simp [hgt]
    rw [hnxt] at hQ
    rwa [setWidth32_ofNat64 (n := s.core.arena_len) (by omega)]
  · have hle1 : ¬ (cref.toNat + 3 > s.core.arena_len) := by
      (try simp only [hm3_64] at *); c0_bound
    have hcr_lt : cref.toNat < s.core.arena.length := by omega
    have hcr2_lt : cref.toNat + 2 < s.core.arena.length := by omega
    have hsz_isLt : (s.core.arena[cref.toNat + 2]'hcr2_lt).toNat < 2 ^ 32 :=
      (s.core.arena[cref.toNat + 2]'hcr2_lt).isLt
    have hsz_eq : (s.core.arena[cref.toNat + 2]?.getD 0#32).toNat =
        (s.core.arena[cref.toNat + 2]'hcr2_lt).toNat := by
      rw [List.getElem?_eq_getElem hcr2_lt, Option.getD_some]
    have hmp_64 : (BitVec.toNat cref + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 =
        cref.toNat + 2 := by simp; omega
    have hp_gt : cref.toNat + 3 + (s.core.arena[cref.toNat + 2]'hcr2_lt).toNat >
        s.core.arena_len := by
      (try simp only [hmp_64] at *); c0_bound
    have hnxt : fullArenaNextOff s.core.arena s.core.arena_len cref.toNat = s.core.arena_len := by
      unfold fullArenaNextOff; simp [hle1, hsz_eq, hp_gt]
    rw [hnxt] at hQ
    rwa [setWidth32_ofNat64 (n := s.core.arena_len) (by omega)]
  · have hle1 : ¬ (cref.toNat + 3 > s.core.arena_len) := by
      (try simp only [hm3_64] at *); c0_bound
    have hcr_lt : cref.toNat < s.core.arena.length := by omega
    have hcr2_lt : cref.toNat + 2 < s.core.arena.length := by omega
    have hsz_isLt : (s.core.arena[cref.toNat + 2]'hcr2_lt).toNat < 2 ^ 32 :=
      (s.core.arena[cref.toNat + 2]'hcr2_lt).isLt
    have hsz_eq : (s.core.arena[cref.toNat + 2]?.getD 0#32).toNat =
        (s.core.arena[cref.toNat + 2]'hcr2_lt).toNat := by
      rw [List.getElem?_eq_getElem hcr2_lt, Option.getD_some]
    have hmp_64 : (BitVec.toNat cref + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 =
        cref.toNat + 2 := by simp; omega
    have hle2 : ¬ (cref.toNat + 3 + (s.core.arena[cref.toNat + 2]'hcr2_lt).toNat >
        s.core.arena_len) := by
      simp only [hmp_64] at *; c0_bound
    have hshrk : (s.core.arena[cref.toNat]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := by
      rw [List.getElem?_eq_getElem hcr_lt, Option.getD_some]; c0_bound
    let p0 := cref.toNat + 3 + (s.core.arena[cref.toNat + 2]'hcr2_lt).toNat
    have hp0_eq : p0 = cref.toNat + 3 + (s.core.arena[cref.toNat + 2]?.getD 0#32).toNat :=
      congrArg (cref.toNat + 3 + ·) hsz_eq.symm
    have hnxt0 := fullArenaNextOff_ge_skip hle1 p0 hp0_eq (by simpa only [p0] using hle2) hshrk
    refine wp_loop_inv (ts := [i64])
      (fun (t, ()) mL =>
        p0 ≤ t.toNat ∧ t.toNat ≤ s.core.arena_len ∧
        fullArenaNextOff s.core.arena s.core.arena_len cref.toNat =
          fullArenaSkipShrk s.core.arena s.core.arena_len t.toNat
            (s.core.arena_len - t.toNat) ∧
        mL = m)
      (fun (t, ()) _ => s.core.arena_len - t.toNat)
      (fun J hLoop => ?_)
      (fun J (t, ()) mL ⟨hp0_le, ht_le, hskip_eq, hm_eq⟩ hLoop => ?_)
    · c0_hsteps
      have ha2 := arena_add2_toNat cref
      have har2_eq :
          (s.core.arena[(BitVec.setWidth 64 cref + 2).toNat]'(by rw [ha2]; exact hcr2_lt)) =
            s.core.arena[cref.toNat + 2]'hcr2_lt := by
        simp only [ha2]
      have htp0 : (BitVec.setWidth 64 cref + 3 +
          BitVec.setWidth 64 s.core.arena[(BitVec.setWidth 64 cref + 2).toNat]).toNat = p0 := by
        rw [arena_p0_toNat, har2_eq]
      refine hLoop _ m ⟨by rw [htp0]; exact Nat.le_refl _, by rw [htp0]; exact Nat.not_lt.mp hle2,
        ?_, rfl⟩
      rw [hnxt0, htp0]
    · subst hm_eq
      rw [Blocks.get_here]; dsimp only
      c0_hsteps
      · have ht_lt : t.toNat < s.core.arena_len := by c0_bound
        have ht_arr : t.toNat < s.core.arena.length := by omega
        have hstep := @fullArenaSkipShrk_step s.core.arena s.core.arena_len t.toNat
          ht_lt (by omega : 0 < s.core.arena_len - t.toNat)
        have hne : s.core.arena[t.toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
          rw [List.getElem?_eq_getElem ht_arr, Option.getD_some]; c0_bound
        rw [ite_eq_left hne] at hstep
        refine hLoop (t + 1, ()) mL (by dsimp only; bv_omega)
          ⟨by bv_omega, by bv_omega, ?_, rfl⟩
        rw [hskip_eq, hstep]; congr 1 <;> bv_omega
      · have ht_lt : t.toNat < s.core.arena_len := by c0_bound
        have ht_arr : t.toNat < s.core.arena.length := by omega
        have hstep := @fullArenaSkipShrk_step s.core.arena s.core.arena_len t.toNat
          ht_lt (by omega : 0 < s.core.arena_len - t.toNat)
        have heq : s.core.arena[t.toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
          rw [List.getElem?_eq_getElem ht_arr, Option.getD_some]; c0_bound
        rw [ite_eq_right (by simpa using heq)] at hstep
        rw [hskip_eq, hstep] at hQ
        have hsw : BitVec.setWidth 32 (t + 1) = BitVec.ofNat 32 (t.toNat + 1) := by
          apply BitVec.eq_of_toNat_eq
          have hadd1 : (t + 1).toNat = t.toNat + 1 := by bv_omega
          rw [BitVec.toNat_setWidth, hadd1, BitVec.toNat_ofNat]
        rwa [hsw]
      · have ht_eq : t.toNat = s.core.arena_len := by c0_bound
        have hfl0 : s.core.arena_len - t.toNat = 0 := by omega
        rw [hskip_eq, hfl0, fullArenaSkipShrk, ht_eq, Nat.min_self] at hQ
        have ht_bv : t = BitVec.ofNat 64 s.core.arena_len :=
          BitVec.eq_of_toNat_eq (by rw [ht_eq, bv64_ofNat_toNat (by omega)])
        rw [ht_bv]; rwa [setWidth32_ofNat64 (n := s.core.arena_len) (by omega)]
  · have hle1 : ¬ (cref.toNat + 3 > s.core.arena_len) := by
      (try simp only [hm3_64] at *); c0_bound
    have hcr_lt : cref.toNat < s.core.arena.length := by omega
    have hcr2_lt : cref.toNat + 2 < s.core.arena.length := by omega
    have hsz_isLt : (s.core.arena[cref.toNat + 2]'hcr2_lt).toNat < 2 ^ 32 :=
      (s.core.arena[cref.toNat + 2]'hcr2_lt).isLt
    have hsz_eq : (s.core.arena[cref.toNat + 2]?.getD 0#32).toNat =
        (s.core.arena[cref.toNat + 2]'hcr2_lt).toNat := by
      rw [List.getElem?_eq_getElem hcr2_lt, Option.getD_some]
    have hmp_64 : (BitVec.toNat cref + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 =
        cref.toNat + 2 := by simp; omega
    have hle2 : ¬ (cref.toNat + 3 + (s.core.arena[cref.toNat + 2]'hcr2_lt).toNat >
        s.core.arena_len) := by
      (try simp only [hmp_64] at *); c0_bound
    have hns : (s.core.arena[cref.toNat]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
      rw [List.getElem?_eq_getElem hcr_lt, Option.getD_some]; c0_bound
    have hnxt : fullArenaNextOff s.core.arena s.core.arena_len cref.toNat =
        cref.toNat + 3 + (s.core.arena[cref.toNat + 2]'hcr2_lt).toNat := by
      unfold fullArenaNextOff; simp [hle1, hsz_eq, hle2, hns]
    rw [hnxt] at hQ
    have hidx2 := arena_add2_toNat cref
    have har2_eq :
        (s.core.arena[(BitVec.setWidth 64 cref + 2).toNat]'(by rw [hidx2]; exact hcr2_lt)) =
          s.core.arena[cref.toNat + 2]'hcr2_lt := by
      simp only [hidx2]
    have hs64 : (BitVec.setWidth 64 cref + 3 +
          BitVec.setWidth 64 s.core.arena[(BitVec.setWidth 64 cref + 2).toNat]).toNat =
        cref.toNat + 3 + (s.core.arena[cref.toNat + 2]'hcr2_lt).toNat := by
      rw [arena_p0_toNat, har2_eq]
    have hres : BitVec.setWidth 32 (BitVec.setWidth 64 cref + 3 +
          BitVec.setWidth 64 s.core.arena[(BitVec.setWidth 64 cref + 2).toNat]) =
        BitVec.ofNat 32 (cref.toNat + 3 + (s.core.arena[cref.toNat + 2]'hcr2_lt).toNat) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, hs64, BitVec.toNat_ofNat]
    rwa [hres]

/-- Soundness proof for `full_alloc_cl` against canonical `fullAllocClSpec`. -/
theorem full_alloc_cl_wp (Γ : Env) :
    ∀ a m Q X, fullAllocClSpec a m Q X → Func.wp Γ full_alloc_cl_body a m Q X := by
  rintro ⟨h, sz, glue, red, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hcl := hlen.core_ok
  have hal_len := hcl.arena_len_arr
  have hal_le := hcl.arena_len_le
  have harena_cap_lt : c.arena_cap < 2 * dimacsBound := c.harena
  unfold dimacsBound at harena_cap_lt
  have hsz_lt : sz.toNat < 2 ^ 32 := sz.isLt
  have hbv3 : (3 : BitVec 64).toNat = 3 := rfl
  unfold Func.wp full_alloc_cl_body
  c0_hsteps_nogrp
  · have hoom : c.arena_cap - s.core.arena_len < 3 + sz.toNat := by
      simp only [hbv3] at *; c0_bound
    rw [ite_eq_left hoom] at hQ
    exact hQ
  · simp only [hbv3] at *
    have hfit : s.core.arena_len + 3 + sz.toNat ≤ c.arena_cap := by c0_bound
    rw [ite_eq_right (by omega : ¬ (c.arena_cap - s.core.arena_len < 3 + sz.toNat))] at hQ
    refine wp_join_group (ts := [i32])
      (fun (g, ()) mJ => g.toNat ≤ 0x7FFFF ∧ mJ = m) ?_ ?_
    · rintro _ ⟨g, ⟨⟩⟩ mJ ⟨hg_le, hmJ⟩
      subst hmJ
      rw [Blocks.get_here]; dsimp only
      have h0 : (BitVec.ofNat 64 s.core.arena_len).toNat = s.core.arena_len :=
        bv64_ofNat_toNat (by omega)
      have h1 : (BitVec.ofNat 64 s.core.arena_len + 1).toNat = s.core.arena_len + 1 := by
        c0_bound
      have h2 : (BitVec.ofNat 64 s.core.arena_len + 2).toNat = s.core.arena_len + 2 := by
        c0_bound
      have hal_eq : (BitVec.ofNat 64 s.core.arena_len + (3 + BitVec.setWidth 64 sz)).toNat =
          s.core.arena_len + 3 + sz.toNat := by c0_bound
      refine wp_join_group (ts := [i32])
        (fun (r, ()) mR =>
          ((r = 0x00400000#32 ∧ red = true) ∨ (r = 0#32 ∧ red = false)) ∧ mR = mJ) ?_ ?_
      · rintro _ ⟨r, ⟨⟩⟩ mR ⟨hr, hmR⟩
        subst hmR
        rw [Blocks.get_here]; dsimp only
        c0_steps
        refine arena_alloc_finish hQ (by assumption) ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · c0_bound
        · exact ⟨{ hcl with arena_len_arr := by simp [hal_len], arena_len_le := hfit },
            hlen.scratch_ok⟩
        · intro i hi
          simp only [h0, h1, h2]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_ne (by omega)]
        · simp only [h0, h1, h2]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_self (by simp [hal_len]; omega), Option.getD_some,
            bv32_or_and_distrib, bv32_and_shrk_zero hg_le]
          rcases hr with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
        · simp only [h0, h1, h2]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_self (by simp [hal_len]; omega), Option.getD_some,
            bv32_or_and_distrib, bv32_and_garb_zero hg_le]
          rcases hr with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
        · simp only [h0, h1, h2]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_self (by simp [hal_len]; omega), Option.getD_some,
            bv32_or_and_distrib, bv32_and_red_zero hg_le]
          rcases hr with ⟨rfl, ht⟩ | ⟨rfl, hf⟩
          · exact ⟨fun _ => ht, fun _ => by decide⟩
          · exact ⟨fun hne => absurd (by decide) hne, fun ht => absurd ht (by simp [hf])⟩
        · simp only [h0, h1, h2]
          rw [List.getElem?_set_self (by simp [hal_len]; omega), Option.getD_some]
      · intro Jr hJr
        c0_hsteps_nogrp
        · exact hJr (0x00400000#32, ()) mJ ⟨Or.inl ⟨rfl, by assumption⟩, rfl⟩
        · exact hJr (0#32, ()) mJ ⟨Or.inr ⟨rfl, by cases red <;> simp_all⟩, rfl⟩
    · intro J hJ
      c0_hsteps_nogrp
      · exact hJ (0x7FFFF#32, ()) m ⟨by decide, rfl⟩
      · refine hJ (glue, ()) m ⟨?_, rfl⟩
        c0_bound

end LeanQbe.T.Examples.Kissat.Proof.Arena
