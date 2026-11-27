/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Extend.Spec
public import LeanQbe.T.Examples.Kissat.Src.Extend
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Witness Stack Push WP Proofs for `Kissat.Src.Extend`

Proves `Func.wp Γ ...` against `CanonicalEnv` specs for:
- `full_extend_push2` (`full_extend_push2_wp`)
- `full_extend_push_cl` (`full_extend_push_cl_wp`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Extend

open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Extend
open Kraken.Bedrock2.Test
open scoped FullArenaTactics

private theorem bv_zext_toNat {w1 w2 : Nat} (x : BitVec w1) (hle : w1 ≤ w2) :
    (x.setWidth w2).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) hle))]

private theorem bv32_add1 {a : BitVec 32} (h : a.toNat + 1 < 2 ^ 32) :
    (a + 1#32).toNat = a.toNat + 1 :=
  bv32_add_small_eq (by simpa using h)

private theorem bv64_add1 {a : BitVec 64} (h : a.toNat + 1 < 2 ^ 64) :
    (a + 1#64).toNat = a.toNat + 1 :=
  bv64_add_small_eq (by simpa using h)

private theorem ext_bv64_shl1_toNat {v : BitVec 64} (hv : v.toNat < 2 ^ 63) :
    (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
  rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega

private theorem fullMem_cast {c : FullCfg} {s s' : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) (heq : s = s') : (FullMem c s' ⋆ R) m :=
  heq ▸ hm

private def extLitSkip (vals : List (BitVec 8)) (lvl : List (BitVec 32))
    (nlits : Nat) (lit : BitVec 32) : Bool :=
  decide (lit.toNat < nlits ∧
    lvl[lit.toNat / 2]?.getD 0#32 = 0#32 ∧
    ((vals[lit.toNat]?.getD 0#8).signExtend 32).slt 0#32 = true)

private def extLitKeep (ar : List (BitVec 32)) (vals : List (BitVec 8))
    (lvl : List (BitVec 32)) (cref nlits : Nat) (bl : BitVec 32) (j : Nat) : Bool :=
  let lit := (ar[cref + 3 + j]?.getD 0#32) &&& 0x7FFFFFFF#32
  decide (lit ≠ bl) && !(extLitSkip vals lvl nlits lit)

private def extKeepCount (ar : List (BitVec 32)) (vals : List (BitVec 8))
    (lvl : List (BitVec 32)) (cref nlits : Nat) (bl : BitVec 32) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    extKeepCount ar vals lvl cref nlits bl n +
      if extLitKeep ar vals lvl cref nlits bl n then 1 else 0

private theorem extKeepCount_zero (ar : List (BitVec 32)) (vals : List (BitVec 8))
    (lvl : List (BitVec 32)) (cref nlits : Nat) (bl : BitVec 32) :
    extKeepCount ar vals lvl cref nlits bl 0 = 0 := rfl

private theorem extKeepCount_succ (ar : List (BitVec 32)) (vals : List (BitVec 8))
    (lvl : List (BitVec 32)) (cref nlits : Nat) (bl : BitVec 32) (n : Nat) :
    extKeepCount ar vals lvl cref nlits bl (n + 1) =
      extKeepCount ar vals lvl cref nlits bl n +
        if extLitKeep ar vals lvl cref nlits bl n then 1 else 0 := rfl

private theorem extKeepCount_le (ar : List (BitVec 32)) (vals : List (BitVec 8))
    (lvl : List (BitVec 32)) (cref nlits : Nat) (bl : BitVec 32) :
    ∀ n, extKeepCount ar vals lvl cref nlits bl n ≤ n
  | 0 => Nat.le_refl 0
  | n + 1 => by
    rw [extKeepCount_succ]
    have ih := extKeepCount_le ar vals lvl cref nlits bl n
    split <;> omega

private theorem extKeepCount_mono (ar : List (BitVec 32)) (vals : List (BitVec 8))
    (lvl : List (BitVec 32)) (cref nlits : Nat) (bl : BitVec 32) :
    ∀ {a b}, a ≤ b →
      extKeepCount ar vals lvl cref nlits bl a ≤ extKeepCount ar vals lvl cref nlits bl b
  | a, b, hab => by
    induction hab with
    | refl => exact Nat.le_refl _
    | step _ ih =>
      rw [extKeepCount_succ]
      split <;> omega

private theorem extLitKeep_eq_true {ar : List (BitVec 32)} {vals : List (BitVec 8)}
    {lvl : List (BitVec 32)} {cref nlits j : Nat} {bl lit : BitVec 32}
    (hlit : (ar[cref + 3 + j]?.getD 0#32) &&& 0x7FFFFFFF#32 = lit)
    (hne : lit ≠ bl)
    (hnskip : ¬ (lit.toNat < nlits ∧ lvl[lit.toNat / 2]?.getD 0#32 = 0#32 ∧
      ((vals[lit.toNat]?.getD 0#8).signExtend 32).slt 0#32 = true)) :
    extLitKeep ar vals lvl cref nlits bl j = true := by
  unfold extLitKeep extLitSkip; rw [hlit]; simp [hne, hnskip]

private theorem extLitKeep_eq_false_skip {ar : List (BitVec 32)} {vals : List (BitVec 8)}
    {lvl : List (BitVec 32)} {cref nlits j : Nat} {bl lit : BitVec 32}
    (hlit : (ar[cref + 3 + j]?.getD 0#32) &&& 0x7FFFFFFF#32 = lit)
    (hlt : lit.toNat < nlits) (hlvl : lvl[lit.toNat / 2]?.getD 0#32 = 0#32)
    (hval : ((vals[lit.toNat]?.getD 0#8).signExtend 32).slt 0#32 = true) :
    extLitKeep ar vals lvl cref nlits bl j = false := by
  unfold extLitKeep extLitSkip; rw [hlit]; simp [hlt, hlvl, hval]

private theorem extLitKeep_eq_false_bl {ar : List (BitVec 32)} {vals : List (BitVec 8)}
    {lvl : List (BitVec 32)} {cref nlits j : Nat} {bl : BitVec 32}
    (heq : (ar[cref + 3 + j]?.getD 0#32) &&& 0x7FFFFFFF#32 = bl) :
    extLitKeep ar vals lvl cref nlits bl j = false := by
  unfold extLitKeep; rw [heq]; simp

public section

theorem full_extend_push2_wp (Γ : Env) :
    ∀ a m Q X, Spec.fullExtendPush2Spec a m Q X →
      Func.wp Γ full_extend_push2_body a m Q X := by
  rintro ⟨h, blk_lit, other, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, hel⟩, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hlen hm hQ
  have hcap : c.extend_cap < dimacsBound := c.hext
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hcap hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  have hv_len := hlen.core_ok.vals_len
  have hl_len := hlen.core_ok.lvl_len
  have hesl := hlen.scratch_ok.extend_stk_len
  have hnlits :
      ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    have h1 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [ext_bv64_shl1_toNat (by omega), h1]
  unfold Func.wp full_extend_push2_body
  c0_hsteps_nogrp
  refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ())) (fun _ => True) ?_ ?_
  · intro _ skip_ot _
    c0_hsteps_nogrp
    refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
      (fun need => need = (if skip_ot then 1#64 else 2#64)) ?_ ?_
    · intro _ need hneed
      have hneed_nat : need.toNat = if skip_ot then 1 else 2 := by
        rw [hneed]; cases skip_ot <;> rfl
      have hneed_pos : 1 ≤ need.toNat := by rw [hneed_nat]; cases skip_ot <;> decide
      c0_hsplit
      · c0_hsteps; exact hQ (false, ()) s m rfl hlen ⟨rfl, hel, rfl, rfl⟩ hm
      · c0_hsplit
        · c0_hsteps; exact hQ (false, ()) s m rfl hlen ⟨rfl, hel, rfl, rfl⟩ hm
        · have hsub_eq : (BitVec.ofNat 64 c.extend_cap -
              BitVec.ofNat 64 s.scratch.extend_len).toNat =
              c.extend_cap - s.scratch.extend_len := by bv_omega
          have hfit : s.scratch.extend_len + need.toNat ≤ c.extend_cap := by
            have hle : need.toNat ≤ (BitVec.ofNat 64 c.extend_cap -
                BitVec.ofNat 64 s.scratch.extend_len).toNat := by c0_bound
            rw [hsub_eq] at hle; omega
          have hi0 : (BitVec.ofNat 64 s.scratch.extend_len).toNat <
              s.scratch.extend_stk.length := by
            rw [hesl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
          c0_hsteps_nogrp
          refine wp_join_state0 (α := List (BitVec 32))
            (fun ext1 m1 => ext1.length = c.extend_cap ∧
              (FullMem c { s with scratch := { s.scratch with extend_stk := ext1 } } ⋆ R) m1)
            ?_ ?_
          · rintro _ ext1 m1 ⟨hext1, hm1⟩
            have hadd_eq : (BitVec.ofNat 64 s.scratch.extend_len + need).toNat =
                s.scratch.extend_len + need.toNat := by
              rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
                Nat.mod_eq_of_lt (by omega)]
            c0_hsteps
            let s' : FullState :=
              { s with scratch := { s.scratch with
                extend_stk := ext1,
                extend_len := (BitVec.ofNat 64 s.scratch.extend_len + need).toNat } }
            exact hQ (true, ()) s' _ rfl
              (hlen.with_scratch { hlen.scratch_ok with extend_stk_len := hext1 })
              ⟨rfl, by dsimp only [s']; rw [hadd_eq]; exact hfit, rfl, rfl⟩
              (fullMem_cast hm rfl)
          · intro Jw hJw
            c0_hsplit
            · c0_hsteps
              exact hJw _ _ ⟨by simp [hesl], hm⟩
            · have hsf : skip_ot = false := by cases skip_ot <;> simp_all
              have hneed2 : need.toNat = 2 := by rw [hneed_nat, hsf]; rfl
              have h0_el : (BitVec.ofNat 64 s.scratch.extend_len).toNat =
                  s.scratch.extend_len := by
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
              have hi1 : (BitVec.ofNat 64 s.scratch.extend_len + 1#64).toNat <
                  (s.scratch.extend_stk.set (BitVec.ofNat 64 s.scratch.extend_len).toNat
                    ((blk_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32)).length := by
                rw [List.length_set, hesl, BitVec.toNat_add, h0_el,
                  show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
                omega
              c0_hsteps
              exact hJw _ _ ⟨by simp [hesl], hm⟩
    · intro Jn hJn
      c0_hsplit <;> (c0_hsteps; exact hJn _ (by simp_all))
  · intro Js hJs
    c0_hsplit
    · have hot_lt : (other &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars := by
        have h1 : ((other &&& 0x7FFFFFFF#32).setWidth 64).toNat <
            ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat := by c0_bound
        rw [bv_zext_toNat _ (by decide), hnlits] at h1; exact h1
      have hot_v : ((other &&& 0x7FFFFFFF#32).setWidth 64).toNat < s.core.vals.length := by
        rw [bv_zext_toNat _ (by decide), hv_len]; omega
      have hot_l : (((other &&& 0x7FFFFFFF#32) >>> 1#32).setWidth 64).toNat <
          s.core.lvl.length := by
        rw [bv_zext_toNat _ (by decide), bv32_shr1_toNat, hl_len]; omega
      c0_hsteps <;> exact hJs _ trivial
    · c0_hsteps; exact hJs false trivial

theorem full_extend_push_cl_wp (Γ : Env) :
    ∀ a m Q X, Spec.fullExtendPushClSpec a m Q X →
      Func.wp Γ full_extend_push_cl_body a m Q X := by
  rintro ⟨h, blk_lit, cref, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, hel⟩, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hlen hm hQ
  have haca : c.arena_cap < 2 * dimacsBound := c.harena
  have heca : c.extend_cap < dimacsBound := c.hext
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at haca heca hmx
  have harl := hlen.core_ok.arena_len_arr
  have hale := hlen.core_ok.arena_len_le
  have hcv_le := hlen.core_ok.cur_vars_le
  have hv_len := hlen.core_ok.vals_len
  have hl_len := hlen.core_ok.lvl_len
  have hesl := hlen.scratch_ok.extend_stk_len
  have h2bv : (2 : BitVec 64).toNat = 2 := rfl
  have h3bv : (3 : BitVec 64).toNat = 3 := rfl
  have h2cv : 2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 = 2 * s.core.cur_vars := by omega
  have hnlits :
      ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    have h1 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [ext_bv64_shl1_toNat (by omega), h1]
  unfold Func.wp full_extend_push_cl_body
  c0_hsplit
  · c0_hsteps; exact hQ (false, ()) s m rfl hlen ⟨rfl, hel, rfl, rfl⟩ hm
  · have hcr3 : cref.toNat + 3 ≤ s.core.arena_len := by bv_omega
    have hcr2_eq : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2 := by bv_omega
    have hcr2_mod : (cref.toNat + (2 : BitVec 64).toNat) % 2 ^ 64 = cref.toNat + 2 := by
      rw [h2bv, Nat.mod_eq_of_lt (by omega)]
    have hcr2_lt : (cref.setWidth 64 + 2#64).toNat < s.core.arena.length := by
      rw [hcr2_eq, harl]; omega
    let szBv : BitVec 32 := s.core.arena[cref.toNat + 2]'(by omega)
    let sz : Nat := szBv.toNat
    c0_hsplit
    · c0_hsteps; exact hQ (false, ()) s m rfl hlen ⟨rfl, hel, rfl, rfl⟩ hm
    · have hc3sz : cref.toNat + 3 + sz ≤ s.core.arena_len := by
        have h1 := hc
        simp only [hcr2_mod, h3bv] at h1
        have hsz32 := szBv.isLt
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
        change ¬ s.core.arena_len < cref.toNat + 3 + sz at h1
        omega
      let bl : BitVec 32 := blk_lit &&& 0x7FFFFFFF#32
      let cnt :=
        extKeepCount s.core.arena s.core.vals s.core.lvl cref.toNat (2 * s.core.cur_vars) bl
      c0_hsteps_nogrp
      refine wp_loop_inv
        (fun (keep, i, ()) m1 =>
          i.toNat ≤ sz ∧ keep.toNat = cnt i.toNat ∧ m1 = m)
        (fun (_, i, ()) _ => sz - i.toNat)
        (fun J1 hLoop1 => by
          c0_hsteps; exact hLoop1 (0#64, 0#32, ()) m ⟨Nat.zero_le _, rfl, rfl⟩)
        (fun J1 ⟨keep, i, ⟨⟩⟩ m1 ⟨hi_le, hkeep_eq, hm1⟩ hLoop1 => ?_)
      rcases hm1.symm with rfl
      c0_hsplit
      · have hi_lt : i.toNat < sz := by
          have h1 := hc; simp only [hcr2_mod] at h1; exact h1
        have hi1_eq : (i + 1#32).toNat = i.toNat + 1 := bv32_add1 (by omega)
        have hli_eq : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat =
            cref.toNat + 3 + i.toNat := by bv_omega
        have hli_mod : (cref.toNat + (3 : BitVec 64).toNat + i.toNat) % 2 ^ 64 =
            cref.toNat + 3 + i.toNat := by rw [h3bv, Nat.mod_eq_of_lt (by omega)]
        have hli_lt : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat < s.core.arena.length := by
          rw [hli_eq, harl]; omega
        let lit : BitVec 32 :=
          (s.core.arena[cref.toNat + 3 + i.toNat]'(by omega)) &&& 0x7FFFFFFF#32
        have hlit_ar :
            (s.core.arena[cref.toNat + 3 + i.toNat]?.getD 0#32) &&& 0x7FFFFFFF#32 = lit := by
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        have hkeep_ub : keep.toNat ≤ i.toNat := hkeep_eq ▸ extKeepCount_le ..
        have hkp1_eq : (keep + 1#64).toNat = keep.toNat + 1 := bv64_add1 (by omega)
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun k => (k, ()))
          (fun k => k.toNat = cnt (i.toNat + 1)) ?_ ?_
        · intro _ k hk
          c0_hsteps
          exact hLoop1 (k, i + 1#32, ()) m (by dsimp only; rw [hi1_eq]; omega)
            ⟨by rw [hi1_eq]; omega, by rw [hi1_eq]; exact hk, rfl⟩
        · intro Jk hJk
          c0_hsplit
          · have hne_bl : lit ≠ bl := by
              have h1 := hc; simp only [hli_mod] at h1; exact h1
            c0_hsteps_nogrp
            refine wp_join_state0 (α := Unit)
              (fun _ m' => m' = m ∧
                extLitKeep s.core.arena s.core.vals s.core.lvl cref.toNat
                  (2 * s.core.cur_vars) bl i.toNat = true) ?_ ?_
            · rintro _ ⟨⟩ m' ⟨rfl, htk⟩
              c0_hsteps
              exact hJk (keep + 1#64) (by
                dsimp only [cnt]; rw [extKeepCount_succ, htk, hkp1_eq, hkeep_eq]; rfl)
            · intro Js hJs
              c0_hsplit
              · have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by
                  have h1 := hc; simp only [hli_mod, h2cv] at h1; exact h1
                have hlit_lvl_bd : lit.toNat / 2 < s.core.lvl.length := by rw [hl_len]; omega
                have hlit_val_bd : lit.toNat < s.core.vals.length := by rw [hv_len]; omega
                have hlit_val_load :
                    (BitVec.setWidth 64
                      (s.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hli_lt &&&
                        0x7FFFFFFF#32)).toNat < s.core.vals.length := by
                  rw [bv_zext_toNat _ (by decide)]
                  simp only [hli_eq]; exact hlit_val_bd
                c0_hsplit
                · have hlvl0 : s.core.lvl[lit.toNat / 2]?.getD 0#32 = 0#32 := by
                    have h1 := hc; simp only [hli_mod] at h1
                    rw [List.getElem?_eq_getElem hlit_lvl_bd, Option.getD_some]; exact h1
                  c0_hsplit
                  · have hvf : ((s.core.vals[lit.toNat]?.getD 0#8).signExtend 32).slt 0#32 =
                        true := by
                      have h1 := hc; simp only [hli_mod] at h1
                      rw [List.getElem?_eq_getElem hlit_val_bd, Option.getD_some]; exact h1
                    have hfk := extLitKeep_eq_false_skip (bl := bl) hlit_ar hlit_lt hlvl0 hvf
                    c0_hsteps
                    exact hJk keep (by
                      dsimp only [cnt]; rw [extKeepCount_succ, hfk]; simpa using hkeep_eq)
                  · have hvnf : ((s.core.vals[lit.toNat]?.getD 0#8).signExtend 32).slt 0#32 ≠
                        true := by
                      have h1 := hc; simp only [hli_mod] at h1
                      rw [List.getElem?_eq_getElem hlit_val_bd, Option.getD_some]
                      intro ht; exact Bool.noConfusion (h1.symm.trans ht)
                    c0_hsteps
                    exact hJs () m
                      ⟨rfl, extLitKeep_eq_true hlit_ar hne_bl (fun ⟨_, _, hv⟩ => hvnf hv)⟩
                · have hlvlne : s.core.lvl[lit.toNat / 2]?.getD 0#32 ≠ 0#32 := by
                    have h1 := hc; simp only [hli_mod] at h1
                    rw [List.getElem?_eq_getElem hlit_lvl_bd, Option.getD_some]; exact h1
                  c0_hsteps
                  exact hJs () m
                    ⟨rfl, extLitKeep_eq_true hlit_ar hne_bl (fun ⟨_, h0, _⟩ => hlvlne h0)⟩
              · have hlit_ge : ¬ lit.toNat < 2 * s.core.cur_vars := by
                  have h1 := hc; simp only [hli_mod, h2cv] at h1; exact h1
                c0_hsteps
                exact hJs () m
                  ⟨rfl, extLitKeep_eq_true hlit_ar hne_bl (fun ⟨hlt, _, _⟩ => hlit_ge hlt)⟩
          · have heq_bl :
                (s.core.arena[cref.toNat + 3 + i.toNat]?.getD 0#32) &&& 0x7FFFFFFF#32 = bl := by
              rw [hlit_ar]; have h1 := hc; simp only [hli_mod] at h1; exact h1
            have hfk := extLitKeep_eq_false_bl (vals := s.core.vals) (lvl := s.core.lvl)
              (nlits := 2 * s.core.cur_vars) heq_bl
            c0_hsteps
            exact hJk keep (by
              dsimp only [cnt]; rw [extKeepCount_succ, hfk]; simpa using hkeep_eq)
      · have hi_eq : i.toNat = sz := by
          have h1 := hc; simp only [hcr2_mod] at h1; dsimp only [sz, szBv] at hi_le ⊢; omega
        rw [hi_eq] at hkeep_eq
        have hkeep_ub : keep.toNat ≤ sz := hkeep_eq ▸ extKeepCount_le ..
        have hneed_eq : (1#64 + keep).toNat = 1 + keep.toNat := by bv_omega
        clear hLoop1 J1
        c0_hsplit
        · c0_hsteps; exact hQ (false, ()) s m rfl hlen ⟨rfl, hel, rfl, rfl⟩ hm
        · c0_hsplit
          · c0_hsteps; exact hQ (false, ()) s m rfl hlen ⟨rfl, hel, rfl, rfl⟩ hm
          · have hsub_eq : (BitVec.ofNat 64 c.extend_cap -
                BitVec.ofNat 64 s.scratch.extend_len).toNat =
                c.extend_cap - s.scratch.extend_len := by bv_omega
            have hfit : s.scratch.extend_len + 1 + keep.toNat ≤ c.extend_cap := by
              have hle : (1#64 + keep).toNat ≤ (BitVec.ofNat 64 c.extend_cap -
                  BitVec.ofNat 64 s.scratch.extend_len).toNat := by c0_bound
              rw [hneed_eq, hsub_eq] at hle; omega
            have h0_el :
                (BitVec.ofNat 64 s.scratch.extend_len).toNat = s.scratch.extend_len := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
            have hp0_lt : (BitVec.ofNat 64 s.scratch.extend_len).toNat <
                s.scratch.extend_stk.length := by rw [hesl, h0_el]; omega
            c0_hsteps_nogrp
            refine wp_loop_inv
              (fun (i2, p, ()) m2 =>
                i2.toNat ≤ sz ∧ p.toNat = s.scratch.extend_len + 1 + cnt i2.toNat ∧
                ∃ ext2 : List (BitVec 32), ext2.length = c.extend_cap ∧
                  (FullMem c { s with scratch := { s.scratch with extend_stk := ext2 } } ⋆ R) m2)
              (fun (i2, _, ()) _ => sz - i2.toNat)
              (fun J2 hLoop2 => by
                c0_hsteps
                refine hLoop2 (0#32, BitVec.ofNat 64 s.scratch.extend_len + 1#64, ()) _
                  ⟨Nat.zero_le _, ?_, _, by simp [hesl], hm⟩
                have h032 : (0#32 : BitVec 32).toNat = 0 := rfl
                rw [h032]; dsimp only [cnt]; rw [extKeepCount_zero]
                rw [BitVec.toNat_add, h0_el, show (1#64 : BitVec 64).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt (by omega)])
              (fun J2 ⟨i2, p, ⟨⟩⟩ m2 ⟨hi2_le, hp_eq, ext2, hext2, hm2⟩ hLoop2 => ?_)
            c0_hsplit
            · have hi2_lt : i2.toNat < sz := by
                have h1 := hc; simp only [hcr2_mod] at h1; exact h1
              have hi2_1 : (i2 + 1#32).toNat = i2.toNat + 1 := bv32_add1 (by omega)
              have hli2_eq : (cref.setWidth 64 + 3#64 + i2.setWidth 64).toNat =
                  cref.toNat + 3 + i2.toNat := by bv_omega
              have hli2_mod : (cref.toNat + (3 : BitVec 64).toNat + i2.toNat) % 2 ^ 64 =
                  cref.toNat + 3 + i2.toNat := by rw [h3bv, Nat.mod_eq_of_lt (by omega)]
              have hli2_lt : (cref.setWidth 64 + 3#64 + i2.setWidth 64).toNat <
                  s.core.arena.length := by rw [hli2_eq, harl]; omega
              let lit2 : BitVec 32 :=
                (s.core.arena[cref.toNat + 3 + i2.toNat]'(by omega)) &&& 0x7FFFFFFF#32
              have hlit2_ar :
                  (s.core.arena[cref.toNat + 3 + i2.toNat]?.getD 0#32) &&& 0x7FFFFFFF#32 =
                  lit2 := by
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              have hcnt_le_keep : cnt (i2.toNat + 1) ≤ keep.toNat :=
                hkeep_eq ▸ extKeepCount_mono _ _ _ _ _ _ (by omega)
              c0_hsteps_nogrp
              refine wp_join_state1 (t := i64) (α := BitVec 64 × List (BitVec 32)) Prod.fst
                (fun ⟨p', ext'⟩ m' =>
                  p'.toNat = s.scratch.extend_len + 1 + cnt (i2.toNat + 1) ∧
                  ext'.length = c.extend_cap ∧
                  (FullMem c { s with scratch := { s.scratch with extend_stk := ext' } } ⋆ R) m')
                ?_ ?_
              · rintro _ ⟨p', ext'⟩ m' ⟨hp'eq, hext', hm'⟩
                c0_hsteps
                exact hLoop2 (i2 + 1#32, p', ()) m' (by dsimp only; rw [hi2_1]; omega)
                  ⟨by rw [hi2_1]; omega, by rw [hi2_1]; exact hp'eq, ext', hext', hm'⟩
              · intro Jw hJw
                c0_hsplit
                · have hne_bl : lit2 ≠ bl := by
                    have h1 := hc; simp only [hli2_mod] at h1; exact h1
                  c0_hsteps_nogrp
                  refine wp_join_state0 (α := Unit)
                    (fun _ m' => m' = m2 ∧
                      extLitKeep s.core.arena s.core.vals s.core.lvl cref.toNat
                        (2 * s.core.cur_vars) bl i2.toNat = true) ?_ ?_
                  · rintro _ ⟨⟩ m' ⟨rfl, htk⟩
                    have hstep : cnt (i2.toNat + 1) = cnt i2.toNat + 1 := by
                      dsimp only [cnt]; rw [extKeepCount_succ, htk]; rfl
                    have hp_lt : p.toNat < ext2.length := by rw [hext2]; omega
                    have hp1 : (p + 1#64).toNat =
                        s.scratch.extend_len + 1 + cnt (i2.toNat + 1) := by
                      rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
                        Nat.mod_eq_of_lt (by omega), hp_eq, hstep]; omega
                    c0_hsteps
                    exact hJw (p + 1#64, _) _ ⟨hp1, by simp [hext2], hm⟩
                  · intro Js hJs
                    c0_hsplit
                    · have hlit_lt : lit2.toNat < 2 * s.core.cur_vars := by
                        have h1 := hc; simp only [hli2_mod, h2cv] at h1; exact h1
                      have hlit_lvl_bd : lit2.toNat / 2 < s.core.lvl.length := by
                        rw [hl_len]; omega
                      have hlit_val_bd : lit2.toNat < s.core.vals.length := by
                        rw [hv_len]; omega
                      have hlit_val_load :
                          (BitVec.setWidth 64
                            (s.core.arena[(cref.setWidth 64 + 3#64 +
                              i2.setWidth 64).toNat]'hli2_lt &&&
                              0x7FFFFFFF#32)).toNat < s.core.vals.length := by
                        rw [bv_zext_toNat _ (by decide)]
                        simp only [hli2_eq]; exact hlit_val_bd
                      c0_hsplit
                      · have hlvl0 : s.core.lvl[lit2.toNat / 2]?.getD 0#32 = 0#32 := by
                          have h1 := hc; simp only [hli2_mod] at h1
                          rw [List.getElem?_eq_getElem hlit_lvl_bd, Option.getD_some]; exact h1
                        c0_hsplit
                        · have hvf : ((s.core.vals[lit2.toNat]?.getD 0#8).signExtend 32).slt
                              0#32 = true := by
                            have h1 := hc; simp only [hli2_mod] at h1
                            rw [List.getElem?_eq_getElem hlit_val_bd, Option.getD_some]; exact h1
                          have hfk := extLitKeep_eq_false_skip (bl := bl) hlit2_ar hlit_lt hlvl0 hvf
                          c0_hsteps
                          exact hJw (p, ext2) m2
                            ⟨by dsimp only [cnt]; rw [extKeepCount_succ, hfk]; simpa using hp_eq,
                             hext2, hm2⟩
                        · have hvnf : ((s.core.vals[lit2.toNat]?.getD 0#8).signExtend 32).slt
                              0#32 ≠ true := by
                            have h1 := hc; simp only [hli2_mod] at h1
                            rw [List.getElem?_eq_getElem hlit_val_bd, Option.getD_some]
                            intro ht; exact Bool.noConfusion (h1.symm.trans ht)
                          c0_hsteps
                          exact hJs () m2 ⟨rfl, extLitKeep_eq_true hlit2_ar hne_bl
                            (fun ⟨_, _, hv⟩ => hvnf hv)⟩
                      · have hlvlne : s.core.lvl[lit2.toNat / 2]?.getD 0#32 ≠ 0#32 := by
                          have h1 := hc; simp only [hli2_mod] at h1
                          rw [List.getElem?_eq_getElem hlit_lvl_bd, Option.getD_some]; exact h1
                        c0_hsteps
                        exact hJs () m2 ⟨rfl, extLitKeep_eq_true hlit2_ar hne_bl
                          (fun ⟨_, h0, _⟩ => hlvlne h0)⟩
                    · have hlit_ge : ¬ lit2.toNat < 2 * s.core.cur_vars := by
                        have h1 := hc; simp only [hli2_mod, h2cv] at h1; exact h1
                      c0_hsteps
                      exact hJs () m2 ⟨rfl, extLitKeep_eq_true hlit2_ar hne_bl
                        (fun ⟨hlt, _, _⟩ => hlit_ge hlt)⟩
                · have heq_bl :
                      (s.core.arena[cref.toNat + 3 + i2.toNat]?.getD 0#32) &&& 0x7FFFFFFF#32 =
                      bl := by
                    rw [hlit2_ar]; have h1 := hc; simp only [hli2_mod] at h1; exact h1
                  have hfk := extLitKeep_eq_false_bl (vals := s.core.vals) (lvl := s.core.lvl)
                    (nlits := 2 * s.core.cur_vars) heq_bl
                  c0_hsteps
                  exact hJw (p, ext2) m2
                    ⟨by dsimp only [cnt]; rw [extKeepCount_succ, hfk]; simpa using hp_eq,
                     hext2, hm2⟩
            · have hi2_eq : i2.toNat = sz := by
                have h1 := hc; simp only [hcr2_mod] at h1
                dsimp only [sz, szBv] at hi2_le ⊢; omega
              rw [hi2_eq, ← hkeep_eq] at hp_eq
              c0_hsteps
              let s' : FullState :=
                { s with scratch := { s.scratch with extend_stk := ext2, extend_len := p.toNat } }
              exact hQ (true, ()) s' _ rfl
                (hlen.with_scratch { hlen.scratch_ok with extend_stk_len := hext2 })
                ⟨rfl, by dsimp only [s']; omega, rfl, rfl⟩
                (fullMem_cast hm rfl)

end

end LeanQbe.T.Examples.Kissat.Proof.Extend
