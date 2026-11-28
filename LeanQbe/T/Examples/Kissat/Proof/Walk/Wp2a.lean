/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Walk.Helpers
public import LeanQbe.T.Examples.Kissat.Proof.Walk.Spec
public import LeanQbe.T.Examples.Kissat.Src.Walk

import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Walk WP Proofs — Part 2a (`Proof.Walk.Wp2a`)

Proves canonical WP correctness for literal selection:
1. `full_walk_pick_m7_wp` (`fullWalkPickM7Spec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Walk

open Kraken.Bedrock2.Test
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Walk
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
open LeanQbe.T.Examples.Kissat.Proof.Walk.Spec

open scoped FullArenaTactics WalkMemTactics

/-! ## Shared Helpers -/

private theorem walk2_lengthsOk_set_sb {c : FullCfg} {s : FullState} {k : Nat} {v : BitVec 32}
    (hlen : FullState.LengthsOk c s) :
    FullState.LengthsOk c
      { s with scratch := { s.scratch with scratch_buf := s.scratch.scratch_buf.set k v } } :=
  ⟨hlen.core_ok, { hlen.scratch_ok with
    scratch_buf_len := by simp [hlen.scratch_ok.scratch_buf_len] }⟩

private theorem walk2_lengthsOk_set_sb2 {c : FullCfg} {s : FullState} {k1 k2 : Nat}
    {v1 v2 : BitVec 32} (hlen : FullState.LengthsOk c s) :
    FullState.LengthsOk c
      { s with scratch := { s.scratch with
        scratch_buf := (s.scratch.scratch_buf.set k1 v1).set k2 v2 } } :=
  ⟨hlen.core_ok, { hlen.scratch_ok with
    scratch_buf_len := by simp [hlen.scratch_ok.scratch_buf_len] }⟩

private theorem walk2_lengthsOk_set_wks {c : FullCfg} {s : FullState} {k1 k2 k3 : Nat}
    {w1 w2 w3 : BitVec 32} (hlen : FullState.LengthsOk c s) :
    FullState.LengthsOk c
      { s with scratch := { s.scratch with
        work_stk1 := s.scratch.work_stk1.set k1 w1
        work_stk2 := (s.scratch.work_stk2.set k2 w2).set k3 w3 } } :=
  ⟨hlen.core_ok, { hlen.scratch_ok with
    work_stk1_len := by simp [hlen.scratch_ok.work_stk1_len]
    work_stk2_len := by simp [hlen.scratch_ok.work_stk2_len] }⟩

private theorem walk2_lengthsOk_set_wv2 {c : FullCfg} {s : FullState} {k1 k2 : Nat}
    {v1 v2 : BitVec 8} (hlen : FullState.LengthsOk c s) :
    FullState.LengthsOk c
      { s with scratch := { s.scratch with
        walk_vals := (s.scratch.walk_vals.set k1 v1).set k2 v2 } } :=
  ⟨hlen.core_ok, { hlen.scratch_ok with
    walk_vals_len := by simp [hlen.scratch_ok.walk_vals_len] }⟩

private theorem walkTblExpsOk_imm1080 {s : FullState} (hok : WalkTblExpsOk s)
    {d : BitVec 64} (hd : d.toNat / 4 = 2160)
    {hi_len : d.toNat / 4 + 1 < s.scratch.scratch_buf.length} :
    (pack64 s.scratch.scratch_buf[d.toNat / 4]
      s.scratch.scratch_buf[d.toNat / 4 + 1]).toNat ≤ 1080 := by
  simp only [hd]
  exact walkTblExpsOk_to_lt1080 hok (hi_len := by omega)

private theorem walkTblExpsOk_store_imm {s : FullState} {d v : BitVec 64}
    (hne : d.toNat / 4 ≠ 2160 ∧ d.toNat / 4 ≠ 2161 ∧
      d.toNat / 4 + 1 ≠ 2160 ∧ d.toNat / 4 + 1 ≠ 2161)
    (hok : WalkTblExpsOk s) :
    WalkTblExpsOk { s with scratch := { s.scratch with
      scratch_buf := (s.scratch.scratch_buf.set (d.toNat / 4) (v.setWidth 32)).set
        (d.toNat / 4 + 1) ((v >>> 32).setWidth 32) } } := by
  unfold WalkTblExpsOk at hok ⊢
  rcases hne with ⟨h0, h1, h2, h3⟩
  rw [List.getElem?_set_ne h2, List.getElem?_set_ne h0,
    List.getElem?_set_ne h3, List.getElem?_set_ne h1]
  exact hok

private theorem walkScrPrefixPres_set_ge2 {s : FullState} {k1 k2 : Nat}
    {v1 v2 : BitVec 32} (hk1 : 2200 ≤ k1) (hk2 : 2200 ≤ k2) :
    WalkScrPrefixPres s
      { s with scratch := { s.scratch with
        scratch_buf := (s.scratch.scratch_buf.set k1 v1).set k2 v2 } } :=
  fun j hj => by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]

private theorem walk2_rem_eq {scap : Nat} {ncl : BitVec 64}
    (hsc : scap < 2 ^ 28) (h5 : 2200 + 5 * ncl.toNat ≤ scap) :
    (BitVec.ofNat 64 scap - (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl)).toNat =
      scap - (2200 + 5 * ncl.toNat) := by
  have h1 := bv64_shl1_toNat_lt (x := ncl) (by omega)
  bv_omega

private theorem walk2_sat_idx {ncl x : BitVec 64} (hn : 2200 + 2 * ncl.toNat + x.toNat < 2 ^ 64) :
    ((2200#64 + (ncl <<< (1 : Nat))) + x).toNat = 2200 + 2 * ncl.toNat + x.toNat := by
  have h1 := bv64_shl1_toNat_lt (x := ncl) (by omega); bv_omega

private theorem walk2_upos_idx {ncl x : BitVec 64}
    (hn : 2200 + 3 * ncl.toNat + x.toNat < 2 ^ 64) :
    ((2200#64 + (ncl <<< (1 : Nat)) + ncl) + x).toNat = 2200 + 3 * ncl.toNat + x.toNat := by
  have h1 := bv64_shl1_toNat_lt (x := ncl) (by omega); bv_omega

private theorem walk2_uns_idx {ncl x : BitVec 64}
    (hn : 2200 + 4 * ncl.toNat + x.toNat < 2 ^ 64) :
    ((2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl) + x).toNat = 2200 + 4 * ncl.toNat + x.toNat := by
  have h1 := bv64_shl1_toNat_lt (x := ncl) (by omega); bv_omega

private theorem walk2_uns_sub1_idx {ncl cu : BitVec 64}
    (hn : 2200 + 4 * ncl.toNat + cu.toNat < 2 ^ 64) (hcu : 1 ≤ cu.toNat) :
    ((2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl) + cu - 1#64).toNat =
      2200 + 4 * ncl.toNat + cu.toNat - 1 := by
  have h1 := bv64_shl1_toNat_lt (x := ncl) (by omega); bv_omega

private theorem walk2_lim_avail {scap : Nat} {ncl : BitVec 64} {mark : BitVec 32}
    (hsc : scap < 2 ^ 28) (h5 : 2200 + 5 * ncl.toNat ≤ scap)
    (hm : mark.toNat ≤
      (BitVec.ofNat 64 scap - (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl)).toNat) :
    mark.toNat +
      ((BitVec.ofNat 64 scap - (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl)) -
        mark.setWidth 64).toNat ≤ scap - (2200 + 5 * ncl.toNat) := by
  have hrem := walk2_rem_eq hsc h5
  have hz := bv32_lit_toNat_mod64 mark
  bv_omega

private theorem walk2_lim_trc {scap : Nat} {ncl : BitVec 64} {mark trc : BitVec 32}
    (hsc : scap < 2 ^ 28) (h5 : 2200 + 5 * ncl.toNat ≤ scap)
    (hm : mark.toNat ≤
      (BitVec.ofNat 64 scap - (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl)).toNat)
    (ht : ¬ ((BitVec.ofNat 64 scap - (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl)) -
        mark.setWidth 64).toNat < trc.toNat) :
    mark.toNat + trc.toNat ≤ scap - (2200 + 5 * ncl.toNat) := by
  have hrem := walk2_rem_eq hsc h5
  have hz1 := bv32_lit_toNat_mod64 mark
  have hz2 := bv32_lit_toNat_mod64 trc
  bv_omega

private theorem walk2_lim_avail_exp {scap : Nat} {ncl : BitVec 64} {mark : BitVec 32}
    (hsc : scap < 2 ^ 28) (h5 : 2200 + 5 * ncl.toNat ≤ scap)
    (hm : mark.toNat ≤ (2 ^ 64 - (BitVec.toNat (2200#64) + 2 * ncl.toNat + ncl.toNat +
        ncl.toNat + ncl.toNat) % 2 ^ 64 + scap) % 2 ^ 64) :
    mark.toNat +
      ((BitVec.ofNat 64 scap - (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl)) -
        mark.setWidth 64).toNat ≤ scap - (2200 + 5 * ncl.toNat) := by
  have h2200 : BitVec.toNat (2200#64) = 2200 := rfl
  rw [h2200] at hm
  have hrem := walk2_rem_eq hsc h5
  have hm' : mark.toNat ≤ scap - (2200 + 5 * ncl.toNat) := by omega
  have hz := bv32_lit_toNat_mod64 mark
  bv_omega

private theorem walk2_lim_trc_exp {scap : Nat} {ncl : BitVec 64} {mark : BitVec 32}
    {trc : Nat} (_hsc : scap < 2 ^ 28) (h5 : 2200 + 5 * ncl.toNat ≤ scap)
    (hm : mark.toNat ≤ (2 ^ 64 - (BitVec.toNat (2200#64) + 2 * ncl.toNat + ncl.toNat +
        ncl.toNat + ncl.toNat) % 2 ^ 64 + scap) % 2 ^ 64)
    (ht : ¬ (2 ^ 64 - mark.toNat + (2 ^ 64 - (BitVec.toNat (2200#64) + 2 * ncl.toNat +
        ncl.toNat + ncl.toNat + ncl.toNat) % 2 ^ 64 + scap)) % 2 ^ 64 < trc) :
    mark.toNat + trc ≤ scap - (2200 + 5 * ncl.toNat) := by
  have h2200 : BitVec.toNat (2200#64) = 2200 := rfl
  rw [h2200] at hm ht
  have hm' : mark.toNat ≤ scap - (2200 + 5 * ncl.toNat) := by omega
  omega

private theorem bv32_xor1_toNat (x : BitVec 32) : x.toNat ^^^ 1 = (x ^^^ 1#32).toNat := by
  rw [BitVec.toNat_xor]; rfl

private theorem bv32_mask_lt (w : BitVec 32) : (w &&& 0x7FFFFFFF#32).toNat < 2 ^ 31 := by
  have h : (w &&& 0x7FFFFFFF#32).toNat ≤ (0x7FFFFFFF#32 : BitVec 32).toNat := by
    rw [BitVec.toNat_and]; exact Nat.and_le_right
  have h1 : (0x7FFFFFFF#32 : BitVec 32).toNat = 2147483647 := rfl
  omega

private theorem wp_join_here {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {P : Tup Val ts → Prop}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (hb : ∀ (J : Cont ts) (xs : Tup Val ts), P xs → wp Γ Q X ((bodies (J, ())).get .here xs) m)
    (he : ∀ (J : Cont ts), (∀ xs, P xs → J xs m) → wp Γ Q X (entry (J, ())) m) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_join_group (fun xs m' => m = m' ∧ P xs)
    (fun J xs _ ⟨rfl, hp⟩ => hb J xs hp)
    (fun J hJ => he J fun xs hp => hJ xs m ⟨rfl, hp⟩)

private theorem wp_join_mem {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (hb : ∀ (J : Cont ts) (xs : Tup Val ts), wp Γ Q X ((bodies (J, ())).get .here xs) m)
    (he : ∀ (J : Cont ts), (∀ xs, J xs m) → wp Γ Q X (entry (J, ())) m) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_join_here (P := fun _ => True) (fun J xs _ => hb J xs)
    (fun J h => he J fun xs => h xs trivial)

private theorem wp_loop_mem {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} (inv : Tup Val ts → Prop) (meas : Tup Val ts → Nat)
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (hE : ∀ (J : Cont ts), (∀ xs, inv xs → J xs m) → wp Γ Q X (entry (J, ())) m)
    (hB : ∀ (J : Cont ts) xs, inv xs →
        (∀ ys, meas ys < meas xs → inv ys → J ys m) →
        wp Γ Q X ((bodies (J, ())).get .here xs) m) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_loop_group (fun n xs m' => m = m' ∧ inv xs ∧ meas xs ≤ n)
    (fun J _ xs _ hJ ⟨rfl, hi, hn⟩ => hB J xs hi fun ys hm hy =>
      hJ (meas ys) ys m (Nat.lt_of_lt_of_le hm hn) ⟨rfl, hy, Nat.le_refl _⟩)
    (fun J hJ => hE J fun xs hi => hJ (meas xs) xs m ⟨rfl, hi, Nat.le_refl _⟩)

private theorem wp_loop_slice_hm {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {R : Mem 64 → Prop} {s : FullState} {m : Mem 64}
    (_hm : (FullMem c s ⋆ R) m) (_hlen : s.LengthsOk c)
    (inv : FullState → Tup Val ts → Prop) (meas : Tup Val ts → Nat)
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (hE : ∀ (J : Cont ts),
        (∀ s' xs m', ((FullMem c s' ⋆ R) m') → PreservesCoreSlice FullState.core s s' →
          s'.LengthsOk c → inv s' xs → J xs m') → wp Γ Q X (entry (J, ())) m)
    (hB : ∀ (J : Cont ts) s' xs m', PreservesCoreSlice FullState.core s s' → s'.LengthsOk c →
        inv s' xs → (FullMem c s' ⋆ R) m' →
        (∀ s'' ys ml', (FullMem c s'' ⋆ R) ml' → meas ys < meas xs →
          PreservesCoreSlice FullState.core s' s'' → s''.LengthsOk c → inv s'' ys →
          J ys ml') →
        wp Γ Q X ((bodies (J, ())).get .here xs) m') :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_loop_safety_slice (fullSafetySlice c) s R (fun _ => True) trivial inv meas
    (fun J hJ => hE J fun s' xs m' hm' hc hs hi => hJ s' xs m' hm' hc hs hi)
    (fun J s' xs m' hc hs _ hi hm' hJ => hB J s' xs m' hc hs hi hm' hJ)

private theorem bv64_pack_low32_and {hi lo : BitVec 64} {n : Nat}
    (hlo : lo.toNat ≤ n) (hn : n < 2 ^ 32) :
    (((hi <<< (32 : Nat)) ||| (lo &&& 0xFFFFFFFF#64)) &&& 0xFFFFFFFF#64).toNat ≤ n := by
  have hlt : lo.toNat < 2 ^ 32 := by omega
  have heq : ((hi <<< (32 : Nat)) ||| (lo &&& 0xFFFFFFFF#64)) &&& 0xFFFFFFFF#64 = lo := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi_lt
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
    by_cases h32 : i < 32
    · have h1 : (0xFFFFFFFF#64 : BitVec 64).getLsbD i = true := by
        rw [BitVec.getLsbD_ofNat, show (4294967295 : Nat) = 2 ^ 32 - 1 from rfl,
          Nat.testBit_two_pow_sub_one]; simp [hi_lt, h32]
      have h2 : ¬ (32 ≤ i) := by omega
      simp [h1, h2]
    · have h1 : (0xFFFFFFFF#64 : BitVec 64).getLsbD i = false := by
        rw [BitVec.getLsbD_ofNat, show (4294967295 : Nat) = 2 ^ 32 - 1 from rfl,
          Nat.testBit_two_pow_sub_one]; simp [hi_lt, h32]
      have h2 : lo.getLsbD i = false := by
        rw [BitVec.getLsbD_eq_getElem, BitVec.getElem_eq_testBit_toNat]
        · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega)
            (by omega)))
        · exact hi_lt
      simp [h1, h2]
  rw [heq]; exact hlo

private theorem walk_call_break_m7 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {args : Tup (Arg Val) [i64, i32, i64]} {k : Tup Val [i32] → Expr Val Cont rs}
    (hBrk : Γ.Has "full_walk_break_m7" fullWalkBreakM7Spec)
    {c : FullCfg} {s : FullState} {nl : BitVec 32} {ncl : BitVec 64} {R : Mem 64 → Prop}
    (hargs : vals args = (c.hdr, nl, ncl, ())) (hlen : s.LengthsOk c)
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (brk : BitVec 32) (m' : Mem 64),
      (FullMem c s ⋆ R) m' → wp Γ Q X (k (brk, ())) m') :
    wp Γ Q X (.call "full_walk_break_m7" args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  refine hBrk _ _ _ _ ⟨c, s, R, rfl, hlen, hm, ?_⟩
  rintro ⟨brk, ⟨⟩⟩ s' m' _ _ heq hm'
  subst s'; exact hk brk m' hm'

private theorem walkTblExpsOk_of_sb_eq {s1 s2 : FullState}
    (h : s1.scratch.scratch_buf = s2.scratch.scratch_buf) (hx : WalkTblExpsOk s1) :
    WalkTblExpsOk s2 := by
  simp only [WalkTblExpsOk, ← h]; exact hx

private theorem walk_pick_arena_lit_lt {ar : List (BitVec 32)} {w0 j : BitVec 32} {cv : Nat}
    (hcv : cv < 2 ^ 63) (har : (w0.setWidth 64 + 3#64 + j.setWidth 64).toNat < ar.length)
    (h1 : (ar[(w0.toNat + 3 + j.toNat) % 2 ^ 64]'(by
      have hz1 := bv32_lit_toNat_mod64 w0; have hz2 := bv32_lit_toNat_mod64 j
      have heq : (w0.setWidth 64 + 3#64 + j.setWidth 64).toNat =
          (w0.toNat + 3 + j.toNat) % 2 ^ 64 := by
        rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, hz1, hz2]; omega
      exact heq ▸ har)).toNat < 2 * (cv % 2 ^ 64) % 2 ^ 64) :
    (ar[(w0.setWidth 64 + 3#64 + j.setWidth 64).toNat]'har).toNat < 2 * cv := by
  have hz1 := bv32_lit_toNat_mod64 w0; have hz2 := bv32_lit_toNat_mod64 j
  have heq : (w0.setWidth 64 + 3#64 + j.setWidth 64).toNat = (w0.toNat + 3 + j.toNat) % 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, hz1, hz2]; omega
  simp only [heq]; omega

/-! ## 1. `full_walk_pick_m7` -/

theorem full_walk_pick_m7_wp (Γ : Env)
    (hAdd : Γ.Has "f64u_add" f64uPure2Spec)
    (hMul : Γ.Has "f64u_mul" f64uPure2Spec)
    (hFrom : Γ.Has "f64u_from_u64" f64uPure1Spec)
    (hBrk : Γ.Has "full_walk_break_m7" fullWalkBreakM7Spec) :
    ∀ a m Q X, fullWalkPickM7Spec a m Q X →
      Func.wp Γ full_walk_pick_m7_body a m Q X := by
  rintro ⟨h, cl_id, ncl, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, hexps⟩, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  have hmaxv := c.hmaxv; have hscr := c.hscr; have har := c.harena
  unfold dimacsBound at hmaxv hscr har
  unfold Func.wp full_walk_pick_m7_body
  c0_hfast_nogrp_nobound
  iterate 6 (exact hQ (0xFFFFFFFF#64, ()) s m rfl hlen ⟨⟨rfl, rfl⟩, hexps⟩ hm)
  · have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
    have hcv_pos : 0 < s.core.cur_vars := Nat.pos_of_ne_zero fun h0 =>
      (by assumption : BitVec.ofNat 64 s.core.cur_vars ≠ 0#64) (by simp [h0])
    have hncl_pos : 0 < ncl.toNat := Nat.pos_of_ne_zero fun h0 =>
      (by assumption : ncl ≠ 0#64) (BitVec.eq_of_toNat_eq (by simp [h0]))
    have hcl_lt : cl_id.toNat < ncl.toNat := Nat.lt_of_not_ge (by assumption)
    have hncl_le : ncl.toNat ≤ c.scratch_cap := by
      have : ¬ c.scratch_cap % 2 ^ 64 < ncl.toNat := by assumption
      omega
    have h5ncl : 2200 + 5 * ncl.toNat ≤ c.scratch_cap := by
      have hc : ¬ c.scratch_cap % 2 ^ 64 < (BitVec.toNat (2200 : BitVec 64) +
          BitVec.toNat (5 : BitVec 64) * ncl.toNat) % 2 ^ 64 := by assumption
      change ¬ _ < (2200 + 5 * ncl.toNat) % 2 ^ 64 at hc; omega
    have hsb_len := hlen.scratch_ok.scratch_buf_len; have hval_len := hlen.core_ok.vals_len
    have har_len := hlen.core_ok.arena_len_arr; have htrc_len := hlen.scratch_ok.tarjan_reach_len
    have hwk1_len := hlen.scratch_ok.work_stk1_len; have hwk2_len := hlen.scratch_ok.work_stk2_len
    have h2v : ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
      have hlt : 2 * (BitVec.ofNat 64 s.core.cur_vars).toNat < 2 ^ 64 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      rw [bv64_shl1_toNat_lt hlt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have h2161 : (1080#64 * 8#64 : BitVec 64).toNat / 4 + 1 < s.scratch.scratch_buf.length := by
      rw [hsb_len, show (1080#64 * 8#64 : BitVec 64).toNat = 8640 from rfl]; omega
    have h2163 : (1081#64 * 8#64 : BitVec 64).toNat / 4 + 1 < s.scratch.scratch_buf.length := by
      rw [hsb_len, show (1081#64 * 8#64 : BitVec 64).toNat = 8648 from rfl]; omega
    have hcl_shl := bv64_shl1_toNat_lt (x := cl_id.setWidth 64)
      (by rw [bv32_lit_toNat_mod64]; omega)
    have hi0 : (2200#64 + (cl_id.setWidth 64 <<< (1 : Nat))).toNat =
        (2200 + 2 * cl_id.toNat) % 2 ^ 64 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, hcl_shl, bv32_lit_toNat_mod64 cl_id]
    have hw0_lt : (2200#64 + (cl_id.setWidth 64 <<< (1 : Nat))).toNat <
        s.scratch.scratch_buf.length := by rw [hsb_len, hi0]; omega
    have hw0_lt' : (2200 + 2 * cl_id.toNat) % 2 ^ 64 < s.scratch.scratch_buf.length :=
      hi0 ▸ hw0_lt
    have hi1 : (2200#64 + (cl_id.setWidth 64 <<< (1 : Nat)) + 1#64).toNat =
        (2200 + 2 * cl_id.toNat + 1) % 2 ^ 64 := by
      have hz := bv32_lit_toNat_mod64 cl_id
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hcl_shl, hz]
      omega
    have hw1_lt : (2200#64 + (cl_id.setWidth 64 <<< (1 : Nat)) + 1#64).toNat <
        s.scratch.scratch_buf.length := by rw [hsb_len, hi1]; omega
    have hw1_lt' : (2200 + 2 * cl_id.toNat + 1) % 2 ^ 64 < s.scratch.scratch_buf.length :=
      hi1 ▸ hw1_lt
    let exps := pack64 s.scratch.scratch_buf[(1080#64 * 8#64 : BitVec 64).toNat / 4]
      s.scratch.scratch_buf[(1080#64 * 8#64 : BitVec 64).toNat / 4 + 1]
    have hexps_le : exps.toNat ≤ 1080 := walkTblExpsOk_imm1080 hexps (by decide) (hi_len := h2161)
    let w0 := s.scratch.scratch_buf[(2200#64 + (cl_id.setWidth 64 <<< (1 : Nat))).toNat]'hw0_lt
    let w1 := s.scratch.scratch_buf[(2200#64 +
      (cl_id.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'hw1_lt
    c0_hfast_nogrp_nobound
    · let l0 := w0 &&& 0x7FFFFFFF#32
      let l1 := w1
      refine wp_join_group (ts := [.bool]) (fun (ok0, ()) m0 =>
          m = m0 ∧ (ok0 = true → l0.toNat < 2 * s.core.cur_vars)) ?_ ?_
      · rintro Jok0 ⟨ok0, ⟨⟩⟩ _ ⟨rfl, hok0⟩; rw [Blocks.get_here]
        refine wp_join_group (ts := [.bool]) (fun (ok1, ()) m0 =>
            m = m0 ∧ (ok1 = true → l1.toNat < 2 * s.core.cur_vars)) ?_ ?_
        · rintro Jok1 ⟨ok1, ⟨⟩⟩ _ ⟨rfl, hok1⟩; rw [Blocks.get_here]
          refine wp_join_here (ts := []) (P := fun _ => ok0 = true ∨ ok1 = true) ?_ ?_
          · rintro J1 ⟨⟩ h1; rw [Blocks.get_here]
            refine wp_join_here (ts := []) (P := fun _ => ok1 = true) ?_ ?_
            · rintro J2 ⟨⟩ hl1_t; rw [Blocks.get_here]
              refine wp_join_here (ts := []) (P := fun _ => ok0 = true ∧ ok1 = true) ?_ ?_
              · rintro J3 ⟨⟩ ⟨hl0_t, _⟩; rw [Blocks.get_here]
                have hl0_lt : l0.toNat < 2 * s.core.cur_vars := hok0 hl0_t
                have hl1_lt : l1.toNat < 2 * s.core.cur_vars := hok1 hl1_t
                c0_hfast_nogrp_nobound
                refine walk_call_break_m7 hBrk rfl hlen hm fun b0 m1 hm1 => ?_
                c0_hfast_nogrp_nobound
                refine walk_call_break_m7 hBrk rfl hlen hm1 fun b1 m2 hm2 => ?_
                refine wp_join_group (ts := [i64]) (fun _ m3 => m2 = m3) ?_ ?_
                · rintro Js0 ⟨s0, ⟨⟩⟩ _ rfl; rw [Blocks.get_here]
                  refine wp_join_group (ts := [i64]) (fun _ m3 => m2 = m3) ?_ ?_
                  · rintro Js1 ⟨s1, ⟨⟩⟩ _ rfl; rw [Blocks.get_here]
                    c0_hfast_nogrp_nobound
                    refine wp_call_of_spec _ _ (hAdd _ _ _ _ fun sum => ?_)
                    have h2165 : (1082#64 * 8#64 : BitVec 64).toNat / 4 + 1 <
                        s.scratch.scratch_buf.length := by
                      rw [hsb_len, show (1082#64 * 8#64 : BitVec 64).toNat = 8656 from rfl]; omega
                    c0_hfast_nogrp_nobound
                    refine wp_join_mem (ts := [i64]) ?_ ?_
                    · rintro Jrnd ⟨rnd, ⟨⟩⟩; rw [Blocks.get_here]
                      c0_hfast_nogrp_nobound
                      refine wp_call_of_spec _ _ (hMul _ _ _ _ fun thr => ?_)
                      have hn0 : (l0 ^^^ 1#32).toNat < s.scratch.tarjan_reach.length := by
                        rw [htrc_len]
                        exact Nat.lt_of_lt_of_le (bv32_lit_neg_lt hl0_lt) (by omega)
                      have hn1 : (l1 ^^^ 1#32).toNat < s.scratch.tarjan_reach.length := by
                        rw [htrc_len]
                        exact Nat.lt_of_lt_of_le (bv32_lit_neg_lt hl1_lt) (by omega)
                      c0_hfast_nogrp_nobound
                      refine wp_join_mem (ts := [i64]) ?_ ?_
                      · rintro Jps ⟨ps, ⟨⟩⟩; rw [Blocks.get_here]
                        refine wp_join_mem (ts := [i32]) ?_ ?_
                        · rintro Jch ⟨ch, ⟨⟩⟩; rw [Blocks.get_here]
                          c0_hfast_nogrp_nobound
                          refine hQ _ _ _ ?_ ?_ ?_ hm
                          · rfl
                          · exact walk2_lengthsOk_set_sb2 hlen
                          · exact ⟨⟨rfl, rfl⟩,
                              walkTblExpsOk_store_ne1080 _ (Or.inr (by decide)) hexps⟩
                        · intro Jch hJch; c0_hfast_nogrp_nobound <;> exact hJch _
                      · intro Jps hJps; c0_hfast_nogrp_nobound <;> exact hJps _
                    · intro Jrnd hJrnd; c0_hfast_nogrp_nobound
                      · exact hJrnd _
                      · refine wp_call_of_spec _ _ (hFrom _ _ _ _ fun fv => ?_)
                        c0_hfast_nogrp_nobound; exact hJrnd _
                  · intro Js1 hJs1; c0_hfast_nogrp_nobound
                    · have hb1 : 2 * b1.toNat + 1 < s.scratch.scratch_buf.length := by
                        have hlt : b1.toNat < exps.toNat := by assumption
                        rw [hsb_len]; omega
                      have hb1' : (b1.setWidth 64 * 8#64).toNat / 4 + 1 <
                          s.scratch.scratch_buf.length := by
                        have hz := bv32_lit_toNat_mod64 b1
                        rw [BitVec.toNat_mul, BitVec.toNat_ofNat, hz, Nat.mod_eq_of_lt (by omega)]
                        omega
                      c0_hfast_nobound; exact hJs1 _ m2 rfl
                    · exact hJs1 _ m2 rfl
                · intro Js0 hJs0; c0_hfast_nogrp_nobound
                  · have hb0 : 2 * b0.toNat + 1 < s.scratch.scratch_buf.length := by
                      have hlt : b0.toNat < exps.toNat := by assumption
                      rw [hsb_len]; omega
                    have hb0' : (b0.setWidth 64 * 8#64).toNat / 4 + 1 <
                        s.scratch.scratch_buf.length := by
                      have hz := bv32_lit_toNat_mod64 b0
                      rw [BitVec.toNat_mul, BitVec.toNat_ofNat, hz, Nat.mod_eq_of_lt (by omega)]
                      omega
                    c0_hfast_nobound; exact hJs0 _ m2 rfl
                  · exact hJs0 _ m2 rfl
              · intro J3 hJ3; c0_hfast_nogrp_nobound
                · exact hJ3 () ⟨by assumption, hl1_t⟩
                · c0_hfast_nogrp_nobound
                  exact hQ (l1.setWidth 64, ()) s m rfl hlen ⟨⟨rfl, rfl⟩, hexps⟩ hm
                · simp_all
            · intro J2 hJ2; c0_hfast_nogrp_nobound
              · exact hJ2 () (by assumption)
              · c0_hfast_nogrp_nobound
                exact hQ (l0.setWidth 64, ()) s m rfl hlen ⟨⟨rfl, rfl⟩, hexps⟩ hm
              · exact hJ2 () (by rcases h1 with h0 | h1' <;> simp_all)
          · intro J1 hJ1; c0_hfast_nogrp_nobound
            · exact hJ1 () (Or.inl (by assumption))
            · exact hJ1 () (Or.inr (by assumption))
            · exact hQ (0xFFFFFFFF#64, ()) s m rfl hlen ⟨⟨rfl, rfl⟩, hexps⟩ hm
        · intro Jok1 hJok1; c0_hfast_nogrp
          · have hl1_lt : l1.toNat < 2 * s.core.cur_vars := by
              dsimp only [l1, w1]
              have h1 : (s.scratch.scratch_buf[(2200 + 2 * cl_id.toNat +
                  1) % 2 ^ 64]'hw1_lt').toNat < 2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 := by
                assumption
              simp only [hi1]; omega
            exact hJok1 _ m ⟨rfl, fun _ => hl1_lt⟩
          all_goals exact hJok1 (false, ()) m ⟨rfl, fun hc => absurd hc (by decide)⟩
      · intro Jok0 hJok0; c0_hfast_nogrp
        · have hl0_lt : l0.toNat < 2 * s.core.cur_vars := by
            dsimp only [l0, w0]
            have h1 : ((s.scratch.scratch_buf[(2200 + 2 * cl_id.toNat) %
                2 ^ 64]'hw0_lt') &&& 2147483647#32).toNat <
                2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 := by assumption
            simp only [hi0]; omega
          exact hJok0 _ m ⟨rfl, fun _ => hl0_lt⟩
        all_goals exact hJok0 (false, ()) m ⟨rfl, fun hc => by cases hc⟩
    · exact hQ (0xFFFFFFFF#64, ()) s m rfl hlen ⟨⟨rfl, rfl⟩, hexps⟩ hm
    ·   have hal_le := hlen.core_ok.arena_len_le
        have hw0_end : w0.toNat + 3 ≤ s.core.arena_len := by
          have hz := bv32_lit_toNat_mod64 w0; dsimp only [w0] at hz ⊢; simp only [hi0]
          have h1 : ¬ s.core.arena_len % 2 ^ 64 <
              ((s.scratch.scratch_buf[(2200 + 2 * cl_id.toNat) %
                2 ^ 64]'hw0_lt').toNat + 3) % 2 ^ 64 := by assumption
          omega
        have hcsz_lt : (w0.setWidth 64 + 2#64).toNat < s.core.arena.length := by
          have hz := bv32_lit_toNat_mod64 w0
          rw [har_len, BitVec.toNat_add, BitVec.toNat_ofNat, hz]; omega
        c0_hfast_nogrp_nobound
        · exact hQ (0xFFFFFFFF#64, ()) s m rfl hlen ⟨⟨rfl, rfl⟩, hexps⟩ hm
        · exact hQ (0xFFFFFFFF#64, ()) s m rfl hlen ⟨⟨rfl, rfl⟩, hexps⟩ hm
        · let csz := s.core.arena[(w0.setWidth 64 + 2#64).toNat]'hcsz_lt
          have hcsz3 : 3 ≤ csz.toNat := Nat.le_of_not_lt (by
            dsimp only [csz, w0]; simp only [hi0]; assumption)
          have hcsz_end : w0.toNat + 3 + csz.toNat ≤ s.core.arena_len := by
            have hc : ¬ s.core.arena_len % 2 ^ 64 < (w0.toNat + BitVec.toNat (3 : BitVec 64) +
                csz.toNat) % 2 ^ 64 := by dsimp only [csz, w0]; simp only [hi0]; assumption
            change ¬ _ < (w0.toNat + 3 + csz.toNat) % 2 ^ 64 at hc; omega
          refine wp_loop_safety_slice (fullSafetySlice c) s R (fun _ => True) trivial
            (fun st (sum, stored, cnt, psteps, tail_i, last_lit, j, ()) =>
              FullExtScratchPres s st ∧ WalkTblExpsOk st ∧
              stored.toNat ≤ c.max_vars ∧ tail_i.toNat ≤ csz.toNat ∧ j.toNat ≤ csz.toNat)
            (fun (_, _, _, _, _, _, j, ()) => csz.toNat - j.toNat) ?_ ?_
          · intro Jl hJl; c0_hfast_nobound
            exact hJl s (0#64, 0#64, 0#64, 0#64, csz, 0xFFFFFFFF#32, 0#32, ()) m hm rfl hlen
              ⟨⟨rfl, rfl⟩, hexps, Nat.zero_le _, Nat.le_refl _, Nat.zero_le _⟩
          · rintro Jl st ⟨sum, stored, cnt, psteps, tail_i, last_lit, j, ⟨⟩⟩ ml
              hcorel hlenl _ ⟨hextl, hexpsl, hst_le, htl_le, hj_le⟩ hml hJl
            rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcorel hlenl hm hml hJl
            have harl := hlenl.core_ok.arena_len_arr; have hal_le := hlenl.core_ok.arena_len_le
            have hal_eq := congrArg FullCoreState.arena_len hcorel
            have hvall := hlenl.core_ok.vals_len; have hsbl := hlenl.scratch_ok.scratch_buf_len
            have htrcl := hlenl.scratch_ok.tarjan_reach_len
            have hwk1l := hlenl.scratch_ok.work_stk1_len
            have hwk2l := hlenl.scratch_ok.work_stk2_len
            c0_hfast_nogrp_nobound
            · have hj_lt : j.toNat < csz.toNat := by
                dsimp only [csz, w0]; simp only [hi0]; assumption
              have hlit_ar : (w0.setWidth 64 + 3#64 + j.setWidth 64).toNat <
                  st.core.arena.length := by
                have hz1 := bv32_lit_toNat_mod64 w0; have hz2 := bv32_lit_toNat_mod64 j
                rw [← hal_eq] at hcsz_end
                rw [harl, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, hz1, hz2]; omega
              c0_hfast_nogrp_nobound
              let lit := st.core.arena[(w0.setWidth 64 + 3#64 + j.setWidth 64).toNat]'hlit_ar
              refine wp_join_safety_slice (ts := [i64, i64, i64, i64, i32, i32])
                (fullSafetySlice c) st R (fun _ => True) trivial
                (fun st1 (sum1, stored1, cnt1, psteps1, tail_i1, last_lit1, ()) =>
                  FullExtScratchPres s st1 ∧ WalkTblExpsOk st1 ∧
                  stored1.toNat ≤ c.max_vars ∧ tail_i1.toNat ≤ csz.toNat) ?_ ?_
              · rintro Js st1 ⟨sum1, stored1, cnt1, psteps1, tail_i1, last_lit1, ⟨⟩⟩ m1
                  hcore1 hlen1 _ ⟨hext1, hexps1, hst1, htl1⟩ hm1
                rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore1 hlen1 hm1
                c0_hfast_nobound
                exact hJl st1 (sum1, stored1, cnt1, psteps1, tail_i1, last_lit1, j + 1#32, ())
                  m1 hm1 (by dsimp only; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
                  hcore1 hlen1 ⟨hext1, hexps1, hst1, htl1,
                    by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega⟩
              · intro Js hJs; c0_hfast_nogrp
                · have hlit_lt : lit.toNat < 2 * s.core.cur_vars :=
                    walk_pick_arena_lit_lt (by omega) hlit_ar
                      (by dsimp only [w0]; simp only [hi0]; assumption)
                  refine walk_call_break_m7 hBrk rfl hlenl hml fun b m1 hm1 => ?_
                  refine wp_join_group (ts := [i64]) (fun _ m2 => m1 = m2) ?_ ?_
                  · rintro Jsc ⟨sc, ⟨⟩⟩ _ rfl; rw [Blocks.get_here]
                    c0_hfast_nogrp_nobound
                    refine wp_call_of_spec _ _ (hAdd _ _ _ _ fun sum' => ?_)
                    have hn_trc : (lit ^^^ 1#32).toNat < st.scratch.tarjan_reach.length := by
                      rw [htrcl]; exact Nat.lt_of_lt_of_le (bv32_lit_neg_lt hlit_lt) (by omega)
                    c0_hfast_nogrp_nobound; c0_hstep_nobound; c0_hfast_nogrp_nobound
                    · have hst_lt : stored.toNat < c.max_vars := by
                        have hc1 : stored.toNat < c.max_vars % 2 ^ 64 := by assumption
                        omega
                      have hwk1_i : stored.toNat < st.scratch.work_stk1.length := by
                        rw [hwk1l]; omega
                      have hwk2_i : 2 * stored.toNat + 1 < st.scratch.work_stk2.length := by
                        rw [hwk2l]; omega
                      have hwk2_i' : (stored * 8#64).toNat / 4 + 1 <
                          st.scratch.work_stk2.length := by
                        rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                        omega
                      c0_hfast_nobound; dsimp only [fullSafetySlice] at hJs
                      refine hJs _ (sum', stored + 1#64, cnt + 1#64, _, tail_i, lit, ()) _
                        (by assumption) ?_ ?_ ?_
                      · rfl
                      · exact ⟨hlenl.core_ok, { hlenl.scratch_ok with
                          work_stk1_len := by simp [hwk1l]
                          work_stk2_len := by simp [hwk2l] }⟩
                      · exact ⟨⟨hextl.1, hextl.2⟩, walkTblExpsOk_of_sb_eq rfl hexpsl,
                          by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega, htl_le⟩
                    · c0_hfast_nobound <;> first
                        | exact hJs st (sum', stored, cnt + 1#64, _, j, lit, ()) m1 hm1
                            rfl hlenl ⟨hextl, hexpsl, hst_le, by omega⟩
                        | exact hJs st (sum', stored, cnt + 1#64, _, tail_i, lit, ()) m1 hm1
                            rfl hlenl ⟨hextl, hexpsl, hst_le, htl_le⟩
                  · intro Jsc hJsc; clear hQ hJl
                    c0_hfast_nogrp_nobound
                    · have hb_lt : 2 * b.toNat + 1 < st.scratch.scratch_buf.length := by
                        have hlt : b.toNat < exps.toNat := by assumption
                        rw [hsbl]; omega
                      have hb_lt' : (b.setWidth 64 * 8#64).toNat / 4 + 1 <
                          st.scratch.scratch_buf.length := by
                        have hz := bv32_lit_toNat_mod64 b
                        rw [BitVec.toNat_mul, BitVec.toNat_ofNat, hz, Nat.mod_eq_of_lt (by omega)]
                        omega
                      c0_hfast_nobound; exact hJsc _ m1 rfl
                    · exact hJsc _ m1 rfl
                all_goals
                  exact hJs st (sum, stored, cnt, psteps, tail_i, last_lit, ()) ml hml
                    rfl hlenl ⟨hextl, hexpsl, hst_le, htl_le⟩
            · exact hQ (0xFFFFFFFF#64, ()) st ml hcorel hlenl ⟨hextl, hexpsl⟩ hml
            · exact hQ (0xFFFFFFFF#64, ()) st ml hcorel hlenl ⟨hextl, hexpsl⟩ hml
            · have h2165 : (1082#64 * 8#64 : BitVec 64).toNat / 4 + 1 <
                  st.scratch.scratch_buf.length := by
                rw [hsbl, show (1082#64 * 8#64 : BitVec 64).toNat = 8656 from rfl]; omega
              c0_hfast_nogrp_nobound
              obtain ⟨st_r, hm_r, hcore_r, hlen_r, hext_r, hexps_r⟩ :
                  ∃ st_r : FullState, (FullMem c st_r ⋆ R) m ∧
                    PreservesCoreSlice FullState.core s st_r ∧ FullState.LengthsOk c st_r ∧
                    FullExtScratchPres s st_r ∧ WalkTblExpsOk st_r :=
                ⟨_, hm, hcorel, walk2_lengthsOk_set_sb2 hlenl, hextl,
                  walkTblExpsOk_store_imm (by decide) hexpsl⟩
              clear hm
              have har_r := hlen_r.core_ok.arena_len_arr; have hval_r := hlen_r.core_ok.vals_len
              have hsb_r := hlen_r.scratch_ok.scratch_buf_len
              have hwk1_r := hlen_r.scratch_ok.work_stk1_len
              have hwk2_r := hlen_r.scratch_ok.work_stk2_len
              refine wp_join_mem (ts := [i64]) ?_ ?_
              · rintro Jrnd ⟨rnd, ⟨⟩⟩; rw [Blocks.get_here]
                c0_hfast_nogrp_nobound
                refine wp_call_of_spec _ _ (hMul _ _ _ _ fun thr => ?_)
                refine wp_join_mem (ts := [i64, i32, i64]) ?_ ?_
                · rintro Jbs ⟨acc0, ch0, _sidx0, ⟨⟩⟩; rw [Blocks.get_here]
                  refine wp_join_group (ts := [i64, i32])
                    (fun _ m' => (FullMem c st_r ⋆ R) m') ?_ ?_
                  · rintro Jbk ⟨acc1, ch1, ⟨⟩⟩ m' hm'; rw [Blocks.get_here]
                    refine wp_join_group (ts := [i32])
                      (fun _ m'' => (FullMem c st_r ⋆ R) m'') ?_ ?_
                    · rintro Jch ⟨ch2, ⟨⟩⟩ m'' hm''; rw [Blocks.get_here]
                      refine wp_join_group (ts := [i64])
                        (fun _ m3 => (FullMem c st_r ⋆ R) m3) ?_ ?_
                      · rintro Jps ⟨ps1, ⟨⟩⟩ m3 hm3; rw [Blocks.get_here]
                        c0_hfast_nogrp_nobound
                        exact hQ _ st_r m3 hcore_r hlen_r ⟨hext_r, hexps_r⟩ hm3
                      · intro Jps hJps; c0_hfast_nogrp_nobound <;> exact hJps _ m'' hm''
                    · intro Jch hJch; c0_hfast_nogrp_nobound <;> exact hJch _ m' hm'
                  · intro Jbk hJbk; c0_hfast_nogrp_nobound
                    · refine wp_join_group (ts := [i64, i32, i32])
                        (fun _ m' => (FullMem c st_r ⋆ R) m') ?_ ?_
                      · rintro Jb2 ⟨acc1, ch1, _k1, ⟨⟩⟩ m' hm'; rw [Blocks.get_here]
                        exact hJbk (acc1, ch1, ()) m' hm'
                      · intro Jb2 hJb2
                        refine wp_loop_group (ts := [i64, i32])
                          (fun n (_, k, ()) mk => (FullMem c st_r ⋆ R) mk ∧
                            k.toNat ≤ csz.toNat ∧ csz.toNat - k.toNat ≤ n) ?_ ?_
                        · rintro Jk _ ⟨acck, k, ⟨⟩⟩ mk hJk ⟨hmk, hk_le, hmeas⟩
                          rw [Blocks.get_here]; clear hQ hJl
                          c0_hfast_nogrp_nobound
                          · have hk_lt : k.toNat < csz.toNat := by
                              dsimp only [csz, w0]; simp only [hi0]; assumption
                            have hlit_ar : (w0.setWidth 64 + 3#64 + k.setWidth 64).toNat <
                                st_r.core.arena.length := by
                              have hz1 := bv32_lit_toNat_mod64 w0
                              have hz2 := bv32_lit_toNat_mod64 k
                              rw [har_r, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
                                hz1, hz2]; omega
                            c0_hfast_nogrp_nobound
                            refine wp_join_group (ts := [i64, i32])
                              (fun _ m' => (FullMem c st_r ⋆ R) m') ?_ ?_
                            · rintro Jst ⟨acc', _ch', ⟨⟩⟩ m' hm'; rw [Blocks.get_here]
                              c0_hfast_nobound
                              exact hJk (csz.toNat - (k + 1#32).toNat) (acc', k + 1#32, ()) m'
                                (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
                                ⟨hm', by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega,
                                  Nat.le_refl _⟩
                            · intro Jst hJst; c0_hfast_nobound
                              · have hlit_v : (st_r.core.arena[(w0.setWidth 64 + 3#64 +
                                    k.setWidth 64).toNat]'hlit_ar).toNat <
                                    st_r.core.vals.length := by
                                  have hlt := walk_pick_arena_lit_lt (cv := s.core.cur_vars)
                                    (by omega) hlit_ar
                                    (by dsimp only [w0]; simp only [hi0]; assumption)
                                  rw [hval_r]; omega
                                c0_hfast_nobound
                                · refine walk_call_break_m7 hBrk rfl hlen_r hmk fun b m3 hm3 => ?_
                                  refine wp_join_group (ts := [i64]) (fun _ m4 => m3 = m4) ?_ ?_
                                  · rintro Jsc ⟨sc, ⟨⟩⟩ _ rfl; rw [Blocks.get_here]
                                    refine wp_call_of_spec _ _ (hAdd _ _ _ _ fun acc' => ?_)
                                    c0_hfast_nobound
                                    · exact hJb2 (acc', _, k, ()) m3 hm3
                                    · exact hJst (acc', ch0, ()) m3 hm3
                                  · intro Jsc hJsc; c0_hfast_nogrp_nobound
                                    · have hb_lt : 2 * b.toNat + 1 <
                                          st_r.scratch.scratch_buf.length := by
                                        have hlt : b.toNat < exps.toNat := by assumption
                                        rw [hsb_r]; omega
                                      have hb_lt' : (b.setWidth 64 * 8#64).toNat / 4 + 1 <
                                          st_r.scratch.scratch_buf.length := by
                                        have hz := bv32_lit_toNat_mod64 b
                                        rw [BitVec.toNat_mul, BitVec.toNat_ofNat, hz,
                                          Nat.mod_eq_of_lt (by omega)]; omega
                                      c0_hfast_nobound; exact hJsc _ m3 rfl
                                    · exact hJsc _ m3 rfl
                                · exact hJst (acck, ch0, ()) mk hmk
                              · exact hJst (acck, ch0, ()) mk hmk
                          · exact hJb2 (acck, ch0, k, ()) mk hmk
                        · intro Jk hJk; c0_hfast_nobound
                          exact hJk (csz.toNat - tail_i.toNat) (acc0, tail_i, ()) _
                            ⟨hm_r, htl_le, Nat.le_refl _⟩
                    · exact hJbk (acc0, ch0, ()) _ hm_r
                    · exact hJbk (acc0, ch0, ()) _ hm_r
                · intro Jbs hJbs
                  refine wp_loop_mem (ts := [i64, i64])
                    (fun (accs, sidx, ()) => sidx.toNat ≤ stored.toNat)
                    (fun (_, sidx, ()) => stored.toNat - sidx.toNat) ?_ ?_
                  · intro Js hJs; c0_hfast_nobound
                    exact hJs (0#64, 0#64, ()) (Nat.zero_le _)
                  · rintro Js ⟨accs, sidx, ⟨⟩⟩ hs_le hJs
                    rw [Blocks.get_here]
                    clear hQ hJl hcore_r hlen_r hext_r hexps_r hcorel hlenl hextl hexpsl hlen hm
                    c0_hfast_nogrp_nobound
                    · have hs_lt : sidx.toNat < stored.toNat := by assumption
                      have hs_wk2 : 2 * sidx.toNat + 1 < st_r.scratch.work_stk2.length := by
                        rw [hwk2_r]; omega
                      have hs_wk2' : (sidx * 8#64).toNat / 4 + 1 <
                          st_r.scratch.work_stk2.length := by
                        rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                        omega
                      c0_hfast_nobound
                      refine wp_call_of_spec _ _ (hAdd _ _ _ _ fun acc' => ?_)
                      c0_hfast_nobound
                      · have hs_wk1 : sidx.toNat < st_r.scratch.work_stk1.length := by
                          rw [hwk1_r]; omega
                        c0_hfast_nobound; exact hJbs (acc', _, sidx, ())
                      · exact hJs (acc', sidx + 1#64, ())
                          (by dsimp only; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
                          (by dsimp only; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
                    · exact hJbs (accs, 0xFFFFFFFF#32, sidx, ())
              · intro Jrnd hJrnd
                clear hQ hJl hcore_r hlen_r hext_r hexps_r hcorel hlenl hextl hexpsl hlen hm hm_r
                c0_hfast_nogrp_nobound
                · exact hJrnd _
                · refine wp_call_of_spec _ _ (hFrom _ _ _ _ fun fv => ?_)
                  c0_hfast_nogrp_nobound; exact hJrnd _


end LeanQbe.T.Examples.Kissat.Proof.Walk
