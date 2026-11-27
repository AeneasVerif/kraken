/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3Walk
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3Spec
public import LeanQbe.T.Examples.Kissat.FullM7WalkProof0
public import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Examples.Kissat.FullArena

/-!
# Kissat Fidelity Step 13 Shard S3-A Proofs — Part 0 (`FullFidelityStep13S3WalkProof0`)

Callee-parametric (`Γ : Env`, `XPost := False`, `0` SAT model proofs) `Func.wp` proofs for the
first `6` ProbSAT walk helpers in `FullFidelityStep13S3Walk`:
1. `full_walk_cb_inv_m7_step13_wp` (`step13WalkCbInvSpec`)
2. `full_walk_init_table_m7_step13_wp` (`m7InitTableSpec`)
3. `full_walk_effort_m7_step13_wp` (`step13WalkEffortSpec`)
4. `full_walk_break_m7_step13_wp` (`m7BreakSpec`)
5. `full_walk_flip_m7_step13_wp` (`step13WalkFlipSpec`)
6. `full_walk_collect_m7_step13_wp` (`m7CollectSpec`)
-/

set_option autoImplicit false

local elab "s3w_hsteps_nj" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S3

open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM7Walk
open Kraken.Bedrock2.Test
open scoped FullArenaTactics
open scoped S3WalkMemTactics

/-! ## 1. Shared Arithmetic & Scratch State Helpers -/

section Helpers

private theorem s3_ext_refl (s : FullState) : FullExtScratchPres s s := ⟨rfl, rfl⟩

private theorem s3_ext_trans {s1 s2 s3 : FullState}
    (h12 : FullExtScratchPres s1 s2) (h23 : FullExtScratchPres s2 s3) :
    FullExtScratchPres s1 s3 :=
  ⟨h23.1.trans h12.1, h23.2.trans h12.2⟩

private theorem s3_ext_scrBuf (s : FullState) (b : List (BitVec 32)) :
    FullExtScratchPres s { s with scratch := { s.scratch with scratch_buf := b } } :=
  s3_ext_refl s

private theorem s3_len_scrBuf {c : FullCfg} {s : FullState} (h : s.LengthsOk c)
    {i : Nat} {v : BitVec 32} :
    ({ s with scratch := { s.scratch with scratch_buf := s.scratch.scratch_buf.set i v } } :
      FullState).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with scratch_buf_len := by simp [h.scratch_ok.scratch_buf_len] }⟩

private theorem s3_len_scrBuf_u64 {c : FullCfg} {s : FullState} (h : s.LengthsOk c)
    {i : Nat} {v : BitVec 64} :
    ({ s with scratch := { s.scratch with
      scratch_buf := setU64In32 s.scratch.scratch_buf i v } } : FullState).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with
    scratch_buf_len := by rw [setU64In32_length, h.scratch_ok.scratch_buf_len] }⟩

private theorem s3_len_wvals {c : FullCfg} {s : FullState} (h : s.LengthsOk c)
    {i : Nat} {v : BitVec 8} :
    ({ s with scratch := { s.scratch with walk_vals := s.scratch.walk_vals.set i v } } :
      FullState).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with walk_vals_len := by simp [h.scratch_ok.walk_vals_len] }⟩

private theorem s3_zext32 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat :=
  zext_toNat x (by decide)

private theorem s3_bv64_zext32_lt {x : BitVec 32} {ub : Nat} (hx : x.toNat < ub) :
    (x.setWidth 64).toNat < ub := by
  rwa [s3_zext32]

private theorem s3_bv64_shl1_toNat {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show 2 ^ 1 = 2 from rfl,
    show x.toNat * 2 = 2 * x.toNat by omega, Nat.mod_eq_of_lt hx]

private theorem s3_bv64_add1_toNat {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by bv_omega

private theorem s3_bv64_sub1_toNat {x : BitVec 64} (hx : 0 < x.toNat) :
    (x - 1#64).toNat = x.toNat - 1 := by
  rw [BitVec.toNat_sub, show (1#64 : BitVec 64).toNat = 1 from rfl,
    show 2 ^ 64 - 1 + x.toNat = (x.toNat - 1) + 1 * 2 ^ 64 by omega,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by have := x.isLt; omega)]

private theorem s3_sub1_le {cu ncl : BitVec 64} (hpos : 0 < cu.toNat)
    (hle : cu.toNat ≤ ncl.toNat) : (cu - 1#64).toNat ≤ ncl.toNat := by
  rw [s3_bv64_sub1_toNat hpos]; omega

private theorem s3_bv32_xor1_lt {x : BitVec 32} {n : Nat} (hx : x.toNat < 2 * n) :
    (x ^^^ 1#32).toNat < 2 * n := by
  have h1 : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := rfl
  rw [h1]; exact litNeg_lt_two_mul hx

private theorem s3_pos_of_bv64_ofNat_ne0 {n : Nat} (hb : n < 2 ^ 64)
    (hne : BitVec.ofNat 64 n ≠ 0#64) : 0 < n := by
  have h0 : (BitVec.ofNat 64 n).toNat ≠ 0 := fun h => hne (BitVec.eq_of_toNat_eq h)
  rw [bv64_ofNat_toNat hb] at h0; omega

private theorem s3_le_of_not_bv64_ofNat_lt {n : Nat} {x : BitVec 64} (hb : n < 2 ^ 64)
    (h : ¬ BitVec.ofNat 64 n < x) : x.toNat ≤ n := by
  have h1 : ¬ n < x.toNat := by
    intro hlt; apply h
    change (BitVec.ofNat 64 n).toNat < x.toNat
    rwa [bv64_ofNat_toNat hb]
  exact Nat.le_of_not_lt h1

private theorem s3_bv64_pack32_lo_and (hi cur : BitVec 64) :
    (((hi <<< (32 : Nat)) ||| (cur &&& 0xFFFFFFFF#64)) &&& 0xFFFFFFFF#64).toNat ≤
      cur.toNat := by
  have hzero : (hi <<< (32 : Nat)) &&& 0xFFFFFFFF#64 = 0#64 := by
    ext i hi_lt
    simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft, BitVec.getElem_zero]
    by_cases h32 : i < 32
    · simp [h32]
    · have hf : (0xFFFFFFFF#64 : BitVec 64)[i] = false := by
        rw [BitVec.getElem_eq_testBit_toNat, show (0xFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 32 - 1
          from rfl, Nat.testBit_two_pow_sub_one]; simp [h32]
      simp [hf]
  rw [BitVec.and_comm _ 0xFFFFFFFF#64, BitVec.and_or_distrib_left,
    BitVec.and_comm 0xFFFFFFFF#64 _, hzero, BitVec.zero_or,
    BitVec.and_comm 0xFFFFFFFF#64 _, BitVec.and_assoc,
    show (0xFFFFFFFF#64 &&& 0xFFFFFFFF#64 : BitVec 64) = 0xFFFFFFFF#64 by decide,
    BitVec.toNat_and]
  exact Nat.and_le_left

private theorem s3_bv64_and_lo32_le (x : BitVec 64) : (x &&& 0xFFFFFFFF#64).toNat ≤ x.toNat := by
  rw [BitVec.toNat_and]; exact Nat.and_le_left

private theorem s3_state_abs (s : FullState) {c : FullCfg} {s_new : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s_new ⋆ R) m) (hc : PreservesCoreSlice FullState.core s s_new)
    (hl : s_new.LengthsOk c) (he : FullExtScratchPres s s_new) :
    ∃ st : FullState, PreservesCoreSlice FullState.core s st ∧
      st.LengthsOk c ∧ FullExtScratchPres s st ∧ (FullMem c st ⋆ R) m :=
  ⟨s_new, hc, hl, he, hm⟩

private theorem s3_state_abs_pre (s : FullState) {c : FullCfg} {s_new : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s_new ⋆ R) m) (hc : PreservesCoreSlice FullState.core s s_new)
    (hl : s_new.LengthsOk c) (he : FullExtScratchPres s s_new)
    (hp : WalkScrPrefixPres s s_new) :
    ∃ st : FullState, PreservesCoreSlice FullState.core s st ∧
      st.LengthsOk c ∧ FullExtScratchPres s st ∧ WalkScrPrefixPres s st ∧
      (FullMem c st ⋆ R) m :=
  ⟨s_new, hc, hl, he, hp, hm⟩

private theorem s3_rem1_mod {ncl cap mk : Nat} (h5 : 2200 + 5 * ncl ≤ cap) (hc : cap < 2 ^ 28)
    (hle : mk ≤ (2 ^ 64 - (2200 + 2 * ncl + ncl + ncl + ncl) % 2 ^ 64 + cap) % 2 ^ 64) :
    mk ≤ cap - (2200 + 5 * ncl) := by
  have hb : (2200 + 2 * ncl + ncl + ncl + ncl) % 2 ^ 64 = 2200 + 5 * ncl := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  rw [hb, show 2 ^ 64 - (2200 + 5 * ncl) + cap = (cap - (2200 + 5 * ncl)) + 1 * 2 ^ 64 by omega,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)] at hle
  exact hle

private theorem s3_rem2_mod {ncl cap mk r : Nat} (h5 : 2200 + 5 * ncl ≤ cap) (hc : cap < 2 ^ 28)
    (hmk : mk ≤ cap - (2200 + 5 * ncl))
    (hle : ¬ (2 ^ 64 - mk + (2 ^ 64 - (2200 + 2 * ncl + ncl + ncl + ncl) % 2 ^ 64 + cap)) %
      2 ^ 64 < r) :
    r ≤ cap - (2200 + 5 * ncl) - mk := by
  have hb : (2200 + 2 * ncl + ncl + ncl + ncl) % 2 ^ 64 = 2200 + 5 * ncl := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  rw [hb, show 2 ^ 64 - mk + (2 ^ 64 - (2200 + 5 * ncl) + cap) =
      (cap - (2200 + 5 * ncl) - mk) + 2 * 2 ^ 64 by omega,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)] at hle
  omega

private theorem s3_rem_sub_le {ncl cap : Nat} {bv_ncl mk : BitVec 64}
    (hn : bv_ncl.toNat = ncl) (h5 : 2200 + 5 * ncl ≤ cap) (hc : cap < 2 ^ 28)
    (hmk : mk.toNat ≤ cap - (2200 + 5 * ncl)) :
    (BitVec.ofNat 64 cap - (2200#64 + (bv_ncl <<< (1 : Nat)) + bv_ncl + bv_ncl + bv_ncl) -
      mk).toNat ≤ cap - (2200 + 5 * ncl) - mk.toNat := by
  subst hn
  have hsh : (bv_ncl <<< (1 : Nat)).toNat = 2 * bv_ncl.toNat := s3_bv64_shl1_toNat (by omega)
  have hbase : (2200#64 + (bv_ncl <<< (1 : Nat)) + bv_ncl + bv_ncl + bv_ncl).toNat =
      2200 + 5 * bv_ncl.toNat := by
    simp only [BitVec.toNat_add, show (2200#64 : BitVec 64).toNat = 2200 from rfl, hsh,
      Nat.mod_add_mod]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hcap : (BitVec.ofNat 64 cap).toNat = cap := bv64_ofNat_toNat (by omega)
  have h1 : (BitVec.ofNat 64 cap -
      (2200#64 + (bv_ncl <<< (1 : Nat)) + bv_ncl + bv_ncl + bv_ncl)).toNat =
      cap - (2200 + 5 * bv_ncl.toNat) := by
    rw [BitVec.toNat_sub, hcap, hbase,
      show 2 ^ 64 - (2200 + 5 * bv_ncl.toNat) + cap =
        (cap - (2200 + 5 * bv_ncl.toNat)) + 1 * 2 ^ 64 by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_sub, h1,
    show 2 ^ 64 - mk.toNat + (cap - (2200 + 5 * bv_ncl.toNat)) =
      (cap - (2200 + 5 * bv_ncl.toNat) - mk.toNat) + 1 * 2 ^ 64 by omega,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  exact Nat.le_refl _

private theorem s3_bv64_2200_add_2n {n : BitVec 64} (h : 2200 + 2 * n.toNat + 1 < 2 ^ 64) :
    (2200#64 + (n <<< (1 : Nat))).toNat = 2200 + 2 * n.toNat := by
  rw [BitVec.toNat_add, show (2200#64 : BitVec 64).toNat = 2200 from rfl,
    s3_bv64_shl1_toNat (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem s3_bv64_2200_add_2n1 {n : BitVec 64} (h : 2200 + 2 * n.toNat + 1 < 2 ^ 64) :
    (2200#64 + (n <<< (1 : Nat)) + 1#64).toNat = 2200 + 2 * n.toNat + 1 := by
  rw [BitVec.toNat_add, s3_bv64_2200_add_2n h, show (1#64 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt h]

end Helpers

/-! ## 2. `full_walk_cb_inv_m7_step13_wp`, `init_table`, `effort`, `break` -/

/-- Step-13 `full_walk_cb_inv_m7` satisfies `step13WalkCbInvSpec`: populates `tbl[0..1082]` in
`scratch_buf` via `f64u_*` and establishes `WalkTblExpsOk` (`tbl[1080] ≤ 1080`). -/
theorem full_walk_cb_inv_m7_step13_wp (Γ : Env)
    (hAdd : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_add" [i64, i64] [i64] a m Q X)
    (hSub : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_sub" [i64, i64] [i64] a m Q X)
    (hMul : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_mul" [i64, i64] [i64] a m Q X)
    (hDiv : ∀ a m Q X, f64uPure2Spec a m Q X → Γ "f64u_div" [i64, i64] [i64] a m Q X)
    (hFrom : ∀ a m Q X, f64uPure1Spec a m Q X → Γ "f64u_from_u64" [i64] [i64] a m Q X) :
    ∀ a m Q X, step13WalkCbInvSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.full_walk_cb_inv_m7_body a m Q X := by
  rintro ⟨h, ncl, tot_lits, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  have hscr := c.hscr; unfold dimacsBound at hscr
  have hsbl := hlen.scratch_ok.scratch_buf_len
  dsimp only [Func.wp, FullFidelityStep13S3.full_walk_cb_inv_m7_body]
  c0_hsplit
  · c0_hsteps; exact hQ (0#64, ()) s m rfl hlen ⟨s3_ext_refl s, fun h0 => (h0 rfl).elim⟩ hm
  c0_hsplit
  · c0_hsteps; exact hQ (0#64, ()) s m rfl hlen ⟨s3_ext_refl s, fun h0 => (h0 rfl).elim⟩ hm
  have hcap2208 : 2208 ≤ c.scratch_cap := by
    have h1 : ¬ c.scratch_cap % 2 ^ 64 < (2208#64 : BitVec 64).toNat := by assumption
    rw [show (2208#64 : BitVec 64).toNat = 2208 from rfl, Nat.mod_eq_of_lt (by omega)] at h1
    omega
  c0_hsteps_nogrp
  -- Join `cb` after `if ((widx & 1ULL) != 0ULL)`
  refine wp_join_group (ts := [i64]) (fun (_cb, ()) m1 => m1 = m)
    (fun _ ⟨cb, ⟨⟩⟩ m1 hm1 => ?_) (fun Jcb hJcb => ?_)
  · subst m1
    c0_hsteps_nogrp
    c0_call hDiv; intro base
    c0_hsteps_nogrp
    -- Table fill loop: `while (next != 0ULL && i < 1080ULL)`
    refine wp_loop_safety_slice_pure (ts := [i64, i64, i64]) (fullSafetySlice c) s R
      (fun st (_next, _eps, i, ()) => i.toNat ≤ 1080 ∧ FullExtScratchPres s st)
      (fun (_, _, i, ()) => 1080 - i.toNat) ?_ ?_
    · intro Ji hJi; c0_hsteps
      exact hJi s (0x3FF0000000000000#64, 0x3FF0000000000000#64, 0#64, ()) m hm rfl hlen
        ⟨Nat.zero_le _, s3_ext_refl s⟩
    · rintro Ji st ⟨next, eps, i, ⟨⟩⟩ ml hcore hlen' ⟨hi_le, hext⟩ hml ihi
      dsimp only [fullSafetySlice] at hcore hlen' hml
      have hsbl' := hlen'.scratch_ok.scratch_buf_len
      refine wp_join_group (ts := []) (fun () me => me = ml)
        (fun _ ⟨⟩ me hme => by
          rcases hme with rfl
          c0_let_simp
          refine wp_store_sep (S3WalkMemTactics.store_full_scratch_buf_u64 (i := 1080) i
            (by rw [hsbl']; omega) hml) ?_
          intro m1 hm1
          let st1 : FullState := { st with scratch := { st.scratch with
            scratch_buf := setU64In32 st.scratch.scratch_buf 1080 i } }
          have hlen1 : st1.LengthsOk c := s3_len_scrBuf_u64 hlen'
          have hok1 : WalkTblExpsOk st1 :=
            walkTblExpsOk_of_setU64_1080 (by rw [hsbl']; omega) hi_le
          c0_let_simp
          refine wp_store_sep (S3WalkMemTactics.store_full_scratch_buf_u64 (i := 1081) eps
            (by rw [hlen1.scratch_ok.scratch_buf_len]; omega) hm1) ?_
          intro m2 hm2
          let st2 : FullState := { st1 with scratch := { st1.scratch with
            scratch_buf := setU64In32 st1.scratch.scratch_buf 1081 eps } }
          have hlen2 : st2.LengthsOk c := s3_len_scrBuf_u64 hlen1
          have hok2 : WalkTblExpsOk st2 := walkTblExpsOk_of_setU64_ne (by decide) hok1
          s3w_hsteps_nj
          refine wp_store_sep (S3WalkMemTactics.store_full_scratch_buf_u64 (i := 1082)
            (st2.scratch.rng_state ^^^ (s.scratch.walk_cnt_stat + 1#64))
            (by rw [hlen2.scratch_ok.scratch_buf_len]; omega) hm2) ?_
          intro m3 hm3
          let st3 : FullState := { st2 with scratch := { st2.scratch with
            scratch_buf := setU64In32 st2.scratch.scratch_buf 1082
              (st2.scratch.rng_state ^^^ (s.scratch.walk_cnt_stat + 1#64)) } }
          have hlen3 : st3.LengthsOk c := s3_len_scrBuf_u64 hlen2
          have hok3 : WalkTblExpsOk st3 := walkTblExpsOk_of_setU64_ne (by decide) hok2
          s3w_hsteps_nj
          exact hQ (i, ()) st3 m3 hcore hlen3 ⟨hext, fun _ => hok3⟩ hm3)
        (fun Js hJs => by
          c0_hsplit
          · c0_hsplit
            · have hi_lt : i.toNat < 1080 := by assumption
              have hi_sb : 2 * i.toNat + 1 < st.scratch.scratch_buf.length := by rw [hsbl']; omega
              have hi1 : (i + 1#64).toNat = i.toNat + 1 := s3_bv64_add1_toNat (by omega)
              c0_hsteps_nogrp
              let st1 : FullState := { st with scratch := { st.scratch with
                scratch_buf := setU64In32 st.scratch.scratch_buf i.toNat next } }
              c0_call hMul; intro next'
              c0_hsteps
              exact ihi st1 (next', next, i + 1#64, ()) _ ‹_› (by dsimp only; omega) rfl
                (s3_len_scrBuf_u64 hlen') ⟨by omega, hext⟩
            · c0_hsteps; exact hJs () ml rfl
          · c0_hsteps; exact hJs () ml rfl)
  · -- `if ((widx & 1ULL) != 0ULL)`
    c0_hsplit
    · c0_hsteps_nogrp
      c0_call hFrom; intro ftot
      c0_hsteps_nogrp
      c0_call hFrom; intro fncl
      c0_hsteps_nogrp
      c0_call hDiv; intro size
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64, i64, i64, i64]) (fun _ m1 => m = m1)
        (fun _ _ m1 hm1 => by
          rcases hm1 with rfl; c0_hsteps_nogrp
          c0_call hSub; intro _; c0_hsteps_nogrp
          c0_call hSub; intro _; c0_hsteps_nogrp
          c0_call hSub; intro _; c0_hsteps_nogrp
          c0_call hMul; intro _; c0_hsteps_nogrp
          c0_call hDiv; intro _; c0_hsteps_nogrp
          c0_call hAdd; intro cb'; c0_hsteps
          exact hJcb (cb', ()) m rfl)
        (fun Jx hJx => by c0_hsteps <;> exact hJx (_, _, _, _, ()) m rfl)
    · c0_hsteps; exact hJcb (0x4000000000000000#64, ()) m rfl

/-- Step-13 `full_walk_init_table_m7` is a no-op, trivially satisfying `step13WalkInitTableSpec`. -/
theorem full_walk_init_table_m7_step13_wp (Γ : Env) :
    ∀ a m Q X, step13WalkInitTableSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.full_walk_init_table_m7_body a m Q X := by
  rintro ⟨h, iq, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [Func.wp, FullFidelityStep13S3.full_walk_init_table_m7_body]
  c0_hsteps
  exact hQ () s m rfl hlen (s3_ext_refl s) hm

/-- Step-13 `full_walk_effort_m7` is read-only and computes `(dt * 50) / 1000`. -/
theorem full_walk_effort_m7_step13_wp (Γ : Env) :
    ∀ a m Q X, step13WalkEffortSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.full_walk_effort_m7_body a m Q X := by
  rintro ⟨h, mf, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  dsimp only [Func.wp, FullFidelityStep13S3.full_walk_effort_m7_body]
  have h1000 : (1000#64 : BitVec 64) ≠ 0#64 := by decide
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun _ m1 => m = m1)
    (fun _ ⟨dt0, ⟨⟩⟩ m1 hm1 => by
      rcases hm1 with rfl
      refine wp_join_group (ts := [i64]) (fun _ m2 => m = m2)
        (fun _ ⟨dt1, ⟨⟩⟩ m2 hm2 => by
          rcases hm2 with rfl; c0_hsteps; exact hQ (_, ()) s m rfl hlen rfl hm)
        (fun J2 hJ2 => by c0_hsteps <;> exact hJ2 (_, ()) m rfl))
    (fun J1 hJ1 => by c0_hsteps <;> exact hJ1 (_, ()) m rfl)

/-- Step-13 `full_walk_break_m7` is read-only (`step13WalkBreakSpec`) with `2200ULL` offset. -/
theorem full_walk_break_m7_step13_wp (Γ : Env) :
    ∀ a m Q X, step13WalkBreakSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.full_walk_break_m7_body a m Q X := by
  rintro ⟨h, not_lit, ncl, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  have hmax := c.hmaxv; have hscr := c.hscr; unfold dimacsBound at hmax hscr
  have hsbl := hlen.scratch_ok.scratch_buf_len
  have htmkl := hlen.scratch_ok.tarjan_mark_len
  have htrcl := hlen.scratch_ok.tarjan_reach_len
  have hret0 : Q (0#32, ()) m := hQ (0#32, ()) s m rfl hlen rfl hm
  dsimp only [Func.wp, FullFidelityStep13S3.full_walk_break_m7_body]
  s3w_hsteps_nj
  · exact hret0
  · exact hret0
  · exact hret0
  · exact hret0
  · exact hret0
  · exact hret0
  · have hcv2 : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
    have hcv1 : 0 < s.core.cur_vars := s3_pos_of_bv64_ofNat_ne0 (by omega) ‹_›
    have hnl : not_lit.toNat < 2 * s.core.cur_vars := by
      have hnl0 : (not_lit.setWidth 64).toNat <
          ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat := by c0_bound
      rw [s3_zext32, s3_bv64_shl1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
        bv64_ofNat_toNat (by omega)] at hnl0
      exact hnl0
    have hncl_sc : ncl.toNat ≤ c.scratch_cap := s3_le_of_not_bv64_ofNat_lt (by omega) ‹_›
    have h5n : 2200 + 5 * ncl.toNat ≤ c.scratch_cap := by
      have h5 : (2200#64 + 5#64 * ncl).toNat ≤ c.scratch_cap := by c0_bound
      have hm5 : (5#64 * ncl).toNat = 5 * ncl.toNat := by
        rw [BitVec.toNat_mul, show (5#64 : BitVec 64).toNat = 5 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      rw [BitVec.toNat_add, show (2200#64 : BitVec 64).toNat = 2200 from rfl, hm5,
        Nat.mod_eq_of_lt (by omega)] at h5
      exact h5
    have hnl_tmk : (not_lit.setWidth 64).toNat < s.scratch.tarjan_mark.length := by
      rw [htmkl]; exact s3_bv64_zext32_lt (by omega)
    have hnl_trc : (not_lit.setWidth 64).toNat < s.scratch.tarjan_reach.length := by
      rw [htrcl]; exact s3_bv64_zext32_lt (by omega)
    have hoff_le :
        ((s.scratch.tarjan_mark[(not_lit.setWidth 64).toNat]'hnl_tmk).setWidth 64).toNat ≤
          c.scratch_cap - (2200 + 5 * ncl.toNat) := by c0_bound
    refine wp_join_group (ts := [i64]) (fun (len', ()) m1 =>
        (FullMem c s ⋆ R) m1 ∧
        len'.toNat ≤ c.scratch_cap - (2200 + 5 * ncl.toNat) -
          ((s.scratch.tarjan_mark[(not_lit.setWidth 64).toNat]'hnl_tmk).setWidth 64).toNat) ?_ ?_
    · rintro _ ⟨len', ⟨⟩⟩ m1 ⟨hm1, hlen_le⟩
      s3w_hsteps_nj
      refine wp_loop_inv (ts := [i64, i32])
        (fun (k, _brk, ()) ml => (FullMem c s ⋆ R) ml ∧ k.toNat ≤ len'.toNat)
        (fun (k, _brk, ()) _ => len'.toNat - k.toNat) ?_ ?_
      · intro Jk hJk; s3w_hsteps_nj
        exact hJk (0#64, 0#32, ()) m1 ⟨hm1, Nat.zero_le _⟩
      · rintro Jk ⟨k, brk, ⟨⟩⟩ ml ⟨hml, hk_le⟩ ihk
        s3w_hsteps_nj
        · have hk_lt : k.toNat < len'.toNat := by c0_bound
          have hidx_occ : (2200#64 + 5#64 * ncl +
              (s.scratch.tarjan_mark[(not_lit.setWidth 64).toNat]'hnl_tmk).setWidth 64 +
              k).toNat < s.scratch.scratch_buf.length := by
            rw [hsbl]; c0_bound
          s3w_hsteps_nj
          refine wp_join_group (ts := [i32]) (fun (_brk', ()) mb => (FullMem c s ⋆ R) mb) ?_ ?_
          · rintro _ ⟨brk', ⟨⟩⟩ mb hmb
            s3w_hsteps_nj
            have hk1 : (k + 1#64).toNat = k.toNat + 1 := s3_bv64_add1_toNat (by omega)
            exact ihk (k + 1#64, brk', ()) mb (by dsimp only; omega) ⟨hmb, by omega⟩
          · intro Jb hJb; s3w_hsteps_nj
            · have hc_ncl :
                  ((s.scratch.scratch_buf[(2200#64 + 5#64 * ncl +
                    (s.scratch.tarjan_mark[(not_lit.setWidth 64).toNat]'hnl_tmk).setWidth 64 +
                    k).toNat]'hidx_occ).setWidth 64).toNat < ncl.toNat := by c0_bound
              have hsh_ncl : (ncl <<< (1 : Nat)).toNat = 2 * ncl.toNat :=
                s3_bv64_shl1_toNat (by omega)
              have hsat_lt :
                  (2200#64 + (ncl <<< (1 : Nat)) +
                    (s.scratch.scratch_buf[(2200#64 + 5#64 * ncl +
                      (s.scratch.tarjan_mark[(not_lit.setWidth 64).toNat]'hnl_tmk).setWidth 64 +
                      k).toNat]'hidx_occ).setWidth 64).toNat <
                  s.scratch.scratch_buf.length := by
                generalize hv32 : s.scratch.scratch_buf[(2200#64 + 5#64 * ncl +
                  (s.scratch.tarjan_mark[(not_lit.setWidth 64).toNat]'hnl_tmk).setWidth 64 +
                  k).toNat]'hidx_occ = c32 at hc_ncl ⊢
                rw [hsbl, BitVec.toNat_add, BitVec.toNat_add, hsh_ncl,
                  show (2200#64 : BitVec 64).toNat = 2200 from rfl, s3_zext32,
                  Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                rw [s3_zext32] at hc_ncl; omega
              s3w_hsteps_nj <;> exact hJb (_, ()) ml hml
            · exact hJb (brk, ()) ml hml
        · exact hQ (brk, ()) s ml rfl hlen rfl hml
    · intro Jl hJl; s3w_hsteps_nj
      · exact hJl (_, ()) m ⟨hm, by c0_bound⟩
      · exact hJl (_, ()) m ⟨hm, by c0_bound⟩

/-! ## 3. `full_walk_flip_m7_step13_wp` -/

private theorem s3_walk_occ_lt {c : FullCfg} {st : FullState} {ncl k lb : BitVec 64}
    {mk : BitVec 32} (_h5n : 2200 + 5 * ncl.toNat ≤ c.scratch_cap)
    (hscr : c.scratch_cap < 2 ^ 28) (hsh : (ncl <<< (1 : Nat)).toNat = 2 * ncl.toNat)
    (hlb : lb.toNat ≤ c.scratch_cap - (2200 + 5 * ncl.toNat) - (mk.setWidth 64).toNat)
    (hk : k.toNat < lb.toNat) (hsb : st.scratch.scratch_buf.length = c.scratch_cap) :
    (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl + mk.setWidth 64 + k).toNat <
      st.scratch.scratch_buf.length := by
  simp only [s3_zext32] at hlb
  simp only [BitVec.toNat_add, show (2200#64 : BitVec 64).toNat = 2200 from rfl,
    hsh, s3_zext32, Nat.mod_add_mod]
  rw [Nat.mod_eq_of_lt (by omega), hsb]; omega

private theorem s3_walk_sat_eq {ncl : BitVec 64} {v : BitVec 32}
    (h5n : 2200 + 5 * ncl.toNat < 2 ^ 28) (hsh : (ncl <<< (1 : Nat)).toNat = 2 * ncl.toNat)
    (_hv : v.toNat < ncl.toNat) :
    (2200#64 + (ncl <<< (1 : Nat)) + v.setWidth 64).toNat = 2200 + 2 * ncl.toNat + v.toNat := by
  simp only [BitVec.toNat_add, hsh, show (2200#64 : BitVec 64).toNat = 2200 from rfl,
    s3_zext32, Nat.mod_add_mod]
  rw [Nat.mod_eq_of_lt (by omega)]

private theorem s3_walk_upos_eq {ncl : BitVec 64} {v : BitVec 32}
    (h5n : 2200 + 5 * ncl.toNat < 2 ^ 28) (hsh : (ncl <<< (1 : Nat)).toNat = 2 * ncl.toNat)
    (_hv : v.toNat < ncl.toNat) :
    (2200#64 + (ncl <<< (1 : Nat)) + ncl + v.setWidth 64).toNat =
      2200 + 3 * ncl.toNat + v.toNat := by
  simp only [BitVec.toNat_add, hsh, show (2200#64 : BitVec 64).toNat = 2200 from rfl,
    s3_zext32, Nat.mod_add_mod]
  rw [Nat.mod_eq_of_lt (by omega)]; omega

private theorem s3_walk_unsat_eq {ncl x : BitVec 64}
    (h5n : 2200 + 5 * ncl.toNat < 2 ^ 28) (hsh : (ncl <<< (1 : Nat)).toNat = 2 * ncl.toNat)
    (hx : x.toNat ≤ ncl.toNat) :
    (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + x).toNat = 2200 + 4 * ncl.toNat + x.toNat := by
  simp only [BitVec.toNat_add, hsh, show (2200#64 : BitVec 64).toNat = 2200 from rfl,
    Nat.mod_add_mod]
  rw [Nat.mod_eq_of_lt (by omega)]; omega

private theorem s3_walk_last_idx {ncl cu : BitVec 64}
    (hsum : (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + cu).toNat =
      2200 + 4 * ncl.toNat + cu.toNat) (_h5n : 2200 + 5 * ncl.toNat < 2 ^ 28)
    (hcu : cu.toNat ≤ ncl.toNat) :
    (2 ^ 64 - BitVec.toNat (1 : BitVec 64) +
      (BitVec.toNat (2200 : BitVec 64) + 2 * ncl.toNat + ncl.toNat + ncl.toNat +
        cu.toNat)) % 2 ^ 64 =
    (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + cu - 1#64).toNat := by
  rw [s3_bv64_sub1_toNat (by omega), hsum, show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
    show BitVec.toNat (2200 : BitVec 64) = 2200 from rfl]
  omega

/-- Step-13 `full_walk_flip_m7` satisfies `step13WalkFlipSpec`: preserves `FullExtScratchPres`,
`WalkScrPrefixPres` (`scratch_buf` writes have index `≥ 2200`), and `(r &&& 0xFFFFFFFF) ≤ ncl`. -/
theorem full_walk_flip_m7_step13_wp (Γ : Env) :
    ∀ a m Q X, step13WalkFlipSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.full_walk_flip_m7_body a m Q X := by
  rintro ⟨h, flip_lit, ncl, ulen, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  have hmax := c.hmaxv; have hscr := c.hscr; unfold dimacsBound at hmax hscr
  have hwvl := hlen.scratch_ok.walk_vals_len
  dsimp only [Func.wp, FullFidelityStep13S3.full_walk_flip_m7_body]
  s3w_hsteps_nj
  refine wp_join_group (ts := []) (fun () mu => (FullMem c s ⋆ R) mu) ?_ ?_
  · rintro _ ⟨⟩ m0 hm0
    refine wp_join_group (ts := [i64]) (fun (r0, ()) mr =>
        (FullMem c s ⋆ R) mr ∧ r0.toNat ≤ ncl.toNat)
      (fun _ ⟨r0, ⟨⟩⟩ mr ⟨hmr, hr0⟩ => by
        s3w_hsteps_nj
        exact hQ (r0, ()) s mr rfl hlen
          ⟨s3_ext_refl s, walkScrPrefixPres_refl s,
            Nat.le_trans (s3_bv64_and_lo32_le r0) hr0⟩ hmr)
      (fun Jr hJr => by
        s3w_hsteps_nj
        · exact hJr (ncl, ()) _ ⟨hm0, Nat.le_refl _⟩
        · exact hJr (ulen, ()) _ ⟨hm0, by c0_bound⟩)
  · intro Jg hJg
    s3w_hsteps_nj
    all_goals try exact hJg () m hm
    have hcv2 : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
    have hcv1 : 0 < s.core.cur_vars := s3_pos_of_bv64_ofNat_ne0 (by omega) ‹_›
    have hfl : flip_lit.toNat < 2 * s.core.cur_vars := by
      have h0 : (flip_lit.setWidth 64).toNat <
          ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat := by c0_bound
      rw [s3_zext32, s3_bv64_shl1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
        bv64_ofNat_toNat (by omega)] at h0; exact h0
    have hnl : (flip_lit ^^^ 1#32).toNat < 2 * s.core.cur_vars := s3_bv32_xor1_lt hfl
    have hncl_sc : ncl.toNat ≤ c.scratch_cap := s3_le_of_not_bv64_ofNat_lt (by omega) ‹_›
    have h5n : 2200 + 5 * ncl.toNat ≤ c.scratch_cap := by
      have h5 : (2200#64 + 5#64 * ncl).toNat ≤ c.scratch_cap := by c0_bound
      have hm5 : (5#64 * ncl).toNat = 5 * ncl.toNat := by
        rw [BitVec.toNat_mul, show (5#64 : BitVec 64).toNat = 5 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      rw [BitVec.toNat_add, show (2200#64 : BitVec 64).toNat = 2200 from rfl, hm5,
        Nat.mod_eq_of_lt (by omega)] at h5; exact h5
    have hsh_ncl : (ncl <<< (1 : Nat)).toNat = 2 * ncl.toNat := s3_bv64_shl1_toNat (by omega)
    have hnl_wv : ((flip_lit ^^^ 1#32).setWidth 64).toNat <
        (s.scratch.walk_vals.set (flip_lit.setWidth 64).toNat
          ((1 : BitVec 32).setWidth 8)).length := by
      rw [List.length_set, hwvl]; exact s3_bv64_zext32_lt (by omega)
    s3w_hsteps_nj
    obtain ⟨st0, hcore0, hlen0, hext0, hpre0, hm0⟩ :=
      s3_state_abs_pre s hm rfl (s3_len_wvals (s3_len_wvals hlen))
        (s3_ext_refl s) (walkScrPrefixPres_refl s)
    clear hm
    have hfl_tmk : (flip_lit.setWidth 64).toNat < st0.scratch.tarjan_mark.length := by
      rw [hlen0.scratch_ok.tarjan_mark_len]; exact s3_bv64_zext32_lt (by omega)
    have hfl_trc : (flip_lit.setWidth 64).toNat < st0.scratch.tarjan_reach.length := by
      rw [hlen0.scratch_ok.tarjan_reach_len]; exact s3_bv64_zext32_lt (by omega)
    refine wp_join_group (ts := [i64]) (fun (cu0, ()) m0 =>
        (FullMem c st0 ⋆ R) m0 ∧ cu0.toNat ≤ ncl.toNat) ?_ ?_
    · rintro _ ⟨cu0, ⟨⟩⟩ m0 ⟨hm0', hcu0⟩
      s3w_hsteps_nj
      refine wp_join_safety_slice (fullSafetySlice c) st0 R (fun _ => True) trivial
        (fun st1 (cu1, _, ()) => cu1.toNat ≤ ncl.toNat ∧ FullExtScratchPres st0 st1 ∧
          WalkScrPrefixPres st0 st1)
        (fun _ st1 ⟨cu1, _, ⟨⟩⟩ m1 hcore1 hlen1 _ ⟨hcu1, hext1, hpre1⟩ hm1 => ?_)
        (fun J1 hJ1 => ?_)
      · dsimp only [fullSafetySlice] at hcore1 hlen1 hm1
        have hnl_tmk1 :
            ((flip_lit ^^^ 1#32).setWidth 64).toNat < st1.scratch.tarjan_mark.length := by
          rw [hlen1.scratch_ok.tarjan_mark_len]; exact s3_bv64_zext32_lt (by omega)
        have hnl_trc1 :
            ((flip_lit ^^^ 1#32).setWidth 64).toNat < st1.scratch.tarjan_reach.length := by
          rw [hlen1.scratch_ok.tarjan_reach_len]; exact s3_bv64_zext32_lt (by omega)
        s3w_hsteps_nj
        refine wp_join_safety_slice (fullSafetySlice c) st1 R (fun _ => True) trivial
          (fun st2 (cu2, _, ()) => cu2.toNat ≤ ncl.toNat ∧ FullExtScratchPres st1 st2 ∧
            WalkScrPrefixPres st1 st2)
          (fun _ st2 ⟨cu2, _, ⟨⟩⟩ m2 hcore2 hlen2 _ ⟨hcu2, hext2, hpre2⟩ hm2 => ?_)
          (fun J2 hJ2 => ?_)
        · dsimp only [fullSafetySlice] at hcore2 hlen2 hm2
          have hfl_trc2 : (flip_lit.setWidth 64).toNat < st2.scratch.tarjan_reach.length := by
            rw [hlen2.scratch_ok.tarjan_reach_len]; exact s3_bv64_zext32_lt (by omega)
          have hnl_trc2 : ((flip_lit ^^^ 1#32).setWidth 64).toNat <
              st2.scratch.tarjan_reach.length := by
            rw [hlen2.scratch_ok.tarjan_reach_len]; exact s3_bv64_zext32_lt (by omega)
          s3w_hsteps_nj
          refine wp_join_group (ts := [i64]) (fun _ m3 => (FullMem c st2 ⋆ R) m3)
            (fun _ ⟨hi, ⟨⟩⟩ m3 hm3 => by
              s3w_hsteps_nj
              exact hQ (_, ()) st2 m3 (hcore0.trans (hcore1.trans hcore2)) hlen2
                ⟨s3_ext_trans hext0 (s3_ext_trans hext1 hext2),
                  walkScrPrefixPres_trans hpre0 (walkScrPrefixPres_trans hpre1 hpre2),
                  Nat.le_trans (s3_bv64_pack32_lo_and hi cu2) hcu2⟩ hm3)
            (fun Jh hJh => by s3w_hsteps_nj <;> exact hJh (_, ()) _ hm2)
        · -- Break loop (`not_lit`)
          dsimp only [fullSafetySlice] at hJ2; s3w_hsteps_nj
          · refine wp_join_group (ts := [i64]) (fun (lb', ()) ml =>
                (FullMem c st1 ⋆ R) ml ∧
                lb'.toNat ≤ c.scratch_cap - (2200 + 5 * ncl.toNat) -
                  ((st1.scratch.tarjan_mark[
                    ((flip_lit ^^^ 1#32).setWidth 64).toNat]'hnl_tmk1).setWidth 64).toNat) ?_ ?_
            · rintro _ ⟨lb', ⟨⟩⟩ ml ⟨hml, hlb'⟩
              s3w_hsteps_nj
              refine wp_loop_safety_slice_pure (ts := [i64, i64]) (fullSafetySlice c) st1 R
                (fun st (cu, k, ()) => k.toNat ≤ lb'.toNat ∧ cu.toNat ≤ ncl.toNat ∧
                  FullExtScratchPres st1 st ∧ WalkScrPrefixPres st1 st)
                (fun (_cu, k, ()) => lb'.toNat - k.toNat)
                (fun Jk hJk => by
                  s3w_hsteps_nj
                  exact hJk st1 (cu1, 0#64, ()) ml hml rfl hlen1
                    ⟨Nat.zero_le _, hcu1, s3_ext_refl st1, walkScrPrefixPres_refl st1⟩)
                (fun Jk st ⟨cu, k, ⟨⟩⟩ mk hcorek hlenk ⟨hk_le, hcu, hextk, hprek⟩ hmk ihk => ?_)
              dsimp only [fullSafetySlice] at hcorek hlenk hmk
              have hsblk := hlenk.scratch_ok.scratch_buf_len; s3w_hsteps_nj
              · have hk_lt : k.toNat < lb'.toNat := by c0_bound
                have hk1 : (k + 1#64).toNat = k.toNat + 1 := s3_bv64_add1_toNat (by omega)
                have hidx_occ := s3_walk_occ_lt h5n hscr hsh_ncl hlb' hk_lt hsblk
                s3w_hsteps_nj
                refine wp_join_safety_slice (fullSafetySlice c) st R (fun _ => True) trivial
                  (fun st' (cu', ()) => cu'.toNat ≤ ncl.toNat ∧ FullExtScratchPres st st' ∧
                    WalkScrPrefixPres st st')
                  (fun _ st' ⟨cu', ⟨⟩⟩ m' hcore' hlen' _ ⟨hcu', hext', hpre'⟩ hm' => by
                    dsimp only [fullSafetySlice] at hcore' hlen' hm'; s3w_hsteps_nj
                    exact ihk st' (cu', k + 1#64, ()) m' hm' (by dsimp only; omega) hcore'
                      hlen' ⟨by omega, hcu', s3_ext_trans hextk hext',
                        walkScrPrefixPres_trans hprek hpre'⟩)
                  (fun Jc hJc => ?_)
                dsimp only [fullSafetySlice] at hJc; s3w_hsteps_nj
                · have hcb : (st.scratch.scratch_buf[(2200#64 + (ncl <<< (1 : Nat)) + ncl +
                      ncl + ncl + (st1.scratch.tarjan_mark[((flip_lit ^^^ 1#32).setWidth
                        64).toNat]'hnl_tmk1).setWidth 64 + k).toNat]'hidx_occ).toNat <
                      ncl.toNat := by
                    simpa only [BitVec.toNat_add,
                      show (2200#64 : BitVec 64).toNat = 2200 from rfl,
                      show (2200 : BitVec 64).toNat = 2200 from rfl, hsh_ncl, s3_zext32,
                      Nat.mod_add_mod, BitVec.toNat_xor,
                      show (1#32 : BitVec 32).toNat = 1 from rfl] using hc
                  generalize hv32 : st.scratch.scratch_buf[(2200#64 + (ncl <<< (1 : Nat)) +
                    ncl + ncl + ncl + (st1.scratch.tarjan_mark[
                      ((flip_lit ^^^ 1#32).setWidth 64).toNat]'hnl_tmk1).setWidth 64 +
                    k).toNat]'hidx_occ = c32 at hcb ⊢
                  have hsat_eq := s3_walk_sat_eq (by omega) hsh_ncl hcb
                  have hsat_lt : (2200#64 + (ncl <<< (1 : Nat)) + c32.setWidth 64).toNat <
                      st.scratch.scratch_buf.length := by rw [hsblk, hsat_eq]; omega
                  s3w_hsteps_nj
                  refine wp_join_safety_slice (fullSafetySlice c) st R
                    (fun _ => True) trivial
                    (fun st' (cu', _s', ()) => cu'.toNat ≤ ncl.toNat ∧
                      FullExtScratchPres st st' ∧ WalkScrPrefixPres st st')
                    (fun _ st' ⟨cu', _s', ⟨⟩⟩ m' hcore' hlen' _ ⟨hcu', hext', hpre'⟩ hm' =>
                      hJc st' (cu', ()) m' hm' hcore' hlen' ⟨hcu', hext', hpre'⟩)
                    (fun Jsc hJsc => ?_)
                  dsimp only [fullSafetySlice] at hJsc; s3w_hsteps_nj
                  · obtain ⟨st_s1, hcs1, hls1, hes1, hps1, hms1⟩ :=
                      s3_state_abs_pre st hm rfl (s3_len_scrBuf hlenk) (s3_ext_scrBuf st _)
                        (walkScrPrefixPres_set_ge (by
                          change 2200 ≤ (2200#64 + (ncl <<< (1 : Nat)) +
                            c32.setWidth 64).toNat
                          rw [hsat_eq]; omega))
                    clear hm
                    refine wp_join_safety_slice (fullSafetySlice c) st_s1 R
                      (fun _ => True) trivial
                      (fun st' (cu', ()) => cu'.toNat ≤ ncl.toNat ∧
                        FullExtScratchPres st_s1 st' ∧ WalkScrPrefixPres st_s1 st')
                      (fun _ st' ⟨cu', ⟨⟩⟩ m' hcore' hlen' _ ⟨hcu', hext', hpre'⟩ hm' =>
                        hJsc st' (cu', _, ()) m' hm' (hcs1.trans hcore') hlen'
                          ⟨hcu', s3_ext_trans hes1 hext',
                            walkScrPrefixPres_trans hps1 hpre'⟩)
                      (fun Ju hJu => ?_)
                    dsimp only [fullSafetySlice] at hJu; s3w_hsteps_nj
                    · have hcu_lt : cu.toNat < ncl.toNat := by c0_bound
                      have hupos_eq := s3_walk_upos_eq (by omega) hsh_ncl hcb
                      have hupos_lt : (2200#64 + (ncl <<< (1 : Nat)) + ncl +
                          c32.setWidth 64).toNat < st_s1.scratch.scratch_buf.length := by
                        rw [hls1.scratch_ok.scratch_buf_len, hupos_eq]; omega
                      have hunsat_eq := s3_walk_unsat_eq (by omega) hsh_ncl (Nat.le_of_lt hcu_lt)
                      have hunsat_lt : (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + cu).toNat <
                          (st_s1.scratch.scratch_buf.set (2200#64 + (ncl <<< (1 : Nat)) + ncl +
                            c32.setWidth 64).toNat (BitVec.setWidth 32 cu)).length := by
                        rw [List.length_set, hls1.scratch_ok.scratch_buf_len, hunsat_eq]; omega
                      s3w_hsteps_nj
                      have hp1 := walkScrPrefixPres_set_ge (s := st_s1)
                        (idx := (2200#64 + (ncl <<< (1 : Nat)) + ncl +
                          c32.setWidth 64).toNat)
                        (v := BitVec.setWidth 32 cu) (by rw [hupos_eq]; omega)
                      have hp2 := walkScrPrefixPres_set_ge
                        (s := { st_s1 with scratch := { st_s1.scratch with
                          scratch_buf := st_s1.scratch.scratch_buf.set
                            (2200#64 + (ncl <<< (1 : Nat)) + ncl +
                              c32.setWidth 64).toNat (BitVec.setWidth 32 cu) } })
                        (idx := (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + cu).toNat)
                        (v := c32) (by rw [hunsat_eq]; omega)
                      obtain ⟨st_s2, hcs2, hls2, hes2, hps2, hms2⟩ :=
                        s3_state_abs_pre st_s1 hm rfl
                          (s3_len_scrBuf (s3_len_scrBuf hls1))
                          (s3_ext_scrBuf st_s1 _) (walkScrPrefixPres_trans hp1 hp2)
                      exact hJu st_s2 (cu + 1#64, ()) m hms2 hcs2 hls2
                        ⟨by rw [s3_bv64_add1_toNat (by omega)]; omega, hes2, hps2⟩
                    all_goals
                      exact hJu st_s1 (cu, ()) m hms1 rfl hls1
                        ⟨hcu, s3_ext_refl st_s1, walkScrPrefixPres_refl st_s1⟩
                  · exact hJsc st (cu, _, ()) mk hmk rfl hlenk
                      ⟨hcu, s3_ext_refl st, walkScrPrefixPres_refl st⟩
                · exact hJc st (cu, ()) mk hmk rfl hlenk
                    ⟨hcu, s3_ext_refl st, walkScrPrefixPres_refl st⟩
              · exact hJ2 st (cu, _, ()) mk hmk hcorek hlenk ⟨hcu, hextk, hprek⟩
            · intro Jlb hJlb; s3w_hsteps_nj
              · have hmk_le : ((st1.scratch.tarjan_mark[((flip_lit ^^^ 1#32).setWidth 64).toNat]'
                    hnl_tmk1).setWidth 64).toNat ≤ c.scratch_cap - (2200 + 5 * ncl.toNat) := by
                  simpa only [s3_zext32, BitVec.toNat_xor,
                    show (1#32 : BitVec 32).toNat = 1 from rfl] using s3_rem1_mod h5n hscr ‹_›
                exact hJlb (_, ()) m1 ⟨hm1, s3_rem_sub_le rfl h5n hscr hmk_le⟩
              · have hrz : ((st1.scratch.tarjan_reach[((flip_lit ^^^ 1#32).setWidth 64).toNat]'
                    hnl_trc1).setWidth 64).toNat ≤ c.scratch_cap - (2200 + 5 * ncl.toNat) -
                    ((st1.scratch.tarjan_mark[((flip_lit ^^^ 1#32).setWidth 64).toNat]'
                      hnl_tmk1).setWidth 64).toNat := by
                  simpa only [s3_zext32, BitVec.toNat_xor,
                    show (1#32 : BitVec 32).toNat = 1 from rfl] using
                    s3_rem2_mod h5n hscr (s3_rem1_mod h5n hscr ‹_›) ‹_›
                exact hJlb (_, ()) m1 ⟨hm1, hrz⟩
          · exact hJ2 st1 (cu1, _, ()) m1 hm1 rfl hlen1
              ⟨hcu1, s3_ext_refl st1, walkScrPrefixPres_refl st1⟩
      · -- Make loop (`flip_lit`)
        dsimp only [fullSafetySlice] at hJ1; s3w_hsteps_nj
        · refine wp_join_group (ts := [i64]) (fun (lm', ()) ml =>
              (FullMem c st0 ⋆ R) ml ∧
              lm'.toNat ≤ c.scratch_cap - (2200 + 5 * ncl.toNat) -
                ((st0.scratch.tarjan_mark[
                  (flip_lit.setWidth 64).toNat]'hfl_tmk).setWidth 64).toNat) ?_ ?_
          · rintro _ ⟨lm', ⟨⟩⟩ ml ⟨hml, hlm'⟩
            s3w_hsteps_nj
            refine wp_loop_safety_slice_pure (ts := [i64, i64]) (fullSafetySlice c) st0 R
              (fun st (cu, k, ()) => k.toNat ≤ lm'.toNat ∧ cu.toNat ≤ ncl.toNat ∧
                FullExtScratchPres st0 st ∧ WalkScrPrefixPres st0 st)
              (fun (_cu, k, ()) => lm'.toNat - k.toNat)
              (fun Jk hJk => by
                s3w_hsteps_nj
                exact hJk st0 (cu0, 0#64, ()) ml hml rfl hlen0
                  ⟨Nat.zero_le _, hcu0, s3_ext_refl st0, walkScrPrefixPres_refl st0⟩)
              (fun Jk st ⟨cu, k, ⟨⟩⟩ mk hcorek hlenk ⟨hk_le, hcu, hextk, hprek⟩ hmk ihk => ?_)
            dsimp only [fullSafetySlice] at hcorek hlenk hmk
            have hsblk := hlenk.scratch_ok.scratch_buf_len; s3w_hsteps_nj
            · have hk_lt : k.toNat < lm'.toNat := by c0_bound
              have hk1 : (k + 1#64).toNat = k.toNat + 1 := s3_bv64_add1_toNat (by omega)
              have hidx_occ := s3_walk_occ_lt h5n hscr hsh_ncl hlm' hk_lt hsblk
              s3w_hsteps_nj
              refine wp_join_safety_slice (fullSafetySlice c) st R (fun _ => True) trivial
                (fun st' (cu', ()) => cu'.toNat ≤ ncl.toNat ∧ FullExtScratchPres st st' ∧
                  WalkScrPrefixPres st st')
                (fun _ st' ⟨cu', ⟨⟩⟩ m' hcore' hlen' _ ⟨hcu', hext', hpre'⟩ hm' => by
                  dsimp only [fullSafetySlice] at hcore' hlen' hm'; s3w_hsteps_nj
                  exact ihk st' (cu', k + 1#64, ()) m' hm' (by dsimp only; omega) hcore'
                    hlen' ⟨by omega, hcu', s3_ext_trans hextk hext',
                      walkScrPrefixPres_trans hprek hpre'⟩)
                (fun Jc hJc => ?_)
              dsimp only [fullSafetySlice] at hJc; s3w_hsteps_nj
              · have hcb : (st.scratch.scratch_buf[(2200#64 + (ncl <<< (1 : Nat)) + ncl +
                    ncl + ncl + (st0.scratch.tarjan_mark[
                      (flip_lit.setWidth 64).toNat]'hfl_tmk).setWidth 64 +
                    k).toNat]'hidx_occ).toNat < ncl.toNat := by c0_bound
                generalize hv32 : st.scratch.scratch_buf[(2200#64 + (ncl <<< (1 : Nat)) +
                  ncl + ncl + ncl + (st0.scratch.tarjan_mark[
                    (flip_lit.setWidth 64).toNat]'hfl_tmk).setWidth 64 +
                  k).toNat]'hidx_occ = c32 at hcb ⊢
                have hsat_eq := s3_walk_sat_eq (by omega) hsh_ncl hcb
                have hsat_lt : (2200#64 + (ncl <<< (1 : Nat)) + c32.setWidth 64).toNat <
                    st.scratch.scratch_buf.length := by rw [hsblk, hsat_eq]; omega
                s3w_hsteps_nj
                obtain ⟨st_s1, hcs1, hls1, hes1, hps1, hms1⟩ :=
                  s3_state_abs_pre st hm rfl (s3_len_scrBuf hlenk) (s3_ext_scrBuf st _)
                    (walkScrPrefixPres_set_ge (by
                      change 2200 ≤ (2200#64 + (ncl <<< (1 : Nat)) + c32.setWidth 64).toNat
                      rw [hsat_eq]; omega))
                clear hm
                refine wp_join_safety_slice (fullSafetySlice c) st_s1 R
                  (fun _ => True) trivial
                  (fun st' (cu', ()) => cu'.toNat ≤ ncl.toNat ∧
                    FullExtScratchPres st_s1 st' ∧ WalkScrPrefixPres st_s1 st')
                  (fun _ st' ⟨cu', ⟨⟩⟩ m' hcore' hlen' _ ⟨hcu', hext', hpre'⟩ hm' =>
                    hJc st' (cu', ()) m' hm' (hcs1.trans hcore') hlen'
                      ⟨hcu', s3_ext_trans hes1 hext', walkScrPrefixPres_trans hps1 hpre'⟩)
                  (fun Jz hJz => ?_)
                dsimp only [fullSafetySlice] at hJz; s3w_hsteps_nj
                · have hupos_eq := s3_walk_upos_eq (by omega) hsh_ncl hcb
                  have hupos_lt : (2200#64 + (ncl <<< (1 : Nat)) + ncl +
                      c32.setWidth 64).toNat < st_s1.scratch.scratch_buf.length := by
                    rw [hls1.scratch_ok.scratch_buf_len, hupos_eq]; omega
                  have hcu_pos : 0 < cu.toNat := by assumption
                  s3w_hsteps_nj
                  refine wp_join_safety_slice (ts := [i64]) (fullSafetySlice c) st_s1 R
                    (fun _ => True) trivial
                    (fun st' (cu', ()) => cu'.toNat ≤ ncl.toNat ∧
                      FullExtScratchPres st_s1 st' ∧ WalkScrPrefixPres st_s1 st')
                    (fun _ st' ⟨cu', ⟨⟩⟩ m' hcore' hlen' _ ⟨hcu', hext', hpre'⟩ hm' => by
                      dsimp only [fullSafetySlice] at hcore' hlen' hm'; s3w_hsteps_nj
                      exact hJz st' (cu', ()) m' hm' hcore' hlen' ⟨hcu', hext', hpre'⟩)
                    (fun Jl hJl => by
                      dsimp only [fullSafetySlice] at hJl; c0_let_simp
                      refine wp_jnz_of (fun hc => ?_) (fun hc => ?_)
                      all_goals
                        (try simp only [Arg.val_var] at hc); c0_cond hc; try c0_let_simp
                      · have hupos_idx_eq :
                            (2200 + 2 * ncl.toNat + ncl.toNat + c32.toNat) % 2 ^ 64 =
                            (2200#64 + (ncl <<< (1 : Nat)) + ncl +
                              c32.setWidth 64).toNat := by
                          rw [hupos_eq, Nat.mod_eq_of_lt (by omega)]; omega
                        have hpos_cu : (st_s1.scratch.scratch_buf[(2200#64 +
                            (ncl <<< (1 : Nat)) + ncl + c32.setWidth 64).toNat]'
                              hupos_lt).toNat < cu.toNat := by
                          have hc' : st_s1.scratch.scratch_buf[(2200 + 2 * ncl.toNat +
                              ncl.toNat + c32.toNat) % 2 ^ 64].toNat < cu.toNat := hc
                          simpa only [hupos_idx_eq] using hc'
                        have hsum_eq := s3_walk_unsat_eq (by omega) hsh_ncl hcu
                        have hlast_lt' : (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl +
                            cu - 1#64).toNat < st_s1.scratch.scratch_buf.length := by
                          rw [hls1.scratch_ok.scratch_buf_len,
                            s3_bv64_sub1_toNat (by omega), hsum_eq]; omega
                        have hpos_unsat_eq := s3_walk_unsat_eq (x :=
                          (st_s1.scratch.scratch_buf[(2200#64 + (ncl <<< (1 : Nat)) +
                            ncl + c32.setWidth 64).toNat]'hupos_lt).setWidth 64)
                          (by omega) hsh_ncl (by rw [s3_zext32]; omega)
                        have hpos_unsat_lt : (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl +
                            (st_s1.scratch.scratch_buf[(2200#64 + (ncl <<< (1 : Nat)) +
                              ncl + c32.setWidth 64).toNat]'hupos_lt).setWidth 64).toNat <
                            st_s1.scratch.scratch_buf.length := by
                          rw [hls1.scratch_ok.scratch_buf_len, hpos_unsat_eq, s3_zext32]
                          omega
                        s3w_hsteps_nj
                        obtain ⟨st_s2, hcs2, hls2, hes2, hps2, hms2⟩ :=
                          s3_state_abs_pre st_s1 hm rfl (s3_len_scrBuf hls1)
                            (s3_ext_scrBuf st_s1 _)
                            (walkScrPrefixPres_set_ge (by
                              change 2200 ≤ (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl +
                                (st_s1.scratch.scratch_buf[(2200#64 + (ncl <<< (1 : Nat)) +
                                  ncl + c32.setWidth 64).toNat]'hupos_lt).setWidth
                                  64).toNat
                              rw [hpos_unsat_eq]; omega))
                        clear hm
                        refine wp_join_safety_slice (ts := []) (fullSafetySlice c) st_s2 R
                          (fun _ => True) trivial
                          (fun st' _ => FullExtScratchPres st_s2 st' ∧
                            WalkScrPrefixPres st_s2 st')
                          (fun _ st' ⟨⟩ m' hcore' hlen' _ ⟨hext', hpre'⟩ hm' => by
                            dsimp only [fullSafetySlice] at hcore' hlen' hm'
                            have hupos_c32_lt : (2200#64 + (ncl <<< (1 : Nat)) + ncl +
                                c32.setWidth 64).toNat < st'.scratch.scratch_buf.length :=
                              by rw [hlen'.scratch_ok.scratch_buf_len, hupos_eq]; omega
                            s3w_hsteps_nj
                            obtain ⟨st_s3, hcs3, hls3, hes3, hps3, hms3⟩ :=
                              s3_state_abs_pre st' hm rfl (s3_len_scrBuf hlen')
                                (s3_ext_scrBuf st' _)
                                (walkScrPrefixPres_set_ge (by
                                  change 2200 ≤ (2200#64 + (ncl <<< (1 : Nat)) + ncl +
                                    c32.setWidth 64).toNat
                                  rw [hupos_eq]; omega))
                            exact hJl st_s3 (cu - 1#64, ()) _ hms3
                              (hcs2.trans (hcore'.trans hcs3)) hls3
                              ⟨s3_sub1_le hcu_pos hcu,
                                s3_ext_trans hes2 (s3_ext_trans hext' hes3),
                                walkScrPrefixPres_trans hps2
                                  (walkScrPrefixPres_trans hpre' hps3)⟩)
                          (fun Js_1 hJs_1 => by
                            dsimp only [fullSafetySlice] at hJs_1; c0_let_simp
                            refine wp_jnz_of (fun hc2 => ?_) (fun hc2 => ?_)
                            all_goals
                              (try simp only [Arg.val_var] at hc2)
                              c0_cond hc2; try c0_let_simp
                            · have hc2' : (st_s1.scratch.scratch_buf[(2200#64 +
                                  (ncl <<< (1 : Nat)) + ncl + ncl + cu - 1#64).toNat]'
                                    hlast_lt').toNat < ncl.toNat := by
                                simpa only [s3_walk_last_idx hsum_eq (by omega) hcu]
                                  using hc2
                              have hv_eq := s3_walk_upos_eq (by omega) hsh_ncl hc2'
                              have hupos_ld_lt : (2200#64 + (ncl <<< (1 : Nat)) + ncl +
                                  (st_s1.scratch.scratch_buf[(2200#64 +
                                    (ncl <<< (1 : Nat)) + ncl + ncl + cu - 1#64).toNat]'
                                      hlast_lt').setWidth 64).toNat <
                                  st_s2.scratch.scratch_buf.length := by
                                rw [hls2.scratch_ok.scratch_buf_len, hv_eq]; omega
                              s3w_hsteps_nj
                              obtain ⟨st_s3, hcs3, hls3, hes3, hps3, hms3⟩ :=
                                s3_state_abs_pre st_s2 hm rfl (s3_len_scrBuf hls2)
                                  (s3_ext_scrBuf st_s2 _)
                                  (walkScrPrefixPres_set_ge (by
                                    change 2200 ≤ (2200#64 + (ncl <<< (1 : Nat)) + ncl +
                                      (st_s1.scratch.scratch_buf[(2200#64 +
                                        (ncl <<< (1 : Nat)) + ncl + ncl + cu -
                                        1#64).toNat]'hlast_lt').setWidth 64).toNat
                                    rw [hv_eq]; omega))
                              exact hJs_1 st_s3 () _ hms3 hcs3 hls3 ⟨hes3, hps3⟩
                            · exact hJs_1 st_s2 () _ hms2 rfl hls2
                                ⟨s3_ext_refl st_s2, walkScrPrefixPres_refl st_s2⟩)
                      · exact hJl st_s1 (cu, ()) m hms1 rfl hls1
                          ⟨hcu, s3_ext_refl st_s1, walkScrPrefixPres_refl st_s1⟩)
                all_goals
                  exact hJz st_s1 (cu, ()) m hms1 rfl hls1
                    ⟨hcu, s3_ext_refl st_s1, walkScrPrefixPres_refl st_s1⟩
              · exact hJc st (cu, ()) mk hmk rfl hlenk
                  ⟨hcu, s3_ext_refl st, walkScrPrefixPres_refl st⟩
            · exact hJ1 st (cu, _, ()) mk hmk hcorek hlenk ⟨hcu, hextk, hprek⟩
          · intro Jlm hJlm; s3w_hsteps_nj
            · have hmk_le : ((st0.scratch.tarjan_mark[(flip_lit.setWidth 64).toNat]'
                  hfl_tmk).setWidth 64).toNat ≤ c.scratch_cap - (2200 + 5 * ncl.toNat) := by
                simpa only [s3_zext32] using s3_rem1_mod h5n hscr ‹_›
              exact hJlm (_, ()) m0 ⟨hm0', s3_rem_sub_le rfl h5n hscr hmk_le⟩
            · have hrz : ((st0.scratch.tarjan_reach[(flip_lit.setWidth 64).toNat]'
                  hfl_trc).setWidth 64).toNat ≤ c.scratch_cap - (2200 + 5 * ncl.toNat) -
                  ((st0.scratch.tarjan_mark[(flip_lit.setWidth 64).toNat]'
                    hfl_tmk).setWidth 64).toNat := by
                simpa only [s3_zext32] using
                  s3_rem2_mod h5n hscr (s3_rem1_mod h5n hscr ‹_›) ‹_›
              exact hJlm (_, ()) m0 ⟨hm0', hrz⟩
        · exact hJ1 st0 (cu0, _, ()) m0 hm0' rfl hlen0
            ⟨hcu0, s3_ext_refl st0, walkScrPrefixPres_refl st0⟩
    · intro Jcu hJcu; s3w_hsteps_nj
      · exact hJcu (ncl, ()) _ ⟨hm0, Nat.le_refl _⟩
      · exact hJcu (ulen, ()) _ ⟨hm0, by c0_bound⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S3
