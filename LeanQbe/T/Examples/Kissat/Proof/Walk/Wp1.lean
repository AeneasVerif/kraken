/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Walk.Helpers
public import LeanQbe.T.Examples.Kissat.Proof.Walk.Spec
public import LeanQbe.T.Examples.Kissat.Src.Walk

import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Walk WP Proofs — Part 1 (`Proof.Walk.Wp1`)

Proves canonical WP correctness for clause collection and occurrence-list construction:
1. `full_walk_collect_m7_wp` (`fullWalkCollectM7Spec`)
2. `full_walk_build_occ_m7_wp` (`fullWalkBuildOccM7Spec`)
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
open LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
open LeanQbe.T.Examples.Kissat.Proof.Walk.Spec

open scoped FullArenaTactics WalkMemTactics

/-! ## Shared Arithmetic & `LengthsOk` Helpers -/

private theorem walk_lengthsOk_set_sb {c : FullCfg} {s : FullState} {k : Nat} {v : BitVec 32}
    (hlen : FullState.LengthsOk c s) :
    FullState.LengthsOk c
      { s with scratch := { s.scratch with scratch_buf := s.scratch.scratch_buf.set k v } } :=
  ⟨hlen.core_ok, { hlen.scratch_ok with
    scratch_buf_len := by simp [hlen.scratch_ok.scratch_buf_len] }⟩

private theorem walk_lengthsOk_set_sb2 {c : FullCfg} {s : FullState} {k1 k2 : Nat}
    {v1 v2 : BitVec 32} (hlen : FullState.LengthsOk c s) :
    FullState.LengthsOk c
      { s with scratch := { s.scratch with
        scratch_buf := (s.scratch.scratch_buf.set k1 v1).set k2 v2 } } :=
  ⟨hlen.core_ok, { hlen.scratch_ok with
    scratch_buf_len := by simp [hlen.scratch_ok.scratch_buf_len] }⟩

private theorem walk_lengthsOk_set_trc {c : FullCfg} {s : FullState} {k : Nat} {v : BitVec 32}
    (hlen : FullState.LengthsOk c s) :
    FullState.LengthsOk c
      { s with scratch := { s.scratch with
        tarjan_reach := s.scratch.tarjan_reach.set k v } } :=
  ⟨hlen.core_ok, { hlen.scratch_ok with
    tarjan_reach_len := by simp [hlen.scratch_ok.tarjan_reach_len] }⟩

private theorem walk_lengthsOk_set_tmk_ws {c : FullCfg} {s : FullState}
    {k : Nat} {v1 v2 : BitVec 32} (hlen : FullState.LengthsOk c s) :
    FullState.LengthsOk c
      { s with scratch := { s.scratch with
        tarjan_mark := s.scratch.tarjan_mark.set k v1
        wsort := s.scratch.wsort.set k v2 } } :=
  ⟨hlen.core_ok, { hlen.scratch_ok with
    tarjan_mark_len := by simp [hlen.scratch_ok.tarjan_mark_len]
    wsort_len := by simp [hlen.scratch_ok.wsort_len] }⟩

private theorem walk_lengthsOk_set_ws {c : FullCfg} {s : FullState} {k : Nat} {v : BitVec 32}
    (hlen : FullState.LengthsOk c s) :
    FullState.LengthsOk c
      { s with scratch := { s.scratch with wsort := s.scratch.wsort.set k v } } :=
  ⟨hlen.core_ok, { hlen.scratch_ok with
    wsort_len := by simp [hlen.scratch_ok.wsort_len] }⟩

private theorem walkScrPrefixPres_set_ge2 {s : FullState} {k1 k2 : Nat}
    {v1 v2 : BitVec 32} (hk1 : 2200 ≤ k1) (hk2 : 2200 ≤ k2) :
    WalkScrPrefixPres s
      { s with scratch := { s.scratch with
        scratch_buf := (s.scratch.scratch_buf.set k1 v1).set k2 v2 } } :=
  fun j hj => by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]

private theorem bv64_shl_one (x : BitVec 64) : x <<< (1 : BitVec 64) = x <<< (1 : Nat) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft]

private theorem bv32_succ_toNat {x : BitVec 32} {n : Nat} (hx : x.toNat < n) (hn : n < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by bv_omega

private theorem bv64_succ_toNat {x : BitVec 64} {n : Nat} (hx : x.toNat < n) (hn : n < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by bv_omega

private theorem bv64_add2_toNat {x : BitVec 64} {n : Nat} (hx : x.toNat + 2 ≤ n) (hn : n < 2 ^ 64) :
    (x + 1#64 + 1#64).toNat = x.toNat + 2 := by bv_omega

private theorem bv64_2200_shl1 {x : BitVec 64} (hx : 2200 + 2 * x.toNat < 2 ^ 64) :
    (2200#64 + (x <<< (1 : Nat))).toNat = 2200 + 2 * x.toNat := by
  have h1 := bv64_shl1_toNat_lt (x := x) (by omega)
  bv_omega

private theorem bv64_2200_shl1_1 {x : BitVec 64} (hx : 2200 + 2 * x.toNat + 1 < 2 ^ 64) :
    (2200#64 + (x <<< (1 : Nat)) + 1#64).toNat = 2200 + 2 * x.toNat + 1 := by
  have h1 := bv64_shl1_toNat_lt (x := x) (by omega)
  bv_omega

private theorem bv64_sat_idx {ncl cb : BitVec 64} (hn : 2200 + 2 * ncl.toNat + cb.toNat < 2 ^ 64) :
    (2200#64 + (ncl <<< (1 : Nat)) + cb).toNat = 2200 + 2 * ncl.toNat + cb.toNat := by
  have h1 := bv64_shl1_toNat_lt (x := ncl) (by omega)
  bv_omega

private theorem bv64_upos_idx {ncl cb : BitVec 64}
    (hn : 2200 + 3 * ncl.toNat + cb.toNat < 2 ^ 64) :
    (2200#64 + (ncl <<< (1 : Nat)) + ncl + cb).toNat = 2200 + 3 * ncl.toNat + cb.toNat := by
  have h1 := bv64_shl1_toNat_lt (x := ncl) (by omega)
  bv_omega

private theorem bv64_unsat_idx {ncl u : BitVec 64}
    (hn : 2200 + 4 * ncl.toNat + u.toNat < 2 ^ 64) :
    (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + u).toNat = 2200 + 4 * ncl.toNat + u.toNat := by
  have h1 := bv64_shl1_toNat_lt (x := ncl) (by omega)
  bv_omega

private theorem bv64_occ_cap_eq {scap : Nat} {ncl : BitVec 64}
    (hsc : scap < 2 ^ 28) (h5 : 2200 + 5 * ncl.toNat ≤ scap) :
    (BitVec.ofNat 64 scap - (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl)).toNat =
      scap - (2200 + 5 * ncl.toNat) := by
  have h1 := bv64_shl1_toNat_lt (x := ncl) (by omega)
  bv_omega

private theorem bv64_occ_idx {ncl x : BitVec 64}
    (hn : 2200 + 5 * ncl.toNat + x.toNat < 2 ^ 64) :
    ((2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl) + x).toNat =
      2200 + 5 * ncl.toNat + x.toNat := by
  have h1 := bv64_shl1_toNat_lt (x := ncl) (by omega)
  bv_omega

private theorem bv32_succ_le_of_lt {j : BitVec 32} {n : Nat}
    (hj : j.toNat < n) (hn : n < 2 ^ 32) : (j + 1#32).toNat ≤ n := by bv_omega

private theorem bv32_sub_succ_lt {j : BitVec 32} {n : Nat}
    (hj : j.toNat < n) (hn : n < 2 ^ 32) : n - (j + 1#32).toNat < n - j.toNat := by bv_omega

private theorem bv64_succ_le_of_lt {j : BitVec 64} {n : Nat}
    (hj : j.toNat < n) (hn : n < 2 ^ 64) : (j + 1#64).toNat ≤ n := by bv_omega

private theorem bv64_sub_succ_lt {j : BitVec 64} {n : Nat}
    (hj : j.toNat < n) (hn : n < 2 ^ 64) : n - (j + 1#64).toNat < n - j.toNat := by bv_omega

private theorem bv64_occ_rem_eq {scap : Nat} {ncl off : BitVec 64}
    (hsc : scap < 2 ^ 28) (h5 : 2200 + 5 * ncl.toNat ≤ scap)
    (hoff : off.toNat ≤ scap - (2200 + 5 * ncl.toNat)) :
    (BitVec.ofNat 64 scap - (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl) - off).toNat =
      scap - (2200 + 5 * ncl.toNat) - off.toNat := by
  have h1 := bv64_shl1_toNat_lt (x := ncl) (by omega)
  bv_omega

private theorem walk_lit_bds {c : FullCfg} {s st : FullState} {lit : Nat}
    (hcore : PreservesCoreSlice FullState.core s st)
    (hcv : s.core.cur_vars ≤ c.max_vars) (hlen : st.LengthsOk c)
    (hl : lit < 2 * s.core.cur_vars) :
    lit < st.core.vals.length ∧ lit < st.scratch.walk_vals.length ∧
      lit < st.scratch.wsort.length ∧ lit < st.scratch.tarjan_mark.length ∧
      lit < st.scratch.tarjan_reach.length := by
  have hcv' : st.core.cur_vars ≤ c.max_vars := by
    rw [congrArg FullCoreState.cur_vars hcore]; exact hcv
  exact ⟨hlen.core_ok.vals_len ▸ by omega, hlen.scratch_ok.walk_vals_len ▸ by omega,
    hlen.scratch_ok.wsort_len ▸ by omega, hlen.scratch_ok.tarjan_mark_len ▸ by omega,
    hlen.scratch_ok.tarjan_reach_len ▸ by omega⟩

private theorem bv64_2200_5_le_bound {ncl tot csz scap : Nat}
    (hsc : scap < 2 ^ 28) (_hn : ncl ≤ scap) (_ht : tot ≤ scap) (hcz : csz < 2 ^ 32)
    (hc1 : ¬ scap < ncl + 1) (hc2 : ¬ scap < tot + csz)
    (hc3 : ¬ scap < 2200 + 5 * (ncl + 1) + tot + csz) :
    ncl + 1 ≤ scap ∧ tot + csz ≤ scap ∧ 2200 + 2 * ncl + 1 < scap ∧
      2200 + 5 * (ncl + 1) + tot + csz ≤ scap := by
  omega

private theorem walk_collect_bin_bounds {ncl tot scap : Nat}
    (hsc : scap < 2 ^ 28) (hn : ncl ≤ scap) (ht : tot ≤ scap)
    (hc1 : ¬ scap % 2 ^ 64 < (ncl + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64)
    (hc2 : ¬ scap % 2 ^ 64 < (tot + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64)
    (hc3 : ¬ scap % 2 ^ 64 < (BitVec.toNat (2200 : BitVec 64) +
      BitVec.toNat (5 : BitVec 64) * ((ncl + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64) +
      tot + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64) :
    ncl + 1 ≤ scap ∧ tot + 2 ≤ scap ∧ 2200 + 2 * ncl + 1 < scap ∧
      2200 + 5 * (ncl + 1) + tot + 2 ≤ scap := by
  have h1 : BitVec.toNat (1 : BitVec 64) = 1 := rfl
  have h2 : BitVec.toNat (2 : BitVec 64) = 2 := rfl
  have h5 : BitVec.toNat (5 : BitVec 64) = 5 := rfl
  have h2200 : BitVec.toNat (2200 : BitVec 64) = 2200 := rfl
  rw [h1, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc1
  rw [h2, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc2
  rw [h2200, h5, h1, h2, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc3
  omega

private theorem walk_collect_k1_lt {k : Nat} {off sz : BitVec 32}
    (hk1 : (k + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 <
      (off.toNat + sz.toNat) % 2 ^ 64)
    (hk : k < off.toNat + sz.toNat) :
    k + 1 < off.toNat + sz.toNat := by
  have h1 : BitVec.toNat (1 : BitVec 64) = 1 := rfl
  have := off.isLt; have := sz.isLt
  rw [h1, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hk1
  omega

private theorem walk_collect_push_inv {c : FullCfg} {s stk' : FullState}
    (hext : FullExtScratchPres s stk') {nk tk k : BitVec 64} {fk : Bool}
    {off sz : BitVec 32} (hscr : c.scratch_cap < 2 ^ 28)
    (h1 : nk.toNat + 1 ≤ c.scratch_cap) (h2 : tk.toNat + 2 ≤ c.scratch_cap)
    (h5 : 2200 + 5 * (nk.toNat + 1) + tk.toNat + 2 ≤ c.scratch_cap)
    (hk1 : (k + 1#64).toNat = k.toNat + 1) (hk : k.toNat + 1 ≤ off.toNat + sz.toNat) :
    FullExtScratchPres s stk' ∧
      (nk + 1#64).toNat ≤ c.scratch_cap ∧ (tk + 2#64).toNat ≤ c.scratch_cap ∧
      (k + 1#64).toNat ≤ off.toNat + sz.toNat ∧
      (fk = false → 2200 + 5 * (nk + 1#64).toNat + (tk + 2#64).toNat ≤ c.scratch_cap) := by
  have hnk1 : (nk + 1#64).toNat = nk.toNat + 1 := by bv_omega
  have htk2 : (tk + 2#64).toNat = tk.toNat + 2 := by bv_omega
  exact ⟨hext, by rw [hnk1]; omega, by rw [htk2]; omega,
    by rw [hk1]; omega, fun _ => by rw [hnk1, htk2]; omega⟩

private theorem wp_loop_mem1 {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost}
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

/-! ## 1. `full_walk_collect_m7` -/

theorem full_walk_collect_m7_wp (Γ : Env)
    (hArena : Γ.Has "full_arena_next" fullArenaNextSpec) :
    ∀ a m Q X, fullWalkCollectM7Spec a m Q X →
      Func.wp Γ full_walk_collect_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  have hmaxv := c.hmaxv; have hscr := c.hscr; have hwcap := c.hwcap; have har := c.harena
  unfold dimacsBound at hmaxv hscr hwcap har
  unfold Func.wp full_walk_collect_m7_body
  c0_hsteps_nogrp
  · exact hQ (0#64, ()) s m rfl hlen ⟨rfl, rfl⟩ hm
  · exact hQ (0#64, ()) s m rfl hlen ⟨rfl, rfl⟩ hm
  · exact hQ (0#64, ()) s m rfl hlen ⟨rfl, rfl⟩ hm
  · have hcv_pos : 0 < s.core.cur_vars := by
      have hlt : s.core.cur_vars < 2 ^ 64 := by have := hlen.core_ok.cur_vars_le; omega
      have hne : BitVec.ofNat 64 s.core.cur_vars ≠ 0#64 := by c0_bound
      exact Nat.pos_of_ne_zero fun h0 => hne (by simp [h0])
    have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
    have h2300 : 2300 ≤ c.scratch_cap := by
      have hlt : c.scratch_cap < 2 ^ 64 := by omega
      have hc1 : ¬ (BitVec.ofNat 64 c.scratch_cap).toNat < (2300#64 : BitVec 64).toNat := by
        c0_bound
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at hc1; exact Nat.le_of_not_lt hc1
    have h2v : ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
      have hlt : 2 * (BitVec.ofNat 64 s.core.cur_vars).toNat < 2 ^ 64 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      rw [bv64_shl1_toNat_lt hlt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine wp_loop_safety_slice (fullSafetySlice c) s R (fun _ => True) trivial
      (fun st (ncl, tot, full, lit0, ()) => FullExtScratchPres s st ∧
        ncl.toNat ≤ c.scratch_cap ∧ tot.toNat ≤ c.scratch_cap ∧
        lit0.toNat ≤ 2 * s.core.cur_vars ∧
        (full = false → 2200 + 5 * ncl.toNat + tot.toNat ≤ c.scratch_cap))
      (fun (_ncl, _tot, _full, lit0, ()) => 2 * s.core.cur_vars - lit0.toNat) ?_ ?_
    · intro Jl1 hJl1; c0_hsteps
      exact hJl1 s (0#64, 0#64, false, 0#64, ()) m hm rfl hlen
        ⟨⟨rfl, rfl⟩, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, fun _ => by simp; omega⟩
    · rintro Jl1 st1 ⟨ncl, tot, full, lit0, ⟨⟩⟩ m1 hcore1 hlen1 _
        ⟨hext1, hncl1, htot1, hlit0_le, hbd1⟩ hm1 hJl1
      rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore1 hlen1 hm1 hJl1
      have hval_len := hlen1.core_ok.vals_len
      have hwv_len := hlen1.core_ok.wvec_len
      have hws_len := hlen1.core_ok.wstk_len_arr
      have hwl_eq : st1.core.wlen = s.core.wlen := congrArg FullCoreState.wlen hcore1
      have hwl_le := hlen1.core_ok.wlen_le
      have hsb_len := hlen1.scratch_ok.scratch_buf_len
      refine wp_join_safety_slice (ts := []) (fullSafetySlice c) st1 R (fun _ => True) trivial
        (fun st' () => st' = st1) ?_ ?_
      · rintro Jex st' ⟨⟩ m' _ hlen' _ hst' hm'
        subst st'; rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hlen' hm'
        refine wp_join_safety_slice (ts := [i64, i64, .bool, i64]) (fullSafetySlice c) st1 R
          (fun _ => True) trivial
          (fun st (ncl', tot', full', _cref', ()) => FullExtScratchPres s st ∧
            ncl'.toNat ≤ c.scratch_cap ∧ tot'.toNat ≤ c.scratch_cap) ?_ ?_
        · rintro J2 st2 ⟨ncl2, tot2, full2, _cref2, ⟨⟩⟩ m2 hcore2 hlen2 _ ⟨hext2, _, _⟩ hm2
          rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore2 hlen2 hm2
          c0_hsteps_nogrp
          · exact hQ (0#64, ()) st2 m2 (hcore1.trans hcore2) hlen2 hext2 hm2
          · exact hQ _ st2 m2 (hcore1.trans hcore2) hlen2 hext2 hm2
        · intro J2 hJ2
          refine wp_loop_safety_slice (fullSafetySlice c) st1 R (fun _ => True) trivial
            (fun st (ncl', tot', full', cref, ()) => FullExtScratchPres s st ∧
              ncl'.toNat ≤ c.scratch_cap ∧ tot'.toNat ≤ c.scratch_cap ∧ cref.toNat < 2 ^ 32 ∧
              (full' = false → 2200 + 5 * ncl'.toNat + tot'.toNat ≤ c.scratch_cap))
            (fun (_ncl', _tot', _full', cref, ()) => s.core.arena_len - cref.toNat) ?_ ?_
          · intro Jl2 hJl2; c0_hsteps
            exact hJl2 st1 (ncl, tot, full, 0#64, ()) m' hm' rfl hlen'
              ⟨hext1, hncl1, htot1, by decide, hbd1⟩
          · rintro Jl2 st2 ⟨ncl2, tot2, full2, cref, ⟨⟩⟩ m2 hcore2 hlen2 _
              ⟨hext2, hncl2, htot2, hcref32, hbd2⟩ hm2 hJl2
            rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore2 hlen2 hm2 hJl2
            have hal_eq : st2.core.arena_len = s.core.arena_len :=
              (congrArg FullCoreState.arena_len hcore2).trans
                (congrArg FullCoreState.arena_len hcore1)
            have har_len := hlen2.core_ok.arena_len_arr
            have hval_len := hlen2.core_ok.vals_len
            have hsb_len := hlen2.scratch_ok.scratch_buf_len
            have hal_le := hlen2.core_ok.arena_len_le
            c0_hsteps_nogrp
            · exact hJ2 st2 (ncl2, tot2, full2, cref, ()) m2 hm2 hcore2 hlen2 ⟨hext2, hncl2, htot2⟩
            · have hcr3_le : cref.toNat + 3 ≤ s.core.arena_len := by
                have hc : ¬ (BitVec.ofNat 64 st2.core.arena_len).toNat <
                    (cref + 3#64).toNat := by c0_bound
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_add,
                  BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc
                omega
              have hfull_f : full2 = false := by cases full2 <;> simp_all
              have hbd2' := hbd2 hfull_f
              have hcr0_lt : cref.toNat < st2.core.arena.length := by rw [har_len]; omega
              have hcr2_lt : (cref + 2#64).toNat < st2.core.arena.length := by
                rw [har_len, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
              refine wp_join_safety_slice (ts := [i64, i64, .bool]) (fullSafetySlice c) st2 R
                (fun _ => True) trivial
                (fun st3 (ncl3, tot3, full3, ()) => FullExtScratchPres s st3 ∧
                  ncl3.toNat ≤ c.scratch_cap ∧ tot3.toNat ≤ c.scratch_cap ∧
                  (full3 = false → 2200 + 5 * ncl3.toNat + tot3.toNat ≤ c.scratch_cap)) ?_ ?_
              · rintro Jar st3 ⟨ncl3, tot3, full3, ⟨⟩⟩ m3 hcore3 hlen3 _
                  ⟨hext3, hncl3, htot3, hbd3⟩ hm3
                rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore3 hlen3 hm3
                c0_hsteps_nogrp
                refine walk_call_arena_next hArena rfl hlen3 hm3 ?_
                c0_hsteps_nogrp
                · exact hJ2 st3 (ncl3, tot3, full3, cref, ()) m3 hm3
                    (hcore2.trans hcore3) hlen3 ⟨hext3, hncl3, htot3⟩
                · exact hJl2 st3 (ncl3, tot3, full3, _, ()) m3 hm3 (by
                    dsimp only; rw [bv32_lit_toNat_mod64, BitVec.toNat_ofNat]; omega)
                    hcore3 hlen3 ⟨hext3, hncl3, htot3, by
                      rw [bv32_lit_toNat_mod64]; exact BitVec.isLt _, hbd3⟩
              · intro Jar hJar; dsimp only [fullSafetySlice] at hJar; c0_hsteps_nogrp
                · let csz := st2.core.arena[(cref + 2#64).toNat]'hcr2_lt
                  have hcsz_ge3 : 3 ≤ csz.toNat := by dsimp only [csz]; c0_bound
                  have hcsz_le : csz.toNat ≤ s.core.arena_len := by
                    have hz := bv32_lit_toNat_mod64 csz
                    dsimp only [csz] at hz ⊢; rw [← hal_eq]; c0_bound
                  have hcsz_end : cref.toNat + 3 + csz.toNat ≤ s.core.arena_len := by
                    have hz := bv32_lit_toNat_mod64 csz
                    dsimp only [csz] at hz ⊢; rw [← hal_eq]; c0_bound
                  refine wp_join_group (ts := [.bool, .bool, i32]) (fun _ m3 => m2 = m3) ?_ ?_
                  · rintro Jbrk ⟨rsat, has_un, _jo, ⟨⟩⟩ _ rfl; rw [Blocks.get_here]
                    c0_hfast_nobound <;> first
                      | exact hJar st2 (ncl2, tot2, full2, ()) m2 hm2 rfl hlen2
                          ⟨hext2, hncl2, htot2, hbd2⟩
                      | exact hJar st2 (ncl2, tot2, true, ()) m2 hm2 rfl hlen2
                          ⟨hext2, hncl2, htot2, fun hf => by cases hf⟩
                      | ( have hc2 : (cref + 2#64).toNat = (cref.toNat + 2) % 2 ^ 64 := by
                            rw [BitVec.toNat_add, BitVec.toNat_ofNat]
                          have h5_new : 2200 + 5 * (ncl2.toNat + 1) + tot2.toNat + csz.toNat ≤
                              c.scratch_cap := by
                            have hz := bv32_lit_toNat_mod64 csz
                            dsimp only [csz] at hz ⊢; simp only [hc2] at hz ⊢; c0_bound
                          have hnew := bv64_2200_5_le_bound hscr hncl2 htot2 csz.isLt
                            (by c0_bound) (by omega) (by omega)
                          have h1_lt : (2200#64 + (ncl2 <<< (1 : Nat))).toNat <
                              st2.scratch.scratch_buf.length := by
                            rw [hsb_len, bv64_2200_shl1 (by omega)]; omega
                          have h2_lt : (2200#64 + (ncl2 <<< (1 : Nat)) + 1#64).toNat <
                              st2.scratch.scratch_buf.length := by
                            rw [hsb_len, bv64_2200_shl1_1 (by omega)]; omega
                          c0_hfast
                          refine hJar _ (ncl2 + 1#64, tot2 + csz.setWidth 64, full2, ()) _
                            (by assumption) ?_ ?_ ?_
                          · rfl
                          · exact ⟨hlen2.core_ok, { hlen2.scratch_ok with
                              scratch_buf_len := by simp [hsb_len] }⟩
                          · have hz := bv32_lit_toNat_mod64 csz
                            exact ⟨⟨hext2.1, hext2.2⟩,
                              by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega,
                              by rw [BitVec.toNat_add, hz]; omega,
                              fun _ => by rw [BitVec.toNat_add, BitVec.toNat_add,
                                BitVec.toNat_ofNat, hz]; omega⟩ )
                  · intro Jbrk hJbrk
                    refine wp_loop_mem1 (ts := [.bool, i32])
                      (fun (has_un, j, ()) => j.toNat ≤ csz.toNat)
                      (fun (_, j, ()) => csz.toNat - j.toNat) ?_ ?_
                    · intro Jj hJj; c0_hfast
                      exact hJj (false, 0#32, ()) (Nat.zero_le _)
                    · rintro Jj ⟨has_un, j, ⟨⟩⟩ hj_le hJj
                      rw [Blocks.get_here]; c0_hfast_nogrp
                      · have hj_lt : j.toNat < csz.toNat := by c0_bound
                        have hlit_ar : (cref + 3#64 + j.setWidth 64).toNat <
                            st2.core.arena.length := by
                          have hz := bv32_lit_toNat_mod64 j
                          rw [har_len, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, hz]
                          omega
                        c0_hfast_nogrp
                        refine wp_join_group (ts := [.bool, .bool]) (fun _ m3 => m2 = m3) ?_ ?_
                        · rintro Js ⟨_rs, hu, ⟨⟩⟩ _ rfl; rw [Blocks.get_here]
                          c0_hsteps_nogrp_nobound
                          exact hJj (hu, j + 1#32, ())
                            (bv32_sub_succ_lt hj_lt (by omega))
                            (bv32_succ_le_of_lt hj_lt (by omega))
                        · intro Js hJs
                          clear hQ hJar hJl2 hm hm1
                          c0_hfast <;> first
                            | exact hJbrk (true, has_un, j, ()) m2 rfl
                            | exact hJs (false, true, ()) m2 rfl
                            | exact hJs (false, has_un, ()) m2 rfl
                      · exact hJbrk (false, has_un, j, ()) m2 rfl
                all_goals
                  exact hJar st2 (ncl2, tot2, full2, ()) m2 hm2 rfl hlen2
                    ⟨hext2, hncl2, htot2, hbd2⟩
            · exact hJ2 st2 (ncl2, tot2, full2, cref, ()) m2 hm2 hcore2 hlen2 ⟨hext2, hncl2, htot2⟩
      · intro Jex hJex; c0_hfast_nogrp
        · exact hJex st1 () m1 hm1 rfl hlen1 rfl
        · have hlit0_lt : lit0.toNat < 2 * s.core.cur_vars := by c0_bound
          have hfull_f : full = false := by
            clear hm hm1 hQ hJl1 hlen1 hcore1 hlen
            cases full <;> simp_all
          have hbd1' := hbd1 hfull_f
          have hlit_val : lit0.toNat < st1.core.vals.length := by rw [hval_len]; omega
          refine wp_join_safety_slice (ts := [i64, i64, .bool]) (fullSafetySlice c) st1 R
            (fun _ => True) trivial
            (fun st2 (ncl2, tot2, full2, ()) => FullExtScratchPres s st2 ∧
              ncl2.toNat ≤ c.scratch_cap ∧ tot2.toNat ≤ c.scratch_cap ∧
              (full2 = false → 2200 + 5 * ncl2.toNat + tot2.toNat ≤ c.scratch_cap)) ?_ ?_
          · rintro Jn st2 ⟨ncl2, tot2, full2, ⟨⟩⟩ m2 hcore2 hlen2 _
              ⟨hext2, hncl2, htot2, hbd2⟩ hm2
            rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore2 hlen2 hm2
            c0_hfast
            refine hJl1 st2 (ncl2, tot2, full2, lit0 + 1#64, ()) m2 hm2 (by
              dsimp only; rw [bv64_succ_toNat hlit0_lt (by omega)]; omega)
              hcore2 hlen2 ⟨hext2, hncl2, htot2, by
                rw [bv64_succ_toNat hlit0_lt (by omega)]; omega, hbd2⟩
          · intro Jn hJn; c0_hfast_nogrp
            · have hwv0 : (lit0 <<< (1 : Nat)).toNat < st1.core.wvec.length := by
                rw [hwv_len, bv64_shl1_toNat_lt (by omega)]; omega
              have hwv1 : ((lit0 <<< (1 : Nat)) + 1#64).toNat < st1.core.wvec.length := by
                rw [hwv_len, BitVec.toNat_add, bv64_shl1_toNat_lt (by omega)]
                simp; omega
              have hwv0' : (lit0 <<< (1 : BitVec 64)).toNat < st1.core.wvec.length := by
                rw [bv64_shl_one]; exact hwv0
              have hwv1' : ((lit0 <<< (1 : BitVec 64)) + (1 : BitVec 64)).toNat <
                  st1.core.wvec.length := by
                rw [bv64_shl_one]; exact hwv1
              c0_hfast_nogrp
              let off := st1.core.wvec[(lit0 <<< (1 : Nat)).toNat]'hwv0
              let sz := st1.core.wvec[((lit0 <<< (1 : Nat)) + 1#64).toNat]'hwv1
              refine wp_join_safety_slice (ts := [i64, i64, .bool]) (fullSafetySlice c) st1 R
                (fun _ => True) trivial
                (fun st2 (ncl2, tot2, full2, ()) => FullExtScratchPres s st2 ∧
                  ncl2.toNat ≤ c.scratch_cap ∧ tot2.toNat ≤ c.scratch_cap ∧
                  (full2 = false → 2200 + 5 * ncl2.toNat + tot2.toNat ≤ c.scratch_cap)) ?_ ?_
              · rintro Jwk st2 ⟨ncl2, tot2, full2, ⟨⟩⟩ m2 hcore2 hlen2 _
                  ⟨hext2, hncl2, htot2, hbd2⟩ hm2
                rw [Blocks.get_here]; c0_hsteps
                exact hJn st2 (ncl2, tot2, full2, ()) m2 hm2 hcore2 hlen2
                  ⟨hext2, hncl2, htot2, hbd2⟩
              · intro Jwk hJwk; c0_hfast_nobound
                · have hoff_le : off.toNat ≤ s.core.wlen := by
                    clear hQ hJl1 hm hm1 hJn hJwk hcore1 hlen1 hlen
                    have hz := bv32_lit_toNat_mod64 off
                    dsimp only [off] at hz ⊢; rw [← hwl_eq]; c0_bound
                  have hsz_le : off.toNat + sz.toNat ≤ s.core.wlen := by
                    clear hQ hJl1 hm hm1 hJn hJwk hcore1 hlen1 hlen
                    have hz1 := bv32_lit_toNat_mod64 off
                    have hz2 := bv32_lit_toNat_mod64 sz
                    have hoff_lt := off.isLt
                    have hsb1 : (BitVec.ofNat 64 st1.core.wlen - off.setWidth 64).toNat =
                        st1.core.wlen - off.toNat := by
                      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, hz1]; omega
                    have hc1 : ¬ (BitVec.ofNat 64 st1.core.wlen - off.setWidth 64).toNat <
                        sz.toNat := by dsimp only [off, sz]; c0_bound
                    rw [hsb1] at hc1; omega
                  refine wp_loop_safety_slice (fullSafetySlice c) st1 R (fun _ => True) trivial
                    (fun stk (nk, tk, fk, k, ()) => FullExtScratchPres s stk ∧
                      nk.toNat ≤ c.scratch_cap ∧ tk.toNat ≤ c.scratch_cap ∧
                      k.toNat ≤ off.toNat + sz.toNat ∧
                      (fk = false → 2200 + 5 * nk.toNat + tk.toNat ≤ c.scratch_cap))
                    (fun (_, _, _, k, ()) => off.toNat + sz.toNat - k.toNat) ?_ ?_
                  · intro Jk hJk; c0_hfast
                    exact hJk st1 (ncl, tot, full, off.setWidth 64, ()) m1 hm1 rfl hlen1
                      ⟨hext1, hncl1, htot1, by
                        have hz := bv32_lit_toNat_mod64 off; omega, hbd1⟩
                  · rintro Jk stk ⟨nk, tk, fk, k, ⟨⟩⟩ mk hcorek hlenk _
                      ⟨hextk, hnk, htk, hk_le, hbdk⟩ hmk hJk
                    rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcorek hlenk hmk hJk
                    have hvalk := hlenk.core_ok.vals_len
                    have hsbk := hlenk.scratch_ok.scratch_buf_len
                    have hwsk := hlenk.core_ok.wstk_len_arr
                    c0_hfast_nogrp
                    · exact hJwk stk (nk, tk, fk, ()) mk hmk hcorek hlenk ⟨hextk, hnk, htk, hbdk⟩
                    · have hsh0 : (lit0 <<< (1 : Nat)).toNat = 2 * lit0.toNat % 2 ^ 64 := by
                        rw [bv64_shl1_toNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                      have hsh1 : ((lit0 <<< (1 : Nat)) + 1#64).toNat =
                          (2 * lit0.toNat + 1) % 2 ^ 64 := by
                        rw [BitVec.toNat_add, BitVec.toNat_ofNat, bv64_shl1_toNat_lt (by omega)]
                      have hk_lt : k.toNat < off.toNat + sz.toNat := by
                        have h1 : BitVec.toNat (1 : BitVec 64) = 1 := rfl
                        dsimp only [off, sz]
                        simp only [hsh0, hsh1, h1] at *; omega
                      have hk_ws : k.toNat < stk.core.wstk.length := by rw [hwsk]; omega
                      have hfk_f : fk = false := by
                        clear hmk hJk hJl1 hm hm1 hQ; cases fk <;> simp_all
                      have hbdk' := hbdk hfk_f
                      have hlit0_valk : lit0.toNat < stk.core.vals.length := by rw [hvalk]; omega
                      have hk1_nat : (k + 1#64).toNat = k.toNat + 1 :=
                        bv64_succ_toNat hk_lt (by omega)
                      have hJk_true : Jk (nk, tk, true, k + 1#64, ()) mk :=
                        hJk stk _ mk hmk (by dsimp only; rw [hk1_nat]; omega) rfl hlenk
                          ⟨hextk, hnk, htk, by rw [hk1_nat]; omega, fun hf => by cases hf⟩
                      have hJk_skip : Jk (nk, tk, fk, k + 1#64, ()) mk :=
                        hJk stk _ mk hmk (by dsimp only; rw [hk1_nat]; omega) rfl hlenk
                          ⟨hextk, hnk, htk, by rw [hk1_nat]; omega, hbdk⟩
                      c0_hfast_nobound
                      · have hlit1_val : (stk.core.wstk[k.toNat]'hk_ws &&&
                            (2147483647 : BitVec 32)).toNat < stk.core.vals.length := by
                          clear hQ hJl1 hm hm1 hJn hJwk hcore1 hlen1 hlen hmk hJk hJk_true hJk_skip
                          have hz := bv32_lit_toNat_mod64
                            (stk.core.wstk[k.toNat]'hk_ws &&& (2147483647 : BitVec 32))
                          rw [hvalk]; c0_bound
                        c0_hfast_nogrp
                        · refine wp_join_group (ts := []) (fun _ m' => mk = m') ?_ ?_
                          · rintro Jor ⟨⟩ _ rfl; rw [Blocks.get_here]
                            c0_hfast_nobound
                            · exact hJk_true
                            · exact hJk_true
                            · exact hJk_true
                            · have hnew := walk_collect_bin_bounds hscr hnk htk
                                (by assumption) (by assumption) (by assumption)
                              have h1_lt : (2200#64 + (nk <<< (1 : Nat))).toNat <
                                  stk.scratch.scratch_buf.length := by
                                rw [hsbk, bv64_2200_shl1 (by omega)]; omega
                              have h2_lt : (2200#64 + (nk <<< (1 : Nat)) + 1#64).toNat <
                                  stk.scratch.scratch_buf.length := by
                                rw [hsbk, bv64_2200_shl1_1 (by omega)]; omega
                              c0_hfast
                              refine hJk _ (nk + 1#64, tk + 2#64, fk, k + 1#64, ()) _
                                (by assumption) ?_ ?_ ?_ ?_
                              · dsimp only; omega
                              · rfl
                              · exact ⟨hlenk.core_ok, { hlenk.scratch_ok with
                                  scratch_buf_len := by simp [hsbk] }⟩
                              · exact walk_collect_push_inv ⟨hextk.1, hextk.2⟩ hscr hnew.1 hnew.2.1
                                  hnew.2.2.2 hk1_nat (by omega)
                          · intro Jor hJor; c0_hfast_nobound
                            · exact hJor () mk rfl
                            · exact hJor () mk rfl
                            · exact hJk_skip
                        · exact hJk_skip
                      all_goals first
                        | exact hJk_skip
                        | ( have hk1_lt : (k + 1#64).toNat < off.toNat + sz.toNat := by
                              rw [hk1_nat]
                              refine walk_collect_k1_lt ?_ hk_lt
                              dsimp only [off, sz]; simp only [hsh0, hsh1]; exact hc
                            have hk2_le : k.toNat + 2 ≤ off.toNat + sz.toNat := by
                              rw [hk1_nat] at hk1_lt; exact hk1_lt
                            have hk2_nat : (k + 1#64 + 1#64).toNat = k.toNat + 2 :=
                              bv64_add2_toNat (n := off.toNat + sz.toNat) hk2_le (by omega)
                            exact hJk stk (nk, tk, fk, k + 1#64 + 1#64, ()) mk hmk
                              (by dsimp only; rw [hk2_nat]
                                  exact Nat.sub_lt_sub_left hk_lt (by omega))
                              rfl hlenk ⟨hextk, hnk, htk, by rw [hk2_nat]; exact hk2_le, hbdk⟩ )
                    all_goals
                      exact hJwk stk (nk, tk, fk, ()) mk hmk hcorek hlenk ⟨hextk, hnk, htk, hbdk⟩
                all_goals
                  exact hJwk st1 (ncl, tot, full, ()) m1 hm1 rfl hlen1 ⟨hext1, hncl1, htot1, hbd1⟩
            · exact hJn st1 (ncl, tot, full, ()) m1 hm1 rfl hlen1 ⟨hext1, hncl1, htot1, hbd1⟩
        · exact hJex st1 () m1 hm1 rfl hlen1 rfl

private theorem list_getElem?_set_ne_lt {xs : List (BitVec 32)} {i j : Nat} {v : BitVec 32}
    (hj : j < 2200) (hi : 2200 ≤ i) : (xs.set i v)[j]? = xs[j]? :=
  List.getElem?_set_ne (by omega)

private theorem bv64_sat_ge2200 (ncl cb : BitVec 64)
    (h : 2200 + 2 * ncl.toNat + cb.toNat < 2 ^ 64) :
    2200 ≤ (2200#64 + (ncl <<< (1 : Nat)) + cb).toNat := by
  rw [bv64_sat_idx h]; omega

private theorem bv64_upos_ge2200 (ncl cb : BitVec 64)
    (h : 2200 + 3 * ncl.toNat + cb.toNat < 2 ^ 64) :
    2200 ≤ (2200#64 + (ncl <<< (1 : Nat)) + ncl + cb).toNat := by
  rw [bv64_upos_idx h]; omega

private theorem bv64_unsat_ge2200 (ncl ulen : BitVec 64)
    (h : 2200 + 4 * ncl.toNat + ulen.toNat < 2 ^ 64) :
    2200 ≤ (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ulen).toNat := by
  rw [bv64_unsat_idx h]; omega

private theorem bv64_occ_ge2200 (ncl x : BitVec 64)
    (h : 2200 + 5 * ncl.toNat + x.toNat < 2 ^ 64) :
    2200 ≤ ((2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl) + x).toNat := by
  rw [bv64_occ_idx h]; omega

private theorem walkScrPrefixPres_sat_upos {s₀ st : FullState}
    (hpre : WalkScrPrefixPres s₀ st) {ncl cb : BitVec 64} {sc v : BitVec 32}
    (hbd : 2200 + 3 * ncl.toNat + cb.toNat < 2 ^ 64) :
    WalkScrPrefixPres s₀
      { st with scratch := { st.scratch with
        scratch_buf := (st.scratch.scratch_buf.set
          (2200#64 + (ncl <<< (1 : Nat)) + cb).toNat sc).set
          (2200#64 + (ncl <<< (1 : Nat)) + ncl + cb).toNat v } } :=
  fun j hj =>
    (list_getElem?_set_ne_lt hj (bv64_upos_ge2200 ncl cb hbd)).trans
      ((list_getElem?_set_ne_lt hj (bv64_sat_ge2200 ncl cb (by omega))).trans (hpre j hj))

private theorem walkScrPrefixPres_sat_upos_unsat {s₀ st : FullState}
    (hpre : WalkScrPrefixPres s₀ st) {ncl cb ulen : BitVec 64} {sc v1 v2 : BitVec 32}
    (hbd1 : 2200 + 3 * ncl.toNat + cb.toNat < 2 ^ 64)
    (hbd2 : 2200 + 4 * ncl.toNat + ulen.toNat < 2 ^ 64) :
    WalkScrPrefixPres s₀
      { st with scratch := { st.scratch with
        scratch_buf := ((st.scratch.scratch_buf.set
          (2200#64 + (ncl <<< (1 : Nat)) + cb).toNat sc).set
          (2200#64 + (ncl <<< (1 : Nat)) + ncl + cb).toNat v1).set
          (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ulen).toNat v2 } } :=
  fun j hj =>
    (list_getElem?_set_ne_lt hj (bv64_unsat_ge2200 ncl ulen hbd2)).trans
      (walkScrPrefixPres_sat_upos hpre hbd1 j hj)

private theorem bv64_occ_cnt_le {scap : Nat} {ncl off : BitVec 64} {cnt : BitVec 32}
    (hscr : scap < 2 ^ 28) (h5 : 2200 + 5 * ncl.toNat ≤ scap)
    (hoff : off.toNat ≤ scap - (2200 + 5 * ncl.toNat))
    (hc : ¬ (2 ^ 64 - off.toNat + (2 ^ 64 - (2200 + 2 * ncl.toNat + ncl.toNat + ncl.toNat +
      ncl.toNat) % 2 ^ 64 + scap)) % 2 ^ 64 < (cnt.setWidth 64).toNat) :
    off.toNat + (cnt.setWidth 64).toNat ≤ scap - (2200 + 5 * ncl.toNat) := by
  have hz := bv32_lit_toNat_mod64 cnt
  have hrem : (2 ^ 64 - off.toNat + (2 ^ 64 - (2200 + 2 * ncl.toNat + ncl.toNat + ncl.toNat +
      ncl.toNat) % 2 ^ 64 + scap)) % 2 ^ 64 = scap - (2200 + 5 * ncl.toNat) - off.toNat := by omega
  rw [hrem] at hc; omega

/-! ## 2. `full_walk_build_occ_m7` -/

theorem full_walk_build_occ_m7_wp (Γ : Env) :
    ∀ a m Q X, fullWalkBuildOccM7Spec a m Q X →
      Func.wp Γ full_walk_build_occ_m7_body a m Q X := by
  rintro ⟨h, ncl, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  have hmaxv := c.hmaxv; have hscr := c.hscr; have har := c.harena
  unfold dimacsBound at hmaxv hscr har
  unfold Func.wp full_walk_build_occ_m7_body
  have hret := hQ (0#64, ()) s m rfl hlen ⟨⟨rfl, rfl⟩, walkScrPrefixPres_refl s, Nat.zero_le _⟩ hm
  c0_hsteps_nogrp
  iterate 5 exact hret
  have hcv_pos : 0 < s.core.cur_vars := by
    have hlt : s.core.cur_vars < 2 ^ 64 := by have := hlen.core_ok.cur_vars_le; omega
    have hne : BitVec.ofNat 64 s.core.cur_vars ≠ 0#64 := by c0_bound
    exact Nat.pos_of_ne_zero fun h0 => hne (by simp [h0])
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
  have hncl_pos : 0 < ncl.toNat := by
    have hne : ncl ≠ 0#64 := by c0_bound
    exact Nat.pos_of_ne_zero fun h0 => hne (BitVec.eq_of_toNat_eq (by simp [h0]))
  have hncl_le : ncl.toNat ≤ c.scratch_cap := by c0_bound
  have h5ncl : 2200 + 5 * ncl.toNat ≤ c.scratch_cap := by
    have hc1 : ¬ (BitVec.ofNat 64 c.scratch_cap).toNat < (2200#64 + 5#64 * ncl).toNat := by
      c0_bound
    have hbv : (2200#64 + 5#64 * ncl).toNat = 2200 + 5 * ncl.toNat := by bv_omega
    rw [hbv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc1; omega
  have h2v : ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    have hlt : 2 * (BitVec.ofNat 64 s.core.cur_vars).toNat < 2 ^ 64 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    rw [bv64_shl1_toNat_lt hlt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hocc_cap := bv64_occ_cap_eq hscr h5ncl
  refine wp_loop_safety_slice (fullSafetySlice c) s R (fun _ => True) trivial
    (fun st1 (ulen, cb, ()) => FullExtScratchPres s st1 ∧ WalkScrPrefixPres s st1 ∧
      ulen.toNat ≤ ncl.toNat ∧ cb.toNat ≤ ncl.toNat)
    (fun (_ulen, cb, ()) => ncl.toNat - cb.toNat) ?_ ?_
  · intro J1 hJ1; c0_hsteps
    exact hJ1 s (0#64, 0#64, ()) m hm rfl hlen
      ⟨⟨rfl, rfl⟩, walkScrPrefixPres_refl s, Nat.zero_le _, Nat.zero_le _⟩
  · rintro J1 st1 ⟨ulen, cb, ⟨⟩⟩ m1 hcore1 hlen1 _ ⟨hext1, hpre1, hulen_le, hcb_le⟩ hm1 hJ1
    rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore1 hlen1 hm1 hJ1
    have hsb1 := hlen1.scratch_ok.scratch_buf_len; have hval1 := hlen1.core_ok.vals_len
    have hwv1 := hlen1.scratch_ok.walk_vals_len; have htrc1 := hlen1.scratch_ok.tarjan_reach_len
    have har1 := hlen1.core_ok.arena_len_arr; have hal_le1 := hlen1.core_ok.arena_len_le
    have hal_eq1 : st1.core.arena_len = s.core.arena_len :=
      congrArg FullCoreState.arena_len hcore1
    c0_hsteps_nogrp
    · have hcb_lt : cb.toNat < ncl.toNat := by c0_bound
      have hw0_lt : (2200#64 + (cb <<< (1 : Nat))).toNat < st1.scratch.scratch_buf.length := by
        rw [hsb1, bv64_2200_shl1 (by omega)]; omega
      have hw1_lt : (2200#64 + (cb <<< (1 : Nat)) + 1#64).toNat <
          st1.scratch.scratch_buf.length := by
        rw [hsb1, bv64_2200_shl1_1 (by omega)]; omega
      let w0 := st1.scratch.scratch_buf[(2200#64 + (cb <<< (1 : Nat))).toNat]'hw0_lt
      let w1 := st1.scratch.scratch_buf[(2200#64 + (cb <<< (1 : Nat)) + 1#64).toNat]'hw1_lt
      refine wp_join_safety_slice (ts := [i32]) (fullSafetySlice c) st1 R
        (fun _ => True) trivial
        (fun st2 _ => FullExtScratchPres s st2 ∧ WalkScrPrefixPres s st2) ?_ ?_
      · rintro Jsc st2 ⟨sc, ⟨⟩⟩ m2 hcore2 hlen2 _ ⟨hext2, hpre2⟩ hm2
        rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore2 hlen2 hm2
        have hsb2 := hlen2.scratch_ok.scratch_buf_len
        have hsat_lt : (2200#64 + (ncl <<< (1 : Nat)) + cb).toNat <
            st2.scratch.scratch_buf.length := by
          rw [hsb2, bv64_sat_idx (by omega)]; omega
        c0_hsteps_nogrp
        let sb2 := st2.scratch.scratch_buf.set (2200#64 + (ncl <<< (1 : Nat)) + cb).toNat sc
        have hupos_lt : (2200#64 + (ncl <<< (1 : Nat)) + ncl + cb).toNat < sb2.length := by
          rw [List.length_set, hsb2, bv64_upos_idx (by omega)]; omega
        have hsb2_upos : (sb2.set (2200#64 + (ncl <<< (1 : Nat)) + ncl + cb).toNat
            (ulen.setWidth 32)).length = c.scratch_cap := by
          rw [List.length_set, List.length_set, hsb2]
        have huns_idx : (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ulen).toNat =
            2200 + 4 * ncl.toNat + ulen.toNat := bv64_unsat_idx (by omega)
        c0_hfast <;> first
          | ( refine hJ1 _ (ulen + 1#64, cb + 1#64, ()) _ (by assumption)
                (bv64_sub_succ_lt hcb_lt (by omega)) ?_ ?_ ?_
              · exact hcore2
              · exact ⟨hlen2.core_ok, { hlen2.scratch_ok with scratch_buf_len := by simp [hsb2] }⟩
              · refine ⟨⟨hext2.1, hext2.2⟩,
                  walkScrPrefixPres_sat_upos_unsat hpre2 (by omega) (by omega),
                  by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega,
                  bv64_succ_le_of_lt hcb_lt (by omega)⟩ )
          | ( refine hJ1 _ (ulen, cb + 1#64, ()) _ (by assumption)
                (bv64_sub_succ_lt hcb_lt (by omega)) ?_ ?_ ?_
              · exact hcore2
              · exact ⟨hlen2.core_ok, { hlen2.scratch_ok with scratch_buf_len := by simp [hsb2] }⟩
              · refine ⟨⟨hext2.1, hext2.2⟩,
                  walkScrPrefixPres_sat_upos hpre2 (by omega), hulen_le,
                  bv64_succ_le_of_lt hcb_lt (by omega)⟩ )
      · intro Jsc hJsc; c0_hsteps_nogrp
        · refine wp_join_safety_slice (ts := [i32]) (fullSafetySlice c) st1 R
            (fun _ => True) trivial
            (fun st2 _ => FullExtScratchPres s st2 ∧ WalkScrPrefixPres s st2) ?_ ?_
          · rintro Jl0 st2 ⟨sc1, ⟨⟩⟩ m2 hcore2 hlen2 _ ⟨hext2, hpre2⟩ hm2
            rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore2 hlen2 hm2
            have htrc2 := hlen2.scratch_ok.tarjan_reach_len
            c0_hstep; c0_hsplit
            · have hl1_lt : w1.toNat < 2 * s.core.cur_vars := by
                have hz := bv32_lit_toNat_mod64 w1; dsimp only [w1] at hz ⊢; c0_bound
              obtain ⟨hl1_v, hl1_wv, _, _, hl1_trc⟩ :=
                walk_lit_bds (hcore1.trans hcore2) hcv_le hlen2 hl1_lt
              c0_hfast <;> first
                | ( refine hJsc _ (_, ()) _ (by assumption) ?_ ?_ ?_
                    · exact hcore2
                    · exact ⟨hlen2.core_ok, { hlen2.scratch_ok with
                        tarjan_reach_len := by simp [htrc2] }⟩
                    · exact ⟨⟨hext2.1, hext2.2⟩, hpre2⟩ )
                | exact hJsc st2 (sc1, ()) _ (by assumption) hcore2 hlen2 ⟨hext2, hpre2⟩
            all_goals
              c0_hfast; exact hJsc st2 (sc1, ()) _ (by assumption) hcore2 hlen2 ⟨hext2, hpre2⟩
          · intro Jl0 hJl0; c0_hsplit
            · have hl0_lt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars := by
                have h1 : (w0 &&& (2147483647 : BitVec 32)).toNat < 2 * s.core.cur_vars := by
                  have hz := bv32_lit_toNat_mod64 (w0 &&& (2147483647 : BitVec 32))
                  dsimp only [w0] at hz ⊢; c0_bound
                exact h1
              obtain ⟨hl0_v, hl0_wv, _, _, hl0_trc⟩ := walk_lit_bds hcore1 hcv_le hlen1 hl0_lt
              c0_hfast <;> first
                | ( refine hJl0 _ (_, ()) _ (by assumption) ?_ ?_ ?_
                    · rfl
                    · exact ⟨hlen1.core_ok, { hlen1.scratch_ok with
                        tarjan_reach_len := by simp [htrc1] }⟩
                    · exact ⟨⟨hext1.1, hext1.2⟩, hpre1⟩ )
                | exact hJl0 st1 (0#32, ()) _ (by assumption) rfl hlen1 ⟨hext1, hpre1⟩
            all_goals
              c0_hfast; exact hJl0 st1 (0#32, ()) _ (by assumption) rfl hlen1 ⟨hext1, hpre1⟩
        · refine wp_join_safety_slice (ts := [i32]) (fullSafetySlice c) st1 R
            (fun _ => True) trivial
            (fun st2 _ => FullExtScratchPres s st2 ∧ WalkScrPrefixPres s st2) ?_ ?_
          · rintro Js st2 ⟨sc, ⟨⟩⟩ m2 hcore2 hlen2 _ ⟨hext2, hpre2⟩ hm2
            rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore2 hlen2 hm2
            c0_hfast; exact hJsc st2 (sc, ()) m2 hm2 hcore2 hlen2 ⟨hext2, hpre2⟩
          · intro Js hJs; dsimp only [fullSafetySlice] at hJs; c0_hsteps_nogrp
            · have hw0_end : w0.toNat + 3 ≤ s.core.arena_len := by
                have hz := bv32_lit_toNat_mod64 w0; dsimp only [w0] at hz ⊢
                rw [← hal_eq1]; c0_bound
              have hcsz_lt : (w0.setWidth 64 + 2#64).toNat < st1.core.arena.length := by
                have hz := bv32_lit_toNat_mod64 w0
                rw [har1, BitVec.toNat_add, BitVec.toNat_ofNat, hz]; omega
              c0_hsteps_nogrp
              refine wp_join_safety_slice (ts := [i32]) (fullSafetySlice c) st1 R
                (fun _ => True) trivial
                (fun st2 _ => FullExtScratchPres s st2 ∧ WalkScrPrefixPres s st2) ?_ ?_
              · rintro Js1 st2 ⟨sc, ⟨⟩⟩ m2 hcore2 hlen2 _ ⟨hext2, hpre2⟩ hm2
                rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore2 hlen2 hm2
                c0_hfast; exact hJs st2 (sc, ()) m2 hm2 hcore2 hlen2 ⟨hext2, hpre2⟩
              · intro Js1 hJs1; dsimp only [fullSafetySlice] at hJs1; c0_hsteps_nogrp
                · let csz := st1.core.arena[(w0.setWidth 64 + 2#64).toNat]'hcsz_lt
                  have hcsz_end : w0.toNat + 3 + csz.toNat ≤ s.core.arena_len := by
                    have hz1 := bv32_lit_toNat_mod64 w0; have hz2 := bv32_lit_toNat_mod64 csz
                    dsimp only [csz, w0] at hz1 hz2 ⊢; rw [← hal_eq1]; c0_bound
                  refine wp_loop_safety_slice (fullSafetySlice c) st1 R (fun _ => True) trivial
                    (fun stj (sc, j, ()) => FullExtScratchPres s stj ∧
                      WalkScrPrefixPres s stj ∧ j.toNat ≤ csz.toNat)
                    (fun (_sc, j, ()) => csz.toNat - j.toNat) ?_ ?_
                  · intro Jj hJj; c0_hfast
                    exact hJj st1 (0#32, 0#32, ()) m1 hm1 rfl hlen1 ⟨hext1, hpre1, Nat.zero_le _⟩
                  · rintro Jj stj ⟨sc, j, ⟨⟩⟩ mj hcorej hlenj _ ⟨hextj, hprej, hj_le⟩ hmj hJj
                    rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcorej hlenj hmj hJj
                    have harj := hlenj.core_ok.arena_len_arr
                    have htrcj := hlenj.scratch_ok.tarjan_reach_len
                    c0_hsplit
                    · have hj_lt : j.toNat < csz.toNat := by dsimp only [csz, w0]; c0_bound
                      have hlit_ar : (w0.setWidth 64 + 3#64 + j.setWidth 64).toNat <
                          stj.core.arena.length := by
                        have hz1 := bv32_lit_toNat_mod64 w0; have hz2 := bv32_lit_toNat_mod64 j
                        rw [harj, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, hz1, hz2]
                        omega
                      c0_hstraight
                      refine wp_join_safety_slice (ts := [i32]) (fullSafetySlice c) stj R
                        (fun _ => True) trivial
                        (fun stj' _ => FullExtScratchPres s stj' ∧ WalkScrPrefixPres s stj') ?_ ?_
                      · rintro Jnext stj' ⟨sc', ⟨⟩⟩ mj' hcore' hlen' _ ⟨hext', hpre'⟩ hm'
                        rw [Blocks.get_here]; c0_hfast
                        exact hJj stj' (sc', j + 1#32, ()) mj' hm'
                          (bv32_sub_succ_lt hj_lt (by omega)) hcore' hlen'
                          ⟨hext', hpre', bv32_succ_le_of_lt hj_lt (by omega)⟩
                      · intro Jnext hJnext; dsimp only [fullSafetySlice] at hJnext
                        c0_hsplit
                        · have hlit_lt : (stj.core.arena[(w0.setWidth 64 + 3#64 +
                              j.setWidth 64).toNat]'hlit_ar).toNat < 2 * s.core.cur_vars := by
                            have hz := bv32_lit_toNat_mod64
                              (stj.core.arena[(w0.setWidth 64 + 3#64 +
                                j.setWidth 64).toNat]'hlit_ar)
                            dsimp only [w0] at hz ⊢; c0_bound
                          obtain ⟨hlit_v, hlit_wv, _, _, hlit_trc⟩ :=
                            walk_lit_bds (hcore1.trans hcorej) hcv_le hlenj hlit_lt
                          c0_hfast_nobound <;> first
                            | ( refine hJnext _ (_, ()) _ (by assumption) ?_ ?_ ?_
                                · rfl
                                · exact ⟨hlenj.core_ok, { hlenj.scratch_ok with
                                    tarjan_reach_len := by simp [htrcj] }⟩
                                · exact ⟨hextj, hprej⟩ )
                            | exact hJnext stj (sc, ()) mj hmj rfl hlenj ⟨hextj, hprej⟩
                        · exact hJnext stj (sc, ()) mj hmj rfl hlenj ⟨hextj, hprej⟩
                    · exact hJs1 stj (sc, ()) mj hmj hcorej hlenj ⟨hextj, hprej⟩
                all_goals exact hJs1 st1 (0#32, ()) m1 hm1 rfl hlen1 ⟨hext1, hpre1⟩
            · exact hJs st1 (0#32, ()) m1 hm1 rfl hlen1 ⟨hext1, hpre1⟩
    · refine wp_loop_safety_slice (fullSafetySlice c) st1 R (fun _ => True) trivial
        (fun st2 (off, l, ()) => FullExtScratchPres s st2 ∧ WalkScrPrefixPres s st2 ∧
          off.toNat ≤ c.scratch_cap - (2200 + 5 * ncl.toNat) ∧ l.toNat ≤ 2 * s.core.cur_vars)
        (fun (_off, l, ()) => 2 * s.core.cur_vars - l.toNat) ?_ ?_
      · intro J2 hJ2; c0_hfast
        exact hJ2 st1 (0#64, 0#64, ()) m1 hm1 rfl hlen1
          ⟨hext1, hpre1, Nat.zero_le _, Nat.zero_le _⟩
      · rintro J2 st2 ⟨off, l, ⟨⟩⟩ m2 hcore2 hlen2 _ ⟨hext2, hpre2, hoff, hl_le⟩ hm2 hJ2
        rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore2 hlen2 hm2 hJ2
        have htrc2 := hlen2.scratch_ok.tarjan_reach_len
        c0_hsteps_nogrp
        · have hl_lt : l.toNat < 2 * s.core.cur_vars := by c0_bound
          have hl_trc : l.toNat < st2.scratch.tarjan_reach.length := by rw [htrc2]; omega
          refine wp_join_safety_slice (ts := [i64]) (fullSafetySlice c) st2 R
            (fun _ => True) trivial (fun st3 (off', ()) => st3 = st2 ∧
              off'.toNat ≤ c.scratch_cap - (2200 + 5 * ncl.toNat)) ?_ ?_
          · rintro Joff st3 ⟨off', ⟨⟩⟩ m3 _ hlen3 _ ⟨hst3, hoff'⟩ hm3
            subst st3; rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hlen3 hm3
            refine wp_join_safety_slice (ts := [i64]) (fullSafetySlice c) st2 R
              (fun _ => True) trivial (fun st4 (cnt, ()) =>
                FullExtScratchPres s st4 ∧ WalkScrPrefixPres s st4 ∧
                off'.toNat + cnt.toNat ≤ c.scratch_cap - (2200 + 5 * ncl.toNat)) ?_ ?_
            · rintro Jcnt st4 ⟨cnt, ⟨⟩⟩ m4 hcore4 hlen4 _ ⟨hext4, hpre4, hsum⟩ hm4
              rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore4 hlen4 hm4
              have htmk4 := hlen4.scratch_ok.tarjan_mark_len
              have hws4 := hlen4.scratch_ok.wsort_len
              have hl_tmk : l.toNat < st4.scratch.tarjan_mark.length := by rw [htmk4]; omega
              have hl_ws : l.toNat < st4.scratch.wsort.length := by rw [hws4]; omega
              c0_hfast
              refine hJ2 _ (off' + cnt, l + 1#64, ()) _ (by assumption)
                (bv64_sub_succ_lt hl_lt (by omega)) ?_ ?_ ?_
              · exact hcore4
              · exact ⟨hlen4.core_ok, { hlen4.scratch_ok with
                  tarjan_mark_len := by simp [htmk4], wsort_len := by simp [hws4] }⟩
              · exact ⟨⟨hext4.1, hext4.2⟩, hpre4,
                  by rw [BitVec.toNat_add]; omega, bv64_succ_le_of_lt hl_lt (by omega)⟩
            · intro Jcnt hJcnt; c0_hsteps_nogrp
              · have hsum_le : off'.toNat + (BitVec.ofNat 64 c.scratch_cap -
                    (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl) - off').toNat ≤
                    c.scratch_cap - (2200 + 5 * ncl.toNat) := by
                  rw [bv64_occ_rem_eq hscr h5ncl hoff']; omega
                c0_hfast
                refine hJcnt _ (_, ()) _ (by assumption) ?_ ?_ ?_
                · rfl
                · exact ⟨hlen2.core_ok, { hlen2.scratch_ok with
                    tarjan_reach_len := by simp [htrc2] }⟩
                · exact ⟨hext2, hpre2, hsum_le⟩
              · exact hJcnt st2 (_, ()) m3 hm3 rfl hlen2
                  ⟨hext2, hpre2, bv64_occ_cnt_le hscr h5ncl hoff' (by assumption)⟩
          · intro Joff hJoff; c0_hsteps_nogrp
            all_goals first
              | exact hJoff st2 _ m2 hm2 rfl hlen2 ⟨rfl, by bv_omega⟩
              | exact hJoff st2 _ m2 hm2 rfl hlen2 ⟨rfl, hoff⟩
        · refine wp_loop_safety_slice (fullSafetySlice c) st2 R (fun _ => True) trivial
            (fun st3 (cb3, ()) => FullExtScratchPres s st3 ∧ WalkScrPrefixPres s st3 ∧
              cb3.toNat ≤ ncl.toNat)
            (fun (cb3, ()) => ncl.toNat - cb3.toNat) ?_ ?_
          · intro J3 hJ3; c0_hfast
            exact hJ3 st2 (0#64, ()) m2 hm2 rfl hlen2 ⟨hext2, hpre2, Nat.zero_le _⟩
          · rintro J3 st3 ⟨cb3, ⟨⟩⟩ m3 hcore3 hlen3 _ ⟨hext3, hpre3, hcb3_le⟩ hm3 hJ3
            rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore3 hlen3 hm3 hJ3
            have hsb3 := hlen3.scratch_ok.scratch_buf_len; have hval3 := hlen3.core_ok.vals_len
            have hws3 := hlen3.scratch_ok.wsort_len; have htmk3 := hlen3.scratch_ok.tarjan_mark_len
            have htrc3 := hlen3.scratch_ok.tarjan_reach_len
            have har3 := hlen3.core_ok.arena_len_arr
            have hal_eq3 : st3.core.arena_len = s.core.arena_len :=
              congrArg FullCoreState.arena_len (hcore1.trans (hcore2.trans hcore3))
            c0_hsteps_nogrp_nobound
            · have hcb3_lt : cb3.toNat < ncl.toNat := by c0_bound
              have hw0_lt : (2200#64 + (cb3 <<< (1 : Nat))).toNat <
                  st3.scratch.scratch_buf.length := by
                rw [hsb3, bv64_2200_shl1 (by omega)]; omega
              have hw1_lt : (2200#64 + (cb3 <<< (1 : Nat)) + 1#64).toNat <
                  st3.scratch.scratch_buf.length := by
                rw [hsb3, bv64_2200_shl1_1 (by omega)]; omega
              let w0 := st3.scratch.scratch_buf[(2200#64 + (cb3 <<< (1 : Nat))).toNat]'hw0_lt
              let w1 := st3.scratch.scratch_buf[(2200#64 + (cb3 <<< (1 : Nat)) + 1#64).toNat]'hw1_lt
              c0_hsteps_nogrp_nobound
              refine wp_join_safety_slice (ts := []) (fullSafetySlice c) st3 R
                (fun _ => True) trivial
                (fun st4 _ => FullExtScratchPres s st4 ∧ WalkScrPrefixPres s st4) ?_ ?_
              · rintro Jnx st4 ⟨⟩ m4 hcore4 hlen4 _ ⟨hext4, hpre4⟩ hm4
                rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore4 hlen4 hm4
                c0_hfast
                exact hJ3 st4 (cb3 + 1#64, ()) m4 hm4 (bv64_sub_succ_lt hcb3_lt (by omega))
                  hcore4 hlen4 ⟨hext4, hpre4, bv64_succ_le_of_lt hcb3_lt (by omega)⟩
              · intro Jnx hJnx; c0_hsteps_nogrp_nobound
                · refine wp_join_safety_slice (ts := []) (fullSafetySlice c) st3 R
                    (fun _ => True) trivial
                    (fun st4 _ => FullExtScratchPres s st4 ∧ WalkScrPrefixPres s st4) ?_ ?_
                  · rintro Jl0 st4 ⟨⟩ m4 hcore4 hlen4 _ ⟨hext4, hpre4⟩ hm4
                    rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore4 hlen4 hm4
                    have hsb4 := hlen4.scratch_ok.scratch_buf_len
                    have hws4 := hlen4.scratch_ok.wsort_len
                    refine wp_join_safety_slice (ts := []) (fullSafetySlice c) st4 R
                      (fun _ => True) trivial
                      (fun st5 _ => FullExtScratchPres s st5 ∧ WalkScrPrefixPres s st5) ?_ ?_
                    · rintro Js st5 ⟨⟩ m5 hcore5 hlen5 _ ⟨hext5, hpre5⟩ hm5
                      rw [Blocks.get_here]; c0_hfast
                      exact hJnx st5 () m5 hm5 (hcore4.trans hcore5) hlen5 ⟨hext5, hpre5⟩
                    · intro Js hJs; dsimp only [fullSafetySlice] at hJs; clear hQ hJ1 hJ2
                      c0_hsplit
                      · have hl1_lt : w1.toNat < 2 * s.core.cur_vars := by
                          have hz := bv32_lit_toNat_mod64 w1; dsimp only [w1] at hz ⊢; c0_bound
                        obtain ⟨hl1_v, _, hl1_ws, hl1_tmk, hl1_trc⟩ :=
                          walk_lit_bds (hcore1.trans (hcore2.trans (hcore3.trans hcore4)))
                            hcv_le hlen4 hl1_lt
                        c0_hfast_nobound
                        · have hocc_lt : ((2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl) +
                              (st4.scratch.wsort[w1.toNat]'hl1_ws).setWidth 64).toNat <
                              st4.scratch.scratch_buf.length := by
                            have hz := bv32_lit_toNat_mod64 (st4.scratch.wsort[w1.toNat]'hl1_ws)
                            dsimp only [w1] at hz ⊢; rw [hsb4]; c0_bound
                          c0_hfast_nobound
                          refine hJs _ () _ (by assumption) ?_ ?_ ?_
                          · rfl
                          · exact ⟨hlen4.core_ok, { hlen4.scratch_ok with
                              scratch_buf_len := by simp [hsb4], wsort_len := by simp [hws4] }⟩
                          · refine ⟨⟨hext4.1, hext4.2⟩, fun j hj => ?_⟩
                            exact (list_getElem?_set_ne_lt hj (bv64_occ_ge2200 ncl
                              ((st4.scratch.wsort[w1.toNat]'hl1_ws).setWidth 64)
                              (by rw [bv32_lit_toNat_mod64]; omega))).trans (hpre4 j hj)
                        all_goals exact hJs st4 () _ (by assumption) rfl hlen4 ⟨hext4, hpre4⟩
                      · exact hJs st4 () _ (by assumption) rfl hlen4 ⟨hext4, hpre4⟩
                  · intro Jl0 hJl0; dsimp only [fullSafetySlice] at hJl0; clear hQ hJ1 hJ2
                    c0_hsplit
                    · have hl0_lt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars := by
                        have h1 : (w0 &&& (2147483647 : BitVec 32)).toNat < 2 * s.core.cur_vars :=
                          by have hz := bv32_lit_toNat_mod64 (w0 &&& (2147483647 : BitVec 32))
                             dsimp only [w0] at hz ⊢; c0_bound
                        exact h1
                      obtain ⟨hl0_v, _, hl0_ws, hl0_tmk, hl0_trc⟩ :=
                        walk_lit_bds (hcore1.trans (hcore2.trans hcore3)) hcv_le hlen3 hl0_lt
                      c0_hfast_nobound
                      · have hocc_lt : ((2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl) +
                            (st3.scratch.wsort[(w0 &&& (2147483647 : BitVec 32)).toNat]'hl0_ws
                              ).setWidth 64).toNat < st3.scratch.scratch_buf.length := by
                          have hz := bv32_lit_toNat_mod64
                            (st3.scratch.wsort[(w0 &&& (2147483647 : BitVec 32)).toNat]'hl0_ws)
                          dsimp only [w0] at hz ⊢; rw [hsb3]; c0_bound
                        c0_hfast_nobound
                        refine hJl0 _ () _ (by assumption) ?_ ?_ ?_
                        · rfl
                        · exact ⟨hlen3.core_ok, { hlen3.scratch_ok with
                            scratch_buf_len := by simp [hsb3], wsort_len := by simp [hws3] }⟩
                        · refine ⟨⟨hext3.1, hext3.2⟩, fun j hj => ?_⟩
                          exact (list_getElem?_set_ne_lt hj (bv64_occ_ge2200 ncl
                            ((st3.scratch.wsort[(w0 &&& (2147483647 : BitVec 32)).toNat]'hl0_ws
                              ).setWidth 64)
                            (by rw [bv32_lit_toNat_mod64]; omega))).trans (hpre3 j hj)
                      all_goals exact hJl0 st3 () _ (by assumption) rfl hlen3 ⟨hext3, hpre3⟩
                    · exact hJl0 st3 () _ (by assumption) rfl hlen3 ⟨hext3, hpre3⟩
                · refine wp_join_safety_slice (ts := []) (fullSafetySlice c) st3 R
                    (fun _ => True) trivial
                    (fun st4 _ => FullExtScratchPres s st4 ∧ WalkScrPrefixPres s st4) ?_ ?_
                  · rintro Jnx2 st4 ⟨⟩ m4 hcore4 hlen4 _ ⟨hext4, hpre4⟩ hm4
                    rw [Blocks.get_here]; c0_hfast
                    exact hJnx st4 () m4 hm4 hcore4 hlen4 ⟨hext4, hpre4⟩
                  · intro Jnx2 hJnx2; dsimp only [fullSafetySlice] at hJnx2; c0_hfast_nogrp
                    · have hw0_end : w0.toNat + 3 ≤ s.core.arena_len := by
                        have hz := bv32_lit_toNat_mod64 w0; dsimp only [w0] at hz ⊢
                        rw [← hal_eq3]; c0_bound
                      have hcsz_lt : (w0.setWidth 64 + 2#64).toNat < st3.core.arena.length := by
                        have hz := bv32_lit_toNat_mod64 w0
                        rw [har3, BitVec.toNat_add, BitVec.toNat_ofNat, hz]; omega
                      c0_hfast_nogrp
                      refine wp_join_safety_slice (ts := []) (fullSafetySlice c) st3 R
                        (fun _ => True) trivial
                        (fun st4 _ => FullExtScratchPres s st4 ∧ WalkScrPrefixPres s st4) ?_ ?_
                      · rintro Jnx3 st4 ⟨⟩ m4 hcore4 hlen4 _ ⟨hext4, hpre4⟩ hm4
                        rw [Blocks.get_here]; c0_hfast
                        exact hJnx2 st4 () m4 hm4 hcore4 hlen4 ⟨hext4, hpre4⟩
                      · intro Jnx3 hJnx3; dsimp only [fullSafetySlice] at hJnx3; c0_hfast_nogrp
                        · let csz := st3.core.arena[(w0.setWidth 64 + 2#64).toNat]'hcsz_lt
                          have hcsz_end : w0.toNat + 3 + csz.toNat ≤ s.core.arena_len := by
                            have hz1 := bv32_lit_toNat_mod64 w0
                            have hz2 := bv32_lit_toNat_mod64 csz
                            dsimp only [csz, w0] at hz1 hz2 ⊢; rw [← hal_eq3]; c0_bound
                          refine wp_loop_safety_slice (fullSafetySlice c) st3 R
                            (fun _ => True) trivial
                            (fun stj (j, ()) => FullExtScratchPres s stj ∧
                              WalkScrPrefixPres s stj ∧ j.toNat ≤ csz.toNat)
                            (fun (j, ()) => csz.toNat - j.toNat) ?_ ?_
                          · intro Jj hJj; c0_hfast
                            exact hJj st3 (0#32, ()) m3 hm3 rfl hlen3 ⟨hext3, hpre3, Nat.zero_le _⟩
                          · rintro Jj stj ⟨j, ⟨⟩⟩ mj hcorej hlenj _ ⟨hextj, hprej, hj_le⟩ hmj hJj
                            rw [Blocks.get_here]
                            dsimp only [fullSafetySlice] at hcorej hlenj hmj hJj
                            have harj := hlenj.core_ok.arena_len_arr
                            have hsbj := hlenj.scratch_ok.scratch_buf_len
                            have hwsj := hlenj.scratch_ok.wsort_len
                            clear hQ hJ1 hJ2
                            c0_hsplit
                            · have hj_lt : j.toNat < csz.toNat := by dsimp only [csz, w0]; c0_bound
                              have hlit_ar : (w0.setWidth 64 + 3#64 + j.setWidth 64).toNat <
                                  stj.core.arena.length := by
                                have hz1 := bv32_lit_toNat_mod64 w0
                                have hz2 := bv32_lit_toNat_mod64 j
                                rw [harj, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
                                  hz1, hz2]; omega
                              c0_hstraight
                              refine wp_join_safety_slice (ts := []) (fullSafetySlice c) stj R
                                (fun _ => True) trivial
                                (fun stj' _ => FullExtScratchPres s stj' ∧ WalkScrPrefixPres s stj')
                                ?_ ?_
                              · rintro Jnext stj' ⟨⟩ mj' hcore' hlen' _ ⟨hext', hpre'⟩ hm'
                                rw [Blocks.get_here]; c0_hfast
                                exact hJj stj' (j + 1#32, ()) mj' hm'
                                  (bv32_sub_succ_lt hj_lt (by omega)) hcore' hlen'
                                  ⟨hext', hpre', bv32_succ_le_of_lt hj_lt (by omega)⟩
                              · intro Jnext hJnext; dsimp only [fullSafetySlice] at hJnext
                                c0_hsplit
                                · have hlit_lt : (stj.core.arena[(w0.setWidth 64 + 3#64 +
                                      j.setWidth 64).toNat]'hlit_ar).toNat <
                                      2 * s.core.cur_vars := by
                                    have hz := bv32_lit_toNat_mod64
                                      (stj.core.arena[(w0.setWidth 64 + 3#64 +
                                        j.setWidth 64).toNat]'hlit_ar)
                                    dsimp only [w0] at hz ⊢; c0_bound
                                  obtain ⟨hlit_v, _, hlit_ws, hlit_tmk, hlit_trc⟩ :=
                                    walk_lit_bds (hcore1.trans (hcore2.trans (hcore3.trans hcorej)))
                                      hcv_le hlenj hlit_lt
                                  c0_hfast_nobound
                                  · have hocc_lt : ((2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl +
                                        ncl) + (stj.scratch.wsort[(stj.core.arena[(w0.setWidth 64 +
                                          3#64 + j.setWidth 64).toNat]'hlit_ar).toNat]'hlit_ws
                                          ).setWidth 64).toNat <
                                        stj.scratch.scratch_buf.length := by
                                      have hz := bv32_lit_toNat_mod64
                                        (stj.scratch.wsort[(stj.core.arena[(w0.setWidth 64 + 3#64 +
                                          j.setWidth 64).toNat]'hlit_ar).toNat]'hlit_ws)
                                      dsimp only [w0] at hz ⊢; rw [hsbj]; c0_bound
                                    c0_hfast_nobound
                                    refine hJnext _ () _ (by assumption) ?_ ?_ ?_
                                    · rfl
                                    · exact ⟨hlenj.core_ok, { hlenj.scratch_ok with
                                        scratch_buf_len := by simp [hsbj]
                                        wsort_len := by simp [hwsj] }⟩
                                    · refine ⟨⟨hextj.1, hextj.2⟩, fun i hi => ?_⟩
                                      exact (list_getElem?_set_ne_lt hi (bv64_occ_ge2200 ncl
                                        ((stj.scratch.wsort[(stj.core.arena[(w0.setWidth 64 +
                                          3#64 + j.setWidth 64).toNat]'hlit_ar).toNat]'hlit_ws
                                          ).setWidth 64)
                                        (by rw [bv32_lit_toNat_mod64]; omega))).trans
                                        (hprej i hi)
                                  all_goals exact hJnext stj () mj hmj rfl hlenj ⟨hextj, hprej⟩
                                · exact hJnext stj () mj hmj rfl hlenj ⟨hextj, hprej⟩
                            · exact hJnx3 stj () mj hmj hcorej hlenj ⟨hextj, hprej⟩
                        all_goals exact hJnx3 st3 () m3 hm3 rfl hlen3 ⟨hext3, hpre3⟩
                    · exact hJnx2 st3 () m3 hm3 rfl hlen3 ⟨hext3, hpre3⟩
            · exact hQ (ulen, ()) st3 m3 (hcore1.trans (hcore2.trans hcore3)) hlen3
                ⟨hext3, hpre3, hulen_le⟩ hm3

end LeanQbe.T.Examples.Kissat.Proof.Walk
