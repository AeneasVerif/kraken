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
# Kissat Fidelity Step 13 Shard S3-A Proofs — Part 1 (`FullFidelityStep13S3WalkProof1`)

Callee-parametric (`Γ : Env`, `XPost := False`, `0` SAT model proofs) `Func.wp` proofs for:
1. `full_walk_collect_m7_step13_wp` (`FullM7Walk.m7CollectSpec`, `2200ULL` offset + `full` exit)
2. `full_walk_build_occ_m7_step13_wp` (`step13WalkBuildOccSpec`, preserving `WalkScrPrefixPres`)
-/

set_option autoImplicit false

local elab "s3w1_hsteps_nj" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S3

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.FullM7Walk
open Kraken.Bedrock2.Test
open scoped FullArenaTactics

/-! ## 1. Compact Arithmetic & State Helpers -/

section Helpers

private theorem w1_zext32 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat :=
  zext_toNat x (by decide)

private theorem w1_shl1 {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show 2 ^ 1 = 2 from rfl,
    show x.toNat * 2 = 2 * x.toNat by omega, Nat.mod_eq_of_lt hx]

private theorem w1_add1 {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by bv_omega

private theorem w1_add2 {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

private theorem w1_add1_32 {k s : BitVec 32} (h : k.toNat < s.toNat) :
    (k + 1#32).toNat = k.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by have := s.isLt; omega)]

private theorem w1_2200_2n {n : BitVec 64} (h : 2200 + 2 * n.toNat + 1 < 2 ^ 64) :
    (2200#64 + (n <<< (1 : Nat))).toNat = 2200 + 2 * n.toNat := by
  rw [BitVec.toNat_add, show (2200#64 : BitVec 64).toNat = 2200 from rfl,
    w1_shl1 (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem w1_2200_2n1 {n : BitVec 64} (h : 2200 + 2 * n.toNat + 1 < 2 ^ 64) :
    (2200#64 + (n <<< (1 : Nat)) + 1#64).toNat = 2200 + 2 * n.toNat + 1 := by
  rw [BitVec.toNat_add, w1_2200_2n h, show (1#64 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt h]

private theorem w1_ext_refl (s : FullState) : FullExtScratchPres s s := ⟨rfl, rfl⟩

private theorem w1_ext_trans {s1 s2 s3 : FullState}
    (h1 : FullExtScratchPres s1 s2) (h2 : FullExtScratchPres s2 s3) :
    FullExtScratchPres s1 s3 := ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

private theorem w1_len_sb {c : FullCfg} {s : FullState} {i : Nat} {v : BitVec 32}
    (h : s.LengthsOk c) :
    ({ s with scratch :=
      { s.scratch with scratch_buf := s.scratch.scratch_buf.set i v } }).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with
    scratch_buf_len := by rw [List.length_set, h.scratch_ok.scratch_buf_len] }⟩

private theorem w1_len_tr {c : FullCfg} {s : FullState} {i : Nat} {v : BitVec 32}
    (h : s.LengthsOk c) :
    ({ s with scratch :=
      { s.scratch with tarjan_reach := s.scratch.tarjan_reach.set i v } }).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with
    tarjan_reach_len := by rw [List.length_set, h.scratch_ok.tarjan_reach_len] }⟩

private theorem w1_len_tm {c : FullCfg} {s : FullState} {i : Nat} {v : BitVec 32}
    (h : s.LengthsOk c) :
    ({ s with scratch :=
      { s.scratch with tarjan_mark := s.scratch.tarjan_mark.set i v } }).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with
    tarjan_mark_len := by rw [List.length_set, h.scratch_ok.tarjan_mark_len] }⟩

private theorem w1_len_ws {c : FullCfg} {s : FullState} {i : Nat} {v : BitVec 32}
    (h : s.LengthsOk c) :
    ({ s with scratch := { s.scratch with wsort := s.scratch.wsort.set i v } }).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with
    wsort_len := by rw [List.length_set, h.scratch_ok.wsort_len] }⟩

private theorem w1_cap_check {n tot sz cap : Nat}
    (hcap : cap < 2 ^ 28) (hn : n ≤ cap) (htot : tot ≤ cap) (hsz : sz ≤ cap)
    (h : ¬ cap % 2 ^ 64 <
      ((BitVec.toNat (2200 : BitVec 64) +
        BitVec.toNat (5 : BitVec 64) * ((n + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64) % 2 ^ 64) %
        2 ^ 64 + tot) % 2 ^ 64 + sz % 2 ^ 64) :
    2200 + 5 * (n + 1) + (tot + sz) ≤ cap := by
  rw [show (2200 : BitVec 64).toNat = 2200 from rfl, show (5 : BitVec 64).toNat = 5 from rfl,
    show (1 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega : cap < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : n + 1 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 5 * (n + 1) < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 2200 + 5 * (n + 1) < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 2200 + 5 * (n + 1) + tot < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : sz < 2 ^ 64)] at h
  omega

private theorem w1_sb_2200_def {sb : List (BitVec 32)} {ci : BitVec 64}
    (h1 : (BitVec.toNat (2200 : BitVec 64) + 2 * ci.toNat) % 2 ^ 64 < sb.length)
    (h2 : (2200#64 + (ci <<< (1 : Nat))).toNat < sb.length)
    (hi0 : (2200#64 + (ci <<< (1 : Nat))).toNat = 2200 + 2 * ci.toNat)
    (hb : 2200 + 2 * ci.toNat < 2 ^ 64) :
    sb[(BitVec.toNat (2200 : BitVec 64) + 2 * ci.toNat) % 2 ^ 64]'h1 =
      sb[(2200#64 + (ci <<< (1 : Nat))).toNat]'h2 := by
  congr 1; rw [hi0, show BitVec.toNat (2200 : BitVec 64) = 2200 from rfl, Nat.mod_eq_of_lt hb]

private theorem w1_sb_2200_1_def {sb : List (BitVec 32)} {ci : BitVec 64}
    (h1 : (BitVec.toNat (2200 : BitVec 64) + 2 * ci.toNat +
      BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < sb.length)
    (h2 : (2200#64 + (ci <<< (1 : Nat)) + 1#64).toNat < sb.length)
    (hi1 : (2200#64 + (ci <<< (1 : Nat)) + 1#64).toNat = 2200 + 2 * ci.toNat + 1)
    (hb : 2200 + 2 * ci.toNat + 1 < 2 ^ 64) :
    sb[(BitVec.toNat (2200 : BitVec 64) + 2 * ci.toNat +
      BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'h1 =
      sb[(2200#64 + (ci <<< (1 : Nat)) + 1#64).toNat]'h2 := by
  congr 1
  rw [hi1, show BitVec.toNat (2200 : BitVec 64) = 2200 from rfl,
    show BitVec.toNat (1 : BitVec 64) = 1 from rfl, Nat.mod_eq_of_lt hb]

private theorem w1_lit_lt_2cv {x : BitVec 32} {cv mv : Nat} (hcv : cv ≤ mv) (hmv : mv < 2 * 2 ^ 28)
    (hc : x.toNat < 2 * (cv % 2 ^ 64) % 2 ^ 64) : x.toNat < 2 * cv := by
  rw [Nat.mod_eq_of_lt (by omega : cv < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 2 * cv < 2 ^ 64)] at hc; exact hc

private theorem w1_ar_lit_lt {ar : List (BitVec 32)} {e0 k : BitVec 32} {alen acap : Nat}
    (hal : ar.length = acap) (hale : alen ≤ acap) (haca : acap < 2 * 2 ^ 28)
    (he0k : e0.toNat + 3 + k.toNat < alen) :
    (e0.setWidth 64 + 3#64 + k.setWidth 64).toNat < ar.length := by
  have := e0.isLt; have := k.isLt
  rw [BitVec.toNat_add, BitVec.toNat_add, w1_zext32, w1_zext32,
    show (3#64 : BitVec 64).toNat = 3 from rfl,
    Nat.mod_eq_of_lt (by omega : e0.toNat + 3 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : e0.toNat + 3 + k.toNat < 2 ^ 64), hal]; omega

private theorem w1_ar_lit_def {ar : List (BitVec 32)} {e0 k : BitVec 32}
    (h1 : (e0.toNat + BitVec.toNat (3 : BitVec 64) + k.toNat) % 2 ^ 64 < ar.length)
    (h2 : (e0.setWidth 64 + 3#64 + k.setWidth 64).toNat < ar.length)
    (he : e0.toNat + 3 < 2 ^ 64) :
    ar[(e0.toNat + BitVec.toNat (3 : BitVec 64) + k.toNat) % 2 ^ 64]'h1 =
      ar[(e0.setWidth 64 + 3#64 + k.setWidth 64).toNat]'h2 := by
  congr 1
  rw [BitVec.toNat_add, BitVec.toNat_add, w1_zext32, w1_zext32,
    show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
    show (3#64 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt he]

private theorem w1_e0_3_le {e0 : BitVec 32} {alen acap : Nat} (hale : alen ≤ acap)
    (haca : acap < 2 * 2 ^ 28)
    (hc : (e0.toNat + BitVec.toNat (3 : BitVec 64)) % 2 ^ 64 ≤ alen % 2 ^ 64) :
    e0.toNat + 3 ≤ alen := by
  have := e0.isLt
  rw [show (3 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega : e0.toNat + 3 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : alen < 2 ^ 64)] at hc; exact hc

private theorem w1_e0_sz_le {e0 sz : BitVec 32} {alen acap : Nat} (hale : alen ≤ acap)
    (haca : acap < 2 * 2 ^ 28)
    (hc : (e0.toNat + BitVec.toNat (3 : BitVec 64) + sz.toNat) % 2 ^ 64 ≤ alen % 2 ^ 64) :
    e0.toNat + 3 + sz.toNat ≤ alen := by
  have := e0.isLt; have := sz.isLt
  rw [show (3 : BitVec 64).toNat = 3 from rfl,
    Nat.mod_eq_of_lt (by omega : e0.toNat + 3 + sz.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : alen < 2 ^ 64)] at hc; exact hc

private abbrev W1BuildPost (c : FullCfg) (s s0 : FullState) (R : Mem 64 → Prop) (m : Mem 64) :
    Prop :=
  ∃ sN : FullState, PreservesCoreSlice FullState.core s0 sN ∧ sN.LengthsOk c ∧
    FullExtScratchPres s sN ∧ WalkScrPrefixPres s sN ∧ (FullMem c sN ⋆ R) m

private theorem w1_p3_cur_lt {ncl cur : BitVec 64} {cap : Nat}
    (hcap : 2200 + 5 * ncl.toNat ≤ cap) (hscr : cap < 2 ^ 28) (hcur32 : cur.toNat < 2 ^ 32)
    (hc : (BitVec.toNat (2200 : BitVec 64) + 2 * ncl.toNat + ncl.toNat + ncl.toNat + ncl.toNat +
      cur.toNat) % 2 ^ 64 < cap % 2 ^ 64) :
    2200 + 5 * ncl.toNat + cur.toNat < cap := by
  rw [show BitVec.toNat (2200 : BitVec 64) = 2200 from rfl,
    Nat.mod_eq_of_lt (by omega : cap < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega)] at hc; omega

private theorem w1_p3_post {c : FullCfg} {s s0 : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {v24 cur ci : BitVec 64} {lit : BitVec 32} {ncl : BitVec 64}
    (hs0 : s0.LengthsOk c) (hpres : FullExtScratchPres s s0) (hpre : WalkScrPrefixPres s s0)
    (hcur_eq : (v24 + cur).toNat = 2200 + 5 * ncl.toNat + cur.toNat)
    (hm : (FullMem c { s0 with scratch := { s0.scratch with
      scratch_buf := s0.scratch.scratch_buf.set (v24 + cur).toNat (ci.setWidth 32)
      wsort := s0.scratch.wsort.set (lit.setWidth 64).toNat ((cur + 1#64).setWidth 32) } } ⋆ R) m) :
    W1BuildPost c s s0 R m :=
  ⟨{ s0 with scratch := { s0.scratch with
      scratch_buf := s0.scratch.scratch_buf.set (v24 + cur).toNat (ci.setWidth 32)
      wsort := s0.scratch.wsort.set (lit.setWidth 64).toNat ((cur + 1#64).setWidth 32) } },
    rfl, w1_len_ws (w1_len_sb hs0), ⟨hpres.1, hpres.2⟩,
    walkScrPrefixPres_trans hpre
      (walkScrPrefixPres_set_ge (s := s0) (idx := (v24 + cur).toNat) (by rw [hcur_eq]; omega)), hm⟩

private theorem w1_p1_post {c : FullCfg} {s s0 : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {idx : Nat} {v : BitVec 32} (hs0 : s0.LengthsOk c) (hpres : FullExtScratchPres s s0)
    (hpre : WalkScrPrefixPres s s0)
    (hm : (FullMem c { s0 with scratch := { s0.scratch with
      tarjan_reach := s0.scratch.tarjan_reach.set idx v } } ⋆ R) m) :
    W1BuildPost c s s0 R m :=
  ⟨{ s0 with scratch := { s0.scratch with
      tarjan_reach := s0.scratch.tarjan_reach.set idx v } },
    rfl, w1_len_tr hs0, ⟨hpres.1, hpres.2⟩, hpre, hm⟩

private theorem w1_lit_p1_lt {c : FullCfg} {s s0 : FullState} {lit : BitVec 32}
    (hs0 : s0.LengthsOk c) (hcv : s.core.cur_vars ≤ c.max_vars)
    (hlt : lit.toNat < 2 * s.core.cur_vars) :
    (lit.setWidth 64).toNat < s0.scratch.tarjan_reach.length ∧
    (lit.setWidth 64).toNat < s0.scratch.walk_vals.length :=
  ⟨by rw [w1_zext32, hs0.scratch_ok.tarjan_reach_len]; omega,
   by rw [w1_zext32, hs0.scratch_ok.walk_vals_len]; omega⟩

private theorem w1_lit_p3_lt {c : FullCfg} {s s0 : FullState} {lit : BitVec 32}
    (hs0 : s0.LengthsOk c) (hcv : s.core.cur_vars ≤ c.max_vars)
    (hlt : lit.toNat < 2 * s.core.cur_vars) :
    (lit.setWidth 64).toNat < s0.scratch.wsort.length ∧
    (lit.setWidth 64).toNat < s0.scratch.tarjan_mark.length ∧
    (lit.setWidth 64).toNat < s0.scratch.tarjan_reach.length :=
  ⟨by rw [w1_zext32, hs0.scratch_ok.wsort_len]; omega,
   by rw [w1_zext32, hs0.scratch_ok.tarjan_mark_len]; omega,
   by rw [w1_zext32, hs0.scratch_ok.tarjan_reach_len]; omega⟩

private theorem w1_ar_sz_lt {ar : List (BitVec 32)} {e0 : BitVec 32} {alen acap : Nat}
    (hal : ar.length = acap) (hale : alen ≤ acap) (_haca : acap < 2 * 2 ^ 28)
    (he03 : e0.toNat + 3 ≤ alen) : (e0.setWidth 64 + 2#64).toNat < ar.length := by
  have := e0.isLt
  rw [BitVec.toNat_add, w1_zext32, show (2#64 : BitVec 64).toNat = 2 from rfl,
    Nat.mod_eq_of_lt (by omega), hal]; omega

private theorem w1_ar_sz_def {ar : List (BitVec 32)} {e0 : BitVec 32} {alen acap : Nat}
    (hal : ar.length = acap) (hale : alen ≤ acap) (_haca : acap < 2 * 2 ^ 28)
    (he03 : e0.toNat + 3 ≤ alen) (h2 : (e0.setWidth 64 + 2#64).toNat < ar.length) :
    ar[(e0.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
      have := e0.isLt; rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
        Nat.mod_eq_of_lt (by omega : e0.toNat + 2 < 2 ^ 64), hal]; omega) =
      ar[(e0.setWidth 64 + 2#64).toNat]'h2 := by
  congr 1

private theorem w1_v21_to_v25 {ncl : BitVec 64} {cap : Nat}
    (hcap : 2200 + 5 * ncl.toNat ≤ cap) (hscr : cap < 2 ^ 28) :
    let v21 := 2200#64 + (ncl <<< (1 : Nat))
    let v22 := v21 + ncl; let v23 := v22 + ncl; let v24 := v23 + ncl
    v21.toNat = 2200 + 2 * ncl.toNat ∧ v22.toNat = 2200 + 3 * ncl.toNat ∧
    v23.toNat = 2200 + 4 * ncl.toNat ∧ v24.toNat = 2200 + 5 * ncl.toNat ∧
    (BitVec.ofNat 64 cap - v24).toNat = cap - (2200 + 5 * ncl.toNat) := by
  dsimp only
  have h1 : (2200#64 + (ncl <<< (1 : Nat))).toNat = 2200 + 2 * ncl.toNat := by
    rw [BitVec.toNat_add, w1_shl1 (by omega), show (2200#64 : BitVec 64).toNat = 2200 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have h2 : (2200#64 + (ncl <<< (1 : Nat)) + ncl).toNat = 2200 + 3 * ncl.toNat := by
    rw [w1_add2 (by rw [h1]; omega), h1]; omega
  have h3 : (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl).toNat = 2200 + 4 * ncl.toNat := by
    rw [w1_add2 (by rw [h2]; omega), h2]; omega
  have h4 : (2200#64 + (ncl <<< (1 : Nat)) + ncl + ncl + ncl).toNat = 2200 + 5 * ncl.toNat := by
    rw [w1_add2 (by rw [h3]; omega), h3]; omega
  refine ⟨h1, h2, h3, h4, ?_⟩
  rw [BitVec.toNat_sub, bv64_ofNat_toNat (by omega), h4]
  exact Nat.mod_eq_of_lt (by omega) ▸ by omega

private theorem w1_ci_sb_defs {sb : List (BitVec 32)} {ci ncl : BitVec 64} {cap : Nat}
    (hsbl : sb.length = cap) (hcap : 2200 + 5 * ncl.toNat ≤ cap) (hscr : cap < 2 ^ 28)
    (hci : ci.toNat < ncl.toNat) :
    ∃ (hi0 : (2200#64 + (ci <<< (1 : Nat))).toNat < sb.length)
      (hi1 : (2200#64 + (ci <<< (1 : Nat)) + 1#64).toNat < sb.length),
      sb[(BitVec.toNat (2200 : BitVec 64) + 2 * ci.toNat) % 2 ^ 64]'(by
        rw [show BitVec.toNat (2200 : BitVec 64) = 2200 from rfl,
          Nat.mod_eq_of_lt (by omega : 2200 + 2 * ci.toNat < 2 ^ 64), hsbl]; omega) =
        sb[(2200#64 + (ci <<< (1 : Nat))).toNat]'hi0 ∧
      sb[(BitVec.toNat (2200 : BitVec 64) + 2 * ci.toNat +
        BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
        rw [show BitVec.toNat (2200 : BitVec 64) = 2200 from rfl,
          show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
          Nat.mod_eq_of_lt (by omega : 2200 + 2 * ci.toNat + 1 < 2 ^ 64), hsbl]; omega) =
        sb[(2200#64 + (ci <<< (1 : Nat)) + 1#64).toNat]'hi1 := by
  have hi0_eq := w1_2200_2n (n := ci) (by omega)
  have hi1_eq := w1_2200_2n1 (n := ci) (by omega)
  have hi0 : (2200#64 + (ci <<< (1 : Nat))).toNat < sb.length := by rw [hi0_eq, hsbl]; omega
  have hi1 : (2200#64 + (ci <<< (1 : Nat)) + 1#64).toNat < sb.length := by rw [hi1_eq, hsbl]; omega
  exact ⟨hi0, hi1, w1_sb_2200_def _ hi0 hi0_eq (by omega),
    w1_sb_2200_1_def _ hi1 hi1_eq (by omega)⟩

private theorem w1_p2_deg_le {deg : BitVec 32} {ncl off_c : BitVec 64} {cap : Nat}
    (hcap : 2200 + 5 * ncl.toNat ≤ cap) (hscr : cap < 2 ^ 28)
    (hoff : off_c.toNat ≤ cap - (2200 + 5 * ncl.toNat))
    (hc : ¬ (2 ^ 64 - off_c.toNat + (2 ^ 64 - (BitVec.toNat (2200 : BitVec 64) +
      2 * ncl.toNat + ncl.toNat + ncl.toNat + ncl.toNat) % 2 ^ 64 + cap)) %
      2 ^ 64 < deg.toNat) :
    deg.toNat ≤ cap - (2200 + 5 * ncl.toNat) - off_c.toNat := by
  rw [show BitVec.toNat (2200 : BitVec 64) = 2200 from rfl,
    Nat.mod_eq_of_lt (by omega : 2200 + 2 * ncl.toNat + ncl.toNat + ncl.toNat + ncl.toNat <
      2 ^ 64)] at hc
  have h1 : (2 ^ 64 - off_c.toNat +
      (2 ^ 64 - (2200 + 2 * ncl.toNat + ncl.toNat + ncl.toNat + ncl.toNat) + cap)) % 2 ^ 64 =
      cap - (2200 + 5 * ncl.toNat) - off_c.toNat := by omega
  rw [h1] at hc; omega

end Helpers

/-! ## 2. `full_walk_collect_m7_step13_wp` (`m7CollectSpec`) -/

/-- Step-13 `full_walk_collect_m7` satisfies `FullM7Walk.m7CollectSpec` (`2200ULL` scratch offset
and `full` overflow return `0ULL`). -/
theorem full_walk_collect_m7_step13_wp (Γ : Env)
    (hArenaNext : ∀ args m Q X, fullArenaNextSpec args m Q X →
      Γ "full_arena_next" [i64, i32] [i32] args m Q X) :
    ∀ a m Q X, m7CollectSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.full_walk_collect_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hspec
  rw [m7CollectSpec_eq] at hspec
  dsimp only [SafetySlice.spec, fullSafetySlice] at hspec
  rcases hspec with ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hmax := c.hmaxv; have haca := c.harena; have hwc := c.hwcap; have hscr := c.hscr
  unfold dimacsBound at hmax haca hwc hscr
  have hcv_le := hlen.core_ok.cur_vars_le; have harl := hlen.core_ok.arena_len_arr
  have hale := hlen.core_ok.arena_len_le; have hvl := hlen.core_ok.vals_len
  have hwvl := hlen.core_ok.wvec_len; have hwsl := hlen.core_ok.wstk_len_arr
  have hwll := hlen.core_ok.wlen_le
  dsimp only [Func.wp, FullFidelityStep13S3.full_walk_collect_m7_body]
  c0_hsplit; · c0_hsteps; exact hQ (0#64, ()) s m rfl hlen (w1_ext_refl s) hm
  c0_hsplit; · c0_hsteps; exact hQ (0#64, ()) s m rfl hlen (w1_ext_refl s) hm
  c0_hsplit; · c0_hsteps; exact hQ (0#64, ()) s m rfl hlen (w1_ext_refl s) hm
  have hcv_pos : 0 < s.core.cur_vars := Nat.pos_of_ne_zero fun h0 =>
    (‹¬ BitVec.ofNat 64 s.core.cur_vars = 0›) (by rw [h0]; rfl)
  have hcap2300 : 2300 ≤ c.scratch_cap := by
    have h1 : ¬ c.scratch_cap % 2 ^ 64 < (2300#64 : BitVec 64).toNat := by assumption
    rw [show (2300#64 : BitVec 64).toNat = 2300 from rfl, Nat.mod_eq_of_lt (by omega)] at h1; omega
  have h2cv_eq : ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    rw [w1_shl1 (by rw [bv64_ofNat_toNat (by omega)]; omega), bv64_ofNat_toNat (by omega)]
  let PCol (sA : FullState) (nA totA : BitVec 64) (mA : Mem 64) : Prop :=
    ∃ sB : FullState, PreservesCoreSlice FullState.core sA sB ∧ sB.LengthsOk c ∧
      nA.toNat ≤ c.scratch_cap ∧ totA.toNat ≤ c.scratch_cap ∧
      2200 + 5 * nA.toNat + totA.toNat ≤ c.scratch_cap ∧ FullExtScratchPres s sB ∧
      (FullMem c sB ⋆ R) mA
  c0_hsteps_nogrp
  -- Loop 1: binary clauses (`l < 2 * cur_vars`)
  refine wp_loop_safety_slice_pure (fullSafetySlice c) s R
    (fun s1 (n, tot, ch, l, ()) =>
      n.toNat ≤ c.scratch_cap ∧ tot.toNat ≤ c.scratch_cap ∧
      2200 + 5 * n.toNat + tot.toNat ≤ c.scratch_cap ∧
      l.toNat ≤ 2 * s.core.cur_vars ∧ FullExtScratchPres s s1)
    (fun (_, _, _, l, ()) => 2 * s.core.cur_vars - l.toNat)
    (fun J0 hJ0 => by
      c0_hsteps
      exact hJ0 s (0#64, 0#64, false, 0#64, ()) m hm rfl hlen
        ⟨Nat.zero_le _, Nat.zero_le _, by simp; omega, Nat.zero_le _, w1_ext_refl s⟩)
    (fun J0 s1 (n, tot, ch, l, ()) m1 hcore1 hs1 ⟨hn1, htot1, hcap1, hl1, hpres1⟩ hm1 hJ0 => ?_)
  dsimp only [fullSafetySlice] at hs1 hm1
  have hceq1 : s1.core = s.core := hcore1
  refine wp_join_group (ts := []) (fun () m2 => m1 = m2)
    (fun _ _ m2 hm2 => ?_) (fun J1 hJ1 => ?_)
  · rcases hm2 with rfl; clear J0 hJ0 hl1
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64, i64, .bool, i64])
      (fun (_, _, _, _, ()) m2 => ∃ s2 : FullState,
        PreservesCoreSlice FullState.core s s2 ∧ s2.LengthsOk c ∧
        FullExtScratchPres s s2 ∧ (FullMem c s2 ⋆ R) m2)
      (fun _ ⟨_, _, _, _, ⟨⟩⟩ m2 ⟨s2, hcore2, hs2, hpres2, hm2⟩ => by
        c0_hsteps <;> exact hQ _ s2 m2 hcore2 hs2 hpres2 hm2)
      (fun J2 hJ2 => ?_)
    -- Loop 2: arena scan (`p + 3 <= arena_len`)
    refine wp_loop_safety_slice_pure (fullSafetySlice c) s1 R
      (fun s2 (n2, tot2, ch2, p, ()) =>
        p.toNat ≤ s.core.arena_len ∧ n2.toNat ≤ c.scratch_cap ∧ tot2.toNat ≤ c.scratch_cap ∧
        2200 + 5 * n2.toNat + tot2.toNat ≤ c.scratch_cap ∧ FullExtScratchPres s s2)
      (fun (_, _, _, p, ()) => s.core.arena_len - p.toNat)
      (fun J3 hJ3 => by
        c0_hsteps; exact hJ3 s1 (n, tot, ch, 0#64, ()) m1 hm1 rfl hs1
          ⟨Nat.zero_le _, hn1, htot1, hcap1, hpres1⟩)
      (fun J3 s2 (n2, tot2, ch2, p, ()) m2 hcore2 hs2
          ⟨hp2, hn2, htot2, hcap2, hpres2⟩ hm2 hJ3 => ?_)
    dsimp only [fullSafetySlice] at hs2 hm2
    have hceq2 : s2.core = s.core := Eq.trans hcore2 hceq1
    c0_hsplit
    · c0_hsplit
      · c0_hsteps; exact hJ2 (n2, tot2, ch2, p, ()) m2 ⟨s2, hceq2, hs2, hpres2, hm2⟩
      have hp3_le : p.toNat + 3 ≤ s.core.arena_len := by
        rename_i hcond
        simp only [show (3 : BitVec 64).toNat = 3 from rfl] at hcond
        rw [Nat.mod_eq_of_lt (by omega : p.toNat + 3 < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64)] at hcond; exact hcond
      have hp_ar : p.toNat < s2.core.arena.length := by rw [hceq2, harl]; omega
      have hp2_ar : (p + 2#64).toNat < s2.core.arena.length := by
        rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl,
          Nat.mod_eq_of_lt (by omega), hceq2, harl]; omega
      c0_hsteps_nogrp
      let sz2 := s2.core.arena[(p + 2#64).toNat]'hp2_ar
      refine wp_join_group (ts := [i64, i64, .bool])
        (fun (n3, tot3, _, ()) m3 => PCol s2 n3 tot3 m3)
        (fun _ ⟨n3, tot3, ch3, ⟨⟩⟩ m3 ⟨s3, hcore3, hs3, hn3, htot3, hcap3, hpres3, hm3⟩ => by
          have hceq3 : s3.core = s.core := Eq.trans hcore3 hceq2
          c0_hsteps_nogrp; c0_call hArenaNext
          refine ⟨c, s3, R, rfl, hs3, hm3, ?_⟩; dsimp only
          have hp32_eq : (p.setWidth 32).toNat = p.toNat := by
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
          have hnb := fullArenaNextOff_bounds (ar := s.core.arena) (alen := s.core.arena_len)
            (cref := p.toNat) hp3_le
          have hnxt_nat : (BitVec.ofNat 32 (fullArenaNextOff s3.core.arena s3.core.arena_len
              (p.setWidth 32).toNat)).toNat =
              fullArenaNextOff s.core.arena s.core.arena_len p.toNat := by
            rw [hceq3, hp32_eq, bv32_ofNat_toNat (by omega)]
          c0_hsplit
          · c0_hsteps; exact hJ2 (n3, tot3, ch3, p, ()) m3 ⟨s3, hceq3, hs3, hpres3, hm3⟩
          · have hgt : p.toNat < fullArenaNextOff s.core.arena s.core.arena_len p.toNat := by
              rw [hceq3, Nat.mod_eq_of_lt (by omega : p.toNat < 2 ^ 32),
                Nat.mod_eq_of_lt (by omega :
                  fullArenaNextOff s.core.arena s.core.arena_len p.toNat < 2 ^ 32)] at hc; omega
            c0_hsteps
            exact hJ3 s3 (n3, tot3, ch3, _, ()) m3 hm3
              (by dsimp only; rw [w1_zext32, hnxt_nat]; omega) hcore3 hs3
              ⟨by rw [w1_zext32, hnxt_nat]; exact hnb.2, hn3, htot3, hcap3, hpres3⟩)
        (fun J4 hJ4 => ?_)
      c0_hsplit; rotate_left
      · c0_hsteps; exact hJ4 (n2, tot2, ch2, ()) m2 ⟨s2, rfl, hs2, hn2, htot2, hcap2, hpres2, hm2⟩
      c0_hsplit; rotate_left
      · c0_hsteps; exact hJ4 (n2, tot2, ch2, ()) m2 ⟨s2, rfl, hs2, hn2, htot2, hcap2, hpres2, hm2⟩
      c0_hsplit; rotate_left
      · c0_hsteps; exact hJ4 (n2, tot2, ch2, ()) m2 ⟨s2, rfl, hs2, hn2, htot2, hcap2, hpres2, hm2⟩
      have hsz_le_al : sz2.toNat ≤ s.core.arena_len := by
        rw [Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64)] at hc
        dsimp only [sz2]; simp only [BitVec.toNat_add]; exact hc
      c0_hsplit; rotate_left
      · c0_hsteps; exact hJ4 (n2, tot2, ch2, ()) m2 ⟨s2, rfl, hs2, hn2, htot2, hcap2, hpres2, hm2⟩
      have hp3sz_le : p.toNat + 3 + sz2.toNat ≤ s.core.arena_len := by
        dsimp only [sz2]; simp only [BitVec.toNat_add]
        have hsum_64 : ∀ x : BitVec 32, (p.toNat + 3 + x.toNat) % 2 ^ 64 =
            p.toNat + 3 + x.toNat := fun x => Nat.mod_eq_of_lt (by have := x.isLt; omega)
        rw [Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64)] at hc
        simp only [show (3 : BitVec 64).toNat = 3 from rfl, hsum_64] at hc; exact hc
      c0_hsteps_nogrp
      refine wp_loop_break_group (fun (_, _, _, ()) ma => m2 = ma)
        (fun rem (_, k, ()) ma => m2 = ma ∧ k.toNat ≤ sz2.toNat ∧ rem = sz2.toNat - k.toNat)
        ?_ ?_ ?_
      · rintro _ ⟨_, _, _, ⟨⟩⟩ ma hma; rcases hma with rfl
        refine wp_join_group (ts := [i64, i64, .bool])
          (fun (n3, tot3, _, ()) m3 => PCol s2 n3 tot3 m3)
          (fun _ ⟨n3, tot3, ch3, ⟨⟩⟩ m3 h => by c0_hsteps; exact hJ4 (n3, tot3, ch3, ()) m3 h)
          (fun J6 hJ6 => ?_)
        c0_hsplit
        · c0_hsteps; exact hJ6 (n2, tot2, ch2, ()) m2 ⟨s2, rfl, hs2, hn2, htot2, hcap2, hpres2, hm2⟩
        c0_hsplit; rotate_left
        · c0_hsteps; exact hJ6 (n2, tot2, ch2, ()) m2 ⟨s2, rfl, hs2, hn2, htot2, hcap2, hpres2, hm2⟩
        refine wp_join_group (ts := [i64, i64, .bool])
          (fun (n3, tot3, _, ()) m3 => PCol s2 n3 tot3 m3)
          (fun _ ⟨n3, tot3, ch3, ⟨⟩⟩ m3 h => by c0_hsteps; exact hJ6 (n3, tot3, ch3, ()) m3 h)
          (fun J7 hJ7 => ?_)
        have hfull : ∀ m0, (FullMem c s2 ⋆ R) m0 →
            J7 (n2, tot2, true, ()) m0 := fun m0 hm0 =>
          hJ7 (n2, tot2, true, ()) m0 ⟨s2, rfl, hs2, hn2, htot2, hcap2, hpres2, hm0⟩
        c0_hsplit; · c0_hsteps; exact hfull m2 hm2
        have hsz_raw : s2.core.arena[(p.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64].toNat =
            sz2.toNat := by dsimp only [sz2]; simp only [BitVec.toNat_add]; rfl
        have hsz_cap : sz2.toNat ≤ c.scratch_cap := by rw [hsz_raw] at hc; omega
        c0_hsplit; · c0_hsteps; exact hfull m2 hm2
        have hn2p1 : (n2 + 1#64).toNat = n2.toNat + 1 := w1_add1 (by omega)
        have hn2p1_le : n2.toNat + 1 ≤ c.scratch_cap := by
          rw [show (1 : BitVec 64).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : n2.toNat + 1 < 2 ^ 64)] at hc; omega
        c0_hsplit; · c0_hsteps; exact hfull m2 hm2
        have htot_p : (tot2 + sz2.setWidth 64).toNat = tot2.toNat + sz2.toNat := by
          rw [BitVec.toNat_add, w1_zext32, Nat.mod_eq_of_lt (by omega)]
        have htot_le : tot2.toNat + sz2.toNat ≤ c.scratch_cap := by
          rw [hsz_raw, Nat.mod_eq_of_lt (by omega : tot2.toNat + sz2.toNat < 2 ^ 64)] at hc; omega
        c0_hsplit; · c0_hsteps; exact hfull m2 hm2
        have hcap_new : 2200 + 5 * (n2.toNat + 1) + (tot2.toNat + sz2.toNat) ≤ c.scratch_cap := by
          rw [hsz_raw] at hc; exact w1_cap_check hscr hn2 htot2 hsz_cap (by
            simpa [show (2200 : BitVec 64).toNat = 2200 from rfl,
              show (5 : BitVec 64).toNat = 5 from rfl, show (1 : BitVec 64).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (by omega : sz2.toNat < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : n2.toNat + 1 < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : 5 * (n2.toNat + 1) < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : 2200 + 5 * (n2.toNat + 1) < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : 2200 + 5 * (n2.toNat + 1) + tot2.toNat < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : 2200 + 5 * (n2.toNat + 1) + tot2.toNat + sz2.toNat <
                2 ^ 64)] using hc)
        have hsbl2 := hs2.scratch_ok.scratch_buf_len
        have hi0_eq := w1_2200_2n (n := n2) (by omega)
        have hi1_eq := w1_2200_2n1 (n := n2) (by omega)
        have hi0_lt : (2200#64 + (n2 <<< (1 : Nat))).toNat < s2.scratch.scratch_buf.length := by
          rw [hi0_eq, hsbl2]; omega
        have hi1_lt : (2200#64 + (n2 <<< (1 : Nat)) + 1#64).toNat <
            (s2.scratch.scratch_buf.set (2200#64 + (n2 <<< (1 : Nat))).toNat
              (p.setWidth 32)).length := by rw [List.length_set, hi1_eq, hsbl2]; omega
        c0_hsteps
        exact hJ7 (n2 + 1#64, tot2 + sz2.setWidth 64, ch2, ()) _
          ⟨{ s2 with scratch := { s2.scratch with
              scratch_buf := (s2.scratch.scratch_buf.set (2200#64 + (n2 <<< (1 : Nat))).toNat
                (p.setWidth 32)).set (2200#64 + (n2 <<< (1 : Nat)) + 1#64).toNat 0#32 } },
            rfl, w1_len_sb (w1_len_sb hs2), by rw [hn2p1]; exact hn2p1_le,
            by rw [htot_p]; exact htot_le, by rw [hn2p1, htot_p]; exact hcap_new,
            ⟨hpres2.1, hpres2.2⟩, hm⟩
      · rintro B _ rem ⟨unass, k, ⟨⟩⟩ ma hB ih ⟨hma, hkle, rfl⟩; rcases hma with rfl
        c0_hsplit; rotate_left; · c0_hsteps; exact hB (false, unass, k, ()) m2 rfl
        have hk_lt : k.toNat < sz2.toNat := by assumption
        have hp3k : (p + 3#64 + k.setWidth 64).toNat = p.toNat + 3 + k.toNat := by
          rw [BitVec.toNat_add, BitVec.toNat_add, w1_zext32,
            show (3#64 : BitVec 64).toNat = 3 from rfl,
            Nat.mod_eq_of_lt (by omega : p.toNat + 3 < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
        have hp3k_ar : (p + 3#64 + k.setWidth 64).toNat < s2.core.arena.length := by
          rw [hp3k, hceq2, harl]; omega
        c0_hsteps_nogrp
        refine wp_join_group (ts := [.bool, .bool]) (fun (_, _, ()) ma' => m2 = ma')
          (fun _ ⟨_, ua', ⟨⟩⟩ ma' hma' => by
            rcases hma' with rfl
            have hk1 : (k + 1#32).toNat = k.toNat + 1 := w1_add1_32 hk_lt
            c0_hsteps; exact ih (sz2.toNat - (k + 1#32).toNat) (ua', k + 1#32, ()) m2
              (by rw [hk1]; omega) ⟨rfl, by rw [hk1]; omega, rfl⟩)
          (fun J7 hJ7 => ?_)
        c0_hsplit; rotate_left; · c0_hsteps; exact hJ7 (false, unass, ()) m2 rfl
        have hp3k_raw : (s2.core.arena[(p.toNat + BitVec.toNat (3 : BitVec 64) + k.toNat) %
            2 ^ 64]'(by
              rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                Nat.mod_eq_of_lt (by omega : p.toNat + 3 + k.toNat < 2 ^ 64), hceq2, harl]
              omega)).toNat =
            (s2.core.arena[(p + 3#64 + k.setWidth 64).toNat]'hp3k_ar).toNat := by
          congr 2; rw [hp3k, show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
            Nat.mod_eq_of_lt (by omega : p.toNat + 3 + k.toNat < 2 ^ 64)]
        have hlit_v : ((s2.core.arena[(p + 3#64 + k.setWidth 64).toNat]'hp3k_ar).setWidth
            64).toNat < s2.core.vals.length := by
          rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hc
          have hvl2 : s2.core.vals.length = 2 * c.max_vars := by rw [hceq2, hvl]
          rw [w1_zext32, ← hp3k_raw, hvl2]; exact Nat.lt_of_lt_of_le hc (by omega)
        c0_hsplit
        · c0_hsteps; exact hB (true, unass, k, ()) m2 rfl
        · c0_hsteps <;> first
          | exact hJ7 (false, true, ()) m2 rfl | exact hJ7 (false, unass, ()) m2 rfl
      · intro _ _ _ hL; c0_hsteps
        exact hL sz2.toNat (false, 0#32, ()) m2 ⟨rfl, Nat.zero_le _, (Nat.sub_zero _).symm⟩
    · c0_hsteps; exact hJ2 (n2, tot2, ch2, p, ()) m2 ⟨s2, hceq2, hs2, hpres2, hm2⟩
  · -- Loop 1 body (`l < 2 * cur_vars`)
    c0_hsplit; rotate_left; · c0_hsteps; exact hJ1 () m1 rfl
    have hl_lt : l.toNat < 2 * s.core.cur_vars := by
      try rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
      try rw [Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hc; exact hc
    c0_hsplit; · c0_hsteps; exact hJ1 () m1 rfl
    have hl1_eq : (l + 1#64).toNat = l.toNat + 1 := w1_add1 (by omega)
    refine wp_join_group (ts := [i64, i64, .bool]) (fun (n2, tot2, _, ()) m2 => PCol s1 n2 tot2 m2)
      (fun _ ⟨n2, tot2, ch2, ⟨⟩⟩ m2 ⟨s2, hcore2, hs2, hn2, htot2, hcap2, hpres2, hm2⟩ => by
        c0_hsteps; exact hJ0 s2 (n2, tot2, ch2, l + 1#64, ()) m2 hm2 (by dsimp only; omega)
          hcore2 hs2 ⟨hn2, htot2, hcap2, by omega, hpres2⟩)
      (fun J2 hJ2 => ?_)
    have hl_v : l.toNat < s1.core.vals.length := by rw [hceq1, hvl]; omega
    c0_hsplit; rotate_left
    · c0_hsteps; exact hJ2 (n, tot, ch, ()) m1 ⟨s1, rfl, hs1, hn1, htot1, hcap1, hpres1, hm1⟩
    have h2l : (l <<< (1 : Nat)).toNat = 2 * l.toNat := w1_shl1 (by omega)
    have h2l_wv : (l <<< (1 : Nat)).toNat < s1.core.wvec.length := by rw [h2l, hceq1, hwvl]; omega
    have h2l1_eq : ((l <<< (1 : Nat)) + 1#64).toNat = 2 * l.toNat + 1 := by
      rw [BitVec.toNat_add, h2l, show (1#64 : BitVec 64).toNat = 1 from rfl,
        Nat.mod_eq_of_lt (by omega)]
    have h2l1_wv : ((l <<< (1 : Nat)) + 1#64).toNat < s1.core.wvec.length := by
      rw [h2l1_eq, hceq1, hwvl]; omega
    c0_hsteps_nogrp
    let off := (s1.core.wvec[(l <<< (1 : Nat)).toNat]'h2l_wv).setWidth 64
    let len := (s1.core.wvec[((l <<< (1 : Nat)) + 1#64).toNat]'h2l1_wv).setWidth 64
    have hoff_raw : (s1.core.wvec[2 * l.toNat % 2 ^ 64]'(by
        rw [Nat.mod_eq_of_lt (by omega : 2 * l.toNat < 2 ^ 64), hceq1, hwvl]; omega)).toNat =
        off.toNat := by
      dsimp only [off]; rw [w1_zext32]; congr 2
    have hlen_raw : (s1.core.wvec[(2 * l.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
        rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
          Nat.mod_eq_of_lt (by omega : 2 * l.toNat + 1 < 2 ^ 64), hceq1, hwvl]; omega)).toNat =
        len.toNat := by
      dsimp only [len]; rw [w1_zext32]; congr 2
      rw [h2l1_eq, show BitVec.toNat (1 : BitVec 64) = 1 from rfl]
      rw [Nat.mod_eq_of_lt (by omega)]
    refine wp_join_group (ts := [i64, i64, .bool]) (fun (n2, tot2, _, ()) m2 => PCol s1 n2 tot2 m2)
      (fun _ ⟨n2, tot2, ch2, ⟨⟩⟩ m2 h => by c0_hsteps; exact hJ2 (n2, tot2, ch2, ()) m2 h)
      (fun J3 hJ3 => ?_)
    c0_hsplit; rotate_left
    · c0_hsteps; exact hJ3 (n, tot, ch, ()) m1 ⟨s1, rfl, hs1, hn1, htot1, hcap1, hpres1, hm1⟩
    have hoff_le : off.toNat ≤ s.core.wlen := by
      try rw [Nat.mod_eq_of_lt (by omega : s.core.wlen < 2 ^ 64)] at hc
      rw [hoff_raw] at hc; exact hc
    c0_hsplit; rotate_left
    · c0_hsteps; exact hJ3 (n, tot, ch, ()) m1 ⟨s1, rfl, hs1, hn1, htot1, hcap1, hpres1, hm1⟩
    have hlen_le : len.toNat ≤ s.core.wlen - off.toNat := by
      rw [hoff_raw, hlen_raw] at hc
      (try rw [Nat.mod_eq_of_lt (by omega : s.core.wlen < 2 ^ 64)] at hc)
      omega
    c0_hsteps_nogrp
    refine wp_loop_safety_slice_pure (fullSafetySlice c) s1 R
      (fun s4 (n4, tot4, ch4, k, ()) =>
        off.toNat ≤ k.toNat ∧ k.toNat ≤ off.toNat + len.toNat ∧
        n4.toNat ≤ c.scratch_cap ∧ tot4.toNat ≤ c.scratch_cap ∧
        2200 + 5 * n4.toNat + tot4.toNat ≤ c.scratch_cap ∧ FullExtScratchPres s s4)
      (fun (_, _, _, k, ()) => off.toNat + len.toNat - k.toNat)
      (fun J4 hJ4 => by
        c0_hsteps; exact hJ4 s1 (n, tot, ch, off, ()) m1 hm1 rfl hs1
          ⟨Nat.le_refl _, by omega, hn1, htot1, hcap1, hpres1⟩)
      (fun J4 s4 (n4, tot4, ch4, k, ()) m4 hcore4 hs4
          ⟨hk_lo, hk_hi, hn4, htot4, hcap4, hpres4⟩ hm4 hJ4 => ?_)
    dsimp only [fullSafetySlice] at hs4 hm4
    have hceq4 : s4.core = s.core := Eq.trans hcore4 hceq1
    c0_hsplit; rotate_left
    · c0_hsteps; exact hJ3 (n4, tot4, ch4, ()) m4 ⟨s4, hcore4, hs4, hn4, htot4, hcap4, hpres4, hm4⟩
    have hk_lt : k.toNat < off.toNat + len.toNat := by
      rw [hoff_raw, hlen_raw] at hc
      try rw [Nat.mod_eq_of_lt (by omega : off.toNat + len.toNat < 2 ^ 64)] at hc; exact hc
    c0_hsplit
    · c0_hsteps; exact hJ3 (n4, tot4, ch4, ()) m4 ⟨s4, hcore4, hs4, hn4, htot4, hcap4, hpres4, hm4⟩
    have hk_ws : k.toNat < s4.core.wstk.length := by rw [hceq4, hwsl]; omega
    have hk1 : (k + 1#64).toNat = k.toNat + 1 := w1_add1 (by omega)
    c0_hsteps_nogrp
    let w4 := s4.core.wstk[k.toNat]'hk_ws
    have hl_v4 : l.toNat < s4.core.vals.length := by rw [hceq4, hvl]; omega
    refine wp_join_group (ts := [i64, i64, .bool, i64])
      (fun (n5, tot5, ch5, k5, ()) m5 => ∃ s5 : FullState,
        PreservesCoreSlice FullState.core s4 s5 ∧ s5.LengthsOk c ∧
        k.toNat < k5.toNat ∧ k5.toNat ≤ off.toNat + len.toNat ∧
        n5.toNat ≤ c.scratch_cap ∧ tot5.toNat ≤ c.scratch_cap ∧
        2200 + 5 * n5.toNat + tot5.toNat ≤ c.scratch_cap ∧ FullExtScratchPres s s5 ∧
        (FullMem c s5 ⋆ R) m5)
      (fun _ ⟨n5, tot5, ch5, k5, ⟨⟩⟩ m5
          ⟨s5, hcore5, hs5, hk5_gt, hk5_hi, hn5, htot5, hcap5, hpres5, hm5⟩ => by
        c0_hsteps; exact hJ4 s5 (n5, tot5, ch5, k5, ()) m5 hm5 (by dsimp only; omega) hcore5 hs5
          ⟨by omega, hk5_hi, hn5, htot5, hcap5, hpres5⟩)
      (fun J5 hJ5 => ?_)
    c0_hsplit
    · refine wp_join_group (ts := [i64, i64, .bool])
        (fun (n6, tot6, _, ()) m6 => PCol s4 n6 tot6 m6)
        (fun _ ⟨n6, tot6, ch6, ⟨⟩⟩ m6 ⟨s6, hcore6, hs6, hn6, htot6, hcap6, hpres6, hm6⟩ => by
          c0_hsteps; exact hJ5 (n6, tot6, ch6, k + 1#64, ()) m6
            ⟨s6, hcore6, hs6, by omega, by omega, hn6, htot6, hcap6, hpres6, hm6⟩)
        (fun J6 hJ6 => ?_)
      c0_hsplit; rotate_left
      · c0_hsteps; exact hJ6 (n4, tot4, ch4, ()) m4 ⟨s4, rfl, hs4, hn4, htot4, hcap4, hpres4, hm4⟩
      have hot_lt : (w4 &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars := by
        try rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
        try rw [Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hc; exact hc
      c0_hsplit; rotate_left
      · c0_hsteps; exact hJ6 (n4, tot4, ch4, ()) m4 ⟨s4, rfl, hs4, hn4, htot4, hcap4, hpres4, hm4⟩
      have hot_v : ((w4 &&& 0x7FFFFFFF#32).setWidth 64).toNat < s4.core.vals.length := by
        rw [w1_zext32, hceq4, hvl]; omega
      c0_hsplit; rotate_left
      · c0_hsteps; exact hJ6 (n4, tot4, ch4, ()) m4 ⟨s4, rfl, hs4, hn4, htot4, hcap4, hpres4, hm4⟩
      refine wp_join_group (ts := []) (fun () m7 => m4 = m7)
        (fun _ _ m7 hm7 => by
          rcases hm7 with rfl
          refine wp_join_group (ts := [i64, i64, .bool])
            (fun (n8, tot8, _, ()) m8 => PCol s4 n8 tot8 m8)
            (fun _ ⟨n8, tot8, ch8, ⟨⟩⟩ m8 h => by c0_hsteps; exact hJ6 (n8, tot8, ch8, ()) m8 h)
            (fun J8 hJ8 => ?_)
          have hfull4 : J8 (n4, tot4, true, ()) m4 :=
            hJ8 (n4, tot4, true, ()) m4 ⟨s4, rfl, hs4, hn4, htot4, hcap4, hpres4, hm4⟩
          c0_hsplit; · c0_hsteps; exact hfull4
          have hn4p1 : (n4 + 1#64).toNat = n4.toNat + 1 := w1_add1 (by omega)
          have hn4p1_le : n4.toNat + 1 ≤ c.scratch_cap := by
            rw [show (1 : BitVec 64).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (by omega : n4.toNat + 1 < 2 ^ 64)] at hc; omega
          c0_hsplit; · c0_hsteps; exact hfull4
          have htot_p2 : (tot4 + 2#64).toNat = tot4.toNat + 2 := by
            rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl,
              Nat.mod_eq_of_lt (by omega)]
          have htot_le2 : tot4.toNat + 2 ≤ c.scratch_cap := by
            rw [show (2 : BitVec 64).toNat = 2 from rfl,
              Nat.mod_eq_of_lt (by omega : tot4.toNat + 2 < 2 ^ 64)] at hc; omega
          c0_hsplit; · c0_hsteps; exact hfull4
          have hcap_new2 : 2200 + 5 * (n4.toNat + 1) + (tot4.toNat + 2) ≤ c.scratch_cap := by
            rw [show (2200 : BitVec 64).toNat = 2200 from rfl,
              show (5 : BitVec 64).toNat = 5 from rfl, show (1 : BitVec 64).toNat = 1 from rfl,
              show (2 : BitVec 64).toNat = 2 from rfl,
              Nat.mod_eq_of_lt (by omega : n4.toNat + 1 < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega :
                2200 + 5 * (n4.toNat + 1) + tot4.toNat + 2 < 2 ^ 64)] at hc; omega
          have hsbl4 := hs4.scratch_ok.scratch_buf_len
          have hi0_eq := w1_2200_2n (n := n4) (by omega)
          have hi1_eq := w1_2200_2n1 (n := n4) (by omega)
          have hi0_lt : (2200#64 + (n4 <<< (1 : Nat))).toNat < s4.scratch.scratch_buf.length := by
            rw [hi0_eq, hsbl4]; omega
          have hi1_lt : (2200#64 + (n4 <<< (1 : Nat)) + 1#64).toNat <
              (s4.scratch.scratch_buf.set (2200#64 + (n4 <<< (1 : Nat))).toNat
                (l.setWidth 32 ||| 0x80000000#32)).length := by
            rw [List.length_set, hi1_eq, hsbl4]; omega
          c0_hsteps
          exact hJ8 (n4 + 1#64, tot4 + 2#64, ch4, ()) _
            ⟨{ s4 with scratch := { s4.scratch with
                scratch_buf := (s4.scratch.scratch_buf.set (2200#64 + (n4 <<< (1 : Nat))).toNat
                  (l.setWidth 32 ||| 0x80000000#32)).set
                  (2200#64 + (n4 <<< (1 : Nat)) + 1#64).toNat (w4 &&& 0x7FFFFFFF#32) } },
              rfl, w1_len_sb (w1_len_sb hs4), by rw [hn4p1]; exact hn4p1_le,
              by rw [htot_p2]; exact htot_le2, by rw [hn4p1, htot_p2]; exact hcap_new2,
              ⟨hpres4.1, hpres4.2⟩, hm⟩)
        (fun J7 hJ7 => by
          c0_hsplit; · c0_hsteps; exact hJ7 () m4 rfl
          c0_hsplit; · c0_hsteps; exact hJ7 () m4 rfl
          · c0_hsteps; exact hJ6 (n4, tot4, ch4, ()) m4
              ⟨s4, rfl, hs4, hn4, htot4, hcap4, hpres4, hm4⟩)
    · refine wp_join_group (ts := [i64])
        (fun (k6, ()) m6 => m4 = m6 ∧ k.toNat < k6.toNat ∧ k6.toNat ≤ off.toNat + len.toNat)
        (fun _ ⟨k6, ⟨⟩⟩ m6 ⟨hm6, h1, h2⟩ => by
          rcases hm6 with rfl; c0_hsteps
          exact hJ5 (n4, tot4, ch4, k6, ()) m4
            ⟨s4, rfl, hs4, h1, h2, hn4, htot4, hcap4, hpres4, hm4⟩)
        (fun J6 hJ6 => by
          c0_hsplit
          · have hk2_eq : (k + 1#64 + 1#64).toNat = k.toNat + 2 := by
              rw [BitVec.toNat_add, hk1, show (1#64 : BitVec 64).toNat = 1 from rfl,
                Nat.mod_eq_of_lt (by omega)]
            have hk2_le : k.toNat + 2 ≤ off.toNat + len.toNat := by
              rw [hoff_raw, hlen_raw, show (1 : BitVec 64).toNat = 1 from rfl,
                Nat.mod_eq_of_lt (by omega : k.toNat + 1 < 2 ^ 64),
                Nat.mod_eq_of_lt (by omega : off.toNat + len.toNat < 2 ^ 64)] at hc; omega
            c0_hsteps; exact hJ6 (k + 1#64 + 1#64, ()) m4 ⟨rfl, by omega, by omega⟩
          · c0_hsteps; exact hJ6 (k + 1#64, ()) m4 ⟨rfl, by omega, by omega⟩)

/-! ## 3. `full_walk_build_occ_m7_step13_wp` (`step13WalkBuildOccSpec`) -/

/-- Step-13 `full_walk_build_occ_m7` satisfies `step13WalkBuildOccSpec`: preserves
`FullExtScratchPres`, `WalkScrPrefixPres` (all `scratch_buf` writes have index `≥ 2200`),
and bounds `ulen ≤ ncl`. -/
theorem full_walk_build_occ_m7_step13_wp (Γ : Env) :
    ∀ a m Q X, step13WalkBuildOccSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.full_walk_build_occ_m7_body a m Q X := by
  rintro ⟨h, ncl, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  dsimp only [Func.wp, FullFidelityStep13S3.full_walk_build_occ_m7_body]
  have hmax := c.hmaxv; have haca := c.harena; have hscr := c.hscr
  unfold dimacsBound at hmax haca hscr
  have hcv_le := hlen.core_ok.cur_vars_le; have harl := hlen.core_ok.arena_len_arr
  have hale := hlen.core_ok.arena_len_le; have hvl := hlen.core_ok.vals_len
  have hret0 : Q (0#64, ()) m :=
    hQ (0#64, ()) s m rfl hlen ⟨w1_ext_refl s, walkScrPrefixPres_refl s, Nat.zero_le _⟩ hm
  c0_hsplit; · c0_hsteps; exact hret0
  have hcv_pos : 0 < s.core.cur_vars := Nat.pos_of_ne_zero fun h0 => hc (by rw [h0]; rfl)
  c0_hsplit; · c0_hsteps; exact hret0
  c0_hsplit; · c0_hsteps; exact hret0
  have hncl_pos : 0 < ncl.toNat := Nat.pos_of_ne_zero fun h0 =>
    hc (BitVec.eq_of_toNat_eq (by simpa using h0))
  c0_hsplit; · c0_hsteps; exact hret0
  have hncl_le : ncl.toNat ≤ c.scratch_cap := by
    rw [Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64)] at hc; omega
  c0_hsplit; · c0_hsteps; exact hret0
  have hcap_ok : 2200 + 5 * ncl.toNat ≤ c.scratch_cap := by
    rw [show (2200 : BitVec 64).toNat = 2200 from rfl, show (5 : BitVec 64).toNat = 5 from rfl,
      Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 2200 + 5 * ncl.toNat < 2 ^ 64)] at hc; omega
  have h2cv_eq : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, bv64_ofNat_toNat (by omega), Nat.shiftLeft_eq]; omega
  let v21 := 2200#64 + (ncl <<< (1 : Nat))
  let v22 := v21 + ncl; let v23 := v22 + ncl; let v24 := v23 + ncl
  let v25 := BitVec.ofNat 64 c.scratch_cap - v24
  obtain ⟨hv21, hv22, hv23, hv24, hv25⟩ := w1_v21_to_v25 hcap_ok hscr
  c0_hsteps_nogrp
  -- Pass 1: count occurrences & sat counts (`ci < ncl`)
  refine wp_loop_safety_slice_pure (fullSafetySlice c) s R
    (fun s1 (ulen, ci, ()) => ulen.toNat ≤ ncl.toNat ∧ ci.toNat ≤ ncl.toNat ∧
      FullExtScratchPres s s1 ∧ WalkScrPrefixPres s s1)
    (fun (_, ci, ()) => ncl.toNat - ci.toNat)
    (fun J0 hJ0 => by
      c0_hsteps; exact hJ0 s (0#64, 0#64, ()) m hm rfl hlen
        ⟨Nat.zero_le _, Nat.zero_le _, w1_ext_refl s, walkScrPrefixPres_refl s⟩)
    (fun J0 s1 (ulen, ci, ()) m1 hcore1 hs1 ⟨hulen_le, hci_le, hpres1, hpre1⟩ hm1 hJ0 => ?_)
  dsimp only [fullSafetySlice] at hs1 hm1; have hceq1 : s1.core = s.core := hcore1
  c0_hsplit
  · have hci_lt : ci.toNat < ncl.toNat := hc
    obtain ⟨hi0_sb, hi1_sb, he0_def, he1_def⟩ :=
      w1_ci_sb_defs hs1.scratch_ok.scratch_buf_len hcap_ok hscr hci_lt
    c0_hsteps_nogrp
    let e0 := s1.scratch.scratch_buf[(2200#64 + (ci <<< (1 : Nat))).toNat]'hi0_sb
    let e1 := s1.scratch.scratch_buf[(2200#64 + (ci <<< (1 : Nat)) + 1#64).toNat]'hi1_sb
    refine wp_join_group (ts := [i32]) (fun (_, ()) m2 => W1BuildPost c s s1 R m2)
      (fun _ ⟨sat, ⟨⟩⟩ m2 ⟨s2, hcore2, hs2, hpres2, hpre2, hm2⟩ => by
        have hv21_ci : (v21 + ci).toNat = 2200 + 2 * ncl.toNat + ci.toNat := by
          rw [w1_add2 (by rw [hv21]; omega), hv21]
        have hsbl2 := hs2.scratch_ok.scratch_buf_len
        have hv21_sb : (v21 + ci).toNat < s2.scratch.scratch_buf.length := by
          rw [hv21_ci, hsbl2]; omega
        c0_hsteps_nogrp
        let s3 : FullState := { s2 with scratch :=
          { s2.scratch with scratch_buf := s2.scratch.scratch_buf.set (v21 + ci).toNat sat } }
        have hs3 : s3.LengthsOk c := w1_len_sb hs2
        have hpre3 : WalkScrPrefixPres s s3 :=
          walkScrPrefixPres_trans hpre2 (walkScrPrefixPres_set_ge (by rw [hv21_ci]; omega))
        refine wp_join_group (ts := [i64])
          (fun (ulen', ()) m4 => ulen'.toNat ≤ ncl.toNat ∧ W1BuildPost c s s3 R m4)
          (fun _ ⟨ulen', ⟨⟩⟩ m4 ⟨hu4, s4, hcore4, hs4, hpres4, hpre4, hm4⟩ => by
            have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := w1_add1 (by omega)
            c0_hsteps; exact hJ0 s4 (ulen', ci + 1#64, ()) m4 hm4 (by dsimp only; omega)
              (Eq.trans hcore4 hcore2) hs4 ⟨hu4, by rw [hci1]; omega, hpres4, hpre4⟩)
          (fun J2 hJ2 => by
            have hsbl3 := hs3.scratch_ok.scratch_buf_len
            have hv22_ci : (v22 + ci).toNat = 2200 + 3 * ncl.toNat + ci.toNat := by
              rw [w1_add2 (by rw [hv22]; omega), hv22]
            have hv22_sb : (v22 + ci).toNat < s3.scratch.scratch_buf.length := by
              rw [hv22_ci, hsbl3]; omega
            refine wp_join_group (ts := []) (fun () m3b => (FullMem c s3 ⋆ R) m3b)
              (fun _ _ m3b hm3b => by
                c0_hsteps
                exact hJ2 (ulen, ()) _ ⟨hulen_le,
                  { s3 with scratch := { s3.scratch with
                      scratch_buf := s3.scratch.scratch_buf.set (v22 + ci).toNat 0xFFFFFFFF#32 } },
                    rfl, w1_len_sb hs3, ⟨hpres2.1, hpres2.2⟩,
                    walkScrPrefixPres_trans hpre3
                      (walkScrPrefixPres_set_ge (by rw [hv22_ci]; omega)), hm⟩)
              (fun J3 hJ3 => by
                c0_hsplit; rotate_left; · c0_hsteps; exact hJ3 () _ hm
                c0_hsplit; rotate_left; · c0_hsteps; exact hJ3 () _ hm
                have hul_lt : ulen.toNat < ncl.toNat := hc
                have hv23_ul : (v23 + ulen).toNat = 2200 + 4 * ncl.toNat + ulen.toNat := by
                  rw [w1_add2 (by rw [hv23]; omega), hv23]
                have hv23_sb : (v23 + ulen).toNat < (s3.scratch.scratch_buf.set
                    (v22 + ci).toNat (ulen.setWidth 32)).length := by
                  rw [List.length_set, hv23_ul, hsbl3]; omega
                have hu1 : (ulen + 1#64).toNat = ulen.toNat + 1 := w1_add1 (by omega)
                c0_hsteps
                have hp22 := walkScrPrefixPres_set_ge (s := s3) (idx := (v22 + ci).toNat)
                  (v := ulen.setWidth 32) (by rw [hv22_ci]; omega)
                have hp23 := walkScrPrefixPres_set_ge
                  (s := { s3 with scratch := { s3.scratch with
                    scratch_buf := s3.scratch.scratch_buf.set (v22 + ci).toNat
                      (ulen.setWidth 32) } })
                  (idx := (v23 + ulen).toNat) (v := ci.setWidth 32) (by rw [hv23_ul]; omega)
                exact hJ2 (ulen + 1#64, ()) _ ⟨by rw [hu1]; omega,
                  { s3 with scratch := { s3.scratch with
                      scratch_buf := (s3.scratch.scratch_buf.set (v22 + ci).toNat
                        (ulen.setWidth 32)).set (v23 + ulen).toNat (ci.setWidth 32) } },
                    rfl, w1_len_sb (w1_len_sb hs3), ⟨hpres2.1, hpres2.2⟩,
                    walkScrPrefixPres_trans hpre3 (walkScrPrefixPres_trans hp22 hp23), hm⟩)))
      (fun J1 hJ1 => ?_)
    c0_hsplit
    · -- Pass 1 binary
      let la := e0 &&& 0x7FFFFFFF#32
      refine wp_join_group (ts := [i32]) (fun (_, ()) mA => W1BuildPost c s s1 R mA)
        (fun _ ⟨satA, ⟨⟩⟩ mA ⟨sA, hcoreA, hsA, hpresA, hpreA, hmA⟩ => by
          have hceqA : sA.core = s.core := Eq.trans hcoreA hceq1
          refine wp_join_group (ts := [i32]) (fun (_, ()) mB => W1BuildPost c s sA R mB)
            (fun _ ⟨satB, ⟨⟩⟩ mB ⟨sB, hcoreB, hsB, hpresB, hpreB, hmB⟩ => by
              c0_hsteps; exact hJ1 (satB, ()) mB
                ⟨sB, Eq.trans hcoreB hcoreA, hsB, hpresB, hpreB, hmB⟩)
            (fun J3 hJ3 => by
              c0_hsplit; rotate_left
              · c0_hsteps; exact hJ3 (satA, ()) mA ⟨sA, rfl, hsA, hpresA, hpreA, hmA⟩
              have he1_lt : e1.toNat < 2 * s.core.cur_vars :=
                w1_lit_lt_2cv hcv_le hmax (by simpa only [he1_def] using hc)
              have he1_v : (e1.setWidth 64).toNat < sA.core.vals.length := by
                rw [w1_zext32, hceqA, hvl]; omega
              c0_hsplit; rotate_left
              · c0_hsteps; exact hJ3 (satA, ()) mA ⟨sA, rfl, hsA, hpresA, hpreA, hmA⟩
              obtain ⟨he1_tr, he1_wv⟩ := w1_lit_p1_lt hsA hcv_le he1_lt
              c0_hsteps <;> exact hJ3 (_, ()) _ (w1_p1_post hsA hpresA hpreA hm)))
        (fun J2 hJ2 => by
          c0_hsplit; rotate_left
          · c0_hsteps; exact hJ2 (0#32, ()) m1 ⟨s1, rfl, hs1, hpres1, hpre1, hm1⟩
          have hla_lt : la.toNat < 2 * s.core.cur_vars := by
            have him : (2147483647 : BitVec 32) = 0x7FFFFFFF#32 := rfl
            dsimp only [lift2, Arg.val] at hc
            exact w1_lit_lt_2cv hcv_le hmax (by simpa only [he0_def, him, la, e0] using hc)
          have hla_v : (la.setWidth 64).toNat < s1.core.vals.length := by
            rw [w1_zext32, hceq1, hvl]; omega
          c0_hsplit; rotate_left
          · c0_hsteps; exact hJ2 (0#32, ()) m1 ⟨s1, rfl, hs1, hpres1, hpre1, hm1⟩
          obtain ⟨hla_tr, hla_wv⟩ := w1_lit_p1_lt hs1 hcv_le hla_lt
          c0_hsteps <;> exact hJ2 (_, ()) _ (w1_p1_post hs1 hpres1 hpre1 hm))
    · -- Pass 1 large
      refine wp_join_group (ts := [i32]) (fun (_, ()) m2 => W1BuildPost c s s1 R m2)
        (fun _ ⟨sat, ⟨⟩⟩ m2 h => by c0_hsteps; exact hJ1 (sat, ()) m2 h)
        (fun J2 hJ2 => ?_)
      c0_hsplit; rotate_left
      · c0_hsteps; exact hJ2 (0#32, ()) m1 ⟨s1, rfl, hs1, hpres1, hpre1, hm1⟩
      have he0_3 : e0.toNat + 3 ≤ s.core.arena_len :=
        w1_e0_3_le hale haca (by simpa only [he0_def] using hc)
      have he02_ar := w1_ar_sz_lt (ar := s1.core.arena) (by rw [hceq1, harl]) hale haca he0_3
      c0_hsteps_nogrp
      let sz := s1.core.arena[(e0.setWidth 64 + 2#64).toNat]'he02_ar
      have hsz_def := w1_ar_sz_def (by rw [hceq1, harl]) hale haca he0_3 he02_ar
      refine wp_join_group (ts := [i32]) (fun (_, ()) m2 => W1BuildPost c s s1 R m2)
        (fun _ ⟨sat, ⟨⟩⟩ m2 h => by c0_hsteps; exact hJ2 (sat, ()) m2 h)
        (fun J3 hJ3 => ?_)
      c0_hsplit; rotate_left
      · c0_hsteps; exact hJ3 (0#32, ()) m1 ⟨s1, rfl, hs1, hpres1, hpre1, hm1⟩
      c0_hsplit; rotate_left
      · c0_hsteps; exact hJ3 (0#32, ()) m1 ⟨s1, rfl, hs1, hpres1, hpre1, hm1⟩
      have he0sz : e0.toNat + 3 + sz.toNat ≤ s.core.arena_len :=
        w1_e0_sz_le hale haca (by
          simp only [he0_def] at hc; simpa only [← hsz_def, e0, sz] using hc)
      c0_hsteps_nogrp
      refine wp_loop_safety_slice_pure (fullSafetySlice c) s1 R
        (fun sK (_, k, ()) => k.toNat ≤ sz.toNat ∧ FullExtScratchPres s sK ∧ WalkScrPrefixPres s sK)
        (fun (_, k, ()) => sz.toNat - k.toNat)
        (fun J4 hJ4 => by
          c0_hsteps; exact hJ4 s1 (0#32, 0#32, ()) m1 hm1 rfl hs1 ⟨Nat.zero_le _, hpres1, hpre1⟩)
        (fun J4 sK (satK, k, ()) mK hcoreK hsK ⟨hk_le, hpresK, hpreK⟩ hmK hJ4 => ?_)
      dsimp only [fullSafetySlice] at hsK hmK
      have hceqK : sK.core = s.core := Eq.trans hcoreK hceq1
      c0_hsplit; rotate_left
      · c0_hsteps; exact hJ3 (satK, ()) mK ⟨sK, hcoreK, hsK, hpresK, hpreK, hmK⟩
      have hk_lt : k.toNat < sz.toNat := by simp only [he0_def] at hc; exact hc
      have hk1 : (k + 1#32).toNat = k.toNat + 1 := w1_add1_32 hk_lt
      have hl_ar := w1_ar_lit_lt (ar := sK.core.arena) (e0 := e0) (k := k)
        (by rw [hceqK, harl]) hale haca (by omega)
      c0_hsteps_nogrp
      let lit := sK.core.arena[(e0.setWidth 64 + 3#64 + k.setWidth 64).toNat]'hl_ar
      refine wp_join_group (ts := [i32]) (fun (_, ()) mN => W1BuildPost c s sK R mN)
        (fun _ ⟨satN, ⟨⟩⟩ mN ⟨sN, hcoreN, hsN, hpresN, hpreN, hmN⟩ => by
          c0_hsteps; exact hJ4 sN (satN, k + 1#32, ()) mN hmN (by dsimp only; rw [hk1]; omega)
            hcoreN hsN ⟨by rw [hk1]; omega, hpresN, hpreN⟩)
        (fun J5 hJ5 => by
          have hlit_def := w1_ar_lit_def (ar := sK.core.arena) (e0 := e0) (k := k)
            (by rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
              Nat.mod_eq_of_lt (by omega : e0.toNat + 3 + k.toNat < 2 ^ 64), hceqK, harl]; omega)
            hl_ar (by omega)
          c0_hsplit; rotate_left
          · c0_hsteps; exact hJ5 (satK, ()) mK ⟨sK, rfl, hsK, hpresK, hpreK, hmK⟩
          have hlit_lt : lit.toNat < 2 * s.core.cur_vars :=
            w1_lit_lt_2cv hcv_le hmax (by
              simp only [he0_def] at hc; simpa only [← hlit_def, e0, lit] using hc)
          have hlit_v : (lit.setWidth 64).toNat < sK.core.vals.length := by
            rw [w1_zext32, hceqK, hvl]; omega
          c0_hsplit; rotate_left
          · c0_hsteps; exact hJ5 (satK, ()) mK ⟨sK, rfl, hsK, hpresK, hpreK, hmK⟩
          obtain ⟨hlit_tr, hlit_wv⟩ := w1_lit_p1_lt hsK hcv_le hlit_lt
          c0_hsteps <;> exact hJ5 (_, ()) _ (w1_p1_post hsK hpresK hpreK hm))
  · -- Pass 2: prefix sums (`l < 2 * cur_vars`)
    c0_hsteps_nogrp
    refine wp_loop_safety_slice_pure (fullSafetySlice c) s1 R
      (fun s2 (off, l, ()) => off.toNat ≤ v25.toNat ∧ l.toNat ≤ 2 * s.core.cur_vars ∧
        FullExtScratchPres s s2 ∧ WalkScrPrefixPres s s2)
      (fun (_, l, ()) => 2 * s.core.cur_vars - l.toNat)
      (fun J1 hJ1 => by
        c0_hsteps; exact hJ1 s1 (0#64, 0#64, ()) m1 hm1 rfl hs1
          ⟨Nat.zero_le _, Nat.zero_le _, hpres1, hpre1⟩)
      (fun J1 s2 (off, l, ()) m2 hcore2 hs2 ⟨hoff_le, hl_le, hpres2, hpre2⟩ hm2 hJ1 => ?_)
    dsimp only [fullSafetySlice] at hs2 hm2; have hceq2 : s2.core = s.core := Eq.trans hcore2 hceq1
    c0_hsplit
    · have hl_lt : l.toNat < 2 * s.core.cur_vars := by
        try rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
        try rw [Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hc; exact hc
      have hl_tr : l.toNat < s2.scratch.tarjan_reach.length := by
        rw [hs2.scratch_ok.tarjan_reach_len]; omega
      c0_hsteps_nogrp; let deg := s2.scratch.tarjan_reach[l.toNat]'hl_tr
      refine wp_join_group (ts := [i64]) (fun (off_c, ()) ma => m2 = ma ∧ off_c.toNat ≤ v25.toNat)
        (fun _ ⟨off_c, ⟨⟩⟩ ma ⟨hma, hoffc_le⟩ => by
          rcases hma with rfl
          refine wp_join_group (ts := [i64])
            (fun (taken, ()) m3 => off_c.toNat + taken.toNat ≤ v25.toNat ∧ W1BuildPost c s s2 R m3)
            (fun _ ⟨taken, ⟨⟩⟩ m3 ⟨htot_le, s3, hcore3, hs3, hpres3, hpre3, hm3⟩ => by
              have hl_tmk : l.toNat < s3.scratch.tarjan_mark.length := by
                rw [hs3.scratch_ok.tarjan_mark_len]; omega
              have hl_wsrt : l.toNat < s3.scratch.wsort.length := by
                rw [hs3.scratch_ok.wsort_len]; omega
              have hl1 : (l + 1#64).toNat = l.toNat + 1 := w1_add1 (by omega)
              have hoff1 : (off_c + taken).toNat = off_c.toNat + taken.toNat := by
                rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
              dsimp only; c0_hsteps
              exact hJ1 _ (off_c + taken, l + 1#64, ()) _ hm (by dsimp only; omega) hcore3
                (w1_len_ws (w1_len_tm hs3)) ⟨by rw [hoff1]; exact htot_le, by rw [hl1]; omega,
                  ⟨hpres3.1, hpres3.2⟩, hpre3⟩)
            (fun J3 hJ3 => by
              have hrem : (v25 - off_c).toNat = v25.toNat - off_c.toNat := by
                rw [BitVec.toNat_sub]; omega
              c0_hsplit
              · c0_hsteps; exact hJ3 (v25 - off_c, ()) _
                  ⟨by rw [hrem]; omega, w1_p1_post hs2 hpres2 hpre2 hm⟩
              · have hdeg_le : deg.toNat ≤ v25.toNat - off_c.toNat := by
                  rw [hv25]; exact w1_p2_deg_le hcap_ok hscr (hv25 ▸ hoffc_le) hc
                c0_hsteps; exact hJ3 (deg.setWidth 64, ()) m2
                  ⟨by rw [w1_zext32]; omega, s2, rfl, hs2, hpres2, hpre2, hm2⟩))
        (fun J2 hJ2 => by
          c0_hsplit
          · c0_hsteps; exact hJ2 (v25, ()) m2 ⟨rfl, Nat.le_refl _⟩
          · c0_hsteps; exact hJ2 (off, ()) m2 ⟨rfl, hoff_le⟩)
    · -- Pass 3: populate CSR occurrence array (`ci < ncl`)
      c0_hsteps_nogrp
      refine wp_loop_safety_slice_pure (fullSafetySlice c) s2 R
        (fun s3 (ci, ()) => ci.toNat ≤ ncl.toNat ∧ FullExtScratchPres s s3 ∧ WalkScrPrefixPres s s3)
        (fun (ci, ()) => ncl.toNat - ci.toNat)
        (fun J2 hJ2 => by
          c0_hsteps; exact hJ2 s2 (0#64, ()) m2 hm2 rfl hs2 ⟨Nat.zero_le _, hpres2, hpre2⟩)
        (fun J2 s3 (ci, ()) m3 hcore3 hs3 ⟨hci_le, hpres3, hpre3⟩ hm3 hJ2 => ?_)
      dsimp only [fullSafetySlice] at hs3 hm3
      have hceq3 : s3.core = s.core := Eq.trans hcore3 hceq2
      c0_hsplit; rotate_left
      · c0_hsteps; exact hQ (ulen, ()) s3 m3 hceq3 hs3 ⟨hpres3, hpre3, hulen_le⟩ hm3
      have hci_lt : ci.toNat < ncl.toNat := hc
      obtain ⟨hi0_sb, hi1_sb, he0_def, he1_def⟩ :=
        w1_ci_sb_defs hs3.scratch_ok.scratch_buf_len hcap_ok hscr hci_lt
      c0_hsteps_nogrp
      let e0 := s3.scratch.scratch_buf[(2200#64 + (ci <<< (1 : Nat))).toNat]'hi0_sb
      let e1 := s3.scratch.scratch_buf[(2200#64 + (ci <<< (1 : Nat)) + 1#64).toNat]'hi1_sb
      refine wp_join_group (ts := []) (fun () m4 => W1BuildPost c s s3 R m4)
        (fun _ _ m4 ⟨s4, hcore4, hs4, hpres4, hpre4, hm4⟩ => by
          have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := w1_add1 (by omega)
          c0_hsteps; exact hJ2 s4 (ci + 1#64, ()) m4 hm4 (by dsimp only; omega) hcore4 hs4
            ⟨by rw [hci1]; omega, hpres4, hpre4⟩)
        (fun J3 hJ3 => ?_)
      c0_hsplit
      · -- Pass 3 binary
        let la := e0 &&& 0x7FFFFFFF#32
        refine wp_join_group (ts := []) (fun () m4 => W1BuildPost c s s3 R m4)
          (fun _ _ m4 ⟨s4, hcore4, hs4, hpres4, hpre4, hm4⟩ => by
            have hceq4 : s4.core = s.core := Eq.trans hcore4 hceq3
            refine wp_join_group (ts := []) (fun () m5 => W1BuildPost c s s4 R m5)
              (fun _ _ m5 ⟨s5, hcore5, hs5, hpres5, hpre5, hm5⟩ => by
                c0_hsteps; exact hJ3 () m5 ⟨s5, Eq.trans hcore5 hcore4, hs5, hpres5, hpre5, hm5⟩)
              (fun J5 hJ5 => by
                c0_hsplit; rotate_left
                · c0_hsteps; exact hJ5 () m4 ⟨s4, rfl, hs4, hpres4, hpre4, hm4⟩
                have he1_lt : e1.toNat < 2 * s.core.cur_vars :=
                  w1_lit_lt_2cv hcv_le hmax (by simpa only [he1_def] using hc)
                have he1_v : (e1.setWidth 64).toNat < s4.core.vals.length := by
                  rw [w1_zext32, hceq4, hvl]; omega
                c0_hsplit; rotate_left
                · c0_hsteps; exact hJ5 () m4 ⟨s4, rfl, hs4, hpres4, hpre4, hm4⟩
                obtain ⟨he1_ws1, he1_tmk, he1_tr⟩ := w1_lit_p3_lt hs4 hcv_le he1_lt
                c0_hsteps_nogrp
                let cur := (s4.scratch.wsort[(e1.setWidth 64).toNat]'he1_ws1).setWidth 64
                refine wp_join_group (ts := []) (fun () m5 => W1BuildPost c s s4 R m5)
                  (fun _ _ m5 h => by c0_hsteps; exact hJ5 () m5 h)
                  (fun J6 hJ6 => by
                    c0_hsplit; rotate_left
                    · c0_hsteps; exact hJ6 () m4 ⟨s4, rfl, hs4, hpres4, hpre4, hm4⟩
                    c0_hsplit; rotate_left
                    · c0_hsteps; exact hJ6 () m4 ⟨s4, rfl, hs4, hpres4, hpre4, hm4⟩
                    have hcur_32 : cur.toNat < 2 ^ 32 := by
                      dsimp only [cur]; rw [w1_zext32]; exact BitVec.isLt _
                    have hcur_eq : (v24 + cur).toNat = 2200 + 5 * ncl.toNat + cur.toNat := by
                      rw [w1_add2 (by rw [hv24]; omega), hv24]
                    have hcur_sb : (v24 + cur).toNat < s4.scratch.scratch_buf.length := by
                      rw [hcur_eq, hs4.scratch_ok.scratch_buf_len]
                      exact w1_p3_cur_lt hcap_ok hscr hcur_32 (by simpa only [he1_def, cur,
                        w1_zext32] using hc)
                    c0_hsteps; exact hJ6 () _ (w1_p3_post hs4 hpres4 hpre4 hcur_eq hm))))
          (fun J4 hJ4 => by
            c0_hsplit; rotate_left; · c0_hsteps; exact hJ4 () m3 ⟨s3, rfl, hs3, hpres3, hpre3, hm3⟩
            have hla_lt : la.toNat < 2 * s.core.cur_vars := by
              have him : (2147483647 : BitVec 32) = 0x7FFFFFFF#32 := rfl
              dsimp only [lift2, Arg.val] at hc
              exact w1_lit_lt_2cv hcv_le hmax (by simpa only [he0_def, him, la, e0] using hc)
            have hla_v : (la.setWidth 64).toNat < s3.core.vals.length := by
              rw [w1_zext32, hceq3, hvl]; omega
            c0_hsplit; rotate_left; · c0_hsteps; exact hJ4 () m3 ⟨s3, rfl, hs3, hpres3, hpre3, hm3⟩
            obtain ⟨hla_ws1, hla_tmk, hla_tr⟩ := w1_lit_p3_lt hs3 hcv_le hla_lt
            c0_hsteps_nogrp
            let cur := (s3.scratch.wsort[(la.setWidth 64).toNat]'hla_ws1).setWidth 64
            refine wp_join_group (ts := []) (fun () m4 => W1BuildPost c s s3 R m4)
              (fun _ _ m4 h => by c0_hsteps; exact hJ4 () m4 h)
              (fun J5 hJ5 => by
                c0_hsplit; rotate_left
                · c0_hsteps; exact hJ5 () m3 ⟨s3, rfl, hs3, hpres3, hpre3, hm3⟩
                c0_hsplit; rotate_left
                · c0_hsteps; exact hJ5 () m3 ⟨s3, rfl, hs3, hpres3, hpre3, hm3⟩
                have hcur_32 : cur.toNat < 2 ^ 32 := by
                  dsimp only [cur]; rw [w1_zext32]; exact BitVec.isLt _
                have hcur_eq : (v24 + cur).toNat = 2200 + 5 * ncl.toNat + cur.toNat := by
                  rw [w1_add2 (by rw [hv24]; omega), hv24]
                have hcur_sb : (v24 + cur).toNat < s3.scratch.scratch_buf.length := by
                  rw [hcur_eq, hs3.scratch_ok.scratch_buf_len]
                  exact w1_p3_cur_lt hcap_ok hscr hcur_32 (by
                    have him : (2147483647 : BitVec 32) = 0x7FFFFFFF#32 := rfl
                    dsimp only [lift2, Arg.val] at hc
                    simpa only [he0_def, him, cur, la, e0, w1_zext32] using hc)
                c0_hsteps; exact hJ5 () _ (w1_p3_post hs3 hpres3 hpre3 hcur_eq hm)))
      · -- Pass 3 large
        refine wp_join_group (ts := []) (fun () m4 => W1BuildPost c s s3 R m4)
          (fun _ _ m4 h => by c0_hsteps; exact hJ3 () m4 h)
          (fun J4 hJ4 => ?_)
        c0_hsplit; rotate_left; · c0_hsteps; exact hJ4 () m3 ⟨s3, rfl, hs3, hpres3, hpre3, hm3⟩
        have he0_3 : e0.toNat + 3 ≤ s.core.arena_len :=
          w1_e0_3_le hale haca (by simpa only [he0_def] using hc)
        have he02_ar := w1_ar_sz_lt (ar := s3.core.arena) (by rw [hceq3, harl]) hale haca he0_3
        c0_hsteps_nogrp
        let sz := s3.core.arena[(e0.setWidth 64 + 2#64).toNat]'he02_ar
        have hsz_def := w1_ar_sz_def (by rw [hceq3, harl]) hale haca he0_3 he02_ar
        refine wp_join_group (ts := []) (fun () m4 => W1BuildPost c s s3 R m4)
          (fun _ _ m4 h => by c0_hsteps; exact hJ4 () m4 h)
          (fun J5 hJ5 => ?_)
        c0_hsplit; rotate_left; · c0_hsteps; exact hJ5 () m3 ⟨s3, rfl, hs3, hpres3, hpre3, hm3⟩
        c0_hsplit; rotate_left; · c0_hsteps; exact hJ5 () m3 ⟨s3, rfl, hs3, hpres3, hpre3, hm3⟩
        have he0sz : e0.toNat + 3 + sz.toNat ≤ s.core.arena_len :=
          w1_e0_sz_le hale haca (by
            simp only [he0_def] at hc; simpa only [← hsz_def, e0, sz] using hc)
        c0_hsteps_nogrp
        refine wp_loop_safety_slice_pure (fullSafetySlice c) s3 R
          (fun sK (k, ()) => k.toNat ≤ sz.toNat ∧ FullExtScratchPres s sK ∧ WalkScrPrefixPres s sK)
          (fun (k, ()) => sz.toNat - k.toNat)
          (fun J6 hJ6 => by
            c0_hsteps; exact hJ6 s3 (0#32, ()) m3 hm3 rfl hs3 ⟨Nat.zero_le _, hpres3, hpre3⟩)
          (fun J6 sK (k, ()) mK hcoreK hsK ⟨hk_le, hpresK, hpreK⟩ hmK hJ6 => ?_)
        dsimp only [fullSafetySlice] at hsK hmK
        have hceqK : sK.core = s.core := Eq.trans hcoreK hceq3
        c0_hsplit; rotate_left; · c0_hsteps; exact hJ5 () mK ⟨sK, hcoreK, hsK, hpresK, hpreK, hmK⟩
        have hk_lt : k.toNat < sz.toNat := by simp only [he0_def] at hc; exact hc
        have hk1 : (k + 1#32).toNat = k.toNat + 1 := w1_add1_32 hk_lt
        have hl_ar := w1_ar_lit_lt (ar := sK.core.arena) (e0 := e0) (k := k)
          (by rw [hceqK, harl]) hale haca (by omega)
        c0_hsteps_nogrp
        let lit := sK.core.arena[(e0.setWidth 64 + 3#64 + k.setWidth 64).toNat]'hl_ar
        refine wp_join_group (ts := []) (fun () mN => W1BuildPost c s sK R mN)
          (fun _ _ mN ⟨sN, hcoreN, hsN, hpresN, hpreN, hmN⟩ => by
            c0_hsteps; exact hJ6 sN (k + 1#32, ()) mN hmN (by dsimp only; rw [hk1]; omega)
              hcoreN hsN ⟨by rw [hk1]; omega, hpresN, hpreN⟩)
          (fun J7 hJ7 => by
            have hlit_def := w1_ar_lit_def (ar := sK.core.arena) (e0 := e0) (k := k)
              (by rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                Nat.mod_eq_of_lt (by omega : e0.toNat + 3 + k.toNat < 2 ^ 64), hceqK, harl]; omega)
              hl_ar (by omega)
            c0_hsplit; rotate_left; · c0_hsteps; exact hJ7 () mK ⟨sK, rfl, hsK, hpresK, hpreK, hmK⟩
            have hlit_lt : lit.toNat < 2 * s.core.cur_vars :=
              w1_lit_lt_2cv hcv_le hmax (by
                simp only [he0_def] at hc; simpa only [← hlit_def, e0, lit] using hc)
            have hlit_v : (lit.setWidth 64).toNat < sK.core.vals.length := by
              rw [w1_zext32, hceqK, hvl]; omega
            c0_hsplit; rotate_left; · c0_hsteps; exact hJ7 () mK ⟨sK, rfl, hsK, hpresK, hpreK, hmK⟩
            obtain ⟨hlit_ws1, hlit_tmk, hlit_tr⟩ := w1_lit_p3_lt hsK hcv_le hlit_lt
            c0_hsteps_nogrp
            let cur := (sK.scratch.wsort[(lit.setWidth 64).toNat]'hlit_ws1).setWidth 64
            refine wp_join_group (ts := []) (fun () mN => W1BuildPost c s sK R mN)
              (fun _ _ mN h => by c0_hsteps; exact hJ7 () mN h)
              (fun J8 hJ8 => by
                c0_hsplit; rotate_left
                · c0_hsteps; exact hJ8 () mK ⟨sK, rfl, hsK, hpresK, hpreK, hmK⟩
                c0_hsplit; rotate_left
                · c0_hsteps; exact hJ8 () mK ⟨sK, rfl, hsK, hpresK, hpreK, hmK⟩
                have hcur_32 : cur.toNat < 2 ^ 32 := by
                  dsimp only [cur]; rw [w1_zext32]; exact BitVec.isLt _
                have hcur_eq : (v24 + cur).toNat = 2200 + 5 * ncl.toNat + cur.toNat := by
                  rw [w1_add2 (by rw [hv24]; omega), hv24]
                have hcur_sb : (v24 + cur).toNat < sK.scratch.scratch_buf.length := by
                  rw [hcur_eq, hsK.scratch_ok.scratch_buf_len]
                  exact w1_p3_cur_lt hcap_ok hscr hcur_32 (by
                    simp only [he0_def] at hc
                    simpa only [← hlit_def, e0, lit, cur, w1_zext32] using hc)
                c0_hsteps; exact hJ8 () _ (w1_p3_post hsK hpresK hpreK hcur_eq hm)))

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S3
