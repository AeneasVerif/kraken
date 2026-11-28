/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Definition.WpM7DefK6Helpers0

/-!
# M7 `def_k6_m7` Sub-Phase Helpers Part 1 (`Proof.Definition.WpM7DefK6Helpers1`)

Exports:
- `m7_p6_k6_init_solve_wp` (split with `m7_p6_k6_init_lits_wp` so every decl `<= 450` LOC)
- Clean invariant definitions & commit/framing helpers for `full_bve_def_k6_m7_wp`:
  `M7P6OuterInv`, `M7P6ClearInv`, `M7P6SideInv`, `M7P6TmkJoinInv`, `M7P6ScanLargeInv`,
  `m7_p6_teid_exit_commit`, `m7_p6_side_setup`, `m7_p6_bin_unit_commit`, `m7_p6_outer_init`
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Definition

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics K6Tactics P6Tactics

public section

private theorem m6_getElem_congr' {α : Type} {xs : List α} {i j : Nat} (h : i = j)
    (hi : i < xs.length) (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

/-! ## 1. K6 Header/Workspace Initialization Sub-Phase (`m7_p6_k6_init_solve_wp`) -/

private theorem m7_p6_k6_init_lits_wp (Γ : Env) (Q : Post []) (X : XPost)
    (c : FullCfg) (s0 s_clr : FullState) (R : Mem 64 → Prop)
    (pk : BitVec 64) (nv_s nc_s alen_s : BitVec 32)
    (scr_e scr1 : List (BitVec 32)) (m1 : Mem 64) (k_watch : Expr Val Cont [])
    (hpk : pk = c.pScratchBuf + BitVec.ofNat 64 1096 * 4)
    (hsc28 : c.scratch_cap < 2 ^ 28) (h8192 : 8192 ≤ c.scratch_cap)
    (hscre_l : scr_e.length = c.scratch_cap) (hsc1_l : scr1.length = c.scratch_cap)
    (hnv64 : nv_s.toNat ≤ 64) (hnc128 : nc_s.toNat ≤ 128)
    (hal_le : alen_s.toNat ≤ c.scratch_cap - 4008)
    (hpre1 : ∀ k < 1096, scr1[k]? = s0.scratch.scratch_buf[k]?)
    (hs1_1 : scr1[1096 + 1]? = some nc_s) (hs1_2 : scr1[1096 + 2]? = some nc_s)
    (hs1_14 : scr1[1096 + 14]? = some alen_s)
    (hs1_15 : scr1[1096 + 15]? = some (BitVec.ofNat 32 (c.scratch_cap - 4008)))
    (hmeta1 : ∀ k, 1888 ≤ k → k < 2656 → scr1[1096 + k]? = scr_e[1096 + k]?)
    (hcls_e : ∀ cid < nc_s.toNat,
      (scr_e[1096 + 1888 + cid]?.getD 0#32).toNat +
        ((scr_e[1096 + 2144 + cid]?.getD 0#32) &&& 0xFFFF#32).toNat ≤ alen_s.toNat ∧
      ((scr_e[1096 + 2144 + cid]?.getD 0#32) &&& 0x40000000#32) = 0#32)
    (hm1 : (FullMem c { s_clr with scratch := { s_clr.scratch with scratch_buf := scr1 } } ⋆ R)
      m1)
    (hw_wp : ∀ (scr_pre kb_w0 scr2 : List (BitVec 32)) (m_sp : Mem 64),
      scr2.length = c.scratch_cap → scr_pre.length = 1096 → scr_pre = scr2.take 1096 →
      (∀ k < 1024, scr2[k]? = s0.scratch.scratch_buf[k]?) → kb_w0 = scr2.drop 1096 →
      K6BufOk kb_w0 → kb_w0.length = c.scratch_cap - 1096 →
      scr2[1096 + 1]? = some nc_s → scr2[1096 + 2]? = some nc_s →
      (array64 (c.hdr + 32) (hdrTailWords c s_clr) ⋆
        array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 1096 * 4) kb_w0 ⋆
        (array (t := i32) c.pScratchBuf scr_pre ⋆ m7_p6_fullK6Outer c s_clr ⋆ R)) m_sp →
      wp Γ Q X k_watch m_sp) :
    wp Γ Q X
      (Expr.group (fun (L2 : Tup Cont [[i32]]) =>
        Blocks.cons (fun (p : Tup Val [i32]) =>
        Expr.let_ ⟨OpCode.shl i32, (Arg.var nv_s, Arg.imm 1, ())⟩ fun p4 =>
        Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl, (Arg.var p.fst, Arg.var p4.fst, ())⟩
          fun p5 =>
        Expr.jnz (Arg.var p5.fst)
          (Expr.let_ ⟨OpCode.add i32, (Arg.imm 608, Arg.var p.fst, ())⟩ fun p6 =>
           Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p6.fst, ())⟩ fun p7 =>
           Expr.let_ ⟨OpCode.mul i64, (Arg.var p7.fst, Arg.imm 4, ())⟩ fun p8 =>
           Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p8.fst, ())⟩ fun p9 =>
           Expr.store (t := i32) (Arg.imm 0) (Arg.var p9.fst)
             (Expr.let_ ⟨OpCode.add i32, (Arg.imm 736, Arg.var p.fst, ())⟩ fun p10 =>
              Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p10.fst, ())⟩ fun p11 =>
              Expr.let_ ⟨OpCode.mul i64, (Arg.var p11.fst, Arg.imm 4, ())⟩ fun p12 =>
              Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p12.fst, ())⟩ fun p13 =>
              Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p13.fst)
                (Expr.let_ ⟨OpCode.add i32, (Arg.var p.fst, Arg.imm 1, ())⟩ fun pi =>
                 Expr.jump L2.fst (Arg.var pi.fst, ()))))
          k_watch) Blocks.nil)
        fun L2 => Expr.jump L2.fst (Arg.imm 0, ())) m1 := by
  subst hpk
  have hacap_n_eq : (BitVec.ofNat 32 (c.scratch_cap - 4008)).toNat = c.scratch_cap - 4008 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine wp_loop_group (ts := [i32])
    (fun rem2 (i, ()) m2 => ∃ scr2 : List (BitVec 32),
      let s2 : FullState := { s_clr with scratch := { s_clr.scratch with scratch_buf := scr2 } }
      scr2.length = c.scratch_cap ∧ i.toNat ≤ 2 * nv_s.toNat ∧
      rem2 = 2 * nv_s.toNat - i.toNat ∧
      (∀ k < 1096, scr2[k]? = s0.scratch.scratch_buf[k]?) ∧
      scr2[1096 + 1]? = some nc_s ∧ scr2[1096 + 2]? = some nc_s ∧
      scr2[1096 + 14]? = some alen_s ∧
      scr2[1096 + 15]? = some (BitVec.ofNat 32 (c.scratch_cap - 4008)) ∧
      (∀ k, 1888 ≤ k → k < 2656 → scr2[1096 + k]? = scr_e[1096 + k]?) ∧
      (FullMem c s2 ⋆ R) m2) ?_ ?_
  · rintro L2 rem2 ⟨i, ⟨⟩⟩ m2 hL2
      ⟨scr2, hsc2_l, hi_le, rfl, hpre2, hs2_1, hs2_2, hs2_14, hs2_15, hmeta2, hm2⟩
    c0_hsplit
    · have hi_lt : i.toNat < 2 * nv_s.toNat := by
        rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := m7_p6_add1_toNat (by omega)
      c0_hsteps!
      rw [m7_p6_off_add 608 (by decide) i (by omega),
        m7_p6_off_add 736 (by decide) i (by omega)] at hm
      let scr2' :=
        (scr2.set (1096 + (608 + i.toNat)) 0#32).set (1096 + (736 + i.toNat)) 0xFFFFFFFF#32
      refine hL2 (2 * nv_s.toNat - (i + 1#32).toNat) (i + 1#32, ()) _ (by omega)
        ⟨scr2', by simp [scr2', hsc2_l], by omega, rfl,
          fun k hk => by
            dsimp only [scr2']
            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
            exact hpre2 k hk,
          by dsimp only [scr2']
             rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hs2_1,
          by dsimp only [scr2']
             rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hs2_2,
          by dsimp only [scr2']
             rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
             exact hs2_14,
          by dsimp only [scr2']
             rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
             exact hs2_15,
          fun k hk1 hk2 => by
            dsimp only [scr2']
            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
            exact hmeta2 k hk1 hk2,
          m7_p6_fullMem_subst hm⟩
    · let scr_pre := scr2.take 1096
      let kb_w0 := scr2.drop 1096
      have hpre_l : scr_pre.length = 1096 := List.length_take_of_le (by omega)
      have hkbw0_l : kb_w0.length = c.scratch_cap - 1096 := by simp [kb_w0, hsc2_l]
      have hkbw0_ok : K6BufOk kb_w0 := by
        refine m7_p6_k6BufOk_of_init ?_ ?_ ?_ ?_ fun cid hcid => ?_
        · have h15 := List.getElem?_drop (i := 1096) (j := 15) (xs := scr2)
          change kb_w0[15]? = scr2[1096 + 15]? at h15
          rw [h15, hs2_15, Option.getD_some, hacap_n_eq, hkbw0_l]; omega
        · rw [hkbw0_l]; omega
        · have h1 := List.getElem?_drop (i := 1096) (j := 1) (xs := scr2)
          change kb_w0[1]? = scr2[1096 + 1]? at h1
          rw [h1, hs2_1, Option.getD_some]; exact hnc128
        · have h14 := List.getElem?_drop (i := 1096) (j := 14) (xs := scr2)
          have h15 := List.getElem?_drop (i := 1096) (j := 15) (xs := scr2)
          change kb_w0[14]? = scr2[1096 + 14]? at h14
          change kb_w0[15]? = scr2[1096 + 15]? at h15
          rw [h14, h15, hs2_14, hs2_15, Option.getD_some, Option.getD_some, hacap_n_eq]
          exact hal_le
        · have h1 := List.getElem?_drop (i := 1096) (j := 1) (xs := scr2)
          have h15 := List.getElem?_drop (i := 1096) (j := 15) (xs := scr2)
          have ho := List.getElem?_drop (i := 1096) (j := 1888 + cid) (xs := scr2)
          have hm := List.getElem?_drop (i := 1096) (j := 2144 + cid) (xs := scr2)
          change kb_w0[1]? = scr2[1096 + 1]? at h1
          change kb_w0[15]? = scr2[1096 + 15]? at h15
          change kb_w0[1888 + cid]? = scr2[1096 + (1888 + cid)]? at ho
          change kb_w0[2144 + cid]? = scr2[1096 + (2144 + cid)]? at hm
          rw [h1, hs2_1, Option.getD_some] at hcid
          rw [ho, hm, h15, hs2_15, Option.getD_some, hacap_n_eq,
            hmeta2 (1888 + cid) (by omega) (by omega),
            hmeta2 (2144 + cid) (by omega) (by omega)]
          have hco := hcls_e cid hcid
          rw [show 1096 + 1888 + cid = 1096 + (1888 + cid) from by omega,
            show 1096 + 2144 + cid = 1096 + (2144 + cid) from by omega] at hco
          exact ⟨Nat.le_trans hco.1 hal_le, hco.2⟩
      have hm_sp := m7_p6_fullMem_split_k6 (by rw [hsc2_l]; omega) hm2
      c0_hsteps_nogrp
      exact hw_wp scr_pre kb_w0 scr2 _ hsc2_l hpre_l rfl (fun k hk => hpre2 k (by omega)) rfl
        hkbw0_ok hkbw0_l hs2_1 hs2_2 hm_sp
  · intro L2 hL2; c0_hsteps!
    exact hL2 (2 * nv_s.toNat) (0#32, ()) _
      ⟨scr1, hsc1_l, Nat.zero_le _, rfl, hpre1, hs1_1, hs1_2, hs1_14, hs1_15, hmeta1, hm1⟩

/-- Initializes `22` K6 header words `k[0..21]`, variable arrays `KO_{LVL..QNEXT}`, and literal
arrays `KO_{VALS,WHEAD}` inside `s_clr.scratch.scratch_buf`, splits `FullMem` into `hdr + k`,
and transfers to `hw_wp`. -/
theorem m7_p6_k6_init_solve_wp (Γ : Env) (Q : Post []) (X : XPost)
    (c : FullCfg) (s0 s_clr : FullState) (R : Mem 64 → Prop)
    (pk : BitVec 64) (nv_s nc_s alen_s acap_v nunits_s : BitVec 32)
    (scr_e : List (BitVec 32)) (m_init : Mem 64) (k_watch : Expr Val Cont [])
    (hpk : pk = c.pScratchBuf + BitVec.ofNat 64 1096 * 4)
    (hsc28 : c.scratch_cap < 2 ^ 28) (h8192 : 8192 ≤ c.scratch_cap)
    (hscre_l : scr_e.length = c.scratch_cap)
    (hscre_s : s_clr.scratch.scratch_buf = scr_e)
    (hnv_pos : 0 < nv_s.toNat) (hnv64 : nv_s.toNat ≤ 64)
    (_hnc_ge2 : 2 ≤ nc_s.toNat) (hnc128 : nc_s.toNat ≤ 128)
    (hal_le : alen_s.toNat ≤ c.scratch_cap - 4008)
    (hacap_eq : acap_v = BitVec.ofNat 32 (c.scratch_cap - 4008))
    (hscre_pre : ∀ k < 1096, scr_e[k]? = s0.scratch.scratch_buf[k]?)
    (hcls_e : ∀ cid < nc_s.toNat,
      (scr_e[1096 + 1888 + cid]?.getD 0#32).toNat +
        ((scr_e[1096 + 2144 + cid]?.getD 0#32) &&& 0xFFFF#32).toNat ≤ alen_s.toNat ∧
      ((scr_e[1096 + 2144 + cid]?.getD 0#32) &&& 0x40000000#32) = 0#32)
    (hm_init : (FullMem c s_clr ⋆ R) m_init)
    (hw_wp : ∀ (scr_pre kb_w0 scr2 : List (BitVec 32)) (m_sp : Mem 64),
      scr2.length = c.scratch_cap → scr_pre.length = 1096 → scr_pre = scr2.take 1096 →
      (∀ k < 1024, scr2[k]? = s0.scratch.scratch_buf[k]?) → kb_w0 = scr2.drop 1096 →
      K6BufOk kb_w0 → kb_w0.length = c.scratch_cap - 1096 →
      scr2[1096 + 1]? = some nc_s → scr2[1096 + 2]? = some nc_s →
      (array64 (c.hdr + 32) (hdrTailWords c s_clr) ⋆
        array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 1096 * 4) kb_w0 ⋆
        (array (t := i32) c.pScratchBuf scr_pre ⋆ m7_p6_fullK6Outer c s_clr ⋆ R)) m_sp →
      wp Γ Q X k_watch m_sp) :
    wp Γ Q X
      (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 0, ())⟩ fun p =>
       Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
       Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p.fst, ())⟩ fun p =>
       Expr.store (t := i32) (Arg.var nv_s) (Arg.var p.fst)
       (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 1, ())⟩ fun p =>
        Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p.fst, ())⟩ fun p =>
        Expr.store (t := i32) (Arg.var nc_s) (Arg.var p.fst)
        (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 2, ())⟩ fun p =>
         Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
         Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p.fst, ())⟩ fun p =>
         Expr.store (t := i32) (Arg.var nc_s) (Arg.var p.fst)
         (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 3, ())⟩ fun p =>
          Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p.fst, ())⟩ fun p =>
          Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
          (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4, ())⟩ fun p =>
           Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
           Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p.fst, ())⟩ fun p =>
           Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
           (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 5, ())⟩ fun p =>
            Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
            Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p.fst, ())⟩ fun p =>
            Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
            (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 6, ())⟩ fun p =>
             Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
             Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p.fst, ())⟩ fun p =>
             Expr.store (t := i32) (Arg.var nv_s) (Arg.var p.fst)
             (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 7, ())⟩ fun p =>
              Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
              Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p.fst, ())⟩ fun p =>
              Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p.fst)
              (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 8, ())⟩ fun p =>
               Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
               Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p.fst, ())⟩ fun p =>
               Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
               (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 9, ())⟩ fun p =>
                Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p.fst, ())⟩ fun p =>
                Expr.let_ ⟨OpCode.sub i32, (Arg.var nv_s, Arg.imm 1, ())⟩ fun ps1 =>
                Expr.store (t := i32) (Arg.var ps1.fst) (Arg.var p.fst)
                (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 10, ())⟩ fun p =>
                 Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                 Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p.fst, ())⟩ fun p =>
                 Expr.let_ ⟨OpCode.sub i32, (Arg.var nv_s, Arg.imm 1, ())⟩ fun ps2 =>
                 Expr.store (t := i32) (Arg.var ps2.fst) (Arg.var p.fst)
                 (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 11, ())⟩ fun p =>
                  Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                  Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p.fst, ())⟩ fun p =>
                  Expr.store (t := i32) (Arg.var nv_s) (Arg.var p.fst)
                  (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 12, ())⟩ fun p =>
                   Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                   Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p.fst, ())⟩ fun p =>
                   Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
                   (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 13, ())⟩ fun p =>
                    Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                    Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p.fst, ())⟩ fun p =>
                    Expr.store (t := i32) (Arg.imm 512) (Arg.var p.fst)
                    (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 14, ())⟩ fun p =>
                     Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                     Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p.fst, ())⟩ fun p =>
                     Expr.store (t := i32) (Arg.var alen_s) (Arg.var p.fst)
                     (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 15, ())⟩ fun p =>
                      Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                      Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p.fst, ())⟩ fun p =>
                      Expr.store (t := i32) (Arg.var acap_v) (Arg.var p.fst)
                      (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 16, ())⟩ fun p =>
                       Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                       Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p.fst, ())⟩ fun p =>
                       Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
                       (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 17, ())⟩ fun p =>
                        Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                        Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p.fst, ())⟩ fun p =>
                        Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
                        (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 18, ())⟩ fun p =>
                         Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                         Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p.fst, ())⟩ fun p =>
                         Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
                         (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 19, ())⟩ fun p =>
                          Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                          Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p.fst, ())⟩ fun p =>
                          Expr.store (t := i32) (Arg.var nunits_s) (Arg.var p.fst)
                          (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 20, ())⟩ fun p =>
                           Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                           Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p.fst, ())⟩ fun p =>
                           Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
                           (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 21, ())⟩ fun p =>
                            Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                            Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p.fst, ())⟩ fun p =>
                            Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
                            (Expr.group (fun (L1 : Tup Cont [[i32]]) =>
                              Blocks.cons (fun (p : Tup Val [i32]) =>
                              Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl,
                                  (Arg.var p.fst, Arg.var nv_s, ())⟩ fun p3 =>
                              Expr.jnz (Arg.var p3.fst)
                                (Expr.let_ ⟨OpCode.add i32, (Arg.imm 32, Arg.var p.fst, ())⟩
                                   fun p4 =>
                                 Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p4.fst, ())⟩ fun p5 =>
                                 Expr.let_ ⟨OpCode.mul i64, (Arg.var p5.fst, Arg.imm 4, ())⟩
                                   fun p6 =>
                                 Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p6.fst, ())⟩
                                   fun p7 =>
                                 Expr.store (t := i32) (Arg.imm 0) (Arg.var p7.fst)
                                   (Expr.let_ ⟨OpCode.add i32, (Arg.imm 96, Arg.var p.fst, ())⟩
                                      fun p8 =>
                                    Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p8.fst, ())⟩ fun p9 =>
                                    Expr.let_ ⟨OpCode.mul i64, (Arg.var p9.fst, Arg.imm 4, ())⟩
                                      fun p10 =>
                                    Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p10.fst, ())⟩
                                      fun p11 =>
                                    Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p11.fst)
                                      (Expr.let_ ⟨OpCode.add i32, (Arg.imm 416, Arg.var p.fst, ())⟩
                                         fun p12 =>
                                       Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p12.fst, ())⟩
                                         fun p13 =>
                                       Expr.let_ ⟨OpCode.mul i64, (Arg.var p13.fst, Arg.imm 4, ())⟩
                                         fun p14 =>
                                       Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p14.fst, ())⟩
                                         fun p15 =>
                                       Expr.store (t := i32) (Arg.imm 0) (Arg.var p15.fst)
                                         (Expr.let_ ⟨OpCode.add i32,
                                             (Arg.imm 288, Arg.var p.fst, ())⟩ fun p16 =>
                                          Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p16.fst, ())⟩
                                            fun p17 =>
                                          Expr.let_ ⟨OpCode.mul i64,
                                              (Arg.var p17.fst, Arg.imm 4, ())⟩ fun p18 =>
                                          Expr.let_ ⟨OpCode.add i64,
                                              (Arg.var pk, Arg.var p18.fst, ())⟩ fun p19 =>
                                          Expr.let_ ⟨OpCode.add i32, (Arg.var p.fst, Arg.imm 1, ())⟩
                                            fun p20 =>
                                          Expr.store (t := i32) (Arg.var p20.fst) (Arg.var p19.fst)
                                            (Expr.let_ ⟨OpCode.add i32,
                                                (Arg.imm 160, Arg.var p.fst, ())⟩ fun p21 =>
                                             Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p21.fst, ())⟩
                                               fun p22 =>
                                             Expr.let_ ⟨OpCode.mul i64,
                                                 (Arg.var p22.fst, Arg.imm 4, ())⟩ fun p23 =>
                                             Expr.let_ ⟨OpCode.add i64,
                                                 (Arg.var pk, Arg.var p23.fst, ())⟩ fun p24 =>
                                             Expr.group (fun (_ : Tup Cont [[i32]]) =>
                                               Blocks.cons (fun p25 =>
                                                 Expr.store (t := i32) (Arg.var p25.fst)
                                                   (Arg.var p24.fst)
                                                   (Expr.let_ ⟨OpCode.add i32,
                                                       (Arg.imm 224, Arg.var p.fst, ())⟩ fun p26 =>
                                                    Expr.let_ ⟨OpCode.zext 32 64,
                                                        (Arg.var p26.fst, ())⟩ fun p27 =>
                                                    Expr.let_ ⟨OpCode.mul i64,
                                                        (Arg.var p27.fst, Arg.imm 4, ())⟩ fun p28 =>
                                                    Expr.let_ ⟨OpCode.add i64,
                                                        (Arg.var pk, Arg.var p28.fst, ())⟩
                                                      fun p29 =>
                                                    Expr.group (fun (_ : Tup Cont [[i32]]) =>
                                                      Blocks.cons (fun p30 =>
                                                        Expr.store (t := i32) (Arg.var p30.fst)
                                                          (Arg.var p29.fst)
                                                          (Expr.let_ ⟨OpCode.add i32,
                                                              (Arg.var p.fst, Arg.imm 1, ())⟩
                                                             fun pi =>
                                                           Expr.jump L1.fst (Arg.var pi.fst, ())))
                                                        Blocks.nil)
                                                      fun Js2 =>
                                                    Expr.let_ ⟨OpCode.add i32,
                                                        (Arg.var p.fst, Arg.imm 1, ())⟩ fun p30 =>
                                                    Expr.let_ ⟨OpCode.cmp CmpOp.uge i32 Ty.bool rfl,
                                                        (Arg.var p30.fst, Arg.var nv_s, ())⟩
                                                      fun p31 =>
                                                    Expr.jnz (Arg.var p31.fst)
                                                      (Expr.jump Js2.fst (Arg.imm 4294967295, ()))
                                                      (Expr.let_ ⟨OpCode.add i32,
                                                          (Arg.var p.fst, Arg.imm 1, ())⟩ fun pi =>
                                                       Expr.jump Js2.fst (Arg.var pi.fst, ()))))
                                                 Blocks.nil)
                                               fun Js1 =>
                                             Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
                                                 (Arg.var p.fst, Arg.imm 0, ())⟩ fun p25 =>
                                             Expr.jnz (Arg.var p25.fst)
                                               (Expr.jump Js1.fst (Arg.imm 4294967295, ()))
                                               (Expr.let_ ⟨OpCode.sub i32,
                                                   (Arg.var p.fst, Arg.imm 1, ())⟩ fun pm1 =>
                                                Expr.jump Js1.fst (Arg.var pm1.fst, ())))))))
                                (Expr.group (fun (L2 : Tup Cont [[i32]]) =>
                                  Blocks.cons (fun (p : Tup Val [i32]) =>
                                  Expr.let_ ⟨OpCode.shl i32, (Arg.var nv_s, Arg.imm 1, ())⟩
                                    fun p4 =>
                                  Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl,
                                      (Arg.var p.fst, Arg.var p4.fst, ())⟩ fun p5 =>
                                  Expr.jnz (Arg.var p5.fst)
                                    (Expr.let_ ⟨OpCode.add i32, (Arg.imm 608, Arg.var p.fst, ())⟩
                                       fun p6 =>
                                     Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p6.fst, ())⟩ fun p7 =>
                                     Expr.let_ ⟨OpCode.mul i64, (Arg.var p7.fst, Arg.imm 4, ())⟩
                                       fun p8 =>
                                     Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p8.fst, ())⟩
                                       fun p9 =>
                                     Expr.store (t := i32) (Arg.imm 0) (Arg.var p9.fst)
                                       (Expr.let_ ⟨OpCode.add i32,
                                           (Arg.imm 736, Arg.var p.fst, ())⟩ fun p10 =>
                                        Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p10.fst, ())⟩
                                          fun p11 =>
                                        Expr.let_ ⟨OpCode.mul i64, (Arg.var p11.fst, Arg.imm 4, ())⟩
                                          fun p12 =>
                                        Expr.let_ ⟨OpCode.add i64,
                                            (Arg.var pk, Arg.var p12.fst, ())⟩ fun p13 =>
                                        Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p13.fst)
                                          (Expr.let_ ⟨OpCode.add i32,
                                              (Arg.var p.fst, Arg.imm 1, ())⟩ fun pi =>
                                            Expr.jump L2.fst (Arg.var pi.fst, ()))))
                                    k_watch) Blocks.nil)
                                  fun L2 => Expr.jump L2.fst (Arg.imm 0, ()))) Blocks.nil)
                              fun L1 => Expr.jump L1.fst
                                (Arg.imm 0, ())))))))))))))))))))))))) m_init := by
  subst hpk hacap_eq
  have hm_scr : (P6Scr c.scratch_cap c.pScratchBuf scr_e ⋆
      (m7_p6_fullWithoutScr c s_clr ⋆ R)) m_init := by
    rw [← hscre_s]
    exact m7_p6_scrBuf_split h8192 (by rw [hscre_s]; exact hscre_l) hm_init
  c0_hsteps!
  let scr_h := m7_p6_scr_h scr_e nv_s nc_s alen_s (BitVec.ofNat 32 (c.scratch_cap - 4008)) nunits_s
  have hhm_h :
      (FullMem c { s_clr with scratch := { s_clr.scratch with scratch_buf := scr_h } } ⋆ R) _ :=
    m7_p6_scrBuf_unsplit_eq hm (by
      dsimp only [scr_h, m7_p6_scr_h, OfNat.ofNat, instOfNatNat]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd])
  obtain ⟨hscrh_l, hscrh_pre0, hscrh_meta, hscrh_1, hscrh_2, hscrh_14, hscrh_15⟩ :=
    m7_p6_scr_h_props hscre_l h8192 nv_s nc_s alen_s
      (BitVec.ofNat 32 (c.scratch_cap - 4008)) nunits_s
  have hscrh_pre : ∀ k < 1096, scr_h[k]? = s0.scratch.scratch_buf[k]? := fun k hk =>
    (hscrh_pre0 k hk).trans (hscre_pre k hk)
  refine wp_loop_group (ts := [i32])
    (fun rem1 (i, ()) m1 => ∃ scr1 : List (BitVec 32),
      let s1 : FullState := { s_clr with scratch := { s_clr.scratch with scratch_buf := scr1 } }
      scr1.length = c.scratch_cap ∧ i.toNat ≤ nv_s.toNat ∧ rem1 = nv_s.toNat - i.toNat ∧
      (∀ k < 1096, scr1[k]? = s0.scratch.scratch_buf[k]?) ∧
      scr1[1096 + 1]? = some nc_s ∧ scr1[1096 + 2]? = some nc_s ∧
      scr1[1096 + 14]? = some alen_s ∧
      scr1[1096 + 15]? = some (BitVec.ofNat 32 (c.scratch_cap - 4008)) ∧
      (∀ k, 1888 ≤ k → k < 2656 → scr1[1096 + k]? = scr_e[1096 + k]?) ∧
      (FullMem c s1 ⋆ R) m1) ?_ ?_
  · rintro L1 rem1 ⟨i, ⟨⟩⟩ m1 hL1
      ⟨scr1, hsc1_l, hi_le, rfl, hpre1, hs1_1, hs1_2, hs1_14, hs1_15, hmeta1, hm1⟩
    c0_hsplit
    · have hi_lt : i.toNat < nv_s.toNat := hc
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := m7_p6_add1_toNat (by omega)
      have hbd1 : ∀ off : Nat, off ≤ 480 → 1096 + (off + i.toNat) < scr1.length := fun off ho =>
        by rw [hsc1_l]; omega
      c0_hsteps_nogrp
      let scr1a :=
        (((scr1.set (1096 + (32 + i.toNat)) 0#32).set
          (1096 + (96 + i.toNat)) 0xFFFFFFFF#32).set
          (1096 + (416 + i.toNat)) 0#32).set (1096 + (288 + i.toNat)) (i + 1#32)
      have hsc1a_l : scr1a.length = c.scratch_cap := by simp [scr1a, hsc1_l]
      have h1a_pre : ∀ k < 1096, scr1a[k]? = s0.scratch.scratch_buf[k]? := fun k hk => by
        dsimp only [scr1a]; (repeat rw [List.getElem?_set_ne (by omega)]); exact hpre1 k hk
      have h1a_meta : ∀ k, 1888 ≤ k → k < 2656 → scr1a[1096 + k]? = scr_e[1096 + k]? :=
        fun k hk1 hk2 => by
          dsimp only [scr1a]; (repeat rw [List.getElem?_set_ne (by omega)]); exact hmeta1 k hk1 hk2
      have h1a_1 : scr1a[1096 + 1]? = some nc_s := by
        dsimp only [scr1a]; (repeat rw [List.getElem?_set_ne (by omega)]); exact hs1_1
      have h1a_2 : scr1a[1096 + 2]? = some nc_s := by
        dsimp only [scr1a]; (repeat rw [List.getElem?_set_ne (by omega)]); exact hs1_2
      have h1a_14 : scr1a[1096 + 14]? = some alen_s := by
        dsimp only [scr1a]; (repeat rw [List.getElem?_set_ne (by omega)]); exact hs1_14
      have h1a_15 : scr1a[1096 + 15]? = some (BitVec.ofNat 32 (c.scratch_cap - 4008)) := by
        dsimp only [scr1a]; (repeat rw [List.getElem?_set_ne (by omega)]); exact hs1_15
      refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
        (fun x => (x, ())) (fun _ => True) ?_ ?_
      · intro Jp pv _
        c0_hsteps_nogrp
        let scr1b := scr1a.set (1096 + (160 + i.toNat)) pv
        have hsc1b_l : scr1b.length = c.scratch_cap := by simp [scr1b, hsc1a_l]
        refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
          (fun x => (x, ())) (fun _ => True) ?_ ?_
        · intro Jn nx _
          c0_hsteps!
          rw [m7_p6_off_add 32 (by decide) i (by omega),
            m7_p6_off_add 96 (by decide) i (by omega),
            m7_p6_off_add 416 (by decide) i (by omega),
            m7_p6_off_add 288 (by decide) i (by omega),
            m7_p6_off_add 160 (by decide) i (by omega),
            m7_p6_off_add 224 (by decide) i (by omega)] at hm
          let scr1c := scr1b.set (1096 + (224 + i.toNat)) nx
          refine hL1 (nv_s.toNat - (i + 1#32).toNat) (i + 1#32, ()) _ (by omega)
            ⟨scr1c, by simp [scr1c, hsc1b_l], by omega, rfl,
              fun k hk => by
                dsimp only [scr1c, scr1b]
                rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                exact h1a_pre k hk,
              by dsimp only [scr1c, scr1b]
                 rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact h1a_1,
              by dsimp only [scr1c, scr1b]
                 rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact h1a_2,
              by dsimp only [scr1c, scr1b]
                 rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                 exact h1a_14,
              by dsimp only [scr1c, scr1b]
                 rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                 exact h1a_15,
              fun k hk1 hk2 => by
                dsimp only [scr1c, scr1b]
                rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                exact h1a_meta k hk1 hk2,
              m7_p6_fullMem_subst hm⟩
        · intro _ hJn; c0_hsplit
          · c0_hsteps!; exact hJn 0xFFFFFFFF#32 trivial
          · c0_hsteps!; exact hJn (i + 1#32) trivial
      · intro _ hJp; c0_hsplit
        · c0_hsteps!; exact hJp 0xFFFFFFFF#32 trivial
        · c0_hsteps!; exact hJp (i - 1#32) trivial
    · have hi_eq : i.toNat = nv_s.toNat := by omega
      c0_hsteps_nogrp
      exact m7_p6_k6_init_lits_wp Γ Q X c s0 s_clr R
        (c.pScratchBuf + BitVec.ofNat 64 1096 * 4) nv_s nc_s alen_s
        scr_e scr1 _ k_watch rfl hsc28 h8192 hscre_l hsc1_l hnv64 hnc128 hal_le
        hpre1 hs1_1 hs1_2 hs1_14 hs1_15 hmeta1 hcls_e hm1 hw_wp
  · intro L1 hL1; c0_hsteps!
    exact hL1 nv_s.toNat (0#32, ()) _
      ⟨scr_h, hscrh_l, Nat.zero_le _, rfl, hscrh_pre, hscrh_1, hscrh_2, hscrh_14, hscrh_15,
       hscrh_meta, hhm_h⟩

/-! ## 2. Clean Invariants & Commit Helpers for `full_bve_def_k6_m7_wp` -/

@[expose] def M7P6TmkExpInv (c : FullCfg) (s0 : FullState) (nv : BitVec 32)
    (exp tmk : List (BitVec 32)) : Prop :=
  exp.length = 2 * c.max_vars ∧ tmk.length = 2 * c.max_vars ∧
  nv.toNat ≤ 64 ∧ nv.toNat ≤ 2 * s0.core.cur_vars ∧
  (∀ k < nv.toNat, (exp[k]?.getD 0#32).toNat < s0.core.cur_vars) ∧
  (∀ u < s0.core.cur_vars, tmk[u]?.getD 0#32 ≠ 0#32 →
    1 ≤ (tmk[u]?.getD 0#32).toNat ∧ (tmk[u]?.getD 0#32).toNat ≤ nv.toNat ∧
    ∃ k < nv.toNat, (exp[k]?.getD 0#32).toNat = u)

@[expose] def M7P6ClsInv (nc alen nu : BitVec 32) (acap_n : Nat) (scr : List (BitVec 32)) :
    Prop :=
  nc.toNat ≤ 128 ∧ nu.toNat ≤ nc.toNat ∧ alen.toNat ≤ acap_n ∧
  ∀ cid < nc.toNat,
    (scr[1096 + 1888 + cid]?.getD 0#32).toNat +
      ((scr[1096 + 2144 + cid]?.getD 0#32) &&& 0xFFFF#32).toNat ≤ alen.toNat ∧
    ((scr[1096 + 2144 + cid]?.getD 0#32) &&& 0x40000000#32) = 0#32

@[expose] def M7P6SideInv (c : FullCfg) (s0 : FullState) (R : Mem 64 → Prop) (acap_n : Nat)
    (nv nc al nu teid : BitVec 32) (m : Mem 64) : Prop :=
  ∃ (exp tmk tmp scr : List (BitVec 32)),
    let st : FullState :=
      { s0 with
        core := { s0.core with tmp := tmp }
        scratch := { s0.scratch with wsort := exp, tarjan_mark := tmk, scratch_buf := scr } }
    tmp.length = c.max_vars ∧ scr.length = c.scratch_cap ∧
    (∀ k < 1096, scr[k]? = s0.scratch.scratch_buf[k]?) ∧
    M7P6TmkExpInv c s0 nv exp tmk ∧ M7P6ClsInv nc al nu acap_n scr ∧
    (teid ≠ 0xFFFFFFFF#32 → (teid &&& 0x3FF#32).toNat < 512) ∧
    (FullMem c st ⋆ R) m

@[expose] def M7P6InnerInv (c : FullCfg) (s0 : FullState) (R : Mem 64 → Prop) (acap_n : Nat)
    (cnt : BitVec 32) (rem : Nat) (nv nc al nu : BitVec 32) (ab : Bool) (idx : BitVec 32)
    (m : Mem 64) : Prop :=
  ∃ (exp tmk tmp scr : List (BitVec 32)),
    let st : FullState :=
      { s0 with
        core := { s0.core with tmp := tmp }
        scratch := { s0.scratch with wsort := exp, tarjan_mark := tmk, scratch_buf := scr } }
    tmp.length = c.max_vars ∧ scr.length = c.scratch_cap ∧
    idx.toNat ≤ cnt.toNat ∧ rem = (if !ab then cnt.toNat - idx.toNat else 0) ∧
    (∀ k < 1096, scr[k]? = s0.scratch.scratch_buf[k]?) ∧
    M7P6TmkExpInv c s0 nv exp tmk ∧ M7P6ClsInv nc al nu acap_n scr ∧
    (FullMem c st ⋆ R) m

@[expose] def M7P6ClearInv (c : FullCfg) (s0 : FullState) (R : Mem 64 → Prop)
    (nv nc al : Nat) (tmp exp : List (BitVec 32)) (m : Mem 64) : Prop :=
  ∃ tmk scr : List (BitVec 32),
    let st : FullState :=
      { s0 with
        core := { s0.core with tmp := tmp }
        scratch := { s0.scratch with wsort := exp, tarjan_mark := tmk, scratch_buf := scr } }
    tmk.length = 2 * c.max_vars ∧ scr.length = c.scratch_cap ∧
    (∀ u < s0.core.cur_vars, tmk[u]?.getD 0#32 ≠ 0#32 →
      ∃ k < nv, (exp[k]?.getD 0#32).toNat = u) ∧
    (∀ k < 1096, scr[k]? = s0.scratch.scratch_buf[k]?) ∧
    (∀ cid < nc,
      (scr[1096 + 1888 + cid]?.getD 0#32).toNat +
        ((scr[1096 + 2144 + cid]?.getD 0#32) &&& 0xFFFF#32).toNat ≤ al ∧
      ((scr[1096 + 2144 + cid]?.getD 0#32) &&& 0x40000000#32) = 0#32) ∧
    (FullMem c st ⋆ R) m

@[expose] def M7P6TmkJoinInv (c : FullCfg) (s0 : FullState) (R : Mem 64 → Prop)
    (tmp scr : List (BitVec 32)) (lv : BitVec 32)
    (nv : BitVec 32) (ab : Bool) (m : Mem 64) : Prop :=
  ab = false ∧
  ∃ (exp tmk : List (BitVec 32)),
    let st : FullState :=
      { s0 with
        core := { s0.core with tmp := tmp }
        scratch := { s0.scratch with wsort := exp, tarjan_mark := tmk, scratch_buf := scr } }
    M7P6TmkExpInv c s0 nv exp tmk ∧
    1 ≤ (tmk[lv.toNat]?.getD 0#32).toNat ∧
    (tmk[lv.toNat]?.getD 0#32).toNat ≤ nv.toNat ∧
    (FullMem c st ⋆ R) m

@[expose] def M7P6ScanLargeInv (c : FullCfg) (s0 : FullState) (R : Mem 64 → Prop)
    (scr : List (BitVec 32)) (mc nv csz : BitVec 32) (m : Mem 64) : Prop :=
  ∃ (exp tmk tmp : List (BitVec 32)),
    let st : FullState :=
      { s0 with
        core := { s0.core with tmp := tmp }
        scratch := { s0.scratch with wsort := exp, tarjan_mark := tmk, scratch_buf := scr } }
    tmp.length = c.max_vars ∧ csz.toNat ≤ mc.toNat ∧
    M7P6TmkExpInv c s0 nv exp tmk ∧ (FullMem c st ⋆ R) m

theorem m7_p6_teid_exit_commit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {tmp exp tmk scr : List (BitVec 32)} {teid mbase : BitVec 32}
    (hdw0 : FullDenseInvW c F0 F_cur s0)
    (htmp : tmp.length = c.max_vars) (hexp : exp.length = 2 * c.max_vars)
    (htmk : tmk.length = 2 * c.max_vars) (hscr : scr.length = c.scratch_cap)
    (htmk_clr : ∀ u < s0.core.cur_vars, tmk[u]?.getD 0#32 = 0#32)
    (hpre : ∀ k < 1096, scr[k]? = s0.scratch.scratch_buf[k]?)
    (hidx_lt : (teid &&& 0x3FF#32).toNat < 512)
    (hmbase : mbase = 1024#32 ∨ mbase = 1040#32) :
    let idx_t := teid &&& 0x3FF#32
    let scr_f :=
      ((scr.set (mbase + (idx_t >>> (5 : Nat))).toNat
        (1#32 <<< ((idx_t &&& 31#32).toNat % 32))).set 1056 1#32).set 1057 1#32
    let s_f : FullState :=
      { s0 with
        core := { s0.core with tmp := tmp }
        scratch := { s0.scratch with wsort := exp, tarjan_mark := tmk, scratch_buf := scr_f } }
    1024 ≤ (mbase + (idx_t >>> (5 : Nat))).toNat ∧
    (mbase + (idx_t >>> (5 : Nat))).toNat < 1056 ∧
    scr_f.length = c.scratch_cap ∧
    FullDenseInvW c F0 F_cur s_f ∧ TmkZero s_f ∧
    (∀ k < 512, scr_f[k]? = s0.scratch.scratch_buf[k]?) ∧
    (∀ k < 512, scr_f[512 + k]? = s0.scratch.scratch_buf[512 + k]?) := by
  intro idx_t scr_f s_f
  have h1 : 1024 ≤ (mbase + (idx_t >>> (5 : Nat))).toNat := by
    dsimp only [idx_t]; rcases hmbase with rfl | rfl <;> bv_omega
  have h2 : (mbase + (idx_t >>> (5 : Nat))).toNat < 1056 := by
    dsimp only [idx_t]; rcases hmbase with rfl | rfl <;> bv_omega
  have hlen : scr_f.length = c.scratch_cap := by simp [scr_f, hscr]
  refine ⟨h1, h2, hlen, m7_p6_fullDenseInvW_def hdw0 htmp hexp htmk hlen,
    fun u hu => htmk_clr u hu, fun k hk => ?_, fun k hk => ?_⟩
  · dsimp only [scr_f]; (repeat rw [List.getElem?_set_ne (by omega)])
    exact hpre k (by omega)
  · dsimp only [scr_f]; (repeat rw [List.getElem?_set_ne (by omega)])
    exact hpre (512 + k) (by omega)

theorem m7_p6_side_setup {F_cur : List (List Nat)} {s0 : FullState}
    {v np nn side cnt off except : BitVec 32}
    (hcv_le : s0.core.cur_vars ≤ 2 ^ 28 - 1) (hv_lt : v.toNat < s0.core.cur_vars)
    (hnp : np.toNat ≤ 128) (hnn : nn.toNat ≤ 128) (hside : side.toNat < 2)
    (hp_ok : ∀ i < np.toNat, FullBveEntryOkW F_cur s0 (2 * v.toNat)
      (s0.scratch.scratch_buf[i]?.getD 0#32))
    (hn_ok : ∀ j < nn.toNat, FullBveEntryOkW F_cur s0 (2 * v.toNat + 1)
      (s0.scratch.scratch_buf[512 + j]?.getD 0#32))
    (hcnt_eq : (side = 0#32 → cnt = np) ∧ (side ≠ 0#32 → cnt = nn))
    (hoff_eq : (side = 0#32 → off = 0#32) ∧ (side ≠ 0#32 → off = 512#32))
    (hexc_eq : (side = 0#32 → except = v <<< (1 : Nat)) ∧
      (side ≠ 0#32 → except = ((v <<< (1 : Nat)) ||| 1#32))) :
    cnt.toNat ≤ 128 ∧ off.toNat + cnt.toNat ≤ 1024 ∧
    except.toNat < 2 * s0.core.cur_vars ∧
    ∀ j < cnt.toNat, FullBveEntryOkW F_cur s0 except.toNat
      (s0.scratch.scratch_buf[off.toNat + j]?.getD 0#32) := by
  have hplnl := m7_p6_pl_nl_eq v (by omega)
  rcases Nat.lt_succ_iff_lt_or_eq.mp hside with hs0 | hs1
  · have hs0b : side = 0#32 := BitVec.eq_of_toNat_eq (Nat.lt_one_iff.mp hs0)
    rw [hcnt_eq.1 hs0b, hoff_eq.1 hs0b, hexc_eq.1 hs0b, hplnl.1,
      show (0#32 : BitVec 32).toNat = 0 from rfl, Nat.zero_add]
    exact ⟨hnp, by omega, by omega, fun j hj => by simpa [Nat.zero_add] using hp_ok j hj⟩
  · have hs1ne : side ≠ 0#32 := fun h => by
      have := congrArg BitVec.toNat h; simp only [BitVec.toNat_zero] at this; omega
    rw [hcnt_eq.2 hs1ne, hoff_eq.2 hs1ne, hexc_eq.2 hs1ne, hplnl.2,
      show (512#32 : BitVec 32).toNat = 512 from rfl]
    exact ⟨hnn, by omega, by omega, hn_ok⟩

theorem m7_p6_bin_unit_commit {c : FullCfg} {s0 : FullState}
    {scr : List (BitVec 32)} {nc al nu eid tmkv l : BitVec 32} {acap_n : Nat}
    (hpre : ∀ k < 1096, scr[k]? = s0.scratch.scratch_buf[k]?)
    (hcls : M7P6ClsInv nc al nu acap_n scr)
    (hsc_l : scr.length = c.scratch_cap)
    (hcap : 1096 + 2912 + acap_n ≤ c.scratch_cap)
    (hal1 : (al + 1#32).toNat = al.toNat + 1) (hal1_le : al.toNat + 1 ≤ acap_n)
    (hnc1 : (nc + 1#32).toNat = nc.toNat + 1) (hnc_lt : nc.toNat < 128)
    (hnu1 : (nu + 1#32).toNat = nu.toNat + 1) :
    let ulit := ((tmkv - 1#32) <<< (1 : Nat)) ||| (l &&& 1#32)
    let scr_u :=
      ((((scr.set (1096 + 2912 + al.toNat) ulit).set
        (1096 + 1888 + nc.toNat) al).set
        (1096 + 2144 + nc.toNat) 1#32).set
        (1096 + 2400 + nc.toNat) eid).set
        (1096 + 2656 + nu.toNat) nc
    scr_u.length = c.scratch_cap ∧
    (∀ k < 1096, scr_u[k]? = s0.scratch.scratch_buf[k]?) ∧
    M7P6ClsInv (nc + 1#32) (al + 1#32) (nu + 1#32) acap_n scr_u := by
  intro ulit scr_u
  have hnu_le := hcls.2.1
  have hal_cap := hcls.2.2.1
  have hsl : scr_u.length = c.scratch_cap := by simp [scr_u, hsc_l]
  refine ⟨hsl, fun k hk => ?_, by omega, by omega, by omega, fun cid hcid => ?_⟩
  · dsimp only [scr_u]; (repeat rw [List.getElem?_set_ne (by omega)])
    exact hpre k hk
  · dsimp only [scr_u]
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hnc1 ▸ hcid)) with hlt | rfl
    · (repeat rw [List.getElem?_set_ne (by omega)])
      have hp := hcls.2.2.2 cid hlt
      exact ⟨Nat.le_trans hp.1 (by omega), hp.2⟩
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hsc_l]; omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by simp [hsc_l]; omega),
        Option.getD_some, Option.getD_some,
        show (1#32 &&& 0xFFFF#32 : BitVec 32).toNat = 1 from rfl,
        show (1#32 &&& 0x40000000#32 : BitVec 32) = 0#32 from rfl]
      rw [hal1]; exact ⟨Nat.le_refl _, rfl⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Definition
