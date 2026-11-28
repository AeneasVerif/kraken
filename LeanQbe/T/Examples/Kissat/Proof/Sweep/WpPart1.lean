/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Sweep.LemmasCommon
public import LeanQbe.T.Examples.Kissat.Proof.Sweep.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Kitten.Spec

/-!
# Backward Sweep Partition Refinement WP Proof (`Kissat.Proof.Sweep.WpPart1`)
Proves `Func.wp` for `full_m6_refine_partition` using `Proof.Sweep.Spec`.
-/

set_option autoImplicit false
public section
namespace LeanQbe.T.Examples.Kissat.Proof.Sweep

open Std Std.Sat Kraken.Bedrock2.Test LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Src.Sweep LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec LeanQbe.T.Examples.Kissat.Proof.Sweep.Spec
open LeanQbe.T.Examples.Kissat.Proof.Kitten LeanQbe.T.Examples.Kissat.Proof.Kitten.Spec
open K6MemATactics K6PtrTactics
open scoped FullArenaTactics M6SweepTactics M6PhtMem FullK6DynMem M6ElsBv

/-! ## 0. Pure Helpers -/

private theorem m6_p1_zext32 (x : BitVec 32) : (BitVec.setWidth 64 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (lt_trans (BitVec.isLt x) (by decide))]

private theorem m6_p1_bv32_add1 {n : Nat} (h : n + 1 < 2 ^ 32) :
    BitVec.ofNat 32 n + 1 = BitVec.ofNat 32 (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (1 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega : n < 2 ^ 32),
    Nat.mod_eq_of_lt h]

private theorem m6_p1_bv32_sub1 {n : Nat} (hp : 0 < n) (h : n < 2 ^ 32) :
    BitVec.ofNat 32 n - 1 = BitVec.ofNat 32 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]; exact hp)), BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, show (1 : BitVec 32).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega)]

private theorem m6_p1_zext32_ofNat {n : Nat} (h : n < 2 ^ 32) :
    (BitVec.setWidth 64 (BitVec.ofNat 32 n)).toNat = n := by
  rw [m6_p1_zext32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem m6_p1_bv32_shl1 {v : BitVec 32} (hv : v.toNat < 2 ^ 31) :
    (v <<< (1#32 : BitVec 32)).toNat = 2 * v.toNat := by
  have h1 : (v <<< (1#32 : BitVec 32)) = v <<< (1 : Nat) := rfl
  rw [h1, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem m6_p1_scr_nx_lt {scr : List (BitVec 32)} {L : K6Layout} {cap k : Nat}
    (hL : L.scrLen = cap) (hscr : scr.length = cap) (hk : k < L.maxV) :
    k6PhtNext + k < scr.length := by
  rw [hscr.trans hL.symm]; unfold K6Layout.scrLen K6Layout.k6Base k6PhtNext; omega

private theorem m6_p1_part_set_next_ok {scr0 scr sstk : List (BitVec 32)}
    {cap nv ncls idx : Nat} {L : K6Layout} (v : BitVec 32)
    (hL : L.scrLen = cap) (hscr : scr.length = cap) (hidx : idx < nv) (hnv_le : nv ≤ L.maxV)
    (hv : v = 0xFFFFFFFF#32 ∨ v.toNat < idx)
    (hpref : ∀ j < cap, j < k6PhtNext ∨ L.phtMerged ≤ j → scr[j]? = scr0[j]?)
    (hpart : M6PartitionOk nv ncls scr sstk) :
    let scr' := scr.set (k6PhtNext + idx) v
    scr'.length = cap ∧ (∀ j < cap, j < k6PhtNext ∨ L.phtMerged ≤ j → scr'[j]? = scr0[j]?) ∧
    M6PartitionOk nv ncls scr' sstk := by
  intro scr'; have hnx_bd := m6_p1_scr_nx_lt hL hscr (by omega : idx < L.maxV)
  have hpref' : ∀ j < cap, j < k6PhtNext ∨ L.phtMerged ≤ j → scr'[j]? = scr0[j]? :=
    fun j hj hP => by
      rw [List.getElem?_set_ne (by unfold K6Layout.phtMerged k6PhtNext at *; omega)]
      exact hpref j hj hP
  refine ⟨by simp [scr', hscr], hpref', hpart.1, fun j hj => ?_, hpart.2.2⟩
  by_cases hje : j = idx
  · subst hje; rw [List.getElem?_set_self hnx_bd, Option.getD_some]; exact hv
  · rw [List.getElem?_set_ne (by omega)]; exact hpart.2.1 j hj

/-! ## 1. `full_m6_refine_partition` -/

private theorem m6_ref_push_ws_ok {ws : List (BitVec 32)} {n nv cap : Nat} {hd : BitVec 32}
    (hlen : ws.length = cap) (hn : n < cap) (hhd : hd.toNat < nv)
    (hws : ∀ j < n, (ws[j]?.getD 0xFFFFFFFF#32).toNat < nv) :
    ∀ j < n + 1, ((ws.set n hd)[j]?.getD 0xFFFFFFFF#32).toNat < nv := fun j hj => by
  by_cases hjn : j = n
  · subst hjn; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hhd
  · rw [List.getElem?_set_ne (by omega)]; exact hws j (by omega)

private theorem m6_ref_other_next_ok {hd tl nxt k : BitVec 32} {cnt nv : Nat}
    (hnv : nv < 2 ^ 32) (hk : k.toNat < nv)
    (hnxt : nxt = 0xFFFFFFFF#32 ∨ (nxt.toNat < nv ∧ nxt.toNat < k.toNat))
    (h : (tl = 0xFFFFFFFF#32 ∧ cnt = 0) ∨ (0 < cnt ∧ hd.toNat < nv ∧ tl.toNat < nv ∧
      (k = 0xFFFFFFFF#32 ∨ k.toNat < tl.toNat))) :
    (tl = 0xFFFFFFFF#32 ∧ cnt = 0) ∨ (0 < cnt ∧ hd.toNat < nv ∧ tl.toNat < nv ∧
      (nxt = 0xFFFFFFFF#32 ∨ nxt.toNat < tl.toNat)) := by
  rcases h with h0 | ⟨h1, h2, h3, h4⟩
  · exact Or.inl h0
  · refine Or.inr ⟨h1, h2, h3, ?_⟩; rcases hnxt with hn | ⟨_, hn2⟩
    · exact Or.inl hn
    · refine Or.inr (lt_trans hn2 ?_); rcases h4 with h5 | h5
      · subst h5; simp at hk; omega
      · exact h5

private structure M6RefSt where
  newN : Nat
  ci : Nat
  scr : List (BitVec 32)
  sstk : List (BitVec 32)
  ws : List (BitVec 32)

private structure M6RefCh where
  k : BitVec 32
  head0 : BitVec 32
  tail0 : BitVec 32
  cnt0 : Nat
  head1 : BitVec 32
  tail1 : BitVec 32
  cnt1 : Nat
  rem : Nat
  scr : List (BitVec 32)

private abbrev M6RefStOf (s : FullState) (scr sstk ws : List (BitVec 32)) : FullState :=
  { s with scratch := { s.scratch with scratch_buf := scr, shrink_stk := sstk, wsort := ws } }

private abbrev M6RefScrInv (c : FullCfg) (L : K6Layout) (nv ncls : BitVec 32) (s : FullState)
    (scr sstk : List (BitVec 32)) : Prop :=
  scr.length = c.scratch_cap ∧
  (∀ i < c.scratch_cap, i < k6PhtNext ∨ L.phtMerged ≤ i → scr[i]? = s.scratch.scratch_buf[i]?) ∧
  M6PartitionOk nv.toNat ncls.toNat scr sstk

private abbrev M6RefStInv (c : FullCfg) (L : K6Layout) (nv ncls : BitVec 32) (s : FullState)
    (R : Mem 64 → Prop) (st : M6RefSt) (m' : Mem 64) : Prop :=
  st.ci ≤ ncls.toNat ∧ st.newN ≤ c.max_vars ∧ st.sstk.length = c.max_vars ∧
  st.ws.length = 2 * c.max_vars ∧
  (∀ j < st.newN, (st.ws[j]?.getD 0xFFFFFFFF#32).toNat < nv.toNat) ∧
  M6RefScrInv c L nv ncls s st.scr st.sstk ∧ (FullMem c (M6RefStOf s st.scr st.sstk st.ws) ⋆ R) m'

private abbrev M6RefArmInv (nv nxt hd tl : BitVec 32) (cnt : Nat) : Prop :=
  (tl = 0xFFFFFFFF#32 ∧ cnt = 0) ∨ (0 < cnt ∧ hd.toNat < nv.toNat ∧ tl.toNat < nv.toNat ∧
    (nxt = 0xFFFFFFFF#32 ∨ nxt.toNat < tl.toNat))

private abbrev M6RefChInv (c : FullCfg) (L : K6Layout) (nv ncls : BitVec 32) (s : FullState)
    (R : Mem 64 → Prop) (sstk ws : List (BitVec 32)) (st : M6RefCh) (m' : Mem 64) : Prop :=
  st.rem ≤ nv.toNat ∧ st.rem + st.cnt0 ≤ nv.toNat ∧ st.rem + st.cnt1 ≤ nv.toNat ∧
  (st.k = 0xFFFFFFFF#32 ∨ st.k.toNat < nv.toNat) ∧ M6RefArmInv nv st.k st.head0 st.tail0 st.cnt0 ∧
  M6RefArmInv nv st.k st.head1 st.tail1 st.cnt1 ∧ M6RefScrInv c L nv ncls s st.scr sstk ∧
  (FullMem c (M6RefStOf s st.scr sstk ws) ⋆ R) m'

private abbrev M6RefWsInv (c : FullCfg) (nv : BitVec 32) (s : FullState) (R : Mem 64 → Prop)
    (scr sstk : List (BitVec 32)) (res : Tup Val [i32]) (m' : Mem 64) : Prop :=
  ∃ newN' ws', res.1 = BitVec.ofNat 32 newN' ∧ newN' ≤ c.max_vars ∧ ws'.length = 2 * c.max_vars ∧
  (∀ j < newN', (ws'[j]?.getD 0xFFFFFFFF#32).toNat < nv.toNat) ∧
  (FullMem c (M6RefStOf s scr sstk ws') ⋆ R) m'

private theorem m6_ref_arm_bounds {nv k hd tl : BitVec 32} {cnt : Nat}
    (hk : k.toNat < nv.toNat) (h : M6RefArmInv nv k hd tl cnt) (hne : tl ≠ 0xFFFFFFFF#32) :
    tl.toNat < nv.toNat ∧ hd.toNat < nv.toNat ∧ k.toNat < tl.toNat := by
  rcases h with ⟨rfl, _⟩ | ⟨_, hhd, htl, hkt⟩
  · exact absurd rfl hne
  · refine ⟨htl, hhd, ?_⟩; rcases hkt with rfl | he
    · rw [show (0xFFFFFFFF#32 : BitVec 32).toNat = 4294967295 from rfl] at hk
      have := nv.isLt; omega
    · exact he

private theorem m6_ref_close_arm_wp {Γ : Env} {rs : List Ty} {c : FullCfg} {L : K6Layout}
    {nv ncls tl : BitVec 32} {s : FullState} {R : Mem 64 → Prop} {scr sstk ws : List (BitVec 32)}
    {m : Mem 64} {Q : Post rs} {X : XPost} {k_exit : Expr Val Cont rs} {J_t : Cont []}
    {base : BitVec 64} (hbase : base = c.pScratchBuf + BitVec.ofNat 64 1280 * 4)
    (hL : L.scrLen = c.scratch_cap) (hnv_le : nv.toNat ≤ L.maxV)
    (hscr : M6RefScrInv c L nv ncls s scr sstk) (hm : (FullMem c (M6RefStOf s scr sstk ws) ⋆ R) m)
    (hJ_t : ∀ m', (∃ scr', M6RefScrInv c L nv ncls s scr' sstk ∧
      (FullMem c (M6RefStOf s scr' sstk ws) ⋆ R) m') → J_t () m')
    (hJ_t' : k_exit = Expr.jump J_t ()) :
    wp Γ Q X (Expr.let_
        { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool,
          args := (Arg.var tl, Arg.var nv, ()) }
        fun p => Expr.jnz (Arg.var p.fst)
          (Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var tl, ()) }
            fun p => Expr.let_
              { sig := [i64, i64], code := OpCode.mul i64,
                args := (Arg.var p.fst, Arg.imm 4, ()) }
              fun p => Expr.let_
                { sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var base, Arg.var p.fst, ()) }
                fun p => Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p.fst) k_exit)
          (Expr.jump J_t ())) m := by
  subst hJ_t'; rw [hbase]; have hscr_len := hscr.1; c0_hsteps_nogrp
  · have htl_nv : tl.toNat < nv.toNat := by bv_omega
    have htl_mv : tl.toNat < L.maxV := by omega
    c0_hsteps_nogrp
    have hok := m6_p1_part_set_next_ok 0xFFFFFFFF#32 hL hscr.1 htl_nv hnv_le
      (Or.inl rfl) hscr.2.1 hscr.2.2
    dsimp only [M6RefStOf] at hm ⊢; exact hJ_t _ ⟨_, ⟨hok.1, hok.2.1, hok.2.2⟩, hm⟩
  · exact hJ_t _ ⟨scr, hscr, hm⟩

theorem full_m6_refine_partition_wp (Γ : Env)
    (hMaxV : Γ.Has "full_m6_max_v" m6MaxVSpec) :
    ∀ args m Q X, fullM6RefinePartitionSpec args m Q X →
      Func.wp Γ full_m6_refine_partition_body args m Q X := by
  rintro ⟨h, nv, ncls, ⟨⟩⟩ m Q X
    ⟨c, s, L, R, rfl, hlen, hscrLen, hmaxV, hnv_le, hnv_mv, hnc_mv, hstk, hpart, hm, hQ⟩
  have hcap64 : c.scratch_cap < 2 ^ 64 := by have := c.hscr; unfold dimacsBound at this; omega
  have hmv_db := c.hmaxv; unfold dimacsBound at hmv_db; have hL_max := L.hmaxV
  dsimp only [Func.wp]; unfold full_m6_refine_partition_body
  c0_hsteps_nogrp; refine k6_maxV_call_step hMaxV hcap64 ?_; c0_hsteps_nogrp
  have hmv32 : BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) = L.mv32 := by
    apply BitVec.eq_of_toNat_eq; have := hL_max.2; simp [K6Layout.mv32, ← hmaxV]
  have hkptr : c.pScratchBuf +
      BitVec.setWidth 64 ((1280 : BitVec 32) + L.mv32 <<< OfNat.ofNat 1) * 4 =
      L.kPtr c.pScratchBuf := by
    unfold K6Layout.kPtr K6Layout.k6Base K6Layout.mv32; congr 1; apply BitVec.eq_of_toNat_eq
    have h2 := hL_max.2
    have hm32' : (BitVec.ofNat 32 L.maxV <<< OfNat.ofNat 1).toNat = 2 * L.maxV := by
      rw [M6SweepTactics.m6_bv32_shl1_nat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_mul, m6_p1_zext32, BitVec.toNat_add,
      show BitVec.toNat (1280 : BitVec 32) = 1280 from rfl, hm32',
      Nat.mod_eq_of_lt (by omega : 1280 + 2 * L.maxV < 2 ^ 32), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 4 * (1280 + 2 * L.maxV) < 2 ^ 64),
      show BitVec.toNat (4 : BitVec 64) = 4 from rfl,
      Nat.mod_eq_of_lt (by omega : (1280 + 2 * L.maxV) * 4 < 2 ^ 64)]; omega
  rw [hmv32]
  refine wp_while_state (ts := [i32, i32]) (α := M6RefSt)
    (fun st => (BitVec.ofNat 32 st.newN, BitVec.ofNat 32 st.ci, ()))
    (fun st => ncls.toNat - st.ci) (M6RefStInv c L nv ncls s R) ?_ ?_
  · intro J0 hJ0; c0_hsteps_nogrp
    exact hJ0 ⟨0, 0, s.scratch.scratch_buf, s.scratch.shrink_stk, s.scratch.wsort⟩ _
      ⟨Nat.zero_le _, Nat.zero_le _, hlen.scratch_ok.shrink_stk_len, hlen.scratch_ok.wsort_len,
       fun _ hj => absurd hj (Nat.not_lt_zero _),
       ⟨hlen.scratch_ok.scratch_buf_len, fun _ _ _ => rfl, hpart⟩, hm⟩
  · rintro J0 ⟨new_n, ci, scr, sstk, ws⟩ m'
      ⟨hci_le, hnn_mv, hsstk_len, hws_len, hws_hd, hscr_inv, hm'⟩ ih
    obtain ⟨hscr_len, hpref, hpart_lp⟩ := hscr_inv
    dsimp only at hci_le hnn_mv hsstk_len hws_len hws_hd hscr_len hpref hpart_lp hm' ih
    clear hm; c0_hsteps_nogrp
    · have hci_lt : ci < ncls.toNat := by bv_omega
      have hci_32 : (BitVec.ofNat 32 ci).toNat = ci := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hci_bd : (BitVec.setWidth 64 (BitVec.ofNat 32 ci)).toNat < sstk.length := by
        rw [hsstk_len, m6_p1_zext32, hci_32]; omega
      c0_hsteps_nogrp
      let head := sstk[(BitVec.setWidth 64 (BitVec.ofNat 32 ci)).toNat]'hci_bd
      have hhead_lt : head.toNat < nv.toNat := by
        have hp := hpart_lp.2.2 ci hci_lt
        rw [List.getElem?_eq_getElem (by rw [hsstk_len]; omega), Option.getD_some] at hp
        simpa [head, m6_p1_zext32, hci_32] using hp
      refine wp_while_state (ts := [i32, i32, i32, i32, i32, i32, i32, i32]) (α := M6RefCh)
        (fun st => (st.k, st.head0, st.tail0, BitVec.ofNat 32 st.cnt0,
          st.head1, st.tail1, BitVec.ofNat 32 st.cnt1, BitVec.ofNat 32 st.rem, ()))
        (fun st => st.rem) (M6RefChInv c L nv ncls s R sstk ws) ?_ ?_
      · intro J_ch hJ_ch; c0_hsteps_nogrp
        simpa [head, M6RefStOf, BitVec.ofNat_toNat] using hJ_ch
          ⟨head, 0xFFFFFFFF#32, 0xFFFFFFFF#32, 0, 0xFFFFFFFF#32, 0xFFFFFFFF#32, 0, nv.toNat, scr⟩
          m' ⟨Nat.le_refl _, by dsimp only; omega, by dsimp only; omega,
            Or.inr hhead_lt, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩,
            ⟨hscr_len, hpref, hpart_lp⟩, hm'⟩
      · rintro J_ch ⟨k, head0, tail0, cnt0, head1, tail1, cnt1, rem, scr_ch⟩ m2
          ⟨hrem_le, hcnt0_le, hcnt1_le, hk_ok, h0_ok, h1_ok, hscr_ch_inv, hm2⟩ ih_ch
        obtain ⟨hscr_ch, hpref_ch, hpart_ch⟩ := hscr_ch_inv
        dsimp only at hrem_le hcnt0_le hcnt1_le hk_ok h0_ok h1_ok hm2 ih_ch
        dsimp only at hscr_ch hpref_ch hpart_ch
        refine wp_join0 (fun m3 => ∃ scr3, M6RefScrInv c L nv ncls s scr3 sstk ∧
            (FullMem c (M6RefStOf s scr3 sstk ws) ⋆ R) m3) ?_ ?_
        · rintro J_ex m3 ⟨scr3, hscr3_inv, hm3⟩; c0_hsteps_nogrp
          refine wp_join0 (fun m4 => ∃ scr4, M6RefScrInv c L nv ncls s scr4 sstk ∧
              (FullMem c (M6RefStOf s scr4 sstk ws) ⋆ R) m4) ?_ ?_
          · rintro J_t0 m4 ⟨scr4, hscr4_inv, hm4⟩; c0_hsteps_nogrp
            refine wp_join0 (fun m5 => ∃ scr5, M6RefScrInv c L nv ncls s scr5 sstk ∧
                (FullMem c (M6RefStOf s scr5 sstk ws) ⋆ R) m5) ?_ ?_
            · rintro J_t1 m5 ⟨scr5, hscr5_inv, hm5⟩
              refine wp_join_group (ts := [i32]) (M6RefWsInv c nv s R scr5 sstk) ?_ ?_
              · rintro J_p0 ⟨res0, ⟨⟩⟩ m6 ⟨newN1, ws1, rfl, hn1_mv, hws1, hws1_hd, hm6⟩
                refine wp_join_group (ts := [i32]) (M6RefWsInv c nv s R scr5 sstk) ?_ ?_
                · rintro J_p1 ⟨res1, ⟨⟩⟩ m7 ⟨newN2, ws2, rfl, hn2_mv, hws2, hws2_hd, hm7⟩
                  c0_hsteps_nogrp; rw [m6_p1_bv32_add1 (n := ci) (by omega)]
                  exact ih ⟨newN2, ci + 1, scr5, sstk, ws2⟩ m7 (by dsimp only; omega)
                    ⟨by dsimp only; omega, hn2_mv, hsstk_len, hws2, hws2_hd, hscr5_inv, hm7⟩
                · intro J_p1 hJ_p1; c0_hsteps_nogrp
                  · have hlt := ‹(BitVec.ofNat 32 newN1).toNat < c.max_vars % 2 ^ 64›
                    rw [Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by omega)] at hlt
                    have hc1 : (BitVec.setWidth 64 (BitVec.ofNat 32 newN1)).toNat < ws1.length :=
                      by rw [m6_p1_zext32_ofNat (by omega), hws1]; omega
                    c0_hsteps_nogrp
                    have hhd1 : head1.toNat < nv.toNat := by
                      rcases h1_ok with ⟨_, h⟩ | h; omega; exact h.2.1
                    dsimp only [M6RefStOf] at hm ⊢
                    refine hJ_p1 _ _ ⟨newN1 + 1, _, m6_p1_bv32_add1 (n := newN1) (by omega),
                      by omega, by simp [hws1], ?_, hm⟩
                    rw [m6_p1_zext32_ofNat (by omega)]
                    exact m6_ref_push_ws_ok hws1 (by omega) hhd1 hws1_hd
                  all_goals exact hJ_p1 _ m6 ⟨newN1, ws1, rfl, hn1_mv, hws1, hws1_hd, hm6⟩
              · intro J_p0 hJ_p0; c0_hsteps_nogrp
                · have hlt := ‹(BitVec.ofNat 32 new_n).toNat < c.max_vars % 2 ^ 64›
                  rw [Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega)] at hlt
                  have hnn_lt : (BitVec.setWidth 64 (BitVec.ofNat 32 new_n)).toNat < ws.length :=
                    by rw [m6_p1_zext32_ofNat (by omega), hws_len]; omega
                  c0_hsteps_nogrp
                  have hhd0 : head0.toNat < nv.toNat := by
                    rcases h0_ok with ⟨_, h⟩ | h; omega; exact h.2.1
                  dsimp only [M6RefStOf] at hm ⊢
                  refine hJ_p0 _ _ ⟨new_n + 1, _, m6_p1_bv32_add1 (n := new_n) (by omega),
                    by omega, by simp [hws_len], ?_, hm⟩
                  rw [m6_p1_zext32_ofNat (by omega)]
                  exact m6_ref_push_ws_ok hws_len (by omega) hhd0 hws_hd
                all_goals exact hJ_p0 _ m5 ⟨new_n, ws, rfl, hnn_mv, hws_len, hws_hd, hm5⟩
            · intro J_t1 hJ_t1
              exact m6_ref_close_arm_wp rfl hscrLen hnv_le hscr4_inv hm4 hJ_t1 rfl
          · intro J_t0 hJ_t0
            exact m6_ref_close_arm_wp rfl hscrLen hnv_le hscr3_inv hm3 hJ_t0 rfl
        · intro J_ex hJ_ex; c0_hsteps_nogrp
          · have hrem_pos : 0 < rem := by bv_omega
            have hk_nv : k.toNat < nv.toNat := by bv_omega
            have hk_mv : k.toNat < L.maxV := by omega
            c0_hsteps_nogrp
            let nxt := scr_ch[k6PhtNext + k.toNat]'(m6_p1_scr_nx_lt hscrLen hscr_ch hk_mv)
            have hnxt_ok : nxt = 0xFFFFFFFF#32 ∨ (nxt.toNat < nv.toNat ∧ nxt.toNat < k.toNat) := by
              have hn := hpart_ch.2.1 k.toNat hk_nv
              rw [List.getElem?_eq_getElem (m6_p1_scr_nx_lt hscrLen hscr_ch hk_mv),
                Option.getD_some] at hn
              rcases hn with h | h; exact Or.inl h; exact Or.inr ⟨Nat.lt_trans h hk_nv, h⟩
            refine wp_join_group (ts := [i32, i32, i32, i32, i32, i32]) (fun xs m3 =>
                ∃ h0' t0' h1' t1' : BitVec 32, ∃ c0' c1' : Nat, ∃ scr3 : List (BitVec 32),
                  xs = (h0', t0', BitVec.ofNat 32 c0', h1', t1', BitVec.ofNat 32 c1', ()) ∧
                  c0' ≤ cnt0 + 1 ∧ c1' ≤ cnt1 + 1 ∧
                  M6RefArmInv nv nxt h0' t0' c0' ∧ M6RefArmInv nv nxt h1' t1' c1' ∧
                  M6RefScrInv c L nv ncls s scr3 sstk ∧
                  (FullMem c (M6RefStOf s scr3 sstk ws) ⋆ R) m3) ?_ ?_
            · rintro J_nx ⟨h0', t0', c0'', h1', t1', c1'', ⟨⟩⟩ m3
                ⟨h0_, t0_, h1_, t1_, c0', c1', scr3, hxs, hc0', hc1', h0n, h1n, hscr3_inv, hm3⟩
              rcases hxs with ⟨rfl, rfl, rfl, rfl, rfl, rfl, _⟩
              rw [m6_p1_bv32_sub1 (n := rem) hrem_pos (by omega)]
              have hnxt_bv : nxt = 0xFFFFFFFF#32 ∨ nxt.toNat < nv.toNat := by
                rcases hnxt_ok with h | h; exact Or.inl h; exact Or.inr h.1
              exact ih_ch ⟨nxt, h0', t0', c0', h1', t1', c1', rem - 1, scr3⟩ m3
                (by dsimp only; omega)
                ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
                 hnxt_bv, h0n, h1n, hscr3_inv, hm3⟩
            · intro J_nx hJ_nx
              have hkeep0 := m6_ref_other_next_ok nv.isLt hk_nv hnxt_ok h0_ok
              have hkeep1 := m6_ref_other_next_ok nv.isLt hk_nv hnxt_ok h1_ok
              c0_hsteps_nogrp
              · have hwk_k : (BitVec.setWidth 64 k).toNat < s.scratch.work_stk1.length := by
                  rw [hlen.scratch_ok.work_stk1_len, m6_p1_zext32]; omega
                have hlit_v := hstk k.toNat hk_nv
                rw [List.getElem?_eq_getElem (by rw [hlen.scratch_ok.work_stk1_len]; omega),
                  Option.getD_some] at hlit_v
                have hvals_k : (BitVec.setWidth 64
                    (s.scratch.work_stk1[(BitVec.setWidth 64 k).toNat]'hwk_k <<< 1#32)).toNat <
                    s.core.vals.length := by
                  have hcl := hlen.core_ok.cur_vars_le
                  rw [m6_p1_zext32, hlen.core_ok.vals_len]
                  have hget : s.scratch.work_stk1[(BitVec.setWidth 64 k).toNat]'hwk_k =
                      s.scratch.work_stk1[k.toNat]'(by
                        rw [hlen.scratch_ok.work_stk1_len]; omega) := by congr 1
                  rw [hget, m6_p1_bv32_shl1 (by omega)]; omega
                c0_hsteps_nogrp
                · have hmclr_k : (BitVec.setWidth 64 k).toNat < s.core.min_clr.length := by
                    rw [hlen.core_ok.min_clr_len_arr, m6_p1_zext32]; omega
                  have hkv_lt : ((k <<< (1 : Nat)) |||
                      (s.core.min_clr[(BitVec.setWidth 64 k).toNat]'hmclr_k &&& 1#32)).toNat <
                      2 * L.maxV := by
                    rw [m6_bv32_shl1_or_and1 k _ (by omega)]
                    have := Nat.mod_lt
                      (s.core.min_clr[(BitVec.setWidth 64 k).toNat]'hmclr_k).toNat
                      (by decide : 0 < 2); omega
                  c0_hsteps_nogrp; rw [hkptr]; c0_hsteps_nogrp
                  refine wp_join_group (ts := [i32, i32, i32, i32, i32, i32]) (fun xs m3 =>
                      ∃ h0' t0' h1' t1' : BitVec 32, ∃ c0' c1' : Nat, ∃ scr3 : List (BitVec 32),
                      xs = (h0', t0', BitVec.ofNat 32 c0', h1', t1', BitVec.ofNat 32 c1', ()) ∧
                      c0' ≤ cnt0 + 1 ∧ c1' ≤ cnt1 + 1 ∧
                      M6RefArmInv nv nxt h0' t0' c0' ∧ M6RefArmInv nv nxt h1' t1' c1' ∧
                      M6RefScrInv c L nv ncls s scr3 sstk ∧
                      (FullMem c (M6RefStOf s scr3 sstk ws) ⋆ R) m3) ?_ ?_
                  · rintro J_99 ⟨h0', t0', c0'', h1', t1', c1'', ⟨⟩⟩ m3
                        ⟨h0_, t0_, h1_, t1_, c0', c1', scr3, hxs, hc0', hc1', h0n, h1n,
                        hscr3_inv, hm3⟩
                    rcases hxs with ⟨rfl, rfl, rfl, rfl, rfl, rfl, _⟩
                    c0_hsteps_nogrp
                    exact hJ_nx _ m3 ⟨h0', t0', h1', t1', c0', c1', scr3,
                      rfl, hc0', hc1', h0n, h1n, hscr3_inv, hm3⟩
                  · intro J_99 hJ_99
                    have hnxk : nxt = 0xFFFFFFFF#32 ∨ nxt.toNat < k.toNat := by
                      rcases hnxt_ok with h | h; exact Or.inl h; exact Or.inr h.2
                    c0_hsteps_nogrp
                    · refine wp_join_group (ts := [i32]) (fun ⟨h0', _⟩ m3 =>
                          ∃ scr3 : List (BitVec 32), h0'.toNat < nv.toNat ∧
                          M6RefScrInv c L nv ncls s scr3 sstk ∧
                          (FullMem c (M6RefStOf s scr3 sstk ws) ⋆ R) m3) ?_ ?_
                      · rintro J_101 ⟨h0', ⟨⟩⟩ m3 ⟨scr3, hh0', hscr3_inv, hm3⟩; c0_hsteps_nogrp
                        rw [m6_p1_bv32_add1 (n := cnt0) (by have := nv.isLt; omega)]
                        exact hJ_99 (h0', k, BitVec.ofNat 32 (cnt0 + 1),
                            head1, tail1, BitVec.ofNat 32 cnt1, ()) m3
                          ⟨h0', k, head1, tail1, cnt0 + 1, cnt1, scr3, rfl, by omega, by omega,
                           Or.inr ⟨by omega, hh0', hk_nv, hnxk⟩, hkeep1, hscr3_inv, hm3⟩
                      · intro J_101 hJ_101; c0_hsteps_nogrp
                        · exact hJ_101 _ m2 ⟨scr_ch, hk_nv, ⟨hscr_ch, hpref_ch, hpart_ch⟩, hm2⟩
                        · have hb0 := m6_ref_arm_bounds hk_nv h0_ok ‹tail0 ≠ 0xFFFFFFFF#32›
                          have hok := m6_p1_part_set_next_ok k hscrLen hscr_ch hb0.1 hnv_le
                            (Or.inr hb0.2.2) hpref_ch hpart_ch
                          dsimp only [M6RefStOf, k6PhtNext] at hm ⊢
                          exact hJ_101 _ _ ⟨_, hb0.2.1, ⟨hok.1, hok.2.1, hok.2.2⟩, hm⟩
                    · refine wp_join_group (ts := [i32, i32, i32]) (fun xs m3 =>
                          ∃ h1' t1' : BitVec 32, ∃ c1' : Nat, ∃ scr3 : List (BitVec 32),
                          xs = (h1', t1', BitVec.ofNat 32 c1', ()) ∧ c1' ≤ cnt1 + 1 ∧
                          M6RefArmInv nv nxt h1' t1' c1' ∧ M6RefScrInv c L nv ncls s scr3 sstk ∧
                          (FullMem c (M6RefStOf s scr3 sstk ws) ⋆ R) m3) ?_ ?_
                      · rintro J_101 ⟨h1', t1', c1'', ⟨⟩⟩ m3
                            ⟨h1_, t1_, c1', scr3, hxs, hc1', h1n, hscr3_inv, hm3⟩
                        rcases hxs with ⟨rfl, rfl, rfl, _⟩
                        c0_hsteps_nogrp
                        exact hJ_99 (head0, tail0, BitVec.ofNat 32 cnt0,
                            h1', t1', BitVec.ofNat 32 c1', ()) m3
                          ⟨head0, tail0, h1', t1', cnt0, c1', scr3, rfl,
                           by omega, hc1', hkeep0, h1n, hscr3_inv, hm3⟩
                      · intro J_101 hJ_101; c0_hsteps_nogrp
                        · refine wp_join_group (ts := [i32]) (fun ⟨h1', _⟩ m3 =>
                              ∃ scr3 : List (BitVec 32), h1'.toNat < nv.toNat ∧
                              M6RefScrInv c L nv ncls s scr3 sstk ∧
                              (FullMem c (M6RefStOf s scr3 sstk ws) ⋆ R) m3) ?_ ?_
                          · rintro J_103 ⟨h1', ⟨⟩⟩ m3 ⟨scr3, hh1', hscr3_inv, hm3⟩
                            c0_hsteps_nogrp
                            rw [m6_p1_bv32_add1 (n := cnt1) (by have := nv.isLt; omega)]
                            exact hJ_101 (h1', k, BitVec.ofNat 32 (cnt1 + 1), ()) m3
                              ⟨h1', k, cnt1 + 1, scr3, rfl, by omega,
                               Or.inr ⟨by omega, hh1', hk_nv, hnxk⟩, hscr3_inv, hm3⟩
                          · intro J_103 hJ_103; c0_hsteps_nogrp
                            · exact hJ_103 _ m2 ⟨scr_ch, hk_nv, ⟨hscr_ch, hpref_ch, hpart_ch⟩, hm2⟩
                            · have hb1 := m6_ref_arm_bounds hk_nv h1_ok ‹tail1 ≠ 0xFFFFFFFF#32›
                              have hok := m6_p1_part_set_next_ok k hscrLen hscr_ch hb1.1 hnv_le
                                (Or.inr hb1.2.2) hpref_ch hpart_ch
                              dsimp only [M6RefStOf, k6PhtNext] at hm ⊢
                              exact hJ_103 _ _ ⟨_, hb1.2.1, ⟨hok.1, hok.2.1, hok.2.2⟩, hm⟩
                        · exact hJ_101 _ m2 ⟨head1, tail1, cnt1, scr_ch, rfl, by omega, hkeep1,
                            ⟨hscr_ch, hpref_ch, hpart_ch⟩, hm2⟩
                · exact hJ_nx (head0, tail0, BitVec.ofNat 32 cnt0,
                    head1, tail1, BitVec.ofNat 32 cnt1, ()) m2
                    ⟨head0, tail0, head1, tail1, cnt0, cnt1, scr_ch, rfl, by omega, by omega,
                     hkeep0, hkeep1, ⟨hscr_ch, hpref_ch, hpart_ch⟩, hm2⟩
              · exact hJ_nx (head0, tail0, BitVec.ofNat 32 cnt0,
                  head1, tail1, BitVec.ofNat 32 cnt1, ()) m2
                  ⟨head0, tail0, head1, tail1, cnt0, cnt1, scr_ch, rfl, by omega, by omega,
                   hkeep0, hkeep1, ⟨hscr_ch, hpref_ch, hpart_ch⟩, hm2⟩
          all_goals exact hJ_ex m2 ⟨scr_ch, ⟨hscr_ch, hpref_ch, hpart_ch⟩, hm2⟩
    · have hci_eq : ci = ncls.toNat := by bv_omega
      subst hci_eq
      refine wp_while_state (ts := [i32]) (α := Nat × List (BitVec 32))
        (fun st => (BitVec.ofNat 32 st.1, ())) (fun st => new_n - st.1)
        (fun st m'' => st.1 ≤ new_n ∧ st.2.length = c.max_vars ∧
          M6PartitionOk nv.toNat st.1 scr st.2 ∧ (∀ j < st.1, st.2[j]? = ws[j]?) ∧
          (FullMem c (M6RefStOf s scr st.2 ws) ⋆ R) m'') ?_ ?_
      · intro J1 hJ1; c0_hsteps_nogrp
        exact hJ1 (0, sstk) m' ⟨Nat.zero_le _, hsstk_len, ⟨Nat.zero_le _, hpart_lp.2.1,
          fun _ hj => absurd hj (Nat.not_lt_zero _)⟩,
          fun _ hj => absurd hj (Nat.not_lt_zero _), hm'⟩
      · rintro J1 ⟨k, sstk1⟩ m1 ⟨hk_le, hsstk1_len, hpart1, hcp1, hm1⟩ ih1
        dsimp only at hk_le hsstk1_len hpart1 hcp1 hm1 ih1; c0_hsteps_nogrp
        · have hk_lt : k < new_n := by bv_omega
          have hk32 : (BitVec.ofNat 32 k).toNat = k := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have hws_k : (BitVec.ofNat 32 k).toNat < ws.length := by rw [hk32, hws_len]; omega
          have hs_k : (BitVec.ofNat 32 k).toNat < sstk1.length := by rw [hk32, hsstk1_len]; omega
          c0_hsteps_nogrp
          have hidx_k : (BitVec.setWidth 64 (BitVec.ofNat 32 k)).toNat = k := by
            rw [m6_p1_zext32, hk32]
          have hws_eq : ∀ h_p, ws[(BitVec.setWidth 64 (BitVec.ofNat 32 k)).toNat]'h_p =
              ws[k]'(by rw [hws_len]; omega) := fun _ => by congr 1
          dsimp only [M6RefStOf] at hm ⊢
          have hpart' : M6PartitionOk nv.toNat (k + 1) scr
              (sstk1.set (BitVec.setWidth 64 (BitVec.ofNat 32 k)).toNat
                ws[(BitVec.setWidth 64 (BitVec.ofNat 32 k)).toNat]) := by
            rw [hws_eq, hidx_k]
            refine ⟨by simp [hsstk1_len]; omega, hpart1.2.1, fun ci' hci' => ?_⟩
            by_cases hck : ci' = k
            · subst ci'; rw [List.getElem?_set_self (by rw [hsstk1_len]; omega),
                Option.getD_some, m6_getElem_eq_getD ws (by rw [hws_len]; omega) 0xFFFFFFFF#32]
              exact hws_hd k hk_lt
            · rw [List.getElem?_set_ne (by omega)]; exact hpart1.2.2 ci' (by omega)
          have hcp' : ∀ j < k + 1, (sstk1.set (BitVec.setWidth 64 (BitVec.ofNat 32 k)).toNat
                ws[(BitVec.setWidth 64 (BitVec.ofNat 32 k)).toNat])[j]? = ws[j]? := by
            intro j hj; rw [hws_eq, hidx_k]; by_cases hjk : j = k
            · subst hjk; rw [List.getElem?_set_self (by rw [hsstk1_len]; omega),
                List.getElem?_eq_getElem (by rw [hws_len]; omega)]
            · rw [List.getElem?_set_ne (by omega)]; exact hcp1 j (by omega)
          rw [m6_p1_bv32_add1 (n := k) (by omega)]
          exact ih1 (k + 1, sstk1.set (BitVec.setWidth 64 (BitVec.ofNat 32 k)).toNat
              ws[(BitVec.setWidth 64 (BitVec.ofNat 32 k)).toNat]) _
            (by dsimp only; omega) ⟨by dsimp only; omega, by simp [hsstk1_len], hpart', hcp', hm⟩
        · have hk_eq : k = new_n := by bv_omega
          rw [hk_eq] at hk_le hcp1 hpart1; subst k; c0_hsteps_nogrp
          have hnn32 : (BitVec.ofNat 32 new_n).toNat = new_n := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          dsimp only [M6RefStOf] at hm1
          exact hQ (BitVec.ofNat 32 new_n) scr sstk1 ws m1 hscr_len hsstk1_len hws_len hpref
            (by rw [hnn32]; exact hnn_mv) (by rw [hnn32]; exact hpart1) hm1

end LeanQbe.T.Examples.Kissat.Proof.Sweep

end
