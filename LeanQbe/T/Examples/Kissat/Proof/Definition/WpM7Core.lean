/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Definition.WpM7CoreHelpers

/-!
# Kissat M7 K6 Core Preservation Proof (`Proof.Definition.WpM7Core`)

Certifies `fullK6CoreM7Spec` for `full_k6_core_m7` on flat `CanonicalEnv`, split across
`k6_core_rsn_mark_wp`, `k6_core_trail_loop_wp`, `k6_core_inc_mark_wp`, and
`full_k6_core_m7_wp`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Definition

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Definition
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FidK6Tactics K6Tactics

@[local bv_c0]
private theorem k6_ofnat_one :
    @OfNat.ofNat Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (instOfNatNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) = 1 := rfl

private def k6SL3 {L rs} : Expr Val L rs → Expr Val L rs
  | .let_ (ts := t1) _ k1 => match k1 (k6DfltT t1) with
    | .let_ (ts := t2) _ k2 => match k2 (k6DfltT t2) with
      | .let_ (ts := t3) _ k3 => k3 (k6DfltT t3)
      | _ => .hlt
    | _ => .hlt
  | _ => .hlt

private def k6SL4 {L rs} : Expr Val L rs → Expr Val L rs
  | .let_ (ts := t1) _ k1 => match k1 (k6DfltT t1) with
    | .let_ (ts := t2) _ k2 => match k2 (k6DfltT t2) with
      | .let_ (ts := t3) _ k3 => match k3 (k6DfltT t3) with
        | .let_ (ts := t4) _ k4 => k4 (k6DfltT t4)
        | _ => .hlt
      | _ => .hlt
    | _ => .hlt
  | _ => .hlt

private def k6SLd3 {L rs} (v : BitVec 32) (e : Expr Val L rs) : Expr Val L rs :=
  k6SLd v (k6SL3 e)

private def k6SLd4 {L rs} (v : BitVec 32) (e : Expr Val L rs) : Expr Val L rs :=
  k6SLd v (k6SL4 e)

private def k6PostFix (pk : BitVec 64) (nc nv acap inc : BitVec 32)
    (Jinc : Cont [.bits 32]) : Expr Val Cont [] :=
  let e := k6SLd3 nc (full_k6_core_m7_body Val Cont (pk, ()))
  let e := k6SJF (k6SLet (k6SJF (k6SLet (k6SLd3 acap (k6SLd3 nv e)))))
  let e := k6SLd3 inc (k6SJF (k6SLet (k6SGrpBI nc e)))
  k6SGrpKI Jinc e

private def k6CorePreGroupE (pk : BitVec 64) (nc nv acap inc off_i sz_i : BitVec 32)
    (Jinc : Cont [.bits 32]) : Expr Val Cont [] :=
  let e := k6SJT (k6SLet (k6PostFix pk nc nv acap inc Jinc))
  let e := k6SJF (k6SLet (k6SGrpBI 0#32 e))
  let e := k6SSt (k6SLet (k6SLd4 0#32 (k6SL4 e)))
  k6SLetI sz_i (k6SLd4 0#32 (k6SLd4 off_i e))

private def k6CoreIncMarkE (pk : BitVec 64) (nc nv acap inc off_i sz_i : BitVec 32)
    (JincCl : Cont []) : Expr Val Cont [] :=
  k6SGrpKN JincCl (k6CorePreGroupE pk nc nv acap inc off_i sz_i (fun _ _ => True))

private def k6CoreTrailE (pk : BitVec 64) (nc nv acap : BitVec 32)
    (Jinc : Cont [.bits 32]) : Expr Val Cont [] :=
  k6SGrpBN (k6CorePreGroupE pk nc nv acap 0#32 0#32 0#32 Jinc)

private def k6CoreRsnE (pk : BitVec 64) (nc nv acap roff rsz vt : BitVec 32)
    (Jg : Cont []) : Expr Val Cont [] :=
  let e := k6SLd3 0#32 (k6CoreTrailE pk nc nv acap (fun _ _ => True))
  let e := k6SJT (k6SLet (k6SGrpBI 0#32 (k6SGrpBI 0#32 e)))
  let e := k6SJF (k6SLet (k6SLetI vt (k6SLd4 0#32 (k6SLet e))))
  let e := k6SJF (k6SLet (k6SLet (k6SLd4 0#32 e)))
  let e := k6SSt (k6SLet (k6SLet (k6SLd4 0#32 (k6SL4 e))))
  let e := k6SJF (k6SLet (k6SLd4 0#32 e))
  let e := k6SSt (k6SLet (k6SLd4 0#32 (k6SL4 e)))
  let e := k6SLetI rsz (k6SLd4 0#32 (k6SLd4 roff e))
  k6SGrpKN Jg e

private theorem k6_core_rsn_mark_wp {Γ : Env} {pk : BitVec 64} {kbuf : List (BitVec 32)}
    {nc nv acap roff rsz vt : BitVec 32} {R : Mem 64 → Prop} {Q : Post []} {X : XPost}
    {Jg : Cont []} (hlen : 2912 ≤ kbuf.length) (hnv_le : nv.toNat ≤ 64)
    (hnv0 : kbuf[0]'(by omega) = nv) (hacap15 : kbuf[15]'(by omega) = acap)
    (hJg : ∀ m', ∀ kbr, CoreInv kbuf nc kbr → (array (t := i32) pk kbr ⋆ R) m' → Jg () m')
    {kbt2 : List (BitVec 32)} {mt2 : Mem 64}
    (hkt2 : CoreInv kbuf nc kbt2) (hmt2 : (array (t := i32) pk kbt2 ⋆ R) mt2)
    (hrsz_nw : roff.toNat + rsz.toNat < 2 ^ 32) (hrsz_lt : rsz.toNat < 65536) :
    wp Γ Q X (k6CoreRsnE pk nc nv acap roff rsz vt Jg) mt2 := by
  let invCore := CoreInv kbuf nc
  dsimp only [k6CoreRsnE, k6CoreTrailE, k6CorePreGroupE, k6PostFix, k6SLd3, k6SLd4, k6SL3, k6SL4,
    k6SLet, k6SLetI, k6SLd, k6SSt, k6SJF, k6SJT, k6SGrpBI, k6SGrpBN, k6SGrpKI, k6SGrpKN,
    k6DfltT, k6Dflt, Prod.fst]
  c0_hsplit
  · have hrsz_bd : roff.toNat + rsz.toNat ≤ acap.toNat := by
      simpa [Nat.mod_eq_of_lt hrsz_nw, k6_c15] using hc
    clear hc; c0_hsteps_nogrp
    refine wp_loop_group (ts := [i32])
      (fun remj (jr, ()) mr => ∃ kbr, invCore kbr ∧ jr.toNat ≤ rsz.toNat ∧
        remj = rsz.toNat - jr.toNat ∧ (array (t := i32) pk kbr ⋆ R) mr) ?_ ?_
    · rintro Lr remr ⟨jr, ⟨⟩⟩ mr hLr ⟨kbr, hkr, hjr_le, rfl, hmr⟩
      have hkr_l := hkr.2.1; have hlt28 := hkr.1.length_lt; have hge := hkr.1.length_ge
      c0_hsplit
      · have hjr_lt : jr.toNat < rsz.toNat := hc
        clear hc
        have hj1 : (jr + 1#32).toNat = jr.toNat + 1 := by
          have := hrsz_lt; have := hjr_lt; c0_bound
        have har_r : 2912 + roff.toNat + jr.toNat < kbr.length := by
          have h15 : (kbr[15]?.getD 0#32).toNat = acap.toNat := by
            have := hkr.2.2.1 15 (by omega) (Or.inl (by omega))
            rw [this, m8_k6_get_eq (by omega), hacap15]
          omega
        have h2912_r_c0 : (BitVec.setWidth 64 ((2912 : BitVec 32) + roff + jr)).toNat <
            kbr.length := by
          have := har_r; have := hlt28; c0_bound
        c0_hsteps_nogrp
        refine wp_join0 (fun mr1 => ∃ kbr1, invCore kbr1 ∧ (array (t := i32) pk kbr1 ⋆ R) mr1)
          ?_ ?_
        · intro _ mr1 ⟨kbr1, hkr1, hmr1⟩; c0_hsteps!
          exact hLr (rsz.toNat - (jr + 1#32).toNat) (jr + 1#32, ()) mr1 (by have := hj1; omega)
            ⟨kbr1, hkr1, by have := hj1; omega, rfl, hmr1⟩
        · intro Jlv hJlv
          c0_hsplit
          · have hlv_lt : ((kbr[2912 + roff.toNat + jr.toNat]'har_r) >>> (1 : Nat)).toNat <
                nv.toNat := by
              have har_mod : (2912 + roff.toNat + jr.toNat) % 2 ^ 32 =
                  2912 + roff.toNat + jr.toNat := by
                have := har_r; have := hlt28; omega
              rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                ← m8_k6_get_congr har_mod (by rw [har_mod]; exact har_r) har_r]
              simpa [hnv0, Nat.reducePow] using hc
            clear hc
            have hget_lr : kbr[(BitVec.setWidth 64
                ((2912 : BitVec 32) + roff + jr)).toNat]'h2912_r_c0 =
                kbr[2912 + roff.toNat + jr.toNat]'har_r :=
              m8_k6_get_congr (by have := har_r; have := hlt28; c0_bound) _ _
            have h416_r_eq : (BitVec.setWidth 64 ((416 : BitVec 32) +
                (kbr[(BitVec.setWidth 64 ((2912 : BitVec 32) + roff + jr)).toNat]'h2912_r_c0 >>>
                  (1 : Nat)))).toNat =
                416 + ((kbr[2912 + roff.toNat + jr.toNat]'har_r) >>> (1 : Nat)).toNat := by
              rw [hget_lr]; have := hlv_lt; have := hnv_le; c0_bound
            have h416_r_c0 : (BitVec.setWidth 64 ((416 : BitVec 32) +
                (kbr[(BitVec.setWidth 64 ((2912 : BitVec 32) + roff + jr)).toNat]'h2912_r_c0 >>>
                  (1 : Nat)))).toNat < kbr.length := by
              rw [h416_r_eq]; have := hlv_lt; have := hnv_le; have := hkr_l; have := hlen; omega
            c0_hsplit
            · c0_hsteps!
              have hmr_eq := m8_k6_set_congr (xs := kbr) h416_r_eq
                (congrArg (· ||| (2 : BitVec 32))
                  (m8_k6_get_congr (xs := kbr) h416_r_eq h416_r_c0
                    (by have := hkr_l; have := hlen; omega)))
              simp only [k6_ofnat_one] at hm; rw [hmr_eq] at hm
              exact hJlv _ ⟨_, coreInv_set_flags hkr (v := ((kbr[2912 + roff.toNat +
                jr.toNat]'har_r) >>> (1 : Nat)).toNat)
                (by have := hlv_lt; have := hnv_le; omega) _, hm⟩
            · c0_hsteps!; exact hJlv mr ⟨kbr, hkr, hmr⟩
          · c0_hsteps!; exact hJlv mr ⟨kbr, hkr, hmr⟩
      · c0_hsteps!; exact hJg mr kbr hkr hmr
    · intro Lr hLr; c0_hsteps!
      exact hLr rsz.toNat (0#32, ()) mt2 ⟨kbt2, hkt2, Nat.zero_le _, by simp, hmt2⟩
  · c0_hsteps!; exact hJg mt2 kbt2 hkt2 hmt2

private theorem k6_core_trail_loop_wp {Γ : Env} {pk : BitVec 64} {kbuf : List (BitVec 32)}
    {nc nv acap : BitVec 32} {R : Mem 64 → Prop} {Q : Post []} {X : XPost}
    {Jinc : Cont [.bits 32]}
    (hlen : 2912 ≤ kbuf.length) (hnc_le : nc.toNat ≤ 256) (hnv_le : nv.toNat ≤ 64)
    (hnv0 : kbuf[0]'(by omega) = nv) (hnc1 : kbuf[1]'(by omega) = nc)
    (hacap15 : kbuf[15]'(by omega) = acap)
    (hJinc : ∀ if2 m', ∀ kbf2, CoreInv kbuf nc kbf2 → (array (t := i32) pk kbf2 ⋆ R) m' →
      Jinc (if2, ()) m')
    {kbj : List (BitVec 32)} {mj : Mem 64}
    (hkj : CoreInv kbuf nc kbj) (hmj : (array (t := i32) pk kbj ⋆ R) mj) :
    wp Γ Q X (k6CoreTrailE pk nc nv acap Jinc) mj := by
  let invCore := CoreInv kbuf nc
  have invCore_set_meta := @coreInv_set_meta kbuf nc hnc_le
  have hkj_l := hkj.2.1
  dsimp only [k6CoreTrailE, k6CorePreGroupE, k6PostFix, k6SLd3, k6SLd4, k6SL3, k6SL4,
    k6SLet, k6SLetI, k6SLd, k6SSt, k6SJF, k6SJT, k6SGrpBI, k6SGrpBN, k6SGrpKI, k6DfltT,
    k6Dflt, Prod.fst]
  c0_hsteps_nogrp; dsimp only [Prod.fst]; c0_hsteps_nogrp
  refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
    (fun ti => (ti, ())) (fun ti => ti.toNat ≤ 64) ?_ ?_
  · intro _ ti hti; c0_hsteps_nogrp
    refine wp_loop_group (ts := [i32])
      (fun rem (tic, ()) mt => ∃ kbt, invCore kbt ∧ tic.toNat ≤ 64 ∧ rem = tic.toNat ∧
        (array (t := i32) pk kbt ⋆ R) mt) ?_ ?_
    · rintro Lt remt ⟨tic, ⟨⟩⟩ mt hLt ⟨kbt, hkt, htic, rfl, hmt⟩
      have hkt_l := hkt.2.1; have hlt28 := hkt.1.length_lt; have hlen_ge := hkt.1.length_ge
      c0_hsplit
      · have ht_pos : 0 < tic.toNat := hc
        clear hc
        let t1 := tic - 1#32
        have ht1_lt : t1.toNat < 64 := by
          dsimp only [t1]; rw [m8_bv32_sub1_toNat ht_pos]; omega
        have ht1_dec : t1.toNat < tic.toNat := by
          dsimp only [t1]; rw [m8_bv32_sub1_toNat ht_pos]; omega
        c0_hsplit
        · c0_hsteps!; exact hLt t1.toNat (t1, ()) mt ht1_dec ⟨kbt, hkt, by omega, rfl, hmt⟩
        · have ht_352_mod : (BitVec.toNat (352 : BitVec 32) +
              (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + tic.toNat)) % 2 ^ 32 = 352 + t1.toNat := by
            change (352 + (2 ^ 32 - 1 + tic.toNat)) % 2 ^ 32 = 352 + t1.toNat
            rw [show t1.toNat = tic.toNat - 1 from m8_bv32_sub1_toNat ht_pos]; omega
          have ht_352_c0 : (BitVec.setWidth 64
              ((352 : BitVec 32) + (tic - (1 : BitVec 32)))).toNat = 352 + t1.toNat := by
            have := ht1_lt; c0_bound
          have ht_352_bd_mod : (BitVec.toNat (352 : BitVec 32) +
              (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + tic.toNat)) % 2 ^ 32 < kbt.length := by
            rw [ht_352_mod]; have := hkt_l; have := hlen; omega
          have ht_352_bd_c0 : (BitVec.setWidth 64
              ((352 : BitVec 32) + (tic - (1 : BitVec 32)))).toNat < kbt.length := by
            rw [ht_352_c0]; have := hkt_l; have := hlen; omega
          let v_t := (kbt[352 + t1.toNat]'(by have := hkt_l; have := hlen; omega)) >>> (1 : Nat)
          have hvt_lt : v_t.toNat < nv.toNat := by
            refine Nat.lt_of_not_le (show ¬nv.toNat ≤ v_t.toNat from ?_)
            dsimp only [v_t]
            rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
              ← m8_k6_get_congr ht_352_mod ht_352_bd_mod (by omega)]
            simpa [hnv0, Nat.reducePow, k6_c0] using hc
          clear hc
          have hget_352_c0 : kbt[(BitVec.setWidth 64
              ((352 : BitVec 32) + (tic - (1 : BitVec 32)))).toNat]'ht_352_bd_c0 =
              kbt[352 + t1.toNat]'(by have := hkt_l; have := hlen; omega) :=
            m8_k6_get_congr ht_352_c0 ht_352_bd_c0 (by omega)
          have h416_t_eq : (BitVec.setWidth 64 ((416 : BitVec 32) + (kbt[(BitVec.setWidth 64
              ((352 : BitVec 32) + (tic - (1 : BitVec 32)))).toNat]'ht_352_bd_c0 >>>
              (1 : Nat)))).toNat = 416 + v_t.toNat := by
            rw [hget_352_c0]; change (BitVec.setWidth 64 (416#32 + v_t)).toNat = 416 + v_t.toNat
            have := hvt_lt; have := hnv_le; c0_bound
          have h416_t_c0 : (BitVec.setWidth 64 ((416 : BitVec 32) + (kbt[(BitVec.setWidth 64
              ((352 : BitVec 32) + (tic - (1 : BitVec 32)))).toNat]'ht_352_bd_c0 >>>
              (1 : Nat)))).toNat < kbt.length := by
            rw [h416_t_eq]; have := hkt_l; have := hlen; omega
          have h96_t_eq : (BitVec.setWidth 64 ((96 : BitVec 32) + (kbt[(BitVec.setWidth 64
              ((352 : BitVec 32) + (tic - (1 : BitVec 32)))).toNat]'ht_352_bd_c0 >>>
              (1 : Nat)))).toNat = 96 + v_t.toNat := by
            rw [hget_352_c0]; change (BitVec.setWidth 64 (96#32 + v_t)).toNat = 96 + v_t.toNat
            have := hvt_lt; have := hnv_le; c0_bound
          have h96_t_c0 : (BitVec.setWidth 64 ((96 : BitVec 32) + (kbt[(BitVec.setWidth 64
              ((352 : BitVec 32) + (tic - (1 : BitVec 32)))).toNat]'ht_352_bd_c0 >>>
              (1 : Nat)))).toNat < kbt.length := by
            rw [h96_t_eq]; have := hkt_l; have := hlen; omega
          c0_hsplit
          · c0_hsteps!; exact hLt t1.toNat (t1, ()) mt ht1_dec ⟨kbt, hkt, by omega, rfl, hmt⟩
          · clear hc
            have hm1_eq := m8_k6_set_congr (xs := kbt) h416_t_eq
              (congrArg (· &&& ~~~(2 : BitVec 32))
                (m8_k6_get_congr (xs := kbt) h416_t_eq h416_t_c0 (by have := hkt_l; omega)))
            c0_hsplit
            · c0_hsteps!; simp only [k6_ofnat_one] at hm; rw [hm1_eq] at hm
              exact hLt t1.toNat (t1, ()) _ ht1_dec
                ⟨_, coreInv_set_flags hkt (v := v_t.toNat)
                  (by have := hvt_lt; have := hnv_le; omega) _, by omega, rfl, hm⟩
            · simp only [k6_ofnat_one] at hm; rw [hm1_eq] at hm
              obtain ⟨kbt1, hkt1, hkt1_l, hkbt1_96, hm_n1⟩ :
                  ∃ kbt1 : List (BitVec 32), invCore kbt1 ∧ kbt1.length = kbuf.length ∧
                    kbt1[96 + v_t.toNat]? = kbt[96 + v_t.toNat]? ∧
                    (array (t := i32) pk kbt1 ⋆ R) m :=
                ⟨_, coreInv_set_flags hkt
                  (v := v_t.toNat) (by have := hvt_lt; have := hnv_le; omega) _,
                  by simp [hkt_l], List.getElem?_set_ne (by omega), hm⟩
              clear hm; have hm := hm_n1; clear hm_n1
              have hrsn : (kbt1[96 + v_t.toNat]'(by have := hkt1_l; omega)).toNat < nc.toNat := by
                have hvt_div : v_t.toNat =
                    (kbt[352 + t1.toNat]'(by have := hkt_l; omega)).toNat / 2 := by
                  dsimp only [v_t]; rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                have hk_raw : (kbt[(BitVec.toNat (352 : BitVec 32) + (2 ^ 32 -
                    BitVec.toNat (1 : BitVec 32) + tic.toNat)) % 2 ^ 32]'(ht_352_bd_mod)).toNat /
                    2 = v_t.toNat := by
                  rw [m8_k6_get_congr ht_352_mod ht_352_bd_mod (by omega)]; exact hvt_div.symm
                have h416_ne : (BitVec.toNat (416 : BitVec 32) +
                    (kbt[(BitVec.toNat (352 : BitVec 32) + (2 ^ 32 - BitVec.toNat (1 : BitVec 32) +
                      tic.toNat)) % 2 ^ 32]'(ht_352_bd_mod)).toNat / 2) % 2 ^ 32 ≠
                    (BitVec.toNat (96 : BitVec 32) +
                    (kbt[(BitVec.toNat (352 : BitVec 32) + (2 ^ 32 - BitVec.toNat (1 : BitVec 32) +
                      tic.toNat)) % 2 ^ 32]'(ht_352_bd_mod)).toNat / 2) % 2 ^ 32 := by
                  rw [hk_raw]; change (416 + v_t.toNat) % 2 ^ 32 ≠ (96 + v_t.toNat) % 2 ^ 32
                  have := hvt_lt; have := hnv_le; omega
                have h96_idx_eq : (BitVec.toNat (96 : BitVec 32) +
                    (kbt[(BitVec.toNat (352 : BitVec 32) + (2 ^ 32 - BitVec.toNat (1 : BitVec 32) +
                      tic.toNat)) % 2 ^ 32]'(ht_352_bd_mod)).toNat / 2) % 2 ^ 32 =
                    96 + v_t.toNat := by
                  rw [hk_raw]; change (96 + v_t.toNat) % 2 ^ 32 = _
                  have := hvt_lt; have := hnv_le; omega
                have hc' := hc; rw [List.getElem_set_ne h416_ne] at hc'
                rw [m8_k6_get_congr h96_idx_eq (by rw [h96_idx_eq]; have := hkt_l; omega)
                  (by have := hkt_l; omega)] at hc'
                rw [m8_k6_elem_of_opt hkbt1_96 (by have := hkt1_l; omega) (by have := hkt_l; omega)]
                exact Nat.lt_of_not_le (by simpa [hnc1] using hc')
              clear hc
              obtain ⟨rsn, hrsn_def, hrsn⟩ : ∃ rsn : BitVec 32,
                  rsn = kbt1[96 + v_t.toNat]'(by have := hkt1_l; omega) ∧
                  rsn.toNat < nc.toNat :=
                ⟨kbt1[96 + v_t.toNat]'(by have := hkt1_l; omega), rfl, hrsn⟩
              have hkbt_rsn : kbt[96 + v_t.toNat]'(by have := hkt_l; omega) = rsn :=
                (m8_k6_elem_of_opt hkbt1_96 (by have := hkt1_l; omega)
                  (by have := hkt_l; omega)).symm.trans hrsn_def.symm
              have hget_raw_rsn : ∀ hbd, (kbt.set (BitVec.setWidth 64 ((416 : BitVec 32) +
                  (kbt[(BitVec.setWidth 64 ((352 : BitVec 32) +
                    (tic - (1 : BitVec 32)))).toNat]'ht_352_bd_c0 >>> (1 : Nat)))).toNat
                  (kbt[(BitVec.setWidth 64 ((416 : BitVec 32) + (kbt[(BitVec.setWidth 64
                    ((352 : BitVec 32) + (tic - (1 : BitVec 32)))).toNat]'ht_352_bd_c0 >>>
                    (1 : Nat)))).toNat]'h416_t_c0 &&& ~~~(2 : BitVec 32)))[(BitVec.setWidth 64
                    ((96 : BitVec 32) + (kbt[(BitVec.setWidth 64 ((352 : BitVec 32) +
                      (tic - (1 : BitVec 32)))).toNat]'ht_352_bd_c0 >>> (1 : Nat)))).toNat]'hbd =
                  rsn := by
                intro hbd; rw [List.getElem_set_ne (by rw [h416_t_eq, h96_t_eq]; omega)]
                exact (m8_k6_get_congr h96_t_eq _ _).trans hkbt_rsn
              simp only [k6_ofnat_one, hget_raw_rsn]
              have hk_rsn := hkt1.1.clause_ok (by
                have h1eq := hkt1.2.2.1 1 (by have := hkt1.1.base_ge; omega) (Or.inl (by omega))
                rw [h1eq, m8_k6_get_eq (by omega), hnc1]; exact hrsn)
              let oldmr := kbt1[2144 + rsn.toNat]'(by have := hkt1_l; have := hnc_le; omega)
              have hpr := k6_km_core_or_pres oldmr
              have h2144_r_eq : (BitVec.setWidth 64 ((2144 : BitVec 32) + rsn)).toNat =
                  2144 + rsn.toNat :=
                k6_sw64_add_2144 (Nat.lt_of_lt_of_le hrsn hnc_le)
              have h1888_r_eq : (BitVec.setWidth 64 ((1888 : BitVec 32) + rsn)).toNat =
                  1888 + rsn.toNat :=
                k6_sw64_add_1888 (Nat.lt_of_lt_of_le hrsn hnc_le)
              have h2144_r_c0 : (BitVec.setWidth 64 ((2144 : BitVec 32) + rsn)).toNat <
                  kbt1.length := by
                rw [h2144_r_eq]; exact k6_2144_len_lt hrsn hnc_le hkt1.1.base_ge
              have h1888_r_c0 : (BitVec.setWidth 64 ((1888 : BitVec 32) + rsn)).toNat <
                  kbt1.length := by
                rw [h1888_r_eq]; exact k6_1888_len_lt hrsn hnc_le hkt1.1.base_ge
              have hrsn_nw : (kbt1[1888 + rsn.toNat]'(k6_1888_len_lt hrsn hnc_le
                  hkt1.1.base_ge)).toNat + ((oldmr ||| 0x80000000#32) &&& 0xFFFF#32).toNat <
                  2 ^ 32 := by
                have h15 : (kbt1[15]?.getD 0#32).toNat = acap.toNat := by
                  have := hkt1.2.2.1 15 (by omega) (Or.inl (by omega))
                  rw [this, m8_k6_get_eq (by omega), hacap15]
                rw [m8_k6_get_eq (k6_1888_len_lt hrsn hnc_le hkt1.1.base_ge),
                  m8_k6_get_eq (k6_2144_len_lt hrsn hnc_le hkt1.1.base_ge), h15] at hk_rsn
                rw [hpr.1]; dsimp only [oldmr] at hk_rsn ⊢
                have := hkt1.1.length_lt; have := hkt1.1.length_ge; omega
              have hpr' : ((oldmr ||| 0x80000000#32) &&& 0xFFFF#32 =
                    (kbt1[2144 + rsn.toNat]?.getD 0#32) &&& 0xFFFF#32) ∧
                  ((oldmr ||| 0x80000000#32) &&& 0x40000000#32 =
                    (kbt1[2144 + rsn.toNat]?.getD 0#32) &&& 0x40000000#32) := by
                rw [m8_k6_get_eq (k6_2144_len_lt hrsn hnc_le hkt1.1.base_ge)]; exact hpr
              have hm2_eq := m8_k6_set_congr (xs := kbt1) h2144_r_eq
                (congrArg (· ||| (2147483648 : BitVec 32))
                  (m8_k6_get_congr (xs := kbt1) h2144_r_eq h2144_r_c0
                    (k6_2144_len_lt hrsn hnc_le hkt1.1.base_ge)))
              let roff := kbt1[1888 + rsn.toNat]'(k6_1888_len_lt hrsn hnc_le hkt1.1.base_ge)
              let rsz := (oldmr ||| 0x80000000#32) &&& 0xFFFF#32
              iterate 11 (c0_hstep; try dsimp only [Prod.fst])
              rw [hm2_eq] at hm
              obtain ⟨kbt2, hkt2, hkt2_l, hkbt2_1888, hkbt2_2144, hm_n2⟩ :
                  ∃ kbt2 : List (BitVec 32), invCore kbt2 ∧ kbt2.length = kbuf.length ∧
                    kbt2[1888 + rsn.toNat]? = kbt1[1888 + rsn.toNat]? ∧
                    kbt2[2144 + rsn.toNat]? = some (oldmr ||| (2147483648 : BitVec 32)) ∧
                    (array (t := i32) pk kbt2 ⋆ R) m :=
                ⟨kbt1.set (2144 + rsn.toNat) (oldmr ||| 0x80000000#32),
                  invCore_set_meta hkt1 hrsn hpr'.1 hpr'.2,
                  by simp [hkt1_l], List.getElem?_set_ne (by omega),
                  List.getElem?_set_self (by have := hkt1_l; have := hnc_le; omega), hm⟩
              clear hm; have hm := hm_n2; clear hm_n2
              have h1888_r2_c0 : (BitVec.setWidth 64 ((1888 : BitVec 32) + rsn)).toNat <
                  kbt2.length := by
                rw [h1888_r_eq]; exact k6_1888_len_lt hrsn hnc_le hkt2.1.base_ge
              have h2144_r2_c0 : (BitVec.setWidth 64 ((2144 : BitVec 32) + rsn)).toNat <
                  kbt2.length := by
                rw [h2144_r_eq]; exact k6_2144_len_lt hrsn hnc_le hkt2.1.base_ge
              c0_hsteps_nogrp
              have hget_raw_roff : ∀ hbd, kbt2[(BitVec.setWidth 64
                  ((1888 : BitVec 32) + rsn)).toNat]'hbd = roff := by
                intro hbd
                have htmp := m8_k6_get_congr (xs := kbt2) h1888_r_eq hbd
                  (by have := hkt2_l; have := hnc_le; omega)
                exact htmp.trans (m8_k6_elem_of_opt hkbt2_1888
                  (by have := hkt2_l; have := hnc_le; omega)
                  (by have := hkt1_l; have := hnc_le; omega))
              have hget_raw_newmr : ∀ hbd, kbt2[(BitVec.setWidth 64
                  ((2144 : BitVec 32) + rsn)).toNat]'hbd =
                  oldmr ||| (2147483648 : BitVec 32) := by
                intro hbd
                have htmp := m8_k6_get_congr (xs := kbt2) h2144_r_eq hbd
                  (by have := hkt2_l; have := hnc_le; omega)
                have h2144_val : kbt2[2144 + rsn.toNat]'(by have := hkt2_l; have := hnc_le; omega) =
                    oldmr ||| (2147483648 : BitVec 32) := by
                  rw [← m8_k6_get_eq (by have := hkt2_l; have := hnc_le; omega), hkbt2_2144]; rfl
                exact htmp.trans h2144_val
              have hget_raw_vt : ∀ hbd, kbt[(BitVec.setWidth 64
                  ((352 : BitVec 32) + (tic - (1 : BitVec 32)))).toNat]'hbd >>> (1 : Nat) =
                  v_t := by
                intro hbd
                rw [m8_k6_get_congr ht_352_c0 hbd (by have := hkt_l; have := hlen; omega)]
              simp only [hget_raw_roff, hget_raw_newmr, hget_raw_vt]
              have hrsz_lt : rsz.toNat < 65536 := by
                dsimp only [rsz]; rw [BitVec.toNat_and]
                exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
              refine wp_join0
                (fun mr => ∃ kbr, invCore kbr ∧ (array (t := i32) pk kbr ⋆ R) mr) ?_ ?_
              · intro _ mr ⟨kbr, hkr, hmr⟩; c0_hsteps!
                exact hLt t1.toNat (t1, ()) mr ht1_dec ⟨kbr, hkr, by omega, rfl, hmr⟩
              · intro Jg hJg
                have h_rsn : wp Γ Q X (k6CoreRsnE pk nc nv acap roff rsz v_t Jg) m :=
                  k6_core_rsn_mark_wp (Γ := Γ) (Q := Q) (X := X) (Jg := Jg)
                    (pk := pk) (kbuf := kbuf) (nc := nc) (nv := nv) (acap := acap)
                    (R := R) (kbt2 := kbt2) (mt2 := m) (roff := roff) (rsz := rsz) (vt := v_t)
                    hlen hnv_le hnv0 hacap15
                    (fun m' kbr hkr hmr => hJg m' ⟨kbr, hkr, hmr⟩) hkt2 hm hrsn_nw hrsz_lt
                dsimp only [k6CoreRsnE, k6CoreTrailE, k6CorePreGroupE, k6PostFix, k6SLd3, k6SLd4,
                  k6SL3, k6SL4, k6SLet, k6SLetI, k6SLd, k6SSt, k6SJF, k6SJT, k6SGrpBI, k6SGrpBN,
                  k6SGrpKI, k6SGrpKN, k6DfltT, k6Dflt] at h_rsn
                exact h_rsn
      · c0_hsteps_nogrp
        refine wp_loop_group (ts := [i32])
          (fun rem (i2, ()) mf2 => ∃ kbf2, invCore kbf2 ∧ i2.toNat ≤ nv.toNat ∧
            rem = nv.toNat - i2.toNat ∧ (array (t := i32) pk kbf2 ⋆ R) mf2) ?_ ?_
        · rintro Lf2 remf2 ⟨if2, ⟨⟩⟩ mf2 hLf2 ⟨kbf2, hkf2, hif2, rfl, hmf2⟩
          have hkf2_l := hkf2.2.1; c0_hsplit
          · have hi_lt : if2.toNat < nv.toNat := by simpa [hnv0, k6_c0] using hc
            clear hc
            have hif2_s : (if2 + 1#32).toNat = if2.toNat + 1 := by
              have := hnv_le; have := hi_lt; c0_bound
            have h416_i2 : (BitVec.setWidth 64 ((416 : BitVec 32) + if2)).toNat =
                416 + if2.toNat := by
              have := hnv_le; have := hi_lt; c0_bound
            c0_hsteps!; rw [m8_k6_set_congr h416_i2 rfl] at hm
            exact hLf2 (nv.toNat - (if2 + 1#32).toNat) (if2 + 1#32, ()) _ (by omega)
              ⟨_, coreInv_set_flags hkf2 (by have := hnv_le; have := hi_lt; omega) _,
                by omega, rfl, hm⟩
          · c0_hsteps!; exact hJinc if2 mf2 kbf2 hkf2 hmf2
        · intro Lf2 hLf2; c0_hsteps!
          exact hLf2 nv.toNat (0#32, ()) mt ⟨kbt, hkt, Nat.zero_le _, by simp, hmt⟩
    · intro Lt hLt; c0_hsteps!; exact hLt ti.toNat (ti, ()) mj ⟨kbj, hkj, hti, rfl, hmj⟩
  · intro Jti hJti; c0_hsplit
    · c0_hsteps!; exact hJti 64#32 (by decide)
    · c0_hsteps!; exact hJti _ (by c0_bound)

private theorem k6_core_inc_mark_wp {Γ : Env} {pk : BitVec 64} {kbuf : List (BitVec 32)}
    {nc nv acap inc off_i sz_i : BitVec 32} {R : Mem 64 → Prop} {Q : Post []} {X : XPost}
    {JincCl : Cont []} (hlen : 2912 ≤ kbuf.length) (hnv_le : nv.toNat ≤ 64)
    (hacap15 : kbuf[15]'(by omega) = acap)
    (hJincCl : ∀ mj', ∀ kbj', CoreInv kbuf nc kbj' →
      (array (t := i32) pk kbj' ⋆ R) mj' → JincCl () mj')
    {kbf1s : List (BitVec 32)} {m : Mem 64}
    (hk_f1s : CoreInv kbuf nc kbf1s) (hm : (array (t := i32) pk kbf1s ⋆ R) m)
    (hisz_nw : off_i.toNat + sz_i.toNat < 2 ^ 32) (hsz_lt : sz_i.toNat < 65536) :
    wp Γ Q X (k6CoreIncMarkE pk nc nv acap inc off_i sz_i JincCl) m := by
  let invCore := CoreInv kbuf nc
  dsimp only [k6CoreIncMarkE, k6CorePreGroupE, k6PostFix, k6SLd3, k6SLd4, k6SL3, k6SL4,
    k6SLet, k6SLetI, k6SLd, k6SSt, k6SJF, k6SJT, k6SGrpBI, k6SGrpKI, k6SGrpKN,
    k6DfltT, k6Dflt, Prod.fst]
  c0_hsplit
  · have hisz_bd : off_i.toNat + sz_i.toNat ≤ acap.toNat := by
      simpa [Nat.mod_eq_of_lt hisz_nw, k6_c15] using hc
    clear hc; c0_hsteps_nogrp
    refine wp_loop_group (ts := [i32])
      (fun rem (j, ()) mj1 => ∃ kbj1, invCore kbj1 ∧ j.toNat ≤ sz_i.toNat ∧
        rem = sz_i.toNat - j.toNat ∧ (array (t := i32) pk kbj1 ⋆ R) mj1) ?_ ?_
    · rintro Li remi ⟨ji, ⟨⟩⟩ mj1 hLi ⟨kbj1, hkj1, hji, rfl, hmj1⟩
      have hkj1_l := hkj1.2.1; have hlt28 := hkj1.1.length_lt
      c0_hsplit
      · have hj_lt : ji.toNat < sz_i.toNat := hc
        clear hc
        have hji1 : (ji + 1#32).toNat = ji.toNat + 1 := by
          have := hsz_lt; have := hj_lt; c0_bound
        have har_j : 2912 + off_i.toNat + ji.toNat < kbj1.length := by
          have := hkj1.1.length_ge
          have h15_j : (kbj1[15]?.getD 0#32).toNat = acap.toNat := by
            have := hkj1.2.2.1 15 (by omega) (Or.inl (by omega))
            rw [this, m8_k6_get_eq (by omega), hacap15]
          omega
        have har_j_c0 : (BitVec.setWidth 64 ((2912 : BitVec 32) + off_i + ji)).toNat <
            kbj1.length := by
          have := har_j; have := hlt28; c0_bound
        c0_hsteps_nogrp
        refine wp_join0 (fun mj2 => ∃ kbj2, invCore kbj2 ∧ (array (t := i32) pk kbj2 ⋆ R) mj2)
          ?_ ?_
        · intro _ mj2 ⟨kbj2, hkj2, hmj2⟩; c0_hsteps!
          exact hLi (sz_i.toNat - (ji + 1#32).toNat) (ji + 1#32, ()) mj2
            (by have := hji1; omega) ⟨kbj2, hkj2, by have := hji1; omega, rfl, hmj2⟩
        · intro Jlv hJlv
          c0_hsplit
          · have hj_v_lt : ((kbj1[2912 + off_i.toNat + ji.toNat]'har_j) >>> (1 : Nat)).toNat <
                nv.toNat := by
              have har_mod : (2912 + off_i.toNat + ji.toNat) % 2 ^ 32 =
                  2912 + off_i.toNat + ji.toNat := by
                have := har_j; have := hlt28; omega
              rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                ← m8_k6_get_congr har_mod (by rw [har_mod]; exact har_j) har_j]
              simpa [Nat.reducePow] using hc
            clear hc
            have hget_j_c0 : kbj1[(BitVec.setWidth 64
                ((2912 : BitVec 32) + off_i + ji)).toNat]'har_j_c0 =
                kbj1[2912 + off_i.toNat + ji.toNat]'har_j :=
              m8_k6_get_congr (by have := har_j; have := hlt28; c0_bound) _ _
            have h416_j_eq : (BitVec.setWidth 64 ((416 : BitVec 32) + (kbj1[(BitVec.setWidth 64
                ((2912 : BitVec 32) + off_i + ji)).toNat]'har_j_c0 >>> (1 : Nat)))).toNat =
                416 + ((kbj1[2912 + off_i.toNat + ji.toNat]'har_j) >>> (1 : Nat)).toNat := by
              rw [hget_j_c0]; have := hj_v_lt; have := hnv_le; c0_bound
            have h416_j_c0 : (BitVec.setWidth 64 ((416 : BitVec 32) + (kbj1[(BitVec.setWidth 64
                ((2912 : BitVec 32) + off_i + ji)).toNat]'har_j_c0 >>> (1 : Nat)))).toNat <
                kbj1.length := by
              rw [h416_j_eq]; have := hj_v_lt; have := hnv_le; have := hkj1_l; have := hlen; omega
            c0_hsteps!
            have hmj_eq := m8_k6_set_congr (xs := kbj1) h416_j_eq
              (congrArg (· ||| (2 : BitVec 32))
                (m8_k6_get_congr (xs := kbj1) h416_j_eq h416_j_c0
                  (by have := hkj1_l; have := hlen; omega)))
            simp only [k6_ofnat_one] at hm; rw [hmj_eq] at hm
            exact hJlv _ ⟨_, coreInv_set_flags hkj1 (v := ((kbj1[2912 + off_i.toNat +
              ji.toNat]'har_j) >>> (1 : Nat)).toNat)
              (by have := hj_v_lt; have := hnv_le; omega) _, hm⟩
          · c0_hsteps!; exact hJlv mj1 ⟨kbj1, hkj1, hmj1⟩
      · c0_hsteps!; exact hJincCl mj1 kbj1 hkj1 hmj1
    · intro Li hLi; c0_hsteps!
      exact hLi sz_i.toNat (0#32, ()) m ⟨kbf1s, hk_f1s, Nat.zero_le _, by simp, hm⟩
  · c0_hsteps!; exact hJincCl m kbf1s hk_f1s hm

public section

/-- Certifies `fullK6CoreM7Spec` for `full_k6_core_m7`. -/
theorem full_k6_core_m7_wp (Γ : Env) :
    ∀ a m Q X, fullK6CoreM7Spec a m Q X → Func.wp Γ full_k6_core_m7_body a m Q X := by
  rintro ⟨pk, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨kbuf, R, hok0, hm0, hQ⟩ := fullK6CoreM7Spec_elim hSpec
  have hlen := hok0.base_ge
  let nc := kbuf[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 1)).toNat]'(by
    change 1 % 2 ^ 64 < _; omega)
  let nv := kbuf[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat]'(by
    change 0 % 2 ^ 64 < _; omega)
  let acap := kbuf[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 15)).toNat]'(by
    change 15 % 2 ^ 64 < _; omega)
  unfold Func.wp full_k6_core_m7_body; c0_hsplit
  · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ => rfl) (fun _ _ => ⟨rfl, rfl⟩) hm0
  · have hnc_le : nc.toNat ≤ 256 := Nat.le_of_not_lt (by simpa [nc, k6_c1] using hc)
    clear hc; c0_hsplit
    · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ => rfl) (fun _ _ => ⟨rfl, rfl⟩) hm0
    · have hnv_le : nv.toNat ≤ 64 := Nat.le_of_not_lt (by simpa [nv, k6_c0] using hc)
      clear hc
      let invCore := CoreInv kbuf nc
      have invCore_set_meta := @coreInv_set_meta kbuf nc hnc_le
      c0_hsteps_nogrp
      refine wp_loop_group (ts := [i32])
        (fun rem (i, ()) mi => ∃ kbi, invCore kbi ∧ i.toNat ≤ nc.toNat ∧
          rem = nc.toNat - i.toNat ∧ (array (t := i32) pk kbi ⋆ R) mi) ?_ ?_
      · rintro L1 rem1 ⟨i1, ⟨⟩⟩ m1 hL1 ⟨kb1, hk1, hi1_le, rfl, hm1⟩
        have hk1_l := hk1.2.1; c0_hsplit
        · have hi1_lt : i1.toNat < nc.toNat := hc; clear hc
          have hi1_succ : (i1 + 1#32).toNat = i1.toNat + 1 := by
            have := hnc_le; have := hi1_lt; c0_bound
          have hbd1 : 2144 + i1.toNat < kb1.length := by
            have := hk1_l; have := hlen; have := hnc_le; omega
          let oldm := kb1[2144 + i1.toNat]'hbd1
          have hpres := k6_km_core_clear_pres oldm; c0_hsteps!
          have hidx1 : (BitVec.setWidth 64 (2144 + i1)).toNat = 2144 + i1.toNat := by
            have := hnc_le; have := hi1_lt; c0_bound
          have hkb1_eq : kb1.set (BitVec.setWidth 64 (2144 + i1)).toNat
              (kb1[(BitVec.setWidth 64 (2144 + i1)).toNat]'(by omega) &&& ~~~2147483648) =
              kb1.set (2144 + i1.toNat) (oldm &&& ~~~2147483648#32) :=
            m8_k6_set_congr hidx1
              (congrArg (· &&& ~~~2147483648#32) (m8_k6_get_congr hidx1 _ _))
          rw [hkb1_eq] at hm; dsimp only [oldm] at hpres hm
          rw [← m8_k6_get_eq hbd1] at hpres hm
          exact hL1 (nc.toNat - (i1 + 1#32).toNat) (i1 + 1#32, ()) _
            (by have := hnc_le; have := hi1_lt; have := hi1_succ; omega)
            ⟨_, invCore_set_meta hk1 hi1_lt hpres.1 hpres.2, by omega, rfl, hm⟩
        · have hi1_nc : i1 = nc := BitVec.eq_of_toNat_eq (by
            have : ¬i1.toNat < nc.toNat := hc; omega)
          clear hc; c0_hsteps_nogrp
          refine wp_join_state1 (t := i32) (α := List (BitVec 32) × BitVec 32) (fun x => x.2)
            (fun x mj => invCore x.1 ∧ (array (t := i32) pk x.1 ⋆ R) mj) ?_ ?_
          · rintro _ ⟨kbj, _⟩ mj ⟨hkj, hmj⟩
            dsimp only [Prod.fst]
            have h_fix := k6_core_fixpoint_wp (Γ := Γ) (Q := Q) (X := X)
              hlen rfl rfl rfl hnc_le hnv_le
              (fun kbp mp hkp hmp => hQ kbp mp hkp.2.1 hkp.2.2.1
                (fun cid hcid => hkp.2.2.2 cid
                  (by rw [m8_k6_get_eq (by omega)] at hcid; exact hcid)) hmp) hkj hmj
            dsimp only [k6FixpointE, k6SLet, k6SLd, k6SJF, k6SGrpBI, k6DfltT, k6Dflt] at h_fix
            exact h_fix
          · intro Jinc hJinc
            let inc := kb1[7]'(by omega)
            c0_hsplit
            · have hinc : inc.toNat < nc.toNat := by
                simpa [inc, nc, k6_c1, k6_c7] using hc
              clear hc
              refine wp_loop_group (ts := [i32])
                (fun rem (i, ()) mf => ∃ kbf, invCore kbf ∧ i.toNat ≤ nv.toNat ∧
                  rem = nv.toNat - i.toNat ∧ (array (t := i32) pk kbf ⋆ R) mf) ?_ ?_
              · rintro Lf remf ⟨if1, ⟨⟩⟩ mf1 hLf ⟨kbf1, hkf1, hif1, rfl, hmf1⟩
                have hkf1_l := hkf1.2.1; c0_hsplit
                · have hi_lt : if1.toNat < nv.toNat := hc
                  clear hc
                  have hif1_s : (if1 + 1#32).toNat = if1.toNat + 1 := by
                    have := hnv_le; have := hi_lt; c0_bound
                  have h416_i : (BitVec.setWidth 64 ((416 : BitVec 32) + if1)).toNat =
                      416 + if1.toNat := by
                    have := hnv_le; have := hi_lt; c0_bound
                  c0_hsteps!; rw [m8_k6_set_congr h416_i rfl] at hm
                  exact hLf (nv.toNat - (if1 + 1#32).toNat) (if1 + 1#32, ()) _ (by omega)
                    ⟨_, coreInv_set_flags hkf1 (by have := hnv_le; have := hi_lt; omega) _,
                      by omega, rfl, hm⟩
                · clear hc
                  have hkb_inc := hkf1.1.clause_ok (by
                    have h1eq := hkf1.2.2.1 1 (by have := hkf1.1.base_ge; omega) (Or.inl (by omega))
                    rw [h1eq, m8_k6_get_eq (by omega)]; exact hinc)
                  let oldmi := kbf1[2144 + inc.toNat]'(k6_2144_len_lt hinc hnc_le hkf1.1.base_ge)
                  have hpmi := k6_km_core_or_pres oldmi
                  have hlt28 := hkf1.1.length_lt; have hlen_ge := hkf1.1.length_ge
                  have h15 : (kbf1[15]?.getD 0#32).toNat = acap.toNat := by
                    have := hkf1.2.2.1 15 (by omega) (Or.inl (by omega))
                    rw [this, m8_k6_get_eq (by omega)]; rfl
                  have hinc_sz_nw : (kbf1[1888 + inc.toNat]'(k6_1888_len_lt hinc hnc_le
                      hkf1.1.base_ge)).toNat +
                      ((oldmi ||| 0x80000000#32) &&& 0xFFFF#32).toNat < 2 ^ 32 := by
                    rw [m8_k6_get_eq (k6_1888_len_lt hinc hnc_le hkf1.1.base_ge),
                      m8_k6_get_eq (k6_2144_len_lt hinc hnc_le hkf1.1.base_ge), h15] at hkb_inc
                    dsimp only [oldmi] at hpmi ⊢; rw [hpmi.1]; have := hkf1.1.base_ge; omega
                  have hk7_bd : (BitVec.ofNat (OfNat.ofNat 64)
                      (OfNat.ofNat 7)).toNat < kb1.length := by
                    change 7 % 2 ^ 64 < kb1.length; omega
                  have hinc_c0_lt : (kb1[(BitVec.ofNat (OfNat.ofNat 64)
                      (OfNat.ofNat 7)).toNat]'hk7_bd).toNat < nc.toNat := hinc
                  have h1888_inc_c0 : (BitVec.setWidth 64 ((1888 : BitVec 32) +
                      kb1[(BitVec.ofNat (OfNat.ofNat 64)
                        (OfNat.ofNat 7)).toNat]'hk7_bd)).toNat < kbf1.length := by
                    have := hkf1.1.base_ge; have := hnc_le; have := hinc_c0_lt; c0_bound
                  have h2144_inc_c0 : (BitVec.setWidth 64 ((2144 : BitVec 32) +
                      kb1[(BitVec.ofNat (OfNat.ofNat 64)
                        (OfNat.ofNat 7)).toNat]'hk7_bd)).toNat < kbf1.length := by
                    have := hkf1.1.base_ge; have := hnc_le; have := hinc_c0_lt; c0_bound
                  have h2144_inc_c0s : (BitVec.setWidth 64 ((2144 : BitVec 32) +
                      kb1[(BitVec.ofNat (OfNat.ofNat 64)
                        (OfNat.ofNat 7)).toNat]'hk7_bd)).toNat <
                      (kbf1.set (BitVec.setWidth 64 ((2144 : BitVec 32) +
                          kb1[(BitVec.ofNat (OfNat.ofNat 64)
                            (OfNat.ofNat 7)).toNat]'hk7_bd)).toNat
                        (kbf1[(BitVec.setWidth 64 ((2144 : BitVec 32) +
                          kb1[(BitVec.ofNat (OfNat.ofNat 64)
                            (OfNat.ofNat 7)).toNat]'hk7_bd)).toNat]'h2144_inc_c0 |||
                          (2147483648 : BitVec 32))).length := by
                    rw [List.length_set]; exact h2144_inc_c0
                  c0_hsteps_nogrp; dsimp only [Prod.fst]; c0_hsteps_nogrp
                  refine wp_join0 (fun mj => ∃ kbj, invCore kbj ∧ (array (t := i32) pk kbj ⋆ R) mj)
                    ?_ ?_
                  · intro _ mj ⟨kbj, hkj, hmj⟩
                    have h_trail := k6_core_trail_loop_wp (Γ := Γ) (Q := Q) (X := X) (Jinc := Jinc)
                      hlen hnc_le hnv_le rfl rfl rfl
                      (fun if2 m' kbf2 hkf2 hmf2 => hJinc (kbf2, if2) m' ⟨hkf2, hmf2⟩) hkj hmj
                    dsimp only [k6CoreTrailE, k6CorePreGroupE, k6PostFix, k6SLd3, k6SLd4, k6SL3,
                      k6SL4, k6SLet, k6SLetI, k6SLd, k6SSt, k6SJF, k6SJT, k6SGrpBI, k6SGrpBN,
                      k6SGrpKI, k6DfltT, k6Dflt] at h_trail
                    exact h_trail
                  · intro JincCl hJincCl
                    let off_i := kbf1[1888 + inc.toNat]'(k6_1888_len_lt hinc hnc_le hkf1.1.base_ge)
                    let sz_i := (oldmi ||| 0x80000000#32) &&& 0xFFFF#32
                    have h2144_idx : (BitVec.setWidth 64 ((2144 : BitVec 32) +
                        kb1[(BitVec.ofNat (OfNat.ofNat 64)
                          (OfNat.ofNat 7)).toNat]'hk7_bd)).toNat = 2144 + inc.toNat :=
                      k6_sw64_add_2144 (Nat.lt_of_lt_of_le hinc hnc_le)
                    have h1888_idx : (BitVec.setWidth 64 ((1888 : BitVec 32) +
                        kb1[(BitVec.ofNat (OfNat.ofNat 64)
                          (OfNat.ofNat 7)).toNat]'hk7_bd)).toNat = 1888 + inc.toNat :=
                      k6_sw64_add_1888 (Nat.lt_of_lt_of_le hinc hnc_le)
                    have hpmi' : ((oldmi ||| 0x80000000#32) &&& 0xFFFF#32 =
                          (kbf1[2144 + inc.toNat]?.getD 0#32) &&& 0xFFFF#32) ∧
                        ((oldmi ||| 0x80000000#32) &&& 0x40000000#32 =
                          (kbf1[2144 + inc.toNat]?.getD 0#32) &&& 0x40000000#32) := by
                      rw [m8_k6_get_eq (k6_2144_len_lt hinc hnc_le hkf1.1.base_ge)]; exact hpmi
                    have hm_s_eq := m8_k6_set_congr (xs := kbf1) h2144_idx
                      (congrArg (· ||| (2147483648 : BitVec 32))
                        (m8_k6_get_congr (xs := kbf1) h2144_idx h2144_inc_c0
                          (k6_2144_len_lt hinc hnc_le hkf1.1.base_ge)))
                    rw [hm_s_eq] at hm
                    let kbf1s := kbf1.set (2144 + inc.toNat) (oldmi ||| 0x80000000#32)
                    have hk_f1s : invCore kbf1s := invCore_set_meta hkf1 hinc hpmi'.1 hpmi'.2
                    have hget_raw_off_i : ∀ hbd, (kbf1.set (BitVec.setWidth 64 ((2144 : BitVec 32) +
                        kb1[(BitVec.ofNat (OfNat.ofNat 64)
                          (OfNat.ofNat 7)).toNat]'hk7_bd)).toNat
                        (kbf1[(BitVec.setWidth 64 ((2144 : BitVec 32) +
                          kb1[(BitVec.ofNat (OfNat.ofNat 64)
                            (OfNat.ofNat 7)).toNat]'hk7_bd)).toNat]'h2144_inc_c0 |||
                          (2147483648 : BitVec 32)))[(BitVec.setWidth 64
                            ((1888 : BitVec 32) + kb1[(BitVec.ofNat (OfNat.ofNat 64)
                              (OfNat.ofNat 7)).toNat]'hk7_bd)).toNat]'hbd = off_i := by
                      intro hbd; rw [List.getElem_set_ne (by rw [h2144_idx, h1888_idx]; omega)]
                      exact m8_k6_get_congr h1888_idx _ _
                    have hget_raw_newmi : ∀ hbd, (kbf1.set (BitVec.setWidth 64 ((2144 : BitVec 32) +
                        kb1[(BitVec.ofNat (OfNat.ofNat 64)
                          (OfNat.ofNat 7)).toNat]'hk7_bd)).toNat
                        (kbf1[(BitVec.setWidth 64 ((2144 : BitVec 32) +
                          kb1[(BitVec.ofNat (OfNat.ofNat 64)
                            (OfNat.ofNat 7)).toNat]'hk7_bd)).toNat]'h2144_inc_c0 |||
                          (2147483648 : BitVec 32)))[(BitVec.setWidth 64
                            ((2144 : BitVec 32) + kb1[(BitVec.ofNat (OfNat.ofNat 64)
                              (OfNat.ofNat 7)).toNat]'hk7_bd)).toNat]'hbd =
                        oldmi ||| (2147483648 : BitVec 32) := by
                      intro hbd
                      rw [List.getElem_set_self (by rw [List.length_set]; exact h2144_inc_c0)]
                      exact congrArg (· ||| (2147483648 : BitVec 32))
                        (m8_k6_get_congr h2144_idx h2144_inc_c0 _)
                    simp only [hget_raw_off_i, hget_raw_newmi]
                    have hsz_lt : sz_i.toNat < 65536 := by
                      dsimp only [sz_i]; rw [BitVec.toNat_and]
                      exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
                    have h_inc := k6_core_inc_mark_wp (Γ := Γ) (Q := Q) (X := X) (JincCl := JincCl)
                      (inc := inc) (off_i := off_i) (sz_i := sz_i)
                      hlen hnv_le rfl
                      (fun mj' kbj' hkj' hmj' => hJincCl mj' ⟨kbj', hkj', hmj'⟩)
                      hk_f1s hm hinc_sz_nw hsz_lt
                    dsimp only [k6CoreIncMarkE, k6CorePreGroupE, k6PostFix, k6SLd3, k6SLd4, k6SL3,
                      k6SL4, k6SLet, k6SLetI, k6SLd, k6SSt, k6SJF, k6SJT, k6SGrpBI, k6SGrpKI,
                      k6SGrpKN, k6DfltT, k6Dflt] at h_inc
                    exact h_inc
              · intro Lf hLf; c0_hsteps!
                exact hLf nv.toNat (0#32, ()) m1 ⟨kb1, hk1, Nat.zero_le _, by simp, hm1⟩
            · c0_hsteps!; rw [hi1_nc]; exact hJinc (kb1, nc) m1 ⟨hk1, hm1⟩
      · intro L1 hL1; c0_hsteps!
        exact hL1 nc.toNat (0#32, ()) m0
          ⟨kbuf, ⟨hok0, rfl, fun _ _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩, Nat.zero_le _, by simp, hm0⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Definition
