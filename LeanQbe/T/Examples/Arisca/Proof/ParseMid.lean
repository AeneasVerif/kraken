/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.ParseBase
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0StepAttr
meta import LeanQbe.T.Logic.C0StepAttr
import LeanQbe.T.Logic.Arith

/-!
# ARiSCA AIG Parser WP Proof (`Arisca.Proof.ParseMid`)

WP proof for `ar_parse_aig` (`ar_parse_aig_wp`), re-exporting all parser specs and lemmas from
`LeanQbe.T.Examples.Arisca.Proof.ParseBase`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Proof

open Std Std.ExtHashMap LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Arisca LeanQbe.T.Examples.Arisca.Src
open LeanQbe.T.Examples.Arisca.Src.Header LeanQbe.T.Examples.Arisca.Src.Parse

public section

private theorem arrayPad_u32_eq (a : BitVec 64) (xs : List (BitVec 32)) :
    arrayPad i32 a xs = (array (t := i32) a xs ⋆
      region (a + BitVec.ofNat 64 (4 * xs.length))
        (align8 (4 * xs.length) - 4 * xs.length)) := by
  simp only [arrayPad, SlabSeg.ofArrayAlign8, SlabSeg.ofArray, Ty.bytes, Ty.size]

private structure AigLoopSt where
  p : BitVec 64
  ok : Bool
  j : BitVec 32

private theorem bv32_add1_toNat {j n : BitVec 32} (h : j.toNat < n.toNat) :
    (j + 1#32).toNat = j.toNat + 1 := by c0_bv_omega [h]

private theorem bv32_aig_lhs {I M A j : BitVec 32} (hMIA : M.toNat = I.toNat + A.toNat)
    (hM : M.toNat ≤ 0x3FFFFFF0) (hj : j.toNat < A.toNat) :
    (2#32 * (I + 1#32 + j)).toNat = 2 * (I.toNat + 1 + j.toNat) := by
  c0_bv_omega [hMIA, hM, hj]

private theorem bv32_sub_toNat {a b : BitVec 32} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by c0_bv_omega [h]

private theorem nat_sub_succ_eq {a j : Nat} (h : j < a) : a - j = (a - (j + 1)) + 1 := by omega
private theorem nat_aig_lhs_next (a b : Nat) :
    2 * (a + 1 + b) + 2 = 2 * (a + 1 + (b + 1)) := by omega

private theorem bv32_ne_zero_pos {d : BitVec 32} (h : d ≠ 0#32) : 0 < d.toNat :=
  Nat.pos_of_ne_zero fun h0 => h (BitVec.eq_of_toNat_eq (by simpa using h0))

private theorem bv32_aig_d0_le {I M A j d0 : BitVec 32}
    (hMIA : M.toNat = I.toNat + A.toNat) (hM : M.toNat ≤ 0x3FFFFFF0) (hj : j.toNat < A.toNat)
    (hnot : ¬ ((2#32 : BitVec 32).toNat * ((I.toNat + (1#32 : BitVec 32).toNat + j.toNat) %
      2 ^ 32)) % 2 ^ 32 < d0.toNat) : d0.toNat ≤ 2 * (I.toNat + 1 + j.toNat) := by
  have h2 : (2#32 : BitVec 32).toNat = 2 := rfl
  have h1 : (1#32 : BitVec 32).toNat = 1 := rfl
  rw [h2, h1, Nat.mod_eq_of_lt (by omega : I.toNat + 1 + j.toNat < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : 2 * (I.toNat + 1 + j.toNat) < 2 ^ 32)] at hnot
  omega

private theorem bv32_aig_r0_le {I M A j d0 d1 : BitVec 32}
    (hMIA : M.toNat = I.toNat + A.toNat) (hM : M.toNat ≤ 0x3FFFFFF0) (hj : j.toNat < A.toNat)
    (hd0 : d0.toNat ≤ 2 * (I.toNat + 1 + j.toNat))
    (hnot : ¬ (2 ^ 32 - d0.toNat + (2#32 : BitVec 32).toNat *
      ((I.toNat + (1#32 : BitVec 32).toNat + j.toNat) % 2 ^ 32)) % 2 ^ 32 < d1.toNat) :
    d1.toNat ≤ 2 * (I.toNat + 1 + j.toNat) - d0.toNat := by
  have h2 : (2#32 : BitVec 32).toNat = 2 := rfl
  have h1 : (1#32 : BitVec 32).toNat = 1 := rfl
  have hd0_lt := d0.isLt
  rw [h2, h1, Nat.mod_eq_of_lt (by omega : I.toNat + 1 + j.toNat < 2 ^ 32),
    show 2 ^ 32 - d0.toNat + 2 * (I.toNat + 1 + j.toNat) =
      2 ^ 32 + (2 * (I.toNat + 1 + j.toNat) - d0.toNat) by omega,
    Nat.add_mod_left,
    Nat.mod_eq_of_lt (by omega : 2 * (I.toNat + 1 + j.toNat) - d0.toNat < 2 ^ 32)] at hnot
  omega

private theorem aig_fail_collapse {cx b : BitVec 64} {s s3 : ArCtxState}
    {rhs0 rhs1 olit : List (BitVec 32)} {aigBytes : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]}
    (hm_fail : ∀ (s' : ArCtxState), s'.w = s.w → s'.wlen = s.wlen → s'.art = s.art →
      s'.nw = s.nw → s'.pos = s.pos → s'.rs_n = s.rs_n → s'.rs_ptop = s.rs_ptop →
      s'.rs_cap = s.rs_cap → s'.rs_pcap = s.rs_pcap → ∀ m',
      (arCtxMem cx s' ⋆ region (s.w + 776#64) (s.wlen.toNat - 776) ⋆
        bytes b aigBytes ⋆ R) m' → Q (false, ⟨⟩) m')
    (hm : (arCtxMem cx s3 ⋆ arrayPad i32 s3.rhs0 rhs0 ⋆ arrayPad i32 s3.rhs1 rhs1 ⋆
      array (t := i32) s3.olit olit ⋆ region (s.w + s3.top) (s.wlen.toNat - s3.top.toNat) ⋆
      bytes b aigBytes ⋆ R) m)
    (hw : s3.w = s.w) (hwlen : s3.wlen = s.wlen) (hart : s3.art = s.art) (hnw : s3.nw = s.nw)
    (hpos : s3.pos = s.pos) (hrn : s3.rs_n = s.rs_n) (hrpt : s3.rs_ptop = s.rs_ptop)
    (hrc : s3.rs_cap = s.rs_cap) (hrpc : s3.rs_pcap = s.rs_pcap)
    (hfit : s.w.toNat + s.wlen.toNat < 2 ^ 64) (htop3 : s3.top.toNat =
      776 + align8 (4 * rhs0.length) + align8 (4 * rhs1.length) + 4 * olit.length)
    (hle3 : s3.top.toNat ≤ s.wlen.toNat) (hr0 : s3.rhs0 = s.w + 776#64)
    (hr1 : s3.rhs1 = s.w + BitVec.ofNat 64 (776 + align8 (4 * rhs0.length)))
    (hol : s3.olit =
      s.w + BitVec.ofNat 64 (776 + align8 (4 * rhs0.length) + align8 (4 * rhs1.length))) :
    Q (false, ⟨⟩) m :=
  let hm0 : (arrayPad i32 s3.rhs0 rhs0 ⋆ arrayPad i32 s3.rhs1 rhs1 ⋆
      array (t := i32) s3.olit olit ⋆ region (s.w + s3.top) (s.wlen.toNat - s3.top.toNat) ⋆
      (arCtxMem cx s3 ⋆ bytes b aigBytes ⋆ R)) m := sep_cast hm (by ac_rfl)
  hm_fail s3 hw hwlen hart hnw hpos hrn hrpt hrc hrpc m
    (sep_cast (aigArraysPre_collapse hfit htop3 hle3 hr0 hr1 hol hm0) (by ac_rfl))

private theorem parseAig_header (bs : List UInt8) (M I O A p_hdr : Nat)
    (h4 : 4 ≤ bs.length) (hb0 : bs[0].toNat = 97) (hb1 : bs[1].toNat = 105)
    (hb2 : bs[2].toNat = 103) (hb3 : bs[3].toNat = 32)
    (hparse : ∀ (fail : Option Aig)
        (k : Nat → Nat → Nat → Nat → Nat → List Nat → Option Aig),
      (pnum 32 fail ((toNatBytes bs).drop 4) fun M' bs => pnum 32 fail bs fun I' bs =>
        pnum 32 fail bs fun L' bs => pnum 32 fail bs fun O' bs =>
          pnum 10 fail bs fun A' bs => k M' I' L' O' A' bs) =
      k M I 0 O A ((toNatBytes bs).drop p_hdr)) (hm : M = I + A) :
    parseAig (toNatBytes bs) =
      poutsGo none (fun outs bs' => pandsGo none (fun ands => some ⟨M, I, outs, ands⟩)
        A (Nat.mul 2 (Nat.add I 1)) [] bs') O [] ((toNatBytes bs).drop p_hdr) := by
  have h01 : 0 < bs.length := by omega
  have h11 : 1 < bs.length := by omega
  have h21 : 2 < bs.length := by omega
  have h31 : 3 < bs.length := by omega
  unfold parseAig rd
  have hcons : toNatBytes bs = 97 :: 105 :: 103 :: 32 :: (toNatBytes bs).drop 4 := by
    conv => lhs; rw [← List.drop_zero (l := toNatBytes bs)]
    rw [drop_toNatBytes_cons h01, drop_toNatBytes_cons h11,
      drop_toNatBytes_cons h21, drop_toNatBytes_cons h31, hb0, hb1, hb2, hb3]
  conv => lhs; rw [hcons]
  have hb : Nat.beq 97 97 = true ∧ Nat.beq 105 105 = true ∧
      Nat.beq 103 103 = true ∧ Nat.beq 32 32 = true := by decide
  simp only [hb.1, hb.2.1, hb.2.2.1, hb.2.2.2]
  rw [hparse none (fun M' I' L' O' A' bs' => Bool.rec none
    (poutsGo none (fun outs bs => pandsGo none (fun ands => some ⟨M', I', outs, ands⟩)
      A' (Nat.mul 2 (Nat.add I' 1)) [] bs) O' [] bs')
    (Bool.rec false (Nat.beq M' (Nat.add I' A')) (Nat.beq L' 0)))]
  have hm' : Nat.beq M (Nat.add I A) = true := Nat.beq_eq.mpr hm
  simp only [Nat.beq_eq.mpr rfl, hm']

private theorem pch_ok_extract {bs : List UInt8} {n p p' : BitVec 64} {c : BitVec 8}
    (hok : (p.toNat < n.toNat ∧ (bs.getD p.toNat 0).toNat = c.toNat →
        true = true ∧ p' = p + 1 ∧ p'.toNat = p.toNat + 1 ∧ p.toNat + 1 ≤ n.toNat) ∧
      (¬ (p.toNat < n.toNat ∧ (bs.getD p.toNat 0).toNat = c.toNat) → true = false ∧ p' = p)) :
    p.toNat < n.toNat ∧ (bs.getD p.toNat 0).toNat = c.toNat ∧
      p' = p + 1 ∧ p'.toNat = p.toNat + 1 ∧ p.toNat + 1 ≤ n.toNat := by
  by_cases hcond : p.toNat < n.toNat ∧ (bs.getD p.toNat 0).toNat = c.toNat
  · obtain ⟨_, h1, h2, h3⟩ := hok.1 hcond; exact ⟨hcond.1, hcond.2, h1, h2, h3⟩
  · exact absurd (hok.2 hcond).1 (by decide)

local macro "aig_hdr_byte" k:num c:num b:ident aigBytes:ident s:ident m:ident hm:ident
    hc:ident hm_b:ident hm_f:ident hb:ident : tactic =>
  `(tactic| (
    c0_hstraight
    refine head_wp_load (addr := $b + BitVec.ofNat 64 $k)
      (v := BitVec.ofNat 8 (($aigBytes)[$k]'(by omega)).toNat)
      (by simp [Arg.val]) (load_bytes_at (i := $k) (by omega) (by omega) $hm_b) ?_
    c0_hsplit
    · c0_hsteps; exact $hm_f $s rfl rfl rfl rfl rfl rfl rfl rfl rfl $m $hm
    have $hb : (($aigBytes)[$k]'(by omega)).toNat = $c := by
      have hlt := (($aigBytes)[$k]'(by omega)).toNat_lt; c0_bv_omega [$hc, hlt]
    clear $hc))

local macro "aig_hdr_num" del:num hPnum:ident hPch:ident aigBytes:ident s:ident m:ident hm:ident
    hc:ident hm_b:ident hm_f:ident frameB:ident okX:ident pX:ident valX:ident
    okXc:ident pXc:ident hstep:ident : tactic =>
  `(tactic| (
    c0_hsteps_nogrp; c0_hcall $hPnum
    refine ⟨$aigBytes, $frameB, by omega, by omega, $hm_b, ?_⟩
    intro $okX $pX $valX h_num; c0_hsplit; rotate_left
    · c0_hsteps; exact $hm_f $s rfl rfl rfl rfl rfl rfl rfl rfl rfl $m $hm
    obtain ⟨_, _, _, h_fn⟩ := h_num $hc; clear $hc
    c0_hsteps_nogrp; c0_hcall $hPch
    refine ⟨$aigBytes, $frameB, by omega, by omega, $hm_b, ?_⟩
    intro $okXc $pXc ⟨hc_a, hc_b⟩; c0_hsplit; rotate_left
    · c0_hsteps; exact $hm_f $s rfl rfl rfl rfl rfl rfl rfl rfl rfl $m $hm
    obtain ⟨hp_lt, hc_eq, _, hp_nat, _⟩ :=
      pch_ok_extract (by have hc_r := $hc; rw [hc_r] at hc_a hc_b; exact ⟨hc_a, hc_b⟩)
    have $hstep : ∀ {β} (fail : β) k, pnum $del fail ((toNatBytes $aigBytes).drop _) k =
        k (BitVec.toNat $valX) ((toNatBytes $aigBytes).drop (BitVec.toNat $pXc)) := fun fail k => by
      simpa [hp_nat] using h_fn $del fail k hp_lt hc_eq
    clear $hc))

theorem ar_parse_aig_wp (Γ : LeanQbe.T.Env)
    (hPnum : ∀ xs m Q X, arPnumSpec xs m Q X →
      Γ "ar_pnum" [i64, i64, i64] [.bool, i64, i32] xs m Q X)
    (hPch : ∀ xs m Q X, arPchSpec xs m Q X →
      Γ "ar_pch" [i64, i64, i64, i8] [.bool, i64] xs m Q X)
    (hPvar : ∀ xs m Q X, arPvarintSpec xs m Q X →
      Γ "ar_pvarint" [i64, i64, i64] [.bool, i64, i32] xs m Q X)
    (hAlloc : ∀ xs m Q X, arAallocSpec xs m Q X →
      Γ "ar_aalloc" [i64, i64] [i64] xs m Q X) :
    ∀ xs m Q X, arParseAigSpec xs m Q X → Func.wp Γ ar_parse_aig_body xs m Q X := by
  rintro ⟨cx, b, n, ⟨⟩⟩ m Q X ⟨s, aigBytes, R, hwpos, htop0, hw776, hfit, hn, hm, hQ⟩
  have hm_fail : ∀ (s' : ArCtxState), s'.w = s.w → s'.wlen = s.wlen → s'.art = s.art →
      s'.nw = s.nw → s'.pos = s.pos → s'.rs_n = s.rs_n → s'.rs_ptop = s.rs_ptop →
      s'.rs_cap = s.rs_cap → s'.rs_pcap = s.rs_pcap → ∀ m',
      (arCtxMem cx s' ⋆ region (s.w + 776#64) (s.wlen.toNat - 776) ⋆
        bytes b aigBytes ⋆ R) m' → Q (false, ⟨⟩) m' :=
    fun s' hw hwlen hart hnw hpos hrn hrpt hrc hrpc m' hm' =>
      hQ false m' (Or.inl ⟨rfl, s', hw, hwlen, hart, hnw, hpos, hrn, hrpt, hrc, hrpc, hm'⟩)
  have hm_bytes : (bytes b aigBytes ⋆
      (arCtxMem cx s ⋆ (region (s.w + 776#64) (s.wlen.toNat - 776) ⋆ R))) m := by
    simp only [sep_assoc] at hm; exact sep_pull3r hm
  c0_hsplit
  · c0_hsteps; exact hm_fail s rfl rfl rfl rfl rfl rfl rfl rfl rfl m hm
  · have hn4 : 4 ≤ n.toNat := by c0_bv_omega [hc]
    clear hc
    aig_hdr_byte 0 97 b aigBytes s m hm hc hm_bytes hm_fail hb0
    aig_hdr_byte 1 105 b aigBytes s m hm hc hm_bytes hm_fail hb1
    aig_hdr_byte 2 103 b aigBytes s m hm hc hm_bytes hm_fail hb2
    aig_hdr_byte 3 32 b aigBytes s m hm hc hm_bytes hm_fail hb3
    let frameBytes : Mem 64 → Prop :=
      arCtxMem cx s ⋆ (region (s.w + 776#64) (s.wlen.toNat - 776) ⋆ R)
    aig_hdr_num 32 hPnum hPch aigBytes s m hm hc hm_bytes hm_fail frameBytes
      okM pM M okMc pMc hM_step
    aig_hdr_num 32 hPnum hPch aigBytes s m hm hc hm_bytes hm_fail frameBytes
      okI pI I okIc pIc hI_step
    aig_hdr_num 32 hPnum hPch aigBytes s m hm hc hm_bytes hm_fail frameBytes
      okL pL L okLc pLc hL_step
    aig_hdr_num 32 hPnum hPch aigBytes s m hm hc hm_bytes hm_fail frameBytes
      okO pO O okOc pOc hO_step
    aig_hdr_num 10 hPnum hPch aigBytes s m hm hc hm_bytes hm_fail frameBytes
      okA pA A okAc pAc hA_step
    c0_hsplit
    · c0_hsteps; exact hm_fail s rfl rfl rfl rfl rfl rfl rfl rfl rfl m hm
    have hL0 : L = 0#32 := by simpa using hc
    clear hc
    c0_hsplit
    · c0_hsteps; exact hm_fail s rfl rfl rfl rfl rfl rfl rfl rfl rfl m hm
    have hM_le : M.toNat ≤ 0x3FFFFFF0 := by c0_bv_omega [hc]
    clear hc
    c0_hsplit
    · c0_hsteps; exact hm_fail s rfl rfl rfl rfl rfl rfl rfl rfl rfl m hm
    have hMIA : M.toNat = I.toNat + A.toNat := by c0_bv_omega [hc]
    clear hc
    let s0 : ArCtxState := { s with M := M, I := I, A := A, O := O }
    c0_hsteps_nogrp; dsimp only at hm; rw [htop0] at hm; simp only [sep_emp] at hm
    have hm0 : (arCtxMem cx s0 ⋆ (region (s0.w + BitVec.ofNat 64 776) (s0.top.toNat - 776) ⋆
        (region (s0.w + s0.top) (s0.wlen.toNat - s0.top.toNat) ⋆ (bytes b aigBytes ⋆ R)))) m := by
      dsimp only [s0]
      rw [htop0, show (776#64 : BitVec 64).toNat = 776 from rfl, Nat.sub_self, region_zero, emp_sep]
      exact sep_mono_r (fun _ => sep_swap2r) hm
    c0_hcall (ar_aalloc_seq_step Γ hAlloc (s := s0) (baseTop := 776)
      hwpos hfit (by rw [htop0]; decide) (by rw [htop0]; exact hw776) hm0)
    intro rhs0Ptr top1 _ hbase1 htop1 hstep1 _; c0_hsteps_nogrp; dsimp only at hm
    let s1 : ArCtxState := { s0 with top := top1, rhs0 := rhs0Ptr }
    c0_hcall (ar_aalloc_seq_step Γ hAlloc (s := s1) (baseTop := 776) hwpos hfit hbase1 htop1 hm)
    intro rhs1Ptr top2 _ hbase2 htop2 hstep2 _; c0_hsteps_nogrp; dsimp only at hm
    let s2 : ArCtxState := { s1 with top := top2, rhs1 := rhs1Ptr }
    c0_hcall (ar_aalloc_seq_step Γ hAlloc (s := s2) (baseTop := 776) hwpos hfit hbase2 htop2 hm)
    intro olitPtr top3 _ hbase3 htop3 hstep3 _; c0_hstraight; dsimp only at hm
    let s3 : ArCtxState := { s2 with top := top3, olit := olitPtr }
    have hm3' : (arCtxMem cx s3 ⋆ (region (s.w + BitVec.ofNat 64 776) (top3.toNat - 776) ⋆
        (region (s.w + top3) (s.wlen.toNat - top3.toNat) ⋆ (bytes b aigBytes ⋆ R)))) m := hm
    have collapse3 : (region (s.w + BitVec.ofNat 64 776) (top3.toNat - 776) ⋆
        region (s.w + top3) (s.wlen.toNat - top3.toNat)) =
        region (s.w + 776#64) (s.wlen.toNat - 776) := by
      rw [← addr_add_toNat s.w top3, show (776#64 : BitVec 64) = BitVec.ofNat 64 776 from rfl]
      exact region_merge_offset s.w hbase3 htop3 hfit
    have hfail3 : Q (false, ⟨⟩) m := by
      rw [← sep_assoc (region (s.w + BitVec.ofNat 64 776) _), collapse3,
        ← sep_assoc (arCtxMem cx s3), ← sep_assoc] at hm3'
      exact hm_fail s3 rfl rfl rfl rfl rfl rfl rfl rfl rfl m hm3'
    c0_hsplit
    · c0_hsteps; exact hfail3
    have hrhs0_ne : rhs0Ptr ≠ 0#64 := hc; clear hc
    c0_hsplit
    · c0_hsteps; exact hfail3
    have hrhs1_ne : rhs1Ptr ≠ 0#64 := hc; clear hc
    c0_hsplit
    · c0_hsteps; exact hfail3
    have holit_ne : olitPtr ≠ 0#64 := hc; clear hc
    rcases hstep1 with ⟨h0, _⟩ | ⟨_, hr0_eq, ht1_eq⟩; · exact absurd h0 hrhs0_ne
    rcases hstep2 with ⟨h0, _⟩ | ⟨_, hr1_eq, ht2_eq⟩; · exact absurd h0 hrhs1_ne
    rcases hstep3 with ⟨h0, _⟩ | ⟨_, hol_eq, ht3_eq⟩; · exact absurd h0 holit_ne
    have ha776 : align8 776 = 776 := by decide
    have ha4A : align8 (776 + 4 * A.toNat) = 776 + align8 (4 * A.toNat) :=
      align8_add_mul8 (by decide)
    have ha4A2 : align8 (776 + align8 (4 * A.toNat) + 4 * A.toNat) =
        776 + align8 (4 * A.toNat) + align8 (4 * A.toNat) :=
      align8_add_mul8 (by have := align8_mod (4 * A.toNat); omega)
    have hn4A : (4 * A.setWidth 64).toNat = 4 * A.toNat := by
      have := A.isLt
      rw [BitVec.toNat_mul, BitVec.toNat_setWidth, show (4 : BitVec 64).toNat = 4 from rfl,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hn4O : (4 * O.setWidth 64).toNat = 4 * O.toNat := by
      have := O.isLt
      rw [BitVec.toNat_mul, BitVec.toNat_setWidth, show (4 : BitVec 64).toNat = 4 from rfl,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have htop1_nat : top1.toNat = 776 + 4 * A.toNat := by
      rw [ht1_eq, htop0, show (776#64 : BitVec 64).toNat = 776 from rfl, ha776]
      exact congrArg (776 + ·) hn4A
    have htop2_nat : top2.toNat = 776 + align8 (4 * A.toNat) + 4 * A.toNat := by
      rw [ht2_eq, htop1_nat, ha4A]; exact congrArg (776 + align8 (4 * A.toNat) + ·) hn4A
    have htop3_nat : top3.toNat =
        776 + align8 (4 * A.toNat) + align8 (4 * A.toNat) + 4 * O.toNat := by
      rw [ht3_eq, htop2_nat, ha4A2]
      exact congrArg (776 + align8 (4 * A.toNat) + align8 (4 * A.toNat) + ·) hn4O
    have hr0_fin : rhs0Ptr = s.w + 776#64 := by
      rw [hr0_eq, htop0, show (776#64 : BitVec 64).toNat = 776 from rfl, ha776]
    have hr1_fin : rhs1Ptr = s.w + BitVec.ofNat 64 (776 + align8 (4 * A.toNat)) := by
      rw [hr1_eq, htop1_nat, ha4A]
    have hol_fin : olitPtr =
        s.w + BitVec.ofNat 64 (776 + align8 (4 * A.toNat) + align8 (4 * A.toNat)) := by
      rw [hol_eq, htop2_nat, ha4A2]
    have hm3'' : (region (s.w + 776#64) (top3.toNat - 776) ⋆
        region (s.w + top3) (s.wlen.toNat - top3.toNat) ⋆
        (arCtxMem cx s3 ⋆ bytes b aigBytes ⋆ R)) m := by
      have := sep_swap2r hm3'; rw [sep_assoc]
      exact sep_mono_r (fun _ h => by simpa [sep_assoc] using sep_swap2r h) this
    obtain ⟨rhs0, rhs1, olit, hr0_len, hr1_len, hol_len, hm_pop⟩ := aig_pop_alloc htop3_nat hm3''
    have hm_loop1 : (arCtxMem cx s3 ⋆ arrayPad i32 s3.rhs0 rhs0 ⋆ arrayPad i32 s3.rhs1 rhs1 ⋆
        array (t := i32) s3.olit olit ⋆ region (s.w + s3.top) (s.wlen.toNat - s3.top.toNat) ⋆
        bytes b aigBytes ⋆ R) m := by
      rw [← hr0_fin, ← hr1_fin, ← hol_fin] at hm_pop; simp only [sep_assoc] at hm_pop ⊢
      exact sep_swap2r (sep_mono_r (fun _ => sep_swap2r)
        (sep_mono_r (fun _ => sep_mono_r (fun _ => sep_swap2r))
          (sep_mono_r (fun _ => sep_mono_r (fun _ => sep_mono_r (fun _ => sep_swap2r))) hm_pop)))
    c0_hstraight
    refine c0_while_state (α := AigLoopSt) (fun st => (st.p, st.ok, st.j, ()))
      (fun st => O.toNat - st.j.toNat)
      (fun st m' => ∃ (olitCur : List (BitVec 32)) (acc : List Nat),
        st.j.toNat ≤ O.toNat ∧ olitCur.length = O.toNat ∧ acc.length = st.j.toNat ∧
        st.p.toNat ≤ aigBytes.length ∧ (arCtxMem cx s3 ⋆ arrayPad i32 s3.rhs0 rhs0 ⋆
          arrayPad i32 s3.rhs1 rhs1 ⋆ array (t := i32) s3.olit olitCur ⋆
          region (s.w + s3.top) (s.wlen.toNat - s3.top.toNat) ⋆ bytes b aigBytes ⋆ R) m' ∧
        (∀ k < st.j.toNat,
          (olitCur.getD k 0#32).toNat = acc.reverse.getD k 0 ∧ acc.reverse.getD k 0 / 2 ≤ M.toNat) ∧
        (∀ (fail : Option Aig) (k : List Nat → List Nat → Option Aig),
          poutsGo fail k O.toNat [] ((toNatBytes aigBytes).drop pAc.toNat) =
            poutsGo fail k (O.toNat - st.j.toNat) acc ((toNatBytes aigBytes).drop st.p.toNat)))
      (fun J hJ => by
        c0_hsteps
        exact hJ ⟨pAc, okAc, 0#32⟩ m ⟨olit, [], by simp, hol_len, rfl,
          by dsimp only; omega, hm_loop1, fun k hk => by simp at hk, fun fail k => rfl⟩)
      (fun J1 st1 m1 ⟨olitCur, acc1, hj1, hol_cur, hacc1, hp1_le, hm1, hinv1, houts_fn⟩ hJ1 => by
        c0_hsplit
        · have hj1_lt : st1.j.toNat < O.toNat := hc; clear hc
          have hm1_fail : Q (false, ⟨⟩) m1 := aig_fail_collapse hm_fail hm1
            rfl rfl rfl rfl rfl rfl rfl rfl rfl hfit
            (by change top3.toNat = _; rw [htop3_nat, hr0_len, hr1_len, hol_cur]) htop3 hr0_fin
            (by change rhs1Ptr = _; rw [hr1_fin, hr0_len])
            (by change olitPtr = _; rw [hol_fin, hr0_len, hr1_len])
          let frameO1 : Mem 64 → Prop := arCtxMem cx s3 ⋆ arrayPad i32 s3.rhs0 rhs0 ⋆
            arrayPad i32 s3.rhs1 rhs1 ⋆ array (t := i32) s3.olit olitCur ⋆
            region (s.w + s3.top) (s.wlen.toNat - s3.top.toNat) ⋆ R
          have hm1_bytes : (bytes b aigBytes ⋆ frameO1) m1 := by
            dsimp only [frameO1]; exact sep_cast hm1 (by ac_rfl)
          c0_hsteps_nogrp; c0_hcall hPnum
          refine ⟨aigBytes, frameO1, by omega, by omega, hm1_bytes, ?_⟩
          intro okO1 pO1 vO1 hvO1; c0_hsplit; rotate_left
          · c0_hsteps; exact hm1_fail
          obtain ⟨_, _, _, hvO1_fn⟩ := hvO1 hc; clear hc
          c0_hsteps_nogrp; c0_hcall hPch
          refine ⟨aigBytes, frameO1, by omega, by omega, hm1_bytes, ?_⟩
          intro okOc1 pOc1 ⟨hOc1a, hOc1b⟩; c0_hsplit; rotate_left
          · c0_hsteps; exact hm1_fail
          obtain ⟨hpO1_lt, hOc1_eq, _, hpOc1_nat, _⟩ :=
            pch_ok_extract (by rw [hc] at hOc1a hOc1b; exact ⟨hOc1a, hOc1b⟩)
          clear hc; c0_hsplit
          · c0_hsteps; exact hm1_fail
          have hvO1_le : vO1.toNat ≤ 2 * M.toNat + 1 := by
            have := M.isLt
            rw [show BitVec.toNat 2 = 2 from rfl, show BitVec.toNat 1 = 1 from rfl,
              Nat.mod_eq_of_lt (by omega : 2 * M.toNat + 1 < 2 ^ 32)] at hc
            omega
          clear hc; c0_hsteps
          have hj1'_eq : (st1.j + 1#32).toNat = st1.j.toNat + 1 := bv32_add1_toNat hj1_lt
          refine hJ1 ⟨pOc1, okOc1, st1.j + 1#32⟩ m
            (by dsimp only; rw [hj1'_eq]; exact Nat.sub_lt_sub_left hj1_lt (Nat.lt_succ_self _))
            ⟨olitCur.set st1.j.toNat vO1, vO1.toNat :: acc1,
             by dsimp only; rw [hj1'_eq]; exact hj1_lt,
             by simp [hol_cur], by simp [hj1'_eq, hacc1], by dsimp only; omega,
             sep_cast hm (by ac_rfl), fun k hk => ?_, fun fail k => ?_⟩
          · dsimp only at hk; rw [hj1'_eq] at hk
            rw [getD_set_nat 0#32 olitCur st1.j.toNat vO1 (by omega),
              getD_reverse_append 0 acc1 vO1.toNat k, hacc1]
            by_cases hlt : k < st1.j.toNat
            · have hne : k ≠ st1.j.toNat := by omega
              simp only [hlt, hne, ↓reduceIte]; exact hinv1 k hlt
            · have heq : k = st1.j.toNat := by omega
              simp only [heq, Nat.lt_irrefl, ↓reduceIte, true_and]; omega
          · dsimp only
            rw [hj1'_eq, houts_fn fail k, nat_sub_succ_eq hj1_lt, poutsGo_succ, hpOc1_nat]
            exact hvO1_fn 10 fail _ hpO1_lt hOc1_eq
        · have hj1_eq : st1.j.toNat = O.toNat := by omega
          clear hc
          have houts_done : ∀ (fail : Option Aig) (k : List Nat → List Nat → Option Aig),
              poutsGo fail k O.toNat [] ((toNatBytes aigBytes).drop pAc.toNat) =
                k acc1.reverse ((toNatBytes aigBytes).drop st1.p.toNat) := fun fail k => by
            rw [houts_fn fail k, hj1_eq, Nat.sub_self]; rfl
          have hm1_unfold : (arCtxMem cx s3 ⋆ array (t := i32) s3.rhs0 rhs0 ⋆
              region (s3.rhs0 + BitVec.ofNat 64 (4 * rhs0.length))
                (align8 (4 * rhs0.length) - 4 * rhs0.length) ⋆
              array (t := i32) s3.rhs1 rhs1 ⋆
              region (s3.rhs1 + BitVec.ofNat 64 (4 * rhs1.length))
                (align8 (4 * rhs1.length) - 4 * rhs1.length) ⋆
              array (t := i32) s3.olit olitCur ⋆
              region (s.w + s3.top) (s.wlen.toNat - s3.top.toNat) ⋆ bytes b aigBytes ⋆ R) m1 := by
            rw [arrayPad_u32_eq s3.rhs0 rhs0, arrayPad_u32_eq s3.rhs1 rhs1] at hm1
            exact sep_cast hm1 (by ac_rfl)
          refine c0_while_state (α := AigLoopSt) (fun st => (st.p, st.ok, st.j, ()))
            (fun st => A.toNat - st.j.toNat)
            (fun st m' => ∃ (r0Cur r1Cur : List (BitVec 32)) (acc2 : List (Nat × Nat)),
              st.j.toNat ≤ A.toNat ∧ r0Cur.length = A.toNat ∧ r1Cur.length = A.toNat ∧
              acc2.length = st.j.toNat ∧ st.p.toNat ≤ aigBytes.length ∧
              (arCtxMem cx s3 ⋆ array (t := i32) s3.rhs0 r0Cur ⋆
                region (s3.rhs0 + BitVec.ofNat 64 (4 * r0Cur.length))
                  (align8 (4 * r0Cur.length) - 4 * r0Cur.length) ⋆
                array (t := i32) s3.rhs1 r1Cur ⋆
                region (s3.rhs1 + BitVec.ofNat 64 (4 * r1Cur.length))
                  (align8 (4 * r1Cur.length) - 4 * r1Cur.length) ⋆
                array (t := i32) s3.olit olitCur ⋆
                region (s.w + s3.top) (s.wlen.toNat - s3.top.toNat) ⋆
                bytes b aigBytes ⋆ R) m' ∧
              (∀ k < st.j.toNat, (r0Cur.getD k 0#32).toNat = (acc2.reverse.getD k (0, 0)).1 ∧
                (r1Cur.getD k 0#32).toNat = (acc2.reverse.getD k (0, 0)).2 ∧
                (acc2.reverse.getD k (0, 0)).1 / 2 < I.toNat + 1 + k ∧
                (acc2.reverse.getD k (0, 0)).2 / 2 < I.toNat + 1 + k) ∧
              (∀ (fail : Option Aig) (k : List (Nat × Nat) → Option Aig),
                pandsGo fail k A.toNat (2 * (I.toNat + 1)) []
                    ((toNatBytes aigBytes).drop st1.p.toNat) =
                  pandsGo fail k (A.toNat - st.j.toNat) (2 * (I.toNat + 1 + st.j.toNat))
                    acc2 ((toNatBytes aigBytes).drop st.p.toNat)))
            (fun J2 hJ2 => by
              c0_hsteps
              exact hJ2 ⟨st1.p, st1.ok, 0#32⟩ m1 ⟨rhs0, rhs1, [], by simp, hr0_len,
                hr1_len, rfl, hp1_le, hm1_unfold, fun k hk => by simp at hk, fun fail k => rfl⟩)
            (fun J2 st2 m2 ⟨r0Cur, r1Cur, acc2, hj2, hr0c, hr1c, hacc2, hp2_le, hm2,
                hinv2, hands_fn⟩ hJ2 => by
              have hm2_fold : ∀ m', (arCtxMem cx s3 ⋆ array (t := i32) s3.rhs0 r0Cur ⋆
                  region (s3.rhs0 + BitVec.ofNat 64 (4 * r0Cur.length))
                    (align8 (4 * r0Cur.length) - 4 * r0Cur.length) ⋆
                  array (t := i32) s3.rhs1 r1Cur ⋆
                  region (s3.rhs1 + BitVec.ofNat 64 (4 * r1Cur.length))
                    (align8 (4 * r1Cur.length) - 4 * r1Cur.length) ⋆
                  array (t := i32) s3.olit olitCur ⋆
                  region (s.w + s3.top) (s.wlen.toNat - s3.top.toNat) ⋆
                  bytes b aigBytes ⋆ R) m' →
                  (arCtxMem cx s3 ⋆ arrayPad i32 s3.rhs0 r0Cur ⋆ arrayPad i32 s3.rhs1 r1Cur ⋆
                    array (t := i32) s3.olit olitCur ⋆
                    region (s.w + s3.top) (s.wlen.toNat - s3.top.toNat) ⋆
                    bytes b aigBytes ⋆ R) m' := fun m' h => by
                rw [arrayPad_u32_eq s3.rhs0 r0Cur, arrayPad_u32_eq s3.rhs1 r1Cur]
                exact sep_cast h (by ac_rfl)
              c0_hsplit
              · have hj2_lt : st2.j.toNat < A.toNat := hc; clear hc
                have hm2_fail : Q (false, ⟨⟩) m2 := aig_fail_collapse hm_fail (hm2_fold m2 hm2)
                  rfl rfl rfl rfl rfl rfl rfl rfl rfl hfit
                  (by change top3.toNat = _; rw [htop3_nat, hr0c, hr1c, hol_cur]) htop3 hr0_fin
                  (by change rhs1Ptr = _; rw [hr1_fin, hr0c])
                  (by change olitPtr = _; rw [hol_fin, hr0c, hr1c])
                let frameA2 : Mem 64 → Prop := arCtxMem cx s3 ⋆ array (t := i32) s3.rhs0 r0Cur ⋆
                  region (s3.rhs0 + BitVec.ofNat 64 (4 * r0Cur.length))
                    (align8 (4 * r0Cur.length) - 4 * r0Cur.length) ⋆
                  array (t := i32) s3.rhs1 r1Cur ⋆
                  region (s3.rhs1 + BitVec.ofNat 64 (4 * r1Cur.length))
                    (align8 (4 * r1Cur.length) - 4 * r1Cur.length) ⋆
                  array (t := i32) s3.olit olitCur ⋆
                  region (s.w + s3.top) (s.wlen.toNat - s3.top.toNat) ⋆ R
                have hm2_bytes : (bytes b aigBytes ⋆ frameA2) m2 := by
                  dsimp only [frameA2]; exact sep_cast hm2 (by ac_rfl)
                c0_hsteps_nogrp; c0_hcall hPvar
                refine ⟨aigBytes, frameA2, by omega, by omega, hm2_bytes, ?_⟩
                intro okD0 pD0 d0 hd0; c0_hsplit; rotate_left
                · c0_hsteps; exact hm2_fail
                obtain ⟨_, hpD0_le, hd0_fn⟩ := hd0 hc; clear hc
                c0_hsteps_nogrp; c0_hcall hPvar
                refine ⟨aigBytes, frameA2, by omega, by omega, hm2_bytes, ?_⟩
                intro okD1 pD1 d1 hd1; c0_hsplit; rotate_left
                · c0_hsteps; exact hm2_fail
                obtain ⟨_, hpD1_le, hd1_fn⟩ := hd1 hc; clear hc
                c0_hsplit
                · c0_hsteps; exact hm2_fail
                have hd0_pos : 0 < d0.toNat := bv32_ne_zero_pos hc; clear hc
                let lhs := 2#32 * (I + 1#32 + st2.j)
                have hlhs_nat : lhs.toNat = 2 * (I.toNat + 1 + st2.j.toNat) :=
                  bv32_aig_lhs hMIA hM_le hj2_lt
                c0_hsplit
                · c0_hsteps; exact hm2_fail
                have hd0_le : d0.toNat ≤ lhs.toNat := by
                  rw [hlhs_nat]; exact bv32_aig_d0_le hMIA hM_le hj2_lt hc
                clear hc; let r0 := lhs - d0
                have hr0_nat : r0.toNat = lhs.toNat - d0.toNat := bv32_sub_toNat hd0_le
                c0_hsplit
                · c0_hsteps; exact hm2_fail
                have hd1_le : d1.toNat ≤ r0.toNat := by
                  rw [hr0_nat, hlhs_nat]
                  exact bv32_aig_r0_le hMIA hM_le hj2_lt (by rw [← hlhs_nat]; exact hd0_le) hc
                clear hc; let r1 := r0 - d1
                have hr1_nat : r1.toNat = r0.toNat - d1.toNat := bv32_sub_toNat hd1_le
                c0_hsteps
                have hj2'_eq : (st2.j + 1#32).toNat = st2.j.toNat + 1 := bv32_add1_toNat hj2_lt
                have hset : (BitVec.setWidth 64 st2.j).toNat = st2.j.toNat := by
                  rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := st2.j.isLt; omega)
                have hm2' : (arCtxMem cx s3 ⋆ array (t := i32) s3.rhs0 (r0Cur.set st2.j.toNat r0) ⋆
                    region (s3.rhs0 + BitVec.ofNat 64 (4 * (r0Cur.set st2.j.toNat r0).length))
                      (align8 (4 * (r0Cur.set st2.j.toNat r0).length) -
                        4 * (r0Cur.set st2.j.toNat r0).length) ⋆
                    array (t := i32) s3.rhs1 (r1Cur.set st2.j.toNat r1) ⋆
                    region (s3.rhs1 + BitVec.ofNat 64 (4 * (r1Cur.set st2.j.toNat r1).length))
                      (align8 (4 * (r1Cur.set st2.j.toNat r1).length) -
                        4 * (r1Cur.set st2.j.toNat r1).length) ⋆
                    array (t := i32) s3.olit olitCur ⋆
                    region (s.w + s3.top) (s.wlen.toNat - s3.top.toNat) ⋆
                    bytes b aigBytes ⋆ R) m := by
                  dsimp only [r0, r1, lhs]; simp only [sep_emp, List.length_set] at hm ⊢
                  rw [hset] at hm; exact sep_cast hm (by ac_rfl)
                refine hJ2 ⟨pD1, okD1, st2.j + 1#32⟩ m
                  (by
                    dsimp only; rw [hj2'_eq]
                    exact Nat.sub_lt_sub_left hj2_lt (Nat.lt_succ_self _))
                  ⟨r0Cur.set st2.j.toNat r0, r1Cur.set st2.j.toNat r1,
                    (r0.toNat, r1.toNat) :: acc2, by dsimp only; rw [hj2'_eq]; exact hj2_lt,
                    by simp [hr0c], by simp [hr1c], by simp [hj2'_eq, hacc2],
                    Nat.le_trans hpD1_le (hn ▸ Nat.le_refl _), hm2',
                    fun k hk => ?_, fun fail k => ?_⟩
                · dsimp only at hk; rw [hj2'_eq] at hk
                  rw [getD_set_nat 0#32 r0Cur st2.j.toNat r0 (by omega),
                    getD_set_nat 0#32 r1Cur st2.j.toNat r1 (by omega),
                    getD_reverse_append (0, 0) acc2 (r0.toNat, r1.toNat) k, hacc2]
                  by_cases hlt : k < st2.j.toNat
                  · have hne : k ≠ st2.j.toNat := by omega
                    simp only [hlt, hne, ↓reduceIte]; exact hinv2 k hlt
                  · have heq : k = st2.j.toNat := by omega
                    simp only [heq, Nat.lt_irrefl, ↓reduceIte, true_and]; constructor <;> omega
                · dsimp only
                  rw [hj2'_eq, hands_fn fail k, nat_sub_succ_eq hj2_lt, pandsGo_succ,
                    hd0_fn fail, hd1_fn fail]
                  have hbeq0 : Nat.ble d0.toNat lhs.toNat = true := Nat.ble_eq.mpr hd0_le
                  have hne0 : Nat.beq d0.toNat 0 = false := by
                    cases hb : Nat.beq d0.toNat 0
                    · rfl
                    · exact absurd hd0_pos (by rw [Nat.beq_eq.mp hb]; decide)
                  have hble1 : Nat.ble d1.toNat (lhs.toNat - d0.toNat) = true :=
                    Nat.ble_eq.mpr (by rw [← hr0_nat]; exact hd1_le)
                  rw [← hlhs_nat, hne0, hbeq0, hble1, ← hr0_nat, ← hr1_nat, hlhs_nat,
                    nat_aig_lhs_next]
              · have hj2_eq : st2.j.toNat = A.toNat := Nat.le_antisymm hj2 (Nat.le_of_not_lt hc)
                clear hc; c0_hsteps
                let g : Aig := ⟨M.toNat, I.toNat, acc1.reverse, acc2.reverse⟩
                have hg_ands : g.ands.length = A.toNat := by dsimp only [g]; simp [hacc2, hj2_eq]
                have hg_outs : g.outs.length = O.toNat := by dsimp only [g]; simp [hacc1, hj1_eq]
                have hparse : parseAig (toNatBytes aigBytes) = some g := by
                  rw [parseAig_header aigBytes M.toNat I.toNat O.toNat A.toNat pAc.toNat
                    (hn ▸ hn4) hb0 hb1 hb2 hb3 ?_ hMIA]
                  · rw [houts_done, show Nat.mul 2 (Nat.add I.toNat 1) = 2 * (I.toNat + 1) from rfl,
                      hands_fn none (fun ands => some ⟨M.toNat, I.toNat, acc1.reverse, ands⟩),
                      hj2_eq, Nat.sub_self]; rfl
                  · intro fail k
                    rw [hM_step fail, hI_step fail, hL_step fail, hO_step fail, hA_step fail, hL0]
                    rfl
                have hrep : AigRep g r0Cur r1Cur olitCur :=
                  ⟨by dsimp only [g]; rw [hMIA]; exact Nat.le_add_right _ _,
                   by dsimp only [g]; rw [hg_ands, hMIA], by rw [hg_ands]; exact hr0c,
                   by rw [hg_ands]; exact hr1c, by rw [hg_outs]; exact hol_cur,
                   fun j hj => (hinv2 j (by rw [hj2_eq, ← hg_ands]; exact hj)).1,
                   fun j hj => (hinv2 j (by rw [hj2_eq, ← hg_ands]; exact hj)).2.1,
                   fun j hj => (hinv1 j (by rw [hj1_eq, ← hg_outs]; exact hj)).1,
                   fun j hj => (hinv2 j (by rw [hj2_eq, ← hg_ands]; exact hj)).2.2,
                   fun j hj => (hinv1 j (by rw [hj1_eq, ← hg_outs]; exact hj)).2⟩
                refine hQ true m2 (Or.inr ⟨rfl, g, r0Cur, r1Cur, olitCur, s3, hparse, hrep, hM_le,
                  rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                  rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hg_ands.symm, hg_outs.symm,
                  hr0_fin, ?_, ?_, ?_, htop3, sep_cast (hm2_fold m2 hm2) (by ac_rfl)⟩)
                · change rhs1Ptr = _; rw [hr1_fin, hg_ands]
                · change olitPtr = _; rw [hol_fin, hg_ands]
                · change top3.toNat = _; rw [htop3_nat, hg_ands, hg_outs]))

end

end LeanQbe.T.Examples.Arisca.Proof
