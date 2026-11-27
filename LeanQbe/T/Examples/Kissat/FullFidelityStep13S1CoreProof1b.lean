/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1CoreProof1a
import LeanQbe.T.Examples.Kissat.FullFidelityBveTactics
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard S1-C Proofs — Part 1b (`full_k6_core_fid` Incremental & Entry)

Certifies `FullFidelityBve.fidK6CoreSpec` for Step-13 `full_k6_core_fid` (`s13_fid_inc_wp` +
`full_k6_core_fid_s13_wp`), decomposed into `<= 420`-line theorems (`public section`, `0`
`@[expose]` on theorems/lemmas, `0` `import all`, `<= 100` cols, `< 1,400` LOC).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S1

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.FullFidelityBve
open Kraken.Bedrock2.Test

open scoped M8K6bTactics FidK6Tactics

attribute [local bv_c0] List.length_set

local macro_rules
  | `(tactic| c0_bound) => `(tactic| first | assumption | rfl | decide | omega | fid_omega)

section S13CoreFidMain

private def fSDropToGrp0 : Nat → Expr Val Cont [] → Expr Val Cont []
  | 0, e => e
  | n + 1, .let_ (ts := ts) _ k => fSDropToGrp0 n (k (fidDfltT ts))
  | n + 1, .load (.bits 32) _ k => fSDropToGrp0 n (k 0#32)
  | n + 1, .store _ _ k => fSDropToGrp0 n k
  | _, e => e

private def s13FidIncTrailE (h scrPtr : BitVec 64) (mv nc nv acap inc : BitVec 32)
    (J2 : Cont [.bits 32]) : Expr Val Cont [] :=
  match s13FidIncE h scrPtr mv nc nv acap inc J2 with
  | .group (sig := [[.bits 32]]) bs _ =>
      match bs ((fun _ _ => True), ()) with
      | .cons b _ =>
        match fSDropToGrp0 22 (fSJF (fSLet (b (0#32, ())))) with
        | .group (sig := [[]]) bs _ =>
            match bs ((fun _ _ => True), ()) with | .cons bt _ => bt ()
        | _ => .hlt
  | _ => .hlt

private def s13FidIncClauseE (scrPtr : BitVec 64) (mv nv acap v roff rsz : BitVec 32)
    (Jc : Cont []) : Expr Val Cont [] :=
  let o_arena : BitVec 32 := 4224#32 + 45#32 * mv
  let o_flags : BitVec 32 := 4224#32 + 6#32 * mv
  Expr.let_ (Op.mk (.add i32) (Arg.var roff, Arg.var rsz, ())) (fun (sum, ()) =>
  Expr.let_ (Op.mk (.cmp .ule i32 .bool rfl) (Arg.var sum, Arg.var acap, ())) (fun (bc, ()) =>
  Expr.jnz (Arg.var bc)
    (Expr.group (sig := [[i32]]) (fun Lj => Blocks.cons (fun (j, ()) =>
      Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var j, Arg.var rsz, ())) (fun (bj, ()) =>
      Expr.jnz (Arg.var bj)
        (Expr.let_ (Op.mk (.add i32) (Arg.var o_arena, Arg.var roff, ())) (fun (p1, ()) =>
        Expr.let_ (Op.mk (.add i32) (Arg.var p1, Arg.var j, ())) (fun (p2, ()) =>
        Expr.let_ (Op.mk (.zext 32 64) (Arg.var p2, ())) (fun (p64, ()) =>
        Expr.let_ (Op.mk (.mul i64) (Arg.var p64, Arg.imm 4, ())) (fun (po, ()) =>
        Expr.let_ (Op.mk (.add i64) (Arg.var scrPtr, Arg.var po, ())) (fun (pa, ()) =>
        Expr.load i32 (Arg.var pa) (fun raw =>
        Expr.let_ (Op.mk (.lshr i32) (Arg.var raw, Arg.imm 1, ())) (fun (lv, ()) =>
        Expr.group (sig := [[]]) (fun _Js => Blocks.cons (fun _ =>
          Expr.let_ (Op.mk (.add i32) (Arg.var j, Arg.imm 1, ())) (fun (j1, ()) =>
          Expr.jump Lj.fst (Arg.var j1, ()))) Blocks.nil) (fun Js =>
        Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var lv, Arg.var nv, ())) (fun (blv, ()) =>
        Expr.jnz (Arg.var blv)
          (Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl) (Arg.var lv, Arg.var v, ())) (fun (bne, ()) =>
          Expr.jnz (Arg.var bne)
            (Expr.let_ (Op.mk (.add i32) (Arg.var o_flags, Arg.var lv, ())) (fun (pf1, ()) =>
            Expr.let_ (Op.mk (.zext 32 64) (Arg.var pf1, ())) (fun (pf64, ()) =>
            Expr.let_ (Op.mk (.mul i64) (Arg.var pf64, Arg.imm 4, ())) (fun (pfo, ()) =>
            Expr.let_ (Op.mk (.add i64) (Arg.var scrPtr, Arg.var pfo, ())) (fun (pfa, ()) =>
            Expr.let_ (Op.mk (.add i32) (Arg.var o_flags, Arg.var lv, ())) (fun (qf1, ()) =>
            Expr.let_ (Op.mk (.zext 32 64) (Arg.var qf1, ())) (fun (qf64, ()) =>
            Expr.let_ (Op.mk (.mul i64) (Arg.var qf64, Arg.imm 4, ())) (fun (qfo, ()) =>
            Expr.let_ (Op.mk (.add i64) (Arg.var scrPtr, Arg.var qfo, ())) (fun (qfa, ()) =>
            Expr.load i32 (Arg.var qfa) (fun flv =>
            Expr.let_ (Op.mk (.or i32) (Arg.var flv, Arg.imm 2, ())) (fun (flv2, ()) =>
            Expr.store (Arg.var flv2) (Arg.var pfa) (Expr.jump Js.fst ()))))))))))))
            (Expr.jump Js.fst ())))
          (Expr.jump Js.fst ())))))))))))
        (Expr.jump Jc ()))) Blocks.nil) (fun Lj => Expr.jump Lj.fst (Arg.imm 0, ())))
    (Expr.jump Jc ())))

private theorem s13_fid_inc_clause_wp {Γ : Env} {c : FullCfg} {s : FullState}
    {scr0 : List (BitVec 32)} {mv nc nv acap v roff rsz : BitVec 32} {R : Mem 64 → Prop}
    {Q : Post []} {X : XPost} {Jc : Cont []}
    (h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv)
    (hmv_lo : 256 ≤ mv.toNat) (hmv_hi : mv.toNat ≤ 8192)
    (_h4207 : 4207 < scr0.length) (_hac_eq : scr0[4207]?.getD 0#32 = acap)
    (hnv_le : nv.toNat ≤ mv.toNat) (hbge : 4224 + 45 * mv.toNat ≤ scr0.length)
    (hlen_scr : 4224 + 45 * mv.toNat + acap.toNat ≤ scr0.length) (_hcap_lt : scr0.length < 2 ^ 30)
    (hJc : ∀ m' : Mem 64, (∃ scrj : List (BitVec 32),
      FidCoreInv scr0 mv nc scrj ∧ (FullMem c (m8ScrSt s scrj) ⋆ R) m') → Jc () m')
    {scrt2 : List (BitVec 32)} {mb : Mem 64}
    (hikt2 : FidCoreInv scr0 mv nc scrt2)
    (hroff_rsz : roff.toNat + rsz.toNat ≤ acap.toNat)
    (hrsz_le : rsz.toNat ≤ 65535)
    (hm : (FullMem c (m8ScrSt s scrt2) ⋆ R) mb) :
    wp Γ Q X (s13FidIncClauseE c.pScratchBuf mv nv acap v roff rsz Jc) mb := by
  let invS : Mem 64 → Prop := fun mj =>
    ∃ scrj : List (BitVec 32), FidCoreInv scr0 mv nc scrj ∧ (FullMem c (m8ScrSt s scrj) ⋆ R) mj
  unfold s13FidIncClauseE; dsimp only
  c0_hsteps_nogrp
  c0_hsplit
  · clear hc; c0_hsteps_nogrp
    refine wp_loop_group (ts := [i32])
      (fun rem_j (j, ()) mj => ∃ scrj : List (BitVec 32),
        FidCoreInv scr0 mv nc scrj ∧ j.toNat ≤ rsz.toNat ∧
        rem_j = rsz.toNat - j.toNat ∧ (FullMem c (m8ScrSt s scrj) ⋆ R) mj) ?_ ?_
    · rintro Lj rem_j ⟨j, ⟨⟩⟩ mj hLj ⟨scrj, hikj, hj_le, rfl, hmj⟩
      have hlj : scrj.length = scr0.length := hikj.2.1
      c0_hsplit
      · have hj_lt : j.toNat < rsz.toNat := hc
        clear hc
        have hj1 : (j + 1#32).toNat = j.toNat + 1 := m8_bv32_add1_toNat hj_lt (by omega)
        have har_e := fid_k6_off_add2 (mv := mv) (k := 45) (x := roff) (y := j)
          hmv_hi (by decide) (by omega)
        have har_lt : ((4224 + 45 * mv + roff + j).setWidth 64).toNat < scrj.length := by
          rw [hlj, har_e]; omega
        let lv := (scrj[((4224 + 45 * mv + roff + j).setWidth 64).toNat]'har_lt) >>> (1 : Nat)
        c0_hsteps_nogrp
        refine wp_join0 invS
          (fun _ mj' ⟨scrj', hikj', hmj'⟩ => by
            c0_hsteps_nogrp
            exact hLj (rsz.toNat - (j + 1#32).toNat) (j + 1#32, ()) mj'
              (by omega) ⟨scrj', hikj', by omega, rfl, hmj'⟩)
          (fun Js hJs => by
            c0_hsplit
            · have hlv_lt : lv.toNat < nv.toNat := by
                have hc' := hc; clear hc
                have har_lt' : 4224 + 45 * mv.toNat + roff.toNat + j.toNat < 4294967296 := by omega
                have har_u : (4224 + 45 * mv.toNat + roff.toNat + j.toNat) % 4294967296 =
                    ((4224 + 45 * mv + roff + j).setWidth 64).toNat := by
                  rw [har_e, Nat.mod_eq_of_lt har_lt']
                simp only [show (45 % 2 ^ 32 : Nat) = 45 from rfl, har_u,
                  ← m8_bv32_lshr1_toNat] at hc'
                exact hc'
              c0_hsplit
              · have hfl_lv := fid_k6_off_add (mv := mv) (k := 6) (x := lv)
                  hmv_hi (by decide) (by omega)
                have hfl_lvb : ((4224 + 6 * mv + lv).setWidth 64).toNat < scrj.length := by
                  rw [hlj, hfl_lv]; omega
                c0_hsteps_nogrp
                refine hJs _ ⟨_, fidCoreInv_set_flags_e h4214 hmv_eq hikj (by omega) hfl_lv
                  ((scrj[((4224 + 6 * mv + lv).setWidth 64).toNat]'hfl_lvb) ||| 2#32), ?_⟩
                simpa only [List.length_set, show (4224#32 : BitVec 32) = 4224 from rfl,
                  show (6#32 : BitVec 32) = 6 from rfl, show (45#32 : BitVec 32) = 45 from rfl,
                  show (2 : BitVec 32) = 2#32 from rfl] using hm
              · c0_hsteps_nogrp; exact hJs _ ⟨scrj, hikj, hmj⟩
            · c0_hsteps_nogrp; exact hJs _ ⟨scrj, hikj, hmj⟩)
      · c0_hsteps_nogrp; exact hJc mj ⟨scrj, hikj, hmj⟩
    · intro Lj hLj; c0_hsteps_nogrp; exact hLj rsz.toNat (0#32, ()) mb
        ⟨scrt2, hikt2, Nat.zero_le _, by simp, hm⟩

private theorem s13_fid_inc_trail_wp {Γ : Env} {c : FullCfg} {s : FullState}
    {scr0 : List (BitVec 32)} {mv nc nv acap inc : BitVec 32} {R : Mem 64 → Prop}
    {Q : Post []} {X : XPost} {J2 : Cont [.bits 32]}
    (h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv)
    (hmv_lo : 256 ≤ mv.toNat) (hmv_hi : mv.toNat ≤ 8192)
    (h4192 : 4192 < scr0.length) (_hnv_d : scr0[4192]'h4192 = nv)
    (h4193 : 4193 < scr0.length) (hnc_d : scr0[4193]'h4193 = nc)
    (hnc_le : nc.toNat ≤ 4 * mv.toNat)
    (h4207 : 4207 < scr0.length) (hac_eq : scr0[4207]?.getD 0#32 = acap)
    (hnv_le : nv.toNat ≤ mv.toNat) (hbge : 4224 + 45 * mv.toNat ≤ scr0.length)
    (hlen_scr : 4224 + 45 * mv.toNat + acap.toNat ≤ scr0.length) (hcap_lt : scr0.length < 2 ^ 30)
    (hJ2 : ∀ x : Val i32, ∀ m2, (∃ scr2 : List (BitVec 32),
      FidCoreInv scr0 mv nc scr2 ∧ (FullMem c (m8ScrSt s scr2) ⋆ R) m2) → J2 (x, ()) m2)
    {scrm : List (BitVec 32)} {mb : Mem 64}
    (hikm : FidCoreInv scr0 mv nc scrm) (hmb : (FullMem c (m8ScrSt s scrm) ⋆ R) mb) :
    wp Γ Q X (s13FidIncTrailE c.hdr c.pScratchBuf mv nc nv acap inc J2) mb := by
  let invS : Mem 64 → Prop := fun mj =>
    ∃ scrj : List (BitVec 32), FidCoreInv scr0 mv nc scrj ∧ (FullMem c (m8ScrSt s scrj) ⋆ R) mj
  have hlm : scrm.length = scr0.length := hikm.2.1
  dsimp only [s13FidIncTrailE, s13FidIncE, s13FidPhase2E, full_k6_core_fid_body,
    fSDropToGrp0, fSLet, fSLet32, fSLd, fSLd64, fSJF, fSJT, fSGrp1, fidDfltT, fidDflt]
  c0_hsteps_nogrp
  refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun ti => (ti, ()))
    (fun ti => ti.toNat ≤ mv.toNat)
    (fun _ ti0 hti0 => by
      c0_hsteps_nogrp
      refine wp_loop_group (ts := [i32])
        (fun rem_t (ti, ()) mt => ∃ scrt : List (BitVec 32), FidCoreInv scr0 mv nc scrt ∧
          ti.toNat ≤ mv.toNat ∧ rem_t = ti.toNat ∧ (FullMem c (m8ScrSt s scrt) ⋆ R) mt)
        ?_ (fun Lt hLt => by
          c0_hsteps_nogrp; exact hLt ti0.toNat (ti0, ()) mb ⟨scrm, hikm, hti0, rfl, hmb⟩)
      rintro Lt rem_t ⟨ti, ⟨⟩⟩ mt hLt ⟨scrt, hikt, hti_le, rfl, hmt⟩
      have hlt : scrt.length = scr0.length := hikt.2.1
      c0_hsplit
      · have hti_pos : 0 < ti.toNat := hc
        clear hc
        have hti1 : (ti - 1#32).toNat = ti.toNat - 1 := m8_bv32_sub1_toNat hti_pos
        let ti' := ti - 1#32
        have htr_e := fid_k6_off_add (mv := mv) (k := 5) (x := ti') hmv_hi (by decide)
          (by dsimp only [ti']; rw [hti1]; omega)
        have htr_b : ((4224 + 5 * mv + ti').setWidth 64).toNat < scrt.length := by
          rw [hlt, htr_e]; dsimp only [ti']; rw [hti1]; omega
        let v := (scrt[((4224 + 5 * mv + ti').setWidth 64).toNat]'htr_b) >>> (1 : Nat)
        c0_hsplit
        · c0_hsteps_nogrp; exact hLt ti'.toNat (ti', ()) mt
            (by dsimp only [ti']; rw [hti1]; omega)
            ⟨scrt, hikt, by dsimp only [ti']; rw [hti1]; omega, rfl, hmt⟩
        · have hv_lt : v.toNat < nv.toNat := by
            have hc' := hc; fid_norm_ofnat
            simp (disch := fid_omega) only [bv_c0, Nat.reducePow, Nat.reduceMod,
              BitVec.reduceToNat] at hc'
            have hti_bnd : 4224 + 5 * mv.toNat + (ti.toNat - 1) < 4294967296 := by
              dsimp only [ti'] at htr_e; rw [hti1] at htr_e; omega
            have hadd : (4224 + 5 * mv.toNat + (4294967296 - 1 + ti.toNat)) %
                4294967296 = ((4224 + 5 * mv + ti').setWidth 64).toNat := by
              rw [htr_e]; dsimp only [ti']; rw [hti1]
              exact s13f_sub1_mod32 _ _ hti_pos hti_bnd
            rw [m8_k6_get_congr hadd _ htr_b, ← m8_bv32_lshr1_toNat] at hc'
            exact Nat.lt_of_not_le hc'
          clear hc
          have hfl_e := fid_k6_off_add (mv := mv) (k := 6) (x := v) hmv_hi (by decide)
            (by omega)
          have hfl_b : ((4224 + 6 * mv + v).setWidth 64).toNat < scrt.length := by
            rw [hlt, hfl_e]; exact fidCore_mv_lt 6 (by omega) hmv_lo hbge
          have hfl_b' :
              ((4224 + 6 * mv + (scrt[((4224 + 5 * mv +
                (ti - 1#32)).setWidth 64).toNat]'htr_b >>> (1 : Nat))).setWidth 64).toNat <
                scrt.length := hfl_b
          c0_hsplit
          · c0_hsteps_nogrp; exact hLt ti'.toNat (ti', ()) mt
              (by dsimp only [ti']; rw [hti1]; omega)
              ⟨scrt, hikt, by dsimp only [ti']; rw [hti1]; omega, rfl, hmt⟩
          · clear hc
            have hrs_e := fid_k6_off_add1 (mv := mv) (x := v) hmv_hi (by omega)
            let scrt1 := scrt.set ((4224 + 6 * mv + v).setWidth 64).toNat
              ((scrt[((4224 + 6 * mv + v).setWidth 64).toNat]'hfl_b) &&& ~~~2#32)
            have hikt1 := fidCoreInv_set_flags_e h4214 hmv_eq hikt (by omega) hfl_e
              ((scrt[((4224 + 6 * mv + v).setWidth 64).toNat]'hfl_b) &&& ~~~2#32)
            have hlt1 : scrt1.length = scr0.length := hikt1.2.1
            have hrs_b : ((4224 + mv + v).setWidth 64).toNat < scrt1.length := by
              rw [hlt1, hrs_e]; exact fidCore_1_lt (by omega) hmv_lo hbge
            have hrs_b' :
                ((4224 + mv + (scrt[((4224 + 5 * mv +
                  (ti - 1#32)).setWidth 64).toNat]'htr_b >>> (1 : Nat))).setWidth 64).toNat <
                  scrt1.length := hrs_b
            c0_hsteps_nogrp; c0_hsplit
            · c0_hsteps_nogrp; exact hLt ti'.toNat (ti', ()) _
                (by dsimp only [ti']; rw [hti1]; omega)
                ⟨scrt1, hikt1, by dsimp only [ti']; rw [hti1]; omega, rfl, hm⟩
            · let rsn := scrt1[((4224 + mv + v).setWidth 64).toNat]'hrs_b
              have hti_bnd : 4224 + 5 * mv.toNat + (ti.toNat - 1) < 4294967296 := by
                dsimp only [ti'] at htr_e; rw [hti1] at htr_e; omega
              have hadd : (4224 + 5 * mv.toNat + (4294967296 - 1 + ti.toNat)) % 4294967296 =
                  ((4224 + 5 * mv + ti').setWidth 64).toNat := by
                rw [htr_e]; dsimp only [ti']; rw [hti1]; exact s13f_sub1_mod32 _ _ hti_pos hti_bnd
              have hrs_k : ((4224 + mv + v).setWidth 64).toNat < scrt.length := by
                rw [hlt, hrs_e]; exact fidCore_1_lt (by omega) hmv_lo hbge
              have hrsn_lt : rsn.toNat < nc.toNat := by
                have hc' := hc; fid_norm_ofnat
                simp (disch := fid_omega) only [bv_c0, Nat.reducePow, Nat.reduceMod] at hc'
                have hne_fl_rs : ((4224 + 6 * mv + v).setWidth 64).toNat ≠
                    ((4224 + mv + v).setWidth 64).toNat := by rw [hfl_e, hrs_e]; omega
                have h1_lt : 4224 + mv.toNat + v.toNat < 4294967296 :=
                  Nat.lt_trans (Nat.add_lt_add_left hv_lt _) (by omega)
                have h6_lt : 4224 + 6 * mv.toNat + v.toNat < 4294967296 :=
                  Nat.lt_trans (Nat.add_lt_add_left hv_lt _) (by omega)
                have hrs_i : (4224 + mv.toNat + (scrt[(4224 + 5 * mv.toNat + (4294967296 - 1 +
                    ti.toNat)) % 4294967296]'(by rw [hadd]; exact htr_b)).toNat / 2) % 4294967296 =
                    ((4224 + mv + v).setWidth 64).toNat := by
                  rw [m8_k6_get_congr hadd _ htr_b, ← m8_bv32_lshr1_toNat, hrs_e,
                    Nat.mod_eq_of_lt h1_lt]
                have hfl_i : (4224 + 6 * mv.toNat +
                    (scrt[(4224 + 5 * mv.toNat + (4294967296 - 1 + ti.toNat)) % 4294967296]'(by
                      rw [hadd]; exact htr_b)).toNat / 2) % 4294967296 =
                    ((4224 + 6 * mv + v).setWidth 64).toNat := by
                  rw [m8_k6_get_congr hadd _ htr_b, ← m8_bv32_lshr1_toNat, hfl_e,
                    Nat.mod_eq_of_lt h6_lt]
                have h1_bv : BitVec.toNat (1 : BitVec 32) = 1 := rfl
                simp only [h1_bv, hfl_i, hrs_i] at hc'
                erw [List.getElem_set_ne hne_fl_rs] at hc'
                have : scrt[((4224 + mv + v).setWidth 64).toNat]'hrs_k = rsn := by
                  dsimp only [rsn, scrt1]; exact (List.getElem_set_ne hne_fl_rs _).symm
                rw [this] at hc'; exact Nat.lt_of_not_le hc'
              clear hc
              have hmr_e := fid_k6_off_add (mv := mv) (k := 33) (x := rsn)
                hmv_hi (by decide) (by omega)
              have hor_e := fid_k6_off_add (mv := mv) (k := 29) (x := rsn)
                hmv_hi (by decide) (by omega)
              have hmr_b : ((4224 + 33 * mv + rsn).setWidth 64).toNat < scrt1.length := by
                rw [hlt1, hmr_e]; exact fidCore_k_lt 33 (by omega) hmv_lo hbge
              have hor_b : ((4224 + 29 * mv + rsn).setWidth 64).toNat < scrt1.length := by
                rw [hlt1, hor_e]; exact fidCore_k_lt 29 (by omega) hmv_lo hbge
              let mr := scrt1[((4224 + 33 * mv + rsn).setWidth 64).toNat]'hmr_b
              let scrt2_raw :=
                scrt1.set ((4224 + 33 * mv + rsn).setWidth 64).toNat (mr ||| 0x80000000#32)
              have hikt2_raw := fidCoreInv_set_meta_pres
                h4214 hmv_eq hnc_le hikt1 hrsn_lt hmr_e hmr_b (m8_km_core_or_pres _)
              have hlt2_raw : scrt2_raw.length = scr0.length := hikt2_raw.2.1
              have hor_b2_raw : ((4224 + 29 * mv + rsn).setWidth 64).toNat < scrt2_raw.length := by
                rw [hlt2_raw, hor_e]; exact fidCore_k_lt 29 (by omega) hmv_lo hbge
              have hmr_b2_raw : ((4224 + 33 * mv + rsn).setWidth 64).toNat < scrt2_raw.length := by
                rw [hlt2_raw, hmr_e]; exact fidCore_k_lt 33 (by omega) hmv_lo hbge
              have h4193' : 4193 < scr0.length := h4193
              have hnc_eq' : scr0[4193]?.getD 0#32 = nc := by
                rw [List.getElem?_eq_getElem h4193', Option.getD_some, hnc_d]
              have h4207' : 4207 < scr0.length := by omega
              c0_hsteps_nogrp
              obtain ⟨scrt2, hscrt2_d⟩ : ∃ x : List (BitVec 32), x = scrt2_raw := ⟨_, rfl⟩
              have hikt2 : FidCoreInv scr0 mv nc scrt2 := hscrt2_d ▸ hikt2_raw
              have hlt2 : scrt2.length = scr0.length := hikt2.2.1
              have hor_b2 : ((4224 + 29 * mv + rsn).setWidth 64).toNat < scrt2.length := by
                rw [hlt2, hor_e]; exact fidCore_k_lt 29 (by omega) hmv_lo hbge
              have hmr_b2 : ((4224 + 33 * mv + rsn).setWidth 64).toNat < scrt2.length := by
                rw [hlt2, hmr_e]; exact fidCore_k_lt 33 (by omega) hmv_lo hbge
              have hcl_t2 := fidCore_clause_ok_bnds h4214 hmv_eq h4193' hnc_eq' h4207 hac_eq
                hmv_hi hnc_le hikt2 hrsn_lt hor_e hmr_e hor_b2 hmr_b2
              replace hm : (FullMem c (m8ScrSt s scrt2) ⋆ R) m := by
                rw [hscrt2_d]; exact hm
              obtain ⟨roff, hroff_d⟩ : ∃ x : BitVec 32,
                  x = scrt2[((4224 + 29 * mv + rsn).setWidth 64).toNat]'hor_b2 := ⟨_, rfl⟩
              obtain ⟨rsz, hrsz_d⟩ : ∃ x : BitVec 32,
                  x = (scrt2[((4224 + 33 * mv + rsn).setWidth 64).toNat]'hmr_b2) &&& 0xFFFF#32 :=
                ⟨_, rfl⟩
              have hrsz_le : rsz.toNat ≤ 65535 := by rw [hrsz_d]; exact m8_and_ffff_le _
              refine wp_join0 invS
                (fun _ mj ⟨scrj, hikj, hmj⟩ => by
                  c0_hsteps_nogrp; exact hLt ti'.toNat (ti', ()) mj
                    (by dsimp only [ti']; rw [hti1]; omega)
                    ⟨scrj, hikj, by dsimp only [ti']; rw [hti1]; omega, rfl, hmj⟩)
                (fun Jc hJc => by
                  have hrsn_c : (scrt.set ((4224 + 6 * mv + v).setWidth 64).toNat
                      ((scrt[((4224 + 6 * mv + v).setWidth 64).toNat]'hfl_b) &&&
                        ~~~(2 : BitVec 32)))[((4224 + mv + v).setWidth 64).toNat]'(by
                          rw [List.length_set]; exact hrs_k) = rsn := rfl
                  have hmr_c : (scrt.set ((4224 + 6 * mv + v).setWidth 64).toNat
                      ((scrt[((4224 + 6 * mv + v).setWidth 64).toNat]'hfl_b) &&&
                        ~~~(2 : BitVec 32)))[((4224 + 33 * mv + rsn).setWidth 64).toNat]'(by
                          rw [List.length_set, hlt, ← hlt1]; exact hmr_b) = mr := rfl
                  have hscrt2_eq :
                      (scrt.set ((4224 + 6 * mv + v).setWidth 64).toNat
                          ((scrt[((4224 + 6 * mv + v).setWidth 64).toNat]'hfl_b) &&&
                            ~~~(2 : BitVec 32))).set
                        ((4224 + 33 * mv + rsn).setWidth 64).toNat
                        (mr ||| (2147483648 : BitVec 32)) = scrt2 := by
                    rw [hscrt2_d]; rfl
                  have hroff_c : scrt2[((4224 + 29 * mv + rsn).setWidth 64).toNat]'hor_b2 =
                      roff := hroff_d.symm
                  have hrsz_c :
                      (scrt2[((4224 + 33 * mv + rsn).setWidth 64).toNat]'hmr_b2 &&&
                        (65535 : BitVec 32)) = rsz := hrsz_d.symm
                  have hv_c : (scrt[((4224 + 5 * mv + ti').setWidth 64).toNat]'htr_b) >>>
                      (1 : Nat) = v := rfl
                  have hroff_rsz : roff.toNat + rsz.toNat ≤ acap.toNat := by
                    simpa only [← hroff_d, ← hrsz_d] using hcl_t2.1
                  simp only [show (4224#32 : BitVec 32) = 4224 from rfl,
                    show (5#32 : BitVec 32) = 5 from rfl, show (6#32 : BitVec 32) = 6 from rfl,
                    show (29#32 : BitVec 32) = 29 from rfl, show (33#32 : BitVec 32) = 33 from rfl,
                    show (45#32 : BitVec 32) = 45 from rfl,
                    show ti - (1 : BitVec 32) = ti' from rfl]
                  simp only [hv_c, hrsn_c, hmr_c, hscrt2_eq, hroff_c, hrsz_c]
                  change wp Γ Q X
                    (s13FidIncClauseE c.pScratchBuf mv nv acap v roff rsz Jc) m
                  exact s13_fid_inc_clause_wp h4214 hmv_eq hmv_lo hmv_hi h4207 hac_eq
                    hnv_le hbge hlen_scr hcap_lt hJc hikt2 hroff_rsz hrsz_le hm)
      · c0_hsteps_nogrp
        refine wp_loop_group (ts := [i32])
          (fun rem_f (i, ()) mf => ∃ scrf : List (BitVec 32), FidCoreInv scr0 mv nc scrf ∧
            i.toNat ≤ nv.toNat ∧ rem_f = nv.toNat - i.toNat ∧
            (FullMem c (m8ScrSt s scrf) ⋆ R) mf)
          ?_ (fun Lf hLf => by
            c0_hsteps_nogrp
            exact hLf nv.toNat (0#32, ()) mt ⟨scrt, hikt, Nat.zero_le _, by simp, hmt⟩)
        rintro Lf rem_f ⟨i, ⟨⟩⟩ mf hLf ⟨scrf, hikf, hi_le, rfl, hmf⟩
        have hlf : scrf.length = scr0.length := hikf.2.1
        c0_hsplit
        · have hi_lt : i.toNat < nv.toNat := hc
          have hi1 : (i + 1#32).toNat = i.toNat + 1 := m8_bv32_add1_toNat hi_lt (by omega)
          have hfl_e := fid_k6_off_add (mv := mv) (k := 6) (x := i)
            hmv_hi (by decide) (by omega)
          have hfl_b : ((4224 + 6 * mv + i).setWidth 64).toNat < scrf.length := by
            rw [hlf, hfl_e]; omega
          c0_hsteps_nogrp; exact hLf (nv.toNat - (i + 1#32).toNat) (i + 1#32, ()) _ (by omega)
            ⟨_, fidCoreInv_set_flags_e h4214 hmv_eq hikf (by omega) hfl_e _, by omega, rfl, hm⟩
        · c0_hsteps_nogrp; exact hJ2 _ mf ⟨scrf, hikf, hmf⟩)
    (fun Jti hJti => by
      c0_hsplit
      · c0_hsteps_nogrp; exact hJti mv (Nat.le_refl _)
      · c0_hsteps_nogrp; exact hJti _ (Nat.le_of_not_lt hc))

private theorem s13_fid_inc_wp {Γ : Env} {c : FullCfg} {s : FullState}
    {scr0 : List (BitVec 32)} {mv nc nv acap inc : BitVec 32} {R : Mem 64 → Prop}
    {Q : Post []} {X : XPost} {J2 : Cont [.bits 32]}
    (hscr_len : scr0.length = c.scratch_cap)
    (h4214 : 4214 < scr0.length) (_hmv_d : scr0[4214]'h4214 = mv)
    (hmv_eq : scr0[4214]?.getD 0#32 = mv) (hmv_lo : 256 ≤ mv.toNat) (hmv_hi : mv.toNat ≤ 8192)
    (h4192 : 4192 < scr0.length) (hnv_d : scr0[4192]'h4192 = nv)
    (h4193 : 4193 < scr0.length) (hnc_d : scr0[4193]'h4193 = nc)
    (hnc_eq : scr0[4193]?.getD 0#32 = nc) (hnc_le : nc.toNat ≤ 4 * mv.toNat)
    (h4207 : 4207 < scr0.length) (_hac_d : scr0[4207]'h4207 = acap)
    (hac_eq : scr0[4207]?.getD 0#32 = acap)
    (hnv_le : nv.toNat ≤ mv.toNat) (hbge : 4224 + 45 * mv.toNat ≤ scr0.length)
    (hlen_scr : 4224 + 45 * mv.toNat + acap.toNat ≤ scr0.length) (hcap_lt : scr0.length < 2 ^ 30)
    (hinc_lt : inc.toNat < nc.toNat)
    (hJ2 : ∀ x : Val i32, ∀ m2, (∃ scr2 : List (BitVec 32),
      FidCoreInv scr0 mv nc scr2 ∧ (FullMem c (m8ScrSt s scr2) ⋆ R) m2) → J2 (x, ()) m2)
    {scrl : List (BitVec 32)} {ml : Mem 64}
    (hikl : FidCoreInv scr0 mv nc scrl) (hml : (FullMem c (m8ScrSt s scrl) ⋆ R) ml) :
    wp Γ Q X (s13FidIncE c.hdr c.pScratchBuf mv nc nv acap inc J2) ml := by
  let invS : Mem 64 → Prop := fun mj =>
    ∃ scrj : List (BitVec 32), FidCoreInv scr0 mv nc scrj ∧ (FullMem c (m8ScrSt s scrj) ⋆ R) mj
  dsimp only [s13FidIncE, s13FidPhase2E, full_k6_core_fid_body, fSLet, fSLd, fSLd64, fSJF, fSJT,
    fSGrp1, fidDfltT, fidDflt]
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32])
    (fun rem (i, ()) ma => ∃ scra : List (BitVec 32), FidCoreInv scr0 mv nc scra ∧
      i.toNat ≤ nv.toNat ∧ rem = nv.toNat - i.toNat ∧ (FullMem c (m8ScrSt s scra) ⋆ R) ma)
    ?_ (fun La hLa => by
      c0_hsteps_nogrp; exact hLa nv.toNat (0#32, ()) ml ⟨scrl, hikl, Nat.zero_le _, by simp, hml⟩)
  rintro La rem ⟨i, ⟨⟩⟩ ma hLa ⟨scra, hika, hi_le, rfl, hma⟩
  have hla : scra.length = scr0.length := hika.2.1
  c0_hsplit
  · have hi_lt : i.toNat < nv.toNat := hc
    have hi1 : (i + 1#32).toNat = i.toNat + 1 := m8_bv32_add1_toNat hi_lt (by omega)
    have hfl_e := fid_k6_off_add (mv := mv) (k := 6) (x := i) hmv_hi (by decide) (by omega)
    have hfl_b : ((4224 + 6 * mv + i).setWidth 64).toNat < scra.length := by rw [hla, hfl_e]; omega
    c0_hsteps_nogrp; exact hLa (nv.toNat - (i + 1#32).toNat) (i + 1#32, ()) _ (by omega)
      ⟨_, fidCoreInv_set_flags_e h4214 hmv_eq hika (by omega) hfl_e _, by omega, rfl, hm⟩
  · have hcm_e := fid_k6_off_add (mv := mv) (k := 33) (x := inc) hmv_hi (by decide) (by omega)
    have hco_e := fid_k6_off_add (mv := mv) (k := 29) (x := inc) hmv_hi (by decide) (by omega)
    have hcm_b : ((4224 + 33 * mv + inc).setWidth 64).toNat < scra.length := by
      rw [hla, hcm_e]; omega
    have hco_b : ((4224 + 29 * mv + inc).setWidth 64).toNat < scra.length := by
      rw [hla, hco_e]; omega
    let meta_i := scra[((4224 + 33 * mv + inc).setWidth 64).toNat]'hcm_b
    have hmeta_get : scra[4224 + 33 * mv.toNat + inc.toNat]'(by omega) = meta_i :=
      m8_k6_get_congr hcm_e.symm (by omega) hcm_b
    let scrb := scra.set (4224 + 33 * mv.toNat + inc.toNat) (meta_i ||| 0x80000000#32)
    have hikb : FidCoreInv scr0 mv nc scrb := by
      have hpres := m8_km_core_or_pres meta_i
      refine fidCoreInv_set_meta h4214 hmv_eq hnc_le hika hinc_lt ?_ ?_
      · rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hmeta_get]; exact hpres.1
      · rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hmeta_get]; exact hpres.2
    have hlb : scrb.length = scr0.length := hikb.2.1
    have hcl_b := fidCore_clause_ok_bnds h4214 hmv_eq h4193 hnc_eq h4207 hac_eq hmv_hi hnc_le
      hikb hinc_lt hco_e hcm_e (by rw [hlb, hco_e]; omega) (by rw [hlb, hcm_e]; omega)
    c0_hsteps_nogrp
    replace hm : (FullMem c (m8ScrSt s scrb) ⋆ R) m := by
      dsimp only [scrb]; rw [← hcm_e]; exact hm
    refine wp_join0 invS
      (fun _ mb ⟨scrm, hikm, hmb⟩ => by
        dsimp only [Blocks.get]
        exact s13_fid_inc_trail_wp (inc := inc) h4214 hmv_eq hmv_lo hmv_hi h4192 hnv_d h4193
          hnc_d hnc_le h4207 hac_eq hnv_le hbge hlen_scr hcap_lt hJ2 hikm hmb)
      (fun Jm hJm => by
        have h33_lt : 4224 + 33 * mv.toNat + inc.toNat < scr0.length := by
          have : nc.toNat ≤ 4 * mv.toNat := hnc_le
          have : inc.toNat < nc.toNat := hinc_lt
          have : 4224 + 45 * mv.toNat ≤ scr0.length := hbge
          omega
        have h29_lt : 4224 + 29 * mv.toNat + inc.toNat < scr0.length := by
          have : 256 ≤ mv.toNat := hmv_lo
          omega
        have h33_b : 4224 + 33 * mv.toNat + inc.toNat < scra.length := hla ▸ h33_lt
        have h29_b : 4224 + 29 * mv.toNat + inc.toNat < scra.length := hla ▸ h29_lt
        have h33_b2 : 4224 + 33 * mv.toNat + inc.toNat < scrb.length := hlb ▸ h33_lt
        have h29_b2 : 4224 + 29 * mv.toNat + inc.toNat < scrb.length := hlb ▸ h29_lt
        have hco_b2 : ((4224 + 29 * mv + inc).setWidth 64).toNat < scrb.length := by
          rw [hlb, hco_e]; exact h29_lt
        have hcm_b2 : ((4224 + 33 * mv + inc).setWidth 64).toNat < scrb.length := by
          rw [hlb, hcm_e]; exact h33_lt
        have hne_cm_co : 4224 + 33 * mv.toNat + inc.toNat ≠ 4224 + 29 * mv.toNat + inc.toNat :=
          Nat.ne_of_gt (by
            have : 256 ≤ mv.toNat := hmv_lo
            exact Nat.add_lt_add_right (Nat.add_lt_add_left (by omega) 4224) _)
        let off_i := scra[4224 + 29 * mv.toNat + inc.toNat]'h29_b
        let sz_i := meta_i &&& 0xFFFF#32
        have hoff_0 : scr0[4224 + 29 * mv.toNat + inc.toNat]'h29_lt = off_i := by
          have h29_r : 4224 + 7 * mv.toNat ≤ 4224 + 29 * mv.toNat + inc.toNat ∧
              4224 + 29 * mv.toNat + inc.toNat < 4224 + 33 * mv.toNat :=
            ⟨by omega, by omega⟩
          have heq := hika.2.2.1 (4224 + 29 * mv.toNat + inc.toNat) h29_lt
            (Or.inr (Or.inl h29_r))
          rw [List.getElem?_eq_getElem h29_b, List.getElem?_eq_getElem h29_lt] at heq
          exact Option.some.inj heq.symm
        have hoff_g2 : scrb[4224 + 29 * mv.toNat + inc.toNat]'h29_b2 = off_i := by
          dsimp only [scrb, off_i]; exact List.getElem_set_ne hne_cm_co _
        have hoff_g2e : scrb[((4224 + 29 * mv + inc).setWidth 64).toNat]'hco_b2 = off_i :=
          (m8_k6_get_congr hco_e hco_b2 h29_b2).trans hoff_g2
        have hmeta_g2 : scrb[4224 + 33 * mv.toNat + inc.toNat]'h33_b2 =
            meta_i ||| 0x80000000#32 := by
          dsimp only [scrb]; rw [List.getElem_set_self]
        have hsz_g2e :
            (scrb[((4224 + 33 * mv + inc).setWidth 64).toNat]'hcm_b2 &&& 0xFFFF#32) = sz_i := by
          rw [m8_k6_get_congr hcm_e hcm_b2 h33_b2, hmeta_g2]; exact (m8_km_core_or_pres meta_i).1
        have hszi_le : sz_i.toNat ≤ 65535 := m8_and_ffff_le _
        have hszi_bnd : off_i.toNat + sz_i.toNat ≤ acap.toNat := by
          have hb := (fidCore_clause_ok_bnds h4214 hmv_eq h4193 hnc_eq h4207 hac_eq hmv_hi hnc_le
            hikb hinc_lt hco_e hcm_e hco_b2 hcm_b2).1
          rwa [hoff_g2e, hsz_g2e] at hb
        c0_hsplit
        · try clear hc
          c0_hsteps_nogrp
          refine wp_loop_group (ts := [i32])
            (fun rem_j (j, ()) mj => ∃ scrj : List (BitVec 32), FidCoreInv scr0 mv nc scrj ∧
              j.toNat ≤ sz_i.toNat ∧ rem_j = sz_i.toNat - j.toNat ∧
              (FullMem c (m8ScrSt s scrj) ⋆ R) mj)
            ?_ (fun Lj hLj => by
              c0_hsteps_nogrp
              exact hLj sz_i.toNat (0#32, ()) _ ⟨scrb, hikb, Nat.zero_le _, by simp, hm⟩)
          rintro Lj rem_j ⟨j, ⟨⟩⟩ mj hLj ⟨scrj, hikj, hj_le, rfl, hmj⟩
          have hlj : scrj.length = scr0.length := hikj.2.1
          c0_hsplit
          · have hj_lt : j.toNat < sz_i.toNat := by
              have hc' := hc; clear hc
              try rw [BitVec.lt_def] at hc'
              simp only [Nat.reducePow, show (33 % 2 ^ 32 : Nat) = 33 from rfl] at hc'
              have h33_u : 4224 + 33 * mv.toNat + inc.toNat < 4294967296 :=
                Nat.lt_trans h33_lt (Nat.lt_trans hcap_lt (by decide))
              have hidx_33 : (4224 + 33 * mv.toNat + inc.toNat) % 4294967296 =
                  4224 + 33 * mv.toNat + inc.toNat := Nat.mod_eq_of_lt h33_u
              simp only [hidx_33, List.getElem_set_self, hmeta_get] at hc'
              have hsz_lt : ((meta_i ||| 2147483648).toNat % 65536) = sz_i.toNat := by
                rw [← Nat.and_two_pow_sub_one_eq_mod _ 16,
                  show (2 ^ 16 - 1 : Nat) = (65535 : BitVec 32).toNat from rfl,
                  ← BitVec.toNat_and, show (65535 : BitVec 32) = 0xFFFF#32 from rfl,
                  show (2147483648 : BitVec 32) = 0x80000000#32 from rfl,
                  (m8_km_core_or_pres meta_i).1]
              rwa [hsz_lt] at hc'
            clear hc
            have hj1 : (j + 1#32).toNat = j.toNat + 1 := m8_bv32_add1_toNat hj_lt (by omega)
            have har_sum : 4224 + 45 * mv.toNat + off_i.toNat + j.toNat < scr0.length := by
              have : off_i.toNat + j.toNat < off_i.toNat + sz_i.toNat := Nat.add_lt_add_left hj_lt _
              exact Nat.lt_of_lt_of_le (by omega) hlen_scr
            have har_u : 4224 + 45 * mv.toNat + off_i.toNat + j.toNat < 2 ^ 32 :=
              Nat.lt_trans har_sum (Nat.lt_trans hcap_lt (by decide))
            have har_e := fid_k6_off_add2 (mv := mv) (k := 45) (x := off_i) (y := j)
              hmv_hi (by decide) (by omega)
            have har_lt : ((4224 + 45 * mv + off_i + j).setWidth 64).toNat < scrj.length := by
              erw [hlj, har_e]; exact har_sum
            let lv :=
              (scrj[((4224 + 45 * mv + off_i + j).setWidth 64).toNat]'har_lt) >>> (1 : Nat)
            have h33_c0_b :
                (BitVec.setWidth 64 (4224#32 + 33#32 * mv + inc)).toNat < scra.length := hcm_b
            have h29_c0_b :
                (BitVec.setWidth 64 (4224#32 + 29#32 * mv + inc)).toNat <
                  (scra.set (BitVec.setWidth 64 (4224#32 + 33#32 * mv + inc)).toNat
                    (scra[(BitVec.setWidth 64 (4224#32 + 33#32 * mv + inc)).toNat]'h33_c0_b |||
                      2147483648)).length := by
              rw [List.length_set]; exact hco_b
            have hscrb_off_g :
                (scra.set (BitVec.setWidth 64 (4224#32 + 33#32 * mv + inc)).toNat
                    (scra[(BitVec.setWidth 64 (4224#32 + 33#32 * mv + inc)).toNat]'h33_c0_b |||
                      2147483648))[(BitVec.setWidth 64 (4224#32 + 29#32 * mv + inc)).toNat]'
                    h29_c0_b = off_i := by
              have h := hoff_g2e
              dsimp only [scrb, meta_i] at h
              simp only [hcm_e] at h
              simpa only [show (4224#32 : BitVec 32) = 4224 from rfl,
                show (33#32 : BitVec 32) = 33 from rfl, show (29#32 : BitVec 32) = 29 from rfl,
                show (2147483648 : BitVec 32) = 0x80000000#32 from rfl, hcm_e] using h
            clear hm
            simp only [hscrb_off_g]
            c0_hsteps_nogrp
            refine wp_join0 invS
              (fun _ mj' ⟨scrj', hikj', hmj'⟩ => by
                c0_hsteps_nogrp; exact hLj (sz_i.toNat - (j + 1#32).toNat) (j + 1#32, ()) mj'
                  (by omega) ⟨scrj', hikj', by omega, rfl, hmj'⟩)
              (fun Js hJs => by
                c0_hsplit
                · have hlv_lt : lv.toNat < nv.toNat := by
                    have hc' := hc; clear hc
                    simp only [show (45 % 2 ^ 32 : Nat) = 45 from rfl] at hc'
                    have har_i :
                        (4224 + 45 * mv.toNat + off_i.toNat + j.toNat) % 2 ^ 32 =
                        ((4224 + 45 * mv + off_i + j).setWidth 64).toNat := by
                      rw [har_e, show (2 ^ 32 : Nat) = 4294967296 from rfl,
                        Nat.mod_eq_of_lt har_u]
                    rw [m8_k6_get_congr har_i _ har_lt, ← m8_bv32_lshr1_toNat] at hc'
                    exact hc'
                  have hfl_lv := fid_k6_off_add (mv := mv) (k := 6) (x := lv)
                    hmv_hi (by decide) (by omega)
                  have hfl_lvb : ((4224 + 6 * mv + lv).setWidth 64).toNat < scrj.length := by
                    erw [hlj, hfl_lv]; omega
                  c0_hsteps_nogrp
                  refine hJs _ ⟨_, fidCoreInv_set_flags_e h4214 hmv_eq hikj
                    (by omega) hfl_lv
                    ((scrj[((4224 + 6 * mv + lv).setWidth 64).toNat]'hfl_lvb) ||| 2#32), ?_⟩
                  simpa only [List.length_set, show (4224#32 : BitVec 32) = 4224 from rfl,
                    show (6#32 : BitVec 32) = 6 from rfl, show (45#32 : BitVec 32) = 45 from rfl,
                    show (2 : BitVec 32) = 2#32 from rfl] using hm
                · c0_hsteps_nogrp; exact hJs _ ⟨scrj, hikj, hmj⟩)
          · c0_hsteps_nogrp; exact hJm mj ⟨scrj, hikj, hmj⟩
        · c0_hsteps_nogrp; exact hJm _ ⟨scrb, hikb, hm⟩)

/-- Certifies `FullFidelityBve.fidK6CoreSpec` for Step-13 `full_k6_core_fid`. -/
theorem full_k6_core_fid_s13_wp (Γ : Env) :
    ∀ a m Q X, fidK6CoreSpec a m Q X → Func.wp Γ full_k6_core_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, s, R, rfl, hlen, hok, hm0, hQ⟩ := fidK6CoreSpec_elim hSpec
  let scr0 := s.scratch.scratch_buf
  have hscr_len : scr0.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hmin : 15744 ≤ scr0.length := hok.min_len
  have hmv_lo : 256 ≤ (scr0[4214]?.getD 0#32).toNat := hok.mv_lo
  have hmv_hi : (scr0[4214]?.getD 0#32).toNat ≤ 8192 := hok.mv_hi
  have hbge : 4224 + 45 * (scr0[4214]?.getD 0#32).toNat ≤ scr0.length := hok.base_ge
  have hlen_ge := hok.length_ge; have hlen_lt := hok.length_lt
  have h4214 : 4214 < scr0.length := by omega
  have h4193 : 4193 < scr0.length := by omega
  have h4192 : 4192 < scr0.length := by omega
  have h4207 : 4207 < scr0.length := by omega
  let mv := scr0[4214]'h4214; let nc := scr0[4193]'h4193
  let nv := scr0[4192]'h4192; let acap := scr0[4207]'h4207
  have hmv_eq : (scr0[4214]?.getD 0#32) = mv := m8_k6_get_eq h4214
  have hnc_eq : (scr0[4193]?.getD 0#32) = nc := m8_k6_get_eq h4193
  have hac_eq : (scr0[4207]?.getD 0#32) = acap := m8_k6_get_eq h4207
  rw [hmv_eq] at hmv_lo hmv_hi hbge hlen_ge; rw [hac_eq] at hlen_ge
  have hm0' : (FullMem c (m8ScrSt s scr0) ⋆ R) m0 := by rwa [m8ScrSt_self]
  have hret_noop : Q () m0 := hQ scr0 m0 hscr_len (fun _ _ _ => rfl) hok hm0
  unfold Func.wp full_k6_core_fid_body
  c0_hsplit; · c0_hsteps_nogrp; exact hret_noop
  c0_hsplit; · c0_hsteps_nogrp; exact hret_noop
  c0_hsplit; · c0_hsteps_nogrp; exact hret_noop
  have hnc_le : nc.toNat ≤ 4 * mv.toNat := by
    change ¬ (mv.toNat * 4) % 2 ^ 32 < nc.toNat at hc
    rw [Nat.mod_eq_of_lt (by omega)] at hc
    omega
  c0_hsplit; · c0_hsteps_nogrp; exact hret_noop
  have hnv_le : nv.toNat ≤ mv.toNat := Nat.le_of_not_lt hc
  have hinv0 : FidCoreInv scr0 mv nc scr0 := ⟨hok, rfl, fun _ _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32])
    (fun rem (i, ()) ml => ∃ scrl : List (BitVec 32), FidCoreInv scr0 mv nc scrl ∧
      i.toNat ≤ nc.toNat ∧ rem = nc.toNat - i.toNat ∧ (FullMem c (m8ScrSt s scrl) ⋆ R) ml)
    ?_ (fun L1 hL1 => by
      c0_hsteps_nogrp
      exact hL1 nc.toNat (0#32, ()) m0 ⟨scr0, hinv0, Nat.zero_le _, by simp, hm0'⟩)
  rintro L1 rem ⟨i, ⟨⟩⟩ ml hL1 ⟨scrl, hikl, hi_le, rfl, hml⟩
  have hll : scrl.length = scr0.length := hikl.2.1
  c0_hsplit
  · have hi_lt : i.toNat < nc.toNat := hc
    have hi1 : (i + 1#32).toNat = i.toNat + 1 := m8_bv32_add1_toNat hi_lt (by omega)
    have hcm_e := fid_k6_off_add (mv := mv) (k := 33) (x := i) hmv_hi (by decide) (by omega)
    have hcm_lt : (((4224 : BitVec 32) + (33 : BitVec 32) * mv + i).setWidth 64).toNat <
        scrl.length := by rw [hll, hcm_e]; omega
    c0_hsteps_nogrp; exact hL1 (nc.toNat - (i + 1#32).toNat) (i + 1#32, ()) _ (by omega)
      ⟨_, fidCoreInv_set_meta_pres h4214 hmv_eq hnc_le hikl hi_lt hcm_e hcm_lt
        (m8_km_core_clear_pres _), by omega, rfl, hm⟩
  · c0_hsteps_nogrp
    refine wp_join_state (ts := [i32]) (α := BitVec 32 × List (BitVec 32)) (fun x => (x.1, ()))
      (fun x m2 => FidCoreInv scr0 mv nc x.2 ∧ (FullMem c (m8ScrSt s x.2) ⋆ R) m2)
      (fun J2 ⟨x_i, scr2⟩ m2 ⟨hik2, hm2⟩ => by
        dsimp only [Blocks.get]
        change wp Γ Q X (s13FidFixE c.hdr c.pScratchBuf mv nc nv acap x_i J2) m2
        exact s13_fid_fixpoint_wp (x_i := x_i) (J2 := J2) hscr_len h4214 rfl hmv_eq hmv_lo hmv_hi
          h4192 rfl h4193 rfl hnc_eq hnc_le h4207 rfl hac_eq hnv_le hbge hlen_ge hlen_lt
          (fun scrp mp hikp hlp hmp => hQ scrp mp hlp
            (fun idx hi hor => by rw [hmv_eq] at hor; exact hikp.2.2.1 idx (by omega) hor)
            hikp.1 (m8ScrSt_eq s scrp ▸ hmp)) hik2 hm2)
      (fun J2 hJ2 => by
        have h4199 : 4199 < scrl.length := by omega
        let inc := scrl[4199]'h4199
        c0_hsplit
        · exact s13_fid_inc_wp hscr_len h4214 rfl hmv_eq hmv_lo hmv_hi h4192 rfl h4193 rfl
            hnc_eq hnc_le h4207 rfl hac_eq hnv_le hbge hlen_ge hlen_lt hc
            (fun x m2 ⟨scr2, hik2, hm2⟩ => hJ2 (x, scr2) m2 ⟨hik2, hm2⟩) hikl hml
        · c0_hsteps_nogrp; exact hJ2 (i, scrl) ml ⟨hikl, hml⟩)

end S13CoreFidMain

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S1
