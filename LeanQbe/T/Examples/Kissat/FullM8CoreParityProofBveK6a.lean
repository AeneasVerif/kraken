/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBve0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M8 Core Parity K6 Core Pass (`full_k6_core_m8_wp`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM8CoreParity

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM7BveGates
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro "m8_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))


private def M8CoreInv (scr0 : List (BitVec 32)) (nc : BitVec 32)
    (scr : List (BitVec 32)) : Prop :=
  M8K6BufOk scr ∧ scr.length = scr0.length ∧
  (∀ idx < scr0.length, (idx < 5760 ∨ (6016 ≤ idx ∧ idx < 12672) ∨ 13696 ≤ idx) →
    scr[idx]? = scr0[idx]?) ∧
  (∀ cid < nc.toNat,
    let m0 := scr0[12672 + cid]?.getD 0#32
    let m1 := scr[12672 + cid]?.getD 0#32
    (m1 &&& 0xFFFF#32) = (m0 &&& 0xFFFF#32) ∧
    (m1 &&& 0x40000000#32) = (m0 &&& 0x40000000#32))

private theorem m8CoreInv_set_meta {scr0 : List (BitVec 32)} {nc : BitVec 32}
    (hnc_le : nc.toNat ≤ 1024) {scr : List (BitVec 32)} (hik : M8CoreInv scr0 nc scr)
    {cid : Nat} (hcid : cid < nc.toNat) {v : BitVec 32}
    (hsz : (v &&& 0xFFFF#32) = ((scr[12672 + cid]?.getD 0#32) &&& 0xFFFF#32))
    (hlrn : (v &&& 0x40000000#32) = ((scr[12672 + cid]?.getD 0#32) &&& 0x40000000#32)) :
    M8CoreInv scr0 nc (scr.set (12672 + cid) v) := by
  refine ⟨m8K6BufOk_set_core_meta hik.1 (by omega) hsz hlrn, by simp [hik.2.1],
    fun idx hi hor => ?_, fun j hj => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hik.2.2.1 idx hi hor
  · by_cases heq : j = cid
    · subst heq
      have hk_l : 12672 + j < scr.length := by have := hik.1.base_ge; omega
      dsimp only
      rw [List.getElem?_set_self hk_l, Option.getD_some, hsz, hlrn]
      exact hik.2.2.2 j hj
    · rw [List.getElem?_set_ne (by omega)]; exact hik.2.2.2 j hj

private theorem m8CoreInv_set_flags {scr0 : List (BitVec 32)} {nc : BitVec 32}
    {scr : List (BitVec 32)} (hik : M8CoreInv scr0 nc scr)
    {v : Nat} (hv : v < 256) (val : BitVec 32) :
    M8CoreInv scr0 nc (scr.set (5760 + v) val) := by
  refine ⟨m8K6BufOk_set_flags hik.1 hv val, by simp [hik.2.1],
    fun idx hi hor => ?_, fun j hj => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hik.2.2.1 idx hi hor
  · rw [List.getElem?_set_ne (by omega)]; exact hik.2.2.2 j hj

private def m8K6Dflt : (t : Ty) → Val t
  | .bool => false | .bits _ => 0 | .float _ => 0 | .pair a b => (m8K6Dflt a, m8K6Dflt b)
private def m8K6DfltT : (ts : List Ty) → Tup Val ts
  | [] => () | t :: r => (m8K6Dflt t, m8K6DfltT r)
private def m8K6SLd64 {L rs} (v : Val i64) : Expr Val L rs → Expr Val L rs
  | .let_ (ts := ts) _ k => m8K6SLd64 v (k (m8K6DfltT ts))
  | .load (.bits 64) _ k => k v
  | _ => .hlt
private def m8K6SLd32 {L rs} (v : Val i32) : Expr Val L rs → Expr Val L rs
  | .let_ (ts := ts) _ k => m8K6SLd32 v (k (m8K6DfltT ts))
  | .load (.bits 32) _ k => k v
  | _ => .hlt
private def m8K6SJF {L rs} : Expr Val L rs → Expr Val L rs
  | .let_ (ts := ts) _ k => m8K6SJF (k (m8K6DfltT ts))
  | .jnz _ _ e => e
  | _ => .hlt
private def m8K6SGrpB {rs} (x : Val i32) : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (ts := ts) _ k => m8K6SGrpB x (k (m8K6DfltT ts))
  | .group (sig := [[.bits 32]]) bs _ =>
      match bs ((fun _ _ => True), ()) with | .cons b _ => b (x, ())
  | _ => .hlt

private def m8K6FixpointE (hdr pScr : BitVec 64) (nc nv acap : BitVec 32) : Expr Val Cont [] :=
  let e := m8K6SLd64 pScr (full_k6_core_m8_body Val Cont (hdr, ()))
  let e := m8K6SJF (m8K6SJF (m8K6SLd32 acap (m8K6SLd32 nv (m8K6SLd32 nc e))))
  m8K6SGrpB 0#32 (m8K6SLd32 0#32 (m8K6SJF (m8K6SGrpB nc e)))

private def m8FullMemNoScr (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
  FullScrMetaArrs c s.scratch ⋆
  array (t := i32) c.pDelayed s.scratch.delayed ⋆
  array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
  array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆ c.pad

private theorem m8_fullMem_eq_scr (c : FullCfg) (s : FullState) (scr : List (BitVec 32)) :
    FullMem c { s with scratch := { s.scratch with scratch_buf := scr } } =
      (array (t := i32) c.pScratchBuf scr ⋆ m8FullMemNoScr c s) := by
  unfold FullMem FullScratchArrays FullScrDynArrs m8FullMemNoScr
  ac_rfl

private theorem m8_k6_zext_add_toNat {a b : BitVec 32} (h : a.toNat + b.toNat < 2 ^ 32) :
    (BitVec.setWidth 64 (a + b)).toNat = a.toNat + b.toNat := by
  rw [m6_zext32_toNat, BitVec.toNat_add, Nat.mod_eq_of_lt h]

private def m8K6CoreOrigLoopExpr (pScr : BitVec 64) (nc nv off_c sz_c : BitVec 32)
    (ch_c : Bool) (Jelse : Cont [.bool]) : Expr Val Cont [] :=
  Expr.group (sig := [[.bool, i32]])
    (fun Js =>
      Blocks.cons
        (fun p =>
          Expr.let_ ⟨OpCode.ult i32, (Arg.var p.snd.fst, Arg.var sz_c, ())⟩ fun b =>
          Expr.jnz (Arg.var b.fst)
            (Expr.let_ ⟨OpCode.add i32, (Arg.imm 15744, Arg.var off_c, ())⟩ fun a0 =>
             Expr.let_ ⟨OpCode.add i32, (Arg.var a0.fst, Arg.var p.snd.fst, ())⟩ fun a1 =>
             Expr.let_ ⟨OpCode.zext 32 64, (Arg.var a1.fst, ())⟩ fun a2 =>
             Expr.let_ ⟨OpCode.mul i64, (Arg.var a2.fst, Arg.imm 4, ())⟩ fun a3 =>
             Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var a3.fst, ())⟩ fun a4 =>
             Expr.load i32 (Arg.var a4.fst) fun ld0 =>
             Expr.let_ ⟨OpCode.lshr i32, (Arg.var ld0, Arg.imm 1, ())⟩ fun lv =>
             Expr.group (sig := [[.bool]])
               (fun _ =>
                 Blocks.cons
                   (fun p2 =>
                     Expr.let_ ⟨OpCode.add i32, (Arg.var p.snd.fst, Arg.imm 1, ())⟩ fun nj =>
                     Expr.jump Js.fst (Arg.var p2.fst, Arg.var nj.fst, ()))
                   Blocks.nil)
               (fun Jlv =>
                 Expr.let_ ⟨OpCode.ult i32, (Arg.var lv.fst, Arg.var nv, ())⟩ fun c1 =>
                 Expr.jnz (Arg.var c1.fst)
                   (Expr.let_ ⟨OpCode.add i32, (Arg.imm 4224, Arg.var lv.fst, ())⟩ fun b0 =>
                    Expr.let_ ⟨OpCode.zext 32 64, (Arg.var b0.fst, ())⟩ fun b1 =>
                    Expr.let_ ⟨OpCode.mul i64, (Arg.var b1.fst, Arg.imm 4, ())⟩ fun b2 =>
                    Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var b2.fst, ())⟩ fun b3 =>
                    Expr.load i32 (Arg.var b3.fst) fun ld1 =>
                    Expr.let_ ⟨OpCode.eq i32, (Arg.var ld1, Arg.imm 0, ())⟩ fun c2 =>
                    Expr.jnz (Arg.var c2.fst)
                      (Expr.let_ ⟨OpCode.add i32, (Arg.imm 4480, Arg.var lv.fst, ())⟩ fun d0 =>
                       Expr.let_ ⟨OpCode.zext 32 64, (Arg.var d0.fst, ())⟩ fun d1 =>
                       Expr.let_ ⟨OpCode.mul i64, (Arg.var d1.fst, Arg.imm 4, ())⟩ fun d2 =>
                       Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var d2.fst, ())⟩ fun d3 =>
                       Expr.load i32 (Arg.var d3.fst) fun r0 =>
                       Expr.group (sig := [[.bool]])
                         (fun _ =>
                           Blocks.cons (fun p3 => Expr.jump Jlv.fst (Arg.var p3.fst, ()))
                             Blocks.nil)
                         (fun Jr0 =>
                           Expr.let_ ⟨OpCode.ult i32, (Arg.var r0, Arg.var nc, ())⟩ fun c3 =>
                           Expr.jnz (Arg.var c3.fst)
                             (Expr.let_ ⟨OpCode.add i32, (Arg.imm 12672, Arg.var r0, ())⟩ fun e0 =>
                              Expr.let_ ⟨OpCode.zext 32 64, (Arg.var e0.fst, ())⟩ fun e1 =>
                              Expr.let_ ⟨OpCode.mul i64, (Arg.var e1.fst, Arg.imm 4, ())⟩ fun e2 =>
                              Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var e2.fst,
                                ())⟩ fun e3 =>
                              Expr.load i32 (Arg.var e3.fst) fun ld2 =>
                              Expr.let_ ⟨OpCode.and i32, (Arg.var ld2, Arg.imm 2147483648, ())⟩
                                fun e4 =>
                              Expr.let_ ⟨OpCode.eq i32, (Arg.var e4.fst, Arg.imm 0, ())⟩ fun c4 =>
                              Expr.jnz (Arg.var c4.fst)
                                (Expr.let_ ⟨OpCode.add i32, (Arg.imm 12672, Arg.var r0, ())⟩
                                   fun f0 =>
                                 Expr.let_ ⟨OpCode.zext 32 64, (Arg.var f0.fst, ())⟩ fun f1 =>
                                 Expr.let_ ⟨OpCode.mul i64, (Arg.var f1.fst, Arg.imm 4, ())⟩
                                   fun f2 =>
                                 Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var f2.fst, ())⟩
                                   fun f3 =>
                                 Expr.let_ ⟨OpCode.add i32, (Arg.imm 12672, Arg.var r0, ())⟩
                                   fun g0 =>
                                 Expr.let_ ⟨OpCode.zext 32 64, (Arg.var g0.fst, ())⟩ fun g1 =>
                                 Expr.let_ ⟨OpCode.mul i64, (Arg.var g1.fst, Arg.imm 4, ())⟩
                                   fun g2 =>
                                 Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var g2.fst, ())⟩
                                   fun g3 =>
                                 Expr.load i32 (Arg.var g3.fst) fun ld3 =>
                                 Expr.let_ ⟨OpCode.or i32, (Arg.var ld3, Arg.imm 2147483648, ())⟩
                                   fun g4 =>
                                 Expr.store (Arg.var g4.fst) (Arg.var f3.fst)
                                   (Expr.jump Jr0.fst (Arg.imm true, ())))
                                (Expr.jump Jr0.fst (Arg.var p.fst, ())))
                             (Expr.jump Jr0.fst (Arg.var p.fst, ()))))
                      (Expr.jump Jlv.fst (Arg.var p.fst, ())))
                   (Expr.jump Jlv.fst (Arg.var p.fst, ()))))
            (Expr.jump Jelse (Arg.var p.fst, ())))
        Blocks.nil)
    (fun Js => Expr.jump Js.fst (Arg.var ch_c, Arg.imm 0, ()))

private theorem m8_k6_core_orig_loop_wp {Γ : Env} {pScr : BitVec 64}
    {scr scc : List (BitVec 32)} {R' : Mem 64 → Prop} {Q : Post []} {X : XPost}
    {nc nv acap off_c sz_c : BitVec 32} {ch_c : Bool} {Jelse : Cont [.bool]} {mc : Mem 64}
    (hlen_ge : 15744 ≤ scr.length) (hnc_le : nc.toNat ≤ 1024) (hnv_le : nv.toNat ≤ 256)
    (hsz_lt : sz_c.toNat < 65536) (hoff_sz : off_c.toNat + sz_c.toNat ≤ acap.toNat)
    (hlt_ge : 15744 + acap.toNat ≤ scc.length) (hlt : scc.length < 2 ^ 30)
    (hkc : M8CoreInv scr nc scc)
    (hmc : (array (t := i32) pScr scc ⋆ R') mc)
    (hJelse : ∀ sc' ch' m', M8CoreInv scr nc sc' →
      (array (t := i32) pScr sc' ⋆ R') m' → Jelse (ch', ()) m') :
    wp Γ Q X (m8K6CoreOrigLoopExpr pScr nc nv off_c sz_c ch_c Jelse) mc := by
  have invCore_set_meta := @m8CoreInv_set_meta scr nc hnc_le
  have hkc_l := hkc.2.1
  unfold m8K6CoreOrigLoopExpr
  refine wp_loop_group (ts := [.bool, i32])
    (fun remj (_chj, j_c, ()) mj => ∃ scj, M8CoreInv scr nc scj ∧
      j_c.toNat ≤ sz_c.toNat ∧ remj = sz_c.toNat - j_c.toNat ∧
      (array (t := i32) pScr scj ⋆ R') mj)
    ?_ ?_
  · rintro Lj remj ⟨ch_j, j_c, ⟨⟩⟩ mj hLj ⟨scj, hkj, hj_le, rfl, hmj⟩
    have hkj_l := hkj.2.1
    c0_hsplit
    · have hj_lt : j_c.toNat < sz_c.toNat := hc; clear hc
      have hj1 : (j_c + 1#32).toNat = j_c.toNat + 1 := by c0_bound
      have hidx_lt : 15744 + off_c.toNat + j_c.toNat < scj.length := by omega
      have hidx_eq : (BitVec.setWidth 64 ((15744 : BitVec 32) + off_c + j_c)).toNat =
          15744 + off_c.toNat + j_c.toNat := by
        rw [m8_k6_zext_add_toNat (by
          rw [BitVec.toNat_add, show BitVec.toNat (15744 : BitVec 32) = 15744 from rfl,
            Nat.mod_eq_of_lt (by omega)]; omega)]
        rw [BitVec.toNat_add, show BitVec.toNat (15744 : BitVec 32) = 15744 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      have hidx_c0 : (BitVec.setWidth 64 ((15744 : BitVec 32) + off_c + j_c)).toNat <
          scj.length := by
        rw [hidx_eq]; exact hidx_lt
      c0_hsteps_nogrp
      refine wp_join_state1 (t := .bool) (α := List (BitVec 32) × Bool) (fun x => x.2)
        (fun x mj' => M8CoreInv scr nc x.1 ∧ (array (t := i32) pScr x.1 ⋆ R') mj')
        ?_ ?_
      · rintro _ ⟨scj', chj'⟩ mj' ⟨hkj', hmj'⟩
        c0_hsteps!
        exact hLj (sz_c.toNat - (j_c + 1#32).toNat) (chj', j_c + 1#32, ()) mj' (by omega)
          ⟨scj', hkj', by omega, rfl, hmj'⟩
      · intro Jlv hJlv
        let lv := (scj[15744 + off_c.toNat + j_c.toNat]'hidx_lt) >>> (1 : Nat)
        have hget_lv_c0 : scj[(BitVec.setWidth 64 ((15744 : BitVec 32) + off_c +
          j_c)).toNat]'hidx_c0 =
            scj[15744 + off_c.toNat + j_c.toNat]'hidx_lt := m8_k6_get_congr hidx_eq _ _
        have har_mod : (BitVec.toNat (15744 : BitVec 32) + off_c.toNat + j_c.toNat) % 2 ^ 32 =
            15744 + off_c.toNat + j_c.toNat := by
          rw [show BitVec.toNat (15744 : BitVec 32) = 15744 from rfl]; omega
        c0_hsplit
        · have hlv_lt : lv.toNat < nv.toNat := by
            dsimp only [lv]; rw [m8_bv32_lshr1_toNat,
              ← m8_k6_get_congr har_mod (by rw [har_mod]; exact hidx_lt) hidx_lt]
            exact hc
          clear hc
          have h4224_c0 : (BitVec.setWidth 64 ((4224 : BitVec 32) +
              ((scj[(BitVec.setWidth 64 ((15744 : BitVec 32) + off_c + j_c)).toNat]'hidx_c0) >>>
                (1 : Nat)))).toNat < scj.length := by
            rw [hget_lv_c0]
            rw [show (4224 : BitVec 32) + (scj[15744 + off_c.toNat +
              j_c.toNat]'hidx_lt >>> (1 : Nat)) =
                (4224 : BitVec 32) + lv from rfl]
            rw [m8_k6_zext_add_toNat (by
              rw [show BitVec.toNat (4224 : BitVec 32) = 4224 from rfl]; omega)]
            rw [show BitVec.toNat (4224 : BitVec 32) = 4224 from rfl]; omega
          c0_hsplit
          · clear hc
            have h4480_eq : (BitVec.setWidth 64 ((4480 : BitVec 32) +
                ((scj[(BitVec.setWidth 64 ((15744 : BitVec 32) + off_c + j_c)).toNat]'hidx_c0) >>>
                  (1 : Nat)))).toNat = 4480 + lv.toNat := by
              rw [hget_lv_c0]
              rw [show (4480 : BitVec 32) + (scj[15744 + off_c.toNat +
                j_c.toNat]'hidx_lt >>> (1 : Nat)) =
                  (4480 : BitVec 32) + lv from rfl]
              rw [m8_k6_zext_add_toNat (by
                rw [show BitVec.toNat (4480 : BitVec 32) = 4480 from rfl]; omega)]
              rfl
            have h4480_c0 : (BitVec.setWidth 64 ((4480 : BitVec 32) +
                ((scj[(BitVec.setWidth 64 ((15744 : BitVec 32) + off_c + j_c)).toNat]'hidx_c0) >>>
                  (1 : Nat)))).toNat < scj.length := by
              rw [h4480_eq]; omega
            let r0 := scj[4480 + lv.toNat]'(by omega)
            have hr0_c0_eq : scj[(BitVec.setWidth 64 ((4480 : BitVec 32) +
                ((scj[(BitVec.setWidth 64 ((15744 : BitVec 32) + off_c + j_c)).toNat]'hidx_c0) >>>
                  (1 : Nat)))).toNat]'h4480_c0 = r0 := m8_k6_get_congr h4480_eq h4480_c0 _
            c0_hsteps_nogrp
            refine wp_join_state1 (t := .bool) (α := List (BitVec 32) × Bool) (fun x => x.2)
              (fun x mj' => M8CoreInv scr nc x.1 ∧ (array (t := i32) pScr x.1 ⋆ R') mj')
              ?_ ?_
            · rintro _ ⟨scj', chj'⟩ mj' ⟨hkj', hmj'⟩
              c0_hsteps!; exact hJlv (scj', chj') mj' ⟨hkj', hmj'⟩
            · intro Jr0 hJr0
              have h4480_mod : (BitVec.toNat (4480 : BitVec 32) +
                  (scj[(BitVec.toNat (15744 : BitVec 32) + off_c.toNat + j_c.toNat) %
                    2 ^ 32]'(by rw [har_mod]; exact hidx_lt)).toNat / 2) % 2 ^ 32 =
                  4480 + lv.toNat := by
                rw [m8_k6_get_congr har_mod _ hidx_lt,
                  show BitVec.toNat (4480 : BitVec 32) = 4480 from rfl]
                have hdiv : (scj[15744 + off_c.toNat + j_c.toNat]'hidx_lt).toNat / 2 =
                    lv.toNat := (m8_bv32_lshr1_toNat _).symm
                rw [hdiv]; omega
              have hget_r0_raw : scj[(BitVec.toNat (4480 : BitVec 32) +
                  (scj[(BitVec.toNat (15744 : BitVec 32) + off_c.toNat + j_c.toNat) %
                    2 ^ 32]'(by rw [har_mod]; exact hidx_lt)).toNat / 2) %
                  2 ^ 32]'(by rw [h4480_mod]; omega) = r0 := m8_k6_get_congr h4480_mod _ _
              c0_hsplit
              · have hr0_lt : r0.toNat < nc.toNat := by rw [← hget_r0_raw]; exact hc
                clear hc
                let oldr := scj[12672 + r0.toNat]'(by omega)
                have hpr := m8_km_core_or_pres oldr
                have h12672_r_idx : (BitVec.setWidth 64 ((12672 : BitVec 32) +
                    scj[(BitVec.setWidth 64 ((4480 : BitVec 32) +
                      ((scj[(BitVec.setWidth 64 ((15744 : BitVec 32) + off_c +
                        j_c)).toNat]'hidx_c0) >>>
                        (1 : Nat)))).toNat]'h4480_c0)).toNat = 12672 + r0.toNat := by
                  rw [hr0_c0_eq, m8_k6_zext_add_toNat (by
                    rw [show BitVec.toNat (12672 : BitVec 32) = 12672 from rfl]; omega)]
                  rfl
                have h12672_r_c0 : (BitVec.setWidth 64 ((12672 : BitVec 32) +
                    scj[(BitVec.setWidth 64 ((4480 : BitVec 32) +
                      ((scj[(BitVec.setWidth 64 ((15744 : BitVec 32) + off_c +
                        j_c)).toNat]'hidx_c0) >>>
                        (1 : Nat)))).toNat]'h4480_c0)).toNat < scj.length := by
                  rw [h12672_r_idx]; omega
                c0_hsplit
                · clear hc; c0_hsteps!
                  have hm_eq := m8_k6_set_congr (xs := scj) h12672_r_idx
                    (congrArg (· ||| (2147483648 : BitVec 32))
                      (m8_k6_get_congr (xs := scj) h12672_r_idx h12672_r_c0 (by omega)))
                  rw [hm_eq] at hm
                  exact hJr0 (_, true) _
                    ⟨invCore_set_meta hkj hr0_lt
                      (by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hpr.1)
                      (by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hpr.2),
                        hm⟩
                · c0_hsteps!; exact hJr0 (scj, ch_j) mj ⟨hkj, hmj⟩
              · c0_hsteps!; exact hJr0 (scj, ch_j) mj ⟨hkj, hmj⟩
          · c0_hsteps!; exact hJlv (scj, ch_j) mj ⟨hkj, hmj⟩
        · c0_hsteps!; exact hJlv (scj, ch_j) mj ⟨hkj, hmj⟩
    · c0_hsteps!; exact hJelse scj ch_j mj hkj hmj
  · intro Lj hLj; c0_hsteps!
    exact hLj sz_c.toNat (ch_c, 0#32, ()) mc ⟨scc, hkc, Nat.zero_le _, by simp, hmc⟩

private def m8K6CoreLrnLoopExpr (pScr : BitVec 64) (nc off_c sz_c na_c : BitVec 32)
    (ch_c : Bool) (J805 : Cont [.bool]) : Expr Val Cont [] :=
  Expr.group (sig := [[.bool, i32]])
    (fun Js =>
      Blocks.cons
        (fun p =>
          Expr.let_ ⟨OpCode.ult i32, (Arg.var p.snd.fst, Arg.var na_c, ())⟩ fun b =>
          Expr.jnz (Arg.var b.fst)
            (Expr.let_ ⟨OpCode.add i32, (Arg.imm 15744, Arg.var off_c, ())⟩ fun a0 =>
             Expr.let_ ⟨OpCode.add i32, (Arg.var a0.fst, Arg.var sz_c, ())⟩ fun a1 =>
             Expr.let_ ⟨OpCode.add i32, (Arg.var a1.fst, Arg.var p.snd.fst, ())⟩ fun a2 =>
             Expr.let_ ⟨OpCode.zext 32 64, (Arg.var a2.fst, ())⟩ fun a3 =>
             Expr.let_ ⟨OpCode.mul i64, (Arg.var a3.fst, Arg.imm 4, ())⟩ fun a4 =>
             Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var a4.fst, ())⟩ fun a5 =>
             Expr.load i32 (Arg.var a5.fst) fun ant =>
             Expr.group (sig := [[.bool]])
               (fun _ =>
                 Blocks.cons
                   (fun p2 =>
                     Expr.let_ ⟨OpCode.add i32, (Arg.var p.snd.fst, Arg.imm 1, ())⟩ fun nj =>
                     Expr.jump Js.fst (Arg.var p2.fst, Arg.var nj.fst, ()))
                   Blocks.nil)
               (fun Jant =>
                 Expr.let_ ⟨OpCode.ult i32, (Arg.var ant, Arg.var nc, ())⟩ fun c1 =>
                 Expr.jnz (Arg.var c1.fst)
                   (Expr.let_ ⟨OpCode.add i32, (Arg.imm 12672, Arg.var ant, ())⟩ fun e0 =>
                    Expr.let_ ⟨OpCode.zext 32 64, (Arg.var e0.fst, ())⟩ fun e1 =>
                    Expr.let_ ⟨OpCode.mul i64, (Arg.var e1.fst, Arg.imm 4, ())⟩ fun e2 =>
                    Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var e2.fst, ())⟩ fun e3 =>
                    Expr.load i32 (Arg.var e3.fst) fun ld2 =>
                    Expr.let_ ⟨OpCode.and i32, (Arg.var ld2, Arg.imm 2147483648, ())⟩ fun e4 =>
                    Expr.let_ ⟨OpCode.eq i32, (Arg.var e4.fst, Arg.imm 0, ())⟩ fun c2 =>
                    Expr.jnz (Arg.var c2.fst)
                      (Expr.let_ ⟨OpCode.add i32, (Arg.imm 12672, Arg.var ant, ())⟩ fun f0 =>
                       Expr.let_ ⟨OpCode.zext 32 64, (Arg.var f0.fst, ())⟩ fun f1 =>
                       Expr.let_ ⟨OpCode.mul i64, (Arg.var f1.fst, Arg.imm 4, ())⟩ fun f2 =>
                       Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var f2.fst, ())⟩ fun f3 =>
                       Expr.let_ ⟨OpCode.add i32, (Arg.imm 12672, Arg.var ant, ())⟩ fun g0 =>
                       Expr.let_ ⟨OpCode.zext 32 64, (Arg.var g0.fst, ())⟩ fun g1 =>
                       Expr.let_ ⟨OpCode.mul i64, (Arg.var g1.fst, Arg.imm 4, ())⟩ fun g2 =>
                       Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var g2.fst, ())⟩ fun g3 =>
                       Expr.load i32 (Arg.var g3.fst) fun ld3 =>
                       Expr.let_ ⟨OpCode.or i32, (Arg.var ld3, Arg.imm 2147483648, ())⟩ fun g4 =>
                       Expr.store (Arg.var g4.fst) (Arg.var f3.fst)
                         (Expr.jump Jant.fst (Arg.imm true, ())))
                      (Expr.jump Jant.fst (Arg.var p.fst, ())))
                   (Expr.jump Jant.fst (Arg.var p.fst, ()))))
            (Expr.jump J805 (Arg.var p.fst, ())))
        Blocks.nil)
    (fun Js => Expr.jump Js.fst (Arg.var ch_c, Arg.imm 0, ()))

private theorem m8_k6_core_lrn_loop_wp {Γ : Env} {pScr : BitVec 64}
    {scr scc : List (BitVec 32)} {R' : Mem 64 → Prop} {Q : Post []} {X : XPost}
    {nc acap off_c sz_c na_c : BitVec 32} {ch_c : Bool} {J805 : Cont [.bool]} {mc : Mem 64}
    (hlen_ge : 15744 ≤ scr.length) (hnc_le : nc.toNat ≤ 1024)
    (hoff_na : off_c.toNat + sz_c.toNat + na_c.toNat ≤ acap.toNat)
    (hlt_ge : 15744 + acap.toNat ≤ scc.length) (hlt : scc.length < 2 ^ 30)
    (hkc : M8CoreInv scr nc scc)
    (hmc : (array (t := i32) pScr scc ⋆ R') mc)
    (hJ805 : ∀ sc' ch' m', M8CoreInv scr nc sc' →
      (array (t := i32) pScr sc' ⋆ R') m' → J805 (ch', ()) m') :
    wp Γ Q X (m8K6CoreLrnLoopExpr pScr nc off_c sz_c na_c ch_c J805) mc := by
  have invCore_set_meta := @m8CoreInv_set_meta scr nc hnc_le
  have hkc_l := hkc.2.1
  unfold m8K6CoreLrnLoopExpr
  refine wp_loop_group (ts := [.bool, i32])
    (fun remj (_chj, j_c, ()) mj2 => ∃ scj2, M8CoreInv scr nc scj2 ∧
      j_c.toNat ≤ na_c.toNat ∧ remj = na_c.toNat - j_c.toNat ∧
      (array (t := i32) pScr scj2 ⋆ R') mj2)
    ?_ ?_
  · rintro Lj remj ⟨ch_j, j_c, ⟨⟩⟩ mj2 hLj ⟨scj2, hkj2, hj_le, rfl, hmj2⟩
    have hkj2_l := hkj2.2.1
    c0_hsplit
    · have hj_lt : j_c.toNat < na_c.toNat := hc; clear hc
      have hj1 : (j_c + 1#32).toNat = j_c.toNat + 1 := by c0_bound
      have hidx_lt : 15744 + off_c.toNat + sz_c.toNat + j_c.toNat < scj2.length := by omega
      have hidx_eq : (BitVec.setWidth 64 ((15744 : BitVec 32) + off_c + sz_c + j_c)).toNat =
          15744 + off_c.toNat + sz_c.toNat + j_c.toNat := by
        rw [m8_k6_zext_add_toNat (by
          rw [BitVec.toNat_add, BitVec.toNat_add,
            show BitVec.toNat (15744 : BitVec 32) = 15744 from rfl,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)]
        rw [BitVec.toNat_add, BitVec.toNat_add,
          show BitVec.toNat (15744 : BitVec 32) = 15744 from rfl,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have hidx_c0 : (BitVec.setWidth 64 ((15744 : BitVec 32) + off_c + sz_c + j_c)).toNat <
          scj2.length := by rw [hidx_eq]; exact hidx_lt
      let ant := scj2[15744 + off_c.toNat + sz_c.toNat + j_c.toNat]'hidx_lt
      have hant_c0_eq : scj2[(BitVec.setWidth 64 ((15744 : BitVec 32) + off_c + sz_c +
          j_c)).toNat]'hidx_c0 = ant := m8_k6_get_congr hidx_eq hidx_c0 hidx_lt
      c0_hsteps_nogrp
      refine wp_join_state1 (t := .bool) (α := List (BitVec 32) × Bool) (fun x => x.2)
        (fun x mj3 => M8CoreInv scr nc x.1 ∧ (array (t := i32) pScr x.1 ⋆ R') mj3)
        ?_ ?_
      · rintro _ ⟨scj3, chj3⟩ mj3 ⟨hkj3, hmj3⟩
        c0_hsteps!
        exact hLj (na_c.toNat - (j_c + 1#32).toNat) (chj3, j_c + 1#32, ()) mj3 (by omega)
          ⟨scj3, hkj3, by omega, rfl, hmj3⟩
      · intro Jant hJant
        have har_mod : (BitVec.toNat (15744 : BitVec 32) + off_c.toNat + sz_c.toNat +
            j_c.toNat) % 2 ^ 32 = 15744 + off_c.toNat + sz_c.toNat + j_c.toNat := by
          rw [show BitVec.toNat (15744 : BitVec 32) = 15744 from rfl]; omega
        have hget_ant : scj2[(BitVec.toNat (15744 : BitVec 32) + off_c.toNat + sz_c.toNat +
            j_c.toNat) % 2 ^ 32]'(by rw [har_mod]; exact hidx_lt) = ant :=
          m8_k6_get_congr har_mod _ hidx_lt
        c0_hsplit
        · have hant_lt : ant.toNat < nc.toNat := by rw [← hget_ant]; exact hc
          clear hc
          let olda := scj2[12672 + ant.toNat]'(by omega)
          have hpa := m8_km_core_or_pres olda
          have h12672_a_idx : (BitVec.setWidth 64 ((12672 : BitVec 32) +
              scj2[(BitVec.setWidth 64 ((15744 : BitVec 32) + off_c + sz_c +
                j_c)).toNat]'hidx_c0)).toNat = 12672 + ant.toNat := by
            rw [hant_c0_eq, m8_k6_zext_add_toNat (by
              rw [show BitVec.toNat (12672 : BitVec 32) = 12672 from rfl]; omega)]
            rfl
          have h12672_a_c0 : (BitVec.setWidth 64 ((12672 : BitVec 32) +
              scj2[(BitVec.setWidth 64 ((15744 : BitVec 32) + off_c + sz_c +
                j_c)).toNat]'hidx_c0)).toNat < scj2.length := by rw [h12672_a_idx]; omega
          c0_hsplit
          · clear hc; c0_hsteps!
            have hm_eq := m8_k6_set_congr (xs := scj2) h12672_a_idx
              (congrArg (· ||| (2147483648 : BitVec 32))
                (m8_k6_get_congr (xs := scj2) h12672_a_idx h12672_a_c0 (by omega)))
            rw [hm_eq] at hm
            exact hJant (_, true) _
              ⟨invCore_set_meta hkj2 hant_lt
                (by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hpa.1)
                (by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hpa.2), hm⟩
          · c0_hsteps!; exact hJant (scj2, ch_j) mj2 ⟨hkj2, hmj2⟩
        · c0_hsteps!; exact hJant (scj2, ch_j) mj2 ⟨hkj2, hmj2⟩
    · c0_hsteps!; exact hJ805 scj2 ch_j mj2 hkj2 hmj2
  · intro Lj hLj; c0_hsteps!
    exact hLj na_c.toNat (ch_c, 0#32, ()) mc ⟨scc, hkc, Nat.zero_le _, by simp, hmc⟩

private theorem m8_k6_core_fixpoint_wp {Γ : Env} {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {Q : Post []} {X : XPost}
    {nc nv acap : BitVec 32}
    (hscr_len : s.scratch.scratch_buf.length = c.scratch_cap)
    (hsc16 : 16384 ≤ c.scratch_cap) (hok0 : M8K6BufOk s.scratch.scratch_buf)
    (hnc_def : nc = s.scratch.scratch_buf[4193]'(by rw [hscr_len]; omega))
    (_hnv_def : nv = s.scratch.scratch_buf[4192]'(by rw [hscr_len]; omega))
    (hacap_def : acap = s.scratch.scratch_buf[4207]'(by rw [hscr_len]; omega))
    (hnc_le : nc.toNat ≤ 1024) (hnv_le : nv.toNat ≤ 256)
    (hQ : ∀ scr' m', scr'.length = c.scratch_cap →
      (∀ idx < c.scratch_cap, (idx < 5760 ∨ (6016 ≤ idx ∧ idx < 12672) ∨ 13696 ≤ idx) →
        scr'[idx]? = s.scratch.scratch_buf[idx]?) →
      M8K6BufOk scr' →
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
      Q () m')
    {scj : List (BitVec 32)} {mj : Mem 64}
    (hkj : M8CoreInv s.scratch.scratch_buf nc scj)
    (hmj : (FullMem c { s with scratch := { s.scratch with scratch_buf := scj } } ⋆ R) mj) :
    wp Γ Q X (m8K6FixpointE c.hdr c.pScratchBuf nc nv acap) mj := by
  have hsc := c.hscr; unfold dimacsBound at hsc
  let scr := s.scratch.scratch_buf
  have hscr_l : scr.length = c.scratch_cap := hscr_len
  have hlen_ge := hok0.base_ge
  let invCore := M8CoreInv scr nc
  have invCore_set_meta := @m8CoreInv_set_meta scr nc hnc_le
  let R' : Mem 64 → Prop := m8FullMemNoScr c s ⋆ R
  have hmj' : (array (t := i32) c.pScratchBuf scj ⋆ R') mj := by
    rw [m8_fullMem_eq_scr, sep_assoc] at hmj; exact hmj
  clear hmj
  dsimp only [m8K6FixpointE, m8K6SLd64, m8K6SLd32, m8K6SJF, m8K6SGrpB, m8K6DfltT, m8K6Dflt]
  {
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32, .bool])
    (fun rem (pass, _ch, ()) mp => ∃ scp, invCore scp ∧ pass.toNat ≤ nc.toNat ∧
      rem = nc.toNat - pass.toNat ∧
      (array (t := i32) c.pScratchBuf scp ⋆ R') mp)
    ?_ ?_
  ·
      rintro Lp remp ⟨pass, ch, ⟨⟩⟩ mp hLp ⟨scp, hkp, hpass_le, rfl, hmp⟩
      c0_hsplit
      · clear hc
        c0_hsplit
        · have hpass_lt : pass.toNat < nc.toNat := hc; clear hc
          have hpass1 : (pass + 1#32).toNat = pass.toNat + 1 := by c0_bound
          c0_hsteps_nogrp
          refine wp_loop_group (ts := [.bool, i32])
            (fun rem (_chc, cid_c, ()) mc => ∃ scc, invCore scc ∧
              cid_c.toNat ≤ nc.toNat ∧ rem = cid_c.toNat ∧
              (array (t := i32) c.pScratchBuf scc ⋆ R') mc)
            ?_ ?_
          · rintro Lc remc ⟨ch_c, cid_c, ⟨⟩⟩ mc hLc ⟨scc, hkc, hc_le, rfl, hmc⟩
            have hkc_l := hkc.2.1
            c0_hsplit
            · have hcid_pos : 0 < cid_c.toNat := hc; clear hc
              have hcid1_lt : (cid_c - 1#32).toNat < nc.toNat := by
                rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
              let c_i := cid_c - 1#32
              have hc_i_lt : c_i.toNat < nc.toNat := hcid1_lt
              have hbd_c : 12672 + c_i.toNat < scc.length := by omega
              have hc_12672_idx : (BitVec.setWidth 64
                  ((12672 : BitVec 32) + (cid_c - (1 : BitVec 32)))).toNat =
                  12672 + c_i.toNat := by
                rw [m6_zext32_toNat]; dsimp only [c_i]; c0_bound
              have hbd_c_c0 : (BitVec.setWidth 64
                  ((12672 : BitVec 32) + (cid_c - (1 : BitVec 32)))).toNat <
                  scc.length := by
                rw [hc_12672_idx]; exact hbd_c
              let cm := scc[12672 + c_i.toNat]'hbd_c
              have hget_12672_c0 : scc[(BitVec.setWidth 64
                  ((12672 : BitVec 32) + (cid_c - (1 : BitVec 32)))).toNat]'hbd_c_c0 =
                  cm := m8_k6_get_congr hc_12672_idx hbd_c_c0 hbd_c
              c0_hsteps_nogrp
              refine wp_join_state1 (t := .bool) (α := List (BitVec 32) × Bool)
                (fun x => x.2)
                (fun x mc' => invCore x.1 ∧
                  (array (t := i32) c.pScratchBuf x.1 ⋆ R') mc')
                (fun _ ⟨scc', ch'⟩ mc' ⟨hkc', hmc'⟩ => by
                  c0_hsteps!
                  exact hLc (cid_c - 1#32).toNat (ch', cid_c - 1#32, ()) mc'
                    (by rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega)
                    ⟨scc', hkc', by omega, rfl, hmc'⟩)
                (fun Jcid hJcid => by
                  have hbd_off : 11648 + c_i.toNat < scc.length := by omega
                  have hc_11648_idx : (BitVec.setWidth 64
                      ((11648 : BitVec 32) + (cid_c - (1 : BitVec 32)))).toNat =
                      11648 + c_i.toNat := by
                    rw [m6_zext32_toNat]; dsimp only [c_i]; c0_bound
                  have hbd_off_c0 : (BitVec.setWidth 64
                      ((11648 : BitVec 32) + (cid_c - (1 : BitVec 32)))).toNat <
                      scc.length := by
                    rw [hc_11648_idx]; exact hbd_off
                  c0_hsplit
                  · clear hc
                    let off_c := scc[11648 + c_i.toNat]'hbd_off
                    have hget_11648_c0 : scc[(BitVec.setWidth 64
                        ((11648 : BitVec 32) + (cid_c - (1 : BitVec 32)))).toNat]'hbd_off_c0 =
                        off_c := m8_k6_get_congr hc_11648_idx hbd_off_c0 hbd_off
                    let sz_c := cm &&& 0xFFFF#32
                    have hlt := hkc.1.length_lt
                    have h15_eq : scc[4207]'(by omega) = acap := by
                      have h15 := hkc.2.2.1 4207 (by omega) (Or.inl (by omega))
                      rw [List.getElem?_eq_getElem (by omega),
                        List.getElem?_eq_getElem (by omega)] at h15
                      exact (Option.some.inj h15).trans hacap_def.symm
                    have h1' : scc[4193]'(by omega) = nc := by
                      have h1eq := hkc.2.2.1 4193 (by omega) (Or.inl (by omega))
                      rw [List.getElem?_eq_getElem (by omega),
                        List.getElem?_eq_getElem (by omega)] at h1eq
                      exact (Option.some.inj h1eq).trans hnc_def.symm
                    have hkcl := hkc.1.clause_ok (by
                      rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
                        h1']; exact hc_i_lt)
                    have hlt_ge := hkc.1.length_ge
                    rw [List.getElem?_eq_getElem (by omega : 4207 < scc.length),
                      Option.getD_some, h15_eq] at hlt_ge
                    rw [List.getElem?_eq_getElem (by omega : 11648 + c_i.toNat < scc.length),
                      List.getElem?_eq_getElem (by omega : 12672 + c_i.toNat < scc.length),
                      List.getElem?_eq_getElem (by omega : 13696 + c_i.toNat < scc.length),
                      List.getElem?_eq_getElem (by omega : 4207 < scc.length),
                      Option.getD_some, Option.getD_some, Option.getD_some, Option.getD_some,
                      h15_eq] at hkcl
                    have hci_sub1_eq : (cid_c - 1#32).toNat = cid_c.toNat - 1 := by
                      rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
                    have hno_ov1 : off_c.toNat + sz_c.toNat < 2 ^ 30 := by
                      dsimp only [off_c, sz_c, cm] at *
                      have := hkcl.1; have := hkc.1.length_lt; omega
                    c0_hsteps_nogrp
                    refine wp_join_state1 (t := .bool) (α := List (BitVec 32) × Bool)
                      (fun x => x.2)
                      (fun x mc' => invCore x.1 ∧
                        (array (t := i32) c.pScratchBuf x.1 ⋆ R') mc')
                      (fun _ ⟨scc', ch'⟩ mc' ⟨hkc', hmc'⟩ => by
                        c0_hsteps!; exact hJcid (scc', ch') mc' ⟨hkc', hmc'⟩)
                      (fun Jbr hJbr => by
                        c0_hsplit
                        · have hlrn_cm : (cm &&& 0x40000000#32) ≠ 0#32 := by
                            have hwrap : (BitVec.toNat (12672 : BitVec 32) +
                                (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + cid_c.toNat)) % 2 ^ 32 =
                                12672 + c_i.toNat := by
                              dsimp only [c_i]; rw [hci_sub1_eq,
                                show BitVec.toNat (12672 : BitVec 32) = 12672 from rfl,
                                show BitVec.toNat (1 : BitVec 32) = 1 from rfl]; omega
                            have hcm_c0 : scc[(BitVec.toNat (12672 : BitVec 32) +
                                (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + cid_c.toNat)) % 2 ^ 32]'(by
                                  rw [hwrap]; exact hbd_c) = cm :=
                              m8_k6_get_congr hwrap _ hbd_c
                            rw [hcm_c0] at hc; exact hc
                          clear hc
                          have hbd_aux : 13696 + c_i.toNat < scc.length := by omega
                          let na_c := scc[13696 + c_i.toNat]'hbd_aux
                          have hoff_na' : off_c.toNat + sz_c.toNat + na_c.toNat ≤ acap.toNat :=
                            hkcl.2 hlrn_cm
                          have hno_ov2 : off_c.toNat + sz_c.toNat + na_c.toNat < 2 ^ 30 := by
                            have := hkc.1.length_lt; omega
                          c0_hsteps_nogrp
                          refine wp_join_state1 (t := .bool) (α := List (BitVec 32) × Bool)
                            (fun x => x.2)
                            (fun x mc' => invCore x.1 ∧
                              (array (t := i32) c.pScratchBuf x.1 ⋆ R') mc')
                            (fun _ ⟨scc', ch'⟩ mc' ⟨hkc', hmc'⟩ => by
                              c0_hsteps!; exact hJbr (scc', ch') mc' ⟨hkc', hmc'⟩)
                            (fun J805 hJ805 => by
                              c0_hsplit
                              · clear hc
                                have hc_13696_idx : (BitVec.setWidth 64 ((13696 : BitVec 32) +
                                    (cid_c - (1 : BitVec 32)))).toNat = 13696 + c_i.toNat := by
                                  rw [m8_k6_zext_add_toNat (by
                                    change BitVec.toNat 13696#32 + (cid_c - 1#32).toNat < 2 ^ 32
                                    rw [show BitVec.toNat 13696#32 = 13696 from rfl,
                                      hci_sub1_eq]; omega)]
                                  rw [show BitVec.toNat (13696 : BitVec 32) = 13696 from rfl]; rfl
                                have hbd_aux_c0 : (BitVec.setWidth 64 ((13696 : BitVec 32) +
                                    (cid_c - (1 : BitVec 32)))).toNat < scc.length := by
                                  rw [hc_13696_idx]; exact hbd_aux
                                have hget_13696_c0 : scc[(BitVec.setWidth 64 ((13696 : BitVec 32) +
                                    (cid_c - (1 : BitVec 32)))).toNat]'hbd_aux_c0 = na_c :=
                                  m8_k6_get_congr hc_13696_idx hbd_aux_c0 hbd_aux
                                have hoff_na2 :
                                    (scc[(BitVec.setWidth 64 ((11648 : BitVec 32) +
                                      (cid_c - (1 : BitVec 32)))).toNat]'hbd_off_c0).toNat +
                                    ((scc[(BitVec.setWidth 64 ((12672 : BitVec 32) +
                                      (cid_c - (1 : BitVec 32)))).toNat]'hbd_c_c0) &&&
                                      (65535 : BitVec 32)).toNat +
                                    (scc[(BitVec.setWidth 64 ((13696 : BitVec 32) +
                                      (cid_c - (1 : BitVec 32)))).toNat]'hbd_aux_c0).toNat ≤
                                    acap.toNat := by
                                  rw [hget_11648_c0, hget_12672_c0, hget_13696_c0]; exact hoff_na'
                                c0_hsteps_nogrp
                                exact m8_k6_core_lrn_loop_wp hlen_ge hnc_le hoff_na2 hlt_ge hlt
                                  hkc hmc
                                  (fun sc' ch' m' hk' hm' => hJ805 (sc', ch') m' ⟨hk', hm'⟩)
                              · c0_hsteps!; exact hJ805 (scc, ch_c) mc ⟨hkc, hmc⟩)
                        · clear hc; c0_hsteps_nogrp
                          refine wp_join_state1 (t := .bool) (α := List (BitVec 32) × Bool)
                            (fun x => x.2)
                            (fun x mc' => invCore x.1 ∧
                              (array (t := i32) c.pScratchBuf x.1 ⋆ R') mc')
                            (fun _ ⟨scc', ch'⟩ mc' ⟨hkc', hmc'⟩ => by
                              c0_hsteps!; exact hJbr (scc', ch') mc' ⟨hkc', hmc'⟩)
                            (fun Jelse hJelse => by
                              c0_hsplit
                              · clear hc
                                have hoff_sz : off_c.toNat + sz_c.toNat ≤ acap.toNat := hkcl.1
                                have hsz_lt : sz_c.toNat < 65536 := by
                                  dsimp only [sz_c]; rw [BitVec.toNat_and]
                                  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
                                have hsz_lt2 :
                                    ((scc[(BitVec.setWidth 64 ((12672 : BitVec 32) +
                                      (cid_c - (1 : BitVec 32)))).toNat]'hbd_c_c0) &&&
                                      (65535 : BitVec 32)).toNat < 65536 := by
                                  rw [hget_12672_c0]; exact hsz_lt
                                have hoff_sz2 :
                                    (scc[(BitVec.setWidth 64 ((11648 : BitVec 32) +
                                      (cid_c - (1 : BitVec 32)))).toNat]'hbd_off_c0).toNat +
                                    ((scc[(BitVec.setWidth 64 ((12672 : BitVec 32) +
                                      (cid_c - (1 : BitVec 32)))).toNat]'hbd_c_c0) &&&
                                      (65535 : BitVec 32)).toNat ≤ acap.toNat := by
                                  rw [hget_11648_c0, hget_12672_c0]; exact hoff_sz
                                c0_hsteps_nogrp
                                exact m8_k6_core_orig_loop_wp hlen_ge hnc_le hnv_le hsz_lt2
                                  hoff_sz2 hlt_ge hlt hkc hmc
                                  (fun sc' ch' m' hk' hm' => hJelse (sc', ch') m' ⟨hk', hm'⟩)
                              · c0_hsteps!; exact hJelse (scc, ch_c) mc ⟨hkc, hmc⟩))
                  · c0_hsteps!; exact hJcid (scc, ch_c) mc ⟨hkc, hmc⟩)
            · c0_hsteps!; exact hLp (nc.toNat - (pass + 1#32).toNat)
                (pass + 1#32, ch_c, ()) mc (by omega) ⟨scc, hkc, by omega, rfl, hmc⟩
          · intro Lc hLc; c0_hsteps!
            exact hLc nc.toNat (false, nc, ()) mp ⟨scp, hkp, Nat.le_refl _, rfl, hmp⟩
        · c0_hsteps!; exact hQ scp mp (by rw [hkp.2.1, hscr_l]) (fun idx hi hor =>
            hkp.2.2.1 idx (hscr_l.symm ▸ hi) hor) hkp.1 (by
              rw [m8_fullMem_eq_scr, sep_assoc]; exact hmp)
      · c0_hsteps!; exact hQ scp mp (by rw [hkp.2.1, hscr_l]) (fun idx hi hor =>
          hkp.2.2.1 idx (hscr_l.symm ▸ hi) hor) hkp.1 (by
            rw [m8_fullMem_eq_scr, sep_assoc]; exact hmp)
  · intro Lp hLp
    rw [wp_jump]
    exact hLp nc.toNat (0#32, true, ()) mj ⟨scj, hkj, Nat.zero_le _, by simp, hmj'⟩
  }

/-- Parametric `Func.wp` proof for `full_k6_core_m8`. -/
theorem full_k6_core_m8_wp (Γ : Env) :
    ∀ a m Q X, m8K6CoreSpec a m Q X →
      Func.wp Γ full_k6_core_m8_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, s, R, rfl, hlen, hsc16, hok0, hm0, hQ⟩ := m8K6CoreSpec_elim hSpec
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  have hsc := c.hscr; unfold dimacsBound at hsc
  let scr := s.scratch.scratch_buf
  have hscr_l : scr.length = c.scratch_cap := hscr_len
  have hlen_ge := hok0.base_ge
  have h4192 := m8_scr_imm_lt hscr_len hsc16 (k := 4192) (by decide)
  have h4193 := m8_scr_imm_lt hscr_len hsc16 (k := 4193) (by decide)
  have h4207 := m8_scr_imm_lt hscr_len hsc16 (k := 4207) (by decide)
  let nc := scr[4193]'(by rw [hscr_l]; omega)
  let nv := scr[4192]'(by rw [hscr_l]; omega)
  let acap := scr[4207]'(by rw [hscr_l]; omega)
  unfold Func.wp full_k6_core_m8_body
  c0_hsplit
  · c0_hsteps!; exact hQ scr m0 hscr_len (fun _ _ _ => rfl) hok0 hm0
  · have hnc_le : nc.toNat ≤ 1024 := Nat.le_of_not_lt (show ¬1024 < nc.toNat from by simpa [nc,
      scr] using hc)
    clear hc
    c0_hsplit
    · c0_hsteps!; exact hQ scr m0 hscr_len (fun _ _ _ => rfl) hok0 hm0
    · have hnv_le : nv.toNat ≤ 256 := Nat.le_of_not_lt (show ¬256 < nv.toNat from by simpa [nv,
        scr] using hc)
      clear hc
      let invCore := M8CoreInv scr nc
      have invCore_set_meta := @m8CoreInv_set_meta scr nc hnc_le
      have invCore_set_flags := @m8CoreInv_set_flags scr nc
      let R' : Mem 64 → Prop := m8FullMemNoScr c s ⋆ R
      have hm0' : (array (t := i32) c.pScratchBuf scr ⋆ R') m0 := by
        have h := hm0
        change (FullMem c { s with scratch := { s.scratch with scratch_buf := scr } } ⋆ R) m0 at h
        rw [m8_fullMem_eq_scr, sep_assoc] at h; exact h
      c0_hsteps_nogrp
      refine wp_loop_group (ts := [i32])
        (fun rem (i, ()) mi => ∃ scri, invCore scri ∧ i.toNat ≤ nc.toNat ∧
          rem = nc.toNat - i.toNat ∧
          (array (t := i32) c.pScratchBuf scri ⋆ R') mi)
        ?_ ?_
      · rintro L1 rem1 ⟨i1, ⟨⟩⟩ m1 hL1 ⟨sc1, hk1, hi1_le, rfl, hm1⟩
        have hk1_l := hk1.2.1
        c0_hsplit
        · have hi1_lt : i1.toNat < nc.toNat := hc; clear hc
          have hi1_succ : (i1 + 1#32).toNat = i1.toNat + 1 := by c0_bound
          have hbd1 : 12672 + i1.toNat < sc1.length := by omega
          let oldm := sc1[12672 + i1.toNat]'hbd1
          have hpres := m8_km_core_clear_pres oldm
          have hidx1 : ((12672#32 + i1).setWidth 64).toNat = 12672 + i1.toNat := by c0_bound
          have hbd1' : ((12672#32 + i1).setWidth 64).toNat < sc1.length := by rw [hidx1]; exact hbd1
          c0_hsteps!
          refine hL1 (nc.toNat - (i1 + 1#32).toNat) (i1 + 1#32, ()) _ (by omega)
            ⟨_, ?_, by omega, rfl, hm⟩
          · have hidx1' : (BitVec.setWidth 64 (12672 + i1)).toNat = 12672 + i1.toNat := hidx1
            have hset_congr :
              sc1.set ((12672 + i1).setWidth 64).toNat
                ((sc1[((12672 + i1).setWidth 64).toNat]'hbd1') &&& ~~~(2147483648 : BitVec 32)) =
                sc1.set (12672 + i1.toNat) (oldm &&& ~~~(2147483648 : BitVec 32)) := by
              apply List.ext_getElem (by simp)
              intro k hk1' hk2'
              simp only [List.getElem_set, hidx1']
              split <;> rfl
            change invCore
              (sc1.set ((12672 + i1).setWidth 64).toNat
                ((sc1[((12672 + i1).setWidth 64).toNat]'hbd1') &&& ~~~(2147483648 : BitVec 32)))
            rw [hset_congr]
            exact invCore_set_meta hk1 hi1_lt
              (by rw [List.getElem?_eq_getElem hbd1, Option.getD_some]; simpa [oldm] using hpres.1)
              (by rw [List.getElem?_eq_getElem hbd1, Option.getD_some]; simpa [oldm] using hpres.2)
        · have hi1_nc : i1 = nc := BitVec.eq_of_toNat_eq (by
            have : ¬i1.toNat < nc.toNat := hc; omega)
          clear hc
          have h4199_1 : (4199#64).toNat < sc1.length := by
            rw [hk1_l, show (4199#64).toNat = 4199 from rfl]; omega
          c0_hsteps_nogrp
          refine wp_join_state1 (t := i32) (α := List (BitVec 32) × BitVec 32)
            (fun x => x.2)
            (fun x mj => invCore x.1 ∧
              (array (t := i32) c.pScratchBuf x.1 ⋆ R') mj)
            ?_ ?_
          · rintro _ ⟨scj, _⟩ mj ⟨hkj, hmj⟩
            exact m8_k6_core_fixpoint_wp hscr_len hsc16 hok0 rfl rfl rfl hnc_le hnv_le hQ hkj
              (by rw [m8_fullMem_eq_scr, sep_assoc]; exact hmj)
          ·
              intro Jinc hJinc
              let inc := sc1[4199]'(by omega)
              c0_hsplit
              · have hinc : inc.toNat < nc.toNat := hc; clear hc
                refine wp_loop_group (ts := [i32])
                  (fun rem (i, ()) mf => ∃ scf, invCore scf ∧ i.toNat ≤ nv.toNat ∧
                    rem = nv.toNat - i.toNat ∧
                    (array (t := i32) c.pScratchBuf scf ⋆ R') mf)
                  ?_ ?_
                · rintro Lf remf ⟨if1, ⟨⟩⟩ mf1 hLf ⟨scf1, hkf1, hif1, rfl, hmf1⟩
                  have hkf1_l := hkf1.2.1
                  c0_hsplit
                  · have hi_lt : if1.toNat < nv.toNat := hc; clear hc
                    have hif1_s : (if1 + 1#32).toNat = if1.toNat + 1 := by c0_bound
                    have h5760_eq : (BitVec.setWidth 64 ((5760 : BitVec 32) + if1)).toNat = 5760 +
                      if1.toNat := by
                      rw [m6_zext32_toNat, BitVec.toNat_add,
                        show (5760 : BitVec 32).toNat = 5760 from rfl, Nat.mod_eq_of_lt (by omega)]
                    c0_hsteps!
                    rw [m8_k6_set_congr h5760_eq rfl] at hm
                    exact hLf (nv.toNat - (if1 + 1#32).toNat) (if1 + 1#32, ()) _ (by omega)
                      ⟨_, invCore_set_flags hkf1 (v := if1.toNat) (by omega) _, by omega, rfl, hm⟩
                  · have h1eq := hkf1.2.2.1 4193 (by omega) (Or.inl (by omega))
                    rw [List.getElem?_eq_getElem (by omega),
                      List.getElem?_eq_getElem (by omega)] at h1eq
                    have hnc_e : scf1[4193]'(by omega) = nc := Option.some.inj h1eq
                    have hkb_inc := hkf1.1.clause_ok (by
                      rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hnc_e]; exact hinc)
                    clear hc
                    let oldmi := scf1[12672 + inc.toNat]'(by omega)
                    have hpmi := m8_km_core_or_pres oldmi
                    have h15_eq : scf1[4207]'(by omega) = acap := by
                      have := hkf1.2.2.1 4207 (by omega) (Or.inl (by omega))
                      rw [List.getElem?_eq_getElem (by omega),
                        List.getElem?_eq_getElem (by omega)] at this
                      exact Option.some.inj this
                    have hlt_ge_f := hkf1.1.length_ge
                    rw [List.getElem?_eq_getElem (by omega : 4207 < scf1.length),
                      Option.getD_some, h15_eq] at hlt_ge_f
                    have hinc_sz_nw : (scf1[11648 + inc.toNat]'(by omega)).toNat +
                        ((oldmi ||| 0x80000000#32) &&& 0xFFFF#32).toNat < 2 ^ 30 := by
                      rw [List.getElem?_eq_getElem (by omega : 11648 + inc.toNat < scf1.length),
                        List.getElem?_eq_getElem (by omega : 12672 + inc.toNat < scf1.length),
                        List.getElem?_eq_getElem (by omega : 4207 < scf1.length),
                        Option.getD_some, Option.getD_some, Option.getD_some, h15_eq] at hkb_inc
                      dsimp only [oldmi] at hpmi ⊢; rw [hpmi.1]; have := hkf1.1.length_lt; omega
                    have h4199_sc1 : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 4199)).toNat <
                        sc1.length := by
                      change 4199 % 2 ^ 64 < sc1.length; omega
                    have h12672_inc_eq : (BitVec.setWidth 64 ((12672 : BitVec 32) +
                        sc1[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat
                          4199)).toNat]'h4199_sc1)).toNat =
                        12672 + inc.toNat := by
                      change ((12672#32 + inc).setWidth 64).toNat = 12672 + inc.toNat
                      rw [m6_zext32_toNat]; c0_bound
                    have h11648_inc_eq : (BitVec.setWidth 64 ((11648 : BitVec 32) +
                        sc1[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat
                          4199)).toNat]'h4199_sc1)).toNat =
                        11648 + inc.toNat := by
                      change ((11648#32 + inc).setWidth 64).toNat = 11648 + inc.toNat
                      rw [m6_zext32_toNat]; c0_bound
                    have h12672_inc : (BitVec.setWidth 64 ((12672 : BitVec 32) +
                        sc1[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat
                          4199)).toNat]'h4199_sc1)).toNat <
                        scf1.length := by
                      rw [h12672_inc_eq]; omega
                    have h11648_inc : (BitVec.setWidth 64 ((11648 : BitVec 32) +
                        sc1[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat
                          4199)).toNat]'h4199_sc1)).toNat <
                        scf1.length := by
                      rw [h11648_inc_eq]; omega
                    let off_i := scf1[11648 + inc.toNat]'(by omega)
                    let sz_i := (oldmi ||| 0x80000000#32) &&& 0xFFFF#32
                    c0_hsteps_nogrp
                    have hpmi' : ((oldmi ||| 0x80000000#32) &&& 0xFFFF#32 =
                          (scf1[12672 + inc.toNat]?.getD 0#32) &&& 0xFFFF#32) ∧
                        ((oldmi ||| 0x80000000#32) &&& 0x40000000#32 =
                          (scf1[12672 + inc.toNat]?.getD 0#32) &&& 0x40000000#32) := by
                      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hpmi
                    have hm_s_eq := m8_k6_set_congr (xs := scf1) h12672_inc_eq
                      (congrArg (· ||| (2147483648 : BitVec 32))
                        (m8_k6_get_congr (xs := scf1) h12672_inc_eq h12672_inc (by omega)))
                    rw [hm_s_eq] at hm
                    have hget_raw_off_i : ∀ hbd,
                        (scf1.set (BitVec.setWidth 64 ((12672 : BitVec 32) +
                          sc1[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat
                            4199)).toNat]'h4199_sc1)).toNat
                          (scf1[(BitVec.setWidth 64 ((12672 : BitVec 32) +
                            sc1[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat
                              4199)).toNat]'h4199_sc1)).toNat]'h12672_inc |||
                            (2147483648 : BitVec 32)))[(BitVec.setWidth 64 ((11648 : BitVec 32) +
                          sc1[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat
                            4199)).toNat]'h4199_sc1)).toNat]'hbd = off_i := by
                      intro hbd
                      rw [List.getElem_set_ne (by rw [h12672_inc_eq, h11648_inc_eq]; omega)]
                      exact m8_k6_get_congr h11648_inc_eq _ _
                    simp only [hget_raw_off_i]
                    have hscf1s_ex : ∃ scf1s : List (BitVec 32), invCore scf1s ∧
                        scf1s.length = scr.length ∧
                        scf1s[12672 + inc.toNat]? = some (oldmi ||| 0x80000000#32) ∧
                        (array (t := i32) c.pScratchBuf scf1s ⋆ R') m := by
                      refine ⟨scf1.set (12672 + inc.toNat) (oldmi ||| 0x80000000#32),
                        invCore_set_meta hkf1 hinc hpmi'.1 hpmi'.2, by rw [List.length_set,
                          hkf1_l], ?_, hm⟩
                      rw [List.getElem?_set_self (by omega)]
                    obtain ⟨scf1s, h_scf1s, hk1s_l, h12672_sq, hm_n⟩ := hscf1s_ex
                    clear hm hpmi' hm_s_eq hget_raw_off_i
                    have hm := hm_n; clear hm_n
                    have h12672_inc_s : (BitVec.setWidth 64 ((12672 : BitVec 32) +
                        sc1[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat
                          4199)).toNat]'h4199_sc1)).toNat <
                        scf1s.length := by
                      rw [h12672_inc_eq]; omega
                    have hget_12672_s : scf1s[(BitVec.setWidth 64 ((12672 : BitVec 32) +
                        sc1[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat
                          4199)).toNat]'h4199_sc1)).toNat]'h12672_inc_s =
                        oldmi ||| 0x80000000#32 := by
                      rw [m8_k6_get_congr h12672_inc_eq h12672_inc_s (by omega)]
                      have hbd : 12672 + inc.toNat < scf1s.length := by omega
                      rw [List.getElem?_eq_getElem hbd] at h12672_sq
                      exact Option.some.inj h12672_sq
                    c0_hsteps_nogrp
                    simp only [hget_12672_s]
                    refine wp_join0
                      (fun mj => ∃ scj, invCore scj ∧
                        (array (t := i32) c.pScratchBuf scj ⋆ R') mj)
                      ?_ ?_
                    · rintro _ mj ⟨scj, hkj, hmj⟩
                      have hkj_l := hkj.2.1
                      have h4197 := m8_scr_imm_lt (by rw [hkj_l, hscr_l]) hsc16 (k :=
                        4197) (by decide)
                      c0_hsteps_nogrp
                      refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
                        (fun ti => (ti, ())) (fun ti => ti.toNat ≤ 256)
                        ?_ ?_
                      · rintro _ ti hti
                        c0_hsteps_nogrp
                        refine wp_loop_group (ts := [i32])
                          (fun rem (tic, ()) mt => ∃ sct, invCore sct ∧ tic.toNat ≤ 256 ∧
                            rem = tic.toNat ∧
                            (array (t := i32) c.pScratchBuf sct ⋆ R') mt)
                          ?_ ?_
                        · rintro Lt remt ⟨tic, ⟨⟩⟩ mt hLt ⟨sct, hkt, htic, rfl, hmt⟩
                          have hkt_l := hkt.2.1
                          c0_hsplit
                          · have ht_pos : 0 < tic.toNat := hc; clear hc
                            let t1 := tic - 1#32
                            have ht1_lt : t1.toNat < 256 := by
                              dsimp only [t1]; rw [BitVec.toNat_sub]; simp only
                                [BitVec.toNat_ofNat]; omega
                            have ht1_dec : t1.toNat < tic.toNat := by
                              dsimp only [t1]; rw [BitVec.toNat_sub]; simp only
                                [BitVec.toNat_ofNat]; omega
                            have ht_5504_mod : (BitVec.toNat (5504 : BitVec 32) +
                                (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + tic.toNat)) %
                                2 ^ 32 = 5504 + t1.toNat := by
                              have hsub : t1.toNat = tic.toNat - 1 := by
                                dsimp only [t1]; rw [BitVec.toNat_sub]
                                simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
                              rw [hsub, show BitVec.toNat (5504 : BitVec 32) = 5504 from rfl,
                                show BitVec.toNat (1 : BitVec 32) = 1 from rfl]; omega
                            have ht_5504_c0 : (BitVec.setWidth 64
                                ((5504 : BitVec 32) + (tic - (1 : BitVec 32)))).toNat =
                                5504 + t1.toNat := by
                              change ((5504#32 + t1).setWidth 64).toNat = 5504 + t1.toNat
                              rw [m6_zext32_toNat]; c0_bound
                            have ht_5504_bd_c0 : (BitVec.setWidth 64
                                ((5504 : BitVec 32) + (tic - (1 : BitVec 32)))).toNat <
                                sct.length := by
                              rw [ht_5504_c0]; omega
                            have ht_5504_bd_mod : (BitVec.toNat (5504 : BitVec 32) +
                                (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + tic.toNat)) %
                                2 ^ 32 < sct.length := by
                              rw [ht_5504_mod]; omega
                            c0_hsplit
                            · c0_hsteps!; exact hLt t1.toNat (t1, ()) mt ht1_dec
                                ⟨sct, hkt, by omega, rfl, hmt⟩
                            · let v_t := (sct[5504 + t1.toNat]'(by omega)) >>> (1 : Nat)
                              have hvt_lt : v_t.toNat < nv.toNat := by
                                refine Nat.lt_of_not_le (show ¬nv.toNat ≤ v_t.toNat from ?_)
                                dsimp only [v_t]
                                rw [m8_bv32_lshr1_toNat,
                                  ← m8_k6_get_congr ht_5504_mod ht_5504_bd_mod (by omega)]
                                simpa [nv, scr] using hc
                              clear hc
                              have hget_5504_c0 : sct[(BitVec.setWidth 64
                                  ((5504 : BitVec 32) +
                                    (tic - (1 : BitVec 32)))).toNat]'ht_5504_bd_c0 =
                                  sct[5504 + t1.toNat]'(by omega) :=
                                m8_k6_get_congr ht_5504_c0 ht_5504_bd_c0 (by omega)
                              have h5760_t_eq : (BitVec.setWidth 64 ((5760 : BitVec 32) +
                                  (sct[(BitVec.setWidth 64 ((5504 : BitVec 32) +
                                    (tic - (1 : BitVec 32)))).toNat]'ht_5504_bd_c0 >>> (1 :
                                      Nat)))).toNat =
                                  5760 + v_t.toNat := by
                                rw [hget_5504_c0]
                                change ((5760#32 + v_t).setWidth 64).toNat = 5760 + v_t.toNat
                                rw [m6_zext32_toNat]; c0_bound
                              have h5760_t_c0 : (BitVec.setWidth 64 ((5760 : BitVec 32) +
                                  (sct[(BitVec.setWidth 64 ((5504 : BitVec 32) +
                                    (tic - (1 : BitVec 32)))).toNat]'ht_5504_bd_c0 >>> (1 :
                                      Nat)))).toNat <
                                  sct.length := by
                                rw [h5760_t_eq]; omega
                              have h4480_t_eq : (BitVec.setWidth 64 ((4480 : BitVec 32) +
                                  (sct[(BitVec.setWidth 64 ((5504 : BitVec 32) +
                                    (tic - (1 : BitVec 32)))).toNat]'ht_5504_bd_c0 >>> (1 :
                                      Nat)))).toNat =
                                  4480 + v_t.toNat := by
                                rw [hget_5504_c0]
                                change ((4480#32 + v_t).setWidth 64).toNat = 4480 + v_t.toNat
                                rw [m6_zext32_toNat]; c0_bound
                              have h4480_t_c0 : (BitVec.setWidth 64 ((4480 : BitVec 32) +
                                  (sct[(BitVec.setWidth 64 ((5504 : BitVec 32) +
                                    (tic - (1 : BitVec 32)))).toNat]'ht_5504_bd_c0 >>> (1 :
                                      Nat)))).toNat <
                                  sct.length := by
                                rw [h4480_t_eq]; omega
                              c0_hsplit
                              · c0_hsteps!; exact hLt t1.toNat (t1, ()) mt ht1_dec
                                  ⟨sct, hkt, by omega, rfl, hmt⟩
                              · clear hc
                                have hm1_eq := m8_k6_set_congr (xs := sct) h5760_t_eq
                                  (congrArg (· &&& ~~~(2 : BitVec 32))
                                    (m8_k6_get_congr (xs := sct) h5760_t_eq h5760_t_c0 (by omega)))
                                c0_hsplit
                                · c0_hsteps!
                                  rw [hm1_eq] at hm
                                  exact hLt t1.toNat (t1, ()) _ ht1_dec
                                    ⟨_, invCore_set_flags hkt (v := v_t.toNat) (by omega) _,
                                      by omega, rfl, hm⟩
                                · rw [hm1_eq] at hm
                                  have hsct1_ex : ∃ sct1 : List (BitVec 32), invCore sct1 ∧
                                      sct1.length = scr.length ∧
                                      sct1[4480 + v_t.toNat]? = some (sct[4480 +
                                        v_t.toNat]'(by omega)) ∧
                                      (array (t := i32) c.pScratchBuf sct1 ⋆ R') m := by
                                    refine ⟨sct.set (5760 + v_t.toNat)
                                        ((sct[5760 + v_t.toNat]'(by omega)) &&& ~~~2#32),
                                      invCore_set_flags hkt (v := v_t.toNat) (by omega) _,
                                      by rw [List.length_set, hkt_l], ?_, hm⟩
                                    rw [List.getElem?_set_ne (by omega),
                                      List.getElem?_eq_getElem (by omega)]
                                  obtain ⟨sct1, hkt1, hkt1_l, hsct1_4480q, hm_n1⟩ := hsct1_ex
                                  clear hm
                                  have hm := hm_n1; clear hm_n1
                                  have hsct1_4480 : sct1[4480 + v_t.toNat]'(by omega) =
                                      sct[4480 + v_t.toNat]'(by omega) := by
                                    rw [List.getElem?_eq_getElem (by omega)] at hsct1_4480q
                                    exact Option.some.inj hsct1_4480q
                                  have hrsn : (sct1[4480 + v_t.toNat]'(by omega)).toNat <
                                    nc.toNat := by
                                    have hvt_div : v_t.toNat = (sct[5504 +
                                      t1.toNat]'(by omega)).toNat / 2 :=
                                      m8_bv32_lshr1_toNat _
                                    have hk_raw : (sct[(BitVec.toNat (5504 : BitVec 32) +
                                        (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + tic.toNat)) %
                                        2 ^ 32]'ht_5504_bd_mod).toNat / 2 = v_t.toNat := by
                                      rw [m8_k6_get_congr ht_5504_mod ht_5504_bd_mod (by omega)]
                                      exact hvt_div.symm
                                    have h5760_ne : (BitVec.toNat (5760 : BitVec 32) +
                                        (sct[(BitVec.toNat (5504 : BitVec 32) +
                                          (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + tic.toNat)) %
                                          2 ^ 32]'ht_5504_bd_mod).toNat / 2) % 2 ^ 32 ≠
                                        (BitVec.toNat (4480 : BitVec 32) +
                                          (sct[(BitVec.toNat (5504 : BitVec 32) +
                                            (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + tic.toNat)) %
                                            2 ^ 32]'ht_5504_bd_mod).toNat / 2) % 2 ^ 32 := by
                                      rw [hk_raw, show BitVec.toNat (5760 : BitVec 32) =
                                        5760 from rfl,
                                        show BitVec.toNat (4480 : BitVec 32) = 4480 from rfl]; omega
                                    have h4480_idx_eq : (BitVec.toNat (4480 : BitVec 32) +
                                        (sct[(BitVec.toNat (5504 : BitVec 32) +
                                          (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + tic.toNat)) %
                                          2 ^ 32]'ht_5504_bd_mod).toNat / 2) % 2 ^ 32 = 4480 +
                                            v_t.toNat := by
                                      rw [hk_raw, show BitVec.toNat (4480 : BitVec 32) =
                                        4480 from rfl]; omega
                                    have hc' := hc
                                    rw [List.getElem_set_ne h5760_ne] at hc'
                                    rw [m8_k6_get_congr h4480_idx_eq _ (by omega)] at hc'
                                    rw [hsct1_4480]
                                    exact Nat.lt_of_not_le (by simpa [nc, scr] using hc')
                                  clear hc
                                  let rsn := sct1[4480 + v_t.toNat]'(by omega)
                                  change rsn.toNat < nc.toNat at hrsn
                                  have hget_raw_rsn : ∀ hbd,
                                      (sct.set (BitVec.setWidth 64 ((5760 : BitVec 32) +
                                        (sct[(BitVec.setWidth 64 ((5504 : BitVec 32) +
                                          (tic - (1 : BitVec 32)))).toNat]'ht_5504_bd_c0 >>> (1 :
                                            Nat)))).toNat
                                        (sct[(BitVec.setWidth 64 ((5760 : BitVec 32) +
                                          (sct[(BitVec.setWidth 64 ((5504 : BitVec 32) +
                                            (tic - (1 : BitVec 32)))).toNat]'ht_5504_bd_c0 >>> (1 :
                                              Nat)))).toNat]'h5760_t_c0 &&&
                                          ~~~(2 : BitVec 32)))[(BitVec.setWidth 64 ((4480 : BitVec
                                            32) +
                                        (sct[(BitVec.setWidth 64 ((5504 : BitVec 32) +
                                          (tic - (1 : BitVec 32)))).toNat]'ht_5504_bd_c0 >>> (1 :
                                            Nat)))).toNat]'hbd = rsn := by
                                    intro hbd
                                    rw [List.getElem_set_ne (by rw [h5760_t_eq, h4480_t_eq]; omega)]
                                    exact (m8_k6_get_congr h4480_t_eq _ _).trans hsct1_4480.symm
                                  simp only [hget_raw_rsn]
                                  clear hm1_eq hget_raw_rsn
                                  have hk_rsn := hkt1.1.clause_ok (by
                                    have h1eq := hkt1.2.2.1 4193 (by omega) (Or.inl (by omega))
                                    rw [List.getElem?_eq_getElem (by omega),
                                      List.getElem?_eq_getElem (by omega)] at h1eq
                                    have hnc_e : sct1[4193]'(by omega) = nc := Option.some.inj h1eq
                                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
                                      hnc_e]; exact hrsn)
                                  let oldmr := sct1[12672 + rsn.toNat]'(by omega)
                                  have hpr := m8_km_core_or_pres oldmr
                                  have h12672_r_eq : (BitVec.setWidth 64 ((12672 : BitVec 32) +
                                    rsn)).toNat =
                                      12672 + rsn.toNat := by
                                    rw [m6_zext32_toNat]; c0_bound
                                  have h11648_r_eq : (BitVec.setWidth 64 ((11648 : BitVec 32) +
                                    rsn)).toNat =
                                      11648 + rsn.toNat := by
                                    rw [m6_zext32_toNat]; c0_bound
                                  have h12672_r_c0 : (BitVec.setWidth 64 ((12672 : BitVec 32) +
                                    rsn)).toNat <
                                      sct1.length := by
                                    rw [h12672_r_eq]; omega
                                  have h11648_r_c0 : (BitVec.setWidth 64 ((11648 : BitVec 32) +
                                    rsn)).toNat <
                                      sct1.length := by
                                    rw [h11648_r_eq]; omega
                                  have hrsn_nw : (sct1[11648 + rsn.toNat]'(by omega)).toNat +
                                      ((oldmr ||| 0x80000000#32) &&& 0xFFFF#32).toNat < 2 ^ 30 := by
                                    have h15_t : sct1[4207]'(by omega) = acap := by
                                      have := hkt1.2.2.1 4207 (by omega) (Or.inl (by omega))
                                      rw [List.getElem?_eq_getElem (by omega),
                                        List.getElem?_eq_getElem (by omega)] at this
                                      exact Option.some.inj this
                                    have hge_t := hkt1.1.length_ge
                                    rw [List.getElem?_eq_getElem (by omega : 4207 < sct1.length),
                                      Option.getD_some, h15_t] at hge_t
                                    rw [List.getElem?_eq_getElem (by omega : 11648 + rsn.toNat <
                                      sct1.length),
                                      List.getElem?_eq_getElem (by omega : 12672 + rsn.toNat <
                                        sct1.length),
                                      List.getElem?_eq_getElem (by omega : 4207 < sct1.length),
                                      Option.getD_some, Option.getD_some, Option.getD_some,
                                        h15_t] at hk_rsn
                                    dsimp only [oldmr] at hpr ⊢; rw [hpr.1]; have :=
                                      hkt1.1.length_lt; omega
                                  let roff := sct1[11648 + rsn.toNat]'(by omega)
                                  let rsz := (oldmr ||| 0x80000000#32) &&& 0xFFFF#32
                                  c0_hsteps_nogrp
                                  have hpr' : ((oldmr ||| 0x80000000#32) &&& 0xFFFF#32 =
                                        (sct1[12672 + rsn.toNat]?.getD 0#32) &&& 0xFFFF#32) ∧
                                      ((oldmr ||| 0x80000000#32) &&& 0x40000000#32 =
                                        (sct1[12672 + rsn.toNat]?.getD 0#32) &&& 0x40000000#32) :=
                                          by
                                    rw [List.getElem?_eq_getElem (by omega),
                                      Option.getD_some]; exact hpr
                                  have hm2_eq := m8_k6_set_congr (xs := sct1) h12672_r_eq
                                    (congrArg (· ||| (2147483648 : BitVec 32))
                                      (m8_k6_get_congr (xs :=
                                        sct1) h12672_r_eq h12672_r_c0 (by omega)))
                                  rw [hm2_eq] at hm
                                  have hget_raw_roff : ∀ hbd,
                                      (sct1.set (BitVec.setWidth 64 ((12672 : BitVec 32) +
                                        rsn)).toNat
                                        (sct1[(BitVec.setWidth 64 ((12672 : BitVec 32) +
                                          rsn)).toNat]'h12672_r_c0 |||
                                          (2147483648 : BitVec 32)))[(BitVec.setWidth 64 ((11648 :
                                            BitVec 32) +
                                        rsn)).toNat]'hbd = roff := by
                                    intro hbd
                                    rw [List.getElem_set_ne (by
                                      rw [h12672_r_eq, h11648_r_eq]; omega)]
                                    exact m8_k6_get_congr h11648_r_eq _ _
                                  have hget_raw_rmeta : ∀ hbd,
                                      (sct1.set (BitVec.setWidth 64 ((12672 : BitVec 32) +
                                        rsn)).toNat
                                        (sct1[(BitVec.setWidth 64 ((12672 : BitVec 32) +
                                          rsn)).toNat]'h12672_r_c0 |||
                                          (2147483648 : BitVec 32)))[(BitVec.setWidth 64 ((12672 :
                                            BitVec 32) +
                                        rsn)).toNat]'hbd = oldmr ||| (2147483648 : BitVec 32) := by
                                    intro hbd
                                    rw [List.getElem_set_self]
                                    exact congrArg (· ||| (2147483648 : BitVec 32))
                                      (m8_k6_get_congr h12672_r_eq _ _)
                                  simp only [hget_raw_roff, hget_raw_rmeta]
                                  have hsct2_ex : ∃ sct2 : List (BitVec 32), invCore sct2 ∧
                                      sct2.length = scr.length ∧
                                      sct2[12672 + rsn.toNat]? = some (oldmr ||| 0x80000000#32) ∧
                                      (array (t := i32) c.pScratchBuf sct2 ⋆ R') m := by
                                    refine ⟨sct1.set (12672 + rsn.toNat) (oldmr ||| 0x80000000#32),
                                      invCore_set_meta hkt1 hrsn hpr'.1 hpr'.2,
                                      by rw [List.length_set, hkt1_l], ?_, hm⟩
                                    rw [List.getElem?_set_self (by omega)]
                                  obtain ⟨sct2, hkt2, hkt2_l, h12672_r2q, hm_n2⟩ := hsct2_ex
                                  clear hm hpr' hm2_eq hget_raw_roff h12672_r2q hkt2_l
                                  have hm := hm_n2; clear hm_n2
                                  refine wp_join0
                                    (fun mr => ∃ scr_r, invCore scr_r ∧
                                      (array (t := i32) c.pScratchBuf scr_r ⋆ R') mr)
                                    ?_ ?_
                                  · intro _ mr ⟨scr_r, hkr, hmr⟩
                                    c0_hsteps!
                                    exact hLt t1.toNat (t1, ()) mr ht1_dec ⟨scr_r, hkr, by omega,
                                      rfl, hmr⟩
                                  · intro Jg hJg
                                    c0_hsplit
                                    · have hrsz_bd : roff.toNat + rsz.toNat ≤ acap.toNat := by
                                        have hmod : (roff.toNat + rsz.toNat) % 2 ^ 32 =
                                          roff.toNat + rsz.toNat :=
                                          Nat.mod_eq_of_lt (by dsimp only [roff, rsz]; omega)
                                        have hnw : ((oldmr ||| (2147483648 : BitVec 32)) &&&
                                          (65535 : BitVec 32)).toNat =
                                            rsz.toNat := rfl
                                        rw [hnw, hmod] at hc
                                        exact hc
                                      clear hc
                                      c0_hsteps_nogrp
                                      refine wp_loop_group (ts := [i32])
                                        (fun remj (jr, ()) mr => ∃ scr_r, invCore scr_r ∧
                                          jr.toNat ≤ rsz.toNat ∧ remj = rsz.toNat - jr.toNat ∧
                                          (array (t := i32) c.pScratchBuf scr_r ⋆ R') mr)
                                        ?_ ?_
                                      · rintro Lr remr ⟨jr, ⟨⟩⟩ mr hLr ⟨scr_r, hkr, hjr_le, rfl,
                                          hmr⟩
                                        have hkr_l := hkr.2.1
                                        c0_hsplit
                                        · have hjr_lt : jr.toNat < rsz.toNat := hc; clear hc
                                          have hrsz_lt : rsz.toNat < 65536 := by
                                            dsimp only [rsz]; rw [BitVec.toNat_and]
                                            exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
                                          have hj1 : (jr + 1#32).toNat = jr.toNat + 1 := by c0_bound
                                          have h15_r : scr_r[4207]'(by omega) = acap := by
                                            have := hkr.2.2.1 4207 (by omega) (Or.inl (by omega))
                                            rw [List.getElem?_eq_getElem (by omega),
                                              List.getElem?_eq_getElem (by omega)] at this
                                            exact Option.some.inj this
                                          have hge_r := hkr.1.length_ge
                                          rw [List.getElem?_eq_getElem (by omega : 4207 <
                                            scr_r.length),
                                            Option.getD_some, h15_r] at hge_r
                                          have har_r : 15744 + roff.toNat + jr.toNat <
                                            scr_r.length := by omega
                                          have h15744_r_c0 : (BitVec.setWidth 64 ((15744 : BitVec
                                            32) + roff + jr)).toNat <
                                              scr_r.length := by
                                            have := hkr.1.length_lt; rw [m6_zext32_toNat]; c0_bound
                                          c0_hsteps_nogrp
                                          refine wp_join0
                                            (fun mr1 => ∃ scr_r1, invCore scr_r1 ∧
                                              (array (t := i32) c.pScratchBuf scr_r1 ⋆ R') mr1)
                                            ?_ ?_
                                          · intro _ mr1 ⟨scr_r1, hkr1, hmr1⟩
                                            c0_hsteps!
                                            exact hLr (rsz.toNat - (jr + 1#32).toNat) (jr + 1#32,
                                              ()) mr1 (by omega)
                                              ⟨scr_r1, hkr1, by omega, rfl, hmr1⟩
                                          · intro Jlv hJlv
                                            c0_hsplit
                                            · have hlv_lt : ((scr_r[15744 + roff.toNat +
                                                jr.toNat]'har_r) >>> (1 : Nat)).toNat <
                                                  nv.toNat := by
                                                have har_mod : (BitVec.toNat (15744 : BitVec 32) +
                                                  roff.toNat + jr.toNat) %
                                                    2 ^ 32 = 15744 + roff.toNat + jr.toNat := by
                                                  have := hkr.1.length_lt
                                                  rw [show BitVec.toNat (15744 : BitVec 32) =
                                                    15744 from rfl,
                                                    Nat.mod_eq_of_lt (by omega)]
                                                rw [m8_bv32_lshr1_toNat,
                                                  ← m8_k6_get_congr har_mod (by
                                                    rw [har_mod]; exact har_r) har_r]
                                                simpa [nv, scr] using hc
                                              clear hc
                                              have hget_lr : scr_r[(BitVec.setWidth 64 ((15744 :
                                                BitVec 32) +
                                                  roff + jr)).toNat]'h15744_r_c0 =
                                                  scr_r[15744 + roff.toNat + jr.toNat]'har_r :=
                                                m8_k6_get_congr (by
                                                  have := hkr.1.length_lt
                                                  rw [m6_zext32_toNat]; c0_bound) _ _
                                              have h5760_r_eq : (BitVec.setWidth 64 ((5760 : BitVec
                                                32) +
                                                  (scr_r[(BitVec.setWidth 64 ((15744 : BitVec 32) +
                                                    roff + jr)).toNat]'h15744_r_c0 >>> (1 :
                                                      Nat)))).toNat =
                                                  5760 + ((scr_r[15744 + roff.toNat +
                                                    jr.toNat]'har_r) >>> (1 : Nat)).toNat := by
                                                rw [hget_lr, m6_zext32_toNat]; c0_bound
                                              have h5760_r_c0 : (BitVec.setWidth 64 ((5760 : BitVec
                                                32) +
                                                  (scr_r[(BitVec.setWidth 64 ((15744 : BitVec 32) +
                                                    roff + jr)).toNat]'h15744_r_c0 >>> (1 :
                                                      Nat)))).toNat < scr_r.length := by
                                                rw [h5760_r_eq]; omega
                                              c0_hsplit
                                              · c0_hsteps!
                                                have hmr_eq := m8_k6_set_congr (xs :=
                                                  scr_r) h5760_r_eq
                                                  (congrArg (· ||| (2 : BitVec 32))
                                                    (m8_k6_get_congr (xs :=
                                                      scr_r) h5760_r_eq h5760_r_c0 (by omega)))
                                                rw [hmr_eq] at hm
                                                exact hJlv _ ⟨_, invCore_set_flags hkr
                                                  (v := ((scr_r[15744 + roff.toNat +
                                                    jr.toNat]'har_r) >>> (1 : Nat)).toNat)
                                                  (by omega) _, hm⟩
                                              · c0_hsteps!; exact hJlv mr ⟨scr_r, hkr, hmr⟩
                                            · c0_hsteps!; exact hJlv mr ⟨scr_r, hkr, hmr⟩
                                        · c0_hsteps!; exact hJg mr ⟨scr_r, hkr, hmr⟩
                                      · intro Lr hLr; c0_hsteps!
                                        exact hLr rsz.toNat (0#32, ()) _ ⟨sct2, hkt2,
                                          Nat.zero_le _, by simp, hm⟩
                                    · c0_hsteps!; exact hJg m ⟨sct2, hkt2, hm⟩
                          · c0_hsteps_nogrp
                            refine wp_loop_group (ts := [i32])
                              (fun rem (i2, ()) mf2 => ∃ scf2, invCore scf2 ∧ i2.toNat ≤ nv.toNat ∧
                                rem = nv.toNat - i2.toNat ∧
                                (array (t := i32) c.pScratchBuf scf2 ⋆ R') mf2)
                              ?_ ?_
                            · rintro Lf2 remf2 ⟨if2, ⟨⟩⟩ mf2 hLf2 ⟨scf2, hkf2, hif2, rfl, hmf2⟩
                              have hkf2_l := hkf2.2.1
                              c0_hsplit
                              · have hi_lt : if2.toNat < nv.toNat := by simpa [nv, scr] using hc
                                clear hc
                                have hif2_s : (if2 + 1#32).toNat = if2.toNat + 1 := by c0_bound
                                have h5760_i2 : (BitVec.setWidth 64 ((5760 : BitVec 32) +
                                  if2)).toNat =
                                    5760 + if2.toNat := by
                                  rw [m6_zext32_toNat]; c0_bound
                                c0_hsteps!
                                rw [m8_k6_set_congr h5760_i2 rfl] at hm
                                exact hLf2 (nv.toNat - (if2 + 1#32).toNat) (if2 + 1#32,
                                  ()) _ (by omega)
                                  ⟨_, invCore_set_flags hkf2 (v := if2.toNat) (by omega) _,
                                    by omega, rfl, hm⟩
                              · c0_hsteps!; exact hJinc (scf2, if2) mf2 ⟨hkf2, hmf2⟩
                            · intro Lf2 hLf2; c0_hsteps!
                              exact hLf2 nv.toNat (0#32, ()) mt ⟨sct, hkt, Nat.zero_le _, by simp,
                                hmt⟩
                        · intro Lt hLt; c0_hsteps!
                          exact hLt ti.toNat (ti, ()) mj ⟨scj, hkj, hti, rfl, hmj⟩
                      · intro Jti hJti
                        c0_hsplit
                        · c0_hsteps!; exact hJti 256#32 (by decide)
                        · c0_hsteps!; exact hJti _ (by c0_bound)
                    · intro Jinc_loop hJinc_loop
                      try clear hL1 hi1_le hm1 hk1_l hk1 L1 Jinc hJinc hLf hif1 hmf1 Lf
                      c0_hsplit
                      · have hisz_bd : off_i.toNat + sz_i.toNat ≤ acap.toNat := by
                          have hmod : (off_i.toNat + sz_i.toNat) % 2 ^ 32 = off_i.toNat +
                            sz_i.toNat :=
                            Nat.mod_eq_of_lt (by dsimp only [off_i, sz_i]; omega)
                          have hnw : ((oldmi ||| 2147483648#32) &&& (65535 : BitVec 32)).toNat =
                              sz_i.toNat := rfl
                          rw [hnw, hmod] at hc
                          exact hc
                        clear hc
                        c0_hsteps_nogrp
                        refine wp_loop_group (ts := [i32])
                          (fun rem (j, ()) mj => ∃ scj, invCore scj ∧
                            j.toNat ≤ sz_i.toNat ∧ rem = sz_i.toNat - j.toNat ∧
                            (array (t := i32) c.pScratchBuf scj ⋆ R') mj)
                          ?_ ?_
                        · rintro Lj remj ⟨j, ⟨⟩⟩ mj hLj ⟨scj, hkj, hj_le, rfl, hmj⟩
                          have hkj_l := hkj.2.1
                          c0_hsplit
                          · have hj_lt : j.toNat < sz_i.toNat := hc; clear hc
                            have hsz_lt : sz_i.toNat < 65536 := by
                              dsimp only [sz_i]; rw [BitVec.toNat_and]
                              exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
                            have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
                            have h15_j : scj[4207]'(by omega) = acap := by
                              have := hkj.2.2.1 4207 (by omega) (Or.inl (by omega))
                              rw [List.getElem?_eq_getElem (by omega),
                                List.getElem?_eq_getElem (by omega)] at this
                              exact Option.some.inj this
                            have hge_j := hkj.1.length_ge
                            rw [List.getElem?_eq_getElem (by omega : 4207 < scj.length),
                              Option.getD_some, h15_j] at hge_j
                            have har_j : 15744 + off_i.toNat + j.toNat < scj.length := by omega
                            have har_j_c0 : (BitVec.setWidth 64 ((15744 : BitVec 32) + off_i +
                              j)).toNat <
                                scj.length := by
                              have := hkj.1.length_lt; rw [m6_zext32_toNat]; c0_bound
                            c0_hsteps_nogrp
                            refine wp_join0
                              (fun mj2 => ∃ scj2, invCore scj2 ∧
                                (array (t := i32) c.pScratchBuf scj2 ⋆ R') mj2)
                              ?_ ?_
                            · intro _ mj2 ⟨scj2, hkj2, hmj2⟩
                              c0_hsteps!
                              exact hLj (sz_i.toNat - (j + 1#32).toNat) (j + 1#32,
                                ()) mj2 (by omega)
                                ⟨scj2, hkj2, by omega, rfl, hmj2⟩
                            · intro Jlv hJlv
                              c0_hsplit
                              · have hget_j_c0 : scj[(BitVec.setWidth 64 ((15744 : BitVec 32) +
                                    off_i + j)).toNat]'har_j_c0 = scj[15744 + off_i.toNat +
                                      j.toNat]'har_j :=
                                  m8_k6_get_congr (by
                                    have := hkj.1.length_lt
                                    rw [m6_zext32_toNat]; c0_bound) _ _
                                have hj_v_lt : ((scj[15744 + off_i.toNat +
                                  j.toNat]'har_j) >>> (1 : Nat)).toNat <
                                    nv.toNat := by
                                  have har_mod : (BitVec.toNat (15744 : BitVec 32) + off_i.toNat +
                                    j.toNat) %
                                      2 ^ 32 = 15744 + off_i.toNat + j.toNat := by
                                    have := hkj.1.length_lt
                                    rw [show BitVec.toNat (15744 : BitVec 32) = 15744 from rfl,
                                      Nat.mod_eq_of_lt (by omega)]
                                  rw [m8_bv32_lshr1_toNat,
                                    ← m8_k6_get_congr har_mod (by rw [har_mod]; exact har_j) har_j]
                                  simpa [nv, scr] using hc
                                clear hc
                                have h5760_j_eq : (BitVec.setWidth 64 ((5760 : BitVec 32) +
                                    (scj[(BitVec.setWidth 64 ((15744 : BitVec 32) +
                                      off_i + j)).toNat]'har_j_c0 >>> (1 : Nat)))).toNat =
                                    5760 + ((scj[15744 + off_i.toNat +
                                      j.toNat]'har_j) >>> (1 : Nat)).toNat := by
                                  rw [hget_j_c0, m6_zext32_toNat]; c0_bound
                                have h5760_j_c0 : (BitVec.setWidth 64 ((5760 : BitVec 32) +
                                    (scj[(BitVec.setWidth 64 ((15744 : BitVec 32) +
                                      off_i + j)).toNat]'har_j_c0 >>> (1 : Nat)))).toNat <
                                        scj.length := by
                                  rw [h5760_j_eq]; omega
                                c0_hsteps!
                                have hmj_eq := m8_k6_set_congr (xs := scj) h5760_j_eq
                                  (congrArg (· ||| (2 : BitVec 32))
                                    (m8_k6_get_congr (xs := scj) h5760_j_eq h5760_j_c0 (by omega)))
                                rw [hmj_eq] at hm
                                exact hJlv _ ⟨_, invCore_set_flags hkj
                                  (v := ((scj[15744 + off_i.toNat +
                                    j.toNat]'har_j) >>> (1 : Nat)).toNat)
                                  (by omega) _, hm⟩
                              · c0_hsteps!; exact hJlv mj ⟨scj, hkj, hmj⟩
                          · c0_hsteps!; exact hJinc_loop mj ⟨scj, hkj, hmj⟩
                        · intro Lj hLj; c0_hsteps!
                          exact hLj sz_i.toNat (0#32, ()) _ ⟨scf1s, h_scf1s, Nat.zero_le _,
                            by simp, hm⟩
                      · c0_hsteps!; exact hJinc_loop _ ⟨scf1s, h_scf1s, hm⟩
                · intro Lf hLf; c0_hsteps!
                  exact hLf nv.toNat (0#32, ()) m1 ⟨sc1, hk1, Nat.zero_le _, by simp, hm1⟩
              · c0_hsteps!; exact hJinc (sc1, i1) m1 ⟨hk1, hm1⟩
      · intro L1 hL1; c0_hsteps!
        exact hL1 nc.toNat (0#32, ()) m0 ⟨scr, ⟨hok0, rfl, fun _ _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩,
          Nat.zero_le _, by simp, hm0'⟩


end LeanQbe.T.Examples.Kissat.FullM8CoreParity
