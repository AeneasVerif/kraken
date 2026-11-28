/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Definition
public import LeanQbe.T.Examples.Kissat.Proof.Definition.WpFidBasic
public import LeanQbe.T.Examples.Kissat.Proof.Definition.WpFidExtract
public import LeanQbe.T.Examples.Kissat.Proof.Definition.WpFidCert
public import LeanQbe.T.Examples.Kissat.Proof.Gates.Spec

/-!
# Kissat Fidelity BVE K6 Def & Gates Dispatcher WP (`Proof.Definition.WpFidGates`)

Flat `CanonicalEnv` `Func.wp` proofs for the top-level fidelity gate dispatchers:
- `full_bve_def_k6_fid_wp` (`m8BveGatesSpec`)
- `full_bve_gates_fid_wp` (`m8BveGatesSpec`)

Zero legacy `Full*` imports; zero `@[expose]` on theorems/lemmas/sections; every decl `<= 450`
LOC; every line `<= 100` cols.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Definition

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Definition
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
open LeanQbe.T.Examples.Kissat.Proof.Gates

open scoped FullArenaTactics M8K6bTactics FidK6cTactics

local macro_rules
  | `(tactic| c0_bound) => `(tactic| first | assumption | rfl | decide |
      ((try rw [fid_zext32_toNat]); (repeat rw [List.length_set]); omega))

/-! ## 1. Pure BitVec, Entry, & Scratch Preservation Helpers -/

private theorem fid_gates_and_1_eq {v : BitVec 32} :
    ((v <<< 1) &&& 1#32) = 0#32 ∧ (((v <<< 1) ||| 1#32) &&& 1#32) = 1#32 := by
  have hz : (v <<< 1).toNat % 2 = 0 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm,
      ← Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2 ^ 32)]
    simp [Nat.mul_mod_right]
  have h1bit : ∀ j : Nat, Nat.testBit 1 (j + 1) = false := fun j => by
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt
      (by have : 2 ≤ 2 ^ (j + 1) := Nat.le_self_pow (by omega) 2; omega : 1 < 2 ^ (j + 1))]
    decide
  have h0 : ((v <<< 1) &&& 1#32).toNat = 0 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod, hz]
  have h1 : (((v <<< 1) ||| 1#32) &&& 1#32).toNat = 1 := by
    rw [BitVec.toNat_and, BitVec.toNat_or, show (1#32 : BitVec 32).toNat = 1 from rfl]
    apply Nat.eq_of_testBit_eq; intro i; cases i with
    | zero =>
      rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_zero, Nat.testBit_zero]
      simp [show (1 : Nat) % 2 = 1 by decide]
    | succ j => rw [Nat.testBit_and, h1bit j, Bool.and_false]
  exact ⟨BitVec.eq_of_toNat_eq h0, BitVec.eq_of_toNat_eq h1⟩

private theorem fid_gates_shl1_xor1 {v : BitVec 32} {cv : Nat}
    (hv : v.toNat < cv) (hcv : 2 * cv + 1 < 2 ^ 30) :
    ((v <<< 1) ^^^ 1#32).toNat = 2 * v.toNat + 1 ∧
      (((v <<< 1) ||| 1#32) ^^^ 1#32).toNat = 2 * v.toNat := by
  have hsh := fid_k6c_bv32_shl1_add1_lt hv hcv
  have h20 : (2 * v.toNat) / 2 = v.toNat := by omega
  have h21 : (2 * v.toNat + 1) / 2 = v.toNat := by omega
  have h0 : ((v <<< 1) ^^^ 1#32).toNat = 2 * v.toNat + 1 := by
    rw [BitVec.toNat_xor, hsh.1, show (1#32 : BitVec 32).toNat = 1 from rfl]
    apply Nat.eq_of_testBit_eq; intro i; cases i with
    | zero => simp [Nat.testBit_zero, show (2 * v.toNat + 1) % 2 = 1 by omega]
    | succ j =>
      rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
        show (1 : Nat) / 2 = 0 from rfl, Nat.zero_testBit, Bool.xor_false, h21, h20]
  have h1 : (((v <<< 1) ||| 1#32) ^^^ 1#32).toNat = 2 * v.toNat := by
    rw [BitVec.toNat_xor, hsh.2, show (1#32 : BitVec 32).toNat = 1 from rfl]
    apply Nat.eq_of_testBit_eq; intro i; cases i with
    | zero => simp [Nat.testBit_zero, show (2 * v.toNat + 1) % 2 = 1 by omega]
    | succ j =>
      rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
        show (1 : Nat) / 2 = 0 from rfl, Nat.zero_testBit, Bool.xor_false, h21, h20]
  exact ⟨h0, h1⟩

private theorem fid_gates_entry_bin_bounds {F_cur : List (List Nat)} {s : FullState}
    {lit : Nat} {w : BitVec 32} (hok : FullBveEntryOkW F_cur s lit w)
    (hbit : (w &&& 0x80000000#32) ≠ 0#32) :
    (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars := by
  unfold FullBveEntryOkW at hok
  rw [ite_eq_left hbit] at hok
  exact hok.1

private theorem fid_gates_inv_exit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    (s0 : FullState) {np nn : BitVec 32} {R : Mem 64 → Prop}
    {s : FullState} {m : Mem 64}
    (hinv' : FullDenseInvW c F0 F_cur s) (htmk' : TmkZero s)
    (hcv : s.core.cur_vars = s0.core.cur_vars) (har : s.core.arena = s0.core.arena)
    (hal : s.core.arena_len = s0.core.arena_len) (hfl : s.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hpres : ∀ i < 4002, s.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]?)
    (hm : (FullMem c s ⋆ R) m) (hnp : np.toNat ≤ 2001) (hnn : nn.toNat ≤ 2001)
    {Q : Post []}
    (hQ : ∀ (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.arena = s0.core.arena →
      s'.core.arena_len = s0.core.arena_len → s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (∀ i < np.toNat, s'.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]?) →
      (∀ j < nn.toNat, s'.scratch.scratch_buf[2001 + j]? = s0.scratch.scratch_buf[2001 + j]?) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    Q () m :=
  hQ s m hinv' htmk' hcv har hal hfl
    (fun i hi => hpres i (by omega))
    (fun j hj => hpres (2001 + j) (by omega))
    hm

private theorem fid_def_k6_clear4130_wp {Γ : Env} {Q : Post []} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} (s0 s2 : FullState)
    {R : Mem 64 → Prop} {m2 : Mem 64}
    {K : Expr Val Cont []}
    (hinv2 : FullDenseInvW c F0 F_cur s2) (htmk2 : TmkZero s2)
    (hcv2 : s2.core.cur_vars = s0.core.cur_vars) (har2 : s2.core.arena = s0.core.arena)
    (hal2 : s2.core.arena_len = s0.core.arena_len) (hfl2 : s2.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (h16k : 16384 ≤ c.scratch_cap)
    (hpres2 : ∀ i < 4002, s2.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]?)
    (hm2 : (FullMem c s2 ⋆ R) m2)
    (hK : ∀ (s3 : FullState) (m3 : Mem 64),
      FullDenseInvW c F0 F_cur s3 → TmkZero s3 →
      s3.core.cur_vars = s0.core.cur_vars → s3.core.arena = s0.core.arena →
      s3.core.arena_len = s0.core.arena_len → s3.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (∀ i < 4002, s3.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]?) →
      (FullMem c s3 ⋆ R) m3 → wp Γ Q X K m3) :
    wp Γ Q X
      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm (t := i32) 4130, ())) fun p =>
       Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
       Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p.fst, ())) fun p =>
       Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
         (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm (t := i32) 4131, ())) fun p =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p.fst, ())) fun p =>
          Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst) K)) m2 := by
  have hscr2 : s2.scratch.scratch_buf.length = c.scratch_cap := hinv2.1.scratch_ok.scratch_buf_len
  have hm2' : (FullMem c (m8ScrSt s2 s2.scratch.scratch_buf) ⋆ R) m2 := by rwa [m8ScrSt_self]
  have h15k : 15744 ≤ s2.scratch.scratch_buf.length := by omega
  c0_hsteps!
  let scr3 := (s2.scratch.scratch_buf.set (BitVec.setWidth 64 4130#32).toNat 0#32).set
    (BitVec.setWidth 64 4131#32).toNat 0#32
  let s3 := m8ScrSt s2 scr3
  have hscr3 : scr3.length = c.scratch_cap := by simp [scr3, hscr2]
  have hinv3 : FullDenseInvW c F0 F_cur s3 := m8_fullDenseInvW_scr hinv2 hscr3
  have h4130 : (BitVec.setWidth 64 (4130#32 : BitVec 32)).toNat = 4130 := rfl
  have h4131 : (BitVec.setWidth 64 (4131#32 : BitVec 32)).toNat = 4131 := rfl
  have hpres3 : ∀ i < 4002, s3.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]? := by
    intro i hi
    dsimp only [s3, m8ScrSt, scr3]
    rw [List.getElem?_set_ne (by rw [h4131]; omega),
      List.getElem?_set_ne (by rw [h4130]; omega)]
    exact hpres2 i hi
  exact hK s3 _ hinv3 htmk2 hcv2 har2 hal2 hfl2 hpres3 ‹_›

/-! ## 2. `full_bve_def_k6_fid_wp` -/

@[reducible] private def fidDefK6AfterScanExpr (c : FullCfg) (v np nn : BitVec 32)
    (hp hn : Bool) : Expr Val Cont [] :=
  Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var v, Arg.imm 1, ())) fun p15 =>
  Expr.let_ (Op.mk (OpCode.or i32) (Arg.var p15.fst, Arg.imm 1, ())) fun p16 =>
  Expr.group (fun _ : Tup Cont [[]] =>
     Blocks.cons (fun _ : Tup Val [] => Expr.ret ()) Blocks.nil)
   fun Js_ret =>
   Expr.group (fun _ : Tup Cont [[]] =>
     Blocks.cons (fun _ : Tup Val [] =>
       Expr.group (fun _ : Tup Cont [[]] =>
         Blocks.cons (fun _ : Tup Val [] => Expr.jump Js_ret.fst ()) Blocks.nil)
       fun Js_out =>
       Expr.jnz (Arg.var hp)
         (Expr.jnz (Arg.var hn)
           (Expr.jump Js_out.fst ())
           (Expr.group (fun _ : Tup Cont [[]] =>
              Blocks.cons (fun _ : Tup Val [] => Expr.jump Js_out.fst ()) Blocks.nil)
            fun Js_in =>
            Expr.call (as := [i64, i32, i32, i32, i32, i32]) (bs := [Ty.bool])
              "full_bve_certify_unit_fid"
              (Arg.var c.hdr, Arg.var v, Arg.var p15.fst, Arg.imm 0, Arg.var np,
                Arg.imm 4002, ())
              fun okp =>
              Expr.jnz (Arg.var okp.fst)
                (Expr.jump Js_in.fst ())
                (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm (t := i32) 4130, ())) fun p =>
                 Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
                 Expr.let_ (Op.mk (OpCode.add i64)
                     (Arg.var c.pScratchBuf, Arg.var p.fst, ())) fun p =>
                 Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
                   (Expr.let_ (Op.mk (OpCode.zext 32 64)
                        (Arg.imm (t := i32) 4131, ())) fun p =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
                    Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pScratchBuf, Arg.var p.fst, ())) fun p =>
                    Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
                      (Expr.jump Js_in.fst ())))))
         (Expr.jump Js_out.fst ()))
     Blocks.nil)
   fun Js_after =>
   Expr.jnz (Arg.var hp)
     (Expr.jump Js_after.fst ())
     (Expr.jnz (Arg.var hn)
       (Expr.group (fun _ : Tup Cont [[]] =>
          Blocks.cons (fun _ : Tup Val [] => Expr.jump Js_ret.fst ()) Blocks.nil)
        fun Js_in =>
        Expr.call (as := [i64, i32, i32, i32, i32, i32]) (bs := [Ty.bool])
          "full_bve_certify_unit_fid"
          (Arg.var c.hdr, Arg.var v, Arg.var p16.fst, Arg.imm 2001, Arg.var nn,
            Arg.imm 4066, ())
          fun okn =>
          Expr.jnz (Arg.var okn.fst)
            (Expr.jump Js_in.fst ())
            (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm (t := i32) 4130, ())) fun p =>
             Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
             Expr.let_ (Op.mk (OpCode.add i64)
                 (Arg.var c.pScratchBuf, Arg.var p.fst, ())) fun p =>
             Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
               (Expr.let_ (Op.mk (OpCode.zext 32 64)
                    (Arg.imm (t := i32) 4131, ())) fun p =>
                Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
                Expr.let_ (Op.mk (OpCode.add i64)
                    (Arg.var c.pScratchBuf, Arg.var p.fst, ())) fun p =>
                Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
                  (Expr.jump Js_in.fst ()))))
       (Expr.jump Js_after.fst ()))

private theorem fid_def_k6_scan_wp {Γ : Env} {Q : Post []} {X : XPost}
    (after : Bool → Bool → Expr Val Cont [])
    {c : FullCfg} {s2 : FullState} {R : Mem 64 → Prop} {m2 : Mem 64}
    (_h16k : 16384 ≤ c.scratch_cap) (hscr2 : s2.scratch.scratch_buf.length = c.scratch_cap)
    (hm2 : (FullMem c s2 ⋆ R) m2)
    (hExit : ∀ (hp hn : Bool) (m' : Mem 64),
      (FullMem c s2 ⋆ R) m' → wp Γ Q X (after hp hn) m') :
    wp Γ Q X
      (Expr.group (fun Lscan : Tup Cont [[Ty.bool, Ty.bool, i32]] =>
        Blocks.cons (fun p13 : Tup Val [Ty.bool, Ty.bool, i32] =>
          Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl)
              (Arg.var p13.snd.snd.fst, Arg.imm 64, ())) fun p14 =>
          Expr.jnz (Arg.var p14.fst)
            (Expr.group (fun _ : Tup Cont [[Ty.bool]] =>
               Blocks.cons (fun p : Tup Val [Ty.bool] =>
                 Expr.group (fun _ : Tup Cont [[Ty.bool]] =>
                   Blocks.cons (fun p15 : Tup Val [Ty.bool] =>
                     Expr.let_ (Op.mk (OpCode.add i32)
                         (Arg.var p13.snd.snd.fst, Arg.imm 1, ())) fun p16 =>
                     Expr.jump Lscan.fst (Arg.var p.fst, Arg.var p15.fst, Arg.var p16.fst, ()))
                   Blocks.nil)
                 fun Js_neg =>
                 Expr.let_ (Op.mk (OpCode.add i32)
                     (Arg.imm 4066, Arg.var p13.snd.snd.fst, ())) fun pa =>
                 Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pa.fst, ())) fun pb =>
                 Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var pb.fst, Arg.imm 4, ())) fun pc =>
                 Expr.let_ (Op.mk (OpCode.add i64)
                     (Arg.var c.pScratchBuf, Arg.var pc.fst, ())) fun pd =>
                 Expr.load i32 (Arg.var pd.fst) fun ld =>
                 Expr.let_ (Op.mk (OpCode.cmp .ne i32 .bool rfl)
                     (Arg.var ld, Arg.imm 0, ())) fun pe =>
                 Expr.jnz (Arg.var pe.fst)
                   (Expr.jump Js_neg.fst (Arg.imm true, ()))
                   (Expr.jump Js_neg.fst (Arg.var p13.snd.fst, ())))
               Blocks.nil)
             fun Js_pos =>
             Expr.let_ (Op.mk (OpCode.add i32)
                 (Arg.imm 4002, Arg.var p13.snd.snd.fst, ())) fun pa =>
             Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pa.fst, ())) fun pb =>
             Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var pb.fst, Arg.imm 4, ())) fun pc =>
             Expr.let_ (Op.mk (OpCode.add i64)
                 (Arg.var c.pScratchBuf, Arg.var pc.fst, ())) fun pd =>
             Expr.load i32 (Arg.var pd.fst) fun ld =>
             Expr.let_ (Op.mk (OpCode.cmp .ne i32 .bool rfl)
                 (Arg.var ld, Arg.imm 0, ())) fun pe =>
             Expr.jnz (Arg.var pe.fst)
               (Expr.jump Js_pos.fst (Arg.imm true, ()))
               (Expr.jump Js_pos.fst (Arg.var p13.fst, ())))
            (after p13.fst p13.snd.fst))
        Blocks.nil)
      fun Lscan => Expr.jump Lscan.fst (Arg.imm false, Arg.imm false, Arg.imm 0, ())) m2 := by
  have hm2' : (FullMem c (m8ScrSt s2 s2.scratch.scratch_buf) ⋆ R) m2 := by rwa [m8ScrSt_self]
  refine wp_loop_group (ts := [Ty.bool, Ty.bool, i32])
    (fun rem pl m' => pl.snd.snd.fst.toNat ≤ 64 ∧ rem = 64 - pl.snd.snd.fst.toNat ∧
      (FullMem c (m8ScrSt s2 s2.scratch.scratch_buf) ⋆ R) m')
    ?_ ?_
  · intro J n ⟨hp, hn, k, ⟨⟩⟩ m' hcont ⟨hk_le, hrem, hm'⟩
    dsimp only at hk_le hrem
    dsimp only [Blocks.get, Member.here]
    c0_hsplit
    · have hk_lt : k.toNat < 64 := hc
      have hk1 : (k + 1#32).toNat = k.toNat + 1 := fid_k6c_add1_toNat hk_lt (by omega)
      have hidx_p : (BitVec.setWidth 64 (4002#32 + k)).toNat < s2.scratch.scratch_buf.length := by
        rw [fid_zext32_toNat]; have : (4002#32 + k).toNat = 4002 + k.toNat := by bv_omega
        omega
      have hidx_n : (BitVec.setWidth 64 (4066#32 + k)).toNat < s2.scratch.scratch_buf.length := by
        rw [fid_zext32_toNat]; have : (4066#32 + k).toNat = 4066 + k.toNat := by bv_omega
        omega
      c0_hsteps_nogrp
      refine wp_join_state_pure (ts := [Ty.bool]) (fun b => (b, ())) (fun _ => True) ?_ ?_
      · intro _ hp' _
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [Ty.bool]) (fun b => (b, ())) (fun _ => True) ?_ ?_
        · intro _ hn' _
          c0_hsteps!
          exact hcont (64 - (k + 1#32).toNat) (hp', hn', k + 1#32, ()) m'
            (by rw [hk1, hrem]; omega) ⟨by dsimp only; rw [hk1]; omega, rfl, hm'⟩
        · intro Jn hJn
          c0_hsplit <;> c0_hsteps! <;> exact hJn _ trivial
      · intro Jp hJp
        c0_hsplit <;> c0_hsteps! <;> exact hJp _ trivial
    · rw [m8ScrSt_self] at hm'
      exact hExit hp hn m' hm'
  · intro J hJ; c0_hsteps!
    exact hJ 64 _ _ ⟨Nat.zero_le _, rfl, hm2'⟩

private theorem fid_def_k6_post_extract2_wp {Γ : Env} {Q : Post []} {X : XPost}
    (hCertify : Γ.Has "full_bve_certify_unit_fid" fidBveCertifyUnitSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} (s0 s2 : FullState)
    {v np nn : BitVec 32} {hp hn : Bool} {R : Mem 64 → Prop} {m2 : Mem 64}
    (hinv2 : FullDenseInvW c F0 F_cur s2) (htmk2 : TmkZero s2)
    (hcv2 : s2.core.cur_vars = s0.core.cur_vars) (har2 : s2.core.arena = s0.core.arena)
    (hal2 : s2.core.arena_len = s0.core.arena_len) (hfl2 : s2.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (h16k : 16384 ≤ c.scratch_cap) (hv2 : v.toNat < s2.core.cur_vars)
    (hnp : np.toNat ≤ 2001) (hnn : nn.toNat ≤ 2001)
    (hpos2 : ∀ i < np.toNat, FullBveEntryOkW F_cur s2 (2 * v.toNat)
      (s2.scratch.scratch_buf[i]?.getD 0#32))
    (hneg2 : ∀ j < nn.toNat, FullBveEntryOkW F_cur s2 (2 * v.toNat + 1)
      (s2.scratch.scratch_buf[2001 + j]?.getD 0#32))
    (hpres2 : ∀ i < 4002, s2.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]?)
    (hm2 : (FullMem c s2 ⋆ R) m2)
    (hQ : ∀ (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.arena = s0.core.arena →
      s'.core.arena_len = s0.core.arena_len → s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (∀ i < np.toNat, s'.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]?) →
      (∀ j < nn.toNat, s'.scratch.scratch_buf[2001 + j]? = s0.scratch.scratch_buf[2001 + j]?) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    wp Γ Q X (fidDefK6AfterScanExpr c v np nn hp hn) m2 := by
  have hcv_lt : 2 * s2.core.cur_vars + 1 < 2 ^ 30 := by
    have := hinv2.1.core_ok.cur_vars_le; have := c.hmaxv
    simp only [dimacsBound] at this; omega
  have hsh := fid_k6c_bv32_shl1_add1_lt hv2 hcv_lt
  dsimp only [fidDefK6AfterScanExpr]
  c0_hsteps_nogrp
  apply wp_unroll_group; intro Js_ret hJs_ret
  have hRet : ∀ (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.arena = s0.core.arena →
      s'.core.arena_len = s0.core.arena_len → s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (∀ i < 4002, s'.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Js_ret () m' := by
    intro s' m' hi ht hcv har hal hfl hpr hm'
    apply hJs_ret; try dsimp only [Blocks.get, Member.here]
    c0_hsteps!
    exact fid_gates_inv_exit s0 hi ht hcv har hal hfl hpr hm' hnp hnn hQ
  clear hJs_ret
  apply wp_unroll_group; intro Js_after hJs_after
  have hAfter : ∀ (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.arena = s0.core.arena →
      s'.core.arena_len = s0.core.arena_len → s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (∀ i < np.toNat, FullBveEntryOkW F_cur s' (2 * v.toNat)
        (s'.scratch.scratch_buf[i]?.getD 0#32)) →
      (∀ i < 4002, s'.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Js_after () m' := by
    intro s' m' hi' ht' hcv' har' hal' hfl' hpos' hpr' hm'
    apply hJs_after; try dsimp only [Blocks.get, Member.here]
    apply wp_unroll_group; intro Js_out hJs_out
    have hOut : ∀ (s'' : FullState) (m'' : Mem 64),
        FullDenseInvW c F0 F_cur s'' → TmkZero s'' →
        s''.core.cur_vars = s0.core.cur_vars → s''.core.arena = s0.core.arena →
        s''.core.arena_len = s0.core.arena_len → s''.core.fuel.toNat ≤ s0.core.fuel.toNat →
        (∀ i < 4002, s''.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]?) →
        (FullMem c s'' ⋆ R) m'' → Js_out () m'' := by
      intro s'' m'' hi'' ht'' hcv'' har'' hal'' hfl'' hpr'' hm''
      apply hJs_out; try dsimp only [Blocks.get, Member.here]
      c0_hsteps!; exact hRet s'' m'' hi'' ht'' hcv'' har'' hal'' hfl'' hpr'' hm''
    clear hJs_out
    c0_hsteps_nogrp
    · exact hOut s' m' hi' ht' hcv' har' hal' hfl' hpr' hm'
    · apply wp_unroll_group; intro Js_in hJs_in
      have hIn : ∀ (s'' : FullState) (m'' : Mem 64),
          FullDenseInvW c F0 F_cur s'' → TmkZero s'' →
          s''.core.cur_vars = s0.core.cur_vars → s''.core.arena = s0.core.arena →
          s''.core.arena_len = s0.core.arena_len →
          s''.core.fuel.toNat ≤ s0.core.fuel.toNat →
          (∀ i < 4002, s''.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]?) →
          (FullMem c s'' ⋆ R) m'' → Js_in () m'' := by
        intro s'' m'' hi'' ht'' hcv'' har'' hal'' hfl'' hpr'' hm''
        apply hJs_in; try dsimp only [Blocks.get, Member.here]
        c0_hsteps!; exact hOut s'' m'' hi'' ht'' hcv'' har'' hal'' hfl'' hpr'' hm''
      clear hJs_in
      apply wp_call_of_spec; apply hCertify
      dsimp only [vals, Arg.val]
      refine fidBveCertifyUnitSpec_intro rfl hi' ht' h16k
        (by rw [hsh.1]; exact by omega)
        hnp (by rw [show (0 : BitVec 32).toNat = 0 from rfl]; omega) (Or.inl rfl)
        (fun i hi => by
          rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_add, hsh.1]
          exact hpos' i hi)
        hm' ?_
      intro okp s'' m'' hi'' ht'' hcv'' har'' hal'' hfl'' hpr'' hm''
      have hpr_p : ∀ i < 4002, s''.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]? :=
        fun i hi => (hpr'' i (by omega)).trans (hpr' i hi)
      c0_hsplit
      · c0_hsteps!
        exact hIn s'' m'' hi'' ht'' (hcv''.trans hcv') (har''.trans har') (hal''.trans hal')
          (Nat.le_trans hfl'' hfl') hpr_p hm''
      · refine fid_def_k6_clear4130_wp s0 s'' hi'' ht'' (hcv''.trans hcv') (har''.trans har')
          (hal''.trans hal') (Nat.le_trans hfl'' hfl') h16k hpr_p hm'' ?_
        intro s3 m3 hi3 ht3 hcv3 har3 hal3 hfl3 hpr3 hm3
        c0_hsteps!; exact hIn s3 m3 hi3 ht3 hcv3 har3 hal3 hfl3 hpr3 hm3
    · exact hOut s' m' hi' ht' hcv' har' hal' hfl' hpr' hm'
  clear hJs_after
  c0_hsteps_nogrp
  · exact hAfter s2 m2 hinv2 htmk2 hcv2 har2 hal2 hfl2 hpos2 hpres2 hm2
  · apply wp_unroll_group; intro Js_in hJs_in
    have hIn : ∀ (s'' : FullState) (m'' : Mem 64),
        FullDenseInvW c F0 F_cur s'' → TmkZero s'' →
        s''.core.cur_vars = s0.core.cur_vars → s''.core.arena = s0.core.arena →
        s''.core.arena_len = s0.core.arena_len →
        s''.core.fuel.toNat ≤ s0.core.fuel.toNat →
        (∀ i < 4002, s''.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]?) →
        (FullMem c s'' ⋆ R) m'' → Js_in () m'' := by
      intro s'' m'' hi'' ht'' hcv'' har'' hal'' hfl'' hpr'' hm''
      apply hJs_in; try dsimp only [Blocks.get, Member.here]
      c0_hsteps!; exact hRet s'' m'' hi'' ht'' hcv'' har'' hal'' hfl'' hpr'' hm''
    clear hJs_in
    apply wp_call_of_spec; apply hCertify
    dsimp only [vals, Arg.val]
    have hnl : (v <<< 1#32 ||| 1#32).toNat = 2 * v.toNat + 1 := by
      change (v <<< 1 ||| 1#32).toNat = _; exact hsh.2
    refine fidBveCertifyUnitSpec_intro rfl hinv2 htmk2 h16k
      (by change (v <<< 1#32 ||| 1#32).toNat < 2 * s2.core.cur_vars; rw [hnl]; omega)
      hnn (by rw [show (2001 : BitVec 32).toNat = 2001 from rfl]; omega) (Or.inr rfl)
      (fun j hj => by
        rw [show (2001 : BitVec 32).toNat = 2001 from rfl]
        change FullBveEntryOkW F_cur s2 (v <<< 1#32 ||| 1#32).toNat _
        rw [hnl]
        exact hneg2 j hj)
      hm2 ?_
    intro okn s'' m'' hi'' ht'' hcv'' har'' hal'' hfl'' hpr'' hm''
    have hpr_n : ∀ i < 4002, s''.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]? :=
      fun i hi => (hpr'' i (by omega)).trans (hpres2 i hi)
    c0_hsplit
    · c0_hsteps!
      exact hIn s'' m'' hi'' ht'' (hcv''.trans hcv2) (har''.trans har2) (hal''.trans hal2)
        (Nat.le_trans hfl'' hfl2) hpr_n hm''
    · refine fid_def_k6_clear4130_wp s0 s'' hi'' ht'' (hcv''.trans hcv2) (har''.trans har2)
        (hal''.trans hal2) (Nat.le_trans hfl'' hfl2) h16k hpr_n hm'' ?_
      intro s3 m3 hi3 ht3 hcv3 har3 hal3 hfl3 hpr3 hm3
      c0_hsteps!; exact hIn s3 m3 hi3 ht3 hcv3 har3 hal3 hfl3 hpr3 hm3
  · exact hAfter s2 m2 hinv2 htmk2 hcv2 har2 hal2 hfl2 hpos2 hpres2 hm2

public section

/-- Certifies `m8BveGatesSpec` for `full_bve_def_k6_fid`. -/
theorem full_bve_def_k6_fid_wp (Γ : Env)
    (hMv : Γ.Has "full_bve_k6_mv_fid" fidBveK6MvSpec)
    (hExtract : Γ.Has "full_k6_extract_and_solve_fid" fidK6ExtractSolveSpec)
    (hCertify : Γ.Has "full_bve_certify_unit_fid" fidBveCertifyUnitSpec) :
    ∀ a m Q X, m8BveGatesSpec a m Q X →
      Func.wp Γ full_bve_def_k6_fid_body a m Q X := by
  rintro ⟨h, v, np, nn, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hinv, htmk0, h16k, hv, hnp, hnn, hpos, hneg, hm0, hQ⟩ :=
    m8BveGatesSpec_elim hSpec
  have hscr_lt : c.scratch_cap < 2 ^ 28 := c.hscr
  unfold Func.wp full_bve_def_k6_fid_body
  c0_hsteps_nogrp
  apply wp_call_of_spec; apply hMv
  refine fidBveK6MvSpec_intro ?_
  dsimp only [vals, Arg.val]
  rw [show (BitVec.ofNat 64 c.scratch_cap).toNat = c.scratch_cap from
    Nat.mod_eq_of_lt (by omega)]
  c0_hsteps_nogrp
  · exact fid_gates_inv_exit s0 hinv htmk0 rfl rfl rfl (Nat.le_refl _) (fun _ _ => rfl) hm0
      hnp hnn hQ
  · exact fid_gates_inv_exit s0 hinv htmk0 rfl rfl rfl (Nat.le_refl _) (fun _ _ => rfl) hm0
      hnp hnn hQ
  · exact fid_gates_inv_exit s0 hinv htmk0 rfl rfl rfl (Nat.le_refl _) (fun _ _ => rfl) hm0
      hnp hnn hQ
  · exact fid_gates_inv_exit s0 hinv htmk0 rfl rfl rfl (Nat.le_refl _) (fun _ _ => rfl) hm0
      hnp hnn hQ
  · apply wp_call_of_spec; apply hExtract
    refine fidK6ExtractSolveSpec_intro rfl hinv htmk0 h16k hv hnp hnn hpos hneg hm0 ?_
    intro ok1 s1 m1 hinv1 htmk1 hcv1 har1 hal1 hfl1 hpres1_lo _ hm1
    c0_hsplit
    · c0_hsteps_nogrp
      apply wp_call_of_spec; apply hExtract
      have hpos1 : ∀ i < np.toNat, FullBveEntryOkW F_cur s1 (2 * v.toNat)
          (s1.scratch.scratch_buf[i]?.getD 0#32) := fun i hi => by
        rw [hpres1_lo i (by omega)]
        exact m8_bveEntry_congr_core (hpos i hi) hcv1 har1 hal1
      have hneg1 : ∀ j < nn.toNat, FullBveEntryOkW F_cur s1 (2 * v.toNat + 1)
          (s1.scratch.scratch_buf[2001 + j]?.getD 0#32) := fun j hj => by
        rw [hpres1_lo (2001 + j) (by omega)]
        exact m8_bveEntry_congr_core (hneg j hj) hcv1 har1 hal1
      refine fidK6ExtractSolveSpec_intro rfl hinv1 htmk1 h16k (by rw [hcv1]; exact hv) hnp hnn
        hpos1 hneg1 hm1 ?_
      intro ok2 s2 m2 hinv2 htmk2 hcv2 har2 hal2 hfl2 hpres2_lo _ hm2
      have hpres2 : ∀ i < 4002, s2.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]? :=
        fun i hi => (hpres2_lo i hi).trans (hpres1_lo i hi)
      c0_hsplit
      · refine fid_def_k6_scan_wp (fidDefK6AfterScanExpr c v np nn) h16k
          hinv2.1.scratch_ok.scratch_buf_len hm2 ?_
        intro hp hn m2' hm2'
        have hpos2 : ∀ i < np.toNat, FullBveEntryOkW F_cur s2 (2 * v.toNat)
            (s2.scratch.scratch_buf[i]?.getD 0#32) := fun i hi => by
          rw [hpres2_lo i (by omega)]
          exact m8_bveEntry_congr_core (hpos1 i hi) hcv2 har2 hal2
        have hneg2 : ∀ j < nn.toNat, FullBveEntryOkW F_cur s2 (2 * v.toNat + 1)
            (s2.scratch.scratch_buf[2001 + j]?.getD 0#32) := fun j hj => by
          rw [hpres2_lo (2001 + j) (by omega)]
          exact m8_bveEntry_congr_core (hneg1 j hj) hcv2 har2 hal2
        exact fid_def_k6_post_extract2_wp hCertify s0 s2 hinv2 htmk2 (hcv2.trans hcv1)
          (har2.trans har1) (hal2.trans hal1) (Nat.le_trans hfl2 hfl1) h16k
          (by rw [hcv2, hcv1]; exact hv) hnp hnn hpos2 hneg2 hpres2 hm2' hQ
      · refine fid_def_k6_clear4130_wp s0 s2 hinv2 htmk2 (hcv2.trans hcv1) (har2.trans har1)
          (hal2.trans hal1) (Nat.le_trans hfl2 hfl1) h16k hpres2 hm2 ?_
        intro s3 m3 hi3 ht3 hcv3 har3 hal3 hfl3 hpr3 hm3
        c0_hsteps!
        exact fid_gates_inv_exit s0 hi3 ht3 hcv3 har3 hal3 hfl3 hpr3 hm3 hnp hnn hQ
    · c0_hsteps!
      exact fid_gates_inv_exit s0 hinv1 htmk1 hcv1 har1 hal1 hfl1 hpres1_lo hm1 hnp hnn hQ

/-! ## 3. `full_bve_gates_fid_wp` -/

/-- Certifies `m8BveGatesSpec` for `full_bve_gates_fid`. -/
theorem full_bve_gates_fid_wp (Γ : Env)
    (hEquiv : Γ.Has "full_bve_find_equiv_m8" Gates.m8BveFindEquivSpec)
    (hAnd : Γ.Has "full_bve_find_and_m8" Gates.m8BveFindAndSpec)
    (hIte : Γ.Has "full_bve_find_ite_m8" Gates.m8BveFindIteSpec)
    (hDefK6 : Γ.Has "full_bve_def_k6_fid" m8BveGatesSpec) :
    ∀ a m Q X, m8BveGatesSpec a m Q X →
      Func.wp Γ full_bve_gates_fid_body a m Q X := by
  rintro ⟨h, v, np, nn, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hinv, htmk0, h16k, hv, hnp, hnn, hpos, hneg, hm0, hQ⟩ :=
    m8BveGatesSpec_elim hSpec
  have hscr_len0 : s0.scratch.scratch_buf.length = c.scratch_cap :=
    hinv.1.scratch_ok.scratch_buf_len
  have hscr_lt : c.scratch_cap < 2 ^ 28 := c.hscr
  unfold Func.wp full_bve_gates_fid_body
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun p m => ∃ scr : List (BitVec 32), p.fst.toNat ≤ 130 ∧ scr.length = c.scratch_cap ∧
      (∀ k < 4002, scr[k]? = s0.scratch.scratch_buf[k]?) ∧
      (FullMem c (m8ScrSt s0 scr) ⋆ R) m)
    (fun p _ => 130 - p.fst.toNat) ?_ ?_
  · intro J hJ; c0_hsteps!
    refine hJ (0#32, ()) m0 ⟨s0.scratch.scratch_buf, Nat.zero_le _, hscr_len0, fun _ _ => rfl, ?_⟩
    rwa [m8ScrSt_self]
  · intro J ⟨i, ⟨⟩⟩ m ⟨scr, hi_le, hscr_len, hpres, hm⟩ hrec
    c0_hsplit
    · have hi : i.toNat < 130 := by c0_bound
      have hidx_bv : (BitVec.setWidth 64 (4002#32 + i)).toNat = 4002 + i.toNat := by bv_omega
      have hidx_lt : (BitVec.setWidth 64 (4002#32 + i)).toNat < scr.length := by omega
      c0_hsteps!
      refine hrec (i + 1, ()) _ (by bv_omega)
        ⟨scr.set (BitVec.setWidth 64 (4002#32 + i)).toNat 0#32, by bv_omega,
          by rw [List.length_set, hscr_len],
          fun k hk => by rw [List.getElem?_set_ne (by rw [hidx_bv]; omega)]; exact hpres k hk,
          ‹_›⟩
    · let s1 : FullState := m8ScrSt s0 scr
      have hinv1 : FullDenseInvW c F0 F_cur s1 := m8_fullDenseInvW_scr hinv hscr_len
      have hpos1 : ∀ j < np.toNat, FullBveEntryOkW F_cur s1 (2 * v.toNat)
          (s1.scratch.scratch_buf[j]?.getD 0#32) := fun j hj => by
        simp only [s1, m8ScrSt, hpres j (by omega)]
        exact m8_bveEntry_congr_core (hpos j hj) rfl rfl rfl
      have hneg1 : ∀ j < nn.toNat, FullBveEntryOkW F_cur s1 (2 * v.toNat + 1)
          (s1.scratch.scratch_buf[2001 + j]?.getD 0#32) := fun j hj => by
        simp only [s1, m8ScrSt, hpres (2001 + j) (by omega)]
        exact m8_bveEntry_congr_core (hneg j hj) rfl rfl rfl
      have hbin1 : ∀ k < np.toNat,
          have w := s1.scratch.scratch_buf[k]?.getD 0#32
          (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s1.core.cur_vars :=
        fun k hk hbit => fid_gates_entry_bin_bounds (hpos1 k hk) hbit
      have hbin2 : ∀ k < nn.toNat,
          have w := s1.scratch.scratch_buf[2001 + k]?.getD 0#32
          (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s1.core.cur_vars :=
        fun k hk hbit => fid_gates_entry_bin_bounds (hneg1 k hk) hbit
      c0_hsplit
      · c0_hsteps!
        exact fid_gates_inv_exit s0 hinv1 htmk0 rfl rfl rfl (Nat.le_refl _) hpres hm hnp hnn hQ
      · c0_hsplit
        · c0_hsteps!
          exact fid_gates_inv_exit s0 hinv1 htmk0 rfl rfl rfl (Nat.le_refl _) hpres hm hnp hnn hQ
        · apply wp_call_of_spec; apply hEquiv
          refine m8BveFindEquivSpec_intro rfl hinv1 h16k hnp hnn hbin1 hbin2 hm ?_
          intro ok1 lm1 scr1 m1 _ hinv_e hlen1 hpres1 hm1
          let s_e : FullState :=
            { s1 with core := { s1.core with lit_mark := lm1 }
                      scratch := { s1.scratch with scratch_buf := scr1 } }
          have hpres_e : ∀ k < 4002, s_e.scratch.scratch_buf[k]? = s0.scratch.scratch_buf[k]? :=
            fun k hk => (hpres1 k (by omega) (Or.inl hk)).trans (hpres k hk)
          have hpos_e : ∀ j < np.toNat, FullBveEntryOkW F_cur s_e (2 * v.toNat)
              (s_e.scratch.scratch_buf[j]?.getD 0#32) := fun j hj => by
            simp only [s_e, hpres1 j (by omega) (Or.inl (by omega))]
            exact m8_bveEntry_congr_core (hpos1 j hj) rfl rfl rfl
          have hneg_e : ∀ j < nn.toNat, FullBveEntryOkW F_cur s_e (2 * v.toNat + 1)
              (s_e.scratch.scratch_buf[2001 + j]?.getD 0#32) := fun j hj => by
            simp only [s_e, hpres1 (2001 + j) (by omega) (Or.inl (by omega))]
            exact m8_bveEntry_congr_core (hneg1 j hj) rfl rfl rfl
          c0_hsplit
          · c0_hsteps!
            exact fid_gates_inv_exit s0 hinv_e htmk0 rfl rfl rfl (Nat.le_refl _)
              hpres_e hm1 hnp hnn hQ
          · have hcv_lt : 2 * s_e.core.cur_vars + 1 < 2 ^ 30 := by
              have hcv_le := hinv_e.1.core_ok.cur_vars_le
              have hmax := c.hmaxv
              change s_e.core.cur_vars ≤ c.max_vars at hcv_le
              simp only [dimacsBound] at hmax; omega
            have hl_eq := fid_k6c_bv32_shl1_add1_lt hv hcv_lt
            have hxor := fid_gates_shl1_xor1 hv hcv_lt
            c0_hsteps_nogrp
            apply wp_call_of_spec; apply hAnd
            dsimp only [vals, Arg.val]
            rw [show (OfNat.ofNat 1 : Nat) = 1 from rfl, show (1 : BitVec 32) = 1#32 from rfl]
            refine m8BveFindAndSpec_intro rfl hinv_e h16k hnp hnn
              (fun j hj => by
                rw [ite_eq_right (by intro hn; exact hn fid_gates_and_1_eq.1),
                  Nat.zero_add, hl_eq.1]
                exact hpos_e j hj)
              (fun j hj => by
                rw [ite_eq_right (by intro hn; exact hn fid_gates_and_1_eq.1), hxor.1]
                exact hneg_e j hj)
              hm1 ?_
            intro ok2 lm2 scr2 m2 _ hinv_a1 hlen2 hpres2 hm2
            let s_a1 : FullState :=
              { s_e with core := { s_e.core with lit_mark := lm2 }
                         scratch := { s_e.scratch with scratch_buf := scr2 } }
            have hpres_a1 : ∀ k < 4002,
                s_a1.scratch.scratch_buf[k]? = s0.scratch.scratch_buf[k]? :=
              fun k hk => (hpres2 k (by omega) (Or.inl hk)).trans (hpres_e k hk)
            have hpos_a1 : ∀ j < np.toNat, FullBveEntryOkW F_cur s_a1 (2 * v.toNat)
                (s_a1.scratch.scratch_buf[j]?.getD 0#32) := fun j hj => by
              simp only [s_a1, hpres2 j (by omega) (Or.inl (by omega))]
              exact m8_bveEntry_congr_core (hpos_e j hj) rfl rfl rfl
            have hneg_a1 : ∀ j < nn.toNat, FullBveEntryOkW F_cur s_a1 (2 * v.toNat + 1)
                (s_a1.scratch.scratch_buf[2001 + j]?.getD 0#32) := fun j hj => by
              simp only [s_a1, hpres2 (2001 + j) (by omega) (Or.inl (by omega))]
              exact m8_bveEntry_congr_core (hneg_e j hj) rfl rfl rfl
            c0_hsplit
            · c0_hsteps!
              exact fid_gates_inv_exit s0 hinv_a1 htmk0 rfl rfl rfl (Nat.le_refl _)
                hpres_a1 hm2 hnp hnn hQ
            · apply wp_call_of_spec; apply hAnd
              dsimp only [vals, Arg.val]
              refine m8BveFindAndSpec_intro rfl hinv_a1 h16k hnn hnp
                (fun j hj => by
                  rw [ite_eq_left (by rw [fid_gates_and_1_eq.2]; decide), hl_eq.2]
                  exact hneg_a1 j hj)
                (fun j hj => by
                  rw [ite_eq_left (by rw [fid_gates_and_1_eq.2]; decide), Nat.zero_add, hxor.2]
                  exact hpos_a1 j hj)
                hm2 ?_
              intro ok3 lm3 scr3 m3 _ hinv_a2 hlen3 hpres3 hm3
              let s_a2 : FullState :=
                { s_a1 with core := { s_a1.core with lit_mark := lm3 }
                            scratch := { s_a1.scratch with scratch_buf := scr3 } }
              have hpres_a2 : ∀ k < 4002,
                  s_a2.scratch.scratch_buf[k]? = s0.scratch.scratch_buf[k]? :=
                fun k hk => (hpres3 k (by omega) (Or.inl hk)).trans (hpres_a1 k hk)
              have hpos_a2 : ∀ j < np.toNat, FullBveEntryOkW F_cur s_a2 (2 * v.toNat)
                  (s_a2.scratch.scratch_buf[j]?.getD 0#32) := fun j hj => by
                simp only [s_a2, hpres3 j (by omega) (Or.inl (by omega))]
                exact m8_bveEntry_congr_core (hpos_a1 j hj) rfl rfl rfl
              have hneg_a2 : ∀ j < nn.toNat, FullBveEntryOkW F_cur s_a2 (2 * v.toNat + 1)
                  (s_a2.scratch.scratch_buf[2001 + j]?.getD 0#32) := fun j hj => by
                simp only [s_a2, hpres3 (2001 + j) (by omega) (Or.inl (by omega))]
                exact m8_bveEntry_congr_core (hneg_a1 j hj) rfl rfl rfl
              c0_hsplit
              · c0_hsteps!
                exact fid_gates_inv_exit s0 hinv_a2 htmk0 rfl rfl rfl (Nat.le_refl _)
                  hpres_a2 hm3 hnp hnn hQ
              · apply wp_call_of_spec; apply hIte
                refine m8BveFindIteSpec_intro rfl hinv_a2 h16k hv hnp hnn hpos_a2 hneg_a2 hm3 ?_
                intro ok4 scr4 m4 _ hlen4 hpres4 hm4
                let s_i : FullState :=
                  { s_a2 with scratch := { s_a2.scratch with scratch_buf := scr4 } }
                have hinv_i : FullDenseInvW c F0 F_cur s_i := m8_fullDenseInvW_scr hinv_a2 hlen4
                have hpres_i : ∀ k < 4002,
                    s_i.scratch.scratch_buf[k]? = s0.scratch.scratch_buf[k]? :=
                  fun k hk => (hpres4 k (by omega) (Or.inl hk)).trans (hpres_a2 k hk)
                have hpos_i : ∀ j < np.toNat, FullBveEntryOkW F_cur s_i (2 * v.toNat)
                    (s_i.scratch.scratch_buf[j]?.getD 0#32) := fun j hj => by
                  simp only [s_i, hpres4 j (by omega) (Or.inl (by omega))]
                  exact m8_bveEntry_congr_core (hpos_a2 j hj) rfl rfl rfl
                have hneg_i : ∀ j < nn.toNat, FullBveEntryOkW F_cur s_i (2 * v.toNat + 1)
                    (s_i.scratch.scratch_buf[2001 + j]?.getD 0#32) := fun j hj => by
                  simp only [s_i, hpres4 (2001 + j) (by omega) (Or.inl (by omega))]
                  exact m8_bveEntry_congr_core (hneg_a2 j hj) rfl rfl rfl
                c0_hsplit
                · c0_hsteps!
                  exact fid_gates_inv_exit s0 hinv_i htmk0 rfl rfl rfl (Nat.le_refl _)
                    hpres_i hm4 hnp hnn hQ
                · apply wp_call_of_spec; apply hDefK6
                  refine m8BveGatesSpec_intro rfl hinv_i htmk0 h16k hv hnp hnn hpos_i hneg_i hm4 ?_
                  intro s' m' hinv' htmk' hcv' har' harl' hfl' hsp hsn hm'
                  c0_hsteps!
                  exact hQ s' m' hinv' htmk' hcv' har' harl' hfl'
                    (fun i hi => (hsp i hi).trans (hpres_i i (by omega)))
                    (fun j hj => (hsn j hj).trans (hpres_i (2001 + j) (by omega)))
                    hm'

end

end LeanQbe.T.Examples.Kissat.Proof.Definition
