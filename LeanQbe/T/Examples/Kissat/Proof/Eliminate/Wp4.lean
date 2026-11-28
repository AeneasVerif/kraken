/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Helpers
public import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Spec
public import LeanQbe.T.Examples.Kissat.Src.Eliminate
public import LeanQbe.T.Examples.Kissat.Proof.Dense.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Forward.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Internal.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat BVE & Elimination Top-Level `Func.wp` Proofs (`Wp4`)

Clean `CanonicalEnv` `Func.wp` proofs (`0` legacy `Full*` imports, `0` `@[expose]` on theorems/
sections, `<= 100` cols, every decl `<= 450`L, `<= 1,500`L total):
1. `full_elim_bve_m7_wp` (`Spec.fullElimBveM7Spec`)
2. `full_has_elim_cands_fid_wp` (`Spec.fullHasElimCandsFidSpec`)
3. `full_eliminate_m6_wp` (`Spec.fullEliminateM6Spec`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Eliminate

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Eliminate
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
open LeanQbe.T.Examples.Kissat.Proof.Eliminate.EliminateTactics
open Kraken.Bedrock2.Test

open scoped FullArenaTactics
open scoped EliminateTactics

/-! ## 1. Shared Invariant Helpers -/

private theorem elim_denseInv_with_resSz {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) (v : BitVec 64) :
    FullDenseInv c F0 { s with scratch := { s.scratch with res_sz := v } } :=
  fullDenseInv_with_scratch_keep h
    { h.lengths.scratch_ok with walk_vals_len := h.lengths.scratch_ok.walk_vals_len } rfl rfl

private theorem elim_denseInv_with_elimBound {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) (v : BitVec 64) :
    FullDenseInv c F0 { s with scratch := { s.scratch with elim_bound := v } } :=
  fullDenseInv_with_scratch_keep h
    { h.lengths.scratch_ok with walk_vals_len := h.lengths.scratch_ok.walk_vals_len } rfl rfl

private theorem elim_denseInv_with_tmk {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {tmki : List (BitVec 32)} (ht : tmki.length = 2 * c.max_vars) :
    FullDenseInv c F0 { s with scratch := { s.scratch with tarjan_mark := tmki } } :=
  fullDenseInv_with_scratch_keep h
    { h.lengths.scratch_ok with tarjan_mark_len := ht } rfl rfl

private theorem elim_denseInv_with_fwdSub {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) (v : BitVec 64) :
    FullDenseInv c F0 { s with scratch := { s.scratch with fwd_sub_cnt := v } } :=
  fullDenseInv_with_scratch_keep h
    { h.lengths.scratch_ok with walk_vals_len := h.lengths.scratch_ok.walk_vals_len } rfl rfl

private theorem elim_sparseInv_with_scr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {sc' : FullScratch} (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hel : sc'.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0 { s with scratch := sc' } :=
  fullSparseInv_of_core_eq h ⟨h.lengths.core_ok, hok⟩ rfl ⟨hll, hel⟩

/-! ## 2. `full_elim_bve_m7_wp` Helpers & Proof -/

private theorem elim_bve_round_br_wp (Γ : Env) (c : FullCfg) (F0 : CNF Nat)
    (R : Mem 64 → Prop) (s0 sb : FullState) (res_lim : Val i64)
    (hl0 : Bool) (hln0 : Val i64) (lre0 : Bool) (rd0 : Val i64) (mb : Mem 64)
    (Q : Post [i64]) (X : XPost)
    (hQ : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullDenseInv c F0 s' → TmkZero s' → s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      r = 1#64 ∨ r = 20#64 → (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hdenb : FullDenseInv c F0 sb) (htmkb : TmkZero sb)
    (hfub : sb.core.fuel.toNat ≤ s0.core.fuel.toNat) (hmb : (FullMem c sb ⋆ R) mb) :
    wp Γ Q X
      ((Blocks.cons (fun (p : Tup Val [.bool, i64, .bool, i64]) =>
        Expr.group (fun (_Js : Tup Cont [[]]) =>
          Blocks.cons (fun (_p : Tup Val []) =>
            Expr.group (fun (_Js : Tup Cont [[i64]]) =>
              Blocks.cons (fun (p : Tup Val [i64]) => Expr.ret (Arg.var p.fst, ()))
                Blocks.nil) fun Js =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 1024, ())) fun p =>
            Expr.load i64 (Arg.var p.fst) fun ld =>
            Expr.let_ (Op.mk (OpCode.cmp CmpOp.ne i64 Ty.bool (by decide))
              (Arg.var ld, Arg.imm 0, ())) fun p =>
            Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.imm 20, ()))
              (Expr.jump Js.fst (Arg.imm 1, ()))) Blocks.nil) fun Js =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 1024, ())) fun p_1 =>
        Expr.load i64 (Arg.var p_1.fst) fun ld =>
        Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i64 Ty.bool (by decide))
          (Arg.var ld, Arg.imm 0, ())) fun p_2 =>
        Expr.jnz (Arg.var p_2.fst)
          (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 776, ())) fun p_3 =>
          Expr.load i64 (Arg.var p_3.fst) fun ld =>
          Expr.group (fun (_Js_1 : Tup Cont [[.bool]]) =>
            Blocks.cons (fun (p : Tup Val [.bool]) =>
              Expr.group (fun (_Js_2 : Tup Cont [[]]) =>
                Blocks.cons (fun (_p : Tup Val []) => Expr.jump Js.fst ()) Blocks.nil) fun Js =>
              Expr.jnz (Arg.var p.fst)
                (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 1008, ())) fun p =>
                Expr.load i64 (Arg.var p.fst) fun ld_1 =>
                Expr.group (fun (_Js_2 : Tup Cont [[]]) =>
                  Blocks.cons (fun (_p : Tup Val []) => Expr.jump Js.fst ()) Blocks.nil) fun Js =>
                Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i64 Ty.bool (by decide))
                  (Arg.var ld_1, Arg.imm 16, ())) fun p =>
                Expr.jnz (Arg.var p.fst)
                  (Expr.group (fun (_Js_2 : Tup Cont [[i64]]) =>
                    Blocks.cons (fun (p : Tup Val [i64]) =>
                      Expr.group (fun (_Js_3 : Tup Cont [[i64]]) =>
                        Blocks.cons (fun (p : Tup Val [i64]) =>
                          Expr.let_ (Op.mk (OpCode.add i64)
                            (Arg.var c.hdr, Arg.imm 1008, ())) fun p_4 =>
                          Expr.store (Arg.var p.fst) (Arg.var p_4.fst)
                            (Expr.group (fun (Js_4 : Tup Cont [[i64]]) =>
                              Blocks.cons (fun (p : Tup Val [i64]) =>
                                Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i64 Ty.bool (by decide))
                                  (Arg.var p.fst, Arg.var ld, ())) fun p_5 =>
                                Expr.jnz (Arg.var p_5.fst)
                                  (Expr.let_ (Op.mk (OpCode.mul i64)
                                    (Arg.var p.fst, Arg.imm 4, ())) fun p_6 =>
                                  Expr.let_ (Op.mk (OpCode.add i64)
                                    (Arg.var c.pFlags, Arg.var p_6.fst, ())) fun p_7 =>
                                  Expr.let_ (Op.mk (OpCode.mul i64)
                                    (Arg.var p.fst, Arg.imm 4, ())) fun p_8 =>
                                  Expr.let_ (Op.mk (OpCode.add i64)
                                    (Arg.var c.pFlags, Arg.var p_8.fst, ())) fun p_9 =>
                                  Expr.load i32 (Arg.var p_9.fst) fun ld =>
                                  Expr.let_ (Op.mk (OpCode.or i32)
                                    (Arg.var ld, Arg.imm 16, ())) fun p_10 =>
                                  Expr.store (Arg.var p_10.fst) (Arg.var p_7.fst)
                                    (Expr.let_ (Op.mk (OpCode.add i64)
                                      (Arg.var p.fst, Arg.imm 1, ())) fun p =>
                                    Expr.jump Js_4.fst (Arg.var p.fst, ())))
                                  (Expr.jump Js.fst ())) Blocks.nil) fun Js =>
                            Expr.jump Js.fst (Arg.imm 0, ()))) Blocks.nil) fun Js =>
                      Expr.let_ (Op.mk (OpCode.cmp CmpOp.ugt i64 Ty.bool (by decide))
                        (Arg.var p.fst, Arg.imm 16, ())) fun p_4 =>
                      Expr.jnz (Arg.var p_4.fst) (Expr.jump Js.fst (Arg.imm 16, ()))
                        (Expr.jump Js.fst (Arg.var p.fst, ()))) Blocks.nil) fun Js =>
                  Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i64 Ty.bool (by decide))
                    (Arg.var ld_1, Arg.imm 0, ())) fun p =>
                  Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.imm 1, ()))
                    (Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm 1, ())) fun p =>
                    Expr.let_ (Op.mk (OpCode.shl i64) (Arg.var ld_1, Arg.var p.fst, ())) fun p =>
                    Expr.jump Js.fst (Arg.var p.fst, ()))) (Expr.jump Js.fst ()))
                (Expr.group (fun (Js_2 : Tup Cont [[i64]]) =>
                  Blocks.cons (fun (p : Tup Val [i64]) =>
                    Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i64 Ty.bool (by decide))
                      (Arg.var p.fst, Arg.var ld, ())) fun p_4 =>
                    Expr.jnz (Arg.var p_4.fst)
                      (Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p_5 =>
                      Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pFlags, Arg.var p_5.fst, ())) fun p_6 =>
                      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p_7 =>
                      Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pFlags, Arg.var p_7.fst, ())) fun p_8 =>
                      Expr.load i32 (Arg.var p_8.fst) fun ld =>
                      Expr.let_ (Op.mk (OpCode.not i32) (Arg.imm 16, ())) fun p_9 =>
                      Expr.let_ (Op.mk (OpCode.and i32) (Arg.var ld, Arg.var p_9.fst, ()))
                        fun p_10 =>
                      Expr.store (Arg.var p_10.fst) (Arg.var p_6.fst)
                        (Expr.let_ (Op.mk (OpCode.add i64)
                          (Arg.var p.fst, Arg.imm 1, ())) fun p =>
                        Expr.jump Js_2.fst (Arg.var p.fst, ()))) (Expr.jump Js.fst ()))
                    Blocks.nil) fun Js =>
                Expr.jump Js.fst (Arg.imm 0, ()))) Blocks.nil) fun Js =>
          Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.imm false, ()))
            (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 1144, ())) fun p_4 =>
            Expr.load i64 (Arg.var p_4.fst) fun ld =>
            Expr.let_ (Op.mk (OpCode.cmp CmpOp.ule i64 Ty.bool (by decide))
              (Arg.var ld, Arg.var res_lim, ())) fun p_5 =>
            Expr.jnz (Arg.var p_5.fst)
              (Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i64 Ty.bool (by decide))
                (Arg.var p.snd.fst, Arg.imm 0, ())) fun p_6 =>
              Expr.jnz (Arg.var p_6.fst)
                (Expr.jnz (Arg.var p.snd.snd.fst) (Expr.jump Js.fst (Arg.imm false, ()))
                  (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 760, ())) fun p =>
                  Expr.load i64 (Arg.var p.fst) fun ld =>
                  Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i64 Ty.bool (by decide))
                    (Arg.var ld, Arg.imm 0, ())) fun p =>
                  Expr.jnz (Arg.var p.fst)
                    (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 168, ())) fun p =>
                    Expr.load i64 (Arg.var p.fst) fun ld =>
                    Expr.let_ (Op.mk (OpCode.cmp CmpOp.ugt i64 Ty.bool (by decide))
                      (Arg.var ld, Arg.imm 0, ())) fun p =>
                    Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.imm true, ()))
                      (Expr.jump Js.fst (Arg.imm false, ())))
                    (Expr.jump Js.fst (Arg.imm false, ()))))
                (Expr.jump Js.fst (Arg.imm false, ())))
              (Expr.jump Js.fst (Arg.imm false, ()))))
          (Expr.jump Js.fst ())) Blocks.nil).get Member.here (hl0, hln0, lre0, rd0, ())) mb := by
  c0_hsteps_nogrp
  refine wp_join0 (P := fun mf => ∃ sf : FullState,
    FullDenseInv c F0 sf ∧ TmkZero sf ∧ sf.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
    (FullMem c sf ⋆ R) mf)
    (fun _ mf ⟨sf, hdenf, htmkf, hfuf, hmf⟩ => by
      c0_hsteps!
      · exact hQ 20#64 sf mf hdenf htmkf hfuf (Or.inr rfl)
          (fun _ => hdenf.inconsistent_unsat hc) hmf
      · exact hQ 1#64 sf mf hdenf htmkf hfuf (Or.inl rfl) (fun h => by cases h) hmf)
    (fun Jf hJf => by
      c0_hsplit
      · have hmx := c.hmaxv; unfold dimacsBound at hmx
        have hcvb := hdenb.lengths.core_ok.cur_vars_le
        have hflb := hdenb.lengths.core_ok.flags_len
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ())) (fun _ => True)
          (fun _ comp _ => by
            c0_hsteps_nogrp
            refine wp_join0 (P := fun mj => ∃ sj : FullState,
                FullDenseInv c F0 sj ∧ TmkZero sj ∧ sj.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
                (FullMem c sj ⋆ R) mj)
              (fun _ mj h => by c0_hsteps!; exact hJf mj h)
              (fun _ hJc => by
                c0_hsplit
                · c0_hsteps_nogrp
                  refine wp_join0 (P := fun mj => ∃ sj : FullState,
                      FullDenseInv c F0 sj ∧ TmkZero sj ∧
                      sj.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sj ⋆ R) mj)
                    (fun _ mj h => by c0_hsteps!; exact hJc mj h)
                    (fun _ hJc2 => by
                      c0_hsplit
                      · c0_hsteps_nogrp
                        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                          (fun x => (x, ())) (fun _ => True)
                          (fun _ nb0 _ => by
                            c0_hsteps_nogrp
                            refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                              (fun x => (x, ())) (fun _ => True)
                              (fun _ nb _ => by
                                c0_hsteps_nogrp
                                let sb1 : FullState :=
                                  { sb with scratch := { sb.scratch with elim_bound := nb } }
                                have hden1 : FullDenseInv c F0 sb1 :=
                                  elim_denseInv_with_elimBound hdenb nb
                                refine wp_loop_group (ts := [i64])
                                  (fun rem_k (k, ()) mk => ∃ flk : List (BitVec 32),
                                    flk.length = c.max_vars ∧ k.toNat ≤ sb.core.cur_vars ∧
                                    rem_k = sb.core.cur_vars - k.toNat ∧
                                    (FullMem c
                                      { sb1 with core := { sb1.core with flags := flk } } ⋆ R) mk)
                                  ?_ ?_
                                · rintro Lk rem_k ⟨k, ⟨⟩⟩ mk hLk ⟨flk, hflk, hk_le, rfl, hmk⟩
                                  c0_hsplit
                                  · have hk_lt : k.toNat < sb.core.cur_vars := by
                                      rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                                    have hk_b : k.toNat < flk.length := by omega
                                    have hk1 : (k + 1#64).toNat = k.toNat + 1 := by c0_bound
                                    c0_hsteps!
                                    exact hLk (sb.core.cur_vars - (k + 1#64).toNat)
                                      (k + 1#64, ()) _ (by omega)
                                      ⟨_, by simp [hflk], by omega, rfl, hm⟩
                                  · c0_hsteps!
                                    let sf : FullState :=
                                      { sb1 with core := { sb1.core with flags := flk } }
                                    exact hJc2 mk ⟨sf, fullDenseInv_with_flags hden1 hflk,
                                      tmkZero_congr htmkb rfl rfl, hfub, hmk⟩
                                · intro Lk hLk; c0_hsteps!
                                  exact hLk sb.core.cur_vars (0#64, ()) _
                                    ⟨sb.core.flags, hflb, Nat.zero_le _, by simp, hm⟩)
                              (fun Jm hJm => by c0_hsplit <;> (c0_hsteps!; exact hJm _ trivial)))
                          (fun Jb hJb => by c0_hsplit <;> (c0_hsteps!; exact hJb _ trivial))
                      · c0_hsteps!; exact hJc2 mb ⟨sb, hdenb, htmkb, hfub, hmb⟩)
                · c0_hsteps_nogrp
                  refine wp_loop_group (ts := [i64])
                    (fun rem_k (k, ()) mk => ∃ flk : List (BitVec 32),
                      flk.length = c.max_vars ∧ k.toNat ≤ sb.core.cur_vars ∧
                      rem_k = sb.core.cur_vars - k.toNat ∧
                      (FullMem c { sb with core := { sb.core with flags := flk } } ⋆ R) mk)
                    ?_ ?_
                  · rintro Lk rem_k ⟨k, ⟨⟩⟩ mk hLk ⟨flk, hflk, hk_le, rfl, hmk⟩
                    c0_hsplit
                    · have hk_lt : k.toNat < sb.core.cur_vars := by
                        rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                      have hk_b : k.toNat < flk.length := by omega
                      have hk1 : (k + 1#64).toNat = k.toNat + 1 := by c0_bound
                      c0_hsteps!
                      exact hLk (sb.core.cur_vars - (k + 1#64).toNat) (k + 1#64, ()) _ (by omega)
                        ⟨_, by simp [hflk], by omega, rfl, hm⟩
                    · c0_hsteps!
                      let sf : FullState := { sb with core := { sb.core with flags := flk } }
                      exact hJc mk ⟨sf, fullDenseInv_with_flags hdenb hflk,
                        tmkZero_congr htmkb rfl rfl, hfub, hmk⟩
                  · intro Lk hLk; c0_hsteps!
                    exact hLk sb.core.cur_vars (0#64, ()) mb
                      ⟨sb.core.flags, hflb, Nat.zero_le _, by simp, hmb⟩))
          (fun Jc hJc => by c0_hsteps! <;> exact hJc _ trivial)
      · c0_hsteps!; exact hJf mb ⟨sb, hdenb, htmkb, hfub, hmb⟩)

private theorem elim_bve_post_flush_wp (Γ : Env)
    (hPush : Γ.Has "full_bve_heap_push_m7" Spec.fullBveHeapPushM7Spec)
    (c : FullCfg) (F0 : CNF Nat) (R : Mem 64 → Prop)
    (hl_h nn bve0 : Val i64) (re_h ok_f : Bool) (s0 sh s5 : FullState) (m5 : Mem 64)
    (Q : Post [i64]) (X : XPost) (Lh : Cont [i64, .bool])
    (hQ : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullDenseInv c F0 s' → TmkZero s' → s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      r = 1#64 ∨ r = 20#64 → (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hLh : ∀ rem_h (ys : Tup Val [i64, .bool]) mh,
      rem_h < sh.core.fuel.toNat * (c.max_vars + 1) + hl_h.toNat →
      (match ys with
        | (hl_h, _re_h, ()) => ∃ sh' : FullState,
          hl_h.toNat ≤ sh'.core.cur_vars ∧
          rem_h = sh'.core.fuel.toNat * (c.max_vars + 1) + hl_h.toNat ∧
          FullDenseInv c F0 sh' ∧ TmkZero sh' ∧ sh'.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
          (FullMem c sh' ⋆ R) mh) →
      Lh ys mh)
    (hnn_mv : nn.toNat ≤ c.max_vars)
    (hden5 : FullDenseInv c F0 s5) (htmk5' : TmkZero s5)
    (hsh_fu_pos : 0 < sh.core.fuel.toNat)
    (hsh_fu_le : sh.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hfu5_dec : s5.core.fuel.toNat ≤ sh.core.fuel.toNat - 1)
    (hfu5' : s5.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hfu5_uns : ok_f = false → F0.Unsat)
    (hhl_s5 : (hl_h - 1#64).toNat ≤ s5.core.cur_vars) (hm5 : (FullMem c s5 ⋆ R) m5) :
    wp Γ Q X
      (Expr.jnz (Arg.var ok_f)
        (Expr.group (fun (_Js : Tup Cont [[i64, .bool]]) =>
          Blocks.cons (fun (p : Tup Val [i64, .bool]) =>
            Expr.jump Lh (Arg.var p.fst, Arg.var p.snd.fst, ())) Blocks.nil) fun Js =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 1088, ())) fun p =>
        Expr.load i64 (Arg.var p.fst) fun ld =>
        Expr.let_ (Op.mk (OpCode.cmp CmpOp.ugt i64 Ty.bool (by decide))
          (Arg.var ld, Arg.var bve0, ())) fun p =>
        Expr.jnz (Arg.var p.fst)
          (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 776, ())) fun p =>
          Expr.load i64 (Arg.var p.fst) fun ld =>
          Expr.group (fun (Js_1 : Tup Cont [[i64, i64]]) =>
            Blocks.cons (fun (p : Tup Val [i64, i64]) =>
              Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i64 Ty.bool (by decide))
                (Arg.var p.snd.fst, Arg.var nn, ())) fun p_1 =>
              Expr.jnz (Arg.var p_1.fst)
                (Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p.snd.fst, Arg.imm 4, ())) fun p_2 =>
                Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pWorkStk2, Arg.var p_2.fst, ()))
                  fun p_3 =>
                Expr.load i32 (Arg.var p_3.fst) fun ld_1 =>
                Expr.group (fun (_Js : Tup Cont [[i64]]) =>
                  Blocks.cons (fun (p_4 : Tup Val [i64]) =>
                    Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p.snd.fst, Arg.imm 1, ())) fun p =>
                    Expr.jump Js_1.fst (Arg.var p_4.fst, Arg.var p.fst, ())) Blocks.nil) fun Js =>
                Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld_1, ())) fun p_4 =>
                Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i64 Ty.bool (by decide))
                  (Arg.var p_4.fst, Arg.var ld, ())) fun p_5 =>
                Expr.jnz (Arg.var p_5.fst)
                  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld_1, ())) fun p_6 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_6.fst, Arg.imm 4, ())) fun p_7 =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pFlags, Arg.var p_7.fst, ()))
                    fun p_8 =>
                  Expr.load i32 (Arg.var p_8.fst) fun ld =>
                  Expr.let_ (Op.mk (OpCode.and i32) (Arg.var ld, Arg.imm 1, ())) fun p_9 =>
                  Expr.let_ (Op.mk (OpCode.cmp CmpOp.ne i32 Ty.bool (by decide))
                    (Arg.var p_9.fst, Arg.imm 0, ())) fun p_10 =>
                  Expr.jnz (Arg.var p_10.fst)
                    (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld_1, ())) fun p_11 =>
                    Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm 1, ())) fun p_12 =>
                    Expr.let_ (Op.mk (OpCode.shl i64) (Arg.var p_11.fst, Arg.var p_12.fst, ()))
                      fun p_13 =>
                    Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pVals, Arg.var p_13.fst, ()))
                      fun p_14 =>
                    Expr.load i8 (Arg.var p_14.fst) fun ld =>
                    Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p_15 =>
                    Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var ld, ())) fun p_16 =>
                    Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p_15.fst, ())) fun p_17 =>
                    Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i32 Ty.bool (by decide))
                      (Arg.var p_16.fst, Arg.var p_17.fst, ())) fun p_18 =>
                    Expr.jnz (Arg.var p_18.fst)
                      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld_1, ())) fun p_19 =>
                      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_19.fst, Arg.imm 4, ()))
                        fun p_20 =>
                      Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pFlags, Arg.var p_20.fst, ())) fun p_21 =>
                      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld_1, ())) fun p_22 =>
                      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_22.fst, Arg.imm 4, ()))
                        fun p_23 =>
                      Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pFlags, Arg.var p_23.fst, ())) fun p_24 =>
                      Expr.load i32 (Arg.var p_24.fst) fun ld =>
                      Expr.let_ (Op.mk (OpCode.or i32) (Arg.var ld, Arg.imm 16, ())) fun p_25 =>
                      Expr.store (Arg.var p_25.fst) (Arg.var p_21.fst)
                        (Expr.call (as := [i64, i64, i32]) (bs := [i64]) "full_bve_heap_push_m7"
                          (Arg.var c.hdr, Arg.var p.fst, Arg.var ld_1, ()) fun p =>
                        Expr.jump Js.fst (Arg.var p.fst, ())))
                      (Expr.jump Js.fst (Arg.var p.fst, ())))
                    (Expr.jump Js.fst (Arg.var p.fst, ())))
                  (Expr.jump Js.fst (Arg.var p.fst, ())))
                (Expr.jump Js.fst (Arg.var p.fst, Arg.imm true, ()))) Blocks.nil) fun Js =>
          Expr.jump Js.fst (Arg.var (hl_h - 1#64), Arg.imm 0, ()))
          (Expr.jump Js.fst (Arg.var (hl_h - 1#64), Arg.var re_h, ())))
        (Expr.ret (Arg.imm 20, ()))) m5 := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  c0_hsplit
  · have hcont_4 : ∀ (hl_f : BitVec 64) (re_f : Bool) (sf : FullState) (mf : Mem 64),
        hl_f.toNat ≤ sf.core.cur_vars → FullDenseInv c F0 sf → TmkZero sf →
        sf.core.fuel.toNat ≤ sh.core.fuel.toNat - 1 → (FullMem c sf ⋆ R) mf →
        Lh (hl_f, re_f, ()) mf :=
      fun hl_f re_f sf mf hhlf hdenf htmkf hfuf hmf => by
        have hcvf := hdenf.lengths.core_ok.cur_vars_le
        have hmul : sf.core.fuel.toNat * (c.max_vars + 1) ≤
            (sh.core.fuel.toNat - 1) * (c.max_vars + 1) :=
          Nat.mul_le_mul_right _ hfuf
        have hsub : sh.core.fuel.toNat * (c.max_vars + 1) =
            (sh.core.fuel.toNat - 1) * (c.max_vars + 1) + (c.max_vars + 1) := by
          rw [← Nat.succ_mul]; congr 1; omega
        refine hLh (sf.core.fuel.toNat * (c.max_vars + 1) + hl_f.toNat) (hl_f, re_f, ()) mf
          (by omega) ⟨sf, hhlf, rfl, hdenf, htmkf, by omega, hmf⟩
    refine wp_join_state (ts := [i64, .bool]) (α := BitVec 64 × Bool × FullState)
      (fun x => (x.1, x.2.1, ()))
      (fun x mj =>
        x.1.toNat ≤ x.2.2.core.cur_vars ∧ FullDenseInv c F0 x.2.2 ∧ TmkZero x.2.2 ∧
        x.2.2.core.fuel.toNat ≤ sh.core.fuel.toNat - 1 ∧ (FullMem c x.2.2 ⋆ R) mj)
      (fun _ ⟨hl_f, re_f, sf⟩ mf ⟨hhlf, hdenf, htmkf, hfuf, hmf⟩ => by
        c0_hsteps!
        exact hcont_4 hl_f re_f sf mf hhlf hdenf htmkf hfuf hmf)
      (fun Jn hJn => by
        c0_hsplit
        · c0_hsteps_nogrp
          refine wp_loop_group (ts := [i64, i64])
            (fun rem_k (hl_k, k, ()) mk => ∃ sk : FullState,
              k.toNat ≤ nn.toNat ∧ rem_k = nn.toNat - k.toNat ∧
              hl_k.toNat ≤ sk.core.cur_vars ∧ sk.core.cur_vars = s5.core.cur_vars ∧
              FullDenseInv c F0 sk ∧ TmkZero sk ∧
              sk.core.fuel.toNat ≤ sh.core.fuel.toNat - 1 ∧ (FullMem c sk ⋆ R) mk)
            ?_ ?_
          · rintro Lk rem_k ⟨hl_k, k, ⟨⟩⟩ mk hLk
              ⟨sk, hk_le, rfl, hhlk, hcvk, hdenk, htmkk, hfuk, hmk⟩
            have hlkl := hdenk.lengths
            have hcvk_le := hlkl.core_ok.cur_vars_le
            c0_hsplit
            · have hk_lt : k.toNat < nn.toNat := hc
              have hk1 : (k + 1#64).toNat = k.toNat + 1 := by c0_bound
              have hws2_k := hlkl.scratch_ok.work_stk2_len
              have hk_w : k.toNat < sk.scratch.work_stk2.length := by omega
              let uk := sk.scratch.work_stk2[k.toNat]'hk_w
              c0_hsteps_nogrp
              refine wp_join_state (ts := [i64]) (α := BitVec 64 × FullState) (fun x => (x.1, ()))
                (fun x mj =>
                  x.1.toNat ≤ x.2.core.cur_vars ∧ x.2.core.cur_vars = s5.core.cur_vars ∧
                  FullDenseInv c F0 x.2 ∧ TmkZero x.2 ∧
                  x.2.core.fuel.toNat ≤ sh.core.fuel.toNat - 1 ∧ (FullMem c x.2 ⋆ R) mj)
                (fun _ ⟨hl_j, sj⟩ mj ⟨hhlj, hcvj, hdenj, htmkj, hfuj, hmj⟩ => by
                  c0_hsteps!
                  exact hLk (nn.toNat - (k + 1#64).toNat) (hl_j, k + 1#64, ()) mj (by omega)
                    ⟨sj, by omega, rfl, hhlj, hcvj, hdenj, htmkj, hfuj, hmj⟩)
                (fun Jk hJk => by
                  c0_hsplit
                  · have huk_lt : uk.toNat < sk.core.cur_vars := by
                      rw [← hcvk, Nat.mod_eq_of_lt (by omega : sk.core.cur_vars < 2 ^ 64)] at hc
                      exact hc
                    have hflk_l := hlkl.core_ok.flags_len
                    have huk_fl : (uk.setWidth 64).toNat < sk.core.flags.length := by
                      rw [hflk_l, elim_zext32_toNat]; omega
                    c0_hsplit
                    · have hvlk_l := hlkl.core_ok.vals_len
                      have huk_vl : (uk.setWidth 64 <<< (1 : Nat)).toNat <
                          sk.core.vals.length := by rw [hvlk_l]; c0_bound
                      c0_hsplit
                      · c0_hsteps_nogrp
                        let u64 := (uk.setWidth 64).toNat
                        let fl_u := sk.core.flags.set u64 (sk.core.flags[u64]'huk_fl ||| 16#32)
                        let su_k : FullState := { sk with core := { sk.core with flags := fl_u } }
                        have hflu_l : fl_u.length = c.max_vars := by
                          simp only [fl_u, List.length_set, hflk_l]
                        have hden_u := fullDenseInv_with_flags hdenk hflu_l
                        elim_call hPush
                        refine ⟨c, su_k, R, rfl, hden_u.lengths,
                          watchLayout_of_denseInv hden_u, hm, ?_⟩
                        intro hl_p ws1p ssp mp_ hws1p hssp hhlp hmp_
                        c0_hsteps!
                        let s_pu : FullState :=
                          { su_k with scratch :=
                            { su_k.scratch with work_stk1 := ws1p, sim_sig := ssp } }
                        exact hJk (hl_p, s_pu) mp_
                          ⟨hhlp hhlk, hcvk, fullDenseInv_with_ws1_ss hden_u hws1p hssp,
                           tmkZero_congr htmkk rfl rfl, hfuk, hmp_⟩
                      · c0_hsteps!; exact hJk (hl_k, sk) mk ⟨hhlk, hcvk, hdenk, htmkk, hfuk, hmk⟩
                    · c0_hsteps!; exact hJk (hl_k, sk) mk ⟨hhlk, hcvk, hdenk, htmkk, hfuk, hmk⟩
                  · c0_hsteps!; exact hJk (hl_k, sk) mk ⟨hhlk, hcvk, hdenk, htmkk, hfuk, hmk⟩)
            · c0_hsteps!; exact hJn (hl_k, true, sk) mk ⟨hhlk, hdenk, htmkk, hfuk, hmk⟩
          · intro Lk hLk; c0_hsteps!
            exact hLk nn.toNat (hl_h - 1#64, 0#64, ()) m5
              ⟨s5, Nat.zero_le _, by simp, hhl_s5, rfl, hden5, htmk5', hfu5_dec, hm5⟩
        · c0_hsteps!; exact hJn (hl_h - 1#64, re_h, s5) m5 ⟨hhl_s5, hden5, htmk5', hfu5_dec, hm5⟩)
  · c0_hsteps!
    exact hQ 20#64 s5 m5 hden5 htmk5' hfu5' (Or.inr rfl) (fun _ => hfu5_uns (by simpa using hc)) hm5

/-- Canonical `Func.wp` proof for `full_elim_bve_m7` (`Spec.fullElimBveM7Spec`). -/
public theorem full_elim_bve_m7_wp (Γ : Env)
    (hFlush : Γ.Has "full_dense_flush_units_m7" Dense.Spec.fullDenseFlushUnitsSpec)
    (hPush : Γ.Has "full_bve_heap_push_m7" Spec.fullBveHeapPushM7Spec)
    (hPop : Γ.Has "full_bve_heap_pop_m7" Spec.fullBveHeapPopM7Spec)
    (hNbrs : Γ.Has "full_bve_collect_nbrs_m7" Spec.fullBveCollectNbrsM7Spec)
    (hVar : Γ.Has "full_bve_var_m7" Spec.fullBveVarM7Spec) :
    ∀ a m Q X, Spec.fullElimBveM7Spec a m Q X →
      Func.wp Γ full_elim_bve_m7_body a m Q X := by
  rintro ⟨h, res_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, rfl, hden0, htmk0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv0_le := hden0.lengths.core_ok.cur_vars_le
  have hmcl0 := hden0.lengths.core_ok.min_clr_len_arr
  unfold Func.wp full_elim_bve_m7_body
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i64])
    (fun rem_c (ci, ()) mc => ∃ mclrc : List (BitVec 32),
      mclrc.length = c.max_vars ∧ ci.toNat ≤ s0.core.cur_vars ∧
      rem_c = s0.core.cur_vars - ci.toNat ∧
      (FullMem c { s0 with core := { s0.core with min_clr := mclrc } } ⋆ R) mc)
    ?_ (fun Lc hLc => by
      c0_hsteps!
      exact hLc s0.core.cur_vars (0#64, ()) m0
        ⟨s0.core.min_clr, hmcl0, Nat.zero_le _, by simp, hm0⟩)
  rintro Lc rem_c ⟨ci, ⟨⟩⟩ mc hLc ⟨mclrc, hmclrc, hci_le, rfl, hmc⟩
  c0_hsplit
  · have hci_lt : ci.toNat < s0.core.cur_vars := by
      rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
    have hmcl_b : ci.toNat < mclrc.length := by omega
    have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := by c0_bound
    c0_hsteps!
    exact hLc (s0.core.cur_vars - (ci + 1#64).toNat) (ci + 1#64, ()) _ (by omega)
      ⟨_, by simp [hmclrc], by omega, rfl, hm⟩
  let sz : FullState :=
    { s0 with
      core := { s0.core with min_clr := mclrc }
      scratch := { s0.scratch with res_sz := 0#64 } }
  have hdenz : FullDenseInv c F0 sz :=
    elim_denseInv_with_resSz (fullDenseInv_with_min_clr hden0 hmclrc) 0#64
  have htmkz : TmkZero sz := tmkZero_congr htmk0 rfl rfl
  c0_hsteps_nogrp
  refine wp_loop_break_group (brkTs := [.bool, i64, .bool, i64]) (lpTs := [.bool, i64, .bool, i64])
    (fun (_hl, _hln, _lre, _rd, ()) mb => ∃ sb : FullState,
      FullDenseInv c F0 sb ∧ TmkZero sb ∧ sb.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
      (FullMem c sb ⋆ R) mb)
    (fun rem_r (hit_lim, hlen, _lre, round, ()) mr => ∃ sr : FullState,
      round.toNat ≤ 2 ∧ rem_r = 2 - round.toNat ∧
      hlen.toNat ≤ sr.core.cur_vars ∧
      FullDenseInv c F0 sr ∧ TmkZero sr ∧ sr.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
      (FullMem c sr ⋆ R) mr)
    ?_ ?_ ?_
  · rintro _ ⟨hl0, hln0, lre0, rd0, ⟨⟩⟩ mb ⟨sb, hdenb, htmkb, hfub, hmb⟩
    exact elim_bve_round_br_wp Γ c F0 R s0 sb res_lim hl0 hln0 lre0 rd0 mb Q X hQ
      hdenb htmkb hfub hmb
  · rintro Br Lr rem_r ⟨hit_lim, hlen, lre, round, ⟨⟩⟩ mr hBr hLr
      ⟨sr, hrd_le, rfl, hhl_le, hdenr, htmkr, hfur, hmr⟩
    have hbrk_r : Br (hit_lim, hlen, lre, round, ()) mr :=
      hBr (hit_lim, hlen, lre, round, ()) mr ⟨sr, hdenr, htmkr, hfur, hmr⟩
    c0_hsplit
    · have hrd_lt : round.toNat < 2 := hc
      have hrd1 : (round + 1#64).toNat = round.toNat + 1 := by c0_bound
      c0_hsplit
      · c0_hsteps!; exact hbrk_r
      · c0_hsteps_nogrp
        obtain ⟨F_cur, hdwr⟩ := hdenr.exists_witness
        elim_call hFlush
        refine ⟨c, F0, F_cur, sr, R, rfl, hdwr, hmr, ?_⟩
        intro ok_u su mu hdwu hcvu _ hfuu _ htmku _ _ _ _ _ hfu_uns hmu
        have hdenu : FullDenseInv c F0 su := hdwu.toDense
        have htmku' : TmkZero su := tmkZero_congr htmkr hcvu htmku
        have hfuu' : su.core.fuel.toNat ≤ s0.core.fuel.toNat := by rw [hfuu]; exact hfur
        c0_hsplit
        · have hcvu_le := hdwu.1.core_ok.cur_vars_le
          have hws1u := hdwu.1.scratch_ok.work_stk1_len
          c0_hsteps_nogrp
          refine wp_loop_group (ts := [i64])
            (fun rem_i (i, ()) mi => ∃ ws1 : List (BitVec 32),
              ws1.length = 2 * c.max_vars ∧ i.toNat ≤ su.core.cur_vars ∧
              rem_i = su.core.cur_vars - i.toNat ∧
              (FullMem c { su with scratch := { su.scratch with work_stk1 := ws1 } } ⋆ R)
                mi)
            ?_ ?_
          · rintro Li rem_i ⟨i, ⟨⟩⟩ mi hLi ⟨ws1, hws1, hi_le, rfl, hmi⟩
            c0_hsplit
            · have hi_lt : i.toNat < su.core.cur_vars := by
                rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
              have hmv_i : (BitVec.ofNat 64 c.max_vars + i).toNat < ws1.length := by
                rw [hws1]; c0_bound
              have hi1 : (i + 1#64).toNat = i.toNat + 1 := by c0_bound
              c0_hsteps!
              exact hLi (su.core.cur_vars - (i + 1#64).toNat) (i + 1#64, ()) _ (by omega)
                ⟨_, by simp [hws1], by omega, rfl, hm⟩
            · let su1 : FullState :=
                { su with scratch := { su.scratch with work_stk1 := ws1 } }
              have hdenu1 : FullDenseInv c F0 su1 :=
                fullDenseInv_with_ws1_ss hdenu hws1 hdwu.1.scratch_ok.sim_sig_len
              c0_hsteps_nogrp
              refine wp_loop_group (ts := [i64, i64])
                (fun rem_p (hl_p, ip, ()) mp => ∃ (ws1p : List (BitVec 32))
                    (ssp : List (BitVec 64)),
                  let sp : FullState :=
                    { su with scratch :=
                      { su.scratch with work_stk1 := ws1p, sim_sig := ssp } }
                  ws1p.length = 2 * c.max_vars ∧ ssp.length = c.max_vars ∧
                  ip.toNat ≤ su.core.cur_vars ∧ rem_p = su.core.cur_vars - ip.toNat ∧
                  hl_p.toNat ≤ su.core.cur_vars ∧ (FullMem c sp ⋆ R) mp)
                ?_ ?_
              · rintro Lp rem_p ⟨hl_p, ip, ⟨⟩⟩ mp hLp
                  ⟨ws1p, ssp, hws1p, hssp, hip_le, rfl, hhlp_le, hmp⟩
                let sp : FullState :=
                  { su with scratch :=
                    { su.scratch with work_stk1 := ws1p, sim_sig := ssp } }
                c0_hsplit
                · have hip_lt : ip.toNat < su.core.cur_vars := by
                    rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                  have hip1 : (ip + 1#64).toNat = ip.toNat + 1 := by c0_bound
                  have hip_fl : ip.toNat < su.core.flags.length := by
                    rw [hdwu.1.core_ok.flags_len]; omega
                  have hip_vl : (ip <<< (1 : Nat)).toNat < su.core.vals.length := by
                    rw [hdwu.1.core_ok.vals_len]; c0_bound
                  c0_hsteps_nogrp
                  refine wp_join_state (ts := [i64])
                    (α := BitVec 64 × List (BitVec 32) × List (BitVec 64))
                    (fun x => (x.1, ()))
                    (fun x mj =>
                      let sj : FullState :=
                        { su with scratch :=
                          { su.scratch with work_stk1 := x.2.1, sim_sig := x.2.2 } }
                      x.2.1.length = 2 * c.max_vars ∧ x.2.2.length = c.max_vars ∧
                      x.1.toNat ≤ su.core.cur_vars ∧ (FullMem c sj ⋆ R) mj)
                    (fun _ ⟨hl_j, ws1j, ssj⟩ mj ⟨hws1j, hssj, hhlj, hmj⟩ => by
                      c0_hsteps!
                      exact hLp (su.core.cur_vars - (ip + 1#64).toNat)
                        (hl_j, ip + 1#64, ()) mj (by omega)
                        ⟨ws1j, ssj, hws1j, hssj, by omega, rfl, hhlj, hmj⟩)
                    (fun Jp hJp => by
                      c0_hsplit
                      · c0_hsplit
                        · c0_hsteps_nogrp
                          let sp1 : FullState :=
                            { su with scratch :=
                              { su.scratch with work_stk1 := ws1p, sim_sig := ssp } }
                          elim_call hPush
                          refine ⟨c, sp1, R, rfl,
                            (fullDenseInv_with_ws1_ss hdenu hws1p hssp).lengths,
                            watchLayout_of_denseInv
                              (fullDenseInv_with_ws1_ss hdenu hws1p hssp),
                            hmp, ?_⟩
                          intro hl_n ws1n ssn mn hws1n hssn hhln hmn
                          c0_hsteps!
                          exact hJp (hl_n, ws1n, ssn) mn
                            ⟨hws1n, hssn, hhln hhlp_le, hmn⟩
                        · c0_hsteps!; exact hJp (hl_p, ws1p, ssp) mp
                            ⟨hws1p, hssp, hhlp_le, hmp⟩
                      · c0_hsteps!; exact hJp (hl_p, ws1p, ssp) mp
                          ⟨hws1p, hssp, hhlp_le, hmp⟩)
                · have hdensp : FullDenseInv c F0 sp :=
                    fullDenseInv_with_ws1_ss hdenu hws1p hssp
                  have htmksp : TmkZero sp := tmkZero_congr htmku' rfl rfl
                  c0_hsplit
                  · c0_hsteps!
                    exact hBr (hit_lim, hl_p, false, round, ()) mp
                      ⟨sp, hdensp, htmksp, hfuu', hmp⟩
                  · c0_hsteps_nogrp
                    refine wp_loop_break_group
                      (brkTs := [.bool, i64, .bool]) (lpTs := [i64, .bool])
                      (fun (hl_b, hl_len, re_b, ()) mb => ∃ sb : FullState,
                        hl_len.toNat ≤ sb.core.cur_vars ∧
                        FullDenseInv c F0 sb ∧ TmkZero sb ∧
                        sb.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sb ⋆ R) mb)
                      (fun rem_h (hl_h, re_h, ()) mh => ∃ sh : FullState,
                        hl_h.toNat ≤ sh.core.cur_vars ∧
                        rem_h = sh.core.fuel.toNat * (c.max_vars + 1) + hl_h.toNat ∧
                        FullDenseInv c F0 sh ∧ TmkZero sh ∧
                        sh.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c sh ⋆ R) mh)
                      ?_ ?_ ?_
                    · rintro _ ⟨hl_b, hl_len, re_b, ⟨⟩⟩ mb
                        ⟨sb, hhlb, hdenb, htmkb, hfub, hmb⟩
                      c0_hsplit
                      · c0_hsteps!
                        exact hLr (2 - (round + 1#64).toNat)
                          (hl_b, hl_len, re_b, round + 1#64, ()) mb (by omega)
                          ⟨sb, by omega, rfl, hhlb, hdenb, htmkb, hfub, hmb⟩
                      · c0_hsteps!
                        exact hBr (hl_b, hl_len, re_b, round, ()) mb
                          ⟨sb, hdenb, htmkb, hfub, hmb⟩
                    · rintro Bh Lh rem_h ⟨hl_h, re_h, ⟨⟩⟩ mh hBh hLh
                        ⟨sh, hhlh, rfl, hdenh, htmkh, hfuh, hmh⟩
                      have hbrk_h : Bh (hit_lim, hl_h, re_h, ()) mh :=
                        hBh (hit_lim, hl_h, re_h, ()) mh
                          ⟨sh, hhlh, hdenh, htmkh, hfuh, hmh⟩
                      c0_hsplit
                      · have hhl_pos : 0 < hl_h.toNat := hc
                        have hhl_dec : (hl_h - 1#64).toNat = hl_h.toNat - 1 := by c0_bound
                        c0_hsplit
                        · have hfu_pos : 0 < sh.core.fuel.toNat := hc
                          have hfu_dec : (sh.core.fuel - 1#64).toNat =
                              sh.core.fuel.toNat - 1 := by c0_bound
                          c0_hsplit
                          · c0_hsplit
                            · c0_hsplit
                              · c0_hsteps!
                                exact hBh (true, hl_h, re_h, ()) mh
                                  ⟨sh, hhlh, hdenh, htmkh, hfuh, hmh⟩
                              · c0_hsteps_nogrp
                                elim_call hPop
                                refine ⟨c, sh, R, rfl, hdenh.lengths, hmh, ?_⟩
                                intro v ws1_1 m1 hws1_1 hm1
                                let s1 : FullState :=
                                  { sh with scratch :=
                                    { sh.scratch with work_stk1 := ws1_1 } }
                                have hden1 : FullDenseInv c F0 s1 :=
                                  fullDenseInv_with_ws1_ss hdenh hws1_1
                                    hdenh.lengths.scratch_ok.sim_sig_len
                                have htmk1 : TmkZero s1 := tmkZero_congr htmkh rfl rfl
                                have hcv1_le := hden1.lengths.core_ok.cur_vars_le
                                have hhl_dec1 : (hl_h - 1#64).toNat ≤ s1.core.cur_vars := by
                                  dsimp only [s1]; rw [hhl_dec]; omega
                                c0_hsplit
                                · c0_hsteps!
                                  exact hLh _ (hl_h - 1#64, re_h, ()) m1
                                    (by dsimp only [s1]; rw [hhl_dec]; omega)
                                    ⟨s1, hhl_dec1, rfl, hden1, htmk1, hfuh, hm1⟩
                                · c0_hsplit
                                  · c0_hsteps!
                                    exact hLh _ (hl_h - 1#64, re_h, ()) m1
                                      (by dsimp only [s1]; rw [hhl_dec]; omega)
                                      ⟨s1, hhl_dec1, rfl, hden1, htmk1, hfuh, hm1⟩
                                  · have hv_lt : v.toNat < s1.core.cur_vars := by
                                      rw [Nat.mod_eq_of_lt
                                        (by omega : s1.core.cur_vars < 2 ^ 64)] at hc
                                      omega
                                    have hv_fl : (v.setWidth 64).toNat <
                                        s1.core.flags.length := by
                                      rw [hden1.lengths.core_ok.flags_len, elim_zext32_toNat]
                                      omega
                                    have hv_vl : (v.setWidth 64 <<< (1 : Nat)).toNat <
                                        s1.core.vals.length := by
                                      rw [hden1.lengths.core_ok.vals_len]; c0_bound
                                    c0_hsplit
                                    · c0_hsteps!
                                      exact hLh _ (hl_h - 1#64, re_h, ()) m1
                                        (by dsimp only [s1]; rw [hhl_dec]; omega)
                                        ⟨s1, hhl_dec1, rfl, hden1, htmk1, hfuh, hm1⟩
                                    · c0_hsplit
                                      · c0_hsteps!
                                        exact hLh _ (hl_h - 1#64, re_h, ()) m1
                                          (by dsimp only [s1]; rw [hhl_dec]; omega)
                                          ⟨s1, hhl_dec1, rfl, hden1, htmk1, hfuh, hm1⟩
                                      · c0_hsteps_nogrp
                                        let fl2 := s1.core.flags.set (v.setWidth 64).toNat
                                          (s1.core.flags[(v.setWidth 64).toNat]'hv_fl &&&
                                            ~~~16#32)
                                        let s2 : FullState :=
                                          { s1 with core :=
                                            { s1.core with
                                              flags := fl2
                                              fuel := s1.core.fuel - 1#64 } }
                                        have hden2 : FullDenseInv c F0 s2 :=
                                          fullDenseInv_with_flags_fuel hden1
                                            (by simp [fl2, hden1.lengths.core_ok.flags_len])
                                            (s1.core.fuel - 1#64)
                                        have htmk2 : TmkZero s2 := tmkZero_congr htmk1 rfl rfl
                                        elim_call hNbrs
                                        refine ⟨c, F0, s2, R, rfl, hden2, htmk2, hm, ?_⟩
                                        intro nn mclr3 ws2_3 m3 _s3_n hl3 hnn_le _ hm3
                                        have hcv2_le := hden2.lengths.core_ok.cur_vars_le
                                        have hnn_mv : nn.toNat ≤ c.max_vars :=
                                          Nat.le_trans hnn_le hcv2_le
                                        let s3 : FullState :=
                                          { s2 with
                                            core := { s2.core with min_clr := mclr3 },
                                            scratch :=
                                              { s2.scratch with work_stk2 := ws2_3 } }
                                        have hden3 : FullDenseInv c F0 s3 :=
                                          fullDenseInv_with_min_clr_ws2 hden2
                                            hl3.core_ok.min_clr_len_arr
                                            hl3.scratch_ok.work_stk2_len
                                        have htmk3 : TmkZero s3 := tmkZero_congr htmk2 rfl rfl
                                        c0_hsteps_nogrp
                                        elim_call hVar
                                        refine ⟨c, F0, s3, R, rfl, hden3, htmk3, hv_lt,
                                          hm3, ?_⟩
                                        intro st s4 m4 hden4 htmk4 hcv4 hfu4 _ hst20 hm4
                                        have hfu4_dec : s4.core.fuel.toNat ≤
                                            sh.core.fuel.toNat - 1 := by
                                          change s4.core.fuel.toNat ≤
                                            (s1.core.fuel - 1#64).toNat at hfu4
                                          rw [show s1.core.fuel = sh.core.fuel from rfl,
                                            hfu_dec] at hfu4
                                          exact hfu4
                                        have hfu4' : s4.core.fuel.toNat ≤
                                            s0.core.fuel.toNat := by omega
                                        have hcv4_le := hden4.lengths.core_ok.cur_vars_le
                                        have hhl_s4 : (hl_h - 1#64).toNat ≤
                                            s4.core.cur_vars := by
                                          dsimp only [s3, s2, s1] at hcv4
                                          rw [hhl_dec]; omega
                                        c0_hsplit
                                        · c0_hsteps!
                                          exact hQ 20#64 s4 m4 hden4 htmk4 hfu4'
                                            (Or.inr rfl) (fun _ => hst20 hc) hm4
                                        · c0_hsplit
                                          · c0_hsteps!
                                            exact hQ 20#64 s4 m4 hden4 htmk4 hfu4'
                                              (Or.inr rfl)
                                              (fun _ => hden4.inconsistent_unsat hc) hm4
                                          · c0_hsplit
                                            · c0_hsteps!
                                              exact hBh (hit_lim, hl_h - 1#64, re_h, ())
                                                m4 ⟨s4, hhl_s4, hden4, htmk4, hfu4', hm4⟩
                                            · c0_hsteps_nogrp
                                              obtain ⟨F_cur4, hdw4⟩ := hden4.exists_witness
                                              elim_call hFlush
                                              refine ⟨c, F0, F_cur4, s4, R, rfl, hdw4, hm4, ?_⟩
                                              intro ok_f s5 m5 hdw5 hcv5 _ hfu5 _
                                                htmk5 _ _ _ _ _ hfu5_uns hm5
                                              have hden5 : FullDenseInv c F0 s5 := hdw5.toDense
                                              have htmk5' : TmkZero s5 :=
                                                tmkZero_congr htmk4 hcv5 htmk5
                                              have hfu5_dec : s5.core.fuel.toNat ≤
                                                  sh.core.fuel.toNat - 1 := by
                                                rw [hfu5]; exact hfu4_dec
                                              have hfu5' : s5.core.fuel.toNat ≤
                                                  s0.core.fuel.toNat := by omega
                                              have hhl_s5 : (hl_h - 1#64).toNat ≤
                                                  s5.core.cur_vars := by
                                                rw [hcv5]; exact hhl_s4
                                              exact elim_bve_post_flush_wp Γ hPush c F0 R
                                                hl_h nn _s3_n.scratch.bve_cnt re_h ok_f s0
                                                sh s5 m5 Q X Lh hQ hLh hnn_mv hden5 htmk5'
                                                hfu_pos hfuh hfu5_dec hfu5' hfu5_uns hhl_s5 hm5
                            · c0_hsteps!; exact hbrk_h
                          · c0_hsteps!; exact hbrk_h
                        · c0_hsteps!; exact hbrk_h
                      · c0_hsteps!; exact hbrk_h
                    · intro _ Lh _ hLh; c0_hsteps!
                      exact hLh _ (hl_p, false, ()) mp
                        ⟨sp, hhlp_le, rfl, hdensp, htmksp, hfuu', hmp⟩
              · intro Lp hLp; c0_hsteps!
                exact hLp su.core.cur_vars (0#64, 0#64, ()) mi
                  ⟨ws1, su.scratch.sim_sig, hws1, hdwu.1.scratch_ok.sim_sig_len,
                   Nat.zero_le _, by simp, Nat.zero_le _, hmi⟩
          · intro Li hLi; c0_hsteps!
            exact hLi su.core.cur_vars (0#64, ()) mu
              ⟨su.scratch.work_stk1, hws1u, Nat.zero_le _, by simp, hmu⟩
        · c0_hsteps!
          exact hQ 20#64 su mu hdenu htmku' hfuu' (Or.inr rfl)
            (fun _ => hfu_uns (by simpa using hc)) hmu
        all_goals (c0_hsteps!; exact hbrk_r)
    · c0_hsteps!; exact hbrk_r
  · intro _ Lr _ hLr; c0_hsteps!
    exact hLr 2 (false, 0#64, false, 0#64, ()) _
      ⟨sz, Nat.zero_le _, rfl, Nat.zero_le _, hdenz, htmkz, Nat.le_refl _, hm⟩

/-! ## 3. `full_has_elim_cands_fid_wp` -/

/-- Canonical `Func.wp` proof for `full_has_elim_cands_fid` (`Spec.fullHasElimCandsFidSpec`). -/
public theorem full_has_elim_cands_fid_wp (Γ : Env) :
    ∀ a m Q X, Spec.fullHasElimCandsFidSpec a m Q X →
      Func.wp Γ full_has_elim_cands_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  unfold Func.wp full_has_elim_cands_fid_body
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i64])
    (fun rem (v, ()) mv => mv = m ∧ v.toNat ≤ s.core.cur_vars ∧ rem = s.core.cur_vars - v.toNat)
    ?_ (fun _ hL => by
      c0_hsteps!; exact hL s.core.cur_vars (0#64, ()) m ⟨rfl, Nat.zero_le _, rfl⟩)
  rintro L rem ⟨v, ⟨⟩⟩ mv hL ⟨rfl, hv_le, rfl⟩
  c0_hsplit
  · have hv_lt : v.toNat < s.core.cur_vars := by
      rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
    have hv_fl : v.toNat < s.core.flags.length := by rw [hlen.core_ok.flags_len]; omega
    have hv_vals : (v <<< (1 : Nat)).toNat < s.core.vals.length := by
      rw [hlen.core_ok.vals_len]; c0_bound
    have hv1 : (v + 1#64).toNat = v.toNat + 1 := by c0_bound
    c0_hsteps_nogrp
    refine wp_join0 (fun mj => mj = mv)
      (fun _ mj hmj => by
        rcases hmj.symm with rfl; c0_hsteps!
        exact hL (s.core.cur_vars - (v + 1#64).toNat) (v + 1#64, ()) mv (by omega)
          ⟨rfl, by omega, rfl⟩)
      (fun Jx hJx => by
        c0_hsplit
        · c0_hsplit
          · c0_hsplit
            · c0_hsteps!; exact hQ true
            · c0_hsteps!; exact hJx mv rfl
          · c0_hsteps!; exact hJx mv rfl
        · c0_hsteps!; exact hJx mv rfl)
  · c0_hsteps!; exact hQ false

/-! ## 4. `full_eliminate_m6_wp` -/

/-- Canonical `Func.wp` proof for `full_eliminate_m6` (`Spec.fullEliminateM6Spec`). -/
public theorem full_eliminate_m6_wp (Γ : Env)
    (hDticks : Γ.Has "full_elim_dticks" Limits.Spec.schedElimDticksSpec)
    (hF64Nlog : Γ.Has "f64u_nlogpown" Float64.Spec.f64uPure2Spec)
    (hF64Mul : Γ.Has "f64u_mul" Float64.Spec.f64uPure2Spec)
    (hF64ToU64 : Γ.Has "f64u_to_u64" Float64.Spec.f64uPure1Spec)
    (hScale : Γ.Has "full_scale_delta" Limits.Spec.schedScaleDeltaSpec)
    (hHasCands : Γ.Has "full_has_elim_cands_fid" Spec.fullHasElimCandsFidSpec)
    (hEnter : Γ.Has "full_enter_dense_ex_fid" Dense.Spec.fullEnterDenseExM6Spec)
    (hFwd : Γ.Has "full_forward_sub_m7" Forward.Spec.fullForwardSubM7Spec)
    (hReb : Γ.Has "full_rebuild_watches" Dense.Spec.fullRebuildWatchesM6Spec)
    (hElimBve : Γ.Has "full_elim_bve_m7" Spec.fullElimBveM7Spec)
    (hClassify : Γ.Has "full_update_classify_fid" Internal.Spec.fullUpdateClassifyFidSpec) :
    ∀ a m Q X, Spec.fullEliminateM6Spec a m Q X →
      Func.wp Γ full_eliminate_m6_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m0 Q X ⟨c, F0, ext0, s0, R, rfl, hinvM0, hcl0, hm0, hQ⟩
  have hcfg := hinvM0.cfgOk; have hext0 := hinvM0.extOk; have hinv0 := hinvM0.sparse
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  let Rext0 : Mem 64 → Prop := m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R
  unfold Func.wp full_eliminate_m6_body
  have hm0_f := fullM6HdrMem_focus_full hm0
  c0_hsteps_nogrp; elim_call hDticks; refine ⟨c, s0, Rext0, rfl, hinv0.lengths, hm0_f, ?_⟩
  intro dticks
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s1 m1 => FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c s1 ⋆ Rext0) m1)
    (fun _ s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩ => by
      have hm1_u : (FullM6HdrMem c ext0 s1 ⋆ R) m1 := fullM6HdrMem_unfocus_full hm1
      refine wp_join0 (P := fun m_e => m_e = m1)
        (fun _ m_e hm_e => by
          subst hm_e; c0_hsteps_nogrp; elim_call hEnter
          refine ⟨c, F0, ext0, s1, R, rfl, hcfg, hext0, hinv1.lengths, hinv1.1, hinv1.2.1,
            hinv1.2.2.1, hinv1.2.2.2.1, (fun hnz => absurd hinv1.2.2.2.2 hnz), hm1_u, ?_⟩
          intro ok ext2 s2 m2 _ hext2 _ hlen2 _ _ _ _ hfu2 hok_d hfail_s hm2
          let Rext2 : Mem 64 → Prop := m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R
          have hm2_f := fullM6HdrMem_focus_full hm2
          c0_hsplit
          · have hden2 : FullDenseInv c F0 s2 := (hok_d hc).1
            c0_hsteps_nogrp
            refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
              (fun b => (b, ())) (fun _ => True)
              (fun _ _ _ => by
                c0_hsteps_nogrp; elim_call hFwd; refine ⟨c, F0, s2, Rext2, rfl, hden2, hm2_f, ?_⟩
                intro fs s3 m3 hden3 _ hfu3 _ huf3 hm3
                let s3r : FullState :=
                  { s3 with scratch := { s3.scratch with fwd_sub_cnt := s2.scratch.fwd_sub_cnt } }
                have hden3r : FullDenseInv c F0 s3r :=
                  elim_denseInv_with_fwdSub hden3 s2.scratch.fwd_sub_cnt
                have hfu3r : s3r.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                  have hfu2' : s2.core.fuel.toNat ≤ s1.core.fuel.toNat := hfu2
                  change s3.core.fuel.toNat ≤ s0.core.fuel.toNat; rw [hfu3]; omega
                c0_hsplit
                · c0_hsteps_nogrp; elim_call hReb
                  refine ⟨c, F0, ext2, s3r, R, rfl, hcfg, hext2, hden3r,
                    fullM6HdrMem_unfocus_full hm, ?_⟩
                  intro _ ext4 s4 m4 hinvM4 hcl4 hfu4 _ _ hm4
                  c0_hsteps!; exact hQ 20#64 ext4 s4 m4 hinvM4 hcl4 (by omega) (Or.inr rfl)
                    (fun _ => huf3 hc) hm4
                · let cv3 := s3r.core.cur_vars
                  have hcv3_eq : cv3 = s3.core.cur_vars := rfl
                  have hcv3_le : cv3 ≤ c.max_vars := hden3r.lengths.core_ok.cur_vars_le
                  have htl3 := hden3r.lengths.scratch_ok.tarjan_mark_len
                  c0_hsteps_nogrp
                  refine wp_loop_group (ts := [i64])
                    (fun rem_t (ti, ()) mt => ∃ tmki : List (BitVec 32),
                      tmki.length = 2 * c.max_vars ∧ ti.toNat ≤ cv3 ∧ rem_t = cv3 - ti.toNat ∧
                      (∀ k < ti.toNat, tmki[k]?.getD 0#32 = 0#32) ∧
                      (FullMem c { s3r with scratch := { s3r.scratch with tarjan_mark := tmki } }
                        ⋆ Rext2) mt)
                    ?_ ?_
                  · rintro Lt rem_t ⟨ti, ⟨⟩⟩ mt hLt ⟨tmki, htli, hti_le, rfl, hinit, hmt⟩
                    c0_hsplit
                    · have hti_lt : ti.toNat < cv3 := by
                        rw [← hcv3_eq, Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                      have hti_b : ti.toNat < tmki.length := by omega
                      have hti1 : (ti + 1#64).toNat = ti.toNat + 1 := by c0_bound
                      c0_hsteps!; exact hLt (cv3 - (ti + 1#64).toNat) (ti + 1#64, ()) _ (by omega)
                        ⟨tmki.set ti.toNat 0#32, by simp [htli], by omega, rfl, fun k hk => by
                           rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hti1 ▸ hk)) with h | h
                           · rw [List.getElem?_set_ne (by omega)]; exact hinit k h
                           · subst h; rw [List.getElem?_set_self hti_b, Option.getD_some], hm⟩
                    · have hti_eq : ti.toNat = cv3 := by
                        rw [← hcv3_eq, Nat.mod_eq_of_lt (by omega)] at hc
                        change ¬ti.toNat < cv3 at hc; omega
                      rw [hti_eq] at hinit
                      let s3t : FullState :=
                        { s3r with scratch := { s3r.scratch with tarjan_mark := tmki } }
                      have hden3t : FullDenseInv c F0 s3t := elim_denseInv_with_tmk hden3r htli
                      have htmk3t : TmkZero s3t := fun v hv => hinit v hv
                      c0_hsteps_nogrp
                      refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                        (fun b => (b, ())) (fun _ => True)
                        (fun _ _ _ => by
                          c0_hsteps_nogrp; elim_call hElimBve
                          refine ⟨c, F0, s3t, Rext2, rfl, hden3t, htmk3t, hmt, ?_⟩
                          intro res s4 m4 hden4 _ hfu4 _ hres_u hm4
                          have hfu4' : s4.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                            have hfu4s : s4.core.fuel.toNat ≤ s3t.core.fuel.toNat := hfu4
                            have hfu3t : s3t.core.fuel.toNat = s3r.core.fuel.toNat := rfl
                            omega
                          c0_hsteps_nogrp; elim_call hReb
                          refine ⟨c, F0, ext2, s4, R, rfl, hcfg, hext2, hden4,
                            fullM6HdrMem_unfocus_full hm4, ?_⟩
                          intro rr ext5 se me hinvM5 hcle hfue _ hue hme
                          have hmef := fullM6HdrMem_focus_full hme
                          c0_hsteps_nogrp
                          let se1 : FullState :=
                            { se with scratch := { se.scratch with
                              search_ticks := s0.scratch.search_ticks } }
                          have hinvM5_1 : FullM6HdrInv c F0 ext5 se1 :=
                            fullM6HdrInv_of_core_eq hinvM5
                              ⟨hinvM5.sparse.lengths.core_ok,
                               { hinvM5.sparse.lengths.scratch_ok with
                                 walk_vals_len := hinvM5.sparse.lengths.scratch_ok.walk_vals_len }⟩
                              rfl ⟨rfl, rfl⟩
                          have hme1_u : (FullM6HdrMem c ext5 se1 ⋆ R) m :=
                            fullM6HdrMem_unfocus_full hm
                          elim_call hClassify
                          refine m6HdrW2aSpec_of rfl hcfg hinvM5.extOk hinvM5_1.sparse.lengths
                            hme1_u ?_
                          intro _ ext6 se3 me3 hcore3 hlen3 hpres3 hext6 _ hme3
                          have hinvM6 : FullM6HdrInv c F0 ext6 se3 :=
                            fullM6HdrInv_with_ext
                              (fullM6HdrInv_of_m6Pres hinvM5_1 hlen3 hcore3 hpres3) hext6
                          have hme3_f := fullM6HdrMem_focus_full hme3
                          let se4 : FullState :=
                            { se3 with scratch := { se3.scratch with
                              fwd_str_cnt := se3.scratch.search_ticks } }
                          have hinvM6_4 : FullM6HdrInv c F0 ext6 se4 :=
                            fullM6HdrInv_of_core_eq hinvM6
                              ⟨hlen3.core_ok,
                               { hlen3.scratch_ok with
                                 walk_vals_len := hlen3.scratch_ok.walk_vals_len }⟩
                              rfl ⟨rfl, rfl⟩
                          have hfu4e : se4.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                            change se3.core.fuel.toNat ≤ s0.core.fuel.toNat
                            rw [hcore3]; change se.core.fuel.toNat ≤ s0.core.fuel.toNat; omega
                          have hcle4 : se4.core.cur_level = 0 := by
                            change se3.core.cur_level = 0; rw [hcore3]; exact hcle
                          c0_hsteps!
                          · exact hQ 20#64 ext6 se4 _ hinvM6_4 hcle4 hfu4e (Or.inr rfl)
                              (fun _ => hres_u hc) (fullM6HdrMem_unfocus_full hm)
                          · exact hQ 20#64 ext6 se4 _ hinvM6_4 hcle4 hfu4e (Or.inr rfl)
                              (fun _ => hue hc) (fullM6HdrMem_unfocus_full hm)
                          · exact hQ 20#64 ext6 se4 _ hinvM6_4 hcle4 hfu4e (Or.inr rfl)
                              (fun _ => hinvM6_4.sparse.inconsistent_unsat hc)
                              (fullM6HdrMem_unfocus_full hm)
                          · exact hQ 1#64 ext6 se4 _ hinvM6_4 hcle4 hfu4e (Or.inl rfl)
                              (fun h => by cases h) (fullM6HdrMem_unfocus_full hm))
                        (fun Jb hJb => by c0_hsplit <;> (c0_hsteps!; exact hJb _ trivial))
                  · intro Lt hLt; c0_hsteps!; exact hLt cv3 (0#64, ()) _
                      ⟨s3r.scratch.tarjan_mark, htl3, Nat.zero_le _, by simp,
                        fun _ h => by simp at h, hm⟩)
              (fun Jfb hJfb => by c0_hsplit <;> (c0_hsteps!; exact hJfb _ trivial))
          · obtain ⟨hsp2, hcl2⟩ := hfail_s hc
            let s2' : FullState :=
              { s2 with scratch := { s2.scratch with fwd_str_cnt := s2.scratch.search_ticks } }
            have hsp2' : FullSparseInv c F0 s2' :=
              elim_sparseInv_with_scr hsp2
                { hsp2.lengths.scratch_ok with
                  walk_vals_len := hsp2.lengths.scratch_ok.walk_vals_len }
                rfl rfl
            have hfu2' : s2'.core.fuel.toNat ≤ s0.core.fuel.toNat := by
              change s2.core.fuel.toNat ≤ s0.core.fuel.toNat; omega
            c0_hsteps!
            · exact hQ 20#64 ext2 s2' _ (FullM6HdrInv.mk_inv hcfg hext2 hsp2') hcl2 hfu2'
                (Or.inr rfl) (fun _ => hsp2'.inconsistent_unsat hc) (fullM6HdrMem_unfocus_full hm)
            · exact hQ 1#64 ext2 s2' _ (FullM6HdrInv.mk_inv hcfg hext2 hsp2') hcl2 hfu2'
                (Or.inl rfl) (fun h => by cases h) (fullM6HdrMem_unfocus_full hm))
        (fun Je hJe => by
          c0_hsplit
          · exact hJe m1 rfl
          · c0_hsteps_nogrp; elim_call hHasCands
            refine ⟨c, s1, Rext0, rfl, hinv1.lengths, hm1, fun _ => ?_⟩
            c0_hsplit
            · exact hJe m1 rfl
            · let s1' : FullState :=
                { s1 with scratch := { s1.scratch with fwd_str_cnt := s1.scratch.search_ticks } }
              have hinv1' : FullSparseInv c F0 s1' :=
                elim_sparseInv_with_scr hinv1
                  { hinv1.lengths.scratch_ok with
                    walk_vals_len := hinv1.lengths.scratch_ok.walk_vals_len }
                  rfl rfl
              have hfu1' : s1'.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                change s1.core.fuel.toNat ≤ s0.core.fuel.toNat; omega
              c0_hsteps!; exact hQ 1#64 ext0 s1' _ (FullM6HdrInv.mk_inv hcfg hext0 hinv1')
                hcl1 hfu1' (Or.inl rfl) (fun h => by cases h) (fullM6HdrMem_unfocus_full hm)))
    (fun J1 hJ1 => by
      c0_hsplit
      · c0_hsteps!; exact hJ1 s0 m0 ⟨hinv0, hcl0, Nat.le_refl _, hm0_f⟩
      · c0_hsteps_nogrp
        let s0a : FullState :=
          { s0 with scratch := { s0.scratch with eliminations := s0.scratch.eliminations + 1#64 } }
        have hlen0a : s0a.LengthsOk c :=
          ⟨hinv0.lengths.core_ok,
           { hinv0.lengths.scratch_ok with
             walk_vals_len := hinv0.lengths.scratch_ok.walk_vals_len }⟩
        elim_call hF64Nlog; intro _; c0_hsteps_nogrp
        elim_call hF64Mul; intro _; c0_hsteps_nogrp
        elim_call hF64ToU64; intro _; c0_hsteps_nogrp
        elim_call hScale; refine ⟨c, s0a, Rext0, rfl, hlen0a, hm, ?_⟩
        intro delta; c0_hsteps!
        let s0b : FullState :=
          { s0a with scratch := { s0a.scratch with elim_limit := s0a.scratch.conflicts + delta } }
        have hinv0b : FullSparseInv c F0 s0b :=
          elim_sparseInv_with_scr hinv0
            { hinv0.lengths.scratch_ok with
              walk_vals_len := hinv0.lengths.scratch_ok.walk_vals_len }
            rfl rfl
        exact hJ1 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩)

end LeanQbe.T.Examples.Kissat.Proof.Eliminate
