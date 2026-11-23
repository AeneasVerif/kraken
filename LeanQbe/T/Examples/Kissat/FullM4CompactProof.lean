/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM4CompactPart1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` M4a Compaction Verification (`FullM4CompactProof`, `13/13` functions)

Proves all `13` `Func.wp` contracts for `FullM4Compact`, `compact_tableImpl`,
`compact_moduleOk : ModuleOk compactEnv compactModule`, UNSAT-soundness preservation
(`FullSparseInv` + `FullCfgCompat`), and concrete `1972`-byte `Mem 64` UNSAT non-vacuity
(`XPost := False`, verifying `cur_vars' = 1 < nvCompactCfg.mv = 2`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4Compact

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

private theorem level0_conflict_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hcl0 : s.core.cur_level = 0)
    (hc : FullConflictOkW F_cur s) : F0.Unsat := by
  refine hw.ext_sound.2 (unsat_of_entails_nil ?_)
  rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨_, href, hng, hfals⟩
  · refine entails_of_mem_or_false hent fun l hl => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    right
    rcases hl with rfl | rfl
    · exact level0_vals_false_entails hw hcl0 h0lt hf0
    · exact level0_vals_false_entails hw hcl0 h1lt hf1
  · refine entails_of_mem_or_false (hw.arena.entails _ href hng) fun l hl => ?_
    right
    exact level0_vals_false_entails hw hcl0 (hw.arena.lits_lt _ href hng l hl) (hfals l hl)

private theorem nodup_unmap_kept {ncv ovnew : Nat} {inv : List (BitVec 32)}
    {kept : List Nat} (hpre : ∀ x ∈ kept, x / 2 < ncv)
    (hkept_nd : (kept.map (· / 2)).Nodup)
    {knew : Nat} (hknew_lt : knew / 2 < ncv)
    (hinv_new : (inv[knew / 2]?.getD 0#32).toNat = ovnew)
    (hinv_inj : ∀ {n1 n2}, n1 < ncv → n2 < ncv →
      (inv[n1]?.getD 0#32).toNat = (inv[n2]?.getD 0#32).toNat → n1 = n2)
    (hfresh : ovnew ∉ (kept.map fun x => (inv[x / 2]?.getD 0#32).toNat)) :
    ((kept ++ [knew]).map (· / 2)).Nodup := by
  rw [List.map_append, List.map_singleton, List.nodup_append]
  refine ⟨hkept_nd, by simp, ?_⟩
  intro a ha b hb heq
  rw [List.mem_singleton] at hb; subst hb
  rw [List.mem_map] at ha; obtain ⟨x, hx, rfl⟩ := ha
  have hx_lt := hpre x hx
  have hinv_eq : (inv[x / 2]?.getD 0#32).toNat = (inv[knew / 2]?.getD 0#32).toNat := by
    rw [heq]
  have h12 := hinv_inj hx_lt hknew_lt hinv_eq
  rw [hinv_new] at hinv_eq
  exact hfresh (List.mem_map.mpr ⟨x, hx, hinv_eq⟩)

private theorem fullArenaVarsNodup_of_permEq {s s' : FullState}
    (hnd : FullArenaVarsNodup s) (hp : FullArenaPermEq s.core s'.core) :
    FullArenaVarsNodup s' := by
  intro r hr hng
  have hr0 : r ∈ fullArenaClauseRefs s := by
    change r ∈ fullArenaClauseRefsCore s'.core at hr
    change r ∈ fullArenaClauseRefsCore s.core
    rw [hp.2.1] at hr; exact hr
  obtain ⟨_, hg_eq, hperm⟩ := hp.2.2 r hr0
  have hng0 : fullArenaClauseGarb s r = false := by
    change fullArenaClauseGarbCore s'.core r = false at hng
    rw [hg_eq] at hng; exact hng
  exact (List.Perm.nodup_iff (hperm.map (· / 2))).mpr (hnd r hr0 hng0)

open FullArenaTactics FullCompactTactics
open scoped FullArenaTactics FullCompactTactics

/-! ## 2. `Func.wp` Proofs — Part 2 (`arena`, `flush`, `full_compact`) -/

private def arenaKeepExpr (Val : Ty → Type) (Cont : List Ty → Type)
    (h src dst fred irred redd nsrc arP : Val i64) (hdr : Val i32)
    (sat : Val .bool) (new_sz : Val i32)
    (J1 : Cont [i64, i64, i64, i64, i64, i64])
    (Jl : Cont [i64, i64, i64, i64, i64]) : Expr Val Cont [i64] :=
  Expr.jnz (Arg.var sat)
  (
  Expr.jump Jl (Arg.var nsrc, Arg.var dst, Arg.var fred, Arg.var irred, Arg.var redd, ()))
  (
  Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl, (Arg.var new_sz, Arg.imm 0, ())⟩ fun p_27 =>
  Expr.jnz (Arg.var p_27.fst)
  (
  Expr.jump J1 (Arg.var src, Arg.var dst, Arg.var fred, Arg.var irred, Arg.var redd, Arg.imm 2,
    ()))
  (
  Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl, (Arg.var new_sz, Arg.imm 1, ())⟩ fun p_28 =>
  Expr.jnz (Arg.var p_28.fst)
  (
  Expr.jump Jl (Arg.var nsrc, Arg.var dst, Arg.var fred, Arg.var irred, Arg.var redd, ()))
  (
  Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl, (Arg.var new_sz, Arg.imm 2, ())⟩ fun p_29 =>
  Expr.jnz (Arg.var p_29.fst)
  (
  Expr.let_ ⟨OpCode.add i64, (Arg.var dst, Arg.imm 3, ())⟩ fun p_30 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_30.fst, Arg.imm 4, ())⟩ fun p_31 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var arP, Arg.var p_31.fst, ())⟩ fun p_32 =>
  Expr.load i32 (Arg.var p_32.fst) fun ld_6 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var dst, Arg.imm 4, ())⟩ fun p_33 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_33.fst, Arg.imm 4, ())⟩ fun p_34 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var arP, Arg.var p_34.fst, ())⟩ fun p_35 =>
  Expr.load i32 (Arg.var p_35.fst) fun ld =>
  Expr.let_ ⟨OpCode.and i32, (Arg.var ld, Arg.imm 2147483647, ())⟩ fun p_36 =>
  Expr.let_ ⟨OpCode.or i32, (Arg.var p_36.fst, Arg.imm 2147483648, ())⟩ fun p_37 =>
  Expr.let_ ⟨OpCode.and i32, (Arg.var ld_6, Arg.imm 2147483647, ())⟩ fun p_38 =>
  Expr.let_ ⟨OpCode.or i32, (Arg.var p_38.fst, Arg.imm 2147483648, ())⟩ fun p_39 =>
  Expr.group (sig := [[]]) (fun _Js_3 =>
  Blocks.cons (fun _p_40 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 760, ())⟩ fun p =>
  Expr.store (t := i64) (Arg.imm 1) (Arg.var p.fst)
  (
  Expr.jump J1 (Arg.var src, Arg.var dst, Arg.var fred, Arg.var irred, Arg.var redd, Arg.imm 3,
    ()))) Blocks.nil) fun Js =>
  Expr.call (as := [i64, i32, i32, i32, i32]) (bs := [.bool]) "full_watch_push" (Arg.var h,
    Arg.var ld_6, Arg.var p_37.fst, Arg.imm 0, Arg.imm 1, ()) fun p_40 =>
  Expr.jnz (Arg.var p_40.fst)
  (
  Expr.call (as := [i64, i32, i32, i32, i32]) (bs := [.bool]) "full_watch_push" (Arg.var h,
    Arg.var ld, Arg.var p_39.fst, Arg.imm 0, Arg.imm 1, ()) fun p_41 =>
  Expr.jnz (Arg.var p_41.fst)
  (
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 504, ())⟩ fun p_42 =>
  Expr.load i64 (Arg.var p_42.fst) fun ld =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var ld, Arg.imm 1, ())⟩ fun p_43 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 504, ())⟩ fun p =>
  Expr.store (Arg.var p_43.fst) (Arg.var p.fst)
  (
  Expr.jump Jl (Arg.var nsrc, Arg.var dst, Arg.var fred, Arg.var irred, Arg.var redd, ())))
  (
  Expr.jump Js.fst ()))
  (
  Expr.jump Js.fst ()))
  (
  Expr.let_ ⟨OpCode.mul i64, (Arg.var dst, Arg.imm 4, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var arP, Arg.var p.fst, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.or i32, (Arg.imm 8388608, Arg.imm 2097152, ())⟩ fun p_30 =>
  Expr.let_ ⟨OpCode.not i32, (Arg.var p_30.fst, ())⟩ fun p_31 =>
  Expr.let_ ⟨OpCode.and i32, (Arg.var hdr, Arg.var p_31.fst, ())⟩ fun p_32 =>
  Expr.store (Arg.var p_32.fst) (Arg.var p.fst)
  (
  Expr.let_ ⟨OpCode.add i64, (Arg.var dst, Arg.imm 1, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var arP, Arg.var p.fst, ())⟩ fun p =>
  Expr.store (t := i32) (Arg.imm 2) (Arg.var p.fst)
  (
  Expr.let_ ⟨OpCode.add i64, (Arg.var dst, Arg.imm 2, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var arP, Arg.var p.fst, ())⟩ fun p =>
  Expr.store (Arg.var new_sz) (Arg.var p.fst)
  (
  Expr.group (sig := [[i64, i64, i64]]) (fun _Js =>
  Blocks.cons (fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var dst, Arg.imm 3, ())⟩ fun p_33 =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var new_sz, ())⟩ fun p_34 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var p_33.fst, Arg.var p_34.fst, ())⟩ fun p_35 =>
  Expr.jump Jl (Arg.var nsrc, Arg.var p_35.fst, Arg.var p.fst, Arg.var p.snd.fst, Arg.var
    p.snd.snd.fst, ())) Blocks.nil) fun Js =>
  Expr.let_ ⟨OpCode.and i32, (Arg.var hdr, Arg.imm 4194304, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ne i32 Ty.bool rfl, (Arg.var p.fst, Arg.imm 0, ())⟩ fun p =>
  Expr.jnz (Arg.var p.fst)
  (
  Expr.group (sig := [[i64]]) (fun _Js_3 =>
  Blocks.cons (fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var redd, Arg.imm 1, ())⟩ fun p_33 =>
  Expr.jump Js.fst (Arg.var p.fst, Arg.var irred, Arg.var p_33.fst, ())) Blocks.nil) fun Js =>
  Expr.let_ ⟨OpCode.cmp CmpOp.eq i64 Ty.bool rfl, (Arg.var fred, Arg.imm 4294967295, ())⟩ fun p
    =>
  Expr.jnz (Arg.var p.fst)
  (
  Expr.jump Js.fst (Arg.var dst, ()))
  (
  Expr.jump Js.fst (Arg.var fred, ())))
  (
  Expr.let_ ⟨OpCode.add i64, (Arg.var irred, Arg.imm 1, ())⟩ fun p =>
  Expr.jump Js.fst (Arg.var fred, Arg.var p.fst, Arg.var redd, ())))))))))

private def arenaInnerExpr (Val : Ty → Type) (Cont : List Ty → Type)
    (src dst nlits arP valsP mapP : Val i64) (old_sz : Val i32)
    (Ji : Cont [.bool, i32, i32]) : Expr Val Cont [i64] :=
  Expr.group (sig := [[i32, i32]]) (fun Js_2 =>
  Blocks.cons (fun p =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl, (Arg.var p.snd.fst, Arg.var old_sz, ())⟩ fun
    p_26 =>
  Expr.jnz (Arg.var p_26.fst)
  (
  Expr.let_ ⟨OpCode.add i64, (Arg.var src, Arg.imm 3, ())⟩ fun p_27 =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p.snd.fst, ())⟩ fun p_28 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var p_27.fst, Arg.var p_28.fst, ())⟩ fun p_29 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_29.fst, Arg.imm 4, ())⟩ fun p_30 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var arP, Arg.var p_30.fst, ())⟩ fun p_31 =>
  Expr.load i32 (Arg.var p_31.fst) fun ld_6 =>
  Expr.group (sig := [[.bool, i32]]) (fun _Js =>
  Blocks.cons (fun p_32 =>
  Expr.let_ ⟨OpCode.add i32, (Arg.var p.snd.fst, Arg.imm 1, ())⟩ fun p =>
  Expr.jump Js_2.fst (Arg.var p_32.snd.fst, Arg.var p.fst, ())) Blocks.nil) fun Js_3 =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var ld_6, ())⟩ fun p_32 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ult i64 Ty.bool rfl, (Arg.var p_32.fst, Arg.var nlits, ())⟩ fun
    p_33 =>
  Expr.jnz (Arg.var p_33.fst)
  (
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var ld_6, ())⟩ fun p_34 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var valsP, Arg.var p_34.fst, ())⟩ fun p_35 =>
  Expr.load i8 (Arg.var p_35.fst) fun ld_7 =>
  Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun p_36 =>
  Expr.let_ ⟨OpCode.sext 8 32, (Arg.var ld_7, ())⟩ fun p_37 =>
  Expr.let_ ⟨OpCode.sext 8 32, (Arg.var p_36.fst, ())⟩ fun p_38 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.sgt i32 Ty.bool rfl, (Arg.var p_37.fst, Arg.var p_38.fst, ())⟩
    fun p_39 =>
  Expr.jnz (Arg.var p_39.fst)
  (
  Expr.jump Ji (Arg.imm true, Arg.var p.fst, Arg.var p.snd.fst, ()))
  (
  Expr.group (sig := [[.bool, i32]]) (fun _Js =>
  Blocks.cons (fun p =>
  Expr.jump Js_3.fst (Arg.var p.fst, Arg.var p.snd.fst, ())) Blocks.nil) fun Js_4 =>
  Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun p_40 =>
  Expr.let_ ⟨OpCode.sext 8 32, (Arg.var ld_7, ())⟩ fun p_41 =>
  Expr.let_ ⟨OpCode.sext 8 32, (Arg.var p_40.fst, ())⟩ fun p_42 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl, (Arg.var p_41.fst, Arg.var p_42.fst, ())⟩ fun
    p_43 =>
  Expr.jnz (Arg.var p_43.fst)
  (
  Expr.let_ ⟨OpCode.lshr i32, (Arg.var ld_6, Arg.imm 1, ())⟩ fun p_44 =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p_44.fst, ())⟩ fun p_45 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_45.fst, Arg.imm 4, ())⟩ fun p_46 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var mapP, Arg.var p_46.fst, ())⟩ fun p_47 =>
  Expr.load i32 (Arg.var p_47.fst) fun ld_8 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl, (Arg.var ld_8, Arg.imm 4294967295, ())⟩ fun
    p_48 =>
  Expr.jnz (Arg.var p_48.fst)
  (
  Expr.jump Ji (Arg.imm true, Arg.var p.fst, Arg.var p.snd.fst, ()))
  (
  Expr.let_ ⟨OpCode.add i64, (Arg.var dst, Arg.imm 3, ())⟩ fun p_49 =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p.fst, ())⟩ fun p_50 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var p_49.fst, Arg.var p_50.fst, ())⟩ fun p_51 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_51.fst, Arg.imm 4, ())⟩ fun p_52 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var arP, Arg.var p_52.fst, ())⟩ fun p_53 =>
  Expr.let_ ⟨OpCode.shl i32, (Arg.var ld_8, Arg.imm 1, ())⟩ fun p_54 =>
  Expr.let_ ⟨OpCode.and i32, (Arg.var ld_6, Arg.imm 1, ())⟩ fun p_55 =>
  Expr.let_ ⟨OpCode.or i32, (Arg.var p_54.fst, Arg.var p_55.fst, ())⟩ fun p_56 =>
  Expr.store (Arg.var p_56.fst) (Arg.var p_53.fst)
  (
  Expr.let_ ⟨OpCode.add i32, (Arg.var p.fst, Arg.imm 1, ())⟩ fun p =>
  Expr.jump Js_4.fst (Arg.imm false, Arg.var p.fst, ()))))
  (
  Expr.jump Js_4.fst (Arg.imm false, Arg.var p.fst, ()))))
  (
  Expr.jump Js_3.fst (Arg.imm false, Arg.var p.fst, ())))
  (
  Expr.jump Ji (Arg.imm false, Arg.var p.fst, Arg.var p.snd.fst, ()))) Blocks.nil) fun Js =>
  Expr.jump Js.fst (Arg.imm 0, Arg.imm 0, ())

private def flushLoopExpr (Val : Ty → Type) (Cont : List Ty → Type)
    (h : Val i64) : Expr Val Cont [i64] :=
  Expr.group (sig := [[]]) (fun _Js =>
  Blocks.cons (fun _ =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 512, ())⟩ fun p =>
  Expr.store (t := i64) (Arg.imm 0) (Arg.var p.fst)
  (
  Expr.ret (Arg.imm 1, ()))) Blocks.nil) fun Js =>
  Expr.group (sig := [[]]) (fun Js_1 =>
  Blocks.cons (fun _ =>
  Expr.jnz (Arg.imm true)
  (
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 760, ())⟩ fun p_5 =>
  Expr.load i64 (Arg.var p_5.fst) fun ld =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ne i64 Ty.bool rfl, (Arg.var ld, Arg.imm 0, ())⟩ fun p_6 =>
  Expr.jnz (Arg.var p_6.fst)
  (
  Expr.ret (Arg.imm 0, ()))
  (
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 168, ())⟩ fun p_7 =>
  Expr.load i64 (Arg.var p_7.fst) fun ld =>
  Expr.let_ ⟨OpCode.cmp CmpOp.eq i64 Ty.bool rfl, (Arg.var ld, Arg.imm 0, ())⟩ fun p_8 =>
  Expr.jnz (Arg.var p_8.fst)
  (
  Expr.ret (Arg.imm 0, ()))
  (
  Expr.call (as := [i64]) (bs := [i64]) "full_propagate" (Arg.var h, ()) fun p_9 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.eq i64 Ty.bool rfl, (Arg.var p_9.fst, Arg.imm 1, ())⟩ fun p_10 =>
  Expr.jnz (Arg.var p_10.fst)
  (
  Expr.ret (Arg.imm 20, ()))
  (
  Expr.let_ ⟨OpCode.cmp CmpOp.eq i64 Ty.bool rfl, (Arg.var p_9.fst, Arg.imm 2, ())⟩ fun p_11 =>
  Expr.jnz (Arg.var p_11.fst)
  (
  Expr.ret (Arg.imm 0, ()))
  (
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 760, ())⟩ fun p_12 =>
  Expr.load i64 (Arg.var p_12.fst) fun ld =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ne i64 Ty.bool rfl, (Arg.var ld, Arg.imm 0, ())⟩ fun p_13 =>
  Expr.jnz (Arg.var p_13.fst)
  (
  Expr.ret (Arg.imm 0, ()))
  (
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 168, ())⟩ fun p_14 =>
  Expr.load i64 (Arg.var p_14.fst) fun ld =>
  Expr.let_ ⟨OpCode.cmp CmpOp.eq i64 Ty.bool rfl, (Arg.var ld, Arg.imm 0, ())⟩ fun p_15 =>
  Expr.jnz (Arg.var p_15.fst)
  (
  Expr.ret (Arg.imm 0, ()))
  (
  Expr.call (as := [i64]) (bs := [i64]) "full_arena_sweep" (Arg.var h, ()) fun p_16 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.eq i64 Ty.bool rfl, (Arg.var p_16.fst, Arg.imm 2, ())⟩ fun p_17 =>
  Expr.jnz (Arg.var p_17.fst)
  (
  Expr.ret (Arg.imm 20, ()))
  (
  Expr.let_ ⟨OpCode.cmp CmpOp.eq i64 Ty.bool rfl, (Arg.var p_16.fst, Arg.imm 3, ())⟩ fun p_18 =>
  Expr.jnz (Arg.var p_18.fst)
  (
  Expr.ret (Arg.imm 0, ()))
  (
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 760, ())⟩ fun p_19 =>
  Expr.load i64 (Arg.var p_19.fst) fun ld =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ne i64 Ty.bool rfl, (Arg.var ld, Arg.imm 0, ())⟩ fun p_20 =>
  Expr.jnz (Arg.var p_20.fst)
  (
  Expr.ret (Arg.imm 0, ()))
  (
  Expr.let_ ⟨OpCode.cmp CmpOp.eq i64 Ty.bool rfl, (Arg.var p_16.fst, Arg.imm 0, ())⟩ fun p_21 =>
  Expr.jnz (Arg.var p_21.fst)
  (
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 152, ())⟩ fun p_22 =>
  Expr.load i64 (Arg.var p_22.fst) fun ld =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 144, ())⟩ fun p =>
  Expr.load i64 (Arg.var p.fst) fun ld_1 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.uge i64 Ty.bool rfl, (Arg.var ld, Arg.var ld_1, ())⟩ fun p =>
  Expr.jnz (Arg.var p.fst)
  (
  Expr.jump Js.fst ())
  (
  Expr.jump Js_1.fst ()))
  (
  Expr.jump Js_1.fst ())))))))))))
  (
  Expr.jump Js.fst ())) Blocks.nil) fun Js =>
  Expr.jump Js.fst ()

private theorem full_compact_arena_keep {Γ : Env} {Q : Post [i64]} {X : XPost}
    (hpush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    {J1 : Cont [i64, i64, i64, i64, i64, i64]}
    {Jl : Cont [i64, i64, i64, i64, i64]}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ncv : Nat}
    {s sL : FullState} {kCore : FullCoreState} {R : Mem 64 → Prop}
    {arL arI wvecL wstkL wsL : List (BitVec 32)} {wlenL : Nat}
    {wuL nbL oomL src dst fred irred redd nsrc : BitVec 64}
    {hdr old_sz new_sz : BitVec 32} {sat : Bool} {nsrc_nat : Nat} {mI : Mem 64}
    (hkCore : kCore = { s.core with arena := arL, wvec := wvecL, wstk := wstkL, wlen := wlenL,
                                      wusable := wuL, num_binary := nbL, oom := oomL })
    (hsL : sL = { s with core := kCore, scratch := { s.scratch with wsort := wsL } })
    (hnsrc_eq : nsrc = (BitVec.ofNat 32 nsrc_nat).setWidth 64)
    (hext_u : (cnfOfClauses F_cur).Unsat → F0.Unsat)
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hal_le : s.core.arena_len ≤ c.arena_cap)
    (hmax_lt : c.max_vars < 2 * 2 ^ 28) (har_cap_lt : c.arena_cap < 2 * 2 ^ 28)
    (hncv_le : ncv ≤ s.core.cur_vars)
    (hd_le : dst.toNat ≤ src.toNat) (hsrc_lt : src.toNat < s.core.arena_len)
    (hsz3 : 3 ≤ old_sz.toNat) (hfit_src : src.toNat + 3 + old_sz.toNat ≤ s.core.arena_len)
    (hnsrc_bounds : src.toNat + 3 + old_sz.toNat ≤ nsrc_nat ∧ nsrc_nat ≤ s.core.arena_len ∧
      (nsrc_nat = s.core.arena_len ∨ nsrc_nat + 3 ≤ s.core.arena_len))
    (hnsrc_to : (BitVec.ofNat 64 nsrc_nat).toNat = nsrc_nat)
    (hnsrc64 : (BitVec.ofNat 32 nsrc_nat).setWidth 64 = BitVec.ofNat 64 nsrc_nat)
    (hnsrc_mem : nsrc_nat = s.core.arena_len ∨ nsrc_nat ∈ fullArenaClauseRefsCore s.core)
    (hng : (hdr &&& 0x00080000#32) = 0#32)
    (hckL : FullCoreState.LengthsOk c kCore) (hws_ok : FullScratch.LengthsOk c s.scratch)
    (hwsL_len : wsL.length = 2 * c.max_vars)
    (har_tail : ∀ j, nsrc_nat ≤ j → j < s.core.arena_len → arL[j]? = s.core.arena[j]?)
    (hpreL : CompactArenaPrefix c ncv s.scratch.work_stk2 F_cur arL dst.toNat)
    (hbinL : CompactUnmapBinsOk ncv s.scratch.work_stk2 F_cur kCore)
    (hns_le : new_sz.toNat ≤ old_sz.toNat) (harI : arI.length = c.arena_cap)
    (hpresI : ∀ k, (k < dst.toNat ∨ dst.toNat + 3 + new_sz.toNat ≤ k) →
      k < s.core.arena_len → arI[k]? = arL[k]?)
    (hsatI : sat = false →
      let kept := ((arI.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat
      (∀ j < new_sz.toNat, (arI[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * ncv) ∧
      (kept.map (· / 2)).Nodup ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause (kept.map (compactUnmapLit s.scratch.work_stk2))))
    (hmI : (FullMem c { sL with core := { kCore with arena := arI } } ⋆ R) mI)
    (hJ1 : ∀ (xs : Tup Val [i64, i64, i64, i64, i64, i64]) (mE : Mem 64),
      (xs.2.1.toNat ≤ s.core.arena_len ∧
        (xs.2.2.2.2.2.1 = 0#64 ∨ xs.2.2.2.2.2.1 = 2#64 ∨ xs.2.2.2.2.2.1 = 3#64) ∧
        (xs.2.2.2.2.2.1 = 2#64 → F0.Unsat) ∧
        ∃ (arE wvecE wstkE : List (BitVec 32)) (wlenE : Nat) (wuE nbE oomE : BitVec 64)
          (wsE : List (BitVec 32)),
          let kE : FullCoreState :=
            { s.core with arena := arE, wvec := wvecE, wstk := wstkE, wlen := wlenE,
                          wusable := wuE, num_binary := nbE, oom := oomE }
          FullCoreState.LengthsOk c kE ∧ wsE.length = 2 * c.max_vars ∧
          (xs.2.2.2.2.2.1 = 3#64 → oomE = 1#64) ∧
          CompactArenaPrefix c ncv s.scratch.work_stk2 F_cur arE xs.2.1.toNat ∧
          CompactUnmapBinsOk ncv s.scratch.work_stk2 F_cur kE ∧
          (FullMem c { s with core := kE, scratch := { s.scratch with wsort := wsE } } ⋆ R) mE) →
      J1 xs mE)
    (hLoopL : ∀ (xs : Tup Val [i64, i64, i64, i64, i64]) (m' : Mem 64),
      s.core.arena_len - xs.1.toNat < s.core.arena_len - src.toNat →
      (xs.2.1.toNat ≤ xs.1.toNat ∧ xs.1.toNat ≤ s.core.arena_len ∧
        (xs.1.toNat = s.core.arena_len ∨ xs.1.toNat ∈ fullArenaClauseRefsCore s.core) ∧
        ∃ (arL wvecL wstkL : List (BitVec 32)) (wlenL : Nat) (wuL nbL oomL : BitVec 64)
          (wsL : List (BitVec 32)),
          let kL : FullCoreState :=
            { s.core with arena := arL, wvec := wvecL, wstk := wstkL, wlen := wlenL,
                          wusable := wuL, num_binary := nbL, oom := oomL }
          FullCoreState.LengthsOk c kL ∧ wsL.length = 2 * c.max_vars ∧
          (∀ j, xs.1.toNat ≤ j → j < s.core.arena_len → arL[j]? = s.core.arena[j]?) ∧
          CompactArenaPrefix c ncv s.scratch.work_stk2 F_cur arL xs.2.1.toNat ∧
          CompactUnmapBinsOk ncv s.scratch.work_stk2 F_cur kL ∧
          (FullMem c { s with core := kL, scratch := { s.scratch with wsort := wsL } } ⋆ R) m') →
      Jl xs m') :
    wp Γ Q X (arenaKeepExpr Val Cont c.hdr src dst fred irred redd nsrc c.pArena hdr sat
      new_sz J1 Jl) mI := by
  unfold arenaKeepExpr
  subst hkCore hsL
  let inv := s.scratch.work_stk2
  let kI : FullCoreState :=
    { s.core with arena := arI, wvec := wvecL, wstk := wstkL, wlen := wlenL, wusable := wuL,
                  num_binary := nbL, oom := oomL }
  let sI : FullState := { s with core := kI, scratch := { s.scratch with wsort := wsL } }
  have hckI : FullCoreState.LengthsOk c kI := { hckL with arena_len_arr := harI }
  have hpreI : CompactArenaPrefix c ncv inv F_cur arI dst.toNat :=
    compactArenaPrefix_congr hpreL (by omega) fun i hi => hpresI i (Or.inl hi) (by omega)
  have har_tailI : ∀ j, nsrc_nat ≤ j → j < s.core.arena_len →
      arI[j]? = s.core.arena[j]? := fun j hj1 hj2 =>
    (hpresI j (Or.inr (by omega)) hj2).trans (har_tail j (by omega) hj2)
  have hbinI : CompactUnmapBinsOk ncv inv F_cur kI :=
    ⟨⟨hbinL.layout.bounds, hbinL.layout.pos_off, hbinL.layout.disjoint, hbinL.layout.no_sentinel⟩,
     hbinL.empty_hi, fun l hl => by
       have hs0 := hbinL.slices l hl
       unfold fullWatchOffCore fullWatchSizeCore at hs0 ⊢
       exact hs0.relocate (fun _ _ => by rfl)⟩
  cm_split
  · cm_steps
    exact hLoopL (nsrc, dst, fred, irred, redd, ()) mI
      (by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; omega)
      ⟨by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; omega,
       by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; omega,
       by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; exact hnsrc_mem,
       arI, wvecL, wstkL, wlenL, wuL, nbL, oomL, wsL, hckI, hwsL_len,
       by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; exact har_tailI, hpreI, hbinI, hmI⟩
  · have hsat_f : sat = false := by c0_bound
    obtain ⟨hkl_lt, hkl_nd, hkl_ent⟩ := hsatI hsat_f
    cm_split
    · have hns0 : new_sz.toNat = 0 := by c0_bound
      have hnil : ((arI.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat = [] := by
        simp [hns0]
      rw [hnil, List.map_nil] at hkl_ent
      have hunsat : F0.Unsat := hext_u (unsat_of_entails_nil hkl_ent)
      cm_steps
      exact hJ1 (src, dst, fred, irred, redd, 2#64, ()) mI
        ⟨by dsimp only; omega, Or.inr (Or.inl rfl), fun _ => hunsat, arI, wvecL, wstkL, wlenL,
         wuL, nbL, oomL, wsL, hckI, hwsL_len,
         fun h => by dsimp only at h; exact absurd h (by decide), hpreI, hbinI, hmI⟩
    · cm_split
      · cm_steps
        exact hLoopL (nsrc, dst, fred, irred, redd, ()) mI
          (by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; omega)
          ⟨by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; omega,
           by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; omega,
           by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; exact hnsrc_mem,
           arI, wvecL, wstkL, wlenL, wuL, nbL, oomL, wsL, hckI, hwsL_len,
           by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; exact har_tailI, hpreI, hbinI, hmI⟩
      · cm_split
        · have hns2 : new_sz.toNat = 2 := by c0_bound
          have hd3_lt : dst.toNat + 3 < arI.length := by omega
          have hd4_lt : dst.toNat + 4 < arI.length := by omega
          let l0 := arI[dst.toNat + 3]'hd3_lt
          let l1 := arI[dst.toNat + 4]'hd4_lt
          have hl0_lt : l0.toNat < 2 * ncv := by
            have := hkl_lt 0 (by omega)
            rwa [List.getElem?_eq_getElem hd3_lt, Option.getD_some] at this
          have hl1_lt : l1.toNat < 2 * ncv := by
            have := hkl_lt 1 (by omega)
            rwa [List.getElem?_eq_getElem hd4_lt, Option.getD_some] at this
          have hkept2 :
              ((arI.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat =
              [l0.toNat, l1.toNat] := by
            rw [hns2]
            have ha := drop_take_succ_cm hd3_lt (off := dst.toNat + 3) (n := 0)
            have hb := drop_take_succ_cm hd4_lt (off := dst.toNat + 3) (n := 1)
            simp only [Nat.add_zero, List.take_zero, List.nil_append] at ha
            rw [hb, ha]; rfl
          rw [hkept2] at hkl_ent
          have hkl_ent10 : (cnfOfClauses F_cur).EntailsClause
              (cnfClause [compactUnmapLit inv l1.toNat, compactUnmapLit inv l0.toNat]) := by
            refine entails_of_mem_or_false hkl_ent fun x hx => ?_
            simp only [List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hx
            obtain ⟨a, rfl | rfl, rfl⟩ := hx
            · exact Or.inl (by simp [inv])
            · exact Or.inl (by simp [inv])
          have hbw0 := bv32_bin_word_props (show l1.toNat < 0x7FFFFFFF by omega)
          have hbw1 := bv32_bin_word_props (show l0.toNat < 0x7FFFFFFF by omega)
          have hd3_nat : (dst + (3 : BitVec 64)).toNat = dst.toNat + 3 :=
            bv64_add3 (by omega)
          have hd4_nat : (dst + (4 : BitVec 64)).toNat = dst.toNat + 4 :=
            bv64_add4 (by omega)
          cm_steps; c0_call hpush
          refine ⟨c, sI, R, rfl, ⟨hckI, { hws_ok with wsort_len := hwsL_len }⟩,
            hbinI.layout, fun _ => by simp only [hd4_nat]; exact hbw0.2.1,
            fun hc2 => absurd hc2 (by decide), hmI,
            fun ok0 wvec0 wstk0 wlen0 wu0 ws0 m0 hlen0 hlay0 hoth0 hok0_t hok0_f hm0 => ?_⟩
          clear hmI
          have hl0_bv_eq :
              (arI[(dst + (3 : BitVec 64)).toNat]'(by rw [hd3_nat]; exact hd3_lt)).toNat =
              l0.toNat := congrArg BitVec.toNat (by simp only [hd3_nat]; rfl)
          have hbin0' : CompactUnmapBinsOk ncv inv F_cur
              { kI with wvec := wvec0, wstk := wstk0, wlen := wlen0, wusable := wu0 } := by
            cases ok0 with
            | false =>
              refine ⟨hlay0, fun l h1 h2 => ?_, fun l hl => ?_⟩
              · change l < 2 * s.core.cur_vars at h2
                have h2I : l < 2 * sI.core.cur_vars := h2
                exact (hoth0 l h2I (by rw [hl0_bv_eq]; omega)).1.trans (hbinI.empty_hi l h1 h2)
              · have hlI : l < 2 * sI.core.cur_vars := by change l < 2 * s.core.cur_vars; omega
                by_cases he : l = l0.toNat
                · obtain ⟨hsz, hpre⟩ := (hok0_f rfl).1 (by rw [hl0_bv_eq]; rw [← he]; exact hlI)
                  rw [hl0_bv_eq, ← he] at hsz hpre
                  dsimp only [fullWatchOff, fullWatchSize, fullWatchOffCore,
                    fullWatchSizeCore] at hsz hpre ⊢
                  rw [hsz]; exact (hbinI.slices _ hl).relocate hpre
                · obtain ⟨hsz, hoth⟩ := hoth0 l hlI (by rw [hl0_bv_eq]; exact he)
                  dsimp only [fullWatchOff, fullWatchSize, fullWatchOffCore,
                    fullWatchSizeCore] at hsz hoth ⊢
                  rw [hsz]; exact (hbinI.slices l hl).relocate hoth
            | true =>
              obtain ⟨_, _, hsz0, hpre0, hw0, _⟩ := hok0_t rfl
              rw [hl0_bv_eq] at hsz0 hpre0 hw0
              simp only [hd4_nat] at hw0
              refine ⟨hlay0, fun l h1 h2 => ?_, fun l hl => ?_⟩
              · change l < 2 * s.core.cur_vars at h2
                have h2I : l < 2 * sI.core.cur_vars := h2
                exact (hoth0 l h2I (by rw [hl0_bv_eq]; omega)).1.trans (hbinI.empty_hi l h1 h2)
              · have hlI : l < 2 * sI.core.cur_vars := by change l < 2 * s.core.cur_vars; omega
                by_cases he : l = l0.toNat
                · subst he
                  dsimp only [fullWatchOff, fullWatchSize, fullWatchOffCore,
                    fullWatchSizeCore] at hsz0 hpre0 hw0 ⊢
                  rw [hsz0]
                  exact (hbinI.slices _ hl).append_bin hpre0 hw0 hbw0.1 hbw0.2.1
                    (by
                      change (((l1 &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&&
                        0x7FFFFFFF#32).toNat < 2 * ncv
                      rw [hbw0.2.2]; exact hl1_lt)
                    (by
                      change (cnfOfClauses F_cur).EntailsClause (cnfClause
                        [compactUnmapLit inv l0.toNat,
                         compactUnmapLit inv (((l1 &&& 0x7FFFFFFF#32) |||
                           0x80000000#32) &&& 0x7FFFFFFF#32).toNat])
                      rw [hbw0.2.2]; exact hkl_ent)
                · obtain ⟨hsz, hoth⟩ := hoth0 l hlI (by rw [hl0_bv_eq]; exact he)
                  dsimp only [fullWatchOff, fullWatchSize, fullWatchOffCore,
                    fullWatchSizeCore] at hsz hoth ⊢
                  rw [hsz]; exact (hbinI.slices l hl).relocate hoth
          cm_split
          · let sI0 : FullState :=
              { sI with core := { kI with wvec := wvec0, wstk := wstk0, wlen := wlen0,
                                          wusable := wu0 },
                        scratch := { sI.scratch with wsort := ws0 } }
            cm_steps; c0_call hpush
            refine ⟨c, sI0, R, rfl, hlen0, hbin0'.layout,
              fun _ => by simp only [hd3_nat]; exact hbw1.2.1,
              fun hc2 => absurd hc2 (by decide), hm0,
              fun ok1 wvec1 wstk1 wlen1 wu1 ws1 m1 hlen1 hlay1 hoth1
                hok1_t hok1_f hm1 => ?_⟩
            clear hm0
            have hl1_bv_eq :
                (arI[(dst + (4 : BitVec 64)).toNat]'(by rw [hd4_nat]; exact hd4_lt)).toNat =
                  l1.toNat := congrArg BitVec.toNat (by simp only [hd4_nat]; rfl)
            have hbin1' : CompactUnmapBinsOk ncv inv F_cur
                { sI0.core with wvec := wvec1, wstk := wstk1, wlen := wlen1,
                                wusable := wu1 } := by
              cases ok1 with
              | false =>
                refine ⟨hlay1, fun l h1 h2 => ?_, fun l hl => ?_⟩
                · change l < 2 * s.core.cur_vars at h2
                  have h2I : l < 2 * sI0.core.cur_vars := h2
                  exact (hoth1 l h2I (by rw [hl1_bv_eq]; omega)).1.trans (hbin0'.empty_hi l h1 h2)
                · have hlI : l < 2 * sI0.core.cur_vars := by change l < 2 * s.core.cur_vars; omega
                  by_cases he : l = l1.toNat
                  · obtain ⟨hsz, hpre⟩ := (hok1_f rfl).1 (by rw [hl1_bv_eq]; rw [← he]; exact hlI)
                    rw [hl1_bv_eq, ← he] at hsz hpre
                    dsimp only [fullWatchOff, fullWatchSize, fullWatchOffCore,
                      fullWatchSizeCore] at hsz hpre ⊢
                    rw [hsz]; exact (hbin0'.slices _ hl).relocate hpre
                  · obtain ⟨hsz, hoth⟩ := hoth1 l hlI (by rw [hl1_bv_eq]; exact he)
                    dsimp only [fullWatchOff, fullWatchSize, fullWatchOffCore,
                      fullWatchSizeCore] at hsz hoth ⊢
                    rw [hsz]; exact (hbin0'.slices l hl).relocate hoth
              | true =>
                obtain ⟨_, _, hsz1, hpre1, hw1, _⟩ := hok1_t rfl
                rw [hl1_bv_eq] at hsz1 hpre1 hw1
                simp only [hd3_nat] at hw1
                refine ⟨hlay1, fun l h1 h2 => ?_, fun l hl => ?_⟩
                · change l < 2 * s.core.cur_vars at h2
                  have h2I : l < 2 * sI0.core.cur_vars := h2
                  exact (hoth1 l h2I (by rw [hl1_bv_eq]; omega)).1.trans (hbin0'.empty_hi l h1 h2)
                · have hlI : l < 2 * sI0.core.cur_vars := by change l < 2 * s.core.cur_vars; omega
                  by_cases he : l = l1.toNat
                  · subst he
                    dsimp only [fullWatchOff, fullWatchSize, fullWatchOffCore,
                      fullWatchSizeCore] at hsz1 hpre1 hw1 ⊢
                    rw [hsz1]
                    exact (hbin0'.slices _ hl).append_bin hpre1 hw1 hbw1.1 hbw1.2.1
                      (by
                        change (((l0 &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&&
                          0x7FFFFFFF#32).toNat < 2 * ncv
                        rw [hbw1.2.2]; exact hl0_lt)
                      (by
                        change (cnfOfClauses F_cur).EntailsClause (cnfClause
                          [compactUnmapLit inv l1.toNat,
                           compactUnmapLit inv (((l0 &&& 0x7FFFFFFF#32) |||
                             0x80000000#32) &&& 0x7FFFFFFF#32).toNat])
                        rw [hbw1.2.2]; exact hkl_ent10)
                  · obtain ⟨hsz, hoth⟩ := hoth1 l hlI (by rw [hl1_bv_eq]; exact he)
                    dsimp only [fullWatchOff, fullWatchSize, fullWatchOffCore,
                      fullWatchSizeCore] at hsz hoth ⊢
                    rw [hsz]; exact (hbin0'.slices l hl).relocate hoth
            cm_split
            · cm_steps
              exact hLoopL (nsrc, dst, fred, irred, redd, ()) _
                (by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; omega)
                ⟨by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; omega,
                 by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; omega,
                 by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; exact hnsrc_mem,
                 arI, wvec1, wstk1, wlen1, wu1, nbL + 1#64, oomL, ws1,
                 { hlen1.core_ok with cur_vars_le := hckL.cur_vars_le },
                 hlen1.scratch_ok.wsort_len,
                 by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; exact har_tailI, hpreI,
                 ⟨⟨hbin1'.layout.bounds, hbin1'.layout.pos_off, hbin1'.layout.disjoint,
                    hbin1'.layout.no_sentinel⟩, hbin1'.empty_hi, fun l hl => by
                    have hs0 := hbin1'.slices l hl
                    unfold fullWatchOffCore fullWatchSizeCore at hs0 ⊢
                    exact hs0.relocate (fun _ _ => by rfl)⟩,
                 by assumption⟩
            · cm_steps
              exact hJ1 (src, dst, fred, irred, redd, 3#64, ()) _
                ⟨by dsimp only; omega, Or.inr (Or.inr rfl),
                 fun h => by dsimp only at h; exact absurd h (by decide),
                 arI, wvec1, wstk1, wlen1, wu1, nbL, 1#64, ws1, { hlen1.core_ok with },
                 hlen1.scratch_ok.wsort_len, fun _ => rfl, hpreI,
                 ⟨⟨hbin1'.layout.bounds, hbin1'.layout.pos_off, hbin1'.layout.disjoint,
                    hbin1'.layout.no_sentinel⟩, hbin1'.empty_hi, fun l hl => by
                    have hs0 := hbin1'.slices l hl
                    unfold fullWatchOffCore fullWatchSizeCore at hs0 ⊢
                    exact hs0.relocate (fun _ _ => by rfl)⟩,
                 by assumption⟩
          · cm_steps
            exact hJ1 (src, dst, fred, irred, redd, 3#64, ()) _
              ⟨by dsimp only; omega, Or.inr (Or.inr rfl),
               fun h => by dsimp only at h; exact absurd h (by decide),
               arI, wvec0, wstk0, wlen0, wu0, nbL, 1#64, ws0, { hlen0.core_ok with },
               hlen0.scratch_ok.wsort_len, fun _ => rfl, hpreI,
               ⟨⟨hbin0'.layout.bounds, hbin0'.layout.pos_off, hbin0'.layout.disjoint,
                  hbin0'.layout.no_sentinel⟩, hbin0'.empty_hi, fun l hl => by
                  have hs0 := hbin0'.slices l hl
                  unfold fullWatchOffCore fullWatchSizeCore at hs0 ⊢
                  exact hs0.relocate (fun _ _ => by rfl)⟩,
               by assumption⟩
        · have hns3 : 3 ≤ new_sz.toNat := by c0_bound
          have hdst_lt_cap : dst.toNat + 3 + new_sz.toNat ≤ s.core.arena_len := by omega
          have hd0_lt : dst.toNat < arI.length := by omega
          have hd1_lt : dst.toNat + 1 < arI.length := by omega
          have hd2_lt : dst.toNat + 2 < arI.length := by omega
          have hd3_eq : (dst + (3 : BitVec 64) + new_sz.setWidth 64).toNat =
              dst.toNat + 3 + new_sz.toNat := bv64_add3_zext_toNat (by omega)
          let arW :=
            ((arI.set dst.toNat (hdr &&& ~~~(0x00800000#32 ||| 0x00200000#32))).set
              (dst.toNat + 1) 2#32).set (dst.toNat + 2) new_sz
          have hclear := bv32_clear_shrk_rsn hdr hng
          have hdrop_len : ((arW.drop (dst.toNat + 3)).take new_sz.toNat).length =
              ((arI.drop (dst.toNat + 3)).take new_sz.toNat).length := by
            simp [arW, harI]
          have hdrop_eq : (arW.drop (dst.toNat + 3)).take new_sz.toNat =
              (arI.drop (dst.toNat + 3)).take new_sz.toNat := by
            refine List.ext_getElem hdrop_len fun j h1 h2 => ?_
            simp only [List.length_take, List.length_drop, arW, List.length_set] at h1 h2
            rw [List.getElem_take, List.getElem_drop, List.getElem_take, List.getElem_drop]
            apply Option.some.inj
            rw [← List.getElem?_eq_getElem (by simp [arW, harI]; omega),
              ← List.getElem?_eq_getElem (by omega : dst.toNat + 3 + j < arI.length)]
            dsimp only [arW]
            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
              List.getElem?_set_ne (by omega)]
          have hpreW : CompactArenaPrefix c ncv inv F_cur arW (dst.toNat + 3 + new_sz.toNat) := by
            apply compactArenaPrefix_append hpreI hns3 (by simp [arW, harI]; omega)
            · intro j hj; dsimp only [arW]
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                List.getElem?_set_ne (by omega)]
            · dsimp only [arW]
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                List.getElem?_set_self (by omega), Option.getD_some]; exact hclear.1
            · dsimp only [arW]
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                List.getElem?_set_self (by omega), Option.getD_some]; exact hclear.2
            · dsimp only [arW]
              rw [List.getElem?_set_self (by simp [harI]; omega), Option.getD_some]
            · intro j hj; dsimp only [arW]
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                List.getElem?_set_ne (by omega)]
              exact hkl_lt j hj
            · rw [hdrop_eq]; exact hkl_nd
            · rw [hdrop_eq]; exact hkl_ent
          have har_tailW : ∀ j, nsrc_nat ≤ j → j < s.core.arena_len →
              arW[j]? = s.core.arena[j]? := fun j hj1 hj2 => by
            dsimp only [arW]
            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
              List.getElem?_set_ne (by omega)]
            exact har_tailI j hj1 hj2
          have harW_len : arW.length = c.arena_cap := by simp [arW, harI]
          have hckW : FullCoreState.LengthsOk c { kI with arena := arW } :=
            { hckI with arena_len_arr := harW_len }
          have hbinW : CompactUnmapBinsOk ncv inv F_cur { kI with arena := arW } :=
            ⟨⟨hbinI.layout.bounds, hbinI.layout.pos_off, hbinI.layout.disjoint,
              hbinI.layout.no_sentinel⟩, hbinI.empty_hi, fun l hl => by
              have hs0 := hbinI.slices l hl
              unfold fullWatchOffCore fullWatchSizeCore at hs0 ⊢
              exact hs0.relocate (fun _ _ => by rfl)⟩
          have hcontW : ∀ (f i r : BitVec 64) (mW : Mem 64),
              (FullMem c { sI with core := { kI with arena := arW } } ⋆ R) mW →
              Jl (nsrc, dst + (3 : BitVec 64) + new_sz.setWidth 64, f, i, r, ()) mW :=
            fun f i r mW hmW =>
              hLoopL (nsrc, dst + (3 : BitVec 64) + new_sz.setWidth 64, f, i, r, ()) mW
                (by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; omega)
              ⟨by dsimp only; rw [hd3_eq, hnsrc_eq, hnsrc64, hnsrc_to]; omega,
               by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; omega,
               by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; exact hnsrc_mem, arW, wvecL, wstkL,
               wlenL, wuL, nbL, oomL, wsL, hckW, hwsL_len,
               by dsimp only; rw [hnsrc_eq, hnsrc64, hnsrc_to]; exact har_tailW,
               by dsimp only; rw [hd3_eq]; exact hpreW, hbinW, hmW⟩
          have hd1_nat : (dst + (1 : BitVec 64)).toNat = dst.toNat + 1 := bv64_add1 (by omega)
          have hd2_nat : (dst + (2 : BitVec 64)).toNat = dst.toNat + 2 := bv64_add2 (by omega)
          have harW_eq : arW =
              ((arI.set dst.toNat (hdr &&& ~~~(0x00800000#32 ||| 0x00200000#32))).set
                (dst + (1 : BitVec 64)).toNat 2#32).set
                (dst + (2 : BitVec 64)).toNat new_sz := by
            dsimp only [arW]; rw [hd1_nat, hd2_nat]
          cm_steps
          · exact hcontW dst irred (redd + 1#64) _ (by rw [harW_eq]; exact (by assumption))
          · exact hcontW fred irred (redd + 1#64) _ (by rw [harW_eq]; exact (by assumption))
          · exact hcontW fred (irred + 1#64) redd _ (by rw [harW_eq]; exact (by assumption))

private theorem full_compact_arena_inner {Γ : Env} {Q : Post [i64]} {X : XPost}
    {Ji : Cont [.bool, i32, i32]}
    {c : FullCfg} {F_cur : List (List Nat)} {ncv : Nat}
    {s kL : FullState} {kCore : FullCoreState} {R : Mem 64 → Prop}
    {arL wvecL wstkL wsL : List (BitVec 32)} {wlenL : Nat}
    {wuL nbL oomL src dst nlits old_cv : BitVec 64} {old_sz : BitVec 32}
    {olits : List Nat} {mL : Mem 64}
    (hkCore : kCore = { s.core with arena := arL, wvec := wvecL, wstk := wstkL, wlen := wlenL,
                                      wusable := wuL, num_binary := nbL, oom := oomL })
    (hkL : kL = { s with core := kCore, scratch := { s.scratch with wsort := wsL } })
    (hckL : FullCoreState.LengthsOk c kCore)
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hal_le : s.core.arena_len ≤ c.arena_cap) (hv_len : s.core.vals.length = 2 * c.max_vars)
    (hws1_len : s.scratch.work_stk1.length = 2 * c.max_vars)
    (hmax_lt : c.max_vars < 2 * 2 ^ 28) (har_cap_lt : c.arena_cap < 2 * 2 ^ 28)
    (hold : s.core.cur_vars = old_cv.toNat) (hnlits : nlits.toNat = 2 * old_cv.toNat)
    (_hncv_le : ncv ≤ old_cv.toNat)
    (hbij : CompactBijOk old_cv.toNat ncv s.core.vals s.scratch.work_stk1 s.scratch.work_stk2)
    (hdom : ∀ l < 2 * old_cv.toNat,
      s.core.vals[l]?.getD 0#8 = 0#8 ∨ s.core.vals[l]?.getD 0#8 = 1#8 ∨
        s.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hfent : ∀ l < 2 * old_cv.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8 →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1]))
    (hd_le : dst.toNat ≤ src.toNat)
    (hfit_src : src.toNat + 3 + old_sz.toNat ≤ s.core.arena_len)
    (hol_len : olits.length = old_sz.toNat)
    (hol_mem : ∀ j < old_sz.toNat,
      olits[j]? = (s.core.arena[src.toNat + 3 + j]?).map BitVec.toNat)
    (hol_lt : ∀ l ∈ olits, l < 2 * old_cv.toNat)
    (hol_nd : (olits.map (· / 2)).Nodup)
    (hent_ol : (cnfOfClauses F_cur).EntailsClause (cnfClause olits))
    (har_tail_inner : ∀ j, src.toNat + 3 ≤ j → j < src.toNat + 3 + old_sz.toNat →
      arL[j]? = s.core.arena[j]?)
    (hmL : (FullMem c kL ⋆ R) mL)
    (hJi : ∀ (xs : Tup Val [.bool, i32, i32]) (mI : Mem 64),
      (xs.2.1.toNat ≤ old_sz.toNat ∧
        ∃ arI : List (BitVec 32), arI.length = c.arena_cap ∧
          (∀ k, (k < dst.toNat ∨ dst.toNat + 3 + xs.2.1.toNat ≤ k) →
            k < s.core.arena_len → arI[k]? = arL[k]?) ∧
          (xs.1 = false →
            let kept := ((arI.drop (dst.toNat + 3)).take xs.2.1.toNat).map BitVec.toNat
            (∀ j < xs.2.1.toNat, (arI[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * ncv) ∧
            (kept.map (· / 2)).Nodup ∧
            (cnfOfClauses F_cur).EntailsClause
              (cnfClause (kept.map (compactUnmapLit s.scratch.work_stk2)))) ∧
          (FullMem c { kL with core := { kCore with arena := arI } } ⋆ R) mI) →
      Ji xs mI) :
    wp Γ Q X (arenaInnerExpr Val Cont src dst nlits c.pArena c.pVals c.pWorkStk1 old_sz Ji)
      mL := by
  unfold arenaInnerExpr
  subst hkCore hkL
  let inv := s.scratch.work_stk2
  let kCore : FullCoreState :=
    { s.core with arena := arL, wvec := wvecL, wstk := wstkL, wlen := wlenL, wusable := wuL,
                  num_binary := nbL, oom := oomL }
  let kL : FullState := { s with core := kCore, scratch := { s.scratch with wsort := wsL } }
  refine wp_loop_inv
    (fun (new_sz, i, ()) mI =>
      i.toNat ≤ old_sz.toNat ∧ new_sz.toNat ≤ i.toNat ∧
      ∃ arI : List (BitVec 32), arI.length = c.arena_cap ∧
        (∀ k, (k < dst.toNat ∨ dst.toNat + 3 + new_sz.toNat ≤ k) →
          k < s.core.arena_len → arI[k]? = arL[k]?) ∧
        (let kept := ((arI.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat
         (∀ j < new_sz.toNat, (arI[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * ncv) ∧
         (kept.map (· / 2)).Nodup ∧
         (∀ x ∈ kept, x / 2 < ncv ∧
           (inv[x / 2]?.getD 0#32).toNat ∈ (olits.take i.toNat).map (· / 2)) ∧
         ∀ l ∈ olits.take i.toNat,
           l ∈ kept.map (compactUnmapLit inv) ∨
           (l < 2 * old_cv.toNat ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1]))) ∧
        (FullMem c { kL with core := { kCore with arena := arI } } ⋆ R) mI)
    (fun (_, i, ()) _ => old_sz.toNat - i.toNat)
    (fun Ji' hLoopI => ?_) ?_
  · cm_steps
    refine hLoopI (0#32, 0#32, ()) mL ⟨Nat.zero_le _, Nat.zero_le _, arL, hckL.arena_len_arr,
      fun _ _ _ => rfl, ?_, hmL⟩
    refine ⟨fun j hj => by simp at hj, ?_, ?_, ?_⟩ <;> simp
  · rintro Ji' ⟨new_sz, i, ⟨⟩⟩ mI ⟨hi_le, hns_le, arI, harI, hpresI, hsatI, hmI⟩ hLoopI
    cm_split
    · have hi_lt : i.toNat < old_sz.toNat := by c0_bound
      have hi1_eq : (i + (1 : BitVec 32)).toNat = i.toNat + 1 := bv32_add1 (by omega)
      have hsi_eq : (src + (3 : BitVec 64) + i.setWidth 64).toNat =
          src.toNat + 3 + i.toNat := bv64_add3_zext_toNat (by omega)
      have hsi_lt : src.toNat + 3 + i.toNat < arI.length := by omega
      have hsi_ar : arI[src.toNat + 3 + i.toNat]? = s.core.arena[src.toNat + 3 + i.toNat]? :=
        (hpresI (src.toNat + 3 + i.toNat) (Or.inr (by omega)) (by omega)).trans
          (har_tail_inner (src.toNat + 3 + i.toNat) (by omega) (by omega))
      let lit := arI[src.toNat + 3 + i.toNat]'hsi_lt
      have hlit_mem : lit.toNat ∈ olits := by
        have hm' := hol_mem i.toNat hi_lt
        rw [← hsi_ar, List.getElem?_eq_getElem hsi_lt, Option.map_some,
          List.getElem?_eq_getElem (by rw [hol_len]; exact hi_lt)] at hm'
        exact (Option.some.inj hm') ▸ List.getElem_mem (by rw [hol_len]; exact hi_lt)
      have hlit_eq_ol : olits[i.toNat]? = some lit.toNat := by
        have hm' := hol_mem i.toNat hi_lt
        rwa [← hsi_ar, List.getElem?_eq_getElem hsi_lt, Option.map_some] at hm'
      have hlit_lt_cv : lit.toNat < 2 * old_cv.toNat := hol_lt lit.toNat hlit_mem
      have htake_succ : olits.take (i.toNat + 1) = olits.take i.toNat ++ [lit.toNat] := by
        rw [List.take_add_one, hlit_eq_ol, Option.toList_some]
      cm_split
      · have hlit_lt64 : lit.toNat < 2 * old_cv.toNat := by c0_bound
        have hlit_vals : lit.toNat < s.core.vals.length := by omega
        have hlit_ws1 : (lit >>> 1#32).toNat < s.scratch.work_stk1.length := by
          rw [bv32_shr1_toNat]; omega
        have hlit_bv64 : (BitVec.setWidth 64
            (arI[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'(by
              rw [hsi_eq]; exact hsi_lt))).toNat < kCore.vals.length := by
          rw [zext_toNat _ (by decide)]; simp only [hsi_eq]; exact hlit_vals
        have hws1_bv64 : (BitVec.setWidth 64
            ((arI[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'(by
              rw [hsi_eq]; exact hsi_lt)) >>> 1#32)).toNat <
            kL.scratch.work_stk1.length := by
          rw [zext_toNat _ (by decide)]; simp only [hsi_eq]; exact hlit_ws1
        cm_steps
        · exact hJi (true, new_sz, i, ()) mI
            ⟨Nat.le_trans hns_le hi_le, arI, harI, hpresI, fun hf => Bool.noConfusion hf, hmI⟩
        · exact hJi (true, new_sz, i, ()) mI
            ⟨Nat.le_trans hns_le hi_le, arI, harI, hpresI, fun hf => Bool.noConfusion hf, hmI⟩
        · have hidx_s : (src.toNat + 3 + i.toNat) % 2 ^ 64 = src.toNat + 3 + i.toNat :=
            Nat.mod_eq_of_lt (by omega)
          have hmap_ne : s.scratch.work_stk1[lit.toNat / 2]? ≠ some 0xFFFFFFFF#32 := by
            intro heq
            rw [List.getElem?_eq_getElem
              (by omega : lit.toNat / 2 < s.scratch.work_stk1.length)] at heq
            have hneq_raw :
                (s.scratch.work_stk1[((arI[(src.toNat + 3 + i.toNat) % 2 ^ 64]'(by
                  rw [hidx_s]; exact hsi_lt)) >>> 1#32).toNat]'(by
                  simp only [hidx_s]; exact hlit_ws1)) ≠ 0xFFFFFFFF#32 := by
              c0_bound
            have hneq : (s.scratch.work_stk1[(lit >>> 1#32).toNat]'(by omega)) ≠
                0xFFFFFFFF#32 := by simpa only [hidx_s] using hneq_raw
            simp only [bv32_shr1_toNat] at hneq; exact hneq (Option.some.inj heq)
          rcases hbij.map_ok (lit.toNat / 2) (by omega) with
              hff | ⟨nv, hnv, _, _, hm_l, hi_l⟩
          · exact absurd hff hmap_ne
          · have hnv30 : nv < 2 ^ 30 := by omega
            have hnv_eq : (s.scratch.work_stk1[(lit >>> 1#32).toNat]'(by omega)) =
                BitVec.ofNat 32 nv := by
              rw [List.getElem?_eq_getElem
                (by omega : lit.toNat / 2 < s.scratch.work_stk1.length)] at hm_l
              simp only [bv32_shr1_toNat]; exact Option.some.inj hm_l
            have hpack := bv32_lit_pack hnv30 lit
            let lnew : BitVec 32 := (BitVec.ofNat 32 nv <<< 1#32) ||| (lit &&& 1#32)
            have hd_lt : dst.toNat + 3 + new_sz.toNat < arI.length := by omega
            have hns1_eq : (new_sz + (1 : BitVec 32)).toNat = new_sz.toNat + 1 :=
              bv32_add1 (by omega)
            have hi1_val : (i + (1 : BitVec 32)).toNat = i.toNat + 1 := bv32_add1 (by omega)
            let arI' := arI.set (dst.toNat + 3 + new_sz.toNat) lnew
            refine hLoopI (new_sz + (1 : BitVec 32), i + (1 : BitVec 32), ()) _
              (by dsimp only; rw [hi1_val]; omega)
              ⟨by rw [hi1_val]; omega, by rw [hns1_eq, hi1_val]; omega, arI',
               by simp [arI', harI], fun k hk hk_al => ?_, ?_, ?_⟩
            · dsimp only [arI']
              rw [List.getElem?_set_ne (by rw [hns1_eq] at hk; omega)]
              exact hpresI k
                (hk.elim Or.inl fun h2 => Or.inr (by rw [hns1_eq] at h2; omega)) hk_al
            · obtain ⟨hjl, hndK, hcovK, hsubK⟩ := hsatI
              have hkept' : ((arI'.drop (dst.toNat + 3)).take
                  (new_sz + (1 : BitVec 32)).toNat).map BitVec.toNat =
                  ((arI.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat ++
                    [lnew.toNat] := by
                rw [hns1_eq]
                have hlen_pre : ((arI'.drop (dst.toNat + 3)).take new_sz.toNat) =
                    (arI.drop (dst.toNat + 3)).take new_sz.toNat := by
                  refine List.ext_getElem (by simp [arI', harI]) fun j hj _ => ?_
                  simp only [List.length_take, List.length_drop, arI', List.length_set] at hj
                  rw [List.getElem_take, List.getElem_drop, List.getElem_take, List.getElem_drop]
                  apply Option.some.inj
                  rw [← List.getElem?_eq_getElem (by simp [arI', harI]; omega),
                    ← List.getElem?_eq_getElem (by omega : dst.toNat + 3 + j < arI.length)]
                  dsimp only [arI']; rw [List.getElem?_set_ne (by omega)]
                have hdt := drop_take_succ_cm (xs := arI') (off := dst.toNat + 3)
                  (n := new_sz.toNat) (by simp [arI', harI]; omega)
                rw [hdt, hlen_pre, List.map_append, List.map_singleton]
                congr 2; dsimp only [arI']; exact congrArg BitVec.toNat (List.getElem_set_self _)
              have hinv_new :
                  (inv[lnew.toNat / 2]?.getD 0#32).toNat = lit.toNat / 2 := by
                rw [hpack, show (2 * nv + lit.toNat % 2) / 2 = nv by omega,
                  hi_l, Option.getD_some, bv32_ofNat_toNat (by omega)]
              refine ⟨fun j hj => ?_, ?_, fun x hx => ?_, fun l hl => ?_⟩
              · rw [hns1_eq] at hj
                by_cases hjn : j = new_sz.toNat
                · subst hjn; dsimp only [arI']
                  rw [List.getElem?_set_self (by simp [harI]; omega), Option.getD_some, hpack]
                  omega
                · dsimp only [arI']
                  rw [List.getElem?_set_ne (by omega)]; exact hjl j (by omega)
              · rw [hkept']
                apply nodup_unmap_kept (fun x hx => (hcovK x hx).1) hndK (by rw [hpack]; omega)
                  hinv_new (fun hn1 hn2 heq => hbij.inv_inj hn1 hn2 heq)
                intro hmem_in
                rw [List.mem_map] at hmem_in
                obtain ⟨x, hx, hxe⟩ := hmem_in
                have hxo := (hcovK x hx).2
                rw [hxe] at hxo
                rw [List.mem_map] at hxo
                obtain ⟨y, hy, hye⟩ := hxo
                have hnd_take : ((olits.take (i.toNat + 1)).map (· / 2)).Nodup := by
                  refine List.Pairwise.sublist ?_ hol_nd
                  exact List.Sublist.map _ (List.take_sublist _ _)
                rw [htake_succ, List.map_append, List.map_singleton, List.nodup_append] at hnd_take
                exact hnd_take.2.2 _ (List.mem_map_of_mem hy) _ (List.mem_singleton.mpr rfl) hye
              · rw [hkept', List.mem_append, List.mem_singleton] at hx
                rcases hx with hx | rfl
                · obtain ⟨h1, h2⟩ := hcovK x hx
                  refine ⟨h1, ?_⟩
                  rw [hi1_val, htake_succ, List.map_append]; exact List.mem_append_left _ h2
                · refine ⟨by rw [hpack]; omega, ?_⟩
                  rw [hinv_new, hi1_val, htake_succ, List.map_append, List.map_singleton]
                  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
              · rw [hi1_val, htake_succ, List.mem_append, List.mem_singleton] at hl
                rcases hl with hl | rfl
                · rcases hsubK l hl with hin | hunit
                  · rw [hkept', List.map_append]; exact Or.inl (List.mem_append_left _ hin)
                  · exact Or.inr hunit
                · left; rw [hkept', List.map_append, List.map_singleton]
                  refine List.mem_append_right _ (List.mem_singleton.mpr ?_)
                  rw [hpack]
                  symm; apply compactUnmapLit_pair
                  rw [hi_l, Option.getD_some, bv32_ofNat_toNat (by omega)]
            · have hd_eq : (dst + (3 : BitVec 64) + new_sz.setWidth 64).toNat =
                  dst.toNat + 3 + new_sz.toNat := bv64_add3_zext_toNat (by omega)
              have hnv_zext :
                  (kL.scratch.work_stk1[(BitVec.setWidth 64
                    ((arI[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'(by
                      rw [hsi_eq]; exact hsi_lt)) >>> (1 : BitVec 32))).toNat]'(
                      hws1_bv64)) = BitVec.ofNat 32 nv := by
                apply Option.some.inj
                have hg := List.getElem?_eq_getElem hws1_bv64
                change some (kL.scratch.work_stk1[(BitVec.setWidth 64
                  ((arI[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'(by
                    rw [hsi_eq]; exact hsi_lt)) >>> 1#32)).toNat]'hws1_bv64) =
                  some (BitVec.ofNat 32 nv)
                rw [← hg, zext_toNat _ (by decide)]; simp only [hsi_eq]
                rw [bv32_shr1_toNat]; exact hm_l
              have har_rhs : arI' =
                  arI.set (dst + (3 : BitVec 64) + new_sz.setWidth 64).toNat
                    ((kL.scratch.work_stk1[(BitVec.setWidth 64
                      ((arI[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'(by
                        rw [hsi_eq]; exact hsi_lt)) >>> (1 : BitVec 32))).toNat]'(
                        hws1_bv64) <<< (1 : BitVec 32)) |||
                      ((arI[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'(by
                        rw [hsi_eq]; exact hsi_lt)) &&& (1 : BitVec 32))) := by
                dsimp only [arI', lnew]; rw [hd_eq, hnv_zext]; simp only [hsi_eq]; rfl
              rw [har_rhs]; exact (by assumption)
        · have hidx_s : (src.toNat + 3 + i.toNat) % 2 ^ 64 = src.toNat + 3 + i.toNat :=
            Nat.mod_eq_of_lt (by omega)
          have hlv_dom := hdom lit.toNat hlit_lt_cv
          have hlv_ff : s.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8 := by
            have hne0_raw :
                (s.core.vals[(arI[(src.toNat + 3 + i.toNat) % 2 ^ 64]'(by
                  rw [hidx_s]; exact hsi_lt)).toNat]'(by
                  simp only [hidx_s]; exact hlit_vals)).signExtend 32 ≠ 0#32 := by c0_bound
            have hng0_raw :
                ((0#32).slt ((kCore.vals[(arI[(src.toNat + 3 + i.toNat) % 2 ^ 64]'(by
                  rw [hidx_s]; exact hsi_lt)).toNat]'(by
                  simp only [hidx_s]; exact hlit_vals)).signExtend 32)) = false := by c0_bound
            have hne0 : (s.core.vals[lit.toNat]'(by omega)).signExtend 32 ≠ 0#32 := by
              simpa only [hidx_s] using hne0_raw
            have hng0 :
                ((0#32).slt ((s.core.vals[lit.toNat]'(by omega)).signExtend 32)) = false := by
              simpa only [hidx_s] using hng0_raw
            rw [List.getElem?_eq_getElem (by omega : lit.toNat < s.core.vals.length),
              Option.getD_some] at hlv_dom ⊢
            rcases hlv_dom with h0 | h1 | hff
            · exact absurd (by simp [h0]) hne0
            · exact absurd hng0 (by simp [h1])
            · exact hff
          have hent_neg : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat ^^^ 1]) :=
            hfent lit.toNat hlit_lt_cv hlv_ff
          cm_steps
          have hi1_val : (i + (1 : BitVec 32)).toNat = i.toNat + 1 := bv32_add1 (by omega)
          refine hLoopI (new_sz, i + (1 : BitVec 32), ()) mI
            (by dsimp only; rw [hi1_val]; omega)
            ⟨by rw [hi1_val]; omega, by rw [hi1_val]; omega, arI, harI, hpresI, ?_, hmI⟩
          obtain ⟨hjl, hndK, hcovK, hsubK⟩ := hsatI
          rw [hi1_val, htake_succ]
          refine ⟨hjl, hndK, fun x hx => ?_, fun l hl => ?_⟩
          · obtain ⟨h1, h2⟩ := hcovK x hx
            refine ⟨h1, ?_⟩
            rw [List.map_append]; exact List.mem_append_left _ h2
          · rw [List.mem_append, List.mem_singleton] at hl
            rcases hl with hl | rfl
            · exact hsubK l hl
            · exact Or.inr ⟨hlit_lt_cv, hent_neg⟩
      · exfalso
        have hidx : (src.toNat + 3 + i.toNat) % 2 ^ 64 = src.toNat + 3 + i.toNat :=
          Nat.mod_eq_of_lt (by omega)
        have hge_n : nlits.toNat ≤ (arI[(src.toNat + 3 + i.toNat) % 2 ^ 64]'(by
            rw [hidx]; exact hsi_lt)).toNat := by c0_bound
        simp only [hidx] at hge_n
        change nlits.toNat ≤ lit.toNat at hge_n
        rw [hnlits] at hge_n; omega
    · have hi_eq : i.toNat = old_sz.toNat := by c0_bound
      cm_steps
      refine hJi (false, new_sz, i, ()) mI ⟨hi_eq ▸ hns_le, arI, harI, hpresI, fun _ => ?_, hmI⟩
      obtain ⟨hjl, hndK, _, hsubK⟩ := hsatI
      have htake_all : olits.take i.toNat = olits := by
        rw [hi_eq, ← hol_len]; exact List.take_length
      rw [htake_all] at hsubK
      refine ⟨hjl, hndK,
        compactArena_entails_kept (old_cv := old_cv.toNat) hent_ol fun l hl => ?_⟩
      rcases hsubK l hl with hin | hunit
      · exact Or.inl hin
      · exact Or.inr hunit

private theorem full_compact_flush_loop {Γ : Env} {Q : Post [i64]} {X : XPost}
    (hprop : ∀ a m Q X, fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hsweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {s s0 : FullState} {R : Mem 64 → Prop} {m0 : Mem 64}
    (hsp0 : FullSparseInv c F0 s0) (hcl0 : s0.core.cur_level = 0)
    (hinc0' : s0.core.inconsistent = 0#64) (hcv0 : s0.core.cur_vars = s.core.cur_vars)
    (hfuel0 : s0.core.fuel = s.core.fuel) (hm0 : (FullMem c s0 ⋆ R) m0)
    (hQ : ∀ (res : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullSparseInv c F0 s' → (res = 0#64 ∨ res = 1#64 ∨ res = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (res = 20#64 → F0.Unsat) →
      (res = 1#64 → s'.core.cur_level = 0 ∧ s'.core.propagated = s'.core.trail_end ∧
        s'.core.oom = 0#64 ∧ s'.core.unflushed = 0#64 ∧ s'.core.inconsistent = 0#64) →
      (FullMem c s' ⋆ R) m' → Q (res, ()) m') :
    wp Γ Q X (flushLoopExpr Val Cont c.hdr) m0 := by
  unfold flushLoopExpr
  let rd (off : Nat) (mem : Mem 64) : Nat :=
    match loadVal mem i64 (c.hdr + BitVec.ofNat 64 off) with
    | some v => v.toNat | none => 0
  let meas (_ : Unit) (mem : Mem 64) : Nat :=
    2 * rd 168 mem + (if rd 152 mem = rd 144 mem then 1 else 0)
  have hmeas_eq : ∀ sM mM, FullState.LengthsOk c sM → (FullMem c sM ⋆ R) mM →
      meas () mM = 2 * sM.core.fuel.toNat +
        (if sM.core.propagated = sM.core.trail_end then 1 else 0) := by
    intro sM mM hlenM hmM
    have hf := load_full_fuel hmM
    have hp := load_full_propagated hmM
    have ht := load_full_trail_end hmM
    have hp_lt : sM.core.propagated < 2 ^ 64 := by
      have := hlenM.core_ok.propagated_le; have := hlenM.core_ok.trail_end_le
      have := hlenM.core_ok.cur_vars_le; have := c.hmaxv; unfold dimacsBound at *; omega
    have ht_lt : sM.core.trail_end < 2 ^ 64 := by
      have := hlenM.core_ok.trail_end_le; have := hlenM.core_ok.cur_vars_le
      have := c.hmaxv; unfold dimacsBound at *; omega
    dsimp only [meas, rd]
    simp only [show c.hdr + BitVec.ofNat 64 168 = c.hdr + 168 from rfl,
      show c.hdr + BitVec.ofNat 64 152 = c.hdr + 152 from rfl,
      show c.hdr + BitVec.ofNat 64 144 = c.hdr + 144 from rfl, hf, hp, ht,
      bv64_ofNat_toNat hp_lt, bv64_ofNat_toNat ht_lt]
  refine wp_join_group (ts := [])
    (fun () m1 =>
      ∃ s1 : FullState, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
        s1.core.inconsistent = 0#64 ∧ s1.core.cur_vars = s.core.cur_vars ∧
        s1.core.propagated = s1.core.trail_end ∧ s1.core.oom = 0#64 ∧
        s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1)
    ?_ ?_
  · rintro _ ⟨⟩ m1 ⟨s1, hsp1, hcl1, hinc1, hcv1, hpe1, hoom1, hfuel1, hm1⟩
    clear hsp0 hcl0 hinc0' hcv0 hfuel0 hm0
    cm_steps
    let s1' : FullState := { s1 with core := { s1.core with unflushed := 0#64 } }
    obtain ⟨Fc1, hw1⟩ := hsp1.1.witness
    have hlen1' : FullState.LengthsOk c s1' :=
      ⟨{ hsp1.1.lengths.core_ok with }, hsp1.1.lengths.scratch_ok⟩
    have hw1' : FullWitnessInv c F0 Fc1 s1'.core :=
      { hw1 with
        arena := { hw1.arena with len_ok := hw1.arena.len_ok }
        watches := hw1.watches.with_wstk rfl rfl rfl rfl rfl fun _ h => h }
    have hsp1' : FullSparseInv c F0 s1' :=
      ⟨⟨hlen1', Fc1, hw1'⟩, hsp1.2.1, hsp1.2.2.1,
       FullExtScratchOk.of_pres hsp1.2.2.2.1 ⟨rfl, rfl⟩ (fun _ h => h), hsp1.2.2.2.2⟩
    exact hQ 1#64 s1' _ hsp1' (Or.inr (Or.inl rfl)) hcv1 hfuel1 (fun h => absurd h (by decide))
      (fun _ => ⟨hcl1, hpe1, hoom1, rfl, hinc1⟩) (by assumption)
  intro Js hJs
  refine wp_loop_inv
    (fun () mL =>
      ∃ sL : FullState, FullSparseInv c F0 sL ∧ sL.core.cur_level = 0 ∧
        sL.core.inconsistent = 0#64 ∧ sL.core.cur_vars = s.core.cur_vars ∧
        sL.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sL ⋆ R) mL)
    meas
    (fun J hLoop => ?_) ?_
  · cm_steps
    exact hLoop () m0 ⟨s0, hsp0, hcl0, hinc0', hcv0,
      Nat.le_of_eq (congrArg BitVec.toNat hfuel0), hm0⟩
  · rintro J ⟨⟩ mL ⟨sL, hspL, hclL, hincL, hcvL, hfuelL, hmL⟩ hLoop
    clear hsp0 hcl0 hinc0' hcv0 hfuel0 hm0
    have hmeasL := hmeas_eq sL mL hspL.1.lengths hmL
    obtain ⟨FcL, hwL⟩ := hspL.1.witness
    have hcv_leL := hspL.1.lengths.core_ok.cur_vars_le
    have hprop_leL := hspL.1.lengths.core_ok.propagated_le
    have hmL_marks := hspL.2.1
    have hndL := hspL.2.2.1
    have hextL := hspL.2.2.2.1
    have hdmL := hspL.2.2.2.2
    cm_split
    rotate_left
    · simp only [Bool.true_eq_false] at *
    cm_split
    · cm_steps
      exact hQ 0#64 sL mL hspL (Or.inl rfl) hcvL hfuelL (fun h => absurd h (by decide))
        (fun h => absurd h (by decide)) hmL
    · cm_split
      · cm_steps
        exact hQ 0#64 sL mL hspL (Or.inl rfl) hcvL hfuelL (fun h => absurd h (by decide))
          (fun h => absurd h (by decide)) hmL
      · have hoomL0 : sL.core.oom = 0#64 := by c0_bound
        have hfuel_ne : sL.core.fuel ≠ 0#64 := by c0_bound
        have hfuel_pos : 0 < sL.core.fuel.toNat :=
          Nat.pos_of_ne_zero fun h0 => hfuel_ne (BitVec.eq_of_toNat_eq h0)
        cm_steps; c0_call hprop
        refine ⟨c, F0, FcL, sL, R, rfl, hspL.1.lengths, hwL, hdmL, hmL,
          fun pr valsP flagsP lvlP rsnsP trlP tpP teP propP unassP unflP wvecP arenaP wstkP
            wlenP wuP fuelP ctypeP crefP c0P c1P oomP ticksP wsortP phasesP mP
            hlenP hwP _ hpa hfuel_leP hpr hp0 hp1 _ hpeq hmP => ?_⟩
        clear hmL hspL
        have hfuelP : fuelP.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfuel_leP hfuelL
        let sP : FullState :=
          { sL with
            core := { sL.core with vals := valsP, flags := flagsP, lvl := lvlP, rsns := rsnsP,
                                   trl := trlP, trail_pos := tpP, trail_end := teP,
                                   propagated := propP, unassigned := unassP,
                                   unflushed := unflP, wvec := wvecP, arena := arenaP,
                                   wstk := wstkP, wlen := wlenP, wusable := wuP, fuel := fuelP,
                                   confl_type := ctypeP, confl_ref := crefP, confl_lit0 := c0P,
                                   confl_lit1 := c1P, oom := oomP }
            scratch := { sL.scratch with search_ticks := ticksP, wsort := wsortP,
                                         phases := phasesP } }
        have hndP : FullArenaVarsNodup sP := fullArenaVarsNodup_of_permEq hndL hpa
        have hextP : FullExtScratchOk c sP :=
          FullExtScratchOk.of_pres hextL ⟨rfl, rfl⟩ fun r hr => by
            unfold fullArenaClauseRefs at *; exact hpa.2.1.symm ▸ hr
        have hspP : FullSparseInv c F0 sP :=
          ⟨⟨hlenP, FcL, hwP⟩, hmL_marks, hndP, hextP, hdmL⟩
        cm_split
        · obtain ⟨_, _, hconfl⟩ := hp1 (by c0_bound)
          have hunsat : F0.Unsat := level0_conflict_unsat hwP hclL hconfl
          cm_steps
          exact hQ 20#64 sP mP hspP (Or.inr (Or.inr rfl)) hcvL hfuelP (fun _ => hunsat)
            (fun h => absurd h (by decide)) hmP
        · have hne1 : pr ≠ 1#64 := by c0_bound
          have hpr_02 : pr = 0#64 ∨ pr = 2#64 := by
            rcases hpr with rfl | rfl | rfl
            · exact Or.inl rfl
            · exact absurd rfl hne1
            · exact Or.inr rfl
          cm_split
          · cm_steps
            exact hQ 0#64 sP mP hspP (Or.inl rfl) hcvL hfuelP (fun h => absurd h (by decide))
              (fun h => absurd h (by decide)) hmP
          · have hne2 : pr ≠ 2#64 := by c0_bound
            obtain rfl : pr = 0#64 := by
              rcases hpr_02 with rfl | rfl
              · rfl
              · exact absurd rfl hne2
            obtain ⟨hprop_eq, hoom_fn, hfuel_lt⟩ := hp0 rfl
            have hoomP : oomP = 0#64 := hoom_fn hoomL0
            cm_split; try (apply False.elim; apply absurd hoomP; c0_bound)
            cm_split
            · cm_steps
              exact hQ 0#64 sP mP hspP (Or.inl rfl) hcvL hfuelP (fun h => absurd h (by decide))
                (fun h => absurd h (by decide)) hmP
            · have hfuelP_nz : fuelP ≠ 0#64 := by c0_bound
              have hpP_lt : propP < 2 ^ 64 := by
                have h1 : propP ≤ teP := hlenP.core_ok.propagated_le
                have h2 : teP ≤ sL.core.cur_vars := hlenP.core_ok.trail_end_le
                have h3 := c.hmaxv; unfold dimacsBound at h3; omega
              have hextP2 := hextP.2
              cm_steps; c0_call hsweep
              refine ⟨c, F0, FcL, sP, R, rfl, hlenP, hwP, hndP, hdmL,
                fun h => False.elim (by
                  rw [show sP.core.cur_level = sL.core.cur_level from rfl, hclL] at h
                  exact Nat.lt_irrefl 0 h),
                hmP,
                fun sr valsA flagsA lvlA rsnsA trlA tpA teA unassA unflA wvecA wstkA
                  arenaA alenA wlenA wuA fredA niA nrA nbA oomA scA mA
                  hlenA hsr hex_len _ hllA hwA hndA hsr01 _ hsr1 hsr2 _ hmA => ?_⟩
              clear hmP hspP hndP hextP hwP hlenP
              let sA : FullState :=
                { sP with
                  core := { sP.core with vals := valsA, flags := flagsA, lvl := lvlA,
                                         rsns := rsnsA, trl := trlA, trail_pos := tpA,
                                         trail_end := teA, unassigned := unassA,
                                         unflushed := unflA, wvec := wvecA, wstk := wstkA,
                                         arena := arenaA, arena_len := alenA, wlen := wlenA,
                                         wusable := wuA, arena_garbage := 0#64,
                                         first_reducible := fredA, num_irred := niA,
                                         num_redundant := nrA, num_binary := nbA,
                                         oom := oomA }
                  scratch := scA }
              have hextA : FullExtScratchOk c sA := ⟨hllA, hex_len ▸ hextP2⟩
              have hspA : FullSparseInv c F0 sA :=
                ⟨⟨hlenA, FcL, hwA⟩, hmL_marks, hndA, hextA, hdmL⟩
              cm_split
              · have hunsat : F0.Unsat := (hsr2 (by c0_bound)).2
                cm_steps
                exact hQ 20#64 sA mA hspA (Or.inr (Or.inr rfl)) hcvL hfuelP (fun _ => hunsat)
                  (fun h => absurd h (by decide)) hmA
              · have hne2 : sr ≠ 2#64 := by c0_bound
                cm_split
                · cm_steps
                  exact hQ 0#64 sA mA hspA (Or.inl rfl) hcvL hfuelP (fun h => absurd h (by decide))
                    (fun h => absurd h (by decide)) hmA
                · cm_split <;> first
                    | (cm_steps
                       exact hQ 0#64 sA mA hspA (Or.inl rfl) hcvL hfuelP
                         (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hmA)
                    | skip
                  · have hne3 : sr ≠ 3#64 := by c0_bound
                    have hsr_01 : sr = 0#64 ∨ sr = 1#64 := by
                      rcases hsr with rfl | rfl | rfl | rfl
                      · exact Or.inl rfl
                      · exact Or.inr rfl
                      · exact absurd rfl hne2
                      · exact absurd rfl hne3
                    have hoomA0 : oomA = 0#64 := hsr01 hsr_01
                    have htA_lt : teA < 2 ^ 64 := by
                      have h1 : teA ≤ sL.core.cur_vars := hlenA.core_ok.trail_end_le
                      have h3 := c.hmaxv; unfold dimacsBound at h3; omega
                    have hdec_of : sr = 1#64 ∨ propP < teA → meas () mA < meas () mL := by
                      intro hor
                      have hmeasA := hmeas_eq sA mA hlenA hmA
                      rw [hmeasA, hmeasL]
                      by_cases hpe : sL.core.propagated = sL.core.trail_end
                      · obtain ⟨_, hsP_eq⟩ := hpeq hpe
                        have hsP_core : sP.core = sL.core := congrArg FullState.core hsP_eq
                        have hfa : sA.core.fuel = sL.core.fuel := by
                          change sP.core.fuel = sL.core.fuel; rw [hsP_core]
                        have hlt_te : propP < teA := by
                          rcases hor with rfl | hlt
                          · have h1 : sP.core.trail_end < teA := (hsr1 rfl).2
                            have hte_eq : teP = sP.core.trail_end := rfl
                            omega
                          · exact hlt
                        rw [ite_eq_left hpe, ite_eq_right (by change propP ≠ teA; omega), hfa]
                        omega
                      · have hlt_p : sL.core.propagated < sL.core.trail_end :=
                          Nat.lt_of_le_of_ne hprop_leL hpe
                        have hfl := hfuel_lt hlt_p
                        rw [ite_eq_right hpe]
                        change 2 * fuelP.toNat + _ < 2 * sL.core.fuel.toNat + 0
                        split <;> omega
                    cm_split
                    · cm_split
                      · have hge_te : propP ≥ teA := by
                          have h1 : teA ≤ propP := by
                            simpa [sP, Nat.mod_eq_of_lt htA_lt,
                              Nat.mod_eq_of_lt hpP_lt] using hc
                          omega
                        have hprop_eqA : propP = teA :=
                          Nat.le_antisymm hlenA.core_ok.propagated_le hge_te
                        cm_steps
                        exact hJs () mA ⟨sA, hspA, hclL, hincL, hcvL, hprop_eqA, hoomA0, hfuelP,
                          hmA⟩
                      · have hlt_te : propP < teA := by
                          have h1 : ¬ teA ≤ propP := by
                            simpa [sP, Nat.mod_eq_of_lt htA_lt,
                              Nat.mod_eq_of_lt hpP_lt] using hc
                          omega
                        cm_steps
                        exact hLoop () mA (hdec_of (Or.inr hlt_te))
                          ⟨sA, hspA, hclL, hincL, hcvL, hfuelP, hmA⟩
                    · have hsr1_eq : sr = 1#64 := by
                        have hne0 : sr ≠ 0#64 := by c0_bound
                        rcases hsr_01 with rfl | rfl
                        · exact absurd rfl hne0
                        · rfl
                      cm_steps
                      exact hLoop () mA (hdec_of (Or.inl hsr1_eq))
                        ⟨sA, hspA, hclL, hincL, hcvL, hfuelP, hmA⟩

theorem full_compact_arena_wp (Γ : Env)
    (hnext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hpush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullCompactArenaSpec a m Q X → Func.wp Γ full_compact_arena_body a m Q X := by
  rintro ⟨h, old_cv, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, ncv, s, R, rfl, hlen, hext_s, har_inv, hnd, hdm, hcl0, hold, hncv_le,
     hbij, hdom, hfent, hbin0, hm, hQ⟩
  have hck0 := hlen.core_ok
  have hcv_le := hck0.cur_vars_le
  have har_len := hck0.arena_len_arr
  have hal_le := hck0.arena_len_le
  have hv_len := hck0.vals_len
  have hws1_len := hlen.scratch_ok.work_stk1_len
  have hll_len := hlen.scratch_ok.last_learned_len
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have har_cap_lt : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hal_lt64 : s.core.arena_len < 2 ^ 64 := by omega
  have hnlits_eq : (old_cv <<< (1 : Nat)).toNat = 2 * old_cv.toNat := bv64_shl1_toNat (by omega)
  let inv := s.scratch.work_stk2
  have hsrc0 : s.core.arena_len = 0 ∨ 0 ∈ fullArenaClauseRefsCore s.core := by
    rcases har_inv.len_ok with hz | h3
    · exact Or.inl hz
    · right; unfold fullArenaClauseRefsCore
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s.core.arena_len ≠ 0)
      have hf : fullArenaScanRefs s.core.arena s.core.arena_len 0 s.core.arena_len =
          fullArenaScanRefs s.core.arena s.core.arena_len 0 k.succ :=
        congrArg (fullArenaScanRefs s.core.arena s.core.arena_len 0) hk
      rw [hf]; unfold fullArenaScanRefs; simp [h3]
  cm_to_group
  refine wp_join_group (ts := [i64, i64, i64, i64, i64, i64])
    (fun (_src, dst, fred, irred, redd, status, ()) mE =>
      dst.toNat ≤ s.core.arena_len ∧ (status = 0#64 ∨ status = 2#64 ∨ status = 3#64) ∧
      (status = 2#64 → F0.Unsat) ∧
      ∃ (arE wvecE wstkE : List (BitVec 32)) (wlenE : Nat) (wuE nbE oomE : BitVec 64)
        (wsE : List (BitVec 32)),
        let kE : FullCoreState :=
          { s.core with arena := arE, wvec := wvecE, wstk := wstkE, wlen := wlenE,
                        wusable := wuE, num_binary := nbE, oom := oomE }
        FullCoreState.LengthsOk c kE ∧ wsE.length = 2 * c.max_vars ∧
        (status = 3#64 → oomE = 1#64) ∧
        CompactArenaPrefix c ncv inv F_cur arE dst.toNat ∧
        CompactUnmapBinsOk ncv inv F_cur kE ∧
        (FullMem c { s with core := kE, scratch := { s.scratch with wsort := wsE } } ⋆ R) mE)
    ?_ ?_
  · rintro _ ⟨_src, dst, fred, irred, redd, status, ⟨⟩⟩ mE
      ⟨hd_le, hst_ok, hst2, arE, wvecE, wstkE, wlenE, wuE, nbE, oomE, wsE,
       hckE, hwsE_len, hst3, hpreE, hbinE, hmE⟩
    clear hm hbin0
    cm_steps
    refine wp_loop_inv
      (fun (li, ()) mLi =>
        li.toNat ≤ 16 ∧ ∃ llL : List (BitVec 32), llL.length = 16 ∧
          (∀ j < li.toNat, llL[j]? = some 0xFFFFFFFF#32) ∧
          (FullMem c {
            core := { s.core with arena := arE, arena_len := dst.toNat, arena_garbage := 0#64,
                                  first_reducible := fred, num_irred := irred,
                                  num_redundant := redd, wvec := wvecE, wstk := wstkE,
                                  wlen := wlenE, wusable := wuE, num_binary := nbE, oom := oomE }
            scratch := { s.scratch with wsort := wsE, last_learned := llL } } ⋆ R) mLi)
      (fun (li, ()) _ => 16 - li.toNat)
      (fun Jli hLoopLi => ?_) ?_
    · cm_steps
      exact hLoopLi (0#64, ()) _ ⟨Nat.zero_le _, s.scratch.last_learned, hll_len,
        fun _ h => by simp at h, by assumption⟩
    · rintro Jli ⟨li, ⟨⟩⟩ mLi ⟨hli_le, llL, hllL, hallL, hmLi⟩ hLoopLi
      cm_split
      · have hli_lt : li.toNat < 16 := by c0_bound
        have hli1_eq : (li + (1 : BitVec 64)).toNat = li.toNat + 1 := bv64_add1 (by omega)
        cm_steps
        refine hLoopLi (li + (1 : BitVec 64), ()) _ (by dsimp only; rw [hli1_eq]; omega)
          ⟨by rw [hli1_eq]; omega, llL.set li.toNat 0xFFFFFFFF#32, by simp [hllL], fun j hj => ?_,
           by assumption⟩
        rw [hli1_eq] at hj
        by_cases hje : j = li.toNat
        · subst hje; exact List.getElem?_set_self (by omega)
        · rw [List.getElem?_set_ne (Ne.symm hje)]; exact hallL j (by omega)
      · have hli_16 : li.toNat = 16 := by c0_bound
        rw [hli_16] at hallL
        let sF : FullState :=
          { core := { s.core with arena := arE, arena_len := dst.toNat, arena_garbage := 0#64,
                                  first_reducible := fred, num_irred := irred,
                                  num_redundant := redd, wvec := wvecE, wstk := wstkE,
                                  wlen := wlenE, wusable := wuE, num_binary := nbE, oom := oomE }
            scratch := { s.scratch with last_learned := llL, wsort := wsE } }
        have hckF : FullState.LengthsOk c sF :=
          ⟨{ hckE with arena_len_le := by change dst.toNat ≤ c.arena_cap; omega },
           { hlen.scratch_ok with last_learned_len := hllL, wsort_len := hwsE_len }⟩
        have harF : CompactArenaOk c ncv inv F_cur sF.core :=
          compactArenaPrefix_to_ok (k := sF.core) hpreE hckE.arena_len_arr
        have hbinF : CompactUnmapBinsOk ncv inv F_cur sF.core :=
          ⟨⟨fun l hl => hbinE.layout.bounds l hl,
            fun l hl hp => hbinE.layout.pos_off l hl hp,
            fun l1 l2 h1 h2 hn p1 p2 => hbinE.layout.disjoint l1 l2 h1 h2 hn p1 p2,
            fun l hl idx hi => hbinE.layout.no_sentinel l hl idx hi⟩,
            hbinE.empty_hi, fun l hl => by
              have hs0 := hbinE.slices l hl
              unfold fullWatchOffCore fullWatchSizeCore at hs0 ⊢
              exact hs0.relocate (fun _ _ => by rfl)⟩
        have hllF : FullLastLearnedWf sF :=
          fullLastLearnedWf_of_cleared fun j hj => by rw [hallL j (by omega), Option.getD_some]
        cm_steps
        exact hQ status arE dst.toNat fred irred redd wvecE wstkE wlenE wuE nbE oomE llL wsE mLi
          hckF hst_ok hst2 hst3 hbinF harF hllF hmLi
  · intro J1 hJ1
    cm_steps
    refine wp_loop_inv
      (fun (src, dst, fred, irred, redd, ()) mL =>
        dst.toNat ≤ src.toNat ∧ src.toNat ≤ s.core.arena_len ∧
        (src.toNat = s.core.arena_len ∨ src.toNat ∈ fullArenaClauseRefsCore s.core) ∧
        ∃ (arL wvecL wstkL : List (BitVec 32)) (wlenL : Nat) (wuL nbL oomL : BitVec 64)
          (wsL : List (BitVec 32)),
          let kL : FullCoreState :=
            { s.core with arena := arL, wvec := wvecL, wstk := wstkL, wlen := wlenL,
                          wusable := wuL, num_binary := nbL, oom := oomL }
          FullCoreState.LengthsOk c kL ∧ wsL.length = 2 * c.max_vars ∧
          (∀ j, src.toNat ≤ j → j < s.core.arena_len → arL[j]? = s.core.arena[j]?) ∧
          CompactArenaPrefix c ncv inv F_cur arL dst.toNat ∧
          CompactUnmapBinsOk ncv inv F_cur kL ∧
          (FullMem c { s with core := kL, scratch := { s.scratch with wsort := wsL } } ⋆ R) mL)
      (fun (src, _, _, _, _, ()) _ => s.core.arena_len - src.toNat)
      (fun Jl hLoopL => ?_) ?_
    · cm_steps
      exact hLoopL (0#64, 0#64, 0xFFFFFFFF#64, 0#64, 0#64, ()) m
        ⟨Nat.zero_le _, Nat.zero_le _,
         (by rcases hsrc0 with hz | hr; exact Or.inl hz.symm; exact Or.inr hr),
         s.core.arena, s.core.wvec, s.core.wstk, s.core.wlen, s.core.wusable,
         s.core.num_binary, s.core.oom, s.scratch.wsort, hck0, hlen.scratch_ok.wsort_len,
         fun _ _ _ => rfl, compactArenaPrefix_zero, hbin0, hm⟩
    · rintro Jl ⟨src, dst, fred, irred, redd, ⟨⟩⟩ mL
        ⟨hd_le, hsrc_le, hsrc_ok, arL, wvecL, wstkL, wlenL, wuL, nbL, oomL, wsL,
         hckL, hwsL_len, har_tail, hpreL, hbinL, hmL⟩ hLoopL
      let kL : FullCoreState :=
        { s.core with arena := arL, wvec := wvecL, wstk := wstkL, wlen := wlenL,
                      wusable := wuL, num_binary := nbL, oom := oomL }
      let sL : FullState := { s with core := kL, scratch := { s.scratch with wsort := wsL } }
      cm_split
      · have hsrc_lt : src.toNat < s.core.arena_len := by c0_bound
        have hsrc_ref : src.toNat ∈ fullArenaClauseRefsCore s.core := by
          rcases hsrc_ok with h | h
          · omega
          · exact h
        have hwf := har_inv.refs_wf src.toNat hsrc_ref
        cm_split
        · have hsrc3_le : src.toNat + 3 ≤ s.core.arena_len := by c0_bound
          have hsrc2_eq : (src + (2 : BitVec 64)).toNat = src.toNat + 2 := bv64_add2 (by omega)
          have har_eq_len : arL.length = c.arena_cap := hckL.arena_len_arr
          have hsrc_lt_arL : src.toNat < arL.length := by omega
          have hsrc2_lt_arL : src.toNat + 2 < arL.length := by omega
          have har_s0 : arL[src.toNat]? = s.core.arena[src.toNat]? :=
            har_tail src.toNat (Nat.le_refl _) hsrc_lt
          have har_s2 : arL[src.toNat + 2]? = s.core.arena[src.toNat + 2]? :=
            har_tail (src.toNat + 2) (by omega) (by omega)
          let hdr := s.core.arena[src.toNat]'(by rw [har_len]; omega)
          let old_sz := s.core.arena[src.toNat + 2]'(by rw [har_len]; omega)
          have hhdr_arL : arL[src.toNat]'hsrc_lt_arL = hdr := by
            apply Option.some.inj
            rw [← List.getElem?_eq_getElem hsrc_lt_arL, har_s0, List.getElem?_eq_getElem]
          have hosz_arL : arL[src.toNat + 2]'hsrc2_lt_arL = old_sz := by
            apply Option.some.inj
            rw [← List.getElem?_eq_getElem hsrc2_lt_arL, har_s2, List.getElem?_eq_getElem]
          have har_src2 :
              ∀ h' : (src + (2 : BitVec 64)).toNat < arL.length,
                arL[(src + (2 : BitVec 64)).toNat]'h' = old_sz := fun h' => by
            simp only [hsrc2_eq]; exact hosz_arL
          have hsrc32_eq : (src.setWidth 32).toNat = src.toNat := by
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
          have har_s0_def : s.core.arena[src.toNat]?.getD 0#32 = hdr := by
            rw [List.getElem?_eq_getElem (by rw [har_len]; omega), Option.getD_some]
          have hnxt_eq : fullArenaNextOff arL s.core.arena_len src.toNat =
              fullArenaNextOff s.core.arena s.core.arena_len src.toNat :=
            fullArenaNextOff_congr_block har_s0 har_s2 fun k hk1 hk2 =>
              har_tail k (by omega) (by have := hwf.2.2.2.1; omega)
          have hosz_eq : fullArenaClauseSizeCore s.core src.toNat = old_sz.toNat := by
            unfold fullArenaClauseSizeCore
            rw [List.getElem?_eq_getElem (by rw [har_len]; omega), Option.getD_some]
          let nsrc_nat := fullArenaNextOff s.core.arena s.core.arena_len src.toNat
          have hnsrc_bounds : src.toNat + 3 + old_sz.toNat ≤ nsrc_nat ∧
              nsrc_nat ≤ s.core.arena_len ∧
              (nsrc_nat = s.core.arena_len ∨ nsrc_nat + 3 ≤ s.core.arena_len) :=
            ⟨hosz_eq ▸ hwf.2.2.1, hwf.2.2.2.1, hwf.2.2.2.2⟩
          have hnsrc64 : (BitVec.ofNat 32 nsrc_nat).setWidth 64 = BitVec.ofNat 64 nsrc_nat := by
            apply BitVec.eq_of_toNat_eq
            rw [zext_toNat _ (by decide), bv32_ofNat_toNat (by omega),
              BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have hnsrc_to : (BitVec.ofNat 64 nsrc_nat).toNat = nsrc_nat := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have hnsrc_mem : nsrc_nat = s.core.arena_len ∨
              nsrc_nat ∈ fullArenaClauseRefsCore s.core := by
            rcases hwf.2.2.2.2 with heq | h3
            · exact Or.inl heq
            · exact Or.inr (fullArenaNextOff_mem_of_mem hsrc_ref h3)
          cm_steps; c0_call hnext
          refine ⟨c, sL, R, rfl, ⟨hckL, { hlen.scratch_ok with wsort_len := hwsL_len }⟩, hmL, ?_⟩
          rw [hsrc32_eq, hnxt_eq, hhdr_arL, har_src2]
          cm_split
          · cm_steps
            exact hLoopL (BitVec.ofNat 32 nsrc_nat |>.setWidth 64, dst, fred, irred, redd, ()) mL
              (by dsimp only; rw [hnsrc64, hnsrc_to]; omega)
              ⟨by rw [hnsrc64, hnsrc_to]; omega, by rw [hnsrc64, hnsrc_to]; omega,
               by rw [hnsrc64, hnsrc_to]; exact hnsrc_mem,
               arL, wvecL, wstkL, wlenL, wuL, nbL, oomL, wsL, hckL, hwsL_len,
               by rw [hnsrc64, hnsrc_to]; exact fun j hj1 hj2 => har_tail j (by omega) hj2,
               hpreL, hbinL, hmL⟩
          · have hng : (hdr &&& 0x00080000#32) = 0#32 := by c0_bound
            have hgarb_f : fullArenaClauseGarbCore s.core src.toNat = false := by
              unfold fullArenaClauseGarbCore fullArenaHdrCore
              rw [har_s0_def, hng]; rfl
            cm_split <;> first
              | (exfalso; have h2 : old_sz.toNat < 3 := by c0_bound
                 have hsz3 : 3 ≤ old_sz.toNat := hosz_eq ▸ hwf.2.1; omega)
              | skip
            cm_split <;> first
              | (exfalso
                 have h3 :
                     s.core.arena_len < (src + (3 : BitVec 64) + old_sz.setWidth 64).toNat := by
                   c0_bound
                 have hfit_src : src.toNat + 3 + old_sz.toNat ≤ s.core.arena_len := by
                   have := hosz_eq ▸ hwf.2.2.1; omega
                 have hfit_64 : src.toNat + 3 + old_sz.toNat < 2 ^ 64 := by
                   unfold dimacsBound at har_cap_lt; omega
                 rw [bv64_add3_zext_toNat hfit_64] at h3; omega)
              | skip
            have hsz3 : 3 ≤ old_sz.toNat := hosz_eq ▸ hwf.2.1
            have hfit_src : src.toNat + 3 + old_sz.toNat ≤ s.core.arena_len := by
              have := hosz_eq ▸ hwf.2.2.1; omega
            have hfit_64 : src.toNat + 3 + old_sz.toNat < 2 ^ 64 := by
              unfold dimacsBound at har_cap_lt; omega
            let olits := fullArenaClauseLitsCore s.core src.toNat
            have hol_len : olits.length = old_sz.toNat := by
              unfold olits fullArenaClauseLitsCore
              rw [List.length_map, List.length_take, List.length_drop, har_len, hosz_eq]
              have : src.toNat + 3 + old_sz.toNat ≤ c.arena_cap :=
                Nat.le_trans hfit_src hal_le
              exact Nat.min_eq_left (by omega)
            have hol_mem : ∀ j < old_sz.toNat,
                olits[j]? = (s.core.arena[src.toNat + 3 + j]?).map BitVec.toNat := fun j hj => by
              have hj' : j < (fullArenaClauseLitsCore s.core src.toNat).length := hol_len ▸ hj
              unfold olits fullArenaClauseLitsCore at hj' ⊢
              rw [List.getElem?_eq_getElem hj', List.getElem_map,
                List.getElem_take, List.getElem_drop,
                List.getElem?_eq_getElem (by rw [har_len]; omega), Option.map_some]
            have hol_lt : ∀ l ∈ olits, l < 2 * old_cv.toNat :=
              fun l hl => hold ▸ har_inv.lits_lt src.toNat hsrc_ref hgarb_f l hl
            have hol_nd : (olits.map (· / 2)).Nodup := hnd src.toNat hsrc_ref hgarb_f
            cm_to_group
            refine wp_join_group (ts := [.bool, i32, i32])
              (fun (sat, new_sz, _, ()) mI =>
                new_sz.toNat ≤ old_sz.toNat ∧
                ∃ arI : List (BitVec 32), arI.length = c.arena_cap ∧
                  (∀ k, (k < dst.toNat ∨ dst.toNat + 3 + new_sz.toNat ≤ k) →
                    k < s.core.arena_len → arI[k]? = arL[k]?) ∧
                  (sat = false →
                    let kept := ((arI.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat
                    (∀ j < new_sz.toNat, (arI[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * ncv) ∧
                    (kept.map (· / 2)).Nodup ∧
                    (cnfOfClauses F_cur).EntailsClause
                      (cnfClause (kept.map (compactUnmapLit inv)))) ∧
                  (FullMem c { sL with core := { kL with arena := arI } } ⋆ R) mI)
              ?_ ?_
            · rintro _ ⟨sat, new_sz, _, ⟨⟩⟩ mI ⟨hns_le, arI, harI, hpresI, hsatI, hmI⟩
              clear hm hbin0
              exact full_compact_arena_keep hpush (c := c) (s := s) (sL := sL) (kCore := kL)
                rfl rfl rfl hext_s.2 hcv_le hal_le hmax_lt har_cap_lt
                (hold ▸ hncv_le) hd_le hsrc_lt hsz3 hfit_src hnsrc_bounds hnsrc_to hnsrc64
                hnsrc_mem hng hckL hlen.scratch_ok hwsL_len
                (fun j hj1 hj2 => har_tail j (by omega) hj2) hpreL hbinL hns_le harI hpresI
                hsatI hmI hJ1 hLoopL
            · intro Ji hJi
              clear hm hbin0
              refine full_compact_arena_inner (c := c) (s := s) (kL := sL) (kCore := kL) rfl rfl
                hckL hcv_le hal_le hv_len hws1_len hmax_lt har_cap_lt hold.symm ?_ hncv_le hbij
                hdom hfent hd_le hfit_src hol_len hol_mem hol_lt hol_nd
                (har_inv.entails src.toNat hsrc_ref hgarb_f)
                (fun j hj1 hj2 => har_tail j (by omega) (by omega)) hmL hJi
              simpa [bv_c0] using hnlits_eq
      · have hsrc_eq : src.toNat = s.core.arena_len := by c0_bound
        cm_steps
        exact hJ1 (src, dst, fred, irred, redd, 0#64, ()) mL
          ⟨by omega, Or.inl rfl, (fun h => absurd h (by decide)), arL, wvecL, wstkL, wlenL, wuL,
           nbL, oomL, wsL, hckL, hwsL_len, (fun h => absurd h (by decide)), hpreL, hbinL, hmL⟩

theorem full_compact_flush_wp (Γ : Env)
    (hbt : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hprop : ∀ a m Q X, fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hsweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullCompactFlushSpec a m Q X → Func.wp Γ full_compact_flush_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩
  cm_split
  · have hinc : s.core.inconsistent ≠ 0#64 := by c0_bound
    cm_steps; exact hQ 20#64 s m hsp (Or.inr (Or.inr rfl)) rfl (Nat.le_refl _)
      (fun _ => hsp.1.inconsistent_unsat hinc) (fun h1 => absurd h1 (by decide)) hm
  · have hinc0 : s.core.inconsistent = 0#64 := by c0_bound
    obtain ⟨F_cur, hw⟩ := hsp.1.witness
    have hcl_lt : s.core.cur_level < 2 ^ 64 := by
      have := hw.cur_level_le; have := hsp.1.lengths.core_ok.trail_end_le
      have := hsp.1.lengths.core_ok.cur_vars_le; have := c.hmaxv; unfold dimacsBound at *; omega
    cm_to_group
    refine wp_join_group
      (fun () m0 =>
        ∃ s0 : FullState, FullSparseInv c F0 s0 ∧ s0.core.cur_level = 0 ∧
          s0.core.inconsistent = 0#64 ∧ s0.core.cur_vars = s.core.cur_vars ∧
          s0.core.fuel = s.core.fuel ∧ (FullMem c s0 ⋆ R) m0)
      ?_ ?_
    · rintro _ ⟨⟩ m0 ⟨s0, hsp0, hcl0, hinc0', hcv0, hfuel0, hm0⟩
      exact full_compact_flush_loop hprop hsweep hsp0 hcl0 hinc0' hcv0 hfuel0 hm0 hQ
    · intro Jbt hJbt
      cm_split
      · have hcl_pos : 0 < s.core.cur_level :=
          Nat.pos_of_ne_zero fun h0 =>
            (by c0_bound : BitVec.ofNat 64 s.core.cur_level ≠ 0#64) (by simp [h0])
        cm_steps; c0_call hbt
        refine ⟨c, s, R, rfl, hsp.1.lengths, hcl_lt, fun _ => by
            have := hw.cur_level_le; have := hsp.1.lengths.core_ok.trail_end_le
            have := hsp.1.lengths.core_ok.cur_vars_le; omega,
          hw.trail_lits_lt, hm,
          fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
            hlen' _ _ hcl' hpres _ _ _ hwf' _ hm' => ?_⟩
        let s0 : FullState :=
          { s with
            core := { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                                  trail_pos := tp', trail_end := te', propagated := prop',
                                  cur_level := cl', unassigned := unass' }
            scratch := sc' }
        have hcl0 : s0.core.cur_level = 0 := by dsimp only [s0]; rw [hcl']; simp
        have hw0 := hwf' F0 F_cur hw (Nat.zero_le _)
        have hext0 : FullExtScratchOk c s0 :=
          FullExtScratchOk.of_pres hsp.2.2.2.1 hpres.1 (fun _ h => h)
        exact hJbt () m' ⟨s0, ⟨⟨hlen', F_cur, hw0⟩, hsp.2.1, hsp.2.2.1, hext0, hsp.2.2.2.2⟩,
          hcl0, hinc0, rfl, rfl, hm'⟩
      · have hcl0 : s.core.cur_level = 0 := by c0_bound
        cm_steps; exact hJbt () m ⟨s, hsp, hcl0, hinc0, rfl, rfl, hm⟩

theorem full_compact_wp (Γ : Env)
    (hfl : ∀ a m Q X, fullCompactFlushSpec a m Q X →
      Γ "full_compact_flush" [i64] [i64] a m Q X)
    (hmk : ∀ a m Q X, fullCompactMarkLiveSpec a m Q X →
      Γ "full_compact_mark_live" [i64] [] a m Q X)
    (hmp : ∀ a m Q X, fullCompactAssignMapSpec a m Q X →
      Γ "full_compact_assign_map" [i64] [i64] a m Q X)
    (hre : ∀ a m Q X, fullCompactRecordExtSpec a m Q X →
      Γ "full_compact_record_ext" [i64, i64, i64] [.bool] a m Q X)
    (hbn : ∀ a m Q X, fullCompactBinsSpec a m Q X →
      Γ "full_compact_bins" [i64, i64, i64] [] a m Q X)
    (hdf : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (har : ∀ a m Q X, fullCompactArenaSpec a m Q X →
      Γ "full_compact_arena" [i64, i64] [i64] a m Q X)
    (hvr : ∀ a m Q X, fullCompactVarsSpec a m Q X →
      Γ "full_compact_vars" [i64, i64, i64] [] a m Q X)
    (hvm : ∀ a m Q X, fullCompactVmtfSpec a m Q X →
      Γ "full_compact_vmtf" [i64, i64] [] a m Q X)
    (hhp : ∀ a m Q X, fullCompactHeapSpec a m Q X →
      Γ "full_compact_heap" [i64, i64] [] a m Q X)
    (hrw : ∀ a m Q X, fullRewatchArenaSpec a m Q X →
      Γ "full_rewatch_arena" [i64, i64] [.bool] a m Q X) :
    ∀ a m Q X, fullCompactSpec a m Q X → Func.wp Γ full_compact_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩
  cm_split
  · exfalso
    have hne : s.core.dense_mode ≠ 0#64 := by c0_bound
    exact hne hsp.2.2.2.2
  · cm_steps; c0_call hfl
    refine ⟨c, F0, s, R, rfl, hsp, hm, ?_⟩
    intro fst s1 m1 hsp1 hfst hcv1 hfuel1 h20 h1 hm1
    cm_split
    · have hfst_ne1 : fst ≠ 1#64 := by c0_bound
      rcases hfst with rfl | rfl | rfl
      · exact hQ 0#64 c s1 m1 (FullCfgCompat.refl c) hsp1 (Or.inl rfl) (by omega) hfuel1
          (fun h => by cases h) (fun h => by cases h) hm1
      · exact absurd rfl hfst_ne1
      · exact hQ 20#64 c s1 m1 (FullCfgCompat.refl c) hsp1 (Or.inr (Or.inr rfl)) (by omega) hfuel1
          h20 (fun h => by cases h) hm1
    · have hfst1 : fst = 1#64 := by c0_bound
      obtain ⟨hcl1, _, _, _, hinc1⟩ := h1 hfst1
      obtain ⟨F_cur, hspW1⟩ := hsp1.exists_witness
      have hcv1_le := hspW1.1.core_ok.cur_vars_le
      have hmax_lt := c.hmaxv
      have hcv1_lt64 : s1.core.cur_vars < 2 ^ 64 := by unfold dimacsBound at hmax_lt; omega
      cm_split
      · cm_steps
        exact hQ 1#64 c s1 m1 (FullCfgCompat.refl c) hsp1 (Or.inr (Or.inl rfl)) (by omega) hfuel1
          (fun h => by cases h) (fun _ => hcl1) hm1
      · cm_steps; c0_call hmk
        refine ⟨c, F0, F_cur, s1, R, rfl, hspW1, hm1, fun ws1_mk m2 hspW2 hm2 => ?_⟩
        let s2 : FullState := { s1 with scratch := { s1.scratch with work_stk1 := ws1_mk } }
        cm_steps; c0_call hmp
        refine ⟨c, s2, R, rfl, hspW2.1, hm2, fun ncv ws1_3 ws2_3 m3 hlen3 hbij3 hm3 => ?_⟩
        let s3 : FullState :=
          { s2 with scratch := { s2.scratch with work_stk1 := ws1_3, work_stk2 := ws2_3 } }
        have hspW3 : FullSparseInvW c F0 F_cur s3 :=
          ⟨hlen3, hspW2.2.1, hspW2.2.2.1, hspW2.2.2.2.1, hspW2.2.2.2.2.1, hspW2.2.2.2.2.2⟩
        cm_split
        · cm_steps
          exact hQ 1#64 c s3 m3 (FullCfgCompat.refl c) hspW3.toSparse (Or.inr (Or.inl rfl))
            (by change s1.core.cur_vars ≤ _; omega) hfuel1 (fun h => by cases h)
            (fun _ => hcl1) hm3
        · have hold_cv : (BitVec.ofNat 64 s1.core.cur_vars).toNat = s3.core.cur_vars :=
            bv64_ofNat_toNat hcv1_lt64
          have hncv_le : ncv.toNat ≤ (BitVec.ofNat 64 s1.core.cur_vars).toNat := by
            rw [hold_cv]; exact hbij3.ncv_le
          have hncv_le_s : ncv.toNat ≤ s.core.cur_vars := by
            rw [hold_cv, show s3.core.cur_vars = s1.core.cur_vars from rfl, hcv1] at hncv_le
            exact hncv_le
          cm_steps; c0_call hre
          refine ⟨c, s3, R, rfl, hlen3, hold_cv, hncv_le, hspW3.2.2.2.2.1.2, hm3,
            fun ok ext4 elen4 m4 hlen4 helen4 _ _ hm4 => ?_⟩
          let s4 : FullState :=
            { s3 with scratch := { s3.scratch with extend_stk := ext4, extend_len := elen4 } }
          have hspW4 : FullSparseInvW c F0 F_cur s4 :=
            ⟨hlen4, hspW3.2.1, hspW3.2.2.1, hspW3.2.2.2.1,
             ⟨hspW3.2.2.2.2.1.1, helen4⟩, hspW3.2.2.2.2.2⟩
          cm_split
          rotate_left
          · cm_steps
            exact hQ 1#64 c s4 m4 (FullCfgCompat.refl c) hspW4.toSparse (Or.inr (Or.inl rfl))
              (by change s1.core.cur_vars ≤ _; omega) hfuel1 (fun h => by cases h)
              (fun _ => hcl1) hm4
          cm_steps; c0_call hbn
          refine ⟨c, F0, F_cur, s4, R, rfl, hspW4, hold_cv, hncv_le,
            (by change CompactBijOk (BitVec.ofNat 64 s1.core.cur_vars).toNat _ _ _ _
                rw [hold_cv]; exact hbij3),
            hm4, fun wvec5 wstk5 wu5 nb5 m5 hlen5 hbin5 hm5 => ?_⟩
          let s5 : FullState :=
            { s4 with core := { s4.core with wvec := wvec5, wstk := wstk5, wusable := wu5,
                                             num_binary := nb5 } }
          cm_steps; c0_call hdf
          refine ⟨c, s5, R, rfl, hlen5, hbin5.layout, hm5,
            fun wvec6 wstk6 wlen6 wsort6 m6 hlen6 hlay6 _ hpres6 hm6 => ?_⟩
          let s6 : FullState :=
            { s5 with
              core := { s5.core with wvec := wvec6, wstk := wstk6, wlen := wlen6, wusable := 0#64 }
              scratch := { s5.scratch with wsort := wsort6 } }
          have hbin6 : CompactUnmapBinsOk ncv.toNat s6.scratch.work_stk2 F_cur s6.core := by
            refine ⟨hlay6, fun l hl1 hl2 => ?_, fun l hl => ?_⟩
            · exact (hpres6 l hl2).1.trans (hbin5.empty_hi l hl1 hl2)
            · have hncv_s5 : ncv.toNat ≤ s5.core.cur_vars := by
                change ncv.toNat ≤ s3.core.cur_vars; exact hbij3.ncv_le
              obtain ⟨hsz, hsl⟩ := hpres6 l (by omega)
              change CompactUnmapBinSliceOk ncv.toNat ws2_3 F_cur s6.core l
                (fullWatchOff s6 l) (fullWatchSize s6 l)
              rw [hsz]; exact (hbin5.slices l hl).relocate hsl
          have hw3 := hspW3.2.1
          cm_steps; c0_call har
          refine ⟨c, F0, F_cur, ncv.toNat, s6, R, rfl, hlen6,
            (by change ExtUnsatSound F0 (BitVec.ofNat 64 s1.core.cur_vars).toNat F_cur
                rw [hold_cv]; exact hw3.ext_sound),
            ⟨hw3.arena.len_ok, hw3.arena.refs_wf, hw3.arena.shrk_term, hw3.arena.lits_lt,
             hw3.arena.entails⟩,
            hspW3.2.2.2.1, hspW3.2.2.2.2.2, hcl1, hold_cv, hncv_le,
            (by change CompactBijOk (BitVec.ofNat 64 s1.core.cur_vars).toNat _ _ _ _
                rw [hold_cv]; exact hbij3),
            (by change ∀ l < 2 * (BitVec.ofNat 64 s1.core.cur_vars).toNat, _
                rw [hold_cv]; exact hw3.vals_domain),
            fun l hl hf => level0_vals_false_entails hw3 hcl1
              (by change l < 2 * s3.core.cur_vars; rw [← hold_cv]; exact hl) hf,
            hbin6, hm6,
            fun ast ar7 al7 fred7 ni7 nr7 wvec7 wstk7 wlen7 wu7 nb7 oom7 ll7 ws7 m7
              hlen7 hast hast2 hast3 hbin7 har7 hll7 hm7 => ?_⟩
          let s7 : FullState :=
            { core := { s6.core with arena := ar7, arena_len := al7, arena_garbage := 0#64,
                                     first_reducible := fred7, num_irred := ni7,
                                     num_redundant := nr7, wvec := wvec7, wstk := wstk7,
                                     wlen := wlen7, wusable := wu7, num_binary := nb7, oom := oom7 }
              scratch := { s6.scratch with last_learned := ll7, wsort := ws7 } }
          cm_steps; c0_call hvr
          refine ⟨c, s7, R, rfl, hlen7, hold_cv, hncv_le, fun nv hnv => ?_, hm7,
            fun c' vals8 fl8 lvl8 rsns8 ft0 fd0 sc8 m8 hcompat8 hlen8 hft0 hvals8 hpres8
              hws1_8 hws2_8 hm8 => ?_⟩
          · obtain ⟨ov, hov, _, _, hinv, _⟩ := hbij3.inv_ok nv hnv
            rw [hinv, Option.getD_some, bv32_ofNat_toNat (by have := hbij3.old_cv_lt; omega)]
            rw [hold_cv]; exact hov
          · let s8 : FullState :=
              { core := { s7.core with vals := vals8, flags := fl8, lvl := lvl8, rsns := rsns8,
                                       frame_trail := s7.core.frame_trail.set 0 ft0,
                                       frame_dec := s7.core.frame_dec.set 0 fd0,
                                       trail_end := 0, propagated := 0, cur_level := 0,
                                       unflushed := 0#64, confl_ref := 0xFFFFFFFF#64,
                                       confl_type := 0#64, cur_vars := ncv.toNat,
                                       unassigned := ncv }
                scratch := sc8 }
            cm_steps; c0_call hvm
            refine ⟨c', s8, R, hcompat8.hdr.symm, hlen8, hlen8.core_ok.cur_vars_le, hm8,
              fun sc9 m9 hlen9 hpres9 hws1_9 hws2_9 hm9 => ?_⟩
            let s9 : FullState := { s8 with scratch := sc9 }
            cm_steps; c0_call hhp
            refine ⟨c', s9, R, hcompat8.hdr.symm, hlen9, hlen9.core_ok.cur_vars_le, hm9,
              fun sc10 m10 hlen10 hpres10 hws1_10 hws2_10 hm10 => ?_⟩
            let s10 : FullState := { s9 with scratch := sc10 }
            let har7c := har7.with_core rfl rfl
            have har10 : CompactArenaOk c' ncv.toNat ws2_3 F_cur s10.core :=
              ⟨har7c.len_ok, har7c.refs_wf, har7c.no_shrk, har7c.no_garb, har7c.lits_lt,
               har7c.nodup, har7c.entails⟩
            have hbin10 : CompactUnmapBinsOk ncv.toNat ws2_3 F_cur s10.core :=
              hbin7.with_vars rfl (by change ncv.toNat ≤ s1.core.cur_vars; omega) rfl rfl rfl
            have hnd10 : FullArenaVarsNodup s10 := fun r hr _ => har10.nodup r hr
            have hmarks10 : FullLitMarksClear c' s10 :=
              FullLitMarksClear.of_compat hcompat8 hspW3.2.2.1
            have hext10 : FullExtScratchOk c' s10 :=
              FullExtScratchOk.of_compat hcompat8 ⟨hll7, helen4⟩
                ⟨hpres10.1.trans (hpres9.1.trans hpres8.1),
                 hpres10.2.trans (hpres9.2.trans hpres8.2)⟩
                fun _ h => h
            have hvals10 : ∀ l < 2 * s10.core.cur_vars, s10.core.vals[l]?.getD 0#8 = 0#8 := by
              intro l hl
              have hl1 : l < 2 * c'.max_vars := by
                have := hlen10.core_ok.cur_vars_le
                change l < 2 * s10.core.cur_vars at hl
                change s10.core.cur_vars ≤ c'.max_vars at this; omega
              have hl2 : l < 2 * (BitVec.ofNat 64 s1.core.cur_vars).toNat := by
                rw [hold_cv]; have := hbij3.ncv_le
                change l < 2 * ncv.toNat at hl
                change ncv.toNat ≤ s3.core.cur_vars at this; omega
              rw [hvals8 l hl1 hl2]; rfl
            have hft10 : (s10.core.frame_trail[0]?.getD 0#32).toNat = 0 := by
              have hft_len : 0 < s7.core.frame_trail.length := by
                have := hlen7.core_ok.frame_trail_len
                dsimp only [s7] at this ⊢; omega
              change ((s7.core.frame_trail.set 0 ft0)[0]?.getD 0#32).toNat = 0
              rw [List.getElem?_set_self hft_len, Option.getD_some, hft0]; rfl
            cm_split
            · have hast_2 : ast = 2#64 := by c0_bound
              rw [← hcompat8.hdr]; cm_steps
              let s11 : FullState := { s10 with core := { s10.core with inconsistent := 1#64 } }
              have har11 : CompactArenaOk c' ncv.toNat ws2_3 F_cur s11.core :=
                har10.with_core rfl rfl
              have hbin11 : CompactUnmapBinsOk ncv.toNat ws2_3 F_cur s11.core :=
                hbin10.with_vars rfl (Nat.le_refl _) rfl rfl rfl
              have hw11 := fullWitnessInv_compact_unsat (hast2 hast_2) hbin11 har11 rfl
                hspW3.2.2.2.2.2 rfl rfl hft10 hvals10
              have hsp11 : FullSparseInv c' F0 s11 :=
                ⟨⟨{ hlen10 with core_ok := { hlen10.core_ok with
                    vals_len := hlen10.core_ok.vals_len } },
                  [[]], hw11⟩, hmarks10, hnd10, hext10, hspW3.2.2.2.2.2⟩
              exact hQ 20#64 c' s11 m hcompat8 hsp11 (Or.inr (Or.inr rfl)) hncv_le_s hfuel1
                (fun _ => hast2 hast_2) (fun h => by cases h) (compactMem_cast hm rfl)
            · cm_split
              · rw [← hcompat8.hdr]; cm_steps
                let s11 : FullState := { s10 with core := { s10.core with oom := 1#64 } }
                have har11 : CompactArenaOk c' ncv.toNat ws2_3 F_cur s11.core :=
                  har10.with_core rfl rfl
                have hbin11 : CompactUnmapBinsOk ncv.toNat ws2_3 F_cur s11.core :=
                  hbin10.with_vars rfl (Nat.le_refl _) rfl rfl rfl
                obtain ⟨hw11, _⟩ := fullWitnessInv_compact_build hw3.ext_sound
                  hbin11 har11 rfl hinc1 hspW3.2.2.2.2.2 rfl rfl hft10 hvals10
                have hsp11 : FullSparseInv c' F0 s11 :=
                  ⟨⟨{ hlen10 with core_ok := { hlen10.core_ok with
                      vals_len := hlen10.core_ok.vals_len } },
                    stateClausesCore s11.core, hw11⟩, hmarks10, hnd10, hext10, hspW3.2.2.2.2.2⟩
                exact hQ 0#64 c' s11 m hcompat8 hsp11 (Or.inl rfl) hncv_le_s hfuel1
                  (fun h => by cases h) (fun h => by cases h) (compactMem_cast hm rfl)
              · obtain ⟨hw10, _⟩ := fullWitnessInv_compact_build hw3.ext_sound
                  hbin10 har10 rfl hinc1 hspW3.2.2.2.2.2 rfl rfl hft10 hvals10
                have hal10_lt : s10.core.arena_len < 2 ^ 64 := by
                  have hle : s10.core.arena_len ≤ c'.arena_cap := hlen10.core_ok.arena_len_le
                  have := c'.harena; unfold dimacsBound at *; omega
                rw [← hcompat8.hdr]; cm_steps; c0_call hrw
                refine ⟨c', F0, stateClausesCore s10.core, s10, R, rfl, hlen10, hw10,
                  hspW3.2.2.2.2.2, bv64_ofNat_toNat hal10_lt, ?_, hm10,
                  fun ok arena11 wvec11 wstk11 wlen11 wu11 oom11 ws11 m11
                    hlen11 hw11 hnd11 href11 _ _ hm11 => ?_⟩
                · intro r hr
                  refine ⟨?_, har10.no_shrk r hr⟩
                  have := har10.no_garb r hr
                  unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; exact this
                · let s11 : FullState :=
                    { s10 with
                      core := { s10.core with arena := arena11, wvec := wvec11, wstk := wstk11,
                                              wlen := wlen11, wusable := wu11, oom := oom11 }
                      scratch := { s10.scratch with wsort := ws11 } }
                  have hext11 : FullExtScratchOk c' s11 :=
                    FullExtScratchOk.of_pres hext10 ⟨rfl, rfl⟩ fun r hr => by
                      change r ∈ fullArenaClauseRefs s11
                      rw [href11]; exact hr
                  have hsp11 : FullSparseInv c' F0 s11 :=
                    ⟨⟨hlen11, stateClausesCore s10.core, hw11⟩, hmarks10, hnd11 hnd10, hext11,
                     hspW3.2.2.2.2.2⟩
                  cm_split
                  · cm_steps
                    exact hQ 1#64 c' s11 m11 hcompat8 hsp11 (Or.inr (Or.inl rfl)) hncv_le_s hfuel1
                      (fun h => by cases h) (fun _ => rfl) hm11
                  · have hok_f : ok = false := by c0_bound
                    cm_steps
                    let s12 : FullState := { s11 with core := { s11.core with oom := 1#64 } }
                    have hw12 : FullWitnessInv c' F0 (stateClausesCore s10.core) s12.core :=
                      { hw11 with
                        arena := { hw11.arena with len_ok := hw11.arena.len_ok }
                        watches := hw11.watches.with_wstk rfl rfl rfl rfl rfl fun _ h => h }
                    have hlen12 : s12.LengthsOk c' :=
                      { hlen11 with core_ok := { hlen11.core_ok with
                          vals_len := hlen11.core_ok.vals_len } }
                    have hext12 : FullExtScratchOk c' s12 :=
                      FullExtScratchOk.of_pres hext11 ⟨rfl, rfl⟩ fun _ h => h
                    have hsp12 : FullSparseInv c' F0 s12 :=
                      ⟨⟨hlen12, stateClausesCore s10.core, hw12⟩, hmarks10, hnd11 hnd10,
                       hext12, hspW3.2.2.2.2.2⟩
                    exact hQ 0#64 c' s12 m hcompat8 hsp12 (Or.inl rfl) hncv_le_s hfuel1
                      (fun h => by cases h) (fun h => by cases h) (compactMem_cast hm rfl)

/-! ## 3. Closed `TableImpl` & `ModuleOk compactEnv compactModule` -/

theorem compact_tableImpl : TableImpl compactEnv compact_fns compactSpecTable := by
  have row_needed : ∀ a m Q X, fullCompactNeededSpec a m Q X →
      compactEnv "full_compact_needed" [i64] [.bool] a m Q X :=
    compactEnv_row (by simp [compactSpecTable]) fun _ _ _ _ ⟨c, s, R, h1, h2, h3, h4, h5⟩ =>
      ⟨c, s, R, h1, h2, h3, h4, h5⟩
  have row_flush : ∀ a m Q X, fullCompactFlushSpec a m Q X →
      compactEnv "full_compact_flush" [i64] [i64] a m Q X :=
    compactEnv_row (by simp [compactSpecTable]) fun _ _ _ _ ⟨c, F0, s, R, h1, h2, h3, h4⟩ =>
      ⟨c, F0, s, R, h1, h2, h3, h4⟩
  have row_mark : ∀ a m Q X, fullCompactMarkLiveSpec a m Q X →
      compactEnv "full_compact_mark_live" [i64] [] a m Q X :=
    compactEnv_row (by simp [compactSpecTable])
      fun _ _ _ _ ⟨c, F0, F_cur, s, R, h1, h2, h3, h4⟩ => ⟨c, F0, F_cur, s, R, h1, h2, h3, h4⟩
  have row_map : ∀ a m Q X, fullCompactAssignMapSpec a m Q X →
      compactEnv "full_compact_assign_map" [i64] [i64] a m Q X :=
    compactEnv_row (by simp [compactSpecTable]) fun _ _ _ _ ⟨c, s, R, h1, h2, h3, h4⟩ =>
      ⟨c, s, R, h1, h2, h3, h4⟩
  have row_ext : ∀ a m Q X, fullCompactRecordExtSpec a m Q X →
      compactEnv "full_compact_record_ext" [i64, i64, i64] [.bool] a m Q X :=
    compactEnv_row (by simp [compactSpecTable])
      fun _ _ _ _ ⟨c, s, R, h1, h2, h3, h4, h5, h6, h7⟩ =>
        ⟨c, s, R, h1, h2, h3, h4, h5, h6, h7⟩
  have row_bins : ∀ a m Q X, fullCompactBinsSpec a m Q X →
      compactEnv "full_compact_bins" [i64, i64, i64] [] a m Q X :=
    compactEnv_row (by simp [compactSpecTable])
      fun _ _ _ _ ⟨c, F0, F_cur, s, R, h1, h2, h3, h4, h5, h6, h7⟩ =>
        ⟨c, F0, F_cur, s, R, h1, h2, h3, h4, h5, h6, h7⟩
  have row_arena : ∀ a m Q X, fullCompactArenaSpec a m Q X →
      compactEnv "full_compact_arena" [i64, i64] [i64] a m Q X :=
    compactEnv_row (by simp [compactSpecTable])
      fun _ _ _ _ ⟨c, F0, F_cur, ncv, s, R, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
        h13, h14, h15⟩ =>
        ⟨c, F0, F_cur, ncv, s, R, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  have row_vars : ∀ a m Q X, fullCompactVarsSpec a m Q X →
      compactEnv "full_compact_vars" [i64, i64, i64] [] a m Q X :=
    compactEnv_row (by simp [compactSpecTable])
      fun _ _ _ _ ⟨c, s, R, h1, h2, h3, h4, h5, h6, h7⟩ => ⟨c, s, R, h1, h2, h3, h4, h5, h6, h7⟩
  have row_sift_q : ∀ a m Q X, fullCompactSiftQSpec a m Q X →
      compactEnv "full_compact_sift_q" [i64, i64, i64, i64] [] a m Q X :=
    compactEnv_row (by simp [compactSpecTable])
      fun _ _ _ _ ⟨qs, ws, R, h1, h2, h3, h4, h5, h6⟩ => ⟨qs, ws, R, h1, h2, h3, h4, h5, h6⟩
  have row_vmtf : ∀ a m Q X, fullCompactVmtfSpec a m Q X →
      compactEnv "full_compact_vmtf" [i64, i64] [] a m Q X :=
    compactEnv_row (by simp [compactSpecTable])
      fun _ _ _ _ ⟨c, s, R, h1, h2, h3, h4, h5⟩ => ⟨c, s, R, h1, h2, h3, h4, h5⟩
  have row_sift_h : ∀ a m Q X, fullCompactSiftHSpec a m Q X →
      compactEnv "full_compact_sift_h" [i64, i64, i64, i64, i64] [] a m Q X :=
    compactEnv_row (by simp [compactSpecTable])
      fun _ _ _ _ ⟨sc, hp, ps, R, h1, h2, h3, h4, h5, h6, h7⟩ =>
        ⟨sc, hp, ps, R, h1, h2, h3, h4, h5, h6, h7⟩
  have row_heap : ∀ a m Q X, fullCompactHeapSpec a m Q X →
      compactEnv "full_compact_heap" [i64, i64] [] a m Q X :=
    compactEnv_row (by simp [compactSpecTable])
      fun _ _ _ _ ⟨c, s, R, h1, h2, h3, h4, h5⟩ => ⟨c, s, R, h1, h2, h3, h4, h5⟩
  have row_next : ∀ a m Q X, fullArenaNextSpec a m Q X →
      compactEnv "full_arena_next" [i64, i32] [i32] a m Q X :=
    compactEnv_row (by simp [compactSpecTable])
      fun _ _ _ _ ⟨c, s, R, h1, h2, h3, h4⟩ => ⟨c, s, R, h1, h2, h3, h4⟩
  have row_defrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      compactEnv "full_wstack_defrag" [i64] [] a m Q X :=
    compactEnv_row (by simp [compactSpecTable])
      fun _ _ _ _ ⟨c, s, R, h1, h2, h3, h4, h5⟩ => ⟨c, s, R, h1, h2, h3, h4, h5⟩
  have row_push : ∀ a m Q X, fullWatchPushSpec a m Q X →
      compactEnv "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X :=
    compactEnv_row (by simp [compactSpecTable])
      fun _ _ _ _ ⟨c, s, R, h1, h2, h3, h4, h5, h6, h7⟩ =>
        ⟨c, s, R, h1, h2, h3, h4, h5, h6, h7⟩
  have row_bt : ∀ a m Q X, fullBacktrackSpec a m Q X →
      compactEnv "full_backtrack" [i64, i64] [] a m Q X :=
    compactEnv_row (by simp [compactSpecTable])
      fun _ _ _ _ ⟨c, s, R, h1, h2, h3, h4, h5, h6, h7⟩ =>
        ⟨c, s, R, h1, h2, h3, h4, h5, h6, h7⟩
  have row_prop : ∀ a m Q X, fullPropagateSpec a m Q X →
      compactEnv "full_propagate" [i64] [i64] a m Q X :=
    compactEnv_row (by simp [compactSpecTable])
      fun _ _ _ _ ⟨c, F0, F_cur, s, R, h1, h2, h3, h4, h5, h6⟩ =>
        ⟨c, F0, F_cur, s, R, h1, h2, h3, h4, h5, h6⟩
  have row_rw : ∀ a m Q X, fullRewatchArenaSpec a m Q X →
      compactEnv "full_rewatch_arena" [i64, i64] [.bool] a m Q X :=
    compactEnv_row (by simp [compactSpecTable])
      fun _ _ _ _ ⟨c, F0, F_cur, s, R, h1, h2, h3, h4, h5, h6, h7, h8⟩ =>
        ⟨c, F0, F_cur, s, R, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have row_sweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      compactEnv "full_arena_sweep" [i64] [i64] a m Q X :=
    compactEnv_row (by simp [compactSpecTable])
      fun _ _ _ _ ⟨c, F0, F_cur, s, R, h1, h2, h3, h4, h5, h6, h7, h8⟩ =>
        ⟨c, F0, F_cur, s, R, h1, h2, h3, h4, h5, h6, h7, h8⟩
  refine ⟨SpecEntry.Impl.of (full_compact_needed_wp compactEnv),
    SpecEntry.Impl.of (full_compact_flush_wp compactEnv row_bt row_prop row_sweep),
    SpecEntry.Impl.of (full_compact_mark_live_wp compactEnv row_next),
    SpecEntry.Impl.of (full_compact_assign_map_wp compactEnv),
    SpecEntry.Impl.of (full_compact_record_ext_wp compactEnv),
    SpecEntry.Impl.of (full_compact_bins_wp compactEnv),
    SpecEntry.Impl.of (full_compact_arena_wp compactEnv row_next row_push),
    SpecEntry.Impl.of (full_compact_vars_wp compactEnv),
    SpecEntry.Impl.of (full_compact_sift_q_wp compactEnv),
    SpecEntry.Impl.of (full_compact_vmtf_wp compactEnv row_sift_q),
    SpecEntry.Impl.of (full_compact_sift_h_wp compactEnv),
    SpecEntry.Impl.of (full_compact_heap_wp compactEnv row_sift_h),
    SpecEntry.Impl.of (full_compact_wp compactEnv row_flush row_mark row_map row_ext row_bins
      row_defrag row_arena row_vars row_vmtf row_heap row_rw),
    trivial⟩

theorem compact_moduleOk : ModuleOk compactEnv compactModule :=
  Env.ofTable_moduleOk compactModule_acyclic
    ⟨full_compact_needed_wf, full_compact_flush_wf, full_compact_mark_live_wf,
     full_compact_assign_map_wf, full_compact_record_ext_wf, full_compact_bins_wf,
     full_compact_arena_wf, full_compact_vars_wf, full_compact_sift_q_wf, full_compact_vmtf_wf,
     full_compact_sift_h_wf, full_compact_heap_wf, full_compact_wf, trivial⟩
    compact_tableImpl

/-! ## 4. Concrete `1972`-byte `Mem 64` UNSAT non-vacuity (`nv_full_compact`, `XPost := False`) -/

/-- Minimal 2-variable UNSAT formula `{(x0), (x1 ∨ x1), (¬x1 ∨ ¬x1)}` with fixed dead `x0`. -/
def nvCompactF0 : CNF Nat := cnfOfClauses [[0], [2, 2], [3, 3]]

theorem nvCompactF0_unsat : nvCompactF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have h1 : (cnfClause [2, 2]).Sat α := (CNF.sat_iff_all_mem_sat.mp hα) _
    (CNF.Internal.mem_iff.mpr (by simp [nvCompactF0, cnfOfClauses]))
  have h2 : (cnfClause [3, 3]).Sat α := (CNF.sat_iff_all_mem_sat.mp hα) _
    (CNF.Internal.mem_iff.mpr (by simp [nvCompactF0, cnfOfClauses]))
  rw [clause_sat_cnfClause_iff] at h1 h2
  obtain ⟨l1, hl1, he1⟩ := h1; obtain ⟨l2, hl2, he2⟩ := h2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl1 hl2
  rcases hl1 with rfl | rfl <;> rcases hl2 with rfl | rfl <;> simp_all [litVar, litSign]

/-- Concrete `FullCfg` (`mv = 2`, `max_vars = 2`, `wcap = 3`, `avail = 1972`, `slack = 0`). -/
def nvCompactCfg : FullCfg where
  hdr := 0x2000#64
  avail := 1972
  mv := 2
  max_vars := 2
  bva_cap := 0
  nc := 3
  arena_cap := 0
  wcap := 3
  delayed_cap := 0
  red_cap := 0
  extend_cap := 0
  scratch_cap := 0
  hbva := rfl
  hmv := by decide
  hmaxv := by decide
  hnc := by decide
  harena := by decide
  hwcap := by decide
  hdel := by decide
  hred := by decide
  hext := by decide
  hscr := by decide
  havail_fit := by decide
  hsize := by decide

/-- Zero-initialized `FullScratch` for `nvCompactCfg`. -/
def nvCompactScratch : FullScratch where
  heap_len := 0
  scinc := 0#64; rel_period := 0#64; rel_limit := 0#64; rel_wait := 0#64
  rel_u := 0#64; rel_v := 0#64; rel_trigger := 0#64; conflicts := 0#64
  learned_lits := 0#64; min_removed := 0#64; delayed_len := 0; stable := 0#64
  switched := 0#64; mode_count := 0#64; mode_confl_lim := 0#64; mode_tick_lim := 0#64
  mode_saved_ticks := 0#64; search_ticks := 0#64; q_first := 0#64; q_last := 0#64
  q_search_idx := 0#64; q_search_stamp := 0#64; q_cur_stamp := 0#64
  target_assigned := 0#64; best_assigned := 0#64; rephase_limit := 0#64; rephased := 0#64
  reduce_limit := 0#64; reductions := 0#64; tier1 := 0#64; tier2 := 0#64
  restarts := 0#64; restart_limit := 0#64; ema_fast_biased := 0#64; ema_fast_exp := 0#64
  ema_slow_biased := 0#64; ema_slow_exp := 0#64; extend_len := 0; rng_state := 0#64
  chrono_levels := 0#64; otfs_cnt := 0#64; eager_sub_cnt := 0#64; probe_limit := 0#64
  probings := 0#64; elim_limit := 0#64; eliminations := 0#64; elim_bound := 0#64
  iterating := 0#64; hbr_cnt := 0#64; trans_cnt := 0#64; viv_cnt := 0#64
  subst_cnt := 0#64; cong_cnt := 0#64; sweep_cnt := 0#64; bve_cnt := 0#64
  bce_cnt := 0#64; bva_cnt := 0#64; walk_cnt_stat := 0#64; fwd_sub_cnt := 0#64
  fwd_str_cnt := 0#64; ant_sz := 0#64; res_sz := 0#64
  walk_vals := List.replicate 4 0#8
  phases := List.replicate 2 0#8
  phases_target := List.replicate 2 0#8
  phases_best := List.replicate 2 0#8
  walk_best := List.replicate 2 0#8
  heap := List.replicate 2 0#32
  pos := List.replicate 2 0#32
  shrink_stk := List.replicate 2 0#32
  q_prev := List.replicate 2 0#32
  q_next := List.replicate 2 0#32
  q_stamp := List.replicate 2 0#32
  wsort := List.replicate 4 0#32
  work_stk1 := List.replicate 4 0#32
  work_stk2 := List.replicate 4 0#32
  tarjan_mark := List.replicate 4 0#32
  tarjan_reach := List.replicate 4 0#32
  score := List.replicate 2 0#64
  sim_sig := List.replicate 2 0#64
  glue_used := List.replicate 64 0#32
  last_learned := List.replicate 16 0xFFFFFFFF#32
  delayed := []
  red_refs := []
  extend_stk := []
  scratch_buf := []

/-- Concrete level-0 state with dead fixed `x0 = true` and active binary-watched `x1`. -/
def nvCompactState : FullState where
  core :=
    { d_cur := 0#64, d_val := 0#64, cur_vars := 2, unassigned := 1#64
      arena_len := 0, wlen := 3, wusable := 0#64, arena_garbage := 0#64
      first_reducible := 0#64, num_irred := 0#64, num_redundant := 0#64, num_binary := 1#64
      unflushed := 0#64, probing := 0#64, trail_end := 1, propagated := 1
      cur_level := 0, fuel := 10#64, confl_ref := 0#64, confl_type := 0#64
      confl_lit0 := 0#64, confl_lit1 := 0#64, tmp_cnt := 0, tmp_len := 0
      min_clr_len := 0, min_clr_full := 0#64, oom := 0#64, dense_mode := 0#64
      inconsistent := 0#64
      vals := [1#8, 0xFF#8, 0#8, 0#8]
      lit_mark := [0#8, 0#8, 0#8, 0#8]
      mrk := [0#8, 0#8]
      flags := [0#32, 1#32]
      lvl := [0#32, 0#32]
      rsns := [0xFFFFFFFF#32, 0xFFFFFFFF#32]
      trl := [0#32, 0#32]
      trail_pos := [0#32, 0#32]
      tmp := [0#32, 0#32]
      min_clr := [0#32, 0#32]
      frame_trail := [0#32, 0#32, 0#32]
      frame_dec := [0#32, 0#32, 0#32]
      wvec := [0#32, 0#32, 0#32, 0#32, 1#32, 1#32, 2#32, 1#32]
      repr := [0#32, 0#32, 0#32, 0#32]
      min_stk := List.replicate 6 0#32
      arena := []
      wstk := [0#32, 0x80000002#32, 0x80000003#32] }
  scratch := nvCompactScratch

def nvCompactBlockHdr : List UInt8 :=
  bytes64 [2#64, 3#64, 0#64, 0#64] ++ bytes64 (Full.hdrTailWords nvCompactCfg nvCompactState)

def nvCompactBlockBytes : List UInt8 :=
  (bytesOf (t := i8) nvCompactState.core.vals ++ List.replicate 4 0) ++
  (bytesOf (t := i8) nvCompactState.scratch.walk_vals ++ List.replicate 4 0) ++
  (bytesOf (t := i8) nvCompactState.core.lit_mark ++ List.replicate 4 0) ++
  (bytesOf (t := i8) nvCompactState.core.mrk ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvCompactState.scratch.phases ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvCompactState.scratch.phases_target ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvCompactState.scratch.phases_best ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvCompactState.scratch.walk_best ++ List.replicate 6 0)

def nvCompactBlockU32A : List UInt8 :=
  (bytesOf (t := i32) nvCompactState.core.flags ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvCompactState.core.lvl ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvCompactState.core.rsns ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvCompactState.core.trl ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvCompactState.core.trail_pos ++ List.replicate 8 0)

def nvCompactBlockU32B : List UInt8 :=
  (bytesOf (t := i32) nvCompactState.core.tmp ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvCompactState.scratch.heap ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvCompactState.scratch.pos ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvCompactState.core.min_clr ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvCompactState.scratch.shrink_stk ++ List.replicate 8 0)

def nvCompactBlockU32C : List UInt8 :=
  (bytesOf (t := i32) nvCompactState.scratch.q_prev ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvCompactState.scratch.q_next ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvCompactState.scratch.q_stamp ++ List.replicate 8 0) ++
  (bytesOf (t := i32) nvCompactState.core.frame_trail ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvCompactState.core.frame_dec ++ List.replicate 4 0)

def nvCompactBlockWvec : List UInt8 :=
  bytesOf (t := i32) nvCompactState.core.wvec ++
  bytesOf (t := i32) nvCompactState.core.repr ++
  bytesOf (t := i32) nvCompactState.scratch.wsort ++
  bytesOf (t := i32) nvCompactState.scratch.work_stk1 ++
  bytesOf (t := i32) nvCompactState.scratch.work_stk2 ++
  bytesOf (t := i32) nvCompactState.scratch.tarjan_mark ++
  bytesOf (t := i32) nvCompactState.scratch.tarjan_reach ++
  bytes64 nvCompactState.scratch.score ++
  bytes64 nvCompactState.scratch.sim_sig

def nvCompactBlockTail : List UInt8 :=
  bytesOf (t := i32) nvCompactState.core.min_stk ++
  bytesOf (t := i32) nvCompactState.scratch.glue_used ++
  bytesOf (t := i32) nvCompactState.scratch.last_learned ++
  bytesOf (t := i32) nvCompactState.core.arena ++
  bytesOf (t := i32) nvCompactState.core.wstk ++
  bytesOf (t := i32) nvCompactState.scratch.delayed ++
  bytesOf (t := i32) nvCompactState.scratch.red_refs ++
  bytesOf (t := i32) nvCompactState.scratch.extend_stk ++
  bytesOf (t := i32) nvCompactState.scratch.scratch_buf ++
  List.replicate 0 0

/-- Concrete `1972`-byte arena image encoding `nvCompactCfg` and `nvCompactState`. -/
def nvCompactBytes : List UInt8 :=
  nvCompactBlockHdr ++ nvCompactBlockBytes ++ nvCompactBlockU32A ++ nvCompactBlockU32B ++
  nvCompactBlockU32C ++ nvCompactBlockWvec ++ nvCompactBlockTail

/-- Concrete `Mem 64` heap mapped at `nvCompactCfg.hdr` (`0x2000`). -/
def nvCompactMem : Mem 64 := nvCompactBytes.At nvCompactCfg.hdr

theorem nvCompactMem_ok : FullMem nvCompactCfg nvCompactState nvCompactMem := by
  let c := nvCompactCfg; let s := nvCompactState
  have hvb : valsBytes c.max_vars - 2 * c.max_vars = 4 := by decide
  have hmb : markBytes c.max_vars - c.max_vars = 6 := by decide
  have hu4 : u32FullBytes c.max_vars - 4 * c.max_vars = 8 := by decide
  have hu8 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 4 := by decide
  have hmv2 : BitVec.ofNat 64 c.max_vars = 2#64 := rfl
  have hmv4 : BitVec.ofNat 64 (2 * c.max_vars) = 4#64 := rfl
  have hmv8 : BitVec.ofNat 64 (4 * c.max_vars) = 8#64 := rfl
  have hmv12 : BitVec.ofNat 64 (4 * (c.max_vars + 1)) = 12#64 := rfl
  have hHdr : nvCompactBlockHdr.length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s))
        (nvCompactBlockHdr.At c.hdr) :=
    cm_join_pair
      (cm_arr64_p (a := c.hdr) (xs := [2#64, 3#64, 0#64, 0#64]) 32 rfl (by decide))
      (cm_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide))
      (by decide) (by decide)
  have hBytes : nvCompactBlockBytes.length = 64 ∧
      (FullCoreByteArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆ c.padBytes)
        (nvCompactBlockBytes.At c.pVals) := by
    have h1 := cm_arr_pad_p (t := i8) (a := c.pVals) (xs := s.core.vals) 4 4 rfl (by decide)
    have h2 := cm_arr_pad_p (t := i8) (a := c.pWalkVals) (xs := s.scratch.walk_vals) 4 4 rfl
      (by decide)
    have h3 := cm_arr_pad_p (t := i8) (a := c.pLitMark) (xs := s.core.lit_mark) 4 4 rfl
      (by decide)
    have h4 := cm_arr_pad_p (t := i8) (a := c.pMark) (xs := s.core.mrk) 2 6 rfl (by decide)
    have h5 := cm_arr_pad_p (t := i8) (a := c.pPhases) (xs := s.scratch.phases) 2 6 rfl
      (by decide)
    have h6 := cm_arr_pad_p (t := i8) (a := c.pPhasesTarget) (xs := s.scratch.phases_target) 2 6
      rfl (by decide)
    have h7 := cm_arr_pad_p (t := i8) (a := c.pPhasesBest) (xs := s.scratch.phases_best) 2 6 rfl
      (by decide)
    have h8 := cm_arr_pad_p (t := i8) (a := c.pWalkBest) (xs := s.scratch.walk_best) 2 6 rfl
      (by decide)
    let pB1 : Mem 64 → Prop :=
      region (c.pVals + 4#64) 4 ⋆ region (c.pWalkVals + 4#64) 4 ⋆
      region (c.pLitMark + 4#64) 4 ⋆ region (c.pMark + 2#64) 6
    have h12 := cm_join_pair h1 h2 (by decide) (by decide)
    have h123 := cm_join_pair h12 h3 (by decide) (by decide)
    have h1234 := cm_sep_reorg (cm_join_pair h123 h4 (by decide) (by decide))
      (Q := (FullCoreByteArrs c s.core ⋆ array (t := i8) c.pWalkVals s.scratch.walk_vals) ⋆ pB1)
      fun _ hm => cm_zip4 hm
    have h12345 := cm_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := cm_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := cm_join_pair h123456 h7 (by decide) (by decide)
    have hall := cm_join_pair h1234567 h8 (by decide) (by decide)
    exact cm_sep_reorg hall fun _ hm => by
      have hfin := cm_zip4_tail hm
      unfold FullScrByteArrs FullCfg.padBytes
      rw [hvb, hmb, hmv4, hmv2]
      simpa only [pB1, sep_assoc] using hfin
  have hU32A : nvCompactBlockU32A.length = 80 ∧
      ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
        (nvCompactBlockU32A.At c.pFlags) := by
    have h1 := cm_arr_pad_p (t := i32) (a := c.pFlags) (xs := s.core.flags) 8 8 rfl (by decide)
    have h2 := cm_arr_pad_p (t := i32) (a := c.pLevel) (xs := s.core.lvl) 8 8 rfl (by decide)
    have h3 := cm_arr_pad_p (t := i32) (a := c.pReason) (xs := s.core.rsns) 8 8 rfl (by decide)
    have h4 := cm_arr_pad_p (t := i32) (a := c.pTrail) (xs := s.core.trl) 8 8 rfl (by decide)
    have h5 := cm_arr_pad_p (t := i32) (a := c.pTrailPos) (xs := s.core.trail_pos) 8 8 rfl
      (by decide)
    have h12 := cm_join_pair h1 h2 (by decide) (by decide)
    have h123 := cm_join_pair h12 h3 (by decide) (by decide)
    have h1234 := cm_join_pair h123 h4 (by decide) (by decide)
    exact cm_sep_reorg (cm_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32A; rw [hu4, hmv8]; exact sep_ac hm
  have hU32B : nvCompactBlockU32B.length = 80 ∧
      ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
        (array (t := i32) c.pHeap s.scratch.heap ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
         array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
        (nvCompactBlockU32B.At c.pTmp) := by
    have h1 := cm_arr_pad_p (t := i32) (a := c.pTmp) (xs := s.core.tmp) 8 8 rfl (by decide)
    have h2 := cm_arr_pad_p (t := i32) (a := c.pHeap) (xs := s.scratch.heap) 8 8 rfl (by decide)
    have h3 := cm_arr_pad_p (t := i32) (a := c.pPos) (xs := s.scratch.pos) 8 8 rfl (by decide)
    have h4 := cm_arr_pad_p (t := i32) (a := c.pMinClr) (xs := s.core.min_clr) 8 8 rfl (by decide)
    have h5 := cm_arr_pad_p (t := i32) (a := c.pShrinkStk) (xs := s.scratch.shrink_stk) 8 8 rfl
      (by decide)
    have h12 := cm_join_pair h1 h2 (by decide) (by decide)
    have h123 := cm_join_pair h12 h3 (by decide) (by decide)
    have h1234 := cm_join_pair h123 h4 (by decide) (by decide)
    exact cm_sep_reorg (cm_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32B; rw [hu4, hmv8]; exact sep_ac hm
  have hU32C : nvCompactBlockU32C.length = 80 ∧
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆
        array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
         array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
        (nvCompactBlockU32C.At c.pQPrev) := by
    have h1 := cm_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev) 8 8 rfl
      (by decide)
    have h2 := cm_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next) 8 8 rfl
      (by decide)
    have h3 := cm_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 8 8 rfl
      (by decide)
    have h4 := cm_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail) 12 4 rfl
      (by decide)
    have h5 := cm_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec) 12 4 rfl
      (by decide)
    have h12 := cm_join_pair h1 h2 (by decide) (by decide)
    have h123 := cm_join_pair h12 h3 (by decide) (by decide)
    have h1234 := cm_join_pair h123 h4 (by decide) (by decide)
    exact cm_sep_reorg (cm_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32C; rw [hu4, hu8, hmv8, hmv12]; exact sep_ac hm
  have hWvec : nvCompactBlockWvec.length = 160 ∧
      ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
        FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
        (nvCompactBlockWvec.At c.pWvec) := by
    have h1 := cm_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 32 rfl (by decide)
    have h2 := cm_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 16 rfl (by decide)
    have h3 := cm_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 16 rfl (by decide)
    have h4 := cm_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1) 16 rfl
      (by decide)
    have h5 := cm_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2) 16 rfl
      (by decide)
    have h6 := cm_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 16 rfl
      (by decide)
    have h7 := cm_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach) 16 rfl
      (by decide)
    have h8 := cm_arr64_p (a := c.pScore) (xs := s.scratch.score) 16 rfl (by decide)
    have h9 := cm_arr64_p (a := c.pSimSig) (xs := s.scratch.sim_sig) 16 rfl (by decide)
    have h12 := cm_join_pair h1 h2 (by decide) (by decide)
    have h123 := cm_join_pair h12 h3 (by decide) (by decide)
    have h1234 := cm_join_pair h123 h4 (by decide) (by decide)
    have h12345 := cm_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := cm_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := cm_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := cm_join_pair h1234567 h8 (by decide) (by decide)
    exact cm_sep_reorg (cm_join_pair h12345678 h9 (by decide) (by decide)) fun _ hm => by
      unfold FullScrWksArrs; exact sep_ac hm
  have hTail : nvCompactBlockTail.length = 356 ∧
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
        (nvCompactBlockTail.At c.pMinStk) := by
    have h1 := cm_arr_p (t := i32) (a := c.pMinStk) (xs := s.core.min_stk) 24 rfl (by decide)
    have h2 := cm_arr_p (t := i32) (a := c.pGlueUsed) (xs := s.scratch.glue_used) 256 rfl
      (by decide)
    have h3 := cm_arr_p (t := i32) (a := c.pLastLearned) (xs := s.scratch.last_learned) 64 rfl
      (by decide)
    have h4 := cm_arr_p (t := i32) (a := c.pArena) (xs := s.core.arena) 0 rfl (by decide)
    have h5 := cm_arr_p (t := i32) (a := c.pWstk) (xs := s.core.wstk) 12 rfl (by decide)
    have h6 := cm_arr_p (t := i32) (a := c.pDelayed) (xs := s.scratch.delayed) 0 rfl (by decide)
    have h7 := cm_arr_p (t := i32) (a := c.pRedRefs) (xs := s.scratch.red_refs) 0 rfl (by decide)
    have h8 := cm_arr_p (t := i32) (a := c.pExtendStk) (xs := s.scratch.extend_stk) 0 rfl
      (by decide)
    have h9 := cm_arr_p (t := i32) (a := c.pScratchBuf) (xs := s.scratch.scratch_buf) 0 rfl
      (by decide)
    have h10 : (List.replicate 0 (0 : UInt8)).length = 0 ∧
        region c.pSlack c.slack ((List.replicate 0 0).At c.pSlack) :=
      ⟨rfl, ⟨List.replicate 0 0, by decide, rfl⟩⟩
    have h12 := cm_join_pair h1 h2 (by decide) (by decide)
    have h123 := cm_join_pair h12 h3 (by decide) (by decide)
    have h1234 := cm_join_pair h123 h4 (by decide) (by decide)
    have h12345 := cm_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := cm_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := cm_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := cm_join_pair h1234567 h8 (by decide) (by decide)
    have h123456789 := cm_join_pair h12345678 h9 (by decide) (by decide)
    exact cm_sep_reorg (cm_join_pair h123456789 h10 (by decide) (by decide)) fun _ hm => by
      unfold FullCoreDynArrs FullScrDynArrs; exact sep_ac hm
  have h01 := cm_join_pair hHdr hBytes (by decide) (by decide)
  have h02 := cm_join_pair h01 hU32A (by decide) (by decide)
  have h03 := cm_join_pair h02 hU32B (by decide) (by decide)
  have h04 := cm_join_pair h03 hU32C (by decide) (by decide)
  have h05 := cm_join_pair h04 hWvec (by decide) (by decide)
  exact (cm_sep_reorg (cm_join_pair h05 hTail (by decide) (by decide)) fun _ hm => by
    unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B FullScratchArrays FullScrU32A
      FullScrMetaArrs FullCfg.pad
    exact sep_ac hm).2

theorem nvCompact_lengths : FullState.LengthsOk nvCompactCfg nvCompactState :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, by decide, Nat.le_refl _,
    Nat.zero_le _, Nat.zero_le _⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem nvCompact_witness :
    FullWitnessInv nvCompactCfg nvCompactF0 [[0], [2, 2], [3, 3]] nvCompactState.core := by
  have hrefs : fullArenaClauseRefsCore nvCompactState.core = [] := rfl
  have hcv : nvCompactState.core.cur_vars = 2 := rfl
  have hte : nvCompactState.core.trail_end = 1 := rfl
  have hcl : nvCompactState.core.cur_level = 0 := rfl
  have hdm : nvCompactState.core.dense_mode = 0#64 := rfl
  have he_0 : (cnfOfClauses [[0], [2, 2], [3, 3]]).EntailsClause (cnfClause [0]) := by
    rw [CNF.entails_clause_def]; intro α hα
    exact (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  have he_22 : (cnfOfClauses [[0], [2, 2], [3, 3]]).EntailsClause (cnfClause [2, 2]) := by
    rw [CNF.entails_clause_def]; intro α hα
    exact (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  have he_33 : (cnfOfClauses [[0], [2, 2], [3, 3]]).EntailsClause (cnfClause [3, 3]) := by
    rw [CNF.entails_clause_def]; intro α hα
    exact (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  have hwat : ModeWatchesInv [[0], [2, 2], [3, 3]] nvCompactState.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_)
      (fun l1 l2 h1 h2 hn p1 p2 => ?_) (fun l hl => ?_)
    · rw [hcv] at hl
      rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> decide
    · rw [hcv] at hl
      rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;>
        (simp [fullWatchSizeCore, nvCompactState] at hp <;> decide)
    · rw [hcv] at h1 h2
      rcases (by omega : l1 = 0 ∨ l1 = 1 ∨ l1 = 2 ∨ l1 = 3) with rfl | rfl | rfl | rfl <;>
        rcases (by omega : l2 = 0 ∨ l2 = 1 ∨ l2 = 2 ∨ l2 = 3) with rfl | rfl | rfl | rfl <;>
        (simp [fullWatchOffCore, fullWatchSizeCore, nvCompactState] at p1 p2 ⊢ <;>
          first | exact absurd rfl hn | omega)
    · rw [hcv] at hl
      rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
      · exact .empty
      · exact .empty
      · exact .bin rfl (by decide) (by decide) (by decide) he_22 .empty
      · exact .bin rfl (by decide) (by decide) (by decide) he_33 .empty
  exact
    { ext_sound := ⟨(varsBoundedBool_iff 2 [[0], [2, 2], [3, 3]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl, fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr,
        fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr⟩
      watches := hwat
      cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hte] at hi hj; omega
      vals_domain := fun l hl => by
        rw [hcv] at hl
        rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;>
          simp [nvCompactState]
      vals_true_iff := fun l hl => by
        rw [hcv] at hl
        rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
        · exact ⟨fun h => (by cases h), fun ⟨i, hi, h⟩ =>
            (by rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h)⟩
        · exact ⟨fun h => (by cases h), fun ⟨i, hi, h⟩ =>
            (by rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h)⟩
        · exact ⟨fun h => (by cases h), fun ⟨i, hi, h⟩ =>
            (by rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h)⟩
      vals_false_iff := fun l hl => by
        rw [hcv] at hl
        rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
        · exact ⟨fun h => (by cases h), fun ⟨i, hi, h⟩ =>
            (by rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h)⟩
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
        · exact ⟨fun h => (by cases h), fun ⟨i, hi, h⟩ =>
            (by rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h)⟩
        · exact ⟨fun h => (by cases h), fun ⟨i, hi, h⟩ =>
            (by rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h)⟩
      lvl_le := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact Nat.le_refl 0
      dec_earliest := fun _ j _ hj _ hpos => by
        rw [hte] at hj; obtain rfl : j = 0 := (by omega); exact absurd hpos.1 (by decide)
      levels_inhabited := fun L h1 h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact he_0
      trail_pos_inv := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      level0_rsn_none := fun i hi _ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      frame_trail_lt := fun L hL => by rw [hcl] at hL; obtain rfl : L = 0 := (by omega); decide
      frame_trail_mono := fun L1 L2 _ hL2 => by
        rw [hcl] at hL2; obtain rfl : L1 = 0 := (by omega)
        obtain rfl : L2 = 0 := (by omega); exact Nat.le_refl _
      frame_trail_before_lt := fun L h1 h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun L h1 h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne
      reason_lit_mem := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne }

theorem nvCompact_sparse : FullSparseInv nvCompactCfg nvCompactF0 nvCompactState := by
  have hmv : nvCompactCfg.max_vars = 2 := rfl
  have hmarks : FullLitMarksClear nvCompactCfg nvCompactState := by
    refine ⟨fun v hv => ?_, fun l hl => ?_⟩
    · rw [hmv] at hv; rcases (by omega : v = 0 ∨ v = 1) with rfl | rfl <;> rfl
    · rw [hmv] at hl
      rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> rfl
  have hnd : FullArenaVarsNodup nvCompactState := fun r hr => by
    have : fullArenaClauseRefs nvCompactState = [] := rfl
    simp [this] at hr
  have hext : FullExtScratchOk nvCompactCfg nvCompactState :=
    ⟨FullLastLearnedWf.of_cleared fun i hi => by
      simp only [nvCompactState, nvCompactScratch, List.getElem?_replicate, show i < 16 by omega,
        ↓reduceIte, Option.getD_some], Nat.le_refl 0⟩
  exact ⟨⟨nvCompact_lengths, [[0], [2, 2], [3, 3]], nvCompact_witness⟩, hmarks, hnd, hext, rfl⟩

/-- Concrete `Mem 64` UNSAT non-vacuity for `full_compact` under `compactEnv` (`XPost := False`). -/
theorem nv_full_compact :
    Func.wp compactEnv full_compact_body (nvCompactCfg.hdr, ()) nvCompactMem
      (fun (r, ()) m' => ∃ c' s',
        FullCfgCompat nvCompactCfg c' ∧ FullSparseInv c' nvCompactF0 s' ∧
        (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) ∧ nvCompactF0.Unsat ∧ FullMem c' s' m')
      (fun _ _ _ _ => False) := by
  have hok : FullSparseInv nvCompactCfg nvCompactF0 nvCompactState := nvCompact_sparse
  have hm : (FullMem nvCompactCfg nvCompactState ⋆ emp) nvCompactMem := by
    rw [sep_emp]; exact nvCompactMem_ok
  exact full_compact_wp compactEnv
    (compactEnv_row (by simp [compactSpecTable]) fun _ _ _ _ ⟨c, F0, s, R, h1, h2, h3, h4⟩ =>
      ⟨c, F0, s, R, h1, h2, h3, h4⟩)
    (compactEnv_row (by simp [compactSpecTable])
      fun _ _ _ _ ⟨c, F0, F_cur, s, R, h1, h2, h3, h4⟩ => ⟨c, F0, F_cur, s, R, h1, h2, h3, h4⟩)
    (compactEnv_row (by simp [compactSpecTable]) fun _ _ _ _ ⟨c, s, R, h1, h2, h3, h4⟩ =>
      ⟨c, s, R, h1, h2, h3, h4⟩)
    (compactEnv_row (by simp [compactSpecTable])
      fun _ _ _ _ ⟨c, s, R, h1, h2, h3, h4, h5, h6, h7⟩ =>
        ⟨c, s, R, h1, h2, h3, h4, h5, h6, h7⟩)
    (compactEnv_row (by simp [compactSpecTable])
      fun _ _ _ _ ⟨c, F0, F_cur, s, R, h1, h2, h3, h4, h5, h6, h7⟩ =>
        ⟨c, F0, F_cur, s, R, h1, h2, h3, h4, h5, h6, h7⟩)
    (compactEnv_row (by simp [compactSpecTable])
      fun _ _ _ _ ⟨c, s, R, h1, h2, h3, h4, h5⟩ => ⟨c, s, R, h1, h2, h3, h4, h5⟩)
    (compactEnv_row (by simp [compactSpecTable])
      fun _ _ _ _ ⟨c, F0, F_cur, ncv, s, R, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
        h13, h14, h15⟩ =>
        ⟨c, F0, F_cur, ncv, s, R, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
          h13, h14, h15⟩)
    (compactEnv_row (by simp [compactSpecTable])
      fun _ _ _ _ ⟨c, s, R, h1, h2, h3, h4, h5, h6, h7⟩ => ⟨c, s, R, h1, h2, h3, h4, h5, h6, h7⟩)
    (compactEnv_row (by simp [compactSpecTable])
      fun _ _ _ _ ⟨c, s, R, h1, h2, h3, h4, h5⟩ => ⟨c, s, R, h1, h2, h3, h4, h5⟩)
    (compactEnv_row (by simp [compactSpecTable])
      fun _ _ _ _ ⟨c, s, R, h1, h2, h3, h4, h5⟩ => ⟨c, s, R, h1, h2, h3, h4, h5⟩)
    (compactEnv_row (by simp [compactSpecTable])
      fun _ _ _ _ ⟨c, F0, F_cur, s, R, h1, h2, h3, h4, h5, h6, h7, h8⟩ =>
        ⟨c, F0, F_cur, s, R, h1, h2, h3, h4, h5, h6, h7, h8⟩)
    (nvCompactCfg.hdr, ()) nvCompactMem _ _ ⟨nvCompactCfg, nvCompactF0, nvCompactState, emp,
      rfl, hok, hm, fun r c' s' m' hcompat' hsp' hr _ _ _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨c', s', hcompat', hsp', hr, nvCompactF0_unsat, hm'⟩⟩

/-- Compaction non-vacuity (`cur_vars` shrinks `< nvCompactCfg.mv = 2`) under `compactEnv`. -/
theorem nv_full_compact_canary10 :
    Func.wp compactEnv full_compact_assign_map_body (nvCompactCfg.hdr, ()) nvCompactMem
      (fun (ncv, ()) m' => ∃ s',
        ncv.toNat < nvCompactCfg.mv ∧ ncv.toNat ≤ 1 ∧
        CompactBijOk nvCompactState.core.cur_vars ncv.toNat nvCompactState.core.vals
          s'.scratch.work_stk1 s'.scratch.work_stk2 ∧
        FullMem nvCompactCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvCompactCfg nvCompactState ⋆ emp) nvCompactMem := by
    rw [sep_emp]; exact nvCompactMem_ok
  refine full_compact_assign_map_wp compactEnv (nvCompactCfg.hdr, ()) nvCompactMem _ _
    ⟨nvCompactCfg, nvCompactState, emp, rfl, nvCompact_lengths, hm,
     fun ncv ws1' ws2' m' _ hbij hm' => ?_⟩
  rw [sep_emp] at hm'
  have hle1 : ncv.toNat ≤ 1 := by
    by_cases hle : ncv.toNat ≤ 1
    · exact hle
    · exfalso
      have hgt1 : 1 < ncv.toNat := by omega
      obtain ⟨ov0, hov0, _, hv0, hi0, _⟩ := hbij.inv_ok 0 (by omega)
      obtain ⟨ov1, hov1, _, hv1, hi1, _⟩ := hbij.inv_ok 1 (by omega)
      have hov0_eq : ov0 = 1 := by
        change ov0 < 2 at hov0
        rcases (by omega : ov0 = 0 ∨ ov0 = 1) with rfl | rfl
        · cases hv0
        · rfl
      have hov1_eq : ov1 = 1 := by
        change ov1 < 2 at hov1
        rcases (by omega : ov1 = 0 ∨ ov1 = 1) with rfl | rfl
        · cases hv1
        · rfl
      subst hov0_eq hov1_eq
      have h01 := hbij.inv_inj (nv1 := 0) (nv2 := 1) (by omega) (by omega) (by rw [hi0, hi1])
      omega
  exact ⟨_, by change ncv.toNat < 2; omega, hle1, hbij, hm'⟩

end LeanQbe.T.Examples.Kissat.FullM4Compact

